// The main idea comes from cpython 3.8's `gcmodule.c` [1].
//
// [1]: https://github.com/python/cpython/blob/v3.8.0/Modules/gcmodule.c

// NOTE: Consider adding generation support if necessary. It won't be too hard.

use crate::cc::CcDummy;
use crate::cc::CcDyn;
use crate::cc::GcClone;
use crate::debug;
use crate::ref_count;
use crate::ref_count::RefCount;
use crate::Cc;
use crate::Trace;
use std::cell::Cell;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::pin::Pin;

/// A collection of [`Cc`](struct.Cc.html)s that might form cycles with one
/// another.
///
/// # Example
///
/// ```
/// use gcmodule::{Cc, CcObjectSpace, Trace};
/// use std::cell::RefCell;
///
/// let mut space = CcObjectSpace::default();
/// assert_eq!(space.count_tracked(), 0);
///
/// {
///     type List = Cc<RefCell<Vec<Box<dyn Trace>>>>;
///     let a: List = space.create(Default::default());
///     let b: List = space.create(Default::default());
///     a.borrow_mut().push(Box::new(b.clone()));
///     b.borrow_mut().push(Box::new(a.clone()));
/// }
///
/// assert_eq!(space.count_tracked(), 2);
/// assert_eq!(space.collect_cycles(), 2);
/// ```
///
/// Use [`Cc::new_in_space`](struct.Cc.html#method.new_in_space).
pub struct CcObjectSpace {
    /// Linked list to the tracked objects.
    pub(crate) list: RefCell<Pin<Box<GcHeader>>>,

    /// Mark `ObjectSpace` as `!Send` and `!Sync`. This enforces thread-exclusive
    /// access to the linked list so methods can use `&self` instead of
    /// `&mut self`, together with usage of interior mutability.
    _phantom: PhantomData<Cc<()>>,
}

/// This is a private type.
pub trait ObjectSpace: 'static + Sized {
    type RefCount: RefCount;
    type Header;

    /// Insert "header" and "value" to the linked list.
    fn insert(&self, header: &Self::Header, value: &dyn CcDyn);

    /// Remove from linked list.
    fn remove(header: &Self::Header);

    /// Create a `RefCount` object.
    fn new_ref_count(&self, tracked: bool) -> Self::RefCount;

    fn default_header(&self) -> Self::Header;
}

impl ObjectSpace for CcObjectSpace {
    type RefCount = Cell<usize>;
    type Header = GcHeader;

    fn insert(&self, header: &Self::Header, value: &dyn CcDyn) {
        let header: &GcHeader = &header;
        let prev: &GcHeader = &self.list.borrow();
        debug_assert!(header.next.get().is_null());
        let next = prev.next.get();
        header.prev.set(prev.deref());
        header.next.set(next);
        unsafe {
            // safety: The linked list is maintained, and pointers are valid.
            (&*next).prev.set(header);
            // safety: To access vtable pointer. Test by test_gc_header_value.
            let fat_ptr: [*mut (); 2] = mem::transmute(value);
            header.ccdyn_vptr.set(fat_ptr[1]);
        }
        prev.next.set(header);
    }

    #[inline]
    fn remove(header: &Self::Header) {
        let header: &GcHeader = &header;
        debug_assert!(!header.next.get().is_null());
        debug_assert!(!header.prev.get().is_null());
        let next = header.next.get();
        let prev = header.prev.get();
        // safety: The linked list is maintained. Pointers in it are valid.
        unsafe {
            (*prev).next.set(next);
            (*next).prev.set(prev);
        }
        header.next.set(std::ptr::null_mut());
    }

    #[inline]
    fn new_ref_count(&self, tracked: bool) -> Self::RefCount {
        let value = (1 << ref_count::REF_COUNT_SHIFT)
            | if tracked {
                ref_count::REF_COUNT_MASK_TRACKED
            } else {
                0
            };
        Cell::new(value)
    }

    #[inline]
    fn default_header(&self) -> Self::Header {
        GcHeader::empty()
    }
}

impl Default for CcObjectSpace {
    /// Constructs an empty [`ObjectSpace`](struct.ObjectSpace.html).
    fn default() -> Self {
        let header = new_gc_list();
        Self {
            list: RefCell::new(header),
            _phantom: PhantomData,
        }
    }
}

impl CcObjectSpace {
    /// Count objects tracked by this [`ObjectSpace`](struct.ObjectSpace.html).
    pub fn count_tracked(&self) -> usize {
        let list: &GcHeader = &self.list.borrow();
        let mut count = 0;
        visit_list(list, |_| count += 1);
        count
    }

    /// Collect cyclic garbage tracked by this [`ObjectSpace`](struct.ObjectSpace.html).
    /// Return the number of objects collected.
    pub fn collect_cycles(&self) -> usize {
        let list: &GcHeader = &self.list.borrow();
        collect_list(list, (), ())
    }

    /// Constructs a new [`Cc<T>`](struct.Cc.html) in this
    /// [`ObjectSpace`](struct.ObjectSpace.html).
    ///
    /// The returned [`Cc<T>`](struct.Cc.html) can refer to other `Cc`s in the
    /// same [`ObjectSpace`](struct.ObjectSpace.html).
    ///
    /// If a `Cc` refers to another `Cc` in another
    /// [`ObjectSpace`](struct.ObjectSpace.html), the cyclic collector will not
    /// be able to collect cycles.
    pub fn create<T: Trace>(&self, value: T) -> Cc<T> {
        // `&mut self` ensures thread-exclusive access.
        Cc::new_in_space(value, self)
    }

    // TODO: Consider implementing "merge" or method to collect multiple spaces
    // together, to make it easier to support generational collection.
}

impl Drop for CcObjectSpace {
    fn drop(&mut self) {
        self.collect_cycles();
    }
}

pub trait Linked {
    fn next(&self) -> *const Self;
    fn prev(&self) -> *const Self;
    fn set_prev(&self, other: *const Self);

    /// Get the trait object to operate on the actual `CcBox`.
    fn value(&self) -> &dyn CcDyn;
}

/// Internal metadata used by the cycle collector.
#[repr(C)]
pub struct GcHeader {
    pub(crate) next: Cell<*const GcHeader>,
    pub(crate) prev: Cell<*const GcHeader>,

    /// Vtable of (`&CcBox<T> as &dyn CcDyn`)
    pub(crate) ccdyn_vptr: Cell<*mut ()>,
}

impl Linked for GcHeader {
    #[inline]
    fn next(&self) -> *const Self {
        self.next.get()
    }
    #[inline]
    fn prev(&self) -> *const Self {
        self.prev.get()
    }
    #[inline]
    fn set_prev(&self, other: *const Self) {
        self.prev.set(other)
    }
    #[inline]
    fn value(&self) -> &dyn CcDyn {
        // safety: To build trait object from self and vtable pointer.
        // Test by test_gc_header_value_consistency().
        unsafe {
            let fat_ptr: (*const (), *mut ()) =
                ((self as *const Self).offset(1) as _, self.ccdyn_vptr.get());
            mem::transmute(fat_ptr)
        }
    }
}

impl GcHeader {
    /// Create an empty header.
    pub(crate) fn empty() -> Self {
        Self {
            next: Cell::new(std::ptr::null()),
            prev: Cell::new(std::ptr::null()),
            ccdyn_vptr: Cell::new(CcDummy::ccdyn_vptr()),
        }
    }
}

/// Collect cyclic garbage in the current thread created by
/// [`Cc::new`](struct.Cc.html#method.new).
/// Return the number of objects collected.
pub fn collect_thread_cycles() -> usize {
    debug::log(|| ("collect", "collect_thread_cycles"));
    THREAD_OBJECT_SPACE.with(|list| list.collect_cycles())
}

/// Count number of objects tracked by the collector in the current thread
/// created by [`Cc::new`](struct.Cc.html#method.new).
/// Return the number of objects tracked.
pub fn count_thread_tracked() -> usize {
    THREAD_OBJECT_SPACE.with(|list| list.count_tracked())
}

thread_local!(pub(crate) static THREAD_OBJECT_SPACE: CcObjectSpace = CcObjectSpace::default());

/// Create an empty linked list with a dummy GcHeader.
pub(crate) fn new_gc_list() -> Pin<Box<GcHeader>> {
    let pinned = Box::pin(GcHeader::empty());
    let header: &GcHeader = pinned.deref();
    header.prev.set(header);
    header.next.set(header);
    pinned
}

/// Scan the specified linked list. Collect cycles.
pub(crate) fn collect_list<L: Linked, K1, K2>(
    list: &L,
    linked_list_lock: K1,
    ref_count_lock: K2,
) -> usize {
    update_refs(list);
    subtract_refs(list);
    release_unreachable(list, linked_list_lock, ref_count_lock)
}

/// Visit the linked list.
pub(crate) fn visit_list<'a, L: Linked>(list: &'a L, mut func: impl FnMut(&'a L)) {
    // Skip the first dummy entry.
    let mut ptr = list.next();
    while ptr as *const _ != list as *const _ {
        // The linked list is maintained so the pointer is valid.
        let header: &L = unsafe { &*ptr };
        ptr = header.next();
        func(header);
    }
}

const PREV_MASK_COLLECTING: usize = 1;
const PREV_SHIFT: u32 = 1;

/// Temporarily use `GcHeader.prev` as `gc_ref_count`.
/// Idea comes from https://bugs.python.org/issue33597.
fn update_refs<L: Linked>(list: &L) {
    visit_list(list, |header| {
        let ref_count = header.value().gc_ref_count();
        // It's possible that the ref_count becomes 0 in a multi-thread context:
        //  thread 1> drop()
        //  thread 1> drop() -> dec_ref()
        //  thread 2> collect_cycles()        # take linked list lock
        //  thread 1> drop() -> drop_ccbox()  # blocked by the linked list lock
        //  thread 2> observe that ref_count is 0, but T is not dropped yet.
        // In such case just ignore the object by not marking it as COLLECTING.
        if ref_count > 0 {
            let shifted = (ref_count << PREV_SHIFT) | PREV_MASK_COLLECTING;
            header.set_prev(shifted as _);
        } else {
            debug_assert!(header.prev() as usize & PREV_MASK_COLLECTING == 0);
        }
    });
}

/// Subtract ref counts in `GcHeader.prev` by calling the non-recursive
/// `Trace::trace` on every track objects.
///
/// After this, potential unreachable objects will have ref count down
/// to 0. If vertexes in a connected component _all_ have ref count 0,
/// they are unreachable and can be released.
fn subtract_refs<L: Linked>(list: &L) {
    let mut tracer = |header: *const ()| {
        // safety: The type is known to be GcHeader.
        let header = unsafe { &*(header as *const L) };
        if is_collecting(header) {
            debug_assert!(!is_unreachable(header));
            edit_gc_ref_count(header, -1);
        }
    };
    visit_list(list, |header| {
        header.value().gc_traverse(&mut tracer);
    });
}

/// Mark objects as reachable recursively. So ref count 0 means unreachable
/// values. This also removes the COLLECTING flag for reachable objects so
/// unreachable objects all have the COLLECTING flag set.
fn mark_reachable<L: Linked>(list: &L) {
    fn revive<L: Linked>(header: *const ()) {
        // safety: The type is known to be GcHeader.
        let header = unsafe { &*(header as *const L) };
        // hasn't visited?
        if is_collecting(header) {
            unset_collecting(header);
            if is_unreachable(header) {
                edit_gc_ref_count(header, 1); // revive
            }
            header.value().gc_traverse(&mut revive::<L>); // revive recursively
        }
    }
    visit_list(list, |header| {
        if is_collecting(header) && !is_unreachable(header) {
            unset_collecting(header);
            header.value().gc_traverse(&mut revive::<L>)
        }
    });
}

/// Release unreachable objects in the linked list.
fn release_unreachable<L: Linked, K1, K2>(
    list: &L,
    linked_list_lock: K1,
    ref_count_lock: K2,
) -> usize {
    // Mark reachable objects. For example, A refers B. A's gc_ref_count
    // is 1 while B's gc_ref_count is 0. In this case B should be revived
    // by A's non-zero gc_ref_count.
    mark_reachable(list);

    let mut count = 0;

    // Count unreachable objects. This is an optimization to avoid realloc.
    visit_list(list, |header| {
        if is_unreachable(header) {
            count += 1;
        }
    });

    debug::log(|| ("collect", format!("{} unreachable objects", count)));

    // Build a list of what to drop. The collecting steps change the linked list
    // so `visit_list` cannot be used.
    //
    // Here we keep extra references to the `CcBox<T>` to keep them alive. This
    // ensures metadata fields like `ref_count` is available.
    let mut to_drop: Vec<Box<dyn GcClone>> = Vec::with_capacity(count);
    visit_list(list, |header| {
        if is_unreachable(header) {
            to_drop.push(header.value().gc_clone());
        }
    });

    // Restore "prev" so deleting nodes from the linked list can work.
    restore_prev(list);

    // Drop the ref count lock so reference counts can be changed.
    // This is needed because gc_drop_t might change the ref counts.
    drop(ref_count_lock);

    // Drop `T` without releasing memory of `CcBox<T>`. This might trigger some
    // recursive drops of other `Cc<T>`. `CcBox<T>` need to stay alive so
    // `Cc<T>::drop` can read the ref count metadata.
    for value in to_drop.iter() {
        value.gc_drop_t();
    }

    // At this point the only references to the `CcBox<T>`s are inside the
    // `to_drop` list. Dropping `to_drop` would release the memory.
    for value in to_drop.iter() {
        let ref_count = value.gc_ref_count();
        assert_eq!(
            ref_count, 1,
            concat!(
                "bug: unexpected ref-count after dropping cycles\n",
                "This usually indicates a buggy Trace or Drop implementation."
            )
        );
    }

    // Drop the linked list lock.
    // This is needed because dropping `to_drop` will change the linked list
    // by ObjectSpace::remove, which might need to lock.
    drop(linked_list_lock);

    count
}

/// Restore `GcHeader.prev` as a pointer used in the linked list.
fn restore_prev<L: Linked>(list: &L) {
    let mut prev = list;
    visit_list(list, |header| {
        header.set_prev(prev);
        prev = header;
    });
}

fn is_unreachable<L: Linked>(header: &L) -> bool {
    let prev = header.prev() as *const L as usize;
    is_collecting(header) && (prev >> PREV_SHIFT) == 0
}

pub(crate) fn is_collecting<L: Linked>(header: &L) -> bool {
    let prev = header.prev() as *const L as usize;
    (prev & PREV_MASK_COLLECTING) != 0
}

fn unset_collecting<L: Linked>(header: &L) {
    let prev = header.prev() as *const L as usize;
    let new_prev = (prev & PREV_MASK_COLLECTING) ^ prev;
    header.set_prev(new_prev as _);
}

fn edit_gc_ref_count<L: Linked>(header: &L, delta: isize) {
    let prev = header.prev() as *const L as isize;
    let new_prev = prev + (1 << PREV_SHIFT) * delta;
    header.set_prev(new_prev as _);
}
