use crate::trace::{Trace, Tracer};

/// Mark types as acyclic. Opt-out the cycle collector.
///
/// See [`Trace::is_type_tracked`](trait.Trace.html#method.is_type_tracked) for details.
/// In general, types including trait objects (directly or indirectly) should
/// not be acyclic.
///
/// ## Examples
///
/// ```
/// use gcmodule::trace_acyclic;
///
/// struct X(u32);
/// struct Y(String);
/// struct Z<T>(fn (T));
///
/// trace_acyclic!{ X };
/// trace_acyclic!{ Y };
/// trace_acyclic!{ <T> Z<T> };
/// ```
#[macro_export]
macro_rules! trace_acyclic {
    ( <$( $g:ident ),* $(,)?> $ty:ty ) => {
        impl<$( $g: 'static ),*> $crate::Trace for $ty {
            #[inline]
            fn is_type_tracked() -> bool { false }
        }
    };
    ( $( $(#[$attr:meta])* $ty: ty ),* $(,)? ) => {
        $( $(#[$attr])* trace_acyclic!{ <> $ty } )*
    };
}

macro_rules! trace_fn_acyclic {
    ($($arg:ident),* $(,)?) => {
        trace_acyclic!{ <X, $($arg),*> extern "Rust" fn ($($arg),*) -> X }
        trace_acyclic!{ <X, $($arg),*> extern "C" fn ($($arg),*) -> X }
        trace_acyclic!{ <X, $($arg),*> unsafe extern "Rust" fn ($($arg),*) -> X }
        trace_acyclic!{ <X, $($arg),*> unsafe extern "C" fn ($($arg),*) -> X }
    };
}

/// Implement [`Trace`](trait.Trace.html) for simple container types.
///
/// ## Examples
///
/// ```
/// use gcmodule::Trace;
/// use gcmodule::trace_fields;
///
/// struct X<T1, T2> { a: T1, b: T2 };
/// struct Y<T>(Box<T>);
/// struct Z(Box<dyn Trace>);
///
/// trace_fields!(
///     X<T1, T2> { a: T1, b: T2 },
///     Y<T> { 0: T },
///     Z { 0 }
/// );
/// ```
#[macro_export]
macro_rules! trace_fields {
    ( $( $type:ty { $( $field:tt $(: $tp:ident )? ),* $(,)? } ),* $(,)? ) => {
        $(
            impl< $( $( $tp: $crate::Trace )? ),* > $crate::Trace for $type {
                fn trace(&self, tracer: &mut $crate::Tracer) {
                    let _ = tracer;
                    $( (&self . $field ).trace(tracer); )*
                }
                #[inline]
                fn is_type_tracked() -> bool {
                    $($($tp::is_type_tracked() || )?)* false
                }
            }
        )*
    };
}

use std::borrow::Cow;

trace_acyclic!{
    (),
    bool, char,
    f32, f64,
    isize, i8, i16, i32, i64, i128,
    usize, u8, u16, u32, u64, u128,
    std::sync::atomic::AtomicIsize,
    std::sync::atomic::AtomicI8,
    std::sync::atomic::AtomicI16,
    std::sync::atomic::AtomicI32,
    std::sync::atomic::AtomicI64,
    std::sync::atomic::AtomicUsize,
    std::sync::atomic::AtomicU8,
    std::sync::atomic::AtomicU16,
    std::sync::atomic::AtomicU32,
    std::sync::atomic::AtomicU64,
    String, Box<str>, &'static str,
    std::ffi::NulError,
    std::ffi::CString, Box<std::ffi::CStr>, &'static std::ffi::CStr,
    std::ffi::OsString, Box<std::ffi::OsStr>, &'static std::ffi::OsStr,
    std::path::PathBuf, Box<std::path::Path>, &'static std::path::Path,
    std::net::AddrParseError,
    std::net::Ipv4Addr,
    std::net::Ipv6Addr,
    std::net::SocketAddrV4,
    std::net::SocketAddrV6,
    std::net::TcpListener,
    std::net::TcpStream,
    std::net::UdpSocket,
    std::process::Child,
    std::process::ChildStderr,
    std::process::ChildStdin,
    std::process::ChildStdout,
    std::process::Command,
    std::process::ExitStatus,
    std::process::Output,
    std::process::Stdio
}

trace_acyclic!{ <T> &'static T }
trace_acyclic!{ <T> &'static [T] }
trace_acyclic!{ <T> std::marker::PhantomData<T> }
trace_acyclic!{ <T> std::thread::JoinHandle<T> }
trace_acyclic!{ <T> std::thread::LocalKey<T> }
trace_acyclic!{ std::thread::Thread }

trace_fields!{
    (A,) { 0: A },
    (A, B) { 0: A, 1: B },
    (A, B, C) { 0: A, 1: B, 2: C },
    (A, B, C, D) { 0: A, 1: B, 2: C, 3: D },
    (A, B, C, D, E) { 0: A, 1: B, 2: C, 3: D, 4: E },
    (A, B, C, D, E, F) { 0: A, 1: B, 2: C, 3: D, 4: E, 5: F },
    (A, B, C, D, E, F, G) { 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G },
    (A, B, C, D, E, F, G, H) { 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H },
    (A, B, C, D, E, F, G, H, I) { 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I },
    (A, B, C, D, E, F, G, H, I, J) { 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J },
    (A, B, C, D, E, F, G, H, I, J, K) { 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K },
    (A, B, C, D, E, F, G, H, I, J, K, L) { 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K, 11: L }
}

impl<T: Trace> Trace for Option<T> {
    fn trace(&self, tracer: &mut Tracer) {
        if let Some(ref t) = *self {
            t.trace(tracer);
        }
    }

    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: Trace, U: Trace> Trace for Result<T, U> {
    fn trace(&self, tracer: &mut Tracer) {
        match *self {
            Ok(ref t) => t.trace(tracer),
            Err(ref u) => u.trace(tracer),
        }
    }

    fn is_type_tracked() -> bool {
        T::is_type_tracked() || U::is_type_tracked()
    }
}

impl<T: Trace, const N: usize> Trace for [T; N] {
    fn trace(&self, tracer: &mut Tracer) {
        for t in self {
            t.trace(tracer);
        }
    }

    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: Trace> Trace for Vec<T> {
    fn trace(&self, tracer: &mut Tracer) {
        for t in self {
            t.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: ToOwned + ?Sized> Trace for Cow<'static, T>
where T::Owned: Trace {
    fn trace(&self, tracer: &mut Tracer) {
        match self {
            Cow::Owned(v) => v.trace(tracer),
            Cow::Borrowed(..) => (),
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::Owned::is_type_tracked()
    }
}

impl<T: Trace> Trace for Box<T> {
    fn trace(&self, tracer: &mut Tracer) {
        self.as_ref().trace(tracer);
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: Trace> Trace for Box<[T]> {
    fn trace(&self, tracer: &mut Tracer) {
        for t in self.as_ref() {
            t.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl Trace for Box<dyn Trace> {
    fn trace(&self, tracer: &mut Tracer) {
        self.as_ref().trace(tracer);
    }

    #[inline]
    fn is_type_tracked() -> bool {
        // Trait objects can have complex non-atomic structure.
        true
    }
}

impl Trace for Box<dyn Trace + Send> {
    fn trace(&self, tracer: &mut Tracer) {
        self.as_ref().trace(tracer);
    }

    #[inline]
    fn is_type_tracked() -> bool {
        true
    }
}

impl Trace for Box<dyn Trace + Send + Sync> {
    fn trace(&self, tracer: &mut Tracer) {
        self.as_ref().trace(tracer);
    }

    #[inline]
    fn is_type_tracked() -> bool {
        true
    }
}

impl<T: Copy + Trace> Trace for std::cell::Cell<T> {
    fn trace(&self, tracer: &mut Tracer) {
        self.get().trace(tracer);
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: Trace> Trace for std::cell::RefCell<T> {
    fn trace(&self, tracer: &mut Tracer) {
        // If the RefCell is currently borrowed we
        // assume there's an outstanding reference to this
        // cycle so it's ok if we don't trace through it.
        // If the borrow gets leaked somehow then we're going
        // to leak the cycle.
        if let Ok(x) = self.try_borrow() {
            x.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<K: Trace, V: Trace> Trace for std::collections::BTreeMap<K, V> {
    fn trace(&self, tracer: &mut Tracer) {
        for (k, v) in self {
            k.trace(tracer);
            v.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        K::is_type_tracked() || V::is_type_tracked()
    }
}

impl<T: Trace> Trace for std::collections::BTreeSet<T> {
    fn trace(&self, tracer: &mut Tracer) {
        for t in self {
            t.trace(tracer);
        }
    }

    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: Trace> Trace for std::collections::BinaryHeap<T> {
    fn trace(&self, tracer: &mut Tracer) {
        for t in self {
            t.trace(tracer);
        }
    }

    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<K: Trace, V: Trace, B: 'static> Trace for std::collections::HashMap<K, V, B> {
    fn trace(&self, tracer: &mut Tracer) {
        for (k, v) in self {
            k.trace(tracer);
            v.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        K::is_type_tracked() || V::is_type_tracked()
    }
}

impl<T: Trace, B: 'static> Trace for std::collections::HashSet<T, B> {
    fn trace(&self, tracer: &mut Tracer) {
        for t in self {
            t.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: Trace> Trace for std::collections::LinkedList<T> {
    fn trace(&self, tracer: &mut Tracer) {
        for t in self {
            t.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: Trace> Trace for std::collections::VecDeque<T> {
    fn trace(&self, tracer: &mut Tracer) {
        for t in self {
            t.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

trace_acyclic!{ <T> std::rc::Rc<T> }
trace_acyclic!{ <T> std::rc::Weak<T> }
trace_acyclic!{ <T> std::rc::Rc<[T]> }
trace_acyclic!{ <T> std::rc::Weak<[T]> }
trace_acyclic!{
    std::rc::Rc<std::ffi::CStr>,
    std::rc::Rc<std::ffi::OsStr>,
    std::rc::Rc<std::path::Path>,
    std::rc::Weak<std::ffi::CStr>,
    std::rc::Weak<std::ffi::OsStr>,
    std::rc::Weak<std::path::Path>
}

// See comment in Mutex for why this is acyclic.
trace_acyclic!{ <T> std::sync::Arc<T> }
trace_acyclic!{ <T> std::sync::Weak<T> }
trace_acyclic!{ <T> std::sync::Arc<[T]> }
trace_acyclic!{ <T> std::sync::Weak<[T]> }
trace_acyclic!{
    std::sync::Arc<std::ffi::CStr>,
    std::sync::Arc<std::ffi::OsStr>,
    std::sync::Arc<std::path::Path>,
    std::sync::Weak<std::ffi::CStr>,
    std::sync::Weak<std::ffi::OsStr>,
    std::sync::Weak<std::path::Path>
}

impl<T: Trace> Trace for std::sync::Mutex<T> {
    fn trace(&self, tracer: &mut Tracer) {
        // For single-thread collector (ObjectSpace):
        // Locking is optional. See RefCell.
        //
        // For multi-thread collector (ThreadedObjectSpace):
        // `ThreadedCcRef` is expected to be the only way to access a `T`
        // stored in `ThreadedCc<T>`. `ThreadedCcRef` takes a lock so
        // collector does not run. When the collector runs, `ThreadedCcRef`
        // are dropped so locks are released.
        // A special is when `T` is `Arc<Mutex<M>>`. It allows mutating `M`
        // without going through `ThreadedCcRef`. This is handled by marking
        // `Arc` as acyclic. The collector only cares about `trace`, and
        // `trace` result for an `Arc` cannot be changed by another thread,
        // even if `M` is mutable.
        if let Ok(x) = self.try_lock() {
            x.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

impl<T: Trace> Trace for std::sync::RwLock<T> {
    fn trace(&self, tracer: &mut Tracer) {
        // See Mutex for why locking is optional.
        //
        // If read or write locks are already taken, that indicates
        // outstanding references that keeps the objects alive.
        if let Ok(x) = self.try_write() {
            x.trace(tracer);
        }
    }

    #[inline]
    fn is_type_tracked() -> bool {
        T::is_type_tracked()
    }
}

trace_fn_acyclic!{}
trace_fn_acyclic!{ A }
trace_fn_acyclic!{ A, B }
trace_fn_acyclic!{ A, B, C }
trace_fn_acyclic!{ A, B, C, D }
trace_fn_acyclic!{ A, B, C, D, E }
trace_fn_acyclic!{ A, B, C, D, E, F }
trace_fn_acyclic!{ A, B, C, D, E, F, G }
trace_fn_acyclic!{ A, B, C, D, E, F, G, H }
trace_fn_acyclic!{ A, B, C, D, E, F, G, H, I }
trace_fn_acyclic!{ A, B, C, D, E, F, G, H, I, J }
trace_fn_acyclic!{ A, B, C, D, E, F, G, H, I, J, K }
trace_fn_acyclic!{ A, B, C, D, E, F, G, H, I, J, K, L }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Cc;
    use std::cell::{Cell, RefCell};
    use std::rc::Rc;

    #[test]
    fn test_is_type_tracked() {
        assert!(!u8::is_type_tracked());
        assert!(!<f32 as Trace>::is_type_tracked());
        assert!(!String::is_type_tracked());
        assert!(!Option::<u32>::is_type_tracked());
        assert!(!Vec::<u8>::is_type_tracked());
        assert!(!<(bool, f64)>::is_type_tracked());
        assert!(!Cell::<u32>::is_type_tracked());
        assert!(!RefCell::<String>::is_type_tracked());
        assert!(Box::<dyn Trace>::is_type_tracked());
        assert!(RefCell::<Box::<dyn Trace>>::is_type_tracked());
        assert!(RefCell::<Vec::<Box::<dyn Trace>>>::is_type_tracked());
        assert!(Vec::<RefCell::<Box::<dyn Trace>>>::is_type_tracked());
        assert!(!Cc::<u8>::is_type_tracked());
        assert!(!Vec::<Cc::<u8>>::is_type_tracked());

        assert!(!<fn(u8) -> u8>::is_type_tracked());
    }

    #[test]
    fn test_is_cyclic_type_tracked() {
        type C1 = RefCell<Option<Rc<Box<S1>>>>;
        struct S1(C1);
        impl Trace for S1 {
            fn trace(&self, t: &mut Tracer) {
                self.0.trace(t);
            }
            fn is_type_tracked() -> bool {
                // This is not an infinite loop because Rc is not tracked.
                C1::is_type_tracked()
            }
        }

        type C2 = RefCell<Option<Cc<Box<S2>>>>;
        struct S2(C2);
        impl Trace for S2 {
            fn trace(&self, t: &mut Tracer) {
                self.0.trace(t);
            }
            fn is_type_tracked() -> bool {
                // C2::is_type_tracked() can cause an infinite loop.
                true
            }
        }

        assert!(!S1::is_type_tracked());
        assert!(S2::is_type_tracked());
    }
}
