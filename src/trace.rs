use crate::cc::GcHeader;

/// Callback function that serves as the parameter of
/// [`Trace::trace`](trait.Trace.html#method.trace).
pub type Tracer<'a> = dyn FnMut(&mut GcHeader) + 'a;

/// Defines how the cycle collector should collect a type.
pub trait Trace {
    /// Traverse through values referred by this value.
    ///
    /// For example, if `self.x` is a value referred by `self`,
    /// call `self.x.trace(tracer)`.
    ///
    /// Do not call the `trace` function directly.
    fn trace(&self, tracer: &mut Tracer) {
        let _ = tracer;
    }

    /// Whether this type should be tracked by the cycle collector.
    /// This provides an optimization that makes atomic types opt
    /// out the cycle collector.
    ///
    /// This is ideally an associated constant. However that is
    /// currently impossible due to compiler limitations.
    /// See https://doc.rust-lang.org/error-index.html#E0038.
    fn is_type_tracked(&self) -> bool {
        true
    }

    #[doc(hidden)]
    #[inline(never)]
    /// Name used for debugging purpose.
    fn debug_name(&self) -> &str {
        "<unnamed>"
    }
}
