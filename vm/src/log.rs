#[cfg(feature = "tracing")]
pub(crate) const TARGET: &str = "tycho_vm";

#[cfg(feature = "tracing")]
macro_rules! vm_log_op {
    ($($tt:tt)*) => { $crate::log::__log_op(format_args!($($tt)*)) };
}

#[cfg(feature = "tracing")]
pub(crate) fn __log_op(args: std::fmt::Arguments<'_>) {
    tracing::trace!(target: TARGET, opcode = %args);
}

#[cfg(not(feature = "tracing"))]
macro_rules! vm_log_op {
    ($($tt:tt)*) => {{}};
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_stack {
    ($stack:expr, $verbose:expr) => {
        tracing::trace!(
            target: $crate::log::TARGET,
            stack = %$stack.display_dump($verbose),
        );
    };
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_exec_location {
    ($cell:expr, $offset_bits:expr, $offset_refs:expr) => {
        tracing::trace!(
            target: $crate::log::TARGET,
            exec_location=%$crate::log::CodePosition {
                cell_hash: $cell.repr_hash(),
                offset_bits: $offset_bits,
                offset_refs: $offset_refs,
            },
        );
    };
}

#[cfg(feature = "tracing")]
pub(crate) struct CodePosition<'a> {
    pub cell_hash: &'a ::everscale_types::cell::HashBytes,
    pub offset_bits: u16,
    pub offset_refs: u8,
}

#[cfg(feature = "tracing")]
impl std::fmt::Display for CodePosition<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}",
            self.cell_hash, self.offset_bits, self.offset_refs
        )
    }
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_gas_remaining {
    ($gas:expr) => {
        tracing::trace!(
            target: $crate::log::TARGET,
            gas_remaining = %$gas,
        )
    };
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_c5 {
    ($c5:expr) => {
        tracing::trace!(
            target: $crate::log::TARGET,
            c5 = ::everscale_types::boc::Boc::encode_base64($c5),
        )
    };
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_trace {
    ($($tt:tt)*) => {
        tracing::trace!(
            target: $crate::log::TARGET,
            $($tt)*
        )
    };
}

#[cfg(not(feature = "tracing"))]
macro_rules! vm_log_trace {
    ($($tt:tt)*) => {{}};
}
