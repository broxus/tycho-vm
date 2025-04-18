#[cfg(feature = "tracing")]
pub use self::subscriber::{VmLogRows, VmLogRowsGuard, VmLogSubscriber};

/// Tracing target used by VM logs.
#[cfg(feature = "tracing")]
pub const VM_LOG_TARGET: &str = "tycho_vm";

#[cfg(feature = "tracing")]
macro_rules! vm_log_op {
    ($($tt:tt)*) => { $crate::log::__log_op(format_args!($($tt)*)) };
}

#[cfg(feature = "tracing")]
pub(crate) fn __log_op(args: std::fmt::Arguments<'_>) {
    tracing::trace!(target: VM_LOG_TARGET, opcode = %args);
}

#[cfg(not(feature = "tracing"))]
macro_rules! vm_log_op {
    ($($tt:tt)*) => {{}};
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_stack {
    ($stack:expr, $verbose:expr) => {
        tracing::trace!(
            target: $crate::log::VM_LOG_TARGET,
            stack = %$stack.display_dump($verbose),
        );
    };
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_exec_location {
    ($cell:expr, $offset_bits:expr, $offset_refs:expr) => {
        tracing::trace!(
            target: $crate::log::VM_LOG_TARGET,
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
            target: $crate::log::VM_LOG_TARGET,
            gas_remaining = %$gas,
        )
    };
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_gas_consumed {
    ($gas:expr) => {
        tracing::trace!(
            target: $crate::log::VM_LOG_TARGET,
            gas_used = %$gas,
        )
    };
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_c5 {
    ($c5:expr) => {
        tracing::trace!(
            target: $crate::log::VM_LOG_TARGET,
            c5 = ::everscale_types::boc::Boc::encode_base64($c5),
        )
    };
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_trace {
    ($($tt:tt)*) => {
        tracing::trace!(
            target: $crate::log::VM_LOG_TARGET,
            $($tt)*
        )
    };
}

#[cfg(not(feature = "tracing"))]
macro_rules! vm_log_trace {
    ($($tt:tt)*) => {{}};
}

#[cfg(feature = "tracing")]
mod subscriber {
    use std::collections::VecDeque;
    use std::num::NonZeroU64;
    use std::sync::{Arc, Mutex};

    use tracing::{span, Subscriber};

    use super::VM_LOG_TARGET;
    use crate::state::VmLogMask;

    /// Tracing subscriber which intercepts all VM logs and collets it into [`VmLogRows`].
    ///
    /// # Example
    /// ```rust
    /// # use tycho_vm::{VmLogSubscriber, VmLogMask};
    /// # fn main() {
    /// let subscriber = VmLogSubscriber::new(VmLogMask::FULL, 128);
    /// let log_rows = subscriber.rows().clone();
    /// {
    ///     let _tracing = tracing::subscriber::set_default(subscriber);
    ///     // ...run vm...
    /// }
    /// println!("{}", log_rows);
    /// #}
    /// ```
    pub struct VmLogSubscriber {
        vm_log_mask: VmLogMask,
        state: VmLogRows,
    }

    impl VmLogSubscriber {
        pub fn new(mask: VmLogMask, capacity: usize) -> Self {
            Self {
                vm_log_mask: mask,
                state: VmLogRows {
                    inner: Arc::new(Mutex::new(Inner {
                        capacity,
                        rows: VecDeque::with_capacity(capacity.min(256)),
                    })),
                },
            }
        }

        pub fn rows(&self) -> &VmLogRows {
            &self.state
        }
    }

    impl Subscriber for VmLogSubscriber {
        fn enabled(&self, metadata: &tracing::Metadata<'_>) -> bool {
            metadata.target() == VM_LOG_TARGET
        }

        fn new_span(&self, _: &span::Attributes<'_>) -> span::Id {
            span::Id::from_non_zero_u64(NonZeroU64::MIN)
        }

        fn record(&self, _: &span::Id, _: &span::Record<'_>) {}

        fn record_follows_from(&self, _: &span::Id, _: &span::Id) {}

        fn event(&self, event: &tracing::Event<'_>) {
            if !self.enabled(event.metadata()) {
                return;
            }

            event.record(&mut LogVisitor {
                inner: &mut self.state.inner.lock().unwrap(),
                mask: self.vm_log_mask,
            });
        }

        fn enter(&self, _: &span::Id) {}

        fn exit(&self, _: &span::Id) {}
    }

    struct LogVisitor<'a> {
        inner: &'a mut Inner,
        mask: VmLogMask,
    }

    impl tracing::field::Visit for LogVisitor<'_> {
        fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
            use std::fmt::Write;

            const STACK_MASK: VmLogMask =
                VmLogMask::DUMP_STACK.union(VmLogMask::DUMP_STACK_VERBOSE);

            let mut buffer = self.inner.get_buffer();

            let res = match field.name() {
                "message" if self.mask.contains(VmLogMask::MESSAGE) => {
                    write!(&mut buffer, "{value:?}")
                }
                "opcode" if self.mask.contains(VmLogMask::MESSAGE) => {
                    write!(&mut buffer, "execute {value:?}")
                }
                "stack" if self.mask.intersects(STACK_MASK) => {
                    write!(&mut buffer, "stack: {value:?}")
                }
                "exec_location" if self.mask.contains(VmLogMask::EXEC_LOCATION) => {
                    write!(&mut buffer, "code cell hash: {value:?}")
                }
                "gas_remaining" if self.mask.contains(VmLogMask::GAS_REMAINING) => {
                    write!(&mut buffer, "gas remaining: {value:?}")
                }
                "gas_consumed" if self.mask.contains(VmLogMask::GAS_CONSUMED) => {
                    write!(&mut buffer, "gas consumed: {value:?}")
                }
                "c5" if self.mask.contains(VmLogMask::DUMP_C5) => {
                    write!(&mut buffer, "c5: {value:?}")
                }
                _ => return,
            };

            if res.is_ok() {
                self.inner.rows.push_back(buffer);
            }
        }
    }

    /// VM log output from [`VmLogSubscriber`].
    #[derive(Clone)]
    pub struct VmLogRows {
        inner: Arc<Mutex<Inner>>,
    }

    impl VmLogRows {
        pub fn lock(&self) -> VmLogRowsGuard<'_> {
            VmLogRowsGuard {
                inner: self.inner.lock().unwrap(),
            }
        }
    }

    impl std::fmt::Display for VmLogRows {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let mut inner = self.inner.lock().unwrap();
            for row in std::mem::take(&mut inner.rows) {
                writeln!(f, "{row}")?;
            }
            Ok(())
        }
    }

    /// Mutex guard for [`VmLogRows`].
    pub struct VmLogRowsGuard<'a> {
        inner: std::sync::MutexGuard<'a, Inner>,
    }

    impl std::ops::Deref for VmLogRowsGuard<'_> {
        type Target = VecDeque<String>;

        #[inline]
        fn deref(&self) -> &Self::Target {
            &self.inner.rows
        }
    }

    struct Inner {
        capacity: usize,
        rows: VecDeque<String>,
    }

    impl Inner {
        fn get_buffer(&mut self) -> String {
            const OK_LEN: usize = 128;

            if self.rows.len() >= self.capacity {
                if let Some(mut s) = self.rows.pop_front() {
                    if s.len() <= OK_LEN {
                        s.clear();
                        return s;
                    }
                }
            }

            String::new()
        }
    }
}
