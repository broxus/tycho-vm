#[cfg(test)]
#[macro_use]
extern crate tycho_asm_macros;
extern crate self as tycho_vm;

/// Prevents using `From::from` for plain error conversion.
macro_rules! ok {
    ($e:expr $(,)?) => {
        match $e {
            core::result::Result::Ok(val) => val,
            core::result::Result::Err(err) => return core::result::Result::Err(err),
        }
    };
}

macro_rules! vm_ensure {
    ($cond:expr, $($tt:tt)+) => {
        if $crate::__private::not($cond) {
            return Err(Box::new($crate::error::VmError::$($tt)+));
        }
    };
}

macro_rules! vm_bail {
    ($($tt:tt)*) => {
        return Err(Box::new($crate::error::VmError::$($tt)*))
    };
}

/// Tuple builder.
#[macro_export]
macro_rules! tuple {
    ($($tt:tt)*) => {
        $crate::tuple_impl!(@v [] $($tt)*)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! tuple_impl {
    (@v [$($values:tt)*] null $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [$($values)* $crate::Stack::make_null(), ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] nan $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [$($values)* $crate::Stack::make_nan(), ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] int $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::RcStackValue::new_dyn_value(
                $crate::__export::num_bigint::BigInt::from($value)
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] cell $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::SafeRc::into_dyn_value(
                $crate::SafeRc::<::tycho_types::cell::Cell>::new($value)
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] slice $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::RcStackValue::new_dyn_value(
                $crate::OwnedCellSlice::from($value)
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] builder $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::SafeRc::into_dyn_value(
                $crate::SafeRc::<::tycho_types::cell::CellBuilder>::new($value)
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] [ $($inner:tt)* ] $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::RcStackValue::new_dyn_value(
                $crate::tuple!($($inner)*)
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] raw $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::SafeRc::into_dyn_value($value),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] $(,)?) => {
        vec![$($values)*]
    };
}

#[cfg(test)]
#[macro_export]
macro_rules! assert_run_vm {
    (
        $($code:literal),+,
        $(c7: $c7_params:expr,)?
        $(gas: $gas_limit:expr,)?
        $(libs: $libs:expr,)?
        $(state: |$state:ident| $state_expr:expr,)?
        [$($origin_stack:tt)*] => [$($expected_stack:tt)*]
        $(, exit_code: $exit_code:literal)?
        $(,)?
    ) => {{
        let libs = $crate::assert_run_vm!(@libs $($libs)?);
        let mut output = $crate::tests::TracingOutput::default();
        let (exit_code, vm) = $crate::tests::run_vm_with_stack(
            tvmasm!($($code),+),
            $crate::assert_run_vm!(@c7 $($c7_params)?),
            $crate::tuple![$($origin_stack)*],
            $crate::assert_run_vm!(@gas $($gas_limit)?),
            &libs,
            $crate::assert_run_vm!(@state $($state $state_expr)?),
            &mut output,
        );

        vm_log_trace!(
            "test vm finished: res={exit_code}, steps={}, gas={}",
            vm.steps,
            vm.gas.consumed(),
        );

        $crate::assert_run_vm!(@check_exit_code exit_code $($exit_code)?);

        let expected_stack = $crate::tuple![$($expected_stack)*];

        let expected = format!("{}", (&expected_stack as &dyn $crate::stack::StackValue).display_list());
        let actual = format!("{}", (&vm.stack.items as &dyn $crate::stack::StackValue).display_list());
        assert_eq!(actual, expected);

        $crate::tests::compare_stack(&vm.stack.items, &expected_stack);
    }};
    (@check_exit_code $ident:ident) => {
        assert_eq!($ident, 0, "non-zero exit code")
    };
    (@check_exit_code $ident:ident $exit_code:literal) => {
        assert_eq!($ident, $exit_code, "exit code mismatch")
    };
    (@c7) => {
        $crate::tuple![]
    };
    (@c7 $c7_params:expr) => {
        $c7_params
    };
    (@gas) => {
        1000000
    };
    (@gas $gas_limit:expr) => {
        $gas_limit
    };
    (@libs) => {
        $crate::NoLibraries
    };
    (@libs $libs:expr) => {
        $libs
    };
    (@state) => {
        |_| {}
    };
    (@state $state:ident $state_expr:expr) => {
        |$state| $state_expr
    };
}

pub use self::cont::{
    AgainCont, ArgContExt, Cont, ControlData, ControlRegs, ExcQuitCont, OrdCont, PushIntCont,
    QuitCont, RcCont, RepeatCont, UntilCont, WhileCont,
};
pub use self::dispatch::{
    DispatchTable, FnExecInstrArg, FnExecInstrFull, FnExecInstrSimple, OpcodeBase, OpcodeExec,
    Opcodes,
};
#[cfg(feature = "dump")]
pub use self::dispatch::{
    DumpOutput, FnDumpInstrArg, FnDumpInstrFull, FnDumpInstrSimple, OpcodeDump,
};
#[cfg(feature = "dump")]
pub use self::error::{DumpError, DumpResult};
pub use self::error::{VmError, VmException, VmResult};
pub use self::gas::{
    GasConsumer, GasConsumerDeriveParams, GasParams, LibraryProvider, LimitedGasConsumer,
    NoLibraries, ParentGasConsumer, RestoredGasConsumer,
};
pub use self::instr::{codepage, codepage0};
#[cfg(feature = "tracing")]
pub use self::log::{VM_LOG_TARGET, VmLogRows, VmLogRowsGuard, VmLogSubscriber};
pub use self::saferc::{SafeDelete, SafeRc, SafeRcMakeMut};
pub use self::smc_info::{
    CustomSmcInfo, SmcInfo, SmcInfoBase, SmcInfoTonV4, SmcInfoTonV6, SmcInfoTonV11, UnpackedConfig,
    UnpackedInMsgSmcInfo, VmVersion,
};
pub use self::stack::{
    NaN, RcStackValue, Stack, StackValue, StackValueType, StaticStackValue, Tuple, TupleExt,
};
#[cfg(feature = "tracing")]
pub use self::state::VmLogMask;
pub use self::state::{
    BehaviourModifiers, CommittedState, InitSelectorParams, IntoCode, ParentVmState, SaveCr,
    VmState, VmStateBuilder,
};
pub use self::util::OwnedCellSlice;

#[macro_use]
mod log;

mod cont;
mod dispatch;
mod error;
mod gas;
mod instr;
mod saferc;
mod smc_info;
mod stack;
mod state;
mod util;

#[doc(hidden)]
pub mod __export {
    pub use {num_bigint, tycho_types};
}

#[doc(hidden)]
mod __private {
    use self::not::Bool;

    #[doc(hidden)]
    #[inline]
    pub fn not(cond: impl Bool) -> bool {
        cond.not()
    }

    mod not {
        #[doc(hidden)]
        pub trait Bool {
            fn not(self) -> bool;
        }

        impl Bool for bool {
            #[inline]
            fn not(self) -> bool {
                !self
            }
        }

        impl Bool for &bool {
            #[inline]
            fn not(self) -> bool {
                !*self
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use tracing_test::traced_test;
    use tycho_types::models::{CurrencyCollection, SimpleLib, StdAddr};
    use tycho_types::prelude::*;

    use super::*;
    use crate::stack::{RcStackValue, Tuple};

    pub fn run_vm_with_stack<'a, I>(
        code: &[u8],
        c7_params: Tuple,
        original_stack: I,
        gas_limit: u64,
        libs: &'a impl LibraryProvider,
        modify_state: impl FnOnce(&mut VmState),
        output: &'a mut impl std::fmt::Write,
    ) -> (i32, VmState<'a>)
    where
        I: IntoIterator<Item = RcStackValue>,
    {
        let code = Boc::decode(code).unwrap();

        let mut vm = VmState::builder()
            .with_code(code)
            .with_libraries(libs)
            .with_smc_info(CustomSmcInfo {
                version: VmState::DEFAULT_VERSION,
                c7: SafeRc::new(c7_params),
            })
            .with_debug(output)
            .with_stack(original_stack)
            .with_gas(GasParams {
                max: gas_limit,
                limit: gas_limit,
                credit: 0,
                ..GasParams::getter()
            })
            .build();

        modify_state(&mut vm);

        let exit_code = !vm.run();

        (exit_code, vm)
    }

    #[track_caller]
    pub fn compare_stack(actual: &Tuple, expected: &Tuple) {
        let cx = Cell::empty_context();

        let actual_stack = {
            let mut b = CellBuilder::new();
            actual.store_as_stack_value(&mut b, cx).unwrap();
            b.build_ext(cx).unwrap()
        };

        let expected_stack = {
            let mut b = CellBuilder::new();
            expected.store_as_stack_value(&mut b, cx).unwrap();
            b.build_ext(cx).unwrap()
        };

        assert_eq!(actual_stack, expected_stack, "stack mismatch");
    }

    #[test]
    #[traced_test]
    fn dispatch_works() {
        let code = Boc::decode(tvmasm!(
            "PUSHINT 0",
            "PUSHINT 1",
            "PUSHINT 2",
            "NOP",
            "PUSHNAN",
            "DEBUG 0",
            "XCHG s0, s3",
            "XCHG s1, s3",
            "PUXC s1, s2",
            "DUP",
            "OVER",
            "PUSH s3",
            "DROP",
            "NIP",
            "POP s3",
            "XCHG3 s1, s2, s3",
            "XCHG2 s1, s2",
            "XCPU s1, s2",
            "PUXC s1, s0",
            "PUSH2 s3, s4",
            "XCHG3 s3, s4, s0",
            "PUXC2 s3, s1, s0",
            "PUSH3 s1, s2, s3",
            "PU2XC s1, s2, s(-2)",
            "BLKSWAP 1, 2",
            "DEBUG 0",
            "DEBUGSTR x{48454c50313233}",
        ))
        .unwrap();

        let mut output = TracingOutput::default();
        let mut vm = VmState::builder()
            .with_code(code)
            .with_debug(&mut output)
            .build();
        let exit_code = !vm.run();
        println!("Exit code: {exit_code}");
    }

    #[test]
    #[traced_test]
    fn library_cells_works() -> anyhow::Result<()> {
        let library = Boc::decode_base64(
            "te6ccuECDwEAA9EAABoAJAEkAS4CJgL+A5wEVAVSBkoGrgcsB1EHfAeiART/APSkE/S88sgLAQIBYgIDAvjQAdDTAwFxsI5IE18DgCDXIe1E0NMD+gD6QPpA0QTTHwGEDyGCEBeNRRm6AoIQe92X3roSsfL0gEDXIfoAMBKgQBMDyMsDWPoCAc8WAc8Wye1U4PpA+kAx+gAx9AH6ADH6AAExcPg6AtMfASCCEA+KfqW6joUwNFnbPOAzBAUCASANDgHyA9M/AQH6APpAIfpEMMAA8uFN7UTQ0wP6APpA+kDRUwnHBSRxsMAAIbHyrVIrxwVQCrHy4ElRFaEgwv/yr/gqVCWQcFRgBBMVA8jLA1j6AgHPFgHPFskhyMsBE/QAEvQAywDJIPkAcHTIywLKB8v/ydAE+kD0AfoAIAYC0CKCEBeNRRm6joQyWts84DQhghBZXwe8uo6EMQHbPOAyIIIQ7tI207qOLzABgEDXIdMD0e1E0NMD+gD6QPpA0TNRQscF8uBKQDMDyMsDWPoCAc8WAc8Wye1U4GwhghDTchWMutyED/LwCAkBmCDXCwCa10vAAQHAAbDysZEw4siCEBeNRRkByx9QCgHLP1AI+gIjzxYBzxYm+gJQB88WyciAGAHLBVAEzxZw+gJAY3dQA8trzMzJRTcHALQhkXKRceL4OSBuk4EkJ5Eg4iFulDGBKHORAeJQI6gToHOBA6Nw+DygAnD4NhKgAXD4NqBzgQQJghAJZgGAcPg3oLzysASAUPsAWAPIywNY+gIBzxYBzxbJ7VQD9O1E0NMD+gD6QPpA0SNysMAC8m0H0z8BAfoAUUGgBPpA+kBTuscF+CpUZOBwVGAEExUDyMsDWPoCAc8WAc8WySHIywET9AAS9ADLAMn5AHB0yMsCygfL/8nQUAzHBRux8uBKCfoAIZJfBOMNJtcLAcAAs5MwbDPjDVUCCgsMAfLtRNDTA/oA+kD6QNEG0z8BAfoA+kD0AdFRQaFSiMcF8uBJJsL/8q/IghB73ZfeAcsfWAHLPwH6AiHPFljPFsnIgBgBywUmzxZw+gIBcVjLaszJA/g5IG6UMIEWn95xgQLycPg4AXD4NqCBGndw+DagvPKwAoBQ+wADDABgyIIQc2LQnAHLHyUByz9QBPoCWM8WWM8WyciAEAHLBSTPFlj6AgFxWMtqzMmAEfsAAHpQVKH4L6BzgQQJghAJZgGAcPg3tgly+wLIgBABywVQBc8WcPoCcAHLaoIQ1TJ22wHLH1gByz/JgQCC+wBZACADyMsDWPoCAc8WAc8Wye1UACe/2BdqJoaYH9AH0gfSBomfwVIJhAAhvFCPaiaGmB/QB9IH0gaK+Bz+s3AU",
        )?;
        let libraries = HashMap::from([(
            "8f452d7a4dfd74066b682365177259ed05734435be76b5fd4bd5d8af2b7c3d68"
                .parse::<HashBytes>()?,
            SimpleLib {
                public: true,
                root: library,
            },
        )]);

        let addr = "0:2626CF30B702BDDED845EFC883EFA45029FF59DEFDACC4CE7B8B0A5966D75002"
            .parse::<StdAddr>()?;

        let mut code =
            Boc::decode_base64("te6ccgEBAQEAIwAIQgKPRS16Tf10BmtoI2UXclntBXNENb52tf1L1divK3w9aA==")?;

        let data = Boc::decode_base64(
            "te6ccgEBAQEATAAAkwYKW203ZzmABH9S8yMeP84FtyIBfwh9D44CvZmnNI5D0211guF4CZxwAsROplLUCShZxn2kTkyjrdZWWw4ol9ZAosUb+zcNiHf6",
        )?;

        let smc_info = SmcInfoBase::new()
            .with_now(1733142533)
            .with_block_lt(52499545000000)
            .with_tx_lt(52499545000005)
            .with_account_balance(CurrencyCollection::new(5981380))
            .with_account_addr(addr.clone().into())
            .require_ton_v4();

        if code.is_exotic() {
            code = CellBuilder::build_from(code)?;
        }

        let mut output = TracingOutput::default();
        let mut vm_state = VmState::builder()
            .with_smc_info(smc_info)
            .with_stack(tuple![
                int 97026, // get_wallet_data
            ])
            .with_code(code)
            .with_data(data)
            .with_gas(GasParams::getter())
            .with_debug(&mut output)
            .with_libraries(&libraries)
            .build();

        assert_eq!(vm_state.run(), -1);
        Ok(())
    }

    #[test]
    #[traced_test]
    fn recursive_libraries() -> anyhow::Result<()> {
        fn make_lib(code: &DynCell) -> Cell {
            let mut b = CellBuilder::new();
            b.set_exotic(true);
            b.store_u8(CellType::LibraryReference.to_byte()).unwrap();
            b.store_u256(code.repr_hash()).unwrap();
            b.build().unwrap()
        }

        let leaf_lib = Boc::decode(tvmasm!("NOP"))?;
        let lib1 = make_lib(leaf_lib.as_ref());
        let lib2 = make_lib(lib1.as_ref());

        let libraries = HashMap::from([
            (*leaf_lib.repr_hash(), SimpleLib {
                public: true,
                root: leaf_lib,
            }),
            (*lib1.repr_hash(), SimpleLib {
                public: true,
                root: lib1,
            }),
            (*lib2.repr_hash(), SimpleLib {
                public: true,
                root: lib2.clone(),
            }),
        ]);

        let code = CellBuilder::build_from(lib2)?;

        let smc_info = SmcInfoBase::new()
            .with_now(1733142533)
            .with_block_lt(52499545000000)
            .with_tx_lt(52499545000005)
            .with_account_balance(CurrencyCollection::new(5981380))
            .with_account_addr(Default::default())
            .require_ton_v4();

        let mut output = TracingOutput::default();
        let mut vm_state = VmState::builder()
            .with_smc_info(smc_info)
            .with_code(code)
            .with_gas(GasParams::getter())
            .with_debug(&mut output)
            .with_libraries(&libraries)
            .build();

        assert_eq!(vm_state.run(), -10); // cell underflow
        Ok(())
    }

    #[derive(Default)]
    pub struct TracingOutput {
        buffer: String,
    }

    impl std::fmt::Write for TracingOutput {
        fn write_str(&mut self, mut s: &str) -> std::fmt::Result {
            while !s.is_empty() {
                match s.split_once('\n') {
                    None => {
                        self.buffer.push_str(s);
                        return Ok(());
                    }
                    Some((prefix, rest)) => {
                        tracing::debug!("{}{prefix}", self.buffer);
                        self.buffer.clear();
                        s = rest;
                    }
                }
            }
            Ok(())
        }
    }
}
