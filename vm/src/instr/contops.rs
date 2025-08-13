use tycho_types::prelude::*;
use tycho_vm_proc::vm_module;

use crate::cont::{ArgContExt, ControlData, ControlRegs, OrdCont, PushIntCont, RcCont};
#[cfg(feature = "dump")]
use crate::dispatch::DumpOutput;
use crate::error::VmResult;
#[cfg(feature = "dump")]
use crate::error::{DumpError, DumpResult};
use crate::gas::{GasConsumer, GasConsumerDeriveParams};
use crate::instr::codepage0;
use crate::saferc::SafeRc;
use crate::stack::{Stack, StackValueType};
use crate::state::{EXC_QUIT, ParentVmState, QUIT0, QUIT1, QUIT11, SaveCr, VmState};

pub struct ContOps;

#[vm_module]
impl ContOps {
    // === Jump ops ===

    #[op(code = "d8", fmt = "EXECUTE")]
    fn exec_execute(st: &mut VmState) -> VmResult<i32> {
        let cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        st.call(cont)
    }

    #[op(code = "d9", fmt = "JMPX")]
    fn exec_jmpx(st: &mut VmState) -> VmResult<i32> {
        let cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        st.jump(cont)
    }

    #[op(code = "dapr", fmt = "CALLXARGS {p},{r}")]
    fn exec_callx_args(st: &mut VmState, p: u32, r: u32) -> VmResult<i32> {
        let cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        st.call_ext(cont, Some(p as _), Some(r as _))
    }

    #[op(code = "db0p", fmt = "CALLXARGS {p},-1")]
    fn exec_callx_args_p(st: &mut VmState, p: u32) -> VmResult<i32> {
        let cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        st.call_ext(cont, Some(p as _), None)
    }

    #[op(code = "db1p", fmt = "JMPXARGS {p}")]
    fn exec_jmpx_args(st: &mut VmState, p: u32) -> VmResult<i32> {
        let cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        st.jump_ext(cont, Some(p as _))
    }

    #[op(code = "db2r", fmt = "RETARGS {r}")]
    fn exec_ret_args(st: &mut VmState, r: u32) -> VmResult<i32> {
        st.ret_ext(Some(r as _))
    }

    #[op(code = "db30", fmt = "RET")]
    fn exec_ret(st: &mut VmState) -> VmResult<i32> {
        st.ret()
    }

    #[op(code = "db31", fmt = "RETALT")]
    fn exec_ret_alt(st: &mut VmState) -> VmResult<i32> {
        st.ret_alt()
    }

    #[op(code = "db32", fmt = "RETBOOL")]
    fn exec_ret_bool(st: &mut VmState) -> VmResult<i32> {
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            st.ret()
        } else {
            st.ret_alt()
        }
    }

    #[op(code = "db34", fmt = "CALLCC")]
    fn exec_callcc(st: &mut VmState) -> VmResult<i32> {
        let cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        let cc = ok!(st.extract_cc(SaveCr::C0_C1, None, None));
        ok!(SafeRc::make_mut(&mut st.stack).push_raw(cc));
        st.jump(cont)
    }

    #[op(code = "db35", fmt = "JMPXDATA")]
    fn exec_jmpx_data(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        ok!(stack.push(st.code.clone()));
        st.jump(cont)
    }

    #[op(code = "db36pr", fmt = "CALLCCARGS {p},{r}", args(r = ((args as i32 + 1) & 0xf) - 1))]
    fn exec_callcc_args(st: &mut VmState, p: u32, r: i32) -> VmResult<i32> {
        let cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        let cc = ok!(st.extract_cc(SaveCr::C0_C1, Some(p as _), (r >= 0).then_some(r as _)));
        ok!(SafeRc::make_mut(&mut st.stack).push_raw(cc));
        st.jump(cont)
    }

    #[op(code = "db38", fmt = "CALLXVARARGS")]
    fn exec_callx_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let r = ok!(stack.pop_smallint_signed_range(-1, 254));
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont());
        st.call_ext(cont, (p >= 0).then_some(p as _), (r >= 0).then_some(r as _))
    }

    #[op(code = "db39", fmt = "RETVARARGS")]
    fn exec_ret_varargs(st: &mut VmState) -> VmResult<i32> {
        let r = ok!(SafeRc::make_mut(&mut st.stack).pop_smallint_signed_range(-1, 254));
        st.ret_ext((r >= 0).then_some(r as _))
    }

    #[op(code = "db3a", fmt = "JMPXVARARGS")]
    fn exec_jmpx_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont());
        st.jump_ext(cont, (p >= 0).then_some(p as _))
    }

    #[op(code = "db3b", fmt = "CALLCCVARARGS")]
    fn exec_callcc_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let r = ok!(stack.pop_smallint_signed_range(-1, 254));
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont());
        let cc = ok!(st.extract_cc(
            SaveCr::C0_C1,
            (p >= 0).then_some(p as _),
            (r >= 0).then_some(r as _)
        ));
        ok!(SafeRc::make_mut(&mut st.stack).push_raw(cc));
        st.jump(cont)
    }

    #[op_ext(code = 0xdb3c, code_bits = 16, arg_bits = 0, dump_with = dump_callref)]
    fn exec_callref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "CALLREF"));
        st.call(cont)
    }

    #[cfg(feature = "dump")]
    fn dump_callref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "CALLREF", f)
    }

    #[op_ext(code = 0xdb3d, code_bits = 16, arg_bits = 0, dump_with = dump_jmpref)]
    fn exec_jmpref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "JMPREF"));
        st.jump(cont)
    }

    #[cfg(feature = "dump")]
    fn dump_jmpref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "JMPREF", f)
    }

    #[op_ext(code = 0xdb3e, code_bits = 16, arg_bits = 0, dump_with = dump_jmpref_data)]
    fn exec_jmpref_data(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "JMPREFDATA"));
        ok!(SafeRc::make_mut(&mut st.stack).push(st.code.clone()));
        st.jump(cont)
    }

    #[cfg(feature = "dump")]
    fn dump_jmpref_data(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "JMPREFDATA", f)
    }

    #[op(code = "db3f", fmt = "RETDATA")]
    fn exec_ret_data(st: &mut VmState) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push(st.code.clone()));
        st.ret()
    }

    #[op(code = "db4xxx", fmt = "RUNVM {x}")]
    fn exec_runvm(st: &mut VmState, x: u32) -> VmResult<i32> {
        exec_runvm_common(st, RunVmArgs(x))
    }

    #[op(code = "db50", fmt = "RUNVMX")]
    fn exec_runvmx(st: &mut VmState) -> VmResult<i32> {
        let x = ok!(SafeRc::make_mut(&mut st.stack).pop_smallint_range(0, 0xfff));
        exec_runvm_common(st, RunVmArgs(x))
    }

    // === Conditions and loops ===

    #[op(code = "dc", fmt = "IFRET")]
    fn exec_ifret(st: &mut VmState) -> VmResult<i32> {
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            st.ret()
        } else {
            Ok(0)
        }
    }

    #[op(code = "dd", fmt = "IFNOTRET")]
    fn exec_ifnotret(st: &mut VmState) -> VmResult<i32> {
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            st.ret()
        }
    }

    #[op(code = "de", fmt = "IF")]
    fn exec_if(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        if ok!(stack.pop_bool()) {
            st.call(cont)
        } else {
            Ok(0)
        }
    }

    #[op(code = "df", fmt = "IFNOT")]
    fn exec_ifnot(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        if ok!(stack.pop_bool()) {
            Ok(0)
        } else {
            st.call(cont)
        }
    }

    #[op(code = "e0", fmt = "IFJMP")]
    fn exec_if_jmp(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        if ok!(stack.pop_bool()) {
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    #[op(code = "e1", fmt = "IFNOTJMP")]
    fn exec_ifnot_jmp(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        if ok!(stack.pop_bool()) {
            Ok(0)
        } else {
            st.jump(cont)
        }
    }

    #[op(code = "e2", fmt = "IFELSE")]
    fn exec_if_else(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cont = {
            let cont0 = ok!(stack.pop_cont());
            let cont1 = ok!(stack.pop_cont());
            match ok!(stack.pop_bool()) {
                false => cont0,
                true => cont1,
            }
        };
        st.call(cont)
    }

    #[op_ext(code = 0xe300, code_bits = 16, arg_bits = 0, dump_with = dump_ifref)]
    fn exec_ifref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFREF"));
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            let cont = ok!(st.ref_to_cont(cell));
            st.call(cont)
        } else {
            Ok(0)
        }
    }

    #[cfg(feature = "dump")]
    fn dump_ifref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "IFREF", f)
    }

    #[op_ext(code = 0xe301, code_bits = 16, arg_bits = 0, dump_with = dump_ifnotref)]
    fn exec_ifnotref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFNOTREF"));
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            let cont = ok!(st.ref_to_cont(cell));
            st.call(cont)
        }
    }

    #[cfg(feature = "dump")]
    fn dump_ifnotref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "IFNOTREF", f)
    }

    #[op_ext(code = 0xe302, code_bits = 16, arg_bits = 0, dump_with = dump_ifjmpref)]
    fn exec_ifjmpref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFJMPREF"));
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            let cont = ok!(st.ref_to_cont(cell));
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    #[cfg(feature = "dump")]
    fn dump_ifjmpref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "IFJMPREF", f)
    }

    #[op_ext(code = 0xe303, code_bits = 16, arg_bits = 0, dump_with = dump_ifnotjmpref)]
    fn exec_ifnotjmpref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFNOTJMPREF"));
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            let cont = ok!(st.ref_to_cont(cell));
            st.jump(cont)
        }
    }

    #[cfg(feature = "dump")]
    fn dump_ifnotjmpref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "IFNOTJMPREF", f)
    }

    #[op(code = "e304", fmt = "CONDSEL")]
    fn exec_condsel(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop());
        let x = ok!(stack.pop());
        let cond = ok!(stack.pop_bool());
        ok!(stack.push_raw(match cond {
            true => x,
            false => y,
        }));
        Ok(0)
    }

    #[op(code = "e305", fmt = "CONDSELCHK")]
    fn exec_condsel_chk(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop());
        let x = ok!(stack.pop());
        vm_ensure!(x.raw_ty() == y.raw_ty(), InvalidType {
            expected: x.raw_ty(),
            actual: y.raw_ty(),
        });
        let cond = ok!(stack.pop_bool());
        ok!(stack.push_raw(match cond {
            true => x,
            false => y,
        }));
        Ok(0)
    }

    #[op(code = "e308", fmt = "IFRETALT")]
    fn exec_ifretalt(st: &mut VmState) -> VmResult<i32> {
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            st.ret_alt()
        } else {
            Ok(0)
        }
    }

    #[op(code = "e309", fmt = "IFNOTRETALT")]
    fn exec_ifnotretalt(st: &mut VmState) -> VmResult<i32> {
        if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            st.ret_alt()
        }
    }

    #[op_ext(code = 0xe30d, code_bits = 16, arg_bits = 0, dump_with = dump_ifrefelse)]
    fn exec_ifrefelse(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_ifelse_ref_impl(st, bits, true)
    }

    #[cfg(feature = "dump")]
    fn dump_ifrefelse(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "IFREFELSE", f)
    }

    #[op_ext(code = 0xe30e, code_bits = 16, arg_bits = 0, dump_with = dump_ifelseref)]
    fn exec_ifelseref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_ifelse_ref_impl(st, bits, false)
    }

    #[cfg(feature = "dump")]
    fn dump_ifelseref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_ref_prefix(code, bits, "IFELSEREF", f)
    }

    #[op_ext(code = 0xe30f, code_bits = 16, arg_bits = 0, dump_with = dump_ifref_elseref)]
    fn exec_ifref_elseref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = {
            let code = &mut st.code;
            vm_ensure!(code.range().has_remaining(bits, 2), InvalidOpcode);
            let ok = code.range_mut().skip_first(bits, 0).is_ok();
            debug_assert!(ok);

            let Some(cell1) = code.cell().reference_cloned(code.range().offset_refs()) else {
                vm_bail!(CellError(tycho_types::error::Error::CellUnderflow));
            };
            let ok = code.range_mut().skip_first(0, 1).is_ok();
            debug_assert!(ok);

            let Some(cell0) = code.cell().reference_cloned(code.range().offset_refs()) else {
                vm_bail!(CellError(tycho_types::error::Error::CellUnderflow));
            };
            let ok = code.range_mut().skip_first(0, 1).is_ok();
            debug_assert!(ok);

            vm_log_op!(
                "IFREFELSEREF ({}) ({})",
                cell1.repr_hash(),
                cell0.repr_hash()
            );

            match ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) {
                false => cell0,
                true => cell1,
            }
        };
        let cont = ok!(st.ref_to_cont(cell));
        st.call(cont)
    }

    #[cfg(feature = "dump")]
    fn dump_ifref_elseref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        if !code.has_remaining(bits, 2) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits, 0)?;

        let cell1 = code.load_reference_cloned()?;
        let cell0 = code.load_reference_cloned()?;

        f.record_cont(cell1.clone())?;
        f.record_cont(cell0.clone())?;

        f.record_opcode(&format_args!(
            "IFREFELSEREF ({}) ({})",
            cell1.repr_hash(),
            cell0.repr_hash()
        ))
    }

    #[op(code = "e3$10nx#x", fmt = ("IF{}BITJMP {x}", if n { "N" } else { "" }))]
    fn exec_if_bit_jmp(st: &mut VmState, n: bool, x: u32) -> VmResult<i32> {
        let (cont, bit) = {
            let stack = SafeRc::make_mut(&mut st.stack);
            let cont = ok!(stack.pop_cont());
            let value = ok!(stack.pop_int());
            let bit = value.bit(x as _);
            ok!(stack.push_raw(value));
            (cont, bit)
        };

        if bit ^ n { st.jump(cont) } else { Ok(0) }
    }

    #[op_ext(code = 0xe3c0 >> 6, code_bits = 10, arg_bits = 0, dump_with = dump_if_bit_jmpref)]
    fn exec_if_bit_jmpref(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let code_range = st.code.range();
        vm_ensure!(code_range.has_remaining(bits, 1), InvalidOpcode);
        let ok = st.code.range_mut().skip_first(bits, 0).is_ok();
        debug_assert!(ok);

        let Some(cell) = st.code.cell().reference_cloned(code_range.offset_refs()) else {
            vm_bail!(CellError(tycho_types::error::Error::CellUnderflow));
        };
        let ok = st.code.range_mut().skip_first(0, 1).is_ok();
        debug_assert!(ok);

        let negate = (args & 0x20) != 0;
        let bit = args & 0x1f;
        vm_log_op!(
            "{}BITJMPREF {bit} ({})",
            if negate { "N" } else { "" },
            cell.repr_hash()
        );

        let bit = {
            let stack = SafeRc::make_mut(&mut st.stack);
            let value = ok!(stack.pop_int());
            let bit = value.bit(bit as _);
            ok!(stack.push_raw(value));
            bit
        };

        if bit ^ negate {
            let cont = ok!(st.ref_to_cont(cell));
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    #[cfg(feature = "dump")]
    fn dump_if_bit_jmpref(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        if !code.has_remaining(bits, 1) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits, 0)?;
        let cell = code.load_reference_cloned()?;

        let negate = (args & 0x20) != 0;
        let bit = args & 0x1f;

        f.record_cont(cell.clone())?;
        f.record_opcode(&format_args!(
            "{}BITJMPREF {bit} ({})",
            if negate { "N" } else { "" },
            cell.repr_hash()
        ))
    }

    #[op(code = "e4", fmt = "REPEAT", args(brk = false))]
    #[op(code = "e314", fmt = "REPEATBRK", args(brk = true))]
    fn exec_repeat(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let body = ok!(stack.pop_cont());
        let n = ok!(stack.pop_smallint_signed_range(i32::MIN, i32::MAX));
        if n <= 0 {
            return Ok(0);
        }

        let cc = ok!(st.extract_cc(SaveCr::C0, None, None));
        let after = st.c1_envelope_if(brk, cc, true);
        st.repeat(body, after, n as _)
    }

    #[op(code = "e5", fmt = "REPEATEND", args(brk = false))]
    #[op(code = "e315", fmt = "REPEATENDBRK", args(brk = true))]
    fn exec_repeat_end(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let n = ok!(SafeRc::make_mut(&mut st.stack).pop_smallint_signed_range(i32::MIN, i32::MAX));
        if n <= 0 {
            return st.ret();
        }
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            vm_bail!(InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.repeat(body, after, n as _)
    }

    #[op(code = "e6", fmt = "UNTIL", args(brk = false))]
    #[op(code = "e316", fmt = "UNTILBRK", args(brk = true))]
    fn exec_until(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let body = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        let cc = ok!(st.extract_cc(SaveCr::C0, None, None));
        let after = st.c1_envelope_if(brk, cc, true);
        st.until(body, after)
    }

    #[op(code = "e7", fmt = "UNTILEND", args(brk = false))]
    #[op(code = "e317", fmt = "UNTILENDBRK", args(brk = true))]
    fn exec_until_end(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            vm_bail!(InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.until(body, after)
    }

    #[op(code = "e8", fmt = "WHILE", args(brk = false))]
    #[op(code = "e318", fmt = "WHILEBRK", args(brk = true))]
    fn exec_while(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let body = ok!(stack.pop_cont());
        let cond = ok!(stack.pop_cont());

        let cc = ok!(st.extract_cc(SaveCr::C0, None, None));
        let after = st.c1_envelope_if(brk, cc, true);
        st.loop_while(cond, body, after)
    }

    #[op(code = "e9", fmt = "WHILEEND", args(brk = false))]
    #[op(code = "e319", fmt = "WHILEENDBRK", args(brk = true))]
    fn exec_while_end(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let cond = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            vm_bail!(InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.loop_while(cond, body, after)
    }

    #[op(code = "ea", fmt = "AGAIN", args(brk = false))]
    #[op(code = "e31a", fmt = "AGAINBRK", args(brk = true))]
    fn exec_again(st: &mut VmState, brk: bool) -> VmResult<i32> {
        if brk {
            let cc = ok!(st.extract_cc(SaveCr::C0_C1, None, None));
            st.cr.c[1] = Some(cc);
        }
        let body = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        st.again(body)
    }

    #[op(code = "eb", fmt = "AGAINEND", args(brk = false))]
    #[op(code = "e31b", fmt = "AGAINENDBRK", args(brk = true))]
    fn exec_again_end(st: &mut VmState, brk: bool) -> VmResult<i32> {
        if brk {
            st.c1_save_set();
        }
        let cc = ok!(st.extract_cc(SaveCr::NONE, None, None));
        st.again(cc)
    }

    // === Continuation change ===

    #[op(code = "ecrn", fmt = "SETCONTARGS {r},{n}", args(n = ((args as i32 + 1) & 0xf) - 1))]
    fn exec_setcontargs(st: &mut VmState, r: u32, n: i32) -> VmResult<i32> {
        ok!(exec_setcontargs_common(st, r, n));
        Ok(0)
    }

    #[op(code = "ed0p", fmt = "RETURNARGS {p}")]
    fn exec_return_args(st: &mut VmState, p: u32) -> VmResult<i32> {
        ok!(exec_return_args_common(st, p));
        Ok(0)
    }

    #[op(code = "ed10", fmt = "RETURNVARARGS")]
    fn exec_return_varargs(st: &mut VmState) -> VmResult<i32> {
        let count = ok!(SafeRc::make_mut(&mut st.stack).pop_smallint_range(0, 255));
        ok!(exec_return_args_common(st, count));
        Ok(0)
    }

    #[op(code = "ed11", fmt = "SETCONTVARARGS")]
    fn exec_setcont_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let more = ok!(stack.pop_smallint_signed_range(-1, 255));
        let copy = ok!(stack.pop_smallint_range(0, 255));
        ok!(exec_setcontargs_common(st, copy, more));
        Ok(0)
    }

    #[op(code = "ed12", fmt = "SETNUMVARARGS")]
    fn exec_setnum_varargs(st: &mut VmState) -> VmResult<i32> {
        let more = ok!(SafeRc::make_mut(&mut st.stack).pop_smallint_signed_range(-1, 255));
        ok!(exec_setcontargs_common(st, 0, more));
        Ok(0)
    }

    #[op(code = "ed1e", fmt = "BLESS")]
    fn exec_bless(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let code = ok!(stack.pop_cs());
        let cont = SafeRc::new(OrdCont::simple(SafeRc::unwrap_or_clone(code), st.cp.id()));
        ok!(stack.push_raw(cont));
        Ok(0)
    }

    #[op(code = "ed1f", fmt = "BLESSVARARGS")]
    fn exec_bless_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let more = ok!(stack.pop_smallint_signed_range(-1, 255));
        let copy = ok!(stack.pop_smallint_range(0, 255));
        ok!(exec_bless_args_common(st, copy, more));
        Ok(0)
    }

    #[op(code = "ed4i", fmt = "PUSH c{i}")]
    fn exec_push_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        ok!(SafeRc::make_mut(&mut st.stack).push_opt_raw(st.cr.get_as_stack_value(i as _)));
        Ok(0)
    }

    #[op(code = "ed5i", fmt = "POP c{i}")]
    fn exec_pop_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        let value = ok!(SafeRc::make_mut(&mut st.stack).pop());
        ok!(st.cr.set(i as _, value));
        Ok(0)
    }

    #[op(code = "ed6i", fmt = "SETCONTCTR c{i}")]
    fn exec_setcont_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut cont = ok!(stack.pop_cont());
        let value = ok!(stack.pop());
        ok!(force_cdata(&mut cont).save.define(i as _, value));
        ok!(stack.push_raw(cont));
        Ok(0)
    }

    #[op(code = "ed7i", fmt = "SETRETCTR c{i}")]
    fn exec_setret_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        let cont = st.cr.c[0].as_mut().expect("c0 should always be set");
        let value = ok!(SafeRc::make_mut(&mut st.stack).pop());
        ok!(force_cdata(cont).save.define(i as _, value));
        Ok(0)
    }

    #[op(code = "ed8i", fmt = "SETALTCTR c{i}")]
    fn exec_setalt_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        // TODO: Check if c1 is always set
        let cont = st.cr.c[1].as_mut().expect("c1 should always be set");
        let value = ok!(SafeRc::make_mut(&mut st.stack).pop());
        ok!(force_cdata(cont).save.define(i as _, value));
        Ok(0)
    }

    #[op(code = "ed9i", fmt = "POPSAVE c{i}")]
    fn exec_popsave(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        let stack = SafeRc::make_mut(&mut st.stack);
        let value = ok!(stack.pop());
        let mut c0 = st.cr.c[0].clone().expect("c0 should always be set");

        vm_ensure!(
            i > 0 || value.raw_ty() == StackValueType::Cont as u8,
            InvalidType {
                expected: StackValueType::Cont as _,
                actual: value.raw_ty(),
            }
        );

        let prev = st
            .cr
            .get_as_stack_value(i as _)
            .unwrap_or_else(Stack::make_null);

        // NOTE: Is it ok to ignore redefinition errors?
        force_cdata(&mut c0).save.define(i as _, prev).ok();

        // TODO: Check if the order of setting c0 and `cr.set(..)` really matters
        if i == 0 {
            st.cr.c[0] = Some(c0);
            ok!(st.cr.set(i as _, value));
        } else {
            ok!(st.cr.set(i as _, value));
            st.cr.c[0] = Some(c0);
        }

        Ok(0)
    }

    #[op(code = "edai", fmt = "SAVECTR c{i}")]
    fn exec_savectr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);

        let mut c0 = st.cr.c[0].clone().expect("c0 should always be set");

        let value = st
            .cr
            .get_as_stack_value(i as _)
            .unwrap_or_else(Stack::make_null);

        ok!(force_cdata(&mut c0).save.define(i as _, value));
        st.cr.c[0] = Some(c0);
        Ok(0)
    }

    #[op(code = "edbi", fmt = "SAVEALTCTR c{i}")]
    fn exec_savealt_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);

        // TODO: Check if c1 is always set
        let mut c1 = st.cr.c[1].clone().expect("c1 should always be set");

        let value = st
            .cr
            .get_as_stack_value(i as _)
            .unwrap_or_else(Stack::make_null);

        ok!(force_cdata(&mut c1).save.define(i as _, value));
        st.cr.c[1] = Some(c1);
        Ok(0)
    }

    #[op(code = "edci", fmt = "SAVEBOTHCTR c{i}")]
    fn exec_saveboth_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);

        let mut c0 = st.cr.c[0].clone().expect("c0 should always be set");
        let mut c1 = st.cr.c[1].clone().expect("c1 should always be set");

        let value = st
            .cr
            .get_as_stack_value(i as _)
            .unwrap_or_else(Stack::make_null);

        // NOTE: Is it ok to ignore redefinition errors?
        force_cdata(&mut c0).save.define(i as _, value.clone()).ok();
        force_cdata(&mut c1).save.define(i as _, value).ok();
        st.cr.c[0] = Some(c0);
        st.cr.c[1] = Some(c1);
        Ok(0)
    }

    #[op(code = "ede0", fmt = "PUSHCTRX")]
    fn exec_push_ctr_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 16)) as usize;
        let Some(value) = st.cr.get_as_stack_value(idx) else {
            vm_bail!(ControlRegisterOutOfRange(idx));
        };
        ok!(stack.push_raw(value));
        Ok(0)
    }

    #[op(code = "ede1", fmt = "POPCTRX")]
    fn exec_pop_ctr_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 16)) as usize;
        vm_ensure!(
            ControlRegs::is_valid_idx(idx),
            ControlRegisterOutOfRange(idx)
        );

        let value = ok!(stack.pop());
        ok!(st.cr.set(idx, value));
        Ok(0)
    }

    #[op(code = "ede2", fmt = "SETCONTCTRX")]
    fn exec_setcont_ctr_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 16)) as usize;
        vm_ensure!(
            ControlRegs::is_valid_idx(idx),
            ControlRegisterOutOfRange(idx)
        );
        let mut cont = ok!(stack.pop_cont());
        let value = ok!(stack.pop());
        ok!(force_cdata(&mut cont).save.define(idx, value));
        ok!(stack.push_raw(cont));
        Ok(0)
    }

    #[op(code = "ede3xx", fmt = ("SETCONTCTRMANY {}", args & 0xff), args(x = Some(args & 0xff)))]
    #[op(code = "ede4", fmt = "SETCONTCTRMANYX", args(x = None))]
    fn exec_setcont_ctr_many(st: &mut VmState, x: Option<u32>) -> VmResult<i32> {
        ok!(st.version.require_ton(9..));

        let stack = SafeRc::make_mut(&mut st.stack);
        let x = match x {
            Some(x) => x,
            None => ok!(stack.pop_smallint_range(0, 255)),
        };
        vm_ensure!(x & (1 << 6) == 0, ControlRegisterOutOfRange(6));

        let mut cont = ok!(stack.pop_cont());

        for i in 0..8 {
            if x & (1 << i) == 0 {
                continue;
            }

            let Some(st_value) = st.cr.get_as_stack_value(i) else {
                vm_bail!(InvalidType {
                    expected: StackValueType::Cont as _,
                    actual: StackValueType::Null as _
                })
            };
            ok!(force_cdata(&mut cont).save.define(i, st_value));
        }

        ok!(stack.push_raw(cont));
        Ok(0)
    }

    #[op(code = "edf0", fmt = "BOOLAND", args(op = Compose::And))]
    #[op(code = "edf1", fmt = "BOOLOR", args(op = Compose::Or))]
    #[op(code = "edf2", fmt = "COMPOSBOTH", args(op = Compose::Both))]
    fn exec_compos(st: &mut VmState, op: Compose) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let value = ok!(stack.pop_cont());
        let mut cont = ok!(stack.pop_cont());
        let refs = &mut force_cdata(&mut cont).save;
        match op {
            Compose::And => refs.define_c0(&Some(value)),
            Compose::Or => refs.define_c1(&Some(value)),
            Compose::Both => {
                refs.define_c0(&Some(value.clone()));
                refs.define_c1(&Some(value));
            }
        }
        ok!(stack.push_raw(cont));
        Ok(0)
    }

    #[op(code = "edf3", fmt = "ATEXIT")]
    fn exec_atexit(st: &mut VmState) -> VmResult<i32> {
        let mut cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        force_cdata(&mut cont).save.define_c0(&st.cr.c[0]);
        st.cr.c[0] = Some(cont);
        Ok(0)
    }

    #[op(code = "edf4", fmt = "ATEXITALT")]
    fn exec_atexit_alt(st: &mut VmState) -> VmResult<i32> {
        let mut cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        force_cdata(&mut cont).save.define_c1(&st.cr.c[1]);
        st.cr.c[1] = Some(cont);
        Ok(0)
    }

    #[op(code = "edf5", fmt = "SETEXITALT")]
    fn exec_setexit_alt(st: &mut VmState) -> VmResult<i32> {
        let mut cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());
        let cr = force_cdata(&mut cont);
        cr.save.define_c0(&st.cr.c[0]);
        cr.save.define_c1(&st.cr.c[1]);
        st.cr.c[1] = Some(cont);
        Ok(0)
    }

    #[op(code = "edf6", fmt = "THENRET")]
    fn exec_thenret(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut cont = ok!(stack.pop_cont());
        force_cdata(&mut cont).save.define_c0(&st.cr.c[0]);
        ok!(stack.push_raw(cont));
        Ok(0)
    }

    #[op(code = "edf7", fmt = "THENRETALT")]
    fn exec_thenret_alt(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut cont = ok!(stack.pop_cont());
        force_cdata(&mut cont).save.define_c1(&st.cr.c[1]);
        ok!(stack.push_raw(cont));
        Ok(0)
    }

    #[op(code = "edf8", fmt = "INVERT")]
    fn exec_invert(st: &mut VmState) -> VmResult<i32> {
        st.cr.c.swap(0, 1);
        Ok(0)
    }

    #[op(code = "edf9", fmt = "BOOLEVAL")]
    fn exec_booleval(st: &mut VmState) -> VmResult<i32> {
        let cont = ok!(SafeRc::make_mut(&mut st.stack).pop_cont());

        let next = ok!(st.extract_cc(SaveCr::C0_C1, None, None));
        st.cr.c[0] = Some(SafeRc::from(PushIntCont {
            value: -1,
            next: next.clone(),
        }));
        st.cr.c[1] = Some(SafeRc::from(PushIntCont { value: 0, next }));

        st.jump(cont)
    }

    #[op(code = "edfa", fmt = "SAMEALT", args(save = false))]
    #[op(code = "edfb", fmt = "SAMEALTSAVE", args(save = true))]
    fn exec_samealt(st: &mut VmState, save: bool) -> VmResult<i32> {
        let [c0, c1, ..] = &mut st.cr.c;

        // TODO: Check if there are no ways to leave `None` in c0
        let c0 = c0.as_mut().expect("c0 should be always set");
        if save {
            force_cdata(c0).save.define_c1(c1);
        }

        *c1 = Some(c0.clone());
        Ok(0)
    }

    #[op(code = "eern", fmt = "BLESSARGS {r},{n}", args(n = ((args as i32 + 1) & 0xf) - 1))]
    fn exec_bless_args(st: &mut VmState, r: u32, n: i32) -> VmResult<i32> {
        ok!(exec_bless_args_common(st, r, n));
        Ok(0)
    }

    // === Dictjump ===

    #[op(code = "f0nn", fmt = "CALLDICT {n}")]
    #[op(code = "f1$00nn#nnn", fmt = "CALLDICT {n}")]
    fn exec_calldict_short(st: &mut VmState, n: u32) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push_int(n));
        let Some(c3) = st.cr.c[3].clone() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Cont as _,
                actual: StackValueType::Null as _,
            });
        };
        st.call(c3)
    }

    #[op(code = "f1$01nn#nnn", fmt = "JMPDICT {n}")]
    fn exec_jmpdict(st: &mut VmState, n: u32) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push_int(n));
        let Some(c3) = st.cr.c[3].clone() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Cont as _,
                actual: StackValueType::Null as _,
            });
        };
        st.jump(c3)
    }

    #[op(code = "f1$10nn#nnn", fmt = "PREPAREDICT {n}")]
    fn exec_preparedict(st: &mut VmState, n: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_int(n));

        let c3 = match st.cr.c[3].clone() {
            Some(c3) => c3.into_dyn_value(),
            None => Stack::make_null(),
        };
        ok!(stack.push_raw(c3));
        Ok(0)
    }

    // === Exceptions ===

    #[op(code = "f2$00nn#n", fmt = "THROW {n}", args(mode = ThrowMode::Direct))]
    #[op(code = "f2$01nn#n", fmt = "THROWIF {n}", args(mode = ThrowMode::Cond(true)))]
    #[op(code = "f2$10nn#n", fmt = "THROWIFNOT {n}", args(mode = ThrowMode::Cond(false)))]
    #[op(code = "f2c$0nnn#nn", fmt = "THROW {n}", args(mode = ThrowMode::Direct))]
    #[op(code = "f2d$0nnn#nn", fmt = "THROWIF {n}", args(mode = ThrowMode::Cond(true)))]
    #[op(code = "f2e$0nnn#nn", fmt = "THROWIFNOT {n}", args(mode = ThrowMode::Cond(false)))]
    fn exec_throw_fixed(st: &mut VmState, n: u32, mode: ThrowMode) -> VmResult<i32> {
        if let ThrowMode::Cond(cond) = mode {
            if ok!(SafeRc::make_mut(&mut st.stack).pop_bool()) != cond {
                return Ok(0);
            }
        }

        st.throw_exception(n as i32)
    }

    #[op(code = "f2c$1nnn#nn", fmt = "THROWARG {n}", args(mode = ThrowMode::Direct))]
    #[op(code = "f2d$1nnn#nn", fmt = "THROWARGIF {n}", args(mode = ThrowMode::Cond(true)))]
    #[op(code = "f2e$1nnn#nn", fmt = "THROWARGIFNOT {n}", args(mode = ThrowMode::Cond(false)))]
    fn exec_throw_arg_fixed(st: &mut VmState, n: u32, mode: ThrowMode) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        if let ThrowMode::Cond(cond) = mode {
            if ok!(stack.pop_bool()) != cond {
                ok!(stack.pop());
                return Ok(0);
            }
        }

        let arg = ok!(stack.pop());
        st.throw_exception_with_arg(n as i32, arg)
    }

    #[op(code = "f2fx @ ..f2f6", fmt = ThrowAnyArgs(x))]
    fn exec_throw_any(st: &mut VmState, x: u32) -> VmResult<i32> {
        let args = ThrowAnyArgs(x);

        let stack = SafeRc::make_mut(&mut st.stack);
        let cond = if args.has_cond() {
            ok!(stack.pop_bool())
        } else {
            args.throw_cond()
        };

        let n = ok!(stack.pop_smallint_range(0, 0xffff));
        if cond != args.throw_cond() {
            if args.has_param() {
                ok!(stack.pop());
            }
            Ok(0)
        } else if args.has_param() {
            let arg = ok!(stack.pop());
            st.throw_exception_with_arg(n as i32, arg)
        } else {
            st.throw_exception(n as i32)
        }
    }

    #[op(code = "f2ff", fmt = "TRY")]
    fn exec_try(st: &mut VmState) -> VmResult<i32> {
        exec_try_common(st, None)
    }

    #[op(code = "f3pr", fmt = "TRYARGS {p},{r}")]
    fn exec_tryargs(st: &mut VmState, p: u32, r: u32) -> VmResult<i32> {
        exec_try_common(st, Some((p as u16, r as u16)))
    }

    // === Codepage ops ===
    #[op(code = "fff0", fmt = "SETCPX")]
    fn exec_set_cp_any(st: &mut VmState) -> VmResult<i32> {
        let cp = ok!(SafeRc::make_mut(&mut st.stack).pop_smallint_signed_range(-0x8000, 0x7fff));
        ok!(st.force_cp(cp as i16 as u16));
        Ok(0)
    }

    #[op(code = "ff00", fmt = "SETCP0", args(x = 0i16))]
    #[op(code = "ffxx @ ff01..fff0", fmt = "SETCP", args(x = (args & 0xff) as i16),)]
    #[op(code = "fffx @ fff1..", fmt = "SETCP {x}", args(x = (args & 0xf) as i16 - 16))]
    fn exec_set_cp(st: &mut VmState, x: i16) -> VmResult<i32> {
        ok!(st.force_cp(x as u16));
        Ok(0)
    }
}

fn exec_ref_prefix(st: &mut VmState, bits: u16, name: &str) -> VmResult<RcCont> {
    let code_range = st.code.range();
    vm_ensure!(code_range.has_remaining(bits, 1), InvalidOpcode);
    let ok = st.code.range_mut().skip_first(bits, 0).is_ok();
    debug_assert!(ok);

    let Some(code) = st.code.cell().reference_cloned(code_range.offset_refs()) else {
        vm_bail!(CellError(tycho_types::error::Error::CellUnderflow));
    };
    let ok = st.code.range_mut().skip_first(0, 1).is_ok();
    debug_assert!(ok);

    vm_log_op!("{name} ({})", code.repr_hash());
    st.ref_to_cont(code)
}

#[cfg(feature = "dump")]
fn dump_ref_prefix(
    code: &mut CellSlice<'_>,
    bits: u16,
    name: &str,
    f: &mut dyn DumpOutput,
) -> DumpResult {
    if !code.has_remaining(bits, 1) {
        return Err(DumpError::InvalidOpcode);
    }
    code.skip_first(bits, 0)?;
    let code = code.load_reference_cloned()?;

    f.record_cont(code.clone())?;
    f.record_opcode(&format_args!("{name} ({})", code.repr_hash()))
}

fn exec_cell_prefix(st: &mut VmState, bits: u16, name: &str) -> VmResult<Cell> {
    let code_range = st.code.range();
    vm_ensure!(code_range.has_remaining(bits, 1), InvalidOpcode);
    let ok = st.code.range_mut().skip_first(bits, 0).is_ok();
    debug_assert!(ok);

    let Some(cell) = st.code.cell().reference_cloned(code_range.offset_refs()) else {
        vm_bail!(CellError(tycho_types::error::Error::CellUnderflow));
    };
    let ok = st.code.range_mut().skip_first(0, 1).is_ok();
    debug_assert!(ok);

    vm_log_op!("{name} ({})", cell.repr_hash());
    Ok(cell)
}

fn exec_ifelse_ref_impl(st: &mut VmState, bits: u16, ref_first: bool) -> VmResult<i32> {
    let cont = {
        let code_range = st.code.range();
        vm_ensure!(code_range.has_remaining(bits, 1), InvalidOpcode);
        let ok = st.code.range_mut().skip_first(bits, 0).is_ok();
        debug_assert!(ok);

        let Some(cell) = st.code.cell().reference_cloned(code_range.offset_refs()) else {
            vm_bail!(CellError(tycho_types::error::Error::CellUnderflow));
        };
        let ok = st.code.range_mut().skip_first(0, 1).is_ok();
        debug_assert!(ok);

        let name = match ref_first {
            true => "IFREFELSE",
            false => "IFELSEREF",
        };

        vm_log_op!("{name} ({})", cell.repr_hash());

        let stack = SafeRc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());

        if ok!(stack.pop_bool()) == ref_first {
            ok!(st.ref_to_cont(cell))
        } else {
            cont
        }
    };
    st.call(cont)
}

fn exec_setcontargs_common(st: &mut VmState, copy: u32, more: i32) -> VmResult<()> {
    let stack = SafeRc::make_mut(&mut st.stack);
    let mut cont = ok!(stack.pop_cont());
    if copy > 0 || more >= 0 {
        let cdata = force_cdata(&mut cont);

        if copy > 0 {
            ok!(cdata.require_nargs(copy as _));
            if let Some(cdata_stack) = &mut cdata.stack {
                ok!(SafeRc::make_mut(cdata_stack).move_from_stack(stack, copy as _));
            } else {
                cdata.stack = Some(ok!(stack.split_top(copy as _)));
            }

            st.gas.try_consume_stack_gas(cdata.stack.as_ref())?;

            if let Some(n) = &mut cdata.nargs {
                *n -= copy as u16;
            }
        }

        if more >= 0 {
            match &mut cdata.nargs {
                Some(n) => {
                    if *n as i32 > more {
                        *n = u16::MAX; // will throw an exception if run
                    }
                }
                None => cdata.nargs = Some(more as _),
            }
        }
    }

    ok!(stack.push_raw(cont));
    Ok(())
}

fn exec_return_args_common(st: &mut VmState, count: u32) -> VmResult<()> {
    let (copy, alt_stack) = {
        let stack = SafeRc::make_mut(&mut st.stack);

        let depth = stack.depth();
        let copy = match (count as usize).cmp(&depth) {
            std::cmp::Ordering::Less => depth - count as usize,
            std::cmp::Ordering::Equal => return Ok(()),
            std::cmp::Ordering::Greater => vm_bail!(StackUnderflow(count as _)),
        };
        let new_stack = ok!(stack.split_top(count as _));

        (copy, std::mem::replace(&mut st.stack, new_stack))
    };

    let cont = st.cr.c[0].as_mut().expect("c0 should always be set");
    let cdata = force_cdata(cont);
    ok!(cdata.require_nargs(copy));

    if let Some(cdata_stack) = &mut cdata.stack {
        ok!(SafeRc::make_mut(cdata_stack)
            .move_from_stack(&mut SafeRc::unwrap_or_clone(alt_stack), copy))
    } else {
        cdata.stack = Some(alt_stack);
    }

    st.gas.try_consume_stack_gas(cdata.stack.as_ref())?;

    if let Some(n) = &mut cdata.nargs {
        *n -= copy as u16;
    }
    Ok(())
}

fn exec_bless_args_common(st: &mut VmState, copy: u32, more: i32) -> VmResult<()> {
    let stack = SafeRc::make_mut(&mut st.stack);
    let cs = ok!(stack.pop_cs());
    let new_stack = ok!(stack.split_top(copy as _));
    st.gas.try_consume_stack_gas(Some(&new_stack))?;
    let cont = SafeRc::new(OrdCont {
        data: ControlData {
            nargs: (more >= 0).then_some(more as _),
            stack: Some(new_stack),
            save: Default::default(),
            cp: Some(st.cp.id()),
        },
        code: SafeRc::unwrap_or_clone(cs),
    });
    ok!(stack.push_raw(cont));
    Ok(())
}

fn exec_try_common(st: &mut VmState, args: Option<(u16, u16)>) -> VmResult<i32> {
    let stack = SafeRc::make_mut(&mut st.stack);
    let mut handler_cont = ok!(stack.pop_cont());
    let cont = ok!(stack.pop_cont());
    let old_c2 = st.cr.c[2].clone();

    let (stack_copy, nargs) = args.unzip();
    let cc = ok!(st.extract_cc(SaveCr::FULL, stack_copy, nargs));

    let handler_cr = &mut force_cdata(&mut handler_cont).save;
    handler_cr.define_c2(&old_c2);
    if handler_cr.c[0].is_none() {
        handler_cr.c[0] = Some(cc.clone());
    }

    st.cr.c[0] = Some(cc);
    st.cr.c[2] = Some(handler_cont);
    st.jump(cont)
}

fn force_cdata(cont: &mut RcCont) -> &mut ControlData {
    if cont.get_control_data().is_some() {
        return SafeRc::make_mut(cont)
            .get_control_data_mut()
            .expect("always has control data");
    }

    *cont = SafeRc::from(ArgContExt {
        data: Default::default(),
        ext: cont.clone(), // TODO: Somehow reduce this `clone`
    });

    SafeRc::get_mut(cont)
        .expect("only one instance")
        .get_control_data_mut()
        .expect("always has control data")
}

#[derive(Debug, Clone, Copy)]
enum Compose {
    And,
    Or,
    Both,
}

#[derive(Debug, Clone, Copy)]
enum ThrowMode {
    Direct,
    Cond(bool),
}

#[derive(Clone, Copy)]
struct ThrowAnyArgs(u32);

impl ThrowAnyArgs {
    const fn has_param(self) -> bool {
        self.0 & 0b001 != 0
    }

    const fn has_cond(self) -> bool {
        self.0 & 0b110 != 0
    }

    const fn throw_cond(self) -> bool {
        self.0 & 0b010 != 0
    }
}

impl std::fmt::Display for ThrowAnyArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let arg = if self.has_param() { "ARG" } else { "" };
        let cond = if self.has_cond() {
            if self.throw_cond() { "IF" } else { "IFNOT" }
        } else {
            ""
        };

        write!(f, "THROW{arg}ANY{cond}")
    }
}

#[derive(Clone, Copy)]
struct RunVmArgs(u32);

impl RunVmArgs {
    /// +1 = same_c3 (set c3 to code).
    const fn same_c3(self) -> bool {
        self.0 & 0b000000001 != 0
    }

    /// +2 = push_0 (push an implicit 0 before running the code).
    const fn push_0(self) -> bool {
        self.0 & 0b000000010 != 0
    }

    /// +4 = load c4 (persistent data) from stack and return its final value.
    const fn load_c4(self) -> bool {
        self.0 & 0b000000100 != 0
    }

    /// +8 = load gas limit from stack and return consumed gas.
    const fn load_gas(self) -> bool {
        self.0 & 0b000001000 != 0
    }

    /// +16 = load c7 (smart-contract context).
    const fn load_c7(self) -> bool {
        self.0 & 0b000010000 != 0
    }

    /// +32 = return c5 (actions).
    const fn return_c5(self) -> bool {
        self.0 & 0b000100000 != 0
    }

    /// +64 = pop hard gas limit (enabled by ACCEPT) from stack as well.
    const fn load_hard_gas_limit(self) -> bool {
        self.0 & 0b001000000 != 0
    }

    /// +128 = isolated gas consumption (separate set of visited cells, reset chksgn counter).
    const fn isolate_gas(self) -> bool {
        self.0 & 0b010000000 != 0
    }

    /// +256 = pop number N, return exactly N values from stack
    /// (only if res=0 or 1; if not enough then res=stk_und).
    const fn ret_n(self) -> bool {
        self.0 & 0b100000000 != 0
    }
}

fn exec_runvm_common(st: &mut VmState, args: RunVmArgs) -> VmResult<i32> {
    // Check possible args range (all other bits are reserved for future).
    vm_ensure!(args.0 < 512, IntegerOutOfRange {
        min: 0,
        max: 511,
        actual: args.0.to_string()
    });

    // Compensate vm creation.
    st.gas.try_consume(GasConsumer::RUNVM_GAS_PRICE)?;

    // Read args from the stack.
    let stack = SafeRc::make_mut(&mut st.stack);

    let mut gas_max = if args.load_hard_gas_limit() {
        ok!(stack.pop_long_range(0, u64::MAX))
    } else {
        u64::MAX
    };
    let gas_limit = if args.load_gas() {
        ok!(stack.pop_long_range(0, u64::MAX))
    } else {
        u64::MAX
    };

    if args.load_hard_gas_limit() {
        gas_max = std::cmp::max(gas_max, gas_limit);
    } else {
        gas_max = gas_limit;
    }

    let child_c7 = if args.load_c7() {
        ok!(stack.pop_tuple())
    } else {
        SafeRc::new(Vec::new())
    };

    let child_data = if args.load_c4() {
        SafeRc::unwrap_or_clone(ok!(stack.pop_cell()))
    } else {
        Cell::default()
    };

    let return_values = if args.ret_n() {
        Some(ok!(stack.pop_smallint_range(0, 1 << 30)))
    } else {
        None
    };

    let child_code = SafeRc::unwrap_or_clone(ok!(stack.pop_cs()));
    let stack_size = ok!(stack.pop_long_range(0, stack.depth().saturating_sub(1) as u64));
    let mut child_stack = ok!(stack.split_top(stack_size as usize));
    st.gas.try_consume_stack_gas(Some(&child_stack))?;

    // Build child VM state.

    let parent_gas = ok!(st.gas.derive(GasConsumerDeriveParams {
        gas_max,
        gas_limit,
        isolate: args.isolate_gas(),
    }));

    // === ↓↓↓ Must not return any error afterwards ↓↓↓ ===

    let child_quit0 = QUIT0.with(SafeRc::clone);
    let child_quit1 = QUIT1.with(SafeRc::clone);
    let child_cp = codepage0();
    let child_c3 = if args.same_c3() {
        if args.push_0() {
            vm_log_trace!("implicit PUSH 0 at start");
            SafeRc::make_mut(&mut child_stack)
                .items
                .push(Stack::make_zero());
        }
        SafeRc::from(OrdCont::simple(child_code.clone(), child_cp.id()))
    } else {
        QUIT11.with(SafeRc::clone).into_dyn_cont()
    };

    let child_cr = ControlRegs {
        c: [
            Some(child_quit0.clone().into_dyn_cont()),
            Some(child_quit1.clone().into_dyn_cont()),
            Some(EXC_QUIT.with(SafeRc::clone).into_dyn_cont()),
            Some(child_c3),
        ],
        d: [Some(child_data), Some(Cell::empty_cell())],
        c7: Some(child_c7),
    };

    st.parent = Some(Box::new(ParentVmState {
        code: std::mem::replace(&mut st.code, child_code),
        stack: std::mem::replace(&mut st.stack, child_stack),
        cr: std::mem::replace(&mut st.cr, child_cr),
        committed_state: std::mem::take(&mut st.committed_state),
        steps: std::mem::take(&mut st.steps),
        quit0: std::mem::replace(&mut st.quit0, child_quit0),
        quit1: std::mem::replace(&mut st.quit1, child_quit1),
        gas: parent_gas,
        cp: std::mem::replace(&mut st.cp, child_cp),
        return_data: args.load_c4(),
        return_actions: args.return_c5(),
        return_gas: args.load_gas(),
        return_values,
        parent: st.parent.take(),
    }));

    Ok(0)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use tracing_test::traced_test;
    use tycho_types::boc::Boc;

    use super::*;
    use crate::OwnedCellSlice;
    use crate::cont::QuitCont;
    use crate::instr::codepage0;
    use crate::state::IntoCode;

    #[test]
    #[traced_test]
    fn argument_contops() {
        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 1, 2
            "#,
            [] => [int 3, int 2],
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHCONT {
                NOP
            }
            CALLXARGS 1, 1
            "#,
            [] => [int 1],
        );

        assert_run_vm!(
            r#"
            PUSHCONT {
                NOP
            }
            CALLXARGS 1, 0
            "#,
            [] => [int 0],
            exit_code: 2
        );

        assert_run_vm!(
            r#"
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 0, 3
            "#,
            [] => [int 0],
            exit_code: 2
        );

        assert_run_vm!(
            r#"
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 0, 3
            "#,
            [] => [int 0],
            exit_code: 2
        );

        assert_run_vm!(
            r#"
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 0, -1
            "#,
            [] => [int 3, int 2]
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 1, -1
            "#,
            [] => [int 1, int 3, int 2]
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHINT 2
            PUSHCONT {
                PUSHINT 3
                PUSHINT 4
            }
            JMPXARGS 1
            PUSHINT 1
            "#,
            [] => [int 2, int 3, int 4]
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHINT 2
            PUSHCONT {
                PUSHINT 3
                PUSHINT 4
            }
            JMPXARGS 1
            PUSHINT 1
            "#,
            [] => [int 2, int 3, int 4]
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHCONT {
                PUSHINT 123
                PUSHINT 245
                RETARGS 2
            }
            EXECUTE
            "#,
            [] => [int 123, int 245]
        );
    }

    #[test]
    #[traced_test]
    fn basic_contops() -> anyhow::Result<()> {
        let cont = SafeRc::new_dyn_value(PushIntCont {
            value: 1,
            next: SafeRc::from(PushIntCont {
                value: 2,
                next: SafeRc::from(QuitCont { exit_code: 0 }),
            }),
        });

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1, int 2],
        );

        let code = make_code(tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        });
        let cont = SafeRc::new_dyn_value(OrdCont::simple(code, codepage0().id()));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1, int 2],
        );

        assert_run_vm!(
            "JMPX",
            [raw cont.clone()] => [int 1, int 2],
        );

        Ok(())
    }

    #[test]
    #[traced_test]
    fn conditional_contops() -> anyhow::Result<()> {
        let code = make_code(tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            IFRET
            PUSHINT 0
            "#
        });
        let cont = SafeRc::new_dyn_value(OrdCont::simple(code, codepage0().id()));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1]
        );

        //--------

        let code = make_code(tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 0
            IFRET
            PUSHINT 2
            "#
        });
        let cont = SafeRc::new_dyn_value(OrdCont::simple(code, codepage0().id()));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1, int 2]
        );

        assert_run_vm!(
            "IFRET",
            [null] => [int 0],
            exit_code: 7
        );

        //-------

        let code = make_code(tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 0
            IFNOTRET
            PUSHINT 1
            "#
        });
        let cont = SafeRc::new_dyn_value(OrdCont::simple(code, codepage0().id()));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 2]
        );

        //--------

        let code = make_code(tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 1
            IFNOTRET
            PUSHINT 1
            "#
        });
        let cont = SafeRc::new_dyn_value(OrdCont::simple(code, codepage0().id()));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 2, int 1]
        );

        //-------------

        let code = make_code(tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        });
        let cont = SafeRc::new_dyn_value(OrdCont::simple(code, codepage0().id()));

        assert_run_vm!(
            "IF",
            [int 0, raw cont.clone()] => [],
        );
        assert_run_vm!(
            "IF",
            [int 123, raw cont.clone()] => [int 1, int 2],
        );

        assert_run_vm!(
            "IFNOT",
            [int 1, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 13890, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 0, raw cont.clone()] => [int 1, int 2],
        );

        //-------

        let code1 = make_code(tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        });
        let cont1 = SafeRc::new_dyn_value(OrdCont::simple(code1, codepage0().id()));

        let code2 = make_code(tvmasm! {
            r#"
            PUSHINT 3
            PUSHINT 4
            "#
        });
        let cont2 = SafeRc::new_dyn_value(OrdCont::simple(code2, codepage0().id()));

        assert_run_vm!(
            "IFELSE",
            [int 0, raw cont1.clone(), raw cont2.clone()] => [int 3, int 4]
        );

        assert_run_vm!(
            "IFELSE",
            [int 1, raw cont1.clone(), raw cont2.clone()] => [int 1, int 2]
        );

        assert_run_vm!(
            "IFELSE",
            [null, raw cont1.clone(), raw cont2.clone()] => [int 0],
            exit_code: 7
        );

        Ok(())
    }

    #[test]
    #[traced_test]
    fn conditional_refcontops() -> anyhow::Result<()> {
        let code = make_code(tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        });
        let cont = SafeRc::new_dyn_value(OrdCont::simple(code, codepage0().id()));

        // assert_run_vm!(
        //     "IFREF",
        //     code.as,
        //     [int 0, raw cont.clone()] => [],
        // );

        assert_run_vm!(
            "IF",
            [int 123, raw cont.clone()] => [int 1, int 2],
        );

        assert_run_vm!(
            r#"PUSHCONT { PUSHINT 1 PUSHINT 2 } EXECUTE"#,
            [] => [int 1, int 2],
        );

        assert_run_vm!(
            "IF",
            [int 0, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 1, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 13890, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 0, raw cont.clone()] => [int 1, int 2],
        );

        Ok(())
    }

    #[test]
    #[traced_test]
    fn conditional_altcontops() -> anyhow::Result<()> {
        assert_run_vm!(
            r#"
            PUSHCONT { PUSHINT 1 }
            POP c0
            PUSHCONT { PUSHINT 2 }
            POP c1
            PUSHINT 1
            IFRETALT
            "#,
            [] => [int 2, int 1]
        );

        assert_run_vm!(
            r#"
            PUSHCONT { PUSHINT 1 }
            POP c0
            PUSHCONT { PUSHINT 2 }
            POP c1
            PUSHINT 0
            IFRETALT
            "#,
            [] => [int 1]
        );

        Ok(())
    }

    #[test]
    #[traced_test]
    fn loops() -> anyhow::Result<()> {
        // REPEAT
        let code = make_code(tvmasm! {
            r#"
            PUSHINT 2
            "#
        });
        let cont = SafeRc::new_dyn_value(OrdCont::simple(code, codepage0().id()));

        let code1 = make_code(tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 1
            "#
        });
        let cont1 = SafeRc::new_dyn_value(OrdCont::simple(code1, codepage0().id()));

        assert_run_vm!(
            "REPEAT",
            [int 5, raw cont.clone()] => [int 2, int 2,int 2, int 2, int 2 ]
        );

        assert_run_vm!(
            "REPEAT",
            [int -1, raw cont.clone()] => []
        );

        assert_run_vm!(
            "REPEAT",
            [int (BigInt::from(1) << 31), raw cont.clone()] => [int 0],
            exit_code: 5
        );

        // REPEATEND

        assert_run_vm!(
            "REPEATEND PUSHINT 2",
            [int 3] => [int 2, int 2, int 2]
        );

        // UNTIL
        assert_run_vm!(
            "UNTIL",
            [raw cont1.clone()] => [int 2]
        );

        // UNTILEND
        // TODO: case for other branch
        assert_run_vm!(
            "UNTILEND PUSHINT 0 PUSHINT 1",
            [int 3] => [int 3, int 0]
        );

        // WHILE
        let code0 = make_code(tvmasm! {
            r#"
            PUSHINT 2
            "#
        });
        let c0 = SafeRc::new_dyn_value(OrdCont::simple(code0, codepage0().id()));

        let code1 = make_code(tvmasm! {
            r#"
            PUSHINT 0
            "#
        });
        let c1 = SafeRc::new_dyn_value(OrdCont::simple(code1, codepage0().id()));

        assert_run_vm!(
            "WHILE",
            [int 2, raw c1.clone(), raw c0.clone()] => [int 2]
        );

        // WHILEEND
        // TODO: case for other branch
        assert_run_vm!(
            "WHILEEND PUSHINT 1",
            [int 2, raw c1.clone()] => [int 2]
        );

        // AGAIN
        // TODO: TEST MORE CASES

        let code_c0 = make_code(tvmasm! {
            r#"
            PUSHINT 2
            RETALT
            "#
        });
        let cont_c0 = SafeRc::new_dyn_value(OrdCont::simple(code_c0, codepage0().id()));

        // TODO: probably this behaviour with exit code 1 is okay. Add more cases with more loops

        assert_run_vm!(
            "AGAIN",
            [int 2, raw cont_c0.clone()] => [int 2, int 2],
            exit_code: 1
        );

        // AGAINEND
        assert_run_vm!(
            "AGAINEND PUSHINT 2 RETALT",
            [int 2] => [int 2, int 2],
            exit_code: 1
        );

        // REPEATBRK

        let code_c0 = make_code(tvmasm! {
            r#"
            PUSHINT 0
            DUMPSTK
            SWAP
            DEC
            DUP
            PUSHCONT {
                DROP
                RETALT
            }
            IFNOT
            "#
        });
        let cont_c0 = SafeRc::new_dyn_value(OrdCont::simple(code_c0, codepage0().id()));

        assert_run_vm!(
            "REPEATBRK",
            [int 5, int 10, raw cont_c0.clone()] => [int 0, int 0, int 0, int 0, int 0]
        );

        // REPEATENDBRK

        assert_run_vm!(
            r#"
            PUSHCONT {
                REPEATENDBRK
                PUSHINT 0
                SWAP
                DEC
                DUP
                PUSHCONT {
                    DROP
                    RETALT
                }
                IFNOT
                POP s1
            }
            EXECUTE
            "#,
            [int 5, int 10] => [int 0]
        );

        let code_c0 = make_code(tvmasm! {
            r#"
            INC
            SWAP
            DUP
            PUSHCONT {
                DROP
                RETALT
            }
            IFNOT
            SWAP
            DUMPSTK
            "#
        });
        let cont_c0 = SafeRc::new_dyn_value(OrdCont::simple(code_c0, codepage0().id()));

        assert_run_vm!(
            "UNTILBRK",
            [int 0, int -5, raw cont_c0.clone()] => [int -4]
        );

        Ok(())
    }

    #[test]
    #[traced_test]
    fn callcc() {
        assert_run_vm!(
            r#"
            PUSHCONT { DROP }
            INT 0
            INT -1
            CALLCCVARARGS
            "#,
            [] => []
        );

        assert_run_vm!(
            r#"
            PUSHCONT { DROP }
            POPSAVE c0

            INT 2
            REPEATEND
            PUSH c0
            CALLCCARGS 0, 3
            DROP
            "#,
            [] => [],
        );

        assert_run_vm!(
            r#"
            INT 0
            SAVECTR c2
            RETURNARGS 0
            "#,
            [] => [int 0],
        );
    }

    #[test]
    #[traced_test]
    fn runvm_simple() {
        let child_code = make_code(tvmasm!(
            r#"
            ADD
            DEPTH
            PUSH c4 CTOS SBITREFS
            PUSH c5 CTOS SBITREFS
            PUSH c7
            PUSHREF x{99991111} POP c4
            PUSHREF x{aaaabbbb} POP c5

            NIL
            INT 100
            TPUSH
            INT 200
            TPUSH
            POP c7

            INT 123
            "#
        ));

        assert_run_vm!(
            r#"
            PUSHREF x{1234} POP c4
            PUSHREF x{5678} POP c5
            NIL
            INT 5
            TPUSH
            INT 6
            TPUSH
            POP c7

            RUNVM 0

            PUSH c4 CTOS
            PUSH c5 CTOS
            PUSH c7
            "#,
            [int 111, int 10, int 20, int 2, slice child_code] => [
                int 111,
                int 30,
                int 1,
                int 0,
                int 0,
                int 0,
                int 0,
                [],
                int 123,
                int 0,
                slice make_slice(0x1234_u16),
                slice make_slice(0x5678_u16),
                [int 5, int 6],
            ],
        );
    }

    #[test]
    #[traced_test]
    fn runvm_exception() {
        // === Simple exception ===

        let child_code = make_code(tvmasm!(
            r#"
            INT 22
            INT 55 THROWARG 66
            "#
        ));

        assert_run_vm!(
            "RUNVM 0",
            [int 111, int 10, int 20, int 2, slice child_code] => [
                int 111,
                int 55,
                int 66,
            ],
        );

        // === c4, c5 with exception ===

        let child_code = make_code(tvmasm!(
            r#"
            PUSHREF x{abcdaaaa} POP c4
            PUSHREF x{abcdbbbb} POP c5
            THROW 55
            "#,
        ));

        assert_run_vm!(
            r#"
            PUSHREF x{1234aaaa} POP c4
            PUSHREF x{1234bbbb} POP c5
            RUNVM 36
            PUSH c4 CTOS
            PUSH c5 CTOS
            "#,
            [int 0, slice child_code, cell make_cell(0x5678_u16)] => [
                int 0,
                int 55,
                null,
                null,
                slice make_slice(0x1234aaaa_u32),
                slice make_slice(0x1234bbbb_u32),
            ],
        );

        // === c4, c5 with exception and commit ===

        let child_code = make_code(tvmasm!(
            r#"
            PUSHREF x{abcdaaaa} POP c4
            PUSHREF x{abcdbbbb} POP c5
            COMMIT
            PUSHREF x{} POP c4
            @newcell
            PUSHREF x{} POP c5
            THROW 55
            "#,
        ));

        assert_run_vm!(
            r#"
            PUSHREF x{1234aaaa} POP c4
            PUSHREF x{1234bbbb} POP c5
            RUNVM 36
            CTOS SWAP CTOS SWAP
            PUSH c4 CTOS
            PUSH c5 CTOS
            "#,
            [int 0, slice child_code, cell make_cell(0x5678_u16)] => [
                int 0,
                int 55,
                slice make_slice(0xabcdaaaa_u32),
                slice make_slice(0xabcdbbbb_u32),
                slice make_slice(0x1234aaaa_u32),
                slice make_slice(0x1234bbbb_u32),
            ],
        );

        // === Gas limit of parent VM is too low ===

        let child_code = make_code(tvmasm!("PUSHCONT { NOP } AGAIN"));
        assert_run_vm!(
            "RUNVM 8 INT 1234",
            gas: 300,
            [int 0, slice child_code, int 1000000] => [int 301],
            exit_code: -14,
        )
    }

    #[test]
    #[traced_test]
    fn runvm_flags_1_2() {
        // === flag +1: same c3 ===

        assert_run_vm!(
            r#"
            @define(simpleProg) {
                SETCP 0
                DICTPUSHCONST 19, [
                    0 => {
                        DUP
                        CALLDICT 22
                        INC
                    }
                    22 => {
                        MUL
                    }
                ]
                DICTIGETJMPZ
                THROWARG 11
            }

            INT 10 INT 0 INT 2 PUSHSLICE @use(simpleProg) RUNVM 1
            INT 10 INT 0 INT 2 PUSHSLICE @use(simpleProg) RUNVM 0
            "#,
            [] => [int 101, int 0, int 22, int 11],
        );

        // === flag +2(+1): push0 ===

        assert_run_vm!(
            "INT 10 INT 1 PUSHSLICE {
                SETCP 0
                DICTPUSHCONST 19, [
                    0 => {
                        DUP
                        CALLDICT 22
                        INC
                    }
                    22 => {
                        MUL
                    }
                ]
                DICTIGETJMPZ
                THROWARG 11
            } RUNVM 3",
            [] => [int 101, int 0]
        );
    }

    #[test]
    #[traced_test]
    fn runvm_flag_4() {
        // flag +4 - load and return c4

        let child_code = make_code(tvmasm!(
            r#"
            PUSHCTR c4 CTOS
            PUSHREF x{abcd} POPCTR c4
            INT 1000
            "#
        ));

        assert_run_vm!(
            r#"
            PUSHREF x{1234} POP c4
            RUNVM 4
            CTOS
            PUSH c4 CTOS
            "#,
            [int 0, slice child_code, cell make_cell(0x5678_u16)] => [
                slice make_slice(0x5678_u16),
                int 1000,
                int 0,
                slice make_slice(0xabcd_u16),
                slice make_slice(0x1234_u16),
            ]
        );
    }

    #[test]
    #[traced_test]
    fn runvm_flag_8() {
        // flag: +8 - gas limit

        let child_code = make_code(tvmasm!("PUSHCONT { NOP } AGAIN"));

        assert_run_vm!(
            r#"RUNVM 8 INT 1234"#,
            [int 0, slice child_code, int 200] => [
                int 215,
                int -14,
                int 215,
                int 1234,
            ]
        );
    }

    #[test]
    #[traced_test]
    fn runvm_flag_16() {
        // flag +16 - load c7

        let child_code = make_code(tvmasm!(
            r#"
            PUSH c7
            NIL
            INT 111 TPUSH
            INT 222 TPUSH
            INT 3333 TPUSH
            POP c7
            INT 1000
            "#
        ));

        assert_run_vm!(
            r#"
            NIL
            INT 1 TPUSH
            INT 2 TPUSH
            INT 3 TPUSH
            POP c7
            RUNVM 16
            PUSH c7
            "#,
            [int 0, slice child_code, [int 10, int 15, int 20]] => [
                [int 10, int 15, int 20],
                int 1000,
                int 0,
                [int 1, int 2, int 3],
            ],
        );
    }

    #[test]
    #[traced_test]
    fn runvm_flag_32() {
        // flag +32 - return c5

        let child_code = make_code(tvmasm!(
            r#"
            PUSH c5 CTOS SBITREFS
            PUSHREF x{5678} POP c5
            INT 1000
            "#
        ));

        assert_run_vm!(
            r#"
            PUSHREF x{1234} POP c5
            RUNVM 32
            CTOS
            PUSH c5 CTOS
            "#,
            [int 0, slice child_code] => [
                int 0,
                int 0,
                int 1000,
                int 0,
                slice make_slice(0x5678_u16),
                slice make_slice(0x1234_u16),
            ],
        );
    }

    #[test]
    #[traced_test]
    fn runvm_flag_64() {
        // flag +64 - hard gas limit

        let child_code = make_code(tvmasm!("PUSHCONT { NOP } AGAIN"));
        assert_run_vm!(
            "RUNVM 72 INT 1234",
            [int 0, slice child_code, int 200, int 500] => [int 215, int -14, int 215, int 1234],
        );

        let child_code = make_code(tvmasm!("ACCEPT PUSHCONT { NOP } AGAIN"));
        assert_run_vm!(
            "RUNVM 72 INT 1234",
            [int 0, slice child_code, int 200, int 500] => [int 517, int -14, int 517, int 1234],
        );
    }

    #[test]
    #[traced_test]
    fn runvm_flag_128() {
        // flag +128 - separate loaded_cells

        assert_run_vm!(
            r#"
            DUP CTOS DROP
            INT 2
            PUSHSLICE { CTOS DROP CTOS DROP }
            INT 10000
            RUNVM 8
            "#,
            [cell make_cell(0x12345678_u32), cell make_cell(0x87654321_u32)] => [
                int 0,
                int 202,
            ],
        );
    }

    #[test]
    #[traced_test]
    fn runvm_flag_256() {
        // +256 - fixed number of return values

        let child_code = make_code(tvmasm!("INT 1 INT 2 INT 3 INT 4 INT 5"));
        assert_run_vm!(
            "RUNVM 256",
            [int 11, int 22, int 33, int 3, slice child_code.clone(), int 3] => [
                int 3,
                int 4,
                int 5,
                int 0,
            ]
        );
        assert_run_vm!(
            "RUNVM 256",
            [int 11, int 22, int 33, int 3, slice child_code.clone(), int 0] => [int 0]
        );
        assert_run_vm!(
            "RUNVM 256",
            [int 11, int 22, int 33, int 3, slice child_code, int 20] => [int 0, int -3]
        );

        let child_code = make_code(tvmasm!("INT 1 INT 2 INT 3 INT 4 INT 5 THROW 77"));
        assert_run_vm!(
            "RUNVM 256",
            [int 11, int 22, int 33, int 3, slice child_code, int 3] => [int 0, int 77]
        );
    }

    #[test]
    // #[traced_test]
    fn runvm_compute_big() {
        assert_run_vm!(
            r#"
            @define(slice) {
                DUP EQINT 0
                PUSHCONT {
                    DROP DROP
                    ZERO
                } IFJMP
                OVER OVER DEC
                INT 2
                PUSH s2
                RUNVM 0 THROWIF 11
                ADD NIP
            }
            PUSHSLICE @use(slice)
            INT 10000
            INT 2
            PUSHSLICE @use(slice) RUNVM 0
            "#,
            gas: 10000000,
            [] => [int 50005000, int 0],
        );

        assert_run_vm!(
            r#"
            @define(slice) {
                DUP EQINT 0
                PUSHCONT {
                    DROP DROP
                    ZERO
                } IFJMP
                OVER OVER DEC
                INT 2
                PUSH s2
                RUNVM 0 THROWIF 11
                ADD NIP
            }
            PUSHSLICE @use(slice)
            INT 10000
            INT 2
            PUSHSLICE @use(slice) RUNVM 0
            "#,
            gas: 100000,
            [] => [int 100001],
            exit_code: -14,
        );
    }

    #[test]
    #[traced_test]
    fn runvmx() {
        let child_code = make_code(tvmasm!("PUSHCONT { NOP } AGAIN"));
        assert_run_vm!(
            r#"INT 8 RUNVMX INT 1234"#,
            [int 0, slice child_code, int 200] => [int 215, int -14, int 215, int 1234],
        );
    }

    #[test]
    // #[traced_test]
    fn infinite_recursion() {
        assert_run_vm!(
            r#"
            PUSHCONT {
                DUP
                EXECUTE
            }
            DUP
            EXECUTE
            "#,
            [] => [int 1000008],
            exit_code: -14,
        );
    }

    #[test]
    // #[traced_test]
    fn infinite_loop_1() {
        assert_run_vm!(
            r#"
            AGAINEND
            SAVEBOTHCTR c0
            "#,
            [] => [int 1000011],
            exit_code: -14,
        );
    }

    #[test]
    // #[traced_test]
    fn infinite_loop_2() {
        assert_run_vm!(
            r#"
            PUSHINT -1
            PUSHINT 10
            PUSHCONT { PUSHCONT {} }
            AGAIN
            AND
            AGAINEND
            DEPTH
            "#,
            [] => [int 1000015],
            exit_code: -14,
        );
    }

    #[test]
    // #[traced_test]
    fn infinite_loop_3() {
        assert_run_vm!(
            r#"
            PUSHCONT {
                @inline x{94ed}
            }
            POPSAVE c2
            AGAINEND
            @inline x{8a}
            "#,
            [] => [int 1000002],
            exit_code: -14,
        );
    }

    #[test]
    // #[traced_test]
    fn oom_1() {
        assert_run_vm!(
            r#"
            PUSHCONT {
                PUSHNULL
                PUSHINT 7
                REPEATEND
                BLKPUSH 15, 0
                TUPLE 15
            }
            CALLXARGS 0, 0
            "#,
            [] => [],
        );
    }

    #[test]
    #[traced_test]
    fn empty_stack_on_exit() {
        assert_run_vm!(
            r#"
            PUSHCONT {
                PUSHINT 7
                REPEATEND

                DEPTH
                DUMPSTK
            }
            CALLXARGS 0, 0
            "#,
            [] => [],
        );
    }

    #[test]
    // #[traced_test]
    fn safe_infinite_recursion() {
        assert_run_vm!(
            r#"
            PUSHCONT {
                DUP
                POPSAVE c0
            }
            DUP
            EXECUTE
            "#,
            [] => [int 1000015],
            exit_code: -14,
        );
    }

    #[test]
    // #[traced_test]
    fn infinite_tuple() {
        assert_run_vm!(
            r#"
            NIL
            PUSHCONT {
                SWAP SINGLE SWAP
                DUP
                POPSAVE c0
            }
            DUP
            EXECUTE
            "#,
            [] => [int 1000011],
            exit_code: -14,
        );
    }

    #[test]
    // #[traced_test]
    fn infinite_runvm() {
        assert_run_vm!(
            r#"
            PUSHSLICE x{00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}
            PUSHSLICE x{29b80902c424a3bb10064298f03e315e179ddc47d6a6f5695500f793f05d0b9b}
            LDU 256
            DROP

            PUSHSLICE {
                PUSH s2
                PUSH s2
                ZERO ROTREV
                CHKSIGNU DROP

                DUP
                INT 3 SWAP INT 128 RUNVMX
            }
            DUP
            INT 3 SWAP INT 128 RUNVMX
            "#,
            [] => [int 1000001],
            exit_code: -14,
        );
    }

    fn make_code(code: &[u8]) -> OwnedCellSlice {
        Boc::decode(code).unwrap().into_code().unwrap()
    }

    fn make_cell<T: Store>(value: T) -> Cell {
        CellBuilder::build_from(value).unwrap()
    }

    fn make_slice<T: Store>(value: T) -> OwnedCellSlice {
        OwnedCellSlice::new_allow_exotic(CellBuilder::build_from(value).unwrap())
    }
}
