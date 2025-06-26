use std::borrow::Cow;

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;
use tycho_types::cell::LoadMode;
use tycho_types::error::Error;
use tycho_types::prelude::*;
use tycho_vm_proc::vm_module;

use crate::cont::OrdCont;
#[cfg(feature = "dump")]
use crate::dispatch::DumpOutput;
#[cfg(feature = "dump")]
use crate::error::{DumpError, DumpResult};
use crate::error::{VmError, VmResult};
use crate::saferc::SafeRc;
use crate::stack::{Stack, StackValue};
use crate::state::VmState;
#[cfg(any(feature = "dump", feature = "tracing"))]
use crate::util::CellSliceExt;
use crate::util::{OwnedCellSlice, remove_trailing};

pub struct CellOps;

#[vm_module]
impl CellOps {
    // === Const ops ===

    #[op_ext(code = 0x88, code_bits = 8, arg_bits = 0, dump_with = dump_push_ref)]
    fn exec_push_ref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_push_ref_common(st, bits, "PUSHREF", PushRefMode::Cell)
    }

    #[cfg(feature = "dump")]
    fn dump_push_ref(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_push_ref_common(code, bits, "PUSHREF", false, f)
    }

    #[op_ext(code = 0x89, code_bits = 8, arg_bits = 0, dump_with = dump_push_ref_slice)]
    fn exec_push_ref_slice(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_push_ref_common(st, bits, "PUSHREFSLICE", PushRefMode::Slice)
    }

    #[cfg(feature = "dump")]
    fn dump_push_ref_slice(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_push_ref_common(code, bits, "PUSHREFSLICE", false, f)
    }

    #[op_ext(code = 0x8a, code_bits = 8, arg_bits = 0, dump_with = dump_push_ref_cont)]
    fn exec_push_ref_cont(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_push_ref_common(st, bits, "PUSHREFCONT", PushRefMode::Cont)
    }

    #[cfg(feature = "dump")]
    fn dump_push_ref_cont(
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        dump_push_ref_common(code, bits, "PUSHREFCONT", true, f)
    }

    #[op_ext(code = 0x8b, code_bits = 8, arg_bits = 4, dump_with = dump_push_slice)]
    fn exec_push_slice(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0xf) * 8 + 4) as u16;
        exec_push_slice_common(st, bits, data_bits, 0)
    }

    #[cfg(feature = "dump")]
    fn dump_push_slice(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let data_bits = ((args & 0xf) * 8 + 4) as u16;
        dump_push_slice_common(code, bits, data_bits, 0, f)
    }

    #[op_ext(code = 0x8c, code_bits = 8, arg_bits = 7, dump_with = dump_push_slice_r)]
    fn exec_push_slice_r(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0x1f) * 8 + 1) as u16;
        let refs = (((args >> 5) & 0b11) + 1) as u8;
        exec_push_slice_common(st, bits, data_bits, refs)
    }

    #[cfg(feature = "dump")]
    fn dump_push_slice_r(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let data_bits = ((args & 0x1f) * 8 + 1) as u16;
        let refs = (((args >> 5) & 0b11) + 1) as u8;
        dump_push_slice_common(code, bits, data_bits, refs, f)
    }

    #[op_ext_range(
        code_min = 0x8d << 10,
        code_max = ((0x8d << 3) + 5) << 7,
        total_bits = 18,
        dump_with = dump_push_slice_r2,
    )]
    fn exec_push_slice_r2(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0x7f) * 8 + 6) as u16;
        let refs = ((args >> 7) & 0b111) as u8;
        exec_push_slice_common(st, bits, data_bits, refs)
    }

    #[cfg(feature = "dump")]
    fn dump_push_slice_r2(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let data_bits = ((args & 0x7f) * 8 + 6) as u16;
        let refs = ((args >> 7) & 0b111) as u8;
        dump_push_slice_common(code, bits, data_bits, refs, f)
    }

    #[op_ext(code = 0x8e >> 1, code_bits = 7, arg_bits = 9, dump_with = dump_push_cont)]
    fn exec_push_cont(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0x7f) * 8) as u16;
        let refs = ((args >> 7) & 0b11) as u8;

        let code_range = st.code.range_mut();
        vm_ensure!(
            code_range.has_remaining(bits + data_bits, refs),
            InvalidOpcode
        );
        code_range.skip_first(bits, 0).ok();

        let mut slice_range = *code_range;
        slice_range.only_first(data_bits, refs).ok();

        code_range.skip_first(data_bits, refs).ok();

        let code = OwnedCellSlice::from((slice_range, st.code.cell().clone()));
        vm_log_op!("PUSHCONT {}", code);

        let cont = SafeRc::new(OrdCont::simple(code, st.cp.id()));
        ok!(SafeRc::make_mut(&mut st.stack).push_raw(cont));
        Ok(0)
    }

    #[cfg(feature = "dump")]
    fn dump_push_cont(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let data_bits = ((args & 0x7f) * 8) as u16;
        let refs = ((args >> 7) & 0b11) as u8;

        if !code.has_remaining(bits + data_bits, refs) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits, 0)?;

        let mut slice = *code;
        slice.only_first(data_bits, refs)?;
        code.skip_first(data_bits, refs)?;

        f.record_cont_slice(slice)?;
        f.record_opcode(&format_args!("PUSHCONT {}", slice.display_as_stack_value()))
    }

    #[op_ext(code = 0x9, code_bits = 4, arg_bits = 4, dump_with = dump_push_cont_simple)]
    fn exec_push_cont_simple(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0xf) * 8) as u16;

        let code_range = st.code.range_mut();
        vm_ensure!(code_range.has_remaining(bits + data_bits, 0), InvalidOpcode);
        code_range.skip_first(bits, 0).ok();

        let mut slice_range = *code_range;
        slice_range.only_first(data_bits, 0).ok();

        code_range.skip_first(data_bits, 0).ok();

        let code = OwnedCellSlice::from((slice_range, st.code.cell().clone()));
        vm_log_op!("PUSHCONT {}", code);

        let cont = SafeRc::new(OrdCont::simple(code, st.cp.id()));
        ok!(SafeRc::make_mut(&mut st.stack).push_raw(cont));
        Ok(0)
    }

    #[cfg(feature = "dump")]
    fn dump_push_cont_simple(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let data_bits = ((args & 0xf) * 8) as u16;

        if !code.has_remaining(bits + data_bits, 0) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits, 0)?;

        let mut slice = *code;
        slice.only_first(data_bits, 0)?;
        code.skip_first(data_bits, 0)?;

        f.record_cont_slice(slice)?;
        f.record_opcode(&format_args!("PUSHCONT {}", slice.display_as_stack_value()))
    }

    // === Slice comparison ops ===

    #[op(code = "c700", fmt = "SEMPTY", args(op = SliceBoolUnaryOp::IsEmpty))]
    #[op(code = "c701", fmt = "SDEMPTY", args(op = SliceBoolUnaryOp::NoBits))]
    #[op(code = "c702", fmt = "SREMPTY", args(op = SliceBoolUnaryOp::NoRefs))]
    #[op(code = "c703", fmt = "SDFIRST", args(op = SliceBoolUnaryOp::FirstBit))]
    fn exec_slice_bool_unary_op(st: &mut VmState, op: SliceBoolUnaryOp) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let range = cs.range();
        let res = match op {
            SliceBoolUnaryOp::IsEmpty => range.is_data_empty() && range.is_refs_empty(),
            SliceBoolUnaryOp::NoBits => range.is_data_empty(),
            SliceBoolUnaryOp::NoRefs => range.is_refs_empty(),
            SliceBoolUnaryOp::FirstBit => {
                let slice = cs.apply();
                slice.get_bit(0).unwrap_or_default()
            }
        };
        ok!(stack.push_bool(res));
        Ok(0)
    }

    #[op(code = "c704", fmt = "SDLEXCMP")]
    fn exec_slice_lex_cmp(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cs2 = ok!(stack.pop_cs());
        let cs1 = ok!(stack.pop_cs());

        let slice1 = cs1.apply();
        let slice2 = cs2.apply();

        let res = slice1.lex_cmp(&slice2)? as i8;
        ok!(stack.push_int(res));
        Ok(0)
    }

    #[op(code = "c705", fmt = "SDEQ", args(op = SliceBinaryOp::DataEq))]
    #[op(code = "c708", fmt = "SDPFX", args(op = SliceBinaryOp::IsPrefix))]
    #[op(code = "c709", fmt = "SDPFXREV", args(op = SliceBinaryOp::IsPrefixRev))]
    #[op(code = "c70a", fmt = "SDPPFX", args(op = SliceBinaryOp::IsProperPrefix))]
    #[op(code = "c70b", fmt = "SDPPFXREV", args(op = SliceBinaryOp::IsProperPrefixRev))]
    #[op(code = "c70c", fmt = "SDSFX", args(op = SliceBinaryOp::IsSuffix))]
    #[op(code = "c70d", fmt = "SDSFXREV", args(op = SliceBinaryOp::IsSuffixRev))]
    #[op(code = "c70e", fmt = "SDPSFX", args(op = SliceBinaryOp::IsProperSuffix))]
    #[op(code = "c70f", fmt = "SDPSFXREV", args(op = SliceBinaryOp::IsProperSuffixRev))]
    fn exec_slice_bin_op(st: &mut VmState, op: SliceBinaryOp) -> VmResult<i32> {
        fn is_proper(left: &CellSlice<'_>, right: &CellSlice<'_>) -> bool {
            left.size_bits() < right.size_bits()
        }

        let stack = SafeRc::make_mut(&mut st.stack);
        let cs2 = ok!(stack.pop_cs());
        let cs1 = ok!(stack.pop_cs());

        let slice1 = cs1.apply();
        let slice2 = cs2.apply();

        let res = match op {
            SliceBinaryOp::DataEq => slice1.lex_cmp(&slice2)?.is_eq(),
            SliceBinaryOp::IsPrefix => slice1.is_data_prefix_of(&slice2)?,
            SliceBinaryOp::IsPrefixRev => slice2.is_data_prefix_of(&slice1)?,
            SliceBinaryOp::IsProperPrefix => {
                is_proper(&slice1, &slice2) && slice1.is_data_prefix_of(&slice2)?
            }
            SliceBinaryOp::IsProperPrefixRev => {
                is_proper(&slice2, &slice1) && slice2.is_data_prefix_of(&slice1)?
            }
            SliceBinaryOp::IsSuffix => slice1.is_data_suffix_of(&slice2)?,
            SliceBinaryOp::IsSuffixRev => slice2.is_data_suffix_of(&slice1)?,
            SliceBinaryOp::IsProperSuffix => {
                is_proper(&slice1, &slice2) && slice1.is_data_suffix_of(&slice2)?
            }
            SliceBinaryOp::IsProperSuffixRev => {
                is_proper(&slice2, &slice1) && slice2.is_data_suffix_of(&slice1)?
            }
        };
        ok!(stack.push_bool(res));
        Ok(0)
    }

    #[op(code = "c710", fmt = "SDCNTLEAD0", args(op = SliceIntUnaryOp::Leading0))]
    #[op(code = "c711", fmt = "SDCNTLEAD1", args(op = SliceIntUnaryOp::Leading1))]
    #[op(code = "c712", fmt = "SDCNTTRAIL0", args(op = SliceIntUnaryOp::Trailing0))]
    #[op(code = "c713", fmt = "SDCNTTRAIL1", args(op = SliceIntUnaryOp::Trailing1))]
    fn exec_slice_int_unary_op(st: &mut VmState, op: SliceIntUnaryOp) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let slice = cs.apply();
        let res = match op {
            SliceIntUnaryOp::Leading0 => slice.count_leading(false),
            SliceIntUnaryOp::Leading1 => slice.count_leading(true),
            SliceIntUnaryOp::Trailing0 => slice.count_trailing(false),
            SliceIntUnaryOp::Trailing1 => slice.count_trailing(true),
        }?;
        ok!(stack.push_int(res));
        Ok(0)
    }

    // === Serializer ops ===

    #[op(code = "c8", fmt = "NEWC")]
    fn exec_new_builder(st: &mut VmState) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push(CellBuilder::new()));
        Ok(0)
    }

    #[op(code = "c9", fmt = "ENDC")]
    fn exec_builder_to_cell(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = stack.pop_builder()?;
        let cell = SafeRc::unwrap_or_clone(builder).build_ext(&st.gas)?;
        ok!(stack.push(cell));
        Ok(0)
    }

    #[op(code = "caxx", fmt = "STI {x}", args(x = (args & 0xff) + 1, signed = true))]
    #[op(code = "cbxx", fmt = "STU {x}", args(x = (args & 0xff) + 1, signed = false))]
    fn exec_store_int(st: &mut VmState, x: u32, signed: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        exec_store_int_common(stack, x as u16, StoreIntArgs::from_sign(signed))
    }

    #[op(code = "cc", fmt = "STREF", args(quiet = false))]
    #[op(code = "cf10", fmt = "STREF", args(quiet = false))]
    #[op(code = "cf18", fmt = "STREFQ", args(quiet = true))]
    fn exec_store_ref(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let cell = ok!(stack.pop_cell());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, cell, builder, quiet);
        }

        SafeRc::make_mut(&mut builder).store_reference(SafeRc::unwrap_or_clone(cell))?;

        finish_store_ok(stack, builder, quiet)
    }

    #[op(code = "cd", fmt = "ENDCST", args(quiet = false))]
    #[op(code = "cf15", fmt = "STBREFR", args(quiet = false))]
    #[op(code = "cf1d", fmt = "STBREFRQ", args(quiet = true))]
    fn exec_store_builder_as_ref_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let child_builder = ok!(stack.pop_builder());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, builder, child_builder, quiet);
        }

        let cell = SafeRc::unwrap_or_clone(child_builder).build_ext(&st.gas)?;
        SafeRc::make_mut(&mut builder).store_reference(cell)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[op(code = "ce", fmt = "STSLICE", args(quiet = false))]
    #[op(code = "cf12", fmt = "STSLICE", args(quiet = false))]
    #[op(code = "cf1a", fmt = "STSLICEQ", args(quiet = true))]
    fn exec_store_slice(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let cs = ok!(stack.pop_cs());

        if !cs.fits_into(&builder) {
            return finish_store_overflow(stack, cs, builder, quiet);
        }

        let slice = cs.apply();
        SafeRc::make_mut(&mut builder).store_slice(slice)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[op(code = "cf0$0sss", fmt = s.display_x(), args(s = StoreIntArgs(args)))]
    fn exec_store_int_var(st: &mut VmState, s: StoreIntArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 256 + s.is_signed() as u32));
        exec_store_int_common(stack, bits as u16, s)
    }

    #[op(
        code = "cf0$1sss#nn",
        fmt = ("{} {n}", s.display()),
        args(s = StoreIntArgs(args >> 8), n = (args & 0xff) + 1),
    )]
    fn exec_store_int_fixed(st: &mut VmState, s: StoreIntArgs, n: u32) -> VmResult<i32> {
        exec_store_int_common(SafeRc::make_mut(&mut st.stack), n as _, s)
    }

    #[op(code = "cf11", fmt = "STBREF", args(quiet = false))]
    #[op(code = "cf19", fmt = "STBREFQ", args(quiet = true))]
    fn exec_store_builder_as_ref(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let child_builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, child_builder, builder, quiet);
        }

        let cell = SafeRc::unwrap_or_clone(child_builder).build_ext(&st.gas)?;
        SafeRc::make_mut(&mut builder).store_reference(cell)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[op(code = "cf13", fmt = "STB", args(quiet = false))]
    #[op(code = "cf1b", fmt = "STBQ", args(quiet = true))]
    fn exec_store_builder(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let other_builder = ok!(stack.pop_builder());

        if !builder.has_capacity(other_builder.size_bits(), other_builder.size_refs()) {
            return finish_store_overflow(stack, other_builder, builder, quiet);
        }

        SafeRc::make_mut(&mut builder).store_builder(&other_builder)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[op(code = "cf14", fmt = "STREFR", args(quiet = false))]
    #[op(code = "cf1c", fmt = "STREFRQ", args(quiet = true))]
    fn exec_store_ref_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, builder, cell, quiet);
        }

        SafeRc::make_mut(&mut builder).store_reference(SafeRc::unwrap_or_clone(cell))?;

        finish_store_ok(stack, builder, quiet)
    }

    #[op(code = "cf16", fmt = "STSLICER", args(quiet = false))]
    #[op(code = "cf1e", fmt = "STSLICERQ", args(quiet = true))]
    fn exec_store_slice_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let mut builder = ok!(stack.pop_builder());

        if !cs.fits_into(&builder) {
            return finish_store_overflow(stack, builder, cs, quiet);
        }

        let slice = cs.apply();
        SafeRc::make_mut(&mut builder).store_slice(slice)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[op(code = "cf17", fmt = "STBR", args(quiet = false))]
    #[op(code = "cf1f", fmt = "STBRQ", args(quiet = true))]
    fn exec_store_builder_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let other_builder = ok!(stack.pop_builder());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(other_builder.size_bits(), other_builder.size_refs()) {
            return finish_store_overflow(stack, builder, other_builder, quiet);
        }

        SafeRc::make_mut(&mut builder).store_builder(&other_builder)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[op_ext_range(code_min = 0xcf20, code_max = 0xcf22, total_bits = 16, dump_with = dump_store_const_ref)]
    fn exec_store_const_ref(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let refs = ((args & 1) + 1) as u8;
        let code_range = st.code.range_mut();
        vm_ensure!(code_range.has_remaining(bits, refs), InvalidOpcode);
        code_range.skip_first(bits, 0).ok();

        vm_log_op!("STREF{refs}CONST");

        let stack = SafeRc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());

        vm_ensure!(
            builder.has_capacity(0, refs),
            CellError(Error::CellOverflow)
        );

        {
            let builder = SafeRc::make_mut(&mut builder);
            let mut code = st.code.apply();
            for _ in 0..refs {
                let cell = code.load_reference_cloned()?;
                builder.store_reference(cell)?;
            }
            st.code.set_range(code.range());
        }

        ok!(stack.push_raw(builder));
        Ok(0)
    }

    #[cfg(feature = "dump")]
    fn dump_store_const_ref(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let refs = ((args & 1) + 1) as u8;
        if !code.has_remaining(bits, refs) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits, 0)?;
        for _ in 0..refs {
            let cell = code.load_reference_cloned()?;
            f.record_cell(cell)?;
        }
        f.record_opcode(&format_args!("STREF{refs}CONST"))
    }

    #[op(code = "cf22$ss", fmt = "{s}", args(s = StoreLeIntArgs(args)))]
    fn exec_store_le_int(st: &mut VmState, s: StoreLeIntArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());

        let bits = if s.is_long() { 64 } else { 32 };
        vm_ensure!(
            builder.has_capacity(bits, 0),
            CellError(Error::CellOverflow)
        );

        let x = ok!(stack.pop_int());

        enum Int {
            U32(u32),
            U64(u64),
        }

        let Some(x) = (match (s.is_unsigned(), s.is_long()) {
            (false, false) => x.to_i32().map(|x| Int::U32(x as _)),
            (false, true) => x.to_i64().map(|x| Int::U64(x as _)),
            (true, false) => x.to_u32().map(Int::U32),
            (true, true) => x.to_u64().map(Int::U64),
        }) else {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: bits as _,
                actual: String::new(),
            });
        };

        {
            let builder = SafeRc::make_mut(&mut builder);
            match x {
                Int::U32(x) => builder.store_u32(x.swap_bytes()),
                Int::U64(x) => builder.store_u64(x.swap_bytes()),
            }?;
        }

        ok!(stack.push_raw(builder));
        Ok(0)
    }

    #[op(code = "cf23", fmt = "ENDXC")]
    fn exec_builder_to_special_cell(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let special = ok!(stack.pop_bool());
        let mut builder = SafeRc::unwrap_or_clone(ok!(stack.pop_builder()));

        builder.set_exotic(special);

        // TODO: Test if `special` build fails with ordinary cell type in first 8 bits
        let cell = builder.build_ext(&st.gas)?;

        ok!(stack.push(cell));
        Ok(0)
    }

    #[op(code = "cf30", fmt = "BDEPTH")]
    fn exec_builder_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());

        let depth = compute_depth(builder.references());
        ok!(stack.push_int(depth));
        Ok(0)
    }

    #[op(code = "cf31", fmt = "BBITS")]
    fn exec_builder_bits(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.size_bits()));
        Ok(0)
    }

    #[op(code = "cf32", fmt = "BREFS")]
    fn exec_builder_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.size_refs()));
        Ok(0)
    }

    #[op(code = "cf33", fmt = "BBITREFS")]
    fn exec_builder_bits_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.size_bits()));
        ok!(stack.push_int(builder.size_refs()));
        Ok(0)
    }

    #[op(code = "cf35", fmt = "BREMBITS")]
    fn exec_builder_rem_bits(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_capacity_bits()));
        Ok(0)
    }

    #[op(code = "cf36", fmt = "BREMREFS")]
    fn exec_builder_rem_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_capacity_refs()));
        Ok(0)
    }

    #[op(code = "cf37", fmt = "BREMBITREFS")]
    fn exec_builder_rem_bits_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_capacity_bits()));
        ok!(stack.push_int(builder.spare_capacity_refs()));
        Ok(0)
    }

    #[op(code = "cf38xx", fmt = "BCHKBITS {x}", args(x = (args & 0xff) + 1, quiet = false))]
    #[op(code = "cf3cxx", fmt = "BCHKBITSQ {x}", args(x = (args & 0xff) + 1, quiet = true))]
    fn exec_builder_chk_bits(st: &mut VmState, x: u32, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());

        let fits = builder.has_capacity(x as u16, 0);
        if quiet {
            ok!(stack.push_bool(fits));
        } else if !fits {
            vm_bail!(CellError(Error::CellOverflow));
        }
        Ok(0)
    }

    #[op(code = "cf39", fmt = "BCHKBITS", args(mode = CheckMode::Bits, quiet = false))]
    #[op(code = "cf3a", fmt = "BCHKREFS", args(mode = CheckMode::Refs, quiet = false))]
    #[op(code = "cf3b", fmt = "BCHKBITREFS", args(mode = CheckMode::BitRefs, quiet = false))]
    #[op(code = "cf3d", fmt = "BCHKBITSQ", args(mode = CheckMode::Bits, quiet = true))]
    #[op(code = "cf3e", fmt = "BCHKREFSQ", args(mode = CheckMode::Refs, quiet = true))]
    #[op(code = "cf3f", fmt = "BCHKBITREFSQ", args(mode = CheckMode::BitRefs, quiet = true))]
    fn exec_builder_chk_bits_refs(st: &mut VmState, mode: CheckMode, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        // TODO: Check why `7` is the max value for refs in the original code
        let (bits, refs) = match mode {
            CheckMode::Bits => (ok!(stack.pop_smallint_range(0, 1023)), 0),
            CheckMode::Refs => (0, ok!(stack.pop_smallint_range(0, 7))),
            CheckMode::BitRefs => {
                let refs = ok!(stack.pop_smallint_range(0, 7));
                let bits = ok!(stack.pop_smallint_range(0, 1023));
                (bits, refs)
            }
        };
        let builder = ok!(stack.pop_builder());

        let fits = builder.has_capacity(bits as u16, refs as u8);
        if quiet {
            ok!(stack.push_bool(fits));
        } else if !fits {
            vm_bail!(CellError(Error::CellOverflow));
        }
        Ok(0)
    }

    #[op(code = "cf40", fmt = "STZEROES", args(value = Some(false)))]
    #[op(code = "cf41", fmt = "STONES", args(value = Some(true)))]
    #[op(code = "cf42", fmt = "STSAME", args(value = None))]
    fn exec_store_same(st: &mut VmState, value: Option<bool>) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let value = match value {
            Some(value) => value,
            None => ok!(stack.pop_smallint_range(0, 1)) != 0,
        };
        let bits = ok!(stack.pop_smallint_range(0, 1023));
        let mut builder = ok!(stack.pop_builder());

        vm_ensure!(
            builder.has_capacity(bits as _, 0),
            CellError(Error::CellOverflow)
        );

        {
            let builder = SafeRc::make_mut(&mut builder);
            match value {
                true => builder.store_ones(bits as _)?,
                false => builder.store_zeros(bits as _)?,
            }
        }

        ok!(stack.push_raw(builder));
        Ok(0)
    }

    // cf$1xxxxx
    #[op_ext(code = 0xcf80 >> 7, code_bits = 9, arg_bits = 5, dump_with = dump_store_const_slice)]
    fn exec_store_const_slice(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0b111) * 8 + 2) as u16;
        let refs = ((args >> 3) & 0b11) as u8;

        let code_range = st.code.range_mut();
        vm_ensure!(
            code_range.has_remaining(bits + data_bits, refs),
            InvalidOpcode
        );
        code_range.skip_first(bits, 0).ok();

        let mut slice_range = *code_range;
        slice_range.only_first(data_bits, refs).ok();

        code_range.skip_first(data_bits, refs).ok();

        // Remove tag and trailing zeroes
        let mut slice = slice_range.apply(st.code.cell())?;
        remove_trailing(&mut slice)?;

        vm_log_op!("STSLICECONST {}", slice.display_as_stack_value());

        let stack = SafeRc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        SafeRc::make_mut(&mut builder).store_slice(slice)?;
        ok!(stack.push_raw(builder));
        Ok(0)
    }

    #[cfg(feature = "dump")]
    fn dump_store_const_slice(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let data_bits = ((args & 0b111) * 8 + 2) as u16;
        let refs = ((args >> 3) & 0b11) as u8;

        if !code.has_remaining(bits + data_bits, refs) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits, 0)?;

        let mut slice = *code;
        slice.only_first(data_bits, refs)?;
        code.skip_first(data_bits, refs)?;

        // Remove tag and trailing zeroes
        remove_trailing(&mut slice)?;

        f.record_slice(slice)?;
        f.record_opcode(&format_args!(
            "STSLICECONST {}",
            slice.display_as_stack_value()
        ))
    }

    // === Deserializer ops ===

    #[op(code = "d0", fmt = "CTOS")]
    fn exec_cell_to_slice(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());

        let cs = st
            .gas
            .load_cell_as_slice(SafeRc::unwrap_or_clone(cell), LoadMode::Full)?;

        ok!(stack.push(cs));
        Ok(0)
    }

    #[op(code = "d1", fmt = "ENDS")]
    fn exec_slice_chk_empty(st: &mut VmState) -> VmResult<i32> {
        let cs = ok!(SafeRc::make_mut(&mut st.stack).pop_cs());
        let range = cs.range();
        vm_ensure!(
            range.size_bits() == 0 && range.size_refs() == 0,
            CellError(Error::CellUnderflow)
        );
        Ok(0)
    }

    #[op(code = "d2xx", fmt = "LDI {x}", args(x = (args & 0xff) + 1, signed = true))]
    #[op(code = "d3xx", fmt = "LDU {x}", args(x = (args & 0xff) + 1, signed = false))]
    fn exec_load_int_fixed(st: &mut VmState, x: u32, signed: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        exec_load_int_common(stack, x as _, LoadIntArgs::from_sign(signed))
    }

    #[op(code = "d4", fmt = "LDREF")]
    fn exec_load_ref(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());
        vm_ensure!(cs.range().size_refs() > 0, CellError(Error::CellUnderflow));

        let mut slice = cs.apply();
        let cell = slice.load_reference_cloned()?;
        ok!(stack.push(cell));

        let range = slice.range();
        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[op(code = "d5", fmt = "LDREFRTOS")]
    fn exec_load_ref_rev_to_slice(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());
        vm_ensure!(cs.range().size_refs() > 0, CellError(Error::CellUnderflow));

        let mut slice = cs.apply();
        let cell = slice.load_reference_cloned()?;
        let child_cs = st.gas.load_cell_as_slice(cell, LoadMode::Full)?;

        let range = slice.range();
        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        ok!(stack.push(child_cs));
        Ok(0)
    }

    #[op(code = "d6xx", fmt = "LDSLICE {x}", args(x = (args & 0xff) + 1))]
    fn exec_load_slice_fixed(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        exec_load_slice_common(stack, x as _, LoadSliceArgs(0))
    }

    #[op(code = "d70$0sss", fmt = s.display_x(), args(s = LoadIntArgs(args)))]
    fn exec_load_int_var(st: &mut VmState, s: LoadIntArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 256 + s.is_signed() as u32));
        exec_load_int_common(stack, bits as _, s)
    }

    #[op(
        code = "d70$1sss#nn",
        fmt = ("{} {n}", s.display()),
        args(s = LoadIntArgs(args >> 8), n = (args & 0xff) + 1)
    )]
    fn exec_load_int_fixed2(st: &mut VmState, s: LoadIntArgs, n: u32) -> VmResult<i32> {
        exec_load_int_common(SafeRc::make_mut(&mut st.stack), n as _, s)
    }

    #[op(code = "d71$0xxx", fmt = "PLDUZ {x}", args(x = ((args & 7) + 1) << 5))]
    fn exec_preload_uint_fixed_0e(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());

        let (int, range) = {
            let mut slice = cs.apply();

            let ld_bits = std::cmp::min(slice.size_bits(), x as _);
            let int = match x {
                0..=64 => {
                    let value = slice
                        .load_uint(ld_bits)?
                        .checked_shl(x - ld_bits as u32)
                        .unwrap_or_default();
                    Some(BigInt::from(value))
                }
                65..=256 => {
                    // Extra bits after loading
                    let rshift = (8 - ld_bits as u32 % 8) % 8;
                    // Zero-padding
                    let lshift = x - ld_bits as u32;

                    let mut buffer = [0u8; 32];
                    let mut int = slice
                        .load_raw(&mut buffer, ld_bits)
                        .map(|buffer| BigInt::from_bytes_be(Sign::Plus, buffer))?;

                    // Combine shifts
                    match rshift.cmp(&lshift) {
                        std::cmp::Ordering::Less => {
                            int <<= lshift - rshift;
                        }
                        std::cmp::Ordering::Greater => {
                            int >>= rshift - lshift;
                        }
                        std::cmp::Ordering::Equal => {}
                    }

                    Some(int)
                }
                _ => None,
            };

            (int, slice.range())
        };

        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));

        ok!(match int {
            Some(int) => stack.push_int(int),
            None => stack.push_nan(),
        });
        Ok(0)
    }

    #[op(code = "d71$10ss", fmt = s.display_x(), args(s = LoadSliceArgs(args)))]
    fn exec_load_slice(st: &mut VmState, s: LoadSliceArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 1023));
        exec_load_slice_common(stack, bits as _, s)
    }

    #[op(
        code = "d71$11ss#nn",
        fmt = ("{} {n}", s.display()),
        args(s = LoadSliceArgs(args >> 8), n = (args & 0xff) + 1)
    )]
    fn exec_load_slice_fixed2(st: &mut VmState, s: LoadSliceArgs, n: u32) -> VmResult<i32> {
        exec_load_slice_common(SafeRc::make_mut(&mut st.stack), n as _, s)
    }

    #[op(code = "d720", fmt = "SDCUTFIRST", args(op = SliceRangeOp::CutFirst))]
    #[op(code = "d721", fmt = "SDSKIPFIRST", args(op = SliceRangeOp::SkipFirst))]
    #[op(code = "d722", fmt = "SDCUTLAST", args(op = SliceRangeOp::CutLast))]
    #[op(code = "d723", fmt = "SDSKIPLAST", args(op = SliceRangeOp::SkipLast))]
    fn exec_slice_range_op(st: &mut VmState, op: SliceRangeOp) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        vm_ensure!(
            range.has_remaining(bits, 0),
            CellError(Error::CellUnderflow)
        );

        let ok = match op {
            SliceRangeOp::CutFirst => range.only_first(bits, 0),
            SliceRangeOp::SkipFirst => range.skip_first(bits, 0),
            SliceRangeOp::CutLast => range.only_last(bits, 0),
            SliceRangeOp::SkipLast => range.skip_last(bits, 0),
        }
        .is_ok();
        debug_assert!(ok);

        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[op(code = "d724", fmt = "SDSUBSTR")]
    fn exec_slice_substr(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let len_bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let offset_bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        vm_ensure!(
            range.has_remaining(offset_bits + len_bits, 0),
            CellError(Error::CellUnderflow)
        );

        let mut ok = range.skip_first(offset_bits, 0).is_ok();
        ok &= range.only_first(len_bits, 0).is_ok();
        debug_assert!(ok);

        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[op(code = "d726", fmt = "SDBEGINSX", args(quiet = false))]
    #[op(code = "d727", fmt = "SDBEGINSXQ", args(quiet = true))]
    fn exec_slice_begins_with(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let target = ok!(stack.pop_cs());
        let target = target.apply();
        exec_slice_begins_with_common(stack, &target, quiet)
    }

    // d72$1xxxxxxxx
    #[op_ext(code = 0xd728 >> 3, code_bits = 13, arg_bits = 8, dump_with = dump_slice_begins_with_const)]
    fn exec_slice_begins_with_const(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let quiet = (args & 0x80) != 0;
        let data_bits = ((args & 0x7f) * 8 + 3) as u16;

        let code_range = st.code.range_mut();
        vm_ensure!(code_range.has_remaining(bits + data_bits, 0), InvalidOpcode);
        code_range.skip_first(bits, 0).ok();

        let mut slice_range = *code_range;
        slice_range.only_first(data_bits, 0).ok();

        code_range.skip_first(data_bits, 0).ok();

        // Remove tag and trailing zeroes
        let mut slice = slice_range.apply(st.code.cell())?;
        remove_trailing(&mut slice)?;

        vm_log_op!(
            "SDBEGINS{} {}",
            if quiet { "Q" } else { "" },
            slice.display_as_stack_value()
        );

        let stack = SafeRc::make_mut(&mut st.stack);
        exec_slice_begins_with_common(stack, &slice, quiet)
    }

    #[cfg(feature = "dump")]
    fn dump_slice_begins_with_const(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let quiet = (args & 0x80) != 0;
        let data_bits = ((args & 0x7f) * 8 + 3) as u16;

        if !code.has_remaining(bits + data_bits, 0) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits, 0)?;

        let mut slice = *code;
        slice.only_first(data_bits, 0)?;
        code.skip_first(data_bits, 0)?;

        // Remove tag and trailing zeroes
        remove_trailing(&mut slice)?;

        f.record_slice(slice)?;
        f.record_opcode(&format_args!(
            "SDBEGINS{} {}",
            if quiet { "Q" } else { "" },
            slice.display_as_stack_value()
        ))
    }

    #[op(code = "d730", fmt = "SCUTFIRST", args(op = SliceRangeOp::CutFirst))]
    #[op(code = "d731", fmt = "SSKIPFIRST", args(op = SliceRangeOp::SkipFirst))]
    #[op(code = "d732", fmt = "SCUTLAST", args(op = SliceRangeOp::CutLast))]
    #[op(code = "d733", fmt = "SSKIPLAST", args(op = SliceRangeOp::SkipLast))]
    fn exec_slice_full_range_op(st: &mut VmState, op: SliceRangeOp) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let refs = ok!(stack.pop_smallint_range(0, 4)) as u8;
        let bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        vm_ensure!(
            range.has_remaining(bits, refs),
            CellError(Error::CellUnderflow)
        );

        let ok = match op {
            SliceRangeOp::CutFirst => range.only_first(bits, refs),
            SliceRangeOp::SkipFirst => range.skip_first(bits, refs),
            SliceRangeOp::CutLast => range.only_last(bits, refs),
            SliceRangeOp::SkipLast => range.skip_last(bits, refs),
        }
        .is_ok();
        debug_assert!(ok);

        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[op(code = "d734", fmt = "SUBSLICE")]
    fn exec_subslice(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let len_refs = ok!(stack.pop_smallint_range(0, 4)) as u8;
        let len_bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let offset_refs = ok!(stack.pop_smallint_range(0, 4)) as u8;
        let offset_bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        vm_ensure!(
            range.has_remaining(offset_bits + len_bits, offset_refs + len_refs),
            CellError(Error::CellUnderflow)
        );

        let mut ok = range.skip_first(offset_bits, offset_refs).is_ok();
        ok &= range.only_first(len_bits, len_refs).is_ok();
        debug_assert!(ok);

        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[op(code = "d736", fmt = "SPLIT", args(quiet = false))]
    #[op(code = "d737", fmt = "SPLITQ", args(quiet = true))]
    fn exec_split(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let refs = ok!(stack.pop_smallint_range(0, 4)) as u8;
        let bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        if !range.has_remaining(bits, refs) {
            if !quiet {
                vm_bail!(CellError(Error::CellUnderflow));
            }

            ok!(stack.push_raw(cs));
            ok!(stack.push_bool(false));
            return Ok(0);
        }

        let prefix_range = range.get_prefix(bits, refs);
        let ok = range.skip_first(bits, refs).is_ok();
        debug_assert!(ok);

        ok!(stack.push(OwnedCellSlice::from((prefix_range, cs.cell().clone()))));

        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));

        if quiet {
            ok!(stack.push_bool(true));
        }
        Ok(0)
    }

    #[op(code = "d739", fmt = "XCTOS")]
    fn exec_cell_to_slice_maybe_special(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let is_special = cell.descriptor().is_exotic();

        // NOTE: Do not resolve cell here since we want to return an original.
        let cs = st
            .gas
            .load_cell_as_slice(SafeRc::unwrap_or_clone(cell), LoadMode::UseGas)?;

        ok!(stack.push(cs));
        ok!(stack.push_bool(is_special));
        Ok(0)
    }

    #[op(code = "d73a", fmt = "XLOAD", args(quiet = false))]
    #[op(code = "d73b", fmt = "XLOADQ", args(quiet = true))]
    fn exec_load_special_cell(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let handle_error = |stack: &mut Stack, e: Error| {
            if quiet {
                ok!(stack.push_bool(false));
                Ok(0)
            } else {
                vm_bail!(CellError(e));
            }
        };

        let stack = SafeRc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());

        let cell = 'load: {
            // Do nothing for old VM versions.
            if st.version.is_ton(..5) {
                break 'load cell;
            }

            // Consume only cell gas without resolve.
            st.gas.load_dyn_cell((*cell).as_ref(), LoadMode::UseGas)?;

            let descr = cell.descriptor();

            // Do nothing for ordinary cells.
            if !descr.is_exotic() {
                break 'load cell;
            }

            // Only library cells can be loaded.
            if !descr.is_library() {
                return handle_error(stack, Error::CellUnderflow);
            }

            // Library data structure is enforced by `CellContext::finalize_cell`.
            debug_assert_eq!(cell.bit_len(), 8 + 256);

            // Find library by hash.
            let mut library_hash = HashBytes::ZERO;
            cell.as_slice_allow_exotic()
                .get_raw(8, &mut library_hash.0, 256)?;

            match st.gas.libraries().find(&library_hash) {
                Ok(Some(lib)) => SafeRc::new(lib),
                Ok(None) => {
                    st.gas.set_missing_library(&library_hash);
                    return handle_error(stack, Error::CellUnderflow);
                }
                Err(e) => return handle_error(stack, e),
            }
        };

        ok!(stack.push_raw(cell));
        if quiet {
            ok!(stack.push_bool(true));
        }
        Ok(0)
    }

    #[op(code = "d741", fmt = "SCHKBITS", args(mode = CheckMode::Bits, quiet = false))]
    #[op(code = "d742", fmt = "SCHKREFS", args(mode = CheckMode::Refs, quiet = false))]
    #[op(code = "d743", fmt = "SCHKBITREFS", args(mode = CheckMode::BitRefs, quiet = false))]
    #[op(code = "d745", fmt = "SCHKBITSQ", args(mode = CheckMode::Bits, quiet = true))]
    #[op(code = "d746", fmt = "SCHKREFSQ", args(mode = CheckMode::Refs, quiet = true))]
    #[op(code = "d747", fmt = "SCHKBITREFSQ", args(mode = CheckMode::BitRefs, quiet = true))]
    fn exec_check_slice(st: &mut VmState, mode: CheckMode, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let (bits, refs) = match mode {
            CheckMode::Bits => (ok!(stack.pop_smallint_range(0, 1023)), 0),
            CheckMode::Refs => (0, ok!(stack.pop_smallint_range(0, 4))),
            CheckMode::BitRefs => {
                let refs = ok!(stack.pop_smallint_range(0, 4));
                let bits = ok!(stack.pop_smallint_range(0, 1023));
                (bits, refs)
            }
        };
        let cs = ok!(stack.pop_cs());

        let fits = cs.range().has_remaining(bits as _, refs as _);
        if quiet {
            ok!(stack.push_bool(fits));
        } else if !fits {
            vm_bail!(CellError(Error::CellOverflow));
        }
        Ok(0)
    }

    #[op(code = "d748", fmt = "PLDREFVAR")]
    fn exec_preload_ref(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 3)) as u8;
        let cs = ok!(stack.pop_cs());

        let slice = cs.apply();
        let cell = slice.get_reference_cloned(idx)?;
        ok!(stack.push(cell));
        Ok(0)
    }

    #[op(code = "d749", fmt = "SBITS", args(mode = CheckMode::Bits))]
    #[op(code = "d74a", fmt = "SREFS", args(mode = CheckMode::Refs))]
    #[op(code = "d74b", fmt = "SBITREFS", args(mode = CheckMode::BitRefs))]
    fn exec_slice_bits_refs(st: &mut VmState, mode: CheckMode) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());

        let range = cs.range();
        if matches!(mode, CheckMode::Bits | CheckMode::BitRefs) {
            ok!(stack.push_int(range.size_bits()));
        }
        if matches!(mode, CheckMode::Refs | CheckMode::BitRefs) {
            ok!(stack.push_int(range.size_refs()));
        }
        Ok(0)
    }

    #[op(code = "d74$11xx", fmt = "PLDREFIDX {x}")]
    fn exec_preload_ref_fixed(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());

        let slice = cs.apply();
        let cell = slice.get_reference_cloned(x as _)?;
        ok!(stack.push(cell));
        Ok(0)
    }

    #[op(code = "d75s", fmt = "{s}", args(s = LoadLeIntArgs(args)))]
    fn exec_load_le_int(st: &mut VmState, s: LoadLeIntArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());

        let bits = if s.is_long() { 64 } else { 32 };
        if !cs.range().has_remaining(bits, 0) {
            if !s.is_quiet() {
                vm_bail!(CellError(Error::CellUnderflow));
            }

            if !s.is_prefetch() {
                ok!(stack.push_raw(cs));
            }

            ok!(stack.push_bool(false));
            return Ok(0);
        }

        let range = {
            let mut slice = cs.apply();

            let int = match (s.is_unsigned(), s.is_long()) {
                (false, false) => BigInt::from(slice.load_u32()?.swap_bytes() as i32),
                (false, true) => BigInt::from(slice.load_u64()?.swap_bytes() as i64),
                (true, false) => BigInt::from(slice.load_u32()?.swap_bytes()),
                (true, true) => BigInt::from(slice.load_u64()?.swap_bytes()),
            };
            ok!(stack.push_int(int));

            slice.range()
        };

        if !s.is_prefetch() {
            SafeRc::make_mut(&mut cs).set_range(range);
            ok!(stack.push_raw(cs));
        }

        if s.is_quiet() {
            ok!(stack.push_bool(true));
        }
        Ok(0)
    }

    #[op(code = "d760", fmt = "LDZEROES", args(value = Some(false)))]
    #[op(code = "d761", fmt = "LDONES", args(value = Some(true)))]
    #[op(code = "d762", fmt = "LDSAME", args(value = None))]
    fn exec_load_same(st: &mut VmState, value: Option<bool>) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let value = match value {
            Some(value) => value,
            None => ok!(stack.pop_smallint_range(0, 1)) != 0,
        };
        let mut cs = ok!(stack.pop_cs());

        let range = {
            let target = match value {
                false => Cell::all_zeros_ref(),
                true => Cell::all_ones_ref(),
            };
            let target = target.as_slice_allow_exotic();

            let mut slice = cs.apply();
            let prefix = slice.longest_common_data_prefix(&target);
            let ok = slice.skip_first(prefix.size_bits(), 0).is_ok();
            debug_assert!(ok);

            ok!(stack.push_int(prefix.size_bits()));

            slice.range()
        };

        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[op(code = "d764", fmt = "SDEPTH")]
    fn exec_slice_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let slice = cs.apply();

        let depth = compute_depth(slice.references());
        ok!(stack.push_int(depth));
        Ok(0)
    }

    #[op(code = "d765", fmt = "CDEPTH")]
    fn exec_cell_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let cell = {
            let item = ok!(stack.pop());
            if item.is_null() {
                None
            } else {
                Some(ok!(item.into_cell()))
            }
        };

        ok!(match cell {
            Some(cell) => {
                let depth = compute_depth(cell.references());
                stack.push_int(depth)
            }
            None => stack.push_zero(),
        });
        Ok(0)
    }

    #[op(code = "d766", fmt = "CLEVEL")]
    fn exec_cell_level(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let level = cell.descriptor().level_mask().level();
        ok!(stack.push_int(level));
        Ok(0)
    }

    #[op(code = "d767", fmt = "CLEVELMASK")]
    fn exec_cell_level_mask(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let mask = cell.descriptor().level_mask().to_byte();
        ok!(stack.push_int(mask));
        Ok(0)
    }

    #[op(code = "d76$10xx", fmt = "CHASHI {x}", args(op = LevelOp::Hash))]
    #[op(code = "d76$11xx", fmt = "CDEPTHI {x}", args(op = LevelOp::Depth))]
    fn exec_cell_level_op(st: &mut VmState, x: u32, op: LevelOp) -> VmResult<i32> {
        exec_cell_level_op_common(SafeRc::make_mut(&mut st.stack), x as _, op)
    }

    #[op(code = "d770", fmt = "CHASHIX", args(op = LevelOp::Hash))]
    #[op(code = "d771", fmt = "CDEPTHIX", args(op = LevelOp::Depth))]
    fn exec_cell_level_op_var(st: &mut VmState, op: LevelOp) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_smallint_range(0, 3));
        exec_cell_level_op_common(stack, x as _, op)
    }
}

enum PushRefMode {
    Cell,
    Slice,
    Cont,
}

#[cfg(feature = "dump")]
fn dump_push_ref_common(
    code: &mut CellSlice<'_>,
    bits: u16,
    name: &str,
    as_cont: bool,
    f: &mut dyn DumpOutput,
) -> DumpResult {
    if !code.has_remaining(bits, 1) {
        return Err(DumpError::InvalidOpcode);
    }
    code.skip_first(bits, 0)?;
    let cell = code.load_reference_cloned()?;
    if as_cont {
        f.record_cont(cell.clone())?;
    } else {
        f.record_cell(cell.clone())?;
    }
    f.record_opcode(&format_args!("{name} ({})", cell.repr_hash()))
}

fn exec_push_ref_common(
    st: &mut VmState,
    bits: u16,
    name: &str,
    mode: PushRefMode,
) -> VmResult<i32> {
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

    let stack = SafeRc::make_mut(&mut st.stack);
    ok!(match mode {
        PushRefMode::Cell => stack.push(cell),
        PushRefMode::Slice => {
            let cs = st.gas.load_cell_as_slice(cell, LoadMode::Full)?;
            stack.push(cs)
        }
        PushRefMode::Cont => {
            let code = st.gas.load_cell_as_slice(cell, LoadMode::Full)?;
            let cont = SafeRc::new(OrdCont::simple(code, st.cp.id()));
            stack.push_raw(cont)
        }
    });
    Ok(0)
}

fn exec_push_slice_common(st: &mut VmState, bits: u16, data_bits: u16, refs: u8) -> VmResult<i32> {
    let code_range = st.code.range_mut();
    vm_ensure!(
        code_range.has_remaining(bits + data_bits, refs),
        InvalidOpcode
    );
    code_range.skip_first(bits, 0).ok();

    let mut slice_range = *code_range;
    slice_range.only_first(data_bits, refs).ok();

    code_range.skip_first(data_bits, refs).ok();

    // Remove tag and trailing zeroes
    {
        let mut slice = slice_range.apply(st.code.cell())?;
        remove_trailing(&mut slice)?;
        slice_range = slice.range();
    }

    let slice = OwnedCellSlice::from((slice_range, st.code.cell().clone()));
    vm_log_op!("PUSHSLICE {}", slice);

    ok!(SafeRc::make_mut(&mut st.stack).push(slice));
    Ok(0)
}

#[cfg(feature = "dump")]
fn dump_push_slice_common(
    code: &mut CellSlice<'_>,
    bits: u16,
    data_bits: u16,
    refs: u8,
    f: &mut dyn DumpOutput,
) -> DumpResult {
    if !code.has_remaining(bits + data_bits, refs) {
        return Err(DumpError::InvalidOpcode);
    }

    code.skip_first(bits, 0)?;

    let mut slice = *code;
    slice.only_first(data_bits, refs)?;
    code.skip_first(data_bits, refs)?;

    // Remove tag and trailing zeroes
    remove_trailing(&mut slice)?;

    f.record_slice(slice)?;
    f.record_opcode(&format_args!(
        "PUSHSLICE {}",
        slice.display_as_stack_value()
    ))
}

#[derive(Clone, Copy)]
enum SliceBoolUnaryOp {
    IsEmpty,
    NoBits,
    NoRefs,
    FirstBit,
}

#[derive(Clone, Copy)]
enum SliceBinaryOp {
    DataEq,
    IsPrefix,
    IsPrefixRev,
    IsProperPrefix,
    IsProperPrefixRev,
    IsSuffix,
    IsSuffixRev,
    IsProperSuffix,
    IsProperSuffixRev,
}

#[derive(Clone, Copy)]
enum SliceIntUnaryOp {
    Leading0,
    Leading1,
    Trailing0,
    Trailing1,
}

fn exec_store_int_common(stack: &mut Stack, bits: u16, args: StoreIntArgs) -> VmResult<i32> {
    fn finish_store_fail(
        stack: &mut Stack,
        builder: SafeRc<CellBuilder>,
        x: SafeRc<BigInt>,
        code: i32,
        args: StoreIntArgs,
    ) -> VmResult<i32> {
        if args.is_reversed() {
            ok!(stack.push_raw_int(x, true));
            ok!(stack.push_raw(builder));
        } else {
            ok!(stack.push_raw(builder));
            ok!(stack.push_raw_int(x, true));
        }
        ok!(stack.push_int(code));
        Ok(0)
    }

    let mut builder;
    let x;
    if !args.is_reversed() {
        builder = ok!(stack.pop_builder());
        x = ok!(stack.pop_int());
    } else {
        x = ok!(stack.pop_int());
        builder = ok!(stack.pop_builder());
    }

    if !builder.has_capacity(bits, 0) {
        return if args.is_quiet() {
            finish_store_fail(stack, builder, x, -1, args)
        } else {
            Err(Box::new(VmError::CellError(Error::CellOverflow)))
        };
    }

    let int_bits = x.bitsize(args.is_signed());
    if bits < int_bits {
        return if args.is_quiet() {
            finish_store_fail(stack, builder, x, 1, args)
        } else {
            Err(Box::new(VmError::IntegerOutOfRange {
                min: 0,
                max: bits as _,
                actual: int_bits.to_string(),
            }))
        };
    }

    {
        let builder = SafeRc::make_mut(&mut builder);
        match x.to_u64() {
            Some(value) => builder.store_uint(value, bits)?,
            None => {
                let int = if bits % 8 != 0 {
                    let align = 8 - bits % 8;
                    Cow::Owned((*x).clone() << align)
                } else {
                    Cow::Borrowed(x.as_ref())
                };

                let minimal_bytes = bits.div_ceil(8) as usize;

                let (prefix, mut bytes) = if args.is_signed() {
                    let bytes = int.to_signed_bytes_le();
                    (
                        bytes
                            .last()
                            .map(|first| (first >> 7) * 255)
                            .unwrap_or_default(),
                        bytes,
                    )
                } else {
                    (0, int.to_bytes_le().1)
                };
                bytes.resize(minimal_bytes, prefix);
                bytes.reverse();

                builder.store_raw(&bytes, bits)?;
            }
        }
    }

    finish_store_ok(stack, builder, args.is_quiet())
}

pub(crate) fn finish_store_overflow<T1, T2>(
    stack: &mut Stack,
    arg1: SafeRc<T1>,
    arg2: SafeRc<T2>,
    quiet: bool,
) -> VmResult<i32>
where
    T1: StackValue + 'static,
    T2: StackValue + 'static,
{
    if quiet {
        ok!(stack.push_raw(arg1));
        ok!(stack.push_raw(arg2));
        ok!(stack.push_bool(true)); // `true` here is intentional
        Ok(0)
    } else {
        Err(Box::new(VmError::CellError(Error::CellOverflow)))
    }
}

pub(crate) fn finish_store_ok(
    stack: &mut Stack,
    builder: SafeRc<CellBuilder>,
    quiet: bool,
) -> VmResult<i32> {
    ok!(stack.push_raw(builder));
    if quiet {
        ok!(stack.push_bool(false)); // `false` here is intentional
    }
    Ok(0)
}

#[derive(Clone, Copy)]
struct StoreLeIntArgs(u32);

impl StoreLeIntArgs {
    const fn is_unsigned(self) -> bool {
        self.0 & 0b1 != 0
    }

    const fn is_signed(self) -> bool {
        !self.is_unsigned()
    }

    const fn is_long(&self) -> bool {
        self.0 & 0b10 != 0
    }
}

impl std::fmt::Display for StoreLeIntArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sign = if self.is_signed() { "I" } else { "U" };
        let bytes = if self.is_long() { "8" } else { "4" };
        write!(f, "ST{sign}LE{bytes}")
    }
}

#[derive(Clone, Copy)]
struct StoreIntArgs(u32);

impl StoreIntArgs {
    const fn from_sign(signed: bool) -> Self {
        Self((!signed) as u32)
    }

    const fn is_unsigned(self) -> bool {
        self.0 & 0b001 != 0
    }

    const fn is_signed(self) -> bool {
        !self.is_unsigned()
    }

    const fn is_reversed(self) -> bool {
        self.0 & 0b010 != 0
    }

    const fn is_quiet(self) -> bool {
        self.0 & 0b100 != 0
    }

    fn display(&self) -> DisplayStoreIntArgs<false> {
        DisplayStoreIntArgs(self.0)
    }

    fn display_x(self) -> DisplayStoreIntArgs<true> {
        DisplayStoreIntArgs(self.0)
    }
}

struct DisplayStoreIntArgs<const X: bool>(u32);

impl<const X: bool> std::fmt::Display for DisplayStoreIntArgs<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args = StoreIntArgs(self.0);

        let sign = if args.is_signed() { "I" } else { "U" };
        let x = if X { "X" } else { "" };
        let rev = if args.is_reversed() { "R" } else { "" };
        let quiet = if args.is_quiet() { "Q" } else { "" };

        write!(f, "ST{sign}{x}{rev}{quiet}")
    }
}

#[derive(Clone, Copy)]
enum CheckMode {
    Bits,
    Refs,
    BitRefs,
}

impl std::fmt::Display for CheckMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Bits => "BITS",
            Self::Refs => "REFS",
            Self::BitRefs => "BITREFS",
        })
    }
}

fn exec_load_int_common(stack: &mut Stack, bits: u16, args: LoadIntArgs) -> VmResult<i32> {
    let mut cs = ok!(stack.pop_cs());

    if !cs.range().has_remaining(bits, 0) {
        if !args.is_quiet() {
            vm_bail!(CellError(Error::CellUnderflow));
        }

        if !args.is_prefetch() {
            ok!(stack.push_raw(cs));
        }

        ok!(stack.push_bool(false));
        return Ok(0);
    }

    let range = {
        let mut slice = cs.apply();
        let int = slice.load_bigint(bits, args.is_signed())?;

        ok!(stack.push_int(int));

        slice.range()
    };

    if !args.is_prefetch() {
        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
    }

    if args.is_quiet() {
        ok!(stack.push_bool(true));
    }
    Ok(0)
}

#[derive(Clone, Copy)]
struct LoadLeIntArgs(u32);

impl LoadLeIntArgs {
    const fn is_unsigned(self) -> bool {
        self.0 & 0b0001 != 0
    }

    const fn is_signed(self) -> bool {
        !self.is_unsigned()
    }

    const fn is_long(&self) -> bool {
        self.0 & 0b0010 != 0
    }

    const fn is_prefetch(self) -> bool {
        self.0 & 0b0100 != 0
    }

    const fn is_quiet(self) -> bool {
        self.0 & 0b1000 != 0
    }
}

impl std::fmt::Display for LoadLeIntArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let prefetch = if self.is_prefetch() { "P" } else { "" };
        let sign = if self.is_signed() { "I" } else { "U" };
        let bytes = if self.is_long() { "8" } else { "4" };
        let quiet = if self.is_quiet() { "Q" } else { "" };
        write!(f, "{prefetch}LD{sign}LE{bytes}{quiet}")
    }
}

#[derive(Clone, Copy)]
struct LoadIntArgs(u32);

impl LoadIntArgs {
    const fn from_sign(signed: bool) -> Self {
        Self((!signed) as u32)
    }

    const fn is_unsigned(self) -> bool {
        self.0 & 0b001 != 0
    }

    const fn is_signed(self) -> bool {
        !self.is_unsigned()
    }

    const fn is_prefetch(self) -> bool {
        self.0 & 0b010 != 0
    }

    const fn is_quiet(self) -> bool {
        self.0 & 0b100 != 0
    }

    fn display(&self) -> DisplayLoadIntArgs<false> {
        DisplayLoadIntArgs(self.0)
    }

    fn display_x(self) -> DisplayLoadIntArgs<true> {
        DisplayLoadIntArgs(self.0)
    }
}

struct DisplayLoadIntArgs<const X: bool>(u32);

impl<const X: bool> std::fmt::Display for DisplayLoadIntArgs<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args = LoadIntArgs(self.0);

        let prefetch = if args.is_prefetch() { "P" } else { "" };
        let sign = if args.is_signed() { "I" } else { "U" };
        let x = if X { "X" } else { "" };
        let quiet = if args.is_quiet() { "Q" } else { "" };

        write!(f, "{prefetch}LD{sign}{x}{quiet}")
    }
}

fn exec_load_slice_common(stack: &mut Stack, bits: u16, args: LoadSliceArgs) -> VmResult<i32> {
    let mut cs = ok!(stack.pop_cs());

    if !cs.range().has_remaining(bits, 0) {
        if !args.is_quiet() {
            vm_bail!(CellError(Error::CellUnderflow));
        }

        if !args.is_prefetch() {
            ok!(stack.push_raw(cs));
        }

        ok!(stack.push_bool(false));
        return Ok(0);
    }

    let range = {
        let mut range = cs.range();
        let slice = OwnedCellSlice::from((range.get_prefix(bits, 0), cs.cell().clone()));
        ok!(stack.push(slice));

        let ok = range.skip_first(bits, 0).is_ok();
        debug_assert!(ok);

        range
    };

    if !args.is_prefetch() {
        SafeRc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
    }

    if args.is_quiet() {
        ok!(stack.push_bool(true));
    }
    Ok(0)
}

#[derive(Clone, Copy)]
struct LoadSliceArgs(u32);

impl LoadSliceArgs {
    const fn is_prefetch(self) -> bool {
        self.0 & 0b01 != 0
    }

    const fn is_quiet(self) -> bool {
        self.0 & 0b10 != 0
    }

    fn display(&self) -> DisplayLoadSliceArgs<false> {
        DisplayLoadSliceArgs(self.0)
    }

    fn display_x(&self) -> DisplayLoadSliceArgs<true> {
        DisplayLoadSliceArgs(self.0)
    }
}

struct DisplayLoadSliceArgs<const X: bool>(u32);

impl<const X: bool> std::fmt::Display for DisplayLoadSliceArgs<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args = LoadSliceArgs(self.0);

        let prefetch = if args.is_prefetch() { "P" } else { "" };
        let x = if X { "X" } else { "" };
        let quiet = if args.is_quiet() { "Q" } else { "" };

        write!(f, "{prefetch}LDSLICE{x}{quiet}")
    }
}

#[derive(Clone, Copy)]
enum SliceRangeOp {
    CutFirst,
    SkipFirst,
    CutLast,
    SkipLast,
}

fn exec_slice_begins_with_common(
    stack: &mut Stack,
    prefix: &CellSlice<'_>,
    quiet: bool,
) -> VmResult<i32> {
    let mut cs = ok!(stack.pop_cs());

    let range = {
        let slice = cs.apply();
        let Some(slice) = slice.strip_data_prefix(prefix) else {
            if !quiet {
                vm_bail!(CellError(Error::CellUnderflow));
            }
            ok!(stack.push_raw(cs));
            ok!(stack.push_bool(false));
            return Ok(0);
        };
        slice.range()
    };

    SafeRc::make_mut(&mut cs).set_range(range);
    ok!(stack.push_raw(cs));

    if quiet {
        ok!(stack.push_bool(true));
    }
    Ok(0)
}

#[inline]
fn compute_depth<I: IntoIterator<Item = C>, C: AsRef<DynCell>>(references: I) -> u16 {
    let mut depth = 0;
    for cell in references {
        depth = std::cmp::max(depth, cell.as_ref().repr_depth().saturating_add(1));
    }
    depth
}

#[derive(Clone, Copy)]
enum LevelOp {
    Hash,
    Depth,
}

fn exec_cell_level_op_common(stack: &mut Stack, level: u8, op: LevelOp) -> VmResult<i32> {
    let cell = ok!(stack.pop_cell());
    ok!(match op {
        LevelOp::Hash => stack.push_int(BigInt::from_bytes_be(
            Sign::Plus,
            cell.hash(level).as_array(),
        )),
        LevelOp::Depth => stack.push_int(cell.depth(level)),
    });
    Ok(0)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use tracing_test::traced_test;
    use tycho_types::boc::Boc;
    use tycho_types::cell::{CellBuilder, CellType};
    use tycho_types::merkle::{MerkleProof, MerkleUpdate};
    use tycho_types::models::SimpleLib;

    use super::*;

    #[test]
    #[traced_test]
    fn store_int() {
        assert_run_vm!(
            r#"
            PUSHSLICE x{6_}
            PUSHINT -1
            OVER
            PUSHINT 0
            NEWC
            PUSHSLICE x{6_} STSLICER
            STI 1
            PUSHSLICE x{1_} STSLICER
            STSLICE
            PUSHINT 12321070556741797692511081747621921145552344918445724
            STUR 175
            STI 1
            ENDC
            2DROP
            "#,
            [] => [],
        );
    }

    #[test]
    #[traced_test]
    fn lexcmp_tests() {
        let slice1 = make_uint_cell_slice(0b0, 1);
        let slice2 = make_uint_cell_slice(0b1, 1);

        assert_run_vm!("SDLEXCMP", [slice slice1.clone(), slice slice1.clone()] => [int 0]);
        assert_run_vm!("SDLEXCMP", [slice slice1.clone(), slice slice2.clone()] => [int -1]);
        assert_run_vm!("SDLEXCMP", [slice slice2, slice slice1] => [int 1]);
    }

    #[test]
    #[traced_test]
    fn store_tests() {
        let cell = Cell::default();
        let init_builder = init_builder_with_refs(cell.clone(), 0);
        let result_builer = init_builder_with_refs(cell.clone(), 1);

        assert_run_vm!("STREF", [cell cell.clone(), builder init_builder] => [builder result_builer]);

        let init_builder = init_builder_with_refs(cell.clone(), 4);
        assert_run_vm!("STREF", [cell cell.clone(), builder init_builder] => [int 0], exit_code: 8);

        let init_builder_one = init_builder_with_refs(cell.clone(), 1);
        let init_builder_two = init_builder_with_refs(cell.clone(), 0);
        let cb = init_builder_two.clone();
        let cell = cb.build().unwrap();

        let result = init_builder_with_refs(cell.clone(), 2);
        assert_run_vm!("STBREFR", [builder init_builder_one.clone(), builder init_builder_two.clone()] => [builder result.clone()]);
        assert_run_vm!("ENDCST", [builder init_builder_one.clone(), builder init_builder_two.clone()] => [builder result.clone()]);
        assert_run_vm!("ENDC SWAP STREF", [builder init_builder_one.clone(), builder init_builder_two.clone()] => [builder result.clone()]);
    }

    #[test]
    #[traced_test]
    fn store_builder_tests() {
        let mut builder1 = CellBuilder::new();
        builder1.store_uint(1, 512).unwrap();
        let mut builder2 = CellBuilder::new();
        builder2.store_uint(2, 511).unwrap();

        let mut builder3 = CellBuilder::new();
        builder3.store_uint(3, 512).unwrap();

        let mut result = CellBuilder::new();
        result.store_uint(2, 511).unwrap();
        result.store_uint(1, 512).unwrap();

        assert_run_vm!("STB", [builder builder1.clone(), builder builder2.clone()] => [builder result.clone()]);
        assert_run_vm!("STB", [builder builder1.clone(), builder builder3.clone()] => [int 0], exit_code: 8);
        assert_run_vm!("STBQ", [builder builder1.clone(), builder builder3.clone()] => [builder builder1.clone(), builder builder3.clone(), int -1]); // -1 here is part of the spec

        assert_run_vm!("STBR", [builder builder2.clone(), builder builder1.clone()] => [builder result.clone()]);
        assert_run_vm!("STBRQ", [builder builder2.clone(), builder builder1.clone()] => [builder result.clone(), int 0]);
        // 0 here is part of the spec
    }

    #[test]
    #[traced_test]
    fn builder_info_tests() {
        let mut builder = CellBuilder::new();
        builder.store_uint(1, 512).unwrap();
        builder.store_reference(Cell::empty_cell()).unwrap();
        assert_run_vm!("BCHKBITS", [builder builder.clone(), int 256] => []);
        assert_run_vm!("BCHKBITSQ", [builder builder.clone(), int 256] => [int -1]);
        assert_run_vm!("BCHKBITS", [builder builder.clone(), int 512] => [int 0], exit_code: 8);
        assert_run_vm!("BCHKBITSQ", [builder builder.clone(), int 512] => [int 0]);

        assert_run_vm!("BCHKREFS", [builder builder.clone(), int 3] => []);
        assert_run_vm!("BCHKREFS", [builder builder.clone(), int 4] => [int 0], exit_code: 8);

        assert_run_vm!("BCHKBITREFS", [builder builder.clone(), int 256, int 3] => []);
        assert_run_vm!("BCHKBITREFS", [builder builder.clone(), int 256, int 4] => [int 0], exit_code: 8);

        assert_run_vm!("BDEPTH", [builder builder.clone()] => [int 1]);
        assert_run_vm!("BBITS", [builder builder.clone()] => [int 512]);
        assert_run_vm!("BREFS", [builder builder.clone()] => [int 1]);
        assert_run_vm!("BBITREFS", [builder builder.clone()] => [int 512, int 1]);

        let mut builder1 = CellBuilder::new();
        builder1.store_reference(Cell::empty_cell()).unwrap();
        let cell = builder1.build().unwrap();
        builder.store_reference(cell).unwrap();
        assert_run_vm!("BDEPTH", [builder builder.clone()] => [int 2]);
        assert_run_vm!("BDEPTH", [builder CellBuilder::new()] => [int 0]);

        let builder = create_builder(1023);
        assert_run_vm!("BDEPTH", [builder builder] => [int 1024]); // 1 + depth according to spec
    }

    fn create_builder(depth: u32) -> CellBuilder {
        let mut builder = CellBuilder::new();
        let cell = create_complex_cell(0, depth);
        builder.store_reference(cell).unwrap();
        builder
    }
    fn create_complex_cell(mut current_depth: u32, depth: u32) -> Cell {
        if current_depth == depth {
            return Cell::empty_cell();
        }
        current_depth += 1;
        let mut builder = CellBuilder::new();
        let cell = create_complex_cell(current_depth, depth);
        builder.store_reference(cell).unwrap();
        builder.build().unwrap()
    }

    fn init_builder_with_refs(cell: Cell, ref_count: u8) -> CellBuilder {
        let mut cb = CellBuilder::new();
        for _ in 0..ref_count {
            cb.store_reference(cell.clone()).unwrap();
        }
        cb
    }

    #[test]
    #[traced_test]
    fn ctos_tests() {
        let mut cb = CellBuilder::new();
        cb.store_u8(1).unwrap();
        cb.store_u8(0).unwrap();

        let cell = cb.build().unwrap();
        let slice = OwnedCellSlice::new_allow_exotic(cell.clone());
        assert_run_vm!("CTOS", [cell cell] => [slice slice])
    }

    #[test]
    #[traced_test]
    fn ends_tests() {
        let cell = Cell::default();
        let slice = OwnedCellSlice::new_allow_exotic(cell.clone());

        assert_run_vm!("ENDS", [slice slice.clone()] => []);
        assert_run_vm!("ENDS", [int 1, slice slice] => [int 1]);

        let mut cb = CellBuilder::new();
        cb.store_u8(1).unwrap();
        let cell = cb.build().unwrap();
        let sc = OwnedCellSlice::new_allow_exotic(cell);

        assert_run_vm!("ENDS", [slice sc] => [int 0], exit_code: 9)
    }

    #[test]
    #[traced_test]
    fn ldi_tests() {
        let slice = make_int_cell_slice(i128::MIN, 257);

        let (left, right) = cut_slice_to_int(&slice, 16);
        assert_run_vm!("LDI 16", [slice slice.clone()] => [int left, slice right.clone()]);

        let (left, right) = cut_slice_to_int(&slice, 32);
        assert_run_vm!("LDI 32", [slice slice.clone()] => [int left, slice right.clone()]);

        let (left, right) = cut_slice_to_int(&slice, 1);
        assert_run_vm!("LDI 1", [slice slice.clone()] => [int left, slice right.clone()]);

        let slice = make_int_cell_slice(i128::MAX, 255);
        assert_run_vm!("LDIQ 256", [slice slice.clone()] => [slice slice.clone(), int 0]);
    }

    #[test]
    #[traced_test]
    fn ldu_tests() {
        let slice = make_int_cell_slice(i128::MIN, 256);

        let (left, right) = cut_slice_to_int(&slice, 16);
        assert_run_vm!("LDI 16", [slice slice.clone()] => [int left, slice right.clone()]);

        let (left, right) = cut_slice_to_int(&slice, 32);
        assert_run_vm!("LDI 32", [slice slice.clone()] => [int left, slice right.clone()]);

        let (left, right) = cut_slice_to_int(&slice, 1);
        assert_run_vm!("LDI 1", [slice slice.clone()] => [int left, slice right.clone()]);

        let slice = make_int_cell_slice(i128::MAX, 254);
        assert_run_vm!("LDIQ 255", [slice slice.clone()] => [slice slice.clone(), int 0]);
    }

    #[test]
    #[traced_test]
    fn ldref_tests() {
        let cell = make_cell_with_reference();
        let reference = cell.reference_cloned(0).unwrap();

        let mut slice = OwnedCellSlice::new_allow_exotic(cell.clone());
        let initial_rc_slice = slice.clone();

        let mut cs = slice.apply();
        cs.skip_first(0, 1).unwrap();
        slice.set_range(cs.range());

        assert_run_vm!("LDREF", [slice initial_rc_slice.clone()] => [cell reference.clone(), slice slice]);

        let slice = OwnedCellSlice::new_allow_exotic(cell.clone());
        let mut initial_rc_slice = slice.clone();
        let mut cs = initial_rc_slice.apply();
        cs.skip_first(0, 1).unwrap();
        initial_rc_slice.set_range(cs.range());

        assert_run_vm!("LDREF", [slice initial_rc_slice] => [int 0], exit_code: 9);
    }

    #[test]
    #[traced_test]
    fn ldrefrtos_tests() {
        let cell = make_cell_with_reference();
        let reference = cell.reference_cloned(0).unwrap();

        let initial_cell = OwnedCellSlice::new_allow_exotic(cell.clone());
        let result_slice = OwnedCellSlice::new_allow_exotic(reference.clone());

        let mut slice = OwnedCellSlice::new_allow_exotic(cell.clone());
        let mut cs = slice.apply();
        cs.skip_first(0, 1).unwrap();
        slice.set_range(cs.range());

        assert_run_vm!("LDREFRTOS", [slice initial_cell] => [slice slice, slice result_slice]);
    }

    #[test]
    #[traced_test]
    fn ldslice_tests() {
        let slice = make_uint_cell_slice(1000, 32);
        let (left, right) = cut_slice(&slice, 16);

        assert_run_vm!("LDSLICE 16", [slice slice.clone()] => [slice left, slice right]);

        let (left, right) = cut_slice(&slice, 32);
        assert_run_vm!("LDSLICE 32", [slice slice.clone()] => [slice left, slice right]);

        let (left, right) = cut_slice(&slice, 1);
        assert_run_vm!("LDSLICE 1", [slice slice.clone()] => [slice left.clone(), slice right.clone()]);
        assert_run_vm!("LDSLICEQ 1", [slice slice.clone()] => [slice left, slice right, int -1]);
        assert_run_vm!("LDSLICE 33", [slice slice.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("LDSLICEQ 33", [slice slice.clone()] => [slice slice, int 0]);
    }

    #[test]
    #[traced_test]
    fn ldslicex_tests() {
        let slice = make_uint_cell_slice(1000, 32);
        let (left, right) = cut_slice(&slice, 16);

        assert_run_vm!("LDSLICEX", [slice slice.clone(), int 16] => [slice left, slice right]);

        let (left, right) = cut_slice(&slice, 32);
        assert_run_vm!("LDSLICEX", [slice slice.clone(), int 32] => [slice left.clone(), slice right.clone()]);
        assert_run_vm!("LDSLICEXQ", [slice slice.clone(), int 32] => [slice left, slice right, int -1]);

        let (left, right) = cut_slice(&slice, 1);
        assert_run_vm!("LDSLICEX", [slice slice.clone(), int 1] => [slice left, slice right]);
        assert_run_vm!("LDSLICEX", [slice slice.clone(), int 33] => [int 0], exit_code: 9);
        assert_run_vm!("LDSLICEXQ", [slice slice.clone(), int 33] => [slice slice, int 0]);
    }

    #[test]
    #[traced_test]
    fn ldix_tests() {
        let slice = make_int_cell_slice(i128::MIN, 257);

        let (left, right) = cut_slice_to_int(&slice, 16);
        assert_run_vm!("LDIX", [slice slice.clone(), int 16] => [int left, slice right.clone()]);

        let (left, right) = cut_slice_to_int(&slice, 32);
        assert_run_vm!("LDIX", [slice slice.clone(), int 32] => [int left, slice right.clone()]);

        let (left, right) = cut_slice_to_int(&slice, 1);
        assert_run_vm!("LDIX", [slice slice.clone(), int 1] => [int left, slice right.clone()]);

        assert_run_vm!("LDIX", [slice slice.clone(), int 258] => [int 0], exit_code: 5);
        assert_run_vm!("LDIXQ", [slice slice.clone(), int 258] => [int 0], exit_code: 5);

        let slice = make_int_cell_slice(i128::MAX, 256);
        assert_run_vm!("LDIXQ", [slice slice.clone(), int 257] => [slice slice.clone(), int 0]);
    }

    #[test]
    #[traced_test]
    fn ldux_tests() {
        let slice = make_uint_cell_slice(u128::MAX, 256);

        let (left, right) = cut_slice_to_uint(&slice, 16);
        assert_run_vm!("LDIX", [slice slice.clone(), int 16] => [int left, slice right.clone()]);

        let (left, right) = cut_slice_to_uint(&slice, 32);
        assert_run_vm!("LDUX", [slice slice.clone(), int 32] => [int left, slice right.clone()]);

        let (left, right) = cut_slice_to_uint(&slice, 1);
        assert_run_vm!("LDUX", [slice slice.clone(), int 1] => [int left, slice right.clone()]);

        assert_run_vm!("LDUX", [slice slice.clone(), int 257] => [int 0], exit_code: 5);
        assert_run_vm!("LDUXQ", [slice slice.clone(), int 257] => [int 0], exit_code: 5);

        let slice = make_uint_cell_slice(u128::MAX, 255);
        assert_run_vm!("LDUXQ", [slice slice.clone(), int 256] => [slice slice.clone(), int 0]);
    }

    #[test]
    #[traced_test]
    fn pldi_tests() {
        let slice = make_int_cell_slice(i128::MIN, 200);
        let i = extract_int(&slice, 200);
        assert_run_vm!("PLDI 200", [slice slice.clone()] => [int i.clone()]);
        assert_run_vm!("PLDIQ 200", [slice slice.clone()] => [int i, int -1]);
        let i = extract_int(&slice, 37);
        assert_run_vm!("PLDI 37", [slice slice.clone()] => [int i.clone()]);

        let _i = extract_int(&slice, 200);
        assert_run_vm!("PLDI 210", [slice slice.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("PLDIQ 210", [slice slice.clone()] => [int 0]);
    }

    #[test]
    #[traced_test]
    fn pldu_tests() {
        let slice = make_uint_cell_slice(u128::MAX, 200);
        let i = extract_uint(&slice, 200);
        assert_run_vm!("PLDI 200", [slice slice.clone()] => [int i.clone()]);
        assert_run_vm!("PLDIQ 200", [slice slice.clone()] => [int i, int -1]);
        let i = extract_int(&slice, 37);
        assert_run_vm!("PLDI 37", [slice slice.clone()] => [int i.clone()]);

        let _i = extract_int(&slice, 200);
        assert_run_vm!("PLDI 210", [slice slice.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("PLDIQ 210", [slice slice.clone()] => [int 0]);
    }

    #[test]
    #[traced_test]
    fn pldix_tests() {
        let slice = make_int_cell_slice(i128::MIN, 200);
        let i = extract_int(&slice, 200);
        assert_run_vm!("PLDIX", [slice slice.clone(), int 200] => [int i.clone()]);
        assert_run_vm!("PLDIXQ", [slice slice.clone(), int 200] => [int i, int -1]);
        let i = extract_int(&slice, 37);
        assert_run_vm!("PLDIX", [slice slice.clone(), int 37] => [int i.clone()]);

        let _i = extract_int(&slice, 200);
        assert_run_vm!("PLDIX", [slice slice.clone(), int 210] => [int 0], exit_code: 9);
        assert_run_vm!("PLDIXQ", [slice slice.clone(), int 210] => [int 0]);
    }

    #[test]
    #[traced_test]
    fn pldux_tests() {
        let slice = make_uint_cell_slice(u128::MAX, 200);
        let i = extract_uint(&slice, 200);
        assert_run_vm!("PLDUX", [slice slice.clone(), int 200] => [int i.clone()]);
        assert_run_vm!("PLDUXQ", [slice slice.clone(), int 200] => [int i, int -1]);

        // let i = extract_uint(&slice, 64);
        // assert_run_vm!("PLDUZ 64", [raw Rc::new(slice.clone())] => [raw Rc::new(slice.clone()), int i.clone()]);

        let i = extract_int(&slice, 37);
        assert_run_vm!("PLDUX", [slice slice.clone(), int 37] => [int i.clone()]);

        let _i = extract_int(&slice, 200);
        assert_run_vm!("PLDUX", [slice slice.clone(), int 210] => [int 0], exit_code: 9);
        assert_run_vm!("PLDUXQ", [slice slice.clone(), int 210] => [int 0]);
    }

    #[test]
    #[traced_test]
    fn pldslice_tests() {
        let slice = make_uint_cell_slice(1000, 512);
        let prefix = cut_slice_prefix(&slice, 256, 0);
        assert_run_vm!("PLDSLICE 256", [slice slice.clone()] => [slice prefix.clone()]);
        assert_run_vm!("PLDSLICEQ 256", [slice slice.clone()] => [slice prefix.clone(), int -1]);

        let prefix = cut_slice_prefix(&slice, 1, 0);
        assert_run_vm!("PLDSLICE 1", [slice slice.clone()] => [slice prefix.clone()]);
        let _prefix = cut_slice_prefix(&slice, 0, 0);

        let slice = make_uint_cell_slice(1000, 128);
        assert_run_vm!("PLDSLICE 129", [slice slice.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("PLDSLICEQ 129", [slice slice.clone()] => [int 0]);
    }

    #[test]
    #[traced_test]
    fn pldslicex_tests() {
        let slice = make_uint_cell_slice(1000, 512);
        let prefix = cut_slice_prefix(&slice, 256, 0);
        assert_run_vm!("PLDSLICEX", [slice slice.clone(), int 256] => [slice prefix.clone()]);
        assert_run_vm!("SDCUTFIRST", [slice slice.clone(), int 256] => [slice prefix.clone()]);
        assert_run_vm!("PLDSLICEXQ", [slice slice.clone(), int 256] => [slice prefix.clone(), int -1],);

        let prefix = cut_slice_prefix(&slice, 1, 0);
        assert_run_vm!("PLDSLICEX", [slice slice.clone(), int 1] => [slice prefix.clone()]);
        assert_run_vm!("SDCUTFIRST", [slice slice.clone(), int 1] => [slice prefix.clone()]);
        let _prefix = cut_slice_prefix(&slice, 0, 0);

        let slice = make_uint_cell_slice(1000, 128);
        assert_run_vm!("PLDSLICEX", [slice slice.clone(), int 129] => [int 0], exit_code: 9);
        assert_run_vm!("SDCUTFIRST", [slice slice.clone(), int 129] => [int 0], exit_code: 9);
        assert_run_vm!("PLDSLICEXQ", [slice slice.clone(), int 129] => [int 0]);
    }

    #[test]
    #[traced_test]
    fn cut_tests() {
        let slice = make_uint_cell_slice(1000, 512);
        let suffix = cut_slice_suffix(&slice, 256, 0);

        assert_run_vm!("SDSKIPFIRST", [slice slice.clone(), int 256] => [slice suffix.clone()]);
        assert_run_vm!("SDSKIPFIRST", [slice slice.clone(), int 513] => [int 0], exit_code: 9);

        assert_run_vm!("LDSLICEX NIP", [slice slice.clone(), int 256] => [slice suffix.clone()]);
        assert_run_vm!("LDSLICEX NIP", [slice slice.clone(), int 513] => [int 0], exit_code: 9);

        assert_run_vm!("SDCUTLAST", [slice slice.clone(), int 256] => [slice suffix.clone()]);
        let suffix = cut_slice_suffix(&slice, 512, 0);

        assert_run_vm!("SDCUTLAST", [slice slice.clone(), int 512] => [slice suffix.clone()]);

        let suffix = cut_slice_suffix(&slice, 0, 0);
        assert_run_vm!("SDCUTLAST", [slice slice.clone(), int 0] => [slice suffix.clone()]);
        assert_run_vm!("SDCUTLAST", [slice slice.clone(), int 513] => [int 0], exit_code: 9);

        let prefix = cut_slice_prefix(&slice, 512, 0);
        assert_run_vm!("SDSKIPLAST", [slice slice.clone(), int 0] => [slice prefix.clone()]);

        let prefix = cut_slice_prefix(&slice, 256, 0);
        assert_run_vm!("SDSKIPLAST", [slice slice.clone(), int 256] => [slice prefix.clone()]);
        let prefix = cut_slice_prefix(&slice, 0, 0);
        assert_run_vm!("SDSKIPLAST", [slice slice.clone(), int 512] => [slice prefix.clone()]);

        assert_run_vm!("SDSKIPLAST", [slice slice.clone(), int 513] => [int 0], exit_code: 9);
    }

    #[test]
    #[traced_test]
    fn cut_with_refs_tests() {
        let slice = make_cell_slice_with_refs(1000, 512, 2);
        let prefix = cut_slice_prefix(&slice, 256, 2);
        assert_run_vm!("SCUTFIRST", [slice slice.clone(), int 256, int 2] => [slice prefix.clone()]);
        assert_run_vm!("SCUTFIRST", [slice slice.clone(), int 512, int 2] => [slice slice.clone()]);
        assert_run_vm!("SCUTFIRST", [slice slice.clone(), int 256, int 3] => [int 0], exit_code: 9);

        assert_run_vm!("SSKIPLAST", [slice slice.clone(), int 256, int 0] => [slice prefix.clone()]);
        assert_run_vm!("SSKIPLAST", [slice slice.clone(), int 0, int 0] => [slice slice.clone()]);
        assert_run_vm!("SSKIPLAST", [slice slice.clone(), int 256, int 3] => [int 0], exit_code: 9);

        let suffix = cut_slice_suffix(&slice, 256, 2);

        assert_run_vm!("SCUTLAST", [slice slice.clone(), int 256, int 2] => [slice suffix.clone()]);
        assert_run_vm!("SCUTLAST", [slice slice.clone(), int 512, int 2] => [slice slice.clone()]);
        assert_run_vm!("SCUTLAST", [slice slice.clone(), int 256, int 3] => [int 0], exit_code: 9);

        assert_run_vm!("SSKIPFIRST", [slice slice.clone(), int 256, int 0] => [slice suffix.clone()]);
        assert_run_vm!("SSKIPFIRST", [slice slice.clone(), int 0, int 0] => [slice slice.clone()]);
        assert_run_vm!("SSKIPFIRST", [slice slice.clone(), int 256, int 3] => [int 0], exit_code: 9);
    }

    #[test]
    #[traced_test]
    fn subslice_tests() {
        let slice = make_cell_slice_with_refs(1000, 512, 4);
        let initial = slice.clone();
        let subslice = get_subslice(&slice, 10, 10, 0, 0);
        assert_run_vm!("SDSUBSTR", [slice initial.clone(), int 10, int 10] => [slice subslice]);

        let subslice = get_subslice(&slice, 0, 0, 0, 0);
        assert_run_vm!("SDSUBSTR", [slice initial.clone(), int 0, int 0] => [slice subslice]);

        let subslice = get_subslice(&slice, 100, 50, 0, 0);
        assert_run_vm!("SDSUBSTR", [slice initial.clone(), int 100, int 50] => [slice subslice]);
        assert_run_vm!("SDSUBSTR", [slice initial.clone(), int 100, int 513] => [int 0], exit_code: 9);
        assert_run_vm!("SDSUBSTR", [slice initial.clone(), int 513, int 5] => [int 0], exit_code: 9);

        let subslice = get_subslice(&slice, 100, 50, 0, 4);
        assert_run_vm!("SUBSLICE", [slice initial.clone(), int 100, int 0, int 50, int 4] => [slice subslice]);

        let subslice = get_subslice(&slice, 1, 50, 2, 2);
        assert_run_vm!("SUBSLICE", [slice initial.clone(), int 1, int 2, int 50, int 2] => [slice subslice]);
        assert_run_vm!("SUBSLICE", [slice initial.clone(), int 1, int 2, int 50, int 3] => [int 0], exit_code: 9);

        assert_run_vm!("SUBSLICE", [slice initial.clone(), int 100, int 0, int 50, int 5] => [int 0], exit_code: 5);
        assert_run_vm!("SUBSLICE", [slice initial.clone(), int 100, int 5, int 50, int 4] => [int 0], exit_code: 5);
    }

    #[test]
    #[traced_test]
    fn check_tests() {
        let slice = make_cell_slice_with_refs(1000, 512, 2);
        assert_run_vm!("SCHKBITS", [slice slice.clone(), int 512] => []);
        assert_run_vm!("SCHKBITS", [slice slice.clone(), int 0] => []);
        assert_run_vm!("SCHKBITSQ", [slice slice.clone(), int 0] => [int -1]);

        assert_run_vm!("SCHKBITS", [slice slice.clone(), int 1023] => [int 0,], exit_code: 8);
        assert_run_vm!("SCHKBITS", [slice slice.clone(), int 99999999] => [int 0], exit_code: 5);
        assert_run_vm!("SCHKBITSQ", [slice slice.clone(), int 1023] => [int 0]);

        assert_run_vm!("SCHKREFS", [slice slice.clone(), int 2] => []);
        assert_run_vm!("SCHKREFS", [slice slice.clone(), int 0] => []);
        assert_run_vm!("SCHKREFSQ", [slice slice.clone(), int 1] => [int -1]);

        assert_run_vm!("SCHKREFS", [slice slice.clone(), int 3] => [int 0], exit_code: 8);
        assert_run_vm!("SCHKREFS", [slice slice.clone(), int 99999] => [int 0], exit_code: 5);
        assert_run_vm!("SCHKREFSQ", [slice slice.clone(), int 3] => [int 0]);

        assert_run_vm!("SCHKBITREFS", [slice slice.clone(), int 512, int 2] => []);
        assert_run_vm!("SCHKBITREFS", [slice slice.clone(), int 0, int 0] => []);
        assert_run_vm!("SCHKBITREFSQ", [slice slice.clone(), int 0, int 1] => [int -1]);

        assert_run_vm!("SCHKBITREFS", [slice slice.clone(), int 1023, int 3] => [int 0], exit_code: 8);
        assert_run_vm!("SCHKBITREFSQ", [slice slice.clone(), int 1023, int 3] => [int 0]);
    }

    #[test]
    #[traced_test]
    fn info_tests() {
        let slice = make_cell_slice_with_refs(1000, 512, 2);
        let cs = slice.apply();
        let cell = cs.get_reference_cloned(0).unwrap();
        assert_run_vm!("PLDREFVAR", [slice slice.clone(), int 0] => [cell cell.clone()]);
        assert_run_vm!("PLDREF", [slice slice.clone()] => [cell cell.clone()]);
        assert_run_vm!("PLDREFIDX 0", [slice slice.clone()] => [cell cell]);

        let cell = cs.get_reference_cloned(1).unwrap();
        assert_run_vm!("PLDREFVAR", [slice slice.clone(), int 1] => [cell cell.clone()]);
        assert_run_vm!("PLDREFIDX 1", [slice slice.clone()] => [cell cell]);

        assert_run_vm!("PLDREFVAR", [slice slice.clone(), int 3] => [int 0], exit_code: 9);
        assert_run_vm!("PLDREFIDX 3", [slice slice.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("PLDREFVAR", [slice slice.clone(), int 10] => [int 0], exit_code: 5);

        assert_run_vm!("SBITS", [slice slice.clone()] => [int 512]);
        assert_run_vm!("SREFS", [slice slice.clone()] => [int 2]);
        assert_run_vm!("SBITREFS", [slice slice.clone()] => [int 512, int 2]);
    }

    #[test]
    #[traced_test]
    fn begins_tests() {
        let slice = make_uint_cell_slice(1, 8);
        let prefix = make_uint_cell_slice(0b0000, 4);
        let result = skip_common(&slice, &prefix);

        assert_run_vm!("SDBEGINSX", [slice slice.clone(), slice prefix.clone()] => [slice result.clone()]);
        assert_run_vm!("SDBEGINSXQ", [slice slice.clone(), slice prefix.clone()] => [slice result, int -1]);

        let prefix = make_uint_cell_slice(0b11, 9);
        assert_run_vm!("SDBEGINSX", [slice slice.clone(), slice prefix.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("SDBEGINSXQ", [slice slice.clone(), slice prefix.clone()] => [slice slice.clone(), int 0]);
    }

    #[test]
    #[traced_test]
    fn load_library_cell() {
        let main_code = Boc::decode(tvmasm! {
            r#"
            PUSHREF @{2b698ae42e5cbea6096608a76572ad2fabd5c706a701bedb6369799c0d175c0f}
            XLOAD
            CTOS
            BLESS
            EXECUTE
            "#
        })
        .unwrap();

        let library_code = Boc::decode(tvmasm! {
            r#"
            PUSHINT 10
            PUSHINT 11
            "#
        })
        .unwrap();

        let libraries = HashMap::from([(
            "2b698ae42e5cbea6096608a76572ad2fabd5c706a701bedb6369799c0d175c0f"
                .parse::<HashBytes>()
                .unwrap(),
            SimpleLib {
                public: true,
                root: library_code,
            },
        )]);

        let mut output = crate::tests::TracingOutput::default();
        let mut state = VmState::builder()
            .with_version(crate::VmVersion::LATEST_TON)
            .with_code(main_code)
            .with_libraries(&libraries)
            .with_debug(&mut output)
            .build();

        let result = state.run();
        println!("execution result {:?}", !result);
    }

    #[test]
    #[traced_test]
    fn load_exotic_cells() -> anyhow::Result<()> {
        // Ordinary
        let cell = Cell::default();
        assert_run_vm!("CTOS", [cell cell.clone()] => [slice OwnedCellSlice::new_allow_exotic(cell.clone())]);
        assert_run_vm!("XCTOS", [cell cell.clone()] => [slice OwnedCellSlice::new_allow_exotic(cell.clone()), int 0]);
        assert_run_vm!("XLOAD", [cell cell.clone()] => [cell cell.clone()]);
        assert_run_vm!("XLOADQ", [cell cell.clone()] => [cell cell.clone(), int -1]);

        // Pruned branch
        let pruned_branch = tycho_types::merkle::make_pruned_branch(
            Cell::empty_cell_ref(),
            0,
            Cell::empty_context(),
        )?;
        assert_run_vm!("CTOS", [cell pruned_branch.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("XCTOS", [cell pruned_branch.clone()] => [slice OwnedCellSlice::new_allow_exotic(pruned_branch.clone()), int -1]);
        assert_run_vm!("XLOAD", [cell pruned_branch.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("XLOADQ", [cell pruned_branch.clone()] => [int 0]);

        // Merkle proof
        let merkle_proof = CellBuilder::build_from(MerkleProof::default())?;
        assert_run_vm!("CTOS", [cell merkle_proof.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("XCTOS", [cell merkle_proof.clone()] => [slice OwnedCellSlice::new_allow_exotic(merkle_proof.clone()), int -1]);
        assert_run_vm!("XLOAD", [cell merkle_proof.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("XLOADQ", [cell merkle_proof.clone()] => [int 0]);

        // Merkle update
        let merkle_update = CellBuilder::build_from(MerkleUpdate::default())?;
        assert_run_vm!("CTOS", [cell merkle_update.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("XCTOS", [cell merkle_update.clone()] => [slice OwnedCellSlice::new_allow_exotic(merkle_update.clone()), int -1]);
        assert_run_vm!("XLOAD", [cell merkle_update.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("XLOADQ", [cell merkle_update.clone()] => [int 0]);

        // Library
        let library_code = Boc::decode(tvmasm!("NOP"))?;
        let library = {
            let mut b = CellBuilder::new();
            b.set_exotic(true);
            b.store_u8(CellType::LibraryReference.to_byte())?;
            b.store_u256(library_code.repr_hash())?;
            b.build()?
        };

        // - unregistered
        assert_run_vm!("CTOS", [cell library.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("XCTOS", [cell library.clone()] => [slice OwnedCellSlice::new_allow_exotic(library.clone()), int -1]);
        assert_run_vm!("XLOAD", [cell library.clone()] => [int 0], exit_code: 9);
        assert_run_vm!("XLOADQ", [cell library.clone()] => [int 0]);

        // - registered
        let libs = HashMap::from([(*library_code.repr_hash(), SimpleLib {
            public: true,
            root: library_code.clone(),
        })]);

        assert_run_vm!("CTOS", libs: libs.clone(), [cell library.clone()] => [slice OwnedCellSlice::new_allow_exotic(library_code.clone())]);
        assert_run_vm!("XCTOS", libs: libs.clone(), [cell library.clone()] => [slice OwnedCellSlice::new_allow_exotic(library.clone()), int -1]);
        assert_run_vm!("XLOAD", libs: libs.clone(), [cell library.clone()] => [cell library_code.clone()]);
        assert_run_vm!("XLOADQ", libs: libs.clone(), [cell library.clone()] => [cell library_code.clone(), int -1]);

        Ok(())
    }

    fn skip_common(slice: &OwnedCellSlice, prefix: &OwnedCellSlice) -> OwnedCellSlice {
        let common = get_common_prefix(slice, prefix);
        let mut slice = slice.clone();
        slice
            .range_mut()
            .skip_first(common.range().size_bits(), 0)
            .unwrap();
        slice
    }

    fn get_common_prefix(slice: &OwnedCellSlice, prefix: &OwnedCellSlice) -> OwnedCellSlice {
        let cs = slice.apply();
        let prefix = prefix.apply();
        let common = cs.longest_common_data_prefix(&prefix);
        let mut slice = slice.clone();
        slice.set_range(common.range());
        slice
    }

    fn get_subslice(
        slice: &OwnedCellSlice,
        from: u16,
        len: u16,
        from_refs: u8,
        refs_count: u8,
    ) -> OwnedCellSlice {
        let mut new = slice.clone();
        let mut range = slice.range();
        range.skip_first(from, from_refs).unwrap();
        range.only_first(len, refs_count).unwrap();
        new.set_range(range);
        new
    }

    fn make_cell_slice_with_refs(value: u128, bits: u16, refs_count: u8) -> OwnedCellSlice {
        let mut cb = CellBuilder::new();
        cb.store_bigint(&BigInt::from(value), bits, false).unwrap();

        for _ in 0..refs_count {
            let mut rb = CellBuilder::new();
            rb.store_u64(u64::MAX).unwrap();
            let cell = rb.build().unwrap();
            cb.store_reference(cell).unwrap()
        }
        let cell = cb.build().unwrap();
        OwnedCellSlice::new_allow_exotic(cell)
    }

    fn make_uint_cell_slice(value: u128, bits: u16) -> OwnedCellSlice {
        let mut cb = CellBuilder::new();
        cb.store_bigint(&BigInt::from(value), bits, false).unwrap();
        let cell = cb.build().unwrap();
        OwnedCellSlice::new_allow_exotic(cell)
    }

    fn make_int_cell_slice(value: i128, bits: u16) -> OwnedCellSlice {
        let mut cb = CellBuilder::new();
        cb.store_bigint(&BigInt::from(value), bits, true).unwrap();
        let cell = cb.build().unwrap();
        OwnedCellSlice::new_allow_exotic(cell)
    }

    fn cut_slice(slice: &OwnedCellSlice, bits: u16) -> (OwnedCellSlice, OwnedCellSlice) {
        let mut cs = slice.apply();
        let prefix = cs.load_prefix(bits, 0).unwrap();
        let mut left = slice.clone();
        let mut right = slice.clone();

        left.set_range(prefix.range());
        right.set_range(cs.range());
        (left, right)
    }

    fn cut_slice_prefix(slice: &OwnedCellSlice, bits: u16, refs: u8) -> OwnedCellSlice {
        let mut cs = slice.apply();
        let prefix = cs.load_prefix(bits, refs).unwrap();
        let mut slice = slice.clone();
        slice.set_range(prefix.range());
        slice
    }

    fn cut_slice_suffix(slice: &OwnedCellSlice, bits: u16, refs: u8) -> OwnedCellSlice {
        let mut cs = slice.apply();
        let suffix = cs.load_suffix(bits, refs).unwrap();
        let mut slice = slice.clone();
        slice.set_range(suffix.range());
        slice
    }

    fn cut_slice_to_uint(slice: &OwnedCellSlice, bits: u16) -> (BigInt, OwnedCellSlice) {
        let mut cs = slice.apply();
        let prefix = cs.load_bigint(bits, false).unwrap();

        let mut right = slice.clone();
        right.set_range(cs.range());
        (prefix, right)
    }

    fn cut_slice_to_int(slice: &OwnedCellSlice, bits: u16) -> (BigInt, OwnedCellSlice) {
        let mut cs = slice.apply();
        let prefix = cs.load_bigint(bits, true).unwrap();

        let mut right = slice.clone();
        right.set_range(cs.range());
        (prefix, right)
    }

    fn extract_int(slice: &OwnedCellSlice, bits: u16) -> BigInt {
        let cs = slice.apply();
        get_int_from_slice(&cs, bits, true).unwrap()
    }

    fn extract_uint(slice: &OwnedCellSlice, bits: u16) -> BigInt {
        let cs = slice.apply();
        get_int_from_slice(&cs, bits, false).unwrap()
    }

    fn make_cell_with_reference() -> Cell {
        let mut cb = CellBuilder::new();
        cb.store_reference(Cell::default()).unwrap();
        cb.build().unwrap()
    }

    fn get_int_from_slice(slice: &CellSlice<'_>, bits: u16, signed: bool) -> Result<BigInt, Error> {
        match bits {
            0 => Ok(BigInt::default()),
            0..=64 if !signed => slice.get_uint(slice.offset_bits(), bits).map(BigInt::from),
            0..=64 if signed => slice.get_uint(slice.offset_bits(), bits).map(|mut int| {
                if bits < 64 {
                    // Clone sign bit into all high bits
                    int |= ((int >> (bits - 1)) * u64::MAX) << (bits - 1);
                }
                BigInt::from(int as i64)
            }),
            _ => {
                let rem = bits % 8;
                let mut buffer = [0u8; 33];
                slice
                    .get_raw(slice.offset_bits(), &mut buffer, bits)
                    .map(|buffer| {
                        let mut int = if signed {
                            BigInt::from_signed_bytes_be(buffer)
                        } else {
                            BigInt::from_bytes_be(Sign::Plus, buffer)
                        };
                        if bits % 8 != 0 {
                            int >>= 8 - rem;
                        }
                        int
                    })
            }
        }
    }
}
