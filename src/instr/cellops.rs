use std::borrow::Cow;
use std::rc::Rc;

use anyhow::Result;
use everscale_types::cell::{
    Cell, CellBuilder, CellContext, CellFamily, CellSlice, DynCell, LoadMode,
};
use everscale_types::error::Error;
use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, Sign};
use num_traits::{ToPrimitive, Zero};

use crate::cont::OrdCont;
use crate::dispatch::Opcodes;
use crate::error::{VmError, VmResult};
use crate::stack::{RcStackValue, Stack};
use crate::state::VmState;
use crate::util::{bitsize, load_int_from_slice, remove_trailing, OwnedCellSlice};

pub struct Cellops;

#[vm_module]
impl Cellops {
    // === Const ops ===

    #[init]
    fn init_cell_const(&self, t: &mut Opcodes) -> Result<()> {
        t.add_ext(0x88, 8, 0, exec_push_ref)?;
        t.add_ext(0x89, 8, 0, exec_push_ref_slice)?;
        t.add_ext(0x8a, 8, 0, exec_push_ref_cont)?;
        t.add_ext(0x8b, 8, 4, exec_push_slice)?;
        t.add_ext(0x8c, 8, 7, exec_push_slice_r)?;
        t.add_ext_range(0x8d << 10, ((0x8d << 3) + 5) << 7, 18, exec_push_slice_r2)?;
        t.add_ext(0x8e >> 1, 7, 9, exec_push_cont)?;
        t.add_ext(0x9, 4, 4, exec_push_cont_simple)
    }

    fn exec_push_ref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_push_ref_common(st, bits, "PUSHREF", PushRefMode::Cell)
    }

    fn exec_push_ref_slice(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_push_ref_common(st, bits, "PUSHREFSLICE", PushRefMode::Slice)
    }

    fn exec_push_ref_cont(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_push_ref_common(st, bits, "PUSHREFCONT", PushRefMode::Cont)
    }

    fn exec_push_slice(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0xf) * 8 + 4) as u16;
        exec_push_slice_common(st, bits, data_bits, 0)
    }

    fn exec_push_slice_r(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0x1f) * 8 + 1) as u16;
        let refs = (((args >> 5) & 0b11) + 1) as u8;
        exec_push_slice_common(st, bits, data_bits, refs)
    }

    fn exec_push_slice_r2(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0x7f) * 8 + 6) as u16;
        let refs = ((args >> 7) & 0b111) as u8;
        exec_push_slice_common(st, bits, data_bits, refs)
    }

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

        let code = OwnedCellSlice::from((st.code.cell().clone(), slice_range));
        vm_log!("execute PUSHCONT {}", code);

        let cont = Rc::new(OrdCont::simple(code, st.cp.id()));
        ok!(Rc::make_mut(&mut st.stack).push_raw(cont));
        Ok(0)
    }

    fn exec_push_cont_simple(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0xf) * 8) as u16;

        let code_range = st.code.range_mut();
        vm_ensure!(code_range.has_remaining(bits + data_bits, 0), InvalidOpcode);
        code_range.skip_first(bits, 0).ok();

        let mut slice_range = *code_range;
        slice_range.only_first(data_bits, 0).ok();

        code_range.skip_first(data_bits, 0).ok();

        let code = OwnedCellSlice::from((st.code.cell().clone(), slice_range));
        vm_log!("execute PUSHCONT {}", code);

        let cont = Rc::new(OrdCont::simple(code, st.cp.id()));
        ok!(Rc::make_mut(&mut st.stack).push_raw(cont));
        Ok(0)
    }

    // === Slice comparison ops ===

    #[instr(code = "c700", fmt = "SEMPTY", args(op = SliceBoolUnaryOp::IsEmpty))]
    #[instr(code = "c701", fmt = "SDEMPTY", args(op = SliceBoolUnaryOp::NoBits))]
    #[instr(code = "c702", fmt = "SREMPTY", args(op = SliceBoolUnaryOp::NoRefs))]
    #[instr(code = "c703", fmt = "SDFIRST", args(op = SliceBoolUnaryOp::FirstBit))]
    fn exec_slice_bool_unary_op(st: &mut VmState, op: SliceBoolUnaryOp) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let range = cs.range();
        let res = match op {
            SliceBoolUnaryOp::IsEmpty => range.is_data_empty() && range.is_refs_empty(),
            SliceBoolUnaryOp::NoBits => range.is_data_empty(),
            SliceBoolUnaryOp::NoRefs => range.is_refs_empty(),
            SliceBoolUnaryOp::FirstBit => {
                let slice = cs.apply_allow_special();
                slice.get_bit(0).unwrap_or_default()
            }
        };
        ok!(stack.push_bool(res));
        Ok(0)
    }

    #[instr(code = "c704", fmt = "SDLEXCMP")]
    fn exec_slice_lex_cmp(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs2 = ok!(stack.pop_cs());
        let cs1 = ok!(stack.pop_cs());

        let slice1 = cs1.apply_allow_special();
        let slice2 = cs2.apply_allow_special();

        let res = slice1.lex_cmp(&slice2)? as i8;
        ok!(stack.push_int(res));
        Ok(0)
    }

    #[instr(code = "c705", fmt = "SDEQ", args(op = SliceBinaryOp::DataEq))]
    #[instr(code = "c708", fmt = "SDPFX", args(op = SliceBinaryOp::IsPrefix))]
    #[instr(code = "c709", fmt = "SDPFXREV", args(op = SliceBinaryOp::IsPrefixRev))]
    #[instr(code = "c70a", fmt = "SDPPFX", args(op = SliceBinaryOp::IsProperPrefix))]
    #[instr(code = "c70b", fmt = "SDPPFXREV", args(op = SliceBinaryOp::IsProperPrefixRev))]
    #[instr(code = "c70c", fmt = "SDSFX", args(op = SliceBinaryOp::IsSuffix))]
    #[instr(code = "c70d", fmt = "SDSFXREV", args(op = SliceBinaryOp::IsSuffixRev))]
    #[instr(code = "c70e", fmt = "SDPSFX", args(op = SliceBinaryOp::IsProperSuffix))]
    #[instr(code = "c70f", fmt = "SDPSFXREV", args(op = SliceBinaryOp::IsProperSuffixRev))]
    fn exec_slice_bin_op(st: &mut VmState, op: SliceBinaryOp) -> VmResult<i32> {
        fn is_proper(left: &CellSlice<'_>, right: &CellSlice<'_>) -> bool {
            left.size_bits() < right.size_bits()
        }

        let stack = Rc::make_mut(&mut st.stack);
        let cs2 = ok!(stack.pop_cs());
        let cs1 = ok!(stack.pop_cs());

        let slice1 = cs1.apply_allow_special();
        let slice2 = cs2.apply_allow_special();

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

    #[instr(code = "c710", fmt = "SDCNTLEAD0", args(op = SliceIntUnaryOp::Leading0))]
    #[instr(code = "c711", fmt = "SDCNTLEAD1", args(op = SliceIntUnaryOp::Leading1))]
    #[instr(code = "c712", fmt = "SDCNTTRAIL0", args(op = SliceIntUnaryOp::Trailing0))]
    #[instr(code = "c713", fmt = "SDCNTTRAIL1", args(op = SliceIntUnaryOp::Trailing1))]
    fn exec_slice_int_unary_op(st: &mut VmState, op: SliceIntUnaryOp) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let slice = cs.apply_allow_special();
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

    #[init]
    fn init_serializer_ops(&self, t: &mut Opcodes) -> Result<()> {
        t.add_ext_range(0xcf20, 0xcf22, 16, exec_store_const_ref)?;
        t.add_ext(0xcf80 >> 7, 9, 5, exec_store_const_slice)
    }

    #[instr(code = "c8", fmt = "NEWC")]
    fn exec_new_builder(st: &mut VmState) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut st.stack).push(CellBuilder::new()));
        Ok(0)
    }

    #[instr(code = "c9", fmt = "ENDC")]
    fn exec_builder_to_cell(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = stack.pop_builder()?;
        let cell = Rc::unwrap_or_clone(builder).build_ext(st.gas.context())?;
        ok!(stack.push(cell));
        Ok(0)
    }

    #[instr(code = "caxx", fmt = "STI {x}", args(x = (args & 0xff) + 1, signed = true))]
    #[instr(code = "cbxx", fmt = "STU {x}", args(x = (args & 0xff) + 1, signed = false))]
    fn exec_store_int(st: &mut VmState, x: u32, signed: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        exec_store_int_common(stack, x as u16, StoreIntArgs::from_sign(signed))
    }

    #[instr(code = "cc", fmt = "STREF", args(quiet = false))]
    #[instr(code = "cf10", fmt = "STREF", args(quiet = false))]
    #[instr(code = "cf18", fmt = "STREFQ", args(quiet = true))]
    fn exec_store_ref(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let cell = ok!(stack.pop_cell());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, cell, builder, quiet);
        }

        Rc::make_mut(&mut builder).store_reference(Rc::unwrap_or_clone(cell))?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cd", fmt = "ENDCST", args(quiet = false))]
    #[instr(code = "cf15", fmt = "STBREFR", args(quiet = false))]
    #[instr(code = "cf1d", fmt = "STBREFRQ", args(quiet = true))]
    fn exec_store_builder_as_ref_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let child_builder = ok!(stack.pop_builder());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, builder, child_builder, quiet);
        }

        let cell = Rc::unwrap_or_clone(child_builder).build_ext(st.gas.context())?;
        Rc::make_mut(&mut builder).store_reference(cell)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "ce", fmt = "STSLICE", args(quiet = false))]
    #[instr(code = "cf12", fmt = "STSLICE", args(quiet = false))]
    #[instr(code = "cf1a", fmt = "STSLICEQ", args(quiet = true))]
    fn exec_store_slice(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let cs = ok!(stack.pop_cs());

        if !cs.fits_into(&builder) {
            return finish_store_overflow(stack, cs, builder, quiet);
        }

        // TODO: Is it ok to store special cells data as is?
        let slice = cs.apply_allow_special();
        Rc::make_mut(&mut builder).store_slice(slice)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf0$0sss", fmt = ("{}", s.display_x()), args(s = StoreIntArgs(args)))]
    fn exec_store_int_var(st: &mut VmState, s: StoreIntArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 256 + s.is_signed() as u32));
        exec_store_int_common(stack, bits as u16, s)
    }

    #[instr(
        code = "cf0$1sss#n",
        fmt = ("{} {n}", s.display()),
        args(s = StoreIntArgs(args >> 8), n = (args & 0xff) + 1),
    )]
    fn exec_store_int_fixed(st: &mut VmState, s: StoreIntArgs, n: u32) -> VmResult<i32> {
        exec_store_int_common(Rc::make_mut(&mut st.stack), n as _, s)
    }

    #[instr(code = "cf11", fmt = "STBREF", args(quiet = false))]
    #[instr(code = "cf19", fmt = "STBREFQ", args(quiet = true))]
    fn exec_store_builder_as_ref(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let child_builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, child_builder, builder, quiet);
        }

        let cell = Rc::unwrap_or_clone(child_builder).build_ext(st.gas.context())?;
        Rc::make_mut(&mut builder).store_reference(cell)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf13", fmt = "STB", args(quiet = false))]
    #[instr(code = "cf1b", fmt = "STBQ", args(quiet = true))]
    fn exec_store_builder(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let other_builder = ok!(stack.pop_builder());

        if !builder.has_capacity(other_builder.size_bits(), other_builder.size_refs()) {
            return finish_store_overflow(stack, other_builder, builder, quiet);
        }

        Rc::make_mut(&mut builder).store_builder(&other_builder)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf14", fmt = "STREFR", args(quiet = false))]
    #[instr(code = "cf1c", fmt = "STREFRQ", args(quiet = true))]
    fn exec_store_ref_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, builder, cell, quiet);
        }

        Rc::make_mut(&mut builder).store_reference(Rc::unwrap_or_clone(cell))?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf16", fmt = "STSLICER", args(quiet = false))]
    #[instr(code = "cf1e", fmt = "STSLICERQ", args(quiet = true))]
    fn exec_store_slice_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let mut builder = ok!(stack.pop_builder());

        if !cs.fits_into(&builder) {
            return finish_store_overflow(stack, builder, cs, quiet);
        }

        // TODO: Is it ok to store special cells data as is?
        let slice = cs.apply_allow_special();
        Rc::make_mut(&mut builder).store_slice(slice)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf17", fmt = "STBR", args(quiet = false))]
    #[instr(code = "cf1f", fmt = "STBRQ", args(quiet = true))]
    fn exec_store_builder_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let other_builder = ok!(stack.pop_builder());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(other_builder.size_bits(), other_builder.size_refs()) {
            return finish_store_overflow(stack, builder, other_builder, quiet);
        }

        Rc::make_mut(&mut builder).store_builder(&other_builder)?;

        finish_store_ok(stack, builder, quiet)
    }

    fn exec_store_const_ref(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let refs = ((args & 1) + 1) as u8;
        let code_range = st.code.range_mut();
        vm_ensure!(code_range.has_remaining(bits, refs), InvalidOpcode);
        code_range.skip_first(bits, 0).ok();

        vm_log!("execute STREF{refs}CONST");

        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());

        vm_ensure!(
            builder.has_capacity(0, refs),
            CellError(Error::CellOverflow)
        );

        {
            let builder = Rc::make_mut(&mut builder);
            let mut code = st.code.apply()?;
            for _ in 0..refs {
                let cell = code.load_reference_cloned()?;
                builder.store_reference(cell)?;
            }
            st.code.set_range(code.range());
        }

        ok!(stack.push_raw(builder));
        Ok(0)
    }

    #[instr(code = "cf22$ss", fmt = "{s}", args(s = StoreLeIntArgs(args)))]
    fn exec_store_le_int(st: &mut VmState, s: StoreLeIntArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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
            let builder = Rc::make_mut(&mut builder);
            match x {
                Int::U32(x) => builder.store_u32(x.swap_bytes()),
                Int::U64(x) => builder.store_u64(x.swap_bytes()),
            }?;
        }

        ok!(stack.push_raw(builder));
        return Ok(0);
    }

    #[instr(code = "cf23", fmt = "ENDXC")]
    fn exec_builder_to_special_cell(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let special = ok!(stack.pop_bool());
        let mut builder = Rc::unwrap_or_clone(ok!(stack.pop_builder()));

        builder.set_exotic(special);

        // TODO: Test if `special` build fails with ordinary cell type in first 8 bits
        let cell = builder.build_ext(st.gas.context())?;

        ok!(stack.push(cell));
        Ok(0)
    }

    #[instr(code = "cf30", fmt = "BDEPTH")]
    fn exec_builder_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());

        let depth = compute_depth(builder.references());
        ok!(stack.push_int(depth));
        Ok(0)
    }

    #[instr(code = "cf31", fmt = "BBITS")]
    fn exec_builder_bits(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.size_bits()));
        Ok(0)
    }

    #[instr(code = "cf32", fmt = "BREFS")]
    fn exec_builder_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.size_refs()));
        Ok(0)
    }

    #[instr(code = "cf33", fmt = "BBITREFS")]
    fn exec_builder_bits_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.size_bits()));
        ok!(stack.push_int(builder.size_refs()));
        Ok(0)
    }

    #[instr(code = "cf35", fmt = "BREMBITS")]
    fn exec_builder_rem_bits(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_capacity_bits()));
        Ok(0)
    }

    #[instr(code = "cf36", fmt = "BREMREFS")]
    fn exec_builder_rem_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_capacity_refs()));
        Ok(0)
    }

    #[instr(code = "cf37", fmt = "BREMBITREFS")]
    fn exec_builder_rem_bits_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_capacity_bits()));
        ok!(stack.push_int(builder.spare_capacity_refs()));
        Ok(0)
    }

    #[instr(code = "cf38xx", fmt = "BCHKBITS {x}", args(x = (args & 0xff) + 1, quiet = false))]
    #[instr(code = "cf3cxx", fmt = "BCHKBITSQ {x}", args(x = (args & 0xff) + 1, quiet = true))]
    fn exec_builder_chk_bits(st: &mut VmState, x: u32, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());

        let fits = builder.has_capacity(x as u16, 0);
        if quiet {
            ok!(stack.push_bool(fits));
        } else if !fits {
            vm_bail!(CellError(Error::CellOverflow));
        }
        Ok(0)
    }

    #[instr(code = "cf39", fmt = "BCHKBITS", args(mode = CheckMode::Bits, quiet = false))]
    #[instr(code = "cf3a", fmt = "BCHKREFS", args(mode = CheckMode::Refs, quiet = false))]
    #[instr(code = "cf3b", fmt = "BCHKBITREFS", args(mode = CheckMode::BitRefs, quiet = false))]
    #[instr(code = "cf3d", fmt = "BCHKBITSQ", args(mode = CheckMode::Bits, quiet = true))]
    #[instr(code = "cf3e", fmt = "BCHKREFSQ", args(mode = CheckMode::Refs, quiet = true))]
    #[instr(code = "cf3f", fmt = "BCHKBITREFSQ", args(mode = CheckMode::BitRefs, quiet = true))]
    fn exec_builder_chk_bits_refs(st: &mut VmState, mode: CheckMode, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

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

    #[instr(code = "cf40", fmt = "STZEROES", args(value = Some(false)))]
    #[instr(code = "cf41", fmt = "STONES", args(value = Some(true)))]
    #[instr(code = "cf42", fmt = "STSAME", args(value = None))]
    fn exec_store_same(st: &mut VmState, value: Option<bool>) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

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
            let builder = Rc::make_mut(&mut builder);
            match value {
                true => builder.store_ones(bits as _)?,
                false => builder.store_zeros(bits as _)?,
            }
        }

        ok!(stack.push_raw(builder));
        Ok(0)
    }

    // cf$1xxxxx
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

        vm_log!(
            "execute STSLICECONST {}",
            OwnedCellSlice::from((st.code.cell().clone(), slice_range))
        );

        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        Rc::make_mut(&mut builder).store_slice(slice)?;
        ok!(stack.push_raw(builder));
        Ok(0)
    }

    // === Deserializer ops ===

    #[init]
    fn init_deserializer_ops(&self, t: &mut Opcodes) -> Result<()> {
        t.add_ext(0xd728 >> 3, 13, 8, exec_slice_begins_with_const)
    }

    #[instr(code = "d0", fmt = "CTOS")]
    fn exec_cell_to_slice(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());

        // TODO: Load with gas consumer
        let cs = OwnedCellSlice::new(Rc::unwrap_or_clone(cell));
        ok!(stack.push(cs));
        Ok(0)
    }

    #[instr(code = "d1", fmt = "ENDS")]
    fn exec_slice_chk_empty(st: &mut VmState) -> VmResult<i32> {
        let cs = ok!(Rc::make_mut(&mut st.stack).pop_cs());
        let range = cs.range();
        vm_ensure!(
            range.size_bits() == 0 && range.size_refs() == 0,
            CellError(Error::CellUnderflow)
        );
        Ok(0)
    }

    #[instr(code = "d2xx", fmt = "LDI {x}", args(x = (args & 0xff) + 1, signed = true))]
    #[instr(code = "d3xx", fmt = "LDU {x}", args(x = (args & 0xff) + 1, signed = false))]
    fn exec_load_int_fixed(st: &mut VmState, x: u32, signed: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        exec_load_int_common(stack, x as _, LoadIntArgs::from_sign(signed))
    }

    #[instr(code = "d4", fmt = "LDREF")]
    fn exec_load_ref(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());
        vm_ensure!(cs.range().size_refs() > 0, CellError(Error::CellUnderflow));

        let mut slice = cs.apply_allow_special();
        let cell = slice.load_reference_cloned()?;
        ok!(stack.push(cell));

        let range = slice.range();
        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d5", fmt = "LDREFRTOS")]
    fn exec_load_ref_rev_to_slice(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());
        vm_ensure!(cs.range().size_refs() > 0, CellError(Error::CellUnderflow));

        let mut slice = cs.apply_allow_special();
        let cell = slice.load_reference_cloned()?;
        // TODO: Load with gas consumer
        ok!(stack.push(OwnedCellSlice::new(cell)));

        let range = slice.range();
        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d6xx", fmt = "LDSLICE {x}", args(x = (args & 0xff) + 1))]
    fn exec_load_slice_fixed(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        exec_load_slice_common(stack, x as _, LoadSliceArgs(0))
    }

    #[instr(code = "d70$0sss", fmt = ("{}", s.display_x()), args(s = LoadIntArgs(args)))]
    fn exec_load_int_var(st: &mut VmState, s: LoadIntArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 256 + s.is_signed() as u32));
        exec_load_int_common(stack, bits as _, s)
    }

    #[instr(
        code = "d70$1sss#n",
        fmt = ("{} {n}", s.display()),
        args(s = LoadIntArgs(args >> 8), n = (args & 0xff) + 1)
    )]
    fn exec_load_int_fixed2(st: &mut VmState, s: LoadIntArgs, n: u32) -> VmResult<i32> {
        exec_load_int_common(Rc::make_mut(&mut st.stack), n as _, s)
    }

    #[instr(code = "d71$0xxx", fmt = "PLDUZ {x}", args(x = ((args & 7) + 1) << 5))]
    fn exec_preload_uint_fixed_0e(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());

        let (int, range) = {
            let mut slice = cs.apply_allow_special();

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

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));

        ok!(match int {
            Some(int) => stack.push_int(int),
            None => stack.push_nan(),
        });
        Ok(0)
    }

    #[instr(code = "d71$10ss", fmt = ("{}", s.display_x()), args(s = LoadSliceArgs(args)))]
    fn exec_load_slice(st: &mut VmState, s: LoadSliceArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 1023));
        exec_load_slice_common(stack, bits as _, s)
    }

    #[instr(
        code = "d71$11ss#n",
        fmt = ("{} {n}", s.display()),
        args(s = LoadSliceArgs(args >> 8), n = (args & 0xff) + 1)
    )]
    fn exec_load_slice_fixed2(st: &mut VmState, s: LoadSliceArgs, n: u32) -> VmResult<i32> {
        exec_load_slice_common(Rc::make_mut(&mut st.stack), n as _, s)
    }

    #[instr(code = "d720", fmt = "SDCUTFIRST", args(op = SliceRangeOp::CutFirst))]
    #[instr(code = "d721", fmt = "SDSKIPFIRST", args(op = SliceRangeOp::SkipFirst))]
    #[instr(code = "d722", fmt = "SDCUTLAST", args(op = SliceRangeOp::CutLast))]
    #[instr(code = "d723", fmt = "SDSKIPLAST", args(op = SliceRangeOp::SkipLast))]
    fn exec_slice_range_op(st: &mut VmState, op: SliceRangeOp) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d724", fmt = "SDSUBSTR")]
    fn exec_slice_substr(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d726", fmt = "SDBEGINSX", args(quiet = false))]
    #[instr(code = "d727", fmt = "SDBEGINSXQ", args(quiet = true))]
    fn exec_slice_begins_with(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let target = ok!(stack.pop_cs());
        let target = target.apply_allow_special();
        exec_slice_begins_with_common(stack, &target, quiet)
    }

    // d72$1xxxxxxxx
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

        vm_log!(
            "execute SDBEGINS{} {}",
            if quiet { "Q" } else { "" },
            OwnedCellSlice::from((st.code.cell().clone(), slice_range))
        );

        let stack = Rc::make_mut(&mut st.stack);
        exec_slice_begins_with_common(stack, &slice, quiet)
    }

    #[instr(code = "d730", fmt = "SCUTFIRST", args(op = SliceRangeOp::CutFirst))]
    #[instr(code = "d731", fmt = "SSKIPFIRST", args(op = SliceRangeOp::SkipFirst))]
    #[instr(code = "d732", fmt = "SCUTLAST", args(op = SliceRangeOp::CutLast))]
    #[instr(code = "d733", fmt = "SSKIPLAST", args(op = SliceRangeOp::SkipLast))]
    fn exec_slice_full_range_op(st: &mut VmState, op: SliceRangeOp) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d734", fmt = "SUBSLICE")]
    fn exec_subslice(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d736", fmt = "SPLIT", args(quiet = false))]
    #[instr(code = "d737", fmt = "SPLITQ", args(quiet = true))]
    fn exec_split(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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

        ok!(stack.push(OwnedCellSlice::from((cs.cell().clone(), prefix_range))));

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));

        if quiet {
            ok!(stack.push_bool(true));
        }
        Ok(0)
    }

    #[instr(code = "d739", fmt = "XCTOS")]
    fn exec_cell_to_slice_maybe_special(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let is_special = cell.descriptor().is_exotic();

        // TODO: Load with gas consumer
        let cs = OwnedCellSlice::new(Rc::unwrap_or_clone(cell));
        ok!(stack.push(cs));
        ok!(stack.push_bool(is_special));
        Ok(0)
    }

    #[instr(code = "d73a", fmt = "XLOAD", args(quiet = false))]
    #[instr(code = "d73b", fmt = "XLOADQ", args(quiet = true))]
    fn exec_load_special_cell(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let _cell = ok!(stack.pop_cell());
        let _ = quiet;

        todo!();
    }

    #[instr(code = "d741", fmt = "SCHKBITS", args(mode = CheckMode::Bits, quiet = false))]
    #[instr(code = "d742", fmt = "SCHKREFS", args(mode = CheckMode::Refs, quiet = false))]
    #[instr(code = "d743", fmt = "SCHKBITREFS", args(mode = CheckMode::BitRefs, quiet = false))]
    #[instr(code = "d745", fmt = "SCHKBITSQ", args(mode = CheckMode::Bits, quiet = true))]
    #[instr(code = "d746", fmt = "SCHKREFSQ", args(mode = CheckMode::Refs, quiet = true))]
    #[instr(code = "d747", fmt = "SCHKBITREFSQ", args(mode = CheckMode::BitRefs, quiet = true))]
    fn exec_check_slice(st: &mut VmState, mode: CheckMode, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

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

    #[instr(code = "d748", fmt = "PLDREFVAR")]
    fn exec_preload_ref(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 3)) as u8;
        let cs = ok!(stack.pop_cs());

        let slice = cs.apply_allow_special();
        let cell = slice.get_reference_cloned(idx)?;
        ok!(stack.push(cell));
        Ok(0)
    }

    #[instr(code = "d749", fmt = "SBITS", args(mode = CheckMode::Bits))]
    #[instr(code = "d74a", fmt = "SREFS", args(mode = CheckMode::Refs))]
    #[instr(code = "d74b", fmt = "SBITREFS", args(mode = CheckMode::BitRefs))]
    fn exec_slice_bits_refs(st: &mut VmState, mode: CheckMode) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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

    #[instr(code = "d74$11xx", fmt = "PLDREFIDX {x}")]
    fn exec_preload_ref_fixed(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());

        let slice = cs.apply_allow_special();
        let cell = slice.get_reference_cloned(x as _)?;
        ok!(stack.push(cell));
        Ok(0)
    }

    #[instr(code = "d75s", fmt = "{s}", args(s = LoadLeIntArgs(args)))]
    fn exec_load_le_int(st: &mut VmState, s: LoadLeIntArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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
            let mut slice = cs.apply_allow_special();

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
            Rc::make_mut(&mut cs).set_range(range);
            ok!(stack.push_raw(cs));
        }

        if s.is_quiet() {
            ok!(stack.push_bool(true));
        }
        Ok(0)
    }

    #[instr(code = "d760", fmt = "LDZEROES", args(value = Some(false)))]
    #[instr(code = "d761", fmt = "LDONES", args(value = Some(true)))]
    #[instr(code = "d762", fmt = "LDSAME", args(value = None))]
    fn exec_load_same(st: &mut VmState, value: Option<bool>) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
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
            let target = unsafe { target.as_slice_unchecked() };

            let mut slice = cs.apply_allow_special();
            let prefix = slice.longest_common_data_prefix(&target);
            let ok = slice.skip_first(prefix.size_bits(), 0).is_ok();
            debug_assert!(ok);

            ok!(stack.push_int(prefix.size_bits()));

            slice.range()
        };

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d764", fmt = "SDEPTH")]
    fn exec_slice_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let slice = cs.apply_allow_special();

        let depth = compute_depth(slice.references());
        ok!(stack.push_int(depth));
        Ok(0)
    }

    #[instr(code = "d765", fmt = "CDEPTH")]
    fn exec_cell_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

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
            None => stack.push_int(0),
        });
        Ok(0)
    }

    #[instr(code = "d766", fmt = "CLEVEL")]
    fn exec_cell_level(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let level = cell.descriptor().level_mask().level();
        ok!(stack.push_int(level));
        Ok(0)
    }

    #[instr(code = "d767", fmt = "CLEVELMASK")]
    fn exec_cell_level_mask(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let mask = cell.descriptor().level_mask().to_byte();
        ok!(stack.push_int(mask));
        Ok(0)
    }

    #[instr(code = "d76$10xx", fmt = "CHASHI {x}", args(op = LevelOp::Hash))]
    #[instr(code = "d76$11xx", fmt = "CDEPTHI {x}", args(op = LevelOp::Depth))]
    fn exec_cell_level_op(st: &mut VmState, x: u32, op: LevelOp) -> VmResult<i32> {
        exec_cell_level_op_common(Rc::make_mut(&mut st.stack), x as _, op)
    }

    #[instr(code = "d770", fmt = "CHASHIX", args(op = LevelOp::Hash))]
    #[instr(code = "d771", fmt = "CDEPTHIX", args(op = LevelOp::Depth))]
    fn exec_cell_level_op_var(st: &mut VmState, op: LevelOp) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_smallint_range(0, 3));
        exec_cell_level_op_common(stack, x as _, op)
    }
}

enum PushRefMode {
    Cell,
    Slice,
    Cont,
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
        vm_bail!(CellError(everscale_types::error::Error::CellUnderflow));
    };
    let ok = st.code.range_mut().skip_first(0, 1).is_ok();
    debug_assert!(ok);

    vm_log!("execute {name} ({})", cell.repr_hash());

    let stack = Rc::make_mut(&mut st.stack);
    ok!(match mode {
        PushRefMode::Cell => stack.push(cell),
        // TODO: Load with gas consumer
        PushRefMode::Slice => stack.push(OwnedCellSlice::new(cell)),
        PushRefMode::Cont => {
            let code = st.gas.context().load_cell(cell, LoadMode::Full)?;
            let cont = Rc::new(OrdCont::simple(code.into(), st.cp.id()));
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

    let slice: RcStackValue = Rc::new(OwnedCellSlice::from((st.code.cell().clone(), slice_range)));
    vm_log!("execute PUSHSLICE {}", slice.display_list());

    ok!(Rc::make_mut(&mut st.stack).push_raw(slice));
    Ok(0)
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
        builder: Rc<CellBuilder>,
        x: Rc<BigInt>,
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
    if args.is_reversed() {
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

    let int_bits = bitsize(&x, args.is_signed());
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
        let builder = Rc::make_mut(&mut builder);
        match x.to_u64() {
            Some(value) => builder.store_uint(value, bits)?,
            None => {
                let int = if bits % 8 != 0 {
                    let align = 8 - bits % 8;
                    Cow::Owned((*x).clone() << align)
                } else {
                    Cow::Borrowed(x.as_ref())
                };

                let minimal_bytes = ((bits + 7) / 8) as usize;

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

pub(crate) fn finish_store_overflow(
    stack: &mut Stack,
    arg1: RcStackValue,
    arg2: RcStackValue,
    quiet: bool,
) -> VmResult<i32> {
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
    builder: Rc<CellBuilder>,
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
        let mut slice = cs.apply_allow_special();
        let int = load_int_from_slice(&mut slice, bits, args.is_signed())?;

        ok!(stack.push_int(int));

        slice.range()
    };

    if !args.is_prefetch() {
        Rc::make_mut(&mut cs).set_range(range);
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
        let slice = OwnedCellSlice::from((cs.cell().clone(), range.get_prefix(bits, 0)));
        ok!(stack.push(slice));

        let ok = range.skip_first(bits, 0).is_ok();
        debug_assert!(ok);

        range
    };

    if !args.is_prefetch() {
        Rc::make_mut(&mut cs).set_range(range);
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
        let slice = cs.apply_allow_special();
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

    Rc::make_mut(&mut cs).set_range(range);
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
    use super::*;
    use crate::cont::RcCont;
    use everscale_types::boc::Boc;
    use everscale_vm::cont::{ControlData, ControlRegs};
    use tracing_test::traced_test;

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
    fn basic_contops() {
        let cont: RcStackValue = Rc::new(crate::cont::PushIntCont {
            value: 1,
            next: Rc::new(crate::cont::PushIntCont {
                value: 2,
                next: Rc::new(crate::cont::QuitCont { exit_code: 0 }),
            }),
        });

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1, int 2],
        );

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1, int 2],
        );

        assert_run_vm!(
            "JMPX",
            [raw cont.clone()] => [int 1, int 2],
        );
    }

    #[test]
    #[traced_test]
    fn conditional_contops() {
        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            IFRET
            PUSHINT 0
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1]
        );

        //--------

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 0
            IFRET
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

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

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 0
            IFNOTRET
            PUSHINT 1
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 2]
        );

        //--------

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 1
            IFNOTRET
            PUSHINT 1
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 2, int 1]
        );

        //-------------

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

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

        let code1 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont1: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code1.into(),
            crate::instr::codepage0().id(),
        ));

        let code2 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 3
            PUSHINT 4
            "#
        })
        .unwrap();

        let cont2: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code2.into(),
            crate::instr::codepage0().id(),
        ));

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
    }

    #[test]
    #[traced_test]
    fn conditional_refcontops() {
        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

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
    }

    #[test]
    #[traced_test]
    fn conditional_altcontops() {
        //----

        let code_c1 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            "#
        })
        .unwrap();
        let cont_c1 = crate::cont::OrdCont::simple(code_c1.into(), crate::instr::codepage0().id());

        let mut cr = ControlRegs::default();
        cr.set_c(1, Rc::new(cont_c1));

        let code_c0 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont_c0: RcStackValue = Rc::new(crate::cont::OrdCont {
            data: ControlData {
                nargs: None,
                stack: None,
                save: cr,
                cp: Some(crate::instr::codepage0().id()),
            },
            code: code_c0.into(),
        });

        assert_run_vm!(
            "IFRETALT",
            [int 1, raw cont_c0.clone()] => [int 1]
        );
    }

    #[test]
    #[traced_test]
    fn loops() {
        // REPEAT
        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            "#
        })
        .unwrap();
        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        let code1 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 1
            "#
        })
        .unwrap();
        let cont1: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code1.into(),
            crate::instr::codepage0().id(),
        ));

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

        //UNTIL
        assert_run_vm!(
            "UNTIL",
            [raw cont1.clone()] => [int 2]
        );

        //UNTILEND
        // TODO: case for other branch
        assert_run_vm!(
            "UNTILEND PUSHINT 0 PUSHINT 1",
            [int 3] => [int 3, int 0]
        );

        // WHILE
        let code0 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            "#
        })
        .unwrap();
        let c0: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code0.into(),
            crate::instr::codepage0().id(),
        ));

        let code1 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 0
            "#
        })
        .unwrap();
        let c1: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code1.into(),
            crate::instr::codepage0().id(),
        ));

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

        let code_c0 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            RETALT
            "#
        })
        .unwrap();

        let cont_c0: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code_c0.into(),
            crate::instr::codepage0().id(),
        ));

        //TODO: probably this behaviour with exit code 1 is okay. Add more cases with more loops

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

        //REPEATBRK

        let code_c0 = Boc::decode(&everscale_asm_macros::tvmasm! {
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
        })
        .unwrap();

        let cont_c0: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code_c0.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "REPEATBRK",
            [int 5, int 10, raw cont_c0.clone()] => [int 0, int 0, int 0, int 0, int 0]
        );

        //REPEATENDBRK

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

        let code_c0 = Boc::decode(&everscale_asm_macros::tvmasm! {
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
        })
        .unwrap();

        let cont_c0: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code_c0.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "UNTILBRK",
            [int 0, int -5, raw cont_c0.clone()] => [int -4]
        );
    }
}