use everscale_types::cell::{CellBuilder, CellSlice, CellSliceParts, Load, Size};
use everscale_types::dict::{self, DictBound, SetMode};
use everscale_types::error::Error;
use everscale_types::prelude::{Cell, CellFamily, Store};
use num_bigint::Sign;
use tycho_vm_proc::vm_module;

use crate::cont::OrdCont;
use crate::dispatch::Opcodes;
use crate::error::VmResult;
use crate::saferc::SafeRc;
use crate::stack::RcStackValue;
use crate::state::VmState;
use crate::util::{
    bitsize, in_bitsize_range, load_int_from_slice, store_int_to_builder,
    store_int_to_builder_unchecked, OwnedCellSlice,
};

pub struct DictOps;

#[vm_module]
impl DictOps {
    #[init]
    fn init_dict_const(&self, t: &mut Opcodes) -> anyhow::Result<()> {
        t.add_ext_range(0xf4a400, 0xf4a800, 24, exec_push_const_dict)?;
        Ok(())
    }

    #[op(code = "f400", fmt = "STDICT")]
    fn exec_stdict(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let mut builder = ok!(stack.pop_builder());
        let cell = ok!(stack.pop_cell_opt());

        cell.as_deref()
            .store_into(SafeRc::make_mut(&mut builder), Cell::empty_context())?;
        ok!(stack.push_raw(builder));
        Ok(0)
    }

    #[op(code = "f401", fmt = "SKIPDICT")]
    fn exec_skip_dict(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut csr = ok!(stack.pop_cs());
        {
            let mut cs = csr.apply();
            if cs.load_bit()? {
                cs.skip_first(0, 1)?;
            }
            let range = cs.range();
            SafeRc::make_mut(&mut csr).set_range(range);
        }
        ok!(stack.push_raw(csr));
        Ok(0)
    }

    #[op(code = "f402", fmt = "LDDICTS", args(preload = false))]
    #[op(code = "f403", fmt = "PLDDICTS", args(preload = true))]
    fn exec_load_dict_slice(st: &mut VmState, preload: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut csr = ok!(stack.pop_cs());

        let mut cs = csr.apply();
        let dict_cs = cs.load_prefix(1, cs.get_bit(0)? as u8)?;

        ok!(stack.push(OwnedCellSlice::from((dict_cs.range(), csr.cell().clone()))));
        if !preload {
            let range = cs.range();
            SafeRc::make_mut(&mut csr).set_range(range);
            ok!(stack.push_raw(csr));
        }
        Ok(0)
    }

    #[op(code = "f404", fmt = "LDDICT", args(preload = false, quiet = false))]
    #[op(code = "f405", fmt = "PLDDICT", args(preload = true, quiet = false))]
    #[op(code = "f406", fmt = "LDDICTQ", args(preload = false, quiet = true))]
    #[op(code = "f407", fmt = "PLDDICTQ", args(preload = true, quiet = true))]
    fn exec_load_dict(st: &mut VmState, preload: bool, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut csr = ok!(stack.pop_cs());

        let mut cs = csr.apply();
        let dict = match cs.get_bit(0) {
            Ok(has_root) if cs.has_remaining(1, has_root as _) => {
                Option::<Cell>::load_from(&mut cs)?
            }
            _ if quiet => {
                if !preload {
                    ok!(stack.push_raw(csr));
                }
                ok!(stack.push_bool(false));
                return Ok(0);
            }
            _ => vm_bail!(CellError(Error::CellUnderflow)),
        };

        ok!(stack.push_opt(dict));
        if !preload {
            let range = cs.range();
            SafeRc::make_mut(&mut csr).set_range(range);
            ok!(stack.push_raw(csr));
        }
        if quiet {
            ok!(stack.push_bool(true));
        }
        Ok(0)
    }

    #[op(code = "f4ss @ f40a..f410", fmt = s.display("GET"), args(s = DictOpArgs(args)))]
    fn exec_dict_get(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let cs;
        let mut cb;
        let key = if s.is_int() {
            let int = ok!(stack.pop_int());

            let signed = s.is_signed();
            if !in_bitsize_range(&int, signed) || bitsize(&int, signed) > n {
                ok!(stack.push_bool(false));
                return Ok(0);
            }

            cb = CellBuilder::new();
            store_int_to_builder_unchecked(&int, n, signed, &mut cb)?;
            cb.as_data_slice()
        } else {
            cs = stack.pop_cs()?;
            cs.apply().load_prefix(n, 0)?
        };

        let value = if s.is_ref() {
            let value = dict::dict_get(dict.as_deref(), n, key, &st.gas)?;
            ok!(value.map(to_value_ref).transpose())
        } else {
            dict::dict_get_owned(dict.as_deref(), n, key, &st.gas)?
                .map(|parts| SafeRc::new_dyn_value(OwnedCellSlice::from(parts)))
        };

        match value {
            None => ok!(stack.push_bool(false)),
            Some(value) => {
                ok!(stack.push_raw(value));
                ok!(stack.push_bool(true));
            }
        }
        Ok(0)
    }

    #[op(
        code = "f4ss @ f412..f418",
        fmt = s.display("SET"),
        args(s = DictOpArgs(args), b = false, mode = SetMode::Set)
    )]
    #[op(
        code = "f4ss @ f422..f428",
        fmt = s.display("REPLACE"),
        args(s = DictOpArgs(args), b = false, mode = SetMode::Replace)
    )]
    #[op(
        code = "f4ss @ f432..f438",
        fmt = s.display("ADD"),
        args(s = DictOpArgs(args), b = false, mode = SetMode::Add)
    )]
    #[op(
        code = "f4ss @ f441..f444",
        fmt = s.display_b("SET"),
        args(s = DictOpArgs(args << 1), b = true, mode = SetMode::Set)
    )]
    #[op(
        code = "f4ss @ f449..f44c",
        fmt = s.display_b("REPLACE"),
        args(s = DictOpArgs(args << 1), b = true, mode = SetMode::Replace)
    )]
    #[op(
        code = "f4ss @ f451..f454",
        fmt = s.display_b("ADD"),
        args(s = DictOpArgs(args << 1), b = true, mode = SetMode::Add)
    )]
    fn exec_dict_set(st: &mut VmState, s: DictOpArgs, b: bool, mode: SetMode) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let cs;
        let mut cb;
        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            cb = CellBuilder::new();
            store_int_to_builder(&int, n, s.is_signed(), &mut cb)?;
            cb.as_data_slice()
        } else {
            cs = stack.pop_cs()?;
            cs.apply().load_prefix(n, 0)?
        };

        let value = ok!(stack.pop());
        let value_cs;
        let value: &dyn Store = if b {
            value_cs = ok!(value.try_as_cell_builder()).as_full_slice();
            &value_cs as &dyn Store
        } else if s.is_ref() {
            ok!(value.try_as_cell()) as &dyn Store
        } else {
            value_cs = ok!(value.try_as_cell_slice()).apply();
            &value_cs as &dyn Store
        };

        let mut dict = dict.as_deref().cloned();
        let result = dict::dict_insert(&mut dict, &mut key, n, value, mode, &st.gas);

        ok!(stack.push_opt(dict));

        if mode == SetMode::Set {
            result?;
        } else {
            ok!(stack.push_bool(result.is_ok()));
        }
        Ok(0)
    }

    #[op(
        code = "f4ss @ f41a..f420",
        fmt = s.display("SETGET"),
        args(s = DictOpArgs(args), b = false, mode = SetMode::Set)
    )]
    #[op(
        code = "f4ss @ f42a..f430",
        fmt = s.display("REPLACEGET"),
        args(s = DictOpArgs(args), b = false, mode = SetMode::Replace)
    )]
    #[op(
        code = "f4ss @ f43a..f440",
        fmt = s.display("ADDGET"),
        args(s = DictOpArgs(args), b = false, mode = SetMode::Add)
    )]
    #[op(
        code = "f4ss @ f445..f448",
        fmt = s.display_b("SETGET"),
        args(s = DictOpArgs(args << 1), b = true, mode = SetMode::Set)
    )]
    #[op(
        code = "f4ss @ f44d..f450",
        fmt = s.display_b("REPLACEGET"),
        args(s = DictOpArgs(args << 1), b = true, mode = SetMode::Replace)
    )]
    #[op(
        code = "f4ss @ f455..f458",
        fmt = s.display_b("ADDGET"),
        args(s = DictOpArgs(args << 1), b = true, mode = SetMode::Add)
    )]
    fn exec_dict_setget(st: &mut VmState, s: DictOpArgs, b: bool, mode: SetMode) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let cs;
        let mut cb;
        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            cb = CellBuilder::new();
            store_int_to_builder(&int, n, s.is_signed(), &mut cb)?;
            cb.as_data_slice()
        } else {
            cs = stack.pop_cs()?;
            cs.apply().load_prefix(n, 0)?
        };

        let ok_f = !matches!(mode, SetMode::Add);

        let value = ok!(stack.pop());
        let value_cs;
        let value: &dyn Store = if b {
            value_cs = ok!(value.try_as_cell_builder()).as_full_slice();
            &value_cs as &dyn Store
        } else if s.is_ref() {
            ok!(value.try_as_cell()) as &dyn Store
        } else {
            value_cs = ok!(value.try_as_cell_slice()).apply();
            &value_cs as &dyn Store
        };

        let mut dict = dict.as_deref().cloned();
        let (_, prev) = dict::dict_insert_owned(&mut dict, &mut key, n, value, mode, &st.gas)?;
        let prev = ok!(prev.map(|p| extract_value_ref(p, s.is_ref())).transpose());

        ok!(stack.push_opt(dict));
        match prev {
            Some(prev) => {
                ok!(stack.push_raw(prev));
                ok!(stack.push_bool(ok_f));
            }
            None => {
                ok!(stack.push_bool(!ok_f));
            }
        }
        Ok(0)
    }

    #[op(code = "f4ss @ f459..f45c", fmt = s.display("DEL"), args(s = ShortDictOpArgs(args)))]
    fn exec_dict_delete(st: &mut VmState, s: ShortDictOpArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let cs;
        let mut cb;
        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());

            let signed = s.is_signed();
            if !in_bitsize_range(&int, signed) || bitsize(&int, signed) > n {
                ok!(stack.push_opt_raw(dict));
                ok!(stack.push_bool(false));
                return Ok(0);
            }

            cb = CellBuilder::new();
            store_int_to_builder_unchecked(&int, n, signed, &mut cb)?;
            cb.as_data_slice()
        } else {
            cs = stack.pop_cs()?;
            cs.apply().load_prefix(n, 0)?
        };

        let mut dict = dict.as_deref().cloned();
        let result = dict::dict_remove_owned(&mut dict, &mut key, n, true, &st.gas)?;
        ok!(stack.push_opt(dict));
        ok!(stack.push_bool(result.is_some()));
        Ok(0)
    }

    #[op(code = "f4ss @ f462..f468", fmt = s.display("DELGET"), args(s = DictOpArgs(args)))]
    fn exec_dict_deleteget(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let cs;
        let mut cb;
        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());

            let signed = s.is_signed();
            if !in_bitsize_range(&int, signed) || bitsize(&int, signed) > n {
                ok!(stack.push_opt_raw(dict));
                ok!(stack.push_bool(false));
                return Ok(0);
            }

            cb = CellBuilder::new();
            store_int_to_builder_unchecked(&int, n, signed, &mut cb)?;
            cb.as_data_slice()
        } else {
            cs = stack.pop_cs()?;
            cs.apply().load_prefix(n, 0)?
        };

        let mut dict = dict.as_deref().cloned();
        let prev = dict::dict_remove_owned(&mut dict, &mut key, n, false, &st.gas)?;
        let prev = ok!(prev.map(|p| extract_value_ref(p, s.is_ref())).transpose());

        ok!(stack.push_opt(dict));
        match prev {
            Some(prev) => {
                ok!(stack.push_raw(prev));
                ok!(stack.push_bool(true));
            }
            None => {
                ok!(stack.push_bool(false));
            }
        }
        Ok(0)
    }

    #[op(code = "f4ss @ f469..f46c", fmt = s.display("GETOPTREF"), args(s = ShortDictOpArgs(args)))]
    fn exec_dict_get_optref(st: &mut VmState, s: ShortDictOpArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let cs;
        let mut cb;
        let key = if s.is_int() {
            let int = ok!(stack.pop_int());

            let signed = s.is_signed();
            if !in_bitsize_range(&int, signed) || bitsize(&int, signed) > n {
                ok!(stack.push_null());
                return Ok(0);
            }

            cb = CellBuilder::new();
            store_int_to_builder_unchecked(&int, n, signed, &mut cb)?;
            cb.as_data_slice()
        } else {
            cs = stack.pop_cs()?;
            cs.apply().load_prefix(n, 0)?
        };

        let value = dict::dict_get(dict.as_deref(), n, key, &st.gas)?;
        let value = ok!(value.map(to_value_ref).transpose());
        ok!(stack.push_opt_raw(value));
        Ok(0)
    }

    #[op(code = "f4ss @ f46d..f470", fmt = s.display("SETGETOPTREF"), args(s = ShortDictOpArgs(args)))]
    fn exec_dict_setget_optref(st: &mut VmState, s: ShortDictOpArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let cs;
        let mut cb;
        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            cb = CellBuilder::new();
            store_int_to_builder(&int, n, s.is_signed(), &mut cb)?;
            cb.as_data_slice()
        } else {
            cs = stack.pop_cs()?;
            cs.apply().load_prefix(n, 0)?
        };

        let value = ok!(stack.pop_cell_opt());

        let ctx = &st.gas;
        let mut dict = dict.as_deref().cloned();
        let prev = match value {
            Some(cell) => {
                dict::dict_insert_owned(&mut dict, &mut key, n, &*cell, SetMode::Set, ctx)
                    .map(|(_, prev)| prev)?
            }
            None => dict::dict_remove_owned(&mut dict, &mut key, n, false, ctx)?,
        };
        let prev = ok!(prev.map(|p| extract_value_ref(p, true)).transpose());

        ok!(stack.push_opt(dict));
        ok!(stack.push_opt_raw(prev));
        Ok(0)
    }

    #[op(code = "f4ss @ f474..f480", fmt = s, args(s = DictGetNearArgs(args)))]
    fn exec_dict_get_near(st: &mut VmState, s: DictGetNearArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let max_key_bits = if s.is_int() {
            256 + s.is_signed() as u32
        } else {
            1023
        };
        let n = ok!(stack.pop_smallint_range(0, max_key_bits)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let dir = if s.is_prev() {
            DictBound::Min
        } else {
            DictBound::Max
        };

        let ctx = &st.gas;
        if s.is_int() {
            let int = ok!(stack.pop_int());

            let signed = s.is_signed();
            let nearest = if in_bitsize_range(&int, signed) && bitsize(&int, signed) <= n {
                let mut cb = CellBuilder::new();
                store_int_to_builder_unchecked(&int, n, signed, &mut cb)?;
                let key = cb.as_data_slice();
                dict::dict_find_owned(dict.as_deref(), n, key, dir, s.is_eq(), signed, ctx)?
            } else if (int.sign() == Sign::Minus) != s.is_prev() {
                // Find closest value for keys out of range using the opposite direction.
                let dir = match dir {
                    DictBound::Min => DictBound::Max,
                    DictBound::Max => DictBound::Min,
                };
                dict::dict_find_bound_owned(dict.as_deref(), n, dir, signed, ctx)?
            } else {
                None
            };

            let Some((key, value)) = nearest else {
                ok!(stack.push_bool(false));
                return Ok(0);
            };

            ok!(stack.push(OwnedCellSlice::from(value)));
            ok!(stack.push(load_int_from_slice(&mut key.as_data_slice(), n, signed)?));
        } else {
            let cs = ok!(stack.pop_cs());
            let key = cs.apply().load_prefix(n, 0)?;

            let Some((key, value)) =
                dict::dict_find_owned(dict.as_deref(), n, key, dir, s.is_eq(), false, ctx)?
            else {
                ok!(stack.push_bool(false));
                return Ok(0);
            };

            ok!(stack.push(OwnedCellSlice::from(value)));
            ok!(stack.push(OwnedCellSlice::new_allow_exotic(key.build_ext(ctx)?)));
        }

        ok!(stack.push_bool(true));
        Ok(0)
    }

    #[op(code = "f4ss @ f482..f488", fmt = s.display("MIN"), args(s = DictOpArgs(args)))]
    #[op(code = "f4ss @ f48a..f490", fmt = s.display("MAX"), args(s = DictOpArgs(args)))]
    #[op(code = "f4ss @ f492..f498", fmt = s.display("REMMIN"), args(s = DictOpArgs(args)))]
    #[op(code = "f4ss @ f49a..f4a0", fmt = s.display("REMMAX"), args(s = DictOpArgs(args)))]
    fn exec_dict_get_min(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let max_key_bits = if s.is_int() {
            256 + s.is_signed() as u32
        } else {
            1023
        };
        let n = ok!(stack.pop_smallint_range(0, max_key_bits)) as u16;
        let dict = ok!(stack.pop_cell_opt());

        let bound = if s.is_max() {
            DictBound::Max
        } else {
            DictBound::Min
        };

        let signed = s.is_signed();
        let ctx = &st.gas;
        let key = if s.is_rem() {
            let mut dict = dict.as_deref().cloned();
            let prev = dict::dict_remove_bound_owned(&mut dict, n, bound, signed, ctx)?;
            let prev = ok!(prev
                .map(|(key, value)| {
                    let value = ok!(extract_value_ref(value, s.is_ref()));
                    Ok((key, value))
                })
                .transpose());
            ok!(stack.push_opt(dict));

            let Some((key, value)) = prev else {
                ok!(stack.push_bool(false));
                return Ok(0);
            };
            ok!(stack.push_raw(value));
            key
        } else {
            let Some((key, value)) =
                dict::dict_find_bound_owned(dict.as_deref(), n, bound, signed, ctx)?
            else {
                ok!(stack.push_bool(false));
                return Ok(0);
            };

            let value = ok!(extract_value_ref(value, s.is_ref()));
            ok!(stack.push_raw(value));
            key
        };

        if s.is_int() {
            ok!(stack.push(load_int_from_slice(&mut key.as_data_slice(), n, signed)?));
        } else {
            ok!(stack.push(OwnedCellSlice::new_allow_exotic(key.build_ext(ctx)?)));
        }
        ok!(stack.push_bool(true));
        Ok(0)
    }

    #[op(code = "f4a$00ss", fmt = s, args(s = DictExecArgs(args)))]
    #[op(code = "f4b$11ss", fmt = s, args(s = DictExecArgs(args)))]
    fn exec_dict_get_exec(st: &mut VmState, s: DictExecArgs) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict = ok!(stack.pop_cell_opt());
        let idx = ok!(stack.pop_int());

        'scope: {
            let signed = s.is_signed();
            if !in_bitsize_range(&idx, signed) || bitsize(&idx, signed) > n {
                break 'scope;
            }

            let mut cb = CellBuilder::new();
            store_int_to_builder_unchecked(&idx, n, signed, &mut cb)?;
            let key = cb.as_data_slice();

            let Some(value) = dict::dict_get_owned(dict.as_deref(), n, key, &st.gas)? else {
                break 'scope;
            };

            let cont = SafeRc::from(OrdCont::simple(value.into(), st.cp.id()));
            return if s.is_exec() {
                st.call(cont)
            } else {
                st.jump(cont)
            };
        }

        if s.is_z() {
            ok!(stack.push_raw(idx));
        }
        Ok(0)
    }

    // f4a400..f4a800
    fn exec_push_const_dict(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        vm_ensure!(st.code.range().has_remaining(bits, 1), InvalidOpcode);
        let ok = st.code.range_mut().skip_first(bits - 11, 0).is_ok();
        debug_assert!(ok);

        let stack = SafeRc::make_mut(&mut st.stack);
        let mut code = st.code.apply();

        let slice = code.load_prefix(1, 1)?;
        let slice_range = slice.range();
        let dict = slice.get_reference_cloned(0)?;

        let n = code.load_uint(10)? as u16;
        st.code.set_range(code.range());

        vm_log_op!(
            "DICTPUSHCONST {n} ({})",
            OwnedCellSlice::from((slice_range, st.code.cell().clone()))
        );
        ok!(stack.push(dict));
        ok!(stack.push_int(n));
        Ok(0)
    }

    // TODO: Implement a proper subdictionary cut.
    // #[op(code = "f4ss @ f4b1..f4b4", fmt = s.display("GET"), args(s = SubDictOpArgs(args)))]
    // #[op(code = "f4ss @ f4b5..f4b8", fmt = s.display("RPGET"), args(s = SubDictOpArgs(args)))]
    // fn exec_subdict_get(st: &mut VmState, s: SubDictOpArgs) -> VmResult<i32> {
    //     let stack = Rc::make_mut(&mut st.stack);
    //     let n = ok!(stack.pop_smallint_range(0, 1023));
    //     let dict = ok!(stack.pop_cell_opt());

    //     let mk = if s.is_int() {
    //         256 + s.is_signed() as u32
    //     } else {
    //         1023
    //     };
    //     let k = ok!(stack.pop_smallint_range(0, std::cmp::min(mk, n))) as u16;

    //     let cs;
    //     let mut cb;
    //     let mut key = if s.is_int() {
    //         let int = ok!(stack.pop_int());
    //         cb = CellBuilder::new();
    //         store_int_to_builder(&int, n, s.is_signed(), &mut cb)?;
    //         cb.as_data_slice()
    //     } else {
    //         cs = stack.pop_cs()?;
    //         cs.apply()?.load_prefix(n, 0)?
    //     };

    //     let subdict =
    //         dict::dict_get_subdict(dict_deref.as_ref(), 32, &mut prefix, &st.gas)?;

    //     ok!(stack.push_opt(subdict));

    //     Ok(0)
    // }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
struct DictOpArgs(u32);

impl DictOpArgs {
    pub fn is_unsigned(&self) -> bool {
        self.0 & 0b010 != 0
    }

    pub fn is_signed(&self) -> bool {
        !self.is_unsigned()
    }

    pub fn is_int(&self) -> bool {
        self.0 & 0b100 != 0
    }

    pub fn is_ref(&self) -> bool {
        self.0 & 0b001 != 0
    }

    pub fn is_max(&self) -> bool {
        self.0 & 0b1000 != 0
    }

    pub fn is_rem(&self) -> bool {
        self.0 & 0b10000 != 0
    }

    pub fn display(self, name: &'static str) -> DisplayDictOpArgs<false> {
        DisplayDictOpArgs { name, args: self }
    }

    pub fn display_b(self, name: &'static str) -> DisplayDictOpArgs<true> {
        DisplayDictOpArgs { name, args: self }
    }
}

struct DisplayDictOpArgs<const B: bool> {
    name: &'static str,
    args: DictOpArgs,
}

impl<const B: bool> std::fmt::Display for DisplayDictOpArgs<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let int = if self.args.is_int() {
            if self.args.is_unsigned() {
                "U"
            } else {
                "I"
            }
        } else {
            ""
        };
        let suffix = if B {
            "B"
        } else if self.args.is_ref() {
            "REF"
        } else {
            ""
        };

        write!(f, "DICT{int}{}{suffix}", self.name)
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
struct ShortDictOpArgs(u32);

impl ShortDictOpArgs {
    fn is_unsigned(&self) -> bool {
        self.0 & 0b01 != 0
    }

    fn is_signed(&self) -> bool {
        !self.is_unsigned()
    }

    fn is_int(&self) -> bool {
        self.0 & 0b10 != 0
    }

    fn display(self, name: &'static str) -> DisplayShortDictOpArgs {
        DisplayShortDictOpArgs { name, args: self }
    }
}

struct DisplayShortDictOpArgs {
    name: &'static str,
    args: ShortDictOpArgs,
}

impl std::fmt::Display for DisplayShortDictOpArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let int = if self.args.is_int() {
            if self.args.is_unsigned() {
                "U"
            } else {
                "I"
            }
        } else {
            ""
        };
        write!(f, "DICT{int}{}", self.name)
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
struct DictGetNearArgs(u32);

impl DictGetNearArgs {
    fn is_prev(&self) -> bool {
        self.0 & 0b0010 != 0
    }

    fn is_signed(&self) -> bool {
        !self.is_unsigned()
    }

    fn is_unsigned(&self) -> bool {
        self.0 & 0b0100 != 0
    }

    fn is_int(&self) -> bool {
        self.0 & 0b1000 != 0
    }

    fn is_eq(&self) -> bool {
        self.0 & 0b0001 != 0
    }
}

impl std::fmt::Display for DictGetNearArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let int = if self.is_int() {
            if self.is_unsigned() {
                "U"
            } else {
                "I"
            }
        } else {
            ""
        };
        let dir = if self.is_prev() { "PREV" } else { "NEXT" };
        let eq = if self.is_eq() { "EQ" } else { "" };
        write!(f, "DICT{int}GET{dir}{eq}")
    }
}

struct DictExecArgs(u32);

impl DictExecArgs {
    fn is_unsigned(&self) -> bool {
        self.0 & 0b01 != 0
    }

    fn is_signed(&self) -> bool {
        !self.is_unsigned()
    }

    fn is_exec(&self) -> bool {
        self.0 & 0b10 != 0
    }

    fn is_z(&self) -> bool {
        self.0 & 0b100 != 0
    }
}

impl std::fmt::Display for DictExecArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let int = if self.is_unsigned() { "U" } else { "I" };
        let exec = if self.is_exec() { "EXEC" } else { "JMP" };
        let z = if self.is_z() { "Z" } else { "" };
        write!(f, "DICT{int}GET{exec}{z}")
    }
}

// #[derive(Clone, Copy)]
// #[repr(transparent)]
// struct SubDictOpArgs(u32);

// impl SubDictOpArgs {
//     fn is_unsigned(&self) -> bool {
//         self.0 & 0b001 != 0
//     }

//     fn is_signed(&self) -> bool {
//         !self.is_unsigned()
//     }

//     fn is_int(&self) -> bool {
//         self.0 & 0b010 != 0
//     }

//     fn is_rp(&self) -> bool {
//         self.0 & 0b100 != 0
//     }

//     fn display(self, name: &'static str) -> DisplaySubDictOpArgs {
//         DisplaySubDictOpArgs { name, args: self }
//     }
// }

// struct DisplaySubDictOpArgs {
//     name: &'static str,
//     args: SubDictOpArgs,
// }

// impl std::fmt::Display for DisplaySubDictOpArgs {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         let int = if self.args.is_int() {
//             if self.args.is_unsigned() {
//                 "U"
//             } else {
//                 "I"
//             }
//         } else {
//             ""
//         };
//         write!(f, "SUBDICT{int}{}", self.name)
//     }
// }

fn extract_value_ref(value: CellSliceParts, is_ref: bool) -> VmResult<RcStackValue> {
    let value = OwnedCellSlice::from(value);
    if is_ref {
        to_value_ref(value.apply())
    } else {
        Ok(SafeRc::new_dyn_value(value))
    }
}

fn to_value_ref(mut cs: CellSlice<'_>) -> VmResult<RcStackValue> {
    vm_ensure!(cs.size() == Size { bits: 0, refs: 1 }, DictError);
    let cell = cs.load_reference_cloned()?;
    Ok(SafeRc::new_dyn_value(cell))
}

#[cfg(test)]
pub mod tests {
    use everscale_types::cell::Lazy;
    use num_bigint::BigInt;
    use tracing_test::traced_test;

    use self::dict::{Dict, DictKey};
    use super::*;

    #[test]
    #[traced_test]
    fn store_dict() {
        let init_builder = SafeRc::new_dyn_value(CellBuilder::new());
        let mut dict = Dict::<u32, u32>::new();
        dict.add(1, 1).unwrap();
        let dict = dict.clone().into_root().unwrap();

        let stored = SafeRc::new_dyn_value({
            let mut builder = CellBuilder::new();
            builder.store_bit_one().unwrap();
            builder.store_reference(Cell::clone(&dict)).unwrap();
            builder
        });
        assert_run_vm!("STDICT", [cell dict.clone(), raw init_builder.clone()] => [raw stored]);

        let stored = SafeRc::new_dyn_value({
            let mut builder = CellBuilder::new();
            builder.store_bit_zero().unwrap();
            builder
        });
        assert_run_vm!("STDICT", [null, raw init_builder.clone()] => [raw stored]);
    }

    // TODO: Add SKIPDICT tests

    #[test]
    #[traced_test]
    fn get_dict() {
        let dict = build_dict::<u32, u32, _>(|dict| {
            dict.add(1, 123)?;
            Ok(())
        });

        assert_run_vm!(
            r#"
                DICTIGET
                SWAP NEWC STSLICE ENDC
                SWAP
            "#,
            [int 1, raw dict.clone(), int 32] => [raw new_cell(123), int -1],
        );

        assert_run_vm!("DICTIGET", [int 3, raw dict.clone(), int 32] => [int 0]);
    }

    #[test]
    #[traced_test]
    fn set_dict() {
        let dict_value = build_dict::<u32, u32, _>(|dict| {
            dict.set(1, 1)?;
            Ok(())
        });

        let result_dict = build_dict::<u32, u32, _>(|dict| {
            dict.set(1, 3)?;
            Ok(())
        });
        assert_run_vm!(
            "DICTISET",
            [raw new_slice(3), int 1, raw dict_value.clone(), int 32] => [raw result_dict],
        );

        let result_dict = build_dict::<u32, Lazy<i32>, _>(|dict| {
            dict.add(1, Lazy::new(&123)?)?;
            Ok(())
        });
        assert_run_vm!(
            "DICTISETREF",
            [raw new_cell(123), int 1, raw dict_value.clone(), int 32] => [raw result_dict],
        );
    }

    #[test]
    #[traced_test]
    fn delete_dict() {
        let dict_value = build_dict::<i32, i32, _>(|dict| {
            dict.set(-1, 1)?;
            dict.set(-2, 2)?;
            Ok(())
        });

        let result_dict = build_dict::<i32, i32, _>(|dict| {
            dict.set(-1, 1)?;
            Ok(())
        });

        assert_run_vm!(
            "DICTDEL",
            [raw new_slice(-2), raw dict_value.clone(), int 32] => [raw result_dict.clone(), int -1],
        );
        assert_run_vm!(
            "DICTDEL",
            [raw new_slice(3), raw dict_value.clone(), int 32] => [raw dict_value.clone(), int 0],
        );

        assert_run_vm!("DICTIDEL",
            [int 3, raw dict_value.clone(), int 32] => [raw dict_value.clone(), int 0],
        );
        assert_run_vm!("DICTIDEL",
            [int -2, raw dict_value.clone(), int 32] => [raw result_dict.clone(), int -1],
        );
        assert_run_vm!("DICTUDEL",
            [int -2, raw dict_value.clone(), int 32] => [raw dict_value, int 0],
        );
    }

    #[test]
    #[traced_test]
    fn delete_and_get_dict() {
        let dict = build_dict::<i32, i32, _>(|dict| {
            dict.set(1, 1)?;
            dict.set(-2, 2)?;
            Ok(())
        });

        let result = build_dict::<i32, i32, _>(|dict| {
            dict.set(1, 1)?;
            Ok(())
        });

        assert_run_vm!(
            r#"
            DICTDELGET
            SWAP
            XCHG s1, s2
            NEWC STSLICE ENDC
            XCHG s1, s2
            SWAP
            "#,
            [raw new_slice(-2), raw dict.clone(), int 32] => [raw result.clone(), raw new_cell(2), int -1],
        );
        assert_run_vm!(
            "DICTDELGET",
            [raw new_slice(3), raw dict.clone(), int 32] => [raw dict.clone(), int 0],
        );

        assert_run_vm!(
            r#"
            DICTIDELGET
            SWAP
            XCHG s1, s2
            NEWC STSLICE ENDC
            XCHG s1, s2
            SWAP
            "#,
            [int -2, raw dict.clone(), int 32] => [raw result.clone(), raw new_cell(2), int -1],
        );
        assert_run_vm!(
            "DICTIDELGET",
            [int 3, raw dict.clone(), int 32] => [raw dict.clone(), int 0],
        );
    }

    #[test]
    #[traced_test]
    fn get_min_max_tests() {
        let dict = build_dict::<i32, i32, _>(|dict| {
            dict.set(0, 10)?;
            dict.set(2, 20)?;
            dict.set(3, 30)?;
            Ok(())
        });

        assert_run_vm!(
            r#"
            DICTMIN
            XCHG s0, s2
            NEWC STSLICE ENDC
            XCHG s0, s2
            "#,
            [raw dict.clone(), int 32] => [raw new_cell(10), raw new_slice(0), int -1],
        );
        assert_run_vm!(
            r#"
            DICTMAX
            XCHG s0, s2
            NEWC STSLICE ENDC
            XCHG s0, s2
            "#,
            [raw dict.clone(), int 32] => [raw new_cell(30), raw new_slice(3), int -1],
        );

        assert_run_vm!(
            r#"
            DICTIMIN
            XCHG s0, s2
            NEWC STSLICE ENDC
            XCHG s0, s2
            "#,
            [raw dict.clone(), int 32] => [raw new_cell(10), int 0, int -1],
        );
        assert_run_vm!(
            r#"
            DICTIMAX
            XCHG s0, s2
            NEWC STSLICE ENDC
            XCHG s0, s2
            "#,
            [raw dict.clone(), int 32] => [raw new_cell(30), int 3, int -1],
        );
    }

    #[test]
    #[traced_test]
    fn get_near() {
        let dict = build_dict::<i32, i32, _>(|dict| {
            dict.set(0, 2)?;
            dict.set(1, 4)?;
            dict.set(2, 8)?;
            Ok(())
        });

        assert_run_vm!(
            r#"
            DICTGETNEXT
            XCHG s0, s2
            NEWC STSLICE ENDC
            XCHG s0, s2
            "#,
            [raw new_slice(0), raw dict.clone(), int 32] => [raw new_cell(4), raw new_slice(1), int -1],
        );

        assert_run_vm!(
            r#"
            DICTIGETPREV
            XCHG s0, s2
            NEWC STSLICE ENDC
            XCHG s0, s2
            "#,
            [int 1, raw dict.clone(), int 32] => [raw new_cell(2), int 0, int -1],
        );

        assert_run_vm!(
            r#"
            DICTIGETNEXT
            XCHG s0, s2
            NEWC STSLICE ENDC
            XCHG s0, s2
            "#,
            [int i64::MIN, raw dict.clone(), int 32] => [raw new_cell(2), int 0, int -1],
        );

        assert_run_vm!(
            r#"
            DICTIGETPREV
            XCHG s0, s2
            NEWC STSLICE ENDC
            XCHG s0, s2
            "#,
            [int i64::MAX, raw dict.clone(), int 32] => [raw new_cell(8), int 2, int -1],
        );
    }

    #[test]
    #[traced_test]
    fn set_get_dict() {
        let dict = build_dict::<i32, i32, _>(|dict| {
            dict.set(0, 2)?;
            dict.set(1, 4)?;
            dict.set(2, 8)?;
            Ok(())
        });

        let updated_dict = build_dict::<i32, i32, _>(|dict| {
            dict.set(0, 5)?;
            dict.set(1, 4)?;
            dict.set(2, 8)?;
            Ok(())
        });

        let updated_dict2 = build_dict::<i32, i32, _>(|dict| {
            dict.set(0, 2)?;
            dict.set(1, 4)?;
            dict.set(2, 8)?;
            dict.set(3, 5)?;
            Ok(())
        });

        assert_run_vm!(
            r#"
            DICTSETGET
            SWAP
            NEWC STSLICE ENDC
            SWAP
            "#,
            [
                raw new_slice(5),
                raw new_slice(0),
                raw dict.clone(),
                int 32
            ] => [raw updated_dict.clone(), raw new_cell(2), int -1],
        );
        assert_run_vm!(
            r#"
            DICTREPLACEGET
            SWAP
            NEWC STSLICE ENDC
            SWAP
            "#,
            [
                raw new_slice(5),
                raw new_slice(0),
                raw dict.clone(),
                int 32
            ] => [raw updated_dict.clone(), raw new_cell(2), int -1],
        );

        assert_run_vm!(
            "DICTREPLACEGET",
            [raw new_slice(5), raw new_slice(3), raw dict.clone(), int 32] => [raw dict.clone(), int 0],
        );
        assert_run_vm!(
            "DICTADDGET",
            [raw new_slice(5), raw new_slice(3), raw dict.clone(), int 32] => [raw updated_dict2, int -1],
        );
    }

    // #[test]
    // #[traced_test]
    // fn subdict_get_test() {
    //     let x = 0b100000;
    //     let v = 0b100001;
    //     let y = 0b000001;
    //     let z = 0b000010;

    //     let dict = build_dict::<i32, i32, _>(|dict| {
    //         dict.set(x, 32)?;
    //         dict.set(y, 1)?;
    //         dict.set(z, 2)?;
    //         dict.set(v, 33)?;
    //         Ok(())
    //     });

    //     let mut builder = CellBuilder::new();
    //     builder.store_bit_zero().unwrap();
    //     builder.store_bit_zero().unwrap();
    //     let cell = builder.build().unwrap();
    //     let slice = OwnedCellSlice::from(cell);
    //     let binding = slice.clone();
    //     let mut cloned = binding.apply().unwrap();

    //     let mut dict2 = everscale_types::dict::Dict::<i32, i32>::new();
    //     dict2.set(x, 32).unwrap();
    //     dict2.set(y, 1).unwrap();
    //     dict2.set(z, 2).unwrap();
    //     dict2.set(v, 33).unwrap();

    //     let subdict = everscale_types::dict::dict_get_subdict(
    //         dict2.into_root().as_ref(),
    //         32,
    //         &mut cloned,
    //         Cell::empty_context(),
    //     )
    //     .unwrap()
    //     .unwrap();
    //     let subdict: RcStackValue = Rc::new(subdict);

    //     let key = Rc::new(slice);

    //     assert_run_vm!(r#"
    //             SUBDICTGET
    //         "#,
    //         [raw key, int 32, raw dict.clone(), int 32] => [raw subdict],
    //     );
    // }

    #[test]
    #[traced_test]
    fn dict_set_getopt_ref_tests() {
        let dict = build_dict::<i32, Lazy<i32>, _>(|dict| {
            dict.set(0, Lazy::new(&2)?)?;
            Ok(())
        });

        assert_run_vm!(
            "DICTGETOPTREF",
            [raw new_slice(0), raw dict.clone(), int 32] => [raw new_cell(2)],
        );

        assert_run_vm!(
            "DICTGETOPTREF",
            [raw new_slice(1), raw dict.clone(), int 32] => [null],
        );
    }

    #[test]
    #[traced_test]
    fn set_get_opt_ref_dict() {
        let dict = build_dict::<i32, Lazy<i32>, _>(|dict| {
            dict.set(0, Lazy::new(&2)?)?;
            dict.set(1, Lazy::new(&2)?)?;
            Ok(())
        });

        let updated_dict = build_dict::<i32, Lazy<i32>, _>(|dict| {
            dict.set(0, Lazy::new(&5)?)?;
            dict.set(1, Lazy::new(&2)?)?;
            Ok(())
        });
        assert_run_vm!(
            "DICTSETGETOPTREF",
            [
                raw new_cell(5),
                raw new_slice(0),
                raw dict.clone(),
                int 32
            ] => [raw updated_dict, raw new_cell(2)],
        );

        let updated_dict = build_dict::<i32, Lazy<i32>, _>(|dict| {
            dict.set(0, Lazy::new(&2)?)?;
            dict.set(1, Lazy::new(&2)?)?;
            dict.set(2, Lazy::new(&5)?)?;
            Ok(())
        });
        assert_run_vm!(
            "DICTSETGETOPTREF",
            [raw new_cell(5), raw new_slice(2), raw dict.clone(), int 32] => [raw updated_dict.clone(), null],
        );

        let updated_dict = build_dict::<i32, Lazy<i32>, _>(|dict| {
            dict.set(1, Lazy::new(&2)?)?;
            Ok(())
        });
        assert_run_vm!(
            "DICTSETGETOPTREF",
            [null, raw new_slice(0), raw dict.clone(), int 32] => [raw updated_dict, raw new_cell(2)],
        );
    }

    fn new_slice(value: i32) -> RcStackValue {
        let value = BigInt::from(value);
        let mut builder = CellBuilder::new();
        store_int_to_builder(&value, 32, true, &mut builder).unwrap();
        SafeRc::new_dyn_value(OwnedCellSlice::new_allow_exotic(builder.build().unwrap()))
    }

    fn new_cell(value: i32) -> RcStackValue {
        SafeRc::new_dyn_value(CellBuilder::build_from(value).unwrap())
    }

    fn build_dict<K, V, F>(f: F) -> RcStackValue
    where
        K: Store + DictKey,
        V: Store,
        for<'a> F: FnOnce(&'a mut Dict<K, V>) -> anyhow::Result<()>,
    {
        let mut dict = Dict::<K, V>::new();
        f(&mut dict).unwrap();
        SafeRc::new_dyn_value(dict.into_root().unwrap())
    }
}
