use std::fmt::Formatter;

use num_bigint::Sign;
use tycho_types::cell::{CellTreeStats, LoadMode};
use tycho_types::dict;
use tycho_types::models::{GasLimitsPrices, MsgForwardPrices, StoragePrices};
use tycho_types::prelude::*;
use tycho_vm_proc::vm_module;

use crate::cont::ControlRegs;
use crate::error::VmResult;
use crate::gas::GasConsumer;
use crate::saferc::SafeRc;
use crate::smc_info::{SmcInfoBase, SmcInfoTonV4, SmcInfoTonV6, SmcInfoTonV11};
use crate::stack::{RcStackValue, Stack, TupleExt};
use crate::state::VmState;
use crate::util::{OwnedCellSlice, shift_ceil_price};

pub struct ConfigOps;

#[vm_module]
impl ConfigOps {
    #[op(code = "f82i", fmt = DisplayConfigOpsArgs(i))]
    fn exec_get_param(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        get_and_push_param(&mut st.cr, stack, i as usize)
    }

    #[op(code = "f830", fmt = "CONFIGDICT")]
    fn exec_get_config_dict(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(get_and_push_param(
            &mut st.cr,
            stack,
            SmcInfoBase::CONFIG_IDX
        ));
        ok!(stack.push_int(CONFIG_KEY_BITS));
        Ok(0)
    }

    #[op(code = "f832", fmt = "CONFIGPARAM", args(opt = false))]
    #[op(code = "f833", fmt = "CONFIGOPTPARAM", args(opt = true))]
    fn exec_get_config_param(st: &mut VmState, opt: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_int());

        ok!(get_and_push_param(
            &mut st.cr,
            stack,
            SmcInfoBase::CONFIG_IDX
        ));
        let dict = ok!(stack.pop_cell_opt());

        let mut builder = CellDataBuilder::new();
        builder.store_bigint(&idx, CONFIG_KEY_BITS, true)?;
        let key = builder.as_data_slice();

        let value = dict::dict_get(dict.as_deref(), CONFIG_KEY_BITS, key, &st.gas)?;
        let param = match value {
            Some(mut value) => Some(value.load_reference_cloned()?),
            None => None,
        };

        if opt {
            ok!(stack.push_opt(param));
        } else {
            match param {
                Some(cell) => {
                    ok!(stack.push_raw(SafeRc::new(cell)));
                    ok!(stack.push_bool(true));
                }
                None => ok!(stack.push_bool(false)),
            }
        }
        Ok(0)
    }

    #[op(code = "f83400", fmt = "PREVMCBLOCKS", args(i = 0))]
    #[op(code = "f83401", fmt = "PREVKEYBLOCK", args(i = 1))]
    fn exec_get_prev_blocks_info(st: &mut VmState, i: u32) -> VmResult<i32> {
        ok!(st.version.require_ton(4..));
        let t1 = ok!(st.cr.get_c7_params());
        let t2 = ok!(t1.try_get_tuple_range(SmcInfoTonV4::PREV_BLOCKS_IDX, 0..=255));
        let param = ok!(t2.try_get((i as usize) & 0b11));
        ok!(SafeRc::make_mut(&mut st.stack).push_raw(param.clone()));
        Ok(0)
    }

    #[op(code = "f835", fmt = "GLOBALID")]
    fn exec_get_global_id(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(4..));

        let global_id = if let Some(global_id) = st.modifiers.signature_with_id {
            global_id
        } else if st.version.is_ton(6..) {
            let t2 = ok!(get_parsed_config(&st.cr));
            ok!(t2.try_get_ref::<OwnedCellSlice>(1))
                .apply()
                .load_u32()? as i32
        } else {
            let t1 = ok!(st.cr.get_c7_params());
            let config_root = ok!(t1.try_get_ref::<Cell>(SmcInfoBase::CONFIG_IDX));

            let mut builder = CellBuilder::new();
            builder.store_u32(19).unwrap(); // ConfigParam 19 contains global id
            let key = builder.as_data_slice();

            let Some(mut value) = dict::dict_get(Some(config_root), CONFIG_KEY_BITS, key, &st.gas)?
            else {
                vm_bail!(Unknown("invalid global id config".to_owned()));
            };

            let param = value.load_reference()?;
            st.gas
                .load_dyn_cell(param, LoadMode::Full)?
                .parse::<u32>()? as i32
        };

        ok!(SafeRc::make_mut(&mut st.stack).push_int(global_id));
        Ok(0)
    }

    #[op(code = "f836", fmt = "GETGASFEE")]
    fn exec_get_gas_fee(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(6..));

        let stack = SafeRc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let gas = ok!(stack.pop_long_range(0, u64::MAX));

        let t2 = ok!(get_parsed_config(&st.cr));
        let cs = ok!(t2.try_get_ref::<OwnedCellSlice>(if is_masterchain { 2 } else { 3 }));
        let config = GasLimitsPrices::load_from(&mut cs.apply())?;

        let price = config.compute_gas_fee(gas);
        ok!(stack.push_int(price.into_inner()));
        Ok(0)
    }

    #[op(code = "f837", fmt = "GETSTORAGEFEE")]
    fn exec_get_storage_fee(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(6..));

        let stack = SafeRc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let delta = ok!(stack.pop_long_range(0, u64::MAX));
        let bits = ok!(stack.pop_long_range(0, u64::MAX));
        let cells = ok!(stack.pop_long_range(0, u64::MAX));

        let t2 = ok!(get_parsed_config(&st.cr));
        match t2.first().and_then(|t| t.as_cell_slice()) {
            // No StoragePrices is active, so the price is 0.
            None => ok!(stack.push_zero()),
            Some(cs) => {
                let config = StoragePrices::load_from(&mut cs.apply())?;
                let fee = config.compute_storage_fee(is_masterchain, delta, CellTreeStats {
                    bit_count: bits,
                    cell_count: cells,
                });
                ok!(stack.push_int(fee.into_inner()));
            }
        }
        Ok(0)
    }

    #[op(code = "f838", fmt = "GETFORWARDFEE")]
    fn exec_get_forward_fee(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(6..));

        let stack = SafeRc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let bits = ok!(stack.pop_long_range(0, u64::MAX));
        let cells = ok!(stack.pop_long_range(0, u64::MAX));

        let t2 = ok!(get_parsed_config(&st.cr));
        let cs = ok!(t2.try_get_ref::<OwnedCellSlice>(if is_masterchain { 4 } else { 5 }));
        let config = MsgForwardPrices::load_from(&mut cs.apply())?;

        let fee = config.compute_fwd_fee(CellTreeStats {
            bit_count: bits,
            cell_count: cells,
        });
        ok!(stack.push_int(fee.into_inner()));
        Ok(0)
    }

    #[op(code = "f839", fmt = "GETPRECOMPILEDGAS")]
    fn exec_get_precompiled_gas(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(6..));

        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(get_and_push_param(
            &mut st.cr,
            stack,
            SmcInfoTonV6::PRECOMPILED_GAS_IDX
        ));
        Ok(0)
    }

    #[op(code = "f83a", fmt = "GETORIGINALFWDFEE")]
    fn exec_get_original_fwd_fee(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(6..));

        let stack = SafeRc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let mut fwd_fee = ok!(stack.pop_int());
        vm_ensure!(fwd_fee.sign() != Sign::Minus, IntegerOutOfRange {
            min: u64::MIN as isize,
            max: u64::MAX as isize,
            actual: fwd_fee.to_string()
        });

        let t2 = ok!(get_parsed_config(&st.cr));
        let cs = ok!(t2.try_get_ref::<OwnedCellSlice>(if is_masterchain { 4 } else { 5 }));
        let config = MsgForwardPrices::load_from(&mut cs.apply())?;

        {
            let t = SafeRc::make_mut(&mut fwd_fee);
            *t <<= 16;

            // NOTE: `q` is always non-zero because `first_frac` is `u16` and we substract
            //       at most `2^16-1` from `2^16`.
            *t /= (1u32 << 16) - config.first_frac as u32;
        }

        ok!(stack.push_raw(fwd_fee));
        Ok(0)
    }

    #[op(code = "f83b", fmt = "GETGASFEESIMPLE")]
    fn exec_get_gas_fee_simple(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(6..));

        let stack = SafeRc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let gas = ok!(stack.pop_long_range(0, u64::MAX));

        let t2 = ok!(get_parsed_config(&st.cr));
        let cs = ok!(t2.try_get_ref::<OwnedCellSlice>(if is_masterchain { 2 } else { 3 }));
        let config = GasLimitsPrices::load_from(&mut cs.apply())?;

        let fee = shift_ceil_price(gas as u128 * config.gas_price as u128);
        ok!(stack.push_int(fee));
        Ok(0)
    }

    #[op(code = "f83c", fmt = "GETFORWARDFEESIMPLE")]
    fn exec_get_forward_fee_simple(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(6..));

        let stack = SafeRc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let bits = ok!(stack.pop_long_range(0, u64::MAX));
        let cells = ok!(stack.pop_long_range(0, u64::MAX));

        let t2 = ok!(get_parsed_config(&st.cr));
        let cs = ok!(t2.try_get_ref::<OwnedCellSlice>(if is_masterchain { 4 } else { 5 }));
        let config = MsgForwardPrices::load_from(&mut cs.apply())?;

        let fee = shift_ceil_price(
            (cells as u128 * config.cell_price as u128)
                .saturating_add(bits as u128 * config.bit_price as u128),
        );
        ok!(stack.push_int(fee));
        Ok(0)
    }

    #[op(code = "f880", fmt = "GETEXTRABALANCE")]
    fn exec_get_extra_currency_balance(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(10..));

        let stack = SafeRc::make_mut(&mut st.stack);
        let id = ok!(stack.pop_smallint_range(0, u32::MAX));

        let t1 = ok!(st.cr.get_c7_params());
        let balance = ok!(t1.try_get_tuple_range(SmcInfoBase::BALANCE_IDX, 0..=255));
        let extra_currency = balance.get(1).and_then(|v| v.as_cell()).cloned();
        let balance = RawDict::<32>::from(extra_currency);

        let mut key_builder = CellBuilder::new();
        key_builder.store_u32(id).ok();

        let cheap_consumer = st.gas.try_get_extra_balance_consumer();
        let gas_context: &dyn CellContext = match &cheap_consumer {
            Some(cheap_consumer) => cheap_consumer,
            None => &st.gas,
        };

        let value_opt = balance.get_ext(key_builder.as_data_slice(), gas_context)?;
        if let Some(mut value) = value_opt {
            let result = value.load_var_bigint(5, false)?;
            ok!(stack.push_int(result));
        } else {
            ok!(stack.push_zero());
        }
        Ok(0)
    }

    #[op(code = "f840", fmt = "GETGLOBVAR")]
    fn exec_get_global_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let args = ok!(stack.pop_smallint_range(0, 254));
        get_global_common(&mut st.cr, stack, args as usize)
    }

    #[op(code = "f8ii @ f841..f860", fmt = "GETGLOB {i}", args(i = args & 31))]
    fn exec_get_global(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        get_global_common(&mut st.cr, stack, i as usize)
    }

    #[op(code = "f860", fmt = "SETGLOBVAR")]
    fn exec_set_global_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let args = ok!(stack.pop_smallint_range(0, 254));
        set_global_common(&mut st.cr, stack, &st.gas, args as usize)
    }

    #[op(code = "f8ii @ f861..f880", fmt = "SETGLOB {i}", args(i = args & 31))]
    fn exec_set_global(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        set_global_common(&mut st.cr, stack, &st.gas, i as usize)
    }

    #[op(code = "f881ii", fmt = DisplayConfigOpsArgs(i))]
    fn exec_get_param_long(st: &mut VmState, i: u32) -> VmResult<i32> {
        ok!(st.version.require_ton(11..));
        let stack = SafeRc::make_mut(&mut st.stack);
        get_and_push_param(&mut st.cr, stack, i as usize)
    }

    #[op(code = "f89i", fmt = DisplayInMsgParamArgs(i))]
    fn exec_get_in_msg_param(st: &mut VmState, i: u32) -> VmResult<i32> {
        ok!(st.version.require_ton(11..));
        let stack = SafeRc::make_mut(&mut st.stack);
        get_and_push_in_msg_param(&mut st.cr, stack, i as usize)
    }
}

pub struct DisplayConfigOpsArgs(u32);

impl std::fmt::Display for DisplayConfigOpsArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self.0 {
            3 => "NOW",
            4 => "BLOCKLT",
            5 => "LTIME",
            6 => "RANDSEED",
            7 => "BALANCE",
            8 => "MYADDR",
            9 => "CONFIGROOT",
            10 => "MYCODE",
            11 => "INCOMINGVALUE",
            12 => "STORAGEFEES",
            13 => "PREVBLOCKSINFOTUPLE",
            14 => "UNPACKEDCONFIGTUPLE",
            15 => "DUEPAYMENT",
            17 => "INMSGPARAMS",
            i => return write!(f, "GETPARAM {i}"),
        })
    }
}

pub struct DisplayInMsgParamArgs(u32);

impl std::fmt::Display for DisplayInMsgParamArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self.0 {
            0 => "INMSG_BOUNCE",
            1 => "INMSG_BOUNCED",
            2 => "INMSG_SRC",
            3 => "INMSG_FWDFEE",
            4 => "INMSG_LT",
            5 => "INMSG_UTIME",
            6 => "INMSG_ORIGVALUE",
            7 => "INMSG_VALUE",
            8 => "INMSG_VALUEEXTRA",
            9 => "INMSG_STATEINIT",
            i => return write!(f, "INMSGPARAM {i}"),
        })
    }
}

fn get_global_common(regs: &mut ControlRegs, stack: &mut Stack, index: usize) -> VmResult<i32> {
    match &regs.c7 {
        None => ok!(stack.push_null()),
        Some(c7) => ok!(stack.push_opt_raw(c7.get(index).cloned())),
    }
    Ok(0)
}

fn set_global_common(
    regs: &mut ControlRegs,
    stack: &mut Stack,
    gas: &GasConsumer,
    index: usize,
) -> VmResult<i32> {
    let value = ok!(stack.pop());
    vm_ensure!(index < 255, IntegerOutOfRange {
        min: 0,
        max: 255,
        actual: index.to_string()
    });

    let tuple_len_to_pay;
    match &mut regs.c7 {
        // Do nothing if we are inserting `null` to an empty tuple.
        None if value.is_null() => tuple_len_to_pay = 0,
        // Create a new tuple with only one value set.
        None => {
            let mut c7 = vec![Stack::make_null(); index + 1];
            c7[index] = value;
            tuple_len_to_pay = c7.len();
            regs.c7 = Some(SafeRc::new(c7));
        }
        // Do nothing if we are inserting `null` to an index out of the tuple range.
        Some(c7) if index >= c7.len() && value.is_null() => tuple_len_to_pay = 0,
        // Replace an existing value.
        Some(c7) => {
            let c7 = SafeRc::make_mut(c7);
            if index >= c7.len() {
                c7.resize(index + 1, Stack::make_null());
            }
            c7[index] = value;
            tuple_len_to_pay = c7.len();
        }
    }

    gas.try_consume_tuple_gas(tuple_len_to_pay as _)?;
    Ok(0)
}

fn get_and_push_param(regs: &mut ControlRegs, stack: &mut Stack, index: usize) -> VmResult<i32> {
    let param = ok!(regs.get_c7_params().and_then(|t| t.try_get(index)));
    ok!(stack.push_raw(param.clone()));
    Ok(0)
}

fn get_and_push_in_msg_param(
    regs: &mut ControlRegs,
    stack: &mut Stack,
    index: usize,
) -> VmResult<i32> {
    let t1 = ok!(regs.get_c7_params());
    let in_msg_params = ok!(t1.try_get(SmcInfoTonV11::IN_MSG_PARAMS_IDX));
    let in_msg_params = ok!(in_msg_params.try_as_tuple());
    let param = ok!(in_msg_params.try_get(index));
    ok!(stack.push_raw(param.clone()));
    Ok(0)
}

fn get_parsed_config(regs: &ControlRegs) -> VmResult<&[RcStackValue]> {
    ok!(regs.get_c7_params()).try_get_tuple_range(SmcInfoTonV6::PARSED_CONFIG_IDX, 0..=255)
}

const CONFIG_KEY_BITS: u16 = 32;

#[cfg(test)]
mod test {
    use tracing_test::traced_test;
    use tycho_types::models::{CurrencyCollection, ExtraCurrencyCollection, IntAddr};
    use tycho_types::num::{Tokens, VarUint248};
    use tycho_types::prelude::*;
    use tycho_vm::smc_info::SmcInfoTonV11;

    use crate::{OwnedCellSlice, RcStackValue, SafeRc, SmcInfoBase, Stack, VmState};

    #[test]
    #[traced_test]
    pub fn in_msg_params_works() {
        let t2 = SafeRc::new_dyn_value(
            tuple![int 0, int 1, int 2, int 3, int 4, int 5, int 6, int 7, int 8, int 9],
        );

        let mut t1 = Vec::<RcStackValue>::with_capacity(SmcInfoTonV11::IN_MSG_PARAMS_IDX + 1);
        t1.resize_with(SmcInfoTonV11::IN_MSG_PARAMS_IDX, Stack::make_null);
        t1.push(t2.clone());

        let c7 = tuple![raw RcStackValue::from(t1)];

        assert_run_vm!("INMSGPARAMS", c7: c7.clone(), [] => [raw t2.clone()]);
        assert_run_vm!("GETPARAMLONG 17", c7: c7.clone(), [] => [raw t2]);

        assert_run_vm!("INMSG_BOUNCE", c7: c7.clone(), [] => [int 0]);
        assert_run_vm!("INMSGPARAM 0", c7: c7.clone(), [] => [int 0]);

        assert_run_vm!("INMSG_BOUNCED", c7: c7.clone(), [] => [int 1]);
        assert_run_vm!("INMSGPARAM 1", c7: c7.clone(), [] => [int 1]);

        assert_run_vm!("INMSG_SRC", c7: c7.clone(), [] => [int 2]);
        assert_run_vm!("INMSGPARAM 2", c7: c7.clone(), [] => [int 2]);

        assert_run_vm!("INMSG_FWDFEE", c7: c7.clone(), [] => [int 3]);
        assert_run_vm!("INMSGPARAM 3", c7: c7.clone(), [] => [int 3]);

        assert_run_vm!("INMSG_LT", c7: c7.clone(), [] => [int 4]);
        assert_run_vm!("INMSGPARAM 4", c7: c7.clone(), [] => [int 4]);

        assert_run_vm!("INMSG_UTIME", c7: c7.clone(), [] => [int 5]);
        assert_run_vm!("INMSGPARAM 5", c7: c7.clone(), [] => [int 5]);

        assert_run_vm!("INMSG_ORIGVALUE", c7: c7.clone(), [] => [int 6]);
        assert_run_vm!("INMSGPARAM 6", c7: c7.clone(), [] => [int 6]);

        assert_run_vm!("INMSG_VALUE", c7: c7.clone(), [] => [int 7]);
        assert_run_vm!("INMSGPARAM 7", c7: c7.clone(), [] => [int 7]);

        assert_run_vm!("INMSG_VALUEEXTRA", c7: c7.clone(), [] => [int 8]);
        assert_run_vm!("INMSGPARAM 8", c7: c7.clone(), [] => [int 8]);

        assert_run_vm!("INMSG_STATEINIT", c7: c7.clone(), [] => [int 9]);
        assert_run_vm!("INMSGPARAM 9", c7: c7.clone(), [] => [int 9]);

        assert_run_vm!("INMSGPARAM 10", c7: c7.clone(), [] => [int 0], exit_code: 5);

        assert_run_vm!("NULL POP c7 GETPARAMLONG 17", [] => [int 0], exit_code: 7);
        assert_run_vm!("NIL POP c7 GETPARAMLONG 17", [] => [int 0], exit_code: 5);

        assert_run_vm!(
            r#"
            PUSHCONT { INT 20 REPEATEND NULL } EXECUTE
            POP c7 GETPARAMLONG 17
            "#,
            [] => [int 0],
            exit_code: 7,
        );
        assert_run_vm!(
            r#"
            PUSHCONT { INT 20 REPEATEND NIL } EXECUTE
            POP c7 GETPARAMLONG 17
            "#,
            [] => [int 0],
            exit_code: 5,
        );
    }

    #[test]
    #[traced_test]
    pub fn in_msg_params_real_message() -> anyhow::Result<()> {
        let msg = Boc::decode_base64("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").unwrap();
        let t2 =
            SmcInfoTonV11::unpack_in_msg_partial(msg.clone(), Some(CurrencyCollection::new(123)))?
                .unwrap()
                .into_tuple()
                .into_dyn_value();

        let mut t1 = Vec::<RcStackValue>::with_capacity(SmcInfoTonV11::IN_MSG_PARAMS_IDX + 1);
        t1.resize_with(SmcInfoTonV11::IN_MSG_PARAMS_IDX, Stack::make_null);
        t1.push(t2.clone());

        let c7 = tuple![raw RcStackValue::from(t1)];

        let expected_src = "0:cfc857bf789e991903c273a68e9d5a10f4f9647d79fb669f9a8ab96a2eb6894b"
            .parse::<IntAddr>()?;
        let mut expected_src_addr = CellBuilder::new();
        expected_src.store_into(&mut expected_src_addr, Cell::empty_context())?;
        let expected_src_addr = expected_src_addr.as_data_slice();

        let src_addr_slice = {
            let mut cs = msg.as_slice()?;
            cs.skip_first(4, 0)?;
            let mut addr_slice = cs;
            IntAddr::load_from(&mut cs)?;
            addr_slice.skip_last(cs.size_bits(), cs.size_refs())?;
            assert!(addr_slice.contents_eq(&expected_src_addr)?);
            OwnedCellSlice::from((addr_slice.range(), msg))
        };

        let state_init = Boc::decode_base64(
            "te6ccgECHwEAAusAAgE0BwEBAcACAgPPoAQDAENIAJ6f+HWW+qtokWFlE2WdLD8aATPceZK4qWHZeqfEJ7rnAgEgBgUAQyAFJOanCsVNCqqvMSOs8XJzs2kTAFvABsSPI3yUj4IlSewAQQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAIGits1HggEJIrtUyDjAyDA/+MCIMD+4wLyCxoLCgkAAAOK7UTQ10nDAfhmifhpIds80wABn4ECANcYIPkBWPhC+RDyqN7TPwH4QyG58rQg+COBA+iogggbd0CgufK0+GPTHwHbPPI8GBQMA1LtRNDXScMB+GYi0NMD+kAw+GmpOADcIccA4wIh1w0f8rwh4wMB2zzyPBkZDAEUIIIQFaA4+7rjAg0EkDD4Qm7jAPhG8nMhltTTH9TR0JPU0x/i+kDU0dD6QNH4SfhKxwUgjoDfjoCOFCDIz4UIzoBvz0DJgQCApiC1B/sA4l8E2zzyABQRDh0BCF0i2zwPAnz4SsjO+EsBznABy39wAcsfEssfzvhBiMjPjits1szOyQHMIfsEAdAgizits1jHBZPXTdDe10zQ7R7tU8nbPB4QAATwAgEeMCH6Qm8T1wv/wwAgjoDeEgEQMCHbPPhJxwUTAX5wyMv/cG2AQPRD+EpxWIBA9BYBcliAQPQWyPQAyfhBiMjPjits1szOycjPhID0APQAz4HJ+QDIz4oAQMv/ydAeAhbtRNDXScIBjoDjDRYVADTtRNDT/9M/0wAx+kDU0dD6QNH4a/hq+GP4YgJUcO1E0PQFcSGAQPQOjoDfciKAQPQOjoDf+Gv4aoBA9A7yvdcL//hicPhjFxcBAokYAEOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAr4RvLgTAIK9KQg9KEcGwAUc29sIDAuNTcuMQEYoAAAAAIw2zz4D/IAHQAs+Er4Q/hCyMv/yz/Pg874S8jOzcntVAAMIPhh7R7Z",
        )?;

        assert_run_vm!("INMSGPARAMS", c7: c7.clone(), [] => [raw t2.clone()]);
        assert_run_vm!("INMSG_BOUNCE", c7: c7.clone(), [] => [int -1]);
        assert_run_vm!("INMSG_BOUNCED", c7: c7.clone(), [] => [int 0]);
        assert_run_vm!("INMSG_SRC", c7: c7.clone(), [] => [slice src_addr_slice]);
        assert_run_vm!("INMSG_FWDFEE", c7: c7.clone(), [] => [int Tokens::new(14429777)]);
        assert_run_vm!("INMSG_LT", c7: c7.clone(), [] => [int 60816838000029u64]);
        assert_run_vm!("INMSG_UTIME", c7: c7.clone(), [] => [int 1747232881u32]);
        assert_run_vm!("INMSG_ORIGVALUE", c7: c7.clone(), [] => [int Tokens::new(500_000_000)]);
        assert_run_vm!("INMSG_VALUE", c7: c7.clone(), [] => [int 123]);
        assert_run_vm!("INMSG_VALUEEXTRA", c7: c7.clone(), [] => [null]);
        assert_run_vm!("INMSG_STATEINIT", c7: c7.clone(), [] => [cell state_init]);

        Ok(())
    }

    #[test]
    #[traced_test]
    pub fn balance_test() -> anyhow::Result<()> {
        let mut dict = Dict::<u32, VarUint248>::new();
        dict.set(1, VarUint248::new(2))?;

        let c7 = tuple![[
            null,                                   // 0
            null,                                   // 1
            null,                                   // 2
            null,                                   // 3
            null,                                   // 4
            null,                                   // 5
            null,                                   // 6
            [null, cell dict.into_root().unwrap()], // balance
        ]];
        assert_run_vm!("GETEXTRABALANCE", c7: c7.clone(), [int 1] => [int 2]);
        Ok(())
    }

    #[test]
    #[traced_test]
    pub fn balance_gas_test() -> anyhow::Result<()> {
        let mut dict = Dict::<u32, VarUint248>::new();
        for i in 1..20 {
            dict.set(i, VarUint248::new(i as _))?;
        }

        let code = Boc::decode(tvmasm!("GETEXTRABALANCE"))?;

        let stack = tuple![int 10];
        let mut output = crate::tests::TracingOutput::default();
        let mut state = VmState::builder()
            .with_stack(stack)
            .with_smc_info(SmcInfoBase {
                now: 0,
                block_lt: 0,
                tx_lt: 0,
                rand_seed: Default::default(),
                account_balance: CurrencyCollection {
                    tokens: Default::default(),
                    other: ExtraCurrencyCollection::from_raw(dict.into_root()),
                },
                addr: Default::default(),
                config: None,
            })
            .with_version(crate::VmVersion::LATEST_TON)
            .with_code(code)
            .with_debug(&mut output)
            .build();

        let result = !state.run();

        assert_eq!(state.gas.consumed(), 231);
        assert_eq!(result, 0);

        Ok(())
    }
}
