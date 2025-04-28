use std::fmt::Formatter;

use everscale_types::cell::{CellTreeStats, LoadMode};
use everscale_types::dict;
use everscale_types::models::{GasLimitsPrices, MsgForwardPrices, StoragePrices};
use everscale_types::prelude::*;
use num_bigint::Sign;
use tycho_vm_proc::vm_module;

use crate::cont::ControlRegs;
use crate::error::VmResult;
use crate::gas::GasConsumer;
use crate::saferc::SafeRc;
use crate::smc_info::{SmcInfoBase, SmcInfoTonV11, SmcInfoTonV4, SmcInfoTonV6};
use crate::stack::{RcStackValue, Stack, TupleExt};
use crate::state::VmState;
use crate::util::{shift_ceil_price, OwnedCellSlice};

pub struct ConfigOps;

#[vm_module]
impl ConfigOps {
    #[op(code = "f82s", fmt = DisplayConfigOpsArgs(s))]
    fn exec_get_param(st: &mut VmState, s: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(get_and_push_param(&mut st.cr, stack, s as usize));
        Ok(0)
    }

    #[op(code = "f88111", fmt = "INMSGPARAMS")]
    fn exec_get_in_msg_params(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(11..));
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(get_and_push_param(
            &mut st.cr,
            stack,
            SmcInfoTonV11::IN_MSG_PARAMS_IDX
        ));
        Ok(0)
    }

    #[op(code = "f8ssss @ f88100..f88111", fmt = "GETPARAMLONG {s}", args(s = args & 255))]
    #[op(code = "f8ssss @ f88112..f881ff", fmt = "GETPARAMLONG {s}", args(s = args & 255))]
    fn exec_get_param_long(st: &mut VmState, s: u32) -> VmResult<i32> {
        ok!(st.version.require_ton(11..));
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(get_and_push_param(&mut st.cr, stack, s as usize));
        Ok(0)
    }

    #[op(code = "f8ss @ f890..f8a0", fmt = DisplayInMsgParamArgs(s), args(s = args & 15))]
    fn exec_get_in_msg_param(st: &mut VmState, s: u32) -> VmResult<i32> {
        ok!(st.version.require_ton(11..));
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(get_and_push_in_msg_param(&mut st.cr, stack, s as usize));
        Ok(0)
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
}

pub struct DisplayInMsgParamArgs(u32);

impl std::fmt::Display for DisplayInMsgParamArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let code = match self.0 {
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
        };
        write!(f, "{}", code)
    }
}

pub struct DisplayConfigOpsArgs(u32);

impl std::fmt::Display for DisplayConfigOpsArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let code = match self.0 {
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
            i => return write!(f, "GETPARAM {i}"),
        };
        write!(f, "{}", code)
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
    mss_param_index: usize,
) -> VmResult<i32> {
    let param = ok!(regs
        .get_c7_params()
        .and_then(|t| t.try_get(SmcInfoTonV11::IN_MSG_PARAMS_IDX)));
    let in_msg_params_tuple = ok!(param.clone().into_tuple());
    let param = ok!(in_msg_params_tuple.try_get(mss_param_index));
    ok!(stack.push_raw(param.clone()));
    Ok(0)
}

fn get_parsed_config(regs: &ControlRegs) -> VmResult<&[RcStackValue]> {
    ok!(regs.get_c7_params()).try_get_tuple_range(SmcInfoTonV6::PARSED_CONFIG_IDX, 0..=255)
}

const CONFIG_KEY_BITS: u16 = 32;

#[cfg(test)]
mod test {
    use everscale_types::boc::Boc;
    use everscale_types::dict::Dict;
    use everscale_types::models::{CurrencyCollection, ExtraCurrencyCollection};
    use everscale_types::num::VarUint248;
    use tracing_test::traced_test;

    use crate::{SmcInfoBase, VmState};

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
