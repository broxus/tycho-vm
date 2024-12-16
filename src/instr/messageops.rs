use crate::cont::ControlRegs;
use crate::error::VmResult;
use crate::stack::RcStackValue;
use crate::util::OwnedCellSlice;
use crate::VmState;
use everscale_types::cell::{CellBuilder, CellSlice, CellSliceParts, HashBytes, StorageStat};
use everscale_types::error::Error;
use everscale_types::models::{
    BaseMessage, BlockchainConfig, MsgForwardPrices, OwnedRelaxedMessage, RelaxedMsgInfo,
};
use everscale_types::num::{SplitDepth, Tokens};
use everscale_types::prelude::{Cell, CellFamily, Load, Store};
use everscale_vm::stack::StackValueType;
use everscale_vm::util::{get_param_from_c7, load_uint_leq};
use everscale_vm_proc::vm_module;
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use std::fmt::Formatter;
use std::ops::{Add, AddAssign, Mul, Shr, Sub};
use std::rc::Rc;

pub struct MessageOps;

const OUTPUT_ACTIONS_IDX: usize = 5;
#[vm_module]
impl MessageOps {
    #[instr(code = "fb00", fmt = "SENDRAWMSG")]
    fn exec_send_message_raw(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let f = ok!(stack.pop_smallint_range(0, 255));
        let cell: Rc<Cell> = ok!(stack.pop_cell());

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x0ec3c86d, 32)?;
        cb.store_uint(f as u64, 8)?;
        cb.store_reference(cell.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb08", fmt = "SENDMSG")]
    fn exec_send_message(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mode = ok!(stack.pop_smallint_range(0, 2047));
        let send = (mode & 1024) == 0;
        let mode = mode & !1024;
        if mode >= 256 {
            vm_bail!(IntegerOverflow) //TODO: Range error
        }

        let msg_cell: Rc<Cell> = ok!(stack.pop_cell());

        let msg_cell_cloned = Rc::unwrap_or_clone(msg_cell);
        let owned_slice = OwnedCellSlice::from(msg_cell_cloned.clone());

        let mut cs = owned_slice.apply()?;
        let relaxed_message: BaseMessage<RelaxedMsgInfo, CellSliceParts> =
            OwnedRelaxedMessage::load_from(&mut cs)?;
        let my_addr_value: &RcStackValue = ok!(get_param_from_c7(&st.cr, 8));
        let my_addr = my_addr_value.as_slice();
        let Some(my_addr) = my_addr else {
            vm_bail!(InvalidType {
                expected: StackValueType::Slice,
                actual: StackValueType::Null
            });
        };

        let mut value: BigInt = BigInt::zero();
        let mut have_extra_currencies = false;
        let ihr_disabled;

        let user_fwd_fee: BigInt;
        let user_ihr_fee: BigInt;

        let mut my_addr_sc = my_addr.apply()?;
        let my_wc: i8 = ok!(parse_address_workchain(&mut my_addr_sc));

        let (is_masterchain, is_external, dst_bit_len) = match &relaxed_message.info {
            RelaxedMsgInfo::Int(info) => {
                have_extra_currencies = !info.value.other.is_empty();
                ihr_disabled = info.ihr_disabled;
                user_fwd_fee = BigInt::from(info.fwd_fee.into_inner());
                user_ihr_fee = BigInt::from(info.ihr_fee.into_inner());
                (
                    my_wc == -1 || info.dst.is_masterchain(),
                    false,
                    info.dst.bit_len(),
                )
            }
            RelaxedMsgInfo::ExtOut(info) => {
                ihr_disabled = true;
                user_fwd_fee = BigInt::zero();
                user_ihr_fee = BigInt::zero();
                (
                    false,
                    true,
                    info.dst.as_ref().map(|x| x.bit_len()).unwrap_or(0),
                )
            }
        };

        let message_prices: MsgForwardPrices = ok!(get_message_prices(is_masterchain, &st.cr));
        let max_cells: usize = 1 << 13;

        let mut storage_stat = StorageStat::with_limit(max_cells);
        let mut cs = owned_slice.apply()?;
        cs.skip_first(cs.size_bits(), 0)?;
        storage_stat.add_slice(&cs);

        match is_external {
            true if mode & 128 != 0 => {
                let balances: &[RcStackValue] = ok!(get_balances(&st.cr, 7));

                let Some(balances_value) = balances.first() else {
                    vm_bail!(InvalidType {
                        expected: StackValueType::Int,
                        actual: StackValueType::Null
                    })
                };

                let Some(balance) = balances_value.as_int() else {
                    vm_bail!(InvalidType {
                        expected: StackValueType::Int,
                        actual: balances_value.ty()
                    })
                };

                value = balance.clone();

                let Some(extra_balance_value) = balances.get(1) else {
                    vm_bail!(InvalidType {
                        expected: StackValueType::Int,
                        actual: StackValueType::Null
                    })
                };

                let extra_balances_opt = extra_balance_value.as_cell();
                have_extra_currencies |= extra_balances_opt.is_some();
            }
            true if mode & 64 != 0 => {
                let balances: &[RcStackValue] = ok!(get_balances(&st.cr, 11));
                let Some(balances_value) = balances.first() else {
                    vm_bail!(InvalidType {
                        expected: StackValueType::Int,
                        actual: StackValueType::Null
                    })
                };
                let Some(balance) = balances_value.as_int() else {
                    vm_bail!(InvalidType {
                        expected: StackValueType::Int,
                        actual: balances_value.ty()
                    })
                };
                let Some(extra_balance_value) = balances.get(1) else {
                    vm_bail!(InvalidType {
                        expected: StackValueType::Int,
                        actual: StackValueType::Null
                    })
                };

                let extra_balances_opt = extra_balance_value.as_cell();
                have_extra_currencies |= extra_balances_opt.is_some();
                value.add_assign(balance);
            }
            _ => (),
        };

        let (have_init, mut init_is_ref, init_bit_len, init_refs) = match relaxed_message.init {
            Some(init) => (
                true,
                relaxed_message.layout.unwrap().init_to_cell,
                init.exact_size_const().bits,
                init.exact_size_const().refs,
            ), //TODO: we 100% have layout due to relaxed message parsing
            None => (false, false, 0, 0),
        };

        let body_owned_slice = OwnedCellSlice::from(relaxed_message.body);
        let body_cs = body_owned_slice.apply()?;
        let body_bit_len = body_cs.size_bits();
        let body_refs = body_cs.size_refs();
        let body_is_ref = body_cs.get_bit(0)?;

        let mut fwd_fee = BigInt::zero();
        let mut ihr_fee = BigInt::zero();

        let mut total_cells = storage_stat.stats().cell_count;
        let mut total_bits = storage_stat.stats().bit_count;

        compute_fees(
            ihr_disabled,
            total_bits,
            total_cells,
            &message_prices,
            &mut fwd_fee,
            &mut ihr_fee,
            &user_fwd_fee,
            &user_ihr_fee,
        );

        let my_addr = my_addr.apply()?;

        let bits = msg_root_bits(
            is_external,
            have_init,
            init_is_ref,
            body_is_ref,
            init_bit_len,
            body_bit_len,
            dst_bit_len,
            &message_prices,
            &fwd_fee,
            &ihr_fee,
            &my_addr,
            &value,
        );

        let refs = msg_root_refs(
            is_external,
            have_extra_currencies,
            have_init,
            init_is_ref,
            init_refs,
            body_is_ref,
            body_refs,
        );

        if have_init && !init_is_ref && (bits > 1023 || refs > 4) {
            init_is_ref = true;
            total_cells += 1;
            total_bits += init_bit_len as u64 - 1;

            compute_fees(
                ihr_disabled,
                total_bits,
                total_cells,
                &message_prices,
                &mut fwd_fee,
                &mut ihr_fee,
                &user_fwd_fee,
                &user_ihr_fee,
            );
        };

        let bits = msg_root_bits(
            is_external,
            have_init,
            init_is_ref,
            body_is_ref,
            init_bit_len,
            body_bit_len,
            dst_bit_len,
            &message_prices,
            &fwd_fee,
            &ihr_fee,
            &my_addr,
            &value,
        );

        let refs = msg_root_refs(
            is_external,
            have_extra_currencies,
            have_init,
            init_is_ref,
            init_refs,
            body_is_ref,
            body_refs,
        );

        if !body_is_ref && (bits > 1023 || refs > 4) {
            //body_is_ref = true;
            total_cells += 1;
            total_bits += body_bit_len as u64 - 1;
            compute_fees(
                ihr_disabled,
                total_bits,
                total_cells,
                &message_prices,
                &mut fwd_fee,
                &mut ihr_fee,
                &user_fwd_fee,
                &user_ihr_fee,
            );
        }

        ok!(stack.push_int(fwd_fee + ihr_fee));

        if send {
            let mut cb = CellBuilder::new();
            let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
                vm_bail!(ControlRegisterOutOfRange(5))
            };
            cb.store_reference(actions)?;
            cb.store_uint(0x0ec3c86d, 32)?;
            cb.store_uint(mode as u64, 8)?;
            cb.store_reference(msg_cell_cloned)?;
            let cell = cb.build()?;
            return install_output_actions(&mut st.cr, cell);
        }

        Ok(0)
    }

    #[instr(code = "fbss", range_from = "fb02", range_to = "fb04", fmt = ("{}", s.display()), args(s = ReserveArgs(args)))]
    fn exec_reserve_raw(st: &mut VmState, s: ReserveArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let f = ok!(stack.pop_smallint_range(0, 15));

        let mut cell: Option<Rc<Cell>> = None;
        if s.is_x() {
            cell = ok!(stack.pop_cell_opt());
        }

        let amount: Rc<BigInt> = ok!(stack.pop_int());
        let Some(uamount) = amount.to_u128() else {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: u128::MAX as isize,
                actual: amount.to_string()
            })
        };

        let tokens = Tokens::new(uamount);
        if !tokens.is_valid() {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: Tokens::MAX.into_inner() as isize,
                actual: amount.to_string()
            })
        }

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x36e6b809, 32)?;
        cb.store_uint(f as u64, 8)?;
        tokens.store_into(&mut cb, &mut Cell::empty_context())?;
        if let Some(cell) = cell {
            cb.store_bit_one()?;
            cb.store_reference(cell.as_ref().clone())?;
        } else {
            cb.store_bit_zero()?;
        }

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb04", fmt = "SETCODE")]
    fn exec_set_code(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let code = ok!(stack.pop_cell());
        let mut cb = CellBuilder::new();

        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };

        cb.store_reference(actions)?;
        cb.store_uint(0x36e6b809, 32)?;
        cb.store_reference(code.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb06", fmt = "SETLIBCODE")]
    fn exec_set_lib_code(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mode = ok!(stack.pop_smallint_range(0, 2));
        let code = ok!(stack.pop_cell());

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };

        cb.store_reference(actions)?;
        cb.store_uint(0x26fa1dd4, 32)?;
        cb.store_uint((mode * 2 + 1) as u64, 8)?;
        cb.store_reference(code.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb07", fmt = "CHANGELIB")]
    fn exec_change_lib(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mode = ok!(stack.pop_smallint_range(0, 2));
        let hash: Rc<BigInt> = ok!(stack.pop_int());
        let mut hash_bytes = [0u8; 32];
        if hash_bytes.len() < hash.to_bytes_be().1.len() {
            vm_bail!(IntegerOverflow)
        }
        hash_bytes.copy_from_slice(hash.to_bytes_be().1.as_ref());
        let hash_bytes = HashBytes::from(hash_bytes);

        let mut cb = CellBuilder::new();

        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x26fa1dd4, 32)?;
        cb.store_uint((mode * 2) as u64, 8)?;
        cb.store_u256(&hash_bytes)?;
        install_output_actions(&mut st.cr, cb.build()?)
    }
}

fn msg_root_bits(
    is_external: bool,
    have_init: bool,
    init_is_ref: bool,
    body_is_ref: bool,
    init_bit_len: u16,
    body_bit_len: u16,
    dst_bit_len: u16,
    message_prices: &MsgForwardPrices,
    fwd_fee: &BigInt,
    ihr_fee: &BigInt,
    my_addr: &CellSlice,
    value: &BigInt,
) -> u16 {
    let mut bits = 0;
    if is_external {
        bits = 2 + my_addr.size_bits() + dst_bit_len + 32 + 64;
    } else {
        bits = my_addr.size_bits() + dst_bit_len + stored_tokens_len(value) + 1 + 32 + 64;
        let fwd_fee_first = (fwd_fee * (message_prices.first_frac)) >> 16;
        bits += stored_tokens_len(&fwd_fee.sub(fwd_fee_first));
        bits += stored_tokens_len(&ihr_fee);
    };

    bits += 1;

    if have_init {
        bits += 1;
        bits += if init_is_ref { 0 } else { init_bit_len * 2 - 1 };
    }
    bits += 1;
    bits += if body_is_ref { 0 } else { body_bit_len - 1 };
    bits
}

fn msg_root_refs(
    is_external: bool,
    have_extra_currencies: bool,
    have_init: bool,
    init_is_ref: bool,
    init_refs: u8,
    body_is_ref: bool,
    body_refs: u8,
) -> u8 {
    let mut refs = match (is_external, have_extra_currencies) {
        (true, _) => 0,
        (false, true) => 1,
        (false, false) => 0,
    };

    if have_init {
        refs += if init_is_ref { 1 } else { init_refs };
    }
    refs += if body_is_ref { 1 } else { body_refs };
    refs
}

fn compute_fees(
    ihr_disabled: bool,
    total_bits: u64,
    total_cells: u64,
    message_prices: &MsgForwardPrices,
    fwd_fee: &mut BigInt,
    ihr_fee: &mut BigInt,
    user_fwd_fee: &BigInt,
    user_ihr_fee: &BigInt,
) {
    let fwd_fee_short = message_prices.lump_price
        + (message_prices
            .bit_price
            .mul(total_bits)
            .add(message_prices.cell_price.mul(total_cells))
            .add(0xffff)
            .shr(16)) as u64;

    // Calculate new forward fee
    *fwd_fee = BigInt::from(fwd_fee_short);
    if user_fwd_fee > fwd_fee {
        *fwd_fee = user_fwd_fee.clone();
    }

    // Calculate new IHR fee only if not disabled
    if ihr_disabled {
        *ihr_fee = BigInt::zero();
    } else {
        let ihr_fee_short = fwd_fee_short
            .mul(message_prices.ihr_price_factor as u64)
            .shr(16);
        *ihr_fee = BigInt::from(ihr_fee_short);

        if user_ihr_fee > ihr_fee {
            *ihr_fee = user_ihr_fee.clone();
        }
    }
}

fn stored_tokens_len(x: &BigInt) -> u16 {
    let bits = x.bits();
    4 + ((bits + 7) & !7) as u16
}
fn get_balances(regs: &ControlRegs, index: usize) -> VmResult<&'_ [RcStackValue]> {
    let balance: &RcStackValue = ok!(get_param_from_c7(regs, index));
    let Some(balances) = balance.as_tuple() else {
        vm_bail!(InvalidType {
            expected: StackValueType::Tuple,
            actual: StackValueType::Null
        })
    };
    Ok(balances)
}

fn get_message_prices(is_masterchain: bool, regs: &ControlRegs) -> VmResult<MsgForwardPrices> {
    let config = ok!(get_param_from_c7(regs, 9));

    let Some(config_slice) = config.as_slice() else {
        vm_bail!(InvalidType {
            expected: StackValueType::Slice,
            actual: config.ty()
        })
    };
    let mut config = config_slice.apply()?;
    let config = BlockchainConfig::load_from(&mut config)?;
    let Ok(msg_prices) = config.get_msg_forward_prices(is_masterchain) else {
        vm_bail!(CellError(Error::CellUnderflow))
    };

    Ok(msg_prices)
}

pub fn parse_address_workchain(cs: &mut CellSlice) -> VmResult<i8> {
    let t = cs.load_bit()?;
    if !t {
        vm_bail!(IntegerOutOfRange {
            min: 1,
            max: 1,
            actual: t.to_string()
        })
    }

    let is_var = cs.load_bit()?;
    let anycast = cs.load_bit()?;
    if anycast {
        let depth = SplitDepth::new(load_uint_leq(cs, 30)? as u8)?;
        cs.skip_first(depth.into_bit_len(), 0)?;
    }

    if is_var {
        cs.skip_first(9, 0)?;
        Ok(cs.load_u32()? as i8)
    } else {
        Ok(cs.load_u8()? as i8)
    }
}

pub struct ReserveArgs(u32);
impl ReserveArgs {
    fn is_x(&self) -> bool {
        self.0 & 0b1 != 0
    }

    fn display(&self) -> DisplayReserveArgs {
        DisplayReserveArgs(self.0)
    }
}

pub struct DisplayReserveArgs(u32);
impl std::fmt::Display for DisplayReserveArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args = ReserveArgs(self.0);
        let is_x = if args.is_x() { "X" } else { "" };
        write!(f, "RAWRESERVE{is_x}")
    }
}
fn install_output_actions(regs: &mut ControlRegs, action_head: Cell) -> VmResult<i32> {
    vm_log!("installing an output action");
    regs.set_d(OUTPUT_ACTIONS_IDX, action_head);
    Ok(0)
}

#[cfg(test)]
mod tests {
    use crate::cont::OrdCont;
    use crate::stack::StackValueType::Cont;
    use crate::stack::{RcStackValue, Stack};
    use crate::util::OwnedCellSlice;
    use crate::VmState;
    use anyhow::Context;
    use everscale_types::cell::{Cell, CellBuilder, CellSlice};
    use everscale_types::dict::{Dict, RawDict};
    use everscale_types::models::{
        Account, AccountState, ExtInMsgInfo, GlobalCapabilities, GlobalCapability, Message,
        OwnedMessage, StdAddr,
    };
    use everscale_types::prelude::{Boc, CellFamily, HashBytes, Load, Store};
    use everscale_vm::stack::Tuple;
    use everscale_vm::util::store_int_to_builder;
    use num_bigint::BigInt;
    use std::rc::Rc;
    use std::str::FromStr;
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn send_msg_test() {
        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            SETCP0 DUP IFNOTRET // return if recv_internal
            DUP
            PUSHINT 85143
            EQUAL OVER
            PUSHINT 78748
            EQUAL OR
            // "seqno" and "get_public_key" get-methods
            PUSHCONT {
                PUSHINT 1
                AND
                PUSHCTR c4 CTOS
                LDU 32
                LDU 32
                NIP
                PLDU 256
                CONDSEL
            }
            IFJMP
            // fail unless recv_external
            INC THROWIF 32

            PUSHPOW2 9 LDSLICEX // signature
            DUP
            LDU 32 // subwallet_id
            LDU 32 // valid_until
            LDU 32 // msg_seqno

            NOW
            XCHG s1, s3
            LEQ
            DUMPSTK
            THROWIF 35

            PUSH c4 CTOS
            LDU 32
            LDU 32
            LDU 256
            ENDS

            XCPU s3, s2
            EQUAL
            THROWIFNOT 33

            XCPU s4, s4
            EQUAL
            THROWIFNOT 34

            XCHG s0, s4
            HASHSU
            XC2PU s0, s5, s5
            CHKSIGNU THROWIFNOT 35

            ACCEPT

            PUSHCONT { DUP SREFS }
            PUSHCONT {
                LDU 8
                LDREF
                XCHG s0, s2
                SENDRAWMSG
            }
            WHILE

            ENDS SWAP INC

            NEWC
            STU 32
            STU 32
            STU 256
            ENDC
            POP c4
            "#
        })
        .unwrap();

        let code = OwnedCellSlice::from(code);

        let balance_tuple: Tuple = vec![Rc::new(BigInt::from(10000000000u64)), Stack::make_null()];

        let addr =
            StdAddr::from_str("0:4f4f10cb9a30582792fb3c1e364de5a6fbe6fe04f4167f1f12f83468c767aeb3")
                .unwrap();
        let addr = OwnedCellSlice::from(CellBuilder::build_from(addr).unwrap());

        let c7: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(0x076ef1ea)),
            Rc::new(BigInt::from(0)),                 //actions
            Rc::new(BigInt::from(0)),                 //msgs_sent
            Rc::new(BigInt::from(1732042729)),        //unix_time
            Rc::new(BigInt::from(55364288000000u64)), //block_logical_time
            Rc::new(BigInt::from(55396331000001u64)), // transaction_logical_time
            Rc::new(BigInt::from(0)),                 //rand_seed
            Rc::new(balance_tuple),
            Rc::new(addr),
            Stack::make_null(),
            Rc::new(code.clone()),
        ];

        let c4_data = Boc::decode_base64(
            "te6ccgEBAQEAKgAAUAAAAblLqS2KyLDWxgjLA6yhKJfmGLWfXdvRC34pWEXEek1ncgteNXU=",
        )
        .unwrap();

        let message_cell = Boc::decode_base64("te6ccgEBAgEAqQAB34gAnp4hlzRgsE8l9ng8bJvLTffN/AnoLP4+JfBo0Y7PXWYHO+2B5vPMosfjPalLE/qz0rm+wRn9g9sSu0q4Zwo0Lq5vB/YbhvWObr1T6jLdyEU3xEQ2uSP7sKARmIsEqMbIal1JbFM55wEgAAANyBwBAGhCACeniGXNGCwTyX2eDxsm8tN9838Cegs/j4l8GjRjs9dZodzWUAAAAAAAAAAAAAAAAAAA").unwrap();
        let message = OwnedMessage::load_from(
            &mut OwnedCellSlice::from(message_cell.clone()).apply().unwrap(),
        )
        .unwrap();
        let message_body = OwnedCellSlice::from(message.body);

        let stack: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(1406127106355u64)),
            Rc::new(BigInt::from(0)),
            Rc::new(message_cell),
            Rc::new(message_body),
            Rc::new(BigInt::from(-1)),
        ];

        let mut builder = VmState::builder();
        builder.c7 = Some(vec![Rc::new(c7)]);
        builder.stack = stack;
        builder.code = code;
        let mut vm_state = builder
            .with_gas_base(1000)
            .with_gas_remaining(1000)
            .with_gas_max(u64::MAX)
            .with_debug(TracingOutput::default())
            .build()
            .unwrap();
        vm_state.cr.set(4, Rc::new(c4_data)).unwrap();
        let result = vm_state.run();
        println!("code {result}");
    }

    #[test]
    #[traced_test]
    pub fn e_wallet_send_msg() {
        let code = Boc::decode_base64("te6cckEBBgEA/AABFP8A9KQT9LzyyAsBAgEgAgMABNIwAubycdcBAcAA8nqDCNcY7UTQgwfXAdcLP8j4KM8WI88WyfkAA3HXAQHDAJqDB9cBURO68uBk3oBA1wGAINcBgCDXAVQWdfkQ8qj4I7vyeWa++COBBwiggQPoqFIgvLHydAIgghBM7mRsuuMPAcjL/8s/ye1UBAUAmDAC10zQ+kCDBtcBcdcBeNcB10z4AHCAEASqAhSxyMsFUAXPFlAD+gLLaSLQIc8xIddJoIQJuZgzcAHLAFjPFpcwcQHLABLM4skB+wAAPoIQFp4+EbqOEfgAApMg10qXeNcB1AL7AOjRkzLyPOI+zYS/").unwrap();
        let code = OwnedCellSlice::from(code);

        let balance_tuple: Tuple = vec![Rc::new(BigInt::from(10000000000u64)), Stack::make_null()];

        let addr =
            StdAddr::from_str("0:6301b2c75596e6e569a6d13ae4ec70c94f177ece0be19f968ddce73d44e7afc7")
                .unwrap();
        let addr = OwnedCellSlice::from(CellBuilder::build_from(addr).unwrap());

        let c7: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(0x076ef1ea)),
            Rc::new(BigInt::from(0)),                 //actions
            Rc::new(BigInt::from(0)),                 //msgs_sent
            Rc::new(BigInt::from(1732048342)),        //unix_time
            Rc::new(BigInt::from(55398352000001u64)), //block_logical_time
            Rc::new(BigInt::from(55398317000004u64)), // transaction_logical_time
            Rc::new(BigInt::from(0)),                 //rand_seed
            Rc::new(balance_tuple),
            Rc::new(addr),
            Stack::make_null(),
            Rc::new(code.clone()),
        ];

        let c4_data = Boc::decode_base64(
            "te6ccgEBAQEAKgAAUMiw1sYIywOsoSiX5hi1n13b0Qt+KVhFxHpNZ3ILXjV1AAABk0YeykY=",
        )
        .unwrap();

        let message_cell = Boc::decode_base64("te6ccgEBBAEA0gABRYgAxgNljqstzcrTTaJ1ydjhkp4u/ZwXwz8tG7nOeonPX44MAQHhmt2/xQjjwjfYraY7Tv53Ct8o9OAtI8nD7DFB19TrG7W8wYMxQKtbXuvGvaKFoB9D0lMZwnPpZ1fEBWxaXZgtg/IsNbGCMsDrKEol+YYtZ9d29ELfilYRcR6TWdyC141dQAAAZNGIEb+Zzz2EEzuZGyACAWWADGA2WOqy3NytNNonXJ2OGSni79nBfDPy0buc56ic9fjgAAAAAAAAAAAAAAAHc1lAADgDAAA=").unwrap();
        let message = OwnedMessage::load_from(
            &mut OwnedCellSlice::from(message_cell.clone()).apply().unwrap(),
        )
        .unwrap();
        let message_body = OwnedCellSlice::from(message.body);

        let stack: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(4989195982u64)),
            Rc::new(BigInt::from(0)),
            Rc::new(message_cell),
            Rc::new(message_body),
            Rc::new(BigInt::from(-1)),
        ];

        let mut builder = VmState::builder();
        builder.c7 = Some(vec![Rc::new(c7)]);
        builder.stack = stack;
        builder.code = code;

        let mut vm_state = builder
            .with_gas_base(10000)
            .with_gas_remaining(10000)
            .with_gas_max(u64::MAX)
            .with_debug(TracingOutput::default())
            .build()
            .unwrap();
        vm_state.cr.set(4, Rc::new(c4_data)).unwrap();
        let result = vm_state.run();
        println!("code {result}");
    }

    #[test]
    #[traced_test]
    pub fn jetton() {
        let code = Boc::decode_base64("te6ccgECGgEABQ4AART/APSkE/S88sgLAQIBYgIDAgLLBAUCASAQEQHX0MtDTAwFxsI5EMIAg1yHTHwGCEBeNRRm6kTDhgEDXIfoAMO1E0PoA+kD6QNTU0/8B+GHRUEWhQTT4QchQBvoCUATPFljPFszMy//J7VTg+kD6QDH6ADH0AfoAMfoAATFw+DoC0x8BAdM/ARKBgAdojhkZYOA54tkgUGD+gvABPztRND6APpA+kDU1NP/Afhh0SaCEGQrfQe6jss1NVFhxwXy4EkE+kAh+kQwwADy4U36ANTRINDTHwGCEBeNRRm68uBIgEDXIfoA+kAx+kAx+gAg1wsAmtdLwAEBwAGw8rGRMOJUQxvgOSWCEHvdl9664wIlghAsdrlzuuMCNCQHCAkKAY4hkXKRceL4OSBuk4F4LpEg4iFulDGBfuCRAeJQI6gToHOBBK1w+DygAnD4NhKgAXD4NqBzgQUTghAJZgGAcPg3oLzysCVZfwsB5jUF+gD6QPgo+EEoEDQB2zxvIjD5AHB0yMsCygfL/8nQUAjHBfLgShKhRBRQNvhByFAG+gJQBM8WWM8WzMzL/8ntVPpA0SDXCwHAALOOIsiAEAHLBQHPFnD6AnABy2qCENUydtsByx8BAcs/yYBC+wCRW+IYAdI1XwM0AfpA0gABAdGVyCHPFsmRbeLIgBABywVQBM8WcPoCcAHLaoIQ0XNUAAHLH1AEAcs/I/pEMMAAjp34KPhBEDVBUNs8byIw+QBwdMjLAsoHy//J0BLPFpcxbBJwAcsB4vQAyYBQ+wAYBP6CEGUB81S6jiUwM1FCxwXy4EkC+kDRQAME+EHIUAb6AlAEzxZYzxbMzMv/ye1U4CSCEPuI4Rm6jiQxMwPRUTHHBfLgSYsCQDT4QchQBvoCUATPFljPFszMy//J7VTgJIIQy4YpArrjAjAjghAlCNZquuMCI4IQdDHyIbrjAhA2DA0ODwHAghA7msoAcPsC+Cj4QRA2QVDbPG8iMCD5AHB0yMsCygfL/8iAGAHLBQHPF1j6AgKYWHdQA8trzMyXMAFxWMtqzOLJgBH7AFAFoEMU+EHIUAb6AlAEzxZYzxbMzMv/ye1UGABONDZRRccF8uBJyFADzxbJEDQS+EHIUAb6AlAEzxZYzxbMzMv/ye1UACI2XwMCxwXy4EnU1NEB7VT7BABKM1BCxwXy4EkB0YsCiwJANPhByFAG+gJQBM8WWM8WzMzL/8ntVAAcXwaCENNyFYy63IQP8vACAUgSEwICcRYXAT+10V2omh9AH0gfSBqamn/gPww6IovgnwUfCCJbZ43kUBgCAWoUFQAuq1vtRND6APpA+kDU1NP/Afhh0RAkXwQALqpn7UTQ+gD6QPpA1NTT/wH4YdFfBfhBAVutvPaiaH0AfSB9IGpqaf+A/DDoii+CfBR8IIltnjeRGHyAODpkZYFlA+X/5OhAGACLrxb2omh9AH0gfSBqamn/gPww6L+Z6DbBeDhy69tRTZyXwoO38K5ReQKeK2EZw5RicZ5PRu2PdBPmLHgKOGRlg/oAZKGAQAH2hA9/cCb6RDGr+1MRSUYYBMjLA1AD+gIBzxYBzxbL/yCBAMrIyw8Bzxck+QAl12UlggIBNMjLFxLLD8sPy/+OKQakXAHLCXH5BABScAHL/3H5BACr+yiyUwS5kzQ0I5Ew4iDAICTAALEX5hAjXwMzMyJwA8sJySLIywESGQAU9AD0AMsAyQFvAg==").unwrap();
        let code = OwnedCellSlice::from(code);

        let balance_tuple: Tuple = vec![Rc::new(BigInt::from(1931553923u64)), Stack::make_null()];

        let addr =
            StdAddr::from_str("0:2a0c78148c73416b63250b990efdfbf9d5897bf3b33e2f5498a2fe0617174bb8")
                .unwrap();
        let addr = OwnedCellSlice::from(CellBuilder::build_from(addr).unwrap());

        let c7: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(0x076ef1ea)),
            Rc::new(BigInt::from(0)),                 //actions
            Rc::new(BigInt::from(0)),                 //msgs_sent
            Rc::new(BigInt::from(1733142533)),        //unix_time
            Rc::new(BigInt::from(50899537000013u64)), //block_logical_time
            Rc::new(BigInt::from(50899537000013u64)), // transaction_logical_time
            Rc::new(BigInt::from(0)),                 //rand_seed
            Rc::new(balance_tuple),
            Rc::new(addr.clone()),
            Stack::make_null(),
            //Rc::new(code.clone()),
        ];

        let c4_data = Boc::decode_base64(
            "te6ccgEBBAEA3gACTmE+QBlNGKCvtRVlwuLLP8LwzhcDJNm1TPewFBFqmlIYet7ln0NupwECCEICDvGeG/QPK6SS/KrDhu7KWb9oJ6OFBwjZ/NmttoOrwzYB5mh0dHBzOi8vZ2lzdC5naXRodWJ1c2VyY29udGVudC5jb20vRW1lbHlhbmVua29LLzI3MWMwYWRhMWRlNDJiOTdjNDU1YWM5MzVjOTcyZjQyL3Jhdy9iN2IzMGMzZTk3MGUwNzdlMTFkMDg1Y2M2NzEzYmUDADAzMTU3YzdjYTA4L21ldGFkYXRhLmpzb24=",
        )
            .unwrap();

        let stack: Vec<RcStackValue> = vec![
            Rc::new(addr),
            Rc::new(BigInt::from(103289)),
            //Rc::new(BigInt::from(106029)),
        ];

        let mut builder = VmState::builder();

        let mut vm_state = builder
            .with_c7(vec![Rc::new(c7)])
            .with_stack(stack)
            .with_code(code.clone())
            .with_gas_base(1000000)
            .with_gas_remaining(1000000)
            .with_gas_max(u64::MAX)
            .with_debug(TracingOutput::default())
            .build()
            .unwrap();
        vm_state.cr.set(4, Rc::new(c4_data)).unwrap();
        vm_state
            .cr
            .set(
                3,
                Rc::new(OrdCont::simple(
                    code.clone(),
                    crate::instr::codepage0().id(),
                )),
            )
            .unwrap();

        let result = !vm_state.run();
        println!("code {result}");
    }

    #[test]
    #[traced_test]
    pub fn gas_test() {
        let msg_cell = Boc::decode_base64("te6ccgEBAQEAWwAAsUgAMZM1//wnphAm4e74Ifiao3ipylccMDttQdF26orbI/8ABjJmv/+E9MIE3D3fBD8TVG8VOUrjhgdtqDou3VFbZH/QdzWUAAYUWGAAABZ6pIT8hMDDnIhA").unwrap();
        let new_slice = OwnedCellSlice::new(Cell::empty_cell());

        let account_cell = Boc::decode_base64("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").unwrap();
        let account = read_account(account_cell).unwrap();

        let (code, data) = match account.state {
            AccountState::Active(state) => (state.code.unwrap(), state.data.unwrap()),
            _ => panic!(),
        };

        let code_slice = OwnedCellSlice::from(code);

        let balance_tuple: Tuple = vec![
            Rc::new(BigInt::from(account.balance.tokens.into_inner())),
            Stack::make_null(),
        ];

        let addr = account.address.as_std().unwrap();
        let addr = OwnedCellSlice::from(CellBuilder::build_from(addr).unwrap());

        let c7: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(0x076ef1ea)),
            Rc::new(BigInt::from(0)),                 //actions
            Rc::new(BigInt::from(0)),                 //msgs_sent
            Rc::new(BigInt::from(1733142533)),        //unix_time
            Rc::new(BigInt::from(50899537000013u64)), //block_logical_time
            Rc::new(BigInt::from(50899537000013u64)), // transaction_logical_time
            Rc::new(BigInt::from(0)),                 //rand_seed
            Rc::new(balance_tuple),
            Rc::new(addr.clone()),
            Stack::make_null(),
            //Rc::new(code.clone()),
        ];

        let stack: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(1307493522)),
            Rc::new(BigInt::from(500000000)),
            Rc::new(msg_cell),
            Rc::new(new_slice),
            Rc::new(BigInt::from(0)),
        ];

        let mut builder = VmState::builder();
        let mut vm_state = builder
            .with_c7(vec![Rc::new(c7)])
            .with_stack(stack)
            .with_code(code_slice.clone())
            .with_gas_base(1000000)
            .with_gas_remaining(1000000)
            .with_gas_max(u64::MAX)
            .with_debug(TracingOutput::default())
            .build()
            .unwrap();
        vm_state.cr.set(4, Rc::new(data)).unwrap();
        vm_state
            .cr
            .set(
                3,
                Rc::new(OrdCont::simple(
                    code_slice.clone(),
                    crate::instr::codepage0().id(),
                )),
            )
            .unwrap();

        let result = !vm_state.run();
        println!("code {result}");
    }

    fn read_account(cell: Cell) -> Result<Box<Account>, everscale_types::error::Error> {
        let s = &mut cell.as_slice()?;
        assert!(s.load_bit()?);

        Ok(Box::new(Account {
            address: <_>::load_from(s)?,
            storage_stat: <_>::load_from(s)?,
            last_trans_lt: <_>::load_from(s)?,
            balance: <_>::load_from(s)?,
            state: <_>::load_from(s)?,
            init_code_hash: if s.is_data_empty() {
                None
            } else {
                Some(<_>::load_from(s)?)
            },
        }))
    }

    #[derive(Default)]
    struct TracingOutput {
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
