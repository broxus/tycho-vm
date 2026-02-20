use num_bigint::BigInt;
use tycho_types::crc::crc_16;
use tycho_types::models::{
    Account, AccountState, BlockchainConfigParams, CurrencyCollection, ExtInMsgInfo, IntAddr,
    IntMsgInfo, LibDescr, MsgInfo, MsgType, OwnedMessage, StdAddr,
};
use tycho_types::num::Tokens;
use tycho_types::prelude::*;

use crate::{
    BehaviourModifiers, CommittedState, GasParams, RcStackValue, SafeRc, SmcInfoBase, Stack,
    UnpackedInMsgSmcInfo, VmStateBuilder,
};

pub trait VmGetterMethodId {
    fn as_getter_method_id(&self) -> u32;
}

impl<T: VmGetterMethodId + ?Sized> VmGetterMethodId for &T {
    fn as_getter_method_id(&self) -> u32 {
        T::as_getter_method_id(*self)
    }
}

impl<T: VmGetterMethodId + ?Sized> VmGetterMethodId for &mut T {
    fn as_getter_method_id(&self) -> u32 {
        T::as_getter_method_id(*self)
    }
}

impl VmGetterMethodId for u32 {
    fn as_getter_method_id(&self) -> u32 {
        *self
    }
}

impl VmGetterMethodId for str {
    fn as_getter_method_id(&self) -> u32 {
        let crc = crc_16(self.as_bytes());
        crc as u32 | 0x10000
    }
}

pub struct VmCaller {
    pub libraries: Dict<HashBytes, LibDescr>,
    pub behaviour_modifiers: BehaviourModifiers,
    pub config: BlockchainConfigParams,
}

impl VmCaller {
    const MAX_GAS: u64 = 1_000_000;
    const BASE_GAS_PRICE: u64 = 1000 << 16;

    pub fn call_with_external_message_body(
        &self,
        account: &Account,
        body: Cell,
    ) -> Result<VmMessageOutput, VmMessageError> {
        self.call_with_external_message_body_ext(account, body, &Default::default())
    }

    pub fn call_with_external_message_body_ext(
        &self,
        account: &Account,
        body: Cell,
        args: &VmMessageArgs,
    ) -> Result<VmMessageOutput, VmMessageError> {
        let msg = build_external_message(&account.address, body)
            .map_err(VmMessageError::InvalidMessage)?;
        self.call_with_message_ext(account, msg, args)
    }

    pub fn call_with_internal_message_body(
        &self,
        account: &Account,
        amount: CurrencyCollection,
        body: Cell,
    ) -> Result<VmMessageOutput, VmMessageError> {
        self.call_with_internal_message_body_ext(account, amount, body, &Default::default())
    }

    pub fn call_with_internal_message_body_ext(
        &self,
        account: &Account,
        amount: CurrencyCollection,
        body: Cell,
        args: &VmMessageArgs,
    ) -> Result<VmMessageOutput, VmMessageError> {
        let msg = build_internal_message(&account.address, amount, body)
            .map_err(VmMessageError::InvalidMessage)?;
        self.call_with_message_ext(account, msg, args)
    }

    pub fn call_with_message(
        &self,
        account: &Account,
        msg: Cell,
    ) -> Result<VmMessageOutput, VmMessageError> {
        self.call_with_message_ext(account, msg, &Default::default())
    }

    pub fn call_with_message_ext(
        &self,
        account: &Account,
        msg: Cell,
        args: &VmMessageArgs,
    ) -> Result<VmMessageOutput, VmMessageError> {
        let state = match &account.state {
            AccountState::Active(state_init) => state_init,
            _ => return Err(VmMessageError::NoCode),
        };
        let code = state.code.clone().ok_or(VmMessageError::NoCode)?;

        let parsed = msg
            .parse::<OwnedMessage>()
            .map_err(VmMessageError::InvalidMessage)?;

        let msg_lt;
        let selector;
        let message_balance;
        let unpacked_in_msg;
        match &parsed.info {
            MsgInfo::ExtIn(_) => {
                msg_lt = 0;
                selector = -1;
                message_balance = CurrencyCollection::ZERO;
                unpacked_in_msg = None;
            }
            MsgInfo::Int(info) => {
                let src_addr_slice =
                    load_int_msg_src_addr(&msg).map_err(VmMessageError::InvalidMessage)?;

                msg_lt = info.created_lt;
                selector = 0;
                message_balance = info.value.clone();
                unpacked_in_msg = Some(
                    UnpackedInMsgSmcInfo {
                        bounce: info.bounce,
                        bounced: info.bounced,
                        src_addr: src_addr_slice.into(),
                        fwd_fee: info.fwd_fee,
                        created_lt: info.created_lt,
                        created_at: info.created_at,
                        original_value: info.value.tokens,
                        remaining_value: info.value.clone(),
                        state_init: parsed
                            .init
                            .as_ref()
                            .map(CellBuilder::build_from)
                            .transpose()
                            .map_err(VmMessageError::InvalidMessage)?,
                    }
                    .into_tuple(),
                );
            }
            MsgInfo::ExtOut(_) => return Err(VmMessageError::ExtOut),
        }

        let balance = args
            .override_balance
            .clone()
            .unwrap_or_else(|| account.balance.clone());

        let stack = Stack {
            items: tuple![
                int balance.tokens,
                int message_balance.tokens,
                cell msg,
                slice parsed.body,
                int selector,
            ],
        };

        let gas_params = args.override_gas_params.unwrap_or_else(|| {
            let (limit, credit) = if selector == 0 {
                let message_balance =
                    u64::try_from(message_balance.tokens.into_inner()).unwrap_or(u64::MAX);
                (message_balance.saturating_mul(1000), 0)
            } else {
                (0, 10000)
            };

            GasParams {
                max: Self::MAX_GAS,
                limit,
                credit,
                price: Self::BASE_GAS_PRICE,
            }
        });

        let address_hash = match &account.address {
            IntAddr::Std(addr) => addr.address,
            IntAddr::Var(_) => HashBytes::ZERO,
        };

        let lt = std::cmp::max(account.last_trans_lt, msg_lt);
        let smc_info = SmcInfoBase::new()
            .with_now(args.now)
            .with_block_lt(lt)
            .with_tx_lt(lt)
            .with_mixed_rand_seed(&args.rand_seed, &address_hash)
            .with_account_balance(account.balance.clone())
            .with_account_addr(account.address.clone())
            .with_config(self.config.clone())
            .require_ton_v4()
            .with_code(code.clone())
            .with_message_balance(message_balance)
            .require_ton_v6()
            .fill_unpacked_config()
            .map_err(VmMessageError::InvalidConfig)?
            .require_ton_v11()
            .with_unpacked_in_msg(unpacked_in_msg);

        let data = state.data.clone().unwrap_or_default();

        // TODO: Also use libraries from the message here.
        let libraries = (&state.libraries, &self.libraries);
        let mut vm = VmStateBuilder::new()
            .with_smc_info(smc_info)
            .with_code(code)
            .with_data(data)
            .with_libraries(&libraries)
            .with_init_selector(false)
            .with_raw_stack(SafeRc::new(stack))
            .with_gas(gas_params)
            .with_modifiers(self.behaviour_modifiers)
            .build();

        let exit_code = !vm.run();

        let accepted = vm.gas.credit() == 0;
        let success = accepted && vm.committed_state.is_some();

        Ok(VmMessageOutput {
            exit_code,
            stack: vm.stack.items.clone(),
            success,
            gas_used: vm.gas.consumed(),
            missing_library: vm.gas.missing_library(),

            accepted,
            commited: vm.committed_state.filter(|_| accepted),
        })
    }

    pub fn call_getter<T: VmGetterMethodId>(
        &self,
        account: &Account,
        method: T,
        stack: Vec<RcStackValue>,
    ) -> Result<VmGetterOutput, VmGetterError> {
        self.call_getter_impl(
            account,
            method.as_getter_method_id(),
            stack,
            &Default::default(),
        )
    }

    #[inline]
    pub fn call_getter_ext<T: VmGetterMethodId>(
        &self,
        account: &Account,
        method: T,
        stack: Vec<RcStackValue>,
        args: &VmGetterArgs,
    ) -> Result<VmGetterOutput, VmGetterError> {
        self.call_getter_impl(account, method.as_getter_method_id(), stack, args)
    }

    fn call_getter_impl(
        &self,
        account: &Account,
        method_id: u32,
        mut stack: Vec<RcStackValue>,
        args: &VmGetterArgs,
    ) -> Result<VmGetterOutput, VmGetterError> {
        let state = match &account.state {
            AccountState::Active(state_init) => state_init,
            _ => return Err(VmGetterError::NoCode),
        };
        let code = state.code.clone().ok_or(VmGetterError::NoCode)?;

        stack.push(RcStackValue::new_dyn_value(BigInt::from(method_id)));

        let address_hash = match &account.address {
            IntAddr::Std(addr) => addr.address,
            IntAddr::Var(_) => HashBytes::ZERO,
        };

        let smc_info = SmcInfoBase::new()
            .with_now(args.now)
            .with_block_lt(account.last_trans_lt)
            .with_tx_lt(account.last_trans_lt)
            .with_mixed_rand_seed(&args.rand_seed, &address_hash)
            .with_account_balance(account.balance.clone())
            .with_account_addr(account.address.clone())
            .with_config(self.config.clone())
            .require_ton_v4()
            .with_code(code.clone())
            .require_ton_v6()
            .fill_unpacked_config()
            .map_err(VmGetterError::InvalidConfig)?
            .require_ton_v11();

        let data = state.data.clone().unwrap_or_default();

        let libraries = (&state.libraries, &self.libraries);
        let mut vm = VmStateBuilder::new()
            .with_smc_info(smc_info)
            .with_code(code)
            .with_data(data)
            .with_libraries(&libraries)
            .with_init_selector(false)
            .with_stack(stack)
            .with_gas(args.gas_params)
            .with_modifiers(self.behaviour_modifiers)
            .build();

        let exit_code = !vm.run();

        Ok(VmGetterOutput {
            exit_code,
            stack: vm.stack.items.clone(),
            success: exit_code == 0 || exit_code == 1,
            gas_used: vm.gas.consumed(),
            missing_library: vm.gas.missing_library(),
        })
    }
}

fn load_int_msg_src_addr(msg_root: &Cell) -> Result<CellSliceParts, tycho_types::error::Error> {
    let mut cs = msg_root.as_slice()?;
    if MsgType::load_from(&mut cs)? != MsgType::Int {
        return Err(tycho_types::error::Error::InvalidTag);
    }

    // Skip flags.
    cs.skip_first(3, 0)?;
    let mut addr_slice = cs;
    // Read `src`.
    IntAddr::load_from(&mut cs)?;
    addr_slice.skip_last(cs.size_bits(), cs.size_refs())?;
    let range = addr_slice.range();

    Ok((range, msg_root.clone()))
}

fn build_internal_message(
    address: &IntAddr,
    amount: CurrencyCollection,
    body: Cell,
) -> Result<Cell, tycho_types::error::Error> {
    CellBuilder::build_from(OwnedMessage {
        info: MsgInfo::Int(IntMsgInfo {
            ihr_disabled: true,
            bounce: true,
            bounced: false,
            src: StdAddr::default().into(),
            dst: address.clone(),
            value: amount,
            extra_flags: Default::default(),
            fwd_fee: Tokens::ZERO,
            created_lt: 0,
            created_at: 0,
        }),
        init: None,
        body: body.into(),
        layout: None,
    })
}

fn build_external_message(
    address: &IntAddr,
    body: Cell,
) -> Result<Cell, tycho_types::error::Error> {
    CellBuilder::build_from(OwnedMessage {
        info: MsgInfo::ExtIn(ExtInMsgInfo {
            src: None,
            dst: address.clone(),
            import_fee: Tokens::ZERO,
        }),
        init: None,
        body: body.into(),
        layout: None,
    })
}

#[derive(Debug)]
#[non_exhaustive]
pub struct VmMessageArgs {
    /// Current unix timestamp.
    ///
    /// Default: current timestamp on non-wasm platforms and `0` on wasm.
    pub now: u32,
    /// Random seed.
    ///
    /// Default: [`HashBytes::ZERO`].
    pub rand_seed: HashBytes,
    /// Custom gas limits for execution.
    ///
    /// Default: max gas.
    pub override_gas_params: Option<GasParams>,
    /// Set custom account balance.
    ///
    /// Default: `None`.
    pub override_balance: Option<CurrencyCollection>,
}

impl Default for VmMessageArgs {
    fn default() -> Self {
        Self {
            #[cfg(target_arch = "wasm32")]
            now: 0,
            #[cfg(not(target_arch = "wasm32"))]
            now: std::time::SystemTime::now()
                .duration_since(std::time::SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_secs() as u32,
            rand_seed: HashBytes::ZERO,
            override_gas_params: None,
            override_balance: None,
        }
    }
}

#[derive(Debug)]
pub struct VmMessageOutput {
    pub exit_code: i32,
    pub stack: Vec<RcStackValue>,
    pub success: bool,
    pub gas_used: u64,
    pub missing_library: Option<HashBytes>,

    pub accepted: bool,
    pub commited: Option<CommittedState>,
}

#[derive(Debug, thiserror::Error)]
pub enum VmMessageError {
    #[error("external outbound message cannot be executed")]
    ExtOut,
    #[error("invalid message: {0}")]
    InvalidMessage(tycho_types::error::Error),
    #[error("invalid config: {0}")]
    InvalidConfig(tycho_types::error::Error),
    #[error("account has no code")]
    NoCode,
}

#[derive(Debug)]
#[non_exhaustive]
pub struct VmGetterArgs {
    /// Current unix timestamp.
    ///
    /// Default: current timestamp on non-wasm platforms and `0` on wasm.
    pub now: u32,
    /// Random seed.
    ///
    /// Default: [`HashBytes::ZERO`].
    pub rand_seed: HashBytes,
    /// Gas limits for execution.
    ///
    /// Default: [`GasParams::getter`]
    pub gas_params: GasParams,
}

impl Default for VmGetterArgs {
    fn default() -> Self {
        Self {
            #[cfg(target_arch = "wasm32")]
            now: 0,
            #[cfg(not(target_arch = "wasm32"))]
            now: std::time::SystemTime::now()
                .duration_since(std::time::SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_secs() as u32,
            rand_seed: HashBytes::ZERO,
            gas_params: GasParams::getter(),
        }
    }
}

#[derive(Debug)]
pub struct VmGetterOutput {
    pub exit_code: i32,
    pub stack: Vec<RcStackValue>,
    pub success: bool,
    pub gas_used: u64,
    pub missing_library: Option<HashBytes>,
}

#[derive(Debug, thiserror::Error)]
pub enum VmGetterError {
    #[error("account has no code")]
    NoCode,
    #[error("invalid config: {0}")]
    InvalidConfig(tycho_types::error::Error),
}
