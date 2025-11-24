use std::rc::Rc;
use std::sync::Arc;

use num_bigint::{BigInt, Sign};
use sha2::Digest;
use tycho_types::error::Error;
use tycho_types::models::{
    BlockchainConfigParams, CurrencyCollection, IntAddr, IntMsgInfo, MsgType, StateInit,
};
use tycho_types::num::Tokens;
use tycho_types::prelude::*;

use crate::error::VmResult;
use crate::saferc::{SafeDelete, SafeRc};
use crate::stack::{RcStackValue, Stack, Tuple};
use crate::util::OwnedCellSlice;

/// Version of a VM context.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum VmVersion {
    Everscale(u32),
    Ton(u32),
}

impl VmVersion {
    pub const LATEST_TON: Self = Self::Ton(12);

    pub fn is_ton<R: std::ops::RangeBounds<u32>>(&self, range: R) -> bool {
        matches!(self, Self::Ton(version) if range.contains(version))
    }

    pub fn require_ton<R: std::ops::RangeBounds<u32>>(&self, range: R) -> VmResult<()> {
        vm_ensure!(self.is_ton(range), InvalidOpcode);
        Ok(())
    }
}

/// Smart Contract Info context.
pub trait SmcInfo {
    fn version(&self) -> VmVersion;

    fn build_c7(&self) -> SafeRc<Tuple>;
}

impl<T: SmcInfo + ?Sized> SmcInfo for &'_ T {
    #[inline]
    fn version(&self) -> VmVersion {
        T::version(self)
    }

    #[inline]
    fn build_c7(&self) -> SafeRc<Tuple> {
        T::build_c7(self)
    }
}

impl<T: SmcInfo + ?Sized> SmcInfo for Box<T> {
    #[inline]
    fn version(&self) -> VmVersion {
        T::version(self)
    }

    #[inline]
    fn build_c7(&self) -> SafeRc<Tuple> {
        T::build_c7(self)
    }
}

impl<T: SmcInfo + ?Sized> SmcInfo for Rc<T> {
    #[inline]
    fn version(&self) -> VmVersion {
        T::version(self)
    }

    #[inline]
    fn build_c7(&self) -> SafeRc<Tuple> {
        T::build_c7(self)
    }
}

impl<T: SmcInfo + ?Sized> SmcInfo for Arc<T> {
    #[inline]
    fn version(&self) -> VmVersion {
        T::version(self)
    }

    #[inline]
    fn build_c7(&self) -> SafeRc<Tuple> {
        T::build_c7(self)
    }
}

impl<T: SmcInfo + SafeDelete + ?Sized> SmcInfo for SafeRc<T> {
    #[inline]
    fn version(&self) -> VmVersion {
        T::version(self)
    }

    #[inline]
    fn build_c7(&self) -> SafeRc<Tuple> {
        T::build_c7(self)
    }
}

/// Common Smart Contract Info.
#[derive(Default, Debug, Clone)]
pub struct SmcInfoBase {
    /// Unix timestamp in seconds.
    pub now: u32,
    /// Block logical time.
    pub block_lt: u64,
    /// Transaction logical time.
    pub tx_lt: u64,
    /// Random seed.
    pub rand_seed: HashBytes,
    /// Account balance.
    pub account_balance: CurrencyCollection,
    /// Account address.
    pub addr: IntAddr,
    /// Blockchain config.
    pub config: Option<BlockchainConfigParams>,
}

impl SmcInfoBase {
    pub const MAGIC: u32 = 0x076ef1ea;

    pub const ACTIONS_IDX: usize = 1;
    pub const MSGS_SENT_IDX: usize = 2;
    pub const UNIX_TIME_IDX: usize = 3;
    pub const BLOCK_LT_IDX: usize = 4;
    pub const TX_LT_IDX: usize = 5;
    pub const RANDSEED_IDX: usize = 6;
    pub const BALANCE_IDX: usize = 7;
    pub const MYADDR_IDX: usize = 8;
    pub const CONFIG_IDX: usize = 9;

    const C7_ITEM_COUNT: usize = 10;

    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_now(mut self, now: u32) -> Self {
        self.now = now;
        self
    }

    pub fn with_block_lt(mut self, block_lt: u64) -> Self {
        self.block_lt = block_lt;
        self
    }

    pub fn with_tx_lt(mut self, tx_lt: u64) -> Self {
        self.tx_lt = tx_lt;
        self
    }

    pub fn with_raw_rand_seed(mut self, raw_rand_seed: HashBytes) -> Self {
        self.rand_seed = raw_rand_seed;
        self
    }

    pub fn with_mixed_rand_seed(mut self, block_seed: &HashBytes, account: &HashBytes) -> Self {
        if *block_seed == HashBytes::ZERO {
            self.rand_seed = HashBytes::ZERO;
        } else {
            let mut hasher = sha2::Sha256::new();
            hasher.update(block_seed.as_array());
            hasher.update(account.as_array());
            self.rand_seed = HashBytes(hasher.finalize().into());
        }
        self
    }

    pub fn with_account_balance(mut self, balance: CurrencyCollection) -> Self {
        self.account_balance = balance;
        self
    }

    pub fn with_account_addr(mut self, addr: IntAddr) -> Self {
        self.addr = addr;
        self
    }

    pub fn with_config(mut self, params: BlockchainConfigParams) -> Self {
        self.config = Some(params);
        self
    }

    pub fn require_ton_v4(self) -> SmcInfoTonV4 {
        SmcInfoTonV4 {
            base: self,
            code: None,
            message_balance: CurrencyCollection::ZERO,
            storage_fees: Tokens::ZERO,
            prev_blocks_info: None,
        }
    }

    fn write_items(&self, items: &mut Tuple) {
        // magic:0x076ef1ea
        items.push(SafeRc::new_dyn_value(BigInt::from(Self::MAGIC)));
        // actions:Integer
        items.push(Stack::make_zero());
        // msgs_sent:Integer
        items.push(Stack::make_zero());
        // unixtime:Integer
        items.push(SafeRc::new_dyn_value(BigInt::from(self.now)));
        // block_lt:Integer
        items.push(SafeRc::new_dyn_value(BigInt::from(self.block_lt)));
        // trans_lt:Integer
        items.push(SafeRc::new_dyn_value(BigInt::from(self.tx_lt)));
        // rand_seed:Integer
        items.push(SafeRc::new_dyn_value(BigInt::from_bytes_be(
            Sign::Plus,
            self.rand_seed.as_slice(),
        )));
        // balance_remaining:[Integer (Maybe Cell)]
        items.push(balance_as_tuple(&self.account_balance).into_dyn_value());
        // myself:MsgAddressInt
        items.push(SafeRc::new_dyn_value(OwnedCellSlice::new_allow_exotic(
            CellBuilder::build_from(&self.addr).unwrap(),
        )));
        // global_config:(Maybe Cell) ] = SmartContractInfo;
        items.push(
            match self
                .config
                .as_ref()
                .and_then(|c| c.as_dict().root().as_ref())
            {
                None => Stack::make_null(),
                Some(config_root) => SafeRc::new_dyn_value(config_root.clone()),
            },
        );
    }
}

impl SmcInfo for SmcInfoBase {
    fn version(&self) -> VmVersion {
        VmVersion::Ton(1)
    }

    fn build_c7(&self) -> SafeRc<Tuple> {
        let mut t1 = Vec::with_capacity(Self::C7_ITEM_COUNT);
        self.write_items(&mut t1);
        SafeRc::new(vec![SafeRc::new_dyn_value(t1)])
    }
}

/// Extended smart contract info for TVM since version 4.
#[derive(Default, Debug, Clone)]
pub struct SmcInfoTonV4 {
    /// Base values.
    pub base: SmcInfoBase,
    /// Smart contract code.
    pub code: Option<Cell>,
    /// Incoming message balance (zero for external messages).
    pub message_balance: CurrencyCollection,
    /// Storage fees collected on the storage phase.
    pub storage_fees: Tokens,
    /// Previous blocks info (raw for now).
    pub prev_blocks_info: Option<SafeRc<Tuple>>,
}

impl SmcInfoTonV4 {
    pub const MYCODE_IDX: usize = 10;
    pub const IN_MSG_VALUE_IDX: usize = 11;
    pub const STORAGE_FEE_IDX: usize = 12;
    pub const PREV_BLOCKS_IDX: usize = 13;

    const C7_ITEM_COUNT: usize = SmcInfoBase::C7_ITEM_COUNT + 4;

    pub fn with_code(mut self, code: Cell) -> Self {
        self.code = Some(code);
        self
    }

    pub fn with_message_balance(mut self, balance: CurrencyCollection) -> Self {
        self.message_balance = balance;
        self
    }

    pub fn with_storage_fees(mut self, storage_fees: Tokens) -> Self {
        self.storage_fees = storage_fees;
        self
    }

    pub fn with_prev_blocks_info(mut self, prev_blocks_info: SafeRc<Tuple>) -> Self {
        self.prev_blocks_info = Some(prev_blocks_info);
        self
    }

    pub fn require_ton_v6(self) -> SmcInfoTonV6 {
        SmcInfoTonV6 {
            base: self,
            unpacked_config: None,
            due_payment: Tokens::ZERO,
        }
    }

    fn write_items(&self, items: &mut Tuple) {
        // ..base:SmartContractInfo
        self.base.write_items(items);
        // code:Cell
        items.push(match self.code.clone() {
            None => Stack::make_null(),
            Some(code) => SafeRc::new_dyn_value(code),
        });
        // in_msg_value:[Integer (Maybe Cell)]
        items.push(balance_as_tuple(&self.message_balance).into_dyn_value());
        // storage_fees:Integer
        items.push(SafeRc::new_dyn_value(BigInt::from(
            self.storage_fees.into_inner(),
        )));
        // [ wc:Integer shard:Integer seqno:Integer root_hash:Integer file_hash:Integer] = BlockId;
        // [ last_mc_blocks:[BlockId...]
        //   prev_key_block:BlockId ] : PrevBlocksInfo
        match self.prev_blocks_info.clone() {
            None => items.push(Stack::make_null()),
            Some(info) => items.push(info.into_dyn_value()),
        }
    }
}

impl SmcInfo for SmcInfoTonV4 {
    fn version(&self) -> VmVersion {
        VmVersion::Ton(4)
    }

    fn build_c7(&self) -> SafeRc<Tuple> {
        let mut t1 = Vec::with_capacity(Self::C7_ITEM_COUNT);
        self.write_items(&mut t1);
        SafeRc::new(vec![SafeRc::new_dyn_value(t1)])
    }
}

/// Extended smart contract info for TVM since version 6.
#[derive(Default, Debug, Clone)]
pub struct SmcInfoTonV6 {
    /// Base values.
    pub base: SmcInfoTonV4,
    /// Unpacked blockchain config.
    pub unpacked_config: Option<SafeRc<Tuple>>,
    /// Storage phase debt.
    pub due_payment: Tokens,
    // TODO: Add `precompiled_gas_usage`.
}

impl SmcInfoTonV6 {
    pub const PARSED_CONFIG_IDX: usize = 14;
    pub const STORAGE_DEBT_IDX: usize = 15;
    pub const PRECOMPILED_GAS_IDX: usize = 16;

    const C7_ITEM_COUNT: usize = SmcInfoTonV4::C7_ITEM_COUNT + 3;

    pub fn unpack_config(
        params: &BlockchainConfigParams,
        now: u32,
    ) -> Result<SafeRc<Tuple>, Error> {
        let get_param = |id| {
            let Some(value) = params.as_dict().get(id)? else {
                return Ok(Stack::make_null());
            };
            Ok(SafeRc::new_dyn_value(OwnedCellSlice::new_allow_exotic(
                value,
            )))
        };

        Ok(SafeRc::new(vec![
            match Self::find_storage_prices(params, now)? {
                None => Stack::make_null(),
                Some(prices) => SafeRc::new_dyn_value(OwnedCellSlice::from(prices)),
            }, // storage_prices
            get_param(19)?, // global_id
            get_param(20)?, // config_mc_gas_prices
            get_param(21)?, // config_gas_prices
            get_param(24)?, // config_mc_fwd_prices
            get_param(25)?, // config_fwd_prices
            get_param(43)?, // size_limits_config
        ]))
    }

    pub fn unpack_config_partial(
        params: &BlockchainConfigParams,
        now: u32,
    ) -> Result<UnpackedConfig, Error> {
        let get_param = |id| params.as_dict().get(id);

        Ok(UnpackedConfig {
            latest_storage_prices: Self::find_storage_prices(params, now)?,
            global_id: get_param(19)?,
            mc_gas_prices: get_param(20)?,
            gas_prices: get_param(21)?,
            mc_fwd_prices: get_param(24)?,
            fwd_prices: get_param(25)?,
            size_limits_config: get_param(43)?,
        })
    }

    fn find_storage_prices(
        params: &BlockchainConfigParams,
        now: u32,
    ) -> Result<Option<CellSliceParts>, Error> {
        let prices = RawDict::<32>::from(params.get_storage_prices()?.into_root());
        for value in prices.values_owned().reversed() {
            let value = value?;

            // First 32 bits of value is unix timestamp.
            let utime_since = value.0.apply_allow_exotic(&value.1).load_u32()?;
            if now < utime_since {
                continue;
            }
            return Ok(Some(value));
        }
        Ok(None)
    }

    pub fn with_unpacked_config(mut self, config: SafeRc<Tuple>) -> Self {
        self.unpacked_config = Some(config);
        self
    }

    pub fn fill_unpacked_config(mut self) -> Result<Self, Error> {
        let Some(params) = &self.base.base.config else {
            return Err(Error::CellUnderflow);
        };
        self.unpacked_config = Some(Self::unpack_config(params, self.base.base.now)?);
        Ok(self)
    }

    pub fn with_due_payment(mut self, due_payment: Tokens) -> Self {
        self.due_payment = due_payment;
        self
    }

    pub fn require_ton_v11(self) -> SmcInfoTonV11 {
        SmcInfoTonV11 {
            base: self,
            in_msg: None,
        }
    }

    fn write_items(&self, items: &mut Tuple) {
        // ..base:SmartContractInfoV4
        self.base.write_items(items);
        // unpacked_config_tuple:[...]
        items.push(match &self.unpacked_config {
            None => Stack::make_null(),
            Some(config) => config.clone().into_dyn_value(),
        });
        // due_payment:Integer
        items.push(SafeRc::new_dyn_value(BigInt::from(
            self.due_payment.into_inner(),
        )));
        // precompiled_gas_usage:Integer
        items.push(Stack::make_null());
    }
}

impl SmcInfo for SmcInfoTonV6 {
    fn version(&self) -> VmVersion {
        VmVersion::Ton(6)
    }

    fn build_c7(&self) -> SafeRc<Tuple> {
        let mut t1 = Vec::with_capacity(Self::C7_ITEM_COUNT);
        self.write_items(&mut t1);
        SafeRc::new(vec![SafeRc::new_dyn_value(t1)])
    }
}

#[derive(Default, Debug, Clone)]
pub struct SmcInfoTonV11 {
    pub base: SmcInfoTonV6,
    pub in_msg: Option<SafeRc<Tuple>>,
}

impl SmcInfoTonV11 {
    pub const IN_MSG_PARAMS_IDX: usize = 17;

    const C7_ITEM_COUNT: usize = SmcInfoTonV6::C7_ITEM_COUNT + 1;

    pub fn unpack_in_msg_partial(
        msg_root: Cell,
        remaining_value: Option<CurrencyCollection>,
    ) -> Result<Option<UnpackedInMsgSmcInfo>, Error> {
        fn src_addr_slice_range(mut cs: CellSlice<'_>) -> Result<CellSliceRange, Error> {
            // Skip flags.
            cs.skip_first(3, 0)?;

            // Read `src`.
            let mut addr_slice = cs;
            IntAddr::load_from(&mut cs)?;

            // Leave only a `src` range in the `addr_slice`.
            addr_slice.skip_last(cs.size_bits(), cs.size_refs())?;

            Ok(addr_slice.range())
        }

        let mut cs = msg_root.as_slice()?;
        let src_addr_slice;
        let info = match MsgType::load_from(&mut cs)? {
            MsgType::Int => {
                src_addr_slice = src_addr_slice_range(cs)?;
                IntMsgInfo::load_from(&mut cs)?
            }
            MsgType::ExtIn | MsgType::ExtOut => return Ok(None),
        };

        let state_init = if cs.load_bit()? {
            Some(if cs.load_bit()? {
                cs.load_reference_cloned()?
            } else {
                let mut state_init_cs = cs;
                StateInit::load_from(&mut cs)?;
                state_init_cs.skip_last(cs.size_bits(), cs.size_refs())?;
                CellBuilder::build_from(state_init_cs)?
            })
        } else {
            None
        };

        Ok(Some(UnpackedInMsgSmcInfo {
            bounce: info.bounce,
            bounced: info.bounced,
            src_addr: (src_addr_slice, msg_root).into(),
            fwd_fee: info.fwd_fee,
            created_lt: info.created_lt,
            created_at: info.created_at,
            original_value: info.value.tokens,
            remaining_value: remaining_value.unwrap_or(info.value),
            state_init,
        }))
    }

    pub fn with_unpacked_in_msg(mut self, in_msg: Option<SafeRc<Tuple>>) -> Self {
        self.in_msg = in_msg;
        self
    }

    #[inline]
    fn write_items(&self, items: &mut Tuple) {
        // ..base:SmcInfoTonV6
        self.base.write_items(items);
        // in_msg_params:[...]
        items.push(
            match &self.in_msg {
                Some(message) => message.clone(),
                None => UnpackedInMsgSmcInfo::empty_msg_tuple(),
            }
            .into_dyn_value(),
        );
    }
}

impl SmcInfo for SmcInfoTonV11 {
    fn version(&self) -> VmVersion {
        VmVersion::Ton(11)
    }

    fn build_c7(&self) -> SafeRc<Tuple> {
        let mut t1 = Vec::with_capacity(Self::C7_ITEM_COUNT);
        self.write_items(&mut t1);
        SafeRc::new(vec![SafeRc::new_dyn_value(t1)])
    }
}

/// Unpacked config params, ready to be used in [`SmcInfoTonV6::with_unpacked_config`].
///
/// A `Send + Sync` alternative of C7 [`SafeRc<Tuple>`] at the cost of vec allocation.
/// Can be shared between execution groups in multiple threads.
#[derive(Clone)]
pub struct UnpackedConfig {
    pub latest_storage_prices: Option<CellSliceParts>,
    pub global_id: Option<Cell>,
    pub mc_gas_prices: Option<Cell>,
    pub gas_prices: Option<Cell>,
    pub mc_fwd_prices: Option<Cell>,
    pub fwd_prices: Option<Cell>,
    pub size_limits_config: Option<Cell>,
}

impl UnpackedConfig {
    pub fn into_tuple(self) -> SafeRc<Tuple> {
        SafeRc::new(vec![
            Self::slice_or_null(self.latest_storage_prices),
            Self::slice_or_null(self.global_id),
            Self::slice_or_null(self.mc_gas_prices),
            Self::slice_or_null(self.gas_prices),
            Self::slice_or_null(self.mc_fwd_prices),
            Self::slice_or_null(self.fwd_prices),
            Self::slice_or_null(self.size_limits_config),
        ])
    }

    pub fn as_tuple(&self) -> SafeRc<Tuple> {
        self.clone().into_tuple()
    }

    fn slice_or_null<T>(slice: Option<T>) -> RcStackValue
    where
        T: IntoSliceUnchecked,
    {
        match slice {
            None => Stack::make_null(),
            Some(slice) => SafeRc::new_dyn_value(slice.into_slice_unchecked()),
        }
    }
}

trait IntoSliceUnchecked {
    fn into_slice_unchecked(self) -> OwnedCellSlice;
}

impl IntoSliceUnchecked for Cell {
    #[inline]
    fn into_slice_unchecked(self) -> OwnedCellSlice {
        OwnedCellSlice::new_allow_exotic(self)
    }
}

impl IntoSliceUnchecked for CellSliceParts {
    #[inline]
    fn into_slice_unchecked(self) -> OwnedCellSlice {
        OwnedCellSlice::from(self)
    }
}

/// Internal message parts.
pub struct UnpackedInMsgSmcInfo {
    pub bounce: bool,
    pub bounced: bool,
    pub src_addr: OwnedCellSlice,
    pub fwd_fee: Tokens,
    pub created_lt: u64,
    pub created_at: u32,
    pub original_value: Tokens,
    pub remaining_value: CurrencyCollection,
    pub state_init: Option<Cell>,
}

impl Default for UnpackedInMsgSmcInfo {
    fn default() -> Self {
        Self {
            bounce: false,
            bounced: false,
            src_addr: addr_none_slice(),
            fwd_fee: Tokens::ZERO,
            created_lt: 0,
            created_at: 0,
            original_value: Tokens::ZERO,
            remaining_value: CurrencyCollection::ZERO,
            state_init: None,
        }
    }
}

impl UnpackedInMsgSmcInfo {
    pub fn empty_msg_tuple() -> SafeRc<Tuple> {
        thread_local! {
            static TUPLE: SafeRc<Tuple> = {
                SafeRc::new(tuple![
                    int 0, // bounce
                    int 0, // bounced
                    raw UnpackedInMsgSmcInfo::addr_none_slice(),
                    int 0, // fwd fee
                    int 0, // created_lt
                    int 0, // created_at
                    int 0, // original value
                    int 0, // value
                    null,  // value extra
                    null,  // state_init
                ])
            }
        }

        TUPLE.with(Clone::clone)
    }

    pub fn into_tuple(self) -> SafeRc<Tuple> {
        SafeRc::new(tuple![
            raw Stack::make_bool(self.bounce),
            raw Stack::make_bool(self.bounced),
            slice self.src_addr,
            int self.fwd_fee,
            int self.created_lt,
            int self.created_at,
            int self.original_value,
            int self.remaining_value.tokens,
            raw match self.remaining_value.other.into_dict().into_root() {
                Some(root) => SafeRc::new_dyn_value(root),
                None => Stack::make_null(),
            },
            raw match self.state_init {
                Some(root) => SafeRc::new_dyn_value(root),
                None => Stack::make_null(),
            },
        ])
    }

    pub fn addr_none_slice() -> RcStackValue {
        thread_local! {
            static ADDR_NONE: RcStackValue = SafeRc::new_dyn_value(addr_none_slice());
        }

        ADDR_NONE.with(SafeRc::clone)
    }
}

fn addr_none_slice() -> OwnedCellSlice {
    let mut addr_none = CellBuilder::new();
    addr_none.store_zeros(2).unwrap();
    OwnedCellSlice::from(CellSliceParts::from(addr_none.build().unwrap()))
}

/// Custom-built Smart Contract Info.
pub struct CustomSmcInfo {
    pub version: VmVersion,
    pub c7: SafeRc<Tuple>,
}

impl SmcInfo for CustomSmcInfo {
    fn version(&self) -> VmVersion {
        self.version
    }

    fn build_c7(&self) -> SafeRc<Tuple> {
        self.c7.clone()
    }
}

fn balance_as_tuple(balance: &CurrencyCollection) -> SafeRc<Tuple> {
    SafeRc::new(vec![
        SafeRc::new_dyn_value(BigInt::from(balance.tokens.into_inner())),
        match balance.other.as_dict().root() {
            None => Stack::make_null(),
            Some(cell) => SafeRc::new_dyn_value(cell.clone()),
        },
    ])
}
