use anyhow::{Context, Result};
use everscale_types::cell::Lazy;
use everscale_types::dict;
use everscale_types::error::Error;
use everscale_types::models::{
    Account, AccountState, AccountStatus, CurrencyCollection, HashUpdate, IntAddr, LibDescr,
    Message, OwnedMessage, ShardAccount, SimpleLib, StdAddr, StorageInfo, StorageUsed, TickTock,
    Transaction, TxInfo,
};
use everscale_types::num::{Tokens, Uint15, VarUint56};
use everscale_types::prelude::*;

pub use self::config::ParsedConfig;
pub use self::error::{TxError, TxResult};
use self::util::new_varuint56_truncate;
pub use self::util::{ExtStorageStat, OwnedExtStorageStat, StorageStatLimits};

mod config;
mod error;
mod util;

pub mod phase {
    pub use self::action::{ActionPhaseContext, ActionPhaseFull};
    pub use self::bounce::BouncePhaseContext;
    pub use self::compute::{ComputePhaseContext, ComputePhaseFull, TransactionInput};
    pub use self::receive::{MsgStateInit, ReceivedMessage};
    pub use self::storage::StoragePhaseContext;

    mod action;
    mod bounce;
    mod compute;
    mod credit;
    mod receive;
    mod storage;
}

mod tx {
    mod ordinary;
    mod ticktock;
}

/// Transaction executor.
pub struct Executor<'a> {
    params: &'a ExecutorParams,
    config: &'a ParsedConfig,
    min_lt: u64,
    override_special: Option<bool>,
}

impl<'a> Executor<'a> {
    pub fn new(params: &'a ExecutorParams, config: &'a ParsedConfig) -> Self {
        Self {
            params,
            config,
            min_lt: 0,
            override_special: None,
        }
    }

    pub fn with_min_lt(mut self, min_lt: u64) -> Self {
        self.set_min_lt(min_lt);
        self
    }

    pub fn set_min_lt(&mut self, min_lt: u64) {
        self.min_lt = min_lt;
    }

    pub fn override_special(mut self, is_special: bool) -> Self {
        self.override_special = Some(is_special);
        self
    }

    pub fn begin_ordinary<'s, M>(
        &self,
        address: &StdAddr,
        is_external: bool,
        msg: M,
        state: &'s ShardAccount,
    ) -> TxResult<UncommitedTransaction<'a, 's>>
    where
        M: LoadMessage,
    {
        let msg_root = msg.load_message_root()?;

        let account = state.load_account()?;
        let mut exec = self.begin(address, account)?;
        let info = exec.run_ordinary_transaction(is_external, msg_root.clone())?;

        UncommitedTransaction::with_info(exec, state, Some(msg_root), info).map_err(TxError::Fatal)
    }

    pub fn begin_tick_tock<'s>(
        &self,
        address: &StdAddr,
        kind: TickTock,
        state: &'s ShardAccount,
    ) -> TxResult<UncommitedTransaction<'a, 's>> {
        let account = state.load_account()?;
        let mut exec = self.begin(address, account)?;
        let info = exec.run_tick_tock_transaction(kind)?;

        UncommitedTransaction::with_info(exec, state, None, info).map_err(TxError::Fatal)
    }

    pub fn begin(&self, address: &StdAddr, account: Option<Account>) -> Result<ExecutorState<'a>> {
        let is_special = self
            .override_special
            .unwrap_or_else(|| self.config.is_special(address));

        let acc_address;
        let acc_storage_stat;
        let acc_balance;
        let acc_state;
        let orig_status;
        let end_status;
        let start_lt;
        match account {
            Some(acc) => {
                acc_address = 'addr: {
                    if let IntAddr::Std(acc_addr) = acc.address {
                        if acc_addr == *address {
                            break 'addr acc_addr;
                        }
                    }
                    anyhow::bail!("account address mismatch");
                };
                acc_storage_stat = acc.storage_stat;
                acc_balance = acc.balance;
                acc_state = acc.state;
                orig_status = acc_state.status();
                end_status = orig_status;
                start_lt = std::cmp::max(self.min_lt, acc.last_trans_lt);
            }
            None => {
                acc_address = address.clone();
                acc_storage_stat = StorageInfo {
                    used: StorageUsed::ZERO,
                    last_paid: 0,
                    due_payment: None,
                };
                acc_balance = CurrencyCollection::ZERO;
                acc_state = AccountState::Uninit;
                orig_status = AccountStatus::NotExists;
                end_status = AccountStatus::Uninit;
                start_lt = self.min_lt;
            }
        };

        Ok(ExecutorState {
            params: self.params,
            config: self.config,
            is_special,
            address: acc_address,
            storage_stat: acc_storage_stat,
            balance: acc_balance,
            state: acc_state,
            orig_status,
            end_status,
            start_lt,
            end_lt: start_lt + 1,
            out_msgs: Vec::new(),
            total_fees: Tokens::ZERO,
            burned: Tokens::ZERO,
            cached_storage_stat: None,
        })
    }
}

/// Shared state for executor phases.
pub struct ExecutorState<'a> {
    pub params: &'a ExecutorParams,
    pub config: &'a ParsedConfig,

    pub is_special: bool,

    pub address: StdAddr,
    pub storage_stat: StorageInfo,
    pub balance: CurrencyCollection,
    pub state: AccountState,

    pub orig_status: AccountStatus,
    pub end_status: AccountStatus,
    pub start_lt: u64,
    pub end_lt: u64,

    pub out_msgs: Vec<Lazy<OwnedMessage>>,
    pub total_fees: Tokens,

    pub burned: Tokens,

    pub cached_storage_stat: Option<OwnedExtStorageStat>,
}

#[cfg(test)]
impl<'a> ExecutorState<'a> {
    pub(crate) fn new_non_existent(
        params: &'a ExecutorParams,
        config: &'a impl AsRef<ParsedConfig>,
        address: &StdAddr,
    ) -> Self {
        Self {
            params,
            config: config.as_ref(),
            is_special: false,
            address: address.clone(),
            storage_stat: Default::default(),
            balance: CurrencyCollection::ZERO,
            state: AccountState::Uninit,
            orig_status: AccountStatus::NotExists,
            end_status: AccountStatus::Uninit,
            start_lt: 0,
            end_lt: 1,
            out_msgs: Vec::new(),
            total_fees: Tokens::ZERO,
            burned: Tokens::ZERO,
            cached_storage_stat: None,
        }
    }

    pub(crate) fn new_uninit(
        params: &'a ExecutorParams,
        config: &'a impl AsRef<ParsedConfig>,
        address: &StdAddr,
        balance: impl Into<CurrencyCollection>,
    ) -> Self {
        let mut res = Self::new_non_existent(params, config, address);
        res.balance = balance.into();
        res.orig_status = AccountStatus::Uninit;
        res
    }

    pub(crate) fn new_frozen(
        params: &'a ExecutorParams,
        config: &'a impl AsRef<ParsedConfig>,
        address: &StdAddr,
        balance: impl Into<CurrencyCollection>,
        state_hash: HashBytes,
    ) -> Self {
        let mut res = Self::new_non_existent(params, config, address);
        res.balance = balance.into();
        res.state = AccountState::Frozen(state_hash);
        res.orig_status = AccountStatus::Frozen;
        res.end_status = AccountStatus::Frozen;
        res
    }

    pub(crate) fn new_active(
        params: &'a ExecutorParams,
        config: &'a impl AsRef<ParsedConfig>,
        address: &StdAddr,
        balance: impl Into<CurrencyCollection>,
        data: Cell,
        code_boc: impl AsRef<[u8]>,
    ) -> Self {
        use everscale_types::models::StateInit;

        let mut res = Self::new_non_existent(params, config, address);
        res.balance = balance.into();
        res.state = AccountState::Active(StateInit {
            split_depth: None,
            special: None,
            code: Some(Boc::decode(code_boc).unwrap()),
            data: Some(data),
            libraries: Dict::new(),
        });
        res.orig_status = AccountStatus::Active;
        res.end_status = AccountStatus::Active;
        res
    }
}

/// Executor configuration parameters.
#[derive(Default)]
pub struct ExecutorParams {
    /// Public libraries from the referenced masterchain state.
    pub libraries: Dict<HashBytes, LibDescr>,
    /// Rand seed of the block.
    pub rand_seed: HashBytes,
    /// Unix timestamp in seconds of the block.
    pub block_unixtime: u32,
    /// Logical time of the block.
    pub block_lt: u64,
    /// VM behaviour modifiers.
    pub vm_modifiers: tycho_vm::BehaviourModifiers,
    /// Prevent [`Frozen`] accounts from being deleted
    /// when their storage due is too high.
    ///
    /// [`Frozen`]: everscale_types::models::AccountState::Frozen
    pub disable_delete_frozen_accounts: bool,
    /// Charge account balance for additional `total_action_fees`
    /// when action phase fails.
    pub charge_action_fees_on_fail: bool,
    /// Attaches an original message body as an additional cell
    /// to a bounced message body.
    pub full_body_in_bounced: bool,
}

/// Executed transaction.
pub struct UncommitedTransaction<'a, 's> {
    original: &'s ShardAccount,
    exec: ExecutorState<'a>,
    in_msg: Option<Cell>,
    info: Lazy<TxInfo>,
    brief_info: BriefTxInfo,
}

struct BriefTxInfo {
    gas_used: u64,
}

impl<'a, 's> UncommitedTransaction<'a, 's> {
    #[inline]
    pub fn with_info(
        exec: ExecutorState<'a>,
        original: &'s ShardAccount,
        in_msg: Option<Cell>,
        info: impl Into<TxInfo>,
    ) -> Result<Self> {
        use everscale_types::models::ComputePhase;

        let info = info.into();
        let gas_used = match &info {
            TxInfo::Ordinary(info) => match &info.compute_phase {
                ComputePhase::Executed(phase) => phase.gas_used.into_inner(),
                ComputePhase::Skipped(_) => 0,
            },
            TxInfo::TickTock(info) => match &info.compute_phase {
                ComputePhase::Executed(phase) => phase.gas_used.into_inner(),
                ComputePhase::Skipped(_) => 0,
            },
        };

        let info = Lazy::new(&info)?;
        Ok(Self {
            original,
            exec,
            in_msg,
            info,
            brief_info: BriefTxInfo { gas_used },
        })
    }

    /// Creates a partially finalized transaction.
    ///
    /// It differs from the normal transaction by having a stub `state_update`
    /// and possibly denormalized `end_status`.
    pub fn build_uncommited(&self) -> Result<Transaction, Error> {
        thread_local! {
            static EMPTY_STATE_UPDATE: Lazy<HashUpdate> = Lazy::new(&HashUpdate {
                old: HashBytes::ZERO,
                new: HashBytes::ZERO,
            })
            .unwrap();
        }

        self.build_transaction(self.exec.end_status, EMPTY_STATE_UPDATE.with(Clone::clone))
    }

    /// Creates a final transaction and a new contract state.
    pub fn commit(mut self) -> Result<ExecutorOutput> {
        // Collect brief account state info and build new account state.
        let account_state;
        let new_state_meta;
        let end_status = match self.build_account_state()? {
            None => {
                // TODO: Replace with a constant?
                account_state = CellBuilder::build_from(false)?;

                // Brief meta.
                new_state_meta = AccountMeta {
                    balance: CurrencyCollection::ZERO,
                    libraries: Dict::new(),
                    exists: false,
                };

                // Done
                AccountStatus::NotExists
            }
            Some(state) => {
                // Load previous account storage info.
                let prev_account_storage = 'prev: {
                    let mut cs = self.original.account.as_slice_allow_exotic();
                    if !cs.load_bit()? {
                        // account_none$0
                        break 'prev None;
                    }
                    // account$1
                    // addr:MsgAddressInt
                    IntAddr::load_from(&mut cs)?;
                    // storage_stat:StorageInfo
                    let storage_info = StorageInfo::load_from(&mut cs)?;
                    // storage:AccountStorage
                    Some((storage_info.used, cs))
                };

                // Serialize part of the new account state to compute new storage stats.
                let mut account_storage = CellBuilder::new();
                // last_trans_lt:uint64
                account_storage.store_u64(self.exec.end_lt)?;
                // balance:CurrencyCollection
                self.exec
                    .balance
                    .store_into(&mut account_storage, Cell::empty_context())?;
                // state:AccountState
                state.store_into(&mut account_storage, Cell::empty_context())?;

                // Update storage info.
                self.exec.storage_stat.used = compute_storage_used(
                    &prev_account_storage,
                    account_storage.as_full_slice(),
                    &mut self.exec.cached_storage_stat,
                )?;

                // Build new account state.
                account_state = CellBuilder::build_from((
                    true,                            // account$1
                    &self.exec.address,              // addr:MsgAddressInt
                    &self.exec.storage_stat,         // storage_stat:StorageInfo
                    account_storage.as_full_slice(), // storage:AccountStorage
                ))?;

                // Brief meta.
                let libraries = match &state {
                    AccountState::Active(state) => state.libraries.clone(),
                    AccountState::Frozen(..) | AccountState::Uninit => Dict::new(),
                };
                new_state_meta = AccountMeta {
                    balance: self.exec.balance.clone(),
                    libraries,
                    exists: true,
                };

                // Done
                state.status()
            }
        };

        // Serialize transaction.
        let state_update = Lazy::new(&HashUpdate {
            old: *self.original.account.repr_hash(),
            new: *account_state.repr_hash(),
        })?;
        let transaction = self
            .build_transaction(end_status, state_update)
            .and_then(|tx| Lazy::new(&tx))?;

        // Collect brief transaction info.
        let transaction_meta = TransactionMeta {
            total_fees: self.exec.total_fees,
            next_lt: self.exec.end_lt,
            out_msgs: self.exec.out_msgs,
            gas_used: self.brief_info.gas_used,
        };

        // New shard account state.
        let new_state = ShardAccount {
            // SAFETY: `account_state` is an ordinary cell.
            account: unsafe { Lazy::from_raw_unchecked(account_state) },
            last_trans_hash: *transaction.repr_hash(),
            last_trans_lt: self.exec.start_lt,
        };

        // Done
        Ok(ExecutorOutput {
            new_state,
            new_state_meta,
            transaction,
            transaction_meta,
            burned: self.exec.burned,
        })
    }

    fn build_account_state(&self) -> Result<Option<AccountState>> {
        Ok(match self.exec.end_status {
            // Account was deleted.
            AccountStatus::NotExists => None,
            // Uninit account we zero balance is also treated as deleted.
            AccountStatus::Uninit if self.exec.balance.is_zero() => None,
            // Uninit account stays the same.
            AccountStatus::Uninit => Some(AccountState::Uninit),
            // Active account must have a known active state.
            AccountStatus::Active => {
                debug_assert!(matches!(self.exec.state, AccountState::Active(_)));
                Some(self.exec.state.clone())
            }
            // Normalize frozen state.
            AccountStatus::Frozen => {
                let cell;
                let frozen_hash = match &self.exec.state {
                    // Uninit accounts can't be frozen, but if they accidentialy can
                    // just use the account address as frozen state hash to produce the
                    // same uninit state.
                    AccountState::Uninit => &self.exec.address.address,
                    // To freeze an active account we must compute a hash of its state.
                    AccountState::Active(state_init) => {
                        cell = CellBuilder::build_from(state_init)?;
                        cell.repr_hash()
                    }
                    // Account is already frozen.
                    AccountState::Frozen(hash_bytes) => hash_bytes,
                };

                // Normalize account state.
                Some(if frozen_hash == &self.exec.address.address {
                    AccountState::Uninit
                } else {
                    AccountState::Frozen(*frozen_hash)
                })
            }
        })
    }

    fn build_transaction(
        &self,
        end_status: AccountStatus,
        state_update: Lazy<HashUpdate>,
    ) -> Result<Transaction, Error> {
        Ok(Transaction {
            account: self.exec.address.address,
            lt: self.exec.start_lt,
            prev_trans_hash: self.original.last_trans_hash,
            prev_trans_lt: self.original.last_trans_lt,
            now: self.exec.params.block_unixtime,
            out_msg_count: Uint15::new(self.exec.out_msgs.len() as _),
            orig_status: self.exec.orig_status,
            end_status,
            in_msg: self.in_msg.clone(),
            out_msgs: build_out_msgs(&self.exec.out_msgs)?,
            total_fees: self.exec.total_fees.into(),
            state_update,
            info: self.info.clone(),
        })
    }
}

fn compute_storage_used(
    prev: &Option<(StorageUsed, CellSlice<'_>)>,
    new_storage: CellSlice<'_>,
    cache: &mut Option<OwnedExtStorageStat>,
) -> Result<StorageUsed> {
    // Try to reuse previous storage stats if no cells were changed.
    if let Some((prev_used, prev_storage)) = prev {
        'reuse: {
            // Always recompute when previous stats are invalid.
            if prev_used.cells.is_zero()
                || prev_used.bits.into_inner() < prev_storage.size_bits() as u64
            {
                break 'reuse;
            }

            // Simple check that some cells were changed.
            if prev_storage.size_refs() != new_storage.size_refs() {
                break 'reuse;
            }

            // Compare each cell.
            for (prev, new) in prev_storage.references().zip(new_storage.references()) {
                if prev != new {
                    break 'reuse;
                }
            }

            // Adjust bit size of the root slice.
            return Ok(StorageUsed {
                // Compute the truncated difference of the previous storage root and a new one.
                bits: new_varuint56_truncate(
                    (prev_used.bits.into_inner() - prev_storage.size_bits() as u64)
                        .saturating_add(new_storage.size_bits() as u64),
                ),
                // All other stats are unchanged.
                cells: prev_used.cells,
                public_cells: prev_used.public_cells,
            });
        }
    }

    // Init cache.
    let cache = cache.get_or_insert_with(OwnedExtStorageStat::unlimited);
    cache.set_unlimited();

    // Compute stats for childern.
    for cell in new_storage.references().cloned() {
        cache.add_cell(cell);
    }
    let stats = cache.stats();

    // Done.
    Ok(StorageUsed {
        cells: new_varuint56_truncate(stats.cell_count.saturating_add(1)),
        bits: new_varuint56_truncate(stats.bit_count.saturating_add(new_storage.size_bits() as _)),
        public_cells: VarUint56::ZERO,
    })
}

/// Commited transaction output.
#[derive(Clone, Debug)]
pub struct ExecutorOutput {
    pub new_state: ShardAccount,
    pub new_state_meta: AccountMeta,
    pub transaction: Lazy<Transaction>,
    pub transaction_meta: TransactionMeta,
    pub burned: Tokens,
}

/// Short account description.
#[derive(Clone, Debug)]
pub struct AccountMeta {
    pub balance: CurrencyCollection,
    pub libraries: Dict<HashBytes, SimpleLib>,
    pub exists: bool,
}

/// Short transaction description.
#[derive(Clone, Debug)]
pub struct TransactionMeta {
    pub total_fees: Tokens,
    pub out_msgs: Vec<Lazy<OwnedMessage>>,
    pub gas_used: u64,
    pub next_lt: u64,
}

/// Message cell source.
pub trait LoadMessage {
    fn load_message_root(self) -> Result<Cell>;
}

impl<T: LoadMessage + Clone> LoadMessage for &T {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        T::load_message_root(T::clone(self))
    }
}

impl LoadMessage for Cell {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        Ok(self)
    }
}

impl<T: EquivalentRepr<OwnedMessage>> LoadMessage for Lazy<T> {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        Ok(self.into_inner())
    }
}

impl LoadMessage for OwnedMessage {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        CellBuilder::build_from(self).context("failed to serialize inbound message")
    }
}

impl LoadMessage for Message<'_> {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        CellBuilder::build_from(self).context("failed to serialize inbound message")
    }
}

fn build_out_msgs(out_msgs: &[Lazy<OwnedMessage>]) -> Result<Dict<Uint15, Cell>, Error> {
    dict::build_dict_from_sorted_iter(
        out_msgs
            .iter()
            .enumerate()
            .map(|(i, msg)| (Uint15::new(i as _), msg.inner().clone())),
        15,
        Cell::empty_context(),
    )
    .map(Dict::from_raw)
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use everscale_types::boc::BocRepr;
    use everscale_types::models::{BlockchainConfig, MsgInfo, SizeLimitsConfig, StateInit};

    use super::*;

    pub fn make_default_config() -> Rc<ParsedConfig> {
        thread_local! {
            pub static PARSED_CONFIG: Rc<ParsedConfig> = make_custom_config(|_| Ok(()));
        }

        PARSED_CONFIG.with(Clone::clone)
    }

    pub fn make_custom_config<F>(f: F) -> Rc<ParsedConfig>
    where
        F: FnOnce(&mut BlockchainConfig) -> anyhow::Result<()>,
    {
        let mut config: BlockchainConfig =
            BocRepr::decode(include_bytes!("../res/config.boc")).unwrap();

        config.params.set_global_id(100).unwrap();

        // TODO: Update config BOC
        config
            .params
            .set_size_limits(&SizeLimitsConfig {
                max_msg_bits: 1 << 21,
                max_msg_cells: 1 << 13,
                max_library_cells: 1000,
                max_vm_data_depth: 512,
                max_ext_msg_size: 65535,
                max_ext_msg_depth: 512,
                max_acc_state_cells: 1 << 16,
                max_acc_state_bits: (1 << 16) * 1023,
                max_acc_public_libraries: 256,
                defer_out_queue_size_limit: 256,
            })
            .unwrap();

        f(&mut config).unwrap();

        Rc::new(ParsedConfig::parse(config, u32::MAX).unwrap())
    }

    pub fn make_default_params() -> ExecutorParams {
        ExecutorParams {
            block_unixtime: 1738799198,
            full_body_in_bounced: false,
            vm_modifiers: tycho_vm::BehaviourModifiers {
                chksig_always_succeed: true,
                ..Default::default()
            },
            ..Default::default()
        }
    }

    pub fn make_message(
        info: impl Into<MsgInfo>,
        init: Option<StateInit>,
        body: Option<CellBuilder>,
    ) -> Cell {
        let body = match &body {
            None => Cell::empty_cell_ref().as_slice_allow_exotic(),
            Some(cell) => cell.as_full_slice(),
        };
        CellBuilder::build_from(Message {
            info: info.into(),
            init,
            body,
            layout: None,
        })
        .unwrap()
    }

    pub fn make_big_tree(depth: u8, count: &mut u16, target: u16) -> Cell {
        *count += 1;

        if depth == 0 {
            CellBuilder::build_from(*count).unwrap()
        } else {
            let mut b = CellBuilder::new();
            for _ in 0..4 {
                if *count < target {
                    b.store_reference(make_big_tree(depth - 1, count, target))
                        .unwrap();
                }
            }
            b.build().unwrap()
        }
    }
}
