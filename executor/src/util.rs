use std::collections::hash_map;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};

use ahash::HashMap;
use everscale_types::cell::CellTreeStats;
use everscale_types::models::{
    IntAddr, ShardIdent, SimpleLib, SizeLimitsConfig, StateInit, StdAddr, WorkchainDescription,
    WorkchainFormat,
};
use everscale_types::num::{VarUint24, VarUint56};
use everscale_types::prelude::*;

/// Brings [unlikely](core::intrinsics::unlikely) to stable rust.
#[inline(always)]
pub(crate) const fn unlikely(b: bool) -> bool {
    #[allow(clippy::needless_bool, clippy::bool_to_int_with_if)]
    if (1i32).checked_div(if b { 0 } else { 1 }).is_none() {
        true
    } else {
        false
    }
}

#[derive(Default)]
pub struct StorageStatLimits {
    pub bit_count: u32,
    pub cell_count: u32,
}

impl StorageStatLimits {
    pub const UNLIMITED: Self = Self {
        bit_count: u32::MAX,
        cell_count: u32::MAX,
    };
}

#[derive(Default)]
pub struct StorageCache {
    items: HashMap<HashBytes, StorageCacheItem>,
}

impl StorageCache {
    pub(crate) fn with_target_capacity(existing: Option<&StorageCache>) -> Self {
        match existing {
            None => Self::default(),
            Some(existing) => Self {
                items: HashMap::with_capacity_and_hasher(existing.items.len(), Default::default()),
            },
        }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn clear(&mut self) {
        self.items.clear();
    }

    pub(crate) fn into_final(self, existing: Option<&'_ StorageCache>) -> FinalStorageStat<'_> {
        FinalStorageStat {
            existing,
            visited: self,
        }
    }
}

pub(crate) struct FinalStorageStat<'a> {
    existing: Option<&'a StorageCache>,
    visited: StorageCache,
}

impl FinalStorageStat<'_> {
    pub fn into_storage_cache(self) -> StorageCache {
        self.visited
    }

    pub fn compute_stats(&self) -> CellTreeStats {
        let mut result = CellTreeStats {
            bit_count: 0,
            cell_count: 0,
        };

        for item in self.visited.items.values() {
            result.bit_count = result.bit_count.saturating_add(item.bit_len as u64);
            result.cell_count = result.cell_count.saturating_add(1);
        }

        result
    }

    pub fn add_cell(&mut self, cell: &DynCell) {
        self.add_cell_impl(cell);
    }

    fn add_cell_impl(&mut self, cell: &DynCell) -> InsertedItem {
        let hash = cell.repr_hash();
        if let Some(item) = self.visited.items.get(hash) {
            return InsertedItem::AlreadyVisited {
                merkle_depth: item.merkle_depth,
            };
        } else if let Some(existing) = self.existing {
            if let Some(existing) = existing.items.get(hash).cloned() {
                self.visit_cached(&existing);
                return InsertedItem::New(existing);
            }
        }

        let merkle_diff = cell.cell_type().is_merkle() as u8;
        let mut max_merkle_depth = 0;
        let mut item = Box::new(StorageCacheItemInner {
            strong: AtomicUsize::new(1),
            parent_hash: *hash,
            children: [const { None }; 4],
        });
        for (i, cell) in cell.references().enumerate() {
            let child_merkle_depth;
            match self.add_cell_impl(cell) {
                InsertedItem::New(child) => {
                    child_merkle_depth = child.merkle_depth;
                    unsafe { *item.children.get_unchecked_mut(i) = Some(child) };
                }
                InsertedItem::AlreadyVisited { merkle_depth } => {
                    child_merkle_depth = merkle_depth;
                }
            }
            max_merkle_depth = std::cmp::max(max_merkle_depth, child_merkle_depth);
        }

        let item = StorageCacheItem {
            bit_len: cell.bit_len(),
            merkle_depth: max_merkle_depth + merkle_diff,
            // SAFETY: Pointer is never null since we are using an existing allocation.
            ptr: unsafe { NonNull::new_unchecked(Box::into_raw(item)) },
        };

        self.visited.items.insert(*hash, item.clone());
        InsertedItem::New(item)
    }

    fn visit_cached(&mut self, cached: &StorageCacheItem) {
        match self.visited.items.entry(*cached.hash()) {
            hash_map::Entry::Vacant(entry) => {
                entry.insert(cached.clone());
            }
            hash_map::Entry::Occupied(_) => return,
        }

        for cached in cached.references() {
            self.visit_cached(cached);
        }
    }
}

pub(crate) struct NewStorageStat<'a> {
    existing: Option<&'a StorageCache>,
    visited: StorageCache,
    limits: StorageStatLimits,
    cells: u32,
    bits: u32,
}

impl<'a> NewStorageStat<'a> {
    pub fn with_limits(limits: StorageStatLimits, existing: Option<&'a StorageCache>) -> Self {
        let visited = StorageCache::with_target_capacity(existing);
        Self {
            existing,
            visited,
            limits,
            cells: 0,
            bits: 0,
        }
    }

    pub fn into_storage_cache(self) -> StorageCache {
        self.visited
    }

    pub fn add_cell(&mut self, cell: &DynCell) -> bool {
        self.add_cell_impl(cell).is_some()
    }

    fn add_cell_impl(&mut self, cell: &DynCell) -> Option<InsertedItem> {
        let hash = cell.repr_hash();
        if let Some(item) = self.visited.items.get(hash) {
            return Some(InsertedItem::AlreadyVisited {
                merkle_depth: item.merkle_depth,
            });
        } else if let Some(existing) = self.existing {
            if let Some(existing) = existing.items.get(hash).cloned() {
                return if self.visit_cached(&existing) {
                    Some(InsertedItem::New(existing))
                } else {
                    None
                };
            }
        }

        let bit_len = cell.bit_len();
        if !self.add_cell_stats(bit_len) {
            return None;
        }

        let merkle_diff = cell.cell_type().is_merkle() as u8;
        let mut max_merkle_depth = 0;
        let mut item = Box::new(StorageCacheItemInner {
            strong: AtomicUsize::new(1),
            parent_hash: *hash,
            children: [const { None }; 4],
        });
        for (i, cell) in cell.references().enumerate() {
            let child_merkle_depth;
            match self.add_cell_impl(cell)? {
                InsertedItem::New(child) => {
                    child_merkle_depth = child.merkle_depth;
                    unsafe { *item.children.get_unchecked_mut(i) = Some(child) };
                }
                InsertedItem::AlreadyVisited { merkle_depth } => {
                    child_merkle_depth = merkle_depth;
                }
            }
            max_merkle_depth = std::cmp::max(max_merkle_depth, child_merkle_depth);
            if max_merkle_depth + merkle_diff > ExtStorageStat::MAX_ALLOWED_MERKLE_DEPTH {
                return None;
            }
        }

        let item = StorageCacheItem {
            bit_len,
            merkle_depth: max_merkle_depth + merkle_diff,
            // SAFETY: Pointer is never null since we are using an existing allocation.
            ptr: unsafe { NonNull::new_unchecked(Box::into_raw(item)) },
        };

        self.visited.items.insert(*hash, item.clone());
        Some(InsertedItem::New(item))
    }

    fn visit_cached(&mut self, cached: &StorageCacheItem) -> bool {
        match self.visited.items.entry(*cached.hash()) {
            hash_map::Entry::Vacant(entry) => {
                entry.insert(cached.clone());
            }
            hash_map::Entry::Occupied(_) => return true,
        }

        if !self.add_cell_stats(cached.bit_len) {
            return false;
        }

        for cached in cached.references() {
            if !self.visit_cached(cached) {
                return false;
            }
        }

        true
    }

    fn add_cell_stats(&mut self, bit_len: u16) -> bool {
        self.cells = match self.cells.checked_add(1) {
            Some(cells) => cells,
            None => return false,
        };
        self.bits = match self.bits.checked_add(bit_len as u32) {
            Some(bits) => bits,
            None => return false,
        };
        self.cells <= self.limits.cell_count && self.bits <= self.limits.bit_count
    }
}

enum InsertedItem {
    New(StorageCacheItem),
    AlreadyVisited { merkle_depth: u8 },
}

pub(crate) struct StorageCacheItem {
    bit_len: u16,
    merkle_depth: u8,
    ptr: NonNull<StorageCacheItemInner>,
}

impl StorageCacheItem {
    const MAX_REFCOUNT: usize = isize::MAX as usize;

    pub fn hash(&self) -> &HashBytes {
        &self.inner().parent_hash
    }

    pub fn references(&self) -> impl Iterator<Item = &'_ Self> {
        self.inner().children.iter().flat_map(Option::as_ref)
    }

    #[inline]
    fn inner(&self) -> &StorageCacheItemInner {
        // This unsafety is ok because while this arc is alive we're guaranteed
        // that the inner pointer is valid. Furthermore, we know that the
        // `ArcInner` structure itself is `Sync` because the inner data is
        // `Sync` as well, so we're ok loaning out an immutable pointer to these
        // contents.
        unsafe { self.ptr.as_ref() }
    }

    // Non-inlined part of `drop`. Just invokes the destructor.
    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        let _ = Box::from_raw(self.ptr.as_ptr());
    }
}

impl Clone for StorageCacheItem {
    #[inline]
    fn clone(&self) -> Self {
        let old_size = self.inner().strong.fetch_add(1, Ordering::Relaxed);
        if old_size > Self::MAX_REFCOUNT {
            std::process::abort();
        }
        Self {
            bit_len: self.bit_len,
            merkle_depth: self.merkle_depth,
            ptr: self.ptr,
        }
    }
}

impl Drop for StorageCacheItem {
    #[inline]
    fn drop(&mut self) {
        // Because `fetch_sub` is already atomic, we do not need to synchronize
        // with other threads unless we are going to delete the object.
        if self.inner().strong.fetch_sub(1, Ordering::Release) != 1 {
            return;
        }

        self.inner().strong.load(Ordering::Acquire);

        unsafe {
            self.drop_slow();
        }
    }
}

unsafe impl Send for StorageCacheItem {}
unsafe impl Sync for StorageCacheItem {}

struct StorageCacheItemInner {
    strong: AtomicUsize,
    parent_hash: HashBytes,
    children: [Option<StorageCacheItem>; 4],
}

#[derive(Default)]
pub struct ExtStorageStat<'a> {
    visited: ahash::HashMap<&'a HashBytes, u8>,
    limits: StorageStatLimits,
    pub cells: u32,
    pub bits: u32,
}

impl<'a> ExtStorageStat<'a> {
    pub const MAX_ALLOWED_MERKLE_DEPTH: u8 = 2;

    pub fn with_limits(limits: StorageStatLimits) -> Self {
        Self {
            visited: ahash::HashMap::default(),
            limits,
            cells: 0,
            bits: 0,
        }
    }

    pub fn compute_for_slice(
        cs: &CellSlice<'a>,
        limits: StorageStatLimits,
    ) -> Option<CellTreeStats> {
        let mut state = Self {
            visited: ahash::HashMap::default(),
            limits,
            cells: 1,
            bits: cs.size_bits() as u32,
        };

        for cell in cs.references() {
            state.add_cell_impl(cell)?;
        }

        Some(CellTreeStats {
            bit_count: state.bits as u64,
            cell_count: state.cells as u64,
        })
    }

    pub fn stats(&self) -> CellTreeStats {
        CellTreeStats {
            bit_count: self.bits as u64,
            cell_count: self.cells as u64,
        }
    }

    pub fn add_cell(&mut self, cell: &'a DynCell) -> bool {
        self.add_cell_impl(cell).is_some()
    }

    fn add_cell_impl(&mut self, cell: &'a DynCell) -> Option<u8> {
        if let Some(merkle_depth) = self.visited.get(cell.repr_hash()).copied() {
            return Some(merkle_depth);
        }

        self.cells = self.cells.checked_add(1)?;
        self.bits = self.bits.checked_add(cell.bit_len() as u32)?;

        if self.cells > self.limits.cell_count || self.bits > self.limits.bit_count {
            return None;
        }

        let mut max_merkle_depth = 0u8;
        for cell in cell.references() {
            max_merkle_depth = std::cmp::max(self.add_cell_impl(cell)?, max_merkle_depth);
        }
        max_merkle_depth = max_merkle_depth.saturating_add(cell.cell_type().is_merkle() as u8);

        self.visited.insert(cell.repr_hash(), max_merkle_depth);
        (max_merkle_depth <= Self::MAX_ALLOWED_MERKLE_DEPTH).then_some(max_merkle_depth)
    }
}

pub fn new_varuint24_truncate(value: u64) -> VarUint24 {
    VarUint24::new(std::cmp::min(value, VarUint24::MAX.into_inner() as u64) as _)
}

pub fn new_varuint56_truncate(value: u64) -> VarUint56 {
    VarUint56::new(std::cmp::min(value, VarUint56::MAX.into_inner()))
}

/// Rewrites message source address.
pub fn check_rewrite_src_addr(my_addr: &StdAddr, addr: &mut Option<IntAddr>) -> bool {
    match addr {
        // Replace `addr_none` with the address of the account.
        None => {
            *addr = Some(my_addr.clone().into());
            true
        }
        // Only allow `addr_std` that must be equal to the account address.
        Some(IntAddr::Std(addr)) if addr == my_addr => true,
        // All other addresses are considered invalid.
        Some(_) => false,
    }
}

/// Rewrite message destination address.
pub fn check_rewrite_dst_addr(
    workchains: &HashMap<i32, WorkchainDescription>,
    addr: &mut IntAddr,
) -> bool {
    const STD_WORKCHAINS: std::ops::Range<i32> = -128..128;
    const STD_ADDR_LEN: u16 = 256;

    // Check destination workchain.
    let mut can_rewrite = false;
    let workchain = match addr {
        IntAddr::Std(addr) => {
            if addr.anycast.is_some() {
                // Anycasts are not supported for now.
                return false;
            }

            addr.workchain as i32
        }
        IntAddr::Var(addr) => {
            if addr.anycast.is_some() {
                // Anycasts are not supported for now.
                return false;
            }

            // `addr_var` of len 256 in a valid workchains range
            // can be rewritten to `addr_std` if needed.
            can_rewrite = addr.address_len.into_inner() == STD_ADDR_LEN
                && STD_WORKCHAINS.contains(&addr.workchain);

            addr.workchain
        }
    };

    if workchain != ShardIdent::MASTERCHAIN.workchain() {
        let Some(workchain) = workchains.get(&workchain) else {
            // Cannot send message to an unknown workchain.
            return false;
        };

        if !workchain.accept_msgs {
            // Cannot send messages to disabled workchains.
            return false;
        }

        match (&workchain.format, &*addr) {
            // `addr_std` is the default address format for basic workchains.
            (WorkchainFormat::Basic(_), IntAddr::Std(_)) => {}
            // `addr_var` can be rewritten to `addr_std` for basic workchains.
            (WorkchainFormat::Basic(_), IntAddr::Var(_)) if can_rewrite => {}
            // `addr_std` can be used for extended workchains if the length is ok.
            (WorkchainFormat::Extended(f), IntAddr::Std(_)) if f.check_addr_len(STD_ADDR_LEN) => {}
            // `addr_var` can be used for extended workchains if the length is ok.
            (WorkchainFormat::Extended(f), IntAddr::Var(a))
                if f.check_addr_len(a.address_len.into_inner()) => {}
            // All other combinations are invalid.
            _ => return false,
        }
    }

    // Rewrite if needed.
    if can_rewrite {
        if let IntAddr::Var(var) = addr {
            debug_assert!(STD_WORKCHAINS.contains(&var.workchain));
            debug_assert_eq!(var.address_len.into_inner(), STD_ADDR_LEN);

            // Copy high address bytes into the target address.
            let len = std::cmp::min(var.address.len(), 32);
            let mut address = [0; 32];
            address[..len].copy_from_slice(&var.address[..len]);

            // Set type as `addr_std`.
            *addr = IntAddr::Std(StdAddr::new(var.workchain as i8, HashBytes(address)));
        }
    }

    // Done
    true
}

pub enum StateLimitsResult {
    Unchanged,
    Exceeds,
    Fits,
}

/// NOTE: `storage_cache` is updated only when `StateLimitsResult::Fits` is returned.
pub fn check_state_limits_diff(
    old_state: &StateInit,
    new_state: &StateInit,
    limits: &SizeLimitsConfig,
    is_masterchain: bool,
    storage_cache: &mut Option<StorageCache>,
    prev_storage_cache: Option<&StorageCache>,
) -> StateLimitsResult {
    /// Returns (code, data, libs)
    fn unpack_state(state: &StateInit) -> (Option<&'_ Cell>, Option<&'_ Cell>, &'_ StateLibs) {
        (state.code.as_ref(), state.data.as_ref(), &state.libraries)
    }

    let (old_code, old_data, old_libs) = unpack_state(old_state);
    let (new_code, new_data, new_libs) = unpack_state(new_state);

    // Early exit if nothing changed.
    let libs_changed = old_libs != new_libs;
    if old_code == new_code && old_data == new_data && !libs_changed {
        return StateLimitsResult::Unchanged;
    }

    // Check public libraries (only for masterchain, because in other workchains all
    // public libraries are ignored and not tracked).
    let check_public_libs = is_masterchain && libs_changed;

    check_state_limits(
        new_code,
        new_data,
        new_libs,
        limits,
        check_public_libs,
        storage_cache,
        prev_storage_cache,
    )
}

pub fn check_state_limits(
    code: Option<&Cell>,
    data: Option<&Cell>,
    libs: &StateLibs,
    limits: &SizeLimitsConfig,
    check_public_libs: bool,
    storage_cache: &mut Option<StorageCache>,
    prev_storage_cache: Option<&StorageCache>,
) -> StateLimitsResult {
    // Compute storage stats.
    let mut stats = NewStorageStat::with_limits(
        StorageStatLimits {
            bit_count: limits.max_acc_state_bits,
            cell_count: limits.max_acc_state_cells,
        },
        prev_storage_cache,
    );

    if let Some(code) = code {
        if !stats.add_cell(code.as_ref()) {
            return StateLimitsResult::Exceeds;
        }
    }

    if let Some(data) = data {
        if !stats.add_cell(data.as_ref()) {
            return StateLimitsResult::Exceeds;
        }
    }

    if let Some(libs) = libs.root() {
        if !stats.add_cell(libs.as_ref()) {
            return StateLimitsResult::Exceeds;
        }
    }

    // Check public libraries (only for masterchain, because in other workchains all
    // public libraries are ignored and not tracked).
    if check_public_libs {
        let mut public_libs_count = 0;
        for lib in libs.values() {
            let Ok(lib) = lib else {
                return StateLimitsResult::Exceeds;
            };

            public_libs_count += lib.public as usize;
            if public_libs_count > limits.max_acc_public_libraries as usize {
                return StateLimitsResult::Exceeds;
            }
        }
    }

    // Ok
    *storage_cache = Some(stats.into_storage_cache());
    StateLimitsResult::Fits
}

type StateLibs = Dict<HashBytes, SimpleLib>;

pub const fn shift_ceil_price(value: u128) -> u128 {
    let r = value & 0xffff != 0;
    (value >> 16) + r as u128
}

#[cfg(test)]
mod tests {
    use everscale_types::models::BlockchainConfig;

    use super::*;

    #[test]
    fn new_storage_stat_works() -> anyhow::Result<()> {
        let cell = Boc::decode(include_bytes!("../res/config.boc"))?;
        let target_stats = cell.compute_unique_stats(usize::MAX).unwrap();
        println!("target_stats: {target_stats:?}");

        let mut new_storage_stats = NewStorageStat::with_limits(StorageStatLimits::UNLIMITED, None);
        assert!(new_storage_stats.add_cell(cell.as_ref()));
        assert_eq!(
            CellTreeStats {
                bit_count: new_storage_stats.bits as u64,
                cell_count: new_storage_stats.cells as u64,
            },
            target_stats
        );

        let prev_storage_stats = {
            let mut config = cell.parse::<BlockchainConfig>()?;
            config.params.set_fundamental_addresses(&[
                HashBytes([0x33; 32]),
                HashBytes([0x55; 32]),
                HashBytes([0x66; 32]),
            ])?;
            let cell = CellBuilder::build_from(config)?;
            let mut stat = NewStorageStat::with_limits(StorageStatLimits::UNLIMITED, None);
            assert!(stat.add_cell(cell.as_ref()));
            stat.into_storage_cache()
        };

        let mut new_storage_stats =
            NewStorageStat::with_limits(StorageStatLimits::UNLIMITED, Some(&prev_storage_stats));
        assert!(new_storage_stats.add_cell(cell.as_ref()));
        assert_eq!(
            CellTreeStats {
                bit_count: new_storage_stats.bits as u64,
                cell_count: new_storage_stats.cells as u64,
            },
            target_stats
        );

        let mut cache = new_storage_stats
            .into_storage_cache()
            .into_final(Some(&prev_storage_stats));
        cache.add_cell(cell.as_ref());
        assert_eq!(cache.compute_stats(), target_stats);

        let mut cache = StorageCache::default().into_final(Some(&prev_storage_stats));
        cache.add_cell(cell.as_ref());
        assert_eq!(cache.compute_stats(), target_stats);

        Ok(())
    }
}
