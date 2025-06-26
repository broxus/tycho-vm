use std::mem::ManuallyDrop;

use ahash::HashMap;
use tycho_types::cell::CellTreeStats;
use tycho_types::models::{
    IntAddr, ShardIdent, SimpleLib, SizeLimitsConfig, StateInit, StdAddr, WorkchainDescription,
    WorkchainFormat,
};
use tycho_types::num::{VarUint24, VarUint56};
use tycho_types::prelude::*;

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

pub struct OwnedExtStorageStat {
    cells: Vec<Cell>,
    inner: ManuallyDrop<ExtStorageStat<'static>>,
}

impl OwnedExtStorageStat {
    pub fn unlimited() -> Self {
        Self::with_limits(StorageStatLimits::UNLIMITED)
    }

    pub fn with_limits(limits: StorageStatLimits) -> Self {
        Self {
            cells: Vec::new(),
            inner: ManuallyDrop::new(ExtStorageStat::with_limits(limits)),
        }
    }

    pub fn set_unlimited(&mut self) {
        self.inner.limits = StorageStatLimits::UNLIMITED;
    }

    pub fn stats(&self) -> CellTreeStats {
        self.inner.stats()
    }

    pub fn add_cell(&mut self, cell: Cell) -> bool {
        if self.inner.visited.contains_key(cell.repr_hash()) {
            return true;
        }

        // SAFETY: We will store the cell afterwards so the lifetime of its hash
        //         will outlive the `inner` object.
        let cell_ref = unsafe { std::mem::transmute::<&DynCell, &'static DynCell>(cell.as_ref()) };
        let res = self.inner.add_cell(cell_ref);
        self.cells.push(cell);
        res
    }

    pub fn clear(&mut self) {
        self.inner.visited.clear();
        self.inner.cells = 0;
        self.inner.bits = 0;

        // NOTE: We can clear the cells vector only after clearing the `visited` map.
        self.cells.clear();
    }
}

impl Drop for OwnedExtStorageStat {
    fn drop(&mut self) {
        // We must ensure that `inner` is dropped before `cells`.
        // SAFETY: This is the only place where `inner` is dropped.
        unsafe { ManuallyDrop::drop(&mut self.inner) };
    }
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

/// NOTE: `stats_cache` is updated only when `StateLimitsResult::Fits` is returned.
pub fn check_state_limits_diff(
    old_state: &StateInit,
    new_state: &StateInit,
    limits: &SizeLimitsConfig,
    is_masterchain: bool,
    stats_cache: &mut Option<OwnedExtStorageStat>,
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
        stats_cache,
    )
}

pub fn check_state_limits(
    code: Option<&Cell>,
    data: Option<&Cell>,
    libs: &StateLibs,
    limits: &SizeLimitsConfig,
    check_public_libs: bool,
    stats_cache: &mut Option<OwnedExtStorageStat>,
) -> StateLimitsResult {
    // Compute storage stats.
    let mut stats = OwnedExtStorageStat::with_limits(StorageStatLimits {
        bit_count: limits.max_acc_state_bits,
        cell_count: limits.max_acc_state_cells,
    });

    if let Some(code) = code {
        if !stats.add_cell(code.clone()) {
            return StateLimitsResult::Exceeds;
        }
    }

    if let Some(data) = data {
        if !stats.add_cell(data.clone()) {
            return StateLimitsResult::Exceeds;
        }
    }

    if let Some(libs) = libs.root() {
        if !stats.add_cell(libs.clone()) {
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
    *stats_cache = Some(stats);
    StateLimitsResult::Fits
}

type StateLibs = Dict<HashBytes, SimpleLib>;

pub const fn shift_ceil_price(value: u128) -> u128 {
    let r = value & 0xffff != 0;
    (value >> 16) + r as u128
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn miri_check() {
        // Drop is ok.
        let mut owned = OwnedExtStorageStat::with_limits(StorageStatLimits {
            bit_count: 1000,
            cell_count: 1000,
        });

        fn fill(owned: &mut OwnedExtStorageStat) {
            let res = owned.add_cell(Cell::empty_cell());
            assert!(res);
            assert_eq!(owned.inner.bits, 0);
            assert_eq!(owned.inner.cells, 1);

            let res = owned.add_cell({
                let mut b = CellBuilder::new();
                b.store_u32(123).unwrap();
                b.store_reference(Cell::empty_cell()).unwrap();
                b.build().unwrap()
            });
            assert!(res);
            assert_eq!(owned.inner.bits, 32);
            assert_eq!(owned.inner.cells, 2);

            // Create the same cell as above to possibly trigger a dangling pointer access.
            let res = owned.add_cell({
                let mut b = CellBuilder::new();
                b.store_u32(123).unwrap();
                b.store_reference(Cell::empty_cell()).unwrap();
                b.build().unwrap()
            });
            assert!(res);
            assert_eq!(owned.inner.bits, 32);
            assert_eq!(owned.inner.cells, 2);
        }

        fill(&mut owned);
        drop(owned);

        // Clear is ok.
        let mut owned = OwnedExtStorageStat::with_limits(StorageStatLimits {
            bit_count: 1000,
            cell_count: 1000,
        });

        fill(&mut owned);
        owned.clear();
        fill(&mut owned);
    }
}
