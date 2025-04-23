use std::hash::BuildHasher;
use std::num::NonZeroU64;
use std::rc::Rc;
use std::sync::Arc;

use ahash::HashSet;
use everscale_types::cell::{CellParts, LoadMode};
use everscale_types::error::Error;
use everscale_types::models::{LibDescr, SimpleLib};
use everscale_types::prelude::*;

use crate::error::VmResult;
use crate::saferc::SafeRc;
use crate::stack::Stack;
use crate::util::OwnedCellSlice;

/// Initialization params for [`GasConsumer`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GasParams {
    /// Maximum possible value of the `limit`.
    pub max: u64,
    /// Gas limit for the out-of-gas exception.
    pub limit: u64,
    /// Free gas (e.g. for external messages without any balance).
    pub credit: u64,
    /// Gas price (fixed point with 16 bits for fractional part).
    pub price: u64,
}

impl GasParams {
    pub const MAX_GAS: u64 = i64::MAX as u64;

    const STUB_GAS_PRICE: u64 = 1000 << 16;

    pub const fn unlimited() -> Self {
        Self {
            max: Self::MAX_GAS,
            limit: Self::MAX_GAS,
            credit: 0,
            price: Self::STUB_GAS_PRICE,
        }
    }

    pub const fn getter() -> Self {
        Self {
            max: 1000000,
            limit: 1000000,
            credit: 0,
            price: Self::STUB_GAS_PRICE,
        }
    }
}

impl Default for GasParams {
    #[inline]
    fn default() -> Self {
        Self::unlimited()
    }
}

/// Library cells resolver.
pub trait LibraryProvider {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error>;

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error>;
}

impl<T: LibraryProvider> LibraryProvider for &'_ T {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        T::find_ref(self, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Option<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        match self {
            Some(this) => T::find(this, library_hash),
            None => Ok(None),
        }
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        match self {
            Some(this) => T::find_ref(this, library_hash),
            None => Ok(None),
        }
    }
}

impl<T1, T2> LibraryProvider for (T1, T2)
where
    T1: LibraryProvider,
    T2: LibraryProvider,
{
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        if let res @ Some(_) = ok!(T1::find(&self.0, library_hash)) {
            return Ok(res);
        }
        T2::find(&self.1, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        if let res @ Some(_) = ok!(T1::find_ref(&self.0, library_hash)) {
            return Ok(res);
        }
        T2::find_ref(&self.1, library_hash)
    }
}

impl<T1, T2, T3> LibraryProvider for (T1, T2, T3)
where
    T1: LibraryProvider,
    T2: LibraryProvider,
    T3: LibraryProvider,
{
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        if let res @ Some(_) = ok!(T1::find(&self.0, library_hash)) {
            return Ok(res);
        }
        if let res @ Some(_) = ok!(T2::find(&self.1, library_hash)) {
            return Ok(res);
        }
        T3::find(&self.2, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        if let res @ Some(_) = ok!(T1::find_ref(&self.0, library_hash)) {
            return Ok(res);
        }
        if let res @ Some(_) = ok!(T2::find_ref(&self.1, library_hash)) {
            return Ok(res);
        }
        T3::find_ref(&self.2, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Box<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        T::find_ref(self, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Rc<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        T::find_ref(self, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Arc<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        T::find_ref(self, library_hash)
    }
}

/// Empty libraries provider.
#[derive(Default, Debug, Clone, Copy)]
pub struct NoLibraries;

impl LibraryProvider for NoLibraries {
    #[inline]
    fn find(&self, _library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        Ok(None)
    }

    fn find_ref<'a>(&'a self, _library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        Ok(None)
    }
}

impl LibraryProvider for Dict<HashBytes, SimpleLib> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        match self.get(library_hash)? {
            Some(lib) => Ok(Some(lib.root)),
            None => Ok(None),
        }
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        match self
            .cast_ref::<HashBytes, SimpleLibRef<'_>>()
            .get(library_hash)?
        {
            Some(lib) => Ok(Some(lib.root)),
            None => Ok(None),
        }
    }
}

impl LibraryProvider for Vec<Dict<HashBytes, SimpleLib>> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        for lib in self {
            match lib.get(library_hash)? {
                Some(lib) => return Ok(Some(lib.root)),
                None => continue,
            }
        }
        Ok(None)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        for lib in self {
            match lib
                .cast_ref::<HashBytes, SimpleLibRef<'_>>()
                .get(library_hash)?
            {
                Some(lib) => return Ok(Some(lib.root)),
                None => continue,
            }
        }
        Ok(None)
    }
}

impl LibraryProvider for Dict<HashBytes, LibDescr> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        Ok(self.get(library_hash)?.map(|lib| lib.lib.clone()))
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        struct LibDescrRef<'tlb> {
            lib: &'tlb DynCell,
        }

        impl<'a> Load<'a> for LibDescrRef<'a> {
            fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
                if slice.load_small_uint(2)? != 0 {
                    return Err(Error::InvalidTag);
                }
                Ok(Self {
                    lib: slice.load_reference()?,
                })
            }
        }

        impl EquivalentRepr<LibDescr> for LibDescrRef<'_> {}

        Ok(self
            .cast_ref::<HashBytes, LibDescrRef<'a>>()
            .get(library_hash)?
            .map(|lib| lib.lib))
    }
}

impl<S: BuildHasher> LibraryProvider for std::collections::HashMap<HashBytes, SimpleLib, S> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        Ok(self.get(library_hash).map(|lib| lib.root.clone()))
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        Ok(self.get(library_hash).map(|lib| lib.root.as_ref()))
    }
}

struct SimpleLibRef<'tlb> {
    root: &'tlb DynCell,
}

impl<'a> Load<'a> for SimpleLibRef<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        slice.load_bit()?;
        Ok(Self {
            root: slice.load_reference()?,
        })
    }
}

impl EquivalentRepr<SimpleLib> for SimpleLibRef<'_> {}

/// Gas tracking context.
pub struct GasConsumer<'l> {
    /// Maximum possible value of the `limit`.
    gas_max: u64,
    /// Gas limit for the out-of-gas exception.
    gas_limit: std::cell::Cell<u64>,
    /// Free gas (e.g. for external messages without any balance).
    gas_credit: std::cell::Cell<u64>,
    /// Initial gas to compute the consumed amount.
    gas_base: std::cell::Cell<u64>,
    /// Remaining gas available.
    gas_remaining: std::cell::Cell<i64>,
    /// Gas price (fixed point with 16 bits for fractional part).
    gas_price: NonZeroU64,

    /// A set of visited cells.
    loaded_cells: std::cell::UnsafeCell<HashSet<HashBytes>>,
    /// Libraries provider.
    libraries: &'l dyn LibraryProvider,

    /// Number of signature checks.
    chksign_counter: std::cell::Cell<usize>,
    /// Free gas (can be paid when using isolated consumer).
    free_gas_consumed: std::cell::Cell<u64>,

    // Missing library in case of resolving error occured.
    missing_library: std::cell::Cell<Option<HashBytes>>,
}

impl<'l> GasConsumer<'l> {
    pub const BUILD_CELL_GAS: u64 = 500;
    pub const NEW_CELL_GAS: u64 = 100;
    pub const OLD_CELL_GAS: u64 = 25;

    pub const FREE_STACK_DEPTH: usize = 32;
    pub const FREE_SIGNATURE_CHECKS: usize = 10;
    pub const FREE_NESTED_CONT_JUMP: usize = 8;

    pub const STACK_VALUE_GAS_PRICE: u64 = 1;
    pub const TUPLE_ENTRY_GAS_PRICE: u64 = 1;
    pub const HASH_EXT_ENTRY_GAS_PRICE: u64 = 1;
    pub const CHK_SGN_GAS_PRICE: u64 = 4000;
    pub const IMPLICIT_JMPREF_GAS_PRICE: u64 = 10;
    pub const IMPLICIT_RET_GAS_PRICE: u64 = 5;
    pub const EXCEPTION_GAS_PRICE: u64 = 50;
    pub const RUNVM_GAS_PRICE: u64 = 40;

    pub fn new(params: GasParams) -> Self {
        static NO_LIBRARIES: NoLibraries = NoLibraries;

        Self::with_libraries(params, &NO_LIBRARIES)
    }

    pub fn with_libraries(params: GasParams, libraries: &'l dyn LibraryProvider) -> Self {
        let gas_remaining = truncate_gas(params.limit.saturating_add(params.credit));

        Self {
            gas_max: truncate_gas(params.max),
            gas_limit: std::cell::Cell::new(truncate_gas(params.limit)),
            gas_credit: std::cell::Cell::new(truncate_gas(params.credit)),
            gas_base: std::cell::Cell::new(gas_remaining),
            gas_remaining: std::cell::Cell::new(gas_remaining as i64),
            gas_price: NonZeroU64::new(params.price).unwrap_or(NonZeroU64::MIN),
            loaded_cells: Default::default(),
            libraries,
            chksign_counter: std::cell::Cell::new(0),
            free_gas_consumed: std::cell::Cell::new(0),
            missing_library: std::cell::Cell::new(None),
        }
    }

    // TODO: Consume free gas as non-free when `isolate`.
    pub fn derive(&mut self, params: GasConsumerDeriveParams) -> VmResult<ParentGasConsumer<'l>> {
        use std::cell::Cell;

        Ok(if params.isolate {
            // Pay for the free gas to prevent abuse.
            self.try_consume(self.free_gas_consumed.get())?;

            // NOTE: Compute remaining gas only when all operations
            //       with parent consumer are made.
            let gas_remaining = self.remaining();
            vm_ensure!(gas_remaining >= 0, OutOfGas);

            // Reset current free gas counters.
            self.chksign_counter.set(0);
            self.free_gas_consumed.set(0);

            // Create a new gas consumer.
            let params = GasParams {
                max: std::cmp::min(params.gas_max, gas_remaining as u64),
                limit: std::cmp::min(params.gas_limit, gas_remaining as u64),
                credit: 0,
                price: self.price(),
            };
            let libraries = self.libraries;

            ParentGasConsumer::Isolated(std::mem::replace(
                self,
                Self::with_libraries(params, libraries),
            ))
        } else {
            // NOTE: Compute remaining gas only when all operations
            //       with parent consumer are made.
            let gas_remaining = self.remaining();
            vm_ensure!(gas_remaining >= 0, OutOfGas);

            // Create child gas consumer params.
            let gas_max = std::cmp::min(params.gas_max, gas_remaining as u64);
            let gas_limit = std::cmp::min(params.gas_limit, gas_remaining as u64);

            // Move gas params from child to parent.
            ParentGasConsumer::Shared(GasConsumer {
                gas_max: std::mem::replace(&mut self.gas_max, gas_max),
                gas_limit: std::mem::replace(&mut self.gas_limit, Cell::new(gas_limit)),
                gas_credit: std::mem::replace(&mut self.gas_credit, Cell::new(0)),
                gas_base: std::mem::replace(&mut self.gas_base, Cell::new(gas_limit)),
                gas_remaining: std::mem::replace(
                    &mut self.gas_remaining,
                    Cell::new(gas_limit as i64),
                ),
                gas_price: self.gas_price,
                loaded_cells: Default::default(),
                libraries: self.libraries,
                chksign_counter: self.chksign_counter.clone(),
                free_gas_consumed: self.free_gas_consumed.clone(),
                missing_library: self.missing_library.clone(),
            })
        })
    }

    pub fn restore(&mut self, mut parent: ParentGasConsumer<'l>) -> RestoredGasConsumer {
        let meta = RestoredGasConsumer {
            gas_consumed: self.consumed(),
            gas_limit: self.limit(),
        };

        if let ParentGasConsumer::Shared(parent) = &mut parent {
            // Merge loaded cells.
            parent.loaded_cells = std::mem::take(&mut self.loaded_cells);
        }

        match parent {
            ParentGasConsumer::Isolated(mut parent) | ParentGasConsumer::Shared(mut parent) => {
                // Merge missing library.
                let missing_lib = self.missing_library.get_mut();
                let parent_lib = parent.missing_library.get_mut();
                if parent_lib.is_none() && missing_lib.is_some() {
                    *parent_lib = *missing_lib;
                }

                // Merge free gas counters.
                parent.chksign_counter = self.chksign_counter.clone();
                parent.free_gas_consumed = self.free_gas_consumed.clone();

                *self = parent
            }
        }

        meta
    }

    pub fn libraries(&self) -> &'l dyn LibraryProvider {
        self.libraries
    }

    pub fn credit(&self) -> u64 {
        self.gas_credit.get()
    }

    pub fn consumed(&self) -> u64 {
        (self.gas_base.get() as i64).saturating_sub(self.gas_remaining.get()) as u64
    }

    pub fn remaining(&self) -> i64 {
        self.gas_remaining.get()
    }

    pub fn base(&self) -> u64 {
        self.gas_base.get()
    }

    pub fn limit(&self) -> u64 {
        self.gas_limit.get()
    }

    pub fn set_limit(&self, limit: u64) {
        let limit = std::cmp::min(limit, self.gas_max);
        vm_log_trace!("changing gas limit: new_limit={limit}");

        self.gas_credit.set(0);
        self.gas_limit.set(limit);
        self.set_base(limit);
    }

    fn set_base(&self, mut base: u64) {
        base = truncate_gas(base);
        let diff = base as i64 - self.gas_base.get() as i64;
        self.gas_remaining.set(self.gas_remaining.get() + diff);
        self.gas_base.set(base);
    }

    pub fn price(&self) -> u64 {
        self.gas_price.get()
    }

    pub fn try_consume_exception_gas(&self) -> Result<(), Error> {
        self.try_consume(Self::EXCEPTION_GAS_PRICE)
    }

    pub fn try_consume_implicit_jmpref_gas(&self) -> Result<(), Error> {
        self.try_consume(Self::IMPLICIT_JMPREF_GAS_PRICE)
    }

    pub fn try_consume_implicit_ret_gas(&self) -> Result<(), Error> {
        self.try_consume(Self::IMPLICIT_RET_GAS_PRICE)
    }

    pub fn try_consume_check_signature_gas(&self) -> Result<(), Error> {
        self.chksign_counter.set(self.chksign_counter.get() + 1);
        if self.chksign_counter.get() > Self::FREE_SIGNATURE_CHECKS {
            self.try_consume(Self::CHK_SGN_GAS_PRICE)?;
        } else {
            self.consume_free_gas(Self::CHK_SGN_GAS_PRICE);
        }
        Ok(())
    }

    pub fn try_consume_stack_gas(&self, stack: Option<&SafeRc<Stack>>) -> Result<(), Error> {
        if let Some(stack) = stack {
            self.try_consume_stack_depth_gas(stack.depth())?;
        }
        Ok(())
    }

    pub fn try_consume_tuple_gas(&self, tuple_len: u64) -> Result<(), Error> {
        self.try_consume(tuple_len * Self::TUPLE_ENTRY_GAS_PRICE)?;
        Ok(())
    }

    pub fn try_consume_stack_depth_gas(&self, depth: usize) -> Result<(), Error> {
        self.try_consume(
            (std::cmp::max(depth, Self::FREE_STACK_DEPTH) - Self::FREE_STACK_DEPTH) as u64
                * Self::STACK_VALUE_GAS_PRICE,
        )
    }

    pub fn try_consume(&self, amount: u64) -> Result<(), Error> {
        let remaining = self
            .gas_remaining
            .get()
            .saturating_sub(truncate_gas(amount) as i64);
        self.gas_remaining.set(remaining);

        if remaining >= 0 {
            Ok(())
        } else {
            Err(Error::Cancelled)
        }
    }

    pub fn consume_free_gas(&self, amount: u64) {
        let consumed = truncate_gas(self.free_gas_consumed.get().saturating_add(amount));
        self.free_gas_consumed.set(consumed);
    }

    pub fn missing_library(&self) -> Option<HashBytes> {
        self.missing_library.get()
    }

    pub fn set_missing_library(&self, hash: &HashBytes) {
        self.missing_library.set(Some(*hash));
    }

    pub fn load_cell_as_slice(&self, cell: Cell, mode: LoadMode) -> Result<OwnedCellSlice, Error> {
        let cell = ok!(self.load_cell_impl(cell, mode));
        Ok(OwnedCellSlice::new_allow_exotic(cell))
    }

    fn load_cell_impl<'s: 'a, 'a, T: LoadLibrary<'a>>(
        &'s self,
        mut cell: T,
        mode: LoadMode,
    ) -> Result<T, Error> {
        let mut library_loaded = false;
        loop {
            if mode.use_gas() {
                // SAFETY: This is the only place where we borrow `loaded_cells` as mut.
                let is_new =
                    unsafe { (*self.loaded_cells.get()).insert(*cell.as_ref().repr_hash()) };

                ok!(self.try_consume(if is_new {
                    GasConsumer::NEW_CELL_GAS
                } else {
                    GasConsumer::OLD_CELL_GAS
                }));
            }

            if !mode.resolve() {
                return Ok(cell);
            }

            match cell.as_ref().cell_type() {
                CellType::Ordinary => return Ok(cell),
                CellType::LibraryReference if !library_loaded => {
                    // Library data structure is enforced by `CellContext::finalize_cell`.
                    debug_assert_eq!(cell.as_ref().bit_len(), 8 + 256);

                    // Find library by hash.
                    let mut library_hash = HashBytes::ZERO;
                    ok!(cell
                        .as_ref()
                        .as_slice_allow_exotic()
                        .get_raw(8, &mut library_hash.0, 256));

                    let Some(library_cell) = ok!(T::load_library(self, &library_hash)) else {
                        self.missing_library.set(Some(library_hash));
                        return Err(Error::CellUnderflow);
                    };

                    cell = library_cell;
                    library_loaded = true;
                }
                _ => return Err(Error::CellUnderflow),
            }
        }
    }
}

impl CellContext for GasConsumer<'_> {
    fn finalize_cell(&self, cell: CellParts<'_>) -> Result<Cell, Error> {
        ok!(self.try_consume(GasConsumer::BUILD_CELL_GAS));
        Cell::empty_context().finalize_cell(cell)
    }

    fn load_cell(&self, cell: Cell, mode: LoadMode) -> Result<Cell, Error> {
        self.load_cell_impl(cell, mode)
    }

    fn load_dyn_cell<'s: 'a, 'a>(
        &'s self,
        cell: &'a DynCell,
        mode: LoadMode,
    ) -> Result<&'a DynCell, Error> {
        self.load_cell_impl(cell, mode)
    }
}

trait LoadLibrary<'a>: AsRef<DynCell> + 'a {
    fn load_library(gas: &'a GasConsumer, library_hash: &HashBytes) -> Result<Option<Self>, Error>
    where
        Self: Sized;
}

impl<'a> LoadLibrary<'a> for &'a DynCell {
    fn load_library(gas: &'a GasConsumer, library_hash: &HashBytes) -> Result<Option<Self>, Error>
    where
        Self: Sized,
    {
        gas.libraries.find_ref(library_hash)
    }
}

impl LoadLibrary<'_> for Cell {
    fn load_library(gas: &'_ GasConsumer, library_hash: &HashBytes) -> Result<Option<Self>, Error>
    where
        Self: Sized,
    {
        gas.libraries.find(library_hash)
    }
}

/// Params to replace the current gas consumer.
#[derive(Debug, Clone, Copy)]
pub struct GasConsumerDeriveParams {
    pub gas_max: u64,
    pub gas_limit: u64,
    pub isolate: bool,
}

/// Parent of the derived gas consumer.
pub enum ParentGasConsumer<'l> {
    Isolated(GasConsumer<'l>),
    Shared(GasConsumer<'l>),
}

/// Info extracted when parent gas consumer is restored.
#[derive(Debug, Clone, Copy)]
pub struct RestoredGasConsumer {
    pub gas_consumed: u64,
    pub gas_limit: u64,
}

const fn truncate_gas(gas: u64) -> u64 {
    if gas <= i64::MAX as u64 {
        gas
    } else {
        i64::MAX as u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn find_lib_dict_ref() {
        let lib1 = Boc::decode(tvmasm!("NOP")).unwrap();
        let lib2 = Boc::decode(tvmasm!("NOP NOP")).unwrap();

        // Dict with SimpleLib
        let mut libraries = vec![
            (*lib1.repr_hash(), SimpleLib {
                public: true,
                root: lib1.clone(),
            }),
            (*lib2.repr_hash(), SimpleLib {
                public: true,
                root: lib2.clone(),
            }),
        ];
        libraries.sort_unstable_by(|(l, _), (r, _)| l.cmp(r));
        let libraries = Dict::<HashBytes, SimpleLib>::try_from_sorted_slice(&libraries).unwrap();

        assert!(libraries.find(&HashBytes::ZERO).unwrap().is_none());
        assert!(libraries.find_ref(&HashBytes::ZERO).unwrap().is_none());

        assert_eq!(
            libraries.find(lib1.repr_hash()).unwrap().unwrap().as_ref(),
            libraries.find_ref(lib1.repr_hash()).unwrap().unwrap()
        );
        assert_eq!(
            libraries.find(lib2.repr_hash()).unwrap().unwrap().as_ref(),
            libraries.find_ref(lib2.repr_hash()).unwrap().unwrap()
        );

        // Dict with LibDescr
        let mut publishers = Dict::new();
        publishers.add(HashBytes::ZERO, ()).unwrap();

        {
            let lib = LibDescr {
                lib: lib1.clone(),
                publishers: publishers.clone(),
            };
            let c = CellBuilder::build_from(&lib).unwrap();
            let parsed = c.parse::<LibDescr>().unwrap();

            assert_eq!(lib, parsed);
        }

        let mut libraries = vec![
            (*lib1.repr_hash(), LibDescr {
                lib: lib1.clone(),
                publishers: publishers.clone(),
            }),
            (*lib2.repr_hash(), LibDescr {
                lib: lib2.clone(),
                publishers,
            }),
        ];
        libraries.sort_unstable_by(|(l, _), (r, _)| l.cmp(r));

        let libraries = Dict::<HashBytes, LibDescr>::try_from_sorted_slice(&libraries).unwrap();

        assert!(libraries.find(&HashBytes::ZERO).unwrap().is_none());
        assert!(libraries.find_ref(&HashBytes::ZERO).unwrap().is_none());

        assert_eq!(
            libraries.find(lib1.repr_hash()).unwrap().unwrap().as_ref(),
            libraries.find_ref(lib1.repr_hash()).unwrap().unwrap()
        );
        assert_eq!(
            libraries.find(lib2.repr_hash()).unwrap().unwrap().as_ref(),
            libraries.find_ref(lib2.repr_hash()).unwrap().unwrap()
        );
    }
}
