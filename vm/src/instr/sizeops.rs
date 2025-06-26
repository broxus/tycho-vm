use num_traits::{Signed, ToPrimitive};
use tycho_types::cell::{LoadMode, RefsIter};
use tycho_types::error::Error;
use tycho_types::prelude::*;
use tycho_vm_proc::vm_module;

use crate::GasConsumer;
use crate::error::VmResult;
use crate::saferc::SafeRc;
use crate::stack::StackValueType;
use crate::state::VmState;

pub struct SizeOps;

#[vm_module]
impl SizeOps {
    #[op(code = "f940", fmt = "CDATASIZEQ", args(is_slice = false, q = true))]
    #[op(code = "f941", fmt = "CDATASIZE", args(is_slice = false, q = false))]
    #[op(code = "f942", fmt = "SDATASIZEQ", args(is_slice = true, q = true))]
    #[op(code = "f943", fmt = "SDATASIZE", args(is_slice = true, q = false))]
    pub fn exec_compute_data_size(st: &mut VmState, is_slice: bool, q: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let bound = ok!(stack.pop_int_or_nan());

        let value = if is_slice {
            ok!(stack.pop_cs()).into_dyn_value()
        } else {
            ok!(stack.pop_cell()).into_dyn_value()
        };
        let bound = match bound {
            Some(bound) if !bound.is_negative() => SafeRc::unwrap_or_clone(bound),
            _ => vm_bail!(IntegerOverflow),
        };
        let limit = bound.to_u64().unwrap_or(u64::MAX);
        let mut storage = StorageStatExt::with_limit(&st.gas, limit);

        let ok = if is_slice {
            let Some(slice) = value.as_cell_slice() else {
                vm_bail!(InvalidType {
                    expected: StackValueType::Slice,
                    actual: value.ty()
                })
            };
            let cs = slice.apply();
            ok!(storage.add_slice(&cs))
        } else {
            let Some(cell) = value.as_cell() else {
                vm_bail!(InvalidType {
                    expected: StackValueType::Cell,
                    actual: value.ty()
                })
            };
            ok!(storage.add_cell(cell.as_ref()))
        };

        if ok {
            ok!(stack.push_int(storage.stats.cell_count));
            ok!(stack.push_int(storage.stats.bit_count));
            ok!(stack.push_int(storage.stats.ref_count));
        } else if !q {
            vm_bail!(CellError(Error::CellOverflow));
        }

        if q {
            ok!(stack.push_bool(ok))
        }

        Ok(0)
    }
}

struct StorageStatExt<'a, 'c: 'a, 'l> {
    gas: &'c GasConsumer<'l>,
    visited: ahash::HashSet<&'a HashBytes>,
    stack: Vec<RefsIter<'a>>,
    stats: CellTreeStatsExt,
    limit: u64,
}

impl<'a, 'c: 'a, 'l> StorageStatExt<'a, 'c, 'l> {
    pub fn with_limit(gas: &'c GasConsumer<'l>, limit: u64) -> Self {
        Self {
            gas,
            visited: Default::default(),
            stack: Vec::new(),
            stats: Default::default(),
            limit,
        }
    }

    fn add_cell(&mut self, mut cell: &'a DynCell) -> VmResult<bool> {
        if !self.visited.insert(cell.repr_hash()) {
            return Ok(true);
        }
        if self.stats.cell_count >= self.limit {
            return Ok(false);
        }

        cell = self.gas.load_dyn_cell(cell, LoadMode::UseGas)?;

        let refs = cell.references();

        self.stats.bit_count += cell.bit_len() as u64;
        self.stats.ref_count += refs.len() as u64;
        self.stats.cell_count += 1;

        self.stack.clear();
        self.stack.push(refs);
        self.reduce_stack()
    }

    fn add_slice(&mut self, slice: &CellSlice<'a>) -> VmResult<bool> {
        let refs = slice.references();

        self.stats.bit_count += slice.size_bits() as u64;
        self.stats.ref_count += refs.len() as u64;

        self.stack.clear();
        self.stack.push(refs);
        self.reduce_stack()
    }

    fn reduce_stack(&mut self) -> VmResult<bool> {
        'outer: while let Some(item) = self.stack.last_mut() {
            for mut cell in item.by_ref() {
                if !self.visited.insert(cell.repr_hash()) {
                    continue;
                }

                if self.stats.cell_count >= self.limit {
                    return Ok(false);
                }

                cell = self.gas.load_dyn_cell(cell, LoadMode::UseGas)?;

                let next = cell.references();
                let ref_count = next.len();

                self.stats.bit_count += cell.bit_len() as u64;
                self.stats.ref_count += ref_count as u64;
                self.stats.cell_count += 1;

                if ref_count > 0 {
                    self.stack.push(next);
                    continue 'outer;
                }
            }

            self.stack.pop();
        }

        Ok(true)
    }
}

#[derive(Default)]
struct CellTreeStatsExt {
    bit_count: u64,
    ref_count: u64,
    cell_count: u64,
}

#[cfg(test)]
mod tests {
    use rand::Rng;
    use tracing_test::traced_test;
    use tycho_types::prelude::*;

    use crate::OwnedCellSlice;

    #[test]
    #[traced_test]
    fn data_size() {
        let empty_cell = Cell::default();
        assert_run_vm!("CDATASIZE", [cell empty_cell.clone(), int 10] => [int 1, int 0, int 0]);
        assert_run_vm!("CDATASIZE", [cell empty_cell.clone(), int 0] => [int 0], exit_code: 8);
        assert_run_vm!("CDATASIZEQ", [cell empty_cell.clone(), int 10] => [int 1, int 0, int 0, int -1]);
        assert_run_vm!("CDATASIZEQ", [cell empty_cell.clone(), int 0] => [int 0]);
        assert_run_vm!("CDATASIZEQ", [cell empty_cell.clone(), nan] => [int 0], exit_code: 4);

        let empty_slice = OwnedCellSlice::new_allow_exotic(empty_cell);
        assert_run_vm!("SDATASIZE", [slice empty_slice.clone(), int 10] => [int 0, int 0, int 0]);
        assert_run_vm!("SDATASIZE", [slice empty_slice.clone(), int 0] => [int 0, int 0, int 0]);
        assert_run_vm!("SDATASIZEQ", [slice empty_slice.clone(), int 10] => [int 0, int 0, int 0, int -1]);
        assert_run_vm!("SDATASIZEQ", [slice empty_slice, int 0] => [int 0, int 0, int 0, int -1]);

        let plain_cell = CellBuilder::build_from((123u8, 123123123u32, false)).unwrap();
        assert_run_vm!("CDATASIZE", [cell plain_cell.clone(), int 1] => [int 1, int 8 + 32 + 1, int 0]);
        assert_run_vm!("CDATASIZEQ", [cell plain_cell.clone(), int 1] => [int 1, int 8 + 32 + 1, int 0, int -1]);

        let plain_slice = OwnedCellSlice::new_allow_exotic(plain_cell);
        assert_run_vm!("SDATASIZE", [slice plain_slice.clone(), int 1] => [int 0, int 8 + 32 + 1, int 0]);
        assert_run_vm!("SDATASIZEQ", [slice plain_slice.clone(), int 1] => [int 0, int 8 + 32 + 1, int 0, int -1]);

        let one_ref_cell =
            CellBuilder::build_from((123u8, 123123123u32, false, Cell::default())).unwrap();
        assert_run_vm!("CDATASIZE", [cell one_ref_cell.clone(), int 2] => [int 2, int 8 + 32 + 1, int 1]);
        assert_run_vm!("CDATASIZEQ", [cell one_ref_cell.clone(), int 2] => [int 2, int 8 + 32 + 1, int 1, int -1]);
        assert_run_vm!("CDATASIZE", [cell one_ref_cell.clone(), int 1] => [int 0], exit_code: 8);
        assert_run_vm!("CDATASIZEQ", [cell one_ref_cell.clone(), int 1] => [int 0]);

        let one_ref_slice = OwnedCellSlice::new_allow_exotic(one_ref_cell);
        assert_run_vm!("SDATASIZE", [slice one_ref_slice.clone(), int 1] => [int 1, int 8 + 32 + 1, int 1]);
        assert_run_vm!("SDATASIZEQ", [slice one_ref_slice.clone(), int 1] => [int 1, int 8 + 32 + 1, int 1, int -1]);
        assert_run_vm!("SDATASIZE", [slice one_ref_slice.clone(), int 0] => [int 0], exit_code: 8);
        assert_run_vm!("SDATASIZEQ", [slice one_ref_slice.clone(), int 0] => [int 0]);

        let mut deep_cell = CellBuilder::build_from(HashBytes::ZERO).unwrap();
        for _ in 0..100 {
            deep_cell = CellBuilder::build_from((
                deep_cell.clone(),
                deep_cell.clone(),
                deep_cell.clone(),
                deep_cell.clone(),
            ))
            .unwrap();
        }
        assert_run_vm!("CDATASIZE", [cell deep_cell.clone(), int 101] => [int 101, int 256, int 100 * 4]);
        assert_run_vm!("CDATASIZEQ", [cell deep_cell.clone(), int 100] => [int 0]);

        let deep_slice = OwnedCellSlice::new_allow_exotic(deep_cell);
        assert_run_vm!("SDATASIZE", [slice deep_slice.clone(), int 100] => [int 100, int 256, int 100 * 4]);
        assert_run_vm!("SDATASIZEQ", [slice deep_slice.clone(), int 99] => [int 0]);

        fn make_huge_cell(rng: &mut impl Rng, depth: u8) -> Cell {
            if depth == 0 {
                CellBuilder::build_from(rng.random::<HashBytes>()).unwrap()
            } else {
                CellBuilder::build_from((
                    rng.random::<HashBytes>(),
                    make_huge_cell(rng, depth - 1),
                    make_huge_cell(rng, depth - 1),
                ))
                .unwrap()
            }
        }
        let huge_cell = make_huge_cell(&mut rand::rng(), 10);
        assert_run_vm!("CDATASIZE", [cell huge_cell.clone(), int 2048] => [int 2047, int 524032, int 2046]);
        assert_run_vm!("CDATASIZEQ", [cell huge_cell.clone(), int 100] => [int 0]);
        assert_run_vm!("CDATASIZE", gas: 10000, [cell huge_cell.clone(), int 2048] => [int 10026], exit_code: -14);
        assert_run_vm!("CDATASIZEQ", gas: 10000, [cell huge_cell.clone(), int 2048] => [int 10026], exit_code: -14);

        let huge_slice = OwnedCellSlice::new_allow_exotic(huge_cell);
        assert_run_vm!("SDATASIZE", [slice huge_slice.clone(), int 2048] => [int 2046, int 524032, int 2046]);
        assert_run_vm!("SDATASIZEQ", [slice huge_slice.clone(), int 100] => [int 0]);
        assert_run_vm!("SDATASIZE", gas: 10000, [slice huge_slice.clone(), int 2048] => [int 10026], exit_code: -14);
        assert_run_vm!("SDATASIZEQ", gas: 10000, [slice huge_slice.clone(), int 2048] => [int 10026], exit_code: -14);
    }
}
