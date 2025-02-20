use std::collections::BTreeMap;

use anyhow::Result;
use everscale_types::prelude::*;

use crate::error::VmResult;
use crate::state::VmState;

/// Opcode description.
pub trait Opcode: Send + Sync {
    /// Opcode range aligned to 24 bits.
    fn range(&self) -> (u32, u32);

    /// Execute this opcode.
    fn dispatch(&self, st: &mut VmState, opcode: u32, bits: u16) -> VmResult<i32>;
}

/// Code page.
pub struct DispatchTable {
    id: u16,
    opcodes: Vec<(u32, Box<dyn Opcode>)>,
}

impl DispatchTable {
    pub fn builder(id: u16) -> Opcodes {
        Opcodes {
            id,
            opcodes: Default::default(),
        }
    }

    #[inline]
    pub fn id(&self) -> u16 {
        self.id
    }

    pub fn lookup(&self, opcode: u32) -> &dyn Opcode {
        debug_assert!(!self.opcodes.is_empty());

        let mut i = 0;
        let mut j = self.opcodes.len();
        while j - i > 1 {
            let k = (j + i) >> 1;
            if self.opcodes[k].0 <= opcode {
                i = k;
            } else {
                j = k;
            }
        }
        self.opcodes[i].1.as_ref()
    }

    pub fn dispatch(&self, st: &mut VmState) -> VmResult<i32> {
        let (opcode, bits) = Self::get_opcode_from_slice(&st.code.apply());
        let op = self.lookup(opcode);
        op.dispatch(st, opcode, bits)
    }

    fn get_opcode_from_slice(slice: &CellSlice<'_>) -> (u32, u16) {
        let bits = std::cmp::min(MAX_OPCODE_BITS, slice.size_bits());
        let opcode = (slice.get_uint(0, bits).unwrap() as u32) << (MAX_OPCODE_BITS - bits);
        (opcode, bits)
    }
}

/// A builder for [`DispatchTable`].
pub struct Opcodes {
    id: u16,
    opcodes: BTreeMap<u32, Box<dyn Opcode>>,
}

impl Opcodes {
    pub fn build(self) -> DispatchTable {
        let mut opcodes = Vec::with_capacity(self.opcodes.len() * 2 + 1);

        let mut upto = 0;
        for (k, opcode) in self.opcodes {
            let (min, max) = opcode.range();
            if min > upto {
                opcodes.push((
                    upto,
                    Box::new(DummyOpcode {
                        opcode_min: upto,
                        opcode_max: min,
                    }) as Box<_>,
                ));
            }

            opcodes.push((k, opcode));
            upto = max;
        }

        if upto < MAX_OPCODE {
            opcodes.push((
                upto,
                Box::new(DummyOpcode {
                    opcode_min: upto,
                    opcode_max: MAX_OPCODE,
                }),
            ));
        }

        opcodes.shrink_to_fit();

        DispatchTable {
            id: self.id,
            opcodes,
        }
    }

    pub fn add_simple(&mut self, opcode: u32, bits: u16, exec: FnExecInstrSimple) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - bits;
        self.add_opcode(Box::new(SimpleOpcode {
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            opcode_bits: bits,
            exec,
        }))
    }

    pub fn add_fixed(
        &mut self,
        opcode: u32,
        opcode_bits: u16,
        arg_bits: u16,
        exec: FnExecInstrArg,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - opcode_bits;
        self.add_opcode(Box::new(FixedOpcode {
            exec,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            total_bits: opcode_bits + arg_bits,
        }))
    }

    pub fn add_fixed_range(
        &mut self,
        opcode_min: u32,
        opcode_max: u32,
        total_bits: u16,
        _arg_bits: u16,
        exec: FnExecInstrArg,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - total_bits;
        self.add_opcode(Box::new(FixedOpcode {
            exec,
            opcode_min: opcode_min << remaining_bits,
            opcode_max: opcode_max << remaining_bits,
            total_bits,
        }))
    }

    pub fn add_ext(
        &mut self,
        opcode: u32,
        opcode_bits: u16,
        arg_bits: u16,
        exec: FnExecInstrFull,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - opcode_bits;
        self.add_opcode(Box::new(ExtOpcode {
            exec,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            total_bits: opcode_bits + arg_bits,
        }))
    }

    pub fn add_ext_range(
        &mut self,
        opcode_min: u32,
        opcode_max: u32,
        total_bits: u16,
        exec: FnExecInstrFull,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - total_bits;
        self.add_opcode(Box::new(ExtOpcode {
            exec,
            opcode_min: opcode_min << remaining_bits,
            opcode_max: opcode_max << remaining_bits,
            total_bits,
        }))
    }

    pub fn add_opcode(&mut self, opcode: Box<dyn Opcode>) -> Result<()> {
        let (min, max) = opcode.range();
        debug_assert!(min < max);
        debug_assert!(max <= MAX_OPCODE);

        if let Some((other_min, _)) = self.opcodes.range(min..).next() {
            anyhow::ensure!(
                max <= *other_min,
                "Opcode overlaps with next min: {other_min:06x}"
            );
        }

        if let Some((k, prev)) = self.opcodes.range(..=min).next_back() {
            let (prev_min, prev_max) = prev.range();
            debug_assert!(prev_min < prev_max);
            debug_assert!(prev_min == *k);
            anyhow::ensure!(
                prev_max <= min,
                "Opcode overlaps with prev max: {prev_max:06x}"
            );
        }

        self.opcodes.insert(min, opcode);
        Ok(())
    }
}

// === Opcodes ===

struct DummyOpcode {
    opcode_min: u32,
    opcode_max: u32,
}

impl Opcode for DummyOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }

    fn dispatch(&self, st: &mut VmState, _: u32, _: u16) -> VmResult<i32> {
        st.gas.try_consume(GAS_PER_INSTRUCTION)?;
        vm_bail!(InvalidOpcode);
    }
}

struct SimpleOpcode {
    exec: FnExecInstrSimple,
    opcode_min: u32,
    opcode_max: u32,
    opcode_bits: u16,
}

impl Opcode for SimpleOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }

    fn dispatch(&self, st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        st.gas
            .try_consume(GAS_PER_INSTRUCTION + self.opcode_bits as u64 * GAS_PER_BIT)?;
        vm_ensure!(bits >= self.opcode_bits, InvalidOpcode);
        st.code.range_mut().skip_first(self.opcode_bits, 0)?;
        (self.exec)(st)
    }
}

struct FixedOpcode {
    exec: FnExecInstrArg,
    opcode_min: u32,
    opcode_max: u32,
    total_bits: u16,
}

impl Opcode for FixedOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }

    fn dispatch(&self, st: &mut VmState, opcode: u32, bits: u16) -> VmResult<i32> {
        st.gas
            .try_consume(GAS_PER_INSTRUCTION + self.total_bits as u64 * GAS_PER_BIT)?;
        vm_ensure!(bits >= self.total_bits, InvalidOpcode);
        st.code.range_mut().skip_first(self.total_bits, 0)?;
        (self.exec)(st, opcode >> (MAX_OPCODE_BITS - self.total_bits))
    }
}

struct ExtOpcode {
    exec: FnExecInstrFull,
    opcode_min: u32,
    opcode_max: u32,
    total_bits: u16,
}

impl Opcode for ExtOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }

    fn dispatch(&self, st: &mut VmState, opcode: u32, bits: u16) -> VmResult<i32> {
        st.gas
            .try_consume(GAS_PER_INSTRUCTION + self.total_bits as u64 * GAS_PER_BIT)?;
        vm_ensure!(bits >= self.total_bits, InvalidOpcode);
        (self.exec)(
            st,
            opcode >> (MAX_OPCODE_BITS - self.total_bits),
            self.total_bits,
        )
    }
}

/// Fn pointer for a simple opcode.
pub type FnExecInstrSimple = fn(&mut VmState) -> VmResult<i32>;

/// Fn pointer for an opcode with a single argument.
pub type FnExecInstrArg = fn(&mut VmState, u32) -> VmResult<i32>;

/// Fn pointer for an extended opcode.
pub type FnExecInstrFull = fn(&mut VmState, u32, u16) -> VmResult<i32>;

const MAX_OPCODE_BITS: u16 = 24;
const MAX_OPCODE: u32 = 1 << MAX_OPCODE_BITS;

const GAS_PER_INSTRUCTION: u64 = 10;
const GAS_PER_BIT: u64 = 1;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cont::QuitCont;
    use crate::error::VmError;
    use crate::gas::{GasConsumer, GasParams};
    use crate::saferc::SafeRc;
    use crate::smc_info::VmVersion;

    #[test]
    fn dummy_codepage() {
        let cp = DispatchTable::builder(123).build();

        let mut state = VmState {
            code: Default::default(),
            throw_on_code_access: false,
            stack: Default::default(),
            cr: Default::default(),
            commited_state: Default::default(),
            steps: 0,
            quit0: SafeRc::from(QuitCont { exit_code: 0 }),
            quit1: SafeRc::from(QuitCont { exit_code: 0 }),
            gas: GasConsumer::new(GasParams::getter()),
            cp: Box::leak(Box::new(cp)),
            debug: None,
            modifiers: Default::default(),
            version: VmVersion::LATEST_TON,
        };

        let dummy = state.cp.lookup(0x800000);
        assert_eq!(dummy.range(), (0x000000, 0x1000000));

        let err = dummy.dispatch(&mut state, 0x800000, 24).unwrap_err();
        assert!(matches!(*err, VmError::InvalidOpcode));
    }

    #[test]
    fn opcode_overlap_check_works() {
        // Simple overlap
        {
            let mut cp = DispatchTable::builder(123);
            cp.add_simple(0xab, 8, |_| Ok(0)).unwrap();
            cp.add_simple(0xab, 8, |_| Ok(0)).unwrap_err();
        }

        // Range-simple overlap
        {
            let mut cp = DispatchTable::builder(123);
            cp.add_simple(0xab, 8, |_| Ok(0)).unwrap();
            cp.add_fixed_range(0xa0, 0xaf, 8, 4, |_, _| Ok(0))
                .unwrap_err();
        }

        // Simple-range overlap
        {
            let mut cp = DispatchTable::builder(123);
            cp.add_fixed_range(0xa0, 0xaf, 8, 4, |_, _| Ok(0)).unwrap();
            cp.add_simple(0xab, 8, |_| Ok(0)).unwrap_err();
        }

        // Range-range overlap
        {
            let mut cp = DispatchTable::builder(123);
            cp.add_fixed_range(0xa0, 0xaf, 8, 4, |_, _| Ok(0)).unwrap();
            cp.add_fixed_range(0xa4, 0xa7, 8, 2, |_, _| Ok(0))
                .unwrap_err();
        }
    }
}
