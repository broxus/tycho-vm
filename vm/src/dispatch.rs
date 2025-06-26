use std::collections::BTreeMap;

use anyhow::Result;
use tycho_types::prelude::*;

use crate::error::VmResult;
#[cfg(feature = "dump")]
use crate::error::{DumpError, DumpResult};
use crate::state::VmState;

pub trait OpcodeBase: Send + Sync {
    /// Opcode range aligned to 24 bits.
    fn range(&self) -> (u32, u32);
}

/// Opcode description.
pub trait OpcodeExec: OpcodeBase {
    /// Execute this opcode.
    fn exec(&self, st: &mut VmState, opcode: u32, bits: u16) -> VmResult<i32>;
}

/// Opcode description.
#[cfg(feature = "dump")]
pub trait OpcodeDump: OpcodeBase {
    /// Dump this opcode.
    fn dump(
        &self,
        code: &mut CellSlice<'_>,
        opcode: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult;
}

/// Dump output visitor.
#[cfg(feature = "dump")]
pub trait DumpOutput {
    fn record_gas(&mut self, gas: u64) -> DumpResult;
    fn record_opcode(&mut self, value: &dyn std::fmt::Display) -> DumpResult;
    fn record_cell(&mut self, value: Cell) -> DumpResult;
    fn record_slice(&mut self, value: CellSlice<'_>) -> DumpResult;
    fn record_cont(&mut self, cont: Cell) -> DumpResult;
    fn record_cont_slice(&mut self, cont: CellSlice<'_>) -> DumpResult;
    fn record_dict(&mut self, n: u16, slice: CellSlice<'_>) -> DumpResult;
}

/// Code page.
pub struct DispatchTable {
    id: u16,
    exec_opcodes: Vec<(u32, Box<dyn OpcodeExec>)>,
    #[cfg(feature = "dump")]
    dump_opcodes: Vec<(u32, Box<dyn OpcodeDump>)>,
}

impl DispatchTable {
    pub fn builder(id: u16) -> Opcodes {
        Opcodes {
            id,
            exec_opcodes: Default::default(),
            #[cfg(feature = "dump")]
            dump_opcodes: Default::default(),
        }
    }

    #[inline]
    pub fn id(&self) -> u16 {
        self.id
    }

    pub fn lookup(&self, opcode: u32) -> &dyn OpcodeExec {
        Self::lookup_impl(opcode, &self.exec_opcodes)
    }

    pub fn dispatch(&self, st: &mut VmState) -> VmResult<i32> {
        let (opcode, bits) = Self::get_opcode_from_slice(&st.code.apply());
        let op = self.lookup(opcode);
        op.exec(st, opcode, bits)
    }

    #[cfg(feature = "dump")]
    pub fn dispatch_dump(&self, code: &mut CellSlice<'_>, f: &mut dyn DumpOutput) -> DumpResult {
        let (opcode, bits) = Self::get_opcode_from_slice(code);
        let op = Self::lookup_impl(opcode, &self.dump_opcodes);
        op.dump(code, opcode, bits, f)
    }

    fn get_opcode_from_slice(slice: &CellSlice<'_>) -> (u32, u16) {
        let bits = std::cmp::min(MAX_OPCODE_BITS, slice.size_bits());
        let opcode = (slice.get_uint(0, bits).unwrap() as u32) << (MAX_OPCODE_BITS - bits);
        (opcode, bits)
    }

    #[inline]
    fn lookup_impl<T, V>(opcode: u32, opcodes: &[(u32, T)]) -> &V
    where
        T: AsRef<V>,
        V: ?Sized,
    {
        debug_assert!(!opcodes.is_empty());

        let mut i = 0;
        let mut j = opcodes.len();
        while j - i > 1 {
            let k = (j + i) >> 1;
            if opcodes[k].0 <= opcode {
                i = k;
            } else {
                j = k;
            }
        }
        opcodes[i].1.as_ref()
    }
}

/// A builder for [`DispatchTable`].
pub struct Opcodes {
    id: u16,
    exec_opcodes: BTreeMap<u32, Box<dyn OpcodeExec>>,
    #[cfg(feature = "dump")]
    dump_opcodes: BTreeMap<u32, Box<dyn OpcodeDump>>,
}

impl Opcodes {
    pub fn build(self) -> DispatchTable {
        let exec_opcodes = build_opcodes(self.exec_opcodes, |min, max| {
            Box::new(DummyOpcode {
                opcode_min: min,
                opcode_max: max,
            })
        });

        #[cfg(feature = "dump")]
        let dump_opcodes = build_opcodes(self.dump_opcodes, |min, max| {
            Box::new(DummyOpcode {
                opcode_min: min,
                opcode_max: max,
            })
        });

        DispatchTable {
            id: self.id,
            exec_opcodes,
            #[cfg(feature = "dump")]
            dump_opcodes,
        }
    }

    pub fn add_simple(
        &mut self,
        opcode: u32,
        bits: u16,
        exec: FnExecInstrSimple,
        #[cfg(feature = "dump")] dump: FnDumpInstrSimple,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - bits;

        #[cfg(feature = "dump")]
        self.add_dump_opcode(Box::new(SimpleOpcode {
            f: dump,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            opcode_bits: bits,
        }))?;

        self.add_opcode(Box::new(SimpleOpcode {
            f: exec,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            opcode_bits: bits,
        }))
    }

    pub fn add_fixed(
        &mut self,
        opcode: u32,
        opcode_bits: u16,
        arg_bits: u16,
        exec: FnExecInstrArg,
        #[cfg(feature = "dump")] dump: FnDumpInstrArg,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - opcode_bits;

        #[cfg(feature = "dump")]
        self.add_dump_opcode(Box::new(FixedOpcode {
            f: dump,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            total_bits: opcode_bits + arg_bits,
        }))?;

        self.add_opcode(Box::new(FixedOpcode {
            f: exec,
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
        #[cfg(feature = "dump")] dump: FnDumpInstrArg,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - total_bits;

        #[cfg(feature = "dump")]
        self.add_dump_opcode(Box::new(FixedOpcode {
            f: dump,
            opcode_min: opcode_min << remaining_bits,
            opcode_max: opcode_max << remaining_bits,
            total_bits,
        }))?;

        self.add_opcode(Box::new(FixedOpcode {
            f: exec,
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
        #[cfg(feature = "dump")] dump: FnDumpInstrFull,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - opcode_bits;

        #[cfg(feature = "dump")]
        self.add_dump_opcode(Box::new(ExtOpcode {
            f: dump,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            total_bits: opcode_bits + arg_bits,
        }))?;

        self.add_opcode(Box::new(ExtOpcode {
            f: exec,
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
        #[cfg(feature = "dump")] dump: FnDumpInstrFull,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - total_bits;

        #[cfg(feature = "dump")]
        self.add_dump_opcode(Box::new(ExtOpcode {
            f: dump,
            opcode_min: opcode_min << remaining_bits,
            opcode_max: opcode_max << remaining_bits,
            total_bits,
        }))?;

        self.add_opcode(Box::new(ExtOpcode {
            f: exec,
            opcode_min: opcode_min << remaining_bits,
            opcode_max: opcode_max << remaining_bits,
            total_bits,
        }))
    }

    pub fn add_opcode(&mut self, opcode: Box<dyn OpcodeExec>) -> Result<()> {
        Self::add_opcode_impl(opcode, &mut self.exec_opcodes)
    }

    #[cfg(feature = "dump")]
    pub fn add_dump_opcode(&mut self, opcode: Box<dyn OpcodeDump>) -> Result<()> {
        Self::add_opcode_impl(opcode, &mut self.dump_opcodes)
    }

    #[inline]
    fn add_opcode_impl<T: OpcodeBase + ?Sized>(
        opcode: Box<T>,
        opcodes: &mut BTreeMap<u32, Box<T>>,
    ) -> Result<()> {
        let (min, max) = opcode.range();
        debug_assert!(min < max);
        debug_assert!(max <= MAX_OPCODE);

        if let Some((other_min, _)) = opcodes.range(min..).next() {
            anyhow::ensure!(
                max <= *other_min,
                "Opcode overlaps with next min: {other_min:06x}"
            );
        }

        if let Some((k, prev)) = opcodes.range(..=min).next_back() {
            let (prev_min, prev_max) = prev.range();
            debug_assert!(prev_min < prev_max);
            debug_assert!(prev_min == *k);
            anyhow::ensure!(
                prev_max <= min,
                "Opcode overlaps with prev max: {prev_max:06x}"
            );
        }

        opcodes.insert(min, opcode);
        Ok(())
    }
}

fn build_opcodes<T, F>(items: BTreeMap<u32, Box<T>>, f: F) -> Vec<(u32, Box<T>)>
where
    T: OpcodeBase + ?Sized,
    F: Fn(u32, u32) -> Box<T>,
{
    let mut opcodes = Vec::with_capacity(items.len() * 2 + 1);

    let mut upto = 0;
    for (k, opcode) in items {
        let (min, max) = opcode.range();
        if min > upto {
            opcodes.push((upto, f(upto, min)));
        }

        opcodes.push((k, opcode));
        upto = max;
    }

    if upto < MAX_OPCODE {
        opcodes.push((upto, f(upto, MAX_OPCODE)));
    }

    opcodes.shrink_to_fit();
    opcodes
}

// === Opcodes ===

struct DummyOpcode {
    opcode_min: u32,
    opcode_max: u32,
}

impl OpcodeBase for DummyOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }
}

impl OpcodeExec for DummyOpcode {
    fn exec(&self, st: &mut VmState, _: u32, _: u16) -> VmResult<i32> {
        st.gas.try_consume(GAS_PER_INSTRUCTION)?;
        vm_bail!(InvalidOpcode);
    }
}

#[cfg(feature = "dump")]
impl OpcodeDump for DummyOpcode {
    fn dump(&self, _: &mut CellSlice<'_>, _: u32, _: u16, _: &mut dyn DumpOutput) -> DumpResult {
        Err(DumpError::InvalidOpcode)
    }
}

struct SimpleOpcode<T> {
    f: T,
    opcode_min: u32,
    opcode_max: u32,
    opcode_bits: u16,
}

impl<T: Send + Sync> OpcodeBase for SimpleOpcode<T> {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }
}

impl OpcodeExec for SimpleOpcode<FnExecInstrSimple> {
    fn exec(&self, st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        st.gas.try_consume(opcode_gas(self.opcode_bits))?;
        vm_ensure!(bits >= self.opcode_bits, InvalidOpcode);
        st.code.range_mut().skip_first(self.opcode_bits, 0)?;
        (self.f)(st)
    }
}

#[cfg(feature = "dump")]
impl OpcodeDump for SimpleOpcode<FnDumpInstrSimple> {
    fn dump(
        &self,
        code: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        if bits >= self.opcode_bits {
            f.record_gas(opcode_gas(self.opcode_bits))?;
            code.skip_first(self.opcode_bits, 0)?;
            (self.f)(f)
        } else {
            Err(DumpError::InvalidOpcode)
        }
    }
}

struct FixedOpcode<T> {
    f: T,
    opcode_min: u32,
    opcode_max: u32,
    total_bits: u16,
}

impl<T: Send + Sync> OpcodeBase for FixedOpcode<T> {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }
}

impl OpcodeExec for FixedOpcode<FnExecInstrArg> {
    fn exec(&self, st: &mut VmState, opcode: u32, bits: u16) -> VmResult<i32> {
        st.gas.try_consume(opcode_gas(self.total_bits))?;
        vm_ensure!(bits >= self.total_bits, InvalidOpcode);
        st.code.range_mut().skip_first(self.total_bits, 0)?;
        (self.f)(st, opcode >> (MAX_OPCODE_BITS - self.total_bits))
    }
}

#[cfg(feature = "dump")]
impl OpcodeDump for FixedOpcode<FnDumpInstrArg> {
    fn dump(
        &self,
        code: &mut CellSlice<'_>,
        opcode: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        if bits >= self.total_bits {
            f.record_gas(opcode_gas(self.total_bits))?;
            code.skip_first(self.total_bits, 0)?;
            (self.f)(opcode >> (MAX_OPCODE_BITS - self.total_bits), f)
        } else {
            Err(DumpError::InvalidOpcode)
        }
    }
}

struct ExtOpcode<T> {
    f: T,
    opcode_min: u32,
    opcode_max: u32,
    total_bits: u16,
}

impl<T: Send + Sync> OpcodeBase for ExtOpcode<T> {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }
}

impl OpcodeExec for ExtOpcode<FnExecInstrFull> {
    fn exec(&self, st: &mut VmState, opcode: u32, bits: u16) -> VmResult<i32> {
        st.gas.try_consume(opcode_gas(self.total_bits))?;
        vm_ensure!(bits >= self.total_bits, InvalidOpcode);
        (self.f)(
            st,
            opcode >> (MAX_OPCODE_BITS - self.total_bits),
            self.total_bits,
        )
    }
}

#[cfg(feature = "dump")]
impl OpcodeDump for ExtOpcode<FnDumpInstrFull> {
    fn dump(
        &self,
        code: &mut CellSlice<'_>,
        opcode: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        if bits >= self.total_bits {
            f.record_gas(opcode_gas(self.total_bits))?;
            (self.f)(
                code,
                opcode >> (MAX_OPCODE_BITS - self.total_bits),
                self.total_bits,
                f,
            )
        } else {
            Err(DumpError::InvalidOpcode)
        }
    }
}

const fn opcode_gas(bits: u16) -> u64 {
    GAS_PER_INSTRUCTION + bits as u64 * GAS_PER_BIT
}

/// Fn pointer for a simple opcode execution logic.
pub type FnExecInstrSimple = fn(&mut VmState) -> VmResult<i32>;

/// Fn pointer for a simple opcode dump logic.
#[cfg(feature = "dump")]
pub type FnDumpInstrSimple = fn(&mut dyn DumpOutput) -> DumpResult;

/// Fn pointer for an opcode execution logic with a single argument.
pub type FnExecInstrArg = fn(&mut VmState, u32) -> VmResult<i32>;

/// Fn pointer for an opcode dump logic with a single argument.
#[cfg(feature = "dump")]
pub type FnDumpInstrArg = fn(u32, &mut dyn DumpOutput) -> DumpResult;

/// Fn pointer for an extended opcode execution logic.
pub type FnExecInstrFull = fn(&mut VmState, u32, u16) -> VmResult<i32>;

/// Fn pointer for an extended opcode dump logic.
#[cfg(feature = "dump")]
pub type FnDumpInstrFull = fn(&mut CellSlice<'_>, u32, u16, &mut dyn DumpOutput) -> DumpResult;

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
            committed_state: Default::default(),
            steps: 0,
            quit0: SafeRc::from(QuitCont { exit_code: 0 }),
            quit1: SafeRc::from(QuitCont { exit_code: 0 }),
            gas: GasConsumer::new(GasParams::getter()),
            cp: Box::leak(Box::new(cp)),
            debug: None,
            modifiers: Default::default(),
            version: VmVersion::LATEST_TON,
            parent: None,
        };

        let dummy = state.cp.lookup(0x800000);
        assert_eq!(dummy.range(), (0x000000, 0x1000000));

        let err = dummy.exec(&mut state, 0x800000, 24).unwrap_err();
        assert!(matches!(*err, VmError::InvalidOpcode));
    }

    #[test]
    fn opcode_overlap_check_works() {
        // Simple overlap
        {
            let mut cp = DispatchTable::builder(123);
            cp.add_simple(
                0xab,
                8,
                |_| Ok(0),
                #[cfg(feature = "dump")]
                |_| Ok(()),
            )
            .unwrap();
            cp.add_simple(
                0xab,
                8,
                |_| Ok(0),
                #[cfg(feature = "dump")]
                |_| Ok(()),
            )
            .unwrap_err();
        }

        // Range-simple overlap
        {
            let mut cp = DispatchTable::builder(123);
            cp.add_simple(
                0xab,
                8,
                |_| Ok(0),
                #[cfg(feature = "dump")]
                |_| Ok(()),
            )
            .unwrap();
            cp.add_fixed_range(
                0xa0,
                0xaf,
                8,
                4,
                |_, _| Ok(0),
                #[cfg(feature = "dump")]
                |_, _| Ok(()),
            )
            .unwrap_err();
        }

        // Simple-range overlap
        {
            let mut cp = DispatchTable::builder(123);
            cp.add_fixed_range(
                0xa0,
                0xaf,
                8,
                4,
                |_, _| Ok(0),
                #[cfg(feature = "dump")]
                |_, _| Ok(()),
            )
            .unwrap();
            cp.add_simple(
                0xab,
                8,
                |_| Ok(0),
                #[cfg(feature = "dump")]
                |_| Ok(()),
            )
            .unwrap_err();
        }

        // Range-range overlap
        {
            let mut cp = DispatchTable::builder(123);
            cp.add_fixed_range(
                0xa0,
                0xaf,
                8,
                4,
                |_, _| Ok(0),
                #[cfg(feature = "dump")]
                |_, _| Ok(()),
            )
            .unwrap();
            cp.add_fixed_range(
                0xa4,
                0xa7,
                8,
                2,
                |_, _| Ok(0),
                #[cfg(feature = "dump")]
                |_, _| Ok(()),
            )
            .unwrap_err();
        }
    }
}
