#[cfg(feature = "dump")]
use everscale_types::prelude::*;
use tycho_vm_proc::vm_module;

#[cfg(feature = "dump")]
use crate::dispatch::DumpOutput;
use crate::error::VmResult;
#[cfg(feature = "dump")]
use crate::error::{DumpError, DumpResult};
use crate::state::VmState;

pub struct DebugOps;

// TODO: Decide whether to panic on debug write errors

#[vm_module]
impl DebugOps {
    #[op(code = "fe00", fmt = "DUMPSTK")]
    fn exec_dump_stack(st: &mut VmState) -> VmResult<i32> {
        let Some(debug) = &mut st.debug else {
            return Ok(0);
        };

        let mut depth = st.stack.depth();
        write!(&mut *debug, "#DEBUG#: stack({depth} values) :").unwrap();
        if depth > 255 {
            write!(&mut *debug, " ...").unwrap();
            depth = 255;
        }

        for value in st.stack.items.iter().rev().take(depth).rev() {
            write!(&mut *debug, " {}", value.display_list()).unwrap();
        }

        writeln!(&mut *debug).unwrap();
        Ok(0)
    }

    #[op(code = "fexx @ fe01..fe14", fmt = "DEBUG {x}", args(x = args & 0xff))]
    #[op(code = "fexx @ fe15..fe20", fmt = "DEBUG {x}", args(x = args & 0xff))]
    #[op(code = "fexx @ fe30..fef0", fmt = "DEBUG {x}", args(x = args & 0xff))]
    fn exec_dummy_debug(_: &mut VmState, x: u32) -> VmResult<i32> {
        _ = x;
        Ok(0)
    }

    #[op(code = "fe14", fmt = "STRDUMP")]
    fn exec_dump_string(st: &mut VmState) -> VmResult<i32> {
        let Some(debug) = &mut st.debug else {
            return Ok(0);
        };

        if let Some(value) = st.stack.items.last() {
            if let Some(slice) = value.as_cell_slice() {
                // TODO: print as string, but why is it needed?
                writeln!(&mut *debug, "#DEBUG#: {}", slice.apply().display_data()).unwrap();
            } else {
                writeln!(&mut *debug, "#DEBUG#: is not a slice").unwrap();
            }
        } else {
            writeln!(&mut *debug, "#DEBUG#: s0 is absent").unwrap();
        }
        Ok(0)
    }

    #[op(code = "fe2x", fmt = "DUMP s{x}")]
    fn exec_dump_value(st: &mut VmState, x: u32) -> VmResult<i32> {
        let Some(debug) = &mut st.debug else {
            return Ok(0);
        };

        let x = x as usize;
        let depth = st.stack.depth();
        if x < depth {
            writeln!(
                &mut *debug,
                "#DEBUG#: s{x} = {}",
                st.stack.items[depth - x - 1].display_list()
            )
            .unwrap();
        } else {
            writeln!(&mut *debug, "#DEBUG#: s{x} is absent").unwrap();
        }

        Ok(0)
    }

    #[op_ext(code = 0xfef, code_bits = 12, arg_bits = 4, dump_with = dump_dummy_debug_str)]
    fn exec_dummy_debug_str(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let data_bits = ((args & 0xf) + 1) as u16 * 8;
        vm_ensure!(
            st.code.range().has_remaining(bits + data_bits, 0),
            InvalidOpcode
        );
        let ok = st.code.range_mut().skip_first(bits + data_bits, 0).is_ok();
        debug_assert!(ok);

        Ok(0)
    }

    #[cfg(feature = "dump")]
    fn dump_dummy_debug_str(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let data_bits = ((args & 0xf) + 1) as u16 * 8;
        if !code.has_remaining(bits + data_bits, 0) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits + data_bits, 0)?;
        f.record_opcode(&"DEBUGSTR")
    }
}
