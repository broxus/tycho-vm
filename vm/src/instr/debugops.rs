use anyhow::Result;
use tycho_vm_proc::vm_module;

use crate::dispatch::Opcodes;
use crate::error::VmResult;
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

    #[init]
    fn init_dummy_debug_str_ext(&self, t: &mut Opcodes) -> Result<()> {
        t.add_ext(0xfef, 12, 4, exec_dummy_debug_str)
    }

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
}
