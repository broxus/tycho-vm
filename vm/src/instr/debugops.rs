use tycho_types::prelude::*;
use tycho_vm_proc::vm_module;

#[cfg(feature = "dump")]
use crate::dispatch::DumpOutput;
use crate::error::VmResult;
#[cfg(feature = "dump")]
use crate::error::{DumpError, DumpResult};
use crate::state::VmState;
#[cfg(any(feature = "dump", feature = "tracing"))]
use crate::util::CellSliceExt;

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
                writeln!(
                    &mut *debug,
                    "#DEBUG#: {}",
                    DisplaySliceString(slice.apply())
                )
                .unwrap();
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

        if let Some(debug) = &mut st.debug {
            let mut slice = st.code.apply();
            slice.skip_first(bits, 0)?;
            slice.only_first(data_bits, 0)?;
            vm_log_op!("DEBUGSTR {}", slice.display_as_stack_value());
            writeln!(&mut *debug, "#DEBUG#: {}", DisplaySliceString(slice)).unwrap();
        } else {
            vm_log_op!("DEBUGSTR");
        }

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
        code.skip_first(bits, 0)?;

        let mut slice = *code;
        slice.only_first(data_bits, 0)?;
        code.skip_first(data_bits, 0)?;

        f.record_slice(slice)?;
        f.record_opcode(&format_args!("DEBUGSTR {}", slice.display_as_stack_value()))
    }
}

struct DisplaySliceString<'a>(CellSlice<'a>);

impl std::fmt::Display for DisplaySliceString<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const MAX_BIT_LEN: u16 = 127 * 8;

        match (|bytes| {
            let bit_len = self.0.size_bits();
            if bit_len > MAX_BIT_LEN || bit_len % 8 != 0 {
                return None;
            }

            let mut slice = self.0;
            let mut bytes = &*slice.load_raw(bytes, bit_len).ok()?;
            while let [rest @ .., last] = bytes {
                if *last == 0 || last.is_ascii_whitespace() {
                    bytes = rest;
                } else {
                    break;
                }
            }

            std::str::from_utf8(bytes).ok()
        })(&mut [0; 128])
        {
            Some(bytes) => f.write_str(bytes),
            None => write!(f, "x{:X}", self.0.display_data()),
        }
    }
}

#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    use super::*;

    #[test]
    #[traced_test]
    fn strdump_works() {
        let output = run_get_dump(tvmasm!(
            r#"
            SLICE x{48656C6C6F2C20776F726C6421}
            STRDUMP
            "#,
        ));
        assert_eq!(output, "#DEBUG#: Hello, world!\n");

        let output = run_get_dump(tvmasm!(
            r#"
            SLICE x{5370616365732020202020202020202020202020}
            STRDUMP
            "#,
        ));
        assert_eq!(output, "#DEBUG#: Spaces\n");

        let output = run_get_dump(tvmasm!(
            r#"
            SLICE x{0000}
            STRDUMP
            "#,
        ));
        assert_eq!(output, "#DEBUG#: \n");

        let output = run_get_dump(tvmasm!(
            r#"
            SLICE x{0000abab}
            STRDUMP
            "#,
        ));
        assert_eq!(output, "#DEBUG#: x0000ABAB\n");

        let output = run_get_dump(tvmasm!(
            r#"
            SLICE x{00c_}
            STRDUMP
            "#,
        ));
        assert_eq!(output, "#DEBUG#: x00C_\n");
    }

    #[test]
    #[traced_test]
    fn debugstr_works() {
        let output = run_get_dump(tvmasm!("@inline x{fefc48656C6C6F2C20776F726C6421}"));
        assert_eq!(output, "#DEBUG#: Hello, world!\n");

        let output = run_get_dump(tvmasm!("@inline x{feff53706163657320202020202020202020}"));
        assert_eq!(output, "#DEBUG#: Spaces\n");

        let output = run_get_dump(tvmasm!("@inline x{fef10000}"));
        assert_eq!(output, "#DEBUG#: \n");

        let output = run_get_dump(tvmasm!("@inline x{fef30000abab}"));
        assert_eq!(output, "#DEBUG#: x0000ABAB\n");
    }

    fn run_get_dump(code: &[u8]) -> String {
        let code = Boc::decode(code).unwrap();

        let mut debug_output = String::new();
        let mut vm = VmState::builder()
            .with_code(code)
            .with_debug(&mut debug_output)
            .build();
        assert_eq!(!vm.run(), 0);
        debug_output
    }
}
