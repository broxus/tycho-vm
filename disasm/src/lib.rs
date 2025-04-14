use std::collections::hash_map;
use std::fmt::Write;

use ahash::HashMap;
use anyhow::Result;
use everscale_types::prelude::*;
use num_bigint::BigInt;
use smol_str::SmolStr;
use tycho_vm::{load_int_from_slice, DumpError, DumpOutput, DumpResult};

pub use self::models::{
    Code, CodeBlock, CodeBlockTail, Data, DataBlock, Item, ItemId, JumpTable, Library, Link,
    LinkType, Opcode,
};

mod models;

pub fn disasm_structured(code: Cell) -> Result<Code> {
    let mut stack = Vec::new();
    let mut res = Resources::default();

    // Add root continuation.
    let root = match res.add_cont(code) {
        // Root continuation is a code so add it to the stack to process.
        Ok(item) => {
            let id = item.id;
            stack.push(item);
            id
        }
        // Root continuation is a library so just use its id.
        Err(id) => id,
    };

    // Disasm works only with CP0 for now.
    let cp = tycho_vm::codepage0();

    // Prepare dump state which will be filled by `dispatch_dump`.
    let mut state = DumpState {
        opcode: String::with_capacity(128),
        ..Default::default()
    };

    // New continuations are collected during the instruction dump
    // and added to the stack afterwards.
    let mut new_conts = Vec::new();

    'outer: while let Some(item) = stack.last_mut() {
        // Process the topmost continuation.

        // Apply cell slice parts to get a `CellSlice` with code.
        let mut cs = item.slice.0.apply(&item.slice.1)?;

        // Use the current code root in a DumpState so it can transform
        // `CellSlice<'_>` into `CellSliceParts`.
        state.root = item.slice.1.clone();

        let mut incomplete = false;
        'inner: while !cs.is_data_empty() {
            // Remember the current position relative to the code cell.
            let offset_bits = cs.offset_bits();
            let offset_refs = cs.offset_refs();

            // Dispatch one instruction and dump its info into the `DumpState`.
            let dump = cp.dispatch_dump(&mut cs, &mut state);
            // NOTE: Code root cell must not change.
            debug_assert_eq!(cs.cell(), item.slice.1.as_ref());

            match dump {
                // Apply the new slice range to the stack item.
                Ok(()) => item.slice.0 = cs.range(),
                // In case of an explicitly invalid opcode treat the remainder as some unparsed tail.
                Err(DumpError::InvalidOpcode) => {
                    state.clear();
                    incomplete = true;
                    break 'inner;
                }
                // All other errors are fatal.
                Err(e) => return Err(e.into()),
            }

            // Start describing the new opcode.
            let mut opcode = Opcode {
                bits: cs.offset_bits() - offset_bits,
                refs: cs.offset_refs() - offset_refs,
                // TODO: Tokenize opcode text into name and args.
                text: SmolStr::from(&state.opcode),
                gas: state.gas,
                links: Vec::new(),
            };

            // Fill opcode links to cells (as data).
            for cell in state.cells.drain(..) {
                let id = res.add_cell(cell);
                opcode.links.push(Link {
                    to: Some(id),
                    ty: LinkType::Data,
                });
            }

            // Fill opcode links to slices (as data).
            for slice in state.slices.drain(..) {
                let id = res.add_slice(slice);
                opcode.links.push(Link {
                    to: Some(id),
                    ty: LinkType::Data,
                });
            }

            // Fill opcode links to continuation references.
            for cont in state.conts.drain(..) {
                let id = match res.add_cont(cont) {
                    // New continuation found, remember to push it to the stack
                    // right after this opcode is processed.
                    Ok(item) => {
                        let id = item.id;
                        new_conts.push(item);
                        id
                    }
                    // An existing continuation found, just add it as link.
                    Err(id) => id,
                };

                opcode.links.push(Link {
                    to: Some(id),
                    ty: LinkType::Body,
                });
            }

            // Fill opcode links to inline continuations.
            for cont in state.cont_slices.drain(..) {
                let id = match res.add_cont_slice(cont) {
                    // New continuation found, remember to push it to the stack
                    // right after this opcode is processed.
                    Ok(item) => {
                        let id = item.id;
                        new_conts.push(item);
                        id
                    }
                    // An existing continuation found, just add it as link.
                    Err(id) => id,
                };

                opcode.links.push(Link {
                    to: Some(id),
                    ty: LinkType::Body,
                });
            }

            // Fill opcode links to jump tables.
            for (n, root) in state.dicts.drain(..) {
                let id = match res.add_jump_table(n, root) {
                    // New jump table found, remember to push its items to the stack
                    // right after this opcode is processed.
                    Ok(item) => {
                        let id = item.id;
                        new_conts.extend(item.to_parse);
                        id
                    }
                    // An existing jump table found, just add it as link.
                    Err(id) => id,
                };

                opcode.links.push(Link {
                    to: Some(id),
                    ty: LinkType::Body,
                });
            }

            // Add opcode to the code block.
            item.block.opcodes.push(opcode);

            // Reset `DumpState`.
            state.clear();

            // Refill the stack with new continuations.
            // NOTE: Reverse order is used here to preserve the resulting total ordering.
            if !new_conts.is_empty() {
                stack.extend(new_conts.drain(..).rev());
                continue 'outer;
            }
        }

        // Try to get the next cell if the code was fully processed.
        let next = (!incomplete && !cs.is_refs_empty())
            .then(|| cs.load_reference_cloned())
            .transpose()?;

        // This stack item is not needed on stack anymore.
        let mut item = stack.pop().unwrap();

        if let Some(next) = next {
            // Try to add the next cell as a continuation.
            match res.add_cont(next) {
                // New continuation found, link it to the previous and push it to the stack.
                Ok(next_item) => {
                    item.block.tail = Some(CodeBlockTail::Child { id: next_item.id });
                    stack.push(next_item);
                }
                // An existing continuation found, just link it to the previous.
                Err(next_id) => {
                    item.block.tail = Some(CodeBlockTail::Child { id: next_id });
                }
            }
        } else if incomplete {
            // If code was not fully processed mark the block tail as incomplete.
            item.block.tail = Some(CodeBlockTail::Incomplete);
        } else {
            // No more code left in this continuation.
            item.block.tail = None;
        }

        // Replace the stub with the code block.
        res.items[item.id as usize] = Item::Code(item.block);

        // Save this code block to the jump table if needed.
        if let Some(save_to) = item.save_to {
            let Item::JumpTable(table) = &mut res.items[save_to.jump_table_id as usize] else {
                unreachable!("save_to index mismatch");
            };
            table.items.push((save_to.key, item.id));
        }
    }

    // Done.
    Ok(Code {
        root,
        items: res.items,
    })
}

#[derive(Default)]
struct Resources {
    cont_to_id: HashMap<HashBytes, ItemId>,
    cont_slice_to_id: HashMap<SliceKey, ItemId>,
    cell_to_id: HashMap<HashBytes, ItemId>,
    slice_to_id: HashMap<SliceKey, ItemId>,
    lib_to_id: HashMap<HashBytes, ItemId>,
    dict_to_id: HashMap<(u16, HashBytes), ItemId>,
    items: Vec<Item>,
}

impl Resources {
    fn add_cont(&mut self, cont: Cell) -> Result<DumpStackItem, ItemId> {
        if cont.descriptor().is_library() {
            return Err(self.add_library(cont));
        }

        match self.cont_to_id.entry(*cont.repr_hash()) {
            // First time we see this continuation.
            hash_map::Entry::Vacant(entry) => {
                // Insert a stub item to get the new id.
                let id = add_item(&mut self.items, DataBlock {
                    data: Cell::default().into(),
                });
                entry.insert(id);
                // Create a stack item.
                Ok(DumpStackItem::new(id, cont.into(), false, None))
            }
            // Continuation is already known.
            hash_map::Entry::Occupied(entry) => Err(*entry.get()),
        }
    }

    fn add_cont_slice(&mut self, cont: CellSliceParts) -> Result<DumpStackItem, ItemId> {
        // First time we see this continuation.
        match self.cont_slice_to_id.entry((*cont.1.repr_hash(), cont.0)) {
            hash_map::Entry::Vacant(entry) => {
                // Insert a stub item to get the new id.
                let id = add_item(&mut self.items, DataBlock {
                    data: Cell::default().into(),
                });
                entry.insert(id);
                // Create a stack item.
                Ok(DumpStackItem::new(id, cont, true, None))
            }
            // Continuation is already known.
            hash_map::Entry::Occupied(entry) => Err(*entry.get()),
        }
    }

    fn add_jump_table(&mut self, n: u16, root: Cell) -> Result<NewJumpTable, ItemId> {
        match self.dict_to_id.entry((n, *root.repr_hash())) {
            // First time we see this jump table.
            hash_map::Entry::Vacant(entry) => {
                // Insert a new empty jump table.
                let id = add_item(&mut self.items, JumpTable {
                    cell_hash: *root.repr_hash(),
                    key_bits: n,
                    items: Vec::new(),
                    is_full_code: true,
                });
                entry.insert(id);

                // Parse jump table items into inline continuations.
                let mut to_parse = Vec::new();
                if (|| {
                    for item in everscale_types::dict::RawOwnedIter::new(&Some(root), n) {
                        let (key, value) = item?;
                        let key = load_int_from_slice(&mut key.as_data_slice(), n, true)?;

                        let save_to = SaveTo {
                            jump_table_id: id,
                            key,
                        };

                        let id = add_item(&mut self.items, DataBlock {
                            data: Cell::default().into(),
                        });
                        to_parse.push(DumpStackItem::new(id, value, true, Some(save_to)));
                    }
                    Ok::<_, everscale_types::error::Error>(())
                })()
                .is_ok()
                {
                    // Mark jump table as fully parsed if there were no errors.
                    let Item::JumpTable(table) = &mut self.items[id as usize] else {
                        unreachable!("table index mismatch");
                    };
                    table.is_full_code = true;
                }

                Ok(NewJumpTable { id, to_parse })
            }
            // Jump table is already known.
            hash_map::Entry::Occupied(entry) => Err(*entry.get()),
        }
    }

    fn add_cell(&mut self, cell: Cell) -> ItemId {
        *self
            .cell_to_id
            .entry(*cell.repr_hash())
            .or_insert_with(|| add_item(&mut self.items, DataBlock { data: cell.into() }))
    }

    fn add_slice(&mut self, slice: CellSliceParts) -> ItemId {
        *self
            .slice_to_id
            .entry((*slice.1.repr_hash(), slice.0))
            .or_insert_with(|| add_item(&mut self.items, DataBlock { data: slice.into() }))
    }

    fn add_library(&mut self, cell: Cell) -> ItemId {
        debug_assert!(cell.descriptor().is_library());

        let hash = *cell.repr_hash();
        *self
            .lib_to_id
            .entry(hash)
            .or_insert_with(|| add_item(&mut self.items, Library { hash }))
    }
}

fn add_item<T: Into<Item>>(items: &mut Vec<Item>, item: T) -> ItemId {
    let id = items.len() as ItemId;
    items.push(item.into());
    id
}

struct DumpStackItem {
    id: ItemId,
    block: CodeBlock,
    slice: CellSliceParts,
    save_to: Option<SaveTo>,
}

impl DumpStackItem {
    fn new(id: ItemId, slice: CellSliceParts, is_inline: bool, save_to: Option<SaveTo>) -> Self {
        Self {
            id,
            block: CodeBlock {
                cell_hash: *slice.1.repr_hash(),
                is_inline,
                offset_bits: slice.0.offset_bits(),
                offset_refs: slice.0.offset_refs(),
                bits: slice.0.size_bits(),
                refs: slice.0.size_refs(),
                opcodes: Vec::new(),
                tail: Some(CodeBlockTail::Incomplete),
            },
            slice,
            save_to,
        }
    }
}

struct SaveTo {
    jump_table_id: ItemId,
    key: BigInt,
}

struct NewJumpTable {
    id: ItemId,
    to_parse: Vec<DumpStackItem>,
}

type SliceKey = (HashBytes, CellSliceRange);

#[derive(Default)]
struct DumpState {
    root: Cell,
    cells: Vec<Cell>,
    slices: Vec<CellSliceParts>,
    conts: Vec<Cell>,
    cont_slices: Vec<CellSliceParts>,
    dicts: Vec<(u16, Cell)>,
    gas: u64,
    opcode: String,
}

impl DumpState {
    fn clear(&mut self) {
        self.cells.clear();
        self.slices.clear();
        self.conts.clear();
        self.cont_slices.clear();
        self.dicts.clear();
        self.gas = 0;
        self.opcode.clear();
    }
}

impl DumpOutput for DumpState {
    fn record_gas(&mut self, gas: u64) -> DumpResult {
        self.gas = gas;
        Ok(())
    }

    fn record_opcode(&mut self, value: &dyn std::fmt::Display) -> DumpResult {
        write!(&mut self.opcode, "{}", value)?;
        Ok(())
    }

    fn record_cell(&mut self, value: Cell) -> DumpResult {
        self.cells.push(value);
        Ok(())
    }

    fn record_slice(&mut self, value: CellSlice<'_>) -> DumpResult {
        if value.cell() != self.root.as_ref() {
            return Err(DumpError::CellMismatch);
        }
        self.slices.push((value.range(), self.root.clone()));
        Ok(())
    }

    fn record_cont(&mut self, cont: Cell) -> DumpResult {
        self.conts.push(cont);
        Ok(())
    }

    fn record_cont_slice(&mut self, cont: CellSlice<'_>) -> DumpResult {
        if cont.cell() != self.root.as_ref() {
            return Err(DumpError::CellMismatch);
        }
        self.cont_slices.push((cont.range(), self.root.clone()));
        Ok(())
    }

    fn record_dict(&mut self, n: u16, mut slice: CellSlice<'_>) -> DumpResult {
        self.dicts.push((n, slice.load_reference_cloned()?));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use everscale_asm_macros::tvmasm;

    use super::*;

    #[test]
    fn disasm_ever_wallet() -> Result<()> {
        let code = Boc::decode_base64("te6ccgEBBgEA/AABFP8A9KQT9LzyyAsBAgEgBQIC5vJx1wEBwADyeoMI1xjtRNCDB9cB1ws/yPgozxYjzxbJ+QADcdcBAcMAmoMH1wFRE7ry4GTegEDXAYAg1wGAINcBVBZ1+RDyqPgju/J5Zr74I4EHCKCBA+ioUiC8sfJ0AiCCEEzuZGy64w8ByMv/yz/J7VQEAwA+ghAWnj4Ruo4R+AACkyDXSpd41wHUAvsA6NGTMvI84gCYMALXTND6QIMG1wFx1wF41wHXTPgAcIAQBKoCFLHIywVQBc8WUAP6AstpItAhzzEh10mghAm5mDNwAcsAWM8WlzBxAcsAEsziyQH7AAAE0jA=")?;
        let code = disasm_structured(code)?;
        println!("{}", serde_json::to_string_pretty(&code).unwrap());

        // std::fs::write(
        //     "ever_wallet.json",
        //     serde_json::to_string_pretty(&code).unwrap(),
        // )
        // .unwrap();

        Ok(())
    }

    #[test]
    fn disasm_wallet_v3() -> Result<()> {
        let code = Boc::decode_base64("te6ccgEBAQEAcQAA3v8AIN0gggFMl7ohggEznLqxn3Gw7UTQ0x/THzHXC//jBOCk8mCDCNcYINMf0x/TH/gjE7vyY+1E0NMf0x/T/9FRMrryoVFEuvKiBPkBVBBV+RDyo/gAkyDXSpbTB9QC+wDo0QGkyMsfyx/L/8ntVA==")?;
        let code = disasm_structured(code)?;
        println!("{}", serde_json::to_string_pretty(&code).unwrap());

        // std::fs::write(
        //     "wallet_v3.json",
        //     serde_json::to_string_pretty(&code).unwrap(),
        // )
        // .unwrap();

        Ok(())
    }

    #[test]
    fn disasm_slice_data() -> Result<()> {
        let code = Boc::decode(tvmasm!("PUSHSLICE x{6_}"))?;
        let code = disasm_structured(code)?;
        println!("{}", serde_json::to_string_pretty(&code).unwrap());

        Ok(())
    }

    #[test]
    fn disasm_cell_data() -> Result<()> {
        let code = Boc::decode(tvmasm!("PUSHREF x{6_}"))?;
        let code = disasm_structured(code)?;
        println!("{}", serde_json::to_string_pretty(&code).unwrap());

        Ok(())
    }
}
