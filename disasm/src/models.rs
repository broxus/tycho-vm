use std::cell::RefCell;

use base64::prelude::{Engine as _, BASE64_STANDARD};
use everscale_types::prelude::*;
use num_bigint::BigInt;
use serde::ser::SerializeStruct;
use serde::Serialize;
use smol_str::SmolStr;

pub type ItemId = u32;

#[derive(Debug, Clone, Serialize)]
pub struct Code {
    pub root: ItemId,
    #[serde(serialize_with = "Code::serialize_items")]
    pub items: Vec<Item>,
}

impl Code {
    fn serialize_items<S>(items: &[Item], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeSeq;

        #[derive(Serialize)]
        struct ItemWithId<'a> {
            id: ItemId,
            #[serde(flatten)]
            item: &'a Item,
        }

        let mut s = serializer.serialize_seq(Some(items.len()))?;
        for (i, item) in items.iter().enumerate() {
            s.serialize_element(&ItemWithId {
                id: i as ItemId,
                item,
            })?;
        }
        s.end()
    }
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum Item {
    JumpTable(JumpTable),
    Code(CodeBlock),
    Data(DataBlock),
    Library(Library),
}

#[derive(Debug, Clone, Serialize)]
pub struct JumpTable {
    pub cell_hash: HashBytes,
    pub key_bits: u16,
    #[serde(serialize_with = "JumpTable::serialize_items")]
    pub items: Vec<(BigInt, ItemId)>,
    pub is_full_code: bool,
}

impl From<JumpTable> for Item {
    #[inline]
    fn from(value: JumpTable) -> Self {
        Self::JumpTable(value)
    }
}

impl JumpTable {
    fn serialize_items<T, S>(value: &[(BigInt, T)], serializer: S) -> Result<S::Ok, S::Error>
    where
        T: Serialize,
        S: serde::Serializer,
    {
        use serde::ser::SerializeMap;

        let mut s = serializer.serialize_map(Some(value.len()))?;
        for (key, value) in value {
            s.serialize_entry(&DisplayBigInt(key), value)?;
        }
        s.end()
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct CodeBlock {
    pub cell_hash: HashBytes,
    pub is_inline: bool,
    pub offset_bits: u16,
    pub offset_refs: u8,
    pub bits: u16,
    pub refs: u8,
    pub opcodes: Vec<Opcode>,
    pub tail: Option<CodeBlockTail>,
}

impl From<CodeBlock> for Item {
    #[inline]
    fn from(value: CodeBlock) -> Self {
        Self::Code(value)
    }
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum CodeBlockTail {
    Incomplete,
    Child { id: ItemId },
}

#[derive(Debug, Clone, Serialize)]
pub struct DataBlock {
    pub data: Data,
}

impl From<DataBlock> for Item {
    #[inline]
    fn from(value: DataBlock) -> Self {
        Self::Data(value)
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct Library {
    pub hash: HashBytes,
}

impl From<Library> for Item {
    #[inline]
    fn from(value: Library) -> Self {
        Self::Library(value)
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct Opcode {
    pub bits: u16,
    #[serde(skip_serializing_if = "is_zero_refs")]
    pub refs: u8,
    pub name: SmolStr,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub args: Vec<OpcodeArg>,
    pub gas: u64,
}

const fn is_zero_refs(refs: &u8) -> bool {
    *refs == 0
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum OpcodeArg {
    Int(#[serde(serialize_with = "OpcodeArg::serialize_int")] BigInt),
    Stack { idx: i32 },
    Reg { idx: u8 },
    Cell { id: ItemId },
    Slice { id: ItemId },
}

impl OpcodeArg {
    fn serialize_int<S>(value: &BigInt, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut s = serializer.serialize_struct("Int", 1)?;
        s.serialize_field("value", &DisplayBigInt(value))?;
        s.end()
    }
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum Data {
    Slice(#[serde(serialize_with = "Data::serialize_slice")] CellSliceParts),
    Cell(#[serde(serialize_with = "Data::serialize_cell")] Cell),
}

impl From<CellSliceParts> for Data {
    #[inline]
    fn from(value: CellSliceParts) -> Self {
        Self::Slice(value)
    }
}

impl From<Cell> for Data {
    #[inline]
    fn from(value: Cell) -> Self {
        Self::Cell(value)
    }
}

impl Data {
    fn serialize_slice<S>(value: &CellSliceParts, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let range = value.0;
        let cs = CellSlice::apply_allow_exotic(value);
        let cell = CellBuilder::build_from(cs).unwrap();

        let mut s = serializer.serialize_struct("CellSlice", 5)?;
        s.serialize_field("offset_bits", &range.offset_bits())?;
        s.serialize_field("offset_refs", &range.offset_refs())?;
        s.serialize_field("bits", &range.size_bits())?;
        s.serialize_field("refs", &range.size_refs())?;
        Self::serialize_with_buffer(&cell, |data| s.serialize_field("boc", data))?;
        s.end()
    }

    fn serialize_cell<S>(value: &Cell, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut s = serializer.serialize_struct("Cell", 1)?;
        Self::serialize_with_buffer(value, |data| s.serialize_field("boc", data))?;
        s.end()
    }

    fn serialize_with_buffer<F, R>(cell: &Cell, f: F) -> R
    where
        F: FnOnce(&str) -> R,
    {
        use everscale_types::boc::ser::BocHeader;

        struct Buffers {
            bytes: Vec<u8>,
            base64: String,
        }

        thread_local! {
            static BUFFERS: RefCell<Buffers> = const {
                RefCell::new(Buffers {
                    bytes: Vec::new(),
                    base64: String::new(),
                })
            };
        }

        const MAX_OK_SIZE: usize = 10 << 10; // 10 KB

        BUFFERS.with_borrow_mut(|buffers| {
            BocHeader::<ahash::RandomState>::with_root(cell.as_ref()).encode(&mut buffers.bytes);

            BASE64_STANDARD.encode_string(&buffers.bytes, &mut buffers.base64);
            let res = f(&buffers.base64);

            if buffers.bytes.len() <= MAX_OK_SIZE {
                buffers.bytes.clear();
            } else {
                std::mem::take(&mut buffers.bytes);
            }

            if buffers.base64.len() <= MAX_OK_SIZE {
                buffers.base64.clear();
            } else {
                std::mem::take(&mut buffers.base64);
            }

            res
        })
    }
}

#[repr(transparent)]
struct DisplayBigInt<'a>(&'a BigInt);

impl std::fmt::Display for DisplayBigInt<'_> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.0, f)
    }
}

impl serde::Serialize for DisplayBigInt<'_> {
    #[inline]
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}
