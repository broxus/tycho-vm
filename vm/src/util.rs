use tycho_types::dict::DictKey;
use tycho_types::error::Error;
use tycho_types::prelude::*;

/// A wrapper around [`CellSliceParts`] extending its lifetime.
#[derive(Default, Debug, Clone)]
#[repr(transparent)]
pub struct OwnedCellSlice(CellSliceParts);

impl OwnedCellSlice {
    #[inline]
    pub fn new_allow_exotic(cell: Cell) -> Self {
        Self(CellSliceParts::from(cell))
    }

    pub fn apply(&self) -> CellSlice<'_> {
        self.range().apply_allow_exotic(self.cell())
    }

    #[inline]
    pub fn range(&self) -> CellSliceRange {
        self.0.0
    }

    #[inline]
    pub fn range_mut(&mut self) -> &mut CellSliceRange {
        &mut self.0.0
    }

    #[inline]
    pub fn cell(&self) -> &Cell {
        &self.0.1
    }

    #[inline]
    pub fn set_range(&mut self, range: CellSliceRange) {
        self.0.0 = range
    }

    pub fn fits_into(&self, builder: &CellBuilder) -> bool {
        let range = self.range();
        let bits = range.size_bits();
        let refs = range.size_refs();
        builder.has_capacity(bits, refs)
    }
}

impl std::fmt::Display for OwnedCellSlice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cs = CellSlice::apply_allow_exotic(&self.0);
        let cs = cs.display_as_stack_value();
        std::fmt::Display::fmt(&cs, f)
    }
}

pub(crate) trait CellSliceExt<'a> {
    fn display_as_stack_value(&self) -> impl std::fmt::Display + 'a;
}

impl<'a> CellSliceExt<'a> for CellSlice<'a> {
    fn display_as_stack_value(&self) -> impl std::fmt::Display + 'a {
        #[repr(transparent)]
        struct Display<'a>(CellSlice<'a>);

        impl std::fmt::Display for Display<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let cs = &self.0;
                let refs = cs.size_refs();
                if refs != 0 {
                    ok!(write!(f, "("));
                }
                ok!(write!(f, "x{:X}", cs.display_data()));
                if refs != 0 {
                    write!(f, ",{refs})")
                } else {
                    Ok(())
                }
            }
        }

        Display(*self)
    }
}

impl From<CellSliceParts> for OwnedCellSlice {
    #[inline]
    fn from(parts: CellSliceParts) -> Self {
        Self(parts)
    }
}

impl From<OwnedCellSlice> for CellSliceParts {
    #[inline]
    fn from(value: OwnedCellSlice) -> Self {
        value.0
    }
}

impl PartialEq<CellSlice<'_>> for OwnedCellSlice {
    fn eq(&self, right: &CellSlice<'_>) -> bool {
        let left = self.apply();
        matches!(left.contents_eq(right), Ok(true))
    }
}

#[repr(transparent)]
pub struct Uint4(pub usize);

impl DictKey for Uint4 {
    const BITS: u16 = 4;
}

impl LoadDictKey for Uint4 {
    #[inline]
    fn load_from_data(data: &CellDataBuilder) -> Option<Self> {
        let raw_data = data.raw_data();
        Some(Self((raw_data[0] & 0xf) as usize))
    }
}

impl StoreDictKey for Uint4 {
    #[inline]
    fn store_into_data(&self, data: &mut CellDataBuilder) -> Result<(), Error> {
        if self.0 > 0xf {
            return Err(Error::IntOverflow);
        }
        data.store_small_uint(self.0 as _, 4)
    }
}

impl Store for Uint4 {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder, _: &dyn CellContext) -> Result<(), Error> {
        self.store_into_data(builder.as_mut())
    }
}

impl Load<'_> for Uint4 {
    #[inline]
    fn load_from(slice: &mut CellSlice<'_>) -> Result<Self, Error> {
        Ok(Self(ok!(slice.load_small_uint(4)) as usize))
    }
}

pub const fn shift_ceil_price(value: u128) -> u128 {
    let r = value & 0xffff != 0;
    (value >> 16) + r as u128
}

pub fn ensure_empty_slice(slice: &CellSlice) -> Result<(), Error> {
    if slice.is_data_empty() && slice.is_refs_empty() {
        Ok(())
    } else {
        Err(Error::InvalidData)
    }
}

pub fn load_uint_leq(cs: &mut CellSlice, upper_bound: u32) -> Result<u64, Error> {
    let bits = 32 - upper_bound.leading_zeros();
    let result = cs.load_uint(bits as u16)?;
    if result > upper_bound as u64 {
        return Err(Error::IntOverflow);
    };
    Ok(result)
}

pub fn remove_trailing(slice: &mut CellSlice<'_>) -> Result<(), tycho_types::error::Error> {
    let bits = slice.size_bits();
    if bits == 0 {
        return Ok(());
    }

    let n = ok!(slice.count_trailing(false));
    // NOTE: Skip one additional bit for non-empty slice
    slice.skip_last(n + (n != bits) as u16, 0)
}
