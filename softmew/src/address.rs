use std::cmp::Ordering;
use std::ops::Range;

#[cfg(feature = "serde")]
use serde::{Serialize, Deserialize};

/// Range of virtual addresses
///
/// These are fully ordered by their beginning address so that it is easy to keep them sorted in
/// the MMU struct.
///
/// The start address is inclusive and the end address is exclusive.
#[derive(Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AddrRange {
    /// Address of the first byte in the range
    pub start: usize,
    /// Last address of the range exclusive
    pub end: usize,
}

impl AddrRange {
    /// Create a new address range
    ///
    /// # Arguments
    /// - `addr`: First address in the range
    /// - `len`: Number of bytes in the address range
    #[inline]
    #[must_use]
    pub const fn new(addr: usize, len: usize) -> Self {
        Self {
            start: addr,
            end: addr + len,
        }
    }

    /// Checks for containment of the address
    #[inline]
    #[must_use]
    pub const fn contains(&self, addr: usize) -> bool {
        self.start <= addr && addr < self.end
    }

    /// Compares this address range to a specific address.
    ///
    /// This is used to determine in which address range an address lies. If the address is in this
    /// range, then equal is returned. Otherwise, the comparison of the address to the beginning of
    /// this range is returned.
    #[inline]
    #[must_use]
    pub const fn compare_to_addr(&self, addr: usize) -> Ordering {
        if self.contains(addr) {
            Ordering::Equal
        } else if self.start >= addr {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }

    /// Test for full equality between two address ranges.
    ///
    /// This is mainly just used for testing.
    #[inline]
    #[must_use]
    pub const fn full_eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end
    }

    /// Compare this address range to another by starting addresses.
    #[inline]
    #[must_use]
    pub fn ord_by_start(&self, other: &Self) -> Ordering {
        self.start.cmp(&other.start)
    }

    /// Size of the address range in bytes.
    #[inline]
    #[must_use]
    pub const fn size(&self) -> usize {
        self.end - self.start
    }
}

impl std::fmt::Debug for AddrRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[0x{:016X} - 0x{:016X}]", self.start, self.end)
    }
}

impl From<Range<usize>> for AddrRange {
    fn from(value: Range<usize>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

impl IntoIterator for AddrRange {
    type Item = usize;
    type IntoIter = Range<usize>;

    /// Iterator over every address in the range.
    fn into_iter(self) -> Self::IntoIter {
        self.start..self.end
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordering() {
        let a = AddrRange::new(0, 10);
        let b = AddrRange::new(1, 9);
        let c = AddrRange::new(0, 1);
        assert_eq!(a.ord_by_start(&b), Ordering::Less);
        assert_eq!(b.ord_by_start(&c), Ordering::Greater);
        assert_eq!(a.ord_by_start(&c), Ordering::Equal);
    }

    #[test]
    fn from_range() {
        let a: AddrRange = (10..20).into();
        assert_eq!(a.start, 10);
        assert_eq!(a.end, 20);
    }

    #[test]
    fn full_eq() {
        let a = AddrRange::new(0, 10);
        let b = AddrRange::new(0, 9);
        let c = AddrRange::new(1, 10);
        let d = AddrRange::new(0, 10);
        assert!(a.full_eq(&a));
        assert!(!a.full_eq(&b));
        assert!(!a.full_eq(&c));
        assert!(a.full_eq(&d));
    }
}
