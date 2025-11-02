use crate::address::AddrRange;
use crate::fault::Fault;
use crate::fault::Reason;
use crate::page::{Page, SnapshotPage};
pub use crate::permission::Perm;
use std::cmp::Ordering;
use std::ops::Range;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub mod address;
pub mod fault;
pub mod page;
pub mod permission;

/// Software memory management unit
///
/// A full software implementation of a memory management unit with byte level permissions.
///
/// This MMU is meant to be as flexible as possible. It can map any amount of memory at any address
/// with no alignment requirements. The only limitation is that mapped address ranges may not
/// overlap each other.
///
/// The goal of this MMU is to be very performant for reads, writes, and resets. Memory can be
/// initialized up to some point and then snapshotted after initialization using clone. The copy
/// can then be used as the backing memory for something before using the snapshot to reset the
/// memory to the original state before starting a new run.
///
/// A snapshot of memory is literally just a full copy of memory at some point in time. This means
/// that memory usage will double if you take a snapshot of an MMU. This crate makes the choice of
/// sacrificing memory usage for runtime performance.
///
/// # Examples
/// ```
/// use softmew::MMU;
/// use softmew::permission::Perm;
/// use softmew::page::{Page, SnapshotPage};
///
/// # fn use_mmu<P: Page>(_mew: &mut MMU<P>) {}
///
/// let mut memory = MMU::<SnapshotPage>::new();
/// let data = memory.map_memory(0x1000, 0x1000, Perm::default()).expect("Failed to map data section");
/// data.as_mut()[..8].copy_from_slice(&[0, 1, 2, 3, 4, 5, 6, 7]);
/// let code = memory.map_memory(0x8000, 0x1000, Perm::READ).expect("Failed to map code section");
/// code.as_mut()[..8].copy_from_slice(&[8, 9, 0xa, 0xb, 0xc, 0xd, 0xe, 0xf]);
///
/// // Make a snapshot
/// let snapshot = memory.snapshot();
///
/// // Use memory somehow
/// use_mmu(&mut memory);
///
/// // Reset memory
/// // snapshot is a snapshot of memory so it is safe to use here
/// unsafe { memory.reset(&snapshot); }
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MMU<P> {
    /// List of `AddrRanges` sorted by the lowest address in the range
    ///
    /// Must always remain sorted or else everything will break. It is assumed that an element at
    /// index `i` in pages is the address range for the backing memory at index `i` in data.
    pages: Vec<AddrRange>,
    /// List of the allocated memory to back each memory mapping
    ///
    /// This must always be sorted by the address at which the memory is mapped at. This will
    /// ensure that it is always sorted in the same way as pages.
    data: Vec<P>,
}

impl<P> Default for MMU<P> {
    fn default() -> Self {
        Self {
            pages: Vec::new(),
            data: Vec::new(),
        }
    }
}

impl<P: Page> MMU<P> {
    /// Create a new memory management instance
    ///
    /// Will have no memory associated with it.
    #[must_use]
    pub fn new() -> Self {
        Self {
            pages: Vec::new(),
            data: Vec::new(),
        }
    }

    /// Get the mapping associated with an address
    ///
    /// Looks through all mapped memory to find any that contain `addr` and returns a
    /// reference to that mapping.
    ///
    /// If no mapping is found, None is returned.
    #[must_use]
    #[inline]
    pub fn get_mapping(&self, addr: usize) -> Option<&P> {
        let idx = self.get_mapping_idx(addr)?;
        // SAFETY: See safety comment in get_mapping_mut
        Some(unsafe { self.data.get_unchecked(idx) })
    }

    /// Get a mutable reference to the mapping associated with `addr`
    ///
    /// Same as [`MMU::get_mapping`] but will get a mutable reference.
    #[must_use]
    #[inline]
    pub fn get_mapping_mut(&mut self, addr: usize) -> Option<&mut P> {
        let idx = self.get_mapping_idx(addr)?;
        // SAFETY: idx is returned by get_mapping_idx which will return a valid index into the pages
        // vector. The pages and data vectors are always kept in sync so a valid page index is
        // valid data index. That makes this unchecked access safe.
        Some(unsafe { self.data.get_unchecked_mut(idx) })
    }

    #[must_use]
    #[inline]
    fn get_mapping_idx(&self, addr: usize) -> Option<usize> {
        // Why does `is_sorted_by` have a different interface to `sort_by`? I feel like those should
        // both take a function that returns `Ordering`.
        debug_assert!(
            self.pages
                .is_sorted_by(|a, b| AddrRange::ord_by_start(a, b) == Ordering::Less),
            "Pages list is not sorted"
        );
        debug_assert!(
            self.data.is_sorted_by(|d1, d2| d1.start() < d2.start()),
            "Memory mappings are not sorted"
        );
        debug_assert_eq!(
            self.pages.len(),
            self.data.len(),
            "Data and pages have differing sizes"
        );
        self.pages
            .binary_search_by(|map| map.compare_to_addr(addr))
            .ok()
    }

    /// Create a new memory mapping of the address range [start, size+1) with the given permission.
    ///
    /// Returns a mutable reference to the newly created mapping so that it can be initialized.
    ///
    /// # Errors
    /// Returns an error if any of the address ranges that are already mapped would overlap with
    /// the new mapping. Returns the address range of the first mapping found that would overlap
    /// with it.
    ///
    /// # Panics
    /// `size` must not be zero. This MMU does not support zero sized memory mappings.
    pub fn map_memory(
        &mut self,
        start: usize,
        size: usize,
        perm: Perm,
    ) -> Result<&mut P, AddrRange> {
        assert_ne!(size, 0, "Zero sized memory mappings are not supported");
        let end = start + size;
        // Loop through to make sure there isn't any overlap
        for map in &self.pages {
            // See
            // https://stackoverflow.com/a/12888920
            if start.max(map.start) < end.min(map.end) {
                return Err(*map);
            }
        }
        let new_mapping = P::new(start, size, perm);
        let new_range = AddrRange::new(start, size);
        self.pages.push(new_range);
        self.data.push(new_mapping);
        self.pages.sort_by(AddrRange::ord_by_start);
        self.data.sort_by_key(Page::start);
        // This cannot panic because we just inserted the mapping that we're requesting.
        Ok(self.get_mapping_mut(start).unwrap())
    }

    /// Reads some memory in this MMU's memory space
    ///
    /// This is a simple wrapper around finding the correct memory space using [`MMU::get_mapping`]
    /// and then calling [`Page::read`] on the returned mapping.
    ///
    /// # Errors
    /// Returns an error if `addr` is not mapped in this MMU. Will also propagate the fault
    /// returned by the underlying page implementation.
    pub fn read_perm(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        let map = self.get_mapping(addr).ok_or(Fault {
            address: AddrRange::new(addr, buf.len()),
            reason: Reason::NotMapped,
        })?;
        map.read(addr, buf)
    }

    /// Writes some memory in this MMU's memory space
    ///
    /// This is a simple wrapper around finding the correct memory space using
    /// [`MMU::get_mapping_mut`]
    /// and then calling [`Page::write`] on the returned mapping.
    ///
    /// # Errors
    /// Returns an error if `addr` is not mapped in this MMU. Will also propagate the fault
    /// returned by the underlying page implementation.
    pub fn write_perm(&mut self, addr: usize, buf: &[u8]) -> Result<(), Fault> {
        let map = self.get_mapping_mut(addr).ok_or(Fault {
            address: AddrRange::new(addr, buf.len()),
            reason: Reason::NotMapped,
        })?;
        map.write(addr, buf)
    }

    /// Iterate over all of the mapped memory ranges.
    pub fn mappings(&self) -> impl Iterator<Item = &P> {
        self.data.iter()
    }

    /// Get an iterator over all of the unmapped ranges.
    #[must_use]
    pub fn gaps(&self) -> Gaps<'_, P> {
        Gaps::new(self)
    }

    /// Get the bytes backing specific addresses.
    ///
    /// Uses the given permissions to check for faults on accessing the memory.
    ///
    /// # Errors
    /// Returns an error if any address is not mapped or missing the read permission.
    pub fn get_slice(&self, addrs: Range<usize>, perm: Perm) -> Result<&[u8], Fault> {
        let map = self.get_mapping(addrs.start).ok_or(Fault {
            address: AddrRange::new(addrs.start, addrs.end - addrs.start),
            reason: Reason::NotMapped,
        })?;
        map.get_slice(addrs, perm)
    }

    /// Get a mutable reference to the bytes backing specific addresses.
    ///
    /// Uses the given permissions to check for faults on accessing the memory.
    ///
    /// # Errors
    /// Returns an error if any address is not mapped or missing the write permission.
    pub fn get_slice_mut(&mut self, addrs: Range<usize>, perm: Perm) -> Result<&mut [u8], Fault> {
        let map = self.get_mapping_mut(addrs.start).ok_or(Fault {
            address: AddrRange::new(addrs.start, addrs.end - addrs.start),
            reason: Reason::NotMapped,
        })?;
        map.get_slice_mut(addrs, perm)
    }
}

impl MMU<SnapshotPage> {
    /// Reset all memory to some snapshotted state
    ///
    /// Resets all the memory in this MMU to the state that it was at when `original` was cloned
    /// from this MMU.
    ///
    /// # Safety
    /// Requires that original be a snapshot of this mapping.
    ///
    /// # Panics
    /// May panic if `original` was not cloned from this MMU or if more memory was mapped to
    /// `original` after it was cloned.
    pub unsafe fn reset(&mut self, original: &Self) {
        debug_assert_eq!(self.data.len(), original.data.len());
        for (dirty, orig) in self.data.iter_mut().zip(original.data.iter()) {
            if dirty.dirtied() {
                unsafe {
                    dirty.reset(orig);
                }
            }
        }
    }

    /// Check if any state in the MMU has been dirtied
    #[must_use]
    pub fn dirtied(&self) -> bool {
        self.data.iter().any(SnapshotPage::dirtied)
    }

    /// Snapshot the entire MMU state
    ///
    /// This is basically just a clone but will clear dirty state of all mappings without reverting
    /// the memory.
    #[must_use]
    pub fn snapshot(&mut self) -> Self {
        let pages = self.pages.clone();
        let mut data = Vec::with_capacity(self.data.len());
        for d in &mut self.data {
            data.push(d.snapshot());
        }
        Self { pages, data }
    }
}

/// Iterator over the contiguous unmapped ranges in an MMU.
///
/// This can make it easier to determine what unmapped ranges exist when you
/// need to map in a new range but have complete information about what might
/// already have been mapped.
pub struct Gaps<'m, P> {
    mmu: &'m MMU<P>,
    starting_addr: usize,
    page_idx: usize,
}

impl<'m, P> Gaps<'m, P> {
    fn new(mmu: &'m MMU<P>) -> Self {
        Self {
            mmu,
            starting_addr: 0,
            page_idx: 0,
        }
    }
}

impl<P> Iterator for Gaps<'_, P> {
    type Item = AddrRange;

    fn next(&mut self) -> Option<Self::Item> {
        if self.starting_addr == usize::MAX {
            return None;
        }

        if self.mmu.data.is_empty() {
            self.starting_addr = usize::MAX;
            return Some(AddrRange {
                start: 0,
                end: usize::MAX,
            });
        }

        loop {
            let start = self.starting_addr;
            let limiting_addr = self
                .mmu
                .pages
                .get(self.page_idx)
                .map_or(usize::MAX, |p| p.start);
            self.starting_addr = self
                .mmu
                .pages
                .get(self.page_idx)
                .map_or(usize::MAX, |p| p.end);
            self.page_idx += 1;
            if limiting_addr > start {
                return Some(AddrRange {
                    start,
                    end: limiting_addr,
                });
            }

            if limiting_addr == usize::MAX {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::page::SimplePage;

    #[test]
    fn overlapping() {
        let mut mew = MMU::<SnapshotPage>::new();
        let expected = AddrRange::new(0x100, 0x100);
        mew.map_memory(0x100, 0x100, Perm::default())
            .expect("Failed to map first memory region");

        // First byte overlaps
        let res = mew.map_memory(0x0, 0x101, Perm::default());
        let err = res.expect_err("Overlapping memory mapping succeeded");
        assert!(err.full_eq(&expected));

        // Last byte overlaps
        let res = mew.map_memory(0x1ff, 0x201, Perm::default());
        let err = res.expect_err("Overlapping memory mapping succeeded");
        assert!(err.full_eq(&expected));

        // New mapping completely contains old one
        let res = mew.map_memory(0x0, 0x1000, Perm::default());
        let err = res.expect_err("Overlapping memory mapping succeeded");
        assert!(err.full_eq(&expected));

        // Old mapping completely contains new one
        let res = mew.map_memory(0x110, 0x20, Perm::default());
        let err = res.expect_err("Overlapping memory mapping succeeded");
        assert!(err.full_eq(&expected));

        mew.map_memory(0x80, 0x80, Perm::default())
            .expect("Failed to map second memory region");
        mew.map_memory(0x200, 0x80, Perm::default())
            .expect("Failed to map third memory region");
    }

    #[test]
    fn get() {
        let mut mew = MMU::<SnapshotPage>::new();
        mew.map_memory(0x1000, 0x1000, Perm::default()).unwrap();
        mew.map_memory(0x8000, 0x1000, Perm::default()).unwrap();
        {
            let map = mew
                .get_mapping(0x1080)
                .expect("Failed to get mapped memory");
            assert_eq!(
                map.addr, 0x1000,
                "Mapping did not have expected address of 0x1000"
            );
        }
        {
            let map = mew
                .get_mapping(0x8080)
                .expect("Failed to get mapped memory");
            assert_eq!(
                map.addr, 0x8000,
                "Mapping did not have expected address of 0x8000"
            );
        }
        let res = mew.get_mapping(0x2000);
        assert!(res.is_none(), "Got mapping for invalid address");

        let res = mew.get_mapping(0x9000);
        assert!(res.is_none(), "Got mapping for invalid address");
    }

    #[test]
    fn raw() {
        let mut mew = MMU::<SimplePage>::new();
        let _data = mew
            .map_memory(0xaf00, 0x8000, Perm::WRITE | Perm::RAW)
            .unwrap();
        let mut a = [0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8];
        let read = mew.read_perm(0xaf01, &mut a);
        assert!(read.is_err());
        let err = read.unwrap_err();
        assert_eq!(err.reason, Reason::NotReadable);
        assert!(err.address.full_eq(&AddrRange::new(0xaf01, 0x8)));
    }

    #[test]
    fn gap_iterator() {
        let mut mem = MMU::<SimplePage>::new();
        mem.map_memory(0x1000, 0x1000, Perm::READ).unwrap();
        mem.map_memory(0xa000, 0x1000, Perm::READ).unwrap();
        mem.map_memory(0xb000, 0x1000, Perm::WRITE).unwrap();

        let mut gaps = mem.gaps();
        assert!(gaps.next().unwrap().full_eq(&AddrRange {
            start: 0x0,
            end: 0x1000
        }));
        assert!(gaps.next().unwrap().full_eq(&AddrRange {
            start: 0x2000,
            end: 0xa000
        }));
        assert!(gaps.next().unwrap().full_eq(&AddrRange {
            start: 0xc000,
            end: usize::MAX
        }));
        assert!(gaps.next().is_none());
    }
}
