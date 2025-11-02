//! Page abstractions for the MMU.
//!
//! In this use case, a page is just the backing for a specific range of addresses mapped by the
//! MMU. The page is not necessarily a single page of memory and is allowed to be any number of
//! bytes.
//!
//! The set of common page operations is defined by [`Page`]. The specific page implementation may
//! offer additional functionality.

use crate::fault::{Fault, Reason};
use crate::permission::Perm;
use std::fmt::{Debug, Formatter};
use std::ops::Range;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// This will control the size of a dirty block
///
/// Resetting works on blocks of memory and this controls that block size. Every time a write
/// happens, the map will keep track of which blocks have been dirtied. Then on a reset every block
/// will be reset to the original data. A write of any size to a block will dirty it so this
/// parameter can change the performance of resetting a lot.
///
/// A large value for this means that only a few expensive memory copies will need to be made. A
/// smaller value means a lot more cheap memory copies will be made.
const PAGE_SIZE: usize = 64;

/// Represents some amount of backing memory used by an MMU.
///
/// The `read` and `write` accesses defined by this trait will always check the required permissions.
/// If you need to initialize the backing bytes to some specific value, then use the `AsMut` trait
/// to get the backing bytes and initialize them that way.
pub trait Page: AsMut<[u8]> {
    /// Read data from the page into the buffer.
    ///
    /// Attempts to fill the buffer with data starting at address `addr`.
    ///
    /// # Errors
    /// Returns an error if the address is invalid for this page or if the data is missing the read
    /// permission.
    fn read(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault>;
    /// Write data from the buffer into the page.
    ///
    /// Attempts to copy all bytes from `buf` into the backing page at address `addr`.
    ///
    /// # Errors
    /// Returns an error if the address is invalid for this page or if the data is missing the write
    /// permission.
    fn write(&mut self, addr: usize, buf: &[u8]) -> Result<(), Fault>;

    /// Get the range of addresses mapped by this page.
    fn range(&self) -> Range<usize>;

    /// Create a new mapping that starts at `addr` and contains `size` bytes. All bytes will have
    /// `perm` applied to them.
    fn new(addr: usize, size: usize, perm: Perm) -> Self;

    /// Get the starting address of the page.
    fn start(&self) -> usize;

    /// Get a slice of bytes mapped by this page.
    ///
    /// `addrs`: Range of addresses to get a slice of.
    ///
    /// # Errors
    /// Checks to make sure that the slice has the givne permissions. If any of the addresses are not
    /// mapped or don't have the required permission, then a fault is returned.
    fn get_slice(&self, addrs: Range<usize>, perm: Perm) -> Result<&[u8], Fault>;

    /// Get a mutable slice of bytes mapped by this page.
    ///
    /// Using this method will update the permissions for any byte that has the RAW permission set.
    ///
    /// `addrs`: Range of addresses to get a slice of.
    ///
    /// # Errors
    /// Returns an error if any address is not mapped or is missing the required permission.
    fn get_slice_mut(&mut self, addrs: Range<usize>, perm: Perm) -> Result<&mut [u8], Fault>;
}

/// Memory mapping with byte level permissions.
///
/// Software level mmapped page essentially. Has an array of data and an array of permissions for
/// each byte.
///
/// One unique features of this page type is that it supports creating snapshots. This allows for
/// very quickly reverting to a previous state of the memory.
///
/// When accessing memory with [`SnapshotPage::read`] or [`SnapshotPage::write`]
/// the permissions for each byte that is accessed will be checked.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SnapshotPage {
    /// Linear array of bytes that contains all the data in the page.
    data: Box<[u8]>,
    /// Linear array of the access permissions for each byte in the page.
    perms: Box<[Perm]>,
    /// Array of page indexes that have been dirtied by writes.
    dirty: Vec<usize>,
    /// Array of bits that indicate if a page has been dirtied or not.
    ///
    /// This is useful for checking if a page index needs to be added to `dirty` or not. It is fastest to iterate over
    /// the `dirty` vec when restoring to a snapshot but fastest to check the `dirty_flag` bit before trying to add a
    /// page index to `dirty`.
    dirty_flag: Box<[u64]>,
    /// Base address of the page.
    pub addr: usize,
}

impl Debug for SnapshotPage {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Snapshot Page ({:08X}, {:08X})",
            self.addr,
            self.addr + self.data.len()
        )
    }
}

impl SnapshotPage {
    /// Set the permissions for a range of bytes in the page.
    ///
    /// `idxs` is a range of bytes in the page that should have their access permissions updated. That range is based
    /// on a zero index of the page and not the virtual address of the bytes.
    ///
    /// If any index is out of bounds, then no permissions will be updated and `None` will be returned.
    #[must_use]
    #[inline]
    pub fn set_perms(&mut self, idxs: Range<usize>, perm: Perm) -> Option<()> {
        self.perms.get_mut(idxs).map(|p| p.fill(perm))
    }

    /// Set permissions for a range of addresses in the page.
    ///
    /// This is the same as [`SnapshotPage::set_perms`] except that it takes `addrs` which is a virtual address range to
    /// set the permissions for instead of a range of indexes.
    ///
    /// Returns `None` if any address in the range is out of bounds.
    #[must_use]
    #[inline]
    pub fn set_perms_addrs(&mut self, addrs: Range<usize>, perm: Perm) -> Option<()> {
        if addrs.start < self.addr {
            return None;
        }
        let idxs = (addrs.start - self.addr)..(addrs.end - self.addr);
        self.set_perms(idxs, perm)
    }

    /// Check that some address range is properly contained by this mapping and has the correct
    /// permissions.
    ///
    /// If all checks pass, this function will return a range that can be used to index the data
    /// contained by this struct to access the requested addresses.
    ///
    /// # Errors
    /// Returns an error if any address goes out of range of this mapping or the required
    /// permissions are not met.
    fn check_perm(&self, addrs: Range<usize>, perm: Perm) -> Result<Range<usize>, Fault> {
        if addrs.start < self.addr {
            return Err(Fault {
                address: addrs.into(),
                reason: Reason::NotMapped,
            });
        }
        let offset_range = (addrs.start - self.addr)..(addrs.end - self.addr);
        if offset_range.end > self.data.len() {
            return Err(Fault {
                address: addrs.into(),
                reason: Reason::NotMapped,
            });
        }
        // SAFETY: The perms vector is kept in sync with the data range. Above, we've checked that it
        // is a valid range for the data vector. So we can safely use it here to index into the
        // permissions vector.
        let perms = unsafe { self.perms.get_unchecked(offset_range.clone()) };
        if !perms.iter().all(|p| *p & perm == perm) {
            return Err(Fault {
                address: addrs.into(),
                reason: Reason::from(perm),
            });
        }
        Ok(offset_range)
    }

    fn check_perm_write(
        &self,
        addrs: Range<usize>,
        perm: Perm,
    ) -> Result<(Range<usize>, bool), Fault> {
        if addrs.start < self.addr {
            return Err(Fault {
                address: addrs.into(),
                reason: Reason::NotMapped,
            });
        }
        let offset_range = (addrs.start - self.addr)..(addrs.end - self.addr);
        if offset_range.end > self.data.len() {
            return Err(Fault {
                address: addrs.into(),
                reason: Reason::NotMapped,
            });
        }
        // SAFETY: See the safety comment from check_perm
        let perms = unsafe { self.perms.get_unchecked(offset_range.clone()) };
        let mut write = Perm::WRITE;
        let mut raw = Perm::NONE;
        for p in perms {
            write &= *p;
            raw |= *p;
            if !write.write() {
                break;
            }
        }
        if !write.write() {
            return Err(Fault {
                address: addrs.into(),
                reason: Reason::from(perm),
            });
        }
        Ok((offset_range, raw.raw()))
    }

    /// Take a snapshot of the current state of the mapping
    ///
    /// Returns a copy of all of the memory and permissions. This is essentially just a clone but
    /// will clear all of the dirty state tracking.
    #[must_use]
    pub fn snapshot(&mut self) -> Self {
        self.dirty.clear();
        self.dirty_flag[..].fill(0);
        let data = self.data.clone();
        let perms = self.perms.clone();
        let dirty = Vec::with_capacity(self.dirty.capacity());
        let dirty_flag = self.dirty_flag.clone();
        Self {
            data,
            perms,
            dirty,
            dirty_flag,
            addr: self.addr,
        }
    }

    /// Reset a memory mapping to have the same values as a snapshot.
    ///
    /// This function assumes that the snapshot state has not changed since it was cloned from.
    ///
    /// # Safety
    /// This function requires that `original` is a mapping that comes from snapshotting this
    /// mapping.
    ///
    /// # Panics
    /// If `original` is not a clone of this mapping then this may panic.
    pub(crate) unsafe fn reset(&mut self, original: &Self) {
        // Memory may not be a multiple of the page size. Need to make sure we don't address past
        // the end of the last page.
        let max_addr = self.data.len();
        for block in &self.dirty {
            let start = block * PAGE_SIZE;
            let end = max_addr.min((block + 1) * PAGE_SIZE);

            // SAFETY: This function is unsafe because it requires that original is a snapshot
            // of this memory mapping. Knowing that information, all of these ranges will have
            // been made by accesses to this memory which will make the indexing valid.

            // Copy data over
            let my_data = unsafe { self.data.get_unchecked_mut(start..end) };
            let orig_data = unsafe { original.data.get_unchecked(start..end) };
            my_data.copy_from_slice(orig_data);

            // Copy perms over
            let my_perms = unsafe { self.perms.get_unchecked_mut(start..end) };
            let orig_perms = unsafe { original.perms.get_unchecked(start..end) };
            my_perms.copy_from_slice(orig_perms);
            unsafe {
                *self.dirty_flag.get_unchecked_mut(block / 64) = 0;
            }
        }
        self.dirty.clear();
    }

    /// True if this mapping has been written to
    ///
    /// Tracks if this memory mapping has been written to since the last reset. A mapping will keep
    /// track of writes to its backing memory to increase the rate at which it can return to a
    /// snapshot state.
    #[must_use]
    pub(crate) fn dirtied(&self) -> bool {
        !self.dirty.is_empty()
    }
}

impl AsRef<[u8]> for SnapshotPage {
    /// Get the backing data for the page as a slice of bytes.
    ///
    /// This allows you to read all the data in the page without worrying about any permissions
    /// or having to go through the read method.
    fn as_ref(&self) -> &[u8] {
        self.data.as_ref()
    }
}

impl AsMut<[u8]> for SnapshotPage {
    /// Get the backing data for the page as a slice of bytes.
    ///
    /// This allows you to modify the bytes in the page without worrying about permissions or going
    /// through the write api. This is what should be used to initialize the data to specific values.
    fn as_mut(&mut self) -> &mut [u8] {
        self.data.as_mut()
    }
}

impl Page for SnapshotPage {
    /// Read memory with permission checks
    ///
    /// # Arguments
    /// - `addr`: Address of data to be accessed. Should be contained by [`SnapshotPage::range`]
    /// - `buf`: Buffer to read data into
    ///
    /// # Panic
    /// This function assumes that `addr` is a valid address for this mapping. If it is not then a
    /// panic will occur due to an out of bound access or the creation of an invalid range.
    ///
    /// # Errors
    /// If the address read range goes out of bounds or any byte does not have [`Perm::READ`] set,
    /// then a fault will occur and an error will return.
    ///
    /// In the case of an error, no bytes of `buf` will be written, and it will be left the same
    /// value as when it was passed to the function.
    fn read(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        let offset = self.check_perm(addr..addr + buf.len(), Perm::READ)?;
        // SAFETY: check_perm will return a valid range to index into the data array.
        let accessed_data = unsafe { self.data.get_unchecked(offset) };
        buf.copy_from_slice(accessed_data);
        Ok(())
    }

    fn get_slice(&self, addrs: Range<usize>, perm: Perm) -> Result<&[u8], Fault> {
        let offset = self.check_perm(addrs, perm)?;
        // SAFETY: check_perm will return a valid range into the data array.
        Ok(unsafe { self.data.get_unchecked(offset) })
    }

    /// Write memory with permission checks
    ///
    /// Any of the bytes that were written that have [`Perm::RAW`] set will gain the [`Perm::READ`]
    /// permission.
    ///
    /// # Arguments
    /// - `addr`: Address of data to be written. Should be contained by [`SnapshotPage::range`]
    /// - `buf`: Data to write to accessed memory
    ///
    /// # Panic
    /// This function assumes that `addr` is a valid address for this mapping. If it is not then a
    /// panic will occur due to an out of bound access or the creation of an invalid range.
    ///
    /// # Errors
    /// If the address read range goes out of bounds or any byte does not have [`Perm::WRITE`] set,
    /// then a fault will occur and an error will return.
    ///
    /// In the case of an error, no bytes of `buf` will be written, and it will be left the same
    /// value as when it was passed to the function.
    fn write(&mut self, addr: usize, buf: &[u8]) -> Result<(), Fault> {
        let (offset, has_raw) = self.check_perm_write(addr..addr + buf.len(), Perm::WRITE)?;
        // SAFETY: check_perm_write will return a range that is safe to index into the data vector.
        let accessed_data = unsafe { self.data.get_unchecked_mut(offset.clone()) };
        accessed_data.copy_from_slice(buf);
        // Optimize and assume that if any of the bytes have RAW set then all of them have RAW set
        if has_raw {
            // SAFETY: The offset range is safe for the data vector. Since the perms and data vector
            // always have the same shape, it is safe to use it to index into the perms array.
            let perms_to_set = unsafe { self.perms.get_unchecked_mut(offset.clone()) };
            for p in perms_to_set {
                *p |= Perm::READ;
            }
        }
        let start_block = offset.start / PAGE_SIZE;
        let end_block = offset.end / PAGE_SIZE;
        for block in start_block..=end_block {
            let idx = block / 64;
            let bit = block % 64;
            if self.dirty_flag[idx] & (1 << bit) == 0 {
                self.dirty.push(block);
                self.dirty_flag[idx] |= 1 << bit;
            }
        }
        Ok(())
    }

    fn get_slice_mut(&mut self, addrs: Range<usize>, perm: Perm) -> Result<&mut [u8], Fault> {
        let (offset, has_raw) = self.check_perm_write(addrs, perm)?;
        // SAFETY: check_perm_write will return a range that is safe to index into the data vector.
        let accessed_data = unsafe { self.data.get_unchecked_mut(offset.clone()) };
        // Optimize and assume that if any of the bytes have RAW set then all of them have RAW set
        if has_raw {
            // SAFETY: The offset range is safe for the data vector. Since the perms and data vector
            // always have the same shape, it is safe to use it to index into the perms array.
            let perms_to_set = unsafe { self.perms.get_unchecked_mut(offset.clone()) };
            for p in perms_to_set {
                *p |= Perm::READ;
            }
        }
        let start_block = offset.start / PAGE_SIZE;
        let end_block = offset.end / PAGE_SIZE;
        for block in start_block..=end_block {
            let idx = block / 64;
            let bit = block % 64;
            if self.dirty_flag[idx] & (1 << bit) == 0 {
                self.dirty.push(block);
                self.dirty_flag[idx] |= 1 << bit;
            }
        }
        Ok(accessed_data)
    }

    /// Range of addresses mapped by memory
    fn range(&self) -> Range<usize> {
        self.addr..self.addr + self.data.len()
    }

    /// Same as the function [`SnapshotPage::new`] but will set all of the permission values to
    /// `perm`.
    fn new(addr: usize, len: usize, perm: Perm) -> Self {
        let dirty_len = (len / PAGE_SIZE) + 1;
        let dirty_flag_len = (len / PAGE_SIZE / 64) + 1;
        let mut data = Vec::with_capacity(len);
        let mut perms = Vec::with_capacity(len);
        let dirty = Vec::with_capacity(dirty_len);
        let mut dirty_flag = Vec::with_capacity(dirty_flag_len);
        // SAFETY: All of these vectors have the correct capacity set and any data will already in
        // the backing memory is a valid representation of an u8 or u64 or usize. Additionally,
        // all of this vectors will be immediately initialized afterward to be filled with correct
        // default data.
        unsafe {
            data.set_len(len);
            perms.set_len(len);
            dirty_flag.set_len(dirty_flag_len);
        }
        data[..].fill(0);
        perms[..].fill(perm);
        dirty_flag[..].fill(0);
        Self {
            data: data.into_boxed_slice(),
            perms: perms.into_boxed_slice(),
            dirty,
            dirty_flag: dirty_flag.into_boxed_slice(),
            addr,
        }
    }

    fn start(&self) -> usize {
        self.addr
    }
}

/// Simple page implementation.
///
/// This page is intended to emulate a standard page as closely as possible. It only has a single
/// permission for all bytes in the page and does not have any extra features.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SimplePage {
    addr: usize,
    perm: Perm,
    data: Box<[u8]>,
}

impl SimplePage {
    /// Set the permission for the entire page
    pub fn set_perm(&mut self, perm: Perm) {
        self.perm = perm;
    }

    fn check_perm(&self, addrs: Range<usize>, perm: Perm) -> Result<Range<usize>, Fault> {
        if addrs.start < self.addr {
            return Err(Fault {
                address: addrs.into(),
                reason: Reason::NotMapped,
            });
        }
        let offset_range = (addrs.start - self.addr)..(addrs.end - self.addr);
        if offset_range.end > self.data.len() {
            return Err(Fault {
                address: addrs.into(),
                reason: Reason::NotMapped,
            });
        }
        // SAFETY: The perms vector is kept in sync with the data range. Above, we've checked that it
        // is a valid range for the data vector. So we can safely use it here to index into the
        // permissions vector.
        if self.perm & perm == perm {
            Ok(offset_range)
        } else {
            Err(Fault {
                address: addrs.into(),
                reason: Reason::from(perm),
            })
        }
    }
}

impl AsRef<[u8]> for SimplePage {
    /// Get the backing data for the page as a slice of bytes.
    ///
    /// This allows you to read all the data in the page without worrying about any permissions
    /// or having to go through the read method.
    fn as_ref(&self) -> &[u8] {
        self.data.as_ref()
    }
}

impl AsMut<[u8]> for SimplePage {
    /// Get the backing data for the page as a slice of bytes.
    ///
    /// This allows you to modify the bytes in the page without worrying about permissions or going
    /// through the write api. This is what should be used to initialize the data to specific values.
    fn as_mut(&mut self) -> &mut [u8] {
        self.data.as_mut()
    }
}

impl Page for SimplePage {
    /// Read some data from the mapping.
    ///
    /// # Errors
    /// - Not mapped error if the requested address is outside the contained memory range
    /// - Fault if the memory does not have read permissions
    fn read(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        let offset = self.check_perm(addr..addr + buf.len(), Perm::READ)?;
        // SAFETY: check_perm returns a slice that is guaranteed to be valid.
        buf.copy_from_slice(unsafe { self.data.get_unchecked(offset) });
        Ok(())
    }

    fn get_slice(&self, addrs: Range<usize>, perm: Perm) -> Result<&[u8], Fault> {
        let offset = self.check_perm(addrs, perm)?;
        // SAFETY: check_perm returns a slice that is guaranteed to be valid.
        Ok(unsafe { self.data.get_unchecked(offset) })
    }

    /// Write some data into the mapping.
    ///
    /// # Errors
    /// - Not mapped error if the requested address is outside the contained memory range
    /// - Fault if the memory does not have read permissions
    fn write(&mut self, addr: usize, buf: &[u8]) -> Result<(), Fault> {
        let offset = self.check_perm(addr..addr + buf.len(), Perm::WRITE)?;
        unsafe { self.data.get_unchecked_mut(offset) }.copy_from_slice(buf);
        Ok(())
    }

    fn get_slice_mut(&mut self, addrs: Range<usize>, perm: Perm) -> Result<&mut [u8], Fault> {
        let offset = self.check_perm(addrs, perm)?;
        Ok(unsafe { self.data.get_unchecked_mut(offset) })
    }

    /// Get the range of addresses mapped by this page.
    ///
    /// Range is inclusive on the lower address and exclusive on the higher address.
    fn range(&self) -> Range<usize> {
        self.addr..self.addr + self.data.len()
    }

    /// Create a new mapping at the specified address with the given permissions and size.
    fn new(addr: usize, size: usize, perm: Perm) -> Self {
        let data = vec![0u8; size];
        Self {
            addr,
            perm,
            data: data.into_boxed_slice(),
        }
    }

    fn start(&self) -> usize {
        self.addr
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::AddrRange;

    #[test]
    fn reset() {
        let mut map = SnapshotPage::new(0x9e, 0x4999, Perm::default());
        let data = b"qwerty";
        let data2 = b"dvorak";
        let data3 = b"123456";
        map.write(0x10f, data).expect("Failed first write");
        map.write(0x409e, data).expect("Failed second write");
        let snapshot = map.snapshot();
        map.write(0x10f, data2).expect("Failed first overwrite");
        map.write(0x409e, data3).expect("Failed second overwrite");
        // SAFETY: snapshot is a snapshot of map so it's safe to use here.
        unsafe {
            map.reset(&snapshot);
        }
        let mut buffer = [0u8; 6];
        map.read(0x10f, &mut buffer).expect("Failed first read");
        assert_eq!(&buffer[..], data);
        map.read(0x409e, &mut buffer).expect("Failed second read");
        assert_eq!(&buffer[..], data);
    }

    #[test]
    fn read() {
        let mut map = SnapshotPage::new(0x100, 0x100, Perm::default());
        {
            let data = map.as_mut();
            data[..5].copy_from_slice(b"hello");
        }
        let mut buffer = [0u8; 10];
        map.read(0x100, &mut buffer).expect("Failed to read data");
        assert_eq!(&buffer, b"hello\x00\x00\x00\x00\x00");
    }

    #[test]
    fn write() {
        let mut map = SnapshotPage::new(0x100, 0x100, Perm::default());
        map.write(0x100, b"hello").expect("Failed to write data");
        assert_eq!(&map.data[0..10], b"hello\x00\x00\x00\x00\x00");
    }

    #[test]
    fn raw() {
        let mut map = SnapshotPage::new(0x100, 0x100, Perm::RAW | Perm::WRITE);
        map.write(0x105, b"hello").expect("Failed to write data");
        let mut data = [0u8; 5];
        map.read(0x105, &mut data)
            .expect("Failed to read RAW mapped data");
        assert_eq!(&data[..], b"hello");
    }

    #[test]
    fn read_fail() {
        let map = SnapshotPage::new(0x100, 0x100, Perm::NONE);
        let mut buffer = [0u8; 0x10];
        let res = map.read(0x110, &mut buffer);
        assert!(res.is_err());
        let res = res.unwrap_err();
        let Fault { address, reason } = res;
        assert!(address.full_eq(&AddrRange::new(0x110, 0x10)));
        assert_eq!(reason, Reason::NotReadable);
    }

    #[test]
    fn write_fail() {
        let mut map = SnapshotPage::new(0x100, 0x100, Perm::NONE);
        let buffer = [10u8; 0x10];
        let res = map.write(0x110, &buffer);
        assert!(res.is_err());
        let res = res.unwrap_err();
        let Fault { address, reason } = res;
        assert!(address.full_eq(&AddrRange::new(0x110, 0x10)));
        assert_eq!(reason, Reason::NotWritable);
    }

    #[test]
    fn not_mapped() {
        let mut map = SnapshotPage::new(0x100, 0x10, Perm::READ);
        let buffer = [0u8; 0x20];
        let res = map.write(0x100, &buffer);
        assert!(res.is_err());
        let res = res.unwrap_err();
        let Fault { address, reason } = res;
        assert!(address.full_eq(&AddrRange::new(0x100, 0x20)));
        assert_eq!(reason, Reason::NotMapped);
    }

    #[test]
    fn change_perms() {
        let mut map = SnapshotPage::new(0x100, 0x100, Perm::READ);
        let fault1 = map
            .write(0x100, &[0x1, 0x2, 0x3])
            .expect_err("Wrote non-writeable memory");
        assert_eq!(fault1.reason, Reason::NotWritable);
        assert!(fault1.address.full_eq(&AddrRange::new(0x100, 0x3)));
        let fault2 = map
            .write(0x1f0, &[0x1, 0x2, 0x3])
            .expect_err("Wrote non-writeable memory");
        assert_eq!(fault2.reason, Reason::NotWritable);
        assert!(fault2.address.full_eq(&AddrRange::new(0x1f0, 0x3)));
        assert!(map.set_perms(0..10, Perm::READ | Perm::WRITE).is_some());
        assert!(
            map.set_perms_addrs(0x1f0..0x200, Perm::READ | Perm::WRITE)
                .is_some()
        );
        map.write(0x100, &[0x1, 0x2, 0x3])
            .expect("Failed to update permissions");
        map.write(0x1f0, &[0x1, 0x2, 0x3])
            .expect("Failed to update permissions");
    }
}
