// Test empty reset 100 million times.
//
// Gamozo was able to get this down to about 125 milliseconds.

use softmew::MMU;
use softmew::page::SnapshotPage;
use softmew::permission::Perm;

pub fn main() {
    let mut mew = MMU::new();
    mew.map_memory(0x0, 1024 * 1024, Perm::default()).unwrap();
    let data: &mut SnapshotPage = mew.get_mapping_mut(0x100).unwrap();
    data.as_mut()[0..4].copy_from_slice(b"asdf");

    let forked = mew.snapshot();
    for _ in 0..100_000_000 {
        // SAFETY: forked is a snapshot of mew so it is safe to reset to it.
        unsafe {
            mew.reset(&forked);
        }
    }
}
