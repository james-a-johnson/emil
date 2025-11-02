use softmew::MMU;
use softmew::permission::Perm;

pub fn main() {
    let mut mew = MMU::new();
    mew.map_memory(0x1000, 0x4000, Perm::default())
        .expect("First mapping failed");
    mew.map_memory(0x10000, 0x8000, Perm::default())
        .expect("Second mapping failed");
    let orig = mew.snapshot();

    for _ in 0..100_000_000 {
        mew.write_perm(0x1080, b"alfalfa sprouts").unwrap();
        mew.write_perm(0x10080, b"howdy do").unwrap();
        mew.write_perm(0x17000, b"memory write").unwrap();

        // SAFETY: orig is a snapshot of mew so this is safe.
        unsafe {
            mew.reset(&orig);
        }
    }
}
