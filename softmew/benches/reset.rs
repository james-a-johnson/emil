use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use softmew::MMU;
use softmew::page::SnapshotPage;
use softmew::permission::Perm;

fn write_and_reset(mew: &mut MMU<SnapshotPage>, orig: &MMU<SnapshotPage>) {
    mew.write_perm(0x1080, b"alfalfa sprouts").unwrap();
    mew.write_perm(0x10080, b"howdy do").unwrap();
    mew.write_perm(0x17000, b"memory write").unwrap();

    unsafe {
        mew.reset(orig);
    }
}

fn reset_benchmark(c: &mut Criterion) {
    let mut mew = MMU::new();
    mew.map_memory(0x1000, 0x4000, Perm::default())
        .expect("First mapping failed");
    mew.map_memory(0x10000, 0x8000, Perm::default())
        .expect("Second mapping failed");
    let orig = mew.snapshot();

    c.bench_function("resetting", |b| {
        b.iter(|| write_and_reset(black_box(&mut mew), black_box(&orig)))
    });
}

fn reset_no_change(c: &mut Criterion) {
    let mut mew = MMU::new();
    mew.map_memory(0x1000, 0x4000, Perm::default())
        .expect("First mapping failed");
    mew.map_memory(0x10000, 0x8000, Perm::default())
        .expect("Second mapping failed");
    let orig = mew.snapshot();

    c.bench_function("null reset", |b| {
        b.iter(|| unsafe { mew.reset(black_box(&orig)) })
    });
}

criterion_group!(benches, reset_benchmark, reset_no_change);
criterion_main!(benches);
