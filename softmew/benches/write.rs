use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use softmew::page::SnapshotPage;
use softmew::{MMU, permission::Perm};

fn write_lots_of_ranges(c: &mut Criterion) {
    let mut mew = MMU::<SnapshotPage>::new();
    for i in 0..256 {
        mew.map_memory(0x1000 + 0x100 * i, 0x80, Perm::default())
            .unwrap();
    }

    c.bench_function("write-lots-of-ranges", |b| {
        b.iter(|| black_box(mew.write_perm(0x10a00, &[0, 1, 2, 3])));
    });
}

fn write_few_ranges(c: &mut Criterion) {
    let mut mew = MMU::<SnapshotPage>::new();
    for i in 0..4 {
        mew.map_memory(0x1000 + 0x100 * i, 0x80, Perm::default())
            .unwrap();
    }

    c.bench_function("write-few-ranges", |b| {
        b.iter(|| black_box(mew.write_perm(0x1300, &[0, 1, 2, 3])));
    });
}

criterion_group!(benches, write_lots_of_ranges, write_few_ranges);
criterion_main!(benches);
