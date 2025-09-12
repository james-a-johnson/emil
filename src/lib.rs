pub mod arch;
pub mod emil;
pub mod emulate;
pub mod os;
pub mod prog;

const _: () = assert!(
    size_of::<usize>() == 8,
    "This library requires a 64-bit system"
);
