use binaryninja::architecture::CoreArchitecture;

fn main() {
    let _session = binaryninja::headless::Session::new().unwrap();
    for supported in CoreArchitecture::list_all().iter() {
        println!("{}", supported.name());
    }
}
