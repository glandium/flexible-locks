extern crate cc;

fn main() {
    cc::Build::new().file("src/ffi.c").compile("ffi");
}
