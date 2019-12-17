use trybuild::TestCases;

fn main() {
    let t = TestCases::new();
    t.compile_fail("ui/*.rs");
}
