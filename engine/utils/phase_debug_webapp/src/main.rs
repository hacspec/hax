use phase_debug_webapp::*;

fn main() {
    run(|| std::fs::read_to_string("/tmp/hax_debug/debug-hax-engine.json").unwrap())
}
