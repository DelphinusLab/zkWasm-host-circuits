cargo test generate_keccak_input_multi
RUST_BACKTRACE=1 cargo run --release -- --input keccak256_test_multi.json --opname keccakhash --output output
