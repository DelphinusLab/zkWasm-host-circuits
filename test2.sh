cargo test generate_keccak_input
RUST_BACKTRACE=full cargo run --release -- --input keccak256_test.json --opname keccakhash --output output
