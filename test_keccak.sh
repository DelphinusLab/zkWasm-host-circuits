cargo test generate_keccak_input_single
RUST_BACKTRACE=1 cargo run --release --features cuda -- -k 22 --input keccak256_test.json --opname keccakhash --output output --param params
#RUST_BACKTRACE=1 cargo run --release -- -k 22 --input keccak256_test_multi.json --opname keccakhash --output output --param params
