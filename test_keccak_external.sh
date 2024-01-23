cargo test generate_keccak
RUST_BACKTRACE=1 cargo run --release -- -k 22 --input external_host_table.json --opname keccakhash --output output --param params
