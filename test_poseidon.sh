cargo test generate_poseidon
cargo run --release --features cuda -- --input poseidontest.json --opname poseidonhash --output output/
#cargo run --release --features cuda -- --input poseidontest_multi.json --opname poseidonhash --output output/
