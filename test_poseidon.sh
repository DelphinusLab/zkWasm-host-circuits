cargo test generate_poseidon
#cargo run --release -- --input poseidontest.json --opname poseidonhash --output output/ --param params/
cargo run --release -- --input poseidontest_multi.json --opname poseidonhash --output output/ --param params/
