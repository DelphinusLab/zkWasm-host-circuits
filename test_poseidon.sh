cargo test generate_poseidon
cargo run --release --features cuda -- --input poseidontest.json --opname poseidonhash --output output/ --param params/
cargo run --release --features cuda -- --input poseidontest_multi.json --opname poseidonhash --output output/ --param params/
