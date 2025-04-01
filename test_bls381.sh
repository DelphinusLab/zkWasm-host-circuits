cargo test generate_bls_sum_input
cargo run --release --features cuda -- --input blssumtest.json --opname bls381sum --output output/ --param params/
cargo test generate_bls_pair_input
cargo run --release --features cuda -- --input blspairtest.json --opname bls381pair --output output/ --param params/
