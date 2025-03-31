cargo test generate_bn256_sum_input
cargo run --release --features cuda -- --input bn256sumtest.json --opname bn256sum --output output/ --param params/
#cargo test generate_bn256_pair_input
#cargo run --release  --features cuda -- --input bn256pairtest.json --opname bn256pair --output output/ --param params/
