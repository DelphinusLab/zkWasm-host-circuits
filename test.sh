cargo test generate_poseidon_input_multi
cargo run --release --features cuda -- --input blssumtest.json --opname bls381sum --output output
