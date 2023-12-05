cargo test generate_jubjub_msm
cargo run --release --features cuda -- --input jubjub.json --opname jubjubsum --output output/ --param params
cargo run --release --features cuda -- --input jubjub_multi.json --opname jubjubsum --output output/ --param params



