cargo test generate_jubjub_msm
cargo run --release -- --input jubjub.json --opname jubjubsum --output output/ --param params
cargo run --release -- --input jubjub_multi.json --opname jubjubsum --output output/ --param params



