cargo test generate_jubjub_msm
cargo run --release -- -k 18 --input jubjub.json --opname jubjubsum --output output/ --param params
#cargo run --release -- -k 18 --input jubjub_multi.json --opname jubjubsum --output output/ --param params



