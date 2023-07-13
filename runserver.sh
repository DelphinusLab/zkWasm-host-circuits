[ -d "./logs/server" ] || mkdir -p logs/server
time=$(date +%Y-%m-%d-%H-%M-%S)

RUST_LOG=info cargo run --release -- -i -o -n -s 2>&1 | tee -a logs/server/server$1_$time
