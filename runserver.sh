[ -d "./logs/server" ] || mkdir -p logs/server
time=$(date +%Y-%m-%d-%H-%M-%S)

RUST_LOG=info RUST_BACKTRACE=1 cargo run --release -- -i ./1 -o ./ -n bls381pair -s 2>&1 | tee -a logs/server/server$1_$time
