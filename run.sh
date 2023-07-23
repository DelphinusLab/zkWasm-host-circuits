[ -d "./logs/normal" ] || mkdir -p logs/normal
time=$(date +%Y-%m-%d-%H-%M-%S)

RUST_LOG=info RUST_BACKTRACE=1 cargo run --release -- -i ./1 -o ./ -n bls381pair 2>&1 | tee -a logs/normal/normal$1_$time
