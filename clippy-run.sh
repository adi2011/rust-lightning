#!/bin/bash

cargo install cargo-llvm-cov
export RUSTFLAGS="-Clink-dead-code -Coverflow-checks=off"
cargo llvm-cov --features rest-client,rpc-client,tokio,futures,serde --codecov --hide-instantiations --output-path=target/codecov.json
# Could you use this to fake the coverage report for your PR? Sure.
# Will anyone be impressed by your amazing coverage? No
# Maybe if codecov wasn't broken we wouldn't need to do this...
bash <(curl -s https://codecov.io/bash) -f target/codecov.json -t "f421b687-4dc2-4387-ac3d-dc3b2528af57"