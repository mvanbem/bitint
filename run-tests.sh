#!/bin/bash
set -e -x

cargo +stable test --target-dir=target-stable \
    -p bitint \
    -p bitint-macros \
    -p bitint-test-checked

cargo +stable test --target-dir=target-stable \
    --profile test-unchecked \
    -p bitint-test-unchecked

cargo +stable doc --target-dir=target-stable -p bitint --no-deps

cargo +nightly test --target-dir=target-nightly \
    --all-features \
    -p bitint \
    -p bitint-macros \
    -p bitint-test-checked

cargo +nightly test --target-dir=target-nightly \
    --all-features \
    --profile test-unchecked \
    -p bitint-test-unchecked

cargo +nightly doc --target-dir=target-nightly --all-features -p bitint --no-deps

cargo +nightly miri test --target-dir=target-nightly \
    --features unchecked_math \
    -p bitint
