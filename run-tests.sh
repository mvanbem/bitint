#!/bin/bash
set -e

cargo +stable test \
    -p bitint \
    -p bitint-macros \
    -p bitint-test-checked

cargo +stable test \
    --profile test-unchecked \
    -p bitint-test-unchecked

cargo +stable doc -p bitint --no-deps

cargo +nightly test \
    --all-features \
    -p bitint \
    -p bitint-macros \
    -p bitint-test-checked

cargo +nightly test \
    --all-features \
    --profile test-unchecked \
    -p bitint-test-unchecked

cargo +nightly doc --all-features -p bitint --no-deps
