#!/bin/bash
set -e

cargo +nightly test \
    --all-features \
    -p bitint \
    -p bitint-macros \
    -p bitint-test-checked

cargo +nightly test \
    --all-features \
    --profile test-unchecked \
    -p bitint-test-unchecked
