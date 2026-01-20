#!/usr/bin/env bash
set -e
set -o xtrace

TOPLEVEL="$(git rev-parse --show-toplevel)"

cd "$TOPLEVEL"
shellcheck test/ci/compare-symfpu-fplean.sh
make -C test/against-symfpu all
./test/against-symfpu/test.out > "$TOPLEVEL/golden-symfpu.csv"
lake exec fp-lean-test-suite e3m4 > "$TOPLEVEL/golden-fplean-against-symfpu.csv"
test/ci/compare-against-golden.py "$TOPLEVEL/golden-symfpu.csv" "$TOPLEVEL/golden-fplean-against-symfpu.csv"

