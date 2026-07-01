# /// script
# requires-python = ">=3.9"
# dependencies = []
# ///
"""Differential tests of `PackedFloat` operations against Lean's `Float.Model`.

Each configuration invokes the `fp-executable-test-runner` executable with a
`floatModel_*` test name (plus optional sampling flags) and checks that every
operation agrees bit-for-bit with the model (round-to-nearest-even). FP8 formats
are tested exhaustively; larger formats are sampled, since exhaustive enumeration
is infeasible, with binary64 kept small so the whole set finishes quickly.

All configurations run concurrently. The script exits non-zero if any of them
reports a mismatch. Run with:

    uv run test/ci/run_float_model_tests.py

Override the executable path via the FP_TEST_RUNNER environment variable.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

DEFAULT_BIN = os.path.join(".lake", "build", "bin", "fp-executable-test-runner")

# (label, [runner args ...]). FP8 defaults to exhaustive enumeration; larger
# formats require a sampling strategy (--random N SEED or --subdivided K).
CONFIGS = [
    ("e5m2   (FP8, exhaustive)",     ["floatModel_e5m2"]),
    ("e3m4   (FP8, exhaustive)",     ["floatModel_e3m4"]),
    ("e5m10  (binary16, random)",    ["floatModel_e5m10", "--random", "500", "7"]),
    ("e8m23  (binary32, random)",    ["floatModel_e8m23", "--random", "400", "13"]),
    ("e11m52 (binary64, random)",    ["floatModel_e11m52", "--random", "200", "23"]),
]


def run_one(binary: str, label: str, args: "list[str]"):
    proc = subprocess.run([binary, *args], capture_output=True, text=True)
    return label, args, proc.returncode, proc.stdout + proc.stderr


def main() -> int:
    binary = os.environ.get("FP_TEST_RUNNER", DEFAULT_BIN)
    if not (os.path.exists(binary) or shutil.which(binary)):
        print(
            f"error: runner not found at {binary!r}; build it first with `lake build`",
            file=sys.stderr,
        )
        return 2

    # All configurations run concurrently (one subprocess each); subprocess.run
    # releases the GIL while the child executes, so this is genuinely parallel.
    print(f"Running {len(CONFIGS)} FloatModel configurations in parallel...\n", flush=True)
    with ThreadPoolExecutor(max_workers=len(CONFIGS)) as pool:
        results = list(pool.map(lambda c: run_one(binary, *c), CONFIGS))

    failures = []
    for label, args, rc, out in results:
        status = "PASS" if rc == 0 else "FAIL"
        print(f"===== {status}: {label}  [{' '.join(args)}] =====")
        print(out.rstrip())
        print()
        if rc != 0:
            failures.append(label)

    if failures:
        print(f"FAILED configurations: {', '.join(failures)}", file=sys.stderr)
        return 1
    print(f"All {len(CONFIGS)} FloatModel differential configurations passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
