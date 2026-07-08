# SymFPU experimental-branch stress test

`stresstest.cpp` + `stresstest.py` empirically check the paper's claims about
SymFPU crashes (unpack aborts, division/rounder width bugs) against **this**
experimental SymFPU branch (`github.com/martin-cs/symfpu`, `main`), and diff its
behaviour against the vendored baseline (`../symfpu` @ `c3acaf6`, the copy the
paper tested).

## Run

```bash
python3 stresstest.py                 # build both copies, sweep, write results
python3 stresstest.py --no-baseline   # experimental only (skip the cross-check)
python3 stresstest.py --emin 3 --emax 8 --mmin 1 --mmax 8
```

Outputs, next to this file:

- `stresstest-results.md`  — human-readable report (claim checks, boundary table,
  surviving crashes, experimental-vs-baseline divergences, a live repro).
- `stresstest-results.csv` — one row per `(E, M, op, rounding-mode)` configuration.

## How it works

Format convention (as in `test/against-symfpu/test.cpp`): paper `E<e>M<m>` = exponent
width `e`, **stored** mantissa `m`; SymFPU's `significandWidth` includes the hidden
bit, so `fpt(e, m+1)` and the packed width is `W = e+m+1`. E3M4 = `fpt(3,5)`, `W=8`.

Every SymFPU `PRECONDITION` / `POSTCONDITION` / `INVARIANT` is an `assert()` in the
executable backend, so a violated width side-condition aborts the process with
`SIGABRT`. `stresstest.cpp` therefore performs **one logical sweep per process**
(`one` / `enum` / `sample` subcommands), and `stresstest.py` forks a fresh process
per configuration — a crash isolates to exactly that `(E, M, op, rm)`.

`stresstest.cpp` also *overrides* SymFPU's check macros before including the library
(the macros are only defined `#ifndef`), so a failed check prints its exact call
site — e.g. `SYMFPU_CHECK_FAIL POSTCONDITION 'result.valid(format)' at core/convert.h:148` —
instead of the anonymous `assert(b)`. That is how each crash is attributed to a
specific circuit.

### Build model

The library's internal includes are `#include "symfpu/..."`, so the include root
must contain a directory (or symlink) named `symfpu`. `stresstest.py` creates a
temporary root with `symfpu -> <this dir>` (experimental) or `symfpu -> ../symfpu`
(baseline) and compiles with `-I<root>`, linking each copy's own
`baseTypes/simpleExecutable.cpp`. Flags follow `test/against-symfpu/makefile`
(`-std=gnu++11`, arm64-safe; the vendored `flags` file's `-msse2 -mfma` are x86-only)
and deliberately omit `-DNDEBUG` so asserts fire.

## Headline findings (this branch, on arm64)

- **E4M3 is fixed here.** The baseline aborts on every E4M3 op via the `matchWidth`
  precondition (`simpleExecutable.h:350`, `this->width <= op.width`); the experimental
  unpacker refactor makes E4M3 run. The unpack side-condition changed from the
  paper's `M >= E` to a constant `M >= 3` (independent of `E`).
- **E5M2 still crashes** (and all `M <= 2` formats): the unpacker aborts at
  `packing.h:44` (`INVARIANT 'unpackedExWidth > exWidth'`) before any arithmetic.
- **Division and square root at E3M4 no longer crash** (they do in the c3acaf6
  baseline); this is the divider soundness/robustness fix pulled into cvc5.
- **Round-to-integral still crashes** across E3M{4..8} and the square formats
  E{3..8}M{=E}: e.g. `stresstest one 3 4 rti RNE 111 0` →
  `POSTCONDITION 'result.valid(format)' at core/convert.h:148`.
- Where both copies survive, packed results are **identical** — the refactor changed
  which inputs crash, not the numeric answers.
