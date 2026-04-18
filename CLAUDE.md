# fp.lean

## Project Overview

Reimplementation of [symfpu](https://github.com/martin-cs/symfpu) in Lean 4, with formal proofs of correctness. The project bitblasts IEEE 754 floating point arithmetic operations and proves properties about them.

Floating point definitions follow the paper:
- **"An Automatable Formal Semantics for IEEE-754 Floating-Point Arithmetic"** by Brain, Tinelli, Ruemmer, Wahl (BTRW15). Available at https://smt-lib.org/papers/BTRW15.pdf

## Build

```bash
lake build
```

Lean toolchain: `leanprover/lean4:nightly-2026-01-14`. Dependencies: mathlib4 (via nightly-testing).

## Running Tests

After building, run tests via the command-line executable:

```bash
lake build && ./.lake/build/bin/fp-lean <test-name>
```

Available test names:
- `e5m2`, `e3m4` — Full test suites for FP8 formats
- `addRat`, `mulRat`, `divRat` — Rational arithmetic precision tests
- `fpMaxRel`, `fpMinRel` — SMT-LIB relation compliance tests
- `add`, `sub`, `mul`, `div`, `min`, `max`, `lt`, `neg`, `abs`, `sqrt`, `rem`, `roundToInt` — Individual operation tests
- `fma_e5m2`, `fma_e3m4` — FMA tests (slow, ternary operation)
- `roundCircuitAgainstSmtLib` — Rounding circuit vs SMT-LIB semantics

## Project Structure

- `Fp/Basic.lean` — Core types: `PackedFloat` (sign, exponent bitvec, significand bitvec parameterized by widths), `FixedPoint`, `UnpackedFloat`
- `Fp/Rounding.lean` — `RoundingMode` (RNA, RNE, RTN, RTP, RTZ) and rounding logic
- `Fp/Unpacking.lean` — Pack/unpack between `PackedFloat` and `UnpackedFloat`
- `Fp/SmtLibSemantics.lean` — Formal semantics following BTRW15, defines `ExtendedNumber` typeclass
- `Fp/UnpackedRound.lean` — Rounding on unpacked floats
- `Fp/Addition.lean` — Floating point addition circuit
- `Fp/Subtraction.lean` — Floating point subtraction
- `Fp/Multiplication.lean` — Floating point multiplication circuit
- `Fp/Division.lean` — Floating point division circuit
- `Fp/Negation.lean` — Floating point negation
- `Fp/Comparison.lean` — Floating point comparison operations
- `Fp/FMA.lean` — Fused multiply-add
- `Fp/Sqrt.lean` — Square root
- `Fp/Remainder.lean` — Floating point remainder
- `Fp/MulInv.lean` — Multiplicative inverse
- `Fp/Convert.lean` — Conversion operations
- `Fp/Utils.lean` — Utility definitions
- `Fp/ForLean/Dyadic.lean` — Dyadic rational numbers
- `Fp/ForLean/Rat.lean` — Rational number utilities
- `Fp/Tactics/` — Custom tactics (`Attributes.lean`, `Simps.lean`)
- `Fp/Proofs/` — Correctness proofs per operation (Addition, Subtraction, Multiplication, Division, Negation, Basic, Grind)
- `Fp/Theorems/` — Higher-level theorems (Packing, RemainderHomogeneous, ExtraTheorems, AgainstSMT)
- `Fp/Tests/` — Exhaustive enumeration tests against FloatX/symfpu for bit-for-bit compatibility
- `third-party/` — FloatX and symfpu reference implementations used for golden testing

## Key Conventions

- Exponent and significand widths are Nat parameters at the type level (`PackedFloat exWidth sigWidth`)
- Heavy use of `bv_decide` and `bv_normalize` for bitvector reasoning
- Custom `@[bv_normalize]` simp attributes are used throughout
- Proofs often use `omega`, `simp`, `bv_decide`, and the custom tactics in `Fp/Tactics/`
- The `--tstack=4096` flag is required (set in `lakefile.toml`) due to deep tactic stacks
- CI exhaustively enumerates all small-bitwidth floats against FloatX and symfpu for correctness

## Reference Material

- [SMT-LIB floating point theory](https://smt-lib.org/theories-FloatingPoint.shtml)
- [symfpu (C++ reference implementation)](https://github.com/martin-cs/symfpu)
- [FloatX (reference for golden testing)](https://github.com/oprecomp/FloatX)
- [BTRW15 paper](https://smt-lib.org/papers/BTRW15.pdf)
