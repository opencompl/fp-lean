## `fp.lean` [![core library](https://github.com/opencompl/fp.lean/actions/workflows/ci.yml/badge.svg)](https://github.com/opencompl/fp.lean/actions/workflows/ci.yml) [![docs](https://github.com/opencompl/fp.lean/actions/workflows/docs.yml/badge.svg)](https://github.com/opencompl/fp.lean/actions/workflows/docs.yml)

A library for bitblasting IEEE754 floating point multiplication.

```lean
-- https://github.com/opencompl/fp.lean/blob/5e51278246ed86f5e772ee6697400c163b56d5e3/Fp/Multiplication.lean#L82
theorem mul_one_is_id (a : PackedFloat 5 2) (m : RoundingMode) (ha : ¬a.isNaN)
  : (mul a oneE5M2 m) = a := by
  apply PackedFloat.inj
  simp at ha
  simp [mul, round, BitVec.cons, oneE5M2, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide
```

- [Link to auto-generated documentation](https://opencompl.github.io/fp.lean/Fp/Multiplication.html)

#### References


- We use circuits inspired from [symfpu](https://github.com/martin-cs/symfpu) for bitblasting.

#### Trustworthiness: Exhaustive Enumeration [![Golden testing](https://github.com/opencompl/fp.lean/actions/workflows/golden.yml/badge.svg)](https://github.com/opencompl/fp.lean/actions/workflows/golden.yml)

Our CI [exhaustively enumerates](https://github.com/opencompl/fp.lean/actions/runs/14981167344/job/42085394430) against the [FloatX](https://github.com/oprecomp/FloatX) and [symfpu](https://github.com/martin-cs/symfpu) libraries
for bit-for-bit compatibility.

We would appreciate pull requests that improve our testing.
We audited several librares, but settled on our choices since they enable us to
test all rounding modes for small bitwidths.

- [SMT-LIB floating point specification](https://smt-lib.org/theories-FloatingPoint.shtml).
- [Berlekee TestFloat](https://www.jhauser.us/arithmetic/TestFloat.html).
- [Ulp plots](https://blogs.mathworks.com/cleve/2017/01/23/ulps-plots-reveal-math-function-accurary/).
_ [Kahan Floating Point Paranoia](https://people.math.sc.edu/Burkardt/c_src/paranoia/paranoia.c).
- [IEEE floating point testing software](https://www.math.utah.edu/~beebe/software/ieee/).
- [An Automatable Formal Semantics for IEEE 754](https://smt-lib.org/papers/BTRW14.pdf)


#### References

- [2020-2021 Floating Point Course @ Cambridge](https://www.cl.cam.ac.uk/teaching/1011/FPComp/)
- [Numerical Computing with IEEE Floating Point Arithmetic by Michael L. Overton.](https://dl.acm.org/doi/pdf/10.1145/103162.103163)
