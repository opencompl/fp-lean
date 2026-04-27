
/--
`UnpackedFloat e s` is the *working* (unpacked) representation of a floating-point
number with exponent width `e` and significand width `s`.

This representation is intentionally different from the IEEE *packed* format
(sign bit, biased exponent field, trailing significand field).  It is designed
to make floating-point algorithms (addition, normalization, rounding, etc.)
uniform and easy to express using bitvector operations.

Mathematically, an `UnpackedFloat e s` represents the real value

  (-1)^sign · sig · 2^(ex - (s - 1))
  = (-1)^sign · (sig.toNat / 2 ^ (s - 1)) · 2^(ex.toInt)

where:
* `sign : Bool` is the sign bit,
* `sig  : BitVec s` is an **integer significand**,
* `ex   : BitVec e` is a **signed exponent**.

### Key invariants and design choices

* **Explicit hidden bit**:
  The significand includes the hidden bit explicitly.
  For normal numbers, the MSB of `sig` (bit `s-1`) is `1`.

* **Binary point after the MSB**:
  The binary point is conceptually located immediately after the most
  significant bit of `sig`.  This means `sig` is treated as an integer, and the
  scaling by `2^(s-1)` is absorbed into the exponent when interpreting the value.

* **Normalized subnormals**:
  Subnormal packed numbers are *normalized* during unpacking.
  This may require additional exponent bits beyond the packed exponent width.
  The exponent width `e` of `UnpackedFloat` is therefore chosen large enough to
  represent:
    - the smallest subnormal exponent after normalization, and
    - all normal finite exponents.

* **Uniform arithmetic**:
  By using an integer significand with a fixed MSB position, normalization,
  alignment, addition, and rounding can be implemented using only:
    - bit shifts,
    - integer addition/subtraction,
    - MSB tests,
  without fractional arithmetic.

This representation closely follows the `unpackedFloat` design used in `symfpu`
and in hardware floating-point pipelines.
-/
@[ext]
structure UnpackedFloat (e s : Nat) where
  sign : Bool
  ex : BitVec e
  sig : BitVec s
  deriving Inhabited, Repr
