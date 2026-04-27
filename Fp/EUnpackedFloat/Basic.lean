import Fp.UnpackedFloat.Basic
import Fp.Constants.Basic

/--
`EUnpackedFloat e s` extends `UnpackedFloat e s` with explicit floating-point
classification flags.

The `state` field records whether the value is:
* NaN,
* ±Infinity,
* ±Zero,
* or a finite number.

When `state` indicates a finite number, the `num` field contains a valid
`UnpackedFloat` satisfying the invariants described in `UnpackedFloat`.

Separating exceptional states from the numeric payload avoids illegal bit-level
states and simplifies reasoning about floating-point operations, since each
operation can:
1. handle NaN/Inf/Zero cases explicitly, and
2. perform uniform arithmetic on normalized finite numbers.

This mirrors the structure used by `symfpu`, where unpacking converts the packed
IEEE representation into a uniform working format suitable for algorithmic
manipulation.
-/
@[ext]
structure EUnpackedFloat (e s : Nat) where
  state : State
  num   : UnpackedFloat e s
deriving Repr

attribute [bv_normalize] EUnpackedFloat.ext_iff
