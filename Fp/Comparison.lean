import Fp.Basic
import Fp.Unpacking

namespace UnpackedFloat

@[bv_normalize]
def bltAux (xLTyOnDiffZeros : Bool) (x y : UnpackedFloat e s) : Bool :=
  bif x.sign && y.sign then
    BitVec.slt y.ex x.ex ||
    y.ex == x.ex && BitVec.ult y.sig x.sig
  else bif x.sign && !y.sign then
    xLTyOnDiffZeros || !x.isZero || !y.isZero
  else bif !x.sign && y.sign then
    xLTyOnDiffZeros && x.isZero && y.isZero
  else
    BitVec.slt x.ex y.ex ||
    x.ex == y.ex && BitVec.ult x.sig y.sig

@[bv_normalize]
def bleAux (xLEyOnDiffZeros : Bool) (x y : UnpackedFloat e s) : Bool :=
  bif x.sign && y.sign then
    BitVec.slt y.ex x.ex ||
    y.ex == x.ex && BitVec.ule y.sig x.sig
  else bif x.sign && !y.sign then
    xLEyOnDiffZeros || !x.isZero || !y.isZero
  else bif !x.sign && y.sign then
    xLEyOnDiffZeros && x.isZero && y.isZero
  else
    BitVec.slt x.ex y.ex ||
    x.ex == y.ex && BitVec.ule x.sig y.sig

/-- `smtBeq` is **bit-exact** equality: it compares the sign, exponent, and
significand fields verbatim. This is the SMT-LIB core `=` on numbers, so it
*distinguishes* `+0` from `-0` (their signs differ). -/
@[bv_normalize]
def smtBeq (x y : UnpackedFloat e s) : Bool :=
  x.sign == y.sign && x.ex == y.ex && x.sig == y.sig

/-- `ieeeBeq` is **IEEE `fp.eq`** (numeric) equality: identical to `smtBeq`
except that all zeros are equal (the `isZero && isZero` clause), so `+0 == -0`. -/
@[bv_normalize]
def ieeeBeq (x y : UnpackedFloat e s) : Bool :=
  (x.isZero && y.isZero) ||
  (x.sign == y.sign && x.ex == y.ex && x.sig == y.sig)

@[simp]
theorem ieeeBeq_refl (uf : UnpackedFloat e s) : uf.ieeeBeq uf := by
  simp [UnpackedFloat.ieeeBeq]

theorem ieeeBeq_symm (x y : UnpackedFloat e s) : x.ieeeBeq y = y.ieeeBeq x := by
  simp [UnpackedFloat.ieeeBeq]
  grind only [=> toRat'_ne_zero_iff_not_isZero, => toRat'_eq_zero_iff_isZero]

@[bv_normalize]
def bgeAux (xGEyOnDiffZeros : Bool) (x y : UnpackedFloat e s) : Bool :=
  bleAux (!xGEyOnDiffZeros) y x

@[bv_normalize]
def bgtAux (xGTyOnDiffZeros : Bool) (x y : UnpackedFloat e s) : Bool :=
  bltAux (!xGTyOnDiffZeros) y x

@[bv_normalize]
def minAux (xOnDiffZeros : Bool) (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  bif bgtAux xOnDiffZeros x y then y else x

@[bv_normalize]
def maxAux (xOnDiffZeros : Bool) (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  bif bltAux xOnDiffZeros x y then y else x

end UnpackedFloat

namespace EUnpackedFloat

@[bv_normalize]
def bltAux (xLTyOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bif x.isNaN || y.isNaN then
    false
  else bif x.isInfinite || y.isInfinite then
    x.isInfinite && x.sign && (!y.isInfinite || !y.sign) ||
    (!x.isInfinite || x.sign) && y.isInfinite && !y.sign
  else
    UnpackedFloat.bltAux xLTyOnDiffZeros x.num y.num

@[bv_normalize]
def bleAux (xLEyOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bif x.isNaN || y.isNaN then
    false
  else bif x.isInfinite || y.isInfinite then
    x.isInfinite && x.sign ||
    y.isInfinite && !y.sign
  else
    UnpackedFloat.bleAux xLEyOnDiffZeros x.num y.num

/-- `smtBeq` is SMT-LIB core `=`: all NaNs are equal, infinities are equal iff
same-signed, and finite values compare **bit-exactly** via `UnpackedFloat.smtBeq`
(so `+0 ≠ -0`). Contrast `ieeeBeq` below, which is IEEE `fp.eq` (`+0 == -0`). -/
@[bv_normalize]
def smtBeq (x y : EUnpackedFloat e s) : Bool :=
  x.isNaN && y.isNaN ||
  x.isInfinite && y.isInfinite && x.sign == y.sign ||
  !x.isNaN && !y.isNaN && !x.isInfinite && !y.isInfinite && UnpackedFloat.smtBeq x.num y.num

@[simp]
theorem smtBeq_refl (euf : EUnpackedFloat e s) : euf.smtBeq euf := by
  simp [EUnpackedFloat.smtBeq, UnpackedFloat.smtBeq]
  grind only

@[bv_normalize]
def smtBne (x y : EUnpackedFloat e s) : Bool :=
  !smtBeq x y

/-- `ieeeBeq` is IEEE `fp.eq`: NaN is never equal (even to itself), infinities
are equal iff same-signed, and finite values compare via `UnpackedFloat.ieeeBeq`
(numeric equality, so `+0 == -0`). Contrast `smtBeq` above (SMT core `=`). -/
@[bv_normalize]
def ieeeBeq (x y : EUnpackedFloat e s) : Bool :=
  !x.isNaN && !y.isNaN &&
  (x.isInfinite && y.isInfinite && x.sign == y.sign ||
   !x.isInfinite && !y.isInfinite && UnpackedFloat.ieeeBeq x.num y.num)

@[bv_normalize]
def bgeAux (xGEyOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bleAux (!xGEyOnDiffZeros) y x

@[bv_normalize]
def bgtAux (xGTyOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bltAux (!xGTyOnDiffZeros) y x

@[bv_normalize]
def minAux (xOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : EUnpackedFloat e s :=
  bif x.isNaN || bgtAux xOnDiffZeros x y then y else x

@[bv_normalize]
def maxAux (xOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : EUnpackedFloat e s :=
  bif x.isNaN || bltAux xOnDiffZeros x y then y else x

/-! ## SMT-LIB order comparisons on `EUnpackedFloat`

These mirror the `PackedFloat` wrappers (`smtBlt`/`smtBle`/`smtBge`/`smtBgt`) and
let the parser's ordered comparisons operate on the unpacked form so the inner
op-output `pack` can cancel. See the `PackedFloat` namespace for the NaN-handling
rationale (`whenBothNaN`). -/

@[bv_normalize]
def smtBlt (whenBothNaN : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bif x.isNaN && y.isNaN then whenBothNaN else bltAux false x y

@[bv_normalize]
def smtBle (whenBothNaN : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bif x.isNaN && y.isNaN then whenBothNaN else bleAux true x y

@[bv_normalize]
def smtBge (whenBothNaN : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bif x.isNaN && y.isNaN then whenBothNaN else bgeAux false x y

@[bv_normalize]
def smtBgt (whenBothNaN : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bif x.isNaN && y.isNaN then whenBothNaN else bgtAux true x y

end EUnpackedFloat

namespace PackedFloat

@[bv_normalize]
def bltAux (xLTyOnDiffZeros : Bool) (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.bltAux xLTyOnDiffZeros x.unpack y.unpack

@[bv_normalize]
def bleAux (xLEyOnDiffZeros : Bool) (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.bleAux xLEyOnDiffZeros x.unpack y.unpack

@[bv_normalize]
def smtBeq (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.smtBeq x.unpack y.unpack

@[bv_normalize]
def smtBne (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.smtBne x.unpack y.unpack

@[bv_normalize]
def ieeeBeq (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.ieeeBeq x.unpack y.unpack

@[bv_normalize]
def bgeAux (xGEyOnDiffZeros : Bool) (x y : PackedFloat e s) : Bool :=
  bleAux (!xGEyOnDiffZeros) y x

@[bv_normalize]
def bgtAux (xGTyOnDiffZeros : Bool) (x y : PackedFloat e s) : Bool :=
  bltAux (!xGTyOnDiffZeros) y x

@[bv_normalize]
def minAux (xOnDiffZeros : Bool) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.minAux xOnDiffZeros x.unpack y.unpack).pack

@[bv_normalize]
def maxAux (xOnDiffZeros : Bool) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.maxAux xOnDiffZeros x.unpack y.unpack).pack

-- The SMT-LIB order comparisons are *partial* relations only at NaN, which is
-- unordered: on `(NaN, NaN)` the result is the implementation's choice, exposed
-- as `whenBothNaN` (when exactly one side is NaN the result is the determined
-- `false`). Differing-signed zeros `(±0, ∓0)` are NOT ambiguous: `±0` and `∓0`
-- compare as numerically equal (`-0 ≤ +0` and `+0 ≤ -0`, `-0 < +0` false, etc.),
-- so the on-differing-zeros flag is hardcoded to that determined value:
--   * `lt`/`gt` → `false` (zeros are not strictly ordered);
--   * `le`/`ge` → `true`  (zeros are `≤`/`≥` each other).
-- `smtBgt`/`smtBge` pass the flag through `bgtAux`/`bgeAux`, which negate it, so
-- the hardcoded value there is the complement of the `lt`/`le` one.
-- The equivalence proofs (`Fp/Theorems/Comparison.lean`) are then guarded only
-- by non-NaN-ness of the inputs.
@[bv_normalize]
def smtBlt (whenBothNaN : Bool) (x y : PackedFloat e s) : Bool :=
  bif x.isNaN && y.isNaN then whenBothNaN else bltAux false x y

@[bv_normalize]
def smtBle (whenBothNaN : Bool) (x y : PackedFloat e s) : Bool :=
  bif x.isNaN && y.isNaN then whenBothNaN else bleAux true x y

@[bv_normalize]
def smtBge (whenBothNaN : Bool) (x y : PackedFloat e s) : Bool :=
  bif x.isNaN && y.isNaN then whenBothNaN else bgeAux false x y

@[bv_normalize]
def smtBgt (whenBothNaN : Bool) (x y : PackedFloat e s) : Bool :=
  bif x.isNaN && y.isNaN then whenBothNaN else bgtAux true x y

@[bv_normalize]
def smtMin (xOnDiffZeros : Bool) (x y : PackedFloat e s) : PackedFloat e s :=
  minAux xOnDiffZeros x y

@[bv_normalize]
def smtMax (xOnDiffZeros : Bool) (x y : PackedFloat e s) : PackedFloat e s :=
  maxAux xOnDiffZeros x y

def smtIsNeg (x : PackedFloat e s) : Bool :=
  !x.isNaN && x.sign

def smtIsPos (x : PackedFloat e s) : Bool :=
  !x.isNaN && !x.sign


@[simp]
theorem smtBeq_refl (pf : PackedFloat ep sp) : pf.smtBeq pf := by
  simp [PackedFloat.smtBeq]

end PackedFloat
