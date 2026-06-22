import Fp.Basic

/--
The conditions under which an `UnpackedFloat` of the unpacked width for target format `(e, s)`
packs losslessly into a `PackedFloat e s`:
* it is normalized (`normalize` is the identity),
* its exponent does not exceed `maxNormalExp e` (no overflow to infinity), and
* it is exactly representable: either it sits in the normal range, or (in the subnormal range)
  the significand is divisible by the shift used to express it at `minNormalExp e`, so no bits
  are lost.

These are exactly the side conditions of `toRat_pack_mkNumber_eq_toRat`.
-/
def UnpackedFloat.Packable {e s : Nat} (uf : UnpackedFloat (exponentWidth e s) (s + 1)) : Prop :=
  uf.normalize = uf ∧
  uf.ex.toInt ≤ maxNormalExp e ∧
  (minNormalExp e ≤ uf.ex.toInt ∨
    2 ^ (minNormalExp e - uf.ex.toInt).toNat ∣ uf.sig.toNat)
