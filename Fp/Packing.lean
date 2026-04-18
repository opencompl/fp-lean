import Fp.Basic
import Fp.Unpacking
import Fp.Theorems.Packing

namespace EUnpackedFloat

/-- Packing a NaN gives a NaN PackedFloat. -/
@[simp]
theorem isNaN_pack_of_isNaN
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isNaN) :
    uf.pack.isNaN = true := by sorry

/--
Packing an infinity gives an infinite PackedFloat. Requires `0 < s` because with no sig bits,
the PackedFloat infinity encoding aliases NaN.
-/
@[simp]
theorem isInfinite_pack_of_isInfinite
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isInfinite) (hs : 0 < s) :
    uf.pack.isInfinite = true := by sorry

/-- Packing an infinity preserves the sign. -/
@[simp]
theorem sign_pack_of_isInfinite
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isInfinite) :
    uf.pack.sign = uf.sign := by sorry

/--
The round-trip: packing a *normalized* EUnpackedFloat and then unpacking returns the same value.
Normalization is in the sense of `EUnpackedFloat.normalize` (Fp/Basic.lean): for a Number, this means
the significand is either zero or has its MSB set; for NaN/Infinity states the condition is trivial.

The side conditions `0 < e`, `0 < s` rule out degenerate packed formats where infinity/zero
aliases NaN (see `PackedFloat.unpack_getInfinity`, `PackedFloat.unpack_getZero`).
-/
theorem unpack_pack_of_normalize_eq
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.normalize = uf) (he : 0 < e) (hs : 0 < s) :
    uf.pack.unpack = uf := by sorry

/-- Corollary: packing preserves `toExtRat` on normalized inputs. -/
theorem toExtRat_pack_of_normalize_eq
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.normalize = uf) (he : 0 < e) (hs : 0 < s) :
    uf.pack.toExtRat = uf.toExtRat := by
  rw [← PackedFloat.toExtRat_unpack_eq_toExtRat, unpack_pack_of_normalize_eq uf huf he hs]

end EUnpackedFloat
