import Fp.Basic
import Fp.Unpacking
import Fp.Theorems.Packing

namespace EUnpackedFloat

/-- Packing a NaN gives a NaN PackedFloat. -/
@[simp]
theorem isNaN_pack_of_isNaN
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isNaN) :
    uf.pack.isNaN = true := by
  simp [pack, PackedFloat.isNaN, huf]
  grind

/--
Packing an infinity gives an infinite PackedFloat. Requires `0 < s` because with no sig bits,
the PackedFloat infinity encoding aliases NaN.
-/
@[simp]
theorem isInfinite_pack_of_isInfinite
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isInfinite) (hs : 0 < s) :
    uf.pack.isInfinite = true := by
  have hnan : uf.isNaN = false := by
    simp [isNaN, isInfinite] at huf ⊢
    grind
  simp [pack, PackedFloat.isInfinite, huf, hnan]
  grind

/-- Packing always preserves the sign. -/
@[simp]
theorem sign_pack
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    uf.pack.sign = uf.sign := by
  simp [pack, EUnpackedFloat.sign]

/--
Packing then unpacking an infinity recovers `mkInfinity` with the same sign.
Corollary of `isInfinite_pack_of_isInfinite` + `sign_pack`: once we know `uf.pack` is infinite
and not NaN, `PackedFloat.unpack` normalizes it to `mkInfinity uf.pack.sign = mkInfinity uf.sign`.
-/
theorem unpack_pack_of_isInfinite
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isInfinite) (hs : 0 < s) :
    uf.pack.unpack = EUnpackedFloat.mkInfinity uf.sign := by
  have hInf : uf.pack.isInfinite = true := isInfinite_pack_of_isInfinite uf huf hs
  have hNaN : uf.pack.isNaN = false := by
    have := PackedFloat.not_isNaN_of_isInfinite (pf := uf.pack) hInf
    grind
  simp [PackedFloat.unpack, hNaN, hInf]

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
