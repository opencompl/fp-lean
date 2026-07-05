import Fp.Convert
import Fp.Theorems.UnpackedFloat.Round.Widen
import Fp.Theorems.PackedFloat.Packing
import Fp.Theorems.PackUnpackRoundTrip

/-!
# `to_fp` (format conversion) is exact under widening

`PackedFloat.setWidths m e' s'` converts a float from format `(e, s)` to `(e', s')`,
rounding with mode `m` when precision is lost. This file proves the **promotion**
(widening) case is *exact*: when the target format is at least as wide in both the
exponent (`exponentWidth e s ≤ exponentWidth e' s'`) and the significand (`s ≤ s'`),
`setWidths` preserves the exact `ExtRat` value — no rounding occurs, matching the
SMT-LIB semantics (rounding an exactly-representable value is the identity).

The finite-number case reuses `Fp.toRat'_widen` (value preservation of
`UnpackedFloat.widen`), of which the `setWidths` promotion branch is definitionally
an instance; NaN/∞/±0 are preserved by their smart constructors.
-/

namespace EUnpackedFloat

/-- Off the exceptional states, `toExtRat` is the numeric value. -/
theorem toExtRat_eq_of_not_special {e s : Nat} (x : EUnpackedFloat e s)
    (hnan : x.isNaN = false) (hinf : x.isInfinite = false) :
    x.toExtRat = .Number x.num.toRat := by
  simp only [EUnpackedFloat.toExtRat, hnan, hinf, Bool.false_eq_true, cond_false]

theorem toExtRat_eq_NaN_of_isNaN {e s : Nat} (x : EUnpackedFloat e s) (hnan : x.isNaN = true) :
    x.toExtRat = .NaN := by
  simp only [EUnpackedFloat.toExtRat, hnan, cond_true]

theorem toExtRat_eq_Infinity_of_isInfinite {e s : Nat} (x : EUnpackedFloat e s)
    (hnan : x.isNaN = false) (hinf : x.isInfinite = true) :
    x.toExtRat = .Infinity x.num.sign := by
  simp only [EUnpackedFloat.toExtRat, hnan, hinf, Bool.false_eq_true, cond_false, cond_true]

/-- **`setWidths` is exact under widening** (`EUnpackedFloat` level, `sorry`-free).
Every classification is preserved and the finite value is carried unchanged. -/
theorem setWidths_toExtRat_of_le {e s e' s' : Nat} (m : RoundingMode)
    (heu : exponentWidth e s ≤ exponentWidth e' s') (hsu : s ≤ s')
    (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    (euf.setWidths m e' s').toExtRat = euf.toExtRat := by
  rw [EUnpackedFloat.setWidths]
  by_cases hnan : euf.isNaN = true
  · -- NaN → NaN
    simp only [hnan, cond_true, toExtRat_mkNan]
    rw [toExtRat_eq_NaN_of_isNaN euf hnan]
  · have hnanF : euf.isNaN = false := by simpa using hnan
    by_cases hinf : euf.isInfinite = true
    · -- ±∞ → ±∞
      simp only [hnanF, hinf, cond_true, cond_false, toExtRat_mkInfinity]
      rw [toExtRat_eq_Infinity_of_isInfinite euf hnanF hinf, EUnpackedFloat.sign]
    · have hinfF : euf.isInfinite = false := by simpa using hinf
      by_cases hzero : euf.isZero = true
      · -- ±0 → +0 (value `0`)
        simp only [hnanF, hinfF, hzero, cond_true, cond_false, toExtRat_mkZero]
        rw [toExtRat_eq_of_not_special euf hnanF hinfF]
        have hz : euf.num.isZero = true := by
          have h := hzero
          simp only [EUnpackedFloat.isZero, Bool.and_eq_true] at h
          exact h.2
        rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat'_eq_zero_of_isZero euf.num hz]
      · -- promotion branch: guard holds, output is `widen`, value preserved
        have hzeroF : euf.isZero = false := by simpa using hzero
        have hguard : ((exponentWidth e s).ble (exponentWidth e' s') && s.ble s') = true := by
          simp only [Bool.and_eq_true, Nat.ble_eq]
          exact ⟨heu, hsu⟩
        simp only [hnanF, hinfF, hzeroF, hguard, cond_true, cond_false]
        -- both sides are `Number (·.num.toRat)`: the update keeps `state`, so the record's
        -- classification is `euf`'s. Unfold `toExtRat` and discharge the exceptional branches.
        have hstn : (euf.state == State.NaN) = false := hnanF
        have hsti : (euf.state == State.Infinity) = false := hinfF
        simp only [EUnpackedFloat.toExtRat, EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite,
          hstn, hsti, cond_false]
        congr 1
        -- rewrite the promotion record to `widen`, then apply value preservation
        rw [show (⟨euf.num.sign, euf.num.ex.signExtend (exponentWidth e' s'),
              euf.num.sig.setWidth (s' + 1) <<< (s' - s)⟩ :
                UnpackedFloat (exponentWidth e' s') (s' + 1))
            = euf.num.widen (exponentWidth e' s') (s' + 1) from by
              rw [UnpackedFloat.widen, show (s' + 1) - (s + 1) = s' - s from by omega]]
        rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat_eq_toRat',
          Fp.toRat'_widen euf.num (exponentWidth e' s') (s' + 1) heu (by omega) (by omega)]

end EUnpackedFloat


namespace PackedFloat

/-- **`to_fp`/`setWidths` is exact under widening** (`PackedFloat` level).
For a genuine format widening — `1 < e`, `0 < s`, `1 < e'`, `0 < s'`, `e ≤ e'`, `s ≤ s'` — the
converted float carries exactly the same extended-rational value:
`(pf.setWidths m e' s').toExtRat = pf.toExtRat`.

The widening hypotheses `e ≤ e'`, `s ≤ s'` are essential and cannot be weakened to the
`setWidths` guard `exponentWidth e s ≤ exponentWidth e' s'`: the latter permits `e > e'`, where a
large-magnitude source value overflows the target's `maxNormalExp` and packs to ∞. -/
theorem setWidths_toExtRat_of_le {e s e' s' : Nat} (m : RoundingMode)
    (he : 1 < e) (hs : 0 < s) (he' : 1 < e') (hs' : 0 < s')
    (hee : e ≤ e') (hss : s ≤ s')
    (pf : PackedFloat e s) :
    (pf.setWidths m e' s').toExtRat = pf.toExtRat := by
  rw [PackedFloat.setWidths]
  -- `res.pack.toExtRat = res.toExtRat` via the pack/unpack round-trip of the *proven-Canonical*
  -- result (no `Canonical_all`).
  have hcanon : EUnpackedFloat.Canonical (pf.unpack.setWidths m e' s') :=
    EUnpackedFloat.Canonical_setWidths m he hs he' hs' hee hss pf.unpack
      (EUnpackedFloat.Canonical_unpack he hs pf)
  have hpack : (pf.unpack.setWidths m e' s').pack.toExtRat
      = (pf.unpack.setWidths m e' s').toExtRat := by
    have h2 : (pf.unpack.setWidths m e' s').pack.unpack = pf.unpack.setWidths m e' s' :=
      EUnpackedFloat.pack_unpack_of_Canonical he' hs' _ hcanon
    calc (pf.unpack.setWidths m e' s').pack.toExtRat
        = (pf.unpack.setWidths m e' s').pack.unpack.toExtRat :=
          PackedFloat.toExtRat_unpack_eq_toExtRat.symm
      _ = (pf.unpack.setWidths m e' s').toExtRat := by rw [h2]
  rw [hpack, EUnpackedFloat.setWidths_toExtRat_of_le m (exponentWidth_le_of_le hee hss) hss
      pf.unpack, PackedFloat.toExtRat_unpack_eq_toExtRat]

end PackedFloat

-- The `EUnpackedFloat`-level widening exactness is `sorry`-free (standard axioms only).
/--
info: 'EUnpackedFloat.setWidths_toExtRat_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms EUnpackedFloat.setWidths_toExtRat_of_le

-- The `PackedFloat` corollary is likewise `sorry`-free and axiom-clean: it round-trips through
-- the *proven* `Canonical_setWidths` (no `Canonical_all`).
/--
info: 'PackedFloat.setWidths_toExtRat_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PackedFloat.setWidths_toExtRat_of_le
