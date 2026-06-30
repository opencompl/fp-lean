import Fp.UnpackedFloat.Basic

/-!
## UnpackedFloat negation/zero/normalize lemmas

Lemmas about neg/abs, mkZero, isZero and normalize.
-/

namespace UnpackedFloat


@[bv_normalize]
theorem neg_def {x : UnpackedFloat e s} : -x = UnpackedFloat.neg x := rfl

@[simp]
theorem neg_neg (x : UnpackedFloat e s) : -(-x) = x := by
  simp [neg_def, neg]

@[simp, bv_normalize]
theorem neg_sign (x : UnpackedFloat e s) : (-x).sign = !x.sign := rfl

@[simp, bv_normalize]
theorem neg_ex (x : UnpackedFloat e s) : (-x).ex = x.ex := rfl

@[simp, bv_normalize]
theorem neg_sig (x : UnpackedFloat e s) : (-x).sig = x.sig := rfl


@[bv_normalize]
theorem eq_cond_sign {x y : UnpackedFloat e s} :
  (bif b then x else y).sign = bif b then x.sign else y.sign := by
  cases b <;> rfl

@[bv_normalize]
theorem eq_cond_ex {x y : UnpackedFloat e s} :
  (bif b then x else y).ex = bif b then x.ex else y.ex := by
  cases b <;> rfl

@[bv_normalize]
theorem eq_cond_sig {x y : UnpackedFloat e s} :
  (bif b then x else y).sig = bif b then x.sig else y.sig := by
  cases b <;> rfl

@[simp]
theorem ex_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).ex = BitVec.intMin e := rfl

@[simp]
theorem sig_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).sig = 0#s := rfl


@[simp]
theorem sign_normalize (uf : UnpackedFloat e s) : (normalize uf zsign).sign =
  if uf.sig == 0#s then zsign else uf.sign := by
  grind [normalize, mkZero]

@[simp]
theorem sig_normalize (uf : UnpackedFloat e s) : (normalize uf zsign).sig =
  if uf.sig == 0#s then 0#s else uf.sig <<< uf.sig.clz := by
  grind [normalize, mkZero]

@[simp]
theorem exp_normalize (uf : UnpackedFloat e s) : (normalize uf zsign).ex =
  if uf.sig == 0#s then BitVec.intMin e else uf.ex - uf.sig.clz.setWidth _ := by
  grind [normalize, mkZero]

/--
Normalize gives a number whose most significant bit is one,
iff the number is nonzero.
-/
@[simp]
theorem msb_normalize_eq_decide (uf : UnpackedFloat e s) :
    ((normalize uf zsign).sig.msb = decide (uf.sig ≠ 0)) := by
  simp
  by_cases hs : uf.sig = 0#s <;> simp [hs]

/-- When the number is nonzero,
the normalization is idempotent iff  and its most significant bit is one.
-/
theorem normalize_eq_self_iff (uf : UnpackedFloat e s) (huf : uf.sig ≠ 0#s) :
    normalize uf zsign = uf ↔ (uf.sig.msb = true) := by
  simp [normalize]
  by_cases hs : uf.sig == 0#s
  · simp [hs]
    grind only
  · simp only [hs, cond_false]
    rcases uf with ⟨sign, ex, sig⟩
    simp only [mk.injEq, true_and]
    constructor
    · intros h
      simp only [ne_eq, beq_iff_eq] at huf hs
      obtain ⟨hex, hsig⟩ := h
      have := BitVec.shiftLeft_eq_self_iff_eq_zero.mp hsig
      rcases this with this | this
      · have := BitVec.clz_eq_zero_iff_msb_of_lt sig |>.mp (by grind)
        simp [show s ≠ 0 by grind] at this
        exact this
      · grind only
    · intros hmsb
      have : sig.clz = 0#s := by grind [BitVec.clz_eq_zero_iff_msb_of_lt]
      rw [this]
      simp only [BitVec.setWidth_zero, BitVec.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod,
        BitVec.shiftLeft_zero, and_self]


/--
Normalize is idempotent when the most significant bit is one,
as such a number is already normalized.
-/
theorem normalize_eq_self_of_msb_eq_true (uf : UnpackedFloat e s)
    (hmsb : uf.sig.msb = true) :
    normalize uf zsign = uf := by
  rw [normalize_eq_self_iff]
  · simp [hmsb]
  · grind only [= BitVec.msb_eq_getMsbD_zero, = BitVec.getMsbD_zero]

/--
info: 'UnpackedFloat.normalize_eq_self_of_msb_eq_true' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms normalize_eq_self_of_msb_eq_true
end UnpackedFloat
