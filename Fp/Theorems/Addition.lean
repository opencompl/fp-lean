import Fp.Comparison
import Fp.Negation
import Fp.UnpackedRound
import Fp.Addition
import Mathlib.Tactic

theorem add_zero_is_id (a : PackedFloat 5 2)
  (ha : ¬a.isNaN)
  :  a + (PackedFloat.getZero _ _ true) = a := by
  bv_decide

theorem isSome_not_nan {a : PackedFloat e s} (h : a.toRat?.isSome) : ¬a.isNaN := by
  intro hnan
  have hnone : a.toRat? = none := by
    have : a.ex = BitVec.allOnes e ∧ (s = 0 ∨ ¬a.sig = 0#s) := by
      simpa [PackedFloat.isNaN] using hnan
    simp [PackedFloat.toRat?, PackedFloat.toEFixed, PackedFloat.isNaN, this, EFixedPoint.toRat?,
      EFixedPoint.toDyadic?]
    grind
  simp [hnone] at h

theorem infin_not_num {e s : Nat} (sign : Bool) :
    (EUnpackedFloat.mkInfinity (e := exponentWidth e s) (s := s + 1) sign).pack.toEFixed.state ≠ .Number := by
  by_cases hs : s = 0
  · simp [hs, PackedFloat.toEFixed, EUnpackedFloat.pack, EUnpackedFloat.mkInfinity,
      EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite]
  · have hsig : (bif State.Infinity == State.NaN then BitVec.intMin s else (0#s)) = (0#s) := by
      rfl
    simp [hs, hsig, PackedFloat.toEFixed, EUnpackedFloat.pack, EUnpackedFloat.mkInfinity,
      EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite]

theorem nan_not_num {e s : Nat} :
    (EUnpackedFloat.mkNaN (e := exponentWidth e s) (s := s + 1)).pack.toEFixed.state ≠ .Number := by
  by_cases hs : s = 0
  · simp [hs, PackedFloat.toEFixed, EUnpackedFloat.pack, EUnpackedFloat.mkNaN,
      EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite]
  · simp [hs, PackedFloat.toEFixed, EUnpackedFloat.pack, EUnpackedFloat.mkNaN,
      EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite]

theorem nan_state_is_nan {a : PackedFloat e s} (h : a.toEFixed.state == .NaN) : a.unpack.isNaN := by
  simp_all [PackedFloat.unpack, EUnpackedFloat.isNaN, PackedFloat.toEFixed]
  have : a.ex = BitVec.allOnes e ∧ (s = 0 ∨ ¬a.sig = 0#s) := by grind
  simp [this]
  have : s == 0 || a.sig != 0#s := by grind
  simp [this, EUnpackedFloat.mkNaN]

theorem infin_state_is_infin {a : PackedFloat e s} (h : a.toEFixed.state == .Infinity) : a.unpack.isInfinite ∨ a.unpack.isNaN := by
  simp_all [PackedFloat.unpack, EUnpackedFloat.isInfinite, PackedFloat.toEFixed]
  have : a.ex = BitVec.allOnes e ∧ ¬s = 0 ∧ a.sig = 0#s := by grind
  simp [this]
  by_cases sz : s = 0 <;> try simp [sz]
  ·   grind
  ·   have : (s == 0) = false := by grind
      simp [this]
      have : (s != 0) = true := by simp_all
      simp [this]
      left
      bv_decide

theorem pack_is_nan : EUnpackedFloat.mkNaN.pack.isNaN (e := e) (s := s) := by
  by_cases hs : s = 0
  · simp [hs, EUnpackedFloat.pack, EUnpackedFloat.mkNaN, EUnpackedFloat.isNaN,
      EUnpackedFloat.isInfinite, PackedFloat.isNaN]
  · simp [hs, EUnpackedFloat.pack, EUnpackedFloat.mkNaN, EUnpackedFloat.isNaN,
      EUnpackedFloat.isInfinite, PackedFloat.isNaN]

theorem one_of_state (h₁ : s ≠ State.Number) (h₂ : s ≠ State.NaN) (h₃ : s ≠ State.Infinity) : False := by
  grind

theorem left_not_number (a : PackedFloat e s) (h : a.toRat?.isNone) : (a + b).toRat?.isNone := by
  rw [PackedFloat.PackedFloat.add_def]
  by_cases h₁ : a.toEFixed.state == .NaN
  ·   simp [PackedFloat.add, EUnpackedFloat.add]
      have : a.unpack.isNaN := nan_state_is_nan h₁
      simp_all [PackedFloat.toRat?, EFixedPoint.toRat?, EFixedPoint.toDyadic?]
      rw [PackedFloat.toEFixed]
      have : EUnpackedFloat.mkNaN.pack.isNaN (e := e) (s := s) := pack_is_nan
      rw [this]
      simp
      grind
  ·   by_cases h₂ : a.toEFixed.state == .Infinity
      ·   simp [PackedFloat.add, EUnpackedFloat.add]
          have : a.unpack.isInfinite ∨ a.unpack.isNaN := infin_state_is_infin h₂
          simp_all [PackedFloat.toRat?, EFixedPoint.toRat?, EFixedPoint.toDyadic?]
          grind [infin_not_num, nan_not_num]
      ·   false_or_by_contra
          simp_all [PackedFloat.toRat?, EFixedPoint.toRat?, EFixedPoint.toDyadic?]
          apply one_of_state (s := a.toEFixed.state) <;> simp_all
          grind


theorem right_not_number (b : PackedFloat e s) (h : b.toRat?.isNone) : (a + b).toRat?.isNone := by
  rw [PackedFloat.PackedFloat.add_def]
  by_cases h₁ : b.toEFixed.state == .NaN
  ·   simp [PackedFloat.add, EUnpackedFloat.add]
      have : b.unpack.isNaN := nan_state_is_nan h₁
      simp_all [PackedFloat.toRat?, EFixedPoint.toRat?, EFixedPoint.toDyadic?]
      rw [PackedFloat.toEFixed]
      have : EUnpackedFloat.mkNaN.pack.isNaN (e := e) (s := s) := pack_is_nan
      rw [this]
      simp
      grind
  ·   by_cases h₂ : b.toEFixed.state == .Infinity
      ·   simp [PackedFloat.add, EUnpackedFloat.add]
          have : b.unpack.isInfinite ∨ b.unpack.isNaN := infin_state_is_infin h₂
          simp_all [PackedFloat.toRat?, EFixedPoint.toRat?, EFixedPoint.toDyadic?]
          grind [infin_not_num, nan_not_num]
      ·   false_or_by_contra
          simp_all [PackedFloat.toRat?, EFixedPoint.toRat?, EFixedPoint.toDyadic?]
          apply one_of_state (s := b.toEFixed.state) <;> simp_all
          grind


theorem add_result_norm_args_norm {a b : PackedFloat e s} :
    (a + b).toRat? = some c → (a.toRat?.isSome) ∧ b.toRat?.isSome := by
  intro hsum
  constructor
  · by_contra hA
    have hA_none : a.toRat?.isNone := by
      cases hopt : a.toRat? <;> simp [hopt] at hA ⊢
    have : (a + b).toRat?.isNone := left_not_number a hA_none
    simp [hsum] at this
  · by_contra hB
    have hB_none : b.toRat?.isNone := by
      cases hopt : b.toRat? <;> simp [hopt] at hB ⊢
    have : (a + b).toRat?.isNone := right_not_number b hB_none
    simp [hsum] at this
