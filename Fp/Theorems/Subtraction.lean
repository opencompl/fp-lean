import Fp.Theorems.Addition
import Fp.SmtLibPackedFloat
import Fp.Subtraction
import Fp.Theorems.PackedFloat.Negation

/-!
# Correctness of `PackedFloat.sub` against the SMT-LIB semantics

The goal of this file is `Fp.sub_eq_sub`, the analogue of `Fp.add_eq_add`:
the bit-blasted subtraction circuit agrees (up to NaN bit patterns) with the
SMT-LIB semantics `SmtLibFunctions.sub`, which subtracts the *exact* rational
values and rounds the result, for RNE.

The proof reduces subtraction to addition against a negated operand, on both
the circuit and the spec side:

  `spec-sub  ≈  spec-add(a, -b)  ≈  circuit-add(a, -b)  =  circuit-sub`.

* The circuit identity `circuit-sub a b = circuit-add a (-b)` is a strict
  equality (`hcirc`), proven via `PackedFloat.unpack_neg_of_not_isNaN`.
* The spec identity `spec-sub a b ≈ spec-add a (-b)` (`hspec`) is a strict
  equality away from NaN, using that `ExtRat` subtraction is addition of the
  negation and that `SmtLibFunctions.neg` agrees with `-·` off NaN.
* The middle `≈` is `Fp.add_eq_add`.
-/

namespace PackedFloat

/-- `PackedFloat.sub` collapses to the canonical NaN whenever its right
argument is a NaN, mirroring `add_eq_getNaN_of_right_isNaN`. -/
theorem sub_eq_getNaN_of_right_isNaN (m : RoundingMode) (x y : PackedFloat e s)
    (hy : y.isNaN) : PackedFloat.sub m x y = PackedFloat.getNaN e s := by
  simp [PackedFloat.sub, EUnpackedFloat.sub, PackedFloat.unpack_eq_NaN_of_isNaN y hy,
    EUnpackedFloat.add, EUnpackedFloat.neg, EUnpackedFloat.mkNaN, EUnpackedFloat.isNaN]

/-- Negation commutes with `unpackNum`: `(-b).unpackNum = (b.unpackNum).neg`.
Negation only flips the sign field of a `PackedFloat`, which is exactly the
field `unpackNum` copies into (or, in the subnormal case, threads through
`normalize`). -/
theorem unpackNum_neg (b : PackedFloat e s) :
    (-b).unpackNum = (b.unpackNum).neg := by
  simp only [unpackNum, isNorm_neg, PackedFloat.neg_sign, PackedFloat.neg_ex, PackedFloat.neg_sig]
  by_cases h : b.isNorm
  · simp [h, UnpackedFloat.neg]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    by_cases hz : b.sig.cons false = 0#(s + 1)
    · simp [UnpackedFloat.normalize, hz, UnpackedFloat.mkZero, UnpackedFloat.neg]
    · have hzb : (BitVec.cons false b.sig == 0#(s + 1)) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hz
      simp [UnpackedFloat.normalize, hzb, UnpackedFloat.neg]

/-- Away from NaN, unpacking commutes with negation: `(-b).unpack = (b.unpack).neg`.
On the NaN branch the two sides differ (packed negation flips the NaN's sign bit
while `unpack` discards it), which is why the hypothesis `¬ b.isNaN` is needed. -/
theorem unpack_neg_of_not_isNaN {e s} (hs : 0 < s) (he : 0 < e) {b : PackedFloat e s}
    (hb : ¬ b.isNaN) : (-b).unpack = (b.unpack).neg := by
  by_cases hinf : b.isInfinite
  · have hlhs : (-b).unpack = EUnpackedFloat.mkInfinity (!b.sign) := by
      simp [PackedFloat.unpack, isNaN_neg, isInfinite_neg, hb, hinf, PackedFloat.neg_sign]
    have hrhs : b.unpack = EUnpackedFloat.mkInfinity b.sign := by
      simp [PackedFloat.unpack, hb, hinf]
    rw [hlhs, hrhs]; rfl
  · by_cases hz : b.isZero
    · have hlhs : (-b).unpack = EUnpackedFloat.mkZero (!b.sign) := by
        simp [PackedFloat.unpack, isNaN_neg, isInfinite_neg, isZero_neg, hb, hinf, hz,
          PackedFloat.neg_sign]
      have hrhs : b.unpack = EUnpackedFloat.mkZero b.sign := by
        simp [PackedFloat.unpack, hb, hinf, hz]
      rw [hlhs, hrhs]; rfl
    · have hlhs : (-b).unpack = EUnpackedFloat.mkNumber ((-b).unpackNum) := by
        simp [PackedFloat.unpack, isNaN_neg, isInfinite_neg, isZero_neg, hb, hinf, hz]
      have hrhs : b.unpack = EUnpackedFloat.mkNumber (b.unpackNum) := by
        simp [PackedFloat.unpack, hb, hinf, hz]
      rw [hlhs, hrhs, PackedFloat.unpackNum_neg]
      rfl

end PackedFloat

namespace Fp

set_option maxHeartbeats 1000000 in
theorem sub_eq_sub {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 1 < ein)
    (rm : RoundingMode) (a b : PackedFloat ein sin) :
    (Fp.SmtLibSemantics.SmtLibFunctions.sub (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b).EquivUptoNaN
      (PackedFloat.sub rm a b) := by
  have he0 : 0 < ein := by grind
  -- Step A: the circuit identity, a strict equality.
  have hcirc : PackedFloat.sub rm a b = PackedFloat.add rm a (-b) := by
    by_cases hb : b.isNaN
    · rw [PackedFloat.sub_eq_getNaN_of_right_isNaN rm a b hb,
        PackedFloat.add_eq_getNaN_of_right_isNaN rm a (-b) (by simpa using hb)]
    · rw [PackedFloat.sub, EUnpackedFloat.sub, PackedFloat.add,
        PackedFloat.unpack_neg_of_not_isNaN hsin he0 hb]
  -- Step B: the spec identity, an `EquivUptoNaN`.
  have hspec : (Fp.SmtLibSemantics.SmtLibFunctions.sub
      (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b).EquivUptoNaN
      (Fp.SmtLibSemantics.SmtLibFunctions.add
        (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a (-b)) := by
    by_cases hb : b.isNaN
    · -- Both sides round `ExtRat.NaN`, hence are NaN.
      apply PackedFloat.EquivUptoNaN.of_isNaN_isNaN
      · simp only [SmtLibSemantics.SmtLibFunctions.sub, SmtLibSemantics.smtLibRoundMethod.embed_eq,
          SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq,
          PackedFloat.toExtRat_eq_toExtRat', roundQ_eq]
        rw [b.toExtRat'_eq_NaN_of_isNaN hb,
          show a.toExtRat' - ExtRat.NaN = ExtRat.NaN by rw [← ExtRat.sub_def]; simp [ExtRat.sub]]
        exact isNaN_round_of_nan
      · simp only [SmtLibSemantics.SmtLibFunctions.add, SmtLibSemantics.smtLibRoundMethod.embed_eq,
          SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq,
          PackedFloat.toExtRat_eq_toExtRat', roundQ_eq]
        rw [PackedFloat.toExtRat'_neg, b.toExtRat'_eq_NaN_of_isNaN hb, ExtRat.ExtRat.neg_NaN,
          ExtRat.ExtRat.add_NaN]
        exact isNaN_round_of_nan
    · -- Off NaN: a strict equality.
      apply PackedFloat.EquivUptoNaN.of_eq
      simp only [SmtLibSemantics.SmtLibFunctions.sub, SmtLibSemantics.SmtLibFunctions.add,
        SmtLibSemantics.SmtLibFunctions.subSign, SmtLibSemantics.smtLibRoundMethod.embed_eq,
        SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq,
        PackedFloat.toExtRat_eq_toExtRat', roundQ_eq]
      have hnegb : Fp.SmtLibSemantics.SmtLibFunctions.neg b = -b := by
        simp [SmtLibSemantics.SmtLibFunctions.neg, hb, PackedFloat.neg_def, PackedFloat.neg]
      rw [hnegb, PackedFloat.toExtRat'_neg]
      rfl
  -- Step C: assemble.
  rw [hcirc]
  exact hspec.trans (Fp.add_eq_add hsin he hep rm a (-b))

/--
info: 'Fp.sub_eq_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sub_eq_sub

end Fp
