import Fp.Theorems.PackedFloat.Packing
import Fp.Theorems.UnpackedFloat.Round.RNE
import Fp.Theorems.Addition
import Fp.Theorems.Multiplication
import Fp.Theorems.Division
import Fp.Subtraction

/-!
# `pack`/`unpack` round-trip on canonical / `Packable` `EUnpackedFloat`s

This module proves the "forward" round-trip `euf.pack.unpack = euf` for the values that
actually flow through the staged normalization pipeline in `Fp/PackUnpackNormalize.lean`:
the smart constructors (`mkNaN`/`mkInfinity`/`mkZero`) and `Packable` `mkNumber`s, and
therefore the outputs of `EUnpackedFloat.blastSmtLibRound` (RNE) and of the arithmetic ops.

It is the mirror of `PackedFloat.unpack_pack_eq_self_of_isNormOrNonzeroSubnorm`
(`Fp/Theorems/PackedFloat/Packing.lean`), which handles the *reverse* composition.
-/

namespace EUnpackedFloat

variable {e s : Nat}

/-- `mkNaN` round-trips through `pack`/`unpack`. -/
@[simp]
theorem unpack_pack_of_mkNaN :
    (EUnpackedFloat.mkNaN : EUnpackedFloat (exponentWidth e s) (s + 1)).pack.unpack
      = EUnpackedFloat.mkNaN := by
  rw [EUnpackedFloat.mkNaN_pack_eq_mkNaN]
  exact PackedFloat.unpack_eq_NaN_of_isNaN _ PackedFloat.isNaN_getNaN

/-- `mkInfinity` round-trips (given a nonzero significand width). -/
@[simp]
theorem unpack_pack_of_mkInfinity (hs : 0 < s) (sign : Bool) :
    (EUnpackedFloat.mkInfinity sign : EUnpackedFloat (exponentWidth e s) (s + 1)).pack.unpack
      = EUnpackedFloat.mkInfinity sign := by
  rw [EUnpackedFloat.mkInfinity_pack_eq_getInfinity, PackedFloat.unpack_getInfinity]
  simp [hs]

/-- `mkZero` round-trips (given a nonzero exponent width). -/
@[simp]
theorem unpack_pack_of_mkZero (he : 0 < e) (sign : Bool) :
    (EUnpackedFloat.mkZero sign : EUnpackedFloat (exponentWidth e s) (s + 1)).pack.unpack
      = EUnpackedFloat.mkZero sign := by
  rw [EUnpackedFloat.mkZero_pack_eq_getZero, PackedFloat.unpack_getZero]
  simp [he]

/-- The main new round-trip: a `Packable` `mkNumber` recovers itself.
Mirror of `PackedFloat.unpack_pack_eq_self_of_isNormOrNonzeroSubnorm`. -/
theorem unpack_pack_of_Packable_Number (he : 1 < e) (hs : 0 < s)
    (uf : UnpackedFloat (exponentWidth e s) (s + 1)) (hpack : uf.Packable) :
    (EUnpackedFloat.mkNumber uf).pack.unpack = EUnpackedFloat.mkNumber uf := by
  obtain ⟨hnorm, hexp1, hexp2⟩ := hpack
  by_cases hzero : uf.sig = 0#(s + 1)
  · -- Zero payload: pack lands `getZero`, and a normalized zero is `mkZero uf.sign`.
    have hufz : uf = UnpackedFloat.mkZero uf.sign :=
      hnorm.symm.trans (by simp [UnpackedFloat.normalize, hzero])
    have hisZero : (EUnpackedFloat.mkNumber uf).isZero := by
      simp [EUnpackedFloat.isZero, EUnpackedFloat.isNumber, EUnpackedFloat.mkNumber,
        UnpackedFloat.isZero, hzero]
    rw [EUnpackedFloat.pack_eq_pack', pack'_eq_getZero_of_isZero _ hisZero,
      PackedFloat.unpack_getZero, if_pos (show 0 < e by omega)]
    -- goal: `mkZero (mkNumber uf).sign = mkNumber uf`; both nums are `UnpackedFloat.mkZero uf.sign`.
    apply EUnpackedFloat.ext
    · rfl
    · simpa [EUnpackedFloat.mkZero, EUnpackedFloat.mkNumber, EUnpackedFloat.sign] using hufz.symm
  · -- Nonzero payload: `pack` lands a normal/nonzero-subnormal float; recover by value.
    have hmsb : uf.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff uf hzero).mp hnorm
    obtain ⟨pf, hpf_def⟩ : ∃ pf, pf = (EUnpackedFloat.mkNumber uf).pack := ⟨_, rfl⟩
    rw [← hpf_def]
    -- `pf.toRat = uf.toRat`
    have htoRat : pf.toRat = uf.toRat := by
      rw [hpf_def]; exact EUnpackedFloat.toRat_pack_mkNumber_eq_toRat he hs uf ⟨hnorm, hexp1, hexp2⟩
    -- `pf` is normal / nonzero subnormal (mirror of Packing.lean:1046-1064).
    have hpacked : pf = EUnpackedFloat.packNumber' uf.sign uf.sig uf.ex := by
      rw [hpf_def, EUnpackedFloat.pack_eq_pack', EUnpackedFloat.pack']
      have hz : (EUnpackedFloat.mkNumber uf).isZero = false := by
        rw [EUnpackedFloat.isZero_mkNumber]
        simp [UnpackedFloat.isZero, hzero]
      simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber, hz,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    have hnotNaN : ¬ pf.isNaN := by
      rw [hpacked, EUnpackedFloat.not_isNaN_packNumber' hs he _ _ _ hexp1]
      simp
    have hnotInf : ¬ pf.isInfinite := by
      rw [hpacked]
      have hne := EUnpackedFloat.packNumber'.exPacked_ne_allOnes hs he uf.ex hexp1
      simp only [PackedFloat.isInfinite, EUnpackedFloat.packNumber']
      grind
    have hnotZero : ¬ pf.isZero := by
      intro hzc
      have h0 := PackedFloat.toRat_eq_Zero_of_isZero _ hzc
      rw [htoRat, UnpackedFloat.toRat_eq_toRat'] at h0
      have hnz : ¬ uf.isZero := by simp [UnpackedFloat.isZero, hzero]
      exact (UnpackedFloat.toRat'_ne_zero_iff_not_isZero uf).mp hnz h0
    have hresnorm : pf.isNormOrNonzeroSubnorm :=
      PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero hnotNaN hnotInf hnotZero
    -- `pf.unpack = mkNumber pf.unpackNum`, and `pf.unpackNum = uf` by value injectivity.
    rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hresnorm]
    have hpackNum : pf.unpackNum.Packable := PackedFloat.unpackNum_packable he hs pf hresnorm
    have hnumMsb : pf.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true hresnorm
    have hnumToRat : pf.unpackNum.toRat = pf.toRat := pf.unpackNum_toRat_eq_toRat hresnorm
    have : pf.unpackNum = uf :=
      Fp.UnpackedFloat.eq_of_toRat_eq_toRat_of_msb pf.unpackNum uf hnumMsb hmsb
        (by rw [hnumToRat, htoRat])
    rw [this]

/-- **Master round-trip.** A `Packable` value whose non-`Number` states are the canonical
smart constructors round-trips through `pack`/`unpack`. The two canonicity hypotheses are
vacuous for `Number` states and are discharged by inspection for the smart constructors and
for `blastSmtLibRound` outputs. -/
theorem pack_unpack_of_Packable (he : 1 < e) (hs : 0 < s)
    (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) (hpack : euf.Packable)
    (hNaN : euf.isNaN = true → euf = EUnpackedFloat.mkNaN)
    (hInf : euf.isInfinite = true → euf = EUnpackedFloat.mkInfinity euf.sign) :
    euf.pack.unpack = euf := by
  match hst : euf.state with
  | .NaN =>
    have : euf = EUnpackedFloat.mkNaN := hNaN (by simp [EUnpackedFloat.isNaN, hst])
    rw [this]; exact unpack_pack_of_mkNaN
  | .Infinity =>
    have : euf = EUnpackedFloat.mkInfinity euf.sign := hInf (by simp [EUnpackedFloat.isInfinite, hst])
    rw [this]; exact unpack_pack_of_mkInfinity hs euf.sign
  | .Number =>
    have hnum : euf.num.Packable := hpack (by simp [hst])
    have : euf = EUnpackedFloat.mkNumber euf.num := by
      apply EUnpackedFloat.ext <;> simp [EUnpackedFloat.mkNumber, hst]
    rw [this]; exact unpack_pack_of_Packable_Number he hs euf.num hnum

/-! ## Canonical special states

`CanonState euf` says the non-`Number` states of `euf` are the canonical smart constructors.
It is closed under the constructors, `cond`/`ite`, sign-negation (of non-`NaN` values), and
`normalize`, and it is what upgrades `blastSmtLibRound`'s `Packable` output to a round-trip
fixpoint via `pack_unpack_of_Packable`. -/

/-- The non-`Number` states of `euf` are canonical (`mkInfinity`/`mkNaN`). -/
def CanonState (euf : EUnpackedFloat e s) : Prop :=
  (euf.isInfinite = true → euf = EUnpackedFloat.mkInfinity euf.sign) ∧
  (euf.isNaN = true → euf = EUnpackedFloat.mkNaN)

@[simp] theorem CanonState_mkInfinity (sign : Bool) :
    CanonState (EUnpackedFloat.mkInfinity sign : EUnpackedFloat e s) := by
  refine ⟨fun _ => ?_, fun h => ?_⟩ <;>
    simp_all [EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite, EUnpackedFloat.sign,
      EUnpackedFloat.mkInfinity]

@[simp] theorem CanonState_mkNaN :
    CanonState (EUnpackedFloat.mkNaN : EUnpackedFloat e s) := by
  refine ⟨fun h => ?_, fun _ => rfl⟩
  simp_all [EUnpackedFloat.isInfinite, EUnpackedFloat.mkNaN]

@[simp] theorem CanonState_mkNumber (n : UnpackedFloat e s) :
    CanonState (EUnpackedFloat.mkNumber n) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp_all [EUnpackedFloat.isInfinite, EUnpackedFloat.isNaN, EUnpackedFloat.mkNumber]

@[simp] theorem CanonState_mkZero (sign : Bool) :
    CanonState (EUnpackedFloat.mkZero sign : EUnpackedFloat e s) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp_all [EUnpackedFloat.isInfinite, EUnpackedFloat.isNaN, EUnpackedFloat.mkZero]

theorem CanonState.cond {c : Bool} {a b : EUnpackedFloat e s}
    (ha : CanonState a) (hb : CanonState b) : CanonState (bif c then a else b) := by
  cases c <;> assumption

theorem CanonState.ite {c : Prop} [Decidable c] {a b : EUnpackedFloat e s}
    (ha : CanonState a) (hb : CanonState b) : CanonState (if c then a else b) := by
  split <;> assumption

theorem CanonState.isNaN_false_of_isInfinite {euf : EUnpackedFloat e s}
    (h : euf.isInfinite = true) : euf.isNaN = false := by
  simp_all [EUnpackedFloat.isInfinite, EUnpackedFloat.isNaN]

/-- `neg` of a non-`NaN` canonical value is canonical. (`neg` flips the sign of `mkNaN`, so the
`NaN`-freeness hypothesis is needed; the rounding circuit only negates `Number`/`Infinity`
sub-results.) -/
theorem sign_neg (euf : EUnpackedFloat e s) : (-euf).sign = !euf.sign := by
  simp [EUnpackedFloat.neg, EUnpackedFloat.sign, UnpackedFloat.neg_sign]

theorem neg_mkInfinity (sign : Bool) :
    -(EUnpackedFloat.mkInfinity sign : EUnpackedFloat e s) = EUnpackedFloat.mkInfinity !sign := rfl

theorem CanonState.neg {euf : EUnpackedFloat e s}
    (h : CanonState euf) (hnan : euf.isNaN = false) : CanonState (-euf) := by
  obtain ⟨hInf, _⟩ := h
  refine ⟨fun hi => ?_, fun hn => ?_⟩
  · rw [EUnpackedFloat.isInfinite_neg_eq_isInfinite] at hi
    have heq : euf = EUnpackedFloat.mkInfinity euf.sign := hInf hi
    rw [sign_neg, ← neg_mkInfinity, ← heq]
  · rw [EUnpackedFloat.isNaN_neg_eq_isNaN] at hn
    rw [hn] at hnan; simp at hnan

theorem CanonState_normalize {euf : EUnpackedFloat e s} (h : CanonState euf) :
    CanonState euf.normalize := by
  rw [EUnpackedFloat.normalize]
  cases hnum : euf.isNumber
  · simpa [hnum] using h
  · simp only [hnum, cond_true]
    exact CanonState_mkNumber _

/-! ### `CanonState` of the rounding circuit (RNE) -/

variable {eu su : Nat}

theorem CanonState_blastLowerNonneg (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    CanonState (uf.blastLowerNonneg tep tsp) := by
  simp only [UnpackedFloat.blastLowerNonneg]
  repeat' split
  all_goals simp

theorem blastLowerNonneg_not_isNaN (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    (uf.blastLowerNonneg tep tsp).isNaN = false := by
  simp only [UnpackedFloat.blastLowerNonneg]
  repeat' split
  all_goals simp [EUnpackedFloat.isNaN, EUnpackedFloat.mkNumber, EUnpackedFloat.mkInfinity,
    EUnpackedFloat.mkZero]

theorem CanonState_blastUpperNonneg (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    CanonState (uf.blastUpperNonneg tep tsp) := by
  simp only [UnpackedFloat.blastUpperNonneg]
  repeat' split
  all_goals simp

theorem blastUpperNonneg_not_isNaN (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    (uf.blastUpperNonneg tep tsp).isNaN = false := by
  simp only [UnpackedFloat.blastUpperNonneg]
  repeat' split
  all_goals simp [EUnpackedFloat.isNaN, EUnpackedFloat.mkNumber, EUnpackedFloat.mkInfinity,
    EUnpackedFloat.mkZero]

theorem CanonState_blastUpper (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    CanonState (uf.blastUpper tep tsp) := by
  unfold UnpackedFloat.blastUpper
  split
  · unfold UnpackedFloat.blastUpperNeg
    exact (CanonState_blastLowerNonneg _ _ _).neg (blastLowerNonneg_not_isNaN _ _ _)
  · exact CanonState_blastUpperNonneg _ _ _

theorem CanonState_blastLower (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    CanonState (uf.blastLower tep tsp) := by
  unfold UnpackedFloat.blastLower
  split
  · unfold UnpackedFloat.blastLowerNeg
    exact (CanonState_blastUpperNonneg _ _ _).neg (blastUpperNonneg_not_isNaN _ _ _)
  · exact CanonState_blastLowerNonneg _ _ _

theorem CanonState_blastSmtLibRoundRNE (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    CanonState (uf.blastSmtLibRoundRNE tep tsp) := by
  unfold UnpackedFloat.blastSmtLibRoundRNE
  repeat' split
  all_goals first
    | exact CanonState_blastUpper _ _ _
    | exact CanonState_blastLower _ _ _
    | simp

/-- **Canonical special states of the RNE rounder output.** -/
theorem CanonState_blastSmtLibRound_RNE (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    CanonState (uf.blastSmtLibRound tep tsp .RNE) := by
  unfold UnpackedFloat.blastSmtLibRound
  split
  · exact CanonState_mkZero _
  · split
    · simp [blastRounderSpecialCaseOverflow]
    · split
      · simp [blastRounderSpecialCaseUnderflow]
      · apply CanonState_normalize
        unfold UnpackedFloat.blastSmtLibRoundAux
        exact CanonState_blastSmtLibRoundRNE _ _ _

/-! ### `Packable` closure for the arithmetic ops (RNE) -/

/-- A `Packable` value that is not NaN/∞/zero has a normalized (msb-set) significand. -/
theorem msb_num_of_Packable_of_not_special
    {a : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : a.Packable)
    (hnan : a.isNaN = false) (hinf : a.isInfinite = false) (hzero : a.isZero = false) :
    a.num.sig.msb = true := by
  have hstate : a.state = .Number := by
    rcases h : a.state <;> simp_all [EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite]
  have hnum : a.num.Packable := ha hstate
  have hsig : a.num.sig ≠ 0#(s + 1) := by
    have hz : a.num.isZero = false := by
      simpa [EUnpackedFloat.isZero, EUnpackedFloat.isNumber, hstate] using hzero
    simpa [UnpackedFloat.isZero] using hz
  exact (UnpackedFloat.normalize_eq_self_iff a.num hsig).mp hnum.1

theorem Packable_mul (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : a.Packable) (hb : b.Packable) :
    (EUnpackedFloat.mul .RNE a b).Packable := by
  have he1 : 1 < e := by omega
  unfold EUnpackedFloat.mul
  by_cases h1 : (a.isNaN || b.isNaN || a.isInfinite && b.isZero || b.isInfinite && a.isZero) = true
  · simp only [h1, cond_true]; exact Fp.EUnpackedFloat.Packable_of_state_ne_Number (by simp [EUnpackedFloat.mkNaN])
  · simp only [Bool.not_eq_true] at h1; simp only [h1, cond_false]
    by_cases h2 : (a.isInfinite || b.isInfinite) = true
    · simp only [h2, cond_true]
      exact Fp.EUnpackedFloat.Packable_of_state_ne_Number (by simp [EUnpackedFloat.mkInfinity])
    · simp only [Bool.not_eq_true] at h2; simp only [h2, cond_false]
      by_cases h3 : (a.isZero || b.isZero) = true
      · simp only [h3, cond_true]; exact Fp.EUnpackedFloat.mkZero_Packable he1 hs _
      · simp only [Bool.not_eq_true] at h3; simp only [h3, cond_false]
        have hna : a.isNaN = false := by simp_all
        have hnb : b.isNaN = false := by simp_all
        have hia : a.isInfinite = false := by simp_all
        have hib : b.isInfinite = false := by simp_all
        have hza : a.isZero = false := by simp_all
        have hzb : b.isZero = false := by simp_all
        have hmsb : (a.num.mul b.num).sig.msb = true :=
          UnpackedFloat.msb_mul_eq_true_of_msb_eq_true
            (msb_num_of_Packable_of_not_special ha hna hia hza)
            (msb_num_of_Packable_of_not_special hb hnb hib hzb)
        have hxnorm : (a.num.mul b.num).normalize = a.num.mul b.num :=
          UnpackedFloat.normalize_eq_self_of_msb_eq_true _ hmsb
        exact Fp.UnpackedFloat.blastSmtLibRound_Packable_of_RNE (by grind) (by grind) (by grind)
          (by simp [Nat.mul_add]; grind only) _ hxnorm

/-- **The RNE rounder output round-trips through `pack`/`unpack`.** -/
theorem blastSmtLibRound_pack_unpack (he : 2 < e) (hs : 0 < s)
    (heu : exponentWidth e s ≤ eu) (hsu : s + 2 ≤ su)
    (uf : UnpackedFloat eu su) (hnorm : uf.normalize = uf) :
    (uf.blastSmtLibRound e s .RNE : EUnpackedFloat (exponentWidth e s) (s + 1)).pack.unpack
      = uf.blastSmtLibRound e s .RNE :=
  pack_unpack_of_Packable (by omega) hs _
    (Fp.UnpackedFloat.blastSmtLibRound_Packable_of_RNE he hs heu hsu uf hnorm)
    (CanonState_blastSmtLibRound_RNE uf e s).2
    (CanonState_blastSmtLibRound_RNE uf e s).1

/-! ## `Canonical`: the single source of truth

`Canonical euf` bundles the two independent obligations that characterize the `pack ∘ unpack`
fixpoint: `euf.Packable` (the `Number` payload is normalized and exactly representable) and
`CanonState euf` (the `∞`/`NaN` states carry the canonical smart-constructor `num`). It is
*exactly* the set of fixpoints — see `pack_unpack_eq_self_iff` below — and it composes: every
`pf.unpack` is `Canonical`, and every arithmetic op maps `Canonical` inputs to a `Canonical`
output. -/

/-- A value is **canonical** iff it is a fixpoint of `pack ∘ unpack` (`pack_unpack_eq_self_iff`). -/
def Canonical (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) : Prop :=
  euf.Packable ∧ CanonState euf

/-- Sufficiency: a `Canonical` value round-trips. -/
theorem pack_unpack_of_Canonical (he : 1 < e) (hs : 0 < s)
    (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) (h : Canonical euf) :
    euf.pack.unpack = euf :=
  pack_unpack_of_Packable he hs euf h.1 h.2.2 h.2.1

/-! ### `mul` -/

theorem CanonState_mul (a b : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    CanonState (EUnpackedFloat.mul .RNE a b) := by
  unfold EUnpackedFloat.mul
  exact CanonState.cond CanonState_mkNaN (CanonState.cond (CanonState_mkInfinity _)
    (CanonState.cond (CanonState_mkZero _) (CanonState_blastSmtLibRound_RNE _ _ _)))

/-- `mul` preserves `Canonical`. -/
theorem Canonical_mul (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : Canonical a) (hb : Canonical b) :
    Canonical (EUnpackedFloat.mul .RNE a b) :=
  ⟨Packable_mul he hs ha.1 hb.1, CanonState_mul a b⟩

/-- **`mul` cancellation.** -/
theorem mul_pack_unpack (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : Canonical a) (hb : Canonical b) :
    (EUnpackedFloat.mul .RNE a b).pack.unpack = EUnpackedFloat.mul .RNE a b :=
  pack_unpack_of_Canonical (by omega) hs _ (Canonical_mul he hs ha hb)

/-! ### `div` -/

theorem Packable_div (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : a.Packable) (hb : b.Packable) :
    (EUnpackedFloat.div .RNE a b).Packable := by
  have he1 : 1 < e := by omega
  unfold EUnpackedFloat.div
  by_cases h1 : (a.isNaN || b.isNaN || a.isInfinite && b.isInfinite || a.isZero && b.isZero) = true
  · simp only [h1, cond_true]; exact Fp.EUnpackedFloat.Packable_of_state_ne_Number (by simp [EUnpackedFloat.mkNaN])
  · simp only [Bool.not_eq_true] at h1; simp only [h1, cond_false]
    by_cases h2 : (a.isInfinite || b.isZero) = true
    · simp only [h2, cond_true]
      exact Fp.EUnpackedFloat.Packable_of_state_ne_Number (by simp [EUnpackedFloat.mkInfinity])
    · simp only [Bool.not_eq_true] at h2; simp only [h2, cond_false]
      by_cases h3 : (a.isZero || b.isInfinite) = true
      · simp only [h3, cond_true]; exact Fp.EUnpackedFloat.mkZero_Packable he1 hs _
      · simp only [Bool.not_eq_true] at h3; simp only [h3, cond_false]
        have hna : a.isNaN = false := by simp_all
        have hnb : b.isNaN = false := by simp_all
        have hia : a.isInfinite = false := by simp_all
        have hib : b.isInfinite = false := by simp_all
        have hza : a.isZero = false := by simp_all
        have hzb : b.isZero = false := by simp_all
        have hmsb : (a.num.div b.num).sig.msb = true :=
          Fp.UnpackedFloat.msb_div_eq_true a.num b.num (by omega)
            (msb_num_of_Packable_of_not_special ha hna hia hza)
            (msb_num_of_Packable_of_not_special hb hnb hib hzb)
        have hxnorm : (a.num.div b.num).normalize = a.num.div b.num :=
          UnpackedFloat.normalize_eq_self_of_msb_eq_true _ hmsb
        exact Fp.UnpackedFloat.blastSmtLibRound_Packable_of_RNE (by grind) (by grind) (by omega)
          (by omega) _ hxnorm

theorem CanonState_div (a b : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    CanonState (EUnpackedFloat.div .RNE a b) := by
  unfold EUnpackedFloat.div
  exact CanonState.cond CanonState_mkNaN (CanonState.cond (CanonState_mkInfinity _)
    (CanonState.cond (CanonState_mkZero _) (CanonState_blastSmtLibRound_RNE _ _ _)))

/-- `div` preserves `Canonical`. -/
theorem Canonical_div (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : Canonical a) (hb : Canonical b) :
    Canonical (EUnpackedFloat.div .RNE a b) :=
  ⟨Packable_div he hs ha.1 hb.1, CanonState_div a b⟩

/-- **`div` cancellation.** -/
theorem div_pack_unpack (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : Canonical a) (hb : Canonical b) :
    (EUnpackedFloat.div .RNE a b).pack.unpack = EUnpackedFloat.div .RNE a b :=
  pack_unpack_of_Canonical (by omega) hs _ (Canonical_div he hs ha hb)

/-! ### `add` / `sub` -/

/-- A value that is neither NaN nor ∞ has canonical special states (both implications vacuous). -/
theorem CanonState_of_not_special {a : EUnpackedFloat e s}
    (hnan : a.isNaN = false) (hinf : a.isInfinite = false) : CanonState a := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp_all

theorem CanonState_add (a b : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    CanonState (EUnpackedFloat.add .RNE a b) := by
  unfold EUnpackedFloat.add
  by_cases h1 : (a.isNaN || b.isNaN || a.isInfinite && b.isInfinite && a.sign != b.sign) = true
  · simp only [h1, cond_true]; exact CanonState_mkNaN
  · simp only [Bool.not_eq_true] at h1; simp only [h1, cond_false]
    by_cases h2 : (a.isInfinite && b.isInfinite && a.sign == b.sign ||
        a.isInfinite && !b.isInfinite || !a.isInfinite && b.isInfinite) = true
    · simp only [h2, cond_true]; exact CanonState_mkInfinity _
    · simp only [Bool.not_eq_true] at h2; simp only [h2, cond_false]
      by_cases h3 : (UnpackedFloat.structBeq a.num b.num.neg) = true
      · simp only [h3, cond_true]; exact CanonState_mkZero _
      · simp only [Bool.not_eq_true] at h3; simp only [h3, cond_false]
        by_cases h4 : a.isZero = true
        · simp only [h4, cond_true]
          exact CanonState_of_not_special (by grind) (by grind)
        · simp only [Bool.not_eq_true] at h4; simp only [h4, cond_false]
          by_cases h5 : b.isZero = true
          · simp only [h5, cond_true]
            exact CanonState_of_not_special (by grind) (by grind)
          · simp only [Bool.not_eq_true] at h5; simp only [h5, cond_false]
            exact CanonState_blastSmtLibRound_RNE _ _ _

theorem Packable_add (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : a.Packable) (hb : b.Packable) :
    (EUnpackedFloat.add .RNE a b).Packable := by
  have he1 : 1 < e := by omega
  unfold EUnpackedFloat.add
  by_cases h1 : (a.isNaN || b.isNaN || a.isInfinite && b.isInfinite && a.sign != b.sign) = true
  · simp only [h1, cond_true]
    exact Fp.EUnpackedFloat.Packable_of_state_ne_Number (by simp [EUnpackedFloat.mkNaN])
  · simp only [Bool.not_eq_true] at h1; simp only [h1, cond_false]
    by_cases h2 : (a.isInfinite && b.isInfinite && a.sign == b.sign ||
        a.isInfinite && !b.isInfinite || !a.isInfinite && b.isInfinite) = true
    · simp only [h2, cond_true]
      exact Fp.EUnpackedFloat.Packable_of_state_ne_Number (by simp [EUnpackedFloat.mkInfinity])
    · simp only [Bool.not_eq_true] at h2; simp only [h2, cond_false]
      by_cases h3 : (UnpackedFloat.structBeq a.num b.num.neg) = true
      · simp only [h3, cond_true]; exact Fp.EUnpackedFloat.mkZero_Packable he1 hs _
      · simp only [Bool.not_eq_true] at h3; simp only [h3, cond_false]
        by_cases h4 : a.isZero = true
        · simp only [h4, cond_true]; exact hb
        · simp only [Bool.not_eq_true] at h4; simp only [h4, cond_false]
          by_cases h5 : b.isZero = true
          · simp only [h5, cond_true]; exact ha
          · simp only [Bool.not_eq_true] at h5; simp only [h5, cond_false]
            have hna : a.isNaN = false := by grind
            have hnb : b.isNaN = false := by grind
            have hia : a.isInfinite = false := by grind
            have hib : b.isInfinite = false := by grind
            have hmsba := msb_num_of_Packable_of_not_special ha hna hia h4
            have hmsbb := msb_num_of_Packable_of_not_special hb hnb hib h5
            have hsumne : a.num.toRat + b.num.toRat ≠ 0 :=
              Fp.UnpackedFloat.toRat_add_toRat_ne_zero_of_not_structBeq_neg a.num b.num hmsba hmsbb
                (by simpa using h3)
            have hxnorm : (a.num.add b.num).normalize = a.num.add b.num :=
              UnpackedFloat.normalize_eq_self_of_msb_eq_true _
                (Fp.UnpackedFloat.msb_add_eq_true a.num b.num (by omega) hmsba hmsbb hsumne)
            exact Fp.UnpackedFloat.blastSmtLibRound_Packable_of_RNE (by grind) (by grind)
              (by omega) (by omega) _ hxnorm

/-- `add` preserves `Canonical`. -/
theorem Canonical_add (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : Canonical a) (hb : Canonical b) :
    Canonical (EUnpackedFloat.add .RNE a b) :=
  ⟨Packable_add he hs ha.1 hb.1, CanonState_add a b⟩

/-- **`add` cancellation.** -/
theorem add_pack_unpack (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : Canonical a) (hb : Canonical b) :
    (EUnpackedFloat.add .RNE a b).pack.unpack = EUnpackedFloat.add .RNE a b :=
  pack_unpack_of_Canonical (by omega) hs _ (Canonical_add he hs ha hb)

/-- `sub` preserves `Canonical` (`sub = add · (neg)`; `neg` preserves `Packable`, and the
`add`-output's state is canonical unconditionally). -/
theorem Canonical_sub (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : Canonical a) (hb : Canonical b) :
    Canonical (EUnpackedFloat.sub .RNE a b) := by
  unfold EUnpackedFloat.sub
  exact ⟨Packable_add he hs ha.1 (Fp.EUnpackedFloat.neg_Packable hb.1), CanonState_add a b.neg⟩

/-- **`sub` cancellation** (reduces to `add`). -/
theorem sub_pack_unpack (he : 2 < e) (hs : 0 < s)
    {a b : EUnpackedFloat (exponentWidth e s) (s + 1)} (ha : Canonical a) (hb : Canonical b) :
    (EUnpackedFloat.sub .RNE a b).pack.unpack = EUnpackedFloat.sub .RNE a b :=
  pack_unpack_of_Canonical (by omega) hs _ (Canonical_sub he hs ha hb)

/-! ### `Packable` of a leaf `unpack` -/

/-- The `unpack` of any packed float is `Packable`: it lands a smart constructor or a
`Packable` `mkNumber` (`unpackNum_packable`). -/
theorem Packable_unpack (he : 1 < e) (hs : 0 < s) (pf : PackedFloat e s) :
    pf.unpack.Packable := by
  unfold PackedFloat.unpack
  by_cases hnan : pf.isNaN
  · simp only [hnan, cond_true]
    exact Fp.EUnpackedFloat.Packable_of_state_ne_Number (by simp [EUnpackedFloat.mkNaN])
  · simp only [Bool.not_eq_true] at hnan; simp only [hnan, cond_false]
    by_cases hinf : pf.isInfinite
    · simp only [hinf, cond_true]
      exact Fp.EUnpackedFloat.Packable_of_state_ne_Number (by simp [EUnpackedFloat.mkInfinity])
    · simp only [Bool.not_eq_true] at hinf; simp only [hinf, cond_false]
      by_cases hzero : pf.isZero
      · simp only [hzero, cond_true]; exact Fp.EUnpackedFloat.mkZero_Packable he hs _
      · simp only [Bool.not_eq_true] at hzero; simp only [hzero, cond_false]
        have hnorm : pf.isNormOrNonzeroSubnorm :=
          PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero
            (by simp [hnan]) (by simp [hinf]) (by simp [hzero])
        exact Fp.EUnpackedFloat.mkNumber_Packable (PackedFloat.unpackNum_packable he hs pf hnorm)

/-! ## The characterization and the `unpack` corollary -/

/-- **Necessity.** A fixpoint of `pack ∘ unpack` is `Canonical`: it equals `euf.pack.unpack`,
which is always the `unpack` of a packed float (hence `Packable`, `Packable_unpack`) and always
in canonical `∞`/`NaN` form (`unpack_pack_of_isInfinite` / `unpack_pack_of_isNaN`). -/
theorem Canonical_of_pack_unpack (he : 1 < e) (hs : 0 < s)
    (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) (h : euf.pack.unpack = euf) :
    Canonical euf := by
  refine ⟨by rw [← h]; exact Packable_unpack he hs euf.pack, ⟨fun hinf => ?_, fun hnan => ?_⟩⟩
  · exact h.symm.trans (unpack_pack_of_isInfinite euf hinf hs)
  · exact h.symm.trans (unpack_pack_of_isNaN euf hnan)

/-- **The characterization.** `euf` is a fixpoint of `pack ∘ unpack` iff it is `Canonical`. -/
theorem pack_unpack_eq_self_iff (he : 1 < e) (hs : 0 < s)
    (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    euf.pack.unpack = euf ↔ Canonical euf :=
  ⟨Canonical_of_pack_unpack he hs euf, pack_unpack_of_Canonical he hs euf⟩

/-- **Every `pf.unpack` is `Canonical`** — no hypothesis on `pf`. This is why chained ops cancel
at any nesting depth: the leaves are `Canonical` and each op preserves `Canonical`. -/
theorem Canonical_unpack (he : 1 < e) (hs : 0 < s) (pf : PackedFloat e s) :
    Canonical pf.unpack := by
  refine ⟨Packable_unpack he hs pf, ?_⟩
  unfold PackedFloat.unpack
  by_cases hnan : pf.isNaN
  · simp only [hnan, cond_true]; exact CanonState_mkNaN
  · simp only [Bool.not_eq_true] at hnan; simp only [hnan, cond_false]
    by_cases hinf : pf.isInfinite
    · simp only [hinf, cond_true]; exact CanonState_mkInfinity _
    · simp only [Bool.not_eq_true] at hinf; simp only [hinf, cond_false]
      by_cases hzero : pf.isZero
      · simp only [hzero, cond_true]; exact CanonState_mkZero _
      · simp only [Bool.not_eq_true] at hzero; simp only [hzero, cond_false]
        exact CanonState_mkNumber _

/-- info: 'EUnpackedFloat.pack_unpack_eq_self_iff' depends on axioms: [propext,
 BitVec.toNat_clz_cons,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pack_unpack_eq_self_iff

end EUnpackedFloat
