import Fp.Tactics.Attributes
import Fp.Negation
import Fp.Comparison

/-!
# Bitwuzla-style FP normalization rewrites

This module collects algebraic floating-point simplifications ported from
bitwuzla's rewrite catalog. They are *symbolic* (they fire on a variable, not
just on literals), and are folded into the `fp_normalize_consts` simp-set so a
single `simp only [fp_normalize_consts]` performs both literal constant-folding
(the `dsimproc`s in `Fp/ConstFold.lean`) and these algebraic rewrites.

Rules are proved, where possible, at **both** the surface `PackedFloat` level and
the `EUnpackedFloat` level. The raw op heads (`PackedFloat.neg`, not the `-·`
notation) are used on the LHS so simp's discrimination tree matches the surface
form produced by the symbolic rewriter and the regression tests.

## Soundness note on NaN

`PackedFloat`/`EUnpackedFloat`/`UnpackedFloat` `abs`/`neg` are pure sign-bit
updates with no NaN guard, and every classification predicate reads only the
exponent/significand (Packed) or `state`/`num` (EUnpacked) — never the sign — so
the `abs`/`neg`-under-predicate rewrites hold definitionally.

Some abstract-semantics bitwuzla rules do **not** transfer to this bit-level
model as bit-equalities. In particular `fp.min a a → a` / `fp.max a a → a` are
only added at the `EUnpackedFloat` level: the `PackedFloat` versions route
through `(a.unpack).pack`, which canonicalizes non-canonical NaN payloads, so
they are not bit-identities and are intentionally omitted.
-/

/-! ## `FP_ABS_ABS_NEG`: `abs (abs a) = abs a`, `abs (neg a) = abs a`. -/

@[fp_normalize_consts]
theorem PackedFloat.abs_abs_normalize (x : PackedFloat e s) :
    PackedFloat.abs (PackedFloat.abs x) = PackedFloat.abs x := rfl

@[fp_normalize_consts]
theorem PackedFloat.abs_neg_normalize (x : PackedFloat e s) :
    PackedFloat.abs (PackedFloat.neg x) = PackedFloat.abs x := rfl

@[fp_normalize_consts]
theorem EUnpackedFloat.abs_abs_normalize
    (x : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    EUnpackedFloat.abs (EUnpackedFloat.abs x) = EUnpackedFloat.abs x := rfl

@[fp_normalize_consts]
theorem EUnpackedFloat.abs_neg_normalize
    (x : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    EUnpackedFloat.abs (EUnpackedFloat.neg x) = EUnpackedFloat.abs x := rfl

/-! ## `FP_IS_*_ABS_NEG`: classification predicates ignore `abs`/`neg`.

`fp.isInfinite`/`isNaN`/`isNormal`/`isSubnormal`/`isZero` of `abs a` or `neg a`
reduce to the predicate of `a`. -/

/-! ### PackedFloat level -/

@[fp_normalize_consts]
theorem PackedFloat.isInfinite_abs_normalize (x : PackedFloat e s) :
    PackedFloat.isInfinite (PackedFloat.abs x) = PackedFloat.isInfinite x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isInfinite_neg_normalize (x : PackedFloat e s) :
    PackedFloat.isInfinite (PackedFloat.neg x) = PackedFloat.isInfinite x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isNaN_abs_normalize (x : PackedFloat e s) :
    PackedFloat.isNaN (PackedFloat.abs x) = PackedFloat.isNaN x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isNaN_neg_normalize (x : PackedFloat e s) :
    PackedFloat.isNaN (PackedFloat.neg x) = PackedFloat.isNaN x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isNorm_abs_normalize (x : PackedFloat e s) :
    PackedFloat.isNorm (PackedFloat.abs x) = PackedFloat.isNorm x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isNorm_neg_normalize (x : PackedFloat e s) :
    PackedFloat.isNorm (PackedFloat.neg x) = PackedFloat.isNorm x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isNonzeroSubnorm_abs_normalize (x : PackedFloat e s) :
    PackedFloat.isNonzeroSubnorm (PackedFloat.abs x) = PackedFloat.isNonzeroSubnorm x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isNonzeroSubnorm_neg_normalize (x : PackedFloat e s) :
    PackedFloat.isNonzeroSubnorm (PackedFloat.neg x) = PackedFloat.isNonzeroSubnorm x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isZero_abs_normalize (x : PackedFloat e s) :
    PackedFloat.isZero (PackedFloat.abs x) = PackedFloat.isZero x := rfl

@[fp_normalize_consts]
theorem PackedFloat.isZero_neg_normalize (x : PackedFloat e s) :
    PackedFloat.isZero (PackedFloat.neg x) = PackedFloat.isZero x := rfl

/-! ### EUnpackedFloat level (no `isNorm`/`isNonzeroSubnorm` at this level). -/

@[fp_normalize_consts]
theorem EUnpackedFloat.isInfinite_abs_normalize
    (x : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    EUnpackedFloat.isInfinite (EUnpackedFloat.abs x) = EUnpackedFloat.isInfinite x := rfl

@[fp_normalize_consts]
theorem EUnpackedFloat.isInfinite_neg_normalize (x : EUnpackedFloat e s) :
    EUnpackedFloat.isInfinite (EUnpackedFloat.neg x) = EUnpackedFloat.isInfinite x := rfl

@[fp_normalize_consts]
theorem EUnpackedFloat.isNaN_abs_normalize
    (x : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    EUnpackedFloat.isNaN (EUnpackedFloat.abs x) = EUnpackedFloat.isNaN x := rfl

@[fp_normalize_consts]
theorem EUnpackedFloat.isNaN_neg_normalize (x : EUnpackedFloat e s) :
    EUnpackedFloat.isNaN (EUnpackedFloat.neg x) = EUnpackedFloat.isNaN x := rfl

@[fp_normalize_consts]
theorem EUnpackedFloat.isZero_abs_normalize
    (x : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    EUnpackedFloat.isZero (EUnpackedFloat.abs x) = EUnpackedFloat.isZero x := rfl

@[fp_normalize_consts]
theorem EUnpackedFloat.isZero_neg_normalize (x : EUnpackedFloat e s) :
    EUnpackedFloat.isZero (EUnpackedFloat.neg x) = EUnpackedFloat.isZero x := rfl

/-! ## `FP_MIN_EQ` / `FP_MAX_EQ`: `min a a = a`, `max a a = a` (EUnpacked level).

`minAux`/`maxAux` are `bif _ then a else a`, so they collapse via `cond_self`
regardless of the `xOnDiffZeros` flag. -/

@[fp_normalize_consts]
theorem EUnpackedFloat.minAux_self_normalize (b : Bool) (x : EUnpackedFloat e s) :
    EUnpackedFloat.minAux b x x = x := by
  simp only [EUnpackedFloat.minAux, Bool.cond_self]

@[fp_normalize_consts]
theorem EUnpackedFloat.maxAux_self_normalize (b : Bool) (x : EUnpackedFloat e s) :
    EUnpackedFloat.maxAux b x x = x := by
  simp only [EUnpackedFloat.maxAux, Bool.cond_self]

/-! ## `FP_NEG_NEG`: `neg (neg a) = a` (double-negation elimination). -/

@[fp_normalize_consts]
theorem PackedFloat.neg_neg_normalize (x : PackedFloat e s) :
    PackedFloat.neg (PackedFloat.neg x) = x := by
  simp only [PackedFloat.neg, Bool.not_not]

@[fp_normalize_consts]
theorem EUnpackedFloat.neg_neg_normalize (x : EUnpackedFloat e s) :
    EUnpackedFloat.neg (EUnpackedFloat.neg x) = x := by
  simp only [EUnpackedFloat.neg, UnpackedFloat.neg_neg]

/-! ## `FP_LT_EQ` / `FP_LEQ_EQ`: `lt a a = false`, `leq a a = ¬isNaN a`.

The SMT-LIB `whenBothNaN` flag is fixed to `false` (matching `fp.lt`/`fp.leq`,
which are `false` on NaN). `lt a a` is always `false`; `leq a a` is `true`
exactly when `a` is not NaN. Proved through the aux reflexivity helpers below. -/

theorem UnpackedFloat.bltAux_self (b : Bool) (x : UnpackedFloat e s) :
    UnpackedFloat.bltAux b x x = false := by
  simp only [UnpackedFloat.bltAux]
  cases hs : x.sign <;>
    simp [BitVec.slt, BitVec.ult]

theorem UnpackedFloat.bleAux_self (b : Bool) (x : UnpackedFloat e s) :
    UnpackedFloat.bleAux b x x = true := by
  simp only [UnpackedFloat.bleAux]
  cases hs : x.sign <;>
    simp [BitVec.slt, BitVec.ule]

theorem EUnpackedFloat.bltAux_self (b : Bool) (x : EUnpackedFloat e s) :
    EUnpackedFloat.bltAux b x x = false := by
  simp only [EUnpackedFloat.bltAux, UnpackedFloat.bltAux_self]
  cases x.isNaN <;> cases x.isInfinite <;> simp

theorem EUnpackedFloat.bleAux_self (b : Bool) (x : EUnpackedFloat e s) :
    EUnpackedFloat.bleAux b x x = !x.isNaN := by
  simp only [EUnpackedFloat.bleAux, UnpackedFloat.bleAux_self]
  cases hn : x.isNaN <;> cases x.isInfinite <;> simp

@[fp_normalize_consts]
theorem EUnpackedFloat.smtBlt_self_normalize (x : EUnpackedFloat e s) :
    EUnpackedFloat.smtBlt false x x = false := by
  simp only [EUnpackedFloat.smtBlt, EUnpackedFloat.bltAux_self, Bool.cond_self]

@[fp_normalize_consts]
theorem EUnpackedFloat.smtBle_self_normalize (x : EUnpackedFloat e s) :
    EUnpackedFloat.smtBle false x x = !x.isNaN := by
  simp only [EUnpackedFloat.smtBle, Bool.and_self, EUnpackedFloat.bleAux_self]
  cases x.isNaN <;> rfl

@[fp_normalize_consts]
theorem PackedFloat.smtBlt_self_normalize (x : PackedFloat e s) :
    PackedFloat.smtBlt false x x = false := by
  simp only [PackedFloat.smtBlt, PackedFloat.bltAux, EUnpackedFloat.bltAux_self,
    Bool.cond_self]

@[fp_normalize_consts]
theorem PackedFloat.smtBle_self_normalize (x : PackedFloat e s) :
    PackedFloat.smtBle false x x = !x.isNaN := by
  simp only [PackedFloat.smtBle, PackedFloat.bleAux, Bool.and_self,
    EUnpackedFloat.bleAux_self, PackedFloat.isNaN_unpack_eq_isNaN]
  cases x.isNaN <;> rfl
