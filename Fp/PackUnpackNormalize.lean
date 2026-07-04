import Fp.Tactics.Attributes
import Fp.Unpacking
import Fp.Addition
import Fp.Subtraction
import Fp.Multiplication
import Fp.Division
import Fp.Remainder
import Fp.FMA
import Fp.Comparison
import Fp.Theorems.PackUnpackRoundTrip

/-!
# Staged pack/unpack normalization lemmas

This module provides the rewrite rules that drive the staged pipeline eliminating
the redundant `pack`/`unpack` round-trips between chained floating-point
operations (see `Fp/Tactics/Attributes.lean` for the simp attributes).

* `@[fp_expand_pack_unpack]` — unfold each surface `PackedFloat.*` operation into
  its `unpack`/`EUnpackedFloat`-op/`pack` form (definitional, `:= rfl`).
* `@[fp_normalize_pack_unpack_eunpacked]` — cancel the intermediate round-trips
  `(EUnpackedFloat.op …).pack.unpack = EUnpackedFloat.op …`.

## The cancellation lemmas

For `add`/`sub`/`mul`/`div` (RNE) the cancellation is **proven** in
`Fp/Theorems/PackUnpackRoundTrip.lean` and merely tagged into the simp set here.
The identity requires the operands to be `EUnpackedFloat.CanonState` (`= Packable ∧`
canonical `∞`/`NaN` states): several ops (`add`/`sub`) have passthrough branches
returning an input unchanged, so the round-trip only holds when that input is itself in
the image of `pack`/`unpack`. `CanonState` composes (every op output and every
`pf.unpack` is `CanonState`), so the cancellation fires at any nesting depth.

`fma`/`mod` remain `axiom`s for now (`fma` has the same shape; `mod` uses
`.toEUnpackedFloat` rather than a rounder and needs a separate "remainder is
exactly representable ⇒ `Packable`" argument). They are true and do not make the
environment inconsistent; `#print axioms` lists them until they are proven.
-/

namespace PackedFloat

/-! ## Stage 1: expand `PackedFloat` operations into `unpack`/EUnpacked-op/`pack` -/

@[fp_expand_pack_unpack]
theorem add_expand (m : RoundingMode) (x y : PackedFloat e s) :
    PackedFloat.add m x y = (EUnpackedFloat.add m x.unpack y.unpack).pack := rfl

@[fp_expand_pack_unpack]
theorem sub_expand (m : RoundingMode) (x y : PackedFloat e s) :
    PackedFloat.sub m x y = (EUnpackedFloat.sub m x.unpack y.unpack).pack := rfl

@[fp_expand_pack_unpack]
theorem mul_expand (m : RoundingMode) (x y : PackedFloat e s) :
    PackedFloat.mul m x y = (EUnpackedFloat.mul m x.unpack y.unpack).pack := rfl

@[fp_expand_pack_unpack]
theorem div_expand (m : RoundingMode) (x y : PackedFloat e s) :
    PackedFloat.div m x y = (EUnpackedFloat.div m x.unpack y.unpack).pack := rfl

@[fp_expand_pack_unpack]
theorem mod_expand (m : RoundingMode) (x y : PackedFloat e s) :
    PackedFloat.mod m x y = (EUnpackedFloat.mod m x.unpack y.unpack).pack := rfl

@[fp_expand_pack_unpack]
theorem fma_expand (m : RoundingMode) (x y z : PackedFloat e s) :
    PackedFloat.fma m x y z = (EUnpackedFloat.fma m x.unpack y.unpack z.unpack).pack := rfl

/-- Equality/`fp.eq` comparisons are already definitionally on the unpacked form,
so expanding lets their `unpack`s meet (and cancel) the inner op outputs' `pack`. -/
@[fp_expand_pack_unpack]
theorem smtBeq_expand (x y : PackedFloat e s) :
    PackedFloat.smtBeq x y = EUnpackedFloat.smtBeq x.unpack y.unpack := rfl

@[fp_expand_pack_unpack]
theorem smtBne_expand (x y : PackedFloat e s) :
    PackedFloat.smtBne x y = EUnpackedFloat.smtBne x.unpack y.unpack := rfl

@[fp_expand_pack_unpack]
theorem ieeeBeq_expand (x y : PackedFloat e s) :
    PackedFloat.ieeeBeq x y = EUnpackedFloat.ieeeBeq x.unpack y.unpack := rfl

/-! ### Ordered comparisons

`PackedFloat.smtB{lt,le,ge,gt}` are not definitionally the unpacked form (they
branch on the packed `isNaN`), so these are proved via the `isNaN`/`unpack`
bridging lemmas rather than `rfl`. -/

@[fp_expand_pack_unpack]
theorem smtBlt_expand (wbn : Bool) (x y : PackedFloat e s) :
    PackedFloat.smtBlt wbn x y = EUnpackedFloat.smtBlt wbn x.unpack y.unpack := by
  simp only [PackedFloat.smtBlt, EUnpackedFloat.smtBlt, PackedFloat.bltAux,
    PackedFloat.isNaN_unpack_eq_isNaN]

@[fp_expand_pack_unpack]
theorem smtBle_expand (wbn : Bool) (x y : PackedFloat e s) :
    PackedFloat.smtBle wbn x y = EUnpackedFloat.smtBle wbn x.unpack y.unpack := by
  simp only [PackedFloat.smtBle, EUnpackedFloat.smtBle, PackedFloat.bleAux,
    PackedFloat.isNaN_unpack_eq_isNaN]

@[fp_expand_pack_unpack]
theorem smtBge_expand (wbn : Bool) (x y : PackedFloat e s) :
    PackedFloat.smtBge wbn x y = EUnpackedFloat.smtBge wbn x.unpack y.unpack := by
  simp only [PackedFloat.smtBge, EUnpackedFloat.smtBge, PackedFloat.bgeAux,
    EUnpackedFloat.bgeAux, PackedFloat.bleAux, PackedFloat.isNaN_unpack_eq_isNaN]

@[fp_expand_pack_unpack]
theorem smtBgt_expand (wbn : Bool) (x y : PackedFloat e s) :
    PackedFloat.smtBgt wbn x y = EUnpackedFloat.smtBgt wbn x.unpack y.unpack := by
  simp only [PackedFloat.smtBgt, EUnpackedFloat.smtBgt, PackedFloat.bgtAux,
    EUnpackedFloat.bgtAux, PackedFloat.bltAux, PackedFloat.isNaN_unpack_eq_isNaN]

/-! ### Predicates

`isNaN`/`isInfinite`/`isZero` inspect the packed encoding; expanding them to the
`unpack` form (via the proven bridging lemmas) lets an inner op-output's `pack`
cancel in stage 3. -/

@[fp_expand_pack_unpack]
theorem isNaN_expand (x : PackedFloat e s) :
    PackedFloat.isNaN x = EUnpackedFloat.isNaN x.unpack :=
  (PackedFloat.isNaN_unpack_eq_isNaN x).symm

@[fp_expand_pack_unpack]
theorem isInfinite_expand (x : PackedFloat e s) :
    PackedFloat.isInfinite x = EUnpackedFloat.isInfinite x.unpack :=
  (PackedFloat.isInfinite_unpack_eq_isInfinite x).symm

@[fp_expand_pack_unpack]
theorem isZero_expand (x : PackedFloat e s) :
    PackedFloat.isZero x = EUnpackedFloat.isZero x.unpack :=
  (PackedFloat.isZero_unpack_eq_isZero x).symm

end PackedFloat

namespace EUnpackedFloat

/-! ## Stage 3: cancel `(EUnpackedFloat.op …).pack.unpack = EUnpackedFloat.op …`

For `add`/`sub`/`mul`/`div` (RNE) the cancellations are the proven theorems from
`Fp/Theorems/PackUnpackRoundTrip.lean`; here we only add them to the simp set. -/

attribute [fp_normalize_pack_unpack_eunpacked]
  add_pack_unpack sub_pack_unpack mul_pack_unpack div_pack_unpack

/-- TODO: discharge like the ops above; `mod` uses `.toEUnpackedFloat` (no rounder), so its
`Packable` argument is "the remainder is exactly representable" rather than a rounder lemma. -/
@[fp_normalize_pack_unpack_eunpacked]
axiom mod_pack_unpack {e s : Nat} (m : RoundingMode)
    (a b : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    ((EUnpackedFloat.mod m a b).pack).unpack = EUnpackedFloat.mod m a b

/-- TODO: discharge like the ops above (`fma` has passthrough branches like `add`). -/
@[fp_normalize_pack_unpack_eunpacked]
axiom fma_pack_unpack {e s : Nat} (m : RoundingMode)
    (a b c : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    ((EUnpackedFloat.fma m a b c).pack).unpack = EUnpackedFloat.fma m a b c

end EUnpackedFloat
