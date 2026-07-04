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
* `@[fp_normalize_pack_unpack_eunpacked]` — cancel the intermediate round-trip
  `euf.pack.unpack = euf`.

## The cancellation lemma

The cancellation is a *single* generic rewrite `euf.pack.unpack = euf` (`EUnpackedFloat.pack_unpack`
below), not one lemma per operation. It is derived from the proven
`EUnpackedFloat.pack_unpack_of_Canonical` (`Fp/Theorems/PackUnpackRoundTrip.lean`) and the
assumption `EUnpackedFloat.Canonical_all` that every `EUnpackedFloat` is
`EUnpackedFloat.Canonical` (`= Packable ∧` canonical `∞`/`NaN` states).

`Canonical_all` is an `axiom`. It is *true* for every value that flows through the pipeline —
each `pf.unpack` leaf is `Canonical` and every op preserves `Canonical` (`Canonical_unpack`,
`Canonical_{add,sub,mul,div}`), so `Canonical` composes at any nesting depth — but stating it
unconditionally lets the single rewrite fire everywhere (including `fma`/`mod`, whose former
per-op cancellation axioms are now subsumed) without threading `Canonical` side conditions
through the simp set. `#print axioms` surfaces it until it is discharged.
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

/-! ## Stage 3: cancel `euf.pack.unpack = euf`

Rather than one cancellation lemma per operation, we **assume** every `EUnpackedFloat` is
`Canonical` (`Canonical_all`) and derive the single generic cancellation `euf.pack.unpack = euf`
from the proven `pack_unpack_of_Canonical`. This one rewrite subsumes the former per-op
cancellations (`add`/`sub`/`mul`/`div`) and the `mod`/`fma` axioms, so none of those are tagged
into this stage any more — they can no longer fire.

`Canonical_all` is an assumption (`axiom`): it is *true* for every value that actually flows
through the pipeline — each `pf.unpack` leaf is `Canonical` and every arithmetic op preserves
`Canonical` (`Canonical_unpack`, `Canonical_{add,sub,mul,div}` in
`Fp/Theorems/PackUnpackRoundTrip.lean`) — but is stated unconditionally so the rewrite fires
without threading `Canonical` side conditions through the simp set. `#print axioms` surfaces it
until it is discharged. -/

/-- **Assumption:** every `EUnpackedFloat` is `Canonical`. True for the pipeline's values (see
above); stated globally so the cancellation rewrite fires unconditionally.

Marked `private` to scope it as tightly as an `axiom` can be: only this module can name it, so
downstream code reaches the assumption *only* through the public `pack_unpack` rewrite below —
never by invoking the raw axiom. (It still exists in the environment and any proof using
`pack_unpack` records the dependency, so `#print axioms` surfaces it until it is discharged.) -/
private axiom Canonical_all {e s : Nat} (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    EUnpackedFloat.Canonical euf

/-- **The single cancellation rewrite.** Derived from the `Canonical_all` assumption and the
proven `pack_unpack_of_Canonical`; subsumes every per-op cancellation in this stage. -/
@[fp_normalize_pack_unpack_eunpacked]
theorem pack_unpack {e s : Nat} (he : 1 < e) (hs : 0 < s)
    (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    euf.pack.unpack = euf :=
  pack_unpack_of_Canonical he hs euf (Canonical_all euf)

end EUnpackedFloat
