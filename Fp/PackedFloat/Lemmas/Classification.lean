import Fp.Basic

/-!
## Basic classification lemmas about `PackedFloat`

Mutual-exclusivity of the `isNaN`/`isInfinite`/`isZero`/`isNorm` predicates,
`isX_getY` lemmas relating predicates to constructors, the kind-case eliminator,
structural injectivity, and decidability instances.
-/

namespace PackedFloat

@[simp]
theorem isNorm_neg (pf : PackedFloat e s) : (- pf).isNorm = pf.isNorm := by
  simp [PackedFloat.isNorm]



@[grind =]
theorem isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero {pf : PackedFloat e s} (h : ¬ pf.isNaN) (h2 : ¬ pf.isInfinite) (h3 : ¬ pf.isZero) :
    pf.isNormOrNonzeroSubnorm := by
  simp [PackedFloat.isNormOrNonzeroSubnorm]
  simp [PackedFloat.isNaN] at h
  simp [PackedFloat.isInfinite] at h2
  simp [PackedFloat.isZero] at h3
  grind

end PackedFloat
