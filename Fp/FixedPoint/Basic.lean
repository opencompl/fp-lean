/--
A fixed point number with specified exponent offset.
-/
@[ext]
structure FixedPoint (width prec : Nat) where
    sign : Bool
    val : BitVec width
    -- | This should not be part of the structure, but a side invariant we keep in mind.
    hPrec : prec < width
deriving DecidableEq

attribute [bv_normalize] FixedPoint.ext_iff

@[bv_normalize]
theorem FixedPoint.ext_iff_beq {x y : FixedPoint width exOffset}
  : (x == y) = (x.sign == y.sign && x.val == y.val) := by
  cases h : (x == y) <;> simp_all [FixedPoint.ext_iff]

@[bv_normalize]
theorem FixedPoint.bne_to_beq {x y : FixedPoint width exOffset}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [FixedPoint.ext_iff]

@[bv_normalize]
theorem FixedPoint.eq_cond_sign {x y : FixedPoint width exOffset} :
  (bif b then x else y).sign = bif b then x.sign else y.sign := by
  cases b <;> rfl

@[bv_normalize]
theorem FixedPoint.eq_cond_val {x y : FixedPoint width exOffset} :
  (bif b then x else y).val = bif b then x.val else y.val := by
  cases b <;> rfl

instance : Repr (FixedPoint width ExOffset) where
  reprPrec (x : FixedPoint _ _) _prec :=
    f!"{if x.sign then "-" else "+"} {x.val}"

-- Concretely, any enum we have must look like a C enum, so we must flatten
-- all our state into a single enum.
