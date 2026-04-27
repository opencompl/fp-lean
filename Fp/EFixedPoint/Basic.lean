import Fp.FixedPoint.Basic
import Fp.Constants.Basic

/--
A fixed point number extended with infinity and NaN.
-/
@[ext]
structure EFixedPoint (width prec : Nat) where
  state : State
  num : FixedPoint width prec
deriving DecidableEq, Repr

attribute [bv_normalize] EFixedPoint.ext_iff

@[bv_normalize]
theorem EFixedPoint.ext_iff_beq {x y : EFixedPoint width exOffset}
  : (x == y) = (x.state == y.state && x.num == y.num) := by
  cases h : (x == y) <;> simp_all [EFixedPoint.ext_iff]

@[bv_normalize]
theorem EFixedPoint.bne_to_beq {x y : EFixedPoint width exOffset}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [EFixedPoint.ext_iff]

@[bv_normalize]
theorem EFixedPoint.eq_cond_state {x y : EFixedPoint width exOffset} :
  (bif b then x else y).state = bif b then x.state else y.state := by
  cases b <;> rfl

@[bv_normalize]
theorem EFixedPoint.eq_cond_num {x y : EFixedPoint width exOffset} :
  (bif b then x else y).num = bif b then x.num else y.num := by
  cases b <;> rfl

class HExOffset (e : Nat) (m : Nat) where
  h : e < m

instance HExOffsetSucc [hex : HExOffset e m] :
    HExOffset e (m + 1) where
  h := by
    have := hex.h
    omega

instance HExOffsetAdd [hex : HExOffset e m] (k : Nat) :
    HExOffset (e + k) (m + k) where
  h := by
    have := hex.h
    omega

instance HExOffsetDouble [hex : HExOffset e m] :
    HExOffset (e + e) (m + m) where
  h := by
    have := hex.h
    omega
