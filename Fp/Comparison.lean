import Fp.Basic
import Fp.Rounding
import Fp.Addition

@[simp, bv_normalize]
def f_lt (a b : FixedPoint w e) : Bool :=
  (a.sign && b.sign && b.val < a.val) ∨
  (a.sign && ¬b.sign && (a.val ≠ 0 || b.val ≠ 0)) ∨
  (¬a.sign && ¬b.sign && a.val < b.val)

@[simp, bv_normalize]
def e_lt (a b : EFixedPoint w e) : Bool :=
  a.state != .NaN && b.state != .NaN && (
    (a.state = .Infinity && a.num.sign && (b.state = .Number || ¬b.num.sign)) ||
    (b.state = .Infinity && ¬b.num.sign && (a.state = .Number || a.num.sign)) ||
    (a.state = .Number && b.state = .Number && f_lt a.num b.num)
  )

@[simp, bv_normalize]
def e_le (a b : EFixedPoint w e) : Bool :=
  a.equal b || e_lt a b

@[simp, bv_normalize]
def lt (a b : PackedFloat w e) : Bool :=
  let comp (x y : PackedFloat w e) :=
    x.ex < y.ex || (x.ex == y.ex && x.sig < y.sig)
  ¬a.isNaN && ¬b.isNaN && (
    (a.sign && b.sign && comp b a) ||
    (a.sign && ¬b.sign && (¬a.isZero || ¬b.isZero)) ||
    (¬a.sign && ¬b.sign && comp a b)
  )

@[simp, bv_normalize]
def gt (a b : PackedFloat w e) : Bool :=
  let comp (x y : PackedFloat w e) :=
    x.ex < y.ex || (x.ex == y.ex && x.sig < y.sig)
  ¬a.isNaN && ¬b.isNaN && (
    (a.sign && b.sign && comp a b) ||
    (¬a.sign && b.sign && (¬a.isZero || ¬b.isZero)) ||
    (¬a.sign && ¬b.sign && comp b a)
  )

@[simp, bv_normalize]
def eq (a b : PackedFloat w e) : Bool :=
  ¬a.isNaN && ¬b.isNaN && (
    (a.sign == b.sign && a.ex == b.ex && a.sig == b.sig) ||
    (a.ex == 0 && b.ex == 0 && a.sig == 0 && b.sig == 0)
  )

@[simp, bv_normalize]
def le (a b : PackedFloat w e) : Bool :=
  eq a b || lt a b

@[simp, bv_normalize]
def ge (a b : PackedFloat w e) : Bool :=
  eq a b || gt a b

@[bv_normalize]
def flt_min (a b : PackedFloat e s) : PackedFloat e s :=
  if a.isNaN && b.isNaN then PackedFloat.getNaN e s
  else if b.isNaN || lt a b || (a.isZero && b.isZero && a.isSignMinus) then a
  else b

@[bv_normalize]
def flt_max (a b : PackedFloat e s) : PackedFloat e s :=
  if a.isNaN && b.isNaN then PackedFloat.getNaN e s
  else if b.isNaN || gt a b || (a.isZero && b.isZero && b.isSignMinus) then a
  else b

theorem e_lt_nan (a : EFixedPoint w e)
  : ¬(e_lt a (EFixedPoint.getNaN a.num.hExOffset)) := by
  simp [e_lt]

theorem nan_e_lt (a : EFixedPoint w e)
  : ¬(e_lt (EFixedPoint.getNaN a.num.hExOffset) a) := by
  simp [e_lt]
