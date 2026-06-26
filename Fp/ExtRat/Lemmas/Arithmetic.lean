import Fp.ExtRat.Basic

/-!
## ExtRat arithmetic lemmas

Lemmas about add/neg/sub/mul/inv/div on ExtRat.
-/

namespace ExtRat


@[simp ←]
theorem ExtRat.zero_def : ExtRat.Number 0 = (0 : ExtRat) := rfl

@[simp ←]
theorem ExtRat.zero_def' : ExtRat.Number 0 = Zero.zero := rfl

@[simp]
theorem ExtRat.add_def {a b : ExtRat} : a.add b = a + b := rfl

@[simp]
theorem ExtRat.NaN_add (x : ExtRat) : (.NaN + x) = .NaN := rfl

@[simp]
theorem ExtRat.add_NaN (x : ExtRat) : (x + .NaN) = .NaN := by
  simp [← add_def, add]
  grind [ExtRat]

@[simp]
theorem ExtRat.add_Number (x y : Rat) :
    (ExtRat.Number x + .Number y) = .Number (x + y) := by
  simp [← add_def, add]

-- TODO: write theorems for addition for infinity and such.

@[simp]
theorem ExtRat.neg_def {a : ExtRat} : a.neg = -a := rfl

@[simp]
theorem ExtRat.neg_NaN : (-.NaN : ExtRat) = .NaN := rfl

@[simp]
theorem ExtRat.neg_infinity (s : Bool) : (-.Infinity s : ExtRat) = .Infinity (!s) := rfl

@[simp]
theorem ExtRat.neg_number (r : Rat) : (-.Number r : ExtRat) = .Number (-r) := rfl


@[simp]
theorem sub_def {a b : ExtRat} : a.sub b = a - b := rfl

@[simp]
theorem number_sub_number {r1 r2 : Rat} :
    (ExtRat.Number r1 - ExtRat.Number r2) = ExtRat.Number (r1 - r2) := by
  rw [← sub_def, sub]
  simp
  grind only

@[simp]
theorem mul_def {a b : ExtRat} : a.mul b = a * b := rfl

@[simp] theorem div_def {a b : ExtRat} : a.div b = a / b := rfl
end ExtRat
