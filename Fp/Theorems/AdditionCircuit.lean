import Fp.Addition
import Fp.Theorems.RoundEquiv

/-!
# Modular mirror of the `UnpackedFloat.add` circuit

The addition circuit (`UnpackedFloat.add`, `Fp/Addition.lean`) is finicky and prone to change, so we
mirror each `let`-binding as a named `def` here. Value lemmas for `stickyEquiv_add` / `msb_add_eq_true`
should be stated and proven against these named intermediates, so a circuit change localises to this file.

**Next step (reconstruction).** Tie the circuit to these defs, e.g.
`(x.add y).sign = (addNormSum x y).sign`, `(x.add y).ex = (addNormSum x y).ex`,
`(x.add y).sig = (addNormSum x y).sig ||| (BitVec.ofBool (addSticky x y)).setWidth' _`.
NOTE: the circuit is `bif`/`cond`-heavy and projections through `cond` are *not* definitional, so plain
`rfl`/`simp [add]` will not close these. The working recipe is to `generalize` the repeated boolean
conditions (swap cond, sign-equality, overflow `sigSum.msb`, cancellation `!sum.sig.msb`) to fresh
variables and then `cases` on them, reducing every `bif`; each branch is then `cond`-free and closes by
`rfl`/`grind`. Build the per-field reconstruction lemmas, then `toNat`/`toInt` value lemmas, then the
aligned-sum sticky core (reusing `floor_sticky_within_one` with `Y = 2^d`, lost bits via
`BitVec.toNat_and_orderEncode`), then assemble via `StickyEquiv.of_sign_grid`.
-/

namespace Fp
namespace UnpackedFloat

variable {e s : Nat}

/-- Signed exponent difference (widened by one bit). -/
def addExpDiff (x y : UnpackedFloat e s) : BitVec (e + 1) :=
  x.ex.signExtend (e + 1) - y.ex.signExtend (e + 1)

/-- Absolute exponent difference. -/
def addAbsExpDiff (x y : UnpackedFloat e s) : BitVec (e + 1) :=
  bif (addExpDiff x y).msb then -(addExpDiff x y) else addExpDiff x y

/-- The circuit swaps operands so the first is the larger; this is that condition. -/
def addSwapCond (x y : UnpackedFloat e s) : Bool :=
  (addExpDiff x y).msb || ((addAbsExpDiff x y == 0) && x.sig.ult y.sig)

/-- post-swap larger operand (the def's rebound `x`). -/
def addBig (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  bif addSwapCond x y then y else x
/-- post-swap smaller operand (the def's rebound `y`). -/
def addSmall (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  bif addSwapCond x y then x else y

/-- larger significand, extended (1 overflow bit on the left, 2 round/sticky bits on the right). -/
def addXSig (x y : UnpackedFloat e s) : BitVec (s + 3) :=
  (addBig x y).sig.setWidth' (by omega) ++ 0#2
/-- smaller significand, similarly extended and negated when the signs differ (so one adder serves
both addition and subtraction). -/
def addYSig (x y : UnpackedFloat e s) : BitVec (s + 3) :=
  bif (addBig x y).sign == (addSmall x y).sign
    then (addSmall x y).sig.setWidth' (by omega) ++ 0#2
    else -((addSmall x y).sig.setWidth' (by omega) ++ 0#2)

/-- right-shift amount for alignment, capped at `s + 3`. -/
def addShiftAmount (x y : UnpackedFloat e s) : BitVec (s + 3) :=
  bif (addAbsExpDiff x y).ult (s + 3) then (addAbsExpDiff x y).setWidth (s + 3) else (s + 3)

/-- the aligned (signed) significand sum. -/
def addSigSum (x y : UnpackedFloat e s) : BitVec (s + 3) :=
  addXSig x y + (addYSig x y).sshiftRight' (addShiftAmount x y)

/-- sticky bit: set if the alignment shift dropped a nonzero bit, or an overflow folded a bit out. -/
def addSticky (x y : UnpackedFloat e s) : Bool :=
  (addYSig x y &&& (addShiftAmount x y).orderEncode != 0)
    || ((addSigSum x y).msb && (addSigSum x y)[0])

/-- the pre-normalisation result (sign of the larger; exponent bumped on overflow; significand
right-shifted on overflow). -/
def addSum (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  { sign := (addBig x y).sign
    ex := (addBig x y).ex.signExtend (e + 1) + (BitVec.ofBool (addSigSum x y).msb).setWidth' (by omega)
    sig := ((addSigSum x y) >>> BitVec.ofBool (addSigSum x y).msb).truncate (s + 2) }

/-- normalised result: on catastrophic cancellation (`!sum.sig.msb`) renormalise. -/
def addNormSum (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  bif !(addSum x y).sig.msb then (addSum x y).normalize else (addSum x y)

end UnpackedFloat
end Fp
