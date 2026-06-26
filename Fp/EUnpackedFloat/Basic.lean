import Fp.UnpackedFloat
import Fp.Constants.Basic
import Fp.ExtRat
import Fp.ExtDyadic.Basic
import Fp.Utils
import Fp.Grind
import Fp.Sign.Basic


/--
`EUnpackedFloat e s` extends `UnpackedFloat e s` with explicit floating-point
classification flags.

The `state` field records whether the value is:
* NaN,
* ±Infinity,
* ±Zero,
* or a finite number.

When `state` indicates a finite number, the `num` field contains a valid
`UnpackedFloat` satisfying the invariants described in `UnpackedFloat`.

Separating exceptional states from the numeric payload avoids illegal bit-level
states and simplifies reasoning about floating-point operations, since each
operation can:
1. handle NaN/Inf/Zero cases explicitly, and
2. perform uniform arithmetic on normalized finite numbers.

This mirrors the structure used by `symfpu`, where unpacking converts the packed
IEEE representation into a uniform working format suitable for algorithmic
manipulation.
-/
@[ext]
structure EUnpackedFloat (e s : Nat) where
  state : State
  num   : UnpackedFloat e s
deriving Repr

attribute [bv_normalize] EUnpackedFloat.ext_iff

/--
negate the number in an EUnpackedFloat.
-/
def EUnpackedFloat.neg (x : EUnpackedFloat e s) : EUnpackedFloat e s :=
  { x with num := - x.num }

instance : Neg (EUnpackedFloat e s) where
  neg := .neg

@[simp]
theorem EUnpackedFloat.neg_def (x : EUnpackedFloat e s) : EUnpackedFloat.neg x  = -x := rfl

namespace UnpackedFloat


@[bv_normalize]
def toEUnpackedFloat (uf : UnpackedFloat e s) : EUnpackedFloat e s :=
  .mk .Number uf

@[simp]
theorem state_toEUnpackedFloat (uf : UnpackedFloat e s) : uf.toEUnpackedFloat = .mk .Number uf := rfl

end UnpackedFloat

namespace EUnpackedFloat

instance {P : EUnpackedFloat e s → Prop}
    [∀ (uf : EUnpackedFloat e s), Decidable (P uf)] : Decidable (∀ (x : EUnpackedFloat e s), P x) := by
  cases hp : decideProp (fun state num => P { state := state, num := num })
  case isFalse h => exact isFalse (by
    simp at h ⊢
    grind only [#a55c]
  )
  case isTrue h => exact isTrue (by
    intro x
    rcases x with ⟨state, num⟩
    have := h state num
    exact this)
  where
  decideProp (P : State → UnpackedFloat e s → Prop)
      [∀ (state : State) (num : UnpackedFloat e s), Decidable (P state num)] : Decidable (∀ (state : State) (num : UnpackedFloat e s), P state num) := by
    infer_instance

@[bv_normalize]
def isNaN (x : EUnpackedFloat e s) : Bool :=
  x.state == .NaN


@[bv_normalize]
def isInfinite (x : EUnpackedFloat e s) : Bool :=
  x.state == .Infinity

@[bv_normalize]
def isNumber (x : EUnpackedFloat e s) : Bool :=
  x.state == .Number

@[bv_normalize]
def isZero (x : EUnpackedFloat e s) : Bool :=
  x.isNumber && x.num.isZero

@[bv_normalize]
def sign (x : EUnpackedFloat e s) : Bool :=
  x.num.sign

@[bv_normalize]
def exp (x : EUnpackedFloat e s) : BitVec e :=
  x.num.ex

@[bv_normalize]
def sig (x : EUnpackedFloat e s) : BitVec s :=
  x.num.sig

@[bv_normalize]
def mkNaN : EUnpackedFloat e s :=
  {
    state := .NaN
    num := {
      sign := false
      ex := 0
      sig := 0
    }
  }

@[bv_normalize]
def mkInfinity (sign : Bool) : EUnpackedFloat e s :=
  {
    state := .Infinity
    num := {
      sign := sign
      ex := 0
      sig := 0
    }
  }

@[bv_normalize]
def mkNumber (num : UnpackedFloat e s) : EUnpackedFloat e s :=
  {
    state := .Number
    num := num
  }

@[bv_normalize]
def mkZero (sign : Bool) : EUnpackedFloat e s :=
  {
    state := .Number
    num := UnpackedFloat.mkZero sign
  }

@[bv_normalize]
def normalize (euf : EUnpackedFloat e s) : EUnpackedFloat e s :=
  bif euf.isNumber then
    euf.num.normalize.toEUnpackedFloat
  else
    euf

def toExtDyadic (ef : EUnpackedFloat e s) : ExtDyadic :=
  bif ef.isNaN then
    .NaN
  else bif ef.isInfinite then
    .Infinity ef.num.sign
  else
    .Number ef.num.toDyadic

def toExtRat (ef : EUnpackedFloat e s) : ExtRat :=
  bif ef.isNaN then
    .NaN
  else bif ef.isInfinite then
    .Infinity ef.num.sign
  else
    .Number ef.num.toRat

end EUnpackedFloat
