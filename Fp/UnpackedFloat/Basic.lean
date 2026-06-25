import Fp.Utils
import Fp.Utils.Dyadic
import Fp.Utils.Rat
import Fp.Grind
import Fp.Sign.Basic
import Fp.Constants.Basic


/--
`UnpackedFloat e s` is the *working* (unpacked) representation of a floating-point
number with exponent width `e` and significand width `s`.

This representation is intentionally different from the IEEE *packed* format
(sign bit, biased exponent field, trailing significand field).  It is designed
to make floating-point algorithms (addition, normalization, rounding, etc.)
uniform and easy to express using bitvector operations.

Mathematically, an `UnpackedFloat e s` represents the real value

  (-1)^sign · sig · 2^(ex - (s - 1))
  = (-1)^sign · (sig.toNat / 2 ^ (s - 1)) · 2^(ex.toInt)

where:
* `sign : Bool` is the sign bit,
* `sig  : BitVec s` is an **integer significand**,
* `ex   : BitVec e` is a **signed exponent**.

### Key invariants and design choices

* **Explicit hidden bit**:
  The significand includes the hidden bit explicitly.
  For normal numbers, the MSB of `sig` (bit `s-1`) is `1`.

* **Binary point after the MSB**:
  The binary point is conceptually located immediately after the most
  significant bit of `sig`.  This means `sig` is treated as an integer, and the
  scaling by `2^(s-1)` is absorbed into the exponent when interpreting the value.

* **Normalized subnormals**:
  Subnormal packed numbers are *normalized* during unpacking.
  This may require additional exponent bits beyond the packed exponent width.
  The exponent width `e` of `UnpackedFloat` is therefore chosen large enough to
  represent:
    - the smallest subnormal exponent after normalization, and
    - all normal finite exponents.

* **Uniform arithmetic**:
  By using an integer significand with a fixed MSB position, normalization,
  alignment, addition, and rounding can be implemented using only:
    - bit shifts,
    - integer addition/subtraction,
    - MSB tests,
  without fractional arithmetic.

This representation closely follows the `unpackedFloat` design used in `symfpu`
and in hardware floating-point pipelines.
-/
@[ext]
structure UnpackedFloat (e s : Nat) where
  sign : Bool
  ex : BitVec e
  sig : BitVec s
  deriving Inhabited, Repr

attribute [bv_normalize] UnpackedFloat.ext_iff

namespace UnpackedFloat

@[bv_normalize]
def neg (x : UnpackedFloat e s) : UnpackedFloat e s :=
  { x with sign := !x.sign }

@[bv_normalize]
def abs (x : UnpackedFloat e s) : UnpackedFloat e s :=
  { x with sign := false }

instance : Neg (UnpackedFloat e s) where
  neg := .neg

/-- Enumerate all UnpackedFloats of a given e and s. -/
def enumerate (e s : Nat) : Array (UnpackedFloat e s) := Id.run do
  let mut out := #[]
  for b in #[true, false] do
    for ex in [0:2^e] do
      for sig in [0:2^s] do
        out := out.push { sign := b, ex := ex, sig := sig }
  return out

@[bv_normalize]
def mkZero (sign : Bool) : UnpackedFloat e s :=
  {
    sign := sign
    ex := BitVec.intMin e
    sig := 0#s
  }

 @[simp]
 theorem sign_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).sign = sign := rfl

@[bv_normalize]
def isZero (uf : UnpackedFloat e s) : Bool :=
  -- | We don't need the exponent to be `intMin`, as the unpacked float
  -- value is zero iff the significand it zero.
  uf.sig == 0#s

-- | Why does the 'ex' fit?
@[bv_normalize]
def normalize (uf : UnpackedFloat e s) (sign := uf.sign) : UnpackedFloat e s :=
  bif uf.sig == 0#s then
    -- zero case: make it explicit!
    mkZero sign
  else
    {
      sign := uf.sign
      ex := uf.ex - uf.sig.clz.setWidth _
      sig := uf.sig <<< uf.sig.clz
    }


def toDyadic (uf : UnpackedFloat e s) : Dyadic :=
  let sig : BitVec (s + 1) := uf.sig.setWidth' (Nat.le.step Nat.le.refl)
  -- | this can lead to overflow in the case where
  -- sig = intMin. negating intMin causes overflow, so we need to be careful.
  .ofIntWithPrec (uf.sign.toSign * sig.toInt) ((s - 1 : Nat) - uf.ex.toInt)

def toRat (uf : UnpackedFloat e s) : Rat :=
  uf.toDyadic.toRat

def toSigNat (uf : UnpackedFloat e s) : Nat :=
  uf.sig.toNat

def toExpInt {e s} (uf : UnpackedFloat e s) (prec : Nat := s - 1): Int :=
  - ((prec) - uf.ex.toInt)

/--
Evaluate the value of the UnpackedFloat at a given precicsion, which by default
is `s - 1`.
-/
def toRat' (uf : UnpackedFloat e s) (prec : Nat := s - 1): Rat :=
  uf.sign.toSign * uf.toSigNat * (2 : Rat) ^ uf.toExpInt prec

@[bv_normalize]
def maxNormal (eout sout : Nat) (e s : Nat) (sign : Bool) :
    UnpackedFloat eout sout :=
  {
    sign := sign
    ex := BitVec.ofInt eout (maxNormalExp e)
    sig := (BitVec.allOnes (s + 1)).zeroExtend sout
  }

@[bv_normalize]
def minSubnormalForPackedFloat (eout sout : Nat)
  (etarget starget : Nat) (sign : Bool) :
    UnpackedFloat eout sout :=
  {
    sign := sign
    ex := BitVec.ofInt eout (minSubnormalExp etarget starget)
    -- | recall that 'startget' is in PackedFloat format, and therefore
    -- the leading one is implicit. so we need to add one to the significand to get the correct exponent.
    sig := (BitVec.leadingOne (starget + 1)).zeroExtend sout
  }

instance {P : UnpackedFloat e s → Prop}
    [∀ (uf : UnpackedFloat e s), Decidable (P uf)] : Decidable (∀ (x : UnpackedFloat e s), P x) := by
  cases hp : decideProp (fun sign ex sig => P (UnpackedFloat.mk sign ex sig))
  case isFalse h => exact isFalse (by
    simp at h ⊢
    grind only [#f34e]
  )
  case isTrue h => exact isTrue (by
    intro x
    rcases x with ⟨sign, ex, sig⟩
    have := h sign ex sig
    exact this)
  where
  decideProp (P : Bool → BitVec e → BitVec s → Prop)
      [∀ (b : Bool) (e : BitVec e) (s : BitVec s), Decidable (P b e s)] : Decidable (∀ (sign : Bool) (ex : BitVec e) (sig : BitVec s), P sign ex sig) := by
    infer_instance


instance {P : UnpackedFloat e s → Prop}
    [∀ (uf : UnpackedFloat e s), Decidable (P uf)] : Decidable (∃ (x : UnpackedFloat e s), P x) := by
  cases hp : decideProp (fun sign ex sig => P (UnpackedFloat.mk sign ex sig))
  case isFalse h => exact isFalse (by
    simp at h ⊢
    intros x
    rcases x with ⟨rfl | rfl, ex, sig⟩
    · grind only [#b5c5]
    · grind only [#b5c5]
  )
  case isTrue h => exact isTrue (by
    obtain ⟨sign, ex, sig, h⟩ := h
    exists (UnpackedFloat.mk sign ex sig)
  )
  where
  decideProp (P : Bool → BitVec e → BitVec s → Prop)
      [∀ (b : Bool) (e : BitVec e) (s : BitVec s), Decidable (P b e s)] : Decidable (∃ (sign : Bool) (ex : BitVec e) (sig : BitVec s), P sign ex sig) := by
    infer_instance

end UnpackedFloat
