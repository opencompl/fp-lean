import Fp.Basic
import Fp.Rounding
import Fp.MulInv
import Fp.Grind
import Fp.ForLean.Rat
import Fp.Rounding
import Fp.Theorems.Packing

@[bv_normalize]
def BitVec.leadingOne (w : Nat) : BitVec w :=
  1#w <<< (w - 1)

@[simp]
def BitVec.getElem_leadingOne (w : Nat) (i : Nat) (hi : i < w ) : (BitVec.leadingOne w)[i] = decide (i = w - 1) := by
  simp [leadingOne]
  grind

@[bv_normalize]
def BitVec.decrement (x : BitVec w) : BitVec w := x - 1#w

@[bv_normalize]
def BitVec.extendAtMsb (x : BitVec w) (δ : Nat) : BitVec (δ + w) :=
  x.zeroExtend _

/-- Extract from the MSB, starting at msb lo, going downward for 'len' bits.
0<----------------------->(w-1)
----------->loMsb----|len
           |
            <-----------------loLsb

-/
@[bv_normalize]
def BitVec.extractMsb' (x : BitVec w) (loMsb : Nat) (len : Nat) :
    BitVec len :=
  (x.reverse.extractLsb' loMsb len).reverse

theorem BitVec.getLsbD_extractMsb' {w lo len : Nat} (x : BitVec w)
    (i : Nat):
    (extractMsb' x lo len).getMsbD i =
    (x.getMsbD (lo + i) && decide (i < len) && decide (lo + i < w)) := by
  simp [extractMsb', BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_reverse]
  by_cases h1 : i < len
  · simp [h1]
    simp [show len - 1 - i < len by omega]
    simp [show len - 1 - (len - 1 - i) < len by omega]
    simp [show len - 1 - (len - 1 - i) = i by omega]
    intros h2 h3
    have := BitVec.lt_of_getLsbD h3
    omega
  · simp [h1]

@[bv_normalize]
def BitVec.expandingSubtract {w} (a b : BitVec w) : BitVec (w + 1) :=
  let a' : BitVec (w + 1) := a.signExtend (w + 1)
  let b' : BitVec (w + 1) := b.signExtend (w + 1)
  a' - b'


@[simp]
theorem BitVec.toInt_expandingSubtract {w} (a b : BitVec w) :
  (expandingSubtract a b).toInt = a.toInt - b.toInt := by
  simp [expandingSubtract, toInt_signExtend]
  have : 2 ^ (w + 1) / 2 = 2^w := by grind
  apply Int.bmod_eq_of_le <;> grind


@[bv_normalize]
def BitVec.width {w : Nat} (_x : BitVec w) : Nat := w

/-- bitvector that has 1 at index i and 0 everywhere else. -/
@[bv_normalize]
def BitVec.oneHotBV (i : BitVec w) : BitVec w :=
    1#w <<< i

@[simp]
theorem BitVec.getlsbD_oneHotBV (i : BitVec w) :
    (oneHotBV i).getLsbD j =
    (decide (j < w) && decide (i.toNat = j)) := by
  simp [oneHotBV]
  by_cases h1 : j < w
  · simp [h1]
    grind
  · simp [h1]

@[simp]
theorem BitVec.getElem_oneHotBV (i : BitVec w) (j : Fin w) :
    (oneHotBV i)[j] = decide (i.toNat = j) := by
  simp [← BitVec.getLsbD_eq_getElem]

/-- Convert a binary number into a unary mask of that number. -/
@[bv_normalize]
def BitVec.orderEncode (x : BitVec w) : BitVec w :=
  (oneHotBV x) - 1

theorem BitVec.orderEncode_eq_oneHotBV_sub (x : BitVec w) :
    BitVec.orderEncode x = oneHotBV x - 1 := rfl

@[simp]
theorem BitVec.orderEncode_eq_allOnes_of_le {w : Nat} (x : BitVec w)
    (h : w ≤ x.toNat) :
    orderEncode x = allOnes w := by
  simp [orderEncode, oneHotBV]
  rw [BitVec.shiftLeft_eq_zero]
  · simp [BitVec.neg_one_eq_allOnes]
  · omega

axiom AxOrderEncode {P : Prop} : P

theorem BitVec.getLsbD_orderEncode_of_lt (x : BitVec w) (i : Nat) (hi : i < w) :
    (orderEncode x).getLsbD i = (decide (i < x.toNat)) := by
  by_cases hi : x.toNat < w
  · rw [orderEncode]
    · -- ⊢ (1#w <<< x - 1).getLsbD i = decide (i < x.toNat)
      exact AxOrderEncode
  · rw [BitVec.orderEncode_eq_allOnes_of_le]
    · simp; omega
    · omega

theorem BitVec.getElem_orderEncode_of_lt {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    (orderEncode x)[i] = (decide (i < x.toNat)) := by
  rw [← getLsbD_eq_getElem]
  apply BitVec.getLsbD_orderEncode_of_lt x i hi

@[simp]
theorem BitVec.getLsbD_orderEncode {w : Nat} (x : BitVec w) (i : Nat) :
    (orderEncode x).getLsbD i = (decide (i < x.toNat) && decide (i < w)) := by
  by_cases hi : i < w
  · simp [hi]
    rw [BitVec.getElem_orderEncode_of_lt]
  · rw [BitVec.getLsbD_of_ge x.orderEncode i (by omega)]
    simp; omega

@[simp]
theorem BitVec.getElem_orderEncode {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    (orderEncode x)[i] = (decide (i < x.toNat)) := by
  rw [← getLsbD_eq_getElem]
  rw [BitVec.getLsbD_orderEncode x i]
  simp [hi]

@[simp]
theorem BitVec.orderEncode_eq_shiftRight_allOnes {x : BitVec w} :
    orderEncode x = BitVec.allOnes w >>> (w - x.toNat) := by
  ext i hi
  simp
  omega


@[bv_normalize]
def roundingDecision (mode : RoundingMode) (sign : Bool) (significandEven : Bool)
  (guardBit : Bool) (stickyBit : Bool) (_exact : Bool) : Bool :=
  match mode with
  | RoundingMode.RNE =>
      (guardBit && (stickyBit || !significandEven))
  | RoundingMode.RNA =>
      guardBit
  | RoundingMode.RTP =>
      (!sign && (guardBit || stickyBit))
  | RoundingMode.RTN =>
      (sign && (guardBit || stickyBit))
  | RoundingMode.RTZ =>
      false

@[bv_normalize]
def rounderSpecialCases
  (roundingMode : RoundingMode)
  (roundedResult : UnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1))
  (overflow : Bool)
  (underflow : Bool)
  (isZero : Bool) : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let returnInf : Bool :=
    match roundingMode with
    | RoundingMode.RNE => true
    | RoundingMode.RNA => true
    | RoundingMode.RTP => !roundedResult.sign
    | RoundingMode.RTN => roundedResult.sign
    | _ => false
  let returnZero : Bool :=
    match roundingMode with
    | RoundingMode.RNE => true
    | RoundingMode.RNA => true
    | RoundingMode.RTZ => true
    | RoundingMode.RTP =>
      -- if the rounded result is negative,
      -- then return 0 instead.
      roundedResult.sign
    | RoundingMode.RTN =>
      !roundedResult.sign

  let inf : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    EUnpackedFloat.mkInfinity roundedResult.sign
  let max : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    EUnpackedFloat.mkNumber <|
    { sign := roundedResult.sign,
      ex := BitVec.ofInt (exponentWidth targetExponentWidth targetSignificandWidth) (maxNormalExp targetExponentWidth),
      sig := BitVec.allOnes (targetSignificandWidth + 1) }
  let min : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    EUnpackedFloat.mkNumber <|
    { sign := roundedResult.sign,
      ex := BitVec.ofInt (exponentWidth targetExponentWidth targetSignificandWidth) (minSubnormalExp targetExponentWidth targetSignificandWidth),
      sig := BitVec.leadingOne (targetSignificandWidth + 1) }
  let zero : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    EUnpackedFloat.mkZero roundedResult.sign

  if isZero then
    zero
  else if underflow then
    if returnZero then zero else min
  else if overflow then
    if returnInf then inf else max
  else
    EUnpackedFloat.mkNumber <| roundedResult

axiom AxRoundPreconditions {P : Prop} : P

def mkPackedFloats (E : Nat) (S : Nat) : Array (PackedFloat E S) := Id.run do
  let mut res := #[]
  for expVal in [0:Nat.pow 2 E] do
    for sigVal in [0:Nat.pow 2 S] do
      for sign in [true, false] do
        let pf : PackedFloat E S :=
          { sign := sign,
            ex := BitVec.ofNat E expVal,
            sig := BitVec.ofNat S sigVal }
        res := res.push pf
  res

/--
Return all representable packed floats of given exponent and significand widths,
in ascending order by their rational value.
-/
def mkPackedFloatNumsSorted (E : Nat) (S : Nat) :
    Array (PackedFloat E S × Rat) := Id.run do
  let pfs ← mkPackedFloats E S
  let mut res := #[]
  for pf in pfs do
    if let .some r := pf.toRat? then
      res := res.push (pf, r)
  res.qsort (fun a b => a.2 < b.2)

/-
Implementation of RNE rounding by finding the closest representable float, exhaustively.
Note that zero needs special handling, because toRat does not distinguish +0 and -0,
but FP does.
-/
def getClosestRNEResult {expWidth sigWidth : Nat}
    (targetExponentWidth targetSignificandWidth : Nat)
    (inUf : UnpackedFloat expWidth sigWidth) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) := Id.run do
  let inRat := inUf.toRat
  let candidates := mkPackedFloatNumsSorted targetExponentWidth targetSignificandWidth
  if inRat < (candidates.getD 0 default).2 then
    EUnpackedFloat.mkInfinity true
  else if inRat > (candidates.getD (candidates.size - 1) default).2 then
    EUnpackedFloat.mkInfinity false
  else
    let candidatesWithDist := candidates.map (fun (pf, r) =>
      (pf, r, (inRat - r).abs))
    let candidatesSorted := candidatesWithDist.qsort (fun a b => a.2.2 < b.2.2)
    let out1 := candidatesSorted.getD 0 default
    let out2 := candidatesSorted.getD 1 default
    let (pf1, r1, dist1) := out1
    let (pf2, _r2, dist2) := out2
    if r1 = 0 then
      EUnpackedFloat.mkZero inUf.sign
    else
      if hlt : dist1 < dist2 then
        pf1.unpack
      else if hgt : dist2 < dist1 then
        pf2.unpack
      else
        have : dist1 = dist2 := by grind
          -- round to the nearest even number
          if r1.num % 2 == 0 then
            pf1.unpack
          else
            pf2.unpack
          -- round to nearest even.

def BitVec.toBitsStr {w : Nat} (bv : BitVec w) : String := Id.run do
  let mut s := "0b"
  for i in [0:w] do
    let bit := if bv.getMsbD i then "1" else "0"
    s := s.append bit
  s

@[bv_normalize]
def BitVec.isZero {w : Nat} (bv : BitVec w) : Bool :=
  bv = BitVec.ofNat w 0

/-- conditionally increment, and return flag of whether overflow was observed -/
@[bv_normalize]
def conditionalIncrementWithFlags (cond : Bool) (x : BitVec w) : BitVec w × Bool :=
  if cond then
    let x' := x.zeroExtend (w + 1) + 1#(w + 1)
    (x'.setWidth w, x'.msb)
  else
    (x, false)

def BitVec.smin (a b : BitVec w) : BitVec w :=
  if a.slt b then a else b

def BitVec.smax (a b : BitVec w) : BitVec w :=
  -- a > b then a else b
  -- b < a
  if b.slt a then a else b


/-- A variant of 'getLsbD' where the index is also a bitvector. -/
@[bv_normalize]
def BitVec.getLsbDBV {w : Nat} (x : BitVec w) (i : BitVec w) : Bool :=
  x &&& (1#w <<< i) ≠ 0#w

example (x y : BitVec 5) (hy : y < 3#5) : (x <<< 3#5).getLsbDBV y = false := by
  bv_decide

@[simp]
theorem BitVec.getLsbDBV_eq_getLsbD {w : Nat} (x : BitVec w) (i : BitVec w) :
    x.getLsbDBV i = x.getLsbD (i.toNat) := by
  rw [getLsbDBV]
  simp
  by_cases hx : x &&& (1#w <<< i.toNat) = 0#w
  · rw [hx]
    simp
    have : (x &&& (1#w <<< i.toNat)).getLsbD i.toNat = false := by
      grind
    grind
  · simp [hx]
    simp at hx
    have : (x &&& (1#w <<< i.toNat)).getLsbD i.toNat = true := by
      simp
      grind
    grind

def BitVec.getMsbDBV {w : Nat} (x : BitVec w) (i : BitVec w) : Bool :=
  x.getLsbDBV ((BitVec.ofNat w (w - 1)) - i)

@[simp]
theorem BitVec.getMsbDBV_eq_getMsbD {w : Nat} (x : BitVec w) (i : BitVec w)
    (hi : i.toNat < w) :
    x.getMsbDBV i = x.getMsbD (i.toNat) := by
  have : w - 1 < 2^w := by
    have : w < 2^w := by exact Nat.lt_two_pow_self
    grind
  rw [getMsbDBV, getLsbDBV_eq_getLsbD]
  rw [BitVec.toNat_sub_of_le]
  · simp
    rw [Nat.mod_eq_of_lt (by omega)]
    simp [BitVec.getMsbD]
    omega
  · rw [BitVec.le_def]
    simp only [toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/--
Extract the bits from LSB from low index `0` to high index `start` (excluded), setting other bits to zero.
-/
def BitVec.extractLsbTo0BV {w : Nat} (x : BitVec w) (start : BitVec w) : BitVec w :=
  x &&& (orderEncode start)

@[simp]
theorem BitVec.getLsbD_extractLsbTo0BV_eq_decide {w : Nat} (x : BitVec w) (start : BitVec w) (i : Nat) :
    (x.extractLsbTo0BV start).getLsbD i = (x.getLsbD i &&  decide (i < start.toNat)) := by
  rw [extractLsbTo0BV]
  rw [BitVec.getLsbD_and]
  rw [BitVec.getLsbD_orderEncode]
  by_cases hi : i < w
  · by_cases hstart : start.toNat < w
    · have : start.toNat < 2^w := by
        have : w < 2^w := by exact Nat.lt_two_pow_self
        omega
      simp [hi]
    · simp [hi]
  · simp [hi]
    intros hx
    have := BitVec.lt_of_getLsbD hx
    omega


/--
Extract out bits from 'startMsb' (excluded) down to low index `0`, setting other bits to zero.
-/
def BitVec.maskMsbTo0BV {w : Nat} (x : BitVec w) (startMsb : BitVec w) : BitVec w :=
  BitVec.extractLsbTo0BV x (BitVec.ofNat w w  - startMsb)

/--
observe that the bounds are sane.
if startMsb = 0, then we extract the full vector, and the decide is just (i < w).
if startMsb = 1, then we extract all but the MSB, and the decide is (i < w - 1).
if startMsb = w, then we extract nothing, and the decide is (i < 0) which is always false.
-/
@[simp]
theorem BitVec.getMsbD_extractMsbTo0BV_eq_decide {w : Nat}
    (x : BitVec w)
    (startMsb : BitVec w)
    (i : Nat)
    (hstart : startMsb.toNat ≤ w) :
    (x.maskMsbTo0BV startMsb).getLsbD i =
      (x.getLsbD i &&  decide (i < (w - startMsb.toNat))) := by
  rw [maskMsbTo0BV]
  rw [BitVec.getLsbD_extractLsbTo0BV_eq_decide]
  by_cases hx : x.getLsbD i
  · simp only [hx, Bool.true_and, decide_eq_decide]
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      simp
      omega
  · simp [hx]


/-- a > b -/
@[bv_normalize]
private def BitVec.sgt {w : Nat} (a b : BitVec w) : Bool :=
  b.slt a


/--
This implementation performs rounding, with many redundant checks
to help with debugging.

Preconditions for rounding to succeed:

(hs : sigWidth >= targetSignificandWidth + 1 + 2)
(he : expWidth >= targetExponentWidth)
(hs' : sigWidth >= 1) :
-/
@[bv_normalize]
def UnpackedFloat.debugRound {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
  (inUf : UnpackedFloat expWidth sigWidth)
  (mode : RoundingMode) :
  (EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) × String) :=
  let out := ""
  -- round a normalized, normal float.
  let out := out ++ s!"\n--- rounding: {repr inUf} ---"
  let out := out ++ s!"\n  val (Q): {inUf.toRat} = sig({inUf.sig.toBitsStr}=nat:{inUf.sig.toNat})) * 2 ** exp:([{inUf.ex.toBitsStr}=int:{inUf.ex.toInt}] - ({sigWidth - 1}))"
  let exp : BitVec expWidth := inUf.ex

  let targetMinNormalExp : BitVec expWidth :=
    BitVec.ofInt expWidth (minNormalExp targetExponentWidth)
  let out := out ++ s!"\nexp: {exp.toBitsStr} = int:{exp.toInt}"
  let out := out ++ s!"\ntargetMinNormalExp: {targetMinNormalExp.toBitsStr} = int:{targetMinNormalExp.toInt}"
  let out := if targetMinNormalExp.toInt != minNormalExp targetExponentWidth then
    out ++ "\nERROR: targetMinNormalExp.toInt != minNormalExp targetExponentWidth"
  else
    out

  let out := out ++ s!"\nmaxNormalExp: {maxNormalExp targetExponentWidth}"
  let earlyOverflow : Bool := exp.sgt (BitVec.ofInt expWidth (maxNormalExp targetExponentWidth))
  let out := out ++ s!"\nearlyOverflow: {earlyOverflow}"
  let out := out ++ s!"\nminSubnormalExp: {minSubnormalExp targetExponentWidth targetSignificandWidth}"
  -- early underflow:
  let earlyUnderflow : Bool := exp.slt (BitVec.ofInt expWidth (minSubnormalExp targetExponentWidth targetSignificandWidth - 1))
  let out := out ++ s!"\nearlyUnderflow: {earlyUnderflow}"

  -- force exponent to be at least min normal exponent.
  let expGeMin :=
    if exp.slt targetMinNormalExp then
      targetMinNormalExp
    else
      exp
  let out := out ++ s!"\nexpGeMin: {expGeMin.toBitsStr} = int:{expGeMin.toInt}"

  -- how much to shift 'sig' by.
  let shiftAmtPositive := expGeMin - exp
  let out := out ++ s!"\nshiftAmtPositive: {shiftAmtPositive.toBitsStr} = int:{shiftAmtPositive.toInt} = nat:{shiftAmtPositive.toNat}"
  -- have : shiftAmtPositive.toInt ≥ 0 := AxRoundNormal
  -- have : shiftAmtPositive.toNat = shiftAmtPositive.toInt := AxRoundNormal
  -- have : exp.toInt + shiftAmtPositive.toInt = expGeMin.toInt := AxRoundNormal

  let sigWithHidden : BitVec sigWidth := inUf.sig
  let out := out ++ s!"\nsigWithHidden: {sigWithHidden.toBitsStr} = nat:{sigWithHidden.toNat}"

  -- in inf precision, we want to take:
  --                ↓ guard
  --  1 . a b c d e f g h ... * 2^exp
  --  ============↑ (6 bits of precision)
  -- suppose we exceed by 3 bits, so shiftAmt = 3.

  -- and convert to target precision:
  --                  ↓ guard
  --  0 . 0 0 0 1 a b c d e f g h * 2^exp + 2^shiftAmt | to make 'exp + shiftAmt >= minNormalExp'.
  --  ==============↑ (6 bits of precision)
  -- (sigWidth - 1) - (targetSignificandWidth - 1) -
  -- let targetSigWithHidden : BitVec (targetSignificandWidth + 1) :=
  --   sigWithHidden.extractMsb' 0 (targetSignificandWidth + 1)
  -- to grab the bit *after* w bits, it's the bit x[w].
  -- we want the bit *after* targetSignificandWidth + 1, i.e., bit at index targetSignificandWidth + 1.
  let out := out ++ s!"\nguardBitIndexFromLsb: (sigWidth({sigWidth}) - 1)  - (targetSignificandWidth({targetSignificandWidth}) + 1) = {(sigWidth - 1) - (targetSignificandWidth + 1)}"
  let guardBitIndexFromLsb : BitVec sigWidth :=
    BitVec.ofNat sigWidth ((sigWidth - 1) - (targetSignificandWidth + 1))
  let out := out ++ s!"\nguardBitIndexFromLsb: {guardBitIndexFromLsb.toBitsStr} = nat:{guardBitIndexFromLsb.toNat}"
  -- | See that when we call 'shiftAmtPositive.zeroExtend sigWidth', there is
  -- a potential that shiftAmtPositive is wider than sigWidth.
  -- However, when we compute early underflow,
  let guardBitIndexFromLsbAdjusted : BitVec sigWidth :=
    guardBitIndexFromLsb + shiftAmtPositive.zeroExtend sigWidth
  let out := out ++ s!"\nguardBitIndexFromLsbAdjusted({guardBitIndexFromLsbAdjusted.toBitsStr})nat:{guardBitIndexFromLsbAdjusted.toNat} = guardBitIndexFromLsb({guardBitIndexFromLsb.toBitsStr})nat:{guardBitIndexFromLsb.toNat} + shiftAmtPositive({shiftAmtPositive.toBitsStr})nat:{shiftAmtPositive.toNat}"

  let guardBitMask : BitVec sigWidth := BitVec.oneHotBV guardBitIndexFromLsbAdjusted
  let out := out ++ s!"\nguardBitMask: {guardBitMask.toBitsStr}"
  let guardBit : Bool := (sigWithHidden &&& guardBitMask) ≠ 0#sigWidth
  let out := out ++ s!"\nguardBit: {guardBit} = {sigWithHidden.toBitsStr} &&& {guardBitMask.toBitsStr}"
  let stickyBitsMask : BitVec sigWidth := (BitVec.orderEncode guardBitIndexFromLsbAdjusted)
  let out := out ++ s!"\nstickyBitsMask: {stickyBitsMask.toBitsStr}"
  let stickyBits : BitVec sigWidth := (sigWithHidden &&& stickyBitsMask)
  let out := out ++ s!"\nstickyBits: {stickyBits.toBitsStr}"
  let stickyBit : Bool := stickyBits ≠ 0#sigWidth
  let out := out ++ s!"\nstickyBit: {stickyBit} = {sigWithHidden.toBitsStr} &&& {stickyBitsMask.toBitsStr}"

  let sigwithHiddenCleared : BitVec sigWidth :=
    sigWithHidden &&& (~~~(guardBitMask ||| stickyBitsMask))
  let out := out ++ s!"\nsigwithHiddenCleared: {sigwithHiddenCleared.toBitsStr} = {sigWithHidden.toBitsStr} &&& ~({guardBitMask.toBitsStr} ||| {stickyBitsMask.toBitsStr})"

  let lsbMask : BitVec sigWidth :=
     BitVec.oneHotBV (guardBitIndexFromLsbAdjusted + 1#sigWidth)
  let out := out ++ s!"\nlsbMask: {lsbMask.toBitsStr}"

  let isEven : Bool := sigWithHidden &&& lsbMask = 0#sigWidth
  let out := out ++ s!"\nisEven: {isEven} = {sigWithHidden.toBitsStr} &&& {lsbMask.toBitsStr}"
  let shouldRoundUp := roundingDecision
    (mode := mode)
    (sign := inUf.sign)
    (significandEven := isEven)
    (guardBit := guardBit)
    (stickyBit := stickyBit)
    (_exact := false)
  let out := out ++ s!"\nshouldRoundUp: {shouldRoundUp}"
  let out := if shouldRoundUp then
    out ++ s!"\nroundedTargetSigWithHidden = sigwithHiddenCleared({sigwithHiddenCleared.toBitsStr}) + lsbMask({lsbMask.toBitsStr})"
  else
    out ++ s!"\nroundedTargetSigWithHidden = sigwithHiddenCleared({sigwithHiddenCleared.toBitsStr})"
  let sigDidOverflow_RoundedTargetSigWithHidden : BitVec (sigWidth + 1) :=
    if shouldRoundUp then
      if sigwithHiddenCleared = 0#sigWidth && lsbMask = 0#sigWidth then
        BitVec.oneHotBV (w := sigWidth + 1) (sigWidth)
      else
        sigwithHiddenCleared.zeroExtend (sigWidth + 1) + lsbMask.zeroExtend (sigWidth + 1)
    else
      sigwithHiddenCleared.zeroExtend (sigWidth + 1)

  let sigDidOverflow : Bool :=
    sigDidOverflow_RoundedTargetSigWithHidden.msb

  let roundedTargetSigWithHidden : BitVec sigWidth :=
    sigDidOverflow_RoundedTargetSigWithHidden.setWidth sigWidth

  let out := out ++ s!"\nroundedTargetSigWithHidden: {roundedTargetSigWithHidden.toBitsStr} = nat:{roundedTargetSigWithHidden.toNat}"
  let out := out ++ s!"\nsigDidOverflow: {sigDidOverflow}"

  let roundedTargetSigWithHiddenOverflowAdjusted : BitVec sigWidth :=
    if sigDidOverflow then
      BitVec.leadingOne sigWidth
    else
      roundedTargetSigWithHidden
  let out := out ++ s!"\nroundedTargetSigWithHiddenOverflowAdjusted: {roundedTargetSigWithHiddenOverflowAdjusted.toBitsStr} = nat:{roundedTargetSigWithHiddenOverflowAdjusted.toNat}"

  let roundedExpExtended : BitVec (expWidth + 1) :=
    if sigDidOverflow then
      exp.signExtend (expWidth + 1) + 1#(expWidth + 1)
    else
      exp.signExtend (expWidth + 1)

  let out := out ++ s!"\nroundedExpExtended: {roundedExpExtended.toBitsStr} = int:{roundedExpExtended.toInt}"
  -- I find this width stuff confusing, which width should we use?
  -- have : expWidth ≥ exponentWidth targetExponentWidth targetSignificandWidth := by grind
  let maxNormalExpBV : BitVec (expWidth + 1) :=
    BitVec.ofInt (expWidth + 1) (maxNormalExp targetExponentWidth)
  let lateOverflow : Bool :=
    maxNormalExpBV.slt roundedExpExtended
  let out := out ++ s!"\nlate overflow: {lateOverflow} = roundedExpExtended({roundedExpExtended.toBitsStr}=int:{roundedExpExtended.toInt}) > maxNormalExpBV({maxNormalExpBV.toBitsStr}=int:{maxNormalExpBV.toInt})"
  -- let subnormalExpBV : BitVec (expWidth) := BitVec.ofInt (expWidth) (subnormalExp targetExponentWidth)
  -- let minSubnormalExpMinusOneBV : BitVec (expWidth + 1) :=
  --   BitVec.ofInt (expWidth + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth - 1)
  let minSubnormalExpBV : BitVec (expWidth + 1) :=
    BitVec.ofInt (expWidth + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth)
  let lateUnderflow : Bool :=
    roundedExpExtended.slt minSubnormalExpBV
    -- (roundedExpExtended = minSubnormalExpMinusOneBV) && !shouldRoundUp
  let out := out ++ s!"\nlateUnderflow: {lateUnderflow} = roundedExpExtended({roundedExpExtended.toBitsStr}=int:{roundedExpExtended.toInt}) < minSubnormalExpBV: {minSubnormalExpBV.toBitsStr} = int:{minSubnormalExpBV.toInt}"
  -- let out := out ++ s!"\nlateUnderflow: {lateUnderflow} = (roundedExpExtended({roundedExpExtended.toBitsStr}=int:{roundedExpExtended.toInt}) = minSubnormalExpMinusOneBV({minSubnormalExpMinusOneBV.toBitsStr}=int:{minSubnormalExpMinusOneBV.toInt}) - 1) && !shouldRoundUp({shouldRoundUp})"
  -- let out := out ++ s!"\nlate underflow: {lateUnderflow} = roundedExp({roundedExp.toBitsStr}=int:{roundedExp.toInt}) < subnormalExpBV({subnormalExpBV.toBitsStr}=int:{subnormalExpBV.toInt})"
  let underflow : Bool := lateUnderflow || earlyUnderflow
  let out := out ++ s!"\nunderflow: {underflow} = lateUnderflow({lateUnderflow}) || earlyUnderflow({earlyUnderflow})"
  let overflow : Bool := lateOverflow || earlyOverflow
  let out := out ++ s!"\noverflow: {overflow} = lateOverflow({lateOverflow}) || earlyOverflow({earlyOverflow})"

  let roundedClampedExpExtended : BitVec (expWidth + 1) :=
    if lateOverflow then
      BitVec.ofInt (expWidth + 1) (maxNormalExp targetExponentWidth)
    else if lateUnderflow then
      BitVec.ofInt (expWidth + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth)
    else
      roundedExpExtended
  let out := out ++ s!"\nroundedClampedExpExtended: {roundedClampedExpExtended.toBitsStr} = int:{roundedClampedExpExtended.toInt}"
  let finalExp := roundedClampedExpExtended.truncate (exponentWidth targetExponentWidth targetSignificandWidth)
  let out := out ++ s!"\nfinalExp: {finalExp.toBitsStr} = int:{finalExp.toInt}"
  let finalSigTruncated := roundedTargetSigWithHiddenOverflowAdjusted.extractMsb' 0 (targetSignificandWidth + 1)
  let out := out ++ s!"\nfinalSigTruncated: {finalSigTruncated.toBitsStr} = nat:{finalSigTruncated.toNat}"
  let finalNumber : UnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    { sign := inUf.sign,
      ex := finalExp,
      sig := finalSigTruncated
    }
  let out := out ++ s!"\nfinalNumber: {repr finalNumber} | (Q): {finalNumber.toRat}"
  -- | TODO: I don't fully understand the special cases
  let result := rounderSpecialCases
    (roundingMode := mode)
    (roundedResult := finalNumber)
    (overflow := overflow)
    (underflow := underflow)
    (isZero := inUf.isZero)
  let out := out ++ s!"\nresult: {repr result} | (Q): {repr result.toExtRat}"
  (result, out)


/--
The core rounding function, that rounds an `UnpackedFloat` to the target exponent and significand widths,
-/
@[bv_normalize]
def UnpackedFloat.round {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
  (inUf : UnpackedFloat expWidth sigWidth)
  (mode : RoundingMode) :
  EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  -- round a normalized, normal float.
  let exp : BitVec expWidth := inUf.ex

  let targetMinNormalExp : BitVec expWidth :=
    BitVec.ofInt expWidth (minNormalExp targetExponentWidth)

  let earlyOverflow : Bool := exp.sgt (BitVec.ofInt expWidth (maxNormalExp targetExponentWidth))
  -- early underflow:
  let earlyUnderflow : Bool := exp.slt (BitVec.ofInt expWidth (minSubnormalExp targetExponentWidth targetSignificandWidth - 1))

  -- force exponent to be at least min normal exponent.
  let expGeMin :=
    if exp.slt targetMinNormalExp then
      targetMinNormalExp
    else
      exp

  -- how much to shift 'sig' by.
  let shiftAmtPositive := expGeMin - exp
  -- have : shiftAmtPositive.toInt ≥ 0 := AxRoundNormal
  -- have : shiftAmtPositive.toNat = shiftAmtPositive.toInt := AxRoundNormal
  -- have : exp.toInt + shiftAmtPositive.toInt = expGeMin.toInt := AxRoundNormal

  let sigWithHidden : BitVec sigWidth := inUf.sig

  -- in inf precision, we want to take:
  --                ↓ guard
  --  1 . a b c d e f g h ... * 2^exp
  --  ============↑ (6 bits of precision)
  -- suppose we exceed by 3 bits, so shiftAmt = 3.

  -- and convert to target precision:
  --                  ↓ guard
  --  0 . 0 0 0 1 a b c d e f g h * 2^exp + 2^shiftAmt | to make 'exp + shiftAmt >= minNormalExp'.
  --  ==============↑ (6 bits of precision)
  -- (sigWidth - 1) - (targetSignificandWidth - 1) -
  -- let targetSigWithHidden : BitVec (targetSignificandWidth + 1) :=
  --   sigWithHidden.extractMsb' 0 (targetSignificandWidth + 1)
  -- to grab the bit *after* w bits, it's the bit x[w].
  -- we want the bit *after* targetSignificandWidth + 1, i.e., bit at index targetSignificandWidth + 1.
  let guardBitIndexFromLsb : BitVec sigWidth :=
    BitVec.ofNat sigWidth ((sigWidth - 1) - (targetSignificandWidth + 1))
  -- | See that when we call 'shiftAmtPositive.zeroExtend sigWidth', there is
  -- a potential that shiftAmtPositive is wider than sigWidth.
  -- However, when we compute early underflow,
  let guardBitIndexFromLsbAdjusted : BitVec sigWidth :=
    guardBitIndexFromLsb + shiftAmtPositive.zeroExtend sigWidth

  let guardBitMask : BitVec sigWidth := BitVec.oneHotBV guardBitIndexFromLsbAdjusted
  let guardBit : Bool := (sigWithHidden &&& guardBitMask) ≠ 0#sigWidth
  let stickyBitsMask : BitVec sigWidth := (BitVec.orderEncode guardBitIndexFromLsbAdjusted)
  let stickyBits : BitVec sigWidth := (sigWithHidden &&& stickyBitsMask)
  let stickyBit : Bool := stickyBits ≠ 0#sigWidth

  let sigwithHiddenCleared : BitVec sigWidth :=
    sigWithHidden &&& (~~~(guardBitMask ||| stickyBitsMask))

  let lsbMask : BitVec sigWidth :=
     BitVec.oneHotBV (guardBitIndexFromLsbAdjusted + 1#sigWidth)

  let isEven : Bool := sigWithHidden &&& lsbMask = 0#sigWidth
  let shouldRoundUp := roundingDecision
    (mode := mode)
    (sign := inUf.sign)
    (significandEven := isEven)
    (guardBit := guardBit)
    (stickyBit := stickyBit)
    (_exact := false)
  let sigDidOverflow_RoundedTargetSigWithHidden : BitVec (sigWidth + 1) :=
    if shouldRoundUp then
      if sigwithHiddenCleared = 0#sigWidth && lsbMask = 0#sigWidth then
        BitVec.oneHotBV (w := sigWidth + 1) (sigWidth)
      else
        sigwithHiddenCleared.zeroExtend (sigWidth + 1) + lsbMask.zeroExtend (sigWidth + 1)
    else
      sigwithHiddenCleared.zeroExtend (sigWidth + 1)

  let sigDidOverflow : Bool :=
    sigDidOverflow_RoundedTargetSigWithHidden.msb

  let roundedTargetSigWithHidden : BitVec sigWidth :=
    sigDidOverflow_RoundedTargetSigWithHidden.setWidth sigWidth


  let roundedTargetSigWithHiddenOverflowAdjusted : BitVec sigWidth :=
    if sigDidOverflow then
      BitVec.leadingOne sigWidth
    else
      roundedTargetSigWithHidden

  let roundedExpExtended : BitVec (expWidth + 1) :=
    if sigDidOverflow then
      exp.signExtend (expWidth + 1) + 1#(expWidth + 1)
    else
      exp.signExtend (expWidth + 1)

  -- I find this width stuff confusing, which width should we use?
  -- have : expWidth ≥ exponentWidth targetExponentWidth targetSignificandWidth := by grind
  let maxNormalExpBV : BitVec (expWidth + 1) :=
    BitVec.ofInt (expWidth + 1) (maxNormalExp targetExponentWidth)
  let lateOverflow : Bool :=
    maxNormalExpBV.slt roundedExpExtended
  -- let subnormalExpBV : BitVec (expWidth) := BitVec.ofInt (expWidth) (subnormalExp targetExponentWidth)
  -- let minSubnormalExpMinusOneBV : BitVec (expWidth + 1) :=
  --   BitVec.ofInt (expWidth + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth - 1)
  let minSubnormalExpBV : BitVec (expWidth + 1) :=
    BitVec.ofInt (expWidth + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth)
  let lateUnderflow : Bool :=
    roundedExpExtended.slt minSubnormalExpBV
    -- (roundedExpExtended = minSubnormalExpMinusOneBV) && !shouldRoundUp
  -- let out := out ++ s!"\nlateUnderflow: {lateUnderflow} = (roundedExpExtended({roundedExpExtended.toBitsStr}=int:{roundedExpExtended.toInt}) = minSubnormalExpMinusOneBV({minSubnormalExpMinusOneBV.toBitsStr}=int:{minSubnormalExpMinusOneBV.toInt}) - 1) && !shouldRoundUp({shouldRoundUp})"
  -- let out := out ++ s!"\nlate underflow: {lateUnderflow} = roundedExp({roundedExp.toBitsStr}=int:{roundedExp.toInt}) < subnormalExpBV({subnormalExpBV.toBitsStr}=int:{subnormalExpBV.toInt})"
  let underflow : Bool := lateUnderflow || earlyUnderflow
  let overflow : Bool := lateOverflow || earlyOverflow

  let roundedClampedExpExtended : BitVec (expWidth + 1) :=
    if lateOverflow then
      maxNormalExpBV
    else if lateUnderflow then
      minSubnormalExpBV
    else
      roundedExpExtended
  let finalExp := roundedClampedExpExtended.truncate (exponentWidth targetExponentWidth targetSignificandWidth)
  let finalSigTruncated := roundedTargetSigWithHiddenOverflowAdjusted.extractMsb' 0 (targetSignificandWidth + 1)
  let finalNumber : UnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    { sign := inUf.sign,
      ex := finalExp,
      sig := finalSigTruncated
    }
  -- | TODO: I don't fully understand the special cases
  let result := rounderSpecialCases
    (roundingMode := mode)
    (roundedResult := finalNumber)
    (overflow := overflow)
    (underflow := underflow)
    (isZero := inUf.isZero)
  result

-- theorem BitVec.toInt_sub_eq_toInt_sub_toInt_of_le (a b : BitVec w) (h : b.sle a) :
--     (a - b).toInt = a.toInt - b.toInt := by
--   simp
--   have : b.toInt ≤ a.toInt := by simp [BitVec.sle] at h; grind only
--   apply Int.bmod_eq_of_le
--   · simp
--     grind
--   · simp
--     have ha := BitVec.toInt_le (x := a)
--     have hb := BitVec.toInt_lt (x := b)
--     have ha' := BitVec.le_two_mul_toInt (x := a)
--     have hb' := BitVec.le_two_mul_toInt (x := b)
--     rcases w with rfl | w
--     · simp; grind only
--     · simp [Int.pow_succ]
--       have : ((2 : Int) ^ w * 2 + 1 ) / 2 = 2 ^ w := by sorry
--       rw [this]
--       simp [Int.pow_succ] at ha hb ha' hb'
--       have : - 2 ^ w ≤ b.toInt := by grind

--       grind

/--
The core rounding function,
that rounds an `UnpackedFloat` to the target exponent and significand widths.
-/
@[bv_normalize]
def UnpackedFloat.proofRound {expWidth sigWidth : Nat}
  {targetExponentWidth targetSignificandWidth : Nat}
  (inUf : UnpackedFloat expWidth sigWidth)
  (hTargetExponentWidth2 : exponentWidth targetExponentWidth sigWidth ≤ expWidth)
  (hSigWidth : targetSignificandWidth + 2 ≤ sigWidth)
  (hExpWidth : 0 < expWidth)
  (mode : RoundingMode) :
  EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  -- round a normalized, normal float.
  have hTargetExponentWidth : targetExponentWidth ≤ expWidth := by
    grind [expWidth_le_exponentWidth]


  let exp : BitVec expWidth := inUf.ex

  let targetMinNormalExp : BitVec expWidth :=
    BitVec.ofInt expWidth (minNormalExp targetExponentWidth)

  let hTargetMinNormalExp : targetMinNormalExp.toInt = minNormalExp targetExponentWidth := by
    unfold targetMinNormalExp
    apply PackedFloat.toInt_ofInt_minNormalExp_eq_of_le (s := sigWidth)
    exact hTargetExponentWidth2

  let earlyOverflow : Bool := exp.sgt (BitVec.ofInt expWidth (maxNormalExp targetExponentWidth))
  let hEarlyOverflow : earlyOverflow =
    decide (maxNormalExp targetExponentWidth < exp.toInt) := by
    unfold earlyOverflow
    rw [BitVec.sgt, BitVec.slt_eq_decide]
    rw [PackedFloat.toInt_ofInt_maxNormalExp_eq_of_le (s := sigWidth)]
    grind only

  -- early underflow:
  let earlyUnderflow : Bool := exp.slt (BitVec.ofInt expWidth (minSubnormalExp targetExponentWidth targetSignificandWidth - 1))
  let hEarlyUnderflow : earlyUnderflow =
      decide (exp < minSubnormalExp targetExponentWidth targetSignificandWidth - 1) := by
      simp only [earlyUnderflow, BitVec.slt]
      sorry
  -- force exponent to be at least min normal exponent.
  let expGeMin :=
    if exp.slt targetMinNormalExp then
      targetMinNormalExp
    else
      exp
  let hExpGeMin : expGeMin.toInt = max targetMinNormalExp.toInt exp.toInt := by
    simp [expGeMin]
    rw [Int.max_def]
    simp [BitVec.slt]
    grind only [BitVec.toInt_inj, #87550518d2ea581d]

  -- how much to shift 'sig' by.
  let shiftAmtPositive := expGeMin - exp

  let hShiftAmtPositive1 : shiftAmtPositive.toInt = expGeMin.toInt - exp.toInt := by
    simp only [shiftAmtPositive]
    rw [BitVec.toInt_sub_of_not_ssubOverflow]
    sorry

  -- | this needs an even more complex bound.
  let hShiftAmtPositive2 : shiftAmtPositive.toNat = expGeMin.toInt - exp.toInt := by sorry
  -- have : shiftAmtPositive.toInt ≥ 0 := AxRoundNormal
  -- have : shiftAmtPositive.toNat = shiftAmtPositive.toInt := AxRoundNormal
  -- have : exp.toInt + shiftAmtPositive.toInt = expGeMin.toInt := AxRoundNormal

  let sigWithHidden : BitVec sigWidth := inUf.sig

  -- in inf precision, we want to take:
  --                ↓ guard
  --  1 . a b c d e f g h ... * 2^exp
  --  ============↑ (6 bits of precision)
  -- suppose we exceed by 3 bits, so shiftAmt = 3.

  -- and convert to target precision:
  --                  ↓ guard
  --  0 . 0 0 0 1 a b c d e f g h * 2^exp + 2^shiftAmt | to make 'exp + shiftAmt >= minNormalExp'.
  --  ==============↑ (6 bits of precision)
  -- (sigWidth - 1) - (targetSignificandWidth - 1) -
  -- let targetSigWithHidden : BitVec (targetSignificandWidth + 1) :=
  --   sigWithHidden.extractMsb' 0 (targetSignificandWidth + 1)
  -- to grab the bit *after* w bits, it's the bit x[w].
  -- we want the bit *after* targetSignificandWidth + 1, i.e., bit at index targetSignificandWidth + 1.
  let guardBitIndexFromLsb : BitVec sigWidth :=
    BitVec.ofNat sigWidth ((sigWidth - 1) - (targetSignificandWidth + 1))
  -- | See that when we call 'shiftAmtPositive.zeroExtend sigWidth', there is
  -- a potential that shiftAmtPositive is wider than sigWidth.
  -- However, when we compute early underflow,
  let guardBitIndexFromLsbAdjusted : BitVec sigWidth :=
    guardBitIndexFromLsb + shiftAmtPositive.zeroExtend sigWidth
  -- TODO: figure out what to say about 'guardBitIndexFromLsb'?
  let guardBitMask : BitVec sigWidth := BitVec.oneHotBV guardBitIndexFromLsbAdjusted
  let guardBit : Bool := (sigWithHidden &&& guardBitMask) ≠ 0#sigWidth
  -- TODO: guardBit ↔ ¬ isLower?
  let stickyBitsMask : BitVec sigWidth := (BitVec.orderEncode guardBitIndexFromLsbAdjusted)
  let stickyBits : BitVec sigWidth := (sigWithHidden &&& stickyBitsMask)
  let stickyBit : Bool := stickyBits ≠ 0#sigWidth
  -- TODO: guardbit => (stikyBit ↔ tieBreak)?
  let sigwithHiddenCleared : BitVec sigWidth :=
    sigWithHidden &&& (~~~(guardBitMask ||| stickyBitsMask))

  let lsbMask : BitVec sigWidth :=
     BitVec.oneHotBV (guardBitIndexFromLsbAdjusted + 1#sigWidth)

  let isEven : Bool := sigWithHidden &&& lsbMask = 0#sigWidth
  -- TODO: isEven ↔ isEven?
  let shouldRoundUp := roundingDecision
    (mode := mode)
    (sign := inUf.sign)
    (significandEven := isEven)
    (guardBit := guardBit)
    (stickyBit := stickyBit)
    (_exact := false)
  -- TODO: shouldRoundUp ↔ SMT-LIB shouldRoundUp?

  let sigDidOverflow_RoundedTargetSigWithHidden : BitVec (sigWidth + 1) :=
    if shouldRoundUp then
      if sigwithHiddenCleared = 0#sigWidth && lsbMask = 0#sigWidth then
        BitVec.oneHotBV (w := sigWidth + 1) (sigWidth)
      else
        sigwithHiddenCleared.zeroExtend (sigWidth + 1) + lsbMask.zeroExtend (sigWidth + 1)
    else
      sigwithHiddenCleared.zeroExtend (sigWidth + 1)

  let sigDidOverflow : Bool :=
    sigDidOverflow_RoundedTargetSigWithHidden.msb

  let roundedTargetSigWithHidden : BitVec sigWidth :=
    sigDidOverflow_RoundedTargetSigWithHidden.setWidth sigWidth


  let roundedTargetSigWithHiddenOverflowAdjusted : BitVec sigWidth :=
    if sigDidOverflow then
      BitVec.leadingOne sigWidth
    else
      roundedTargetSigWithHidden
  -- lower = upper + 1.
  let roundedExpExtended : BitVec (expWidth + 1) :=
    if sigDidOverflow then
      exp.signExtend (expWidth + 1) + 1#(expWidth + 1)
    else
      exp.signExtend (expWidth + 1)

  -- TODO: upper = lower + 1
  -- I find this width stuff confusing, which width should we use?
  -- have : expWidth ≥ exponentWidth targetExponentWidth targetSignificandWidth := by grind
  let maxNormalExpBV : BitVec (expWidth + 1) :=
    BitVec.ofInt (expWidth + 1) (maxNormalExp targetExponentWidth)
  let lateOverflow : Bool :=
    maxNormalExpBV.slt roundedExpExtended
  -- let subnormalExpBV : BitVec (expWidth) := BitVec.ofInt (expWidth) (subnormalExp targetExponentWidth)
  -- let minSubnormalExpMinusOneBV : BitVec (expWidth + 1) :=
  --   BitVec.ofInt (expWidth + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth - 1)
  let minSubnormalExpBV : BitVec (expWidth + 1) :=
    BitVec.ofInt (expWidth + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth)
  let lateUnderflow : Bool :=
    roundedExpExtended.slt minSubnormalExpBV
    -- (roundedExpExtended = minSubnormalExpMinusOneBV) && !shouldRoundUp
  -- let out := out ++ s!"\nlateUnderflow: {lateUnderflow} = (roundedExpExtended({roundedExpExtended.toBitsStr}=int:{roundedExpExtended.toInt}) = minSubnormalExpMinusOneBV({minSubnormalExpMinusOneBV.toBitsStr}=int:{minSubnormalExpMinusOneBV.toInt}) - 1) && !shouldRoundUp({shouldRoundUp})"
  -- let out := out ++ s!"\nlate underflow: {lateUnderflow} = roundedExp({roundedExp.toBitsStr}=int:{roundedExp.toInt}) < subnormalExpBV({subnormalExpBV.toBitsStr}=int:{subnormalExpBV.toInt})"
  let underflow : Bool := lateUnderflow || earlyUnderflow
  let overflow : Bool := lateOverflow || earlyOverflow

  let roundedClampedExpExtended : BitVec (expWidth + 1) :=
    if lateOverflow then
      maxNormalExpBV
    else if lateUnderflow then
      minSubnormalExpBV
    else
      roundedExpExtended
  let finalExp := roundedClampedExpExtended.truncate (exponentWidth targetExponentWidth targetSignificandWidth)
  let finalSigTruncated := roundedTargetSigWithHiddenOverflowAdjusted.extractMsb' 0 (targetSignificandWidth + 1)
  let finalNumber : UnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    { sign := inUf.sign,
      ex := finalExp,
      sig := finalSigTruncated
    }
  -- | TODO: I don't fully understand the special cases
  let result := rounderSpecialCases
    (roundingMode := mode)
    (roundedResult := finalNumber)
    (overflow := overflow)
    (underflow := underflow)
    (isZero := inUf.isZero)
  result


/-- Round an EUnpacked float, by ignoring NaN and infinity. -/
def EUnpackedFloat.round {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
  (inEuf : EUnpackedFloat expWidth sigWidth)
  (mode : RoundingMode) :
  EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  if inEuf.isNumber then
    let inUf := inEuf.num
    UnpackedFloat.round (targetExponentWidth := targetExponentWidth) (targetSignificandWidth := targetSignificandWidth)
      inUf mode
  else if inEuf.isNaN then EUnpackedFloat.mkNaN
  else EUnpackedFloat.mkInfinity inEuf.sign

/--
Prove that the debug mode round function is equal to the core round function.
-/
theorem debugRound_eq_round {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
  (inUf : UnpackedFloat expWidth sigWidth)
  (mode : RoundingMode) :
  (UnpackedFloat.debugRound (targetExponentWidth := targetExponentWidth) (targetSignificandWidth := targetSignificandWidth)
    inUf mode).1 =
  UnpackedFloat.round (targetExponentWidth := targetExponentWidth) (targetSignificandWidth := targetSignificandWidth)
    inUf mode := rfl

-- TODO: these are expensive checks, so move them into a separate file.
def checkRoundCorrect (EUnpacked SUnpackedNoHidden : Nat) (EOut SOutNoHidden : Nat) (mode : RoundingMode) : IO Bool := do
  let mut outError : String := ""
  let mut nsucceeded : Nat := 0
  let mut nfailed : Nat := 0

  for originalPacked in mkPackedFloats EUnpacked SUnpackedNoHidden do
    let originalEUnpacked := originalPacked.unpack
    if ! originalEUnpacked.isNumber then continue

    let originalUnpacked := originalEUnpacked.num
    let originalNormalized := originalUnpacked.normalize
    let (outputRoundedEUnpacked, log) :=
      UnpackedFloat.debugRound (targetExponentWidth := EOut) (targetSignificandWidth := SOutNoHidden)
        originalNormalized mode
    let outputRoundedPacked := outputRoundedEUnpacked.pack

    -- check that I produce a result that packs properly.
    if ! outputRoundedEUnpacked.pack.unpack.pack.equal_denotation outputRoundedEUnpacked.pack then
      let err : String := ""
      let err := err ++ s!"\nFailed packing roundtrip ❌ | original {repr originalEUnpacked}"
      let err := err ++ s!"\n  original (packed) {repr originalPacked}"
      let err := err ++ s!"\n  output rounded (eunpacked) {repr outputRoundedEUnpacked}"
      let err := err ++ s!"\n  output rounded (eunpacked.Q) {repr outputRoundedEUnpacked.toExtRat}"
      let err := err ++ s!"\n  output rounded (unpacked(packed(eunpacked))) {repr outputRoundedEUnpacked.pack.unpack}"
      let err := err ++ s!"\n  output rounded (unpacked(packed(eunpacked)).Q) {repr outputRoundedEUnpacked.pack.unpack.toExtRat}"
      IO.println err
      outError := err
      nfailed := nfailed + 1
      continue

    let expectedPacked : PackedFloat EOut SOutNoHidden :=
       originalPacked.toEFixed.round (exWidth := EOut) (sigWidth := SOutNoHidden) mode
    let expectedEUnpacked := expectedPacked.unpack
    if outputRoundedPacked.equal_denotation expectedPacked then
      IO.println s!"Succeeded ✅ | original {repr originalEUnpacked}"
      nsucceeded := nsucceeded + 1
    else
      let err : String := ""
      let err := err ++ s!"\nFailed ❌ | original {repr originalEUnpacked}"
      let err := err ++ s!"\n  original (packed) {repr originalPacked}"
      let err := err ++ s!"\n  original (Q) {repr originalPacked.toRat?}"
      let err := err ++ s!"\n  --"
      let err := err ++ s!"\n  output rounded (packed) {repr outputRoundedPacked}"
      let err := err ++ s!"\n  output rounded (eunpacked) {repr outputRoundedEUnpacked}"
      let err := err ++ s!"\n  output rounded (Q) {repr outputRoundedEUnpacked.toExtRat}"
      let err := err ++ s!"\n  --"
      let err := err ++ s!"\n  expected (packed) {repr expectedPacked}"
      let err := err ++ s!"\n  expected (Q) {repr expectedPacked.toExtRat}"
      let err := err ++ s!"\n  expected (eunpacked) {repr expectedEUnpacked}"
      let err := err ++ s!"\n\n{log}"
      IO.println err
      outError := err
      nfailed := nfailed + 1
  if nfailed = 0 then
    IO.println "All succeeded ✅"
  else
    -- | this is fixed point, with two digits of precision.
    let fracSuccess : Float := (nsucceeded.toFloat * 100.0) / ((nsucceeded + nfailed).toFloat)
    throw (IO.Error.userError s!"({nsucceeded} succeeded / {nsucceeded + nfailed} total) ({fracSuccess}% succeeded) ({nfailed} failures) ❌\n{outError}")
  return nfailed = 0

-- TODO: these are expensive checks, so move them into a separate file.
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RNA
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RNA

-- TODO: these are expensive checks, so move them into a separa4 5 4 2.
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RNE
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RNE
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RNE

#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RTZ
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RTZ

/--
error: (383 succeeded / 384 total) (99.739583% succeeded) (1 failures) ❌

Failed ❌ | original { state := num, num := { sign := false, ex := 0xa#4, sig := 0x40#7 } }
  original (packed) { sign := +, ex := 0x0#2, sig := 0x01#6 }
  original (Q) some (1 : Rat)/64
  --
  output rounded (packed) { sign := +, ex := 0x0#2, sig := 0x0#4 }
  output rounded (eunpacked) { state := num, num := { sign := false, ex := 0xb#4, sig := 0x10#5 } }
  output rounded (Q) ExtRat.Number (1 : Rat)/32
  --
  expected (packed) { sign := +, ex := 0x0#2, sig := 0x1#4 }
  expected (Q) ExtRat.Number (1 : Rat)/16
  expected (eunpacked) { state := num, num := { sign := false, ex := 0xc#4, sig := 0x10#5 } }


--- rounding: { sign := false, ex := 0xa#4, sig := 0x40#7 } ---
  val (Q): 1/64 = sig(0b1000000=nat:64)) * 2 ** exp:([0b1010=int:-6] - (6))
exp: 0b1010 = int:-6
targetMinNormalExp: 0b0000 = int:0
maxNormalExp: 1
earlyOverflow: false
minSubnormalExp: -5
earlyUnderflow: false
expGeMin: 0b0000 = int:0
shiftAmtPositive: 0b0110 = int:6 = nat:6
sigWithHidden: 0b1000000 = nat:64
guardBitIndexFromLsb: (sigWidth(7) - 1)  - (targetSignificandWidth(4) + 1) = 1
guardBitIndexFromLsb: 0b0000001 = nat:1
guardBitIndexFromLsbAdjusted(0b0000111)nat:7 = guardBitIndexFromLsb(0b0000001)nat:1 + shiftAmtPositive(0b0110)nat:6
guardBitMask: 0b0000000
guardBit: false = 0b1000000 &&& 0b0000000
stickyBitsMask: 0b1111111
stickyBits: 0b1000000
stickyBit: true = 0b1000000 &&& 0b1111111
sigwithHiddenCleared: 0b0000000 = 0b1000000 &&& ~(0b0000000 ||| 0b1111111)
lsbMask: 0b0000000
isEven: true = 0b1000000 &&& 0b0000000
shouldRoundUp: true
roundedTargetSigWithHidden = sigwithHiddenCleared(0b0000000) + lsbMask(0b0000000)
roundedTargetSigWithHidden: 0b0000000 = nat:0
sigDidOverflow: true
roundedTargetSigWithHiddenOverflowAdjusted: 0b1000000 = nat:64
roundedExpExtended: 0b11011 = int:-5
late overflow: false = roundedExpExtended(0b11011=int:-5) > maxNormalExpBV(0b00001=int:1)
lateUnderflow: false = roundedExpExtended(0b11011=int:-5) < minSubnormalExpBV: 0b11011 = int:-5
underflow: false = lateUnderflow(false) || earlyUnderflow(false)
overflow: false = lateOverflow(false) || earlyOverflow(false)
roundedClampedExpExtended: 0b11011 = int:-5
finalExp: 0b1011 = int:-5
finalSigTruncated: 0b10000 = nat:16
finalNumber: { sign := false, ex := 0xb#4, sig := 0x10#5 } | (Q): 1/32
result: { state := num, num := { sign := false, ex := 0xb#4, sig := 0x10#5 } } | (Q): ExtRat.Number (1 : Rat)/32
-/
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 2 6 2 4 .RTP
/--
error: (957 succeeded / 960 total) (99.687500% succeeded) (3 failures) ❌

Failed ❌ | original { state := num, num := { sign := false, ex := 0x16#5, sig := 0x30#6 } }
  original (packed) { sign := +, ex := 0x0#4, sig := 0x03#5 }
  original (Q) some (3 : Rat)/2048
  --
  output rounded (packed) { sign := +, ex := 0x0#4, sig := 0x0#2 }
  output rounded (eunpacked) { state := num, num := { sign := false, ex := 0x17#5, sig := 0x4#3 } }
  output rounded (Q) ExtRat.Number (1 : Rat)/512
  --
  expected (packed) { sign := +, ex := 0x0#4, sig := 0x1#2 }
  expected (Q) ExtRat.Number (1 : Rat)/256
  expected (eunpacked) { state := num, num := { sign := false, ex := 0x18#5, sig := 0x4#3 } }


--- rounding: { sign := false, ex := 0x16#5, sig := 0x30#6 } ---
  val (Q): 3/2048 = sig(0b110000=nat:48)) * 2 ** exp:([0b10110=int:-10] - (5))
exp: 0b10110 = int:-10
targetMinNormalExp: 0b11010 = int:-6
maxNormalExp: 7
earlyOverflow: false
minSubnormalExp: -9
earlyUnderflow: false
expGeMin: 0b11010 = int:-6
shiftAmtPositive: 0b00100 = int:4 = nat:4
sigWithHidden: 0b110000 = nat:48
guardBitIndexFromLsb: (sigWidth(6) - 1)  - (targetSignificandWidth(2) + 1) = 2
guardBitIndexFromLsb: 0b000010 = nat:2
guardBitIndexFromLsbAdjusted(0b000110)nat:6 = guardBitIndexFromLsb(0b000010)nat:2 + shiftAmtPositive(0b00100)nat:4
guardBitMask: 0b000000
guardBit: false = 0b110000 &&& 0b000000
stickyBitsMask: 0b111111
stickyBits: 0b110000
stickyBit: true = 0b110000 &&& 0b111111
sigwithHiddenCleared: 0b000000 = 0b110000 &&& ~(0b000000 ||| 0b111111)
lsbMask: 0b000000
isEven: true = 0b110000 &&& 0b000000
shouldRoundUp: true
roundedTargetSigWithHidden = sigwithHiddenCleared(0b000000) + lsbMask(0b000000)
roundedTargetSigWithHidden: 0b000000 = nat:0
sigDidOverflow: true
roundedTargetSigWithHiddenOverflowAdjusted: 0b100000 = nat:32
roundedExpExtended: 0b110111 = int:-9
late overflow: false = roundedExpExtended(0b110111=int:-9) > maxNormalExpBV(0b000111=int:7)
lateUnderflow: false = roundedExpExtended(0b110111=int:-9) < minSubnormalExpBV: 0b110111 = int:-9
underflow: false = lateUnderflow(false) || earlyUnderflow(false)
overflow: false = lateOverflow(false) || earlyOverflow(false)
roundedClampedExpExtended: 0b110111 = int:-9
finalExp: 0b10111 = int:-9
finalSigTruncated: 0b100 = nat:4
finalNumber: { sign := false, ex := 0x17#5, sig := 0x4#3 } | (Q): 1/512
result: { state := num, num := { sign := false, ex := 0x17#5, sig := 0x4#3 } } | (Q): ExtRat.Number (1 : Rat)/512
-/
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RTP
/--
error: (957 succeeded / 960 total) (99.687500% succeeded) (3 failures) ❌

Failed ❌ | original { state := num, num := { sign := true, ex := 0x16#5, sig := 0x30#6 } }
  original (packed) { sign := -, ex := 0x0#4, sig := 0x03#5 }
  original (Q) some (-3 : Rat)/2048
  --
  output rounded (packed) { sign := -, ex := 0x0#4, sig := 0x0#2 }
  output rounded (eunpacked) { state := num, num := { sign := true, ex := 0x17#5, sig := 0x4#3 } }
  output rounded (Q) ExtRat.Number (-1 : Rat)/512
  --
  expected (packed) { sign := -, ex := 0x0#4, sig := 0x1#2 }
  expected (Q) ExtRat.Number (-1 : Rat)/256
  expected (eunpacked) { state := num, num := { sign := true, ex := 0x18#5, sig := 0x4#3 } }


--- rounding: { sign := true, ex := 0x16#5, sig := 0x30#6 } ---
  val (Q): -3/2048 = sig(0b110000=nat:48)) * 2 ** exp:([0b10110=int:-10] - (5))
exp: 0b10110 = int:-10
targetMinNormalExp: 0b11010 = int:-6
maxNormalExp: 7
earlyOverflow: false
minSubnormalExp: -9
earlyUnderflow: false
expGeMin: 0b11010 = int:-6
shiftAmtPositive: 0b00100 = int:4 = nat:4
sigWithHidden: 0b110000 = nat:48
guardBitIndexFromLsb: (sigWidth(6) - 1)  - (targetSignificandWidth(2) + 1) = 2
guardBitIndexFromLsb: 0b000010 = nat:2
guardBitIndexFromLsbAdjusted(0b000110)nat:6 = guardBitIndexFromLsb(0b000010)nat:2 + shiftAmtPositive(0b00100)nat:4
guardBitMask: 0b000000
guardBit: false = 0b110000 &&& 0b000000
stickyBitsMask: 0b111111
stickyBits: 0b110000
stickyBit: true = 0b110000 &&& 0b111111
sigwithHiddenCleared: 0b000000 = 0b110000 &&& ~(0b000000 ||| 0b111111)
lsbMask: 0b000000
isEven: true = 0b110000 &&& 0b000000
shouldRoundUp: true
roundedTargetSigWithHidden = sigwithHiddenCleared(0b000000) + lsbMask(0b000000)
roundedTargetSigWithHidden: 0b000000 = nat:0
sigDidOverflow: true
roundedTargetSigWithHiddenOverflowAdjusted: 0b100000 = nat:32
roundedExpExtended: 0b110111 = int:-9
late overflow: false = roundedExpExtended(0b110111=int:-9) > maxNormalExpBV(0b000111=int:7)
lateUnderflow: false = roundedExpExtended(0b110111=int:-9) < minSubnormalExpBV: 0b110111 = int:-9
underflow: false = lateUnderflow(false) || earlyUnderflow(false)
overflow: false = lateOverflow(false) || earlyOverflow(false)
roundedClampedExpExtended: 0b110111 = int:-9
finalExp: 0b10111 = int:-9
finalSigTruncated: 0b100 = nat:4
finalNumber: { sign := true, ex := 0x17#5, sig := 0x4#3 } | (Q): -1/512
result: { state := num, num := { sign := true, ex := 0x17#5, sig := 0x4#3 } } | (Q): ExtRat.Number (-1 : Rat)/512
-/
#guard_msgs(check error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RTN
