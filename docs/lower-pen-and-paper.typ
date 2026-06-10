#set document(title: "Correctness of the bit-blasted lower-rounding circuit", author: "fp.lean")
#set page(numbering: "1", margin: (x: 2.4cm, y: 2.6cm))
#set par(justify: true, leading: 0.62em)
#set text(size: 10.5pt, font: "New Computer Modern")
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
// Only number equations that are referenced (carry a label).
#show math.equation: it => {
  if it.block and it.has("label") { it } else {
    set math.equation(numbering: none)
    it
  }
}
#show heading: it => block(above: 1.1em, below: 0.6em)[#it]

#let Rel = $sans("Rel")$
#let lower = $sans("lower")$
#let upper = $sans("upper")$
#let embed = $v$
#let Number = $sans("Number")$
#let toRat = $sans("toRat")$
#let toRatp = $sans("toRat)'")$
#let sig = $sans("sig")$
#let ex = $sans("ex")$
#let sgn = $sans("sign")$
#let NaN = $sans("NaN")$
#let isNaN = $sans("isNaN")$
#let minNE = $e_min$
#let maxNE = $e_max$
#let minSE = $e_(min)^("sub")$
#let bRTZ = $sans("blastRoundTowardZero")$
#let bLN = $sans("blastLowerNonneg")$
#let bUN = $sans("blastUpperNonneg")$
#let bL = $sans("blastLower")$
#let bclr = $sans("blastClearSig")$
#let IsLawfulLower = $sans("IsLawfulLower")$
#let IsLawfulUpper = $sans("IsLawfulUpper")$
#let maxN = $sans("maxNormal")$
#let lf = "lawful lower"

// --- Status badges (Material palette: blue 800 = done, red 600 = to do) ---
#let cOk = rgb("#1565C0")
#let cNo = rgb("#E53935")
#let badge(col, label) = box(
  baseline: 0.15em, fill: col, inset: (x: 4pt, y: 1.5pt), radius: 2.5pt,
  text(fill: white, size: 7pt, weight: "bold", tracking: 0.3pt, label),
)
#let proved = badge(cOk, "PROVED")
#let todo = badge(cNo, "SORRY")

// Monospace with break opportunities at `_` and `.` so long Lean names wrap.
#let zwsp = "\u{200B}"
#let c(s) = raw(s.replace("_", "_" + zwsp).replace(".", "." + zwsp))

#align(center)[
  #text(17pt, weight: "bold")[Correctness of the bit-blasted lower-rounding circuit]
  #v(0.2em)
  #text(11pt)[A pen-and-paper proof, structured for mechanisation in Lean 4]
  #v(0.4em)
  #text(9.5pt, style: "italic")[Target file: `Fp/Theorems/UnpackedFloat/Round.lean` — theorem `UnpackedFloat.blastLower_Rel_smtLibLower`]
]

#v(0.6em)


== Correctness of lower (also upper)

Check that lower produces any floating point number.
This needs us to show that the result of lower can be packed.
ie, (lowerComputed r).pack.unpack = lowerComputed r under the conditions we call it.


Next, we show that 'lowerComputed r' is close enough to 'r'. That is, (a) `lowerComputed r <= r`
and (b) `r - 2^(-(s+2)) < lowerComputed r`.

From this, we will show that `lowerComputer r = lowr `r.

First, see that we must have that `lowerComputer r <= lower r`, since `lowerComputed r` is a lower bound on `r`,
and must be dominated by the greatest lower bound, which is `lower r`.
Next, we want to show that `lower r <= lowerComputed r`.

We start from `lowerComputer r <= r`.
We assume for contradiction that `lowerComputed r != lower r`.
Then, we must have that `lowerComputed r + 2^-(s+2) <= lower r`, 
from the 'discreteness lemma' for PackedFloat.
This then means that `lowerComputed r + 2^-(s+2) <= lower r <= r`.
This contradicts property (b), wher we show that `lowerComputed r` is at least `2^-(s+2)` away from `r`.
This proves `lower` correct.


== Correctness of upper

Upper follows the same strategy, adjusted for the incrementing the significand and whatnot.

== Correctness of isLowerHalf

In SMT-LIB, we define `isLowerHalf` as 

```
lowerHalf r := ExtendedNumber.smtLibEq (v.embed (v.lower r))  (ves.embed (ves.lower r))
```

We know that `r - 2^(-s+2) <= v.embed (v.lower r) <= r`,
and similarly, `r - 2^(-s+3) <= ves.embed (ves.lower r) <= r`.


== Correctness of isTieBreak


```
tieBreak r :=
  (v.embed (v.lower r) < ves.embed (ves.lower r)) =
  (ves.embed (ves.upper r) < (v.embed (v.upper r)))
```

== Correctness of isEvenLower


```
isEven := roundableIsEven_of_packedFloat.isEven
```


Once we know that 'lower' is correct, this follows since 'isEvenLower' just takes that bit of the 'lower'.
We just show that the value of the 'getLsbD' agrees.

== Correctess of isEvenHigher

We prove that in the case where the numberis not a tie, we know that 'isEvenHigher = !isEvenLower',
since the significands of adjacent numbers diifer by 1. For this, we need some predicate or something called 'PackedFloat.succ'
so we can prove properties about it.




