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

#block(inset: (left: 0.4em, right: 0.4em), [
  *Abstract.* We give a complete pen-and-paper proof that the bit-blasted
  rounding-towards-the-greatest-representable-value circuit `blastLower`
  computes a packed float that is `Rel`-equivalent to the SMT-LIB
  specification `lower` (the greatest representable float $≤ r$). The proof
  is organised so that each step maps directly onto a Lean lemma. We
  isolate the abstract interface we require of the specification side
  (`IsLawfulLower`, `lower`, `Rel`, the float ordering) in
  @sec:interface, treating those facts as a black box. The mathematical
  content — that bit-clearing implements truncation toward zero, and that
  truncation toward zero is the greatest representable lower bound — lives
  in @sec:normal, where we are careful about the exponent bounds that make
  the subnormal shift well-defined.
])

= Setup and notation <sec:setup>

== Formats and values

Fix two pairs of natural numbers. The *target format* $(e_p, s_p)$ describes
the packed floats we are rounding *into*; the *working format* $(e_u, s_u)$
describes the unpacked float we are rounding *from*. We write
$ "PF" := "PackedFloat" e_p s_p, wide "UF" := "UnpackedFloat" e_u s_u . $

An unpacked float $x ∈ "UF"$ carries a sign bit $x.sgn$, a signed exponent
bit-vector $x.ex ∈ "BitVec" e_u$, and a significand bit-vector
$x.sig ∈ "BitVec" s_u$. Its rational value (`UnpackedFloat.toRat'`, taken at
precision $p$) is
$
  x.toRat'(p) = (-1)^(x.sgn) dot x.sig."toNat" dot 2^(E(x,p)),
  wide E(x,p) = x.ex."toInt" - p ,
$ <eq:toRat>
where $E(x, p)$ is `UnpackedFloat.toExpInt`. Throughout we take the default
precision $p = s_u - 1$ and abbreviate $x.toRat' := x.toRat'(s_u - 1)$ and
$E(x) := E(x, s_u - 1)$. We say $x$ is *nonnegative* when $x.sgn = sans("false")$.

A packed float $f ∈ "PF"$ has a rational/extended value $f.toRat$ and an
extended-rational embedding $#embed (f) := f."toExtRat" ∈ overline(QQ)$,
where $overline(QQ) = QQ ∪ {plus.minus ∞, #NaN}$ is the type `ExtRat`. On
non-special floats $#embed (f) = #Number (f.toRat)$.

== The relevant constants

With $sans("bias")(e) = 2^(e-1) - 1$, recall (`Fp/Constants/Basic.lean`):
$
  #minNE (e) &= -(sans("bias")(e) - 1) && quad "(minimum normal exponent)" \
  #maxNE (e) &= sans("bias")(e) && quad "(maximum normal exponent)" \
  #minSE (e, s) &= #minNE (e) - s && quad "(minimum subnormal exponent)."
$ <eq:consts>
The last identity is `minSubnormalExp_eq` unfolded: $#minSE = (#minNE - 1) - (s - 1) = #minNE - s$.
We also use the *exponent width* $sans("exponentWidth")(e_p, s_p)$, the number
of bits needed to hold every exponent of the target format including
normalised subnormals; the standing hypothesis $sans("exponentWidth")(e_p,s_p) ≤ e_u$
guarantees the working format can name every target exponent.

== The specification: `lower`

For $r ∈ overline(QQ)$, the SMT-LIB greatest lower bound `smtLibLower.lower`
is defined by Hilbert choice,
$ #lower (r) := epsilon.alt thin x. thin #IsLawfulLower (r, x), $
where (`SmtLibSemantics.IsLawfulLower`)
$
  #IsLawfulLower (r, x) thick <==> thick #embed (x) ≤ r ∧ (∀ x'. thin #embed (x') ≤ r ⟹ x' ≤ x).
$ <eq:lawful>
That is, $x$ embeds below $r$ and is the $≤$-greatest such packed float, where
$≤$ is the float ordering (`PackedFloat.le`). The dual notion #IsLawfulUpper and
#upper are defined symmetrically with the inequalities reversed.

== The implementation: `blastLower`

The circuit (`Fp/UnpackedRound.lean`) is layered. The innermost piece,
$ #bRTZ (x) : "UnpackedFloat" e_u (s_p + 1), $
clears the guard and sticky bits of $x$ at the target precision and keeps the
top $s_p + 1$ significand bits; we analyse it in @sec:rtz. On top of it,
$
  #bLN (x) := cases(
    +0 & "if " sans("under")(x),
    #maxN _(e_u, s_p+1) & "else if " sans("over")(x),
    #bRTZ (x) & "otherwise,"
  )
$ <eq:bln>
where $sans("under")(x) := sans("blastIsUnderflowNonneg")(x)$ and
$sans("over")(x) := sans("blastIsEarlyOverflowNonneg")(x)$ are the early
under/overflow tests, returned as an `EUnpackedFloat` (an unpacked float
extended with $∞$/#NaN states). Finally, splitting on the sign,
$
  #bL (x) := cases(
    -((-x).#bUN) & "if " x.sgn = sans("true"),
    #bLN (x) & "otherwise,"
  )
$ <eq:blastlower>
where $#bUN$ is the analogous least-upper-bound circuit.

== The goal

The target relation `EUnpackedFloat.Rel` between $y : "EUnpackedFloat" e_u (s_p+1)$
and $f : "PF"$ is
$
  y #Rel f thick <==> thick &(y."state" = NaN ∧ f.isNaN) \
  ∨ thin &(y."state" = ∞ ∧ f."isInfinite" ∧ y.sgn = f.sgn) \
  ∨ thin &(y."state" = Number ∧ y."num".toRat'(s_p) = f.toRat ∧ y."num".sgn = f.sgn).
$ <eq:rel>
The theorem to prove (`UnpackedFloat.blastLower_Rel_smtLibLower`) is:

#block(stroke: 0.6pt + luma(60%), inset: 8pt, radius: 3pt, width: 100%)[
  *Theorem (Main).* Assume $2 < e_p$, $0 < s_p$, $s_p + 2 ≤ s_u$,
  $sans("exponentWidth")(e_p, s_p) ≤ e_u$, and that $x$ is normalised
  ($x."normalize" = x$). Then
  $ #bL (x) thin #Rel thin (#lower (#Number (x.toRat')) : "PF"). $
]

The standing hypotheses are used as follows. $0 < s_p$ and $2 < e_p$ make the
target format non-degenerate (so $#maxN$ is not #NaN and the bias is positive).
$sans("exponentWidth")(e_p, s_p) ≤ e_u$ lets every target exponent be named in
the working exponent width. $s_p + 2 ≤ s_u$ leaves room for a guard bit and a
sticky region below the retained $s_p + 1$ bits (this is what makes the
guard/sticky indexing in @sec:rtz well-typed and in-range). Normalisation
$x."normalize" = x$ pins down a *canonical* working representative, so
that "keep the top $s_p + 1$ bits" is value-faithful — without it, several
unpacked floats share a value and the bit-level truncation does not commute
with @eq:toRat.

= The abstract specification interface <sec:interface>

We never unfold the Hilbert choice in `lower`. Instead we use only the
following four facts about the specification and three facts about #Rel and
the ordering. In the mechanisation these are exactly the cited Lean lemmas;
for the paper they are the axioms of our argument.

#block(inset: (left: 1em))[
  #proved *(S1) Lawfulness* (`lsLawfulLower_smtLibLower`). For $0 < e_p$, $0 < s_p$ and
  any $r$, #h(0.3em) $#IsLawfulLower (r, #lower (r))$.

  #proved *(S2) Uniqueness* (`eq_of_IsLawfulLower_of_IsLawfulLower`). If $x, y : "PF"$
  are both non-#NaN and both satisfy $#IsLawfulLower (r, dot.c)$, then $x = y$.

  #proved *(S3) Non-#NaN* (`not_isNaN_lower_of_ne_NaN`). If $r ≠ #NaN$ then
  $#lower (r)$ is not #NaN.

  #proved *(S4) Negation duality* (`smtLibLower_eq_neg_smtLibUpper_neg`). For $r ≠ #NaN$,
  $ #lower (r) = -(#upper (-r)), $
  and dually $#upper (r) = -(#lower (-r))$ (`smtLibUpper_eq_neg_smtLibLower_neg`).
]

#block(inset: (left: 1em))[
  #proved *(R1) Number introduction* (`UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign`
  composed with `EUnpackedFloat.Rel_of_Rel_of_state_eq_Number`). If
  $y."state" = Number$, $y."num".toRat'(s_p) = f.toRat$ and
  $y."num".sgn = f.sgn$, then $y #Rel f$.

  #proved *(R2) Negation is functorial* (`EUnpackedFloat.neg_Rel_neg`). If $y #Rel f$
  then $(-y) #Rel (-f)$.

  #proved *(O1) Order reflection* (`PackedFloat.le_of_toExtRat'_le_toExtRat'`). For
  non-#NaN $f, g : "PF"$, if $#embed (f) ≤ #embed (g)$ then $f ≤ g$ in the float
  order. (Conversely `toExtRat'_le_toExtRat'_of_le` gives monotonicity; we only
  need reflection.)
]

The whole proof of the Main Theorem is now a finite case analysis that, in
each leaf, *exhibits a witness* packed float $f$, proves $#IsLawfulLower$ of
it, and matches values and signs. The next lemma is the engine that turns a
witness into the conclusion.

#block(stroke: 0.6pt + luma(60%), inset: 8pt, radius: 3pt, width: 100%)[
  #proved *Lemma 1 (Witness principle, `EUnpackedFloat.Rel_smtLibLower_of_witness`).*
  Let $0 < e_p$, $0 < s_p$, $r ∈ QQ$, and let $y : "EUnpackedFloat" e_u (s_p+1)$
  have $y."state" = Number$. Suppose there is $f : "PF"$ with
  + $f$ is not #NaN;
  + $#IsLawfulLower (#Number (r), f)$;
  + $y."num".toRat'(s_p) = f.toRat$;
  + $y."num".sgn = f.sgn$.
  Then $y #Rel (#lower (#Number (r)) : "PF")$.
]

#block(inset: (left: 0.8em))[
  *Sketch.* By (S1), $#lower (#Number (r))$ is itself a #lf for $#Number (r)$, and
  by (S3) it is non-#NaN (as $#Number (r) ≠ #NaN$). By hypotheses (1)–(2), $f$ is
  a non-#NaN #lf for the same $r$. Uniqueness (S2) forces $f = #lower (#Number (r))$.
  Now (3)–(4) and (R1) give $y #Rel f$, i.e. $y #Rel #lower (#Number (r))$. $qed$
]

It therefore remains to produce, in each branch of @eq:bln and @eq:blastlower,
a witness $f$ together with proofs of (1)–(4). Branches (under/over) have easy
explicit witnesses; the normal branch is the mathematical core.

= The nonnegative case <sec:nonneg>

Throughout this section assume $x.sgn = sans("false")$, so $x.toRat' ≥ 0$, and
write $r := x.toRat' ≥ 0$. We prove
$ #bLN (x) thin #Rel thin #lower (#Number (r)) $
(`UnpackedFloat.blastLowerNonneg_Rel_smtLibLower`) by the three-way split of
@eq:bln. Recall the exponent characterisations of the guards (already
mechanised):
$
  sans("under")(x) &= [thin x.ex."toInt" < #minSE (e_p, s_p) thin]
    && quad ("blastUnderflowNonneg_eq_decide") \
  sans("over")(x) &= [thin #maxNE (e_p) < x.ex."toInt" thin]
    && quad ("blastIsEarlyOverflowNonneg_eq_decide")
$ <eq:guards>
where $[dot.c]$ is the Boolean indicator. Both require $1 < e_p$, $0 < s_p$,
$sans("exponentWidth")(e_p,s_p) ≤ e_u$.

== Branch U: underflow

*Witness:* $f := sans("getZero")(e_p, s_p, sans("false")) = +0$.

#block(inset: (left: 0.8em))[
  *Sketch.* Assume $sans("under")(x)$, i.e. $x.ex."toInt" < #minSE$. By
  @eq:bln the circuit returns $+0$ (state $Number$). We apply Lemma 1 with
  witness $+0$. Conditions (1) $+0$ is not #NaN, (3) $(+0).toRat'(s_p) = 0 = (+0).toRat$,
  and (4) signs are both $sans("false")$ are immediate. The content is condition (2):

  #todo *Lemma U (`isLawfulLower_Number_getZero_of_underflowNonneg`).* If $x.sgn = sans("false")$
  and $sans("under")(x)$, then $#IsLawfulLower (#Number (r), +0)$.

  For Lemma U we must show $#embed (+0) = 0 ≤ r$ (true since $r ≥ 0$) and that
  every $f'$ with $#embed (f') ≤ r$ has $f' ≤ +0$. Here the underflow bound
  @eq:guards is the crux: $x.ex."toInt" < #minSE = #minNE - s_p$ together
  with @eq:toRat forces $0 ≤ r < 2^(#minSE) = $ (the smallest positive
  representable magnitude). Hence the only representable $f'$ with $#embed (f') ≤ r$
  are $≤ +0$ in the float order: a positive representable float has value
  $≥ 2^(#minSE) > r$, contradicting $#embed (f') ≤ r$, so $f'$ is a zero or
  negative, all $≤ +0$. $qed$
]

== Branch O: overflow

*Witness:* $f := sans("maxNormalNumber")(e_p, s_p, sans("false"))$, the largest finite float.

#block(inset: (left: 0.8em))[
  *Sketch.* Assume $sans("over")(x)$, i.e. $#maxNE < x.ex."toInt"$. By
  @eq:bln the circuit returns the unpacked $#maxN _(e_u, s_p+1)$. Apply Lemma 1
  with witness $sans("maxNormalNumber")$. Condition (1): its exponent is
  $sans("allOnes") - 1 ≠ sans("allOnes")$, so it is not #NaN
  (`PackedFloat.not_isNaN_maxNormalNumber`, needs $0 < e_p$). Condition (3):
  the unpacked and packed maxima agree under value,
  $ (#maxN _(e_u, s_p+1)).toRat'(s_p) = (sans("maxNormalNumber")).toRat $
  (`UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber`, needs
  $0 < s_p$, $s_p + 1 ≤ s_u$, $2 < e_p$, $sans("exponentWidth") ≤ e_u$). Condition
  (4): both signs $sans("false")$. The content is condition (2):

  #todo *Lemma O (`isLawfulLower_Number_maxNormalNumber_of_overflowNonneg`).* If
  $x.sgn = sans("false")$ and $sans("over")(x)$, then
  $#IsLawfulLower (#Number (r), sans("maxNormalNumber"))$.

  For Lemma O: the overflow bound $#maxNE < x.ex."toInt"$ gives, via
  @eq:toRat, $r > 2^(#maxNE + 1) ≥ $ value of $sans("maxNormalNumber")$, so
  $#embed (sans("maxNormalNumber")) ≤ r$. For maximality, any representable $f'$
  with $#embed (f') ≤ r$ is finite (since $+∞ > r$ is excluded only if... ) — more
  precisely every *finite* float is $≤ sans("maxNormalNumber")$ in value, and
  $+∞$ has $#embed (+∞) = +∞ > r$ because $r ∈ QQ$; hence $f' ≤ sans("maxNormalNumber")$
  by (O1). $qed$
]

#block(inset: (left: 0.8em), text(9.5pt)[
  _Remark on bounds._ Overflow uses the *early* test
  $#maxNE < x.ex."toInt"$ rather than a value comparison against
  $sans("maxNormalNumber")$. This is sound for `lower` because once the exponent
  strictly exceeds $#maxNE$, the value exceeds every finite float regardless of
  significand, so $sans("maxNormalNumber")$ is the greatest representable lower
  bound. (For #upper the same exponent regime instead yields $+∞$; see @sec:sign.)
])

== Branch N: the normal range <sec:normal>

This is the heart of the proof. Assume $x.sgn = sans("false")$,
$x."normalize" = x$, $not sans("under")(x)$ and $not sans("over")(x)$;
by @eq:guards this means
$ #minSE (e_p, s_p) ≤ x.ex."toInt" ≤ #maxNE (e_p). $ <eq:normalrange>
By @eq:bln the circuit returns $#bRTZ (x)$ (state $Number$). The goal is

#block(stroke: 0.6pt + luma(60%), inset: 8pt, radius: 3pt, width: 100%)[
  #todo *Lemma N (`exists_packedFloat_isLawfulLower_of_blastRoundTowardZero`).* Under
  the hypotheses above there is $f : "PF"$ with $f$ non-#NaN,
  $#IsLawfulLower (#Number (r), f)$, $(#bRTZ (x)).toRat' = f.toRat$, and
  $(#bRTZ (x)).sgn = f.sgn$.
]

Given Lemma N, the normal branch follows from Lemma 1 immediately
(`UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_normal`). We now prove Lemma N
by reducing it to three sublemmas about truncation toward zero.

=== What `blastRoundTowardZero` computes <sec:rtz>

The circuit is $#bRTZ (x) = (#bclr (x))$ with its top $s_p + 1$ significand bits
extracted, where $#bclr$ (`blastClearSignificand`) zeroes all significand bits
at and below the *guard index*
$ g(x) := (s_u - 1) - (s_p + 1) + (#minNE (e_p) - x.ex."toInt"."toNat" $
(`UnpackedFloat.toNat_guardBitIndex_eq`). The natural-number coercion
$(#minNE - x.ex."toInt"."toNat"$ is the *subnormal shift* $δ(x)$:
the number of extra low-order significand positions that must be discarded when
$x$ sits below the minimum normal exponent. For $g$ to be a sensible index and
$δ$ to behave, the indexing lemma needs three bounds, all discharged here from
@eq:normalrange and the standing hypotheses:
$
  -2^(e_u - 1) ≤ #minNE - x.ex."toInt" < 2^(e_u - 1),
  wide δ(x) = (#minNE - x.ex."toInt"."toNat" ≤ s_p .
$ <eq:shiftbounds>
The right-hand bound $δ(x) ≤ s_p$ is *exactly* $not sans("under")(x)$: by
@eq:consts, $#minNE - x.ex."toInt" ≤ s_p <==> x.ex."toInt" ≥ #minNE - s_p = #minSE$.
The two-sided bound holds because $#minNE - x.ex."toInt"$ fits in the
signed working exponent width (using $sans("exponentWidth") ≤ e_u$ and
@eq:normalrange). These are the hypotheses `hdiffLower`, `hdiffUpper`,
`hdiffNatLe` that thread through every guard/sticky lemma in the file.

#block(inset: (left: 0.8em))[
  #todo *Claim (truncation).* Let $t := (#bRTZ (x)).toRat'(s_p)$. Then $t$ is the
  truncation of $r$ toward zero at target precision: writing
  $beta := 2^(x.ex."toInt" - (s_p - 1) - δ(x))$ for the target unit in the
  last place,
  $ t = beta dot floor(r \/ beta), wide 0 ≤ r - t < beta. $ <eq:trunc>
]

#block(inset: (left: 0.8em))[
  *Sketch.* By @eq:toRat, $r = x.sig."toNat" dot 2^(E(x))$. Clearing the
  bits at and below index $g(x)$ replaces $x.sig."toNat"$ by
  $2^(g(x)+1) dot floor(x.sig."toNat" \/ 2^(g(x)+1))$, i.e. it rounds the
  significand down to a multiple of $2^(g(x)+1)$
  (`blastClearSignificand_sig_toNat_le` gives $≤$; the exact quotient form is the
  arithmetic content). Extracting the top $s_p + 1$ bits and re-reading the value
  at precision $s_p$ rescales by the same power of two, yielding @eq:trunc with
  $beta$ as stated. Monotonicity $0 ≤ r - t$ is
  `blastClearSignificand_toRat_le_of_nonneg` /
  `blastClearSignificand_toRat_le_of_nonneg`; nonnegativity of $t$ uses $x.sgn = sans("false")$. $qed$
]

The use of $x."normalize" = x$ enters here: normalisation guarantees the
implicit leading one sits in the top bit, so that "keep the top $s_p + 1$ bits"
retains the hidden bit plus $s_p$ significand bits and the rescaling in
@eq:trunc is exact rather than an inequality.

=== Truncation is the greatest representable lower bound

We now manufacture the witness $f$. Because @eq:normalrange holds, $t$ from
@eq:trunc has an exponent within the target range, so it is *representable*:

#block(inset: (left: 0.8em))[
  #todo *Sublemma N1 (representability).* There is $f : "PF"$, non-#NaN, with
  $f.toRat = t$ and $f.sgn = (#bRTZ (x)).sgn = sans("false")$.

  _Proof idea._ $t$ has the form $m dot 2^(x.ex."toInt" - (s_p-1) - δ)$ with
  $0 ≤ m < 2^(s_p+1)$ an integer significand (the top $s_p+1$ bits), and exponent
  in $[#minSE, #maxNE]$ by @eq:normalrange and $δ ≤ s_p$. Packing $m$ and the
  exponent produces $f$; that pack is value- and sign-preserving is
  `Packing`-style bookkeeping. (In the file this $f$ is obtained existentially;
  one may instead take $f := (#bRTZ (x))."pack"$.) $qed$
]

#block(inset: (left: 0.8em))[
  #proved *Sublemma N2 (lower bound).* $#embed (f) = #Number (t) ≤ #Number (r)$.

  _Proof._ Immediate from $t ≤ r$ in @eq:trunc and $#embed$ on finite floats
  being $#Number (dot.c)$. $qed$
]

#block(inset: (left: 0.8em))[
  #todo *Sublemma N3 (maximality).* For every $f' : "PF"$ with $#embed (f') ≤ #Number (r)$,
  we have $f' ≤ f$.

  _Proof._ Let $#embed (f') ≤ #Number (r)$. Then $f'$ is finite (as $#Number (r) ≠ +∞$
  and $≠ #NaN$), so $#embed (f') = #Number (f'.toRat)$ with $f'.toRat ≤ r$. Every
  representable value is an integer multiple of its own unit-in-last-place, and at
  the exponent of $f$ the target grid has spacing $beta$; since $f'.toRat ≤ r$ and
  $f'.toRat$ is a grid point, $f'.toRat ≤ beta floor(r\/beta) = t = f.toRat$ by
  @eq:trunc (no grid point lies in $(t, r]$ because the next grid point above $t$
  is $t + beta > r$). Thus $#embed (f') ≤ #embed (f)$, and (O1) gives $f' ≤ f$. $qed$
]

#block(inset: (left: 0.8em))[
  #todo *Proof of Lemma N.* Take $f$ from N1. It is non-#NaN. N2 and N3 are exactly the
  two conjuncts of @eq:lawful, so $#IsLawfulLower (#Number (r), f)$. Finally
  $(#bRTZ (x)).toRat' = t = f.toRat$ (N1, @eq:trunc) and
  $(#bRTZ (x)).sgn = sans("false") = f.sgn$ (N1). $qed$
]

#block(inset: (left: 0.8em), text(9.5pt)[
  _Where the bounds are essential._ N3 needs "the next grid point above $t$
  exceeds $r$," which is $r - t < beta$ from @eq:trunc. That strict inequality is
  precisely the truncation identity, and it depends on the guard index $g(x)$
  pointing at the correct bit, which in turn requires @eq:shiftbounds — i.e. the
  full strength of $not sans("under")(x)$, $not sans("over")(x)$,
  $s_p + 2 ≤ s_u$, and $sans("exponentWidth")(e_p,s_p) ≤ e_u$. Drop any of these
  and either $g(x)$ leaves the significand window or $δ$ saturates, breaking
  @eq:trunc.
])

= The sign reduction and the Main Theorem <sec:sign>

It remains to remove the standing assumption $x.sgn = sans("false")$ used in
@sec:nonneg, and to assemble the pieces. The negative case is handled by
duality, never re-doing the grid argument.

#block(stroke: 0.6pt + luma(60%), inset: 8pt, radius: 3pt, width: 100%)[
  #todo *Lemma U★ (`blastUpperNonneg_Rel_smtLibUpper`).* For $x.sgn = sans("false")$
  (and the standing hypotheses), $#bUN (x) thin #Rel thin #upper (#Number (x.toRat'))$.
]

Lemma U★ is the mirror image of @sec:nonneg: the same three branches with the
inequalities reversed, the witnesses $sans("minSubnormal")$ (underflow), $+∞$
(overflow), and $sans("blastSuccessorAwayFromZero")(x)$ (normal). We take it as
established by the symmetric development (it is the dual sorry in the file).

#block(stroke: 0.6pt + luma(60%), inset: 8pt, radius: 3pt, width: 100%)[
  #todo *Proof of the Main Theorem* (`UnpackedFloat.blastLower_Rel_smtLibLower`).
  Split on $x.sgn$. #h(0.3em) _(Structure complete; depends on the #todo lemmas above.)_

  - *$x.sgn = sans("false")$.* Then $#bL (x) = #bLN (x)$ by @eq:blastlower, and
    the conclusion is `blastLowerNonneg_Rel_smtLibLower`: combine Branches U, O, N
    above through @eq:bln. Each branch supplies a witness and invokes Lemma 1;
    the guard characterisations @eq:guards select the branch matching the
    specification's own case analysis.

  - *$x.sgn = sans("true")$.* Then $#bL (x) = -((-x).#bUN)$ by @eq:blastlower.
    Since $x.toRat' ≠ #NaN$, the duality (S4) gives
    $ #lower (#Number (x.toRat')) = -(#upper (-#Number (x.toRat'))) = -(#upper (#Number ((-x).toRat'))), $
    using $-#Number (x.toRat') = #Number ((-x).toRat')$ (`toRat'_neg`). Now $-x$ has
    sign $sans("false")$, so Lemma U★ yields
    $(-x).#bUN thin #Rel thin #upper (#Number ((-x).toRat'))$, and (R2) negates both
    sides:
    $ -((-x).#bUN) thin #Rel thin -(#upper (#Number ((-x).toRat'))) = #lower (#Number (x.toRat')). $
    This is precisely $#bL (x) #Rel #lower (#Number (x.toRat'))$. $qed$
]

= Dependency map for mechanisation <sec:deps>

The following table lists every lemma the argument consumes, its status in
`Round.lean`, and the section that uses it. "Interface" lemmas are assumed; the
remaining ones (Lemmas U, O, N and the sublemmas) are the genuine proof
obligations, currently `sorry` in the file.

#text(size: 8.5pt)[
#table(
  columns: (3.4cm, 1fr, auto),
  align: (left + horizon, left + horizon, center + horizon),
  stroke: 0.4pt + luma(70%),
  inset: (x: 6pt, y: 4pt),
  table.header(
    table.cell(fill: luma(94%))[*Used in*],
    table.cell(fill: luma(94%))[*Lemma (Lean name)*],
    table.cell(fill: luma(94%))[*Status*],
  ),
  [Lemma 1], [#c("EUnpackedFloat.Rel_smtLibLower_of_witness")], [#proved],
  [S1], [#c("lsLawfulLower_smtLibLower")], [#proved],
  [S2], [#c("eq_of_IsLawfulLower_of_IsLawfulLower")], [#proved],
  [S3], [#c("not_isNaN_lower_of_ne_NaN")], [#proved],
  [S4], [#c("smtLibLower_eq_neg_smtLibUpper_neg")], [#proved],
  [R1], [#c("Rel_of_toRat_eq_toRat_and_sign"), #c("Rel_of_Rel_of_state_eq_Number")], [#proved],
  [R2], [#c("EUnpackedFloat.neg_Rel_neg")], [#proved],
  [O1], [#c("PackedFloat.le_of_toExtRat'_le_toExtRat'")], [#proved],
  [@eq:guards], [#c("blastUnderflowNonneg_eq_decide"), #c("blastIsEarlyOverflowNonneg_eq_decide")], [#proved],
  [Branch U (Lemma U)], [#c("isLawfulLower_Number_getZero_of_underflowNonneg")], [#todo],
  [Branch O (Lemma O)], [#c("isLawfulLower_Number_maxNormalNumber_of_overflowNonneg")], [#todo],
  [Branch O (support)], [#c("not_isNaN_maxNormalNumber"), #c("toRat'_maxNormal_eq_toRat_maxNormalNumber")], [#proved],
  [Branch N (Lemma N)], [#c("exists_packedFloat_isLawfulLower_of_blastRoundTowardZero")], [#todo],
  [@eq:trunc (≤ part)], [#c("blastClearSignificand_toRat_le_of_nonneg"), #c("blastClearSignificand_sig_toNat_le")], [#proved],
  [@eq:trunc (exact)], [truncation identity — strengthen the ≤-lemmas to equality], [#todo],
  [@eq:shiftbounds], [#c("toNat_guardBitIndex_eq"), #c("toNat_lsbIndex_eq")], [#proved],
  [Lemma U★], [#c("blastUpperNonneg_Rel_smtLibUpper")], [#todo],
  [Main], [#c("blastLower_Rel_smtLibLower")], [#todo],
)
]

#v(0.3em)
#text(size: 8.5pt)[#proved #h(0.2em) interface fact or already in `Round.lean`. #h(1em) #todo #h(0.2em) remaining proof obligation (currently `sorry`).]

== Recommended mechanisation order

The five steps below are ordered by dependency: each consumes only proved
facts and the outputs of earlier steps. Equation numbers refer to the boxed,
numbered displays above.

=== Step 1 — the truncation identity (@eq:trunc)

This is the keystone; everything in the normal branch rests on it. The file
currently proves only the inequality direction (`blastClearSignificand_toRat_le_of_nonneg`,
`blastClearSignificand_sig_toNat_le`). Strengthen this to the *exact* quotient
form of @eq:trunc:
$ (#bRTZ (x)).toRat'(s_p) = beta dot floor(x.toRat' \/ beta), wide beta = 2^(x.ex."toInt" - (s_p-1) - δ(x)). $
Prove it at the bit level: `blastClearSignificand` replaces $x."sig"."toNat"$ by
$2^(g+1) floor(x."sig"."toNat" \/ 2^(g+1))$ with $g = g(x)$ the guard index, and
the top-$(s_p{+}1)$-bit extraction is exactly division by $2^(g+1)$ followed by
rescaling. The index arithmetic needs the three bounds of Equation
@eq:shiftbounds, which are already available via `toNat_guardBitIndex_eq`. *This
step requires* $x."normalize" = x$ (so the hidden bit is in the top position and
the rescaling is exact, not merely $≤$).

=== Step 2 — Sublemmas N1, N3 and Lemma N (@eq:trunc, @eq:normalrange, @eq:shiftbounds)

With Step 1 in hand, N2 is already trivial. Prove N1 (representability) by
packing the integer significand $m$ and the in-range exponent guaranteed by
@eq:normalrange together with $δ(x) ≤ s_p$ from Equation
@eq:shiftbounds; the cleanest witness is $f := (#bRTZ (x))."pack"$, so that the
existential in `exists_packedFloat_isLawfulLower_of_blastRoundTowardZero`
becomes a concrete term. Prove N3 (maximality) from the strict bound
$x.toRat' - t < beta$ of @eq:trunc plus the grid-spacing fact and order
reflection (O1). Assembling N1–N3 through @eq:lawful discharges Lemma N.

=== Step 3 — the boundary branches, Lemmas U and O (@eq:guards)

Both are short once @eq:guards rewrites the Boolean guards as exponent
comparisons. For Lemma U, $x.ex."toInt" < #minSE$ forces
$0 ≤ x.toRat' < 2^(#minSE)$, below the smallest positive representable, so $+0$
is the greatest lower bound. For Lemma O, $#maxNE < x.ex."toInt"$ forces
$x.toRat'$ above every finite float, so $#maxN$ is the greatest lower bound; the
value/sign side conditions are already proved
(`toRat'_maxNormal_eq_toRat_maxNormalNumber`, `not_isNaN_maxNormalNumber`).

=== Step 4 — mirror to the upper circuit, Lemma U★

Repeat Steps 1–3 with all inequalities reversed to obtain
`blastUpperNonneg_Rel_smtLibUpper`: the dual primitive is
`blastSuccessorAwayFromZero` (round *away* from zero), and the boundary
witnesses become $sans("minSubnormal")$ (underflow) and $+∞$ (overflow). The
truncation identity of Step 1 reused with a $ceil(dot.c)$ in place of
$floor(dot.c)$ gives the dual of @eq:trunc. No new ideas are needed.

=== Step 5 — assembly (@eq:bln, @eq:blastlower)

The top-level case analysis is already written in
`blastLower_Rel_smtLibLower`. The nonnegative case combines Steps 2–3 through
@eq:bln; the negative case rewrites via the duality (S4) and Equation
@eq:blastlower, applies Step 4, and negates with (R2). Once Steps 1–4 are
filled, this theorem closes with no remaining `sorry`.
