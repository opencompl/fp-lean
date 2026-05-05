# PLAN: filling `toExtRat_round_Rel_smtLibRound_of_RNE`

- add a underflowSpecialCases so we know that the exponent is inbounds.
- calling blastLower of normalized, non overflowing value will equal lower, because
  the result of blastLower is (a) packable [ie, we need a new lemma that characterizes when we can call 'pack'],
  and (b) 1ulp away. These two uniquely pin the value to be the lower.
- output of lower is normalized.
- Next, say that packing of a normalized value will give a Rel.
- Given a Rel, we know that packing the unpacked one gives the same Rel.
- Also, to prove what guard and tie break do, use that x - lower <= 2^<whatever>.
- We need a lemma that `packNumber'` preserves sign as well as `toExtRat`. 