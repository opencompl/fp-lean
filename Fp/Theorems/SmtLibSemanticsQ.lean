/-
Instantiation of the SMT-LIB semantics for rationals and packed floats.
This will be where our proofs of correctness will be written against.
-/
import Fp.SmtLibSemantics

namespace Fp
namespace SmtLibSemanticsQ

noncomputable abbrev smtLibRoundMethodQ (eout sout : Nat) : SmtLibSemantics.RoundMethod (PackedFloat eout sout) ExtRat :=
  SmtLibSemantics.smtLibRoundMethod eout sout (R := ExtRat) (SmtLibSemantics.smtLibV) (SmtLibSemantics.smtLibV)


/--
The noncomputable implementation of rounding, that rounds an unpacked float of 'ein, sin'
into a packed float of 'eout, sout' according to the SMT-Lib semantics.

Our proofs will be against this definition.
-/
noncomputable def roundQ (ein sin eout sout : Nat) (rm : RoundingMode)
  (euf : EUnpackedFloat ein sin) : PackedFloat eout sout :=
  (smtLibRoundMethodQ eout sout).round rm euf.sign euf.toExtRat

end SmtLibSemanticsQ
end Fp
