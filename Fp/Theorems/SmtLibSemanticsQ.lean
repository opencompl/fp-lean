/-
Instantiation of the SMT-LIB semantics for rationals and packed floats.
This will be where our proofs of correctness will be written against.
-/
import Fp.SmtLibSemantics

namespace Fp
namespace SmtLibSemanticsQ

/--
The noncomputable implementation of rounding, that rounds an unpacked float of 'ein, sin'
into a packed float of 'eout, sout' according to the SMT-Lib semantics.

Our proofs will be against this definition.
-/
noncomputable abbrev smtLibRoundMethodQ (eout sout : Nat) : SmtLibSemantics.RoundMethod (PackedFloat eout sout) ExtRat :=
  SmtLibSemantics.smtLibRoundMethod eout sout (R := ExtRat) (SmtLibSemantics.smtLibV) (SmtLibSemantics.smtLibV)

end SmtLibSemanticsQ

end Fp
