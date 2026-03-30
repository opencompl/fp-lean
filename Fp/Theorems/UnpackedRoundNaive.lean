import Fp.UnpackedRoundNaive
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.Packing

/-!
## Bridge Theorems: Naive Rounding ↔ SMT-LIB Semantics

Sorry'd theorems connecting each named component of `UnpackedFloat.roundNaive`
to its corresponding SMT-LIB `RoundMethod` concept.

The proof strategy is:
1. Each component theorem bridges one bitvector computation to one SMT-LIB concept.
2. The main theorem `roundNaive_pack_eq_smtLibRound` composes them all.
-/

namespace Fp
namespace UnpackedRoundNaive
