import Fp
import Fp.SmtLibQSemantics


def main : IO UInt32 := do
    let mut success := true
    IO.println "Running the slow semantics to test for idempotence..."
    let out ← QSemanticsFast.ExhaustiveEnumeration.runSlowIdempotent 3 5 RoundingMode.RNE
    success := success && out
    IO.println "Running the fast semantics to test for idempotence..."
    -- | test when we give same sizes
    let out ← QSemanticsFast.ExhaustiveEnumeration.runFastIdempotent 3 5 RoundingMode.RNE
    success := success && out
    -- | test where we reduce mantissa
    -- let out ← QSemanticsFast.ExhaustiveEnumeration.runFastAgreesWithRefTest 3 5 3 3 RoundingMode.RNE
    -- success := success && out
    -- -- | test where we reduce exponent
    -- let out ← QSemanticsFast.ExhaustiveEnumeration.runFastAgreesWithRefTest 4 5 3 5 RoundingMode.RNE
    -- success := success && out
    -- -- | test where we reduce both
    -- let out ← QSemanticsFast.ExhaustiveEnumeration.runFastAgreesWithRefTest 4 5 2 3 RoundingMode.RNE
    -- success := success && out

    return if success then 0 else 1
