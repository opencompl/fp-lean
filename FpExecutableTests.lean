import FpExecutableTests.PackedFloatEnumeration
import FpExecutableTests.SmtLibSemanticsEnumerator
import FpExecutableTests.ExhaustiveEnumerationRat
import FpExecutableTests.Harness
import FpExecutableTests.Sampling
import FpExecutableTests.AgainstFloatModel

/-!
# `FpExecutableTests`

Umbrella for the project's executable-testing infrastructure: packed-float enumerators,
the CSV golden-diff harness (FloatX/symfpu), the rational and SMT-LIB test suites, the
sampling strategies, and the format-generic differential test against `Float.Model`.

The `fp-executable-test-runner` executable roots at `FpExecutableTests.Main`, which imports
this module. `Main` is intentionally *not* imported here, so building the library does not
pull `main` into the library target.
-/
