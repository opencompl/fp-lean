import Fp.EUnpackedFloat.Basic
import Fp.UnpackedFloat.packable

/--
An `EUnpackedFloat` is packable iff, whenever it is a finite number, its numeric payload is
`UnpackedFloat.Packable`. The NaN/∞/zero states impose no condition (they always pack).
-/
def EUnpackedFloat.Packable {e s : Nat} (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) : Prop :=
  euf.state = .Number → euf.num.Packable
