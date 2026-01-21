import Fp.Basic
import Fp.Packing

def UnpackedFloat.neg (x : UnpackedFloat e s) : UnpackedFloat e s :=
  { x with sign := !x.sign }

def EUnpackedFloat.neg (x : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  .mkNumber x.num.neg

namespace PackedFloat

def neg (x : PackedFloat e s) : PackedFloat e s :=
  x.unpack.neg.pack

instance : Neg (PackedFloat e s) where
  neg := .neg

end PackedFloat
