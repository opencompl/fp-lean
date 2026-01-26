import Fp.Basic
import Fp.Packing

def UnpackedFloat.neg (x : UnpackedFloat e s) : UnpackedFloat e s :=
  { x with sign := !x.sign }

def UnpackedFloat.abs (x : UnpackedFloat e s) : UnpackedFloat e s :=
  { x with sign := false }

def EUnpackedFloat.neg (x : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  { x with num := x.num.neg }

def EUnpackedFloat.abs (x : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  { x with num := x.num.abs }

namespace PackedFloat

def neg (x : PackedFloat e s) : PackedFloat e s :=
  -- At first glance, unpacking a float just to modify its sign might look like
  -- unnecessary work; after all, you *can* toggle the sign bit directly on the
  -- packed representation. And if this operation lived in isolation, that would
  -- indeed be the simpler route.
  --
  -- However, most floating‑point operations already require unpacking, and once
  -- you're working in that representation, it's usually best to stay there.
  -- Thanks to the identity
  --
  --   `∀ uf m, (uf.round m).pack.unpack = uf.round m`
  --
  -- we can keep everything in the unpacked form throughout a chain of
  -- operations and only repack at the very end. Unpacking here helps maintain
  -- that workflow and avoids bouncing back and forth between representations.
  --
  -- TODO: is there a way to hint this optimization strategy to the compiler?
  x.unpack.neg.pack

instance : Neg (PackedFloat e s) where
  neg := .neg

def abs (x : PackedFloat e s) : PackedFloat e s :=
  -- At first glance, unpacking a float just to modify its sign might look like
  -- unnecessary work; after all, you *can* toggle the sign bit directly on the
  -- packed representation. And if this operation lived in isolation, that would
  -- indeed be the simpler route.
  --
  -- However, most floating‑point operations already require unpacking, and once
  -- you're working in that representation, it's usually best to stay there.
  -- Thanks to the identity
  --
  --   `∀ uf m, (uf.round m).pack.unpack = uf.round m`
  --
  -- we can keep everything in the unpacked form throughout a chain of
  -- operations and only repack at the very end. Unpacking here helps maintain
  -- that workflow and avoids bouncing back and forth between representations.
  --
  -- TODO: is there a way to hint this optimization strategy to the compiler?
  x.unpack.abs.pack

end PackedFloat
