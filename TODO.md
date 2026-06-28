# TODO / Known Issues


```
def PackedFloat.unpack (pf : PackedFloat e s)
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
```

1. Increase the width precondition to ask that `s+1+2 = s+3` bits is how many we have in the `UnpackedFloat`.
   Use this new bounds everywhere, make this into a separate PR.
1. need to round at `sp+1` iff sticky bit: Sticky theory needsRounding_{sp+1} = stickyBit_sp (both = OR of sig bits below the guard index)
1. Prove that `upper(sp+1) = upper(sp)` iff `(guard == sticky)` (from the sticky theory + lower bridge + upper = lower + needsRounding·ulp).
1. Prove that `lower(neg) = −upper(neg)` uniformly.
1. Wire all the theory together.
