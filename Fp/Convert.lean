import Fp.Basic
import Fp.UnpackedRound

set_option linter.unusedVariables false in
def UnpackedFloat.extendWidths (uf : UnpackedFloat e s) (he : e ≤ e') (hs : s ≤ s')
  : UnpackedFloat e' s' :=
  { uf with ex := uf.ex.signExtend _, sig := uf.sig.setWidth' hs <<< (s' - s) }

def EUnpackedFloat.setWidths (m : RoundingMode) (e' s')
  (euf : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e' s') (s' + 1) :=
  bif euf.isNaN then
    .mkNaN
  else bif euf.isInfinite then
    .mkInfinity euf.sign
  else bif euf.isZero then
    .mkZero euf.sign
  else bif (exponentWidth e s).ble (exponentWidth e' s') && s.ble s' then
    -- Promotion: no rounding needed!
    { euf with num := { euf.num with ex := euf.num.ex.signExtend _, sig := euf.num.sig.setWidth _ <<< (s' - s) } }
  else
    euf.num.round m

def PackedFloat.setWidths (m : RoundingMode) (e' s') (pf : PackedFloat e s) : PackedFloat e' s' :=
  (pf.unpack.setWidths m e' s').pack
