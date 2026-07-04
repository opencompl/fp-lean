import Fp.Tactics.Attributes
import Fp.Addition
import Fp.Subtraction
import Fp.Multiplication
import Fp.Division
import Fp.Remainder
import Fp.FMA
import Fp.Negation
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.BitVec

/-!
# Stage-0 constant folding for `PackedFloat` operations

Custom `dsimproc`s (registered in our own `fp_normalize_consts` simp set) that
symbolically evaluate `PackedFloat` operations whose arguments are all literals,
folding e.g. `PackedFloat.add RNE <lit> <lit>` to the resulting `PackedFloat.mk`
literal *before* the operation is expanded into the `unpack`/`pack` circuit.

The design mirrors the core `BitVec` constant-folding simprocs in
`Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.lean`: a `Literal`-style
`fromExpr?` recovers a runtime `PackedFloat` value from a `PackedFloat.mk`
application, the *actual* compiled operation is run at meta level, and `toExpr'`
reifies the result. These are `dsimproc`s (definitional): the reified result is
defeq to the input, so no proof term is needed.
-/

open Lean Meta Simp

namespace PackedFloat

/-- Recover a runtime `PackedFloat e s` value from a literal
`@PackedFloat.mk e s <bool> <bitvec> <bitvec>` expression (for the given, already
known, widths `e`/`s`). Returns `none` if `expr` is not such a literal. -/
def fromExprAt? (e s : Nat) (expr : Expr) : SimpM (Option (PackedFloat e s)) := do
  let_expr PackedFloat.mk _e _s signE exE sigE := expr | return none
  let sign ←
    if signE.isConstOf ``Bool.true then pure true
    else if signE.isConstOf ``Bool.false then pure false
    else return none
  let some ⟨ne, exV⟩ ← getBitVecValue? exE | return none
  let some ⟨ns, sigV⟩ ← getBitVecValue? sigE | return none
  if hE : ne = e then
    if hS : ns = s then
      return some { sign := sign, ex := hE ▸ exV, sig := hS ▸ sigV }
    else return none
  else return none

/-- Reify a `PackedFloat e s` value to a clean `@PackedFloat.mk e s …` literal. -/
def toExpr' {e s : Nat} (v : PackedFloat e s) : SimpM Expr := do
  let exE ← BitVec.toExpr' v.ex
  let sigE ← BitVec.toExpr' v.sig
  return mkApp5 (.const ``PackedFloat.mk []) (mkNatLit e) (mkNatLit s)
    (toExpr v.sign) exE sigE

/-- Parse a `RoundingMode` literal (a nullary constructor). -/
def roundingModeFromExpr? (e : Expr) : Option RoundingMode :=
  if e.isConstOf ``RoundingMode.RNE then some .RNE
  else if e.isConstOf ``RoundingMode.RNA then some .RNA
  else if e.isConstOf ``RoundingMode.RTN then some .RTN
  else if e.isConstOf ``RoundingMode.RTP then some .RTP
  else if e.isConstOf ``RoundingMode.RTZ then some .RTZ
  else none

/-- Fold a unary op `@op e s x` (e.g. `neg`, `abs`) on a literal argument. -/
@[inline] def reduceUnary (declName : Name)
    (op : {e s : Nat} → PackedFloat e s → PackedFloat e s) (expr : Expr) : SimpM DStep := do
  unless expr.isAppOfArity declName 3 do return .continue
  let xE := expr.appArg!
  let sE := expr.appFn!.appArg!
  let eE := expr.appFn!.appFn!.appArg!
  let some e ← Nat.fromExpr? eE | return .continue
  let some s ← Nat.fromExpr? sE | return .continue
  let some x ← fromExprAt? e s xE | return .continue
  return .done (← toExpr' (op x))

/-- Fold a rounded binary op `@op e s m x y` on literal arguments. -/
@[inline] def reduceBinRM (declName : Name)
    (op : {e s : Nat} → RoundingMode → PackedFloat e s → PackedFloat e s → PackedFloat e s)
    (expr : Expr) : SimpM DStep := do
  unless expr.isAppOfArity declName 5 do return .continue
  let yE := expr.appArg!
  let xE := expr.appFn!.appArg!
  let mE := expr.appFn!.appFn!.appArg!
  let sE := expr.appFn!.appFn!.appFn!.appArg!
  let eE := expr.appFn!.appFn!.appFn!.appFn!.appArg!
  let some e ← Nat.fromExpr? eE | return .continue
  let some s ← Nat.fromExpr? sE | return .continue
  let some m := roundingModeFromExpr? mE | return .continue
  let some x ← fromExprAt? e s xE | return .continue
  let some y ← fromExprAt? e s yE | return .continue
  return .done (← toExpr' (op m x y))

/-- Fold a rounded ternary op `@op e s m x y z` (i.e. `fma`) on literal arguments. -/
@[inline] def reduceTernaryRM (declName : Name)
    (op : {e s : Nat} → RoundingMode → PackedFloat e s → PackedFloat e s → PackedFloat e s →
      PackedFloat e s)
    (expr : Expr) : SimpM DStep := do
  unless expr.isAppOfArity declName 6 do return .continue
  let zE := expr.appArg!
  let yE := expr.appFn!.appArg!
  let xE := expr.appFn!.appFn!.appArg!
  let mE := expr.appFn!.appFn!.appFn!.appArg!
  let sE := expr.appFn!.appFn!.appFn!.appFn!.appArg!
  let eE := expr.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!
  let some e ← Nat.fromExpr? eE | return .continue
  let some s ← Nat.fromExpr? sE | return .continue
  let some m := roundingModeFromExpr? mE | return .continue
  let some x ← fromExprAt? e s xE | return .continue
  let some y ← fromExprAt? e s yE | return .continue
  let some z ← fromExprAt? e s zE | return .continue
  return .done (← toExpr' (op m x y z))

end PackedFloat

/-! ## The constant-folding simprocs (our own `fp_normalize_consts` simp set) -/

dsimproc [fp_normalize_consts] reducePackedFloatAdd (PackedFloat.add _ _ _) :=
  PackedFloat.reduceBinRM ``PackedFloat.add PackedFloat.add

dsimproc [fp_normalize_consts] reducePackedFloatSub (PackedFloat.sub _ _ _) :=
  PackedFloat.reduceBinRM ``PackedFloat.sub PackedFloat.sub

dsimproc [fp_normalize_consts] reducePackedFloatMul (PackedFloat.mul _ _ _) :=
  PackedFloat.reduceBinRM ``PackedFloat.mul PackedFloat.mul

dsimproc [fp_normalize_consts] reducePackedFloatDiv (PackedFloat.div _ _ _) :=
  PackedFloat.reduceBinRM ``PackedFloat.div PackedFloat.div

dsimproc [fp_normalize_consts] reducePackedFloatMod (PackedFloat.mod _ _ _) :=
  PackedFloat.reduceBinRM ``PackedFloat.mod PackedFloat.mod

dsimproc [fp_normalize_consts] reducePackedFloatFma (PackedFloat.fma _ _ _ _) :=
  PackedFloat.reduceTernaryRM ``PackedFloat.fma PackedFloat.fma

dsimproc [fp_normalize_consts] reducePackedFloatNeg (PackedFloat.neg _) :=
  PackedFloat.reduceUnary ``PackedFloat.neg PackedFloat.neg

dsimproc [fp_normalize_consts] reducePackedFloatAbs (PackedFloat.abs _) :=
  PackedFloat.reduceUnary ``PackedFloat.abs PackedFloat.abs

-- The symbolic (non-literal) algebraic bitwuzla rewrites that are also folded
-- into `fp_normalize_consts` live in `Fp/BitwuzlaRewrites.lean`.
