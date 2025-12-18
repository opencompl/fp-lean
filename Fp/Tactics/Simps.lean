import Fp.Tactics.Attributes

-- TODO: look into why these theorems are needed!
attribute [bv_normalize] BitVec.setWidth'_eq
attribute [bv_normalize] Eq.mp

theorem ite_eq_cond {α} {c} [Decidable c] {b : Bool} {t e : α} (h : c = b)
  : (if c then t else e) = (bif b then t else e) := by
  simp [h]

theorem dite_eq_cond {α} {c} [Decidable c] {b : Bool} {t e : α} (h : c = b)
  : (if _ : c then t else e) = (bif b then t else e) := by
  simp [h]

theorem decide_eq_bool {p} [Decidable p] {b : Bool} (h : p = b)
  : decide p = b := by
  simp [h]

-- | TODO: upstream
attribute [bv_normalize] BitVec.cons

-- | TODO: upstream
open Lean Meta Simp in
dsimproc [seval, simp, bv_normalize] reduceLog2 (Nat.log2 _) :=
  Nat.reduceUnary ``Nat.log2 1 Nat.log2

open Lean Meta Simp in
simproc ↓ [bv_normalize] ite_eq_cond_proc (@ite _ _ _ _ _) := fun e => do
  let mkApp5 (.const ``ite [u]) α c hc t e := e | return .continue
  let r ← simp c
  let some (_, b, .const ``true _)  := r.expr.eq? | return .continue
  let h ← r.getProof
  return .visit { expr := mkApp4 (.const ``cond [u]) α b t e
                  proof? := some (mkApp7 (.const ``ite_eq_cond [u]) α c hc b t e h) }

open Lean Meta Simp in
simproc ↓ [bv_normalize] dite_eq_cond_proc (@dite _ _ _ _ _) := fun e => do
  let mkApp5 (.const ``dite [u]) α c hc (.lam _ _ t _) (.lam _ _ e _) := e | return .continue
  if t.hasLooseBVars || e.hasLooseBVars then return .continue
  let r ← simp c
  let some (_, b, .const ``true _)  := r.expr.eq? | return .continue
  let h ← r.getProof
  return .visit { expr := mkApp4 (.const ``cond [u]) α b t e
                  proof? := some (mkApp7 (.const ``dite_eq_cond [u]) α c hc b t e h) }

open Lean Meta Simp in
simproc ↓ [bv_normalize] decide_eq_bool_proc (@decide _ _) := fun e => do
  let_expr decide p hp := e | return .continue
  let r ← simp p
  let some (_, b, .const ``true _)  := r.expr.eq? | return .continue
  let h ← r.getProof
  return .visit { expr := b
                  proof? := some (mkApp4 (.const ``decide_eq_bool []) p hp b h) }
