/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.NormNum

/-!
# The `tendsto` tactic

A `positivity`-style discharger for limit goals of the form
`Tendsto (fun x ↦ e x) l (𝓝 L)`.

The tactic decomposes the function body `e x` over the algebraic operations `+`, `-`, `*`,
`/` (by a constant) and negation, bottoming out in two kinds of leaves:

* **constants** — subterms not mentioning the bound variable, handled by `tendsto_const_nhds`;
* **atomic limits** — subterms `g x` for which a local hypothesis `h : Tendsto g l (𝓝 v)`
  is already available.

It builds the combined limit proof with `Filter.Tendsto.add/.sub/.neg/.mul/.div_const`,
reading each intermediate limit value back off the sub-proof's type, and finally reconciles
the computed limit with the stated target `L` using `ring`/`norm_num`. This last step is
exactly the manual `rw [mul_zero]` / `rw [add_zero]` bookkeeping that pervades the asymptotic
proofs in this project (e.g. the `h.const_mul c; rwa [mul_zero] at h` idiom and the
`h₁.mul h₂; rw [zero_mul]` idiom).

## Usage

```
example (X Y : ℕ → ℝ) (a b : ℝ) (hX : Tendsto X atTop (𝓝 a)) (hY : Tendsto Y atTop (𝓝 b)) :
    Tendsto (fun n ↦ 3 * X n + X n * Y n) atTop (𝓝 (3 * a + a * b)) := by tendsto
```

Any sub-limit the algebra cannot derive on its own (a `sqrt`, a `pow`, an `isLittleO`-based
rate, …) can simply be supplied as a hypothesis, and the tactic threads it through.

## Scope and future work

Only `𝓝 L` targets are supported; `atTop`/`atBot` divergence goals report a clear error.
The set of structural rules is currently hard-coded; the natural next step is to key the
leaf/atomic-limit rules off an attribute (à la `@[positivity]`/`@[fun_prop]`) so the "known
limits" library becomes user-extensible.
-/

public meta section

open Lean Lean.Meta Lean.Elab.Tactic Filter Topology

namespace AlphaRAR.Tactic

/-- Extract the limit value `v` from a proof whose type is `Tendsto _ _ (𝓝 v)`. -/
private def tendstoVal (pf : Expr) : MetaM Expr := do
  let ty := (← inferType pf).consumeMData
  match ty.getAppFnArgs with
  | (``Filter.Tendsto, #[_, _, _, _, nb]) =>
    match nb.consumeMData.getAppFnArgs with
    | (``nhds, #[_, _, v]) => return v
    | _ => throwError "tendsto: expected a `𝓝 _` limit, got{indentExpr ty}"
  | _ => throwError "tendsto: expected a `Tendsto` proof, got{indentExpr ty}"

/-- Look for a local hypothesis `h : Tendsto g l (𝓝 v)` with `g` defeq `targetFun`. -/
private def findHyp (l targetFun : Expr) : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty := (← instantiateMVars decl.type).consumeMData
    match ty.getAppFnArgs with
    | (``Filter.Tendsto, #[_, _, g, l', _]) =>
      if (← withNewMCtxDepth (isDefEq l' l)) && (← withNewMCtxDepth (isDefEq g targetFun)) then
        return some decl.toExpr
    | _ => pure ()
  return none

/-- Core recursion: build a proof of `Tendsto (fun x ↦ body) l (𝓝 _)`. The limit value is
recovered by the caller from the resulting proof's type. -/
private partial def core (ι β l x : Expr) (body : Expr) : MetaM Expr := do
  let body := body.consumeMData
  -- 1. constant subterm (does not mention the bound variable)
  if !body.containsFVar x.fvarId! then
    return ← mkAppOptM ``tendsto_const_nhds #[some β, none, some ι, some body, some l]
  -- 2. a hypothesis already provides this limit
  let targetFun ← mkLambdaFVars #[x] body
  if let some pf ← findHyp l targetFun then
    return pf
  -- 3. structural algebra rules
  match body.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    mkAppM ``Filter.Tendsto.add #[← core ι β l x a, ← core ι β l x b]
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    mkAppM ``Filter.Tendsto.sub #[← core ι β l x a, ← core ι β l x b]
  | (``Neg.neg, #[_, _, a]) =>
    mkAppM ``Filter.Tendsto.neg #[← core ι β l x a]
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    mkAppM ``Filter.Tendsto.mul #[← core ι β l x a, ← core ι β l x b]
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
    if !b.containsFVar x.fvarId! then
      mkAppM ``Filter.Tendsto.div_const #[← core ι β l x a, b]
    else
      throwError "tendsto: cannot divide by the non-constant sequence{indentExpr b}"
  | _ =>
    throwError "tendsto: no rule for the subterm{indentExpr body}\n\
      (provide it as a hypothesis `h : Tendsto (fun x ↦ …) l (𝓝 _)`)"

/-- `tendsto` discharges goals `Tendsto (fun x ↦ e x) l (𝓝 L)` by decomposing `e` over
`+`, `-`, `*`, `/` (by a constant) and negation into constants and hypothesis-provided atomic
limits, then reconciling the computed limit with `L` via `ring`/`norm_num`.

See the module docstring for details and scope. -/
elab "tendsto" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
  let goalTy := (← instantiateMVars (← goal.getType)).consumeMData
  let some (ι, β, f, l, nb) := (match goalTy.getAppFnArgs with
      | (``Filter.Tendsto, #[ι, β, f, l, nb]) => some (ι, β, f, l, nb)
      | _ => none)
    | throwError "tendsto: goal is not of the form `Tendsto f l (𝓝 L)`:{indentExpr goalTy}"
  let some targetVal := (match nb.consumeMData.getAppFnArgs with
      | (``nhds, #[_, _, v]) => some v
      | _ => none)
    | throwError "tendsto: only `𝓝 L` limits are supported (not `atTop`/`atBot`):{indentExpr nb}"
  let proof ← withLocalDeclD `x ι fun x => do
    let body := (mkApp f x).headBeta
    instantiateMVars (← core ι β l x body)
  if ← isDefEq goalTy (← inferType proof) then
    goal.assign proof
  else
    let val ← tendstoVal proof
    let heq ← mkFreshExprMVar (← mkEq targetVal val)
    let rem ← Lean.Elab.Tactic.run heq.mvarId! do
      evalTactic (← `(tactic| first | rfl | ring1 | norm_num | simp | ring_nf))
    unless rem.isEmpty do
      throwError "tendsto: computed the limit{indentExpr val}\n\
        but the goal claims{indentExpr targetVal}\n(they could not be reconciled automatically)."
    let motive ← withLocalDeclD `t β fun t => do
      mkLambdaFVars #[t] (← mkAppM ``Filter.Tendsto #[f, l, ← mkAppM ``nhds #[t]])
    let hGV ← mkCongrArg motive (← instantiateMVars heq)
    goal.assign (← mkAppM ``Eq.mpr #[hGV, proof])

end AlphaRAR.Tactic
