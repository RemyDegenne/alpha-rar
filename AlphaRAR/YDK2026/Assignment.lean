/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.Filtration
public import AlphaRAR.Mathlib.Process
public import AlphaRAR.YDK2026.Deterministic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.Centering
public meta import LeanSpec

/-!
# The assignment martingale

This file gives the probabilistic construction of the assignment martingale of a
single arm.

Fix a probability space with a filtration `ℱ` (the *history* filtration — in the
`IsAlgEnvSeq` framework, `ℱ_n = σ((A_i, Y_i)_{i ≤ n})`) and an (adapted, integrable)
assignment indicator process `X : ℕ → Ω → ℝ` (`X n = 𝟙{A_n = k}`, the indicator that
patient `n` is assigned to the arm).

The (0-indexed) count process is `N n = ∑_{i<n} X i`, and the assignment martingale is
the martingale part of `N` in its Doob decomposition with respect to the **previous-history
filtration** `ℱ.shiftDown` (`(ℱ.shiftDown) n = ℱ (n-1)`, with `(ℱ.shiftDown) 0 = ⊥`):
`M n = N n - ∑_{i<n} μ[X i | ℱ (i-1)]`, whose increments are `X n - μ[X n | ℱ (n-1)]`.

The shift is forced by the model: the assignment `X n = 𝟙{A_n = k}` is *fresh given the
previous history* `ℱ (n-1)` (the RAR rule draws `A_n` from an `ℱ (n-1)`-measurable law), and it
is already `ℱ n`-measurable — so its compensator `p_n = μ[X n | ℱ (n-1)]` is the selection
probability, and `M` is a martingale for `ℱ.shiftDown`. At `n = 0` there is no prior history, so
`ℱ.shiftDown 0 = ⊥` and `p_0 = μ[X_0 | ⊥] = 𝔼[X_0]`.

## Main results

* `AlphaRAR.martingale_assignMart`: `M` is a martingale (blueprint `lem:M_martingale`).
* `AlphaRAR.assignMart_succ_sub`: the increment `M (n+1) - M n = X n - μ[X n | ℱ (n-1)]`.
* `AlphaRAR.IsAssignMart`: the property that characterizes `M` — an `ℱ.shiftDown`-martingale, null
  at `0`, leaving a predictable remainder in the count — together with the two theorems saying `M`
  has it and nothing else does, up to indistinguishability.
-/

@[expose] public section

open MeasureTheory Filter Finset

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- The assignment martingale, i.e. the martingale part of the count process `N` in its Doob
decomposition with respect to the previous-history filtration `ℱ.shiftDown` (blueprint `def:M`).
Its increments are `X n - μ[X n | ℱ (n-1)]`. -/
noncomputable def assignMart (X : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  martingalePart (count X) ℱ.shiftDown μ

/-- **The assignment process is a martingale** (blueprint `lem:M_martingale`).
For an adapted, integrable assignment indicator `X`, the martingale part `M` of the count process
is a martingale for the previous-history filtration `ℱ.shiftDown`. -/
@[specifies assignMart "names the filtration the martingale property actually holds for: \
`ℱ.shiftDown`, not `ℱ`. Against `ℱ` itself the compensated count is *not* a martingale, so this \
is the fact that justifies the whole `shiftDown` detour"]
lemma martingale_assignMart [IsFiniteMeasure μ]
    (hX : StronglyAdapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ) :
    Martingale (assignMart X ℱ μ) ℱ.shiftDown μ :=
  martingale_martingalePart (stronglyAdapted_count hX) (integrable_count hX_int)

/-- The increment of the assignment martingale is `X n - μ[X n | ℱ (n-1)]`,
matching the blueprint's `ΔM = X - p` with `p_n = μ[X n | ℱ (n-1)]`. -/
@[specifies assignMart "identifies the compensator as the blueprint's selection probability \
`p_n = μ[X n | ℱ_{n-1}]` — conditioning on the history *strictly before* patient `n`, which is \
what makes `p_n` the probability of assigning arm `k` to that patient"]
lemma assignMart_succ_sub (n : ℕ) :
    assignMart X ℱ μ (n + 1) - assignMart X ℱ μ n = X n - μ[X n | ℱ.shiftDown n] := by
  have hg : count X (n + 1) - count X n = X n := by rw [count_succ]; abel
  unfold assignMart martingalePart
  rw [predictablePart_add_one, hg, count_succ]
  abel

/-- The increments of the assignment martingale are bounded by `1` (blueprint
`lem:M_martingale`, bounded-increment part): if `0 ≤ X ≤ 1` a.e., then `|M (n+1) - M n| ≤ 1` a.e. -/
lemma abs_assignMart_succ_sub_le [IsFiniteMeasure μ]
    (hX_int : ∀ n, Integrable (X n) μ)
    (h0 : ∀ n, 0 ≤ᵐ[μ] X n) (h1 : ∀ n, X n ≤ᵐ[μ] fun _ ↦ (1 : ℝ)) (n : ℕ) :
    ∀ᵐ ω ∂μ, |(assignMart X ℱ μ (n + 1) - assignMart X ℱ μ n) ω| ≤ 1 := by
  have hc0 : (0 : Ω → ℝ) ≤ᵐ[μ] μ[X n | ℱ.shiftDown n] := by
    have h := condExp_mono (m := ℱ.shiftDown n) (integrable_zero Ω ℝ μ) (hX_int n) (h0 n)
    rwa [condExp_zero] at h
  have hc1 : μ[X n | ℱ.shiftDown n] ≤ᵐ[μ] fun _ ↦ (1 : ℝ) := by
    have h := condExp_mono (m := ℱ.shiftDown n) (hX_int n) (integrable_const (1 : ℝ)) (h1 n)
    rwa [condExp_const (ℱ.shiftDown.le n)] at h
  filter_upwards [h0 n, h1 n, hc0, hc1] with ω hx0 hx1 hcω0 hcω1
  have e := congrFun (assignMart_succ_sub (X := X) (ℱ := ℱ) (μ := μ) n) ω
  simp only [Pi.sub_apply, Pi.zero_apply] at hx0 hx1 hcω0 hcω1 e ⊢
  rw [e, abs_le]
  constructor <;> linarith

end AlphaRAR
