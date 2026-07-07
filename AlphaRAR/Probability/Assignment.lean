/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# The assignment martingale

This file gives the probabilistic construction of the assignment martingale of a
single arm, and proves it is a martingale.

Fix a probability space with a filtration `ℱ` and an (adapted, integrable)
assignment indicator process `X : ℕ → Ω → ℝ` (`X n` is the indicator that patient
`n` is assigned to the arm). The count process is `N n = ∑_{i<n} X (i+1)`, and the
assignment martingale is the martingale part of `N` in its Doob decomposition:
`M n = N n - ∑_{i<n} μ[X (i+1) | ℱ i]`, whose increments are
`X (n+1) - μ[X (n+1) | ℱ n]`.

## Main results

* `AlphaRAR.martingale_assignMart`: `M` is a martingale (blueprint `lem:M_martingale`).
* `AlphaRAR.assignMart_succ_sub`: the increment `M (n+1) - M n = X (n+1) - μ[X (n+1) | ℱ n]`.
-/

open MeasureTheory Filter Finset

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- The assignment count process of a fixed arm, `N n = ∑_{i<n} X (i+1)`. -/
def acount (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := ∑ i ∈ Finset.range n, X (i + 1)

@[simp] theorem acount_zero : acount X 0 = 0 := by simp [acount]

theorem acount_succ (n : ℕ) : acount X (n + 1) = acount X n + X (n + 1) := by
  simp [acount, Finset.sum_range_succ]

/-- The assignment martingale, i.e. the martingale part of the count process `N` in
its Doob decomposition (blueprint `def:M`). Its increments are
`X (n+1) - μ[X (n+1) | ℱ n]`. -/
noncomputable def assignMart (X : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  martingalePart (acount X) ℱ μ

theorem stronglyAdapted_acount (hX : StronglyAdapted ℱ X) : StronglyAdapted ℱ (acount X) := by
  intro n
  apply Finset.stronglyMeasurable_sum
  intro i hi
  rw [Finset.mem_range] at hi
  exact (hX (i + 1)).mono (ℱ.mono (by omega))

theorem integrable_acount (hX : ∀ n, Integrable (X n) μ) (n : ℕ) :
    Integrable (acount X n) μ :=
  integrable_finsetSum' _ fun i _ => hX (i + 1)

/-- **The assignment process is a martingale** (blueprint `lem:M_martingale`).
For an adapted, integrable assignment indicator `X`, the martingale part `M` of the
count process is a martingale. -/
theorem martingale_assignMart [IsFiniteMeasure μ]
    (hX : StronglyAdapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ) :
    Martingale (assignMart X ℱ μ) ℱ μ :=
  martingale_martingalePart (stronglyAdapted_acount hX) (integrable_acount hX_int)

/-- The increment of the assignment martingale is `X (n+1) - μ[X (n+1) | ℱ n]`,
matching the blueprint's `ΔM = X - p` with `p = μ[X | ℱ]`. -/
theorem assignMart_succ_sub (n : ℕ) :
    assignMart X ℱ μ (n + 1) - assignMart X ℱ μ n = X (n + 1) - μ[X (n + 1) | ℱ n] := by
  have hg : acount X (n + 1) - acount X n = X (n + 1) := by rw [acount_succ]; abel
  unfold assignMart martingalePart
  rw [predictablePart_add_one, hg, acount_succ]
  abel

/-- The increments of the assignment martingale are bounded by `1` (blueprint
`lem:M_martingale`, bounded-increment part): if `0 ≤ X ≤ 1` a.e., then
`|M (n+1) - M n| ≤ 1` a.e. -/
theorem abs_assignMart_succ_sub_le [IsFiniteMeasure μ]
    (hX_int : ∀ n, Integrable (X n) μ)
    (h0 : ∀ n, 0 ≤ᵐ[μ] X n) (h1 : ∀ n, X n ≤ᵐ[μ] fun _ => (1 : ℝ)) (n : ℕ) :
    ∀ᵐ ω ∂μ, |(assignMart X ℱ μ (n + 1) - assignMart X ℱ μ n) ω| ≤ 1 := by
  have hc0 : (0 : Ω → ℝ) ≤ᵐ[μ] μ[X (n + 1) | ℱ n] := by
    have h := condExp_mono (m := ℱ n) (integrable_zero Ω ℝ μ) (hX_int (n + 1)) (h0 (n + 1))
    rwa [condExp_zero] at h
  have hc1 : μ[X (n + 1) | ℱ n] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have h := condExp_mono (m := ℱ n) (hX_int (n + 1)) (integrable_const (1 : ℝ)) (h1 (n + 1))
    rwa [condExp_const (ℱ.le n)] at h
  filter_upwards [h0 (n + 1), h1 (n + 1), hc0, hc1] with ω hx0 hx1 hcω0 hcω1
  have e := congrFun (assignMart_succ_sub (X := X) (ℱ := ℱ) (μ := μ) n) ω
  simp only [Pi.sub_apply, Pi.zero_apply] at hx0 hx1 hcω0 hcω1 e ⊢
  rw [e, abs_le]
  constructor <;> linarith

end AlphaRAR
