/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.Assignment
public import AlphaRAR.Mathlib.LILLogLog
public import AlphaRAR.Mathlib.MartingaleRate
public import AlphaRAR.Mathlib.MartingaleSLLN

/-!
# Rates for the assignment martingale

The assignment martingale `M` (the martingale part of a `[0,1]`-valued assignment
count process) has increments bounded by `1`. Feeding this into the bounded-increment
rate bound `isBigOpOne_of_bdd_increments` gives `M n = O_p(√n)` (blueprint `lem:M_Op`),
and into the martingale strong law `martingale_div_atTop_ae_tendsto_zero_of_bdd` gives
`M n / n → 0` a.e. (blueprint `lem:M_lln`).
-/

@[expose] public section

open MeasureTheory Filter

open scoped Topology

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- **The assignment martingale is `O_p(√n)`** (blueprint `lem:M_Op`).
For a `[0,1]`-valued adapted integrable assignment indicator `X`, the assignment
martingale `M` satisfies `M n / √n = O_p(1)`. -/
lemma isBigOpOne_assignMart_div_sqrt [IsFiniteMeasure μ]
    (hX : StronglyAdapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ)
    (h0X : ∀ n, 0 ≤ᵐ[μ] X n) (h1X : ∀ n, X n ≤ᵐ[μ] fun _ ↦ (1 : ℝ)) :
    IsBigOpOne μ (fun n ω ↦ assignMart X ℱ μ n ω / √n) := by
  have h0 : assignMart X ℱ μ 0 = 0 := by rw [assignMart, martingalePart_zero, count_zero]
  have hM0 : assignMart X ℱ μ 0 =ᵐ[μ] 0 := by filter_upwards with ω; rw [h0]
  have hΔ : ∀ n, ∀ᵐ ω ∂μ,
      |assignMart X ℱ μ (n + 1) ω - assignMart X ℱ μ n ω| ≤ 1 := by
    intro n
    filter_upwards [abs_assignMart_succ_sub_le hX_int h0X h1X n] with ω h
    simpa only [Pi.sub_apply] using h
  exact isBigOpOne_of_bdd_increments (martingale_assignMart hX hX_int) hM0 1 hΔ

/-- **LLN for the assignment martingale** (blueprint `lem:M_lln`). For a `[0,1]`-valued adapted
integrable assignment indicator `X` on a probability space, the assignment martingale `M` satisfies
`M n / n → 0` almost everywhere. The increments are bounded by `1`, so the martingale strong law of
large numbers `martingale_div_atTop_ae_tendsto_zero_of_bdd` applies. -/
lemma assignMart_div_atTop_ae_tendsto_zero [IsProbabilityMeasure μ]
    (hX : StronglyAdapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ)
    (h0X : ∀ n, 0 ≤ᵐ[μ] X n) (h1X : ∀ n, X n ≤ᵐ[μ] fun _ ↦ (1 : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ assignMart X ℱ μ n ω / n) atTop (𝓝 0) := by
  have hΔ k : ∀ᵐ ω ∂μ, |assignMart X ℱ μ (k + 1) ω - assignMart X ℱ μ k ω| ≤ 1 := by
    filter_upwards [abs_assignMart_succ_sub_le hX_int h0X h1X k] with ω h
    simpa only [Pi.sub_apply] using h
  exact martingale_div_atTop_ae_tendsto_zero_of_bdd (martingale_assignMart hX hX_int) hΔ

/-- **Loglog LIL for the assignment martingale** (blueprint `thm:lil_bounded` applied to `M_{·,k}`).
For a `[0,1]`-valued adapted integrable assignment indicator `X` on a probability space, the
assignment martingale `M` satisfies `|M_n| = O(√(n log log n))` almost surely. The increments are
bounded by `1`, so the *unconditional* bounded-increment loglog LIL
`ae_eventually_abs_le_sqrt_nat_mul_loglog_of_bdd` applies — crucially **without** requiring
`⟨M⟩_n → ∞`, which can fail here (a design whose selection probabilities degenerate to `{0,1}` has
`⟨M⟩ ≡ 0`). -/
lemma ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog [IsProbabilityMeasure μ]
    (hX : StronglyAdapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ)
    (h0X : ∀ n, 0 ≤ᵐ[μ] X n) (h1X : ∀ n, X n ≤ᵐ[μ] fun _ ↦ (1 : ℝ)) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop,
      |assignMart X ℱ μ n ω| ≤ C * √((n : ℝ) * Real.log (Real.log n)) := by
  have h0 : assignMart X ℱ μ 0 = 0 := by rw [assignMart, martingalePart_zero, count_zero]
  have hM0 : assignMart X ℱ μ 0 =ᵐ[μ] 0 := by filter_upwards with ω; rw [h0]
  have hΔ k : ∀ᵐ ω ∂μ, |assignMart X ℱ μ (k + 1) ω - assignMart X ℱ μ k ω| ≤ 1 := by
    filter_upwards [abs_assignMart_succ_sub_le hX_int h0X h1X k] with ω h
    simpa only [Pi.sub_apply] using h
  exact ae_eventually_abs_le_sqrt_nat_mul_loglog_of_bdd (martingale_assignMart hX hX_int) hM0
    one_pos hΔ

end AlphaRAR
