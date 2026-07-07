/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Probability.Assignment
import AlphaRAR.Probability.MartingaleRate

/-!
# The assignment martingale is `O_p(√n)`

The assignment martingale `M` (the martingale part of a `[0,1]`-valued assignment
count process) has increments bounded by `1`, so the bounded-increment rate bound
`isBigOpOne_of_bdd_increments` gives `M n = O_p(√n)`. This is blueprint `lem:M_Op`.
-/

open MeasureTheory Filter

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- **The assignment martingale is `O_p(√n)`** (blueprint `lem:M_Op`).
For a `[0,1]`-valued adapted integrable assignment indicator `X`, the assignment
martingale `M` satisfies `M n / √n = O_p(1)`. -/
theorem isBigOpOne_assignMart_div_sqrt [IsFiniteMeasure μ]
    (hX : StronglyAdapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ)
    (h0X : ∀ n, 0 ≤ᵐ[μ] X n) (h1X : ∀ n, X n ≤ᵐ[μ] fun _ => (1 : ℝ)) :
    IsBigOpOne μ (fun n ω => assignMart X ℱ μ n ω / Real.sqrt n) := by
  have h0 : assignMart X ℱ μ 0 = 0 := by rw [assignMart, martingalePart_zero, acount_zero]
  have hM0 : assignMart X ℱ μ 0 =ᵐ[μ] 0 := by filter_upwards with ω; rw [h0]
  have hΔ : ∀ n, ∀ᵐ ω ∂μ,
      |assignMart X ℱ μ (n + 1) ω - assignMart X ℱ μ n ω| ≤ 1 := by
    intro n
    filter_upwards [abs_assignMart_succ_sub_le hX_int h0X h1X n] with ω h
    simpa only [Pi.sub_apply] using h
  exact isBigOpOne_of_bdd_increments (martingale_assignMart hX hX_int) hM0 1 zero_le_one hΔ

end AlphaRAR
