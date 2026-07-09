/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Probability.AssignmentRate
import AlphaRAR.Auxiliary.Deterministic

/-!
# Bridging the probabilistic assignment martingale to the deterministic core

The deterministic consistency lemmas (`pos_part_vanishes`, …) are stated in terms of the
per-path count `count X'` and the assignment martingale `assignMG X' p` of a real assignment
sequence `X' : ℕ → ℝ`. The probabilistic assignment martingale `assignMart X ℱ μ` (the martingale
part of the count `acount X`) is the same object, read along a path: with the `+1` indexing
convention of `acount` (`N n = ∑_{i<n} X (i+1)`),

`assignMart X ℱ μ n ω = assignMG (fun j ↦ X (j+1) ω) (fun j ↦ μ[X (j+1) | ℱ j] ω) n`,

i.e. the compensator uses the conditional selection probability `p_{j} = μ[X (j+1) | ℱ j]`.
This file records that identification and the resulting a.s. statement
`assignMG(path)/n → 0`, which supplies the `hM` hypothesis of `pos_part_vanishes`.

## Main results

* `AlphaRAR.assignMart_eq_assignMG`: the per-path identification above.
* `AlphaRAR.assignMG_path_div_ae_tendsto_zero`: `assignMG(path)/n → 0` a.s.
-/

open MeasureTheory Filter

open scoped Topology

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- **The probabilistic assignment martingale is the deterministic one along each path.**
With the compensator's conditional selection probability `p_j = μ[X (j+1) | ℱ j]`,
`assignMart X ℱ μ n ω = assignMG (fun j ↦ X (j+1) ω) (fun j ↦ μ[X (j+1) | ℱ j] ω) n`. Proved by
telescoping `assignMart` (which starts at `0`) into its increments `X (i+1) - μ[X (i+1) | ℱ i]`
(`assignMart_succ_sub`), the summand of the deterministic `assignMG`. -/
lemma assignMart_eq_assignMG (n : ℕ) (ω : Ω) :
    assignMart X ℱ μ n ω
      = assignMG (fun j ↦ X (j + 1) ω) (fun j ↦ (μ[X (j + 1) | ℱ j]) ω) n := by
  have h0 : assignMart X ℱ μ 0 ω = 0 := by
    have : assignMart X ℱ μ 0 = 0 := by rw [assignMart, martingalePart_zero, acount_zero]
    rw [this]; rfl
  have htel : assignMart X ℱ μ n ω
      = ∑ i ∈ Finset.range n, (assignMart X ℱ μ (i + 1) ω - assignMart X ℱ μ i ω) := by
    rw [Finset.sum_range_sub (fun i ↦ assignMart X ℱ μ i ω), h0, sub_zero]
  rw [htel]
  simp only [assignMG]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := congrFun (assignMart_succ_sub (X := X) (ℱ := ℱ) (μ := μ) i) ω
  simpa only [Pi.sub_apply] using hi

/-- **The normalized assignment martingale vanishes, in path form** (blueprint `lem:M_lln`,
per-path). For a `[0,1]`-valued adapted integrable assignment indicator `X`, almost surely
`assignMG(path)_n / n → 0`, where `path = (fun j ↦ X (j+1) ω)` and the compensator uses
`p_j = μ[X (j+1) | ℱ j]`. This is exactly the `hM` hypothesis consumed by `pos_part_vanishes`. -/
lemma assignMG_path_div_ae_tendsto_zero [IsProbabilityMeasure μ]
    (hX : StronglyAdapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ)
    (h0X : ∀ n, 0 ≤ᵐ[μ] X n) (h1X : ∀ n, X n ≤ᵐ[μ] fun _ => (1 : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ assignMG (fun j ↦ X (j + 1) ω)
      (fun j ↦ (μ[X (j + 1) | ℱ j]) ω) n / (n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [assignMart_div_atTop_ae_tendsto_zero hX hX_int h0X h1X] with ω hω
  exact hω.congr fun n ↦ by rw [assignMart_eq_assignMG]

/-! ### Almost-sure matching of proportions

These are the a.s. forms of the deterministic matching lemmas: each is a `filter_upwards` over the
a.s. hypotheses (the vanishing positive/negative parts and the plug-in-target limit, supplied by
`pos_part_vanishes`/`neg_part_vanishes` and `rho_converges`) followed by the corresponding pathwise
core. The proportion process is `count (fun i ↦ Y i ω k)` (`= N_{n,k}(ω)`), the plug-in target is
`r n ω k` (`= ρ̂_{n,k}(ω)`), and the (random) limit is `u ω`. -/

variable {ι : Type*}

/-- **Negative part vanishes a.s.** (blueprint `lem:neg_part_vanishes`, a.s. form). -/
theorem neg_part_vanishes_ae [Fintype ι] {Y r : ℕ → Ω → ι → ℝ}
    (hY : ∀ᵐ ω ∂μ, ∀ j, ∑ k, Y j ω k = 1) (hr : ∀ᵐ ω ∂μ, ∀ n, ∑ k, r n ω k = 1)
    (hpos : ∀ᵐ ω ∂μ, ∀ j : ι,
      Tendsto (fun n ↦ max (count (fun i ↦ Y i ω j) n / (n : ℝ) - r n ω j) 0) atTop (𝓝 0))
    (k : ι) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ max (r n ω k - count (fun i ↦ Y i ω k) n / (n : ℝ)) 0) atTop (𝓝 0) := by
  filter_upwards [hY, hr, hpos] with ω hYω hrω hposω
  exact neg_part_vanishes (fun n ↦ Y n ω) (fun n ↦ r n ω) hYω hrω hposω k

/-- **Proportions match the plug-in target a.s.** (blueprint `lem:match`, a.s. form).
Given the vanishing gaps and `ρ̂_{n,k} → u_k`, the proportion `N_{n,k}/n → u_k` a.s. -/
theorem match_proportion_ae {Y r : ℕ → Ω → ι → ℝ} {u : Ω → ℝ} (k : ι)
    (hpos : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ max (count (fun i ↦ Y i ω k) n / (n : ℝ) - r n ω k) 0) atTop (𝓝 0))
    (hneg : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ max (r n ω k - count (fun i ↦ Y i ω k) n / (n : ℝ)) 0) atTop (𝓝 0))
    (hr : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ r n ω k) atTop (𝓝 (u ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ count (fun i ↦ Y i ω k) n / (n : ℝ)) atTop (𝓝 (u ω)) := by
  filter_upwards [hpos, hneg, hr] with ω hp hn hrω
  exact match_proportion (fun n ↦ Y n ω) (fun n ↦ r n ω) k hp hn hrω

/-- **All arms sampled infinitely often a.s.** (blueprint `lem:all_arms_infinite`, a.s. form).
If the proportion converges to a positive (random) limit, the count diverges a.s. -/
theorem all_arms_infinite_ae {Y : ℕ → Ω → ι → ℝ} {u : Ω → ℝ} (k : ι) (hu : ∀ᵐ ω ∂μ, 0 < u ω)
    (hmatch : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ count (fun i ↦ Y i ω k) n / (n : ℝ)) atTop (𝓝 (u ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ count (fun i ↦ Y i ω k) n) atTop atTop := by
  filter_upwards [hu, hmatch] with ω huω hmω
  exact all_arms_infinite (fun n ↦ Y n ω) k huω hmω

end AlphaRAR
