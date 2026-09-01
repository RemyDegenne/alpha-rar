/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.Deterministic
public import AlphaRAR.YDK2026.AssignmentRate

/-!
# Bridging the probabilistic assignment martingale to the deterministic core

The deterministic consistency lemmas (`pos_part_vanishes`, …) are stated in terms of the
per-path count `count X'` and the assignment martingale `assignMG X' p` of a real assignment
sequence `X' : ℕ → ℝ`. The probabilistic assignment martingale `assignMart X ℱ μ` (the martingale
part of the 0-indexed count `count X`, compensated against the previous-history filtration
`ℱ.shiftDown`) is the same object, read along a path:

`assignMart X ℱ μ n ω = assignMG (X · ω) (fun j ↦ μ[X j | ℱ.shiftDown j] ω) n`,

i.e. the compensator uses the conditional selection probability `p_j = μ[X j | ℱ (j-1)]`.
This file records that identification and the resulting a.s. statement
`assignMG(path)/n → 0`, which supplies the `hM` hypothesis of `pos_part_vanishes_ae`.
It then lifts the deterministic matching lemmas to almost-sure statements, ending with the
convergence of the allocation proportions under the generic conditions.

## Main results

* `AlphaRAR.assignMart_eq_assignMG`: the per-path identification above.
* `AlphaRAR.assignMG_path_div_ae_tendsto_zero`: `assignMG(path)/n → 0` a.s.
* `AlphaRAR.consistency_ae`: `N_{n,k}/n → u_k` a.s. for every arm, from the vanishing gaps.
* `AlphaRAR.consistency_of_generic_ae`: the same conclusion from the generic conditions.
-/

@[expose] public section

open MeasureTheory Filter

open scoped Topology

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- **The probabilistic assignment martingale is the deterministic one along each path.**
With the compensator's conditional selection probability `p_j = μ[X j | ℱ (j-1)]`,
`assignMart X ℱ μ n ω = assignMG (X · ω) (fun j ↦ μ[X j | ℱ.shiftDown j] ω) n`. Proved by
telescoping `assignMart` (which starts at `0`) into its increments `X i - μ[X i | ℱ.shiftDown i]`
(`assignMart_succ_sub`), the summand of the deterministic `assignMG`. -/
lemma assignMart_eq_assignMG (n : ℕ) (ω : Ω) :
    assignMart X ℱ μ n ω
      = assignMG (X · ω) (fun j ↦ (μ[X j | ℱ.shiftDown j]) ω) n := by
  have h0 : assignMart X ℱ μ 0 ω = 0 := by
    have : assignMart X ℱ μ 0 = 0 := by rw [assignMart, martingalePart_zero, count_zero]
    rw [this]; rfl
  have htel : assignMart X ℱ μ n ω
      = ∑ i ∈ Finset.range n, (assignMart X ℱ μ (i + 1) ω - assignMart X ℱ μ i ω) := by
    rw [Finset.sum_range_sub (fun i ↦ assignMart X ℱ μ i ω), h0, sub_zero]
  rw [htel]
  simp only [assignMG]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := congrFun (assignMart_succ_sub (X := X) (ℱ := ℱ) (μ := μ) i) ω
  simpa only [Pi.sub_apply] using hi

/-- **The normalized assignment martingale vanishes, in path form.**
For a `[0,1]`-valued adapted integrable assignment indicator `X`, almost surely
`assignMG(path)_n / n → 0`, where `path = (X · ω)` and the compensator uses
`p_j = μ[X j | ℱ (j-1)]`. This is exactly the `hM` hypothesis consumed by
`pos_part_vanishes_ae`. -/
lemma assignMG_path_div_ae_tendsto_zero [IsProbabilityMeasure μ]
    (hX : StronglyAdapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ)
    (h0X : ∀ n, 0 ≤ᵐ[μ] X n) (h1X : ∀ n, X n ≤ᵐ[μ] fun _ ↦ (1 : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ assignMG (X · ω)
      (fun j ↦ (μ[X j | ℱ.shiftDown j]) ω) n / (n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [assignMart_div_atTop_ae_tendsto_zero hX hX_int h0X h1X] with ω hω
  exact hω.congr fun n ↦ by rw [assignMart_eq_assignMG]

/-- **Positive part vanishes a.s.**
The a.s. wrapper of the pathwise `pos_part_vanishes`, over general per-path processes
`Xp, pp, ρp : ℕ → Ω → ℝ` (assignment indicator, selection probability, plug-in target) and a
per-path last-under-sampling schedule `ℓ : Ω → ℕ → ℕ`. Given the plug-in-target limit (`hρ`,
from `rho_converges`), the vanishing normalized martingale (`hM`, from
`assignMG_path_div_ae_tendsto_zero`), and the two generic conditions (`hgen`, `hgs`, discharged
separately for the specific design) all a.s., the positive gap `(N_{n,k}/n - ρ̂_{n,k})⁺ → 0`
a.s. Proved by `filter_upwards` over the hypotheses and the pathwise `pos_part_vanishes`. -/
lemma pos_part_vanishes_ae {Xp pp ρp : ℕ → Ω → ℝ} {α C : ℝ} {ℓ : Ω → ℕ → ℕ} {u : Ω → ℝ}
    (hℓle : ∀ᵐ ω ∂μ, ∀ n, ℓ ω n ≤ n) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∀ᵐ ω ∂μ, u ω ∈ Set.Icc (0 : ℝ) 1)
    (hρ : ∀ᵐ ω ∂μ, Tendsto (ρp · ω) atTop (𝓝 (u ω)))
    (hM : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ assignMG (Xp · ω) (pp · ω) n / (n : ℝ)) atTop (𝓝 0))
    (hgen : ∀ᵐ ω ∂μ, ∀ n, count (Xp · ω) n - (n : ℝ) * ρp n ω
      ≤ C + (count (Xp · ω) (ℓ ω n) - (ℓ ω n : ℝ) * ρp (ℓ ω n) ω)
        + (auxU (Xp · ω) (pp · ω) (ρp · ω) α n
          - auxU (Xp · ω) (pp · ω) (ρp · ω) α (ℓ ω n)))
    (hgs : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count (Xp · ω) (ℓ ω n) - (ℓ ω n : ℝ) * ρp (ℓ ω n) ω) / (n : ℝ) < δ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ max (count (Xp · ω) n / (n : ℝ) - ρp n ω) 0) atTop (𝓝 0) := by
  filter_upwards [hℓle, hu, hρ, hM, hgen, hgs] with ω h1 h2 h3 h4 h5 h6
  exact pos_part_vanishes (Xp · ω) (pp · ω) (ρp · ω) α
    h1 hα h2 h3 h4 h5 h6

/-! ### Almost-sure matching of proportions

These are the a.s. forms of the deterministic matching lemmas: each is a `filter_upwards` over the
a.s. hypotheses (the vanishing positive/negative parts and the plug-in-target limit, supplied by
`pos_part_vanishes_ae`/`neg_part_vanishes_ae` and `rho_converges`) followed by the corresponding
pathwise core. The proportion process is `count (Y · ω k)` (`= N_{n,k}(ω)`), the plug-in target is
`r n ω k` (`= ρ̂_{n,k}(ω)`), and the (random) limit is `u ω`. -/

variable {ι : Type*}

/-- **Negative part vanishes a.s.**, the a.s. form of the pathwise `neg_part_vanishes`. -/
lemma neg_part_vanishes_ae [Fintype ι] {Y r : ℕ → Ω → ι → ℝ}
    (hY : ∀ᵐ ω ∂μ, ∀ j, ∑ k, Y j ω k = 1) (hr : ∀ᵐ ω ∂μ, ∀ n, ∑ k, r n ω k = 1)
    (hpos : ∀ᵐ ω ∂μ, ∀ j : ι,
      Tendsto (fun n ↦ max (count (Y · ω j) n / (n : ℝ) - r n ω j) 0) atTop (𝓝 0))
    (k : ι) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ max (r n ω k - count (Y · ω k) n / (n : ℝ)) 0) atTop (𝓝 0) := by
  filter_upwards [hY, hr, hpos] with ω hYω hrω hposω
  exact neg_part_vanishes (Y · ω) (r · ω) hYω hrω hposω k

/-- **Proportions match the plug-in target a.s.**
Given the vanishing gaps and `ρ̂_{n,k} → u_k`, the proportion `N_{n,k}/n → u_k` a.s. -/
lemma match_proportion_ae {Y r : ℕ → Ω → ι → ℝ} {u : Ω → ℝ} (k : ι)
    (hpos : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ max (count (Y · ω k) n / (n : ℝ) - r n ω k) 0) atTop (𝓝 0))
    (hneg : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ max (r n ω k - count (Y · ω k) n / (n : ℝ)) 0) atTop (𝓝 0))
    (hr : ∀ᵐ ω ∂μ, Tendsto (r · ω k) atTop (𝓝 (u ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ count (Y · ω k) n / (n : ℝ)) atTop (𝓝 (u ω)) := by
  filter_upwards [hpos, hneg, hr] with ω hp hn hrω
  exact match_proportion (Y · ω) (r · ω) k hp hn hrω

/-- **All arms sampled infinitely often a.s.**
If the proportion converges to a positive (random) limit, the count diverges a.s. -/
lemma all_arms_infinite_ae {Y : ℕ → Ω → ι → ℝ} {u : Ω → ℝ} (k : ι) (hu : ∀ᵐ ω ∂μ, 0 < u ω)
    (hmatch : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ count (Y · ω k) n / (n : ℝ)) atTop (𝓝 (u ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ count (Y · ω k) n) atTop atTop := by
  filter_upwards [hu, hmatch] with ω huω hmω
  exact all_arms_infinite (Y · ω) k huω hmω

/-- **A.s. consistency of the proportions**, the generic form of the first conclusion of the
paper's Theorem 4.1. Given the a.s. vanishing positive gaps for every arm (from
`pos_part_vanishes_ae`) and the plug-in-target limits `ρ̂_{n,k} → u_k` (from `rho_converges`),
together with the simplex constraints (assignments and target both sum to `1`), the proportions
converge a.s. to the target: `N_{n,k}/n → u_k` for all arms `k` simultaneously. The per-arm
negative gaps vanish by `neg_part_vanishes_ae`, and `match_proportion_ae` then closes each arm;
`ae_all_iff` bundles the finitely many arms into a single a.s. event. -/
lemma consistency_ae [Fintype ι] {Y r : ℕ → Ω → ι → ℝ} {u : Ω → ι → ℝ}
    (hY : ∀ᵐ ω ∂μ, ∀ j, ∑ k, Y j ω k = 1) (hr : ∀ᵐ ω ∂μ, ∀ n, ∑ k, r n ω k = 1)
    (hpos : ∀ k, ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ max (count (Y · ω k) n / (n : ℝ) - r n ω k) 0) atTop (𝓝 0))
    (hru : ∀ k, ∀ᵐ ω ∂μ, Tendsto (r · ω k) atTop (𝓝 (u ω k))) :
    ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun n ↦ count (Y · ω k) n / (n : ℝ)) atTop (𝓝 (u ω k)) := by
  have hpos_all : ∀ᵐ ω ∂μ, ∀ j : ι,
      Tendsto (fun n ↦ max (count (Y · ω j) n / (n : ℝ) - r n ω j) 0) atTop (𝓝 0) :=
    ae_all_iff.mpr hpos
  have hmatch : ∀ k, ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ count (Y · ω k) n / (n : ℝ)) atTop (𝓝 (u ω k)) := fun k ↦
    match_proportion_ae k (hpos k) (neg_part_vanishes_ae hY hr hpos_all k) (hru k)
  exact ae_all_iff.mpr hmatch

/-- **Generic conditions imply a.s. consistency**, the consistency direction of the paper's
Lemma 4.4. This is the modular main step: under the generic conditions (`hℓle`, `hgen`,
`hgs` — the a.s. forms of that lemma's conditions, with only `ℓ k ω n ≤ n` required of `ℓ`)
and the plug-in-target convergence `hru` (from `rho_converges`), the vanishing normalized
martingale `hM` (from the assignment martingale, `assignMG_path_div_ae_tendsto_zero`), and the
simplex constraints, the allocation proportions converge a.s. to the target for every arm:
`N_{n,k}/n → u_k`. The positive gaps vanish arm-by-arm via `pos_part_vanishes_ae`, and
`consistency_ae` closes the argument. The generic conditions themselves are discharged
separately for each design (e.g. aRTS, via `preliminary_ineq`/`preliminary_small`), so this
lemma never uses the specific form of the procedure. -/
lemma consistency_of_generic_ae [Fintype ι] {Y pp r : ℕ → Ω → ι → ℝ} {u : Ω → ι → ℝ} {α C : ℝ}
    {ℓ : ι → Ω → ℕ → ℕ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hY : ∀ᵐ ω ∂μ, ∀ j, ∑ k, Y j ω k = 1) (hr : ∀ᵐ ω ∂μ, ∀ n, ∑ k, r n ω k = 1)
    (hℓle : ∀ k, ∀ᵐ ω ∂μ, ∀ n, ℓ k ω n ≤ n)
    (hu : ∀ k, ∀ᵐ ω ∂μ, u ω k ∈ Set.Icc (0 : ℝ) 1)
    (hru : ∀ k, ∀ᵐ ω ∂μ, Tendsto (r · ω k) atTop (𝓝 (u ω k)))
    (hM : ∀ k, ∀ᵐ ω ∂μ, Tendsto (fun n ↦ assignMG (Y · ω k) (pp · ω k) n
      / (n : ℝ)) atTop (𝓝 0))
    (hgen : ∀ k, ∀ᵐ ω ∂μ, ∀ n, count (Y · ω k) n - (n : ℝ) * r n ω k
      ≤ C + (count (Y · ω k) (ℓ k ω n) - (ℓ k ω n : ℝ) * r (ℓ k ω n) ω k)
        + (auxU (Y · ω k) (pp · ω k) (r · ω k) α n
          - auxU (Y · ω k) (pp · ω k) (r · ω k) α (ℓ k ω n)))
    (hgs : ∀ k, ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count (Y · ω k) (ℓ k ω n) - (ℓ k ω n : ℝ) * r (ℓ k ω n) ω k) / (n : ℝ) < δ) :
    ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun n ↦ count (Y · ω k) n / (n : ℝ)) atTop (𝓝 (u ω k)) :=
  consistency_ae hY hr
    (fun k ↦ pos_part_vanishes_ae (hℓle k) hα (hu k) (hru k) (hM k) (hgen k) (hgs k)) hru

end AlphaRAR
