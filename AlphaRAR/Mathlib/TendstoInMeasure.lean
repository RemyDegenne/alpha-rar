/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# A remainder-in-probability lemma for the delta method

This file provides the analytic core of the delta method's convergence-in-probability step.

Suppose `Xₙ = aₙ • Sₙ` is a *tight* sequence of random vectors (in the sense that the tail
probabilities `μ{‖Xₙ‖ ≥ M}` are uniformly small for large `M`), the scaled-down sequence `Sₙ`
tends to `0` in probability, and `φ` is a `o(‖·‖)` remainder near the origin. Then the rescaled
remainder `aₙ • φ(Sₙ)` tends to `0` in probability.

This is the abstract statement behind the fact that, for a map `T` differentiable at `θ` with
Jacobian `G` and estimators `θ̂ₙ → θ` with `√n(θ̂ₙ - θ)` tight (from a CLT), the first-order
remainder `√n(T(θ̂ₙ) - T(θ)) - G·√n(θ̂ₙ - θ) = √n · φ(θ̂ₙ - θ)` vanishes in probability, which is
the missing hypothesis of the delta-method CLT.

The tightness input is itself supplied by weak convergence: if the laws of `Xₙ` converge to a
probability measure `ν`, then `Xₙ` is tight (`tight_of_tendsto_probabilityMeasure`), by the
portmanteau theorem together with the continuity from above of the finite measure `ν` over the
shrinking balls' complements `{‖x‖ ≥ j} ↓ ∅`.

## Main results

* `MeasureTheory.tendstoInMeasure_smul_littleO_of_tight`.
* `MeasureTheory.tight_of_tendsto_probabilityMeasure`.
-/

open Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Delta-method remainder in probability.** Let `Xₙ = aₙ • Sₙ` (with `aₙ ≥ 0`) be tight
(`hX`: for every `η > 0` there is a radius `M` with `μ{‖Xₙ‖ ≥ M} ≤ η` eventually), let
`Sₙ → 0` in probability (`hS`), and let `φ` be a first-order remainder at the origin
(`hφ`: `‖φ h‖ ≤ ε‖h‖` for `‖h‖` small, for every slope `ε > 0`). Then the rescaled remainder
`aₙ • φ(Sₙ)` tends to `0` in probability.

The proof is the classical `ε`–`δ` split: on `{‖Sₙ‖ ≤ δ} ∩ {‖Xₙ‖ < M}` one has
`‖aₙ • φ(Sₙ)‖ ≤ (ε/M)‖Xₙ‖ < ε`, so the "bad" event is contained in `{δ ≤ ‖Sₙ‖} ∪ {M ≤ ‖Xₙ‖}`,
whose probability is small by `hS` and tightness. The tightness hypothesis is only needed
*eventually*, which is exactly what a portmanteau/weak-convergence argument supplies. -/
lemma tendstoInMeasure_smul_littleO_of_tight
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {φ : E → F}
    (hφ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : E, ‖h‖ ≤ δ → ‖φ h‖ ≤ ε * ‖h‖)
    {S X : ℕ → Ω → E} (hrel : ∀ n ω, X n ω = a n • S n ω)
    (hS : TendstoInMeasure μ S atTop (fun _ ↦ 0))
    (hX : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n in atTop, μ {ω | M ≤ dist (X n ω) 0} ≤ η) :
    TendstoInMeasure μ (fun n ω ↦ a n • φ (S n ω)) atTop (fun _ ↦ (0 : F)) := by
  refine tendstoInMeasure_iff_dist.mpr fun ε hε ↦ ?_
  refine ENNReal.tendsto_nhds_zero.mpr fun b hb ↦ ?_
  obtain ⟨M, hM, hMev⟩ := hX (b / 2) (ENNReal.half_pos hb.ne')
  obtain ⟨δ, hδ, hδbd⟩ := hφ (ε / M) (div_pos hε hM)
  have hSev : ∀ᶠ n in atTop, μ {ω | δ ≤ dist (S n ω) 0} ≤ b / 2 :=
    ENNReal.tendsto_nhds_zero.mp (tendstoInMeasure_iff_dist.mp hS δ hδ) (b / 2)
      (ENNReal.half_pos hb.ne')
  filter_upwards [hSev, hMev] with n hn hMn
  calc μ {ω | ε ≤ dist (a n • φ (S n ω)) 0}
      ≤ μ ({ω | δ ≤ dist (S n ω) 0} ∪ {ω | M ≤ dist (X n ω) 0}) := by
        refine measure_mono fun ω hω ↦ ?_
        simp only [Set.mem_ofPred_eq, dist_zero_right] at hω
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, dist_zero_right, not_or, not_le] at hcon
        obtain ⟨hSlt, hXlt⟩ := hcon
        have hXnorm : ‖X n ω‖ = a n * ‖S n ω‖ := by
          rw [hrel, norm_smul, Real.norm_of_nonneg (ha n)]
        have hlt : ‖a n • φ (S n ω)‖ < ε := by
          rw [norm_smul, Real.norm_of_nonneg (ha n)]
          calc a n * ‖φ (S n ω)‖
              ≤ a n * (ε / M * ‖S n ω‖) :=
                mul_le_mul_of_nonneg_left (hδbd _ hSlt.le) (ha n)
            _ = ε / M * (a n * ‖S n ω‖) := by ring
            _ = ε / M * ‖X n ω‖ := by rw [← hXnorm]
            _ < ε / M * M := mul_lt_mul_of_pos_left hXlt (div_pos hε hM)
            _ = ε := div_mul_cancel₀ ε hM.ne'
        exact absurd hω (not_le.mpr hlt)
    _ ≤ μ {ω | δ ≤ dist (S n ω) 0} + μ {ω | M ≤ dist (X n ω) 0} := measure_union_le _ _
    _ ≤ b / 2 + b / 2 := add_le_add hn hMn
    _ = b := ENNReal.add_halves b

omit [NormedSpace ℝ E] in
/-- **Tightness from weak convergence.** If the laws `μs n` of a sequence of random vectors `Xₙ`
(i.e. `μs n = μ.map Xₙ`, hypothesis `hμs`) converge weakly to a probability measure `ν` on a
normed space, then `Xₙ` is tight: for every `η > 0` there is a radius `M > 0` with
`μ{‖Xₙ‖ ≥ M} ≤ η` eventually.

The proof combines the portmanteau theorem (weak convergence controls the `limsup` of the closed
tail `{M ≤ ‖·‖}`) with the continuity from above of the finite measure `ν` over the shrinking
family `{j ≤ ‖·‖} ↓ ∅`, which produces a radius with small `ν`-mass. -/
lemma tight_of_tendsto_probabilityMeasure {mE : MeasurableSpace E} [OpensMeasurableSpace E]
    [HasOuterApproxClosed E] {X : ℕ → Ω → E} (hXmeas : ∀ n, Measurable (X n))
    {μs : ℕ → ProbabilityMeasure E} (hμs : ∀ n, (μs n : Measure E) = μ.map (X n))
    {ν : ProbabilityMeasure E} (hconv : Tendsto μs atTop (𝓝 ν)) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, μ {ω | M ≤ dist (X n ω) 0} ≤ η := by
  -- continuity from above: the finite measure `ν` of `{j ≤ ‖·‖}` tends to `ν ∅ = 0`
  have hCanti : Antitone (fun j : ℕ ↦ {x : E | (j : ℝ) ≤ dist x 0}) := by
    intro i j hij x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact le_trans (by exact_mod_cast hij) hx
  have hCclosed : ∀ j : ℕ, IsClosed {x : E | (j : ℝ) ≤ dist x 0} := fun j ↦
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hCempty : (⋂ j : ℕ, {x : E | (j : ℝ) ≤ dist x 0}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x 0)
    exact absurd (Set.mem_iInter.mp hx j) (not_le.mpr hj)
  have hCtendsto : Tendsto (fun j : ℕ ↦ (ν : Measure E) {x : E | (j : ℝ) ≤ dist x 0}) atTop
      (𝓝 ((ν : Measure E) (⋂ j : ℕ, {x : E | (j : ℝ) ≤ dist x 0}))) :=
    tendsto_measure_iInter_atTop (fun j ↦ (hCclosed j).measurableSet.nullMeasurableSet)
      hCanti ⟨0, measure_ne_top _ _⟩
  rw [hCempty, measure_empty] at hCtendsto
  obtain ⟨j, hj⟩ := (hCtendsto.eventually_lt_const hη).exists
  refine ⟨max (j : ℝ) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  -- the closed tail at radius `M = max j 1`, whose `ν`-mass is `< η`
  have hFclosed : IsClosed {x : E | max (j : ℝ) 1 ≤ dist x 0} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hsub : {x : E | max (j : ℝ) 1 ≤ dist x 0} ⊆ {x : E | (j : ℝ) ≤ dist x 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact le_trans (le_max_left _ _) hx
  have hνF : (ν : Measure E) {x : E | max (j : ℝ) 1 ≤ dist x 0} < η :=
    lt_of_le_of_lt (measure_mono hsub) hj
  -- portmanteau: the limsup of the tail probabilities is `≤ ν`-mass `< η`
  have hlt := lt_of_le_of_lt
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv hFclosed) hνF
  filter_upwards [eventually_lt_of_limsup_lt hlt] with n hn
  rw [hμs n, Measure.map_apply (hXmeas n) hFclosed.measurableSet] at hn
  exact hn.le

end MeasureTheory
