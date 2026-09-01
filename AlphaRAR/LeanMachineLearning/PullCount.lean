/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# Pull counts

General facts about the pull counts of the `LeanMachineLearning` sequential-learning framework:
the process-level count `pullCount A a t ω = #{s < t : A s ω = a}`. Nothing here is specific to a
design or to a probabilistic model — these are the pathwise counting facts every allocation
argument needs.

## Main results

* `Learning.infinite_setOf_eq_of_pullCount_atTop`: a diverging count forces the arm to be chosen
  infinitely often, and `Learning.infinite_setOf_eq_of_tendsto_div` for a positive limiting
  proportion.
-/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology

namespace Learning

variable {Ω 𝓐 : Type*} {A : ℕ → Ω → 𝓐}

section Infinite

variable [DecidableEq 𝓐]

/-- If arm `k`'s pull count diverges along a path, the arm is chosen infinitely often. (Were the
hit set finite, the count would be bounded by its cardinality.) -/
lemma infinite_setOf_eq_of_pullCount_atTop {k : 𝓐} {ω : Ω}
    (hN : Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop) :
    {j | A j ω = k}.Infinite := by
  intro hfin
  have hbound : ∀ n, (pullCount A k n ω : ℝ) ≤ (hfin.toFinset.card : ℝ) := by
    intro n
    have hle : pullCount A k n ω ≤ hfin.toFinset.card := by
      rw [pullCount]
      refine Finset.card_le_card fun s hs ↦ ?_
      rw [Finset.mem_filter] at hs
      exact hfin.mem_toFinset.mpr hs.2
    exact_mod_cast hle
  obtain ⟨n, hn⟩ := (hN.eventually_gt_atTop (hfin.toFinset.card : ℝ)).exists
  exact absurd (hbound n) (not_le.mpr hn)

/-- If arm `k` has a *positive* limiting proportion `N_{n,k}/n → v > 0`, it is chosen infinitely
often: `N_{n,k} = (N_{n,k}/n)·n → ∞`, so `infinite_setOf_eq_of_pullCount_atTop` applies. -/
lemma infinite_setOf_eq_of_tendsto_div {k : 𝓐} {ω : Ω} {v : ℝ} (hv : 0 < v)
    (hN : Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 v)) :
    {j | A j ω = k}.Infinite := by
  refine infinite_setOf_eq_of_pullCount_atTop ?_
  refine (hN.pos_mul_atTop hv (tendsto_natCast_atTop_atTop (R := ℝ))).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_mul_cancel₀ _ hne]

end Infinite

end Learning
