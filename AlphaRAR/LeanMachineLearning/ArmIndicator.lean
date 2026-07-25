/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.LeanMachineLearning.Filtration

/-!
# The arm indicator

`armIndicator A k n ω = 𝟙{A n ω = k}` is the `{0,1}`-valued indicator that action `k` was chosen
at round `n`. It is the increment weight of every per-arm sum attached to an action process:
`pullCount A k n` is its partial sum (`sum_range_armIndicator_eq_pullCount`) and
`sumRewards A Y k n` is its reward-weighted partial sum (`sum_armIndicator_mul`).

Nothing here is specific to any particular design: these are statements about
`LeanMachineLearning`'s action process and its filtration, and belong upstream alongside
`Learning.pullCount` and `Learning.sumRewards`. Accordingly the adaptedness and integrability
lemmas take bare measurability hypotheses `hA`/`hY` rather than an `IsAlgEnvSeq` in a particular
environment.

## Main definitions

* `Learning.armIndicator`

## Main results

* `Learning.sum_range_armIndicator_eq_pullCount`, `Learning.sum_armIndicator_mul` — the two
  partial-sum identities.
* `Learning.stronglyAdapted_armIndicator`, `Learning.integrable_armIndicator`.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace Learning

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {P : Measure Ω}

/-- The `{0,1}`-valued assignment indicator of arm `k`: `armIndicator A k n ω = 𝟙{A n ω = k}`. -/
noncomputable def armIndicator (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ) (ω : Ω) : ℝ :=
  Set.indicator {ω | A n ω = k} (fun _ ↦ (1 : ℝ)) ω

/-- `armIndicator A k n ω = 1` exactly when arm `k` is pulled at time `n`. -/
lemma armIndicator_eq_one_iff {k : 𝓐} {n : ℕ} {ω : Ω} :
    armIndicator A k n ω = 1 ↔ A n ω = k := by
  rw [armIndicator]
  by_cases h : A n ω = k
  · rw [Set.indicator_of_mem (show ω ∈ {ω | A n ω = k} from h)]; simp [h]
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | A n ω = k} from h)]; simp [h]

lemma armIndicator_nonneg (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ) (ω : Ω) :
    0 ≤ armIndicator A k n ω :=
  Set.indicator_apply_nonneg fun _ ↦ zero_le_one

lemma armIndicator_le_one (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ) (ω : Ω) :
    armIndicator A k n ω ≤ 1 := by
  classical
  unfold armIndicator
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- Exactly one arm is pulled at each round, so the indicators sum to `1`. -/
lemma sum_armIndicator [Fintype 𝓐] (A : ℕ → Ω → 𝓐) (j : ℕ) (ω : Ω) :
    ∑ k, armIndicator A k j ω = 1 := by
  classical
  simp only [armIndicator, Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- **The partial sums of the arm indicator are the pull counts.** -/
lemma sum_range_armIndicator_eq_pullCount [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ)
    (ω : Ω) :
    ∑ j ∈ Finset.range n, armIndicator A k j ω = (pullCount A k n ω : ℝ) := by
  classical
  rw [pullCount_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [armIndicator, Set.indicator_apply, Set.mem_setOf_eq]

/-- **The reward-weighted partial sums of the arm indicator are the summed rewards.** -/
lemma sum_armIndicator_mul [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (k : 𝓐) (t : ℕ)
    (ω : Ω) :
    ∑ j ∈ Finset.range t, armIndicator A k j ω * Y j ω = sumRewards A Y k t ω := by
  rw [sumRewards]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [armIndicator, Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs <;> simp

lemma measurable_armIndicator (hA : ∀ n, Measurable (A n)) (k : 𝓐) (n : ℕ) :
    Measurable (armIndicator A k n) :=
  measurable_const.indicator ((hA n) (measurableSet_singleton k))

/-- The arm indicator is adapted to the history filtration: whether arm `k` was pulled at `n` is
known at time `n`. -/
lemma stronglyAdapted_armIndicator (hA : ∀ n, Measurable (A n)) (hY : ∀ n, Measurable (Y n))
    (k : 𝓐) :
    StronglyAdapted (IsAlgEnvSeq.filtration hA hY) (armIndicator A k) := fun n ↦
  StronglyMeasurable.indicator stronglyMeasurable_const
    (IsAlgEnvSeq.measurable_action_filtration hA hY (le_refl n) (measurableSet_singleton k))

lemma integrable_armIndicator (hA : ∀ n, Measurable (A n)) (P : Measure Ω) [IsFiniteMeasure P]
    (k : 𝓐) (n : ℕ) :
    Integrable (armIndicator A k n) P :=
  (integrable_const (1 : ℝ)).indicator ((hA n) (measurableSet_singleton k))

end Learning
