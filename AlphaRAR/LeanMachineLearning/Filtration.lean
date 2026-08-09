/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# Filtration facts for the algorithm–environment framework

General properties of the two filtrations of a `Learning.IsAlgEnvSeq` — the history filtration
`ℱ n = σ((A i, Y i)_{i ≤ n})` and the action-augmented filtration `𝒢 n` with
`𝒢 (n+1) = ℱ n ⊔ σ(A (n+1))`.

Nothing here is specific to the `αRTS` model: these are statements about `LeanMachineLearning`'s
algorithm–environment framework, and belong upstream with it. They are what makes the tower
property through `filtrationAction` usable — the *assignment* `A (n+1)` is fresh given `ℱ n`, while
the *response* `Y (n+1)` is fresh given `ℱ n` together with `A (n+1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning

namespace Learning.IsAlgEnvSeq

variable {Ω 𝓐 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  (hA : ∀ n, Measurable (A n)) (hY : ∀ n, Measurable (Y n))

/-- The history `history A Y n` is measurable with respect to the action-augmented
filtration `filtrationAction (n+1) = ℱ n ⊔ σ(A (n+1))`. -/
@[fun_prop]
lemma measurable_history_filtrationAction (n : ℕ) :
    Measurable[filtrationAction hA hY (n + 1)] (history A Y n) := by
  rw [filtrationAction_eq_comap (n + 1) (Nat.succ_ne_zero n)]
  exact measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)

/-- The next action `A (n+1)` is measurable with respect to the action-augmented
filtration `filtrationAction (n+1) = ℱ n ⊔ σ(A (n+1))`. -/
lemma measurable_action_filtrationAction (n : ℕ) :
    Measurable[filtrationAction hA hY (n + 1)] (A (n + 1)) := by
  rw [filtrationAction_eq_comap (n + 1) (Nat.succ_ne_zero n)]
  exact measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl)

/-- The action `A n` is measurable with respect to the action-augmented filtration
`filtrationAction n`, for every `n` (including `n = 0`, where `filtrationAction 0 = σ(A 0)`). -/
lemma measurable_action_filtrationAction' (n : ℕ) :
    Measurable[filtrationAction hA hY n] (A n) := by
  cases n with
  | zero => rw [filtrationAction_zero_eq_comap]; exact measurable_iff_comap_le.mpr le_rfl
  | succ m => exact measurable_action_filtrationAction hA hY m

/-- The history filtration is below the action-augmented filtration one step ahead:
`ℱ n ≤ 𝒢 (n+1)`. This is the inclusion behind the tower property that makes the
response martingale work. -/
lemma filtration_le_filtrationAction_succ (n : ℕ) :
    filtration hA hY n ≤ filtrationAction hA hY (n + 1) :=
  measurable_iff_comap_le.mp (measurable_history_filtrationAction hA hY n)

/-- A past action is measurable with respect to a later history filtration:
for `i ≤ n`, `A i` is `filtration n`-measurable. -/
lemma measurable_action_filtration {i n : ℕ} (hin : i ≤ n) :
    Measurable[filtration hA hY n] (A i) :=
  Measurable.mono (adapted_action hA hY i) ((filtration hA hY).mono hin) le_rfl

/-- A past feedback is measurable with respect to a later history filtration:
for `i ≤ n`, `Y i` is `filtration n`-measurable. -/
lemma measurable_feedback_filtration {i n : ℕ} (hin : i ≤ n) :
    Measurable[filtration hA hY n] (Y i) :=
  Measurable.mono (adapted_feedback hA hY i) ((filtration hA hY).mono hin) le_rfl

/-- A past action `A m` (`m < n`) is measurable with respect to `filtrationAction n`
(via `ℱ (n-1) ≤ filtrationAction n`). -/
lemma measurable_action_filtrationAction_lt {m n : ℕ} (hmn : m < n) :
    Measurable[filtrationAction hA hY n] (A m) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  exact (measurable_action_filtration hA hY (show m ≤ j by omega)).mono
    (filtration_le_filtrationAction_succ hA hY j) le_rfl

/-- A past feedback `Y m` (`m < n`) is measurable with respect to `filtrationAction n`
(via `ℱ (n-1) ≤ filtrationAction n`). -/
lemma measurable_feedback_filtrationAction_lt {m n : ℕ} (hmn : m < n) :
    Measurable[filtrationAction hA hY n] (Y m) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  exact (measurable_feedback_filtration hA hY (show m ≤ j by omega)).mono
    (filtration_le_filtrationAction_succ hA hY j) le_rfl

end Learning.IsAlgEnvSeq
