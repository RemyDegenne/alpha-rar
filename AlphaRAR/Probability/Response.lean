/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.HasCondDistrib
import AlphaRAR.Probability.QuadraticVariation
import AlphaRAR.Probability.MartingaleRate
import LeanMachineLearning.SequentialLearning.StationaryEnv
import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# The response martingale, via the algorithm–environment framework

We model the sequential multi-treatment experiment with the `LeanMachineLearning`
`IsAlgEnvSeq` framework: an *action* `A n` is the arm assigned to patient `n`, and
the *feedback* `Y n` is the observed response. In a **stationary environment** with
per-arm reward kernel `ν : Kernel 𝓐 ℝ`, the response of a patient assigned to arm
`a` is drawn from `ν a`, independently of the past given the arm.

The mean of arm `a` is `(ν a)[id] = ∫ x, x ∂(ν a)`. The centered response martingale
of arm `k` is `Q k n = ∑_{m < n} 𝟙{A (m+1) = k} (Y (m+1) - (ν k)[id])`.

This resolves the filtration-convention issue behind blueprint `lem:Q_martingale`:
`M` (the assignment martingale) is a martingale because the *assignment* `A (n+1)`
is fresh randomness given the history `ℱ n`, while `Q` is a martingale because the
*response* `Y (n+1)` is fresh given the history **and** the current assignment
(`filtrationAction (n+1) = ℱ n ⊔ σ(A (n+1))`). The two use genuinely different
information at each step, made rigorous here by the tower property through
`filtrationAction`.

## Main results

* `AlphaRAR.condExp_feedback`: `𝔼[Y n | filtrationAction n] = (ν (A n))[id]`.
-/

open MeasureTheory ProbabilityTheory Filter Learning

/-!
### Filtration facts for the algorithm–environment framework

These are general properties of the two filtrations of an algorithm–environment
sequence — the history filtration `ℱ n = σ((A i, Y i)_{i ≤ n})` and the
action-augmented filtration `𝒢 n` with `𝒢 (n+1) = ℱ n ⊔ σ(A (n+1))`. They belong
naturally to `Learning.IsAlgEnvSeq`; we record the pieces used by the response
martingale here.
-/

namespace Learning.IsAlgEnvSeq

variable {Ω 𝓐 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  (hA : ∀ n, Measurable (A n)) (hY : ∀ n, Measurable (Y n))

/-- The history `history A Y n` is measurable with respect to the action-augmented
filtration `filtrationAction (n+1) = ℱ n ⊔ σ(A (n+1))`. -/
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

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

omit [MeasurableSingletonClass 𝓐] in
/-- **Conditional expectation of a function of the feedback.**
Under a stationary environment with per-arm reward kernel `ν`, the conditional
expectation of `g (Y n)` given the action-augmented filtration `filtrationAction n`
(the history up to `n-1` together with the current action `A n`) is the integral of `g`
against the chosen arm's reward distribution, `∫ x, g x ∂(ν (A n))`. This is the crux behind
the response martingale (and its quadratic variation): the fresh randomness of a step is the
response, revealed *after* the arm is chosen. The base case `n = 0` (conditioning on just
`σ(A 0)`, initial kernel `ν0 = ν`) and the step `n = m+1` (conditioning on the history and
`A (m+1)`, step kernel `ν.prodMkLeft`) are treated separately. -/
lemma condExp_feedback_comp (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ)
    {g : ℝ → ℝ} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y n ω)) P) :
    P[fun ω ↦ g (Y n ω) |
        IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback n]
      =ᵐ[P] fun ω ↦ (ν (A n ω))[g] := by
  cases n with
  | zero =>
    have hX : Measurable (A 0) := h.measurable_action 0
    have hcd : HasCondDistrib (Y 0) (A 0) ν P := by
      have hf := h.hasCondDistrib_feedback_zero
      rwa [ν0_stationaryEnv] at hf
    rw [IsAlgEnvSeq.filtrationAction_zero_eq_comap]
    exact hcd.condExp_comp_eq hX hg hint
  | succ m =>
    have hX : Measurable (fun ω ↦ (history A Y m ω, A (m + 1) ω)) :=
      (measurable_history h.measurable_action h.measurable_feedback m).prodMk
        (h.measurable_action (m + 1))
    have hcd : HasCondDistrib (Y (m + 1)) (fun ω ↦ (history A Y m ω, A (m + 1) ω))
        (ν.prodMkLeft _) P := by
      have hf := h.hasCondDistrib_feedback m
      rwa [feedback_stationaryEnv] at hf
    rw [IsAlgEnvSeq.filtrationAction_eq_comap (m + 1) (Nat.succ_ne_zero m)]
    refine (hcd.condExp_comp_eq hX hg hint).trans ?_
    filter_upwards with ω
    rw [Kernel.prodMkLeft_apply]

omit [MeasurableSingletonClass 𝓐] in
/-- **Conditional expectation of the feedback is the mean of the arm's reward kernel.**
Under a stationary environment with per-arm reward kernel `ν`, the conditional expectation of
the response `Y n` given the action-augmented filtration `filtrationAction n` is the mean
`(ν (A n))[id]` of the chosen arm's reward distribution. This is the `g = id` case of
`condExp_feedback_comp`. -/
lemma condExp_feedback (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ)
    (hint : Integrable (Y n) P) :
    P[Y n | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback n]
      =ᵐ[P] fun ω ↦ (ν (A n ω))[id] :=
  condExp_feedback_comp h n stronglyMeasurable_id hint

/-- The **variance of arm `a`** under its reward kernel: `V_a = Var[id ; ν a]`, the
variance of the reward distribution `ν a` (Mathlib's `ProbabilityTheory.variance`). This
is the `V_k` of blueprint Condition **A**; it is the per-step conditional variance of the
response martingale increment. -/
noncomputable def armVar (ν : Kernel 𝓐 ℝ) (a : 𝓐) : ℝ := variance id (ν a)

omit [MeasurableSingletonClass 𝓐] in
/-- `armVar` as the central second moment: `V_a = ∫ (x - θ_a)² ∂(ν a)`, where
`θ_a = (ν a)[id]` is the arm mean. -/
lemma armVar_eq_integral (ν : Kernel 𝓐 ℝ) (a : 𝓐) :
    armVar ν a = ∫ x, (x - (ν a)[id]) ^ 2 ∂(ν a) := by
  rw [armVar, variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq]

/-- The centered **response martingale** of arm `k`:
`Q k n = ∑_{m < n} 𝟙{A m = k} (Y m - (ν k)[id])`, summing over patients `0, …, n-1`. Its
increments are the mean-centered responses of the patients assigned to arm `k`. -/
noncomputable def respMart (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (k : 𝓐) (n : ℕ) :
    Ω → ℝ := ∑ m ∈ Finset.range n, fun ω ↦
  Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω * (Y m ω - (ν k)[id])

omit [IsMarkovKernel ν] in
/-- Each response-martingale increment is integrable (the indicator is bounded and the
centered response is integrable). -/
lemma integrable_respMart_increment {m : ℕ} (hAmeas : Measurable (A m))
    (hint : Integrable (Y m) P) (k : 𝓐) :
    Integrable (fun ω ↦ Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω
      * (Y m ω - (ν k)[id])) P := by
  have heq : (fun ω ↦ Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω
        * (Y m ω - (ν k)[id]))
      = {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (ν k)[id]) := by
    funext ω
    simp only [Set.indicator]
    by_cases hω : ω ∈ {ω | A m ω = k} <;> simp [hω]
  rw [heq]
  exact (hint.sub (integrable_const _)).indicator (hAmeas (measurableSet_singleton k))

/-- **The response martingale increment has zero conditional expectation given `𝒢`.**
Conditioning on the action-augmented filtration `𝒢 i = filtrationAction i` (the history up to
`i-1` *and* the current assignment `A i`), the increment `𝟙{A i = k}(Y i - (ν k)[id])` vanishes
in conditional mean: the indicator is `𝒢 i`-measurable and pulls out, and the response's
conditional mean is the arm mean `(ν (A i))[id]`, which cancels `(ν k)[id]` on `{A i = k}`. This is
the fact that makes `Q` a martingale for `filtrationAction`. -/
lemma condExp_respMart_increment (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ)
    (hint : Integrable (Y i) P) :
    P[fun ω ↦ Set.indicator {ω | A i ω = k} (fun _ ↦ (1 : ℝ)) ω * (Y i ω - (ν k)[id])
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] 0 := by
  set hA := h.measurable_action with hA_def
  set hY := h.measurable_feedback with hY_def
  set G := IsAlgEnvSeq.filtrationAction hA hY i with hG_def
  set c : Ω → ℝ := Set.indicator {ω | A i ω = k} (fun _ ↦ (1 : ℝ)) with hc_def
  set g : Ω → ℝ := fun ω ↦ Y i ω - (ν k)[id] with hg_def
  have hGle : G ≤ mΩ := (IsAlgEnvSeq.filtrationAction hA hY).le i
  -- `A i` and the indicator `c` are `G`-measurable.
  have hAG : Measurable[G] (A i) :=
    IsAlgEnvSeq.measurable_action_filtrationAction' hA hY i
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator (hAG (measurableSet_singleton k))
  have hgint : Integrable g P := hint.sub (integrable_const _)
  have hcint : Integrable (fun ω ↦ c ω * g ω) P :=
    integrable_respMart_increment (hA i) hint k
  have hcondg : P[g | G] =ᵐ[P] fun ω ↦ (ν (A i ω))[id] - (ν k)[id] := by
    refine (condExp_sub hint (integrable_const _) _).trans ?_
    rw [condExp_const hGle]
    exact (condExp_feedback h i hint).sub (EventuallyEq.refl _ _)
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcint hgint
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * g | G] ω = 0
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A i ω) k with hak | hak
  · rw [hak]; ring
  · have : c ω = 0 := by rw [hc_def, Set.indicator_of_notMem (by simpa using hak)]
    rw [this, zero_mul]

/-- **Conditional second moment of the response-martingale increment** (blueprint
`lem:Q_quad_var`, per-step form). Conditioning on the action-augmented filtration
`𝒢 i = filtrationAction i` (the history and the current assignment `A i`), the squared increment
`(𝟙{A i = k}(Y i - θ_k))²` has conditional expectation `𝟙{A i = k} · V_k`, where
`V_k = armVar ν k` is the variance of arm `k`. The indicator squares to itself, and on the event
`{A i = k}` the response's conditional second central moment is exactly the arm variance.
Retaining the (`𝒢`-measurable) indicator is what turns the summed second moments into
`V_k N_{n,k}`. -/
lemma condExp_respMart_increment_sq (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ)
    (hint : Integrable (fun ω ↦ (Y i ω - (ν k)[id]) ^ 2) P) :
    P[fun ω ↦ (Set.indicator {ω | A i ω = k} (fun _ ↦ (1 : ℝ)) ω
          * (Y i ω - (ν k)[id])) ^ 2
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] fun ω ↦ Set.indicator {ω | A i ω = k} (fun _ ↦ (1 : ℝ)) ω * armVar ν k := by
  set hA := h.measurable_action with hA_def
  set hY := h.measurable_feedback with hY_def
  set G := IsAlgEnvSeq.filtrationAction hA hY i with hG_def
  set c : Ω → ℝ := Set.indicator {ω | A i ω = k} (fun _ ↦ (1 : ℝ)) with hc_def
  set g : Ω → ℝ := fun ω ↦ (Y i ω - (ν k)[id]) ^ 2 with hg_def
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator
      ((IsAlgEnvSeq.measurable_action_filtrationAction' hA hY i) (measurableSet_singleton k))
  -- The squared increment equals `c · g` (the indicator squares to itself).
  have hsq : (fun ω ↦ (c ω * (Y i ω - (ν k)[id])) ^ 2) = fun ω ↦ c ω * g ω := by
    funext ω
    simp only [hg_def]
    by_cases hω : ω ∈ {ω | A i ω = k}
    · simp only [hc_def, Set.indicator_of_mem hω]; ring
    · simp only [hc_def, Set.indicator_of_notMem hω]; ring
  rw [hsq]
  -- `c · g` is integrable (bounded indicator times an integrable square).
  have hcgint : Integrable (fun ω ↦ c ω * g ω) P := by
    have hform : (fun ω ↦ c ω * g ω) = {ω | A i ω = k}.indicator g := by
      funext ω
      simp only [hc_def, Set.indicator]
      by_cases hω : ω ∈ {ω | A i ω = k} <;> simp [hω]
    rw [hform]
    exact hint.indicator (hA i (measurableSet_singleton k))
  -- Conditional expectation of `g = (Y - θ_k)²` given `G` is the arm's second central moment.
  have hcondg : P[g | G] =ᵐ[P] fun ω ↦ ∫ x, (x - (ν k)[id]) ^ 2 ∂(ν (A i ω)) := by
    have hg2 : StronglyMeasurable (fun x : ℝ ↦ (x - (ν k)[id]) ^ 2) :=
      ((continuous_id.sub continuous_const).pow 2).stronglyMeasurable
    exact condExp_feedback_comp h i hg2 hint
  -- Pull out the `G`-measurable indicator `c`, then evaluate on the arm event.
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcgint hint
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * g | G] ω = _
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A i ω) k with hak | hak
  · rw [hak, armVar_eq_integral]
  · have hc0 : c ω = 0 := by rw [hc_def, Set.indicator_of_notMem (by simpa using hak)]
    rw [hc0, zero_mul, zero_mul]

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- Successor form: `Q k (n+1) = Q k n + 𝟙{A n = k}(Y n - (ν k)[id])`. -/
lemma respMart_succ (k : 𝓐) (n : ℕ) :
    respMart ν A Y k (n + 1) = respMart ν A Y k n + fun ω ↦
      Set.indicator {ω | A n ω = k} (fun _ ↦ (1 : ℝ)) ω * (Y n ω - (ν k)[id]) := by
  funext ω
  simp only [respMart, Finset.sum_range_succ, Pi.add_apply]

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- The response-martingale increment: `Q k (n+1) - Q k n = 𝟙{A n=k}(Y n - (ν k)[id])`. -/
lemma respMart_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω
      = Set.indicator {ω | A n ω = k} (fun _ ↦ (1 : ℝ)) ω * (Y n ω - (ν k)[id]) := by
  rw [respMart_succ]; simp only [Pi.add_apply]; ring

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- **The increments of `Q_k` and `Q_j` have identically-zero product for `k ≠ j`.**
A patient is assigned to exactly one arm, so the indicators `𝟙{A = k}` and `𝟙{A = j}` are
disjoint (`𝟙{A = k}·𝟙{A = j} = 0`); hence `ΔQ_{·,k} · ΔQ_{·,j} = 0`. This is the (unconditional)
orthogonality behind the vanishing cross variation. -/
lemma respMart_increment_mul_eq_zero {k j : 𝓐} (hkj : k ≠ j) (n : ℕ) :
    (respMart ν A Y k (n + 1) - respMart ν A Y k n)
      * (respMart ν A Y j (n + 1) - respMart ν A Y j n) = 0 := by
  funext ω
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, respMart_succ_sub]
  rcases eq_or_ne (A n ω) k with hak | hak
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω | A n ω = j} by simp only [Set.mem_setOf_eq]; rw [hak]; exact hkj)]
    ring
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω | A n ω = k} by simpa using hak)]
    ring

omit [IsMarkovKernel ν] in
/-- Each `Q k n` is integrable (a finite sum of integrable increments). -/
lemma integrable_respMart (hA : ∀ n, Measurable (A n)) (hint : ∀ n, Integrable (Y n) P)
    (k : 𝓐) (n : ℕ) : Integrable (respMart ν A Y k n) P :=
  integrable_finsetSum' _ fun m _ => integrable_respMart_increment (hA m) (hint m) k

/-- The response martingale `Q k` is adapted to the action-augmented filtration
`𝒢 = filtrationAction`: `Q k n` depends only on the assignments and responses of patients
`0, …, n-1`, all of which are `𝒢 n`-measurable (since `ℱ (n-1) ≤ 𝒢 n`). -/
lemma stronglyAdapted_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) :
    StronglyAdapted (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
      (respMart ν A Y k) := by
  set 𝒢 := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  intro n
  unfold respMart
  refine Finset.stronglyMeasurable_sum _ fun m hm => ?_
  rw [Finset.mem_range] at hm
  have hAm : Measurable[𝒢 n] (A m) :=
    IsAlgEnvSeq.measurable_action_filtrationAction_lt h.measurable_action h.measurable_feedback hm
  have hYm : Measurable[𝒢 n] (Y m) :=
    IsAlgEnvSeq.measurable_feedback_filtrationAction_lt h.measurable_action h.measurable_feedback hm
  exact (stronglyMeasurable_const.indicator (hAm (measurableSet_singleton k))).mul
    (hYm.stronglyMeasurable.sub stronglyMeasurable_const)

/-- **The response martingale is a martingale** (blueprint `lem:Q_martingale`).
For arm `k`, `Q k` is a martingale for the action-augmented filtration
`𝒢 n = filtrationAction n = ℱ (n-1) ⊔ σ(A n)` — the history up to the previous patient together
with the current assignment. The increment `𝟙{A i = k}(Y i - (ν k)[id])` has zero conditional
expectation given `𝒢 i` because the response `Y i` is fresh given the current arm
(`condExp_respMart_increment`); this is the filtration for which the paper's response martingale
is a genuine martingale difference (the assignment is known, the response is not). -/
theorem martingale_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) :
    Martingale (respMart ν A Y k)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  set 𝒢 := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback with h𝒢
  have hInt : ∀ n, Integrable (respMart ν A Y k n) P :=
    integrable_respMart h.measurable_action hint k
  have hadapt : StronglyAdapted 𝒢 (respMart ν A Y k) := stronglyAdapted_respMart h k
  refine martingale_nat hadapt hInt fun i => ?_
  rw [respMart_succ]
  symm
  have hadd := condExp_add (hInt i)
    (integrable_respMart_increment (ν := ν) (h.measurable_action i) (hint i) k) (𝒢 i)
  have hself : P[respMart ν A Y k i | 𝒢 i] = respMart ν A Y k i :=
    condExp_of_stronglyMeasurable (𝒢.le i) (hadapt i) (hInt i)
  have hincr := condExp_respMart_increment h k i (hint i)
  rw [← h𝒢] at hincr
  filter_upwards [hadd, hincr] with ω ha hin
  rw [ha, Pi.add_apply, congrFun hself ω, hin, Pi.zero_apply, add_zero]

/-!
### The quadratic variation of the response martingale

Since `Q k` is a martingale for `𝒢 = filtrationAction`, the paper's quadratic variation
`V_k N_{n,k}` is the *ordinary* predictable quadratic variation `predQuadVar Q 𝒢`: the compensator
increment `V_k X_{n,k}` keeps the indicator because the current arm `A n` is `𝒢 n`-measurable
(`condExp_respMart_increment_sq`).
-/

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The squared response-martingale increment is integrable (indicator bounded × integrable
centered square). -/
lemma integrable_respMart_increment_sq {m : ℕ} (k : 𝓐) (hAmeas : Measurable (A m))
    (hcent2 : Integrable (fun ω ↦ (Y m ω - (ν k)[id]) ^ 2) P) :
    Integrable (fun ω ↦ (Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω
      * (Y m ω - (ν k)[id])) ^ 2) P := by
  have heq : (fun ω ↦ (Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω
        * (Y m ω - (ν k)[id])) ^ 2)
      = {ω | A m ω = k}.indicator (fun ω ↦ (Y m ω - (ν k)[id]) ^ 2) := by
    funext ω
    by_cases hω : ω ∈ {ω | A m ω = k}
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [heq]
  exact hcent2.indicator (hAmeas (measurableSet_singleton k))

omit [IsMarkovKernel ν] in
/-- Each response-martingale increment is in `L²` when the response is (Condition **A**): a
bounded indicator times the `L²` centered response. -/
lemma memLp_respMart_increment {m : ℕ} (k : 𝓐) (hAmeas : Measurable (A m))
    (hY2 : MemLp (Y m) 2 P) :
    MemLp (fun ω ↦ Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω
      * (Y m ω - (ν k)[id])) 2 P := by
  have heq : (fun ω ↦ Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω
        * (Y m ω - (ν k)[id]))
      = {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (ν k)[id]) := by
    funext ω
    by_cases hω : ω ∈ {ω | A m ω = k}
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [heq]
  exact (hY2.sub (memLp_const _)).indicator (hAmeas (measurableSet_singleton k))

omit [IsMarkovKernel ν] in
/-- `Q k n` is in `L²` when the responses are (Condition **A**): a finite sum of `L²` increments. -/
lemma memLp_respMart (hA : ∀ n, Measurable (A n)) (hY2 : ∀ n, MemLp (Y n) 2 P) (k : 𝓐) (n : ℕ) :
    MemLp (respMart ν A Y k n) 2 P := by
  unfold respMart
  exact memLp_finsetSum' _ fun m _ => memLp_respMart_increment k (hA m) (hY2 m)

/-- **The quadratic variation of `Q` is `V_k N`** (blueprint `lem:Q_quad_var`).
For the action-augmented filtration `𝒢 = filtrationAction` — for which `Q k` is a martingale
(`martingale_respMart`) — the ordinary predictable quadratic variation of `Q k` is `V_k` times the
assignment count of arm `k`: `⟨Q k⟩_n = V_k N_{n,k}` a.e. The compensator increments are the
`𝒢`-conditional second moments `V_k X_{m,k}` (`condExp_respMart_increment_sq`), which sum to
`V_k N` because the indicator is retained. The only hypothesis is Condition **A**: the responses
are square-integrable (`hY2 : MemLp (Y n) 2 P`); the integrability of `Q`, its increments, and its
increment products (feeding the discrete Doob decomposition) are all derived from it. -/
theorem predQuadVar_respMart_eq [DecidableEq 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (hY2 : ∀ n, MemLp (Y n) 2 P) (n : ℕ) :
    predQuadVar (respMart ν A Y k)
        (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
        P n
      =ᵐ[P] fun ω ↦ armVar ν k * (pullCount A k n ω : ℝ) := by
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hcent2 : ∀ n, Integrable (fun ω ↦ (Y n ω - (ν k)[id]) ^ 2) P :=
    fun n ↦ ((hY2 n).sub (memLp_const _)).integrable_sq
  have hprod : ∀ n, Integrable (respMart ν A Y k n
      * (respMart ν A Y k (n + 1) - respMart ν A Y k n)) P := fun n ↦
    (memLp_respMart h.measurable_action hY2 k n).integrable_mul
      ((memLp_respMart h.measurable_action hY2 k (n + 1)).sub
        (memLp_respMart h.measurable_action hY2 k n))
  have hM := martingale_respMart h hint k
  -- The martingale increment `ΔQ` squares to the squared centered response.
  have hdiff : ∀ m, (fun ω ↦ (respMart ν A Y k (m + 1) ω - respMart ν A Y k m ω) ^ 2)
      = fun ω ↦ (Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω
        * (Y m ω - (ν k)[id])) ^ 2 := by
    intro m; funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
  have hd2 : ∀ m, Integrable
      (fun ω ↦ (respMart ν A Y k (m + 1) ω - respMart ν A Y k m ω) ^ 2) P := by
    intro m; rw [hdiff m]
    exact integrable_respMart_increment_sq k (h.measurable_action m) (hcent2 m)
  -- Each compensator increment is `V_k · X_{m,k}`.
  have hkey : ∀ m, predQuadVar (respMart ν A Y k)
          (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P (m + 1)
        - predQuadVar (respMart ν A Y k)
          (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P m
      =ᵐ[P] fun ω ↦ armVar ν k * Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω := by
    intro m
    have h1 := predQuadVar_succ_sub_eq hM m (hd2 m) (hprod m)
    rw [hdiff m] at h1
    refine h1.trans ?_
    refine (condExp_respMart_increment_sq h k m (hcent2 m)).trans ?_
    filter_upwards with ω; ring
  induction n with
  | zero => filter_upwards with ω; simp [predQuadVar_zero]
  | succ n ih =>
    filter_upwards [ih, hkey n] with ω hih hk
    simp only [Pi.sub_apply] at hk
    -- `N_{n+1,k} = N_{n,k} + X_{n,k}` (as reals), matching the compensator increment.
    have hrc : (pullCount A k (n + 1) ω : ℝ)
        = (pullCount A k n ω : ℝ) + Set.indicator {ω | A n ω = k} (fun _ ↦ (1 : ℝ)) ω := by
      rw [pullCount_add_one]
      by_cases hak : A n ω = k
      · rw [if_pos hak, Set.indicator_of_mem (show ω ∈ {ω | A n ω = k} from hak)]
        push_cast; ring
      · rw [if_neg hak, Set.indicator_of_notMem (show ω ∉ {ω | A n ω = k} from hak)]
        push_cast; ring
    change predQuadVar (respMart ν A Y k)
        (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
        P (n + 1) ω = armVar ν k * (pullCount A k (n + 1) ω : ℝ)
    rw [hrc, mul_add]
    have hih' : predQuadVar (respMart ν A Y k)
        (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
        P n ω = armVar ν k * (pullCount A k n ω : ℝ) := hih
    linarith [hk, hih']

/-- **`Q² - ⟨Q⟩` is a martingale** for the action-augmented filtration `𝒢 = filtrationAction`
(`lem:qv_mart` for `Q`). Together with `predQuadVar_respMart_eq` (`⟨Q⟩ = V_k N`) this is the
compensated response martingale. The only hypothesis is Condition **A** (`hY2 : MemLp (Y n) 2 P`),
from which the square-integrability of `Q` is derived. -/
theorem martingale_sq_sub_predQuadVar_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (hY2 : ∀ n, MemLp (Y n) 2 P) :
    Martingale
      (fun n ↦ (fun ω ↦ respMart ν A Y k n ω ^ 2)
        - predQuadVar (respMart ν A Y k)
            (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P n)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
      P :=
  martingale_sq_sub_predQuadVar (stronglyAdapted_respMart h k)
    (fun n ↦ (memLp_respMart h.measurable_action hY2 k n).integrable_sq)

/-- **The second moment of `Q` is `V_k` times the expected assignment count** (blueprint
`lem:Q_second_moment`): `𝔼[Q_{n,k}²] = V_k · 𝔼[N_{n,k}]`. This is the discrete Itô isometry
(`integral_sq_eq_integral_predQuadVar`, `lem:qv_second_moment`) specialized to `Q`, using
`⟨Q_k⟩ = V_k N` (`predQuadVar_respMart_eq`): `𝔼[Q²] = 𝔼[⟨Q⟩] = V_k 𝔼[N]`. The only hypothesis is
Condition **A**. -/
theorem integral_respMart_sq_eq [DecidableEq 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (hY2 : ∀ n, MemLp (Y n) 2 P) (n : ℕ) :
    ∫ ω, respMart ν A Y k n ω ^ 2 ∂P = armVar ν k * ∫ ω, (pullCount A k n ω : ℝ) ∂P := by
  rw [integral_sq_eq_integral_predQuadVar (stronglyAdapted_respMart h k)
      (fun m ↦ (memLp_respMart h.measurable_action hY2 k m).integrable_sq)
      (by filter_upwards with ω; simp [respMart]) n,
    integral_congr_ae (predQuadVar_respMart_eq h k hY2 n), integral_const_mul]

/-- **The cross variation of `Q_k` and `Q_j` vanishes for `k ≠ j`** (blueprint `lem:Q_cross_var`):
`Q_k · Q_j` is a martingale (for the action-augmented filtration `𝒢 = filtrationAction`), hence its
predictable compensator — the cross variation `⟨Q_k, Q_j⟩` — is `0`. The orthogonality is not
merely conditional: since each patient is assigned to exactly one arm, the increment indicators
`𝟙{A = k}` and `𝟙{A = j}` are disjoint, so the product of increments `ΔQ_{·,k} · ΔQ_{·,j}` is
*identically* `0`. -/
theorem martingale_respMart_mul (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) {k j : 𝓐} (hkj : k ≠ j) :
    Martingale (fun n ↦ respMart ν A Y k n * respMart ν A Y j n)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
      P := by
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hMN : ∀ n, Integrable (respMart ν A Y k n * respMart ν A Y j n) P := fun n ↦
    (memLp_respMart h.measurable_action hY2 k n).integrable_mul
      (memLp_respMart h.measurable_action hY2 j n)
  have hB : ∀ i, Integrable
      (respMart ν A Y k i * (respMart ν A Y j (i + 1) - respMart ν A Y j i)) P := fun i ↦
    (memLp_respMart h.measurable_action hY2 k i).integrable_mul
      ((memLp_respMart h.measurable_action hY2 j (i + 1)).sub
        (memLp_respMart h.measurable_action hY2 j i))
  have hC : ∀ i, Integrable
      (respMart ν A Y j i * (respMart ν A Y k (i + 1) - respMart ν A Y k i)) P := fun i ↦
    (memLp_respMart h.measurable_action hY2 j i).integrable_mul
      ((memLp_respMart h.measurable_action hY2 k (i + 1)).sub
        (memLp_respMart h.measurable_action hY2 k i))
  exact martingale_mul (martingale_respMart h hint k) (martingale_respMart h hint j)
    hMN hB hC (fun i ↦ by rw [respMart_increment_mul_eq_zero hkj i]; exact integrable_zero _ _ _)
    (fun i ↦ by rw [respMart_increment_mul_eq_zero hkj i]; simp)

/-- **The increment second moment of `Q` is bounded by the arm variance `V_k`.**
`∫ (ΔQ_{n+1})² ∂P = V_k · P{A n = k} ≤ V_k`: the `𝒢`-conditional second moment is `𝟙{A n = k}·V_k`
(`condExp_respMart_increment_sq`), so by the tower property the integral is `V_k` times the
probability of assigning arm `k`, which is `≤ 1`. This is the increment bound feeding `cor:mart_Op`
(`isBigOpOne_respMart_div_sqrt`). -/
lemma integral_respMart_increment_sq_le (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (n : ℕ) (hY2 : MemLp (Y n) 2 P) :
    ∫ ω, (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2 ∂P ≤ armVar ν k := by
  have hcent2 : Integrable (fun ω ↦ (Y n ω - (ν k)[id]) ^ 2) P :=
    (hY2.sub (memLp_const _)).integrable_sq
  have hdiff : (fun ω ↦ (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2)
      = fun ω ↦ (Set.indicator {ω | A n ω = k} (fun _ ↦ (1 : ℝ)) ω
        * (Y n ω - (ν k)[id])) ^ 2 := by
    funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
  have hGle : IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback n
      ≤ mΩ :=
    (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback).le n
  have hset : MeasurableSet {ω | A n ω = k} :=
    h.measurable_action n (measurableSet_singleton k)
  have hσ2 : (0 : ℝ) ≤ armVar ν k := by rw [armVar]; exact variance_nonneg _ _
  rw [hdiff, ← integral_condExp hGle,
    integral_congr_ae (condExp_respMart_increment_sq h k n hcent2),
    integral_mul_const (armVar ν k), integral_indicator_const (1 : ℝ) hset,
    smul_eq_mul, mul_one]
  have hprob : (P {ω | A n ω = k}).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  exact mul_le_of_le_one_left hσ2 hprob

/-- **The response martingale is `O_p(√n)`** (blueprint `cor:mart_Op` applied to `Q`).
For each arm `k`, under Condition **A** (square-integrable responses, `hY2 : MemLp (Y n) 2 P`),
`Q_{n,k} / √n = O_p(1)`, i.e. `Q_{n,k} = O_p(√n)`.

`Q k` is a martingale for the action-augmented filtration `𝒢 = filtrationAction`
(`martingale_respMart`) with `Q k 0 = 0`, and its increment second moments are bounded by the arm
variance: `∫ (ΔQ)² ≤ V_k`. Indeed the `𝒢`-conditional second moment is `𝟙{A n = k}·V_k`
(`condExp_respMart_increment_sq`), so by the tower property `∫ (ΔQ)² = V_k · P{A n = k} ≤ V_k`.
Then `isBigOpOne_martingale_div_sqrt` (`cor:mart_Op`) applies with `σ² = V_k`. -/
theorem isBigOpOne_respMart_div_sqrt (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (k : 𝓐) :
    IsBigOpOne P (fun n ω ↦ respMart ν A Y k n ω / Real.sqrt n) := by
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hcent2 : ∀ n, Integrable (fun ω ↦ (Y n ω - (ν k)[id]) ^ 2) P :=
    fun n ↦ ((hY2 n).sub (memLp_const _)).integrable_sq
  -- The martingale increment `ΔQ` squares to the squared centered response.
  have hdiff : ∀ m, (fun ω ↦ (respMart ν A Y k (m + 1) ω - respMart ν A Y k m ω) ^ 2)
      = fun ω ↦ (Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω
        * (Y m ω - (ν k)[id])) ^ 2 := by
    intro m; funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
  have hM := martingale_respMart h hint k
  have hM2 : ∀ n, Integrable (fun ω ↦ respMart ν A Y k n ω ^ 2) P :=
    fun n ↦ (memLp_respMart h.measurable_action hY2 k n).integrable_sq
  have hM0 : respMart ν A Y k 0 =ᵐ[P] 0 := by filter_upwards with ω; simp [respMart]
  have hd2 : ∀ m, Integrable
      (fun ω ↦ (respMart ν A Y k (m + 1) ω - respMart ν A Y k m ω) ^ 2) P := by
    intro m; rw [hdiff m]
    exact integrable_respMart_increment_sq k (h.measurable_action m) (hcent2 m)
  have hprod : ∀ n, Integrable (respMart ν A Y k n
      * (respMart ν A Y k (n + 1) - respMart ν A Y k n)) P := fun n ↦
    (memLp_respMart h.measurable_action hY2 k n).integrable_mul
      ((memLp_respMart h.measurable_action hY2 k (n + 1)).sub
        (memLp_respMart h.measurable_action hY2 k n))
  have hσ2 : (0 : ℝ) ≤ armVar ν k := by rw [armVar]; exact variance_nonneg _ _
  have hinc : ∀ n, ∫ ω, (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2 ∂P
      ≤ armVar ν k := fun n ↦ integral_respMart_increment_sq_le h k n (hY2 n)
  exact isBigOpOne_martingale_div_sqrt hM hM2 hM0 (armVar ν k) hσ2 hd2 hprod hinc

end AlphaRAR
