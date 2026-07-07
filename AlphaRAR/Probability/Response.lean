/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.HasCondDistrib
import AlphaRAR.Probability.QuadraticVariation
import LeanMachineLearning.SequentialLearning.StationaryEnv

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

* `AlphaRAR.condExp_feedback`: `𝔼[Y (n+1) | ℱ n ⊔ σ(A (n+1))] = (ν (A (n+1)))[id]`.
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

end Learning.IsAlgEnvSeq

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [StandardBorelSpace 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐] in
/-- **Conditional expectation of a function of the feedback.**
Under a stationary environment with per-arm reward kernel `ν`, the conditional
expectation of `g (Y (n+1))` given the history up to `n` together with the action
`A (n+1)` is the integral of `g` against the chosen arm's reward distribution,
`∫ x, g x ∂(ν (A (n+1)))`. This is the crux behind the response martingale (and its
quadratic variation): the fresh randomness of a step is the response, revealed
*after* the arm is chosen. -/
lemma condExp_feedback_comp (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ)
    {g : ℝ → ℝ} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y (n + 1) ω)) P) :
    P[fun ω ↦ g (Y (n + 1) ω) |
        IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback (n + 1)]
      =ᵐ[P] fun ω ↦ (ν (A (n + 1) ω))[g] := by
  have hX : Measurable (fun ω ↦ (history A Y n ω, A (n + 1) ω)) :=
    (measurable_history h.measurable_action h.measurable_feedback n).prodMk
      (h.measurable_action (n + 1))
  have hcd : HasCondDistrib (Y (n + 1)) (fun ω ↦ (history A Y n ω, A (n + 1) ω))
      (ν.prodMkLeft _) P := by
    have hf := h.hasCondDistrib_feedback n
    rwa [feedback_stationaryEnv] at hf
  rw [IsAlgEnvSeq.filtrationAction_eq_comap (n + 1) (Nat.succ_ne_zero n)]
  refine (hcd.condExp_comp_eq hX hg hint).trans ?_
  filter_upwards with ω
  rw [Kernel.prodMkLeft_apply]

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐] in
/-- **Conditional expectation of the feedback is the mean of the arm's reward kernel.**
Under a stationary environment with per-arm reward kernel `ν`, the conditional
expectation of the response `Y (n+1)` given the history up to `n` together with the
action `A (n+1)` is the mean `(ν (A (n+1)))[id]` of the chosen arm's reward
distribution. This is the `g = id` case of `condExp_feedback_comp`. -/
lemma condExp_feedback (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ)
    (hint : Integrable (Y (n + 1)) P) :
    P[Y (n + 1) | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback (n + 1)]
      =ᵐ[P] fun ω ↦ (ν (A (n + 1) ω))[id] :=
  condExp_feedback_comp h n stronglyMeasurable_id hint

/-- The **variance of arm `a`** under its reward kernel: `V_a = Var[id ; ν a]`, the
variance of the reward distribution `ν a` (Mathlib's `ProbabilityTheory.variance`). This
is the `V_k` of blueprint Condition **A**; it is the per-step conditional variance of the
response martingale increment. -/
noncomputable def armVar (ν : Kernel 𝓐 ℝ) (a : 𝓐) : ℝ := variance id (ν a)

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐] in
/-- `armVar` as the central second moment: `V_a = ∫ (x - θ_a)² ∂(ν a)`, where
`θ_a = (ν a)[id]` is the arm mean. -/
lemma armVar_eq_integral (ν : Kernel 𝓐 ℝ) (a : 𝓐) :
    armVar ν a = ∫ x, (x - (ν a)[id]) ^ 2 ∂(ν a) := by
  rw [armVar, variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq]

/-- The centered **response martingale** of arm `k`:
`Q k n = ∑_{m < n} 𝟙{A (m+1) = k} (Y (m+1) - (ν k)[id])`. Its increments are the
mean-centered responses of the patients assigned to arm `k`. -/
noncomputable def respMart (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (k : 𝓐) (n : ℕ) :
    Ω → ℝ := ∑ m ∈ Finset.range n, fun ω ↦
  Set.indicator {ω | A (m + 1) ω = k} (fun _ ↦ (1 : ℝ)) ω * (Y (m + 1) ω - (ν k)[id])

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] [IsMarkovKernel ν] in
/-- Each response-martingale increment is integrable (the indicator is bounded and the
centered response is integrable). -/
lemma integrable_respMart_increment {m : ℕ} (hAmeas : Measurable (A (m + 1)))
    (hint : Integrable (Y (m + 1)) P) (k : 𝓐) :
    Integrable (fun ω ↦ Set.indicator {ω | A (m + 1) ω = k} (fun _ ↦ (1 : ℝ)) ω
      * (Y (m + 1) ω - (ν k)[id])) P := by
  have heq : (fun ω ↦ Set.indicator {ω | A (m + 1) ω = k} (fun _ ↦ (1 : ℝ)) ω
        * (Y (m + 1) ω - (ν k)[id]))
      = {ω | A (m + 1) ω = k}.indicator (fun ω ↦ Y (m + 1) ω - (ν k)[id]) := by
    funext ω
    simp only [Set.indicator]
    by_cases hω : ω ∈ {ω | A (m + 1) ω = k} <;> simp [hω]
  rw [heq]
  exact (hint.sub (integrable_const _)).indicator (hAmeas (measurableSet_singleton k))

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
/-- **The response martingale increment has zero conditional expectation.**
For arm `k`, `𝔼[𝟙{A (i+1) = k}(Y (i+1) - (ν k)[id]) | ℱ i] = 0`, where `ℱ` is the
history filtration. The proof conditions first on `ℱ i ⊔ σ(A (i+1))` (where the
indicator is measurable and the feedback's conditional mean is the arm mean, so the
product vanishes), then applies the tower property down to `ℱ i`. -/
lemma condExp_respMart_increment (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ)
    (hint : Integrable (Y (i + 1)) P) :
    P[fun ω ↦ Set.indicator {ω | A (i + 1) ω = k} (fun _ ↦ (1 : ℝ)) ω * (Y (i + 1) ω - (ν k)[id])
        | IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback i] =ᵐ[P] 0 := by
  set hA := h.measurable_action with hA_def
  set hY := h.measurable_feedback with hY_def
  set G := IsAlgEnvSeq.filtrationAction hA hY (i + 1) with hG_def
  set c : Ω → ℝ := Set.indicator {ω | A (i + 1) ω = k} (fun _ ↦ (1 : ℝ)) with hc_def
  set g : Ω → ℝ := fun ω ↦ Y (i + 1) ω - (ν k)[id] with hg_def
  have hGle : G ≤ mΩ := (IsAlgEnvSeq.filtrationAction hA hY).le (i + 1)
  have hFle : IsAlgEnvSeq.filtration hA hY i ≤ G :=
    IsAlgEnvSeq.filtration_le_filtrationAction_succ hA hY i
  -- `A (i+1)` and the indicator `c` are `G`-measurable.
  have hAG : Measurable[G] (A (i + 1)) :=
    IsAlgEnvSeq.measurable_action_filtrationAction hA hY i
  have hSG : MeasurableSet[G] {ω | A (i + 1) ω = k} := hAG (measurableSet_singleton k)
  have hcG : StronglyMeasurable[G] c := stronglyMeasurable_const.indicator hSG
  have hgint : Integrable g P := hint.sub (integrable_const _)
  have hcint : Integrable (fun ω ↦ c ω * g ω) P :=
    integrable_respMart_increment (hA (i + 1)) hint k
  -- Conditional expectation given `G` vanishes.
  have hEG : P[fun ω ↦ c ω * g ω | G] =ᵐ[P] 0 := by
    have hcondg : P[g | G] =ᵐ[P] fun ω ↦ (ν (A (i + 1) ω))[id] - (ν k)[id] := by
      refine (condExp_sub hint (integrable_const _) _).trans ?_
      rw [condExp_const hGle]
      exact (condExp_feedback h i hint).sub (EventuallyEq.refl _ _)
    have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcint hgint
    filter_upwards [hpull, hcondg] with ω hp hcg
    change P[c * g | G] ω = 0
    rw [hp, Pi.mul_apply, hcg]
    rcases eq_or_ne (A (i + 1) ω) k with hak | hak
    · rw [hak]; ring
    · have : c ω = 0 := by rw [hc_def, Set.indicator_of_notMem (by simpa using hak)]
      rw [this, zero_mul]
  -- Tower property down to `ℱ i`.
  calc P[fun ω ↦ c ω * g ω | IsAlgEnvSeq.filtration hA hY i]
      =ᵐ[P] P[P[fun ω ↦ c ω * g ω | G] | IsAlgEnvSeq.filtration hA hY i] :=
        (condExp_condExp_of_le hFle hGle).symm
    _ =ᵐ[P] P[(0 : Ω → ℝ) | IsAlgEnvSeq.filtration hA hY i] := condExp_congr_ae hEG
    _ =ᵐ[P] 0 := by simp

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
/-- **Conditional second moment of the response-martingale increment** (blueprint
`lem:Q_quad_var`, per-step form). Conditioning on the history *and* the current
assignment `𝒢 (i+1) = ℱ i ⊔ σ(A (i+1))`, the squared increment
`(𝟙{A (i+1) = k}(Y (i+1) - θ_k))²` has conditional expectation `𝟙{A (i+1) = k} · V_k`,
where `V_k = armVar ν k` is the variance of arm `k`. The indicator squares to itself,
and on the event `{A (i+1) = k}` the response's conditional second central moment is
exactly the arm variance. Retaining the (`𝒢`-measurable) indicator is what turns the
summed second moments into `V_k N_{n,k}`. -/
lemma condExp_respMart_increment_sq (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ)
    (hint : Integrable (fun ω ↦ (Y (i + 1) ω - (ν k)[id]) ^ 2) P) :
    P[fun ω ↦ (Set.indicator {ω | A (i + 1) ω = k} (fun _ ↦ (1 : ℝ)) ω
          * (Y (i + 1) ω - (ν k)[id])) ^ 2
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback (i + 1)]
      =ᵐ[P] fun ω ↦ Set.indicator {ω | A (i + 1) ω = k} (fun _ ↦ (1 : ℝ)) ω * armVar ν k := by
  set hA := h.measurable_action with hA_def
  set hY := h.measurable_feedback with hY_def
  set G := IsAlgEnvSeq.filtrationAction hA hY (i + 1) with hG_def
  set c : Ω → ℝ := Set.indicator {ω | A (i + 1) ω = k} (fun _ ↦ (1 : ℝ)) with hc_def
  set g : Ω → ℝ := fun ω ↦ (Y (i + 1) ω - (ν k)[id]) ^ 2 with hg_def
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator
      ((IsAlgEnvSeq.measurable_action_filtrationAction hA hY i) (measurableSet_singleton k))
  -- The squared increment equals `c · g` (the indicator squares to itself).
  have hsq : (fun ω ↦ (c ω * (Y (i + 1) ω - (ν k)[id])) ^ 2) = fun ω ↦ c ω * g ω := by
    funext ω
    simp only [hg_def]
    by_cases hω : ω ∈ {ω | A (i + 1) ω = k}
    · simp only [hc_def, Set.indicator_of_mem hω]; ring
    · simp only [hc_def, Set.indicator_of_notMem hω]; ring
  rw [hsq]
  -- `c · g` is integrable (bounded indicator times an integrable square).
  have hcgint : Integrable (fun ω ↦ c ω * g ω) P := by
    have hform : (fun ω ↦ c ω * g ω) = {ω | A (i + 1) ω = k}.indicator g := by
      funext ω
      simp only [hc_def, Set.indicator]
      by_cases hω : ω ∈ {ω | A (i + 1) ω = k} <;> simp [hω]
    rw [hform]
    exact hint.indicator (hA (i + 1) (measurableSet_singleton k))
  -- Conditional expectation of `g = (Y - θ_k)²` given `G` is the arm's second central moment.
  have hcondg : P[g | G] =ᵐ[P] fun ω ↦ ∫ x, (x - (ν k)[id]) ^ 2 ∂(ν (A (i + 1) ω)) := by
    have hg2 : StronglyMeasurable (fun x : ℝ ↦ (x - (ν k)[id]) ^ 2) :=
      ((continuous_id.sub continuous_const).pow 2).stronglyMeasurable
    exact condExp_feedback_comp h i hg2 hint
  -- Pull out the `G`-measurable indicator `c`, then evaluate on the arm event.
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcgint hint
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * g | G] ω = _
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A (i + 1) ω) k with hak | hak
  · rw [hak, armVar_eq_integral]
  · have hc0 : c ω = 0 := by rw [hc_def, Set.indicator_of_notMem (by simpa using hak)]
    rw [hc0, zero_mul, zero_mul]

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- Successor form: `Q k (n+1) = Q k n + 𝟙{A (n+1) = k}(Y (n+1) - (ν k)[id])`. -/
lemma respMart_succ (k : 𝓐) (n : ℕ) :
    respMart ν A Y k (n + 1) = respMart ν A Y k n + fun ω ↦
      Set.indicator {ω | A (n + 1) ω = k} (fun _ ↦ (1 : ℝ)) ω * (Y (n + 1) ω - (ν k)[id]) := by
  funext ω
  simp only [respMart, Finset.sum_range_succ, Pi.add_apply]

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] [IsMarkovKernel ν] in
/-- Each `Q k n` is integrable (a finite sum of integrable increments). -/
lemma integrable_respMart (hA : ∀ n, Measurable (A n)) (hint : ∀ n, Integrable (Y n) P)
    (k : 𝓐) (n : ℕ) : Integrable (respMart ν A Y k n) P :=
  integrable_finsetSum' _ fun m _ => integrable_respMart_increment (hA (m + 1)) (hint (m + 1)) k

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
/-- The response martingale `Q k` is adapted to the history filtration `ℱ`: `Q k n`
only depends on the assignments and responses of the first `n` patients. -/
lemma stronglyAdapted_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) :
    StronglyAdapted (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback)
      (respMart ν A Y k) := by
  set ℱ := IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback
  intro n
  unfold respMart
  refine Finset.stronglyMeasurable_sum _ fun m hm => ?_
  rw [Finset.mem_range] at hm
  have hAm : Measurable[ℱ n] (A (m + 1)) :=
    IsAlgEnvSeq.measurable_action_filtration h.measurable_action h.measurable_feedback (by omega)
  have hYm : Measurable[ℱ n] (Y (m + 1)) :=
    IsAlgEnvSeq.measurable_feedback_filtration h.measurable_action h.measurable_feedback (by omega)
  exact (stronglyMeasurable_const.indicator (hAm (measurableSet_singleton k))).mul
    (hYm.stronglyMeasurable.sub stronglyMeasurable_const)

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
/-- **The response martingale is a martingale** (blueprint `lem:Q_martingale`).
For arm `k`, the centered process `Q k` is a martingale for the history filtration
`ℱ n = σ((A i, Y i)_{i ≤ n})`. This is the honest resolution of the
filtration-convention issue: the increment `𝟙{A (i+1)=k}(Y (i+1) - (ν k)[id])` has
zero conditional expectation given `ℱ i` because the response `Y (i+1)` is fresh
given `ℱ i ⊔ σ(A (i+1))` (`condExp_respMart_increment`), even though the assignment
`A (i+1)` is not `ℱ i`-measurable. -/
theorem martingale_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) :
    Martingale (respMart ν A Y k)
      (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P := by
  set ℱ := IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback with hℱ
  have hInt : ∀ n, Integrable (respMart ν A Y k n) P :=
    integrable_respMart h.measurable_action hint k
  have hadapt : StronglyAdapted ℱ (respMart ν A Y k) := stronglyAdapted_respMart h k
  refine martingale_nat hadapt hInt fun i => ?_
  rw [respMart_succ]
  symm
  have hadd := condExp_add (hInt i)
    (integrable_respMart_increment (ν := ν) (h.measurable_action (i + 1)) (hint (i + 1)) k) (ℱ i)
  have hself : P[respMart ν A Y k i | ℱ i] = respMart ν A Y k i :=
    condExp_of_stronglyMeasurable (ℱ.le i) (hadapt i) (hInt i)
  have hincr := condExp_respMart_increment h k i (hint (i + 1))
  rw [← hℱ] at hincr
  filter_upwards [hadd, hincr] with ω ha hin
  rw [ha, Pi.add_apply, congrFun hself ω, hin, Pi.zero_apply, add_zero]

end AlphaRAR
