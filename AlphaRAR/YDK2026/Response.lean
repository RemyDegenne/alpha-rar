/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.LeanMachineLearning.ArmIndicator
import AlphaRAR.LeanMachineLearning.IsAlgEnvSeq
import AlphaRAR.Mathlib.HasCondDistrib
import AlphaRAR.Mathlib.Variance
import AlphaRAR.Mathlib.MartingaleRate
import LeanMachineLearning.SequentialLearning.FiniteActions
import LeanMachineLearning.SequentialLearning.StationaryEnv
import Mathlib.Topology.Separation.CompletelyRegular

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
* `AlphaRAR.memLp_feedback`: `Y n ∈ L²(P)` as soon as every arm's reward distribution is in `L²`.
-/

open MeasureTheory ProbabilityTheory Filter Learning

open scoped ENNReal

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- The centered **response martingale** of arm `k`:
`Q k n = ∑_{m < n} 𝟙{A m = k} (Y m - (ν k)[id])`, summing over patients `0, …, n-1`. Its
increments are the mean-centered responses of the patients assigned to arm `k`. -/
noncomputable def respMart (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (k : 𝓐) (n : ℕ)
    (ω : Ω) : ℝ :=
    ∑ m ∈ Finset.range n, armIndicator A k m ω * (Y m ω - (ν k)[id])

omit [IsMarkovKernel ν] in
/-- Each response-martingale increment is integrable (the indicator is bounded and the
centered response is integrable). -/
@[fun_prop]
lemma integrable_respMart_increment {m : ℕ} (hAmeas : Measurable (A m))
    (hint : Integrable (Y m) P) (k : 𝓐) :
    Integrable (fun ω ↦ armIndicator A k m ω * (Y m ω - (ν k)[id])) P := by
  have heq : (fun ω ↦ armIndicator A k m ω * (Y m ω - (ν k)[id]))
      = {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (ν k)[id]) := by
    funext ω
    simp only [armIndicator, Set.indicator]
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
    P[fun ω ↦ armIndicator A k i ω * (Y i ω - (ν k)[id])
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] 0 := by
  let hA := h.measurable_action
  let hY := h.measurable_feedback
  let G := IsAlgEnvSeq.filtrationAction hA hY i
  set c : Ω → ℝ := armIndicator A k i with hc_def
  let g : Ω → ℝ := fun ω ↦ Y i ω - (ν k)[id]
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
    exact (h.condExp_feedback i hint).sub (EventuallyEq.refl _ _)
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcint hgint
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * g | G] ω = 0
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A i ω) k with hak | hak
  · rw [hak]; ring
  · have : c ω = 0 := by rw [hc_def, armIndicator, Set.indicator_of_notMem (by simpa using hak)]
    rw [this, zero_mul]

/-- **Conditional second moment of the response-martingale increment** (blueprint
`lem:Q_quad_var`, per-step form). Conditioning on the action-augmented filtration
`𝒢 i = filtrationAction i` (the history and the current assignment `A i`), the squared increment
`(𝟙{A i = k}(Y i - θ_k))²` has conditional expectation `𝟙{A i = k} · V_k`, where
`V_k = Var[id; ν k]` is the variance of arm `k`. The indicator squares to itself, and on the event
`{A i = k}` the response's conditional second central moment is exactly the arm variance.
Retaining the (`𝒢`-measurable) indicator is what turns the summed second moments into
`V_k N_{n,k}`. -/
lemma condExp_respMart_increment_sq (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ)
    (hint : Integrable (fun ω ↦ (Y i ω - (ν k)[id]) ^ 2) P) :
    P[fun ω ↦ (armIndicator A k i ω * (Y i ω - (ν k)[id])) ^ 2
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] fun ω ↦ armIndicator A k i ω * Var[id; ν k] := by
  let hA := h.measurable_action
  let hY := h.measurable_feedback
  let G := IsAlgEnvSeq.filtrationAction hA hY i
  set c : Ω → ℝ := armIndicator A k i with hc_def
  set g : Ω → ℝ := fun ω ↦ (Y i ω - (ν k)[id]) ^ 2 with hg_def
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator
      ((IsAlgEnvSeq.measurable_action_filtrationAction' hA hY i) (measurableSet_singleton k))
  -- The squared increment equals `c · g` (the indicator squares to itself).
  have hsq : (fun ω ↦ (c ω * (Y i ω - (ν k)[id])) ^ 2) = fun ω ↦ c ω * g ω := by
    funext ω
    simp only [hg_def]
    by_cases hω : ω ∈ {ω | A i ω = k}
    · simp only [hc_def, armIndicator, Set.indicator_of_mem hω]; ring
    · simp only [hc_def, armIndicator, Set.indicator_of_notMem hω]; ring
  rw [hsq]
  -- `c · g` is integrable (bounded indicator times an integrable square).
  have hcgint : Integrable (fun ω ↦ c ω * g ω) P := by
    have hform : (fun ω ↦ c ω * g ω) = {ω | A i ω = k}.indicator g := by
      funext ω
      simp only [hc_def, armIndicator, Set.indicator]
      by_cases hω : ω ∈ {ω | A i ω = k} <;> simp [hω]
    rw [hform]
    exact hint.indicator (hA i (measurableSet_singleton k))
  -- Conditional expectation of `g = (Y - θ_k)²` given `G` is the arm's second central moment.
  have hcondg : P[g | G] =ᵐ[P] fun ω ↦ ∫ x, (x - (ν k)[id]) ^ 2 ∂(ν (A i ω)) := by
    have hg2 : StronglyMeasurable (fun x : ℝ ↦ (x - (ν k)[id]) ^ 2) :=
      ((continuous_id.sub continuous_const).pow 2).stronglyMeasurable
    exact h.condExp_feedback_comp i hg2 hint
  -- Pull out the `G`-measurable indicator `c`, then evaluate on the arm event.
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcgint hint
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * g | G] ω = _
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A i ω) k with hak | hak
  · rw [hak, variance_id_eq_integral]
  · have hc0 : c ω = 0 := by rw [hc_def, armIndicator, Set.indicator_of_notMem (by simpa using hak)]
    rw [hc0, zero_mul, zero_mul]

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- Successor form: `Q k (n+1) = Q k n + 𝟙{A n = k}(Y n - (ν k)[id])`. -/
lemma respMart_succ (k : 𝓐) (n : ℕ) :
    respMart ν A Y k (n + 1) = respMart ν A Y k n +
      fun ω ↦ armIndicator A k n ω * (Y n ω - (ν k)[id]) := by
  funext ω
  simp only [respMart, Finset.sum_range_succ, Pi.add_apply]

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- The response-martingale increment: `Q k (n+1) - Q k n = 𝟙{A n=k}(Y n - (ν k)[id])`. -/
lemma respMart_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω
      = armIndicator A k n ω * (Y n ω - (ν k)[id]) := by
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
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, respMart_succ_sub, armIndicator]
  rcases eq_or_ne (A n ω) k with hak | hak
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω | A n ω = j} by simp only [Set.mem_ofPred_eq]; rw [hak]; exact hkj)]
    ring
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω | A n ω = k} by simpa using hak)]
    ring

omit [IsMarkovKernel ν] in
/-- Each `Q k n` is integrable (a finite sum of integrable increments). -/
@[fun_prop]
lemma integrable_respMart (hA : ∀ n, Measurable (A n)) (hint : ∀ n, Integrable (Y n) P)
    (k : 𝓐) (n : ℕ) :
    Integrable (respMart ν A Y k n) P :=
  integrable_finsetSum _ fun m _ ↦ integrable_respMart_increment (hA m) (hint m) k

/-- The response martingale `Q k` is adapted to the action-augmented filtration
`𝒢 = filtrationAction`: `Q k n` depends only on the assignments and responses of patients
`0, …, n-1`, all of which are `𝒢 n`-measurable (since `ℱ (n-1) ≤ 𝒢 n`). -/
lemma stronglyAdapted_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) :
    StronglyAdapted (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
      (respMart ν A Y k) := by
  set 𝒢 := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  intro n
  unfold respMart
  refine Finset.stronglyMeasurable_fun_sum _ fun m hm ↦ ?_
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
lemma martingale_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) :
    Martingale (respMart ν A Y k)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  set 𝒢 := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback with h𝒢
  have hInt : ∀ n, Integrable (respMart ν A Y k n) P :=
    integrable_respMart h.measurable_action hint k
  have hadapt : StronglyAdapted 𝒢 (respMart ν A Y k) := stronglyAdapted_respMart h k
  refine martingale_nat hadapt hInt fun i ↦ ?_
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
@[fun_prop]
lemma integrable_respMart_increment_sq {m : ℕ} (k : 𝓐) (hAmeas : Measurable (A m))
    (hcent2 : Integrable (fun ω ↦ (Y m ω - (ν k)[id]) ^ 2) P) :
    Integrable (fun ω ↦ (armIndicator A k m ω * (Y m ω - (ν k)[id])) ^ 2) P := by
  have heq : (fun ω ↦ (armIndicator A k m ω * (Y m ω - (ν k)[id])) ^ 2)
      = {ω | A m ω = k}.indicator (fun ω ↦ (Y m ω - (ν k)[id]) ^ 2) := by
    funext ω
    by_cases hω : ω ∈ {ω | A m ω = k}
    · simp [armIndicator, Set.indicator_of_mem hω]
    · simp [armIndicator, Set.indicator_of_notMem hω]
  rw [heq]
  exact hcent2.indicator (hAmeas (measurableSet_singleton k))

omit [IsMarkovKernel ν] in
/-- Each response-martingale increment is in `L²` when the response is (Condition **A**): a
bounded indicator times the `L²` centered response. -/
lemma memLp_respMart_increment {m : ℕ} (k : 𝓐) (hAmeas : Measurable (A m))
    (hY2 : MemLp (Y m) 2 P) :
    MemLp (fun ω ↦ armIndicator A k m ω * (Y m ω - (ν k)[id])) 2 P := by
  have heq : (fun ω ↦ armIndicator A k m ω * (Y m ω - (ν k)[id]))
      = {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (ν k)[id]) := by
    funext ω
    by_cases hω : ω ∈ {ω | A m ω = k}
    · simp [armIndicator, Set.indicator_of_mem hω]
    · simp [armIndicator, Set.indicator_of_notMem hω]
  rw [heq]
  exact (hY2.sub (memLp_const _)).indicator (hAmeas (measurableSet_singleton k))

omit [IsMarkovKernel ν] in
/-- `Q k n` is in `L²` when the responses are (Condition **A**): a finite sum of `L²` increments. -/
lemma memLp_respMart (hA : ∀ n, Measurable (A n)) (hY2 : ∀ n, MemLp (Y n) 2 P) (k : 𝓐) (n : ℕ) :
    MemLp (respMart ν A Y k n) 2 P := by
  unfold respMart
  exact memLp_finsetSum _ fun m _ ↦ memLp_respMart_increment k (hA m) (hY2 m)

/-- **The quadratic variation of `Q` is `V_k N`** (blueprint `lem:Q_quad_var`).
For the action-augmented filtration `𝒢 = filtrationAction` — for which `Q k` is a martingale
(`martingale_respMart`) — the ordinary predictable quadratic variation of `Q k` is `V_k` times the
assignment count of arm `k`: `⟨Q k⟩_n = V_k N_{n,k}` a.e. The compensator increments are the
`𝒢`-conditional second moments `V_k X_{m,k}` (`condExp_respMart_increment_sq`), which sum to
`V_k N` because the indicator is retained. The only hypothesis is Condition **A**: the responses
are square-integrable (`hY2 : MemLp (Y n) 2 P`); the integrability of `Q`, its increments, and its
increment products (feeding the discrete Doob decomposition) are all derived from it. -/
lemma predQuadVar_respMart_eq [DecidableEq 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (hY2 : ∀ n, MemLp (Y n) 2 P) (n : ℕ) :
    predQuadVar (respMart ν A Y k)
        (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P n
      =ᵐ[P] fun ω ↦ Var[id; ν k] * (pullCount A k n ω : ℝ) := by
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
      = fun ω ↦ (armIndicator A k m ω
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
      =ᵐ[P] fun ω ↦ Var[id; ν k] * armIndicator A k m ω := by
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
        = (pullCount A k n ω : ℝ) + armIndicator A k n ω := by
      rw [pullCount_add_one]
      by_cases hak : A n ω = k
      · rw [if_pos hak, armIndicator, Set.indicator_of_mem (show ω ∈ {ω | A n ω = k} from hak)]
        push_cast; ring
      · rw [if_neg hak, armIndicator, Set.indicator_of_notMem (show ω ∉ {ω | A n ω = k} from hak)]
        push_cast; ring
    change predQuadVar (respMart ν A Y k)
        (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
        P (n + 1) ω = Var[id; ν k] * (pullCount A k (n + 1) ω : ℝ)
    rw [hrc, mul_add]
    have hih' : predQuadVar (respMart ν A Y k)
        (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
        P n ω = Var[id; ν k] * (pullCount A k n ω : ℝ) := hih
    linarith [hk, hih']

/-- **`Q² - ⟨Q⟩` is a martingale** for the action-augmented filtration `𝒢 = filtrationAction`
(`lem:qv_mart` for `Q`). Together with `predQuadVar_respMart_eq` (`⟨Q⟩ = V_k N`) this is the
compensated response martingale. The only hypothesis is Condition **A** (`hY2 : MemLp (Y n) 2 P`),
from which the square-integrability of `Q` is derived. -/
lemma martingale_sq_sub_predQuadVar_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
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
lemma integral_respMart_sq_eq [DecidableEq 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (hY2 : ∀ n, MemLp (Y n) 2 P) (n : ℕ) :
    ∫ ω, respMart ν A Y k n ω ^ 2 ∂P = Var[id; ν k] * ∫ ω, (pullCount A k n ω : ℝ) ∂P := by
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
lemma martingale_respMart_mul (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
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
    ∫ ω, (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2 ∂P ≤ Var[id; ν k] := by
  have hcent2 : Integrable (fun ω ↦ (Y n ω - (ν k)[id]) ^ 2) P :=
    (hY2.sub (memLp_const _)).integrable_sq
  have hdiff : (fun ω ↦ (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2)
      = fun ω ↦ (armIndicator A k n ω * (Y n ω - (ν k)[id])) ^ 2 := by
    funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
  have hGle : IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback n
      ≤ mΩ :=
    (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback).le n
  have hset : MeasurableSet {ω | A n ω = k} :=
    h.measurable_action n (measurableSet_singleton k)
  have hσ2 : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  rw [hdiff, ← integral_condExp hGle,
    integral_congr_ae (condExp_respMart_increment_sq h k n hcent2),
    integral_mul_const (Var[id; ν k])]
  simp only [armIndicator]
  rw [integral_indicator_const (1 : ℝ) hset, smul_eq_mul, mul_one]
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
lemma isBigOpOne_respMart_div_sqrt (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (k : 𝓐) :
    IsBigOpOne P (fun n ω ↦ respMart ν A Y k n ω / √n) := by
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hcent2 : ∀ n, Integrable (fun ω ↦ (Y n ω - (ν k)[id]) ^ 2) P :=
    fun n ↦ ((hY2 n).sub (memLp_const _)).integrable_sq
  -- The martingale increment `ΔQ` squares to the squared centered response.
  have hdiff : ∀ m, (fun ω ↦ (respMart ν A Y k (m + 1) ω - respMart ν A Y k m ω) ^ 2)
      = fun ω ↦ (armIndicator A k m ω
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
  have hσ2 : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  have hinc : ∀ n, ∫ ω, (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2 ∂P
      ≤ Var[id; ν k] := fun n ↦ integral_respMart_increment_sq_le h k n (hY2 n)
  exact isBigOpOne_martingale_div_sqrt hM hM2 hM0 (Var[id; ν k]) hσ2 hd2 hprod hinc

end AlphaRAR
