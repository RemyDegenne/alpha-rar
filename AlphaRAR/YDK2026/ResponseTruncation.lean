/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.TsumMeasureIoi
public import AlphaRAR.Mathlib.LILTruncation
public import AlphaRAR.YDK2026.Response
public meta import LeanSpec

/-!
# The truncated response martingale

For the finite-variance law of the iterated logarithm (blueprint `lem:lil_truncation`) we need the
response martingale with *truncated* increments. Both the response martingale and its truncated
version are instances of a **general functional response martingale**
`genRespMart ν A Y k g n = ∑_{m<n} 𝟙{A m = k} (g m (Y m) - (ν k)[g m])`,
parametrised by a sequence of functions `g : ℕ → ℝ → ℝ`. The martingale property holds for any
`g` (with `g n` measurable and `g n (Y n)` integrable), by exactly the argument for `respMart`
(the `g = fun _ ↦ id` case): the increment's conditional mean given `filtrationAction i` is
`𝟙{A i = k}((ν (A i))[g i] - (ν k)[g i]) = 0` on `{A i = k}`.

The **truncated response martingale** is the instance
`g i = truncation (· - ν.means k) (√i)` (blueprint `lem:trunc_mart`, the centred truncated
increments `ξ̃_i = truncation(ξ_i, √i) - m_i`).

## Main results

* `AlphaRAR.martingale_genRespMart`: the general functional response martingale is a martingale.
* `AlphaRAR.martingale_truncRespMart`: the truncated response martingale is a martingale
  (blueprint `lem:trunc_mart`).
* `AlphaRAR.predQuadVar_genRespMart_eq`: its quadratic variation is the weighted assignment sum
  `∑_{i<n} variance (g i) (ν k) · 𝟙{A i = k}`.
* `AlphaRAR.predQuadVar_truncRespMart_eq`: the truncated case `⟨M̃⟩_n = ∑_{i<n} v_i 𝟙{A i = k}`
  (blueprint `lem:trunc_qv`).
* `AlphaRAR.abs_truncMean_le`, `AlphaRAR.abs_truncDrift_le`: `|m_i| ≤ V_k/√i` and the drift bound
  `|Dr_n| ≤ 2 V_k √n` (blueprint `lem:trunc_drift`).
* `AlphaRAR.truncVar_le_variance`, `AlphaRAR.predQuadVar_truncRespMart_le`: `v_i ≤ V_k` and hence
  `⟨M̃⟩_n ≤ V_k N_{n,k}` (blueprint `lem:trunc_qv_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Real

open scoped ENNReal

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- The **general functional response martingale** of arm `k` with increment functions
`g : ℕ → ℝ → ℝ`: `∑_{m<n} 𝟙{A m = k} (g m (Y m) - (ν k)[g m])`. The response martingale
`respMart` is the case `g = fun _ ↦ id`; the truncated one is `g i = truncation(· - θ_k, √i)`. -/
noncomputable def genRespMart (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (k : 𝓐)
    (g : ℕ → ℝ → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ m ∈ Finset.range n, fun ω ↦
    actionIndicator A k m ω * (g m (Y m ω) - (ν k)[g m])

omit [IsMarkovKernel ν] in
/-- Each general-functional increment is integrable. -/
@[fun_prop]
lemma integrable_genRespMart_increment {m : ℕ} (hAmeas : Measurable (A m)) {g : ℝ → ℝ}
    (hint : Integrable (fun ω ↦ g (Y m ω)) P) (k : 𝓐) :
    Integrable (fun ω ↦ actionIndicator A k m ω
      * (g (Y m ω) - (ν k)[g])) P := by
  have heq : (fun ω ↦ actionIndicator A k m ω * (g (Y m ω) - (ν k)[g]))
      = {ω | A m ω = k}.indicator (fun ω ↦ g (Y m ω) - (ν k)[g]) := by
    funext ω
    simp only [actionIndicator, Set.indicator]
    by_cases hω : ω ∈ {ω | A m ω = k} <;> simp [hω]
  rw [heq]
  exact (hint.sub (integrable_const _)).indicator (hAmeas (measurableSet_singleton k))

/-- **The general-functional increment has zero conditional expectation given `𝒢`.**
For any measurable `g` with `g (Y i)` integrable, the increment `𝟙{A i = k}(g (Y i) - (ν k)[g])`
vanishes in conditional mean given `filtrationAction i`: pulling out the `𝒢`-measurable indicator
and using `condExp_feedback_comp_stationaryEnv` (`𝔼[g (Y i) | 𝒢 i] = (ν (A i))[g]`), the value on
`{A i = k}` is `(ν k)[g] - (ν k)[g] = 0`. -/
lemma condExp_genRespMart_increment (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ)
    {g : ℝ → ℝ} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y i ω)) P) :
    P[fun ω ↦ actionIndicator A k i ω * (g (Y i ω) - (ν k)[g])
        | h.filtrationAction i]
      =ᵐ[P] 0 := by
  let hA := h.measurable_action
  let G := h.filtrationAction i
  set c : Ω → ℝ := actionIndicator A k i with hc_def
  let gg : Ω → ℝ := fun ω ↦ g (Y i ω) - (ν k)[g]
  have hGle : G ≤ mΩ := h.filtrationAction.le i
  have hAG : Measurable[G] (A i) :=
    h.adapted_action_filtrationAction i
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator (hAG (measurableSet_singleton k))
  have hggint : Integrable gg P := hint.sub (integrable_const _)
  have hcint : Integrable (fun ω ↦ c ω * gg ω) P :=
    integrable_genRespMart_increment (hA i) hint k
  have hcondg : P[gg | G] =ᵐ[P] fun ω ↦ (ν (A i ω))[g] - (ν k)[g] := by
    refine (condExp_sub hint (integrable_const _) _).trans ?_
    rw [condExp_const hGle]
    exact (h.condExp_feedback_comp_stationaryEnv i hg hint).sub (EventuallyEq.refl _ _)
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcint hggint
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * gg | G] ω = 0
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A i ω) k with hak | hak
  · rw [hak]; ring
  · have : c ω = 0 := by rw [hc_def, actionIndicator, Set.indicator_of_notMem (by simpa using hak)]
    rw [this, zero_mul]

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- Successor form of the general-functional martingale. -/
lemma genRespMart_succ (k : 𝓐) (g : ℕ → ℝ → ℝ) (n : ℕ) :
    genRespMart ν A Y k g (n + 1) = genRespMart ν A Y k g n + fun ω ↦
      actionIndicator A k n ω * (g n (Y n ω) - (ν k)[g n]) := by
  funext ω
  simp only [genRespMart, Finset.sum_range_succ, Pi.add_apply]

omit [IsMarkovKernel ν] in
/-- The general-functional martingale is integrable. -/
@[fun_prop]
lemma integrable_genRespMart (hA : ∀ n, Measurable (A n)) {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, Integrable (fun ω ↦ g n (Y n ω)) P) (k : 𝓐) (n : ℕ) :
    Integrable (genRespMart ν A Y k g n) P :=
  integrable_finsetSum' _ fun m _ ↦ integrable_genRespMart_increment (hA m) (hint m) k

/-- The general-functional martingale is adapted to `filtrationAction`. -/
lemma stronglyAdapted_genRespMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    {g : ℕ → ℝ → ℝ} (hg : ∀ n, StronglyMeasurable (g n)) :
    StronglyAdapted h.filtrationAction
      (genRespMart ν A Y k g) := by
  set 𝒢 := h.filtrationAction
  intro n
  unfold genRespMart
  refine Finset.stronglyMeasurable_sum _ fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  have hAm : Measurable[𝒢 n] (A m) :=
    h.adapted_action_filtrationAction.measurable_le hm.le
  have hYm : Measurable[𝒢 n] (Y m) :=
    h.measurable_feedback_filtrationAction_of_lt hm
  exact (stronglyMeasurable_const.indicator (hAm (measurableSet_singleton k))).mul
    (((hg m).mono le_rfl).comp_measurable hYm |>.sub stronglyMeasurable_const)

/-- **The general functional response martingale is a martingale** for `filtrationAction`.
For any increment functions `g` (with `g n` measurable and `g n (Y n)` integrable), by
`condExp_genRespMart_increment`. -/
@[specifies genRespMart "the martingale property holds for *arbitrary* increment functions `g`, \
with no hypothesis beyond measurability and integrability — so subtracting the kernel mean \
`(ν k)[g m]` is the right centring for every instance, `g = id` and `g = truncation` alike"]
lemma martingale_genRespMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    {g : ℕ → ℝ → ℝ} (hg : ∀ n, StronglyMeasurable (g n))
    (hint : ∀ n, Integrable (fun ω ↦ g n (Y n ω)) P) (k : 𝓐) :
    Martingale (genRespMart ν A Y k g)
      h.filtrationAction P := by
  set 𝒢 := h.filtrationAction with h𝒢
  have hInt : ∀ n, Integrable (genRespMart ν A Y k g n) P :=
    integrable_genRespMart h.measurable_action hint k
  have hadapt : StronglyAdapted 𝒢 (genRespMart ν A Y k g) := stronglyAdapted_genRespMart h k hg
  refine martingale_nat hadapt hInt fun i ↦ ?_
  rw [genRespMart_succ]
  symm
  have hadd := condExp_add (hInt i)
    (integrable_genRespMart_increment (ν := ν) (h.measurable_action i) (hint i) k) (𝒢 i)
  have hself : P[genRespMart ν A Y k g i | 𝒢 i] = genRespMart ν A Y k g i :=
    condExp_of_stronglyMeasurable (𝒢.le i) (hadapt i) (hInt i)
  have hincr := condExp_genRespMart_increment h k i (hg i) (hint i)
  rw [← h𝒢] at hincr
  filter_upwards [hadd, hincr] with ω ha hin
  rw [ha, Pi.add_apply, congrFun hself ω, hin, Pi.zero_apply, add_zero]

/-- **Conditional second moment of the general-functional increment.** Conditioning on
`filtrationAction i`, `(𝟙{A i = k}(g (Y i) - (ν k)[g]))²` has conditional expectation
`𝟙{A i = k} · variance g (ν k)`: the indicator squares to itself and pulls out, and on `{A i = k}`
the conditional second central moment of `g` is `∫ (g - (ν k)[g])² ∂(ν k) = variance g (ν k)`. -/
lemma condExp_genRespMart_increment_sq (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (i : ℕ) {g : ℝ → ℝ} (hg : StronglyMeasurable g)
    (hcent2 : MemLp (fun ω ↦ g (Y i ω)) 2 P) :
    P[fun ω ↦ (actionIndicator A k i ω * (g (Y i ω) - (ν k)[g])) ^ 2
        | h.filtrationAction i]
      =ᵐ[P] fun ω ↦ actionIndicator A k i ω * variance g (ν k) := by
  have hcent2' : Integrable (fun ω ↦ (g (Y i ω) - (ν k)[g]) ^ 2) P :=
    (hcent2.sub (memLp_const _)).integrable_sq
  let hA := h.measurable_action
  let G := h.filtrationAction i
  set c : Ω → ℝ := actionIndicator A k i with hc_def
  set gg : Ω → ℝ := fun ω ↦ (g (Y i ω) - (ν k)[g]) ^ 2 with hgg_def
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator
      ((h.adapted_action_filtrationAction i) (measurableSet_singleton k))
  have hsq : (fun ω ↦ (c ω * (g (Y i ω) - (ν k)[g])) ^ 2) = fun ω ↦ c ω * gg ω := by
    funext ω
    simp only [hgg_def]
    by_cases hω : ω ∈ {ω | A i ω = k}
    · simp only [hc_def, actionIndicator, Set.indicator_of_mem hω]; ring
    · simp only [hc_def, actionIndicator, Set.indicator_of_notMem hω]; ring
  rw [hsq]
  have hcgint : Integrable (fun ω ↦ c ω * gg ω) P := by
    have hform : (fun ω ↦ c ω * gg ω) = {ω | A i ω = k}.indicator gg := by
      funext ω
      simp only [hc_def, actionIndicator, Set.indicator]
      by_cases hω : ω ∈ {ω | A i ω = k} <;> simp [hω]
    rw [hform]
    exact hcent2'.indicator (hA i (measurableSet_singleton k))
  have hcondg : P[gg | G] =ᵐ[P] fun ω ↦ ∫ x, (g x - (ν k)[g]) ^ 2 ∂(ν (A i ω)) := by
    have hg2 : StronglyMeasurable (fun x : ℝ ↦ (g x - (ν k)[g]) ^ 2) :=
      (hg.sub stronglyMeasurable_const).pow 2
    exact h.condExp_feedback_comp_stationaryEnv i hg2 hcent2'
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcgint hcent2'
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * gg | G] ω = _
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A i ω) k with hak | hak
  · rw [hak, ← variance_eq_integral hg.aemeasurable]
  · have hc0 : c ω = 0 := by
      rw [hc_def, actionIndicator, Set.indicator_of_notMem (by simpa using hak)]
    rw [hc0, zero_mul, zero_mul]

omit [IsMarkovKernel ν] in
/-- Each general-functional increment is in `L²` when `g n (Y n)` is. -/
lemma memLp_genRespMart_increment {m : ℕ} (k : 𝓐) (hAmeas : Measurable (A m)) {g : ℝ → ℝ}
    (hg2 : MemLp (fun ω ↦ g (Y m ω)) 2 P) :
    MemLp (fun ω ↦ actionIndicator A k m ω
      * (g (Y m ω) - (ν k)[g])) 2 P := by
  have heq : (fun ω ↦ actionIndicator A k m ω
        * (g (Y m ω) - (ν k)[g]))
      = {ω | A m ω = k}.indicator (fun ω ↦ g (Y m ω) - (ν k)[g]) := by
    funext ω
    by_cases hω : ω ∈ {ω | A m ω = k}
    · simp [actionIndicator, Set.indicator_of_mem hω]
    · simp [actionIndicator, Set.indicator_of_notMem hω]
  rw [heq]
  exact (hg2.sub (memLp_const _)).indicator (hAmeas (measurableSet_singleton k))

omit [IsMarkovKernel ν] in
/-- `genRespMart` is in `L²` when each increment function is. -/
lemma memLp_genRespMart (hA : ∀ n, Measurable (A n)) {g : ℕ → ℝ → ℝ}
    (hg2 : ∀ n, MemLp (fun ω ↦ g n (Y n ω)) 2 P) (k : 𝓐) (n : ℕ) :
    MemLp (genRespMart ν A Y k g n) 2 P := by
  unfold genRespMart
  exact memLp_finsetSum' _ fun m _ ↦ memLp_genRespMart_increment k (hA m) (hg2 m)

/-- **The quadratic variation of the general-functional martingale** is the weighted assignment
sum `⟨M⟩_n = ∑_{i<n} variance (g i) (ν k) · 𝟙{A i = k}`. For `respMart` (`g = id`, constant variance
`Var[id; ν k]`) this collapses to `V_k · N`; for the truncated martingale the varying variances
`v_i = variance (g i) (ν k)` are retained (blueprint `lem:trunc_qv`). -/
@[specifies genRespMart "the clock is again the arm's own indicator: variance accrues only at \
rounds where arm `k` is pulled, at the step-`i` rate `variance (g i) (ν k)`. Specializing `g = id` \
recovers `⟨respMart⟩ = V_k N`, which is how the general form is checked against the concrete one"]
lemma predQuadVar_genRespMart_eq (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    {g : ℕ → ℝ → ℝ} (hg : ∀ n, StronglyMeasurable (g n))
    (hg2 : ∀ n, MemLp (fun ω ↦ g n (Y n ω)) 2 P) (n : ℕ) :
    predQuadVar (genRespMart ν A Y k g)
        h.filtrationAction P n
      =ᵐ[P] fun ω ↦ ∑ i ∈ Finset.range n,
        variance (g i) (ν k) * actionIndicator A k i ω := by
  have hint : ∀ n, Integrable (fun ω ↦ g n (Y n ω)) P := fun n ↦ (hg2 n).integrable one_le_two
  have hQ2 : ∀ n, MemLp (genRespMart ν A Y k g n) 2 P :=
    memLp_genRespMart h.measurable_action hg2 k
  have hprod : ∀ n, Integrable (genRespMart ν A Y k g n
      * (genRespMart ν A Y k g (n + 1) - genRespMart ν A Y k g n)) P := fun n ↦
    integrable_mul_increment (hQ2 n) (hQ2 (n + 1))
  have hd2 : ∀ m, MemLp
      (fun ω ↦ genRespMart ν A Y k g (m + 1) ω - genRespMart ν A Y k g m ω) 2 P :=
    fun m ↦ memLp_increment (hQ2 m) (hQ2 (m + 1))
  have hM := martingale_genRespMart h hg hint k
  have hdiff : ∀ m, (fun ω ↦ (genRespMart ν A Y k g (m + 1) ω - genRespMart ν A Y k g m ω) ^ 2)
      = fun ω ↦ (actionIndicator A k m ω
        * (g m (Y m ω) - (ν k)[g m])) ^ 2 := by
    intro m; funext ω; rw [genRespMart_succ]; simp only [Pi.add_apply]; ring
  have hkey : ∀ m, predQuadVar (genRespMart ν A Y k g)
          h.filtrationAction P (m + 1)
        - predQuadVar (genRespMart ν A Y k g)
          h.filtrationAction P m
      =ᵐ[P] fun ω ↦ variance (g m) (ν k) * actionIndicator A k m ω := by
    intro m
    have h1 := predQuadVar_succ_sub_eq hM m (hd2 m) (hprod m)
    rw [hdiff m] at h1
    refine h1.trans ?_
    refine (condExp_genRespMart_increment_sq h k m (hg m) (hg2 m)).trans ?_
    filter_upwards with ω; ring
  induction n with
  | zero => filter_upwards with ω; simp [predQuadVar_zero]
  | succ n ih =>
    filter_upwards [ih, hkey n] with ω hih hk
    simp only [Pi.sub_apply] at hk
    rw [Finset.sum_range_succ]
    have hih' : predQuadVar (genRespMart ν A Y k g)
        h.filtrationAction P n ω
          = ∑ i ∈ Finset.range n,
            variance (g i) (ν k) * actionIndicator A k i ω := hih
    linarith [hk, hih']

/-- The **truncated response martingale** of arm `k`: the general functional martingale with
`g i = truncation(· - θ_k, √i)`, i.e. increments `𝟙{A i = k}(truncation(Y i - θ_k, √i) - m_i)`
with `m_i = (ν k)[truncation(· - θ_k, √i)]` (blueprint `lem:trunc_mart`). -/
noncomputable def truncRespMart (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (k : 𝓐) :
    ℕ → Ω → ℝ :=
  genRespMart ν A Y k (fun i ↦ truncation (fun y ↦ y - ν.means k) (√i))

/-- `truncation (· - θ) A` is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_truncation_sub_const (θ A : ℝ) :
    StronglyMeasurable (truncation (fun y : ℝ ↦ y - θ) A) :=
  (stronglyMeasurable_id.indicator measurableSet_Ioc).comp_measurable (measurable_id.sub_const θ)

/-- The truncated increment function `truncation (· - θ) (√i)` applied to `Y i` is integrable
(it is bounded by `√i`). -/
@[fun_prop]
lemma integrable_truncation_comp (hint : ∀ n, Integrable (Y n) P) (θ : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ truncation (fun y : ℝ ↦ y - θ) (√n) (Y n ω)) P := by
  have haesm : AEStronglyMeasurable
      (fun ω ↦ truncation (fun y : ℝ ↦ y - θ) (√n) (Y n ω)) P :=
    ((stronglyMeasurable_truncation_sub_const θ (√n)).measurable.comp_aemeasurable
      (hint n).1.aemeasurable).aestronglyMeasurable
  refine Integrable.mono' (integrable_const (√n)) haesm ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (abs_truncation_le_bound _ _ _).trans (le_of_eq (abs_of_nonneg (sqrt_nonneg _)))

/-- The truncated increment function `truncation (· - θ) (√n) ∘ Y n` is in `L²` (it is bounded by
`√n`). -/
lemma memLp_truncation_comp (hint : ∀ n, Integrable (Y n) P) (θ : ℝ) (n : ℕ) :
    MemLp (fun ω ↦ truncation (fun y : ℝ ↦ y - θ) (√n) (Y n ω)) 2 P := by
  have haesm : AEStronglyMeasurable
      (fun ω ↦ truncation (fun y : ℝ ↦ y - θ) (√n) (Y n ω)) P :=
    ((stronglyMeasurable_truncation_sub_const θ (√n)).measurable.comp_aemeasurable
      (hint n).1.aemeasurable).aestronglyMeasurable
  refine MemLp.of_bound haesm (√n) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (abs_truncation_le_bound _ _ _).trans (le_of_eq (abs_of_nonneg (sqrt_nonneg _)))

/-- **The truncated response martingale is a martingale** (blueprint `lem:trunc_mart`).
Instance of `martingale_genRespMart` with `g i = truncation(· - θ_k, √i)`. -/
lemma martingale_truncRespMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) :
    Martingale (truncRespMart ν A Y k)
      h.filtrationAction P :=
  martingale_genRespMart h (fun _ ↦ stronglyMeasurable_truncation_sub_const _ _)
    (fun n ↦ integrable_truncation_comp hint _ n) k

/-- The per-step variance of the truncated response martingale:
`v_i = variance (truncation(· - θ_k, √i)) (ν k)`, the variance of the truncated centred response
`ξ̃_i` under the arm-`k` reward law. -/
noncomputable def truncVar (ν : Kernel 𝓐 ℝ) (k : 𝓐) (i : ℕ) : ℝ :=
  variance (truncation (fun y ↦ y - ν.means k) (√i)) (ν k)

omit [MeasurableSingletonClass 𝓐] in
/-- **The truncated variance is at most the arm variance**: `v_i ≤ V_k`. Truncation reduces
absolute value (`|truncation ξ A| ≤ |ξ|`), so the second moment drops, and variance is at most the
second moment. Gives the upper bound `⟨M̃⟩ ≤ V_k N` needed for the LIL block argument. -/
@[specifies truncVar "places the per-step truncated variance below the untruncated arm variance \
`V_k`, uniformly in `i` — the fact that lets every `truncVar` be replaced by `V_k` in a bound"]
lemma truncVar_le_variance (k : 𝓐) (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) (i : ℕ) :
    truncVar ν k i ≤ Var[id; ν k] := by
  have : IsProbabilityMeasure (ν k) := inferInstance
  have hgSM : StronglyMeasurable (truncation (fun y ↦ y - ν.means k) (√i)) :=
    stronglyMeasurable_truncation_sub_const _ _
  have hgmem : MemLp (truncation (fun y ↦ y - ν.means k) (√i)) 2 (ν k) :=
    MemLp.of_bound hgSM.aestronglyMeasurable (√i) (by
      filter_upwards with x; rw [Real.norm_eq_abs]
      exact (abs_truncation_le_bound _ _ _).trans (le_of_eq (abs_of_nonneg (sqrt_nonneg _))))
  rw [truncVar]
  refine (variance_le_expectation_sq hgSM.aestronglyMeasurable).trans ?_
  rw [variance_id_eq_integral]
  refine integral_mono hgmem.integrable_sq (hν2.sub (memLp_const _)).integrable_sq (fun x ↦ ?_)
  simp only [Pi.pow_apply]
  calc (truncation (fun y ↦ y - ν.means k) (√i) x) ^ 2
      = |truncation (fun y ↦ y - ν.means k) (√i) x| ^ 2 := (sq_abs _).symm
    _ ≤ |x - ν.means k| ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (abs_nonneg _) (abs_truncation_le_abs_self _ _ _)
    _ = (x - ν.means k) ^ 2 := sq_abs _

/-- **The quadratic variation of the truncated response martingale** (blueprint `lem:trunc_qv`):
`⟨M̃⟩_n = ∑_{i<n} v_i 𝟙{A i = k}`, with `v_i = truncVar ν k i`. Instance of
`predQuadVar_genRespMart_eq`. -/
lemma predQuadVar_truncRespMart_eq (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (n : ℕ) :
    predQuadVar (truncRespMart ν A Y k)
        h.filtrationAction P n
      =ᵐ[P] fun ω ↦ ∑ i ∈ Finset.range n,
        truncVar ν k i * actionIndicator A k i ω :=
  predQuadVar_genRespMart_eq h k (fun _ ↦ stronglyMeasurable_truncation_sub_const _ _)
    (fun n ↦ memLp_truncation_comp hint _ n) n

/-- **The truncated quadratic variation is bounded by `V_k N`**: `⟨M̃⟩_n ≤ V_k · N_{n,k}` a.e.,
since each `v_i ≤ V_k` (`truncVar_le_variance`). This is the `⟨M̃⟩ ≲ σ² N` bound the LIL block
argument needs (the upper half of blueprint `lem:trunc_var_conv`). -/
@[specifies truncRespMart "truncation buys the increment bound without paying in variance: `⟨M̃⟩` \
is still dominated by the untruncated `V_k N_{n,k}`"]
lemma predQuadVar_truncRespMart_le (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) (n : ℕ) :
    predQuadVar (truncRespMart ν A Y k)
        h.filtrationAction P n
      ≤ᵐ[P] fun ω ↦ Var[id; ν k]
        * ∑ i ∈ Finset.range n, actionIndicator A k i ω := by
  filter_upwards [predQuadVar_truncRespMart_eq h hint k n] with ω hω
  rw [hω, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  exact mul_le_mul_of_nonneg_right (truncVar_le_variance k hν2 i)
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω)

/-- The truncated mean `m_i = (ν k)[truncation(· - θ_k, √i)] = ∫ truncation(x - θ_k, √i) ∂(ν k)`,
the deterministic centering of the truncated increment. -/
noncomputable def truncMean (ν : Kernel 𝓐 ℝ) (k : 𝓐) (i : ℕ) : ℝ :=
  ∫ x, truncation (fun y ↦ y - ν.means k) (√i) x ∂(ν k)

omit [MeasurableSingletonClass 𝓐] in
/-- **Bound on the truncated mean** in the LML framework: `|m_i| ≤ V_k/√i`. Instance of the
abstract `abs_integral_truncation_le` applied to the centred reward `x - θ_k` under `ν_k`
(centred since `θ_k = ν.means k`, with `∫ (x-θ_k)² ∂ν_k = V_k = Var[id; ν k]`). -/
@[specifies truncMean "the bias truncation introduces is `O(1/√i)`, not `O(1)`: truncating an \
already-centred variable leaves a mean that decays. This is the estimate that makes the \
accumulated drift negligible"]
lemma abs_truncMean_le (k : 𝓐) (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) (i : ℕ) :
    |truncMean ν k i| ≤ Var[id; ν k] / √i := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi; simp [truncMean, sqrt_zero, truncation_zero]
  · have hipos : (0 : ℝ) < √i := sqrt_pos.mpr (by exact_mod_cast hi)
    have hintX : Integrable (fun x ↦ x - ν.means k) (ν k) :=
      (hν2.integrable one_le_two).sub (integrable_const _)
    have hX2 : MemLp (fun x ↦ x - ν.means k) 2 (ν k) := hν2.sub (memLp_const _)
    have hX0 : ∫ x, (x - ν.means k) ∂(ν k) = 0 := by
      rw [integral_sub (hν2.integrable one_le_two) (integrable_const _), integral_const]
      simp [Kernel.means_apply]
    have h := abs_integral_truncation_le hX2 hX0 hipos
    rwa [Kernel.means_apply, ← variance_id_eq_integral] at h

/-- The truncated **drift** process `Dr_n = ∑_{i<n} m_i 𝟙{A i = k}` (blueprint `lem:trunc_drift`),
the accumulated centering. Deterministic coefficients `m_i` times the arm-`k` indicators. -/
noncomputable def truncDrift (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ) : Ω → ℝ :=
  ∑ i ∈ Finset.range n, fun ω ↦ truncMean ν k i * actionIndicator A k i ω

omit [MeasurableSingletonClass 𝓐] in
/-- **The drift is `O(√n)`** (blueprint `lem:trunc_drift`): `|Dr_n| ≤ 2 V_k √n`, from
`|m_i| ≤ V_k/√i` (`abs_truncMean_le`) and `∑_{i<n} 1/√i ≤ 2√n` (`sum_one_div_sqrt_le`). -/
@[specifies truncDrift "what the accumulated bias costs: `O(√n)`, hence negligible against the \
`√(n log log n)` scale the LIL works at — the reason the drift can be discarded"]
lemma abs_truncDrift_le (k : 𝓐) (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) (n : ℕ) (ω : Ω) :
    |truncDrift ν A k n ω| ≤ 2 * Var[id; ν k] * √n := by
  have harm : 0 ≤ Var[id; ν k] := variance_nonneg _ _
  have hval : truncDrift ν A k n ω
      = ∑ i ∈ Finset.range n, truncMean ν k i * actionIndicator A k i ω :=
    by rw [truncDrift, Finset.sum_apply]
  rw [hval]
  have hterm : ∀ i ∈ Finset.range n,
      |truncMean ν k i * actionIndicator A k i ω|
        ≤ Var[id; ν k] / √i := by
    intro i _
    rw [abs_mul]
    have hind : |actionIndicator A k i ω| ≤ 1 := by
      by_cases hω : ω ∈ {ω | A i ω = k}
      · rw [actionIndicator, Set.indicator_of_mem hω]; norm_num
      · rw [actionIndicator, Set.indicator_of_notMem hω]; norm_num
    calc |truncMean ν k i| * |actionIndicator A k i ω|
        ≤ |truncMean ν k i| * 1 := by
          apply mul_le_mul_of_nonneg_left hind (abs_nonneg _)
      _ = |truncMean ν k i| := mul_one _
      _ ≤ Var[id; ν k] / √i := abs_truncMean_le k hν2 i
  calc |∑ i ∈ Finset.range n, truncMean ν k i * actionIndicator A k i ω|
      ≤ ∑ i ∈ Finset.range n,
          |truncMean ν k i * actionIndicator A k i ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, Var[id; ν k] / √i := Finset.sum_le_sum hterm
    _ = Var[id; ν k] * ∑ i ∈ Finset.range n, 1 / √i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ (mul_one_div _ _).symm
    _ ≤ Var[id; ν k] * (2 * √n) :=
        mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le n) harm
    _ = 2 * Var[id; ν k] * √n := by ring

/-! ### Core: the growing-increment LIL for the truncated martingale -/

omit [MeasurableSingletonClass 𝓐] in
/-- **Crude uniform bound on the truncated mean**: `|m_i| ≤ √i`. The truncated increment is bounded
by `√i` pointwise (`abs_truncation_le_bound`) and `ν k` is a probability measure, so its mean is
too. Unlike the sharper `abs_truncMean_le` (`V_k/√i`, used for the drift), this uniform bound is
what controls the martingale increments in the block LIL. -/
lemma abs_truncMean_le_sqrt (k : 𝓐) (i : ℕ) : |truncMean ν k i| ≤ √i := by
  have : IsProbabilityMeasure (ν k) := inferInstance
  have hbound : ∀ x : ℝ, |truncation (fun y ↦ y - ν.means k) (√i) x| ≤ √i :=
    fun x ↦ (abs_truncation_le_bound _ _ _).trans (le_of_eq (abs_of_nonneg (sqrt_nonneg _)))
  have hgint : Integrable (truncation (fun y ↦ y - ν.means k) (√i)) (ν k) :=
    Integrable.mono' (integrable_const (√i))
      (stronglyMeasurable_truncation_sub_const _ _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hbound x)
  rw [truncMean]
  calc |∫ x, truncation (fun y ↦ y - ν.means k) (√i) x ∂(ν k)|
      ≤ ∫ x, |truncation (fun y ↦ y - ν.means k) (√i) x| ∂(ν k) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _x, √i ∂(ν k) := integral_mono hgint.abs (integrable_const _) hbound
    _ = √i := by rw [integral_const]; simp

omit [MeasurableSingletonClass 𝓐] in
/-- **Increment bound for the truncated martingale**: `|Δ M̃_i| ≤ 2√i`. The increment is
`𝟙{A i = k}(truncation(Y_i - θ_k, √i) - m_i)`, and both the truncated response and its mean `m_i`
are bounded by `√i` (`abs_truncation_le_bound`, `abs_truncMean_le_sqrt`). The bound *grows* with
`i`, which is why the block LIL must stop the martingale at each dyadic horizon rather than use a
single increment bound. -/
@[specifies truncRespMart "reads off the truncation level: increments are bounded by `2√i`, which \
is the only reason to truncate at all, and shows the level *grows* with `i` rather than being \
uniform"]
lemma abs_truncRespMart_increment_le (k : 𝓐) (i : ℕ) (ω : Ω) :
    |truncRespMart ν A Y k (i + 1) ω - truncRespMart ν A Y k i ω| ≤ 2 * √i := by
  have hsucc := congrFun (genRespMart_succ (ν := ν) (A := A) (Y := Y) k
    (fun j ↦ truncation (fun y ↦ y - ν.means k) (√j)) i) ω
  have hincr : truncRespMart ν A Y k (i + 1) ω - truncRespMart ν A Y k i ω
      = actionIndicator A k i ω
        * (truncation (fun y ↦ y - ν.means k) (√i) (Y i ω) - truncMean ν k i) := by
    simp only [truncRespMart, Pi.add_apply] at hsucc ⊢
    rw [hsucc, add_sub_cancel_left]; rfl
  rw [hincr, abs_mul]
  have hind : |actionIndicator A k i ω| ≤ 1 := by
    by_cases hω : ω ∈ {ω | A i ω = k}
    · rw [actionIndicator, Set.indicator_of_mem hω]; norm_num
    · rw [actionIndicator, Set.indicator_of_notMem hω]; norm_num
  have habs : |truncation (fun y ↦ y - ν.means k) (√i) (Y i ω) - truncMean ν k i|
      ≤ √i + √i := by
    calc |truncation (fun y ↦ y - ν.means k) (√i) (Y i ω) - truncMean ν k i|
        = |truncation (fun y ↦ y - ν.means k) (√i) (Y i ω) + -truncMean ν k i| := by
          rw [sub_eq_add_neg]
      _ ≤ |truncation (fun y ↦ y - ν.means k) (√i) (Y i ω)| + |-truncMean ν k i| :=
          abs_add_le _ _
      _ ≤ √i + √i := by
          rw [abs_neg]
          exact add_le_add ((abs_truncation_le_bound _ _ _).trans
            (le_of_eq (abs_of_nonneg (sqrt_nonneg _)))) (abs_truncMean_le_sqrt k i)
  calc |actionIndicator A k i ω|
        * |truncation (fun y ↦ y - ν.means k) (√i) (Y i ω) - truncMean ν k i|
      ≤ 1 * (√i + √i) :=
        mul_le_mul hind habs (abs_nonneg _) zero_le_one
    _ = 2 * √i := by ring

/-! ### The truncated martingale as an instance of the general `√i`-growing-increment LIL

The truncated response martingale `M̃ = truncRespMart` is an `L²` martingale (for the
action-augmented filtration `𝒢`) starting at `0`, with `√i`-growing increments `|ΔM̃_i| ≤ 2√i` and
linear quadratic variation `⟨M̃⟩_n ≤ V_k n`. It therefore satisfies the hypotheses of the general
finite-variance LIL of `AlphaRAR/Mathlib/LILTruncation.lean`, from which the block bounds below
are read off directly (with increment scale `a = 2` and variance scale `v = V_k = Var[id; ν k]`). -/

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The truncated response martingale starts at `0`. -/
lemma truncRespMart_zero_ae (k : 𝓐) : truncRespMart ν A Y k 0 =ᵐ[P] 0 := by
  have h0 : truncRespMart ν A Y k 0 = (0 : Ω → ℝ) := by simp [truncRespMart, genRespMart]
  filter_upwards with ω; rw [h0]

/-- The truncated response martingale is square-integrable. -/
lemma integrable_truncRespMart_sq (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (n : ℕ) :
    MemLp (truncRespMart ν A Y k n) 2 P :=
  memLp_genRespMart (g := fun i ↦ truncation (fun y ↦ y - ν.means k) (√i))
    h.measurable_action (fun m ↦ memLp_truncation_comp hint (ν.means k) m) k n

omit [MeasurableSingletonClass 𝓐] [IsProbabilityMeasure P] in
/-- The truncated increments obey the `√i`-growing bound `|ΔM̃_i| ≤ 2√i` a.e.
(`abs_truncRespMart_increment_le`). -/
lemma ae_abs_truncRespMart_increment_le (k : 𝓐) (i : ℕ) :
    ∀ᵐ ω ∂P,
      |truncRespMart ν A Y k (i + 1) ω - truncRespMart ν A Y k i ω| ≤ 2 * √i :=
  Eventually.of_forall fun ω ↦ abs_truncRespMart_increment_le k i ω

/-- The truncated quadratic variation is bounded by `V_k n`: from
`predQuadVar_truncRespMart_le` (`⟨M̃⟩_n ≤ V_k ∑_{i<n} 𝟙{A_i=k}`) and `∑_{i<n} 𝟙{A_i=k} ≤ n`. -/
lemma ae_predQuadVar_truncRespMart_le_nat (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) :
    ∀ᵐ ω ∂P, ∀ n, predQuadVar (truncRespMart ν A Y k)
        h.filtrationAction P n ω
      ≤ Var[id; ν k] * (n : ℝ) := by
  have harm : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  filter_upwards [ae_all_iff.mpr fun n ↦ predQuadVar_truncRespMart_le h hint k hν2 n] with ω hqv n
  refine (hqv n).trans (mul_le_mul_of_nonneg_left ?_ harm)
  calc ∑ i ∈ Finset.range n, actionIndicator A k i ω
      ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
        by_cases hω : ω ∈ {ω | A i ω = k}
        · rw [actionIndicator, Set.indicator_of_mem hω]
        · rw [actionIndicator, Set.indicator_of_notMem hω]; norm_num
    _ = (n : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- **Per-block Freedman bound for the truncated martingale** (blueprint `lem:trunc_block`).
With horizon `2^j`, increment bound `c_j = 2√(2^j)`, and the *constrained* exponential parameter
`θ_j = 1/c_j` (the true optimizer `λ/(2v)` is inadmissible), the Freedman inequality on the
martingale stopped at `2^j` (`measure_exists_ge_le_exp_horizon`) gives, for `λ_j = C√(2^j j)` and
`v = V_k 2^j`,
`P(∃ m ≤ 2^j : M̃_m ≥ λ_j ∧ ⟨M̃⟩_m ≤ V_k 2^j) ≤ exp(-(C/2)√j + V_k/4)`.
The exponent is `-(C/2)√j + V_k/4` because `θ_j λ_j = (C/2)√j` (the `√(2^j)` cancels) and
`θ_j² v = V_k/4` stays bounded. -/
lemma measure_exists_truncRespMart_block (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (C : ℝ) (j : ℕ) :
    P {ω | ∃ m ≤ 2 ^ j, C * √((2 : ℝ) ^ j * j) ≤ truncRespMart ν A Y k m ω
          ∧ predQuadVar (truncRespMart ν A Y k)
              h.filtrationAction P m ω
            ≤ Var[id; ν k] * (2 : ℝ) ^ j}
      ≤ ENNReal.ofReal (exp (-(C / 2) * √j + Var[id; ν k] / 4)) := by
  rw [show Var[id; ν k] / 4 = Var[id; ν k] / (2 : ℝ) ^ 2 by norm_num]
  exact measure_exists_ge_le_exp_block (martingale_truncRespMart h hint k)
    (truncRespMart_zero_ae k) (integrable_truncRespMart_sq h hint k) (by norm_num : (0 : ℝ) < 2)
    (ae_abs_truncRespMart_increment_le k) (Var[id; ν k]) C j

/-- **Block Borel–Cantelli for the truncated martingale** (blueprint `lem:trunc_mart_lil`, first
half). The per-block bounds `P(s_j) ≤ exp(-(C/2)√j + V_k/4)` (`measure_exists_truncRespMart_block`)
are summable in `j` (`summable_exp_neg_mul_sqrt`), so the first Borel–Cantelli lemma
(`ae_eventually_notMem`) gives that a.s. only finitely many blocks are bad: for a.e. `ω`, for all
large `j` and every `m ≤ 2^j`, `⟨M̃⟩_m ω ≤ V_k 2^j ⇒ M̃_m ω < C√(2^j j)`. -/
lemma ae_eventually_truncRespMart_lt_block (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) {C : ℝ} (hC : 0 < C) :
    ∀ᵐ ω ∂P, ∀ᶠ (j : ℕ) in atTop, ∀ m ≤ 2 ^ j,
      predQuadVar (truncRespMart ν A Y k)
          h.filtrationAction P m ω
        ≤ Var[id; ν k] * (2 : ℝ) ^ j →
      truncRespMart ν A Y k m ω < C * √((2 : ℝ) ^ j * j) :=
  ae_eventually_lt_block_of_growing (martingale_truncRespMart h hint k)
    (truncRespMart_zero_ae k) (integrable_truncRespMart_sq h hint k) (by norm_num : (0 : ℝ) < 2)
    (ae_abs_truncRespMart_increment_le k) (Var[id; ν k]) hC

/-- **`O(√(n log n))` LIL for the truncated martingale** (formalized content of blueprint
`lem:trunc_mart_lil`). From the block exceedance (`ae_eventually_truncRespMart_lt_block`) and the
quadratic-variation bound `⟨M̃⟩_n ≤ V_k N_{n,k} ≤ V_k n` (`predQuadVar_truncRespMart_le`), almost
surely `M̃_n ≤ C' √(n log n)` eventually. For each large `n`, take the least `j` with `n ≤ 2^j` (so
`2^j ≤ 2n` and `j ≤ log₂ n + 1`); then `⟨M̃⟩_n ≤ V_k n ≤ V_k 2^j`, so the block bound applies at
`m = n ≤ 2^j`, giving `M̃_n < √(2^j j) ≤ C' √(n log n)`.

The horizon restriction `m ≤ 2^j` yields the `n`-scale rather than the `⟨M̃⟩_n`-scale of the
blueprint's displayed statement: time-blocking controls `M̃_n` on the scale of the time `n`, which
is what the growing increment bound `2√i` permits. When arm `k` is sampled a positive fraction of
the time (`N_{n,k} ≍ n`, the regime of interest) this coincides with the `√(⟨M̃⟩_n log⟨M̃⟩_n)`
form. -/
lemma ae_eventually_truncRespMart_le_sqrt_nat_mul_log
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hint : ∀ n, Integrable (Y n) P) (k : 𝓐)
    (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) :
    ∀ᵐ ω ∂P, ∃ C', ∀ᶠ n in atTop,
      truncRespMart ν A Y k n ω ≤ C' * √(n * log n) := by
  have harm : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  exact ae_eventually_le_sqrt_nat_mul_log_of_growing (martingale_truncRespMart h hint k)
    (truncRespMart_zero_ae k) (integrable_truncRespMart_sq h hint k) (by norm_num : (0 : ℝ) < 2)
    (ae_abs_truncRespMart_increment_le k) harm (ae_predQuadVar_truncRespMart_le_nat h hint k hν2)

/-- **Two-sided `O(√(n log n))` LIL for the truncated martingale.** The absolute-value companion of
`ae_eventually_truncRespMart_le_sqrt_nat_mul_log`, obtained by instantiating the general two-sided
bound `ae_eventually_abs_le_sqrt_nat_mul_log_of_growing` at the truncated martingale. Almost surely
`|M̃_n| ≤ C' √(n log n)` eventually. -/
lemma ae_eventually_abs_truncRespMart_le_sqrt_nat_mul_log
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hint : ∀ n, Integrable (Y n) P) (k : 𝓐)
    (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) :
    ∀ᵐ ω ∂P, ∃ C', ∀ᶠ n in atTop,
      |truncRespMart ν A Y k n ω| ≤ C' * √(n * log n) := by
  have harm : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  exact ae_eventually_abs_le_sqrt_nat_mul_log_of_growing (martingale_truncRespMart h hint k)
    (truncRespMart_zero_ae k) (integrable_truncRespMart_sq h hint k) (by norm_num : (0 : ℝ) < 2)
    (ae_abs_truncRespMart_increment_le k) harm (ae_predQuadVar_truncRespMart_le_nat h hint k hν2)

/-! ### Assembling: the finite-variance LIL for the response martingale -/

/-- **A sequence whose increments eventually vanish is eventually bounded.** If `a (n+1) = a n`
for all large `n`, then `a` is eventually constant, so `|a n| ≤ |a N|` eventually. -/
lemma eventually_bounded_of_eventually_const {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, a (n + 1) = a n) : ∃ C, ∀ᶠ n in atTop, |a n| ≤ C := by
  rw [eventually_atTop] at ha
  obtain ⟨N, hN⟩ := ha
  have hconst : ∀ n, N ≤ n → a n = a N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [hN m hm, ih]
  exact ⟨|a N|, eventually_atTop.mpr ⟨N, fun n hn ↦ le_of_eq (by rw [hconst n hn])⟩⟩

/-- **Off the truncation window the tail is nonzero.** If the truncated value
`truncation(· - θ, A)(x)` differs from `x - θ`, then `x - θ` lies outside `(-A, A]`, so
`A ≤ |x - θ|`. This pins the support of the tail-remainder increment to the summable tail event. -/
lemma le_abs_of_truncation_sub_ne {θ A x : ℝ}
    (hx : truncation (fun y ↦ y - θ) A x ≠ x - θ) : A ≤ |x - θ| := by
  by_contra hlt
  rw [not_le] at hlt
  apply hx
  have hmem : x - θ ∈ Set.Ioc (-A) A :=
    Set.mem_Ioc.mpr ⟨by linarith [neg_abs_le (x - θ)], by linarith [le_abs_self (x - θ)]⟩
  simp only [truncation, Function.comp_apply, Set.indicator_of_mem hmem, id_eq]

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- Successor increment of the truncated response martingale:
`M̃_{n+1} - M̃_n = 𝟙{A n = k}(truncation(Y n - θ_k, √n) - m_n)`. -/
lemma truncRespMart_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    truncRespMart ν A Y k (n + 1) ω - truncRespMart ν A Y k n ω
      = actionIndicator A k n ω
        * (truncation (fun y ↦ y - ν.means k) (√n) (Y n ω) - truncMean ν k n) := by
  have hsucc := congrFun (genRespMart_succ (ν := ν) (A := A) (Y := Y) k
    (fun j ↦ truncation (fun y ↦ y - ν.means k) (√j)) n) ω
  simp only [truncRespMart, Pi.add_apply] at hsucc ⊢
  rw [hsucc, add_sub_cancel_left]; rfl

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- Successor increment of the truncated drift: `Dr_{n+1} - Dr_n = m_n 𝟙{A n = k}`. -/
@[specifies truncDrift "the drift accrues on the arm's own clock: the step-`n` bias `m_n` is \
charged only when arm `k` is actually pulled, matching the centring `truncRespMart` removed"]
lemma truncDrift_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    truncDrift ν A k (n + 1) ω - truncDrift ν A k n ω
      = truncMean ν k n * actionIndicator A k n ω := by
  have h1 : truncDrift ν A k (n + 1) ω
      = ∑ i ∈ Finset.range (n + 1),
        truncMean ν k i * actionIndicator A k i ω := by
    rw [truncDrift, Finset.sum_apply]
  have h2 : truncDrift ν A k n ω
      = ∑ i ∈ Finset.range n,
        truncMean ν k i * actionIndicator A k i ω := by
    rw [truncDrift, Finset.sum_apply]
  rw [h1, h2, Finset.sum_range_succ]; ring

/-- The **tail remainder** `R_n = Q_n - M̃_n - Dr_n` of the truncated decomposition
(blueprint `def:lil_trunc`, the `R` term). -/
noncomputable def tailRespPart (ν : Kernel 𝓐 ℝ) [IsMarkovKernel ν] (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ)
    (k : 𝓐) (n : ℕ) : Ω → ℝ :=
  respMart ν A Y k n - truncRespMart ν A Y k n - truncDrift ν A k n

omit [MeasurableSingletonClass 𝓐] in
/-- **The tail-remainder increment is the discarded tail** `𝟙{A n = k}((Y n - θ_k) -
truncation(Y n - θ_k, √n))`: the truncated mean `m_n` cancels between `M̃` and `Dr`. -/
@[specifies tailRespPart "certifies the three-way split `Q = M̃ + Dr + R` is exact: the remainder \
carries precisely what truncation discarded, with the centring `m_n` cancelling between the \
martingale and the drift and leaving no extra term"]
lemma tailRespPart_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    tailRespPart ν A Y k (n + 1) ω - tailRespPart ν A Y k n ω
      = actionIndicator A k n ω
        * ((Y n ω - ν.means k) - truncation (fun y ↦ y - ν.means k) (√n) (Y n ω)) := by
  simp only [tailRespPart, Pi.sub_apply]
  rw [show respMart ν A Y k (n + 1) ω = respMart ν A Y k n ω
        + actionIndicator A k n ω * (Y n ω - ν.means k) from
      by rw [← respMart_succ_sub]; ring,
    show truncRespMart ν A Y k (n + 1) ω = truncRespMart ν A Y k n ω
        + actionIndicator A k n ω
          * (truncation (fun y ↦ y - ν.means k) (√n) (Y n ω) - truncMean ν k n) from
      by rw [← truncRespMart_succ_sub]; ring,
    show truncDrift ν A k (n + 1) ω = truncDrift ν A k n ω
        + truncMean ν k n * actionIndicator A k n ω from
      by rw [← truncDrift_succ_sub]; ring]
  ring

/-- **Conditional bookkeeping for the sampled tail.** The probability that arm `k` is chosen at
step `n` *and* its response lands in the tail `√n ≤ |Y n - θ_k|` is at most the reward law's tail
`ν_k(√n ≤ |· - θ_k|)`. Conditioning on `𝒢 n` replaces the sampled response's tail indicator by its
`ν(A n)`-integral (`condExp_feedback_comp_stationaryEnv`), which on `{A n = k}` is `ν_k`, and
`P{A n = k} ≤ 1`. -/
lemma measure_action_and_tail_le (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (n : ℕ) :
    P {ω | A n ω = k ∧ √n ≤ |Y n ω - ν.means k|}
      ≤ (ν k) {x | √n ≤ |x - ν.means k|} := by
  let θ := ν.means k
  let S : Set ℝ := {x | √n ≤ |x - θ|}
  have hSmeas : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  set g : ℝ → ℝ := S.indicator (fun _ ↦ 1) with hg_def
  have hgSM : StronglyMeasurable g := stronglyMeasurable_const.indicator hSmeas
  have hgbound : ∀ x, |g x| ≤ 1 := fun x ↦ by
    rw [hg_def]; by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  have hgint : Integrable (fun ω ↦ g (Y n ω)) P :=
    Integrable.mono' (integrable_const (1 : ℝ))
      (hgSM.comp_measurable (h.measurable_feedback n)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hgbound (Y n ω))
  have hAk : MeasurableSet {ω | A n ω = k} := h.measurable_action n (measurableSet_singleton k)
  set c : Ω → ℝ := actionIndicator A k n with hc_def
  have hbadmeas : MeasurableSet {ω | A n ω = k ∧ √n ≤ |Y n ω - θ|} :=
    hAk.inter (hSmeas.preimage (h.measurable_feedback n))
  -- `𝟙{bad} = c · (g ∘ Y n)` pointwise.
  have hcg_eq : (fun ω ↦ c ω * g (Y n ω))
      = Set.indicator {ω | A n ω = k ∧ √n ≤ |Y n ω - θ|} (fun _ ↦ (1 : ℝ)) := by
    funext ω
    rw [hc_def, actionIndicator, hg_def]
    by_cases hak : A n ω = k
    · by_cases hy : √n ≤ |Y n ω - θ|
      · rw [Set.indicator_of_mem (show ω ∈ {ω | A n ω = k} from hak),
          Set.indicator_of_mem (show Y n ω ∈ S from hy),
          Set.indicator_of_mem (show ω ∈ {ω | A n ω = k ∧ √n ≤ |Y n ω - θ|} from ⟨hak, hy⟩)]
        ring
      · rw [Set.indicator_of_notMem (show Y n ω ∉ S from hy),
          Set.indicator_of_notMem
            (show ω ∉ {ω | A n ω = k ∧ √n ≤ |Y n ω - θ|} from fun hb ↦ hy hb.2), mul_zero]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | A n ω = k} from hak),
        Set.indicator_of_notMem
          (show ω ∉ {ω | A n ω = k ∧ √n ≤ |Y n ω - θ|} from fun hb ↦ hak hb.1), zero_mul]
  have hcint : Integrable (fun ω ↦ c ω * g (Y n ω)) P := by
    rw [hcg_eq]; exact (integrable_const (1 : ℝ)).indicator hbadmeas
  let G := h.filtrationAction n
  have hGle : G ≤ mΩ :=
    h.filtrationAction.le n
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator
      ((h.adapted_action_filtrationAction n) (measurableSet_singleton k))
  -- Tower + pull-out + feedback: `P[𝟙{bad}] = ν_k(S) · P{A n = k}`.
  have hcondexp : P[fun ω ↦ c ω * g (Y n ω) | G] =ᵐ[P] fun ω ↦ (ν k)[g] * c ω := by
    have hpull : P[fun ω ↦ c ω * g (Y n ω) | G] =ᵐ[P] c * P[fun ω ↦ g (Y n ω) | G] :=
      condExp_mul_of_stronglyMeasurable_left hcG hcint hgint
    have hfb : P[fun ω ↦ g (Y n ω) | G] =ᵐ[P] fun ω ↦ (ν (A n ω))[g] :=
      h.condExp_feedback_comp_stationaryEnv n hgSM hgint
    filter_upwards [hpull, hfb] with ω hp hf
    rw [hp, Pi.mul_apply, hf]
    by_cases hak : A n ω = k
    · rw [hak]; ring
    · rw [hc_def, actionIndicator, Set.indicator_of_notMem (show ω ∉ {ω | A n ω = k} from hak)]
      ring
  have hgval : (ν k)[g] = ((ν k) S).toReal := by
    have he : (ν k)[g] = ∫ x, g x ∂(ν k) := rfl
    rw [he, hg_def, integral_indicator_const (1 : ℝ) hSmeas, smul_eq_mul, mul_one]; rfl
  have hreal : (P {ω | A n ω = k ∧ √n ≤ |Y n ω - θ|}).toReal ≤ ((ν k) S).toReal := by
    have hbadint : ∫ ω, c ω * g (Y n ω) ∂P
        = (P {ω | A n ω = k ∧ √n ≤ |Y n ω - θ|}).toReal := by
      rw [hcg_eq, integral_indicator_const (1 : ℝ) hbadmeas, smul_eq_mul, mul_one]; rfl
    have hprob : (P {ω | A n ω = k}).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    rw [← hbadint, ← integral_condExp hGle, integral_congr_ae hcondexp, integral_const_mul, hc_def]
    simp only [actionIndicator]
    rw [integral_indicator_const (1 : ℝ) hAk, smul_eq_mul, mul_one, hgval]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg hprob
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- **Summability of the sampled tail events.** With `ν_k` of finite second moment,
`∑' n, P(A n = k ∧ √n ≤ |Y n - θ_k|) < ∞`, by the conditional bookkeeping
(`measure_action_and_tail_le`) and the law-level tail summability
(`tsum_measure_abs_sub_ge_sqrt_ne_top`). -/
lemma tsum_measure_action_and_tail_ne_top (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) :
    (∑' n : ℕ, P {ω | A n ω = k ∧ √n ≤ |Y n ω - ν.means k|}) ≠ ∞ := by
  refine ne_top_of_le_ne_top (tsum_measure_abs_sub_ge_sqrt_ne_top (ν.means k) hν2) ?_
  exact ENNReal.tsum_le_tsum fun n ↦ measure_action_and_tail_le h k n

/-- **The tail remainder is eventually constant** (blueprint `lem:trunc_tail_const`, sampled form).
By the first Borel–Cantelli lemma applied to the summable sampled tail events
(`tsum_measure_action_and_tail_ne_top`), almost surely for all large `n` the tail-remainder
increment `𝟙{A n = k}((Y n - θ_k) - truncation(Y n - θ_k, √n))` vanishes, so `R_n` is eventually
constant, hence `R_n = O(1)` a.s. -/
lemma ae_eventually_tailRespPart_const (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, tailRespPart ν A Y k (n + 1) ω = tailRespPart ν A Y k n ω := by
  filter_upwards [ae_eventually_notMem (tsum_measure_action_and_tail_ne_top h k hν2)] with ω hω
  filter_upwards [hω] with n hn
  rw [← sub_eq_zero, tailRespPart_succ_sub]
  by_cases hak : A n ω = k
  · have htail : (Y n ω - ν.means k)
        - truncation (fun y ↦ y - ν.means k) (√n) (Y n ω) = 0 := by
      by_contra hne
      exact hn ⟨hak, le_abs_of_truncation_sub_ne (sub_ne_zero.mp hne).symm⟩
    rw [htail, mul_zero]
  · rw [actionIndicator, Set.indicator_of_notMem (show ω ∉ {ω | A n ω = k} from hak), zero_mul]

/-- **The response martingale is two-sided `O(√(n log n))`** (blueprint `lem:lil_truncation`).
Assembling the truncated decomposition `Q_n = M̃_n + R_n + Dr_n` (Definition `def:lil_trunc`): the
truncated martingale is two-sided `O(√(n log n))` (an instance of the general growing-increment LIL,
`ae_eventually_abs_truncRespMart_le_sqrt_nat_mul_log`), the tail remainder is `O(1)`
(`ae_eventually_tailRespPart_const`), and the drift is `O(√n)` (`abs_truncDrift_le`); the last two
are `o(√(n log n))`, so almost surely `|Q_{n,k}| ≤ C √(n log n)` eventually. -/
lemma ae_eventually_abs_respMart_le_sqrt_nat_mul_log
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hint : ∀ n, Integrable (Y n) P) (k : 𝓐)
    (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) :
    ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      |respMart ν A Y k n ω| ≤ C * √(n * log n) := by
  have harm : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  filter_upwards [ae_eventually_abs_truncRespMart_le_sqrt_nat_mul_log h hint k hν2,
    ae_eventually_tailRespPart_const h k hν2] with ω hMtilde hRconst
  obtain ⟨C₁, hC₁⟩ := hMtilde
  obtain ⟨C₂, hC₂⟩ :=
    eventually_bounded_of_eventually_const (a := fun n ↦ tailRespPart ν A Y k n ω) hRconst
  refine ⟨C₁ + C₂ + 2 * Var[id; ν k], ?_⟩
  filter_upwards [hC₁, hC₂, eventually_ge_atTop 3] with n hn1 hn2 hn3
  have hnR3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn1 : (1 : ℝ) ≤ log n :=
    (le_log_iff_exp_le hnpos).mpr (le_trans exp_one_lt_d9.le (by linarith))
  have hge1 : (1 : ℝ) ≤ (n : ℝ) * log n := by
    have := mul_le_mul (show (1 : ℝ) ≤ (n : ℝ) by linarith) hlogn1 zero_le_one (by linarith)
    linarith
  have hL1 : (1 : ℝ) ≤ √((n : ℝ) * log n) := Real.one_le_sqrt.mpr hge1
  have hsn : √(n : ℝ) ≤ √((n : ℝ) * log n) :=
    sqrt_le_sqrt (le_mul_of_one_le_right (by positivity) hlogn1)
  have hC₂nn : (0 : ℝ) ≤ C₂ := (abs_nonneg _).trans hn2
  have hdecomp : respMart ν A Y k n ω = tailRespPart ν A Y k n ω
      + truncRespMart ν A Y k n ω + truncDrift ν A k n ω := by
    simp only [tailRespPart, Pi.sub_apply]; ring
  have ht' : |tailRespPart ν A Y k n ω| ≤ C₂ * √((n : ℝ) * log n) :=
    hn2.trans (le_mul_of_one_le_right hC₂nn hL1)
  have hd' : |truncDrift ν A k n ω| ≤ 2 * Var[id; ν k] * √((n : ℝ) * log n) :=
    (abs_truncDrift_le k hν2 n ω).trans (mul_le_mul_of_nonneg_left hsn (by positivity))
  rw [hdecomp]
  calc |tailRespPart ν A Y k n ω + truncRespMart ν A Y k n ω + truncDrift ν A k n ω|
      ≤ |tailRespPart ν A Y k n ω + truncRespMart ν A Y k n ω| + |truncDrift ν A k n ω| :=
        abs_add_le _ _
    _ ≤ |tailRespPart ν A Y k n ω| + |truncRespMart ν A Y k n ω| + |truncDrift ν A k n ω| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ C₂ * √((n : ℝ) * log n) + C₁ * √((n : ℝ) * log n)
        + 2 * Var[id; ν k] * √((n : ℝ) * log n) := add_le_add (add_le_add ht' hn1) hd'
    _ = (C₁ + C₂ + 2 * Var[id; ν k]) * √((n : ℝ) * log n) := by ring

/-- **The response martingale is `O(√(n log n))`** (blueprint `lem:lil_truncation`), the one-sided
consequence of `ae_eventually_abs_respMart_le_sqrt_nat_mul_log` via `Q_n ≤ |Q_n|`. -/
lemma ae_eventually_respMart_le_sqrt_nat_mul_log
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hint : ∀ n, Integrable (Y n) P) (k : 𝓐)
    (hν2 : MemLp (fun x : ℝ ↦ x) 2 (ν k)) :
    ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      respMart ν A Y k n ω ≤ C * √(n * log n) := by
  filter_upwards [ae_eventually_abs_respMart_le_sqrt_nat_mul_log h hint k hν2] with ω hω
  obtain ⟨C, hC⟩ := hω
  exact ⟨C, hC.mono fun n hn ↦ (le_abs_self _).trans hn⟩

end AlphaRAR
