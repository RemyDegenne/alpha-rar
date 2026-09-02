/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.LeanMachineLearning.PullCount
public import LeanMachineLearning.SequentialLearning.ActionIndicator
public import LeanMachineLearning.SequentialLearning.FeedbackMartingale
public import AlphaRAR.LeanMachineLearning.IsAlgEnvSeq
public import AlphaRAR.Mathlib.HasCondDistrib
public import AlphaRAR.Mathlib.Variance
public import AlphaRAR.Mathlib.MartingaleRate
public import LeanMachineLearning.SequentialLearning.FiniteActions
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Topology.Separation.CompletelyRegular
public meta import Characterization

/-!
# The response martingale, via the algorithm–environment framework

We model the sequential multi-treatment experiment with the `LeanMachineLearning`
`IsAlgEnvSeq` framework: an *action* `A n` is the arm assigned to patient `n`, and
the *feedback* `Y n` is the observed response. In a **stationary environment** with
per-arm reward kernel `ν : Kernel 𝓐 ℝ`, the response of a patient assigned to arm
`a` is drawn from `ν a`, independently of the past given the arm.

The mean of arm `a` is `ν.means a = ∫ x, x ∂(ν a)`. The centered response martingale
of arm `k` is `Q k n = ∑_{m < n} 𝟙{A m = k} (Y m - ν.means k)`: it is `LeanMachineLearning`'s
`noiseSum` — the martingale part of the summed rewards of an action, for an arbitrary environment —
instantiated at the stationary environment `stationaryEnv ν`, whose step means are the arm means
(`respMart_apply`). Its martingale property, adaptedness, integrability and `L²` membership are the
upstream `IsAlgEnvSeq.martingale_noiseSum` and friends; what is specific to the stationary model is
the quadratic variation `⟨Q k⟩ = V_k N_k`.

The two martingales of the model rest on different filtration conventions:
`M` (the assignment martingale) is a martingale because the *assignment* `A (n+1)`
is fresh randomness given the history `ℱ n`, while `Q` is a martingale because the
*response* `Y (n+1)` is fresh given the history **and** the current assignment
(`filtrationAction (n+1) = ℱ n ⊔ σ(A (n+1))`). The two use genuinely different
information at each step, made rigorous here by the tower property through
`filtrationAction`.

## Main results

* `AlphaRAR.respMart`: the centered response martingale `Q k`.
* `AlphaRAR.martingale_respMart`: `Q k` is a martingale for `filtrationAction`.
* `AlphaRAR.predQuadVar_respMart_eq`: `⟨Q k⟩_n = V_k N_{n,k}`, with `V_k = Var[id; ν k]`.
* `AlphaRAR.integral_respMart_sq_eq`: `𝔼[Q_{n,k}²] = V_k 𝔼[N_{n,k}]`.
* `AlphaRAR.martingale_respMart_mul`: `Q k · Q j` is a martingale for `k ≠ j`, so the cross
  variation vanishes.
* `AlphaRAR.isBigOpOne_respMart_div_sqrt`: `Q_{n,k} = O_p(√n)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning

open scoped ENNReal

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- The centered **response martingale** of arm `k`:
`Q k n = ∑_{m < n} 𝟙{A m = k} (Y m - ν.means k)`, summing over patients `0, …, n-1`. Its
increments are the mean-centered responses of the patients assigned to arm `k`.

It is the upstream `Learning.noiseSum` — the martingale part of `sumRewards A Y k` for the
action-augmented filtration, in an arbitrary environment — at the stationary environment
`stationaryEnv ν`, whose mean at every step is the arm mean `ν.means (A m)`; on `{A m = k}` that is
`ν.means k`, which gives the displayed formula (`respMart_apply`). -/
noncomputable def respMart (ν : Kernel 𝓐 ℝ) [IsMarkovKernel ν] (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ)
    (k : 𝓐) : ℕ → Ω → ℝ :=
  noiseSum (stationaryEnv ν) A Y k

omit [MeasurableSingletonClass 𝓐] in
/-- In the stationary environment the `noiseSum` increment of arm `k` is the indicator of
`{A m = k}` times the response centered at the arm mean `ν.means k`. -/
lemma respMart_increment_eq (k : 𝓐) (m : ℕ) (ω : Ω) :
    {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (stationaryEnv ν).means A Y (A m ω) m ω) ω
      = actionIndicator A k m ω * (Y m ω - ν.means k) := by
  by_cases hω : A m ω = k
  · simp [hω, actionIndicator, Kernel.means_apply]
  · simp [hω, actionIndicator]

omit [MeasurableSingletonClass 𝓐] in
/-- Function form of `respMart_increment_eq`. -/
lemma respMart_increment_eq' (k : 𝓐) (m : ℕ) :
    {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (stationaryEnv ν).means A Y (A m ω) m ω)
      = fun ω ↦ actionIndicator A k m ω * (Y m ω - ν.means k) :=
  funext (respMart_increment_eq k m)

omit [MeasurableSingletonClass 𝓐] in
/-- The response martingale as an explicit sum:
`Q k n ω = ∑_{m < n} 𝟙{A m = k} (Y m - ν.means k)`. -/
lemma respMart_apply (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMart ν A Y k n ω = ∑ m ∈ Finset.range n, actionIndicator A k m ω * (Y m ω - ν.means k) := by
  simp only [respMart, noiseSum, respMart_increment_eq]

omit [MeasurableSingletonClass 𝓐] in
@[simp]
lemma respMart_zero (k : 𝓐) : respMart ν A Y k 0 = fun _ ↦ 0 := noiseSum_zero k

omit [IsMarkovKernel ν] in
/-- Each response-martingale increment is integrable (the indicator is bounded and the
centered response is integrable). -/
@[fun_prop]
lemma integrable_respMart_increment {m : ℕ} (hAmeas : Measurable (A m))
    (hint : Integrable (Y m) P) (k : 𝓐) :
    Integrable (fun ω ↦ actionIndicator A k m ω * (Y m ω - ν.means k)) P := by
  have heq : (fun ω ↦ actionIndicator A k m ω * (Y m ω - ν.means k))
      = {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - ν.means k) := by
    funext ω
    simp only [actionIndicator, Set.indicator]
    by_cases hω : ω ∈ {ω | A m ω = k} <;> simp [hω]
  rw [heq]
  exact (hint.sub (integrable_const _)).indicator (hAmeas (measurableSet_singleton k))

/-- **The response martingale increment has zero conditional expectation given `𝒢`.**
Conditioning on the action-augmented filtration `𝒢 i = filtrationAction i` (the history up to
`i-1` *and* the current assignment `A i`), the increment `𝟙{A i = k}(Y i - ν.means k)` vanishes
in conditional mean: the indicator is `𝒢 i`-measurable and pulls out, and the response's
conditional mean is the arm mean `ν.means (A i)`, which cancels `ν.means k` on `{A i = k}`. This is
the fact that makes `Q` a martingale for `filtrationAction` (upstream
`IsAlgEnvSeq.condExp_noiseSum_increment`, in the stationary environment). -/
lemma condExp_respMart_increment (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ)
    (hint : Integrable (Y i) P) :
    P[fun ω ↦ actionIndicator A k i ω * (Y i ω - ν.means k) | h.filtrationAction i] =ᵐ[P] 0 := by
  have h' := h.condExp_noiseSum_increment k i hint
  rwa [respMart_increment_eq'] at h'

/-- **Conditional second moment of the response-martingale increment**, per step.
Conditioning on the action-augmented filtration `𝒢 i = filtrationAction i` (the history and the
current assignment `A i`), the squared increment `(𝟙{A i = k}(Y i - θ_k))²` has conditional
expectation `𝟙{A i = k} · V_k`, where `V_k = Var[id; ν k]` is the variance of arm `k`. The
indicator squares to itself, and on the event `{A i = k}` the response's conditional second
central moment is exactly the arm variance. Retaining the (`𝒢`-measurable) indicator is what
turns the summed second moments into `V_k N_{n,k}`. -/
lemma condExp_respMart_increment_sq [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (i : ℕ) (hνk : ∀ a, MemLp id 2 (ν a)) :
    P[fun ω ↦ (actionIndicator A k i ω * (Y i ω - ν.means k)) ^ 2
        | h.filtrationAction i]
      =ᵐ[P] fun ω ↦ actionIndicator A k i ω * Var[id; ν k] := by
  have hint2 : Integrable (fun ω ↦ (Y i ω - ν.means k) ^ 2) P :=
    ((h.memLp_feedback hνk i).sub (memLp_const _)).integrable_sq
  let hA := h.measurable_action
  let G := h.filtrationAction i
  set c : Ω → ℝ := actionIndicator A k i with hc_def
  set g : Ω → ℝ := fun ω ↦ (Y i ω - ν.means k) ^ 2 with hg_def
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator
      ((h.adapted_action_filtrationAction i) (measurableSet_singleton k))
  -- The squared increment equals `c · g` (the indicator squares to itself).
  have hsq : (fun ω ↦ (c ω * (Y i ω - ν.means k)) ^ 2) = fun ω ↦ c ω * g ω := by
    funext ω
    simp only [hg_def]
    by_cases hω : ω ∈ {ω | A i ω = k}
    · simp only [hc_def, actionIndicator, Set.indicator_of_mem hω]; ring
    · simp only [hc_def, actionIndicator, Set.indicator_of_notMem hω]; ring
  rw [hsq]
  -- `c · g` is integrable (bounded indicator times an integrable square).
  have hcgint : Integrable (fun ω ↦ c ω * g ω) P := by
    have hform : (fun ω ↦ c ω * g ω) = {ω | A i ω = k}.indicator g := by
      funext ω
      simp only [hc_def, actionIndicator, Set.indicator]
      by_cases hω : ω ∈ {ω | A i ω = k} <;> simp [hω]
    rw [hform]
    exact hint2.indicator (hA i (measurableSet_singleton k))
  -- Conditional expectation of `g = (Y - θ_k)²` given `G` is the arm's second central moment.
  have hcondg : P[g | G] =ᵐ[P] fun ω ↦ ∫ x, (x - ν.means k) ^ 2 ∂(ν (A i ω)) := by
    have hg2 : StronglyMeasurable (fun x : ℝ ↦ (x - ν.means k) ^ 2) :=
      ((continuous_id.sub continuous_const).pow 2).stronglyMeasurable
    exact h.condExp_feedback_comp_stationaryEnv i hg2 hint2
  -- Pull out the `G`-measurable indicator `c`, then evaluate on the arm event.
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcgint hint2
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * g | G] ω = _
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A i ω) k with hak | hak
  · rw [hak, variance_id_eq_integral, Kernel.means_apply]
  · have hc0 : c ω = 0 := by
      rw [hc_def, actionIndicator, Set.indicator_of_notMem (by simpa using hak)]
    rw [hc0, zero_mul, zero_mul]

omit [MeasurableSingletonClass 𝓐] in
/-- Successor form: `Q k (n+1) = Q k n + 𝟙{A n = k}(Y n - ν.means k)` (`noiseSum_succ`). -/
lemma respMart_succ (k : 𝓐) (n : ℕ) :
    respMart ν A Y k (n + 1) = respMart ν A Y k n +
      fun ω ↦ actionIndicator A k n ω * (Y n ω - ν.means k) := by
  unfold respMart
  rw [noiseSum_succ, respMart_increment_eq']

omit [MeasurableSingletonClass 𝓐] in
/-- The response-martingale increment: `Q k (n+1) - Q k n = 𝟙{A n=k}(Y n - ν.means k)`. -/
lemma respMart_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω
      = actionIndicator A k n ω * (Y n ω - ν.means k) := by
  rw [respMart_succ]; simp only [Pi.add_apply]; ring

omit [MeasurableSingletonClass 𝓐] in
/-- **The increments of `Q_k` and `Q_j` have identically-zero product for `k ≠ j`.**
A patient is assigned to exactly one arm, so the indicators `𝟙{A = k}` and `𝟙{A = j}` are
disjoint (`𝟙{A = k}·𝟙{A = j} = 0`); hence `ΔQ_{·,k} · ΔQ_{·,j} = 0`. This is the (unconditional)
orthogonality behind the vanishing cross variation. -/
lemma respMart_increment_mul_eq_zero {k j : 𝓐} (hkj : k ≠ j) (n : ℕ) :
    (respMart ν A Y k (n + 1) - respMart ν A Y k n)
      * (respMart ν A Y j (n + 1) - respMart ν A Y j n) = 0 := by
  funext ω
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, respMart_succ_sub, actionIndicator]
  rcases eq_or_ne (A n ω) k with hak | hak
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω | A n ω = j} by simp only [Set.mem_ofPred_eq]; rw [hak]; exact hkj)]
    ring
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω | A n ω = k} by simpa using hak)]
    ring

/-- Each `Q k n` is integrable (`IsAlgEnvSeq.integrable_noiseSum`). -/
@[fun_prop]
lemma integrable_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (n : ℕ) :
    Integrable (respMart ν A Y k n) P :=
  h.integrable_noiseSum hint k n

/-- The response martingale `Q k` is adapted to the action-augmented filtration
`𝒢 = filtrationAction`: `Q k n` depends only on the assignments and responses of patients
`0, …, n-1`, all of which are `𝒢 n`-measurable (`IsAlgEnvSeq.stronglyAdapted_noiseSum`). -/
lemma stronglyAdapted_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) :
    StronglyAdapted h.filtrationAction (respMart ν A Y k) :=
  h.stronglyAdapted_noiseSum k

/-- **The response martingale is a martingale.**
For arm `k`, `Q k` is a martingale for the action-augmented filtration
`𝒢 n = filtrationAction n = ℱ (n-1) ⊔ σ(A n)` — the history up to the previous patient together
with the current assignment. The increment `𝟙{A i = k}(Y i - ν.means k)` has zero conditional
expectation given `𝒢 i` because the response `Y i` is fresh given the current arm
(`condExp_respMart_increment`); this is the filtration for which the paper's response martingale
is a genuine martingale difference (the assignment is known, the response is not). This is the
upstream `IsAlgEnvSeq.martingale_noiseSum` in the stationary environment. -/
@[specifies respMart "names the filtration that makes `Q` a martingale: the *action-augmented* \
`filtrationAction n = ℱ_{n-1} ⊔ σ(A n)`, where the assignment is already known and only the \
response is fresh. Centring at the arm mean `ν.means k` is exactly what this filtration requires"]
lemma martingale_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) :
    Martingale (respMart ν A Y k) h.filtrationAction P :=
  h.martingale_noiseSum hint k

/-!
### The quadratic variation of the response martingale

Since `Q k` is a martingale for `𝒢 = filtrationAction`, the paper's quadratic variation
`V_k N_{n,k}` is the *ordinary* predictable quadratic variation `predQuadVar Q 𝒢`: the compensator
increment `V_k X_{n,k}` keeps the indicator because the current arm `A n` is `𝒢 n`-measurable
(`condExp_respMart_increment_sq`).
-/

omit [IsMarkovKernel ν] in
/-- Each response-martingale increment is in `L²` when the response is (Condition **A**): a
bounded indicator times the `L²` centered response. -/
lemma memLp_respMart_increment {m : ℕ} (k : 𝓐) (hAmeas : Measurable (A m))
    (hY2 : MemLp (Y m) 2 P) :
    MemLp (fun ω ↦ actionIndicator A k m ω * (Y m ω - ν.means k)) 2 P := by
  have heq : (fun ω ↦ actionIndicator A k m ω * (Y m ω - ν.means k))
      = {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - ν.means k) := by
    funext ω
    by_cases hω : ω ∈ {ω | A m ω = k}
    · simp [actionIndicator, Set.indicator_of_mem hω]
    · simp [actionIndicator, Set.indicator_of_notMem hω]
  rw [heq]
  exact (hY2.sub (memLp_const _)).indicator (hAmeas (measurableSet_singleton k))

/-- `Q k n` is in `L²` when the responses are (Condition **A**): `IsAlgEnvSeq.memLp_noiseSum`. -/
lemma memLp_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (k : 𝓐) (n : ℕ) :
    MemLp (respMart ν A Y k n) 2 P :=
  h.memLp_noiseSum one_le_two ENNReal.ofNat_ne_top hY2 k n

/-- **The quadratic variation of `Q` is `V_k N`.**
For the action-augmented filtration `𝒢 = filtrationAction` — for which `Q k` is a martingale
(`martingale_respMart`) — the ordinary predictable quadratic variation of `Q k` is `V_k` times the
assignment count of arm `k`: `⟨Q k⟩_n = V_k N_{n,k}` a.e. The compensator increments are the
`𝒢`-conditional second moments `V_k X_{m,k}` (`condExp_respMart_increment_sq`), which sum to
`V_k N` because the indicator is retained. The only hypothesis is Condition **A**: every arm's
reward distribution is square-integrable (`hνk : ∀ a, MemLp id 2 (ν a)`); the integrability of
`Q`, its increments, and its increment products (feeding the discrete Doob decomposition) are all
derived from it. -/
@[specifies respMart "the sharpest check on the construction: `Q k` accumulates variance at rate \
`V_k` per *pull of arm `k`*, so `⟨Q k⟩_n = V_k N_{n,k}` exactly — not `V_k n`. This is what \
makes the clock of `Q k` the arm's own count and drives every rate downstream"]
lemma predQuadVar_respMart_eq [DecidableEq 𝓐] [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (hνk : ∀ a, MemLp id 2 (ν a)) (n : ℕ) :
    predQuadVar (respMart ν A Y k)
        h.filtrationAction P n
      =ᵐ[P] fun ω ↦ Var[id; ν k] * (pullCount A k n ω : ℝ) := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hQ2 : ∀ n, MemLp (respMart ν A Y k n) 2 P := memLp_respMart h hY2 k
  have hprod : ∀ n, Integrable (respMart ν A Y k n
      * (respMart ν A Y k (n + 1) - respMart ν A Y k n)) P := fun n ↦
    integrable_mul_increment (hQ2 n) (hQ2 (n + 1))
  have hd2 : ∀ m, MemLp (fun ω ↦ respMart ν A Y k (m + 1) ω - respMart ν A Y k m ω) 2 P :=
    fun m ↦ memLp_increment (hQ2 m) (hQ2 (m + 1))
  have hM := martingale_respMart h hint k
  -- The martingale increment `ΔQ` squares to the squared centered response.
  have hdiff : ∀ m, (fun ω ↦ (respMart ν A Y k (m + 1) ω - respMart ν A Y k m ω) ^ 2)
      = fun ω ↦ (actionIndicator A k m ω
        * (Y m ω - ν.means k)) ^ 2 := by
    intro m; funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
  -- Each compensator increment is `V_k · X_{m,k}`.
  have hkey : ∀ m, predQuadVar (respMart ν A Y k)
          h.filtrationAction P (m + 1)
        - predQuadVar (respMart ν A Y k)
          h.filtrationAction P m
      =ᵐ[P] fun ω ↦ Var[id; ν k] * actionIndicator A k m ω := by
    intro m
    have h1 := predQuadVar_succ_sub_eq hM m (hd2 m) (hprod m)
    rw [hdiff m] at h1
    refine h1.trans ?_
    refine (condExp_respMart_increment_sq h k m hνk).trans ?_
    filter_upwards with ω; ring
  induction n with
  | zero => filter_upwards with ω; simp
  | succ n ih =>
    filter_upwards [ih, hkey n] with ω hih hk
    simp only [Pi.sub_apply] at hk
    -- `N_{n+1,k} = N_{n,k} + X_{n,k}` (as reals), matching the compensator increment.
    have hrc : (pullCount A k (n + 1) ω : ℝ)
        = (pullCount A k n ω : ℝ) + actionIndicator A k n ω := by
      rw [pullCount_add_one]
      by_cases hak : A n ω = k
      · rw [ite_eq_left hak, actionIndicator,
          Set.indicator_of_mem (show ω ∈ {ω | A n ω = k} from hak)]
        push_cast; ring
      · rw [ite_eq_right hak, actionIndicator,
          Set.indicator_of_notMem (show ω ∉ {ω | A n ω = k} from hak)]
        push_cast; ring
    change predQuadVar (respMart ν A Y k)
        h.filtrationAction
        P (n + 1) ω = Var[id; ν k] * (pullCount A k (n + 1) ω : ℝ)
    rw [hrc, mul_add]
    have hih' : predQuadVar (respMart ν A Y k)
        h.filtrationAction
        P n ω = Var[id; ν k] * (pullCount A k n ω : ℝ) := hih
    linarith [hk, hih']

/-- **`Q² - ⟨Q⟩` is a martingale** for the action-augmented filtration `𝒢 = filtrationAction`
(`martingale_sq_sub_predQuadVar` for `Q`). Together with `predQuadVar_respMart_eq`
(`⟨Q⟩ = V_k N`) this is the compensated response martingale. The only hypothesis is
Condition **A** (`hνk`), from which the square-integrability of `Q` is derived. -/
lemma martingale_sq_sub_predQuadVar_respMart [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (hνk : ∀ a, MemLp id 2 (ν a)) :
    Martingale
      (fun n ↦ (fun ω ↦ respMart ν A Y k n ω ^ 2)
        - predQuadVar (respMart ν A Y k)
            h.filtrationAction P n)
      h.filtrationAction
      P :=
  martingale_sq_sub_predQuadVar (stronglyAdapted_respMart h k)
    (fun n ↦ memLp_respMart h (fun n ↦ h.memLp_feedback hνk n) k n)

/-- **The second moment of `Q` is `V_k` times the expected assignment count**:
`𝔼[Q_{n,k}²] = V_k · 𝔼[N_{n,k}]`. This is the discrete Itô isometry
(`integral_sq_eq_integral_predQuadVar`) specialized to `Q`, using
`⟨Q_k⟩ = V_k N` (`predQuadVar_respMart_eq`): `𝔼[Q²] = 𝔼[⟨Q⟩] = V_k 𝔼[N]`. The only hypothesis is
Condition **A**. -/
lemma integral_respMart_sq_eq [DecidableEq 𝓐] [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (k : 𝓐) (hνk : ∀ a, MemLp id 2 (ν a)) (n : ℕ) :
    ∫ ω, respMart ν A Y k n ω ^ 2 ∂P = Var[id; ν k] * ∫ ω, (pullCount A k n ω : ℝ) ∂P := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  rw [integral_sq_eq_integral_predQuadVar (stronglyAdapted_respMart h k)
      (fun m ↦ memLp_respMart h hY2 k m)
      (by filter_upwards with ω; simp [respMart]) n,
    integral_congr_ae (predQuadVar_respMart_eq h k hνk n), integral_const_mul]

/-- **The cross variation of `Q_k` and `Q_j` vanishes for `k ≠ j`**:
`Q_k · Q_j` is a martingale (for the action-augmented filtration `𝒢 = filtrationAction`), hence its
predictable compensator — the cross variation `⟨Q_k, Q_j⟩` — is `0`. The orthogonality is not
merely conditional: since each patient is assigned to exactly one arm, the increment indicators
`𝟙{A = k}` and `𝟙{A = j}` are disjoint, so the product of increments `ΔQ_{·,k} · ΔQ_{·,j}` is
*identically* `0`. -/
lemma martingale_respMart_mul [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {k j : 𝓐} (hkj : k ≠ j) :
    Martingale (fun n ↦ respMart ν A Y k n * respMart ν A Y j n)
      h.filtrationAction
      P := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hMN : ∀ a b, Integrable (respMart ν A Y k a * respMart ν A Y j b) P := fun a b ↦
    (memLp_respMart h hY2 k a).integrable_mul
      (memLp_respMart h hY2 j b)
  exact martingale_mul (martingale_respMart h hint k) (martingale_respMart h hint j) hMN
    (fun i ↦ by rw [respMart_increment_mul_eq_zero hkj i]; simp)

/-- **The increment second moment of `Q` is bounded by the arm variance `V_k`.**
`∫ (ΔQ_{n+1})² ∂P = V_k · P{A n = k} ≤ V_k`: the `𝒢`-conditional second moment is `𝟙{A n = k}·V_k`
(`condExp_respMart_increment_sq`), so by the tower property the integral is `V_k` times the
probability of assigning arm `k`, which is `≤ 1`. This is the increment bound feeding
`isBigOpOne_respMart_div_sqrt`. -/
lemma integral_respMart_increment_sq_le [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (n : ℕ)
    (hνk : ∀ a, MemLp id 2 (ν a)) :
    ∫ ω, (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2 ∂P ≤ Var[id; ν k] := by
  have hY2 : MemLp (Y n) 2 P := h.memLp_feedback hνk n
  have hdiff : (fun ω ↦ (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2)
      = fun ω ↦ (actionIndicator A k n ω * (Y n ω - ν.means k)) ^ 2 := by
    funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
  have hGle : h.filtrationAction n
      ≤ mΩ :=
    h.filtrationAction.le n
  have hset : MeasurableSet {ω | A n ω = k} :=
    h.measurable_action n (measurableSet_singleton k)
  have hσ2 : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  rw [hdiff, ← integral_condExp hGle,
    integral_congr_ae (condExp_respMart_increment_sq h k n hνk),
    integral_mul_const (Var[id; ν k])]
  simp only [actionIndicator]
  rw [integral_indicator_const (1 : ℝ) hset, smul_eq_mul, mul_one]
  have hprob : (P {ω | A n ω = k}).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  exact mul_le_of_le_one_left hσ2 hprob

/-- **The response martingale is `O_p(√n)`.**
For each arm `k`, under Condition **A** (square-integrable arm rewards,
`hνk : ∀ a, MemLp id 2 (ν a)`), `Q_{n,k} / √n = O_p(1)`, i.e. `Q_{n,k} = O_p(√n)`.

`Q k` is a martingale for the action-augmented filtration `𝒢 = filtrationAction`
(`martingale_respMart`) with `Q k 0 = 0`, and its increment second moments are bounded by the arm
variance: `∫ (ΔQ)² ≤ V_k`. Indeed the `𝒢`-conditional second moment is `𝟙{A n = k}·V_k`
(`condExp_respMart_increment_sq`), so by the tower property `∫ (ΔQ)² = V_k · P{A n = k} ≤ V_k`.
Then `isBigOpOne_martingale_div_sqrt` applies with `σ² = V_k`. -/
lemma isBigOpOne_respMart_div_sqrt [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) :
    IsBigOpOne P (fun n ω ↦ respMart ν A Y k n ω / √n) := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  -- The martingale increment `ΔQ` squares to the squared centered response.
  have hdiff : ∀ m, (fun ω ↦ (respMart ν A Y k (m + 1) ω - respMart ν A Y k m ω) ^ 2)
      = fun ω ↦ (actionIndicator A k m ω
        * (Y m ω - ν.means k)) ^ 2 := by
    intro m; funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
  have hM := martingale_respMart h hint k
  have hM2 : ∀ n, MemLp (respMart ν A Y k n) 2 P :=
    fun n ↦ memLp_respMart h hY2 k n
  have hM0 : respMart ν A Y k 0 =ᵐ[P] 0 := by filter_upwards with ω; simp [respMart]
  have hσ2 : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  have hinc : ∀ n, ∫ ω, (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2 ∂P
      ≤ Var[id; ν k] := fun n ↦ integral_respMart_increment_sq_le h k n hνk
  exact isBigOpOne_martingale_div_sqrt hM hM2 hM0 (Var[id; ν k]) hσ2 hinc

end AlphaRAR
