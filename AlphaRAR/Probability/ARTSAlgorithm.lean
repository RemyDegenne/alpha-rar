/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Probability.ARTSConsistency

/-!
# The aRTS design family as a property of an `Algorithm`

`aRTS_consistency` (blueprint `cor:aRTS_consistency`) proves consistency of the aRTS proportions
*given* a process-level throttle hypothesis on the selection probabilities. This file expresses that
throttle as a property `IsARTS` of the driving `Algorithm` itself — a membership condition for the
aRTS *family* — and bridges it back to the consistency theorem.

An `Algorithm 𝓐 ℝ` chooses the next action from a history `h : Iic n → 𝓐 × ℝ` via a Markov kernel
`alg.policy n`. The selection probability of arm `k` for patient `n+1` given the history is
`(alg.policy n h {k}).toReal`. `IsARTS alg θ₀ T α` requires this to be throttled — bounded by
`α · ρ̂_k(h)` — whenever arm `k` is over-sampled in `h`, where the plug-in target `ρ̂_k(h)` and the
counts are computed from the history via the finite-action bookkeeping of `LeanMachineLearning`
(`pullCount'`, `sumRewards'`).

The bridge `aRTS_consistency_of_isARTS` shows that any `IsARTS` algorithm satisfies the throttle
hypothesis of `aRTS_consistency`, and hence its allocation proportions converge a.s. The linchpin is
that the process selection probability `P[𝟙{A_{n+1}=k} | ℱ_n]` equals `(policy n (history n) {k})`
a.e. — a conditional-expectation-from-conditional-distribution computation
(`HasCondDistrib.condExp_comp_eq`, via the algorithm's `hasCondDistrib_action`).

## Main results

* `AlphaRAR.IsARTS`: the aRTS family membership predicate on an `Algorithm`.
* `AlphaRAR.aRTS_consistency_of_isARTS`: an `IsARTS` algorithm's proportions converge a.s.
-/

open MeasureTheory ProbabilityTheory Filter Learning Finset

open scoped Topology

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

-- `[StandardBorelSpace 𝓐] [Nonempty 𝓐]` are needed only by the two lemmas passing through
-- `HasCondDistrib.condExp_comp_eq` on the action, and `[Fintype 𝓐]` only by the final corollary;
-- they are attached to those declarations rather than the whole file.

/-! ### History-level plug-in target and the family predicate -/

/-- History-level plug-in target `ρ̂_k`: the target map `T` applied to the vector of regularized
empirical means `(sumRewards' + θ₀)/(pullCount' + 1)` computed from a history `h : Iic n → 𝓐 × ℝ`.
This is the design's target as a function of the observed history, matching `aRTSTarget` on the
history of the process (`histTarget_eq`). -/
noncomputable def histTarget (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (k : 𝓐) (n : ℕ)
    (h : Iic n → 𝓐 × ℝ) : ℝ :=
  T (fun k' ↦ (sumRewards' n h k' + θ₀ k') / ((pullCount' n h k' : ℝ) + 1)) k

/-- **The aRTS design family** (blueprint `def:aRTS`, algorithm form). An algorithm `alg` is an
`α`-throttled aRTS design with offsets `θ₀` and target map `T` if its policy throttles every
over-sampled arm: for any history `h : Iic n → 𝓐 × ℝ`, if arm `k` is over-sampled
(`N_{n+1,k}(h) > (n+1) ρ̂_k(h)`), then the probability the policy assigns to arm `k` for the next
patient is at most `α ρ̂_k(h)`. -/
structure IsARTS (alg : Algorithm 𝓐 ℝ) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (α : ℝ) : Prop where
  throttle : ∀ (n : ℕ) (h : Iic n → 𝓐 × ℝ) (k : 𝓐),
    ((n : ℝ) + 1) * histTarget θ₀ T k n h < (pullCount' n h k : ℝ) →
      (alg.policy n h {k}).toReal ≤ α * histTarget θ₀ T k n h

/-! ### History-statistic identities -/

/-- The weighted assignment sum equals the summed rewards of arm `k`. -/
lemma sum_armIndicator_mul (k : 𝓐) (t : ℕ) (ω : Ω) :
    ∑ j ∈ Finset.range t, armIndicator A k j ω * Y j ω = sumRewards A Y k t ω := by
  rw [sumRewards]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [armIndicator, Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs <;> simp

/-- The deterministic regularized estimator of the assignment/response process equals the
regularized empirical mean of arm `k`. -/
lemma estimator_eq (θ₀ : 𝓐 → ℝ) (k : 𝓐) (t : ℕ) (ω : Ω) :
    estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) t
      = (sumRewards A Y k t ω + θ₀ k) / ((pullCount A k t ω : ℝ) + 1) := by
  rw [estimator, sum_armIndicator_mul]
  congr 2
  simp only [armIndicator]
  exact count_indicator_eq_pullCount k t ω

/-- The process plug-in target `ρ̂_{n+1,k}` equals the history-level target evaluated on the
history of the process up to time `n`. -/
lemma histTarget_eq (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (k : 𝓐) (n : ℕ) (ω : Ω) :
    histTarget θ₀ T k n (history A Y n ω) = aRTSTarget A Y θ₀ T (n + 1) ω k := by
  rw [aRTSTarget, histTarget]
  congr 1
  funext k'
  have hsr : sumRewards A Y k' (n + 1) ω = sumRewards' n (history A Y n ω) k' :=
    sumRewards_add_one_eq_sumRewards'
  have hpc : pullCount A k' (n + 1) ω = pullCount' n (history A Y n ω) k' :=
    pullCount_add_one_eq_pullCount' (R' := Y)
  rw [estimator_eq, hsr, hpc]

/-- The process count `N_{n+1,k}` equals the history-level count on the history up to time `n`. -/
lemma histCount_eq (k : 𝓐) (n : ℕ) (ω : Ω) :
    count (fun j ↦ armIndicator A k j ω) (n + 1) = (pullCount' n (history A Y n ω) k : ℝ) := by
  have hpc : pullCount A k (n + 1) ω = pullCount' n (history A Y n ω) k :=
    pullCount_add_one_eq_pullCount' (R' := Y)
  rw [count_indicator_eq_pullCount, hpc]

/-! ### The selection probability is the policy evaluated on the history -/

omit [DecidableEq 𝓐] in
/-- **The selection probability is the policy's mass on the arm** (the linchpin of the bridge).
For `m = n+1`, the aRTS selection probability `p_{n+1,k} = P[𝟙{A_{n+1}=k} | ℱ_n]` equals, almost
surely, the probability the policy assigns to arm `k` given the history:
`(alg.policy n (history A Y n ω) {k}).toReal`. Proved from the algorithm's `hasCondDistrib_action`
via `HasCondDistrib.condExp_comp_eq` applied to the indicator `g = 𝟙_{· = k}`. -/
lemma aRTSSelProb_succ_ae [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (n : ℕ) :
    aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P (n + 1)
      =ᵐ[P] fun ω ↦ (alg.policy n (history A Y n ω) {k}).toReal := by
  let 𝔽 := IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback
  set g : 𝓐 → ℝ := Set.indicator {k} (fun _ ↦ (1 : ℝ)) with hg_def
  have hg : StronglyMeasurable g := stronglyMeasurable_const.indicator (measurableSet_singleton k)
  have hgeq : (fun ω ↦ g (A (n + 1) ω)) = armIndicator A k (n + 1) := by
    funext ω
    by_cases hak : A (n + 1) ω = k
    · have h1 : A (n + 1) ω ∈ ({k} : Set 𝓐) := hak
      have h2 : ω ∈ {ω | A (n + 1) ω = k} := hak
      rw [hg_def, armIndicator, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · have h1 : A (n + 1) ω ∉ ({k} : Set 𝓐) := hak
      have h2 : ω ∉ {ω | A (n + 1) ω = k} := hak
      rw [hg_def, armIndicator, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have hint : Integrable (fun ω ↦ g (A (n + 1) ω)) P := by
    rw [hgeq]; exact integrable_armIndicator h k (n + 1)
  have hbridge : P[fun ω ↦ g (A (n + 1) ω) | 𝔽.shiftDown (n + 1)]
      =ᵐ[P] fun ω ↦ ∫ a, g a ∂(alg.policy n (history A Y n ω)) :=
    (h.hasCondDistrib_action n).condExp_comp_eq (h.measurable_history n) hg hint
  have hsel : aRTSSelProb A k 𝔽 P (n + 1) = P[fun ω ↦ g (A (n + 1) ω) | 𝔽.shiftDown (n + 1)] := by
    unfold aRTSSelProb
    rw [← hgeq]
  rw [hsel]
  refine hbridge.trans ?_
  filter_upwards with ω
  rw [hg_def, MeasureTheory.integral_indicator_const (1 : ℝ) (measurableSet_singleton k)]
  simp [Measure.real]

/-! ### The bridge: `IsARTS` implies consistency -/

/-- **`IsARTS` discharges the throttle hypothesis of `aRTS_consistency`.** If `alg` is an aRTS
design (`IsARTS`), then for every arm the process selection probabilities satisfy the throttle:
whenever arm `k` is over-sampled at time `m`, `p_{m,k} ≤ α ρ̂_{m,k}`. At `m = 0` the condition is
vacuous (`N_0 = 0`); at `m = n+1` it is `IsARTS.throttle` transported through `aRTSSelProb_succ_ae`,
`histTarget_eq` and `histCount_eq`. -/
lemma throttle_of_isARTS [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {α : ℝ} (hARTS : IsARTS alg θ₀ T α) (k : 𝓐) :
    ∀ᵐ ω ∂P, ∀ m, ¬ aRTSUnder A Y θ₀ T k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k := by
  rw [ae_all_iff]
  intro m
  cases m with
  | zero =>
    filter_upwards with ω hm
    exact absurd (by simp [aRTSUnder, count] : aRTSUnder A Y θ₀ T k ω 0) hm
  | succ n =>
    filter_upwards [aRTSSelProb_succ_ae h k n] with ω hsel hm
    rw [hsel, ← histTarget_eq]
    refine hARTS.throttle n (history A Y n ω) k ?_
    -- Over-sampling: `¬ (N_{n+1,k} ≤ (n+1) ρ̂_{n+1,k})` gives `(n+1) ρ̂ < N_{n+1,k}`.
    have hlt : (↑(n + 1) : ℝ) * aRTSTarget A Y θ₀ T (n + 1) ω k
        < count (fun j ↦ armIndicator A k j ω) (n + 1) := by
      rw [aRTSUnder] at hm
      exact lt_of_not_ge hm
    rw [histTarget_eq, ← histCount_eq]
    push_cast at hlt ⊢
    linarith

/-- **Consistency of an aRTS algorithm** (blueprint `cor:aRTS_consistency`, algorithm form). If
`alg` is an aRTS design (`IsARTS alg θ₀ T α`) driving an algorithm–environment sequence under a
stationary environment with `Y_n ∈ L²` (Condition **A**) and continuous simplex-valued target map
`T`, then almost surely the allocation proportions and plug-in targets converge to a common limit:
`N_{n,k}/n → u_k` and `ρ̂_{n,k} → u_k` for every arm `k`. This is `aRTS_consistency` with its
throttle hypothesis discharged by `throttle_of_isARTS`. -/
lemma aRTS_consistency_of_isARTS [Fintype 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n / (n : ℝ)) atTop (𝓝 (u k))
        ∧ Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop (𝓝 (u k)) :=
  aRTS_consistency h hY2 θ₀ T hT hTnn hTsum α hα (fun k ↦ throttle_of_isARTS h hARTS k)

end AlphaRAR
