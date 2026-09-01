/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.ARTSConsistency
public meta import LeanSpec

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

@[expose] public section

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

/-- The deterministic regularized estimator of the assignment/response process equals the
regularized empirical mean of arm `k`. -/
lemma estimator_eq (θ₀ : 𝓐 → ℝ) (k : 𝓐) (t : ℕ) (ω : Ω) :
    estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) t
      = (sumRewards A Y k t ω + θ₀ k) / ((pullCount A k t ω : ℝ) + 1) := by
  rw [estimator, sum_actionIndicator_mul A Y]
  congr 2
  simp only [actionIndicator]
  exact count_indicator_eq_pullCount k t ω

/-- The process plug-in target `ρ̂_{n+1,k}` equals the history-level target evaluated on the
history of the process up to time `n`. -/
@[specifies histTarget "the history-level target is the process target, read on the process's own \
history — including the index shift: the history up to `n` determines `ρ̂` at time `n+1`",
  specifies aRTSTarget "the process target is a function of the observed history alone, so it is \
implementable: `ρ̂_{n+1,k}` is computable from the first `n+1` observations and nothing else"]
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

/-! ### The selection probability is the policy evaluated on the history -/

omit [DecidableEq 𝓐] in
/-- **The selection probability is the policy's mass on the arm** (the linchpin of the bridge).
For `m = n+1`, the aRTS selection probability `p_{n+1,k} = P[𝟙{A_{n+1}=k} | ℱ_n]` equals, almost
surely, the probability the policy assigns to arm `k` given the history:
`(alg.policy n (history A Y n ω) {k}).toReal`. Proved from the algorithm's `hasCondDistrib_action`
via `HasCondDistrib.condExp_comp_eq` applied to the indicator `g = 𝟙_{· = k}`. -/
@[specifies aRTSSelProb "identifies the conditional expectation with the quantity a designer \
controls — the mass the policy puts on arm `k` given the history. Without this the definition \
would be a probabilistic object with no operational meaning"]
lemma aRTSSelProb_succ_ae [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (n : ℕ) :
    aRTSSelProb A k h.filtration P (n + 1)
      =ᵐ[P] fun ω ↦ (alg.policy n (history A Y n ω) {k}).toReal := by
  let 𝔽 := h.filtration
  set g : 𝓐 → ℝ := Set.indicator {k} (fun _ ↦ (1 : ℝ)) with hg_def
  have hg : StronglyMeasurable g := stronglyMeasurable_const.indicator (measurableSet_singleton k)
  have hgeq : (fun ω ↦ g (A (n + 1) ω)) = actionIndicator A k (n + 1) := by
    funext ω
    by_cases hak : A (n + 1) ω = k
    · have h1 : A (n + 1) ω ∈ ({k} : Set 𝓐) := hak
      have h2 : ω ∈ {ω | A (n + 1) ω = k} := hak
      rw [hg_def, actionIndicator, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · have h1 : A (n + 1) ω ∉ ({k} : Set 𝓐) := hak
      have h2 : ω ∉ {ω | A (n + 1) ω = k} := hak
      rw [hg_def, actionIndicator, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have hint : Integrable (fun ω ↦ g (A (n + 1) ω)) P := by
    rw [hgeq]; exact integrable_actionIndicator P k (h.measurable_action (n + 1))
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
@[specifies IsARTS "the history-level condition really is the process-level throttle: stating it \
on arbitrary histories, rather than on the realised process, costs nothing",
  specifies aRTSUnder "fixes the sense of the inequality: `aRTSUnder` is the *under*-sampled event \
`N ≤ m ρ̂`, so it is its complement that triggers the throttle"]
lemma throttle_of_isARTS [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {α : ℝ} (hARTS : IsARTS alg θ₀ T α) (k : 𝓐) :
    ∀ᵐ ω ∂P, ∀ m, ¬ aRTSUnder A Y θ₀ T k ω m →
      aRTSSelProb A k h.filtration P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k := by
  rw [ae_all_iff]
  intro m
  cases m with
  | zero =>
    filter_upwards with ω hm
    exact absurd (by simp [aRTSUnder] : aRTSUnder A Y θ₀ T k ω 0) hm
  | succ n =>
    filter_upwards [aRTSSelProb_succ_ae h k n] with ω hsel hm
    rw [hsel, ← histTarget_eq]
    refine hARTS.throttle n (history A Y n ω) k ?_
    -- Over-sampling: `¬ (N_{n+1,k} ≤ (n+1) ρ̂_{n+1,k})` gives `(n+1) ρ̂ < N_{n+1,k}`.
    have hlt : (↑(n + 1) : ℝ) * aRTSTarget A Y θ₀ T (n + 1) ω k
        < (pullCount A k (n + 1) ω : ℝ) := by
      rw [aRTSUnder] at hm
      exact lt_of_not_ge hm
    rw [histTarget_eq, ← histCount_eq, count_indicator_eq_pullCount]
    push_cast at hlt ⊢
    linarith

/-- **Consistency of an aRTS algorithm** (blueprint `cor:aRTS_consistency`, algorithm form). If
`alg` is an aRTS design (`IsARTS alg θ₀ T α`) driving an algorithm–environment sequence under a
stationary environment with `Y_n ∈ L²` (Condition **A**) and continuous simplex-valued target map
`T`, then almost surely the allocation proportions and plug-in targets converge to a common limit:
`N_{n,k}/n → u_k` and `ρ̂_{n,k} → u_k` for every arm `k`. This is `aRTS_consistency` with its
throttle hypothesis discharged by `throttle_of_isARTS`. -/
@[specifies IsARTS "the membership condition is strong enough to be worth having: it alone (plus \
Condition **A** and a simplex-valued continuous `T`) forces the allocation proportions to converge"]
lemma aRTS_consistency_of_isARTS [Fintype 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (u k))
        ∧ Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop (𝓝 (u k)) :=
  aRTS_consistency h hνk θ₀ T hT hTnn hTsum α hα (fun k ↦ throttle_of_isARTS h hARTS k)

/-- **aRTS allocation proportions in pull-count form** (blueprint `cor:aRTS_consistency`). Restates
the aRTS consistency limit `N_{n,k}/n → u_k` (`aRTS_consistency_of_isARTS`) with the pull count
`pullCount A k n` — the `N_{n,k}` vocabulary of the LIL and CLT rate lemmas — in place of
`count (𝟙{A · = k})`: almost surely there is a common limit vector `u` with
`(pullCount A k n)/n → u_k` for every arm `k`. This is exactly the proportion input `hN` of the
loglog estimator rate `abs_estimator_sub_le_rate_loglog_of_proportion` (blueprint `lem:theta_LIL`);
the only piece still needed to pin the limiting proportion `v_k := u_k` is its strict positivity
`u_k > 0` (the non-sparsity of Condition **B**, deferred). -/
lemma aRTS_pullCount_div_ae_tendsto [Fintype 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (u k)) := by
  filter_upwards [aRTS_consistency_of_isARTS h hνk hT hTnn hTsum hα hARTS] with ω hω
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, fun k ↦ (hu k).1⟩

/-- **Estimator consistency for an aRTS algorithm** (blueprint `lem:theta_consistent`). Under
Condition **B**'s non-sparsity — `hTpos`, i.e. `T` maps the product of the attainable sets
(`attainableSet`) into the positive orthant — an aRTS design's sequential estimator converges a.s.
to the true parameter: `θ̂_n → θ = (ν.means k)_k`. The aRTS consistency `aRTS_consistency_of_isARTS`
supplies the joint limit `N_{n,k}/n → u_k` together with `ρ̂_{n,k} → u_k` (its plug-in target
`aRTSTarget` is by definition `T(θ̂_n)`); `theta_consistent_pi_of_condB` then makes the shared limit
`u` positive — so every arm is sampled infinitely often — and identifies each estimator limit as its
arm mean. This is `lem:theta_consistent` with Condition **B**'s non-sparsity as the only extra
hypothesis. -/
lemma aRTS_theta_consistent [Fintype 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) :
    ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) atTop (𝓝 ν.means) := by
  refine theta_consistent_pi_of_condB h hνk θ₀ T hT hTpos ?_
  filter_upwards [aRTS_consistency_of_isARTS h hνk hT hTnn hTsum hα hARTS] with ω hω
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, hu⟩

/-- **Allocation proportions converge to the target** (blueprint `thm:LLN`, first conclusion). For
an aRTS design, under Condition **B** the allocation proportion converges a.s. to the
*deterministic* target `N_{n,k}/n → v_k = T(θ)_k`. Combining `aRTS_theta_consistent` (`θ̂_n → θ`, so
`ρ̂_{n,k} = T(θ̂_n)_k → T(θ)_k` by continuity) with the joint aRTS consistency (`N_{n,k}/n` and
`ρ̂_{n,k}` share the limit `u_k`) identifies `u_k = T(θ)_k = v_k`. -/
lemma aRTS_proportion_tendsto [Fintype 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) (k : 𝓐) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ))
      atTop (𝓝 (T ν.means k)) := by
  filter_upwards [aRTS_consistency_of_isARTS h hνk hT hTnn hTsum hα hARTS,
    aRTS_theta_consistent h hνk hT hTnn hTsum hα hARTS hTpos] with ω hjω hθω
  obtain ⟨u, hu⟩ := hjω
  have hrho : Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop
      (𝓝 (T ν.means k)) :=
    tendsto_pi_nhds.mp ((hT.tendsto _).comp hθω) k
  have huk : u k = T ν.means k := tendsto_nhds_unique (hu k).2 hrho
  rw [← huk]
  exact (hu k).1

end AlphaRAR
