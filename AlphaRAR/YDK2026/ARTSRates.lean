/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.ARTSAlgorithm
public import AlphaRAR.YDK2026.PluginTargetRate

/-!
# Strong consistency and rates for the aRTS design

Assembling Theorem 4.1 of the paper, strong consistency and rates, for a concrete aRTS design:
under Conditions **A** (reward second moments) and **B** (`T` differentiable and non-sparse),
almost surely for every arm `k`,
* the allocation proportion converges to the target, `N_{n,k}/n → v_k = T(θ)_k`;
* the estimator is consistent, `θ̂_{n,k} → θ_k`;
* the estimator achieves the loglog rate, `θ̂_{n,k} - θ_k = O(√(log log n / n))`;
* the plug-in target achieves the loglog rate, `ρ̂_{n,k} - v_k = O(√(log log n / n))`.

The first two are `aRTS_proportion_tendsto` and `aRTS_theta_consistent`; the estimator rate
(`aRTS_theta_rate`) is the subsampled loglog LIL discharged through the positive allocation
proportion, and the target rate (`aRTS_rho_rate`) sends it through the delta-method rate
`rho_rate`. Condition **B** enters as `hTpos` (non-sparsity) and `hT_diff`
(differentiability at `θ`).
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Learning Real Asymptotics

open scoped Topology

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [Fintype 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
/-- **Positive allocation proportion at an abstract hitting time** (per-arm). The
abstract-hitting-time generalisation of `aRTS_count_proportion_pos`: given the consistency
throttle `hthrottle` and smallness `hgs`, together with Condition **B**'s non-sparsity `hTpos`, each
allocation proportion `N_{n,k}/n` converges a.s. to a *positive* limit `v_k = T(θ)_k`. The target
`θ` is attainable (a.s. limit of the estimator, `theta_consistent_of_hitting`), so `hTpos` makes
`T(θ)` positive; `consistency_of_hitting` identifies the proportion limit with `T(θ)`. -/
lemma count_proportion_pos_of_hitting
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k h.filtration P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hgs : ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ((pullCount A k (hitting (Q k ω) n) ω : ℝ)
          - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k) / (n : ℝ) < δ)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) (k : 𝓐) :
    ∀ᵐ ω ∂P, ∃ uk : ℝ, 0 < uk ∧ Tendsto (fun n ↦ (pullCount A k n ω : ℝ)
      / (n : ℝ)) atTop (𝓝 uk) := by
  have hmem : ∀ k', ν.means k' ∈ attainableSet A Y (θ₀ k') k' := by
    obtain ⟨ω, hω⟩ :=
      (theta_consistent_of_hitting h hνk θ₀ T hT hTnn hTsum α hα Q hthrottle hgs hTpos).exists
    exact fun k' ↦ estimator_limit_mem_attainableSet k' (θ₀ k') (tendsto_pi_nhds.mp hω k')
  have hposk : 0 < T ν.means k := hTpos ν.means hmem k
  filter_upwards [consistency_of_hitting h hνk θ₀ T hT hTnn hTsum α hα Q hthrottle hgs,
    theta_consistent_of_hitting h hνk θ₀ T hT hTnn hTsum α hα Q hthrottle hgs hTpos] with ω hjω hθω
  obtain ⟨u, hu⟩ := hjω
  have hrho : Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop
      (𝓝 (T ν.means k)) := tendsto_pi_nhds.mp ((hT.tendsto _).comp hθω) k
  have huk : u k = T ν.means k := tendsto_nhds_unique (hu k).2 hrho
  exact ⟨u k, huk.symm ▸ hposk, (hu k).1⟩

/-- **Positive allocation proportion for an aRTS design** (count form, per-arm). The `aRTS`
instantiation of `count_proportion_pos_of_hitting` at the last under-sampling time. -/
lemma aRTS_count_proportion_pos (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) (k : 𝓐) :
    ∀ᵐ ω ∂P, ∃ uk : ℝ, 0 < uk ∧ Tendsto (fun n ↦ (pullCount A k n ω : ℝ)
      / (n : ℝ)) atTop (𝓝 uk) :=
  count_proportion_pos_of_hitting h hνk hT hTnn hTsum hα (aRTSUnder A Y θ₀ T)
    (fun k ↦ throttle_of_isARTS h hARTS k)
    (aRTS_smallness_all θ₀ T) hTpos k

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
/-- **Loglog rate of the estimator at an abstract hitting time** (the second conclusion of
Theorem 4.1 of the paper, generic form). The abstract-hitting-time generalisation of
`aRTS_theta_rate`: the estimator achieves `θ̂_{n,k} - θ_k = O(√(log log n / n))` a.s. This is the
subsampled loglog LIL `abs_estimator_sub_le_rate_loglog_of_pos_count`, whose positive-proportion
input is `count_proportion_pos_of_hitting`, restated as an `IsBigO` (the rate function is
nonnegative, so the absolute values of the pointwise bound are the norms of the `IsBigO`). -/
lemma theta_rate_of_hitting (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k h.filtration P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hgs : ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ((pullCount A k (hitting (Q k ω) n) ω : ℝ)
          - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k) / (n : ℝ) < δ)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k)
        =O[atTop] (fun n ↦ √(n * log (log n)) / (n : ℝ)) := by
  filter_upwards [abs_estimator_sub_le_rate_loglog_of_pos_count h k (θ₀ k) (hνk k)
    (by simpa only [← count_indicator_eq_pullCount] using
      count_proportion_pos_of_hitting h hνk hT hTnn hTsum hα Q hthrottle hgs hTpos k)] with ω hω
  obtain ⟨C', hC'⟩ := hω
  refine isBigO_iff.mpr ⟨C', ?_⟩
  filter_upwards [hC'] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n))]
  exact hn

omit [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
/-- **Loglog rate of the plug-in target at an abstract hitting time** (the third conclusion of
Theorem 4.1 of the paper, generic form). The abstract-hitting-time generalisation of
`aRTS_rho_rate`: the plug-in target achieves `ρ̂_{n,k} - v_k = O(√(log log n / n))` a.s., combining
the estimator consistency `theta_consistent_of_hitting` and the per-arm loglog estimator rate
`theta_rate_of_hitting` through the delta-method rate `rho_rate`. -/
lemma rho_rate_of_hitting (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k h.filtration P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hgs : ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ((pullCount A k (hitting (Q k ω) n) ω : ℝ)
          - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k) / (n : ℝ) < δ)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) k - T ν.means k)
        =O[atTop] (fun n ↦ √(n * log (log n)) / (n : ℝ)) := by
  exact rho_rate hT_diff
    (theta_consistent_of_hitting h hνk θ₀ T hT hTnn hTsum α hα Q hthrottle hgs hTpos)
    (fun k' ↦ theta_rate_of_hitting h hνk hT hTnn hTsum hα Q hthrottle hgs hTpos k') k

/-- **Loglog rate of the estimator for an aRTS design** (the second conclusion of Theorem 4.1 of
the paper). The `aRTS` instantiation of `theta_rate_of_hitting`:
`θ̂_{n,k} - θ_k = O(√(log log n / n))` a.s. -/
theorem aRTS_theta_rate (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k)
        =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)) :=
  theta_rate_of_hitting h hνk hT hTnn hTsum hα (aRTSUnder A Y θ₀ T)
    (fun k ↦ throttle_of_isARTS h hARTS k)
    (aRTS_smallness_all θ₀ T)
    hTpos k

/-- **Loglog rate of the plug-in target for an aRTS design** (the third conclusion of Theorem 4.1
of the paper). The `aRTS` instantiation of `rho_rate_of_hitting`:
`ρ̂_{n,k} - v_k = O(√(log log n / n))` a.s. -/
theorem aRTS_rho_rate (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) k - T ν.means k)
        =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)) :=
  rho_rate_of_hitting h hνk hT hTnn hTsum hα (aRTSUnder A Y θ₀ T)
    (fun k ↦ throttle_of_isARTS h hARTS k)
    (aRTS_smallness_all θ₀ T)
    hTpos hT_diff k

/-- **Strong consistency and rates for an aRTS design** (Theorem 4.1 of the paper). Under
Conditions **A** (`hνk`) and **B** (`hT`, `hTpos`, `hT_diff`, and the simplex conditions `hTnn`,
`hTsum`) an `α`-throttled aRTS design satisfies, almost surely for every arm `k`:
the allocation proportion converges to the target `N_{n,k}/n → v_k = T(θ)_k`; the estimator is
consistent `θ̂_{n,k} → θ_k` and achieves the loglog rate `θ̂_{n,k} - θ_k = O(√(log log n / n))`; and
the plug-in target achieves the same rate `ρ̂_{n,k} - v_k = O(√(log log n / n))` — the last two are
the paper's `Θ̂_n - Θ = O(√(log log n / n))` and `n(ρ̂_n - v) = O(√(n log log n))`. Bundles
`aRTS_proportion_tendsto`, `aRTS_theta_consistent`, `aRTS_theta_rate`, `aRTS_rho_rate`. -/
theorem aRTS_LLN (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTS : IsARTS alg θ₀ T α)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means) (k : 𝓐) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (T ν.means k)) ∧
      Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
        (Y · ω) (θ₀ k) n) atTop (𝓝 (ν.means k)) ∧
      (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k)
          =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)) ∧
      (fun n ↦ T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
        (Y · ω) (θ₀ k') n) k - T ν.means k)
          =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)) := by
  filter_upwards [aRTS_proportion_tendsto h hνk hT hTnn hTsum hα hARTS hTpos k,
    aRTS_theta_consistent h hνk hT hTnn hTsum hα hARTS hTpos,
    aRTS_theta_rate h hνk hT hTnn hTsum hα hARTS hTpos k,
    aRTS_rho_rate h hνk hT hTnn hTsum hα hARTS hTpos hT_diff k]
    with ω hprop hθ hθrate hrate
  exact ⟨hprop, tendsto_pi_nhds.mp hθ k, hθrate, hrate⟩

end AlphaRAR
