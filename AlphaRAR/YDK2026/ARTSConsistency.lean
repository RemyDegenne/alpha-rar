/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.YDK2026.ConsistencyMatching
import AlphaRAR.YDK2026.ResponseConsistency
import LeanSpec

/-!
# Consistency of the aRTS design family

This file instantiates the modular consistency theorem `consistency_of_generic_ae`
(blueprint `thm:generic_main`) for the aRTS design family, giving the concrete strong law of
large numbers for the allocation proportions (blueprint `thm:LLN`, consistency direction).

The aRTS design is specified through three derived per-arm processes of an
`IsAlgEnvSeq` algorithm–environment sequence:

* `armIndicator A k n ω = 𝟙{A n ω = k}` — the assignment indicator;
* `aRTSTarget A Y θ₀ T n ω k = T(θ̂_n)_k` — the plug-in target `ρ̂_{n,k}`, obtained by
  applying a continuous simplex-valued target map `T` to the sequential estimator vector;
* `aRTSSelProb A k ℱ P n ω = P[𝟙{A n = k} | ℱ_{n-1}] ω` — the selection probability `p_{n,k}`,
  the conditional probability of assigning arm `k` to patient `n` given the previous history.

The *design semantics* enter as a single hypothesis on these processes:

* the **throttle** (blueprint `eq:throttle`): whenever arm `k` is over-sampled at time `m`
  (`¬ aRTSUnder`, i.e. `N_{m,k} > m ρ̂_{m,k}`), its selection probability is throttled,
  `p_{m,k} ≤ α ρ̂_{m,k}` (patient `m` uses the target `ρ̂_{m,k}` of patients `0, …, m-1`).

Under this, together with Condition **A** (`hY2 : MemLp (Y n) 2`) and the target map being a
continuous map into the simplex, the allocation proportions converge a.s. to the (random) common
limit of the plug-in targets: `N_{n,k}/n → u_k` and `ρ̂_{n,k} → u_k`.

The throttle itself — that a concrete aRTS selection rule satisfies `eq:throttle` — is the
design-specific step flagged in the blueprint (`prop:aRTS_generic`) and is taken here as a
hypothesis; everything downstream of it is proved.

## Main results

* `AlphaRAR.aRTS_consistency`: the concrete a.s. consistency of the aRTS proportions.
-/

open MeasureTheory ProbabilityTheory Filter Learning

open scoped Topology

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-! ### The aRTS derived processes -/

/-- The aRTS plug-in target `ρ̂_{n,k} = T(θ̂_n)_k`: the continuous target map `T` applied to the
vector of sequential estimators of the arm means. -/
noncomputable def aRTSTarget (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (T : (𝓐 → ℝ) → 𝓐 → ℝ) (n : ℕ) (ω : Ω) (k : 𝓐) : ℝ :=
  T (fun k' ↦ estimator (fun j ↦ armIndicator A k' j ω) (fun j ↦ Y j ω) (θ₀ k') n) k

/-- The aRTS selection probability `p_{n,k} = P[𝟙{A n = k} | ℱ_{n-1}]`: the conditional probability
of assigning arm `k` to patient `n` given the previous history `ℱ.shiftDown n = ℱ_{n-1}`. -/
noncomputable def aRTSSelProb (A : ℕ → Ω → 𝓐) (k : 𝓐) (𝔽 : Filtration ℕ mΩ) (P : Measure Ω)
    (n : ℕ) (ω : Ω) : ℝ :=
  (P[armIndicator A k n | 𝔽.shiftDown n]) ω

/-- The under-sampling event of arm `k` at time `m`: `N_{m,k} ≤ m ρ̂_{m,k}`. -/
def aRTSUnder (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (k : 𝓐) (ω : Ω) (m : ℕ) : Prop :=
  count (fun j ↦ armIndicator A k j ω) m ≤ (m : ℝ) * aRTSTarget A Y θ₀ T m ω k

noncomputable instance {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ}
    {k : 𝓐} {ω : Ω} : DecidablePred (aRTSUnder A Y θ₀ T k ω) :=
  Classical.decPred _

/-! ### The concrete aRTS consistency theorem -/

/-- **Generic a.s. consistency of the aRTS proportions at an abstract hitting time** (blueprint
`thm:generic_main`, consistency direction, for any design with a suitable hitting predicate). This
generalises `aRTS_consistency` from the last under-sampling time `aRTSUnder` to an *arbitrary*
per-arm predicate `Q` for the hitting time `ℓ_{n,k} = hitting (Q k ω) n`: only the throttle
`¬ Q → p ≤ α ρ̂` (`hthrottle`) and the smallness `(N_ℓ - ℓ ρ̂_ℓ)/n → 0` (`hgs`) are design-specific,
and both are taken as hypotheses. The `aRTS` and `aRTSFE` designs then instantiate it with their
respective predicates (last under-sampling time, resp. forced-exploration hitting time). Everything
else — the vanishing normalised martingale, the plug-in-target convergence, and the generic key
inequality (`generic_ineq_of_hitting`, valid for *any* predicate) — is discharged uniformly. -/
lemma consistency_of_hitting [Fintype 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hgs : ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count (fun j ↦ armIndicator A k j ω) (hitting (Q k ω) n)
          - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k) / (n : ℝ) < δ) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n / (n : ℝ)) atTop (𝓝 (u k))
        ∧ Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop (𝓝 (u k)) := by
  let ℱ := IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback
  -- The target map lands in `[0,1]` because it lands in the simplex.
  have hTle1 : ∀ z k, T z k ≤ 1 := fun z k ↦
    (Finset.single_le_sum (fun i _ ↦ hTnn z i) (Finset.mem_univ k)).trans_eq (hTsum z)
  have htgt_nn : ∀ n ω k, 0 ≤ aRTSTarget A Y θ₀ T n ω k := fun n ω k ↦ hTnn _ k
  have htgt_le1 : ∀ n ω k, aRTSTarget A Y θ₀ T n ω k ≤ 1 := fun n ω k ↦ hTle1 _ k
  -- Plug-in-target convergence (`rho_converges`), phrased via `aRTSTarget`.
  have hrho : ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop (𝓝 (u k)) :=
    rho_converges h hY2 θ₀ T hT
  -- Discharge each hypothesis of `consistency_of_generic_ae`.
  have hYsum : ∀ᵐ ω ∂P, ∀ j, ∑ k, armIndicator A k j ω = 1 :=
    Eventually.of_forall fun ω j ↦ sum_armIndicator A j ω
  have hrsum : ∀ᵐ ω ∂P, ∀ n, ∑ k, aRTSTarget A Y θ₀ T n ω k = 1 :=
    Eventually.of_forall fun ω n ↦ by simp only [aRTSTarget]; exact hTsum _
  have hℓle : ∀ k, ∀ᵐ ω ∂P, ∀ n, hitting (Q k ω) n ≤ n :=
    fun k ↦ Eventually.of_forall fun ω n ↦ Nat.findGreatest_le n
  have hu : ∀ k, ∀ᵐ ω ∂P,
      (limUnder atTop fun n ↦ aRTSTarget A Y θ₀ T n ω k) ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    filter_upwards [hrho] with ω hω
    obtain ⟨uu, huu⟩ := hω
    rw [(huu k).limUnder_eq]
    exact ⟨ge_of_tendsto' (huu k) fun n ↦ htgt_nn n ω k,
      le_of_tendsto' (huu k) fun n ↦ htgt_le1 n ω k⟩
  have hru : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop
      (𝓝 (limUnder atTop fun n ↦ aRTSTarget A Y θ₀ T n ω k)) := by
    intro k
    filter_upwards [hrho] with ω hω
    obtain ⟨uu, huu⟩ := hω
    rw [(huu k).limUnder_eq]
    exact huu k
  have hM : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ assignMG (fun j ↦ armIndicator A k j ω)
      (fun j ↦ aRTSSelProb A k ℱ P j ω) n / (n : ℝ)) atTop (𝓝 0) := by
    intro k
    exact assignMG_path_div_ae_tendsto_zero
      (stronglyAdapted_armIndicator h.measurable_action h.measurable_feedback k)
      (integrable_armIndicator h.measurable_action P k)
      (fun n ↦ Eventually.of_forall fun ω ↦ armIndicator_nonneg A k n ω)
      (fun n ↦ Eventually.of_forall fun ω ↦ armIndicator_le_one A k n ω)
  -- Selection probabilities are `≤ 1` (conditional expectation of a `≤ 1` indicator).
  have hp1 : ∀ k, ∀ᵐ ω ∂P, ∀ m, aRTSSelProb A k ℱ P m ω ≤ 1 := by
    intro k
    rw [ae_all_iff]
    intro m
    have hmono := condExp_mono (m := ℱ.shiftDown m)
      (integrable_armIndicator h.measurable_action P k m)
      (integrable_const (1 : ℝ)) (Eventually.of_forall fun ω ↦ armIndicator_le_one A k m ω)
    rw [condExp_const (ℱ.shiftDown.le m)] at hmono
    filter_upwards [hmono] with ω hω
    exact hω
  -- Key inequality (`generic_ineq_of_hitting`, constant `1`), valid for any predicate.
  have hgen : ∀ k, ∀ᵐ ω ∂P, ∀ n,
      count (fun j ↦ armIndicator A k j ω) n - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k
        ≤ 1 + (count (fun j ↦ armIndicator A k j ω) (hitting (Q k ω) n)
              - (hitting (Q k ω) n : ℝ)
                * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k)
          + (auxU (fun j ↦ armIndicator A k j ω) (fun j ↦ aRTSSelProb A k ℱ P j ω)
                (fun j ↦ aRTSTarget A Y θ₀ T j ω k) α n
              - auxU (fun j ↦ armIndicator A k j ω) (fun j ↦ aRTSSelProb A k ℱ P j ω)
                (fun j ↦ aRTSTarget A Y θ₀ T j ω k) α
                (hitting (Q k ω) n)) := by
    intro k
    filter_upwards [hthrottle k, hp1 k] with ω hthr hp1ω
    exact generic_ineq_of_hitting (fun j ↦ armIndicator A k j ω)
      (fun j ↦ aRTSSelProb A k ℱ P j ω) (fun j ↦ aRTSTarget A Y θ₀ T j ω k) α
      (Q k ω) hthr hp1ω (fun m ↦ mul_nonneg hα.1 (htgt_nn m ω k))
  -- Assemble via the modular theorem (the smallness `hgs` is the design-specific hypothesis).
  have hcons := consistency_of_generic_ae (μ := P)
    (Y := fun j ω k ↦ armIndicator A k j ω)
    (pp := fun j ω k ↦ aRTSSelProb A k ℱ P j ω)
    (r := fun n ω k ↦ aRTSTarget A Y θ₀ T n ω k)
    (u := fun ω k ↦ limUnder atTop fun n ↦ aRTSTarget A Y θ₀ T n ω k)
    (α := α) (C := 1) (ℓ := fun k ω n ↦ hitting (Q k ω) n)
    hα hYsum hrsum hℓle hu hru hM hgen hgs
  filter_upwards [hcons, hrho] with ω hcons_ω hrho_ω
  obtain ⟨uu, huu⟩ := hrho_ω
  refine ⟨uu, fun k ↦ ⟨?_, huu k⟩⟩
  have hk := hcons_ω k
  rwa [(huu k).limUnder_eq] at hk

/-- **Estimator consistency at an abstract hitting time** (blueprint `lem:theta_consistent`, generic
form). The abstract-hitting-time generalisation of `aRTS_theta_consistent`: from the joint
consistency `consistency_of_hitting` (whose throttle `hthrottle` and smallness `hgs` are the
design-specific inputs) and Condition **B**'s non-sparsity `hTpos`, the sequential estimator
converges a.s. to the true parameter `θ̂_n → θ = ((ν k)[id])_k`, via the design-independent
`theta_consistent_pi_of_condB`. -/
lemma theta_consistent_of_hitting [Fintype 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hgs : ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count (fun j ↦ armIndicator A k j ω) (hitting (Q k ω) n)
          - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k) / (n : ℝ) < δ)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) :
    ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ armIndicator A k' j ω)
      (fun j ↦ Y j ω) (θ₀ k') n) atTop (𝓝 (fun k ↦ (ν k)[id])) := by
  classical
  refine theta_consistent_pi_of_condB h hY2 θ₀ T hT hTpos ?_
  filter_upwards [consistency_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα Q hthrottle hgs] with ω hω
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, fun k ↦ ⟨((hu k).1).congr fun n ↦ by rw [count_indicator_eq_pullCount], (hu k).2⟩⟩

/-- **Allocation proportions converge to the target at an abstract hitting time** (blueprint
`thm:LLN`, first conclusion, generic form). The abstract-hitting-time generalisation of
`aRTS_proportion_tendsto`: combining the joint consistency `consistency_of_hitting`
(`N_{n,k}/n` and `ρ̂_{n,k}` share the random limit `u_k`) with the estimator consistency
`theta_consistent_of_hitting` (so `ρ̂_{n,k} → T(θ)_k` by continuity) identifies the limit as the
deterministic `v_k = T(θ)_k`: `N_{n,k}/n → v_k` a.s. -/
lemma proportion_tendsto_of_hitting [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hgs : ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count (fun j ↦ armIndicator A k j ω) (hitting (Q k ω) n)
          - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k) / (n : ℝ) < δ)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) (k : 𝓐) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ))
      atTop (𝓝 (T (fun k ↦ (ν k)[id]) k)) := by
  filter_upwards [consistency_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα Q hthrottle hgs,
    theta_consistent_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα Q hthrottle hgs hTpos]
    with ω hjω hθω
  obtain ⟨u, hu⟩ := hjω
  have hrho : Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop
      (𝓝 (T (fun k ↦ (ν k)[id]) k)) :=
    tendsto_pi_nhds.mp ((hT.tendsto _).comp hθω) k
  have huk : u k = T (fun k ↦ (ν k)[id]) k := tendsto_nhds_unique (hu k).2 hrho
  rw [← huk]
  exact ((hu k).1).congr fun n ↦ by rw [count_indicator_eq_pullCount]

/-- **Consistency of the aRTS allocation proportions** (blueprint `thm:LLN`, consistency direction).
The `aRTS` instantiation of `consistency_of_hitting` at the last under-sampling time
`hitting (aRTSUnder …)`: whenever arm `k` is over-sampled its selection probability is throttled
(`hthrottle`), so the smallness `N_{ℓ} - ℓ ρ̂_{ℓ} ≤ 0` is automatic (`generic_small_of_hitting`).
Almost surely there is a common limit `u` with `N_{n,k}/n → u_k`, `ρ̂_{n,k} → u_k` for every `k`. -/
lemma aRTS_consistency [Fintype 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ aRTSUnder A Y θ₀ T k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n / (n : ℝ)) atTop (𝓝 (u k))
        ∧ Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop (𝓝 (u k)) :=
  consistency_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα (aRTSUnder A Y θ₀ T) hthrottle
    (fun k ↦ Eventually.of_forall fun ω δ hδ ↦ generic_small_of_hitting
      (fun j ↦ armIndicator A k j ω) (fun j ↦ aRTSTarget A Y θ₀ T j ω k)
      (aRTSUnder A Y θ₀ T k ω) (fun _ hm ↦ hm) δ hδ)

end AlphaRAR
