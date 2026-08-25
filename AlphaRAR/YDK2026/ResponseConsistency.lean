/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.Deterministic
public import AlphaRAR.Mathlib.MartingaleSLLN
public import AlphaRAR.YDK2026.Response
public import Mathlib.Algebra.Ring.IsFormallyReal
public meta import LeanSpec

/-!
# Consistency of the sequential estimator on `{N → ∞}`

This file connects the bracket-normalized martingale strong law
(`martingale_div_predQuadVar_ae_tendsto_zero`) to the sequential estimator of the
response model. It formalizes the first branch of the blueprint dichotomy
`lem:theta_limit_dichotomy`: **on the event that arm `k` is sampled infinitely
often, the estimator `θ̂_{n,k}` converges a.s. to the arm mean `θ_k = ν.means k`.**

The argument is:

* `⟨Q_k⟩_n = V_k N_{n,k}` (`predQuadVar_respMart_eq`), so on `{N_{n,k} → ∞}` the
  quadratic variation `⟨Q_k⟩` tends to `∞` (when `V_k > 0`), and the bracket SLLN
  gives `Q_{n,k}/⟨Q_k⟩_n → 0`, hence `Q_{n,k}/N_{n,k} → 0`
  (`respMart_div_pullCount_ae_tendsto_zero`). The degenerate case `V_k = 0` forces
  `Q_{n,k} = 0` a.s. (its second moment `V_k 𝔼[N]` vanishes), so the ratio is `0`.
* The exact estimator error `θ̂_{n,k} - θ_k = (Q_{n,k} + (θ_{0,k}-θ_k))/(N_{n,k}+1)`
  (`estimator_sub_eq`) then tends to `0`, since `Q_{n,k}/(N_{n,k}+1) → 0` and the
  constant offset is `O(N^{-1})` (`estimator_ae_tendsto_of_pullCount_atTop`).

The two bridge lemmas `count_indicator_eq_pullCount` and
`respMG_indicator_eq_respMart` identify the deterministic per-path estimator core
(`AlphaRAR.estimator`, `AlphaRAR.count`, `AlphaRAR.respMG` applied to the assignment
indicator `𝟙{A · = k}` and the response `Y · ω`) with the probabilistic objects
`pullCount` and `respMart`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning

open scoped Topology

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-! ### Bridge lemmas: deterministic estimator core ↔ probabilistic objects -/

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] in
/-- The deterministic response martingale `respMG` of the assignment-indicator sequence
`𝟙{A · = k}` and response `Y · ω`, centered at the arm mean `ν.means k`, equals the
probabilistic response martingale `respMart` evaluated at `ω`. -/
lemma respMG_indicator_eq_respMart (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMG (fun j ↦ actionIndicator A k j ω)
        (Y · ω) (ν.means k) n
      = respMart ν A Y k n ω := by
  simp only [respMG, respMart_apply]

/-! ### The bracket SLLN applied to the response martingale -/

/-- **`Q_{n,k}/N_{n,k} → 0` a.s. on `{N_{n,k} → ∞}`** (branch 1 of `lem:theta_limit_dichotomy`,
probabilistic core). This is the bracket-normalized martingale strong law
(`martingale_div_predQuadVar_ae_tendsto_zero`) transported to the response martingale via
`⟨Q_k⟩_n = V_k N_{n,k}` (`predQuadVar_respMart_eq`).

If `V_k = Var[id; ν k] > 0`, then on `{N_{n,k} → ∞}` the quadratic variation `⟨Q_k⟩ = V_k N`
tends to `∞`, and the bracket SLLN gives `Q_{n,k}/⟨Q_k⟩_n → 0`, whence
`Q_{n,k}/N_{n,k} = V_k · (Q_{n,k}/⟨Q_k⟩_n) → 0`. If `V_k = 0`, then `𝔼[Q_{n,k}²] = V_k 𝔼[N] = 0`,
so `Q_{n,k} = 0` a.s. for every `n`, and the ratio is identically `0`. -/
lemma respMart_div_pullCount_ae_tendsto_zero [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (hνk : ∀ a, MemLp id 2 (ν a)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop →
      Tendsto (fun n ↦ respMart ν A Y k n ω / (pullCount A k n ω : ℝ)) atTop (𝓝 0) := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hV : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  rcases hV.eq_or_lt with hV0 | hVpos
  · -- Degenerate case `V_k = 0`: `Q_{n,k} = 0` a.s. for every `n`.
    have hzero : ∀ n, respMart ν A Y k n =ᵐ[P] 0 := by
      intro n
      have hsq0 : ∫ ω, respMart ν A Y k n ω ^ 2 ∂P = 0 := by
        rw [integral_respMart_sq_eq h k hνk n, ← hV0, zero_mul]
      have hnn : 0 ≤ᵐ[P] fun ω ↦ respMart ν A Y k n ω ^ 2 :=
        Eventually.of_forall fun ω ↦ sq_nonneg _
      have hintsq : Integrable (fun ω ↦ respMart ν A Y k n ω ^ 2) P :=
        (memLp_respMart h hY2 k n).integrable_sq
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hintsq).mp hsq0] with ω hω
      exact sq_eq_zero_iff.mp hω
    filter_upwards [ae_all_iff.mpr hzero] with ω hω _
    simp only [hω, Pi.zero_apply, zero_div]
    exact tendsto_const_nhds
  · -- Nondegenerate case `V_k > 0`: transport the bracket SLLN through `⟨Q_k⟩ = V_k N`.
    have hM := martingale_respMart h hint k
    have hM2 : ∀ n, MemLp (respMart ν A Y k n) 2 P := memLp_respMart h hY2 k
    have hbracket := martingale_div_predQuadVar_ae_tendsto_zero hM hM2
    have hqv := ae_all_iff.mpr (fun n ↦ predQuadVar_respMart_eq h k hνk n)
    filter_upwards [hbracket, hqv] with ω hbω hqvω hN
    have hVne : Var[id; ν k] ≠ 0 := hVpos.ne'
    have hQinf : Tendsto (fun n ↦ predQuadVar (respMart ν A Y k)
        h.filtrationAction P n ω)
        atTop atTop :=
      (Tendsto.const_mul_atTop hVpos hN).congr' (Eventually.of_forall fun n ↦ (hqvω n).symm)
    have hlim := (hbω hQinf).mul_const (Var[id; ν k])
    rw [zero_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    have hpc : (pullCount A k n ω : ℝ) ≠ 0 := hn.ne'
    rw [hqvω n]
    field_simp

/-! ### Consistency of the estimator on `{N → ∞}` -/

/-- **Estimator consistency on `{N_{n,k} → ∞}`** (branch 1 of `lem:theta_limit_dichotomy`).
On the event that arm `k` is sampled infinitely often, the sequential estimator converges
a.s. to the arm mean `θ_k = ν.means k`:
`θ̂_{n,k} = (∑_{j<n} 𝟙{A j = k} Y j + θ₀)/(N_{n,k}+1) → ν.means k` a.s.

From the exact error identity `θ̂_{n,k} - θ_k = (Q_{n,k} + (θ₀-θ_k))/(N_{n,k}+1)`
(`estimator_sub_eq`), both fractions vanish: `Q_{n,k}/(N_{n,k}+1) → 0` because
`Q_{n,k}/N_{n,k} → 0` (`respMart_div_pullCount_ae_tendsto_zero`) and `N_{n,k}/(N_{n,k}+1) → 1`,
while the constant offset `(θ₀-θ_k)/(N_{n,k}+1) → 0` since `N_{n,k} → ∞`. -/
lemma estimator_ae_tendsto_of_pullCount_atTop [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop →
      Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
        (Y · ω) θ₀ n) atTop (𝓝 (ν.means k)) := by
  filter_upwards [respMart_div_pullCount_ae_tendsto_zero h k hνk] with ω hslln hN
  have hslln' := hslln hN
  -- `N_{n,k} + 1 → ∞` and its inverse → 0.
  have hpc1 : Tendsto (fun n ↦ (pullCount A k n ω : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hN
  have hpcinv : Tendsto (fun n ↦ ((pullCount A k n ω : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpc1
  -- Ratio `N/(N+1) → 1`.
  have hratio : Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / ((pullCount A k n ω : ℝ) + 1))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun n ↦ (1 : ℝ) - ((pullCount A k n ω : ℝ) + 1)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hpcinv
    refine h1.congr' (Eventually.of_forall fun n ↦ ?_)
    have hne : (pullCount A k n ω : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  -- Term A: `Q_{n,k}/(N+1) = (Q_{n,k}/N)·(N/(N+1)) → 0`.
  have hA : Tendsto (fun n ↦ respMart ν A Y k n ω / ((pullCount A k n ω : ℝ) + 1))
      atTop (𝓝 0) := by
    have hmul := hslln'.mul hratio
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    have hpc : (pullCount A k n ω : ℝ) ≠ 0 := hn.ne'
    have hpc1' : (pullCount A k n ω : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  -- Term B: constant offset `(θ₀-θ)/(N+1) → 0`.
  have hB : Tendsto (fun n ↦ (θ₀ - ν.means k) / ((pullCount A k n ω : ℝ) + 1)) atTop (𝓝 0) := by
    have hb := hpcinv.const_mul (θ₀ - ν.means k)
    rw [mul_zero] at hb
    simpa [div_eq_mul_inv] using hb
  -- Sum of the two fractions → 0, and it equals `θ̂ - θ`.
  have hAB : Tendsto (fun n ↦ (respMart ν A Y k n ω + (θ₀ - ν.means k))
      / ((pullCount A k n ω : ℝ) + 1)) atTop (𝓝 0) := by
    have hsum := hA.add hB
    rw [add_zero] at hsum
    refine hsum.congr' (Eventually.of_forall fun n ↦ ?_)
    simp only [add_div]
  have hsub : Tendsto (fun n ↦ estimator
      (fun j ↦ actionIndicator A k j ω) (Y · ω) θ₀ n
      - ν.means k) atTop (𝓝 0) := by
    refine hAB.congr' (Eventually.of_forall fun n ↦ ?_)
    have hden_ne : count (fun j ↦ actionIndicator A k j ω) n + 1 ≠ 0 := by
      rw [count_indicator_eq_pullCount]; positivity
    have key : estimator (fun j ↦ actionIndicator A k j ω)
          (Y · ω) θ₀ n - ν.means k
        = (respMart ν A Y k n ω + (θ₀ - ν.means k)) / ((pullCount A k n ω : ℝ) + 1) := by
      rw [estimator_sub_eq _ _ (ν.means k) θ₀ n hden_ne]
      simp only [respMG_indicator_eq_respMart, count_indicator_eq_pullCount]
    exact key.symm
  have hconst : Tendsto (fun _ : ℕ ↦ ν.means k) atTop (𝓝 (ν.means k)) := tendsto_const_nhds
  have hfinal := hconst.add hsub
  rw [add_zero] at hfinal
  exact hfinal.congr fun n ↦ by ring

/-! ### Estimator convergence on `{sup N < ∞}` and the full dichotomy -/

omit [MeasurableSingletonClass 𝓐] in
/-- **Estimator eventually constant on `{\sup_n N_{n,k} < \infty\}`** (branch 2 of
`lem:theta_limit_dichotomy`). For a fixed path `ω`, if the count `N_{n,k}(ω)` does not tend to
`∞`, then the sequential estimator is eventually constant, hence converges.

Since `N_{\cdot,k}` is a nondecreasing `ℕ`-valued sequence, `N_{n,k}\not\to\infty` forces it to
be bounded, and thus eventually constant at its supremum `N_{N_0,k}`. For `n \ge N_0` no further
patient is assigned to arm `k`, so both the numerator `\sum_{j<n} 𝟙\{A_j=k\}Y_j` and the
denominator `N_{n,k}+1` are constant, and the estimator freezes. -/
lemma exists_tendsto_estimator_of_not_pullCount_atTop (k : 𝓐) (θ₀ : ℝ) (ω : Ω)
    (hnot : ¬ Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop) :
    ∃ L, Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
      (Y · ω) θ₀ n) atTop (𝓝 L) := by
  -- The count (as a `ℕ`-valued sequence) does not tend to `∞` either, hence is bounded.
  have hnatnot : ¬ Tendsto (fun n ↦ pullCount A k n ω) atTop atTop :=
    fun hnat ↦ hnot (tendsto_natCast_atTop_atTop.comp hnat)
  have hbdd : BddAbove (Set.range fun n ↦ pullCount A k n ω) := by
    by_contra hb
    exact hnatnot (tendsto_atTop_atTop_of_monotone' (monotone_pullCount k ω) hb)
  -- The supremum is attained at some `N₀`, and the count is constant from `N₀` on.
  obtain ⟨N₀, hN₀⟩ := Set.mem_range.mp (Nat.sSup_mem (Set.range_nonempty _) hbdd)
  have hle : ∀ n, pullCount A k n ω ≤ pullCount A k N₀ ω := fun n ↦ by
    rw [hN₀]; exact le_csSup hbdd (Set.mem_range_self n)
  have hconst : ∀ n, N₀ ≤ n → pullCount A k n ω = pullCount A k N₀ ω := fun n hn ↦
    le_antisymm (hle n) (monotone_pullCount k ω hn)
  -- For `n ≥ N₀` the estimator equals its value at `N₀`.
  refine ⟨estimator (fun j ↦ actionIndicator A k j ω)
    (Y · ω) θ₀ N₀, tendsto_atTop_of_eventually_const (i₀ := N₀) fun n hn ↦ ?_⟩
  have hden : count (fun j ↦ actionIndicator A k j ω) n
      = count (fun j ↦ actionIndicator A k j ω) N₀ := by
    rw [count_indicator_eq_pullCount, count_indicator_eq_pullCount, hconst n hn]
  have hnum : ∑ j ∈ Finset.range n, actionIndicator A k j ω * Y j ω
      = ∑ j ∈ Finset.range N₀, actionIndicator A k j ω * Y j ω := by
    symm
    have hsub : Finset.range N₀ ⊆ Finset.range n := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    refine Finset.sum_subset hsub fun j _ hjN ↦ ?_
    rw [Finset.mem_range, not_lt] at hjN
    -- The count is unchanged at step `j ≥ N₀`, so patient `j` is not assigned to arm `k`.
    have hj1 : pullCount A k (j + 1) ω = pullCount A k j ω := by
      rw [hconst (j + 1) (by omega), hconst j hjN]
    have hAjk : A j ω ≠ k := by
      intro hEq
      rw [pullCount_add_one, hEq, ite_eq_left rfl] at hj1
      omega
    rw [actionIndicator, Set.indicator_of_notMem (by simpa using hAjk), zero_mul]
  simp only [estimator, hden, hnum]

omit [DecidableEq 𝓐] in
/-- **The sequential estimator converges a.s.** (the convergence content of
`lem:theta_limit_dichotomy`). For each arm `k`, `\hat\theta_{n,k}` converges almost surely: to
the arm mean `θ_k = ν.means k` on `\{N_{n,k}\to\infty\}` (Lemma
`estimator_ae_tendsto_of_pullCount_atTop`), and to an eventually-attained value on
`\{\sup_n N_{n,k}<\infty\}` (Lemma `exists_tendsto_estimator_of_not_pullCount_atTop`). The
dichotomy is exhaustive because `N_{n,k}` is monotone in `n`. -/
lemma estimator_ae_tendsto [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : ℝ) :
    ∀ᵐ ω ∂P, ∃ L, Tendsto (fun n ↦ estimator
      (fun j ↦ actionIndicator A k j ω) (Y · ω) θ₀ n)
      atTop (𝓝 L) := by
  classical
  filter_upwards [estimator_ae_tendsto_of_pullCount_atTop h k hνk θ₀] with ω hω
  by_cases hlim : Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop
  · exact ⟨ν.means k, hω hlim⟩
  · exact exists_tendsto_estimator_of_not_pullCount_atTop k θ₀ ω hlim

omit [DecidableEq 𝓐] in
/-- **The estimator vector converges a.s.** (vector form of `lem:theta_converges`, feeding
`lem:rho_converges`). With finitely (or countably) many arms, the per-arm a.s. limits combine
into a single a.s. limit vector `z : 𝓐 → ℝ`: almost surely there is `z` with
`\hat\theta_{n,k}\to z_k` for every arm `k` simultaneously. This is the a.s. convergence
`\hat\Params_n \to z` that Condition **B** then transports through the (continuous) target map. -/
lemma estimator_ae_tendsto_pi [Finite 𝓐] [Countable 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) :
    ∀ᵐ ω ∂P, ∃ z : 𝓐 → ℝ, ∀ k, Tendsto (fun n ↦ estimator
      (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n)
      atTop (𝓝 (z k)) := by
  filter_upwards [ae_all_iff.mpr fun k ↦ estimator_ae_tendsto h k hνk (θ₀ k)] with ω hω
  choose z hz using hω
  exact ⟨z, hz⟩

/-! ### Identifying the limit as the true parameter (Condition B non-sparsity) -/

/-- **Estimator consistency to the true mean** (blueprint `lem:theta_consistent`, per-arm core).
If the allocation proportion converges to a *positive* limit, `N_{n,k}/n → u_k > 0` a.s. (the
positivity `u_k > 0` is the non-sparsity of Condition **B**, blueprint `lem:rho_converges`), then
arm `k` is sampled infinitely often (`all_arms_infinite`), so the dichotomy's first branch
(`estimator_ae_tendsto_of_pullCount_atTop`) identifies the estimator limit as the true arm mean:
`θ̂_{n,k} → θ_k = ν.means k` a.s. -/
lemma theta_consistent [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) {u : Ω → 𝓐 → ℝ}
    (hmatch : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (u ω k)))
    (hpos : ∀ k, ∀ᵐ ω ∂P, 0 < u ω k) (k : 𝓐) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
      (Y · ω) (θ₀ k) n) atTop (𝓝 (ν.means k)) := by
  filter_upwards [hmatch k, hpos k,
    estimator_ae_tendsto_of_pullCount_atTop h k hνk (θ₀ k)] with ω hmω hpω hestω
  refine hestω ?_
  have hcount := all_arms_infinite (fun i k' ↦ actionIndicator A k' i ω) k hpω
    (hmω.congr fun n ↦ by rw [count_indicator_eq_pullCount])
  exact hcount.congr fun n ↦ count_indicator_eq_pullCount k n ω

/-- **Estimator vector consistency** (blueprint `lem:theta_consistent`, vector form). Under a
positive allocation-proportion limit for every arm, the estimator vector converges a.s. to the true
parameter: `θ̂_n → θ = (ν.means k)_k`. Bundles `theta_consistent` over the finitely many arms via
`ae_all_iff` and `tendsto_pi_nhds`. This is the a.s. consistency the delta-method rate `rho_rate`
consumes. -/
lemma theta_consistent_pi [Finite 𝓐] [Countable 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) {u : Ω → 𝓐 → ℝ}
    (hmatch : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (u ω k)))
    (hpos : ∀ k, ∀ᵐ ω ∂P, 0 < u ω k) :
    ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) atTop (𝓝 ν.means) := by
  filter_upwards [ae_all_iff.mpr fun k ↦ theta_consistent h hνk θ₀ hmatch hpos k] with ω hω
  exact tendsto_pi_nhds.mpr hω

/-- **Attainable set of the estimator** (blueprint `def:attainable`, closure form). The closure of
all values `θ̂_{n,k}(ω)` of the sequential estimator for arm `k`, over times `n` and outcomes `ω`.
Every pointwise limit of `θ̂_{·,k}` lies in it (`estimator_limit_mem_attainableSet`), so Condition
**B**'s positivity requirement on this set transfers to the plug-in-target limit `u_k = T(z)_k`. -/
def attainableSet (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : ℝ) (k : 𝓐) : Set ℝ :=
  closure (Set.range fun p : ℕ × Ω ↦
    estimator (fun j ↦ actionIndicator A k j p.2) (Y · p.2) θ₀ p.1)

omit [DecidableEq 𝓐] in
/-- Any pointwise limit of the sequential estimator lies in the attainable set: it is a limit of
estimator values, hence in the closure of their range. -/
@[specifies attainableSet "the only property Condition **B** needs, and the reason the definition \
takes a *closure* of the range rather than the range itself: limits of estimator values must \
belong to it, and they need not be attained at any finite time"]
lemma estimator_limit_mem_attainableSet (k : 𝓐) (θ₀ : ℝ) {ω : Ω} {L : ℝ}
    (hL : Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
      (Y · ω) θ₀ n) atTop (𝓝 L)) :
    L ∈ attainableSet A Y θ₀ k :=
  mem_closure_of_tendsto hL (Eventually.of_forall fun n ↦ ⟨(n, ω), rfl⟩)

omit [DecidableEq 𝓐] in
/-- **Non-sparse convergence of the plug-in target** (blueprint `lem:rho_converges`). Under
Condition **B**'s non-sparsity — the target `T` maps the product of attainable sets into the
positive orthant (`hTpos`) — the plug-in target `ρ̂_{n,k} = T(θ̂_n)_k` converges a.s. to a
*positive* limit: almost surely there is `u` with `u_k > 0` and `ρ̂_{n,k} → u_k` for every arm. The
limit is
`u = T(z)` with `z` the a.s. estimator-vector limit (`estimator_ae_tendsto_pi`), whose coordinates
lie in the attainable sets (`estimator_limit_mem_attainableSet`); `hTpos` makes `u` positive and
continuity of `T` transports the convergence. This is the non-sparse refinement supplying the
positivity `u_k > 0` identifying the estimator limit as the true parameter (`theta_consistent`). -/
lemma rho_converges_pos [Finite 𝓐] [Countable 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, (∀ k, 0 < u k) ∧ ∀ k, Tendsto (fun n ↦ T (fun k' ↦ estimator
      (fun j ↦ actionIndicator A k' j ω) (Y · ω) (θ₀ k') n) k) atTop (𝓝 (u k)) := by
  filter_upwards [estimator_ae_tendsto_pi h hνk θ₀] with ω hω
  obtain ⟨z, hz⟩ := hω
  refine ⟨T z, hTpos z (fun k ↦ estimator_limit_mem_attainableSet k (θ₀ k) (hz k)), fun k ↦ ?_⟩
  have hvec : Tendsto (fun n ↦ (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n)) atTop (𝓝 z) := tendsto_pi_nhds.mpr hz
  exact tendsto_pi_nhds.mp ((hT.tendsto z).comp hvec) k

/-- **The allocation-proportion limit is positive** (the non-sparsity discharge). Given the *joint*
consistency `hjoint` — for a.e. `ω` a common limit `u` with `N_{n,k}/n → u_k` *and*
`ρ̂_{n,k} = T(θ̂_n)_k → u_k` (supplied by the design's consistency theorem, e.g.
`aRTS_consistency`) — together with Condition **B** (`T` continuous, positive on the attainable
sets), the shared limit `u` is positive: `u_k = T(z)_k > 0` where `z` is the estimator-vector limit.
This turns the joint consistency into the *positive* proportion limit that identifies the estimator
limit as the true parameter. -/
lemma proportion_pos_of_condB [Finite 𝓐] [Countable 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hjoint : ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (u k)) ∧
      Tendsto (fun n ↦ T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
        (Y · ω) (θ₀ k') n) k) atTop (𝓝 (u k))) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, (∀ k, 0 < u k) ∧
      ∀ k, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (u k)) := by
  filter_upwards [hjoint, estimator_ae_tendsto_pi h hνk θ₀] with ω hjω hzω
  obtain ⟨u, hu⟩ := hjω
  obtain ⟨z, hz⟩ := hzω
  have hrho : ∀ k, Tendsto (fun n ↦ T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) k) atTop (𝓝 (T z k)) := by
    intro k
    have hvec : Tendsto (fun n ↦ (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
        (Y · ω) (θ₀ k') n)) atTop (𝓝 z) := tendsto_pi_nhds.mpr hz
    exact tendsto_pi_nhds.mp ((hT.tendsto z).comp hvec) k
  have huz : ∀ k, u k = T z k := fun k ↦ tendsto_nhds_unique (hu k).2 (hrho k)
  refine ⟨u, fun k ↦ ?_, fun k ↦ (hu k).1⟩
  rw [huz k]
  exact hTpos z (fun k' ↦ estimator_limit_mem_attainableSet k' (θ₀ k') (hz k')) k

/-- **Estimator consistency from a positive proportion limit** (`lem:theta_consistent`, per-arm,
existential form). Same as `theta_consistent` but taking the positive proportion limit as a per-`ω`
existential `∃ u_k > 0, N_{n,k}/n → u_k`, which is the shape `proportion_pos_of_condB` produces —
avoiding a global choice of the (random) limit. -/
lemma theta_consistent_of_pos [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : ℝ) (k : 𝓐)
    (hpp : ∀ᵐ ω ∂P, ∃ uk : ℝ, 0 < uk ∧
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 uk)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
      (Y · ω) θ₀ n) atTop (𝓝 (ν.means k)) := by
  filter_upwards [hpp, estimator_ae_tendsto_of_pullCount_atTop h k hνk θ₀] with ω hppω hestω
  obtain ⟨uk, hukpos, hlim⟩ := hppω
  refine hestω ?_
  have hcount := all_arms_infinite (fun i k' ↦ actionIndicator A k' i ω) k hukpos
    (hlim.congr fun n ↦ by rw [count_indicator_eq_pullCount])
  exact hcount.congr fun n ↦ count_indicator_eq_pullCount k n ω

/-- **Estimator vector consistency under Condition B** (`lem:theta_consistent`, vector form,
discharged). From the joint consistency `hjoint` and Condition **B**, the estimator vector converges
a.s. to the true parameter `θ̂_n → θ = (ν.means k)_k`: `proportion_pos_of_condB` makes the shared
proportion limit positive, then `theta_consistent_of_pos` identifies each arm's limit as its
mean. -/
lemma theta_consistent_pi_of_condB [Finite 𝓐] [Countable 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hjoint : ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (u k)) ∧
      Tendsto (fun n ↦ T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
        (Y · ω) (θ₀ k') n) k) atTop (𝓝 (u k))) :
    ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) atTop (𝓝 ν.means) := by
  have hprop := proportion_pos_of_condB h hνk θ₀ T hT hTpos hjoint
  have hper : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
      (Y · ω) (θ₀ k) n) atTop (𝓝 (ν.means k)) := by
    intro k
    refine theta_consistent_of_pos h hνk (θ₀ k) k ?_
    filter_upwards [hprop] with ω hpω
    obtain ⟨u, hupos, hulim⟩ := hpω
    exact ⟨u k, hupos k, hulim k⟩
  filter_upwards [ae_all_iff.mpr hper] with ω hω
  exact tendsto_pi_nhds.mpr hω

omit [DecidableEq 𝓐] in
/-- **Convergence of the plug-in target** (blueprint `lem:rho_converges`, continuity form).
For any continuous target map `T : (𝓐 → ℝ) → (𝓐 → ℝ)`, the plug-in target
`\hat\rho_n = T(\hat\Params_n)` converges a.s.: almost surely there is `u : 𝓐 → ℝ` with
`\hat\rho_{n,k} \to u_k` for every arm `k`. Here `u = T z`, where `z` is the a.s. limit of the
estimator vector (`estimator_ae_tendsto_pi`); continuity of `T` transports the convergence
`\hat\Params_n \to z` (in the product topology) to `T(\hat\Params_n) \to T z`. The blueprint's
non-sparse refinement `u \in (0,1)^K` needs the rest of Condition **B** and is deferred. -/
lemma rho_converges [Finite 𝓐] [Countable 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k, Tendsto (fun n ↦ T (fun k' ↦ estimator
      (fun j ↦ actionIndicator A k' j ω) (Y · ω) (θ₀ k') n) k)
      atTop (𝓝 (u k)) := by
  filter_upwards [estimator_ae_tendsto_pi h hνk θ₀] with ω hω
  obtain ⟨z, hz⟩ := hω
  refine ⟨T z, fun k ↦ ?_⟩
  have hvec : Tendsto (fun n ↦ (fun k' ↦ estimator
      (fun j ↦ actionIndicator A k' j ω)
        (Y · ω) (θ₀ k') n)) atTop (𝓝 z) := tendsto_pi_nhds.mpr hz
  exact tendsto_pi_nhds.mp ((hT.tendsto z).comp hvec) k

omit [MeasurableSingletonClass 𝓐] [IsProbabilityMeasure P] in
/-- **LIL rate for the estimator, a.s.** (blueprint `lem:theta_LIL`, a.s. form). Given the
proportion limit `N_{n,k}/n → v_k > 0` a.s. (from `match_proportion_ae` via the count-indexing
bridge) and the two-sided LIL bound `|Q_{n,k}| ≤ C√(n log n)` eventually a.s. (from
`ae_eventually_abs_respMart_le_sqrt_nat_mul_log`), the estimator error is `O(√(log n / n))` a.s.:
`|θ̂_{n,k} - θ_k| ≤ C'·√(n log n)/n` for large `n`. Each is the pathwise `abs_estimator_sub_le_rate`
after the bridges `count(𝟙{A·=k}) = N_{n,k}` and `respMG(𝟙{A·=k}) = Q_{n,k}`; the (random) LIL
constant is made nonnegative via `max C 0`. -/
lemma abs_estimator_sub_le_rate_ae (k : 𝓐) (θ₀ : ℝ) {v : Ω → ℝ}
    (hv : ∀ᵐ ω ∂P, 0 < v ω)
    (hN : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v ω)))
    (hQ : ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      |respMart ν A Y k n ω| ≤ C * √((n : ℝ) * Real.log n)) :
    ∀ᵐ ω ∂P, ∃ C', ∀ᶠ n in atTop,
      |estimator (fun j ↦ actionIndicator A k j ω)
          (Y · ω) θ₀ n - ν.means k|
        ≤ C' * (√((n : ℝ) * Real.log n) / (n : ℝ)) := by
  filter_upwards [hv, hN, hQ] with ω hvω hNω hQω
  obtain ⟨C, hCbound⟩ := hQω
  have hN' : Tendsto (fun n ↦ count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ))
      atTop (𝓝 (v ω)) :=
    hNω.congr fun n ↦ by rw [count_indicator_eq_pullCount]
  have hQ' : ∀ᶠ n in atTop, |respMG (fun j ↦ actionIndicator A k j ω)
      (Y · ω) (ν.means k) n|
      ≤ max C 0 * √((n : ℝ) * Real.log n) := by
    filter_upwards [hCbound] with n hn
    rw [respMG_indicator_eq_respMart]
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _))
  exact abs_estimator_sub_le_rate (fun j ↦ actionIndicator A k j ω)
    (Y · ω) (ν.means k) θ₀ hvω hN' (le_max_right C 0) hQ'

/-! ### The loglog rate for the estimator -/

omit [MeasurableSingletonClass 𝓐] [IsProbabilityMeasure P] in
/-- **The response martingale is `O(√(n log log n))`** (the `n`-indexed form of the loglog LIL
`cor:subsampled_lil`). The sharp subsampled LIL `abs_respMart_le_sqrt_nat_mul_loglog` bounds
`|Q_{n,k}|` by `β√(2 V_k N_{n,k} log log N_{n,k})` in terms of the *pull count* `N_{n,k}`; combined
with the proportion limit `N_{n,k}/n → v_k > 0` — which gives `N_{n,k} ≤ 2 v_k n` and
`log log N_{n,k} ≤ 2 log log n` eventually — it becomes a bound in the *time index* `n`:
`|Q_{n,k}| ≤ C√(n log log n)` eventually, a.s. This is the loglog analogue of
`ae_eventually_abs_respMart_le_sqrt_nat_mul_log`, and the `hQ` input of
`abs_estimator_sub_le_rate_loglog_ae`. -/
lemma ae_eventually_abs_respMart_le_sqrt_nat_mul_loglog (k : 𝓐) {v : Ω → ℝ}
    (hv : ∀ᵐ ω ∂P, 0 < v ω)
    (hN : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v ω)))
    (hQ : ∀ᵐ ω ∂P, ∀ β : ℝ, 1 < β → ∀ᶠ n in atTop,
      |respMart ν A Y k n ω| ≤ β * √(2 * Var[id; ν k] * (pullCount A k n ω : ℝ)
        * Real.log (Real.log (pullCount A k n ω : ℝ)))) :
    ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      |respMart ν A Y k n ω| ≤ C * √((n : ℝ) * Real.log (Real.log (n : ℝ))) := by
  have hV : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  filter_upwards [hv, hN, hQ] with ω hvω hNω hQω
  have h2 := hQω 2 one_lt_two
  -- `N_{n,k} ≤ 2 v n` eventually.
  have hNle : ∀ᶠ n in atTop, (pullCount A k n ω : ℝ) ≤ 2 * v ω * (n : ℝ) := by
    have hlt := (tendsto_order.1 hNω).2 (2 * v ω) (by linarith)
    filter_upwards [hlt, eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    exact le_of_lt ((div_lt_iff₀ hnpos).1 hn)
  -- `N_{n,k} → ∞`.
  have hNinf : Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop := by
    have hlt := (tendsto_order.1 hNω).1 (v ω / 2) (by linarith)
    have hge : ∀ᶠ (n : ℕ) in atTop, v ω / 2 * (n : ℝ) ≤ (pullCount A k n ω : ℝ) := by
      filter_upwards [hlt, eventually_gt_atTop 0] with n hn hn0
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
      exact le_of_lt ((lt_div_iff₀ hnpos).1 hn)
    exact tendsto_atTop_mono' atTop hge
      (Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < v ω / 2) tendsto_natCast_atTop_atTop)
  -- `log log N_{n,k} ≤ 2 log log n` eventually.
  have hloglog : ∀ᶠ n in atTop, Real.log (Real.log (pullCount A k n ω : ℝ))
      ≤ 2 * Real.log (Real.log (n : ℝ)) := by
    have hlogtop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hloglogtop : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp hlogtop
    filter_upwards [hNle, hNinf.eventually_ge_atTop 3,
      hlogtop.eventually_ge_atTop (Real.log (2 * v ω)),
      hloglogtop.eventually_ge_atTop (Real.log 2), eventually_ge_atTop 3]
      with n hle h3 hl2v hll2 hn3
    have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hnpos : (0 : ℝ) < n := by linarith
    have hn1 : (1 : ℝ) < n := by linarith
    have hNpos : (0 : ℝ) < (pullCount A k n ω : ℝ) := by linarith
    have hN1 : (1 : ℝ) < (pullCount A k n ω : ℝ) := by linarith
    have e1 : Real.log (pullCount A k n ω : ℝ) ≤ Real.log (2 * v ω * (n : ℝ)) :=
      Real.log_le_log hNpos hle
    have e2 : Real.log (2 * v ω * (n : ℝ)) = Real.log (2 * v ω) + Real.log (n : ℝ) :=
      Real.log_mul (mul_ne_zero two_ne_zero (ne_of_gt hvω)) (ne_of_gt hnpos)
    have e3 : Real.log (pullCount A k n ω : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      rw [e2] at e1; linarith
    have hlogNpos : (0 : ℝ) < Real.log (pullCount A k n ω : ℝ) := Real.log_pos hN1
    have hlognpos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos hn1
    have e4 : Real.log (Real.log (pullCount A k n ω : ℝ)) ≤ Real.log (2 * Real.log (n : ℝ)) :=
      Real.log_le_log hlogNpos e3
    have e5 : Real.log (2 * Real.log (n : ℝ)) = Real.log 2 + Real.log (Real.log (n : ℝ)) :=
      Real.log_mul two_ne_zero (ne_of_gt hlognpos)
    rw [e5] at e4; linarith
  -- Combine: convert the `N`-scale bound into an `n`-scale bound.
  refine ⟨2 * √(8 * Var[id; ν k] * v ω), ?_⟩
  filter_upwards [h2, hNle, hloglog, hNinf.eventually_ge_atTop 3, eventually_ge_atTop 3]
    with n hb hle hll h3 hn3
  have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  set Nn : ℝ := (pullCount A k n ω : ℝ) with hNndef
  have hNpos : (0 : ℝ) < Nn := by linarith
  have hlogN1 : (1 : ℝ) ≤ Real.log Nn :=
    (Real.le_log_iff_exp_le hNpos).mpr (le_trans Real.exp_one_lt_d9.le (by linarith))
  have hllN_nonneg : (0 : ℝ) ≤ Real.log (Real.log Nn) := Real.log_nonneg hlogN1
  have hprod : Nn * Real.log (Real.log Nn)
      ≤ (2 * v ω * (n : ℝ)) * (2 * Real.log (Real.log (n : ℝ))) :=
    mul_le_mul hle hll hllN_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hvω.le) hnpos.le)
  have hkey : 2 * Var[id; ν k] * Nn * Real.log (Real.log Nn)
      ≤ 8 * Var[id; ν k] * v ω * ((n : ℝ) * Real.log (Real.log (n : ℝ))) := by
    have h2V : (0 : ℝ) ≤ 2 * Var[id; ν k] := mul_nonneg (by norm_num) hV
    calc 2 * Var[id; ν k] * Nn * Real.log (Real.log Nn)
        = 2 * Var[id; ν k] * (Nn * Real.log (Real.log Nn)) := by ring
      _ ≤ 2 * Var[id; ν k] * ((2 * v ω * (n : ℝ)) * (2 * Real.log (Real.log (n : ℝ)))) :=
          mul_le_mul_of_nonneg_left hprod h2V
      _ = 8 * Var[id; ν k] * v ω * ((n : ℝ) * Real.log (Real.log (n : ℝ))) := by ring
  have hsplit : √(8 * Var[id; ν k] * v ω * ((n : ℝ) * Real.log (Real.log (n : ℝ))))
      = √(8 * Var[id; ν k] * v ω) * √((n : ℝ) * Real.log (Real.log (n : ℝ))) :=
    Real.sqrt_mul (mul_nonneg (mul_nonneg (by norm_num) hV) hvω.le) _
  calc |respMart ν A Y k n ω|
      ≤ 2 * √(2 * Var[id; ν k] * Nn * Real.log (Real.log Nn)) := hb
    _ ≤ 2 * √(8 * Var[id; ν k] * v ω * ((n : ℝ) * Real.log (Real.log (n : ℝ)))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkey) (by norm_num)
    _ = 2 * √(8 * Var[id; ν k] * v ω)
          * √((n : ℝ) * Real.log (Real.log (n : ℝ))) := by
        rw [hsplit]; ring

omit [MeasurableSingletonClass 𝓐] [IsProbabilityMeasure P] in
/-- **Loglog LIL rate for the estimator, a.s.** (blueprint `lem:theta_LIL`, loglog form). Given the
proportion limit `N_{n,k}/n → v_k > 0` a.s. (from `match_proportion_ae`) and the loglog LIL bound
`|Q_{n,k}| ≤ C√(n log log n)` eventually a.s. (from
`ae_eventually_abs_respMart_le_sqrt_nat_mul_loglog`, itself the subsampled LIL
`abs_respMart_le_sqrt_nat_mul_loglog`), the estimator error is
`O(√(log log n / n))` a.s.: `|θ̂_{n,k} - θ_k| ≤ C'·√(n log log n)/n` for large `n`. This is the
`log log`, sharp-constant upgrade of `abs_estimator_sub_le_rate_ae`, obtained through the same
deterministic core `abs_estimator_sub_le_rate_gen` with the rate `r n = √(n log log n)`. -/
lemma abs_estimator_sub_le_rate_loglog_ae (k : 𝓐) (θ₀ : ℝ) {v : Ω → ℝ}
    (hv : ∀ᵐ ω ∂P, 0 < v ω)
    (hN : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v ω)))
    (hQ : ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      |respMart ν A Y k n ω| ≤ C * √((n : ℝ) * Real.log (Real.log (n : ℝ)))) :
    ∀ᵐ ω ∂P, ∃ C', ∀ᶠ n in atTop,
      |estimator (fun j ↦ actionIndicator A k j ω)
          (Y · ω) θ₀ n - ν.means k|
        ≤ C' * (√((n : ℝ) * Real.log (Real.log (n : ℝ))) / (n : ℝ)) := by
  have hr : ∀ᶠ (n : ℕ) in atTop, (1 : ℝ) ≤ √((n : ℝ) * Real.log (Real.log (n : ℝ))) := by
    have hloglogtop : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    filter_upwards [hloglogtop.eventually_ge_atTop 1, eventually_ge_atTop 1] with n hll hn1
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    exact Real.one_le_sqrt.mpr (by nlinarith)
  filter_upwards [hv, hN, hQ] with ω hvω hNω hQω
  obtain ⟨C, hCbound⟩ := hQω
  have hN' : Tendsto (fun n ↦ count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ))
      atTop (𝓝 (v ω)) :=
    hNω.congr fun n ↦ by rw [count_indicator_eq_pullCount]
  have hQ' : ∀ᶠ n in atTop, |respMG (fun j ↦ actionIndicator A k j ω)
      (Y · ω) (ν.means k) n|
      ≤ max C 0 * √((n : ℝ) * Real.log (Real.log (n : ℝ))) := by
    filter_upwards [hCbound] with n hn
    rw [respMG_indicator_eq_respMart]
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _))
  exact abs_estimator_sub_le_rate_gen (fun j ↦ actionIndicator A k j ω)
    (Y · ω) (ν.means k) θ₀ hvω hN' (le_max_right C 0) hr hQ'

end AlphaRAR
