/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Probability.Response
import AlphaRAR.Probability.MartingaleSLLN
import AlphaRAR.Auxiliary.Deterministic

/-!
# Consistency of the sequential estimator on `{N → ∞}`

This file connects the bracket-normalized martingale strong law
(`martingale_div_predQuadVar_ae_tendsto_zero`) to the sequential estimator of the
response model. It formalizes the first branch of the blueprint dichotomy
`lem:theta_limit_dichotomy`: **on the event that arm `k` is sampled infinitely
often, the estimator `θ̂_{n,k}` converges a.s. to the arm mean `θ_k = (ν k)[id]`.**

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

open MeasureTheory ProbabilityTheory Filter Learning

open scoped Topology

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-! ### Bridge lemmas: deterministic estimator core ↔ probabilistic objects -/

/-- The deterministic count of the assignment-indicator sequence `𝟙{A · = k}` at a fixed
path `ω` equals the (real cast of the) pull count `N_{n,k}` of arm `k`. -/
lemma count_indicator_eq_pullCount (k : 𝓐) (n : ℕ) (ω : Ω) :
    count (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω) n
      = (pullCount A k n ω : ℝ) := by
  rw [count, pullCount_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] in
/-- The deterministic response martingale `respMG` of the assignment-indicator sequence
`𝟙{A · = k}` and response `Y · ω`, centered at the arm mean `(ν k)[id]`, equals the
probabilistic response martingale `respMart` evaluated at `ω`. -/
lemma respMG_indicator_eq_respMart (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMG (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω)
        (fun j ↦ Y j ω) ((ν k)[id]) n
      = respMart ν A Y k n ω := by
  simp only [respMG, respMart, Finset.sum_apply]

/-! ### The bracket SLLN applied to the response martingale -/

/-- **`Q_{n,k}/N_{n,k} → 0` a.s. on `{N_{n,k} → ∞}`** (branch 1 of `lem:theta_limit_dichotomy`,
probabilistic core). This is the bracket-normalized martingale strong law
(`martingale_div_predQuadVar_ae_tendsto_zero`) transported to the response martingale via
`⟨Q_k⟩_n = V_k N_{n,k}` (`predQuadVar_respMart_eq`).

If `V_k = armVar ν k > 0`, then on `{N_{n,k} → ∞}` the quadratic variation `⟨Q_k⟩ = V_k N`
tends to `∞`, and the bracket SLLN gives `Q_{n,k}/⟨Q_k⟩_n → 0`, whence
`Q_{n,k}/N_{n,k} = V_k · (Q_{n,k}/⟨Q_k⟩_n) → 0`. If `V_k = 0`, then `𝔼[Q_{n,k}²] = V_k 𝔼[N] = 0`,
so `Q_{n,k} = 0` a.s. for every `n`, and the ratio is identically `0`. -/
theorem respMart_div_pullCount_ae_tendsto_zero
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (hY2 : ∀ n, MemLp (Y n) 2 P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop →
      Tendsto (fun n ↦ respMart ν A Y k n ω / (pullCount A k n ω : ℝ)) atTop (𝓝 0) := by
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hV : (0 : ℝ) ≤ armVar ν k := by rw [armVar]; exact variance_nonneg _ _
  rcases hV.eq_or_lt with hV0 | hVpos
  · -- Degenerate case `V_k = 0`: `Q_{n,k} = 0` a.s. for every `n`.
    have hzero : ∀ n, respMart ν A Y k n =ᵐ[P] 0 := by
      intro n
      have hsq0 : ∫ ω, respMart ν A Y k n ω ^ 2 ∂P = 0 := by
        rw [integral_respMart_sq_eq h k hY2 n, ← hV0, zero_mul]
      have hnn : 0 ≤ᵐ[P] fun ω ↦ respMart ν A Y k n ω ^ 2 :=
        Eventually.of_forall fun ω ↦ sq_nonneg _
      have hintsq : Integrable (fun ω ↦ respMart ν A Y k n ω ^ 2) P :=
        (memLp_respMart h.measurable_action hY2 k n).integrable_sq
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hintsq).mp hsq0] with ω hω
      exact sq_eq_zero_iff.mp hω
    filter_upwards [ae_all_iff.mpr hzero] with ω hω _
    simp only [hω, Pi.zero_apply, zero_div]
    exact tendsto_const_nhds
  · -- Nondegenerate case `V_k > 0`: transport the bracket SLLN through `⟨Q_k⟩ = V_k N`.
    have hM := martingale_respMart h hint k
    have hM0 : respMart ν A Y k 0 =ᵐ[P] 0 := by filter_upwards with ω; simp [respMart]
    have hM2 : ∀ n, MemLp (respMart ν A Y k n) 2 P := memLp_respMart h.measurable_action hY2 k
    have hbracket := martingale_div_predQuadVar_ae_tendsto_zero hM hM0 hM2
    have hqv := ae_all_iff.mpr (fun n ↦ predQuadVar_respMart_eq h k hY2 n)
    filter_upwards [hbracket, hqv] with ω hbω hqvω hN
    have hVne : armVar ν k ≠ 0 := hVpos.ne'
    have hQinf : Tendsto (fun n ↦ predQuadVar (respMart ν A Y k)
        (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P n ω)
        atTop atTop :=
      (Tendsto.const_mul_atTop hVpos hN).congr' (Eventually.of_forall fun n ↦ (hqvω n).symm)
    have hlim := (hbω hQinf).mul_const (armVar ν k)
    rw [zero_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    have hpc : (pullCount A k n ω : ℝ) ≠ 0 := hn.ne'
    rw [hqvω n]
    field_simp

/-! ### Consistency of the estimator on `{N → ∞}` -/

/-- **Estimator consistency on `{N_{n,k} → ∞}`** (branch 1 of `lem:theta_limit_dichotomy`).
On the event that arm `k` is sampled infinitely often, the sequential estimator converges
a.s. to the arm mean `θ_k = (ν k)[id]`:
`θ̂_{n,k} = (∑_{j<n} 𝟙{A j = k} Y j + θ₀)/(N_{n,k}+1) → (ν k)[id]` a.s.

From the exact error identity `θ̂_{n,k} - θ_k = (Q_{n,k} + (θ₀-θ_k))/(N_{n,k}+1)`
(`estimator_sub_eq`), both fractions vanish: `Q_{n,k}/(N_{n,k}+1) → 0` because
`Q_{n,k}/N_{n,k} → 0` (`respMart_div_pullCount_ae_tendsto_zero`) and `N_{n,k}/(N_{n,k}+1) → 1`,
while the constant offset `(θ₀-θ_k)/(N_{n,k}+1) → 0` since `N_{n,k} → ∞`. -/
theorem estimator_ae_tendsto_of_pullCount_atTop
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop →
      Tendsto (fun n ↦ estimator (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω)
        (fun j ↦ Y j ω) θ₀ n) atTop (𝓝 ((ν k)[id])) := by
  filter_upwards [respMart_div_pullCount_ae_tendsto_zero h k hY2] with ω hslln hN
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
  have hB : Tendsto (fun n ↦ (θ₀ - (ν k)[id]) / ((pullCount A k n ω : ℝ) + 1)) atTop (𝓝 0) := by
    have hb := hpcinv.const_mul (θ₀ - (ν k)[id])
    rw [mul_zero] at hb
    simpa [div_eq_mul_inv] using hb
  -- Sum of the two fractions → 0, and it equals `θ̂ - θ`.
  have hAB : Tendsto (fun n ↦ (respMart ν A Y k n ω + (θ₀ - (ν k)[id]))
      / ((pullCount A k n ω : ℝ) + 1)) atTop (𝓝 0) := by
    have hsum := hA.add hB
    rw [add_zero] at hsum
    refine hsum.congr' (Eventually.of_forall fun n ↦ ?_)
    simp only [add_div]
  have hsub : Tendsto (fun n ↦ estimator
      (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω) (fun j ↦ Y j ω) θ₀ n
      - (ν k)[id]) atTop (𝓝 0) := by
    refine hAB.congr' (Eventually.of_forall fun n ↦ ?_)
    have hden_ne : count (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω) n + 1 ≠ 0 := by
      rw [count_indicator_eq_pullCount]; positivity
    have key : estimator (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω)
          (fun j ↦ Y j ω) θ₀ n - (ν k)[id]
        = (respMart ν A Y k n ω + (θ₀ - (ν k)[id])) / ((pullCount A k n ω : ℝ) + 1) := by
      rw [estimator_sub_eq _ _ ((ν k)[id]) θ₀ n hden_ne]
      simp only [respMG_indicator_eq_respMart, count_indicator_eq_pullCount]
    exact key.symm
  have hconst : Tendsto (fun _ : ℕ ↦ (ν k)[id]) atTop (𝓝 ((ν k)[id])) := tendsto_const_nhds
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
theorem exists_tendsto_estimator_of_not_pullCount_atTop (k : 𝓐) (θ₀ : ℝ) (ω : Ω)
    (hnot : ¬ Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop) :
    ∃ L, Tendsto (fun n ↦ estimator (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω)
      (fun j ↦ Y j ω) θ₀ n) atTop (𝓝 L) := by
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
  refine ⟨estimator (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω)
    (fun j ↦ Y j ω) θ₀ N₀, tendsto_atTop_of_eventually_const (i₀ := N₀) fun n hn ↦ ?_⟩
  have hden : count (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω) n
      = count (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω) N₀ := by
    rw [count_indicator_eq_pullCount, count_indicator_eq_pullCount, hconst n hn]
  have hnum : ∑ j ∈ Finset.range n, Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω * Y j ω
      = ∑ j ∈ Finset.range N₀, Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω * Y j ω := by
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
      rw [pullCount_add_one, hEq, if_pos rfl] at hj1
      omega
    rw [Set.indicator_of_notMem (by simpa using hAjk), zero_mul]
  simp only [estimator, hden, hnum]

omit [DecidableEq 𝓐] in
/-- **The sequential estimator converges a.s.** (the convergence content of
`lem:theta_limit_dichotomy`). For each arm `k`, `\hat\theta_{n,k}` converges almost surely: to
the arm mean `θ_k = (ν k)[id]` on `\{N_{n,k}\to\infty\}` (Lemma
`estimator_ae_tendsto_of_pullCount_atTop`), and to an eventually-attained value on
`\{\sup_n N_{n,k}<\infty\}` (Lemma `exists_tendsto_estimator_of_not_pullCount_atTop`). The
dichotomy is exhaustive because `N_{n,k}` is monotone in `n`. -/
theorem estimator_ae_tendsto (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : ℝ) :
    ∀ᵐ ω ∂P, ∃ L, Tendsto (fun n ↦ estimator
      (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω) (fun j ↦ Y j ω) θ₀ n)
      atTop (𝓝 L) := by
  classical
  filter_upwards [estimator_ae_tendsto_of_pullCount_atTop h k hY2 θ₀] with ω hω
  by_cases hlim : Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop
  · exact ⟨(ν k)[id], hω hlim⟩
  · exact exists_tendsto_estimator_of_not_pullCount_atTop k θ₀ ω hlim

omit [DecidableEq 𝓐] in
/-- **The estimator vector converges a.s.** (vector form of `lem:theta_converges`, feeding
`lem:rho_converges`). With finitely (or countably) many arms, the per-arm a.s. limits combine
into a single a.s. limit vector `z : 𝓐 → ℝ`: almost surely there is `z` with
`\hat\theta_{n,k}\to z_k` for every arm `k` simultaneously. This is the a.s. convergence
`\hat\Params_n \to z` that Condition **B** then transports through the (continuous) target map. -/
theorem estimator_ae_tendsto_pi [Countable 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ) :
    ∀ᵐ ω ∂P, ∃ z : 𝓐 → ℝ, ∀ k, Tendsto (fun n ↦ estimator
      (fun j ↦ Set.indicator {ω | A j ω = k} (fun _ ↦ (1 : ℝ)) ω) (fun j ↦ Y j ω) (θ₀ k) n)
      atTop (𝓝 (z k)) := by
  filter_upwards [ae_all_iff.mpr fun k ↦ estimator_ae_tendsto h k hY2 (θ₀ k)] with ω hω
  choose z hz using hω
  exact ⟨z, hz⟩

omit [DecidableEq 𝓐] in
/-- **Convergence of the plug-in target** (blueprint `lem:rho_converges`, continuity form).
For any continuous target map `T : (𝓐 → ℝ) → (𝓐 → ℝ)`, the plug-in target
`\hat\rho_n = T(\hat\Params_n)` converges a.s.: almost surely there is `u : 𝓐 → ℝ` with
`\hat\rho_{n,k} \to u_k` for every arm `k`. Here `u = T z`, where `z` is the a.s. limit of the
estimator vector (`estimator_ae_tendsto_pi`); continuity of `T` transports the convergence
`\hat\Params_n \to z` (in the product topology) to `T(\hat\Params_n) \to T z`. The blueprint's
non-sparse refinement `u \in (0,1)^K` needs the rest of Condition **B** and is deferred. -/
theorem rho_converges [Countable 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k, Tendsto (fun n ↦ T (fun k' ↦ estimator
      (fun j ↦ Set.indicator {ω | A j ω = k'} (fun _ ↦ (1 : ℝ)) ω) (fun j ↦ Y j ω) (θ₀ k') n) k)
      atTop (𝓝 (u k)) := by
  filter_upwards [estimator_ae_tendsto_pi h hY2 θ₀] with ω hω
  obtain ⟨z, hz⟩ := hω
  refine ⟨T z, fun k ↦ ?_⟩
  have hvec : Tendsto (fun n ↦ (fun k' ↦ estimator
      (fun j ↦ Set.indicator {ω | A j ω = k'} (fun _ ↦ (1 : ℝ)) ω)
        (fun j ↦ Y j ω) (θ₀ k') n)) atTop (𝓝 z) := tendsto_pi_nhds.mpr hz
  exact tendsto_pi_nhds.mp ((hT.tendsto z).comp hvec) k

end AlphaRAR
