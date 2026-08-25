/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.AnscombeCLT
public import AlphaRAR.YDK2026.ResponseLIL
public import AlphaRAR.YDK2026.ResponseCLT

/-!
# The self-normalized response-martingale CLT for sparse targets

Applying the Anscombe random-time CLT (`AlphaRAR.tendsto_map_anscombe_iid`) to the i.i.d. sampled
responses of a fixed arm `k`, we obtain the self-normalized response-martingale CLT normalized by
the arm's **own** random pull count `N_{n,k}`:
`Q_{n,k}/√N_{n,k} ⇒ 𝒩(0, V_k)`, where `V_k = Var[id; ν k]`.

Unlike the deterministic-normalizer route (`AlphaRAR.respMart_selfNorm_tendsto_gaussianReal`), which
requires a *positive* limiting proportion `N_{n,k}/n → v_k > 0`, this version needs only the
regularity `N_{n,k}/c_{n,k} → 1` for a deterministic `c_{n,k} → ∞` — the concentration input which,
for **sparse** targets `v_k = 0`, replaces positivity. This is the componentwise ingredient of the
sparse CLT (blueprint `cor:sparse_clt`, `lem:componentwise`).
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Learning Real

open scoped Topology ENNReal

namespace AlphaRAR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {𝓐 : Type*} {m𝓐 : MeasurableSpace 𝓐} [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The self-normalized response martingale `ω ↦ (√N_{n,k})⁻¹ Q_{n,k}` is measurable. -/
lemma measurable_respSelfNorm (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (n : ℕ) :
    Measurable (fun ω ↦ (√(pullCount A k n ω : ℝ))⁻¹ * respMart ν A Y k n ω) :=
  (((measurable_of_countable _).comp (measurable_pullCount h.measurable_action k n)).sqrt.inv).mul
    (measurable_respMart h k n)

/-- **The self-normalized response-martingale CLT for sparse targets** (blueprint
`lem:componentwise`, per-arm form via Anscombe). Under Condition A, for an arm `k` sampled
infinitely often, whose pull count obeys the regularity `N_{n,k}/c_n → 1` a.s.\ for some
deterministic `c_n → ∞`, the response martingale normalized by its own random count converges,
`Q_{n,k}/√N_{n,k} ⇒ 𝒩(0, V_k)`, where `V_k = Var[id; ν k]`. No positivity of the limiting proportion
is required, so this holds for sparse targets `v_k = 0`. -/
lemma respMart_selfNorm_anscombe_tendsto
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (hk_inf : ∀ᵐ ω ∂P, {j | A j ω = k}.Infinite)
    (hνk : MemLp id 2 (ν k))
    {c : ℕ → ℕ} (hc : Tendsto c atTop atTop)
    (hreg : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (c n : ℝ)) atTop (𝓝 1)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ (⟨P.map (fun ω ↦ (√(pullCount A k n ω : ℝ))⁻¹ * respMart ν A Y k n ω),
        Measure.isProbabilityMeasure_map
          (measurable_respSelfNorm h k n).aemeasurable⟩ : ProbabilityMeasure ℝ)) atTop
      (𝓝 (⟨gaussianReal 0 (Var[id; ν k]).toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have : IsProbabilityMeasure (ν k) := IsMarkovKernel.isProbabilityMeasure k
  have hint_id : Integrable (fun x : ℝ ↦ x) (ν k) := hνk.integrable (by norm_num)
  have hint_sq : Integrable (fun x : ℝ ↦ x ^ 2) (ν k) := hνk.integrable_sq
  set D := actionIndicator A k with hDdef
  set θ := ν.means k with hθdef
  -- Clean-sample setup (globally i.i.d.\ representative of the sampled responses of arm `k`).
  have hD𝒢 : ∀ i, Measurable[h.filtrationAction i] (D i) := fun i ↦
    Measurable.ite ((h.adapted_action_filtrationAction i) (measurableSet_singleton k))
      measurable_const measurable_const
  have hDinf : ∀ᵐ ω ∂P, {j | D j ω = 1}.Infinite := by
    filter_upwards [hk_inf] with ω hω; rwa [Set.ext (fun j ↦ actionIndicator_eq_one_iff)]
  have hCmeas : ∀ i, Measurable (sampledClean Y D i) :=
    fun i ↦ measurable_sampledClean h.measurable_feedback hD𝒢 i
  have hmapC : ∀ i, P.map (sampledClean Y D i) = ν k := fun i ↦
    (Measure.map_congr (sampledSeq_ae_eq_sampledClean hDinf i).symm).trans
      (map_sampledResponse_eq h k hk_inf i)
  have hcov : ∀ g : ℝ → ℝ, AEStronglyMeasurable g (ν k) →
      ∫ ω, g (sampledClean Y D 0 ω) ∂P = ∫ x, g x ∂(ν k) := by
    intro g hg
    have hg' : AEStronglyMeasurable g (P.map (sampledClean Y D 0)) := by rw [hmapC 0]; exact hg
    have hmap := integral_map (φ := sampledClean Y D 0) (hCmeas 0).aemeasurable hg'
    rw [hmapC 0] at hmap; exact hmap.symm
  have hintcov : ∀ g : ℝ → ℝ, Integrable g (ν k) →
      Integrable (fun ω ↦ g (sampledClean Y D 0 ω)) P := by
    intro g hg
    have hg' : AEStronglyMeasurable g (P.map (sampledClean Y D 0)) := by
      rw [hmapC 0]; exact hg.aestronglyMeasurable
    refine (integrable_map_measure hg' (hCmeas 0).aemeasurable).mp ?_
    rw [hmapC 0]; exact hg
  have hθ' : θ = ∫ x, x ∂(ν k) := by rw [hθdef, Kernel.means_apply]; simp only [id_eq]
  -- moments of the clean sample, expressed through the common law `ν k`
  have hμθ : ∫ ω, sampledClean Y D 0 ω ∂P = θ := by
    rw [hcov (fun x ↦ x) hint_id.aestronglyMeasurable, ← hθ']
  have hint2C : Integrable (fun ω ↦ sampledClean Y D 0 ω ^ 2) P := hintcov (fun x ↦ x ^ 2) hint_sq
  have hX2 : MemLp (sampledClean Y D 0) 2 P :=
    (memLp_two_iff_integrable_sq (hCmeas 0).aestronglyMeasurable).mpr hint2C
  have hintCsq : Integrable (fun x ↦ (x - θ) ^ 2) (ν k) := by
    have hexp : (fun x : ℝ ↦ (x - θ) ^ 2) = fun x ↦ x ^ 2 - 2 * θ * x + θ ^ 2 := by
      funext x; ring
    rw [hexp]
    exact (hint_sq.sub (hint_id.const_mul (2 * θ))).add (integrable_const (θ ^ 2))
  have hVar : Var[sampledClean Y D 0; P] = Var[id; ν k] := by
    rw [variance_eq_integral (hCmeas 0).aemeasurable, hμθ,
      show (fun ω ↦ (sampledClean Y D 0 ω - θ) ^ 2)
          = fun ω ↦ (fun x ↦ (x - θ) ^ 2) (sampledClean Y D 0 ω) from rfl,
      hcov (fun x ↦ (x - θ) ^ 2) hintCsq.aestronglyMeasurable, variance_id_eq_integral,
      hθdef, Kernel.means_apply]
  -- global i.i.d.\ and identical distribution of the clean samples
  have hindepC : iIndepFun (sampledClean Y D) P :=
    (iIndepFun_congr fun i ↦ sampledSeq_ae_eq_sampledClean hDinf i).mp
      (iIndepFun_sampledResponse h k hk_inf)
  have hidentC : ∀ i, IdentDistrib (sampledClean Y D i) (sampledClean Y D 0) P P := fun i ↦
    IdentDistrib.mk (hCmeas i).aemeasurable (hCmeas 0).aemeasurable ((hmapC i).trans (hmapC 0).symm)
  -- random-index sum measurability
  have hSumMeas : ∀ n, Measurable
      (fun ω ↦ ∑ i ∈ Finset.range (pullCount A k n ω), sampledClean Y D i ω) := fun n ↦ by
    have hF : Measurable (fun p : ℕ × Ω ↦ ∑ i ∈ Finset.range p.1, sampledClean Y D i p.2) :=
      measurable_from_prod_countable_right
        (f := fun p : ℕ × Ω ↦ ∑ i ∈ Finset.range p.1, sampledClean Y D i p.2)
        fun m ↦ Finset.measurable_sum (Finset.range m) fun i _ ↦ hCmeas i
    exact hF.comp ((measurable_pullCount h.measurable_action k n).prodMk measurable_id)
  -- Anscombe CLT for the clean samples with random index `N_{n,k}`.
  have hanscombe := tendsto_map_anscombe_iid hCmeas hX2 hindepC hidentC
    (measurable_pullCount h.measurable_action k) hSumMeas hc hreg
  rw [hVar] at hanscombe
  -- identify the Anscombe object with `(√N_{n,k})⁻¹ Q_{n,k}` almost everywhere
  have hae_eq : ∀ᵐ ω ∂P, ∀ i, sampledSeq Y D i ω = sampledClean Y D i ω := by
    rw [ae_all_iff]; exact fun i ↦ sampledSeq_ae_eq_sampledClean hDinf i
  refine hanscombe.congr' (Filter.Eventually.of_forall fun n ↦ Subtype.ext (Measure.map_congr ?_))
  filter_upwards [hae_eq] with ω hω
  congr 1
  rw [hμθ, respMart_eq_sum_sampledSeq k n ω, hitCount_actionIndicator_eq_pullCount k n ω, ← hθdef,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ (hω i).symm

omit [DecidableEq 𝓐] in
/-- The per-arm estimator `θ̂_{n,k}` is measurable. -/
lemma measurable_estimator_arm (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (θ₀ : ℝ)
    (n : ℕ) :
    Measurable (fun ω ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) θ₀ n) := by
  have harm : ∀ j, Measurable (fun ω ↦ actionIndicator A k j ω) := fun j ↦
    (measurable_const (a := (1 : ℝ))).indicator
      ((measurableSet_singleton k).preimage (h.measurable_action j))
  simp only [estimator]
  exact Measurable.div
    ((Finset.measurable_sum _ fun j _ ↦ (harm j).mul (h.measurable_feedback j)).add_const θ₀)
    ((measurable_count_actionIndicator h k n).add_const 1)

/-- The self-normalized estimator error `ω ↦ √N_{n,k}(θ̂_{n,k} - θ_k)` is measurable. -/
lemma measurable_estimatorSqrtN (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (θ₀ : ℝ)
    (n : ℕ) :
    Measurable (fun ω ↦ √(pullCount A k n ω : ℝ)
      * (estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) θ₀ n - ν.means k)) :=
  (((measurable_of_countable _).comp (measurable_pullCount h.measurable_action k n)).sqrt).mul
    ((measurable_estimator_arm h k θ₀ n).sub_const _)

/-- **The self-normalized estimator CLT for sparse targets** (blueprint `cor:sparse_clt`, per-arm
form via Anscombe). Under Condition A, for an arm `k` sampled infinitely often whose pull count
obeys the regularity `N_{n,k}/c_n → 1` a.s.\ for some deterministic `c_n → ∞`, the estimator error
scaled by its own random count converges,
`√N_{n,k}(θ̂_{n,k} - θ_k) ⇒ 𝒩(0, V_k)`, with `V_k = Var[id; ν k]`. No positivity of the limiting
proportion is required, so this is the componentwise ingredient of the sparse CLT. Obtained from
`respMart_selfNorm_anscombe_tendsto` via the exact Bahadur identity `estimator_sub_eq` and two
Slutsky steps (the scaling factors `N/(N+1) → 1` and `√N/(N+1) → 0` in probability). -/
lemma estimator_sqrtN_anscombe_tendsto
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (hk_inf : ∀ᵐ ω ∂P, {j | A j ω = k}.Infinite)
    (hνk : MemLp id 2 (ν k)) (θ₀ : ℝ)
    {c : ℕ → ℕ} (hc : Tendsto c atTop atTop)
    (hreg : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (c n : ℝ)) atTop (𝓝 1)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ (⟨P.map (fun ω ↦ √(pullCount A k n ω : ℝ)
          * (estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) θ₀ n - ν.means k)),
        Measure.isProbabilityMeasure_map
          (measurable_estimatorSqrtN h k θ₀ n).aemeasurable⟩ : ProbabilityMeasure ℝ))
      atTop
      (𝓝 (⟨gaussianReal 0 (Var[id; ν k]).toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  set θ := ν.means k with hθdef
  have hQ := respMart_selfNorm_anscombe_tendsto h k hk_inf hνk hc hreg
  -- pull count `→ ∞` a.e. (from infinitely many pulls)
  have hpcinf : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop := by
    have hDinf : ∀ᵐ ω ∂P, {j | actionIndicator A k j ω = 1}.Infinite := by
      filter_upwards [hk_inf] with ω hω; rwa [Set.ext fun j ↦ actionIndicator_eq_one_iff]
    filter_upwards [hDinf] with ω hinf
    exact tendsto_natCast_atTop_atTop.comp
      ((hitCount_tendsto_atTop (D := actionIndicator A k) hinf).congr fun n ↦
        hitCount_actionIndicator_eq_pullCount k n ω)
  -- abbreviations for the Slutsky factors
  set R : ℕ → Ω → ℝ := fun n ω ↦ (pullCount A k n ω : ℝ) / ((pullCount A k n ω : ℝ) + 1) with hRdef
  set E : ℕ → Ω → ℝ := fun n ω ↦
    (θ₀ - θ) * (√(pullCount A k n ω : ℝ) / ((pullCount A k n ω : ℝ) + 1)) with hEdef
  have hRmeas : ∀ n, AEMeasurable (R n) P := fun n ↦ by
    have hm : Measurable (fun ω ↦ (pullCount A k n ω : ℝ)) :=
      (measurable_of_countable _).comp (measurable_pullCount h.measurable_action k n)
    exact (hm.div (hm.add_const 1)).aemeasurable
  have hEmeas : ∀ n, AEMeasurable (E n) P := fun n ↦ by
    have hm : Measurable (fun ω ↦ (pullCount A k n ω : ℝ)) :=
      (measurable_of_countable _).comp (measurable_pullCount h.measurable_action k n)
    exact (measurable_const.mul (hm.sqrt.div (hm.add_const 1))).aemeasurable
  have hR1 : TendstoInMeasure P R atTop (fun _ ↦ (1 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hRmeas n).aestronglyMeasurable) ?_
    filter_upwards [hpcinf] with ω hω
    have hinv : Tendsto (fun n ↦ ((pullCount A k n ω : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 hω)
    have hlim : Tendsto (fun n ↦ 1 - ((pullCount A k n ω : ℝ) + 1)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hinv
    rw [sub_zero] at hlim
    refine hlim.congr fun n ↦ ?_
    rw [hRdef]; field_simp; ring
  have hE0 : TendstoInMeasure P E atTop (fun _ ↦ (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hEmeas n).aestronglyMeasurable) ?_
    filter_upwards [hpcinf] with ω hω
    have hg0 : Tendsto (fun n ↦ (√(pullCount A k n ω : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hω)
    have hsqrt0 : Tendsto
        (fun n ↦ √(pullCount A k n ω : ℝ) / ((pullCount A k n ω : ℝ) + 1)) atTop
        (𝓝 0) := by
      refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hg0
      rcases eq_or_ne (√(pullCount A k n ω : ℝ)) 0 with hs | hs
      · simp [hs]
      · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (pullCount A k n ω : ℝ) + 1), inv_mul_eq_div,
          le_div_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)),
          Real.mul_self_sqrt (Nat.cast_nonneg _)]
        linarith
    have := hsqrt0.const_mul (θ₀ - θ)
    rw [mul_zero] at this
    exact this.congr fun n ↦ by rw [hEdef]
  -- Multiplicative then additive Slutsky, then identify with `√N(θ̂-θ)`.
  have hmul := tendsto_map_mul_of_tendstoInMeasure_one
    (fun n ↦ (measurable_respSelfNorm h k n).aemeasurable) hRmeas hQ hR1
  have hadd := tendsto_map_add_of_tendstoInMeasure_zero
    (fun n ↦ ((measurable_respSelfNorm h k n).aemeasurable.mul (hRmeas n))) hEmeas hmul hE0
  refine hadd.congr' (Filter.Eventually.of_forall fun n ↦ Subtype.ext (congrArg (P.map ·) ?_))
  funext ω
  simp only [Pi.mul_apply, hRdef, hEdef]
  have hne : count (fun j ↦ actionIndicator A k j ω) n + 1 ≠ 0 := by
    rw [count_indicator_eq_pullCount]; positivity
  rw [estimator_sub_eq (X := fun j ↦ actionIndicator A k j ω) (Y · ω) θ θ₀ n hne,
    respMG_indicator_eq_respMart, count_indicator_eq_pullCount]
  rcases eq_or_ne (√(pullCount A k n ω : ℝ)) 0 with hs | hs
  · simp [hs]
  · have hNpos : (0 : ℝ) < (pullCount A k n ω : ℝ) :=
      Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs))
    have key1 : (√(pullCount A k n ω : ℝ))⁻¹ * (pullCount A k n ω : ℝ)
        = √(pullCount A k n ω : ℝ) := by
      rw [inv_mul_eq_div, div_eq_iff hs]; exact (Real.mul_self_sqrt hNpos.le).symm
    rw [show (√(pullCount A k n ω : ℝ))⁻¹ * respMart ν A Y k n ω
            * ((pullCount A k n ω : ℝ) / ((pullCount A k n ω : ℝ) + 1))
          = respMart ν A Y k n ω
            * ((√(pullCount A k n ω : ℝ))⁻¹ * (pullCount A k n ω : ℝ))
            / ((pullCount A k n ω : ℝ) + 1) by ring, key1]
    field_simp

end AlphaRAR
