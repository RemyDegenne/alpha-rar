/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.CentralLimitTheorem
import AlphaRAR.Mathlib.MartingaleMaximal
import AlphaRAR.Mathlib.LILHartmanWintner
import AlphaRAR.Mathlib.MartingaleCLT

/-!
# The Anscombe random-time-change central limit theorem

For an i.i.d. sequence `X : ℕ → Ω → ℝ` with finite variance `v = Var[X 0]`, write
`S_m = ∑_{j<m}(X_j - μ)` for the centered partial sums (`μ = 𝔼[X 0]`). The classical CLT gives
`S_n/√n ⇒ 𝒩(0, v)` along the *deterministic* index `n`. **Anscombe's theorem** upgrades this to a
*random* index: if `N : ℕ → Ω → ℕ` satisfies the regularity `N_n/c_n → 1` in probability for some
deterministic `c_n → ∞`, then the self-normalized random-time sum still converges,
`S_{N_n}/√(N_n) ⇒ 𝒩(0, v)`.

The regularity hypothesis is essential: for a general *adaptive* `N_n → ∞` the statement is false
(one can freeze the self-normalized martingale above its typical value by pausing the index near a
level crossing, using the law of the iterated logarithm). This is why the self-normalized response
CLT for **sparse** targets (where `N_{n,k}/n → 0`) genuinely needs this theorem rather than the
Slutsky self-normalization used in the non-sparse case.

## Proof outline

Decompose `S_{N_n}/√(N_n) = (S_{c_n}/√(c_n)) · √(c_n/N_n) + (S_{N_n} - S_{c_n})/√(N_n)`:

* the base term `S_{c_n}/√(c_n) ⇒ 𝒩(0,v)` is the Mathlib i.i.d. CLT
  (`tendstoInDistribution_inv_sqrt_mul_sum_sub`) precomposed with the subsequence `c_n → ∞`;
* the scaling `√(c_n/N_n) → 1` in probability by the regularity `N_n/c_n → 1`, so Slutsky
  (`tendsto_map_mul_of_tendstoInMeasure_one`) keeps the limit;
* the window remainder `(S_{N_n} - S_{c_n})/√(N_n) → 0` in probability, controlled by the Doob
  maximal inequality for the partial-sum martingale (`mart_maximal`) over the window
  `|m - c_n| ≤ ε c_n`.
-/

open MeasureTheory ProbabilityTheory Filter Finset

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The i.i.d. CLT along a deterministic subsequence.** For i.i.d. `X` with finite second moment,
the centered partial sums normalized by `√(c n)` converge in distribution to `𝒩(0, Var[X 0])` along
any `c : ℕ → ℕ` with `c n → ∞`. This is Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`
precomposed with the subsequence. -/
lemma tendsto_map_clt_comp {X : ℕ → Ω → ℝ} (hX2 : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {c : ℕ → ℕ} (hc : Tendsto c atTop atTop) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ (⟨P.map (fun ω ↦ (Real.sqrt (c n : ℝ))⁻¹ *
          (∑ k ∈ Finset.range (c n), X k ω - (c n : ℝ) * P[X 0])),
        Measure.isProbabilityMeasure_map
          (((Finset.aemeasurable_fun_sum _ fun i _ ↦ (hident i).aemeasurable_fst).sub_const
            _).const_mul _)⟩ : ProbabilityMeasure ℝ)) atTop
      (𝓝 (⟨gaussianReal 0 Var[X 0; P].toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have hbase := (tendstoInDistribution_inv_sqrt_mul_sum_sub (Y := (id : ℝ → ℝ))
    (P' := gaussianReal 0 Var[X 0; P].toNNReal) HasLaw.id hX2 hindep hident).tendsto
  simp only [Measure.map_id] at hbase
  exact hbase.comp hc

/-- **Additive Slutsky for the CLT.** If the laws of `X n` converge weakly to `𝒩(0,σ²)` and
`Y n → 0` in probability, then so do the laws of `X n + Y n`. Companion to
`tendsto_map_mul_of_tendstoInMeasure_one`, used to absorb the negligible window remainder in the
Anscombe assembly. -/
lemma tendsto_map_add_of_tendstoInMeasure_zero {σ2 : NNReal} {X Y : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, AEMeasurable (X n) P) (hY_meas : ∀ n, AEMeasurable (Y n) P)
    (hX : Tendsto (β := ProbabilityMeasure ℝ)
        (fun n ↦ ⟨P.map (X n), Measure.isProbabilityMeasure_map (hX_meas n)⟩) atTop
        (𝓝 ⟨gaussianReal 0 σ2, inferInstance⟩))
    (hY : TendstoInMeasure P Y atTop (fun _ ↦ (0 : ℝ))) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ ⟨P.map (fun ω ↦ X n ω + Y n ω),
        Measure.isProbabilityMeasure_map ((hX_meas n).add (hY_meas n))⟩) atTop
      (𝓝 ⟨gaussianReal 0 σ2, inferInstance⟩) := by
  have hid : TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ ↦ P) (gaussianReal 0 σ2) := by
    refine ⟨hX_meas, aemeasurable_id, ?_⟩
    simp only [Measure.map_id]
    exact hX
  have hslut := hid.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun x : ℝ × ℝ ↦ x.1 + x.2) (by fun_prop) hY hY_meas
  have h2 := hslut.tendsto
  simp only [id_eq, add_zero, Measure.map_id'] at h2
  exact h2

/-- **The window remainder is negligible in probability.** For a square-integrable martingale `S`
whose increments have second moment `≤ v`, a random index `N` and a deterministic `c → ∞` with the
regularity `N_n/c_n → 1` a.s., the self-normalized increment across the window `[N_n, c_n]` tends to
`0` in probability:
`(√N_n)⁻¹ (S_{N_n} - S_{c_n}) → 0`.

The window `|m - c_n| ≤ ε c_n` is controlled by the Doob maximal inequality (`mart_maximal`)
anchored at `c_n + ⌊ε c_n⌋`: the maximal increment there is `O(√(ε c_n))` in `L¹`, so after
dividing by `√((1-ε) c_n)` and applying Markov it is `O(√ε)`, uniformly in `n`. Letting `ε → 0`
(after the good
event `|N_n - c_n| ≤ ε c_n` has probability `→ 1`) gives the claim. -/
lemma tendstoInMeasure_window {S : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ mΩ} (hM : Martingale S 𝒢 P)
    (hM2 : ∀ n, Integrable (fun ω ↦ S n ω ^ 2) P)
    (hd2 : ∀ n, Integrable (fun ω ↦ (S (n + 1) ω - S n ω) ^ 2) P)
    (hcross : ∀ a b, Integrable (fun ω ↦ S a ω * S b ω) P)
    {v : ℝ} (hv0 : 0 ≤ v) (hinc : ∀ n, ∫ ω, (S (n + 1) ω - S n ω) ^ 2 ∂P ≤ v)
    {N : ℕ → Ω → ℕ} (hNmeas : ∀ n, Measurable (N n))
    {c : ℕ → ℕ} (hc : Tendsto (fun n ↦ (c n : ℕ)) atTop atTop)
    (hreg : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (N n ω : ℝ) / (c n : ℝ)) atTop (𝓝 1)) :
    TendstoInMeasure P
      (fun n ω ↦ (Real.sqrt (N n ω : ℝ))⁻¹ * (S (N n ω) ω - S (c n) ω))
      atTop (fun _ ↦ 0) := by
  have hSmeas : ∀ k, Measurable (S k) := fun k ↦
    (hM.stronglyAdapted k).measurable.mono (𝒢.le k) le_rfl
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  simp only [dist_zero_right, Real.norm_eq_abs]
  rw [ENNReal.tendsto_nhds_zero]
  intro ηe hηe
  rcases eq_or_ne ηe ⊤ with htop | hηtop
  · exact Eventually.of_forall fun k ↦ htop ▸ le_top
  -- `ηe` is finite positive; split it as `ofReal ρ + ofReal ρ` with `ρ = ηe.toReal/2`.
  set ρ : ℝ := ηe.toReal / 2 with hρdef
  have hηR : 0 < ηe.toReal := ENNReal.toReal_pos hηe.ne' hηtop
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρη : ENNReal.ofReal ρ + ENNReal.ofReal ρ = ηe := by
    rw [← ENNReal.ofReal_add hρ0.le hρ0.le, hρdef]
    rw [show ηe.toReal / 2 + ηe.toReal / 2 = ηe.toReal by ring, ENNReal.ofReal_toReal hηtop]
  -- Choose the window scale `ε ∈ (0,1)` so that the maximal-inequality contribution `≤ ρ`.
  set ε : ℝ := min (1 / 2) ((ρ * δ / 8) ^ 2 / (4 * (v + 1))) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hε1 : ε < 1 := lt_of_le_of_lt hεhalf (by norm_num)
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have hKε : (8 / δ) * Real.sqrt (2 * v * ε / (1 - ε)) ≤ ρ := by
    have hεbound : ε ≤ (ρ * δ / 8) ^ 2 / (4 * (v + 1)) := min_le_right _ _
    have h4v : (0 : ℝ) < 4 * (v + 1) := by positivity
    have hs2 : 4 * (v + 1) * ε ≤ (ρ * δ / 8) ^ 2 := by
      rw [show 4 * (v + 1) * ε = ε * (4 * (v + 1)) by ring]
      exact (le_div_iff₀ h4v).mp hεbound
    have hs1 : 2 * v * ε / (1 - ε) ≤ 4 * (v + 1) * ε := by
      rw [div_le_iff₀ h1ε]
      nlinarith [mul_nonneg hε0.le hv0, mul_nonneg (mul_nonneg hε0.le hv0)
        (by linarith : (0 : ℝ) ≤ 1 - 2 * ε), hε0.le, hv0]
    have harg : 2 * v * ε / (1 - ε) ≤ (ρ * δ / 8) ^ 2 := le_trans hs1 hs2
    have hsqrt : Real.sqrt (2 * v * ε / (1 - ε)) ≤ ρ * δ / 8 :=
      calc Real.sqrt (2 * v * ε / (1 - ε)) ≤ Real.sqrt ((ρ * δ / 8) ^ 2) := Real.sqrt_le_sqrt harg
        _ = ρ * δ / 8 := Real.sqrt_sq (by positivity)
    calc (8 / δ) * Real.sqrt (2 * v * ε / (1 - ε)) ≤ (8 / δ) * (ρ * δ / 8) := by
          gcongr
      _ = ρ := by field_simp
  -- Window quantities: `L k = ⌊ε c_k⌋`, anchor `a k = c_k + L k`, maximal increment `W k`.
  set L : ℕ → ℕ := fun k ↦ ⌊ε * (c k : ℝ)⌋₊ with hLdef
  set a : ℕ → ℕ := fun k ↦ c k + L k with hadef
  set W : ℕ → Ω → ℝ := fun k ω ↦
    (range (2 * L k + 1)).sup' nonempty_range_add_one (fun m ↦ |S (a k) ω - S (a k - m) ω|)
    with hWdef
  have hWnn : ∀ k ω, 0 ≤ W k ω := fun k ω ↦
    le_trans (abs_nonneg _) (Finset.le_sup' (fun m ↦ |S (a k) ω - S (a k - m) ω|)
      (mem_range.mpr (Nat.succ_pos _)))
  have hWmeas : ∀ k, Measurable (W k) := fun k ↦
    Finset.measurable_range_sup'' fun m _ ↦
      continuous_abs.measurable.comp ((hSmeas (a k)).sub (hSmeas (a k - m)))
  have hLle : ∀ k, L k ≤ c k := fun k ↦ by
    have hcknn : (0 : ℝ) ≤ (c k : ℝ) := Nat.cast_nonneg _
    have hle : ε * (c k : ℝ) ≤ (c k : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) hcknn]
    calc L k = ⌊ε * (c k : ℝ)⌋₊ := rfl
      _ ≤ ⌊(c k : ℝ)⌋₊ := Nat.floor_le_floor hle
      _ = c k := Nat.floor_natCast _
  -- Doob maximal inequality: `∫⁻ W k ≤ ofReal (4√(v·2L k))`.
  have hmax : ∀ k, ∫⁻ ω, ENNReal.ofReal (W k ω) ∂P
      ≤ ENNReal.ofReal (4 * Real.sqrt (v * ((2 * L k : ℕ) : ℝ))) := fun k ↦ by
    simp only [hWdef]
    exact mart_maximal hM hM2 hd2 hcross hinc (L := 2 * L k) (n := a k)
      (by have h := hLle k; simp only [hadef]; omega)
  -- The good event `G k = {|N_k - c_k| ≤ ε c_k}`; its complement has probability `→ 0`.
  set G : ℕ → Set Ω := fun k ↦ {ω | |(N k ω : ℝ) - (c k : ℝ)| ≤ ε * (c k : ℝ)} with hGdef
  have hNcast : ∀ k, Measurable (fun ω ↦ (N k ω : ℝ)) := fun k ↦
    (measurable_of_countable _).comp (hNmeas k)
  have hGmeas : ∀ k, MeasurableSet (G k) :=
    fun k ↦ measurableSet_le (((hNcast k).sub measurable_const).abs) measurable_const
  have hGc : Tendsto (fun k ↦ P (G k)ᶜ) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k ↦ ∫⁻ ω, (G k)ᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂P) atTop
        (𝓝 (∫⁻ _ω, (0 : ℝ≥0∞) ∂P)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ 1)
        (fun k ↦ measurable_const.indicator (hGmeas k).compl)
        (fun k ↦ Eventually.of_forall fun ω ↦ Set.indicator_le_self _ _ ω) (by simp) ?_
      filter_upwards [hreg] with ω hω
      have hev : ∀ᶠ k in atTop, (G k)ᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω = 0 := by
        have h1 : ∀ᶠ k in atTop, |(N k ω : ℝ) / (c k : ℝ) - 1| < ε := by
          filter_upwards [hω (Metric.ball_mem_nhds (1 : ℝ) hε0)] with k hk
          rwa [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hk
        filter_upwards [h1, hc.eventually_ge_atTop 1] with k hk hck1
        have hck0 : (0 : ℝ) < (c k : ℝ) := by exact_mod_cast hck1
        have hmemG : ω ∈ G k := by
          rw [hGdef]
          simp only [Set.mem_setOf_eq]
          rw [show (N k ω : ℝ) - (c k : ℝ) = ((N k ω : ℝ) / (c k : ℝ) - 1) * (c k : ℝ) by
            field_simp, abs_mul, abs_of_nonneg hck0.le]
          exact mul_le_mul_of_nonneg_right hk.le hck0.le
        exact Set.indicator_of_notMem (by simpa using hmemG) _
      exact tendsto_const_nhds.congr' (by filter_upwards [hev] with k hk; rw [hk])
    have heq : (fun k ↦ ∫⁻ ω, (G k)ᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂P)
        = fun k ↦ P (G k)ᶜ := by
      funext k; rw [lintegral_indicator (hGmeas k).compl]; simp
    rw [heq, lintegral_zero] at hlim
    exact hlim
  -- Assemble: `P{δ ≤ |·|} ≤ P(Gᶜ) + ofReal ρ`, and `P(Gᶜ) → 0`, so eventually `≤ 2 ofReal ρ = ηe`.
  have hA : ∀ᶠ k in atTop, P (G k)ᶜ ≤ ENNReal.ofReal ρ :=
    hGc.eventually_le_const (by simpa using ENNReal.ofReal_pos.mpr hρ0)
  have hB : ∀ᶠ k in atTop,
      P {ω | δ ≤ |(Real.sqrt (N k ω : ℝ))⁻¹ * (S (N k ω) ω - S (c k) ω)|}
        ≤ P (G k)ᶜ + ENNReal.ofReal ρ := by
    filter_upwards [hc.eventually_ge_atTop 1] with k hck1
    have hck0 : (0 : ℝ) < (c k : ℝ) := by exact_mod_cast hck1
    have hak : a k = c k + L k := rfl
    have hLle' := hLle k
    have h1εck : (0 : ℝ) < (1 - ε) * (c k : ℝ) := mul_pos h1ε hck0
    -- Pointwise bound on the good event.
    have hfG : ∀ ω ∈ G k, |(Real.sqrt (N k ω : ℝ))⁻¹ * (S (N k ω) ω - S (c k) ω)|
        ≤ 2 * W k ω / Real.sqrt ((1 - ε) * (c k : ℝ)) := by
      intro ω hωG
      rw [hGdef] at hωG
      simp only [Set.mem_setOf_eq] at hωG
      have hNlo : (1 - ε) * (c k : ℝ) ≤ (N k ω : ℝ) := by
        have := (abs_le.mp hωG).1; nlinarith [this]
      -- window membership of `N k ω` and `c k`
      have hNle : N k ω ≤ a k := by
        by_cases h : c k ≤ N k ω
        · have hr : ((N k ω - c k : ℕ) : ℝ) ≤ ε * (c k : ℝ) := by
            rw [Nat.cast_sub h]; have := (abs_le.mp hωG).2; linarith
          have hle2 : N k ω - c k ≤ L k := Nat.le_floor hr
          omega
        · omega
      have hNge : a k - 2 * L k ≤ N k ω := by
        by_cases h : N k ω ≤ c k
        · have hr : ((c k - N k ω : ℕ) : ℝ) ≤ ε * (c k : ℝ) := by
            rw [Nat.cast_sub h]; have := (abs_le.mp hωG).1; linarith
          have hle2 : c k - N k ω ≤ L k := Nat.le_floor hr
          omega
        · omega
      have hck_le_ak : c k ≤ a k := by omega
      have hwin : ∀ j, j ≤ a k → a k - 2 * L k ≤ j → |S (a k) ω - S j ω| ≤ W k ω := by
        intro j hj1 hj2
        have hmem : (a k - j) ∈ range (2 * L k + 1) := mem_range.mpr (by omega)
        have hle := Finset.le_sup' (fun m ↦ |S (a k) ω - S (a k - m) ω|) hmem
        rwa [Nat.sub_sub_self hj1] at hle
      have hSbnd : |S (N k ω) ω - S (c k) ω| ≤ 2 * W k ω := by
        calc |S (N k ω) ω - S (c k) ω|
            ≤ |S (a k) ω - S (N k ω) ω| + |S (a k) ω - S (c k) ω| := by
              rw [abs_sub_comm (S (a k) ω) (S (N k ω) ω)]; exact abs_sub_le _ _ _
          _ ≤ W k ω + W k ω := add_le_add (hwin _ hNle hNge) (hwin _ hck_le_ak (by omega))
          _ = 2 * W k ω := by ring
      have hsqrtle : Real.sqrt ((1 - ε) * (c k : ℝ)) ≤ Real.sqrt (N k ω : ℝ) :=
        Real.sqrt_le_sqrt hNlo
      have hsqrtpos : (0 : ℝ) < Real.sqrt ((1 - ε) * (c k : ℝ)) := Real.sqrt_pos.mpr h1εck
      have hNsqrtpos : (0 : ℝ) < Real.sqrt (N k ω : ℝ) :=
        Real.sqrt_pos.mpr (lt_of_lt_of_le h1εck hNlo)
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_comm, ← div_eq_mul_inv,
        div_le_div_iff₀ hNsqrtpos hsqrtpos]
      exact mul_le_mul hSbnd hsqrtle (Real.sqrt_nonneg _) (by nlinarith [hWnn k ω])
    -- Inclusion into `Gᶜ ∪ {λ ≤ W}` and Markov.
    have hincl : {ω | δ ≤ |(Real.sqrt (N k ω : ℝ))⁻¹ * (S (N k ω) ω - S (c k) ω)|}
        ⊆ (G k)ᶜ ∪ {ω | δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2 ≤ W k ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      rcases em (ω ∈ G k) with hG | hG
      · refine Or.inr ?_
        simp only [Set.mem_setOf_eq]
        have hb := (hfG ω hG).trans' hω
        have hsqrtpos : (0 : ℝ) < Real.sqrt ((1 - ε) * (c k : ℝ)) :=
          Real.sqrt_pos.mpr h1εck
        rw [le_div_iff₀ hsqrtpos] at hb
        nlinarith [hb, hWnn k ω, hsqrtpos]
      · exact Or.inl hG
    have hMk : P {ω | δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2 ≤ W k ω} ≤ ENNReal.ofReal ρ := by
      have hlam : (0 : ℝ) < δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2 := by
        have : (0 : ℝ) < Real.sqrt ((1 - ε) * (c k : ℝ)) := Real.sqrt_pos.mpr h1εck
        positivity
      have hset : {ω | δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2 ≤ W k ω}
          = {ω | ENNReal.ofReal (δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2)
              ≤ ENNReal.ofReal (W k ω)} := by
        ext ω; exact (ENNReal.ofReal_le_ofReal_iff (hWnn k ω)).symm
      -- real bound `4√(v·2L k)/λ ≤ Kε ≤ ρ`
      have hLkεck : (L k : ℝ) ≤ ε * (c k : ℝ) := Nat.floor_le (by positivity)
      have hδ0 : δ ≠ 0 := ne_of_gt hδ
      have hKlam : (8 / δ) * Real.sqrt (2 * v * ε / (1 - ε))
            * (δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2)
          = 4 * Real.sqrt (2 * v * ε * (c k : ℝ)) := by
        set X := Real.sqrt (2 * v * ε / (1 - ε)) with hXdef
        set Y := Real.sqrt ((1 - ε) * (c k : ℝ)) with hYdef
        have hXY : X * Y = Real.sqrt (2 * v * ε * (c k : ℝ)) := by
          rw [hXdef, hYdef, ← Real.sqrt_mul (by positivity)]
          congr 1
          rw [div_mul_eq_mul_div, mul_comm (1 - ε) (c k : ℝ), ← mul_assoc, mul_div_assoc,
            div_self h1ε.ne', mul_one]
        rw [← hXY]; field_simp; ring
      have hnum : 4 * Real.sqrt (v * ((2 * L k : ℕ) : ℝ))
          ≤ 4 * Real.sqrt (2 * v * ε * (c k : ℝ)) := by
        have harg : v * ((2 * L k : ℕ) : ℝ) ≤ 2 * v * ε * (c k : ℝ) := by
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left hLkεck hv0]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg) (by norm_num)
      have hdivle : 4 * Real.sqrt (v * ((2 * L k : ℕ) : ℝ))
          / (δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2) ≤ ρ := by
        rw [div_le_iff₀ hlam]
        exact le_trans (hnum.trans_eq hKlam.symm)
          (mul_le_mul_of_nonneg_right hKε hlam.le)
      rw [hset]
      refine (meas_ge_le_lintegral_div (hWmeas k).ennreal_ofReal.aemeasurable
        (ENNReal.ofReal_pos.mpr hlam).ne' ENNReal.ofReal_ne_top).trans ?_
      calc (∫⁻ ω, ENNReal.ofReal (W k ω) ∂P)
              / ENNReal.ofReal (δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2)
          ≤ ENNReal.ofReal (4 * Real.sqrt (v * ((2 * L k : ℕ) : ℝ)))
              / ENNReal.ofReal (δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2) := by
            gcongr
            exact hmax k
        _ = ENNReal.ofReal (4 * Real.sqrt (v * ((2 * L k : ℕ) : ℝ))
              / (δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2)) :=
            (ENNReal.ofReal_div_of_pos hlam).symm
        _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hdivle
    calc P {ω | δ ≤ |(Real.sqrt (N k ω : ℝ))⁻¹ * (S (N k ω) ω - S (c k) ω)|}
        ≤ P ((G k)ᶜ ∪ {ω | δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2 ≤ W k ω}) :=
          measure_mono hincl
      _ ≤ P (G k)ᶜ + P {ω | δ * Real.sqrt ((1 - ε) * (c k : ℝ)) / 2 ≤ W k ω} := measure_union_le _ _
      _ ≤ P (G k)ᶜ + ENNReal.ofReal ρ := by gcongr
  filter_upwards [hA, hB] with k hAk hBk
  calc P {ω | δ ≤ |(Real.sqrt (N k ω : ℝ))⁻¹ * (S (N k ω) ω - S (c k) ω)|}
      ≤ P (G k)ᶜ + ENNReal.ofReal ρ := hBk
    _ ≤ ENNReal.ofReal ρ + ENNReal.ofReal ρ := by gcongr
    _ = ηe := hρη

/-- Measurability of the self-normalized random-time sum
`ω ↦ (√N ω)⁻¹ ((∑_{k<N ω} X k ω) - N ω · μ)`. -/
lemma measurable_natTimeSelfNorm {X : ℕ → Ω → ℝ} {N : Ω → ℕ} (μ : ℝ)
    (hNmeas : Measurable N) (hSumMeas : Measurable (fun ω ↦ ∑ k ∈ Finset.range (N ω), X k ω)) :
    Measurable (fun ω ↦ (Real.sqrt (N ω : ℝ))⁻¹ *
      ((∑ k ∈ Finset.range (N ω), X k ω) - (N ω : ℝ) * μ)) := by
  have hNr : Measurable (fun ω ↦ (N ω : ℝ)) := (measurable_of_countable _).comp hNmeas
  exact (hNr.sqrt.inv).mul (hSumMeas.sub (hNr.mul measurable_const))

/-- **The Anscombe self-normalized central limit theorem for i.i.d. sums.** For an i.i.d. sequence
`X` with finite variance `v = Var[X 0]` and centered partial sums `S_m = ∑_{k<m}(X_k − μ)`, and any
random index `N` obeying the regularity `N_n/c_n → 1` a.s. for a deterministic `c_n → ∞`, the
self-normalized random-time sum converges in distribution,
`S_{N_n}/√N_n = (√N_n)⁻¹ (∑_{k<N_n} X_k − N_n μ) ⇒ 𝒩(0, v)`.

The regularity hypothesis is essential: for a general adaptive `N_n → ∞` the statement fails (see
`tendstoInMeasure_window`). The proof combines the base i.i.d. CLT along the subsequence `c_n`
(`tendsto_map_clt_comp`), the negligibility of the window remainder (`tendstoInMeasure_window`), and
two Slutsky steps (`tendsto_map_mul_of_tendstoInMeasure_one`,
`tendsto_map_add_of_tendstoInMeasure_zero`). -/
theorem tendsto_map_anscombe_iid {X : ℕ → Ω → ℝ} (hXmeas : ∀ i, Measurable (X i))
    (hX2 : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {N : ℕ → Ω → ℕ} (hNmeas : ∀ n, Measurable (N n))
    (hSumMeas : ∀ n, Measurable (fun ω ↦ ∑ k ∈ Finset.range (N n ω), X k ω))
    {c : ℕ → ℕ} (hc : Tendsto c atTop atTop)
    (hreg : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (N n ω : ℝ) / (c n : ℝ)) atTop (𝓝 1)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ (⟨P.map (fun ω ↦ (Real.sqrt (N n ω : ℝ))⁻¹ *
          ((∑ k ∈ Finset.range (N n ω), X k ω) - (N n ω : ℝ) * P[X 0])),
        Measure.isProbabilityMeasure_map
          (measurable_natTimeSelfNorm P[X 0] (hNmeas n) (hSumMeas n)).aemeasurable⟩
            : ProbabilityMeasure ℝ)) atTop
      (𝓝 (⟨gaussianReal 0 Var[X 0; P].toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  set μ : ℝ := P[X 0] with hμ
  set v : ℝ := Var[X 0; P] with hvdef
  have hv0 : 0 ≤ v := variance_nonneg _ _
  set Yc : ℕ → Ω → ℝ := fun j ω ↦ X j ω - μ with hYc
  have hYcmeas : ∀ i, StronglyMeasurable (Yc i) := fun i ↦
    ((hXmeas i).sub measurable_const).stronglyMeasurable
  have hindepYc : iIndepFun Yc P := hindep.comp (fun _ x ↦ x - μ) fun _ ↦ measurable_id.sub_const μ
  have hmemLp : ∀ i, MemLp (X i) 2 P := fun i ↦ (hident i).memLp_iff.mpr hX2
  have hmemLpYc : ∀ i, MemLp (Yc i) 2 P := fun i ↦ (hmemLp i).sub (memLp_const μ)
  have hintYc : ∀ i, Integrable (Yc i) P := fun i ↦ (hmemLpYc i).integrable one_le_two
  have hcentYc : ∀ i, ∫ ω, Yc i ω ∂P = 0 := fun i ↦ by
    have hval : ∫ ω, Yc i ω ∂P = ∫ ω, X i ω ∂P - μ := by
      simp only [hYc]
      rw [integral_sub ((hmemLp i).integrable one_le_two) (integrable_const μ), integral_const]
      simp
    rw [hval, (hident i).integral_eq, ← hμ, sub_self]
  set S : ℕ → Ω → ℝ := fun m ↦ ∑ j ∈ Finset.range m, Yc j with hS
  have hMart : Martingale S (natFiltLT Yc hYcmeas) P :=
    martingale_iidSum hYcmeas hindepYc hintYc hcentYc
  have hint2 : ∀ i, Integrable (fun ω ↦ Yc i ω ^ 2) P := fun i ↦
    (memLp_two_iff_integrable_sq (hYcmeas i).aestronglyMeasurable).mp (hmemLpYc i)
  have hmemLpS : ∀ m, MemLp (S m) 2 P := fun m ↦ memLp_finsetSum' _ fun j _ ↦ hmemLpYc j
  have hSmeas : ∀ m, Measurable (S m) := fun m ↦
    (hMart.stronglyAdapted m).measurable.mono ((natFiltLT Yc hYcmeas).le m) le_rfl
  have hΔ : ∀ n ω, S (n + 1) ω - S n ω = Yc n ω := fun n ω ↦ by
    simp only [hS, Finset.sum_apply, Finset.sum_range_succ]; ring
  have hM2 : ∀ n, Integrable (fun ω ↦ S n ω ^ 2) P := fun n ↦
    (memLp_two_iff_integrable_sq (hmemLpS n).aestronglyMeasurable).mp (hmemLpS n)
  have hd2 : ∀ n, Integrable (fun ω ↦ (S (n + 1) ω - S n ω) ^ 2) P := fun n ↦ by
    have he : (fun ω ↦ (S (n + 1) ω - S n ω) ^ 2) = fun ω ↦ Yc n ω ^ 2 := by
      funext ω; rw [hΔ n ω]
    rw [he]; exact hint2 n
  have hcross : ∀ a b, Integrable (fun ω ↦ S a ω * S b ω) P := fun a b ↦
    (hmemLpS a).integrable_mul (hmemLpS b)
  have hinc : ∀ n, ∫ ω, (S (n + 1) ω - S n ω) ^ 2 ∂P ≤ v := fun n ↦ by
    have he : (fun ω ↦ (S (n + 1) ω - S n ω) ^ 2) = fun ω ↦ (X n ω - μ) ^ 2 := by
      funext ω; rw [hΔ n ω]
    have hcomp : IdentDistrib (fun ω ↦ (X n ω - μ) ^ 2) (fun ω ↦ (X 0 ω - μ) ^ 2) P P :=
      (hident n).comp ((measurable_id.sub_const μ).pow_const 2)
    have hval : ∫ ω, (X n ω - μ) ^ 2 ∂P = v := by
      rw [hcomp.integral_eq, hvdef, variance_eq_integral (hmemLp 0).aemeasurable, ← hμ]
    rw [he]; exact hval.le
  -- The centered partial sum at `m` equals `(∑_{k<m} X_k) − m μ`.
  have hSeq : ∀ m ω, S m ω = (∑ k ∈ Finset.range m, X k ω) - (m : ℝ) * μ := fun m ω ↦ by
    simp only [hS, Finset.sum_apply, hYc, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  -- Base CLT along `c_n`: the law of `A_n = (√c_n)⁻¹ S(c_n)` converges to `𝒩(0, v)`.
  have hbase := tendsto_map_clt_comp hX2 hindep hident hc
  simp only [← hμ, ← hvdef] at hbase
  -- Scaling `R_n = √c_n · (√N_n)⁻¹ → 1` in probability.
  have hcr : Tendsto (fun n ↦ (c n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hc
  have hR1 : TendstoInMeasure P (fun n ω ↦ Real.sqrt (c n : ℝ) * (Real.sqrt (N n ω : ℝ))⁻¹)
      atTop (fun _ ↦ (1 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (measurable_const.mul
      (((measurable_of_countable _).comp (hNmeas n)).sqrt.inv)).aestronglyMeasurable) ?_
    filter_upwards [hreg] with ω hω
    have hcN : Tendsto (fun n ↦ (c n : ℝ) / (N n ω : ℝ)) atTop (𝓝 1) := by
      have hinv : Tendsto (fun n ↦ ((N n ω : ℝ) / (c n : ℝ))⁻¹) atTop (𝓝 1) := by
        simpa using hω.inv₀ one_ne_zero
      exact hinv.congr' (Filter.Eventually.of_forall fun n ↦ by rw [inv_div])
    have h2 : Tendsto (fun n ↦ Real.sqrt ((c n : ℝ) / (N n ω : ℝ))) atTop (𝓝 1) := by
      have := (Real.continuous_sqrt.tendsto 1).comp hcN
      rwa [Real.sqrt_one] at this
    refine h2.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    rw [Real.sqrt_div (Nat.cast_nonneg _), div_eq_mul_inv]
  -- Window remainder `E_n → 0` in probability.
  have hwindow := tendstoInMeasure_window hMart hM2 hd2 hcross hv0 hinc hNmeas hc hreg
  -- Measurability of the three assembled pieces.
  have hA_meas : ∀ n, AEMeasurable (fun ω ↦ (Real.sqrt (c n : ℝ))⁻¹ *
      (∑ k ∈ Finset.range (c n), X k ω - (c n : ℝ) * μ)) P := fun n ↦
    (measurable_const.mul
      ((Finset.measurable_sum _ fun k _ ↦ hXmeas k).sub measurable_const)).aemeasurable
  have hR_meas : ∀ n, AEMeasurable
      (fun ω ↦ Real.sqrt (c n : ℝ) * (Real.sqrt (N n ω : ℝ))⁻¹) P := fun n ↦
    (measurable_const.mul
      (((measurable_of_countable _).comp (hNmeas n)).sqrt.inv)).aemeasurable
  have hSNfun_meas : ∀ n, Measurable (fun ω ↦ S (N n ω) ω) := fun n ↦ by
    have heq : (fun ω ↦ S (N n ω) ω)
        = fun ω ↦ (∑ k ∈ Finset.range (N n ω), X k ω) - (N n ω : ℝ) * μ := by
      funext ω; exact hSeq (N n ω) ω
    rw [heq]
    exact (hSumMeas n).sub (((measurable_of_countable _).comp (hNmeas n)).mul measurable_const)
  have hE_meas : ∀ n, AEMeasurable
      (fun ω ↦ (Real.sqrt (N n ω : ℝ))⁻¹ * (S (N n ω) ω - S (c n) ω)) P := fun n ↦
    ((((measurable_of_countable _).comp (hNmeas n)).sqrt.inv).mul
      ((hSNfun_meas n).sub (hSmeas (c n)))).aemeasurable
  -- Multiplicative then additive Slutsky.
  have hmul := tendsto_map_mul_of_tendstoInMeasure_one hA_meas hR_meas hbase hR1
  have hadd := tendsto_map_add_of_tendstoInMeasure_zero
    (fun n ↦ (hA_meas n).mul (hR_meas n)) hE_meas hmul hwindow
  -- Identify the assembled process `A_n R_n + E_n` with the target `(√N_n)⁻¹ S(N_n)`.
  refine hadd.congr' ?_
  filter_upwards [hc.eventually_ge_atTop 1] with n hn
  apply Subtype.ext
  refine congrArg (P.map ·) ?_
  funext ω
  have hcn0 : Real.sqrt (c n : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hn)
  simp only [Pi.mul_apply]
  rw [show (∑ k ∈ Finset.range (c n), X k ω - (c n : ℝ) * μ) = S (c n) ω from (hSeq (c n) ω).symm,
    show (∑ k ∈ Finset.range (N n ω), X k ω - (N n ω : ℝ) * μ) = S (N n ω) ω from
      (hSeq (N n ω) ω).symm]
  field_simp
  ring

end AlphaRAR
