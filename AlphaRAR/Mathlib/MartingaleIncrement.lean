/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.StochasticOrder
import AlphaRAR.Mathlib.MartingaleMaximal
import AlphaRAR.Mathlib.IncrementControl

/-!
# `o_p` increment bounds for a martingale family

For a finite family `M` of square-integrable martingales with uniformly bounded increment second
moments, the Euclidean-norm increment `‖(M_{k,n} - M_{k,ℓ})_k‖` over a window `ℓ ≤ n` is
`o_p(1)·(n - ℓ) + o_p(√n)`. This is the probabilistic core of blueprint `lem:QM_increments`.

The argument fixes the dyadic window `L = ⌊√n⌋` and controls the increment by two maxima
(`vmaxSeq`, `wmaxSeq`) via the deterministic `norm_sub_le_increment_control`; the maxima are then
shown to be `o_p(1)` and `o_p(√n)` from the vector Doob maximal bounds (`mart_maximal_pi`,
`mart_maximal_dyadic_pi`) and Markov's inequality.

## Main results

* `AlphaRAR.isLittleOpOne_vmaxSeq`: `vmaxSeq = o_p(1)`.
* `AlphaRAR.isLittleOpOne_wmaxSeq_div_sqrt`: `wmaxSeq = o_p(√n)`.
* `AlphaRAR.norm_increment_le_vmaxSeq_wmaxSeq`: the pathwise increment-control bound.
-/

open MeasureTheory Filter Finset
open scoped ENNReal Topology

namespace AlphaRAR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **`o_p(1)` from a vanishing expectation bound.** If `Y n ≥ 0` a.e. with
`∫⁻ Y n ≤ ofReal (b n)` eventually and `b n → 0`, then `Y = o_p(1)`. -/
lemma isLittleOpOne_of_lintegral_le_tendsto {Y : ℕ → Ω → ℝ}
    (hYnn : ∀ n, 0 ≤ᵐ[μ] Y n) (hmeas : ∀ n, AEMeasurable (Y n) μ)
    {b : ℕ → ℝ} (hbound : ∀ᶠ n in atTop, ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ ≤ ENNReal.ofReal (b n))
    (hbtend : Tendsto b atTop (𝓝 0)) : IsLittleOpOne μ Y := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hstep : ∀ᶠ n in atTop, μ {ω | ε ≤ |Y n ω|} ≤ ENNReal.ofReal (b n) / ENNReal.ofReal ε := by
    filter_upwards [hbound] with n hbn
    have hmeasf : AEMeasurable (fun ω ↦ ENNReal.ofReal (Y n ω)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hmeas n)
    have hsub : {ω | ε ≤ |Y n ω|} ≤ᵐ[μ]
        {ω | ENNReal.ofReal ε ≤ ENNReal.ofReal (Y n ω)} := by
      filter_upwards [hYnn n] with ω hω hmem
      have hmem' : ε ≤ |Y n ω| := hmem
      have hω' : 0 ≤ Y n ω := hω
      change ENNReal.ofReal ε ≤ ENNReal.ofReal (Y n ω)
      rw [abs_of_nonneg hω'] at hmem'
      exact ENNReal.ofReal_le_ofReal hmem'
    calc μ {ω | ε ≤ |Y n ω|}
        ≤ μ {ω | ENNReal.ofReal ε ≤ ENNReal.ofReal (Y n ω)} := measure_mono_ae hsub
      _ ≤ (∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ) / ENNReal.ofReal ε :=
          meas_ge_le_lintegral_div hmeasf (ENNReal.ofReal_ne_zero_iff.mpr hε) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (b n) / ENNReal.ofReal ε := ENNReal.div_le_div_right hbn _
  have htend : Tendsto (fun n ↦ ENNReal.ofReal (b n) / ENNReal.ofReal ε) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ b n / ε) atTop (𝓝 0) := by simpa using hbtend.div_const ε
    have h2 : Tendsto (fun n ↦ ENNReal.ofReal (b n / ε)) atTop (𝓝 0) := by
      have hc := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h1
      rwa [ENNReal.ofReal_zero] at hc
    refine h2.congr (fun n ↦ ?_)
    rw [ENNReal.ofReal_div_of_pos hε]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
    (Eventually.of_forall (fun n ↦ zero_le)) hstep

/-- `Nat.sqrt n → ∞` as `n → ∞`, at the real level. -/
lemma tendsto_natCast_sqrt_atTop :
    Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ)) atTop atTop := by
  have hnat : Tendsto (fun n : ℕ ↦ Nat.sqrt n) atTop atTop := by
    refine tendsto_atTop_atTop.mpr (fun M ↦ ⟨M * M, fun n hn ↦ ?_⟩)
    exact Nat.le_sqrt.mpr hn
  exact tendsto_natCast_atTop_atTop.comp hnat

/-- `Nat.sqrt n / n → 0` as `n → ∞`. -/
lemma tendsto_natCast_sqrt_div_atTop :
    Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall (fun n ↦ by positivity)) ?_
    (g := fun n ↦ (Nat.sqrt n : ℝ)⁻¹) ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hsn : (0 : ℝ) < (Nat.sqrt n : ℝ) := by exact_mod_cast Nat.sqrt_pos.mpr hn
    rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n), inv_mul_eq_div, le_div_iff₀ hsn]
    exact_mod_cast Nat.sqrt_le n
  · exact tendsto_natCast_sqrt_atTop.inv_tendsto_atTop

/-- The Euclidean norm of `toLp v` is `√(∑ v_k²)`. -/
lemma norm_toLp_eq_sqrt {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ = Real.sqrt (∑ k, (v k) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  refine congrArg Real.sqrt (Finset.sum_congr rfl (fun k _ ↦ ?_))
  rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

section IncrementBounds

variable [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {ι : Type*} [Fintype ι]
  {M : ι → ℕ → Ω → ℝ}

/-- The scale-normalized backward-increment maximum over the "long" dyadic range, with the
window `L = ⌊√n⌋`. This is the `o_p(1)` factor in the increment control. -/
noncomputable def vmaxSeq (M : ι → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.Icc (Nat.sqrt n) n).sup' (Finset.nonempty_Icc.mpr (Nat.sqrt_le_self n))
    (fun m ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2) / (m : ℝ))

/-- The unnormalized backward-increment maximum over the "short" range `m ≤ ⌊√n⌋`. This is the
`o_p(√n)` term in the increment control. -/
noncomputable def wmaxSeq (M : ι → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (Nat.sqrt n + 1)).sup' nonempty_range_add_one
    (fun m ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2))

/-- **Pathwise increment control.** For `2 ≤ n` and `ℓ ≤ n`, the Euclidean norm of the increment
`Q_n - Q_ℓ` (with `Q_j = (M_{k,j})_k`) is bounded by `(n-ℓ)·vmaxSeq + wmaxSeq`. Instantiation of
`norm_sub_le_increment_control` at `E = EuclideanSpace ℝ ι` with window `L = ⌊√n⌋`. -/
lemma norm_increment_le_vmaxSeq_wmaxSeq (n : ℕ) (hn : 2 ≤ n) {ℓ : ℕ} (hℓ : ℓ ≤ n) (ω : Ω) :
    Real.sqrt (∑ k, (M k n ω - M k ℓ ω) ^ 2)
      ≤ ((n - ℓ : ℕ) : ℝ) * vmaxSeq M n ω + wmaxSeq M n ω := by
  set Q : ℕ → EuclideanSpace ℝ ι := fun j ↦ WithLp.toLp 2 (fun k ↦ M k j ω) with hQdef
  have hbridge : ∀ a b, ‖Q a - Q b‖ = Real.sqrt (∑ k, (M k a ω - M k b ω) ^ 2) := by
    intro a b
    rw [hQdef, ← WithLp.toLp_sub, norm_toLp_eq_sqrt]
    exact congrArg Real.sqrt (Finset.sum_congr rfl (fun k _ ↦ by rw [Pi.sub_apply]))
  have hL1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  have hLn : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
  have hic := norm_sub_le_increment_control Q hℓ hL1 hLn
  rw [hbridge n ℓ] at hic
  refine hic.trans (add_le_add
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) ?_)
  · -- Icc-sup' equals vmaxSeq
    apply le_of_eq
    unfold vmaxSeq
    exact Finset.sup'_congr _ rfl (fun m _ ↦ by rw [hbridge n (n - m)])
  · -- range-sup' ≤ wmaxSeq
    calc (Finset.range (Nat.sqrt n)).sup' _ (fun m ↦ ‖Q n - Q (n - m)‖)
        = (Finset.range (Nat.sqrt n)).sup' _
            (fun m ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2)) :=
          Finset.sup'_congr _ rfl (fun m _ ↦ hbridge n (n - m))
      _ ≤ wmaxSeq M n ω := by
          refine Finset.sup'_le _ _ (fun m hm ↦ ?_)
          unfold wmaxSeq
          exact Finset.le_sup' (f := fun m ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2))
            (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hm)))

variable (hM : ∀ k, Martingale (M k) ℱ μ)
  (hM2 : ∀ k n, Integrable (fun ω ↦ M k n ω ^ 2) μ)
  (hd2 : ∀ k n, Integrable (fun ω ↦ (M k (n + 1) ω - M k n ω) ^ 2) μ)
  (hcross : ∀ k a b, Integrable (fun ω ↦ M k a ω * M k b ω) μ)
  {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hinc : ∀ k n, ∫ ω, (M k (n + 1) ω - M k n ω) ^ 2 ∂μ ≤ C₀)

include hM hC₀ hinc hM2 hd2 hcross in
/-- **The long-range normalized increment maximum is `o_p(1)`.** -/
lemma isLittleOpOne_vmaxSeq : IsLittleOpOne μ (vmaxSeq M) := by
  have hMmeas : ∀ k j, Measurable (M k j) := fun k j ↦
    ((hM k).stronglyAdapted j).measurable.mono (ℱ.le j) le_rfl
  have hgmeas : ∀ n m, Measurable (fun ω ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2)) :=
    fun n m ↦ Real.continuous_sqrt.measurable.comp (Finset.measurable_sum Finset.univ
      (fun k _ ↦ ((hMmeas k n).sub (hMmeas k (n - m))).pow_const 2))
  set b : ℕ → ℝ :=
    fun n ↦ (Fintype.card ι : ℝ) * (32 * Real.sqrt (C₀ / (Nat.sqrt n : ℝ))) with hbdef
  refine isLittleOpOne_of_lintegral_le_tendsto (b := b) (fun n ↦ ?_) (fun n ↦ ?_) ?_ ?_
  · -- 0 ≤ vmaxSeq
    exact ae_of_all _ (fun ω ↦ le_trans (by positivity)
      (Finset.le_sup' (f := fun m ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2) / (m : ℝ))
        (Finset.mem_Icc.mpr ⟨le_rfl, Nat.sqrt_le_self n⟩)))
  · -- measurable vmaxSeq n
    unfold vmaxSeq
    rw [show (fun ω ↦ (Finset.Icc (Nat.sqrt n) n).sup'
            (Finset.nonempty_Icc.mpr (Nat.sqrt_le_self n))
          (fun m ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2) / (m : ℝ)))
        = (Finset.Icc (Nat.sqrt n) n).sup' (Finset.nonempty_Icc.mpr (Nat.sqrt_le_self n))
          (fun m ω ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2) / (m : ℝ)) from by
        ext ω; rw [Finset.sup'_apply]]
    exact (Finset.measurable_sup' _ (fun m _ ↦ (hgmeas n m).div_const _)).aemeasurable
  · -- eventual lintegral bound
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact mart_maximal_dyadic_pi M hM hM2 hd2 hcross hC₀ hinc (Nat.sqrt_pos.mpr hn)
      (Nat.sqrt_le_self n)
  · -- b n → 0
    rw [hbdef]
    have hdiv : Tendsto (fun n ↦ C₀ / (Nat.sqrt n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_natCast_sqrt_atTop.inv_tendsto_atTop).const_mul C₀
    have hsqrt : Tendsto (fun n ↦ Real.sqrt (C₀ / (Nat.sqrt n : ℝ))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hdiv
      rwa [Real.sqrt_zero] at this
    have h1 := (hsqrt.const_mul (32 : ℝ)).const_mul (Fintype.card ι : ℝ)
    simpa using h1

include hM hC₀ hinc hM2 hd2 hcross in
/-- **The short-range increment maximum is `o_p(√n)`.** -/
lemma isLittleOpOne_wmaxSeq_div_sqrt :
    IsLittleOpOne μ (fun n ω ↦ wmaxSeq M n ω / Real.sqrt n) := by
  have hMmeas : ∀ k j, Measurable (M k j) := fun k j ↦
    ((hM k).stronglyAdapted j).measurable.mono (ℱ.le j) le_rfl
  have hgmeas : ∀ n m, Measurable (fun ω ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2)) :=
    fun n m ↦ Real.continuous_sqrt.measurable.comp (Finset.measurable_sum Finset.univ
      (fun k _ ↦ ((hMmeas k n).sub (hMmeas k (n - m))).pow_const 2))
  have hwmeasReal : ∀ n, Measurable (fun ω ↦ wmaxSeq M n ω) := fun n ↦ by
    unfold wmaxSeq
    exact Finset.measurable_range_sup'' (fun m _ ↦ hgmeas n m)
  have hwmeas : ∀ n, Measurable (fun ω ↦ ENNReal.ofReal (wmaxSeq M n ω)) := fun n ↦
    (hwmeasReal n).ennreal_ofReal
  set b : ℕ → ℝ :=
    fun n ↦ (1 / Real.sqrt n) * ((Fintype.card ι : ℝ) * (4 * Real.sqrt (C₀ * (Nat.sqrt n : ℝ))))
    with hbdef
  refine isLittleOpOne_of_lintegral_le_tendsto (b := b) (fun n ↦ ?_) (fun n ↦ ?_) ?_ ?_
  · -- 0 ≤ wmaxSeq / √n
    refine ae_of_all _ (fun ω ↦ div_nonneg ?_ (Real.sqrt_nonneg _))
    exact le_trans (Real.sqrt_nonneg _)
      (Finset.le_sup' (f := fun m ↦ Real.sqrt (∑ k, (M k n ω - M k (n - m) ω) ^ 2))
        (Finset.mem_range.mpr (Nat.succ_pos _)))
  · -- measurable
    exact ((hwmeasReal n).div_const _).aemeasurable
  · -- eventual bound
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hmp := mart_maximal_pi M hM hM2 hd2 hcross hinc (L := Nat.sqrt n) (n := n)
      (Nat.sqrt_le_self n)
    calc ∫⁻ ω, ENNReal.ofReal (wmaxSeq M n ω / Real.sqrt n) ∂μ
        = ENNReal.ofReal (1 / Real.sqrt n) * ∫⁻ ω, ENNReal.ofReal (wmaxSeq M n ω) ∂μ := by
          rw [← lintegral_const_mul _ (hwmeas n)]
          refine lintegral_congr (fun ω ↦ ?_)
          rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_eq_div]
      _ ≤ ENNReal.ofReal (1 / Real.sqrt n)
            * ENNReal.ofReal ((Fintype.card ι : ℝ) * (4 * Real.sqrt (C₀ * (Nat.sqrt n : ℝ)))) := by
          gcongr
          exact hmp
      _ = ENNReal.ofReal (b n) := by rw [hbdef, ← ENNReal.ofReal_mul (by positivity)]
  · -- b n → 0
    have haux : Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) :=
      tendsto_natCast_sqrt_div_atTop
    have hin : Tendsto (fun n : ℕ ↦ C₀ * ((Nat.sqrt n : ℝ) / n)) atTop (𝓝 0) := by
      simpa using haux.const_mul C₀
    have hsq : Tendsto (fun n : ℕ ↦ Real.sqrt (C₀ * ((Nat.sqrt n : ℝ) / n))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hin
      rwa [Real.sqrt_zero] at this
    have hgoal : Tendsto
        (fun n : ℕ ↦ (Fintype.card ι : ℝ) * (4 * Real.sqrt (C₀ * ((Nat.sqrt n : ℝ) / n))))
        atTop (𝓝 0) := by simpa using (hsq.const_mul (4 : ℝ)).const_mul (Fintype.card ι : ℝ)
    refine hgoal.congr' ?_
    filter_upwards with n
    rw [hbdef, show C₀ * ((Nat.sqrt n : ℝ) / n) = (C₀ * (Nat.sqrt n : ℝ)) / n by ring,
      Real.sqrt_div (mul_nonneg hC₀ (Nat.cast_nonneg _))]
    ring

end IncrementBounds

section Scalar

variable [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {N : ℕ → Ω → ℝ}

/-- **The running maximum of a square-integrable martingale is `O_p(√n)`.** For a martingale `N`
with `N 0 = 0` and increment second moments `≤ σ²`, `max_{m ≤ n} |N_m| = O_p(√n)`. Combines the
Doob `L²` maximal bound (`lintegral_sup'_abs_le_two_mul_sqrt`) with `E[N_n²] ≤ σ²n` and Markov. -/
lemma isBigOpOne_sup'_abs_div_sqrt (hN : Martingale N ℱ μ)
    (hN2 : ∀ n, Integrable (fun ω ↦ N n ω ^ 2) μ) (hN0 : N 0 =ᵐ[μ] 0)
    (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    (hd2 : ∀ n, Integrable (fun ω ↦ (N (n + 1) ω - N n ω) ^ 2) μ)
    (hprod : ∀ n, Integrable (N n * (N (n + 1) - N n)) μ)
    (hinc : ∀ n, ∫ ω, (N (n + 1) ω - N n ω) ^ 2 ∂μ ≤ σ2) :
    IsBigOpOne μ (fun n ω ↦ (Finset.range (n + 1)).sup' nonempty_range_add_one
      (fun m ↦ |N m ω|) / Real.sqrt n) := by
  have hgrow := integral_sq_le_of_increment_bound hN hN2 hN0 σ2 hd2 hprod hinc
  have hNmeas : ∀ k, Measurable (N k) := fun k ↦
    (hN.stronglyAdapted k).measurable.mono (ℱ.le k) le_rfl
  set S : ℕ → Ω → ℝ := fun n ω ↦ (Finset.range (n + 1)).sup' nonempty_range_add_one
    (fun m ↦ |N m ω|) with hSdef
  have hSnn : ∀ n ω, 0 ≤ S n ω := fun n ω ↦ by
    rw [hSdef]
    exact le_trans (abs_nonneg (N 0 ω))
      (Finset.le_sup' (fun m ↦ |N m ω|) (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hSmeas : ∀ n, Measurable (S n) := fun n ↦
    Finset.measurable_range_sup'' (fun m _ ↦ continuous_abs.measurable.comp (hNmeas m))
  set v : ℕ → ℝ := fun n ↦ Real.sqrt (max (n : ℝ) 1) with hv
  have hvpos : ∀ n, 0 < v n := fun n ↦
    Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal |S n ω| ∂μ
      ≤ ENNReal.ofReal (2 * Real.sqrt σ2 * v n) := by
    intro n
    have hle := lintegral_sup'_abs_le_two_mul_sqrt hN hN2 hd2 hprod n
    rw [show (fun ω ↦ ENNReal.ofReal |S n ω|) = fun ω ↦ ENNReal.ofReal (S n ω) from by
      funext ω; rw [abs_of_nonneg (hSnn n ω)]]
    refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Real.sqrt (∫ ω, N n ω ^ 2 ∂μ) ≤ Real.sqrt (σ2 * n) := Real.sqrt_le_sqrt (hgrow n)
    have h2 : Real.sqrt (σ2 * n) ≤ Real.sqrt σ2 * v n := by
      rw [Real.sqrt_mul hσ2]
      exact mul_le_mul_of_nonneg_left
        (by rw [hv]; exact Real.sqrt_le_sqrt (le_max_left _ _)) (Real.sqrt_nonneg _)
    calc 2 * Real.sqrt (∫ ω, N n ω ^ 2 ∂μ)
        ≤ 2 * (Real.sqrt σ2 * v n) := by gcongr; exact h1.trans h2
      _ = 2 * Real.sqrt σ2 * v n := by ring
  have hOp : IsBigOpOne μ (fun n ω ↦ S n ω / v n) :=
    isBigOpOne_of_lintegral_le S v (2 * Real.sqrt σ2) hvpos (by positivity)
      (fun n ↦ (hSmeas n).aemeasurable) hbound
  refine IsBigOpOne.congr (fun n ↦ ?_) hOp
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    filter_upwards [hN0] with ω hω
    simp only [Pi.zero_apply] at hω
    have hS0 : S 0 ω = 0 := by
      have he : S 0 ω = |N 0 ω| := by
        simp only [hSdef, zero_add, Finset.range_one, Finset.sup'_singleton]
      rw [he, hω, abs_zero]
    rw [hS0]; simp
  · have hvn : v n = Real.sqrt n := by
      change Real.sqrt (max (n : ℝ) 1) = Real.sqrt n
      rw [max_eq_left (by exact_mod_cast hn1 : (1 : ℝ) ≤ n)]
    filter_upwards with ω; rw [hvn]

/-- **Scalar increment maxima are `o_p(1)` and `o_p(√n)` for a bounded-increment martingale.**
For a martingale `N` with `N 0 = 0` and `|ΔN| ≤ c` a.e., the increment maxima of the singleton
family `fun _ : Unit ↦ N` are `o_p(1)` and `o_p(√n)`. Provides the `M`-side of blueprint
`lem:QM_increments` (the assignment martingale has `|ΔM| ≤ 1`). -/
lemma qm_increments_of_bdd (hN : Martingale N ℱ μ) (hN0 : N 0 =ᵐ[μ] 0) {c : ℝ} (hc : 0 ≤ c)
    (hΔ : ∀ n, ∀ᵐ ω ∂μ, |N (n + 1) ω - N n ω| ≤ c) :
    IsLittleOpOne μ (vmaxSeq (fun _ : Unit ↦ N)) ∧
      IsLittleOpOne μ (fun n ω ↦ wmaxSeq (fun _ : Unit ↦ N) n ω / Real.sqrt n) := by
  have hmeasN : ∀ n, AEMeasurable (N n) μ := fun n ↦
    ((hN.stronglyMeasurable n).mono (ℱ.le n)).measurable.aemeasurable
  have bdd_int : ∀ (f : Ω → ℝ) (B : ℝ), AEStronglyMeasurable f μ →
      (∀ᵐ ω ∂μ, |f ω| ≤ B) → Integrable f μ := fun f B hf hb ↦
    (integrable_const B).mono' hf (by filter_upwards [hb] with ω h; rwa [Real.norm_eq_abs])
  have hbdd : ∀ n, ∀ᵐ ω ∂μ, |N n ω| ≤ n * c := by
    intro n
    filter_upwards [ae_all_iff.mpr hΔ, hN0] with ω hΔω hN0ω
    simp only [Pi.zero_apply] at hN0ω
    have htel : (∑ k ∈ Finset.range n, (N (k + 1) ω - N k ω)) = N n ω := by
      rw [Finset.sum_range_sub (fun k ↦ N k ω) n, hN0ω, sub_zero]
    calc |N n ω| = |∑ k ∈ Finset.range n, (N (k + 1) ω - N k ω)| := by rw [htel]
      _ ≤ ∑ k ∈ Finset.range n, |N (k + 1) ω - N k ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, c := Finset.sum_le_sum fun k _ ↦ hΔω k
      _ = n * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM2 : ∀ n, Integrable (fun ω ↦ N n ω ^ 2) μ := fun n ↦
    bdd_int _ (((n : ℝ) * c) ^ 2) ((hmeasN n).pow_const 2).aestronglyMeasurable
      (by filter_upwards [hbdd n] with ω hb
          rw [abs_of_nonneg (sq_nonneg _)]
          exact sq_le_sq' (neg_le_of_abs_le hb) (le_of_abs_le hb))
  have hd2 : ∀ n, Integrable (fun ω ↦ (N (n + 1) ω - N n ω) ^ 2) μ := fun n ↦
    bdd_int _ (c ^ 2) (((hmeasN (n + 1)).sub (hmeasN n)).pow_const 2).aestronglyMeasurable
      (by filter_upwards [hΔ n] with ω hb
          rw [abs_of_nonneg (sq_nonneg _)]
          exact sq_le_sq' (neg_le_of_abs_le hb) (le_of_abs_le hb))
  have hcross : ∀ a b, Integrable (fun ω ↦ N a ω * N b ω) μ := fun a b ↦ by
    refine bdd_int _ ((a : ℝ) * c * ((b : ℝ) * c))
      ((hmeasN a).mul (hmeasN b)).aestronglyMeasurable ?_
    filter_upwards [hbdd a, hbdd b] with ω hba hbb
    rw [abs_mul]
    exact mul_le_mul hba hbb (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg a) hc)
  have hinc : ∀ n, ∫ ω, (N (n + 1) ω - N n ω) ^ 2 ∂μ ≤ c ^ 2 := fun n ↦ by
    have hb : (fun ω ↦ (N (n + 1) ω - N n ω) ^ 2) ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
      filter_upwards [hΔ n] with ω h
      exact sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
    calc ∫ ω, (N (n + 1) ω - N n ω) ^ 2 ∂μ
        ≤ ∫ _, c ^ 2 ∂μ := integral_mono_ae (hd2 n) (integrable_const _) hb
      _ = c ^ 2 := by simp
  exact ⟨isLittleOpOne_vmaxSeq (M := fun _ : Unit ↦ N) (fun _ ↦ hN) (fun _ ↦ hM2)
      (fun _ ↦ hd2) (fun _ ↦ hcross) (sq_nonneg c) (fun _ ↦ hinc),
    isLittleOpOne_wmaxSeq_div_sqrt (M := fun _ : Unit ↦ N) (fun _ ↦ hN) (fun _ ↦ hM2)
      (fun _ ↦ hd2) (fun _ ↦ hcross) (sq_nonneg c) (fun _ ↦ hinc)⟩

end Scalar

end AlphaRAR
