/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib
import AlphaRAR.Probability.QuadraticVariation

/-!
# Exponential supermartingale for the law of the iterated logarithm

For a martingale `M` with `M 0 = 0` and increments bounded by `c`, the process
`Z_n(θ) = exp(θ M_n - θ² ⟨M⟩_n)` is a supermartingale whenever `|θ| c ≤ 1`, where
`⟨M⟩` is the predictable quadratic variation. This is the exponential/Freedman
supermartingale, the starting point of the one-sided law of the iterated logarithm
(blueprint chapter `chap:pre_lil`).

The key one-step estimate is the conditional moment-generating-function bound
`μ[exp(θ ΔM_i) | ℱ_i] ≤ 1 + θ² μ[(ΔM_i)² | ℱ_i]`, obtained from the elementary
inequality `eˣ ≤ 1 + x + x²` (valid for `|x| ≤ 1`) together with the martingale
property `μ[ΔM_i | ℱ_i] = 0`.

## Main results

* `AlphaRAR.condExp_exp_increment_le`: the conditional MGF bound.
* `AlphaRAR.predQuadVar_nonneg`: the predictable quadratic variation is nonnegative.
* `AlphaRAR.supermartingale_expProcess`: `Z_n(θ)` is a supermartingale
  (blueprint `lem:lil_exp_supermart`).
-/

open MeasureTheory Filter

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- **The predictable quadratic variation is nonnegative.** Since `⟨M⟩ 0 = 0` and `⟨M⟩` is
nondecreasing (its increments are conditional second moments), `0 ≤ ⟨M⟩ n` a.e. -/
theorem predQuadVar_nonneg [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hd2 : ∀ n, Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ) (n : ℕ) :
    0 ≤ᵐ[μ] predQuadVar M ℱ μ n := by
  induction n with
  | zero => rw [predQuadVar_zero]
  | succ k ih =>
    filter_upwards [ih, predQuadVar_le_succ hM k (hd2 k) (hprod k)] with ω hik hstep
    simp only [Pi.zero_apply] at hik ⊢
    exact le_trans hik hstep

/-- **Conditional MGF bound for a bounded martingale increment.**
If `|ΔM_i| ≤ c` a.e. and `|θ| c ≤ 1`, then
`μ[exp(θ ΔM_i) | ℱ_i] ≤ 1 + θ² (⟨M⟩_{i+1} - ⟨M⟩_i)` a.e.
The proof uses `eˣ ≤ 1 + x + x²` for `|x| ≤ 1`, monotonicity of conditional expectation, the
martingale property `μ[ΔM_i | ℱ_i] = 0`, and `μ[(ΔM_i)² | ℱ_i] = ⟨M⟩_{i+1} - ⟨M⟩_i`
(`predQuadVar_succ_sub_eq`). -/
theorem condExp_exp_increment_le [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ) {c θ : ℝ}
    (hθ : |θ| * c ≤ 1) (i : ℕ) (hb : ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hd2 : Integrable (fun ω ↦ (M (i + 1) ω - M i ω) ^ 2) μ)
    (hprod : Integrable (M i * (M (i + 1) - M i)) μ) :
    μ[fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω)) | ℱ i]
      ≤ᵐ[μ] fun ω ↦ 1 + θ ^ 2 * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
  have haesm_d : AEStronglyMeasurable (fun ω ↦ M (i + 1) ω - M i ω) μ :=
    (((hM.stronglyMeasurable (i + 1)).mono (ℱ.le _)).sub
      ((hM.stronglyMeasurable i).mono (ℱ.le _))).aestronglyMeasurable
  -- Pointwise quadratic bound `exp(θ ΔM) ≤ 1 + θ ΔM + θ² ΔM²`.
  have hptwise : (fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω)))
      ≤ᵐ[μ] fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω) + θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 := by
    filter_upwards [hb] with ω hbω
    have hx : |θ * (M (i + 1) ω - M i ω)| ≤ 1 := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
    have h := le_of_abs_le (Real.abs_exp_sub_one_sub_id_le hx)
    have heq : (θ * (M (i + 1) ω - M i ω)) ^ 2 = θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 := by ring
    linarith [h, heq]
  -- The quadratic bound and the exponential are integrable.
  have hint_exp : Integrable (fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω))) μ := by
    refine (MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
      (haesm_d.const_mul θ)) (Real.exp 1) ?_).integrable le_rfl
    filter_upwards [hb] with ω hbω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
  have hint_lin : Integrable (fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω)) μ :=
    (integrable_const 1).add (((hM.integrable (i + 1)).sub (hM.integrable i)).const_mul θ)
  have hint_quad : Integrable (fun ω ↦ θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2) μ :=
    hd2.const_mul _
  have hint_q : Integrable (fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
      + θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2) μ := hint_lin.add hint_quad
  -- Conditional expectation of the increment is `0`.
  have hd0 : μ[fun ω ↦ M (i + 1) ω - M i ω | ℱ i] =ᵐ[μ] 0 := by
    have h3 : μ[M i | ℱ i] = M i :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hM.stronglyMeasurable i) (hM.integrable i)
    have h1 : μ[fun ω ↦ M (i + 1) ω - M i ω | ℱ i] =ᵐ[μ] μ[M (i + 1) | ℱ i] - μ[M i | ℱ i] :=
      condExp_sub (hM.integrable (i + 1)) (hM.integrable i) _
    rw [h3] at h1
    have h2 : μ[M (i + 1) | ℱ i] =ᵐ[μ] M i := hM.condExp_ae_eq (Nat.le_succ i)
    filter_upwards [h1, h2] with ω e1 e2
    simp only [Pi.sub_apply, Pi.zero_apply, e1, e2, sub_self]
  -- Conditional expectation of the squared increment is `⟨M⟩_{i+1} - ⟨M⟩_i`.
  have hd2eq : μ[fun ω ↦ (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
      =ᵐ[μ] fun ω ↦ predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω :=
    (predQuadVar_succ_sub_eq hM i hd2 hprod).symm
  -- Conditional expectation of the quadratic bound.
  have hcond_q : μ[fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
      + θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
      =ᵐ[μ] fun ω ↦ 1 + θ ^ 2 * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
    have hlin : μ[fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω) | ℱ i] =ᵐ[μ] fun _ ↦ 1 := by
      have hs : μ[fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω) | ℱ i]
          =ᵐ[μ] μ[fun _ ↦ (1 : ℝ) | ℱ i]
            + μ[fun ω ↦ θ * (M (i + 1) ω - M i ω) | ℱ i] :=
        condExp_add (integrable_const 1)
          (((hM.integrable (i + 1)).sub (hM.integrable i)).const_mul θ) _
      rw [condExp_const (ℱ.le i)] at hs
      have hsmul : μ[fun ω ↦ θ * (M (i + 1) ω - M i ω) | ℱ i]
          =ᵐ[μ] θ • μ[fun ω ↦ M (i + 1) ω - M i ω | ℱ i] := condExp_smul θ _ _
      filter_upwards [hs, hsmul, hd0] with ω es esm ed0
      simp only [es, Pi.add_apply, esm, Pi.smul_apply, ed0, Pi.zero_apply, smul_zero, add_zero]
    have hquad : μ[fun ω ↦ θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
        =ᵐ[μ] fun ω ↦ θ ^ 2 * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
      have hsmul : μ[fun ω ↦ θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
          =ᵐ[μ] θ ^ 2 • μ[fun ω ↦ (M (i + 1) ω - M i ω) ^ 2 | ℱ i] := condExp_smul (θ ^ 2) _ _
      filter_upwards [hsmul, hd2eq] with ω esm ed2
      rw [esm, Pi.smul_apply, ed2, smul_eq_mul]
    have hadd : μ[fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
        + θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
        =ᵐ[μ] μ[fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω) | ℱ i]
          + μ[fun ω ↦ θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i] :=
      condExp_add hint_lin hint_quad _
    filter_upwards [hadd, hlin, hquad] with ω ea el eq
    rw [ea, Pi.add_apply, el, eq]
  -- Combine monotonicity of conditional expectation with the pointwise bound.
  exact (condExp_mono hint_exp hint_q hptwise).trans hcond_q.le

/-- The **exponential process** `Z_n(θ) = exp(θ M_n - θ² ⟨M⟩_n)`
(blueprint `lem:lil_exp_supermart`). -/
noncomputable def expProcess (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) (θ : ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω ↦ Real.exp (θ * M n ω - θ ^ 2 * predQuadVar M ℱ μ n ω)

/-- **The exponential process is a supermartingale** (blueprint `lem:lil_exp_supermart`).
For a martingale `M` with `M 0 = 0`, square-integrable, with increments bounded by `c`, and for
`|θ| c ≤ 1`, the process `Z_n(θ) = exp(θ M_n - θ² ⟨M⟩_n)` is a supermartingale.
The one-step bound is `μ[Z_{i+1} | ℱ_i] = Z_i e^{-θ² Δ⟨M⟩_i} μ[e^{θ ΔM_i} | ℱ_i]
≤ Z_i e^{-θ² Δ⟨M⟩_i}(1 + θ² Δ⟨M⟩_i) ≤ Z_i`, using `condExp_exp_increment_le` and `1 + y ≤ eʸ`. -/
theorem supermartingale_expProcess [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c θ : ℝ} (hθ : |θ| * c ≤ 1)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    Supermartingale (expProcess M ℱ μ θ) ℱ μ := by
  classical
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  -- Increments and values are `L²`, giving the side conditions for the quadratic-variation lemmas.
  have haesm_d : ∀ i, AEStronglyMeasurable (fun ω ↦ M (i + 1) ω - M i ω) μ := fun i ↦
    (((hM.stronglyMeasurable (i + 1)).mono (ℱ.le _)).sub
      ((hM.stronglyMeasurable i).mono (ℱ.le _))).aestronglyMeasurable
  have hdmem : ∀ i, MemLp (fun ω ↦ M (i + 1) ω - M i ω) 2 μ := fun i ↦
    MemLp.of_bound (haesm_d i) c (by filter_upwards [hb i] with ω h; rwa [Real.norm_eq_abs])
  have hMmem : ∀ n, MemLp (M n) 2 μ := fun n ↦
    (memLp_two_iff_integrable_sq ((hM.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable).mpr
      (hM2 n)
  have hd2 : ∀ i, Integrable (fun ω ↦ (M (i + 1) ω - M i ω) ^ 2) μ :=
    fun i ↦ (hdmem i).integrable_sq
  have hprod : ∀ i, Integrable (M i * (M (i + 1) - M i)) μ := fun i ↦
    (hMmem i).integrable_mul ((hMmem (i + 1)).sub (hMmem i))
  -- A.e. bound `|M n| ≤ n c` from `M 0 = 0` and bounded increments.
  have hMn : ∀ n, ∀ᵐ ω ∂μ, |M n ω| ≤ n * c := by
    intro n
    filter_upwards [ae_all_iff.mpr hb, hM0] with ω hball h0
    simp only [Pi.zero_apply] at h0
    have htel : (∑ j ∈ Finset.range n, (M (j + 1) ω - M j ω)) = M n ω := by
      rw [Finset.sum_range_sub (fun j ↦ M j ω) n, h0, sub_zero]
    rw [← htel]
    calc |∑ j ∈ Finset.range n, (M (j + 1) ω - M j ω)|
        ≤ ∑ j ∈ Finset.range n, |M (j + 1) ω - M j ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, c := Finset.sum_le_sum fun j _ ↦ hball j
      _ = n * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Measurability of `θ M n - θ² ⟨M⟩ n` with respect to `ℱ n`.
  have hinner : ∀ n, StronglyMeasurable[ℱ n]
      (fun ω ↦ θ * M n ω - θ ^ 2 * predQuadVar M ℱ μ n ω) := fun n ↦
    ((hM.stronglyMeasurable n).const_mul θ).sub
      ((stronglyAdapted_predictablePart' (f := fun k ↦ M k ^ 2) n).const_mul (θ ^ 2))
  -- `Z n` is measurable, and `0 ≤ Z n ≤ exp(|θ| (n c))`, hence integrable.
  have hZaesm : ∀ n, AEStronglyMeasurable (expProcess M ℱ μ θ n) μ := fun n ↦
    ((Real.continuous_exp.comp_stronglyMeasurable (hinner n)).mono (ℱ.le n)).aestronglyMeasurable
  have hZbd : ∀ n, ∀ᵐ ω ∂μ, ‖expProcess M ℱ μ θ n ω‖ ≤ Real.exp (|θ| * (n * c)) := by
    intro n
    filter_upwards [hMn n, predQuadVar_nonneg hM hd2 hprod n] with ω hMnω hqvω
    change ‖Real.exp (θ * M n ω - θ ^ 2 * predQuadVar M ℱ μ n ω)‖ ≤ _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    simp only [Pi.zero_apply] at hqvω
    have h1 : θ * M n ω ≤ |θ| * (n * c) := by
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hMnω (abs_nonneg _)
    nlinarith [mul_nonneg (sq_nonneg θ) hqvω]
  have hZint_n : ∀ n, Integrable (expProcess M ℱ μ θ n) μ := fun n ↦
    (MemLp.of_bound (hZaesm n) _ (hZbd n)).integrable le_rfl
  refine supermartingale_nat (fun n ↦ Real.continuous_exp.comp_stronglyMeasurable (hinner n))
    hZint_n (fun i ↦ ?_)
  · -- One-step supermartingale inequality.
    have hfac_meas : StronglyMeasurable[ℱ i]
        (fun ω ↦ Real.exp (θ * M i ω - θ ^ 2 * predQuadVar M ℱ μ i ω)
          * Real.exp (-(θ ^ 2 * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)))) :=
      (Real.continuous_exp.comp_stronglyMeasurable (hinner i)).mul
        (Real.continuous_exp.comp_stronglyMeasurable
          (((stronglyAdapted_predictablePart (f := fun k ↦ M k ^ 2) i).sub
            (stronglyAdapted_predictablePart' (f := fun k ↦ M k ^ 2) i)).const_mul (θ ^ 2)).neg)
    -- `Z_{i+1} = factor · exp(θ ΔM_i)` and `factor · exp(θ² Δ⟨M⟩_i) = Z_i`.
    set factor := fun ω ↦ Real.exp (θ * M i ω - θ ^ 2 * predQuadVar M ℱ μ i ω)
      * Real.exp (-(θ ^ 2 * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω))) with hfac
    have hZfac : expProcess M ℱ μ θ (i + 1)
        = fun ω ↦ factor ω * Real.exp (θ * (M (i + 1) ω - M i ω)) := by
      funext ω
      simp only [expProcess, hfac, ← Real.exp_add]
      congr 1
      ring
    have hint_exp : Integrable (fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω))) μ := by
      refine (MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
        ((haesm_d i).const_mul θ)) (Real.exp 1) ?_).integrable le_rfl
      filter_upwards [hb i] with ω hbω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
    have hZint : Integrable (fun ω ↦ factor ω * Real.exp (θ * (M (i + 1) ω - M i ω))) μ := by
      rw [← hZfac]; exact hZint_n (i + 1)
    -- Pull out the `ℱ_i`-measurable factor, then apply the MGF bound.
    have hpull : μ[expProcess M ℱ μ θ (i + 1) | ℱ i]
        =ᵐ[μ] fun ω ↦ factor ω * μ[fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω)) | ℱ i] ω := by
      rw [hZfac]
      exact condExp_mul_of_stronglyMeasurable_left hfac_meas hZint hint_exp
    have hmgf := condExp_exp_increment_le hM hθ i (hb i) (hd2 i) (hprod i)
    have hfac_nonneg : ∀ ω, 0 ≤ factor ω := fun ω ↦ by
      rw [hfac]; positivity
    filter_upwards [hpull, hmgf] with ω hp hm
    rw [hp]
    -- `factor · μ[e^{θΔM}|ℱ] ≤ factor·(1+θ²Δqv) ≤ factor·e^{θ²Δqv} = Z_i`.
    calc factor ω * μ[fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω)) | ℱ i] ω
        ≤ factor ω * (1 + θ ^ 2 * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)) :=
          mul_le_mul_of_nonneg_left hm (hfac_nonneg ω)
      _ ≤ factor ω
          * Real.exp (θ ^ 2 * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hfac_nonneg ω)
          have hle := Real.add_one_le_exp
            (θ ^ 2 * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω))
          linarith
      _ = expProcess M ℱ μ θ i ω := by
          simp only [expProcess, hfac, ← Real.exp_add]
          congr 1
          ring

open Finset in
/-- **Ville's maximal inequality** for a nonnegative supermartingale. If `Z ≥ 0` is a
supermartingale, then `ε · μ{ω : ε ≤ maxₖ≤ₙ Z_k ω} ≤ E[Z_0]`. Mathlib has Doob's maximal
inequality for submartingales but not this supermartingale version, which controls the running
maximum by the *initial* value; the proof stops `Z` at the first time it reaches `ε` and applies
the optional stopping theorem to the submartingale `-Z`. -/
theorem smul_measure_sup_le_integral_zero [IsFiniteMeasure μ] {Z : ℕ → Ω → ℝ}
    (hZ : Supermartingale Z ℱ μ) (hnonneg : 0 ≤ Z) {ε : ℝ≥0} (n : ℕ) :
    ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ Z k ω}
      ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂μ) := by
  classical
  set s := {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ Z k ω} with hs_def
  set τ : Ω → WithTop ℕ := fun ω ↦ (hittingBtwn Z {y : ℝ | (ε : ℝ) ≤ y} 0 n ω : ℕ) with hτ_def
  have hτ_stop : IsStoppingTime ℱ τ :=
    hZ.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτ_le : ∀ ω, τ ω ≤ (n : WithTop ℕ) := fun ω ↦ by
    simp only [hτ_def]; exact WithTop.coe_le_coe.mpr (hittingBtwn_le ω)
  have hsv_int : Integrable (stoppedValue Z τ) μ := by
    have h := (hZ.neg).integrable_stoppedValue hτ_stop hτ_le
    simpa [stoppedValue, Pi.neg_apply] using h.neg
  have hsv_nonneg : (0 : Ω → ℝ) ≤ stoppedValue Z τ := fun ω ↦ hnonneg _ _
  have hconst : ∀ ω ∈ s, (ε : ℝ) ≤ stoppedValue Z τ ω := by
    intro ω hω
    rw [hs_def, Set.mem_setOf_eq, le_sup'_iff] at hω
    obtain ⟨j, hj, hj₂⟩ := hω
    rw [mem_range, Nat.lt_succ_iff] at hj
    exact stoppedValue_hittingBtwn_mem ⟨j, ⟨Nat.zero_le _, hj⟩, hj₂⟩
  have hs_meas : MeasurableSet s :=
    measurableSet_le measurable_const
      (measurable_range_sup'' fun k _ ↦ ((hZ.stronglyAdapted k).mono (ℱ.le k)).measurable)
  -- `ε · μ s ≤ ofReal (∫_s Z_τ)` from the constant lower bound on `s`.
  have h1 : ε • μ s ≤ ENNReal.ofReal (∫ ω in s, stoppedValue Z τ ω ∂μ) := by
    have h := setIntegral_ge_of_const_le_real hs_meas (measure_ne_top _ _) hconst
      hsv_int.integrableOn
    rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
    · exact h
    · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h
  -- `∫_s Z_τ ≤ ∫ Z_τ ≤ ∫ Z_0` (nonnegativity and optional stopping on `-Z`).
  have h2 : ∫ ω in s, stoppedValue Z τ ω ∂μ ≤ ∫ ω, stoppedValue Z τ ω ∂μ :=
    setIntegral_le_integral hsv_int (Eventually.of_forall hsv_nonneg)
  have h3 : ∫ ω, stoppedValue Z τ ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ := by
    have hos := (hZ.neg).expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hτ_stop
      (fun ω ↦ by positivity) hτ_le
    rw [stoppedValue_const] at hos
    simp only [stoppedValue, Pi.neg_apply, integral_neg] at hos ⊢
    linarith
  calc ε • μ s ≤ ENNReal.ofReal (∫ ω in s, stoppedValue Z τ ω ∂μ) := h1
    _ ≤ ENNReal.ofReal (∫ ω, stoppedValue Z τ ω ∂μ) := ENNReal.ofReal_le_ofReal h2
    _ ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂μ) := ENNReal.ofReal_le_ofReal h3

/-- **Freedman-type inequality** (blueprint `lem:lil_freedman`, before optimizing over `θ`).
For a square-integrable martingale `M` with `M 0 = 0`, increments bounded by `c`, and `0 < θ` with
`θ c ≤ 1`, and for any `λ, v`,
`μ{ω : ∃ k ≤ n, λ ≤ M_k ω ∧ ⟨M⟩_k ω ≤ v} ≤ exp(-θλ + θ² v)`.
On this event the exponential supermartingale `Z_k(θ) = exp(θ M_k - θ² ⟨M⟩_k)` reaches
`exp(θλ - θ² v)`, so Ville's inequality (`smul_measure_sup_le_integral_zero`) with `E[Z_0] = 1`
gives the bound. Optimizing `θ = λ/(2v) ∧ 1/c` yields the classical `exp(-λ²/(2(v+cλ)))`. -/
theorem measure_exists_ge_le_exp [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c θ : ℝ} (hθc : |θ| * c ≤ 1) (hθ0 : 0 < θ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) (lam v : ℝ) (n : ℕ) :
    μ {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (Real.exp (-θ * lam + θ ^ 2 * v)) := by
  classical
  set Z := expProcess M ℱ μ θ with hZdef
  have hZ_super : Supermartingale Z ℱ μ := supermartingale_expProcess hM hM0 hM2 hθc hb
  have hZ_nonneg : (0 : ℕ → Ω → ℝ) ≤ Z := fun k ω ↦ (Real.exp_pos _).le
  set a := Real.exp (θ * lam - θ ^ 2 * v) with hadef
  have ha_pos : 0 < a := Real.exp_pos _
  -- `E[Z_0] = 1`.
  have hZ0 : ∫ ω, Z 0 ω ∂μ = 1 := by
    have hae : (fun ω ↦ Z 0 ω) =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
      filter_upwards [hM0] with ω h0
      simp only [Pi.zero_apply] at h0
      simp [hZdef, expProcess, predQuadVar_zero, h0]
    rw [integral_congr_ae hae]; simp
  -- The event is contained in `{a ≤ maxₖ≤ₙ Z_k}`.
  have hsubset : {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ⊆ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω} := by
    intro ω hω
    obtain ⟨k, hk, hMk, hqvk⟩ := hω
    have hZk : a ≤ Z k ω := by
      rw [hadef, hZdef]
      simp only [expProcess]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_le_mul_of_nonneg_left hMk hθ0.le,
        mul_le_mul_of_nonneg_left hqvk (sq_nonneg θ)]
    exact le_trans hZk (Finset.le_sup' (fun j ↦ Z j ω) (Finset.mem_range.mpr (by omega)))
  -- Ville's inequality with `ε = a` gives `a · μ{a ≤ sup} ≤ 1`.
  have hville := smul_measure_sup_le_integral_zero hZ_super hZ_nonneg (ε := a.toNNReal) n
  rw [hZ0, ENNReal.ofReal_one, ENNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal a ha_pos.le] at hville
  -- Convert to the exponential bound.
  have hmul : μ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω}
      * ENNReal.ofReal a ≤ 1 := by
    rw [mul_comm]; exact hville
  calc μ {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ μ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω} :=
        measure_mono hsubset
    _ ≤ (ENNReal.ofReal a)⁻¹ := ENNReal.le_inv_iff_mul_le.mpr hmul
    _ = ENNReal.ofReal (Real.exp (-θ * lam + θ ^ 2 * v)) := by
        have hexp : Real.exp (-θ * lam + θ ^ 2 * v) = a⁻¹ := by
          rw [hadef, ← Real.exp_neg]; congr 1; ring
        rw [hexp, ENNReal.ofReal_inv_of_pos ha_pos]

end AlphaRAR
