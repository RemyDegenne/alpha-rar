/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.QuadraticVariation
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Martingale.OptionalStopping

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
* `AlphaRAR.smul_measure_sup_le_integral_zero`: Ville's maximal inequality for a nonnegative
  supermartingale (fills a Mathlib gap).
* `AlphaRAR.measure_exists_ge_le_exp`, `measure_exists_ge_le_exp_optimized`,
  `measure_exists_ge_le_exp_all`: the Freedman-type tail bound (blueprint `lem:lil_freedman`),
  and its `θ`-optimized finite- and infinite-horizon forms (blueprint `cor:lil_freedman_opt`).
* `AlphaRAR.ae_eventually_forall_lt_of_summable`: the Borel–Cantelli step over a block schedule
  (blueprint `lem:lil_bc`).
* `AlphaRAR.ae_eventually_forall_lt_dyadic`: the one-sided LIL upper bound with the dyadic
  schedule (blueprint `thm:lil_bounded`).
* `AlphaRAR.ae_eventually_le_sqrt_predQuadVar_mul_log`: the consumable normalized form
  `M_n ≤ C √(⟨M⟩_n log⟨M⟩_n)` eventually, a.s. (blueprint `cor:lil_upper`).
* `AlphaRAR.ae_eventually_le_sqrt_nat_mul_log`: the `O(√(n log n))` a.s. bound for a
  bounded-increment martingale (blueprint `cor:lil_upper_nat`).
-/

open MeasureTheory Filter

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}


/-- **Conditional MGF bound for a bounded martingale increment.**
If `|ΔM_i| ≤ c` a.e. and `|θ| c ≤ 1`, then
`μ[exp(θ ΔM_i) | ℱ_i] ≤ 1 + θ² (⟨M⟩_{i+1} - ⟨M⟩_i)` a.e.
The proof uses `eˣ ≤ 1 + x + x²` for `|x| ≤ 1`, monotonicity of conditional expectation, the
martingale property `μ[ΔM_i | ℱ_i] = 0`, and `μ[(ΔM_i)² | ℱ_i] = ⟨M⟩_{i+1} - ⟨M⟩_i`
(`predQuadVar_succ_sub_eq`). -/
lemma condExp_exp_increment_le [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ) {c θ : ℝ}
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
lemma supermartingale_expProcess [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c θ : ℝ} (hθ : |θ| * c ≤ 1)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    Supermartingale (expProcess M ℱ μ θ) ℱ μ := by
  classical
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
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
lemma smul_measure_sup_le_integral_zero [IsFiniteMeasure μ] {Z : ℕ → Ω → ℝ}
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
lemma measure_exists_ge_le_exp [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
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

/-- **Freedman inequality with the optimal `θ = λ/(2v)`** (finite horizon).
For a square-integrable martingale `M` with `M 0 = 0`, increments bounded by `c > 0`, and
`0 < λ`, `0 < v` with `λ c ≤ 2 v` (so the optimizer `θ = λ/(2v)` is admissible, `θ c ≤ 1`),
`μ{ω : ∃ k ≤ n, λ ≤ M_k ω ∧ ⟨M⟩_k ω ≤ v} ≤ exp(-λ²/(4v))`.
This is `measure_exists_ge_le_exp` evaluated at `θ = λ/(2v)`, where
`-θλ + θ² v = -λ²/(4v)`. The variance proxy is `2v` rather than the sharp `v` because the
one-step bound uses `eˣ ≤ 1 + x + x²`; this costs a factor `√2` in the eventual LIL constant. -/
lemma measure_exists_ge_le_exp_optimized [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {lam v : ℝ} (hlam : 0 < lam) (hv : 0 < v)
    (hadm : lam * c ≤ 2 * v) (n : ℕ) :
    μ {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (Real.exp (-lam ^ 2 / (4 * v))) := by
  set θ := lam / (2 * v) with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθc : |θ| * c ≤ 1 := by
    rw [abs_of_pos hθ0, hθdef, div_mul_eq_mul_div, div_le_one (by positivity)]
    exact hadm
  have h := measure_exists_ge_le_exp hM hM0 hM2 hθc hθ0 hb lam v n
  have hexp : -θ * lam + θ ^ 2 * v = -lam ^ 2 / (4 * v) := by
    rw [hθdef]; field_simp; ring
  rwa [hexp] at h

/-- The process `M` **stopped at the deterministic time `N`**: `stopMart M N m = M (min m N)`. Since
the horizon is a constant (not a random stopping time), we avoid Mathlib's `WithTop`-valued
`stoppedProcess` machinery and record the elementary facts we need directly. This is the device that
lets the Freedman bound accommodate a martingale whose increments are bounded only *up to* a fixed
horizon (the truncated-response martingale, whose truncation level `√i` grows). -/
noncomputable def stopMart (M : ℕ → Ω → ℝ) (N : ℕ) : ℕ → Ω → ℝ := fun m ↦ M (min m N)

lemma stopMart_apply (M : ℕ → Ω → ℝ) (N m : ℕ) : stopMart M N m = M (min m N) := rfl

/-- **The stopped process is a martingale.** For `i < N` the increment equals `M (i+1) - M i`
(a martingale increment); for `i ≥ N` the process is frozen at `M N`, whose conditional expectation
given `ℱ i ⊇ ℱ N` is itself. -/
lemma martingale_stopMart [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (N : ℕ) :
    Martingale (stopMart M N) ℱ μ := by
  refine martingale_nat (fun i ↦ (hM.stronglyMeasurable (min i N)).mono (ℱ.mono (min_le_left i N)))
    (fun i ↦ hM.integrable (min i N)) (fun i ↦ ?_)
  by_cases hi : i < N
  · have h1 : min i N = i := by omega
    have h2 : min (i + 1) N = i + 1 := by omega
    simp only [stopMart_apply, h1, h2]
    exact (hM.condExp_ae_eq (Nat.le_succ i)).symm
  · have hNi : N ≤ i := not_lt.mp hi
    have h1 : min i N = N := by omega
    have h2 : min (i + 1) N = N := by omega
    simp only [stopMart_apply, h1, h2]
    rw [condExp_of_stronglyMeasurable (ℱ.le i)
      ((hM.stronglyMeasurable N).mono (ℱ.mono hNi)) (hM.integrable N)]

/-- **The quadratic variation is unaffected by stopping, below the horizon.** For `m ≤ N`,
`⟨stopMart M N⟩_m = ⟨M⟩_m`, since every increment in the defining sum has index `i < m ≤ N`, where
`min (i+1) N = i+1` and `min i N = i`, so the compensator terms agree exactly. -/
lemma predQuadVar_stopMart_of_le (M : ℕ → Ω → ℝ) (N : ℕ) {m : ℕ} (hmN : m ≤ N) :
    predQuadVar (stopMart M N) ℱ μ m = predQuadVar M ℱ μ m := by
  simp only [predQuadVar, predictablePart]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  have h1 : min i N = i := by omega
  have h2 : min (i + 1) N = i + 1 := by omega
  simp only [stopMart_apply, h1, h2]

/-- **Freedman inequality with a horizon-local increment bound.** Same conclusion as
`measure_exists_ge_le_exp` (the pre-optimization form, with an *explicit* `θ`), but the increment
bound `|ΔM_i| ≤ c` is required only up to the horizon `N` (`∀ i < N`), and the event restricted to
times `m ≤ N`. This is what makes the bound applicable to a martingale with *growing* increments
(bounded only below `N`): apply the bound to the process stopped at `N`, whose increments are
globally bounded by `c` (they vanish past `N`) and whose value and quadratic variation agree with
`M`'s at every time `m ≤ N`. The pre-optimization form is essential here: the block LIL uses the
*constrained* `θ = 1/c` (the true optimizer `λ/(2v)` is inadmissible), so `measure_exists_ge_le_exp`
rather than `measure_exists_ge_le_exp_optimized` is what stops at the horizon. -/
lemma measure_exists_ge_le_exp_horizon [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c θ : ℝ} (hc : 0 ≤ c)
    (hθc : |θ| * c ≤ 1) (hθ0 : 0 < θ) (lam v : ℝ) (N : ℕ)
    (hb : ∀ i < N, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    μ {ω | ∃ m ≤ N, lam ≤ M m ω ∧ predQuadVar M ℱ μ m ω ≤ v}
      ≤ ENNReal.ofReal (Real.exp (-θ * lam + θ ^ 2 * v)) := by
  have hM'0 : stopMart M N 0 =ᵐ[μ] 0 := by
    have : stopMart M N 0 = M 0 := by rw [stopMart_apply, Nat.zero_min]
    rw [this]; exact hM0
  have hM'2 : ∀ n, Integrable (fun ω ↦ stopMart M N n ω ^ 2) μ := fun n ↦ by
    simp only [stopMart_apply]; exact hM2 (min n N)
  -- Increments of the stopped process are globally bounded by `c`.
  have hb' : ∀ i, ∀ᵐ ω ∂μ, |stopMart M N (i + 1) ω - stopMart M N i ω| ≤ c := fun i ↦ by
    by_cases hi : i < N
    · have h1 : min i N = i := by omega
      have h2 : min (i + 1) N = i + 1 := by omega
      simpa only [stopMart_apply, h1, h2] using hb i hi
    · have hNi : N ≤ i := not_lt.mp hi
      have h1 : min i N = N := by omega
      have h2 : min (i + 1) N = N := by omega
      filter_upwards with ω
      simp only [stopMart_apply, h1, h2, sub_self, abs_zero]; exact hc
  have hmain := measure_exists_ge_le_exp (martingale_stopMart hM N) hM'0 hM'2 hθc hθ0 hb'
    lam v N
  -- Below the horizon the two events coincide.
  have hset : {ω | ∃ m ≤ N, lam ≤ M m ω ∧ predQuadVar M ℱ μ m ω ≤ v}
      = {ω | ∃ m ≤ N, lam ≤ stopMart M N m ω ∧ predQuadVar (stopMart M N) ℱ μ m ω ≤ v} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun m ↦ and_congr_right fun hm ↦ ?_
    rw [stopMart_apply, min_eq_left hm, predQuadVar_stopMart_of_le M N hm]
  rw [hset]; exact hmain

/-- **Freedman inequality with the optimal `θ`, infinite horizon.**
Taking `n → ∞` in `measure_exists_ge_le_exp_optimized` (the events increase with `n`):
`μ{ω : ∃ k, λ ≤ M_k ω ∧ ⟨M⟩_k ω ≤ v} ≤ exp(-λ²/(4v))`. This is the form fed to Borel–Cantelli
in the one-sided law of the iterated logarithm. -/
lemma measure_exists_ge_le_exp_all [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {lam v : ℝ} (hlam : 0 < lam) (hv : 0 < v)
    (hadm : lam * c ≤ 2 * v) :
    μ {ω | ∃ k, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (Real.exp (-lam ^ 2 / (4 * v))) := by
  set A : ℕ → Set Ω := fun n ↦ {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v} with hA
  have hmono : Monotone A := fun a b hab ω ⟨k, hk, h⟩ ↦ ⟨k, hk.trans hab, h⟩
  have hUnion : (⋃ n, A n) = {ω | ∃ k, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v} := by
    ext ω
    simp only [hA, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun ⟨_, k, _, h⟩ ↦ ⟨k, h⟩, fun ⟨k, h⟩ ↦ ⟨k, k, le_rfl, h⟩⟩
  rw [← hUnion, hmono.measure_iUnion]
  exact iSup_le fun n ↦ measure_exists_ge_le_exp_optimized hM hM0 hM2 hb hlam hv hadm n

/-- **Borel–Cantelli step of the one-sided LIL.**
Given a block schedule `(v_k)`, `(λ_k)` of thresholds with `λ_k c ≤ 2 v_k` (admissibility) whose
optimized Freedman tail bounds are summable, `∑_k exp(-λ_k²/(4 v_k)) < ∞`, almost surely only
finitely many blocks are "bad": for a.e. `ω`, eventually in `k`, no time `n` has both
`M_n ≥ λ_k` and `⟨M⟩_n ≤ v_k`. Equivalently, for large `k`, `⟨M⟩_n ≤ v_k ⇒ M_n < λ_k` for all `n`.
This is the first Borel–Cantelli lemma (`ae_eventually_notMem`) applied to the sets
`s_k = {∃ n, M_n ≥ λ_k ∧ ⟨M⟩_n ≤ v_k}`, whose measures are bounded via
`measure_exists_ge_le_exp_all`. -/
lemma ae_eventually_forall_lt_of_summable [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {lam v : ℕ → ℝ} (hlam : ∀ k, 0 < lam k)
    (hv : ∀ k, 0 < v k) (hadm : ∀ k, lam k * c ≤ 2 * v k)
    (hsum : Summable fun k ↦ Real.exp (-lam k ^ 2 / (4 * v k))) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ∀ n, predQuadVar M ℱ μ n ω ≤ v k → M n ω < lam k := by
  set s : ℕ → Set Ω := fun k ↦ {ω | ∃ n, lam k ≤ M n ω ∧ predQuadVar M ℱ μ n ω ≤ v k} with hs_def
  have hμs : ∀ k, μ (s k) ≤ ENNReal.ofReal (Real.exp (-lam k ^ 2 / (4 * v k))) := fun k ↦
    measure_exists_ge_le_exp_all hM hM0 hM2 hb (hlam k) (hv k) (hadm k)
  have hfin : (∑' k, μ (s k)) ≠ ∞ := by
    have h1 : (∑' k, μ (s k)) ≤ ∑' k, ENNReal.ofReal (Real.exp (-lam k ^ 2 / (4 * v k))) :=
      ENNReal.tsum_le_tsum hμs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (Real.exp_pos _).le) hsum] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with k hk
  simp only [hs_def, Set.mem_setOf_eq, not_exists, not_and] at hk
  intro n hn
  by_contra hcon
  rw [not_lt] at hcon
  exact hk n hcon hn

/-- **One-sided LIL with a dyadic schedule** (formalized content of blueprint `thm:lil_bounded`).
Instantiating the Borel–Cantelli step (`ae_eventually_forall_lt_of_summable`) with dyadic blocks
`v_k = 2^k` and thresholds `λ_k = K √(2^k (k+1))`, where `0 < K` and `K c ≤ 2`. Admissibility
`λ_k c ≤ 2 v_k` then holds for *every* `k` (via `k + 1 ≤ 2^k`, so `√(2^k(k+1)) ≤ 2^k`), and the
tail bounds telescope to a geometric series,
`exp(-λ_k²/(4 v_k)) = exp(-K²(k+1)/4)`. Conclusion: almost surely, for all large `k` and every
time `n`, `⟨M⟩_n ≤ 2^k ⇒ M_n < K √(2^k (k+1))`. Since on the block `⟨M⟩_n ∈ (2^{k-1}, 2^k]` one has
`√(2^k(k+1)) ≍ √(⟨M⟩_n log ⟨M⟩_n)`, this is the `O(√(⟨M⟩_n log ⟨M⟩_n))` upper bound — a `log`
(not `log log`) rate, which suffices for the `o(⟨M⟩_n)` uses downstream. -/
theorem ae_eventually_forall_lt_dyadic [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c K : ℝ} (hc : 0 ≤ c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) (hK : 0 < K) (hKc : K * c ≤ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ (k : ℕ) in atTop, ∀ n, predQuadVar M ℱ μ n ω ≤ (2 : ℝ) ^ k →
      M n ω < K * √((2 : ℝ) ^ k * ((k : ℝ) + 1)) := by
  have hv : ∀ k : ℕ, (0 : ℝ) < (2 : ℝ) ^ k := fun k ↦ by positivity
  have hkle : ∀ k : ℕ, (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := fun k ↦ by
    have h : k + 1 ≤ 2 ^ k := k.lt_two_pow_self
    calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 : ℝ) ^ k := by push_cast; ring
  have hlam : ∀ k : ℕ, 0 < K * √((2 : ℝ) ^ k * ((k : ℝ) + 1)) := fun k ↦
    mul_pos hK (Real.sqrt_pos.mpr (by positivity))
  have hadm : ∀ k : ℕ, K * √((2 : ℝ) ^ k * ((k : ℝ) + 1)) * c ≤ 2 * (2 : ℝ) ^ k :=
    fun k ↦ by
      have hsqrt_le : √((2 : ℝ) ^ k * ((k : ℝ) + 1)) ≤ (2 : ℝ) ^ k := by
        calc √((2 : ℝ) ^ k * ((k : ℝ) + 1))
            ≤ √((2 : ℝ) ^ k * (2 : ℝ) ^ k) :=
              Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hkle k) (hv k).le)
          _ = (2 : ℝ) ^ k := Real.sqrt_mul_self (hv k).le
      calc K * √((2 : ℝ) ^ k * ((k : ℝ) + 1)) * c
          ≤ K * (2 : ℝ) ^ k * c :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt_le hK.le) hc
        _ = K * c * (2 : ℝ) ^ k := by ring
        _ ≤ 2 * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_right hKc (hv k).le
  have hsum : Summable fun k : ℕ ↦
      Real.exp (-(K * √((2 : ℝ) ^ k * ((k : ℝ) + 1))) ^ 2 / (4 * (2 : ℝ) ^ k)) := by
    have hkey : ∀ k : ℕ,
        Real.exp (-(K * √((2 : ℝ) ^ k * ((k : ℝ) + 1))) ^ 2 / (4 * (2 : ℝ) ^ k))
          = Real.exp (-(K ^ 2 / 4)) ^ (k + 1) := by
      intro k
      have hsq : (K * √((2 : ℝ) ^ k * ((k : ℝ) + 1))) ^ 2
          = K ^ 2 * ((2 : ℝ) ^ k * ((k : ℝ) + 1)) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [hsq, ← Real.exp_nat_mul]
      congr 1
      push_cast
      rw [div_eq_iff (by positivity : (0 : ℝ) < 4 * 2 ^ k).ne']
      ring
    rw [summable_congr hkey]
    have hr1 : Real.exp (-(K ^ 2 / 4)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have : 0 < K ^ 2 := by positivity
      linarith
    have hgeo : Summable fun k : ℕ ↦ Real.exp (-(K ^ 2 / 4)) ^ k :=
      summable_geometric_of_lt_one (Real.exp_pos _).le hr1
    exact (hgeo.mul_right (Real.exp (-(K ^ 2 / 4)))).congr fun k ↦ (pow_succ _ k).symm
  refine ae_eventually_forall_lt_of_summable hM hM0 hM2 hb ?_ ?_ ?_ ?_
  · exact hlam
  · exact hv
  · exact hadm
  · exact hsum

/-- **One-sided LIL upper bound in normalized form** (the consumable `O`-rate).
If additionally `⟨M⟩_n → ∞` a.s., then almost surely `M_n ≤ C √(⟨M⟩_n · log⟨M⟩_n)` eventually,
for a deterministic constant `C` (depending only on `c`). This repackages the dyadic exceedance
statement `ae_eventually_forall_lt_dyadic`: for large `n`, take the least block `k` with
`⟨M⟩_n ≤ 2^k`; minimality gives `2^k ≤ 2⟨M⟩_n` and `k ≲ log₂⟨M⟩_n`, so
`K√(2^k(k+1)) ≤ C√(⟨M⟩_n log⟨M⟩_n)`. This is the `O(√(⟨M⟩_n log⟨M⟩_n))` a.s. upper bound used
downstream (blueprint `lem:U_increment_bound`, via the bounded assignment martingale) — a `log`
rather than `log log` rate, which suffices for the `o(⟨M⟩_n)` conclusions. -/
lemma ae_eventually_le_sqrt_predQuadVar_mul_log [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop,
      M n ω ≤ C * √(predQuadVar M ℱ μ n ω * Real.log (predQuadVar M ℱ μ n ω)) := by
  classical
  set K : ℝ := 2 / c with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  have hKc : K * c = 2 := by rw [hKdef]; field_simp
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  filter_upwards [ae_eventually_forall_lt_dyadic hM hM0 hM2 hc.le hb hK hKc.le, hV]
    with ω hgood hVω
  rw [eventually_atTop] at hgood
  obtain ⟨k₀, hk₀⟩ := hgood
  refine ⟨K * √(2 * (1 / Real.log 2 + 2)), ?_⟩
  filter_upwards [hVω.eventually_ge_atTop ((2 : ℝ) ^ k₀), hVω.eventually_ge_atTop (Real.exp 1)]
    with n hn0 hne
  let V := predQuadVar M ℱ μ n ω
  have hVpos : 0 < V := lt_of_lt_of_le (Real.exp_pos 1) hne
  have hlogV1 : (1 : ℝ) ≤ Real.log V := (Real.le_log_iff_exp_le hVpos).mpr hne
  have hlogVnn : (0 : ℝ) ≤ Real.log V := le_trans zero_le_one hlogV1
  have hVge1 : (1 : ℝ) ≤ V := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hne
  -- Least block `k` with `V ≤ 2^k`.
  obtain ⟨k, hVle, hkmin⟩ : ∃ k : ℕ, V ≤ (2 : ℝ) ^ k ∧ ∀ m, m < k → ¬ V ≤ (2 : ℝ) ^ m := by
    have hex : ∃ k : ℕ, V ≤ (2 : ℝ) ^ k :=
      ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop V).exists
    exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
  have hkk0 : k₀ ≤ k := (pow_le_pow_iff_right₀ one_lt_two).mp (le_trans hn0 hVle)
  have h2k : (2 : ℝ) ^ k ≤ 2 * V := by
    obtain _ | m := k
    · rw [pow_zero]; linarith
    · have hm : ¬ V ≤ (2 : ℝ) ^ m := hkmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      rw [pow_succ]; linarith
  have hk1 : (k : ℝ) + 1 ≤ Real.log V / Real.log 2 + 2 := by
    obtain _ | m := k
    · simp only [Nat.cast_zero]; have := div_nonneg hlogVnn hlog2.le; linarith
    · have hm : ¬ V ≤ (2 : ℝ) ^ m := hkmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmlog : (m : ℝ) * Real.log 2 < Real.log V := by
        rw [← Real.log_pow]; exact Real.log_lt_log (by positivity) hm
      have : (m : ℝ) < Real.log V / Real.log 2 := by rw [lt_div_iff₀ hlog2]; linarith
      push_cast; linarith
  -- Assemble the normalized bound.
  have hMn : M n ω < K * √((2 : ℝ) ^ k * ((k : ℝ) + 1)) := hk₀ k hkk0 n hVle
  have hb2 : Real.log V / Real.log 2 + 2 ≤ (1 / Real.log 2 + 2) * Real.log V := by
    have h : (1 / Real.log 2 + 2) * Real.log V
        = Real.log V / Real.log 2 + 2 * Real.log V := by
      rw [add_mul, one_div, inv_mul_eq_div]
    rw [h]; linarith
  have hprod_le : (2 : ℝ) ^ k * ((k : ℝ) + 1) ≤ 2 * (1 / Real.log 2 + 2) * (V * Real.log V) := by
    have step1 : (2 : ℝ) ^ k * ((k : ℝ) + 1) ≤ 2 * V * (Real.log V / Real.log 2 + 2) :=
      mul_le_mul h2k hk1 (by positivity) (by positivity)
    have step2 : 2 * V * (Real.log V / Real.log 2 + 2)
        ≤ 2 * (1 / Real.log 2 + 2) * (V * Real.log V) := by
      have h := mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ 2 * V)
      calc 2 * V * (Real.log V / Real.log 2 + 2)
          ≤ 2 * V * ((1 / Real.log 2 + 2) * Real.log V) := h
        _ = 2 * (1 / Real.log 2 + 2) * (V * Real.log V) := by ring
    linarith
  have hDnn : (0 : ℝ) ≤ 2 * (1 / Real.log 2 + 2) := by positivity
  have hsqrt_le : √((2 : ℝ) ^ k * ((k : ℝ) + 1))
      ≤ √(2 * (1 / Real.log 2 + 2)) * √(V * Real.log V) := by
    rw [← Real.sqrt_mul hDnn]; exact Real.sqrt_le_sqrt hprod_le
  calc M n ω ≤ K * √((2 : ℝ) ^ k * ((k : ℝ) + 1)) := hMn.le
    _ ≤ K * (√(2 * (1 / Real.log 2 + 2)) * √(V * Real.log V)) :=
        mul_le_mul_of_nonneg_left hsqrt_le hK.le
    _ = K * √(2 * (1 / Real.log 2 + 2)) * √(V * Real.log V) := by ring

/-- **One-sided LIL upper bound at scale `√(n log n)`** for a bounded-increment martingale.
If `M` is a square-integrable martingale with `M 0 = 0`, `|ΔM_i| ≤ c`, and `⟨M⟩_n → ∞` a.s., then
almost surely `M_n ≤ C √(n log n)` eventually. This combines the normalized bound
`ae_eventually_le_sqrt_predQuadVar_mul_log` with `⟨M⟩_n ≤ c² n` (`predQuadVar_le_of_bound`) and
`log⟨M⟩_n ≤ 2 log n` (valid once `n ≥ c²`). It is the `O(√(n log n))` a.s. upper bound applied
downstream to the bounded assignment martingale (blueprint `lem:U_increment_bound`, stated there
with `log log`, weakened here to `log`). -/
lemma ae_eventually_le_sqrt_nat_mul_log [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop, M n ω ≤ C * √(n * Real.log n) := by
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  have haesm_d : ∀ i, AEStronglyMeasurable (fun ω ↦ M (i + 1) ω - M i ω) μ := fun i ↦
    (((hM.stronglyMeasurable (i + 1)).mono (ℱ.le _)).sub
      ((hM.stronglyMeasurable i).mono (ℱ.le _))).aestronglyMeasurable
  have hdmem : ∀ i, MemLp (fun ω ↦ M (i + 1) ω - M i ω) 2 μ := fun i ↦
    MemLp.of_bound (haesm_d i) c (by filter_upwards [hb i] with ω h; rwa [Real.norm_eq_abs])
  have hMmem : ∀ n, MemLp (M n) 2 μ := fun n ↦
    (memLp_two_iff_integrable_sq
      ((hM.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable).mpr (hM2 n)
  have hd2 : ∀ i, Integrable (fun ω ↦ (M (i + 1) ω - M i ω) ^ 2) μ :=
    fun i ↦ (hdmem i).integrable_sq
  have hprod : ∀ i, Integrable (M i * (M (i + 1) - M i)) μ := fun i ↦
    (hMmem i).integrable_mul ((hMmem (i + 1)).sub (hMmem i))
  filter_upwards [ae_eventually_le_sqrt_predQuadVar_mul_log hM hM0 hM2 hc hb hV,
    predQuadVar_le_of_bound hM hd2 hprod hb, hV] with ω hCex hle hVω
  obtain ⟨C, hC⟩ := hCex
  refine ⟨|C| * √(2 * c ^ 2), ?_⟩
  filter_upwards [hC, hVω.eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (c ^ 2)), eventually_ge_atTop 2]
    with n hCn hV1 hnc hn2
  let V := predQuadVar M ℱ μ n ω
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hlogVnn : 0 ≤ Real.log V := Real.log_nonneg hV1
  have hlogV2 : Real.log V ≤ 2 * Real.log n := by
    have h1 : Real.log V ≤ Real.log (c ^ 2 * n) :=
      (Real.log_le_log_iff (by linarith [hV1]) (by positivity)).mpr (hle n)
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    have hlogc2 : Real.log (c ^ 2) ≤ Real.log n :=
      (Real.log_le_log_iff (by positivity) (by linarith)).mpr hnc
    linarith
  have hprodle : V * Real.log V ≤ 2 * c ^ 2 * ((n : ℝ) * Real.log n) := by
    nlinarith [mul_le_mul (hle n) hlogV2 hlogVnn (by positivity : (0 : ℝ) ≤ c ^ 2 * n)]
  have hsqrt : √(V * Real.log V)
      ≤ √(2 * c ^ 2) * √((n : ℝ) * Real.log n) := by
    rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hprodle
  calc M n ω ≤ C * √(V * Real.log V) := hCn
    _ ≤ |C| * √(V * Real.log V) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
    _ ≤ |C| * (√(2 * c ^ 2) * √((n : ℝ) * Real.log n)) :=
        mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C)
    _ = |C| * √(2 * c ^ 2) * √((n : ℝ) * Real.log n) := by ring

end AlphaRAR
