/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.LILCommon
public import AlphaRAR.Mathlib.QuadraticVariation
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.OptionalStopping
public meta import Characterization

/-!
# The exponential supermartingale and Freedman's inequality

For a martingale `M` with `M 0 = 0`, increments bounded by `c`, and a parameter `θ` with
`|θ| c ≤ η`, where `η` is a window on which `eˣ ≤ 1 + x + ½(1+δ)x²`, the process
`Z_n(θ) = exp(θ M_n - ½(1+δ)θ² ⟨M⟩_n)` is a supermartingale, `⟨M⟩` being the predictable quadratic
variation. Ville's maximal inequality then gives Freedman's inequality
`μ{∃ k ≤ n, λ ≤ M_k ∧ ⟨M⟩_k ≤ v} ≤ exp(-θλ + ½(1+δ)θ²v)`, its optimized form
`exp(-λ²/(2(1+δ)v))`, its infinite-horizon form, and a horizon-local form for increments bounded
only up to a fixed time (via the process stopped at that time). Together with Borel–Cantelli over a
block schedule, this is the whole engine behind the laws of the iterated logarithm of
`LILTruncation.lean` and `LIL.lean`.

The variance proxy `1 + δ` is a parameter throughout: the sharp LIL constant comes from `δ ↓ 0`
with the window `η = min 1 (9δ/4)` of `exp_le_one_add_add_half_mul_sq`, while `δ = η = 1`
(`exp_le_one_add_add_sq`, Mathlib's `Real.abs_exp_sub_one_sub_id_le`) is the crude choice that
suffices for `O`-rates.

## Main results

* `AlphaRAR.exp_le_one_add_add_half_mul_sq`: `eˣ ≤ 1 + x + ½(1+δ)x²` for `|x| ≤ min 1 (9δ/4)`.
* `AlphaRAR.condExp_exp_increment_le`: the conditional MGF bound
  `μ[exp(θ ΔM_i) | ℱ_i] ≤ 1 + ½(1+δ)θ² (⟨M⟩_{i+1} - ⟨M⟩_i)`.
* `AlphaRAR.expProcess`, `AlphaRAR.supermartingale_expProcess`: the exponential supermartingale.
* `AlphaRAR.smul_measure_sup_le_integral_zero`: Ville's maximal inequality for a nonnegative
  supermartingale (fills a Mathlib gap).
* `AlphaRAR.measure_exists_ge_le_exp`, `measure_exists_ge_le_exp_optimized`,
  `measure_exists_ge_le_exp_all`: Freedman's inequality at an explicit `θ`, at the optimal `θ`,
  and over an infinite horizon.
* `AlphaRAR.martingale_stoppedProcess_const`, `AlphaRAR.predQuadVar_stoppedProcess_const_of_le`,
  `AlphaRAR.measure_exists_ge_le_exp_horizon`: Freedman's inequality when the increments are
  bounded only up to a fixed time `N`, via Mathlib's `stoppedProcess` at the constant time `N`.
* `AlphaRAR.ae_eventually_forall_lt_of_summable`: the Borel–Cantelli step over a block schedule
  `(v_k, λ_k)` with summable optimized tails, admissibility being required only eventually.
* `AlphaRAR.ae_eventually_forall_le_lt_of_summable`: the same over time blocks `N_j` with
  horizon-local increment bounds `c_j` and explicit parameters `θ_j`, the engine of every
  growing-increment LIL.
-/

@[expose] public section

open MeasureTheory Filter Real

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-! ### The one-step inequality -/

/-- **Refined elementary inequality.** `eˣ ≤ 1 + x + ½(1+δ)x²` for `|x| ≤ min 1 (9δ/4)`. Mathlib's
`Real.exp_bound` at `n = 3` gives `|eˣ - (1 + x + ½x²)| ≤ (2/9)|x|³` for `|x| ≤ 1`, hence
`eˣ ≤ 1 + x + ½x² + (2/9)|x|³ ≤ 1 + x + ½(1 + (4/9)|x|)x²`. This is the one-step estimate whose
variance proxy `1+δ → 1` gives the sharp LIL constant. (For `δ < 0` the window is empty.) -/
lemma exp_le_one_add_add_half_mul_sq {δ x : ℝ} (hx : |x| ≤ min 1 (9 / 4 * δ)) :
    exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2 := by
  have hx1 : |x| ≤ 1 := hx.trans (min_le_left _ _)
  have hxδ : |x| ≤ 9 / 4 * δ := hx.trans (min_le_right _ _)
  have hb := Real.exp_bound hx1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  have habs3 : |x| ^ 3 = |x| * x ^ 2 := by rw [← sq_abs x]; ring
  have hstep : |x| ^ 3 * (2 / 9) ≤ δ / 2 * x ^ 2 := by
    rw [habs3]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxδ) (sq_nonneg x)]
  rw [show (1 + δ) / 2 * x ^ 2 = x ^ 2 / 2 + δ / 2 * x ^ 2 from by ring]
  linarith [le_of_abs_le hb, hstep]

/-- The `δ = 1` case on the window `η = 1`: `eˣ ≤ 1 + x + x²` for `|x| ≤ 1` (also Mathlib's
`Real.abs_exp_sub_one_sub_id_le`). It is what specializes the engine to the crude `O`-rates. -/
lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + (1 + 1) / 2 * x ^ 2 :=
  exp_le_one_add_add_half_mul_sq (le_min hx (by linarith))

/-! ### The exponential supermartingale -/

/-- **Conditional MGF bound for a bounded martingale increment.** If `|ΔM_i| ≤ c` a.e. and
`|θ| c ≤ η`, where `η` is a window for the one-step inequality at level `δ` (`hη`, e.g. from
`exp_le_one_add_add_half_mul_sq`), then
`μ[exp(θ ΔM_i) | ℱ_i] ≤ 1 + ½(1+δ)θ²(⟨M⟩_{i+1} - ⟨M⟩_i)` a.e. The proof combines the pointwise
inequality, monotonicity of conditional expectation, the martingale property `μ[ΔM_i | ℱ_i] = 0`,
and `μ[(ΔM_i)² | ℱ_i] = ⟨M⟩_{i+1} - ⟨M⟩_i` (`predQuadVar_succ_sub_eq`). -/
lemma condExp_exp_increment_le [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    {c θ δ η : ℝ} (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hθ : |θ| * c ≤ η) (i : ℕ) (hb : ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hd2 : MemLp (fun ω ↦ M (i + 1) ω - M i ω) 2 μ)
    (hprod : Integrable (M i * (M (i + 1) - M i)) μ) :
    μ[fun ω ↦ exp (θ * (M (i + 1) ω - M i ω)) | ℱ i]
      ≤ᵐ[μ] fun ω ↦ 1 + (1 + δ) / 2 * θ ^ 2
        * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
  have haesm_d : AEStronglyMeasurable (fun ω ↦ M (i + 1) ω - M i ω) μ := hd2.aestronglyMeasurable
  -- Pointwise bound `exp(θ ΔM) ≤ 1 + θ ΔM + ½(1+δ)θ² ΔM²`.
  have hptwise : (fun ω ↦ exp (θ * (M (i + 1) ω - M i ω)))
      ≤ᵐ[μ] fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
        + (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 := by
    filter_upwards [hb] with ω hbω
    have hx : |θ * (M (i + 1) ω - M i ω)| ≤ η := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
    nlinarith [hη _ hx]
  -- The quadratic bound and the exponential are integrable.
  have hint_exp : Integrable (fun ω ↦ exp (θ * (M (i + 1) ω - M i ω))) μ := by
    refine (MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
      (haesm_d.const_mul θ)) (exp η) ?_).integrable le_rfl
    filter_upwards [hb] with ω hbω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
  have hint_lin : Integrable (fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω)) μ :=
    (integrable_const 1).add ((hd2.integrable one_le_two).const_mul θ)
  have hint_quad : Integrable (fun ω ↦ (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2) μ :=
    hd2.integrable_sq.const_mul _
  have hint_q : Integrable (fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
      + (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2) μ := hint_lin.add hint_quad
  -- Conditional expectation of the increment is `0`.
  have hd0 : μ[fun ω ↦ M (i + 1) ω - M i ω | ℱ i] =ᵐ[μ] 0 :=
    hM.condExp_sub_ae_eq_zero (Nat.le_succ i)
  -- Conditional expectation of the squared increment is `⟨M⟩_{i+1} - ⟨M⟩_i`.
  have hd2eq : μ[fun ω ↦ (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
      =ᵐ[μ] fun ω ↦ predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω :=
    (predQuadVar_succ_sub_eq hM i hd2 hprod).symm
  -- Conditional expectation of the quadratic bound.
  have hcond_q : μ[fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
      + (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
      =ᵐ[μ] fun ω ↦ 1 + (1 + δ) / 2 * θ ^ 2
        * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
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
    have hquad : μ[fun ω ↦ (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
        =ᵐ[μ] fun ω ↦ (1 + δ) / 2 * θ ^ 2
          * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
      have hsmul : μ[fun ω ↦ (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
          =ᵐ[μ] ((1 + δ) / 2 * θ ^ 2) • μ[fun ω ↦ (M (i + 1) ω - M i ω) ^ 2 | ℱ i] :=
        condExp_smul ((1 + δ) / 2 * θ ^ 2) _ _
      filter_upwards [hsmul, hd2eq] with ω esm ed2
      rw [esm, Pi.smul_apply, ed2, smul_eq_mul]
    have hadd : μ[fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
        + (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
        =ᵐ[μ] μ[fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω) | ℱ i]
          + μ[fun ω ↦ (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i] :=
      condExp_add hint_lin hint_quad _
    filter_upwards [hadd, hlin, hquad] with ω ea el eq
    rw [ea, Pi.add_apply, el, eq]
  exact (condExp_mono hint_exp hint_q hptwise).trans hcond_q.le

/-- The **exponential process** `Z_n(θ) = exp(θ M_n - ½(1+δ)θ² ⟨M⟩_n)`. -/
noncomputable def expProcess (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    (δ θ : ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦ exp (θ * M n ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ n ω)

/-- **The exponential process is a supermartingale.**
For a martingale `M` with `M 0 = 0`, square-integrable, with increments bounded by `c`, and for
`|θ| c ≤ η`, the process `Z_n(θ) = exp(θ M_n - ½(1+δ)θ² ⟨M⟩_n)` is a supermartingale.
The one-step bound is `μ[Z_{i+1} | ℱ_i] = Z_i e^{-½(1+δ)θ² Δ⟨M⟩_i} μ[e^{θ ΔM_i} | ℱ_i]
≤ Z_i e^{-½(1+δ)θ² Δ⟨M⟩_i}(1 + ½(1+δ)θ² Δ⟨M⟩_i) ≤ Z_i`, using `condExp_exp_increment_le` and
`1 + y ≤ eʸ`. -/
@[specifies expProcess "the reason for the `½(1+δ)` coefficient: it is the smallest compensator \
that still yields a supermartingale under the one-step MGF bound, and shrinking it towards the \
Gaussian `½` is exactly what buys the sharp LIL constant"]
lemma supermartingale_expProcess [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) {c θ δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2) (hθ : |θ| * c ≤ η)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    Supermartingale (expProcess M ℱ μ δ θ) ℱ μ := by
  classical
  have hM2 : ∀ n, MemLp (M n) 2 μ := hM.memLp_of_abs_increment_le hM0 hb
  have hd2 : ∀ i, MemLp (fun ω ↦ M (i + 1) ω - M i ω) 2 μ := fun i ↦
    memLp_increment (hM2 i) (hM2 (i + 1))
  have haesm_d : ∀ i, AEStronglyMeasurable (fun ω ↦ M (i + 1) ω - M i ω) μ := fun i ↦
    (hd2 i).aestronglyMeasurable
  have hprod : ∀ i, Integrable (M i * (M (i + 1) - M i)) μ := fun i ↦
    integrable_mul_increment (hM2 i) (hM2 (i + 1))
  have hMn : ∀ n, ∀ᵐ ω ∂μ, |M n ω| ≤ n * c := by
    intro n
    filter_upwards [ae_all_iff.mpr hb, hM0] with ω hball h0
    simp only [Pi.zero_apply] at h0
    have htel : (∑ j ∈ Finset.range n, (M (j + 1) ω - M j ω)) = M n ω := by
      rw [Finset.sum_range_sub (M · ω) n, h0, sub_zero]
    rw [← htel]
    calc |∑ j ∈ Finset.range n, (M (j + 1) ω - M j ω)|
        ≤ ∑ j ∈ Finset.range n, |M (j + 1) ω - M j ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, c := Finset.sum_le_sum fun j _ ↦ hball j
      _ = n * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hinner : ∀ n, StronglyMeasurable[ℱ n]
      (fun ω ↦ θ * M n ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ n ω) := fun n ↦
    ((hM.stronglyMeasurable n).const_mul θ).sub
      ((stronglyAdapted_predictablePart' (f := fun k ↦ M k ^ 2) n).const_mul ((1 + δ) / 2 * θ ^ 2))
  have hZaesm : ∀ n, AEStronglyMeasurable (expProcess M ℱ μ δ θ n) μ := fun n ↦
    ((Real.continuous_exp.comp_stronglyMeasurable (hinner n)).mono (ℱ.le n)).aestronglyMeasurable
  have hZbd : ∀ n, ∀ᵐ ω ∂μ, ‖expProcess M ℱ μ δ θ n ω‖ ≤ Real.exp (|θ| * (n * c)) := by
    intro n
    filter_upwards [hMn n, predQuadVar_nonneg hM hd2 hprod n] with ω hMnω hqvω
    change ‖Real.exp (θ * M n ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ n ω)‖ ≤ _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    simp only [Pi.zero_apply] at hqvω
    have h1 : θ * M n ω ≤ |θ| * (n * c) := by
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hMnω (abs_nonneg _)
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (1 + δ) / 2 by linarith) (sq_nonneg θ)) hqvω]
  have hZint_n : ∀ n, Integrable (expProcess M ℱ μ δ θ n) μ := fun n ↦
    (MemLp.of_bound (hZaesm n) _ (hZbd n)).integrable le_rfl
  refine supermartingale_nat (fun n ↦ Real.continuous_exp.comp_stronglyMeasurable (hinner n))
    hZint_n (fun i ↦ ?_)
  · have hfac_meas : StronglyMeasurable[ℱ i]
        (fun ω ↦ Real.exp (θ * M i ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ i ω)
          * Real.exp (-((1 + δ) / 2 * θ ^ 2
            * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)))) :=
      (Real.continuous_exp.comp_stronglyMeasurable (hinner i)).mul
        (Real.continuous_exp.comp_stronglyMeasurable
          (((stronglyAdapted_predictablePart (f := fun k ↦ M k ^ 2) i).sub
            (stronglyAdapted_predictablePart' (f := fun k ↦ M k ^ 2) i)).const_mul
              ((1 + δ) / 2 * θ ^ 2)).neg)
    set factor := fun ω ↦ Real.exp (θ * M i ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ i ω)
      * Real.exp (-((1 + δ) / 2 * θ ^ 2
        * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω))) with hfac
    have hZfac : expProcess M ℱ μ δ θ (i + 1)
        = fun ω ↦ factor ω * Real.exp (θ * (M (i + 1) ω - M i ω)) := by
      funext ω
      simp only [expProcess, hfac, ← Real.exp_add]
      congr 1
      ring
    have hint_exp : Integrable (fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω))) μ := by
      refine (MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
        ((haesm_d i).const_mul θ)) (exp η) ?_).integrable le_rfl
      filter_upwards [hb i] with ω hbω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
    have hZint : Integrable (fun ω ↦ factor ω * Real.exp (θ * (M (i + 1) ω - M i ω))) μ := by
      rw [← hZfac]; exact hZint_n (i + 1)
    have hpull : μ[expProcess M ℱ μ δ θ (i + 1) | ℱ i]
        =ᵐ[μ] fun ω ↦ factor ω * μ[fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω)) | ℱ i] ω := by
      rw [hZfac]
      exact condExp_mul_of_stronglyMeasurable_left hfac_meas hZint hint_exp
    have hmgf := condExp_exp_increment_le hM hη hθ i (hb i) (hd2 i) (hprod i)
    have hfac_nonneg : ∀ ω, 0 ≤ factor ω := fun ω ↦ by
      rw [hfac]; positivity
    filter_upwards [hpull, hmgf] with ω hp hm
    rw [hp]
    calc factor ω * μ[fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω)) | ℱ i] ω
        ≤ factor ω * (1 + (1 + δ) / 2 * θ ^ 2
            * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)) :=
          mul_le_mul_of_nonneg_left hm (hfac_nonneg ω)
      _ ≤ factor ω * Real.exp ((1 + δ) / 2 * θ ^ 2
          * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hfac_nonneg ω)
          have hle := Real.add_one_le_exp ((1 + δ) / 2 * θ ^ 2
            * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω))
          linarith
      _ = expProcess M ℱ μ δ θ i ω := by
          simp only [expProcess, hfac, ← Real.exp_add]
          congr 1
          ring

/-! ### Ville's inequality and Freedman's inequality -/

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
    rw [hs_def, Set.mem_ofPred_eq, le_sup'_iff] at hω
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
      (fun _ ↦ zero_le) hτ_le
    rw [stoppedValue_const] at hos
    simp only [stoppedValue, Pi.neg_apply, integral_neg] at hos ⊢
    linarith
  calc ε • μ s ≤ ENNReal.ofReal (∫ ω in s, stoppedValue Z τ ω ∂μ) := h1
    _ ≤ ENNReal.ofReal (∫ ω, stoppedValue Z τ ω ∂μ) := ENNReal.ofReal_le_ofReal h2
    _ ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂μ) := ENNReal.ofReal_le_ofReal h3

/-- **Freedman's inequality** (before optimizing over `θ`).
For a square-integrable martingale `M` with `M 0 = 0`, increments bounded by `c`, and `0 < θ` with
`θ c ≤ η` (`η` a window for the one-step inequality at level `δ`), and for any `λ, v`,
`μ{ω : ∃ k ≤ n, λ ≤ M_k ω ∧ ⟨M⟩_k ω ≤ v} ≤ exp(-θλ + ½(1+δ)θ² v)`.
On this event the exponential supermartingale reaches `exp(θλ - ½(1+δ)θ² v)`, so Ville's
inequality (`smul_measure_sup_le_integral_zero`) with `E[Z_0] = 1` gives the bound. -/
lemma measure_exists_ge_le_exp [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) {c θ δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2) (hθc : |θ| * c ≤ η) (hθ0 : 0 < θ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) (t v : ℝ) (n : ℕ) :
    μ {ω | ∃ k ≤ n, t ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (exp (-θ * t + (1 + δ) / 2 * θ ^ 2 * v)) := by
  classical
  set Z := expProcess M ℱ μ δ θ with hZdef
  have hZ_super : Supermartingale Z ℱ μ :=
    supermartingale_expProcess hM hM0 hδ hη hθc hb
  have hZ_nonneg : (0 : ℕ → Ω → ℝ) ≤ Z := fun k ω ↦ (Real.exp_pos _).le
  set a := exp (θ * t - (1 + δ) / 2 * θ ^ 2 * v) with hadef
  have ha_pos : 0 < a := Real.exp_pos _
  have hZ0 : ∫ ω, Z 0 ω ∂μ = 1 := by
    have hae : (fun ω ↦ Z 0 ω) =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
      filter_upwards [hM0] with ω h0
      simp only [Pi.zero_apply] at h0
      simp [hZdef, expProcess, predQuadVar_zero, h0]
    rw [integral_congr_ae hae]; simp
  have hsubset : {ω | ∃ k ≤ n, t ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ⊆ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω} := by
    intro ω hω
    obtain ⟨k, hk, hMk, hqvk⟩ := hω
    have hZk : a ≤ Z k ω := by
      rw [hadef, hZdef]
      simp only [expProcess]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_le_mul_of_nonneg_left hMk hθ0.le,
        mul_le_mul_of_nonneg_left hqvk
          (mul_nonneg (show (0 : ℝ) ≤ (1 + δ) / 2 by linarith) (sq_nonneg θ))]
    exact le_trans hZk (Finset.le_sup' (Z · ω) (Finset.mem_range.mpr (by omega)))
  have hville := smul_measure_sup_le_integral_zero hZ_super hZ_nonneg (ε := a.toNNReal) n
  rw [hZ0, ENNReal.ofReal_one, ENNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal a ha_pos.le] at hville
  have hmul : μ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω}
      * ENNReal.ofReal a ≤ 1 := by
    rw [mul_comm]; exact hville
  calc μ {ω | ∃ k ≤ n, t ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ μ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω} :=
        measure_mono hsubset
    _ ≤ (ENNReal.ofReal a)⁻¹ := ENNReal.le_inv_iff_mul_le.mpr hmul
    _ = ENNReal.ofReal (exp (-θ * t + (1 + δ) / 2 * θ ^ 2 * v)) := by
        have hexp : exp (-θ * t + (1 + δ) / 2 * θ ^ 2 * v) = a⁻¹ := by
          rw [hadef, ← Real.exp_neg]; congr 1; ring
        rw [hexp, ENNReal.ofReal_inv_of_pos ha_pos]

/-- **Freedman's inequality with the optimal `θ = λ/((1+δ)v)`** (finite horizon). At the
optimizer the exponent is `-λ²/(2(1+δ)v)`; the admissibility `θ c ≤ η` reads `λ c ≤ (1+δ) v η`. -/
lemma measure_exists_ge_le_exp_optimized [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) {c δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {t v : ℝ} (ht : 0 < t) (hv : 0 < v)
    (hadm : t * c ≤ (1 + δ) * v * η) (n : ℕ) :
    μ {ω | ∃ k ≤ n, t ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (exp (-t ^ 2 / (2 * (1 + δ) * v))) := by
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  set θ := t / ((1 + δ) * v) with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθc : |θ| * c ≤ η := by
    rw [abs_of_pos hθ0, hθdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hadm]
  have h := measure_exists_ge_le_exp hM hM0 hδ hη hθc hθ0 hb t v n
  have hexp : -θ * t + (1 + δ) / 2 * θ ^ 2 * v = -t ^ 2 / (2 * (1 + δ) * v) := by
    have hne : ((1 + δ) * v) ≠ 0 := by positivity
    rw [hθdef]; field_simp; ring
  rwa [hexp] at h

/-- **Freedman's inequality with the optimal `θ`, infinite horizon.** Taking `n → ∞` in
`measure_exists_ge_le_exp_optimized` (the events increase with `n`):
`μ{ω : ∃ k, λ ≤ M_k ω ∧ ⟨M⟩_k ω ≤ v} ≤ exp(-λ²/(2(1+δ)v))`. This is the form fed to
Borel–Cantelli in the laws of the iterated logarithm. -/
lemma measure_exists_ge_le_exp_all [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) {c δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {t v : ℝ} (ht : 0 < t) (hv : 0 < v)
    (hadm : t * c ≤ (1 + δ) * v * η) :
    μ {ω | ∃ k, t ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (exp (-t ^ 2 / (2 * (1 + δ) * v))) := by
  set A : ℕ → Set Ω := fun n ↦ {ω | ∃ k ≤ n, t ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v} with hA
  have hmono : Monotone A := fun a b hab ω ⟨k, hk, h⟩ ↦ ⟨k, hk.trans hab, h⟩
  have hUnion : (⋃ n, A n) = {ω | ∃ k, t ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v} := by
    ext ω
    simp only [hA, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, k, _, h⟩ ↦ ⟨k, h⟩, fun ⟨k, h⟩ ↦ ⟨k, k, le_rfl, h⟩⟩
  rw [← hUnion, hmono.measure_iUnion]
  exact iSup_le fun n ↦
    measure_exists_ge_le_exp_optimized hM hM0 hδ hη hb ht hv hadm n

/-! ### Stopping at a deterministic horizon

Freedman's inequality needs the increments bounded at all times. For a martingale whose increment
bound grows with time (the truncated i.i.d. sums of `HartmanWintner.lean`, the truncated
response martingale of the design analysis), one stops at a deterministic horizon `N`: Mathlib's
`stoppedProcess M (fun _ ↦ N)` is a martingale for the same filtration, its increments vanish past
`N`, and its value and quadratic variation agree with those of `M` at every time `m ≤ N`. -/

/-- Below the horizon, the process stopped at the constant time `N` is the process itself. -/
lemma stoppedProcess_const_of_le (u : ℕ → Ω → ℝ) {N i : ℕ} (h : i ≤ N) :
    stoppedProcess u (fun _ ↦ (N : WithTop ℕ)) i = u i :=
  funext fun _ ↦ stoppedProcess_eq_of_le (WithTop.coe_le_coe.mpr h)

/-- Past the horizon, the process stopped at the constant time `N` is frozen at `u N`. -/
lemma stoppedProcess_const_of_ge (u : ℕ → Ω → ℝ) {N i : ℕ} (h : N ≤ i) :
    stoppedProcess u (fun _ ↦ (N : WithTop ℕ)) i = u N :=
  funext fun ω ↦ by
    rw [stoppedProcess_eq_of_ge (u := u) (τ := fun _ ↦ (N : WithTop ℕ)) (ω := ω)
      (WithTop.coe_le_coe.mpr h), WithTop.untopA_natCast]

/-- **A martingale stopped at a deterministic time is a martingale** for the same filtration:
Mathlib's `Submartingale.stoppedProcess` applied to `M` and `-M` at the constant stopping time. -/
lemma martingale_stoppedProcess_const [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (N : ℕ) :
    Martingale (stoppedProcess M fun _ ↦ (N : WithTop ℕ)) ℱ μ := by
  have hτ : IsStoppingTime ℱ fun _ ↦ (N : WithTop ℕ) := isStoppingTime_const ℱ N
  refine martingale_iff.mpr ⟨?_, hM.submartingale.stoppedProcess hτ⟩
  have h := (hM.neg.submartingale.stoppedProcess hτ).neg
  rwa [show stoppedProcess (-M) (fun _ ↦ (N : WithTop ℕ))
    = -stoppedProcess M fun _ ↦ (N : WithTop ℕ) from rfl, neg_neg] at h

/-- **The quadratic variation is unaffected by stopping, below the horizon.** For `m ≤ N`,
`⟨stoppedProcess M N⟩_m = ⟨M⟩_m`, since every increment in the defining sum has index
`i < m ≤ N`, where the stopped process agrees with `M` at times `i` and `i + 1`. -/
lemma predQuadVar_stoppedProcess_const_of_le (M : ℕ → Ω → ℝ) (N : ℕ) {m : ℕ} (hmN : m ≤ N) :
    predQuadVar (stoppedProcess M fun _ ↦ (N : WithTop ℕ)) ℱ μ m = predQuadVar M ℱ μ m := by
  simp only [predQuadVar, predictablePart]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [stoppedProcess_const_of_le M (by omega : i ≤ N),
    stoppedProcess_const_of_le M (by omega : i + 1 ≤ N)]

/-- **Freedman's inequality with a horizon-local increment bound.** Same conclusion as
`measure_exists_ge_le_exp` (the pre-optimization form, with an *explicit* `θ`), but the increment
bound `|ΔM_i| ≤ c` is required only up to the horizon `N` (`∀ i < N`), and the event is restricted
to times `m ≤ N`. Apply `measure_exists_ge_le_exp` to the process stopped at `N`, whose increments
are globally bounded by `c` (they vanish past `N`) and whose value and quadratic variation agree
with `M`'s at every time `m ≤ N`. The pre-optimization form is essential here: the block LILs use
a *constrained* `θ` (the true optimizer may be inadmissible). -/
lemma measure_exists_ge_le_exp_horizon [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) {c θ δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2) (hc : 0 ≤ c)
    (hθc : |θ| * c ≤ η) (hθ0 : 0 < θ) (t v : ℝ) (N : ℕ)
    (hb : ∀ i < N, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    μ {ω | ∃ m ≤ N, t ≤ M m ω ∧ predQuadVar M ℱ μ m ω ≤ v}
      ≤ ENNReal.ofReal (exp (-θ * t + (1 + δ) / 2 * θ ^ 2 * v)) := by
  have hM'0 : stoppedProcess M (fun _ ↦ (N : WithTop ℕ)) 0 =ᵐ[μ] 0 := by
    rw [stoppedProcess_const_of_le M (Nat.zero_le N)]; exact hM0
  -- Increments of the stopped process are globally bounded by `c`.
  have hb' : ∀ i, ∀ᵐ ω ∂μ, |stoppedProcess M (fun _ ↦ (N : WithTop ℕ)) (i + 1) ω
      - stoppedProcess M (fun _ ↦ (N : WithTop ℕ)) i ω| ≤ c := fun i ↦ by
    rcases lt_or_ge i N with hi | hi
    · rw [stoppedProcess_const_of_le M hi.le, stoppedProcess_const_of_le M (by omega : i + 1 ≤ N)]
      exact hb i hi
    · rw [stoppedProcess_const_of_ge M hi, stoppedProcess_const_of_ge M (by omega : N ≤ i + 1)]
      filter_upwards with ω
      simp only [sub_self, abs_zero]; exact hc
  have hmain := measure_exists_ge_le_exp (martingale_stoppedProcess_const hM N) hM'0 hδ hη hθc
    hθ0 hb' t v N
  -- Below the horizon the two events coincide.
  have hset : {ω | ∃ m ≤ N, t ≤ M m ω ∧ predQuadVar M ℱ μ m ω ≤ v}
      = {ω | ∃ m ≤ N, t ≤ stoppedProcess M (fun _ ↦ (N : WithTop ℕ)) m ω
          ∧ predQuadVar (stoppedProcess M fun _ ↦ (N : WithTop ℕ)) ℱ μ m ω ≤ v} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun m ↦ and_congr_right fun hm ↦ ?_
    rw [stoppedProcess_const_of_le M hm, predQuadVar_stoppedProcess_const_of_le M N hm]
  rw [hset]; exact hmain

/-! ### Borel–Cantelli over a block schedule -/

/-- **Borel–Cantelli step of the one-sided LIL.**
Given a block schedule `(v_k)`, `(λ_k)` of thresholds whose optimized Freedman tail bounds are
summable, `∑_k exp(-λ_k²/(2(1+δ) v_k)) < ∞`, and whose positivity and admissibility
`λ_k c ≤ (1+δ) v_k η` hold for all large `k`, almost surely only finitely many blocks are "bad":
for a.e. `ω`, eventually in `k`, `⟨M⟩_n ≤ v_k ⇒ M_n < λ_k` for all `n`. Admissibility is only
needed eventually because the loglog schedules have optimizer `θ_k → 0`, so it fails on a finite
prefix, where the trivial bound `μ(s_k) ≤ 1` keeps `∑_k μ(s_k)` finite
(`ae_eventually_forall_lt_of_measure_le`). -/
lemma ae_eventually_forall_lt_of_summable [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {c δ η : ℝ} (hδ : 0 ≤ δ) (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {t v : ℕ → ℝ}
    (hadm : ∀ᶠ k in atTop, 0 < t k ∧ 0 < v k ∧ t k * c ≤ (1 + δ) * v k * η)
    (hsum : Summable fun k ↦ exp (-t k ^ 2 / (2 * (1 + δ) * v k))) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ∀ n, predQuadVar M ℱ μ n ω ≤ v k → M n ω < t k := by
  refine ae_eventually_forall_lt_of_measure_le hsum (fun _ ↦ (exp_pos _).le) ?_
  filter_upwards [hadm] with k ⟨htk, hvk, hak⟩
  exact measure_exists_ge_le_exp_all hM hM0 hδ hη hb htk hvk hak


/-- **Borel–Cantelli over time blocks with horizon-local increment bounds.** Given horizons `N_j`,
per-block increment bounds `c_j` valid up to `N_j`, parameters `θ_j > 0` admissible for all large
`j` (`θ_j c_j ≤ η`), thresholds `λ_j` and quadratic-variation levels `v_j` whose Freedman exponents
are summable, `∑_j exp(-θ_j λ_j + ½(1+δ)θ_j² v_j) < ∞`, almost surely for all large `j` and every
`m ≤ N_j`, `⟨M⟩_m ≤ v_j ⇒ M_m < λ_j`. This is the block engine behind the `√(n log n)` LIL for
`√i`-growing increments (`LILTruncation.lean`) and the sharp `√(n log log n)` LIL for growing
increments (`LIL.lean`); they differ only in the schedule `(N_j, c_j, θ_j, λ_j, v_j)`. -/
lemma ae_eventually_forall_le_lt_of_summable [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    {N : ℕ → ℕ} {c t v θ : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j) (hθ0 : ∀ j, 0 < θ j)
    (hadm : ∀ᶠ j in atTop, θ j * c j ≤ η)
    (hb : ∀ j, ∀ i < N j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j)
    (hsum : Summable fun j ↦ exp (-θ j * t j + (1 + δ) / 2 * θ j ^ 2 * v j)) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, ∀ m ≤ N j, predQuadVar M ℱ μ m ω ≤ v j → M m ω < t j := by
  refine ae_eventually_forall_le_lt_of_measure_le hsum (fun _ ↦ (exp_pos _).le) ?_
  filter_upwards [hadm] with j hj
  exact measure_exists_ge_le_exp_horizon hM hM0 hδ hη (hc0 j)
    (by rw [abs_of_pos (hθ0 j)]; exact hj) (hθ0 j) (t j) (v j) (N j) (hb j)

end AlphaRAR
