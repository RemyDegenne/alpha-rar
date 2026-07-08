/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Martingale.Convergence
import AlphaRAR.Mathlib.Kronecker
import AlphaRAR.Probability.QuadraticVariation

/-!
# Strong law of large numbers for martingales

If a square-integrable martingale `M` has `M 0 = 0` and increment variances summable against `k⁻²`
(in particular for uniformly bounded increments), then `M n / n → 0` almost everywhere. Mathlib has
the i.i.d. strong law but no martingale version; the classical route below is Kolmogorov's: reduce
to the a.s. convergence of the weighted series `∑ ΔM_k / k` via the `L²` martingale convergence
theorem, then apply Kronecker's lemma (`AlphaRAR.kronecker`).

## Main results

* `AlphaRAR.martingale_ae_tendsto_of_eLpNorm_two_le`: an `L²`-bounded martingale converges a.e.
-/

open MeasureTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M S : ℕ → Ω → ℝ}

/-- **An `L²`-bounded martingale converges almost everywhere** (blueprint `lem:slln_l2_conv`).
If `S` is a martingale with `eLpNorm (S n) 2 μ ≤ C` for all `n`, then `S n` converges a.e. to a
(finite) limit. This is the `L²`- (hence `L¹`-) bounded martingale convergence theorem: on a
probability space `‖·‖₁ ≤ ‖·‖₂`, so the uniform `L²` bound gives a uniform `L¹` bound, and Mathlib's
`Submartingale.exists_ae_tendsto_of_bdd` applies. -/
theorem martingale_ae_tendsto_of_eLpNorm_two_le [IsProbabilityMeasure μ]
    (hS : Martingale S ℱ μ) {C : ℝ≥0} (hbdd : ∀ n, eLpNorm (S n) 2 μ ≤ C) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ S n ω) atTop (𝓝 c) :=
  hS.submartingale.exists_ae_tendsto_of_bdd (R := C) fun n ↦
    le_trans (eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) one_le_two
      ((hS.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) (hbdd n)

/-- Integral form of `lem:slln_l2_conv`: a martingale `S` with square-integrable values and
`∫ (S n)² ∂μ ≤ C` for all `n` converges a.e. to a finite limit. The uniform second-moment bound
gives `eLpNorm (S n) 2 μ ≤ √C`, so `martingale_ae_tendsto_of_eLpNorm_two_le` applies. -/
theorem martingale_ae_tendsto_of_integral_sq_le [IsProbabilityMeasure μ]
    (hS : Martingale S ℱ μ) (hS2 : ∀ n, Integrable (fun ω ↦ (S n ω) ^ 2) μ)
    {C : ℝ} (hbdd : ∀ n, ∫ ω, (S n ω) ^ 2 ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ S n ω) atTop (𝓝 c) := by
  have hCnn : 0 ≤ C := le_trans (integral_nonneg fun ω ↦ sq_nonneg _) (hbdd 0)
  refine martingale_ae_tendsto_of_eLpNorm_two_le hS (C := (Real.sqrt C).toNNReal) fun n ↦ ?_
  have haesm : AEStronglyMeasurable (S n) μ :=
    ((hS.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable
  have hmem : MemLp (S n) 2 μ := (memLp_two_iff_integrable_sq haesm).mpr (hS2 n)
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num)]
  have h2 : ((2 : ℝ≥0∞).toReal)⁻¹ = 1 / 2 := by norm_num
  have hnorm : (fun ω ↦ ‖S n ω‖ ^ ((2 : ℝ≥0∞).toReal)) = fun ω ↦ (S n ω) ^ 2 := by
    funext ω; rw [show ((2 : ℝ≥0∞).toReal) = 2 by norm_num, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hnorm, h2, ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hbdd n))

/-- The **weighted increment series** `S n = ∑_{k<n} (M (k+1) − M k)/(k+1)` of a martingale `M` is
itself a martingale (part of blueprint `lem:slln_weighted`). Each increment `ΔS_n = ΔM_n/(n+1)` is
a scaled martingale difference, so `𝔼[ΔS_n ∣ ℱ_n] = (n+1)⁻¹ 𝔼[ΔM_n ∣ ℱ_n] = 0`. -/
theorem martingale_weightedSeries [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) :
    Martingale (fun n ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) ℱ μ := by
  have hint : ∀ n, Integrable (M n) μ := hM.integrable
  have hadapt : ∀ n, StronglyMeasurable[ℱ n]
      (fun ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) := fun n ↦
    Finset.stronglyMeasurable_fun_sum _ fun k hk ↦
      (((hM.stronglyMeasurable (k + 1)).mono (ℱ.mono (by rw [Finset.mem_range] at hk; omega))).sub
        ((hM.stronglyMeasurable k).mono (ℱ.mono (by rw [Finset.mem_range] at hk; omega)))).div
        stronglyMeasurable_const
  have hSint : ∀ n, Integrable (fun ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) μ :=
    fun n ↦ integrable_finsetSum _ fun k _ ↦ ((hint (k + 1)).sub (hint k)).div_const _
  refine martingale_nat hadapt hSint (fun n ↦ ?_)
  -- `S n =ᵐ 𝔼[S (n+1) ∣ ℱ n]`: split off the last increment, which conditions to `0`.
  have hSsucc : (fun ω ↦ ∑ k ∈ range (n + 1), (M (k + 1) ω - M k ω) / ((k : ℝ) + 1))
      = (fun ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1))
        + ((n : ℝ) + 1)⁻¹ • (M (n + 1) - M n) := by
    funext ω; simp only [Finset.sum_range_succ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]; ring
  have hincr : Integrable (((n : ℝ) + 1)⁻¹ • (M (n + 1) - M n)) μ :=
    (((hint (n + 1)).sub (hint n))).smul _
  have hself := condExp_of_stronglyMeasurable (ℱ.le n) (hadapt n) (hSint n)
  have hzero : μ[((n : ℝ) + 1)⁻¹ • (M (n + 1) - M n) | ℱ n] =ᵐ[μ] 0 := by
    have hd : μ[M (n + 1) - M n | ℱ n] =ᵐ[μ] 0 := by
      refine (condExp_sub (hint (n + 1)) (hint n) _).trans ?_
      filter_upwards [hM.condExp_ae_eq (Nat.le_succ n), hM.condExp_ae_eq (le_refl n)]
        with ω hω1 hω2
      simp only [Pi.sub_apply, Pi.zero_apply, hω1, hω2, sub_self]
    refine (condExp_smul _ _ _).trans ?_
    filter_upwards [hd] with ω hω
    simp only [Pi.smul_apply, Pi.zero_apply, hω, smul_zero]
  rw [hSsucc]
  filter_upwards [condExp_add (hSint n) hincr (ℱ n), hzero] with ω ha h2
  rw [ha, Pi.add_apply, congrFun hself ω, h2, Pi.zero_apply, add_zero]

/-- **Martingale SLLN** (the a.e. convergence `M n / n → 0`), given a uniform second-moment bound on
the weighted increment series `S n = ∑_{k<n} (M (k+1) − M k)/(k+1)`. Blueprint `thm:mart_slln`,
modulo the identity `∫ (S n)² = ∑_{k<n} 𝔼[(ΔM_k)²]/(k+1)²` (which turns the summability hypothesis
into the bound `hbdd` below). By `martingale_weightedSeries` and
`martingale_ae_tendsto_of_integral_sq_le`, `S n` converges a.e.; Kronecker's lemma
(`AlphaRAR.kronecker'`, applied pathwise with `x_k = ΔM_k/(k+1)`) then gives `M n / n → 0`, since
`∑_{k<n} (k+1)·x_k = ∑_{k<n} ΔM_k = M n` (using `M 0 = 0`). -/
theorem martingale_div_atTop_ae_tendsto_zero [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    (hS2 : ∀ n, Integrable
      (fun ω ↦ (∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) ^ 2) μ)
    {C : ℝ} (hbdd : ∀ n, ∫ ω, (∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) ^ 2 ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ M n ω / n) atTop (𝓝 0) := by
  have hconv := martingale_ae_tendsto_of_integral_sq_le (martingale_weightedSeries hM) hS2 hbdd
  filter_upwards [hconv, hM0] with ω hcω h0
  obtain ⟨c, hc⟩ := hcω
  refine (kronecker' hc).congr' (Eventually.of_forall fun n ↦ ?_)
  have hterm : ∀ k ∈ range n, ((k : ℝ) + 1) * ((M (k + 1) ω - M k ω) / ((k : ℝ) + 1))
      = (fun j ↦ M j ω) (k + 1) - (fun j ↦ M j ω) k := fun k _ ↦ by
    rw [mul_div_cancel₀ _ (by positivity)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j ↦ M j ω) n, h0, Pi.zero_apply,
    sub_zero]
  simp only [div_eq_inv_mul]

/-- **Martingale SLLN for bounded increments** (blueprint `cor:mart_slln_bounded`). If `M` is a
martingale with `M 0 = 0` and a.e. uniformly bounded increments `|M (k+1) − M k| ≤ c`, then
`M n / n → 0` almost everywhere.

The bounded increments make everything square-integrable, and give the orthogonality bound
`∫ (S n)² = ∑_{k<n} ∫ (ΔM_k / (k+1))² ≤ c² ∑_{k<n} (k+1)⁻² ≤ c² ∑' (k+1)⁻² < ∞`
on the weighted increment series `S`, via the discrete Itô isometry
(`integral_sq_eq_integral_predQuadVar`) and the telescoping of its predictable quadratic variation
(`integral_predQuadVar_succ_sub`). `martingale_div_atTop_ae_tendsto_zero` then applies. -/
theorem martingale_div_atTop_ae_tendsto_zero_of_bdd [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) {c : ℝ}
    (hb : ∀ k, ∀ᵐ ω ∂μ, |M (k + 1) ω - M k ω| ≤ c) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ M n ω / n) atTop (𝓝 0) := by
  classical
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1) with hSdef
  have hSmart : Martingale S ℱ μ := martingale_weightedSeries hM
  have hS0 : S 0 =ᵐ[μ] 0 := by filter_upwards with ω; simp [hSdef]
  -- Each increment `ΔM_k` is square-integrable (bounded on a probability space).
  have haesm : ∀ k, AEStronglyMeasurable (fun ω ↦ M (k + 1) ω - M k ω) μ := fun k ↦
    (((hM.stronglyMeasurable (k + 1)).mono (ℱ.le _)).sub
      ((hM.stronglyMeasurable k).mono (ℱ.le _))).aestronglyMeasurable
  have hdmem : ∀ k, MemLp (fun ω ↦ M (k + 1) ω - M k ω) 2 μ := fun k ↦
    MemLp.of_bound (haesm k) c (by filter_upwards [hb k] with ω h; rwa [Real.norm_eq_abs])
  -- The scaled increments `ΔS_k = ΔM_k / (k+1)`, the series `S n`, and its increments are `L²`.
  have hDmem : ∀ k, MemLp (fun ω ↦ (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) 2 μ := fun k ↦ by
    simpa only [div_eq_inv_mul] using (hdmem k).const_mul ((k : ℝ) + 1)⁻¹
  have hSmem : ∀ n, MemLp (S n) 2 μ := fun n ↦
    memLp_finsetSum (Finset.range n) fun k _ ↦ hDmem k
  have hS2 : ∀ n, Integrable (fun ω ↦ (S n ω) ^ 2) μ := fun n ↦ (hSmem n).integrable_sq
  have hd2 : ∀ k, Integrable (fun ω ↦ (S (k + 1) ω - S k ω) ^ 2) μ := fun k ↦
    ((hSmem (k + 1)).sub (hSmem k)).integrable_sq
  have hprod : ∀ k, Integrable (S k * (S (k + 1) - S k)) μ := fun k ↦
    (hSmem k).integrable_mul ((hSmem (k + 1)).sub (hSmem k))
  -- Orthogonality / discrete Itô isometry: `∫ (S n)² = ∑_{k<n} ∫ (S (k+1) − S k)²`.
  have hsqeq : ∀ n, ∫ ω, (S n ω) ^ 2 ∂μ
      = ∑ k ∈ range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ := by
    intro n
    rw [integral_sq_eq_integral_predQuadVar hSmart.stronglyAdapted hS2 hS0 n]
    have e : ∑ k ∈ range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        = ∑ k ∈ range n,
            ((∫ ω, predQuadVar S ℱ μ (k + 1) ω ∂μ) - ∫ ω, predQuadVar S ℱ μ k ω ∂μ) :=
      Finset.sum_congr rfl fun k _ ↦
        (integral_predQuadVar_succ_sub hSmart hS2 k (hd2 k) (hprod k)).symm
    rw [e, Finset.sum_range_sub (fun k ↦ ∫ ω, predQuadVar S ℱ μ k ω ∂μ) n]
    simp [predQuadVar_zero]
  -- The summability `∑ (k+1)⁻² < ∞`.
  have hsummable : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  -- Per-increment bound `∫ (S (k+1) − S k)² ≤ c² / (k+1)²`.
  have hbound : ∀ k, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ ≤ c ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hinc : ∀ ω, S (k + 1) ω - S k ω = (M (k + 1) ω - M k ω) / ((k : ℝ) + 1) := by
      intro ω; simp only [hSdef, Finset.sum_range_succ]; ring
    have hsqle : ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ ≤ c ^ 2 := by
      have hle : (fun ω ↦ (M (k + 1) ω - M k ω) ^ 2) ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
        filter_upwards [hb k] with ω h
        obtain ⟨h1, h2⟩ := abs_le.mp h
        nlinarith [h1, h2]
      calc ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ
          ≤ ∫ _, c ^ 2 ∂μ := integral_mono_ae (hdmem k).integrable_sq (integrable_const _) hle
        _ = c ^ 2 := by simp
    have hpt : ∀ ω, (S (k + 1) ω - S k ω) ^ 2
        = (M (k + 1) ω - M k ω) ^ 2 / ((k : ℝ) + 1) ^ 2 := fun ω ↦ by
      rw [hinc ω, div_pow]
    calc ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        = ∫ ω, (M (k + 1) ω - M k ω) ^ 2 / ((k : ℝ) + 1) ^ 2 ∂μ :=
          integral_congr_ae (.of_forall hpt)
      _ = (∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ) / ((k : ℝ) + 1) ^ 2 := integral_div _ _
      _ ≤ c ^ 2 / ((k : ℝ) + 1) ^ 2 := by gcongr
  -- Assemble the uniform second-moment bound on `S`.
  have hbdd : ∀ n, ∫ ω, (S n ω) ^ 2 ∂μ ≤ c ^ 2 * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
    intro n
    rw [hsqeq n]
    calc ∑ k ∈ range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        ≤ ∑ k ∈ range n, c ^ 2 / ((k : ℝ) + 1) ^ 2 := Finset.sum_le_sum fun k _ ↦ hbound k
      _ = c ^ 2 * ∑ k ∈ range n, 1 / ((k : ℝ) + 1) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_one_div]
      _ ≤ c ^ 2 * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
          gcongr
          exact hsummable.sum_le_tsum (Finset.range n) fun i _ ↦ by positivity
  exact martingale_div_atTop_ae_tendsto_zero hM hM0 hS2 hbdd

end AlphaRAR
