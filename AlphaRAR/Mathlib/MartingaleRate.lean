/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.QuadraticVariation
public import AlphaRAR.Mathlib.StochasticOrder

/-!
# A square-integrable martingale is `O_p(√n)`

Combining the martingale `L²` growth bound (`integral_sq_le_of_increment_bound`,
the discrete Itô isometry plus telescoping of the quadratic variation) with the
`L²` Chebyshev bound (`isBigOpOne_of_lintegral_sq_le`) gives that a square-integrable
martingale with `M 0 = 0` and increment second moments bounded by `σ²` is
`O_p(√n)`. This is blueprint `cor:mart_Op`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- **A square-integrable martingale is `O_p(√n)`** (blueprint `cor:mart_Op`).
If `M` is a martingale with `M 0 = 0`, square-integrable, whose increments have
second moment `≤ σ²`, then `M n / √n = O_p(1)`, i.e. `M n = O_p(√n)`.

The proof bounds `E[M n²] ≤ σ² n` (`integral_sq_le_of_increment_bound`) and feeds
it to the `L²` Chebyshev inequality (`isBigOpOne_of_lintegral_sq_le`). The rate is
taken as `√(max n 1)` to keep it strictly positive, then transferred to `√n`
(the two agree for `n ≥ 1`, and both vanish at `n = 0` since `M 0 = 0`). -/
lemma isBigOpOne_martingale_div_sqrt [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (hM0 : M 0 =ᵐ[μ] 0)
    (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    (hinc : ∀ n, ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ ≤ σ2) :
    IsBigOpOne μ (fun n ω ↦ M n ω / √n) := by
  have hgrow := integral_sq_le_of_increment_bound hM hM2 hM0 σ2 hinc
  set v : ℕ → ℝ := fun n ↦ √(max (n : ℝ) 1) with hv
  have hmax_pos : ∀ n, (0 : ℝ) < max (n : ℝ) 1 := fun n ↦
    lt_of_lt_of_le one_pos (le_max_right _ _)
  have hvpos : ∀ n, 0 < v n := fun n ↦ Real.sqrt_pos.mpr (hmax_pos n)
  have hvsq : ∀ n, (v n) ^ 2 = max (n : ℝ) 1 := fun n ↦ Real.sq_sqrt (hmax_pos n).le
  have hmeasM : ∀ n, AEMeasurable (M n) μ := fun n ↦
    ((hM.stronglyMeasurable n).mono (ℱ.le n)).measurable.aemeasurable
  -- The integrated bound `∫⁻ (M n)² ≤ ofReal (σ² (v n)²)`.
  have hlin : ∀ n, ∫⁻ ω, ‖M n ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (σ2 * (v n) ^ 2) := by
    intro n
    simp_rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have hnn : 0 ≤ᵐ[μ] fun ω ↦ (M n ω) ^ 2 := Eventually.of_forall fun ω ↦ sq_nonneg _
    rw [← ofReal_integral_eq_lintegral_ofReal (hM2 n).integrable_sq hnn]
    apply ENNReal.ofReal_le_ofReal
    rw [hvsq n]
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      have h0 : ∫ ω, (M 0 ω) ^ 2 ∂μ = 0 := by
        have hae : (fun ω ↦ (M 0 ω) ^ 2) =ᵐ[μ] (0 : Ω → ℝ) := by
          filter_upwards [hM0] with ω hω
          simp only [Pi.zero_apply] at hω ⊢
          rw [hω]; ring
        rw [integral_congr_ae hae]; simp
      rw [h0, Nat.cast_zero]
      exact mul_nonneg hσ2 (le_max_left 0 1)
    · rw [max_eq_left (by exact_mod_cast hn1 : (1 : ℝ) ≤ (n : ℝ))]
      exact hgrow n
  have hOp : IsBigOpOne μ (fun n ω ↦ M n ω / v n) :=
    isBigOpOne_of_lintegral_sq_le hvpos hσ2 hmeasM hlin
  -- Transfer the rate `v = √(max n 1)` to `√n`.
  refine IsBigOpOne.congr (fun n ↦ ?_) hOp
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    filter_upwards [hM0] with ω hω
    simp only [Pi.zero_apply] at hω
    rw [hω]; simp
  · have hvn : v n = √(n : ℝ) := by
      simp only [hv]
      rw [max_eq_left (by exact_mod_cast hn1 : (1 : ℝ) ≤ (n : ℝ))]
    filter_upwards with ω
    rw [hvn]

/-- **A martingale with bounded increments is `O_p(√n)`** (blueprint
`lem:mart_bdd_incr_Op`). If `M` is a martingale with `M 0 = 0` and every increment
satisfies `|ΔM (n+1)| ≤ c` a.e., then `M n / √n = O_p(1)`.

This is the convenient form of `cor:mart_Op` for the assignment martingale: the
bounded increments give all the integrability side conditions (`M n` is a.e. bounded
by `c n`, hence square-integrable) and the increment second moment bound
`E[(ΔM)²] ≤ c² μ(univ)`. -/
lemma isBigOpOne_of_bdd_increments [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (c : ℝ)
    (hΔ : ∀ n, ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c) :
    IsBigOpOne μ (fun n ω ↦ M n ω / √n) := by
  have hmeasM : ∀ n, AEMeasurable (M n) μ := fun n ↦
    ((hM.stronglyMeasurable n).mono (ℱ.le n)).measurable.aemeasurable
  -- "bounded a.e. ⟹ integrable" on a finite measure.
  have bdd_int : ∀ (f : Ω → ℝ) (B : ℝ), AEStronglyMeasurable f μ →
      (∀ᵐ ω ∂μ, |f ω| ≤ B) → Integrable f μ := fun f B hf hb ↦
    (integrable_const B).mono' hf (by filter_upwards [hb] with ω h; rwa [Real.norm_eq_abs])
  -- telescoping bound `|M n| ≤ n c` a.e.
  have hbdd : ∀ n, ∀ᵐ ω ∂μ, |M n ω| ≤ n * c := by
    intro n
    filter_upwards [ae_all_iff.mpr hΔ, hM0] with ω hΔω hM0ω
    simp only [Pi.zero_apply] at hM0ω
    have htel : (∑ k ∈ Finset.range n, (M (k + 1) ω - M k ω)) = M n ω := by
      rw [Finset.sum_range_sub (fun k ↦ M k ω) n, hM0ω, sub_zero]
    calc |M n ω| = |∑ k ∈ Finset.range n, (M (k + 1) ω - M k ω)| := by rw [htel]
      _ ≤ ∑ k ∈ Finset.range n, |M (k + 1) ω - M k ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, c := Finset.sum_le_sum fun k _ ↦ hΔω k
      _ = n * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- integrability of `M n ²`, `(ΔM)²`, and the cross term.
  have hM2 : ∀ n, MemLp (M n) 2 μ := fun n ↦
    (memLp_two_iff_integrable_sq (hmeasM n).aestronglyMeasurable).mpr
      (bdd_int _ (((n : ℝ) * c) ^ 2) ((hmeasM n).pow_const 2).aestronglyMeasurable
        (by filter_upwards [hbdd n] with ω hb
            rw [abs_of_nonneg (sq_nonneg _)]
            exact sq_le_sq' (neg_le_of_abs_le hb) (le_of_abs_le hb)))
  have hd2 : ∀ n, Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ := fun n ↦
    bdd_int _ (c ^ 2) (((hmeasM (n + 1)).sub (hmeasM n)).pow_const 2).aestronglyMeasurable
      (by filter_upwards [hΔ n] with ω hb
          rw [abs_of_nonneg (sq_nonneg _)]
          exact sq_le_sq' (neg_le_of_abs_le hb) (le_of_abs_le hb))
  -- increment second moment `≤ c² μ(univ)`.
  refine isBigOpOne_martingale_div_sqrt hM hM2 hM0 ((μ Set.univ).toReal * c ^ 2)
    (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg c)) (fun n ↦ ?_)
  have hb : (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
    filter_upwards [hΔ n] with ω h
    exact sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
  calc ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ
      ≤ ∫ _, c ^ 2 ∂μ := integral_mono_ae (hd2 n) (integrable_const _) hb
    _ = (μ Set.univ).toReal * c ^ 2 := by rw [integral_const, smul_eq_mul]; rfl

end AlphaRAR
