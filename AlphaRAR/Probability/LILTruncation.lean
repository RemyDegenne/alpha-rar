/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib
import AlphaRAR.Probability.LIL

/-!
# Ingredients for the finite-variance law of the iterated logarithm

This file collects self-contained ingredients for the finite-variance case of the one-sided law
of the iterated logarithm (blueprint chapter `chap:pre_lil`, section "the finite-variance case via
truncation", `lem:lil_truncation`). For a martingale `M_n = ∑_{i<n} ξ_i D_i` with `ξ_i` i.i.d.
centred, `E[ξ_0²] < ∞`, and `D_i ∈ {0,1}` predictable, one truncates `ξ_i` at level `b_i = √i` and
controls the tail, drift, and centred-truncated pieces separately.

## Main results

* `AlphaRAR.ae_eventually_abs_le_of_tsum_ne_top`: the Borel–Cantelli "eventually bounded" step
  (blueprint `lem:trunc_tail_const`): if `∑_i μ{|ξ_i| > b_i} < ∞` then a.s. `|ξ_i| ≤ b_i` for all
  large `i`.
* `AlphaRAR.summable_exp_neg_mul_sqrt`: `∑_k exp(-a √k) < ∞` for `a > 0`.
* `AlphaRAR.summable_block_bound`: `∑_k exp(-(C/2)√k + σ²/4) < ∞` (blueprint
  `lem:trunc_block_summable`), the summability of the per-block Freedman tail bounds.
* `AlphaRAR.abs_truncation_sub_le`: the pointwise bound `|truncation f A x - f x| ≤ (f x)²/A`.
* `AlphaRAR.abs_integral_truncation_le`: `|∫ truncation X A| ≤ (∫ X²)/A` for centred `X`
  (blueprint `lem:trunc_mean_bound`).
* `AlphaRAR.sum_one_div_sqrt_le`: `∑_{i<n} 1/√i ≤ 2√n`, the deterministic core of the drift
  bound (blueprint `lem:trunc_drift`).
-/

open MeasureTheory Filter ProbabilityTheory

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Borel–Cantelli: eventually bounded** (blueprint `lem:trunc_tail_const`, the substance).
If `∑' i, μ {ω : b i < |ξ i ω|} < ∞`, then almost surely `|ξ i ω| ≤ b i` for all large `i`.
Applied with `b_i = √i` and `∑_i P(|ξ_i| > √i) < ∞`, the truncation remainder
`ξ_i 𝟙{|ξ_i| > b_i}` vanishes eventually. -/
theorem ae_eventually_abs_le_of_tsum_ne_top {ξ : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    (h : (∑' i, μ {ω | b i < |ξ i ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ i in atTop, |ξ i ω| ≤ b i := by
  filter_upwards [ae_eventually_notMem h] with ω hω
  filter_upwards [hω] with i hi
  simpa only [Set.mem_setOf_eq, not_lt] using hi

/-- `exp(-a √k)` is summable in `k` for `a > 0`. Since `log = o(√·)`, eventually
`2 log k ≤ a √k`, i.e. `exp(-a√k) ≤ 1/k²`, which is summable. -/
theorem summable_exp_neg_mul_sqrt {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℕ ↦ Real.exp (-a * Real.sqrt k)) := by
  have hcomp : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  -- eventually `log x ≤ (a/2) √x` on `ℝ`, from `log = o(x ^ (1/2))`.
  have hlogR : ∀ᶠ x : ℝ in atTop, Real.log x ≤ (a / 2) * Real.sqrt x := by
    have hlit := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).def
      (show (0 : ℝ) < a / 2 by positivity)
    filter_upwards [hlit, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hx
  -- transfer to `ℕ` and compare with `1/k²`.
  have hev : ∀ᶠ k : ℕ in atTop, Real.exp (-a * Real.sqrt k) ≤ 1 / (k : ℝ) ^ 2 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hlogR, eventually_ge_atTop 1]
      with k hk hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have h2 : 2 * Real.log k ≤ a * Real.sqrt k := by
      have := mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 2)
      rwa [show (2 : ℝ) * (a / 2 * Real.sqrt k) = a * Real.sqrt k from by ring] at this
    have hlk : Real.exp (2 * Real.log (k : ℝ)) = (k : ℝ) ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hkpos, pow_two]
    have hrw : (1 : ℝ) / (k : ℝ) ^ 2 = Real.exp (-(2 * Real.log k)) := by
      rw [Real.exp_neg, hlk, one_div]
    rw [hrw]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  rw [← summable_nat_add_iff N]
  exact Summable.of_nonneg_of_le (fun k ↦ (Real.exp_pos _).le)
    (fun k ↦ hN (k + N) (Nat.le_add_left N k)) ((summable_nat_add_iff N).mpr hcomp)

/-- **Pointwise truncation bound.** `|truncation f A x - f x| ≤ (f x)²/A` for `A > 0`. On the
truncation window `truncation f A x = f x` and the difference is `0`; off it `truncation f A x = 0`,
the difference is `|f x|`, and `|f x| ≥ A` there so `|f x| ≤ (f x)²/A`. -/
theorem abs_truncation_sub_le {α : Type*} (f : α → ℝ) {A : ℝ} (hA : 0 < A) (x : α) :
    |truncation f A x - f x| ≤ f x ^ 2 / A := by
  by_cases h : f x ∈ Set.Ioc (-A) A
  · rw [show truncation f A x = f x from by
      simp only [truncation, Function.comp_apply, Set.indicator_of_mem h, id_eq]]
    simp only [sub_self, abs_zero]; positivity
  · rw [show truncation f A x = 0 from by
      simp only [truncation, Function.comp_apply, Set.indicator_of_notMem h]]
    rw [zero_sub, abs_neg]
    have hAle : A ≤ |f x| := by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at h
      rcases h with h | h
      · exact le_trans (by linarith) (neg_le_abs _)
      · exact le_trans h.le (le_abs_self _)
    rw [le_div_iff₀ hA, ← sq_abs (f x), pow_two]
    exact mul_le_mul_of_nonneg_left hAle (abs_nonneg _)

/-- **Bound on the truncated mean** (blueprint `lem:trunc_mean_bound`).
If `X` is centred (`∫ X = 0`) with `X²` integrable, then `|∫ truncation X A| ≤ (∫ X²)/A` for
`A > 0`. Applied to `ξ_i` with `A = √i` and `∫ ξ_i² = σ²`, this gives `|m_i| ≤ σ²/√i`.
The point is that `∫ truncation X A = ∫(truncation X A - X)` (using `∫ X = 0`) and the pointwise
bound `abs_truncation_sub_le`. -/
theorem abs_integral_truncation_le [IsFiniteMeasure μ] {X : Ω → ℝ} (hint : Integrable X μ)
    (hX2 : Integrable (fun ω ↦ X ω ^ 2) μ) (hX0 : ∫ ω, X ω ∂μ = 0) {A : ℝ} (hA : 0 < A) :
    |∫ ω, truncation X A ω ∂μ| ≤ (∫ ω, X ω ^ 2 ∂μ) / A := by
  have htrunc_int : Integrable (truncation X A) μ := hint.aestronglyMeasurable.integrable_truncation
  have heq : ∫ ω, truncation X A ω ∂μ = ∫ ω, (truncation X A ω - X ω) ∂μ := by
    rw [integral_sub htrunc_int hint, hX0, sub_zero]
  calc |∫ ω, truncation X A ω ∂μ|
      = |∫ ω, (truncation X A ω - X ω) ∂μ| := by rw [heq]
    _ ≤ ∫ ω, |truncation X A ω - X ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, X ω ^ 2 / A ∂μ :=
        integral_mono (htrunc_int.sub hint).abs (hX2.div_const A)
          (fun ω ↦ abs_truncation_sub_le X hA ω)
    _ = (∫ ω, X ω ^ 2 ∂μ) / A := integral_div A _

/-- `∑_{i<n} 1/√i ≤ 2√n` (with the convention `1/√0 = 0`). The deterministic core of the drift
bound `lem:trunc_drift`: since `|m_i| ≤ σ²/√i`, the drift `∑ m_i D_i` is `O(√n)` (and `O(√N)`
after restricting to the sampled indices). The key step is `1/√(x+1) ≤ 2(√(x+1) - √x)`. -/
theorem sum_one_div_sqrt_le (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / Real.sqrt i ≤ 2 * Real.sqrt n := by
  have hkey : ∀ x : ℝ, 0 ≤ x → 1 / Real.sqrt (x + 1) ≤ 2 * (Real.sqrt (x + 1) - Real.sqrt x) := by
    intro x hx
    have hsq1 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
    have hsq2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have hsp : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_iff₀ hsp]
    nlinarith [sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x), hsq1, hsq2, Real.sqrt_nonneg x]
  have haux : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), 1 / Real.sqrt i ≤ 2 * Real.sqrt m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linarith [hkey (k : ℝ) (Nat.cast_nonneg k), ih]
  cases n with
  | zero => simp
  | succ m =>
    refine le_trans (haux m) ?_
    have : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ m)
    push_cast at this ⊢
    linarith

/-- **Summability of the per-block Freedman bounds** (blueprint `lem:trunc_block_summable`).
For `C > 0`, `∑_k exp(-(C/2)√k + σ²/4) < ∞`; this is what makes Borel–Cantelli applicable in the
core step `lem:trunc_block` of the finite-variance LIL. -/
theorem summable_block_bound {C σ : ℝ} (hC : 0 < C) :
    Summable (fun k : ℕ ↦ Real.exp (-(C / 2) * Real.sqrt k + σ ^ 2 / 4)) :=
  ((summable_exp_neg_mul_sqrt (a := C / 2) (by positivity)).mul_right
    (Real.exp (σ ^ 2 / 4))).congr fun k ↦ (Real.exp_add _ _).symm

end AlphaRAR
