/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Summability of tail measures (layer cake)

Mathlib's `ProbabilityTheory.tsum_prob_mem_Ioi_lt_top` gives `∑' i, ℙ {X > i} < ∞` for a
nonnegative integrable `X`, but only for the canonical measure `ℙ` of a `MeasureSpace`. We record
the same fact for a general finite measure `μ`, which is what is needed to apply it to a reward
law `ν k` (rather than the ambient probability measure). The proof is the elementary layer-cake
bound `∑_i μ{X > i} = ∫⁻ ∑_i 𝟙{X > i} ≤ ∫⁻ (X + 1) = ofReal(∫ X) + μ(univ) < ∞`, using
`∑_i 𝟙{i < X ω} = ⌈X ω⌉₊ ≤ X ω + 1`.

This belongs upstream in Mathlib (a `μ`-general version of `tsum_prob_mem_Ioi_lt_top`).
-/

open MeasureTheory Filter Finset

open scoped ENNReal NNReal

namespace AlphaRAR

/-- **Layer-cake summability of tail measures, general measure.** For a finite measure `μ` and a
measurable, integrable, nonnegative `X`, `∑' i, μ {ω : (i : ℝ) < X ω} < ∞`. -/
lemma tsum_measure_Ioi_ne_top {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (hint : Integrable X μ) (hnn : 0 ≤ X) :
    (∑' i : ℕ, μ {ω | (i : ℝ) < X ω}) ≠ ∞ := by
  have hmeas : ∀ i : ℕ, MeasurableSet {ω | (i : ℝ) < X ω} :=
    fun i ↦ measurableSet_lt measurable_const hX
  -- Rewrite each tail measure as a `lintegral` of an indicator, then swap sum and integral.
  have hμ : ∀ i : ℕ, μ {ω | (i : ℝ) < X ω}
      = ∫⁻ ω, {ω | (i : ℝ) < X ω}.indicator (1 : Ω → ℝ≥0∞) ω ∂μ :=
    fun i ↦ (lintegral_indicator_one (hmeas i)).symm
  rw [tsum_congr hμ,
    ← lintegral_tsum fun i ↦ (measurable_one.indicator (hmeas i)).aemeasurable]
  -- Pointwise: `∑_i 𝟙{i < X ω} = ⌈X ω⌉₊ ≤ ofReal(X ω) + 1`.
  have hptw : ∀ ω, (∑' i : ℕ, {ω | (i : ℝ) < X ω}.indicator (1 : Ω → ℝ≥0∞) ω)
      ≤ ENNReal.ofReal (X ω) + 1 := by
    intro ω
    have hindic : ∀ i : ℕ, {ω | (i : ℝ) < X ω}.indicator (1 : Ω → ℝ≥0∞) ω
        = if i < ⌈X ω⌉₊ then 1 else 0 := by
      intro i
      by_cases hi : (i : ℝ) < X ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | (i : ℝ) < X ω} from hi), Pi.one_apply,
          if_pos (Nat.lt_ceil.mpr hi)]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | (i : ℝ) < X ω} from hi),
          if_neg fun h ↦ hi (Nat.lt_ceil.mp h)]
    simp_rw [hindic]
    rw [tsum_eq_sum (s := Finset.range ⌈X ω⌉₊)
      fun i hi ↦ if_neg (by rw [Finset.mem_range] at hi; omega)]
    rw [Finset.sum_congr rfl fun i hi ↦ if_pos (Finset.mem_range.mp hi), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    calc (⌈X ω⌉₊ : ℝ≥0∞) = ENNReal.ofReal ⌈X ω⌉₊ := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (X ω + 1) := ENNReal.ofReal_le_ofReal (Nat.ceil_lt_add_one (hnn ω)).le
      _ = ENNReal.ofReal (X ω) + 1 := by
          rw [ENNReal.ofReal_add (hnn ω) zero_le_one, ENNReal.ofReal_one]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hptw)
  rw [lintegral_add_right _ measurable_const, lintegral_one,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, measure_ne_top _ _⟩

/-- **Summable truncation tail** at the law level (blueprint `lem:trunc_tail_summable`).
For a finite measure `ρ` on `ℝ` with finite second central moment `∫ (x-θ)² ∂ρ < ∞`,
`∑' i, ρ {x : √i < |x - θ|} < ∞`. Since `√i < |x-θ| ⟺ i < (x-θ)²`, this is
`tsum_measure_Ioi_ne_top` for `X = (· - θ)²`. Applied to a reward law `ρ = ν k` (with
`θ = θ_k`) this bounds `∑_i ν_k(|· - θ_k| > √i)`. -/
lemma tsum_measure_abs_sub_gt_sqrt_ne_top {ρ : Measure ℝ} [IsFiniteMeasure ρ] (θ : ℝ)
    (hρ2 : Integrable (fun x ↦ (x - θ) ^ 2) ρ) :
    (∑' i : ℕ, ρ {x | Real.sqrt i < |x - θ|}) ≠ ∞ := by
  have hset : ∀ i : ℕ, {x | Real.sqrt i < |x - θ|} = {x | (i : ℝ) < (x - θ) ^ 2} := by
    intro i
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have := mul_self_lt_mul_self (Real.sqrt_nonneg (i : ℝ)) h
      rw [Real.mul_self_sqrt (Nat.cast_nonneg i), abs_mul_abs_self, ← pow_two] at this
      exact this
    · intro h
      have h2 : Real.sqrt i < Real.sqrt ((x - θ) ^ 2) := Real.sqrt_lt_sqrt (Nat.cast_nonneg i) h
      rwa [Real.sqrt_sq_eq_abs] at h2
  simp_rw [hset]
  exact tsum_measure_Ioi_ne_top (by fun_prop) hρ2 fun x ↦ sq_nonneg _

/-- **Summable truncation tail with the closed window.** The `≤` variant of
`tsum_measure_abs_sub_gt_sqrt_ne_top`: `∑' i, ρ {x : √i ≤ |x - θ|} < ∞`. This is what is needed for
the sampled tail term of the finite-variance LIL, because Mathlib's `truncation` uses the
left-open window `Ioc (-A) A`, so a value *equal* to `√i` in absolute value can still be off the
window. Derived from the strict version by shifting the index: for `i ≥ 1`,
`√i ≤ |x-θ| ⟹ √(i-1) < |x-θ|`, and the `i = 0` term is `ρ` of a set, hence finite. -/
lemma tsum_measure_abs_sub_ge_sqrt_ne_top {ρ : Measure ℝ} [IsFiniteMeasure ρ] (θ : ℝ)
    (hρ2 : Integrable (fun x ↦ (x - θ) ^ 2) ρ) :
    (∑' i : ℕ, ρ {x | Real.sqrt i ≤ |x - θ|}) ≠ ∞ := by
  have hbound : ∀ i : ℕ,
      ρ {x | Real.sqrt (↑(i + 1)) ≤ |x - θ|} ≤ ρ {x | Real.sqrt i < |x - θ|} := by
    intro i
    refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact lt_of_lt_of_le
      (Real.sqrt_lt_sqrt (Nat.cast_nonneg i) (by exact_mod_cast Nat.lt_succ_self i)) hx
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ?_⟩
  exact ne_top_of_le_ne_top (tsum_measure_abs_sub_gt_sqrt_ne_top θ hρ2)
    (ENNReal.tsum_le_tsum hbound)

end AlphaRAR
