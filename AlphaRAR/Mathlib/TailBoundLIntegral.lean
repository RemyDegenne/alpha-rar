/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# An `L¹` bound from an inverse-square tail bound

If a nonnegative random variable `Y` on a probability space has the inverse-square tail bound
`μ {Y ≥ t} ≤ B / t²` for every `t > 0`, then `∫⁻ Y ≤ 2√B`.

This is the analytic core of Doob's `L²` maximal inequality: the weak-type maximal inequality
supplies exactly such a tail bound for the maximum of a martingale (with `B` the terminal second
moment), and this lemma turns it into the `L¹` bound on the maximum. The argument is the classical
`E[Y] = ∫₀^∞ P(Y ≥ t) dt ≤ A + B/A` optimized at `A = √B` (layer cake, split at `A`).

## Main result

* `MeasureTheory.lintegral_le_two_mul_sqrt_of_meas_ge_le`.
-/

open Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **`L¹` bound from an inverse-square tail bound.** If `Y ≥ 0` satisfies `μ {Y ≥ t} ≤ B / t²`
for all `t > 0` (with `B ≥ 0`), then `∫⁻ Y ≤ 2√B`. The analytic core of Doob's `L²` maximal
inequality. -/
lemma lintegral_le_two_mul_sqrt_of_meas_ge_le {Y : Ω → ℝ} (hYnn : 0 ≤ᵐ[μ] Y)
    (hYmeas : AEMeasurable Y μ) {B : ℝ} (hB : 0 ≤ B)
    (htail : ∀ t : ℝ, 0 < t → μ {ω | t ≤ Y ω} ≤ ENNReal.ofReal (B / t ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ ≤ ENNReal.ofReal (2 * √B) := by
  have hpow : ∀ t : ℝ, 0 < t → B * t ^ (-2 : ℝ) = B / t ^ 2 := by
    intro t ht
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast,
      ← div_eq_mul_inv]
  rw [lintegral_eq_lintegral_meas_le μ hYnn hYmeas]
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · -- `B = 0`: the tail measures all vanish, so the layer-cake integral is `0`.
    have hzero : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), μ {ω | t ≤ Y ω} ≤ 0 := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht ↦ ?_)
      have := htail t ht
      rwa [← hB0, zero_div, ENNReal.ofReal_zero] at this
    calc ∫⁻ t in Ioi 0, μ {ω | t ≤ Y ω}
        ≤ ∫⁻ _t in Ioi (0 : ℝ), 0 := lintegral_mono_ae hzero
      _ = 0 := lintegral_zero
      _ ≤ ENNReal.ofReal (2 * √B) := by positivity
  · -- `B > 0`: split `Ioi 0 = Ioc 0 A ∪ Ioi A` at `A = √B`.
    set A : ℝ := √B with hAdef
    have hApos : 0 < A := Real.sqrt_pos.mpr hBpos
    have hunion : Ioi (0 : ℝ) = Ioc 0 A ∪ Ioi A := (Ioc_union_Ioi_eq_Ioi hApos.le).symm
    have hdisj : Disjoint (Ioc (0 : ℝ) A) (Ioi A) := by
      simp only [Set.disjoint_left, mem_Ioc, mem_Ioi]
      rintro x ⟨_, hxA⟩ hxA'
      exact absurd hxA (not_le.mpr hxA')
    rw [hunion, lintegral_union measurableSet_Ioi hdisj]
    -- Part 1: the head `(0, A]` contributes at most `A` (probabilities `≤ 1`).
    have hpart1 : ∫⁻ t in Ioc 0 A, μ {ω | t ≤ Y ω} ≤ ENNReal.ofReal A := by
      calc ∫⁻ t in Ioc 0 A, μ {ω | t ≤ Y ω}
          ≤ ∫⁻ _t in Ioc (0 : ℝ) A, 1 :=
            lintegral_mono_ae (ae_of_all _ fun t ↦ prob_le_one)
        _ = ENNReal.ofReal A := by
            rw [setLIntegral_one, Real.volume_Ioc, sub_zero]
    -- Part 2: the tail `(A, ∞)` contributes at most `∫_A^∞ B/t² = B/A`.
    have hAne : A ≠ 0 := ne_of_gt hApos
    have hintegrable : IntegrableOn (fun t ↦ B / t ^ 2) (Ioi A) := by
      have h1 : IntegrableOn (fun t : ℝ ↦ B * t ^ (-2 : ℝ)) (Ioi A) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hApos).const_mul B
      exact h1.congr_fun (fun t ht ↦ hpow t (hApos.trans (mem_Ioi.mp ht))) measurableSet_Ioi
    have hint : ∫ t in Ioi A, B / t ^ 2 = B / A := by
      rw [setIntegral_congr_fun measurableSet_Ioi
          (fun t ht ↦ (hpow t (hApos.trans (mem_Ioi.mp ht))).symm),
        integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hApos,
        show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    have hpart2 : ∫⁻ t in Ioi A, μ {ω | t ≤ Y ω} ≤ ENNReal.ofReal (B / A) := by
      calc ∫⁻ t in Ioi A, μ {ω | t ≤ Y ω}
          ≤ ∫⁻ t in Ioi A, ENNReal.ofReal (B / t ^ 2) :=
            lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _
              fun t ht ↦ htail t (hApos.trans (mem_Ioi.mp ht))))
        _ = ENNReal.ofReal (∫ t in Ioi A, B / t ^ 2) :=
            (ofReal_integral_eq_lintegral_ofReal hintegrable
              (ae_of_all _ fun t ↦ div_nonneg hB (sq_nonneg t))).symm
        _ = ENNReal.ofReal (B / A) := by rw [hint]
    -- Combine: `A + B/A = 2√B`.
    have hBA : B / A = A := by
      rw [hAdef, div_eq_iff (ne_of_gt hApos), Real.mul_self_sqrt hB]
    calc (∫⁻ t in Ioc 0 A, μ {ω | t ≤ Y ω}) + ∫⁻ t in Ioi A, μ {ω | t ≤ Y ω}
        ≤ ENNReal.ofReal A + ENNReal.ofReal (B / A) := add_le_add hpart1 hpart2
      _ = ENNReal.ofReal (2 * √B) := by
          rw [← ENNReal.ofReal_add hApos.le (div_nonneg hB hApos.le), hBA]
          congr 1; ring

end MeasureTheory
