/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib

/-!
# Conditional expectation from a conditional distribution

If `Y` has conditional distribution `κ` given `X` (`HasCondDistrib Y X κ P`), then the
conditional expectation of a (measurable) function `g` of `Y` given `σ(X)` is the integral of
`g` against the kernel evaluated at `X`:
`P[g ∘ Y | σ(X)] =ᵐ[P] fun ω ↦ ∫ y, g y ∂(κ (X ω))`.

This packages the two ingredients `condExp_ae_eq_integral_condDistrib` (conditional expectation
as a `condDistrib` integral) and `HasCondDistrib.condDistrib_eq` (`condDistrib` equals `κ`) into a
single reusable statement.

These belong in Mathlib next to `HasCondDistrib`.

## Main results

* `ProbabilityTheory.HasCondDistrib.condExp_comp_eq`: conditional expectation of `g ∘ Y`.
* `ProbabilityTheory.memLp_two_of_hasCondDistrib`: membership in `L²` from uniformly bounded
  conditional second moments.
-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω β 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → β} {Y : Ω → 𝓨}
  {κ : Kernel β 𝓨} [IsFiniteKernel κ]

/-- **Conditional expectation of a function of `Y` from its conditional distribution.**
If `Y` has conditional distribution `κ` given `X` under `P`, then the conditional expectation of
`g ∘ Y` given `σ(X)` is the integral of `g` against `κ` evaluated at `X`:
`P[g ∘ Y | σ(X)] =ᵐ[P] fun ω ↦ ∫ y, g y ∂(κ (X ω))`. -/
lemma HasCondDistrib.condExp_comp_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (h : HasCondDistrib Y X κ P) (hX : Measurable X)
    {g : 𝓨 → F} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y ω)) P) :
    P[fun ω ↦ g (Y ω) | mβ.comap X] =ᵐ[P] fun ω ↦ ∫ y, g y ∂(κ (X ω)) := by
  refine (condExp_ae_eq_integral_condDistrib hX h.aemeasurable_snd hg hint).trans ?_
  filter_upwards [ae_of_ae_map hX.aemeasurable h.condDistrib_eq] with ω hω
  rw [hω]

/-- **A conditionally-distributed real random variable is in `L²` as soon as its conditional laws
have uniformly bounded second moments.** Disintegrating,
`∫⁻ ‖f‖ₑ² dP = ∫⁻ x, (∫⁻ ‖y‖ₑ² dκ x) d(P.map X) ≤ C`, since `P.map X` is a probability measure. -/
lemma memLp_two_of_hasCondDistrib {𝓧 : Type*} [MeasurableSpace 𝓧]
    {f : Ω → ℝ} {X : Ω → 𝓧} {κ : Kernel 𝓧 ℝ} [IsSFiniteKernel κ] {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hcd : HasCondDistrib f X κ P) (hf : AEStronglyMeasurable f P)
    (hb : ∀ x, ∫⁻ y, ‖y‖ₑ ^ 2 ∂(κ x) ≤ C) :
    MemLp f 2 P := by
  have hXm : AEMeasurable X P := hcd.aemeasurable_fst
  refine (memLp_two_iff_integrable_sq hf).mpr ⟨hf.pow 2, ?_⟩
  have hg : Measurable fun p : 𝓧 × ℝ ↦ ‖p.2‖ₑ ^ 2 := (measurable_snd.enorm).pow_const 2
  have hkey : ∫⁻ ω, ‖f ω ^ 2‖ₑ ∂P = ∫⁻ p : 𝓧 × ℝ, ‖p.2‖ₑ ^ 2 ∂((P.map X) ⊗ₘ κ) := by
    rw [← hcd.map_eq, lintegral_map' hg.aemeasurable hcd.aemeasurable]
    exact lintegral_congr fun ω ↦ by rw [enorm_pow]
  rw [hasFiniteIntegral_iff_enorm, hkey, Measure.lintegral_compProd hg]
  calc ∫⁻ x, ∫⁻ y, ‖y‖ₑ ^ 2 ∂(κ x) ∂(P.map X) ≤ ∫⁻ _, C ∂(P.map X) := lintegral_mono hb
    _ = C * (P.map X) Set.univ := by rw [lintegral_const]
    _ < ⊤ := by
        rw [Measure.map_apply_of_aemeasurable hXm MeasurableSet.univ, Set.preimage_univ]
        exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top P Set.univ)

end ProbabilityTheory
