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
single reusable statement, and specializes it to the mean of `Y` (`g = id`).

These belong in Mathlib next to `HasCondDistrib`.

## Main results

* `ProbabilityTheory.HasCondDistrib.condExp_comp_eq`: conditional expectation of `g ∘ Y`.
* `ProbabilityTheory.HasCondDistrib.condExp_eq`: conditional expectation of `Y` (the kernel mean).
-/

open MeasureTheory

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

/-- **Conditional expectation of `Y` from its conditional distribution.**
If `Y` (valued in a Banach space) has conditional distribution `κ` given `X` under `P`, then its
conditional expectation given `σ(X)` is the mean of the kernel:
`P[Y | σ(X)] =ᵐ[P] fun ω ↦ ∫ y, y ∂(κ (X ω))`. -/
lemma HasCondDistrib.condExp_eq [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨] [CompleteSpace 𝓨]
    [BorelSpace 𝓨] [SecondCountableTopology 𝓨]
    (h : HasCondDistrib Y X κ P) (hX : Measurable X) (hint : Integrable Y P) :
    P[Y | mβ.comap X] =ᵐ[P] fun ω ↦ ∫ y, y ∂(κ (X ω)) :=
  h.condExp_comp_eq hX stronglyMeasurable_id hint

end ProbabilityTheory
