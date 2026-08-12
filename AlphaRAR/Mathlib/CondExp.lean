/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The defining property of a conditional expectation

`IsCondExp μ m f g` says that `g` *is a version of* `μ[f | m]`: it is `m`-measurable, locally
integrable, and has the same integral as `f` over every `m`-measurable set of finite measure.
Those three conditions determine `g` up to a.e. equality, which is Mathlib's
`ae_eq_condExp_of_forall_setIntegral_eq`.

The point of naming the property is that many of this development's definitions *are* conditional
expectations of a specific random variable given a specific σ-algebra — the selection probability
`aRTSSelProb`, the cell variances `MartDiffArray.condVar` — and for those the mathematical content
is not the formula but which variable and which σ-algebra. `IsCondExp` is the predicate their
`@[characterization]` bundles are stated with; `Mathlib.condExp` itself cannot carry the bundle,
since the attribute refuses to annotate an imported declaration.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace AlphaRAR

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → E}

/-- **`g` is a version of the conditional expectation of `f` given `m`.**

The measure and the sub-σ-algebra come first so that `Measure α` still elaborates against the
ambient `m0` rather than against `m`, and so that the characterized object `g` is the last
argument. -/
structure IsCondExp (μ : Measure α) (m : MeasurableSpace α) (f g : α → E) : Prop where
  /-- `g` is measurable for the smaller σ-algebra: it uses only the information in `m`. -/
  aestronglyMeasurable : AEStronglyMeasurable[m] g μ
  /-- `g` is integrable on every `m`-measurable set of finite measure. -/
  integrableOn : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ
  /-- `g` averages `f` correctly: it has the same integral as `f` over every `m`-measurable set of
  finite measure. This is the content; the other two fields are what make it pin `g` down. -/
  setIntegral_eq : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ

/-- `μ[f | m]` is a version of itself. -/
lemma isCondExp_condExp [CompleteSpace E] (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hf : Integrable f μ) :
    IsCondExp μ m f (μ[f | m]) where
  aestronglyMeasurable := stronglyMeasurable_condExp.aestronglyMeasurable
  integrableOn _ _ _ := integrable_condExp.integrableOn
  setIntegral_eq _ hs _ := setIntegral_condExp hm hf hs

/-- **Uniqueness of the conditional expectation**: any version of `μ[f | m]` agrees with it a.e.
This is `ae_eq_condExp_of_forall_setIntegral_eq` with the three hypotheses packaged. -/
lemma IsCondExp.ae_eq_condExp [CompleteSpace E] (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hf : Integrable f μ) (hg : IsCondExp μ m f g) : g =ᵐ[μ] μ[f | m] :=
  ae_eq_condExp_of_forall_setIntegral_eq hm hf hg.integrableOn hg.setIntegral_eq
    hg.aestronglyMeasurable

end AlphaRAR
