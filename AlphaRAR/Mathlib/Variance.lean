/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.Variance

/-!
# The variance of the identity as a central second moment

`Var[id; μ] = ∫ x, (x - μ[id])² ∂μ`: the `X = id` case of `variance_eq_integral`, with the
`id x = x` beta-reduction already performed. This is the form in which the arm variances
`Var[id; ν a]` are compared with truncated second moments.
-/

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory

namespace AlphaRAR

/-- The variance of the identity is the central second moment of the measure. -/
lemma variance_id_eq_integral (μ : Measure ℝ) :
    Var[id; μ] = ∫ x, (x - μ[id]) ^ 2 ∂μ := by
  rw [variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq]

end AlphaRAR
