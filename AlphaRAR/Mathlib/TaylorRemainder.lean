/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A quadratic remainder bound for the first-order Taylor expansion

If a map `f` is differentiable on a convex set `s` with derivative `f'` that is Lipschitz at the
base point `θ` (`‖f' z - f' θ‖ ≤ K‖z - θ‖`), then the first-order Taylor remainder is controlled
quadratically: `‖f x - f θ - f' θ (x - θ)‖ ≤ K‖x - θ‖²`.

This packages the mean-value inequality `norm_image_sub_le_of_norm_hasFDerivWithin_le'` applied on
the segment `[θ, x]`, where the derivative deviation `‖f' z - f' θ‖ ≤ K‖z - θ‖ ≤ K‖x - θ‖` provides
the constant. It is the multivariate first-order expansion with an explicit quadratic bound
(blueprint `lem:taylor_rho`), obtained from a Lipschitz bound on the derivative (which
Condition **B** supplies via the bounded second derivative).

## Main result

* `AlphaRAR.norm_sub_fderiv_le_mul_sq`.
-/

open Set

namespace AlphaRAR

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Quadratic remainder bound for the first-order Taylor expansion.** If `f` is differentiable on
a convex set `s` with derivative `f'`, and `f'` is `K`-Lipschitz relative to `θ` on `s`
(`‖f' z - f' θ‖ ≤ K‖z - θ‖`), then for `x ∈ s`,
`‖f x - f θ - f' θ (x - θ)‖ ≤ K‖x - θ‖²`. -/
theorem norm_sub_fderiv_le_mul_sq {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E} {θ x : E} {K : ℝ}
    (hK : 0 ≤ K) (hs : Convex ℝ s) (hf : ∀ z ∈ s, HasFDerivAt f (f' z) z)
    (hlip : ∀ z ∈ s, ‖f' z - f' θ‖ ≤ K * ‖z - θ‖) (hθ : θ ∈ s) (hx : x ∈ s) :
    ‖f x - f θ - f' θ (x - θ)‖ ≤ K * ‖x - θ‖ ^ 2 := by
  have hseg : segment ℝ θ x ⊆ s := hs.segment_subset hθ hx
  have hbound : ∀ z ∈ segment ℝ θ x, ‖f' z - f' θ‖ ≤ K * ‖x - θ‖ := by
    intro z hz
    have hzs : z ∈ s := hseg hz
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hzθ : (1 - t) • θ + t • x - θ = t • (x - θ) := by module
    calc ‖f' ((1 - t) • θ + t • x) - f' θ‖
        ≤ K * ‖(1 - t) • θ + t • x - θ‖ := hlip _ hzs
      _ = K * (t * ‖x - θ‖) := by rw [hzθ, norm_smul, Real.norm_of_nonneg ht.1]
      _ ≤ K * (1 * ‖x - θ‖) := by gcongr; exact ht.2
      _ = K * ‖x - θ‖ := by rw [one_mul]
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz ↦ (hf z (hseg hz)).hasFDerivWithinAt) hbound (convex_segment θ x)
    (left_mem_segment ℝ θ x) (right_mem_segment ℝ θ x)
  calc ‖f x - f θ - f' θ (x - θ)‖
      ≤ K * ‖x - θ‖ * ‖x - θ‖ := key
    _ = K * ‖x - θ‖ ^ 2 := by ring

end AlphaRAR
