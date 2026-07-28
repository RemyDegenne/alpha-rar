/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LocalExtr.Basic
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

A `C²` map supplies that Lipschitz bound by itself, since `fderiv ℝ f` is then `C¹` and hence
locally Lipschitz: this gives `exists_eventually_norm_sub_fderiv_le_mul_sq`. At a *minimum* the
linear term vanishes by Fermat's theorem, and one gets the one-sided bound `f x - f θ ≤ K‖x - θ‖²`
of `exists_eventually_sub_le_mul_sq_of_isLocalMin` — the second-order Taylor bound at a minimum,
with no explicit Hessian.

## Main results

* `AlphaRAR.norm_sub_fderiv_le_mul_sq` — the mean-value form, from a Lipschitz derivative.
* `AlphaRAR.exists_eventually_norm_sub_fderiv_le_mul_sq` — its `C²` form.
* `AlphaRAR.exists_eventually_sub_le_mul_sq_of_isLocalMin` — the `C²` form at a local minimum.
* `AlphaRAR.sq_norm_le_sum_sq` — sup-norm to sum-of-squares, converting the bounds above into the
  coordinatewise form used downstream.
-/

open Filter Set

open scoped Topology NNReal

namespace AlphaRAR

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Quadratic remainder bound for the first-order Taylor expansion.** If `f` is differentiable on
a convex set `s` with derivative `f'`, and `f'` is `K`-Lipschitz relative to `θ` on `s`
(`‖f' z - f' θ‖ ≤ K‖z - θ‖`), then for `x ∈ s`,
`‖f x - f θ - f' θ (x - θ)‖ ≤ K‖x - θ‖²`. -/
lemma norm_sub_fderiv_le_mul_sq {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E} {θ x : E} {K : ℝ}
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

/-- **The `C²` form of `norm_sub_fderiv_le_mul_sq`.** A map that is twice continuously
differentiable at `θ` has a first-order Taylor remainder that is `O(‖x - θ‖²)` near `θ`.

No Hessian appears: being `C²` makes `fderiv ℝ f` a `C¹` map, hence Lipschitz on a neighbourhood of
`θ` (`ContDiffAt.exists_lipschitzOnWith`), which is exactly the input `norm_sub_fderiv_le_mul_sq`
consumes. -/
lemma exists_eventually_norm_sub_fderiv_le_mul_sq {f : E → F} {θ : E}
    (hf : ContDiffAt ℝ 2 f θ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ x in 𝓝 θ, ‖f x - f θ - fderiv ℝ f θ (x - θ)‖ ≤ K * ‖x - θ‖ ^ 2 := by
  obtain ⟨K, t, ht, hlip⟩ := (hf.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hdiff : ∀ᶠ y in 𝓝 θ, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact hy.differentiableAt two_ne_zero
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hdiff)
  refine ⟨(K : ℝ), K.coe_nonneg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds θ hr] with x hx
  refine norm_sub_fderiv_le_mul_sq (f' := fderiv ℝ f) K.coe_nonneg (convex_ball θ r)
    (fun z hz ↦ (hsub hz).2.hasFDerivAt) (fun z hz ↦ ?_) (Metric.mem_ball_self hr) hx
  have hd := hlip.dist_le_mul z (hsub hz).1 θ (hsub (Metric.mem_ball_self hr)).1
  rwa [dist_eq_norm, dist_eq_norm] at hd

/-- **A `C²` function is quadratically small near a local minimum**: `f x - f θ ≤ K‖x - θ‖²`.

By Fermat's theorem the linear term of the Taylor expansion vanishes at `θ`, so the whole increment
is the quadratic remainder of `exists_eventually_norm_sub_fderiv_le_mul_sq`. This is the standard
"second-order expansion at a minimum" without ever naming the Hessian. -/
lemma exists_eventually_sub_le_mul_sq_of_isLocalMin {f : E → ℝ} {θ : E} (hmin : IsLocalMin f θ)
    (hf : ContDiffAt ℝ 2 f θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x in 𝓝 θ, f x - f θ ≤ K * ‖x - θ‖ ^ 2 := by
  obtain ⟨K, hK, hbd⟩ := exists_eventually_norm_sub_fderiv_le_mul_sq hf
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbd] with x hx
  rw [hmin.fderiv_eq_zero] at hx
  simp only [zero_apply, sub_zero, Real.norm_eq_abs] at hx
  exact (le_abs_self _).trans hx

/-- On a finite product carrying the sup norm, the squared norm is at most the sum of the squared
coordinates. This converts the quadratic bounds above into the coordinatewise form in which
per-coordinate rates plug in. -/
lemma sq_norm_le_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ‖x‖ ^ 2 ≤ ∑ j, x j ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hx : x = 0 := funext fun j ↦ hι.elim j
    simp [hx]
  · obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j ↦ ‖x j‖
    have hnorm : ‖x‖ = ‖x j₀‖ :=
      le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hj₀) (norm_le_pi_norm x j₀)
    rw [hnorm, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (f := fun j ↦ x j ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ j₀)

end AlphaRAR
