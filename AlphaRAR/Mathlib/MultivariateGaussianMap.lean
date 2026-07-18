/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Linear pushforward of a centered multivariate Gaussian

The image of a centered multivariate Gaussian `𝒩(0, S)` on `ℝ^n` under a linear map given by a
(possibly rectangular) matrix `G : m × n` is again a centered Gaussian, with covariance transformed
by the congruence `S ↦ G S Gᵀ`, on `ℝ^m`.

This is the covariance-transformation rule behind the delta method (`x ↦ G x` with `G` the Jacobian)
and behind joint/stacked central limit theorems (`x ↦ (G x, G x)` via a stacked `G`).

## Main result

* `AlphaRAR.multivariateGaussian_map_matrix`.
-/

open MeasureTheory ProbabilityTheory

open scoped Matrix RealInnerProductSpace

namespace AlphaRAR

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Rectangular linear pushforward of a centered Gaussian.** For a matrix `G : m × n`, the image
of `𝒩(0, S)` on `ℝ^n` under `x ↦ G x` is the centered Gaussian `𝒩(0, G S Gᵀ)` on `ℝ^m`.

The proof compares characteristic functions: `x ↦ Gx` has adjoint `t ↦ Gᵀt`, so the characteristic
function of the pushforward at `t` equals that of `𝒩(0, S)` at `Gᵀt`, namely
`exp(-½ (Gᵀt)ᵀ S (Gᵀt)) = exp(-½ tᵀ (G S Gᵀ) t)`, which is the characteristic function of
`𝒩(0, G S Gᵀ)`. -/
lemma multivariateGaussian_map_matrix (S : Matrix n n ℝ) (G : Matrix m n ℝ) (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map
        (fun x : EuclideanSpace ℝ n ↦
          (WithLp.toLp 2 (G.mulVec (WithLp.ofLp x)) : EuclideanSpace ℝ m))
      = multivariateGaussian 0 (G * S * Gᵀ) := by
  have hpsd' : (G * S * Gᵀ).PosSemidef := by
    have hh := hS.mul_mul_conjTranspose_same G
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  have hIPm : ∀ (u v : EuclideanSpace ℝ m), (⟪u, v⟫ : ℝ) = (WithLp.ofLp u) ⬝ᵥ (WithLp.ofLp v) := by
    intro u v
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hIPn : ∀ (u v : EuclideanSpace ℝ n), (⟪u, v⟫ : ℝ) = (WithLp.ofLp u) ⬝ᵥ (WithLp.ofLp v) := by
    intro u v
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  set L : EuclideanSpace ℝ n → EuclideanSpace ℝ m :=
    fun x ↦ WithLp.toLp 2 (G.mulVec (WithLp.ofLp x)) with hLdef
  set L' : EuclideanSpace ℝ m → EuclideanSpace ℝ n :=
    fun t ↦ WithLp.toLp 2 (Gᵀ.mulVec (WithLp.ofLp t)) with hL'def
  have hLmeas : Measurable L := by
    rw [hLdef]
    exact ((PiLp.continuous_toLp 2 (fun _ : m ↦ ℝ)).comp
      (((Matrix.mulVecLin G).continuous_of_finiteDimensional).comp
        (PiLp.continuous_ofLp 2 (fun _ : n ↦ ℝ)))).measurable
  have : IsProbabilityMeasure ((multivariateGaussian 0 S).map L) :=
    Measure.isProbabilityMeasure_map hLmeas.aemeasurable
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  have hinner : ∀ x : EuclideanSpace ℝ n, (⟪L x, t⟫ : ℝ) = ⟪x, L' t⟫ := by
    intro x
    rw [hIPm (L x) t, hIPn x (L' t), hLdef, hL'def, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
      dotProduct_comm (G.mulVec _), Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    exact dotProduct_comm _ _
  have hcont : Continuous (fun x : EuclideanSpace ℝ m ↦ Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).mul continuous_const)
  have hmap : charFun ((multivariateGaussian 0 S).map L) t
      = charFun (multivariateGaussian 0 S) (L' t) := by
    rw [charFun_apply, charFun_apply,
      MeasureTheory.integral_map hLmeas.aemeasurable hcont.aestronglyMeasurable]
    simp_rw [hinner]
  rw [hmap, charFun_multivariateGaussian hS, charFun_multivariateGaussian hpsd']
  have hmove : ∀ (v : m → ℝ) (u : n → ℝ), (Gᵀ *ᵥ v) ⬝ᵥ u = v ⬝ᵥ (G *ᵥ u) := fun v u ↦ by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have hq : (WithLp.ofLp (L' t)) ⬝ᵥ S *ᵥ (WithLp.ofLp (L' t))
      = (WithLp.ofLp t) ⬝ᵥ (G * S * Gᵀ) *ᵥ (WithLp.ofLp t) := by
    rw [hL'def, WithLp.ofLp_toLp, hmove, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [inner_zero_right, inner_zero_right, hq]

end AlphaRAR
