/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Filtration

/-!
# Martingale central limit theorem (Lindeberg form)

This file develops, for a triangular array of martingale differences, the
one-dimensional central limit theorem in Lindeberg form (the Hall–Heyde form).
The analytic top of the argument (Lévy's continuity theorem, the Gaussian
characteristic function, `TendstoInDistribution` and Slutsky) is already in
Mathlib; here we build the martingale core.

This file is Mathlib-bound staging (cf. the `AlphaRAR/Mathlib/` directory).

## Reusable analytic ingredients

* `AlphaRAR.norm_expI_sub_taylor_le` : `‖e^{ix} - (1 + ix - x²/2)‖ ≤ min (2x²) |x|³`,
  the second-order expansion of the complex exponential on the imaginary axis
  (blueprint `lem:clt_exp_bound`).
* `AlphaRAR.abs_exp_mul_one_sub_le` : `|eʸ(1-y) - 1| ≤ y²` on `[0,1]`
  (blueprint `lem:clt_real_exp_bound`).
-/

open Complex intervalIntegral MeasureTheory
open scoped Real Topology

namespace AlphaRAR

section ExpBound

/-- Derivative of `s ↦ (s : ℂ)`. -/
lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 x := by
  simpa using (hasDerivAt_id x).ofReal_comp

/-- Derivative of `s ↦ (s : ℂ) * I`. -/
lemma hasDerivAt_ofReal_mul_I (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (s : ℂ) * I) I x := by
  simpa using (hasDerivAt_ofReal x).mul_const I

/-- Derivative of `s ↦ exp (s * I)` as a map `ℝ → ℂ`. -/
lemma hasDerivAt_expI (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (s * I)) (Complex.exp (x * I) * I) x :=
  (hasDerivAt_ofReal_mul_I x).cexp

/-- Derivative of `s ↦ (s : ℂ)² / 2`. -/
lemma hasDerivAt_ofReal_sq_div_two (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (s : ℂ) ^ 2 / 2) (x : ℂ) x := by
  have hr : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) x x := by
    have h : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * x) x := by
      simpa [pow_one] using hasDerivAt_pow 2 x
    have hd := h.div_const 2
    rw [show (2 * x) / 2 = x by ring] at hd
    exact hd
  simpa [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat] using hr.ofReal_comp

/-- On the segment between `0` and `x`, points have absolute value `≤ |x|`. -/
lemma abs_le_of_mem_uIoc {x s : ℝ} (hs : s ∈ Set.uIoc 0 x) : |s| ≤ |x| := by
  simp only [Set.uIoc, Set.mem_Ioc] at hs
  obtain ⟨h1, h2⟩ := hs
  have hmin : -|x| ≤ (0 ⊓ x) := le_min (neg_nonpos.mpr (abs_nonneg x)) (neg_abs_le x)
  have hmax : (0 ⊔ x) ≤ |x| := max_le (abs_nonneg x) (le_abs_self x)
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- First-order bound: `‖e^{ix} - 1‖ ≤ |x|`. -/
lemma norm_expI_sub_one_le (x : ℝ) : ‖Complex.exp (x * I) - 1‖ ≤ |x| := by
  have key : Complex.exp (x * I) - 1 = ∫ s in (0 : ℝ)..x, Complex.exp (s * I) * I := by
    have h := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (f := fun s : ℝ ↦ Complex.exp (s * I))
      (f' := fun s : ℝ ↦ Complex.exp (s * I) * I)
      (fun s _ ↦ hasDerivAt_expI s)
      (by apply Continuous.intervalIntegrable; fun_prop)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h
    exact h.symm
  rw [key]
  calc ‖∫ s in (0 : ℝ)..x, Complex.exp (s * I) * I‖
      ≤ 1 * |x - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s _
        simp [Complex.norm_exp_ofReal_mul_I]
    _ = |x| := by rw [one_mul, sub_zero]

/-- Second-order bound: `‖e^{ix} - 1 - ix‖ ≤ x²`. -/
lemma norm_expI_sub_one_sub_le (x : ℝ) :
    ‖Complex.exp (x * I) - 1 - x * I‖ ≤ x ^ 2 := by
  have key : Complex.exp (x * I) - 1 - x * I
      = ∫ s in (0 : ℝ)..x, (Complex.exp (s * I) * I - I) := by
    have h := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (f := fun s : ℝ ↦ Complex.exp (s * I) - 1 - s * I)
      (f' := fun s : ℝ ↦ Complex.exp (s * I) * I - I)
      (fun s _ ↦ ((hasDerivAt_expI s).sub_const 1).sub (hasDerivAt_ofReal_mul_I s))
      (by apply Continuous.intervalIntegrable; fun_prop)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero] at h
    exact h.symm
  rw [key]
  calc ‖∫ s in (0 : ℝ)..x, (Complex.exp (s * I) * I - I)‖
      ≤ |x| * |x - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        have heq : Complex.exp (s * I) * I - I = (Complex.exp (s * I) - 1) * I := by ring
        rw [heq, norm_mul, Complex.norm_I, mul_one]
        exact le_trans (norm_expI_sub_one_le s) (abs_le_of_mem_uIoc hs)
    _ = x ^ 2 := by rw [sub_zero, ← sq_abs x, pow_two]

/-- **Complex exponential expansion** (blueprint `lem:clt_exp_bound`): the second-order
Taylor remainder of `e^{ix}` on the imaginary axis is `O(min(x², |x|³))`. -/
lemma norm_expI_sub_taylor_le (x : ℝ) :
    ‖Complex.exp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2‖ ≤ min (2 * x ^ 2) (|x| ^ 3) := by
  rw [le_min_iff]
  refine ⟨?_, ?_⟩
  · -- quadratic bound `2 x²` via the triangle inequality
    have h2 : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by
      have hcast : ((x : ℂ) ^ 2 / 2) = ((x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖Complex.exp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2‖
        ≤ ‖Complex.exp (x * I) - 1 - x * I‖ + ‖(x : ℂ) ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ x ^ 2 + x ^ 2 / 2 := by rw [h2]; linarith [norm_expI_sub_one_sub_le x]
      _ ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg x]
  · -- cubic bound `|x|³` via a third integration
    have key : Complex.exp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2
        = ∫ s in (0 : ℝ)..x, (Complex.exp (s * I) * I - I + s) := by
      have h := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
        (f := fun s : ℝ ↦ Complex.exp (s * I) - 1 - s * I + (s : ℂ) ^ 2 / 2)
        (f' := fun s : ℝ ↦ Complex.exp (s * I) * I - I + s)
        (fun s _ ↦ (((hasDerivAt_expI s).sub_const 1).sub (hasDerivAt_ofReal_mul_I s)).add
          (hasDerivAt_ofReal_sq_div_two s))
        (by apply Continuous.intervalIntegrable; fun_prop)
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, sub_zero] at h
      exact h.symm
    rw [key]
    calc ‖∫ s in (0 : ℝ)..x, (Complex.exp (s * I) * I - I + s)‖
        ≤ x ^ 2 * |x - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro s hs
          have heq : Complex.exp (s * I) * I - I + (s : ℂ)
              = (Complex.exp (s * I) - 1 - s * I) * I := by
            rw [sub_mul, sub_mul, one_mul, mul_assoc, Complex.I_mul_I]; ring
          rw [heq, norm_mul, Complex.norm_I, mul_one]
          refine le_trans (norm_expI_sub_one_sub_le s) ?_
          nlinarith [abs_le_of_mem_uIoc hs, abs_nonneg s, abs_nonneg x, sq_abs s, sq_abs x]
      _ = |x| ^ 3 := by rw [sub_zero, ← sq_abs x]; ring

end ExpBound

section RealExpBound

/-- **Real elementary bound** (blueprint `lem:clt_real_exp_bound`):
`|eʸ(1-y) - 1| ≤ y²` for `y ≤ 1` (in particular on `[0,1]`). -/
lemma abs_exp_mul_one_sub_le {y : ℝ} (hy1 : y ≤ 1) :
    |Real.exp y * (1 - y) - 1| ≤ y ^ 2 := by
  have hle : Real.exp y * (1 - y) ≤ 1 := by
    have h1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos y).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
  have hge : 1 - y ^ 2 ≤ Real.exp y * (1 - y) := by
    have h3 := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp y] : (1 : ℝ) + y ≤ Real.exp y)
      (by positivity : (0 : ℝ) ≤ 1 - y)
    nlinarith [h3]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **Real elementary bound, unbounded form** (blueprint `lem:clt_real_exp_bound_pos`):
`|eʸ(1-y) - 1| ≤ y²·eʸ` for every `y ≥ 0`. Unlike `abs_exp_mul_one_sub_le`, this holds for
all `y ≥ 0` (the extra `eʸ` factor is what makes it valid past `y = 1`). -/
lemma abs_exp_mul_one_sub_le' {y : ℝ} (hy : 0 ≤ y) :
    |Real.exp y * (1 - y) - 1| ≤ y ^ 2 * Real.exp y := by
  have hle : Real.exp y * (1 - y) ≤ 1 := by
    have h1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos y).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
  have hquad : (0 : ℝ) ≤ 1 - y + y ^ 2 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have hge : 1 ≤ Real.exp y * (1 - y) + y ^ 2 * Real.exp y := by
    have hexp : (1 : ℝ) + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    nlinarith [mul_le_mul_of_nonneg_right hexp hquad, pow_nonneg hy 3, Real.exp_pos y]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **`exp(-·)` is `1`-Lipschitz on `[0,∞)`**: for `a, b ≥ 0`, `|e^{-a} - e^{-b}| ≤ |a - b|`.
Used to transfer `V_n → σ²` in probability through the map `x ↦ e^{-(t²/2)x}`. -/
lemma abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a]
    exact this hb ha (not_le.mp hab).le
  have hfac : Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    rw [mul_sub, mul_one, ← Real.exp_add, show -a + -(b - a) = -b from by ring]
  have hle1 : Real.exp (-a) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hpos : 0 ≤ 1 - Real.exp (-(b - a)) := by
    have : Real.exp (-(b - a)) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hub : 1 - Real.exp (-(b - a)) ≤ b - a := by
    have := Real.add_one_le_exp (-(b - a)); linarith
  have h2 : Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    rw [hfac]
    calc Real.exp (-a) * (1 - Real.exp (-(b - a)))
        ≤ 1 * (1 - Real.exp (-(b - a))) := mul_le_mul_of_nonneg_right hle1 hpos
      _ = 1 - Real.exp (-(b - a)) := one_mul _
      _ ≤ b - a := hub
  have h3 : 0 ≤ Real.exp (-a) - Real.exp (-b) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  rw [abs_of_nonneg h3, abs_of_nonpos (by linarith : a - b ≤ 0)]
  linarith [h2]

/-- **Factor bound behind the one-step `Z`-increment estimate.** For `v ≥ 0` and a complex `w`
approximating `1 - (t²/2)v` with error `‖w - (1 - (t²/2)v)‖ ≤ ρ`, the multiplicative increment
`e^{(t²/2)v} w - 1` has modulus
`‖e^{(t²/2)v} w - 1‖ ≤ e^{(t²/2)v}·((t⁴/4)v² + ρ)`.
Split `e^{y}w - 1 = e^{y}(w-(1-y)) + (e^{y}(1-y)-1)` with `y = (t²/2)v`; the first term is
bounded by `e^{y}ρ`, the second by `y²e^{y}` via `abs_exp_mul_one_sub_le'`. The `e^{y}` factor is
essential — `y` is only known to be bounded, not `≤ 1`. -/
lemma norm_expVar_mul_sub_one_le {t v ρ : ℝ} (hv : 0 ≤ v) {w : ℂ}
    (hw : ‖w - (1 - ((t ^ 2 / 2 * v : ℝ) : ℂ))‖ ≤ ρ) :
    ‖Complex.exp ((t ^ 2 / 2 * v : ℝ) : ℂ) * w - 1‖
      ≤ Real.exp (t ^ 2 / 2 * v) * (t ^ 4 / 4 * v ^ 2 + ρ) := by
  set y : ℝ := t ^ 2 / 2 * v with hy
  have hy_nn : 0 ≤ y := by rw [hy]; exact mul_nonneg (by positivity) hv
  have hnorm_expy : ‖Complex.exp (y : ℂ)‖ = Real.exp y := by
    rw [Complex.norm_exp, Complex.ofReal_re]
  have he : ((Real.exp y * (1 - y) - 1 : ℝ) : ℂ) = Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1 := by
    push_cast; ring
  have hbound2 : ‖Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1‖ ≤ y ^ 2 * Real.exp y := by
    rw [← he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_exp_mul_one_sub_le' hy_nn
  have hsplit : Complex.exp (y : ℂ) * w - 1
      = Complex.exp (y : ℂ) * (w - (1 - (y : ℂ))) + (Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1) := by
    ring
  calc ‖Complex.exp (y : ℂ) * w - 1‖
      = ‖Complex.exp (y : ℂ) * (w - (1 - (y : ℂ)))
          + (Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1)‖ := by rw [hsplit]
    _ ≤ ‖Complex.exp (y : ℂ) * (w - (1 - (y : ℂ)))‖
          + ‖Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1‖ := norm_add_le _ _
    _ = Real.exp y * ‖w - (1 - (y : ℂ))‖ + ‖Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1‖ := by
        rw [norm_mul, hnorm_expy]
    _ ≤ Real.exp y * ρ + y ^ 2 * Real.exp y :=
        add_le_add (mul_le_mul_of_nonneg_left hw (Real.exp_pos y).le) hbound2
    _ = Real.exp y * (t ^ 4 / 4 * v ^ 2 + ρ) := by rw [hy]; ring

end RealExpBound

section CondChar

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **Conditional characteristic increment** (blueprint `lem:clt_cond_char`):
for a centered square-integrable increment `Δ` and a sub-σ-algebra `m`, the conditional
characteristic function `E[e^{itΔ}|m]` agrees with `1 - (t²/2)E[Δ²|m]` up to an error whose
norm is bounded a.e. by the conditional expectation of `min(2t²Δ², |t|³|Δ|³)`. -/
lemma norm_condExp_expI_sub_le [IsProbabilityMeasure P] (hm : m ≤ m0)
    {Δ : Ω → ℝ} (hΔ : MemLp Δ 2 P) (hcent : P[Δ | m] =ᵐ[P] 0) (t : ℝ) :
    (fun ω ↦ ‖(P[fun ω' ↦ Complex.exp (((t * Δ ω' : ℝ) : ℂ) * I) | m]) ω
        - (1 - (((t ^ 2 / 2) * (P[fun ω' ↦ (Δ ω') ^ 2 | m]) ω : ℝ) : ℂ))‖)
      ≤ᵐ[P] P[fun ω' ↦ min (2 * t ^ 2 * (Δ ω') ^ 2) (|t| ^ 3 * |Δ ω'| ^ 3) | m] := by
  classical
  have hΔ1 : Integrable Δ P := hΔ.integrable one_le_two
  have hΔ2 : Integrable (fun ω ↦ (Δ ω) ^ 2) P := hΔ.integrable_sq
  have haesm : AEStronglyMeasurable Δ P := hΔ.aestronglyMeasurable
  -- integrand functions
  set g : Ω → ℂ := fun ω' ↦ Complex.exp (((t * Δ ω' : ℝ) : ℂ) * I) with hg_def
  set lin : Ω → ℂ := fun ω' ↦ ((t * Δ ω' : ℝ) : ℂ) * I with hlin_def
  set quad : Ω → ℂ := fun ω' ↦ (((t * Δ ω' : ℝ) : ℂ)) ^ 2 / 2 with hquad_def
  let R : Ω → ℂ := fun ω' ↦ g ω' - 1 - lin ω' + quad ω'
  let v : Ω → ℝ := P[fun ω' ↦ (Δ ω') ^ 2 | m]
  let φ : Ω → ℝ := fun ω' ↦ min (2 * t ^ 2 * (Δ ω') ^ 2) (|t| ^ 3 * |Δ ω'| ^ 3)
  -- helper: condExp commutes with the coercion ℝ → ℂ
  have hofReal : ∀ (f : Ω → ℝ), Integrable f P →
      (P[fun ω ↦ ((f ω : ℝ) : ℂ) | m]) =ᵐ[P] fun ω ↦ ((P[f | m] ω : ℝ) : ℂ) :=
    fun f hf ↦ (Complex.ofRealCLM.comp_condExp_comm hf).symm
  -- integrabilities
  have hg_aesm : AEStronglyMeasurable g P :=
    Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (haesm.const_mul t)).mul aestronglyMeasurable_const)
  have hg_int : Integrable g P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hg_aesm (ae_of_all _ fun ω ↦ ?_)
    simp only [hg_def]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (t * Δ ω))
  have hlin_int : Integrable lin P :=
    (Complex.ofRealCLM.integrable_comp (hΔ1.const_mul t)).mul_const I
  have hquad_eq : quad = fun ω ↦ ((t ^ 2 / 2 * (Δ ω) ^ 2 : ℝ) : ℂ) := by
    funext ω; simp only [hquad_def]; push_cast; ring
  have hquad_int : Integrable quad P := by
    rw [hquad_eq]
    exact Complex.ofRealCLM.integrable_comp (hΔ2.const_mul (t ^ 2 / 2))
  have hR_int : Integrable R P := ((hg_int.sub (integrable_const 1)).sub hlin_int).add hquad_int
  -- pointwise bound on the remainder R
  have hR_le : ∀ ω, ‖R ω‖ ≤ φ ω := fun ω ↦ by
    have h := norm_expI_sub_taylor_le (t * Δ ω)
    have e1 : (2 : ℝ) * (t * Δ ω) ^ 2 = 2 * t ^ 2 * (Δ ω) ^ 2 := by ring
    have e2 : |t * Δ ω| ^ 3 = |t| ^ 3 * |Δ ω| ^ 3 := by rw [abs_mul, mul_pow]
    rw [e1, e2] at h
    exact h
  -- helper: pull a real scalar out of a real conditional expectation
  have hcond_smul : ∀ (c : ℝ) (f : Ω → ℝ),
      P[fun ω ↦ c * f ω | m] =ᵐ[P] fun ω ↦ c * P[f | m] ω := by
    intro c f
    have hcf : (fun ω ↦ c * f ω) = c • f := by funext ω; simp [Pi.smul_apply]
    rw [hcf]
    filter_upwards [condExp_smul c f m] with ω hω
    rw [hω]; simp [Pi.smul_apply]
  -- condExp of the three easy pieces
  have hc1 : P[fun _ : Ω ↦ (1 : ℂ) | m] = fun _ ↦ 1 := condExp_const hm 1
  have hclin : P[lin | m] =ᵐ[P] 0 := by
    have hI : lin = fun ω ↦ (↑t * I) • ((Δ ω : ℝ) : ℂ) := by
      funext ω; simp only [hlin_def, smul_eq_mul]; push_cast; ring
    rw [hI]
    have hz : P[fun ω ↦ ((Δ ω : ℝ) : ℂ) | m] =ᵐ[P] 0 := by
      filter_upwards [hofReal Δ hΔ1, hcent] with ω hω hω0
      rw [hω, hω0]; simp
    calc P[fun ω ↦ ((t : ℂ) * I) • ((Δ ω : ℝ) : ℂ) | m]
        =ᵐ[P] ((t : ℂ) * I) • P[fun ω ↦ ((Δ ω : ℝ) : ℂ) | m] :=
          condExp_smul ((t : ℂ) * I) (fun ω ↦ ((Δ ω : ℝ) : ℂ)) m
      _ =ᵐ[P] 0 := by filter_upwards [hz] with ω hω; rw [Pi.smul_apply, hω]; simp
  have hcquad : P[quad | m] =ᵐ[P] fun ω ↦ ((t ^ 2 / 2 * v ω : ℝ) : ℂ) := by
    rw [hquad_eq]
    calc P[fun ω ↦ ((t ^ 2 / 2 * (Δ ω) ^ 2 : ℝ) : ℂ) | m]
        =ᵐ[P] fun ω ↦ ((P[fun ω' ↦ t ^ 2 / 2 * (Δ ω') ^ 2 | m] ω : ℝ) : ℂ) :=
          hofReal _ (hΔ2.const_mul (t ^ 2 / 2))
      _ =ᵐ[P] fun ω ↦ ((t ^ 2 / 2 * v ω : ℝ) : ℂ) := by
          filter_upwards [hcond_smul (t ^ 2 / 2) (fun ω ↦ (Δ ω) ^ 2)] with ω hω
          rw [hω]
  -- the key identity: `E[g|m] - (1 - ↑(t²/2·v)) =ᵐ E[R|m]`
  have hgR : (fun ω ↦ (P[g | m]) ω - (1 - ((t ^ 2 / 2 * v ω : ℝ) : ℂ))) =ᵐ[P] P[R | m] := by
    have hRexp : P[R | m] =ᵐ[P]
        fun ω ↦ (P[g | m]) ω - 1 - (P[lin | m]) ω + (P[quad | m]) ω := by
      have hR_eq : R = g - (fun _ ↦ 1) - lin + quad := rfl
      rw [hR_eq]
      filter_upwards
        [condExp_add ((hg_int.sub (integrable_const 1)).sub hlin_int) hquad_int m,
          condExp_sub (hg_int.sub (integrable_const 1)) hlin_int m,
          condExp_sub hg_int (integrable_const 1) m] with ω hadd hsub1 hsub2
      simp only [Pi.add_apply, Pi.sub_apply, hc1] at hadd hsub1 hsub2 ⊢
      rw [hadd, hsub1, hsub2]
    filter_upwards [hRexp, hclin, hcquad] with ω hR hlin0 hquad0
    rw [hR]
    simp only [Pi.zero_apply] at hlin0
    rw [hlin0, hquad0]; ring
  -- assemble the norm bound
  have hφ_aesm : AEStronglyMeasurable φ P := by
    have hcont : Continuous (fun x : ℝ ↦ min (2 * t ^ 2 * x ^ 2) (|t| ^ 3 * |x| ^ 3)) := by
      fun_prop
    exact hcont.comp_aestronglyMeasurable haesm
  have hφ_nonneg : ∀ ω, 0 ≤ φ ω := fun ω ↦ le_min (by positivity) (by positivity)
  have hφ_int : Integrable φ P :=
    (hΔ2.const_mul (2 * t ^ 2)).mono' hφ_aesm
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφ_nonneg ω)]; exact min_le_left _ _)
  have hnorm : (fun ω ↦ ‖(P[R | m]) ω‖) ≤ᵐ[P] P[fun ω ↦ ‖R ω‖ | m] := norm_condExp_le R
  have hmono : P[fun ω ↦ ‖R ω‖ | m] ≤ᵐ[P] P[φ | m] :=
    condExp_mono hR_int.norm hφ_int (ae_of_all _ hR_le)
  filter_upwards [hgR, hnorm, hmono] with ω h1 h2 h3
  rw [h1]
  exact le_trans h2 h3

/-- Conditional variance split at level `ε` (blueprint `lem:clt_max_var`, per-cell core):
`E[d²|m] ≤ ε² + E[d²·𝟙{|d|>ε}|m]` a.e. -/
lemma condExp_sq_le [IsProbabilityMeasure P] {d : Ω → ℝ} (hd : Measurable d)
    (hd2 : Integrable (fun ω ↦ (d ω) ^ 2) P) (hm : m ≤ m0) (ε : ℝ) :
    P[fun ω ↦ (d ω) ^ 2 | m] ≤ᵐ[P]
      fun ω ↦ ε ^ 2 + (P[{ω | ε < |d ω|}.indicator (fun ω ↦ (d ω) ^ 2) | m]) ω := by
  set s : Set Ω := {ω | ε < |d ω|} with hs_def
  have hs : MeasurableSet s := measurableSet_lt measurable_const hd.abs
  have hind_int : Integrable (s.indicator (fun ω ↦ (d ω) ^ 2)) P := hd2.indicator hs
  have hle : ((fun ω ↦ (d ω) ^ 2) - s.indicator (fun ω ↦ (d ω) ^ 2)) ≤ᵐ[P] fun _ ↦ ε ^ 2 := by
    filter_upwards with ω
    simp only [Pi.sub_apply]
    by_cases h : ω ∈ s
    · rw [Set.indicator_of_mem h, sub_self]; exact sq_nonneg ε
    · rw [Set.indicator_of_notMem h, sub_zero]
      have hd_le : |d ω| ≤ ε := by simpa only [hs_def, Set.mem_setOf_eq, not_lt] using h
      nlinarith [sq_abs (d ω), abs_nonneg (d ω), hd_le]
  have hsub : P[(fun ω ↦ (d ω) ^ 2) - s.indicator (fun ω ↦ (d ω) ^ 2) | m]
      ≤ᵐ[P] fun _ ↦ ε ^ 2 := by
    rw [← condExp_const (μ := P) hm (ε ^ 2)]
    exact condExp_mono (hd2.sub hind_int) (integrable_const _) hle
  filter_upwards [condExp_sub hd2 hind_int m, hsub] with ω hsplit hb
  rw [hsplit] at hb
  simp only [Pi.sub_apply] at hb
  linarith

/-- Pull a real scalar out of a real conditional expectation. -/
lemma condExp_const_mul (c : ℝ) (f : Ω → ℝ) :
    P[fun ω ↦ c * f ω | m] =ᵐ[P] fun ω ↦ c * (P[f | m]) ω := condExp_smul c f m

/-- Split the conditional expectation of `min(2t²d², |t|³|d|³)` at level `ε ≥ 0` into a
`v`-term and a Lindeberg term (blueprint `lem:clt_sum_rem`, per-cell core). -/
lemma condExp_min_le {d : Ω → ℝ} (hd : Measurable d)
    (hd2 : Integrable (fun ω ↦ (d ω) ^ 2) P) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    P[fun ω ↦ min (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3) | m] ≤ᵐ[P]
      fun ω ↦ |t| ^ 3 * ε * (P[fun ω ↦ (d ω) ^ 2 | m]) ω
        + 2 * t ^ 2 * (P[{ω | ε < |d ω|}.indicator (fun ω ↦ (d ω) ^ 2) | m]) ω := by
  set s : Set Ω := {ω | ε < |d ω|} with hs_def
  have hs : MeasurableSet s := measurableSet_lt measurable_const hd.abs
  have hind_int : Integrable (s.indicator (fun ω ↦ (d ω) ^ 2)) P := hd2.indicator hs
  have hmin_int :
      Integrable (fun ω ↦ min (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3)) P := by
    have hcont : Continuous (fun x : ℝ ↦ min (2 * t ^ 2 * x ^ 2) (|t| ^ 3 * |x| ^ 3)) := by
      fun_prop
    refine (hd2.const_mul (2 * t ^ 2)).mono'
      (hcont.comp_aestronglyMeasurable hd.aestronglyMeasurable) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (by positivity))]
    exact min_le_left _ _
  have hle : ∀ ω, min (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3) ≤
      |t| ^ 3 * ε * (d ω) ^ 2 + 2 * t ^ 2 * (s.indicator (fun ω ↦ (d ω) ^ 2) ω) := by
    intro ω
    have hnn0 : 0 ≤ |t| ^ 3 * ε * (d ω) ^ 2 := by positivity
    by_cases h : ω ∈ s
    · rw [Set.indicator_of_mem h]
      have hml := min_le_left (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3)
      linarith
    · rw [Set.indicator_of_notMem h, mul_zero, add_zero]
      have hd_le : |d ω| ≤ ε := by simpa only [hs_def, Set.mem_setOf_eq, not_lt] using h
      have hmr := min_le_right (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3)
      have hcube : |t| ^ 3 * |d ω| ^ 3 ≤ |t| ^ 3 * ε * (d ω) ^ 2 := by
        have h2 : |d ω| ^ 3 = |d ω| * (d ω) ^ 2 := by rw [pow_succ, sq_abs]; ring
        have hi : |d ω| ^ 3 ≤ ε * (d ω) ^ 2 := by
          rw [h2]; exact mul_le_mul_of_nonneg_right hd_le (sq_nonneg _)
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hi (pow_nonneg (abs_nonneg t) 3)
      linarith
  have hg_int := (hd2.const_mul (|t| ^ 3 * ε)).add (hind_int.const_mul (2 * t ^ 2))
  have hmono := condExp_mono (m := m) hmin_int hg_int (ae_of_all _ hle)
  filter_upwards [hmono,
    condExp_add (hd2.const_mul (|t| ^ 3 * ε)) (hind_int.const_mul (2 * t ^ 2)) m,
    condExp_const_mul (m := m) (|t| ^ 3 * ε) (fun ω ↦ (d ω) ^ 2),
    condExp_const_mul (m := m) (2 * t ^ 2) (s.indicator (fun ω ↦ (d ω) ^ 2))]
    with ω hm1 hadd h1 h2
  rw [hadd] at hm1
  simp only [Pi.add_apply] at hm1
  rw [h1, h2] at hm1
  exact hm1

end CondChar

section BoundedConvergence

open Filter

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Bounded convergence in probability, `L¹` form.** On a probability space, if `g n → 0` in
measure and `‖g n‖ ≤ C` a.e. uniformly in `n`, then `∫ ‖g n‖ → 0`. -/
lemma tendsto_integral_norm_of_tendstoInMeasure_zero [IsProbabilityMeasure P] {E : Type*}
    [NormedAddCommGroup E] {g : ℕ → Ω → E} {C : ℝ}
    (hmeas : ∀ n, StronglyMeasurable (g n)) (hbdd : ∀ n, ∀ᵐ ω ∂P, ‖g n ω‖ ≤ C)
    (hconv : TendstoInMeasure P g atTop 0) :
    Tendsto (fun n ↦ ∫ ω, ‖g n ω‖ ∂P) atTop (𝓝 0) := by
  let C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hbdd' : ∀ n, ∀ᵐ ω ∂P, ‖g n ω‖ ≤ C' :=
    fun n ↦ (hbdd n).mono fun ω hω ↦ le_trans hω (le_max_left _ _)
  have hint : ∀ n, Integrable (g n) P :=
    fun n ↦ Integrable.mono' (integrable_const C) (hmeas n).aestronglyMeasurable (hbdd n)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hε : (0 : ℝ) < δ / 2 := by positivity
  have hmc : Tendsto (fun n ↦ (P {ω | δ / 2 ≤ ‖g n ω‖}).toReal) atTop (𝓝 0) := by
    have h0 := hconv (ENNReal.ofReal (δ / 2)) (by positivity)
    have hset : ∀ n, {ω | ENNReal.ofReal (δ / 2) ≤ edist (g n ω) ((0 : Ω → E) ω)}
        = {ω | δ / 2 ≤ ‖g n ω‖} := by
      intro n; ext ω
      simp only [Set.mem_setOf_eq, Pi.zero_apply, edist_zero_right]
      rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    simp_rw [hset] at h0
    exact (ENNReal.tendsto_toReal_zero_iff (fun n ↦ measure_ne_top P _)).mpr h0
  have hmc' : Tendsto (fun n ↦ C' * (P {ω | δ / 2 ≤ ‖g n ω‖}).toReal) atTop (𝓝 0) := by
    simpa using hmc.const_mul C'
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmc' (δ / 2) hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hSmeas : MeasurableSet {ω | δ / 2 ≤ ‖g n ω‖} :=
    measurableSet_le measurable_const (hmeas n).norm.measurable
  have hbound : ∫ ω, ‖g n ω‖ ∂P ≤ δ / 2 + C' * (P {ω | δ / 2 ≤ ‖g n ω‖}).toReal := by
    have hle : (fun ω ↦ ‖g n ω‖) ≤ᵐ[P]
        fun ω ↦ δ / 2 + {ω | δ / 2 ≤ ‖g n ω‖}.indicator (fun _ ↦ C') ω := by
      filter_upwards [hbdd' n] with ω hω
      by_cases hmem : ω ∈ {ω | δ / 2 ≤ ‖g n ω‖}
      · rw [Set.indicator_of_mem hmem]; linarith [hω, hε.le]
      · rw [Set.indicator_of_notMem hmem, add_zero]
        simp only [Set.mem_setOf_eq, not_le] at hmem
        linarith [hmem]
    calc ∫ ω, ‖g n ω‖ ∂P
        ≤ ∫ ω, (δ / 2 + {ω | δ / 2 ≤ ‖g n ω‖}.indicator (fun _ ↦ C') ω) ∂P :=
          integral_mono_ae (hint n).norm
            ((integrable_const _).add ((integrable_const C').indicator hSmeas)) hle
      _ = δ / 2 + C' * (P {ω | δ / 2 ≤ ‖g n ω‖}).toReal := by
          rw [integral_add (integrable_const _) ((integrable_const C').indicator hSmeas),
            MeasureTheory.integral_const, integral_indicator_const _ hSmeas]
          simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul]
          ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun ω ↦ norm_nonneg _)]
  have hN' := hN n hn
  rw [Real.dist_eq, sub_zero] at hN'
  linarith [hbound, hN', le_abs_self (C' * (P {ω | δ / 2 ≤ ‖g n ω‖}).toReal)]

/-- **Bounded convergence in probability.** On a probability space, if `g n → 0` in measure and
`‖g n‖ ≤ C` a.e. uniformly in `n`, then `∫ g n → 0`. This is the quantitative core of the
bounded-convergence steps of the martingale CLT (`V_n →ᵖ σ²` and `L_n(ε) →ᵖ 0`). -/
lemma tendsto_integral_of_tendstoInMeasure_zero [IsProbabilityMeasure P] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ → Ω → E} {C : ℝ}
    (hmeas : ∀ n, StronglyMeasurable (g n)) (hbdd : ∀ n, ∀ᵐ ω ∂P, ‖g n ω‖ ≤ C)
    (hconv : TendstoInMeasure P g atTop 0) :
    Tendsto (fun n ↦ ∫ ω, g n ω ∂P) atTop (𝓝 0) :=
  squeeze_zero_norm (fun n ↦ norm_integral_le_integral_norm (g n))
    (tendsto_integral_norm_of_tendstoInMeasure_zero hmeas hbdd hconv)

/-- **Bounded × (→ 0 in measure) = → 0 in measure.** If `‖f n‖ ≤ C` a.e. and `h n → 0` in
measure, then `f n · h n → 0` in measure. -/
lemma tendstoInMeasure_bdd_mul {f h : ℕ → Ω → ℂ} {C : ℝ}
    (hf : ∀ n, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ C) (hh : TendstoInMeasure P h atTop 0) :
    TendstoInMeasure P (fun n ω ↦ f n ω * h n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_dist]
  rw [tendstoInMeasure_iff_dist] at hh
  intro ε hε
  let C' := max C 1
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : ∀ n, {ω | ε ≤ dist (f n ω * h n ω) 0} ≤ᵐ[P] {ω | ε / C' ≤ dist (h n ω) 0} := by
    intro n
    filter_upwards [hf n] with ω hbd hmem
    have h1 : ε ≤ ‖f n ω‖ * ‖h n ω‖ := by
      have hd : ε ≤ dist (f n ω * h n ω) 0 := hmem
      rwa [dist_zero_right, norm_mul] at hd
    change ε / C' ≤ dist (h n ω) 0
    rw [dist_zero_right, div_le_iff₀ hC'0]
    calc ε ≤ ‖f n ω‖ * ‖h n ω‖ := h1
      _ ≤ C' * ‖h n ω‖ :=
          mul_le_mul_of_nonneg_right (le_trans hbd (le_max_left _ _)) (norm_nonneg _)
      _ = ‖h n ω‖ * C' := mul_comm _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hh (ε / C') (by positivity))
    (fun _ ↦ zero_le) (fun n ↦ measure_mono_ae (hsub n))

/-- **Domination for convergence in measure.** If `0 ≤ g n ≤ h n` a.e. and `h n → 0` in measure,
then `g n → 0` in measure. -/
lemma tendstoInMeasure_zero_of_le {g h : ℕ → Ω → ℝ}
    (hg0 : ∀ n, (0 : Ω → ℝ) ≤ᵐ[P] g n) (hgh : ∀ n, g n ≤ᵐ[P] h n)
    (hh : TendstoInMeasure P h atTop 0) : TendstoInMeasure P g atTop 0 := by
  rw [tendstoInMeasure_iff_dist]
  rw [tendstoInMeasure_iff_dist] at hh
  intro ε hε
  have hsub : ∀ n, {ω | ε ≤ dist (g n ω) 0} ≤ᵐ[P] {ω | ε ≤ dist (h n ω) 0} := by
    intro n
    filter_upwards [hg0 n, hgh n] with ω h0 h1 hmem
    simp only [Pi.zero_apply] at h0
    have hg : ε ≤ dist (g n ω) 0 := hmem
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0] at hg
    change ε ≤ dist (h n ω) 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_trans h0 h1)]
    exact le_trans hg h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hh ε hε)
    (fun _ ↦ zero_le) (fun n ↦ measure_mono_ae (hsub n))

/-- **Tail of a square-integrable variable vanishes.** If `Z²` is integrable, then
`∫ Z²·𝟙{|Z|>c} → 0` as `c → ∞`. This is the analytic heart of the i.i.d. Lindeberg condition:
each cell's conditional Lindeberg quantity is (a proportion times) `E[(ξ-θ)²𝟙{|ξ-θ|>c_n}]` with
`c_n → ∞`. -/
lemma tendsto_integral_sq_indicator_gt {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ2 : Integrable (fun ω ↦ (Z ω) ^ 2) P) :
    Tendsto (fun c : ℝ ↦ ∫ ω, {ω | c < |Z ω|}.indicator (fun ω ↦ (Z ω) ^ 2) ω ∂P)
      atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∫ _ω, (0 : ℝ) ∂P by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun ω ↦ (Z ω) ^ 2)
    (Eventually.of_forall fun c ↦ (hZ2.aestronglyMeasurable).indicator
      (measurableSet_lt measurable_const hZ.abs))
    (Eventually.of_forall fun c ↦ ae_of_all _ fun ω ↦ ?_) hZ2 (ae_of_all _ fun ω ↦ ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω)]
    exact Set.indicator_le_self' (fun a _ ↦ sq_nonneg (Z a)) ω
  · apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_gt_atTop (|Z ω|)] with c hc
    exact Set.indicator_of_notMem (show ω ∉ {ω | c < |Z ω|} from not_lt.mpr hc.le) _

end BoundedConvergence

section Array

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A triangular array of square-integrable martingale differences, with one filtration per row:
row `n` carries its own filtration `𝓕 n` and increments `d n 0, …, d n (k n - 1)`, each `d n i`
measurable with respect to `𝓕 n (i+1)`, square integrable, and a martingale difference
`E[d n i | 𝓕 n i] = 0`. This is the data of the Lindeberg martingale central limit theorem.

Allowing the filtration to depend on the row `n` costs nothing: every step of the argument works
within a single row, and the cross-row limits (`V_n → σ²`, `L_n(ε) → 0` in probability) only refer
to the measure `P`. It is what lets the self-normalized/joint applications feed a different
filtration for each normalization. -/
structure MartDiffArray (P : Measure Ω) where
  /-- The filtration of row `n`. -/
  𝓕 : ℕ → Filtration ℕ mΩ
  /-- `d n i` is the `i`-th increment of row `n`. -/
  d : ℕ → ℕ → Ω → ℝ
  /-- `k n` is the length of row `n`. -/
  k : ℕ → ℕ
  /-- Each increment is square integrable. -/
  memLp : ∀ n i, MemLp (d n i) 2 P
  /-- Martingale-difference property. -/
  mgdiff : ∀ n i, P[d n i | 𝓕 n i] =ᵐ[P] 0
  /-- `d n i` is revealed at step `i + 1` of row `n`. -/
  adapted : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (d n i)

namespace MartDiffArray

variable {P : Measure Ω} (A : MartDiffArray P)

/-- Row sum `S_n = ∑_{i<k n} d n i`. -/
noncomputable def rowSum (n : ℕ) : Ω → ℝ := fun ω ↦ ∑ i ∈ Finset.range (A.k n), A.d n i ω

/-- Conditional variance of cell `(n,i)`: `v_{n,i} = E[d n i ² | 𝓕 i]`. -/
noncomputable def condVar (n i : ℕ) : Ω → ℝ := P[fun ω ↦ (A.d n i ω) ^ 2 | A.𝓕 n i]

/-- Predictable quadratic variation of row `n`: `V_n = ∑_{i<k n} v_{n,i}`. -/
noncomputable def predVar (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range (A.k n), A.condVar n i ω

/-- Conditional Lindeberg quantity `L_n(ε) = ∑_{i<k n} E[d n i ² 𝟙{|d n i|>ε} | 𝓕 i]`. -/
noncomputable def lindeberg (n : ℕ) (ε : ℝ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range (A.k n),
    (P[{ω | ε < |A.d n i ω|}.indicator (fun ω ↦ (A.d n i ω) ^ 2) | A.𝓕 n i]) ω

@[fun_prop]
lemma measurable_d (n i : ℕ) : Measurable (A.d n i) :=
  (A.adapted n i).measurable.mono ((A.𝓕 n).le (i + 1)) le_rfl

@[fun_prop]
lemma integrable_sq (n i : ℕ) :
    Integrable (fun ω ↦ (A.d n i ω) ^ 2) P := (A.memLp n i).integrable_sq

/-- **Uniform smallness of the conditional variances** (blueprint `lem:clt_max_var`):
each cell variance is controlled by `ε²` plus the whole Lindeberg sum. -/
lemma condVar_le_lindeberg [IsProbabilityMeasure P] (n i : ℕ) (hi : i < A.k n) (ε : ℝ) :
    A.condVar n i ≤ᵐ[P] fun ω ↦ ε ^ 2 + A.lindeberg n ε ω := by
  have hsq := condExp_sq_le (A.measurable_d n i) (A.integrable_sq n i) ((A.𝓕 n).le i) ε
  have hnn : ∀ j, (0 : Ω → ℝ) ≤ᵐ[P]
      P[{ω | ε < |A.d n j ω|}.indicator (fun ω ↦ (A.d n j ω) ^ 2) | A.𝓕 n j] :=
    fun j ↦ condExp_nonneg (ae_of_all _ fun ω ↦
      Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω)
  have hterm :
      (fun ω ↦ (P[{ω | ε < |A.d n i ω|}.indicator (fun ω ↦ (A.d n i ω) ^ 2) | A.𝓕 n i]) ω)
        ≤ᵐ[P] A.lindeberg n ε := by
    filter_upwards [ae_all_iff.mpr hnn] with ω hω
    simp only [Pi.zero_apply] at hω
    simp only [lindeberg]
    exact Finset.single_le_sum (fun j _ ↦ hω j) (Finset.mem_range.mpr hi)
  filter_upwards [hsq, hterm] with ω h1 h2
  simp only [condVar]
  linarith

lemma condVar_nonneg (n i : ℕ) : (0 : Ω → ℝ) ≤ᵐ[P] A.condVar n i :=
  condExp_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _)

/-- **Sum of squared conditional variances** (blueprint `lem:clt_sum_var_sq`):
`∑_i v_{n,i}² ≤ (ε² + L_n(ε)) · V_n` a.e., for every `ε`. -/
lemma sum_condVar_sq_le [IsProbabilityMeasure P] (n : ℕ) (ε : ℝ) :
    (fun ω ↦ ∑ i ∈ Finset.range (A.k n), (A.condVar n i ω) ^ 2)
      ≤ᵐ[P] fun ω ↦ (ε ^ 2 + A.lindeberg n ε ω) * A.predVar n ω := by
  have hcell : ∀ i, ∀ᵐ ω ∂P, i ∈ Finset.range (A.k n) →
      (A.condVar n i ω) ^ 2 ≤ A.condVar n i ω * (ε ^ 2 + A.lindeberg n ε ω) := by
    intro i
    by_cases hi : i ∈ Finset.range (A.k n)
    · filter_upwards [A.condVar_le_lindeberg n i (Finset.mem_range.mp hi) ε,
        A.condVar_nonneg n i] with ω h1 h2
      intro _
      simp only [Pi.zero_apply] at h2
      nlinarith [h1, h2]
    · exact ae_of_all _ fun ω hmem ↦ absurd hmem hi
  filter_upwards [ae_all_iff.mpr hcell] with ω hω
  calc ∑ i ∈ Finset.range (A.k n), (A.condVar n i ω) ^ 2
      ≤ ∑ i ∈ Finset.range (A.k n), A.condVar n i ω * (ε ^ 2 + A.lindeberg n ε ω) :=
        Finset.sum_le_sum fun i hi ↦ hω i hi
    _ = (ε ^ 2 + A.lindeberg n ε ω) * A.predVar n ω := by
        simp only [MartDiffArray.predVar]; rw [← Finset.sum_mul]; ring

/-- **Sum of the conditional-remainder majorants** (blueprint `lem:clt_sum_rem`):
`∑_i E[min(2t²d_i², |t|³|d_i|³) | 𝓕 i] ≤ |t|³ε·V_n + 2t²·L_n(ε)` a.e., for `ε ≥ 0`.
Together with Lemma `norm_condExp_expI_sub_le` this bounds `∑_i ‖r_{n,i}‖`. -/
lemma sum_condExp_min_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    (fun ω ↦ ∑ i ∈ Finset.range (A.k n),
        (P[fun ω ↦ min (2 * t ^ 2 * (A.d n i ω) ^ 2) (|t| ^ 3 * |A.d n i ω| ^ 3) | A.𝓕 n i]) ω)
      ≤ᵐ[P] fun ω ↦ |t| ^ 3 * ε * A.predVar n ω + 2 * t ^ 2 * A.lindeberg n ε ω := by
  have hcell : ∀ i, ∀ᵐ ω ∂P, i ∈ Finset.range (A.k n) →
      (P[fun ω ↦ min (2 * t ^ 2 * (A.d n i ω) ^ 2) (|t| ^ 3 * |A.d n i ω| ^ 3) | A.𝓕 n i]) ω ≤
        |t| ^ 3 * ε * (P[fun ω ↦ (A.d n i ω) ^ 2 | A.𝓕 n i]) ω
          + 2 * t ^ 2 *
            (P[{ω | ε < |A.d n i ω|}.indicator (fun ω ↦ (A.d n i ω) ^ 2) | A.𝓕 n i]) ω := by
    intro i
    by_cases hi : i ∈ Finset.range (A.k n)
    · filter_upwards
        [condExp_min_le (A.measurable_d n i) (A.integrable_sq n i) hε t] with ω hω
      intro _; exact hω
    · exact ae_of_all _ fun ω hmem ↦ absurd hmem hi
  filter_upwards [ae_all_iff.mpr hcell] with ω hω
  calc ∑ i ∈ Finset.range (A.k n),
        (P[fun ω ↦ min (2 * t ^ 2 * (A.d n i ω) ^ 2) (|t| ^ 3 * |A.d n i ω| ^ 3) | A.𝓕 n i]) ω
      ≤ ∑ i ∈ Finset.range (A.k n),
          (|t| ^ 3 * ε * (P[fun ω ↦ (A.d n i ω) ^ 2 | A.𝓕 n i]) ω
            + 2 * t ^ 2 *
              (P[{ω | ε < |A.d n i ω|}.indicator (fun ω ↦ (A.d n i ω) ^ 2) | A.𝓕 n i]) ω) :=
        Finset.sum_le_sum fun i hi ↦ hω i hi
    _ = |t| ^ 3 * ε * A.predVar n ω + 2 * t ^ 2 * A.lindeberg n ε ω := by
        simp only [MartDiffArray.predVar, MartDiffArray.condVar, MartDiffArray.lindeberg,
          Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Partial row sum `S_{n,j} = ∑_{i<j} d n i`. -/
noncomputable def partialSum (n j : ℕ) : Ω → ℝ := fun ω ↦ ∑ i ∈ Finset.range j, A.d n i ω

/-- Partial predictable variation `V_{n,j} = ∑_{i<j} v_{n,i}`. -/
noncomputable def partialVar (n j : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range j, A.condVar n i ω

/-- The exponential (almost-)martingale `Z_{n,j} = exp(it·S_{n,j} + (t²/2)·V_{n,j})`. -/
noncomputable def Zproc (t : ℝ) (n j : ℕ) : Ω → ℂ :=
  fun ω ↦ Complex.exp (((t * A.partialSum n j ω : ℝ) : ℂ) * I
    + ((t ^ 2 / 2 * A.partialVar n j ω : ℝ) : ℂ))

@[fun_prop]
lemma stronglyMeasurable_condVar (n i : ℕ) : StronglyMeasurable[A.𝓕 n i] (A.condVar n i) :=
  stronglyMeasurable_condExp

@[fun_prop]
lemma stronglyMeasurable_partialSum (n j : ℕ) :
    StronglyMeasurable[A.𝓕 n j] (A.partialSum n j) := by
  refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  exact (A.adapted n i).mono ((A.𝓕 n).mono (show i + 1 ≤ j by omega))

@[fun_prop]
lemma stronglyMeasurable_partialVar (n j : ℕ) :
    StronglyMeasurable[A.𝓕 n j] (A.partialVar n j) := by
  refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  exact (A.stronglyMeasurable_condVar n i).mono ((A.𝓕 n).mono (show i ≤ j by omega))

@[fun_prop]
lemma stronglyMeasurable_Zproc (t : ℝ) (n j : ℕ) :
    StronglyMeasurable[A.𝓕 n j] (A.Zproc t n j) := by
  refine Complex.continuous_exp.comp_stronglyMeasurable ?_
  refine ((Complex.continuous_ofReal.comp_stronglyMeasurable
    ((A.stronglyMeasurable_partialSum n j).const_mul t)).mul stronglyMeasurable_const).add ?_
  exact Complex.continuous_ofReal.comp_stronglyMeasurable
    ((A.stronglyMeasurable_partialVar n j).const_mul (t ^ 2 / 2))

/-- The `𝓕 j`-measurable factor `exp((t²/2) v_{n,j})`, the predictable part of the one-step
`Z`-increment. -/
@[fun_prop]
lemma stronglyMeasurable_expVar (t : ℝ) (n j : ℕ) :
    StronglyMeasurable[A.𝓕 n j] (fun ω ↦ Complex.exp ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ)) :=
  Complex.continuous_exp.comp_stronglyMeasurable
    (Complex.continuous_ofReal.comp_stronglyMeasurable
      ((A.stronglyMeasurable_condVar n j).const_mul (t ^ 2 / 2)))

/-- One-step factorisation of the `Z`-process:
`Z_{n,j+1} = Z_{n,j} · exp(it·d_{n,j} + (t²/2)·v_{n,j})`. -/
lemma Zproc_succ (t : ℝ) (n j : ℕ) (ω : Ω) :
    A.Zproc t n (j + 1) ω = A.Zproc t n j ω *
      Complex.exp (((t * A.d n j ω : ℝ) : ℂ) * I + ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ)) := by
  simp only [MartDiffArray.Zproc, MartDiffArray.partialSum, MartDiffArray.partialVar,
    Finset.sum_range_succ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `‖Z_{n,j} ω‖ = exp((t²/2) V_{n,j} ω)`. -/
lemma norm_Zproc (t : ℝ) (n j : ℕ) (ω : Ω) :
    ‖A.Zproc t n j ω‖ = Real.exp (t ^ 2 / 2 * A.partialVar n j ω) := by
  simp only [MartDiffArray.Zproc, Complex.norm_exp]
  rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re]
  ring_nf

/-- The partial variance through step `i` (`V_{n,i+1} = ∑_{l≤i} v_{n,l}`) is `𝓕 i`-measurable:
it involves only `v_{n,0},…,v_{n,i}`. This predictability is what makes the truncation stopping
rule `𝟙{V_{n,i+1} ≤ B}` a legitimate (`𝓕 i`-measurable) weight. -/
@[fun_prop]
lemma stronglyMeasurable_partialVar_succ (n i : ℕ) :
    StronglyMeasurable[A.𝓕 n i] (A.partialVar n (i + 1)) := by
  refine Finset.stronglyMeasurable_fun_sum _ fun l hl ↦ ?_
  rw [Finset.mem_range] at hl
  exact (A.stronglyMeasurable_condVar n l).mono ((A.𝓕 n).mono (show l ≤ i by omega))

/-- The array truncated at predictable-variance level `B`: increment `i` is kept only while the
next partial variance `V_{n,i+1}` (which is `𝓕 i`-measurable) stays `≤ B`. Because `V` is
nondecreasing, the resulting predictable variation never exceeds `B` — there is no overshoot
(Lemma `predVar_trunc_le`). -/
noncomputable def trunc (A : MartDiffArray P) [IsFiniteMeasure P] (B : ℝ) : MartDiffArray P where
  𝓕 := A.𝓕
  k := A.k
  d n i := {ω | A.partialVar n (i + 1) ω ≤ B}.indicator (A.d n i)
  memLp n i := MemLp.indicator
    (measurableSet_le
      ((A.stronglyMeasurable_partialVar_succ n i).measurable.mono ((A.𝓕 n).le i) le_rfl)
      measurable_const) (A.memLp n i)
  adapted n i := (A.adapted n i).indicator
    (measurableSet_le
      ((A.stronglyMeasurable_partialVar_succ n i).measurable.mono ((A.𝓕 n).mono i.le_succ) le_rfl)
      measurable_const)
  mgdiff n i := by
    refine (condExp_indicator ((A.memLp n i).integrable one_le_two)
      (measurableSet_le (A.stronglyMeasurable_partialVar_succ n i).measurable
        measurable_const)).trans ?_
    filter_upwards [A.mgdiff n i] with ω hω
    simp only [Pi.zero_apply] at hω ⊢
    by_cases hmem : ω ∈ {ω | A.partialVar n (i + 1) ω ≤ B}
    · rw [Set.indicator_of_mem hmem, hω]
    · rw [Set.indicator_of_notMem hmem]

/-- Prefix-capped sum bound: a nonnegative sequence, each term kept only while the running
partial sum stays `≤ B`, has total `≤ B` (no overshoot). The engine behind `predVar_trunc_le`. -/
lemma sum_indicator_le {v : ℕ → ℝ} (hv : ∀ i, 0 ≤ v i) {B : ℝ} (hB : 0 ≤ B) (j : ℕ) :
    ∑ i ∈ Finset.range j, (if ∑ l ∈ Finset.range (i + 1), v l ≤ B then v i else 0) ≤ B := by
  induction j with
  | zero => simpa using hB
  | succ j ih =>
    rw [Finset.sum_range_succ]
    by_cases h : ∑ l ∈ Finset.range (j + 1), v l ≤ B
    · rw [if_pos h]
      have hWV : ∑ i ∈ Finset.range j, (if ∑ l ∈ Finset.range (i + 1), v l ≤ B then v i else 0)
          ≤ ∑ i ∈ Finset.range j, v i := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        split
        · exact le_refl _
        · exact hv i
      have hsucc := Finset.sum_range_succ v j
      linarith [hWV, h, hsucc]
    · rw [if_neg h, add_zero]; exact ih

lemma measurableSet_truncSet_filt (B : ℝ) (n i : ℕ) :
    MeasurableSet[A.𝓕 n i] {ω | A.partialVar n (i + 1) ω ≤ B} :=
  measurableSet_le (A.stronglyMeasurable_partialVar_succ n i).measurable measurable_const

/-- The truncated conditional variance is the original one, weighted by the (predictable) stopping
indicator: `v̄_{n,i} = 𝟙{V_{n,i+1} ≤ B} · v_{n,i}` a.e. -/
lemma condVar_trunc [IsFiniteMeasure P] (B : ℝ) (n i : ℕ) :
    (A.trunc B).condVar n i =ᵐ[P]
      {ω | A.partialVar n (i + 1) ω ≤ B}.indicator (A.condVar n i) := by
  have hsq : (fun ω ↦ ({ω | A.partialVar n (i + 1) ω ≤ B}.indicator (A.d n i) ω) ^ 2)
      = {ω | A.partialVar n (i + 1) ω ≤ B}.indicator (fun ω ↦ (A.d n i ω) ^ 2) := by
    funext ω
    by_cases h : ω ∈ {ω | A.partialVar n (i + 1) ω ≤ B}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
  have heq : (A.trunc B).condVar n i
      = P[{ω | A.partialVar n (i + 1) ω ≤ B}.indicator (fun ω ↦ (A.d n i ω) ^ 2) | A.𝓕 n i] := by
    rw [← hsq]; rfl
  rw [heq]
  exact condExp_indicator (A.integrable_sq n i) (A.measurableSet_truncSet_filt B n i)

/-- **No overshoot** (blueprint `lem:clt_truncation`(ii)): the predictable variation of the
array truncated at level `B ≥ 0` is bounded by the constant `B`. -/
lemma predVar_trunc_le [IsProbabilityMeasure P] {B : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    (A.trunc B).predVar n ≤ᵐ[P] fun _ ↦ B := by
  filter_upwards [ae_all_iff.mpr fun i ↦ A.condVar_trunc B n i,
    ae_all_iff.mpr fun i ↦ A.condVar_nonneg n i] with ω hcvω hnnω
  simp only [Pi.zero_apply] at hnnω
  change ∑ i ∈ Finset.range ((A.trunc B).k n), (A.trunc B).condVar n i ω ≤ B
  have hkey : ∀ i ∈ Finset.range (A.k n), (A.trunc B).condVar n i ω
      = (if ∑ l ∈ Finset.range (i + 1), A.condVar n l ω ≤ B then A.condVar n i ω else 0) := by
    intro i _
    rw [hcvω i, Set.indicator_apply]
    rfl
  rw [show (A.trunc B).k n = A.k n from rfl, Finset.sum_congr rfl hkey]
  exact sum_indicator_le hnnω hB (A.k n)

/-- Truncation only shrinks the conditional variances: `v̄_{n,i} ≤ v_{n,i}` a.e. -/
lemma condVar_trunc_le [IsFiniteMeasure P] (B : ℝ) (n i : ℕ) :
    (A.trunc B).condVar n i ≤ᵐ[P] A.condVar n i := by
  filter_upwards [A.condVar_trunc B n i, A.condVar_nonneg n i] with ω h1 h2
  simp only [Pi.zero_apply] at h2
  rw [h1, Set.indicator_apply]
  split
  · exact le_refl _
  · exact h2

/-- The partial predictable variation is nondecreasing in the number of steps. -/
lemma partialVar_mono (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    A.partialVar n a ≤ᵐ[P] A.partialVar n b := by
  filter_upwards [ae_all_iff.mpr fun l ↦ A.condVar_nonneg n l] with ω hω
  simp only [Pi.zero_apply] at hω
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun x hx ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hab))
    fun l _ _ ↦ hω l

/-- **One-step conditional increment of the `Z`-process** (heart of `lem:clt_Z_expectation`):
`E[Z_{n,j+1} - Z_{n,j} | 𝓕 j] = Z_{n,j}·e^{(t²/2)v_{n,j}}·E[e^{itΔ_{n,j}} | 𝓕 j] - Z_{n,j}` a.e.
The factor `Z_{n,j}·e^{(t²/2)v_{n,j}}` is `𝓕 j`-measurable and is pulled out of the conditional
expectation; the remaining `e^{itΔ_{n,j}}` is the fresh randomness. -/
lemma condExp_Zproc_increment [IsProbabilityMeasure P] (t : ℝ) (n j : ℕ)
    (hZj : Integrable (A.Zproc t n j) P) (hZj1 : Integrable (A.Zproc t n (j + 1)) P) :
    P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j] =ᵐ[P]
      fun ω ↦ A.Zproc t n j ω * Complex.exp ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ) *
          (P[fun ω ↦ Complex.exp (((t * A.d n j ω : ℝ) : ℂ) * I) | A.𝓕 n j]) ω
        - A.Zproc t n j ω := by
  set g : Ω → ℂ := fun ω ↦ Complex.exp (((t * A.d n j ω : ℝ) : ℂ) * I) with hg_def
  set fac : Ω → ℂ :=
    fun ω ↦ A.Zproc t n j ω * Complex.exp ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ) with hfac_def
  have hZeq : A.Zproc t n (j + 1) = fun ω ↦ fac ω * g ω := by
    funext ω
    rw [A.Zproc_succ t n j ω, hfac_def, hg_def,
      show ((t * A.d n j ω : ℝ) : ℂ) * I + ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ)
        = ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ) + ((t * A.d n j ω : ℝ) : ℂ) * I from by ring,
      Complex.exp_add]
    ring
  have hfac_sm : StronglyMeasurable[A.𝓕 n j] fac :=
    (A.stronglyMeasurable_Zproc t n j).mul (A.stronglyMeasurable_expVar t n j)
  have hg_aesm : AEStronglyMeasurable g P :=
    Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        ((A.memLp n j).aestronglyMeasurable.const_mul t)).mul aestronglyMeasurable_const)
  have hg_int : Integrable g P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hg_aesm (ae_of_all _ fun ω ↦ ?_)
    simp only [hg_def]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (t * A.d n j ω))
  have hpull : P[fun ω ↦ fac ω * g ω | A.𝓕 n j] =ᵐ[P] fun ω ↦ fac ω * (P[g | A.𝓕 n j]) ω := by
    have hfg : Integrable (fun ω ↦ (ContinuousLinearMap.mul ℝ ℂ) (fac ω) (g ω)) P := by
      simp only [ContinuousLinearMap.mul_apply']
      rw [← hZeq]; exact hZj1
    simpa only [ContinuousLinearMap.mul_apply'] using
      condExp_bilin_of_stronglyMeasurable_left (B := ContinuousLinearMap.mul ℝ ℂ) hfac_sm hfg hg_int
  have hZ1c : P[A.Zproc t n (j + 1) | A.𝓕 n j] =ᵐ[P] fun ω ↦ fac ω * (P[g | A.𝓕 n j]) ω := by
    rw [hZeq]; exact hpull
  have hZjc : P[A.Zproc t n j | A.𝓕 n j] = A.Zproc t n j :=
    condExp_of_stronglyMeasurable ((A.𝓕 n).le j) (A.stronglyMeasurable_Zproc t n j) hZj
  filter_upwards [condExp_sub hZj1 hZj (A.𝓕 n j), hZ1c] with ω h1 h2
  rw [h1, Pi.sub_apply, h2, congrFun hZjc ω]

/-- One-step increment of the partial predictable variation: `V_{n,j+1} = V_{n,j} + v_{n,j}`. -/
lemma partialVar_succ (n j : ℕ) (ω : Ω) :
    A.partialVar n (j + 1) ω = A.partialVar n j ω + A.condVar n j ω := by
  simp only [MartDiffArray.partialVar, Finset.sum_range_succ]

/-- **One-step norm bound for the `Z`-increment** (core estimate of `lem:clt_Z_expectation`):
a.e. `‖E[Z_{n,j+1} - Z_{n,j} | 𝓕 j]‖` is at most
`e^{(t²/2)V_{n,j+1}}·((t⁴/4)v_{n,j}² + E[min(2t²Δ²,|t|³|Δ|³)|𝓕 j])`.
The predictable prefactor `e^{(t²/2)V_{n,j+1}}` is bounded once the array has bounded predictable
variation (`V_n ≤ B`), which is what makes the telescoped sum converge. -/
lemma norm_condExp_Zproc_increment_le [IsProbabilityMeasure P] (t : ℝ) (n j : ℕ)
    (hZj : Integrable (A.Zproc t n j) P) (hZj1 : Integrable (A.Zproc t n (j + 1)) P) :
    (fun ω ↦ ‖(P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω‖) ≤ᵐ[P]
      fun ω ↦ Real.exp (t ^ 2 / 2 * A.partialVar n (j + 1) ω) *
        (t ^ 4 / 4 * (A.condVar n j ω) ^ 2 +
          (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
            | A.𝓕 n j]) ω) := by
  filter_upwards [A.condExp_Zproc_increment t n j hZj hZj1,
    norm_condExp_expI_sub_le ((A.𝓕 n).le j) (A.memLp n j) (A.mgdiff n j) t,
    A.condVar_nonneg n j] with ω hinc hchar hnn
  simp only [Pi.zero_apply] at hnn
  let w : ℂ := (P[fun ω ↦ Complex.exp (((t * A.d n j ω : ℝ) : ℂ) * I) | A.𝓕 n j]) ω
  have hw : ‖w - (1 - ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ))‖
      ≤ (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
        | A.𝓕 n j]) ω := hchar
  have hfac := norm_expVar_mul_sub_one_le (v := A.condVar n j ω) hnn hw
  have hZfactor : A.Zproc t n j ω * Complex.exp ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ) * w
        - A.Zproc t n j ω
      = A.Zproc t n j ω * (Complex.exp ((t ^ 2 / 2 * A.condVar n j ω : ℝ) : ℂ) * w - 1) := by ring
  rw [hinc, hZfactor, norm_mul, A.norm_Zproc t n j ω]
  refine le_trans (mul_le_mul_of_nonneg_left hfac
    (Real.exp_pos (t ^ 2 / 2 * A.partialVar n j ω)).le) (le_of_eq ?_)
  rw [A.partialVar_succ n j ω, show t ^ 2 / 2 * (A.partialVar n j ω + A.condVar n j ω)
      = t ^ 2 / 2 * A.partialVar n j ω + t ^ 2 / 2 * A.condVar n j ω from by ring,
    Real.exp_add, mul_assoc]

/-- The `Z`-process starts at `1`: `Z_{n,0} = 1` (empty partial sum and variation). -/
lemma Zproc_zero (t : ℝ) (n : ℕ) : A.Zproc t n 0 = fun _ ↦ 1 := by
  funext ω
  simp [MartDiffArray.Zproc, MartDiffArray.partialSum, MartDiffArray.partialVar]

/-- Under a bound `V_{n,j} ω ≤ B` on the partial predictable variation, the `Z`-process is
uniformly bounded: `‖Z_{n,j} ω‖ ≤ e^{(t²/2)B}`. -/
lemma norm_Zproc_le_of_le {t : ℝ} {n j : ℕ} {B : ℝ} {ω : Ω} (h : A.partialVar n j ω ≤ B) :
    ‖A.Zproc t n j ω‖ ≤ Real.exp (t ^ 2 / 2 * B) := by
  rw [A.norm_Zproc t n j ω]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (by positivity))

/-- With bounded partial predictable variation (`V_{n,j} ≤ B` a.e.), `Z_{n,j}` is integrable
(it is bounded by the constant `e^{(t²/2)B}`). -/
@[fun_prop]
lemma integrable_Zproc_of_le [IsProbabilityMeasure P] (t : ℝ) (n j : ℕ) {B : ℝ}
    (h : A.partialVar n j ≤ᵐ[P] fun _ ↦ B) : Integrable (A.Zproc t n j) P := by
  refine Integrable.mono' (integrable_const (Real.exp (t ^ 2 / 2 * B)))
    ((A.stronglyMeasurable_Zproc t n j).mono ((A.𝓕 n).le j)).aestronglyMeasurable ?_
  filter_upwards [h] with ω hω
  exact A.norm_Zproc_le_of_le hω

/-- Each conditional variance is dominated by the predictable variation (all summands ≥ 0). -/
lemma condVar_le_predVar {n j : ℕ} (hj : j < A.k n) : A.condVar n j ≤ᵐ[P] A.predVar n := by
  filter_upwards [ae_all_iff.mpr fun l ↦ A.condVar_nonneg n l] with ω hω
  simp only [Pi.zero_apply] at hω
  simp only [MartDiffArray.predVar]
  exact Finset.single_le_sum (fun l _ ↦ hω l) (Finset.mem_range.mpr hj)

/-- Bounded predictable variation caps every partial predictable variation: `V_{n,j} ≤ B` a.e.
for `j ≤ k n`. -/
lemma partialVar_le_of_predVar_le {B : ℝ} {n : ℕ} (hB : A.predVar n ≤ᵐ[P] fun _ ↦ B)
    {j : ℕ} (hj : j ≤ A.k n) : A.partialVar n j ≤ᵐ[P] fun _ ↦ B := by
  filter_upwards [A.partialVar_mono n hj, hB] with ω h1 h2
  exact le_trans h1 h2

/-- With bounded predictable variation, each squared conditional variance is integrable
(it is dominated by `B · v_{n,j}`). -/
@[fun_prop]
lemma integrable_condVar_sq {B : ℝ} {n j : ℕ}
    (hB : A.predVar n ≤ᵐ[P] fun _ ↦ B) (hj : j < A.k n) :
    Integrable (fun ω ↦ (A.condVar n j ω) ^ 2) P := by
  have hb : A.condVar n j ≤ᵐ[P] fun _ ↦ B := (A.condVar_le_predVar hj).trans hB
  have haesm : AEStronglyMeasurable (A.condVar n j) P :=
    ((A.stronglyMeasurable_condVar n j).mono ((A.𝓕 n).le j)).aestronglyMeasurable
  have hdom : Integrable (fun ω ↦ B * A.condVar n j ω) P := by
    have : Integrable (A.condVar n j) P := integrable_condExp
    exact this.const_mul B
  refine Integrable.mono' hdom ((continuous_pow 2).comp_aestronglyMeasurable haesm) ?_
  filter_upwards [hb, A.condVar_nonneg n j] with ω hbω hnnω
  simp only [Pi.zero_apply] at hnnω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hbω) hnnω]

/-- **Pointwise summed one-step bound** (bounded-variance step towards `lem:clt_Z_expectation`).
Under `V_n ≤ B` a.e., summing the one-step norm bounds over `j < k n` gives, a.e.,
`∑_j ‖E[Z_{j+1}-Z_j|𝓕 j]‖ ≤ e^{(t²/2)B}·((t⁴/4)∑_j v_{n,j}² + ∑_j E[min(2t²Δ²,|t|³|Δ|³)|𝓕 j])`. -/
lemma sum_norm_condExp_increment_le [IsProbabilityMeasure P] (t : ℝ) (n : ℕ) {B : ℝ}
    (hB : A.predVar n ≤ᵐ[P] fun _ ↦ B) :
    (fun ω ↦ ∑ j ∈ Finset.range (A.k n),
        ‖(P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω‖) ≤ᵐ[P]
      fun ω ↦ Real.exp (t ^ 2 / 2 * B) *
        (t ^ 4 / 4 * (∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2)
          + ∑ j ∈ Finset.range (A.k n),
              (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
                | A.𝓕 n j]) ω) := by
  have hcell : ∀ j, ∀ᵐ ω ∂P, j ∈ Finset.range (A.k n) →
      ‖(P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω‖ ≤
        Real.exp (t ^ 2 / 2 * B) * (t ^ 4 / 4 * (A.condVar n j ω) ^ 2 +
          (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
            | A.𝓕 n j]) ω) := by
    intro j
    by_cases hj : j ∈ Finset.range (A.k n)
    · have hj' := Finset.mem_range.mp hj
      have hZj := A.integrable_Zproc_of_le t n j (A.partialVar_le_of_predVar_le hB hj'.le)
      have hZj1 := A.integrable_Zproc_of_le t n (j + 1) (A.partialVar_le_of_predVar_le hB hj')
      filter_upwards [A.norm_condExp_Zproc_increment_le t n j hZj hZj1,
        A.partialVar_le_of_predVar_le hB hj',
        condExp_nonneg (μ := P) (m := A.𝓕 n j)
          (f := fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3))
          (ae_of_all _ fun ω ↦ le_min (by positivity) (by positivity))]
        with ω hbd hVle hr_nn
      intro _
      simp only [Pi.zero_apply] at hr_nn
      refine le_trans hbd (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hVle (by positivity)))
        (add_nonneg (by positivity) hr_nn))
    · exact ae_of_all _ fun ω hmem ↦ absurd hmem hj
  filter_upwards [ae_all_iff.mpr hcell] with ω hω
  calc ∑ j ∈ Finset.range (A.k n),
        ‖(P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω‖
      ≤ ∑ j ∈ Finset.range (A.k n), Real.exp (t ^ 2 / 2 * B) *
          (t ^ 4 / 4 * (A.condVar n j ω) ^ 2 +
            (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
              | A.𝓕 n j]) ω) := Finset.sum_le_sum fun j hj ↦ hω j hj
    _ = Real.exp (t ^ 2 / 2 * B) *
          (t ^ 4 / 4 * (∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2)
            + ∑ j ∈ Finset.range (A.k n),
                (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
                  | A.𝓕 n j]) ω) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Integral form of the almost-martingale bound** (bounded-variance core of
`lem:clt_Z_expectation`). Under `V_n ≤ B` a.e.,
`‖∫ Z_{n,k_n} - 1‖ ≤ e^{(t²/2)B}·((t⁴/4)∫∑_j v_{n,j}² + ∫∑_j E[min(2t²Δ²,|t|³|Δ|³)|𝓕 j])`.
The proof telescopes `∫ Z_{n,k_n} - 1 = ∑_j ∫ E[Z_{j+1}-Z_j|𝓕 j]` (tower property), then applies
the pointwise summed one-step bound `sum_norm_condExp_increment_le`. -/
lemma norm_integral_Zproc_sub_one_le [IsProbabilityMeasure P] (t : ℝ) (n : ℕ) {B : ℝ}
    (hB : A.predVar n ≤ᵐ[P] fun _ ↦ B) :
    ‖(∫ ω, A.Zproc t n (A.k n) ω ∂P) - 1‖ ≤
      Real.exp (t ^ 2 / 2 * B) *
        (t ^ 4 / 4 * (∫ ω, ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2 ∂P)
          + ∫ ω, ∑ j ∈ Finset.range (A.k n),
              (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
                | A.𝓕 n j]) ω ∂P) := by
  have hint : ∀ j, j ≤ A.k n → Integrable (A.Zproc t n j) P :=
    fun j hj ↦ A.integrable_Zproc_of_le t n j (A.partialVar_le_of_predVar_le hB hj)
  have hEnorm_int : ∀ j ∈ Finset.range (A.k n),
      Integrable (fun ω ↦ ‖(P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω‖) P :=
    fun j _ ↦ integrable_condExp.norm
  have hv2sum_int : Integrable (fun ω ↦ ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2) P :=
    integrable_finsetSum _ fun j hj ↦ A.integrable_condVar_sq hB (Finset.mem_range.mp hj)
  have hrsum_int : Integrable (fun ω ↦ ∑ j ∈ Finset.range (A.k n),
      (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
        | A.𝓕 n j]) ω) P :=
    integrable_finsetSum _ fun j _ ↦ integrable_condExp
  have hsum : ∑ j ∈ Finset.range (A.k n),
        ∫ ω, (P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω ∂P
      = (∫ ω, A.Zproc t n (A.k n) ω ∂P) - 1 := by
    have step : ∀ j ∈ Finset.range (A.k n),
        ∫ ω, (P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω ∂P
          = (∫ ω, A.Zproc t n (j + 1) ω ∂P) - (∫ ω, A.Zproc t n j ω ∂P) := by
      intro j hj
      rw [integral_condExp ((A.𝓕 n).le j)]
      exact integral_sub (hint (j + 1) (Finset.mem_range.mp hj))
        (hint j (le_of_lt (Finset.mem_range.mp hj)))
    rw [Finset.sum_congr rfl step,
      Finset.sum_range_sub (fun j ↦ ∫ ω, A.Zproc t n j ω ∂P) (A.k n), A.Zproc_zero t n]
    simp
  rw [← hsum]
  calc ‖∑ j ∈ Finset.range (A.k n),
        ∫ ω, (P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω ∂P‖
      ≤ ∑ j ∈ Finset.range (A.k n),
          ‖∫ ω, (P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω ∂P‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (A.k n),
          ∫ ω, ‖(P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω‖ ∂P :=
        Finset.sum_le_sum fun j _ ↦ norm_integral_le_integral_norm _
    _ = ∫ ω, ∑ j ∈ Finset.range (A.k n),
          ‖(P[A.Zproc t n (j + 1) - A.Zproc t n j | A.𝓕 n j]) ω‖ ∂P :=
        (integral_finsetSum _ hEnorm_int).symm
    _ ≤ ∫ ω, Real.exp (t ^ 2 / 2 * B) *
          (t ^ 4 / 4 * (∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2)
            + ∑ j ∈ Finset.range (A.k n),
                (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
                  | A.𝓕 n j]) ω) ∂P :=
        integral_mono_ae (integrable_finsetSum _ hEnorm_int)
          (((hv2sum_int.const_mul (t ^ 4 / 4)).add hrsum_int).const_mul (Real.exp (t ^ 2 / 2 * B)))
          (A.sum_norm_condExp_increment_le t n hB)
    _ = Real.exp (t ^ 2 / 2 * B) *
          (t ^ 4 / 4 * (∫ ω, ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2 ∂P)
            + ∫ ω, ∑ j ∈ Finset.range (A.k n),
                (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
                  | A.𝓕 n j]) ω ∂P) := by
        rw [MeasureTheory.integral_const_mul,
          integral_add (hv2sum_int.const_mul (t ^ 4 / 4)) hrsum_int,
          MeasureTheory.integral_const_mul]

/-- The Lindeberg quantity is integrable. -/
@[fun_prop]
lemma integrable_lindeberg (n : ℕ) (ε : ℝ) : Integrable (A.lindeberg n ε) P :=
  integrable_finsetSum _ fun _ _ ↦ integrable_condExp

/-- The predictable variation is integrable. -/
@[fun_prop]
lemma integrable_predVar (n : ℕ) : Integrable (A.predVar n) P :=
  integrable_finsetSum _ fun _ _ ↦ integrable_condExp

/-- The predictable variation is nonnegative a.e. -/
lemma predVar_nonneg (n : ℕ) : (0 : Ω → ℝ) ≤ᵐ[P] A.predVar n := by
  filter_upwards [ae_all_iff.mpr fun i ↦ A.condVar_nonneg n i] with ω hω
  simp only [Pi.zero_apply] at hω ⊢
  exact Finset.sum_nonneg fun i _ ↦ hω i

/-- The predictable variation is (strongly) measurable. -/
@[fun_prop]
lemma stronglyMeasurable_predVar (n : ℕ) : StronglyMeasurable (A.predVar n) :=
  Finset.stronglyMeasurable_fun_sum _ fun i _ ↦
    (A.stronglyMeasurable_condVar n i).mono ((A.𝓕 n).le i)

/-- The Lindeberg quantity is (strongly) measurable. -/
@[fun_prop]
lemma stronglyMeasurable_lindeberg (n : ℕ) (ε : ℝ) : StronglyMeasurable (A.lindeberg n ε) :=
  Finset.stronglyMeasurable_fun_sum _ fun j _ ↦
    stronglyMeasurable_condExp.mono ((A.𝓕 n).le j)

/-- The Lindeberg quantity is nonnegative a.e. -/
lemma lindeberg_nonneg (n : ℕ) (ε : ℝ) : (0 : Ω → ℝ) ≤ᵐ[P] A.lindeberg n ε := by
  have hcell : ∀ j, (0 : Ω → ℝ) ≤ᵐ[P]
      (P[{ω | ε < |A.d n j ω|}.indicator (fun ω ↦ (A.d n j ω) ^ 2) | A.𝓕 n j]) :=
    fun j ↦ condExp_nonneg (ae_of_all _ fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω)
  filter_upwards [ae_all_iff.mpr hcell] with ω hω
  simp only [Pi.zero_apply] at hω ⊢
  simp only [MartDiffArray.lindeberg]
  exact Finset.sum_nonneg fun j _ ↦ hω j

/-- The Lindeberg quantity never exceeds the predictable variation (dropping the indicators). -/
lemma lindeberg_le_predVar (n : ℕ) (ε : ℝ) : A.lindeberg n ε ≤ᵐ[P] A.predVar n := by
  have hcell : ∀ j, (P[{ω | ε < |A.d n j ω|}.indicator (fun ω ↦ (A.d n j ω) ^ 2) | A.𝓕 n j])
      ≤ᵐ[P] A.condVar n j := by
    intro j
    exact condExp_mono (m := A.𝓕 n j)
      ((A.integrable_sq n j).indicator (measurableSet_lt measurable_const (A.measurable_d n j).abs))
      (A.integrable_sq n j)
      (ae_of_all _ fun ω ↦ by
        rw [Set.indicator_apply]; split
        · exact le_refl _
        · exact sq_nonneg _)
  filter_upwards [ae_all_iff.mpr hcell] with ω hω
  simp only [MartDiffArray.lindeberg, MartDiffArray.predVar]
  exact Finset.sum_le_sum fun j _ ↦ hω j

/-- **Integral bound on the squared-variance sum** (bounded-variance): with `V_n ≤ B`,
`∫ ∑_j v_{n,j}² ≤ B·(ε² + ∫ L_n(ε))`. -/
lemma integral_sum_condVar_sq_le [IsProbabilityMeasure P] {B : ℝ} {n : ℕ}
    (hB : A.predVar n ≤ᵐ[P] fun _ ↦ B) (ε : ℝ) :
    (∫ ω, ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2 ∂P)
      ≤ B * (ε ^ 2 + ∫ ω, A.lindeberg n ε ω ∂P) := by
  have hv2_int : Integrable (fun ω ↦ ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2) P :=
    integrable_finsetSum _ fun j hj ↦ A.integrable_condVar_sq hB (Finset.mem_range.mp hj)
  have hbound_int : Integrable (fun ω ↦ (ε ^ 2 + A.lindeberg n ε ω) * B) P :=
    (((integrable_const (ε ^ 2)).add (A.integrable_lindeberg n ε)).mul_const B)
  have hle : (fun ω ↦ ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2)
      ≤ᵐ[P] fun ω ↦ (ε ^ 2 + A.lindeberg n ε ω) * B := by
    filter_upwards [A.sum_condVar_sq_le n ε, hB, A.lindeberg_nonneg n ε] with ω h1 h2 h3
    simp only [Pi.zero_apply] at h3
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (add_nonneg (by positivity) h3))
  calc (∫ ω, ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2 ∂P)
      ≤ ∫ ω, (ε ^ 2 + A.lindeberg n ε ω) * B ∂P := integral_mono_ae hv2_int hbound_int hle
    _ = B * (ε ^ 2 + ∫ ω, A.lindeberg n ε ω ∂P) := by
        rw [MeasureTheory.integral_mul_const,
          integral_add (integrable_const _) (A.integrable_lindeberg n ε),
          MeasureTheory.integral_const]
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul]
        ring

/-- **Integral bound on the remainder-majorant sum** (bounded-variance): with `V_n ≤ B` and
`ε ≥ 0`, `∫ ∑_j E[min(2t²Δ²,|t|³|Δ|³)|𝓕 j] ≤ |t|³·ε·B + 2t²·∫ L_n(ε)`. -/
lemma integral_sum_condExp_min_le [IsProbabilityMeasure P] {B : ℝ} {n : ℕ}
    (hB : A.predVar n ≤ᵐ[P] fun _ ↦ B) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    (∫ ω, ∑ j ∈ Finset.range (A.k n),
        (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
          | A.𝓕 n j]) ω ∂P)
      ≤ |t| ^ 3 * ε * B + 2 * t ^ 2 * ∫ ω, A.lindeberg n ε ω ∂P := by
  have hr_int : Integrable (fun ω ↦ ∑ j ∈ Finset.range (A.k n),
      (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
        | A.𝓕 n j]) ω) P :=
    integrable_finsetSum _ fun j _ ↦ integrable_condExp
  have hbound_int :
      Integrable (fun ω ↦ |t| ^ 3 * ε * A.predVar n ω + 2 * t ^ 2 * A.lindeberg n ε ω) P :=
    ((A.integrable_predVar n).const_mul (|t| ^ 3 * ε)).add
      ((A.integrable_lindeberg n ε).const_mul (2 * t ^ 2))
  have hVint : (∫ ω, A.predVar n ω ∂P) ≤ B := by
    calc (∫ ω, A.predVar n ω ∂P)
        ≤ ∫ _ω, (B : ℝ) ∂P := integral_mono_ae (A.integrable_predVar n) (integrable_const B) hB
      _ = B := by
          rw [MeasureTheory.integral_const]
          simp [measureReal_def, measure_univ]
  calc (∫ ω, ∑ j ∈ Finset.range (A.k n),
        (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
          | A.𝓕 n j]) ω ∂P)
      ≤ ∫ ω, (|t| ^ 3 * ε * A.predVar n ω + 2 * t ^ 2 * A.lindeberg n ε ω) ∂P :=
        integral_mono_ae hr_int hbound_int (A.sum_condExp_min_le n hε t)
    _ = |t| ^ 3 * ε * (∫ ω, A.predVar n ω ∂P) + 2 * t ^ 2 * ∫ ω, A.lindeberg n ε ω ∂P := by
        rw [integral_add ((A.integrable_predVar n).const_mul _)
            ((A.integrable_lindeberg n ε).const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ |t| ^ 3 * ε * B + 2 * t ^ 2 * ∫ ω, A.lindeberg n ε ω ∂P := by
        have hmul : |t| ^ 3 * ε * (∫ ω, A.predVar n ω ∂P) ≤ |t| ^ 3 * ε * B :=
          mul_le_mul_of_nonneg_left hVint (mul_nonneg (by positivity) hε)
        linarith [hmul]

/-- The row sum is the partial sum through step `k n`. -/
lemma rowSum_eq_partialSum (n : ℕ) : A.rowSum n = A.partialSum n (A.k n) := rfl

/-- The row sum is measurable. -/
@[fun_prop]
lemma measurable_rowSum (n : ℕ) : Measurable (A.rowSum n) :=
  ((A.stronglyMeasurable_partialSum n (A.k n)).mono ((A.𝓕 n).le (A.k n))).measurable

/-- `‖e^{itS_n}‖ = 1`. -/
lemma norm_expI_rowSum (t : ℝ) (n : ℕ) (ω : Ω) :
    ‖Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (t * A.rowSum n ω)

/-- `e^{itS_n}` is (strongly) measurable. -/
@[fun_prop]
lemma stronglyMeasurable_expI_rowSum (t : ℝ) (n : ℕ) :
    StronglyMeasurable (fun ω ↦ Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)) :=
  Complex.continuous_exp.comp_stronglyMeasurable
    ((Complex.continuous_ofReal.comp_stronglyMeasurable
      (((A.stronglyMeasurable_partialSum n (A.k n)).mono ((A.𝓕 n).le (A.k n))).const_mul t)).mul
      stronglyMeasurable_const)

/-- `e^{itS_n}` is integrable (bounded by `1`). -/
@[fun_prop]
lemma integrable_expI_rowSum [IsFiniteMeasure P] (t : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)) P :=
  Integrable.mono' (integrable_const 1) (A.stronglyMeasurable_expI_rowSum t n).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ le_of_eq (A.norm_expI_rowSum t n ω))

/-- The predictable variation is the partial variation through step `k n`. -/
lemma predVar_eq_partialVar (n : ℕ) : A.predVar n = A.partialVar n (A.k n) := rfl

/-- The characteristic-function integrand factors through the `Z`-process:
`e^{it S_n} = Z_{n,k_n} · e^{-(t²/2) V_n}` (since `Z_{n,k_n} = e^{it S_n + (t²/2) V_n}`). -/
lemma expI_rowSum_eq (t : ℝ) (n : ℕ) (ω : Ω) :
    Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)
      = A.Zproc t n (A.k n) ω * Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ) := by
  simp only [MartDiffArray.Zproc, A.rowSum_eq_partialSum, A.predVar_eq_partialVar]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

open Filter in
/-- The exponential weight `e^{-(t²/2)V_n}` converges in probability to `e^{-(t²/2)σ²}` whenever
`V_n → σ²` in probability (with `V_n ≥ 0` a.e., `σ² ≥ 0`, `t ≠ 0`). Via the `1`-Lipschitz bound
`abs_exp_neg_sub_le`. This is the `W_n → 0` step feeding the bounded-convergence part of
`clt_product`. -/
lemma tendstoInMeasure_expNeg_predVar_sub {t : ℝ} (ht : t ≠ 0)
    {σ2 : ℝ} (hσ2 : 0 ≤ σ2) (hVnn : ∀ n, (0 : Ω → ℝ) ≤ᵐ[P] A.predVar n)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2)) :
    TendstoInMeasure P (fun n ω ↦ Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ)
      - Complex.exp ((-(t ^ 2 / 2 * σ2) : ℝ) : ℂ)) atTop 0 := by
  rw [tendstoInMeasure_iff_dist]
  rw [tendstoInMeasure_iff_dist] at hV
  intro ε hε
  set c := t ^ 2 / 2 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hsub : ∀ n, {ω | ε ≤ dist (Complex.exp ((-(c * A.predVar n ω) : ℝ) : ℂ)
        - Complex.exp ((-(c * σ2) : ℝ) : ℂ)) 0}
      ≤ᵐ[P] {ω | ε / c ≤ dist (A.predVar n ω) σ2} := by
    intro n
    filter_upwards [hVnn n] with ω hnn hω
    have hnormeq : ‖Complex.exp ((-(c * A.predVar n ω) : ℝ) : ℂ)
          - Complex.exp ((-(c * σ2) : ℝ) : ℂ)‖
        = |Real.exp (-(c * A.predVar n ω)) - Real.exp (-(c * σ2))| := by
      rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
    have hω' : ε ≤ |Real.exp (-(c * A.predVar n ω)) - Real.exp (-(c * σ2))| := by
      have hmem : ε ≤ dist (Complex.exp ((-(c * A.predVar n ω) : ℝ) : ℂ)
          - Complex.exp ((-(c * σ2) : ℝ) : ℂ)) 0 := hω
      rwa [dist_zero_right, hnormeq] at hmem
    change ε / c ≤ dist (A.predVar n ω) σ2
    rw [Real.dist_eq]
    have hbnd := abs_exp_neg_sub_le (mul_nonneg hc0.le hnn) (mul_nonneg hc0.le hσ2)
    have hcabs : |c * A.predVar n ω - c * σ2| = c * |A.predVar n ω - σ2| := by
      rw [← mul_sub, abs_mul, abs_of_pos hc0]
    rw [hcabs] at hbnd
    rw [div_le_iff₀ hc0]
    calc ε ≤ |Real.exp (-(c * A.predVar n ω)) - Real.exp (-(c * σ2))| := hω'
      _ ≤ c * |A.predVar n ω - σ2| := hbnd
      _ = |A.predVar n ω - σ2| * c := mul_comm _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hV (ε / c) (by positivity))
    (fun _ ↦ zero_le) (fun n ↦ measure_mono_ae (hsub n))

open Filter in
/-- **Almost-martingale expectation** (blueprint `lem:clt_Z_expectation`, bounded-variance form).
If the array has predictable variation uniformly bounded by `B` (`V_n ≤ B` a.e.) and satisfies the
conditional Lindeberg condition (`L_n(ε) → 0` in probability for every `ε > 0`), then
`∫ Z_{n,k_n} → 1`. Combines the integral bound `norm_integral_Zproc_sub_one_le` with the two
variance/remainder integral bounds and bounded convergence in probability; the final double limit
sends `n → ∞` (so `∫ L_n(ε) → 0`) then `ε → 0`. -/
lemma clt_Z_expectation [IsProbabilityMeasure P] (t : ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n, A.predVar n ≤ᵐ[P] fun _ ↦ B)
    (hLindeberg : ∀ ε, 0 < ε → TendstoInMeasure P (fun n ↦ A.lindeberg n ε) atTop 0) :
    Tendsto (fun n ↦ ∫ ω, A.Zproc t n (A.k n) ω ∂P) atTop (𝓝 1) := by
  have hEL : ∀ ε, 0 < ε → Tendsto (fun n ↦ ∫ ω, A.lindeberg n ε ω ∂P) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_integral_of_tendstoInMeasure_zero (C := B)
      (fun n ↦ A.stronglyMeasurable_lindeberg n ε) (fun n ↦ ?_) (hLindeberg ε hε)
    filter_upwards [A.lindeberg_nonneg n ε, A.lindeberg_le_predVar n ε, hB n] with ω h0 h1 h2
    simp only [Pi.zero_apply] at h0
    rw [Real.norm_of_nonneg h0]
    exact le_trans h1 h2
  rw [← tendsto_sub_nhds_zero_iff]
  refine (tendsto_zero_iff_norm_tendsto_zero).mpr ?_
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro η hη
  obtain ⟨ε, hε, hGη⟩ : ∃ ε, 0 < ε ∧
      Real.exp (t ^ 2 / 2 * B) * B * (t ^ 4 / 4 * ε ^ 2 + |t| ^ 3 * ε) < η := by
    let EB := Real.exp (t ^ 2 / 2 * B) * B
    have hEB0 : 0 ≤ EB := mul_nonneg (Real.exp_pos _).le hB0
    set M := EB * (t ^ 4 / 4 + |t| ^ 3) with hMdef
    have hM0 : 0 ≤ M := mul_nonneg hEB0 (by positivity)
    have hden : 0 < M + 1 := by positivity
    refine ⟨min 1 (η / (M + 1)), lt_min one_pos (by positivity), ?_⟩
    let ε := min 1 (η / (M + 1))
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hε2 : ε ≤ η / (M + 1) := min_le_right _ _
    have hεpos : 0 < ε := lt_min one_pos (by positivity)
    have hsq : ε ^ 2 ≤ ε := by nlinarith [hεpos.le, hε1]
    have hstep : EB * (t ^ 4 / 4 * ε ^ 2 + |t| ^ 3 * ε) ≤ M * ε := by
      have hin : t ^ 4 / 4 * ε ^ 2 + |t| ^ 3 * ε ≤ (t ^ 4 / 4 + |t| ^ 3) * ε := by
        have hprod : (0 : ℝ) ≤ t ^ 4 / 4 * (ε - ε ^ 2) :=
          mul_nonneg (by positivity) (by linarith [hsq])
        nlinarith [hprod]
      calc EB * (t ^ 4 / 4 * ε ^ 2 + |t| ^ 3 * ε)
          ≤ EB * ((t ^ 4 / 4 + |t| ^ 3) * ε) := mul_le_mul_of_nonneg_left hin hEB0
        _ = M * ε := by rw [hMdef]; ring
    have hMε : M * ε < η := by
      calc M * ε ≤ M * (η / (M + 1)) := mul_le_mul_of_nonneg_left hε2 hM0
        _ < η := by rw [← mul_div_assoc, div_lt_iff₀ hden]; nlinarith [hη, hM0]
    linarith [hstep, hMε]
  set G := Real.exp (t ^ 2 / 2 * B) * B * (t ^ 4 / 4 * ε ^ 2 + |t| ^ 3 * ε) with hGdef
  set K := Real.exp (t ^ 2 / 2 * B) * (t ^ 4 / 4 * B + 2 * t ^ 2) with hKdef
  have hF : Tendsto (fun n ↦ G + K * ∫ ω, A.lindeberg n ε ω ∂P) atTop (𝓝 G) := by
    simpa using tendsto_const_nhds.add ((hEL ε hε).const_mul K)
  filter_upwards [hF.eventually_lt_const hGη] with n hn
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  refine lt_of_le_of_lt ?_ hn
  refine le_trans (A.norm_integral_Zproc_sub_one_le t n (hB n)) ?_
  have hmono : t ^ 4 / 4 * (∫ ω, ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2 ∂P)
        + ∫ ω, ∑ j ∈ Finset.range (A.k n),
            (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
              | A.𝓕 n j]) ω ∂P
      ≤ t ^ 4 / 4 * (B * (ε ^ 2 + ∫ ω, A.lindeberg n ε ω ∂P))
        + (|t| ^ 3 * ε * B + 2 * t ^ 2 * ∫ ω, A.lindeberg n ε ω ∂P) :=
    add_le_add (mul_le_mul_of_nonneg_left (A.integral_sum_condVar_sq_le (hB n) ε) (by positivity))
      (A.integral_sum_condExp_min_le (hB n) hε.le t)
  calc Real.exp (t ^ 2 / 2 * B) * (t ^ 4 / 4 *
          (∫ ω, ∑ j ∈ Finset.range (A.k n), (A.condVar n j ω) ^ 2 ∂P)
        + ∫ ω, ∑ j ∈ Finset.range (A.k n),
            (P[fun ω ↦ min (2 * t ^ 2 * (A.d n j ω) ^ 2) (|t| ^ 3 * |A.d n j ω| ^ 3)
              | A.𝓕 n j]) ω ∂P)
      ≤ Real.exp (t ^ 2 / 2 * B) * (t ^ 4 / 4 * (B * (ε ^ 2 + ∫ ω, A.lindeberg n ε ω ∂P))
          + (|t| ^ 3 * ε * B + 2 * t ^ 2 * ∫ ω, A.lindeberg n ε ω ∂P)) :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    _ = G + K * ∫ ω, A.lindeberg n ε ω ∂P := by rw [hGdef, hKdef]; ring

open Filter in
/-- **Characteristic-function limit, bounded-variance form** (core of blueprint `lem:clt_product`).
With `V_n ≤ B` a.e., `V_n → σ²` in probability and the conditional Lindeberg condition,
`E[e^{itS_n}] = charFun → e^{-σ²t²/2}`. The general form follows by the variance truncation. -/
lemma clt_charFun_bounded [IsProbabilityMeasure P] (t : ℝ) {B σ2 : ℝ} (hB0 : 0 ≤ B)
    (hσ2 : 0 ≤ σ2) (hB : ∀ n, A.predVar n ≤ᵐ[P] fun _ ↦ B)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2))
    (hLindeberg : ∀ ε, 0 < ε → TendstoInMeasure P (fun n ↦ A.lindeberg n ε) atTop 0) :
    Tendsto (fun n ↦ ∫ ω, Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I) ∂P) atTop
      (𝓝 (Complex.exp ((-(t ^ 2 / 2 * σ2) : ℝ) : ℂ))) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  let c : ℂ := Complex.exp ((-(t ^ 2 / 2 * σ2) : ℝ) : ℂ)
  -- bounds and measurability of the `Z`-process at the last step
  have hZbdd : ∀ n, ∀ᵐ ω ∂P, ‖A.Zproc t n (A.k n) ω‖ ≤ Real.exp (t ^ 2 / 2 * B) := fun n ↦ by
    filter_upwards [A.partialVar_le_of_predVar_le (hB n) (le_refl (A.k n))] with ω hω
    exact A.norm_Zproc_le_of_le hω
  have hZ_sm : ∀ n, StronglyMeasurable (A.Zproc t n (A.k n)) := fun n ↦
    (A.stronglyMeasurable_Zproc t n (A.k n)).mono ((A.𝓕 n).le (A.k n))
  have hZint : ∀ n, Integrable (A.Zproc t n (A.k n)) P := fun n ↦
    A.integrable_Zproc_of_le t n (A.k n) (A.partialVar_le_of_predVar_le (hB n) (le_refl (A.k n)))
  -- the exponential weight `e^{-(t²/2)V_n}` and its bound/measurability
  have hWexp_bdd : ∀ n, ∀ᵐ ω ∂P,
      ‖Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ)‖ ≤ 1 := fun n ↦ by
    filter_upwards [A.predVar_nonneg n] with ω hω
    simp only [Pi.zero_apply] at hω
    rw [Complex.norm_exp, Complex.ofReal_re, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  have hWexp_sm : ∀ n, StronglyMeasurable
      (fun ω ↦ Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ)) := fun n ↦
    Complex.continuous_exp.comp_stronglyMeasurable
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        (((A.stronglyMeasurable_predVar n).const_mul (t ^ 2 / 2)).neg))
  -- `Z · (e^{-(t²/2)V_n} - c) → 0` in expectation, via bounded convergence
  have hW : TendstoInMeasure P (fun n ω ↦ Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ)
      - c) atTop 0 := A.tendstoInMeasure_expNeg_predVar_sub ht0 hσ2 A.predVar_nonneg hV
  have hZW0 : Tendsto (fun n ↦ ∫ ω, A.Zproc t n (A.k n) ω *
      (Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ) - c) ∂P) atTop (𝓝 0) := by
    refine tendsto_integral_of_tendstoInMeasure_zero
      (C := Real.exp (t ^ 2 / 2 * B) * (1 + ‖c‖))
      (fun n ↦ (hZ_sm n).mul ((hWexp_sm n).sub stronglyMeasurable_const)) (fun n ↦ ?_)
      (tendstoInMeasure_bdd_mul hZbdd hW)
    filter_upwards [hZbdd n, hWexp_bdd n] with ω hZ hWe
    rw [norm_mul]
    refine mul_le_mul hZ (le_trans (norm_sub_le _ _) (add_le_add hWe le_rfl)) (norm_nonneg _)
      (Real.exp_pos _).le
  -- assemble: `E[e^{itS_n}] = ∫ Z(e^{-..}-c) + c·∫Z → 0 + c·1 = c`
  have hfinal : Tendsto (fun n ↦ (∫ ω, A.Zproc t n (A.k n) ω *
        (Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ) - c) ∂P)
      + c * ∫ ω, A.Zproc t n (A.k n) ω ∂P) atTop (𝓝 (0 + c * 1)) :=
    hZW0.add ((A.clt_Z_expectation t hB0 hB hLindeberg).const_mul c)
  rw [zero_add, mul_one] at hfinal
  refine (tendsto_congr fun n ↦ ?_).mpr hfinal
  have hpt : (fun ω ↦ Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I))
      = fun ω ↦ A.Zproc t n (A.k n) ω *
          (Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ) - c)
        + c * A.Zproc t n (A.k n) ω := by
    funext ω; rw [A.expI_rowSum_eq t n ω]; ring
  have hZWc_int : Integrable (fun ω ↦ A.Zproc t n (A.k n) ω *
      (Complex.exp ((-(t ^ 2 / 2 * A.predVar n ω) : ℝ) : ℂ) - c)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (t ^ 2 / 2 * B) * (1 + ‖c‖)))
      (((hZ_sm n).mul ((hWexp_sm n).sub stronglyMeasurable_const)).aestronglyMeasurable) ?_
    filter_upwards [hZbdd n, hWexp_bdd n] with ω hZ hWe
    rw [norm_mul]
    exact mul_le_mul hZ (le_trans (norm_sub_le _ _) (add_le_add hWe le_rfl)) (norm_nonneg _)
      (Real.exp_pos _).le
  rw [hpt, integral_add hZWc_int ((hZint n).const_mul c), MeasureTheory.integral_const_mul]

open Filter ProbabilityTheory MeasureTheory in
/-- **Martingale CLT, Lindeberg form — bounded predictable variation** (blueprint `thm:mart_clt`
under the truncation normalization `V_n ≤ B`). If `V_n ≤ B` a.e., `V_n → σ²` in probability and the
conditional Lindeberg condition holds, then the laws of the row sums converge weakly to
`𝒩(0, σ²)`. Combines `clt_charFun_bounded` with Mathlib's Lévy continuity theorem. -/
lemma mart_clt_bounded [IsProbabilityMeasure P] {B σ2 : ℝ} (hB0 : 0 ≤ B) (hσ2 : 0 ≤ σ2)
    (hB : ∀ n, A.predVar n ≤ᵐ[P] fun _ ↦ B)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2))
    (hLindeberg : ∀ ε, 0 < ε → TendstoInMeasure P (fun n ↦ A.lindeberg n ε) atTop 0) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun n ↦ ⟨P.map (A.rowSum n),
        Measure.isProbabilityMeasure_map (A.measurable_rowSum n).aemeasurable⟩) atTop
      (𝓝 ⟨gaussianReal 0 σ2.toNNReal, inferInstance⟩) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
  simp only [ProbabilityMeasure.coe_mk]
  have hrhs : charFun (gaussianReal 0 σ2.toNNReal) t
      = Complex.exp ((-(t ^ 2 / 2 * σ2) : ℝ) : ℂ) := by
    rw [charFun_gaussianReal, Real.coe_toNNReal σ2 hσ2]
    push_cast
    ring_nf
  have hcont : Continuous (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * I)) := by fun_prop
  have hlhs : ∀ n, charFun (P.map (A.rowSum n)) t
      = ∫ ω, Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I) ∂P := by
    intro n
    rw [charFun_apply_real,
      integral_map (A.measurable_rowSum n).aemeasurable hcont.aestronglyMeasurable]
    simp only [← Complex.ofReal_mul]
  simp_rw [hlhs, hrhs]
  exact A.clt_charFun_bounded t hB0 hσ2 hB hV hLindeberg

/-! ### Reduction to bounded predictable variation

The general martingale CLT is reduced to the bounded case (`clt_charFun_bounded`,
`mart_clt_bounded`) by the variance truncation `A.trunc B` with `B = σ² + 1`: on `{V_n ≤ B}` the
truncated array agrees with the original, and `P(V_n > B) → 0`. -/

/-- On `{V_n ≤ B}`, the truncated predictable variation agrees with the original (every truncation
indicator equals `1`, since `V` is nondecreasing). -/
lemma predVar_trunc_ae_eq_of_le [IsFiniteMeasure P] (B : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂P, A.predVar n ω ≤ B → (A.trunc B).predVar n ω = A.predVar n ω := by
  have hmono : ∀ i, ∀ᵐ ω ∂P, i < A.k n → A.partialVar n (i + 1) ω ≤ A.predVar n ω := by
    intro i
    by_cases hi : i < A.k n
    · filter_upwards [A.partialVar_mono n (Nat.succ_le_of_lt hi)] with ω hω _
      rw [A.predVar_eq_partialVar]; exact hω
    · exact ae_of_all _ fun ω h ↦ absurd h hi
  filter_upwards [ae_all_iff.mpr fun i ↦ A.condVar_trunc B n i, ae_all_iff.mpr hmono]
    with ω hcv hmo hVle
  change ∑ i ∈ Finset.range (A.k n), (A.trunc B).condVar n i ω
    = ∑ i ∈ Finset.range (A.k n), A.condVar n i ω
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [hcv i]
  exact Set.indicator_of_mem (show ω ∈ {ω | A.partialVar n (i + 1) ω ≤ B} from
    le_trans (hmo i (Finset.mem_range.mp hi)) hVle) _

/-- On `{V_n ≤ B}`, the truncated row sum agrees with the original row sum. -/
lemma rowSum_trunc_ae_eq_of_le [IsFiniteMeasure P] (B : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂P, A.predVar n ω ≤ B → (A.trunc B).rowSum n ω = A.rowSum n ω := by
  have hmono : ∀ i, ∀ᵐ ω ∂P, i < A.k n → A.partialVar n (i + 1) ω ≤ A.predVar n ω := by
    intro i
    by_cases hi : i < A.k n
    · filter_upwards [A.partialVar_mono n (Nat.succ_le_of_lt hi)] with ω hω _
      rw [A.predVar_eq_partialVar]; exact hω
    · exact ae_of_all _ fun ω h ↦ absurd h hi
  filter_upwards [ae_all_iff.mpr hmono] with ω hmo hVle
  change ∑ i ∈ Finset.range (A.k n), (A.trunc B).d n i ω
    = ∑ i ∈ Finset.range (A.k n), A.d n i ω
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  exact Set.indicator_of_mem (show ω ∈ {ω | A.partialVar n (i + 1) ω ≤ B} from
    le_trans (hmo i (Finset.mem_range.mp hi)) hVle) _

open Filter in
/-- `P(V_n > B) → 0` when `V_n → σ²` in probability and `σ² < B`. -/
lemma tendsto_measure_predVar_gt {σ2 B : ℝ} (hσB : σ2 < B)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2)) :
    Tendsto (fun n ↦ P {ω | B < A.predVar n ω}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist] at hV
  have hsub : ∀ n, {ω | B < A.predVar n ω} ⊆ {ω | B - σ2 ≤ dist (A.predVar n ω) σ2} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hV (B - σ2) (by linarith))
    (fun _ ↦ zero_le) (fun n ↦ measure_mono (hsub n))

/-- Truncation only shrinks the Lindeberg quantity: `L̄_n(ε) ≤ L_n(ε)` a.e. -/
lemma lindeberg_trunc_le [IsFiniteMeasure P] (B : ℝ) (n : ℕ) (ε : ℝ) :
    (A.trunc B).lindeberg n ε ≤ᵐ[P] A.lindeberg n ε := by
  have hcell : ∀ i,
      (P[{ω | ε < |(A.trunc B).d n i ω|}.indicator (fun ω ↦ ((A.trunc B).d n i ω) ^ 2) | A.𝓕 n i])
        ≤ᵐ[P] (P[{ω | ε < |A.d n i ω|}.indicator (fun ω ↦ (A.d n i ω) ^ 2) | A.𝓕 n i]) := by
    intro i
    refine condExp_mono (m := A.𝓕 n i)
      (((A.trunc B).integrable_sq n i).indicator
        (measurableSet_lt measurable_const ((A.trunc B).measurable_d n i).abs))
      ((A.integrable_sq n i).indicator (measurableSet_lt measurable_const (A.measurable_d n i).abs))
      (ae_of_all _ fun ω ↦ ?_)
    change {ω | ε < |(A.trunc B).d n i ω|}.indicator (fun ω ↦ ((A.trunc B).d n i ω) ^ 2) ω
      ≤ {ω | ε < |A.d n i ω|}.indicator (fun ω ↦ (A.d n i ω) ^ 2) ω
    by_cases hmem : ω ∈ {ω | A.partialVar n (i + 1) ω ≤ B}
    · have hdeq : (A.trunc B).d n i ω = A.d n i ω := Set.indicator_of_mem hmem _
      refine le_of_eq ?_
      simp only [Set.indicator_apply, Set.mem_setOf_eq, hdeq]
    · have hd0 : (A.trunc B).d n i ω = 0 := Set.indicator_of_notMem hmem _
      rw [Set.indicator_apply]
      simp only [Set.mem_setOf_eq, hd0, abs_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, ite_self]
      exact Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω
  filter_upwards [ae_all_iff.mpr hcell] with ω hω
  simp only [MartDiffArray.lindeberg]
  exact Finset.sum_le_sum fun i _ ↦ hω i

open Filter in
/-- The truncated predictable variation still converges in probability to `σ²`. -/
lemma tendstoInMeasure_predVar_trunc [IsFiniteMeasure P] {σ2 B : ℝ} (hσB : σ2 < B)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2)) :
    TendstoInMeasure P (fun n ↦ (A.trunc B).predVar n) atTop (fun _ ↦ σ2) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hVd := (tendstoInMeasure_iff_dist.mp hV) ε hε
  have hgt := A.tendsto_measure_predVar_gt hσB hV
  have hsub : ∀ n, {ω | ε ≤ dist ((A.trunc B).predVar n ω) σ2} ≤ᵐ[P]
      ({ω | ε ≤ dist (A.predVar n ω) σ2} ∪ {ω | B < A.predVar n ω} : Set Ω) := by
    intro n
    filter_upwards [A.predVar_trunc_ae_eq_of_le B n] with ω heq hmem
    by_cases hle : A.predVar n ω ≤ B
    · refine Set.mem_union_left _ ?_
      have h2 : ε ≤ dist ((A.trunc B).predVar n ω) σ2 := hmem
      rw [heq hle] at h2
      exact h2
    · exact Set.mem_union_right _ (not_le.mp hle)
  have hsum : Tendsto (fun n ↦ P {ω | ε ≤ dist (A.predVar n ω) σ2}
      + P {ω | B < A.predVar n ω}) atTop (𝓝 0) := by simpa using hVd.add hgt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    (fun n ↦ (measure_mono_ae (hsub n)).trans (measure_union_le _ _))

open Filter in
/-- The truncated array still satisfies the conditional Lindeberg condition. -/
lemma tendstoInMeasure_lindeberg_trunc [IsFiniteMeasure P] (B : ℝ) (ε : ℝ)
    (hL : TendstoInMeasure P (fun n ↦ A.lindeberg n ε) atTop 0) :
    TendstoInMeasure P (fun n ↦ (A.trunc B).lindeberg n ε) atTop 0 :=
  tendstoInMeasure_zero_of_le (fun n ↦ (A.trunc B).lindeberg_nonneg n ε)
    (fun n ↦ A.lindeberg_trunc_le B n ε) hL

open Filter in
/-- The difference `e^{itS_n} - e^{itS̄_n}` converges to `0` in probability (it vanishes on
`{V_n ≤ B}`, whose complement has vanishing probability). -/
lemma tendstoInMeasure_expI_rowSum_sub [IsProbabilityMeasure P] (t : ℝ) {σ2 B : ℝ} (hσB : σ2 < B)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2)) :
    TendstoInMeasure P (fun n ω ↦ Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)
      - Complex.exp (((t * (A.trunc B).rowSum n ω : ℝ) : ℂ) * I)) atTop 0 := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hgt := A.tendsto_measure_predVar_gt hσB hV
  have hsub : ∀ n, {ω | ε ≤ dist (Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)
        - Complex.exp (((t * (A.trunc B).rowSum n ω : ℝ) : ℂ) * I)) 0}
      ≤ᵐ[P] {ω | B < A.predVar n ω} := by
    intro n
    filter_upwards [A.rowSum_trunc_ae_eq_of_le B n] with ω heq hmem
    by_contra hcon
    have hle : A.predVar n ω ≤ B := not_lt.mp hcon
    have hg0 : Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)
        - Complex.exp (((t * (A.trunc B).rowSum n ω : ℝ) : ℂ) * I) = 0 := by
      rw [heq hle, sub_self]
    have hd : ε ≤ dist (Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)
        - Complex.exp (((t * (A.trunc B).rowSum n ω : ℝ) : ℂ) * I)) 0 := hmem
    rw [hg0, dist_self] at hd
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgt (fun _ ↦ zero_le)
    (fun n ↦ measure_mono_ae (hsub n))

open Filter in
/-- **Characteristic-function limit** (blueprint `lem:clt_product`). Under `V_n → σ²` in probability
and the conditional Lindeberg condition, `E[e^{itS_n}] → e^{-σ²t²/2}`. The predictable variation is
truncated at level `B = σ² + 1` to reduce to the bounded case `clt_charFun_bounded`. -/
lemma clt_charFun [IsProbabilityMeasure P] (t : ℝ) {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2))
    (hLindeberg : ∀ ε, 0 < ε → TendstoInMeasure P (fun n ↦ A.lindeberg n ε) atTop 0) :
    Tendsto (fun n ↦ ∫ ω, Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I) ∂P) atTop
      (𝓝 (Complex.exp ((-(t ^ 2 / 2 * σ2) : ℝ) : ℂ))) := by
  set B := σ2 + 1 with hBdef
  have hσB : σ2 < B := by rw [hBdef]; linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; linarith
  have hbar : Tendsto (fun n ↦ ∫ ω, Complex.exp (((t * (A.trunc B).rowSum n ω : ℝ) : ℂ) * I) ∂P)
      atTop (𝓝 (Complex.exp ((-(t ^ 2 / 2 * σ2) : ℝ) : ℂ))) :=
    (A.trunc B).clt_charFun_bounded t hB0 hσ2 (fun n ↦ A.predVar_trunc_le hB0 n)
      (A.tendstoInMeasure_predVar_trunc hσB hV)
      (fun ε hε ↦ A.tendstoInMeasure_lindeberg_trunc B ε (hLindeberg ε hε))
  have hcomp : Tendsto (fun n ↦ ∫ ω, (Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)
      - Complex.exp (((t * (A.trunc B).rowSum n ω : ℝ) : ℂ) * I)) ∂P) atTop (𝓝 0) := by
    refine tendsto_integral_of_tendstoInMeasure_zero (C := 2)
      (fun n ↦ (A.stronglyMeasurable_expI_rowSum t n).sub
        ((A.trunc B).stronglyMeasurable_expI_rowSum t n))
      (fun n ↦ ae_of_all _ fun ω ↦ le_trans (norm_sub_le _ _) ?_)
      (A.tendstoInMeasure_expI_rowSum_sub t hσB hV)
    rw [A.norm_expI_rowSum t n ω, (A.trunc B).norm_expI_rowSum t n ω]; norm_num
  have hsplit : ∀ n, (∫ ω, Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I) ∂P)
      = (∫ ω, (Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I)
          - Complex.exp (((t * (A.trunc B).rowSum n ω : ℝ) : ℂ) * I)) ∂P)
        + ∫ ω, Complex.exp (((t * (A.trunc B).rowSum n ω : ℝ) : ℂ) * I) ∂P := by
    intro n
    rw [integral_sub (A.integrable_expI_rowSum t n) ((A.trunc B).integrable_expI_rowSum t n)]
    ring
  have hcomb := hcomp.add hbar
  rw [zero_add] at hcomb
  exact (tendsto_congr hsplit).mpr hcomb

open Filter ProbabilityTheory MeasureTheory in
/-- **Martingale CLT, Lindeberg form** (blueprint `thm:mart_clt`). Let `(Δ_{n,i})_{i<k_n}` be a
martingale difference array with predictable quadratic variation `V_n → σ²` in probability and
satisfying the conditional Lindeberg condition. Then the laws of the row sums `S_n = ∑_i Δ_{n,i}`
converge weakly to `𝒩(0, σ²)`. -/
theorem mart_clt [IsProbabilityMeasure P] {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2))
    (hLindeberg : ∀ ε, 0 < ε → TendstoInMeasure P (fun n ↦ A.lindeberg n ε) atTop 0) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun n ↦ ⟨P.map (A.rowSum n),
        Measure.isProbabilityMeasure_map (A.measurable_rowSum n).aemeasurable⟩) atTop
      (𝓝 ⟨gaussianReal 0 σ2.toNNReal, inferInstance⟩) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
  simp only [ProbabilityMeasure.coe_mk]
  have hrhs : charFun (gaussianReal 0 σ2.toNNReal) t
      = Complex.exp ((-(t ^ 2 / 2 * σ2) : ℝ) : ℂ) := by
    rw [charFun_gaussianReal, Real.coe_toNNReal σ2 hσ2]
    push_cast
    ring_nf
  have hcont : Continuous (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * I)) := by fun_prop
  have hlhs : ∀ n, charFun (P.map (A.rowSum n)) t
      = ∫ ω, Complex.exp (((t * A.rowSum n ω : ℝ) : ℂ) * I) ∂P := by
    intro n
    rw [charFun_apply_real, integral_map (A.measurable_rowSum n).aemeasurable
      hcont.aestronglyMeasurable]
    simp only [← Complex.ofReal_mul]
  simp_rw [hlhs, hrhs]
  exact A.clt_charFun t hσ2 hV hLindeberg

/-! ### Single self-normalized martingale

Package the triangular-array CLT for the common case of one martingale-difference sequence `d`
normalized by a deterministic `a_n`: row `n` is `d_0/√a_n, …, d_{n-1}/√a_n`, so the row sum is
`M_n/√a_n` with `M_n = ∑_{i<n} d_i`. This is the base CLT the componentwise corollary applies
(to the per-arm sampled martingale with `a_n = V_k · n`). -/

variable (𝓕 : Filtration ℕ mΩ) (d : ℕ → Ω → ℝ) (a : ℕ → ℝ)
  (hmemLp : ∀ i, MemLp (d i) 2 P) (hmgdiff : ∀ i, P[d i | 𝓕 i] =ᵐ[P] 0)
  (hadapted : ∀ i, StronglyMeasurable[𝓕 (i + 1)] (d i))

/-- The triangular array from a single martingale-difference sequence `d` scaled by the
deterministic normalizer `1/√(a n)` in row `n`. Its row sum is `M_n/√(a n)`, `M_n = ∑_{i<n} d_i`. -/
noncomputable def ofSeq : MartDiffArray P where
  𝓕 := fun _ ↦ 𝓕
  d n i := fun ω ↦ (Real.sqrt (a n))⁻¹ * d i ω
  k := id
  memLp n i := (hmemLp i).const_mul _
  mgdiff n i := by
    show P[fun ω ↦ (Real.sqrt (a n))⁻¹ * d i ω | 𝓕 i] =ᵐ[P] 0
    filter_upwards [condExp_const_mul (m := 𝓕 i) (Real.sqrt (a n))⁻¹ (d i), hmgdiff i]
      with ω h1 h2
    simp only [Pi.zero_apply] at h2 ⊢
    rw [h1, h2, mul_zero]
  adapted n i := (hadapted i).const_mul _

/-- The row sum of `ofSeq` is `M_n/√(a n)` with `M_n = ∑_{i<n} d_i`. -/
lemma rowSum_ofSeq (n : ℕ) :
    (ofSeq 𝓕 d a hmemLp hmgdiff hadapted).rowSum n
      = fun ω ↦ (Real.sqrt (a n))⁻¹ * ∑ i ∈ Finset.range n, d i ω := by
  funext ω
  change ∑ i ∈ Finset.range n, (Real.sqrt (a n))⁻¹ * d i ω
    = (Real.sqrt (a n))⁻¹ * ∑ i ∈ Finset.range n, d i ω
  rw [← Finset.mul_sum]

/-- The predictable variation of `ofSeq` is `⟨M⟩_n / a_n = (1/a_n) ∑_{i<n} E[d_i²|𝓕 i]`. -/
lemma predVar_ofSeq (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    (ofSeq 𝓕 d a hmemLp hmgdiff hadapted).predVar n
      =ᵐ[P] fun ω ↦ (a n)⁻¹ * ∑ i ∈ Finset.range n, (P[fun ω ↦ (d i ω) ^ 2 | 𝓕 i]) ω := by
  have hcv : ∀ i, (ofSeq 𝓕 d a hmemLp hmgdiff hadapted).condVar n i
      = P[fun ω ↦ (a n)⁻¹ * (d i ω) ^ 2 | 𝓕 i] := by
    intro i
    change P[fun ω ↦ ((Real.sqrt (a n))⁻¹ * d i ω) ^ 2 | 𝓕 i]
      = P[fun ω ↦ (a n)⁻¹ * (d i ω) ^ 2 | 𝓕 i]
    congr 1
    funext ω
    rw [mul_pow, inv_pow, Real.sq_sqrt (ha n)]
  filter_upwards [ae_all_iff.mpr fun i ↦
    condExp_const_mul (m := 𝓕 i) (a n)⁻¹ (fun ω ↦ (d i ω) ^ 2)] with ω hcm
  change ∑ i ∈ Finset.range n, (ofSeq 𝓕 d a hmemLp hmgdiff hadapted).condVar n i ω
    = (a n)⁻¹ * ∑ i ∈ Finset.range n, (P[fun ω ↦ (d i ω) ^ 2 | 𝓕 i]) ω
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hcv i, hcm i]

end MartDiffArray

section SelfNormalization

open Filter ProbabilityTheory MeasureTheory

variable {P : Measure Ω}

/-- **Slutsky self-normalization for the CLT.** If the laws of `X n` converge weakly to `𝒩(0,σ²)`
and `Y n → 1` in probability, then so do the laws of `X n · Y n`. This is what replaces the
(unnecessary) Anscombe random-time-change argument in the self-normalized martingale CLT:
`M_n/√(random) = (M_n/√(deterministic)) · √(deterministic/random)`, and the second factor tends to
`1` in probability by the strong law, so the deterministic-normalizer CLT (`thm:mart_clt`) plus
this Slutsky step give the self-normalized limit. -/
lemma tendsto_map_mul_of_tendstoInMeasure_one [IsProbabilityMeasure P] {σ2 : NNReal}
    {X Y : ℕ → Ω → ℝ} (hX_meas : ∀ n, AEMeasurable (X n) P) (hY_meas : ∀ n, AEMeasurable (Y n) P)
    (hX : Tendsto (β := ProbabilityMeasure ℝ)
        (fun n ↦ ⟨P.map (X n), Measure.isProbabilityMeasure_map (hX_meas n)⟩) atTop
        (𝓝 ⟨gaussianReal 0 σ2, inferInstance⟩))
    (hY : TendstoInMeasure P Y atTop (fun _ ↦ (1 : ℝ))) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ ⟨P.map (fun ω ↦ X n ω * Y n ω),
        Measure.isProbabilityMeasure_map ((hX_meas n).mul (hY_meas n))⟩) atTop
      (𝓝 ⟨gaussianReal 0 σ2, inferInstance⟩) := by
  have hid : TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ ↦ P) (gaussianReal 0 σ2) := by
    refine ⟨hX_meas, aemeasurable_id, ?_⟩
    simp only [Measure.map_id]
    exact hX
  have hslut := hid.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun x : ℝ × ℝ ↦ x.1 * x.2) (by fun_prop) hY hY_meas
  have h2 := hslut.tendsto
  simp only [id_eq, mul_one, Measure.map_id'] at h2
  exact h2

/-- **Multivariate Slutsky.** If the laws of `Xn : ℕ → Ω → E` converge weakly to a probability
measure `μ'` on `E`, `Rn : ℕ → Ω → E'` converges in probability to a constant `c`, and
`g : E × E' → F` is continuous, then the laws of `fun ω ↦ g (Xn ω, Rn ω)` converge weakly to
`μ'.map (fun x ↦ g (x, c))`. This is the vector generalisation of
`tendsto_map_mul_of_tendstoInMeasure_one`, used to pass from a deterministic-normalizer joint CLT
to the self-normalized one. -/
lemma tendsto_map_comp_of_tendstoInMeasure_const [IsProbabilityMeasure P]
    {E E' F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [SeminormedAddCommGroup E'] [MeasurableSpace E'] [BorelSpace E'] [SecondCountableTopology E']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {μ' : Measure E} [IsProbabilityMeasure μ']
    {Xn : ℕ → Ω → E} {Rn : ℕ → Ω → E'} {c : E'}
    (g : E × E' → F) (hg : Continuous g)
    (hX_meas : ∀ n, AEMeasurable (Xn n) P) (hR_meas : ∀ n, AEMeasurable (Rn n) P)
    (hX : Tendsto (β := ProbabilityMeasure E)
        (fun n ↦ ⟨P.map (Xn n), Measure.isProbabilityMeasure_map (hX_meas n)⟩) atTop
        (𝓝 ⟨μ', inferInstance⟩))
    (hR : TendstoInMeasure P Rn atTop (fun _ ↦ c)) :
    Tendsto (β := ProbabilityMeasure F)
      (fun n ↦ ⟨P.map (fun ω ↦ g (Xn n ω, Rn n ω)),
        Measure.isProbabilityMeasure_map
          (hg.measurable.comp_aemeasurable ((hX_meas n).prodMk (hR_meas n)))⟩) atTop
      (𝓝 ⟨μ'.map (fun x ↦ g (x, c)),
        Measure.isProbabilityMeasure_map
          (hg.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable⟩) := by
  have hid : TendstoInDistribution Xn atTop (id : E → E) (fun _ ↦ P) μ' := by
    refine ⟨hX_meas, aemeasurable_id, ?_⟩
    simp only [Measure.map_id]
    exact hX
  have hslut := hid.continuous_comp_prodMk_of_tendstoInMeasure_const (g := g) hg hR hR_meas
  have h2 := hslut.tendsto
  simp only [id_eq] at h2
  exact h2

end SelfNormalization

end Array

end AlphaRAR
