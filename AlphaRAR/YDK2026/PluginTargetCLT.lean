/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.TendstoInMeasure
import AlphaRAR.YDK2026.ResponseCLTJoint
import LeanSpec

/-!
# The delta-method central limit theorem for the plug-in target

The estimator satisfies the joint CLT `√n(θ̂_n - θ) ⇒ 𝒩(0, V)` with `V = diag(V_k/v_k)`
(`estimator_sqrtN_joint_tendsto_multivariateGaussian`, blueprint `lem:clt_theta`). Applying the
*delta method* to the (Condition **B**) target map `T`, differentiable at `θ` with Jacobian `G`, the
plug-in target `ρ̂_n = T(θ̂_n)` inherits the CLT `√n(ρ̂_n - v) ⇒ 𝒩(0, G V Gᵀ)` (blueprint
`lem:clt_rho`).

This file assembles the delta method from three inputs: the estimator CLT, the linear pushforward of
a multivariate Gaussian (`multivariateGaussian_map_matrix`, giving the covariance `G V Gᵀ`) and the
product-space Slutsky lemma (`tendsto_map_comp_of_tendstoInMeasure_const`). The remaining analytic
content — that the first-order Taylor remainder `√n(T(θ̂_n)-T(θ)) - G·√n(θ̂_n-θ)` vanishes in
probability — enters as the hypothesis `hR`, isolating it for a separate argument (tightness of
`√n(θ̂_n-θ)` from the CLT, plus differentiability of `T` at `θ`).

## Main results

* `AlphaRAR.clt_rho_of_tendstoInMeasure`: the delta-method CLT for the plug-in target, conditional
  on the Taylor-remainder-in-probability hypothesis.
-/

open MeasureTheory Filter ProbabilityTheory Learning

open scoped Topology RealInnerProductSpace Matrix ENNReal

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [Fintype 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- The `√n`-scaled plug-in-target error vector `√n(T(θ̂_n) - T(θ)) ∈ ℝ^𝓐`. -/
noncomputable def targetSqrtNVec (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (T : (𝓐 → ℝ) → 𝓐 → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 (fun k ↦ √n *
    (T (fun k' ↦ estimator (fun j ↦ armIndicator A k' j ω) (fun j ↦ Y j ω) (θ₀ k') n) k
      - T (fun k' ↦ (ν k')[id]) k))

/-- The `√n`-scaled estimator error vector `√n(θ̂_n - θ) ∈ ℝ^𝓐` (the vector of `clt_theta`). -/
noncomputable def estimatorSqrtNVec (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 (fun k ↦ √n *
    (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))

omit [DecidableEq 𝓐] [Fintype 𝓐] in
lemma measurable_estimatorSqrtNVec' (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ)
    (n : ℕ) : Measurable (estimatorSqrtNVec ν A Y θ₀ n) := by
  refine (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦ ?_)
  refine Measurable.const_mul ?_ (√n)
  have harm : ∀ j, Measurable (fun ω ↦ armIndicator A k j ω) := fun j ↦
    (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
      (h.measurable_action j))
  simp only [estimator]
  refine (Measurable.div ?_ ((measurable_count_armIndicator h k n).add_const 1)).sub_const _
  exact (Finset.measurable_sum _ fun j _ ↦ (harm j).mul (h.measurable_feedback j)).add_const (θ₀ k)

/-- **The estimator CLT in this file's vector notation** (blueprint `lem:clt_theta`):
`√n(θ̂_n - θ) ⇒ 𝒩(0, diag(V_k/v_k))`. This is
`estimator_sqrtN_joint_tendsto_multivariateGaussian` read through `estimatorSqrtNVec`, which it
matches definitionally. -/
@[specifies estimatorSqrtNVec "the `√n` scaling and the centring at the true means \
`θ_k = (ν k)[id]` are exactly what makes this vector converge to a nondegenerate Gaussian, with \
the arm-`k` variance inflated by `1/v_k` because arm `k` is only pulled a fraction `v_k` of the \
time"]
theorem estimatorSqrtNVec_joint_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (estimatorSqrtNVec ν A Y θ₀ n),
        Measure.isProbabilityMeasure_map (measurable_estimatorSqrtNVec' h θ₀ n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a] / v a), inferInstance⟩) :=
  estimator_sqrtN_joint_tendsto_multivariateGaussian h hY2 θ₀ hνk hv hNconv

omit [DecidableEq 𝓐] [Fintype 𝓐] in
/-- Measurability of the estimator vector `ω ↦ (θ̂_{n,k}(ω))_k : 𝓐 → ℝ`. -/
lemma measurable_estimatorVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ) (n : ℕ) :
    Measurable (fun ω ↦ (fun k ↦ estimator (fun j ↦ armIndicator A k j ω)
      (fun j ↦ Y j ω) (θ₀ k) n : 𝓐 → ℝ)) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  have harm : ∀ j, Measurable (fun ω ↦ armIndicator A k j ω) := fun j ↦
    (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
      (h.measurable_action j))
  simp only [estimator]
  exact ((Finset.measurable_sum _ fun j _ ↦ (harm j).mul (h.measurable_feedback j)).add_const
    (θ₀ k)).div ((measurable_count_armIndicator h k n).add_const 1)

omit [DecidableEq 𝓐] [Fintype 𝓐] in
lemma measurable_targetSqrtNVec [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (n : ℕ) :
    Measurable (targetSqrtNVec ν A Y θ₀ T n) := by
  cases nonempty_fintype 𝓐
  refine (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦ ?_)
  refine Measurable.const_mul ?_ (√n)
  exact ((measurable_pi_apply k).comp
    (hT.measurable.comp (measurable_estimatorVec h θ₀ n))).sub_const _

open scoped RealInnerProductSpace in
/-- **Delta-method CLT for the plug-in target** (blueprint `lem:clt_rho`), conditional on the
Taylor-remainder-in-probability hypothesis. Given the estimator CLT
`√n(θ̂_n - θ) ⇒ 𝒩(0, diag(V_k/v_k))` and a matrix `G` (the Jacobian of `T` at `θ`) such that the
first-order remainder `√n(T(θ̂_n)-T(θ)) - G·√n(θ̂_n-θ)` tends to `0` in probability (`hR`), the
plug-in target satisfies `√n(T(θ̂_n) - T(θ)) ⇒ 𝒩(0, G · diag(V_k/v_k) · Gᵀ)`. The limiting law is
the linear pushforward of the estimator's Gaussian (`multivariateGaussian_map_matrix`), obtained via
the product-space Slutsky lemma with `g(x, r) = G·x + r`. -/
theorem clt_rho_of_tendstoInMeasure
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a)))
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (G : Matrix 𝓐 𝓐 ℝ)
    (hR : TendstoInMeasure P (fun n ω ↦ targetSqrtNVec ν A Y θ₀ T n ω
      - WithLp.toLp 2 (G.mulVec (WithLp.ofLp (estimatorSqrtNVec ν A Y θ₀ n ω))))
      atTop (fun _ ↦ 0)) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (targetSqrtNVec ν A Y θ₀ T n),
        Measure.isProbabilityMeasure_map (measurable_targetSqrtNVec h θ₀ hT n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / v a) * Gᵀ), inferInstance⟩) := by
  have hVnn : ∀ a, 0 ≤ Var[id; ν a] := fun a ↦ variance_nonneg _ _
  set μ' : Measure (EuclideanSpace ℝ 𝓐) :=
    multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a] / v a) with hμ'
  set g : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 → EuclideanSpace ℝ 𝓐 :=
    fun p ↦ WithLp.toLp 2 (G.mulVec (WithLp.ofLp p.1)) + p.2 with hg_def
  have hg : Continuous g := by
    rw [hg_def]
    refine Continuous.add ?_ continuous_snd
    exact (PiLp.continuous_toLp 2 (fun _ : 𝓐 ↦ ℝ)).comp
      (((Matrix.mulVecLin G).continuous_of_finiteDimensional).comp
        ((PiLp.continuous_ofLp 2 (fun _ : 𝓐 ↦ ℝ)).comp continuous_fst))
  -- measurability of the remainder
  have hXmeas : ∀ n, Measurable (estimatorSqrtNVec ν A Y θ₀ n) :=
    fun n ↦ measurable_estimatorSqrtNVec' h θ₀ n
  have hGXmeas : ∀ n, Measurable (fun ω ↦
      (WithLp.toLp 2 (G.mulVec (WithLp.ofLp (estimatorSqrtNVec ν A Y θ₀ n ω)))
        : EuclideanSpace ℝ 𝓐)) := fun n ↦
    (PiLp.continuous_toLp 2 (fun _ : 𝓐 ↦ ℝ)).measurable.comp
      (((Matrix.mulVecLin G).continuous_of_finiteDimensional).measurable.comp
        ((PiLp.continuous_ofLp 2 (fun _ : 𝓐 ↦ ℝ)).measurable.comp (hXmeas n)))
  have hRmeas : ∀ n, AEMeasurable (fun ω ↦ targetSqrtNVec ν A Y θ₀ T n ω
      - WithLp.toLp 2 (G.mulVec (WithLp.ofLp (estimatorSqrtNVec ν A Y θ₀ n ω)))) P := fun n ↦
    (((measurable_targetSqrtNVec h θ₀ hT n).sub (hGXmeas n))).aemeasurable
  have hclt := estimator_sqrtN_joint_tendsto_multivariateGaussian h hY2 θ₀ hνk hv hNconv
  have hslut := tendsto_map_comp_of_tendstoInMeasure_const (P := P) (μ' := μ') g hg
    (fun n ↦ (hXmeas n).aemeasurable) hRmeas hclt hR
  -- the limiting law: `μ'.map (g(·, 0)) = 𝒩(0, G diag Gᵀ)`
  have hlim : μ'.map (fun x ↦ g (x, 0))
      = multivariateGaussian 0 (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / v a) * Gᵀ) := by
    have hgc : (fun x : EuclideanSpace ℝ 𝓐 ↦ g (x, 0))
        = fun x : EuclideanSpace ℝ 𝓐 ↦
          (WithLp.toLp 2 (G.mulVec (WithLp.ofLp x)) : EuclideanSpace ℝ 𝓐) := by
      funext x; simp only [hg_def, add_zero]
    rw [hgc, hμ', multivariateGaussian_map_matrix _ G
      (Matrix.posSemidef_diagonal_iff.mpr fun a ↦ div_nonneg (hVnn a) (hv a).le)]
  -- rewrite the target of `hslut`
  have heq : (⟨multivariateGaussian 0 (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / v a) * Gᵀ),
        inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      = ⟨μ'.map (fun x ↦ g (x, 0)), Measure.isProbabilityMeasure_map
          (hg.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable⟩ := by
    apply Subtype.ext
    change multivariateGaussian 0 _ = μ'.map _
    rw [hlim]
  rw [heq]
  -- rewrite `g(Xn, Rn) = targetSqrtNVec`
  refine Tendsto.congr (fun n ↦ Subtype.ext (congrArg (P.map ·) ?_)) hslut
  funext ω
  simp only [hg_def]
  abel

open scoped RealInnerProductSpace in
/-- **Delta-method CLT for the plug-in target** (blueprint `lem:clt_rho`), fully discharged. Given
the estimator CLT `√n(θ̂_n - θ) ⇒ 𝒩(0, diag(V_k/v_k))`, the a.s. consistency `θ̂_n → θ` (`hcons`,
from thm:LLN) and the differentiability of the (vectorised) target map at `θ` with Jacobian matrix
`G` (`hTderiv`, from Condition **B**), the plug-in target satisfies
`√n(T(θ̂_n) - T(θ)) ⇒ 𝒩(0, G · diag(V_k/v_k) · Gᵀ)`.

This removes the Taylor-remainder hypothesis of `clt_rho_of_tendstoInMeasure` by discharging it: the
remainder `√n(T(θ̂_n)-T(θ)) - G·√n(θ̂_n-θ) = √n · φ(θ̂_n-θ)` (with `φ` the first-order remainder of
the differentiable map) tends to `0` in probability by `tendstoInMeasure_smul_littleO_of_tight`,
whose tightness input is supplied from the estimator CLT via `tight_of_tendsto_probabilityMeasure`
and whose `Sₙ → 0` input is the a.s. consistency. -/
@[specifies targetSqrtNVec "certifies the two choices in the definition: the same `√n` scale as \
the estimator error (no extra rate is introduced by `T`) and the centring at `T(θ)` rather than at \
any running quantity, which is what makes the limit the delta-method Gaussian `G Σ Gᵀ`"]
theorem clt_rho
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a)))
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (G : Matrix 𝓐 𝓐 ℝ)
    (hTderiv : HasFDerivAt
      (fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (T (WithLp.ofLp x)) : EuclideanSpace ℝ 𝓐))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) G) (WithLp.toLp 2 (fun k ↦ (ν k)[id])))
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ armIndicator A k' j ω)
      (fun j ↦ Y j ω) (θ₀ k') n) atTop (𝓝 (fun k ↦ (ν k)[id]))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (targetSqrtNVec ν A Y θ₀ T n),
        Measure.isProbabilityMeasure_map (measurable_targetSqrtNVec h θ₀ hT n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / v a) * Gᵀ), inferInstance⟩) := by
  refine clt_rho_of_tendstoInMeasure h hY2 θ₀ hνk hv hNconv hT G ?_
  -- Notation for the un-scaled error vector `S`, base point `p`, derivative `L`, remainder `φ`.
  set p : EuclideanSpace ℝ 𝓐 := WithLp.toLp 2 (fun k ↦ (ν k)[id]) with hpdef
  set L : EuclideanSpace ℝ 𝓐 →L[ℝ] EuclideanSpace ℝ 𝓐 :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) G with hLdef
  set Tv : EuclideanSpace ℝ 𝓐 → EuclideanSpace ℝ 𝓐 :=
    fun x ↦ WithLp.toLp 2 (T (WithLp.ofLp x)) with hTvdef
  set S : ℕ → Ω → EuclideanSpace ℝ 𝓐 := fun n ω ↦ WithLp.toLp 2
    (fun k ↦ estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id])
    with hSdef
  set φ : EuclideanSpace ℝ 𝓐 → EuclideanSpace ℝ 𝓐 := fun hh ↦ Tv (p + hh) - Tv p - L hh with hφdef
  -- The remainder `φ` is `o(‖·‖)` at the origin.
  have hlo : (fun hh ↦ Tv (p + hh) - Tv p - L hh) =o[𝓝 0] fun hh : EuclideanSpace ℝ 𝓐 ↦ hh :=
    hasFDerivAt_iff_isLittleO_nhds_zero.mp hTderiv
  have hφbound : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ hh : EuclideanSpace ℝ 𝓐, ‖hh‖ ≤ δ → ‖φ hh‖ ≤ ε * ‖hh‖ := by
    intro ε hε
    have hev := hlo.def hε
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hb⟩ := hev
    refine ⟨δ / 2, half_pos hδ, fun hh hhle ↦ ?_⟩
    have hlt : dist hh 0 < δ := by
      rw [dist_zero_right]; exact lt_of_le_of_lt hhle (half_lt_self hδ)
    exact hb hlt
  -- `√n(θ̂_n-θ) = √n • S`.
  have hrel : ∀ n ω, estimatorSqrtNVec ν A Y θ₀ n ω = √n • S n ω := by
    intro n ω
    apply WithLp.ofLp_injective (p := 2)
    funext k
    simp only [estimatorSqrtNVec, hSdef, WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply,
      smul_eq_mul]
  -- `S n → 0` in probability, from the a.s. consistency `hcons`.
  have hSmeas : ∀ n, Measurable (S n) := by
    intro n
    simp only [hSdef]
    refine (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦ ?_)
    have harm : ∀ j, Measurable (fun ω ↦ armIndicator A k j ω) := fun j ↦
      (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
        (h.measurable_action j))
    simp only [estimator]
    refine (Measurable.div ?_ ((measurable_count_armIndicator h k n).add_const 1)).sub_const _
    exact (Finset.measurable_sum _ fun j _ ↦ (harm j).mul
      (h.measurable_feedback j)).add_const (θ₀ k)
  have hS : TendstoInMeasure P S atTop (fun _ ↦ (0 : EuclideanSpace ℝ 𝓐)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hSmeas n).aestronglyMeasurable) ?_
    filter_upwards [hcons] with ω hω
    have hSeq : ∀ n, S n ω = WithLp.toLp 2 (fun k ↦ estimator (fun j ↦ armIndicator A k j ω)
        (fun j ↦ Y j ω) (θ₀ k) n) - p := by
      intro n; simp only [hSdef, hpdef, ← WithLp.toLp_sub]; rfl
    have hc := ((PiLp.continuous_toLp 2 (fun _ : 𝓐 ↦ ℝ)).tendsto (fun k ↦ (ν k)[id])).comp hω
    have hc2 := hc.sub (tendsto_const_nhds (x := p))
    rw [← hpdef, sub_self] at hc2
    exact hc2.congr fun n ↦ (hSeq n).symm
  -- Tightness of `√n(θ̂_n-θ)` from the estimator CLT.
  have hX : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n in atTop, P {ω | M ≤ dist (estimatorSqrtNVec ν A Y θ₀ n ω) 0} ≤ η := fun η hη ↦
    tight_of_tendsto_probabilityMeasure (measurable_estimatorSqrtNVec' h θ₀) (fun n ↦ rfl)
      (estimator_sqrtN_joint_tendsto_multivariateGaussian h hY2 θ₀ hνk hv hNconv) η hη
  -- The remainder equals `√n • φ(S)`.
  have hpt : ∀ n ω, targetSqrtNVec ν A Y θ₀ T n ω
      - WithLp.toLp 2 (G.mulVec (WithLp.ofLp (estimatorSqrtNVec ν A Y θ₀ n ω)))
      = √n • φ (S n ω) := by
    intro n ω
    have e1 : Tv (p + S n ω) = WithLp.toLp 2 (T fun k ↦ estimator (fun j ↦ armIndicator A k j ω)
        (fun j ↦ Y j ω) (θ₀ k) n) := by
      have hof : (WithLp.ofLp (p + S n ω) : 𝓐 → ℝ)
          = fun k ↦ estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n := by
        funext k
        simp only [hpdef, hSdef, WithLp.ofLp_add, Pi.add_apply]
        ring
      simp only [hTvdef, hof]
    have e2 : Tv p = WithLp.toLp 2 (T fun k ↦ (ν k)[id]) := by
      simp only [hTvdef, hpdef]
    have e3 : L (S n ω) = WithLp.toLp 2 (G.mulVec (WithLp.ofLp (S n ω))) := by
      simp only [hLdef, hSdef, Matrix.toEuclideanCLM_toLp, WithLp.ofLp_toLp]
    have e4 : WithLp.ofLp (estimatorSqrtNVec ν A Y θ₀ n ω)
        = √n • WithLp.ofLp (S n ω) := by rw [hrel n ω, WithLp.ofLp_smul]
    rw [hφdef]
    change targetSqrtNVec ν A Y θ₀ T n ω
      - WithLp.toLp 2 (G.mulVec (WithLp.ofLp (estimatorSqrtNVec ν A Y θ₀ n ω)))
      = √n • (Tv (p + S n ω) - Tv p - L (S n ω))
    rw [e1, e2, e3, e4, Matrix.mulVec_smul]
    apply WithLp.ofLp_injective (p := 2)
    funext k
    simp only [targetSqrtNVec, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  -- Assemble via the abstract remainder-in-probability lemma.
  have key : TendstoInMeasure P (fun (n : ℕ) ω ↦ √n • φ (S n ω)) atTop
      (fun _ ↦ (0 : EuclideanSpace ℝ 𝓐)) :=
    tendstoInMeasure_smul_littleO_of_tight (a := fun n ↦ √n) (S := S)
      (X := estimatorSqrtNVec ν A Y θ₀) (fun n ↦ Real.sqrt_nonneg _) hφbound hrel hS hX
  have hfun : (fun n ω ↦ targetSqrtNVec ν A Y θ₀ T n ω
        - WithLp.toLp 2 (G.mulVec (WithLp.ofLp (estimatorSqrtNVec ν A Y θ₀ n ω))))
      = fun (n : ℕ) ω ↦ √n • φ (S n ω) := by funext n ω; exact hpt n ω
  rw [hfun]; exact key

end AlphaRAR
