/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Probability.PluginTargetCLT
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The joint central limit theorem for proportions and plug-in targets

Assembling the marginal plug-in-target CLT `√n(ρ̂_n - v) ⇒ 𝒩(0, GVGᵀ)` (`clt_rho`) with the
proportion-deviation fact `√n(N_n/n - ρ̂_n) →ₚ 0` (blueprint `lem:prop_dev`, taken here as a
hypothesis) into the joint statement (blueprint `thm:normality` part (ii))
`(√n(N_n/n - v), √n(ρ̂_n - v)) ⇒ 𝒩(0, Ω)`, where `Ω` is the `2×2` block matrix with every block
equal to `GVGᵀ`.

The two components are asymptotically equal (both `√n(ρ̂_n - v) + o_p(1)`), so the joint vector is
the image of `√n(ρ̂_n - v)` under the *duplication* map `x ↦ (x, x)` up to an `o_p(1)` remainder.
The duplication map is the stacked matrix `[I; I]`, so its Gaussian pushforward
(`multivariateGaussian_map_matrix`) has covariance `[I;I] (GVGᵀ) [I;I]ᵀ = Ω`. The assembly is the
product-space Slutsky lemma, exactly as for `clt_rho`.

## Main results

* `AlphaRAR.clt_joint`.
-/

open MeasureTheory Filter ProbabilityTheory Learning

open scoped Topology RealInnerProductSpace Matrix ENNReal

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [Fintype 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- The `√n`-scaled proportion-deviation vector `√n(N_{n,k}/n - v_k) ∈ ℝ^𝓐`. -/
noncomputable def propSqrtNVec (A : ℕ → Ω → 𝓐) (v : 𝓐 → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 (fun k ↦ Real.sqrt n * (count (fun j ↦ armIndicator A k j ω) n / (n : ℝ) - v k))

/-- The `√n`-scaled joint vector `(√n(N_n/n - v), √n(ρ̂_n - v)) ∈ ℝ^(𝓐 ⊕ 𝓐)`. -/
noncomputable def jointSqrtNVec (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (T : (𝓐 → ℝ) → 𝓐 → ℝ) (v : 𝓐 → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (𝓐 ⊕ 𝓐) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp (propSqrtNVec A v n ω))
    (WithLp.ofLp (targetSqrtNVec ν A Y θ₀ T n ω)))

omit [DecidableEq 𝓐] [Fintype 𝓐] in
lemma measurable_propSqrtNVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (v : 𝓐 → ℝ) (n : ℕ) :
    Measurable (propSqrtNVec A v n) := by
  refine (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦ ?_)
  exact (((measurable_count_armIndicator h k n).div_const _).sub_const _).const_mul _

omit [DecidableEq 𝓐] [Fintype 𝓐] in
lemma measurable_jointSqrtNVec [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (v : 𝓐 → ℝ) (n : ℕ) :
    Measurable (jointSqrtNVec ν A Y θ₀ T v n) := by
  cases nonempty_fintype 𝓐
  refine (WithLp.measurable_toLp 2 ((𝓐 ⊕ 𝓐) → ℝ)).comp (measurable_pi_lambda _ fun p ↦ ?_)
  cases p with
  | inl a =>
    simp only [Sum.elim_inl]
    exact (measurable_pi_apply a).comp
      ((WithLp.measurable_ofLp 2 (𝓐 → ℝ)).comp (measurable_propSqrtNVec h v n))
  | inr a =>
    simp only [Sum.elim_inr]
    exact (measurable_pi_apply a).comp
      ((WithLp.measurable_ofLp 2 (𝓐 → ℝ)).comp (measurable_targetSqrtNVec h θ₀ hT n))

omit [DecidableEq 𝓐] in
/-- The embedding `r ↦ toLp (Sum.elim (ofLp r) 0)` of `ℝ^𝓐` into `ℝ^(𝓐 ⊕ 𝓐)` (the first copy)
preserves the norm: `‖toLp (Sum.elim (ofLp r) 0)‖ = ‖r‖`. Used to reduce the joint remainder `→ₚ 0`
to the proportion-deviation hypothesis. -/
lemma norm_toLp_sumElim_zero (r : EuclideanSpace ℝ 𝓐) :
    ‖(WithLp.toLp 2 (Sum.elim (WithLp.ofLp r) 0) : EuclideanSpace ℝ (𝓐 ⊕ 𝓐))‖ = ‖r‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  congr 1
  simp [Sum.elim_inl, Sum.elim_inr]

/-- **Joint CLT for proportions and plug-in targets** (blueprint `thm:normality` part (ii)).
Given the plug-in-target CLT hypotheses (differentiability `hTderiv` from Condition **B**, a.s.
consistency `hcons` from Theorem `thm:LLN`) and the proportion-deviation fact
`√n(N_n/n - ρ̂_n) →ₚ 0` (`hprop`, blueprint `lem:prop_dev`), the joint vector
`(√n(N_n/n - v), √n(ρ̂_n - v))` converges weakly to `𝒩(0, Ω)`, where `Ω` is the block matrix with
every block equal to `G · diag(V_k/v_k) · Gᵀ`.

The proof is the product-space Slutsky assembly (as in `clt_rho`): the base sequence
`√n(ρ̂_n - v)` converges to `𝒩(0, GVGᵀ)` (`clt_rho`), it is pushed forward under the duplication
map `x ↦ (x, x)` (the stacked matrix `[I; I]`), and the remainder `(√n(N_n/n - ρ̂_n), 0)` vanishes
in probability by `hprop`. The limit law is the linear pushforward
`multivariateGaussian_map_matrix`, whose covariance `[I;I] (GVGᵀ) [I;I]ᵀ` equals the block matrix
`Ω` (`fromCols_fromRows_eq_fromBlocks`). -/
theorem clt_joint
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a)))
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (G : Matrix 𝓐 𝓐 ℝ)
    (hTderiv : HasFDerivAt
      (fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (T (WithLp.ofLp x)) : EuclideanSpace ℝ 𝓐))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) G) (WithLp.toLp 2 (fun k ↦ (ν k)[id])))
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ armIndicator A k' j ω)
      (fun j ↦ Y j ω) (θ₀ k') n) atTop (𝓝 (fun k ↦ (ν k)[id])))
    (hprop : TendstoInMeasure P
      (fun n ω ↦ propSqrtNVec A v n ω - targetSqrtNVec ν A Y θ₀ T n ω) atTop (fun _ ↦ 0)) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐)))
      (fun n : ℕ ↦ (⟨P.map (jointSqrtNVec ν A Y θ₀ T v n),
        Measure.isProbabilityMeasure_map (measurable_jointSqrtNVec h θ₀ hT v n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐))))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.fromBlocks
        (G * Matrix.diagonal (fun a ↦ armVar ν a / v a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ armVar ν a / v a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ armVar ν a / v a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ armVar ν a / v a) * Gᵀ)), inferInstance⟩) := by
  have hVnn : ∀ a, 0 ≤ armVar ν a := fun a ↦ by rw [armVar]; exact variance_nonneg _ _
  set M : Matrix 𝓐 𝓐 ℝ := G * Matrix.diagonal (fun a ↦ armVar ν a / v a) * Gᵀ with hMdef
  set μ' : Measure (EuclideanSpace ℝ 𝓐) := multivariateGaussian 0 M with hμ'
  have hMpsd : M.PosSemidef := by
    have hh := (Matrix.posSemidef_diagonal_iff.mpr fun a ↦
      div_nonneg (hVnn a) (hv a).le).mul_mul_conjTranspose_same G
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  -- The duplication map `d = x ↦ (x, x)` as the pushforward of `[I; I]`.
  set D : Matrix (𝓐 ⊕ 𝓐) 𝓐 ℝ := Matrix.fromRows 1 1 with hDdef
  set d : EuclideanSpace ℝ 𝓐 → EuclideanSpace ℝ (𝓐 ⊕ 𝓐) :=
    fun x ↦ WithLp.toLp 2 (D.mulVec (WithLp.ofLp x)) with hd
  have hd_cont : Continuous d := by
    rw [hd]
    exact (PiLp.continuous_toLp 2 (fun _ : 𝓐 ⊕ 𝓐 ↦ ℝ)).comp
      (((Matrix.mulVecLin D).continuous_of_finiteDimensional).comp
        (PiLp.continuous_ofLp 2 (fun _ : 𝓐 ↦ ℝ)))
  set g : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ (𝓐 ⊕ 𝓐) → EuclideanSpace ℝ (𝓐 ⊕ 𝓐) :=
    fun p ↦ d p.1 + p.2 with hg_def
  have hg : Continuous g := (hd_cont.comp continuous_fst).add continuous_snd
  -- Base weak convergence: `√n(ρ̂_n - v) ⇒ 𝒩(0, M)` (this is `clt_rho`).
  have hclt := clt_rho h hY2 θ₀ hνk hv hNconv hT G hTderiv hcons
  have hXmeas : ∀ n, Measurable (targetSqrtNVec ν A Y θ₀ T n) := measurable_targetSqrtNVec h θ₀ hT
  -- The remainder `Rn = jointSqrtNVec - d(√n(ρ̂_n - v)) = (√n(N_n/n - ρ̂_n), 0)`.
  set Rn : ℕ → Ω → EuclideanSpace ℝ (𝓐 ⊕ 𝓐) :=
    fun n ω ↦ jointSqrtNVec ν A Y θ₀ T v n ω - d (targetSqrtNVec ν A Y θ₀ T n ω) with hRn
  have hembed : ∀ n ω, Rn n ω = WithLp.toLp 2
      (Sum.elim (WithLp.ofLp (propSqrtNVec A v n ω - targetSqrtNVec ν A Y θ₀ T n ω)) 0) := by
    intro n ω
    simp only [hRn, jointSqrtNVec, hd, hDdef, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← WithLp.toLp_sub]
    congr 1
    ext (a | a) <;> simp [WithLp.ofLp_sub]
  have hRmeas : ∀ n, AEMeasurable (Rn n) P := fun n ↦ by
    rw [hRn]
    exact ((measurable_jointSqrtNVec h θ₀ hT v n).sub
      (hd_cont.measurable.comp (hXmeas n))).aemeasurable
  have hR : TendstoInMeasure P Rn atTop (fun _ ↦ 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine ((tendstoInMeasure_iff_dist.mp hprop) ε hε).congr fun n ↦ ?_
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, dist_zero_right, hembed n ω, norm_toLp_sumElim_zero]
  have hslut := tendsto_map_comp_of_tendstoInMeasure_const (P := P) (μ' := μ') g hg
    (fun n ↦ (hXmeas n).aemeasurable) hRmeas hclt hR
  -- The limit law: `μ'.map (d) = 𝒩(0, D M Dᵀ) = 𝒩(0, Ω)`.
  have hlim : μ'.map (fun x ↦ g (x, 0))
      = multivariateGaussian 0 (Matrix.fromBlocks M M M M) := by
    have hgc : (fun x : EuclideanSpace ℝ 𝓐 ↦ g (x, 0)) = d := by funext x; simp [hg_def]
    rw [hgc, hd, hμ', multivariateGaussian_map_matrix M D hMpsd]
    congr 1
    rw [hDdef, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.fromRows_mul,
      Matrix.mul_fromCols]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.fromCols_fromRows_eq_fromBlocks]
  have heq : (⟨multivariateGaussian 0 (Matrix.fromBlocks M M M M), inferInstance⟩
        : ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐)))
      = ⟨μ'.map (fun x ↦ g (x, 0)), Measure.isProbabilityMeasure_map
          (hg.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable⟩ := by
    apply Subtype.ext
    change multivariateGaussian 0 _ = μ'.map _
    rw [hlim]
  rw [heq]
  refine Tendsto.congr (fun n ↦ Subtype.ext (congrArg (P.map ·) ?_)) hslut
  funext ω
  simp only [hg_def, hRn]
  abel

end AlphaRAR
