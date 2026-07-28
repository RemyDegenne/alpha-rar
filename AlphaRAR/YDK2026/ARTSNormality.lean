/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.YDK2026.JointCLT
import AlphaRAR.YDK2026.PropDevARTS

/-!
# The joint central limit theorem for the aRTS design

This file assembles the fully self-contained joint central limit theorem for the concrete aRTS
design (blueprint `thm:normality` part (ii)): the `√n`-scaled proportion and plug-in-target
deviations converge jointly to the block-Gaussian `𝒩(0, Ω)`, where every block of `Ω` equals
`G · diag(V_k / v_k) · Gᵀ`.

The generic `AlphaRAR.clt_joint` takes the proportion-deviation fact `√n(N_n/n - ρ̂_n) →ₚ 0` as a
hypothesis; here it is *discharged* from `AlphaRAR.aRTS_prop_dev` (the `o_p(√n)` deviation bound of
`thm:normality` part (i)). The bridge is a generic fact — coordinatewise `o_p(1)` implies vector
convergence in measure — and the exact `√n`-scaling identity relating the coordinate deviation
`(propSqrtNVec - targetSqrtNVec)_k` to the `aRTS_prop_dev` quantity `(N_{n,k} - n ρ̂_{n,k})/√n`.

The only Condition-**B** input beyond the `aRTS_prop_dev` bundle is the first-order
differentiability of the target `T` at `θ` (the Jacobian matrix `G`), exactly as for `clt_rho`;
the `thm:LLN`
consistencies `N/n → v`, `θ̂ → θ` and the non-sparsity `0 < v_k` are all derived from the bundle.

## Main results

* `AlphaRAR.tendstoInMeasure_toLp_of_forall_isLittleOpOne` (generic: coordinatewise `o_p ⟹` vector).
* `AlphaRAR.aRTS_clt_joint`.
-/

open MeasureTheory ProbabilityTheory Filter Learning
open scoped Topology ENNReal NNReal Matrix

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

omit [IsProbabilityMeasure P] in
/-- **Convergence in measure from `o_p(1)` of the norm.** A normed-space-valued sequence converges
to `0` in measure as soon as its norm is `o_p(1)` (the deviation sets `{ε ≤ ‖V n‖}` are literally
the sets controlled by `IsLittleOpOne` of `‖V n‖`). -/
lemma tendstoInMeasure_of_isLittleOpOne_norm {F : Type*} [NormedAddCommGroup F]
    {V : ℕ → Ω → F} (hV : IsLittleOpOne P (fun n ω ↦ ‖V n ω‖)) :
    TendstoInMeasure P V atTop (fun _ ↦ 0) := by
  intro ε hε
  refine (hV ε hε).congr fun n ↦ ?_
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, edist_zero_right, enorm_norm]

omit [IsProbabilityMeasure P] in
/-- **Coordinatewise `o_p(1)` gives vector convergence in measure.** If each coordinate `D k` of a
finite family is `o_p(1)`, then the `EuclideanSpace`-valued vector `ω ↦ (D k n ω)_k` converges to
`0` in measure. The Euclidean norm is dominated by the `ℓ¹`-sum `∑_k |D k|`, itself `o_p(1)`. -/
lemma tendstoInMeasure_toLp_of_forall_isLittleOpOne {ι : Type*} [Fintype ι]
    {D : ι → ℕ → Ω → ℝ} (hD : ∀ k, IsLittleOpOne P (D k)) :
    TendstoInMeasure P
      (fun n ω ↦ (WithLp.toLp 2 (fun k ↦ D k n ω) : EuclideanSpace ℝ ι)) atTop (fun _ ↦ 0) := by
  refine tendstoInMeasure_of_isLittleOpOne_norm ?_
  have hsum : IsLittleOpOne P (fun n ω ↦ ∑ k, |D k n ω|) :=
    isLittleOpOne_finset_sum fun k _ ↦ (hD k).abs
  refine IsLittleOpOne.of_abs_le (fun n ω ↦ ?_) hsum
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Finset.sum_nonneg fun k _ ↦ abs_nonneg _),
    norm_toLp_eq_sqrt, show (∑ k, (D k n ω) ^ 2) = ∑ k, |D k n ω| ^ 2 by simp_rw [sq_abs]]
  calc √(∑ k, |D k n ω| ^ 2)
      ≤ √((∑ k, |D k n ω|) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ ↦ abs_nonneg _))
    _ = ∑ k, |D k n ω| := Real.sqrt_sq (Finset.sum_nonneg (fun i _ ↦ abs_nonneg _))

/-- **Joint central limit theorem at an abstract hitting time** (blueprint `thm:normality` part
(ii), generic form). The abstract-hitting-time generalisation of `aRTS_clt_joint`: from Condition
**A** (`hY2`, `hνk`), a `LipschitzWith K` simplex-valued target `T`, `α ∈ [0,1)`, the non-sparsity
`hTpos`, the differentiability `hTderiv`, a measurable hitting predicate `Q` with throttle
`hthrottle`, consistency smallness `hgs` and `o_p`-smallness `hsmall_op`, the `√n`-scaled joint
vector `(√n(N_n/n - v), √n(ρ̂_n - v))` converges weakly to the block-Gaussian `𝒩(0, Ω)`. The
`thm:LLN` consistencies `θ̂ → θ` (`theta_consistent_of_hitting`), `N/n → v`
(`proportion_tendsto_of_hitting`) and the non-sparsity are derived, and the proportion-deviation
`√n(N_n/n - ρ̂_n) →ₚ 0` is discharged from `prop_dev_of_hitting` (part (i)). -/
lemma clt_joint_of_hitting [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (G : Matrix 𝓐 𝓐 ℝ)
    (hTderiv : HasFDerivAt
      (fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (T (WithLp.ofLp x)) : EuclideanSpace ℝ 𝓐))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) G) (WithLp.toLp 2 (fun k ↦ (ν k)[id])))
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hQmeas : ∀ k m, MeasurableSet {ω | Q k ω m})
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hgs : ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count (fun j ↦ armIndicator A k j ω) (hitting (Q k ω) n)
          - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k) / (n : ℝ) < δ)
    (hsmall_op : ∀ k, IsLittleOpOne P (fun n ω ↦
      max ((1 + (count (fun j ↦ armIndicator A k j ω) (hitting (Q k ω) n)
        - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k)) / √n) 0)) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐)))
      (fun n : ℕ ↦ (⟨P.map (jointSqrtNVec ν A Y θ₀ T (T (fun k' ↦ (ν k')[id])) n),
        Measure.isProbabilityMeasure_map
          (measurable_jointSqrtNVec h θ₀ hlip.continuous (T (fun k' ↦ (ν k')[id])) n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐))))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.fromBlocks
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)),
          inferInstance⟩) := by
  have hT : Continuous T := hlip.continuous
  -- The `thm:LLN` consistencies at the hitting time.
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ armIndicator A k' j ω)
      (fun j ↦ Y j ω) (θ₀ k') n) atTop (𝓝 (fun k ↦ (ν k)[id])) :=
    theta_consistent_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα Q hthrottle hgs hTpos
  have hmem : ∀ k', (ν k')[id] ∈ attainableSet A Y (θ₀ k') k' := by
    obtain ⟨ω, hω⟩ := hcons.exists
    exact fun k' ↦ estimator_limit_mem_attainableSet k' (θ₀ k') (tendsto_pi_nhds.mp hω k')
  have hv : ∀ a, 0 < T (fun k' ↦ (ν k')[id]) a := fun a ↦ hTpos (fun k ↦ (ν k)[id]) hmem a
  have hNconv_arm : ∀ k', ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ count (fun j ↦ armIndicator A k' j ω) n / (n : ℝ))
        atTop (𝓝 (T (fun k'' ↦ (ν k'')[id]) k')) := fun k' ↦
    (proportion_tendsto_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα Q hthrottle hgs hTpos k').mono
      fun ω hω ↦ hω.congr fun n ↦ by rw [count_indicator_eq_pullCount]
  have hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (T (fun k' ↦ (ν k')[id]) a)) := ae_all_iff.mpr hNconv_arm
  -- The proportion-deviation fact `√n(N_n/n - ρ̂_n) →ₚ 0`, discharged from `prop_dev_of_hitting`.
  have hprop : TendstoInMeasure P (fun n ω ↦ propSqrtNVec A (T (fun k' ↦ (ν k')[id])) n ω
      - targetSqrtNVec ν A Y θ₀ T n ω) atTop (fun _ ↦ 0) := by
    have hpd : ∀ k, IsLittleOpOne P (fun n ω ↦ ((pullCount A k n ω : ℝ)
        - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k) / √n) :=
      fun k ↦ prop_dev_of_hitting h hY2 θ₀ T hTnn hTsum α hα hα1 hlip hTpos hcons hNconv_arm
        Q hQmeas hthrottle hsmall_op k
    have hfun : (fun n ω ↦ propSqrtNVec A (T (fun k' ↦ (ν k')[id])) n ω
          - targetSqrtNVec ν A Y θ₀ T n ω)
        = fun n ω ↦ (WithLp.toLp 2 (fun k ↦ ((pullCount A k n ω : ℝ)
            - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k) / √n) : EuclideanSpace ℝ 𝓐) := by
      funext n ω
      -- The `√n`-scaling identity `√n(a/n - c) - √n(t - c) = (a - n t)/√n`.
      have key : ∀ a c t : ℝ,
          √(n : ℝ) * (a / (n : ℝ) - c) - √(n : ℝ) * (t - c) = (a - (n : ℝ) * t) / √(n : ℝ) := by
        intro a c t
        have hrw : √(n : ℝ) * (a / (n : ℝ) - c) - √(n : ℝ) * (t - c)
            = √(n : ℝ) * (a / (n : ℝ) - t) := by ring
        rw [hrw]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
          have hs : √(n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hnR
          have hs2 : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hnR.le
          rw [eq_div_iff hs, mul_right_comm, hs2, mul_sub, mul_comm (n : ℝ) (a / (n : ℝ)),
            div_mul_cancel₀ a hnR.ne']
      simp only [propSqrtNVec, targetSqrtNVec, ← WithLp.toLp_sub]
      congr 1
      funext k
      simp only [Pi.sub_apply, count_indicator_eq_pullCount, aRTSTarget]
      exact key _ _ _
    rw [hfun]
    exact tendstoInMeasure_toLp_of_forall_isLittleOpOne hpd
  exact clt_joint (v := T (fun k' ↦ (ν k')[id]))
    h hY2 θ₀ hνk hv hNconv hT G hTderiv hcons hprop

/-- **Joint central limit theorem for the aRTS design** (blueprint `thm:normality` part (ii)),
fully self-contained. From the `aRTS` design bundle — an `IsAlgEnvSeq` sequence, Condition **A**
(`hY2` and the kernel `L²` bound `hνk`), a simplex-valued target `T` that is `LipschitzWith K`
(Condition **B**), the algorithm-level predicate `IsARTS`, `α ∈ [0,1)`, the non-sparsity `hTpos`,
and the first-order differentiability of `T` at `θ` with Jacobian `G` (`hTderiv`) — the `√n`-scaled
joint vector `(√n(N_n/n - v), √n(ρ̂_n - v))` converges weakly to the block-Gaussian `𝒩(0, Ω)`, with
every block equal to `G · diag(V_k / v_k) · Gᵀ` with `V_k = Var[id; ν k]`, and
`v_k = T((ν_k)[id])_k`.

The `aRTS` instantiation of `clt_joint_of_hitting` at the last under-sampling time: the throttle is
`throttle_of_isARTS` (from `IsARTS`), the consistency smallness is `generic_small_of_hitting`, and
the `o_p`-smallness is automatic (`N_ℓ - ℓ ρ̂_ℓ ≤ 0`, `preliminary_small`). -/
theorem aRTS_clt_joint [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1) (hARTS : IsARTS alg θ₀ T α)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (G : Matrix 𝓐 𝓐 ℝ)
    (hTderiv : HasFDerivAt
      (fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (T (WithLp.ofLp x)) : EuclideanSpace ℝ 𝓐))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) G) (WithLp.toLp 2 (fun k ↦ (ν k)[id]))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐)))
      (fun n : ℕ ↦ (⟨P.map (jointSqrtNVec ν A Y θ₀ T (T (fun k' ↦ (ν k')[id])) n),
        Measure.isProbabilityMeasure_map
          (measurable_jointSqrtNVec h θ₀ hlip.continuous (T (fun k' ↦ (ν k')[id])) n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐))))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.fromBlocks
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)),
          inferInstance⟩) :=
  clt_joint_of_hitting h hY2 hνk θ₀ T hTnn hTsum α hα hα1 hlip hTpos G hTderiv
    (aRTSUnder A Y θ₀ T) (fun k m ↦ measurableSet_aRTSUnder h θ₀ hlip.continuous k m)
    (fun k ↦ throttle_of_isARTS h hARTS k)
    (fun k ↦ Eventually.of_forall fun ω δ hδ ↦ generic_small_of_hitting
      (fun j ↦ armIndicator A k j ω) (fun j ↦ aRTSTarget A Y θ₀ T j ω k)
      (aRTSUnder A Y θ₀ T k ω) (fun _ hm ↦ hm) δ hδ)
    (fun k ↦ by
      refine IsLittleOpOne.of_abs_le (Y := fun n (_ : Ω) ↦ (1 : ℝ) / √n) ?_
        (isLittleOpOne_const_div_sqrt 1)
      intro n ω
      have hps := preliminary_small (fun j ↦ armIndicator A k j ω)
        (fun m ↦ aRTSTarget A Y θ₀ T m ω k) (aRTSUnder A Y θ₀ T k ω) n (fun m hm ↦ hm)
      rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (by positivity)]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
        refine max_le ?_ (by positivity)
        gcongr
        linarith [hps])

end AlphaRAR
