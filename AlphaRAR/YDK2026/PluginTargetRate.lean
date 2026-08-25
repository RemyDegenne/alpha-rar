/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.ResponseLIL
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Convergence rate of the plug-in target (the delta method)

The plug-in target is `ρ̂_{n,k} = T(θ̂_n)_k`, the (Condition **B**) target map `T` applied to the
vector of sequential estimators `θ̂_n = (θ̂_{n,k'})_{k'}`. This file transports the almost-sure
loglog rate of the estimator (`abs_estimator_sub_le_rate_loglog_of_proportion`, blueprint
`lem:theta_LIL`) to the plug-in target via the **delta method** (blueprint `lem:rho_rate`): a
first-order expansion of `T` at `θ` shows that a differentiable map preserves the `O(r_n)` rate,
`T(θ̂_n) - T(θ) = O(‖θ̂_n - θ‖) = O(r_n)`.

## Main results

* `AlphaRAR.isBigO_sub_comp_of_differentiableAt`: the generic delta-method estimate — a map
  differentiable at `x₀` sends a sequence `g_n → x₀` to `f(g_n) - f(x₀) = O(g_n - x₀)`.
* `AlphaRAR.isBigO_target_sub_of_tendsto`: the vector-to-target rate — if the estimator vector
  converges to `θ` with each component `O(r_n)` and `T` is differentiable at `θ`, then every
  coordinate `T(θ̂_n)_k - T(θ)_k = O(r_n)`.
* `AlphaRAR.rho_rate` (blueprint `lem:rho_rate`): the almost-sure loglog rate of the plug-in target,
  `ρ̂_{n,k} - v_k = O(√(log log n / n))`, given estimator consistency and the loglog estimator rate.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Learning Real Asymptotics

open scoped Topology

namespace AlphaRAR

/-- **Delta-method estimate.** A map `f` differentiable at `x₀` preserves big-`O` rates through a
sequence converging to `x₀`: if `g n → x₀` then `f (g n) - f x₀ = O(g n - x₀)`. This is
`HasFDerivAt.isBigO_sub` (the difference is `O` of the increment) composed with `g → x₀`. -/
lemma isBigO_sub_comp_of_differentiableAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x₀ : E} (hf : DifferentiableAt ℝ f x₀)
    {ι : Type*} {l : Filter ι} {g : ι → E} (hg : Tendsto g l (𝓝 x₀)) :
    (fun n ↦ f (g n) - f x₀) =O[l] (g · - x₀) :=
  hf.isBigO_sub.comp_tendsto hg

/-- **Coordinatewise delta-method rate.** If the vector-valued sequence `g n → x₀` has each
coordinate `O(r n)` and `f` is differentiable at `x₀`, then every coordinate of `f (g n) - f x₀` is
`O(r n)`. This is the delta method that turns the estimator's loglog rate into the plug-in target's
loglog rate. -/
lemma isBigO_target_sub_of_tendsto {ι : Type*} [Finite ι] {κ : Type*} [Finite κ]
    {T : (ι → ℝ) → κ → ℝ} {θ : ι → ℝ} (hT : DifferentiableAt ℝ T θ)
    {g : ℕ → ι → ℝ} (hg : Tendsto g atTop (𝓝 θ))
    {r : ℕ → ℝ} (hrate : ∀ i, (g · i - θ i) =O[atTop] r) (k : κ) :
    (fun n ↦ T (g n) k - T θ k) =O[atTop] r := by
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  -- the whole increment vector is `O(r n)`, coordinatewise
  have hvec : (g · - θ) =O[atTop] r := isBigO_pi.mpr fun i ↦ hrate i
  -- the delta method preserves the rate
  have hdelta : (fun n ↦ T (g n) - T θ) =O[atTop] (g · - θ) :=
    isBigO_sub_comp_of_differentiableAt hT hg
  -- project onto coordinate `k`
  have hproj : (fun n ↦ T (g n) k - T θ k) =O[atTop] (fun n ↦ T (g n) - T θ) := by
    refine isBigO_of_le atTop fun n ↦ ?_
    rw [← Pi.sub_apply]
    exact norm_le_pi_norm _ k
  exact hproj.trans (hdelta.trans hvec)

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [Finite 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **Loglog rate of the plug-in target** (blueprint `lem:rho_rate`), abstract-rate form. Given the
estimator vector `θ̂_n → θ` a.s. (blueprint `lem:theta_consistent`), each component at the rate
`θ̂_{n,k} - θ_k = O(r_n)` a.s. (blueprint `lem:theta_LIL`), and the target map `T` differentiable at
`θ` (Condition **B**), the plug-in target `ρ̂_{n,k} = T(θ̂_n)_k` converges to `v_k = T(θ)_k` at the
same rate: `ρ̂_{n,k} - v_k = O(r_n)` a.s. for every arm `k`. -/
lemma rho_rate {θ : 𝓐 → ℝ} {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : DifferentiableAt ℝ T θ)
    {r : ℕ → ℝ}
    (hconsist : ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) atTop (𝓝 θ))
    (hrate : ∀ k, ∀ᵐ ω ∂P, (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
      (Y · ω) (θ₀ k) n - θ k) =O[atTop] r) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) k - T θ k) =O[atTop] r := by
  filter_upwards [hconsist, ae_all_iff.mpr hrate] with ω hcω hrω
  exact isBigO_target_sub_of_tendsto hT hcω hrω k

end AlphaRAR
