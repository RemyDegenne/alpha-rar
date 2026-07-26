/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.DeviationBound

/-!
# `ell_rho_control` and the assembled `prop_dev` deviation bound

This file assembles the `o_p(√n)` deviation bound `lem:prop_dev` from the generic pieces of
`DeviationBound.lean`. The one Condition-B–specific input is packaged as the hypothesis `hlip`
of `ell_rho_control`: the target map `T` is Lipschitz near `θ`, so (eventually) the plug-in target
increment is controlled by the estimator increment,
`|ρ̂_ℓ - ρ̂_n| ≤ L‖θ̂_ℓ - θ̂_n‖ ≤ L∑_{k'}|θ̂_{ℓ,k'} - θ̂_{n,k'}|`. Everything else (the
estimator-increment control, the coefficient `o_p`/`O_p` bounds,
the drift-sign argument, the simplex reverse step) is proved.


## Main results

* `AlphaRAR.ell_rho_control`: the `ρ`-increment bound `ℓ(ρ̂_ℓ - ρ̂_n) ≤ Vρ·(n-ℓ) + Wρ`.
* `AlphaRAR.prop_dev_of_generic`: `Dev_k = o_p(√n)` from the per-arm one-sided bounds.
-/

open MeasureTheory Filter Finset
open scoped ENNReal Topology

namespace AlphaRAR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Control of the plug-in-target increment** (blueprint `lem:ell_rho_control`), parameterized by
the Condition-B Lipschitz bound `hlip`. Given the estimator-increment control `hdiff`
(`AlphaRAR.abs_estimator_diff_le`), the coefficient bounds (`g = o_p(1)` and the reweighting
coefficient `h ≥ 0` bounded in probability, `h = O_p(1)`), and the `Q`-increment control
(`Q-increment ≤ Qv·(n-ℓ) + Qw` with `Qv = o_p(1)`, `Qw = o_p(√n)`), the scaled target increment
`rhoterm = ℓ(ρ̂_ℓ - ρ̂_n)` is bounded by `Vρ·(n-ℓ) + Wρ` with `Vρ = o_p(1)` and `Wρ = o_p(√n)`. The
reweighting coefficient `h = ℓ/(N_n+1)` is only *bounded in probability* (it converges a.s. to
`1/v_k`), not by a uniform constant, so it enters via `O_p·o_p = o_p`. -/
lemma ell_rho_control {ι : Type*} [Fintype ι] {rhoterm d : ℕ → Ω → ℝ}
    {θdiff g h Qinc : ι → ℕ → Ω → ℝ}
    {Qvinc Qwinc : ℕ → Ω → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ n ω, rhoterm n ω ≤ L * ∑ k, θdiff k n ω)
    (hdiff : ∀ k n ω, θdiff k n ω ≤ g k n ω * d n ω + h k n ω * Qinc k n ω)
    (hg : ∀ k, IsLittleOpOne μ (g k)) (hhnn : ∀ k n ω, 0 ≤ h k n ω)
    (hh : ∀ k, IsBigOpOne μ (h k))
    (hQinc : ∀ᶠ n in atTop, ∀ k ω, Qinc k n ω ≤ Qvinc n ω * d n ω + Qwinc n ω)
    (hQv : IsLittleOpOne μ Qvinc) (hQw : IsLittleOpOne μ (fun n ω ↦ Qwinc n ω / √n)) :
    ∃ Vρ Wρ : ℕ → Ω → ℝ, (∀ᶠ n in atTop, ∀ ω, rhoterm n ω ≤ Vρ n ω * d n ω + Wρ n ω)
      ∧ IsLittleOpOne μ Vρ ∧ IsLittleOpOne μ (fun n ω ↦ Wρ n ω / √n) := by
  refine ⟨fun n ω ↦ L * (∑ k, g k n ω) + L * (∑ k, h k n ω * Qvinc n ω),
    fun n ω ↦ L * (∑ k, h k n ω * Qwinc n ω), ?_, ?_, ?_⟩
  · filter_upwards [hQinc] with n hQincn
    intro ω
    have hstep : ∀ k, θdiff k n ω
        ≤ g k n ω * d n ω + h k n ω * (Qvinc n ω * d n ω + Qwinc n ω) := fun k ↦
      (hdiff k n ω).trans (by gcongr; exacts [hhnn k n ω, hQincn k ω])
    calc rhoterm n ω
        ≤ L * ∑ k, θdiff k n ω := hlip n ω
      _ ≤ L * ∑ k, (g k n ω * d n ω + h k n ω * (Qvinc n ω * d n ω + Qwinc n ω)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ hstep k) hL
      _ = (L * (∑ k, g k n ω) + L * (∑ k, h k n ω * Qvinc n ω)) * d n ω
            + L * (∑ k, h k n ω * Qwinc n ω) := by
          have hexp : ∀ k, g k n ω * d n ω + h k n ω * (Qvinc n ω * d n ω + Qwinc n ω)
              = g k n ω * d n ω + h k n ω * Qvinc n ω * d n ω + h k n ω * Qwinc n ω :=
            fun k ↦ by ring
          rw [Finset.sum_congr rfl (fun k _ ↦ hexp k), Finset.sum_add_distrib,
            Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
  · have h1 : IsLittleOpOne μ (fun n ω ↦ ∑ k, g k n ω) := isLittleOpOne_finset_sum fun k _ ↦ hg k
    have h2 : IsLittleOpOne μ (fun n ω ↦ ∑ k, h k n ω * Qvinc n ω) :=
      isLittleOpOne_finset_sum fun k _ ↦ (hh k).mul_littleOp hQv
    exact (IsLittleOpOne.const_mul L h1).add (IsLittleOpOne.const_mul L h2)
  · have heq : (fun n ω ↦ (L * (∑ k, h k n ω * Qwinc n ω)) / √n)
        = fun n ω ↦ L * ∑ k, h k n ω * (Qwinc n ω / √n) := by
      funext n ω
      rw [mul_div_assoc, Finset.sum_div]
      exact congrArg (L * ·) (Finset.sum_congr rfl fun k _ ↦ by rw [mul_div_assoc])
    rw [heq]
    exact IsLittleOpOne.const_mul L
      (isLittleOpOne_finset_sum fun k _ ↦ (hh k).mul_littleOp hQw)

/-- **Deviation between proportions and plug-in target** (blueprint `lem:prop_dev`, `o_p(√n)` part).
Assembling all generic pieces: for a finite family with `∑_k Dev_k = 0`, the generic-inequality
bound `Dev_k ≤ small_k + Uincr_k` with `small = o_p(√n)`, and the `U`-increment decomposition
(drift `-c_k`, an `M`-term and a `ρ`-term each increment-controlled, and an `o_p(1)` perturbation),
we get `Dev_k = o_p(√n)` for every arm `k`. -/
theorem prop_dev {ι : Type*} [Fintype ι]
    {Dev small Uincr Mincr rhoterm pert : ι → ℕ → Ω → ℝ} {d : ι → ℕ → Ω → ℝ} {c : ι → ℝ}
    {VM WM Vρ Wρ : ι → ℕ → Ω → ℝ}
    (hsum : ∀ n ω, ∑ k, Dev k n ω = 0)
    (hle : ∀ k n, ∀ᵐ ω ∂μ, Dev k n ω ≤ small k n ω + Uincr k n ω)
    (hsmall : ∀ k, IsLittleOpOne μ (fun n ω ↦ max (small k n ω / √n) 0))
    (hc : ∀ k, 0 < c k) (hd : ∀ k n ω, 0 ≤ d k n ω)
    (hdecomp : ∀ k n ω,
      Uincr k n ω ≤ -c k * d k n ω + Mincr k n ω + rhoterm k n ω + pert k n ω * d k n ω)
    (hpert : ∀ k, IsLittleOpOne μ (pert k))
    (hMbound : ∀ k, ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, Mincr k n ω ≤ VM k n ω * d k n ω + WM k n ω)
    (hVM : ∀ k, IsLittleOpOne μ (VM k))
    (hWM : ∀ k, IsLittleOpOne μ (fun n ω ↦ WM k n ω / √n))
    (hρbound : ∀ k, ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, rhoterm k n ω ≤ Vρ k n ω * d k n ω + Wρ k n ω)
    (hVρ : ∀ k, IsLittleOpOne μ (Vρ k))
    (hWρ : ∀ k, IsLittleOpOne μ (fun n ω ↦ Wρ k n ω / √n)) (k : ι) :
    IsLittleOpOne μ (fun n ω ↦ Dev k n ω / √n) := by
  refine isLittleOpOne_dev_of_sum_zero hsum (fun j ↦ isLittleOpOne_maxDev_of_le (hle j)
    (hsmall j) ?_) k
  exact isLittleOpOne_max_of_decomp (hc j) (hd j) (hdecomp j) (hpert j) (hMbound j) (hVM j) (hWM j)
    (hρbound j) (hVρ j) (hWρ j)

end AlphaRAR
