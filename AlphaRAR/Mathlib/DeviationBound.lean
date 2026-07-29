/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.StochasticOrder

/-!
# One-sided `o_p(√n)` deviation bounds

This file develops the "drift-sign" lemma used to turn the additive `U`-increment decomposition into
a one-sided `o_p(√n)` bound: if `X_n ≤ (n-ℓ_n)(-c + A_n) + B_n √n` with `c > 0` a constant, `A_n =
o_p(1)`, `B_n = o_p(1)` and `n - ℓ_n ≥ 0`, then the positive part `(X_n/√n)^+ = o_p(1)`, i.e.
`X_n ≤ o_p(√n)` one-sidedly. The negative drift `-c` eventually dominates the `o_p(1)` perturbation
(in probability), forcing the `(n-ℓ_n)`-term nonpositive.

The generic `o_p`/`O_p` closure properties this uses (domination, absolute values, constant
multiples, finite sums) live with the definitions in `StochasticOrder.lean`; what is specific to
this file is the drift-sign argument and its assembly into a per-arm deviation bound.

## Main results

* `AlphaRAR.isLittleOpOne_max_div_sqrt_of_drift`: the drift-sign lemma.
* `AlphaRAR.isLittleOpOne_max_of_decomp`: the same for the full `U`-increment decomposition.
* `AlphaRAR.isLittleOpOne_maxDev_of_le` and `AlphaRAR.isLittleOpOne_dev_of_sum_zero`: transfer to
  the deviations, and the simplex reverse step turning one-sided bounds into two-sided ones.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace AlphaRAR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Drift-sign one-sided `o_p(√n)`.** If eventually `X_n ≤ d_n(-c + A_n) + B_n √n` with `c > 0`,
`d_n ≥ 0`, and `A_n, B_n = o_p(1)`, then `(X_n/√n)^+ = o_p(1)`. The window `d_n = n - ℓ_n` need not
be bounded; only `d_n ≥ 0` and the negative drift `-c` are used. The decomposition need only hold
*eventually* (in `n`), since `o_p` depends only on the tail. -/
lemma isLittleOpOne_max_div_sqrt_of_drift {c : ℝ} (hc : 0 < c)
    {A B X d : ℕ → Ω → ℝ} (hA : IsLittleOpOne μ A) (hB : IsLittleOpOne μ B)
    (hd : ∀ n ω, 0 ≤ d n ω)
    (hX : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, X n ω ≤ d n ω * (-c + A n ω) + B n ω * √n) :
    IsLittleOpOne μ (fun n ω ↦ max (X n ω / √n) 0) := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hbound : ∀ᶠ n in atTop, μ {ω | ε ≤ |max (X n ω / √n) 0|}
      ≤ μ {ω | c ≤ |A n ω|} + μ {ω | ε ≤ |B n ω|} := by
    filter_upwards [hX, eventually_ge_atTop 1] with n hXn hn
    refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
    filter_upwards [hXn] with ω hXω
    intro hω
    have hωval : ε ≤ |max (X n ω / √n) 0| := hω
    rw [abs_of_nonneg (le_max_right (X n ω / √n) 0)] at hωval
    change c ≤ |A n ω| ∨ ε ≤ |B n ω|
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    obtain ⟨hAc, hBε⟩ := hcon
    have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hAlt : A n ω < c := lt_of_abs_lt hAc
    have hdrift : d n ω * (-c + A n ω) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hd n ω) (by linarith)
    have hXle : X n ω ≤ B n ω * √n := by linarith [hXω]
    have hXdiv : X n ω / √n ≤ B n ω := (div_le_iff₀ hsn).mpr hXle
    have hBlt : B n ω < ε := lt_of_abs_lt hBε
    have hmax : max (X n ω / √n) 0 < ε :=
      max_lt_iff.mpr ⟨lt_of_le_of_lt hXdiv hBlt, hε⟩
    linarith
  have hsum : Tendsto (fun n ↦ μ {ω | c ≤ |A n ω|} + μ {ω | ε ≤ |B n ω|}) atTop (𝓝 0) := by
    simpa using (hA.tendsto_abs hc).add (hB.tendsto_abs hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun n ↦ zero_le)) hbound

/-- **Generic `U`-increment bound** (blueprint `lem:U_increment_bound`, `o_p(√n)` half). If the
`U`-increment decomposes as `U_n - U_ℓ ≤ -c·d_n + M_n + ρ_n + pert_n·d_n` with `c > 0`, `d_n ≥ 0`,
`pert = o_p(1)`, and the `M`- and `ρ`-terms are increment-controlled `≤ V·d_n + W` with
`V = o_p(1)`, `W = o_p(√n)`, then `(U_n - U_ℓ)^+ = o_p(√n)` (one-sided). The negative drift `-c`
absorbs all the
`o_p(1)·d_n` perturbations. -/
lemma isLittleOpOne_max_of_decomp {c : ℝ} (hc : 0 < c)
    {d Uincr Mincr rhoterm pert VM WM Vρ Wρ : ℕ → Ω → ℝ}
    (hd : ∀ n ω, 0 ≤ d n ω)
    (hdecomp : ∀ n ω, Uincr n ω ≤ -c * d n ω + Mincr n ω + rhoterm n ω + pert n ω * d n ω)
    (hpert : IsLittleOpOne μ pert)
    (hMbound : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, Mincr n ω ≤ VM n ω * d n ω + WM n ω)
    (hVM : IsLittleOpOne μ VM) (hWM : IsLittleOpOne μ (fun n ω ↦ WM n ω / √n))
    (hρbound : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, rhoterm n ω ≤ Vρ n ω * d n ω + Wρ n ω)
    (hVρ : IsLittleOpOne μ Vρ) (hWρ : IsLittleOpOne μ (fun n ω ↦ Wρ n ω / √n)) :
    IsLittleOpOne μ (fun n ω ↦ max (Uincr n ω / √n) 0) := by
  refine isLittleOpOne_max_div_sqrt_of_drift hc
    (A := fun n ω ↦ VM n ω + Vρ n ω + pert n ω)
    (B := fun n ω ↦ WM n ω / √n + Wρ n ω / √n)
    ((hVM.add hVρ).add hpert) (hWM.add hWρ) hd ?_
  filter_upwards [hMbound, hρbound, eventually_ge_atTop 1] with n hMbn hρbn hn
  filter_upwards [hMbn, hρbn] with ω hMb hρb
  have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hB : (WM n ω / √n + Wρ n ω / √n) * √n = WM n ω + Wρ n ω := by
    field_simp
  have hexpand : d n ω * (-c + (VM n ω + Vρ n ω + pert n ω)) + (WM n ω + Wρ n ω)
      = -c * d n ω + (VM n ω * d n ω + WM n ω) + (Vρ n ω * d n ω + Wρ n ω)
        + pert n ω * d n ω := by ring
  change Uincr n ω ≤ d n ω * (-c + (VM n ω + Vρ n ω + pert n ω))
    + (WM n ω / √n + Wρ n ω / √n) * √n
  rw [hB, hexpand]
  linarith [hdecomp n ω, hMb, hρb]

/-- **Forward one-sided deviation bound.** If `Dev_n ≤ small_n + Uincr_n` with `(small/√n)^+ =
o_p(1)` and `(Uincr/√n)^+ = o_p(1)`, then `(Dev_n/√n)^+ = o_p(1)`. -/
lemma isLittleOpOne_maxDev_of_le {Dev small Uincr : ℕ → Ω → ℝ}
    (hDev : ∀ n, ∀ᵐ ω ∂μ, Dev n ω ≤ small n ω + Uincr n ω)
    (hsmall : IsLittleOpOne μ (fun n ω ↦ max (small n ω / √n) 0))
    (hU : IsLittleOpOne μ (fun n ω ↦ max (Uincr n ω / √n) 0)) :
    IsLittleOpOne μ (fun n ω ↦ max (Dev n ω / √n) 0) := by
  refine IsLittleOpOne.of_abs_le_ae
    (Y := fun n ω ↦ max (small n ω / √n) 0 + max (Uincr n ω / √n) 0) ?_
    (hsmall.add hU)
  intro n
  filter_upwards [hDev n] with ω hDevω
  rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Real.sqrt_zero]
  · have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hdiv : Dev n ω / √n
        ≤ small n ω / √n + Uincr n ω / √n := by
      rw [← add_div]; gcongr
    refine max_le ?_ (by positivity)
    have hsle := le_max_left (small n ω / √n) 0
    have hUle := le_max_left (Uincr n ω / √n) 0
    linarith

/-- **Two-sided deviation from one-sided bounds** (blueprint `lem:prop_dev` reverse step). For a
finite family `Dev` with `∑_j Dev_j = 0` (the counts/target simplex identity), if each positive
part `(Dev_j/√n)^+ = o_p(1)`, then `Dev_k = o_p(√n)` for every `k`. The reverse inequality
`-Dev_k = ∑_{j≠k} Dev_j` transfers the one-sided bounds. -/
lemma isLittleOpOne_dev_of_sum_zero {ι : Type*} [Fintype ι]
    {Dev : ι → ℕ → Ω → ℝ} (hsum : ∀ n ω, ∑ j, Dev j n ω = 0)
    (hfwd : ∀ j, IsLittleOpOne μ (fun n ω ↦ max (Dev j n ω / √n) 0)) (k : ι) :
    IsLittleOpOne μ (fun n ω ↦ Dev k n ω / √n) := by
  classical
  apply isLittleOpOne_of_abs
  have hrev : IsLittleOpOne μ (fun n ω ↦ max (-(Dev k n ω / √n)) 0) := by
    refine IsLittleOpOne.of_abs_le
      (Y := fun n ω ↦ ∑ j ∈ Finset.univ.erase k, max (Dev j n ω / √n) 0) ?_
      (isLittleOpOne_finset_sum fun j _ ↦ hfwd j)
    intro n ω
    rw [abs_of_nonneg (le_max_right _ _),
      abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ le_max_right _ _)]
    have hneg : -(Dev k n ω / √n)
        = ∑ j ∈ Finset.univ.erase k, Dev j n ω / √n := by
      have key : Dev k n ω + ∑ j ∈ Finset.univ.erase k, Dev j n ω = ∑ j, Dev j n ω :=
        Finset.add_sum_erase Finset.univ (fun j ↦ Dev j n ω) (Finset.mem_univ k)
      have h2 : ∑ j ∈ Finset.univ.erase k, Dev j n ω = -(Dev k n ω) := by
        have hz := hsum n ω
        linarith [key, hz]
      rw [← Finset.sum_div, h2, neg_div]
    rw [hneg]
    exact max_le (Finset.sum_le_sum fun j _ ↦ le_max_left _ _)
      (Finset.sum_nonneg fun j _ ↦ le_max_right _ _)
  have hpm : ∀ x : ℝ, |x| = max x 0 + max (-x) 0 := by
    intro x; rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : -x ≤ 0), add_zero]
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -x), zero_add]
  have hcomb : (fun n ω ↦ |Dev k n ω / √n|)
      = fun n ω ↦ max (Dev k n ω / √n) 0 + max (-(Dev k n ω / √n)) 0 := by
    funext n ω; exact hpm _
  rw [hcomb]
  exact (hfwd k).add hrev

end AlphaRAR
