/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Kronecker's lemma

If the partial sums `∑_{k < n} x k` converge, then the identity-weighted averages
`(1/n) ∑_{k < n} k · x k` tend to `0`.

This is the special case `b_k = k` of Kronecker's lemma (positive nondecreasing weights `b_k → ∞`),
which is the form used in the martingale strong law of large numbers: applying it to
`x_k = ΔM_k / k` turns the a.s. convergence of the weighted series `∑ ΔM_k / k` into `M_n / n → 0`.
The identity-weight case reduces to the Cesàro theorem (`Filter.Tendsto.cesaro`) via summation by
parts, avoiding the general Silverman–Toeplitz argument.

This belongs in Mathlib (only the unrelated matrix "Kronecker" results are there).

## Main results

* `AlphaRAR.kronecker`: `(1/n) ∑_{k < n} k · x k → 0` when `∑_{k < n} x k → s`.
-/

open Filter Finset
open scoped Topology

namespace AlphaRAR

/-- **Kronecker's lemma** (identity weights `b_k = k`). If the partial sums `∑_{k < n} x k`
converge to `s`, then `(1/n) ∑_{k < n} k · x k → 0`.

Summation by parts turns `∑_{k < n} k · x k` into `(n-1) · Sₙ - ∑_{k < n} Sₖ` (with
`Sₙ = ∑_{k < n} x k`); dividing by `n`, the first term tends to `s` and the second (a Cesàro
average of `S`) also tends to `s`, so the difference tends to `0`. -/
theorem kronecker {x : ℕ → ℝ} {s : ℝ}
    (hx : Tendsto (fun n ↦ ∑ k ∈ range n, x k) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, (k : ℝ) * x k) atTop (𝓝 0) := by
  set S : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, x k with hS
  -- `(1/n) ∑_{k<n} Sₖ → s` (Cesàro average of the convergent sequence `S`).
  have hces : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, S k) atTop (𝓝 s) := by
    simpa [smul_eq_mul] using hx.cesaro
  -- `(n)⁻¹ → 0`, hence `1 - (n)⁻¹ → 1` and `(1 - (n)⁻¹) · Sₙ → s`.
  have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfirst : Tendsto (fun n : ℕ ↦ (1 - (n : ℝ)⁻¹) * S n) atTop (𝓝 s) := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 - (n : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hinv
    simpa using h1.mul hx
  -- The two limits combine to `s - s = 0`; identify with the target eventually.
  have hg : Tendsto (fun n : ℕ ↦ (1 - (n : ℝ)⁻¹) * S n - (n : ℝ)⁻¹ * ∑ k ∈ range n, S k)
      atTop (𝓝 (s - s)) := hfirst.sub hces
  rw [sub_self] at hg
  refine hg.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Summation by parts: `∑_{k<n} k·x k = (n-1)·Sₙ - ∑_{k<n-1} S_{k+1}`.
  have hbp : ∑ k ∈ range n, (k : ℝ) * x k
      = ((n - 1 : ℕ) : ℝ) * S n - ∑ i ∈ range (n - 1), S (i + 1) := by
    have hparts := Finset.sum_range_by_parts (fun i ↦ (i : ℝ)) x n
    simp only [smul_eq_mul] at hparts
    rw [hparts]
    refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [show ((i + 1 : ℕ) : ℝ) - (i : ℝ) = 1 by push_cast; ring, one_mul]
  -- Reindex `∑_{k<n-1} S_{k+1} = ∑_{k<n} S k` using `S 0 = 0`.
  have hreindex : ∑ i ∈ range (n - 1), S (i + 1) = ∑ k ∈ range n, S k := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sum_range_succ']
    simp [hS]
  rw [hbp, hreindex, Nat.cast_sub hn, Nat.cast_one]
  field_simp

end AlphaRAR
