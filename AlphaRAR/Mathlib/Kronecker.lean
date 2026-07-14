/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# Kronecker's lemma

If `b` is positive, nondecreasing with `b n → ∞` and the partial sums `∑_{k < n} y k` converge,
then the `b`-weighted averages `(1/b n) ∑_{k < n} b (k+1) · y k` tend to `0`. This is the form of
Kronecker's lemma used in the martingale strong law of large numbers: applied to `y_k = ΔM_k / b_k`
with `b_k = 1 + ⟨M⟩_k`, it turns the a.s. convergence of the bracket-normalized series
`∑ ΔM_k / b_k` into `M_n / b_n → 0`.

We prove the general statement `kronecker_general` by summation by parts (a Toeplitz/Silverman
argument on the weights) and derive the identity-weight special cases `kronecker'` (weights `k + 1`)
and `kronecker` (weights `k`) as corollaries.

This belongs in Mathlib (only the unrelated matrix "Kronecker" results are there).

## Main results

* `AlphaRAR.kronecker_general`: `(1/b n) ∑_{k < n} b (k+1) · y k → 0` for positive nondecreasing
  `b n → ∞`, when `∑_{k < n} y k → s`.
* `AlphaRAR.kronecker'`: the special case with weights `b_k = k + 1`.
* `AlphaRAR.kronecker`: the special case with weights `b_k = k`.
-/

open Filter Finset
open scoped Topology

namespace AlphaRAR

/-- **Kronecker's lemma, general positive nondecreasing weights.** If `b` is positive, nondecreasing
and `b n → ∞`, and the partial sums `∑_{k<n} y k` converge (to `s`), then
`(1/b n) ∑_{k<n} b (k+1) · y k → 0`.

Summation by parts writes the sum as `b n · Sₙ − ∑_{i<n-1}(b_{i+2}-b_{i+1}) S_{i+1}` (with
`Sₙ = ∑_{k<n} y k`); dividing by `bₙ`, the first term is `Sₙ → s`, and the second is a
Toeplitz-weighted average of `(S_{i+1})` with nonnegative weights `(b_{i+2}-b_{i+1})/bₙ` summing to
`(bₙ-b₁)/bₙ → 1`, hence also `→ s`, so the difference `→ 0`. This generalizes
`kronecker`/`kronecker'` (weights `k`, `k+1`) to the random nondecreasing weights `b_k = 1+⟨M⟩_k`
of the bracket-normalized
martingale SLLN. -/
lemma kronecker_general {b y : ℕ → ℝ} {s : ℝ}
    (hb_pos : ∀ n, 0 < b n) (hb_mono : Monotone b) (hb_top : Tendsto b atTop atTop)
    (hy : Tendsto (fun n ↦ ∑ k ∈ range n, y k) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ ↦ (b n)⁻¹ * ∑ k ∈ range n, b (k + 1) * y k) atTop (𝓝 0) := by
  set S : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, y k with hS
  have hbinv : Tendsto (fun n : ℕ ↦ (b n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hb_top
  -- `εᵢ := S_{i+1} - s → 0`.
  have hεt : Tendsto (fun i : ℕ ↦ S (i + 1) - s) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ ↦ S (i + 1)) atTop (𝓝 s) := hy.comp (tendsto_add_atTop_nat 1)
    simpa using h1.sub_const s
  -- Telescoping weight total: `∑_{i<n-1}(b_{i+2}-b_{i+1}) = bₙ - b₁` for `n ≥ 1`.
  have htel : ∀ n : ℕ, 1 ≤ n →
      ∑ i ∈ range (n - 1), (b (i + 2) - b (i + 1)) = b n - b 1 := by
    intro n hn
    have key := Finset.sum_range_sub (fun i ↦ b (i + 1)) (n - 1)
    rw [Nat.sub_add_cancel hn] at key
    exact key
  -- Toeplitz core: the absolute weighted average of `|εᵢ|` tends to `0`.
  have hU : Tendsto (fun n : ℕ ↦ (b n)⁻¹ * ∑ i ∈ range (n - 1),
      (b (i + 2) - b (i + 1)) * |S (i + 1) - s|) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hεt (η / 2) (by linarith)
    set A : ℝ := ∑ i ∈ range N₁, (b (i + 2) - b (i + 1)) * |S (i + 1) - s| with hAdef
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ ↦
      mul_nonneg (by linarith [hb_mono (by omega : i + 1 ≤ i + 2)]) (abs_nonneg _)
    have hAdiv : Tendsto (fun n : ℕ ↦ A * (b n)⁻¹) atTop (𝓝 0) := by
      simpa using hbinv.const_mul A
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hAdiv (η / 2) (by linarith)
    refine ⟨max (N₁ + 1) N₂, fun n hn ↦ ?_⟩
    have hnN₁ : N₁ ≤ n - 1 := by omega
    have hnN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
    have hbn0 : 0 < b n := hb_pos n
    -- split the sum at `N₁`
    have hsplit : ∑ i ∈ range (n - 1), (b (i + 2) - b (i + 1)) * |S (i + 1) - s|
        = A + ∑ i ∈ Finset.Ico N₁ (n - 1), (b (i + 2) - b (i + 1)) * |S (i + 1) - s| :=
      (Finset.sum_range_add_sum_Ico _ hnN₁).symm
    -- tail bounded by `(η/2)(bₙ-b₁)`
    have htail : ∑ i ∈ Finset.Ico N₁ (n - 1), (b (i + 2) - b (i + 1)) * |S (i + 1) - s|
        ≤ (η / 2) * (b n - b 1) := by
      calc ∑ i ∈ Finset.Ico N₁ (n - 1), (b (i + 2) - b (i + 1)) * |S (i + 1) - s|
          ≤ ∑ i ∈ Finset.Ico N₁ (n - 1), (b (i + 2) - b (i + 1)) * (η / 2) := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            rw [Finset.mem_Ico] at hi
            have hwi : 0 ≤ b (i + 2) - b (i + 1) := by
              linarith [hb_mono (by omega : i + 1 ≤ i + 2)]
            have hεi : |S (i + 1) - s| ≤ η / 2 := by
              have := hN₁ i hi.1
              rw [Real.dist_eq, sub_zero] at this
              linarith
            exact mul_le_mul_of_nonneg_left hεi hwi
        _ = (η / 2) * ∑ i ∈ Finset.Ico N₁ (n - 1), (b (i + 2) - b (i + 1)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
        _ ≤ (η / 2) * (b n - b 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            calc ∑ i ∈ Finset.Ico N₁ (n - 1), (b (i + 2) - b (i + 1))
                ≤ ∑ i ∈ range (n - 1), (b (i + 2) - b (i + 1)) := by
                  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ ↦ by
                    linarith [hb_mono (by omega : i + 1 ≤ i + 2)]
                  rw [Finset.range_eq_Ico]; exact Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl
              _ = b n - b 1 := htel n (by omega)
    -- assemble
    have hbninv : 0 ≤ (b n)⁻¹ := inv_nonneg.mpr hbn0.le
    have hsum_nn : 0 ≤ ∑ i ∈ range (n - 1), (b (i + 2) - b (i + 1)) * |S (i + 1) - s| :=
      Finset.sum_nonneg fun i _ ↦
        mul_nonneg (by linarith [hb_mono (by omega : i + 1 ≤ i + 2)]) (abs_nonneg _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hbninv hsum_nn)]
    have hb1n : b 1 ≤ b n := hb_mono (by omega)
    have hkey : (b n)⁻¹ * (A + (η / 2) * (b n - b 1)) < η := by
      have h1 : (b n)⁻¹ * A < η / 2 := by
        have := hN₂ n hnN₂
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hA0 hbninv)] at this
        rw [mul_comm]; exact this
      have h2 : (b n)⁻¹ * ((η / 2) * (b n - b 1)) ≤ η / 2 := by
        have hle : (b n)⁻¹ * (b n - b 1) ≤ 1 := by
          rw [inv_mul_eq_div, div_le_one hbn0]; linarith [hb_pos 1]
        calc (b n)⁻¹ * ((η / 2) * (b n - b 1))
            = (η / 2) * ((b n)⁻¹ * (b n - b 1)) := by ring
          _ ≤ (η / 2) * 1 := mul_le_mul_of_nonneg_left hle (by linarith)
          _ = η / 2 := by ring
      calc (b n)⁻¹ * (A + (η / 2) * (b n - b 1))
          = (b n)⁻¹ * A + (b n)⁻¹ * ((η / 2) * (b n - b 1)) := by ring
        _ < η / 2 + η / 2 := by linarith
        _ = η := by ring
    calc (b n)⁻¹ * ∑ i ∈ range (n - 1), (b (i + 2) - b (i + 1)) * |S (i + 1) - s|
        = (b n)⁻¹ * (A + ∑ i ∈ Finset.Ico N₁ (n - 1),
            (b (i + 2) - b (i + 1)) * |S (i + 1) - s|) := by rw [hsplit]
      _ ≤ (b n)⁻¹ * (A + (η / 2) * (b n - b 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hbninv
          linarith
      _ < η := hkey
  -- The signed weighted average tends to `0` (dominated by the absolute one).
  have hR : Tendsto (fun n : ℕ ↦ (b n)⁻¹ * ∑ i ∈ range (n - 1),
      (b (i + 2) - b (i + 1)) * (S (i + 1) - s)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) hU
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (hb_pos n).le)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      (inv_nonneg.mpr (hb_pos n).le)
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [abs_mul, abs_of_nonneg (by linarith [hb_mono (by omega : i + 1 ≤ i + 2)])]
  -- `W n := (1/bₙ) ∑_{i<n-1}(b_{i+2}-b_{i+1}) S_{i+1} → s`.
  have hW : Tendsto (fun n : ℕ ↦ (b n)⁻¹ * ∑ i ∈ range (n - 1),
      (b (i + 2) - b (i + 1)) * S (i + 1)) atTop (𝓝 s) := by
    have hfirst : Tendsto (fun n : ℕ ↦ s * (1 - b 1 / b n)) atTop (𝓝 s) := by
      have hb1div : Tendsto (fun n : ℕ ↦ b 1 / b n) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using hbinv.const_mul (b 1)
      have : Tendsto (fun n : ℕ ↦ 1 - b 1 / b n) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub hb1div
      simpa using this.const_mul s
    have hcomb := hfirst.add hR
    rw [add_zero] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hbn0 : (b n) ≠ 0 := (hb_pos n).ne'
    have hexpand : ∑ i ∈ range (n - 1), (b (i + 2) - b (i + 1)) * S (i + 1)
        = (∑ i ∈ range (n - 1), (b (i + 2) - b (i + 1)) * (S (i + 1) - s))
          + s * (b n - b 1) := by
      rw [← htel n hn, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hexpand]
    field_simp
    ring
  -- Abel summation identity, then combine `Sₙ - Wₙ → s - s = 0`.
  have hAbel : ∀ n : ℕ, 1 ≤ n → (b n)⁻¹ * ∑ k ∈ range n, b (k + 1) * y k
      = S n - (b n)⁻¹ * ∑ i ∈ range (n - 1), (b (i + 2) - b (i + 1)) * S (i + 1) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hparts := Finset.sum_range_by_parts (fun i ↦ b (i + 1)) y (m + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at hparts
    rw [hparts, mul_sub, ← mul_assoc, inv_mul_cancel₀ (hb_pos (m + 1)).ne', one_mul]
    congr 2
  have hcomb : Tendsto (fun n : ℕ ↦ S n - (b n)⁻¹ * ∑ i ∈ range (n - 1),
      (b (i + 2) - b (i + 1)) * S (i + 1)) atTop (𝓝 (s - s)) := hy.sub hW
  rw [sub_self] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hAbel n hn).symm

/-- Kronecker's lemma with weights `k + 1`: if `∑_{k<n} x k` converges, then
`(1/n) ∑_{k<n} (k+1)·x k → 0`. This is the form used for the martingale SLLN, where
`x_k = ΔM_k / (k+1)` makes `∑_{k<n} (k+1)·x_k = M n` telescope.

It is the special case of `kronecker_general` with the positive nondecreasing weights
`b_k = max k 1` (equal to `k` for `k ≥ 1`, so `b (k+1) = k+1` and the divisor is `n` eventually). -/
lemma kronecker' {x : ℕ → ℝ} {s : ℝ}
    (hx : Tendsto (fun n ↦ ∑ k ∈ range n, x k) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ((k : ℝ) + 1) * x k) atTop (𝓝 0) := by
  have hb_pos : ∀ n : ℕ, 0 < max (n : ℝ) 1 := fun n ↦ lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb_mono : Monotone (fun n : ℕ ↦ max (n : ℝ) 1) :=
    fun a b h ↦ max_le_max (by exact_mod_cast h) le_rfl
  have hb_top : Tendsto (fun n : ℕ ↦ max (n : ℝ) 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_max_left _ _) tendsto_natCast_atTop_atTop
  have hG := kronecker_general (b := fun n ↦ max (n : ℝ) 1) (y := x) hb_pos hb_mono hb_top hx
  refine hG.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hbn : max (n : ℝ) 1 = (n : ℝ) := max_eq_left (by exact_mod_cast hn)
  have hbk : ∀ k : ℕ, max ((k + 1 : ℕ) : ℝ) 1 = (k : ℝ) + 1 := fun k ↦ by
    rw [Nat.cast_add, Nat.cast_one]
    exact max_eq_left (le_add_of_nonneg_left (Nat.cast_nonneg k))
  simp only [hbn, hbk]

/-- **Kronecker's lemma** (identity weights `b_k = k`). If the partial sums `∑_{k < n} x k`
converge to `s`, then `(1/n) ∑_{k < n} k · x k → 0`.

Since `∑_{k<n} k·x k = ∑_{k<n} (k+1)·x k - ∑_{k<n} x k`, this follows from `kronecker'` together
with `(1/n) ∑_{k<n} x k → 0` (the partial sums are bounded, being convergent). -/
lemma kronecker {x : ℕ → ℝ} {s : ℝ}
    (hx : Tendsto (fun n ↦ ∑ k ∈ range n, x k) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, (k : ℝ) * x k) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, x k) atTop (𝓝 0) := by
    simpa using hinv.mul hx
  have hsub : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ((k : ℝ) + 1) * x k
      - (n : ℝ)⁻¹ * ∑ k ∈ range n, x k) atTop (𝓝 0) := by
    simpa using (kronecker' hx).sub h2
  refine hsub.congr' (Eventually.of_forall fun n ↦ ?_)
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
  ring

end AlphaRAR
