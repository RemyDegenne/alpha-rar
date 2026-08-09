/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A positive-part convergence lemma

This file formalizes the analytic convergence lemma from the technical appendix
of the paper *On Response-Adaptive Targeting Strategies for Multi-Treatment
Experiments* (Yagouti, Degenne, Kaufmann).

If `X n / n → -α v` with `α, v ∈ [0,1]`, and `a n ≤ n` is non-decreasing, then
for any error sequence `ε n` whose limsup is `≤ 0`, the positive part of
`ε n + (X n - X (a n)) / n` tends to `0`. The point is that the "backward"
contribution `- X (a n) / n` cannot exceed `α v` asymptotically, so the whole
expression is asymptotically `≤ 0`.

## Main result

* `AlphaRAR.tendsto_posPart_sub_div`.

## Blueprint reference

Lemma `lem:convergence` in the technical chapter of the blueprint. The hypothesis
`limsup ε ≤ 0` is formalized in its operational form `∀ δ > 0, ∀ᶠ n, ε n < δ`.
-/

@[expose] public section

open Filter Topology Finset

namespace AlphaRAR

/-- **Positive-part convergence** (blueprint `lem:convergence`).

Let `a` be non-decreasing with `a n ≤ n`, let `α, v ∈ [0,1]`, and let `X` satisfy
`X n / n → -(α v)`. Then for any `ε` with `∀ δ > 0, ∀ᶠ n, ε n < δ` (the meaning
of `limsup ε ≤ 0`),
`max (ε n + (X n - X (a n)) / n) 0 → 0`.

The blueprint states this with `a` non-decreasing, but the argument only needs
`a n ≤ n`, so the monotonicity hypothesis is dropped here. -/
lemma tendsto_posPart_sub_div {a : ℕ → ℕ} {X ε : ℕ → ℝ} {α v : ℝ}
    (ha_le : ∀ n, a n ≤ n)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hX : Tendsto (fun n ↦ X n / (n : ℝ)) atTop (𝓝 (-(α * v))))
    (hε : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ε n < δ) :
    Tendsto (fun n ↦ max (ε n + (X n - X (a n)) / (n : ℝ)) 0) atTop (𝓝 0) := by
  let L := α * v
  have hL0 : 0 ≤ L := mul_nonneg hα.1 hv.1
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · -- lower bound: the positive part is always `≥ 0 > b`
    exact Filter.Eventually.of_forall fun n ↦ lt_of_lt_of_le hb (le_max_right _ _)
  · -- upper bound: for `b > 0`, eventually the inside is `< b`
    set δ := b / 3 with hδdef
    have hδ : (0 : ℝ) < δ := by rw [hδdef]; linarith
    have E1 : ∀ᶠ n in atTop, ε n < δ := hε δ hδ
    have E2 : ∀ᶠ n in atTop, X n / (n : ℝ) < -L + δ :=
      (tendsto_order.1 hX).2 (-L + δ) (by linarith)
    -- the crux: the backward term is eventually below `L + δ`
    have E3 : ∀ᶠ n in atTop, -(X (a n)) / (n : ℝ) < L + δ := by
      have hev : ∀ᶠ m in atTop, -L - δ < X m / (m : ℝ) :=
        (tendsto_order.1 hX).1 (-L - δ) (by linarith)
      obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
      have hne : (range (N0 + 1)).Nonempty := nonempty_range_iff.mpr (Nat.succ_ne_zero N0)
      set B := (range (N0 + 1)).sup' hne (fun m ↦ |X m|) with hBdef
      have hbound : ∀ m ∈ range (N0 + 1), |X m| ≤ B := by
        intro m hm; rw [hBdef]; exact le_sup' (fun m ↦ |X m|) hm
      have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hbound 0 (mem_range.mpr (Nat.succ_pos N0)))
      filter_upwards [eventually_ge_atTop 1, eventually_gt_atTop (Nat.ceil (B / δ))]
        with n hn1 hnc
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hLδ0 : 0 ≤ L + δ := by linarith
      have hfinal : -(X (a n)) < (L + δ) * (n : ℝ) := by
        rcases lt_or_ge (a n) (N0 + 1) with hlt | hge
        · -- short index: `X (a n)` is bounded by `B`
          have hb1 : |X (a n)| ≤ B := hbound (a n) (mem_range.mpr hlt)
          have hb2 : -(X (a n)) ≤ B := by
            have h := le_abs_self (-(X (a n)))
            rw [abs_neg] at h
            linarith
          have hceil : B / δ < (n : ℝ) :=
            lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hnc)
          have hBn : B < δ * (n : ℝ) := by rw [mul_comm]; exact (div_lt_iff₀ hδ).1 hceil
          calc -(X (a n)) ≤ B := hb2
            _ < δ * (n : ℝ) := hBn
            _ ≤ (L + δ) * (n : ℝ) := by
                apply mul_le_mul_of_nonneg_right _ (le_of_lt hnpos); linarith
        · -- long index: use the asymptotics of `X m / m`
          have hkpos : (0 : ℝ) < (a n : ℝ) := by
            have : 1 ≤ a n := by omega
            exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
          have hstep : -L - δ < X (a n) / (a n : ℝ) := hN0 (a n) (by omega)
          have hmul : (-L - δ) * (a n : ℝ) < X (a n) := (lt_div_iff₀ hkpos).1 hstep
          have hkn : (a n : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha_le n
          calc -(X (a n)) < (L + δ) * (a n : ℝ) := by
                have hr : (L + δ) * (a n : ℝ) = -((-L - δ) * (a n : ℝ)) := by ring
                linarith
            _ ≤ (L + δ) * (n : ℝ) := mul_le_mul_of_nonneg_left hkn hLδ0
      exact (div_lt_iff₀ hnpos).2 hfinal
    -- combine the three bounds
    filter_upwards [E1, E2, E3, eventually_ge_atTop 1] with n h1 h2 h3 hn1
    have hsplit : (X n - X (a n)) / (n : ℝ) = X n / n - X (a n) / n := sub_div _ _ _
    have h3δ : 3 * δ = b := by rw [hδdef]; ring
    have heq : -(X (a n)) / (n : ℝ) = -(X (a n) / (n : ℝ)) := neg_div _ _
    refine max_lt ?_ hb
    rw [hsplit]
    grind

end AlphaRAR
