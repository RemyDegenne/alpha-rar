/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Increment control from maximal bounds

This file formalizes the deterministic "increment control" lemma from the
technical appendix of the paper *On Response-Adaptive Targeting Strategies for
Multi-Treatment Experiments* (Yagouti, Degenne, Kaufmann).

For a sequence `Q` valued in a seminormed group, the norm of an increment
`Q n - Q ℓ` is controlled by two maxima of "backward" increments `Q n - Q (n-m)`:
a scale-normalized one over the long range `L ≤ m ≤ n`, and an unnormalized one
over the short range `m < L`. This is a purely algebraic inequality used later to
turn maximal martingale bounds into pointwise increment bounds.

## Main result

* `AlphaRAR.norm_sub_le_increment_control`: the increment-control inequality.

## Blueprint reference

Lemma `lem:increment_control` in the technical chapter of the blueprint.
-/

open Finset

namespace AlphaRAR

/-- **Increment control from maximal bounds** (blueprint `lem:increment_control`).

For any sequence `Q` in a seminormed additive group, any `ℓ ≤ n` and any
`1 ≤ L < n`,
`‖Q n - Q ℓ‖ ≤ (n - ℓ) · max_{L ≤ m ≤ n} ‖Q n - Q (n-m)‖ / m + max_{m < L} ‖Q n - Q (n-m)‖`.

The two summands correspond to the "long" (`n - ℓ ≥ L`) and "short"
(`n - ℓ < L`) cases: exactly one of them carries the increment, the other being
nonnegative. -/
lemma norm_sub_le_increment_control {E : Type*} [SeminormedAddCommGroup E]
    (Q : ℕ → E) {ℓ n L : ℕ} (hℓ : ℓ ≤ n) (hL : 1 ≤ L) (hLn : L < n) :
    ‖Q n - Q ℓ‖
      ≤ ((n - ℓ : ℕ) : ℝ)
          * (Icc L n).sup' (nonempty_Icc.mpr hLn.le)
              (fun m => ‖Q n - Q (n - m)‖ / (m : ℝ))
        + (range L).sup' (nonempty_range_iff.mpr (Nat.one_le_iff_ne_zero.mp hL))
            (fun m => ‖Q n - Q (n - m)‖) := by
  -- Both maxima are nonnegative (each is a max of nonnegative reals).
  have hA0 : (0 : ℝ) ≤ (Icc L n).sup' (nonempty_Icc.mpr hLn.le)
      (fun m => ‖Q n - Q (n - m)‖ / (m : ℝ)) :=
    le_trans (by positivity)
      (le_sup' (fun m => ‖Q n - Q (n - m)‖ / (m : ℝ)) (mem_Icc.mpr ⟨le_rfl, hLn.le⟩))
  have hB0 : (0 : ℝ) ≤ (range L).sup' (nonempty_range_iff.mpr (Nat.one_le_iff_ne_zero.mp hL))
      (fun m => ‖Q n - Q (n - m)‖) :=
    le_trans (norm_nonneg _)
      (le_sup' (fun m => ‖Q n - Q (n - m)‖) (mem_range.mpr hL))
  -- The increment reaches `Q ℓ` as a backward step of size `n - ℓ` from `Q n`.
  have hd : n - (n - ℓ) = ℓ := Nat.sub_sub_self hℓ
  rcases lt_or_ge (n - ℓ) L with hlt | hge
  · -- Short increment `n - ℓ < L`: absorbed by the second maximum.
    have hle : ‖Q n - Q (n - (n - ℓ))‖ ≤ (range L).sup'
        (nonempty_range_iff.mpr (Nat.one_le_iff_ne_zero.mp hL))
        (fun m => ‖Q n - Q (n - m)‖) :=
      le_sup' (fun m => ‖Q n - Q (n - m)‖) (mem_range.mpr hlt)
    rw [hd] at hle
    have hnn : (0 : ℝ) ≤ ((n - ℓ : ℕ) : ℝ) * (Icc L n).sup' (nonempty_Icc.mpr hLn.le)
        (fun m => ‖Q n - Q (n - m)‖ / (m : ℝ)) := mul_nonneg (Nat.cast_nonneg _) hA0
    grind
  · -- Long increment `L ≤ n - ℓ`: absorbed by the (normalized) first maximum.
    have hle : ‖Q n - Q (n - (n - ℓ))‖ / ((n - ℓ : ℕ) : ℝ) ≤ (Icc L n).sup'
        (nonempty_Icc.mpr hLn.le) (fun m => ‖Q n - Q (n - m)‖ / (m : ℝ)) :=
      le_sup' (fun m => ‖Q n - Q (n - m)‖ / (m : ℝ)) (mem_Icc.mpr ⟨hge, Nat.sub_le n ℓ⟩)
    rw [hd] at hle
    have hdpos : (0 : ℝ) < ((n - ℓ : ℕ) : ℝ) := by
      have : 0 < n - ℓ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hL hge)
      exact_mod_cast this
    rw [div_le_iff₀ hdpos] at hle
    grind

end AlphaRAR
