/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Filtration
public meta import LeanSpec

/-!
# The previous-index filtration

`ℱ.shiftDown` re-indexes a filtration by one step: `(ℱ.shiftDown) n = ℱ (n-1)`, with
`(ℱ.shiftDown) 0 = ⊥`. It is the filtration with respect to which the increment at step `n` is
*fresh*, and so the one a Doob decomposition of a step-`n` increment must be taken against.
-/

@[expose] public section

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

namespace MeasureTheory.Filtration

/-- **Previous-index filtration**: `(ℱ.shiftDown) n = ℱ (n-1)`, with `(ℱ.shiftDown) 0 = ⊥`
(the trivial σ-algebra). Applied to a history filtration it is the "history strictly before
step `n`". -/
def shiftDown (ℱ : Filtration ℕ m0) : Filtration ℕ m0 where
  seq n := match n with
    | 0 => ⊥
    | m + 1 => ℱ m
  mono' := monotone_nat_of_le_succ fun n ↦ by
    cases n with
    | zero => exact bot_le
    | succ m => exact ℱ.mono (Nat.le_succ m)
  le' n := by
    cases n with
    | zero => exact bot_le
    | succ m => exact ℱ.le m

/-- At time `0` there is no previous index, so the previous-index filtration is trivial. -/
@[simp, specifies shiftDown "fixes the base case, the one place where \"shift by one\" has to \
make a choice: step `0` sees no history at all rather than the history at step `0`"]
lemma shiftDown_zero (ℱ : Filtration ℕ m0) : ℱ.shiftDown 0 = ⊥ := rfl

/-- Away from `0` the previous-index filtration is the shift: `(ℱ.shiftDown) (n+1) = ℱ n`. -/
@[simp, specifies shiftDown "the shift itself, which together with `shiftDown_zero` determines \
every value of the filtration"]
lemma shiftDown_succ (ℱ : Filtration ℕ m0) (n : ℕ) : ℱ.shiftDown (n + 1) = ℱ n := rfl

/-- The previous-index filtration sits below the current one: `ℱ_{n-1} ≤ ℱ_n`. -/
lemma shiftDown_le_self (ℱ : Filtration ℕ m0) (n : ℕ) : ℱ.shiftDown n ≤ ℱ n := by
  cases n with
  | zero => exact bot_le
  | succ p => exact ℱ.mono (Nat.le_succ p)

end MeasureTheory.Filtration
