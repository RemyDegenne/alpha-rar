/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.Tactic.Tendsto

/-!
# Regression tests for the `tendsto` tactic

Each `example` mirrors a hand-written limit-algebra idiom found in the project's asymptotic
proofs (see `AlphaRAR/Mathlib/StochasticOrder.lean`, `ResponseConsistency.lean`,
`LILLogLog.lean`, `ResponseCLT.lean`).
-/

open Filter Topology

namespace AlphaRAR.TendstoTest

-- Combine two `→ 0` hypotheses (`StochasticOrder.IsLittleOpOne.add`).
example (X Y : ℕ → ℝ) (hX : Tendsto X atTop (𝓝 0)) (hY : Tendsto Y atTop (𝓝 0)) :
    Tendsto (fun n ↦ X n + Y n) atTop (𝓝 0) := by tendsto

-- `const_mul` then `mul_zero` cleanup (`LILLogLog.lean:107`, `ResponseCLT.lean:302`).
example (a : ℝ) (h0 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2) / 2 ^ k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ ↦ a * (((k : ℝ) + 2) / 2 ^ k)) atTop (𝓝 0) := by tendsto

-- `add_zero` reconciliation.
example (X : ℕ → ℝ) (c : ℝ) (hX : Tendsto X atTop (𝓝 0)) :
    Tendsto (fun n ↦ X n + c) atTop (𝓝 c) := by tendsto

-- Mixed sums and products with general limit values (`ResponseConsistency` `hslln'.mul hratio`).
example (X Y : ℕ → ℝ) (a b : ℝ) (hX : Tendsto X atTop (𝓝 a)) (hY : Tendsto Y atTop (𝓝 b)) :
    Tendsto (fun n ↦ 3 * X n + X n * Y n) atTop (𝓝 (3 * a + a * b)) := by tendsto

-- Subtraction and negation.
example (X Y : ℕ → ℝ) (a b : ℝ) (hX : Tendsto X atTop (𝓝 a)) (hY : Tendsto Y atTop (𝓝 b)) :
    Tendsto (fun n ↦ -X n + (Y n - X n)) atTop (𝓝 (-a + (b - a))) := by tendsto

-- Division by a constant.
example (X : ℕ → ℝ) (a : ℝ) (hX : Tendsto X atTop (𝓝 a)) :
    Tendsto (fun n ↦ X n / 3) atTop (𝓝 (a / 3)) := by tendsto

-- `zero_mul` cleanup (`ResponseConsistency` `hmul; rw [zero_mul]`).
example (X Y : ℕ → ℝ) (b : ℝ) (hX : Tendsto X atTop (𝓝 0)) (hY : Tendsto Y atTop (𝓝 b)) :
    Tendsto (fun n ↦ X n * Y n) atTop (𝓝 0) := by tendsto

-- Atomic limit supplied as a hypothesis is threaded through the algebra.
example (X : ℕ → ℝ) (h : Tendsto (fun n ↦ (X n) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ 5 * (X n) ^ 2) atTop (𝓝 0) := by tendsto

end AlphaRAR.TendstoTest
