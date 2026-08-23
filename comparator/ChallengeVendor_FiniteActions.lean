/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import ChallengeVendor_Algorithm
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.BorelCantelli

/-! # Vendored from LML: `LeanMachineLearning.SequentialLearning.FiniteActions`

Part of the comparator challenges (see `comparator/README.md`): the pull-count and sum-of-rewards
bookkeeping definitions, copied **verbatim** from that LML module (with its Mathlib import
surface) so that the challenge import closure bottoms out in Mathlib. Comparator checks the
constants are identical to the LML package's. -/

@[expose] public section

open MeasureTheory Finset Learning

namespace Learning

variable {𝓐 R Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {mR : MeasurableSpace R} {mΩ : MeasurableSpace Ω}
  [DecidableEq 𝓐]
  {alg : Algorithm 𝓐 R} {env : Environment 𝓐 R}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {R' : ℕ → Ω → R}
  {a : 𝓐} {m n t : ℕ} {ω : Ω}

/-- Number of times action `a` was chosen up to time `t` (excluding `t`). -/
noncomputable
def pullCount (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : ℕ :=
  #(filter (fun s ↦ A s ω = a) (range t))

/-- Number of pulls of arm `a` up to (and including) time `n`.
This is the number of entries in `h` in which the arm is `a`. -/
noncomputable
def pullCount' (n : ℕ) (h : Iic n → 𝓐 × R) (a : 𝓐) := #{s | (h s).1 = a}

/-- Sum of rewards of arm `a` up to (and including) time `n`. -/
noncomputable
def sumRewards' (n : ℕ) (h : Iic n → 𝓐 × ℝ) (a : 𝓐) :=
  ∑ s, if (h s).1 = a then (h s).2 else 0

end Learning
