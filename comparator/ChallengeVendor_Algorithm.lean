/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.HasLaw

/-! # Vendored from LML: `LeanMachineLearning.SequentialLearning.Algorithm`

Part of the comparator challenges (see `comparator/README.md`): the Palomar registry requires the
challenge import closure to bottom out in Mathlib, so the declarations of
[LML](https://github.com/LeanMachineLearning/LML) that the challenged statements depend on —
`Algorithm`, `Environment`, `history`, `IsAlgEnvSeq` — are copied here **verbatim** from that
module, in their original order and elaboration context. Comparator checks that the constants
this file produces are *identical* to the ones the project obtains from the LML package, so this
copy cannot silently drift from upstream. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {𝓐 𝓨 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω}

/-- A stochastic, sequential algorithm. -/
structure Algorithm (𝓐 𝓨 : Type*) [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] where
  /-- Policy or sampling rule: distribution of the next action. -/
  policy : (n : ℕ) → Kernel (Iic n → 𝓐 × 𝓨) 𝓐
  /-- The policy is a Markov kernel. -/
  [h_policy : ∀ n, IsMarkovKernel (policy n)]
  /-- Distribution of the first action. -/
  p0 : Measure 𝓐
  /-- The first action distribution is a probability measure. -/
  [hp0 : IsProbabilityMeasure p0]

instance (alg : Algorithm 𝓐 𝓨) (n : ℕ) : IsMarkovKernel (alg.policy n) := alg.h_policy n
instance (alg : Algorithm 𝓐 𝓨) : IsProbabilityMeasure alg.p0 := alg.hp0

/-- A stochastic environment. -/
structure Environment (𝓐 𝓨 : Type*) [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] where
  /-- Distribution of the next observation as function of the past history. -/
  feedback : (n : ℕ) → Kernel ((Iic n → 𝓐 × 𝓨) × 𝓐) 𝓨
  /-- The feedback kernels are Markov kernels. -/
  [h_feedback : ∀ n, IsMarkovKernel (feedback n)]
  /-- Distribution of the first observation given the first action. -/
  ν0 : Kernel 𝓐 𝓨
  /-- The initial observation kernel is a Markov kernel. -/
  [hp0 : IsMarkovKernel ν0]

instance (env : Environment 𝓐 𝓨) (n : ℕ) : IsMarkovKernel (env.feedback n) := env.h_feedback n
instance (env : Environment 𝓐 𝓨) : IsMarkovKernel env.ν0 := env.hp0

section IsAlgEnvSeq

variable {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨}
    {P : Measure Ω} [IsFiniteMeasure P] {N : ℕ}

/-- History of the algorithm-environment sequence up to time `n`. -/
def history (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (n : ℕ) (ω : Ω) : Iic n → 𝓐 × 𝓨 :=
  fun i ↦ (A i ω, Y i ω)

section IsAlgEnvSeq


/-- An algorithm-environment sequence: a sequence of actions and feedbacks generated
by an algorithm interacting with an environment. -/
structure IsAlgEnvSeq
    (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (alg : Algorithm 𝓐 𝓨) (env : Environment 𝓐 𝓨)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  /-- The action sequence is measurable. -/
  measurable_action n : Measurable (A n) := by fun_prop
  /-- The feedback sequence is measurable. -/
  measurable_feedback n : Measurable (Y n) := by fun_prop
  /-- The first action has the correct law. -/
  hasLaw_action_zero : HasLaw (fun ω ↦ (A 0 ω)) alg.p0 P
  /-- The first feedback has the correct conditional distribution. -/
  hasCondDistrib_feedback_zero : HasCondDistrib (Y 0) (A 0) env.ν0 P
  /-- The next action has the correct conditional distribution given the history. -/
  hasCondDistrib_action n :
    HasCondDistrib (A (n + 1)) (history A Y n) (alg.policy n) P
  /-- The next feedback has the correct conditional distribution given the history and
  next action. -/
  hasCondDistrib_feedback n :
    HasCondDistrib (Y (n + 1)) (fun ω ↦ (history A Y n ω, A (n + 1) ω))
      (env.feedback n) P

end IsAlgEnvSeq

end IsAlgEnvSeq

end Learning
