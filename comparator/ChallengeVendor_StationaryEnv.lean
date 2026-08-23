/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import ChallengeVendor_Algorithm

/-! # Vendored from LML: `LeanMachineLearning.SequentialLearning.StationaryEnv`

Part of the comparator challenges (see `comparator/README.md`): `obliviousEnv` and
`stationaryEnv`, copied **verbatim** from that LML module so that the challenge import closure
bottoms out in Mathlib. Comparator checks the constants (including the auxiliary `_proof_*`
constants abstracted from `obliviousEnv`'s instance fields) are identical to the LML package's. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}

/-- An oblivious environment, in which the distribution of the next feedback depends only on
the last action, but in a possibly time-dependent manner. -/
@[simps]
def obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] : Environment 𝓐 𝓨 where
  feedback n := (ν (n + 1)).prodMkLeft _
  ν0 := ν 0

/-- A stationary environment, in which the distribution of the next feedback depends only on the
last action. -/
def stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] : Environment 𝓐 𝓨 := obliviousEnv fun _ ↦ ν

end Learning
