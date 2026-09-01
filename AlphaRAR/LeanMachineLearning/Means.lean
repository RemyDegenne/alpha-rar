/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.LeanMachineLearning.PullCount
public meta import Characterization

/-!
# The means of a kernel

## Main definitions

* `ProbabilityTheory.Kernel.means`: the means of a kernel `ν : Kernel 𝓐 𝓨` is the function
  `k ↦ (ν k)[id] : 𝓐 → 𝓨`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset

namespace ProbabilityTheory.Kernel

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]

/-- The means of a kernel. -/
noncomputable def means (ν : Kernel 𝓐 𝓨) (k : 𝓐) : 𝓨 := (ν k)[id]

@[specifies means "the defining formula, stated so that a reader never has to unfold the \
definition to know what the mean at `k` is"]
lemma means_apply (ν : Kernel 𝓐 𝓨) (k : 𝓐) : ν.means k = (ν k)[id] := rfl

end ProbabilityTheory.Kernel
