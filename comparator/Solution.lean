/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.YDK2026.ARTSRates
import AlphaRAR.YDK2026.ARTSNormality
import AlphaRAR.YDK2026.PropDevARTS
import AlphaRAR.YDK2026.PropDevLIL
import AlphaRAR.YDK2026.ForcedExploration

/-! # Comparator solution module

The solution side of the [comparator](https://github.com/leanprover/comparator) setup in
`comparator/`: this module imports the project files proving the headline results listed in
`formalization.yaml`, so its environment contains, at the exact names stated (with `sorry`) in
the `comparator/Challenge_*.lean` files:

* `AlphaRAR.aRTS_LLN`,
* `AlphaRAR.aRTS_clt_joint` (and `AlphaRAR.measurable_jointSqrtNVec`),
* `AlphaRAR.aRTS_prop_dev`,
* `AlphaRAR.aRTS_prop_dev_ae`,
* `AlphaRAR.aRTSFE_sparse_clt_of_contDiffAt` (and `AlphaRAR.measurable_estimatorErrorVec`),
* `AlphaRAR.aRTSFE_sparse_rate_of_isARTSFE`.

Nothing is restated here: comparator compares the challenge statements against this
environment's constants and replays the proofs through the kernel. See `comparator/README.md`.
-/
