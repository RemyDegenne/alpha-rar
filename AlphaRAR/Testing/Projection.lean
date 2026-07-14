/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# The projection `I - s sᵀ`

For a unit vector `s` (`sᵀ s = 1`), the matrix `I - s sᵀ` is an orthogonal
projection: it is idempotent and symmetric. This is the linear-algebra core of the
Pearson chi-square calibration (blueprint `lem:projection`); the rank `K - 1`
statement is not formalized here.

## Main result

* `AlphaRAR.isProjection_one_sub_vecMulVec`.
-/

open Matrix

namespace AlphaRAR

/-- **`I - s sᵀ` is an orthogonal projection** (blueprint `lem:projection`).
For a unit vector `s` (`s ⬝ᵥ s = 1`), the matrix `1 - s sᵀ` is idempotent and
symmetric. (The rank `K - 1` claim of the blueprint is not formalized here.) -/
lemma isProjection_one_sub_vecMulVec {K : ℕ} (s : Fin K → ℝ) (hs : s ⬝ᵥ s = 1) :
    IsIdempotentElem (1 - vecMulVec s s) ∧ (1 - vecMulVec s s).IsSymm := by
  -- `(s sᵀ)(s sᵀ) = (sᵀ s) (s sᵀ) = s sᵀ`.
  have hmm : vecMulVec s s * vecMulVec s s = vecMulVec s s := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
    have hfac : ∀ k, s i * s k * (s k * s j) = s i * s j * (s k * s k) := fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hfac k), ← Finset.mul_sum]
    have : ∑ k, s k * s k = 1 := hs
    rw [this, mul_one]
  refine ⟨?_, ?_⟩
  · -- idempotent
    have hexp : (1 - vecMulVec s s) * (1 - vecMulVec s s)
        = 1 - vecMulVec s s - vecMulVec s s + vecMulVec s s * vecMulVec s s := by
      noncomm_ring
    rw [IsIdempotentElem, hexp, hmm]
    abel
  · -- symmetric
    change (1 - vecMulVec s s)ᵀ = 1 - vecMulVec s s
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_vecMulVec]

end AlphaRAR
