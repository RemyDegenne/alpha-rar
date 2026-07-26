/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.MartingaleIncrement
import AlphaRAR.YDK2026.Response

/-!
# `o_p` increment bounds for the response martingale `Q`

Instantiating the generic martingale-family increment bounds (`AlphaRAR.isLittleOpOne_vmaxSeq`,
`AlphaRAR.isLittleOpOne_wmaxSeq_div_sqrt`) for the family `Q_k = respMart ν A Y k`, using the
per-arm martingale/integrability facts and the increment second-moment bound
`∫ (ΔQ_k)² ≤ Var[id; ν k] ≤ ∑_j Var[id; ν j]`.

## Main result

* `AlphaRAR.qm_increments_resp`: `vmaxSeq Q = o_p(1)` and `wmaxSeq Q = o_p(√n)`, the probabilistic
  half of blueprint `lem:QM_increments` for `Q`.
-/

open MeasureTheory ProbabilityTheory Filter Learning
open scoped ENNReal Topology

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [Fintype 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- **The response-martingale increment maxima are `o_p(1)` and `o_p(√n)`** (probabilistic core of
blueprint `lem:QM_increments` for `Q`). For each window the deterministic increment control is
`AlphaRAR.norm_increment_le_vmaxSeq_wmaxSeq`. -/
theorem qm_increments_resp (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) :
    IsLittleOpOne P (vmaxSeq (fun k ↦ respMart ν A Y k)) ∧
      IsLittleOpOne P
        (fun n ω ↦ wmaxSeq (fun k ↦ respMart ν A Y k) n ω / √n) := by
  set ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback with hℱdef
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  have hMfam : ∀ k, Martingale (respMart ν A Y k) ℱ P := fun k ↦ martingale_respMart h hint k
  have hM2fam : ∀ k n, Integrable (fun ω ↦ respMart ν A Y k n ω ^ 2) P :=
    fun k n ↦ (memLp_respMart h.measurable_action hY2 k n).integrable_sq
  have hcent2 : ∀ k n, Integrable (fun ω ↦ (Y n ω - (ν k)[id]) ^ 2) P :=
    fun k n ↦ ((hY2 n).sub (memLp_const _)).integrable_sq
  have hd2fam : ∀ k n,
      Integrable (fun ω ↦ (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2) P :=
    fun k n ↦ by
      have heq : (fun ω ↦ (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2)
          = fun ω ↦ (armIndicator A k n ω * (Y n ω - (ν k)[id])) ^ 2 := by
        funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
      rw [heq]; exact integrable_respMart_increment_sq k (h.measurable_action n) (hcent2 k n)
  have hcrossfam : ∀ k a b, Integrable (fun ω ↦ respMart ν A Y k a ω * respMart ν A Y k b ω) P :=
    fun k a b ↦ (memLp_respMart h.measurable_action hY2 k a).integrable_mul
      (memLp_respMart h.measurable_action hY2 k b)
  have harmnn : ∀ k, 0 ≤ Var[id; ν k] := fun k ↦ variance_nonneg _ _
  have hC₀ : 0 ≤ ∑ k, Var[id; ν k] := Finset.sum_nonneg (fun k _ ↦ harmnn k)
  have hincfam : ∀ k n, ∫ ω, (respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω) ^ 2 ∂P
      ≤ ∑ k, Var[id; ν k] := fun k n ↦ (integral_respMart_increment_sq_le h k n (hY2 n)).trans
    (Finset.single_le_sum (fun k' _ ↦ harmnn k') (Finset.mem_univ k))
  exact ⟨isLittleOpOne_vmaxSeq (M := fun k ↦ respMart ν A Y k)
      hMfam hM2fam hd2fam hcrossfam hC₀ hincfam,
    isLittleOpOne_wmaxSeq_div_sqrt (M := fun k ↦ respMart ν A Y k)
      hMfam hM2fam hd2fam hcrossfam hC₀ hincfam⟩

end AlphaRAR
