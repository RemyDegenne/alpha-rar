/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.HasCondDistrib
public import LeanMachineLearning.SequentialLearning.FiniteActions
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# The feedback of an algorithm–environment sequence in a stationary environment

In a **stationary environment** with per-arm reward kernel `ν : Kernel 𝓐 ℝ`, the response of a
round assigned to arm `a` is drawn from `ν a`, independently of the past given the arm. Two
consequences are recorded here:

* `condExp_feedback_comp` — the conditional law of the response given the history *and the current
  action* is `ν (A n)`, so `𝔼[g (Y n) | 𝒢 n] = (ν (A n))[g]`. This is the crux behind every
  response martingale: the fresh randomness of a step is the response, revealed *after* the arm is
  chosen.
* `memLp_feedback` — with finitely many arms, `Y n ∈ L²` as soon as every `ν a` is.

Nothing here is specific to any particular design; these are statements about
`Learning.IsAlgEnvSeq` under `Learning.stationaryEnv` and belong upstream with them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning

open scoped ENNReal

namespace Learning.IsAlgEnvSeq

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- **The response is in `L²` as soon as every arm's reward distribution is** (Condition **A**).
With finitely many arms the second moments `∫ x² dν a` have a finite maximum, and the response's
conditional law given the chosen arm is `ν (A n)`; so `hY2` need not be assumed alongside `hνk`.

The two cases of `n` mirror `condExp_feedback_comp`: at `n = 0` the conditional distribution is `ν`
given `A 0`, and at `n = m+1` it is `ν.prodMkLeft` given the history together with `A (m+1)`. -/
lemma memLp_feedback [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) (n : ℕ) :
    MemLp (Y n) 2 P := by
  classical
  letI := Fintype.ofFinite 𝓐
  -- A uniform bound on the arms' second moments.
  set C : ℝ≥0∞ := ∑ a : 𝓐, ∫⁻ y, ‖y‖ₑ ^ 2 ∂(ν a) with hCdef
  have hone : ∀ a : 𝓐, ∫⁻ y, ‖y‖ₑ ^ 2 ∂(ν a) ≠ ⊤ := by
    intro a
    have hfin := (hνk a).integrable_sq.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hfin
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hfin)
    exact lintegral_congr fun y ↦ by rw [enorm_pow]
  have hC : C ≠ ⊤ := by
    rw [hCdef]
    exact (ENNReal.sum_lt_top.mpr fun a _ ↦ (hone a).lt_top).ne
  have hb : ∀ a : 𝓐, ∫⁻ y, ‖y‖ₑ ^ 2 ∂(ν a) ≤ C :=
    fun a ↦ Finset.single_le_sum (f := fun a ↦ ∫⁻ y, ‖y‖ₑ ^ 2 ∂(ν a))
      (fun _ _ ↦ zero_le) (Finset.mem_univ a)
  have hmeas : AEStronglyMeasurable (Y n) P := (h.measurable_feedback n).aestronglyMeasurable
  cases n with
  | zero =>
    have hcd : HasCondDistrib (Y 0) (A 0) ν P := by
      have hf := h.hasCondDistrib_feedback_zero
      rwa [ν0_stationaryEnv] at hf
    exact memLp_two_of_hasCondDistrib hC hcd hmeas hb
  | succ m =>
    have hcd : HasCondDistrib (Y (m + 1)) (fun ω ↦ (history A Y m ω, A (m + 1) ω))
        (ν.prodMkLeft _) P := by
      have hf := h.hasCondDistrib_feedback m
      rwa [feedback_stationaryEnv] at hf
    refine memLp_two_of_hasCondDistrib hC hcd hmeas fun p ↦ ?_
    rw [Kernel.prodMkLeft_apply]
    exact hb p.2

/-- **Conditional expectation of a function of the feedback.**
Under a stationary environment with per-arm reward kernel `ν`, the conditional
expectation of `g (Y n)` given the action-augmented filtration `filtrationAction n`
(the history up to `n-1` together with the current action `A n`) is the integral of `g`
against the chosen arm's reward distribution, `∫ x, g x ∂(ν (A n))`. This is the crux behind
the response martingale (and its quadratic variation): the fresh randomness of a step is the
response, revealed *after* the arm is chosen. The base case `n = 0` (conditioning on just
`σ(A 0)`, initial kernel `ν0 = ν`) and the step `n = m+1` (conditioning on the history and
`A (m+1)`, step kernel `ν.prodMkLeft`) are treated separately. -/
lemma condExp_feedback_comp (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ)
    {g : ℝ → ℝ} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y n ω)) P) :
    P[fun ω ↦ g (Y n ω) |
        IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback n]
      =ᵐ[P] fun ω ↦ (ν (A n ω))[g] := by
  cases n with
  | zero =>
    have hX : Measurable (A 0) := h.measurable_action 0
    have hcd : HasCondDistrib (Y 0) (A 0) ν P := by
      have hf := h.hasCondDistrib_feedback_zero
      rwa [ν0_stationaryEnv] at hf
    rw [IsAlgEnvSeq.filtrationAction_zero_eq_comap]
    exact hcd.condExp_comp_eq hX hg hint
  | succ m =>
    have hX : Measurable (fun ω ↦ (history A Y m ω, A (m + 1) ω)) :=
      (h.measurable_history m).prodMk (h.measurable_action (m + 1))
    have hcd : HasCondDistrib (Y (m + 1)) (fun ω ↦ (history A Y m ω, A (m + 1) ω))
        (ν.prodMkLeft _) P := by
      have hf := h.hasCondDistrib_feedback m
      rwa [feedback_stationaryEnv] at hf
    rw [IsAlgEnvSeq.filtrationAction_eq_comap (m + 1) (Nat.succ_ne_zero m)]
    refine (hcd.condExp_comp_eq hX hg hint).trans ?_
    filter_upwards with ω
    rw [Kernel.prodMkLeft_apply]

/-- **Conditional expectation of the feedback is the mean of the arm's reward kernel.**
Under a stationary environment with per-arm reward kernel `ν`, the conditional expectation of
the response `Y n` given the action-augmented filtration `filtrationAction n` is the mean
`(ν (A n))[id]` of the chosen arm's reward distribution. This is the `g = id` case of
`condExp_feedback_comp`. -/
lemma condExp_feedback (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ)
    (hint : Integrable (Y n) P) :
    P[Y n | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback n]
      =ᵐ[P] fun ω ↦ (ν (A n ω))[id] :=
  condExp_feedback_comp h n stronglyMeasurable_id hint

end Learning.IsAlgEnvSeq
