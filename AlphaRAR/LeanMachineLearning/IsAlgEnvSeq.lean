/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.LeanMachineLearning.Means
public import AlphaRAR.Mathlib.HasCondDistrib
public import LeanMachineLearning.SequentialLearning.FiniteActions
public import LeanMachineLearning.SequentialLearning.Means

/-!
# The feedback of an algorithm–environment sequence in a stationary environment

In a **stationary environment** with per-arm reward kernel `ν : Kernel 𝓐 ℝ`, the response of a
round assigned to arm `a` is drawn from `ν a`, independently of the past given the arm. Three
consequences are recorded here:

* `condExp_feedback_comp_stationaryEnv` — the conditional law of the response given the history
  *and the current action* is `ν (A n)`, so `𝔼[g (Y n) | 𝒢 n] = (ν (A n))[g]`. This is the crux
  behind every response martingale: the fresh randomness of a step is the response, revealed
  *after* the arm is chosen. It is the stationary-environment instance of the upstream
  `IsAlgEnvSeq.condExp_feedback_comp` (`env.feedback n (history, A (n+1))` is `ν (A (n+1))`) and
  `IsAlgEnvSeq.condExp_feedback_zero_comp`, with the two cases `n = 0` and `n = m+1` merged.
* `condExp_feedback_stationaryEnv` — its `g = id` case, `𝔼[Y n | 𝒢 n] = ν.means (A n)`.
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

/-- **The response is in `L²` as soon as every arm's reward distribution is** (the paper's
Condition **A**). With finitely many arms the second moments `∫ x² dν a` have a finite maximum,
and the response's conditional law given the chosen arm is `ν (A n)`; so an `L²` hypothesis on
`Y` need not be assumed alongside `hνk`.

The two cases of `n` mirror `condExp_feedback_comp_stationaryEnv`: at `n = 0` the conditional
distribution is `ν` given `A 0`, and at `n = m+1` it is `ν.prodMkLeft` given the history together
with `A (m+1)`. -/
lemma memLp_feedback [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) (n : ℕ) :
    MemLp (Y n) 2 P := by
  classical
  let := Fintype.ofFinite 𝓐
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

/-- **Conditional expectation of a function of the feedback given the history and the action.**
Under a stationary environment with per-arm reward kernel `ν`, the conditional
expectation of `g (Y n)` given the action-augmented filtration `filtrationAction n`
(the history up to `n-1` together with the current action `A n`) is the integral of `g`
against the chosen arm's reward distribution, `∫ x, g x ∂(ν (A n))`. This is the crux behind
the response martingale (and its quadratic variation): the fresh randomness of a step is the
response, revealed *after* the arm is chosen. The base case `n = 0` (conditioning on just
`σ(A 0)`, initial kernel `ν0 = ν`) is the upstream `condExp_feedback_zero_comp` and the step
`n = m+1` (conditioning on the history and `A (m+1)`, step kernel `ν.prodMkLeft`) is the upstream
`condExp_feedback_comp`; the stationary environment makes both kernels `ν`. -/
lemma condExp_feedback_comp_stationaryEnv (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ)
    {g : ℝ → ℝ} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y n ω)) P) :
    P[fun ω ↦ g (Y n ω) | h.filtrationAction n] =ᵐ[P] fun ω ↦ (ν (A n ω))[g] := by
  cases n with
  | zero =>
    refine (h.condExp_feedback_zero_comp hg hint).trans ?_
    filter_upwards with ω
    rw [ν0_stationaryEnv]
  | succ m =>
    refine (h.condExp_feedback_comp m hg hint).trans ?_
    filter_upwards with ω
    rw [feedback_stationaryEnv, Kernel.prodMkLeft_apply]

/-- **Conditional expectation of the feedback is the mean of the arm's reward kernel.**
Under a stationary environment with per-arm reward kernel `ν`, the conditional expectation of
the response `Y n` given the action-augmented filtration `filtrationAction n` is the mean
`ν.means (A n)` of the chosen arm's reward distribution. This is the `g = id` case of
`condExp_feedback_comp_stationaryEnv` (equivalently, the upstream `condExp_feedback` with
`means_stationaryEnv`). -/
lemma condExp_feedback_stationaryEnv (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ)
    (hint : Integrable (Y n) P) :
    P[Y n | h.filtrationAction n] =ᵐ[P] fun ω ↦ ν.means (A n ω) :=
  condExp_feedback_comp_stationaryEnv h n stronglyMeasurable_id hint

end Learning.IsAlgEnvSeq
