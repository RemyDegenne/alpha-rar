/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.MartingaleCLT
public import AlphaRAR.YDK2026.ARTSConsistency
public import AlphaRAR.Mathlib.Tactic.Tendsto
public meta import LeanSpec

/-!
# The self-normalized central limit theorem for the response martingale

Applying the abstract martingale CLT (`AlphaRAR.MartDiffArray.mart_clt`) to the per-arm response
martingale `Q_{n,k} = ∑_{m<n} 𝟙{A m = k}(Y m - θ_k)`, we obtain the componentwise
self-normalized CLT (blueprint `cor:mart_clt_componentwise`, univariate form):
`Q_{n,k}/√(V_k N_{n,k}) ⇒ 𝒩(0,1)`, where `V_k = Var[id; ν k]` is the arm variance and
`N_{n,k} = ∑_{m<n} 𝟙{A m = k}` the assignment count.

The key device (which avoids the Anscombe / random-time-change argument) is to normalize by the
**deterministic** `a_n = V_k v_k n`, where `v_k` is the limiting proportion `N_{n,k}/n → v_k`. Then:

* the increments `d_i = 𝟙{A i = k}(Y i - θ_k)` form a martingale-difference sequence for the
  action-augmented filtration `𝒢` (`condExp_respMart_increment`), so `MartDiffArray.ofSeq`
  packages them into a triangular array with row sum `Q_{n,k}/√a_n`;
* the predictable variation is `N_{n,k}/(v_k n) → 1` in probability, from consistency
  (`predVar` ingredient);
* the conditional Lindeberg condition holds because the sampled responses are i.i.d. with finite
  variance: each cell contributes `𝟙{A i = k}·(a_n)⁻¹∫(x-θ_k)²𝟙{|x-θ_k|>ε√a_n} dν_k`, and the
  tail integral `→ 0` by dominated convergence (`tendsto_integral_sq_indicator_gt`).

The deterministic-normalizer CLT (`respMart_div_sqrt_tendsto_gaussianReal`) then gives
`Q_{n,k}/√(V_k v_k n) ⇒ 𝒩(0,1)`, and self-normalization by `√(v_k n/N_{n,k}) → 1`
(`tendsto_map_mul_of_tendstoInMeasure_one`) recovers the random-normalizer statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning

open scoped Topology

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- The `i`-th centered response-martingale increment of arm `k`:
`respIncr ν A Y k i ω = 𝟙{A i ω = k}(Y i ω - ν.means k)`. This is `Q_{k}(i+1) - Q_k i`. -/
noncomputable def respIncr (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (k : 𝓐) (i : ℕ) :
    Ω → ℝ :=
  fun ω ↦ actionIndicator A k i ω * (Y i ω - ν.means k)

omit [MeasurableSingletonClass 𝓐] [IsProbabilityMeasure P] in
/-- The partial sums of the increments are the response martingale:
`∑_{i<n} respIncr ν A Y k i = Q_{k} n`. -/
@[specifies respIncr "identifies the increment with `ΔQ_k` exactly — same indicator, same \
centring, same index — so the array built from `respIncr` has `respMart` for its partial sums"]
lemma sum_respIncr (k : 𝓐) (n : ℕ) :
    ∑ i ∈ Finset.range n, respIncr ν A Y k i = respMart ν A Y k n := by
  funext ω
  rw [Finset.sum_apply, respMart_apply]
  rfl

/-- Each increment is `𝒢 (i+1)`-strongly-measurable (the assignment `A i` and response `Y i` are
revealed by step `i+1`). -/
@[fun_prop]
lemma stronglyMeasurable_respIncr (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ) :
    StronglyMeasurable[h.filtrationAction (i + 1)] (respIncr ν A Y k i) := by
  have hAm := h.adapted_action_filtrationAction.measurable_le (Nat.lt_succ_self i).le
  have hYm := h.measurable_feedback_filtrationAction_of_lt (Nat.lt_succ_self i)
  exact (stronglyMeasurable_const.indicator (hAm (measurableSet_singleton k))).mul
    (hYm.stronglyMeasurable.sub stronglyMeasurable_const)

/-- Each increment is in `L²`: `memLp_respMart_increment` phrased in terms of `respIncr`. -/
lemma memLp_respIncr [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a))
    (k : 𝓐) (i : ℕ) : MemLp (respIncr ν A Y k i) 2 P :=
  memLp_respMart_increment k (h.measurable_action i) (h.memLp_feedback hνk i)

/-- The increments are martingale differences for `𝒢`: `condExp_respMart_increment` phrased in
terms of `respIncr`. -/
lemma condExp_respIncr [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a))
    (k : 𝓐) (i : ℕ) :
    P[respIncr ν A Y k i
        | h.filtrationAction i] =ᵐ[P] 0 :=
  condExp_respMart_increment h k i ((h.memLp_feedback hνk i).integrable one_le_two)

/-- The triangular martingale-difference array of arm `k`, normalized by the deterministic
`a_n = V_k v_k n`: row `n` is `d_0/√a_n, …, d_{n-1}/√a_n` with `d_i = 𝟙{A i = k}(Y i - θ_k)`. Its
row sum is `Q_{n,k}/√(V_k v_k n)`. -/
noncomputable def respArray [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) : MartDiffArray P :=
  MartDiffArray.ofSeq h.filtrationAction
    (respIncr ν A Y k) (fun n ↦ Var[id; ν k] * vk * n)
    (memLp_respIncr h hνk k) (condExp_respIncr h hνk k) (stronglyMeasurable_respIncr h k)

@[simp] lemma respArray_d [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) (n i : ℕ) :
    (respArray h hνk k vk).d n i
      = fun ω ↦ (√(Var[id; ν k] * vk * n))⁻¹ * respIncr ν A Y k i ω := rfl

@[simp] lemma respArray_filt [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) :
    (respArray h hνk k vk).𝓕
      = fun _ ↦ h.filtrationAction := rfl

@[simp] lemma respArray_k [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) :
    (respArray h hνk k vk).k = id := rfl

/-- The row sum of the array is `Q_{n,k}/√(V_k v_k n)`. -/
@[specifies respArray "the array is assembled so that its row sum is the self-normalized statistic \
`Q_{n,k}/√(V_k v_k n)` — the quantity the CLT is about"]
lemma rowSum_respArray [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) (n : ℕ) :
    (respArray h hνk k vk).rowSum n
      = fun ω ↦ (√(Var[id; ν k] * vk * n))⁻¹ * respMart ν A Y k n ω := by
  rw [respArray, MartDiffArray.rowSum_ofSeq]
  funext ω
  rw [← sum_respIncr k n]
  simp only [Finset.sum_apply]

/-- **The predictable variation of the array is `N_{n,k}/(v_k n)` (a.e.).** From `predVar_ofSeq`
(`= (a_n)⁻¹ ∑_{i<n} E[d_i²|𝒢 i]`) and the conditional second moment `E[d_i²|𝒢 i] = 𝟙{A i = k}·V_k`
(`condExp_respMart_increment_sq`), which sums to `V_k N_{n,k}`. -/
@[specifies respArray "explains the choice of normalizer `a_n = V_k v_k n`: it cancels the arm \
variance and leaves the predictable variation equal to `N_{n,k}/(v_k n)`, so the CLT hypothesis \
`predVar → 1` becomes exactly the allocation statement `N_{n,k}/n → v_k`"]
lemma predVar_respArray_ae [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) (hvk0 : 0 ≤ vk)
    (hVk0 : 0 ≤ Var[id; ν k]) (n : ℕ) :
    (respArray h hνk k vk).predVar n =ᵐ[P]
      fun ω ↦ (Var[id; ν k] * vk * n)⁻¹
        * (Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n) := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  have ha : ∀ n : ℕ, 0 ≤ Var[id; ν k] * vk * (n : ℝ) := fun n ↦
    mul_nonneg (mul_nonneg hVk0 hvk0) (Nat.cast_nonneg n)
  have h1 := MartDiffArray.predVar_ofSeq
    h.filtrationAction (respIncr ν A Y k)
    (fun n ↦ Var[id; ν k] * vk * n)
    (memLp_respIncr h hνk k) (condExp_respIncr h hνk k) (stronglyMeasurable_respIncr h k) ha n
  have hcondsq : ∀ i, P[fun ω ↦ (respIncr ν A Y k i ω) ^ 2
        | h.filtrationAction i] =ᵐ[P]
      fun ω ↦ actionIndicator A k i ω * Var[id; ν k] :=
    fun i ↦ condExp_respMart_increment_sq h k i hνk
  unfold respArray
  filter_upwards [h1, ae_all_iff.mpr hcondsq] with ω hω hcs
  rw [hω]
  congr 1
  calc ∑ i ∈ Finset.range n, (P[fun ω ↦ (respIncr ν A Y k i ω) ^ 2
          | h.filtrationAction i]) ω
      = ∑ i ∈ Finset.range n, actionIndicator A k i ω * Var[id; ν k] :=
        Finset.sum_congr rfl fun i _ ↦ hcs i
    _ = (∑ i ∈ Finset.range n, actionIndicator A k i ω) * Var[id; ν k] := by rw [← Finset.sum_mul]
    _ = Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n := by rw [count]; ring

/-- **Conditional expectation of an indicator-weighted function of the feedback.** For any
measurable `φ`, `E[𝟙{A i = k}·φ(Y i) | 𝒢 i] = 𝟙{A i = k}·∫ φ dν_k`: the assignment indicator is
`𝒢 i`-measurable and pulls out, and the response's conditional law given `𝒢 i` on `{A i = k}` is
`ν k`. This is the general form of `condExp_respMart_increment_sq` (which is the case
`φ = (·-θ_k)²`), used for the conditional Lindeberg quantity. -/
lemma condExp_indicator_comp (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (i : ℕ)
    {φ : ℝ → ℝ} (hφ : StronglyMeasurable φ) (hint : Integrable (fun ω ↦ φ (Y i ω)) P) :
    P[fun ω ↦ actionIndicator A k i ω * φ (Y i ω)
        | h.filtrationAction i] =ᵐ[P]
      fun ω ↦ actionIndicator A k i ω * ∫ x, φ x ∂(ν k) := by
  let G := h.filtrationAction i
  set c : Ω → ℝ := actionIndicator A k i with hc
  have hcG : StronglyMeasurable[G] c :=
    stronglyMeasurable_const.indicator
      ((h.adapted_action_filtrationAction i)
        (measurableSet_singleton k))
  have hcgint : Integrable (fun ω ↦ c ω * φ (Y i ω)) P := by
    have hform : (fun ω ↦ c ω * φ (Y i ω)) = {ω | A i ω = k}.indicator (fun ω ↦ φ (Y i ω)) := by
      funext ω
      simp only [hc, actionIndicator, Set.indicator]
      by_cases hω : ω ∈ {ω | A i ω = k} <;> simp [hω]
    rw [hform]
    exact hint.indicator (h.measurable_action i (measurableSet_singleton k))
  have hcondg : P[fun ω ↦ φ (Y i ω) | G] =ᵐ[P] fun ω ↦ (ν (A i ω))[φ] :=
    h.condExp_feedback_comp_stationaryEnv i hφ hint
  have hpull := condExp_mul_of_stronglyMeasurable_left hcG hcgint hint
  filter_upwards [hpull, hcondg] with ω hp hcg
  change P[c * fun ω ↦ φ (Y i ω) | G] ω = _
  rw [hp, Pi.mul_apply, hcg]
  rcases eq_or_ne (A i ω) k with hak | hak
  · rw [hak]
  · have hc0 : c ω = 0 := by
      rw [hc, actionIndicator, Set.indicator_of_notMem (by simpa using hak)]
    rw [hc0, zero_mul, zero_mul]

/-- **Closed form of the conditional Lindeberg quantity.** The array's Lindeberg sum at level `ε`
equals `(a_n)⁻¹ · h_n(ε) · N_{n,k}` (a.e.), where `a_n = V_k v_k n` and
`h_n(ε) = ∫ (x-θ_k)² 𝟙{|x-θ_k| > ε√a_n} dν_k` is the deterministic truncated second moment of arm
`k`. Each cell contributes `𝟙{A i = k}·(a_n)⁻¹ h_n(ε)` (`condExp_indicator_comp` with the truncated
square), and the indicators sum to `N_{n,k}`. -/
lemma lindeberg_respArray_ae [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) (hvk : 0 < vk) (hVk : 0 < Var[id; ν k])
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (respArray h hνk k vk).lindeberg n ε =ᵐ[P]
      fun ω ↦ (Var[id; ν k] * vk * n)⁻¹
        * (∫ x, {x | ε * √(Var[id; ν k] * vk * n) < |x - ν.means k|}.indicator
            (fun x ↦ (x - ν.means k) ^ 2) x ∂(ν k))
        * count (fun j ↦ actionIndicator A k j ω) n := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    filter_upwards with ω
    simp [MartDiffArray.lindeberg, respArray_k, count]
  · have han : 0 < Var[id; ν k] * vk * (n : ℝ) :=
      mul_pos (mul_pos hVk hvk) (by exact_mod_cast hn0)
    have hspos : 0 < √(Var[id; ν k] * vk * (n : ℝ)) := Real.sqrt_pos.mpr han
    have hs2 : √(Var[id; ν k] * vk * (n : ℝ)) ^ 2 = Var[id; ν k] * vk * (n : ℝ) :=
      Real.sq_sqrt han.le
    set θ := ν.means k with hθ
    set s := √(Var[id; ν k] * vk * (n : ℝ)) with hs
    set φ : ℝ → ℝ := {x | ε * s < |x - θ|}.indicator (fun x ↦ (x - θ) ^ 2) with hφ
    have hφsm : StronglyMeasurable φ :=
      (((continuous_id.sub continuous_const).pow 2).stronglyMeasurable).indicator
        (measurableSet_lt measurable_const ((measurable_id.sub measurable_const).abs))
    -- Per-cell conditional Lindeberg contribution.
    have hsummand : ∀ i, (P[{ω | ε < |(respArray h hνk k vk).d n i ω|}.indicator
          (fun ω ↦ ((respArray h hνk k vk).d n i ω) ^ 2)
          | h.filtrationAction i]) =ᵐ[P]
        fun ω ↦ (Var[id; ν k] * vk * (n : ℝ))⁻¹ * actionIndicator A k i ω * ∫ x, φ x ∂(ν k) := by
      intro i
      have hFi : {ω | ε < |(respArray h hνk k vk).d n i ω|}.indicator
            (fun ω ↦ ((respArray h hνk k vk).d n i ω) ^ 2)
          = fun ω ↦ (Var[id; ν k] * vk * (n : ℝ))⁻¹ * (actionIndicator A k i ω * φ (Y i ω)) := by
        funext ω
        simp only [respArray_d, ← hs]
        rcases eq_or_ne (A i ω) k with hak | hak
        · have hmemω : ω ∈ ({ω | A i ω = k} : Set Ω) := hak
          have hri : respIncr ν A Y k i ω = Y i ω - θ := by
            simp only [respIncr, actionIndicator, Set.indicator_of_mem hmemω, one_mul, hθ]
          have harm : actionIndicator A k i ω = 1 := by
            simp only [actionIndicator, Set.indicator_of_mem hmemω]
          have hcond : (ε < |s⁻¹ * (Y i ω - θ)|) ↔ (ε * s < |Y i ω - θ|) := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hspos.le), inv_mul_eq_div, lt_div_iff₀ hspos]
          rw [Set.indicator_apply]
          by_cases hc : ε * s < |Y i ω - θ|
          · rw [ite_eq_left (show ω ∈ {ω | ε < |s⁻¹ * respIncr ν A Y k i ω|} by
                rw [Set.mem_ofPred_eq, hri]; exact hcond.mpr hc), hri, harm, one_mul, hφ,
              Set.indicator_of_mem (show Y i ω ∈ {x | ε * s < |x - θ|} from hc),
              mul_pow, inv_pow, hs2]
          · rw [ite_eq_right (show ω ∉ {ω | ε < |s⁻¹ * respIncr ν A Y k i ω|} by
                rw [Set.mem_ofPred_eq, hri]; exact fun hh ↦ hc (hcond.mp hh)), harm, one_mul, hφ,
              Set.indicator_of_notMem (show Y i ω ∉ {x | ε * s < |x - θ|} from hc)]
            ring
        · have hnotmem : ω ∉ ({ω | A i ω = k} : Set Ω) := by simpa using hak
          have hri0 : respIncr ν A Y k i ω = 0 := by
            simp only [respIncr, actionIndicator, Set.indicator_of_notMem hnotmem, zero_mul]
          have harm0 : actionIndicator A k i ω = 0 := by
            simp only [actionIndicator, Set.indicator_of_notMem hnotmem]
          rw [Set.indicator_of_notMem (show ω ∉ {ω | ε < |s⁻¹ * respIncr ν A Y k i ω|} by
                rw [Set.mem_ofPred_eq, hri0, mul_zero, abs_zero]; exact not_lt.mpr hε.le),
            harm0, zero_mul, mul_zero]
      have hφint : Integrable (fun ω ↦ φ (Y i ω)) P := by
        have hcomp : (fun ω ↦ φ (Y i ω))
            = ((Y i) ⁻¹' {x | ε * s < |x - θ|}).indicator (fun ω ↦ (Y i ω - θ) ^ 2) := by
          funext ω
          rw [hφ]
          by_cases hmem : Y i ω ∈ {x | ε * s < |x - θ|}
          · rw [Set.indicator_of_mem hmem,
              Set.indicator_of_mem (show ω ∈ (Y i) ⁻¹' {x | ε * s < |x - θ|} from hmem)]
          · rw [Set.indicator_of_notMem hmem,
              Set.indicator_of_notMem (show ω ∉ (Y i) ⁻¹' {x | ε * s < |x - θ|} from hmem)]
        rw [hcomp]
        exact (((hY2 i).sub (memLp_const _)).integrable_sq).indicator
          ((h.measurable_feedback i)
            (measurableSet_lt measurable_const ((measurable_id.sub measurable_const).abs)))
      rw [hFi]
      have hconst := condExp_const_mul (P := P)
        (m := h.filtrationAction i)
        (Var[id; ν k] * vk * (n : ℝ))⁻¹ (fun ω ↦ actionIndicator A k i ω * φ (Y i ω))
      have hind := condExp_indicator_comp h k i hφsm hφint
      filter_upwards [hconst, hind] with ω h1 h2
      rw [h1, h2]; ring
    -- Assemble the sum.
    filter_upwards [ae_all_iff.mpr hsummand] with ω hω
    simp only [MartDiffArray.lindeberg, respArray_k, respArray_filt, id]
    rw [Finset.sum_congr rfl fun i _ ↦ hω i]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [show (∑ i ∈ Finset.range n, actionIndicator A k i ω)
        = count (fun j ↦ actionIndicator A k j ω) n from rfl]
    ring

/-- **The conditional Lindeberg condition holds** (the `lindeberg` hypothesis of `thm:mart_clt`).
Since `L_n(ε) = (a_n)⁻¹ h_n(ε) N_{n,k}` (a.e.) with `0 ≤ N_{n,k} ≤ n`, we have
`0 ≤ L_n(ε) ≤ h_n(ε)/(V_k v_k)`, and `h_n(ε) = ∫(x-θ)²𝟙{|x-θ|>ε√a_n} dν_k → 0` because `√a_n → ∞`
and `ν_k` has finite second moment (dominated convergence, `tendsto_integral_sq_indicator_gt`).
So `L_n(ε) → 0` a.s., hence in measure. -/
lemma tendstoInMeasure_lindeberg_respArray [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) (hvk : 0 < vk) (hVk : 0 < Var[id; ν k]) :
    ∀ ε, 0 < ε → TendstoInMeasure P (fun n ↦ (respArray h hνk k vk).lindeberg n ε) atTop 0 := by
  intro ε hε
  have ha_nn : ∀ n : ℕ, (0 : ℝ) ≤ Var[id; ν k] * vk * (n : ℝ) := fun n ↦
    mul_nonneg (mul_nonneg hVk.le hvk.le) (Nat.cast_nonneg n)
  have hcent2ν : MemLp (fun x ↦ x - ν.means k) 2 (ν k) := (hνk k).sub (memLp_const _)
  have hc : Tendsto (fun n : ℕ ↦ ε * √(Var[id; ν k] * vk * (n : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop hε
      (Real.tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (mul_pos hVk hvk)
        tendsto_natCast_atTop_atTop))
  -- Abbreviate the deterministic tail `T n = h_n(ε)`; `hT` is a definitional equality that lets us
  -- avoid comparing the (beta-unreduced) `∫` produced by `hDCT.comp` against the reduced form,
  -- which would loop the defeq checker on the Bochner integral `ν.means k`.
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, ∀ n, T n = ∫ x,
      {x | ε * √(Var[id; ν k] * vk * (n : ℝ)) < |x - ν.means k|}.indicator
        (fun x ↦ (x - ν.means k) ^ 2) x ∂(ν k) := ⟨_, fun n ↦ rfl⟩
  have htail : Tendsto T atTop (𝓝 0) := by
    have hDCT := tendsto_integral_sq_indicator_gt (P := ν k) (Z := fun x ↦ x - ν.means k)
      (measurable_id.sub_const _) hcent2ν
    have h0 : Tendsto (fun n : ℕ ↦ ∫ x,
      {x | ε * √(Var[id; ν k] * vk * (n : ℝ)) < |x - ν.means k|}.indicator
        (fun x ↦ (x - ν.means k) ^ 2) x ∂(ν k)) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using hDCT.comp hc
    exact Tendsto.congr (fun n ↦ (hT n).symm) h0
  have htail_nn : ∀ n : ℕ, (0 : ℝ) ≤ T n := fun n ↦ by
    rw [hT n]; exact integral_nonneg fun x ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) x
  have hb : Tendsto (fun n : ℕ ↦ (Var[id; ν k] * vk)⁻¹ * T n) atTop (𝓝 0) := by
    tendsto
  have hcount_meas : ∀ n, Measurable (fun ω ↦ count (fun j ↦ actionIndicator A k j ω) n) := by
    intro n
    simp only [count, actionIndicator]
    exact Finset.measurable_sum _ fun j _ ↦
      measurable_const.indicator ((h.measurable_action j) (measurableSet_singleton k))
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · exact ((measurable_const.mul (hcount_meas n)).aestronglyMeasurable).congr
      (lindeberg_respArray_ae h hνk k vk hvk hVk ε hε n).symm
  · filter_upwards [ae_all_iff.mpr (fun n ↦ lindeberg_respArray_ae h hνk k vk hvk hVk ε hε n)]
      with ω hω
    have hcnn : ∀ n, (0 : ℝ) ≤ count (fun j ↦ actionIndicator A k j ω) n := fun n ↦
      Finset.sum_nonneg fun j _ ↦ actionIndicator_nonneg A k j ω
    have hcle : ∀ n, count (fun j ↦ actionIndicator A k j ω) n ≤ (n : ℝ) := by
      intro n
      rw [count]
      calc ∑ j ∈ Finset.range n, actionIndicator A k j ω
          ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ ↦ actionIndicator_le_one A k j ω
        _ = (n : ℝ) := by simp
    have hgoal : Tendsto (fun n : ℕ ↦ (Var[id; ν k] * vk * (n : ℝ))⁻¹ * T n
        * count (fun j ↦ actionIndicator A k j ω) n) atTop (𝓝 0) := by
      refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hb
      · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (ha_nn n)) (htail_nn n)) (hcnn n)
      · have hkn : (0 : ℝ) ≤ (Var[id; ν k] * vk * (n : ℝ))⁻¹ * T n :=
          mul_nonneg (inv_nonneg.mpr (ha_nn n)) (htail_nn n)
        calc (Var[id; ν k] * vk * (n : ℝ))⁻¹ * T n * count (fun j ↦ actionIndicator A k j ω) n
            ≤ (Var[id; ν k] * vk * (n : ℝ))⁻¹ * T n * (n : ℝ) :=
              mul_le_mul_of_nonneg_left (hcle n) hkn
          _ ≤ (Var[id; ν k] * vk)⁻¹ * T n := by
              rcases Nat.eq_zero_or_pos n with h0 | h0
              · subst h0
                simp only [Nat.cast_zero, mul_zero]
                exact mul_nonneg (inv_nonneg.mpr (mul_nonneg hVk.le hvk.le)) (htail_nn 0)
              · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
                apply le_of_eq
                field_simp
    exact Tendsto.congr (fun n ↦ by rw [hT n]; exact (hω n).symm) hgoal

/-- **The predictable variation converges to `1` in probability** (the `predVar` hypothesis of
`thm:mart_clt`). Since `predVar n = N_{n,k}/(v_k n)` (a.e.) and `N_{n,k}/n → v_k` a.s.
(consistency), we get `predVar n → 1` a.s., hence in measure. -/
lemma tendstoInMeasure_predVar_respArray [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) (hvk : 0 < vk) (hVk : 0 < Var[id; ν k])
    (hNconv : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ)) atTop (𝓝 vk)) :
    TendstoInMeasure P (fun n ↦ (respArray h hνk k vk).predVar n) atTop (fun _ ↦ (1 : ℝ)) := by
  have hV0 : Var[id; ν k] ≠ 0 := hVk.ne'
  have hvk0 : vk ≠ 0 := hvk.ne'
  have hcount_meas : ∀ n, Measurable (fun ω ↦ count (fun j ↦ actionIndicator A k j ω) n) := by
    intro n
    simp only [count, actionIndicator]
    exact Finset.measurable_sum _ fun j _ ↦
      measurable_const.indicator ((h.measurable_action j) (measurableSet_singleton k))
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · exact ((measurable_const.mul
      (measurable_const.mul (hcount_meas n))).aestronglyMeasurable).congr
      (predVar_respArray_ae h hνk k vk hvk.le hVk.le n).symm
  · have hae := ae_all_iff.mpr (fun n ↦ predVar_respArray_ae h hνk k vk hvk.le hVk.le n)
    filter_upwards [hae, hNconv] with ω hpred hconv
    refine Tendsto.congr (fun n ↦ (hpred n).symm) ?_
    have hlim : Tendsto (fun n ↦ count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ) * vk⁻¹) atTop
        (𝓝 (vk * vk⁻¹)) := hconv.mul_const vk⁻¹
    rw [mul_inv_cancel₀ hvk0] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

/-- The assignment count `N_{n,k}` is measurable in `ω`. -/
@[fun_prop]
lemma measurable_count_actionIndicator (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (n : ℕ) :
    Measurable (fun ω ↦ count (fun j ↦ actionIndicator A k j ω) n) := by
  simp only [count]
  exact Finset.measurable_sum _ fun j _ ↦ measurable_actionIndicator k (h.measurable_action j)

/-- Each `Q_{n,k}` is measurable (a finite sum of measurable increments). -/
@[fun_prop]
lemma measurable_respMart (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (n : ℕ) :
    Measurable (respMart ν A Y k n) := by
  have heq : respMart ν A Y k n = fun ω ↦ ∑ i ∈ Finset.range n, respIncr ν A Y k i ω := by
    funext ω; rw [← sum_respIncr k n, Finset.sum_apply]
  rw [heq]
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_const.indicator ((h.measurable_action i) (measurableSet_singleton k))).mul
      ((h.measurable_feedback i).sub measurable_const)

/-- **The deterministic-normalizer central limit theorem for the response martingale**
(blueprint `cor:mart_clt_componentwise`, per-arm deterministic form). Normalizing `Q_{n,k}` by the
*deterministic* `√(V_k v_k n)` (with `v_k` the limiting assignment proportion), the law of
`Q_{n,k}/√(V_k v_k n)` converges weakly to the standard Gaussian `𝒩(0,1)`. This is
`AlphaRAR.MartDiffArray.mart_clt` applied to `respArray`, whose predictable variation tends to `1`
(`tendstoInMeasure_predVar_respArray`) and which satisfies the conditional Lindeberg condition
(`tendstoInMeasure_lindeberg_respArray`). -/
lemma respMart_div_sqrt_tendsto_gaussianReal [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) (hvk : 0 < vk) (hVk : 0 < Var[id; ν k])
    (hNconv : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ)) atTop (𝓝 vk)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦
          (√(Var[id; ν k] * vk * (n : ℝ)))⁻¹ * respMart ν A Y k n ω),
        Measure.isProbabilityMeasure_map
          (measurable_const.mul (measurable_respMart h k n)).aemeasurable⟩ : ProbabilityMeasure ℝ))
      atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have hmart := (respArray h hνk k vk).mart_clt (σ2 := 1) zero_le_one
    (tendstoInMeasure_predVar_respArray h hνk k vk hvk hVk hNconv)
    (tendstoInMeasure_lindeberg_respArray h hνk k vk hvk hVk)
  simp only [rowSum_respArray, Real.toNNReal_one] at hmart
  exact hmart

/-- **The self-normalized componentwise CLT for the response martingale** (blueprint
`cor:mart_clt_componentwise`, per-arm form). The law of `Q_{n,k}/√(V_k N_{n,k})` — the response
martingale normalized by the *random* observed variation `√(V_k N_{n,k})` — converges weakly to the
standard Gaussian `𝒩(0,1)`. This follows from the deterministic-normalizer CLT
(`respMart_div_sqrt_tendsto_gaussianReal`) and Slutsky
(`tendsto_map_mul_of_tendstoInMeasure_one`), since the ratio
`√(V_k v_k n)/√(V_k N_{n,k}) = √(v_k n/N_{n,k}) → 1` in probability (from `N_{n,k}/n → v_k`). -/
lemma respMart_selfNorm_tendsto_gaussianReal [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (k : 𝓐) (vk : ℝ) (hvk : 0 < vk) (hVk : 0 < Var[id; ν k])
    (hNconv : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ)) atTop (𝓝 vk)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦
          (√(Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n))⁻¹
            * respMart ν A Y k n ω),
        Measure.isProbabilityMeasure_map
          ((((measurable_const.mul (measurable_count_actionIndicator h k n)).sqrt).inv).mul
            (measurable_respMart h k n)).aemeasurable⟩ : ProbabilityMeasure ℝ))
      atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have hRmeas : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(Var[id; ν k] * vk * (n : ℝ))
      * (√(Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n))⁻¹) P :=
    fun n ↦ (measurable_const.mul
      (((measurable_const.mul (measurable_count_actionIndicator h k n)).sqrt).inv)).aemeasurable
  -- The self-normalizing ratio `√(V_k v_k n)/√(V_k N_{n,k}) → 1` in probability.
  have hRtendsto : TendstoInMeasure P (fun (n : ℕ) ω ↦ √(Var[id; ν k] * vk * (n : ℝ))
      * (√(Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n))⁻¹) atTop
      (fun _ ↦ (1 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hRmeas n).aestronglyMeasurable) ?_
    filter_upwards [hNconv] with ω hconv
    have hsqvk : (0 : ℝ) < √vk := Real.sqrt_pos.mpr hvk
    have hcnn : ∀ n, (0 : ℝ) ≤ count (fun j ↦ actionIndicator A k j ω) n := fun n ↦
      Finset.sum_nonneg fun j _ ↦ actionIndicator_nonneg A k j ω
    have hr : Tendsto (fun n ↦ √vk
        * (√(count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ)))⁻¹) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n ↦ √(count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ)))
          atTop (𝓝 (√vk)) := (Real.continuous_sqrt.tendsto vk).comp hconv
      have h2 := (h1.inv₀ hsqvk.ne').const_mul (√vk)
      rwa [mul_inv_cancel₀ hsqvk.ne'] at h2
    refine hr.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rcases eq_or_ne (count (fun j ↦ actionIndicator A k j ω) n) 0 with hN0 | hN0
    · simp [hN0]
    · have hNpos : (0 : ℝ) < count (fun j ↦ actionIndicator A k j ω) n :=
        lt_of_le_of_ne (hcnn n) (Ne.symm hN0)
      have hsV : √(Var[id; ν k]) ≠ 0 := Real.sqrt_ne_zero'.mpr hVk
      have hsn : √(n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hnpos
      have hsN : √(count (fun j ↦ actionIndicator A k j ω) n) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr hNpos
      rw [Real.sqrt_div (hcnn n), Real.sqrt_mul (mul_nonneg hVk.le hvk.le),
        Real.sqrt_mul hVk.le, Real.sqrt_mul hVk.le]
      field_simp
  have hslut := tendsto_map_mul_of_tendstoInMeasure_one (σ2 := 1)
    (fun n ↦ (measurable_const.mul (measurable_respMart h k n)).aemeasurable) hRmeas
    (respMart_div_sqrt_tendsto_gaussianReal h hνk k vk hvk hVk hNconv) hRtendsto
  -- Identify `X_n · R_n` with the self-normalized statistic.
  have hXR : ∀ n : ℕ, (fun ω ↦ (√(Var[id; ν k] * vk * (n : ℝ)))⁻¹ * respMart ν A Y k n ω
        * (√(Var[id; ν k] * vk * (n : ℝ))
          * (√(Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n))⁻¹))
      = fun ω ↦ (√(Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n))⁻¹
          * respMart ν A Y k n ω := by
    intro n
    funext ω
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [respMart]
    · have hne : √(Var[id; ν k] * vk * (n : ℝ)) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (mul_pos (mul_pos hVk hvk) (by exact_mod_cast h0))
      have hrw : (√(Var[id; ν k] * vk * (n : ℝ)))⁻¹ * respMart ν A Y k n ω
          * (√(Var[id; ν k] * vk * (n : ℝ))
            * (√(Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n))⁻¹)
          = ((√(Var[id; ν k] * vk * (n : ℝ)))⁻¹ * √(Var[id; ν k] * vk * (n : ℝ)))
            * ((√(Var[id; ν k] * count (fun j ↦ actionIndicator A k j ω) n))⁻¹
              * respMart ν A Y k n ω) := by ring
      rw [hrw, inv_mul_cancel₀ hne, one_mul]
  refine Tendsto.congr (fun n ↦ ?_) hslut
  exact Subtype.ext (congrArg (fun f ↦ P.map f) (hXR n))

end AlphaRAR
