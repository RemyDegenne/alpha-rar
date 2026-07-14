/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.CramerWold
import AlphaRAR.Probability.ResponseCLT
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The joint componentwise central limit theorem

Assembling the per-arm response-martingale CLTs into the joint (multivariate) statement
`(Q_{n,k}/√n)_k ⇒ 𝒩(0, diag(v_k V_k))` via the Cramér–Wold device
(`tendsto_map_of_tendsto_map_inner`). Cramér–Wold reduces the joint convergence to the
one-dimensional convergence of every scalar projection `∑_k w_k Q_{n,k}/√n`, which is itself a
martingale row sum: the increment is `∑_k w_k 𝟙{A i = k}(Y i - θ_k)` (the disjoint arm indicators
make its conditional square `∑_k w_k² 𝟙{A i = k} V_k`), so `MartDiffArray.mart_clt` applies with
limit variance `∑_k w_k² v_k V_k`.
-/

open MeasureTheory ProbabilityTheory Filter Learning

open scoped Topology

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- The `w`-weighted increment `∑_k w_k 𝟙{A i = k}(Y i - θ_k) = w_{A i}(Y i - θ_{A i})`. Summing it
over `i < n` gives the linear combination `∑_k w_k Q_{n,k}` of the per-arm response martingales. -/
noncomputable def wIncr (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (w : 𝓐 → ℝ) (i : ℕ) :
    Ω → ℝ :=
  fun ω ↦ ∑ a, w a * respIncr ν A Y a i ω

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν]
  [IsProbabilityMeasure P] in
/-- Distinct-arm increments have vanishing product (disjoint indicators). -/
lemma respIncr_mul_eq_zero {a b : 𝓐} (hab : a ≠ b) (i : ℕ) (ω : Ω) :
    respIncr ν A Y a i ω * respIncr ν A Y b i ω = 0 := by
  simp only [respIncr]
  rcases eq_or_ne (A i ω) a with ha | ha
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | A i ω = b} by
      simp only [Set.mem_setOf_eq, ha]; exact hab)]
    ring
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | A i ω = a} by simpa using ha)]
    ring

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The square of the weighted increment collapses to the diagonal:
`(∑_k w_k Δ_k)² = ∑_k w_k² Δ_k²` (cross terms vanish by disjointness). -/
lemma sq_wIncr (w : 𝓐 → ℝ) (i : ℕ) (ω : Ω) :
    (wIncr ν A Y w i ω) ^ 2 = ∑ a, w a ^ 2 * (respIncr ν A Y a i ω) ^ 2 := by
  rw [wIncr, pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single a (fun b _ hba ↦ ?_) (fun h ↦ absurd (Finset.mem_univ a) h)]
  · ring
  · calc w a * respIncr ν A Y a i ω * (w b * respIncr ν A Y b i ω)
        = w a * w b * (respIncr ν A Y a i ω * respIncr ν A Y b i ω) := by ring
      _ = 0 := by rw [respIncr_mul_eq_zero hba.symm i ω, mul_zero]

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] in
/-- The weighted increment as a `Finset.univ`-sum of functions (for `condExp`/`MemLp` lemmas). -/
lemma wIncr_eq_sum (w : 𝓐 → ℝ) (i : ℕ) :
    wIncr ν A Y w i = ∑ a, (fun ω ↦ w a * respIncr ν A Y a i ω) := by
  funext ω; rw [wIncr, Finset.sum_apply]

omit [DecidableEq 𝓐] in
/-- Each weighted increment is in `L²` (finite combination of `L²` per-arm increments). -/
lemma memLp_wIncr (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (w : 𝓐 → ℝ) (i : ℕ) : MemLp (wIncr ν A Y w i) 2 P := by
  rw [wIncr_eq_sum]
  exact memLp_finsetSum' _ fun a _ ↦
    (memLp_respMart_increment a (h.measurable_action i) (hY2 i)).const_mul (w a)

omit [DecidableEq 𝓐] in
/-- Each weighted increment is `𝒢 (i+1)`-strongly-measurable. -/
lemma stronglyMeasurable_wIncr (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (w : 𝓐 → ℝ) (i : ℕ) :
    StronglyMeasurable[IsAlgEnvSeq.filtrationAction h.measurable_action
      h.measurable_feedback (i + 1)] (wIncr ν A Y w i) :=
  Finset.stronglyMeasurable_fun_sum _ fun a _ ↦
    (stronglyMeasurable_respIncr h a i).const_mul (w a)

omit [DecidableEq 𝓐] in
/-- The weighted increment is a martingale difference: `E[∑_k w_k Δ_k | 𝒢 i] = 0`. -/
lemma condExp_wIncr (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (w : 𝓐 → ℝ) (i : ℕ) :
    P[wIncr ν A Y w i | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] 0 := by
  have hint : ∀ a, Integrable (fun ω ↦ w a * respIncr ν A Y a i ω) P := fun a ↦
    (integrable_respMart_increment (h.measurable_action i) ((hY2 i).integrable one_le_two)
      a).const_mul (w a)
  have hcs := condExp_finsetSum (μ := P) (s := (Finset.univ : Finset 𝓐))
    (f := fun a ω ↦ w a * respIncr ν A Y a i ω) (fun a _ ↦ hint a)
    (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i)
  have hper : ∀ a, P[fun ω ↦ w a * respIncr ν A Y a i ω
      | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] (0 : Ω → ℝ) := fun a ↦ by
    have h2 := condExp_respMart_increment h a i ((hY2 i).integrable one_le_two)
    filter_upwards [condExp_const_mul (P := P)
      (m := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i)
      (w a) (respIncr ν A Y a i), h2] with ω h1 h2ω
    simp only [Pi.zero_apply] at h2ω ⊢
    rw [h1, show (P[respIncr ν A Y a i
      | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]) ω = 0 from h2ω,
      mul_zero]
  rw [wIncr_eq_sum]
  filter_upwards [hcs, ae_all_iff.mpr hper] with ω hcsω hperω
  rw [hcsω, Finset.sum_apply]
  simp only [Pi.zero_apply]
  exact Finset.sum_eq_zero fun a _ ↦ hperω a

/-- The `w`-weighted martingale-difference array, normalized by the deterministic `√n`; its row sum
is `(∑_k w_k Q_{n,k})/√n`. -/
noncomputable def wArray (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) : MartDiffArray P :=
  MartDiffArray.ofSeq (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback)
    (wIncr ν A Y w) (fun n ↦ (n : ℝ))
    (fun i ↦ memLp_wIncr h hY2 w i) (fun i ↦ condExp_wIncr h hY2 w i)
    (fun i ↦ stronglyMeasurable_wIncr h w i)

omit [DecidableEq 𝓐] in
@[simp] lemma wArray_d (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) (n i : ℕ) :
    (wArray h hY2 w).d n i = fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ * wIncr ν A Y w i ω := rfl

omit [DecidableEq 𝓐] in
@[simp] lemma wArray_filt (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) :
    (wArray h hY2 w).𝓕
      = fun _ ↦ IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback := rfl

omit [DecidableEq 𝓐] in
@[simp] lemma wArray_k (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) : (wArray h hY2 w).k = id := rfl

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- On `{A i = a}`, only arm `a` contributes: `∑_k w_k Δ_k = w_a (Y i - θ_a)`. -/
lemma wIncr_eq_single {a : 𝓐} {i : ℕ} {ω : Ω} (ha : A i ω = a) (w : 𝓐 → ℝ) :
    wIncr ν A Y w i ω = w a * (Y i ω - (ν a)[id]) := by
  rw [wIncr, Finset.sum_eq_single a]
  · rw [respIncr, Set.indicator_of_mem (show ω ∈ {ω | A i ω = a} from ha), one_mul]
  · intro b _ hba
    rw [respIncr, Set.indicator_of_notMem (show ω ∉ {ω | A i ω = b} by
      simp only [Set.mem_setOf_eq, ha]; exact fun hh ↦ hba hh.symm), zero_mul, mul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ a) h

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Partial sums of the weighted increments are the linear combination of the per-arm
martingales. -/
lemma sum_wIncr (w : 𝓐 → ℝ) (n : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range n, wIncr ν A Y w i ω = ∑ a, w a * respMart ν A Y a n ω := by
  simp only [wIncr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.mul_sum, ← sum_respIncr a n, Finset.sum_apply]

omit [DecidableEq 𝓐] in
/-- The row sum of `wArray` is `(∑_k w_k Q_{n,k})/√n`. -/
lemma rowSum_wArray (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) (n : ℕ) :
    (wArray h hY2 w).rowSum n
      = fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ * ∑ a, w a * respMart ν A Y a n ω := by
  rw [wArray, MartDiffArray.rowSum_ofSeq]
  funext ω
  rw [← sum_wIncr w n ω]

omit [DecidableEq 𝓐] in
/-- **Conditional square of the weighted increment**:
`E[(∑_k w_k Δ_k)² | 𝒢 i] = ∑_k w_k² 𝟙{A i=k} V_k` (diagonal collapse + per-arm second moment). -/
lemma condExp_sq_wIncr (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (w : 𝓐 → ℝ) (i : ℕ) :
    P[fun ω ↦ (wIncr ν A Y w i ω) ^ 2
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] fun ω ↦ ∑ a, w a ^ 2 * (armIndicator A a i ω * armVar ν a) := by
  have hsq : (fun ω ↦ (wIncr ν A Y w i ω) ^ 2)
      = ∑ a, (fun ω ↦ w a ^ 2 * (respIncr ν A Y a i ω) ^ 2) := by
    funext ω; rw [sq_wIncr, Finset.sum_apply]
  have hint : ∀ a, Integrable (fun ω ↦ w a ^ 2 * (respIncr ν A Y a i ω) ^ 2) P := fun a ↦
    (integrable_respMart_increment_sq a (h.measurable_action i)
      (((hY2 i).sub (memLp_const _)).integrable_sq)).const_mul (w a ^ 2)
  have hcs := condExp_finsetSum (μ := P) (s := (Finset.univ : Finset 𝓐))
    (f := fun a ω ↦ w a ^ 2 * (respIncr ν A Y a i ω) ^ 2) (fun a _ ↦ hint a)
    (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i)
  have hper : ∀ a, P[fun ω ↦ w a ^ 2 * (respIncr ν A Y a i ω) ^ 2
      | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] fun ω ↦ w a ^ 2 * (armIndicator A a i ω * armVar ν a) := fun a ↦ by
    filter_upwards [condExp_const_mul (P := P)
      (m := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i)
      (w a ^ 2) (fun ω ↦ (respIncr ν A Y a i ω) ^ 2),
      condExp_respMart_increment_sq h a i (((hY2 i).sub (memLp_const _)).integrable_sq)]
      with ω h1 h2
    rw [h1, show (P[fun ω ↦ (respIncr ν A Y a i ω) ^ 2
      | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]) ω
        = armIndicator A a i ω * armVar ν a from h2]
  rw [hsq]
  filter_upwards [hcs, ae_all_iff.mpr hper] with ω hcsω hperω
  rw [hcsω, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ ↦ hperω a

omit [DecidableEq 𝓐] in
/-- **The predictable variation of `wArray` is `(1/n) ∑_k w_k² V_k N_{n,k}`** (a.e.). -/
lemma predVar_wArray_ae (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) (n : ℕ) :
    (wArray h hY2 w).predVar n =ᵐ[P]
      fun ω ↦ (n : ℝ)⁻¹ * ∑ a, w a ^ 2 * armVar ν a * count (fun j ↦ armIndicator A a j ω) n := by
  have h1 := MartDiffArray.predVar_ofSeq
    (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) (wIncr ν A Y w)
    (fun n ↦ (n : ℝ)) (fun i ↦ memLp_wIncr h hY2 w i) (fun i ↦ condExp_wIncr h hY2 w i)
    (fun i ↦ stronglyMeasurable_wIncr h w i) (fun n ↦ Nat.cast_nonneg n) n
  unfold wArray
  filter_upwards [h1, ae_all_iff.mpr (fun i ↦ condExp_sq_wIncr h hY2 w i)] with ω hω hcs
  rw [hω]
  congr 1
  calc ∑ i ∈ Finset.range n, (P[fun ω ↦ (wIncr ν A Y w i ω) ^ 2
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]) ω
      = ∑ i ∈ Finset.range n, ∑ a, w a ^ 2 * (armIndicator A a i ω * armVar ν a) :=
        Finset.sum_congr rfl fun i _ ↦ hcs i
    _ = ∑ a, w a ^ 2 * armVar ν a * count (fun j ↦ armIndicator A a j ω) n := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [count, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring

omit [DecidableEq 𝓐] in
/-- **The predictable variation of `wArray` converges to `∑_k w_k² v_k V_k`** in probability,
from the joint consistency `N_{n,k}/n → v_k`. -/
lemma tendstoInMeasure_predVar_wArray (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) {v : 𝓐 → ℝ}
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    TendstoInMeasure P (fun n ↦ (wArray h hY2 w).predVar n) atTop
      (fun _ ↦ ∑ a, w a ^ 2 * armVar ν a * v a) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω ↦ (n : ℝ)⁻¹ * ∑ a, w a ^ 2 * armVar ν a * count (fun j ↦ armIndicator A a j ω) n) P :=
    fun n ↦ (measurable_const.mul (Finset.measurable_sum _ fun a _ ↦
      measurable_const.mul (measurable_count_armIndicator h a n))).aestronglyMeasurable
  refine tendstoInMeasure_of_tendsto_ae
    (fun n ↦ (hmeas n).congr (predVar_wArray_ae h hY2 w n).symm) ?_
  filter_upwards [ae_all_iff.mpr (fun n ↦ predVar_wArray_ae h hY2 w n), hNconv] with ω hpred hconv
  refine Tendsto.congr (fun n ↦ (hpred n).symm) ?_
  have heq : (fun n : ℕ ↦ (n : ℝ)⁻¹
        * ∑ a, w a ^ 2 * armVar ν a * count (fun j ↦ armIndicator A a j ω) n)
      = fun n : ℕ ↦ ∑ a, w a ^ 2 * armVar ν a
        * (count (fun j ↦ armIndicator A a j ω) n / (n : ℝ)) := by
    funext n
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [div_eq_mul_inv]; ring
  rw [heq]
  exact tendsto_finsetSum _ fun a _ ↦ (hconv a).const_mul (w a ^ 2 * armVar ν a)

/-- The per-arm cell contribution to the weighted conditional Lindeberg quantity:
`(1/n) w_a² (x-θ_a)² 𝟙{|w_a||x-θ_a| > ε√n}`, as a function of the response `x`. -/
noncomputable def lindTrunc (ν : Kernel 𝓐 ℝ) (w : 𝓐 → ℝ) (ε : ℝ) (n : ℕ) (a : 𝓐) : ℝ → ℝ :=
  fun y ↦ (n : ℝ)⁻¹ * w a ^ 2
    * {y' | ε * Real.sqrt n < |w a| * |y' - (ν a)[id]|}.indicator (fun y' ↦ (y' - (ν a)[id]) ^ 2) y

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν]
  [IsProbabilityMeasure P] in
lemma stronglyMeasurable_lindTrunc (w : 𝓐 → ℝ) (ε : ℝ) (n : ℕ) (a : 𝓐) :
    StronglyMeasurable (lindTrunc ν w ε n a) :=
  ((((continuous_id.sub continuous_const).pow 2).stronglyMeasurable).indicator
    (measurableSet_lt measurable_const
      (measurable_const.mul ((measurable_id.sub_const _).abs)))).const_mul _

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐] in
/-- `x ↦ lindTrunc … (Y i x)` is integrable (bounded by the integrable centered square). -/
lemma integrable_lindTrunc_comp (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) (ε : ℝ) (n : ℕ) (a : 𝓐) (i : ℕ) :
    Integrable (fun ω ↦ lindTrunc ν w ε n a (Y i ω)) P := by
  have hcomp : (fun ω ↦ lindTrunc ν w ε n a (Y i ω))
      = fun ω ↦ (n : ℝ)⁻¹ * w a ^ 2
        * ((Y i ⁻¹' {y' | ε * Real.sqrt n < |w a| * |y' - (ν a)[id]|}).indicator
          (fun ω ↦ (Y i ω - (ν a)[id]) ^ 2) ω) := by
    funext ω
    simp only [lindTrunc]
    by_cases hmem : Y i ω ∈ {y' | ε * Real.sqrt n < |w a| * |y' - (ν a)[id]|}
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem
        (show ω ∈ (Y i) ⁻¹' {y' | ε * Real.sqrt n < |w a| * |y' - (ν a)[id]|} from hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem
        (show ω ∉ (Y i) ⁻¹' {y' | ε * Real.sqrt n < |w a| * |y' - (ν a)[id]|} from hmem)]
  rw [hcomp]
  exact ((((hY2 i).sub (memLp_const _)).integrable_sq).indicator
    ((h.measurable_feedback i) (measurableSet_lt measurable_const
      (measurable_const.mul ((measurable_id.sub_const _).abs))))).const_mul _

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] in
/-- The integral of the cell contribution factors out the deterministic constant. -/
lemma integral_lindTrunc (w : 𝓐 → ℝ) (ε : ℝ) (n : ℕ) (a : 𝓐) :
    ∫ y, lindTrunc ν w ε n a y ∂(ν a)
      = (n : ℝ)⁻¹ * w a ^ 2 * ∫ x, {x | ε * Real.sqrt n < |w a| * |x - (ν a)[id]|}.indicator
          (fun x ↦ (x - (ν a)[id]) ^ 2) x ∂(ν a) := by
  simp only [lindTrunc, mul_assoc]
  rw [integral_const_mul, integral_const_mul]

omit [DecidableEq 𝓐] in
/-- **Closed form of the weighted conditional Lindeberg quantity** (a.e.):
`L_n(ε) = (1/n) ∑_k w_k² h_{n,k}(ε) N_{n,k}`, where
`h_{n,k}(ε) = ∫ (x-θ_k)² 𝟙{|w_k||x-θ_k|>ε√n} dν_k`. Each cell contributes
`∑_k 𝟙{A i=k}·∫ lindTrunc dν_k` (`condExp_indicator_comp` per arm on the diagonal-collapsed
square). -/
lemma lindeberg_wArray_ae (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) (ε : ℝ) (n : ℕ) :
    (wArray h hY2 w).lindeberg n ε =ᵐ[P]
      fun ω ↦ (n : ℝ)⁻¹ * ∑ a, w a ^ 2
        * (∫ x, {x | ε * Real.sqrt n < |w a| * |x - (ν a)[id]|}.indicator
            (fun x ↦ (x - (ν a)[id]) ^ 2) x ∂(ν a))
        * count (fun j ↦ armIndicator A a j ω) n := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    filter_upwards with ω
    simp [MartDiffArray.lindeberg, wArray_k, count]
  · have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0'
    have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0'.le
    have hFi : ∀ i, {ω | ε < |(wArray h hY2 w).d n i ω|}.indicator
          (fun ω ↦ ((wArray h hY2 w).d n i ω) ^ 2)
        = fun ω ↦ ∑ a, armIndicator A a i ω * lindTrunc ν w ε n a (Y i ω) := by
      intro i
      funext ω
      have hd : (wArray h hY2 w).d n i ω
          = (Real.sqrt (n : ℝ))⁻¹ * (w (A i ω) * (Y i ω - (ν (A i ω))[id])) := by
        simp only [wArray_d]; rw [wIncr_eq_single rfl w]
      rw [Finset.sum_eq_single (A i ω) (fun b _ hb ↦ ?_)
        (fun hh ↦ absurd (Finset.mem_univ _) hh)]
      · have harm : armIndicator A (A i ω) i ω = 1 := by
          change Set.indicator {ω' | A i ω' = A i ω} (fun _ ↦ (1 : ℝ)) ω = 1
          rw [Set.indicator_of_mem (show ω ∈ {ω' | A i ω' = A i ω} from rfl)]
        rw [harm, one_mul]
        have hcond : (ε < |(wArray h hY2 w).d n i ω|)
            ↔ (ε * Real.sqrt (n : ℝ) < |w (A i ω)| * |Y i ω - (ν (A i ω))[id]|) := by
          rw [hd, abs_mul, abs_of_nonneg (inv_nonneg.mpr hs.le), abs_mul, inv_mul_eq_div,
            lt_div_iff₀ hs]
        rw [Set.indicator_apply]
        by_cases hc : ε * Real.sqrt (n : ℝ) < |w (A i ω)| * |Y i ω - (ν (A i ω))[id]|
        · rw [if_pos (show ω ∈ {ω | ε < |(wArray h hY2 w).d n i ω|} from hcond.mpr hc), hd,
            lindTrunc, Set.indicator_of_mem
              (show Y i ω ∈ {y' | ε * Real.sqrt n < |w (A i ω)| * |y' - (ν (A i ω))[id]|} from hc),
            mul_pow, mul_pow, inv_pow, hs2]
          ring
        · rw [if_neg (show ω ∉ {ω | ε < |(wArray h hY2 w).d n i ω|} from
            fun hmem ↦ hc (hcond.mp hmem)), lindTrunc, Set.indicator_of_notMem
              (show Y i ω ∉ {y' | ε * Real.sqrt n < |w (A i ω)| * |y' - (ν (A i ω))[id]|} from hc),
            mul_zero]
      · have hb0 : armIndicator A b i ω = 0 := by
          simp only [armIndicator, Set.indicator_of_notMem
            (show ω ∉ {ω | A i ω = b} by simp only [Set.mem_setOf_eq]; exact fun hh ↦ hb hh.symm)]
        rw [hb0, zero_mul]
    have hsummand : ∀ i, (P[{ω | ε < |(wArray h hY2 w).d n i ω|}.indicator
          (fun ω ↦ ((wArray h hY2 w).d n i ω) ^ 2)
          | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]) =ᵐ[P]
        fun ω ↦ ∑ a, armIndicator A a i ω * ∫ y, lindTrunc ν w ε n a y ∂(ν a) := by
      intro i
      have hSi_eq : {ω | ε < |(wArray h hY2 w).d n i ω|}.indicator
            (fun ω ↦ ((wArray h hY2 w).d n i ω) ^ 2)
          = ∑ a, (fun ω ↦ armIndicator A a i ω * lindTrunc ν w ε n a (Y i ω)) := by
        rw [hFi i]; funext ω; rw [Finset.sum_apply]
      rw [hSi_eq]
      have hint : ∀ a, Integrable
          (fun ω ↦ armIndicator A a i ω * lindTrunc ν w ε n a (Y i ω)) P := fun a ↦ by
        have hform : (fun ω ↦ armIndicator A a i ω * lindTrunc ν w ε n a (Y i ω))
            = {ω | A i ω = a}.indicator (fun ω ↦ lindTrunc ν w ε n a (Y i ω)) := by
          funext ω; simp only [armIndicator, Set.indicator]
          by_cases hω : ω ∈ {ω | A i ω = a} <;> simp [hω]
        rw [hform]
        exact (integrable_lindTrunc_comp h hY2 w ε n a i).indicator
          (h.measurable_action i (measurableSet_singleton a))
      have hcs := condExp_finsetSum (μ := P) (s := (Finset.univ : Finset 𝓐))
        (f := fun a ω ↦ armIndicator A a i ω * lindTrunc ν w ε n a (Y i ω)) (fun a _ ↦ hint a)
        (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i)
      have hper : ∀ a, P[fun ω ↦ armIndicator A a i ω * lindTrunc ν w ε n a (Y i ω)
          | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
          =ᵐ[P] fun ω ↦ armIndicator A a i ω * ∫ y, lindTrunc ν w ε n a y ∂(ν a) := fun a ↦
        condExp_indicator_comp h a i (stronglyMeasurable_lindTrunc w ε n a)
          (integrable_lindTrunc_comp h hY2 w ε n a i)
      filter_upwards [hcs, ae_all_iff.mpr hper] with ω hcsω hperω
      rw [hcsω, Finset.sum_apply]
      exact Finset.sum_congr rfl fun a _ ↦ hperω a
    filter_upwards [ae_all_iff.mpr hsummand] with ω hω
    simp only [MartDiffArray.lindeberg, wArray_k, wArray_filt, id]
    rw [Finset.sum_congr rfl fun i _ ↦ hω i, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_mul, show (∑ i ∈ Finset.range n, armIndicator A a i ω)
      = count (fun j ↦ armIndicator A a j ω) n from rfl, integral_lindTrunc]
    simp only [id_eq]
    ring

omit [DecidableEq 𝓐] in
/-- **The weighted conditional Lindeberg condition holds** (the `lindeberg` hypothesis of
`thm:mart_clt`). Since `L_n(ε) ≤ ∑_k w_k² h_{n,k}(ε)` and each truncated moment `h_{n,k}(ε) → 0`
by dominated convergence (`tendsto_integral_sq_indicator_gt`; the threshold `ε√n/|w_k| → ∞`),
`L_n(ε) → 0` a.s., hence in measure. -/
lemma tendstoInMeasure_lindeberg_wArray (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) :
    ∀ ε, 0 < ε → TendstoInMeasure P (fun n ↦ (wArray h hY2 w).lindeberg n ε) atTop 0 := by
  intro ε hε
  obtain ⟨G, hG⟩ : ∃ G : ℕ → 𝓐 → ℝ, ∀ n a, G n a
      = ∫ x, {x | ε * Real.sqrt n < |w a| * |x - (ν a)[id]|}.indicator
          (fun x ↦ (x - (ν a)[id]) ^ 2) x ∂(ν a) := ⟨_, fun n a ↦ rfl⟩
  have hGnn : ∀ n a, (0 : ℝ) ≤ G n a := fun n a ↦ by
    rw [hG]; exact integral_nonneg fun x ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) x
  have hGtail : ∀ a, Tendsto (fun n : ℕ ↦ w a ^ 2 * G n a) atTop (𝓝 0) := by
    intro a
    rcases eq_or_ne (w a) 0 with hwa | hwa
    · simp only [hwa, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact tendsto_const_nhds
    · have hcent2νa : Integrable (fun x ↦ (x - (ν a)[id]) ^ 2) (ν a) :=
        ((hνk a).sub (memLp_const _)).integrable_sq
      have hDCTa := tendsto_integral_sq_indicator_gt (P := ν a) (Z := fun x ↦ x - (ν a)[id])
        (measurable_id.sub_const _) hcent2νa
      have hwapos : (0 : ℝ) < |w a| := abs_pos.mpr hwa
      have hca : Tendsto (fun n : ℕ ↦ ε * Real.sqrt (n : ℝ) / |w a|) atTop atTop :=
        Tendsto.atTop_div_const hwapos (Tendsto.const_mul_atTop hε
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
      have hGa : Tendsto (fun n ↦ G n a) atTop (𝓝 0) := by
        refine Tendsto.congr (fun n ↦ ?_) (by simpa only [Function.comp_def] using hDCTa.comp hca)
        rw [hG]
        have hset : {x | ε * Real.sqrt n / |w a| < |x - (ν a)[id]|}
            = {x | ε * Real.sqrt n < |w a| * |x - (ν a)[id]|} := by
          ext x
          simp only [Set.mem_setOf_eq]
          rw [div_lt_iff₀ hwapos, mul_comm (|x - (ν a)[id]|) (|w a|)]
        rw [hset]
      have := hGa.const_mul (w a ^ 2)
      rwa [mul_zero] at this
  have hb : Tendsto (fun n : ℕ ↦ ∑ a, w a ^ 2 * G n a) atTop (𝓝 0) := by
    have hbb := tendsto_finsetSum (Finset.univ : Finset 𝓐) fun a _ ↦ hGtail a
    rwa [Finset.sum_const_zero] at hbb
  have hlin' : ∀ n, (wArray h hY2 w).lindeberg n ε =ᵐ[P]
      fun ω ↦ (n : ℝ)⁻¹ * ∑ a, w a ^ 2 * G n a * count (fun j ↦ armIndicator A a j ω) n := by
    intro n
    filter_upwards [lindeberg_wArray_ae h hY2 w ε n] with ω hω
    rw [hω]; simp_rw [← hG]
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · exact ((measurable_const.mul (Finset.measurable_sum _ fun a _ ↦
      measurable_const.mul (measurable_count_armIndicator h a n))).aestronglyMeasurable).congr
      (hlin' n).symm
  · filter_upwards [ae_all_iff.mpr hlin'] with ω hlin
    have hcnn : ∀ a n, (0 : ℝ) ≤ count (fun j ↦ armIndicator A a j ω) n := fun a n ↦
      Finset.sum_nonneg fun j _ ↦ armIndicator_nonneg A a j ω
    have hcle : ∀ a n, count (fun j ↦ armIndicator A a j ω) n ≤ (n : ℝ) := fun a n ↦ by
      rw [count]
      calc ∑ j ∈ Finset.range n, armIndicator A a j ω
          ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ ↦ armIndicator_le_one A a j ω
        _ = (n : ℝ) := by simp
    refine Tendsto.congr (fun n ↦ (hlin n).symm) (squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hb)
    · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (Finset.sum_nonneg fun a _ ↦
        mul_nonneg (mul_nonneg (sq_nonneg _) (hGnn n a)) (hcnn a n))
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp only [Nat.cast_zero, inv_zero, zero_mul]
        exact Finset.sum_nonneg fun a _ ↦ mul_nonneg (sq_nonneg _) (hGnn 0 a)
      · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [inv_mul_le_iff₀ (by positivity)]
        calc ∑ a, w a ^ 2 * G n a * count (fun j ↦ armIndicator A a j ω) n
            ≤ ∑ a, w a ^ 2 * G n a * (n : ℝ) :=
              Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hcle a n)
                (mul_nonneg (sq_nonneg _) (hGnn n a))
          _ = (n : ℝ) * ∑ a, w a ^ 2 * G n a := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ ↦ by ring

omit [DecidableEq 𝓐] in
/-- **The 1-D CLT for a linear combination of the response martingales** (the Cramér–Wold
projection ingredient): `(∑_k w_k Q_{n,k})/√n ⇒ 𝒩(0, ∑_k w_k² v_k V_k)`. Applies
`MartDiffArray.mart_clt` to `wArray`, whose predictable variation tends to `∑_k w_k² v_k V_k` and
which satisfies the conditional Lindeberg condition. -/
lemma wLinComb_tendsto_gaussianReal (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (w : 𝓐 → ℝ) {v : 𝓐 → ℝ}
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) (hσ2 : 0 ≤ ∑ a, w a ^ 2 * armVar ν a * v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ * ∑ a, w a * respMart ν A Y a n ω),
        Measure.isProbabilityMeasure_map (measurable_const.mul (Finset.measurable_sum _
          fun a _ ↦ (measurable_respMart h a n).const_mul (w a))).aemeasurable⟩
            : ProbabilityMeasure ℝ))
      atTop (𝓝 ⟨gaussianReal 0 (∑ a, w a ^ 2 * armVar ν a * v a).toNNReal, inferInstance⟩) := by
  have hmart := (wArray h hY2 w).mart_clt (σ2 := ∑ a, w a ^ 2 * armVar ν a * v a) hσ2
    (tendstoInMeasure_predVar_wArray h hY2 w hNconv)
    (tendstoInMeasure_lindeberg_wArray h hY2 w hνk)
  simp only [rowSum_wArray] at hmart
  exact hmart

open scoped RealInnerProductSpace in
open InnerProductSpace ProbabilityTheory in
/-- **Projection of a diagonal multivariate Gaussian is a real Gaussian.** For the covariance
`diag σ` (with `σ ≥ 0`), the pushforward of `𝒩(0, diag σ)` under `x ↦ ⟪x, t⟫` is
`𝒩(0, ∑_a σ_a t_a²)`. This is `IsGaussian.map_eq_gaussianReal` with mean `0` (Gaussian is centered)
and variance `covarianceBilin = t·(diag σ)·t = ∑_a σ_a t_a²`. -/
lemma multivariateGaussian_diag_map_inner (σ : 𝓐 → ℝ) (hσ : ∀ a, 0 ≤ σ a)
    (t : EuclideanSpace ℝ 𝓐) :
    (multivariateGaussian 0 (Matrix.diagonal σ)).map (fun x ↦ ⟪x, t⟫)
      = gaussianReal 0 (∑ a, σ a * t a ^ 2).toNNReal := by
  have hpsd : (Matrix.diagonal σ).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; exact hσ
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ 𝓐) (Matrix.diagonal σ) with hμ
  have hfun : (fun x : EuclideanSpace ℝ 𝓐 ↦ ⟪x, t⟫) = ⇑(toDualMap ℝ (EuclideanSpace ℝ 𝓐) t) := by
    funext x; rw [toDualMap_apply_apply]; exact real_inner_comm t x
  rw [hfun, IsGaussian.map_eq_gaussianReal (toDualMap ℝ (EuclideanSpace ℝ 𝓐) t)]
  have hmean : μ[toDualMap ℝ (EuclideanSpace ℝ 𝓐) t] = 0 := by
    change ∫ x, (toDualMap ℝ (EuclideanSpace ℝ 𝓐) t) x ∂μ = 0
    rw [(toDualMap ℝ (EuclideanSpace ℝ 𝓐) t).integral_comp_id_comm IsGaussian.integrable_id, hμ,
      integral_id_multivariateGaussian, map_zero]
  have hvar : Var[toDualMap ℝ (EuclideanSpace ℝ 𝓐) t; μ] = ∑ a, σ a * t a ^ 2 := by
    have hcb := covarianceBilin_self (μ := μ) IsGaussian.memLp_two_id t
    rw [hμ, covarianceBilin_multivariateGaussian hpsd] at hcb
    rw [show Var[toDualMap ℝ (EuclideanSpace ℝ 𝓐) t; μ] = Var[fun u ↦ ⟪t, u⟫; μ] from rfl, ← hcb]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  rw [hmean, hvar]

open scoped RealInnerProductSpace Matrix in
/-- **Diagonal rescaling of a diagonal multivariate Gaussian.** Scaling coordinate `a` of
`𝒩(0, diag s)` by `d a` (the pushforward under `x ↦ (d a · x_a)_a`) yields
`𝒩(0, diag (a ↦ d a ² · s a))`. Proved by characteristic functions: the diagonal scaling is
self-adjoint, so `charFun (μ.map L) t = charFun μ (L t)`, and both sides are Gaussian charFuns
with the matching diagonal quadratic form. -/
lemma multivariateGaussian_diagonal_smul_map (s d : 𝓐 → ℝ) (hs : ∀ a, 0 ≤ s a) :
    (multivariateGaussian 0 (Matrix.diagonal s)).map
        (fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (fun a ↦ d a * x a) : EuclideanSpace ℝ 𝓐))
      = multivariateGaussian 0 (Matrix.diagonal (fun a ↦ d a ^ 2 * s a)) := by
  have hpsd : (Matrix.diagonal s).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hs
  have hpsd' : (Matrix.diagonal (fun a ↦ d a ^ 2 * s a)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun a ↦ mul_nonneg (sq_nonneg _) (hs a)
  set L : EuclideanSpace ℝ 𝓐 → EuclideanSpace ℝ 𝓐 :=
    fun x ↦ WithLp.toLp 2 (fun a ↦ d a * x a) with hLdef
  have hLmeas : Measurable L :=
    (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp
      (measurable_pi_lambda _ fun a ↦
        (((WithLp.measurable_ofLp 2 (𝓐 → ℝ)).comp measurable_id).eval).const_mul (d a))
  have : IsProbabilityMeasure ((multivariateGaussian 0 (Matrix.diagonal s)).map L) :=
    Measure.isProbabilityMeasure_map hLmeas.aemeasurable
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  have hinner : ∀ x : EuclideanSpace ℝ 𝓐, (⟪L x, t⟫ : ℝ) = ⟪x, L t⟫ := by
    intro x
    simp only [hLdef, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have hcont : Continuous (fun x : EuclideanSpace ℝ 𝓐 ↦ Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).mul continuous_const)
  have hmap : charFun ((multivariateGaussian 0 (Matrix.diagonal s)).map L) t
      = charFun (multivariateGaussian 0 (Matrix.diagonal s)) (L t) := by
    rw [charFun_apply, charFun_apply,
      MeasureTheory.integral_map hLmeas.aemeasurable hcont.aestronglyMeasurable]
    simp_rw [hinner]
  rw [hmap, charFun_multivariateGaussian hpsd, charFun_multivariateGaussian hpsd']
  have hq : (L t) ⬝ᵥ Matrix.diagonal s *ᵥ (L t)
      = t ⬝ᵥ Matrix.diagonal (fun a ↦ d a ^ 2 * s a) *ᵥ t := by
    simp only [dotProduct, Matrix.mulVec_diagonal, hLdef, WithLp.ofLp_toLp]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  rw [inner_zero_right, inner_zero_right, hq]

/-- The normalized joint response-martingale vector `((√n)⁻¹ Q_{n,a})_a ∈ ℝ^𝓐`. -/
noncomputable def respVec (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ 𝓐 := WithLp.toLp 2 (fun a ↦ (Real.sqrt (n : ℝ))⁻¹ * respMart ν A Y a n ω)

omit [Fintype 𝓐] [DecidableEq 𝓐] in
lemma measurable_respVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ) :
    Measurable (respVec ν A Y n) :=
  (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp
    (measurable_pi_lambda _ fun a ↦ (measurable_respMart h a n).const_mul _)

open scoped RealInnerProductSpace in
omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] in
/-- `⟪respVec, t⟫ = (√n)⁻¹ ∑_a t_a Q_{n,a}` — the linear combination that `wLinComb` handles. -/
lemma inner_respVec (n : ℕ) (ω : Ω) (t : EuclideanSpace ℝ 𝓐) :
    (⟪respVec ν A Y n ω, t⟫ : ℝ)
      = (Real.sqrt (n : ℝ))⁻¹ * ∑ a, t.ofLp a * respMart ν A Y a n ω := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, respVec]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

open scoped RealInnerProductSpace in
/-- **The joint componentwise CLT** (blueprint `lem:componentwise`, deterministic-normalizer form):
the joint law of `(Q_{n,k}/√n)_k` converges weakly to the diagonal Gaussian `𝒩(0, diag(v_k V_k))`.
Proved by the Cramér–Wold device (`tendsto_map_of_tendsto_map_inner`): every scalar projection
`⟪·, t⟫ = (∑_k t_k Q_{n,k})/√n` converges to `𝒩(0, ∑_k t_k² v_k V_k)` (the 1-D CLT
`wLinComb_tendsto_gaussianReal`), which is exactly the projection of the target Gaussian
(`multivariateGaussian_diag_map_inner`). -/
lemma respMart_joint_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 ≤ v a)
    (hV : ∀ a, 0 ≤ armVar ν a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    Tendsto (fun n : ℕ ↦ ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
        (measurable_respVec h n).aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map
          (⟨multivariateGaussian 0 (Matrix.diagonal (fun a ↦ v a * armVar ν a)), inferInstance⟩
            : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)) measurable_id.aemeasurable)) := by
  refine tendsto_map_of_tendsto_map_inner measurable_id (measurable_respVec h) fun t ↦ ?_
  have hs2nn : 0 ≤ ∑ a, t.ofLp a ^ 2 * armVar ν a * v a :=
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (mul_nonneg (sq_nonneg _) (hV a)) (hv a)
  -- Q side: the projection of the target Gaussian is a real Gaussian.
  have hQ : ProbabilityMeasure.map
        (⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ v a * armVar ν a), inferInstance⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
          (measurable_id.inner_const (c := t)).aemeasurable
      = ⟨gaussianReal 0 (∑ a, t.ofLp a ^ 2 * armVar ν a * v a).toNNReal, inferInstance⟩ := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]
    change (multivariateGaussian 0 (Matrix.diagonal fun a ↦ v a * armVar ν a)).map
      (fun x ↦ (⟪x, t⟫ : ℝ)) = _
    rw [multivariateGaussian_diag_map_inner _ (fun a ↦ mul_nonneg (hv a) (hV a)) t]
    congr 2
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  -- P side: the `n`-th projected law is the 1-D linear-combination law.
  have hP : ∀ n, ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
        ((measurable_respVec h n).inner_const (c := t)).aemeasurable
      = ⟨P.map (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ * ∑ a, t.ofLp a * respMart ν A Y a n ω),
          Measure.isProbabilityMeasure_map (measurable_const.mul (Finset.measurable_sum _
            fun a _ ↦ (measurable_respMart h a n).const_mul _)).aemeasurable⟩ := by
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]
    change P.map (fun ω ↦ (⟪respVec ν A Y n ω, t⟫ : ℝ)) = _
    exact congrArg (P.map ·) (funext fun ω ↦ inner_respVec n ω t)
  rw [hQ]
  exact Tendsto.congr (fun n ↦ (hP n).symm)
    (wLinComb_tendsto_gaussianReal h hY2 t.ofLp hνk hs2nn hNconv)

omit [Fintype 𝓐] [DecidableEq 𝓐] in
/-- The self-normalized joint response-martingale vector `((√N_{n,a})⁻¹ Q_{n,a})_a ∈ ℝ^𝓐`. -/
lemma measurable_respSelfNormVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ) :
    Measurable (fun ω ↦ (WithLp.toLp 2 (fun a ↦
      (Real.sqrt (count (fun j ↦ armIndicator A a j ω) n))⁻¹ * respMart ν A Y a n ω)
        : EuclideanSpace ℝ 𝓐)) :=
  (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp
    (measurable_pi_lambda _ fun a ↦
      ((measurable_count_armIndicator h a n).sqrt.inv).mul (measurable_respMart h a n))

open scoped RealInnerProductSpace in
/-- **The self-normalized joint componentwise CLT** (blueprint `lem:componentwise`,
pure-martingale form). The joint law of `(Q_{n,k}/√N_{n,k})_k` — each response martingale
normalized by its *own* random count `√N_{n,k}` — converges weakly to `𝒩(0, diag(V_k))`.
This is the deterministic-normalizer joint CLT (`respMart_joint_tendsto_multivariateGaussian`)
composed with multivariate Slutsky (`tendsto_map_comp_of_tendstoInMeasure_const`): the
coordinatewise scaling `√(n/N_{n,k}) → 1/√v_k` in probability, and the diagonal rescaling of the
target Gaussian (`multivariateGaussian_diagonal_smul_map`) turns `diag(v_k V_k)` into
`diag(V_k)`. -/
lemma respMart_joint_selfNorm_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (WithLp.toLp 2 (fun a ↦
          (Real.sqrt (count (fun j ↦ armIndicator A a j ω) n))⁻¹ * respMart ν A Y a n ω)
            : EuclideanSpace ℝ 𝓐)),
        Measure.isProbabilityMeasure_map (measurable_respSelfNormVec h n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a), inferInstance⟩) := by
  have hVnn : ∀ a, 0 ≤ armVar ν a := fun a ↦ by rw [armVar]; exact variance_nonneg _ _
  set μ' : Measure (EuclideanSpace ℝ 𝓐) :=
    multivariateGaussian 0 (Matrix.diagonal fun a ↦ v a * armVar ν a) with hμ'
  -- The constant limit `c_a = 1/√v_a` and the random scaling `R_{n,a} = √n · (√N_{n,a})⁻¹`.
  let c : EuclideanSpace ℝ 𝓐 := WithLp.toLp 2 (fun a ↦ (Real.sqrt (v a))⁻¹)
  set Rn : ℕ → Ω → EuclideanSpace ℝ 𝓐 := fun n ω ↦ WithLp.toLp 2
    (fun a ↦ Real.sqrt n * (Real.sqrt (count (fun j ↦ armIndicator A a j ω) n))⁻¹) with hRn
  have hRmeas : ∀ n, AEMeasurable (Rn n) P := fun n ↦
    ((WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun a ↦
      ((measurable_count_armIndicator h a n).sqrt.inv).const_mul _)).aemeasurable
  -- `R_n → c` in probability (from the a.s. count convergence, componentwise then in `ℝ^𝓐`).
  have hRtendsto : TendstoInMeasure P Rn atTop (fun _ ↦ c) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hRmeas n).aestronglyMeasurable) ?_
    filter_upwards [hNconv] with ω hconv
    refine ((PiLp.continuous_toLp (p := 2) (β := fun _ : 𝓐 ↦ ℝ)).tendsto _).comp
      (tendsto_pi_nhds.mpr fun a ↦ ?_)
    have hcnn : ∀ n, (0 : ℝ) ≤ count (fun j ↦ armIndicator A a j ω) n := fun n ↦
      Finset.sum_nonneg fun j _ ↦ armIndicator_nonneg A a j ω
    have h1 : Tendsto (fun n ↦ Real.sqrt (count (fun j ↦ armIndicator A a j ω) n / (n : ℝ)))
        atTop (𝓝 (Real.sqrt (v a))) := (Real.continuous_sqrt.tendsto (v a)).comp (hconv a)
    have h2 := h1.inv₀ (Real.sqrt_pos.mpr (hv a)).ne'
    refine h2.congr' ?_
    filter_upwards with n
    rw [Real.sqrt_div (hcnn n), inv_div, div_eq_mul_inv]
  -- The coordinatewise product `g (x, r)_a = r_a · x_a`, continuous.
  set g : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 → EuclideanSpace ℝ 𝓐 :=
    fun p ↦ WithLp.toLp 2 (fun a ↦ p.2 a * p.1 a) with hg_def
  have hg : Continuous g := by rw [hg_def]; fun_prop
  have hslut := tendsto_map_comp_of_tendstoInMeasure_const (P := P) (μ' := μ') g hg
    (fun n ↦ (measurable_respVec h n).aemeasurable) hRmeas ?_ hRtendsto
  · -- Identify the source `g (respVec, Rn) = selfNormVec` and the limit Gaussian.
    have hlim : μ'.map (fun x ↦ g (x, c))
        = multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a) := by
      rw [hμ', show (fun x : EuclideanSpace ℝ 𝓐 ↦ g (x, c))
          = fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (fun a ↦ (Real.sqrt (v a))⁻¹ * x a)
            : EuclideanSpace ℝ 𝓐) from rfl,
        multivariateGaussian_diagonal_smul_map (fun a ↦ v a * armVar ν a)
          (fun a ↦ (Real.sqrt (v a))⁻¹) fun a ↦ mul_nonneg (hv a).le (hVnn a)]
      refine congrArg (fun f ↦ multivariateGaussian 0 (Matrix.diagonal f)) (funext fun a ↦ ?_)
      show (Real.sqrt (v a))⁻¹ ^ 2 * (v a * armVar ν a) = armVar ν a
      rw [inv_pow, Real.sq_sqrt (hv a).le, inv_mul_cancel_left₀ (hv a).ne']
    rw [show (⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a), inferInstance⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
        = ⟨μ'.map (fun x ↦ g (x, c)), Measure.isProbabilityMeasure_map
            (hg.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable⟩
        from Subtype.ext hlim.symm]
    refine Tendsto.congr (fun n ↦ Subtype.ext (congrArg (P.map ·) ?_)) hslut
    funext ω
    simp only [hg_def]
    refine congrArg (WithLp.toLp 2) (funext fun a ↦ ?_)
    simp only [hRn, respVec, WithLp.ofLp_toLp]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [respMart]
    · have hsn : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast h0)
      rw [show Real.sqrt n * (Real.sqrt (count (fun j ↦ armIndicator A a j ω) n))⁻¹
          * ((Real.sqrt n)⁻¹ * respMart ν A Y a n ω)
          = (Real.sqrt n * (Real.sqrt n)⁻¹)
            * ((Real.sqrt (count (fun j ↦ armIndicator A a j ω) n))⁻¹ * respMart ν A Y a n ω)
          by ring, mul_inv_cancel₀ hsn, one_mul]
  · -- The deterministic-normalizer joint CLT, in the `⟨P.map ·, ·⟩` form.
    have hjoint := respMart_joint_tendsto_multivariateGaussian h hY2 hνk (fun a ↦ (hv a).le)
      hVnn hNconv
    have e2 : (⟨μ', inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
        = ProbabilityMeasure.map
          (⟨μ', inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
          measurable_id.aemeasurable := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk, Measure.map_id]
    rw [e2]
    refine Tendsto.congr (fun n ↦ ?_) hjoint
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]

omit [Fintype 𝓐] [DecidableEq 𝓐] in
/-- The estimator-error vector `D_n(θ̂_n-θ)_k = √N_{n,k}(θ̂_{n,k}-θ_k)` is measurable. -/
lemma measurable_estimatorErrorVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ)
    (n : ℕ) :
    Measurable (fun ω ↦ (WithLp.toLp 2 (fun k ↦
      Real.sqrt (count (fun j ↦ armIndicator A k j ω) n)
        * (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))
          : EuclideanSpace ℝ 𝓐)) := by
  refine (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦ ?_)
  have harm : ∀ j, Measurable (fun ω ↦ armIndicator A k j ω) := fun j ↦
    (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
      (h.measurable_action j))
  refine ((measurable_count_armIndicator h k n).sqrt).mul ?_
  simp only [estimator]
  refine (Measurable.div ?_ ((measurable_count_armIndicator h k n).add_const 1)).sub_const _
  exact (Finset.measurable_sum _ fun j _ ↦ (harm j).mul (h.measurable_feedback j)).add_const (θ₀ k)

open scoped RealInnerProductSpace in
/-- **The self-normalized componentwise CLT for the estimators** (blueprint
`cor:mart_clt_componentwise` / `lem:componentwise`, martingale + Bahadur form). With
`D_n = diag(√N_{n,1},…,√N_{n,K})`, the estimator errors converge jointly,
`D_n(θ̂_n - θ) ⇒ 𝒩(0, diag(V_1,…,V_K))`. From the self-normalized martingale CLT
(`respMart_joint_selfNorm_tendsto_multivariateGaussian`) via the exact Bahadur identity
`θ̂_{n,k} - θ_k = (Q_{n,k}+(θ_{0,k}-θ_k))/(N_{n,k}+1)` (`estimator_sub_eq`): coordinate `k` equals
`(Q_{n,k}/√N_{n,k})·N_{n,k}/(N_{n,k}+1) + (θ_{0,k}-θ_k)√N_{n,k}/(N_{n,k}+1)`, whose scaling factors
tend to `(1,0)` in probability, so multivariate Slutsky leaves the limit unchanged. -/
lemma estimatorError_joint_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (WithLp.toLp 2 (fun k ↦
          Real.sqrt (count (fun j ↦ armIndicator A k j ω) n)
            * (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))
              : EuclideanSpace ℝ 𝓐)),
        Measure.isProbabilityMeasure_map (measurable_estimatorErrorVec h θ₀ n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a), inferInstance⟩) := by
  set μ' : Measure (EuclideanSpace ℝ 𝓐) :=
    multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a) with hμ'
  set c : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 :=
    (WithLp.toLp 2 (fun _ ↦ (1 : ℝ)), WithLp.toLp 2 (fun _ ↦ (0 : ℝ))) with hc
  set g : EuclideanSpace ℝ 𝓐 × (EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐) → EuclideanSpace ℝ 𝓐 :=
    fun p ↦ WithLp.toLp 2 (fun k ↦ p.1 k * p.2.1 k + p.2.2 k) with hg_def
  -- The scaling pair `R_n = ((N/(N+1))_k, ((θ₀-θ)√N/(N+1))_k) → (1,0)` in probability.
  set Rn : ℕ → Ω → EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 := fun n ω ↦
    (WithLp.toLp 2 (fun k ↦ count (fun j ↦ armIndicator A k j ω) n
        / (count (fun j ↦ armIndicator A k j ω) n + 1)),
     WithLp.toLp 2 (fun k ↦ (θ₀ k - (ν k)[id]) * Real.sqrt (count (fun j ↦ armIndicator A k j ω) n)
        / (count (fun j ↦ armIndicator A k j ω) n + 1))) with hRn
  clear_value g Rn c
  have hcnn : ∀ k n ω, (0 : ℝ) ≤ count (fun j ↦ armIndicator A k j ω) n := fun k n ω ↦
    Finset.sum_nonneg fun j _ ↦ armIndicator_nonneg A k j ω
  have hg : Continuous g := by rw [hg_def]; fun_prop
  have hRmeas : ∀ n, AEMeasurable (Rn n) P := by
    intro n
    rw [hRn]
    exact (((WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦
        (measurable_count_armIndicator h k n).div
          ((measurable_count_armIndicator h k n).add_const 1))).prodMk
      ((WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦
        (measurable_const.mul (measurable_count_armIndicator h k n).sqrt).div
          ((measurable_count_armIndicator h k n).add_const 1)))).aemeasurable
  -- `Rn → c` in probability (from a.s. count convergence; each coordinate needs `N_{n,k} → ∞`).
  have hRtendsto : TendstoInMeasure P Rn atTop (fun _ ↦ c) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hRmeas n).aestronglyMeasurable) ?_
    filter_upwards [hNconv] with ω hconv
    have hNinf : ∀ k, Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n) atTop atTop := by
      intro k
      refine ((hconv k).pos_mul_atTop (hv k) tendsto_natCast_atTop_atTop).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [div_mul_cancel₀]; exact_mod_cast hn.ne'
    have hden : ∀ k, Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n + 1) atTop atTop :=
      fun k ↦ tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one) (hNinf k)
    have hsqrtinf : ∀ k, Tendsto (fun n ↦ Real.sqrt (count (fun j ↦ armIndicator A k j ω) n))
        atTop atTop := by
      intro k
      refine tendsto_atTop.mpr fun b ↦ ?_
      filter_upwards [(hNinf k).eventually_ge_atTop (b ^ 2)] with n hn
      calc b ≤ |b| := le_abs_self b
        _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
        _ ≤ _ := Real.sqrt_le_sqrt hn
    rw [hRn, hc]
    refine Filter.Tendsto.prodMk_nhds ?_ ?_
    · refine ((PiLp.continuous_toLp (p := 2) (β := fun _ : 𝓐 ↦ ℝ)).tendsto _).comp
        (tendsto_pi_nhds.mpr fun k ↦ ?_)
      have h1 : Tendsto (fun n ↦ 1 - (count (fun j ↦ armIndicator A k j ω) n + 1)⁻¹) atTop (𝓝 1)
        := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp (hden k))
      refine h1.congr' (Eventually.of_forall fun n ↦ ?_)
      have hne : (count (fun j ↦ armIndicator A k j ω) n : ℝ) + 1 ≠ 0 := by
        have := hcnn k n ω; linarith
      rw [eq_div_iff hne, sub_mul, one_mul, inv_mul_cancel₀ hne]; ring
    · refine ((PiLp.continuous_toLp (p := 2) (β := fun _ : 𝓐 ↦ ℝ)).tendsto _).comp
        (tendsto_pi_nhds.mpr fun k ↦ ?_)
      have hsq : Tendsto (fun n ↦ Real.sqrt (count (fun j ↦ armIndicator A k j ω) n)
          / (count (fun j ↦ armIndicator A k j ω) n + 1)) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n ↦ ?_) (tendsto_inv_atTop_zero.comp (hsqrtinf k))
        simp only [Function.comp_apply]
        rcases (hcnn k n ω).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · have hne : (0 : ℝ) < count (fun j ↦ armIndicator A k j ω) n + 1 := by linarith
          rw [Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hne.le), div_le_iff₀ hne,
            inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.mpr hpos)]
          nlinarith [Real.mul_self_sqrt (hcnn k n ω)]
      have hc2 := hsq.const_mul (θ₀ k - (ν k)[id])
      rw [mul_zero] at hc2
      exact hc2.congr fun n ↦ (mul_div_assoc _ _ _).symm
  -- Apply multivariate Slutsky; identify source (Bahadur) and limit (`g(·,c)=id`).
  have hX := respMart_joint_selfNorm_tendsto_multivariateGaussian h hY2 hνk hv hNconv
  have hslut := tendsto_map_comp_of_tendstoInMeasure_const (P := P) (μ' := μ') g hg
    (fun n ↦ (measurable_respSelfNormVec h n).aemeasurable) hRmeas hX hRtendsto
  have hlimid : (fun x : EuclideanSpace ℝ 𝓐 ↦ g (x, c)) = id := by
    funext x
    simp only [hg_def, hc, mul_one, add_zero, id_eq, WithLp.toLp_ofLp]
  have heq : (⟨μ', inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      = ⟨μ'.map (fun x ↦ g (x, c)), Measure.isProbabilityMeasure_map
          (hg.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable⟩ := by
    apply Subtype.ext
    change μ' = μ'.map (fun x ↦ g (x, c))
    rw [hlimid, Measure.map_id]
  rw [heq]
  refine Tendsto.congr (fun n ↦ Subtype.ext (congrArg (P.map ·) ?_)) hslut
  funext ω
  simp only [hg_def, hRn]
  refine congrArg (WithLp.toLp 2) (funext fun k ↦ ?_)
  have hbr : respMG (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) ((ν k)[id]) n
      = respMart ν A Y k n ω := respMG_indicator_eq_respMart k n ω
  have hne : (0 : ℝ) < count (fun j ↦ armIndicator A k j ω) n + 1 := by
    have := hcnn k n ω; linarith
  rw [estimator_sub_eq _ _ ((ν k)[id]) (θ₀ k) n hne.ne', hbr]
  rcases eq_or_ne (count (fun j ↦ armIndicator A k j ω) n) 0 with hN0 | hN0
  · rw [hN0]; simp
  · have hNpos : (0 : ℝ) < count (fun j ↦ armIndicator A k j ω) n :=
      lt_of_le_of_ne (hcnn k n ω) (Ne.symm hN0)
    set s := Real.sqrt (count (fun j ↦ armIndicator A k j ω) n)
    have hspos : (0 : ℝ) < s := Real.sqrt_pos.mpr hNpos
    have hNs : count (fun j ↦ armIndicator A k j ω) n = s ^ 2 := (Real.sq_sqrt hNpos.le).symm
    rw [hNs]; field_simp

omit [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- When arm `k` has not been sampled by time `n` (`N_{n,k}=0`), the response martingale
vanishes: every increment `𝟙{A m = k}(Y m - θ_k)` is zero because all indicators are. -/
lemma respMart_eq_zero_of_count_zero (k : 𝓐) (n : ℕ) (ω : Ω)
    (h0 : count (fun j ↦ armIndicator A k j ω) n = 0) :
    respMart ν A Y k n ω = 0 := by
  rw [count] at h0
  have harm := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ armIndicator_nonneg A k j ω).mp h0
  simp only [respMart, Finset.sum_apply]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [show Set.indicator {ω | A m ω = k} (fun _ ↦ (1 : ℝ)) ω = armIndicator A k m ω from rfl,
    harm m hm, zero_mul]

omit [Fintype 𝓐] [DecidableEq 𝓐] in
/-- The `√n`-normalized estimator-error vector `(√n(θ̂_{n,k}-θ_k))_k` is measurable. -/
lemma measurable_estimatorSqrtNVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ)
    (n : ℕ) :
    Measurable (fun ω ↦ (WithLp.toLp 2 (fun k ↦ Real.sqrt n
      * (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))
        : EuclideanSpace ℝ 𝓐)) := by
  refine (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦ ?_)
  refine Measurable.const_mul ?_ (Real.sqrt n)
  have harm : ∀ j, Measurable (fun ω ↦ armIndicator A k j ω) := fun j ↦
    (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
      (h.measurable_action j))
  simp only [estimator]
  refine (Measurable.div ?_ ((measurable_count_armIndicator h k n).add_const 1)).sub_const _
  exact (Finset.measurable_sum _ fun j _ ↦ (harm j).mul (h.measurable_feedback j)).add_const (θ₀ k)

open scoped RealInnerProductSpace in
/-- **The CLT for the estimator** (blueprint `lem:clt_theta`). Under Condition~A with
`N_{n,k}/n → v_k` a.s. (`v_k>0`), the `√n`-normalized estimator errors converge jointly,
`√n(θ̂_n - θ) ⇒ 𝒩(0, diag(V_k/v_k))`. Same Bahadur + product-space Slutsky as
`cor:mart_clt_componentwise`, but the martingale is normalized by the deterministic `√n`: coordinate
`k` is `(Q_{n,k}/√N_{n,k})·√(n N_{n,k})/(N_{n,k}+1) + (θ_{0,k}-θ_k)√n/(N_{n,k}+1)`, whose scaling
factors tend to `1/√v_k` and `0`, so the diagonal Gaussian rescaling
(`multivariateGaussian_diagonal_smul_map`) sends `diag(V_k)` to `diag(V_k/v_k)`. -/
theorem estimator_sqrtN_joint_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (WithLp.toLp 2 (fun k ↦ Real.sqrt n
          * (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))
              : EuclideanSpace ℝ 𝓐)),
        Measure.isProbabilityMeasure_map (measurable_estimatorSqrtNVec h θ₀ n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a / v a), inferInstance⟩) := by
  have hVnn : ∀ a, 0 ≤ armVar ν a := fun a ↦ by rw [armVar]; exact variance_nonneg _ _
  set μ' : Measure (EuclideanSpace ℝ 𝓐) :=
    multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a) with hμ'
  set c : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 :=
    (WithLp.toLp 2 (fun k ↦ (Real.sqrt (v k))⁻¹), WithLp.toLp 2 (fun _ ↦ (0 : ℝ))) with hc
  set g : EuclideanSpace ℝ 𝓐 × (EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐) → EuclideanSpace ℝ 𝓐 :=
    fun p ↦ WithLp.toLp 2 (fun k ↦ p.2.1 k * p.1 k + p.2.2 k) with hg_def
  set Rn : ℕ → Ω → EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 := fun n ω ↦
    (WithLp.toLp 2 (fun k ↦ Real.sqrt n * Real.sqrt (count (fun j ↦ armIndicator A k j ω) n)
        / (count (fun j ↦ armIndicator A k j ω) n + 1)),
     WithLp.toLp 2 (fun k ↦ (θ₀ k - (ν k)[id]) * Real.sqrt n
        / (count (fun j ↦ armIndicator A k j ω) n + 1))) with hRn
  clear_value g Rn c
  have hcnn : ∀ k n ω, (0 : ℝ) ≤ count (fun j ↦ armIndicator A k j ω) n := fun k n ω ↦
    Finset.sum_nonneg fun j _ ↦ armIndicator_nonneg A k j ω
  have hg : Continuous g := by rw [hg_def]; fun_prop
  have hsqrtT : ∀ (f : ℕ → ℝ), Tendsto f atTop atTop →
      Tendsto (fun n ↦ Real.sqrt (f n)) atTop atTop := by
    intro f hf
    refine tendsto_atTop.mpr fun b ↦ ?_
    filter_upwards [hf.eventually_ge_atTop (b ^ 2)] with n hn
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ _ := Real.sqrt_le_sqrt hn
  have hRmeas : ∀ n, AEMeasurable (Rn n) P := by
    intro n
    rw [hRn]
    exact (((WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦
        ((measurable_count_armIndicator h k n).sqrt.const_mul _).div
          ((measurable_count_armIndicator h k n).add_const 1))).prodMk
      ((WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦
        measurable_const.div
          ((measurable_count_armIndicator h k n).add_const 1)))).aemeasurable
  have hRtendsto : TendstoInMeasure P Rn atTop (fun _ ↦ c) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hRmeas n).aestronglyMeasurable) ?_
    filter_upwards [hNconv] with ω hconv
    have hNinf : ∀ k, Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n) atTop atTop := by
      intro k
      refine ((hconv k).pos_mul_atTop (hv k) tendsto_natCast_atTop_atTop).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [div_mul_cancel₀]; exact_mod_cast hn.ne'
    have hB : ∀ k, Tendsto (fun n : ℕ ↦ (n : ℝ) / (count (fun j ↦ armIndicator A k j ω) n + 1))
        atTop (𝓝 (v k)⁻¹) := by
      intro k
      have hBB : Tendsto (fun n : ℕ ↦ (count (fun j ↦ armIndicator A k j ω) n + 1) / (n : ℝ))
          atTop (𝓝 (v k)) := by
        have hsum := (hconv k).add tendsto_one_div_atTop_nhds_zero_nat
        rw [add_zero] at hsum
        exact hsum.congr' (Eventually.of_forall fun n ↦ (add_div _ _ _).symm)
      exact (hBB.inv₀ (hv k).ne').congr' (Eventually.of_forall fun n ↦ inv_div _ _)
    rw [hRn, hc]
    refine Filter.Tendsto.prodMk_nhds ?_ ?_
    · refine ((PiLp.continuous_toLp (p := 2) (β := fun _ : 𝓐 ↦ ℝ)).tendsto _).comp
        (tendsto_pi_nhds.mpr fun k ↦ ?_)
      have hA : Tendsto (fun n ↦ Real.sqrt (count (fun j ↦ armIndicator A k j ω) n / (n : ℝ)))
          atTop (𝓝 (Real.sqrt (v k))) := (Real.continuous_sqrt.tendsto _).comp (hconv k)
      have hval : Real.sqrt (v k) * (v k)⁻¹ = (Real.sqrt (v k))⁻¹ := by
        have hvinv : (v k)⁻¹ = (Real.sqrt (v k))⁻¹ * (Real.sqrt (v k))⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt (hv k).le]
        rw [hvinv, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (hv k)), one_mul]
      have hlimT := hA.mul (hB k)
      rw [hval] at hlimT
      refine hlimT.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Real.sqrt_div (hcnn k n ω)]
      set sn := Real.sqrt (n : ℝ)
      have hsnpos : (0 : ℝ) < sn := Real.sqrt_pos.mpr hnpos
      have hnn : (n : ℝ) = sn ^ 2 := (Real.sq_sqrt hnpos.le).symm
      rw [hnn]; field_simp
    · refine ((PiLp.continuous_toLp (p := 2) (β := fun _ : 𝓐 ↦ ℝ)).tendsto _).comp
        (tendsto_pi_nhds.mpr fun k ↦ ?_)
      have hU : Tendsto (fun n : ℕ ↦ Real.sqrt n / (count (fun j ↦ armIndicator A k j ω) n + 1))
          atTop (𝓝 0) := by
        have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (hsqrtT _ tendsto_natCast_atTop_atTop)
        have hml := hinv.mul (hB k)
        rw [zero_mul] at hml
        refine hml.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        set sn := Real.sqrt (n : ℝ)
        have hsnpos : (0 : ℝ) < sn := Real.sqrt_pos.mpr hnpos
        have hnn : (n : ℝ) = sn ^ 2 := (Real.sq_sqrt hnpos.le).symm
        rw [hnn]; field_simp
      have hc2 := hU.const_mul (θ₀ k - (ν k)[id])
      rw [mul_zero] at hc2
      exact hc2.congr fun n ↦ (mul_div_assoc _ _ _).symm
  have hX := respMart_joint_selfNorm_tendsto_multivariateGaussian h hY2 hνk hv hNconv
  have hslut := tendsto_map_comp_of_tendstoInMeasure_const (P := P) (μ' := μ') g hg
    (fun n ↦ (measurable_respSelfNormVec h n).aemeasurable) hRmeas hX hRtendsto
  have hgc : (fun x : EuclideanSpace ℝ 𝓐 ↦ g (x, c))
      = fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (fun k ↦ (Real.sqrt (v k))⁻¹ * x k)
        : EuclideanSpace ℝ 𝓐) := by
    funext x; simp only [hg_def, hc, add_zero]
  have hlim : μ'.map (fun x ↦ g (x, c))
      = multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a / v a) := by
    rw [hgc, hμ', multivariateGaussian_diagonal_smul_map (fun a ↦ armVar ν a)
      (fun k ↦ (Real.sqrt (v k))⁻¹) hVnn]
    refine congrArg (fun f ↦ multivariateGaussian 0 (Matrix.diagonal f)) (funext fun k ↦ ?_)
    show (Real.sqrt (v k))⁻¹ ^ 2 * armVar ν k = armVar ν k / v k
    rw [inv_pow, Real.sq_sqrt (hv k).le, inv_mul_eq_div]
  have heq : (⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a / v a), inferInstance⟩
        : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      = ⟨μ'.map (fun x ↦ g (x, c)), Measure.isProbabilityMeasure_map
          (hg.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable⟩ := by
    apply Subtype.ext
    change multivariateGaussian 0 (Matrix.diagonal fun a ↦ armVar ν a / v a) = μ'.map _
    rw [hlim]
  rw [heq]
  refine Tendsto.congr (fun n ↦ Subtype.ext (congrArg (P.map ·) ?_)) hslut
  funext ω
  simp only [hg_def, hRn]
  refine congrArg (WithLp.toLp 2) (funext fun k ↦ ?_)
  have hbr : respMG (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) ((ν k)[id]) n
      = respMart ν A Y k n ω := respMG_indicator_eq_respMart k n ω
  have hne : (0 : ℝ) < count (fun j ↦ armIndicator A k j ω) n + 1 := by
    have := hcnn k n ω; linarith
  rw [estimator_sub_eq _ _ ((ν k)[id]) (θ₀ k) n hne.ne', hbr]
  rcases eq_or_ne (count (fun j ↦ armIndicator A k j ω) n) 0 with hN0 | hN0
  · rw [respMart_eq_zero_of_count_zero k n ω hN0]; simp only [hN0, Real.sqrt_zero]; ring
  · have hNpos : (0 : ℝ) < count (fun j ↦ armIndicator A k j ω) n :=
      lt_of_le_of_ne (hcnn k n ω) (Ne.symm hN0)
    set s := Real.sqrt (count (fun j ↦ armIndicator A k j ω) n)
    have hspos : (0 : ℝ) < s := Real.sqrt_pos.mpr hNpos
    have hNs : count (fun j ↦ armIndicator A k j ω) n = s ^ 2 := (Real.sq_sqrt hNpos.le).symm
    rw [hNs]; field_simp

end AlphaRAR
