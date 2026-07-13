/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Probability.ResponseCLT
import AlphaRAR.Mathlib.CramerWold

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
      = IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback := rfl

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
theorem wLinComb_tendsto_gaussianReal (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
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
theorem respMart_joint_tendsto_multivariateGaussian
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

end AlphaRAR
