/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.CramerWold
public import AlphaRAR.Mathlib.MultivariateGaussianMap
public import AlphaRAR.YDK2026.ResponseCLT
public import AlphaRAR.Mathlib.Tactic.Tendsto
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public meta import LeanSpec

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

@[expose] public section

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
  simp only [respIncr, armIndicator]
  rcases eq_or_ne (A i ω) a with ha | ha
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | A i ω = b} by
      simp only [Set.mem_ofPred_eq, ha]; exact hab)]
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
lemma memLp_wIncr [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a))
    (w : 𝓐 → ℝ) (i : ℕ) : MemLp (wIncr ν A Y w i) 2 P := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  rw [wIncr_eq_sum]
  exact memLp_finsetSum' _ fun a _ ↦
    (memLp_respMart_increment a (h.measurable_action i) (hY2 i)).const_mul (w a)

omit [DecidableEq 𝓐] in
/-- Each weighted increment is `𝒢 (i+1)`-strongly-measurable. -/
@[fun_prop]
lemma stronglyMeasurable_wIncr (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (w : 𝓐 → ℝ) (i : ℕ) :
    StronglyMeasurable[IsAlgEnvSeq.filtrationAction h.measurable_action
      h.measurable_feedback (i + 1)] (wIncr ν A Y w i) :=
  Finset.stronglyMeasurable_fun_sum _ fun a _ ↦
    (stronglyMeasurable_respIncr h a i).const_mul (w a)

omit [DecidableEq 𝓐] in
/-- The weighted increment is a martingale difference: `E[∑_k w_k Δ_k | 𝒢 i] = 0`. -/
lemma condExp_wIncr [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a))
    (w : 𝓐 → ℝ) (i : ℕ) :
    P[wIncr ν A Y w i | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] 0 := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
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

/-- The weighted martingale-difference array with **row-dependent** weights `wn n : 𝓐 → ℝ`; its row
sum is `∑_k (wn n)_k Q_{n,k}`.

Allowing the weight to depend on the row is what lets a *single* array cover both the common
deterministic normalization `(wn n)_k = w_k/√n` (giving `(∑_k w_k Q_{n,k})/√n`, used for the
non-sparse joint CLT) and *per-arm* normalizations `(wn n)_k = w_k/√(c_{k,n})` (used for the sparse
joint CLT, where the arms grow at genuinely different rates). -/
noncomputable def wArray [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (wn : ℕ → 𝓐 → ℝ) : MartDiffArray P where
  𝓕 := fun _ ↦ IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  d n i := wIncr ν A Y (wn n) i
  k := id
  memLp n i := memLp_wIncr h hνk (wn n) i
  mgdiff n i := condExp_wIncr h hνk (wn n) i
  adapted n i := stronglyMeasurable_wIncr h (wn n) i

omit [DecidableEq 𝓐] in
@[simp] lemma wArray_d [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (wn : ℕ → 𝓐 → ℝ) (n i : ℕ) :
    (wArray h hνk wn).d n i = wIncr ν A Y (wn n) i := rfl

omit [DecidableEq 𝓐] in
@[simp] lemma wArray_filt [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (wn : ℕ → 𝓐 → ℝ) :
    (wArray h hνk wn).𝓕
      = fun _ ↦ IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback := rfl

omit [DecidableEq 𝓐] in
@[simp] lemma wArray_k [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (wn : ℕ → 𝓐 → ℝ) : (wArray h hνk wn).k = id := rfl

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- On `{A i = a}`, only arm `a` contributes: `∑_k w_k Δ_k = w_a (Y i - θ_a)`. -/
@[specifies wIncr "the sum over arms is a bookkeeping device, not a genuine sum: at each round \
exactly one term survives, so the increment is the single weighted centred response of the arm \
actually pulled. This disjointness is what makes the array's variance diagonal"]
lemma wIncr_eq_single {a : 𝓐} {i : ℕ} {ω : Ω} (ha : A i ω = a) (w : 𝓐 → ℝ) :
    wIncr ν A Y w i ω = w a * (Y i ω - (ν a)[id]) := by
  rw [wIncr, Finset.sum_eq_single a]
  · rw [respIncr]
    simp only [armIndicator]
    rw [Set.indicator_of_mem (show ω ∈ {ω | A i ω = a} from ha), one_mul]
  · intro b _ hba
    rw [respIncr]
    simp only [armIndicator]
    rw [Set.indicator_of_notMem (show ω ∉ {ω | A i ω = b} by
      simp only [Set.mem_ofPred_eq, ha]; exact fun hh ↦ hba hh.symm), zero_mul, mul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ a) h

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Partial sums of the weighted increments are the linear combination of the per-arm
martingales. -/
@[specifies wIncr "summing the increments recovers the linear combination `∑_k w_k Q_{n,k}` of the \
per-arm martingales — the statistic Cramér–Wold needs, and the reason the weights sit inside the \
increment rather than outside the sum"]
lemma sum_wIncr (w : 𝓐 → ℝ) (n : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range n, wIncr ν A Y w i ω = ∑ a, w a * respMart ν A Y a n ω := by
  simp only [wIncr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.mul_sum, ← sum_respIncr a n, Finset.sum_apply]

omit [DecidableEq 𝓐] in
/-- The row sum of `wArray` is the weighted combination `∑_k (wn n)_k Q_{n,k}`. -/
@[specifies wArray "row `n` really carries row `n`'s weights: its row sum is \
`∑_k (wn n)_k Q_{n,k}`, so a row-dependent weight family gives a *different* statistic per row — \
which is what per-arm normalizers require"]
lemma rowSum_wArray [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (wn : ℕ → 𝓐 → ℝ) (n : ℕ) :
    (wArray h hνk wn).rowSum n = fun ω ↦ ∑ a, wn n a * respMart ν A Y a n ω := by
  funext ω
  simp only [MartDiffArray.rowSum, wArray_k, wArray_d, id]
  exact sum_wIncr (wn n) n ω

omit [DecidableEq 𝓐] in
/-- **Conditional square of the weighted increment**:
`E[(∑_k w_k Δ_k)² | 𝒢 i] = ∑_k w_k² 𝟙{A i=k} V_k` (diagonal collapse + per-arm second moment). -/
lemma condExp_sq_wIncr [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a))
    (w : 𝓐 → ℝ) (i : ℕ) :
    P[fun ω ↦ (wIncr ν A Y w i ω) ^ 2
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
      =ᵐ[P] fun ω ↦ ∑ a, w a ^ 2 * (armIndicator A a i ω * Var[id; ν a]) := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
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
      =ᵐ[P] fun ω ↦ w a ^ 2 * (armIndicator A a i ω * Var[id; ν a]) := fun a ↦ by
    filter_upwards [condExp_const_mul (P := P)
      (m := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i)
      (w a ^ 2) (fun ω ↦ (respIncr ν A Y a i ω) ^ 2),
      condExp_respMart_increment_sq h a i (((hY2 i).sub (memLp_const _)).integrable_sq)]
      with ω h1 h2
    rw [h1, show (P[fun ω ↦ (respIncr ν A Y a i ω) ^ 2
      | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]) ω
        = armIndicator A a i ω * Var[id; ν a] from h2]
  rw [hsq]
  filter_upwards [hcs, ae_all_iff.mpr hper] with ω hcsω hperω
  rw [hcsω, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ ↦ hperω a

omit [DecidableEq 𝓐] in
/-- **The predictable variation of `wArray` is `∑_k (wn n)_k² V_k N_{n,k}`** (a.e.). -/
@[specifies wArray "the variance is purely diagonal — no cross terms `w_a w_b` survive — and each \
arm accumulates on its own count `N_{n,k}`. This is the limit computation the joint CLT turns into \
a diagonal covariance matrix"]
lemma predVar_wArray_ae [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (wn : ℕ → 𝓐 → ℝ) (n : ℕ) :
    (wArray h hνk wn).predVar n =ᵐ[P]
      fun ω ↦ ∑ a, wn n a ^ 2 * Var[id; ν a] * count (fun j ↦ armIndicator A a j ω) n := by
  filter_upwards [ae_all_iff.mpr (fun i ↦ condExp_sq_wIncr h hνk (wn n) i)] with ω hcs
  simp only [MartDiffArray.predVar, MartDiffArray.condVar, wArray_k, wArray_filt, wArray_d, id]
  calc ∑ i ∈ Finset.range n, (P[fun ω ↦ (wIncr ν A Y (wn n) i ω) ^ 2
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]) ω
      = ∑ i ∈ Finset.range n, ∑ a, wn n a ^ 2 * (armIndicator A a i ω * Var[id; ν a]) :=
        Finset.sum_congr rfl fun i _ ↦ hcs i
    _ = ∑ a, wn n a ^ 2 * Var[id; ν a] * count (fun j ↦ armIndicator A a j ω) n := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [count, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring

omit [DecidableEq 𝓐] in
/-- The scaled row weights `(wn n)_k = w_k/√(c_{k,n})` turn the predictable variation into
`∑_k w_k² V_k (N_{n,k}/c_{k,n})`. -/
lemma predVar_wArray_scaled_ae [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (w : 𝓐 → ℝ) {c : 𝓐 → ℕ → ℝ} (hc : ∀ a n, 0 ≤ c a n) (n : ℕ) :
    (wArray h hνk (fun n a ↦ w a / √(c a n))).predVar n =ᵐ[P]
      fun ω ↦ ∑ a, w a ^ 2 * Var[id; ν a]
        * (count (fun j ↦ armIndicator A a j ω) n / c a n) := by
  filter_upwards [predVar_wArray_ae h hνk (fun n a ↦ w a / √(c a n)) n] with ω hω
  rw [hω]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [div_pow, Real.sq_sqrt (hc a n)]
  ring

omit [DecidableEq 𝓐] in
/-- **The predictable variation converges to `∑_k w_k² V_k ρ_k`** in probability, for the per-arm
scaled weights `(wn n)_k = w_k/√(c_{k,n})` under the regularity `N_{n,k}/c_{k,n} → ρ_k`.

Taking `c_{k,n} = n` and `ρ = v` recovers the non-sparse statement (limit `∑_k w_k² v_k V_k`);
taking `c_{k,n}` to be per-arm normalizers with `ρ ≡ 1` gives the sparse one
(limit `∑_k w_k² V_k`). -/
lemma tendstoInMeasure_predVar_wArray [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (w : 𝓐 → ℝ) {c : 𝓐 → ℕ → ℝ} (hc : ∀ a n, 0 ≤ c a n) {ρ : 𝓐 → ℝ}
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / c a n)
      atTop (𝓝 (ρ a))) :
    TendstoInMeasure P
      (fun n ↦ (wArray h hνk (fun n a ↦ w a / √(c a n))).predVar n) atTop
      (fun _ ↦ ∑ a, w a ^ 2 * Var[id; ν a] * ρ a) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω ↦ ∑ a, w a ^ 2 * Var[id; ν a]
        * (count (fun j ↦ armIndicator A a j ω) n / c a n)) P :=
    fun n ↦ (Finset.measurable_sum _ fun a _ ↦ measurable_const.mul
      ((measurable_count_armIndicator h a n).div_const _)).aestronglyMeasurable
  refine tendstoInMeasure_of_tendsto_ae
    (fun n ↦ (hmeas n).congr (predVar_wArray_scaled_ae h hνk w hc n).symm) ?_
  filter_upwards [ae_all_iff.mpr (fun n ↦ predVar_wArray_scaled_ae h hνk w hc n), hNconv]
    with ω hpred hconv
  refine Tendsto.congr (fun n ↦ (hpred n).symm) ?_
  exact tendsto_finsetSum _ fun a _ ↦ (hconv a).const_mul (w a ^ 2 * Var[id; ν a])

/-- The per-arm cell contribution to the weighted conditional Lindeberg quantity:
`(wn n)_a² (x-θ_a)² 𝟙{|(wn n)_a||x-θ_a| > ε}`, as a function of the response `x`. -/
noncomputable def lindTrunc (ν : Kernel 𝓐 ℝ) (wn : ℕ → 𝓐 → ℝ) (ε : ℝ) (n : ℕ) (a : 𝓐) : ℝ → ℝ :=
  fun y ↦ wn n a ^ 2
    * {y' | ε < |wn n a| * |y' - (ν a)[id]|}.indicator (fun y' ↦ (y' - (ν a)[id]) ^ 2) y

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν]
  [IsProbabilityMeasure P] in
@[fun_prop]
lemma stronglyMeasurable_lindTrunc (wn : ℕ → 𝓐 → ℝ) (ε : ℝ) (n : ℕ) (a : 𝓐) :
    StronglyMeasurable (lindTrunc ν wn ε n a) :=
  ((((continuous_id.sub continuous_const).pow 2).stronglyMeasurable).indicator
    (measurableSet_lt measurable_const
      (measurable_const.mul ((measurable_id.sub_const _).abs)))).const_mul _

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐] in
/-- `x ↦ lindTrunc … (Y i x)` is integrable (bounded by the integrable centered square). -/
@[fun_prop]
lemma integrable_lindTrunc_comp [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (wn : ℕ → 𝓐 → ℝ) (ε : ℝ) (n : ℕ) (a : 𝓐) (i : ℕ) :
    Integrable (fun ω ↦ lindTrunc ν wn ε n a (Y i ω)) P := by
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  have hcomp : (fun ω ↦ lindTrunc ν wn ε n a (Y i ω))
      = fun ω ↦ wn n a ^ 2
        * ((Y i ⁻¹' {y' | ε < |wn n a| * |y' - (ν a)[id]|}).indicator
          (fun ω ↦ (Y i ω - (ν a)[id]) ^ 2) ω) := by
    funext ω
    simp only [lindTrunc]
    by_cases hmem : Y i ω ∈ {y' | ε < |wn n a| * |y' - (ν a)[id]|}
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem
        (show ω ∈ (Y i) ⁻¹' {y' | ε < |wn n a| * |y' - (ν a)[id]|} from hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem
        (show ω ∉ (Y i) ⁻¹' {y' | ε < |wn n a| * |y' - (ν a)[id]|} from hmem)]
  rw [hcomp]
  exact ((((hY2 i).sub (memLp_const _)).integrable_sq).indicator
    ((h.measurable_feedback i) (measurableSet_lt measurable_const
      (measurable_const.mul ((measurable_id.sub_const _).abs))))).const_mul _

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] in
/-- The integral of the cell contribution factors out the deterministic constant. -/
@[specifies lindTrunc "reads off both halves of the cell contribution: the deterministic weight \
`(wn n)_a²` factors out, leaving the arm-`a` Lindeberg mass `∫ (x-θ_a)² 𝟙{|w||x-θ_a|>ε} dν_a` — \
note the threshold is tested on the *weighted* deviation, which is what makes it shrink with `w`"]
lemma integral_lindTrunc (wn : ℕ → 𝓐 → ℝ) (ε : ℝ) (n : ℕ) (a : 𝓐) :
    ∫ y, lindTrunc ν wn ε n a y ∂(ν a)
      = wn n a ^ 2 * ∫ x, {x | ε < |wn n a| * |x - (ν a)[id]|}.indicator
          (fun x ↦ (x - (ν a)[id]) ^ 2) x ∂(ν a) := by
  simp only [lindTrunc]
  rw [integral_const_mul]

omit [DecidableEq 𝓐] in
/-- **Closed form of the weighted conditional Lindeberg quantity** (a.e.):
`L_n(ε) = ∑_k (wn n)_k² h_{n,k}(ε) N_{n,k}`, where
`h_{n,k}(ε) = ∫ (x-θ_k)² 𝟙{|(wn n)_k||x-θ_k|>ε} dν_k`. Each cell contributes
`∑_k 𝟙{A i=k}·∫ lindTrunc dν_k` (`condExp_indicator_comp` per arm on the diagonal-collapsed
square). -/
lemma lindeberg_wArray_ae [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (wn : ℕ → 𝓐 → ℝ) (ε : ℝ) (n : ℕ) :
    (wArray h hνk wn).lindeberg n ε =ᵐ[P]
      fun ω ↦ ∑ a, wn n a ^ 2
        * (∫ x, {x | ε < |wn n a| * |x - (ν a)[id]|}.indicator
            (fun x ↦ (x - (ν a)[id]) ^ 2) x ∂(ν a))
        * count (fun j ↦ armIndicator A a j ω) n := by
  have hFi : ∀ i, {ω | ε < |(wArray h hνk wn).d n i ω|}.indicator
        (fun ω ↦ ((wArray h hνk wn).d n i ω) ^ 2)
      = fun ω ↦ ∑ a, armIndicator A a i ω * lindTrunc ν wn ε n a (Y i ω) := by
    intro i
    funext ω
    have hd : (wArray h hνk wn).d n i ω = wn n (A i ω) * (Y i ω - (ν (A i ω))[id]) := by
      simp only [wArray_d]; rw [wIncr_eq_single rfl (wn n)]
    rw [Finset.sum_eq_single (A i ω) (fun b _ hb ↦ ?_)
      (fun hh ↦ absurd (Finset.mem_univ _) hh)]
    · have harm : armIndicator A (A i ω) i ω = 1 := by
        change Set.indicator {ω' | A i ω' = A i ω} (fun _ ↦ (1 : ℝ)) ω = 1
        rw [Set.indicator_of_mem (show ω ∈ {ω' | A i ω' = A i ω} from rfl)]
      rw [harm, one_mul]
      have hcond : (ε < |(wArray h hνk wn).d n i ω|)
          ↔ (ε < |wn n (A i ω)| * |Y i ω - (ν (A i ω))[id]|) := by
        rw [hd, abs_mul]
      rw [Set.indicator_apply]
      by_cases hc : ε < |wn n (A i ω)| * |Y i ω - (ν (A i ω))[id]|
      · rw [if_pos (show ω ∈ {ω | ε < |(wArray h hνk wn).d n i ω|} from hcond.mpr hc), hd,
          lindTrunc, Set.indicator_of_mem
            (show Y i ω ∈ {y' | ε < |wn n (A i ω)| * |y' - (ν (A i ω))[id]|} from hc), mul_pow]
      · rw [if_neg (show ω ∉ {ω | ε < |(wArray h hνk wn).d n i ω|} from
          fun hmem ↦ hc (hcond.mp hmem)), lindTrunc, Set.indicator_of_notMem
            (show Y i ω ∉ {y' | ε < |wn n (A i ω)| * |y' - (ν (A i ω))[id]|} from hc),
          mul_zero]
    · have hb0 : armIndicator A b i ω = 0 := by
        simp only [armIndicator, Set.indicator_of_notMem
          (show ω ∉ {ω | A i ω = b} by simp only [Set.mem_ofPred_eq]; exact fun hh ↦ hb hh.symm)]
      rw [hb0, zero_mul]
  have hsummand : ∀ i, (P[{ω | ε < |(wArray h hνk wn).d n i ω|}.indicator
        (fun ω ↦ ((wArray h hνk wn).d n i ω) ^ 2)
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]) =ᵐ[P]
      fun ω ↦ ∑ a, armIndicator A a i ω * ∫ y, lindTrunc ν wn ε n a y ∂(ν a) := by
    intro i
    have hSi_eq : {ω | ε < |(wArray h hνk wn).d n i ω|}.indicator
          (fun ω ↦ ((wArray h hνk wn).d n i ω) ^ 2)
        = ∑ a, (fun ω ↦ armIndicator A a i ω * lindTrunc ν wn ε n a (Y i ω)) := by
      rw [hFi i]; funext ω; rw [Finset.sum_apply]
    rw [hSi_eq]
    have hint : ∀ a, Integrable
        (fun ω ↦ armIndicator A a i ω * lindTrunc ν wn ε n a (Y i ω)) P := fun a ↦ by
      have hform : (fun ω ↦ armIndicator A a i ω * lindTrunc ν wn ε n a (Y i ω))
          = {ω | A i ω = a}.indicator (fun ω ↦ lindTrunc ν wn ε n a (Y i ω)) := by
        funext ω; simp only [armIndicator, Set.indicator]
        by_cases hω : ω ∈ {ω | A i ω = a} <;> simp [hω]
      rw [hform]
      exact (integrable_lindTrunc_comp h hνk wn ε n a i).indicator
        (h.measurable_action i (measurableSet_singleton a))
    have hcs := condExp_finsetSum (μ := P) (s := (Finset.univ : Finset 𝓐))
      (f := fun a ω ↦ armIndicator A a i ω * lindTrunc ν wn ε n a (Y i ω)) (fun a _ ↦ hint a)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i)
    have hper : ∀ a, P[fun ω ↦ armIndicator A a i ω * lindTrunc ν wn ε n a (Y i ω)
        | IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback i]
        =ᵐ[P] fun ω ↦ armIndicator A a i ω * ∫ y, lindTrunc ν wn ε n a y ∂(ν a) := fun a ↦
      condExp_indicator_comp h a i (stronglyMeasurable_lindTrunc wn ε n a)
        (integrable_lindTrunc_comp h hνk wn ε n a i)
    filter_upwards [hcs, ae_all_iff.mpr hper] with ω hcsω hperω
    rw [hcsω, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ ↦ hperω a
  filter_upwards [ae_all_iff.mpr hsummand] with ω hω
  simp only [MartDiffArray.lindeberg, wArray_k, wArray_filt, id]
  rw [Finset.sum_congr rfl fun i _ ↦ hω i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_mul, show (∑ i ∈ Finset.range n, armIndicator A a i ω)
    = count (fun j ↦ armIndicator A a j ω) n from rfl, integral_lindTrunc]
  simp only [id_eq]
  ring

omit [DecidableEq 𝓐] in
/-- **The weighted conditional Lindeberg condition holds** (the `lindeberg` hypothesis of
`thm:mart_clt`) for the per-arm scaled weights `(wn n)_k = w_k/√(c_{k,n})`. In closed form
`L_n(ε) = ∑_k w_k² h_{n,k}(ε) (N_{n,k}/c_{k,n})`, where each truncated moment `h_{n,k}(ε) → 0` by
dominated convergence (`tendsto_integral_sq_indicator_gt`; the threshold `ε√(c_{k,n})/|w_k| → ∞`)
while `N_{n,k}/c_{k,n} → ρ_k`, so the product tends to `0` a.s., hence in measure. -/
lemma tendstoInMeasure_lindeberg_wArray [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (w : 𝓐 → ℝ)
    {c : 𝓐 → ℕ → ℝ} (hc : ∀ a n, 0 ≤ c a n) (hc_atTop : ∀ a, Tendsto (c a) atTop atTop)
    {ρ : 𝓐 → ℝ}
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / c a n)
      atTop (𝓝 (ρ a))) :
    ∀ ε, 0 < ε → TendstoInMeasure P
      (fun n ↦ (wArray h hνk (fun n a ↦ w a / √(c a n))).lindeberg n ε) atTop 0 := by
  intro ε hε
  obtain ⟨G, hG⟩ : ∃ G : ℕ → 𝓐 → ℝ, ∀ n a, G n a
      = ∫ x, {x | ε < |w a / √(c a n)| * |x - (ν a)[id]|}.indicator
          (fun x ↦ (x - (ν a)[id]) ^ 2) x ∂(ν a) := ⟨_, fun n a ↦ rfl⟩
  -- Each truncated moment vanishes: the truncation threshold `ε√(c_{a,n})/|w_a| → ∞`.
  have hGtail : ∀ a, Tendsto (fun n : ℕ ↦ G n a) atTop (𝓝 0) := by
    intro a
    rcases eq_or_ne (w a) 0 with hwa | hwa
    · have hz : ∀ n, G n a = 0 := fun n ↦ by
        rw [hG]
        have hset : {x : ℝ | ε < |w a / √(c a n)| * |x - (ν a)[id]|} = ∅ := by
          ext x
          simp only [hwa, zero_div, abs_zero, zero_mul, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_lt]
          exact hε.le
        rw [hset]
        simp
      simp only [hz]
      exact tendsto_const_nhds
    · have hcent2νa : MemLp (fun x ↦ x - (ν a)[id]) 2 (ν a) := (hνk a).sub (memLp_const _)
      have hDCTa := tendsto_integral_sq_indicator_gt (P := ν a) (Z := fun x ↦ x - (ν a)[id])
        (measurable_id.sub_const _) hcent2νa
      have hwapos : (0 : ℝ) < |w a| := abs_pos.mpr hwa
      have hca : Tendsto (fun n : ℕ ↦ ε * √(c a n) / |w a|) atTop atTop :=
        Tendsto.atTop_div_const hwapos (Tendsto.const_mul_atTop hε
          (Real.tendsto_sqrt_atTop.comp (hc_atTop a)))
      refine Tendsto.congr' ?_ (by simpa only [Function.comp_def] using hDCTa.comp hca)
      filter_upwards [(hc_atTop a).eventually_gt_atTop 0] with n hn
      have hsc : (0 : ℝ) < √(c a n) := Real.sqrt_pos.mpr hn
      have hset : {x : ℝ | ε * √(c a n) / |w a| < |x - (ν a)[id]|}
          = {x : ℝ | ε < |w a / √(c a n)| * |x - (ν a)[id]|} := by
        ext x
        simp only [Set.mem_ofPred_eq, abs_div, abs_of_nonneg (Real.sqrt_nonneg (c a n))]
        rw [div_lt_iff₀ hwapos, div_mul_eq_mul_div, lt_div_iff₀ hsc,
          mul_comm (|w a|) (|x - (ν a)[id]|)]
      rw [hG, hset]
  -- Closed form with the scaled weights: `L_n(ε) = ∑_a w_a² G_n(a) (N_{n,a}/c_{a,n})`.
  have hlin' : ∀ n, (wArray h hνk (fun n a ↦ w a / √(c a n))).lindeberg n ε =ᵐ[P]
      fun ω ↦ ∑ a, w a ^ 2 * G n a * (count (fun j ↦ armIndicator A a j ω) n / c a n) := by
    intro n
    filter_upwards [lindeberg_wArray_ae h hνk (fun n a ↦ w a / √(c a n)) ε n] with ω hω
    rw [hω]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← hG, div_pow, Real.sq_sqrt (hc a n)]
    ring
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · exact ((Finset.measurable_sum _ fun a _ ↦ measurable_const.mul
      ((measurable_count_armIndicator h a n).div_const _)).aestronglyMeasurable).congr
      (hlin' n).symm
  · filter_upwards [ae_all_iff.mpr hlin', hNconv] with ω hlin hconv
    refine Tendsto.congr (fun n ↦ (hlin n).symm) ?_
    have hterm : ∀ a ∈ (Finset.univ : Finset 𝓐),
        Tendsto (fun n ↦ w a ^ 2 * G n a
          * (count (fun j ↦ armIndicator A a j ω) n / c a n)) atTop (𝓝 0) := fun a _ ↦ by
      simpa using ((hGtail a).const_mul (w a ^ 2)).mul (hconv a)
    simpa using tendsto_finsetSum (Finset.univ : Finset 𝓐) hterm

omit [DecidableEq 𝓐] in
/-- **The 1-D CLT for a linear combination of the response martingales, with per-arm deterministic
normalizers** (the Cramér–Wold projection ingredient):
`∑_k (w_k/√(c_{k,n})) Q_{n,k} ⇒ 𝒩(0, ∑_k w_k² ρ_k V_k)` whenever `N_{n,k}/c_{k,n} → ρ_k` and
`c_{k,n} → ∞`. Applies `MartDiffArray.mart_clt` to `wArray` with the scaled row weights.

Because the arm indicators are disjoint, a linear combination of the per-arm martingales — *even
with a different normalizer for each arm* — is again a single martingale-difference array. This is
what makes Cramér–Wold available for the sparse joint CLT, where the arms grow at genuinely
different rates and no common normalizer exists. -/
lemma wLinComb_scaled_tendsto_gaussianReal (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (w : 𝓐 → ℝ) (hνk : ∀ a, MemLp id 2 (ν a))
    {c : 𝓐 → ℕ → ℝ} (hc : ∀ a n, 0 ≤ c a n) (hc_atTop : ∀ a, Tendsto (c a) atTop atTop)
    {ρ : 𝓐 → ℝ} (hσ2 : 0 ≤ ∑ a, w a ^ 2 * Var[id; ν a] * ρ a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / c a n)
      atTop (𝓝 (ρ a))) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ ↦ (⟨P.map
          (fun ω ↦ ∑ a, (w a / √(c a n)) * respMart ν A Y a n ω),
        Measure.isProbabilityMeasure_map (Finset.measurable_sum _
          fun a _ ↦ (measurable_respMart h a n).const_mul _).aemeasurable⟩
            : ProbabilityMeasure ℝ))
      atTop (𝓝 ⟨gaussianReal 0 (∑ a, w a ^ 2 * Var[id; ν a] * ρ a).toNNReal, inferInstance⟩) := by
  have hmart := (wArray h hνk (fun n a ↦ w a / √(c a n))).mart_clt
    (σ2 := ∑ a, w a ^ 2 * Var[id; ν a] * ρ a) hσ2
    (tendstoInMeasure_predVar_wArray h hνk w hc hNconv)
    (tendstoInMeasure_lindeberg_wArray h hνk w hc hc_atTop hNconv)
  simp only [rowSum_wArray] at hmart
  exact hmart

omit [DecidableEq 𝓐] in
/-- **The 1-D CLT for a linear combination of the response martingales** (the Cramér–Wold
projection ingredient, common normalizer `√n`): `(∑_k w_k Q_{n,k})/√n ⇒ 𝒩(0, ∑_k w_k² v_k V_k)`.
The `c_{k,n} = n`, `ρ = v` instance of `wLinComb_scaled_tendsto_gaussianReal`. -/
lemma wLinComb_tendsto_gaussianReal (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (w : 𝓐 → ℝ) {v : 𝓐 → ℝ}
    (hνk : ∀ a, MemLp id 2 (ν a)) (hσ2 : 0 ≤ ∑ a, w a ^ 2 * Var[id; ν a] * v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (√(n : ℝ))⁻¹ * ∑ a, w a * respMart ν A Y a n ω),
        Measure.isProbabilityMeasure_map (measurable_const.mul (Finset.measurable_sum _
          fun a _ ↦ (measurable_respMart h a n).const_mul (w a))).aemeasurable⟩
            : ProbabilityMeasure ℝ))
      atTop (𝓝 ⟨gaussianReal 0 (∑ a, w a ^ 2 * Var[id; ν a] * v a).toNNReal, inferInstance⟩) := by
  have hgen := wLinComb_scaled_tendsto_gaussianReal h w hνk (c := fun _ n ↦ (n : ℝ))
    (fun _ n ↦ Nat.cast_nonneg n) (fun _ ↦ tendsto_natCast_atTop_atTop) hσ2 hNconv
  refine hgen.congr' (Filter.Eventually.of_forall fun n ↦ Subtype.ext (congrArg (P.map ·) ?_))
  funext ω
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [div_eq_mul_inv]; ring

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

/-- The normalized joint response-martingale vector `((√(c_{a,n}))⁻¹ Q_{n,a})_a ∈ ℝ^𝓐`, with a
**per-arm** deterministic normalizer `c_{a,n}`. Taking `c_{a,n} = n` gives the common `√n`
normalization; per-arm normalizers are what the sparse joint CLT needs, since there the arms grow at
genuinely different rates. -/
noncomputable def respVec (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (c : 𝓐 → ℕ → ℝ)
    (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 (fun a ↦ (√(c a n))⁻¹ * respMart ν A Y a n ω)

omit [Fintype 𝓐] [DecidableEq 𝓐] in
@[fun_prop]
lemma measurable_respVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (c : 𝓐 → ℕ → ℝ) (n : ℕ) :
    Measurable (respVec ν A Y c n) :=
  (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp
    (measurable_pi_lambda _ fun a ↦ (measurable_respMart h a n).const_mul _)

open scoped RealInnerProductSpace in
omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] in
/-- `⟪respVec, t⟫ = ∑_a (t_a/√(c_{a,n})) Q_{n,a}` — the linear combination that
`wLinComb_scaled_tendsto_gaussianReal` handles. -/
@[specifies respVec "determines the vector completely (a Euclidean vector is its inner products) \
and shows the normalizer is applied *per arm*: projecting on `t` gives `∑_a (t_a/√(c_{a,n})) \
Q_{n,a}`, the exact family Cramér–Wold reduces the joint limit to"]
lemma inner_respVec (c : 𝓐 → ℕ → ℝ) (n : ℕ) (ω : Ω) (t : EuclideanSpace ℝ 𝓐) :
    (⟪respVec ν A Y c n ω, t⟫ : ℝ)
      = ∑ a, (t.ofLp a / √(c a n)) * respMart ν A Y a n ω := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, respVec]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [div_eq_mul_inv]; ring

open scoped RealInnerProductSpace in
/-- **The joint componentwise CLT** (blueprint `lem:componentwise`, deterministic-normalizer form,
per-arm normalizers): the joint law of `(Q_{n,k}/√(c_{k,n}))_k` converges weakly to the diagonal
Gaussian `𝒩(0, diag(ρ_k V_k))` whenever `N_{n,k}/c_{k,n} → ρ_k` and `c_{k,n} → ∞`.
Proved by the Cramér–Wold device (`tendsto_map_of_tendsto_map_inner`): every scalar projection
`⟪·, t⟫ = ∑_k (t_k/√(c_{k,n})) Q_{n,k}` converges to `𝒩(0, ∑_k t_k² ρ_k V_k)` (the 1-D CLT
`wLinComb_scaled_tendsto_gaussianReal`), which is exactly the projection of the target Gaussian
(`multivariateGaussian_diag_map_inner`).

With `c_{k,n} = n`, `ρ = v` this is the non-sparse statement (limit `diag(v_k V_k)`); with per-arm
`c_{k,n}` and `ρ ≡ 1` it is the sparse one (limit `diag(V_k)`), valid even when some `v_k = 0`. -/
lemma respMart_joint_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {c : 𝓐 → ℕ → ℝ} (hc : ∀ a n, 0 ≤ c a n)
    (hc_atTop : ∀ a, Tendsto (c a) atTop atTop) {ρ : 𝓐 → ℝ} (hρ : ∀ a, 0 ≤ ρ a)
    (hV : ∀ a, 0 ≤ Var[id; ν a])
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / c a n)
      atTop (𝓝 (ρ a))) :
    Tendsto (fun n : ℕ ↦ ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
        (measurable_respVec h c n).aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map
          (⟨multivariateGaussian 0 (Matrix.diagonal (fun a ↦ ρ a * Var[id; ν a])), inferInstance⟩
            : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)) measurable_id.aemeasurable)) := by
  refine tendsto_map_of_tendsto_map_inner measurable_id (measurable_respVec h c) fun t ↦ ?_
  have hs2nn : 0 ≤ ∑ a, t.ofLp a ^ 2 * Var[id; ν a] * ρ a :=
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (mul_nonneg (sq_nonneg _) (hV a)) (hρ a)
  -- Q side: the projection of the target Gaussian is a real Gaussian.
  have hQ : ProbabilityMeasure.map
        (⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ ρ a * Var[id; ν a]), inferInstance⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
          (measurable_id.inner_const (c := t)).aemeasurable
      = ⟨gaussianReal 0 (∑ a, t.ofLp a ^ 2 * Var[id; ν a] * ρ a).toNNReal, inferInstance⟩ := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.coe_mk]
    change (multivariateGaussian 0 (Matrix.diagonal fun a ↦ ρ a * Var[id; ν a])).map
      (fun x ↦ (⟪x, t⟫ : ℝ)) = _
    rw [multivariateGaussian_diag_map_inner _ (fun a ↦ mul_nonneg (hρ a) (hV a)) t]
    congr 2
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  -- P side: the `n`-th projected law is the 1-D linear-combination law.
  have hP : ∀ n, ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
        ((measurable_respVec h c n).inner_const (c := t)).aemeasurable
      = ⟨P.map (fun ω ↦ ∑ a, (t.ofLp a / √(c a n)) * respMart ν A Y a n ω),
          Measure.isProbabilityMeasure_map (Finset.measurable_sum _
            fun a _ ↦ (measurable_respMart h a n).const_mul _).aemeasurable⟩ := by
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.coe_mk]
    change P.map (fun ω ↦ (⟪respVec ν A Y c n ω, t⟫ : ℝ)) = _
    exact congrArg (P.map ·) (funext fun ω ↦ inner_respVec c n ω t)
  rw [hQ]
  exact Tendsto.congr (fun n ↦ (hP n).symm)
    (wLinComb_scaled_tendsto_gaussianReal h t.ofLp hνk hc hc_atTop hs2nn hNconv)

omit [Fintype 𝓐] [DecidableEq 𝓐] in
/-- The self-normalized joint response-martingale vector `((√N_{n,a})⁻¹ Q_{n,a})_a ∈ ℝ^𝓐`. -/
@[fun_prop]
lemma measurable_respSelfNormVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ) :
    Measurable (fun ω ↦ (WithLp.toLp 2 (fun a ↦
      (√(count (fun j ↦ armIndicator A a j ω) n))⁻¹ * respMart ν A Y a n ω)
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
coordinatewise scaling `√(c_{k,n}/N_{n,k}) → 1/√ρ_k` in probability, and the diagonal rescaling of
the target Gaussian (`multivariateGaussian_diagonal_smul_map`) turns `diag(ρ_k V_k)` into
`diag(V_k)`.

The hypothesis is the **regularity** of the pull counts: `N_{n,k}/c_{k,n} → ρ_k > 0` for some
deterministic `c_{k,n} → ∞`. Taking `c_{k,n} = n` and `ρ = v` gives the non-sparse statement (which
needs `v_k > 0`); taking per-arm `c_{k,n}` with `ρ ≡ 1` gives the **sparse** one, valid even when
the limiting proportion `v_k` is `0`. Note that some such regularity is genuinely needed:
`N_{n,k} → ∞` alone does not suffice for an adaptively chosen index. -/
lemma respMart_joint_selfNorm_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) {c : 𝓐 → ℕ → ℝ} (hc : ∀ a n, 0 ≤ c a n)
    (hc_atTop : ∀ a, Tendsto (c a) atTop atTop) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / c a n)
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (WithLp.toLp 2 (fun a ↦
          (√(count (fun j ↦ armIndicator A a j ω) n))⁻¹ * respMart ν A Y a n ω)
            : EuclideanSpace ℝ 𝓐)),
        Measure.isProbabilityMeasure_map (measurable_respSelfNormVec h n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a]), inferInstance⟩) := by
  have hVnn : ∀ a, 0 ≤ Var[id; ν a] := fun a ↦ variance_nonneg _ _
  set μ' : Measure (EuclideanSpace ℝ 𝓐) :=
    multivariateGaussian 0 (Matrix.diagonal fun a ↦ v a * Var[id; ν a]) with hμ'
  -- Constant limit `cst_a = 1/√v_a`; random scaling `R_{n,a} = √(c_{a,n})·(√N_{n,a})⁻¹`.
  let cst : EuclideanSpace ℝ 𝓐 := WithLp.toLp 2 (fun a ↦ (√(v a))⁻¹)
  set Rn : ℕ → Ω → EuclideanSpace ℝ 𝓐 := fun n ω ↦ WithLp.toLp 2
    (fun a ↦ √(c a n) * (√(count (fun j ↦ armIndicator A a j ω) n))⁻¹) with hRn
  have hRmeas : ∀ n, AEMeasurable (Rn n) P := fun n ↦
    ((WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun a ↦
      ((measurable_count_armIndicator h a n).sqrt.inv).const_mul _)).aemeasurable
  -- `R_n → cst` in probability (from the a.s. count convergence, componentwise then in `ℝ^𝓐`).
  have hRtendsto : TendstoInMeasure P Rn atTop (fun _ ↦ cst) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hRmeas n).aestronglyMeasurable) ?_
    filter_upwards [hNconv] with ω hconv
    refine ((PiLp.continuous_toLp (p := 2) (β := fun _ : 𝓐 ↦ ℝ)).tendsto _).comp
      (tendsto_pi_nhds.mpr fun a ↦ ?_)
    have hcnn : ∀ n, (0 : ℝ) ≤ count (fun j ↦ armIndicator A a j ω) n := fun n ↦
      Finset.sum_nonneg fun j _ ↦ armIndicator_nonneg A a j ω
    have h1 : Tendsto (fun n ↦ √(count (fun j ↦ armIndicator A a j ω) n / c a n))
        atTop (𝓝 (√(v a))) := (Real.continuous_sqrt.tendsto (v a)).comp (hconv a)
    have h2 := h1.inv₀ (Real.sqrt_pos.mpr (hv a)).ne'
    refine h2.congr' ?_
    filter_upwards with n
    rw [Real.sqrt_div (hcnn n), inv_div, div_eq_mul_inv]
  -- The coordinatewise product `g (x, r)_a = r_a · x_a`, continuous.
  set g : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 → EuclideanSpace ℝ 𝓐 :=
    fun p ↦ WithLp.toLp 2 (fun a ↦ p.2 a * p.1 a) with hg_def
  have hg : Continuous g := by rw [hg_def]; fun_prop
  have hslut := tendsto_map_comp_of_tendstoInMeasure_const (P := P) (μ' := μ') g hg
    (fun n ↦ (measurable_respVec h c n).aemeasurable) hRmeas ?_ hRtendsto
  · -- Identify the source `g (respVec, Rn) = selfNormVec` and the limit Gaussian.
    have hlim : μ'.map (fun x ↦ g (x, cst))
        = multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a]) := by
      rw [hμ', show (fun x : EuclideanSpace ℝ 𝓐 ↦ g (x, cst))
          = fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (fun a ↦ (√(v a))⁻¹ * x a)
            : EuclideanSpace ℝ 𝓐) from rfl,
        multivariateGaussian_diagonal_smul_map (fun a ↦ v a * Var[id; ν a])
          (fun a ↦ (√(v a))⁻¹) fun a ↦ mul_nonneg (hv a).le (hVnn a)]
      refine congrArg (fun f ↦ multivariateGaussian 0 (Matrix.diagonal f)) (funext fun a ↦ ?_)
      show (√(v a))⁻¹ ^ 2 * (v a * Var[id; ν a]) = Var[id; ν a]
      rw [inv_pow, Real.sq_sqrt (hv a).le, inv_mul_cancel_left₀ (hv a).ne']
    rw [show (⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a]), inferInstance⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
        = ⟨μ'.map (fun x ↦ g (x, cst)), Measure.isProbabilityMeasure_map
            (hg.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable⟩
        from Subtype.ext hlim.symm]
    -- The scaling `√(c_{a,n})·(√(c_{a,n}))⁻¹` cancels once every `c_{a,n} > 0`, which holds
    -- eventually since `c_{a,n} → ∞` (and `𝓐` is finite).
    refine Tendsto.congr' ?_ hslut
    filter_upwards [Filter.eventually_all.mpr
      (fun a ↦ (hc_atTop a).eventually_gt_atTop 0)] with n hn
    refine Subtype.ext (congrArg (P.map ·) ?_)
    funext ω
    simp only [hg_def]
    refine congrArg (WithLp.toLp 2) (funext fun a ↦ ?_)
    simp only [hRn, respVec, WithLp.ofLp_toLp]
    have hsn : √(c a n) ≠ 0 := Real.sqrt_ne_zero'.mpr (hn a)
    rw [show √(c a n) * (√(count (fun j ↦ armIndicator A a j ω) n))⁻¹
        * ((√(c a n))⁻¹ * respMart ν A Y a n ω)
        = (√(c a n) * (√(c a n))⁻¹)
          * ((√(count (fun j ↦ armIndicator A a j ω) n))⁻¹ * respMart ν A Y a n ω)
        by ring, mul_inv_cancel₀ hsn, one_mul]
  · -- The deterministic-normalizer joint CLT, in the `⟨P.map ·, ·⟩` form.
    have hjoint := respMart_joint_tendsto_multivariateGaussian h hνk hc hc_atTop
      (fun a ↦ (hv a).le) hVnn hNconv
    have e2 : (⟨μ', inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
        = ProbabilityMeasure.map
          (⟨μ', inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
          measurable_id.aemeasurable :=
      ProbabilityMeasure.toMeasure_injective Measure.map_id.symm
    rw [e2]
    refine Tendsto.congr (fun n ↦ ?_) hjoint
    exact ProbabilityMeasure.toMeasure_injective rfl

omit [Fintype 𝓐] [DecidableEq 𝓐] in
/-- The estimator-error vector `D_n(θ̂_n-θ)_k = √N_{n,k}(θ̂_{n,k}-θ_k)` is measurable. -/
@[fun_prop]
lemma measurable_estimatorErrorVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ)
    (n : ℕ) :
    Measurable (fun ω ↦ (WithLp.toLp 2 (fun k ↦
      √(count (fun j ↦ armIndicator A k j ω) n)
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
tend to `(1,0)` in probability, so multivariate Slutsky leaves the limit unchanged.

The hypothesis is the **regularity** `N_{n,k}/c_{k,n} → v_k > 0` for a deterministic `c_{k,n} → ∞`.
Two instances:
* `c_{k,n} = n`, `v` the limiting proportions (needs `v_k > 0`): the non-sparse
  `cor:mart_clt_componentwise`;
* per-arm `c_{k,n}` with `v ≡ 1`: the **sparse** componentwise CLT (`cor:sparse_clt`), which needs
  no positivity and so covers arms whose limiting proportion is `0`.

Some regularity of this kind is genuinely necessary: `N_{n,k} → ∞` alone does **not** suffice when
the index is chosen adaptively (one can freeze the self-normalized martingale above its typical
value by pausing an arm near a level crossing, using the law of the iterated logarithm). -/
lemma estimatorError_joint_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp id 2 (ν a)) {cn : 𝓐 → ℕ → ℝ} (hcn : ∀ a n, 0 ≤ cn a n)
    (hcn_atTop : ∀ a, Tendsto (cn a) atTop atTop) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / cn a n)
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (WithLp.toLp 2 (fun k ↦
          √(count (fun j ↦ armIndicator A k j ω) n)
            * (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))
              : EuclideanSpace ℝ 𝓐)),
        Measure.isProbabilityMeasure_map (measurable_estimatorErrorVec h θ₀ n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a]), inferInstance⟩) := by
  set μ' : Measure (EuclideanSpace ℝ 𝓐) :=
    multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a]) with hμ'
  set c : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 :=
    (WithLp.toLp 2 (fun _ ↦ (1 : ℝ)), WithLp.toLp 2 (fun _ ↦ (0 : ℝ))) with hc
  set g : EuclideanSpace ℝ 𝓐 × (EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐) → EuclideanSpace ℝ 𝓐 :=
    fun p ↦ WithLp.toLp 2 (fun k ↦ p.1 k * p.2.1 k + p.2.2 k) with hg_def
  -- The scaling pair `R_n = ((N/(N+1))_k, ((θ₀-θ)√N/(N+1))_k) → (1,0)` in probability.
  set Rn : ℕ → Ω → EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 := fun n ω ↦
    (WithLp.toLp 2 (fun k ↦ count (fun j ↦ armIndicator A k j ω) n
        / (count (fun j ↦ armIndicator A k j ω) n + 1)),
     WithLp.toLp 2 (fun k ↦ (θ₀ k - (ν k)[id]) * √(count (fun j ↦ armIndicator A k j ω) n)
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
      refine ((hconv k).pos_mul_atTop (hv k) (hcn_atTop k)).congr' ?_
      filter_upwards [(hcn_atTop k).eventually_gt_atTop 0] with n hn
      rw [div_mul_cancel₀]; exact hn.ne'
    have hden : ∀ k, Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n + 1) atTop atTop :=
      fun k ↦ tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one) (hNinf k)
    have hsqrtinf : ∀ k, Tendsto (fun n ↦ √(count (fun j ↦ armIndicator A k j ω) n))
        atTop atTop := by
      intro k
      refine tendsto_atTop.mpr fun b ↦ ?_
      filter_upwards [(hNinf k).eventually_ge_atTop (b ^ 2)] with n hn
      calc b ≤ |b| := le_abs_self b
        _ = √(b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
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
      have hsq : Tendsto (fun n ↦ √(count (fun j ↦ armIndicator A k j ω) n)
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
  have hX := respMart_joint_selfNorm_tendsto_multivariateGaussian h hνk hcn hcn_atTop hv hNconv
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
    set s := √(count (fun j ↦ armIndicator A k j ω) n)
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
  simp only [respMart]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [harm m hm, zero_mul]

omit [Fintype 𝓐] [DecidableEq 𝓐] in
/-- The `√n`-normalized estimator-error vector `(√n(θ̂_{n,k}-θ_k))_k` is measurable. -/
@[fun_prop]
lemma measurable_estimatorSqrtNVec (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ)
    (n : ℕ) :
    Measurable (fun ω ↦ (WithLp.toLp 2 (fun k ↦ √n
      * (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))
        : EuclideanSpace ℝ 𝓐)) := by
  refine (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (measurable_pi_lambda _ fun k ↦ ?_)
  refine Measurable.const_mul ?_ (√n)
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
lemma estimator_sqrtN_joint_tendsto_multivariateGaussian
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp id 2 (ν a)) {v : 𝓐 → ℝ} (hv : ∀ a, 0 < v a)
    (hNconv : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
      atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (WithLp.toLp 2 (fun k ↦ √n
          * (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))
              : EuclideanSpace ℝ 𝓐)),
        Measure.isProbabilityMeasure_map (measurable_estimatorSqrtNVec h θ₀ n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a] / v a), inferInstance⟩) := by
  have hVnn : ∀ a, 0 ≤ Var[id; ν a] := fun a ↦ variance_nonneg _ _
  set μ' : Measure (EuclideanSpace ℝ 𝓐) :=
    multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a]) with hμ'
  set c : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 :=
    (WithLp.toLp 2 (fun k ↦ (√(v k))⁻¹), WithLp.toLp 2 (fun _ ↦ (0 : ℝ))) with hc
  set g : EuclideanSpace ℝ 𝓐 × (EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐) → EuclideanSpace ℝ 𝓐 :=
    fun p ↦ WithLp.toLp 2 (fun k ↦ p.2.1 k * p.1 k + p.2.2 k) with hg_def
  set Rn : ℕ → Ω → EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 := fun n ω ↦
    (WithLp.toLp 2 (fun k ↦ √n * √(count (fun j ↦ armIndicator A k j ω) n)
        / (count (fun j ↦ armIndicator A k j ω) n + 1)),
     WithLp.toLp 2 (fun k ↦ (θ₀ k - (ν k)[id]) * √n
        / (count (fun j ↦ armIndicator A k j ω) n + 1))) with hRn
  clear_value g Rn c
  have hcnn : ∀ k n ω, (0 : ℝ) ≤ count (fun j ↦ armIndicator A k j ω) n := fun k n ω ↦
    Finset.sum_nonneg fun j _ ↦ armIndicator_nonneg A k j ω
  have hg : Continuous g := by rw [hg_def]; fun_prop
  have hsqrtT : ∀ (f : ℕ → ℝ), Tendsto f atTop atTop →
      Tendsto (fun n ↦ √(f n)) atTop atTop := by
    intro f hf
    refine tendsto_atTop.mpr fun b ↦ ?_
    filter_upwards [hf.eventually_ge_atTop (b ^ 2)] with n hn
    calc b ≤ |b| := le_abs_self b
      _ = √(b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
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
      have hA : Tendsto (fun n ↦ √(count (fun j ↦ armIndicator A k j ω) n / (n : ℝ)))
          atTop (𝓝 (√(v k))) := (Real.continuous_sqrt.tendsto _).comp (hconv k)
      have hval : √(v k) * (v k)⁻¹ = (√(v k))⁻¹ := by
        have hvinv : (v k)⁻¹ = (√(v k))⁻¹ * (√(v k))⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt (hv k).le]
        rw [hvinv, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (hv k)), one_mul]
      have hlimT := hA.mul (hB k)
      rw [hval] at hlimT
      refine hlimT.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Real.sqrt_div (hcnn k n ω)]
      set sn := √(n : ℝ)
      have hsnpos : (0 : ℝ) < sn := Real.sqrt_pos.mpr hnpos
      have hnn : (n : ℝ) = sn ^ 2 := (Real.sq_sqrt hnpos.le).symm
      rw [hnn]; field_simp
    · refine ((PiLp.continuous_toLp (p := 2) (β := fun _ : 𝓐 ↦ ℝ)).tendsto _).comp
        (tendsto_pi_nhds.mpr fun k ↦ ?_)
      have hU : Tendsto (fun n : ℕ ↦ √n / (count (fun j ↦ armIndicator A k j ω) n + 1))
          atTop (𝓝 0) := by
        have hinv : Tendsto (fun n : ℕ ↦ (√n)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (hsqrtT _ tendsto_natCast_atTop_atTop)
        have hml := hinv.mul (hB k)
        rw [zero_mul] at hml
        refine hml.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        set sn := √(n : ℝ)
        have hsnpos : (0 : ℝ) < sn := Real.sqrt_pos.mpr hnpos
        have hnn : (n : ℝ) = sn ^ 2 := (Real.sq_sqrt hnpos.le).symm
        rw [hnn]; field_simp
      have hc2 := hU.const_mul (θ₀ k - (ν k)[id])
      rw [mul_zero] at hc2
      exact hc2.congr fun n ↦ (mul_div_assoc _ _ _).symm
  have hX := respMart_joint_selfNorm_tendsto_multivariateGaussian h hνk
    (c := fun _ m ↦ (m : ℝ)) (fun _ m ↦ Nat.cast_nonneg m)
    (fun _ ↦ tendsto_natCast_atTop_atTop) hv hNconv
  have hslut := tendsto_map_comp_of_tendstoInMeasure_const (P := P) (μ' := μ') g hg
    (fun n ↦ (measurable_respSelfNormVec h n).aemeasurable) hRmeas hX hRtendsto
  have hgc : (fun x : EuclideanSpace ℝ 𝓐 ↦ g (x, c))
      = fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (fun k ↦ (√(v k))⁻¹ * x k)
        : EuclideanSpace ℝ 𝓐) := by
    funext x; simp only [hg_def, hc, add_zero]
  have hlim : μ'.map (fun x ↦ g (x, c))
      = multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a] / v a) := by
    rw [hgc, hμ', multivariateGaussian_diagonal_smul_map (fun a ↦ Var[id; ν a])
      (fun k ↦ (√(v k))⁻¹) hVnn]
    refine congrArg (fun f ↦ multivariateGaussian 0 (Matrix.diagonal f)) (funext fun k ↦ ?_)
    show (√(v k))⁻¹ ^ 2 * Var[id; ν k] = Var[id; ν k] / v k
    rw [inv_pow, Real.sq_sqrt (hv k).le, inv_mul_eq_div]
  have heq : (⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a] / v a), inferInstance⟩
        : ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      = ⟨μ'.map (fun x ↦ g (x, c)), Measure.isProbabilityMeasure_map
          (hg.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable⟩ := by
    apply Subtype.ext
    change multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a] / v a) = μ'.map _
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
    set s := √(count (fun j ↦ armIndicator A k j ω) n)
    have hspos : (0 : ℝ) < s := Real.sqrt_pos.mpr hNpos
    have hNs : count (fun j ↦ armIndicator A k j ω) n = s ^ 2 := (Real.sq_sqrt hNpos.le).symm
    rw [hNs]; field_simp

end AlphaRAR
