/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.Process
public import Mathlib.Probability.Martingale.Centering
public meta import Characterization

/-!
# Predictable quadratic variation

For a square-integrable martingale `M`, the predictable quadratic variation `⟨M⟩` is the
predictable part of the submartingale `M²` in its Doob decomposition
(`MeasureTheory.predictablePart`): `⟨M⟩_0 = 0` and `⟨M⟩_{n+1} - ⟨M⟩_n = μ[(M_{n+1} - M_n)² | ℱ_n]`,
so `⟨M⟩` is nondecreasing and predictable, and `M² - ⟨M⟩` is a martingale. This file is the API of
`⟨M⟩` for `ℕ`-indexed processes.

## Main definitions and results

* `AlphaRAR.predQuadVar`: the predictable quadratic variation `⟨M⟩`.
* `AlphaRAR.predQuadVar_succ_sub_eq`: the increment formula `Δ⟨M⟩_n = μ[(ΔM_n)² | ℱ_n]`, and its
  summed form `AlphaRAR.predQuadVar_ae_eq_sum`: `⟨M⟩_n = ∑_{i<n} μ[(ΔM_i)² | ℱ_i]`.
* `AlphaRAR.predQuadVar_mono`, `AlphaRAR.predQuadVar_nonneg`, `AlphaRAR.predQuadVar_le_of_bound`:
  `⟨M⟩` is nondecreasing and nonnegative, and `⟨M⟩_n ≤ c² n` when `|ΔM_i| ≤ c`.
* `AlphaRAR.stronglyAdapted_predQuadVar`, `AlphaRAR.isStronglyPredictable_predQuadVar`: `⟨M⟩` is
  adapted and predictable.
* `AlphaRAR.martingale_sq_sub_predQuadVar`, `AlphaRAR.submartingale_sq`: `M² - ⟨M⟩` is a
  martingale, `M²` is a submartingale.
* `AlphaRAR.IsPredQuadVar`: the property that characterizes `⟨M⟩` — predictable, null at `0`, and
  compensating `M²` — with `isPredQuadVar_predQuadVar` (`⟨M⟩` has it) and
  `IsPredQuadVar.indistinguishable_predQuadVar` (nothing else does, up to indistinguishability).
* `AlphaRAR.integral_sq_eq_integral_predQuadVar`,
  `AlphaRAR.integral_sq_eq_sum_integral_increment_sq`: the discrete Itô isometry
  `E[M_n²] = E[⟨M⟩_n] = ∑_{k<n} E[(ΔM_k)²]`.
* `AlphaRAR.martingale_mul`, `AlphaRAR.predQuadVar_add_of_martingale_mul`: the product of
  conditionally orthogonal martingales is a martingale, and `⟨M + N⟩ = ⟨M⟩ + ⟨N⟩` for them.

## Integrability hypotheses

The increment formula at step `n` needs exactly `(ΔM_n)² ∈ L¹` and `M_n ΔM_n ∈ L¹`, and the
one-step lemmas (`predQuadVar_succ_sub_eq`, `predQuadVar_le_succ`) ask for exactly that, as
`hd2 : MemLp (ΔM_n) 2 μ` and `hprod : Integrable (M_n * ΔM_n) μ`. Both follow from
`M_n, M_{n+1} ∈ L²` (`memLp_increment`, `integrable_mul_increment`) and from an a.e. bound on
`ΔM_n` (`memLp_increment_of_bound`, `integrable_mul_increment_of_bound`). The lemmas about the whole
path assume a square-integrable martingale, `hM2 : ∀ n, MemLp (M n) 2 μ`, which
`Martingale.memLp_of_abs_increment_le` supplies for a martingale null at `0` with bounded
increments.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-! ### Martingale increments -/

/-- **A martingale increment has vanishing conditional expectation**: for `i ≤ j`,
`μ[M j - M i | ℱ i] = 0` a.e. This is the martingale property (`Martingale.condExp_ae_eq`)
restated for the increment, which is the form every computation with increments needs. -/
lemma _root_.MeasureTheory.Martingale.condExp_sub_ae_eq_zero {ι E : Type*} [Preorder ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ℱ : Filtration ι m0}
    {N : ι → Ω → E} (hN : Martingale N ℱ μ) {i j : ι} (hij : i ≤ j) :
    μ[N j - N i | ℱ i] =ᵐ[μ] 0 := by
  have h1 : μ[N j - N i | ℱ i] =ᵐ[μ] μ[N j | ℱ i] - μ[N i | ℱ i] :=
    condExp_sub (hN.integrable j) (hN.integrable i) _
  filter_upwards [h1, hN.condExp_ae_eq hij, hN.condExp_ae_eq (le_refl i)] with ω e1 e2 e3
  simp only [Pi.sub_apply, Pi.zero_apply, e1, e2, e3, sub_self]

/-- **A martingale has constant expectation**: `∫ N i = ∫ N j` for `i ≤ j`. This is
`Martingale.setIntegral_eq` on the whole space. -/
lemma _root_.MeasureTheory.Martingale.integral_eq {ι E : Type*} [Preorder ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ℱ : Filtration ι m0}
    [SigmaFiniteFiltration μ ℱ] {N : ι → Ω → E} (hN : Martingale N ℱ μ) {i j : ι} (hij : i ≤ j) :
    ∫ ω, N i ω ∂μ = ∫ ω, N j ω ∂μ := by
  simpa using hN.setIntegral_eq hij MeasurableSet.univ

/-- **The cross term is integrable** for a square-integrable process: `Mₙ·ΔMₙ ∈ L¹` by
Cauchy–Schwarz. -/
lemma integrable_mul_increment {n : ℕ} (hMn : MemLp (M n) 2 μ) (hMn1 : MemLp (M (n + 1)) 2 μ) :
    Integrable (M n * (M (n + 1) - M n)) μ :=
  hMn.integrable_mul (hMn1.sub hMn)

/-- **The increment of a square-integrable process is square-integrable.** -/
lemma memLp_increment {n : ℕ} (hMn : MemLp (M n) 2 μ) (hMn1 : MemLp (M (n + 1)) 2 μ) :
    MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ :=
  hMn1.sub hMn

/-- **The cross term is integrable** for a process with an a.e. bounded increment: `Mₙ ∈ L¹` and
`ΔMₙ ∈ L^∞`. This asks less than `integrable_mul_increment`, which needs `Mₙ ∈ L²`. -/
lemma integrable_mul_increment_of_bound {n : ℕ} {c : ℝ} (hMn : Integrable (M n) μ)
    (hMn1 : AEStronglyMeasurable (M (n + 1)) μ)
    (hb : ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c) :
    Integrable (M n * (M (n + 1) - M n)) μ :=
  hMn.mul_bdd (hMn1.sub hMn.aestronglyMeasurable)
    (by filter_upwards [hb] with ω h; simpa [Real.norm_eq_abs] using h)

/-- **An a.e. bounded increment lies in every `Lᵖ`**, on a finite measure. In particular
`ΔMₙ ∈ L²`, which is the form the quadratic variation needs, and it asks less than
`memLp_increment`, which needs `Mₙ ∈ L²`. -/
lemma memLp_increment_of_bound [IsFiniteMeasure μ] {n : ℕ} {c : ℝ} {p : ℝ≥0∞}
    (hMn : AEStronglyMeasurable (M n) μ) (hMn1 : AEStronglyMeasurable (M (n + 1)) μ)
    (hb : ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c) :
    MemLp (fun ω ↦ M (n + 1) ω - M n ω) p μ :=
  .of_bound (hMn1.sub hMn) c (by filter_upwards [hb] with ω h; rwa [Real.norm_eq_abs])

/-- **A martingale with `M 0 = 0` and a.e. bounded increments lies in every `Lᵖ`** on a finite
measure: telescoping the increments, `|Mₙ| ≤ n c` a.e. This is what lets the exponential
supermartingale and the laws of the iterated logarithm assume only the increment bound. -/
lemma _root_.MeasureTheory.Martingale.memLp_of_abs_increment_le [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) {c : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {p : ℝ≥0∞} (n : ℕ) :
    MemLp (M n) p μ := by
  refine MemLp.of_bound ((hM.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable
    ((n : ℝ) * c) ?_
  filter_upwards [ae_all_iff.mpr hb, hM0] with ω hbω hM0ω
  simp only [Pi.zero_apply] at hM0ω
  rw [Real.norm_eq_abs]
  have htel : (∑ k ∈ range n, (M (k + 1) ω - M k ω)) = M n ω := by
    rw [sum_range_sub (M · ω) n, hM0ω, sub_zero]
  calc |M n ω| = |∑ k ∈ range n, (M (k + 1) ω - M k ω)| := by rw [htel]
    _ ≤ ∑ k ∈ range n, |M (k + 1) ω - M k ω| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range n, c := sum_le_sum fun k _ ↦ hbω k
    _ = n * c := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### Definition and algebra -/

/-- The **predictable quadratic variation** `⟨M⟩` of a process `M`, defined as the
predictable part of `M²` in its Doob decomposition. -/
noncomputable def predQuadVar (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  predictablePart (M · ^ 2) ℱ μ

/-- `⟨M⟩_n` is the defining sum `∑_{i<n} μ[M_{i+1}² - M_i² | ℱ_i]`. For a martingale the summands
simplify to `μ[(ΔM_i)² | ℱ_i]` (`predQuadVar_ae_eq_sum`). -/
lemma predQuadVar_eq_sum (n : ℕ) :
    predQuadVar M ℱ μ n
      = ∑ i ∈ range n, μ[(fun ω ↦ M (i + 1) ω ^ 2) - fun ω ↦ M i ω ^ 2 | ℱ i] := rfl

@[simp, specifies predQuadVar "fixes the additive constant, which the increment formula \
`predQuadVar_succ_sub_eq` alone leaves free; the two together give `⟨M⟩ₙ = ∑_{i<n} μ[(ΔMᵢ)²|ℱᵢ]`"]
lemma predQuadVar_zero : predQuadVar M ℱ μ 0 = 0 := predictablePart_zero

@[simp]
lemma predQuadVar_zero_apply (ω : Ω) : predQuadVar M ℱ μ 0 ω = 0 := by
  rw [predQuadVar_zero, Pi.zero_apply]

/-- `⟨M⟩_{n+1} = ⟨M⟩_n + μ[M_{n+1}² - M_n² | ℱ_n]`: the one-step form of the defining sum, before
the martingale simplification of the cross term (`predQuadVar_succ_sub_eq`). -/
lemma predQuadVar_add_one (n : ℕ) :
    predQuadVar M ℱ μ (n + 1)
      = predQuadVar M ℱ μ n + μ[(fun ω ↦ M (n + 1) ω ^ 2) - fun ω ↦ M n ω ^ 2 | ℱ n] :=
  predictablePart_add_one n

/-- The predictable quadratic variation is invariant under negation: `⟨-M⟩ = ⟨M⟩`, since
`(-M)² = M²` pointwise. -/
@[simp]
lemma predQuadVar_neg (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) :
    predQuadVar (-M) ℱ μ = predQuadVar M ℱ μ := by simp [predQuadVar]

/-- **Scaling**: `⟨c • M⟩ = c² ⟨M⟩` a.e., since `(c M)² = c² M²` pointwise and the predictable part
is linear (`predictablePart_smul`). -/
lemma predQuadVar_const_smul (c : ℝ) (n : ℕ) :
    predQuadVar (c • M) ℱ μ n =ᵐ[μ] c ^ 2 • predQuadVar M ℱ μ n := by
  have h : ((c • M) · ^ 2) = c ^ 2 • (M · ^ 2) := by ext; simp [mul_pow]
  rw [predQuadVar, h]
  exact predictablePart_smul (c ^ 2) n

/-! ### Measurability

`⟨M⟩` is adapted and predictable: `⟨M⟩_{n+1}` is already `ℱ_n`-measurable, being a sum of
conditional expectations given `ℱ_0, …, ℱ_n`. No hypothesis on `M` is needed. -/

lemma stronglyAdapted_predQuadVar : StronglyAdapted ℱ (predQuadVar M ℱ μ) :=
  stronglyAdapted_predictablePart' (f := (M · ^ 2))

lemma stronglyMeasurable_predQuadVar_succ (n : ℕ) :
    StronglyMeasurable[ℱ n] (predQuadVar M ℱ μ (n + 1)) :=
  stronglyAdapted_predictablePart (f := (M · ^ 2)) n

lemma isStronglyPredictable_predQuadVar : IsStronglyPredictable ℱ (predQuadVar M ℱ μ) :=
  isPredictable_predictablePart (f := (M · ^ 2))

/-- **`⟨M⟩ n` is integrable**, being a finite sum of conditional expectations. -/
@[fun_prop]
lemma integrable_predQuadVar (n : ℕ) : Integrable (predQuadVar M ℱ μ n) μ := by
  rw [predQuadVar_eq_sum]
  exact integrable_finsetSum' _ fun _ _ ↦ integrable_condExp

/-! ### The increment formula -/

/-- **Increment of the quadratic variation.**
For a martingale `M`, the increment of `⟨M⟩` is the conditional second moment of
the increment of `M`: `⟨M⟩ (n+1) - ⟨M⟩ n = μ[(M (n+1) - M n)² | ℱ n]` a.e.
(the cross term `2 Mₙ ΔMₙ` vanishes by the martingale property). -/
@[specifies predQuadVar "the textbook increment formula `Δ⟨M⟩ₙ = μ[(ΔMₙ)²|ℱₙ]`, which is what \
\"predictable quadratic variation\" means; the definition itself is the Doob predictable part of \
`M²`, and this is the identification a referee needs"]
lemma predQuadVar_succ_sub_eq (hM : Martingale M ℱ μ) (n : ℕ)
    (hd2 : MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      =ᵐ[μ] μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] := by
  -- `M(n+1)² - Mₙ² = (M(n+1) - Mₙ)² + (Mₙ ΔMₙ + Mₙ ΔMₙ)` pointwise.
  have hfun : ((fun ω ↦ M (n + 1) ω ^ 2) - fun ω ↦ M n ω ^ 2)
      = (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2)
        + (M n * (M (n + 1) - M n) + M n * (M (n + 1) - M n)) := by ext; simp; ring
  rw [predQuadVar_add_one, add_sub_cancel_left, hfun]
  -- the cross term has conditional expectation `0`.
  have hcross : μ[M n * (M (n + 1) - M n) + M n * (M (n + 1) - M n) | ℱ n] =ᵐ[μ] 0 := by
    have hcd : μ[M (n + 1) - M n | ℱ n] =ᵐ[μ] 0 := hM.condExp_sub_ae_eq_zero (Nat.le_succ n)
    have hpull : μ[M n * (M (n + 1) - M n) | ℱ n] =ᵐ[μ] M n * μ[M (n + 1) - M n | ℱ n] :=
      condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable n) hprod
        ((hM.integrable (n + 1)).sub (hM.integrable n))
    refine (condExp_add hprod hprod (ℱ n)).trans ?_
    filter_upwards [hpull, hcd] with ω ep ec
    have hz : μ[M (n + 1) - M n | ℱ n] ω = 0 := by simpa using ec
    simp only [Pi.add_apply, Pi.zero_apply, ep, Pi.mul_apply, hz, mul_zero, add_zero]
  refine (condExp_add hd2.integrable_sq (hprod.add hprod) (ℱ n)).trans ?_
  filter_upwards [hcross] with ω e
  simp [e]

/-- **`⟨M⟩` is non-decreasing.**
The quadratic variation of a martingale increases, since its increment is a
conditional second moment, hence nonnegative. -/
lemma predQuadVar_le_succ (hM : Martingale M ℱ μ) (n : ℕ)
    (hd2 : MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    predQuadVar M ℱ μ n ≤ᵐ[μ] predQuadVar M ℱ μ (n + 1) := by
  have hnn : 0 ≤ᵐ[μ] μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] :=
    condExp_nonneg (by filter_upwards with ω; positivity)
  filter_upwards [predQuadVar_succ_sub_eq hM n hd2 hprod, hnn] with ω e hn
  simp only [Pi.sub_apply, Pi.zero_apply] at e hn
  grind

/-- **`⟨M⟩` is monotone.** Almost surely the whole path `n ↦ ⟨M⟩ n ω` is nondecreasing, since
each increment is a conditional second moment (hence nonnegative, `predQuadVar_le_succ`). -/
lemma predQuadVar_mono (hM : Martingale M ℱ μ) (hM2 : ∀ n, MemLp (M n) 2 μ) :
    ∀ᵐ ω ∂μ, Monotone (predQuadVar M ℱ μ · ω) := by
  filter_upwards [ae_all_iff.mpr fun n ↦ predQuadVar_le_succ hM n
    (memLp_increment (hM2 n) (hM2 (n + 1))) (integrable_mul_increment (hM2 n) (hM2 (n + 1)))]
    with ω hω
  exact monotone_nat_of_le_succ fun n ↦ hω n

/-- **The predictable quadratic variation is nonnegative.** Since `⟨M⟩ 0 = 0` and `⟨M⟩` is
nondecreasing (`predQuadVar_mono`), `0 ≤ ⟨M⟩ n` a.e. -/
lemma predQuadVar_nonneg (hM : Martingale M ℱ μ) (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    0 ≤ᵐ[μ] predQuadVar M ℱ μ n := by
  filter_upwards [predQuadVar_mono hM hM2] with ω hmono
  simpa using hmono (Nat.zero_le n)

/-- **The textbook formula**: `⟨M⟩_n = ∑_{i<n} μ[(ΔM_i)² | ℱ_i]` a.e., for a square-integrable
martingale. -/
lemma predQuadVar_ae_eq_sum (hM : Martingale M ℱ μ) (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    predQuadVar M ℱ μ n =ᵐ[μ] ∑ i ∈ range n, μ[fun ω ↦ (M (i + 1) ω - M i ω) ^ 2 | ℱ i] := by
  rw [predQuadVar_eq_sum]
  refine eventuallyEq_sum fun i _ ↦ ?_
  have h := predQuadVar_succ_sub_eq hM i (memLp_increment (hM2 i) (hM2 (i + 1)))
    (integrable_mul_increment (hM2 i) (hM2 (i + 1)))
  rwa [predQuadVar_add_one, add_sub_cancel_left] at h

/-! ### Telescoping

`⟨M⟩_0 = 0`, so `⟨M⟩_n` is the sum of its increments, and a.e. bounds on the increments become
a.s. bounds on the whole path. -/

/-- `⟨M⟩_n = ∑_{k<n} (⟨M⟩_{k+1} - ⟨M⟩_k)`, pointwise. -/
lemma predQuadVar_eq_sum_succ_sub (n : ℕ) (ω : Ω) :
    predQuadVar M ℱ μ n ω
      = ∑ k ∈ range n, (predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω) := by
  rw [sum_range_sub (predQuadVar M ℱ μ · ω), predQuadVar_zero_apply, sub_zero]

/-- **Upper bounds on the increments bound the path**: if `⟨M⟩_{k+1} - ⟨M⟩_k ≤ v k` a.e. for
every `k`, then a.s. `⟨M⟩_n ≤ ∑_{k<n} v k` for every `n`. -/
lemma predQuadVar_le_sum_of_succ_sub_le {v : ℕ → Ω → ℝ}
    (h : ∀ k, ∀ᵐ ω ∂μ, predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω ≤ v k ω) :
    ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ ∑ k ∈ range n, v k ω := by
  filter_upwards [ae_all_iff.mpr h] with ω hω n
  rw [predQuadVar_eq_sum_succ_sub]
  exact sum_le_sum fun k _ ↦ hω k

/-- **Lower bounds on the increments bound the path**: if `v k ≤ ⟨M⟩_{k+1} - ⟨M⟩_k` a.e. for
every `k`, then a.s. `∑_{k<n} v k ≤ ⟨M⟩_n` for every `n`. -/
lemma sum_le_predQuadVar_of_le_succ_sub {v : ℕ → Ω → ℝ}
    (h : ∀ k, ∀ᵐ ω ∂μ, v k ω ≤ predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω) :
    ∀ᵐ ω ∂μ, ∀ n, ∑ k ∈ range n, v k ω ≤ predQuadVar M ℱ μ n ω := by
  filter_upwards [ae_all_iff.mpr h] with ω hω n
  rw [predQuadVar_eq_sum_succ_sub]
  exact sum_le_sum fun k _ ↦ hω k

/-- **Linear upper bound on `⟨M⟩` for bounded increments.** If `|ΔM_i| ≤ c` a.e., then each
increment `⟨M⟩_{k+1} - ⟨M⟩_k = μ[(ΔM_k)² | ℱ_k]` is at most `c²`, so `⟨M⟩_n ≤ c² n` a.s. No
square-integrability of `M` itself is needed: the bound on `ΔM_k` supplies the integrability the
increment formula asks for. -/
lemma predQuadVar_le_of_bound [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) {c : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ c ^ 2 * n := by
  have hae : ∀ n, AEStronglyMeasurable (M n) μ := fun n ↦ (hM.integrable n).aestronglyMeasurable
  have hstep : ∀ k, ∀ᵐ ω ∂μ,
      predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω ≤ c ^ 2 := fun k ↦ by
    have hd2 : MemLp (fun ω ↦ M (k + 1) ω - M k ω) 2 μ :=
      memLp_increment_of_bound (hae k) (hae (k + 1)) (hb k)
    have hcond : μ[fun ω ↦ (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
      have h := condExp_mono (m := ℱ k) hd2.integrable_sq (integrable_const (c ^ 2)) <| by
        filter_upwards [hb k] with ω h
        exact sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
      rwa [condExp_const (ℱ.le k)] at h
    filter_upwards [predQuadVar_succ_sub_eq hM k hd2
      (integrable_mul_increment_of_bound (hM.integrable k) (hae (k + 1)) (hb k)), hcond]
      with ω e ec
    rw [Pi.sub_apply] at e
    rw [e]
    exact ec
  filter_upwards [predQuadVar_le_sum_of_succ_sub_le hstep] with ω hω n
  exact (hω n).trans_eq (by rw [sum_const, card_range, nsmul_eq_mul, mul_comm])

/-! ### The Doob decomposition of `M²` -/

/-- **`M² - ⟨M⟩` is a martingale.**
For an adapted process `M` with square-integrable values, `M² - ⟨M⟩` is a
martingale, being the martingale part of `M²` in its Doob decomposition. -/
@[specifies predQuadVar "the compensator property, the half of `IsPredQuadVar` that carries the \
content: `⟨M⟩` is what turns `M²` into a martingale"]
lemma martingale_sq_sub_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, MemLp (M n) 2 μ) :
    Martingale (fun n ↦ (fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) ℱ μ :=
  martingale_martingalePart (fun n ↦ (hM n).pow 2) (fun n ↦ (hM2 n).integrable_sq)

/-- **The square of a martingale is a submartingale.** For a square-integrable martingale `M`,
`μ[M_{n+1}² | ℱ_n] = M_n² + μ[(ΔM_n)² | ℱ_n] ≥ M_n²`. This is Doob's `L²` submartingale, the input
to Doob's maximal inequality. -/
lemma submartingale_sq [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) :
    Submartingale (fun n ω ↦ M n ω ^ 2) ℱ μ := by
  refine submartingale_nat (fun n ↦ (hM.stronglyAdapted n).pow 2) (fun n ↦ (hM2 n).integrable_sq)
    fun i ↦ ?_
  -- `μ[M_{i+1}² - M_i² | ℱ_i] = Δ⟨M⟩_i = μ[(ΔM_i)² | ℱ_i] ≥ 0`.
  have hnn : 0 ≤ᵐ[μ] μ[(fun ω ↦ M (i + 1) ω ^ 2) - fun ω ↦ M i ω ^ 2 | ℱ i] := by
    have h := predQuadVar_succ_sub_eq hM i (memLp_increment (hM2 i) (hM2 (i + 1)))
      (integrable_mul_increment (hM2 i) (hM2 (i + 1)))
    rw [predQuadVar_add_one, add_sub_cancel_left] at h
    exact (condExp_nonneg (by filter_upwards with ω; positivity)).trans h.symm.le
  have hsub : μ[(fun ω ↦ M (i + 1) ω ^ 2) - fun ω ↦ M i ω ^ 2 | ℱ i]
      =ᵐ[μ] μ[fun ω ↦ M (i + 1) ω ^ 2 | ℱ i] - fun ω ↦ M i ω ^ 2 := by
    refine (condExp_sub (hM2 (i + 1)).integrable_sq (hM2 i).integrable_sq _).trans ?_
    rw [condExp_of_stronglyMeasurable (ℱ.le i) (f := fun ω ↦ M i ω ^ 2)
      ((hM.stronglyAdapted i).pow 2) (hM2 i).integrable_sq]
  filter_upwards [hnn, hsub] with ω h1 h2
  simp only [Pi.sub_apply, Pi.zero_apply] at h1 h2
  linarith

/-! ### Characterization

`predQuadVar` is *defined* by a formula — the Doob predictable part of `M²` — and a formula is not
a reason to call it a quadratic variation. `IsPredQuadVar` is the property that does: `A` is
predictable, starts at `0`, and **compensates** `M²`, meaning `M² - A` is a martingale. The
compensator property is the content; predictability and `A 0 = 0` are what make it pin `A` down,
and they do so exactly, up to `Indistinguishable`. -/

/-- **`A` is a predictable quadratic variation of `M`**: `A` compensates `M²`, in that `M² - A` is
a martingale, and `A` is predictable and null at `0`.

This is the Doob decomposition of `M²` stated as a property rather than computed by a formula. It
holds of `predQuadVar M ℱ μ` (`isPredQuadVar_predQuadVar`) and of nothing else, up to
indistinguishability (`IsPredQuadVar.indistinguishable_predQuadVar`). -/
@[characterization property predQuadVar "the compensator of `M²`: predictable, null at `0`, and \
turning `M²` into a martingale"]
structure IsPredQuadVar (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    (A : ℕ → Ω → ℝ) : Prop where
  /-- `A` compensates `M²`. This is the content of the property; the other three fields are the
  regularity and the normalisation that turn it from something `A` happens to satisfy into a
  description of `A`. -/
  martingale_sq_sub : Martingale (fun n ↦ (fun ω ↦ M n ω ^ 2) - A n) ℱ μ
  /-- `A` is predictable (`MeasureTheory.IsStronglyPredictable`; for `ℕ`-indexed processes, this
  says `A (n + 1)` is `ℱ n`-measurable). This is what makes the compensator property pin `A` down.
  Without it there is nothing to pin: adding to `A` any martingale null at `0` leaves `M² - A` a
  martingale and `A 0 = 0` intact. -/
  predictable : IsStronglyPredictable ℱ A
  /-- `A` starts at `0`, which fixes the additive constant the other fields leave free. -/
  zero : A 0 = 0
  /-- Each `A n` is integrable, so that `A` can sit in a Doob decomposition at all. -/
  integrable : ∀ n, Integrable (A n) μ

/-- **`⟨M⟩` compensates `M²`** — the existence half of the characterization: `predQuadVar` has the
property that describes a predictable quadratic variation. -/
@[characterization existence]
lemma isPredQuadVar_predQuadVar [IsFiniteMeasure μ] (hM : StronglyAdapted ℱ M)
    (hM2 : ∀ n, MemLp (M n) 2 μ) :
    IsPredQuadVar M ℱ μ (predQuadVar M ℱ μ) where
  martingale_sq_sub := martingale_sq_sub_predQuadVar hM hM2
  predictable := isStronglyPredictable_predQuadVar
  zero := predQuadVar_zero
  integrable := integrable_predQuadVar

/-- **Nothing else compensates `M²`** — the uniqueness half of the characterization: any `A` that
is predictable, null at `0` and compensates `M²` is indistinguishable from `⟨M⟩`. This is the
uniqueness of the Doob decomposition (`predictablePart_add_ae_eq`) applied to the martingale
`M² - A` and the predictable process `A`, which gives one null set per time; the index is `ℕ`, so
that is already indistinguishability. -/
@[characterization uniqueness]
lemma IsPredQuadVar.indistinguishable_predQuadVar [IsFiniteMeasure μ] {A : ℕ → Ω → ℝ}
    (hA : IsPredQuadVar M ℱ μ A) : Indistinguishable μ A (predQuadVar M ℱ μ) := by
  -- `M²` is the sum of the martingale `M² - A` and the predictable process `A`.
  have hsum : (fun n ↦ (fun ω ↦ M n ω ^ 2) - A n) + A = fun n ↦ M n ^ 2 := by
    funext n ω
    simp
  refine .of_forall_ae_eq fun n ↦ ?_
  have h := predictablePart_add_ae_eq (ℱ := ℱ) (μ := μ) hA.martingale_sq_sub
    (fun n ↦ hA.predictable.measurable_add_one n) hA.zero hA.integrable n
  rw [hsum] at h
  exact h.symm

/-! ### The discrete Itô isometry -/

/-- **Discrete Itô isometry, general form**: `E[M_n²] = E[M_0²] + E[⟨M⟩_n]` for an adapted
square-integrable process, since the martingale `M² - ⟨M⟩` has constant expectation and
`⟨M⟩_0 = 0`. -/
lemma integral_sq_eq_integral_sq_zero_add_integral_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ = ∫ ω, M 0 ω ^ 2 ∂μ + ∫ ω, predQuadVar M ℱ μ n ω ∂μ := by
  have h := (martingale_sq_sub_predQuadVar hM hM2).integral_eq (Nat.zero_le n)
  simp only [Pi.sub_apply, predQuadVar_zero_apply, sub_zero] at h
  rw [integral_sub (hM2 n).integrable_sq (integrable_predQuadVar n)] at h
  linarith

/-- **Expected quadratic variation equals the second moment.**
For an adapted, square-integrable process `M` with `M 0 = 0` a.e., `E[M n ²] = E[⟨M⟩ n]`. This
is the discrete Itô isometry: `M² - ⟨M⟩` is a martingale starting at `0`, so its expectation
stays `0`. -/
lemma integral_sq_eq_integral_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hM0 : M 0 =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ = ∫ ω, predQuadVar M ℱ μ n ω ∂μ := by
  have h0 : ∫ ω, M 0 ω ^ 2 ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hM0] with ω hω
    simp [hω]
  rw [integral_sq_eq_integral_sq_zero_add_integral_predQuadVar hM hM2 n, h0, zero_add]

/-- **Integrated increment of `⟨M⟩`.** The expected increment of the quadratic
variation is the second moment of the martingale increment:
`E[⟨M⟩ (n+1)] - E[⟨M⟩ n] = E[(ΔM (n+1))²]`. -/
lemma integral_predQuadVar_succ_sub [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    ∫ ω, predQuadVar M ℱ μ (n + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := by
  have h1 := predQuadVar_succ_sub_eq hM n (memLp_increment (hM2 n) (hM2 (n + 1)))
    (integrable_mul_increment (hM2 n) (hM2 (n + 1)))
  calc ∫ ω, predQuadVar M ℱ μ (n + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∫ ω, (predQuadVar M ℱ μ (n + 1) ω - predQuadVar M ℱ μ n ω) ∂μ :=
        (integral_sub (integrable_predQuadVar (n + 1)) (integrable_predQuadVar n)).symm
    _ = ∫ ω, (μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n]) ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h1] with ω hω
        simpa [Pi.sub_apply] using hω
    _ = ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := integral_condExp (ℱ.le n)

/-- **`E[⟨M⟩_n] = ∑_{k<n} E[(ΔM_k)²]`**, telescoping `integral_predQuadVar_succ_sub`. -/
lemma integral_predQuadVar_eq_sum [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    ∫ ω, predQuadVar M ℱ μ n ω ∂μ = ∑ k ∈ range n, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by
  calc ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∑ k ∈ range n,
          (∫ ω, predQuadVar M ℱ μ (k + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ k ω ∂μ) := by
        rw [sum_range_sub (fun k ↦ ∫ ω, predQuadVar M ℱ μ k ω ∂μ)]
        simp
    _ = ∑ k ∈ range n, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ :=
        sum_congr rfl fun k _ ↦ integral_predQuadVar_succ_sub hM hM2 k

/-- **Orthogonality of increments**: `E[M_n²] = ∑_{k<n} E[(ΔM_k)²]` for a square-integrable
martingale null at `0`. -/
lemma integral_sq_eq_sum_integral_increment_sq [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (hM0 : M 0 =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ = ∑ k ∈ range n, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by
  rw [integral_sq_eq_integral_predQuadVar hM.stronglyAdapted hM2 hM0,
    integral_predQuadVar_eq_sum hM hM2]

/-- **Martingale `L²` growth bound.**
If every increment has second moment `≤ σ²`, then `E[M n ²] ≤ σ² n`. This is the
discrete Itô isometry combined with the telescoping of `⟨M⟩`. -/
lemma integral_sq_le_of_increment_bound [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (hM0 : M 0 =ᵐ[μ] 0) (σ2 : ℝ)
    (hinc : ∀ n, ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ ≤ σ2) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ ≤ σ2 * n := by
  rw [integral_sq_eq_sum_integral_increment_sq hM hM2 hM0]
  calc ∑ k ∈ range n, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ
      ≤ ∑ _k ∈ range n, σ2 := sum_le_sum fun k _ ↦ hinc k
    _ = σ2 * n := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]

/-! ### Orthogonal martingales -/

/-- **Product of conditionally orthogonal martingales is a martingale.**
If `M`, `N` are martingales whose increments are conditionally orthogonal,
`μ[ΔM (i+1) · ΔN (i+1) | ℱ i] = 0`, then `M · N` is a martingale. The integrability of the
products `M i * N j` is taken as a hypothesis. -/
lemma martingale_mul [IsFiniteMeasure μ] {N : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hN : Martingale N ℱ μ)
    (hMN : ∀ i j, Integrable (M i * N j) μ)
    (hortho : ∀ i, μ[(M (i + 1) - M i) * (N (i + 1) - N i) | ℱ i] =ᵐ[μ] 0) :
    Martingale (fun n ↦ M n * N n) ℱ μ := by
  -- `hB`, `hC`, `hD` are algebraic consequences of `hMN`: expand each product.
  have hB : ∀ i, Integrable (M i * (N (i + 1) - N i)) μ := fun i ↦
    ((hMN i (i + 1)).sub (hMN i i)).congr
      (by filter_upwards with ω; simp only [Pi.mul_apply, Pi.sub_apply]; ring)
  have hC : ∀ i, Integrable (N i * (M (i + 1) - M i)) μ := fun i ↦
    (((hMN (i + 1) i).sub (hMN i i)).congr
      (by filter_upwards with ω; simp only [Pi.mul_apply, Pi.sub_apply]; ring))
  have hD : ∀ i, Integrable ((M (i + 1) - M i) * (N (i + 1) - N i)) μ := fun i ↦
    ((((hMN (i + 1) (i + 1)).sub (hMN (i + 1) i)).sub
      ((hMN i (i + 1)).sub (hMN i i)))).congr
      (by filter_upwards with ω; simp only [Pi.mul_apply, Pi.sub_apply]; ring)
  have hMN : ∀ n, Integrable (M n * N n) μ := fun n ↦ hMN n n
  refine martingale_nat
    (fun n ↦ (hM.stronglyMeasurable n).mul (hN.stronglyMeasurable n)) hMN (fun i ↦ ?_)
  -- Increments of `M` and `N` have vanishing conditional expectation.
  have hcdM : μ[M (i + 1) - M i | ℱ i] =ᵐ[μ] 0 := hM.condExp_sub_ae_eq_zero (Nat.le_succ i)
  have hcdN : μ[N (i + 1) - N i | ℱ i] =ᵐ[μ] 0 := hN.condExp_sub_ae_eq_zero (Nat.le_succ i)
  -- Conditional expectations of the four pieces of the product increment.
  have eA : μ[M i * N i | ℱ i] = M i * N i :=
    condExp_of_stronglyMeasurable (ℱ.le i)
      ((hM.stronglyMeasurable i).mul (hN.stronglyMeasurable i)) (hMN i)
  have eB : μ[M i * (N (i + 1) - N i) | ℱ i] =ᵐ[μ] 0 := by
    have hpull : μ[M i * (N (i + 1) - N i) | ℱ i] =ᵐ[μ] M i * μ[N (i + 1) - N i | ℱ i] :=
      condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable i) (hB i)
        ((hN.integrable (i + 1)).sub (hN.integrable i))
    filter_upwards [hpull, hcdN] with ω ep ec
    have hz : μ[N (i + 1) - N i | ℱ i] ω = 0 := by simpa using ec
    simp only [ep, Pi.mul_apply, hz, mul_zero, Pi.zero_apply]
  have eC : μ[N i * (M (i + 1) - M i) | ℱ i] =ᵐ[μ] 0 := by
    have hpull : μ[N i * (M (i + 1) - M i) | ℱ i] =ᵐ[μ] N i * μ[M (i + 1) - M i | ℱ i] :=
      condExp_mul_of_stronglyMeasurable_left (hN.stronglyMeasurable i) (hC i)
        ((hM.integrable (i + 1)).sub (hM.integrable i))
    filter_upwards [hpull, hcdM] with ω ep ec
    have hz : μ[M (i + 1) - M i | ℱ i] ω = 0 := by simpa using ec
    simp only [ep, Pi.mul_apply, hz, mul_zero, Pi.zero_apply]
  -- Pointwise decomposition of the product increment.
  have hdecomp : M (i + 1) * N (i + 1)
      = M i * N i + M i * (N (i + 1) - N i) + N i * (M (i + 1) - M i)
        + (M (i + 1) - M i) * (N (i + 1) - N i) := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  have hAB : Integrable (M i * N i + M i * (N (i + 1) - N i)) μ := (hMN i).add (hB i)
  have hABC : Integrable
      (M i * N i + M i * (N (i + 1) - N i) + N i * (M (i + 1) - M i)) μ := hAB.add (hC i)
  refine Filter.EventuallyEq.symm ?_
  rw [hdecomp]
  filter_upwards [condExp_add hABC (hD i) (ℱ i), condExp_add hAB (hC i) (ℱ i),
    condExp_add (hMN i) (hB i) (ℱ i), eB, eC, hortho i] with ω h1 h2 h3 hb hc hd
  simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 hb hc hd
  rw [h1, h2, h3, congrFun eA ω, hb, hc, hd]
  ring

/-- **Additivity of the quadratic variation for orthogonal martingales.**
If `M · N` is a martingale (e.g. `M`, `N` are conditionally orthogonal martingales, see
`martingale_mul`), then `⟨M + N⟩ = ⟨M⟩ + ⟨N⟩` a.e. This is predictable-part linearity together
with the fact that the predictable part of the martingale `M · N` vanishes. -/
lemma predQuadVar_add_of_martingale_mul {N : ℕ → Ω → ℝ}
    (hM2 : ∀ n, MemLp (M n) 2 μ) (hN2 : ∀ n, MemLp (N n) 2 μ)
    (hmart : Martingale (fun n ↦ M n * N n) ℱ μ) (n : ℕ) :
    predQuadVar (fun k ↦ M k + N k) ℱ μ n =ᵐ[μ] predQuadVar M ℱ μ n + predQuadVar N ℱ μ n := by
  have hproc : (fun k ↦ (M k + N k) ^ 2)
      = (M · ^ 2) + (N · ^ 2) + (2 : ℝ) • (fun k ↦ M k * N k) := by
    ext; simp; ring
  have hMint : ∀ k, Integrable ((M · ^ 2) k) μ := fun k ↦ (hM2 k).integrable_sq
  have hNint : ∀ k, Integrable ((N · ^ 2) k) μ := fun k ↦ (hN2 k).integrable_sq
  have hMNint : ∀ k, Integrable (((2 : ℝ) • fun k ↦ M k * N k) k) μ := fun k ↦ by
    simpa using ((hM2 k).integrable_mul (hN2 k)).smul (2 : ℝ)
  -- Split `⟨M+N⟩` by linearity of the predictable part.
  have h1 : predQuadVar (fun k ↦ M k + N k) ℱ μ n
      =ᵐ[μ] predictablePart ((M · ^ 2) + fun k ↦ N k ^ 2) ℱ μ n
        + predictablePart ((2 : ℝ) • fun k ↦ M k * N k) ℱ μ n := by
    rw [predQuadVar, hproc]
    exact predictablePart_add (fun k ↦ (hMint k).add (hNint k)) hMNint n
  have h2 : predictablePart ((M · ^ 2) + fun k ↦ N k ^ 2) ℱ μ n
      =ᵐ[μ] predQuadVar M ℱ μ n + predQuadVar N ℱ μ n := by
    simpa only [predQuadVar] using predictablePart_add hMint hNint n
  have h3 : predictablePart ((2 : ℝ) • fun k ↦ M k * N k) ℱ μ n =ᵐ[μ] 0 := by
    have hs := predictablePart_smul (ℱ := ℱ) (μ := μ) (f := fun k ↦ M k * N k) (2 : ℝ) n
    have hz := hmart.predictablePart_eq_zero n
    filter_upwards [hs, hz] with ω es ez
    simp only [Pi.smul_apply, Pi.zero_apply] at es ez ⊢
    rw [es, ez, smul_zero]
  filter_upwards [h1, h2, h3] with ω a1 a2 a3
  simp only [Pi.add_apply, Pi.zero_apply] at a1 a2 a3 ⊢
  rw [a1, a2, a3, add_zero]

end AlphaRAR
