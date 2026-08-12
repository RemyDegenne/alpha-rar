/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.Process
public import Mathlib.Probability.Martingale.Centering
public meta import LeanSpec

/-!
# Predictable quadratic variation

For a square-integrable martingale `M` (with `M 0 = 0`), the predictable quadratic
variation `⟨M⟩` is the predictable part of the submartingale `M²` in its Doob
decomposition, and `M² - ⟨M⟩` is a martingale. This file records these as thin
wrappers around Mathlib's discrete Doob decomposition.

## Main results

* `AlphaRAR.predQuadVar`: the predictable quadratic variation (blueprint `def:pred_qv`).
* `AlphaRAR.martingale_sq_sub_predQuadVar`: `M² - ⟨M⟩` is a martingale
  (blueprint `lem:qv_mart`).
* `AlphaRAR.IsPredQuadVar`: the property that characterizes `⟨M⟩` — predictable, null at `0`,
  and compensating `M²` — together with the two theorems saying `⟨M⟩` has it and nothing else
  does, up to indistinguishability.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

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

/-- The **predictable quadratic variation** `⟨M⟩` of a process `M`, defined as the
predictable part of `M²` in its Doob decomposition (blueprint `def:pred_qv`). -/
noncomputable def predQuadVar (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  predictablePart (fun n ↦ M n ^ 2) ℱ μ

@[simp, specifies predQuadVar "fixes the additive constant, which the increment formula \
`predQuadVar_succ_sub_eq` alone leaves free; the two together give `⟨M⟩ₙ = ∑_{i<n} μ[(ΔMᵢ)²|ℱᵢ]`"]
lemma predQuadVar_zero : predQuadVar M ℱ μ 0 = 0 := predictablePart_zero

/-- The predictable quadratic variation is invariant under negation: `⟨-M⟩ = ⟨M⟩`, since
`(-M)² = M²` pointwise. -/
@[simp]
lemma predQuadVar_neg (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) :
    predQuadVar (-M) ℱ μ = predQuadVar M ℱ μ := by simp [predQuadVar]

/-- The increment of `⟨M⟩` is the conditional expectation of the increment of `M²`:
`⟨M⟩ (n+1) - ⟨M⟩ n = μ[M (n+1)² - M n² | ℱ n]` (blueprint `lem:qv_incr`, before the
martingale simplification of the cross term). -/
lemma predQuadVar_succ_sub (n : ℕ) :
    predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      = μ[(fun ω ↦ M (n + 1) ω ^ 2) - fun ω ↦ M n ω ^ 2 | ℱ n] := by
  rw [predQuadVar, predictablePart_add_one]
  abel

/-- **Increment of the quadratic variation** (blueprint `lem:qv_incr`).
For a martingale `M`, the increment of `⟨M⟩` is the conditional second moment of
the increment of `M`: `⟨M⟩ (n+1) - ⟨M⟩ n = μ[(M (n+1) - M n)² | ℱ n]` a.e.
(the cross term `2 Mₙ ΔMₙ` vanishes by the martingale property). -/
@[specifies predQuadVar "the textbook increment formula `Δ⟨M⟩ₙ = μ[(ΔMₙ)²|ℱₙ]`, which is what \
\"predictable quadratic variation\" means; the definition itself is the Doob predictable part of \
`M²`, and this is the identification a referee needs"]
lemma predQuadVar_succ_sub_eq [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (n : ℕ)
    (hd2 : MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      =ᵐ[μ] μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] := by
  -- `M(n+1)² - Mₙ² = (M(n+1) - Mₙ)² + (Mₙ ΔMₙ + Mₙ ΔMₙ)` pointwise.
  have hfun : ((fun ω ↦ M (n + 1) ω ^ 2) - fun ω ↦ M n ω ^ 2)
      = (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2)
        + (M n * (M (n + 1) - M n) + M n * (M (n + 1) - M n)) := by ext; simp; ring
  rw [predQuadVar_succ_sub, hfun]
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

/-- **`⟨M⟩` is non-decreasing** (blueprint `lem:qv_incr`, monotonicity part).
The quadratic variation of a martingale increases, since its increment is a
conditional second moment, hence nonnegative. -/
lemma predQuadVar_le_succ [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (n : ℕ)
    (hd2 : MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    predQuadVar M ℱ μ n ≤ᵐ[μ] predQuadVar M ℱ μ (n + 1) := by
  have hinc := predQuadVar_succ_sub_eq hM n hd2 hprod
  have hnn : (fun _ ↦ 0) ≤ᵐ[μ] μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] := by
    refine condExp_nonneg ?_
    filter_upwards with ω
    positivity
  filter_upwards [hinc, hnn] with ω e hn
  simp only [Pi.sub_apply] at e hn
  grind

/-- **`⟨M⟩` is monotone** (blueprint `lem:qv_incr`, monotonicity part). Almost surely the whole
path `n ↦ ⟨M⟩ n ω` is nondecreasing, since each increment is a conditional second moment (hence
nonnegative, `predQuadVar_le_succ`). -/
lemma predQuadVar_mono [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hd2 : ∀ n, MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ)
    (hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ) :
    ∀ᵐ ω ∂μ, Monotone (predQuadVar M ℱ μ · ω) := by
  filter_upwards [ae_all_iff.mpr fun n ↦ predQuadVar_le_succ hM n (hd2 n) (hprod n)] with ω hω
  exact monotone_nat_of_le_succ fun n ↦ hω n

/-- **The predictable quadratic variation is nonnegative.** Since `⟨M⟩ 0 = 0` and `⟨M⟩` is
nondecreasing (`predQuadVar_mono`), `0 ≤ ⟨M⟩ n` a.e. -/
lemma predQuadVar_nonneg [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hd2 : ∀ n, MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ)
    (hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ) (n : ℕ) :
    0 ≤ᵐ[μ] predQuadVar M ℱ μ n := by
  filter_upwards [predQuadVar_mono hM hd2 hprod] with ω hmono
  have h0n : predQuadVar M ℱ μ 0 ω ≤ predQuadVar M ℱ μ n ω := hmono (Nat.zero_le n)
  rw [show predQuadVar M ℱ μ 0 ω = 0 from by rw [predQuadVar_zero]; rfl] at h0n
  simpa using h0n

/-- **Linear upper bound on `⟨M⟩` for bounded increments.** If `|ΔM_i| ≤ c` a.e., then each
increment `⟨M⟩_{k+1} - ⟨M⟩_k` equals `μ[(ΔM_k)² | ℱ_k] ≤ c²`, so telescoping from `⟨M⟩_0 = 0`
gives `⟨M⟩_n ≤ c² n` a.e. -/
lemma predQuadVar_le_of_bound [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) {c : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ c ^ 2 * n := by
  -- both integrability side conditions follow from the increment bound.
  have hae : ∀ n, AEStronglyMeasurable (M n) μ := fun n ↦ (hM.integrable n).aestronglyMeasurable
  have hd2 : ∀ n, MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ := fun n ↦
    memLp_increment_of_bound (hae n) (hae (n + 1)) (hb n)
  have hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ := fun n ↦
    integrable_mul_increment_of_bound (hM.integrable n) (hae (n + 1)) (hb n)
  have hstep : ∀ k, ∀ᵐ ω ∂μ,
      predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω ≤ c ^ 2 := by
    intro k
    have hinc := predQuadVar_succ_sub_eq hM k (hd2 k) (hprod k)
    have hsqle : (fun ω ↦ (M (k + 1) ω - M k ω) ^ 2) ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
      filter_upwards [hb k] with ω h
      exact sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
    have hcond : μ[fun ω ↦ (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
      have h := condExp_mono (m := ℱ k) (hd2 k).integrable_sq (integrable_const (c ^ 2)) hsqle
      rwa [condExp_const (ℱ.le k)] at h
    filter_upwards [hinc, hcond] with ω e ec
    rw [Pi.sub_apply] at e; rw [e]; exact ec
  filter_upwards [ae_all_iff.mpr hstep] with ω hω
  intro n
  have htel : ∑ k ∈ Finset.range n,
      (predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω) = predQuadVar M ℱ μ n ω := by
    rw [Finset.sum_range_sub (fun k ↦ predQuadVar M ℱ μ k ω) n]
    have h0 : predQuadVar M ℱ μ 0 ω = 0 := by rw [predQuadVar_zero]; rfl
    rw [h0, sub_zero]
  rw [← htel]
  calc ∑ k ∈ Finset.range n, (predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω)
      ≤ ∑ _k ∈ Finset.range n, c ^ 2 := Finset.sum_le_sum fun k _ ↦ hω k
    _ = c ^ 2 * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **A martingale has constant expectation**: `∫ N n = ∫ N 0` for every `n`. -/
lemma martingale_integral_eq [IsFiniteMeasure μ] {N : ℕ → Ω → ℝ} (hN : Martingale N ℱ μ) (n : ℕ) :
    ∫ ω, N n ω ∂μ = ∫ ω, N 0 ω ∂μ :=
  calc ∫ ω, N n ω ∂μ
  _ = ∫ ω, (μ[N n | ℱ 0]) ω ∂μ := (integral_condExp (f := N n) (ℱ.le 0)).symm
  _ = ∫ ω, N 0 ω ∂μ := integral_congr_ae (hN.condExp_ae_eq zero_le)

/-- **`M² - ⟨M⟩` is a martingale** (blueprint `lem:qv_mart`).
For an adapted process `M` with square-integrable values, `M² - ⟨M⟩` is a
martingale, being the martingale part of `M²` in its Doob decomposition. -/
@[specifies predQuadVar "the compensator property, the half of `IsPredQuadVar` that carries the \
content: `⟨M⟩` is what turns `M²` into a martingale"]
lemma martingale_sq_sub_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, MemLp (M n) 2 μ) :
    Martingale (fun n ↦ (fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) ℱ μ :=
  martingale_martingalePart (fun n ↦ (hM n).pow 2) (fun n ↦ (hM2 n).integrable_sq)

/-- **`⟨M⟩ n` is integrable.** Since `M² - ⟨M⟩` is (the martingale part, hence)
integrable and `M²` is integrable, so is `⟨M⟩`. -/
@[fun_prop]
lemma integrable_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    Integrable (predQuadVar M ℱ μ n) μ := by
  have hN := martingale_sq_sub_predQuadVar hM hM2
  have hNk : Integrable ((fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) μ := hN.integrable n
  have hid : predQuadVar M ℱ μ n
      = (fun ω ↦ M n ω ^ 2) - ((fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) := by
    funext ω; simp [Pi.sub_apply]
  rw [hid]
  exact (hM2 n).integrable_sq.sub hNk

/-! ## Characterization

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
  /-- `A` is predictable: `A (n + 1)` is already `ℱ n`-measurable. This is what makes the
  compensator property pin `A` down. Without it there is nothing to pin: adding to `A` any
  martingale null at `0` leaves `M² - A` a martingale and `A 0 = 0` intact. -/
  predictable : StronglyAdapted ℱ fun n ↦ A (n + 1)
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
  predictable := stronglyAdapted_predictablePart
  zero := predQuadVar_zero
  integrable := integrable_predQuadVar hM hM2

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
  have h := predictablePart_add_ae_eq (ℱ := ℱ) (μ := μ) hA.martingale_sq_sub hA.predictable
    hA.zero hA.integrable n
  rw [hsum] at h
  exact h.symm

/-- **The square of a martingale is a submartingale.** For a square-integrable martingale `M`,
`M²` is a submartingale: `M² = (M² - ⟨M⟩) + ⟨M⟩` is the sum of the martingale `M² - ⟨M⟩` and the
nondecreasing predictable quadratic variation `⟨M⟩`. This is Doob's `L²` submartingale, the input
to Doob's maximal inequality. -/
lemma submartingale_sq [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) :
    Submartingale (fun n ω ↦ M n ω ^ 2) ℱ μ := by
  have hd2 : ∀ n, MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ := fun n ↦
    memLp_increment (hM2 n) (hM2 (n + 1))
  have hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ := fun n ↦
    integrable_mul_increment (hM2 n) (hM2 (n + 1))
  have hN := martingale_sq_sub_predQuadVar hM.stronglyAdapted hM2
  have hIqv := integrable_predQuadVar hM.stronglyAdapted hM2
  refine submartingale_of_setIntegral_le_succ (fun n ↦ (hM.stronglyAdapted n).pow 2)
    (fun n ↦ (hM2 n).integrable_sq) ?_
  intro i s hs
  have hNeq := hN.setIntegral_eq (Nat.le_succ i) hs
  have hexp : ∀ j, ∫ ω in s, ((fun ω ↦ M j ω ^ 2) - predQuadVar M ℱ μ j) ω ∂μ
      = (∫ ω in s, M j ω ^ 2 ∂μ) - ∫ ω in s, predQuadVar M ℱ μ j ω ∂μ :=
    fun j ↦ integral_sub (hM2 j).integrable_sq.integrableOn (hIqv j).integrableOn
  rw [hexp i, hexp (i + 1)] at hNeq
  have hqvle : ∫ ω in s, predQuadVar M ℱ μ i ω ∂μ
      ≤ ∫ ω in s, predQuadVar M ℱ μ (i + 1) ω ∂μ :=
    setIntegral_mono_ae (hIqv i).integrableOn (hIqv (i + 1)).integrableOn
      (predQuadVar_le_succ hM i (hd2 i) (hprod i))
  linarith [hNeq, hqvle]

/-- **Expected quadratic variation equals the second moment** (blueprint
`lem:qv_second_moment`). For a square-integrable martingale `M` with `M 0 = 0`,
`E[M n ²] = E[⟨M⟩ n]`. This is the discrete Itô isometry: `M² - ⟨M⟩` is a
martingale starting at `0`, so its expectation stays `0`. -/
lemma integral_sq_eq_integral_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hM0 : M 0 =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ = ∫ ω, predQuadVar M ℱ μ n ω ∂μ := by
  have hN := martingale_sq_sub_predQuadVar hM hM2
  have hIqv := integrable_predQuadVar hM hM2
  -- `∫ (M n² - ⟨M⟩ n) = ∫ M n² - ∫ ⟨M⟩ n`.
  have e1 : ∫ ω, ((fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) ω ∂μ
      = ∫ ω, M n ω ^ 2 ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ :=
    integral_sub (hM2 n).integrable_sq (hIqv n)
  -- At time `0` the process is `M 0² - ⟨M⟩ 0 = 0` a.e.
  have e0 : ∫ ω, ((fun ω ↦ M 0 ω ^ 2) - predQuadVar M ℱ μ 0) ω ∂μ = 0 := by
    have hz : ((fun ω ↦ M 0 ω ^ 2) - predQuadVar M ℱ μ 0) =ᵐ[μ] 0 := by
      filter_upwards [hM0] with ω hω
      simp only [Pi.sub_apply, Pi.zero_apply] at hω ⊢
      rw [show predQuadVar M ℱ μ 0 ω = 0 from by rw [predQuadVar_zero]; rfl, hω]
      ring
    rw [integral_congr_ae hz]; simp
  have hconst := martingale_integral_eq hN n
  have key : ∫ ω, M n ω ^ 2 ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ = 0 := by
    rw [← e1, hconst]; exact e0
  exact sub_eq_zero.mp key

/-- **Integrated increment of `⟨M⟩`.** The expected increment of the quadratic
variation is the second moment of the martingale increment:
`E[⟨M⟩ (n+1)] - E[⟨M⟩ n] = E[(ΔM (n+1))²]`. -/
lemma integral_predQuadVar_succ_sub [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    ∫ ω, predQuadVar M ℱ μ (n + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := by
  have hd2 : MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ := memLp_increment (hM2 n) (hM2 (n + 1))
  have hprod : Integrable (M n * (M (n + 1) - M n)) μ :=
    integrable_mul_increment (hM2 n) (hM2 (n + 1))
  have hIqv := integrable_predQuadVar hM.stronglyAdapted hM2
  have h1 : predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      =ᵐ[μ] μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] :=
    predQuadVar_succ_sub_eq hM n hd2 hprod
  calc ∫ ω, predQuadVar M ℱ μ (n + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∫ ω, (predQuadVar M ℱ μ (n + 1) ω - predQuadVar M ℱ μ n ω) ∂μ :=
        (integral_sub (hIqv (n + 1)) (hIqv n)).symm
    _ = ∫ ω, (μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n]) ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h1] with ω hω
        simpa [Pi.sub_apply] using hω
    _ = ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := integral_condExp (ℱ.le n)

/-- **Martingale `L²` growth bound** (blueprint `lem:mart_sq_growth`).
If every increment has second moment `≤ σ²`, then `E[M n ²] ≤ σ² n`. This is the
discrete Itô isometry combined with the telescoping of `⟨M⟩`. -/
lemma integral_sq_le_of_increment_bound [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (hM0 : M 0 =ᵐ[μ] 0) (σ2 : ℝ)
    (hinc : ∀ n, ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ ≤ σ2) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ ≤ σ2 * n := by
  have hqv : ∀ n, ∫ ω, predQuadVar M ℱ μ n ω ∂μ ≤ σ2 * n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hstep := integral_predQuadVar_succ_sub hM hM2 k
      have heq : ∫ ω, predQuadVar M ℱ μ (k + 1) ω ∂μ
          = ∫ ω, predQuadVar M ℱ μ k ω ∂μ + ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by linarith
      rw [heq]
      have hcast : σ2 * ((k + 1 : ℕ) : ℝ) = σ2 * (k : ℝ) + σ2 := by push_cast; ring
      rw [hcast]
      linarith [ih, hinc k]
  rw [integral_sq_eq_integral_predQuadVar hM.stronglyAdapted hM2 hM0 n]
  exact hqv n

/-- **Product of conditionally orthogonal martingales is a martingale** (blueprint
`lem:qv_orthogonal`, first part). If `M`, `N` are martingales whose increments are
conditionally orthogonal, `μ[ΔM (i+1) · ΔN (i+1) | ℱ i] = 0`, then `M · N` is a
martingale. The integrability of the increment products is taken as hypotheses. -/
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

/-- **Additivity of the quadratic variation for orthogonal martingales** (blueprint
`lem:qv_orthogonal`, second part). If `M · N` is a martingale (e.g. `M`, `N` are
conditionally orthogonal martingales, see `martingale_mul`), then
`⟨M + N⟩ = ⟨M⟩ + ⟨N⟩`. This is predictable-part linearity together with the fact
that the predictable part of the martingale `M · N` vanishes. -/
lemma predQuadVar_add_of_martingale_mul {N : ℕ → Ω → ℝ}
    (hM2 : ∀ n, MemLp (M n) 2 μ) (hN2 : ∀ n, MemLp (N n) 2 μ)
    (hmart : Martingale (fun n ↦ M n * N n) ℱ μ) (n : ℕ) :
    predQuadVar (fun k ↦ M k + N k) ℱ μ n =ᵐ[μ] predQuadVar M ℱ μ n + predQuadVar N ℱ μ n := by
  have hproc : (fun k ↦ (M k + N k) ^ 2)
      = (fun k ↦ M k ^ 2) + (fun k ↦ N k ^ 2) + (2 : ℝ) • (fun k ↦ M k * N k) := by
    ext; simp; ring
  have hMint : ∀ k, Integrable ((fun k ↦ M k ^ 2) k) μ := fun k ↦ (hM2 k).integrable_sq
  have hNint : ∀ k, Integrable ((fun k ↦ N k ^ 2) k) μ := fun k ↦ (hN2 k).integrable_sq
  have hMNint : ∀ k, Integrable (((2 : ℝ) • fun k ↦ M k * N k) k) μ := fun k ↦ by
    simpa using ((hM2 k).integrable_mul (hN2 k)).smul (2 : ℝ)
  -- Split `⟨M+N⟩` by linearity of the predictable part.
  have h1 : predQuadVar (fun k ↦ M k + N k) ℱ μ n
      =ᵐ[μ] predictablePart ((fun k ↦ M k ^ 2) + fun k ↦ N k ^ 2) ℱ μ n
        + predictablePart ((2 : ℝ) • fun k ↦ M k * N k) ℱ μ n := by
    rw [predQuadVar, hproc]
    exact predictablePart_add (fun k ↦ (hMint k).add (hNint k)) hMNint n
  have h2 : predictablePart ((fun k ↦ M k ^ 2) + fun k ↦ N k ^ 2) ℱ μ n
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
