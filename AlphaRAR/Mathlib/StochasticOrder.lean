/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Order.Group.Lattice
public meta import LeanSpec

/-!
# Stochastic Landau orders `o_p` and `O_p`

This file develops the order-one stochastic Landau symbols used throughout the
asymptotic analysis: `o_p(1)` (convergence to `0` in probability) and `O_p(1)`
(boundedness in probability, i.e. uniform tightness). These are the order-one case of the
`o_p(·)` and `O_p(·)` notation introduced in Section 2 of the paper.

## Main definitions

* `AlphaRAR.IsLittleOpOne`: `Y = o_p(1)`.
* `AlphaRAR.IsBigOpOne`: `Y = O_p(1)`.

## Main results

* `AlphaRAR.isLittleOpOne_of_tendsto_ae`: a.e. convergence gives `o_p(1)`.
* `AlphaRAR.isBigOpOne_iff_isTightMeasureSet`: `O_p(1)` is exactly tightness of the family of
  laws, in the sense of `MeasureTheory.IsTightMeasureSet`.
* The arithmetic of the two orders: `AlphaRAR.IsLittleOpOne.add`, `AlphaRAR.IsBigOpOne.add`,
  `AlphaRAR.IsLittleOpOne.add_bigOpOne`, `AlphaRAR.IsBigOpOne.mul`,
  `AlphaRAR.IsBigOpOne.mul_littleOp`, `AlphaRAR.IsBigOpOne.bdd_mul`, together with
  `AlphaRAR.IsLittleOpOne.isBigOpOne` for the implication `o_p(1) ⟹ O_p(1)`.
* `AlphaRAR.isBigOpOne_of_lintegral_le` and `AlphaRAR.isBigOpOne_of_lintegral_sq_le`: a bounded
  first or second moment gives `O_p` (Lemma C.2 of the paper and its `L²` form).
* Closure properties: `AlphaRAR.IsLittleOpOne.of_eventually_abs_le` (domination, with the
  pointwise and a.e. specializations `of_abs_le` / `of_abs_le_ae`), `AlphaRAR.IsLittleOpOne.abs`,
  `AlphaRAR.IsLittleOpOne.const_mul`, `AlphaRAR.isLittleOpOne_finset_sum`, and the basic instances
  `AlphaRAR.isLittleOpOne_zero`, `AlphaRAR.isLittleOpOne_const_div_sqrt`,
  `AlphaRAR.isBigOpOne_of_ae_bounded`.

## Implementation notes

`IsLittleOpOne μ Y` is *definitionally* `MeasureTheory.TendstoInMeasure μ Y atTop 0`, so the
whole `TendstoInMeasure` API of Mathlib applies to it; `IsLittleOpOne.congr` and
`IsLittleOpOne.tendsto_abs` are thin wrappers that keep dot notation working through the `def`.

`IsBigOpOne` is stated as a uniform-in-`n` tail bound rather than as tightness of the pushforward
measures, because that is the form every downstream proof consumes;
`isBigOpOne_iff_isTightMeasureSet` records that the two agree.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- `Y = o_p(1)`: the sequence `Y` converges to `0` in probability, i.e. in measure. -/
def IsLittleOpOne (μ : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  TendstoInMeasure μ Y atTop 0

/-- `Y = O_p(1)`: the sequence `Y` is bounded in probability, i.e. uniformly tight;
stated as a tail bound uniform in `n`. -/
def IsBigOpOne (μ : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, ∀ n, μ {ω | M < |Y n ω|} ≤ ε

/-- `o_p(1)` only depends on each `Y n` up to `μ`-a.e. equality. -/
lemma IsLittleOpOne.congr {Y Y' : ℕ → Ω → ℝ} (h : ∀ n, Y n =ᵐ[μ] Y' n)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ Y' :=
  hY.congr_left h

/-- `O_p(1)` only depends on each `Y n` up to `μ`-a.e. equality. -/
lemma IsBigOpOne.congr {Y Y' : ℕ → Ω → ℝ} (h : ∀ n, Y n =ᵐ[μ] Y' n)
    (hY : IsBigOpOne μ Y) : IsBigOpOne μ Y' := by
  intro ε hε
  obtain ⟨M, hM⟩ := hY ε hε
  refine ⟨M, fun n ↦ ?_⟩
  refine le_of_eq_of_le (measure_congr ?_) (hM n)
  filter_upwards [h n] with ω hω
  change (M < |Y' n ω|) = (M < |Y n ω|)
  rw [hω]

/-- **Single-variable tightness.** For a finite measure and an a.e.-measurable real
function `f`, the measure of `{|f| > M}` can be made `≤ ε` by taking `M` large. -/
lemma exists_measure_abs_lt_le [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEMeasurable f μ)
    {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ M : ℝ, μ {ω | M < |f ω|} ≤ ε := by
  have hmeas : ∀ M : ℕ, NullMeasurableSet {ω | (M : ℝ) < |f ω|} μ := fun _ ↦
    nullMeasurableSet_lt aemeasurable_const hf.abs
  have hanti : Antitone fun M : ℕ ↦ {ω | (M : ℝ) < |f ω|} := by
    intro a b hab ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hab) hω
  have hempty : ⋂ M : ℕ, {ω | (M : ℝ) < |f ω|} = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    exact exists_nat_ge |f ω|
  have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  rw [hempty, measure_empty] at htend
  obtain ⟨M, hM⟩ := (htend.eventually (Iio_mem_nhds hε)).exists
  exact ⟨(M : ℝ), hM.le⟩

/-- The `|·|`-form of `o_p(1)`: `μ {ε ≤ |Y n|} → 0` for every real `ε > 0`. -/
@[specifies IsLittleOpOne "unwinds the `TendstoInMeasure`/`edist` packaging into the textbook \
`ℙ(|Y n| ≥ ε) → 0`, so a referee can read the definition off without chasing `ℝ≥0∞` coercions; \
`isLittleOpOne_of_tendsto_abs` is the converse"]
lemma IsLittleOpOne.tendsto_abs {Y : ℕ → Ω → ℝ} (hY : IsLittleOpOne μ Y) {ε : ℝ}
    (hε : 0 < ε) : Tendsto (fun n ↦ μ {ω | ε ≤ |Y n ω|}) atTop (𝓝 0) := by
  simpa using tendstoInMeasure_iff_norm.1 hY ε hε

/-- Build `o_p(1)` from the `|·|`-form: if `μ {ε ≤ |Y n|} → 0` for all real `ε > 0`,
then `Y = o_p(1)`. -/
@[specifies IsLittleOpOne "the converse of `IsLittleOpOne.tendsto_abs`; together the two make the \
textbook `ℙ(|Y n| ≥ ε) → 0` an equivalent form, so the definition is neither stronger nor weaker \
than convergence in probability"]
lemma isLittleOpOne_of_tendsto_abs {Y : ℕ → Ω → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ε ≤ |Y n ω|}) atTop (𝓝 0)) :
    IsLittleOpOne μ Y :=
  tendstoInMeasure_iff_norm.2 fun ε hε ↦ by simpa using h ε hε

/-- **Almost everywhere convergence gives `o_p`.**
If `Y n → 0` almost everywhere on a finite measure, then `Y = o_p(1)`. -/
lemma isLittleOpOne_of_tendsto_ae [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (Y n) μ)
    (h : ∀ᵐ ω ∂μ, Tendsto (Y · ω) atTop (𝓝 0)) :
    IsLittleOpOne μ Y :=
  tendstoInMeasure_of_tendsto_ae hmeas h

/-- **`o_p(1) + o_p(1) = o_p(1)`.**
The sum of two sequences converging to `0` in probability converges to `0` in
probability. -/
lemma IsLittleOpOne.add {X Y : ℕ → Ω → ℝ} (hX : IsLittleOpOne μ X)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ (fun n ω ↦ X n ω + Y n ω) := by
  refine isLittleOpOne_of_tendsto_abs fun ε hε ↦ ?_
  have hsum : Tendsto (fun n ↦ μ {ω | ε / 2 ≤ |X n ω|} + μ {ω | ε / 2 ≤ |Y n ω|})
      atTop (𝓝 0) := by
    simpa using (hX.tendsto_abs (half_pos hε)).add (hY.tendsto_abs (half_pos hε))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun n ↦ ?_
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hcon
  rcases not_or.mp hcon with ⟨h1, h2⟩
  rw [not_le] at h1 h2
  have := abs_add_le (X n ω) (Y n ω)
  linarith

/-- **`-o_p(1) = o_p(1)`**. -/
lemma IsLittleOpOne.neg {Y : ℕ → Ω → ℝ} (hY : IsLittleOpOne μ Y) :
    IsLittleOpOne μ (fun n ω ↦ -Y n ω) :=
  isLittleOpOne_of_tendsto_abs fun ε hε ↦ by simpa using hY.tendsto_abs hε

/-- **`o_p(1) - o_p(1) = o_p(1)`.** -/
lemma IsLittleOpOne.sub {X Y : ℕ → Ω → ℝ} (hX : IsLittleOpOne μ X)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ (fun n ω ↦ X n ω - Y n ω) := by
  simpa [sub_eq_add_neg] using hX.add hY.neg

/-- **`O_p(1) + O_p(1) = O_p(1)`.**
The sum of two sequences bounded in probability is bounded in probability. -/
lemma IsBigOpOne.add {X Y : ℕ → Ω → ℝ} (hX : IsBigOpOne μ X) (hY : IsBigOpOne μ Y) :
    IsBigOpOne μ (fun n ω ↦ X n ω + Y n ω) := by
  intro ε hε
  obtain ⟨Mx, hMx⟩ := hX (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨My, hMy⟩ := hY (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨Mx + My, fun n ↦ ?_⟩
  have hsub : {ω | Mx + My < |X n ω + Y n ω|}
      ⊆ {ω | Mx < |X n ω|} ∪ {ω | My < |Y n ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    rcases not_or.mp hcon with ⟨h1, h2⟩
    rw [not_lt] at h1 h2
    have hab : |X n ω + Y n ω| ≤ |X n ω| + |Y n ω| := abs_add_le _ _
    linarith
  calc μ {ω | Mx + My < |X n ω + Y n ω|}
      ≤ μ ({ω | Mx < |X n ω|} ∪ {ω | My < |Y n ω|}) := measure_mono hsub
    _ ≤ μ {ω | Mx < |X n ω|} + μ {ω | My < |Y n ω|} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hMx n) (hMy n)
    _ = ε := ENNReal.add_halves ε

/-- **`o_p(1) ⟹ O_p(1)`**: convergence in probability implies boundedness in probability. -/
@[specifies IsBigOpOne "places `O_p` correctly relative to `o_p`: the tightness condition is weak \
enough to be implied by convergence in probability, which rules out an accidentally too-strong \
definition"]
lemma IsLittleOpOne.isBigOpOne [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ}
    (hmeas : ∀ n, AEMeasurable (Y n) μ) (hY : IsLittleOpOne μ Y) : IsBigOpOne μ Y := by
  intro ε hε
  -- Past some rank `N` the bound holds with the uniform threshold `1`; the finitely many
  -- remaining indices are covered one by one, and we take the largest of all the thresholds.
  have hev : ∀ᶠ n in atTop, μ {ω | (1 : ℝ) ≤ |Y n ω|} ≤ ε :=
    ((hY.tendsto_abs one_pos).eventually (Iio_mem_nhds hε)).mono fun n hn ↦ hn.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  choose Mn hMn using fun n ↦ exists_measure_abs_lt_le (μ := μ) (hmeas n) hε
  obtain ⟨M, hM⟩ := ((Finset.range N).image Mn ∪ {1}).exists_le
  have hM1 : (1 : ℝ) ≤ M := hM 1 (Finset.mem_union_right _ (Finset.mem_singleton_self 1))
  refine ⟨M, fun n ↦ ?_⟩
  rcases le_or_gt N n with hn | hn
  · refine le_trans (measure_mono fun ω hω ↦ ?_) (hN n hn)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  · have hle : Mn n ≤ M :=
      hM _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hn)))
    refine le_trans (measure_mono fun ω hω ↦ ?_) (hMn n)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith

/-- **`o_p(1) + O_p(1) = O_p(1)`.** -/
lemma IsLittleOpOne.add_bigOpOne [IsFiniteMeasure μ] {X Y : ℕ → Ω → ℝ}
    (hX : IsLittleOpOne μ X) (hmeas : ∀ n, AEMeasurable (X n) μ) (hY : IsBigOpOne μ Y) :
    IsBigOpOne μ (fun n ω ↦ X n ω + Y n ω) :=
  (hX.isBigOpOne hmeas).add hY

/-- **`O_p(1) · o_p(1) = o_p(1)`.**
The product of a bounded-in-probability sequence and a sequence converging to `0`
in probability converges to `0` in probability. -/
@[specifies IsBigOpOne "the absorption law that makes `O_p` usable, and the direction that rules \
out a too-weak definition: a merely a.e.-finite sequence would not multiply an `o_p` back into an \
`o_p`"]
lemma IsBigOpOne.mul_littleOp {X Y : ℕ → Ω → ℝ} (hX : IsBigOpOne μ X)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ (fun n ω ↦ X n ω * Y n ω) := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  -- Pick a threshold `M'` for `X` that is moreover positive, so that `ε / M'` makes sense.
  obtain ⟨M, hM⟩ := hX (δ / 2) (ENNReal.half_pos hδ.ne')
  obtain ⟨M', hMM', hM'pos⟩ : ∃ M' : ℝ, M ≤ M' ∧ 0 < M' :=
    ⟨max M 1, le_max_left _ _, lt_of_lt_of_le one_pos (le_max_right _ _)⟩
  have hXtail : ∀ n, μ {ω | M' < |X n ω|} ≤ δ / 2 := fun n ↦
    le_trans (measure_mono fun ω hω ↦ lt_of_le_of_lt hMM' hω) (hM n)
  have hYtail : ∀ᶠ n in atTop, μ {ω | ε / M' ≤ |Y n ω|} ≤ δ / 2 :=
    ((hY.tendsto_abs (div_pos hε hM'pos)).eventually
      (Iio_mem_nhds (ENNReal.half_pos hδ.ne'))).mono fun n hn ↦ hn.le
  filter_upwards [hYtail] with n hn
  have hsub : {ω | ε ≤ |X n ω * Y n ω|}
      ⊆ {ω | M' < |X n ω|} ∪ {ω | ε / M' ≤ |Y n ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, abs_mul] at hω ⊢
    by_contra hcon
    rcases not_or.mp hcon with ⟨h1, h2⟩
    rw [not_lt] at h1
    rw [not_le] at h2
    have hlt : |X n ω| * |Y n ω| < ε := by
      calc |X n ω| * |Y n ω| ≤ M' * |Y n ω| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ < M' * (ε / M') := mul_lt_mul_of_pos_left h2 hM'pos
        _ = ε := by field_simp
    linarith
  calc μ {ω | ε ≤ |X n ω * Y n ω|}
      ≤ μ ({ω | M' < |X n ω|} ∪ {ω | ε / M' ≤ |Y n ω|}) := measure_mono hsub
    _ ≤ μ {ω | M' < |X n ω|} + μ {ω | ε / M' ≤ |Y n ω|} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (hXtail n) hn
    _ = δ := ENNReal.add_halves δ

/-- **`O_p(1) · O_p(1) = O_p(1)`**: the product of two sequences bounded in probability is
bounded in probability. -/
lemma IsBigOpOne.mul {X Y : ℕ → Ω → ℝ} (hX : IsBigOpOne μ X) (hY : IsBigOpOne μ Y) :
    IsBigOpOne μ (fun n ω ↦ X n ω * Y n ω) := by
  intro ε hε
  obtain ⟨Mx, hMx⟩ := hX (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨My, hMy⟩ := hY (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨|Mx| * |My|, fun n ↦ ?_⟩
  have hsub : {ω | |Mx| * |My| < |X n ω * Y n ω|}
      ⊆ {ω | Mx < |X n ω|} ∪ {ω | My < |Y n ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, abs_mul] at hω ⊢
    by_contra hcon
    rcases not_or.mp hcon with ⟨h1, h2⟩
    rw [not_lt] at h1 h2
    have h1' : |X n ω| ≤ |Mx| := h1.trans (le_abs_self _)
    have h2' : |Y n ω| ≤ |My| := h2.trans (le_abs_self _)
    nlinarith [abs_nonneg (X n ω), abs_nonneg (Y n ω), abs_nonneg Mx, abs_nonneg My]
  calc μ {ω | |Mx| * |My| < |X n ω * Y n ω|}
      ≤ μ ({ω | Mx < |X n ω|} ∪ {ω | My < |Y n ω|}) := measure_mono hsub
    _ ≤ μ {ω | Mx < |X n ω|} + μ {ω | My < |Y n ω|} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hMx n) (hMy n)
    _ = ε := ENNReal.add_halves ε

/-- A deterministic bounded sequence is `O_p(1)`. -/
lemma isBigOpOne_const {c : ℕ → ℝ} {B : ℝ} (hc : ∀ n, |c n| ≤ B) :
    IsBigOpOne μ (fun n _ ↦ c n) := by
  refine fun ε _ ↦ ⟨B, fun n ↦ ?_⟩
  have hempty : {ω : Ω | B < |c n|} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hc n
  simp [hempty]

/-- **A bounded multiple preserves `O_p(1)`.**
If `|c n| ≤ B` for all `n` and `X = O_p(1)`, then `c n · X n = O_p(1)`. -/
lemma IsBigOpOne.bdd_mul {X : ℕ → Ω → ℝ} {c : ℕ → ℝ} {B : ℝ}
    (hc : ∀ n, |c n| ≤ B) (hX : IsBigOpOne μ X) :
    IsBigOpOne μ (fun n ω ↦ c n * X n ω) :=
  (isBigOpOne_const hc).mul hX

/-- **`O_p(1)` transfers through squares.** If the squared sequence `Z²` is bounded
in probability, then so is `Z` itself (take `M = √M'`). -/
lemma IsBigOpOne.of_sq {Z : ℕ → Ω → ℝ} (h : IsBigOpOne μ (fun n ω ↦ (Z n ω) ^ 2)) :
    IsBigOpOne μ Z := by
  intro ε hε
  obtain ⟨M', hM'⟩ := h ε hε
  refine ⟨√(max M' 0), fun n ↦ ?_⟩
  refine le_trans (measure_mono ?_) (hM' n)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hs : (0 : ℝ) ≤ √(max M' 0) := Real.sqrt_nonneg _
  have hlt : √(max M' 0) < |Z n ω| := hω
  have hz : |(Z n ω) ^ 2| = (Z n ω) ^ 2 := abs_of_nonneg (sq_nonneg _)
  rw [hz]
  have hkey : max M' 0 < |Z n ω| ^ 2 := by
    have h1 : √(max M' 0) ^ 2 = max M' 0 := Real.sq_sqrt (le_max_right _ _)
    nlinarith [hlt, hs, h1]
  calc M' ≤ max M' 0 := le_max_left _ _
    _ < |Z n ω| ^ 2 := hkey
    _ = (Z n ω) ^ 2 := sq_abs _

/-- **Squares of an `O_p(1)` sequence are `O_p(1)`**, the converse of `IsBigOpOne.of_sq`. -/
lemma IsBigOpOne.sq {Z : ℕ → Ω → ℝ} (h : IsBigOpOne μ Z) :
    IsBigOpOne μ (fun n ω ↦ (Z n ω) ^ 2) := by
  simpa [pow_two] using h.mul h

/-- **Eventual a.e. domination for `o_p(1)`.** If `|Z n| ≤ |Y n|` almost surely for all large `n`
and `Y = o_p(1)`, then `Z = o_p(1)` (`o_p` depends only on the tail). -/
lemma IsLittleOpOne.of_eventually_abs_le {Y Z : ℕ → Ω → ℝ}
    (hZY : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, |Z n ω| ≤ |Y n ω|) (hY : IsLittleOpOne μ Y) :
    IsLittleOpOne μ Z := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hbound : ∀ᶠ n in atTop, μ {ω | ε ≤ |Z n ω|} ≤ μ {ω | ε ≤ |Y n ω|} := by
    filter_upwards [hZY] with n hn
    refine measure_mono_ae ?_
    filter_upwards [hn] with ω hω hεZ
    exact le_trans hεZ hω
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hY.tendsto_abs hε)
    (Eventually.of_forall fun n ↦ zero_le) hbound

/-- **a.e. domination for `o_p(1)`.** If `|Z n| ≤ |Y n|` almost surely for each `n` and
`Y = o_p(1)`, then `Z = o_p(1)`. -/
lemma IsLittleOpOne.of_abs_le_ae {Y Z : ℕ → Ω → ℝ} (hZY : ∀ n, ∀ᵐ ω ∂μ, |Z n ω| ≤ |Y n ω|)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ Z :=
  hY.of_eventually_abs_le (Eventually.of_forall hZY)

/-- **Domination for `o_p(1)`.** If `|Z n| ≤ |Y n|` pointwise and `Y = o_p(1)`, then
`Z = o_p(1)`. -/
lemma IsLittleOpOne.of_abs_le {Y Z : ℕ → Ω → ℝ} (hZY : ∀ n ω, |Z n ω| ≤ |Y n ω|)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ Z :=
  hY.of_abs_le_ae fun n ↦ Eventually.of_forall (hZY n)

/-- `o_p(1)` is preserved by taking absolute values. -/
lemma IsLittleOpOne.abs {X : ℕ → Ω → ℝ} (hX : IsLittleOpOne μ X) :
    IsLittleOpOne μ (fun n ω ↦ |X n ω|) :=
  IsLittleOpOne.of_abs_le (fun _ _ ↦ le_of_eq (abs_abs _)) hX

/-- `o_p(1)` is preserved by multiplication by a constant: the constant sequence is `O_p(1)`,
and `O_p(1) · o_p(1) = o_p(1)`. -/
lemma IsLittleOpOne.const_mul {X : ℕ → Ω → ℝ} (c : ℝ) (hX : IsLittleOpOne μ X) :
    IsLittleOpOne μ (fun n ω ↦ c * X n ω) :=
  (isBigOpOne_const (c := fun _ ↦ c) (B := |c|) fun _ ↦ le_rfl).mul_littleOp hX

/-- If `|X| = o_p(1)` then `X = o_p(1)`. -/
lemma isLittleOpOne_of_abs {X : ℕ → Ω → ℝ} (hX : IsLittleOpOne μ (fun n ω ↦ |X n ω|)) :
    IsLittleOpOne μ X :=
  IsLittleOpOne.of_abs_le (fun _ _ ↦ le_of_eq (abs_abs _).symm) hX

/-- The zero sequence is `o_p(1)`. -/
lemma isLittleOpOne_zero : IsLittleOpOne μ (fun _ _ ↦ (0 : ℝ)) := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hz : (fun n : ℕ ↦ μ {ω : Ω | ε ≤ |(fun _ _ ↦ (0 : ℝ)) n ω|}) = fun _ ↦ 0 := by
    funext n
    convert measure_empty (μ := μ)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, abs_zero]
    exact hε
  rw [hz]
  exact tendsto_const_nhds

/-- A constant over `√n` is `o_p(1)`. -/
lemma isLittleOpOne_const_div_sqrt [IsFiniteMeasure μ] (C : ℝ) :
    IsLittleOpOne μ (fun n (_ : Ω) ↦ C / √n) := by
  refine isLittleOpOne_of_tendsto_ae (fun n ↦ measurable_const.aestronglyMeasurable)
    (ae_of_all _ fun ω ↦ ?_)
  have hsqrt : Tendsto (fun n : ℕ ↦ √n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.div_atTop hsqrt

/-- **`O_p(1)` from an a.s. bound.** If, almost surely, the sequence `X_· ω` is bounded (by a
random constant), then `X = O_p(1)`. -/
lemma isBigOpOne_of_ae_bounded [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hmeas : ∀ n, Measurable (X n))
    (hbdd : ∀ᵐ ω ∂μ, ∃ B, ∀ n, |X n ω| ≤ B) : IsBigOpOne μ X := by
  intro ε hε
  set s : ℕ → Set Ω := fun M ↦ {ω | ∃ n, (M : ℝ) < |X n ω|} with hs
  have hsmeas : ∀ M, NullMeasurableSet (s M) μ := fun M ↦ by
    change NullMeasurableSet {ω | ∃ n, (M : ℝ) < |X n ω|} μ
    rw [Set.ofPred_exists]
    exact (MeasurableSet.iUnion fun n ↦
      measurableSet_lt measurable_const (hmeas n).abs).nullMeasurableSet
  have hsanti : Antitone s := by
    intro a b hab ω hω
    obtain ⟨n, hn⟩ := hω
    exact ⟨n, lt_of_le_of_lt (by exact_mod_cast hab) hn⟩
  have hinter0 : μ (⋂ M, s M) = 0 := by
    refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq (ae_iff.mp hbdd))) (zero_le)
    intro ω hω
    simp only [Set.mem_iInter] at hω
    rintro ⟨B, hB⟩
    obtain ⟨M, hM⟩ := exists_nat_ge B
    obtain ⟨n, hn⟩ := hω M
    exact absurd (le_trans (hB n) hM) (not_le.mpr hn)
  have htend := tendsto_measure_iInter_atTop hsmeas hsanti ⟨0, measure_ne_top μ _⟩
  rw [hinter0] at htend
  obtain ⟨M, hM⟩ := (htend.eventually (Iio_mem_nhds hε)).exists
  refine ⟨(M : ℝ), fun n ↦ le_trans (measure_mono ?_) hM.le⟩
  intro ω hω
  change ∃ n', (M : ℝ) < |X n' ω|
  exact ⟨n, hω⟩

/-- `o_p(1)` is closed under finite sums. -/
lemma isLittleOpOne_finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℕ → Ω → ℝ}
    (hf : ∀ j ∈ s, IsLittleOpOne μ (f j)) :
    IsLittleOpOne μ (fun n ω ↦ ∑ j ∈ s, f j n ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isLittleOpOne_zero
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- **`O_p(1)` is tightness of the family of laws.** The uniform tail bound defining
`IsBigOpOne` is exactly `MeasureTheory.IsTightMeasureSet` for the pushforward measures
`μ.map (Y n)`, the compact sets of `ℝ` being the closed bounded ones. -/
lemma isBigOpOne_iff_isTightMeasureSet {Y : ℕ → Ω → ℝ} (hY : ∀ n, AEMeasurable (Y n) μ) :
    IsBigOpOne μ Y ↔ IsTightMeasureSet (Set.range fun n ↦ μ.map (Y n)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  constructor
  · intro h ε hε
    obtain ⟨M, hM⟩ := h ε hε
    refine ⟨Set.Icc (-M) M, isCompact_Icc, ?_⟩
    rintro - ⟨n, rfl⟩
    rw [Measure.map_apply₀ (hY n) measurableSet_Icc.compl.nullMeasurableSet]
    refine le_trans (measure_mono fun ω hω ↦ ?_) (hM n)
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le,
      Set.mem_ofPred_eq] at hω ⊢
    rcases hω with h' | h'
    · exact lt_abs.2 (Or.inr (by linarith))
    · exact lt_abs.2 (Or.inl h')
  · intro h ε hε
    obtain ⟨K, hKc, hK⟩ := h ε hε
    obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall 0
    refine ⟨M, fun n ↦ ?_⟩
    have hKn := hK _ ⟨n, rfl⟩
    rw [Measure.map_apply₀ (hY n) hKc.isClosed.measurableSet.compl.nullMeasurableSet] at hKn
    refine le_trans (measure_mono fun ω hω ↦ ?_) hKn
    simp only [Set.mem_ofPred_eq] at hω
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    intro hmem
    have hball := hM hmem
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hball
    linarith

/-- **Bounded expectation gives `O_p`** (Lemma C.2 of the paper).
If `∫⁻ ‖X n‖ₑ ≤ C · u n` for all `n` (with `u n > 0`, `C ≥ 0`), then
`X n / u n = O_p(1)`, i.e. `X n = O_p(u n)`. -/
lemma isBigOpOne_of_lintegral_le {X : ℕ → Ω → ℝ} {u : ℕ → ℝ} {C : ℝ}
    (hu : ∀ n, 0 < u n) (hC : 0 ≤ C) (hmeas : ∀ n, AEMeasurable (X n) μ)
    (hbound : ∀ n, ∫⁻ ω, ‖X n ω‖ₑ ∂μ ≤ ENNReal.ofReal (C * u n)) :
    IsBigOpOne μ (fun n ω ↦ X n ω / u n) := by
  intro ε hε
  -- A threshold `M` that is positive and satisfies the Markov bound `C / M ≤ ε`.
  obtain ⟨M, hMpos, hle⟩ : ∃ M : ℝ, 0 < M ∧ ENNReal.ofReal (C / M) ≤ ε := by
    refine ⟨C / ε.toReal + 1, by positivity, ?_⟩
    rcases eq_or_ne ε ⊤ with hεtop | hεtop
    · exact hεtop ▸ le_top
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hCM : C / (C / ε.toReal + 1) ≤ ε.toReal := by
      rw [div_le_iff₀ (by positivity)]
      have hid : C / ε.toReal * ε.toReal = C := div_mul_cancel₀ C hεr.ne'
      nlinarith [hid, hεr]
    calc ENNReal.ofReal (C / (C / ε.toReal + 1)) ≤ ENNReal.ofReal ε.toReal :=
          ENNReal.ofReal_le_ofReal hCM
      _ = ε := ENNReal.ofReal_toReal hεtop
  refine ⟨M, fun n ↦ ?_⟩
  have hMun : 0 < M * u n := mul_pos hMpos (hu n)
  have hsub : {ω | M < |X n ω / u n|} ⊆ {ω | ENNReal.ofReal (M * u n) ≤ ‖X n ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Real.enorm_eq_ofReal_abs] at hω ⊢
    rw [abs_div, abs_of_pos (hu n), lt_div_iff₀ (hu n)] at hω
    exact ENNReal.ofReal_le_ofReal hω.le
  calc μ {ω | M < |X n ω / u n|}
      ≤ μ {ω | ENNReal.ofReal (M * u n) ≤ ‖X n ω‖ₑ} := measure_mono hsub
    _ ≤ (∫⁻ ω, ‖X n ω‖ₑ ∂μ) / ENNReal.ofReal (M * u n) :=
        meas_ge_le_lintegral_div (hmeas n).enorm (ENNReal.ofReal_ne_zero_iff.mpr hMun)
          ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C * u n) / ENNReal.ofReal (M * u n) :=
        ENNReal.div_le_div_right (hbound n) _
    _ = ENNReal.ofReal (C / M) := by
        rw [← ENNReal.ofReal_div_of_pos hMun, mul_div_mul_right _ _ (hu n).ne']
    _ ≤ ε := hle

/-- **Bounded second moment gives `O_p`** (the `L²` form of Lemma C.2 of the paper).
If `∫⁻ ‖X n‖ₑ² ≤ C · (u n)²` for all `n` (with `u n > 0`, `C ≥ 0`), then
`X n / u n = O_p(1)`, i.e. `X n = O_p(u n)`. This is Chebyshev's inequality: it
reduces to the `L¹` bound `isBigOpOne_of_lintegral_le` applied to `X²` with rate
`u²`, then transfers back through `IsBigOpOne.of_sq`. -/
lemma isBigOpOne_of_lintegral_sq_le {X : ℕ → Ω → ℝ} {u : ℕ → ℝ} {C : ℝ}
    (hu : ∀ n, 0 < u n) (hC : 0 ≤ C) (hmeas : ∀ n, AEMeasurable (X n) μ)
    (hbound : ∀ n, ∫⁻ ω, ‖X n ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * (u n) ^ 2)) :
    IsBigOpOne μ (fun n ω ↦ X n ω / u n) := by
  have hsq : IsBigOpOne μ (fun n ω ↦ (X n ω) ^ 2 / (u n) ^ 2) := by
    refine isBigOpOne_of_lintegral_le (X := fun n ω ↦ (X n ω) ^ 2) (u := fun n ↦ (u n) ^ 2)
      (fun n ↦ pow_pos (hu n) 2) hC (fun n ↦ (hmeas n).pow_const 2) fun n ↦ ?_
    refine le_trans (le_of_eq (lintegral_congr fun ω ↦ ?_)) (hbound n)
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs, abs_of_nonneg (sq_nonneg _)]
  have heq : (fun n ω ↦ (X n ω) ^ 2 / (u n) ^ 2) = fun n ω ↦ (X n ω / u n) ^ 2 := by
    funext n ω
    rw [div_pow]
  rw [heq] at hsq
  exact hsq.of_sq

end AlphaRAR
