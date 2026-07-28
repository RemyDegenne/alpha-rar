/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import LeanSpec

/-!
# Stochastic Landau orders `o_p` and `O_p`

This file develops the order-one stochastic Landau symbols used throughout the
asymptotic analysis: `o_p(1)` (convergence to `0` in probability) and `O_p(1)`
(boundedness in probability, i.e. uniform tightness). It corresponds to the
`def:op_Op` calculus of the blueprint, which the paper reduces to order one.

## Main definitions

* `AlphaRAR.IsLittleOpOne`: `Y = o_p(1)` (blueprint `def:op_Op`).
* `AlphaRAR.IsBigOpOne`: `Y = O_p(1)` (blueprint `def:op_Op`).

## Main results

* `AlphaRAR.isLittleOpOne_of_tendsto_ae`: a.e. convergence gives `o_p(1)`
  (blueprint `lem:op_of_tendsto`).
* `AlphaRAR.isBigOpOne_of_lintegral_le`: a bounded expectation gives `O_p`
  (blueprint `lem:expectation_to_O`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- `Y = o_p(1)`: the sequence `Y` converges to `0` in probability, i.e. in measure
(blueprint `def:op_Op`, order one). -/
def IsLittleOpOne (μ : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  TendstoInMeasure μ Y atTop 0

/-- `Y = O_p(1)`: the sequence `Y` is bounded in probability, i.e. uniformly tight
(blueprint `def:op_Op`, order one; stated with uniform-in-`n` tightness). -/
def IsBigOpOne (μ : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, ∀ n, μ {ω | M < |Y n ω|} ≤ ε

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

/-- **Single-variable tightness.** For a finite measure and a measurable real
function `f`, the measure of `{|f| > M}` can be made `≤ ε` by taking `M` large. -/
lemma exists_meas_lt [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ M : ℝ, μ {ω | M < |f ω|} ≤ ε := by
  set s : ℕ → Set Ω := fun M ↦ {ω | (M : ℝ) < |f ω|} with hs_def
  have hmeas : ∀ M, NullMeasurableSet (s M) μ := fun M ↦
    (measurableSet_lt measurable_const hf.abs).nullMeasurableSet
  have hanti : Antitone s := by
    intro a b hab ω hω
    simp only [hs_def, Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hab) hω
  have hempty : ⋂ M, s M = ∅ := by
    ext ω
    simp only [hs_def, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    obtain ⟨M, hM⟩ := exists_nat_ge |f ω|
    exact ⟨M, hM⟩
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
  refine Tendsto.congr (fun n ↦ ?_) (hY (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε))
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, edist_zero_right, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]

/-- Build `o_p(1)` from the `|·|`-form: if `μ {ε ≤ |Y n|} → 0` for all real `ε > 0`,
then `Y = o_p(1)`. -/
@[specifies IsLittleOpOne "the converse of `IsLittleOpOne.tendsto_abs`; together the two make the \
textbook `ℙ(|Y n| ≥ ε) → 0` an equivalent form, so the definition is neither stronger nor weaker \
than convergence in probability"]
lemma isLittleOpOne_of_tendsto_abs {Y : ℕ → Ω → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ε ≤ |Y n ω|}) atTop (𝓝 0)) :
    IsLittleOpOne μ Y := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with hεtop | hεtop
  · subst hεtop
    have hzero : (fun n ↦ μ {ω | (⊤ : ℝ≥0∞) ≤ edist (Y n ω) ((0 : Ω → ℝ) ω)})
        = fun _ ↦ 0 := by
      funext n
      have hemp : {ω | (⊤ : ℝ≥0∞) ≤ edist (Y n ω) ((0 : Ω → ℝ) ω)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, edist_zero_right, Set.mem_empty_iff_false,
          iff_false, top_le_iff]
        exact enorm_lt_top.ne
      rw [hemp, measure_empty]
    rw [hzero]
    exact tendsto_const_nhds
  · refine Tendsto.congr (fun n ↦ ?_) (h ε.toReal (ENNReal.toReal_pos hε.ne' hεtop))
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, edist_zero_right, Real.enorm_eq_ofReal_abs]
    exact (ENNReal.le_ofReal_iff_toReal_le hεtop (abs_nonneg _)).symm

/-- **Convergence in probability gives `o_p`** (blueprint `lem:op_of_tendsto`, first
part). If `Y n → 0` almost everywhere on a finite measure, then `Y = o_p(1)`. -/
lemma isLittleOpOne_of_tendsto_ae [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (Y n) μ)
    (h : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 0)) :
    IsLittleOpOne μ Y :=
  tendstoInMeasure_of_tendsto_ae hmeas h

/-- **`o_p(1) + o_p(1) = o_p(1)`** (blueprint `lem:op_arith` (i)).
The sum of two sequences converging to `0` in probability converges to `0` in
probability. -/
lemma IsLittleOpOne.add {X Y : ℕ → Ω → ℝ} (hX : IsLittleOpOne μ X)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ (fun n ω ↦ X n ω + Y n ω) := by
  intro ε hε
  have hX2 := hX (ε / 2) (ENNReal.half_pos hε.ne')
  have hY2 := hY (ε / 2) (ENNReal.half_pos hε.ne')
  have hsum : Tendsto (fun n ↦ μ {ω | ε / 2 ≤ edist (X n ω) ((0 : ℝ → ℝ) 0)}
      + μ {ω | ε / 2 ≤ edist (Y n ω) ((0 : ℝ → ℝ) 0)}) atTop (𝓝 0) := by
    simpa using hX2.add hY2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n ↦ zero_le) (fun n ↦ ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.zero_apply, edist_zero_right] at hω ⊢
  by_contra hcon
  rcases not_or.mp hcon with ⟨h1, h2⟩
  rw [not_le] at h1 h2
  have hab : ‖X n ω + Y n ω‖ₑ ≤ ‖X n ω‖ₑ + ‖Y n ω‖ₑ := enorm_add_le _ _
  have hlt : ‖X n ω‖ₑ + ‖Y n ω‖ₑ < ε := by
    calc ‖X n ω‖ₑ + ‖Y n ω‖ₑ < ε / 2 + ε / 2 := ENNReal.add_lt_add h1 h2
      _ = ε := ENNReal.add_halves ε
  exact absurd hω (not_le.mpr (lt_of_le_of_lt hab hlt))

/-- **`O_p(1) + O_p(1) = O_p(1)`** (blueprint `lem:op_arith` (i)).
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

/-- **`o_p(1) ⟹ O_p(1)`**: convergence in probability implies boundedness in
probability (blueprint `lem:op_arith`, used for (ii)). -/
@[specifies IsBigOpOne "places `O_p` correctly relative to `o_p`: the tightness condition is weak \
enough to be implied by convergence in probability, which rules out an accidentally too-strong \
definition"]
lemma IsLittleOpOne.isBigOpOne [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ}
    (hmeas : ∀ n, Measurable (Y n)) (hY : IsLittleOpOne μ Y) : IsBigOpOne μ Y := by
  intro ε hε
  have hev : ∀ᶠ n in atTop, μ {ω | (1 : ℝ) ≤ |Y n ω|} ≤ ε :=
    ((hY.tendsto_abs one_pos).eventually (Iio_mem_nhds hε)).mono fun n hn ↦ hn.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  choose Mn hMn using fun n ↦ exists_meas_lt (μ := μ) (hmeas n) hε
  refine ⟨1 + ∑ k ∈ Finset.range N, (|Mn k| + 1), fun n ↦ ?_⟩
  set M := 1 + ∑ k ∈ Finset.range N, (|Mn k| + 1) with hMdef
  have hM1 : (1 : ℝ) ≤ M := by
    have : 0 ≤ ∑ k ∈ Finset.range N, (|Mn k| + 1) := Finset.sum_nonneg fun k _ ↦ by positivity
    rw [hMdef]; linarith
  rcases le_or_gt N n with hn | hn
  · refine le_trans (measure_mono ?_) (hN n hn)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  · refine le_trans (measure_mono ?_) (hMn n)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hterm : |Mn n| + 1 ≤ ∑ k ∈ Finset.range N, (|Mn k| + 1) :=
      Finset.single_le_sum (f := fun k ↦ |Mn k| + 1) (fun k _ ↦ by positivity)
        (Finset.mem_range.mpr hn)
    have hle : Mn n ≤ M := by
      have := le_abs_self (Mn n); rw [hMdef]; linarith
    linarith

/-- **`o_p(1) + O_p(1) = O_p(1)`** (blueprint `lem:op_arith` (ii)). -/
lemma IsBigOpOne.add_littleOp [IsFiniteMeasure μ] {X Y : ℕ → Ω → ℝ}
    (hmeas : ∀ n, Measurable (X n)) (hX : IsLittleOpOne μ X) (hY : IsBigOpOne μ Y) :
    IsBigOpOne μ (fun n ω ↦ X n ω + Y n ω) :=
  (hX.isBigOpOne hmeas).add hY

/-- **`O_p(1) · o_p(1) = o_p(1)`** (blueprint `lem:op_arith` (iii)).
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
  obtain ⟨M, hM⟩ := hX (δ / 2) (ENNReal.half_pos hδ.ne')
  set M' := max M 1 with hM'def
  have hM'pos : 0 < M' := by rw [hM'def]; exact lt_of_lt_of_le one_pos (le_max_right M 1)
  have hMM' : ∀ n, μ {ω | M' < |X n ω|} ≤ δ / 2 := fun n ↦
    le_trans (measure_mono fun ω hω ↦ lt_of_le_of_lt (le_max_left M 1) hω) (hM n)
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
    _ ≤ δ / 2 + δ / 2 := add_le_add (hMM' n) hn
    _ = δ := ENNReal.add_halves δ

/-- **A bounded multiple preserves `O_p(1)`** (blueprint `lem:op_arith` (iv)).
If `|c n| ≤ B` for all `n` and `X = O_p(1)`, then `c n · X n = O_p(1)`. -/
lemma IsBigOpOne.bdd_mul {X : ℕ → Ω → ℝ} {c : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ n, |c n| ≤ B) (hX : IsBigOpOne μ X) :
    IsBigOpOne μ (fun n ω ↦ c n * X n ω) := by
  intro ε hε
  obtain ⟨M, hM⟩ := hX ε hε
  refine ⟨B * M + 1, fun n ↦ ?_⟩
  have hsub : {ω | B * M + 1 < |c n * X n ω|} ⊆ {ω | M < |X n ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [abs_mul] at hω
    by_contra hcon
    rw [not_lt] at hcon
    have : |c n| * |X n ω| ≤ B * M :=
      mul_le_mul (hc n) hcon (abs_nonneg _) hB
    linarith
  exact (measure_mono hsub).trans (hM n)

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

/-- **Bounded expectation gives `O_p`** (blueprint `lem:expectation_to_O`).
If `∫⁻ |X n| ≤ C · u n` for all `n` (with `u n > 0`, `C ≥ 0`), then
`X n / u n = O_p(1)`, i.e. `X n = O_p(u n)`. -/
lemma isBigOpOne_of_lintegral_le (X : ℕ → Ω → ℝ) (u : ℕ → ℝ) (C : ℝ)
    (hu : ∀ n, 0 < u n) (hC : 0 ≤ C) (hmeas : ∀ n, AEMeasurable (X n) μ)
    (hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal |X n ω| ∂μ ≤ ENNReal.ofReal (C * u n)) :
    IsBigOpOne μ (fun n ω ↦ X n ω / u n) := by
  intro ε hε
  refine ⟨C / ε.toReal + 1, fun n ↦ ?_⟩
  set M : ℝ := C / ε.toReal + 1 with hMdef
  have hMpos : 0 < M := by
    have hnn : 0 ≤ C / ε.toReal := div_nonneg hC ENNReal.toReal_nonneg
    rw [hMdef]; linarith
  have hMun : 0 < M * u n := mul_pos hMpos (hu n)
  have hmeasf : AEMeasurable (fun ω ↦ ENNReal.ofReal |X n ω|) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hmeas n).abs
  have hsub : {ω | M < |X n ω / u n|}
      ⊆ {ω | ENNReal.ofReal (M * u n) ≤ ENNReal.ofReal |X n ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [abs_div, abs_of_pos (hu n), lt_div_iff₀ (hu n)] at hω
    exact ENNReal.ofReal_le_ofReal hω.le
  have hle : ENNReal.ofReal (C / M) ≤ ε := by
    rcases eq_or_ne ε ⊤ with hεtop | hεtop
    · rw [hεtop]; exact le_top
    · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
      have hCM : C / M ≤ ε.toReal := by
        rw [div_le_iff₀ hMpos, hMdef]
        have hid : C / ε.toReal * ε.toReal = C := div_mul_cancel₀ C hεr.ne'
        nlinarith [hid, hεr]
      calc ENNReal.ofReal (C / M) ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hCM
        _ = ε := ENNReal.ofReal_toReal hεtop
  calc μ {ω | M < |X n ω / u n|}
      ≤ μ {ω | ENNReal.ofReal (M * u n) ≤ ENNReal.ofReal |X n ω|} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal |X n ω| ∂μ) / ENNReal.ofReal (M * u n) :=
        meas_ge_le_lintegral_div hmeasf (ENNReal.ofReal_ne_zero_iff.mpr hMun) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C * u n) / ENNReal.ofReal (M * u n) :=
        ENNReal.div_le_div_right (hbound n) _
    _ = ENNReal.ofReal (C / M) := by
        rw [← ENNReal.ofReal_div_of_pos hMun, mul_div_mul_right _ _ (hu n).ne']
    _ ≤ ε := hle

/-- **Bounded second moment gives `O_p`** (blueprint `lem:sq_expectation_to_O`).
If `∫⁻ (X n)² ≤ C · (u n)²` for all `n` (with `u n > 0`, `C ≥ 0`), then
`X n / u n = O_p(1)`, i.e. `X n = O_p(u n)`. This is Chebyshev's inequality: it
reduces to the `L¹` bound `isBigOpOne_of_lintegral_le` applied to `X²` with rate
`u²`, then transfers back through `IsBigOpOne.of_sq`. -/
lemma isBigOpOne_of_lintegral_sq_le (X : ℕ → Ω → ℝ) (u : ℕ → ℝ) (C : ℝ)
    (hu : ∀ n, 0 < u n) (hC : 0 ≤ C) (hmeas : ∀ n, AEMeasurable (X n) μ)
    (hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal ((X n ω) ^ 2) ∂μ ≤ ENNReal.ofReal (C * (u n) ^ 2)) :
    IsBigOpOne μ (fun n ω ↦ X n ω / u n) := by
  have hsq : IsBigOpOne μ (fun n ω ↦ (X n ω) ^ 2 / (u n) ^ 2) := by
    refine isBigOpOne_of_lintegral_le (fun n ω ↦ (X n ω) ^ 2) (fun n ↦ (u n) ^ 2) C
      (fun n ↦ pow_pos (hu n) 2) hC (fun n ↦ (hmeas n).pow_const 2) (fun n ↦ ?_)
    refine le_trans (le_of_eq ?_) (hbound n)
    exact lintegral_congr fun ω ↦ by rw [abs_of_nonneg (sq_nonneg _)]
  have heq : (fun n ω ↦ (X n ω) ^ 2 / (u n) ^ 2) = (fun n ω ↦ (X n ω / u n) ^ 2) := by
    funext n ω; rw [div_pow]
  rw [heq] at hsq
  exact hsq.of_sq

end AlphaRAR
