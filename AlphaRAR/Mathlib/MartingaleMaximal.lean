/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.QuadraticVariation
public import AlphaRAR.Mathlib.TailBoundLIntegral
public import Mathlib.Probability.Martingale.OptionalStopping
public meta import LeanSpec

/-!
# Doob's `L²` maximal inequality (`L¹` form)

For a square-integrable martingale `M`, the running maximum `max_{k ≤ N} |M k|` has `L¹` norm
bounded by `2√(E[M_N²])`:
`∫⁻ (max_{k ≤ N} |M k|) ≤ 2√(E[M_N²])`.

This combines the weak-type Doob maximal inequality (`MeasureTheory.maximal_ineq`, applied to the
submartingale `M²` via `AlphaRAR.submartingale_sq`) with the analytic core
`MeasureTheory.lintegral_le_two_mul_sqrt_of_meas_ge_le`: the former yields the inverse-square tail
`μ{max_{k≤N}|M k| ≥ t} ≤ E[M_N²]/t²`, and the latter turns it into the `L¹` bound.

## Main results

* `AlphaRAR.lintegral_sup'_abs_le_two_mul_sqrt`: the inequality above.
* `AlphaRAR.mart_maximal` and `AlphaRAR.mart_maximal_dyadic`: bounds on the backward increments,
  for `max_{m ≤ L} |M n - M (n-m)|` and for `max_{L ≤ m ≤ n} |M n - M (n-m)| / m`.
* `AlphaRAR.mart_maximal_pi` and `AlphaRAR.mart_maximal_dyadic_pi`: those two bounds for a finite
  family of martingales, with the Euclidean norm of the increment vector.
-/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- The filtration shifted by `j`: `(shiftFiltration ℱ j) k = ℱ (j + k)`. -/
def shiftFiltration (ℱ : Filtration ℕ m0) (j : ℕ) : Filtration ℕ m0 where
  seq k := ℱ (j + k)
  mono' _ _ hab := ℱ.mono (Nat.add_le_add_left hab j)
  le' k := ℱ.le (j + k)

/-- The shifted filtration reads the original one `j` steps later. -/
@[simp, specifies shiftFiltration "the whole content of the definition: which σ-algebra sits at \
each index, in particular that the shift is *forwards* (`ℱ (j + k)`, not `ℱ (k - j)`)"]
lemma shiftFiltration_apply (ℱ : Filtration ℕ m0) (j k : ℕ) :
    shiftFiltration ℱ j k = ℱ (j + k) := rfl

/-- **Shifted martingale.** For a martingale `M`, the shifted, recentred process
`S k = M (j + k) - M j` is a martingale for the shifted filtration `shiftFiltration ℱ j`, and
`S 0 = 0`. This reduces "increments from time `n` backwards" `M n - M (n - m)` to a forward
martingale starting at `0`. -/
lemma martingale_shift (hM : Martingale M ℱ μ) (j : ℕ) :
    Martingale (fun k ω ↦ M (j + k) ω - M j ω) (shiftFiltration ℱ j) μ := by
  refine ⟨fun k ↦ (hM.stronglyAdapted (j + k)).sub
    ((hM.stronglyAdapted j).mono (ℱ.mono (Nat.le_add_right j k))), fun i i' hii' ↦ ?_⟩
  have hle : j + i ≤ j + i' := Nat.add_le_add_left hii' j
  have hMj_meas : StronglyMeasurable[ℱ (j + i)] (M j) :=
    (hM.stronglyAdapted j).mono (ℱ.mono (Nat.le_add_right j i))
  have hsub := condExp_sub (hM.integrable (j + i')) (hM.integrable j) (m := ℱ (j + i))
  have hm1 : μ[M (j + i') | ℱ (j + i)] =ᵐ[μ] M (j + i) := hM.2 _ _ hle
  have hm2 : μ[M j | ℱ (j + i)] = M j :=
    condExp_of_stronglyMeasurable (ℱ.le (j + i)) hMj_meas (hM.integrable j)
  change μ[M (j + i') - M j | ℱ (j + i)] =ᵐ[μ] M (j + i) - M j
  filter_upwards [hsub, hm1] with ω e1 e2
  simp only [Pi.sub_apply] at e1 ⊢
  rw [e1, e2, congrFun hm2 ω]

/-- **Doob `L²` maximal inequality, `L¹` form.** For a square-integrable martingale `M`,
`∫⁻ (max_{k ≤ N} |M k|) ≤ 2√(E[M_N²])`. -/
lemma lintegral_sup'_abs_le_two_mul_sqrt (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((range (N + 1)).sup' nonempty_range_add_one (fun k ↦ |M k ω|)) ∂μ
      ≤ ENNReal.ofReal (2 * √(∫ ω, M N ω ^ 2 ∂μ)) := by
  set Y : Ω → ℝ := fun ω ↦ (range (N + 1)).sup' nonempty_range_add_one (fun k ↦ |M k ω|) with hYdef
  set B : ℝ := ∫ ω, M N ω ^ 2 ∂μ with hBdef
  have hBnn : 0 ≤ B := integral_nonneg fun ω ↦ sq_nonneg _
  have hMmeas : ∀ k, Measurable (M k) := fun k ↦
    (hM.stronglyAdapted k).measurable.mono (ℱ.le k) le_rfl
  have hYmeas : Measurable Y :=
    Finset.measurable_range_sup'' (fun k _ ↦ continuous_abs.measurable.comp (hMmeas k))
  have hYnn : 0 ≤ᵐ[μ] Y := ae_of_all _ fun ω ↦
    le_trans (abs_nonneg (M 0 ω))
      (Finset.le_sup' (fun k ↦ |M k ω|) (mem_range.mpr (Nat.succ_pos N)))
  have hsub := submartingale_sq hM hM2
  have hnn : (0 : ℕ → Ω → ℝ) ≤ fun n ω ↦ M n ω ^ 2 := fun n ω ↦ sq_nonneg _
  -- Inverse-square tail from the weak-type maximal inequality on `M²`.
  have htail : ∀ t : ℝ, 0 < t → μ {ω | t ≤ Y ω} ≤ ENNReal.ofReal (B / t ^ 2) := by
    intro t ht
    have hcast : ((t ^ 2).toNNReal : ℝ) = t ^ 2 := Real.coe_toNNReal _ (sq_nonneg t)
    have hset : {ω | t ≤ Y ω}
        = {ω | ((t ^ 2).toNNReal : ℝ)
            ≤ (range (N + 1)).sup' nonempty_range_add_one (M · ω ^ 2)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, hYdef, hcast, Finset.le_sup'_iff]
      constructor
      · rintro ⟨k, hk, hkle⟩
        exact ⟨k, hk, (pow_le_pow_left₀ ht.le hkle 2).trans_eq (sq_abs (M k ω))⟩
      · rintro ⟨k, hk, hkle⟩
        refine ⟨k, hk, ?_⟩
        have h := Real.sqrt_le_sqrt hkle
        rwa [Real.sqrt_sq ht.le, Real.sqrt_sq_eq_abs] at h
    rw [hset]
    have hmax := maximal_ineq hsub hnn (ε := (t ^ 2).toNNReal) N
    have hle2 : (∫ ω in {ω | ((t ^ 2).toNNReal : ℝ)
        ≤ (range (N + 1)).sup' nonempty_range_add_one (M · ω ^ 2)}, M N ω ^ 2 ∂μ) ≤ B :=
      setIntegral_le_integral ((hM2 N).integrable_sq) (ae_of_all _ fun ω ↦ sq_nonneg _)
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < t ^ 2),
      ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht.ne')) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    calc ENNReal.ofReal (t ^ 2)
          * μ {ω | ((t ^ 2).toNNReal : ℝ)
              ≤ (range (N + 1)).sup' nonempty_range_add_one (M · ω ^ 2)}
        = (↑(t ^ 2).toNNReal)
            * μ {ω | ((t ^ 2).toNNReal : ℝ)
              ≤ (range (N + 1)).sup' nonempty_range_add_one (M · ω ^ 2)} := rfl
      _ ≤ ENNReal.ofReal (∫ ω in {ω | ((t ^ 2).toNNReal : ℝ)
              ≤ (range (N + 1)).sup' nonempty_range_add_one (M · ω ^ 2)}, M N ω ^ 2 ∂μ) :=
          hmax
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hle2
  exact lintegral_le_two_mul_sqrt_of_meas_ge_le hYnn hYmeas.aemeasurable hBnn htail

/-- **Doob-type maximal bound for backward increments** (the first bound of Lemma C.1 of the
paper, in lintegral form). For a square-integrable martingale `M` whose increments have second
moment `≤ C₀`, and `L ≤ n`, the maximal backward increment satisfies
`∫⁻ (max_{m ≤ L} |M n - M (n-m)|) ≤ 4√(C₀ L)`.

Reduces to the forward Doob `L²` maximal inequality via the shifted martingale
`S k = M (n-L+k) - M (n-L)`: since `M n - M (n-m) = S L - S (L-m)`, the backward max is
`≤ 2·max_{k≤L}|S k|`, and `E[S_L²] ≤ C₀ L` by `integral_sq_le_of_increment_bound`. -/
lemma mart_maximal (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ)
    {C₀ : ℝ} (hinc : ∀ n, ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ ≤ C₀) {L n : ℕ} (hLn : L ≤ n) :
    ∫⁻ ω, ENNReal.ofReal ((range (L + 1)).sup' nonempty_range_add_one
        (fun m ↦ |M n ω - M (n - m) ω|)) ∂μ
      ≤ ENNReal.ofReal (4 * √(C₀ * L)) := by
  set j := n - L with hjdef
  have hjL : j + L = n := by omega
  have hMmeas : ∀ k, Measurable (M k) := fun k ↦
    (hM.stronglyAdapted k).measurable.mono (ℱ.le k) le_rfl
  set S : ℕ → Ω → ℝ := fun k ω ↦ M (j + k) ω - M j ω with hSdef
  have hSmart : Martingale S (shiftFiltration ℱ j) μ := martingale_shift hM j
  have hS0 : S 0 =ᵐ[μ] 0 := by filter_upwards with ω; simp [hSdef]
  have hS2 : ∀ k, MemLp (S k) 2 μ := fun k ↦ (hM2 (j + k)).sub (hM2 j)
  have hSinc : ∀ k, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ ≤ C₀ := fun k ↦ by
    have heq : (fun ω ↦ (S (k + 1) ω - S k ω) ^ 2)
        = fun ω ↦ (M (j + (k + 1)) ω - M (j + k) ω) ^ 2 := by funext ω; simp only [hSdef]; ring
    rw [heq]; exact hinc (j + k)
  have hSL2 : ∫ ω, S L ω ^ 2 ∂μ ≤ C₀ * L :=
    integral_sq_le_of_increment_bound hSmart hS2 hS0 C₀ hSinc L
  have hdoob := lintegral_sup'_abs_le_two_mul_sqrt hSmart hS2 L
  -- Measurability of the forward sup for pulling out the factor `2`.
  have hSsupmeas : Measurable (fun ω ↦
      (range (L + 1)).sup' nonempty_range_add_one (fun k ↦ |S k ω|)) :=
    Finset.measurable_range_sup'' (fun k _ ↦ continuous_abs.measurable.comp
      ((hMmeas (j + k)).sub (hMmeas j)))
  -- Pointwise reduction: `max_{m ≤ L} |M n - M (n-m)| ≤ 2·max_{k ≤ L} |S k|`.
  have hred : ∀ ω, (range (L + 1)).sup' nonempty_range_add_one (fun m ↦ |M n ω - M (n - m) ω|)
      ≤ 2 * (range (L + 1)).sup' nonempty_range_add_one (fun k ↦ |S k ω|) := fun ω ↦ by
    refine Finset.sup'_le _ _ (fun m hm ↦ ?_)
    have hmL : m ≤ L := by rw [mem_range] at hm; omega
    have hSLm : S L ω - S (L - m) ω = M n ω - M (n - m) ω := by
      simp only [hSdef]
      rw [show j + L = n from hjL, show j + (L - m) = n - m by omega]; ring
    rw [← hSLm]
    calc |S L ω - S (L - m) ω|
        ≤ |S L ω| + |S (L - m) ω| := abs_sub _ _
      _ ≤ (range (L + 1)).sup' nonempty_range_add_one (fun k ↦ |S k ω|)
            + (range (L + 1)).sup' nonempty_range_add_one (fun k ↦ |S k ω|) :=
          add_le_add
            (Finset.le_sup' (fun k ↦ |S k ω|) (mem_range.mpr (show L < L + 1 by omega)))
            (Finset.le_sup' (fun k ↦ |S k ω|) (mem_range.mpr (show L - m < L + 1 by omega)))
      _ = 2 * (range (L + 1)).sup' nonempty_range_add_one (fun k ↦ |S k ω|) := by ring
  calc ∫⁻ ω, ENNReal.ofReal ((range (L + 1)).sup' nonempty_range_add_one
          (fun m ↦ |M n ω - M (n - m) ω|)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * (range (L + 1)).sup' nonempty_range_add_one
          (fun k ↦ |S k ω|)) ∂μ :=
        lintegral_mono_ae (ae_of_all _ fun ω ↦ ENNReal.ofReal_le_ofReal (hred ω))
    _ = 2 * ∫⁻ ω, ENNReal.ofReal ((range (L + 1)).sup' nonempty_range_add_one
          (fun k ↦ |S k ω|)) ∂μ := by
        rw [← lintegral_const_mul 2 hSsupmeas.ennreal_ofReal]
        refine lintegral_congr fun ω ↦ ?_
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ 2 * ENNReal.ofReal (2 * √(∫ ω, S L ω ^ 2 ∂μ)) := by gcongr
    _ = ENNReal.ofReal (4 * √(∫ ω, S L ω ^ 2 ∂μ)) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (4 * √(C₀ * L)) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hSL2) (by norm_num))


/-- Geometric-series core: `∑_{j=jL}^{j1} (1/√2)^j ≤ 4/√L` when `L ≤ 2^jL` and `0 < L`. -/
private lemma geom_dyadic_sum_le {L : ℕ} (hL : 0 < L) (jL j1 : ℕ) (hjL : L ≤ 2 ^ jL) :
    ∑ j ∈ Finset.Icc jL j1, ((√2)⁻¹) ^ j ≤ 4 / √L := by
  set r : ℝ := (√2)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hsqrt2 : (4 : ℝ) / 3 ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr34 : r ≤ 3 / 4 := by
    rw [hr, inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hr1 : r < 1 := by linarith
  have hLr : (0:ℝ) < √L := Real.sqrt_pos.mpr (by exact_mod_cast hL)
  have hgeom : ∀ N : ℕ, ∑ i ∈ Finset.range N, r ^ i ≤ 4 := by
    intro N
    have hstep : ∑ i ∈ Finset.range N, r ^ i ≤ (1 - r)⁻¹ := by
      rw [geom_sum_eq (ne_of_lt hr1) N,
        show (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) by rw [← neg_div_neg_eq]; ring_nf,
        div_le_iff₀ (by linarith : (0:ℝ) < 1 - r), inv_mul_cancel₀ (by linarith : (1:ℝ) - r ≠ 0)]
      have : (0:ℝ) ≤ r ^ N := by positivity
      linarith
    have h4 : (1 - r)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ (by linarith : (0:ℝ) < 1 - r) (by norm_num : (0:ℝ) < 4)]; linarith
    linarith
  have hstepA : ∑ j ∈ Finset.Icc jL j1, r ^ j ≤ 4 * r ^ jL := by
    rw [show Finset.Icc jL j1 = Finset.Ico jL (j1 + 1) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    simp_rw [pow_add, ← Finset.mul_sum]
    rw [mul_comm]
    gcongr
    exact hgeom _
  have hstepB : r ^ jL ≤ (√L)⁻¹ := by
    have hinv : (r ^ jL)⁻¹ = (√2) ^ jL := by rw [← inv_pow, hr, inv_inv]
    rw [le_inv_comm₀ (by positivity) hLr, hinv]
    have hsq : ((√2) ^ jL) ^ 2 = (2:ℝ) ^ jL := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    calc √L ≤ √(((√2) ^ jL) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hsq]
          have : (L:ℝ) ≤ ((2 ^ jL : ℕ) : ℝ) := by exact_mod_cast hjL
          rwa [Nat.cast_pow, Nat.cast_ofNat] at this
      _ = (√2) ^ jL := Real.sqrt_sq (by positivity)
  calc ∑ j ∈ Finset.Icc jL j1, r ^ j ≤ 4 * r ^ jL := hstepA
    _ ≤ 4 * (√L)⁻¹ := by gcongr
    _ = 4 / √L := by rw [div_eq_mul_inv]

/-- **Dyadic maximal bound** (a form of the second bound of Lemma C.1 of the paper, as an
lintegral bound and with a larger constant). For a square-integrable martingale `M` whose
increments have second moment `≤ C₀`, and `0 < L ≤ n`,
`∫⁻ (max_{L ≤ m ≤ n} |M n - M (n-m)| / m) ≤ 32√(C₀/L)`. -/
lemma mart_maximal_dyadic (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hinc : ∀ n, ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ ≤ C₀)
    {L n : ℕ} (hL : 0 < L) (hLn : L ≤ n) :
    ∫⁻ ω, ENNReal.ofReal ((Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
        (fun m ↦ |M n ω - M (n - m) ω| / (m : ℝ))) ∂μ
      ≤ ENNReal.ofReal (32 * √(C₀ / L)) := by
  have hMmeas : ∀ k, Measurable (M k) := fun k ↦
    (hM.stronglyAdapted k).measurable.mono (ℱ.le k) le_rfl
  set jL := Nat.log 2 L + 1 with hjLdef
  set j1 := Nat.log 2 n + 1 with hj1def
  set L' : ℕ → ℕ := fun j ↦ min (2 ^ j - 1) n with hL'def
  set g : ℕ → Ω → ℝ := fun j ω ↦ (Finset.range (L' j + 1)).sup' nonempty_range_add_one
    (fun m ↦ |M n ω - M (n - m) ω|) with hgdef
  set h : ℕ → Ω → ℝ := fun j ω ↦ (2 / (2:ℝ) ^ j) * g j ω with hhdef
  have hgnn : ∀ j ω, 0 ≤ g j ω := fun j ω ↦
    le_trans (abs_nonneg _) (Finset.le_sup' (f := fun m ↦ |M n ω - M (n - m) ω|)
      (mem_range.mpr (Nat.succ_pos _)))
  have hhnn : ∀ j ω, 0 ≤ h j ω := fun j ω ↦ mul_nonneg (by positivity) (hgnn j ω)
  have hmeas_g : ∀ j, Measurable (fun ω ↦ ENNReal.ofReal (g j ω)) := fun j ↦
    (Finset.measurable_range_sup'' (fun m _ ↦
      continuous_abs.measurable.comp ((hMmeas n).sub (hMmeas (n - m))))).ennreal_ofReal
  -- Pointwise dyadic decomposition.
  have hpt : ∀ ω, (Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
        (fun m ↦ |M n ω - M (n - m) ω| / (m : ℝ)) ≤ ∑ j ∈ Finset.Icc jL j1, h j ω := by
    intro ω
    refine Finset.sup'_le _ _ (fun m hm ↦ ?_)
    rw [Finset.mem_Icc] at hm
    obtain ⟨hLm, hmn⟩ := hm
    have hm0 : m ≠ 0 := by omega
    have hmpos : (0:ℝ) < (m : ℝ) := by positivity
    have hjmem : Nat.log 2 m + 1 ∈ Finset.Icc jL j1 := by
      rw [Finset.mem_Icc, hjLdef, hj1def]
      exact ⟨by have := Nat.log_mono_right (b := 2) hLm; omega,
        by have := Nat.log_mono_right (b := 2) hmn; omega⟩
    have hlow : (2:ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hm0
    have hup : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have hfg : |M n ω - M (n - m) ω| ≤ g (Nat.log 2 m + 1) ω := by
      simp only [hgdef]
      apply Finset.le_sup' (f := fun m' ↦ |M n ω - M (n - m') ω|)
      rw [Finset.mem_range]
      simp only [hL'def]
      omega
    have h1m : 1 / (m : ℝ) ≤ 2 / (2:ℝ) ^ (Nat.log 2 m + 1) := by
      rw [div_le_iff₀ hmpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul, pow_succ]
      nlinarith [hlow]
    have hterm : |M n ω - M (n - m) ω| / (m : ℝ) ≤ h (Nat.log 2 m + 1) ω := by
      rw [hhdef]
      simp only
      calc |M n ω - M (n - m) ω| / (m : ℝ)
          = |M n ω - M (n - m) ω| * (1 / (m : ℝ)) := by ring
        _ ≤ g (Nat.log 2 m + 1) ω * (2 / (2:ℝ) ^ (Nat.log 2 m + 1)) :=
            mul_le_mul hfg h1m (by positivity) (hgnn _ _)
        _ = 2 / (2:ℝ) ^ (Nat.log 2 m + 1) * g (Nat.log 2 m + 1) ω := by ring
    exact le_trans hterm (Finset.single_le_sum (fun j' _ ↦ hhnn j' ω) hjmem)
  -- Per-scale bound via mart_maximal.
  have hperscale : ∀ j, ∫⁻ ω, ENNReal.ofReal (h j ω) ∂μ
      ≤ ENNReal.ofReal (8 * √C₀ * ((√2)⁻¹) ^ j) := by
    intro j
    have hstep : ∫⁻ ω, ENNReal.ofReal (h j ω) ∂μ
        = ENNReal.ofReal (2 / (2:ℝ) ^ j) * ∫⁻ ω, ENNReal.ofReal (g j ω) ∂μ := by
      rw [← lintegral_const_mul _ (hmeas_g j)]
      apply lintegral_congr
      intro ω
      simp only [hhdef]
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [hstep]
    have hmm := mart_maximal hM hM2 hinc (L := L' j) (n := n)
      (le_trans (min_le_right _ _) le_rfl)
    have hL'le : ((L' j : ℕ) : ℝ) ≤ (2:ℝ) ^ j := by
      have hnat : L' j ≤ 2 ^ j := le_trans (min_le_left (2 ^ j - 1) n) (Nat.sub_le _ _)
      calc ((L' j : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2:ℝ) ^ j := by rw [Nat.cast_pow, Nat.cast_ofNat]
    -- real inequality per scale
    have hreal : (2 / (2:ℝ) ^ j) * (4 * √(C₀ * (L' j : ℝ)))
        ≤ 8 * √C₀ * ((√2)⁻¹) ^ j := by
      set s : ℝ := √((2:ℝ) ^ j) with hsdef
      have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
      have hs2 : s * s = (2:ℝ) ^ j := Real.mul_self_sqrt (by positivity)
      have hsqrtpow : √2 ^ j = √((2:ℝ) ^ j) := by
        rw [show ((2:ℝ) ^ j) = (√2 ^ j) ^ 2 by
          rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)],
          Real.sqrt_sq (by positivity)]
      have hrj : ((√2)⁻¹) ^ j = s⁻¹ := by rw [inv_pow, hsqrtpow, ← hsdef]
      have hXle : √(C₀ * (L' j : ℝ)) ≤ √C₀ * s := by
        rw [Real.sqrt_mul hC₀, hsdef]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL'le) (Real.sqrt_nonneg _)
      rw [hrj, ← hs2]
      calc 2 / (s * s) * (4 * √(C₀ * (L' j : ℝ)))
          = 8 * √(C₀ * (L' j : ℝ)) / (s * s) := by ring
        _ ≤ 8 * (√C₀ * s) / (s * s) := by gcongr
        _ = 8 * √C₀ * s⁻¹ := by field_simp
    calc ENNReal.ofReal (2 / (2:ℝ) ^ j) * ∫⁻ ω, ENNReal.ofReal (g j ω) ∂μ
        ≤ ENNReal.ofReal (2 / (2:ℝ) ^ j) * ENNReal.ofReal (4 * √(C₀ * (L' j : ℝ))) :=
          mul_le_mul' le_rfl hmm
      _ = ENNReal.ofReal ((2 / (2:ℝ) ^ j) * (4 * √(C₀ * (L' j : ℝ)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (8 * √C₀ * ((√2)⁻¹) ^ j) :=
          ENNReal.ofReal_le_ofReal hreal
  -- Assembly.
  calc ∫⁻ ω, ENNReal.ofReal ((Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
          (fun m ↦ |M n ω - M (n - m) ω| / (m : ℝ))) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (∑ j ∈ Finset.Icc jL j1, h j ω) ∂μ :=
        lintegral_mono (fun ω ↦ ENNReal.ofReal_le_ofReal (hpt ω))
    _ = ∫⁻ ω, ∑ j ∈ Finset.Icc jL j1, ENNReal.ofReal (h j ω) ∂μ := by
        apply lintegral_congr
        intro ω
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hhnn j ω)]
    _ = ∑ j ∈ Finset.Icc jL j1, ∫⁻ ω, ENNReal.ofReal (h j ω) ∂μ :=
        lintegral_finsetSum _ (fun j _ ↦ by
          simp only [hhdef]
          exact (((Finset.measurable_range_sup'' (fun m _ ↦
            continuous_abs.measurable.comp ((hMmeas n).sub (hMmeas (n - m))))).const_mul
            (2 / (2:ℝ) ^ j))).ennreal_ofReal)
    _ ≤ ∑ j ∈ Finset.Icc jL j1, ENNReal.ofReal (8 * √C₀ * ((√2)⁻¹) ^ j) :=
        Finset.sum_le_sum (fun j _ ↦ hperscale j)
    _ = ENNReal.ofReal (∑ j ∈ Finset.Icc jL j1, 8 * √C₀ * ((√2)⁻¹) ^ j) :=
        (ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ by positivity)).symm
    _ ≤ ENNReal.ofReal (32 * √(C₀ / L)) := by
        apply ENNReal.ofReal_le_ofReal
        have hjL2 : L ≤ 2 ^ jL := (Nat.lt_pow_succ_log_self (by norm_num) L).le
        have hsum : ∑ j ∈ Finset.Icc jL j1, 8 * √C₀ * ((√2)⁻¹) ^ j
            = 8 * √C₀ * ∑ j ∈ Finset.Icc jL j1, ((√2)⁻¹) ^ j :=
          (Finset.mul_sum _ _ _).symm
        rw [hsum]
        calc 8 * √C₀ * ∑ j ∈ Finset.Icc jL j1, ((√2)⁻¹) ^ j
            ≤ 8 * √C₀ * (4 / √L) := by
              gcongr
              exact geom_dyadic_sum_le hL jL j1 hjL2
          _ = 32 * √(C₀ / L) := by
              rw [Real.sqrt_div hC₀]; ring

/-- L²–L¹ bound: `√(∑ v_k²) ≤ ∑ |v_k|`. -/
private lemma sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    √(∑ k, (v k) ^ 2) ≤ ∑ k, |v k| := by
  rw [show (∑ k, (v k) ^ 2) = ∑ k, |v k| ^ 2 by simp_rw [sq_abs]]
  calc √(∑ k, |v k| ^ 2)
      ≤ √((∑ k, |v k|) ^ 2) :=
        Real.sqrt_le_sqrt (sum_sq_le_sq_sum_of_nonneg (fun i _ ↦ abs_nonneg _))
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg (fun i _ ↦ abs_nonneg _))

/-- **Vector Doob maximal bound for backward increments.** For a finite family `M` of
square-integrable martingales with uniformly bounded increment second moments (`≤ C₀`), the
running maximum of the Euclidean norm of the increment vector satisfies
`∫⁻ (max_{m ≤ L} ‖(M_k n - M_k (n-m))_k‖) ≤ (card ι)·4√(C₀ L)`. -/
lemma mart_maximal_pi {ι : Type*} [Fintype ι] (M : ι → ℕ → Ω → ℝ)
    (hM : ∀ k, Martingale (M k) ℱ μ)
    (hM2 : ∀ k n, MemLp (M k n) 2 μ)
    {C₀ : ℝ} (hinc : ∀ k n, ∫ ω, (M k (n + 1) ω - M k n ω) ^ 2 ∂μ ≤ C₀) {L n : ℕ} (hLn : L ≤ n) :
    ∫⁻ ω, ENNReal.ofReal ((Finset.range (L + 1)).sup' nonempty_range_add_one
        (fun m ↦ √(∑ k, (M k n ω - M k (n - m) ω) ^ 2))) ∂μ
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (4 * √(C₀ * L))) := by
  have hMmeas : ∀ k j, Measurable (M k j) := fun k j ↦
    ((hM k).stronglyAdapted j).measurable.mono (ℱ.le j) le_rfl
  set F : ι → Ω → ℝ := fun k ω ↦ (Finset.range (L + 1)).sup' nonempty_range_add_one
    (fun m ↦ |M k n ω - M k (n - m) ω|) with hFdef
  have hFnn : ∀ k ω, 0 ≤ F k ω := fun k ω ↦
    le_trans (abs_nonneg _) (Finset.le_sup' (f := fun m ↦ |M k n ω - M k (n - m) ω|)
      (mem_range.mpr (Nat.succ_pos _)))
  have hFmeas : ∀ k, Measurable (fun ω ↦ ENNReal.ofReal (F k ω)) := fun k ↦
    (Finset.measurable_range_sup'' (fun m _ ↦
      continuous_abs.measurable.comp ((hMmeas k n).sub (hMmeas k (n - m))))).ennreal_ofReal
  -- Pointwise: max of the norm ≤ sum over coordinates of the coordinate maxima.
  have hpt : ∀ ω, (Finset.range (L + 1)).sup' nonempty_range_add_one
        (fun m ↦ √(∑ k, (M k n ω - M k (n - m) ω) ^ 2)) ≤ ∑ k, F k ω := by
    intro ω
    refine Finset.sup'_le _ _ (fun m hm ↦ ?_)
    calc √(∑ k, (M k n ω - M k (n - m) ω) ^ 2)
        ≤ ∑ k, |M k n ω - M k (n - m) ω| := sqrt_sum_sq_le_sum_abs _
      _ ≤ ∑ k, F k ω := Finset.sum_le_sum (fun k _ ↦
          Finset.le_sup' (f := fun m' ↦ |M k n ω - M k (n - m') ω|) hm)
  calc ∫⁻ ω, ENNReal.ofReal ((Finset.range (L + 1)).sup' nonempty_range_add_one
          (fun m ↦ √(∑ k, (M k n ω - M k (n - m) ω) ^ 2))) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (∑ k, F k ω) ∂μ :=
        lintegral_mono (fun ω ↦ ENNReal.ofReal_le_ofReal (hpt ω))
    _ = ∫⁻ ω, ∑ k, ENNReal.ofReal (F k ω) ∂μ := by
        apply lintegral_congr
        intro ω
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ hFnn k ω)]
    _ = ∑ k, ∫⁻ ω, ENNReal.ofReal (F k ω) ∂μ := lintegral_finsetSum _ (fun k _ ↦ hFmeas k)
    _ ≤ ∑ _k : ι, ENNReal.ofReal (4 * √(C₀ * L)) :=
        Finset.sum_le_sum (fun k _ ↦
          mart_maximal (hM k) (hM2 k) (hinc k) hLn)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (4 * √(C₀ * L))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- **Vector dyadic maximal bound.** For a finite family `M` of square-integrable martingales with
uniformly bounded increment second moments (`≤ C₀`), and `0 < L ≤ n`,
`∫⁻ (max_{L ≤ m ≤ n} ‖(M_k n - M_k (n-m))_k‖ / m) ≤ (card ι)·32√(C₀/L)`. -/
lemma mart_maximal_dyadic_pi {ι : Type*} [Fintype ι] (M : ι → ℕ → Ω → ℝ)
    (hM : ∀ k, Martingale (M k) ℱ μ)
    (hM2 : ∀ k n, MemLp (M k n) 2 μ)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hinc : ∀ k n, ∫ ω, (M k (n + 1) ω - M k n ω) ^ 2 ∂μ ≤ C₀)
    {L n : ℕ} (hL : 0 < L) (hLn : L ≤ n) :
    ∫⁻ ω, ENNReal.ofReal ((Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
        (fun m ↦ √(∑ k, (M k n ω - M k (n - m) ω) ^ 2) / (m : ℝ))) ∂μ
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (32 * √(C₀ / L))) := by
  have hMmeas : ∀ k j, Measurable (M k j) := fun k j ↦
    ((hM k).stronglyAdapted j).measurable.mono (ℱ.le j) le_rfl
  set F : ι → Ω → ℝ := fun k ω ↦ (Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
    (fun m ↦ |M k n ω - M k (n - m) ω| / (m : ℝ)) with hFdef
  have hFnn : ∀ k ω, 0 ≤ F k ω := fun k ω ↦
    le_trans (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (Finset.le_sup' (f := fun m ↦ |M k n ω - M k (n - m) ω| / (m : ℝ))
        (Finset.mem_Icc.mpr ⟨le_rfl, hLn⟩))
  have hFmeas : ∀ k, Measurable (fun ω ↦ ENNReal.ofReal (F k ω)) := fun k ↦ by
    apply Measurable.ennreal_ofReal
    simp only [hFdef]
    rw [show (fun ω ↦ (Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
        (fun m ↦ |M k n ω - M k (n - m) ω| / (m : ℝ)))
        = (Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
          (fun m ω ↦ |M k n ω - M k (n - m) ω| / (m : ℝ)) from by
        ext ω; rw [Finset.sup'_apply]]
    exact Finset.measurable_sup' _ (fun m _ ↦
      (continuous_abs.measurable.comp ((hMmeas k n).sub (hMmeas k (n - m)))).div_const _)
  have hpt : ∀ ω, (Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
        (fun m ↦ √(∑ k, (M k n ω - M k (n - m) ω) ^ 2) / (m : ℝ)) ≤ ∑ k, F k ω := by
    intro ω
    refine Finset.sup'_le _ _ (fun m hm ↦ ?_)
    calc √(∑ k, (M k n ω - M k (n - m) ω) ^ 2) / (m : ℝ)
        ≤ (∑ k, |M k n ω - M k (n - m) ω|) / (m : ℝ) := by
          gcongr
          exact sqrt_sum_sq_le_sum_abs _
      _ = ∑ k, |M k n ω - M k (n - m) ω| / (m : ℝ) := by rw [Finset.sum_div]
      _ ≤ ∑ k, F k ω := Finset.sum_le_sum (fun k _ ↦
          Finset.le_sup' (f := fun m' ↦ |M k n ω - M k (n - m') ω| / (m' : ℝ)) hm)
  calc ∫⁻ ω, ENNReal.ofReal ((Finset.Icc L n).sup' (Finset.nonempty_Icc.mpr hLn)
          (fun m ↦ √(∑ k, (M k n ω - M k (n - m) ω) ^ 2) / (m : ℝ))) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (∑ k, F k ω) ∂μ :=
        lintegral_mono (fun ω ↦ ENNReal.ofReal_le_ofReal (hpt ω))
    _ = ∫⁻ ω, ∑ k, ENNReal.ofReal (F k ω) ∂μ := by
        apply lintegral_congr
        intro ω
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ hFnn k ω)]
    _ = ∑ k, ∫⁻ ω, ENNReal.ofReal (F k ω) ∂μ := lintegral_finsetSum _ (fun k _ ↦ hFmeas k)
    _ ≤ ∑ _k : ι, ENNReal.ofReal (32 * √(C₀ / L)) :=
        Finset.sum_le_sum (fun k _ ↦
          mart_maximal_dyadic (hM k) (hM2 k) hC₀ (hinc k) hL hLn)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (32 * √(C₀ / L))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]


end AlphaRAR
