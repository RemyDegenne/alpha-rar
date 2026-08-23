/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.Kronecker
public import AlphaRAR.Mathlib.QuadraticVariation
public import Mathlib.Analysis.PSeries
public import Mathlib.Probability.Martingale.Convergence
public meta import LeanSpec

/-!
# Strong law of large numbers for martingales

If a square-integrable martingale `M` has `M 0 = 0` and increment variances summable against `k⁻²`
(in particular for uniformly bounded increments), then `M n / n → 0` almost everywhere. Mathlib has
the i.i.d. strong law but no martingale version; the classical route below is Kolmogorov's: reduce
to the a.s. convergence of the weighted series `∑ ΔM_k / k` via the `L²` martingale convergence
theorem, then apply Kronecker's lemma (`AlphaRAR.kronecker`).

## Main results

* `AlphaRAR.martingale_ae_tendsto_of_eLpNorm_two_le`: an `L²`-bounded martingale converges a.e.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M S : ℕ → Ω → ℝ}

/-- **An `L²`-bounded martingale converges almost everywhere** (blueprint `lem:slln_l2_conv`).
If `S` is a martingale with `eLpNorm (S n) 2 μ ≤ C` for all `n`, then `S n` converges a.e. to a
(finite) limit. This is the `L²`- (hence `L¹`-) bounded martingale convergence theorem: on a
probability space `‖·‖₁ ≤ ‖·‖₂`, so the uniform `L²` bound gives a uniform `L¹` bound, and Mathlib's
`Submartingale.exists_ae_tendsto_of_bdd` applies. -/
lemma martingale_ae_tendsto_of_eLpNorm_two_le [IsProbabilityMeasure μ]
    (hS : Martingale S ℱ μ) {C : ℝ≥0} (hbdd : ∀ n, eLpNorm (S n) 2 μ ≤ C) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (S · ω) atTop (𝓝 c) :=
  hS.submartingale.exists_ae_tendsto_of_bdd (R := C) fun n ↦
    le_trans (eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) one_le_two
      ((hS.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) (hbdd n)

/-- Integral form of `lem:slln_l2_conv`: a martingale `S` with square-integrable values and
`∫ (S n)² ∂μ ≤ C` for all `n` converges a.e. to a finite limit. The uniform second-moment bound
gives `eLpNorm (S n) 2 μ ≤ √C`, so `martingale_ae_tendsto_of_eLpNorm_two_le` applies. -/
lemma martingale_ae_tendsto_of_integral_sq_le [IsProbabilityMeasure μ]
    (hS : Martingale S ℱ μ) (hS2 : ∀ n, MemLp (S n) 2 μ)
    {C : ℝ} (hbdd : ∀ n, ∫ ω, (S n ω) ^ 2 ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (S · ω) atTop (𝓝 c) := by
  have hCnn : 0 ≤ C := le_trans (integral_nonneg fun ω ↦ sq_nonneg _) (hbdd 0)
  refine martingale_ae_tendsto_of_eLpNorm_two_le hS (C := (√C).toNNReal) fun n ↦ ?_
  have hmem : MemLp (S n) 2 μ := hS2 n
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num)]
  have h2 : ((2 : ℝ≥0∞).toReal)⁻¹ = 1 / 2 := by norm_num
  have hnorm : (fun ω ↦ ‖S n ω‖ ^ ((2 : ℝ≥0∞).toReal)) = fun ω ↦ (S n ω) ^ 2 := by
    funext ω; rw [show ((2 : ℝ≥0∞).toReal) = 2 by norm_num, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hnorm, h2, ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hbdd n))

/-- The **weighted increment series** `S n = ∑_{k<n} (M (k+1) − M k)/w k` of a martingale `M`, for
an arbitrary deterministic weight `w`, is itself a martingale (part of blueprint
`lem:slln_weighted`).
Each increment `ΔS_n = ΔM_n/w n` is a scaled martingale difference, so
`𝔼[ΔS_n ∣ ℱ_n] = (w n)⁻¹ 𝔼[ΔM_n ∣ ℱ_n] = 0`. The classical case is `w k = k+1`. -/
lemma martingale_weightedSeries [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (w : ℕ → ℝ) :
    Martingale (fun n ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / w k) ℱ μ := by
  have hint : ∀ n, Integrable (M n) μ := hM.integrable
  have hadapt : ∀ n, StronglyMeasurable[ℱ n]
      (fun ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / w k) := fun n ↦
    Finset.stronglyMeasurable_fun_sum _ fun k hk ↦
      (((hM.stronglyMeasurable (k + 1)).mono (ℱ.mono (by rw [Finset.mem_range] at hk; omega))).sub
        ((hM.stronglyMeasurable k).mono (ℱ.mono (by rw [Finset.mem_range] at hk; omega)))).div
        stronglyMeasurable_const
  have hSint : ∀ n, Integrable (fun ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / w k) μ :=
    fun n ↦ integrable_finsetSum _ fun k _ ↦ ((hint (k + 1)).sub (hint k)).div_const _
  refine martingale_nat hadapt hSint (fun n ↦ ?_)
  -- `S n =ᵐ 𝔼[S (n+1) ∣ ℱ n]`: split off the last increment, which conditions to `0`.
  have hSsucc : (fun ω ↦ ∑ k ∈ range (n + 1), (M (k + 1) ω - M k ω) / w k)
      = (fun ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / w k)
        + (w n)⁻¹ • (M (n + 1) - M n) := by
    funext ω; simp only [Finset.sum_range_succ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]; ring
  have hincr : Integrable ((w n)⁻¹ • (M (n + 1) - M n)) μ :=
    (((hint (n + 1)).sub (hint n))).smul _
  have hself := condExp_of_stronglyMeasurable (ℱ.le n) (hadapt n) (hSint n)
  have hzero : μ[(w n)⁻¹ • (M (n + 1) - M n) | ℱ n] =ᵐ[μ] 0 := by
    have hd : μ[M (n + 1) - M n | ℱ n] =ᵐ[μ] 0 := by
      refine (condExp_sub (hint (n + 1)) (hint n) _).trans ?_
      filter_upwards [hM.condExp_ae_eq (Nat.le_succ n), hM.condExp_ae_eq (le_refl n)]
        with ω hω1 hω2
      simp only [Pi.sub_apply, Pi.zero_apply, hω1, hω2, sub_self]
    refine (condExp_smul _ _ _).trans ?_
    filter_upwards [hd] with ω hω
    simp only [Pi.smul_apply, Pi.zero_apply, hω, smul_zero]
  rw [hSsucc]
  filter_upwards [condExp_add (hSint n) hincr (ℱ n), hzero] with ω ha h2
  rw [ha, Pi.add_apply, congrFun hself ω, h2, Pi.zero_apply, add_zero]

/-- **Martingale SLLN** (the a.e. convergence `M n / n → 0`), given a uniform second-moment bound on
the weighted increment series `S n = ∑_{k<n} (M (k+1) − M k)/(k+1)`. Blueprint `thm:mart_slln`,
modulo the identity `∫ (S n)² = ∑_{k<n} 𝔼[(ΔM_k)²]/(k+1)²` (which turns the summability hypothesis
into the bound `hbdd` below). By `martingale_weightedSeries` and
`martingale_ae_tendsto_of_integral_sq_le`, `S n` converges a.e.; Kronecker's lemma
(`AlphaRAR.kronecker'`, applied pathwise with `x_k = ΔM_k/(k+1)`) then gives `M n / n → 0`, since
`∑_{k<n} (k+1)·x_k = ∑_{k<n} ΔM_k = M n - M 0` and the initial value is washed out by `n → ∞`. -/
theorem martingale_div_atTop_ae_tendsto_zero [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ)
    (hS2 : ∀ n, MemLp (fun ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) 2 μ)
    {C : ℝ} (hbdd : ∀ n, ∫ ω, (∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) ^ 2 ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ M n ω / n) atTop (𝓝 0) := by
  have hconv := martingale_ae_tendsto_of_integral_sq_le
    (martingale_weightedSeries hM (fun k ↦ (k : ℝ) + 1)) hS2 hbdd
  filter_upwards [hconv] with ω hcω
  obtain ⟨c, hc⟩ := hcω
  have hstep0 : Tendsto (fun n ↦ (M n ω - M 0 ω) / n) atTop (𝓝 0) := by
    refine (kronecker' hc).congr' (Eventually.of_forall fun n ↦ ?_)
    have hterm : ∀ k ∈ range n, ((k : ℝ) + 1) * ((M (k + 1) ω - M k ω) / ((k : ℝ) + 1))
        = (M · ω) (k + 1) - (M · ω) k := fun k _ ↦ by
      rw [mul_div_cancel₀ _ (by positivity)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (M · ω) n]
    simp only [div_eq_inv_mul]
  have h0 : Tendsto (fun n : ℕ ↦ M 0 ω / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := hstep0.add h0
  rw [add_zero] at hsum
  exact hsum.congr fun n ↦ by ring

/-- **General-weight martingale SLLN.** For a martingale `M` and a positive,
monotone, unbounded weight `a` (`a n ↑ ∞`), if the weighted increment series
`S n = ∑_{k<n} (M (k+1) − M k)/a (k+1)` has a uniform second-moment bound, then `M n / a n → 0`
almost everywhere. `martingale_weightedSeries` (general weight) gives the martingale,
`martingale_ae_tendsto_of_integral_sq_le` its a.e. convergence, and Kronecker's lemma
(`kronecker_general` with `b = a`, since `a (k+1)·(ΔM_k/a (k+1)) = ΔM_k`) telescopes to `M n / a n`.
This is the `a n = n` case (`martingale_div_atTop_ae_tendsto_zero`) with a general normalizer, used
for the loglog-scale weight `a n = √(2 n log log n)` of the Hartman–Wintner medium part. -/
lemma martingale_div_weight_ae_tendsto_zero [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) {a : ℕ → ℝ}
    (ha_pos : ∀ n, 0 < a n) (ha_mono : Monotone a) (ha_top : Tendsto a atTop atTop)
    (hS2 : ∀ n, MemLp (fun ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / a (k + 1)) 2 μ)
    {C : ℝ} (hbdd : ∀ n, ∫ ω, (∑ k ∈ range n, (M (k + 1) ω - M k ω) / a (k + 1)) ^ 2 ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ M n ω / a n) atTop (𝓝 0) := by
  have hconv := martingale_ae_tendsto_of_integral_sq_le
    (martingale_weightedSeries hM (fun k ↦ a (k + 1))) hS2 hbdd
  filter_upwards [hconv] with ω hcω
  obtain ⟨c, hc⟩ := hcω
  have hstep0 : Tendsto (fun n ↦ (M n ω - M 0 ω) / a n) atTop (𝓝 0) := by
    refine (kronecker_general ha_pos ha_mono ha_top hc).congr' (Eventually.of_forall fun n ↦ ?_)
    have hterm : ∀ k ∈ range n, a (k + 1) * ((M (k + 1) ω - M k ω) / a (k + 1))
        = (M · ω) (k + 1) - (M · ω) k := fun k _ ↦ by
      rw [mul_div_cancel₀ _ (ha_pos (k + 1)).ne']
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (M · ω) n]
    simp only [div_eq_inv_mul]
  have h0 : Tendsto (fun n ↦ M 0 ω / a n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ha_top
  have hsum := hstep0.add h0
  rw [add_zero] at hsum
  exact hsum.congr fun n ↦ by ring

/-- **Martingale SLLN for bounded increments** (blueprint `cor:mart_slln_bounded`). If `M` is a
martingale with a.e. uniformly bounded increments `|M (k+1) − M k| ≤ c`, then
`M n / n → 0` almost everywhere.

The bounded increments make everything square-integrable, and give the orthogonality bound
`∫ (S n)² = ∑_{k<n} ∫ (ΔM_k / (k+1))² ≤ c² ∑_{k<n} (k+1)⁻² ≤ c² ∑' (k+1)⁻² < ∞`
on the weighted increment series `S`, via the discrete Itô isometry
(`integral_sq_eq_integral_predQuadVar`) and the telescoping of its predictable quadratic variation
(`integral_predQuadVar_succ_sub`). `martingale_div_atTop_ae_tendsto_zero` then applies. -/
lemma martingale_div_atTop_ae_tendsto_zero_of_bdd [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) {c : ℝ}
    (hb : ∀ k, ∀ᵐ ω ∂μ, |M (k + 1) ω - M k ω| ≤ c) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ M n ω / n) atTop (𝓝 0) := by
  classical
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / ((k : ℝ) + 1) with hSdef
  have hSmart : Martingale S ℱ μ := martingale_weightedSeries hM (fun k ↦ (k : ℝ) + 1)
  have hS0 : S 0 =ᵐ[μ] 0 := by filter_upwards with ω; simp [hSdef]
  -- Each increment `ΔM_k` is square-integrable (bounded on a probability space).
  have hdmem : ∀ k, MemLp (fun ω ↦ M (k + 1) ω - M k ω) 2 μ := fun k ↦
    memLp_increment_of_bound (hM.integrable k).aestronglyMeasurable
      (hM.integrable (k + 1)).aestronglyMeasurable (hb k)
  -- The scaled increments `ΔS_k = ΔM_k / (k+1)`, the series `S n`, and its increments are `L²`.
  have hDmem : ∀ k, MemLp (fun ω ↦ (M (k + 1) ω - M k ω) / ((k : ℝ) + 1)) 2 μ := fun k ↦ by
    simpa only [div_eq_inv_mul] using (hdmem k).const_mul ((k : ℝ) + 1)⁻¹
  have hSmem : ∀ n, MemLp (S n) 2 μ := fun n ↦
    memLp_finsetSum (Finset.range n) fun k _ ↦ hDmem k
  -- Orthogonality / discrete Itô isometry: `∫ (S n)² = ∑_{k<n} ∫ (S (k+1) − S k)²`.
  have hsqeq : ∀ n, ∫ ω, (S n ω) ^ 2 ∂μ
      = ∑ k ∈ range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ := by
    intro n
    rw [integral_sq_eq_integral_predQuadVar hSmart.stronglyAdapted hSmem hS0 n]
    have e : ∑ k ∈ range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        = ∑ k ∈ range n,
            ((∫ ω, predQuadVar S ℱ μ (k + 1) ω ∂μ) - ∫ ω, predQuadVar S ℱ μ k ω ∂μ) :=
      Finset.sum_congr rfl fun k _ ↦
        (integral_predQuadVar_succ_sub hSmart hSmem k).symm
    rw [e, Finset.sum_range_sub (fun k ↦ ∫ ω, predQuadVar S ℱ μ k ω ∂μ) n]
    simp [predQuadVar_zero]
  -- The summability `∑ (k+1)⁻² < ∞`.
  have hsummable : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  -- Per-increment bound `∫ (S (k+1) − S k)² ≤ c² / (k+1)²`.
  have hbound : ∀ k, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ ≤ c ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hinc : ∀ ω, S (k + 1) ω - S k ω = (M (k + 1) ω - M k ω) / ((k : ℝ) + 1) := by
      intro ω; simp only [hSdef, Finset.sum_range_succ]; ring
    have hsqle : ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ ≤ c ^ 2 := by
      have hle : (fun ω ↦ (M (k + 1) ω - M k ω) ^ 2) ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
        filter_upwards [hb k] with ω h
        obtain ⟨h1, h2⟩ := abs_le.mp h
        nlinarith [h1, h2]
      calc ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ
          ≤ ∫ _, c ^ 2 ∂μ := integral_mono_ae (hdmem k).integrable_sq (integrable_const _) hle
        _ = c ^ 2 := by simp
    have hpt : ∀ ω, (S (k + 1) ω - S k ω) ^ 2
        = (M (k + 1) ω - M k ω) ^ 2 / ((k : ℝ) + 1) ^ 2 := fun ω ↦ by
      rw [hinc ω, div_pow]
    calc ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        = ∫ ω, (M (k + 1) ω - M k ω) ^ 2 / ((k : ℝ) + 1) ^ 2 ∂μ :=
          integral_congr_ae (.of_forall hpt)
      _ = (∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ) / ((k : ℝ) + 1) ^ 2 := integral_div _ _
      _ ≤ c ^ 2 / ((k : ℝ) + 1) ^ 2 := by gcongr
  -- Assemble the uniform second-moment bound on `S`.
  have hbdd : ∀ n, ∫ ω, (S n ω) ^ 2 ∂μ ≤ c ^ 2 * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
    intro n
    rw [hsqeq n]
    calc ∑ k ∈ range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        ≤ ∑ k ∈ range n, c ^ 2 / ((k : ℝ) + 1) ^ 2 := Finset.sum_le_sum fun k _ ↦ hbound k
      _ = c ^ 2 * ∑ k ∈ range n, 1 / ((k : ℝ) + 1) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_one_div]
      _ ≤ c ^ 2 * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
          gcongr
          exact hsummable.sum_le_tsum (Finset.range n) fun i _ ↦ by positivity
  exact martingale_div_atTop_ae_tendsto_zero hM hSmem hbdd

/-! ### Bracket-normalized strong law -/

/-- The **bracket-weighted increment series** `T n = ∑_{k<n} (M(k+1) − M k)/(1 + ⟨M⟩_{k+1})` of a
square-integrable martingale `M`. The weights `1/(1+⟨M⟩_{k+1})` are `ℱ_k`-measurable (`⟨M⟩` is
predictable) and lie in `(0,1]`, so `T` is a martingale (below) and `L²`-bounded, and its a.s. limit
delivers `M_n/⟨M⟩_n → 0` (blueprint `lem:slln_bracket_weighted`, `thm:mart_slln_bracket`). -/
noncomputable def bracketSeries (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) :
    ℕ → Ω → ℝ :=
  fun n ω ↦ ∑ k ∈ range n, (M (k + 1) ω - M k ω) / (1 + predQuadVar M ℱ μ (k + 1) ω)

/-- **The bracket-weighted increment series is a martingale** (part of blueprint
`lem:slln_bracket_weighted`). Each increment `ΔT_n = ΔM_n/(1+⟨M⟩_{n+1})` is a predictably-weighted
martingale difference: the weight `1/(1+⟨M⟩_{n+1})` is `ℱ_n`-measurable, so
`𝔼[ΔT_n ∣ ℱ_n] = (1+⟨M⟩_{n+1})⁻¹ 𝔼[ΔM_n ∣ ℱ_n] = 0`. -/
@[specifies bracketSeries "the first of the two things the weight `1/(1+⟨M⟩_{k+1})` is chosen for: \
indexing the bracket at `k+1` keeps the weight predictable, so the weighted sum is still a \
martingale — an off-by-one to `⟨M⟩_k` would break this"]
lemma martingale_bracketSeries [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) :
    Martingale (bracketSeries M ℱ μ) ℱ μ := by
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  have hint : ∀ n, Integrable (M n) μ := hM.integrable
  have hd2 : ∀ n, MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ := fun n ↦
    memLp_increment (hM2 n) (hM2 (n + 1))
  have hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ := fun n ↦
    integrable_mul_increment (hM2 n) (hM2 (n + 1))
  -- The weight `1 + ⟨M⟩_{k+1}` is `ℱ_k`-measurable (predictability of `⟨M⟩`).
  have hqvmeas : ∀ k, StronglyMeasurable[ℱ k] (predQuadVar M ℱ μ (k + 1)) :=
    fun k ↦ stronglyAdapted_predictablePart (f := fun n ↦ M n ^ 2) k
  have hwmeas : ∀ k, StronglyMeasurable[ℱ k] (fun ω ↦ 1 + predQuadVar M ℱ μ (k + 1) ω) :=
    fun k ↦ stronglyMeasurable_const.add (hqvmeas k)
  have hadapt : ∀ n, StronglyMeasurable[ℱ n] (bracketSeries M ℱ μ n) := fun n ↦
    Finset.stronglyMeasurable_fun_sum _ fun k hk ↦ by
      rw [Finset.mem_range] at hk
      exact (((hM.stronglyMeasurable (k + 1)).mono (ℱ.mono (by omega))).sub
        ((hM.stronglyMeasurable k).mono (ℱ.mono (by omega)))).div
        ((hwmeas k).mono (ℱ.mono (by omega)))
  -- Each increment `ΔM_k/(1+⟨M⟩_{k+1})` is integrable (weight in `(0,1]`, so `|·| ≤ |ΔM_k|`).
  have hterm_int : ∀ k,
      Integrable (fun ω ↦ (M (k + 1) ω - M k ω) / (1 + predQuadVar M ℱ μ (k + 1) ω)) μ := by
    intro k
    have haesm : AEStronglyMeasurable
        (fun ω ↦ (M (k + 1) ω - M k ω) / (1 + predQuadVar M ℱ μ (k + 1) ω)) μ :=
      ((((hM.stronglyMeasurable (k + 1)).mono (ℱ.le _)).sub
        ((hM.stronglyMeasurable k).mono (ℱ.le _))).div
        ((hwmeas k).mono (ℱ.le _))).aestronglyMeasurable
    refine Integrable.mono' (g := fun ω ↦ |M (k + 1) ω - M k ω|)
      ((hint (k + 1)).sub (hint k)).abs haesm ?_
    filter_upwards [predQuadVar_nonneg hM hd2 hprod (k + 1)] with ω hqv
    simp only [Pi.zero_apply] at hqv
    have hpos : (0 : ℝ) < 1 + predQuadVar M ℱ μ (k + 1) ω := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    nlinarith [abs_nonneg (M (k + 1) ω - M k ω), hqv]
  have hTint : ∀ n, Integrable (bracketSeries M ℱ μ n) μ := fun n ↦
    integrable_finsetSum _ fun k _ ↦ hterm_int k
  refine martingale_nat hadapt hTint fun n ↦ ?_
  -- `T (n+1) = T n + ΔM_n/(1+⟨M⟩_{n+1})`, whose conditional expectation is `0`.
  have hTsucc : bracketSeries M ℱ μ (n + 1)
      = bracketSeries M ℱ μ n
        + (fun ω ↦ (M (n + 1) ω - M n ω) / (1 + predQuadVar M ℱ μ (n + 1) ω)) := by
    funext ω; simp only [bracketSeries, Finset.sum_range_succ, Pi.add_apply]
  have hzero : μ[(fun ω ↦ (M (n + 1) ω - M n ω) / (1 + predQuadVar M ℱ μ (n + 1) ω)) | ℱ n]
      =ᵐ[μ] 0 := by
    have heq : (fun ω ↦ (M (n + 1) ω - M n ω) / (1 + predQuadVar M ℱ μ (n + 1) ω))
        = (fun ω ↦ (1 + predQuadVar M ℱ μ (n + 1) ω)⁻¹) * (M (n + 1) - M n) := by
      funext ω; simp only [Pi.mul_apply, Pi.sub_apply]; rw [div_eq_inv_mul]
    rw [heq]
    have hwsm : StronglyMeasurable[ℱ n] (fun ω ↦ (1 + predQuadVar M ℱ μ (n + 1) ω)⁻¹) :=
      (hwmeas n).measurable.inv.stronglyMeasurable
    have hprodint : Integrable ((fun ω ↦ (1 + predQuadVar M ℱ μ (n + 1) ω)⁻¹) * (M (n + 1) - M n)) μ
        := by rw [← heq]; exact hterm_int n
    have hpull := condExp_mul_of_stronglyMeasurable_left hwsm hprodint ((hint (n + 1)).sub (hint n))
    have hd0 : μ[(M (n + 1) - M n) | ℱ n] =ᵐ[μ] 0 := by
      refine (condExp_sub (hint (n + 1)) (hint n) _).trans ?_
      filter_upwards [hM.condExp_ae_eq (Nat.le_succ n), hM.condExp_ae_eq (le_refl n)] with ω h1 h2
      simp only [Pi.sub_apply, Pi.zero_apply, h1, h2, sub_self]
    refine hpull.trans ?_
    filter_upwards [hd0] with ω hω
    simp only [Pi.mul_apply, Pi.zero_apply, hω, mul_zero]
  have hself := condExp_of_stronglyMeasurable (ℱ.le n) (hadapt n) (hTint n)
  rw [hTsucc]
  filter_upwards [condExp_add (hTint n) (hterm_int n) (ℱ n), hzero] with ω ha h2
  rw [ha, Pi.add_apply, congrFun hself ω, h2, Pi.zero_apply, add_zero]

/-- Increment of the bracket series: `T (k+1) − T k = (M (k+1) − M k)/(1 + ⟨M⟩_{k+1})`. -/
lemma bracketSeries_succ_sub (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    (k : ℕ) (ω : Ω) :
    bracketSeries M ℱ μ (k + 1) ω - bracketSeries M ℱ μ k ω
      = (M (k + 1) ω - M k ω) / (1 + predQuadVar M ℱ μ (k + 1) ω) := by
  simp only [bracketSeries, Finset.sum_range_succ]; ring

/-- Each bracket-series increment `(M(k+1) − M k)/(1+⟨M⟩_{k+1})` is in `L²`, being dominated by
`|M(k+1) − M k| ∈ L²` (the weight is in `(0,1]`). -/
lemma memLp_bracketSeries_term (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (k : ℕ) :
    MemLp (fun ω ↦ (M (k + 1) ω - M k ω) / (1 + predQuadVar M ℱ μ (k + 1) ω)) 2 μ := by
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  have hd2 : ∀ n, MemLp (fun ω ↦ M (n + 1) ω - M n ω) 2 μ := fun n ↦
    memLp_increment (hM2 n) (hM2 (n + 1))
  have hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ := fun n ↦
    integrable_mul_increment (hM2 n) (hM2 (n + 1))
  have haesm : AEStronglyMeasurable
      (fun ω ↦ (M (k + 1) ω - M k ω) / (1 + predQuadVar M ℱ μ (k + 1) ω)) μ :=
    ((((hM.stronglyMeasurable (k + 1)).mono (ℱ.le _)).sub
      ((hM.stronglyMeasurable k).mono (ℱ.le _))).div (stronglyMeasurable_const.add
        ((stronglyAdapted_predictablePart (f := fun n ↦ M n ^ 2) k).mono
          (ℱ.le _)))).aestronglyMeasurable
  refine MemLp.mono' (((hM2 (k + 1)).sub (hM2 k)).norm) haesm ?_
  filter_upwards [predQuadVar_nonneg hM hd2 hprod (k + 1)] with ω hqv
  simp only [Pi.zero_apply] at hqv
  have hpos : (0 : ℝ) < 1 + predQuadVar M ℱ μ (k + 1) ω := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, Real.norm_eq_abs, Pi.sub_apply, div_le_iff₀ hpos]
  nlinarith [abs_nonneg (M (k + 1) ω - M k ω), hqv]

/-- The bracket series `T n` is in `L²`, being a finite sum of `L²` increments. -/
lemma memLp_bracketSeries (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) : MemLp (bracketSeries M ℱ μ n) 2 μ :=
  memLp_finsetSum _ fun k _ ↦ memLp_bracketSeries_term hM hM2 k

/-- **The bracket series has quadratic variation `≤ 1`** (the `L²`-bound of blueprint
`lem:slln_bracket_weighted`). Each increment of `⟨T⟩` is `𝔼[(ΔT_k)² ∣ ℱ_k] = w_k²·Δ⟨M⟩_k`
(with `w_k = 1/(1+⟨M⟩_{k+1})`), bounded by the telescoping quantity
`1/(1+⟨M⟩_k) − 1/(1+⟨M⟩_{k+1})`; summing gives `⟨T⟩_n ≤ 1/(1+⟨M⟩_0) − 1/(1+⟨M⟩_n) ≤ 1`. -/
@[specifies bracketSeries "the second thing the weight is chosen for, and the one that makes the \
construction worth having: the weighting is strong enough to bound `⟨T⟩` by an absolute constant, \
uniformly in `n` and in the martingale"]
lemma predQuadVar_bracketSeries_le_one [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    predQuadVar (bracketSeries M ℱ μ) ℱ μ n ≤ᵐ[μ] 1 := by
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  have hTmart : Martingale (bracketSeries M ℱ μ) ℱ μ := martingale_bracketSeries hM hM2
  have hd2 : ∀ k, MemLp (fun ω ↦ M (k + 1) ω - M k ω) 2 μ := fun k ↦
    memLp_increment (hM2 k) (hM2 (k + 1))
  have hprod : ∀ k, Integrable (M k * (M (k + 1) - M k)) μ := fun k ↦
    integrable_mul_increment (hM2 k) (hM2 (k + 1))
  have hTmem : ∀ k, MemLp (bracketSeries M ℱ μ k) 2 μ := memLp_bracketSeries hM hM2
  have hd2T : ∀ k, MemLp (fun ω ↦ bracketSeries M ℱ μ (k + 1) ω
      - bracketSeries M ℱ μ k ω) 2 μ := fun k ↦ memLp_increment (hTmem k) (hTmem (k + 1))
  have hd2T' : ∀ k, Integrable (fun ω ↦ (bracketSeries M ℱ μ (k + 1) ω
      - bracketSeries M ℱ μ k ω) ^ 2) μ := fun k ↦ (hd2T k).integrable_sq
  have hprodT : ∀ k, Integrable (bracketSeries M ℱ μ k
      * (bracketSeries M ℱ μ (k + 1) - bracketSeries M ℱ μ k)) μ := fun k ↦
    integrable_mul_increment (hTmem k) (hTmem (k + 1))
  have hw2meas : ∀ k, StronglyMeasurable[ℱ k] (fun ω ↦ ((1 + predQuadVar M ℱ μ (k + 1) ω)⁻¹) ^ 2) :=
    fun k ↦ (((stronglyMeasurable_const.add
      (stronglyAdapted_predictablePart (f := fun n ↦ M n ^ 2) k)).measurable.inv).pow_const
        2).stronglyMeasurable
  -- Per-increment bound `⟨T⟩_{k+1} − ⟨T⟩_k ≤ 1/(1+⟨M⟩_k) − 1/(1+⟨M⟩_{k+1})`.
  have hincr : ∀ k, predQuadVar (bracketSeries M ℱ μ) ℱ μ (k + 1)
        - predQuadVar (bracketSeries M ℱ μ) ℱ μ k
      ≤ᵐ[μ] fun ω ↦ (1 + predQuadVar M ℱ μ k ω)⁻¹ - (1 + predQuadVar M ℱ μ (k + 1) ω)⁻¹ := by
    intro k
    have heq : (fun ω ↦ (bracketSeries M ℱ μ (k + 1) ω - bracketSeries M ℱ μ k ω) ^ 2)
        = (fun ω ↦ ((1 + predQuadVar M ℱ μ (k + 1) ω)⁻¹) ^ 2)
          * (fun ω ↦ (M (k + 1) ω - M k ω) ^ 2) := by
      funext ω; simp only [Pi.mul_apply]; rw [bracketSeries_succ_sub]; ring
    have h1 := predQuadVar_succ_sub_eq hTmart k (hd2T k) (hprodT k)
    rw [heq] at h1
    have h2 := condExp_mul_of_stronglyMeasurable_left (hw2meas k) (heq ▸ hd2T' k)
      (hd2 k).integrable_sq
    have h3 := (predQuadVar_succ_sub_eq hM k (hd2 k) (hprod k)).symm
    filter_upwards [h1, h2, h3, predQuadVar_nonneg hM hd2 hprod k,
      predQuadVar_le_succ hM k (hd2 k) (hprod k)] with ω e1 e2 e3 hnn hle
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply] at e1 e2 e3 hnn hle ⊢
    rw [e1, e2, e3]
    set a := predQuadVar M ℱ μ k ω
    set b := predQuadVar M ℱ μ (k + 1) ω
    have hpa : (0 : ℝ) < 1 + a := by linarith
    have hpb : (0 : ℝ) < 1 + b := by linarith
    have key : (1 + a)⁻¹ - (1 + b)⁻¹ - ((1 + b)⁻¹) ^ 2 * (b - a)
        = (b - a) ^ 2 / ((1 + a) * (1 + b) ^ 2) := by
      field_simp
      ring
    have hnn2 : 0 ≤ (b - a) ^ 2 / ((1 + a) * (1 + b) ^ 2) :=
      div_nonneg (sq_nonneg _) (mul_nonneg hpa.le (sq_nonneg _))
    linarith [key, hnn2]
  -- Telescope: `⟨T⟩_n = ∑ (⟨T⟩_{k+1} − ⟨T⟩_k) ≤ 1/(1+⟨M⟩_0) − 1/(1+⟨M⟩_n) ≤ 1`.
  filter_upwards [ae_all_iff.mpr hincr, predQuadVar_nonneg hM hd2 hprod n] with ω hω hMn
  simp only [Pi.one_apply, Pi.zero_apply] at hMn ⊢
  have htel : predQuadVar (bracketSeries M ℱ μ) ℱ μ n ω
      = ∑ k ∈ range n, (predQuadVar (bracketSeries M ℱ μ) ℱ μ (k + 1) ω
          - predQuadVar (bracketSeries M ℱ μ) ℱ μ k ω) := by
    rw [Finset.sum_range_sub (fun k ↦ predQuadVar (bracketSeries M ℱ μ) ℱ μ k ω),
      show predQuadVar (bracketSeries M ℱ μ) ℱ μ 0 ω = 0 from by rw [predQuadVar_zero]; rfl,
      sub_zero]
  rw [htel]
  have hz0 : predQuadVar M ℱ μ 0 ω = 0 := by rw [predQuadVar_zero]; rfl
  calc ∑ k ∈ range n, (predQuadVar (bracketSeries M ℱ μ) ℱ μ (k + 1) ω
          - predQuadVar (bracketSeries M ℱ μ) ℱ μ k ω)
      ≤ ∑ k ∈ range n, ((1 + predQuadVar M ℱ μ k ω)⁻¹ - (1 + predQuadVar M ℱ μ (k + 1) ω)⁻¹) :=
        Finset.sum_le_sum fun k _ ↦ by simpa only [Pi.sub_apply] using hω k
    _ = (1 + predQuadVar M ℱ μ 0 ω)⁻¹ - (1 + predQuadVar M ℱ μ n ω)⁻¹ :=
        Finset.sum_range_sub' (fun k ↦ (1 + predQuadVar M ℱ μ k ω)⁻¹) n
    _ ≤ 1 := by
        rw [hz0]
        have : (0 : ℝ) ≤ (1 + predQuadVar M ℱ μ n ω)⁻¹ := inv_nonneg.mpr (by linarith)
        simp only [add_zero, inv_one]
        linarith

/-- **Bracket-normalized martingale SLLN** (blueprint `thm:mart_slln_bracket`). For a
square-integrable martingale `M`, almost surely on the event `{⟨M⟩_n → ∞}` one has
`M_n / ⟨M⟩_n → 0`.

The bracket transform `T` is `L²`-bounded (`∫ (T n)² = ∫ ⟨T⟩_n ≤ 1`), so it converges a.s.; the
general Kronecker lemma applied pathwise with weights `b_k = 1 + ⟨M⟩_k` turns this into
`M_n/(1+⟨M⟩_n) → 0`, and since `(1+⟨M⟩_n)/⟨M⟩_n → 1` on the event, `M_n/⟨M⟩_n → 0`. -/
theorem martingale_div_predQuadVar_ae_tendsto_zero [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM2 : ∀ n, MemLp (M n) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop →
      Tendsto (fun n ↦ M n ω / predQuadVar M ℱ μ n ω) atTop (𝓝 0) := by
  have hd2 : ∀ k, MemLp (fun ω ↦ M (k + 1) ω - M k ω) 2 μ := fun k ↦
    memLp_increment (hM2 k) (hM2 (k + 1))
  have hprod : ∀ k, Integrable (M k * (M (k + 1) - M k)) μ := fun k ↦
    integrable_mul_increment (hM2 k) (hM2 (k + 1))
  have hTmart : Martingale (bracketSeries M ℱ μ) ℱ μ := martingale_bracketSeries hM hM2
  have hT0 : bracketSeries M ℱ μ 0 =ᵐ[μ] 0 :=
    Eventually.of_forall fun ω ↦ by simp [bracketSeries]
  have hT2 : ∀ n, MemLp (bracketSeries M ℱ μ n) 2 μ := memLp_bracketSeries hM hM2
  have hbdd : ∀ n, ∫ ω, (bracketSeries M ℱ μ n ω) ^ 2 ∂μ ≤ 1 := by
    intro n
    rw [integral_sq_eq_integral_predQuadVar hTmart.stronglyAdapted hT2 hT0 n]
    calc ∫ ω, predQuadVar (bracketSeries M ℱ μ) ℱ μ n ω ∂μ
        ≤ ∫ _, (1 : ℝ) ∂μ := integral_mono_ae
          (integrable_predQuadVar hTmart.stronglyAdapted hT2 n) (integrable_const 1)
          (predQuadVar_bracketSeries_le_one hM hM2 n)
      _ = 1 := by simp
  have hconv := martingale_ae_tendsto_of_integral_sq_le hTmart hT2 hbdd
  filter_upwards [hconv, predQuadVar_mono hM hd2 hprod,
    ae_all_iff.mpr fun n ↦ predQuadVar_nonneg hM hd2 hprod n] with ω hcω hmono hnn
  intro hinf
  obtain ⟨c, hc⟩ := hcω
  simp only [Pi.zero_apply] at hnn
  -- Kronecker with weights `b_k = 1 + ⟨M⟩_k ω`.
  have hb_pos : ∀ n, 0 < 1 + predQuadVar M ℱ μ n ω := fun n ↦ by have := hnn n; linarith
  have hb_mono : Monotone fun n ↦ 1 + predQuadVar M ℱ μ n ω := hmono.const_add 1
  have hb_top : Tendsto (fun n ↦ 1 + predQuadVar M ℱ μ n ω) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hinf
  have hy : Tendsto (fun n ↦ ∑ k ∈ range n,
      (bracketSeries M ℱ μ (k + 1) ω - bracketSeries M ℱ μ k ω)) atTop (𝓝 c) := by
    refine hc.congr' (Eventually.of_forall fun n ↦ ?_)
    change bracketSeries M ℱ μ n ω
      = ∑ k ∈ range n, (bracketSeries M ℱ μ (k + 1) ω - bracketSeries M ℱ μ k ω)
    rw [Finset.sum_range_sub (fun k ↦ bracketSeries M ℱ μ k ω),
      show bracketSeries M ℱ μ 0 ω = 0 by simp [bracketSeries], sub_zero]
  have hkron := kronecker_general hb_pos hb_mono hb_top hy
  -- `(1/(1+⟨M⟩_n)) ∑ (1+⟨M⟩_{k+1})·ΔT_k = (M_n - M_0)/(1+⟨M⟩_n)`.
  have hstep0 : Tendsto (fun n ↦ (M n ω - M 0 ω) / (1 + predQuadVar M ℱ μ n ω)) atTop (𝓝 0) := by
    refine hkron.congr' (Eventually.of_forall fun n ↦ ?_)
    change (1 + predQuadVar M ℱ μ n ω)⁻¹ * ∑ k ∈ range n, (1 + predQuadVar M ℱ μ (k + 1) ω)
        * (bracketSeries M ℱ μ (k + 1) ω - bracketSeries M ℱ μ k ω)
      = (M n ω - M 0 ω) / (1 + predQuadVar M ℱ μ n ω)
    rw [div_eq_inv_mul]
    congr 1
    have hterm : ∀ k, (1 + predQuadVar M ℱ μ (k + 1) ω)
        * (bracketSeries M ℱ μ (k + 1) ω - bracketSeries M ℱ μ k ω) = M (k + 1) ω - M k ω := by
      intro k
      have hne : (1 + predQuadVar M ℱ μ (k + 1) ω) ≠ 0 := (hb_pos (k + 1)).ne'
      rw [bracketSeries_succ_sub]; field_simp
    rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_range_sub (M · ω)]
  -- the initial value is washed out: `M_0/(1+⟨M⟩_n) → 0` since the denominator diverges.
  have hstep : Tendsto (fun n ↦ M n ω / (1 + predQuadVar M ℱ μ n ω)) atTop (𝓝 0) := by
    have hM0 : Tendsto (fun n ↦ M 0 ω / (1 + predQuadVar M ℱ μ n ω)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hb_top
    have hsum := hstep0.add hM0
    rw [add_zero] at hsum
    exact hsum.congr fun n ↦ by ring
  -- `(1+⟨M⟩_n)/⟨M⟩_n → 1`, so `M_n/⟨M⟩_n = (M_n/(1+⟨M⟩_n))·((1+⟨M⟩_n)/⟨M⟩_n) → 0`.
  have hinv : Tendsto (fun n ↦ (predQuadVar M ℱ μ n ω)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hinf
  have hratio : Tendsto (fun n ↦ (1 + predQuadVar M ℱ μ n ω) / predQuadVar M ℱ μ n ω)
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun n ↦ (predQuadVar M ℱ μ n ω)⁻¹ + 1) atTop (𝓝 (0 + 1)) :=
      hinv.add tendsto_const_nhds
    rw [zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [hinf.eventually_gt_atTop 0] with n hn
    rw [add_div, div_self hn.ne', one_div]
  have hmul := hstep.mul hratio
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [hinf.eventually_gt_atTop 0] with n hn
  show M n ω / (1 + predQuadVar M ℱ μ n ω)
      * ((1 + predQuadVar M ℱ μ n ω) / predQuadVar M ℱ μ n ω)
    = M n ω / predQuadVar M ℱ μ n ω
  have h2 : predQuadVar M ℱ μ n ω ≠ 0 := hn.ne'
  have h1 : (1 + predQuadVar M ℱ μ n ω) ≠ 0 := (hb_pos n).ne'
  field_simp

end AlphaRAR
