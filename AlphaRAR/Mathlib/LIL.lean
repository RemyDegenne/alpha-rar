/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.Freedman
public meta import Characterization

/-!
# Martingale laws of the iterated logarithm

The exponential supermartingale `exp(θ M − ½(1+δ)θ²⟨M⟩)`, Freedman's inequality and the block
Borel–Cantelli steps live in `Freedman.lean`, parameterized by the variance proxy `1 + δ` and the
window `η` of the one-step estimate `eˣ ≤ 1 + x + ½(1+δ)x²`. This file lets `δ ↓ 0` (with the
window `η = min 1 (9δ/4)` of `exp_le_one_add_add_half_mul_sq`) and blocks geometrically with base
`ρ ↓ 1`, to obtain the sharp constant `limsup Mₙ/√(2⟨M⟩ₙ log log⟨M⟩ₙ) ≤ 1` in two settings: bounded
increments, normalized by the quadratic variation; and growing increments, normalized by a linear
bound `⟨M⟩_n ≤ v n` on the quadratic variation, with deterministic time horizons in place of a
random stopping time.

## Main results

* `AlphaRAR.ae_eventually_forall_lt_pow_loglog`: the exceedance bound for bounded increments,
  `⟨M⟩_n ≤ ρ^k ⇒ M_n < √(2(1+ε)ρ^k log(k+2))` eventually.
* `AlphaRAR.ae_eventually_le_sqrt_predQuadVar_mul_loglog_of_lt`,
  `AlphaRAR.ae_forall_one_lt_eventually_le_sqrt_predQuadVar_mul_loglog`: the normalized bound
  `M_n ≤ b √(2⟨M⟩_n log log⟨M⟩_n)` eventually, for a fixed block base and then for every `b > 1`;
  the least-block repackaging keeps the `log log` cost additive, which is what preserves the
  constant.
* `AlphaRAR.ae_forall_one_lt_eventually_abs_le_sqrt_predQuadVar_mul_loglog`,
  `AlphaRAR.ae_limsup_abs_div_sqrt_predQuadVar_mul_loglog_le_one`,
  `AlphaRAR.ae_isBigO_sqrt_predQuadVar_mul_loglog`: the two-sided sharp bound, its `limsup` form
  `limsup |M_n|/√(2⟨M⟩_n log log⟨M⟩_n) ≤ 1` a.s., and its `IsBigO` corollary.
* `AlphaRAR.ae_eventually_lt_block_of_growing_loglog`: the block Borel–Cantelli step for
  growing-increment martingales over an arbitrary horizon sequence `N_j`, with exponent
  `(½(1+δ)α²v − αC) log(j+2)`.
* `AlphaRAR.ae_eventually_le_sqrt_nat_mul_loglog_of_growing_of_lt`,
  `AlphaRAR.ae_eventually_le_sqrt_nat_mul_loglog_of_growing`: `M_n ≤ b √(2vn log log n)`
  eventually for a growing-increment martingale with `⟨M⟩_n ≤ v n`, from horizons `N_j = ⌈ρ^j⌉`
  with `ρ ↓ 1` (`exists_ceil_pow_horizon`) and the block condition `c_j √(log(j+2)/N_j) → 0`.
* `AlphaRAR.tendsto_growth_horizon`: the block condition from a base-independent increment growth
  `g` with `g n √(log log n / n) → 0`.
* `AlphaRAR.ae_forall_one_lt_eventually_le_sqrt_nat_mul_loglog_of_growth`,
  `AlphaRAR.ae_forall_one_lt_eventually_abs_le_sqrt_nat_mul_loglog_of_growth`,
  `AlphaRAR.ae_limsup_abs_div_sqrt_nat_mul_loglog_of_growth_le_one`: the sharp growing-increment
  LIL for every `b > 1`, one- and two-sided, and as `limsup |M_n|/√(2vn log log n) ≤ 1` a.s.
* `AlphaRAR.ae_isBigO_sqrt_nat_mul_loglog_of_bdd`: the **unconditional** bounded-increment LIL
  `M_n = O(√(n log log n))` a.s., with no hypothesis on `⟨M⟩`, from the growing-increment engine
  with constant growth.
-/

@[expose] public section

open MeasureTheory Filter Real

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {M : ℕ → Ω → ℝ}

/-- **Sharp exceedance for bounded increments.** With blocks `v_k = ρ^k` and sharp thresholds
`λ_k = √(2(1+ε)ρ^k log(k+2))` (using `log(k+2) ≍ loglog ρ^k`), almost surely for all large `k`
and every `n`, `⟨M⟩_n ≤ ρ^k ⇒ M_n < √(2(1+ε)ρ^k log(k+2))`. The refined Freedman tail is
`exp(-((1+ε)/(1+δ)) log(k+2))`, a `p`-series with `p = (1+ε)/(1+δ) > 1`
(`summable_exp_neg_mul_log_add`); admissibility `λ_k c ≤ (1+δ)ρ^k η_δ` holds eventually since
`log(k+2)/ρ^k → 0`. -/
lemma ae_eventually_forall_lt_pow_loglog [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {ρ ε δ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ)
    (hεδ : δ < ε) :
    ∀ᵐ ω ∂μ, ∀ᶠ (k : ℕ) in atTop, ∀ n, predQuadVar M ℱ μ n ω ≤ ρ ^ k →
      M n ω < √(2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2)) := by
  obtain ⟨η, hη0, hη⟩ : ∃ η > 0, ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2 :=
    ⟨min 1 (9 / 4 * δ), lt_min one_pos (by positivity), fun _ hx ↦
      exp_le_one_add_add_half_mul_sq hx⟩
  have hε0 : (0 : ℝ) < 1 + ε := by linarith
  have hδ0 : (0 : ℝ) < 1 + δ := by linarith
  have hlogpos : ∀ k : ℕ, (0 : ℝ) < log ((k : ℝ) + 2) := fun k ↦
    log_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hvpos : ∀ k : ℕ, (0 : ℝ) < ρ ^ k := fun k ↦ pow_pos (by linarith) k
  have hXpos : ∀ k : ℕ, (0 : ℝ) < 2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2) := fun k ↦ by
    have := hvpos k; have := hlogpos k; positivity
  set lam : ℕ → ℝ := fun k ↦ √(2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2)) with hlam_def
  have hlam_pos : ∀ k, 0 < lam k := fun k ↦ Real.sqrt_pos.mpr (hXpos k)
  -- Summability of the refined Freedman tail (a `p`-series with `p = (1+ε)/(1+δ) > 1`).
  have hp1 : (1 : ℝ) < (1 + ε) / (1 + δ) := by rw [lt_div_iff₀ hδ0]; linarith
  have hsum : Summable fun k ↦ exp (-lam k ^ 2 / (2 * (1 + δ) * ρ ^ k)) := by
    refine (summable_exp_neg_mul_log_add hp1).congr fun k ↦ ?_
    congr 1
    rw [hlam_def, Real.sq_sqrt (hXpos k).le]
    have hρk : ρ ^ k ≠ 0 := (hvpos k).ne'
    field_simp
  -- Eventual admissibility `λ_k c ≤ (1+δ) ρ^k η`.
  have hadm : ∀ᶠ k in atTop, 0 < lam k ∧ 0 < ρ ^ k ∧ lam k * c ≤ (1 + δ) * ρ ^ k * η := by
    have hη2pos : (0 : ℝ) < (1 + δ) ^ 2 * η ^ 2 := by positivity
    have htend : Tendsto (fun k : ℕ ↦ 2 * (1 + ε) * c ^ 2 * (log ((k : ℝ) + 2) / ρ ^ k)) atTop
        (𝓝 0) := by
      have h := (tendsto_log_add_two_div_pow hρ).const_mul (2 * (1 + ε) * c ^ 2)
      rwa [mul_zero] at h
    filter_upwards [htend.eventually (gt_mem_nhds hη2pos)] with k hk
    refine ⟨hlam_pos k, hvpos k, ?_⟩
    -- `hk : 2(1+ε)c² · (log(k+2)/ρ^k) < (1+δ)²η²`, so `2(1+ε)c² log(k+2) < (1+δ)²η² ρ^k`.
    rw [← mul_div_assoc, div_lt_iff₀ (hvpos k)] at hk
    have hsq : 2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2) * c ^ 2 ≤ ((1 + δ) * ρ ^ k * η) ^ 2 := by
      nlinarith [mul_lt_mul_of_pos_right hk (hvpos k), hvpos k]
    rw [hlam_def, show √(2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2)) * c
        = √(2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2) * c ^ 2) from by
      rw [Real.sqrt_mul (hXpos k).le, Real.sqrt_sq hc.le]]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
  filter_upwards [ae_eventually_forall_lt_of_summable hM hM0 hδ.le hη hb
    (v := fun k ↦ ρ ^ k) hadm hsum] with ω hω using hω

/-- **Sharp normalized bound for fixed block base.** For bounded increments with `⟨M⟩_n → ∞`, if
`b² > (1+ε)ρ` then almost surely eventually
`M_n ≤ b √(2 ⟨M⟩_n log log⟨M⟩_n)`. Repackaging the sharp block via the least `k` with `⟨M⟩_n ≤ ρ^k`:
`ρ^k ≤ ρ⟨M⟩_n` and, crucially, the loglog bound is kept **additive**,
`log(k+2) ≤ D_ρ + log log⟨M⟩_n` (with `D_ρ = log(1/log ρ + 1)`), so no constant `> 1` multiplies the
leading term; the additive `D_ρ` is absorbed since `log log⟨M⟩_n → ∞`. Taking `ρ ↓ 1`, `ε ↓ 0`,
`b ↓ 1` gives the sharp constant `limsup ≤ 1`. -/
lemma ae_eventually_le_sqrt_predQuadVar_mul_loglog_of_lt [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {c : ℝ} (hc : 0 < c) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop)
    {ρ ε δ b : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ) (hεδ : δ < ε) (hb0 : 0 < b)
    (hbA : (1 + ε) * ρ < b ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, M n ω ≤ b * √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω))) := by
  have hε0 : (0 : ℝ) < 1 + ε := by linarith
  have hApos : (0 : ℝ) < (1 + ε) * ρ := by positivity
  have hbApos : (0 : ℝ) < b ^ 2 - (1 + ε) * ρ := by linarith
  set Dρ : ℝ := log (1 / log ρ + 1) with hDρ_def
  set T : ℝ := (1 + ε) * ρ * Dρ / (b ^ 2 - (1 + ε) * ρ) with hT_def
  filter_upwards [ae_eventually_forall_lt_pow_loglog hM hM0 hc hb hρ hδ hεδ, hV]
    with ω hgood hVω
  rw [eventually_atTop] at hgood
  obtain ⟨k₀, hk₀⟩ := hgood
  filter_upwards [hVω.eventually_ge_atTop (ρ ^ k₀),
    hVω.eventually_ge_atTop (exp (exp (max 3 T)))] with n hn0 hnT
  set V := predQuadVar M ℱ μ n ω with hV_def
  have hVpos : 0 < V := lt_of_lt_of_le (exp_pos _) hnT
  have hV1 : (1 : ℝ) ≤ V := le_trans (one_le_exp (exp_pos _).le) hnT
  have hlogV : exp (max 3 T) ≤ log V := by
    rw [← Real.log_exp (exp (max 3 T))]; exact log_le_log (exp_pos _) hnT
  have hlogVpos : 0 < log V := lt_of_lt_of_le (exp_pos _) hlogV
  have hloglogV : max 3 T ≤ log (log V) := by
    rw [← Real.log_exp (max 3 T)]; exact log_le_log (exp_pos _) hlogV
  have hloglogV3 : (3 : ℝ) ≤ log (log V) := le_trans (le_max_left _ _) hloglogV
  have hloglogVT : T ≤ log (log V) := le_trans (le_max_right _ _) hloglogV
  have hloglogVpos : 0 < log (log V) := by linarith
  have hlogV3 : (3 : ℝ) ≤ log V := by
    linarith [log_le_sub_one_of_pos hlogVpos, hloglogV3]
  -- Least block `k` with `V ≤ ρ^k` (`exists_pow_ge_le`).
  obtain ⟨k, hVle, hρk, hk⟩ := exists_pow_ge_le hρ hV1
  have hkk0 : k₀ ≤ k := (pow_le_pow_iff_right₀ hρ).mp (le_trans hn0 hVle)
  have hlogk2 : log ((k : ℝ) + 2) ≤ Dρ + log (log V) := by
    rw [hDρ_def]; exact log_add_two_le_add_loglog hρ hk hlogV3
  -- Core inequality `2(1+ε)ρ^k log(k+2) ≤ b²·2V loglog V`.
  have hMn : M n ω < √(2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2)) := hk₀ k hkk0 n hVle
  have hlognn : (0 : ℝ) ≤ log ((k : ℝ) + 2) :=
    log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have h1 : (1 + ε) * ρ ^ k * log ((k : ℝ) + 2) ≤ (1 + ε) * (ρ * V) * (Dρ + log (log V)) := by
    have hmul : ρ ^ k * log ((k : ℝ) + 2) ≤ ρ * V * (Dρ + log (log V)) :=
      mul_le_mul hρk hlogk2 hlognn (by positivity)
    nlinarith [hmul, hε0]
  have h2 : (1 + ε) * ρ * Dρ ≤ (b ^ 2 - (1 + ε) * ρ) * log (log V) := by
    rw [hT_def, div_le_iff₀ hbApos] at hloglogVT
    linarith [hloglogVT]
  have hcore : 2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2) ≤ b ^ 2 * (2 * V * log (log V)) := by
    nlinarith [h1, mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 * V by positivity),
      hVpos, hloglogVpos]
  have hsqrt : √(2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2)) ≤ b * √(2 * V * log (log V)) := by
    rw [show b * √(2 * V * log (log V)) = √(b ^ 2 * (2 * V * log (log V))) from by
      rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb0.le]]
    exact Real.sqrt_le_sqrt hcore
  exact hMn.le.trans hsqrt

/-- **Sharp `limsup ≤ 1`, one-sided.** For a bounded-increment `L²`-martingale with `M_0 = 0` and
`⟨M⟩_n → ∞` a.s., almost surely for every `b > 1` eventually
`M_n ≤ b √(2 ⟨M⟩_n log log⟨M⟩_n)`, i.e. `limsup M_n/√(2⟨M⟩_n log log⟨M⟩_n) ≤ 1`. Countable
intersection over `b_m = 1 + 1/(m+1) ↓ 1` of `ae_eventually_le_sqrt_predQuadVar_mul_loglog_of_lt`
with `ρ = 1+t`, `ε = t`, `δ = t/2`, `t = min((b²-1)/4, 1)`. -/
lemma ae_forall_one_lt_eventually_le_sqrt_predQuadVar_mul_loglog [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {c : ℝ} (hc : 0 < c) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, M n ω ≤ b * √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω))) := by
  refine ae_forall_one_lt_eventually_le_of_forall_nat (fun m ↦ ?_) (fun _ _ ↦ sqrt_nonneg _)
  set b : ℝ := 1 + 1 / ((m : ℝ) + 1) with hb_def
  have hb1 : 1 < b := by
    rw [hb_def]; have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hb2 : (1 : ℝ) < b ^ 2 := by nlinarith [hb1]
  -- Block parameters `ρ = 1 + t`, `ε = t`, `δ = t/2` with `t = min((b²-1)/4, 1)`, so `(1+ε)ρ < b²`.
  set t := min ((b ^ 2 - 1) / 4) 1 with ht_def
  have ht0 : 0 < t := lt_min (div_pos (by linarith) (by norm_num)) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have ht4 : t ≤ (b ^ 2 - 1) / 4 := min_le_left _ _
  exact ae_eventually_le_sqrt_predQuadVar_mul_loglog_of_lt hM hM0 hc hb hV
    (ρ := 1 + t) (ε := t) (δ := t / 2) (b := b) (by linarith) (by linarith) (by linarith)
    (by linarith) (by nlinarith [ht4, ht1, ht0])

/-- **Sharp `limsup ≤ 1`, two-sided.** Applying the one-sided sharp bound to `M` and `-M` (same
quadratic variation, `predQuadVar_neg`) gives, a.s., for every `b > 1` eventually
`|M_n| ≤ b √(2 ⟨M⟩_n log log⟨M⟩_n)`. This is the sharp constant `1` (two-sided). -/
lemma ae_forall_one_lt_eventually_abs_le_sqrt_predQuadVar_mul_loglog [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {c : ℝ} (hc : 0 < c) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, |M n ω| ≤ b * √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω))) :=
  ae_forall_one_lt_eventually_abs_le
    (ae_forall_one_lt_eventually_le_sqrt_predQuadVar_mul_loglog hM hM0 hc hb hV)
    (by
      simpa only [predQuadVar_neg] using
        ae_forall_one_lt_eventually_le_sqrt_predQuadVar_mul_loglog hM.neg (neg_ae_eq_zero hM0)
          hc (fun i ↦ (hb i).mono fun ω hω ↦ by rwa [abs_neg_increment])
          (by simpa only [predQuadVar_neg] using hV))

/-- **Sharp constant as an actual `limsup`.** The two-sided sharp bound in genuine `limsup` form:
almost surely `limsup_n |M_n| / √(2 ⟨M⟩_n log log⟨M⟩_n) ≤ 1`. Derived from the `∀ b > 1, ∀ᶠ` form
(`ae_forall_one_lt_eventually_abs_le_sqrt_predQuadVar_mul_loglog`): each `b > 1` bounds the `limsup`
(`limsup_le_of_le`, the quotient being cobounded below by `0`), and `limsup ≤ b` for all `b > 1`
gives `limsup ≤ 1`. -/
lemma ae_limsup_abs_div_sqrt_predQuadVar_mul_loglog_le_one [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {c : ℝ} (hc : 0 < c) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, limsup (fun n ↦ |M n ω| / √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω)))) atTop ≤ 1 := by
  filter_upwards [ae_forall_one_lt_eventually_abs_le_sqrt_predQuadVar_mul_loglog hM hM0 hc hb hV]
    with ω hω
  exact limsup_abs_div_le_one_of_forall_one_lt (fun _ ↦ sqrt_nonneg _) hω

/-- **Bounded-increment loglog LIL, `IsBigO` form.** For a bounded-increment `L²`-martingale with
`⟨M⟩_n → ∞` a.s., almost surely `M_n = O(√(⟨M⟩_n log log⟨M⟩_n))`: the `b = 2` instance of the
sharp bound, restated in Mathlib's `IsBigO` idiom. -/
lemma ae_isBigO_sqrt_predQuadVar_mul_loglog [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {c : ℝ} (hc : 0 < c) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, (fun n ↦ M n ω) =O[atTop]
      fun n ↦ √(predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) := by
  filter_upwards [ae_forall_one_lt_eventually_abs_le_sqrt_predQuadVar_mul_loglog hM hM0 hc hb hV]
    with ω hω
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * √2, ?_⟩
  filter_upwards [hω 2 one_lt_two] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
  calc |M n ω| ≤ 2 * √(2 * predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) := hn
    _ = 2 * √2 * √(predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) := by
        rw [mul_assoc (2 : ℝ) (predQuadVar M ℱ μ n ω), sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring

/-! ### Refined per-block Freedman bounds for growing increments (deterministic horizon)

The sharp bounded engine above requires a global increment bound; the i.i.d. Hartman–Wintner low
part has increments growing like `√(i/log i)`. We handle growing increments by stopping at each
deterministic horizon `N_j` (`stoppedProcess` at a constant time), where the increments are bounded
up to the horizon, and applying the pre-optimization Freedman bound with the near-optimal
`θ_j = α√(log(j+2)/N_j)`. The refined exponent collapses to the sharp `(½(1+δ)α²v - αC)log(j+2)`,
a `p`-series tail.

**Scope.** These are the *sharp per-block bounds* (refined-Freedman exponent). With dyadic
horizons, repackaging them to the natural `n`-scale via the least `j` with `n ≤ 2^j` incurs
`2^j ≤ 2n`, an irreducible base-2 factor, so the LIL constant would be `√2·(C/√(2v)) → √2`, not the
sharp `1`: the base-2 deterministic horizon sharpens the exponent but not the constant. The sharp
constant comes instead from horizons of base `ρ ↓ 1` together with a linear quadratic-variation
bound `⟨M⟩_n ≤ v·n`, which lets a deterministic horizon play the role of quadratic-variation
stopping at level `ρ^k`. -/

/-- **Sharp block Borel–Cantelli for a growing-increment martingale.** Given horizons `N j` (with
`1 ≤ N j`), a per-block increment bound `c j` up to horizon `N j` with admissible `θ_j c_j ≤ η`, and
`1 < αC - ½(1+δ)α²v` (so the block tails `(j+2)^{½(1+δ)α²v-αC}` are summable), almost surely for all
large `j` and every `m ≤ N j`, `⟨M⟩_m ≤ v·N j ⇒ M_m < C√(N j·log(j+2))`. The horizon sequence is a
parameter: taking `N j = ⌈ρ^j⌉` with `ρ ↓ 1` (rather than `2^j`) is what delivers the sharp constant
in the repackaging. -/
lemma ae_eventually_lt_block_of_growing_loglog [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {v C α δ η : ℝ} (hδ : 0 ≤ δ) (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hα : 0 < α) (N : ℕ → ℕ) (hN : ∀ j, 1 ≤ N j) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j)
    (hp : 1 < α * C - (1 + δ) / 2 * α ^ 2 * v)
    (hadm : ∀ᶠ (j : ℕ) in atTop, α * √(log ((j : ℝ) + 2) / (N j : ℝ)) * c j ≤ η)
    (hb : ∀ j : ℕ, ∀ i < N j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j) :
    ∀ᵐ ω ∂μ, ∀ᶠ (j : ℕ) in atTop, ∀ m ≤ N j,
      predQuadVar M ℱ μ m ω ≤ v * (N j : ℝ) →
      M m ω < C * √((N j : ℝ) * log ((j : ℝ) + 2)) := by
  have hL : ∀ j : ℕ, (0 : ℝ) < log ((j : ℝ) + 2) := fun j ↦
    log_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hNR : ∀ j, (0 : ℝ) < (N j : ℝ) := fun j ↦ by exact_mod_cast hN j
  refine ae_eventually_forall_le_lt_of_summable hM hM0 hδ hη hc0
    (θ := fun j ↦ α * √(log ((j : ℝ) + 2) / (N j : ℝ)))
    (fun j ↦ mul_pos hα (sqrt_pos.mpr (div_pos (hL j) (hNR j)))) hadm hb ?_
  -- The Freedman exponent collapses to `(½(1+δ)α²v - αC) log(j+2)`: the square roots cancel.
  refine (summable_exp_neg_mul_log_add hp).congr fun j ↦ ?_
  have hLj := hL j
  have hNj := hNR j
  have hst : √(log ((j : ℝ) + 2) / (N j : ℝ)) * √((N j : ℝ) * log ((j : ℝ) + 2))
      = log ((j : ℝ) + 2) := by
    rw [← sqrt_mul (by positivity),
      show log ((j : ℝ) + 2) / (N j : ℝ) * ((N j : ℝ) * log ((j : ℝ) + 2))
        = log ((j : ℝ) + 2) ^ 2 by field_simp, sqrt_sq hLj.le]
  have hs2 : √(log ((j : ℝ) + 2) / (N j : ℝ)) ^ 2 * (N j : ℝ) = log ((j : ℝ) + 2) := by
    rw [sq_sqrt (by positivity)]; exact div_mul_cancel₀ _ hNj.ne'
  congr 1
  linear_combination (α * C) * hst - ((1 + δ) / 2 * α ^ 2 * v) * hs2

set_option maxHeartbeats 800000 in
-- The repackaging combines the per-block bound with the least-`j` estimates `N_j ≤ ρn+1` and
-- the additive `log(j+2) ≤ D_ρ + loglog n` through a single `nlinarith`; the accumulated linear
-- arithmetic exceeds the default heartbeat budget.
/-- **Sharp `√(2vn loglog n)` LIL for a growing-increment martingale with a linear quadratic
variation bound.** With time horizons `N_j = ⌈ρ^j⌉` (`ρ ↓ 1`), the block condition
`c_j √(log(j+2)/N_j) → 0`, and `⟨M⟩_n ≤ v·n`, almost surely eventually
`M_n ≤ b √(2 v n log log n)`, whenever `C√ρ < b√(2v)` and `1 < αC - ½(1+δ)α²v`. Repackaging the
block via the least `j` with `n ≤ N_j`: `N_j ≤ ρn+1` and (additively) `log(j+2) ≤ D_ρ + loglog n`,
so the constant is `C√ρ/√(2v)·(1+o(1)) < b`. No random stopping time is used: the linear QV bound
lets a deterministic time horizon play the role of quadratic-variation stopping. -/
lemma ae_eventually_le_sqrt_nat_mul_loglog_of_growing_of_lt [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {v C α δ b ρ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ) (hα : 0 < α) (hv : 0 < v)
    (hp : 1 < α * C - (1 + δ) / 2 * α ^ 2 * v) (hb0 : 0 < b) (hbC : C * √ρ < b * √(2 * v))
    (N : ℕ → ℕ) (hNmono : Monotone N) (hN1 : ∀ j, 1 ≤ N j) (hNle : ∀ j, ρ ^ j ≤ (N j : ℝ))
    (hNlt : ∀ j, (N j : ℝ) < ρ ^ j + 1) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j)
    (hb : ∀ j, ∀ i < N j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j)
    (hH : Tendsto (fun j : ℕ ↦ c j * √(log ((j : ℝ) + 2) / (N j : ℝ))) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, M n ω ≤ b * √(2 * v * (n : ℝ) * log (log n)) := by
  obtain ⟨η, hη0, hη⟩ : ∃ η > 0, ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2 :=
    ⟨min 1 (9 / 4 * δ), lt_min one_pos (by positivity), fun _ hx ↦
      exp_le_one_add_add_half_mul_sq hx⟩
  have hCpos : 0 < C := by nlinarith [hp, mul_nonneg (sq_nonneg α) hv.le, hα]
  have hlogρ : (0 : ℝ) < log ρ := log_pos hρ
  have h2v : (0 : ℝ) < 2 * v := by positivity
  have hρpos : (0 : ℝ) < ρ := by linarith
  -- Eventual admissibility from the block condition.
  have hAdm : ∀ᶠ (j : ℕ) in atTop, α * √(log ((j : ℝ) + 2) / (N j : ℝ)) * c j ≤ η := by
    have htend : Tendsto (fun j : ℕ ↦ α * (c j * √(log ((j : ℝ) + 2) / (N j : ℝ)))) atTop
        (𝓝 0) := by
      have h := hH.const_mul α
      rwa [mul_zero] at h
    filter_upwards [htend.eventually (gt_mem_nhds hη0)] with j hj
    have he : α * √(log ((j : ℝ) + 2) / (N j : ℝ)) * c j
        = α * (c j * √(log ((j : ℝ) + 2) / (N j : ℝ))) := by ring
    rw [he]; exact hj.le
  -- `A = b²·2v - C²ρ > 0`.
  have hApos : 0 < b ^ 2 * (2 * v) - C ^ 2 * ρ := by
    have hsq : (C * √ρ) ^ 2 < (b * √(2 * v)) ^ 2 :=
      pow_lt_pow_left₀ hbC (by positivity) (by norm_num)
    rw [mul_pow, mul_pow, Real.sq_sqrt hρpos.le, Real.sq_sqrt h2v.le] at hsq
    linarith
  set Dρ : ℝ := log (1 / log ρ + 1) with hDρ_def
  have hDρnn : 0 ≤ Dρ := log_nonneg (by have := div_pos one_pos hlogρ; linarith)
  set A : ℝ := b ^ 2 * (2 * v) - C ^ 2 * ρ with hA_def
  set T : ℝ := 3 * C ^ 2 * ρ * Dρ / A + 3 * C ^ 2 * Dρ / A with hT_def
  set n₀ : ℝ := 3 * C ^ 2 / A with hn0_def
  clear_value Dρ A T n₀
  filter_upwards [ae_eventually_lt_block_of_growing_loglog hM hM0 hδ.le hη hα N hN1 c hc0
    hp hAdm hb, hqv] with ω hgood hqvn
  rw [eventually_atTop] at hgood
  obtain ⟨j₀, hj₀⟩ := hgood
  filter_upwards [eventually_ge_atTop (N j₀ + 1),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (exp (exp (max 3 T))),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop n₀] with n hn0 hnT hnn0
  -- Basic bounds on n, log n, loglog n.
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (exp_pos _) hnT
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (one_le_exp (exp_pos _).le) hnT
  have hlogn : exp (max 3 T) ≤ log n := by
    rw [← Real.log_exp (exp (max 3 T))]; exact log_le_log (exp_pos _) hnT
  have hlognpos : 0 < log n := lt_of_lt_of_le (exp_pos _) hlogn
  have hloglogn : max 3 T ≤ log (log n) := by
    rw [← Real.log_exp (max 3 T)]; exact log_le_log (exp_pos _) hlogn
  have hloglogn3 : (3 : ℝ) ≤ log (log n) := le_trans (le_max_left _ _) hloglogn
  have hloglognT : T ≤ log (log n) := le_trans (le_max_right _ _) hloglogn
  have hloglognpos : 0 < log (log n) := by linarith
  have hlogn3 : (3 : ℝ) ≤ log n := by linarith [log_le_sub_one_of_pos hlognpos, hloglogn3]
  -- Least block `j` with `n ≤ ρ^j` (`exists_pow_ge_le`), hence `n ≤ N j`.
  obtain ⟨j, hnρ, hρn, hj⟩ := exists_pow_ge_le hρ hn1
  have hjle : n ≤ N j := by exact_mod_cast hnρ.trans (hNle j)
  have hjj0 : j₀ ≤ j := by
    by_contra hlt
    rw [not_le] at hlt
    have := hNmono hlt.le
    omega
  -- `N_j ≤ ρ·n + 1`.
  have hNjR : (N j : ℝ) ≤ ρ * (n : ℝ) + 1 := by linarith [hNlt j]
  -- `log(j+2) ≤ D_ρ + loglog n` (additive).
  have hlogj2 : log ((j : ℝ) + 2) ≤ Dρ + log (log n) := by
    rw [hDρ_def]; exact log_add_two_le_add_loglog hρ hj hlogn3
  -- Apply the block bound at `m = n`.
  have hqvcond : predQuadVar M ℱ μ n ω ≤ v * (N j : ℝ) :=
    (hqvn n).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hjle) hv.le)
  have hMn : M n ω < C * √((N j : ℝ) * log ((j : ℝ) + 2)) := hj₀ j hjj0 n hjle hqvcond
  -- Arithmetic core: `C²·N_j·log(j+2) ≤ b²·2v·n·loglog n`.
  have hlognn2 : (0 : ℝ) ≤ log ((j : ℝ) + 2) :=
    log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hcore : C ^ 2 * ((N j : ℝ) * log ((j : ℝ) + 2))
      ≤ b ^ 2 * (2 * v * (n : ℝ) * log (log n)) := by
    have hprod : (N j : ℝ) * log ((j : ℝ) + 2) ≤ (ρ * (n : ℝ) + 1) * (Dρ + log (log n)) :=
      mul_le_mul hNjR hlogj2 hlognn2 (by positivity)
    have hC2Dρnn : (0 : ℝ) ≤ 3 * C ^ 2 * Dρ := by positivity
    have hC2ρDρnn : (0 : ℝ) ≤ 3 * C ^ 2 * ρ * Dρ := by positivity
    have hi : 3 * C ^ 2 * ρ * Dρ ≤ A * log (log n) := by
      have h : 3 * C ^ 2 * ρ * Dρ / A ≤ log (log n) := by
        refine le_trans ?_ hloglognT; rw [hT_def]; linarith [div_nonneg hC2Dρnn hApos.le]
      rw [div_le_iff₀ hApos, mul_comm _ A] at h; exact h
    have hii : 3 * C ^ 2 * Dρ ≤ A * log (log n) := by
      have h : 3 * C ^ 2 * Dρ / A ≤ log (log n) := by
        refine le_trans ?_ hloglognT; rw [hT_def]; linarith [div_nonneg hC2ρDρnn hApos.le]
      rw [div_le_iff₀ hApos, mul_comm _ A] at h; exact h
    have hiii : 3 * C ^ 2 ≤ A * (n : ℝ) := by
      rw [hn0_def] at hnn0
      have h := (div_le_iff₀ hApos).mp hnn0
      linarith [h, mul_comm (n : ℝ) A]
    have hbig : C ^ 2 * ((ρ * (n : ℝ) + 1) * (Dρ + log (log n)))
        ≤ b ^ 2 * (2 * v * (n : ℝ) * log (log n)) := by
      have e1 : b ^ 2 * (2 * v) = A + C ^ 2 * ρ := by rw [hA_def]; ring
      have hALn : A * log (log n) ≤ A * log (log n) * (n : ℝ) :=
        le_mul_of_one_le_right (mul_nonneg hApos.le hloglognpos.le) hn1
      have hP1 : 3 * C ^ 2 * ρ * Dρ * (n : ℝ) ≤ A * log (log n) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hi hnpos.le
      have hP2 : 3 * C ^ 2 * Dρ ≤ A * log (log n) * (n : ℝ) := hii.trans hALn
      have hP3 : 3 * C ^ 2 * log (log n) ≤ A * (n : ℝ) * log (log n) :=
        mul_le_mul_of_nonneg_right hiii hloglognpos.le
      nlinarith [hP1, hP2, hP3, e1]
    calc C ^ 2 * ((N j : ℝ) * log ((j : ℝ) + 2))
        ≤ C ^ 2 * ((ρ * (n : ℝ) + 1) * (Dρ + log (log n))) :=
          mul_le_mul_of_nonneg_left hprod (sq_nonneg C)
      _ ≤ b ^ 2 * (2 * v * (n : ℝ) * log (log n)) := hbig
  -- Assemble: `M_n < C√(N_j log(j+2)) ≤ b√(2vn loglog n)`.
  have hsqrt : C * √((N j : ℝ) * log ((j : ℝ) + 2)) ≤ b * √(2 * v * (n : ℝ) * log (log n)) := by
    rw [show C * √((N j : ℝ) * log ((j : ℝ) + 2))
        = √(C ^ 2 * ((N j : ℝ) * log ((j : ℝ) + 2))) from by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hCpos.le],
      show b * √(2 * v * (n : ℝ) * log (log n))
        = √(b ^ 2 * (2 * v * (n : ℝ) * log (log n))) from by
      rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb0.le]]
    exact Real.sqrt_le_sqrt hcore
  exact hMn.le.trans hsqrt

/-- The geometric time horizons `N_j = ⌈ρ^j⌉` (`ρ > 1`): monotone, `≥ 1`, and bracketing
`ρ^j ≤ N_j < ρ^j + 1`. These are the horizons feeding the sharp growing-increment LIL. -/
lemma exists_ceil_pow_horizon {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ N : ℕ → ℕ, Monotone N ∧ (∀ j, 1 ≤ N j) ∧ (∀ j, ρ ^ j ≤ (N j : ℝ)) ∧
      (∀ j, (N j : ℝ) < ρ ^ j + 1) :=
  ⟨fun j ↦ ⌈ρ ^ j⌉₊, fun _ _ hab ↦ Nat.ceil_mono (pow_le_pow_right₀ hρ.le hab),
    fun _ ↦ Nat.one_le_ceil_iff.mpr (by positivity), fun _ ↦ Nat.le_ceil _,
    fun _ ↦ Nat.ceil_lt_add_one (by positivity)⟩

/-- **Sharp growing-increment LIL, single constant `b`.** Given `1 < ρ`, `0 < δ`, `(1+δ)ρ < b²`, the
sharp block/repackaging with an internally-chosen optimizer `α = C/((1+δ)v)`,
`C = √((1+δ)v + b²v/ρ)` (so `2(1+δ)v < C² < 2b²v/ρ`) yields `M_n ≤ b √(2vn loglog n)` a.s.
This packages the `C, α` arithmetic; the caller supplies only the horizons, the increment bound and
the block condition `c_j √(log(j+2)/N_j) → 0`. -/
lemma ae_eventually_le_sqrt_nat_mul_loglog_of_growing [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {v δ b ρ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ) (hv : 0 < v) (hb0 : 0 < b) (hbρ : (1 + δ) * ρ < b ^ 2)
    (N : ℕ → ℕ) (hNmono : Monotone N) (hN1 : ∀ j, 1 ≤ N j) (hNle : ∀ j, ρ ^ j ≤ (N j : ℝ))
    (hNlt : ∀ j, (N j : ℝ) < ρ ^ j + 1) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j)
    (hb : ∀ j, ∀ i < N j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j)
    (hH : Tendsto (fun j : ℕ ↦ c j * √(log ((j : ℝ) + 2) / (N j : ℝ))) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, M n ω ≤ b * √(2 * v * (n : ℝ) * log (log n)) := by
  have hρpos : (0 : ℝ) < ρ := by linarith
  have h1δv : (0 : ℝ) < (1 + δ) * v := by positivity
  set C : ℝ := √((1 + δ) * v + b ^ 2 * v / ρ) with hC_def
  have hCarg : (0 : ℝ) ≤ (1 + δ) * v + b ^ 2 * v / ρ := by positivity
  have hCpos : 0 < C := Real.sqrt_pos.mpr (by positivity)
  have hC2 : C ^ 2 = (1 + δ) * v + b ^ 2 * v / ρ := Real.sq_sqrt hCarg
  set α : ℝ := C / ((1 + δ) * v) with hα_def
  have hαpos : 0 < α := by rw [hα_def]; positivity
  have hsimp : α * C - (1 + δ) / 2 * α ^ 2 * v = C ^ 2 / (2 * ((1 + δ) * v)) := by
    rw [hα_def]; field_simp; ring
  have hp : 1 < α * C - (1 + δ) / 2 * α ^ 2 * v := by
    rw [hsimp, hC2, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((1 + δ) * v))]
    have hkey : (1 + δ) * v < b ^ 2 * v / ρ := by
      rw [lt_div_iff₀ hρpos]; nlinarith [hbρ, hv]
    linarith [hkey]
  have hbC : C * √ρ < b * √(2 * v) := by
    have hlhs : (C * √ρ) ^ 2 = ((1 + δ) * v + b ^ 2 * v / ρ) * ρ := by
      rw [mul_pow, Real.sq_sqrt hρpos.le, hC2]
    have hrhs : (b * √(2 * v)) ^ 2 = b ^ 2 * (2 * v) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hsqlt : (C * √ρ) ^ 2 < (b * √(2 * v)) ^ 2 := by
      rw [hlhs, hrhs, add_mul, div_mul_cancel₀ _ hρpos.ne']
      nlinarith [hbρ, hv]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsqlt
  exact ae_eventually_le_sqrt_nat_mul_loglog_of_growing_of_lt hM hM0 hρ hδ hαpos hv hp hb0 hbC
    N hNmono hN1 hNle hNlt c hc0 hb hH hqv

/-- **The block condition from a base-independent increment growth.** If the increment growth `g`
(`0 ≤ g`) satisfies `g n · √(loglog n / n) → 0`, then for the geometric horizons `N_j` with
`ρ^j ≤ N_j` (`ρ > 1`) the block condition `g(N_j) √(log(j+2)/N_j) → 0` holds. The bridge:
`N_j → ∞`, and `log(j+2) ≤ (log K + 1)·loglog N_j` with `K = 1/log ρ + 2` (from
`j ≤ log N_j / log ρ`), so the block quantity is `≤ √(log K+1)·g(N_j)√(loglog N_j/N_j) → 0`. -/
lemma tendsto_growth_horizon {ρ : ℝ} (hρ : 1 < ρ) {g : ℕ → ℝ} (hgnn : ∀ i, 0 ≤ g i)
    {N : ℕ → ℕ} (hNle : ∀ j, ρ ^ j ≤ (N j : ℝ))
    (hg : Tendsto (fun n : ℕ ↦ g n * √(log (log n) / n)) atTop (𝓝 0)) :
    Tendsto (fun j : ℕ ↦ g (N j) * √(log ((j : ℝ) + 2) / (N j : ℝ))) atTop (𝓝 0) := by
  have hlogρ : (0 : ℝ) < log ρ := log_pos hρ
  have hρpos : (0 : ℝ) < ρ := by linarith
  set K : ℝ := 1 / log ρ + 2 with hK_def
  have hK0 : (0 : ℝ) < K := by rw [hK_def]; have := div_pos one_pos hlogρ; linarith
  have hK1 : (1 : ℝ) ≤ K := by rw [hK_def]; have := div_pos one_pos hlogρ; linarith
  have hlogK0 : (0 : ℝ) ≤ log K := Real.log_nonneg hK1
  set L : ℝ := √(log K + 1) with hL_def
  -- `N j → ∞`, and its real cast.
  have hNtop : Tendsto N atTop atTop := by
    refine tendsto_atTop.2 fun P ↦ ?_
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_ge_atTop (P : ℝ)] with j hj
    exact_mod_cast le_trans hj (hNle j)
  have hNRtop : Tendsto (fun j : ℕ ↦ (N j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNtop
  -- Comparison sequence `g(N_j) √(loglog N_j / N_j) → 0` (a subsequence of `hg`).
  have hcomp : Tendsto (fun j : ℕ ↦ g (N j) * √(log (log (N j)) / (N j))) atTop (𝓝 0) :=
    hg.comp hNtop
  have hbdd : Tendsto (fun j : ℕ ↦ L * (g (N j) * √(log (log (N j)) / (N j)))) atTop (𝓝 0) := by
    have h := hcomp.const_mul L
    rwa [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun j ↦
    mul_nonneg (hgnn _) (Real.sqrt_nonneg _)) ?_ hbdd
  filter_upwards [hNRtop.eventually_ge_atTop (exp (exp 1))] with j hj
  have hnpos : (0 : ℝ) < (N j : ℝ) := lt_of_lt_of_le (exp_pos _) hj
  have hlogn_ge : exp 1 ≤ log (N j : ℝ) := by
    rw [← Real.log_exp (exp 1)]; exact log_le_log (exp_pos _) hj
  have hlogn_pos : (0 : ℝ) < log (N j : ℝ) := lt_of_lt_of_le (exp_pos _) hlogn_ge
  have hlogn1 : (1 : ℝ) ≤ log (N j : ℝ) := le_trans (one_le_exp (by norm_num)) hlogn_ge
  have hloglogn1 : (1 : ℝ) ≤ log (log (N j : ℝ)) := by
    rw [← Real.log_exp 1]; exact log_le_log (exp_pos 1) hlogn_ge
  -- `j ≤ log N_j / log ρ`, hence `j + 2 ≤ K log N_j`.
  have hjlog : (j : ℝ) * log ρ ≤ log (N j : ℝ) := by
    rw [← Real.log_pow]; exact log_le_log (pow_pos hρpos j) (hNle j)
  have hjdiv : (j : ℝ) ≤ log (N j : ℝ) / log ρ := (le_div_iff₀ hlogρ).2 hjlog
  have hj2 : (j : ℝ) + 2 ≤ K * log (N j : ℝ) := by
    have hKe : K * log (N j : ℝ) = log (N j : ℝ) / log ρ + 2 * log (N j : ℝ) := by
      rw [hK_def]; ring
    rw [hKe]; linarith [hjdiv, hlogn1]
  -- `log(j+2) ≤ (log K + 1) loglog N_j`.
  have hlogj2 : log ((j : ℝ) + 2) ≤ (log K + 1) * log (log (N j : ℝ)) := by
    have h1 : log ((j : ℝ) + 2) ≤ log (K * log (N j : ℝ)) := log_le_log (by positivity) hj2
    rw [Real.log_mul hK0.ne' hlogn_pos.ne'] at h1
    nlinarith [h1, mul_nonneg hlogK0 (sub_nonneg.mpr hloglogn1)]
  -- Push through the square root.
  have hfrac : log ((j : ℝ) + 2) / (N j : ℝ)
      ≤ (log K + 1) * (log (log (N j : ℝ)) / (N j : ℝ)) := by
    rw [div_le_iff₀ hnpos, mul_assoc, div_mul_cancel₀ _ hnpos.ne']; exact hlogj2
  have hsqrt : √(log ((j : ℝ) + 2) / (N j : ℝ))
      ≤ L * √(log (log (N j : ℝ)) / (N j : ℝ)) := by
    calc √(log ((j : ℝ) + 2) / (N j : ℝ))
        ≤ √((log K + 1) * (log (log (N j : ℝ)) / (N j : ℝ))) := Real.sqrt_le_sqrt hfrac
      _ = L * √(log (log (N j : ℝ)) / (N j : ℝ)) := by
          rw [hL_def, Real.sqrt_mul (by linarith [hlogK0] : (0 : ℝ) ≤ log K + 1)]
  calc g (N j) * √(log ((j : ℝ) + 2) / (N j : ℝ))
      ≤ g (N j) * (L * √(log (log (N j : ℝ)) / (N j : ℝ))) :=
        mul_le_mul_of_nonneg_left hsqrt (hgnn _)
    _ = L * (g (N j) * √(log (log (N j : ℝ)) / (N j : ℝ))) := by ring

/-- **Sharp growing-increment LIL, `b > 1` limit (one-sided).** For a martingale with `M_0 = 0`, a
base-independent increment growth `|ΔM_i| ≤ g(i)` (`g` monotone, `0 ≤ g`, `g n √(loglog n/n) → 0`)
and linear quadratic variation `⟨M⟩_n ≤ v·n`, almost surely for every `b > 1` eventually
`M_n ≤ b √(2 v n loglog n)`. For each `b`, blocks with base `ρ = 1 + (b-1)/2 ↓ 1` and
`δ = (b-1)/2` give `(1+δ)ρ = ρ² < b²`; the block condition comes from `tendsto_growth_horizon`. -/
lemma ae_forall_one_lt_eventually_le_sqrt_nat_mul_loglog_of_growth [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {v : ℝ} (hv : 0 < v) {g : ℕ → ℝ} (hgmono : Monotone g) (hgnn : ∀ i, 0 ≤ g i)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ g i)
    (hg : Tendsto (fun n : ℕ ↦ g n * √(log (log n) / n)) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop,
      M n ω ≤ b * √(2 * v * (n : ℝ) * log (log n)) := by
  refine ae_forall_one_lt_eventually_le_of_forall_nat (fun m ↦ ?_) (fun _ _ ↦ sqrt_nonneg _)
  set b : ℝ := 1 + 1 / ((m : ℝ) + 1) with hb_def
  have hb1 : 1 < b := by
    rw [hb_def]; have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hbm1 : 0 < b - 1 := by linarith
  have hb0 : 0 < b := by linarith
  set δ : ℝ := (b - 1) / 2 with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; linarith
  set ρ : ℝ := 1 + δ with hρ_def
  have hρ1 : 1 < ρ := by rw [hρ_def]; linarith
  have hρb : ρ < b := by rw [hρ_def, hδ_def]; linarith
  have hbρ : (1 + δ) * ρ < b ^ 2 := by
    have heq : (1 + δ) = ρ := hρ_def.symm
    rw [heq]
    nlinarith [mul_pos (show (0 : ℝ) < b - ρ by linarith) (show (0 : ℝ) < b + ρ by linarith)]
  obtain ⟨N, hNmono, hN1, hNle, hNlt⟩ := exists_ceil_pow_horizon hρ1
  refine ae_eventually_le_sqrt_nat_mul_loglog_of_growing hM hM0 hρ1 hδ0 hv hb0 hbρ
    N hNmono hN1 hNle hNlt (fun j ↦ g (N j)) (fun j ↦ hgnn _) ?_
    (tendsto_growth_horizon hρ1 hgnn hNle hg) hqv
  intro j i hi
  filter_upwards [hb i] with ω hω
  exact hω.trans (hgmono hi.le)

/-- **Sharp growing-increment LIL, `b > 1` limit (two-sided).** Applying the one-sided limit to `M`
and `-M` (same increment growth and quadratic variation, `predQuadVar_neg`) gives, a.s., for every
`b > 1` eventually `|M_n| ≤ b √(2 v n loglog n)`: the sharp constant `1` for growing increments. -/
lemma ae_forall_one_lt_eventually_abs_le_sqrt_nat_mul_loglog_of_growth [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {v : ℝ} (hv : 0 < v) {g : ℕ → ℝ} (hgmono : Monotone g) (hgnn : ∀ i, 0 ≤ g i)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ g i)
    (hg : Tendsto (fun n : ℕ ↦ g n * √(log (log n) / n)) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop,
      |M n ω| ≤ b * √(2 * v * (n : ℝ) * log (log n)) :=
  ae_forall_one_lt_eventually_abs_le
    (ae_forall_one_lt_eventually_le_sqrt_nat_mul_loglog_of_growth hM hM0 hv hgmono hgnn hb hg
      hqv)
    (ae_forall_one_lt_eventually_le_sqrt_nat_mul_loglog_of_growth hM.neg (neg_ae_eq_zero hM0)
      hv hgmono hgnn
      (fun i ↦ (hb i).mono fun ω hω ↦ by rwa [abs_neg_increment]) hg
      (by simpa only [predQuadVar_neg] using hqv))

/-- **Sharp growing-increment LIL as a `limsup`** (two-sided). Almost surely
`limsup_n |M_n| / √(2 v n log log n) ≤ 1`, from the `∀ b > 1, ∀ᶠ` two-sided form. -/
lemma ae_limsup_abs_div_sqrt_nat_mul_loglog_of_growth_le_one [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {v : ℝ} (hv : 0 < v) {g : ℕ → ℝ} (hgmono : Monotone g) (hgnn : ∀ i, 0 ≤ g i)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ g i)
    (hg : Tendsto (fun n : ℕ ↦ g n * √(log (log n) / n)) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, limsup (fun n ↦ |M n ω| / √(2 * v * (n : ℝ) * log (log n))) atTop ≤ 1 := by
  filter_upwards [ae_forall_one_lt_eventually_abs_le_sqrt_nat_mul_loglog_of_growth hM hM0 hv
    hgmono hgnn hb hg hqv] with ω hω
  exact limsup_abs_div_le_one_of_forall_one_lt (fun _ ↦ sqrt_nonneg _) hω

/-! ### The unconditional bounded-increment LIL

A bounded-increment martingale has `⟨M⟩_n ≤ c² n` (`predQuadVar_le_of_bound`), so the sharp
growing-increment LIL applies with the constant growth `g ≡ c`, whose block condition
`c √(log log n / n) → 0` is automatic. Unlike the normalized form, this needs **no** hypothesis
`⟨M⟩_n → ∞`: a design that hits its target deterministically has `⟨M⟩ ≡ 0`, yet `M ≡ 0` is still
`O(√(n log log n))`. This is the form the (possibly degenerate) assignment martingale needs. -/

/-- **Unconditional bounded-increment loglog LIL, `IsBigO` form.** For a martingale `M` with
`M 0 = 0` and `|ΔM_i| ≤ c` a.s. (`c > 0`), almost surely `M_n = O(√(n log log n))`, with no
hypothesis on `⟨M⟩`. The `L²` side conditions are derived from the increment bound (a.e.
`|M_n| ≤ n c`). -/
lemma ae_isBigO_sqrt_nat_mul_loglog_of_bdd [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {c : ℝ} (hc : 0 < c) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    ∀ᵐ ω ∂μ, (fun n ↦ M n ω) =O[atTop] fun n : ℕ ↦ √((n : ℝ) * log (log n)) := by
  have hg : Tendsto (fun n : ℕ ↦ c * √(log (log n) / n)) atTop (𝓝 0) := by
    have h := tendsto_sqrt_loglog_div_nat.const_mul c
    rwa [mul_zero] at h
  filter_upwards [ae_forall_one_lt_eventually_abs_le_sqrt_nat_mul_loglog_of_growth hM hM0
    (by positivity : (0 : ℝ) < c ^ 2) (g := fun _ ↦ c) monotone_const (fun _ ↦ hc.le) hb hg
    (predQuadVar_le_of_bound hM hb)] with ω hω
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * √(2 * c ^ 2), ?_⟩
  filter_upwards [hω 2 one_lt_two] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
  calc |M n ω| ≤ 2 * √(2 * c ^ 2 * (n : ℝ) * log (log n)) := hn
    _ = 2 * √(2 * c ^ 2) * √((n : ℝ) * log (log n)) := by
        rw [mul_assoc (2 * c ^ 2), sqrt_mul (by positivity)]
        ring

end AlphaRAR
