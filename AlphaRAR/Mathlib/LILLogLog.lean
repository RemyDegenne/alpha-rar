/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.LIL
public import AlphaRAR.Mathlib.Tactic.Tendsto
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A general martingale law of the iterated logarithm at the `log log` rate

This file formalizes the blueprint chapter `chap:pre_llil`, which sharpens the one-sided LIL of
`AlphaRAR/Mathlib/LIL.lean` from the `log` rate to the true `log log` rate, and packages it as a
general martingale statement (no bandit or i.i.d. structure).

The engine — the exponential supermartingale, Ville's inequality, the optimized Freedman bound
`measure_exists_ge_le_exp_all`, and the Borel–Cantelli step — is reused verbatim from `LIL.lean`.
The only change in the bounded-increment case is the block threshold: `λ_k = κ √(2^k · log(k+2))`
(versus `K √(2^k (k+1))`), which turns the geometric tail series into a *p-series* `(k+2)^{-κ²/4}`,
summable exactly when `κ > 2`. Because the optimizer `θ_k → 0`, admissibility holds only eventually
in `k`, so the Borel–Cantelli step is used through its eventual-admissibility variant.

## Main results

* `AlphaRAR.summable_exp_neg_mul_log_add`: the p-series `∑_k exp(-p log(k+2)) < ∞` for `1 < p`
  (blueprint `lem:llil_tail_summable`).
* `AlphaRAR.ae_eventually_forall_lt_of_summable_eventually`: the Borel–Cantelli step with only
  eventual admissibility (blueprint `lem:llil_evt_adm`).
* `AlphaRAR.ae_eventually_forall_lt_dyadic_loglog`: the dyadic loglog exceedance
  (blueprint `lem:llil_bounded_block`).
* `AlphaRAR.ae_eventually_le_sqrt_predQuadVar_mul_loglog`: the consumable
  `M_n ≤ C √(⟨M⟩_n log log⟨M⟩_n)` bound (blueprint `thm:llil_bounded`).
* `AlphaRAR.ae_eventually_abs_le_sqrt_predQuadVar_mul_loglog`: its two-sided form
  (blueprint `cor:llil_norm`).
* `AlphaRAR.ae_eventually_le_sqrt_nat_mul_loglog`,
  `AlphaRAR.ae_eventually_abs_le_sqrt_nat_mul_loglog`: the `√(n log log n)`-scale forms, the second
  two-sided (blueprint `cor:llil_nat`), used for the bounded assignment martingale.
-/

@[expose] public section

open MeasureTheory Filter Real

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- **p-series summability of the loglog block tails** (blueprint `lem:llil_tail_summable`).
For `1 < p`, `∑_k exp(-p · log(k+2)) < ∞`, because `exp(-p log(k+2)) = ((k+2)^p)⁻¹`, a convergent
`p`-series (Mathlib `Real.summable_nat_rpow_inv`). Applied with `p = κ²/4 > 1` to the block tail
bounds `exp(-λ_k²/(4 v_k)) = exp(-(κ²/4) log(k+2))`. -/
lemma summable_exp_neg_mul_log_add {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ ↦ exp (-p * log ((k : ℝ) + 2))) := by
  have hbase : Summable (fun n : ℕ ↦ ((n : ℝ) ^ p)⁻¹) := summable_nat_rpow_inv.mpr hp
  have hcomp : Summable (fun k : ℕ ↦ (((k + 2 : ℕ) : ℝ) ^ p)⁻¹) :=
    hbase.comp_injective (add_left_injective 2)
  refine hcomp.congr (fun k ↦ ?_)
  have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  rw [show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
    ← rpow_neg hpos.le, rpow_def_of_pos hpos]
  congr 1
  ring

/-- **Borel–Cantelli step with eventual admissibility** (blueprint `lem:llil_evt_adm`).
A version of `ae_eventually_forall_lt_of_summable` whose positivity and admissibility hypotheses
hold only *eventually* in `k`. This is what the loglog schedule needs: its optimizer
`θ_k = λ_k/(2 v_k) → 0`, so admissibility `λ_k c ≤ 2 v_k` fails on a finite prefix. There the
trivial bound `μ(s_k) ≤ 1` keeps `∑_k μ(s_k)` finite, and the first Borel–Cantelli lemma applies. -/
lemma ae_eventually_forall_lt_of_summable_eventually [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ)
    {c : ℝ} (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {lam v : ℕ → ℝ}
    (hadm : ∀ᶠ k in atTop, 0 < lam k ∧ 0 < v k ∧ lam k * c ≤ 2 * v k)
    (hsum : Summable fun k ↦ exp (-lam k ^ 2 / (4 * v k))) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ∀ n, predQuadVar M ℱ μ n ω ≤ v k → M n ω < lam k := by
  set s : ℕ → Set Ω := fun k ↦ {ω | ∃ n, lam k ≤ M n ω ∧ predQuadVar M ℱ μ n ω ≤ v k} with hs_def
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hadm
  have hfin : (∑' k, μ (s k)) ≠ ∞ := by
    -- Split off the finite bad prefix `range k₀`; on its complement the Freedman bound applies.
    rw [← ENNReal.sum_add_tsum_compl (Finset.range k₀) fun k ↦ μ (s k)]
    refine ENNReal.add_ne_top.mpr
      ⟨(ENNReal.sum_lt_top.mpr fun k _ ↦ measure_lt_top μ (s k)).ne, ?_⟩
    have key : (∑' i : ↥((↑(Finset.range k₀) : Set ℕ)ᶜ), μ (s ↑i))
        ≤ ∑' k, ENNReal.ofReal (exp (-lam k ^ 2 / (4 * v k))) := by
      refine le_trans (ENNReal.tsum_le_tsum fun i ↦ ?_)
        (ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective _)
      obtain ⟨k, hk⟩ := i
      rw [Finset.coe_range, Set.mem_compl_iff, Set.mem_Iio, not_lt] at hk
      obtain ⟨hlk, hvk, hak⟩ := hk₀ k hk
      exact measure_exists_ge_le_exp_all hM hM0 hM2 hb hlk hvk hak
    refine ne_top_of_le_ne_top ?_ key
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (exp_pos _).le) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with k hk
  simp only [hs_def, Set.mem_ofPred_eq, not_exists, not_and] at hk
  intro n hn
  by_contra hcon
  rw [not_lt] at hcon
  exact hk n hcon hn

/-- Deterministic core of eventual admissibility: for any `a`, eventually `a·(k+2) ≤ 2^k`, since
`(k+2) = o(2^k)` (`isLittleO_coe_const_pow_of_one_lt`). -/
lemma eventually_mul_add_two_le_two_pow (a : ℝ) :
    ∀ᶠ k : ℕ in atTop, a * ((k : ℝ) + 2) ≤ (2 : ℝ) ^ k := by
  have hk2 : Tendsto (fun k : ℕ ↦ (k : ℝ) / (2 : ℝ) ^ k) atTop (𝓝 0) :=
    (isLittleO_coe_const_pow_of_one_lt (R := ℝ) one_lt_two).tendsto_div_nhds_zero
  have hc2 : Tendsto (fun k : ℕ ↦ (2 : ℝ) / (2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h0 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2) / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    have hsum := hk2.add hc2
    rw [add_zero] at hsum
    exact hsum.congr (fun k ↦ (add_div _ _ _).symm)
  have hlim : Tendsto (fun k : ℕ ↦ a * (((k : ℝ) + 2) / (2 : ℝ) ^ k)) atTop (𝓝 0) := by
    tendsto
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [← mul_div_assoc, div_lt_one h2k] at hk
  exact hk.le

/-- **Dyadic loglog exceedance** (blueprint `lem:llil_bounded_block`).
For a bounded-increment martingale (`|ΔM_i| ≤ c`, `c > 0`) and any `κ > 2`, almost surely for all
large `k` and every `n`, `⟨M⟩_n ≤ 2^k ⇒ M_n < κ √(2^k · log(k+2))`. The schedule is `v_k = 2^k`,
`λ_k = κ √(2^k log(k+2))`, whose tail bound `exp(-λ_k²/(4 v_k)) = exp(-(κ²/4) log(k+2))` is the
`p`-series (`summable_exp_neg_mul_log_add`), and whose admissibility `λ_k c ≤ 2 v_k` holds
eventually (`eventually_mul_add_two_le_two_pow`), so the eventual-admissibility step applies. -/
lemma ae_eventually_forall_lt_dyadic_loglog [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ) {c κ : ℝ} (hc : 0 < c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) (hκ : 2 < κ) :
    ∀ᵐ ω ∂μ, ∀ᶠ (k : ℕ) in atTop, ∀ n, predQuadVar M ℱ μ n ω ≤ (2 : ℝ) ^ k →
      M n ω < κ * √((2 : ℝ) ^ k * log ((k : ℝ) + 2)) := by
  have hκ0 : (0 : ℝ) < κ := lt_trans (by norm_num) hκ
  set lam : ℕ → ℝ := fun k ↦ κ * √((2 : ℝ) ^ k * log ((k : ℝ) + 2)) with hlam_def
  have hlogpos : ∀ k : ℕ, (0 : ℝ) < log ((k : ℝ) + 2) := fun k ↦
    log_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hlam_pos : ∀ k, 0 < lam k := fun k ↦ by
    simp only [hlam_def]
    exact mul_pos hκ0 (sqrt_pos.mpr (mul_pos (by positivity) (hlogpos k)))
  -- Summability: the tail is the p-series `exp(-(κ²/4) log(k+2))`.
  have hsum : Summable (fun k ↦ exp (-lam k ^ 2 / (4 * (2 : ℝ) ^ k))) := by
    have hp : (1 : ℝ) < κ ^ 2 / 4 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]; nlinarith [hκ, hκ0]
    refine (summable_exp_neg_mul_log_add hp).congr (fun k ↦ ?_)
    have hsq : lam k ^ 2 = κ ^ 2 * ((2 : ℝ) ^ k * log ((k : ℝ) + 2)) := by
      simp only [hlam_def]
      rw [mul_pow, sq_sqrt (mul_nonneg (by positivity) (hlogpos k).le)]
    rw [hsq]
    congr 1
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
  -- Eventual admissibility `λ_k c ≤ 2 · 2^k`.
  have hadm : ∀ᶠ k in atTop, 0 < lam k ∧ 0 < (2 : ℝ) ^ k ∧ lam k * c ≤ 2 * (2 : ℝ) ^ k := by
    filter_upwards [eventually_mul_add_two_le_two_pow ((κ * c) ^ 2)] with k hk
    refine ⟨hlam_pos k, by positivity, ?_⟩
    have hlog_le : log ((k : ℝ) + 2) ≤ (k : ℝ) + 2 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) + 2 by positivity); linarith
    have hkey : (κ * c) ^ 2 * log ((k : ℝ) + 2) ≤ (2 : ℝ) ^ k :=
      le_trans (mul_le_mul_of_nonneg_left hlog_le (by positivity)) hk
    have hAnn : (0 : ℝ) ≤ lam k * c := mul_nonneg (hlam_pos k).le hc.le
    have hBnn : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ k := by positivity
    rw [← sqrt_sq hAnn, ← sqrt_sq hBnn]
    apply sqrt_le_sqrt
    have hsq : (lam k * c) ^ 2 = (κ * c) ^ 2 * ((2 : ℝ) ^ k * log ((k : ℝ) + 2)) := by
      simp only [hlam_def]
      rw [mul_pow, mul_pow, sq_sqrt (mul_nonneg (by positivity) (hlogpos k).le)]
      ring
    rw [hsq]
    have hx : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have step : (κ * c) ^ 2 * ((2 : ℝ) ^ k * log ((k : ℝ) + 2))
        ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
      calc (κ * c) ^ 2 * ((2 : ℝ) ^ k * log ((k : ℝ) + 2))
          = (2 : ℝ) ^ k * ((κ * c) ^ 2 * log ((k : ℝ) + 2)) := by ring
        _ ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_left hkey hx.le
    calc (κ * c) ^ 2 * ((2 : ℝ) ^ k * log ((k : ℝ) + 2))
        ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ k := step
      _ ≤ (2 * (2 : ℝ) ^ k) ^ 2 := by nlinarith [mul_self_nonneg ((2 : ℝ) ^ k)]
  exact ae_eventually_forall_lt_of_summable_eventually hM hM0 hM2 hb hadm hsum

/-- **General bounded-increment loglog LIL, normalized `O`-rate** (blueprint `thm:llil_bounded`,
consumable form `cor:llil_norm`). If `M` is an `L²`-martingale with `M 0 = 0`, `|ΔM_i| ≤ c`, and
`⟨M⟩_n → ∞` a.s., then almost surely `M_n ≤ C √(⟨M⟩_n · log log⟨M⟩_n)` for all large `n`, with a
deterministic `C`. Repackages `ae_eventually_forall_lt_dyadic_loglog`: for large `n` take the least
`k` with `⟨M⟩_n ≤ 2^k`; minimality gives `2^k ≤ 2⟨M⟩_n` and `k ≤ log₂⟨M⟩_n + 1`, so
`log(k+2) ≤ C'' log log⟨M⟩_n`, whence `κ√(2^k log(k+2)) ≤ C√(⟨M⟩_n log log⟨M⟩_n)`. -/
lemma ae_eventually_le_sqrt_predQuadVar_mul_loglog [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop, M n ω
      ≤ C * √(predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) := by
  have hlog2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hinv : (0 : ℝ) < 1 / log 2 := div_pos one_pos hlog2
  set C'' : ℝ := 1 + log (1 / log 2 + 1) with hC''_def
  have ha : (0 : ℝ) ≤ log (1 / log 2 + 1) := log_nonneg (by linarith)
  filter_upwards [ae_eventually_forall_lt_dyadic_loglog hM hM0 hM2 hc hb
      (show (2 : ℝ) < 3 by norm_num), hV] with ω hgood hVω
  rw [eventually_atTop] at hgood
  obtain ⟨k₀, hk₀⟩ := hgood
  refine ⟨3 * √(2 * C''), ?_⟩
  filter_upwards [hVω.eventually_ge_atTop ((2 : ℝ) ^ k₀), hVω.eventually_ge_atTop (exp 3)]
    with n hn0 hn3
  set V := predQuadVar M ℱ μ n ω with hV_def
  have hVpos : 0 < V := lt_of_lt_of_le (exp_pos 3) hn3
  have hV1 : (1 : ℝ) ≤ V := le_trans (one_le_exp (by norm_num : (0 : ℝ) ≤ 3)) hn3
  have hlogV3 : (3 : ℝ) ≤ log V := (le_log_iff_exp_le hVpos).mpr hn3
  have hlogVpos : 0 < log V := by linarith
  have hloglogV1 : (1 : ℝ) ≤ log (log V) :=
    (le_log_iff_exp_le hlogVpos).mpr (le_trans (le_of_lt exp_one_lt_d9) (by linarith))
  -- Least block `k` with `V ≤ 2^k`.
  obtain ⟨k, hVle, hkmin⟩ : ∃ k : ℕ, V ≤ (2 : ℝ) ^ k ∧ ∀ m, m < k → ¬ V ≤ (2 : ℝ) ^ m := by
    have hex : ∃ k : ℕ, V ≤ (2 : ℝ) ^ k :=
      ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop V).exists
    exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
  have hkk0 : k₀ ≤ k := (pow_le_pow_iff_right₀ one_lt_two).mp (le_trans hn0 hVle)
  have h2k : (2 : ℝ) ^ k ≤ 2 * V := by
    obtain _ | m := k
    · rw [pow_zero]; linarith
    · have hm : ¬ V ≤ (2 : ℝ) ^ m := hkmin m (Nat.lt_succ_self m)
      rw [not_le] at hm; rw [pow_succ]; linarith
  have hk1 : (k : ℝ) + 2 ≤ log V / log 2 + 3 := by
    obtain _ | m := k
    · simp only [Nat.cast_zero]; have := div_nonneg hlogVpos.le hlog2.le; linarith
    · have hm : ¬ V ≤ (2 : ℝ) ^ m := hkmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmlog : (m : ℝ) * log 2 < log V := by
        rw [← log_pow]; exact log_lt_log (by positivity) hm
      have : (m : ℝ) < log V / log 2 := by rw [lt_div_iff₀ hlog2]; linarith
      push_cast; linarith
  -- `log(k+2) ≤ C'' log log V`.
  have hlogk2 : log ((k : ℝ) + 2) ≤ C'' * log (log V) := by
    have hstep1 : (k : ℝ) + 2 ≤ (1 / log 2 + 1) * log V := by
      have hb2 : log V / log 2 + 3 ≤ (1 / log 2 + 1) * log V := by
        rw [add_mul, one_div, inv_mul_eq_div, one_mul]; linarith
      linarith
    have hlogstep : log ((k : ℝ) + 2) ≤ log (1 / log 2 + 1) + log (log V) := by
      calc log ((k : ℝ) + 2)
          ≤ log ((1 / log 2 + 1) * log V) := log_le_log (by positivity) hstep1
        _ = log (1 / log 2 + 1) + log (log V) :=
            log_mul (show (0 : ℝ) < 1 / log 2 + 1 by linarith).ne' hlogVpos.ne'
    rw [hC''_def]
    nlinarith [ha, hloglogV1, hlogstep]
  -- Assemble.
  have hMn : M n ω < 3 * √((2 : ℝ) ^ k * log ((k : ℝ) + 2)) := hk₀ k hkk0 n hVle
  have hprod : (2 : ℝ) ^ k * log ((k : ℝ) + 2) ≤ (2 * C'') * (V * log (log V)) := by
    have hlognn : (0 : ℝ) ≤ log ((k : ℝ) + 2) :=
      log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    calc (2 : ℝ) ^ k * log ((k : ℝ) + 2)
        ≤ (2 * V) * (C'' * log (log V)) := mul_le_mul h2k hlogk2 hlognn (by positivity)
      _ = (2 * C'') * (V * log (log V)) := by ring
  have hCnn : (0 : ℝ) ≤ 2 * C'' := by rw [hC''_def]; positivity
  have hsqrt : √((2 : ℝ) ^ k * log ((k : ℝ) + 2)) ≤ √(2 * C'') * √(V * log (log V)) := by
    rw [← sqrt_mul hCnn]; exact sqrt_le_sqrt hprod
  calc M n ω ≤ 3 * √((2 : ℝ) ^ k * log ((k : ℝ) + 2)) := hMn.le
    _ ≤ 3 * (√(2 * C'') * √(V * log (log V))) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = 3 * √(2 * C'') * √(V * log (log V)) := by ring

/-- **Bounded-increment loglog LIL at scale `√(n log log n)`, one-sided.** Combines
`ae_eventually_le_sqrt_predQuadVar_mul_loglog` with `⟨M⟩_n ≤ c² n` (`predQuadVar_le_of_bound`) and
`log log⟨M⟩_n ≤ 2 log log n` (valid once `n` is large), giving `M_n ≤ C √(n log log n)` a.s. -/
lemma ae_eventually_le_sqrt_nat_mul_loglog [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop, M n ω ≤ C * √((n : ℝ) * log (log n)) := by
  filter_upwards [ae_eventually_le_sqrt_predQuadVar_mul_loglog hM hM0 hM2 hc hb hV,
    predQuadVar_le_of_bound hM hb, hV] with ω hCex hle hVω
  obtain ⟨C, hC⟩ := hCex
  refine ⟨|C| * √(2 * c ^ 2), ?_⟩
  filter_upwards [hC, hVω.eventually_ge_atTop (exp 1),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (c ^ 2),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (exp 2)] with n hCn hVe hnc hne2
  set V := predQuadVar M ℱ μ n ω with hV_def
  have hVpos : 0 < V := lt_of_lt_of_le (exp_pos 1) hVe
  have hlogV1 : (1 : ℝ) ≤ log V := (le_log_iff_exp_le hVpos).mpr hVe
  have hlogVpos : 0 < log V := by linarith
  have hloglogVnn : 0 ≤ log (log V) := log_nonneg hlogV1
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (exp_pos 2) hne2
  have hlogn2 : (2 : ℝ) ≤ log n := (le_log_iff_exp_le hnpos).mpr hne2
  have hlogV_le : log V ≤ 2 * log n := by
    have h1 : log V ≤ log (c ^ 2 * n) := log_le_log hVpos (hle n)
    rw [log_mul (show (0 : ℝ) < c ^ 2 by positivity).ne' hnpos.ne'] at h1
    have hlogc2 : log (c ^ 2) ≤ log n := log_le_log (by positivity) hnc
    linarith
  have hloglogV_le : log (log V) ≤ 2 * log (log n) := by
    have h1 : log (log V) ≤ log (2 * log n) := log_le_log hlogVpos hlogV_le
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (show (0 : ℝ) < log n by linarith).ne'] at h1
    have hlog2_le : log 2 ≤ log (log n) := log_le_log (by norm_num) hlogn2
    linarith
  have hprodle : V * log (log V) ≤ 2 * c ^ 2 * ((n : ℝ) * log (log n)) := by
    nlinarith [mul_le_mul (hle n) hloglogV_le hloglogVnn (by positivity : (0 : ℝ) ≤ c ^ 2 * n)]
  have hsqrt : √(V * log (log V)) ≤ √(2 * c ^ 2) * √((n : ℝ) * log (log n)) := by
    rw [← sqrt_mul (by positivity)]; exact sqrt_le_sqrt hprodle
  calc M n ω ≤ C * √(V * log (log V)) := hCn
    _ ≤ |C| * √(V * log (log V)) := mul_le_mul_of_nonneg_right (le_abs_self C) (sqrt_nonneg _)
    _ ≤ |C| * (√(2 * c ^ 2) * √((n : ℝ) * log (log n))) :=
        mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C)
    _ = |C| * √(2 * c ^ 2) * √((n : ℝ) * log (log n)) := by ring

/-- **Bounded-increment loglog LIL at scale `√(n log log n)`, two-sided** (blueprint
`cor:llil_nat`). Applying the one-sided bound to `M` and `-M` (same quadratic variation, same
increment bound) gives `|M_n| ≤ C √(n log log n)` eventually, a.s. This is the consumable form for
the bounded assignment martingale. -/
lemma ae_eventually_abs_le_sqrt_nat_mul_loglog [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop, |M n ω| ≤ C * √((n : ℝ) * log (log n)) := by
  have hM0neg : (-M) 0 =ᵐ[μ] 0 := by
    filter_upwards [hM0] with ω hω
    simp only [Pi.neg_apply, Pi.zero_apply] at hω ⊢; rw [hω, neg_zero]
  have hM2neg : ∀ n, MemLp ((-M) n) 2 μ := fun n ↦ (hM2 n).neg
  have hbneg : ∀ i, ∀ᵐ ω ∂μ, |(-M) (i + 1) ω - (-M) i ω| ≤ c := fun i ↦ by
    filter_upwards [hb i] with ω hω
    have he : (-M) (i + 1) ω - (-M) i ω = -(M (i + 1) ω - M i ω) := by
      simp only [Pi.neg_apply]; ring
    rw [he, abs_neg]; exact hω
  have hVneg : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar (-M) ℱ μ n ω) atTop atTop := by
    filter_upwards [hV] with ω hω; simpa only [predQuadVar_neg] using hω
  filter_upwards [ae_eventually_le_sqrt_nat_mul_loglog hM hM0 hM2 hc hb hV,
    ae_eventually_le_sqrt_nat_mul_loglog hM.neg hM0neg hM2neg hc hbneg hVneg] with ω hpos hneg
  obtain ⟨C₁, hC₁⟩ := hpos
  obtain ⟨C₂, hC₂⟩ := hneg
  refine ⟨max C₁ C₂, ?_⟩
  filter_upwards [hC₁, hC₂] with n h1 h2
  have hsq : 0 ≤ √((n : ℝ) * log (log n)) := sqrt_nonneg _
  have hu : M n ω ≤ max C₁ C₂ * √((n : ℝ) * log (log n)) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsq)
  have hl : (-M) n ω ≤ max C₁ C₂ * √((n : ℝ) * log (log n)) :=
    h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hsq)
  simp only [Pi.neg_apply] at hl
  rw [abs_le]
  exact ⟨by linarith, hu⟩

/-- **General bounded-increment loglog LIL, two-sided normalized form** (blueprint `cor:llil_norm`).
`|M_n| ≤ C √(⟨M⟩_n log log⟨M⟩_n)` eventually, a.s., by applying
`ae_eventually_le_sqrt_predQuadVar_mul_loglog` to `M` and `-M`. -/
lemma ae_eventually_abs_le_sqrt_predQuadVar_mul_loglog [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ)
    {c : ℝ} (hc : 0 < c) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop,
      |M n ω| ≤ C * √(predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) := by
  have hM0neg : (-M) 0 =ᵐ[μ] 0 := by
    filter_upwards [hM0] with ω hω
    simp only [Pi.neg_apply, Pi.zero_apply] at hω ⊢; rw [hω, neg_zero]
  have hM2neg : ∀ n, MemLp ((-M) n) 2 μ := fun n ↦ (hM2 n).neg
  have hbneg : ∀ i, ∀ᵐ ω ∂μ, |(-M) (i + 1) ω - (-M) i ω| ≤ c := fun i ↦ by
    filter_upwards [hb i] with ω hω
    have he : (-M) (i + 1) ω - (-M) i ω = -(M (i + 1) ω - M i ω) := by
      simp only [Pi.neg_apply]; ring
    rw [he, abs_neg]; exact hω
  have hVneg : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar (-M) ℱ μ n ω) atTop atTop := by
    filter_upwards [hV] with ω hω; simpa only [predQuadVar_neg] using hω
  filter_upwards [ae_eventually_le_sqrt_predQuadVar_mul_loglog hM hM0 hM2 hc hb hV,
    ae_eventually_le_sqrt_predQuadVar_mul_loglog hM.neg hM0neg hM2neg hc hbneg hVneg]
    with ω hpos hneg
  obtain ⟨C₁, hC₁⟩ := hpos
  obtain ⟨C₂, hC₂⟩ := hneg
  simp only [predQuadVar_neg, Pi.neg_apply] at hC₂
  refine ⟨max C₁ C₂, ?_⟩
  filter_upwards [hC₁, hC₂] with n h1 h2
  have hsq : 0 ≤ √(predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) := sqrt_nonneg _
  have hu : M n ω ≤ max C₁ C₂ * √(predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsq)
  have hl : -M n ω ≤ max C₁ C₂ * √(predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) :=
    h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hsq)
  rw [abs_le]
  exact ⟨by linarith, hu⟩

/-! ### Growing increments: the per-block loglog Freedman bound

Toward the finite-variance (i.i.d. Hartman–Wintner) case, whose truncated main part has increments
that grow like `√(i/log i)`. On block `j` (horizon `2^j`) with the near-optimal
`θ_j = α √(log(j+2)/2^j)` and increment bound `c_j = a √(2^j/(j+1))`, the exponent
`-θ_j λ_j + θ_j² v_j` collapses (square roots cancel) to `(α²v - αC) log(j+2)`, a `p`-series tail.
-/

/-- **Per-block loglog Freedman bound for a growing-increment martingale.** With
`θ_j = α √(log(j+2)/2^j)` (near-optimal for a `log log` threshold), an increment bound `c` up to the
horizon `2^j`, threshold `λ_j = C √(2^j log(j+2))` and quadratic-variation bound `v·2^j`, the
horizon Freedman inequality gives exponent `(α²v - αC) log(j+2)` — the square roots collapse
(`√(L/2^j)·√(2^j·L) = L`). Admissibility `θ_j · c ≤ 1` is a hypothesis. -/
lemma measure_exists_ge_le_exp_block_loglog [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ)
    {v C α c : ℝ} (hα : 0 < α) (hc0 : 0 ≤ c) (j : ℕ)
    (hadm : α * √(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) * c ≤ 1)
    (hinc : ∀ i < 2 ^ j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    μ {ω | ∃ m ≤ 2 ^ j, C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2)) ≤ M m ω
          ∧ predQuadVar M ℱ μ m ω ≤ v * (2 : ℝ) ^ j}
      ≤ ENNReal.ofReal (exp ((α ^ 2 * v - α * C) * log ((j : ℝ) + 2))) := by
  have hL : (0 : ℝ) < log ((j : ℝ) + 2) :=
    log_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  set θ : ℝ := α * √(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) with hθ_def
  have hθ0 : 0 < θ := mul_pos hα (sqrt_pos.mpr (by positivity))
  have hθc : |θ| * c ≤ 1 := by rw [abs_of_pos hθ0]; exact hadm
  have hmain := measure_exists_ge_le_exp_horizon hM hM0 hM2 hc0 hθc hθ0
    (C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2))) (v * (2 : ℝ) ^ j) (2 ^ j) hinc
  refine le_trans hmain (le_of_eq ?_)
  congr 2
  -- `-θ λ + θ² v' = (α²v - αC) log(j+2)`, the square roots collapsing.
  have hcollapse2 : √(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) * √((2 : ℝ) ^ j * log ((j : ℝ) + 2))
      = log ((j : ℝ) + 2) := by
    rw [← sqrt_mul (by positivity),
      show log ((j : ℝ) + 2) / (2 : ℝ) ^ j * ((2 : ℝ) ^ j * log ((j : ℝ) + 2))
        = log ((j : ℝ) + 2) ^ 2 by field_simp, sqrt_sq hL.le]
  have hterm1 : θ * (C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2))) = α * C * log ((j : ℝ) + 2) := by
    rw [hθ_def]
    calc α * √(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) * (C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2)))
        = α * C * (√(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) * √((2 : ℝ) ^ j * log ((j : ℝ) + 2))) := by
          ring
      _ = α * C * log ((j : ℝ) + 2) := by rw [hcollapse2]
  have hterm2 : θ ^ 2 * (v * (2 : ℝ) ^ j) = α ^ 2 * v * log ((j : ℝ) + 2) := by
    rw [hθ_def, mul_pow, sq_sqrt (by positivity)]
    field_simp
  rw [show -θ * (C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2))) + θ ^ 2 * (v * (2 : ℝ) ^ j)
      = -(θ * (C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2)))) + θ ^ 2 * (v * (2 : ℝ) ^ j) by ring,
    hterm1, hterm2]
  ring

/-- **Block Borel–Cantelli for a growing-increment martingale at the `log log` scale.** Given a
per-block increment bound `c j` up to horizon `2^j` with admissible `θ_j c_j ≤ 1`, and
`1 < αC - α²v` (so the block tails `exp((α²v-αC)log(j+2)) = (j+2)^{α²v-αC}` are summable), almost
surely for all large `j` and every `m ≤ 2^j`, `⟨M⟩_m ≤ v·2^j ⇒ M_m < C√(2^j log(j+2))`. -/
lemma ae_eventually_lt_block_of_growing_loglog [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ)
    {v C α : ℝ} (hα : 0 < α) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hp : 1 < α * C - α ^ 2 * v)
    (hadm : ∀ j : ℕ, α * √(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) * c j ≤ 1)
    (hinc : ∀ j : ℕ, ∀ i < 2 ^ j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j) :
    ∀ᵐ ω ∂μ, ∀ᶠ (j : ℕ) in atTop, ∀ m ≤ 2 ^ j,
      predQuadVar M ℱ μ m ω ≤ v * (2 : ℝ) ^ j → M m ω < C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2)) := by
  set S : ℕ → Set Ω := fun j ↦ {ω | ∃ m ≤ 2 ^ j, C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2)) ≤ M m ω
    ∧ predQuadVar M ℱ μ m ω ≤ v * (2 : ℝ) ^ j} with hS_def
  have hμs : ∀ j, μ (S j) ≤ ENNReal.ofReal (exp ((α ^ 2 * v - α * C) * log ((j : ℝ) + 2))) :=
    fun j ↦ measure_exists_ge_le_exp_block_loglog hM hM0 hM2 hα (hc0 j) j (hadm j) (hinc j)
  have hsummable : Summable (fun j : ℕ ↦ exp ((α ^ 2 * v - α * C) * log ((j : ℝ) + 2))) := by
    have heq : (fun j : ℕ ↦ exp ((α ^ 2 * v - α * C) * log ((j : ℝ) + 2)))
        = fun j : ℕ ↦ exp (-(α * C - α ^ 2 * v) * log ((j : ℝ) + 2)) := by
      funext j; congr 1; ring
    rw [heq]; exact summable_exp_neg_mul_log_add hp
  have hfin : (∑' j, μ (S j)) ≠ ∞ := by
    have h1 : (∑' j, μ (S j))
        ≤ ∑' j : ℕ, ENNReal.ofReal (exp ((α ^ 2 * v - α * C) * log ((j : ℝ) + 2))) :=
      ENNReal.tsum_le_tsum hμs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ (exp_pos _).le) hsummable] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with j hj
  intro m hm hqv
  by_contra hcon
  rw [not_lt] at hcon
  exact hj ⟨m, hm, hcon, hqv⟩

/-- **One-sided `√(n log log n)` LIL for a growing-increment martingale.** From the block exceedance
(`ae_eventually_lt_block_of_growing_loglog`) and a linear quadratic-variation bound `⟨M⟩_n ≤ v·n`,
almost surely `M_n ≤ C'√(n log log n)` eventually. For large `n` take the least `j` with `n ≤ 2^j`;
then `2^j ≤ 2n`, `j ≤ log₂n + 1`, `⟨M⟩_n ≤ v·n ≤ v·2^j`, and `log(j+2) ≤ C'' log log n`. -/
lemma ae_eventually_le_sqrt_nat_mul_loglog_of_growing [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ)
    {v C α : ℝ} (hα : 0 < α) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hp : 1 < α * C - α ^ 2 * v)
    (hadm : ∀ j : ℕ, α * √(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) * c j ≤ 1)
    (hinc : ∀ j : ℕ, ∀ i < 2 ^ j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j) (hv : 0 ≤ v)
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∃ C', ∀ᶠ n in atTop, M n ω ≤ C' * √((n : ℝ) * log (log n)) := by
  have hlog2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hinv : (0 : ℝ) < 1 / log 2 := div_pos one_pos hlog2
  set C'' : ℝ := 1 + log (1 / log 2 + 1) with hC''_def
  have ha : (0 : ℝ) ≤ log (1 / log 2 + 1) := log_nonneg (by linarith)
  have hCpos : 0 < C := by nlinarith [hp, mul_nonneg (sq_nonneg α) hv, hα]
  filter_upwards [ae_eventually_lt_block_of_growing_loglog hM hM0 hM2 hα c hc0 hp hadm hinc, hqv]
    with ω hgood hqvn
  rw [eventually_atTop] at hgood
  obtain ⟨j₀, hj₀⟩ := hgood
  refine ⟨C * √(2 * C''), ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ j₀),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (exp 3)] with n hn0 hne3
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (exp_pos 3) hne3
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (one_le_exp (by norm_num : (0 : ℝ) ≤ 3)) hne3
  have hlogn3 : (3 : ℝ) ≤ log n := (le_log_iff_exp_le hnpos).mpr hne3
  have hlognpos : 0 < log n := by linarith
  have hloglogn1 : (1 : ℝ) ≤ log (log n) :=
    (le_log_iff_exp_le hlognpos).mpr (le_trans (le_of_lt exp_one_lt_d9) (by linarith))
  -- Least block `j` with `n ≤ 2^j`.
  obtain ⟨j, hjle, hjmin⟩ : ∃ j : ℕ, n ≤ 2 ^ j ∧ ∀ m, m < j → ¬ n ≤ 2 ^ m := by
    have hex : ∃ j : ℕ, n ≤ 2 ^ j := ⟨n, n.lt_two_pow_self.le⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
  have hjj0 : j₀ ≤ j :=
    (pow_le_pow_iff_right₀ one_lt_two).mp (by exact_mod_cast le_trans hn0 hjle)
  have hnleR : (n : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hjle
  have hqvcond : predQuadVar M ℱ μ n ω ≤ v * (2 : ℝ) ^ j :=
    (hqvn n).trans (mul_le_mul_of_nonneg_left hnleR hv)
  have hMn : M n ω < C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2)) := hj₀ j hjj0 n hjle hqvcond
  have h2j : (2 : ℝ) ^ j ≤ 2 * (n : ℝ) := by
    obtain _ | m := j
    · rw [pow_zero]; linarith
    · have hm : ¬ n ≤ 2 ^ m := hjmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmR : (2 : ℝ) ^ m < (n : ℝ) := by exact_mod_cast hm
      rw [pow_succ]; linarith
  have hk1 : (j : ℝ) + 2 ≤ log n / log 2 + 3 := by
    obtain _ | m := j
    · simp only [Nat.cast_zero]; have := div_nonneg hlognpos.le hlog2.le; linarith
    · have hm : ¬ n ≤ 2 ^ m := hjmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmlog : (m : ℝ) * log 2 < log n := by
        rw [← log_pow]; exact log_lt_log (by positivity) (by exact_mod_cast hm)
      have : (m : ℝ) < log n / log 2 := by rw [lt_div_iff₀ hlog2]; linarith
      push_cast; linarith
  have hlogj2 : log ((j : ℝ) + 2) ≤ C'' * log (log n) := by
    have hstep1 : (j : ℝ) + 2 ≤ (1 / log 2 + 1) * log n := by
      have hb2 : log n / log 2 + 3 ≤ (1 / log 2 + 1) * log n := by
        rw [add_mul, one_div, inv_mul_eq_div, one_mul]; linarith
      linarith
    have hlogstep : log ((j : ℝ) + 2) ≤ log (1 / log 2 + 1) + log (log n) := by
      calc log ((j : ℝ) + 2)
          ≤ log ((1 / log 2 + 1) * log n) := log_le_log (by positivity) hstep1
        _ = log (1 / log 2 + 1) + log (log n) :=
            log_mul (show (0 : ℝ) < 1 / log 2 + 1 by linarith).ne' hlognpos.ne'
    rw [hC''_def]
    nlinarith [ha, hloglogn1, hlogstep]
  have hlognn : (0 : ℝ) ≤ log ((j : ℝ) + 2) :=
    log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hprod : (2 : ℝ) ^ j * log ((j : ℝ) + 2) ≤ (2 * C'') * ((n : ℝ) * log (log n)) := by
    calc (2 : ℝ) ^ j * log ((j : ℝ) + 2)
        ≤ (2 * (n : ℝ)) * (C'' * log (log n)) := mul_le_mul h2j hlogj2 hlognn (by positivity)
      _ = (2 * C'') * ((n : ℝ) * log (log n)) := by ring
  have hCnn : (0 : ℝ) ≤ 2 * C'' := by rw [hC''_def]; positivity
  have hsqrt : √((2 : ℝ) ^ j * log ((j : ℝ) + 2)) ≤ √(2 * C'') * √((n : ℝ) * log (log n)) := by
    rw [← sqrt_mul hCnn]; exact sqrt_le_sqrt hprod
  calc M n ω ≤ C * √((2 : ℝ) ^ j * log ((j : ℝ) + 2)) := hMn.le
    _ ≤ C * (√(2 * C'') * √((n : ℝ) * log (log n))) := mul_le_mul_of_nonneg_left hsqrt hCpos.le
    _ = C * √(2 * C'') * √((n : ℝ) * log (log n)) := by ring

/-- **Two-sided `√(n log log n)` LIL for a growing-increment martingale.** Applying the one-sided
`ae_eventually_le_sqrt_nat_mul_loglog_of_growing` to `M` and `-M` (same increment bound and
quadratic variation, `predQuadVar_neg`) gives `|M_n| ≤ C'√(n log log n)` eventually, a.s. Reusable —
growing-increment loglog LIL — the engine for the truncated main part of the i.i.d. case. -/
lemma ae_eventually_abs_le_sqrt_nat_mul_loglog_of_growing [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ)
    {v C α : ℝ} (hα : 0 < α) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hp : 1 < α * C - α ^ 2 * v)
    (hadm : ∀ j : ℕ, α * √(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) * c j ≤ 1)
    (hinc : ∀ j : ℕ, ∀ i < 2 ^ j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j) (hv : 0 ≤ v)
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∃ C', ∀ᶠ n in atTop, |M n ω| ≤ C' * √((n : ℝ) * log (log n)) := by
  have hM0neg : (-M) 0 =ᵐ[μ] 0 := by
    filter_upwards [hM0] with ω hω
    simp only [Pi.neg_apply, Pi.zero_apply] at hω ⊢; rw [hω, neg_zero]
  have hM2neg : ∀ n, MemLp ((-M) n) 2 μ := fun n ↦ (hM2 n).neg
  have hincneg : ∀ j : ℕ, ∀ i < 2 ^ j, ∀ᵐ ω ∂μ, |(-M) (i + 1) ω - (-M) i ω| ≤ c j :=
    fun j i hi ↦ by
      filter_upwards [hinc j i hi] with ω hω
      have he : (-M) (i + 1) ω - (-M) i ω = -(M (i + 1) ω - M i ω) := by
        simp only [Pi.neg_apply]; ring
      rw [he, abs_neg]; exact hω
  have hqvneg : ∀ᵐ ω ∂μ, ∀ n, predQuadVar (-M) ℱ μ n ω ≤ v * (n : ℝ) := by
    filter_upwards [hqv] with ω hω n; rw [predQuadVar_neg]; exact hω n
  filter_upwards
    [ae_eventually_le_sqrt_nat_mul_loglog_of_growing hM hM0 hM2 hα c hc0 hp hadm hinc hv hqv,
     ae_eventually_le_sqrt_nat_mul_loglog_of_growing hM.neg hM0neg hM2neg hα c hc0 hp hadm hincneg
       hv hqvneg] with ω hpos hneg
  obtain ⟨C₁, hC₁⟩ := hpos
  obtain ⟨C₂, hC₂⟩ := hneg
  refine ⟨max C₁ C₂, ?_⟩
  filter_upwards [hC₁, hC₂] with n h1 h2
  have hsq : 0 ≤ √((n : ℝ) * log (log n)) := sqrt_nonneg _
  have hu : M n ω ≤ max C₁ C₂ * √((n : ℝ) * log (log n)) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsq)
  have hl : (-M) n ω ≤ max C₁ C₂ * √((n : ℝ) * log (log n)) :=
    h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hsq)
  simp only [Pi.neg_apply] at hl
  rw [abs_le]; exact ⟨by linarith, hu⟩

/-- **Unconditional bounded-increment loglog LIL at scale `√(n log log n)`.** For an `L²`-martingale
`M` with `M 0 = 0` and `|ΔM_i| ≤ c` a.s. (`c > 0`), almost surely `|M_n| ≤ C √(n log log n)` for all
large `n`, with a deterministic `C`. Unlike `ae_eventually_abs_le_sqrt_nat_mul_loglog`, this needs
**no** hypothesis `⟨M⟩_n → ∞`: it applies the deterministic-horizon growing-increment engine
`ae_eventually_abs_le_sqrt_nat_mul_loglog_of_growing`, whose only quadratic-variation input is the
*linear* bound `⟨M⟩_n ≤ c² n` (`predQuadVar_le_of_bound`), valid unconditionally for bounded
increments. This is the form the (possibly degenerate) assignment martingale needs: a design that
hits its target deterministically has `⟨M⟩ ≡ 0`, so `⟨M⟩ → ∞` genuinely fails, yet `M ≡ 0` is still
`O(√(n log log n))`. Parameters `α = 1/c`, `C = 3c`, `v = c²` satisfy the engine's `hp` (`1 < 2`)
and `hadm` (via `log(j+2) ≤ 2^j`). The `L²` side conditions are all derived from the increment
bound (a.e. `|M_n| ≤ n c`, so `M_n` is square-integrable). -/
lemma ae_eventually_abs_le_sqrt_nat_mul_loglog_of_bdd [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {c : ℝ} (hc : 0 < c) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop, |M n ω| ≤ C * √((n : ℝ) * log (log n)) := by
  have hmeasM : ∀ n, AEMeasurable (M n) μ := fun n ↦
    ((hM.stronglyMeasurable n).mono (ℱ.le n)).measurable.aemeasurable
  -- Telescoping bound `|M_n| ≤ n c` a.e., whence `M_n` is square-integrable.
  have hbdd : ∀ n, ∀ᵐ ω ∂μ, |M n ω| ≤ n * c := by
    intro n
    filter_upwards [ae_all_iff.mpr hb, hM0] with ω hbω hM0ω
    simp only [Pi.zero_apply] at hM0ω
    have htel : (∑ k ∈ Finset.range n, (M (k + 1) ω - M k ω)) = M n ω := by
      rw [Finset.sum_range_sub (M · ω) n, hM0ω, sub_zero]
    calc |M n ω| = |∑ k ∈ Finset.range n, (M (k + 1) ω - M k ω)| := by rw [htel]
      _ ≤ ∑ k ∈ Finset.range n, |M (k + 1) ω - M k ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, c := Finset.sum_le_sum fun k _ ↦ hbω k
      _ = n * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM2 : ∀ n, MemLp (M n) 2 μ := fun n ↦
    .of_bound (hmeasM n).aestronglyMeasurable ((n : ℝ) * c)
      (by filter_upwards [hbdd n] with ω h; rwa [Real.norm_eq_abs])
  have hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ c ^ 2 * (n : ℝ) :=
    predQuadVar_le_of_bound hM hb
  refine ae_eventually_abs_le_sqrt_nat_mul_loglog_of_growing (α := 1 / c) (C := 3 * c) (v := c ^ 2)
    hM hM0 hM2 (by positivity) (fun _ ↦ c) (fun _ ↦ hc.le) ?_ ?_ (fun j i _ ↦ hb i)
    (by positivity) hqv
  · -- `hp : 1 < (1/c)·(3c) - (1/c)²·c²`, which equals `2`.
    have hkey : (1 : ℝ) / c * (3 * c) - (1 / c) ^ 2 * c ^ 2 = 2 := by field_simp; ring
    rw [hkey]; norm_num
  · -- `hadm : ∀ j, (1/c)·√(log(j+2)/2^j)·c ≤ 1`, i.e. `√(log(j+2)/2^j) ≤ 1`.
    intro j
    rw [mul_right_comm, one_div_mul_cancel hc.ne', one_mul]
    have hjpow : (j : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
      have h : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
      calc (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h
        _ = (2 : ℝ) ^ j := by push_cast; ring
    have hlog : log ((j : ℝ) + 2) ≤ (2 : ℝ) ^ j :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    calc √(log ((j : ℝ) + 2) / (2 : ℝ) ^ j) ≤ √1 :=
          Real.sqrt_le_sqrt ((div_le_one (by positivity)).mpr hlog)
      _ = 1 := Real.sqrt_one

/-! ### A monotonicity fact for the finite-variance increment bound

The truncated main part of a finite-variance sum has increments bounded by `2 √(i/log(i+2))` (the
`log`-level truncation). To feed the growing-increment engine above one needs, on block `i < 2^j`, a
uniform bound `√(2^j/log(2^j+2))`; this rests on `x ↦ x/log(x+2)` being nondecreasing. -/

/-- `x ↦ x/log(x+2)` is nondecreasing on `[0,∞)`: cross-multiplying, this is
`x·log(x+3) ≤ (x+1)·log(x+2)`, which follows from `log(1+1/(x+2)) ≤ 1/(x+2)` and
`x/(x+2) ≤ log(x+2)`. -/
lemma div_log_add_two_le {x : ℝ} (hx : 0 ≤ x) : x / log (x + 2) ≤ (x + 1) / log (x + 3) := by
  have hlog2 : (0 : ℝ) < log (x + 2) := log_pos (by linarith)
  have hlog3 : (0 : ℝ) < log (x + 3) := log_pos (by linarith)
  rw [div_le_div_iff₀ hlog2 hlog3]
  have hkey : log (x + 3) - log (x + 2) ≤ 1 / (x + 2) := by
    rw [← log_div (show (0 : ℝ) < x + 3 by linarith).ne' (show (0 : ℝ) < x + 2 by linarith).ne',
      show (x + 3) / (x + 2) = 1 + 1 / (x + 2) by field_simp; ring]
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (x + 2) by positivity)
    linarith
  have hfrac : x / (x + 2) ≤ log (x + 2) := by
    have h1 : (1 : ℝ) - 1 / (x + 2) ≤ log (x + 2) := by
      have h := log_le_sub_one_of_pos (show (0 : ℝ) < (x + 2)⁻¹ by positivity)
      rw [log_inv, inv_eq_one_div] at h; linarith
    have h2 : x / (x + 2) ≤ 1 - 1 / (x + 2) := by
      rw [show (1 : ℝ) - 1 / (x + 2) = (x + 1) / (x + 2) by field_simp; ring]
      gcongr; linarith
    linarith
  have hm : x * (log (x + 3) - log (x + 2)) ≤ x / (x + 2) := by
    have := mul_le_mul_of_nonneg_left hkey hx; rwa [mul_one_div] at this
  nlinarith [hm, hfrac]

end AlphaRAR
