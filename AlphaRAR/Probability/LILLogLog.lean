/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Probability.LIL
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A general martingale law of the iterated logarithm at the `log log` rate

This file formalizes the blueprint chapter `chap:pre_llil`, which sharpens the one-sided LIL of
`AlphaRAR/Probability/LIL.lean` from the `log` rate to the true `log log` rate, and packages it as a
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
-/

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
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
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
  simp only [hs_def, Set.mem_setOf_eq, not_exists, not_and] at hk
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
    have h := h0.const_mul a
    rwa [mul_zero] at h
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
theorem ae_eventually_forall_lt_dyadic_loglog [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c κ : ℝ} (hc : 0 < c)
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
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c : ℝ} (hc : 0 < c)
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

end AlphaRAR
