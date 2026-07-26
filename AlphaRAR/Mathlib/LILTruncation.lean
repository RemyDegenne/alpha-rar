/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.LIL
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.StrongLaw

/-!
# Ingredients for the finite-variance law of the iterated logarithm

This file collects self-contained ingredients for the finite-variance case of the one-sided law
of the iterated logarithm (blueprint chapter `chap:pre_lil`, section "the finite-variance case via
truncation", `lem:lil_truncation`). For a martingale `M_n = ∑_{i<n} ξ_i D_i` with `ξ_i` i.i.d.
centred, `E[ξ_0²] < ∞`, and `D_i ∈ {0,1}` predictable, one truncates `ξ_i` at level `b_i = √i` and
controls the tail, drift, and centred-truncated pieces separately.

## Main results

* `AlphaRAR.ae_eventually_abs_le_of_tsum_ne_top`: the Borel–Cantelli "eventually bounded" step
  (blueprint `lem:trunc_tail_const`): if `∑_i μ{|ξ_i| > b_i} < ∞` then a.s. `|ξ_i| ≤ b_i` for all
  large `i`.
* `AlphaRAR.summable_exp_neg_mul_sqrt`: `∑_k exp(-a √k) < ∞` for `a > 0`.
* `AlphaRAR.summable_block_bound`: `∑_k exp(-(C/2)√k + σ²/4) < ∞` (blueprint
  `lem:trunc_block_summable`), the summability of the per-block Freedman tail bounds.
* `AlphaRAR.abs_truncation_sub_le`: the pointwise bound `|truncation f A x - f x| ≤ (f x)²/A`.
* `AlphaRAR.abs_integral_truncation_le`: `|∫ truncation X A| ≤ (∫ X²)/A` for centred `X`
  (blueprint `lem:trunc_mean_bound`).
* `AlphaRAR.sum_one_div_sqrt_le`: `∑_{i<n} 1/√i ≤ 2√n`, the deterministic core of the drift
  bound (blueprint `lem:trunc_drift`).
-/

open MeasureTheory Filter ProbabilityTheory

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Borel–Cantelli: eventually bounded** (blueprint `lem:trunc_tail_const`, the substance).
If `∑' i, μ {ω : b i < |ξ i ω|} < ∞`, then almost surely `|ξ i ω| ≤ b i` for all large `i`.
Applied with `b_i = √i` and `∑_i P(|ξ_i| > √i) < ∞`, the truncation remainder
`ξ_i 𝟙{|ξ_i| > b_i}` vanishes eventually. -/
lemma ae_eventually_abs_le_of_tsum_ne_top {ξ : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    (h : (∑' i, μ {ω | b i < |ξ i ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ i in atTop, |ξ i ω| ≤ b i := by
  filter_upwards [ae_eventually_notMem h] with ω hω
  filter_upwards [hω] with i hi
  simpa only [Set.mem_ofPred_eq, not_lt] using hi

/-- `exp(-a √k)` is summable in `k` for `a > 0`. Since `log = o(√·)`, eventually
`2 log k ≤ a √k`, i.e. `exp(-a√k) ≤ 1/k²`, which is summable. -/
lemma summable_exp_neg_mul_sqrt {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℕ ↦ Real.exp (-a * √k)) := by
  have hcomp : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  -- eventually `log x ≤ (a/2) √x` on `ℝ`, from `log = o(x ^ (1/2))`.
  have hlogR : ∀ᶠ x : ℝ in atTop, Real.log x ≤ (a / 2) * √x := by
    have hlit := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).def
      (show (0 : ℝ) < a / 2 by positivity)
    filter_upwards [hlit, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hx
  -- transfer to `ℕ` and compare with `1/k²`.
  have hev : ∀ᶠ k : ℕ in atTop, Real.exp (-a * √k) ≤ 1 / (k : ℝ) ^ 2 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hlogR, eventually_ge_atTop 1]
      with k hk hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have h2 : 2 * Real.log k ≤ a * √k := by
      have := mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 2)
      rwa [show (2 : ℝ) * (a / 2 * √k) = a * √k from by ring] at this
    have hlk : Real.exp (2 * Real.log (k : ℝ)) = (k : ℝ) ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hkpos, pow_two]
    have hrw : (1 : ℝ) / (k : ℝ) ^ 2 = Real.exp (-(2 * Real.log k)) := by
      rw [Real.exp_neg, hlk, one_div]
    rw [hrw]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  rw [← summable_nat_add_iff N]
  exact Summable.of_nonneg_of_le (fun k ↦ (Real.exp_pos _).le)
    (fun k ↦ hN (k + N) (Nat.le_add_left N k)) ((summable_nat_add_iff N).mpr hcomp)

/-- **Pointwise truncation bound.** `|truncation f A x - f x| ≤ (f x)²/A` for `A > 0`. On the
truncation window `truncation f A x = f x` and the difference is `0`; off it `truncation f A x = 0`,
the difference is `|f x|`, and `|f x| ≥ A` there so `|f x| ≤ (f x)²/A`. -/
lemma abs_truncation_sub_le {α : Type*} (f : α → ℝ) {A : ℝ} (hA : 0 < A) (x : α) :
    |truncation f A x - f x| ≤ f x ^ 2 / A := by
  by_cases h : f x ∈ Set.Ioc (-A) A
  · rw [show truncation f A x = f x from by
      simp only [truncation, Function.comp_apply, Set.indicator_of_mem h, id_eq]]
    simp only [sub_self, abs_zero]; positivity
  · rw [show truncation f A x = 0 from by
      simp only [truncation, Function.comp_apply, Set.indicator_of_notMem h]]
    rw [zero_sub, abs_neg]
    have hAle : A ≤ |f x| := by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at h
      rcases h with h | h
      · exact le_trans (by linarith) (neg_le_abs _)
      · exact le_trans h.le (le_abs_self _)
    rw [le_div_iff₀ hA, ← sq_abs (f x), pow_two]
    exact mul_le_mul_of_nonneg_left hAle (abs_nonneg _)

/-- **Bound on the truncated mean** (blueprint `lem:trunc_mean_bound`).
If `X` is centred (`∫ X = 0`) with `X²` integrable, then `|∫ truncation X A| ≤ (∫ X²)/A` for
`A > 0`. Applied to `ξ_i` with `A = √i` and `∫ ξ_i² = σ²`, this gives `|m_i| ≤ σ²/√i`.
The point is that `∫ truncation X A = ∫(truncation X A - X)` (using `∫ X = 0`) and the pointwise
bound `abs_truncation_sub_le`. -/
lemma abs_integral_truncation_le [IsFiniteMeasure μ] {X : Ω → ℝ} (hint : Integrable X μ)
    (hX2 : Integrable (fun ω ↦ X ω ^ 2) μ) (hX0 : ∫ ω, X ω ∂μ = 0) {A : ℝ} (hA : 0 < A) :
    |∫ ω, truncation X A ω ∂μ| ≤ (∫ ω, X ω ^ 2 ∂μ) / A := by
  have htrunc_int : Integrable (truncation X A) μ := hint.aestronglyMeasurable.integrable_truncation
  have heq : ∫ ω, truncation X A ω ∂μ = ∫ ω, (truncation X A ω - X ω) ∂μ := by
    rw [integral_sub htrunc_int hint, hX0, sub_zero]
  calc |∫ ω, truncation X A ω ∂μ|
      = |∫ ω, (truncation X A ω - X ω) ∂μ| := by rw [heq]
    _ ≤ ∫ ω, |truncation X A ω - X ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, X ω ^ 2 / A ∂μ :=
        integral_mono (htrunc_int.sub hint).abs (hX2.div_const A)
          (fun ω ↦ abs_truncation_sub_le X hA ω)
    _ = (∫ ω, X ω ^ 2 ∂μ) / A := integral_div A _

/-- `∑_{i<n} 1/√i ≤ 2√n` (with the convention `1/√0 = 0`). The deterministic core of the drift
bound `lem:trunc_drift`: since `|m_i| ≤ σ²/√i`, the drift `∑ m_i D_i` is `O(√n)` (and `O(√N)`
after restricting to the sampled indices). The key step is `1/√(x+1) ≤ 2(√(x+1) - √x)`. -/
lemma sum_one_div_sqrt_le (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / √i ≤ 2 * √n := by
  have hkey : ∀ x : ℝ, 0 ≤ x → 1 / √(x + 1) ≤ 2 * (√(x + 1) - √x) := by
    intro x hx
    have hsq1 : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
    have hsq2 : √x ^ 2 = x := Real.sq_sqrt hx
    have hsp : 0 < √(x + 1) := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_iff₀ hsp]
    nlinarith [sq_nonneg (√(x + 1) - √x), hsq1, hsq2, Real.sqrt_nonneg x]
  have haux : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), 1 / √i ≤ 2 * √m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linarith [hkey (k : ℝ) (Nat.cast_nonneg k), ih]
  cases n with
  | zero => simp
  | succ m =>
    refine le_trans (haux m) ?_
    have : √(m : ℝ) ≤ √((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ m)
    push_cast at this ⊢
    linarith

/-- **Summability of the per-block Freedman bounds** (blueprint `lem:trunc_block_summable`).
For `C > 0`, `∑_k exp(-(C/2)√k + σ²/4) < ∞`; this is what makes Borel–Cantelli applicable in the
core step `lem:trunc_block` of the finite-variance LIL. -/
lemma summable_block_bound {C σ : ℝ} (hC : 0 < C) :
    Summable (fun k : ℕ ↦ Real.exp (-(C / 2) * √k + σ ^ 2 / 4)) :=
  ((summable_exp_neg_mul_sqrt (a := C / 2) (by positivity)).mul_right
    (Real.exp (σ ^ 2 / 4))).congr fun k ↦ (Real.exp_add _ _).symm

/-! ### A general finite-variance LIL for martingales with `√i`-growing increments

The one-sided LIL of `AlphaRAR/Mathlib/LIL.lean` requires *bounded* increments. Many
finite-variance martingales instead have increments that grow like `√i` (e.g. a truncated sum
truncated at level `√i`). For such a martingale the fixed-`c` argument fails, but the dyadic block
argument still works if one stops at each block horizon `2^j` and uses the *constrained* exponential
parameter `θ_j = 1/(a√{2^j})`. The lemmas below package this into a reusable tool, stated for an
abstract martingale `M` with a growing increment bound `|ΔM_i| ≤ a√i` and a linear quadratic
variation bound `⟨M⟩_n ≤ v·n`, and deliver the two-sided rate `|M_n| = O(√(n log n))` a.s.

These belong upstream (a growing-increment companion to a martingale LIL). -/

variable {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- **Per-block Freedman bound for a martingale with `√i`-growing increments.** With horizon `2^j`,
increment scale `a` (so the horizon-local bound is `c_j = a√{2^j}`), and the constrained parameter
`θ_j = 1/c_j`, the horizon Freedman inequality (`measure_exists_ge_le_exp_horizon`) gives
`μ(∃ m ≤ 2^j : λ_j ≤ M_m, ⟨M⟩_m ≤ v·2^j) ≤ exp(-(C/a)√j + v/a²)` for `λ_j = C√(2^j j)`, because
`θ_j λ_j = (C/a)√j` (the `√{2^j}` cancels) and `θ_j² · v·2^j = v/a²` stays bounded. -/
lemma measure_exists_ge_le_exp_block [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {a : ℝ} (ha : 0 < a) (hinc : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ a * √i)
    (v C : ℝ) (j : ℕ) :
    μ {ω | ∃ m ≤ 2 ^ j, C * √((2 : ℝ) ^ j * j) ≤ M m ω
          ∧ predQuadVar M ℱ μ m ω ≤ v * (2 : ℝ) ^ j}
      ≤ ENNReal.ofReal (Real.exp (-(C / a) * √j + v / a ^ 2)) := by
  set s := √((2 : ℝ) ^ j) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = (2 : ℝ) ^ j := Real.sq_sqrt (by positivity)
  set c : ℝ := a * s with hc_def
  have hcpos : 0 < c := by positivity
  set θ : ℝ := 1 / c with hθ_def
  have hθ0 : 0 < θ := by positivity
  have hθc : |θ| * c ≤ 1 := by
    rw [abs_of_pos hθ0, hθ_def, one_div, inv_mul_cancel₀ hcpos.ne']
  have hb : ∀ i < 2 ^ j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c := by
    intro i hi
    filter_upwards [hinc i] with ω hω
    refine hω.trans ?_
    rw [hc_def, hs_def]
    have hile : (i : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hi.le
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hile) ha.le
  have hmain := measure_exists_ge_le_exp_horizon hM hM0 hM2 hcpos.le hθc hθ0
    (C * √((2 : ℝ) ^ j * j)) (v * (2 : ℝ) ^ j) (2 ^ j) hb
  have hexp : -θ * (C * √((2 : ℝ) ^ j * j)) + θ ^ 2 * (v * (2 : ℝ) ^ j)
      = -(C / a) * √j + v / a ^ 2 := by
    have hmul : √((2 : ℝ) ^ j * j) = s * √j := by
      rw [hs_def]; exact Real.sqrt_mul (by positivity) _
    rw [hmul, hθ_def, hc_def, ← hs2]
    field_simp
  rw [hexp] at hmain
  exact hmain

/-- **Block Borel–Cantelli for a `√i`-growing-increment martingale.** The per-block bounds
(`measure_exists_ge_le_exp_block`) are summable in `j` (`summable_exp_neg_mul_sqrt`), so the first
Borel–Cantelli lemma gives that a.s. only finitely many blocks are bad: for a.e. `ω`, for all large
`j` and every `m ≤ 2^j`, `⟨M⟩_m ≤ v·2^j ⇒ M_m < C√(2^j j)`. -/
lemma ae_eventually_lt_block_of_growing [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {a : ℝ} (ha : 0 < a) (hinc : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ a * √i)
    (v : ℝ) {C : ℝ} (hC : 0 < C) :
    ∀ᵐ ω ∂μ, ∀ᶠ (j : ℕ) in atTop, ∀ m ≤ 2 ^ j,
      predQuadVar M ℱ μ m ω ≤ v * (2 : ℝ) ^ j → M m ω < C * √((2 : ℝ) ^ j * j) := by
  set S : ℕ → Set Ω := fun j ↦ {ω | ∃ m ≤ 2 ^ j, C * √((2 : ℝ) ^ j * j) ≤ M m ω
    ∧ predQuadVar M ℱ μ m ω ≤ v * (2 : ℝ) ^ j} with hS_def
  have hμs : ∀ j, μ (S j) ≤ ENNReal.ofReal (Real.exp (-(C / a) * √j + v / a ^ 2)) :=
    fun j ↦ measure_exists_ge_le_exp_block hM hM0 hM2 ha hinc v C j
  have hsum : Summable (fun j : ℕ ↦ Real.exp (-(C / a) * √j + v / a ^ 2)) :=
    ((summable_exp_neg_mul_sqrt (a := C / a) (by positivity)).mul_right
      (Real.exp (v / a ^ 2))).congr fun j ↦ (Real.exp_add _ _).symm
  have hfin : (∑' j, μ (S j)) ≠ ∞ := by
    have h1 : (∑' j, μ (S j))
        ≤ ∑' (j : ℕ), ENNReal.ofReal (Real.exp (-(C / a) * √j + v / a ^ 2)) :=
      ENNReal.tsum_le_tsum hμs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ (Real.exp_pos _).le) hsum] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with j hj
  intro m hm hqv
  by_contra hcon
  rw [not_lt] at hcon
  exact hj ⟨m, hm, hcon, hqv⟩

/-- **One-sided `O(√(n log n))` LIL for a `√i`-growing-increment martingale.** From the block
exceedance (`ae_eventually_lt_block_of_growing`) and the linear quadratic-variation bound
`⟨M⟩_n ≤ v·n`, almost surely `M_n ≤ C'√(n log n)` eventually. For each large `n`, take the least `j`
with `n ≤ 2^j` (so `2^j ≤ 2n` and `j ≤ log₂ n + 1`); then `⟨M⟩_n ≤ v·n ≤ v·2^j`, so the block bound
applies at `m = n`, giving `M_n < √(2^j j) ≤ C'√(n log n)`. The horizon restriction `m ≤ 2^j` yields
the `n`-scale (not the `⟨M⟩_n`-scale): time-blocking is what the growing increments permit. -/
lemma ae_eventually_le_sqrt_nat_mul_log_of_growing [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {a : ℝ} (ha : 0 < a) (hinc : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ a * √i)
    {v : ℝ} (hv : 0 ≤ v) (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∃ C', ∀ᶠ n in atTop, M n ω ≤ C' * √((n : ℝ) * Real.log n) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  filter_upwards [ae_eventually_lt_block_of_growing hM hM0 hM2 ha hinc v one_pos, hqv]
    with ω hgood hqvn
  rw [eventually_atTop] at hgood
  obtain ⟨j₀, hj₀⟩ := hgood
  refine ⟨√(2 * (1 / Real.log 2 + 1)), ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ j₀), eventually_ge_atTop 3] with n hn0 hn3
  have hex : ∃ j : ℕ, n ≤ 2 ^ j := ⟨n, n.lt_two_pow_self.le⟩
  obtain ⟨j, hjle, hjmin⟩ : ∃ j : ℕ, n ≤ 2 ^ j ∧ ∀ m, m < j → ¬ n ≤ 2 ^ m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
  have hjj0 : j₀ ≤ j := by
    have hcast : (2 : ℝ) ^ j₀ ≤ (2 : ℝ) ^ j := by exact_mod_cast le_trans hn0 hjle
    exact (pow_le_pow_iff_right₀ one_lt_two).mp hcast
  have hnR3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn1 : (1 : ℝ) ≤ Real.log n :=
    (Real.le_log_iff_exp_le hnpos).mpr (le_trans Real.exp_one_lt_d9.le (by linarith))
  have hnleR : (n : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hjle
  have hqvcond : predQuadVar M ℱ μ n ω ≤ v * (2 : ℝ) ^ j :=
    (hqvn n).trans (mul_le_mul_of_nonneg_left hnleR hv)
  have hMn : M n ω < 1 * √((2 : ℝ) ^ j * j) := hj₀ j hjj0 n hjle hqvcond
  rw [one_mul] at hMn
  have h2j : (2 : ℝ) ^ j ≤ 2 * (n : ℝ) := by
    obtain _ | m := j
    · rw [pow_zero]; linarith
    · have hm : ¬ n ≤ 2 ^ m := hjmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmR : (2 : ℝ) ^ m < (n : ℝ) := by exact_mod_cast hm
      rw [pow_succ]; linarith
  have hjlog : (j : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
    obtain _ | m := j
    · simp only [Nat.cast_zero]
      have := div_nonneg (le_trans zero_le_one hlogn1) hlog2.le; linarith
    · have hm : ¬ n ≤ 2 ^ m := hjmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmR : (2 : ℝ) ^ m < (n : ℝ) := by exact_mod_cast hm
      have hmlog : (m : ℝ) * Real.log 2 < Real.log n := by
        rw [← Real.log_pow]; exact Real.log_lt_log (by positivity) hmR
      have : (m : ℝ) < Real.log n / Real.log 2 := by rw [lt_div_iff₀ hlog2]; linarith
      push_cast; linarith
  have hprod_le : (2 : ℝ) ^ j * (j : ℝ)
      ≤ 2 * (1 / Real.log 2 + 1) * ((n : ℝ) * Real.log n) := by
    have hb2 : Real.log n / Real.log 2 + 1 ≤ (1 / Real.log 2 + 1) * Real.log n := by
      have he : (1 / Real.log 2 + 1) * Real.log n = Real.log n / Real.log 2 + Real.log n := by
        rw [add_mul, one_div, inv_mul_eq_div, one_mul]
      rw [he]; linarith
    have step1 : (2 : ℝ) ^ j * (j : ℝ) ≤ 2 * (n : ℝ) * (Real.log n / Real.log 2 + 1) :=
      mul_le_mul h2j hjlog (by positivity) (by positivity)
    have step2 : 2 * (n : ℝ) * (Real.log n / Real.log 2 + 1)
        ≤ 2 * (1 / Real.log 2 + 1) * ((n : ℝ) * Real.log n) := by
      have hmul := mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
      calc 2 * (n : ℝ) * (Real.log n / Real.log 2 + 1)
          ≤ 2 * (n : ℝ) * ((1 / Real.log 2 + 1) * Real.log n) := hmul
        _ = 2 * (1 / Real.log 2 + 1) * ((n : ℝ) * Real.log n) := by ring
    linarith
  have hDnn : (0 : ℝ) ≤ 2 * (1 / Real.log 2 + 1) := by positivity
  have hsqrt_le : √((2 : ℝ) ^ j * (j : ℝ))
      ≤ √(2 * (1 / Real.log 2 + 1)) * √((n : ℝ) * Real.log n) := by
    rw [← Real.sqrt_mul hDnn]; exact Real.sqrt_le_sqrt hprod_le
  calc M n ω ≤ √((2 : ℝ) ^ j * (j : ℝ)) := hMn.le
    _ ≤ √(2 * (1 / Real.log 2 + 1)) * √((n : ℝ) * Real.log n) := hsqrt_le

/-- **Two-sided `O(√(n log n))` LIL for a `√i`-growing-increment martingale.** Applying the
one-sided bound `ae_eventually_le_sqrt_nat_mul_log_of_growing` to both `M` and `-M` (a martingale
with the same quadratic variation, `predQuadVar_neg`, and the same increment bound) gives
`|M_n| ≤ C'√(n log n)` eventually, a.s. This is the reusable finite-variance LIL used to control a
martingale with square-root-growing increments on both sides. -/
lemma ae_eventually_abs_le_sqrt_nat_mul_log_of_growing [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {a : ℝ} (ha : 0 < a) (hinc : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ a * √i)
    {v : ℝ} (hv : 0 ≤ v) (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∃ C', ∀ᶠ n in atTop, |M n ω| ≤ C' * √((n : ℝ) * Real.log n) := by
  have hM0neg : (-M) 0 =ᵐ[μ] 0 := by
    filter_upwards [hM0] with ω hω
    simp only [Pi.neg_apply, Pi.zero_apply] at hω ⊢
    rw [hω, neg_zero]
  have hM2neg : ∀ n, Integrable (fun ω ↦ (-M) n ω ^ 2) μ := fun n ↦ by
    have he : (fun ω ↦ (-M) n ω ^ 2) = (fun ω ↦ M n ω ^ 2) := by
      funext ω; simp only [Pi.neg_apply, neg_sq]
    rw [he]; exact hM2 n
  have hincneg : ∀ i, ∀ᵐ ω ∂μ, |(-M) (i + 1) ω - (-M) i ω| ≤ a * √i := fun i ↦ by
    filter_upwards [hinc i] with ω hω
    have he : (-M) (i + 1) ω - (-M) i ω = -(M (i + 1) ω - M i ω) := by
      simp only [Pi.neg_apply]; ring
    rw [he, abs_neg]; exact hω
  have hqvneg : ∀ᵐ ω ∂μ, ∀ n, predQuadVar (-M) ℱ μ n ω ≤ v * (n : ℝ) := by
    filter_upwards [hqv] with ω hω n
    rw [predQuadVar_neg]; exact hω n
  filter_upwards [ae_eventually_le_sqrt_nat_mul_log_of_growing hM hM0 hM2 ha hinc hv hqv,
    ae_eventually_le_sqrt_nat_mul_log_of_growing hM.neg hM0neg hM2neg ha hincneg hv hqvneg]
    with ω hpos hneg
  obtain ⟨C₁, hC₁⟩ := hpos
  obtain ⟨C₂, hC₂⟩ := hneg
  refine ⟨max C₁ C₂, ?_⟩
  filter_upwards [hC₁, hC₂] with n h1 h2
  have hsq : 0 ≤ √((n : ℝ) * Real.log n) := Real.sqrt_nonneg _
  have hu : M n ω ≤ max C₁ C₂ * √((n : ℝ) * Real.log n) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsq)
  have hl : (-M) n ω ≤ max C₁ C₂ * √((n : ℝ) * Real.log n) :=
    h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hsq)
  simp only [Pi.neg_apply] at hl
  rw [abs_le]
  exact ⟨by linarith, hu⟩

end AlphaRAR
