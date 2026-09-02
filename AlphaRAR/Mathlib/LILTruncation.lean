/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.Freedman
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Probability.StrongLaw

/-!
# Ingredients for the finite-variance law of the iterated logarithm

This file collects self-contained ingredients for the finite-variance case of the one-sided law
of the iterated logarithm, reached by truncation. For a martingale `M_n = ∑_{i<n} ξ_i D_i` with
`ξ_i` i.i.d. centred, `E[ξ_0²] < ∞`, and `D_i ∈ {0,1}` predictable, one truncates `ξ_i` at level
`b_i = √i` and controls the tail, drift, and centred-truncated pieces separately.

## Main results

* `AlphaRAR.ae_eventually_abs_le_of_tsum_ne_top`: the Borel–Cantelli "eventually bounded" step:
  if `∑_i μ{|ξ_i| > b_i} < ∞` then a.s. `|ξ_i| ≤ b_i` for all large `i`.
* `AlphaRAR.summable_exp_neg_mul_sqrt`: `∑_k exp(-a √k) < ∞` for `a > 0`.
* `AlphaRAR.summable_exp_neg_mul_sqrt_add`: `∑_k exp(-a√k + b) < ∞`, the summability of the
  per-block Freedman tail bounds.
* `AlphaRAR.abs_truncation_sub_le`: the pointwise bound `|truncation f A x - f x| ≤ (f x)²/A`.
* `AlphaRAR.abs_integral_truncation_le`: `|∫ truncation X A| ≤ (∫ X²)/A` for centred `X`.
* `AlphaRAR.sum_one_div_sqrt_le`: `∑_{i<n} 1/√i ≤ 2√n`, the deterministic core of the drift
  bound.
* `AlphaRAR.ae_isBigO_sqrt_nat_mul_log_of_growing`: a two-sided `O(√(n log n))` LIL
  for a martingale whose increments grow like `√i` and whose predictable quadratic variation is
  at most `v·n`.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Borel–Cantelli: eventually bounded.**
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

/-- `exp(-a √k + b)` is summable in `k` for `a > 0`: a constant multiple of
`summable_exp_neg_mul_sqrt`. This is the shape of every per-block Freedman tail with a `√k`
threshold. -/
lemma summable_exp_neg_mul_sqrt_add {a b : ℝ} (ha : 0 < a) :
    Summable (fun k : ℕ ↦ Real.exp (-a * √k + b)) :=
  ((summable_exp_neg_mul_sqrt ha).mul_right (Real.exp b)).congr fun _ ↦ (Real.exp_add _ _).symm

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

/-- **Bound on the truncated mean.**
If `X` is centred (`∫ X = 0`) with `X²` integrable, then `|∫ truncation X A| ≤ (∫ X²)/A` for
`A > 0`. Applied to `ξ_i` with `A = √i` and `∫ ξ_i² = σ²`, this gives `|m_i| ≤ σ²/√i`.
The point is that `∫ truncation X A = ∫(truncation X A - X)` (using `∫ X = 0`) and the pointwise
bound `abs_truncation_sub_le`. -/
lemma abs_integral_truncation_le [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX2 : MemLp X 2 μ) (hX0 : ∫ ω, X ω ∂μ = 0) {A : ℝ} (hA : 0 < A) :
    |∫ ω, truncation X A ω ∂μ| ≤ (∫ ω, X ω ^ 2 ∂μ) / A := by
  have hint : Integrable X μ := hX2.integrable one_le_two
  have htrunc_int : Integrable (truncation X A) μ := hint.aestronglyMeasurable.integrable_truncation
  have heq : ∫ ω, truncation X A ω ∂μ = ∫ ω, (truncation X A ω - X ω) ∂μ := by
    rw [integral_sub htrunc_int hint, hX0, sub_zero]
  calc |∫ ω, truncation X A ω ∂μ|
      = |∫ ω, (truncation X A ω - X ω) ∂μ| := by rw [heq]
    _ ≤ ∫ ω, |truncation X A ω - X ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, X ω ^ 2 / A ∂μ :=
        integral_mono (htrunc_int.sub hint).abs (hX2.integrable_sq.div_const A)
          (fun ω ↦ abs_truncation_sub_le X hA ω)
    _ = (∫ ω, X ω ^ 2 ∂μ) / A := integral_div A _

/-- `∑_{i<n} 1/√i ≤ 2√n` (with the convention `1/√0 = 0`). The deterministic core of the drift
bound: since `|m_i| ≤ σ²/√i`, the drift `∑ m_i D_i` is `O(√n)` (and `O(√N)` after restricting to
the sampled indices). The key step is `1/√(x+1) ≤ 2(√(x+1) - √x)`. -/
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

/-- **Block Borel–Cantelli for a `√i`-growing-increment martingale.** On the time block with
horizon `2^j` the increments are bounded by `c_j = a√(2^j)`; with the constrained parameter
`θ_j = 1/c_j` (the optimizer is inadmissible), threshold `λ_j = C√(2^j j)` and quadratic-variation
level `v·2^j`, the Freedman exponent is `-(C/a)√j + v/a²` (the `√(2^j)` cancels), which is
summable in `j` (`summable_exp_neg_mul_sqrt_add`). The time-block engine
`ae_eventually_forall_le_lt_of_summable` then gives: for a.e. `ω`, for all large `j` and every
`m ≤ 2^j`, `⟨M⟩_m ≤ v·2^j ⇒ M_m < C√(2^j j)`. -/
lemma ae_eventually_lt_block_of_growing [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0)
    {a : ℝ} (ha : 0 < a) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ a * √i)
    (v : ℝ) {C : ℝ} (hC : 0 < C) :
    ∀ᵐ ω ∂μ, ∀ᶠ (j : ℕ) in atTop, ∀ m ≤ 2 ^ j,
      predQuadVar M ℱ μ m ω ≤ v * (2 : ℝ) ^ j → M m ω < C * √((2 : ℝ) ^ j * j) := by
  have hs : ∀ j : ℕ, (0 : ℝ) < √((2 : ℝ) ^ j) := fun j ↦ Real.sqrt_pos.mpr (by positivity)
  refine ae_eventually_forall_le_lt_of_summable hM hM0 zero_le_one
    (fun _ hx ↦ exp_le_one_add_add_sq hx) (c := fun j ↦ a * √((2 : ℝ) ^ j))
    (fun j ↦ by positivity) (θ := fun j ↦ 1 / (a * √((2 : ℝ) ^ j)))
    (fun j ↦ by have := hs j; positivity)
    (Eventually.of_forall fun j ↦ by rw [one_div_mul_cancel (by have := hs j; positivity)])
    (fun j i hi ↦ (hb i).mono fun ω hω ↦ hω.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hi.le)) ha.le)) ?_
  -- The Freedman exponent is `-(C/a)√j + v/a²`: the `√(2^j)` cancels.
  refine (summable_exp_neg_mul_sqrt_add (a := C / a) (b := v / a ^ 2) (by positivity)).congr
    fun j ↦ ?_
  set s : ℝ := √((2 : ℝ) ^ j) with hs_def
  have hs2 : s ^ 2 = (2 : ℝ) ^ j := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := hs j
  have hmul : √((2 : ℝ) ^ j * j) = s * √j := by
    rw [hs_def]; exact Real.sqrt_mul (by positivity) _
  congr 1
  rw [hmul, show ((1 : ℝ) + 1) / 2 = 1 by norm_num, one_mul, ← hs2]
  field_simp

/-- **One-sided `O(√(n log n))` LIL for a `√i`-growing-increment martingale.** From the block
exceedance (`ae_eventually_lt_block_of_growing`) and the linear quadratic-variation bound
`⟨M⟩_n ≤ v·n`, almost surely `M_n ≤ C'√(n log n)` eventually. For each large `n`, take the least `j`
with `n ≤ 2^j` (so `2^j ≤ 2n` and `j ≤ log₂ n + 1`); then `⟨M⟩_n ≤ v·n ≤ v·2^j`, so the block bound
applies at `m = n`, giving `M_n < √(2^j j) ≤ C'√(n log n)`. The horizon restriction `m ≤ 2^j` yields
the `n`-scale (not the `⟨M⟩_n`-scale): time-blocking is what the growing increments permit. -/
lemma ae_eventually_le_sqrt_nat_mul_log_of_growing [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {a : ℝ} (ha : 0 < a) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ a * √i)
    {v : ℝ} (hv : 0 ≤ v) (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∃ C', ∀ᶠ n in atTop, M n ω ≤ C' * √((n : ℝ) * Real.log n) := by
  filter_upwards [ae_eventually_lt_block_of_growing hM hM0 ha hb v one_pos, hqv]
    with ω hgood hqvn
  rw [eventually_atTop] at hgood
  obtain ⟨j₀, hj₀⟩ := hgood
  refine ⟨√(2 * (1 / Real.log 2 + 1)), ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ j₀), eventually_ge_atTop 3] with n hn0 hn3
  have hnR3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn1 : (1 : ℝ) ≤ Real.log n :=
    (Real.le_log_iff_exp_le hnpos).mpr (le_trans Real.exp_one_lt_d9.le (by linarith))
  -- Least block `j` with `n ≤ 2^j` (`exists_pow_ge_le`).
  obtain ⟨j, hnleR, h2j, hjlog⟩ := exists_pow_ge_le one_lt_two (by linarith : (1 : ℝ) ≤ n)
  have hjle : n ≤ 2 ^ j := by exact_mod_cast hnleR
  have hjj0 : j₀ ≤ j := by
    have hcast : (2 : ℝ) ^ j₀ ≤ (2 : ℝ) ^ j := by exact_mod_cast le_trans hn0 hjle
    exact (pow_le_pow_iff_right₀ one_lt_two).mp hcast
  have hqvcond : predQuadVar M ℱ μ n ω ≤ v * (2 : ℝ) ^ j :=
    (hqvn n).trans (mul_le_mul_of_nonneg_left hnleR hv)
  have hMn : M n ω < 1 * √((2 : ℝ) ^ j * j) := hj₀ j hjj0 n hjle hqvcond
  rw [one_mul] at hMn
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
`M_n = O(√(n log n))` a.s. This is the reusable finite-variance rate used to control a martingale
with square-root-growing increments. -/
lemma ae_isBigO_sqrt_nat_mul_log_of_growing [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    {a : ℝ} (ha : 0 < a) (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ a * √i)
    {v : ℝ} (hv : 0 ≤ v) (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, (fun n ↦ M n ω) =O[atTop] fun n : ℕ ↦ √((n : ℝ) * Real.log n) := by
  filter_upwards [ae_exists_eventually_abs_le
    (ae_eventually_le_sqrt_nat_mul_log_of_growing hM hM0 ha hb hv hqv)
    (ae_eventually_le_sqrt_nat_mul_log_of_growing hM.neg (neg_ae_eq_zero hM0) ha
      (fun i ↦ (hb i).mono fun ω hω ↦ by rwa [abs_neg_increment]) hv
      (by simpa only [predQuadVar_neg] using hqv))
    (fun _ _ ↦ Real.sqrt_nonneg _)] with ω hω
  obtain ⟨C, hC⟩ := hω
  rw [Asymptotics.isBigO_iff]
  exact ⟨C, hC.mono fun n hn ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hn⟩

end AlphaRAR
