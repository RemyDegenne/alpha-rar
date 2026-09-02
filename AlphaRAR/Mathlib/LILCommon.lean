/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.QuadraticVariation
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Shared ingredients of the block arguments for the law of the iterated logarithm

Every law-of-the-iterated-logarithm proof in this project (`Freedman.lean`, `LIL.lean`,
`LILTruncation.lean`, `HartmanWintner.lean`) is a block argument with the same
skeleton: a per-block tail bound, a Borel–Cantelli step over the blocks, a repackaging of the block
index in terms of the level (or time) actually reached, a two-sided form obtained from `M` and
`-M`, and a `limsup` (or `∀ b > 1`) form. The parts of that skeleton that do not depend on the
block schedule are proved here, once.

## Main results

* `AlphaRAR.ae_eventually_notMem_of_eventually_le`: the Borel–Cantelli step from tail bounds that
  are available only for all large block indices.
* `AlphaRAR.ae_eventually_forall_lt_of_measure_le`,
  `AlphaRAR.ae_eventually_forall_le_lt_of_measure_le`: the same, unpacked for the block events
  `{∃ n, λ_k ≤ M_n ∧ A_n ≤ v_k}` (infinite horizon) and `{∃ m ≤ N_k, …}` (finite horizon).
* `AlphaRAR.exists_pow_ge_le`: the least geometric block `ρ^k` above a level `V` satisfies
  `ρ^k ≤ ρ V` and `k ≤ log V / log ρ + 1`.
* `AlphaRAR.log_add_two_le_add_loglog`: `log (k+2) ≤ log (1/log ρ + 1) + log log V` for such `k`,
  the additive form of the block-index cost that preserves the sharp constant.
* `AlphaRAR.abs_neg_increment`, `AlphaRAR.neg_ae_eq_zero`,
  `AlphaRAR.ae_exists_eventually_abs_le`, `AlphaRAR.ae_forall_one_lt_eventually_abs_le`: the
  two-sided bound from one-sided bounds for `M` and `-M`.
* `AlphaRAR.ae_forall_one_lt_eventually_le_of_forall_nat`: `∀ b > 1` from the countable family
  `b_m = 1 + 1/(m+1)`.
* `AlphaRAR.limsup_div_le_one_of_forall_one_lt`,
  `AlphaRAR.limsup_abs_div_le_one_of_forall_one_lt`: `limsup (f n / w n) ≤ 1` from
  `∀ b > 1, ∀ᶠ n, f n ≤ b w n`.
* `AlphaRAR.summable_exp_neg_mul_log_add`: the `p`-series `∑_k exp(-p log(k+2)) < ∞` for `1 < p`,
  the tail of every `log log` block schedule.
* `AlphaRAR.tendsto_add_two_div_pow`, `AlphaRAR.tendsto_log_add_two_div_pow`: `(k+2)/ρ^k → 0` and
  `log(k+2)/ρ^k → 0` for `ρ > 1`, the decay behind eventual admissibility;
  `AlphaRAR.tendsto_sqrt_loglog_div_nat`: `√(log log n / n) → 0`.
* `WithTop.untopA_coe`: `untopA` of a coercion, needed to read Mathlib's `stoppedProcess` at a
  constant time.
* `AlphaRAR.one_lt_log_three`, `AlphaRAR.loglog_pos_of_three_le`: the numeric facts behind the
  positivity of `log log x` for `x ≥ 3`.
-/

@[expose] public section

open MeasureTheory Filter Real

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### A `WithTop` coercion lemma

Mathlib's `stoppedProcess` reads the stopped time through `WithTop.untopA`; for a coercion this is
the element itself (the `WithTop` twin of `WithBot.unbotD_coe`, missing for `untopA`). -/

/-- `untopA` of a coercion is the element itself. -/
@[simp]
lemma _root_.WithTop.untopA_coe {α : Type*} [Nonempty α] (a : α) :
    (a : WithTop α).untopA = a :=
  rfl

/-- `untopA` of a natural number cast into `WithTop ℕ` (the cast is `Nat.cast`, not the `WithTop`
coercion, so this is the form that appears for constant stopping times). -/
@[simp]
lemma _root_.WithTop.untopA_natCast (n : ℕ) : (n : WithTop ℕ).untopA = n :=
  rfl

/-! ### Borel–Cantelli over a block schedule -/

/-- **Borel–Cantelli with eventual tail bounds.** If `μ (s k) ≤ f k` for all large `k`, where
`f ≥ 0` is summable, then almost surely only finitely many of the `s k` occur. On a finite measure
the finite prefix of blocks where no bound is available contributes finitely to `∑_k μ (s k)`. -/
lemma ae_eventually_notMem_of_eventually_le [IsFiniteMeasure μ] {s : ℕ → Set Ω} {f : ℕ → ℝ}
    (hsum : Summable f) (hf : ∀ k, 0 ≤ f k)
    (hle : ∀ᶠ k in atTop, μ (s k) ≤ ENNReal.ofReal (f k)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ s k := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hle
  refine ae_eventually_notMem ?_
  rw [← ENNReal.sum_add_tsum_compl (Finset.range k₀) fun k ↦ μ (s k)]
  refine ENNReal.add_ne_top.mpr
    ⟨(ENNReal.sum_lt_top.mpr fun k _ ↦ measure_lt_top μ (s k)).ne, ?_⟩
  have key : (∑' i : ↥((↑(Finset.range k₀) : Set ℕ)ᶜ), μ (s ↑i))
      ≤ ∑' k, ENNReal.ofReal (f k) := by
    refine le_trans (ENNReal.tsum_le_tsum fun i ↦ ?_)
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective _)
    obtain ⟨k, hk⟩ := i
    rw [Finset.coe_range, Set.mem_compl_iff, Set.mem_Iio, not_lt] at hk
    exact hk₀ k hk
  refine ne_top_of_le_ne_top ?_ key
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hsum]
  exact ENNReal.ofReal_ne_top

/-- **Block Borel–Cantelli, infinite horizon.** If the block events
`{∃ n, λ_k ≤ M_n ∧ A_n ≤ v_k}` have summable tail bounds for all large `k`, then almost surely,
for all large `k` and every `n`, `A_n ≤ v_k ⇒ M_n < λ_k`. In the applications `A` is the
predictable quadratic variation of `M`. -/
lemma ae_eventually_forall_lt_of_measure_le [IsFiniteMeasure μ] {M A : ℕ → Ω → ℝ}
    {t v f : ℕ → ℝ} (hsum : Summable f) (hf : ∀ k, 0 ≤ f k)
    (hle : ∀ᶠ k in atTop,
      μ {ω | ∃ n, t k ≤ M n ω ∧ A n ω ≤ v k} ≤ ENNReal.ofReal (f k)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ∀ n, A n ω ≤ v k → M n ω < t k := by
  filter_upwards [ae_eventually_notMem_of_eventually_le hsum hf hle] with ω hω
  filter_upwards [hω] with k hk
  simp only [not_exists, not_and] at hk
  intro n hn
  by_contra hcon
  exact hk n (not_lt.mp hcon) hn

/-- **Block Borel–Cantelli, finite horizons.** If the block events
`{∃ m ≤ N_k, λ_k ≤ M_m ∧ A_m ≤ v_k}` have summable tail bounds for all large `k`, then almost
surely, for all large `k` and every `m ≤ N_k`, `A_m ≤ v_k ⇒ M_m < λ_k`. -/
lemma ae_eventually_forall_le_lt_of_measure_le [IsFiniteMeasure μ] {M A : ℕ → Ω → ℝ}
    {N : ℕ → ℕ} {t v f : ℕ → ℝ} (hsum : Summable f) (hf : ∀ k, 0 ≤ f k)
    (hle : ∀ᶠ k in atTop,
      μ {ω | ∃ m ≤ N k, t k ≤ M m ω ∧ A m ω ≤ v k} ≤ ENNReal.ofReal (f k)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ∀ m ≤ N k, A m ω ≤ v k → M m ω < t k := by
  filter_upwards [ae_eventually_notMem_of_eventually_le hsum hf hle] with ω hω
  filter_upwards [hω] with k hk
  intro m hm hA
  by_contra hcon
  exact hk ⟨m, hm, not_lt.mp hcon, hA⟩

/-! ### The least geometric block above a level -/

/-- **Least geometric block above a level.** For `1 < ρ` and `1 ≤ V`, the least `k` with
`V ≤ ρ^k` satisfies `ρ^k ≤ ρ V` and `k ≤ log V / log ρ + 1`: the block containing `V` overshoots
it by at most a factor `ρ`, and its index is logarithmic in `V`. This is the deterministic core of
every repackaging of a block exceedance bound at the level (or time) actually reached. -/
lemma exists_pow_ge_le {ρ V : ℝ} (hρ : 1 < ρ) (hV : 1 ≤ V) :
    ∃ k : ℕ, V ≤ ρ ^ k ∧ ρ ^ k ≤ ρ * V ∧ (k : ℝ) ≤ log V / log ρ + 1 := by
  classical
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hlogρ : 0 < log ρ := log_pos hρ
  have hex : ∃ k : ℕ, V ≤ ρ ^ k :=
    ((tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_ge_atTop V).exists
  obtain ⟨k, hVk, hmin⟩ : ∃ k : ℕ, V ≤ ρ ^ k ∧ ∀ m, m < k → ρ ^ m < V :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ not_le.mp (Nat.find_min hex hm)⟩
  refine ⟨k, hVk, ?_, ?_⟩
  · obtain _ | m := k
    · rw [pow_zero]
      nlinarith [mul_nonneg (sub_nonneg.mpr hρ.le) (zero_le_one.trans hV)]
    · have hm := hmin m (Nat.lt_succ_self m)
      rw [pow_succ, mul_comm (ρ ^ m) ρ]
      exact mul_le_mul_of_nonneg_left hm.le hρ0.le
  · obtain _ | m := k
    · simp only [Nat.cast_zero]
      have := div_nonneg (log_nonneg hV) hlogρ.le
      linarith
    · have hm := hmin m (Nat.lt_succ_self m)
      have hmlog : (m : ℝ) * log ρ < log V := by
        rw [← log_pow]; exact log_lt_log (pow_pos hρ0 m) hm
      have : (m : ℝ) < log V / log ρ := by rw [lt_div_iff₀ hlogρ]; linarith
      push_cast; linarith

/-- **Additive cost of the block index on the `log log` scale.** If `k ≤ log V / log ρ + 1` (as for
the least block above `V`, `exists_pow_ge_le`) and `3 ≤ log V`, then
`log (k + 2) ≤ log (1 / log ρ + 1) + log (log V)`. The constant is additive, not multiplicative,
which is what lets the sharp LIL constant survive the repackaging. -/
lemma log_add_two_le_add_loglog {ρ V : ℝ} (hρ : 1 < ρ) {k : ℕ}
    (hk : (k : ℝ) ≤ log V / log ρ + 1) (hV : 3 ≤ log V) :
    log ((k : ℝ) + 2) ≤ log (1 / log ρ + 1) + log (log V) := by
  have hlogρ : 0 < log ρ := log_pos hρ
  have hlogVpos : 0 < log V := by linarith
  have hstep : (k : ℝ) + 2 ≤ (1 / log ρ + 1) * log V := by
    rw [add_mul, one_div, inv_mul_eq_div, one_mul]; linarith
  calc log ((k : ℝ) + 2)
      ≤ log ((1 / log ρ + 1) * log V) := log_le_log (by positivity) hstep
    _ = log (1 / log ρ + 1) + log (log V) := log_mul (by positivity) hlogVpos.ne'

/-! ### Two-sided bounds from `M` and `-M` -/

/-- The increments of `-M` have the same absolute value as those of `M`. -/
lemma abs_neg_increment (M : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) :
    |(-M) (i + 1) ω - (-M) i ω| = |M (i + 1) ω - M i ω| := by
  simp only [Pi.neg_apply]
  rw [neg_sub_neg, abs_sub_comm]

/-- `M 0 = 0` a.e. transfers to `-M`. -/
lemma neg_ae_eq_zero {M : ℕ → Ω → ℝ} (hM0 : M 0 =ᵐ[μ] 0) : (-M) 0 =ᵐ[μ] 0 := by
  filter_upwards [hM0] with ω hω
  simp only [Pi.neg_apply, Pi.zero_apply] at hω ⊢
  rw [hω, neg_zero]

/-- **Two-sided bound with a random constant.** If a.s. `M_n ≤ C₁ w_n` and `-M_n ≤ C₂ w_n`
eventually, with `w ≥ 0`, then a.s. `|M_n| ≤ max C₁ C₂ · w_n` eventually. -/
lemma ae_exists_eventually_abs_le {M w : ℕ → Ω → ℝ}
    (hpos : ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop, M n ω ≤ C * w n ω)
    (hneg : ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop, (-M) n ω ≤ C * w n ω) (hw : ∀ n ω, 0 ≤ w n ω) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop, |M n ω| ≤ C * w n ω := by
  filter_upwards [hpos, hneg] with ω hpω hnω
  obtain ⟨C₁, hC₁⟩ := hpω
  obtain ⟨C₂, hC₂⟩ := hnω
  refine ⟨max C₁ C₂, ?_⟩
  filter_upwards [hC₁, hC₂] with n h1 h2
  have hu : M n ω ≤ max C₁ C₂ * w n ω :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hw n ω))
  have hl : -M n ω ≤ max C₁ C₂ * w n ω :=
    h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hw n ω))
  rw [abs_le]
  exact ⟨by linarith, hu⟩

/-- **Two-sided bound with every constant `b > 1`.** If a.s. for every `b > 1` eventually
`M_n ≤ b w_n` and `-M_n ≤ b w_n`, then a.s. for every `b > 1` eventually `|M_n| ≤ b w_n`. -/
lemma ae_forall_one_lt_eventually_abs_le {M w : ℕ → Ω → ℝ}
    (hpos : ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, M n ω ≤ b * w n ω)
    (hneg : ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, (-M) n ω ≤ b * w n ω) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, |M n ω| ≤ b * w n ω := by
  filter_upwards [hpos, hneg] with ω hpω hnω b hb
  filter_upwards [hpω b hb, hnω b hb] with n h1 h2
  have hl : -M n ω ≤ b * w n ω := h2
  rw [abs_le]
  exact ⟨by linarith, h1⟩

/-- **From the countable family `b_m = 1 + 1/(m+1)` to every `b > 1`.** A bound holding a.s.
eventually for each `b_m` holds a.s. eventually for every `b > 1`, by countable intersection and
`b_m < b` for some `m`. -/
lemma ae_forall_one_lt_eventually_le_of_forall_nat {f w : ℕ → Ω → ℝ}
    (h : ∀ m : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, f n ω ≤ (1 + 1 / ((m : ℝ) + 1)) * w n ω)
    (hw : ∀ n ω, 0 ≤ w n ω) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, f n ω ≤ b * w n ω := by
  filter_upwards [ae_all_iff.mpr h] with ω hω b hb
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < b - 1 by linarith)
  filter_upwards [hω m] with n hn
  exact hn.trans (mul_le_mul_of_nonneg_right (by linarith) (hw n ω))

/-! ### `limsup` from eventual bounds -/

/-- **`limsup ≤ 1` from eventual bounds by every `b > 1`.** If `f n / w n` is cobounded below and
for every `b > 1` eventually `f n ≤ b w n` (with `w ≥ 0`), then `limsup (f n / w n) ≤ 1`. Where
`w n = 0` the quotient is `0`, which is harmless. -/
lemma limsup_div_le_one_of_forall_one_lt {f w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ f n / w n))
    (h : ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, f n ≤ b * w n) :
    limsup (fun n ↦ f n / w n) atTop ≤ 1 := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ limsup_le_of_le hcobdd ?_
  filter_upwards [h a ha] with n hn
  rcases (hw n).eq_or_lt with hs | hs
  · rw [← hs, div_zero]; exact zero_le_one.trans ha.le
  · rw [div_le_iff₀ hs]; exact hn

/-- **`limsup ≤ 1` for a nonnegative quotient.** The absolute-value form of
`limsup_div_le_one_of_forall_one_lt`: the quotient `|f n| / w n` is nonnegative, hence cobounded
below by `0`. -/
lemma limsup_abs_div_le_one_of_forall_one_lt {f w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (h : ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, |f n| ≤ b * w n) :
    limsup (fun n ↦ |f n| / w n) atTop ≤ 1 :=
  limsup_div_le_one_of_forall_one_lt hw
    (IsCoboundedUnder.of_frequently_ge (a := 0)
      (Eventually.of_forall fun n ↦ div_nonneg (abs_nonneg _) (hw n)).frequently) h

/-! ### Geometric decay of the block index -/

/-- `((k:ℝ)+2)/ρ^k → 0` for `ρ > 1`. -/
lemma tendsto_add_two_div_pow {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2) / ρ ^ k) atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ ↦ (k : ℝ) / ρ ^ k) atTop (𝓝 0) :=
    (isLittleO_coe_const_pow_of_one_lt (R := ℝ) hρ).tendsto_div_nhds_zero
  have hc : Tendsto (fun k : ℕ ↦ (2 : ℝ) / ρ ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hρ)
  have hsum := hk.add hc
  rw [add_zero] at hsum
  exact hsum.congr fun k ↦ (add_div _ _ _).symm

/-- `log((k:ℝ)+2)/ρ^k → 0` for `ρ > 1`: `log` grows slower than any geometric sequence. -/
lemma tendsto_log_add_two_div_pow {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun k : ℕ ↦ log ((k : ℝ) + 2) / ρ ^ k) atTop (𝓝 0) := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  refine squeeze_zero (fun k ↦ ?_) (fun k ↦ ?_) (tendsto_add_two_div_pow hρ)
  · exact div_nonneg (log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)) (by positivity)
  · gcongr
    exact (log_le_sub_one_of_pos (by positivity)).trans (by linarith)

/-- **`p`-series summability of the loglog block tails.**
For `1 < p`, `∑_k exp(-p · log(k+2)) < ∞`, because `exp(-p log(k+2)) = ((k+2)^p)⁻¹`, a convergent
`p`-series (Mathlib `Real.summable_nat_rpow_inv`). -/
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

/-! ### Numeric facts about `log 3` -/

/-- `1 < log 3`, since `e < 3`. -/
lemma one_lt_log_three : (1 : ℝ) < log 3 :=
  (lt_log_iff_exp_lt (by norm_num)).2 (lt_trans exp_one_lt_d9 (by norm_num))

/-- `log log x > 0` for `x ≥ 3`. -/
lemma loglog_pos_of_three_le {x : ℝ} (hx : 3 ≤ x) : 0 < log (log x) :=
  log_pos (one_lt_log_three.trans_le (log_le_log (by norm_num) hx))

/-- `log log j > 0` for a natural number `j ≥ 3`. -/
lemma loglog_pos_of_three_le_nat {j : ℕ} (hj : 3 ≤ j) : 0 < log (log (j : ℝ)) :=
  loglog_pos_of_three_le (by exact_mod_cast hj)

/-- `log log n / n → 0`, from `log x / x → 0` and `log log n ≤ log n`. -/
lemma tendsto_loglog_div_nat : Tendsto (fun n : ℕ ↦ log (log n) / n) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun x : ℝ ↦ log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h : Tendsto (fun n : ℕ ↦ log (n : ℝ) / n) atTop (𝓝 0) :=
    hlogdiv.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have := loglog_pos_of_three_le_nat hn
    positivity
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogpos : 0 < log (n : ℝ) := log_pos (by linarith)
    exact div_le_div_of_nonneg_right ((log_le_sub_one_of_pos hlogpos).trans (by linarith))
      (by linarith)

/-- `√(log log n / n) → 0`: the block condition of the sharp growing-increment LIL holds for
bounded increments. -/
lemma tendsto_sqrt_loglog_div_nat :
    Tendsto (fun n : ℕ ↦ √(log (log n) / n)) atTop (𝓝 0) := by
  have hcont : Tendsto (fun t : ℝ ↦ √t) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0)
  simpa [Function.comp_def] using hcont.comp tendsto_loglog_div_nat

end AlphaRAR
