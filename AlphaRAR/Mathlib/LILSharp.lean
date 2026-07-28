/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.LILLogLog
import LeanSpec

/-!
# The sharp-constant martingale law of the iterated logarithm

The `O`-rate engine of `LIL.lean`/`LILLogLog.lean` uses the crude one-step estimate
`eˣ ≤ 1 + x + x²`, whose variance proxy `2` inflates the LIL constant to `√2·(…)`. This file refines
the one-step estimate to the second-order bound `eˣ ≤ 1 + x + ½(1+δ)x²` (valid as the increment
`→ 0`), which propagates through the exponential supermartingale and Freedman inequality to yield
the sharp constant `limsup Mₙ/√(2⟨M⟩ₙ log log⟨M⟩ₙ) ≤ 1` (blueprint chapter `chap:pre_llil`, section
"The sharp constant").

## Main results (in progress)

* `AlphaRAR.exp_le_one_add_add_half_mul_sq`: the refined elementary inequality
  `eˣ ≤ 1 + x + ½(1+δ)x²` for `|x|` small (blueprint `lem:llil_refined_ineq`), from `Real.exp_bound`
  at `n = 3`.
* `AlphaRAR.condExp_exp_increment_le_refined`: the refined conditional MGF bound
  (blueprint `lem:llil_refined_mgf`), variance proxy `1+δ`.
* `AlphaRAR.supermartingale_expProcessRefined` and `AlphaRAR.measure_exists_ge_le_exp_refined`
  / `_optimized_refined` / `_all_refined`: the refined exponential supermartingale and Freedman
  bounds, exponent `-λ²/(2(1+δ)v)` (blueprint `lem:llil_refined_freedman`).
* `AlphaRAR.ae_eventually_forall_lt_of_summable_eventually_refined`: the refined
  eventual-admissibility Borel–Cantelli step.
* `AlphaRAR.ae_eventually_forall_lt_pow_loglog_sharp`: the sharp exceedance for bounded increments
  (blueprint `lem:llil_sharp_block`): `⟨M⟩_n ≤ ρ^k ⇒ M_n < √(2(1+ε)ρ^k log(k+2))` eventually.
* `AlphaRAR.ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp` / `_sharp'` / `_sharp_all`: the
  sharp normalized bound, repackaging least-`k` with the loglog bound kept additive; `_sharp_all`
  gives the one-sided `limsup ≤ 1` (`∀ b > 1, ∀ᶠ n, M_n ≤ b√(2⟨M⟩_n log log⟨M⟩_n)`).
* `AlphaRAR.ae_eventually_abs_le_sqrt_predQuadVar_mul_loglog_sharp`: the **sharp constant,
  two-sided** (blueprint `thm:llil_sharp`): a.s. for every `b > 1`, eventually
  `|M_n| ≤ b √(2 ⟨M⟩_n log log⟨M⟩_n)`.
* `AlphaRAR.ae_limsup_abs_div_sqrt_predQuadVar_mul_loglog_le_one`: the same in genuine `limsup`
  form, `limsup_n |M_n|/√(2 ⟨M⟩_n log log⟨M⟩_n) ≤ 1` a.s.
* `AlphaRAR.measure_exists_ge_le_exp_horizon_refined`,
  `AlphaRAR.measure_exists_ge_le_exp_block_loglog_sharp`,
  `AlphaRAR.ae_eventually_lt_block_of_growing_loglog_sharp`: refined per-block Freedman bounds for
  growing-increment martingales over an **arbitrary horizon sequence `N_j`** (with eventual
  admissibility), sharp exponent `(½(1+δ)α²v-αC)log(j+2)`. Instantiating `N_j = ⌈ρ^j⌉` with `ρ↓1`
  (rather than `2^j`) is what yields the sharp *constant* `1` in the repackaging — for a martingale
  with a linear quadratic-variation bound `⟨M⟩_n ≤ v·n` (e.g. the truncated low part), this needs a
  *deterministic* time horizon, no random stopping time.
* `AlphaRAR.ae_eventually_le_sqrt_nat_mul_loglog_of_growing_sharp`: the **sharp `√(2vn loglog n)`
  LIL for a growing-increment martingale with a linear QV bound** `⟨M⟩_n ≤ v·n`, from the above with
  `N_j = ⌈ρ^j⌉`, `ρ↓1`. The engine for the sharp low part of Hartman–Wintner — no random stopping.
* `AlphaRAR.exists_ceil_pow_horizon`: the geometric horizons `N_j = ⌈ρ^j⌉` and their properties.
* `AlphaRAR.ae_eventually_le_sqrt_nat_mul_loglog_of_growing_sharp'`: the single-constant wrapper,
  hiding the `C, α` choice — takes only `ρ, δ, b` with `(1+δ)ρ < b²`, and the martingale data.
* `AlphaRAR.tendsto_growth_horizon`: the base-independent condition (H). From `g` with
  `g n √(loglog n/n) → 0` it derives, for the geometric horizons `N_j` with `ρ^j ≤ N_j`, the block
  condition `g(N_j) √(log(j+2)/N_j) → 0` (via `log(j+2) ≤ (log K+1)·loglog N_j`, `K = 1/log ρ + 2`).
* `AlphaRAR.ae_eventually_le_sqrt_nat_mul_loglog_of_growth_sharp_all` / `_abs_..._growth_sharp_all`:
  the **`b > 1` limit** of the growing sharp LIL (one- and two-sided): for a martingale with
  base-independent increment growth `|ΔM_i| ≤ g(i)` (`g` monotone, `g n √(loglog n/n) → 0`) and
  `⟨M⟩_n ≤ v·n`, a.s. `∀ b > 1, ∀ᶠ n, |M_n| ≤ b √(2 v n loglog n)`. For each `b` we block with base
  `ρ = 1 + (b-1)/2 ↓ 1`; condition (H) comes from `tendsto_growth_horizon`.
* `AlphaRAR.ae_limsup_abs_div_sqrt_nat_mul_loglog_of_growth_le_one`: the same in genuine `limsup`
  form, `limsup_n |M_n|/√(2 v n log log n) ≤ 1` a.s. The sharp constant `1` for the low part.
-/

open MeasureTheory Filter Real

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {M : ℕ → Ω → ℝ}

/-- **Refined elementary inequality** (blueprint `lem:llil_refined_ineq`). For every `δ > 0` there
is `η > 0` such that `eˣ ≤ 1 + x + ½(1+δ)x²` for all `|x| ≤ η`. Mathlib's `Real.exp_bound` at
`n = 3` gives `|eˣ - (1 + x + ½x²)| ≤ (2/9)|x|³`, hence
`eˣ ≤ 1 + x + ½x² + (2/9)|x|³ ≤ 1 + x + ½(1 + (4/9)|x|)x²`; take `η = min(1, (9/4)δ)`. This is the
one-step estimate whose variance proxy `1+δ → 1` gives the sharp LIL constant. -/
lemma exp_le_one_add_add_half_mul_sq {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2 := by
  refine ⟨min 1 (9 / 4 * δ), lt_min one_pos (by positivity), fun x hx ↦ ?_⟩
  have hx1 : |x| ≤ 1 := hx.trans (min_le_left _ _)
  have hxδ : |x| ≤ 9 / 4 * δ := hx.trans (min_le_right _ _)
  have hb := Real.exp_bound hx1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  have habs3 : |x| ^ 3 = |x| * x ^ 2 := by rw [← sq_abs x]; ring
  have hstep : |x| ^ 3 * (2 / 9) ≤ δ / 2 * x ^ 2 := by
    rw [habs3]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxδ) (sq_nonneg x)]
  rw [show (1 + δ) / 2 * x ^ 2 = x ^ 2 / 2 + δ / 2 * x ^ 2 from by ring]
  linarith [le_of_abs_le hb, hstep]

/-- **Refined conditional MGF bound** (blueprint `lem:llil_refined_mgf`). If `|ΔM_i| ≤ c` a.e. and
`|θ| c ≤ η`, where `η` is admissible for the refined inequality at level `δ`
(`hη`, e.g. from `exp_le_one_add_add_half_mul_sq`), then
`μ[exp(θ ΔM_i) | ℱ_i] ≤ 1 + ½(1+δ)θ²(⟨M⟩_{i+1} - ⟨M⟩_i)` a.e. Same proof as the crude
`condExp_exp_increment_le`, with the refined one-step estimate in place of `eˣ ≤ 1 + x + x²`
(variance proxy `1+δ` instead of `2`). -/
lemma condExp_exp_increment_le_refined [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    {c θ δ η : ℝ} (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hθ : |θ| * c ≤ η) (i : ℕ) (hb : ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hd2 : Integrable (fun ω ↦ (M (i + 1) ω - M i ω) ^ 2) μ)
    (hprod : Integrable (M i * (M (i + 1) - M i)) μ) :
    μ[fun ω ↦ exp (θ * (M (i + 1) ω - M i ω)) | ℱ i]
      ≤ᵐ[μ] fun ω ↦ 1 + (1 + δ) / 2 * θ ^ 2
        * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
  have haesm_d : AEStronglyMeasurable (fun ω ↦ M (i + 1) ω - M i ω) μ :=
    (((hM.stronglyMeasurable (i + 1)).mono (ℱ.le _)).sub
      ((hM.stronglyMeasurable i).mono (ℱ.le _))).aestronglyMeasurable
  -- Pointwise refined bound `exp(θ ΔM) ≤ 1 + θ ΔM + ½(1+δ)θ² ΔM²`.
  have hptwise : (fun ω ↦ exp (θ * (M (i + 1) ω - M i ω)))
      ≤ᵐ[μ] fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
        + (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 := by
    filter_upwards [hb] with ω hbω
    have hx : |θ * (M (i + 1) ω - M i ω)| ≤ η := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
    nlinarith [hη _ hx]
  -- The quadratic bound and the exponential are integrable.
  have hint_exp : Integrable (fun ω ↦ exp (θ * (M (i + 1) ω - M i ω))) μ := by
    refine (MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
      (haesm_d.const_mul θ)) (exp η) ?_).integrable le_rfl
    filter_upwards [hb] with ω hbω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
  have hint_lin : Integrable (fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω)) μ :=
    (integrable_const 1).add (((hM.integrable (i + 1)).sub (hM.integrable i)).const_mul θ)
  have hint_quad : Integrable (fun ω ↦ (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2) μ :=
    hd2.const_mul _
  have hint_q : Integrable (fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
      + (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2) μ := hint_lin.add hint_quad
  -- Conditional expectation of the increment is `0`.
  have hd0 : μ[fun ω ↦ M (i + 1) ω - M i ω | ℱ i] =ᵐ[μ] 0 := by
    have h3 : μ[M i | ℱ i] = M i :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hM.stronglyMeasurable i) (hM.integrable i)
    have h1 : μ[fun ω ↦ M (i + 1) ω - M i ω | ℱ i] =ᵐ[μ] μ[M (i + 1) | ℱ i] - μ[M i | ℱ i] :=
      condExp_sub (hM.integrable (i + 1)) (hM.integrable i) _
    rw [h3] at h1
    have h2 : μ[M (i + 1) | ℱ i] =ᵐ[μ] M i := hM.condExp_ae_eq (Nat.le_succ i)
    filter_upwards [h1, h2] with ω e1 e2
    simp only [Pi.sub_apply, Pi.zero_apply, e1, e2, sub_self]
  -- Conditional expectation of the squared increment is `⟨M⟩_{i+1} - ⟨M⟩_i`.
  have hd2eq : μ[fun ω ↦ (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
      =ᵐ[μ] fun ω ↦ predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω :=
    (predQuadVar_succ_sub_eq hM i hd2 hprod).symm
  -- Conditional expectation of the quadratic bound.
  have hcond_q : μ[fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
      + (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
      =ᵐ[μ] fun ω ↦ 1 + (1 + δ) / 2 * θ ^ 2
        * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
    have hlin : μ[fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω) | ℱ i] =ᵐ[μ] fun _ ↦ 1 := by
      have hs : μ[fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω) | ℱ i]
          =ᵐ[μ] μ[fun _ ↦ (1 : ℝ) | ℱ i]
            + μ[fun ω ↦ θ * (M (i + 1) ω - M i ω) | ℱ i] :=
        condExp_add (integrable_const 1)
          (((hM.integrable (i + 1)).sub (hM.integrable i)).const_mul θ) _
      rw [condExp_const (ℱ.le i)] at hs
      have hsmul : μ[fun ω ↦ θ * (M (i + 1) ω - M i ω) | ℱ i]
          =ᵐ[μ] θ • μ[fun ω ↦ M (i + 1) ω - M i ω | ℱ i] := condExp_smul θ _ _
      filter_upwards [hs, hsmul, hd0] with ω es esm ed0
      simp only [es, Pi.add_apply, esm, Pi.smul_apply, ed0, Pi.zero_apply, smul_zero, add_zero]
    have hquad : μ[fun ω ↦ (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
        =ᵐ[μ] fun ω ↦ (1 + δ) / 2 * θ ^ 2
          * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω) := by
      have hsmul : μ[fun ω ↦ (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
          =ᵐ[μ] ((1 + δ) / 2 * θ ^ 2) • μ[fun ω ↦ (M (i + 1) ω - M i ω) ^ 2 | ℱ i] :=
        condExp_smul ((1 + δ) / 2 * θ ^ 2) _ _
      filter_upwards [hsmul, hd2eq] with ω esm ed2
      rw [esm, Pi.smul_apply, ed2, smul_eq_mul]
    have hadd : μ[fun ω ↦ 1 + θ * (M (i + 1) ω - M i ω)
        + (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i]
        =ᵐ[μ] μ[fun ω ↦ (1 : ℝ) + θ * (M (i + 1) ω - M i ω) | ℱ i]
          + μ[fun ω ↦ (1 + δ) / 2 * θ ^ 2 * (M (i + 1) ω - M i ω) ^ 2 | ℱ i] :=
      condExp_add hint_lin hint_quad _
    filter_upwards [hadd, hlin, hquad] with ω ea el eq
    rw [ea, Pi.add_apply, el, eq]
  exact (condExp_mono hint_exp hint_q hptwise).trans hcond_q.le

/-- The **refined exponential process** `Z_n(θ) = exp(θ M_n - ½(1+δ)θ² ⟨M⟩_n)`
(blueprint `lem:llil_refined_freedman`), the sharp-constant analogue of `expProcess`. -/
noncomputable def expProcessRefined (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    (δ θ : ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦ exp (θ * M n ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ n ω)

/-- **The refined exponential process is a supermartingale**
(blueprint `lem:llil_refined_freedman`).
Same proof as `supermartingale_expProcess`, with the refined MGF bound
`condExp_exp_increment_le_refined` (variance proxy `1+δ`) in place of the crude one, so the exponent
carries `½(1+δ)θ²⟨M⟩` instead of `θ²⟨M⟩`. -/
@[specifies expProcessRefined "the reason for the refined `½(1+δ)` coefficient: it is the smallest \
compensator that still yields a supermartingale under the sharpened MGF bound, and shrinking it \
towards the Gaussian `½` is exactly what buys the sharp LIL constant"]
lemma supermartingale_expProcessRefined [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c θ δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2) (hθ : |θ| * c ≤ η)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    Supermartingale (expProcessRefined M ℱ μ δ θ) ℱ μ := by
  classical
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  have haesm_d : ∀ i, AEStronglyMeasurable (fun ω ↦ M (i + 1) ω - M i ω) μ := fun i ↦
    (((hM.stronglyMeasurable (i + 1)).mono (ℱ.le _)).sub
      ((hM.stronglyMeasurable i).mono (ℱ.le _))).aestronglyMeasurable
  have hdmem : ∀ i, MemLp (fun ω ↦ M (i + 1) ω - M i ω) 2 μ := fun i ↦
    MemLp.of_bound (haesm_d i) c (by filter_upwards [hb i] with ω h; rwa [Real.norm_eq_abs])
  have hMmem : ∀ n, MemLp (M n) 2 μ := fun n ↦
    (memLp_two_iff_integrable_sq ((hM.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable).mpr
      (hM2 n)
  have hd2 : ∀ i, Integrable (fun ω ↦ (M (i + 1) ω - M i ω) ^ 2) μ :=
    fun i ↦ (hdmem i).integrable_sq
  have hprod : ∀ i, Integrable (M i * (M (i + 1) - M i)) μ := fun i ↦
    (hMmem i).integrable_mul ((hMmem (i + 1)).sub (hMmem i))
  have hMn : ∀ n, ∀ᵐ ω ∂μ, |M n ω| ≤ n * c := by
    intro n
    filter_upwards [ae_all_iff.mpr hb, hM0] with ω hball h0
    simp only [Pi.zero_apply] at h0
    have htel : (∑ j ∈ Finset.range n, (M (j + 1) ω - M j ω)) = M n ω := by
      rw [Finset.sum_range_sub (fun j ↦ M j ω) n, h0, sub_zero]
    rw [← htel]
    calc |∑ j ∈ Finset.range n, (M (j + 1) ω - M j ω)|
        ≤ ∑ j ∈ Finset.range n, |M (j + 1) ω - M j ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, c := Finset.sum_le_sum fun j _ ↦ hball j
      _ = n * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hinner : ∀ n, StronglyMeasurable[ℱ n]
      (fun ω ↦ θ * M n ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ n ω) := fun n ↦
    ((hM.stronglyMeasurable n).const_mul θ).sub
      ((stronglyAdapted_predictablePart' (f := fun k ↦ M k ^ 2) n).const_mul ((1 + δ) / 2 * θ ^ 2))
  have hZaesm : ∀ n, AEStronglyMeasurable (expProcessRefined M ℱ μ δ θ n) μ := fun n ↦
    ((Real.continuous_exp.comp_stronglyMeasurable (hinner n)).mono (ℱ.le n)).aestronglyMeasurable
  have hZbd : ∀ n, ∀ᵐ ω ∂μ, ‖expProcessRefined M ℱ μ δ θ n ω‖ ≤ Real.exp (|θ| * (n * c)) := by
    intro n
    filter_upwards [hMn n, predQuadVar_nonneg hM hd2 hprod n] with ω hMnω hqvω
    change ‖Real.exp (θ * M n ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ n ω)‖ ≤ _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    simp only [Pi.zero_apply] at hqvω
    have h1 : θ * M n ω ≤ |θ| * (n * c) := by
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hMnω (abs_nonneg _)
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (1 + δ) / 2 by linarith) (sq_nonneg θ)) hqvω]
  have hZint_n : ∀ n, Integrable (expProcessRefined M ℱ μ δ θ n) μ := fun n ↦
    (MemLp.of_bound (hZaesm n) _ (hZbd n)).integrable le_rfl
  refine supermartingale_nat (fun n ↦ Real.continuous_exp.comp_stronglyMeasurable (hinner n))
    hZint_n (fun i ↦ ?_)
  · have hfac_meas : StronglyMeasurable[ℱ i]
        (fun ω ↦ Real.exp (θ * M i ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ i ω)
          * Real.exp (-((1 + δ) / 2 * θ ^ 2
            * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)))) :=
      (Real.continuous_exp.comp_stronglyMeasurable (hinner i)).mul
        (Real.continuous_exp.comp_stronglyMeasurable
          (((stronglyAdapted_predictablePart (f := fun k ↦ M k ^ 2) i).sub
            (stronglyAdapted_predictablePart' (f := fun k ↦ M k ^ 2) i)).const_mul
              ((1 + δ) / 2 * θ ^ 2)).neg)
    set factor := fun ω ↦ Real.exp (θ * M i ω - (1 + δ) / 2 * θ ^ 2 * predQuadVar M ℱ μ i ω)
      * Real.exp (-((1 + δ) / 2 * θ ^ 2
        * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω))) with hfac
    have hZfac : expProcessRefined M ℱ μ δ θ (i + 1)
        = fun ω ↦ factor ω * Real.exp (θ * (M (i + 1) ω - M i ω)) := by
      funext ω
      simp only [expProcessRefined, hfac, ← Real.exp_add]
      congr 1
      ring
    have hint_exp : Integrable (fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω))) μ := by
      refine (MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
        ((haesm_d i).const_mul θ)) (exp η) ?_).integrable le_rfl
      filter_upwards [hb i] with ω hbω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hbω (abs_nonneg _)) hθ
    have hZint : Integrable (fun ω ↦ factor ω * Real.exp (θ * (M (i + 1) ω - M i ω))) μ := by
      rw [← hZfac]; exact hZint_n (i + 1)
    have hpull : μ[expProcessRefined M ℱ μ δ θ (i + 1) | ℱ i]
        =ᵐ[μ] fun ω ↦ factor ω * μ[fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω)) | ℱ i] ω := by
      rw [hZfac]
      exact condExp_mul_of_stronglyMeasurable_left hfac_meas hZint hint_exp
    have hmgf := condExp_exp_increment_le_refined hM hη hθ i (hb i) (hd2 i) (hprod i)
    have hfac_nonneg : ∀ ω, 0 ≤ factor ω := fun ω ↦ by
      rw [hfac]; positivity
    filter_upwards [hpull, hmgf] with ω hp hm
    rw [hp]
    calc factor ω * μ[fun ω ↦ Real.exp (θ * (M (i + 1) ω - M i ω)) | ℱ i] ω
        ≤ factor ω * (1 + (1 + δ) / 2 * θ ^ 2
            * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)) :=
          mul_le_mul_of_nonneg_left hm (hfac_nonneg ω)
      _ ≤ factor ω * Real.exp ((1 + δ) / 2 * θ ^ 2
          * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hfac_nonneg ω)
          have hle := Real.add_one_le_exp ((1 + δ) / 2 * θ ^ 2
            * (predQuadVar M ℱ μ (i + 1) ω - predQuadVar M ℱ μ i ω))
          linarith
      _ = expProcessRefined M ℱ μ δ θ i ω := by
          simp only [expProcessRefined, hfac, ← Real.exp_add]
          congr 1
          ring

/-- **Refined Freedman-type inequality** (blueprint `lem:llil_refined_freedman`, pre-optimization).
The sharp-constant analogue of `measure_exists_ge_le_exp`, with variance proxy `(1+δ)v` in place of
`2v`: `μ{∃ k ≤ n, λ ≤ M_k, ⟨M⟩_k ≤ v} ≤ exp(-θλ + ½(1+δ)θ²v)`, via Ville's inequality on the refined
supermartingale `expProcessRefined`. -/
lemma measure_exists_ge_le_exp_refined [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c θ δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2) (hθc : |θ| * c ≤ η) (hθ0 : 0 < θ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) (lam v : ℝ) (n : ℕ) :
    μ {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (exp (-θ * lam + (1 + δ) / 2 * θ ^ 2 * v)) := by
  classical
  set Z := expProcessRefined M ℱ μ δ θ with hZdef
  have hZ_super : Supermartingale Z ℱ μ :=
    supermartingale_expProcessRefined hM hM0 hM2 hδ hη hθc hb
  have hZ_nonneg : (0 : ℕ → Ω → ℝ) ≤ Z := fun k ω ↦ (Real.exp_pos _).le
  set a := exp (θ * lam - (1 + δ) / 2 * θ ^ 2 * v) with hadef
  have ha_pos : 0 < a := Real.exp_pos _
  have hZ0 : ∫ ω, Z 0 ω ∂μ = 1 := by
    have hae : (fun ω ↦ Z 0 ω) =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
      filter_upwards [hM0] with ω h0
      simp only [Pi.zero_apply] at h0
      simp [hZdef, expProcessRefined, predQuadVar_zero, h0]
    rw [integral_congr_ae hae]; simp
  have hsubset : {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ⊆ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω} := by
    intro ω hω
    obtain ⟨k, hk, hMk, hqvk⟩ := hω
    have hZk : a ≤ Z k ω := by
      rw [hadef, hZdef]
      simp only [expProcessRefined]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_le_mul_of_nonneg_left hMk hθ0.le,
        mul_le_mul_of_nonneg_left hqvk
          (mul_nonneg (show (0 : ℝ) ≤ (1 + δ) / 2 by linarith) (sq_nonneg θ))]
    exact le_trans hZk (Finset.le_sup' (fun j ↦ Z j ω) (Finset.mem_range.mpr (by omega)))
  have hville := smul_measure_sup_le_integral_zero hZ_super hZ_nonneg (ε := a.toNNReal) n
  rw [hZ0, ENNReal.ofReal_one, ENNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal a ha_pos.le] at hville
  have hmul : μ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω}
      * ENNReal.ofReal a ≤ 1 := by
    rw [mul_comm]; exact hville
  calc μ {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ μ {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ Z k ω} :=
        measure_mono hsubset
    _ ≤ (ENNReal.ofReal a)⁻¹ := ENNReal.le_inv_iff_mul_le.mpr hmul
    _ = ENNReal.ofReal (exp (-θ * lam + (1 + δ) / 2 * θ ^ 2 * v)) := by
        have hexp : exp (-θ * lam + (1 + δ) / 2 * θ ^ 2 * v) = a⁻¹ := by
          rw [hadef, ← Real.exp_neg]; congr 1; ring
        rw [hexp, ENNReal.ofReal_inv_of_pos ha_pos]

/-- **Refined Freedman with the optimal `θ = λ/((1+δ)v)`** (finite horizon, blueprint
`lem:llil_refined_freedman`). At the optimizer the exponent is the sharp `-λ²/(2(1+δ)v)`; the
admissibility `θ c ≤ η` reads `λ c ≤ (1+δ) v η`. -/
lemma measure_exists_ge_le_exp_optimized_refined [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {lam v : ℝ} (hlam : 0 < lam) (hv : 0 < v)
    (hadm : lam * c ≤ (1 + δ) * v * η) (n : ℕ) :
    μ {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (exp (-lam ^ 2 / (2 * (1 + δ) * v))) := by
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  set θ := lam / ((1 + δ) * v) with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθc : |θ| * c ≤ η := by
    rw [abs_of_pos hθ0, hθdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hadm]
  have h := measure_exists_ge_le_exp_refined hM hM0 hM2 hδ hη hθc hθ0 hb lam v n
  have hexp : -θ * lam + (1 + δ) / 2 * θ ^ 2 * v = -lam ^ 2 / (2 * (1 + δ) * v) := by
    have hne : ((1 + δ) * v) ≠ 0 := by positivity
    rw [hθdef]; field_simp; ring
  rwa [hexp] at h

/-- **Refined Freedman with the optimal `θ`, infinite horizon** (sharp analogue of
`measure_exists_ge_le_exp_all`). Taking `n → ∞` over the increasing events. -/
lemma measure_exists_ge_le_exp_all_refined [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {lam v : ℝ} (hlam : 0 < lam) (hv : 0 < v)
    (hadm : lam * c ≤ (1 + δ) * v * η) :
    μ {ω | ∃ k, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v}
      ≤ ENNReal.ofReal (exp (-lam ^ 2 / (2 * (1 + δ) * v))) := by
  set A : ℕ → Set Ω := fun n ↦ {ω | ∃ k ≤ n, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v} with hA
  have hmono : Monotone A := fun a b hab ω ⟨k, hk, h⟩ ↦ ⟨k, hk.trans hab, h⟩
  have hUnion : (⋃ n, A n) = {ω | ∃ k, lam ≤ M k ω ∧ predQuadVar M ℱ μ k ω ≤ v} := by
    ext ω
    simp only [hA, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, k, _, h⟩ ↦ ⟨k, h⟩, fun ⟨k, h⟩ ↦ ⟨k, k, le_rfl, h⟩⟩
  rw [← hUnion, hmono.measure_iUnion]
  exact iSup_le fun n ↦
    measure_exists_ge_le_exp_optimized_refined hM hM0 hM2 hδ hη hb hlam hv hadm n

/-- **Refined Borel–Cantelli with eventual admissibility** (blueprint `lem:llil_evt_adm`, sharp
version). The sharp analogue of `ae_eventually_forall_lt_of_summable_eventually`: with the refined
Freedman bounds `exp(-λ_k²/(2(1+δ)v_k))` summable and admissibility `λ_k c ≤ (1+δ)v_k η` holding
eventually, almost surely for all large `k` and every `n`, `⟨M⟩_n ≤ v_k ⇒ M_n < λ_k`. -/
lemma ae_eventually_forall_lt_of_summable_eventually_refined [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c δ η : ℝ} (hδ : 0 ≤ δ) (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {lam v : ℕ → ℝ}
    (hadm : ∀ᶠ k in atTop, 0 < lam k ∧ 0 < v k ∧ lam k * c ≤ (1 + δ) * v k * η)
    (hsum : Summable fun k ↦ exp (-lam k ^ 2 / (2 * (1 + δ) * v k))) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ∀ n, predQuadVar M ℱ μ n ω ≤ v k → M n ω < lam k := by
  set s : ℕ → Set Ω := fun k ↦ {ω | ∃ n, lam k ≤ M n ω ∧ predQuadVar M ℱ μ n ω ≤ v k} with hs_def
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hadm
  have hfin : (∑' k, μ (s k)) ≠ ∞ := by
    rw [← ENNReal.sum_add_tsum_compl (Finset.range k₀) fun k ↦ μ (s k)]
    refine ENNReal.add_ne_top.mpr
      ⟨(ENNReal.sum_lt_top.mpr fun k _ ↦ measure_lt_top μ (s k)).ne, ?_⟩
    have key : (∑' i : ↥((↑(Finset.range k₀) : Set ℕ)ᶜ), μ (s ↑i))
        ≤ ∑' k, ENNReal.ofReal (exp (-lam k ^ 2 / (2 * (1 + δ) * v k))) := by
      refine le_trans (ENNReal.tsum_le_tsum fun i ↦ ?_)
        (ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective _)
      obtain ⟨k, hk⟩ := i
      rw [Finset.coe_range, Set.mem_compl_iff, Set.mem_Iio, not_lt] at hk
      obtain ⟨hlk, hvk, hak⟩ := hk₀ k hk
      exact measure_exists_ge_le_exp_all_refined hM hM0 hM2 hδ hη hb hlk hvk hak
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

/-- `((k:ℝ)+2)/ρ^k → 0` for `ρ > 1` (the base-`ρ` analogue of the `2^k` decay). -/
lemma tendsto_add_two_div_pow {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2) / ρ ^ k) atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ ↦ (k : ℝ) / ρ ^ k) atTop (𝓝 0) :=
    (isLittleO_coe_const_pow_of_one_lt (R := ℝ) hρ).tendsto_div_nhds_zero
  have hc : Tendsto (fun k : ℕ ↦ (2 : ℝ) / ρ ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hρ)
  have hsum := hk.add hc
  rw [add_zero] at hsum
  exact hsum.congr fun k ↦ (add_div _ _ _).symm

/-- `log((k:ℝ)+2)/ρ^k → 0` for `ρ > 1`: `log` grows slower than any base-`ρ` geometric. -/
lemma tendsto_log_add_two_div_pow {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun k : ℕ ↦ log ((k : ℝ) + 2) / ρ ^ k) atTop (𝓝 0) := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  refine squeeze_zero (fun k ↦ ?_) (fun k ↦ ?_) (tendsto_add_two_div_pow hρ)
  · exact div_nonneg (log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)) (by positivity)
  · gcongr
    exact (log_le_sub_one_of_pos (by positivity)).trans (by linarith)

/-- **Sharp exceedance for bounded increments** (blueprint `lem:llil_sharp_block`). With blocks
`v_k = ρ^k` and sharp thresholds `λ_k = √(2(1+ε)ρ^k log(k+2))` (using `log(k+2) ≍ loglog ρ^k`),
almost surely for all large `k` and every `n`, `⟨M⟩_n ≤ ρ^k ⇒ M_n < √(2(1+ε)ρ^k log(k+2))`. The
refined Freedman tail is `exp(-((1+ε)/(1+δ)) log(k+2))`, a `p`-series with `p = (1+ε)/(1+δ) > 1`
(`summable_exp_neg_mul_log_add`); admissibility `λ_k c ≤ (1+δ)ρ^k η_δ` holds eventually since
`log(k+2)/ρ^k → 0`. -/
theorem ae_eventually_forall_lt_pow_loglog_sharp [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) {ρ ε δ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ)
    (hεδ : δ < ε) :
    ∀ᵐ ω ∂μ, ∀ᶠ (k : ℕ) in atTop, ∀ n, predQuadVar M ℱ μ n ω ≤ ρ ^ k →
      M n ω < √(2 * (1 + ε) * ρ ^ k * log ((k : ℝ) + 2)) := by
  obtain ⟨η, hη0, hη⟩ := exp_le_one_add_add_half_mul_sq hδ
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
  filter_upwards [ae_eventually_forall_lt_of_summable_eventually_refined hM hM0 hM2 hδ.le hη hb
    (v := fun k ↦ ρ ^ k) hadm hsum] with ω hω using hω

/-- **Sharp normalized bound for fixed block base** (blueprint `lem:llil_sharp_block` repackaged).
For bounded increments with `⟨M⟩_n → ∞`, if `b² > (1+ε)ρ` then almost surely eventually
`M_n ≤ b √(2 ⟨M⟩_n log log⟨M⟩_n)`. Repackaging the sharp block via the least `k` with `⟨M⟩_n ≤ ρ^k`:
`ρ^k ≤ ρ⟨M⟩_n` and, crucially, the loglog bound is kept **additive**,
`log(k+2) ≤ D_ρ + log log⟨M⟩_n` (with `D_ρ = log(1/log ρ + 1)`), so no constant `> 1` multiplies the
leading term; the additive `D_ρ` is absorbed since `log log⟨M⟩_n → ∞`. Taking `ρ ↓ 1`, `ε ↓ 0`,
`b ↓ 1` gives the sharp constant `limsup ≤ 1`. -/
lemma ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop)
    {ρ ε δ b : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ) (hεδ : δ < ε) (hb0 : 0 < b)
    (hbA : (1 + ε) * ρ < b ^ 2) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, M n ω ≤ b * √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω))) := by
  have hlogρ : (0 : ℝ) < log ρ := log_pos hρ
  have hε0 : (0 : ℝ) < 1 + ε := by linarith
  have hApos : (0 : ℝ) < (1 + ε) * ρ := by positivity
  have hbApos : (0 : ℝ) < b ^ 2 - (1 + ε) * ρ := by linarith
  set Dρ : ℝ := log (1 / log ρ + 1) with hDρ_def
  set T : ℝ := (1 + ε) * ρ * Dρ / (b ^ 2 - (1 + ε) * ρ) with hT_def
  filter_upwards [ae_eventually_forall_lt_pow_loglog_sharp hM hM0 hM2 hc hbd hρ hδ hεδ, hV]
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
  -- Least block `k` with `V ≤ ρ^k`.
  obtain ⟨k, hVle, hkmin⟩ : ∃ k : ℕ, V ≤ ρ ^ k ∧ ∀ m, m < k → ¬ V ≤ ρ ^ m := by
    have hex : ∃ k : ℕ, V ≤ ρ ^ k :=
      ((tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_ge_atTop V).exists
    exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
  have hkk0 : k₀ ≤ k := (pow_le_pow_iff_right₀ hρ).mp (le_trans hn0 hVle)
  have hρk : ρ ^ k ≤ ρ * V := by
    obtain _ | m := k
    · rw [pow_zero]; nlinarith [hV1, hρ]
    · have hm : ¬ V ≤ ρ ^ m := hkmin m (Nat.lt_succ_self m)
      rw [not_le] at hm; rw [pow_succ, mul_comm (ρ ^ m) ρ]
      exact mul_le_mul_of_nonneg_left hm.le (by linarith)
  have hk1 : (k : ℝ) + 2 ≤ log V / log ρ + 3 := by
    obtain _ | m := k
    · simp only [Nat.cast_zero]; have := div_nonneg hlogVpos.le hlogρ.le; linarith
    · have hm : ¬ V ≤ ρ ^ m := hkmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmlog : (m : ℝ) * log ρ < log V := by
        rw [← log_pow]; exact log_lt_log (by positivity) hm
      have : (m : ℝ) < log V / log ρ := by rw [lt_div_iff₀ hlogρ]; linarith
      push_cast; linarith
  have hlogk2 : log ((k : ℝ) + 2) ≤ Dρ + log (log V) := by
    have hstep1 : (k : ℝ) + 2 ≤ (1 / log ρ + 1) * log V := by
      have hb2 : log V / log ρ + 3 ≤ (1 / log ρ + 1) * log V := by
        rw [add_mul, one_div, inv_mul_eq_div, one_mul]; linarith
      linarith
    calc log ((k : ℝ) + 2)
        ≤ log ((1 / log ρ + 1) * log V) := log_le_log (by positivity) hstep1
      _ = log (1 / log ρ + 1) + log (log V) :=
          log_mul (show (0 : ℝ) < 1 / log ρ + 1 by positivity).ne' hlogVpos.ne'
      _ = Dρ + log (log V) := by rw [hDρ_def]
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

/-- **Sharp normalized bound, any constant `> 1`.** For bounded increments with `⟨M⟩_n → ∞`, for
every `b > 1` almost surely eventually `M_n ≤ b √(2 ⟨M⟩_n log log⟨M⟩_n)`. Instantiates
`ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp` with `ρ = 1+t`, `ε = t`, `δ = t/2` for
`t = min((b²-1)/4, 1) > 0`, which satisfies `(1+ε)ρ < b²`. -/
lemma ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp' [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) {b : ℝ} (hb : 1 < b) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, M n ω ≤ b * √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω))) := by
  have hb2 : (1 : ℝ) < b ^ 2 := by nlinarith [hb]
  set t := min ((b ^ 2 - 1) / 4) 1 with ht_def
  have ht0 : 0 < t := lt_min (div_pos (by linarith) (by norm_num)) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have ht4 : t ≤ (b ^ 2 - 1) / 4 := min_le_left _ _
  exact ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp hM hM0 hM2 hc hbd hV
    (ρ := 1 + t) (ε := t) (δ := t / 2) (b := b) (by linarith) (by linarith) (by linarith)
    (by linarith) (by nlinarith [ht4, ht1, ht0])

/-- **Sharp `limsup ≤ 1`, one-sided** (blueprint `thm:llil_sharp`). For a bounded-increment
`L²`-martingale with `M_0 = 0` and `⟨M⟩_n → ∞` a.s., almost surely for every `b > 1` eventually
`M_n ≤ b √(2 ⟨M⟩_n log log⟨M⟩_n)`, i.e. `limsup M_n/√(2⟨M⟩_n log log⟨M⟩_n) ≤ 1`. Countable
intersection over `b_m = 1 + 1/(m+1) ↓ 1` of the previous lemma. -/
lemma ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp_all [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, M n ω ≤ b * √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω))) := by
  have hmany : ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop, M n ω ≤ (1 + 1 / ((m : ℝ) + 1))
      * √(2 * predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) := by
    rw [ae_all_iff]
    intro m
    refine ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp' hM hM0 hM2 hc hbd hV ?_
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  filter_upwards [hmany] with ω hω b hb1
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < b - 1 by linarith)
  filter_upwards [hω m] with n hn
  refine hn.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  linarith [hm]

/-- **Sharp `limsup ≤ 1`, two-sided** (blueprint `thm:llil_sharp`). Applying the one-sided sharp
bound to `M` and `-M` (same quadratic variation, `predQuadVar_neg`) gives, a.s., for every `b > 1`
eventually `|M_n| ≤ b √(2 ⟨M⟩_n log log⟨M⟩_n)`. This is the sharp constant `1` (two-sided). -/
lemma ae_eventually_abs_le_sqrt_predQuadVar_mul_loglog_sharp [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, |M n ω| ≤ b * √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω))) := by
  have hM0neg : (-M) 0 =ᵐ[μ] 0 := by
    filter_upwards [hM0] with ω hω
    simp only [Pi.neg_apply, Pi.zero_apply] at hω ⊢; rw [hω, neg_zero]
  have hM2neg : ∀ n, Integrable (fun ω ↦ (-M) n ω ^ 2) μ := fun n ↦ by
    have he : (fun ω ↦ (-M) n ω ^ 2) = (fun ω ↦ M n ω ^ 2) := by
      funext ω; simp only [Pi.neg_apply, neg_sq]
    rw [he]; exact hM2 n
  have hbdneg : ∀ i, ∀ᵐ ω ∂μ, |(-M) (i + 1) ω - (-M) i ω| ≤ c := fun i ↦ by
    filter_upwards [hbd i] with ω hω
    have he : (-M) (i + 1) ω - (-M) i ω = -(M (i + 1) ω - M i ω) := by
      simp only [Pi.neg_apply]; ring
    rw [he, abs_neg]; exact hω
  have hVneg : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar (-M) ℱ μ n ω) atTop atTop := by
    filter_upwards [hV] with ω hω; simpa only [predQuadVar_neg] using hω
  filter_upwards [ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp_all hM hM0 hM2 hc hbd hV,
    ae_eventually_le_sqrt_predQuadVar_mul_loglog_sharp_all hM.neg hM0neg hM2neg hc hbdneg hVneg]
    with ω hpos hneg b hb1
  filter_upwards [hpos b hb1, hneg b hb1] with n h1 h2
  rw [predQuadVar_neg] at h2
  simp only [Pi.neg_apply] at h2
  rw [abs_le]
  exact ⟨by linarith [h2], h1⟩

/-- **Sharp constant as an actual `limsup`** (blueprint `thm:llil_sharp`). The two-sided sharp bound
in genuine `limsup` form: almost surely
`limsup_n |M_n| / √(2 ⟨M⟩_n log log⟨M⟩_n) ≤ 1`. Derived from the `∀ b > 1, ∀ᶠ` form
(`ae_eventually_abs_le_sqrt_predQuadVar_mul_loglog_sharp`): each `b > 1` bounds the `limsup`
(`limsup_le_of_le`, the quotient being cobounded below by `0`), and `limsup ≤ b` for all `b > 1`
gives `limsup ≤ 1`. -/
lemma ae_limsup_abs_div_sqrt_predQuadVar_mul_loglog_le_one [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c)
    (hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M ℱ μ n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, limsup (fun n ↦ |M n ω| / √(2 * predQuadVar M ℱ μ n ω
      * log (log (predQuadVar M ℱ μ n ω)))) atTop ≤ 1 := by
  filter_upwards [ae_eventually_abs_le_sqrt_predQuadVar_mul_loglog_sharp hM hM0 hM2 hc hbd hV]
    with ω hω
  have hg_nonneg : ∀ n, 0 ≤ |M n ω|
      / √(2 * predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω))) :=
    fun n ↦ div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ |M n ω|
      / √(2 * predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω)))) :=
    IsCoboundedUnder.of_frequently_ge (a := 0) ((Eventually.of_forall hg_nonneg).frequently)
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  refine limsup_le_of_le hcobdd ?_
  filter_upwards [hω a ha] with n hn
  rcases le_or_gt (√(2 * predQuadVar M ℱ μ n ω * log (log (predQuadVar M ℱ μ n ω)))) 0 with hs | hs
  · rw [le_antisymm hs (Real.sqrt_nonneg _), div_zero]; linarith
  · rw [div_le_iff₀ hs]; exact hn

/-! ### Refined per-block Freedman bounds for growing increments (deterministic horizon)

The sharp bounded engine above requires a global increment bound; the i.i.d. Hartman–Wintner low
part has increments growing like `√(i/log i)`. As in the `O`-rate `LILLogLog.lean`, we handle
growing increments by stopping at each deterministic horizon `2^j` (`stopMart`), where the
increments are bounded up to the horizon, and applying the refined pre-optimization Freedman bound
with the near-optimal `θ_j = α√(log(j+2)/2^j)`. The refined exponent collapses to the sharp
`(½(1+δ)α²v - αC)log(j+2)`, a `p`-series tail.

**Scope.** These are the *sharp per-block bounds* (refined-Freedman exponent). Repackaging them to
the natural `n`-scale via the least `j` with `n ≤ 2^j` incurs `2^j ≤ 2n`, an irreducible base-2
factor, so the resulting LIL constant is `√2·(C/√(2v)) → √2`, not the sharp `1` — the base-2
deterministic horizon sharpens the exponent but not the constant. The sharp constant for growing
increments instead requires blocking with base `ρ ↓ 1` (quadratic-variation stopping at level `ρ^k`,
blueprint `lem:llil_qv_stop`), which reuses the *bounded* sharp block on the stopped martingale;
that random-stopping quadratic-variation identity is the remaining ingredient. -/

/-- **Refined Freedman with a horizon-local increment bound.** The sharp-constant analogue of
`measure_exists_ge_le_exp_horizon`: the increment bound `|ΔM_i| ≤ c` is required only for `i < N`,
via the process stopped at `N` (`stopMart`), whose increments are globally bounded by `c`. -/
lemma measure_exists_ge_le_exp_horizon_refined [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {c θ δ η : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2) (hc : 0 ≤ c)
    (hθc : |θ| * c ≤ η) (hθ0 : 0 < θ) (lam v : ℝ) (N : ℕ)
    (hb : ∀ i < N, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    μ {ω | ∃ m ≤ N, lam ≤ M m ω ∧ predQuadVar M ℱ μ m ω ≤ v}
      ≤ ENNReal.ofReal (exp (-θ * lam + (1 + δ) / 2 * θ ^ 2 * v)) := by
  have hM'0 : stopMart M N 0 =ᵐ[μ] 0 := by
    have : stopMart M N 0 = M 0 := by rw [stopMart_apply, Nat.zero_min]
    rw [this]; exact hM0
  have hM'2 : ∀ n, Integrable (fun ω ↦ stopMart M N n ω ^ 2) μ := fun n ↦ by
    simp only [stopMart_apply]; exact hM2 (min n N)
  have hb' : ∀ i, ∀ᵐ ω ∂μ, |stopMart M N (i + 1) ω - stopMart M N i ω| ≤ c := fun i ↦ by
    by_cases hi : i < N
    · have h1 : min i N = i := by omega
      have h2 : min (i + 1) N = i + 1 := by omega
      simpa only [stopMart_apply, h1, h2] using hb i hi
    · have hNi : N ≤ i := not_lt.mp hi
      have h1 : min i N = N := by omega
      have h2 : min (i + 1) N = N := by omega
      filter_upwards with ω
      simp only [stopMart_apply, h1, h2, sub_self, abs_zero]; exact hc
  have hmain := measure_exists_ge_le_exp_refined (martingale_stopMart hM N) hM'0 hM'2 hδ hη hθc hθ0
    hb' lam v N
  have hset : {ω | ∃ m ≤ N, lam ≤ M m ω ∧ predQuadVar M ℱ μ m ω ≤ v}
      = {ω | ∃ m ≤ N, lam ≤ stopMart M N m ω ∧ predQuadVar (stopMart M N) ℱ μ m ω ≤ v} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun m ↦ and_congr_right fun hm ↦ ?_
    rw [stopMart_apply, min_eq_left hm, predQuadVar_stopMart_of_le M N hm]
  rw [hset]; exact hmain

/-- **Sharp per-block loglog Freedman bound for a growing-increment martingale.** With
`θ_j = α√(log(j+2)/2^j)`, an increment bound `c` up to horizon `2^j`, threshold
`λ_j = C√(2^j log(j+2))` and quadratic-variation bound `v·2^j`, the refined horizon Freedman gives
the sharp exponent `(½(1+δ)α²v - αC)log(j+2)` (square roots collapse). Admissibility
`θ_j c ≤ η` is a hypothesis (`η` from the refined inequality). -/
lemma measure_exists_ge_le_exp_block_loglog_sharp [IsProbabilityMeasure μ] (hM : Martingale M ℱ μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) {v C α δ η c : ℝ}
    (hδ : 0 ≤ δ) (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2) (hα : 0 < α)
    (hc0 : 0 ≤ c) (j Nj : ℕ) (hNj : 1 ≤ Nj)
    (hadm : α * √(log ((j : ℝ) + 2) / (Nj : ℝ)) * c ≤ η)
    (hinc : ∀ i < Nj, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    μ {ω | ∃ m ≤ Nj, C * √((Nj : ℝ) * log ((j : ℝ) + 2)) ≤ M m ω
          ∧ predQuadVar M ℱ μ m ω ≤ v * (Nj : ℝ)}
      ≤ ENNReal.ofReal (exp (((1 + δ) / 2 * α ^ 2 * v - α * C) * log ((j : ℝ) + 2))) := by
  have hL : (0 : ℝ) < log ((j : ℝ) + 2) :=
    log_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hNjR : (0 : ℝ) < (Nj : ℝ) := by exact_mod_cast hNj
  set θ : ℝ := α * √(log ((j : ℝ) + 2) / (Nj : ℝ)) with hθ_def
  have hθ0 : 0 < θ := mul_pos hα (sqrt_pos.mpr (by positivity))
  have hθc : |θ| * c ≤ η := by rw [abs_of_pos hθ0]; exact hadm
  have hmain := measure_exists_ge_le_exp_horizon_refined hM hM0 hM2 hδ hη hc0 hθc hθ0
    (C * √((Nj : ℝ) * log ((j : ℝ) + 2))) (v * (Nj : ℝ)) Nj hinc
  refine le_trans hmain (le_of_eq ?_)
  congr 2
  have hcollapse2 : √(log ((j : ℝ) + 2) / (Nj : ℝ)) * √((Nj : ℝ) * log ((j : ℝ) + 2))
      = log ((j : ℝ) + 2) := by
    rw [← sqrt_mul (by positivity),
      show log ((j : ℝ) + 2) / (Nj : ℝ) * ((Nj : ℝ) * log ((j : ℝ) + 2))
        = log ((j : ℝ) + 2) ^ 2 by field_simp, sqrt_sq hL.le]
  have hterm1 : θ * (C * √((Nj : ℝ) * log ((j : ℝ) + 2))) = α * C * log ((j : ℝ) + 2) := by
    rw [hθ_def]
    calc α * √(log ((j : ℝ) + 2) / (Nj : ℝ)) * (C * √((Nj : ℝ) * log ((j : ℝ) + 2)))
        = α * C * (√(log ((j : ℝ) + 2) / (Nj : ℝ)) * √((Nj : ℝ) * log ((j : ℝ) + 2))) := by
          ring
      _ = α * C * log ((j : ℝ) + 2) := by rw [hcollapse2]
  have hterm2 : (1 + δ) / 2 * θ ^ 2 * (v * (Nj : ℝ))
      = (1 + δ) / 2 * α ^ 2 * v * log ((j : ℝ) + 2) := by
    rw [hθ_def, mul_pow, sq_sqrt (by positivity)]
    field_simp
  rw [show -θ * (C * √((Nj : ℝ) * log ((j : ℝ) + 2))) + (1 + δ) / 2 * θ ^ 2 * (v * (Nj : ℝ))
      = -(θ * (C * √((Nj : ℝ) * log ((j : ℝ) + 2))))
        + (1 + δ) / 2 * θ ^ 2 * (v * (Nj : ℝ)) by ring, hterm1, hterm2]
  ring

/-- **Sharp block Borel–Cantelli for a growing-increment martingale.** Given horizons `N j` (with
`1 ≤ N j`), a per-block increment bound `c j` up to horizon `N j` with admissible `θ_j c_j ≤ η`, and
`1 < αC - ½(1+δ)α²v` (so the block tails `(j+2)^{½(1+δ)α²v-αC}` are summable), almost surely for all
large `j` and every `m ≤ N j`, `⟨M⟩_m ≤ v·N j ⇒ M_m < C√(N j·log(j+2))`. The horizon sequence is a
parameter: taking `N j = ⌈ρ^j⌉` with `ρ ↓ 1` (rather than `2^j`) is what delivers the sharp constant
in the repackaging. -/
lemma ae_eventually_lt_block_of_growing_loglog_sharp [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {v C α δ η : ℝ} (hδ : 0 ≤ δ) (hη : ∀ x : ℝ, |x| ≤ η → exp x ≤ 1 + x + (1 + δ) / 2 * x ^ 2)
    (hα : 0 < α) (N : ℕ → ℕ) (hN : ∀ j, 1 ≤ N j) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j)
    (hp : 1 < α * C - (1 + δ) / 2 * α ^ 2 * v)
    (hadm : ∀ᶠ (j : ℕ) in atTop, α * √(log ((j : ℝ) + 2) / (N j : ℝ)) * c j ≤ η)
    (hinc : ∀ j : ℕ, ∀ i < N j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j) :
    ∀ᵐ ω ∂μ, ∀ᶠ (j : ℕ) in atTop, ∀ m ≤ N j,
      predQuadVar M ℱ μ m ω ≤ v * (N j : ℝ) →
      M m ω < C * √((N j : ℝ) * log ((j : ℝ) + 2)) := by
  set S : ℕ → Set Ω := fun j ↦ {ω | ∃ m ≤ N j, C * √((N j : ℝ) * log ((j : ℝ) + 2)) ≤ M m ω
    ∧ predQuadVar M ℱ μ m ω ≤ v * (N j : ℝ)} with hS_def
  have hsummable : Summable
      (fun j : ℕ ↦ exp (((1 + δ) / 2 * α ^ 2 * v - α * C) * log ((j : ℝ) + 2))) := by
    have heq : (fun j : ℕ ↦ exp (((1 + δ) / 2 * α ^ 2 * v - α * C) * log ((j : ℝ) + 2)))
        = fun j : ℕ ↦ exp (-(α * C - (1 + δ) / 2 * α ^ 2 * v) * log ((j : ℝ) + 2)) := by
      funext j; congr 1; ring
    rw [heq]; exact summable_exp_neg_mul_log_add hp
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hadm
  have hfin : (∑' j, μ (S j)) ≠ ∞ := by
    rw [← ENNReal.sum_add_tsum_compl (Finset.range j₀) fun j ↦ μ (S j)]
    refine ENNReal.add_ne_top.mpr
      ⟨(ENNReal.sum_lt_top.mpr fun k _ ↦ measure_lt_top μ (S k)).ne, ?_⟩
    have key : (∑' i : ↥((↑(Finset.range j₀) : Set ℕ)ᶜ), μ (S ↑i))
        ≤ ∑' j : ℕ,
          ENNReal.ofReal (exp (((1 + δ) / 2 * α ^ 2 * v - α * C) * log ((j : ℝ) + 2))) := by
      refine le_trans (ENNReal.tsum_le_tsum fun i ↦ ?_)
        (ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective _)
      obtain ⟨k, hk⟩ := i
      rw [Finset.coe_range, Set.mem_compl_iff, Set.mem_Iio, not_lt] at hk
      exact measure_exists_ge_le_exp_block_loglog_sharp hM hM0 hM2 hδ hη hα (hc0 k) k (N k) (hN k)
        (hj₀ k hk) (hinc k)
    refine ne_top_of_le_ne_top ?_ key
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ (exp_pos _).le) hsummable]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with j hj
  intro m hm hqv
  by_contra hcon
  rw [not_lt] at hcon
  exact hj ⟨m, hm, hcon, hqv⟩

set_option maxHeartbeats 800000 in
-- The repackaging combines the per-block bound with the least-`j` estimates `N_j ≤ ρn+1` and
-- the additive `log(j+2) ≤ D_ρ + loglog n` through a single `nlinarith`; the accumulated linear
-- arithmetic exceeds the default heartbeat budget.
/-- **Sharp `√(2vn loglog n)` LIL for a growing-increment martingale with a linear quadratic
variation bound.** With time horizons `N_j = ⌈ρ^j⌉` (`ρ ↓ 1`), condition \textbf{(H)} in the form
`c_j √(log(j+2)/N_j) → 0`, and `⟨M⟩_n ≤ v·n`, almost surely eventually
`M_n ≤ b √(2 v n log log n)`, whenever `C√ρ < b√(2v)` and `1 < αC - ½(1+δ)α²v`. Repackaging the
block via the least `j` with `n ≤ N_j`: `N_j ≤ ρn+1` and (additively) `log(j+2) ≤ D_ρ + loglog n`,
so the constant is `C√ρ/√(2v)·(1+o(1)) < b`. No random stopping time is used: the linear QV bound
lets a deterministic time horizon play the role of quadratic-variation stopping. -/
lemma ae_eventually_le_sqrt_nat_mul_loglog_of_growing_sharp [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {v C α δ b ρ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ) (hα : 0 < α) (hv : 0 < v)
    (hp : 1 < α * C - (1 + δ) / 2 * α ^ 2 * v) (hb0 : 0 < b) (hbC : C * √ρ < b * √(2 * v))
    (N : ℕ → ℕ) (hNmono : Monotone N) (hN1 : ∀ j, 1 ≤ N j) (hNle : ∀ j, ρ ^ j ≤ (N j : ℝ))
    (hNlt : ∀ j, (N j : ℝ) < ρ ^ j + 1) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j)
    (hinc : ∀ j, ∀ i < N j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j)
    (hH : Tendsto (fun j : ℕ ↦ c j * √(log ((j : ℝ) + 2) / (N j : ℝ))) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, M n ω ≤ b * √(2 * v * (n : ℝ) * log (log n)) := by
  obtain ⟨η, hη0, hη⟩ := exp_le_one_add_add_half_mul_sq hδ
  have hCpos : 0 < C := by nlinarith [hp, mul_nonneg (sq_nonneg α) hv.le, hα]
  have hlogρ : (0 : ℝ) < log ρ := log_pos hρ
  have h2v : (0 : ℝ) < 2 * v := by positivity
  have hρpos : (0 : ℝ) < ρ := by linarith
  -- Eventual admissibility from condition (H).
  have hAdm : ∀ᶠ (j : ℕ) in atTop, α * √(log ((j : ℝ) + 2) / (N j : ℝ)) * c j ≤ η := by
    have htend : Tendsto (fun j : ℕ ↦ α * (c j * √(log ((j : ℝ) + 2) / (N j : ℝ)))) atTop
        (𝓝 0) := by tendsto
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
  filter_upwards [ae_eventually_lt_block_of_growing_loglog_sharp hM hM0 hM2 hδ.le hη hα N hN1 c hc0
    hp hAdm hinc, hqv] with ω hgood hqvn
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
  -- Least block `j` with `n ≤ N j`.
  obtain ⟨j, hjle, hjmin⟩ : ∃ j : ℕ, n ≤ N j ∧ ∀ m, m < j → ¬ n ≤ N m := by
    have hex : ∃ j : ℕ, n ≤ N j := by
      obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_ge_atTop
        ((n : ℝ) + 1)).exists
      exact ⟨j, by exact_mod_cast (lt_of_lt_of_le (by linarith : (n : ℝ) < ρ ^ j) (hNle j)).le⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
  have hjj0 : j₀ ≤ j := by
    by_contra hlt
    rw [not_le] at hlt
    have := hNmono hlt.le
    omega
  -- `N_j ≤ ρ·n + 1`.
  have hNjR : (N j : ℝ) ≤ ρ * (n : ℝ) + 1 := by
    obtain _ | m := j
    · have h0 := hNlt 0
      rw [pow_zero] at h0
      nlinarith [h0, hn1, hρ]
    · have hm : ¬ n ≤ N m := hjmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmR : (ρ : ℝ) ^ m < (n : ℝ) := lt_of_le_of_lt (hNle m) (by exact_mod_cast hm)
      have h1 := hNlt (m + 1)
      rw [pow_succ] at h1
      nlinarith [h1, hmR, mul_lt_mul_of_pos_right hmR hρpos]
  -- `log(j+2) ≤ D_ρ + loglog n` (additive).
  have hjR : (j : ℝ) + 2 ≤ log n / log ρ + 3 := by
    obtain _ | m := j
    · simp only [Nat.cast_zero]; have := div_nonneg hlognpos.le hlogρ.le; linarith
    · have hm : ¬ n ≤ N m := hjmin m (Nat.lt_succ_self m)
      rw [not_le] at hm
      have hmR : (ρ : ℝ) ^ m < (n : ℝ) := lt_of_le_of_lt (hNle m) (by exact_mod_cast hm)
      have hmlog : (m : ℝ) * log ρ < log n := by
        rw [← log_pow]; exact log_lt_log (by positivity) hmR
      have : (m : ℝ) < log n / log ρ := by rw [lt_div_iff₀ hlogρ]; linarith
      push_cast; linarith
  have hlogj2 : log ((j : ℝ) + 2) ≤ Dρ + log (log n) := by
    have hstep1 : (j : ℝ) + 2 ≤ (1 / log ρ + 1) * log n := by
      have hb2 : log n / log ρ + 3 ≤ (1 / log ρ + 1) * log n := by
        rw [add_mul, one_div, inv_mul_eq_div, one_mul]; linarith
      linarith
    calc log ((j : ℝ) + 2)
        ≤ log ((1 / log ρ + 1) * log n) := log_le_log (by positivity) hstep1
      _ = log (1 / log ρ + 1) + log (log n) :=
          log_mul (show (0 : ℝ) < 1 / log ρ + 1 by positivity).ne' hlognpos.ne'
      _ = Dρ + log (log n) := by rw [hDρ_def]
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
condition \textbf{(H)}. -/
lemma ae_eventually_le_sqrt_nat_mul_loglog_of_growing_sharp' [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {v δ b ρ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ) (hv : 0 < v) (hb0 : 0 < b) (hbρ : (1 + δ) * ρ < b ^ 2)
    (N : ℕ → ℕ) (hNmono : Monotone N) (hN1 : ∀ j, 1 ≤ N j) (hNle : ∀ j, ρ ^ j ≤ (N j : ℝ))
    (hNlt : ∀ j, (N j : ℝ) < ρ ^ j + 1) (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j)
    (hinc : ∀ j, ∀ i < N j, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c j)
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
  exact ae_eventually_le_sqrt_nat_mul_loglog_of_growing_sharp hM hM0 hM2 hρ hδ hαpos hv hp hb0 hbC
    N hNmono hN1 hNle hNlt c hc0 hinc hH hqv

/-- **Condition (H) from a base-independent increment growth.** If the increment growth `g`
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
    tendsto
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
`δ = (b-1)/2` give `(1+δ)ρ = ρ² < b²`; condition (H) comes from `tendsto_growth_horizon`. -/
lemma ae_eventually_le_sqrt_nat_mul_loglog_of_growth_sharp_all [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {v : ℝ} (hv : 0 < v) {g : ℕ → ℝ} (hgmono : Monotone g) (hgnn : ∀ i, 0 ≤ g i)
    (hginc : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ g i)
    (hg : Tendsto (fun n : ℕ ↦ g n * √(log (log n) / n)) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop,
      M n ω ≤ b * √(2 * v * (n : ℝ) * log (log n)) := by
  have hmany : ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop,
      M n ω ≤ (1 + 1 / ((m : ℝ) + 1)) * √(2 * v * (n : ℝ) * log (log n)) := by
    rw [ae_all_iff]
    intro m
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
    refine ae_eventually_le_sqrt_nat_mul_loglog_of_growing_sharp' hM hM0 hM2 hρ1 hδ0 hv hb0 hbρ
      N hNmono hN1 hNle hNlt (fun j ↦ g (N j)) (fun j ↦ hgnn _) ?_
      (tendsto_growth_horizon hρ1 hgnn hNle hg) hqv
    intro j i hi
    filter_upwards [hginc i] with ω hω
    exact hω.trans (hgmono hi.le)
  filter_upwards [hmany] with ω hω b hb1
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < b - 1 by linarith)
  filter_upwards [hω m] with n hn
  refine hn.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  linarith [hm]

/-- **Sharp growing-increment LIL, `b > 1` limit (two-sided).** Applying the one-sided limit to `M`
and `-M` (same increment growth and quadratic variation, `predQuadVar_neg`) gives, a.s., for every
`b > 1` eventually `|M_n| ≤ b √(2 v n loglog n)`: the sharp constant `1` for growing increments. -/
lemma ae_eventually_abs_le_sqrt_nat_mul_loglog_of_growth_sharp_all [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {v : ℝ} (hv : 0 < v) {g : ℕ → ℝ} (hgmono : Monotone g) (hgnn : ∀ i, 0 ≤ g i)
    (hginc : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ g i)
    (hg : Tendsto (fun n : ℕ ↦ g n * √(log (log n) / n)) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, 1 < b → ∀ᶠ n in atTop,
      |M n ω| ≤ b * √(2 * v * (n : ℝ) * log (log n)) := by
  have hM0neg : (-M) 0 =ᵐ[μ] 0 := by
    filter_upwards [hM0] with ω hω; simp only [Pi.neg_apply, Pi.zero_apply] at hω ⊢
    rw [hω, neg_zero]
  have hM2neg : ∀ n, Integrable (fun ω ↦ (-M) n ω ^ 2) μ := fun n ↦ by
    have he : (fun ω ↦ (-M) n ω ^ 2) = (fun ω ↦ M n ω ^ 2) := by
      funext ω; simp only [Pi.neg_apply, neg_sq]
    rw [he]; exact hM2 n
  have hgincneg : ∀ i, ∀ᵐ ω ∂μ, |(-M) (i + 1) ω - (-M) i ω| ≤ g i := fun i ↦ by
    filter_upwards [hginc i] with ω hω
    have he : (-M) (i + 1) ω - (-M) i ω = -(M (i + 1) ω - M i ω) := by
      simp only [Pi.neg_apply]; ring
    rw [he, abs_neg]; exact hω
  have hqvneg : ∀ᵐ ω ∂μ, ∀ n, predQuadVar (-M) ℱ μ n ω ≤ v * (n : ℝ) := by
    filter_upwards [hqv] with ω hω n; rw [predQuadVar_neg]; exact hω n
  filter_upwards [ae_eventually_le_sqrt_nat_mul_loglog_of_growth_sharp_all hM hM0 hM2 hv hgmono
      hgnn hginc hg hqv,
    ae_eventually_le_sqrt_nat_mul_loglog_of_growth_sharp_all hM.neg hM0neg hM2neg hv hgmono
      hgnn hgincneg hg hqvneg] with ω hpos hneg b hb1
  filter_upwards [hpos b hb1, hneg b hb1] with n h1 h2
  simp only [Pi.neg_apply] at h2
  rw [abs_le]
  exact ⟨by linarith [h2], h1⟩

/-- **Sharp growing-increment LIL as a `limsup`** (two-sided). Almost surely
`limsup_n |M_n| / √(2 v n log log n) ≤ 1`, from the `∀ b > 1, ∀ᶠ` two-sided form. -/
lemma ae_limsup_abs_div_sqrt_nat_mul_loglog_of_growth_le_one [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    {v : ℝ} (hv : 0 < v) {g : ℕ → ℝ} (hgmono : Monotone g) (hgnn : ∀ i, 0 ≤ g i)
    (hginc : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ g i)
    (hg : Tendsto (fun n : ℕ ↦ g n * √(log (log n) / n)) atTop (𝓝 0))
    (hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ v * (n : ℝ)) :
    ∀ᵐ ω ∂μ, limsup (fun n ↦ |M n ω| / √(2 * v * (n : ℝ) * log (log n))) atTop ≤ 1 := by
  filter_upwards [ae_eventually_abs_le_sqrt_nat_mul_loglog_of_growth_sharp_all hM hM0 hM2 hv
    hgmono hgnn hginc hg hqv] with ω hω
  have hg_nonneg : ∀ n, 0 ≤ |M n ω| / √(2 * v * (n : ℝ) * log (log n)) :=
    fun n ↦ div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n ↦ |M n ω| / √(2 * v * (n : ℝ) * log (log n))) :=
    IsCoboundedUnder.of_frequently_ge (a := 0) ((Eventually.of_forall hg_nonneg).frequently)
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  refine limsup_le_of_le hcobdd ?_
  filter_upwards [hω a ha] with n hn
  rcases le_or_gt (√(2 * v * (n : ℝ) * log (log n))) 0 with hs | hs
  · rw [le_antisymm hs (Real.sqrt_nonneg _), div_zero]; linarith
  · rw [div_le_iff₀ hs]; exact hn

end AlphaRAR
