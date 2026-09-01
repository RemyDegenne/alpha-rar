/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.PropDevARTS
public import AlphaRAR.YDK2026.AssignmentRate
public import AlphaRAR.YDK2026.ARTSRates
public meta import Characterization

/-!
# The a.s. `O(√(n log log n))` proportion-deviation bound for the aRTS design

This file proves the almost-sure loglog part of Theorem 4.2 (i) of the paper, equations (6)
and (7): for every arm `k`,
`|N_{n,k} - n ρ̂_{n,k}| = O(√(n log log n))` a.s. and `N_{n,k} - n v_k = O(√(n log log n))` a.s.

Unlike the `o_p(√n)` half (`aRTS_prop_dev`), the a.s. bound avoids the entire `ell_rho_control` /
`vmaxSeq` maximal-inequality machinery. It rests on two a.s. loglog rates — the
assignment-martingale LIL `M_{n,k} = O(√(n log log n))`
(`ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog`) and the plug-in-target rate
`ρ̂_{n,k} - v_k = O(√(n log log n)/n)` (`aRTS_rho_rate`) — combined with the same
deterministic backbone as the `o_p` proof: the key inequality `generic_ineq_of_hitting`, the
smallness `preliminary_small`, the `U`-increment decomposition `diff_U_decomp` (drift `≤ 0`), and
the simplex identity `sum_count_sub_smul_eq_zero` for the reverse step.

## Main results

* Analytic lemmas about the `√(n log log n)` rate (`sqrt_mul_log_log` in lemma names).
* `AlphaRAR.aRTS_prop_dev_ae`, `AlphaRAR.aRTS_count_sub_smul_ae`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Real
open scoped Topology ENNReal NNReal

namespace AlphaRAR

/-- The loglog-LIL rate `√(n log log n)` diverges, so an `O(√(n log log n))` bound is a statement
about a diverging scale rather than a disguised constant. -/
lemma tendsto_sqrt_mul_log_log_atTop :
    Tendsto (fun n : ℕ ↦ √(n * log (log n))) atTop atTop := by
  have hll : Tendsto (fun n : ℕ ↦ log (log n)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hprod : Tendsto (fun n : ℕ ↦ (n : ℝ) * log (log n)) atTop atTop :=
    Tendsto.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop hll
  exact tendsto_sqrt_atTop.comp hprod

/-- Eventually `1 ≤ √(n log log n)`. -/
lemma eventually_one_le_sqrt_mul_log_log : ∀ᶠ n : ℕ in atTop, 1 ≤ √(n * log (log n)) :=
  tendsto_sqrt_mul_log_log_atTop.eventually_ge_atTop 1

/-- `√(n log log n)` is nondecreasing once `3 ≤ n`: on `[3, ∞)` the argument `n log log n` is
nondecreasing (`log log` is nonnegative and nondecreasing there). This is what lets the rate at a
random time `ℓ ≤ n` be replaced by the rate at `n`. -/
lemma sqrt_mul_log_log_le_of_le {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    √(m * log (log m)) ≤ √(n * log (log n)) := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (3 : ℝ) ≤ n := le_trans hmR (by exact_mod_cast hmn)
  have hexp3 : exp 1 ≤ 3 := (exp_one_lt_d9.le).trans (by norm_num)
  have hlogm1 : 1 ≤ log m := (le_log_iff_exp_le (by linarith)).mpr (by linarith)
  have hlogn1 : 1 ≤ log n := (le_log_iff_exp_le (by linarith)).mpr (by linarith)
  have hllm : 0 ≤ log (log m) := log_nonneg hlogm1
  have hlln : 0 ≤ log (log n) := log_nonneg hlogn1
  have hloglog : log (log m) ≤ log (log n) :=
    log_le_log (by linarith) (log_le_log (by linarith) (by exact_mod_cast hmn))
  refine sqrt_le_sqrt ?_
  calc (m : ℝ) * log (log m) ≤ (m : ℝ) * log (log n) :=
        mul_le_mul_of_nonneg_left hloglog (by linarith)
    _ ≤ (n : ℝ) * log (log n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hlln

/-- **Uniform loglog bound over a bounded random time.** If `g ≥ 0` is `O(√(m log log m))` (bounded
by `C · √(m * log (log m))` eventually), then eventually in `n`, *every* `g m` with `m ≤ n` is
bounded by a single multiple of `√(n * log (log n))`. This lets one bound `g` at a random time
`ℓ_n ≤ n` (which may stay bounded or diverge) uniformly by `C' · √(n * log (log n))`. -/
lemma exists_forall_le_mul_sqrt_mul_log_log {g : ℕ → ℝ} (hg_nonneg : ∀ m, 0 ≤ g m)
    {C : ℝ} (hg : ∀ᶠ m in atTop, g m ≤ C * √(m * log (log m))) :
    ∃ C', ∀ᶠ n in atTop, ∀ m, m ≤ n → g m ≤ C' * √(n * log (log n)) := by
  rw [eventually_atTop] at hg
  obtain ⟨N, hN⟩ := hg
  set N₀ : ℕ := max N 3 with hN₀
  have hne : (Finset.range (N₀ + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N₀)⟩
  set B : ℝ := (Finset.range (N₀ + 1)).sup' hne g with hBdef
  have hBnn : 0 ≤ B := le_trans (hg_nonneg 0)
    (Finset.le_sup' g (Finset.mem_range.mpr (Nat.succ_pos N₀)))
  have hCnn : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0 + B, ?_⟩
  filter_upwards [eventually_ge_atTop N₀, eventually_one_le_sqrt_mul_log_log] with n hnN₀ hrn m hmn
  have hstep : (max C 0 + B) * 1 ≤ (max C 0 + B) * √(n * log (log n)) :=
    mul_le_mul_of_nonneg_left hrn (add_nonneg hCnn hBnn)
  rw [mul_one] at hstep
  rcases lt_or_ge m N₀ with hmlt | hmge
  · -- `m < N₀`: bounded by `B`, hence by `(max C 0 + B) · rate n`.
    have hgmB : g m ≤ B := Finset.le_sup' g (Finset.mem_range.mpr (by omega))
    linarith
  · -- `N₀ ≤ m ≤ n`: use the tail bound and monotonicity of the rate.
    have hm3 : 3 ≤ m := le_trans (le_max_right N 3) hmge
    have hmN : N ≤ m := le_trans (le_max_left N 3) hmge
    have h1 : g m ≤ max C 0 * √(m * log (log m)) :=
      le_trans (hN m hmN) (mul_le_mul_of_nonneg_right (le_max_left C 0) (sqrt_nonneg _))
    have h2 : max C 0 * √(m * log (log m)) ≤ max C 0 * √(n * log (log n)) :=
      mul_le_mul_of_nonneg_left (sqrt_mul_log_log_le_of_le hm3 hmn) hCnn
    have h3 : max C 0 * √(n * log (log n)) ≤ (max C 0 + B) * √(n * log (log n)) :=
      mul_le_mul_of_nonneg_right (by linarith) (sqrt_nonneg _)
    linarith

/-- A sum of two one-sided `O(√(n log log n))` upper bounds is `O(√(n log log n))`. -/
lemma bigOUpper_add {f g : ℕ → ℝ} {Cf Cg : ℝ}
    (hf : ∀ᶠ n in atTop, f n ≤ Cf * √(n * log (log n)))
    (hg : ∀ᶠ n in atTop, g n ≤ Cg * √(n * log (log n))) :
    ∀ᶠ n in atTop, f n + g n ≤ (Cf + Cg) * √(n * log (log n)) := by
  filter_upwards [hf, hg] with n hfn hgn
  rw [add_mul]; linarith

/-- An eventually-bounded sequence is `O(√(n log log n))` (since the rate tends to `∞`). -/
lemma bigOUpper_of_eventually_le {f : ℕ → ℝ} {B : ℝ} (hf : ∀ᶠ n in atTop, f n ≤ B) :
    ∃ C, ∀ᶠ n in atTop, f n ≤ C * √(n * log (log n)) := by
  refine ⟨max B 0, ?_⟩
  filter_upwards [hf, eventually_one_le_sqrt_mul_log_log] with n hfn hrn
  have hstep : max B 0 * 1 ≤ max B 0 * √(n * log (log n)) :=
    mul_le_mul_of_nonneg_left hrn (le_max_right _ _)
  rw [mul_one] at hstep
  linarith [le_max_left B 0]

/-- **Reverse step: two-sided from one-sided upper bounds via a simplex identity.** For a finite
family `Dev` with `∑_k Dev_k = 0`, if each `Dev_k` is `O(√(n log log n))` from above, then each is
`O(√(n log log n))` two-sided (a genuine `=O[atTop]` bound). -/
lemma isBigO_of_forall_upper_of_sum_zero {ι : Type*} [Fintype ι] {Dev : ι → ℕ → ℝ}
    (hsum : ∀ n, ∑ k, Dev k n = 0)
    (hfwd : ∀ k, ∃ C, ∀ᶠ n in atTop, Dev k n ≤ C * √(n * log (log n))) (k : ι) :
    (fun n ↦ Dev k n) =O[atTop] fun n ↦ √(n * log (log n)) := by
  classical
  choose C hC using hfwd
  have hall : ∀ᶠ n in atTop, ∀ j, Dev j n ≤ C j * √(n * log (log n)) := eventually_all.mpr hC
  rw [Asymptotics.isBigO_iff]
  refine ⟨max (C k) (∑ j, |C j|), ?_⟩
  filter_upwards [hall] with n hn
  have hrn : 0 ≤ √(n * log (log n)) := sqrt_nonneg _
  -- Upper bound: `Dev_k ≤ C_k · rate`.
  have hupper : Dev k n ≤ max (C k) (∑ j, |C j|) * √(n * log (log n)) :=
    le_trans (hn k) (by gcongr; exact le_max_left _ _)
  -- Lower bound: `-Dev_k = ∑_{j≠k} Dev_j ≤ (∑_{j≠k} C_j) rate ≤ (∑ |C_j|) rate`.
  have hneg : -(Dev k n) = ∑ j ∈ Finset.univ.erase k, Dev j n := by
    have key : Dev k n + ∑ j ∈ Finset.univ.erase k, Dev j n = ∑ j, Dev j n :=
      Finset.add_sum_erase Finset.univ (Dev · n) (Finset.mem_univ k)
    have hz := hsum n
    linarith
  have hlower : -(Dev k n) ≤ max (C k) (∑ j, |C j|) * √(n * log (log n)) := by
    rw [hneg]
    calc ∑ j ∈ Finset.univ.erase k, Dev j n
        ≤ ∑ j ∈ Finset.univ.erase k, C j * √(n * log (log n)) :=
          Finset.sum_le_sum fun j _ ↦ hn j
      _ = (∑ j ∈ Finset.univ.erase k, C j) * √(n * log (log n)) := by rw [Finset.sum_mul]
      _ ≤ (∑ j, |C j|) * √(n * log (log n)) := by
          gcongr
          calc ∑ j ∈ Finset.univ.erase k, C j ≤ ∑ j ∈ Finset.univ.erase k, |C j| :=
                Finset.sum_le_sum fun j _ ↦ le_abs_self _
            _ ≤ ∑ j, |C j| := Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.erase_subset _ _) fun j _ _ ↦ abs_nonneg _
      _ ≤ max (C k) (∑ j, |C j|) * √(n * log (log n)) := by gcongr; exact le_max_right _ _
  rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg hrn]
  rw [abs_le]
  exact ⟨by linarith, hupper⟩

/-- If `f = O(√(n log log n)/n)` then `n · f = O(√(n log log n))`. Turns the plug-in-target rate
`ρ̂_n - v = O(√(n log log n)/n)` into `n(ρ̂_n - v) = O(√(n log log n))`. -/
lemma isBigO_natMul_sqrt_mul_log_log {f : ℕ → ℝ}
    (hf : f =O[atTop] fun n ↦ √(n * log (log n)) / (n : ℝ)) :
    (fun n : ℕ ↦ (n : ℝ) * f n) =O[atTop] fun n ↦ √(n * log (log n)) := by
  rw [Asymptotics.isBigO_iff] at hf ⊢
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnne : (n : ℝ) ≠ 0 := hnR.ne'
  simp only [norm_eq_abs] at hn ⊢
  rw [abs_div, abs_of_nonneg (sqrt_nonneg _), abs_of_nonneg hnR.le] at hn
  rw [abs_mul, Nat.abs_cast, abs_of_nonneg (sqrt_nonneg _)]
  have hm := mul_le_mul_of_nonneg_left hn hnR.le
  rwa [show (n : ℝ) * (C * (√(n * log (log n)) / n)) = C * √(n * log (log n)) by field_simp] at hm

section ARTS

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- **Per-arm one-sided a.s. loglog bound on the deviation, at an abstract hitting time.** The
abstract-hitting-time generalisation of `aRTS_dev_upper`: for arm `k'`, given the estimator
consistency `hθconv`, the plug-in-target loglog rate `hρrate` (`ρ̂_n - v = O(√(n log log n)/n)`),
the throttle `hthrottle`, and the smallness upper bound `hsmall_upper`
(`N_ℓ - ℓ ρ̂_ℓ = O(√(n loglog n))` at the hitting time), the deviation `N_{n,k'} - n ρ̂_{n,k'}`
is `≤ C · √(n log log n)` eventually. The chain: `generic_ineq_of_hitting` gives
`Dev ≤ 1 + small + Uincr`; the `U`-increment decomposes (`diff_U_decomp`, `ε = (1-α)v/2`) as
`Uincr ≤ (drift ≤ 0) + (M_n - M_ℓ) + ℓ(ρ̂_ℓ - ρ̂_n)`; the `M`-difference is bounded by the
assignment-martingale LIL and the `ρ̂`-difference by the loglog rate, both lifted over the random
time `ℓ ≤ n` via `exists_forall_le_mul_sqrt_mul_log_log`. Everything but `hsmall_upper` and the
throttle is design-independent. -/
lemma dev_upper_of_hitting [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hθconv : ∀ᵐ ω ∂P, Tendsto (fun n k'' ↦ estimator (fun j ↦ actionIndicator A k'' j ω)
      (Y · ω) (θ₀ k'') n) atTop (𝓝 ν.means))
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k h.filtration P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k) (k' : 𝓐)
    (hρrate : ∀ᵐ ω ∂P, (fun n ↦ T (fun k'' ↦ estimator (fun j ↦ actionIndicator A k'' j ω)
      (Y · ω) (θ₀ k'') n) k' - T ν.means k')
        =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)))
    (hsmall_upper : ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      ((pullCount A k' (hitting (Q k' ω) n) ω : ℝ)
        - (hitting (Q k' ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k' ω) n) ω k')
          ≤ C * √(n * log (log n))) :
    ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      ((pullCount A k' n ω : ℝ)
        - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k') ≤ C * √(n * log (log n)) := by
  classical
  simp only [← count_indicator_eq_pullCount] at hsmall_upper ⊢
  set v : ℝ := T ν.means k' with hvdef
  set ℱ := h.filtration with hℱ
  -- Non-sparsity `v > 0` and the consistency `ρ̂ → v` from the estimator consistency.
  have hvpos : 0 < v := by
    obtain ⟨ω, hω⟩ := hθconv.exists
    exact hTpos ν.means
      (fun k'' ↦ estimator_limit_mem_attainableSet k'' (θ₀ k'') (tendsto_pi_nhds.mp hω k'')) k'
  set ε : ℝ := (1 - α) * v / 2 with hεdef
  have hεpos : 0 < ε := by
    have hp : (0 : ℝ) < (1 - α) * v := mul_pos (by linarith [hα1]) hvpos
    rw [hεdef]; linarith
  have hρconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k') atTop (𝓝 v) := by
    filter_upwards [hθconv] with ω hω
    exact ((continuous_apply k').tendsto _).comp ((hT.tendsto ν.means).comp hω)
  have hp1 : ∀ᵐ ω ∂P, ∀ m, aRTSSelProb A k' ℱ P m ω ≤ 1 := by
    rw [ae_all_iff]; intro m
    have hmono := condExp_mono (m := ℱ.shiftDown m)
      (integrable_actionIndicator P k' (h.measurable_action m)) (integrable_const (1 : ℝ))
      (Eventually.of_forall fun ω ↦ actionIndicator_le_one A k' m ω)
    rw [condExp_const (ℱ.shiftDown.le m)] at hmono
    filter_upwards [hmono] with ω hω; exact hω
  have hMLIL : ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      |assignMart (fun j ↦ actionIndicator A k' j) ℱ P n ω| ≤ C * √(n * log (log n)) :=
    ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog
      (h.adapted_actionIndicator k').stronglyAdapted
      (fun n ↦ integrable_actionIndicator P k' (h.measurable_action n))
      (fun n ↦ ae_of_all _ fun ω ↦ actionIndicator_nonneg A k' n ω)
      (fun n ↦ ae_of_all _ fun ω ↦ actionIndicator_le_one A k' n ω)
  have hρratebd : ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      ((n : ℕ) : ℝ) * |aRTSTarget A Y θ₀ T n ω k' - v| ≤ C * √(n * log (log n)) := by
    filter_upwards [hρrate] with ω hbigO
    rw [Asymptotics.isBigO_iff] at hbigO
    obtain ⟨C, hC⟩ := hbigO
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_gt_atTop 0] with n hn hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnne : (n : ℝ) ≠ 0 := hnR.ne'
    rw [norm_eq_abs, norm_eq_abs, abs_div, abs_of_nonneg (sqrt_nonneg _),
      abs_of_nonneg hnR.le] at hn
    have hmul := mul_le_mul_of_nonneg_left hn hnR.le
    rw [show (n : ℝ) * (C * (√((n : ℝ) * log (log n)) / n))
      = C * √((n : ℝ) * log (log n)) by field_simp] at hmul
    exact hmul
  -- The seam `assignMG (…, aRTSSelProb) = assignMart`.
  filter_upwards [hρconv, hthrottle k', hp1, hMLIL, hρratebd, hsmall_upper]
    with ω hρc hthr hp1ω hMlilω hρrω hsuω
  obtain ⟨CM, hCM⟩ := hMlilω
  obtain ⟨Cρ, hCρ⟩ := hρrω
  obtain ⟨Cs, hCs⟩ := hsuω
  obtain ⟨CM', hCM'⟩ := exists_forall_le_mul_sqrt_mul_log_log
    (g := fun m ↦ |assignMart (fun j ↦ actionIndicator A k' j) ℱ P m ω|)
    (fun m ↦ abs_nonneg _) hCM
  obtain ⟨Cρ', hCρ'⟩ := exists_forall_le_mul_sqrt_mul_log_log
    (g := fun m ↦ (m : ℝ) * |aRTSTarget A Y θ₀ T m ω k' - v|)
    (fun m ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) hCρ
  have hseam : ∀ m, assignMG (fun j ↦ actionIndicator A k' j ω)
      (fun j ↦ aRTSSelProb A k' ℱ P j ω) m
      = assignMart (fun j ↦ actionIndicator A k' j) ℱ P m ω := fun m ↦
    (assignMart_eq_assignMG m ω).symm
  have hdU := diff_U_decomp (X := fun j ↦ actionIndicator A k' j ω)
    (p := fun j ↦ aRTSSelProb A k' ℱ P j ω) (ρ := fun m ↦ aRTSTarget A Y θ₀ T m ω k') (α := α)
    hρc (ℓ := fun n ↦ hitting (Q k' ω) n) (fun n ↦ Nat.findGreatest_le n) hεpos
  refine ⟨1 + (2 * CM' + (Cρ' + Cρ) + Cs), ?_⟩
  filter_upwards [hdU, hCM', hCρ', hCρ, hCs, eventually_one_le_sqrt_mul_log_log]
    with n hdUn hCM'n hCρ'n hCρn hCsn hrn
  set ℓn : ℕ := hitting (Q k' ω) n with hℓndef
  have hℓle : ℓn ≤ n := Nat.findGreatest_le n
  -- Key inequality; the smallness at the hitting time enters through `hCsn`.
  have hgen := generic_ineq_of_hitting (fun j ↦ actionIndicator A k' j ω)
    (fun j ↦ aRTSSelProb A k' ℱ P j ω) (fun m ↦ aRTSTarget A Y θ₀ T m ω k') α
    (Q k' ω) hthr hp1ω (fun m ↦ mul_nonneg hα.1 (hTnn _ k')) n
  -- `Uincr ≤ (drift + M-diff + ρ-term) + ε(n-ℓ)`.
  have hUle : auxU (fun j ↦ actionIndicator A k' j ω) (fun j ↦ aRTSSelProb A k' ℱ P j ω)
        (fun m ↦ aRTSTarget A Y θ₀ T m ω k') α n
      - auxU (fun j ↦ actionIndicator A k' j ω) (fun j ↦ aRTSSelProb A k' ℱ P j ω)
        (fun m ↦ aRTSTarget A Y θ₀ T m ω k') α ℓn
      ≤ (((n : ℝ) - ℓn) * (-(1 - α) * v)
          + (assignMart (fun j ↦ actionIndicator A k' j) ℱ P n ω
            - assignMart (fun j ↦ actionIndicator A k' j) ℱ P ℓn ω)
          + (ℓn : ℝ) * (aRTSTarget A Y θ₀ T ℓn ω k' - aRTSTarget A Y θ₀ T n ω k'))
        + ε * ((n : ℝ) - ℓn) := by
    have h1 := (abs_le.mp hdUn).2
    rw [hseam n, hseam ℓn] at h1
    linarith
  -- Drift `≤ 0`: `(n-ℓ)(-(1-α)v) + ε(n-ℓ) = (n-ℓ)(-(1-α)v/2) ≤ 0`.
  have hℓnnR : (0 : ℝ) ≤ (n : ℝ) - ℓn := by rw [sub_nonneg]; exact_mod_cast hℓle
  have hdrift : ((n : ℝ) - ℓn) * (-(1 - α) * v) + ε * ((n : ℝ) - ℓn) ≤ 0 := by
    have : ((n : ℝ) - ℓn) * (-(1 - α) * v) + ε * ((n : ℝ) - ℓn)
        = ((n : ℝ) - ℓn) * (-(1 - α) * v / 2) := by rw [hεdef]; ring
    rw [this]
    apply mul_nonpos_of_nonneg_of_nonpos hℓnnR
    have : (0 : ℝ) < (1 - α) * v := mul_pos (by linarith [hα1]) hvpos
    linarith
  -- `M`-difference bound.
  have hMbound : assignMart (fun j ↦ actionIndicator A k' j) ℱ P n ω
        - assignMart (fun j ↦ actionIndicator A k' j) ℱ P ℓn ω ≤ 2 * CM' * √(n * log (log n)) := by
    have hMn := hCM'n n (le_refl n)
    have hMℓ := hCM'n ℓn hℓle
    have h1 : assignMart (fun j ↦ actionIndicator A k' j) ℱ P n ω ≤ CM' * √(n * log (log n)) :=
      le_trans (le_abs_self _) hMn
    have h2 : -assignMart (fun j ↦ actionIndicator A k' j) ℱ P ℓn ω ≤ CM' * √(n * log (log n)) :=
      le_trans (neg_le_abs _) hMℓ
    linarith
  -- `ρ̂`-difference bound.
  have hρbound : (ℓn : ℝ) * (aRTSTarget A Y θ₀ T ℓn ω k' - aRTSTarget A Y θ₀ T n ω k')
      ≤ (Cρ' + Cρ) * √(n * log (log n)) := by
    have hℓv := hCρ'n ℓn hℓle
    have hnv := hCρn
    have hsplit : (ℓn : ℝ) * (aRTSTarget A Y θ₀ T ℓn ω k' - aRTSTarget A Y θ₀ T n ω k')
        = (ℓn : ℝ) * (aRTSTarget A Y θ₀ T ℓn ω k' - v)
          - (ℓn : ℝ) * (aRTSTarget A Y θ₀ T n ω k' - v) := by ring
    have h1 : (ℓn : ℝ) * (aRTSTarget A Y θ₀ T ℓn ω k' - v) ≤ Cρ' * √(n * log (log n)) :=
      le_trans (le_trans (le_abs_self _) (by rw [abs_mul, Nat.abs_cast])) hℓv
    have h2 : -((ℓn : ℝ) * (aRTSTarget A Y θ₀ T n ω k' - v)) ≤ Cρ * √(n * log (log n)) := by
      refine le_trans (le_trans (neg_le_abs _) ?_) hnv
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hℓle) (abs_nonneg _)
    rw [hsplit]; linarith
  -- Assemble: `Dev ≤ 1 + small_ℓ + Uincr ≤ 1 + (Cs + 2CM' + Cρ' + Cρ) rate ≤ C rate`.
  have hDev : count (fun j ↦ actionIndicator A k' j ω) n - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k'
      ≤ 1 + (2 * CM' * √(n * log (log n)) + (Cρ' + Cρ) * √(n * log (log n))
        + Cs * √(n * log (log n))) := by
    have := hgen
    simp only [hℓndef] at this hCsn hUle
    linarith [hUle, hdrift, hMbound, hρbound, hCsn]
  have hone : (1 : ℝ) ≤ √(n * log (log n)) := hrn
  nlinarith [hDev, hone, sqrt_nonneg ((n : ℝ) * log (log n))]

/-- **Per-arm one-sided a.s. loglog deviation bound for the aRTS design.** The `aRTS`
instantiation of `dev_upper_of_hitting` at the last under-sampling time: the estimator consistency
and loglog rate come from the `aRTS_LLN` bundle (`aRTS_theta_consistent`, `aRTS_rho_rate`), the
throttle from `throttle_of_isARTS`, and the smallness is automatic — at the last under-sampling time
`N_ℓ - ℓ ρ̂_ℓ ≤ 0` (`preliminary_small`), so it is trivially `O(√(n log log n))`. -/
lemma aRTS_dev_upper [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1) (hARTS : IsARTS alg θ₀ T α)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means) (k' : 𝓐) :
    ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      ((pullCount A k' n ω : ℝ)
        - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k') ≤ C * √(n * log (log n)) :=
  dev_upper_of_hitting h θ₀ T hlip.continuous hTnn α hα hα1 hTpos
    (aRTS_theta_consistent h hνk hlip.continuous hTnn hTsum hα hARTS hTpos)
    (aRTSUnder A Y θ₀ T) (fun k ↦ throttle_of_isARTS h hARTS k) k'
    (aRTS_rho_rate h hνk hlip.continuous hTnn hTsum hα hARTS hTpos hT_diff k')
    (Eventually.of_forall fun ω ↦ ⟨0, Eventually.of_forall fun n ↦ by
      rw [zero_mul, ← count_indicator_eq_pullCount]
      exact preliminary_small (fun j ↦ actionIndicator A k' j ω)
        (fun m ↦ aRTSTarget A Y θ₀ T m ω k') (aRTSUnder A Y θ₀ T k' ω) n
        (fun m hm ↦ by rwa [count_indicator_eq_pullCount])⟩)

/-- **A.s. loglog deviation between proportions and plug-in target at an abstract hitting time**
(Theorem 4.2 (i) of the paper, equation (6), generic form).
The abstract-hitting-time generalisation of `aRTS_prop_dev_ae`: from the per-arm one-sided bounds
`dev_upper_of_hitting` (for *all* arms) via the simplex reverse step
`isBigO_of_forall_upper_of_sum_zero`, whose `∑_k Dev_k = 0` input is `sum_count_sub_smul_eq_zero`.
The design enters only through `hθconv`, the throttle `hthrottle`, the per-arm loglog rate `hρrate`,
and the per-arm smallness `hsmall_upper`. -/
lemma prop_dev_ae_of_hitting [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hθconv : ∀ᵐ ω ∂P, Tendsto (fun n k'' ↦ estimator (fun j ↦ actionIndicator A k'' j ω)
      (Y · ω) (θ₀ k'') n) atTop (𝓝 ν.means))
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k h.filtration P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hρrate : ∀ k', ∀ᵐ ω ∂P, (fun n ↦ T (fun k'' ↦ estimator (fun j ↦ actionIndicator A k'' j ω)
      (Y · ω) (θ₀ k'') n) k' - T ν.means k')
        =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)))
    (hsmall_upper : ∀ k', ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      ((pullCount A k' (hitting (Q k' ω) n) ω : ℝ)
        - (hitting (Q k' ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k' ω) n) ω k')
          ≤ C * √(n * log (log n))) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ (pullCount A k n ω : ℝ) - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k)
      =O[atTop] fun n ↦ √(n * log (log n)) := by
  classical
  have hupper : ∀ k', ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      count (fun j ↦ actionIndicator A k' j ω) n
        - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k' ≤ C * √(n * log (log n)) := fun k' ↦ by
    simpa only [← count_indicator_eq_pullCount] using
      dev_upper_of_hitting h θ₀ T hT hTnn α hα hα1 hTpos hθconv Q hthrottle k'
        (hρrate k') (hsmall_upper k')
  filter_upwards [ae_all_iff.mpr hupper] with ω hω
  simp only [← count_indicator_eq_pullCount]
  refine isBigO_of_forall_upper_of_sum_zero
    (Dev := fun k' n ↦ count (fun j ↦ actionIndicator A k' j ω) n
      - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k') (fun n ↦ ?_) hω k
  exact sum_count_sub_smul_eq_zero (fun j k' ↦ actionIndicator A k' j ω)
    (fun k' ↦ aRTSTarget A Y θ₀ T n ω k') (fun j ↦ sum_actionIndicator A j ω)
    (by simp only [aRTSTarget]; exact hTsum _) n

/-- **A.s. loglog deviation between proportions and plug-in target for the aRTS design**
(Theorem 4.2 (i) of the paper, equation (6)). For every arm `k`, almost surely
`N_{n,k} - n ρ̂_{n,k} = O(√(n log log n))`.

The `aRTS` instantiation of `prop_dev_ae_of_hitting`: the estimator consistency and loglog rate
come from the `aRTS_LLN` bundle, the throttle from `throttle_of_isARTS`, and the smallness is
automatic (`N_ℓ - ℓ ρ̂_ℓ ≤ 0`, `preliminary_small`). Condition **A** (`hνk`) and the Condition
**B** differentiability `hT_diff` feed the loglog rate `aRTS_rho_rate`. -/
theorem aRTS_prop_dev_ae [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1) (hARTS : IsARTS alg θ₀ T α)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ (pullCount A k n ω : ℝ) - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k)
      =O[atTop] fun n ↦ √(n * log (log n)) :=
  prop_dev_ae_of_hitting h θ₀ T hlip.continuous hTnn hTsum α hα hα1 hTpos
    (aRTS_theta_consistent h hνk hlip.continuous hTnn hTsum hα hARTS hTpos)
    (aRTSUnder A Y θ₀ T) (fun k ↦ throttle_of_isARTS h hARTS k)
    (fun k' ↦ aRTS_rho_rate h hνk hlip.continuous hTnn hTsum hα hARTS hTpos hT_diff k')
    (fun k' ↦ Eventually.of_forall fun ω ↦ ⟨0, Eventually.of_forall fun n ↦ by
      rw [zero_mul, ← count_indicator_eq_pullCount]
      exact preliminary_small (fun j ↦ actionIndicator A k' j ω)
        (fun m ↦ aRTSTarget A Y θ₀ T m ω k') (aRTSUnder A Y θ₀ T k' ω) n
        (fun m hm ↦ by rwa [count_indicator_eq_pullCount])⟩) k

/-- **A.s. loglog deviation between the count and the target proportion at an abstract hitting
time** (Theorem 4.2 (i) of the paper, equation (7), generic form). For every arm `k`, almost surely
`N_{n,k} - n v_k = O(√(n log log n))`. Writing
`N_{n,k} - n v_k = (N_{n,k} - n ρ̂_{n,k}) + n(ρ̂_{n,k} - v_k)`, the first term is
`prop_dev_ae_of_hitting` and the second is `n · O(√(n log log n)/n) = O(√(n log log n))` by the
loglog rate `hρrate` and `isBigO_natMul_sqrt_mul_log_log`. -/
lemma count_sub_smul_ae_of_hitting [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hθconv : ∀ᵐ ω ∂P, Tendsto (fun n k'' ↦ estimator (fun j ↦ actionIndicator A k'' j ω)
      (Y · ω) (θ₀ k'') n) atTop (𝓝 ν.means))
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k h.filtration P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hρrate : ∀ k', ∀ᵐ ω ∂P, (fun n ↦ T (fun k'' ↦ estimator (fun j ↦ actionIndicator A k'' j ω)
      (Y · ω) (θ₀ k'') n) k' - T ν.means k')
        =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)))
    (hsmall_upper : ∀ k', ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      ((pullCount A k' (hitting (Q k' ω) n) ω : ℝ)
        - (hitting (Q k' ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k' ω) n) ω k')
          ≤ C * √(n * log (log n))) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ (pullCount A k n ω : ℝ) - (n : ℝ) * T ν.means k)
      =O[atTop] fun n ↦ √(n * log (log n)) := by
  filter_upwards [prop_dev_ae_of_hitting h θ₀ T hT hTnn hTsum α hα hα1 hTpos hθconv Q hthrottle
    hρrate hsmall_upper k, hρrate k] with ω hdev hrate
  have hrate2 : (fun n : ℕ ↦ (n : ℝ) * (aRTSTarget A Y θ₀ T n ω k - T ν.means k))
      =O[atTop] fun n ↦ √(n * log (log n)) := isBigO_natMul_sqrt_mul_log_log hrate
  have hsum := hdev.add hrate2
  refine hsum.congr' (Eventually.of_forall fun n ↦ ?_) (Eventually.of_forall fun n ↦ rfl)
  simp only [aRTSTarget]; ring

/-- **A.s. loglog deviation between the count and the target proportion for the aRTS design**
(Theorem 4.2 (i) of the paper, equation (7)). For every arm `k`, almost surely
`N_{n,k} - n v_k = O(√(n log log n))`, where `v_k = T ν.means k` is the limiting proportion.
The `aRTS` instantiation of `count_sub_smul_ae_of_hitting`. -/
theorem aRTS_count_sub_smul_ae [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1) (hARTS : IsARTS alg θ₀ T α)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ (pullCount A k n ω : ℝ) - (n : ℝ) * T ν.means k)
      =O[atTop] fun n ↦ √(n * log (log n)) :=
  count_sub_smul_ae_of_hitting h θ₀ T hlip.continuous hTnn hTsum α hα hα1 hTpos
    (aRTS_theta_consistent h hνk hlip.continuous hTnn hTsum hα hARTS hTpos)
    (aRTSUnder A Y θ₀ T) (fun k ↦ throttle_of_isARTS h hARTS k)
    (fun k' ↦ aRTS_rho_rate h hνk hlip.continuous hTnn hTsum hα hARTS hTpos hT_diff k')
    (fun k' ↦ Eventually.of_forall fun ω ↦ ⟨0, Eventually.of_forall fun n ↦ by
      rw [zero_mul, ← count_indicator_eq_pullCount]
      exact preliminary_small (fun j ↦ actionIndicator A k' j ω)
        (fun m ↦ aRTSTarget A Y θ₀ T m ω k') (aRTSUnder A Y θ₀ T k' ω) n
        (fun m hm ↦ by rwa [count_indicator_eq_pullCount])⟩) k

end ARTS

end AlphaRAR
