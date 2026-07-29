/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.PropDev
import AlphaRAR.YDK2026.ARTSAlgorithm
import AlphaRAR.YDK2026.ResponseIncrement
import AlphaRAR.YDK2026.PluginTargetCLT

/-!
# The `o_p(√n)` proportion-deviation bound for the aRTS design

This file instantiates the generic deviation theorem `AlphaRAR.prop_dev` for the concrete aRTS
design, giving the paper-form statement (blueprint `lem:prop_dev`, `thm:normality` part (i),
`o_p(√n)` half): for every arm `k`,
`|N_{n,k} - n ρ̂_{n,k}| = o_p(√n)`, where `N_{n,k}` is the allocation count and `ρ̂_{n,k}` the
plug-in target.

Everything is derived from the aRTS design bundle (an `IsAlgEnvSeq` algorithm–environment sequence
under Condition **A** `hY2`, the throttle, `α ∈ [0,1)`) plus Condition **B** (the target map `T`
Lipschitz near `θ`, non-sparsity `v_k > 0`, and the a.s. consistency `N/n → v`, `θ̂ → θ` from
`thm:LLN`).

## Main results

* `AlphaRAR.aRTS_prop_dev`.
-/

open MeasureTheory ProbabilityTheory Filter Learning Finset
open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- **Measurability of a process evaluated at a measurable, bounded random time.** If each
`ω ↦ H ω m` is measurable and `g : Ω → ℕ` is measurable with `g ω ≤ n`, then `ω ↦ H ω (g ω)` is
measurable (finite-sum-of-indicators over `range (n+1)`). -/
lemma measurable_eval_of_le {H : Ω → ℕ → ℝ} (hH : ∀ m, Measurable (fun ω ↦ H ω m))
    {g : Ω → ℕ} (hg : Measurable g) {n : ℕ} (hgn : ∀ ω, g ω ≤ n) :
    Measurable (fun ω ↦ H ω (g ω)) := by
  have heq : (fun ω ↦ H ω (g ω))
      = fun ω ↦ ∑ m ∈ Finset.range (n + 1), if g ω = m then H ω m else 0 := by
    funext ω
    rw [Finset.sum_ite_eq (Finset.range (n + 1)) (g ω) (fun m ↦ H ω m),
      if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (hgn ω)))]
  rw [heq]
  exact Finset.measurable_sum _ fun m _ ↦
    Measurable.ite (hg (measurableSet_singleton m)) (hH m) measurable_const

/-- Measurability of the plug-in-target coordinate `ω ↦ ρ̂_{n,k}(ω)`. -/
lemma measurable_aRTSTarget_coord [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (n : ℕ) (k' : 𝓐) :
    Measurable (fun ω ↦ aRTSTarget A Y θ₀ T n ω k') := by
  cases nonempty_fintype 𝓐
  simp only [aRTSTarget]
  exact (measurable_pi_apply k').comp (hT.measurable.comp (measurable_estimatorVec h θ₀ n))

/-- **Measurability of an abstract last-hitting time.** For a per-path predicate `Q : Ω → ℕ → Prop`
whose level sets `{ω | Q ω m}` are all measurable, the last-hitting time `ω ↦ hitting (Q ω) n` is
measurable (`Nat.findGreatest` of a measurable family). This is the design-independent core of the
hitting-time measurability, used for both `aRTSUnder` and the forced-exploration predicate. -/
lemma measurable_hitting {Q : Ω → ℕ → Prop} [∀ ω, DecidablePred (Q ω)]
    (hQmeas : ∀ m, MeasurableSet {ω | Q ω m}) (n : ℕ) :
    Measurable (fun ω ↦ hitting (Q ω) n) := by
  apply measurable_findGreatest
  intro m _
  exact hQmeas m

/-- The level sets of the aRTS under-sampling predicate are measurable. -/
lemma measurableSet_aRTSUnder [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (k' : 𝓐) (m : ℕ) :
    MeasurableSet {ω | aRTSUnder A Y θ₀ T k' ω m} :=
  measurableSet_le (measurable_count_armIndicator h k' m)
    ((measurable_aRTSTarget_coord h θ₀ hT m k').const_mul _)

/-- Measurability of the aRTS hitting time `ω ↦ ℓ_{n,k}(ω)`. -/
lemma measurable_hitting_aRTSUnder [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (k' : 𝓐) (n : ℕ) :
    Measurable (fun ω ↦ hitting (aRTSUnder A Y θ₀ T k' ω) n) :=
  measurable_hitting (measurableSet_aRTSUnder h θ₀ hT k') n

/-- **Uniform bound on `m/(N_m+1)` from `N_m/m → v > 0`.** If `N_m ≥ 0` and `N_m/m → v > 0`, then
`m/(N_m+1)` is bounded uniformly in `m` (it converges to `1/v`). This is the pathwise ingredient
behind the `O_p(1)` reweighting coefficient of `ell_rho_control`. -/
lemma exists_bound_natCast_div {N : ℕ → ℝ} {v : ℝ} (hv : 0 < v) (hN : ∀ m, 0 ≤ N m)
    (hlim : Tendsto (fun m ↦ N m / (m : ℝ)) atTop (𝓝 v)) :
    ∃ B, ∀ m : ℕ, (m : ℝ) / (N m + 1) ≤ B := by
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_gt_nhds (half_lt_self hv)))
  refine ⟨max (2 / v) (m₀ : ℝ), fun (m : ℕ) ↦ ?_⟩
  have hNpos : 0 < N m + 1 := by linarith [hN m]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0; simp only [Nat.cast_zero, zero_div, le_max_iff]; left; positivity
  rcases lt_or_ge m m₀ with hmlt | hmge
  · refine le_trans ?_ (le_max_right _ _)
    have hmm₀ : (m : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hmlt.le
    rw [div_le_iff₀ hNpos]
    nlinarith [hN m, hmm₀]
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hgt : v / 2 < N m / (m : ℝ) := hm₀ m hmge
    rw [lt_div_iff₀ hmR] at hgt
    refine le_trans ?_ (le_max_left _ _)
    rw [div_le_div_iff₀ hNpos hv]
    nlinarith [hgt]

/-- Count of a fixed arm is nonnegative. -/
lemma count_armIndicator_nonneg (A : ℕ → Ω → 𝓐) (k'' : 𝓐) (m : ℕ) (ω : Ω) :
    0 ≤ count (fun j ↦ armIndicator A k'' j ω) m :=
  Finset.sum_nonneg fun j _ ↦ armIndicator_nonneg A k'' j ω

/-- Measurability of `ω ↦ (hitting (Q ω) n : ℝ)` for a measurable-level-set predicate `Q`. -/
lemma measurable_hitting_cast {Q : Ω → ℕ → Prop} [∀ ω, DecidablePred (Q ω)]
    (hQmeas : ∀ m, MeasurableSet {ω | Q ω m}) (n : ℕ) :
    Measurable (fun ω ↦ ((hitting (Q ω) n : ℕ) : ℝ)) :=
  measurable_eval_of_le (H := fun _ m ↦ (m : ℝ)) (fun _ ↦ measurable_const)
    (measurable_hitting hQmeas n) (fun _ ↦ Nat.findGreatest_le n)

/-- **The reweighting coefficient `ℓ_{n}/(N_{n,k''}+1)` is `O_p(1)`** (converging a.s. to
`1/v_{k''}`), for an abstract hitting time `hitting (Q ·) n ≤ n`. This is the coefficient `h` fed to
`ell_rho_control`; the argument only uses `ℓ ≤ n` and the proportion consistency, so it is
design-independent (the `aRTS`/`aRTSFE` hitting times just supply the measurable predicate `Q`). -/
lemma h_bigOp_of_hitting (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    {Q : Ω → ℕ → Prop} [∀ ω, DecidablePred (Q ω)] (hQmeas : ∀ m, MeasurableSet {ω | Q ω m})
    (k'' : 𝓐) {v : ℝ} (hv : 0 < v)
    (hN : ∀ᵐ ω ∂P, Tendsto (fun m ↦ count (fun j ↦ armIndicator A k'' j ω) m / (m : ℝ))
      atTop (𝓝 v)) :
    IsBigOpOne P (fun n ω ↦ (hitting (Q ω) n : ℝ)
      / (count (fun j ↦ armIndicator A k'' j ω) n + 1)) := by
  refine isBigOpOne_of_ae_bounded (fun n ↦ (measurable_hitting_cast hQmeas n).div
    ((measurable_count_armIndicator h k'' n).add_const 1)) ?_
  filter_upwards [hN] with ω hNω
  obtain ⟨B, hB⟩ := exists_bound_natCast_div
    (N := fun m ↦ count (fun j ↦ armIndicator A k'' j ω) m) hv
    (fun m ↦ count_armIndicator_nonneg A k'' m ω) hNω
  refine ⟨B, fun n ↦ ?_⟩
  have hden : (0 : ℝ) < count (fun j ↦ armIndicator A k'' j ω) n + 1 := by
    linarith [count_armIndicator_nonneg A k'' n ω]
  rw [abs_of_nonneg (by positivity)]
  calc (hitting (Q ω) n : ℝ) / (count (fun j ↦ armIndicator A k'' j ω) n + 1)
      ≤ (n : ℝ) / (count (fun j ↦ armIndicator A k'' j ω) n + 1) := by
        gcongr; exact_mod_cast Nat.findGreatest_le n
    _ ≤ B := hB n

/-- **`√n/(N_{n,k''}+1) → 0` a.s.** from `N_{n,k''}/n → v > 0`. -/
lemma tendsto_sqrt_div_count (k'' : 𝓐) {v : ℝ} (hv : 0 < v)
    {ω : Ω} (hNω : Tendsto (fun m ↦ count (fun j ↦ armIndicator A k'' j ω) m / (m : ℝ))
      atTop (𝓝 v)) :
    Tendsto (fun n : ℕ ↦ √n / (count (fun j ↦ armIndicator A k'' j ω) n + 1))
      atTop (𝓝 0) := by
  have hden : Tendsto
      (fun n ↦ (count (fun j ↦ armIndicator A k'' j ω) n + 1) / √n) atTop atTop := by
    have hsqrt : Tendsto (fun n : ℕ ↦ √n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp
      (hNω.eventually (eventually_gt_nhds (half_lt_self hv)))
    refine tendsto_atTop_mono' _ ?_ (Tendsto.const_mul_atTop (half_pos hv) hsqrt)
    filter_upwards [eventually_ge_atTop (max 1 m₀)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr hnR
    have hgt : v / 2 < count (fun j ↦ armIndicator A k'' j ω) n / (n : ℝ) :=
      hm₀ n (le_trans (le_max_right _ _) hn)
    rw [lt_div_iff₀ hnR] at hgt
    rw [le_div_iff₀ hsn]
    have hsqn : √n * √n = (n : ℝ) := Real.mul_self_sqrt hnR.le
    nlinarith [hgt, count_armIndicator_nonneg A k'' n ω, hsn, hsqn]
  simpa using hden.inv_tendsto_atTop.congr (fun n ↦ (inv_div _ _))

/-- **The `g`-coefficient of `ell_rho_control` is `o_p(1)`**, at an abstract measurable hitting time
`hitting (Q ·) n ≤ n`. With `g = ℓ(|Q_ℓ| + |θ_0-θ|)/((N_ℓ+1)(N_n+1))`, write `g = F₁·F₂` with
`F₁ = ℓ/(N_ℓ+1) = O_p(1)` (a.s. bounded) and `F₂ = (|Q_ℓ|+|a|)/(N_n+1) = o_p(1)` (via the Doob
running-max `sup_{m≤n}|Q_m| = O_p(√n)` and `√n/(N_n+1) → 0`); then `O_p·o_p = o_p`. The argument
uses only `ℓ ≤ n` and measurability of `Q`, so it is design-independent. -/
lemma g_littleOp_of_hitting (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ)
    {Q : Ω → ℕ → Prop} [∀ ω, DecidablePred (Q ω)] (hQmeas : ∀ m, MeasurableSet {ω | Q ω m})
    (k'' : 𝓐) {v : ℝ} (hv : 0 < v)
    (hN : ∀ᵐ ω ∂P, Tendsto (fun m ↦ count (fun j ↦ armIndicator A k'' j ω) m / (m : ℝ))
      atTop (𝓝 v)) :
    IsLittleOpOne P (fun n ω ↦ (hitting (Q ω) n : ℝ)
      * (|respMart ν A Y k'' (hitting (Q ω) n) ω| + |θ₀ k'' - (ν k'')[id]|)
      / ((count (fun j ↦ armIndicator A k'' j ω) (hitting (Q ω) n) + 1)
        * (count (fun j ↦ armIndicator A k'' j ω) n + 1))) := by
  have hint : ∀ n, Integrable (Y n) P := fun n ↦ (hY2 n).integrable one_le_two
  set ℓ : ℕ → Ω → ℕ := fun n ω ↦ hitting (Q ω) n with hℓ
  set Nc : ℕ → Ω → ℝ := fun n ω ↦ count (fun j ↦ armIndicator A k'' j ω) n with hNc
  have hNcnn : ∀ m ω, 0 ≤ Nc m ω := fun m ω ↦ count_armIndicator_nonneg A k'' m ω
  set a : ℝ := |θ₀ k'' - (ν k'')[id]| with ha
  -- F₁ = ℓ/(N_ℓ+1) is O_p (a.s. bounded).
  have hF1 : IsBigOpOne P (fun n ω ↦ (ℓ n ω : ℝ) / (Nc (ℓ n ω) ω + 1)) := by
    refine isBigOpOne_of_ae_bounded (fun n ↦ ?_) ?_
    · exact measurable_eval_of_le (H := fun ω m ↦ (m : ℝ) / (Nc m ω + 1))
        (fun m ↦ measurable_const.div ((measurable_count_armIndicator h k'' m).add_const 1))
        (measurable_hitting hQmeas n) (fun _ ↦ Nat.findGreatest_le n)
    · filter_upwards [hN] with ω hNω
      obtain ⟨B, hB⟩ := exists_bound_natCast_div (N := fun m ↦ Nc m ω) hv
        (fun m ↦ count_armIndicator_nonneg A k'' m ω) hNω
      refine ⟨B, fun n ↦ ?_⟩
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith [hNcnn (ℓ n ω) ω]))]
      exact hB (ℓ n ω)
  -- Doob running-max `S_n = sup_{m≤n}|Q_m| = O_p(√n)`.
  set Sseq : ℕ → Ω → ℝ := fun n ω ↦ (Finset.range (n + 1)).sup' nonempty_range_add_one
    (fun m ↦ |respMart ν A Y k'' m ω|) with hSseq
  have hSOp : IsBigOpOne P (fun n ω ↦ Sseq n ω / √n) := by
    refine isBigOpOne_sup'_abs_div_sqrt (martingale_respMart h hint k'')
      (fun n ↦ (memLp_respMart h.measurable_action hY2 k'' n).integrable_sq)
      (ae_of_all _ fun ω ↦ by simp [respMart, Finset.range_zero]) (Var[id; ν k''])
      (variance_nonneg _ _) ?_ ?_
      (fun n ↦ integral_respMart_increment_sq_le h k'' n (hY2 n))
    · intro n
      have heq : (fun ω ↦ (respMart ν A Y k'' (n + 1) ω - respMart ν A Y k'' n ω) ^ 2)
          = fun ω ↦ (armIndicator A k'' n ω * (Y n ω - (ν k'')[id])) ^ 2 := by
        funext ω; rw [respMart_succ]; simp only [Pi.add_apply]; ring
      rw [heq]
      exact integrable_respMart_increment_sq k'' (h.measurable_action n)
        (((hY2 n).sub (memLp_const _)).integrable_sq)
    · exact fun n ↦ (memLp_respMart h.measurable_action hY2 k'' n).integrable_mul
        ((memLp_respMart h.measurable_action hY2 k'' (n + 1)).sub
          (memLp_respMart h.measurable_action hY2 k'' n))
  have hSseqnn : ∀ n ω, 0 ≤ Sseq n ω := fun n ω ↦ by
    rw [hSseq]
    exact le_trans (abs_nonneg (respMart ν A Y k'' 0 ω))
      (Finset.le_sup' (f := fun m ↦ |respMart ν A Y k'' m ω|)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hann : (0 : ℝ) ≤ a := ha ▸ abs_nonneg _
  -- F₂ = (|Q_ℓ|+|a|)/(N_n+1) is o_p.
  have hF2 : IsLittleOpOne P (fun n ω ↦
      (|respMart ν A Y k'' (ℓ n ω) ω| + a) / (Nc n ω + 1)) := by
    have hprodop : IsLittleOpOne P (fun n ω ↦
        (Sseq n ω / √n + a / √n) * (√n / (Nc n ω + 1))) := by
      have hOpseq : IsBigOpOne P (fun n ω ↦ Sseq n ω / √n + a / √n) :=
        hSOp.add ((isLittleOpOne_const_div_sqrt a).isBigOpOne (fun _ ↦ aemeasurable_const))
      have hopseq : IsLittleOpOne P (fun n ω ↦ √n / (Nc n ω + 1)) := by
        refine isLittleOpOne_of_tendsto_ae (fun n ↦ (measurable_const.div
          ((measurable_count_armIndicator h k'' n).add_const 1)).aestronglyMeasurable) ?_
        filter_upwards [hN] with ω hNω
        exact tendsto_sqrt_div_count k'' hv hNω
      exact hOpseq.mul_littleOp hopseq
    refine IsLittleOpOne.of_eventually_abs_le ?_ hprodop
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine ae_of_all _ fun ω ↦ ?_
    have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hden : (0 : ℝ) < Nc n ω + 1 := by linarith [hNcnn n ω]
    have hSge : |respMart ν A Y k'' (ℓ n ω) ω| ≤ Sseq n ω := by
      rw [hSseq]
      exact Finset.le_sup' (f := fun m ↦ |respMart ν A Y k'' m ω|)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.findGreatest_le n)))
    have hprodeq : (Sseq n ω / √n + a / √n) * (√n / (Nc n ω + 1))
        = (Sseq n ω + a) / (Nc n ω + 1) := by field_simp
    have hnum : 0 ≤ |respMart ν A Y k'' (ℓ n ω) ω| + a := by
      linarith [abs_nonneg (respMart ν A Y k'' (ℓ n ω) ω)]
    rw [abs_of_nonneg (div_nonneg hnum hden.le), hprodeq,
      abs_of_nonneg (div_nonneg (by linarith [hSseqnn n ω]) hden.le)]
    gcongr
  -- g = F₁ · F₂.
  have hgeq : (fun n ω ↦ (ℓ n ω : ℝ)
      * (|respMart ν A Y k'' (ℓ n ω) ω| + |θ₀ k'' - (ν k'')[id]|)
      / ((Nc (ℓ n ω) ω + 1) * (Nc n ω + 1)))
      = fun n ω ↦ ((ℓ n ω : ℝ) / (Nc (ℓ n ω) ω + 1))
        * ((|respMart ν A Y k'' (ℓ n ω) ω| + |θ₀ k'' - (ν k'')[id]|) / (Nc n ω + 1)) := by
    funext n ω; rw [div_mul_div_comm]
  rw [hgeq]
  exact hF1.mul_littleOp hF2

/-- **Deviation between proportions and plug-in target at an abstract hitting time** (blueprint
`lem:prop_dev`, `thm:normality` part (i), `o_p(√n)` half, generic form). The abstract-hitting-time
generalisation of `aRTS_prop_dev`: for any per-arm predicate `Q` with measurable level sets
(`hQmeas`), given the `thm:LLN` consistencies `θ̂ → θ` (`hθconv`) and `N/n → v` (`hNconv`), the
throttle `¬ Q → p ≤ α ρ̂` (`hthrottle`), and the smallness `o_p`-bound `hsmall_op` (that
`(1 + N_ℓ - ℓ ρ̂_ℓ)^+/√n = o_p(1)`), the deviation `N_{n,k} - n ρ̂_{n,k} = o_p(√n)`. Everything
else —
the key inequality `generic_ineq_of_hitting`, the `diff_U_decomp` perturbation, the assignment-
martingale `M`-increment, and the `ell_rho_control` `g`/`h`-coefficients (`g_littleOp_of_hitting`,
`h_bigOp_of_hitting`) — depends only on `hitting (Q k ·) n ≤ n`, so it is discharged uniformly. The
`aRTS`/`aRTSFE` designs then instantiate it with their respective predicates. -/
lemma prop_dev_of_hitting [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hθconv : ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ armIndicator A k' j ω)
      (fun j ↦ Y j ω) (θ₀ k') n) atTop (𝓝 (fun k ↦ (ν k)[id])))
    (hNconv : ∀ k', ∀ᵐ ω ∂P, Tendsto (fun n ↦ count (fun j ↦ armIndicator A k' j ω) n / (n : ℝ))
      atTop (𝓝 (T (fun k'' ↦ (ν k'')[id]) k')))
    (Q : 𝓐 → Ω → ℕ → Prop) [∀ k ω, DecidablePred (Q k ω)]
    (hQmeas : ∀ k m, MeasurableSet {ω | Q k ω m})
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ Q k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hsmall_op : ∀ k, IsLittleOpOne P (fun n ω ↦
      max ((1 + (count (fun j ↦ armIndicator A k j ω) (hitting (Q k ω) n)
        - (hitting (Q k ω) n : ℝ) * aRTSTarget A Y θ₀ T (hitting (Q k ω) n) ω k)) / √n) 0))
    (k : 𝓐) :
    IsLittleOpOne P (fun n ω ↦ ((pullCount A k n ω : ℝ)
      - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k) / √n) := by
  classical
  -- `N_{n,k}` in pull-count form is the count of the assignment indicator.
  simp only [← count_indicator_eq_pullCount]
  -- Continuity and the `ℓ¹`-form Lipschitz bound both follow from `LipschitzWith K T`.
  set L : ℝ := (K : ℝ) with hLdef
  have hT : Continuous T := hlip.continuous
  -- The non-sparsity `0 < v_k` (the mean `(ν k)[id]` lies in every `attainableSet`, so `hTpos`
  -- applies), from the estimator consistency `hθconv`.
  have hmem : ∀ k', (ν k')[id] ∈ attainableSet A Y (θ₀ k') k' := by
    obtain ⟨ω, hω⟩ := hθconv.exists
    exact fun k' ↦ estimator_limit_mem_attainableSet k' (θ₀ k') (tendsto_pi_nhds.mp hω k')
  have hv : ∀ k, 0 < T (fun k' ↦ (ν k')[id]) k := fun k ↦ hTpos (fun k ↦ (ν k)[id]) hmem k
  have hL : (0 : ℝ) ≤ L := K.coe_nonneg
  have hTlip : ∀ z z' : 𝓐 → ℝ, ∀ k, |T z k - T z' k| ≤ L * ∑ k', |z k' - z' k'| := by
    intro z z' k
    calc |T z k - T z' k| = dist (T z k) (T z' k) := (Real.dist_eq _ _).symm
      _ ≤ dist (T z) (T z') := dist_le_pi_dist (T z) (T z') k
      _ ≤ L * dist z z' := hlip.dist_le_mul z z'
      _ ≤ L * ∑ k', |z k' - z' k'| := by
          refine mul_le_mul_of_nonneg_left ?_ hL
          have hrnn : (0 : ℝ) ≤ ∑ k', |z k' - z' k'| :=
            Finset.sum_nonneg fun i _ ↦ abs_nonneg (z i - z' i)
          rw [dist_pi_le_iff hrnn]
          intro k'
          rw [Real.dist_eq]
          exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (z i - z' i)) (Finset.mem_univ k')
  set ℱ := IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback with hℱ
  -- Concrete objects (the hitting time is the abstract `hitting (Q k ·) n`).
  set ℓ : 𝓐 → ℕ → Ω → ℕ := fun k n ω ↦ hitting (Q k ω) n with hℓdef
  set Dev : 𝓐 → ℕ → Ω → ℝ := fun k n ω ↦
    count (fun j ↦ armIndicator A k j ω) n - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k with hDevdef
  set d : 𝓐 → ℕ → Ω → ℝ := fun k n ω ↦ (n : ℝ) - (ℓ k n ω : ℝ) with hddef
  set small : 𝓐 → ℕ → Ω → ℝ := fun k n ω ↦
    1 + (count (fun j ↦ armIndicator A k j ω) (ℓ k n ω)
      - (ℓ k n ω : ℝ) * aRTSTarget A Y θ₀ T (ℓ k n ω) ω k) with hsmalldef
  set Uincr : 𝓐 → ℕ → Ω → ℝ := fun k n ω ↦
    auxU (fun j ↦ armIndicator A k j ω) (fun j ↦ aRTSSelProb A k ℱ P j ω)
        (fun j ↦ aRTSTarget A Y θ₀ T j ω k) α n
      - auxU (fun j ↦ armIndicator A k j ω) (fun j ↦ aRTSSelProb A k ℱ P j ω)
        (fun j ↦ aRTSTarget A Y θ₀ T j ω k) α (ℓ k n ω) with hUdef
  set Mincr : 𝓐 → ℕ → Ω → ℝ := fun k n ω ↦
    assignMG (fun j ↦ armIndicator A k j ω) (fun j ↦ aRTSSelProb A k ℱ P j ω) n
      - assignMG (fun j ↦ armIndicator A k j ω) (fun j ↦ aRTSSelProb A k ℱ P j ω) (ℓ k n ω)
    with hMdef
  set rhoterm : 𝓐 → ℕ → Ω → ℝ := fun k n ω ↦
    (ℓ k n ω : ℝ) * (aRTSTarget A Y θ₀ T (ℓ k n ω) ω k - aRTSTarget A Y θ₀ T n ω k) with hrhodef
  set c : 𝓐 → ℝ := fun k ↦ (1 - α) * T (fun k' ↦ (ν k')[id]) k with hcdef
  set pert : 𝓐 → ℕ → Ω → ℝ := fun k n ω ↦
    (Uincr k n ω - (-c k * d k n ω + Mincr k n ω + rhoterm k n ω)) / d k n ω with hpertdef
  -- M-increment control coefficients (assignment martingale, singleton family).
  set VM : 𝓐 → ℕ → Ω → ℝ := fun k ↦
    vmaxSeq (fun _ : Unit ↦ assignMart (fun j ↦ armIndicator A k j) ℱ P) with hVMdef
  set WM : 𝓐 → ℕ → Ω → ℝ := fun k ↦
    wmaxSeq (fun _ : Unit ↦ assignMart (fun j ↦ armIndicator A k j) ℱ P) with hWMdef
  -- Assignment-martingale facts (per arm): it is an `ℱ.shiftDown`-martingale started at `0` with
  -- increments `|ΔM| ≤ 1`, so `qm_increments_of_bdd` gives the `o_p` increment maxima.
  have hMmart : ∀ k', Martingale (assignMart (fun j ↦ armIndicator A k' j) ℱ P) ℱ.shiftDown P :=
    fun k' ↦ martingale_assignMart
      (stronglyAdapted_armIndicator h.measurable_action h.measurable_feedback k')
      (integrable_armIndicator h.measurable_action P k')
  have hMzero : ∀ k', assignMart (fun j ↦ armIndicator A k' j) ℱ P 0 =ᵐ[P] 0 := fun k' ↦
    ae_of_all _ fun ω ↦ by simp [assignMart, martingalePart_zero, count_zero]
  have hMdelta : ∀ k' n, ∀ᵐ ω ∂P,
      |assignMart (fun j ↦ armIndicator A k' j) ℱ P (n + 1) ω
        - assignMart (fun j ↦ armIndicator A k' j) ℱ P n ω| ≤ 1 := fun k' n ↦
    abs_assignMart_succ_sub_le (integrable_armIndicator h.measurable_action P k')
      (fun m ↦ ae_of_all _ fun ω ↦ armIndicator_nonneg A k' m ω)
      (fun m ↦ ae_of_all _ fun ω ↦ armIndicator_le_one A k' m ω) n
  have hMqm : ∀ k', IsLittleOpOne P (vmaxSeq (fun _ : Unit ↦
        assignMart (fun j ↦ armIndicator A k' j) ℱ P))
      ∧ IsLittleOpOne P (fun n ω ↦ wmaxSeq (fun _ : Unit ↦
        assignMart (fun j ↦ armIndicator A k' j) ℱ P) n ω / √n) := fun k' ↦
    qm_increments_of_bdd (hMmart k') (hMzero k') (by norm_num) (hMdelta k')
  -- The ρ-increment control coefficients from `ell_rho_control`.
  have hρctrl : ∀ k', ∃ Vρ Wρ : ℕ → Ω → ℝ,
      (∀ᶠ n in atTop, ∀ ω, rhoterm k' n ω ≤ Vρ n ω * d k' n ω + Wρ n ω)
        ∧ IsLittleOpOne P Vρ ∧ IsLittleOpOne P (fun n ω ↦ Wρ n ω / √n) := by
    intro k'
    obtain ⟨hQvop, hQwop⟩ := qm_increments_resp h hY2
    refine ell_rho_control (rhoterm := rhoterm k') (d := d k') (L := L)
      (θdiff := fun k'' n ω ↦ (ℓ k' n ω : ℝ)
        * |estimator (fun j ↦ armIndicator A k'' j ω) (fun j ↦ Y j ω) (θ₀ k'') (ℓ k' n ω)
          - estimator (fun j ↦ armIndicator A k'' j ω) (fun j ↦ Y j ω) (θ₀ k'') n|)
      (g := fun k'' n ω ↦ (ℓ k' n ω : ℝ)
        * (|respMart ν A Y k'' (ℓ k' n ω) ω| + |θ₀ k'' - (ν k'')[id]|)
        / ((count (fun j ↦ armIndicator A k'' j ω) (ℓ k' n ω) + 1)
          * (count (fun j ↦ armIndicator A k'' j ω) n + 1)))
      (h := fun k'' n ω ↦ (ℓ k' n ω : ℝ) / (count (fun j ↦ armIndicator A k'' j ω) n + 1))
      (Qinc := fun k'' n ω ↦ |respMart ν A Y k'' n ω - respMart ν A Y k'' (ℓ k' n ω) ω|)
      (Qvinc := vmaxSeq (fun k'' ↦ respMart ν A Y k''))
      (Qwinc := wmaxSeq (fun k'' ↦ respMart ν A Y k''))
      hL ?_ ?_ ?_ ?_ ?_ ?_ hQvop hQwop
    · -- hlip: the Condition-B Lipschitz bound on `T`.
      intro n ω
      simp only [hrhodef, hℓdef]
      have hℓnn : (0 : ℝ) ≤ (hitting (Q k' ω) n : ℝ) := Nat.cast_nonneg _
      have hTb : aRTSTarget A Y θ₀ T (hitting (Q k' ω) n) ω k'
            - aRTSTarget A Y θ₀ T n ω k'
          ≤ L * ∑ k'', |estimator (fun j ↦ armIndicator A k'' j ω) (fun j ↦ Y j ω) (θ₀ k'')
              (hitting (Q k' ω) n)
            - estimator (fun j ↦ armIndicator A k'' j ω) (fun j ↦ Y j ω) (θ₀ k'') n| := by
        refine le_trans (le_abs_self _) ?_
        simp only [aRTSTarget]
        exact hTlip _ _ k'
      calc (hitting (Q k' ω) n : ℝ)
            * (aRTSTarget A Y θ₀ T (hitting (Q k' ω) n) ω k'
              - aRTSTarget A Y θ₀ T n ω k')
          ≤ (hitting (Q k' ω) n : ℝ)
            * (L * ∑ k'', |estimator (fun j ↦ armIndicator A k'' j ω) (fun j ↦ Y j ω) (θ₀ k'')
                (hitting (Q k' ω) n)
              - estimator (fun j ↦ armIndicator A k'' j ω) (fun j ↦ Y j ω) (θ₀ k'') n|) :=
            mul_le_mul_of_nonneg_left hTb hℓnn
        _ = L * ∑ k'', (hitting (Q k' ω) n : ℝ)
              * |estimator (fun j ↦ armIndicator A k'' j ω) (fun j ↦ Y j ω) (θ₀ k'')
                (hitting (Q k' ω) n)
              - estimator (fun j ↦ armIndicator A k'' j ω) (fun j ↦ Y j ω) (θ₀ k'') n| := by
            rw [← Finset.mul_sum]; ring
    · -- hdiff: `abs_estimator_diff_le`, bridged from `respMG` to `respMart`.
      intro k'' n ω
      simp only [hddef, hℓdef]
      have hae := abs_estimator_diff_le (fun j ↦ armIndicator A k'' j ω)
        (fun j ↦ armIndicator_nonneg A k'' j ω)
        (fun j ↦ armIndicator_le_one A k'' j ω) (fun j ↦ Y j ω) ((ν k'')[id]) (θ₀ k'')
        (ℓ := hitting (Q k' ω) n) (Nat.findGreatest_le n)
      simp only [respMG_indicator_eq_respMart] at hae
      exact hae
    · -- hg
      intro k''
      exact g_littleOp_of_hitting h hY2 θ₀ (hQmeas k') k'' (hv k'') (hNconv k'')
    · -- hhnn
      intro k'' n ω
      exact div_nonneg (Nat.cast_nonneg _) (by linarith [count_armIndicator_nonneg A k'' n ω])
    · -- hh
      intro k''
      exact h_bigOp_of_hitting h (hQmeas k') k'' (hv k'') (hNconv k'')
    · -- hQinc: `‖Q_n - Q_ℓ‖ ≤ (n-ℓ)·vmaxSeq + wmaxSeq` (per-coordinate ≤ L² norm), for `n ≥ 2`.
      filter_upwards [eventually_ge_atTop 2] with n hn2
      intro k'' ω
      simp only [hddef, hℓdef]
      have hℓle : hitting (Q k' ω) n ≤ n := Nat.findGreatest_le n
      have hni := norm_increment_le_vmaxSeq_wmaxSeq (M := fun k''' ↦ respMart ν A Y k''')
        n hn2 hℓle ω
      have hcoord : |respMart ν A Y k'' n ω
            - respMart ν A Y k'' (hitting (Q k' ω) n) ω|
          ≤ √(∑ k''', (respMart ν A Y k''' n ω
            - respMart ν A Y k''' (hitting (Q k' ω) n) ω) ^ 2) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum
          (f := fun k''' ↦ (respMart ν A Y k''' n ω
            - respMart ν A Y k''' (hitting (Q k' ω) n) ω) ^ 2)
          (fun i _ ↦ sq_nonneg _) (Finset.mem_univ k''))
      have hcast : ((n - hitting (Q k' ω) n : ℕ) : ℝ)
          = (n : ℝ) - (hitting (Q k' ω) n : ℝ) := by rw [Nat.cast_sub hℓle]
      calc |respMart ν A Y k'' n ω
            - respMart ν A Y k'' (hitting (Q k' ω) n) ω|
          ≤ √(∑ k''', (respMart ν A Y k''' n ω
            - respMart ν A Y k''' (hitting (Q k' ω) n) ω) ^ 2) := hcoord
        _ ≤ ((n - hitting (Q k' ω) n : ℕ) : ℝ)
              * vmaxSeq (fun k''' ↦ respMart ν A Y k''') n ω
            + wmaxSeq (fun k''' ↦ respMart ν A Y k''') n ω := hni
        _ = vmaxSeq (fun k''' ↦ respMart ν A Y k''') n ω
              * ((n : ℝ) - (hitting (Q k' ω) n : ℝ))
            + wmaxSeq (fun k''' ↦ respMart ν A Y k''') n ω := by rw [hcast]; ring
  choose Vρ Wρ hρbd hVρ hWρ using hρctrl
  -- Selection probabilities are `≤ 1` (conditional expectation of a `≤ 1` indicator).
  have hp1 : ∀ k', ∀ᵐ ω ∂P, ∀ m, aRTSSelProb A k' ℱ P m ω ≤ 1 := by
    intro k'
    rw [ae_all_iff]
    intro m
    have hmono := condExp_mono (m := ℱ.shiftDown m)
      (integrable_armIndicator h.measurable_action P k' m)
      (integrable_const (1 : ℝ)) (Eventually.of_forall fun ω ↦ armIndicator_le_one A k' m ω)
    rw [condExp_const (ℱ.shiftDown.le m)] at hmono
    filter_upwards [hmono] with ω hω
    exact hω
  -- Plug-in-target consistency `ρ̂_{n,k} → v_k` from estimator consistency `θ̂ → θ` and `hT`.
  have hρconv : ∀ k', ∀ᵐ ω ∂P, Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k') atTop
      (𝓝 (T (fun k'' ↦ (ν k'')[id]) k')) := by
    intro k'
    filter_upwards [hθconv] with ω hω
    have hTtend : Tendsto (fun n ↦ T (fun k'' ↦ estimator (fun j ↦ armIndicator A k'' j ω)
        (fun j ↦ Y j ω) (θ₀ k'') n)) atTop (𝓝 (T (fun k'' ↦ (ν k'')[id]))) :=
      (hT.tendsto (fun k'' ↦ (ν k'')[id])).comp hω
    exact ((continuous_apply k').tendsto _).comp hTtend
  refine prop_dev (Dev := Dev) (small := small) (Uincr := Uincr) (Mincr := Mincr)
    (rhoterm := rhoterm) (pert := pert) (d := d) (c := c) (VM := VM) (WM := WM)
    (Vρ := Vρ) (Wρ := Wρ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ k
  · -- hsum
    intro n ω
    simp only [hDevdef]
    exact sum_count_sub_smul_eq_zero (fun j k' ↦ armIndicator A k' j ω)
      (fun k' ↦ aRTSTarget A Y θ₀ T n ω k') (fun j ↦ sum_armIndicator A j ω)
      (by simp only [aRTSTarget]; exact hTsum _) n
  · -- hle
    intro k' n
    filter_upwards [hthrottle k', hp1 k'] with ω hthr hp1ω
    simp only [hDevdef, hsmalldef, hUdef, hℓdef]
    have hgen := generic_ineq_of_hitting (fun j ↦ armIndicator A k' j ω)
      (fun j ↦ aRTSSelProb A k' ℱ P j ω) (fun j ↦ aRTSTarget A Y θ₀ T j ω k') α
      (Q k' ω) hthr hp1ω (fun m ↦ mul_nonneg hα.1 (hTnn _ k')) n
    linarith [hgen]
  · -- hsmall (the design-specific smallness `o_p`-bound, taken as the hypothesis `hsmall_op`)
    intro k'
    simpa only [hsmalldef, hℓdef] using hsmall_op k'
  · -- hc
    intro k'
    exact mul_pos (by linarith [hα1] : (0 : ℝ) < 1 - α) (hv k')
  · -- hd
    intro k' n ω
    simp only [hddef, sub_nonneg]
    exact_mod_cast Nat.findGreatest_le n
  · -- hdecomp (holds as an equality: `pert` is defined as the residual over `d`)
    intro k' n ω
    have key : -c k' * d k' n ω + Mincr k' n ω + rhoterm k' n ω + pert k' n ω * d k' n ω
        = Uincr k' n ω := by
      rcases eq_or_ne (d k' n ω) 0 with hd0 | hd0
      · have hℓn : ℓ k' n ω = n := by
          have h1 : ((ℓ k' n ω : ℕ) : ℝ) = (n : ℝ) := by
            have h2 := hd0; simp only [hddef] at h2; linarith
          exact_mod_cast h1
        have hU0 : Uincr k' n ω = 0 := by simp only [hUdef, hℓn, sub_self]
        have hM0 : Mincr k' n ω = 0 := by simp only [hMdef, hℓn, sub_self]
        have hr0 : rhoterm k' n ω = 0 := by simp only [hrhodef, hℓn, sub_self, mul_zero]
        rw [hd0, hU0, hM0, hr0]; ring
      · simp only [hpertdef]
        rw [div_mul_cancel₀ _ hd0]; ring
    linarith [key]
  · -- hpert: the diff_U_decomp perturbation is `o_p` (a.e. `→ 0`, by consistency of `ρ̂`)
    intro k'
    have harmmeas : ∀ j, Measurable (fun ω ↦ armIndicator A k' j ω) := fun j ↦
      (measurable_const (a := (1 : ℝ))).indicator
        ((measurableSet_singleton k').preimage (h.measurable_action j))
    have hselmeas : ∀ j, Measurable (fun ω ↦ aRTSSelProb A k' ℱ P j ω) := fun j ↦ by
      simp only [aRTSSelProb]
      exact (stronglyMeasurable_condExp.mono (ℱ.shiftDown.le j)).measurable
    have hrhomeas : ∀ m, Measurable (fun ω ↦ aRTSTarget A Y θ₀ T m ω k') :=
      fun m ↦ measurable_aRTSTarget_coord h θ₀ hT m k'
    have hℓmeas : ∀ n, Measurable (fun ω ↦ ℓ k' n ω) := fun n ↦ by
      simp only [hℓdef]; exact measurable_hitting (hQmeas k') n
    have hℓleN : ∀ n ω, ℓ k' n ω ≤ n := fun n ω ↦ Nat.findGreatest_le n
    have hℓcast : ∀ n, Measurable (fun ω ↦ ((ℓ k' n ω : ℕ) : ℝ)) := fun n ↦
      measurable_eval_of_le (H := fun _ m ↦ (m : ℝ)) (fun _ ↦ measurable_const)
        (hℓmeas n) (hℓleN n)
    have hassignMGmeas : ∀ m, Measurable (fun ω ↦
        assignMG (fun j ↦ armIndicator A k' j ω) (fun j ↦ aRTSSelProb A k' ℱ P j ω) m) := fun m ↦ by
      simp only [assignMG]
      exact Finset.measurable_sum _ fun j _ ↦ (harmmeas j).sub (hselmeas j)
    have hauxUmeas : ∀ m, Measurable (fun ω ↦
        auxU (fun j ↦ armIndicator A k' j ω) (fun j ↦ aRTSSelProb A k' ℱ P j ω)
          (fun j ↦ aRTSTarget A Y θ₀ T j ω k') α m) := fun m ↦ by
      simp only [auxU]
      exact ((Finset.measurable_sum _ fun j _ ↦ (hrhomeas j).const_mul α).add
        (hassignMGmeas m)).sub ((hrhomeas m).const_mul _)
    refine isLittleOpOne_of_tendsto_ae (fun n ↦ ?_) ?_
    · -- measurability of `pert k' n`
      have hUincrmeas : Measurable (fun ω ↦ Uincr k' n ω) := by
        simp only [hUdef]
        exact (hauxUmeas n).sub (measurable_eval_of_le hauxUmeas (hℓmeas n) (hℓleN n))
      have hMincrmeas : Measurable (fun ω ↦ Mincr k' n ω) := by
        simp only [hMdef]
        exact (hassignMGmeas n).sub
          (measurable_eval_of_le hassignMGmeas (hℓmeas n) (hℓleN n))
      have hrhotermmeas : Measurable (fun ω ↦ rhoterm k' n ω) := by
        simp only [hrhodef]
        exact (hℓcast n).mul
          ((measurable_eval_of_le hrhomeas (hℓmeas n) (hℓleN n)).sub (hrhomeas n))
      have hdmeas : Measurable (fun ω ↦ d k' n ω) := by
        simp only [hddef]; exact measurable_const.sub (hℓcast n)
      simp only [hpertdef]
      exact ((hUincrmeas.sub (((hdmeas.const_mul (-c k')).add hMincrmeas).add
        hrhotermmeas)).div hdmeas).aestronglyMeasurable
    · -- a.e. `pert k' n ω → 0`
      filter_upwards [hρconv k'] with ω hρω
      rw [NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      have hdec := diff_U_decomp (fun j ↦ armIndicator A k' j ω)
        (fun j ↦ aRTSSelProb A k' ℱ P j ω) (fun j ↦ aRTSTarget A Y θ₀ T j ω k') α hρω
        (ℓ := fun n ↦ ℓ k' n ω) (fun n ↦ Nat.findGreatest_le n) (half_pos hε)
      filter_upwards [hdec] with n hn
      have hdval : d k' n ω = (n : ℝ) - ℓ k' n ω := by simp only [hddef]
      have hER : Uincr k' n ω - (-c k' * d k' n ω + Mincr k' n ω + rhoterm k' n ω)
          = auxU (fun j ↦ armIndicator A k' j ω) (fun j ↦ aRTSSelProb A k' ℱ P j ω)
              (fun j ↦ aRTSTarget A Y θ₀ T j ω k') α n
            - auxU (fun j ↦ armIndicator A k' j ω) (fun j ↦ aRTSSelProb A k' ℱ P j ω)
              (fun j ↦ aRTSTarget A Y θ₀ T j ω k') α (ℓ k' n ω)
            - (((n : ℝ) - ℓ k' n ω) * (-(1 - α) * T (fun k'' ↦ (ν k'')[id]) k')
              + (assignMG (fun j ↦ armIndicator A k' j ω)
                  (fun j ↦ aRTSSelProb A k' ℱ P j ω) n
                - assignMG (fun j ↦ armIndicator A k' j ω)
                  (fun j ↦ aRTSSelProb A k' ℱ P j ω) (ℓ k' n ω))
              + (ℓ k' n ω : ℝ)
                * (aRTSTarget A Y θ₀ T (ℓ k' n ω) ω k' - aRTSTarget A Y θ₀ T n ω k')) := by
        simp only [hUdef, hMdef, hrhodef, hcdef, hddef]; ring
      have hdnn : 0 ≤ d k' n ω := by
        rw [hdval]
        have hle : (ℓ k' n ω : ℝ) ≤ n := by exact_mod_cast hℓleN n ω
        linarith
      rcases eq_or_ne (d k' n ω) 0 with hd0 | hd0
      · simp only [hpertdef, hd0, div_zero, norm_zero]; exact hε
      · have hdpos : 0 < d k' n ω := hdnn.lt_of_ne (Ne.symm hd0)
        have hnum : |Uincr k' n ω - (-c k' * d k' n ω + Mincr k' n ω + rhoterm k' n ω)|
            ≤ ε / 2 * d k' n ω := by rw [hER, hdval]; exact hn
        rw [Real.norm_eq_abs]
        simp only [hpertdef]
        rw [abs_div, abs_of_pos hdpos, div_lt_iff₀ hdpos]
        calc |Uincr k' n ω - (-c k' * d k' n ω + Mincr k' n ω + rhoterm k' n ω)|
            ≤ ε / 2 * d k' n ω := hnum
          _ < ε * d k' n ω := by nlinarith [mul_pos (half_pos hε) hdpos]
  · -- hMbound: `M_n - M_ℓ ≤ |M_n - M_ℓ| ≤ (n-ℓ)·vmaxSeq + wmaxSeq`, via the seam and
    -- `norm_increment_le_vmaxSeq_wmaxSeq` for the singleton family `{assignMart}`.
    intro k'
    filter_upwards [eventually_ge_atTop 2] with n hn2
    refine ae_of_all _ fun ω ↦ ?_
    have hℓle : ℓ k' n ω ≤ n := Nat.findGreatest_le n
    have hseam : Mincr k' n ω
        = assignMart (fun j ↦ armIndicator A k' j) ℱ P n ω
          - assignMart (fun j ↦ armIndicator A k' j) ℱ P (ℓ k' n ω) ω := by
      simp only [hMdef]
      rw [assignMart_eq_assignMG, assignMart_eq_assignMG]; rfl
    have hni := norm_increment_le_vmaxSeq_wmaxSeq
      (M := fun _ : Unit ↦ assignMart (fun j ↦ armIndicator A k' j) ℱ P) n hn2 hℓle ω
    have hsum1 : √(∑ _u : Unit, (assignMart (fun j ↦ armIndicator A k' j) ℱ P n ω
          - assignMart (fun j ↦ armIndicator A k' j) ℱ P (ℓ k' n ω) ω) ^ 2)
        = |assignMart (fun j ↦ armIndicator A k' j) ℱ P n ω
          - assignMart (fun j ↦ armIndicator A k' j) ℱ P (ℓ k' n ω) ω| := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_nsmul, Real.sqrt_sq_eq_abs]
    have hdeq : ((n - ℓ k' n ω : ℕ) : ℝ) = d k' n ω := by
      simp only [hddef]; rw [Nat.cast_sub hℓle]
    rw [hsum1, hdeq] at hni
    calc Mincr k' n ω ≤ |Mincr k' n ω| := le_abs_self _
      _ = |assignMart (fun j ↦ armIndicator A k' j) ℱ P n ω
          - assignMart (fun j ↦ armIndicator A k' j) ℱ P (ℓ k' n ω) ω| := by rw [hseam]
      _ ≤ d k' n ω * VM k' n ω + WM k' n ω := hni
      _ = VM k' n ω * d k' n ω + WM k' n ω := by rw [mul_comm]
  · -- hVM
    intro k'
    simpa only [hVMdef] using (hMqm k').1
  · -- hWM
    intro k'
    simpa only [hWMdef] using (hMqm k').2
  · -- hρbound
    exact fun k' ↦ (hρbd k').mono (fun n hn ↦ ae_of_all _ hn)
  · -- hVρ
    exact hVρ
  · -- hWρ
    exact hWρ

/-- **Deviation between proportions and plug-in target for the aRTS design**
(blueprint `lem:prop_dev`, `thm:normality` part (i), `o_p(√n)` half). For every arm `k`,
`|N_{n,k} - n ρ̂_{n,k}| = o_p(√n)`.

The `aRTS` instantiation of `prop_dev_of_hitting` at the last under-sampling time
`hitting (aRTSUnder …)`, fully self-contained: the `thm:LLN` consistencies `θ̂ → θ`
(`aRTS_theta_consistent`), `N/n → v` (`aRTS_proportion_tendsto`), the throttle
(`throttle_of_isARTS`, from the algorithm-level `IsARTS` predicate), and the smallness are all
discharged from the same
`aRTS_LLN` design bundle — an `IsAlgEnvSeq` sequence, `Y ∈ L²` (Condition **A**), a simplex-valued
`LipschitzWith K` target `T` (Condition **B**), `α ∈ [0,1)`, and the non-sparsity `hTpos`. The
smallness is automatic: at the last under-sampling time `N_ℓ - ℓ ρ̂_ℓ ≤ 0` (`preliminary_small`), so
`(1 + N_ℓ - ℓ ρ̂_ℓ)^+/√n ≤ 1/√n = o_p(1)`. The a.s. `O(√(n log log n))` bounds are a separate
statement. -/
lemma aRTS_prop_dev [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1) (hARTS : IsARTS alg θ₀ T α)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k) (k : 𝓐) :
    IsLittleOpOne P (fun n ω ↦ ((pullCount A k n ω : ℝ)
      - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k) / √n) := by
  have hT : Continuous T := hlip.continuous
  refine prop_dev_of_hitting h hY2 θ₀ T hTnn hTsum α hα hα1 hlip hTpos
    (aRTS_theta_consistent h hY2 hT hTnn hTsum hα hARTS hTpos)
    (fun k' ↦ (aRTS_proportion_tendsto h hY2 hT hTnn hTsum hα hARTS hTpos k').mono
      fun ω hω ↦ hω.congr fun n ↦ by rw [count_indicator_eq_pullCount])
    (aRTSUnder A Y θ₀ T) (fun k m ↦ measurableSet_aRTSUnder h θ₀ hT k m)
    (fun k ↦ throttle_of_isARTS h hARTS k) ?_ k
  -- The aRTS smallness `o_p`-bound: `1 + N_ℓ - ℓ ρ̂_ℓ ≤ 1` (`preliminary_small`), so `/√n → 0`.
  intro k'
  refine IsLittleOpOne.of_abs_le (Y := fun n (_ : Ω) ↦ (1 : ℝ) / √n) ?_
    (isLittleOpOne_const_div_sqrt 1)
  intro n ω
  have hps := preliminary_small (fun j ↦ armIndicator A k' j ω)
    (fun j ↦ aRTSTarget A Y θ₀ T j ω k') (aRTSUnder A Y θ₀ T k' ω) n (fun m hm ↦ hm)
  rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    refine max_le ?_ (by positivity)
    gcongr
    linarith [hps]

end AlphaRAR
