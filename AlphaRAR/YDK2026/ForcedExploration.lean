/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.TaylorRemainder
import AlphaRAR.YDK2026.ARTSNormality
import AlphaRAR.YDK2026.PropDevLIL

/-!
# Forced exploration and sparse targets

This file develops the forced-exploration variant `aRTSFE` of the aRTS family (blueprint
`chap:forced`, Section 4 of the paper). Forced exploration samples the least-explored arms whenever
some arm has been pulled fewer than `h(m)` times (`h` an *exploration schedule*), which guarantees
every arm is sampled infinitely often.

The whole point of the generic-conditions modularisation is that the asymptotic theory needs
**nothing** design-specific beyond a hitting time `ℓ_{n,k}` satisfying the generic conditions. The
`aRTSFE` design satisfies them with the forced-exploration hitting time — the last time arm `k` was
either under-sampled *or* under-explored (`count ≤ h(m)`). Both `thm:LLN` (consistency) and
`thm:normality` (deviation bounds and the joint CLT) then follow by reusing the
abstract-hitting-time theorems (`consistency_of_hitting`, `prop_dev_of_hitting`,
`prop_dev_ae_of_hitting`,
`count_sub_smul_ae_of_hitting`, `clt_joint_of_hitting`), the *only* new ingredients being the
smallness bounds `N_ℓ - ℓ ρ̂_ℓ ≤ (h(ℓ))^+`, which is `o(n)` (consistency), `o(√n)` (`o_p` deviation)
and `O(√(n log log n))` (a.s. deviation) by the exploration-schedule conditions.

## Main results

* `AlphaRAR.IsExplorationSchedule`, `AlphaRAR.aRTSFEUnder`.
* `AlphaRAR.IsARTSFE` — the design-family predicate, on histories, `IsARTS`'s analogue for `aRTSFE`;
  `AlphaRAR.throttle_of_isARTSFE` and `AlphaRAR.fe_of_isARTSFE` transport it to the process.
* `AlphaRAR.aRTSFE_proportion_tendsto` — a.s. `N_{n,k}/n → v_k`, `ρ̂_{n,k} → v_k` for `aRTSFE`.
* `AlphaRAR.aRTSFE_prop_dev`, `AlphaRAR.aRTSFE_prop_dev_ae`, `AlphaRAR.aRTSFE_count_sub_smul_ae`,
  `AlphaRAR.aRTSFE_clt_joint` — `thm:normality` for `aRTSFE`.
* `AlphaRAR.aRTSFE_sparse_clt` — the sparse componentwise CLT, given `FEfed`.
* `AlphaRAR.aRTSFE_sparse_clt_of_contDiffAt` — the same conclusion with `FEfed` *discharged*, from
  `C²` smoothness of the target and the reversed schedule condition
  `(⋆) : √(m log log m) ≪ h(m) = o(m)` in place of the paper's `h(m) = o(√m)`. See
  `maths/sparse-clt-fix.md`; `AlphaRAR.sched23_satisfies_schedule_hypotheses` shows the schedule
  hypotheses are satisfiable, and only outside the paper's condition (ii).
-/

open MeasureTheory ProbabilityTheory Filter Learning Real
open scoped Topology ENNReal NNReal Matrix

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓐 ℝ}

/-- An **exploration schedule** (blueprint `def:exploration_schedule`, in the weakened form): a
nondecreasing threshold `h(m)` with `h(m) → ∞` and `h(m) = o(m)`. Monotonicity is a harmless
convenience that lets `h(ℓ) ≤ h(n)` for `ℓ ≤ n`.

The paper additionally requires `h(m) = o(√m)`; that is `IsSqrtSmall` below, deliberately *not* a
field here. It is needed only by the `√n`-scaled normality results, and even there it is not
necessary (`underExplored_eventually_empty`: under Condition **B** forced exploration switches
itself off, so any `h(m) = o(m)` does). Keeping it separate is what makes schedules with
`h(m) ≫ √m` available — and those are exactly the ones under which forced exploration, rather than
the data-dependent targeting rule, decides a *sparse* arm's sample size, which is what earns the
sparse componentwise CLT (`pullCount_div_sched_tendsto_one`, `aRTSFE_sparse_clt`). -/
structure IsExplorationSchedule (hsched : ℕ → ℝ) : Prop where
  /-- The schedule is nondecreasing. -/
  mono : Monotone hsched
  /-- The schedule diverges: `h(m) → ∞` (this is what forces every arm to be sampled infinitely
  often). -/
  tendsto_atTop : Tendsto hsched atTop atTop
  /-- The schedule is `o(m)`. -/
  div_tendsto_zero : Tendsto (fun m ↦ hsched m / (m : ℝ)) atTop (𝓝 0)

/-- The paper's stronger schedule condition `h(m) = o(√m)` (`def:exploration_schedule` (ii)). It is
required only by the `√n`-scaled normality results, and is incompatible with the sparse regime: see
`IsExplorationSchedule`. -/
def IsSqrtSmall (hsched : ℕ → ℝ) : Prop :=
  Tendsto (fun m ↦ hsched m / Real.sqrt m) atTop (𝓝 0)

/-- `h(m) = o(√m)` implies `h(m)/m → 0`, so the paper's condition is stronger than the one
retained in `IsExplorationSchedule`. -/
lemma IsSqrtSmall.div_tendsto_zero {hsched : ℕ → ℝ} (hlo : IsSqrtSmall hsched) :
    Tendsto (fun m ↦ hsched m / (m : ℝ)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun m : ℕ ↦ 1 / Real.sqrt m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hprod : Tendsto (fun m : ℕ ↦ (hsched m / Real.sqrt m) * (1 / Real.sqrt m))
      atTop (𝓝 0) := by simpa using hlo.mul h2
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  rw [div_mul_div_comm, mul_one, Real.mul_self_sqrt (Nat.cast_nonneg m)]

/-- The **forced-exploration hitting predicate**: arm `k` is either *under-sampled*
(`N_{m,k} ≤ m ρ̂_{m,k}`) or *under-explored* (`N_{m,k} ≤ h(m)`). Its last occurrence before `n` is
the forced-exploration hitting time (blueprint `def:hitting_fe`); the generic conditions hold with
it. -/
def aRTSFEUnder (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hsched : ℕ → ℝ) (k : 𝓐) (ω : Ω) (m : ℕ) : Prop :=
  count (fun j ↦ armIndicator A k j ω) m ≤ (m : ℝ) * aRTSTarget A Y θ₀ T m ω k
    ∨ count (fun j ↦ armIndicator A k j ω) m ≤ hsched m

noncomputable instance {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {hsched : ℕ → ℝ} {k : 𝓐} {ω : Ω} :
    DecidablePred (aRTSFEUnder A Y θ₀ T hsched k ω) := Classical.decPred _

/-- **The forced-exploration aRTS design family** (blueprint `def:aRTSFE`, algorithm form) — the
`IsARTS` analogue for `aRTSFE`. An algorithm is an `α`-throttled forced-exploration aRTS design with
offsets `θ₀`, target map `T` and schedule `h` when its policy obeys two rules:

* **forced exploration takes priority**: if some arm is under-explored (`N_{n+1,j} ≤ h(n+1)`), then
  all of the policy's mass sits on the *least-sampled* under-explored arms — every other arm gets
  probability zero;
* **outside forced exploration the design is throttled**: an arm that is neither under-sampled nor
  under-explored gets probability at most `α ρ̂_k`.

Compared with `IsARTS`, the throttle carries the extra premise `h(n+1) < N_{n+1,k}`: forced
exploration is allowed to override it, which is exactly what the design is for.

Like `IsARTS`, this is stated purely on histories — no process, measure or filtration appears — so
it is a property of the algorithm alone, checkable design by design. `throttle_of_isARTSFE` and
`fe_of_isARTSFE` transport the two fields to the process-level hypotheses that the asymptotic
theorems consume. -/
structure IsARTSFE [DecidableEq 𝓐] (alg : Algorithm 𝓐 ℝ) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hsched : ℕ → ℝ) (α : ℝ) : Prop where
  /-- An arm that is neither under-sampled nor under-explored is throttled at `α ρ̂_k`. -/
  throttle : ∀ (n : ℕ) (hist : Finset.Iic n → 𝓐 × ℝ) (k : 𝓐),
    ((n : ℝ) + 1) * histTarget θ₀ T k n hist < (pullCount' n hist k : ℝ) →
      hsched (n + 1) < (pullCount' n hist k : ℝ) →
        (alg.policy n hist {k}).toReal ≤ α * histTarget θ₀ T k n hist
  /-- When some arm is under-explored, an arm that is not a least-sampled under-explored one cannot
  be drawn. -/
  forced : ∀ (n : ℕ) (hist : Finset.Iic n → 𝓐 × ℝ) (k : 𝓐),
    (∃ j, (pullCount' n hist j : ℝ) ≤ hsched (n + 1)) →
      (hsched (n + 1) < (pullCount' n hist k : ℝ) ∨
        ∃ j, (pullCount' n hist j : ℝ) ≤ hsched (n + 1) ∧
          (pullCount' n hist j : ℝ) < (pullCount' n hist k : ℝ)) →
        alg.policy n hist {k} = 0

/-- The level sets of the forced-exploration predicate are measurable (a union of the two
measurable events `N ≤ m ρ̂` and `N ≤ h(m)`). -/
lemma measurableSet_aRTSFEUnder [Finite 𝓐] (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (hsched : ℕ → ℝ) (k : 𝓐) (m : ℕ) :
    MeasurableSet {ω | aRTSFEUnder A Y θ₀ T hsched k ω m} :=
  (measurableSet_aRTSUnder h θ₀ hT k m).union
    (measurableSet_le (measurable_count_armIndicator h k m) measurable_const)

/-- **The forced-exploration gap bound.** At the forced-exploration hitting time the gap
`N_ℓ - ℓ ρ̂_ℓ` is bounded by `(h(ℓ))^+ ≤ (h(n))^+` (blueprint `def:hitting_fe` (iii)): if `ℓ = 0`
the gap is `≤ 0`; otherwise the hitting predicate holds at `ℓ`, so either arm `k` is under-sampled
(gap `≤ 0`) or under-explored (`N_ℓ ≤ h(ℓ)`, and `ℓ ρ̂_ℓ ≥ 0`), and monotonicity lifts `h(ℓ)` to
`h(n)`. This single deterministic bound feeds all three smallness conditions (`o(n)`, `o(√n)`,
`O(√(n log log n))`). -/
lemma aRTSFE_gap_le (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hTnn : ∀ z k, 0 ≤ T z k)
    {hsched : ℕ → ℝ} (hmono : Monotone hsched) (k : 𝓐) (ω : Ω) (n : ℕ) :
    count (fun j ↦ armIndicator A k j ω) (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n)
      - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
        * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k
      ≤ max 0 (hsched n) := by
  rcases Nat.eq_zero_or_pos (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) with h0 | hpos
  · rw [h0]
    have hc0 : count (fun j ↦ armIndicator A k j ω) 0 = 0 := by simp [count]
    rw [hc0]; simp only [Nat.cast_zero, zero_mul, sub_zero]; exact le_max_left _ _
  · have hP : aRTSFEUnder A Y θ₀ T hsched k ω (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) :=
      Nat.findGreatest_of_ne_zero rfl hpos.ne'
    have hmono2 : max 0 (hsched (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n))
        ≤ max 0 (hsched n) := max_le_max le_rfl (hmono (Nat.findGreatest_le n))
    refine le_trans ?_ hmono2
    rcases hP with hunder | hsmall
    · exact le_trans (by linarith) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hnn : (0 : ℝ) ≤ (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
          * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k :=
        mul_nonneg (Nat.cast_nonneg _) (by simp only [aRTSTarget]; exact hTnn _ _)
      linarith

/-- **Forced-exploration consistency smallness** (blueprint `def:hitting_fe` (iii), the `aRTSFE`
form of `generic_small_of_hitting`). At the forced-exploration hitting time the gap is `≤ (h(n))^+`
(`aRTSFE_gap_le`), which is `o(n)` since `h(n) = o(√n) = o(n)`, so it vanishes divided by `n`. -/
lemma aRTSFE_smallness (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hTnn : ∀ z k, 0 ≤ T z k)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (k : 𝓐) (ω : Ω) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      (count (fun j ↦ armIndicator A k j ω) (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n)
        - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
          * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k)
        / (n : ℝ) < δ := by
  -- `max 0 (h n) / n → 0`, by squeezing between `0` and `|h n / n|`.
  have hmaxlim : Tendsto (fun n : ℕ ↦ max 0 (hsched n) / (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_)
      (by simpa using hh.div_tendsto_zero.abs)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [abs_div, Nat.abs_cast]
      gcongr
      exact max_le (abs_nonneg _) (le_abs_self _)
  filter_upwards [hmaxlim.eventually (gt_mem_nhds hδ), eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hnR]
  linarith [aRTSFE_gap_le (A := A) (Y := Y) θ₀ T hTnn hh.mono k ω n, (div_lt_iff₀ hnR).mp hn]

omit [IsProbabilityMeasure P] in
/-- The `aRTSFE` consistency smallness for *all* arms, in the form consumed by the abstract-hitting
consistency/rate theorems (`consistency_of_hitting`, `theta_consistent_of_hitting`,
`proportion_tendsto_of_hitting`, `rho_rate_of_hitting`): `aRTSFE_smallness` bundled over `k`. -/
lemma aRTSFE_smallness_all (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hTnn : ∀ z k, 0 ≤ T z k)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) :
    ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count (fun j ↦ armIndicator A k j ω) (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n)
          - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
            * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k)
          / (n : ℝ) < δ :=
  fun k ↦ Eventually.of_forall fun ω δ hδ ↦ aRTSFE_smallness θ₀ T hTnn hh k ω δ hδ

/-- **Forced-exploration `o_p`-smallness** (the `aRTSFE` form of the `hsmall_op` hypothesis of
`prop_dev_of_hitting`). Since the gap is `≤ (h(n))^+` (`aRTSFE_gap_le`) and `h(n) = o(√n)`, the
scaled quantity `(1 + N_ℓ - ℓ ρ̂_ℓ)^+ / √n` is dominated by the deterministic
`(1 + (h n)^+)/√n → 0`, hence `o_p(1)`. -/
lemma aRTSFE_smallness_op (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hTnn : ∀ z k, 0 ≤ T z k)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (hlo : IsSqrtSmall hsched) (k : 𝓐) :
    IsLittleOpOne P (fun n ω ↦
      max ((1 + (count (fun j ↦ armIndicator A k j ω) (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n)
        - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
          * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k)) / √n) 0) := by
  -- The deterministic majorant `(1 + max 0 (h n))/√n → 0`.
  have ha : Tendsto (fun n : ℕ ↦ (1 : ℝ) / √n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ ↦ max 0 (hsched n) / √n) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) (by simpa using hlo.abs)
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    exact max_le (abs_nonneg _) (le_abs_self _)
  have hYlim : Tendsto (fun n : ℕ ↦ (1 + max 0 (hsched n)) / √n) atTop (𝓝 0) := by
    have hsum := ha.add hb
    rw [add_zero] at hsum
    exact hsum.congr fun n ↦ (add_div 1 (max 0 (hsched n)) (√n)).symm
  refine IsLittleOpOne.of_abs_le (Y := fun n (_ : Ω) ↦ (1 + max 0 (hsched n)) / √n) ?_
    (isLittleOpOne_of_tendsto_ae (fun n ↦ measurable_const.aestronglyMeasurable)
      (ae_of_all _ fun _ ↦ hYlim))
  intro n ω
  have hgap := aRTSFE_gap_le (A := A) (Y := Y) θ₀ T hTnn hh.mono k ω n
  rw [abs_of_nonneg (le_max_right _ _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + max 0 (hsched n)) / √n)]
  refine max_le ?_ (by positivity)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · gcongr

/-- Eventually `(h(n))^+ ≤ √(n log log n)`: `h(n) = o(√n)` gives `h(n) < √n` eventually, and
`√n ≤ √(n log log n)` once `log log n ≥ 1`. -/
lemma aRTSFE_maxsched_le_logLogRate {hsched : ℕ → ℝ} (hlo : IsSqrtSmall hsched) :
    ∀ᶠ n in atTop, max 0 (hsched n) ≤ logLogRate n := by
  have h1 : ∀ᶠ n in atTop, hsched n < √n := by
    filter_upwards [hlo.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      eventually_gt_atTop 0] with n hlt hn0
    rwa [div_lt_one (Real.sqrt_pos.mpr (by exact_mod_cast hn0))] at hlt
  have h2 : ∀ᶠ n : ℕ in atTop, √n ≤ logLogRate n := by
    have hll := (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop (1 : ℝ)
    filter_upwards [hll] with n hlln
    simp only [Function.comp_apply] at hlln
    rw [logLogRate_eq]
    exact Real.sqrt_le_sqrt (le_mul_of_one_le_right (Nat.cast_nonneg n) hlln)
  filter_upwards [h1, h2] with n hlt hle
  exact max_le (le_trans (Real.sqrt_nonneg _) hle) (le_trans hlt.le hle)

omit [IsProbabilityMeasure P] in
/-- **Forced-exploration loglog-smallness** (the `aRTSFE` form of the `hsmall_upper` hypothesis of
`dev_upper_of_hitting`). The gap is `≤ (h(n))^+` (`aRTSFE_gap_le`), which is `≤ √(n log log n)`
eventually (`aRTSFE_maxsched_le_logLogRate`), so `O(√(n log log n))` with constant `1`. -/
lemma aRTSFE_smallness_upper (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hTnn : ∀ z k, 0 ≤ T z k)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (hlo : IsSqrtSmall hsched) (k : 𝓐) :
    ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      (count (fun j ↦ armIndicator A k j ω) (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n)
        - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
          * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k)
        ≤ C * logLogRate n := by
  refine ae_of_all _ fun ω ↦ ⟨1, ?_⟩
  filter_upwards [aRTSFE_maxsched_le_logLogRate hlo] with n hn
  rw [one_mul]
  exact le_trans (aRTSFE_gap_le θ₀ T hTnn hh.mono k ω n) hn

/-- **A.s. consistency of the `aRTSFE` allocation proportions** (blueprint `thm:forced_valid`,
consistency direction). For a forced-exploration design (given here through the process-level
throttle `hthrottle` at the forced-exploration hitting predicate `aRTSFEUnder`) with an exploration
schedule `hsched`, the allocation proportions converge a.s. to the common limit of the plug-in
targets: `N_{n,k}/n → v_k` and `ρ̂_{n,k} → v_k` for every arm `k`.

This is a *direct reuse* of `consistency_of_hitting`: the forced-exploration hitting time
`hitting (aRTSFEUnder …)` and the throttle discharge the generic key inequality exactly as for
`aRTS`, and the only design-specific ingredient — the smallness `N_ℓ - ℓ ρ̂_ℓ ≤ (h(ℓ))^+ = o(n)` —
is `aRTSFE_smallness`. -/
theorem aRTSFE_proportion_tendsto [Fintype 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n / (n : ℝ)) atTop (𝓝 (u k))
        ∧ Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop (𝓝 (u k)) :=
  consistency_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα (aRTSFEUnder A Y θ₀ T hsched) hthrottle
    (aRTSFE_smallness_all θ₀ T hTnn hh)

/-! ### Asymptotic normality under forced exploration (non-sparse targets)

The `thm:normality` (blueprint `thm:forced_valid`, normality direction) for the `aRTSFE` family.
Each result is a *direct reuse* of the corresponding abstract-hitting-time theorem with the
forced-exploration predicate `aRTSFEUnder`: the process-level throttle enters as the design
hypothesis `hthrottle`, and the new ingredients are the forced-exploration smallness lemmas
(`aRTSFE_smallness_all`/`_op`/`_upper`) discharging the generic conditions. -/

/-- **`o_p(√n)` proportion deviation under forced exploration** (blueprint `thm:forced_valid`,
`thm:normality` part (i), `o_p` half). `|N_{n,k} - n ρ̂_{n,k}| = o_p(√n)` for the `aRTSFE` family.
A direct reuse of `prop_dev_of_hitting`; the `o_p`-smallness is `aRTSFE_smallness_op` (using
`h(n) = o(√n)`). -/
theorem aRTSFE_prop_dev [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (hlo : IsSqrtSmall hsched)
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k) (k : 𝓐) :
    IsLittleOpOne P (fun n ω ↦ ((pullCount A k n ω : ℝ)
      - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k) / √n) := by
  have hT : Continuous T := hlip.continuous
  have hgs := aRTSFE_smallness_all (A := A) (Y := Y) (P := P) θ₀ T hTnn hh
  exact prop_dev_of_hitting h hY2 θ₀ T hTnn hTsum α hα hα1 hlip hTpos
    (theta_consistent_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα
      (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos)
    (fun k' ↦ (proportion_tendsto_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα
      (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos k').mono
        fun ω hω ↦ hω.congr fun n ↦ by rw [count_indicator_eq_pullCount])
    (aRTSFEUnder A Y θ₀ T hsched) (fun k m ↦ measurableSet_aRTSFEUnder h θ₀ hT hsched k m)
    hthrottle (aRTSFE_smallness_op θ₀ T hTnn hh hlo) k

/-- **A.s. `O(√(n log log n))` proportion deviation under forced exploration** (blueprint
`thm:forced_valid`, `thm:normality` part (i), a.s. half). `N_{n,k} - n ρ̂_{n,k} = O(√(n log log n))`
a.s. for the `aRTSFE` family. A direct reuse of `prop_dev_ae_of_hitting`; the loglog rate is
`rho_rate_of_hitting` and the smallness is `aRTSFE_smallness_upper` (using `h(n) = o(√n)`). -/
theorem aRTSFE_prop_dev_ae [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T (fun k ↦ (ν k)[id]))
    (hint_id : ∀ k, Integrable (fun x : ℝ ↦ x) (ν k))
    (hint_sq : ∀ k, Integrable (fun x : ℝ ↦ x ^ 2) (ν k))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (hlo : IsSqrtSmall hsched)
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ (pullCount A k n ω : ℝ) - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k)
      =O[atTop] logLogRate := by
  have hgs := aRTSFE_smallness_all (A := A) (Y := Y) (P := P) θ₀ T hTnn hh
  exact prop_dev_ae_of_hitting h θ₀ T hT hTnn hTsum α hα hα1 hTpos
    (theta_consistent_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα
      (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos)
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle
    (fun k' ↦ rho_rate_of_hitting h hY2 hT hTnn hTsum hα (aRTSFEUnder A Y θ₀ T hsched)
      hthrottle hgs hTpos hT_diff hint_id hint_sq k')
    (fun k' ↦ aRTSFE_smallness_upper θ₀ T hTnn hh hlo k') k

/-- **A.s. `O(√(n log log n))` count-versus-target deviation under forced exploration** (blueprint
`thm:forced_valid`, `thm:normality` part (i), last line). `N_{n,k} - n v_k = O(√(n log log n))` a.s.
for the `aRTSFE` family. A direct reuse of `count_sub_smul_ae_of_hitting`. -/
theorem aRTSFE_count_sub_smul_ae [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T (fun k ↦ (ν k)[id]))
    (hint_id : ∀ k, Integrable (fun x : ℝ ↦ x) (ν k))
    (hint_sq : ∀ k, Integrable (fun x : ℝ ↦ x ^ 2) (ν k))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (hlo : IsSqrtSmall hsched)
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ (pullCount A k n ω : ℝ) - (n : ℝ) * T (fun k' ↦ (ν k')[id]) k)
      =O[atTop] logLogRate := by
  have hgs := aRTSFE_smallness_all (A := A) (Y := Y) (P := P) θ₀ T hTnn hh
  exact count_sub_smul_ae_of_hitting h θ₀ T hT hTnn hTsum α hα hα1 hTpos
    (theta_consistent_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα
      (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos)
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle
    (fun k' ↦ rho_rate_of_hitting h hY2 hT hTnn hTsum hα (aRTSFEUnder A Y θ₀ T hsched)
      hthrottle hgs hTpos hT_diff hint_id hint_sq k')
    (fun k' ↦ aRTSFE_smallness_upper θ₀ T hTnn hh hlo k') k

/-- **Joint central limit theorem under forced exploration** (blueprint `thm:forced_valid`,
`thm:normality` part (ii)). The `√n`-scaled joint deviation vector `(√n(N_n/n - v), √n(ρ̂_n - v))`
converges weakly to the block-Gaussian `𝒩(0, Ω)` for the `aRTSFE` family. A direct reuse of
`clt_joint_of_hitting`; the smallness conditions are `aRTSFE_smallness_all` and
`aRTSFE_smallness_op`. -/
theorem aRTSFE_clt_joint [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (G : Matrix 𝓐 𝓐 ℝ)
    (hTderiv : HasFDerivAt
      (fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (T (WithLp.ofLp x)) : EuclideanSpace ℝ 𝓐))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) G) (WithLp.toLp 2 (fun k ↦ (ν k)[id])))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (hlo : IsSqrtSmall hsched)
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐)))
      (fun n : ℕ ↦ (⟨P.map (jointSqrtNVec ν A Y θ₀ T (T (fun k' ↦ (ν k')[id])) n),
        Measure.isProbabilityMeasure_map
          (measurable_jointSqrtNVec h θ₀ hlip.continuous (T (fun k' ↦ (ν k')[id])) n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ (𝓐 ⊕ 𝓐))))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.fromBlocks
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T (fun k' ↦ (ν k')[id]) a) * Gᵀ)),
          inferInstance⟩) := by
  have hT : Continuous T := hlip.continuous
  exact clt_joint_of_hitting h hY2 hνk θ₀ T hTnn hTsum α hα hα1 hlip hTpos G hTderiv
    (aRTSFEUnder A Y θ₀ T hsched) (fun k m ↦ measurableSet_aRTSFEUnder h θ₀ hT hsched k m)
    hthrottle (aRTSFE_smallness_all θ₀ T hTnn hh) (aRTSFE_smallness_op θ₀ T hTnn hh hlo)

/-! ### No starvation under forced exploration (sparse targets)

Forced exploration guarantees every arm is sampled infinitely often, with no assumption on the
target — the key ingredient that extends the theory to sparse targets (`v_k = 0`). -/

/-- **Forced exploration prevents starvation, pathwise** (blueprint `lem:fe_no_starvation`, the
deterministic core). Fix a path `ω`. If the schedule diverges (`hsched → ∞`) and the path obeys the
action-level forced-exploration rule `hfe` — whenever some arm is under-explored
(`N_{m,j} ≤ h(m)` for some `j`), the chosen arm `A_m` is a *least-sampled under-explored* arm — then
every arm's pull count diverges: `N_{n,k} → ∞`.

The proof is the potential-function argument: were arm `k` to stall (`N_{n,k} ≤ B` for all `n`),
then for `n` large enough that `h(n) ≥ B` the arm `k` is under-explored, so `A_n` is least-sampled
among the under-explored arms and has count `≤ N_{n,k} ≤ B`; the potential
`D(n) = ∑_j (B + 1 - N_{n,j})^+` then drops by exactly `1` at every such step, forcing it negative —
impossible for a sum of naturals. -/
theorem no_starvation_pathwise [Finite 𝓐] [DecidableEq 𝓐] (ω : Ω) {hsched : ℕ → ℝ}
    (hh : Tendsto hsched atTop atTop)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω) (k : 𝓐) :
    Tendsto (fun n ↦ pullCount A k n ω) atTop atTop := by
  letI : Fintype 𝓐 := Fintype.ofFinite 𝓐
  refine tendsto_atTop_atTop_of_monotone (monotone_pullCount k ω) fun B ↦ ?_
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  -- `hcon : ∀ n, pullCount A k n ω < B` (arm `k` stalls below `B`).
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hh.eventually_ge_atTop (B : ℝ))
  set D : ℕ → ℕ := fun n ↦ ∑ j, (B + 1 - pullCount A j n ω) with hDdef
  -- The potential drops by exactly `1` at every step `n ≥ N₁`.
  have hdec : ∀ n, N₁ ≤ n → D (n + 1) + 1 = D n := by
    intro n hn
    have hkn : (pullCount A k n ω : ℝ) ≤ hsched n :=
      le_trans (by exact_mod_cast (hcon n).le) (hN₁ n hn)
    obtain ⟨-, hc2⟩ := hfe n ⟨k, hkn⟩
    have hcB : pullCount A (A n ω) n ω ≤ B := le_trans (hc2 k hkn) (hcon n).le
    have hsum_eq : ∑ j ∈ Finset.univ.erase (A n ω), (B + 1 - pullCount A j (n + 1) ω)
        = ∑ j ∈ Finset.univ.erase (A n ω), (B + 1 - pullCount A j n ω) :=
      Finset.sum_congr rfl fun j hj ↦ by
        rw [pullCount_eq_pullCount_of_action_ne (Finset.ne_of_mem_erase hj).symm]
    simp only [hDdef]
    rw [← Finset.add_sum_erase Finset.univ (fun j ↦ B + 1 - pullCount A j (n + 1) ω)
        (Finset.mem_univ (A n ω)),
      ← Finset.add_sum_erase Finset.univ (fun j ↦ B + 1 - pullCount A j n ω)
        (Finset.mem_univ (A n ω)),
      hsum_eq, pullCount_action_eq_pullCount_add_one]
    omega
  -- Hence `D(N₁ + t) + t = D(N₁)` for all `t`, so `t ≤ D(N₁)` — a contradiction at `t = D(N₁) + 1`.
  have hkey : ∀ t, D (N₁ + t) + t = D N₁ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hd := hdec (N₁ + t) (Nat.le_add_right N₁ t)
      change D (N₁ + t + 1) + (t + 1) = D N₁
      omega
  have hbad := hkey (D N₁ + 1)
  omega

omit [IsProbabilityMeasure P] in
/-- **Forced exploration prevents starvation** (blueprint `lem:fe_no_starvation`). For any
forced-exploration design — given here through the a.s. action-level rule `hfe`: whenever some arm
is under-explored, the next action `A_m` is a least-sampled arm among the under-explored ones — with
a diverging schedule (`hsched → ∞`), every arm is sampled infinitely often, `N_{n,k} → ∞` a.s., with
*no assumption on the target*. This is the key ingredient enabling sparse targets (`v_k = 0`); it is
the a.s. wrapper of `no_starvation_pathwise`. -/
theorem aRTSFE_no_starvation [Finite 𝓐] [DecidableEq 𝓐] {hsched : ℕ → ℝ}
    (hh : Tendsto hsched atTop atTop)
    (hfe : ∀ᵐ ω ∂P, ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω) (k : 𝓐) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ pullCount A k n ω) atTop atTop := by
  filter_upwards [hfe] with ω hfeω
  exact no_starvation_pathwise ω hh hfeω k

omit [IsProbabilityMeasure P] in
/-- If arm `k`'s pull count diverges along a path, the arm is chosen infinitely often. (Were the
hit set finite, the count would be bounded by its cardinality.) -/
lemma infinite_setOf_eq_of_pullCount_atTop [DecidableEq 𝓐] {k : 𝓐} {ω : Ω}
    (hN : Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop) :
    (setOf (fun j ↦ A j ω = k)).Infinite := by
  intro hfin
  have hbound : ∀ n, (pullCount A k n ω : ℝ) ≤ (hfin.toFinset.card : ℝ) := by
    intro n
    have hle : pullCount A k n ω ≤ hfin.toFinset.card := by
      rw [pullCount]
      refine Finset.card_le_card fun s hs ↦ ?_
      rw [Finset.mem_filter] at hs
      exact hfin.mem_toFinset.mpr hs.2
    exact_mod_cast hle
  obtain ⟨n, hn⟩ := (hN.eventually_gt_atTop (hfin.toFinset.card : ℝ)).exists
  exact absurd (hbound n) (not_le.mpr hn)

omit [IsProbabilityMeasure P] in
/-- **Forced exploration switches itself off under Condition B** (pathwise). If every arm has a
*positive* limiting proportion `N_{n,k}/n → v_k > 0` and the schedule is `o(n)`, then eventually no
arm is under-explored: `U_n = ∅`.

This shows the hypothesis `h(n) = o(√n)` of `def:exploration_schedule` is **not necessary** for the
non-sparse theory. Under Condition **B** the design eventually coincides with a plain `aRTS` design,
so the deviation gap is eventually `0` and every smallness condition holds trivially — for *any*
schedule with `h(n) = o(n)`, no matter how large. The consistency input `N_{n,k}/n → v_k` itself
needs only `h(n) = o(n)` (`IsExplorationSchedule.div_tendsto_zero`), so there is no circularity.

In particular D-Tracking's own `h(n) = (√n - K/2)^+`, which `def:exploration_schedule` currently has
to exclude, becomes admissible. And schedules with `h(n) ≫ √n` — which are what make forced
exploration, rather than the data-dependent targeting rule, decide a *sparse* arm's sample size
(see `pullCount_div_sched_tendsto_one`) — become available. -/
lemma underExplored_eventually_empty [Finite 𝓐] [DecidableEq 𝓐] {hsched : ℕ → ℝ}
    (hdiv : Tendsto (fun n ↦ hsched n / (n : ℝ)) atTop (𝓝 0))
    {v : 𝓐 → ℝ} (hv : ∀ k, 0 < v k) {ω : Ω}
    (hprop : ∀ k, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v k))) :
    ∀ᶠ n in atTop, ∀ k, hsched n < (pullCount A k n ω : ℝ) := by
  refine eventually_all.mpr fun k ↦ ?_
  have hvk := hv k
  have h1 : ∀ᶠ n in atTop, hsched n / (n : ℝ) < v k / 2 :=
    hdiv.eventually (eventually_lt_nhds (by linarith))
  have h2 : ∀ᶠ n in atTop, v k / 2 < (pullCount A k n ω : ℝ) / (n : ℝ) :=
    (hprop k).eventually (eventually_gt_nhds (by linarith))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n hn1 hn2 hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlt : hsched n / (n : ℝ) < (pullCount A k n ω : ℝ) / (n : ℝ) := hn1.trans hn2
  exact (div_lt_div_iff_of_pos_right hnR).mp hlt

/-! ### Regularity of the pull counts under forced exploration

The self-normalized componentwise CLT (`AlphaRAR.estimatorError_joint_tendsto_multivariateGaussian`)
needs more than `N_{n,k} → ∞`: it needs the **regularity** `N_{n,k}/c_{k,n} → 1` for a deterministic
`c_{k,n} → ∞`. The lemmas below show that forced exploration supplies it — with the
*deterministic* schedule `h` itself as `c` — for arms whose pulls eventually all come from the
forced-exploration mechanism.

The restriction is genuine. Since `h(n) = o(√n)` while a target-chasing design gives a sparse arm
`N_{n,k} ≈ n·T(θ̂_n)_k ≍ √n` (as `T ≥ 0` and `T(θ)_k = 0` force `∇T_k(θ) = 0`, so
`T(θ̂_n)_k = O(‖θ̂_n-θ‖²) = O(1/N_{n,k})`), forced exploration does **not** set the scale for such
designs. It does for designs that stop feeding an arm they have identified as sparse. -/

omit [IsProbabilityMeasure P] in
/-- **A forced-exploration pull leaves the count at most one above the schedule** (pathwise upper
bound), up to the pulls that forced exploration did *not* cause.

`E` is any nondecreasing counter of the "non-FE" pulls of arm `k`: it must increase by at least one
whenever arm `k` is pulled at a round where no arm is under-explored (`hEstep`). Then
`N_{n,k} ≤ max (N_{n₀,k}) (h(n) + 1) + (E n - E n₀)`.

Indeed at an FE round the selected arm is itself under-explored (`N_{m,k} ≤ h(m)`), so one pull
leaves it at `h(m) + 1 ≤ h(n) + 1`; a non-FE pull adds one but is paid for by `E`; and at all other
rounds the count does not move.

Taking `E ≡ 0` recovers the case where arm `k` is fed *only* by forced exploration — which is what
the `α = 0` throttle produces (D-Tracking). For `α > 0` the throttle only makes non-FE pulls
*sporadic*, and one takes `E` to be their count. -/
lemma pullCount_le_sched_of_fe_except [DecidableEq 𝓐] (ω : Ω) {hsched : ℕ → ℝ}
    (hmono : Monotone hsched)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    {k : 𝓐} {n₀ : ℕ} (E : ℕ → ℝ) (hEmono : Monotone E)
    (hEstep : ∀ m, n₀ ≤ m → A m ω = k → (¬ ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      E m + 1 ≤ E (m + 1))
    {n : ℕ} (hn : n₀ ≤ n) :
    (pullCount A k n ω : ℝ) ≤ max (pullCount A k n₀ ω : ℝ) (hsched n + 1) + (E n - E n₀) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hmn : hsched n ≤ hsched (n + 1) := hmono (Nat.le_succ n)
    have hEmn : E n ≤ E (n + 1) := hEmono (Nat.le_succ n)
    have hmax : max (pullCount A k n₀ ω : ℝ) (hsched n + 1)
        ≤ max (pullCount A k n₀ ω : ℝ) (hsched (n + 1) + 1) :=
      max_le_max le_rfl (by linarith)
    by_cases hA : A n ω = k
    · have hstep : pullCount A k (n + 1) ω = pullCount A k n ω + 1 := by
        rw [← hA]; exact pullCount_action_eq_pullCount_add_one n ω
      rw [hstep]
      push_cast
      by_cases hFE : ∃ j, (pullCount A j n ω : ℝ) ≤ hsched n
      · -- FE round: the selected arm was under-explored, so the pull leaves it at `h(n) + 1`
        obtain ⟨hle, -⟩ := hfe n hFE
        rw [hA] at hle
        have hE0 : E n₀ ≤ E (n + 1) := hEmono (by omega)
        have hb : (pullCount A k n ω : ℝ) + 1
            ≤ max (pullCount A k n₀ ω : ℝ) (hsched (n + 1) + 1) :=
          le_max_of_le_right (by linarith)
        linarith
      · -- non-FE round: the extra pull is paid for by `E`
        have hEs := hEstep n hn hA hFE
        linarith
    · rw [pullCount_eq_pullCount_of_action_ne hA]
      linarith

omit [IsProbabilityMeasure P] in
/-- **Forced exploration pins every count to the schedule** (pathwise lower bound). If
`Fintype.card 𝓐 * L < n - s`, then every arm has `N_{n,j} ≥ min L (h s)`.

The mechanism: at a forced-exploration round the selected arm is a *least-sampled* under-explored
arm, hence sits at the global minimum. So the potential `D(m) = ∑_j (L - N_{m,j})⁺` drops by exactly
one per round, as long as the minimum stays below `L` and forced exploration keeps firing. Since
`D ≤ card 𝓐 * L`, that can persist for at most `card 𝓐 * L` rounds — so within any longer window,
either the minimum has reached `L`, or forced exploration failed to fire, which itself means every
count already exceeds `h`. This is the same potential-function device as
`no_starvation_pathwise`. -/
lemma pullCount_ge_min_sched_of_fe [Fintype 𝓐] [DecidableEq 𝓐] (ω : Ω) {hsched : ℕ → ℝ}
    (hmono : Monotone hsched)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    {s n L : ℕ} (hlen : Fintype.card 𝓐 * L < n - s) (j : 𝓐) :
    min (L : ℝ) (hsched s) ≤ (pullCount A j n ω : ℝ) := by
  by_contra hcon
  simp only [not_le, lt_min_iff] at hcon
  obtain ⟨hjL, hjs⟩ := hcon
  have hsn : s ≤ n := by omega
  have hjLn : pullCount A j n ω < L := by exact_mod_cast hjL
  -- On `[s, n)` arm `j` witnesses both "the minimum is `< L`" and "some arm is under-explored".
  have hjm : ∀ m, s ≤ m → m ≤ n →
      pullCount A j m ω < L ∧ (pullCount A j m ω : ℝ) ≤ hsched m := by
    intro m hsm hm
    have hle : pullCount A j m ω ≤ pullCount A j n ω := monotone_pullCount j ω hm
    refine ⟨lt_of_le_of_lt hle hjLn, ?_⟩
    have hcast : (pullCount A j m ω : ℝ) ≤ (pullCount A j n ω : ℝ) := by exact_mod_cast hle
    linarith [hjs, hmono hsm]
  -- The selected arm sits at the minimum, so the potential drops by exactly one each round.
  set D : ℕ → ℕ := fun m ↦ ∑ i, (L - pullCount A i m ω) with hDdef
  have hdec : ∀ m, s ≤ m → m < n → D (m + 1) + 1 = D m := by
    intro m hsm hmn
    obtain ⟨hjmL, hjmh⟩ := hjm m hsm hmn.le
    obtain ⟨-, hmin⟩ := hfe m ⟨j, hjmh⟩
    have hAL : pullCount A (A m ω) m ω < L := lt_of_le_of_lt (hmin j hjmh) hjmL
    have hsum_eq : ∑ i ∈ Finset.univ.erase (A m ω), (L - pullCount A i (m + 1) ω)
        = ∑ i ∈ Finset.univ.erase (A m ω), (L - pullCount A i m ω) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [pullCount_eq_pullCount_of_action_ne (Finset.ne_of_mem_erase hi).symm]
    simp only [hDdef]
    rw [← Finset.add_sum_erase Finset.univ (fun i ↦ L - pullCount A i (m + 1) ω)
        (Finset.mem_univ (A m ω)),
      ← Finset.add_sum_erase Finset.univ (fun i ↦ L - pullCount A i m ω)
        (Finset.mem_univ (A m ω)),
      hsum_eq, pullCount_action_eq_pullCount_add_one]
    omega
  -- Telescoping: the window length is bounded by the initial potential `≤ card 𝓐 * L`.
  have hkey : ∀ t, s + t ≤ n → D (s + t) + t = D s := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have hd := hdec (s + t) (Nat.le_add_right s t) (by omega)
      have := ih (by omega)
      change D (s + t + 1) + (t + 1) = D s
      omega
  have hDs : D s ≤ Fintype.card 𝓐 * L := by
    simp only [hDdef]
    calc ∑ i, (L - pullCount A i s ω) ≤ ∑ _i : 𝓐, L :=
          Finset.sum_le_sum fun i _ ↦ Nat.sub_le _ _
      _ = Fintype.card 𝓐 * L := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hfin := hkey (n - s) (by omega)
  omega

omit [IsProbabilityMeasure P] in
/-- **The deterministic floor that forced exploration puts under every count.** Eventually
`N_{n,k} ≥ h(n - W(n))`, where `W(n) = K⌈h(n)⌉ + 1` is the catch-up window: within any window longer
than `W(n)` the least-sampled arm has been brought up to `⌈h(n)⌉`, or forced exploration stopped
firing — which itself means every count already exceeds `h`.

The bound is **unconditional** on the design (only forced exploration's own rule `hfe` is used), and
its right-hand side is a *deterministic* function of `n`. That is what makes it usable as the `L` of
`exists_decay_of_contDiffAt`, where the loglog rate must be measured against something that does not
depend on ω. The `hshift` hypothesis says exactly that this floor is `h(n)` to first order.

The window fits inside `[0, n]` eventually because `h(n) = o(n)`. -/
lemma eventually_schedShift_le_pullCount [Fintype 𝓐] [DecidableEq 𝓐] (ω : Ω)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    (k : 𝓐) :
    ∀ᶠ n in atTop,
      hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) ≤ (pullCount A k n ω : ℝ) := by
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < hsched n := hh.tendsto_atTop.eventually_gt_atTop 0
  have hwin : ∀ᶠ n in atTop, Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1 ≤ n := by
    have hz : Tendsto (fun n ↦ ((Fintype.card 𝓐 : ℝ) + 1) * ((hsched n + 1) / n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ (hsched n + 1) / (n : ℝ)) atTop (𝓝 0) := by
        have := hh.div_tendsto_zero.add (tendsto_one_div_atTop_nhds_zero_nat)
        simpa [add_div] using this
      simpa using h1.const_mul ((Fintype.card 𝓐 : ℝ) + 1)
    filter_upwards [hz.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)),
      eventually_gt_atTop 0, hpos] with n hn hn0 hsn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hceil : (⌈hsched n⌉₊ : ℝ) ≤ hsched n + 1 := (Nat.ceil_lt_add_one hsn.le).le
    have hcnn : (0 : ℝ) ≤ (Fintype.card 𝓐 : ℝ) := Nat.cast_nonneg _
    have hcen : (0 : ℝ) ≤ (⌈hsched n⌉₊ : ℝ) := Nat.cast_nonneg _
    have hle : ((Fintype.card 𝓐 : ℝ) * ⌈hsched n⌉₊ + 1)
        ≤ ((Fintype.card 𝓐 : ℝ) + 1) * (hsched n + 1) := by nlinarith
    have hlt : ((Fintype.card 𝓐 : ℝ) + 1) * (hsched n + 1) < n := by
      rw [← div_lt_one hnR, mul_div_assoc]
      exact hn
    exact_mod_cast le_of_lt (lt_of_le_of_lt hle hlt)
  filter_upwards [hwin] with n hn
  set L := ⌈hsched n⌉₊ with hL
  set s := n - (Fintype.card 𝓐 * L + 1) with hs
  have hlen : Fintype.card 𝓐 * L < n - s := by omega
  have hb := pullCount_ge_min_sched_of_fe ω hh.mono hfe hlen k
  have hsn' : s ≤ n := by omega
  have hmin : hsched s ≤ min (L : ℝ) (hsched s) :=
    le_min (le_trans (hh.mono hsn') (Nat.le_ceil (hsched n))) le_rfl
  exact hmin.trans hb

/-- **Forced exploration makes an FE-fed arm's pull count regular** (pathwise): `N_{n,k}/h(n) → 1`.

This is exactly the regularity hypothesis that the componentwise CLT
(`AlphaRAR.estimatorError_joint_tendsto_multivariateGaussian`) requires, with the *deterministic*
schedule `h` as the normalizer `c_{k,n}` — so for such arms forced exploration earns the CLT.

`hshift` is a mild regularity of the schedule itself: shifting the argument by the
`O(h n)` catch-up window does not change `h` to first order. It holds for the paper's
`h(n) = (n^{1/3} - K/2)^+` and for any regularly varying schedule.

`E` counts the pulls of arm `k` that forced exploration did *not* cause, and is required only to be
`o(h)`: for the `α = 0` throttle there are none (take `E ≡ 0`), and for `α > 0` the throttle makes
them sporadic enough. -/
theorem pullCount_div_sched_tendsto_one [Fintype 𝓐] [DecidableEq 𝓐] (ω : Ω) {hsched : ℕ → ℝ}
    (hh : IsExplorationSchedule hsched)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    (hshift : Tendsto
      (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n) atTop (𝓝 1))
    {k : 𝓐} {n₀ : ℕ} (E : ℕ → ℝ) (hEmono : Monotone E)
    (hEstep : ∀ m, n₀ ≤ m → A m ω = k → (¬ ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      E m + 1 ≤ E (m + 1))
    (hEsmall : Tendsto (fun n ↦ E n / hsched n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / hsched n) atTop (𝓝 1) := by
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < hsched n := hh.tendsto_atTop.eventually_gt_atTop 0
  -- Upper: once the schedule has passed the initial count, `N_{n,k} ≤ h n + 1 + (E n - E n₀)`.
  have hupper : ∀ᶠ n in atTop, (pullCount A k n ω : ℝ) / hsched n
      ≤ (hsched n + 1) / hsched n + (E n - E n₀) / hsched n := by
    filter_upwards [eventually_ge_atTop n₀, hpos,
      hh.tendsto_atTop.eventually_ge_atTop ((pullCount A k n₀ ω : ℝ))] with n hn hn0 hge
    have hb := pullCount_le_sched_of_fe_except ω hh.mono hfe E hEmono hEstep hn
    rw [← add_div]
    gcongr
    exact hb.trans (by rw [max_eq_right (by linarith)])
  -- Lower: forced exploration's deterministic floor.
  have hlower : ∀ᶠ n in atTop,
      hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n
        ≤ (pullCount A k n ω : ℝ) / hsched n := by
    filter_upwards [eventually_schedShift_le_pullCount ω hh hfe k, hpos] with n hb hsn
    gcongr
  -- Squeeze: both bounds tend to `1`.
  have hone : Tendsto (fun n ↦ (hsched n + 1) / hsched n) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n ↦ (hsched n)⁻¹) atTop (𝓝 0) := hh.tendsto_atTop.inv_tendsto_atTop
    have hsum : Tendsto (fun n ↦ 1 + (hsched n)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hpos] with n hn
    field_simp
  -- The non-FE pulls are `o(h)`, so the upper majorant still tends to `1`.
  have htop : Tendsto (fun n ↦ (hsched n + 1) / hsched n + (E n - E n₀) / hsched n)
      atTop (𝓝 1) := by
    have hconst : Tendsto (fun n : ℕ ↦ E n₀ / hsched n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hh.tendsto_atTop
    have hdiff : Tendsto (fun n ↦ (E n - E n₀) / hsched n) atTop (𝓝 0) := by
      have hs := hEsmall.sub hconst
      rw [sub_zero] at hs
      exact hs.congr fun n ↦ (sub_div _ _ _).symm
    have := hone.add hdiff
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hshift htop hlower hupper

omit [IsProbabilityMeasure P] in
/-- **The throttle fires at every round where arm `k` is not under-explored** (the "Step 3" of
`maths/sparse-clt-fix.md`, pathwise).

If arm `k` is not under-explored at round `m` (`h(m) < N_{m,k}`) and its plug-in target has decayed
below `h(m)/m` (hypotheses `hdecay`, `hgh`), then `¬ aRTSFEUnder`, i.e. arm `k` is *over-sampled*
relative to its target and not under-explored — exactly the antecedent of the `aRTS` throttling
condition, which then caps its selection probability at `α ρ̂_{m,k}`.

The comparison `g(m) < h(m)/m` is where the schedule condition enters, and it is what makes the
*reversed* condition `h(n) ≫ √n` the right one: a sparse arm has `T(Θ)_k = 0` with `T ≥ 0`, so `Θ`
minimises `T_k`, giving `ρ̂_{m,k} = O(‖Θ̂_m-Θ‖²) = O(log log h(m)/h(m))` by the subsampled LIL
(`abs_estimator_sub_le_rate_loglog_N`) once `N_{m,k} ≳ h(m)`; then `g(m) < h(m)/m` reads
`h(m)² ≫ m log log m`. Under the paper's `h(n) = o(√n)` it is false, and the arm keeps being fed by
the targeting rule. -/
lemma not_aRTSFEUnder_of_sched_lt [DecidableEq 𝓐] (ω : Ω) {hsched g : ℕ → ℝ} {θ₀ : 𝓐 → ℝ}
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐} {m : ℕ} (hm : 0 < m)
    (hnot : hsched m < (pullCount A k m ω : ℝ))
    (hdecay : aRTSTarget A Y θ₀ T m ω k ≤ g m)
    (hgh : g m < hsched m / (m : ℝ)) :
    ¬ aRTSFEUnder A Y θ₀ T hsched k ω m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [aRTSFEUnder, count_indicator_eq_pullCount]
  simp only [not_or, not_le]
  refine ⟨?_, hnot⟩
  calc (m : ℝ) * aRTSTarget A Y θ₀ T m ω k ≤ (m : ℝ) * g m := by gcongr
    _ < (m : ℝ) * (hsched m / (m : ℝ)) := by gcongr
    _ = hsched m := by field_simp
    _ < _ := hnot

/-- The previous-history filtration sits below the current one: `ℱ_{i-1} ≤ ℱ_i`. -/
lemma shiftDown_le_self (𝔾 : Filtration ℕ mΩ) (i : ℕ) : 𝔾.shiftDown i ≤ 𝔾 i := by
  cases i with
  | zero => exact bot_le
  | succ p => exact 𝔾.mono (Nat.le_succ p)

/-- The count `N_{m,k}` is a **previous-history** statistic: it reads only `A_0,…,A_{m-1}`. -/
lemma measurable_shiftDown_count
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (m : ℕ) :
    Measurable[(IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback).shiftDown m]
      (fun ω ↦ count (fun j ↦ armIndicator A k j ω) m) := by
  cases m with
  | zero =>
    simp only [count, Finset.range_zero, Finset.sum_empty]
    exact measurable_const
  | succ p =>
    simp only [count]
    refine Finset.measurable_sum _ fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    exact (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
      (IsAlgEnvSeq.measurable_action_filtration h.measurable_action h.measurable_feedback
        (by omega : j ≤ p)))

/-- The forced-exploration predicate at round `m` is a **previous-history** event: both the count
`N_{m,k}` and the plug-in target `ρ̂_{m,k}` are built from `A_0,…,A_{m-1}` and `Y_0,…,Y_{m-1}`.

This is what lets the throttle be applied *inside* a conditional expectation given `ℱ_{m-1}`, and it
is what makes the `α = 0` argument below work with no decay hypothesis at all. -/
lemma measurableSet_shiftDown_aRTSFEUnder [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ}
    (hT : Continuous T) (hsched : ℕ → ℝ) (k : 𝓐) (m : ℕ) :
    MeasurableSet[(IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback).shiftDown m]
      {ω | aRTSFEUnder A Y θ₀ T hsched k ω m} := by
  cases m with
  | zero =>
    have huniv : {ω | aRTSFEUnder A Y θ₀ T hsched k ω 0} = Set.univ := by
      ext ω; simp [aRTSFEUnder, count]
    rw [huniv]; exact MeasurableSet.univ
  | succ p =>
    set 𝔾 := IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback with h𝔾
    have harm : ∀ (k' : 𝓐) (j : ℕ), j ≤ p → Measurable[𝔾 p] (armIndicator A k' j) := by
      intro k' j hj
      exact (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k').preimage
        (IsAlgEnvSeq.measurable_action_filtration h.measurable_action h.measurable_feedback hj))
    have hcount : ∀ k' : 𝓐,
        Measurable[𝔾 p] (fun ω ↦ count (fun j ↦ armIndicator A k' j ω) (p + 1)) :=
      fun k' ↦ measurable_shiftDown_count h k' (p + 1)
    have hnum : ∀ k' : 𝓐, Measurable[𝔾 p]
        (fun ω ↦ ∑ j ∈ Finset.range (p + 1), armIndicator A k' j ω * Y j ω) := by
      intro k'
      refine Finset.measurable_sum _ fun j hj ↦ ?_
      rw [Finset.mem_range] at hj
      exact (harm k' j (by omega : j ≤ p)).mul
        (IsAlgEnvSeq.measurable_feedback_filtration h.measurable_action h.measurable_feedback
          (by omega : j ≤ p))
    have hest : @Measurable Ω (𝓐 → ℝ) (𝔾 p) inferInstance
        (fun ω k' ↦ estimator (fun j ↦ armIndicator A k' j ω) (fun j ↦ Y j ω) (θ₀ k') (p + 1)) := by
      refine @measurable_pi_lambda Ω 𝓐 (fun _ ↦ ℝ) (𝔾 p) (fun _ ↦ inferInstance) _ fun k' ↦ ?_
      simp only [estimator]
      exact ((hnum k').add_const _).div ((hcount k').add_const 1)
    have htarget : Measurable[𝔾 p] (fun ω ↦ aRTSTarget A Y θ₀ T (p + 1) ω k) := by
      simp only [aRTSTarget]
      exact (measurable_pi_apply k).comp (hT.measurable.comp hest)
    exact (measurableSet_le (hcount k) (measurable_const.mul htarget)).union
      (measurableSet_le (hcount k) measurable_const)

/-- **A previous-history event on which the selection probability vanishes is never a pull.** If
`S m` is `ℱ_{m-1}`-measurable and `p_{m,k} ≤ 0` there, then almost surely `A_m ≠ k` on `S m`.

The conditional probability is nonnegative, so it is *zero* on `S m`; integrating the indicator over
the previous-history event `S m` therefore gives `0`, and a nonnegative function with zero integral
vanishes a.e. Measurability of `S m` with respect to `ℱ_{m-1}` — not merely `ℱ_m` — is what makes
`setIntegral_condExp` applicable, and is the crux: the conditioning event has to be decided before
the draw it constrains.

Both ways the aRTS family forbids a pull factor through this: the `α = 0` throttle
(`not_pulled_of_not_aRTSFEUnder_of_alpha_zero`) and forced exploration's exclusion of arms that are
not least-sampled (`fe_of_isARTSFE`). -/
lemma ae_action_ne_of_selProb_nonpos
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) {k : 𝓐} {S : ℕ → Set Ω}
    (hS : ∀ m, MeasurableSet[(IsAlgEnvSeq.filtration h.measurable_action
      h.measurable_feedback).shiftDown m] (S m))
    (hsel : ∀ᵐ ω ∂P, ∀ m, ω ∈ S m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ 0) :
    ∀ᵐ ω ∂P, ∀ m, ω ∈ S m → A m ω ≠ k := by
  set 𝔽 := IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback with h𝔽
  have hint : ∀ i, Integrable (armIndicator A k i) P := fun i ↦
    (integrable_const (1 : ℝ)).indicator ((h.measurable_action i) (measurableSet_singleton k))
  have hstep : ∀ m, ∀ᵐ ω ∂P, ω ∈ S m → A m ω ≠ k := by
    intro m
    have hSmeas : MeasurableSet[𝔽.shiftDown m] (S m) := hS m
    have hzero : ∫ ω in S m, armIndicator A k m ω ∂P = 0 := by
      rw [← setIntegral_condExp (𝔽.shiftDown.le m) (hint m) hSmeas]
      refine setIntegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hsel, condExp_nonneg (m := 𝔽.shiftDown m) (f := armIndicator A k m)
        (ae_of_all _ fun ω ↦ armIndicator_nonneg A k m ω)] with ω hthr hnn hωS
      exact le_antisymm (hthr m hωS) hnn
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun ω ↦ armIndicator_nonneg A k m ω) ((hint m).restrict (s := S m))).mp hzero
    rw [Filter.EventuallyEq, ae_restrict_iff' ((𝔽.shiftDown).le m _ hSmeas)] at hae
    filter_upwards [hae] with ω hω hnot hAk
    have hval : armIndicator A k m ω = 1 := by
      simp only [armIndicator]
      rw [Set.indicator_of_mem (show ω ∈ {ω | A m ω = k} from hAk)]
    have hzeroω := hω hnot
    rw [hval] at hzeroω
    exact one_ne_zero hzeroω
  exact ae_all_iff.mpr hstep

/-- **`IsARTSFE` discharges the throttle hypothesis**, exactly as `throttle_of_isARTS` does for
`IsARTS`. At `m = 0` the antecedent is vacuous (`N_0 = 0 ≤ 0 · ρ̂`); at `m = n+1` it is
`IsARTSFE.throttle` transported through `aRTSSelProb_succ_ae`, `histTarget_eq` and `histCount_eq`.
The two premises of the field are the two disjuncts of `¬ aRTSFEUnder`. -/
lemma throttle_of_isARTSFE [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {hsched : ℕ → ℝ} {α : ℝ}
    (hFE : IsARTSFE alg θ₀ T hsched α) (k : 𝓐) :
    ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k := by
  refine ae_all_iff.mpr fun m ↦ ?_
  cases m with
  | zero =>
    filter_upwards with ω hm
    exact absurd (by simp [aRTSFEUnder, count] : aRTSFEUnder A Y θ₀ T hsched k ω 0) hm
  | succ n =>
    filter_upwards [aRTSSelProb_succ_ae h k n] with ω hsel hm
    rw [aRTSFEUnder, not_or, not_le, not_le] at hm
    obtain ⟨hover, hexpl⟩ := hm
    rw [hsel, ← histTarget_eq]
    refine hFE.throttle n (history A Y n ω) k ?_ ?_
    · rw [histTarget_eq, ← histCount_eq]
      push_cast at hover ⊢
      linarith
    · rw [← histCount_eq]; exact hexpl

/-- The rounds at which forced exploration **forbids** arm `k`: some arm is under-explored, yet `k`
is either not under-explored itself or not among the least-sampled. -/
def feForbidden [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (hsched : ℕ → ℝ) (k : 𝓐) (m : ℕ) : Set Ω :=
  {ω | (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) ∧
    (hsched m < (pullCount A k m ω : ℝ) ∨
      ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m ∧
        (pullCount A j m ω : ℝ) < (pullCount A k m ω : ℝ))}

/-- `feForbidden` is a **previous-history** event: it is built from counts alone. -/
lemma measurableSet_shiftDown_feForbidden [Finite 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hsched : ℕ → ℝ) (k : 𝓐) (m : ℕ) :
    MeasurableSet[(IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback).shiftDown m]
      (feForbidden A hsched k m) := by
  have hcount : ∀ k' : 𝓐,
      Measurable[(IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback).shiftDown m]
        (fun ω ↦ (pullCount A k' m ω : ℝ)) := by
    intro k'
    have heq : (fun ω ↦ (pullCount A k' m ω : ℝ))
        = fun ω ↦ count (fun j ↦ armIndicator A k' j ω) m :=
      funext fun ω ↦ (count_indicator_eq_pullCount k' m ω).symm
    rw [heq]
    exact measurable_shiftDown_count h k' m
  have hex : MeasurableSet[(IsAlgEnvSeq.filtration h.measurable_action
      h.measurable_feedback).shiftDown m] {ω | ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m} := by
    have hset : {ω | ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m}
        = ⋃ j, {ω | (pullCount A j m ω : ℝ) ≤ hsched m} := by ext ω; simp
    rw [hset]
    exact MeasurableSet.iUnion fun j ↦ measurableSet_le (hcount j) measurable_const
  have hmin : MeasurableSet[(IsAlgEnvSeq.filtration h.measurable_action
      h.measurable_feedback).shiftDown m]
      {ω | ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m ∧
        (pullCount A j m ω : ℝ) < (pullCount A k m ω : ℝ)} := by
    have hset : {ω | ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m ∧
        (pullCount A j m ω : ℝ) < (pullCount A k m ω : ℝ)}
        = ⋃ j, ({ω | (pullCount A j m ω : ℝ) ≤ hsched m} ∩
          {ω | (pullCount A j m ω : ℝ) < (pullCount A k m ω : ℝ)}) := by ext ω; simp
    rw [hset]
    exact MeasurableSet.iUnion fun j ↦
      (measurableSet_le (hcount j) measurable_const).inter (measurableSet_lt (hcount j) (hcount k))
  exact hex.inter ((measurableSet_lt measurable_const (hcount k)).union hmin)

/-- **`IsARTSFE` discharges the forced-exploration hypothesis `hfe`.** Almost surely, whenever some
arm is under-explored, the arm actually drawn is under-explored and least-sampled.

The `forced` field says the policy gives every *other* arm mass zero; `aRTSSelProb_succ_ae` turns
that into `p_{m,k} = 0`, and `ae_action_ne_of_selProb_nonpos` — whose hypothesis is met because
`feForbidden` is a previous-history event — turns it into "`k` is a.s. not drawn". Ranging over the
(countably many) arms and instantiating at `k = A_m ω` gives the claim. At `m = 0` all counts are
zero, so `feForbidden` is empty and there is nothing to prove. -/
lemma fe_of_isARTSFE [Finite 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {hsched : ℕ → ℝ} {α : ℝ}
    (hFE : IsARTSFE alg θ₀ T hsched α) :
    ∀ᵐ ω ∂P, ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω := by
  have hsel : ∀ k : 𝓐, ∀ᵐ ω ∂P, ∀ m, ω ∈ feForbidden A hsched k m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ 0 := by
    intro k
    refine ae_all_iff.mpr fun m ↦ ?_
    cases m with
    | zero =>
      filter_upwards with ω hω
      obtain ⟨⟨j, hj⟩, hbad⟩ := hω
      have hz : ∀ j' : 𝓐, (pullCount A j' 0 ω : ℝ) = 0 := fun j' ↦ by
        rw [← count_indicator_eq_pullCount]; simp [count]
      rw [hz j] at hj
      rcases hbad with hbad | ⟨j', _, hj'⟩
      · rw [hz k] at hbad; linarith
      · rw [hz j', hz k] at hj'; linarith
    | succ n =>
      filter_upwards [aRTSSelProb_succ_ae h k n] with ω hselω hω
      obtain ⟨hex, hbad⟩ := hω
      have hpc : ∀ j : 𝓐, (pullCount A j (n + 1) ω : ℝ)
          = (pullCount' n (history A Y n ω) j : ℝ) := fun j ↦ by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
          (pullCount_add_one_eq_pullCount' (A := A) (R' := Y) (a := j) (n := n) (ω := ω))
      simp only [hpc] at hex hbad
      rw [hselω, hFE.forced n (history A Y n ω) k hex hbad]
      simp
  have hall : ∀ᵐ ω ∂P, ∀ (k : 𝓐) (m : ℕ), ω ∈ feForbidden A hsched k m → A m ω ≠ k :=
    ae_all_iff.mpr fun k ↦ ae_action_ne_of_selProb_nonpos h
      (fun m ↦ measurableSet_shiftDown_feForbidden h hsched k m) (hsel k)
  filter_upwards [hall] with ω hω m hex
  by_contra hcon
  refine hω (A m ω) m ⟨hex, ?_⟩ rfl
  rw [not_and_or] at hcon
  rcases hcon with h1 | h2
  · exact Or.inl (lt_of_not_ge h1)
  · push Not at h2
    obtain ⟨j, hj1, hj2⟩ := h2
    exact Or.inr ⟨j, hj1, by exact_mod_cast hj2⟩

/-- **For `α = 0` the throttle forbids throttled pulls outright** (Step 4, `α = 0`, in its correct
pathwise form). Whenever arm `k` is neither under-sampled nor under-explored, it is a.s. not pulled.

This needs **no decay hypothesis at all**: the conditioning event `{¬ aRTSFEUnder}` is itself
previous-history measurable
(`measurableSet_shiftDown_aRTSFEUnder`), so the throttle applies inside the conditional expectation
directly. That matters, because the decay bound has a *random* constant (the LIL constant), so a
hypothesis of the form "`ρ̂ ≤ g` for a deterministic `g`" is not dischargeable — see
`aRTSTarget_le_loglog_of_quadratic`. The decay is then applied *pathwise* afterwards, via
`not_aRTSFEUnder_of_sched_lt`. -/
lemma not_pulled_of_not_aRTSFEUnder_of_alpha_zero [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ}
    (hT : Continuous T) {hsched : ℕ → ℝ} {k : 𝓐}
    (hthrottle : ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ 0) :
    ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m → A m ω ≠ k :=
  ae_action_ne_of_selProb_nonpos h
    (fun m ↦ (measurableSet_shiftDown_aRTSFEUnder h θ₀ hT hsched k m).compl) hthrottle

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **The plug-in target of a sparse arm decays at the loglog rate** (the `hdecay` input of
`not_aRTSFEUnder_of_sched_lt`), pathwise.

Since the target takes values in the simplex (`T ≥ 0`) and `T(Θ)_k = v_k = 0` for a sparse arm, the
point `Θ` *minimises* `x ↦ T(x)_k`; hence `∇T_k(Θ) = 0` and a `C²` target obeys a local quadratic
bound `T(x)_k ≤ Cq ‖x - Θ‖²`, which is hypothesis `hquad`. Feeding in the per-arm loglog rate
`hrate` — what the subsampled LIL `abs_estimator_sub_le_rate_loglog_N` delivers, after replacing the
random count `N_{m,j}` by a deterministic lower bound `L m` — gives `ρ̂_{m,k} = O(log log m / L m)`.

Combined with `L m ≳ h m` (forced exploration, `pullCount_ge_min_sched_of_fe`) this is the decay the
throttle step consumes: `ρ̂_{m,k} < h(m)/m` reduces to `h(m)² ≫ m log log m`, i.e. exactly `(⋆)`.

**The constant is necessarily random**: the LIL constant depends on `ω`. So the `hdecay` hypothesis
of the throttle lemmas cannot be met with a *deterministic* bound — it has to be read pathwise,
which is how `not_aRTSFEUnder_of_sched_lt` is stated. -/
lemma aRTSTarget_le_loglog_of_quadratic [Fintype 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐} {Cq C : ℝ} {L : ℕ → ℝ}
    (hCq : 0 ≤ Cq) (hLnn : ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log (Real.log m) / L m)
    (hquad : ∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k
      ≤ Cq * ∑ j, (estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m
          - (ν j)[id]) ^ 2)
    (hrate : ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m - (ν j)[id]|
        ≤ C * Real.sqrt (Real.log (Real.log m) / L m)) :
    ∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k
      ≤ (Cq * Fintype.card 𝓐 * C ^ 2) * (Real.log (Real.log m) / L m) := by
  filter_upwards [hquad, eventually_all.mpr hrate, hLnn] with m hq hr hLm
  refine hq.trans ?_
  have hterm : ∀ j ∈ (Finset.univ : Finset 𝓐),
      (estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m - (ν j)[id]) ^ 2
        ≤ C ^ 2 * (Real.log (Real.log m) / L m) := by
    intro j _
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hr j) 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hLm] at h2
    exact h2
  calc Cq * ∑ j, (estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m
          - (ν j)[id]) ^ 2
      ≤ Cq * ∑ _j : 𝓐, C ^ 2 * (Real.log (Real.log m) / L m) := by
        gcongr with j hj
        exact hterm j hj
    _ = (Cq * Fintype.card 𝓐 * C ^ 2) * (Real.log (Real.log m) / L m) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **The quadratic bound `hquad` comes for free from a `C²` target**, so it need not be assumed.

For a *sparse* arm `k` one has `T(Θ)_k = v_k = 0` while `T ≥ 0` everywhere (the target takes values
in the simplex), so `Θ` is a global minimum of `x ↦ T(x)_k`. Fermat's theorem kills the linear term
of the Taylor expansion, and `C²` smoothness turns the remainder into `K‖x - Θ‖²`
(`IsLocalMin.exists_eventually_sub_le_mul_sq`) — no Hessian is ever named. Consistency `θ̂_m → Θ`
puts the plug-in point inside that neighbourhood eventually.

The sup norm of `𝓐 → ℝ` is converted to the coordinatewise sum by `sq_norm_le_sum_sq`, which is the
shape in which the per-arm rates of `aRTSTarget_le_loglog_of_quadratic` plug in. -/
lemma exists_aRTSTarget_le_mul_sum_sq [Fintype 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐}
    (hT2 : ContDiffAt ℝ 2 (fun z ↦ T z k) (fun j ↦ (ν j)[id]))
    (hTnn : ∀ z, 0 ≤ T z k) (hTzero : T (fun j ↦ (ν j)[id]) k = 0)
    (hcons : ∀ j, Tendsto
      (fun m ↦ estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m)
      atTop (𝓝 ((ν j)[id]))) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k
      ≤ Cq * ∑ j, (estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m
          - (ν j)[id]) ^ 2 := by
  have hmin : IsLocalMin (fun z ↦ T z k) (fun j ↦ (ν j)[id]) := by
    apply Eventually.of_forall
    intro z
    change T (fun j ↦ (ν j)[id]) k ≤ T z k
    rw [hTzero]
    exact hTnn z
  obtain ⟨K, hK, hbd⟩ := exists_eventually_sub_le_mul_sq_of_isLocalMin hmin hT2
  have hest : Tendsto
      (fun m ↦ fun j ↦ estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m)
      atTop (𝓝 fun j ↦ (ν j)[id]) := tendsto_pi_nhds.mpr hcons
  refine ⟨K, hK, ?_⟩
  filter_upwards [hest.eventually hbd] with m hm
  have hkey : T (fun j ↦ estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m) k
      - T (fun j ↦ (ν j)[id]) k
      ≤ K * ‖(fun j ↦ estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m)
          - (fun j ↦ (ν j)[id])‖ ^ 2 := hm
  rw [hTzero, sub_zero] at hkey
  exact hkey.trans (mul_le_mul_of_nonneg_left (sq_norm_le_sum_sq _) hK)

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **The loglog decay of a sparse arm's plug-in target, from `C²` smoothness alone.**

This is `aRTSTarget_le_loglog_of_quadratic` with its `hquad` hypothesis discharged by
`exists_aRTSTarget_le_mul_sum_sq`: the only structural input left is that `x ↦ T(x)_k` is `C²` at
`Θ`, nonnegative, and vanishes there (sparsity). Consistency of `θ̂` is not assumed either — it
follows from `hrate` together with `log log m / L m → 0`, which `L m ≳ h m → ∞` already gives.

The constant is existentially quantified because it is genuinely `ω`-dependent: `C` is the LIL
constant. -/
lemma exists_aRTSTarget_le_loglog_of_contDiffAt [Fintype 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐} {C : ℝ} {L : ℕ → ℝ}
    (hT2 : ContDiffAt ℝ 2 (fun z ↦ T z k) (fun j ↦ (ν j)[id]))
    (hTnn : ∀ z, 0 ≤ T z k) (hTzero : T (fun j ↦ (ν j)[id]) k = 0)
    (hLnn : ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log (Real.log m) / L m)
    (hL0 : Tendsto (fun m : ℕ ↦ Real.log (Real.log m) / L m) atTop (𝓝 0))
    (hrate : ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m - (ν j)[id]|
        ≤ C * Real.sqrt (Real.log (Real.log m) / L m)) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k
      ≤ Cq * (Real.log (Real.log m) / L m) := by
  have hsqrt : Tendsto (fun m : ℕ ↦ C * Real.sqrt (Real.log (Real.log m) / L m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ ↦ Real.sqrt (Real.log (Real.log m) / L m)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hL0
    simpa using h1.const_mul C
  have hcons : ∀ j, Tendsto
      (fun m ↦ estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m)
      atTop (𝓝 ((ν j)[id])) := by
    intro j
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun m ↦ dist_nonneg) ?_ hsqrt
    filter_upwards [hrate j] with m hm
    rwa [Real.dist_eq]
  obtain ⟨Cq, hCq, hquad⟩ := exists_aRTSTarget_le_mul_sum_sq ω hT2 hTnn hTzero hcons
  exact ⟨Cq * Fintype.card 𝓐 * C ^ 2,
    mul_nonneg (mul_nonneg hCq (Nat.cast_nonneg _)) (sq_nonneg _),
    aRTSTarget_le_loglog_of_quadratic ω hCq hLnn hquad hrate⟩

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **Condition `(⋆)` beats every constant.** If `m log log m = o(L(m) h(m))` then for *any*
constant `Cq` the loglog bound eventually sits strictly below `h(m)/m`.

Quantifying over `Cq` is the whole point: the constant coming out of the LIL is random, so the
comparison has to survive an arbitrary one. Rearranged, `Cq (log log m)/L(m) < h(m)/m` is
`Cq · m log log m < L(m) h(m)`, and with `L ≍ h` this is `h(m)² ≫ m log log m`, i.e. `(⋆)` of
`maths/sparse-clt-fix.md`. -/
lemma eventually_mul_loglog_div_lt_of_star {hsched L : ℕ → ℝ} (Cq : ℝ)
    (hpos : ∀ᶠ m : ℕ in atTop, 0 < L m ∧ 0 < hsched m)
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (L m * hsched m))
      atTop (𝓝 0)) :
    ∀ᶠ m : ℕ in atTop, Cq * (Real.log (Real.log m) / L m) < hsched m / (m : ℝ) := by
  have h1 : Tendsto (fun m : ℕ ↦ Cq * ((m : ℝ) * Real.log (Real.log m) / (L m * hsched m)))
      atTop (𝓝 0) := by simpa using hstar.const_mul Cq
  filter_upwards [hpos, h1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop 0] with m hm hlt hm0
  obtain ⟨hL, hh⟩ := hm
  have hm0' : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hstep := mul_lt_mul_of_pos_right hlt (div_pos hh hm0')
  rw [one_mul] at hstep
  calc Cq * (Real.log (Real.log m) / L m)
      = Cq * ((m : ℝ) * Real.log (Real.log m) / (L m * hsched m)) * (hsched m / (m : ℝ)) := by
        field_simp
    _ < hsched m / (m : ℝ) := hstep

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **`C²` smoothness plus `(⋆)` supply the `hdecay` input of `fEfed_of_decay`**, pathwise.

This closes the chain of `maths/sparse-clt-fix.md`: nothing about the target map is assumed beyond
`C²` at `Θ`, nonnegativity, and `T(Θ)_k = 0` (sparsity of arm `k`); the loglog rate `hrate` is what
the subsampled LIL delivers, and `(⋆)` is the reversed schedule condition
`√(m log log m) ≪ h(m) = o(m)` which replaces the paper's `h(m) = o(√m)`.

The randomness of the LIL constant is handled where it belongs: `g` is produced *inside* the
pathwise statement, and `eventually_mul_loglog_div_lt_of_star` is uniform in that constant. -/
lemma exists_decay_of_contDiffAt [Fintype 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐} {C : ℝ} {L hsched : ℕ → ℝ}
    (hT2 : ContDiffAt ℝ 2 (fun z ↦ T z k) (fun j ↦ (ν j)[id]))
    (hTnn : ∀ z, 0 ≤ T z k) (hTzero : T (fun j ↦ (ν j)[id]) k = 0)
    (hLnn : ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log (Real.log m) / L m)
    (hL0 : Tendsto (fun m : ℕ ↦ Real.log (Real.log m) / L m) atTop (𝓝 0))
    (hpos : ∀ᶠ m : ℕ in atTop, 0 < L m ∧ 0 < hsched m)
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (L m * hsched m))
      atTop (𝓝 0))
    (hrate : ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m - (ν j)[id]|
        ≤ C * Real.sqrt (Real.log (Real.log m) / L m)) :
    ∃ g : ℕ → ℝ, (∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k ≤ g m) ∧
      (∀ᶠ m in atTop, g m < hsched m / (m : ℝ)) := by
  obtain ⟨Cq, _, hCq⟩ :=
    exists_aRTSTarget_le_loglog_of_contDiffAt ω hT2 hTnn hTzero hLnn hL0 hrate
  exact ⟨fun m ↦ Cq * (Real.log (Real.log m) / L m), hCq,
    eventually_mul_loglog_div_lt_of_star Cq hpos hstar⟩

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **From the `N`-scaled loglog rate to a deterministic one.** The subsampled LIL
(`abs_estimator_sub_le_rate_loglog_N`) measures the estimator error against the arm's *own random*
count `N_{m,j}`, whereas `exists_decay_of_contDiffAt` needs it measured against a *deterministic*
`L(m)`. Given a deterministic floor `L(m) ≤ N_{m,j}` diverging to infinity, the two are compatible:

`log log N_{m,j} / N_{m,j} ≤ log log m / L(m)`,

since `N_{m,j} ≤ m` makes the numerator only smaller while `L(m) ≤ N_{m,j}` makes the denominator
only smaller. Both facts are needed — the floor alone would not control the numerator, and this is
why the argument runs through `log log m` rather than the more natural-looking `log log L(m)`.

The constants are merged into `∑ j |C_j|`, which dominates every `C_j` and is nonnegative; taking a
single constant is what lets `aRTSTarget_le_loglog_of_quadratic` sum the squared errors. -/
lemma exists_rate_loglog_of_pullCount_ge [Finite 𝓐] [DecidableEq 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {L : ℕ → ℝ} (hLtop : Tendsto L atTop atTop)
    (hLle : ∀ j, ∀ᶠ m in atTop, L m ≤ (pullCount A j m ω : ℝ))
    (hC : ∀ j, ∃ C' : ℝ, ∀ᶠ m in atTop,
      |estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m - (ν j)[id]|
        ≤ C' * Real.sqrt (Real.log (Real.log (pullCount A j m ω : ℝ))
            / (pullCount A j m ω : ℝ))) :
    ∃ C : ℝ, ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m - (ν j)[id]|
        ≤ C * Real.sqrt (Real.log (Real.log m) / L m) := by
  classical
  letI := Fintype.ofFinite 𝓐
  choose C' hC' using hC
  refine ⟨∑ i, |C' i|, fun j ↦ ?_⟩
  have hCnn : (0 : ℝ) ≤ ∑ i, |C' i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hCle : C' j ≤ ∑ i, |C' i| :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i ↦ |C' i|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ j))
  filter_upwards [hC' j, hLle j, hLtop.eventually_ge_atTop (Real.exp 1)] with m hm hLm hLe
  have hLpos : (0 : ℝ) < L m := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hNpos : (0 : ℝ) < (pullCount A j m ω : ℝ) := lt_of_lt_of_le hLpos hLm
  have hNm : (pullCount A j m ω : ℝ) ≤ (m : ℝ) := by exact_mod_cast pullCount_le j m ω
  -- `N ≥ e` gives `log N ≥ 1`, hence `log log N ≥ 0`; and `N ≤ m` gives `log log N ≤ log log m`.
  have hlogN : (1 : ℝ) ≤ Real.log (pullCount A j m ω : ℝ) :=
    (Real.le_log_iff_exp_le hNpos).mpr (hLe.trans hLm)
  have hlogm : Real.log (pullCount A j m ω : ℝ) ≤ Real.log m := Real.log_le_log hNpos hNm
  have hll : Real.log (Real.log (pullCount A j m ω : ℝ)) ≤ Real.log (Real.log m) :=
    Real.log_le_log (by linarith) hlogm
  have hllnn : (0 : ℝ) ≤ Real.log (Real.log (pullCount A j m ω : ℝ)) := Real.log_nonneg hlogN
  have hkey : Real.log (Real.log (pullCount A j m ω : ℝ)) / (pullCount A j m ω : ℝ)
      ≤ Real.log (Real.log m) / L m := by
    calc Real.log (Real.log (pullCount A j m ω : ℝ)) / (pullCount A j m ω : ℝ)
        ≤ Real.log (Real.log m) / (pullCount A j m ω : ℝ) := by gcongr
      _ ≤ Real.log (Real.log m) / L m := by
          gcongr
          linarith
  calc |estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m - (ν j)[id]|
      ≤ C' j * Real.sqrt (Real.log (Real.log (pullCount A j m ω : ℝ))
          / (pullCount A j m ω : ℝ)) := hm
    _ ≤ (∑ i, |C' i|) * Real.sqrt (Real.log (Real.log (pullCount A j m ω : ℝ))
          / (pullCount A j m ω : ℝ)) := by gcongr
    _ ≤ (∑ i, |C' i|) * Real.sqrt (Real.log (Real.log m) / L m) := by gcongr

/-- The indicator of a **throttled pull** of arm `k`: arm `k` is selected at round `i` while it is
neither under-sampled nor under-explored — so neither the targeting rule nor forced exploration
called for it, and the `αRTS` throttle caps its probability at `α ρ̂_{i,k}`. -/
noncomputable def throttledIndicator (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hsched : ℕ → ℝ) (k : 𝓐) (i : ℕ) : Ω → ℝ :=
  {ω | ¬ aRTSFEUnder A Y θ₀ T hsched k ω i}.indicator (armIndicator A k i)

/-- **The throttled pulls are `o(h)`** (Step 4 of `maths/sparse-clt-fix.md`, the general `α > 0`
case, in its correct pathwise form). Their count satisfies `E_n/h(n) → 0` a.s.

Doob-decompose `E_n = M_n + ∑_{i<n} P[𝟙 | ℱ_{i-1}]`. The conditioning event
`{¬ aRTSFEUnder i}` is previous-history measurable (`measurableSet_shiftDown_aRTSFEUnder`), so
`condExp_indicator` pulls it out and the throttle applies with **no side condition**, giving
`P[𝟙 | ℱ_{i-1}] ≤ α ρ̂_{i,k}` for *every* `i`; the martingale part is `O(√(n log log n))` by
`ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog`.

Compare the deterministic-bound version this replaces: because the loglog decay of `ρ̂_{i,k}`
carries
a *random* constant (the LIL constant — see `aRTSTarget_le_loglog_of_quadratic`), a hypothesis
"`ρ̂ ≤ g` for a deterministic `g`" is not dischargeable. Here the compensator is compared against
the
*random* `∑ α ρ̂_{i,k}(ω)` instead, and `hsum` asks only that this be `o(h(n))` almost surely —
which
is harmless, since a random constant is fine inside an a.s. limit. The hypotheses `m₀`, `g`, `hgh`
and `hdecay` all disappear.

Step 3 (`not_aRTSFEUnder_of_sched_lt`) is what relates this count to the one
`pullCount_le_sched_of_fe_except` consumes: pathwise, and eventually, a pull at a round where arm
`k`
is not under-explored *is* a throttled pull. -/
theorem throttled_count_div_sched_tendsto_zero [Finite 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) {hsched : ℕ → ℝ} {θ₀ : 𝓐 → ℝ}
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (hTnn : ∀ z k, 0 ≤ T z k) {k : 𝓐} {α : ℝ}
    (hα : 0 ≤ α)
    (hthrottle : ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hsched_atTop : Tendsto hsched atTop atTop)
    (hsum : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k) / hsched n) atTop (𝓝 0))
    (hsqrt : ∀ C : ℝ,
      Tendsto (fun n : ℕ ↦ C * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / hsched n)
        atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ count (fun i ↦ throttledIndicator A Y θ₀ T hsched k i ω) n / hsched n)
      atTop (𝓝 0) := by
  set 𝔽 := IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback with h𝔽
  set X : ℕ → Ω → ℝ := fun i ↦ throttledIndicator A Y θ₀ T hsched k i with hXdef
  set S : ℕ → Set Ω := fun i ↦ {ω | ¬ aRTSFEUnder A Y θ₀ T hsched k ω i} with hSdef
  have hSm : ∀ i, MeasurableSet[𝔽.shiftDown i] (S i) := fun i ↦
    (measurableSet_shiftDown_aRTSFEUnder h θ₀ hT hsched k i).compl
  have hintarm : ∀ i, Integrable (armIndicator A k i) P := fun i ↦
    (integrable_const (1 : ℝ)).indicator ((h.measurable_action i) (measurableSet_singleton k))
  have hX0 : ∀ i ω, 0 ≤ X i ω := fun i ω ↦
    Set.indicator_nonneg (fun _ _ ↦ armIndicator_nonneg A k i _) ω
  have hX1 : ∀ i ω, X i ω ≤ 1 := fun i ω ↦ by
    change ((S i).indicator (armIndicator A k i)) ω ≤ 1
    rw [Set.indicator_apply]
    split_ifs with hc
    · exact armIndicator_le_one A k i ω
    · norm_num
  have hXint : ∀ i, Integrable (X i) P := fun i ↦
    (hintarm i).indicator ((𝔽.shiftDown).le i _ (hSm i))
  have hXadapt : StronglyAdapted 𝔽 X := fun i ↦
    StronglyMeasurable.indicator
      (((measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
        (IsAlgEnvSeq.measurable_action_filtration h.measurable_action h.measurable_feedback
          (le_refl i)))).stronglyMeasurable)
      (shiftDown_le_self 𝔽 i _ (hSm i))
  -- (a) The martingale part is `O(√(n log log n))`.
  have hLIL := ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog (ℱ := 𝔽) hXadapt hXint
    (fun n ↦ ae_of_all _ fun ω ↦ hX0 n ω) (fun n ↦ ae_of_all _ fun ω ↦ hX1 n ω)
  -- (b) The compensator is bounded by `α ρ̂_{i,k}` at *every* round — no side condition.
  have hcondle : ∀ i, ∀ᵐ ω ∂P,
      (P[X i | 𝔽.shiftDown i]) ω ≤ α * aRTSTarget A Y θ₀ T i ω k := by
    intro i
    have hpull : P[X i | 𝔽.shiftDown i]
        =ᵐ[P] (S i).indicator (P[armIndicator A k i | 𝔽.shiftDown i]) :=
      condExp_indicator (hintarm i) (hSm i)
    filter_upwards [hpull, hthrottle] with ω hp hthr
    rw [hp, Set.indicator_apply]
    split_ifs with hc
    · exact hthr i hc
    · exact mul_nonneg hα (by simp only [aRTSTarget]; exact hTnn _ _)
  have hpp : ∀ᵐ ω ∂P, ∀ n, predictablePart (count X) 𝔽.shiftDown P n ω
      ≤ ∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k := by
    filter_upwards [ae_all_iff.mpr hcondle] with ω hω n
    have hterm : ∀ i, (P[count X (i + 1) - count X i | 𝔽.shiftDown i]) ω
        ≤ α * aRTSTarget A Y θ₀ T i ω k := by
      intro i
      have heq : count X (i + 1) - count X i = X i := by
        funext ω'; simp only [Pi.sub_apply, count_succ, Pi.add_apply]; ring
      rw [heq]; exact hω i
    calc predictablePart (count X) 𝔽.shiftDown P n ω
        = ∑ i ∈ Finset.range n, (P[count X (i + 1) - count X i | 𝔽.shiftDown i]) ω := by
          rw [predictablePart, Finset.sum_apply]
      _ ≤ ∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k :=
          Finset.sum_le_sum fun i _ ↦ hterm i
  -- (c) Combine and squeeze.
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < hsched n := hsched_atTop.eventually_gt_atTop 0
  filter_upwards [hLIL, hpp, hsum] with ω hlilω hppω hsumω
  obtain ⟨C, hC⟩ := hlilω
  have hmaj : Tendsto (fun n : ℕ ↦ C * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / hsched n
      + (∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k) / hsched n) atTop (𝓝 0) := by
    have := (hsqrt C).add hsumω
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hpos] with n hn
    exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hX0 i ω) hn.le
  · filter_upwards [hC, hpos] with n hCn hn
    have hdecomp : count (fun i ↦ X i ω) n
        = assignMart X 𝔽 P n ω + predictablePart (count X) 𝔽.shiftDown P n ω := by
      have hm : assignMart X 𝔽 P n = count X n - predictablePart (count X) 𝔽.shiftDown P n := rfl
      have happ : assignMart X 𝔽 P n ω
          = count (fun i ↦ X i ω) n - predictablePart (count X) 𝔽.shiftDown P n ω := by
        rw [hm]; simp [count, Finset.sum_apply]
      linarith [happ]
    rw [hdecomp, ← add_div]
    gcongr
    · exact (le_abs_self _).trans hCn
    · exact hppω n


/-- **The sparse componentwise CLT for `aRTSFE`** (blueprint `cor:sparse_clt`), with the regularity
input discharged by forced exploration. With `D_n = diag(√N_{n,1},…,√N_{n,K})`,
`D_n(θ̂_n - θ) ⇒ 𝒩(0, diag(V_1,…,V_K))`.

Arms are split by the predicate `FEfed`:
* `FEfed a` — arm `a` is eventually fed *only* by forced exploration (hypothesis `hFE`). Its count
  is then regular against the deterministic schedule, `N_{n,a}/h(n) → 1`
  (`pullCount_div_sched_tendsto_one`). This is the sparse case: no positive proportion is needed.
* `¬ FEfed a` — arm `a` has a positive limiting proportion `v_a > 0` with `N_{n,a}/n → v_a`
  (hypotheses `hpos`, `hprop`), so its count is regular against `v_a · n`.

Both arms are then covered by the *same* per-arm normalizer
`c_{a,n} = if FEfed a then h(n) else v_a · n`, which is exactly what
`estimatorError_joint_tendsto_multivariateGaussian` consumes (at `v ≡ 1`).

The split is unavoidable: not every arm can be FE-fed, since `∑_a N_{n,a} = n` while
`card 𝓐 · h(n) = o(n)`. -/
theorem aRTSFE_sparse_clt [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hshift : Tendsto
      (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n) atTop (𝓝 1))
    (FEfed : 𝓐 → Prop) {v : 𝓐 → ℝ} (hpos : ∀ a, ¬ FEfed a → 0 < v a)
    (hfe : ∀ᵐ ω ∂P, ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    (hFE : ∀ᵐ ω ∂P, ∀ a, FEfed a → ∃ (n₀ : ℕ) (E : ℕ → ℝ), Monotone E ∧
      (∀ m, n₀ ≤ m → A m ω = a → (¬ ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
        E m + 1 ≤ E (m + 1)) ∧
      Tendsto (fun n ↦ E n / hsched n) atTop (𝓝 0))
    (hprop : ∀ᵐ ω ∂P, ∀ a, ¬ FEfed a →
      Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v a))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (WithLp.toLp 2 (fun k ↦
          Real.sqrt (count (fun j ↦ armIndicator A k j ω) n)
            * (estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]))
              : EuclideanSpace ℝ 𝓐)),
        Measure.isProbabilityMeasure_map (measurable_estimatorErrorVec h θ₀ n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a]), inferInstance⟩) := by
  classical
  -- `max 0 (h n)` rather than `h n`: the schedule may start negative (e.g. `n^{1/3} - K/2`),
  -- and the CLT wants a nonnegative normalizer. The two agree eventually, since `h n → ∞`.
  set c : 𝓐 → ℕ → ℝ := fun a n ↦ if FEfed a then max 0 (hsched n) else v a * n with hc_def
  have hc : ∀ a n, 0 ≤ c a n := by
    intro a n
    simp only [hc_def]
    split_ifs with hfed
    · exact le_max_left _ _
    · exact mul_nonneg (hpos a hfed).le (Nat.cast_nonneg n)
  have hc_atTop : ∀ a, Tendsto (c a) atTop atTop := by
    intro a
    simp only [hc_def]
    split_ifs with hfed
    · exact tendsto_atTop_mono (fun n ↦ le_max_right _ _) hh.tendsto_atTop
    · exact Tendsto.const_mul_atTop (hpos a hfed) tendsto_natCast_atTop_atTop
  -- The per-arm regularity `N_{n,a}/c_{a,n} → 1`, in the `count` form the CLT consumes.
  have hNconv : ∀ᵐ ω ∂P, ∀ a,
      Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / c a n) atTop (𝓝 1) := by
    filter_upwards [hfe, hFE, hprop] with ω hfeω hFEω hpropω a
    have hbridge : ∀ n, count (fun j ↦ armIndicator A a j ω) n = (pullCount A a n ω : ℝ) :=
      fun n ↦ count_indicator_eq_pullCount a n ω
    simp only [hbridge, hc_def]
    split_ifs with hfed
    · obtain ⟨n₀, E, hEmono, hEstep, hEsmall⟩ := hFEω a hfed
      refine (pullCount_div_sched_tendsto_one ω hh hfeω hshift (n₀ := n₀) E hEmono hEstep
        hEsmall).congr' ?_
      filter_upwards [hh.tendsto_atTop.eventually_gt_atTop 0] with n hn
      rw [max_eq_right hn.le]
    · -- `N/(v_a n) = (N/n)/v_a → v_a/v_a = 1`
      have hva := hpos a hfed
      have hdiv := (hpropω a hfed).div_const (v a)
      rw [div_self hva.ne'] at hdiv
      refine hdiv.congr fun n ↦ ?_
      rw [div_div, mul_comm]
  exact estimatorError_joint_tendsto_multivariateGaussian h hY2 θ₀ hνk hc hc_atTop
    (v := fun _ ↦ 1) (fun _ ↦ one_pos) hNconv

/-- **The `N`-scaled loglog estimator rate** (the analytic core of `thm:sparse_rate`). If arm `k`'s
pull count diverges a.s. (which forced exploration guarantees), then under Condition **A** the
estimator error is `O(√(log log N_{n,k} / N_{n,k}))` a.s. — normalized by the arm's *own* sample
count `N_{n,k}`, so meaningful even for sparse arms. Unlike the `√n`-scaled rate `aRTS_rho_rate`,
this uses *only* `N_{n,k} → ∞` (no positive proportion). Via the exact Bahadur identity
`estimator_sub_eq` (`θ̂_{n,k} - θ_k = (Q_{n,k} + (θ_0-θ))/(N_{n,k}+1)`) and the subsampled loglog
LIL `abs_respMart_le_sqrt_nat_mul_loglog` (`|Q_{n,k}| ≤ 2√(2 V_k N_{n,k} log log N_{n,k})`), the two
terms are `O(√(N log log N)/N)` and `O(1/N)`, both `O(√(log log N/N))` (once `log log N ≥ 1`). -/
lemma abs_estimator_sub_le_rate_loglog_N [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (θ₀ : ℝ) (hint_id : Integrable (fun x : ℝ ↦ x) (ν k))
    (hint_sq : Integrable (fun x : ℝ ↦ x ^ 2) (ν k))
    (hNinf : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop) :
    ∀ᵐ ω ∂P, ∃ C', ∀ᶠ n in atTop,
      |estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) θ₀ n - (ν k)[id]|
        ≤ C' * √(Real.log (Real.log (pullCount A k n ω : ℝ)) / (pullCount A k n ω : ℝ)) := by
  have hk_inf : ∀ᵐ ω ∂P, (setOf (fun j ↦ A j ω = k)).Infinite := by
    filter_upwards [hNinf] with ω hNω; exact infinite_setOf_eq_of_pullCount_atTop hNω
  filter_upwards [hNinf, abs_respMart_le_sqrt_nat_mul_loglog h k hk_inf hint_id hint_sq]
    with ω hNω hQω
  have hV : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  refine ⟨2 * √(2 * Var[id; ν k]) + |θ₀ - (ν k)[id]|, ?_⟩
  have hlogloginf : Tendsto (fun n ↦ Real.log (Real.log (pullCount A k n ω : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNω)
  filter_upwards [hQω 2 (by norm_num), hNω.eventually_ge_atTop 1, hlogloginf.eventually_ge_atTop 1]
    with n hQn hN1 hL1
  set N : ℝ := (pullCount A k n ω : ℝ) with hNdef
  set L : ℝ := Real.log (Real.log N) with hLdef
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1' : (1 : ℝ) ≤ L := hL1
  have hsN : (0 : ℝ) < √N := Real.sqrt_pos.mpr hNpos
  -- Bahadur identity `θ̂ - θ = (Q + (θ₀-θ))/(N+1)`.
  have hcount : count (fun j ↦ armIndicator A k j ω) n = N := count_indicator_eq_pullCount k n ω
  have hne : count (fun j ↦ armIndicator A k j ω) n + 1 ≠ 0 := by rw [hcount]; positivity
  rw [estimator_sub_eq (X := fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) ((ν k)[id]) θ₀ n hne,
    respMG_indicator_eq_respMart, hcount]
  have hden : (0 : ℝ) < N + 1 := by linarith
  -- `√(L/N) = √L/√N`, and `√(2 V N L) = √(2V)·√N·√L`.
  have hsLN : √(L / N) = √L / √N := Real.sqrt_div (by linarith) N
  have hsL1 : (1 : ℝ) ≤ √L := Real.one_le_sqrt.mpr (by linarith)
  have hprod : √(2 * Var[id; ν k] * N * L) = √(2 * Var[id; ν k]) * √N * √L := by
    rw [show 2 * Var[id; ν k] * N * L = 2 * Var[id; ν k] * (N * L) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul hNpos.le, mul_assoc]
  set a : ℝ := |θ₀ - (ν k)[id]| with hadef
  have hann : (0 : ℝ) ≤ a := abs_nonneg _
  have hVs : (0 : ℝ) ≤ √(2 * Var[id; ν k]) := Real.sqrt_nonneg _
  have hNN : √N * √N = N := Real.mul_self_sqrt hNpos.le
  have hsN_le : √N ≤ N + 1 := by nlinarith [hNN, hsN.le]
  have hc : (0 : ℝ) ≤ 2 * √(2 * Var[id; ν k]) * √L := by positivity
  -- Bound `|Q + (θ₀-θ)| ≤ |Q| + |θ₀-θ| ≤ 2√(2VNL) + a`.
  have hqbound : |respMart ν A Y k n ω| ≤ 2 * (√(2 * Var[id; ν k]) * √N * √L) := by
    refine hQn.trans (le_of_eq ?_)
    rw [hprod]
  have habs : |respMart ν A Y k n ω + (θ₀ - (ν k)[id])|
      ≤ 2 * (√(2 * Var[id; ν k]) * √N * √L) + a :=
    (abs_add_le _ _).trans (by linarith [hqbound])
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine habs.trans ?_
  rw [hsLN]
  -- Multiply through by `√N > 0` and use `√N·√N = N`.
  rw [show (2 * √(2 * Var[id; ν k]) + a) * (√L / √N) * (N + 1)
        = ((2 * √(2 * Var[id; ν k]) + a) * √L * (N + 1)) / √N by field_simp,
    le_div_iff₀ hsN,
    show (2 * (√(2 * Var[id; ν k]) * √N * √L) + a) * √N
        = 2 * √(2 * Var[id; ν k]) * √L * (√N * √N) + a * √N by ring, hNN]
  -- `2√(2V)√L·N + a√N ≤ (2√(2V)+a)√L(N+1)`, term by term.
  have h1 : 2 * √(2 * Var[id; ν k]) * √L * N ≤ 2 * √(2 * Var[id; ν k]) * √L * (N + 1) := by
    nlinarith [hc]
  have hprodge : √N ≤ √L * (N + 1) := by
    nlinarith [hsL1, hsN_le, mul_nonneg (sub_nonneg.mpr hsL1) hden.le]
  have h2 : a * √N ≤ a * √L * (N + 1) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hprodge hann
  nlinarith [h1, h2]

/-- **Consistency and rate for sparse targets** (blueprint `thm:sparse_rate`). Under Condition **A**
only (no non-sparsity), any forced-exploration design satisfies, for every arm `k`, almost surely:
`N_{n,k} → ∞`; `N_{n,k}/n → v_k = T(θ)_k` (allowing `v_k = 0`); and
`|θ̂_{n,k} - θ_k| = O(√(log log N_{n,k} / N_{n,k}))` (the estimator LIL scaled by the arm's *own*
sample count). All three follow from `aRTSFE_no_starvation` (`N → ∞`, the sparse enabler): it forces
every arm sampled infinitely often, hence `θ̂ → θ` (`estimator_ae_tendsto_of_pullCount_atTop`, no
positivity needed), whence `ρ̂ → T(θ)` and — through the matching `consistency_of_hitting` (which
never uses positivity) — `N/n → T(θ)`; the rate is `abs_estimator_sub_le_rate_loglog_N`. The design
enters through the throttle `hthrottle` (matching) and the action-level rule `hfe`
(no-starvation). -/
theorem aRTSFE_sparse_rate [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hint_id : ∀ k, Integrable (fun x : ℝ ↦ x) (ν k))
    (hint_sq : ∀ k, Integrable (fun x : ℝ ↦ x ^ 2) (ν k))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hthrottle : ∀ k, ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hfe : ∀ᵐ ω ∂P, ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω) (k : 𝓐) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ pullCount A k n ω) atTop atTop ∧
      Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n / (n : ℝ))
        atTop (𝓝 (T (fun k' ↦ (ν k')[id]) k)) ∧
      ∃ C', ∀ᶠ n in atTop,
        |estimator (fun j ↦ armIndicator A k j ω) (fun j ↦ Y j ω) (θ₀ k) n - (ν k)[id]|
          ≤ C' * √(Real.log (Real.log (pullCount A k n ω : ℝ)) / (pullCount A k n ω : ℝ)) := by
  -- No starvation for every arm (`N_{n,k'} → ∞`), in real form.
  have hNinf : ∀ᵐ ω ∂P, ∀ k', Tendsto (fun n ↦ (pullCount A k' n ω : ℝ)) atTop atTop :=
    ae_all_iff.mpr fun k' ↦ (aRTSFE_no_starvation hh.tendsto_atTop hfe k').mono
      fun ω hω ↦ tendsto_natCast_atTop_atTop.comp hω
  -- Estimator vector consistency `θ̂ → θ` from infinite pulls (no positivity).
  have hθconv : ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ armIndicator A k' j ω)
      (fun j ↦ Y j ω) (θ₀ k') n) atTop (𝓝 (fun k' ↦ (ν k')[id])) := by
    have hper : ∀ k', ∀ᵐ ω ∂P, Tendsto (fun n ↦ estimator (fun j ↦ armIndicator A k' j ω)
        (fun j ↦ Y j ω) (θ₀ k') n) atTop (𝓝 ((ν k')[id])) := by
      intro k'
      filter_upwards [estimator_ae_tendsto_of_pullCount_atTop h k' hY2 (θ₀ k'), hNinf]
        with ω hest hNall
      exact hest (hNall k')
    filter_upwards [ae_all_iff.mpr hper] with ω hω
    exact tendsto_pi_nhds.mpr hω
  -- Plug-in target consistency `ρ̂_{n,k} → T(θ)_k` by continuity.
  have hρconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop
      (𝓝 (T (fun k' ↦ (ν k')[id]) k)) := by
    filter_upwards [hθconv] with ω hω
    exact tendsto_pi_nhds.mp ((hT.tendsto _).comp hω) k
  -- `N/n → T(θ)_k`: the common matching limit `u_k` equals `T(θ)_k` (uniqueness with `ρ̂ → T(θ)`).
  have hprop : ∀ᵐ ω ∂P, Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n / (n : ℝ))
      atTop (𝓝 (T (fun k' ↦ (ν k')[id]) k)) := by
    filter_upwards [consistency_of_hitting h hY2 θ₀ T hT hTnn hTsum α hα
      (aRTSFEUnder A Y θ₀ T hsched) hthrottle (aRTSFE_smallness_all θ₀ T hTnn hh), hρconv]
      with ω hmatch hρω
    obtain ⟨u, hu⟩ := hmatch
    rw [← tendsto_nhds_unique (hu k).2 hρω]
    exact (hu k).1
  filter_upwards [aRTSFE_no_starvation hh.tendsto_atTop hfe k, hprop,
    abs_estimator_sub_le_rate_loglog_N h k (θ₀ k) (hint_id k) (hint_sq k)
      (hNinf.mono fun ω hω ↦ hω k)] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-! ### A concrete admissible schedule

`h(n) = n^{2/3}` satisfies every hypothesis the sparse theory imposes, and is **excluded** by the
paper's condition (ii) `h(n) = o(√n)`. So the hypothesis stack is satisfiable, and it is satisfiable
exactly in the regime the paper's definition rules out. -/

/-- The concrete exploration schedule `h(n) = n^{2/3}`. -/
noncomputable def sched23 : ℕ → ℝ := fun n ↦ (n : ℝ) ^ ((2 : ℝ) / 3)

lemma sched23_nonneg (n : ℕ) : 0 ≤ sched23 n := Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- `n^{2/3}` is a legitimate exploration schedule in the weakened sense: nondecreasing, divergent,
and `o(n)`. -/
lemma isExplorationSchedule_sched23 : IsExplorationSchedule sched23 where
  mono := fun a b hab ↦
    Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) (by norm_num)
  tendsto_atTop := (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  div_tendsto_zero := by
    have hthird : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
    refine hthird.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hnR _
    rw [sched23, div_eq_div_iff hp.ne' hnR.ne', one_mul, ← Real.rpow_add hnR,
      show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.rpow_one]

/-- **`n^{2/3}` is not `o(√n)`** — it is excluded by the paper's condition (ii), and that is exactly
what puts a sparse arm in the forced-exploration-dominated regime. -/
lemma not_isSqrtSmall_sched23 : ¬ IsSqrtSmall sched23 := by
  have hgrow : Tendsto (fun n : ℕ ↦ sched23 n / Real.sqrt n) atTop atTop := by
    have hsixth : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine hsixth.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hnR _
    rw [sched23, Real.sqrt_eq_rpow, eq_div_iff hp.ne', ← Real.rpow_add hnR,
      show (1 : ℝ) / 6 + 1 / 2 = 2 / 3 by norm_num]
  intro hcon
  exact not_tendsto_nhds_of_tendsto_atTop hgrow 0 hcon

/-- The **schedule-regularity** hypothesis `hshift` of `pullCount_div_sched_tendsto_one` holds for
`n^{2/3}`: shifting the argument by the `O(h n)` catch-up window changes `h` only to second order,
since `K⌈n^{2/3}⌉ + 1 = o(n)`. -/
lemma sched23_shift (K : ℕ) :
    Tendsto (fun n ↦ sched23 (n - (K * ⌈sched23 n⌉₊ + 1)) / sched23 n) atTop (𝓝 1) := by
  -- the shifted index is `n(1 - o(1))`
  have hshrink : Tendsto (fun n : ℕ ↦ ((n - (K * ⌈sched23 n⌉₊ + 1) : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ ↦ ((K : ℝ) * (sched23 n + 1) + 1) / (n : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ sched23 n / (n : ℝ)) atTop (𝓝 0) :=
        isExplorationSchedule_sched23.div_tendsto_zero
      have h2 : Tendsto (fun n : ℕ ↦ ((K : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have := (h1.const_mul (K : ℝ)).add h2
      simp only [mul_zero, add_zero] at this
      refine this.congr fun n ↦ ?_
      field_simp
      ring
    have hsq : Tendsto (fun n : ℕ ↦ 1 - ((K : ℝ) * (sched23 n + 1) + 1) / (n : ℝ))
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hz
    rw [sub_zero] at hsq
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsq tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have hceil : ((⌈sched23 n⌉₊ : ℝ)) ≤ sched23 n + 1 :=
        (Nat.ceil_lt_add_one (sched23_nonneg n)).le
      have hnum : (n : ℝ) - ((K : ℝ) * (sched23 n + 1) + 1)
          ≤ ((n - (K * ⌈sched23 n⌉₊ + 1) : ℕ) : ℝ) := by
        by_cases hle : K * ⌈sched23 n⌉₊ + 1 ≤ n
        · rw [Nat.cast_sub hle]; push_cast; nlinarith
        · have h0 : n - (K * ⌈sched23 n⌉₊ + 1) = 0 := by omega
          have hcast : (n : ℝ) ≤ (K : ℝ) * (⌈sched23 n⌉₊ : ℝ) + 1 := by
            have : n ≤ K * ⌈sched23 n⌉₊ + 1 := by omega
            exact_mod_cast this
          rw [h0, Nat.cast_zero]
          nlinarith
      calc 1 - ((K : ℝ) * (sched23 n + 1) + 1) / (n : ℝ)
          = ((n : ℝ) - ((K : ℝ) * (sched23 n + 1) + 1)) / (n : ℝ) := by field_simp
        _ ≤ ((n - (K * ⌈sched23 n⌉₊ + 1) : ℕ) : ℝ) / (n : ℝ) := by gcongr
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_one hnR]
      exact_mod_cast Nat.sub_le _ _
  -- `x ↦ x^{2/3}` is continuous at `1`, with value `1`
  have hcont : Tendsto (fun x : ℝ ↦ x ^ ((2 : ℝ) / 3)) (𝓝 1) (𝓝 1) := by
    have := (Real.continuousAt_rpow_const (1 : ℝ) ((2 : ℝ) / 3) (Or.inl one_ne_zero)).tendsto
    simpa using this
  refine (hcont.comp hshrink).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply, sched23]
  rw [← Real.div_rpow (Nat.cast_nonneg _) hnR.le]

/-- `log log n = o(n^p)` for every `p > 0`: iterating the logarithm only helps, so this follows from
`log n = o(n^p)` by `log log n ≤ log n`. It is the single growth fact behind both `sched23_sqrt` and
`sched23_star`. -/
lemma tendsto_loglog_div_rpow {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log n) / (n : ℝ) ^ p) atTop (𝓝 0) := by
  have hlogtop : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := hlogtop.eventually_ge_atTop 1
  have hcomp : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ p) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hcomp
  · filter_upwards [hev] with n hn
    have h1 : (0 : ℝ) ≤ Real.log (Real.log n) := Real.log_nonneg hn
    positivity
  · filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hppos : (0 : ℝ) < (n : ℝ) ^ p := Real.rpow_pos_of_pos hnR _
    gcongr
    exact Real.log_le_self (by linarith)

/-- The `(⋆)` comparison `√(n log log n) = o(h n)` holds for `n^{2/3}` — the `hsqrt` hypothesis of
`throttled_count_div_sched_tendsto_zero`. It reduces to `log log n = o(n^{1/3})`, since
`√(n log log n)/n^{2/3} = √(log log n / n^{1/3})`. -/
lemma sched23_sqrt (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / sched23 n)
      atTop (𝓝 0) := by
  have hlogtop : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := hlogtop.eventually_ge_atTop 1
  have hLL : Tendsto (fun n : ℕ ↦ Real.log (Real.log n) / (n : ℝ) ^ ((1 : ℝ) / 3))
      atTop (𝓝 0) := tendsto_loglog_div_rpow (by norm_num)
  have hsq : Tendsto (fun n : ℕ ↦
      Real.sqrt (Real.log (Real.log n) / (n : ℝ) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hLL
    simpa [Function.comp_def] using this
  have hmain : Tendsto (fun n : ℕ ↦ Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / sched23 n)
      atTop (𝓝 0) := by
    refine hsq.congr' ?_
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hL0 : (0 : ℝ) ≤ Real.log (Real.log n) := Real.log_nonneg hn
    have hnL : (0 : ℝ) ≤ (n : ℝ) * Real.log (Real.log n) := by positivity
    have h43 : (n : ℝ) ^ ((4 : ℝ) / 3) = (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add hnR, Real.rpow_one]
    have hs43 : Real.sqrt ((n : ℝ) ^ ((4 : ℝ) / 3)) = (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnR.le]; norm_num
    simp only [sched23]
    rw [← hs43, ← Real.sqrt_div hnL]
    congr 1
    rw [h43, mul_div_mul_left _ _ hnR.ne']
  have hC := hmain.const_mul C
  rw [mul_zero] at hC
  exact hC.congr fun n ↦ (mul_div_assoc C _ _).symm

/-- **The schedule `n^{2/3}` satisfies `(⋆)`** in the form consumed by `exists_decay_of_contDiffAt`,
with `L ≍ h`: `n log log n / h(n)² = log log n / n^{1/3} → 0` since `h(n)² = n^{4/3}`.

Read together with `not_isSqrtSmall_sched23`, this is what makes the fix non-vacuous: `(⋆)` is
satisfiable *precisely* in the regime `h(n) ≫ √n` that the paper's condition (ii) excludes. -/
lemma sched23_star :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / (sched23 n * sched23 n))
      atTop (𝓝 0) := by
  refine (tendsto_loglog_div_rpow (p := (1 : ℝ) / 3) (by norm_num)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have h43 : sched23 n * sched23 n = (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 3) := by
    simp only [sched23]
    rw [← Real.rpow_add hnR, show (2 : ℝ) / 3 + 2 / 3 = 1 + 1 / 3 by norm_num,
      Real.rpow_add hnR, Real.rpow_one]
  rw [h43, mul_div_mul_left _ _ hnR.ne']

/-- **The schedule hypotheses of `aRTSFE_sparse_clt_of_contDiffAt` are jointly satisfiable** — and
satisfiable only outside the paper's `def:exploration_schedule` (ii). `h(n) = n^{2/3}` supplies all
three (`hh`, `hshift`, `hstar`) while failing `IsSqrtSmall`, so the capstone is not vacuous. -/
lemma sched23_satisfies_schedule_hypotheses :
    IsExplorationSchedule sched23 ∧
    (∀ K : ℕ, Tendsto (fun n ↦ sched23 (n - (K * ⌈sched23 n⌉₊ + 1)) / sched23 n) atTop (𝓝 1)) ∧
    Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (sched23 m * sched23 m))
      atTop (𝓝 0) ∧
    ¬ IsSqrtSmall sched23 :=
  ⟨isExplorationSchedule_sched23, sched23_shift, sched23_star, not_isSqrtSmall_sched23⟩

/-- **`√(n log log n) = o(h(n))` is exactly what `(⋆)` says**, in the scaled form the martingale
part of `throttled_count_div_sched_tendsto_zero` consumes: `√(n log log n)/h(n)` is the square root
of `n log log n / h(n)²`. -/
lemma tendsto_const_mul_sqrt_loglog_div_sched {hsched : ℕ → ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 0 < hsched n)
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (hsched m * hsched m))
      atTop (𝓝 0)) (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / hsched n)
      atTop (𝓝 0) := by
  have hlog1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hbase : Tendsto (fun n : ℕ ↦ Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / hsched n)
      atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ ↦
        Real.sqrt ((n : ℝ) * Real.log (Real.log n) / (hsched n * hsched n))) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hstar
    refine hs.congr' ?_
    filter_upwards [hspos, hlog1, eventually_gt_atTop 0] with n hn hll hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnum : (0 : ℝ) ≤ (n : ℝ) * Real.log (Real.log n) :=
      mul_nonneg hnR.le (Real.log_nonneg hll)
    rw [Real.sqrt_div hnum, Real.sqrt_mul_self hn.le]
  have hC := hbase.const_mul C
  rw [mul_zero] at hC
  exact hC.congr fun n ↦ (mul_div_assoc C _ _).symm

/-- **A nonnegative sequence decaying at the loglog rate has partial sums `o(h(n))`** — under `(⋆)`
and nothing else. This is the `hsum` input of `throttled_count_div_sched_tendsto_zero`, *derived*
rather than assumed.

The point is that `(⋆)` already pins the schedule tightly enough to sum the decay. Writing `(⋆)` as
`i log log i < h(i)²`, i.e. `h(i) > √(i log log i)`, the majorant telescopes into a square root:

`log log i / h(i) ≤ log log i / √(i log log i) = √(log log i) / √i`,

so `∑_{i<n} f i ≲ √(log log n) · ∑_{i<n} 1/√i ≤ 2√(n log log n)` by `sum_one_div_sqrt_le` — and
`√(n log log n) = o(h(n))` is `(⋆)` once more. The finitely many initial terms, where the decay has
not yet started, contribute a constant, which `h(n) → ∞` kills. -/
lemma tendsto_sum_div_sched_of_loglog_decay {f : ℕ → ℝ} {hsched : ℕ → ℝ} {c : ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hsched_atTop : Tendsto hsched atTop atTop)
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (hsched m * hsched m))
      atTop (𝓝 0))
    (hdecay : ∀ᶠ i in atTop, f i ≤ c * (Real.log (Real.log i) / hsched i)) :
    Tendsto (fun n ↦ (∑ i ∈ Finset.range n, f i) / hsched n) atTop (𝓝 0) := by
  have hspos : ∀ᶠ n : ℕ in atTop, 0 < hsched n := hsched_atTop.eventually_gt_atTop 0
  have hloglog1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ Real.log (Real.log i) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  have hstar1 : ∀ᶠ i : ℕ in atTop, (i : ℝ) * Real.log (Real.log i) < hsched i * hsched i := by
    filter_upwards [hstar.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)), hspos]
      with i hi hs
    rwa [div_lt_one (by positivity)] at hi
  have hlog1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ Real.log i :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp
    (hdecay.and (hloglog1.and (hlog1.and (hstar1.and (hspos.and (eventually_gt_atTop 0))))))
  -- Pointwise: the loglog majorant is at most `|c|·√(log log i)/√i`.
  have hpt : ∀ i, i₀ ≤ i →
      f i ≤ (|c| * Real.sqrt (Real.log (Real.log i))) * (1 / Real.sqrt i) := by
    intro i hi
    obtain ⟨hdec, hll, -, hst, hs, hi0⟩ := hi₀ i hi
    have hiR : (0 : ℝ) < i := by exact_mod_cast hi0
    have hll0 : (0 : ℝ) < Real.log (Real.log i) := lt_of_lt_of_le one_pos hll
    have hspos' : (0 : ℝ) < Real.sqrt ((i : ℝ) * Real.log (Real.log i)) :=
      Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt ((i : ℝ) * Real.log (Real.log i)) < hsched i := by
      have hlt := Real.sqrt_lt_sqrt (by positivity) hst
      rwa [Real.sqrt_mul_self hs.le] at hlt
    have heq : Real.log (Real.log i) / Real.sqrt ((i : ℝ) * Real.log (Real.log i))
        = Real.sqrt (Real.log (Real.log i)) * (1 / Real.sqrt i) := by
      rw [Real.sqrt_mul hiR.le,
        mul_comm (Real.sqrt (i : ℝ)) (Real.sqrt (Real.log (Real.log i))),
        ← div_div, Real.div_sqrt, mul_one_div]
    have hkey : Real.log (Real.log i) / hsched i
        ≤ Real.sqrt (Real.log (Real.log i)) * (1 / Real.sqrt i) := by
      rw [← heq]
      gcongr
    calc f i ≤ c * (Real.log (Real.log i) / hsched i) := hdec
      _ ≤ |c| * (Real.log (Real.log i) / hsched i) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (div_nonneg hll0.le hs.le)
      _ ≤ |c| * (Real.sqrt (Real.log (Real.log i)) * (1 / Real.sqrt i)) :=
          mul_le_mul_of_nonneg_left hkey (abs_nonneg c)
      _ = (|c| * Real.sqrt (Real.log (Real.log i))) * (1 / Real.sqrt i) := by ring
  -- Sum the majorant.
  have hbound : ∀ n, i₀ ≤ n → ∑ i ∈ Finset.range n, f i
      ≤ (∑ i ∈ Finset.range i₀, f i)
        + |c| * 2 * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) := by
    intro n hn
    have hsplit : ∑ i ∈ Finset.range n, f i
        = (∑ i ∈ Finset.range i₀, f i) + ∑ i ∈ Finset.Ico i₀ n, f i := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive f (Nat.zero_le i₀) hn]
    rw [hsplit]
    gcongr
    have htail : ∑ i ∈ Finset.Ico i₀ n, f i
        ≤ ∑ i ∈ Finset.range n, (|c| * Real.sqrt (Real.log (Real.log n))) * (1 / Real.sqrt i) := by
      refine (Finset.sum_le_sum (fun i hi ↦ ?_)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2)
          (fun i _ _ ↦ by positivity))
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
      obtain ⟨-, -, hlogi, -, -, hi0⟩ := hi₀ i hi1
      have hiR : (0 : ℝ) < i := by exact_mod_cast hi0
      refine (hpt i hi1).trans ?_
      gcongr
    refine htail.trans ?_
    rw [← Finset.mul_sum]
    calc (|c| * Real.sqrt (Real.log (Real.log n))) * ∑ i ∈ Finset.range n, 1 / Real.sqrt i
        ≤ (|c| * Real.sqrt (Real.log (Real.log n))) * (2 * Real.sqrt n) := by
          gcongr
          exact sum_one_div_sqrt_le n
      _ = |c| * 2 * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n)]; ring
  -- Squeeze.
  refine squeeze_zero' ?_ ?_ (?_ : Tendsto (fun n ↦ (∑ i ∈ Finset.range i₀, f i) / hsched n
    + |c| * 2 * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / hsched n) atTop (𝓝 0))
  · filter_upwards [hspos] with n hn
    exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hf0 i) hn.le
  · filter_upwards [eventually_ge_atTop i₀, hspos] with n hn hs
    rw [← add_div]
    gcongr
    exact hbound n hn
  · have h1 : Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range i₀, f i) / hsched n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsched_atTop
    have h2 := tendsto_const_mul_sqrt_loglog_div_sched hspos hstar (|c| * 2)
    simpa using h1.add h2

/-- **Discharging the `FEfed` hypothesis of `aRTSFE_sparse_clt`** — the final assembly of Steps 3–4.

For an arm `k` whose plug-in target has decayed past the schedule (`hdecay`: pathwise, eventually
`ρ̂_{m,k} ≤ g m < h(m)/m`, which is what `aRTSTarget_le_loglog_of_quadratic` supplies under `(⋆)`),
the counter `E n = ∑_{i<n} 𝟙{throttled pull of k at i}` has all three properties that
`pullCount_div_sched_tendsto_one` asks for:

* it is monotone;
* it increases by one at every non-forced-exploration pull of `k` — because at such a round `k` is
  not under-explored, so Step 3 (`not_aRTSFEUnder_of_sched_lt`) makes the pull a *throttled* one;
* it is `o(h)`, by Step 4 (`throttled_count_div_sched_tendsto_zero`).

Note `n₀` and `g` are allowed to depend on `ω`, which is essential: the decay constant comes
from the law of the iterated logarithm and is genuinely random. -/
lemma fEfed_of_decay [Finite 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) {hsched : ℕ → ℝ} {θ₀ : 𝓐 → ℝ}
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (hTnn : ∀ z k, 0 ≤ T z k) {k : 𝓐} {α : ℝ}
    (hα : 0 ≤ α)
    (hthrottle : ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k (IsAlgEnvSeq.filtration h.measurable_action h.measurable_feedback) P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k)
    (hsched_atTop : Tendsto hsched atTop atTop)
    (hsum : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k) / hsched n) atTop (𝓝 0))
    (hsqrt : ∀ C : ℝ,
      Tendsto (fun n : ℕ ↦ C * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / hsched n)
        atTop (𝓝 0))
    (hdecay : ∀ᵐ ω ∂P, ∃ g : ℕ → ℝ,
      (∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k ≤ g m) ∧
      (∀ᶠ m in atTop, g m < hsched m / (m : ℝ))) :
    ∀ᵐ ω ∂P, ∃ (n₀ : ℕ) (E : ℕ → ℝ), Monotone E ∧
      (∀ m, n₀ ≤ m → A m ω = k → (¬ ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
        E m + 1 ≤ E (m + 1)) ∧
      Tendsto (fun n ↦ E n / hsched n) atTop (𝓝 0) := by
  have hX0 : ∀ i ω, 0 ≤ throttledIndicator A Y θ₀ T hsched k i ω := fun i ω ↦
    Set.indicator_nonneg (fun _ _ ↦ armIndicator_nonneg A k i _) ω
  filter_upwards [hdecay,
    throttled_count_div_sched_tendsto_zero h hT hTnn hα hthrottle hsched_atTop hsum hsqrt]
    with ω hdecayω hlimω
  obtain ⟨g, hg1, hg2⟩ := hdecayω
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hg1.and (hg2.and (eventually_gt_atTop 0)))
  refine ⟨n₀, fun n ↦ count (fun i ↦ throttledIndicator A Y θ₀ T hsched k i ω) n, ?_, ?_, hlimω⟩
  · intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx ↦ ?_) (fun i _ _ ↦ hX0 i ω)
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hab)
  · intro m hm hAm hnotU
    obtain ⟨hdec, hgh, hmpos⟩ := hn₀ m hm
    -- arm `k` is not under-explored at `m`, so Step 3 makes this a *throttled* pull
    have hlt : hsched m < (pullCount A k m ω : ℝ) := by
      by_contra hcon
      exact hnotU ⟨k, not_lt.mp hcon⟩
    have hnot := not_aRTSFEUnder_of_sched_lt ω hmpos hlt hdec hgh
    have hval : throttledIndicator A Y θ₀ T hsched k m ω = 1 := by
      rw [throttledIndicator, Set.indicator_of_mem hnot, armIndicator]
      exact Set.indicator_of_mem (show ω ∈ {ω | A m ω = k} from hAm) _
    change count (fun i ↦ throttledIndicator A Y θ₀ T hsched k i ω) m + 1
      ≤ count (fun i ↦ throttledIndicator A Y θ₀ T hsched k i ω) (m + 1)
    rw [count_succ, hval]

/-- **The sparse componentwise CLT for `aRTSFE`, with the `FEfed` hypothesis discharged.** This is
the capstone of `maths/sparse-clt-fix.md`: `aRTSFE_sparse_clt` assumes that each sparse arm is
eventually fed only by forced exploration; here that assumption is *proved*, from

* `hstar` — the reversed schedule condition `(⋆) : m log log m = o(h(m)²)`, which replaces the
  paper's `h(m) = o(√m)` and is satisfiable exactly where the paper's condition fails
  (`sched23_star`, `not_isSqrtSmall_sched23`);
* `hT2` — the target is `C²` at `Θ` on the sparse arms.
. -/
theorem aRTSFE_sparse_clt_of_contDiffAt [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐]
    [Nonempty 𝓐]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp (fun x : ℝ ↦ x) 2 (ν a))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hshift : Tendsto
      (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n) atTop (𝓝 1))
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * log (log m) / (hsched m * hsched m)) atTop (𝓝 0))
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (hTnn : ∀ z a, 0 ≤ T z a)
    (hTsum : ∀ z, ∑ a, T z a = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTSFE : IsARTSFE alg θ₀ T hsched α)
    (hT2 : ∀ a, T (fun j ↦ (ν j)[id]) a = 0 → ContDiffAt ℝ 2 (T · a) (fun j ↦ (ν j)[id])) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ 𝓐))
      (fun n : ℕ ↦ (⟨P.map (fun ω ↦ (WithLp.toLp 2 (fun k ↦
          √(count (armIndicator A k · ω) n)
            * (estimator (armIndicator A k · ω) (Y · ω) (θ₀ k) n - (ν k)[id])))),
        Measure.isProbabilityMeasure_map (measurable_estimatorErrorVec h θ₀ n).aemeasurable⟩
          : ProbabilityMeasure (EuclideanSpace ℝ 𝓐)))
      atTop
      (𝓝 ⟨multivariateGaussian 0 (Matrix.diagonal (fun a ↦ Var[id; ν a])), inferInstance⟩) := by
  classical
  -- Condition **A** on the arms already puts the response in `L²`.
  have hY2 : ∀ n, MemLp (Y n) 2 P := fun n ↦ h.memLp_feedback hνk n
  have hfe := fe_of_isARTSFE h hARTSFE
  have hthrottle := fun a ↦ throttle_of_isARTSFE h hARTSFE a
  have hint_id : ∀ a, Integrable (fun x : ℝ ↦ x) (ν a) := fun a ↦ (hνk a).integrable (by norm_num)
  have hint_sq : ∀ a, Integrable (fun x : ℝ ↦ x ^ 2) (ν a) := fun a ↦ (hνk a).integrable_sq
  -- Condition **A** already gives, for *every* arm, that the count diverges, that the proportion
  -- converges to `T(Θ)_a` (no positivity needed), and the `N`-scaled loglog rate.
  have hsr : ∀ᵐ ω ∂P, ∀ a : 𝓐,
      Tendsto (fun n ↦ pullCount A a n ω) atTop atTop ∧
      Tendsto (fun n ↦ count (fun j ↦ armIndicator A a j ω) n / (n : ℝ))
        atTop (𝓝 (T (fun k' ↦ (ν k')[id]) a)) ∧
      ∃ C' : ℝ, ∀ᶠ n in atTop,
        |estimator (fun j ↦ armIndicator A a j ω) (fun j ↦ Y j ω) (θ₀ a) n - (ν a)[id]|
          ≤ C' * Real.sqrt (Real.log (Real.log (pullCount A a n ω : ℝ))
              / (pullCount A a n ω : ℝ)) :=
    ae_all_iff.mpr fun a ↦ aRTSFE_sparse_rate h hY2 θ₀ T hT hTnn hTsum α hα hint_id hint_sq
      hh hthrottle hfe a
  have hprop : ∀ᵐ ω ∂P, ∀ a : 𝓐, T (fun j ↦ (ν j)[id]) a ≠ 0 →
      Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / (n : ℝ)) atTop
        (𝓝 (T (fun j ↦ (ν j)[id]) a)) := by
    filter_upwards [hsr] with ω hω a _
    exact ((hω a).2.1).congr fun n ↦ by rw [count_indicator_eq_pullCount]
  refine aRTSFE_sparse_clt (v := fun a ↦ T (fun j ↦ (ν j)[id]) a) h hY2 θ₀ hνk hh hshift
    (fun a ↦ T (fun j ↦ (ν j)[id]) a = 0)
    (fun a ha ↦ lt_of_le_of_ne (hTnn _ a) (Ne.symm ha)) hfe ?_ hprop
  -- The deterministic floor `L(n) = h(n - W(n))` that forced exploration guarantees.
  set L : ℕ → ℝ := fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) with hLdef
  have hspos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < hsched n := hh.tendsto_atTop.eventually_gt_atTop 0
  -- `L ≍ h`: eventually `L ≥ h/2`, so `L → ∞`, and `h/L → 1`.
  have hhalf : ∀ᶠ n : ℕ in atTop, hsched n / 2 ≤ L n := by
    filter_upwards [hshift.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1)), hspos]
      with n hn hs
    rw [lt_div_iff₀ hs] at hn
    linarith
  have hLtop : Tendsto L atTop atTop :=
    tendsto_atTop_mono' atTop hhalf (hh.tendsto_atTop.atTop_div_const (by norm_num))
  have hLpos : ∀ᶠ m : ℕ in atTop, 0 < L m ∧ 0 < hsched m := by
    filter_upwards [hLtop.eventually_gt_atTop 0, hspos] with m h1 h2 using ⟨h1, h2⟩
  have hinv : Tendsto (fun n : ℕ ↦ hsched n / L n) atTop (𝓝 1) := by
    have hi := hshift.inv₀ (by norm_num)
    rw [inv_one] at hi
    exact hi.congr fun n ↦ inv_div _ _
  -- `(⋆)` transported from `h²` to `L·h`, and the resulting `log log m / L m → 0`.
  have hstarL : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (L m * hsched m))
      atTop (𝓝 0) := by
    have hmul := hstar.mul hinv
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [hLpos] with m hm
    have hL' := hm.1.ne'
    have hs' := hm.2.ne'
    field_simp
  have hL0 : Tendsto (fun m : ℕ ↦ Real.log (Real.log m) / L m) atTop (𝓝 0) := by
    have hmul := hstarL.mul hh.div_tendsto_zero
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [hLpos, eventually_gt_atTop 0] with m hm hm0
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    have hL' := hm.1.ne'
    have hs' := hm.2.ne'
    field_simp
  have hlog1 : ∀ᶠ m : ℕ in atTop, (1 : ℝ) ≤ Real.log m :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hLnn : ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log (Real.log m) / L m := by
    filter_upwards [hlog1, hLpos] with m hm hLm
    exact div_nonneg (Real.log_nonneg hm) hLm.1.le
  -- `(⋆)` also gives the martingale-part majorant `√(n log log n) = o(h(n))`.
  have hsqrt : ∀ C : ℝ, Tendsto
      (fun n : ℕ ↦ C * Real.sqrt ((n : ℝ) * Real.log (Real.log n)) / hsched n) atTop (𝓝 0) :=
    tendsto_const_mul_sqrt_loglog_div_sched hspos hstar
  -- The LIL rate re-expressed against the deterministic floor.
  have hrate_ae : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ armIndicator A j i ω) (fun i ↦ Y i ω) (θ₀ j) m - (ν j)[id]|
        ≤ C * Real.sqrt (Real.log (Real.log m) / L m) := by
    filter_upwards [hfe, hsr] with ω hfeω hsrω
    exact exists_rate_loglog_of_pullCount_ge ω hLtop
      (fun j ↦ eventually_schedShift_le_pullCount ω hh hfeω j) (fun a ↦ (hsrω a).2.2)
  -- Arm by arm: decay ⇒ `FEfed`.
  refine ae_all_iff.mpr fun a ↦ ?_
  by_cases hfed : T (fun j ↦ (ν j)[id]) a = 0
  · -- The loglog decay of `ρ̂_{·,a}`, in the explicit form that both inputs of `fEfed_of_decay`
    -- are read off from.
    have hCq_ae : ∀ᵐ ω ∂P, ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ᶠ m in atTop,
        aRTSTarget A Y θ₀ T m ω a ≤ Cq * (Real.log (Real.log m) / L m) := by
      filter_upwards [hrate_ae] with ω hω
      obtain ⟨C, hC⟩ := hω
      exact exists_aRTSTarget_le_loglog_of_contDiffAt ω (hT2 a hfed) (fun z ↦ hTnn z a) hfed
        hLnn hL0 hC
    have hdecay : ∀ᵐ ω ∂P, ∃ g : ℕ → ℝ,
        (∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω a ≤ g m) ∧
        (∀ᶠ m in atTop, g m < hsched m / (m : ℝ)) := by
      filter_upwards [hCq_ae] with ω hω
      obtain ⟨Cq, -, hCq⟩ := hω
      exact ⟨fun m ↦ Cq * (Real.log (Real.log m) / L m), hCq,
        eventually_mul_loglog_div_lt_of_star Cq hLpos hstarL⟩
    -- The compensator bound is the *same* decay, summed: `(⋆)` makes `∑ α ρ̂_{i,a} = o(h(n))`.
    have hsum : ∀ᵐ ω ∂P, Tendsto
        (fun n ↦ (∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω a) / hsched n)
        atTop (𝓝 0) := by
      filter_upwards [hCq_ae] with ω hω
      obtain ⟨Cq, hCq0, hCq⟩ := hω
      refine tendsto_sum_div_sched_of_loglog_decay (c := α * (2 * Cq))
        (fun i ↦ mul_nonneg hα.1 (hTnn _ a)) hh.tendsto_atTop hstar ?_
      filter_upwards [hCq, hhalf, hLpos, hlog1] with i hi hhalfi hLposi hlogi
      have hllnn : (0 : ℝ) ≤ Real.log (Real.log i) := Real.log_nonneg hlogi
      have hstep : Real.log (Real.log i) / L i ≤ 2 * (Real.log (Real.log i) / hsched i) := by
        have hhalf0 : (0 : ℝ) < hsched i / 2 := by linarith [hLposi.2]
        have hmono : Real.log (Real.log i) / L i
            ≤ Real.log (Real.log i) / (hsched i / 2) := by gcongr
        refine hmono.trans_eq ?_
        field_simp
      calc α * aRTSTarget A Y θ₀ T i ω a
          ≤ α * (Cq * (Real.log (Real.log i) / L i)) := mul_le_mul_of_nonneg_left hi hα.1
        _ ≤ α * (Cq * (2 * (Real.log (Real.log i) / hsched i))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hCq0) hα.1
        _ = α * (2 * Cq) * (Real.log (Real.log i) / hsched i) := by ring
    filter_upwards [fEfed_of_decay h hT hTnn hα.1 (hthrottle a) hh.tendsto_atTop hsum hsqrt
      hdecay] with ω hω _
    exact hω
  · exact ae_of_all _ fun ω hcon ↦ absurd hcon hfed

end AlphaRAR
