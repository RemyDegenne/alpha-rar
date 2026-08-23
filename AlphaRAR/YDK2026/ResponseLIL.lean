/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.OptionalSkipping
public import AlphaRAR.Mathlib.LILHartmanWintner
public import AlphaRAR.YDK2026.ResponseConsistency

/-!
# Loglog law of the iterated logarithm for the response martingale

Combining Doob optional skipping (`AlphaRAR.iIndepFun_sampledResponse`,
`AlphaRAR.map_sampledResponse_eq`) with the i.i.d. Hartman–Wintner LIL
(`AlphaRAR.iid_hartmanWintner_limsup_le_one`), we obtain the sharp loglog rate for the response
martingale `Q_k n = ∑_{m<n} 𝟙{A m = k}(Y m − θ_k)` of a fixed arm `k` (blueprint
`cor:subsampled_lil`).

The response martingale is a *predictably subsampled* i.i.d. sum: reindexing the pulls of arm `k`,
`Q_k n = ∑_{i < N_{n,k}} (Y_{τ_i} − θ_k)` with `N_{n,k}` the number of pulls before `n` and
`(Y_{τ_i})` the i.i.d. responses at those pulls. Hartman–Wintner applies to the latter, and the
time-change `N_{n,k} → ∞` transports the `limsup` bound to `Q_k`.

## Main results (in progress)

* `AlphaRAR.respMart_eq_sum_sampledSeq`: the reindexing `Q_k n = ∑_{i<N_{n,k}} (Y_{τ_i} − θ_k)`.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Learning Real
open scoped Topology ENNReal

namespace AlphaRAR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The sample of rank `hitCount D n` at a hit is `Y n`.** If `n` is a hit (`D n ω = 1`), the
`(hitCount D n ω)`-th hit time is `n` itself (`Nat.nth_count`), so `Y` sampled there is `Y n`. -/
lemma sampledSeq_hitCount_of_hit {D Y : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} (hn : D n ω = 1) :
    sampledSeq Y D (hitCount D n ω) ω = Y n ω := by
  unfold sampledSeq sampleTime hitCount
  rw [Nat.nth_count hn]

/-- **The hit count diverges** when there are infinitely many hits: `#{ i < n : D i = 1} → ∞`. The
count is monotone and reaches `M + 1` by time `τ_M + 1` (`Nat.count_nth_of_infinite`). -/
lemma hitCount_tendsto_atTop {D : ℕ → Ω → ℝ} {ω : Ω}
    (hinf : {j | D j ω = 1}.Infinite) :
    Tendsto (fun n ↦ hitCount D n ω) atTop atTop := by
  refine Monotone.tendsto_atTop_atTop (hitCount_mono D ω) (fun M ↦ ?_)
  refine ⟨Nat.nth (D · ω = 1) M + 1, ?_⟩
  simp only [hitCount]
  rw [Nat.count_succ, Nat.count_nth_of_infinite hinf, ite_eq_left (Nat.nth_mem_of_infinite hinf M)]
  omega

variable {𝓐 : Type*} {m𝓐 : MeasurableSpace 𝓐} [DecidableEq 𝓐]
  {ν : Kernel 𝓐 ℝ} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}

omit [DecidableEq 𝓐] in
/-- **Reindexing: the response martingale is the subsampled i.i.d. partial sum.** For every `ω`,
`Q_k n ω = ∑_{i < N_{n,k}} (Y_{τ_i} − θ_k)`, where `N_{n,k} = pullCount A k n ω` counts the pulls of
arm `k` before `n` and `Y_{τ_i} = sampledSeq Y (armIndicator A k) i` is the response at the `i`-th
pull. Proved by induction on `n`: a pull at time `n` (rank `N`) contributes `Y_n − θ_k` and advances
the sample rank; a non-pull leaves both sides unchanged. -/
lemma respMart_eq_sum_sampledSeq (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMart ν A Y k n ω
      = ∑ i ∈ Finset.range (hitCount (armIndicator A k) n ω),
          (sampledSeq Y (armIndicator A k) i ω - ν.means k) := by
  induction n with
  | zero => simp [respMart, hitCount]
  | succ n ih =>
    rw [respMart_succ, Pi.add_apply, ih]
    by_cases hp : A n ω = k
    · have hD1 : armIndicator A k n ω = 1 := armIndicator_eq_one_iff.mpr hp
      rw [hitCount_succ_of_hit hD1, Finset.sum_range_succ, sampledSeq_hitCount_of_hit hD1,
        armIndicator, Set.indicator_of_mem (show ω ∈ {ω | A n ω = k} from hp)]
      ring
    · have hD0 : armIndicator A k n ω ≠ 1 := fun h ↦ hp (armIndicator_eq_one_iff.mp h)
      have hcount : hitCount (armIndicator A k) (n + 1) ω = hitCount (armIndicator A k) n ω := by
        unfold hitCount; rw [Nat.count_succ, ite_eq_right hD0, Nat.add_zero]
      rw [hcount, armIndicator, Set.indicator_of_notMem (show ω ∉ {ω | A n ω = k} from hp)]
      simp

/-- The hit count of the arm indicator is the pull count of arm `k`. -/
lemma hitCount_armIndicator_eq_pullCount (k : 𝓐) (n : ℕ) (ω : Ω) :
    hitCount (armIndicator A k) n ω = pullCount A k n ω := by
  rw [hitCount, Nat.count_eq_card_filter_range, pullCount]
  exact congrArg Finset.card (Finset.filter_congr (fun i _ ↦ by rw [armIndicator_eq_one_iff]))

variable [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm 𝓐 ℝ}

/-- **Loglog LIL for the response martingale** (blueprint `cor:subsampled_lil`). For an
algorithm–environment sequence in a stationary environment, if arm `k` is pulled infinitely often
a.s. and its reward law `ν k` is in `L²` (Condition **A**), then
almost surely, for every `β > 1`, eventually
`|Q_k n| ≤ β √(2 · Var[id; ν k] · N_{n,k} · log log N_{n,k})`, where `N_{n,k}` is the number of
pulls of arm `k` before `n`. In particular `Q_k n = O(√(N_{n,k} log log N_{n,k}))`. -/
lemma abs_respMart_le_sqrt_nat_mul_loglog
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (hk_inf : ∀ᵐ ω ∂P, {j | A j ω = k}.Infinite)
    (hνk : MemLp id 2 (ν k)) :
    ∀ᵐ ω ∂P, ∀ β : ℝ, 1 < β → ∀ᶠ n in atTop,
      |respMart ν A Y k n ω| ≤ β * √(2 * Var[id; ν k] * (pullCount A k n ω : ℝ)
        * log (log (pullCount A k n ω : ℝ))) := by
  have hint_id : Integrable (fun x : ℝ ↦ x) (ν k) := hνk.integrable (by norm_num)
  have hint_sq : Integrable (fun x : ℝ ↦ x ^ 2) (ν k) := hνk.integrable_sq
  simp only [← hitCount_armIndicator_eq_pullCount]
  have : IsProbabilityMeasure (ν k) := IsMarkovKernel.isProbabilityMeasure k
  set D := armIndicator A k with hDdef
  set θ := ν.means k with hθdef
  set 𝒢 := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback with h𝒢
  set W : ℕ → Ω → ℝ := fun i ω ↦ sampledClean Y D i ω - θ with hWdef
  -- measurability of the arm selector and the clean samples
  have hD𝒢 : ∀ i, Measurable[𝒢 i] (D i) := by
    intro i
    exact Measurable.ite ((IsAlgEnvSeq.measurable_action_filtrationAction'
      h.measurable_action h.measurable_feedback i) (measurableSet_singleton k))
      measurable_const measurable_const
  have hDinf : ∀ᵐ ω ∂P, {j | D j ω = 1}.Infinite := by
    filter_upwards [hk_inf] with ω hω; rwa [Set.ext (fun j ↦ armIndicator_eq_one_iff)]
  have hCmeas : ∀ i, Measurable (sampledClean Y D i) :=
    fun i ↦ measurable_sampledClean h.measurable_feedback hD𝒢 i
  have hmapC : ∀ i, P.map (sampledClean Y D i) = ν k := fun i ↦
    (Measure.map_congr (sampledSeq_ae_eq_sampledClean hDinf i).symm).trans
      (map_sampledResponse_eq h k hk_inf i)
  -- change of variables through the common law `ν k`
  have hcov : ∀ g : ℝ → ℝ, AEStronglyMeasurable g (ν k) →
      ∫ ω, g (sampledClean Y D 0 ω) ∂P = ∫ x, g x ∂(ν k) := by
    intro g hg
    have hg' : AEStronglyMeasurable g (P.map (sampledClean Y D 0)) := by rw [hmapC 0]; exact hg
    have hmap := integral_map (φ := sampledClean Y D 0) (hCmeas 0).aemeasurable hg'
    rw [hmapC 0] at hmap
    exact hmap.symm
  have hintcov : ∀ g : ℝ → ℝ, Integrable g (ν k) →
      Integrable (fun ω ↦ g (sampledClean Y D 0 ω)) P := by
    intro g hg
    have hg' : AEStronglyMeasurable g (P.map (sampledClean Y D 0)) := by
      rw [hmapC 0]; exact hg.aestronglyMeasurable
    refine (integrable_map_measure hg' (hCmeas 0).aemeasurable).mp ?_
    rw [hmapC 0]; exact hg
  have hθ' : θ = ∫ x, x ∂(ν k) := by rw [hθdef, Kernel.means_apply]; simp only [id_eq]
  have hintC0 : Integrable (sampledClean Y D 0) P := hintcov (fun x ↦ x) hint_id
  have hmean : ∫ ω, sampledClean Y D 0 ω ∂P = θ := by
    rw [hθ']; exact hcov (fun x ↦ x) hint_id.aestronglyMeasurable
  -- moments of the centred clean sample `W 0`
  have hcent : ∫ ω, W 0 ω ∂P = 0 := by
    have hsplit : ∫ ω, W 0 ω ∂P = (∫ ω, sampledClean Y D 0 ω ∂P) - θ := by
      simp only [hWdef]; rw [integral_sub hintC0 (integrable_const θ)]; simp
    rw [hsplit, hmean, sub_self]
  have hintCsq : Integrable (fun x ↦ (x - θ) ^ 2) (ν k) := by
    have hexp : (fun x : ℝ ↦ (x - θ) ^ 2) = fun x ↦ x ^ 2 - 2 * θ * x + θ ^ 2 := by
      funext x; ring
    rw [hexp]
    exact (hint_sq.sub (hint_id.const_mul (2 * θ))).add (integrable_const (θ ^ 2))
  have hint2W : MemLp (W 0) 2 P :=
    (memLp_two_iff_integrable_sq ((hCmeas 0).sub_const θ).aestronglyMeasurable).mpr
      (hintcov (fun x ↦ (x - θ) ^ 2) hintCsq)
  have hVeq : ∫ ω, W 0 ω ^ 2 ∂P = Var[id; ν k] := by
    rw [show (fun ω ↦ W 0 ω ^ 2) = fun ω ↦ (fun x ↦ (x - θ) ^ 2) (sampledClean Y D 0 ω) from rfl,
      hcov (fun x ↦ (x - θ) ^ 2) hintCsq.aestronglyMeasurable, variance_id_eq_integral,
      hθdef, Kernel.means_apply]
  -- independence and identical distribution of the centred clean samples
  have hW_sm : ∀ i, StronglyMeasurable (W i) := fun i ↦ ((hCmeas i).sub_const θ).stronglyMeasurable
  have hindepW : iIndepFun W P := by
    have h1 : iIndepFun (fun i ω ↦ sampledSeq Y D i ω - θ) P :=
      (iIndepFun_sampledResponse h k hk_inf).comp (fun _ x ↦ x - θ)
        (fun _ ↦ measurable_id.sub_const θ)
    refine (iIndepFun_congr ?_).mp h1
    intro i
    filter_upwards [sampledSeq_ae_eq_sampledClean (Y := Y) (D := D) hDinf i] with ω hω
    simp only [hWdef, hω]
  have hidW : ∀ j, IdentDistrib (W j) (W 0) P P := fun j ↦
    (IdentDistrib.mk (hCmeas j).aemeasurable (hCmeas 0).aemeasurable
      ((hmapC j).trans (hmapC 0).symm)).comp (measurable_id.sub_const θ)
  -- Hartman–Wintner (upper) for `W` and for `-W`
  have hev_up := hw_eventually hW_sm hindepW hidW hint2W hcent
  have hev_lo := hw_eventually (μ := P) (Y := fun i ω ↦ -(W i ω)) (fun i ↦ (hW_sm i).neg)
    (hindepW.comp (fun _ x ↦ -x) (fun _ ↦ measurable_neg))
    (fun j ↦ (hidW j).comp measurable_neg)
    hint2W.neg
    (by rw [integral_neg, hcent, neg_zero])
  -- pull everything onto one full-measure set
  have hae_eq : ∀ᵐ ω ∂P, ∀ i, sampledSeq Y D i ω = sampledClean Y D i ω := by
    rw [ae_all_iff]; exact fun i ↦ sampledSeq_ae_eq_sampledClean hDinf i
  filter_upwards [hev_up, hev_lo, hae_eq, hDinf] with ω hup hlo heq hinf
  -- reindex: `Q_k n = ∑_{i<N_n} W_i`
  have hreindex : ∀ n, respMart ν A Y k n ω = ∑ i ∈ Finset.range (hitCount D n ω), W i ω := by
    intro n
    rw [respMart_eq_sum_sampledSeq, ← hDdef, ← hθdef]
    exact Finset.sum_congr rfl (fun i _ ↦ by simp only [hWdef, heq i])
  intro β hβ
  have hN := hitCount_tendsto_atTop (D := D) hinf
  filter_upwards [hN.eventually (hup β hβ), hN.eventually (hlo β hβ)] with n hn_up hn_lo
  rw [hreindex, ← hVeq]
  simp only [neg_sq] at hn_lo
  rw [Finset.sum_neg_distrib] at hn_lo
  exact abs_le.mpr ⟨by linarith [hn_lo], hn_up⟩

/-- **Response martingale is `O(√(n log log n))` end-to-end** (blueprint `cor:subsampled_lil`,
`n`-indexed form). Discharging the `hQ` input of
`ae_eventually_abs_respMart_le_sqrt_nat_mul_loglog` with the subsampled loglog LIL
`abs_respMart_le_sqrt_nat_mul_loglog`, the response martingale is a.s.
`|Q_{n,k}| ≤ C√(n log log n)` eventually, provided the pull proportion `N_{n,k}/n → v_k > 0`
(blueprint `lem:match`). Arm `k` being pulled infinitely often (`lem:all_arms_infinite`) is
*derived* from that positive proportion (`infinite_setOf_eq_of_tendsto_div`), so the only remaining
hypothesis is the reward-law moment condition `ν k ∈ L²` (Condition **A**). No positivity of
`Var[id; ν k]` is needed — a zero-variance arm has `Q_k ≡ 0`. -/
lemma ae_eventually_abs_respMart_le_sqrt_nat_mul_loglog_of_proportion
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐)
    (hνk : MemLp id 2 (ν k))
    {v : Ω → ℝ} (hv : ∀ᵐ ω ∂P, 0 < v ω)
    (hN : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v ω))) :
    ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      |respMart ν A Y k n ω| ≤ C * √((n : ℝ) * log (log (n : ℝ))) := by
  have hk_inf : ∀ᵐ ω ∂P, {j | A j ω = k}.Infinite := by
    filter_upwards [hv, hN] with ω hvω hNω
    exact infinite_setOf_eq_of_tendsto_div hvω hNω
  exact ae_eventually_abs_respMart_le_sqrt_nat_mul_loglog k hv hN
    (abs_respMart_le_sqrt_nat_mul_loglog h k hk_inf hνk)

/-- **Loglog LIL rate for the estimator, end-to-end** (blueprint `lem:theta_LIL`, loglog form). The
sequential estimator error is a.s. `O(√(log log n / n))`:
`|θ̂_{n,k} - θ_k| ≤ C'·√(n log log n)/n` eventually. This is the `log log`, sharp-constant upgrade
of the `log`-rate `abs_estimator_sub_le_rate_ae`, obtained by feeding the end-to-end subsampled
loglog bound (`ae_eventually_abs_respMart_le_sqrt_nat_mul_loglog_of_proportion`) through the exact
estimator error identity (blueprint `lem:estimator_bahadur`). Its only probabilistic input is the
pull proportion `N_{n,k}/n → v_k > 0` (`lem:match`) — infinitely-many pulls
(`lem:all_arms_infinite`) is derived from it — together with the reward-law moment conditions
(Condition **A**). -/
lemma abs_estimator_sub_le_rate_loglog_of_proportion
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (θ₀ : ℝ)
    (hνk : MemLp id 2 (ν k))
    {v : Ω → ℝ} (hv : ∀ᵐ ω ∂P, 0 < v ω)
    (hN : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v ω))) :
    ∀ᵐ ω ∂P, ∃ C', ∀ᶠ n in atTop,
      |estimator (fun j ↦ armIndicator A k j ω)
          (Y · ω) θ₀ n - ν.means k|
        ≤ C' * (√((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)) :=
  abs_estimator_sub_le_rate_loglog_ae k θ₀ hv hN
    (ae_eventually_abs_respMart_le_sqrt_nat_mul_loglog_of_proportion h k hνk hv hN)

omit [DecidableEq 𝓐] in
/-- **Loglog estimator rate from a positive proportion, count form** (blueprint `lem:theta_LIL`).
A convenience wrapper on `abs_estimator_sub_le_rate_loglog_of_proportion` that (i) takes the
positive
allocation proportion as a per-`ω` existential `∃ u_k > 0, N_{n,k}/n → u_k` — the shape produced by
the consistency layer — instead of a globally-named limit, and (ii) states it with the assignment
count `count (𝟙{A · = k})` in place of `pullCount`, so callers need no `Decidable`/`Classical`
instance for the pull count (the two agree by `count_indicator_eq_pullCount`). This is the form
consumed when discharging `rho_rate`'s per-arm rate hypothesis for a concrete design. -/
lemma abs_estimator_sub_le_rate_loglog_of_pos_count
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (k : 𝓐) (θ₀ : ℝ)
    (hνk : MemLp id 2 (ν k))
    (hpp : ∀ᵐ ω ∂P, ∃ uk : ℝ, 0 < uk ∧ Tendsto (fun n ↦ count (fun j ↦ armIndicator A k j ω) n
      / (n : ℝ)) atTop (𝓝 uk)) :
    ∀ᵐ ω ∂P, ∃ C', ∀ᶠ n in atTop,
      |estimator (fun j ↦ armIndicator A k j ω)
          (Y · ω) θ₀ n - ν.means k|
        ≤ C' * (√((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)) := by
  classical
  obtain ⟨v, hv, hN⟩ : ∃ v : Ω → ℝ, (∀ᵐ ω ∂P, 0 < v ω) ∧ ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v ω)) := by
    refine ⟨fun ω ↦ if hω : ∃ uk : ℝ, 0 < uk ∧ Tendsto (fun n ↦ count
      (fun j ↦ armIndicator A k j ω) n / (n : ℝ)) atTop (𝓝 uk) then hω.choose else 0, ?_, ?_⟩
    · filter_upwards [hpp] with ω hppω
      rw [dite_eq_left hppω]
      exact hppω.choose_spec.1
    · filter_upwards [hpp] with ω hppω
      rw [dite_eq_left hppω]
      exact (hppω.choose_spec.2).congr fun n ↦ by rw [count_indicator_eq_pullCount]
  exact abs_estimator_sub_le_rate_loglog_of_proportion h k θ₀ hνk hv hN

end AlphaRAR
