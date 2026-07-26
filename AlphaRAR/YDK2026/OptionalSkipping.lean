/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.YDK2026.Response
import Mathlib.Data.Nat.Nth
import Mathlib.Probability.Independence.Basic

/-!
# Doob optional skipping

Let `(D j)` be a `{0,1}`-valued process adapted to a filtration `𝒢` (`D j` is `𝒢 j`-measurable) with
infinitely many hits (`D = 1`) almost surely, and let `(Y j)` be a process such that, on the hit
event `{D j = 1}`, the value `Y j` is *fresh* given `𝒢 j` with a fixed law `ρ`. Concretely we ask
for `μ (Y j ⁻¹' E ∩ S) = ρ E · μ S` for every `S ∈ 𝒢 j` contained in `{D j = 1}`.
Enumerate the hit times `τ_0 < τ_1 < ⋯`. Then the sampled sequence `Z m = Y_{τ_m}` is i.i.d. with
law `ρ`.

This is the probabilistic content of Doob's optional-skipping theorem (blueprint `lem:opt_skip`),
which is not in Mathlib: there is no interaction between `IsStoppingTime` and independence in the
library, so the core is built from scratch. The proof avoids the stopping-time σ-algebra and works
with the fixed-time σ-algebra `𝒢 j` and the countable decomposition over the value of `τ_m`.

The abstract factorisation `hfact` is a *generic sufficient condition*. It is discharged in the
`IsAlgEnvSeq` framework (`AlphaRAR.iIndepFun_sampledResponse`): under a stationary environment the
response `Y (n+1)` is fresh given the history and the current action `filtrationAction (n+1)`, so
sampling the times an arm `k` is pulled (`D j = 𝟙{A j = k}`) yields an i.i.d. `ν k` sequence.

These definitions are the *generic* (any `D`, any `Y`, plain `Ω`) counterparts of the arm-specific
`Learning.stepsUntil`/`Learning.rewardByCount` of the `IsAlgEnvSeq` framework: with the arm selector
`D = armIndicator A k`, `sampleTime D m` is the `m`-th pull time (matching `stepsUntil A k (m+1)`
when finite), `hitCount D n = pullCount A k n`, and `sampledSeq Y D m` is the response at the `m`-th
pull. We keep the generic form here: it is self-contained (no `ℕ∞`, no extended reward space) and
carries the optional-skipping argument for an arbitrary predictable selector.

## Main definitions

* `AlphaRAR.sampleTime D m ω`: the `m`-th hit time `τ_m ω`, via `Nat.nth`.
* `AlphaRAR.hitCount D j ω`: the number of hits before `j` (`= pullCount` for `armIndicator`).
* `AlphaRAR.sampledSeq Y D m ω`: the sampled value `Z_m ω = Y_{τ_m ω} ω`.

## Main results

* `AlphaRAR.measure_iInter_cleanPre`: the finite-dimensional law of the sampled sequence is the
  product `∏ ρ (E i)` (master formula, proved by induction).
* `AlphaRAR.iIndepFun_sampledSeq`, `AlphaRAR.map_sampledSeq_eq`: independence and law of samples.
-/

-- A single classical `Decidable (D j ω = 1)` instance is shared throughout (`Nat.count` and its
-- `card_filter` rewrites must agree on it), so we open `Classical` file-wide rather than locally.
set_option linter.style.openClassical false

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal NNReal Classical

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The `m`-th sampling time (0-indexed): the `m`-th index `j` at which `D j ω = 1`, enumerated by
`Nat.nth`. When there are infinitely many hits this is the strictly increasing enumeration of
`{j | D j ω = 1}`. -/
noncomputable def sampleTime (D : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℕ :=
  Nat.nth (fun j ↦ D j ω = 1) m

/-- The number of hits strictly before time `j`: `#{ i < j : D i ω = 1}`. -/
noncomputable def hitCount (D : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℕ :=
  Nat.count (fun i ↦ D i ω = 1) j

/-- The sampled sequence `Z m ω = Y_{τ_m ω} ω`, the value of `Y` at the `m`-th hit time. -/
noncomputable def sampledSeq (Y D : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  Y (sampleTime D m ω) ω

/-- The **hit event** `{ω | D j ω = 1 ∧ hitCount D j ω = m}`: time `j` is the `m`-th hit. This is
the honestly `𝒢 j`-measurable set that stands in for `{τ_m = j}` (agreeing with it a.e.).
Defined through `hitCount`, it enjoys exact (non-a.e.) disjointness/vanishing identities. -/
def hitEvent (D : ℕ → Ω → ℝ) (j m : ℕ) : Set Ω := {ω | D j ω = 1 ∧ hitCount D j ω = m}

@[simp] lemma mem_hitEvent {D : ℕ → Ω → ℝ} {j m : ℕ} {ω : Ω} :
    ω ∈ hitEvent D j m ↔ D j ω = 1 ∧ hitCount D j ω = m := Iff.rfl

/-- `hitCount` written as a finite sum of indicators, the form making its measurability manifest. -/
lemma hitCount_eq_sum (D : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) :
    hitCount D j ω = ∑ i ∈ Finset.range j, if D i ω = 1 then 1 else 0 := by
  rw [hitCount, Nat.count_eq_card_filter_range, Finset.card_filter]

/-- **Characterization of the hit time.** When there are infinitely many hits, `τ_m ω = j` iff `j`
is a hit (`D j ω = 1`) preceded by exactly `m` earlier hits (`hitCount D j ω = m`). -/
lemma sampleTime_eq_iff {D : ℕ → Ω → ℝ} {ω : Ω}
    (hinf : {j | D j ω = 1}.Infinite) {m j : ℕ} :
    sampleTime D m ω = j ↔ D j ω = 1 ∧ hitCount D j ω = m := by
  rw [sampleTime, hitCount]
  constructor
  · rintro rfl
    exact ⟨Nat.nth_mem_of_infinite hinf m, Nat.count_nth_of_infinite hinf m⟩
  · rintro ⟨hj, hc⟩
    rw [← hc]
    exact Nat.nth_count hj

/-- The hit times are strictly increasing (when there are infinitely many hits). -/
lemma sampleTime_strictMono {D : ℕ → Ω → ℝ} {ω : Ω}
    (hinf : {j | D j ω = 1}.Infinite) :
    StrictMono (fun m ↦ sampleTime D m ω) :=
  Nat.nth_strictMono hinf

/-- Earlier samples happen strictly earlier: `i < n → τ_i ω < τ_n ω`. -/
lemma sampleTime_lt_of_lt {D : ℕ → Ω → ℝ} {ω : Ω}
    (hinf : {j | D j ω = 1}.Infinite) {i n : ℕ} (hin : i < n) :
    sampleTime D i ω < sampleTime D n ω :=
  sampleTime_strictMono hinf hin

/-! ### Deterministic combinatorics of the hit counts -/

/-- The hit count is monotone in time. -/
lemma hitCount_mono (D : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun j ↦ hitCount D j ω) :=
  fun _ _ h ↦ Nat.count_monotone _ h

/-- When time `j` is a hit, the count jumps by one. -/
lemma hitCount_succ_of_hit {D : ℕ → Ω → ℝ} {j : ℕ} {ω : Ω} (h : D j ω = 1) :
    hitCount D (j + 1) ω = hitCount D j ω + 1 := by
  rw [hitCount, hitCount, Nat.count_succ, if_pos h]

/-- **Hit events of a lower rank vanish against a later higher-rank event.** For `i < N` and
`j ≤ k`, `hitEvent D k i ∩ hitEvent D j N = ∅`: at rank-`N` time `j` the count is already `N`, so at
the later time `k` it is at least `N`, incompatible with rank `i < N`. Only monotonicity is used. -/
lemma hitEvent_inter_eq_empty_of_le {D : ℕ → Ω → ℝ} {i N j k : ℕ} (hiN : i < N) (hjk : j ≤ k) :
    hitEvent D k i ∩ hitEvent D j N = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ω ⟨⟨_, hk⟩, _, hj⟩
  have hmono : hitCount D j ω ≤ hitCount D k ω := hitCount_mono D ω hjk
  omega

/-- **The rank-`m` hit events are pairwise disjoint in time.** If `j ≠ j'` and both are the `m`-th
hit, one is strictly before the other; the earlier `D = 1` bumps the count to `m + 1`, contradicting
rank `m` at the later time. -/
lemma hitEvent_pairwise_disjoint (D : ℕ → Ω → ℝ) (m : ℕ) :
    Pairwise (Function.onFun Disjoint (fun j ↦ hitEvent D j m)) := by
  have key : ∀ {j j' : ℕ}, j < j' → Disjoint (hitEvent D j m) (hitEvent D j' m) := by
    intro j j' hlt
    rw [Set.disjoint_left]
    rintro ω ⟨hjhit, hj⟩ ⟨_, hj'⟩
    have h1 : hitCount D (j + 1) ω = m + 1 := hj ▸ hitCount_succ_of_hit hjhit
    have h2 : hitCount D (j + 1) ω ≤ hitCount D j' ω := hitCount_mono D ω hlt
    omega
  intro j j' hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key h
  · exact (key h).symm

variable {𝒢 : Filtration ℕ m0} {D Y : ℕ → Ω → ℝ} {E : Set ℝ}

/-- `hitCount D j` is `𝒢 j`-measurable: a finite sum, over `i < j`, of indicators of the adapted
events `{D i = 1}` (each `𝒢 i ≤ 𝒢 j`-measurable). -/
lemma measurable_hitCount (hD : ∀ i, Measurable[𝒢 i] (D i)) (j : ℕ) :
    Measurable[𝒢 j] (hitCount D j) := by
  have hrw : hitCount D j = fun ω ↦ ∑ i ∈ Finset.range j, if D i ω = 1 then (1 : ℕ) else 0 :=
    funext (hitCount_eq_sum D j)
  rw [hrw]
  refine Finset.measurable_sum _ (fun i hi ↦ ?_)
  rw [Finset.mem_range] at hi
  have hset : MeasurableSet[𝒢 j] {ω | D i ω = 1} :=
    (𝒢.mono hi.le) _ ((hD i) (measurableSet_singleton 1))
  exact Measurable.ite hset measurable_const measurable_const

/-- The hit event `hitEvent D j m` is `𝒢 j`-measurable. -/
lemma measurableSet_filt_hitEvent (hD : ∀ i, Measurable[𝒢 i] (D i)) (j m : ℕ) :
    MeasurableSet[𝒢 j] (hitEvent D j m) := by
  have h1 : MeasurableSet[𝒢 j] {ω | D j ω = 1} := (hD j) (measurableSet_singleton 1)
  have h2 : MeasurableSet[𝒢 j] {ω | hitCount D j ω = m} :=
    measurable_hitCount hD j (measurableSet_singleton m)
  rw [hitEvent, Set.ofPred_and]
  exact h1.inter h2

/-- `hitEvent D j m` is measurable in the ambient space (via `𝒢 j ≤ m0`). -/
lemma measurableSet_hitEvent (hD : ∀ i, Measurable[𝒢 i] (D i)) (j m : ℕ) :
    MeasurableSet (hitEvent D j m) :=
  (𝒢.le j) _ (measurableSet_filt_hitEvent hD j m)

/-- Up to a null set, `{τ_m = j}` is the adapted hit event `hitEvent D j m`. -/
lemma sampleTime_eq_ae (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite) (m j : ℕ) :
    {ω | sampleTime D m ω = j} =ᵐ[μ] hitEvent D j m := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [hDinf] with ω hinf
  exact sampleTime_eq_iff hinf

/-! ### Clean measurable stand-ins for the sampled preimages

The map `ω ↦ Y (τ_m ω) ω` is a random-index composition whose ambient measurability is awkward. We
replace `(sampledSeq Y D i) ⁻¹' E` by the honestly measurable `cleanPre`, a union over the possible
hit times, and its finite truncation `cleanBdd` (measurable in `𝒢 j`). -/

/-- The clean stand-in for `(sampledSeq Y D i) ⁻¹' E`: over all times `k`, the event that `k` is the
`i`-th hit and `Y k ∈ E`. Agrees a.e. with the sampled preimage. -/
def cleanPre (Y D : ℕ → Ω → ℝ) (E : Set ℝ) (i : ℕ) : Set Ω :=
  ⋃ k, (Y k ⁻¹' E ∩ hitEvent D k i)

/-- The truncation of `cleanPre` to hit times `k < j`; it is `𝒢 j`-measurable. -/
def cleanBdd (Y D : ℕ → Ω → ℝ) (E : Set ℝ) (i j : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range j, (Y k ⁻¹' E ∩ hitEvent D k i)

/-- Membership in `cleanPre`. -/
lemma mem_cleanPre {i : ℕ} {ω : Ω} :
    ω ∈ cleanPre Y D E i ↔ ∃ k, Y k ω ∈ E ∧ D k ω = 1 ∧ hitCount D k ω = i := by
  simp only [cleanPre, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, mem_hitEvent]

/-- `cleanPre` is measurable in the ambient space. -/
lemma measurableSet_cleanPre (hYmeas : ∀ k, Measurable (Y k))
    (hD : ∀ i, Measurable[𝒢 i] (D i)) (hE : MeasurableSet E) (i : ℕ) :
    MeasurableSet (cleanPre Y D E i) := by
  refine MeasurableSet.iUnion (fun k ↦ ?_)
  exact ((hYmeas k) hE).inter (measurableSet_hitEvent hD k i)

/-- `cleanBdd` is `𝒢 j`-measurable: each `Y k ⁻¹' E` with `k < j` is `𝒢 j`-measurable (adaptedness
of `Y`) and each hit event is `𝒢 k ≤ 𝒢 j`-measurable. -/
lemma measurableSet_filt_cleanBdd (hYlt : ∀ a b, a < b → Measurable[𝒢 b] (Y a))
    (hD : ∀ i, Measurable[𝒢 i] (D i)) (hE : MeasurableSet E) (i j : ℕ) :
    MeasurableSet[𝒢 j] (cleanBdd Y D E i j) := by
  refine MeasurableSet.biUnion (Finset.range j).countable_toSet (fun k hk ↦ ?_)
  rw [Finset.mem_coe, Finset.mem_range] at hk
  have hY : MeasurableSet[𝒢 j] (Y k ⁻¹' E) := (hYlt k j hk) hE
  have hH : MeasurableSet[𝒢 j] (hitEvent D k i) :=
    (𝒢.mono hk.le) _ (measurableSet_filt_hitEvent hD k i)
  exact hY.inter hH

/-- **The sampled preimage equals `cleanPre` a.e.** On the full-measure set where hits are infinite,
`Y (τ_i ω) ω ∈ E` iff some time `k` is the `i`-th hit with `Y k ω ∈ E` (namely `k = τ_i ω`). -/
lemma sampledSeq_preimage_ae_cleanPre
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite) (i : ℕ) :
    (sampledSeq Y D i) ⁻¹' E =ᵐ[μ] cleanPre Y D E i := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [hDinf] with ω hinf
  rw [Set.mem_preimage, mem_cleanPre]
  constructor
  · intro hmem
    exact ⟨sampleTime D i ω, hmem, (sampleTime_eq_iff hinf).mp rfl⟩
  · rintro ⟨k, hYk, hk⟩
    have : sampleTime D i ω = k := (sampleTime_eq_iff hinf).mpr hk
    rw [sampledSeq, this]
    exact hYk

/-- **Exact reduction.** For `i < N`, intersecting `cleanPre … i` with a rank-`N` hit event at time
`j` kills every hit time `k ≥ j` (a lower rank cannot occur at or after a higher rank), leaving the
finite truncation `cleanBdd … i j`. This exact set identity is what reduces `cleanPre` to something
`𝒢 j`-measurable. -/
lemma cleanPre_inter_hitEvent {i N j : ℕ} (hiN : i < N) :
    cleanPre Y D E i ∩ hitEvent D j N = cleanBdd Y D E i j ∩ hitEvent D j N := by
  ext ω
  simp only [cleanPre, cleanBdd, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage,
    Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨⟨k, hYk, hHk⟩, hHjN⟩
    have hkj : k < j := by
      by_contra hle
      rw [not_lt] at hle
      have hempty := hitEvent_inter_eq_empty_of_le (D := D) hiN hle
      rw [Set.eq_empty_iff_forall_notMem] at hempty
      exact hempty ω ⟨hHk, hHjN⟩
    exact ⟨⟨k, hkj, hYk, hHk⟩, hHjN⟩
  · rintro ⟨⟨k, _, hYk, hHk⟩, hHjN⟩
    exact ⟨⟨k, hYk, hHk⟩, hHjN⟩

/-- Distribute a common intersection through a finite intersection when it agrees factorwise. -/
lemma biInter_inter_eq_of_inter_eq {ι : Type*} (s : Finset ι) (A A' : ι → Set Ω) (B : Set Ω)
    (h : ∀ i ∈ s, A i ∩ B = A' i ∩ B) :
    (⋂ i ∈ s, A i) ∩ B = (⋂ i ∈ s, A' i) ∩ B := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  refine ⟨fun ⟨hA, hB⟩ ↦ ⟨fun i hi ↦ ?_, hB⟩, fun ⟨hA', hB⟩ ↦ ⟨fun i hi ↦ ?_, hB⟩⟩
  · have := (Set.ext_iff.mp (h i hi) ω).mp ⟨hA i hi, hB⟩; exact this.1
  · have := (Set.ext_iff.mp (h i hi) ω).mpr ⟨hA' i hi, hB⟩; exact this.1

/-! ### The finite-dimensional distributions of the sampled sequence -/

/-- **Master formula.** With a common sampled law `ρ`, the prefix intersection of clean sampled
preimages has product measure `μ (⋂_{i<N} cleanPre (E i) i) = ∏_{i<N} ρ (E i)`. Proved by induction
on `N`: the newest sample `N` is peeled off and, decomposing over its hit time `j`, the past factor
`W ∩ hitEvent D j N` is `𝒢 j`-measurable and contained in `{D j = 1}`, so the freshness `hfact`
factorises it out with weight `ρ (E N)`; summing over the a.e.-covering, pairwise-disjoint hit
events collapses back to `μ W`. -/
lemma measure_iInter_cleanPre [IsProbabilityMeasure μ]
    (hYmeas : ∀ k, Measurable (Y k))
    (hYlt : ∀ a b, a < b → Measurable[𝒢 b] (Y a))
    (hD : ∀ i, Measurable[𝒢 i] (D i))
    (ρ : Measure ℝ)
    (hfact : ∀ (j : ℕ) (E' : Set ℝ), MeasurableSet E' → ∀ S, MeasurableSet[𝒢 j] S →
      S ⊆ {ω | D j ω = 1} → μ (Y j ⁻¹' E' ∩ S) = ρ E' * μ S)
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite)
    (E : ℕ → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (N : ℕ) :
    μ (⋂ i ∈ Finset.range N, cleanPre Y D (E i) i) = ∏ i ∈ Finset.range N, ρ (E i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    set W := ⋂ i ∈ Finset.range N, cleanPre Y D (E i) i with hW
    have hWmeas : MeasurableSet W :=
      MeasurableSet.biInter (Finset.range N).countable_toSet
        (fun i _ ↦ measurableSet_cleanPre hYmeas hD (hE i) i)
    have hWsucc : (⋂ i ∈ Finset.range (N + 1), cleanPre Y D (E i) i)
        = W ∩ cleanPre Y D (E N) N := by
      ext ω
      simp only [hW, Set.mem_iInter, Set.mem_inter_iff, Finset.mem_range]
      constructor
      · intro h; exact ⟨fun i hi ↦ h i (by omega), h N (by omega)⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact h1 i h
        · subst h; exact h2
    rw [hWsucc, Finset.prod_range_succ, ← ih]
    have hcleanN : cleanPre Y D (E N) N = ⋃ j, (Y j ⁻¹' (E N) ∩ hitEvent D j N) := rfl
    rw [hcleanN, Set.inter_iUnion]
    have hSmeas : ∀ j, MeasurableSet (W ∩ (Y j ⁻¹' (E N) ∩ hitEvent D j N)) := fun j ↦
      hWmeas.inter (((hYmeas j) (hE N)).inter (measurableSet_hitEvent hD j N))
    have hSdisj : Pairwise (Function.onFun Disjoint
        (fun j ↦ W ∩ (Y j ⁻¹' (E N) ∩ hitEvent D j N))) := fun j j' hjj ↦
      (hitEvent_pairwise_disjoint D N hjj).mono
        (Set.inter_subset_right.trans Set.inter_subset_right)
        (Set.inter_subset_right.trans Set.inter_subset_right)
    rw [measure_iUnion hSdisj hSmeas]
    have hterm : ∀ j, μ (W ∩ (Y j ⁻¹' (E N) ∩ hitEvent D j N))
        = ρ (E N) * μ (W ∩ hitEvent D j N) := by
      intro j
      have hWred : W ∩ hitEvent D j N
          = (⋂ i ∈ Finset.range N, cleanBdd Y D (E i) i j) ∩ hitEvent D j N := by
        rw [hW]
        exact biInter_inter_eq_of_inter_eq _ _ _ _
          (fun i hi ↦ cleanPre_inter_hitEvent (by rwa [Finset.mem_range] at hi))
      have hSmeas' : MeasurableSet[𝒢 j]
          ((⋂ i ∈ Finset.range N, cleanBdd Y D (E i) i j) ∩ hitEvent D j N) :=
        (MeasurableSet.biInter (Finset.range N).countable_toSet
          (fun i _ ↦ measurableSet_filt_cleanBdd hYlt hD (hE i) i j)).inter
          (measurableSet_filt_hitEvent hD j N)
      have hSsub : ((⋂ i ∈ Finset.range N, cleanBdd Y D (E i) i j) ∩ hitEvent D j N)
          ⊆ {ω | D j ω = 1} := fun ω hω ↦ (mem_hitEvent.mp hω.2).1
      have hrearrange : W ∩ (Y j ⁻¹' (E N) ∩ hitEvent D j N)
          = (Y j ⁻¹' (E N)) ∩ (W ∩ hitEvent D j N) := by
        ext ω; simp only [Set.mem_inter_iff]; tauto
      rw [hrearrange, hWred, hfact j (E N) (hE N) _ hSmeas' hSsub, ← hWred]
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_left]
    have hWIdisj : Pairwise (Function.onFun Disjoint (fun j ↦ W ∩ hitEvent D j N)) := fun j j' hjj ↦
      (hitEvent_pairwise_disjoint D N hjj).mono Set.inter_subset_right Set.inter_subset_right
    have hWImeas : ∀ j, MeasurableSet (W ∩ hitEvent D j N) := fun j ↦
      hWmeas.inter (measurableSet_hitEvent hD j N)
    have hsum : ∑' j, μ (W ∩ hitEvent D j N) = μ W := by
      rw [← measure_iUnion hWIdisj hWImeas, ← Set.inter_iUnion]
      apply measure_congr
      have hcover : (⋃ j, hitEvent D j N) =ᵐ[μ] Set.univ := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [hDinf] with ω hinf
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        exact ⟨sampleTime D N ω, (sampleTime_eq_iff hinf).mp rfl⟩
      have h := (Filter.EventuallyEq.refl (ae μ) W).inter hcover
      rwa [Set.inter_univ] at h
    rw [hsum, mul_comm]

/-! ### Independence and law of the sampled sequence

We transfer the master formula from `cleanPre` to the honest sampled preimages (a.e. equal), pad
arbitrary finite index sets to prefixes, and package the result as `iIndepFun` together with the
common law `ρ`. A measurable a.e.-representative `sampledClean` supplies `AEMeasurable`. -/

/-- Termwise a.e.-equality of a finite family lifts to their intersections. -/
lemma biInter_ae_eq {ι : Type*} (s : Finset ι) {f g : ι → Set Ω}
    (h : ∀ i ∈ s, f i =ᵐ[μ] g i) : (⋂ i ∈ s, f i) =ᵐ[μ] (⋂ i ∈ s, g i) := by
  rw [Filter.eventuallyEq_set]
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ s, (ω ∈ f i ↔ ω ∈ g i) :=
    (eventually_all_finset s).mpr (fun i hi ↦ Filter.eventuallyEq_set.mp (h i hi))
  filter_upwards [hall] with ω hω
  simp only [Set.mem_iInter]
  exact ⟨fun H i hi ↦ (hω i hi).mp (H i hi), fun H i hi ↦ (hω i hi).mpr (H i hi)⟩

variable [IsProbabilityMeasure μ]

/-- The master formula transferred to the honest sampled preimages. -/
lemma measure_iInter_sampledSeq_preimage
    (hYmeas : ∀ k, Measurable (Y k)) (hYlt : ∀ a b, a < b → Measurable[𝒢 b] (Y a))
    (hD : ∀ i, Measurable[𝒢 i] (D i)) (ρ : Measure ℝ)
    (hfact : ∀ (j : ℕ) (E' : Set ℝ), MeasurableSet E' → ∀ S, MeasurableSet[𝒢 j] S →
      S ⊆ {ω | D j ω = 1} → μ (Y j ⁻¹' E' ∩ S) = ρ E' * μ S)
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite)
    (E : ℕ → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (N : ℕ) :
    μ (⋂ i ∈ Finset.range N, sampledSeq Y D i ⁻¹' E i) = ∏ i ∈ Finset.range N, ρ (E i) := by
  rw [measure_congr (biInter_ae_eq _
    (fun i _ ↦ sampledSeq_preimage_ae_cleanPre (E := E i) hDinf i))]
  exact measure_iInter_cleanPre hYmeas hYlt hD ρ hfact hDinf E hE N

/-- **The finite-dimensional laws of the sampled sequence are the product `∏ ρ (sets i)`**, over an
arbitrary finite index set (obtained by padding a prefix with `univ` factors). -/
lemma measure_iInter_sampledSeq_preimage_finset
    (hYmeas : ∀ k, Measurable (Y k)) (hYlt : ∀ a b, a < b → Measurable[𝒢 b] (Y a))
    (hD : ∀ i, Measurable[𝒢 i] (D i)) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hfact : ∀ (j : ℕ) (E' : Set ℝ), MeasurableSet E' → ∀ S, MeasurableSet[𝒢 j] S →
      S ⊆ {ω | D j ω = 1} → μ (Y j ⁻¹' E' ∩ S) = ρ E' * μ S)
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite)
    (S : Finset ℕ) {sets : ℕ → Set ℝ} (hsets : ∀ i ∈ S, MeasurableSet (sets i)) :
    μ (⋂ i ∈ S, sampledSeq Y D i ⁻¹' sets i) = ∏ i ∈ S, ρ (sets i) := by
  classical
  set N := S.sup id + 1 with hN
  have hSsub : S ⊆ Finset.range N :=
    fun i hi ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  set E' : ℕ → Set ℝ := fun i ↦ if i ∈ S then sets i else Set.univ with hE'
  have hE'meas : ∀ i, MeasurableSet (E' i) := by
    intro i; by_cases hi : i ∈ S
    · simpa only [hE', if_pos hi] using hsets i hi
    · simp only [hE', if_neg hi]; exact MeasurableSet.univ
  have hset_eq : (⋂ i ∈ S, sampledSeq Y D i ⁻¹' sets i)
      = ⋂ i ∈ Finset.range N, sampledSeq Y D i ⁻¹' E' i := by
    ext ω
    simp only [Set.mem_iInter₂, Set.mem_preimage, hE']
    constructor
    · intro h i hi; split_ifs with hiS
      · exact h i hiS
      · exact Set.mem_univ _
    · intro h i hiS; have := h i (hSsub hiS); rwa [if_pos hiS] at this
  have hprod_eq : ∏ i ∈ Finset.range N, ρ (E' i) = ∏ i ∈ S, ρ (sets i) := by
    rw [← Finset.prod_subset hSsub (fun i _ hiS ↦ by simp only [hE', if_neg hiS, measure_univ])]
    exact Finset.prod_congr rfl (fun i hi ↦ by simp only [hE', if_pos hi])
  rw [hset_eq, measure_iInter_sampledSeq_preimage hYmeas hYlt hD ρ hfact hDinf E' hE'meas N,
    hprod_eq]

/-- The **law of a single sample** is `ρ`: `μ (sampledSeq Y D m ⁻¹' F) = ρ F`. -/
lemma measure_sampledSeq_preimage
    (hYmeas : ∀ k, Measurable (Y k)) (hYlt : ∀ a b, a < b → Measurable[𝒢 b] (Y a))
    (hD : ∀ i, Measurable[𝒢 i] (D i)) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hfact : ∀ (j : ℕ) (E' : Set ℝ), MeasurableSet E' → ∀ S, MeasurableSet[𝒢 j] S →
      S ⊆ {ω | D j ω = 1} → μ (Y j ⁻¹' E' ∩ S) = ρ E' * μ S)
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite)
    (m : ℕ) {F : Set ℝ} (hF : MeasurableSet F) :
    μ (sampledSeq Y D m ⁻¹' F) = ρ F := by
  have h := measure_iInter_sampledSeq_preimage_finset hYmeas hYlt hD ρ hfact hDinf {m}
    (sets := fun _ ↦ F) (by simp [hF])
  simpa using h

/-- A measurable a.e.-representative of the `m`-th sample: on the full-measure infinite-hits set,
exactly one hit event `hitEvent D k m` (namely `k = τ_m`) contains `ω`, so the disjoint indicator
sum picks out `Y_{τ_m} = sampledSeq`. -/
noncomputable def sampledClean (Y D : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑' k, (hitEvent D k m).indicator (Y k) ω

lemma measurable_sampledClean (hYmeas : ∀ k, Measurable (Y k))
    (hD : ∀ i, Measurable[𝒢 i] (D i)) (m : ℕ) : Measurable (sampledClean Y D m) :=
  Measurable.tsum (fun k ↦ (hYmeas k).indicator (measurableSet_hitEvent hD k m))

omit [IsProbabilityMeasure μ] in
lemma sampledSeq_ae_eq_sampledClean
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite) (m : ℕ) :
    sampledSeq Y D m =ᵐ[μ] sampledClean Y D m := by
  filter_upwards [hDinf] with ω hinf
  have hzero : ∀ k, k ≠ sampleTime D m ω → (hitEvent D k m).indicator (Y k) ω = 0 := by
    intro k hk
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hk ((sampleTime_eq_iff hinf).mpr (mem_hitEvent.mp hmem)).symm
  rw [sampledSeq, sampledClean, tsum_eq_single (sampleTime D m ω) hzero,
    Set.indicator_of_mem (mem_hitEvent.mpr ((sampleTime_eq_iff hinf).mp rfl))]

omit [IsProbabilityMeasure μ] in
lemma aemeasurable_sampledSeq (hYmeas : ∀ k, Measurable (Y k)) (hD : ∀ i, Measurable[𝒢 i] (D i))
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite) (m : ℕ) :
    AEMeasurable (sampledSeq Y D m) μ :=
  (measurable_sampledClean hYmeas hD m).aemeasurable.congr
    (sampledSeq_ae_eq_sampledClean hDinf m).symm

/-- **The law of each sample is `ρ`.** -/
lemma map_sampledSeq_eq
    (hYmeas : ∀ k, Measurable (Y k)) (hYlt : ∀ a b, a < b → Measurable[𝒢 b] (Y a))
    (hD : ∀ i, Measurable[𝒢 i] (D i)) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hfact : ∀ (j : ℕ) (E' : Set ℝ), MeasurableSet E' → ∀ S, MeasurableSet[𝒢 j] S →
      S ⊆ {ω | D j ω = 1} → μ (Y j ⁻¹' E' ∩ S) = ρ E' * μ S)
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite) (m : ℕ) :
    μ.map (sampledSeq Y D m) = ρ := by
  refine Measure.ext (fun F hF ↦ ?_)
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_sampledSeq hYmeas hD hDinf m) hF]
  exact measure_sampledSeq_preimage hYmeas hYlt hD ρ hfact hDinf m hF

/-- **The sampled sequence is independent.** -/
lemma iIndepFun_sampledSeq
    (hYmeas : ∀ k, Measurable (Y k)) (hYlt : ∀ a b, a < b → Measurable[𝒢 b] (Y a))
    (hD : ∀ i, Measurable[𝒢 i] (D i)) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hfact : ∀ (j : ℕ) (E' : Set ℝ), MeasurableSet E' → ∀ S, MeasurableSet[𝒢 j] S →
      S ⊆ {ω | D j ω = 1} → μ (Y j ⁻¹' E' ∩ S) = ρ E' * μ S)
    (hDinf : ∀ᵐ ω ∂μ, {j | D j ω = 1}.Infinite) :
    iIndepFun (sampledSeq Y D) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  rw [measure_iInter_sampledSeq_preimage_finset hYmeas hYlt hD ρ hfact hDinf S
    (fun i hi ↦ hsets i hi)]
  exact Finset.prod_congr rfl
    (fun i hi ↦ (measure_sampledSeq_preimage hYmeas hYlt hD ρ hfact hDinf i (hsets i hi)).symm)

/-! ### Optional skipping in the algorithm–environment framework

We discharge the abstract freshness hypothesis `hfact` for the stationary-environment response
process: with `𝒢 = filtrationAction`, the selector `D j = 𝟙{A j = k}` of arm `k`, and common law
`ν k`, the factorisation follows from `condExp_feedback_comp` (the conditional law of the response
given the history and current action is `ν (A j)`). Hence sampling the pulls of arm `k` yields an
i.i.d. sequence with law `ν k` — Doob's optional skipping (blueprint `lem:opt_skip`). -/

open Learning

variable {𝓐 : Type*} {m𝓐 : MeasurableSpace 𝓐} [MeasurableSingletonClass 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν] {A : ℕ → Ω → 𝓐} {alg : Algorithm 𝓐 ℝ}

omit [MeasurableSingletonClass 𝓐] in
/-- **Discharge of the freshness hypothesis.** For the arm-`k` selector in a stationary environment,
`μ (Y j ⁻¹' E ∩ S) = (ν k) E · μ S` whenever `S` is measurable in the action-augmented filtration
and forces `A j = k`: there the conditional law of the response `Y j` is the constant `ν k`. -/
lemma hfact_stationaryEnv {Y : ℕ → Ω → ℝ} (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) μ) (k : 𝓐)
    (j : ℕ) {E : Set ℝ} (hE : MeasurableSet E) {S : Set Ω}
    (hS : MeasurableSet[IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback j] S)
    (hSsub : S ⊆ {ω | armIndicator A k j ω = 1}) :
    μ (Y j ⁻¹' E ∩ S) = (ν k) E * μ S := by
  set 𝒢 := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback with h𝒢
  have hmle : 𝒢 j ≤ m0 := 𝒢.le j
  have hSamb : MeasurableSet S := hmle S hS
  have hYjmeas : Measurable (Y j) := h.measurable_feedback j
  set g : ℝ → ℝ := E.indicator (fun _ ↦ 1) with hg_def
  have hg : StronglyMeasurable g := stronglyMeasurable_const.indicator hE
  have hcomp : (fun ω ↦ g (Y j ω)) = (Y j ⁻¹' E).indicator (fun _ ↦ 1) := by
    funext ω; simp only [hg_def, Set.indicator_apply, Set.mem_preimage]
  have hint : Integrable (fun ω ↦ g (Y j ω)) μ := by
    rw [hcomp]; exact (integrable_const 1).indicator (hYjmeas hE)
  have hgint_val : ∀ a : 𝓐, (ν a)[g] = ((ν a) E).toReal := by
    intro a
    rw [hg_def, integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  have hcond := h.condExp_feedback_comp j hg hint
  have e1 : ∫ ω in S, g (Y j ω) ∂μ = (μ (Y j ⁻¹' E ∩ S)).toReal := by
    rw [hcomp, setIntegral_indicator (hYjmeas hE), setIntegral_const, smul_eq_mul, mul_one,
      Set.inter_comm, Measure.real]
  have e2 : ∫ ω in S, g (Y j ω) ∂μ = ∫ _ω in S, ((ν k) E).toReal ∂μ := by
    rw [← setIntegral_condExp hmle hint hS]
    refine setIntegral_congr_ae hSamb ?_
    filter_upwards [hcond] with ω hω hωS
    rw [hω, hgint_val (A j ω), armIndicator_eq_one_iff.mp (hSsub hωS)]
  have key : (μ (Y j ⁻¹' E ∩ S)).toReal = ((ν k) E).toReal * (μ S).toReal := by
    rw [← e1, e2, setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
  have hne : (ν k) E * μ S ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top (ν k) E) (measure_ne_top μ S)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (Y j ⁻¹' E ∩ S)),
    ← ENNReal.ofReal_toReal hne, ENNReal.toReal_mul, key]

/-- **Doob optional skipping (independence).** For an algorithm–environment sequence in a stationary
environment with per-arm reward kernel `ν`, if arm `k` is pulled infinitely often almost surely,
then the responses observed at the pulls of arm `k`, `sampledSeq Y (armIndicator A k)`, are
independent. (Blueprint `lem:opt_skip`.) -/
theorem iIndepFun_sampledResponse {Y : ℕ → Ω → ℝ} (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) μ)
    (k : 𝓐) (hk_inf : ∀ᵐ ω ∂μ, {j | A j ω = k}.Infinite) :
    iIndepFun (sampledSeq Y (armIndicator A k)) μ := by
  set 𝒢 := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback with h𝒢
  haveI : IsProbabilityMeasure (ν k) := IsMarkovKernel.isProbabilityMeasure k
  have hDinf : ∀ᵐ ω ∂μ, {j | armIndicator A k j ω = 1}.Infinite := by
    filter_upwards [hk_inf] with ω hω
    rwa [Set.ext (fun j ↦ armIndicator_eq_one_iff)]
  have hD : ∀ i, Measurable[𝒢 i] (armIndicator A k i) := by
    intro i
    have hset : MeasurableSet[𝒢 i] {ω | A i ω = k} :=
      (IsAlgEnvSeq.measurable_action_filtrationAction' h.measurable_action h.measurable_feedback i)
        (measurableSet_singleton k)
    exact Measurable.ite hset measurable_const measurable_const
  exact iIndepFun_sampledSeq h.measurable_feedback
    (fun a b hab ↦ IsAlgEnvSeq.measurable_feedback_filtrationAction_lt
      h.measurable_action h.measurable_feedback hab) hD (ν k)
    (fun j E hE S hS hSsub ↦ hfact_stationaryEnv h k j hE hS hSsub) hDinf

/-- **Doob optional skipping (identical distribution).** Each response sampled at a pull of arm `k`
has law `ν k`. Together with `iIndepFun_sampledResponse` this says the sampled responses are i.i.d.
with the arm's reward law. (Blueprint `lem:opt_skip`.) -/
theorem map_sampledResponse_eq {Y : ℕ → Ω → ℝ} (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) μ)
    (k : 𝓐) (hk_inf : ∀ᵐ ω ∂μ, {j | A j ω = k}.Infinite) (m : ℕ) :
    μ.map (sampledSeq Y (armIndicator A k) m) = ν k := by
  set 𝒢 := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback with h𝒢
  haveI : IsProbabilityMeasure (ν k) := IsMarkovKernel.isProbabilityMeasure k
  have hDinf : ∀ᵐ ω ∂μ, {j | armIndicator A k j ω = 1}.Infinite := by
    filter_upwards [hk_inf] with ω hω
    rwa [Set.ext (fun j ↦ armIndicator_eq_one_iff)]
  have hD : ∀ i, Measurable[𝒢 i] (armIndicator A k i) := by
    intro i
    have hset : MeasurableSet[𝒢 i] {ω | A i ω = k} :=
      (IsAlgEnvSeq.measurable_action_filtrationAction' h.measurable_action h.measurable_feedback i)
        (measurableSet_singleton k)
    exact Measurable.ite hset measurable_const measurable_const
  exact map_sampledSeq_eq h.measurable_feedback
    (fun a b hab ↦ IsAlgEnvSeq.measurable_feedback_filtrationAction_lt
      h.measurable_action h.measurable_feedback hab) hD (ν k)
    (fun j E hE S hS hSsub ↦ hfact_stationaryEnv h k j hE hS hSsub) hDinf m

end AlphaRAR
