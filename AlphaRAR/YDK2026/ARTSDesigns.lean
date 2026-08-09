/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.ARTSAlgorithm
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public meta import LeanSpec

/-!
# Example designs in the aRTS family

This file records the concrete example designs of Section 3.1 (blueprint Chapter `chap:design`) and
verifies that each belongs to the aRTS family, i.e. satisfies the throttling condition `IsARTS`.

The shared plumbing is a generic construction of an `Algorithm` from a measurable, history-dependent
*probability-vector* function `p : (n) → (Iic n → 𝓐 × ℝ) → 𝓐 → ℝ`:

* `AlphaRAR.probVecKernel`: the Markov kernel `x ↦ ∑ₐ p(x,a) δₐ` on a finite action space.
* `AlphaRAR.aRTSAlgorithmOfProb`: packages such a `p` (measurable, a probability vector, and
  satisfying the throttle) into an `Algorithm` together with a proof that it `IsARTS`.

Each concrete design (`distanceProb`, `eradeProb`, `dTrackingProb`) is then a probability-vector
function whose simplex property and throttle inequality are pure arithmetic on the design formula.

## Main results

* `AlphaRAR.distanceAlgorithm`, `AlphaRAR.distance_isARTS`;
* `AlphaRAR.eradeAlgorithm`, `AlphaRAR.erade_isARTS`;
* `AlphaRAR.dTrackingAlgorithm`, `AlphaRAR.dTracking_isARTS`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Finset
open scoped ENNReal NNReal

namespace AlphaRAR

section ProbVecKernel

variable {X 𝓐 : Type*} [MeasurableSpace X] [Fintype 𝓐] [MeasurableSpace 𝓐]
  [MeasurableSingletonClass 𝓐]

/-- The kernel `x ↦ ∑ₐ p(x,a) δₐ` built from a measurable probability-vector function
`p : X → 𝓐 → ℝ` on a finite action space `𝓐`. When `p x` is a genuine probability vector
(nonnegative, summing to `1`) this is a Markov kernel (`probVecKernel.isMarkovKernel`). -/
noncomputable def probVecKernel (p : X → 𝓐 → ℝ) (hp : ∀ a, Measurable fun x ↦ p x a) :
    Kernel X 𝓐 where
  toFun x := ∑ a, ENNReal.ofReal (p x a) • Measure.dirac a
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun a _ ↦ (hp a).ennreal_ofReal.mul_const _

omit [MeasurableSingletonClass 𝓐] in
lemma probVecKernel_apply (p : X → 𝓐 → ℝ) (hp : ∀ a, Measurable fun x ↦ p x a) (x : X) :
    probVecKernel p hp x = ∑ a, ENNReal.ofReal (p x a) • Measure.dirac a := rfl

/-- The mass the kernel puts on a single arm `k` is `p x k` (for `p x k ≥ 0`). -/
@[specifies probVecKernel "the kernel really samples from `p`: the mass it assigns to each arm is \
that arm's coordinate, with the `ℝ≥0∞` round-trip doing nothing on nonnegative inputs"]
lemma probVecKernel_apply_singleton (p : X → 𝓐 → ℝ) (hp : ∀ a, Measurable fun x ↦ p x a) (x : X)
    (k : 𝓐) (hnn : 0 ≤ p x k) : (probVecKernel p hp x {k}).toReal = p x k := by
  rw [probVecKernel_apply, Measure.finsetSum_apply]
  have hzero : ∀ a ∈ (univ : Finset 𝓐), a ≠ k →
      (ENNReal.ofReal (p x a) • Measure.dirac a) {k} = 0 := by
    intro a _ hak
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton k),
      Set.indicator_of_notMem (by simpa using hak), mul_zero]
  rw [Finset.sum_eq_single_of_mem k (mem_univ k) hzero, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' k (measurableSet_singleton k),
    Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl), Pi.one_apply, mul_one,
    ENNReal.toReal_ofReal hnn]

omit [MeasurableSingletonClass 𝓐] in
/-- When `p x` is a probability vector, `probVecKernel p hp` is a Markov kernel. -/
@[specifies probVecKernel "the construction is total — it accepts any measurable `p` — but is a \
*Markov* kernel exactly under the simplex conditions, which is why every design below has to prove \
its `_nonneg` and `_sum` lemmas"]
lemma probVecKernel.isMarkovKernel (p : X → 𝓐 → ℝ) (hp : ∀ a, Measurable fun x ↦ p x a)
    (hnn : ∀ x a, 0 ≤ p x a) (hsum : ∀ x, ∑ a, p x a = 1) :
    IsMarkovKernel (probVecKernel p hp) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  rw [probVecKernel_apply, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, MeasureTheory.measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hnn x a, hsum x, ENNReal.ofReal_one]

end ProbVecKernel

section HistMeasurable

variable {𝓐 : Type*} [Finite 𝓐] [DecidableEq 𝓐] [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐]

/-- The history-level plug-in target coordinate is measurable in the history (continuous `T`). -/
lemma measurable_histTarget (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (k : 𝓐)
    (n : ℕ) : Measurable fun h : Iic n → 𝓐 × ℝ ↦ histTarget θ₀ T k n h := by
  cases nonempty_fintype 𝓐
  simp only [histTarget]
  refine (measurable_pi_apply k).comp (hT.measurable.comp (measurable_pi_lambda _ fun k' ↦ ?_))
  refine ((measurable_sumRewards' n k').add_const (θ₀ k')).div ?_
  exact (measurable_from_top.comp (measurable_pullCount' n k')).add_const 1

end HistMeasurable

section ARTSDesign

variable {𝓐 : Type*} [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐]
  [Nonempty 𝓐]

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- The history-level counts sum to the number `n + 1` of observed samples. -/
lemma sum_pullCount' (n : ℕ) (h : Iic n → 𝓐 × ℝ) : ∑ a, pullCount' n h a = n + 1 := by
  simp_rw [pullCount'_eq_sum]
  rw [Finset.sum_comm]
  have hcol : ∀ s : Iic n, ∑ a, (if (h s).1 = a then (1 : ℕ) else 0) = 1 := by
    intro s
    rw [Finset.sum_ite_eq univ (h s).1 (fun _ ↦ (1 : ℕ))]
    simp
  simp_rw [hcol]
  simp [Nat.card_Iic]

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- The history-level plug-in target is a probability vector: it sums to `1` (as `T` is
simplex-valued, `hTsum`). -/
lemma sum_histTarget (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTsum : ∀ z, ∑ k, T z k = 1)
    (n : ℕ) (h : Iic n → 𝓐 × ℝ) : ∑ k, histTarget θ₀ T k n h = 1 := by
  simp only [histTarget]
  exact hTsum _


/-- The `Algorithm` whose policy at each step draws the next arm from the history-dependent
probability vector `p n h`, and whose first action is an arbitrary point mass (the burn-in plays no
role, cf. blueprint `rem:burnin`). Requires `p n h` to be measurable in `h` and a probability
vector. -/
noncomputable def aRTSAlgorithmOfProb (p : (n : ℕ) → (Iic n → 𝓐 × ℝ) → 𝓐 → ℝ)
    (hp : ∀ n a, Measurable fun h ↦ p n h a) (hnn : ∀ n h a, 0 ≤ p n h a)
    (hsum : ∀ n h, ∑ a, p n h a = 1) : Algorithm 𝓐 ℝ where
  policy n := probVecKernel (p n) (hp n)
  h_policy := fun n ↦ probVecKernel.isMarkovKernel (p n) (hp n) (hnn n) (hsum n)
  p0 := Measure.dirac (Classical.arbitrary 𝓐)

/-- **The throttle characterisation of the aRTS family.** If the design's probability vector `p`
throttles every over-sampled arm --- `(n+1)ρ̂_k < N_k ⟹ p_k ≤ α ρ̂_k` --- then the algorithm it
builds belongs to the aRTS family (`IsARTS`). This reduces verifying `IsARTS` for a concrete design
to the pure arithmetic of its throttle inequality (`probVecKernel_apply_singleton` identifies the
policy mass on arm `k` with `p n h k`). -/
@[specifies aRTSAlgorithmOfProb "the packaging is faithful: the algorithm's policy assigns arm `k` \
exactly the mass `p n h k`, so a throttle proved for the probability vector holds verbatim for the \
algorithm. This is what makes the burn-in `p0` irrelevant to membership in the family"]
lemma aRTSAlgorithmOfProb_isARTS (p : (n : ℕ) → (Iic n → 𝓐 × ℝ) → 𝓐 → ℝ)
    (hp : ∀ n a, Measurable fun h ↦ p n h a) (hnn : ∀ n h a, 0 ≤ p n h a)
    (hsum : ∀ n h, ∑ a, p n h a = 1) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (α : ℝ)
    (hthrottle : ∀ (n : ℕ) (h : Iic n → 𝓐 × ℝ) (k : 𝓐),
      ((n : ℝ) + 1) * histTarget θ₀ T k n h < (pullCount' n h k : ℝ) →
        p n h k ≤ α * histTarget θ₀ T k n h) :
    IsARTS (aRTSAlgorithmOfProb p hp hnn hsum) θ₀ T α where
  throttle n h k hover := by
    rw [show (aRTSAlgorithmOfProb p hp hnn hsum).policy n = probVecKernel (p n) (hp n) from rfl,
      probVecKernel_apply_singleton (p n) (hp n) h k (hnn n h k)]
    exact hthrottle n h k hover

/-- The empirical allocation proportion `N_{n+1,k}/(n+1)` as a function of the history. -/
noncomputable def histProp (n : ℕ) (h : Iic n → 𝓐 × ℝ) (k : 𝓐) : ℝ :=
  (pullCount' n h k : ℝ) / ((n : ℝ) + 1)

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- The allocation proportions sum to `1`. -/
@[specifies histProp "the denominator `n+1` is the right one: it is exactly the number of patients \
seen in a history indexed by `Iic n`, so the proportions form a probability vector and are \
directly comparable with the simplex-valued target `histTarget`"]
lemma sum_histProp (n : ℕ) (h : Iic n → 𝓐 × ℝ) : ∑ k, histProp n h k = 1 := by
  simp only [histProp, ← Finset.sum_div]
  rw [show (∑ k, (pullCount' n h k : ℝ)) = ((n : ℝ) + 1) by
    rw [← Nat.cast_sum, sum_pullCount']; push_cast; ring]
  rw [div_self (by positivity)]

omit [Fintype 𝓐] [Nonempty 𝓐] in
lemma measurable_histProp (k : 𝓐) (n : ℕ) :
    Measurable fun h : Iic n → 𝓐 × ℝ ↦ histProp n h k := by
  simp only [histProp]
  exact (measurable_from_top.comp (measurable_pullCount' n k)).div_const _

/-! ### Distance-based design (blueprint `def:distance_design`) -/

/-- The **distance-based** design's probability vector: `p_k = α ρ̂_k + (1-α) δ_k / (∑_i δ_i)` with
under-sampling deficit `δ_k = max(0, ρ̂_k - N_k/(n+1))`, degenerating to `ρ̂_k` when `∑ δ = 0`. -/
noncomputable def distanceProb (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (α : ℝ) (n : ℕ)
    (h : Iic n → 𝓐 × ℝ) (k : 𝓐) : ℝ :=
  haveI : Decidable (∑ i, max 0 (histTarget θ₀ T i n h - histProp n h i) = 0) := Classical.dec _
  if ∑ i, max 0 (histTarget θ₀ T i n h - histProp n h i) = 0 then histTarget θ₀ T k n h
  else α * histTarget θ₀ T k n h
    + (1 - α) * (max 0 (histTarget θ₀ T k n h - histProp n h k)
      / ∑ i, max 0 (histTarget θ₀ T i n h - histProp n h i))

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- Each distance-based probability is nonnegative. -/
lemma distanceProb_nonneg (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTnn : ∀ z k, 0 ≤ T z k)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (h : Iic n → 𝓐 × ℝ) (k : 𝓐) :
    0 ≤ distanceProb θ₀ T α n h k := by
  have hρnn : 0 ≤ histTarget θ₀ T k n h := by simp only [histTarget]; exact hTnn _ _
  have hSnn : 0 ≤ ∑ i, max 0 (histTarget θ₀ T i n h - histProp n h i) :=
    Finset.sum_nonneg fun i _ ↦ le_max_left _ _
  simp only [distanceProb]
  split_ifs with hS
  · exact hρnn
  · have h1 : 0 ≤ α * histTarget θ₀ T k n h := mul_nonneg hα.1 hρnn
    have h2 : 0 ≤ (1 - α) * (max 0 (histTarget θ₀ T k n h - histProp n h k)
        / ∑ i, max 0 (histTarget θ₀ T i n h - histProp n h i)) :=
      mul_nonneg (by linarith [hα.2]) (div_nonneg (le_max_left _ _) hSnn)
    linarith

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- **Distance-based is a valid probability vector** (blueprint `lem:distance_simplex`). -/
@[specifies distanceProb "with `distanceProb_nonneg`, the design is a genuine randomization rule; \
in particular the degenerate branch `∑ δ = 0` was given the right fallback value `ρ̂_k`, which is \
the one choice that keeps the total mass at `1`"]
lemma distanceProb_sum (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (n : ℕ) (h : Iic n → 𝓐 × ℝ) : ∑ k, distanceProb θ₀ T α n h k = 1 := by
  simp only [distanceProb]
  split_ifs with hS
  · exact sum_histTarget θ₀ hTsum n h
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_histTarget θ₀ hTsum n h, mul_one,
      ← Finset.mul_sum, ← Finset.sum_div, div_self hS, mul_one]
    ring

omit [Nonempty 𝓐] in
/-- Measurability of the distance-based probability in the history. -/
lemma measurable_distanceProb (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (α : ℝ)
    (n : ℕ) (k : 𝓐) : Measurable fun h : Iic n → 𝓐 × ℝ ↦ distanceProb θ₀ T α n h k := by
  classical
  have hρ : ∀ i, Measurable fun h : Iic n → 𝓐 × ℝ ↦ histTarget θ₀ T i n h :=
    fun i ↦ measurable_histTarget θ₀ hT i n
  have hδ : ∀ i, Measurable fun h : Iic n → 𝓐 × ℝ ↦
      max 0 (histTarget θ₀ T i n h - histProp n h i) :=
    fun i ↦ measurable_const.max ((hρ i).sub (measurable_histProp i n))
  have hS : Measurable fun h : Iic n → 𝓐 × ℝ ↦
      ∑ i, max 0 (histTarget θ₀ T i n h - histProp n h i) := Finset.measurable_sum _ fun i _ ↦ hδ i
  simp only [distanceProb]
  refine Measurable.ite (measurableSet_eq_fun hS measurable_const) (hρ k) ?_
  exact ((measurable_const.mul (hρ k)).add
    (measurable_const.mul ((hδ k).div hS)))

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- **Distance-based is aRTS** (blueprint `lem:distance_isARTS`): when arm `k` is over-sampled its
deficit vanishes, forcing `p_k = α ρ̂_k`; the mixing normaliser is positive because some *other* arm
is then under-sampled (the deficits sum to `0` and are nonnegative after the `max`). -/
@[specifies distanceProb "the design's membership in the aRTS family: the `max 0 (·)` deficit is \
what makes an over-sampled arm receive none of the exploration mass, so its probability collapses \
to the throttled `α ρ̂_k`"]
lemma distanceProb_throttle (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (n : ℕ) (h : Iic n → 𝓐 × ℝ) (k : 𝓐)
    (hover : ((n : ℝ) + 1) * histTarget θ₀ T k n h < (pullCount' n h k : ℝ)) :
    distanceProb θ₀ T α n h k ≤ α * histTarget θ₀ T k n h := by
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : histTarget θ₀ T k n h < histProp n h k := by
    rw [histProp, lt_div_iff₀ hnp]; linarith [hover]
  have hδk : max 0 (histTarget θ₀ T k n h - histProp n h k) = 0 := by
    rw [max_eq_left]; linarith
  have hsum0 : ∑ i, (histProp n h i - histTarget θ₀ T i n h) = 0 := by
    rw [Finset.sum_sub_distrib, sum_histProp, sum_histTarget θ₀ hTsum]; ring
  have hSpos : 0 < ∑ i, max 0 (histTarget θ₀ T i n h - histProp n h i) := by
    obtain ⟨j, _, hj⟩ : ∃ j ∈ Finset.univ, histProp n h j - histTarget θ₀ T j n h < 0 := by
      by_contra hcon
      push Not at hcon
      have hpos : 0 < ∑ i, (histProp n h i - histTarget θ₀ T i n h) :=
        Finset.sum_pos' (fun i _ ↦ hcon i (Finset.mem_univ i))
          ⟨k, Finset.mem_univ k, by linarith⟩
      linarith
    refine Finset.sum_pos' (fun i _ ↦ le_max_left _ _) ⟨j, Finset.mem_univ j, ?_⟩
    rw [lt_max_iff]; right; linarith
  refine le_of_eq ?_
  simp only [distanceProb, if_neg hSpos.ne', hδk, zero_div, mul_zero, add_zero]

/-- The **distance-based** aRTS design as an `Algorithm` (blueprint `def:distance_design`). -/
noncomputable def distanceAlgorithm (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) : Algorithm 𝓐 ℝ :=
  aRTSAlgorithmOfProb (distanceProb θ₀ T α) (fun n k ↦ measurable_distanceProb θ₀ hT α n k)
    (fun n h a ↦ distanceProb_nonneg θ₀ hTnn hα n h a) (fun n h ↦ distanceProb_sum θ₀ hTsum α n h)

/-- **The distance-based design belongs to the aRTS family** (blueprint `lem:distance_isARTS`). -/
@[specifies distanceAlgorithm "the only thing the packaged algorithm has to be: a member of the \
aRTS family, so that every result of the chapter applies to it"]
lemma distance_isARTS (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    IsARTS (distanceAlgorithm θ₀ hT hTnn hTsum hα) θ₀ T α :=
  aRTSAlgorithmOfProb_isARTS (distanceProb θ₀ T α) _ _ _ θ₀ T α
    (fun n h k hover ↦ distanceProb_throttle θ₀ hTsum α n h k hover)

/-! ### ERADE 2025 design (blueprint `def:erade2025`) -/

/-- The **ERADE 2025** design's probability vector: over-sampled arms are throttled to `α ρ̂_k`,
arms at their target keep `ρ̂_k`, and each under-sampled arm receives `ρ̂_k` plus an equal share
`(1-α)(∑_{over} ρ̂_j)/|under|` of the mass freed from the over-sampled arms. -/
noncomputable def eradeProb (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (α : ℝ) (n : ℕ)
    (h : Iic n → 𝓐 × ℝ) (k : 𝓐) : ℝ :=
  letI : DecidablePred fun j : 𝓐 ↦ histTarget θ₀ T j n h < histProp n h j := fun _ ↦ Classical.dec _
  letI : DecidablePred fun j : 𝓐 ↦ histProp n h j < histTarget θ₀ T j n h := fun _ ↦ Classical.dec _
  if histTarget θ₀ T k n h < histProp n h k then α * histTarget θ₀ T k n h
  else if histProp n h k < histTarget θ₀ T k n h then
    histTarget θ₀ T k n h + (1 - α)
      * ((∑ j, if histTarget θ₀ T j n h < histProp n h j then histTarget θ₀ T j n h else 0)
        / ∑ j, if histProp n h j < histTarget θ₀ T j n h then (1 : ℝ) else 0)
  else histTarget θ₀ T k n h

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- Each ERADE probability is nonnegative. -/
lemma eradeProb_nonneg (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTnn : ∀ z k, 0 ≤ T z k)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (h : Iic n → 𝓐 × ℝ) (k : 𝓐) :
    0 ≤ eradeProb θ₀ T α n h k := by
  have hρnn : ∀ i, 0 ≤ histTarget θ₀ T i n h := fun i ↦ by simp only [histTarget]; exact hTnn _ _
  simp only [eradeProb]
  split_ifs with h1 h2
  · exact mul_nonneg hα.1 (hρnn k)
  · refine add_nonneg (hρnn k) (mul_nonneg (by linarith [hα.2]) (div_nonneg ?_ ?_))
    · exact Finset.sum_nonneg fun j _ ↦ by split_ifs; exacts [hρnn j, le_refl 0]
    · exact Finset.sum_nonneg fun j _ ↦ by split_ifs; exacts [zero_le_one, le_refl 0]
  · exact hρnn k

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- **ERADE 2025 is a valid probability vector** (blueprint `lem:erade2025_simplex`). -/
@[specifies eradeProb "the redistribution is exactly mass-preserving: the `(1-α)` taken from the \
over-sampled arms is precisely what the equal shares hand to the under-sampled ones, and the arms \
sitting at their target are left alone"]
lemma eradeProb_sum (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (n : ℕ) (h : Iic n → 𝓐 × ℝ) : ∑ k, eradeProb θ₀ T α n h k = 1 := by
  classical
  set A := ∑ j, if histTarget θ₀ T j n h < histProp n h j then histTarget θ₀ T j n h else 0
    with hAdef
  set Tc := ∑ j, if histProp n h j < histTarget θ₀ T j n h then (1 : ℝ) else 0 with hTcdef
  have hpk : ∀ k, eradeProb θ₀ T α n h k = histTarget θ₀ T k n h
      + (if histTarget θ₀ T k n h < histProp n h k then (α - 1) * histTarget θ₀ T k n h else 0)
      + (if histProp n h k < histTarget θ₀ T k n h then (1 - α) * A / Tc else 0) := by
    intro k
    simp only [eradeProb, ← hAdef, ← hTcdef]
    by_cases hover : histTarget θ₀ T k n h < histProp n h k
    · rw [if_pos hover, if_pos hover, if_neg (not_lt.mpr hover.le)]; ring
    · rw [if_neg hover, if_neg hover]
      by_cases hunder : histProp n h k < histTarget θ₀ T k n h
      · rw [if_pos hunder, if_pos hunder]; ring
      · rw [if_neg hunder, if_neg hunder]; ring
  have hover_sum :
      (∑ k, if histTarget θ₀ T k n h < histProp n h k then (α - 1) * histTarget θ₀ T k n h else 0)
        = (α - 1) * A := by
    rw [hAdef, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> ring
  have hunder_sum :
      (∑ k, if histProp n h k < histTarget θ₀ T k n h then (1 - α) * A / Tc else 0)
        = Tc * ((1 - α) * A / Tc) := by
    rw [hTcdef, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ ↦ hpk k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    hover_sum, hunder_sum, sum_histTarget θ₀ hTsum n h]
  by_cases hTc0 : Tc = 0
  · -- No arm is under-sampled, so (by mass conservation) no arm is over-sampled and `A = 0`.
    have hA0 : A = 0 := by
      have hnn : ∀ i ∈ (univ : Finset 𝓐),
          (0 : ℝ) ≤ if histProp n h i < histTarget θ₀ T i n h then (1 : ℝ) else 0 :=
        fun i _ ↦ by split_ifs <;> norm_num
      have hTcsum : (∑ j, if histProp n h j < histTarget θ₀ T j n h then (1 : ℝ) else 0) = 0 := by
        rw [← hTcdef]; exact hTc0
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hTcsum
      have hge : ∀ j, histTarget θ₀ T j n h ≤ histProp n h j := by
        intro j
        by_contra hj
        have := hall j (mem_univ j)
        rw [if_pos (not_le.mp hj)] at this
        exact one_ne_zero this
      have hzero : ∑ j, (histProp n h j - histTarget θ₀ T j n h) = 0 := by
        rw [Finset.sum_sub_distrib, sum_histProp, sum_histTarget θ₀ hTsum]; ring
      have heq : ∀ j, histProp n h j = histTarget θ₀ T j n h := by
        intro j
        have hnn' : ∀ i ∈ (univ : Finset 𝓐),
            (0 : ℝ) ≤ histProp n h i - histTarget θ₀ T i n h := fun i _ ↦ by linarith [hge i]
        linarith [(Finset.sum_eq_zero_iff_of_nonneg hnn').mp hzero j (mem_univ j)]
      rw [hAdef]
      exact Finset.sum_eq_zero fun j _ ↦ if_neg (by rw [heq j]; exact lt_irrefl _)
    rw [hTc0, hA0]; ring
  · rw [mul_comm Tc, div_mul_cancel₀ _ hTc0]; ring

omit [Nonempty 𝓐] in
/-- Measurability of the ERADE probability in the history. -/
lemma measurable_eradeProb (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (α : ℝ)
    (n : ℕ) (k : 𝓐) : Measurable fun h : Iic n → 𝓐 × ℝ ↦ eradeProb θ₀ T α n h k := by
  classical
  have hρ : ∀ i, Measurable fun h : Iic n → 𝓐 × ℝ ↦ histTarget θ₀ T i n h :=
    fun i ↦ measurable_histTarget θ₀ hT i n
  have hq : ∀ i, Measurable fun h : Iic n → 𝓐 × ℝ ↦ histProp n h i :=
    fun i ↦ measurable_histProp i n
  have hA : Measurable fun h : Iic n → 𝓐 × ℝ ↦
      ∑ j, if histTarget θ₀ T j n h < histProp n h j then histTarget θ₀ T j n h else 0 :=
    Finset.measurable_sum _ fun j _ ↦
      Measurable.ite (measurableSet_lt (hρ j) (hq j)) (hρ j) measurable_const
  have hTc : Measurable fun h : Iic n → 𝓐 × ℝ ↦
      ∑ j, if histProp n h j < histTarget θ₀ T j n h then (1 : ℝ) else 0 :=
    Finset.measurable_sum _ fun j _ ↦
      Measurable.ite (measurableSet_lt (hq j) (hρ j)) measurable_const measurable_const
  simp only [eradeProb]
  refine Measurable.ite (measurableSet_lt (hρ k) (hq k)) (measurable_const.mul (hρ k)) ?_
  exact Measurable.ite (measurableSet_lt (hq k) (hρ k))
    ((hρ k).add (measurable_const.mul (hA.div hTc))) (hρ k)

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- **ERADE 2025 is aRTS** (blueprint `lem:erade2025_isARTS`): an over-sampled arm gets exactly
`p_k = α ρ̂_k`. -/
@[specifies eradeProb "the design's membership in the aRTS family, and it confirms the branch \
condition `ρ̂_k < N_k/(n+1)` is the same over-sampling test `IsARTS` uses"]
lemma eradeProb_throttle (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (α : ℝ) (n : ℕ) (h : Iic n → 𝓐 × ℝ)
    (k : 𝓐) (hover : ((n : ℝ) + 1) * histTarget θ₀ T k n h < (pullCount' n h k : ℝ)) :
    eradeProb θ₀ T α n h k ≤ α * histTarget θ₀ T k n h := by
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : histTarget θ₀ T k n h < histProp n h k := by
    rw [histProp, lt_div_iff₀ hnp]; linarith
  refine le_of_eq ?_
  simp only [eradeProb, if_pos hlt]

/-- The **ERADE 2025** aRTS design as an `Algorithm` (blueprint `def:erade2025`). -/
noncomputable def eradeAlgorithm (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) : Algorithm 𝓐 ℝ :=
  aRTSAlgorithmOfProb (eradeProb θ₀ T α) (fun n k ↦ measurable_eradeProb θ₀ hT α n k)
    (fun n h a ↦ eradeProb_nonneg θ₀ hTnn hα n h a) (fun n h ↦ eradeProb_sum θ₀ hTsum α n h)

/-- **The ERADE 2025 design belongs to the aRTS family** (blueprint `lem:erade2025_isARTS`). -/
@[specifies eradeAlgorithm "the only thing the packaged algorithm has to be: a member of the aRTS \
family, so that every result of the chapter applies to it"]
lemma erade_isARTS (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    IsARTS (eradeAlgorithm θ₀ hT hTnn hTsum hα) θ₀ T α :=
  aRTSAlgorithmOfProb_isARTS (eradeProb θ₀ T α) _ _ _ θ₀ T α
    (fun n h k hover ↦ eradeProb_throttle θ₀ α n h k hover)

/-! ### Interpolated D-Tracking design (blueprint `def:d_tracking`) -/

/-- The deficit `m ρ̂_{m,a} - N_{m,a}` (with `m = n+1`) of arm `a` relative to its target: the
amount by which it is under-allocated. The most under-sampled arm (largest deficit) is favoured. -/
noncomputable def dtDeficit (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (n : ℕ) (h : Iic n → 𝓐 × ℝ)
    (a : 𝓐) : ℝ :=
  ((n : ℝ) + 1) * histTarget θ₀ T a n h - (pullCount' n h a : ℝ)

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] in
/-- **The deficits sum to zero**: the targets form a probability vector and the counts sum to
`n+1`, so over-allocation on some arms is exactly balanced by under-allocation on others. -/
@[specifies dtDeficit "fixes the sign convention and the normalisation together: a *positive* \
deficit means under-allocated, and since the total is `0` there is always an arm with deficit \
`≥ 0` — which is why the arm of maximal deficit is never an over-sampled one"]
lemma sum_dtDeficit (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTsum : ∀ z, ∑ k, T z k = 1)
    (n : ℕ) (h : Iic n → 𝓐 × ℝ) : ∑ a, dtDeficit θ₀ T n h a = 0 := by
  simp only [dtDeficit, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_histTarget θ₀ hTsum]
  rw [show (∑ a, (pullCount' n h a : ℝ)) = ((n : ℝ) + 1) by
    rw [← Nat.cast_sum, sum_pullCount']; push_cast; ring]
  ring

/-- The **Interpolated D-Tracking** design's probability vector: `p_k = α ρ̂_k + (1-α) 𝟙{k = k⋆}`,
where `k⋆` is the arm of maximal deficit `m ρ̂_{m,a} - N_{m,a}` (the most under-sampled arm). -/
noncomputable def dTrackingProb (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (α : ℝ) (n : ℕ)
    (h : Iic n → 𝓐 × ℝ) (k : 𝓐) : ℝ :=
  α * histTarget θ₀ T k n h
    + (1 - α) * (if k = _root_.argmax (fun a ↦ dtDeficit θ₀ T n h a) then 1 else 0)

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] in
/-- Each D-Tracking probability is nonnegative. -/
lemma dTrackingProb_nonneg (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTnn : ∀ z k, 0 ≤ T z k)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (h : Iic n → 𝓐 × ℝ) (k : 𝓐) :
    0 ≤ dTrackingProb θ₀ T α n h k := by
  have hρnn : 0 ≤ histTarget θ₀ T k n h := by simp only [histTarget]; exact hTnn _ _
  refine add_nonneg (mul_nonneg hα.1 hρnn) (mul_nonneg (by linarith [hα.2]) ?_)
  split_ifs <;> norm_num

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] in
/-- **D-Tracking is a valid probability vector** (blueprint `lem:d_tracking_simplex`). -/
@[specifies dTrackingProb "the `(1-α)` mass is put on *exactly one* arm, so the interpolation \
between the target `ρ̂` and the deterministic tracking choice is mass-preserving"]
lemma dTrackingProb_sum (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (n : ℕ) (h : Iic n → 𝓐 × ℝ) : ∑ k, dTrackingProb θ₀ T α n h k = 1 := by
  simp only [dTrackingProb, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_histTarget θ₀ hTsum n h, mul_one]
  rw [Finset.sum_ite_eq' univ (_root_.argmax (fun a ↦ dtDeficit θ₀ T n h a)) (fun _ ↦ (1 : ℝ))]
  simp only [mem_univ, if_true, mul_one]
  ring

omit [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] in
/-- **Interpolated D-Tracking is aRTS** (blueprint `lem:d_tracking_isARTS`): an over-sampled arm has
negative deficit, while the maximal deficit is `≥ 0` (deficits sum to `0`), so an over-sampled arm
is never the favoured `k⋆` and receives exactly `p_k = α ρ̂_k`. -/
@[specifies dTrackingProb "the design's membership in the aRTS family; it also shows the `argmax` \
tie-breaking is irrelevant, since *no* over-sampled arm can be selected however ties are resolved"]
lemma dTrackingProb_throttle (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (n : ℕ) (h : Iic n → 𝓐 × ℝ) (k : 𝓐)
    (hover : ((n : ℝ) + 1) * histTarget θ₀ T k n h < (pullCount' n h k : ℝ)) :
    dTrackingProb θ₀ T α n h k ≤ α * histTarget θ₀ T k n h := by
  set d := fun a ↦ dtDeficit θ₀ T n h a with hddef
  have hk_neg : d k < 0 := by simp only [hddef, dtDeficit]; linarith
  -- The deficits sum to `0`, so the maximal deficit is `≥ 0`.
  have hdsum : ∑ a, d a = 0 := by rw [hddef]; exact sum_dtDeficit θ₀ hTsum n h
  have hMnn : 0 ≤ d (_root_.argmax d) := by
    obtain ⟨j, hj⟩ : ∃ j, 0 ≤ d j := by
      by_contra hcon
      push Not at hcon
      exact absurd hdsum (Finset.sum_neg (fun i _ ↦ hcon i) univ_nonempty).ne
    exact le_trans hj (isMaxOn_argmax d j)
  have hne : k ≠ _root_.argmax d := fun heq ↦ absurd (heq ▸ hk_neg) (not_lt.mpr hMnn)
  refine le_of_eq ?_
  simp only [dTrackingProb, ← hddef, if_neg hne, mul_zero, add_zero]

/-- Measurability of the D-Tracking probability in the history. -/
lemma measurable_dTrackingProb (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (α : ℝ)
    (n : ℕ) (k : 𝓐) : Measurable fun h : Iic n → 𝓐 × ℝ ↦ dTrackingProb θ₀ T α n h k := by
  have hρ : ∀ i, Measurable fun h : Iic n → 𝓐 × ℝ ↦ histTarget θ₀ T i n h :=
    fun i ↦ measurable_histTarget θ₀ hT i n
  have hdef : Measurable fun h : Iic n → 𝓐 × ℝ ↦ (fun a ↦ dtDeficit θ₀ T n h a) := by
    refine measurable_pi_lambda _ fun a ↦ ?_
    simp only [dtDeficit]
    exact (measurable_const.mul (hρ a)).sub
      (measurable_from_top.comp (measurable_pullCount' n a))
  have hargmax : Measurable fun h : Iic n → 𝓐 × ℝ ↦ _root_.argmax (fun a ↦ dtDeficit θ₀ T n h a) :=
    measurable_argmax.comp hdef
  simp only [dTrackingProb]
  refine (measurable_const.mul (hρ k)).add (measurable_const.mul ?_)
  exact Measurable.ite (measurableSet_eq_fun measurable_const hargmax) measurable_const
    measurable_const

/-- The **Interpolated D-Tracking** aRTS design as an `Algorithm` (blueprint `def:d_tracking`). -/
noncomputable def dTrackingAlgorithm (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) : Algorithm 𝓐 ℝ :=
  aRTSAlgorithmOfProb (dTrackingProb θ₀ T α) (fun n k ↦ measurable_dTrackingProb θ₀ hT α n k)
    (fun n h a ↦ dTrackingProb_nonneg θ₀ hTnn hα n h a) (fun n h ↦ dTrackingProb_sum θ₀ hTsum α n h)

/-- **The Interpolated D-Tracking design belongs to the aRTS family**
(blueprint `lem:d_tracking_isARTS`). -/
@[specifies dTrackingAlgorithm "the only thing the packaged algorithm has to be: a member of the \
aRTS family, so that every result of the chapter applies to it"]
lemma dTracking_isARTS (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    IsARTS (dTrackingAlgorithm θ₀ hT hTnn hTsum hα) θ₀ T α :=
  aRTSAlgorithmOfProb_isARTS (dTrackingProb θ₀ T α) _ _ _ θ₀ T α
    (fun n h k hover ↦ dTrackingProb_throttle θ₀ hTsum α n h k hover)

end ARTSDesign

end AlphaRAR
