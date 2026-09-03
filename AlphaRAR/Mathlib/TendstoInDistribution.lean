/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.CramerWold
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.HasLaw

/-!
# Convergence in distribution: complements to Mathlib

Small additions to Mathlib's `TendstoInDistribution` API, used by the central limit theorems of
this project. All limits in the project are stated as
`TendstoInDistribution X atTop id (fun _ ↦ P) ν` with `ν` the limit law (a Gaussian): the identity
on `(E, ν)` is a random variable with law `ν`.

* `TendstoInDistribution.congr'`: change the sequence eventually (a.e. at each index) and the
  limit a.e.; Mathlib's `TendstoInDistribution.congr` asks for the change at every index.
* `TendstoInDistribution.comp`: precompose with a subsequence, or any map tending to the filter.
* `tendstoInDistribution_id_iff`: convergence to a random variable `Z` is convergence to the
  identity on the law of `Z`. This is how a limit named by a variable (Mathlib's
  `HasLaw Y (gaussianReal 0 σ²) P'`) and a limit named by its law are exchanged.
* `TendstoInDistribution.mul_of_tendstoInMeasure_const`: Slutsky for a product, the multiplicative
  twin of Mathlib's `TendstoInDistribution.add_of_tendstoInMeasure_const`.
* `tendstoInDistribution_of_forall_inner`: the Cramér–Wold device (one direction) for
  `TendstoInDistribution`, from the vendored `tendsto_map_of_tendsto_map_inner`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace AlphaRAR

variable {ι Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]
  {l : Filter ι} {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- **Congruence for convergence in distribution**, with the sequence changed only eventually:
if `X i = Y i` a.e. for all large `i`, `Z = T` a.e., and every `Y i` is a.e.-measurable, then
`X i → Z` in distribution gives `Y i → T` in distribution. Mathlib's `TendstoInDistribution.congr`
asks for `X i = Y i` at every index. -/
lemma _root_.MeasureTheory.TendstoInDistribution.congr' {X Y : ι → Ω → E} {Z T : Ω' → E}
    (hXY : ∀ᶠ i in l, X i =ᵐ[μ i] Y i) (hZT : Z =ᵐ[μ'] T) (hY : ∀ i, AEMeasurable (Y i) (μ i))
    (h : TendstoInDistribution X l Z μ μ') : TendstoInDistribution Y l T μ μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    have ht := h.tendsto
    rw [show (⟨μ'.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩ :
          ProbabilityMeasure E)
        = ⟨μ'.map T, Measure.isProbabilityMeasure_map (h.aemeasurable_limit.congr hZT)⟩ from
        Subtype.ext (Measure.map_congr hZT)] at ht
    refine ht.congr' ?_
    filter_upwards [hXY] with i hi
    exact Subtype.ext (Measure.map_congr hi)

/-- **Convergence in distribution along a subsequence**: precomposing with any `c` tending to the
filter (a subsequence, for `atTop`) preserves convergence in distribution. -/
lemma _root_.MeasureTheory.TendstoInDistribution.comp {X : ι → Ω → E} {Z : Ω' → E}
    {κ : Type*} {v : Filter κ} {c : κ → ι}
    (h : TendstoInDistribution X l Z μ μ') (hc : Tendsto c v l) :
    TendstoInDistribution (fun k ↦ X (c k)) v Z (fun k ↦ μ (c k)) μ' where
  forall_aemeasurable k := h.forall_aemeasurable (c k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hc

/-- **A limit can be named by a variable or by its law**: `X i → Z` in distribution exactly when
`X i → id` in distribution on the law `ν` of `Z`. -/
lemma tendstoInDistribution_id_iff {X : ι → Ω → E} {Z : Ω' → E} {ν : Measure E}
    [IsProbabilityMeasure ν] (hZ : HasLaw Z ν μ') :
    TendstoInDistribution X l id μ ν ↔ TendstoInDistribution X l Z μ μ' := by
  have hlim : (⟨ν.map id, Measure.isProbabilityMeasure_map aemeasurable_id⟩ : ProbabilityMeasure E)
      = ⟨μ'.map Z, Measure.isProbabilityMeasure_map hZ.aemeasurable⟩ :=
    Subtype.ext (show ν.map id = μ'.map Z by rw [Measure.map_id, hZ.map_eq])
  constructor
  · intro h
    refine ⟨h.forall_aemeasurable, hZ.aemeasurable, ?_⟩
    have ht := h.tendsto
    rwa [hlim] at ht
  · intro h
    refine ⟨h.forall_aemeasurable, aemeasurable_id, ?_⟩
    have ht := h.tendsto
    rwa [← hlim] at ht

/-- **Slutsky's theorem for a product**: if `X n → Z` in distribution and `Y n → c` in
probability, then `X n * Y n → Z * c` in distribution. The multiplicative twin of Mathlib's
`TendstoInDistribution.add_of_tendstoInMeasure_const`. -/
lemma _root_.MeasureTheory.TendstoInDistribution.mul_of_tendstoInMeasure_const
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    [l.IsCountablyGenerated] {X Y : ι → Ω'' → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY_tendsto : TendstoInMeasure μ'' Y l (fun _ ↦ c)) (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω ↦ X n ω * Y n ω) l (fun ω ↦ Z ω * c) (fun _ ↦ μ'') μ' :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const (g := fun p : ℝ × ℝ ↦ p.1 * p.2)
    (by fun_prop) hY_tendsto hY

open scoped RealInnerProductSpace in
/-- **Cramér–Wold device (one direction) for `TendstoInDistribution`**: if every scalar projection
`⟪Xn n, t⟫` converges in distribution to `⟪X, t⟫`, then `Xn` converges in distribution to `X`.
This is the vendored `tendsto_map_of_tendsto_map_inner` restated for random variables. -/
lemma tendstoInDistribution_of_forall_inner {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Xn : ℕ → Ω → F} {X : Ω' → F} (hXn : ∀ n, Measurable (Xn n)) (hX : Measurable X)
    (h : ∀ t : F, TendstoInDistribution (fun n ω ↦ ⟪Xn n ω, t⟫) atTop (fun ω ↦ ⟪X ω, t⟫)
      (fun _ ↦ P) Q) :
    TendstoInDistribution Xn atTop X (fun _ ↦ P) Q where
  forall_aemeasurable n := (hXn n).aemeasurable
  aemeasurable_limit := hX.aemeasurable
  tendsto := tendsto_map_of_tendsto_map_inner (P := ⟨P, inferInstance⟩) (Q := ⟨Q, inferInstance⟩)
    hX hXn fun t ↦ (h t).tendsto

end AlphaRAR
