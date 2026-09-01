/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.LILLogLog
public import AlphaRAR.Mathlib.LILSharp
public import AlphaRAR.Mathlib.LILTruncation
public import AlphaRAR.Mathlib.MartingaleSLLN
public import AlphaRAR.Mathlib.TsumMeasureIoi
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public meta import LeanSpec

/-!
# The i.i.d. Hartman–Wintner law of the iterated logarithm

This file develops the finite-variance (i.i.d.) case of the loglog LIL (Hartman–Wintner 1941).
A sum of i.i.d. centred increments with only a second moment is split into three levels — low
`|Y|≤b_i`, medium `b_i<|Y|≤√i`, high `|Y|>√i` — with the `log`-level cutoff `b_i = √(i/log(i+2))`.
The main (low) part satisfies the growing-increment hypothesis of `LILLogLog.lean` and gets the
loglog rate; the high part vanishes eventually; the drift and medium parts are `o(√(n log log n))`.

## Main results

* `AlphaRAR.abs_sum_integral_truncation_le`: the drift bound `|∑_{j<m} ∫ trunc(X,√j)| ≤ 2(∫X²)√m`
  for centred `X`, from `abs_integral_truncation_le` and `sum_one_div_sqrt_le`.
* `AlphaRAR.integral_sq_truncation_le`: `∫ trunc(X,A)² ≤ ∫ X²`, the low-part second-moment bound.
* `AlphaRAR.ae_eventually_abs_le_sqrt_of_identDistrib`: the high part vanishes eventually: for
  identically distributed `Y` with finite second moment, a.s. `|Y_j| ≤ √j` for all large `j`.
* `AlphaRAR.natFiltLT`: the "strictly before `n`" natural filtration `σ(Y_0,…,Y_{n-1})`.
* `AlphaRAR.martingale_iidSum`: partial sums of independent centred variables form a martingale for
  `natFiltLT`.
* `AlphaRAR.predQuadVar_iidSum_succ_sub`, `AlphaRAR.predQuadVar_iidSum_le`,
  `AlphaRAR.predQuadVar_iidSum_ge`: the quadratic-variation increment `⟨S⟩_{n+1}-⟨S⟩_n = E[Y_n²]`
  and the two-sided linear bounds `w·n ≤ ⟨S⟩_n ≤ v·n`.
* `AlphaRAR.ae_eventually_abs_sum_le_sqrt_nat_mul_loglog_of_bounded`: the loglog LIL
  `|S_n| = O(√(n log log n))` for bounded independent centred increments with `E[Y_i²] ≥ w > 0`,
  the bounded case of Hartman–Wintner, assembled from the above and the bounded-increment engine
  `ae_eventually_abs_le_sqrt_nat_mul_loglog`.
* The low-part (centred-truncation) ingredients:
  `AlphaRAR.iIndepFun_truncation_sub_const`, `AlphaRAR.martingale_centeredTruncation` (the
  martingale `S̃_n = ∑(Y_j^L - E Y_j^L)`), `AlphaRAR.predQuadVar_centeredTruncation_le`
  (`⟨S̃⟩_n ≤ v·n`),
  `AlphaRAR.abs_truncation_sub_integral_le` (increment bound `|ΔS̃_j| ≤ 2 b_j`), and
  `AlphaRAR.integral_truncation_sub_integral_sq_le` (`Var(Y^L) ≤ σ²`), assembled into the sharp
  low-part LIL `AlphaRAR.ae_eventually_abs_le_sqrt_nat_mul_loglog_centeredTruncation_sharp`.
* `AlphaRAR.medium_variance_summable_seq` and `AlphaRAR.ae_medium_div_weight_tendsto_zero`: the
  medium band has a summable weighted variance series, hence is `o(√(m log log m))`.
* `AlphaRAR.hw_drift_bound`: the deterministic drift bound
  `∑_{j<m}(E Y_j^L + E Y_j^M) ≤ 2σ²√m + E|Y_0|`.
* `AlphaRAR.iid_hartmanWintner_limsup_le_one`: the upper half of the Hartman–Wintner LIL, a.s.
  `limsup_m (∑_{j<m} Y_j) / √(2σ² m log log m) ≤ 1` for i.i.d. centred `L²` increments with
  `σ² = E[Y_0²] > 0` (eventual, coboundedness-free form: `AlphaRAR.hw_eventually`).
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Real

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Drift bound**, the deterministic core. For a centred `X` with `X²` integrable,
`|∑_{j<m} ∫ trunc(X,√j)| ≤ 2 (∫X²) √m`. Each summand is bounded by `(∫X²)/√j`
(`abs_integral_truncation_le`) and `∑_{j<m} 1/√j ≤ 2√m` (`sum_one_div_sqrt_le`). The truncated mean
at level `√j` is `E[X 𝟙_{-√j < X ≤ √j}]`, so this bounds the Hartman–Wintner drift. -/
lemma abs_sum_integral_truncation_le [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX2 : MemLp X 2 μ) (hX0 : ∫ ω, X ω ∂μ = 0) (m : ℕ) :
    |∑ j ∈ Finset.range m, ∫ ω, truncation X (√(j : ℝ)) ω ∂μ|
      ≤ 2 * (∫ ω, X ω ^ 2 ∂μ) * √(m : ℝ) := by
  have hint : Integrable X μ := hX2.integrable one_le_two
  have hX2nn : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg (fun ω ↦ sq_nonneg _)
  calc |∑ j ∈ Finset.range m, ∫ ω, truncation X (√(j : ℝ)) ω ∂μ|
      ≤ ∑ j ∈ Finset.range m, |∫ ω, truncation X (√(j : ℝ)) ω ∂μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range m, (∫ ω, X ω ^ 2 ∂μ) / √(j : ℝ) := by
        refine Finset.sum_le_sum (fun j _ ↦ ?_)
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · subst hj0
          simp only [Nat.cast_zero, sqrt_zero, truncation_zero, Pi.zero_apply, integral_zero,
            abs_zero, div_zero, le_refl]
        · exact abs_integral_truncation_le hX2 hX0 (sqrt_pos.mpr (by exact_mod_cast hjpos))
    _ = (∫ ω, X ω ^ 2 ∂μ) * ∑ j ∈ Finset.range m, 1 / √(j : ℝ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ ↦ (mul_one_div _ _).symm)
    _ ≤ (∫ ω, X ω ^ 2 ∂μ) * (2 * √(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le m) hX2nn
    _ = 2 * (∫ ω, X ω ^ 2 ∂μ) * √(m : ℝ) := by ring

/-- **Second moment of a truncation is not increased** (the low-part variance bound). For `X²`
integrable, `∫ (trunc(X,A))² ≤ ∫ X²`, since `|trunc(X,A)| ≤ |X|` pointwise
(`abs_truncation_le_abs_self`). Hence `Var(Y^L) ≤ E[(Y^L)²] ≤ σ²`, giving `⟨S̃⟩_n ≤ σ² n` for the
truncated main part. -/
lemma integral_sq_truncation_le [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX2 : MemLp X 2 μ) (A : ℝ) :
    ∫ ω, truncation X A ω ^ 2 ∂μ ≤ ∫ ω, X ω ^ 2 ∂μ := by
  have hint : Integrable X μ := hX2.integrable one_le_two
  have hptwise : ∀ ω, truncation X A ω ^ 2 ≤ X ω ^ 2 := fun ω ↦ by
    have h := pow_le_pow_left₀ (abs_nonneg (truncation X A ω)) (abs_truncation_le_abs_self X A ω) 2
    rwa [sq_abs, sq_abs] at h
  have haesm : AEStronglyMeasurable (fun ω ↦ truncation X A ω ^ 2) μ :=
    (hint.aestronglyMeasurable.integrable_truncation.aestronglyMeasurable.pow 2)
  have htrunc2_int : Integrable (fun ω ↦ truncation X A ω ^ 2) μ :=
    Integrable.mono' hX2.integrable_sq haesm (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hptwise ω)
  exact integral_mono htrunc2_int hX2.integrable_sq hptwise

/-- **A centred truncation is bounded by `2|A|`.** On a probability space, both
`|truncation f A| ≤ |A|` and `|E[truncation f A]| ≤ |A|`, so the centred truncation
`truncation f A - E[truncation f A]` is bounded by `2|A|`. This is the increment bound
`|ΔS̃_j| ≤ 2 b_j` of the low-part martingale. -/
lemma abs_truncation_sub_integral_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (A : ℝ) (ω : Ω) :
    |truncation f A ω - ∫ x, truncation f A x ∂μ| ≤ 2 * |A| := by
  have h2 : |∫ x, truncation f A x ∂μ| ≤ |A| := by
    calc |∫ x, truncation f A x ∂μ|
        ≤ ∫ x, |truncation f A x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _x, |A| ∂μ := integral_mono hf.integrable_truncation.abs (integrable_const _)
            (fun x ↦ abs_truncation_le_bound f A x)
      _ = |A| := by simp
  calc |truncation f A ω - ∫ x, truncation f A x ∂μ|
      ≤ |truncation f A ω| + |∫ x, truncation f A x ∂μ| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ |A| + |A| := add_le_add (abs_truncation_le_bound f A ω) h2
    _ = 2 * |A| := by ring

/-- **Variance of a truncation is at most the second moment.**
`∫ (truncation X A - E[truncation X A])² ≤ ∫ X²`, combining `variance_le_expectation_sq`
(`Var ≤ E[·²]`) with `integral_sq_truncation_le`. This is `Var(Y^L) ≤ σ²`, giving the linear
quadratic-variation bound `⟨S̃⟩_n ≤ σ² n` for the centred truncated martingale. -/
lemma integral_truncation_sub_integral_sq_le [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX2 : MemLp X 2 μ) (A : ℝ) :
    ∫ ω, (truncation X A ω - ∫ x, truncation X A x ∂μ) ^ 2 ∂μ ≤ ∫ ω, X ω ^ 2 ∂μ := by
  have hint : Integrable X μ := hX2.integrable one_le_two
  calc ∫ ω, (truncation X A ω - ∫ x, truncation X A x ∂μ) ^ 2 ∂μ
      = variance (truncation X A) μ :=
        (variance_eq_integral hint.aestronglyMeasurable.truncation.aemeasurable).symm
    _ ≤ ∫ ω, truncation X A ω ^ 2 ∂μ :=
        variance_le_expectation_sq hint.aestronglyMeasurable.truncation
    _ ≤ ∫ ω, X ω ^ 2 ∂μ := integral_sq_truncation_le hX2 A

/-- **High part is eventually zero.** For an identically distributed sequence `Y` with finite second
moment, almost surely `|Y j| ≤ √j` for all large `j`; hence the high part `Y_j 𝟙{|Y_j|>√j}` vanishes
eventually and `H_m = ∑_{j≤m} Y_j 𝟙{|Y_j|>√j}` is `O(1)`.
The tail sum `∑_j P(|Y_j|>√j) = ∑_j ρ{|x|>√j}` (with `ρ` the common law) is finite by the
layer-cake bound (`tsum_measure_abs_sub_gt_sqrt_ne_top` at `θ = 0`), and Borel–Cantelli
(`ae_eventually_abs_le_of_tsum_ne_top`) gives the eventual bound. Needs only identical
distribution, not independence. -/
lemma ae_eventually_abs_le_sqrt_of_identDistrib [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (Y j))
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hint2 : MemLp (Y 0) 2 μ) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, |Y j ω| ≤ √(j : ℝ) := by
  set ρ : Measure ℝ := μ.map (Y 0) with hρ
  have : IsFiniteMeasure ρ := by rw [hρ]; infer_instance
  have hρ2 : MemLp (fun x ↦ x) 2 ρ := by
    rw [hρ, memLp_map_measure_iff (by fun_prop) (hmeas 0).aemeasurable]
    exact hint2
  have hfin : (∑' j : ℕ, μ {ω | √(j : ℝ) < |Y j ω|}) ≠ ∞ := by
    have hkey : ∀ j : ℕ, μ {ω | √(j : ℝ) < |Y j ω|} = ρ {x | √(j : ℝ) < |x - 0|} := by
      intro j
      have hset : MeasurableSet {x : ℝ | √(j : ℝ) < |x - 0|} :=
        measurableSet_lt measurable_const (by fun_prop)
      rw [show {ω | √(j : ℝ) < |Y j ω|} = (Y j) ⁻¹' {x | √(j : ℝ) < |x - 0|} by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_zero],
        (hident j).measure_mem_eq hset, ← Measure.map_apply (hmeas 0) hset]
    rw [tsum_congr hkey]
    exact tsum_measure_abs_sub_gt_sqrt_ne_top 0 hρ2
  exact ae_eventually_abs_le_of_tsum_ne_top hfin

/-! ### Partial sums of independent centred variables form a martingale

For a sequence `Y` of independent, integrable, centred variables, the partial sums
`S_n = ∑_{j<n} Y_j` are a martingale with `S_0 = 0`. Mathlib's `Filtration.natural` puts
`Y_n` into level `n`, which would force `S_0 = Y_0 ≠ 0`; the correct filtration for partial sums
is the "strictly before `n`" one, `𝒢_n = σ(Y_0,…,Y_{n-1})`. This is the general martingale carrying
the i.i.d. Hartman–Wintner argument (applied to the truncated increments). -/

/-- **Natural filtration strictly before `n`**: `𝒢_n = σ(Y_0,…,Y_{n-1})`, with `𝒢_0 = ⊥`. Unlike
`Filtration.natural` (which has `ℱ_n = σ(Y_0,…,Y_n)`), this is the filtration making the partial
sums `S_n = ∑_{j<n} Y_j` adapted with `S_0 = 0`, hence a martingale when the `Y_j` are independent
and centred. -/
noncomputable def natFiltLT {Ω : Type*} {m0 : MeasurableSpace Ω} (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable (Y i)) : Filtration ℕ m0 where
  seq n := ⨆ j ∈ {j | j < n}, MeasurableSpace.comap (Y j) inferInstance
  mono' _ _ hij := biSup_mono fun _ hk => lt_of_lt_of_le hk hij
  le' _ := iSup₂_le fun j _ => (hY j).measurable.comap_le

/-- `Y i` is measurable with respect to `natFiltLT Y hY n` whenever `i < n` (`Y i` enters the
filtration strictly before `n`). -/
@[specifies natFiltLT "one half of \"σ(Y_0,…,Y_{n-1})\": the filtration is large enough to see \
every strictly earlier variable, which is what makes partial sums adapted"]
lemma stronglyMeasurable_natFiltLT {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i))
    {i n : ℕ} (hin : i < n) :
    StronglyMeasurable[(natFiltLT Y hY : Filtration ℕ m0) n] (Y i) :=
  (comap_measurable (Y i)).stronglyMeasurable.mono
    (le_iSup₂ (f := fun k (_ : k ∈ {j | j < n}) ↦ MeasurableSpace.comap (Y k) inferInstance) i hin)

/-- **`natFiltLT` is the smallest such filtration.** Any filtration that already sees every
strictly earlier variable contains it, since each `σ(Y j)` with `j < n` is below its level `n` and
`natFiltLT` is the supremum of exactly those. -/
lemma natFiltLT_le {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i)) {𝒢 : Filtration ℕ m0}
    (h𝒢 : ∀ i n, i < n → StronglyMeasurable[𝒢 n] (Y i)) : (natFiltLT Y hY : Filtration ℕ m0) ≤ 𝒢 :=
  fun n ↦ iSup₂_le fun j hj ↦ (h𝒢 j n hj).measurable.comap_le

/-! #### Characterization

The two `@[specifies]` claims above are the two halves of a single description, and together they
are the whole of it: `natFiltLT Y hY` is the **least** filtration that sees every strictly earlier
variable. Large enough is `stronglyMeasurable_natFiltLT`; not too large is `natFiltLT_le`, and it
is minimality that carries the off-by-one — the filtrations seeing `Y i` for `i ≤ n` also see it
for `i < n`, and it is only by being least that `natFiltLT` excludes `Y n` from level `n`. -/

/-- **`𝒢` is the natural filtration strictly before `n`**: it sees every variable of strictly
earlier index, and it is the smallest filtration that does. -/
@[characterization property natFiltLT "the least filtration seeing every strictly earlier \
variable — `Y i` is known at level `n` exactly when `i < n`"]
structure IsNatFiltLT (Y : ℕ → Ω → ℝ) (𝒢 : Filtration ℕ m0) : Prop where
  /-- `𝒢` is large enough: every strictly earlier variable is measurable at level `n`. This is
  what makes the partial sums `S n = ∑_{j<n} Y j` adapted. -/
  stronglyMeasurable : ∀ i n, i < n → StronglyMeasurable[𝒢 n] (Y i)
  /-- `𝒢` is not too large: it is below every filtration with the previous property. Without
  this the field above is satisfied by `Filtration.natural` too, and by `⊤`. -/
  le : ∀ 𝒢' : Filtration ℕ m0, (∀ i n, i < n → StronglyMeasurable[𝒢' n] (Y i)) → 𝒢 ≤ 𝒢'

/-- **`natFiltLT` sees the strict past and no more** — the existence half of the
characterization. -/
@[characterization existence]
lemma isNatFiltLT_natFiltLT {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i)) :
    IsNatFiltLT Y (natFiltLT Y hY : Filtration ℕ m0) where
  stronglyMeasurable _ _ hin := stronglyMeasurable_natFiltLT hY hin
  le _ h𝒢 := natFiltLT_le hY h𝒢

/-- **Nothing else does** — the uniqueness half: a least element of an order is unique, so any
filtration with the property *is* `natFiltLT Y hY`, on the nose rather than up to anything. -/
@[characterization uniqueness]
lemma IsNatFiltLT.eq_natFiltLT {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i))
    {𝒢 : Filtration ℕ m0} (h𝒢 : IsNatFiltLT Y 𝒢) : 𝒢 = natFiltLT Y hY :=
  le_antisymm (h𝒢.le _ fun _ _ hin ↦ stronglyMeasurable_natFiltLT hY hin)
    (natFiltLT_le hY h𝒢.stronglyMeasurable)

/-- The σ-algebra `σ(Y_n)` is independent of the past `𝒢_n = σ(Y_0,…,Y_{n-1})`, from the
independence of `Y`. This is the disjoint-index instance of `indep_iSup_of_disjoint`. -/
@[specifies natFiltLT "the other half, and the one that distinguishes this from \
`Filtration.natural`: `Y n` is *not* seen at level `n`, so the increment is still fresh — an \
off-by-one here would force `S 0 = Y 0 ≠ 0` and destroy the martingale property"]
lemma indep_comap_natFiltLT {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i))
    (hindep : iIndepFun Y μ) (n : ℕ) :
    Indep (MeasurableSpace.comap (Y n) (inferInstance : MeasurableSpace ℝ))
      ((natFiltLT Y hY : Filtration ℕ m0) n) μ := by
  have h := indep_iSup_of_disjoint (fun k ↦ (hY k).measurable.comap_le) hindep
    (S := {n}) (T := {j | j < n}) (by simp)
  rwa [iSup_singleton] at h

/-- **Future independence for the strict natural filtration** (composed form). For independent `Y`
and measurable `g`, the conditional expectation of `g(Y_n)` given the past `𝒢_n = σ(Y_0,…,Y_{n-1})`
is its mean. Applied with `g = id` it gives the martingale increment computation; with `g = (·²)`,
the quadratic-variation increment. -/
lemma condExp_natFiltLT_comp_indep [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ) {g : ℝ → ℝ} (hg : Measurable g)
    (n : ℕ) :
    μ[fun ω ↦ g (Y n ω) | (natFiltLT Y hY : Filtration ℕ m0) n]
      =ᵐ[μ] fun _ ↦ ∫ ω, g (Y n ω) ∂μ :=
  condExp_indep_eq (hY n).measurable.comap_le ((natFiltLT Y hY).le n)
    (hg.comp (comap_measurable (Y n))).stronglyMeasurable (indep_comap_natFiltLT hY hindep n)

/-- **Future independence for the strict natural filtration.** For independent `Y`, the conditional
expectation of `Y n` given the past `𝒢_n = σ(Y_0,…,Y_{n-1})` is its mean. This is the martingale
increment computation, the `<`-analogue of `iIndepFun.condExp_natural_ae_eq_of_lt`. -/
lemma condExp_natFiltLT_indep [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ) (n : ℕ) :
    μ[Y n | (natFiltLT Y hY : Filtration ℕ m0) n] =ᵐ[μ] fun _ ↦ ∫ ω, Y n ω ∂μ :=
  condExp_natFiltLT_comp_indep hY hindep measurable_id n

/-- **Partial sums of independent centred variables form a martingale.** For independent,
integrable, centred `Y`, the partial sums `S_n = ∑_{j<n} Y_j` are a martingale for the strict
natural filtration
`natFiltLT Y hY`, with `S_0 = 0`. This is the martingale underlying the i.i.d. Hartman–Wintner LIL
(applied to the truncated increments) and a natural standalone result. -/
lemma martingale_iidSum [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hint : ∀ i, Integrable (Y i) μ) (hcent : ∀ i, ∫ ω, Y i ω ∂μ = 0) :
    Martingale (fun n ↦ ∑ j ∈ Finset.range n, Y j) (natFiltLT Y hY) μ := by
  set 𝒢 : Filtration ℕ m0 := natFiltLT Y hY with h𝒢
  set S : ℕ → Ω → ℝ := fun n ↦ ∑ j ∈ Finset.range n, Y j with hS
  have hadp : StronglyAdapted 𝒢 S := fun n ↦
    Finset.stronglyMeasurable_sum _ fun j hj ↦
      stronglyMeasurable_natFiltLT hY (Finset.mem_range.mp hj)
  have hSint : ∀ n, Integrable (S n) μ := fun n ↦ integrable_finsetSum' _ fun j _ ↦ hint j
  refine martingale_nat hadp hSint fun n ↦ ?_
  have h1 : μ[S (n + 1) | 𝒢 n] =ᵐ[μ] μ[S n | 𝒢 n] + μ[Y n | 𝒢 n] := by
    rw [show S (n + 1) = S n + Y n from Finset.sum_range_succ Y n]
    exact condExp_add (hSint n) (hint n) _
  have h2 : μ[S n | 𝒢 n] = S n := condExp_of_stronglyMeasurable (𝒢.le n) (hadp n) (hSint n)
  have h3 : μ[Y n | 𝒢 n] =ᵐ[μ] fun _ ↦ ∫ ω, Y n ω ∂μ := condExp_natFiltLT_indep hY hindep n
  filter_upwards [h1, h3] with ω e1 e3
  simp only [e1, Pi.add_apply, e3, hcent n, add_zero]
  exact (congrFun h2 ω).symm

/-- **Quadratic-variation increment of the i.i.d. sum.** The predictable quadratic variation of the
martingale `S_n = ∑_{j<n} Y_j` has increment `⟨S⟩_{n+1} - ⟨S⟩_n = E[Y_n²]` a.e.: it is the
conditional second moment of `ΔS_n = Y_n` (`predQuadVar_succ_sub_eq`), which independence makes
constant equal to `E[Y_n²]` (`condExp_natFiltLT_comp_indep` with `g = (·²)`). -/
lemma predQuadVar_iidSum_succ_sub [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hcent : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hint2 : ∀ i, MemLp (Y i) 2 μ) (n : ℕ) :
    predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (n + 1)
        - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ n
      =ᵐ[μ] fun _ ↦ ∫ ω, Y n ω ^ 2 ∂μ := by
  have hint : ∀ i, Integrable (Y i) μ := fun i ↦ (hint2 i).integrable one_le_two
  set S : ℕ → Ω → ℝ := fun m ↦ ∑ j ∈ Finset.range m, Y j with hS
  have hS2 : ∀ m, MemLp (S m) 2 μ := fun m ↦ memLp_finsetSum' _ fun j _ ↦ hint2 j
  have hM : Martingale S (natFiltLT Y hY) μ := martingale_iidSum hY hindep hint hcent
  have hΔ : ∀ ω, S (n + 1) ω - S n ω = Y n ω := fun ω ↦ by
    simp only [hS, Finset.sum_apply, Finset.sum_range_succ]; ring
  have hd2 : MemLp (fun ω ↦ S (n + 1) ω - S n ω) 2 μ := by simpa only [hΔ] using hint2 n
  have hprod : Integrable (S n * (S (n + 1) - S n)) μ :=
    integrable_mul_increment (hS2 n) (hS2 (n + 1))
  refine (predQuadVar_succ_sub_eq hM n hd2 hprod).trans ?_
  rw [show (fun ω ↦ (S (n + 1) ω - S n ω) ^ 2) = fun ω ↦ Y n ω ^ 2 from
    funext fun ω ↦ by rw [hΔ ω]]
  exact condExp_natFiltLT_comp_indep hY hindep (g := fun x ↦ x ^ 2) (by fun_prop) n

/-- **Linear bound on the quadratic variation of the i.i.d. sum.** If every increment has second
moment `E[Y_i²] ≤ v`, then almost surely `⟨S⟩_n ≤ v·n` for all `n`, telescoping the constant
increments `⟨S⟩_{k+1} - ⟨S⟩_k = E[Y_k²]` (`predQuadVar_iidSum_succ_sub`). This is the `⟨M⟩_n ≤ v·n`
input required by the growing-increment loglog LIL. -/
lemma predQuadVar_iidSum_le [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hcent : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hint2 : ∀ i, MemLp (Y i) 2 μ) {v : ℝ} (hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ v) :
    ∀ᵐ ω ∂μ, ∀ n,
      predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ n ω ≤ v * n := by
  have hint : ∀ i, Integrable (Y i) μ := fun i ↦ (hint2 i).integrable one_le_two
  have hstep : ∀ k, ∀ᵐ ω ∂μ,
      predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (k + 1) ω
        - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω ≤ v := by
    intro k
    filter_upwards [predQuadVar_iidSum_succ_sub hY hindep hcent hint2 k] with ω e
    have he : predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (k + 1) ω
        - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω
        = ∫ ω, Y k ω ^ 2 ∂μ := by simpa using e
    rw [he]; exact hv k
  filter_upwards [ae_all_iff.mpr hstep] with ω hω n
  have htel : ∑ k ∈ Finset.range n,
      (predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (k + 1) ω
        - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω)
      = predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ n ω := by
    rw [Finset.sum_range_sub
        (fun k ↦ predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω) n,
      show predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ 0 ω = 0 from by
        rw [predQuadVar_zero]; rfl, sub_zero]
  rw [← htel]
  calc ∑ k ∈ Finset.range n,
        (predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (k + 1) ω
          - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω)
      ≤ ∑ _k ∈ Finset.range n, v := Finset.sum_le_sum fun k _ ↦ hω k
    _ = v * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Linear lower bound on the quadratic variation of the i.i.d. sum.** If every increment has
second moment `E[Y_i²] ≥ w`, then almost surely `w·n ≤ ⟨S⟩_n` for all `n`. With `w > 0` this forces
`⟨S⟩_n → ∞`, the hypothesis of the (bounded-increment) loglog LIL. -/
lemma predQuadVar_iidSum_ge [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hcent : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hint2 : ∀ i, MemLp (Y i) 2 μ) {w : ℝ} (hw : ∀ i, w ≤ ∫ ω, Y i ω ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, ∀ n,
      w * n ≤ predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ n ω := by
  have hint : ∀ i, Integrable (Y i) μ := fun i ↦ (hint2 i).integrable one_le_two
  have hstep : ∀ k, ∀ᵐ ω ∂μ, w ≤
      predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (k + 1) ω
        - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω := by
    intro k
    filter_upwards [predQuadVar_iidSum_succ_sub hY hindep hcent hint2 k] with ω e
    have he : predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (k + 1) ω
        - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω
        = ∫ ω, Y k ω ^ 2 ∂μ := by simpa using e
    rw [he]; exact hw k
  filter_upwards [ae_all_iff.mpr hstep] with ω hω n
  have htel : ∑ k ∈ Finset.range n,
      (predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (k + 1) ω
        - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω)
      = predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ n ω := by
    rw [Finset.sum_range_sub
        (fun k ↦ predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω) n,
      show predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ 0 ω = 0 from by
        rw [predQuadVar_zero]; rfl, sub_zero]
  rw [← htel]
  calc w * n = ∑ _k ∈ Finset.range n, w := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ k ∈ Finset.range n,
        (predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ (k + 1) ω
          - predQuadVar (fun m ↦ ∑ j ∈ Finset.range m, Y j) (natFiltLT Y hY) μ k ω) :=
        Finset.sum_le_sum fun k _ ↦ hω k

/-- **Loglog LIL for bounded independent centred variables.** For an independent, centred sequence
`Y` with `|Y_i| ≤ c` a.e. and second moments bounded below by `w > 0`, the partial sums
`S_n = ∑_{j<n} Y_j` satisfy `|S_n| ≤ C √(n log log n)` for all large `n`, almost surely. This is the
bounded case of the Hartman–Wintner LIL: the i.i.d.-sum martingale (`martingale_iidSum`), its
quadratic variation (`predQuadVar_iidSum_le`/`predQuadVar_iidSum_ge`, giving `⟨S⟩_n → ∞`), and the
bounded increments feed the general bounded-increment engine
`ae_eventually_abs_le_sqrt_nat_mul_loglog`. -/
lemma ae_eventually_abs_sum_le_sqrt_nat_mul_loglog_of_bounded [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hcent : ∀ i, ∫ ω, Y i ω ∂μ = 0) {c : ℝ} (hc : 0 < c) (hbdd : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ c)
    {w : ℝ} (hw : 0 < w) (hvar : ∀ i, w ≤ ∫ ω, Y i ω ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, ∃ C, ∀ᶠ n in atTop,
      |(∑ j ∈ Finset.range n, Y j) ω| ≤ C * √((n : ℝ) * log (log n)) := by
  have hmemLp2 : ∀ i, MemLp (Y i) 2 μ := fun i ↦ MemLp.of_bound (hY i).aestronglyMeasurable c
    (by filter_upwards [hbdd i] with ω h; rwa [Real.norm_eq_abs])
  have hint : ∀ i, Integrable (Y i) μ := fun i ↦ (hmemLp2 i).integrable one_le_two
  have hint2 : ∀ i, MemLp (Y i) 2 μ := hmemLp2
  set M : ℕ → Ω → ℝ := fun n ↦ ∑ j ∈ Finset.range n, Y j with hM_def
  have hM : Martingale M (natFiltLT Y hY) μ := martingale_iidSum hY hindep hint hcent
  have hM0 : M 0 =ᵐ[μ] 0 := by simp [hM_def]
  have hM2 : ∀ n, MemLp (M n) 2 μ := fun n ↦
    memLp_finsetSum' (Finset.range n) fun j _ ↦ hmemLp2 j
  have hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c := fun i ↦ by
    filter_upwards [hbdd i] with ω h
    have hΔ : M (i + 1) ω - M i ω = Y i ω := by
      simp only [hM_def, Finset.sum_apply, Finset.sum_range_succ]; ring
    rw [hΔ]; exact h
  have hV : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ predQuadVar M (natFiltLT Y hY) μ n ω) atTop atTop := by
    filter_upwards [predQuadVar_iidSum_ge hY hindep hcent hint2 hvar] with ω hge
    exact tendsto_atTop_mono hge (Tendsto.const_mul_atTop hw tendsto_natCast_atTop_atTop)
  exact ae_eventually_abs_le_sqrt_nat_mul_loglog hM hM0 hM2 hc hb hV

/-! ### The centred-truncation (low-part) martingale

For the Hartman–Wintner decomposition the low part is `S̃_n = ∑_{j<n}(Y_j^L - E Y_j^L)` with
`Y_j^L = truncation(Y_j, b_j)`. Since `truncation f A = indicator (Ioc (-A) A) id ∘ f`, the centred
truncations are independent functions of the independent `Y`, so the i.i.d.-sum martingale machinery
applies: `S̃` is a martingale with `⟨S̃⟩_n ≤ σ²·n` (`Var(Y_j^L) ≤ σ²`) and increments
`|ΔS̃_j| ≤ 2 b_j`. -/

/-- **Independence of centred truncations.** If `Y` is independent, so is the family of centred
truncations `j ↦ truncation (Y j) (b j) - c j`, each being a measurable function of `Y j`. -/
lemma iIndepFun_truncation_sub_const {Y : ℕ → Ω → ℝ} (hindep : iIndepFun Y μ) (b c : ℕ → ℝ) :
    iIndepFun (fun j ω ↦ truncation (Y j) (b j) ω - c j) μ :=
  hindep.comp (fun j x ↦ Set.indicator (Set.Ioc (-(b j)) (b j)) id x - c j)
    fun _ ↦ (measurable_id.indicator measurableSet_Ioc).sub measurable_const

/-- The centred truncation `truncation (Y j) (b j) - c j` is strongly measurable. -/
lemma stronglyMeasurable_centeredTruncation {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (b c : ℕ → ℝ) (j : ℕ) :
    StronglyMeasurable (fun ω ↦ truncation (Y j) (b j) ω - c j) :=
  (((measurable_id.indicator measurableSet_Ioc).comp (hY j).measurable).stronglyMeasurable).sub
    stronglyMeasurable_const

/-- The centred truncation `truncation (Y i) (b i) - c i` is in `L²` (indeed bounded by
`|b i| + |c i|`), on a probability space. -/
lemma memLp_two_truncation_sub_const [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (b c : ℕ → ℝ) (i : ℕ) :
    MemLp (fun ω ↦ truncation (Y i) (b i) ω - c i) 2 μ :=
  MemLp.of_bound (stronglyMeasurable_centeredTruncation hY b c i).aestronglyMeasurable
    (|b i| + |c i|) (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      exact add_le_add (abs_truncation_le_bound (Y i) (b i) ω) le_rfl)

/-- **The low-part (centred-truncation) martingale.** For independent `Y`, the centred truncations
`Y_j^L - E Y_j^L = truncation(Y_j, b_j) - E[truncation(Y_j, b_j)]` sum to a martingale
`S̃_n = ∑_{j<n}(Y_j^L - E Y_j^L)`, via `martingale_iidSum`. -/
lemma martingale_centeredTruncation [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ) (b : ℕ → ℝ) :
    Martingale
      (fun n ↦ ∑ j ∈ Finset.range n,
        fun ω ↦ truncation (Y j) (b j) ω - ∫ x, truncation (Y j) (b j) x ∂μ)
      (natFiltLT _ (stronglyMeasurable_centeredTruncation hY b
        fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ)) μ :=
  martingale_iidSum
    (stronglyMeasurable_centeredTruncation hY b fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ)
    (iIndepFun_truncation_sub_const hindep b fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ)
    (fun i ↦ (memLp_two_truncation_sub_const hY b
      (fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ) i).integrable one_le_two)
    (fun i ↦ by
      rw [integral_sub (hY i).aestronglyMeasurable.integrable_truncation (integrable_const _)]
      simp)

/-- **Linear quadratic-variation bound for the low part.** Since `Var(Y_j^L) ≤ E[Y_j²] ≤ v`, the
centred-truncation martingale has `⟨S̃⟩_n ≤ v·n` a.s. -/
lemma predQuadVar_centeredTruncation_le [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hint2 : ∀ i, MemLp (Y i) 2 μ)
    (b : ℕ → ℝ) {v : ℝ} (hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ v) :
    ∀ᵐ ω ∂μ, ∀ n,
      predQuadVar
        (fun m ↦ ∑ j ∈ Finset.range m,
          fun ω ↦ truncation (Y j) (b j) ω - ∫ x, truncation (Y j) (b j) x ∂μ)
        (natFiltLT _ (stronglyMeasurable_centeredTruncation hY b
          fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ)) μ n ω ≤ v * n :=
  predQuadVar_iidSum_le
    (stronglyMeasurable_centeredTruncation hY b fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ)
    (iIndepFun_truncation_sub_const hindep b fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ)
    (fun i ↦ by
      rw [integral_sub (hY i).aestronglyMeasurable.integrable_truncation (integrable_const _)]
      simp)
    (fun i ↦ memLp_two_truncation_sub_const hY b
      (fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ) i)
    (fun i ↦ (integral_truncation_sub_integral_sq_le (hint2 i) (b i)).trans (hv i))

/-- **Sharp low-part LIL (`β > 1` limit, two-sided).** For an independent, `L²` sequence `Y` with
second moments `∫ Y_i² ≤ v` (`0 < v`) and truncation levels `b` that are monotone, nonnegative and
satisfy the base-independent condition \textbf{(H)} `b_n √(loglog n / n) → 0`, the
centred-truncation martingale `S̃_n = ∑_{j<n}(Y_j^L - E Y_j^L)`
(with `Y_j^L = truncation(Y_j, b_j)`) satisfies, a.s., for every `β > 1` eventually
`|S̃_n| ≤ β √(2 v n loglog n)` — the sharp constant `1` for the low part of Hartman–Wintner.
The increments `|ΔS̃_j| ≤ 2 b_j` (`abs_truncation_sub_integral_le`) and the
linear quadratic variation `⟨S̃⟩_n ≤ v·n` (`predQuadVar_centeredTruncation_le`) feed the sharp
growing-increment engine `ae_eventually_abs_le_sqrt_nat_mul_loglog_of_growth_sharp_all` with growth
`g = 2b`. No random stopping time; the log-level cutoff `b_n = √(n/log(n+2))` satisfies (H) since
`b_n √(loglog n/n) = √(loglog n/log(n+2)) → 0`. -/
lemma ae_eventually_abs_le_sqrt_nat_mul_loglog_centeredTruncation_sharp [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hint2 : ∀ i, MemLp (Y i) 2 μ)
    {v : ℝ} (hv0 : 0 < v) (hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ v)
    {b : ℕ → ℝ} (hbmono : Monotone b) (hbnn : ∀ i, 0 ≤ b i)
    (hbH : Tendsto (fun n : ℕ ↦ b n * √(log (log n) / n)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ β : ℝ, 1 < β → ∀ᶠ n in atTop,
      |(∑ j ∈ Finset.range n,
          fun ω ↦ truncation (Y j) (b j) ω - ∫ x, truncation (Y j) (b j) x ∂μ) ω|
        ≤ β * √(2 * v * (n : ℝ) * log (log n)) := by
  have hint : ∀ i, Integrable (Y i) μ := fun i ↦ (hint2 i).integrable one_le_two
  set SL : ℕ → Ω → ℝ := fun n ↦ ∑ j ∈ Finset.range n,
    fun ω ↦ truncation (Y j) (b j) ω - ∫ x, truncation (Y j) (b j) x ∂μ with hSL_def
  have hmemLp : ∀ j, MemLp (fun ω ↦ truncation (Y j) (b j) ω
      - ∫ x, truncation (Y j) (b j) x ∂μ) 2 μ := fun j ↦
    memLp_two_truncation_sub_const hY b (fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ) j
  have hM : Martingale SL (natFiltLT _ (stronglyMeasurable_centeredTruncation hY b
      fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ)) μ :=
    martingale_centeredTruncation hY hindep b
  have hM0 : SL 0 =ᵐ[μ] 0 := by simp [hSL_def]
  have hM2 : ∀ n, MemLp (SL n) 2 μ := fun n ↦
    memLp_finsetSum' (Finset.range n) fun j _ ↦ hmemLp j
  have hgmono : Monotone (fun i ↦ 2 * b i) := hbmono.const_mul (by norm_num)
  have hgnn : ∀ i, 0 ≤ 2 * b i := fun i ↦ mul_nonneg (by norm_num) (hbnn i)
  have hg : Tendsto (fun n : ℕ ↦ 2 * b n * √(log (log n) / n)) atTop (𝓝 0) := by
    have h := hbH.const_mul 2; rw [mul_zero] at h; exact h.congr (fun n ↦ by ring)
  have hginc : ∀ i, ∀ᵐ ω ∂μ, |SL (i + 1) ω - SL i ω| ≤ 2 * b i := fun i ↦
    Eventually.of_forall fun ω ↦ by
      have hΔ : SL (i + 1) ω - SL i ω
          = truncation (Y i) (b i) ω - ∫ x, truncation (Y i) (b i) x ∂μ := by
        simp only [hSL_def, Finset.sum_apply, Finset.sum_range_succ]; ring
      rw [hΔ]
      have hb := abs_truncation_sub_integral_le (μ := μ) (hY i).aestronglyMeasurable (b i) ω
      rwa [abs_of_nonneg (hbnn i)] at hb
  have hqv : ∀ᵐ ω ∂μ, ∀ n, predQuadVar SL (natFiltLT _
      (stronglyMeasurable_centeredTruncation hY b fun j ↦ ∫ x, truncation (Y j) (b j) x ∂μ))
      μ n ω ≤ v * (n : ℝ) :=
    predQuadVar_centeredTruncation_le hY hindep hint2 b hv
  exact ae_eventually_abs_le_sqrt_nat_mul_loglog_of_growth_sharp_all hM hM0 hM2 hv0 hgmono hgnn
    hginc hg hqv

/-- **Sharp low-part LIL as a `limsup`.** From the `∀ β > 1, ∀ᶠ` two-sided form, a.s.
`limsup_n |S̃_n| / √(2 v n log log n) ≤ 1`. -/
lemma ae_limsup_abs_div_sqrt_nat_mul_loglog_centeredTruncation_le_one [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hint2 : ∀ i, MemLp (Y i) 2 μ)
    {v : ℝ} (hv0 : 0 < v) (hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ v)
    {b : ℕ → ℝ} (hbmono : Monotone b) (hbnn : ∀ i, 0 ≤ b i)
    (hbH : Tendsto (fun n : ℕ ↦ b n * √(log (log n) / n)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, limsup (fun n ↦ |(∑ j ∈ Finset.range n,
          fun ω ↦ truncation (Y j) (b j) ω - ∫ x, truncation (Y j) (b j) x ∂μ) ω|
        / √(2 * v * (n : ℝ) * log (log n))) atTop ≤ 1 := by
  filter_upwards [ae_eventually_abs_le_sqrt_nat_mul_loglog_centeredTruncation_sharp hY hindep
    hint2 hv0 hv hbmono hbnn hbH] with ω hω
  have hf_nonneg : ∀ n, 0 ≤ |(∑ j ∈ Finset.range n,
      fun ω ↦ truncation (Y j) (b j) ω - ∫ x, truncation (Y j) (b j) x ∂μ) ω|
        / √(2 * v * (n : ℝ) * log (log n)) :=
    fun n ↦ div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ |(∑ j ∈ Finset.range n,
      fun ω ↦ truncation (Y j) (b j) ω - ∫ x, truncation (Y j) (b j) x ∂μ) ω|
        / √(2 * v * (n : ℝ) * log (log n))) :=
    IsCoboundedUnder.of_frequently_ge (a := 0) ((Eventually.of_forall hf_nonneg).frequently)
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  refine limsup_le_of_le hcobdd ?_
  filter_upwards [hω a ha] with n hn
  rcases le_or_gt (√(2 * v * (n : ℝ) * log (log n))) 0 with hs | hs
  · rw [le_antisymm hs (Real.sqrt_nonneg _), div_zero]; linarith
  · rw [div_le_iff₀ hs]; exact hn

/-! ### The medium-band variance estimate (Kolmogorov's crux)

The medium part `Y_j^{\mathrm M} = Y_j 𝟙{b_j < |Y_j| ≤ √j}` (`b_j = √(j/log(j+2))`, the log-level
cutoff) has `∑_{j≥3} Var(Y_j^M)/(j log log j) < ∞` under only a bare second moment. By Tonelli the
series is `≤ E[Y² · ∑_{j : b_j<|Y|≤√j} 1/(j log log j)]`, and the inner sum is bounded uniformly
in `y = |Y|`: with `t = y²` the index set is `{j : t ≤ j < t log(j+2)}`, of multiplicative width
only `≍ log t` (a `log`-factor), so the harmonic inner sum is `O(1)`. -/

/-- `log u ≤ 2√u` for `u > 0`, via `log u = 2 log √u ≤ 2(√u - 1)`. -/
lemma log_le_two_mul_sqrt {u : ℝ} (hu : 0 < u) : log u ≤ 2 * √u := by
  have h1 : 2 * log (√u) = log u := by rw [Real.log_sqrt hu.le]; ring
  have h2 : log (√u) ≤ √u - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu)
  linarith [h1, h2]

/-- **Crude range bound.** If `j` lies in the medium index set for `t` (i.e. `t ≤ j` and
`j < t log(j+2)`) with `j ≥ 2`, then `j < 8 t²`. Uses only `log(j+2) ≤ 2√(j+2)` and
`√(j+2) ≤ √2·√j`. -/
lemma medium_crude {t : ℝ} {j : ℕ} (hj : 2 ≤ j) (_htj : t ≤ (j : ℝ))
    (hlt : (j : ℝ) < t * log ((j : ℝ) + 2)) : (j : ℝ) < 8 * t ^ 2 := by
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hlogpos : 0 < log ((j : ℝ) + 2) := Real.log_pos (by linarith)
  have htpos : 0 < t := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hlogpos.le]
  have hlogle : log ((j : ℝ) + 2) ≤ 2 * √((j : ℝ) + 2) := log_le_two_mul_sqrt (by linarith)
  have hsqrtle : √((j : ℝ) + 2) ≤ √2 * √(j : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrtj : 0 < √(j : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hjeq : (j : ℝ) = √(j : ℝ) * √(j : ℝ) := (Real.mul_self_sqrt (by linarith)).symm
  have h2sqrt : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- `j < 2√2·t·√j`.
  have hkey : (j : ℝ) < 2 * √2 * t * √(j : ℝ) := by
    calc (j : ℝ) < t * log ((j : ℝ) + 2) := hlt
      _ ≤ t * (2 * √((j : ℝ) + 2)) := by nlinarith [hlogle, htpos]
      _ ≤ t * (2 * (√2 * √(j : ℝ))) := by nlinarith [hsqrtle, htpos, Real.sqrt_nonneg (2 : ℝ)]
      _ = 2 * √2 * t * √(j : ℝ) := by ring
  -- Cancel one `√j`, then square.
  have hsj : √(j : ℝ) < 2 * √2 * t := by
    have h : √(j : ℝ) * √(j : ℝ) < 2 * √2 * t * √(j : ℝ) := by rw [← hjeq]; exact hkey
    exact lt_of_mul_lt_mul_right h hsqrtj.le
  nlinarith [hsj, hsqrtj.le, h2sqrt, htpos]

/-- **Tight range bound.** For `t ≥ √2` and `j` in the medium index set (`t ≤ j`, `j < t log(j+2)`,
`j ≥ 2`), `j < t (log 9 + 2 log t)` — a multiplicative width `≍ log t` above `t`. -/
lemma medium_tight {t : ℝ} {j : ℕ} (ht : √2 ≤ t) (hj : 2 ≤ j) (htj : t ≤ (j : ℝ))
    (hlt : (j : ℝ) < t * log ((j : ℝ) + 2)) : (j : ℝ) < t * (log 9 + 2 * log t) := by
  have htpos : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) ht
  have ht2 : (2 : ℝ) ≤ t ^ 2 := by
    have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [ht, Real.sqrt_nonneg (2 : ℝ), h]
  have hcrude : (j : ℝ) < 8 * t ^ 2 := medium_crude hj htj hlt
  have hlogj2 : log ((j : ℝ) + 2) < log 9 + 2 * log t := by
    have h9 : (j : ℝ) + 2 < 9 * t ^ 2 := by nlinarith [hcrude, ht2]
    have hlog9t : log (9 * t ^ 2) = log 9 + 2 * log t := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    calc log ((j : ℝ) + 2) < log (9 * t ^ 2) := Real.log_lt_log (by positivity) h9
      _ = log 9 + 2 * log t := hlog9t
  calc (j : ℝ) < t * log ((j : ℝ) + 2) := hlt
    _ < t * (log 9 + 2 * log t) := by exact mul_lt_mul_of_pos_left hlogj2 htpos

/-- `log log` is monotone on `[3, ∞)`. -/
lemma loglog_le_loglog {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) : log (log a) ≤ log (log b) := by
  have hla : 0 < log a := Real.log_pos (by linarith)
  exact Real.log_le_log hla (Real.log_le_log (by linarith) hab)

/-- **Harmonic-sum bound.** For `1 ≤ A ≤ B`, `∑_{j=A+1}^{B} 1/j ≤ log B - log A`, by comparing the
antitone `1/x` with its integral (`AntitoneOn.sum_le_integral_Ico`, reindexed to run over
`Icc (A+1) B`). -/
lemma sum_Icc_one_div_le {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∑ j ∈ Finset.Icc (A + 1) B, 1 / (j : ℝ) ≤ log (B : ℝ) - log (A : ℝ) := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le hApos (by exact_mod_cast hAB)
  have hanti : AntitoneOn (fun x : ℝ ↦ 1 / x) (Set.Icc (A : ℝ) (B : ℝ)) := by
    intro x hx _ _ hxy
    exact one_div_le_one_div_of_le (lt_of_lt_of_le hApos hx.1) hxy
  have hstep := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ ↦ 1 / x) (a := A) (b := B) hAB hanti
  have hreindex : ∑ i ∈ Finset.Ico A B, (fun x : ℝ ↦ 1 / x) (↑(i + 1))
      = ∑ j ∈ Finset.Icc (A + 1) B, 1 / (j : ℝ) := by
    have hIcc : Finset.Icc (A + 1) B = Finset.Ico (A + 1) (B + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) (fun k _ ↦ ?_)
    simp only
    push_cast
    ring
  have h0 : (0 : ℝ) ∉ Set.uIcc (A : ℝ) (B : ℝ) := by
    intro hmem
    rcases Set.mem_uIcc.mp hmem with ⟨h1, _⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  have hint : ∫ x in (A : ℝ)..(B : ℝ), (fun x : ℝ ↦ 1 / x) x = log (B : ℝ) - log (A : ℝ) := by
    simp only
    rw [integral_one_div h0, Real.log_div hBpos.ne' hApos.ne']
  calc ∑ j ∈ Finset.Icc (A + 1) B, 1 / (j : ℝ)
      = ∑ i ∈ Finset.Ico A B, (fun x : ℝ ↦ 1 / x) (↑(i + 1)) := hreindex.symm
    _ ≤ ∫ x in (A : ℝ)..(B : ℝ), (fun x : ℝ ↦ 1 / x) x := hstep
    _ = log (B : ℝ) - log (A : ℝ) := hint

/-- **Big-`t` finite-sum bound (the analytic heart).** For `t ≥ 9`, the finite harmonic-type sum
`∑_{j=⌈t⌉}^{⌈t(log 9 + 2 log t)⌉} 1/(j log log j) ≤ 1 + (1/9 + log 5)/log log 9`, a uniform
constant. The multiplicative width of the range is `≍ log t`, so pulling out `1/log log A` (loglog
monotone) and bounding the harmonic sum by `log(B/A) ≤ log(5 log t) = log 5 + log log t` gives an
`O(1)` sum. -/
lemma medium_sum_Icc_big {t : ℝ} (ht : 9 ≤ t) :
    ∑ j ∈ Finset.Icc ⌈t⌉₊ ⌈t * (log 9 + 2 * log t)⌉₊, 1 / ((j : ℝ) * log (log (j : ℝ)))
      ≤ 1 + (1 / 9 + log 5) / log (log 9) := by
  have htpos : (0 : ℝ) < t := by linarith
  have hlog9 : (1 : ℝ) < log 9 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hll9 : (0 : ℝ) < log (log 9) := Real.log_pos hlog9
  have hlogt : log 9 ≤ log t := Real.log_le_log (by norm_num) ht
  have hllt : log (log 9) ≤ log (log t) := loglog_le_loglog (by norm_num) ht
  set A := ⌈t⌉₊ with hA_def
  set X := t * (log 9 + 2 * log t) with hX_def
  set B := ⌈X⌉₊ with hB_def
  have htA : t ≤ (A : ℝ) := Nat.le_ceil t
  have hA9 : (9 : ℝ) ≤ (A : ℝ) := le_trans ht htA
  have hA3 : 3 ≤ A := by
    have h3 : (3 : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast h3
  have hAt1 : (A : ℝ) ≤ t + 1 := (Nat.ceil_lt_add_one htpos.le).le
  have hllA : log (log 9) ≤ log (log (A : ℝ)) := loglog_le_loglog (by norm_num) hA9
  have hlltA : log (log t) ≤ log (log (A : ℝ)) := loglog_le_loglog (by linarith) htA
  have hllApos : (0 : ℝ) < log (log (A : ℝ)) := lt_of_lt_of_le hll9 hllA
  -- `t ≤ X` so `A ≤ B`.
  have hXt : t ≤ X := by
    rw [hX_def]; nlinarith [hlogt, hlog9, htpos]
  have hAB : A ≤ B := by rw [hA_def, hB_def]; exact Nat.ceil_mono hXt
  have hXnn : (0 : ℝ) ≤ X := by
    rw [hX_def]; exact mul_nonneg htpos.le (by linarith [hlog9, hlogt])
  have hXB : (B : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one hXnn).le
  -- Pullout `1/loglog A`, then harmonic bound.
  have hpull : ∑ j ∈ Finset.Icc A B, 1 / ((j : ℝ) * log (log (j : ℝ)))
      ≤ (1 / log (log (A : ℝ))) * ∑ j ∈ Finset.Icc A B, 1 / (j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj ↦ ?_)
    have hjA : A ≤ j := (Finset.mem_Icc.mp hj).1
    have hjR : (3 : ℝ) ≤ (j : ℝ) := by
      have : (A : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjA
      linarith [hA9]
    have hjpos : (0 : ℝ) < (j : ℝ) := by linarith [hjR]
    have hlljA : log (log (A : ℝ)) ≤ log (log (j : ℝ)) :=
      loglog_le_loglog (by linarith [hA9]) (by exact_mod_cast hjA)
    rw [show (1 / log (log (A : ℝ))) * (1 / (j : ℝ)) = 1 / (log (log (A : ℝ)) * (j : ℝ)) from by
      rw [div_mul_div_comm, one_mul]]
    exact one_div_le_one_div_of_le (mul_pos hllApos hjpos)
      (by nlinarith [mul_le_mul_of_nonneg_right hlljA hjpos.le])
  -- Harmonic: `∑_{Icc A B} 1/j ≤ 1/A + (log B - log A)`.
  have hAposR : (0 : ℝ) < (A : ℝ) := by linarith
  have hharm : ∑ j ∈ Finset.Icc A B, 1 / (j : ℝ) ≤ 1 / (A : ℝ) + (log (B : ℝ) - log (A : ℝ)) := by
    have hsplit : Finset.Icc A B = insert A (Finset.Icc (A + 1) B) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have := sum_Icc_one_div_le (A := A) (B := B) (by omega) hAB
    linarith [this]
  -- `log(B/A) ≤ log 5 + loglog t`.
  have hBApos : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le hAposR (by exact_mod_cast hAB)
  have hlog5t : (5 : ℝ) ≤ log t + 4 := by nlinarith [hlogt, hlog9]
  have hBA5 : (B : ℝ) / (A : ℝ) ≤ 5 * log t := by
    rw [div_le_iff₀ hAposR]
    have hXbound : X + 1 ≤ 5 * log t * t := by
      rw [hX_def]; nlinarith [hlogt, hlog9, htpos, hlog5t]
    calc (B : ℝ) ≤ X + 1 := hXB
      _ ≤ 5 * log t * t := hXbound
      _ ≤ 5 * log t * (A : ℝ) := by nlinarith [htA, hlogt, hlog9]
  have hlogBA : log (B : ℝ) - log (A : ℝ) ≤ log 5 + log (log t) := by
    have h1 : log (B : ℝ) - log (A : ℝ) = log ((B : ℝ) / (A : ℝ)) :=
      (Real.log_div hBApos.ne' hAposR.ne').symm
    have h2 : log ((B : ℝ) / (A : ℝ)) ≤ log (5 * log t) :=
      Real.log_le_log (by positivity) hBA5
    have h3 : log (5 * log t) = log 5 + log (log t) := by
      rw [Real.log_mul (by norm_num) (show (0 : ℝ) < log t by linarith [hlog9, hlogt]).ne']
    rw [h1]; linarith [h2, h3]
  -- Assemble.
  calc ∑ j ∈ Finset.Icc A B, 1 / ((j : ℝ) * log (log (j : ℝ)))
      ≤ (1 / log (log (A : ℝ))) * ∑ j ∈ Finset.Icc A B, 1 / (j : ℝ) := hpull
    _ ≤ (1 / log (log (A : ℝ))) * (1 / (A : ℝ) + (log (B : ℝ) - log (A : ℝ))) :=
        mul_le_mul_of_nonneg_left hharm (le_of_lt (div_pos one_pos hllApos))
    _ ≤ (1 / log (log (A : ℝ))) * (1 / 9 + (log 5 + log (log t))) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (div_pos one_pos hllApos))
        have h1A : 1 / (A : ℝ) ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) hA9
        linarith [hlogBA, h1A]
    _ ≤ 1 + (1 / 9 + log 5) / log (log 9) := by
        have hexp : (1 / log (log (A : ℝ))) * (1 / 9 + (log 5 + log (log t)))
            = (1 / log (log (A : ℝ))) * (1 / 9 + log 5)
              + (1 / log (log (A : ℝ))) * log (log t) := by ring
        rw [hexp]
        have hR0 : (0 : ℝ) ≤ 1 / 9 + log 5 := by
          have : (0 : ℝ) ≤ log 5 := Real.log_nonneg (by norm_num)
          linarith
        have hPQ : (1 / log (log (A : ℝ))) * log (log t) ≤ 1 := by
          rw [one_div_mul_eq_div, div_le_one hllApos]; exact hlltA
        have hPR : (1 / log (log (A : ℝ))) * (1 / 9 + log 5)
            ≤ (1 / 9 + log 5) / log (log 9) := by
          rw [one_div_mul_eq_div, div_le_div_iff₀ hllApos hll9]
          nlinarith [mul_nonneg hR0
            (by linarith [hllA] : (0 : ℝ) ≤ log (log (A : ℝ)) - log (log 9))]
        linarith [hPQ, hPR]

/-- **The inner sum is bounded uniformly in `t = y²`.** For every `t`, the medium-band index sum
`∑_{j : t ≤ j < t log(j+2), j ≥ 3} 1/(j log log j) ≤ C` with a single constant `C`. Small `t` land
in the fixed finite range `Icc 3 647`; large `t` (`≥ 9`) use `medium_sum_Icc_big`. -/
lemma medium_inner_tsum_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (n : ℕ),
    ∑ j ∈ Finset.range n, (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
      then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) ≤ C := by
  have hloglogpos : ∀ j : ℕ, 3 ≤ j → 0 < log (log (j : ℝ)) := by
    intro j hj
    have hjR : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    refine Real.log_pos ?_
    calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
      _ < log 3 := Real.log_lt_log (exp_pos 1) (lt_trans Real.exp_one_lt_d9 (by norm_num))
      _ ≤ log (j : ℝ) := Real.log_le_log (by norm_num) hjR
  have hGnn : ∀ j : ℕ, 3 ≤ j → 0 ≤ 1 / ((j : ℝ) * log (log (j : ℝ))) := by
    intro j hj
    have h := hloglogpos j hj
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    positivity
  refine ⟨max (∑ j ∈ Finset.Icc (3 : ℕ) 647, 1 / ((j : ℝ) * log (log (j : ℝ))))
    (1 + (1 / 9 + log 5) / log (log 9)), ?_, ?_⟩
  · exact le_trans (Finset.sum_nonneg fun j hj ↦ hGnn j (Finset.mem_Icc.mp hj).1) (le_max_left _ _)
  intro t n
  have hfnn : ∀ j : ℕ, 0 ≤ (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
      then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) := by
    intro j; split_ifs with hc
    · exact hGnn j hc.1
    · exact le_refl 0
  by_cases ht9 : 9 ≤ t
  · -- big case: support in `Icc ⌈t⌉₊ ⌈t(log 9 + 2 log t)⌉₊`
    have hsqrt2 : √2 ≤ t :=
      le_trans (by nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
        Real.sqrt_nonneg (2 : ℝ)]) ht9
    have hA3 : 3 ≤ ⌈t⌉₊ := by
      have : (3 : ℝ) ≤ (⌈t⌉₊ : ℝ) := le_trans (by norm_num) (le_trans ht9 (Nat.le_ceil t))
      exact_mod_cast this
    have hsupp : ∀ j ∉ Finset.Icc ⌈t⌉₊ ⌈t * (log 9 + 2 * log t)⌉₊,
        (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
          then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) = 0 := by
      intro j hj
      split_ifs with hc
      · refine absurd (?_ : j ∈ _) hj
        rw [Finset.mem_Icc]
        obtain ⟨hj3, hjt, hjlt⟩ := hc
        refine ⟨Nat.ceil_le.mpr hjt, ?_⟩
        have htight : (j : ℝ) < t * (log 9 + 2 * log t) := medium_tight hsqrt2 (by omega) hjt hjlt
        have : (j : ℝ) < (⌈t * (log 9 + 2 * log t)⌉₊ : ℝ) := lt_of_lt_of_le htight (Nat.le_ceil _)
        exact le_of_lt (by exact_mod_cast this)
      · rfl
    calc ∑ j ∈ Finset.range n, (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
          then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0)
        = ∑ j ∈ Finset.range n ∩ Finset.Icc ⌈t⌉₊ ⌈t * (log 9 + 2 * log t)⌉₊,
            (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
              then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) :=
          (Finset.sum_subset Finset.inter_subset_left fun x hx hxni ↦
            hsupp x fun hxI ↦ hxni (Finset.mem_inter.mpr ⟨hx, hxI⟩)).symm
      _ ≤ ∑ j ∈ Finset.Icc ⌈t⌉₊ ⌈t * (log 9 + 2 * log t)⌉₊,
            (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
              then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun i _ _ ↦ hfnn i
      _ ≤ ∑ j ∈ Finset.Icc ⌈t⌉₊ ⌈t * (log 9 + 2 * log t)⌉₊, 1 / ((j : ℝ) * log (log (j : ℝ))) := by
          refine Finset.sum_le_sum (fun j hj ↦ ?_)
          split_ifs with hc
          · exact le_refl _
          · exact hGnn j (le_trans hA3 (Finset.mem_Icc.mp hj).1)
      _ ≤ 1 + (1 / 9 + log 5) / log (log 9) := medium_sum_Icc_big ht9
      _ ≤ _ := le_max_right _ _
  · -- small case: support in `Icc 3 647`
    rw [not_le] at ht9
    have hsupp : ∀ j ∉ Finset.Icc (3 : ℕ) 647,
        (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
          then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) = 0 := by
      intro j hj
      split_ifs with hc
      · refine absurd (?_ : j ∈ _) hj
        rw [Finset.mem_Icc]
        obtain ⟨hj3, hjt, hjlt⟩ := hc
        refine ⟨hj3, ?_⟩
        have hj3R : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
        have hlogpos : 0 ≤ log ((j : ℝ) + 2) := Real.log_nonneg (by linarith)
        have htpos : 0 < t := by
          by_contra h
          rw [not_lt] at h
          have := mul_nonpos_of_nonpos_of_nonneg h hlogpos
          linarith [hjlt]
        have hcrude : (j : ℝ) < 8 * t ^ 2 := medium_crude (by omega) hjt hjlt
        have hj648 : (j : ℝ) < 648 := by nlinarith [hcrude, ht9, htpos]
        have hj648N : j < 648 := by exact_mod_cast hj648
        omega
      · rfl
    calc ∑ j ∈ Finset.range n, (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
          then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0)
        = ∑ j ∈ Finset.range n ∩ Finset.Icc (3 : ℕ) 647,
            (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
              then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) :=
          (Finset.sum_subset Finset.inter_subset_left fun x hx hxni ↦
            hsupp x fun hxI ↦ hxni (Finset.mem_inter.mpr ⟨hx, hxI⟩)).symm
      _ ≤ ∑ j ∈ Finset.Icc (3 : ℕ) 647,
            (if 3 ≤ j ∧ t ≤ (j : ℝ) ∧ (j : ℝ) < t * log ((j : ℝ) + 2)
              then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun i _ _ ↦ hfnn i
      _ ≤ ∑ j ∈ Finset.Icc (3 : ℕ) 647, 1 / ((j : ℝ) * log (log (j : ℝ))) := by
          refine Finset.sum_le_sum (fun j hj ↦ ?_)
          split_ifs with hc
          · exact le_refl _
          · exact hGnn j (Finset.mem_Icc.mp hj).1
      _ ≤ _ := le_max_left _ _

/-- **Medium-band variance series (Tonelli wrapper).** For measurable `X` with `X²` integrable, the
truncated-band second moments summed with the LIL weight are `≤ C·E[X²]`:
`∑_j (∫ X² 𝟙{√(j/log(j+2)) < |X| ≤ √j})/(j log log j) ≤ C·∫X²`, and the series is summable. By
finite-sum linearity `∑_{j<n} … = ∫ X²·∑_{j<n}𝟙{…}/(j log log j)`, the inner sum is `≤ C` pointwise
(`medium_inner_tsum_le` at `t = X(ω)²`, since `√(j/log(j+2)) < |x| ≤ √j ⟺ x² ≤ j < x² log(j+2)`), so
each partial sum is `≤ C·∫X²`; `summable_of_sum_range_le` / `Real.tsum_le_of_sum_range_le` finish.
With `Var(Y_j^M) ≤ E[(Y_j^M)²] = E[X² 𝟙{…}]` (identical distribution) this gives the summability of
the medium-band variance series. -/
lemma medium_variance_series_le {X : Ω → ℝ} (hX : Measurable X)
    (hX2 : MemLp X 2 μ) :
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun j : ℕ ↦ if 3 ≤ j then
        (∫ ω, Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
          (X · ^ 2) ω ∂μ) / ((j : ℝ) * log (log (j : ℝ))) else 0) ∧
      ∑' j : ℕ, (if 3 ≤ j then
        (∫ ω, Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
          (X · ^ 2) ω ∂μ) / ((j : ℝ) * log (log (j : ℝ))) else 0)
        ≤ C * ∫ ω, X ω ^ 2 ∂μ := by
  obtain ⟨C, hC0, hCbound⟩ := medium_inner_tsum_le
  have hloglogpos : ∀ j : ℕ, 3 ≤ j → 0 < log (log (j : ℝ)) := by
    intro j hj
    have hjR : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    refine Real.log_pos ?_
    calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
      _ < log 3 := Real.log_lt_log (exp_pos 1) (lt_trans Real.exp_one_lt_d9 (by norm_num))
      _ ≤ log (j : ℝ) := Real.log_le_log (by norm_num) hjR
  have hXabs : Measurable (fun ω ↦ |X ω|) := continuous_abs.measurable.comp hX
  have hSmeas : ∀ j : ℕ,
      MeasurableSet {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)} := fun j ↦
    (measurableSet_lt measurable_const hXabs).inter (measurableSet_le hXabs measurable_const)
  have hSiff : ∀ (j : ℕ) (ω : Ω),
      ω ∈ {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
        ↔ (X ω ^ 2 ≤ (j : ℝ) ∧ (j : ℝ) < X ω ^ 2 * log ((j : ℝ) + 2)) := by
    intro j ω
    have hlogpos : (0 : ℝ) < log ((j : ℝ) + 2) :=
      Real.log_pos (by have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith)
    have harg : (0 : ℝ) ≤ (j : ℝ) / log ((j : ℝ) + 2) := div_nonneg (Nat.cast_nonneg j) hlogpos.le
    simp only [Set.mem_ofPred_eq]
    rw [Real.sqrt_lt harg (abs_nonneg _), Real.le_sqrt (abs_nonneg _) (Nat.cast_nonneg j)]
    simp only [sq_abs]
    rw [div_lt_iff₀ hlogpos]
    tauto
  set m : ℕ → Ω → ℝ := fun j ω ↦ if 3 ≤ j then
    Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
      (X · ^ 2) ω / ((j : ℝ) * log (log (j : ℝ))) else 0 with hm
  have hint_m : ∀ j, Integrable (m j) μ := fun j ↦ by
    simp only [hm]; by_cases hj3 : 3 ≤ j
    · simp only [ite_eq_left hj3]; exact (hX2.integrable_sq.indicator (hSmeas j)).div_const _
    · simp only [ite_eq_right hj3]; exact integrable_zero _ _ _
  set F : ℕ → ℝ := fun j ↦ if 3 ≤ j then
    (∫ ω, Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
      (X · ^ 2) ω ∂μ) / ((j : ℝ) * log (log (j : ℝ))) else 0 with hF
  have hFm : ∀ j, F j = ∫ ω, m j ω ∂μ := by
    intro j; simp only [hF, hm]; by_cases hj3 : 3 ≤ j
    · simp only [ite_eq_left hj3]; rw [integral_div]
    · simp only [ite_eq_right hj3, integral_zero]
  have hm_nn : ∀ j ω, 0 ≤ m j ω := by
    intro j ω; simp only [hm]; by_cases hj3 : 3 ≤ j
    · simp only [ite_eq_left hj3]
      have hll := hloglogpos j hj3
      have hjpos : (0 : ℝ) < (j : ℝ) := by
        have : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
        linarith
      exact div_nonneg (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _) (by positivity)
    · simp [ite_eq_right hj3]
  have hFnn : ∀ j, 0 ≤ F j := fun j ↦ by rw [hFm]; exact integral_nonneg (hm_nn j)
  have hptwise : ∀ (ω : Ω) (n : ℕ), ∑ j ∈ Finset.range n, m j ω ≤ C * X ω ^ 2 := by
    intro ω n
    have hfac : ∀ j : ℕ, m j ω = X ω ^ 2 * (if 3 ≤ j ∧ X ω ^ 2 ≤ (j : ℝ)
        ∧ (j : ℝ) < X ω ^ 2 * log ((j : ℝ) + 2) then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) := by
      intro j; simp only [hm]; by_cases hj3 : 3 ≤ j
      · rw [ite_eq_left hj3]
        by_cases hmem : ω ∈ {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
        · rw [Set.indicator_of_mem hmem, ite_eq_left ⟨hj3, (hSiff j ω).mp hmem⟩]; ring
        · rw [Set.indicator_of_notMem hmem, ite_eq_right (fun h ↦ hmem ((hSiff j ω).mpr h.2))]; ring
      · rw [ite_eq_right hj3, ite_eq_right (fun h ↦ hj3 h.1)]; ring
    calc ∑ j ∈ Finset.range n, m j ω
        = ∑ j ∈ Finset.range n, X ω ^ 2 * (if 3 ≤ j ∧ X ω ^ 2 ≤ (j : ℝ)
            ∧ (j : ℝ) < X ω ^ 2 * log ((j : ℝ) + 2)
              then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) :=
          Finset.sum_congr rfl (fun j _ ↦ hfac j)
      _ = X ω ^ 2 * ∑ j ∈ Finset.range n, (if 3 ≤ j ∧ X ω ^ 2 ≤ (j : ℝ)
            ∧ (j : ℝ) < X ω ^ 2 * log ((j : ℝ) + 2)
              then 1 / ((j : ℝ) * log (log (j : ℝ))) else 0) :=
          by rw [Finset.mul_sum]
      _ ≤ X ω ^ 2 * C := mul_le_mul_of_nonneg_left (hCbound (X ω ^ 2) n) (sq_nonneg _)
      _ = C * X ω ^ 2 := by ring
  have hbound : ∀ n, ∑ j ∈ Finset.range n, F j ≤ C * ∫ ω, X ω ^ 2 ∂μ := by
    intro n
    have h1 : ∑ j ∈ Finset.range n, F j = ∫ ω, ∑ j ∈ Finset.range n, m j ω ∂μ := by
      rw [integral_finsetSum (Finset.range n) (fun j _ ↦ hint_m j)]
      exact Finset.sum_congr rfl (fun j _ ↦ hFm j)
    rw [h1]
    have h2 : ∫ ω, ∑ j ∈ Finset.range n, m j ω ∂μ ≤ ∫ ω, C * X ω ^ 2 ∂μ :=
      integral_mono (integrable_finsetSum _ (fun j _ ↦ hint_m j)) (hX2.integrable_sq.const_mul C)
        (hptwise · n)
    rwa [integral_const_mul] at h2
  exact ⟨C, hC0, summable_of_sum_range_le hFnn hbound, Real.tsum_le_of_sum_range_le hFnn hbound⟩

/-- **Medium variance series is summable**, in the single-variable form.
`∑_{j≥3} Var(X 𝟙{√(j/log(j+2)) < |X| ≤ √j})/(j log log j) < ∞` under only `X² ∈ L¹`. Reduces to
`medium_variance_series_le` by `Var(X 𝟙_S) ≤ E[(X 𝟙_S)²] = E[X² 𝟙_S]` (`variance_le_expectation_sq`,
`(X 𝟙_S)² = X² 𝟙_S`) and comparison of nonnegative series. With identical distribution
(`Var(Y_j^M) = Var(Y_0 𝟙_{S_j})`) this is exactly the medium-band variance series. -/
lemma medium_variance_summable [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX2 : MemLp X 2 μ) :
    Summable (fun j : ℕ ↦ if 3 ≤ j then
      variance (Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)} X) μ
        / ((j : ℝ) * log (log (j : ℝ))) else 0) := by
  obtain ⟨C, hC0, hsummable, hbound⟩ := medium_variance_series_le hX hX2
  have hXabs : Measurable (fun ω ↦ |X ω|) := continuous_abs.measurable.comp hX
  have hSmeas : ∀ j : ℕ,
      MeasurableSet {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)} := fun j ↦
    (measurableSet_lt measurable_const hXabs).inter (measurableSet_le hXabs measurable_const)
  have hloglogpos : ∀ j : ℕ, 3 ≤ j → 0 < log (log (j : ℝ)) := by
    intro j hj
    have hjR : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    refine Real.log_pos ?_
    calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
      _ < log 3 := Real.log_lt_log (exp_pos 1) (lt_trans Real.exp_one_lt_d9 (by norm_num))
      _ ≤ log (j : ℝ) := Real.log_le_log (by norm_num) hjR
  have hVar_le : ∀ j : ℕ,
      variance (Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)} X) μ
        ≤ ∫ ω, Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
            (X · ^ 2) ω ∂μ := by
    intro j
    calc variance (Set.indicator {ω | _ ∧ _} X) μ
        ≤ ∫ ω, (Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
            X ω) ^ 2 ∂μ :=
          variance_le_expectation_sq (hX.indicator (hSmeas j)).aestronglyMeasurable
      _ = ∫ ω, Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
            (X · ^ 2) ω ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
          dsimp only
          by_cases h : ω ∈ {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)}
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
  refine Summable.of_nonneg_of_le (fun j ↦ ?_) (fun j ↦ ?_) hsummable
  · split_ifs with hj3
    · have hll := hloglogpos j hj3
      have hjpos : (0 : ℝ) < (j : ℝ) := by
        have h3 : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
        linarith
      exact div_nonneg (variance_nonneg _ _) (by positivity)
    · exact le_refl 0
  · split_ifs with hj3
    · have hll := hloglogpos j hj3
      have hjpos : (0 : ℝ) < (j : ℝ) := by
        have h3 : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
        linarith
      have hjL : (0 : ℝ) < (j : ℝ) * log (log (j : ℝ)) := mul_pos hjpos hll
      rw [div_le_div_iff₀ hjL hjL]
      exact mul_le_mul_of_nonneg_right (hVar_le j) hjL.le
    · exact le_refl 0

/-- The **medium truncation** on `ℝ`: `x ↦ x·𝟙{√(j/log(j+2)) < |x| ≤ √j}`, so `Y_j^{\mathrm M} =
mediumTrunc j ∘ Y_j`. As `Set.indicator (id)` of a measurable band it is measurable, and identical
distribution transfers its variance across the i.i.d. sequence. -/
noncomputable def mediumTrunc (j : ℕ) : ℝ → ℝ :=
  Set.indicator {x : ℝ | √((j : ℝ) / log ((j : ℝ) + 2)) < |x| ∧ |x| ≤ √(j : ℝ)} id

lemma measurable_mediumTrunc (j : ℕ) : Measurable (mediumTrunc j) :=
  measurable_id.indicator
    ((measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const))

/-- `mediumTrunc j ∘ X = X · 𝟙{√(j/log(j+2)) < |X| ≤ √j}` as an indicator over `Ω`. -/
@[specifies mediumTrunc "the band the truncation keeps, in the composed form the proofs actually \
use: strictly above the low cutoff `b_j` and at most the high cutoff `√j`, and `0` elsewhere. The \
strict/non-strict split at the two ends is what makes low, medium and high parts tile `ℝ`"]
lemma mediumTrunc_comp_eq {X : Ω → ℝ} (j : ℕ) :
    (fun ω ↦ mediumTrunc j (X ω))
      = Set.indicator {ω | √((j : ℝ) / log ((j : ℝ) + 2)) < |X ω| ∧ |X ω| ≤ √(j : ℝ)} X := by
  funext ω
  simp only [mediumTrunc, Set.indicator_apply, Set.mem_ofPred_eq, id_eq]

/-- **Medium variance series for the i.i.d. sequence.** For identically distributed `Y` with a bare
second moment, `∑_{j≥3} Var(Y_j^{\mathrm M})/(j log log j) < ∞`, where `Y_j^{\mathrm M} =
mediumTrunc j ∘ Y_j`. Reduces to `medium_variance_summable` (at `Y 0`) via
`IdentDistrib.variance_eq` applied to the measurable map `mediumTrunc j`
(`Var(mediumTrunc j ∘ Y_j) = Var(mediumTrunc j ∘ Y_0)`). -/
lemma medium_variance_summable_seq [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, Measurable (Y i)) (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hint2 : MemLp (Y 0) 2 μ) :
    Summable (fun j : ℕ ↦ if 3 ≤ j then
      variance (fun ω ↦ mediumTrunc j (Y j ω)) μ / ((j : ℝ) * log (log (j : ℝ))) else 0) := by
  refine (medium_variance_summable (hY 0) hint2).congr (fun j ↦ ?_)
  split_ifs with hj3
  · congr 1
    have hvar : variance (fun ω ↦ mediumTrunc j (Y j ω)) μ
        = variance (fun ω ↦ mediumTrunc j (Y 0 ω)) μ :=
      ((hident j).comp (measurable_mediumTrunc j)).variance_eq
    rw [hvar, mediumTrunc_comp_eq j]
  · rfl

/-- The medium truncation is bounded by the high cutoff `√j`. -/
@[specifies mediumTrunc "what makes it a *truncation* rather than a restriction: the result is \
bounded by `√j` uniformly in the argument, which is the hypothesis every increment bound needs"]
lemma abs_mediumTrunc_le (j : ℕ) (x : ℝ) : |mediumTrunc j x| ≤ √(j : ℝ) := by
  rw [mediumTrunc]
  by_cases h : x ∈ {x : ℝ | √((j : ℝ) / log ((j : ℝ) + 2)) < |x| ∧ |x| ≤ √(j : ℝ)}
  · rw [Set.indicator_of_mem h]; exact h.2
  · rw [Set.indicator_of_notMem h, abs_zero]; exact Real.sqrt_nonneg _

/-- The medium truncation of a strongly measurable variable is in `L²` (bounded by `√j`). -/
lemma memLp_two_mediumTrunc [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (j : ℕ) :
    MemLp (fun ω ↦ mediumTrunc j (Y j ω)) 2 μ :=
  MemLp.of_bound ((measurable_mediumTrunc j).comp (hY j).measurable).aestronglyMeasurable
    (√(j : ℝ)) (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_mediumTrunc_le j _)

/-- The centred medium truncation `mediumTrunc j ∘ Y_j − 𝔼[mediumTrunc j ∘ Y_j]` is strongly
measurable. -/
lemma stronglyMeasurable_centeredMedium {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i))
    (j : ℕ) :
    StronglyMeasurable (fun ω ↦ mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ) :=
  (((measurable_mediumTrunc j).comp (hY j).measurable).stronglyMeasurable).sub
    stronglyMeasurable_const

/-- **The medium-part martingale.** For independent `Y`, the centred medium truncations
`Y_j^{\mathrm M} - 𝔼 Y_j^{\mathrm M} = mediumTrunc j ∘ Y_j - 𝔼[mediumTrunc j ∘ Y_j]` sum to a
martingale `W_m = ∑_{j<m}(Y_j^{\mathrm M} - 𝔼 Y_j^{\mathrm M})` (via `martingale_iidSum`). -/
lemma martingale_centeredMedium [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ) :
    Martingale
      (fun n ↦ ∑ j ∈ Finset.range n,
        fun ω ↦ mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ)
      (natFiltLT _ (stronglyMeasurable_centeredMedium (μ := μ) hY)) μ :=
  martingale_iidSum (stronglyMeasurable_centeredMedium (μ := μ) hY)
    (hindep.comp (fun j x ↦ mediumTrunc j x - ∫ y, mediumTrunc j (Y j y) ∂μ)
      (fun j ↦ (measurable_mediumTrunc j).sub measurable_const))
    (fun j ↦ ((memLp_two_mediumTrunc hY j).integrable one_le_two).sub (integrable_const _))
    (fun j ↦ by
      rw [integral_sub ((memLp_two_mediumTrunc hY j).integrable one_le_two) (integrable_const _)]
      simp)

set_option maxHeartbeats 400000 in
-- The medium SLLN threads the weighted-series martingale, the discrete Itô isometry and the
-- variance-summability comparison through the general-weight SLLN; the accumulated elaboration
-- exceeds the default heartbeat budget.
/-- **The medium part is negligible.** For i.i.d. `Y` with a bare second moment,
`W_m = ∑_{j<m}(Y_j^{\mathrm M} − 𝔼 Y_j^{\mathrm M}) = o(√(m log log m))` a.s.: precisely,
`W_m / √(2(m+3) log log(m+3)) → 0` (and `√(2(m+3)L(m+3)) ∼ √(2m L(m))`). The medium martingale
`martingale_centeredMedium`, its `L²`-boundedness from the summable variance series
(`medium_variance_summable_seq`, discrete Itô isometry), and the general-weight SLLN
`martingale_div_weight_ae_tendsto_zero` (weight `a m = √(2(m+3)L(m+3))`) give the conclusion. -/
lemma ae_medium_div_weight_tendsto_zero [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ) (hint2 : MemLp (Y 0) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun m ↦
      (∑ j ∈ Finset.range m, (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
        / √(2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3)))) atTop (𝓝 0) := by
  classical
  set M : ℕ → Ω → ℝ := fun n ↦ ∑ j ∈ Finset.range n,
    fun ω ↦ mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ with hMdef
  set 𝒢 : Filtration ℕ m0 := natFiltLT _ (stronglyMeasurable_centeredMedium (μ := μ) hY) with h𝒢
  have hM : Martingale M 𝒢 μ := martingale_centeredMedium hY hindep
  -- The weight `a m = √(2(m+3) log log(m+3))`.
  have hll : ∀ m : ℕ, 0 < log (log ((m : ℝ) + 3)) := fun m ↦ by
    refine Real.log_pos ?_
    calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
      _ < log 3 := Real.log_lt_log (exp_pos 1) (lt_trans Real.exp_one_lt_d9 (by norm_num))
      _ ≤ log ((m : ℝ) + 3) := Real.log_le_log (by norm_num)
          (le_add_of_nonneg_left (Nat.cast_nonneg m))
  have hlog3 : (0 : ℝ) < log (log 3) := Real.log_pos (by
    calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
      _ < log 3 := Real.log_lt_log (exp_pos 1) (lt_trans Real.exp_one_lt_d9 (by norm_num)))
  set a : ℕ → ℝ := fun m ↦ √(2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3))) with hadef
  have harg : ∀ m : ℕ, 0 < 2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3)) := fun m ↦ by
    have := hll m; have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; positivity
  have ha_pos : ∀ m, 0 < a m := fun m ↦ by rw [hadef]; exact Real.sqrt_pos.mpr (harg m)
  have ha_sq : ∀ m, a m ^ 2 = 2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3)) := fun m ↦ by
    rw [hadef]; exact Real.sq_sqrt (harg m).le
  have ha_mono : Monotone a := by
    intro p q hpq
    rw [hadef]
    refine Real.sqrt_le_sqrt ?_
    have hpq3 : ((p : ℝ) + 3) ≤ ((q : ℝ) + 3) := by
      have : (p : ℝ) ≤ q := by exact_mod_cast hpq
      linarith
    have hllpq : log (log ((p : ℝ) + 3)) ≤ log (log ((q : ℝ) + 3)) :=
      loglog_le_loglog (le_add_of_nonneg_left (Nat.cast_nonneg p)) hpq3
    nlinarith [hpq3, hllpq, (hll p).le, (hll q).le, (by positivity : (0 : ℝ) ≤ (p : ℝ) + 3)]
  have ha_top : Tendsto a atTop atTop := by
    rw [hadef]
    refine Real.tendsto_sqrt_atTop.comp ?_
    have hlow : Tendsto (fun m : ℕ ↦ 2 * log (log 3) * ((m : ℝ) + 3)) atTop atTop :=
      Tendsto.const_mul_atTop (by linarith [hlog3])
        (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
    refine tendsto_atTop_mono (fun m ↦ ?_) hlow
    have hm3 : log (log 3) ≤ log (log ((m : ℝ) + 3)) :=
      loglog_le_loglog (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg m))
    nlinarith [hm3, hlog3, (by positivity : (0 : ℝ) ≤ (m : ℝ) + 3)]
  -- The weighted increment series.
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n, (M (k + 1) ω - M k ω) / a (k + 1) with hSdef
  have hSmart : Martingale S 𝒢 μ := martingale_weightedSeries hM (fun k ↦ a (k + 1))
  have hS0 : S 0 =ᵐ[μ] 0 := by filter_upwards with ω; simp [hSdef]
  have hincΔ : ∀ k ω, M (k + 1) ω - M k ω
      = mediumTrunc k (Y k ω) - ∫ x, mediumTrunc k (Y k x) ∂μ := fun k ω ↦ by
    simp only [hMdef, Finset.sum_apply, Finset.sum_range_succ]; ring
  have hdmem : ∀ k, MemLp (fun ω ↦ M (k + 1) ω - M k ω) 2 μ := fun k ↦ by
    have heq : (fun ω ↦ M (k + 1) ω - M k ω)
        = (fun ω ↦ mediumTrunc k (Y k ω) - ∫ x, mediumTrunc k (Y k x) ∂μ) := funext (hincΔ k)
    rw [heq]; exact (memLp_two_mediumTrunc hY k).sub (memLp_const _)
  have hDmem : ∀ k, MemLp (fun ω ↦ (M (k + 1) ω - M k ω) / a (k + 1)) 2 μ := fun k ↦ by
    simpa only [div_eq_inv_mul] using (hdmem k).const_mul (a (k + 1))⁻¹
  have hSmem : ∀ n, MemLp (S n) 2 μ := fun n ↦ memLp_finsetSum (Finset.range n) fun k _ ↦ hDmem k
  -- Discrete Itô isometry: `∫ (S n)² = ∑_{k<n} ∫ (ΔS_k)²`.
  have hsqeq : ∀ n, ∫ ω, (S n ω) ^ 2 ∂μ
      = ∑ k ∈ Finset.range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ := by
    intro n
    rw [integral_sq_eq_integral_predQuadVar hSmart.stronglyAdapted hSmem hS0 n]
    have e : ∑ k ∈ Finset.range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        = ∑ k ∈ Finset.range n,
            ((∫ ω, predQuadVar S 𝒢 μ (k + 1) ω ∂μ) - ∫ ω, predQuadVar S 𝒢 μ k ω ∂μ) :=
      Finset.sum_congr rfl fun k _ ↦
        (integral_predQuadVar_succ_sub hSmart hSmem k).symm
    rw [e, Finset.sum_range_sub (fun k ↦ ∫ ω, predQuadVar S 𝒢 μ k ω ∂μ) n]
    simp [predQuadVar_zero]
  -- Per-increment: `∫ (ΔS_k)² = Var(Y_k^M)/a(k+1)²`.
  have hbound : ∀ k, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
      = variance (fun ω ↦ mediumTrunc k (Y k ω)) μ / a (k + 1) ^ 2 := by
    intro k
    have hpt : ∀ ω, (S (k + 1) ω - S k ω) ^ 2
        = (M (k + 1) ω - M k ω) ^ 2 / a (k + 1) ^ 2 := fun ω ↦ by
      have hinc : S (k + 1) ω - S k ω = (M (k + 1) ω - M k ω) / a (k + 1) := by
        simp only [hSdef, Finset.sum_range_succ]; ring
      rw [hinc, div_pow]
    calc ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        = ∫ ω, (M (k + 1) ω - M k ω) ^ 2 / a (k + 1) ^ 2 ∂μ := integral_congr_ae (.of_forall hpt)
      _ = (∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ) / a (k + 1) ^ 2 := integral_div _ _
      _ = variance (fun ω ↦ mediumTrunc k (Y k ω)) μ / a (k + 1) ^ 2 := by
          rw [variance_eq_integral (X := fun ω ↦ mediumTrunc k (Y k ω))
            ((measurable_mediumTrunc k).comp (hY k).measurable).aemeasurable]
          congr 1
          exact integral_congr_ae (.of_forall fun ω ↦ by dsimp only; rw [hincΔ k ω])
  -- Summability of the variance series against `a(k+1)²`.
  have hsummable : Summable
      (fun k ↦ variance (fun ω ↦ mediumTrunc k (Y k ω)) μ / a (k + 1) ^ 2) := by
    rw [← summable_nat_add_iff 3]
    refine Summable.of_nonneg_of_le (fun n ↦ div_nonneg (variance_nonneg _ _) (sq_nonneg _))
      (fun n ↦ ?_)
      ((summable_nat_add_iff 3).mpr (medium_variance_summable_seq (fun i ↦ (hY i).measurable)
        hident hint2))
    rw [ite_eq_left (show 3 ≤ n + 3 by omega)]
    push_cast
    have hvnn : 0 ≤ variance (fun ω ↦ mediumTrunc (n + 3) (Y (n + 3) ω)) μ := variance_nonneg _ _
    have ha4_pos : (0 : ℝ) < a (n + 3 + 1) ^ 2 := by rw [ha_sq]; exact harg _
    have hden_pos : (0 : ℝ) < ((n : ℝ) + 3) * log (log ((n : ℝ) + 3)) :=
      mul_pos (by positivity) (hll n)
    have hden_le : ((n : ℝ) + 3) * log (log ((n : ℝ) + 3)) ≤ a (n + 3 + 1) ^ 2 := by
      rw [ha_sq]
      have hcast : ((n + 3 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by push_cast; ring
      rw [hcast]
      have h2 : log (log ((n : ℝ) + 3)) ≤ log (log ((n : ℝ) + 4 + 3)) :=
        loglog_le_loglog (le_add_of_nonneg_left (Nat.cast_nonneg n)) (by linarith)
      nlinarith [h2, hll n, (by positivity : (0 : ℝ) ≤ (n : ℝ) + 3)]
    rw [div_le_div_iff₀ ha4_pos hden_pos]
    exact mul_le_mul_of_nonneg_left hden_le hvnn
  -- Uniform second-moment bound.
  have hbdd : ∀ n, ∫ ω, (S n ω) ^ 2 ∂μ
      ≤ ∑' k, variance (fun ω ↦ mediumTrunc k (Y k ω)) μ / a (k + 1) ^ 2 := by
    intro n
    rw [hsqeq n]
    calc ∑ k ∈ Finset.range n, ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ
        = ∑ k ∈ Finset.range n, variance (fun ω ↦ mediumTrunc k (Y k ω)) μ / a (k + 1) ^ 2 :=
          Finset.sum_congr rfl fun k _ ↦ hbound k
      _ ≤ ∑' k, variance (fun ω ↦ mediumTrunc k (Y k ω)) μ / a (k + 1) ^ 2 :=
          hsummable.sum_le_tsum (Finset.range n)
            fun k _ ↦ div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  filter_upwards [martingale_div_weight_ae_tendsto_zero hM ha_pos ha_mono ha_top hSmem hbdd]
    with ω hω
  refine hω.congr (fun m ↦ ?_)
  simp only [hMdef, hadef, Finset.sum_apply]

/-- The log-level Hartman–Wintner low cutoff `b_j = √(j/log(j+2))`. -/
noncomputable def hwCutoff (j : ℕ) : ℝ := √((j : ℝ) / log ((j : ℝ) + 2))

/-- `x/log(x+2) < (x+1)/log(x+3)` strictly, for `x ≥ 0` (strict form of `div_log_add_two_le`). -/
lemma div_log_add_two_lt {x : ℝ} (hx : 0 ≤ x) : x / log (x + 2) < (x + 1) / log (x + 3) := by
  have hlog2 : (0 : ℝ) < log (x + 2) := log_pos (by linarith)
  have hlog3 : (0 : ℝ) < log (x + 3) := log_pos (by linarith)
  rw [div_lt_div_iff₀ hlog2 hlog3]
  have hkey : log (x + 3) - log (x + 2) ≤ 1 / (x + 2) := by
    rw [← log_div (show (0 : ℝ) < x + 3 by linarith).ne' (show (0 : ℝ) < x + 2 by linarith).ne',
      show (x + 3) / (x + 2) = 1 + 1 / (x + 2) by field_simp; ring]
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (x + 2) by positivity)
    linarith
  have hfrac : x / (x + 2) < log (x + 2) := by
    have h1 : (1 : ℝ) - 1 / (x + 2) < log (x + 2) := by
      have h := log_lt_sub_one_of_pos (show (0 : ℝ) < (x + 2)⁻¹ by positivity)
        (by intro h; have := inv_eq_one.mp h; linarith)
      rw [log_inv, inv_eq_one_div] at h; linarith
    have h2 : x / (x + 2) < 1 - 1 / (x + 2) := by
      rw [show (1 : ℝ) - 1 / (x + 2) = (x + 1) / (x + 2) by field_simp; ring,
        div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  have hm : x * (log (x + 3) - log (x + 2)) ≤ x / (x + 2) := by
    have := mul_le_mul_of_nonneg_left hkey hx; rwa [mul_one_div] at this
  nlinarith [hm, hfrac]

lemma strictMono_nat_div_log_add_two :
    StrictMono (fun i : ℕ ↦ (i : ℝ) / log ((i : ℝ) + 2)) := by
  refine strictMono_nat_of_lt_succ (fun i ↦ ?_)
  have h := div_log_add_two_lt (show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i)
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (i : ℝ) + 1 + 2 = (i : ℝ) + 3 by ring]
  exact h

/-- The log-level cutoff `b_j = √(j/log(j+2))` is strictly monotone. -/
@[specifies hwCutoff "the levels grow strictly, so the low truncations `(-b_j, b_j]` are nested \
and the boundary atoms `{-b_j}` are pairwise distinct — the fact the layered decomposition rests \
on"]
lemma strictMono_cutoff : StrictMono hwCutoff := by
  intro i j hij
  simp only [hwCutoff]
  refine Real.sqrt_lt_sqrt ?_ (strictMono_nat_div_log_add_two hij)
  exact div_nonneg (Nat.cast_nonneg i)
    (log_pos (by have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith)).le

lemma cutoff_nonneg (j : ℕ) : 0 ≤ hwCutoff j := Real.sqrt_nonneg _

lemma monotone_cutoff : Monotone hwCutoff := strictMono_cutoff.monotone

/-- `j ↦ -b_j` is injective (the singletons `{-b_j}` are pairwise distinct). -/
lemma injective_neg_cutoff : Function.Injective (fun j : ℕ ↦ -hwCutoff j) :=
  neg_injective.comp strictMono_cutoff.injective

/-- **Pointwise upper decomposition.** With `0 ≤ bj ≤ sj`, every real `x` is bounded above by the
sum of its low `(-bj,bj]`-truncation, its medium `{bj<|·|≤sj}`-part, and its high `{sj<|·|}`-part.
Equality holds except at `x = -bj` (where the LHS `-bj ≤ 0 =` RHS): the half-open low truncation and
the strict medium lower bound leave `-bj` uncovered, but the inequality still holds since `-bj ≤ 0`.
This is what lets the boundary atom be dropped when proving the Hartman–Wintner upper bound. -/
lemma le_lowMedHigh {bj sj x : ℝ} (hb : 0 ≤ bj) (hbs : bj ≤ sj) :
    x ≤ (Set.Ioc (-bj) bj).indicator id x
      + ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x
      + ({y : ℝ | sj < |y|}).indicator id x := by
  by_cases hR : sj < |x|
  · have e1 : (Set.Ioc (-bj) bj).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
      have : |x| ≤ bj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
    have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; rintro ⟨_, hxs⟩; linarith
    have e3 : ({y : ℝ | sj < |y|}).indicator id x = x :=
      Set.indicator_of_mem (by rw [Set.mem_ofPred_eq]; exact hR) id
    rw [e1, e2, e3]; simp
  · rw [not_lt] at hR
    by_cases hM : bj < |x|
    · have e1 : (Set.Ioc (-bj) bj).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
        have : |x| ≤ bj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
      have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = x :=
        Set.indicator_of_mem (by rw [Set.mem_ofPred_eq]; exact ⟨hM, hR⟩) id
      have e3 : ({y : ℝ | sj < |y|}).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; exact not_lt.mpr hR
      rw [e1, e2, e3]; simp
    · rw [not_lt] at hM
      have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; rintro ⟨h, _⟩; linarith
      have e3 : ({y : ℝ | sj < |y|}).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; intro h; linarith
      rw [e2, e3, add_zero, add_zero]
      by_cases hIoc : x ∈ Set.Ioc (-bj) bj
      · rw [Set.indicator_of_mem hIoc]; exact le_rfl
      · rw [Set.indicator_of_notMem hIoc]
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hIoc
        have hxabs := abs_le.mp hM
        rcases hIoc with h | h
        · exact h.trans (neg_nonpos.mpr hb)
        · linarith [hxabs.2]

/-- **Pointwise low+medium bound.** With `0 ≤ bj ≤ sj`, the low `(-bj,bj]`-truncation plus the
medium `{bj<|·|≤sj}`-part is at most the `(-sj,sj]`-truncation plus a boundary atom `bj` at `x=-bj`.
Integrating gives the Hartman–Wintner drift bound
`∫trunc(Y,b_j) + ∫Y^M ≤ ∫trunc(Y,√j) + b_j μ{Y=-b_j}`. -/
lemma lowMed_le {bj sj x : ℝ} (hb : 0 ≤ bj) (hbs : bj ≤ sj) :
    (Set.Ioc (-bj) bj).indicator id x + ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x
      ≤ (Set.Ioc (-sj) sj).indicator id x + (if x = -bj then bj else 0) := by
  by_cases hR : sj < |x|
  · have e1 : (Set.Ioc (-bj) bj).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
      have : |x| ≤ bj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
    have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; rintro ⟨_, hxs⟩; linarith
    have e3 : (Set.Ioc (-sj) sj).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
      have : |x| ≤ sj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
    have e4 : (if x = -bj then bj else 0) = 0 := by
      rw [ite_eq_right]; intro h; rw [h, abs_neg, abs_of_nonneg hb] at hR; linarith
    rw [e1, e2, e3, e4]
  · rw [not_lt] at hR
    by_cases hM : bj < |x|
    · have e1 : (Set.Ioc (-bj) bj).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
        have : |x| ≤ bj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
      have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = x :=
        Set.indicator_of_mem (by rw [Set.mem_ofPred_eq]; exact ⟨hM, hR⟩) id
      have e4 : (if x = -bj then bj else 0) = 0 := by
        rw [ite_eq_right]; intro h; rw [h, abs_neg, abs_of_nonneg hb] at hM; linarith
      rw [e1, e2, e4, zero_add, add_zero]
      by_cases hmem : x ∈ Set.Ioc (-sj) sj
      · rw [Set.indicator_of_mem hmem]; exact le_rfl
      · rw [Set.indicator_of_notMem hmem]
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hmem
        rcases hmem with h | h
        · linarith [hb, hbs]
        · linarith [le_abs_self x]
    · rw [not_lt] at hM
      have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; rintro ⟨h, _⟩; linarith
      rw [e2, add_zero]
      by_cases hbmem : x ∈ Set.Ioc (-bj) bj
      · rw [Set.indicator_of_mem hbmem]
        have hxmem : x ∈ Set.Ioc (-sj) sj := by
          rw [Set.mem_Ioc] at hbmem ⊢
          exact ⟨by linarith [hbmem.1], by linarith [hbmem.2]⟩
        rw [Set.indicator_of_mem hxmem]
        have hatomnn : (0 : ℝ) ≤ (if x = -bj then bj else 0) := by split_ifs; exacts [hb, le_rfl]
        simp only [id_eq]; linarith
      · rw [Set.indicator_of_notMem hbmem]
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hbmem
        have hxabs := abs_le.mp hM
        have hxeq : x = -bj := by
          rcases hbmem with h | h
          · linarith [hxabs.1]
          · linarith [hxabs.2]
        rw [ite_eq_left hxeq]
        by_cases hmem : x ∈ Set.Ioc (-sj) sj
        · rw [Set.indicator_of_mem hmem, hxeq]; simp
        · rw [Set.indicator_of_notMem hmem]; simpa using hb

/-- **Atom-sum bound.** For identically distributed `Y` with `E|Y_0| < ∞`, the boundary atoms at
`-b_j` (`b_j = √(j/log(j+2))`) contribute a uniformly bounded total:
`∑_{j<m} b_j · μ{Y_j = -b_j} ≤ E|Y_0|`. Since `b_j` are distinct (`injective_neg_cutoff`), the
events `{Y_0 = -b_j}` are disjoint, and on `{Y_0 = -b_j}` we have `|Y_0| = b_j`, so
`b_j μ{Y_0=-b_j} = ∫_{Y_0=-b_j}|Y_0|` and the disjoint sum is `≤ ∫|Y_0|`. This lets the boundary
term be absorbed into the (deterministic) Hartman–Wintner drift. -/
lemma sum_atom_le {Y : ℕ → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hint : Integrable (fun ω ↦ |Y 0 ω|) μ) (m : ℕ) :
    ∑ j ∈ Finset.range m, hwCutoff j * (μ {ω | Y j ω = -hwCutoff j}).toReal
      ≤ ∫ ω, |Y 0 ω| ∂μ := by
  set A : ℕ → Set Ω := fun j ↦ Y 0 ⁻¹' {-hwCutoff j} with hAdef
  have hAmeas : ∀ j, MeasurableSet (A j) := fun j ↦ hY 0 (measurableSet_singleton _)
  have hmeas_eq : ∀ j, (μ {ω | Y j ω = -hwCutoff j}).toReal = (μ (A j)).toReal := by
    intro j; congr 1
    rw [show {ω | Y j ω = -hwCutoff j} = Y j ⁻¹' {-hwCutoff j} by ext ω; simp,
      (hident j).measure_mem_eq (measurableSet_singleton (-hwCutoff j))]
  have hdisj : Pairwise fun i j ↦ Disjoint (A i) (A j) := by
    intro i j hij
    refine Set.disjoint_left.mpr (fun ω hωi hωj ↦ hij ?_)
    simp only [hAdef, Set.mem_preimage, Set.mem_singleton_iff] at hωi hωj
    exact injective_neg_cutoff (by rw [← hωi, ← hωj] : -hwCutoff i = -hwCutoff j)
  have hInt : IntegrableOn (fun ω ↦ |Y 0 ω|) (⋃ j, A j) μ := hint.integrableOn
  have hsum := hasSum_integral_iUnion hAmeas hdisj hInt
  have hterm : ∀ j, ∫ ω in A j, |Y 0 ω| ∂μ = hwCutoff j * (μ (A j)).toReal := by
    intro j
    have heqon : Set.EqOn (fun ω ↦ |Y 0 ω|) (fun _ ↦ hwCutoff j) (A j) := by
      intro ω hω
      simp only [hAdef, Set.mem_preimage, Set.mem_singleton_iff] at hω
      simp only [hω, abs_neg]
      exact abs_of_nonneg (cutoff_nonneg j)
    rw [setIntegral_congr_fun (hAmeas j) heqon, setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  have hnn : ∀ j, 0 ≤ ∫ ω in A j, |Y 0 ω| ∂μ := fun j ↦ by
    rw [hterm]; exact mul_nonneg (cutoff_nonneg j) ENNReal.toReal_nonneg
  calc ∑ j ∈ Finset.range m, hwCutoff j * (μ {ω | Y j ω = -hwCutoff j}).toReal
      = ∑ j ∈ Finset.range m, ∫ ω in A j, |Y 0 ω| ∂μ :=
        Finset.sum_congr rfl (fun j _ ↦ by rw [hmeas_eq j, hterm j])
    _ ≤ ∑' j, ∫ ω in A j, |Y 0 ω| ∂μ := hsum.summable.sum_le_tsum _ (fun j _ ↦ hnn j)
    _ = ∫ ω in ⋃ j, A j, |Y 0 ω| ∂μ := hsum.tsum_eq
    _ ≤ ∫ ω, |Y 0 ω| ∂μ :=
        setIntegral_le_integral hint (Eventually.of_forall (fun ω ↦ abs_nonneg _))

/-- `1 ≤ log(j+2)` for `j ≥ 1` (since `j+2 ≥ 3 > e`). -/
lemma one_le_log_add_two {j : ℕ} (hj : 1 ≤ j) : (1 : ℝ) ≤ log ((j : ℝ) + 2) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
    _ ≤ log ((j : ℝ) + 2) := Real.log_le_log (exp_pos 1) (by linarith [Real.exp_one_lt_d9])

/-- **Condition (H) for the log-level cutoff.** `b_n √(loglog n / n) → 0`, since
`b_n √(loglog n/n) = √(loglog n / log(n+2)) → 0` as `loglog n ≪ log(n+2)`. -/
lemma cutoff_condH :
    Tendsto (fun n : ℕ ↦ hwCutoff n * √(log (log n) / n)) atTop (𝓝 0) := by
  simp only [hwCutoff]
  have hlogdiv : Tendsto (fun x : ℝ ↦ log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hg2 : Tendsto (fun n : ℕ ↦ log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hub0 : Tendsto (fun n : ℕ ↦ log (log ((n : ℝ) + 2)) / log ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlogdiv.comp hg2
  have hubsqrt : Tendsto (fun n : ℕ ↦ √(log (log ((n : ℝ) + 2)) / log ((n : ℝ) + 2)))
      atTop (𝓝 0) := by
    have hcont : Tendsto (fun t : ℝ ↦ √t) (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    simpa [Function.comp_def] using hcont.comp hub0
  refine squeeze_zero' ?_ ?_ hubsqrt
  · filter_upwards [eventually_ge_atTop 3] with n _hn; positivity
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : 1 < log (n : ℝ) := by
      calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
        _ < log (n : ℝ) := Real.log_lt_log (exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn2pos : (0 : ℝ) < log ((n : ℝ) + 2) := log_pos (by linarith)
    have hprod : √((n : ℝ) / log ((n : ℝ) + 2)) * √(log (log n) / n)
        = √(log (log n) / log ((n : ℝ) + 2)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    rw [hprod]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff_of_pos_right hlogn2pos]
    exact loglog_le_loglog hn3 (by linarith)

/-- `b_j ≤ √j`: the low cutoff is below the high cutoff. -/
@[specifies hwCutoff "the ordering that makes `b_j` the *low* cutoff: it never overtakes the high \
cutoff `√j`, so the medium band `(b_j, √j]` is non-degenerate"]
lemma cutoff_le_sqrt (j : ℕ) : hwCutoff j ≤ √(j : ℝ) := by
  rw [hwCutoff]
  refine Real.sqrt_le_sqrt ?_
  rcases Nat.eq_zero_or_pos j with hj | hj
  · simp [hj]
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hlog := one_le_log_add_two hj
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log ((j : ℝ) + 2))]
    nlinarith

-- === ratio helpers ===
lemma tendsto_loglog_atTop : Tendsto (fun m : ℕ ↦ log (log (m : ℝ))) atTop atTop := by
  simpa [Function.comp_def] using
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma tendsto_hwWeight_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ ↦ √(2 * c * (m : ℝ) * log (log (m : ℝ)))) atTop atTop := by
  have hmL : Tendsto (fun m : ℕ ↦ (m : ℝ) * log (log (m : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ tendsto_loglog_atTop
  have h : Tendsto (fun m : ℕ ↦ 2 * c * (m : ℝ) * log (log (m : ℝ))) atTop atTop := by
    have h2c := Tendsto.const_mul_atTop (r := 2 * c) (by positivity) hmL
    exact h2c.congr fun m => by ring
  simpa [Function.comp_def] using Real.tendsto_sqrt_atTop.comp h

lemma tendsto_sqrt_div_hwWeight {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ ↦ √(m : ℝ) / √(2 * c * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
  have hLL : Tendsto (fun m : ℕ ↦ 2 * c * log (log (m : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop (r := 2 * c) (by positivity) tendsto_loglog_atTop
  have hsqrt : Tendsto (fun m : ℕ ↦ √(2 * c * log (log (m : ℝ)))) atTop atTop := by
    simpa [Function.comp_def] using Real.tendsto_sqrt_atTop.comp hLL
  have hinv : Tendsto (fun m : ℕ ↦ (√(2 * c * log (log (m : ℝ))))⁻¹) atTop (𝓝 0) :=
    hsqrt.inv_tendsto_atTop
  have key : ∀ᶠ m : ℕ in atTop,
      √(m : ℝ) / √(2 * c * (m : ℝ) * log (log (m : ℝ)))
        = (√(2 * c * log (log (m : ℝ))))⁻¹ := by
    filter_upwards [eventually_ge_atTop 3] with m hm
    have h3m : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hlog3 : (1 : ℝ) < log 3 := by
      have he : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
      calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
        _ < log 3 := Real.log_lt_log (exp_pos 1) he
    have hlogm : (1 : ℝ) < log (m : ℝ) :=
      lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) h3m)
    have hLpos : 0 < log (log (m : ℝ)) := Real.log_pos hlogm
    have hcoef : 0 ≤ 2 * c * log (log (m : ℝ)) := mul_nonneg (by positivity) hLpos.le
    have hmne : √(m : ℝ) ≠ 0 := by rw [Real.sqrt_ne_zero']; linarith
    have harg : 2 * c * log (log (m : ℝ)) * (m : ℝ)
        = 2 * c * (m : ℝ) * log (log (m : ℝ)) := by ring
    rw [← harg, Real.sqrt_mul hcoef, mul_comm (√(2 * c * log (log (m : ℝ)))) (√(m : ℝ)),
      ← div_div, div_self hmne, one_div]
  exact hinv.congr' (key.mono fun m h => h.symm)

lemma mediumWeight_le_hwWeight {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      √(2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3)))
        ≤ (2 / √c) * √(2 * c * (m : ℝ) * log (log (m : ℝ))) := by
  filter_upwards [eventually_ge_atTop 21] with m hm
  have h21m : (21 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hexp3 : exp 3 < 21 := by
    have hb : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hb]
    calc exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 3
      _ < 21 := by norm_num
  have hlog3m : (3 : ℝ) ≤ log (m : ℝ) := by
    rw [← Real.log_exp 3]; exact Real.log_le_log (exp_pos 3) (by linarith)
  have hlogm_pos : 0 < log (m : ℝ) := by linarith
  have hlogm3_pos : 0 < log ((m : ℝ) + 3) := Real.log_pos (by linarith)
  have hcube : (m : ℝ) + 3 ≤ (m : ℝ) ^ 3 := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) - 21 := by linarith
    nlinarith [h0, mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
  have hlog_le : log ((m : ℝ) + 3) ≤ 3 * log (m : ℝ) := by
    have h := Real.log_le_log (by positivity) hcube
    rw [Real.log_pow] at h; push_cast at h; linarith
  have hLm3_le : log (log ((m : ℝ) + 3)) ≤ log 3 + log (log (m : ℝ)) := by
    have h := Real.log_le_log hlogm3_pos hlog_le
    rwa [Real.log_mul (by norm_num) (ne_of_gt hlogm_pos)] at h
  have hlog3_le_Lm : log 3 ≤ log (log (m : ℝ)) := Real.log_le_log (by norm_num) hlog3m
  have hb : log (log ((m : ℝ) + 3)) ≤ 2 * log (log (m : ℝ)) := by linarith
  have hLm_nonneg : 0 ≤ log (log (m : ℝ)) := Real.log_nonneg (by linarith)
  have hlogm_le_m3 : log (m : ℝ) ≤ log ((m : ℝ) + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hLm3_nonneg : 0 ≤ log (log ((m : ℝ) + 3)) := Real.log_nonneg (by linarith)
  have ha : (m : ℝ) + 3 ≤ 2 * (m : ℝ) := by linarith
  have hstep : ((m : ℝ) + 3) * log (log ((m : ℝ) + 3))
      ≤ 4 * (m : ℝ) * log (log (m : ℝ)) := by
    have hmul := mul_le_mul ha hb hLm3_nonneg (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ))
    nlinarith [hmul]
  have hcoef4 : (0 : ℝ) ≤ 4 / c := by positivity
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hRHS : (2 / √c) * √(2 * c * (m : ℝ) * log (log (m : ℝ)))
      = √((4 / c) * (2 * c * (m : ℝ) * log (log (m : ℝ)))) := by
    rw [Real.sqrt_mul hcoef4, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4) c, hsqrt4]
  have hinner : 2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3))
      ≤ (4 / c) * (2 * c * (m : ℝ) * log (log (m : ℝ))) := by
    have hcc : (4 / c) * (2 * c * (m : ℝ) * log (log (m : ℝ)))
        = 8 * (m : ℝ) * log (log (m : ℝ)) := by field_simp; ring
    rw [hcc]; nlinarith [hstep]
  rw [hRHS]; exact Real.sqrt_le_sqrt hinner

/-- **Deterministic Hartman–Wintner drift bound.** `Drift_m = ∑_{j<m}(𝔼 Y_j^L + 𝔼 Y_j^M)
≤ 2σ²√m + 𝔼|Y_0|`: the low+medium truncated means, combined, are the `√j`-truncated mean up to the
boundary atom, bounded by the deterministic drift `2σ²√m` (`abs_sum_integral_truncation_le`) plus
the atom total `𝔼|Y_0|` (`sum_atom_le`). -/
lemma hw_drift_bound [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i))
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ) (hint2 : MemLp (Y 0) 2 μ)
    (hcent : ∫ ω, Y 0 ω ∂μ = 0) (m : ℕ) :
    ∑ j ∈ Finset.range m,
        (∫ x, truncation (Y j) (hwCutoff j) x ∂μ + ∫ x, mediumTrunc j (Y j x) ∂μ)
      ≤ 2 * (∫ x, Y 0 x ^ 2 ∂μ) * √(m : ℝ) + ∫ x, |Y 0 x| ∂μ := by
  have hmeasset : ∀ j, MeasurableSet {ω | Y j ω = -hwCutoff j} := fun j ↦
    (hY j).measurable (measurableSet_singleton _)
  have hcj_ej : ∀ j, ∫ x, truncation (Y j) (hwCutoff j) x ∂μ + ∫ x, mediumTrunc j (Y j x) ∂μ
      ≤ (∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ)
        + hwCutoff j * (μ {ω | Y j ω = -hwCutoff j}).toReal := by
    intro j
    have hint_low : Integrable (fun ω ↦ truncation (Y j) (hwCutoff j) ω) μ :=
      (hY j).aestronglyMeasurable.integrable_truncation
    have hint_med : Integrable (fun ω ↦ mediumTrunc j (Y j ω)) μ :=
      (memLp_two_mediumTrunc hY j).integrable one_le_two
    have hint_hi : Integrable (fun ω ↦ truncation (Y j) (√(j : ℝ)) ω) μ :=
      (hY j).aestronglyMeasurable.integrable_truncation
    have hint_atom : Integrable
        (fun ω ↦ ({ω | Y j ω = -hwCutoff j}).indicator (fun _ ↦ hwCutoff j) ω) μ :=
      (integrable_const (hwCutoff j)).indicator (hmeasset j)
    rw [← integral_add hint_low hint_med]
    have hptw : ∀ ω, truncation (Y j) (hwCutoff j) ω + mediumTrunc j (Y j ω)
        ≤ truncation (Y j) (√(j : ℝ)) ω
          + ({ω | Y j ω = -hwCutoff j}).indicator (fun _ ↦ hwCutoff j) ω := fun ω ↦
      lowMed_le (cutoff_nonneg j) (cutoff_le_sqrt j)
    calc ∫ ω, (truncation (Y j) (hwCutoff j) ω + mediumTrunc j (Y j ω)) ∂μ
        ≤ ∫ ω, (truncation (Y j) (√(j : ℝ)) ω
            + ({ω | Y j ω = -hwCutoff j}).indicator (fun _ ↦ hwCutoff j) ω) ∂μ :=
          integral_mono (hint_low.add hint_med) (hint_hi.add hint_atom) hptw
      _ = (∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ)
          + hwCutoff j * (μ {ω | Y j ω = -hwCutoff j}).toReal := by
        rw [integral_add hint_hi hint_atom, integral_indicator_const _ (hmeasset j),
          smul_eq_mul, mul_comm, measureReal_def]
  calc ∑ j ∈ Finset.range m,
        (∫ x, truncation (Y j) (hwCutoff j) x ∂μ + ∫ x, mediumTrunc j (Y j x) ∂μ)
      ≤ ∑ j ∈ Finset.range m, ((∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ)
          + hwCutoff j * (μ {ω | Y j ω = -hwCutoff j}).toReal) :=
        Finset.sum_le_sum (fun j _ ↦ hcj_ej j)
    _ = (∑ j ∈ Finset.range m, ∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ)
        + ∑ j ∈ Finset.range m, hwCutoff j * (μ {ω | Y j ω = -hwCutoff j}).toReal :=
        Finset.sum_add_distrib
    _ ≤ 2 * (∫ x, Y 0 x ^ 2 ∂μ) * √(m : ℝ) + ∫ x, |Y 0 x| ∂μ := by
        refine add_le_add ?_ (sum_atom_le (fun i ↦ (hY i).measurable) hident
          (hint2.integrable one_le_two).abs m)
        have heq : ∑ j ∈ Finset.range m, ∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ
            = ∑ j ∈ Finset.range m, ∫ x, truncation (Y 0) (√(j : ℝ)) x ∂μ :=
          Finset.sum_congr rfl fun j _ ↦
            ((hident j).comp (measurable_id.indicator measurableSet_Ioc)).integral_eq
        rw [heq]
        exact (le_abs_self _).trans (abs_sum_integral_truncation_le hint2 hcent m)

/-- **Hartman–Wintner upper bound, eventually form** (coboundedness-free core). For an i.i.d.,
centred, `L²` sequence, a.s. `∀ β>1`, eventually
`S_m = ∑_{j<m} Y_j ≤ β √(2σ² m log log m)` with `σ² = 𝔼[Y_0²]`. Combining the sharp low part
(`limsup ≤ 1`), the medium `o(√(m L(m)))`, the eventually-vanishing high part and the deterministic
drift.

No positivity of `σ²` is needed: if `σ² = 0` then every `Y_j` vanishes a.s. and both sides are `0`.
(The *limsup* form `iid_hartmanWintner_limsup_le_one` does need `σ² > 0`, since it divides by
`√(2σ² m log log m)`.) -/
lemma hw_eventually [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i))
    (hindep : iIndepFun Y μ) (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hint2 : MemLp (Y 0) 2 μ) (hcent : ∫ ω, Y 0 ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, ∀ β : ℝ, 1 < β → ∀ᶠ m in atTop,
      (∑ j ∈ Finset.range m, Y j ω)
        ≤ β * √(2 * (∫ x, Y 0 x ^ 2 ∂μ) * (m : ℝ) * log (log (m : ℝ))) := by
  rcases eq_or_lt_of_le (integral_nonneg (fun ω ↦ sq_nonneg (Y 0 ω)) :
      (0 : ℝ) ≤ ∫ ω, Y 0 ω ^ 2 ∂μ) with hσ | hσ
  · -- Degenerate case `σ² = 0`: every `Y j` vanishes a.s., and both sides are `0`.
    have hY0 : Y 0 =ᵐ[μ] 0 := by
      have hz := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun ω ↦ sq_nonneg (Y 0 ω)) hint2.integrable_sq).mp hσ.symm
      filter_upwards [hz] with ω hω
      have h2 : Y 0 ω ^ 2 = 0 := hω
      simpa using sq_eq_zero_iff.mp h2
    have hYj : ∀ j, Y j =ᵐ[μ] 0 := by
      intro j
      have h0 : μ (Y 0 ⁻¹' ({(0 : ℝ)}ᶜ)) = 0 := by
        simpa [Set.preimage, Pi.zero_apply] using ae_iff.mp hY0
      have hj : μ (Y j ⁻¹' ({(0 : ℝ)}ᶜ)) = 0 := by
        rw [(hident j).measure_mem_eq (measurableSet_singleton (0 : ℝ)).compl]; exact h0
      refine ae_iff.mpr ?_
      simpa [Set.preimage, Pi.zero_apply] using hj
    filter_upwards [ae_all_iff.mpr hYj] with ω hω β _
    filter_upwards with m
    rw [Finset.sum_eq_zero fun j _ ↦ hω j, ← hσ]
    simp
  set σ2 := ∫ x, Y 0 x ^ 2 ∂μ with hσ2def
  set K := ∫ x, |Y 0 x| ∂μ with hKdef
  have hint0 : Integrable (Y 0) μ := hint2.integrable one_le_two
  have hident2 : ∀ j, IdentDistrib (fun ω ↦ Y j ω ^ 2) (fun ω ↦ Y 0 ω ^ 2) μ μ := fun j ↦
    (hident j).comp (u := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  have hint_i : ∀ i, Integrable (Y i) μ := fun i ↦ ((hident i).integrable_iff).mpr hint0
  have hint2_i : ∀ i, MemLp (Y i) 2 μ := fun i ↦
    (memLp_two_iff_integrable_sq (hY i).aestronglyMeasurable).mpr
      (((hident2 i).integrable_iff).mpr hint2.integrable_sq)
  have hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2 := fun i ↦ le_of_eq (hident2 i).integral_eq
  have hdrift := hw_drift_bound hY hident hint2 hcent
  have ha_top : Tendsto (fun m : ℕ ↦ √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop atTop :=
    tendsto_hwWeight_atTop hσ
  have ha_pos : ∀ᶠ m : ℕ in atTop, 0 < √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) :=
    ha_top.eventually_gt_atTop 0
  have hw_pos : ∀ᶠ m : ℕ in atTop, 0 < √(2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3))) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hlt : (1 : ℝ) < log ((m : ℝ) + 3) := by
      calc (1 : ℝ) = log (exp 1) := (Real.log_exp 1).symm
        _ < log ((m : ℝ) + 3) := Real.log_lt_log (exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    exact Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) (by linarith)) (Real.log_pos hlt))
  filter_upwards [ae_eventually_abs_le_sqrt_nat_mul_loglog_centeredTruncation_sharp hY hindep
      hint2_i hσ hv (b := hwCutoff) monotone_cutoff cutoff_nonneg cutoff_condH,
    ae_medium_div_weight_tendsto_zero hY hindep hident hint2,
    ae_eventually_abs_le_sqrt_of_identDistrib (fun i ↦ (hY i).measurable) hident hint2]
    with ω hlowω hmedω hhighω
  intro β hβ
  have hβ₁1 : (1 : ℝ) < (1 + β) / 2 := by linarith
  have hβ₁β : (1 + β) / 2 < β := by linarith
  set β₁ := (1 + β) / 2 with hβ₁def
  -- Low part: `|S̃_m| ≤ β₁ a_m` eventually.
  have hlowβ : ∀ᶠ m in atTop, |∑ j ∈ Finset.range m,
      (truncation (Y j) (hwCutoff j) ω - ∫ x, truncation (Y j) (hwCutoff j) x ∂μ)|
        ≤ β₁ * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) := by
    filter_upwards [hlowω β₁ hβ₁1] with m hm
    rwa [Finset.sum_apply] at hm
  -- Medium part: `W_m / a_m → 0`.
  have hWa : Tendsto (fun m ↦ (∑ j ∈ Finset.range m,
      (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
        / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
    have hbound : Tendsto (fun m ↦ (2 / √σ2) * |(∑ j ∈ Finset.range m,
        (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
          / √(2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3)))|) atTop (𝓝 0) := by
      simpa using hmedω.abs.const_mul (2 / √σ2)
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [mediumWeight_le_hwWeight hσ, ha_pos, hw_pos] with m hwle hapos hwpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hapos, abs_div, abs_of_pos hwpos]
    rw [div_le_iff₀ hapos, mul_comm (2 / √σ2), mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hwpos]
    have hWnn : 0 ≤ |∑ j ∈ Finset.range m,
        (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ)| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hwle hWnn]
  -- High part: eventually constant, so `H_m / a_m → 0`.
  have hHa : Tendsto (fun m ↦ (∑ j ∈ Finset.range m,
      ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
        / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
    have hzero : ∀ᶠ j : ℕ in atTop,
        ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω) = 0 := by
      filter_upwards [hhighω] with j hj
      apply Set.indicator_of_notMem
      simp only [Set.mem_ofPred_eq, not_lt]; exact hj
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hzero
    have hconst : ∀ᶠ m : ℕ in atTop, (∑ j ∈ Finset.range m,
        ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
          = ∑ j ∈ Finset.range J, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω) := by
      filter_upwards [eventually_ge_atTop J] with m hm
      refine (Finset.sum_subset (fun x hx ↦ Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hm)) (fun j _ hjnr ↦ ?_)).symm
      exact hJ j (by simpa using hjnr)
    have hCa : Tendsto (fun m : ℕ ↦ (∑ j ∈ Finset.range J,
        ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
          / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using ha_top.inv_tendsto_atTop.const_mul
        (∑ j ∈ Finset.range J, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
    exact hCa.congr' (hconst.mono (fun m h ↦ by simp only [h]))
  -- Drift scale and constant `/ a_m → 0`.
  have hSqa : Tendsto (fun m : ℕ ↦ (2 * σ2 * √(m : ℝ))
      / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
    have h : Tendsto (fun m : ℕ ↦ 2 * σ2 * (√(m : ℝ)
        / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))))) atTop (𝓝 0) := by
      simpa using (tendsto_sqrt_div_hwWeight hσ (c := σ2)).const_mul (2 * σ2)
    exact Tendsto.congr (fun m ↦ (mul_div_assoc _ _ _).symm) h
  have hKa : Tendsto (fun m : ℕ ↦ K / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ha_top.inv_tendsto_atTop.const_mul K
  -- Combined remainder `/ a_m → 0`, hence eventually `≤ (β - β₁) a_m`.
  have hrembd : ∀ᶠ m in atTop, (∑ j ∈ Finset.range m,
      (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
      + (∑ j ∈ Finset.range m, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
      + 2 * σ2 * √(m : ℝ) + K ≤ (β - β₁) * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) := by
    have hrem : Tendsto (fun m ↦ ((∑ j ∈ Finset.range m,
        (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
        + (∑ j ∈ Finset.range m, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
        + 2 * σ2 * √(m : ℝ) + K) / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
      have h4 := ((hWa.add hHa).add hSqa).add hKa
      simp only [add_zero] at h4
      exact Tendsto.congr (fun m ↦ by ring) h4
    filter_upwards [hrem.eventually_lt_const (show (0 : ℝ) < β - β₁ by linarith), ha_pos]
      with m hm hapos
    rw [div_lt_iff₀ hapos] at hm
    linarith
  -- Pointwise decomposition bound.
  have hSbound : ∀ m, (∑ j ∈ Finset.range m, Y j ω)
      ≤ (∑ j ∈ Finset.range m,
          (truncation (Y j) (hwCutoff j) ω - ∫ x, truncation (Y j) (hwCutoff j) x ∂μ))
        + (∑ j ∈ Finset.range m,
            (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
        + (∑ j ∈ Finset.range m, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
        + (∑ j ∈ Finset.range m,
            (∫ x, truncation (Y j) (hwCutoff j) x ∂μ + ∫ x, mediumTrunc j (Y j x) ∂μ)) := by
    intro m
    calc (∑ j ∈ Finset.range m, Y j ω)
        ≤ ∑ j ∈ Finset.range m, (truncation (Y j) (hwCutoff j) ω + mediumTrunc j (Y j ω)
            + ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω)) :=
          Finset.sum_le_sum fun j _ ↦ le_lowMedHigh (cutoff_nonneg j) (cutoff_le_sqrt j)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring
  -- Assemble the eventual bound `S_m ≤ β a_m`.
  filter_upwards [hlowβ, hrembd] with m hlm hrm
  calc (∑ j ∈ Finset.range m, Y j ω)
      ≤ _ := hSbound m
    _ ≤ |∑ j ∈ Finset.range m,
          (truncation (Y j) (hwCutoff j) ω - ∫ x, truncation (Y j) (hwCutoff j) x ∂μ)|
        + ((∑ j ∈ Finset.range m,
            (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
          + (∑ j ∈ Finset.range m, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
          + 2 * σ2 * √(m : ℝ) + K) := by
        have := hdrift m; have := le_abs_self (∑ j ∈ Finset.range m,
          (truncation (Y j) (hwCutoff j) ω - ∫ x, truncation (Y j) (hwCutoff j) x ∂μ)); linarith
    _ ≤ β₁ * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))
        + (β - β₁) * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) := by linarith
    _ = β * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) := by ring

/-- **Sharp i.i.d. Hartman–Wintner LIL, upper half** (Hartman–Wintner 1941). For an i.i.d., centred,
`L²` sequence with `σ² = 𝔼[Y_0²] > 0`, almost surely
`limsup_m (∑_{j<m} Y_j) / √(2σ² m log log m) ≤ 1`. Assembled from the coboundedness-free eventual
bound `hw_eventually` applied to `Y` (upper bound) and to `-Y` (lower bound, giving coboundedness of
`S_m/a_m`), then `limsup_le_of_le`. -/
theorem iid_hartmanWintner_limsup_le_one [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hint2 : MemLp (Y 0) 2 μ) (hcent : ∫ ω, Y 0 ω ∂μ = 0)
    (hσ : 0 < ∫ ω, Y 0 ω ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, limsup (fun m ↦ (∑ j ∈ Finset.range m, Y j ω)
      / √(2 * (∫ x, Y 0 x ^ 2 ∂μ) * (m : ℝ) * log (log (m : ℝ)))) atTop ≤ 1 := by
  have hσeq : (∫ x, (-Y 0 x) ^ 2 ∂μ) = ∫ x, Y 0 x ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x ↦ neg_sq (Y 0 x))
  have ha_pos : ∀ᶠ m : ℕ in atTop,
      0 < √(2 * (∫ x, Y 0 x ^ 2 ∂μ) * (m : ℝ) * log (log (m : ℝ))) :=
    (tendsto_hwWeight_atTop hσ).eventually_gt_atTop 0
  have hY_ev := hw_eventually hY hindep hident hint2 hcent
  have hnegY_ev := hw_eventually (Y := fun i ω ↦ -Y i ω) (fun i ↦ (hY i).neg)
    (hindep.comp (fun _ ↦ (- ·)) (fun _ ↦ measurable_neg))
    (fun j ↦ (hident j).comp (u := fun x : ℝ ↦ -x) measurable_neg)
    hint2.neg
    (by simp only [integral_neg, hcent, neg_zero])
  simp only [hσeq] at hnegY_ev
  filter_upwards [hY_ev, hnegY_ev] with ω h1 h2
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun m ↦ (∑ j ∈ Finset.range m, Y j ω)
      / √(2 * (∫ x, Y 0 x ^ 2 ∂μ) * (m : ℝ) * log (log (m : ℝ)))) := by
    refine IsCoboundedUnder.of_frequently_ge (a := -2) (Eventually.frequently ?_)
    filter_upwards [h2 2 (by norm_num), ha_pos] with m hm hpos
    rw [le_div_iff₀ hpos]
    rw [Finset.sum_neg_distrib] at hm
    linarith
  refine le_of_forall_gt_imp_ge_of_dense (fun a ha ↦ ?_)
  refine limsup_le_of_le hcobdd ?_
  filter_upwards [h1 a ha, ha_pos] with m hm hpos
  rw [div_le_iff₀ hpos]
  exact hm

end AlphaRAR
