/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import AlphaRAR.Mathlib.StochasticOrder

/-!
# One-sided `o_p(√n)` deviation bounds

This file develops the "drift-sign" lemma used to turn the additive `U`-increment decomposition into
a one-sided `o_p(√n)` bound: if `X_n ≤ (n-ℓ_n)(-c + A_n) + B_n √n` with `c > 0` a constant, `A_n =
o_p(1)`, `B_n = o_p(1)` and `n - ℓ_n ≥ 0`, then the positive part `(X_n/√n)^+ = o_p(1)`, i.e.
`X_n ≤ o_p(√n)` one-sidedly. The negative drift `-c` eventually dominates the `o_p(1)` perturbation
(in probability), forcing the `(n-ℓ_n)`-term nonpositive.

## Main result

* `AlphaRAR.isLittleOpOne_max_div_sqrt_of_drift`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace AlphaRAR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Domination for `o_p(1)`.** If `|Z n| ≤ |Y n|` pointwise and `Y = o_p(1)`, then
`Z = o_p(1)`. -/
lemma IsLittleOpOne.of_abs_le {Y Z : ℕ → Ω → ℝ} (hZY : ∀ n ω, |Z n ω| ≤ |Y n ω|)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ Z := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hsub : ∀ n, μ {ω | ε ≤ |Z n ω|} ≤ μ {ω | ε ≤ |Y n ω|} := fun n ↦
    measure_mono fun ω hω ↦ le_trans hω (hZY n ω)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hY.tendsto_abs hε)
    (Eventually.of_forall fun n ↦ zero_le) (Eventually.of_forall hsub)

/-- **a.e. domination for `o_p(1)`.** If `|Z n| ≤ |Y n|` almost surely for each `n` and
`Y = o_p(1)`, then `Z = o_p(1)`. -/
lemma IsLittleOpOne.of_abs_le_ae {Y Z : ℕ → Ω → ℝ} (hZY : ∀ n, ∀ᵐ ω ∂μ, |Z n ω| ≤ |Y n ω|)
    (hY : IsLittleOpOne μ Y) : IsLittleOpOne μ Z := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hsub : ∀ n, μ {ω | ε ≤ |Z n ω|} ≤ μ {ω | ε ≤ |Y n ω|} := fun n ↦ by
    refine measure_mono_ae ?_
    filter_upwards [hZY n] with ω hω hεZ
    exact le_trans hεZ hω
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hY.tendsto_abs hε)
    (Eventually.of_forall fun n ↦ zero_le) (Eventually.of_forall hsub)

/-- **Eventual a.e. domination for `o_p(1)`.** If `|Z n| ≤ |Y n|` almost surely for all large `n`
and `Y = o_p(1)`, then `Z = o_p(1)` (`o_p` depends only on the tail). -/
lemma IsLittleOpOne.of_eventually_abs_le {Y Z : ℕ → Ω → ℝ}
    (hZY : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, |Z n ω| ≤ |Y n ω|) (hY : IsLittleOpOne μ Y) :
    IsLittleOpOne μ Z := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hbound : ∀ᶠ n in atTop, μ {ω | ε ≤ |Z n ω|} ≤ μ {ω | ε ≤ |Y n ω|} := by
    filter_upwards [hZY] with n hn
    refine measure_mono_ae ?_
    filter_upwards [hn] with ω hω hεZ
    exact le_trans hεZ hω
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hY.tendsto_abs hε)
    (Eventually.of_forall fun n ↦ zero_le) hbound

/-- `o_p(1)` is preserved by taking absolute values. -/
lemma IsLittleOpOne.abs {X : ℕ → Ω → ℝ} (hX : IsLittleOpOne μ X) :
    IsLittleOpOne μ (fun n ω ↦ |X n ω|) :=
  IsLittleOpOne.of_abs_le (fun _ _ ↦ le_of_eq (abs_abs _)) hX

/-- `o_p(1)` is preserved by multiplication by a constant. -/
lemma IsLittleOpOne.const_mul {X : ℕ → Ω → ℝ} (c : ℝ) (hX : IsLittleOpOne μ X) :
    IsLittleOpOne μ (fun n ω ↦ c * X n ω) := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    have hz : (fun n : ℕ ↦ μ {ω : Ω | ε ≤ |(0 : ℝ) * X n ω|}) = fun _ ↦ 0 := by
      funext n
      convert measure_empty (μ := μ)
      ext ω
      simp only [zero_mul, abs_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    rw [hz]; exact tendsto_const_nhds
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    refine (hX.tendsto_abs (div_pos hε hcpos)).congr fun n ↦ ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, abs_mul]
    rw [div_le_iff₀ hcpos, mul_comm]

/-- If `|X| = o_p(1)` then `X = o_p(1)`. -/
lemma isLittleOpOne_of_abs {X : ℕ → Ω → ℝ} (hX : IsLittleOpOne μ (fun n ω ↦ |X n ω|)) :
    IsLittleOpOne μ X :=
  IsLittleOpOne.of_abs_le (fun _ _ ↦ le_of_eq (abs_abs _).symm) hX

/-- The zero sequence is `o_p(1)`. -/
lemma isLittleOpOne_zero : IsLittleOpOne μ (fun _ _ ↦ (0 : ℝ)) := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hz : (fun n : ℕ ↦ μ {ω : Ω | ε ≤ |(fun _ _ ↦ (0 : ℝ)) n ω|}) = fun _ ↦ 0 := by
    funext n
    convert measure_empty (μ := μ)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, abs_zero]
    exact hε
  rw [hz]
  exact tendsto_const_nhds

/-- A constant over `√n` is `o_p(1)`. -/
lemma isLittleOpOne_const_div_sqrt [IsFiniteMeasure μ] (C : ℝ) :
    IsLittleOpOne μ (fun n (_ : Ω) ↦ C / √n) := by
  refine isLittleOpOne_of_tendsto_ae (fun n ↦ measurable_const.aestronglyMeasurable)
    (ae_of_all _ fun ω ↦ ?_)
  have hsqrt : Tendsto (fun n : ℕ ↦ √n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.div_atTop hsqrt

/-- **`O_p(1)` from an a.s. bound.** If, almost surely, the sequence `X_· ω` is bounded (by a
random constant), then `X = O_p(1)`. -/
lemma isBigOpOne_of_ae_bounded [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hmeas : ∀ n, Measurable (X n))
    (hbdd : ∀ᵐ ω ∂μ, ∃ B, ∀ n, |X n ω| ≤ B) : IsBigOpOne μ X := by
  intro ε hε
  set s : ℕ → Set Ω := fun M ↦ {ω | ∃ n, (M : ℝ) < |X n ω|} with hs
  have hsmeas : ∀ M, NullMeasurableSet (s M) μ := fun M ↦ by
    change NullMeasurableSet {ω | ∃ n, (M : ℝ) < |X n ω|} μ
    rw [Set.ofPred_exists]
    exact (MeasurableSet.iUnion fun n ↦
      measurableSet_lt measurable_const (hmeas n).abs).nullMeasurableSet
  have hsanti : Antitone s := by
    intro a b hab ω hω
    obtain ⟨n, hn⟩ := hω
    exact ⟨n, lt_of_le_of_lt (by exact_mod_cast hab) hn⟩
  have hinter0 : μ (⋂ M, s M) = 0 := by
    refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq (ae_iff.mp hbdd))) (zero_le)
    intro ω hω
    simp only [Set.mem_iInter] at hω
    rintro ⟨B, hB⟩
    obtain ⟨M, hM⟩ := exists_nat_ge B
    obtain ⟨n, hn⟩ := hω M
    exact absurd (le_trans (hB n) hM) (not_le.mpr hn)
  have htend := tendsto_measure_iInter_atTop hsmeas hsanti ⟨0, measure_ne_top μ _⟩
  rw [hinter0] at htend
  obtain ⟨M, hM⟩ := (htend.eventually (Iio_mem_nhds hε)).exists
  refine ⟨(M : ℝ), fun n ↦ le_trans (measure_mono ?_) hM.le⟩
  intro ω hω
  change ∃ n', (M : ℝ) < |X n' ω|
  exact ⟨n, hω⟩

/-- `o_p(1)` is closed under finite sums. -/
lemma isLittleOpOne_finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℕ → Ω → ℝ}
    (hf : ∀ j ∈ s, IsLittleOpOne μ (f j)) :
    IsLittleOpOne μ (fun n ω ↦ ∑ j ∈ s, f j n ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isLittleOpOne_zero
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- **Drift-sign one-sided `o_p(√n)`.** If eventually `X_n ≤ d_n(-c + A_n) + B_n √n` with `c > 0`,
`d_n ≥ 0`, and `A_n, B_n = o_p(1)`, then `(X_n/√n)^+ = o_p(1)`. The window `d_n = n - ℓ_n` need not
be bounded; only `d_n ≥ 0` and the negative drift `-c` are used. The decomposition need only hold
*eventually* (in `n`), since `o_p` depends only on the tail. -/
lemma isLittleOpOne_max_div_sqrt_of_drift {c : ℝ} (hc : 0 < c)
    {A B X d : ℕ → Ω → ℝ} (hA : IsLittleOpOne μ A) (hB : IsLittleOpOne μ B)
    (hd : ∀ n ω, 0 ≤ d n ω)
    (hX : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, X n ω ≤ d n ω * (-c + A n ω) + B n ω * √n) :
    IsLittleOpOne μ (fun n ω ↦ max (X n ω / √n) 0) := by
  apply isLittleOpOne_of_tendsto_abs
  intro ε hε
  have hbound : ∀ᶠ n in atTop, μ {ω | ε ≤ |max (X n ω / √n) 0|}
      ≤ μ {ω | c ≤ |A n ω|} + μ {ω | ε ≤ |B n ω|} := by
    filter_upwards [hX, eventually_ge_atTop 1] with n hXn hn
    refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
    filter_upwards [hXn] with ω hXω
    intro hω
    have hωval : ε ≤ |max (X n ω / √n) 0| := hω
    rw [abs_of_nonneg (le_max_right (X n ω / √n) 0)] at hωval
    change c ≤ |A n ω| ∨ ε ≤ |B n ω|
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    obtain ⟨hAc, hBε⟩ := hcon
    have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hAlt : A n ω < c := lt_of_abs_lt hAc
    have hdrift : d n ω * (-c + A n ω) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hd n ω) (by linarith)
    have hXle : X n ω ≤ B n ω * √n := by linarith [hXω]
    have hXdiv : X n ω / √n ≤ B n ω := (div_le_iff₀ hsn).mpr hXle
    have hBlt : B n ω < ε := lt_of_abs_lt hBε
    have hmax : max (X n ω / √n) 0 < ε :=
      max_lt_iff.mpr ⟨lt_of_le_of_lt hXdiv hBlt, hε⟩
    linarith
  have hsum : Tendsto (fun n ↦ μ {ω | c ≤ |A n ω|} + μ {ω | ε ≤ |B n ω|}) atTop (𝓝 0) := by
    simpa using (hA.tendsto_abs hc).add (hB.tendsto_abs hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun n ↦ zero_le)) hbound

/-- **Generic `U`-increment bound** (blueprint `lem:U_increment_bound`, `o_p(√n)` half). If the
`U`-increment decomposes as `U_n - U_ℓ ≤ -c·d_n + M_n + ρ_n + pert_n·d_n` with `c > 0`, `d_n ≥ 0`,
`pert = o_p(1)`, and the `M`- and `ρ`-terms are increment-controlled `≤ V·d_n + W` with
`V = o_p(1)`, `W = o_p(√n)`, then `(U_n - U_ℓ)^+ = o_p(√n)` (one-sided). The negative drift `-c`
absorbs all the
`o_p(1)·d_n` perturbations. -/
lemma isLittleOpOne_max_of_decomp {c : ℝ} (hc : 0 < c)
    {d Uincr Mincr rhoterm pert VM WM Vρ Wρ : ℕ → Ω → ℝ}
    (hd : ∀ n ω, 0 ≤ d n ω)
    (hdecomp : ∀ n ω, Uincr n ω ≤ -c * d n ω + Mincr n ω + rhoterm n ω + pert n ω * d n ω)
    (hpert : IsLittleOpOne μ pert)
    (hMbound : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, Mincr n ω ≤ VM n ω * d n ω + WM n ω)
    (hVM : IsLittleOpOne μ VM) (hWM : IsLittleOpOne μ (fun n ω ↦ WM n ω / √n))
    (hρbound : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, rhoterm n ω ≤ Vρ n ω * d n ω + Wρ n ω)
    (hVρ : IsLittleOpOne μ Vρ) (hWρ : IsLittleOpOne μ (fun n ω ↦ Wρ n ω / √n)) :
    IsLittleOpOne μ (fun n ω ↦ max (Uincr n ω / √n) 0) := by
  refine isLittleOpOne_max_div_sqrt_of_drift hc
    (A := fun n ω ↦ VM n ω + Vρ n ω + pert n ω)
    (B := fun n ω ↦ WM n ω / √n + Wρ n ω / √n)
    ((hVM.add hVρ).add hpert) (hWM.add hWρ) hd ?_
  filter_upwards [hMbound, hρbound, eventually_ge_atTop 1] with n hMbn hρbn hn
  filter_upwards [hMbn, hρbn] with ω hMb hρb
  have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hB : (WM n ω / √n + Wρ n ω / √n) * √n = WM n ω + Wρ n ω := by
    field_simp
  have hexpand : d n ω * (-c + (VM n ω + Vρ n ω + pert n ω)) + (WM n ω + Wρ n ω)
      = -c * d n ω + (VM n ω * d n ω + WM n ω) + (Vρ n ω * d n ω + Wρ n ω)
        + pert n ω * d n ω := by ring
  change Uincr n ω ≤ d n ω * (-c + (VM n ω + Vρ n ω + pert n ω))
    + (WM n ω / √n + Wρ n ω / √n) * √n
  rw [hB, hexpand]
  linarith [hdecomp n ω, hMb, hρb]

/-- **Forward one-sided deviation bound.** If `Dev_n ≤ small_n + Uincr_n` with `(small/√n)^+ =
o_p(1)` and `(Uincr/√n)^+ = o_p(1)`, then `(Dev_n/√n)^+ = o_p(1)`. -/
lemma isLittleOpOne_maxDev_of_le {Dev small Uincr : ℕ → Ω → ℝ}
    (hDev : ∀ n, ∀ᵐ ω ∂μ, Dev n ω ≤ small n ω + Uincr n ω)
    (hsmall : IsLittleOpOne μ (fun n ω ↦ max (small n ω / √n) 0))
    (hU : IsLittleOpOne μ (fun n ω ↦ max (Uincr n ω / √n) 0)) :
    IsLittleOpOne μ (fun n ω ↦ max (Dev n ω / √n) 0) := by
  refine IsLittleOpOne.of_abs_le_ae
    (Y := fun n ω ↦ max (small n ω / √n) 0 + max (Uincr n ω / √n) 0) ?_
    (hsmall.add hU)
  intro n
  filter_upwards [hDev n] with ω hDevω
  rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Real.sqrt_zero]
  · have hsn : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hdiv : Dev n ω / √n
        ≤ small n ω / √n + Uincr n ω / √n := by
      rw [← add_div]; gcongr
    refine max_le ?_ (by positivity)
    have hsle := le_max_left (small n ω / √n) 0
    have hUle := le_max_left (Uincr n ω / √n) 0
    linarith

/-- **Two-sided deviation from one-sided bounds** (blueprint `lem:prop_dev` reverse step). For a
finite family `Dev` with `∑_j Dev_j = 0` (the counts/target simplex identity), if each positive
part `(Dev_j/√n)^+ = o_p(1)`, then `Dev_k = o_p(√n)` for every `k`. The reverse inequality
`-Dev_k = ∑_{j≠k} Dev_j` transfers the one-sided bounds. -/
lemma isLittleOpOne_dev_of_sum_zero {ι : Type*} [Fintype ι]
    {Dev : ι → ℕ → Ω → ℝ} (hsum : ∀ n ω, ∑ j, Dev j n ω = 0)
    (hfwd : ∀ j, IsLittleOpOne μ (fun n ω ↦ max (Dev j n ω / √n) 0)) (k : ι) :
    IsLittleOpOne μ (fun n ω ↦ Dev k n ω / √n) := by
  classical
  apply isLittleOpOne_of_abs
  have hrev : IsLittleOpOne μ (fun n ω ↦ max (-(Dev k n ω / √n)) 0) := by
    refine IsLittleOpOne.of_abs_le
      (Y := fun n ω ↦ ∑ j ∈ Finset.univ.erase k, max (Dev j n ω / √n) 0) ?_
      (isLittleOpOne_finset_sum fun j _ ↦ hfwd j)
    intro n ω
    rw [abs_of_nonneg (le_max_right _ _),
      abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ le_max_right _ _)]
    have hneg : -(Dev k n ω / √n)
        = ∑ j ∈ Finset.univ.erase k, Dev j n ω / √n := by
      have key : Dev k n ω + ∑ j ∈ Finset.univ.erase k, Dev j n ω = ∑ j, Dev j n ω :=
        Finset.add_sum_erase Finset.univ (fun j ↦ Dev j n ω) (Finset.mem_univ k)
      have h2 : ∑ j ∈ Finset.univ.erase k, Dev j n ω = -(Dev k n ω) := by
        have hz := hsum n ω
        linarith [key, hz]
      rw [← Finset.sum_div, h2, neg_div]
    rw [hneg]
    exact max_le (Finset.sum_le_sum fun j _ ↦ le_max_left _ _)
      (Finset.sum_nonneg fun j _ ↦ le_max_right _ _)
  have hpm : ∀ x : ℝ, |x| = max x 0 + max (-x) 0 := by
    intro x; rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : -x ≤ 0), add_zero]
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -x), zero_add]
  have hcomb : (fun n ω ↦ |Dev k n ω / √n|)
      = fun n ω ↦ max (Dev k n ω / √n) 0 + max (-(Dev k n ω / √n)) 0 := by
    funext n ω; exact hpm _
  rw [hcomb]
  exact (hfwd k).add hrev

end AlphaRAR
