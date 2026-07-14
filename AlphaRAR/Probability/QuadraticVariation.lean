/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Martingale.Centering

/-!
# Predictable quadratic variation

For a square-integrable martingale `M` (with `M 0 = 0`), the predictable quadratic
variation `⟨M⟩` is the predictable part of the submartingale `M²` in its Doob
decomposition, and `M² - ⟨M⟩` is a martingale. This file records these as thin
wrappers around Mathlib's discrete Doob decomposition.

## Main results

* `AlphaRAR.predQuadVar`: the predictable quadratic variation (blueprint `def:pred_qv`).
* `AlphaRAR.martingale_sq_sub_predQuadVar`: `M² - ⟨M⟩` is a martingale
  (blueprint `lem:qv_mart`).
-/

open MeasureTheory Finset

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- The **predictable quadratic variation** `⟨M⟩` of a process `M`, defined as the
predictable part of `M²` in its Doob decomposition (blueprint `def:pred_qv`). -/
noncomputable def predQuadVar (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  predictablePart (fun n ↦ M n ^ 2) ℱ μ

@[simp] lemma predQuadVar_zero : predQuadVar M ℱ μ 0 = 0 := predictablePart_zero

/-- The predictable quadratic variation is invariant under negation: `⟨-M⟩ = ⟨M⟩`, since
`(-M)² = M²` pointwise. -/
lemma predQuadVar_neg (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) :
    predQuadVar (-M) ℱ μ = predQuadVar M ℱ μ := by
  unfold predQuadVar
  congr 1
  funext n ω
  simp only [Pi.pow_apply, Pi.neg_apply, neg_sq]

/-- The increment of `⟨M⟩` is the conditional expectation of the increment of `M²`:
`⟨M⟩ (n+1) - ⟨M⟩ n = μ[M (n+1)² - M n² | ℱ n]` (blueprint `lem:qv_incr`, before the
martingale simplification of the cross term). -/
lemma predQuadVar_succ_sub (n : ℕ) :
    predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      = μ[(fun ω ↦ M (n + 1) ω ^ 2) - fun ω ↦ M n ω ^ 2 | ℱ n] := by
  rw [predQuadVar, predictablePart_add_one]
  abel

/-- **Increment of the quadratic variation** (blueprint `lem:qv_incr`).
For a martingale `M`, the increment of `⟨M⟩` is the conditional second moment of
the increment of `M`: `⟨M⟩ (n+1) - ⟨M⟩ n = μ[(M (n+1) - M n)² | ℱ n]` a.e.
(the cross term `2 Mₙ ΔMₙ` vanishes by the martingale property). -/
lemma predQuadVar_succ_sub_eq [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (n : ℕ)
    (hd2 : Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      =ᵐ[μ] μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] := by
  rw [predQuadVar_succ_sub]
  -- `M(n+1)² - Mₙ² = (M(n+1) - Mₙ)² + (Mₙ ΔMₙ + Mₙ ΔMₙ)` pointwise.
  have hfun : ((fun ω ↦ M (n + 1) ω ^ 2) - fun ω ↦ M n ω ^ 2)
      = (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2)
        + (M n * (M (n + 1) - M n) + M n * (M (n + 1) - M n)) := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    ring
  rw [hfun]
  -- the increment `M(n+1) - Mₙ` has conditional expectation `0`.
  have hcd : μ[M (n + 1) - M n | ℱ n] =ᵐ[μ] 0 := by
    have h3 : μ[M n | ℱ n] = M n :=
      condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyMeasurable n) (hM.integrable n)
    have h1 : μ[M (n + 1) - M n | ℱ n] =ᵐ[μ] μ[M (n + 1) | ℱ n] - μ[M n | ℱ n] :=
      condExp_sub (hM.integrable (n + 1)) (hM.integrable n) _
    rw [h3] at h1
    have h2 : μ[M (n + 1) | ℱ n] =ᵐ[μ] M n := hM.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [h1, h2] with ω e1 e2
    simp only [Pi.sub_apply, Pi.zero_apply, e1, e2, sub_self]
  -- pull out the `ℱ n`-measurable factor `Mₙ`, leaving `Mₙ · 0 = 0`.
  have hpull : μ[M n * (M (n + 1) - M n) | ℱ n] =ᵐ[μ] M n * μ[M (n + 1) - M n | ℱ n] :=
    condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable n) hprod
      ((hM.integrable (n + 1)).sub (hM.integrable n))
  -- the cross term has conditional expectation `0`.
  have hcross : μ[M n * (M (n + 1) - M n) + M n * (M (n + 1) - M n) | ℱ n] =ᵐ[μ] 0 := by
    refine (condExp_add hprod hprod (ℱ n)).trans ?_
    filter_upwards [hpull, hcd] with ω ep ec
    have hz : μ[M (n + 1) - M n | ℱ n] ω = 0 := by simpa using ec
    simp only [Pi.add_apply, Pi.zero_apply, ep, Pi.mul_apply, hz, mul_zero, add_zero]
  refine (condExp_add hd2 (hprod.add hprod) (ℱ n)).trans ?_
  filter_upwards [hcross] with ω e
  have hz : μ[M n * (M (n + 1) - M n) + M n * (M (n + 1) - M n) | ℱ n] ω = 0 := by simpa using e
  simp only [Pi.add_apply, hz, add_zero]

/-- **`⟨M⟩` is non-decreasing** (blueprint `lem:qv_incr`, monotonicity part).
The quadratic variation of a martingale increases, since its increment is a
conditional second moment, hence nonnegative. -/
lemma predQuadVar_le_succ [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (n : ℕ)
    (hd2 : Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    predQuadVar M ℱ μ n ≤ᵐ[μ] predQuadVar M ℱ μ (n + 1) := by
  have hinc := predQuadVar_succ_sub_eq hM n hd2 hprod
  have hnn : (0 : Ω → ℝ) ≤ᵐ[μ] μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] := by
    refine condExp_nonneg ?_
    filter_upwards with ω
    simp only [Pi.zero_apply]
    positivity
  filter_upwards [hinc, hnn] with ω e hn
  simp only [Pi.sub_apply, Pi.zero_apply] at e hn
  linarith

/-- **`⟨M⟩` is monotone** (blueprint `lem:qv_incr`, monotonicity part). Almost surely the whole
path `n ↦ ⟨M⟩ n ω` is nondecreasing, since each increment is a conditional second moment (hence
nonnegative, `predQuadVar_le_succ`). -/
lemma predQuadVar_mono [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hd2 : ∀ n, Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ) :
    ∀ᵐ ω ∂μ, Monotone (fun n ↦ predQuadVar M ℱ μ n ω) := by
  filter_upwards [ae_all_iff.mpr fun n ↦ predQuadVar_le_succ hM n (hd2 n) (hprod n)] with ω hω
  exact monotone_nat_of_le_succ fun n ↦ hω n

/-- **The predictable quadratic variation is nonnegative.** Since `⟨M⟩ 0 = 0` and `⟨M⟩` is
nondecreasing (`predQuadVar_mono`), `0 ≤ ⟨M⟩ n` a.e. -/
lemma predQuadVar_nonneg [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hd2 : ∀ n, Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ) (n : ℕ) :
    0 ≤ᵐ[μ] predQuadVar M ℱ μ n := by
  filter_upwards [predQuadVar_mono hM hd2 hprod] with ω hmono
  have h0n : predQuadVar M ℱ μ 0 ω ≤ predQuadVar M ℱ μ n ω := hmono (Nat.zero_le n)
  rw [show predQuadVar M ℱ μ 0 ω = 0 from by rw [predQuadVar_zero]; rfl] at h0n
  simpa using h0n

/-- **Linear upper bound on `⟨M⟩` for bounded increments.** If `|ΔM_i| ≤ c` a.e., then each
increment `⟨M⟩_{k+1} - ⟨M⟩_k` equals `μ[(ΔM_k)² | ℱ_k] ≤ c²`, so telescoping from `⟨M⟩_0 = 0`
gives `⟨M⟩_n ≤ c² n` a.e. -/
lemma predQuadVar_le_of_bound [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) {c : ℝ}
    (hd2 : ∀ n, Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ c) :
    ∀ᵐ ω ∂μ, ∀ n, predQuadVar M ℱ μ n ω ≤ c ^ 2 * n := by
  have hstep : ∀ k, ∀ᵐ ω ∂μ,
      predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω ≤ c ^ 2 := by
    intro k
    have hinc := predQuadVar_succ_sub_eq hM k (hd2 k) (hprod k)
    have hsqle : (fun ω ↦ (M (k + 1) ω - M k ω) ^ 2) ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
      filter_upwards [hb k] with ω h
      nlinarith [neg_le_of_abs_le h, le_of_abs_le h]
    have hcond : μ[fun ω ↦ (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ ↦ c ^ 2 := by
      have h := condExp_mono (m := ℱ k) (hd2 k) (integrable_const (c ^ 2)) hsqle
      rwa [condExp_const (ℱ.le k)] at h
    filter_upwards [hinc, hcond] with ω e ec
    rw [Pi.sub_apply] at e; rw [e]; exact ec
  filter_upwards [ae_all_iff.mpr hstep] with ω hω
  intro n
  have htel : ∑ k ∈ Finset.range n,
      (predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω) = predQuadVar M ℱ μ n ω := by
    rw [Finset.sum_range_sub (fun k ↦ predQuadVar M ℱ μ k ω) n]
    have h0 : predQuadVar M ℱ μ 0 ω = 0 := by rw [predQuadVar_zero]; rfl
    rw [h0, sub_zero]
  rw [← htel]
  calc ∑ k ∈ Finset.range n, (predQuadVar M ℱ μ (k + 1) ω - predQuadVar M ℱ μ k ω)
      ≤ ∑ _k ∈ Finset.range n, c ^ 2 := Finset.sum_le_sum fun k _ ↦ hω k
    _ = c ^ 2 * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **A martingale has constant expectation**: `∫ N n = ∫ N 0` for every `n`.
Follows from `N 0 =ᵐ μ[N n | ℱ 0]` and the fact that conditional expectation
preserves the integral. -/
lemma martingale_integral_eq [IsFiniteMeasure μ] {N : ℕ → Ω → ℝ}
    (hN : Martingale N ℱ μ) (n : ℕ) : ∫ ω, N n ω ∂μ = ∫ ω, N 0 ω ∂μ := by
  calc ∫ ω, N n ω ∂μ
      = ∫ ω, (μ[N n | ℱ 0]) ω ∂μ := (integral_condExp (f := N n) (ℱ.le 0)).symm
    _ = ∫ ω, N 0 ω ∂μ := integral_congr_ae (hN.condExp_ae_eq (Nat.zero_le n))

/-- **`M² - ⟨M⟩` is a martingale** (blueprint `lem:qv_mart`).
For an adapted process `M` with square-integrable values, `M² - ⟨M⟩` is a
martingale, being the martingale part of `M²` in its Doob decomposition. -/
lemma martingale_sq_sub_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) :
    Martingale (fun n ↦ (fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) ℱ μ := by
  have hadapt : StronglyAdapted ℱ (fun n ↦ fun ω ↦ M n ω ^ 2) := fun n ↦ (hM n).pow 2
  exact martingale_martingalePart hadapt hM2

/-- **`⟨M⟩ n` is integrable.** Since `M² - ⟨M⟩` is (the martingale part, hence)
integrable and `M²` is integrable, so is `⟨M⟩`. -/
@[fun_prop]
lemma integrable_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) (n : ℕ) :
    Integrable (predQuadVar M ℱ μ n) μ := by
  have hN := martingale_sq_sub_predQuadVar hM hM2
  have hNk : Integrable ((fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) μ := hN.integrable n
  have hid : predQuadVar M ℱ μ n
      = (fun ω ↦ M n ω ^ 2) - ((fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) := by
    funext ω; simp [Pi.sub_apply]
  rw [hid]
  exact (hM2 n).sub hNk

/-- **Expected quadratic variation equals the second moment** (blueprint
`lem:qv_second_moment`). For a square-integrable martingale `M` with `M 0 = 0`,
`E[M n ²] = E[⟨M⟩ n]`. This is the discrete Itô isometry: `M² - ⟨M⟩` is a
martingale starting at `0`, so its expectation stays `0`. -/
lemma integral_sq_eq_integral_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    (hM0 : M 0 =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ = ∫ ω, predQuadVar M ℱ μ n ω ∂μ := by
  have hN := martingale_sq_sub_predQuadVar hM hM2
  have hIqv := integrable_predQuadVar hM hM2
  -- `∫ (M n² - ⟨M⟩ n) = ∫ M n² - ∫ ⟨M⟩ n`.
  have e1 : ∫ ω, ((fun ω ↦ M n ω ^ 2) - predQuadVar M ℱ μ n) ω ∂μ
      = ∫ ω, M n ω ^ 2 ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ :=
    integral_sub (hM2 n) (hIqv n)
  -- At time `0` the process is `M 0² - ⟨M⟩ 0 = 0` a.e.
  have e0 : ∫ ω, ((fun ω ↦ M 0 ω ^ 2) - predQuadVar M ℱ μ 0) ω ∂μ = 0 := by
    have hz : ((fun ω ↦ M 0 ω ^ 2) - predQuadVar M ℱ μ 0) =ᵐ[μ] 0 := by
      filter_upwards [hM0] with ω hω
      simp only [Pi.sub_apply, Pi.zero_apply] at hω ⊢
      rw [show predQuadVar M ℱ μ 0 ω = 0 from by rw [predQuadVar_zero]; rfl, hω]
      ring
    rw [integral_congr_ae hz]; simp
  have hconst := martingale_integral_eq hN n
  have key : ∫ ω, M n ω ^ 2 ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ = 0 := by
    rw [← e1, hconst]; exact e0
  exact sub_eq_zero.mp key

/-- **Integrated increment of `⟨M⟩`.** The expected increment of the quadratic
variation is the second moment of the martingale increment:
`E[⟨M⟩ (n+1)] - E[⟨M⟩ n] = E[(ΔM (n+1))²]`. -/
lemma integral_predQuadVar_succ_sub [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) (n : ℕ)
    (hd2 : Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    ∫ ω, predQuadVar M ℱ μ (n + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := by
  have hIqv := integrable_predQuadVar hM.stronglyAdapted hM2
  have h1 : predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      =ᵐ[μ] μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] :=
    predQuadVar_succ_sub_eq hM n hd2 hprod
  calc ∫ ω, predQuadVar M ℱ μ (n + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∫ ω, (predQuadVar M ℱ μ (n + 1) ω - predQuadVar M ℱ μ n ω) ∂μ :=
        (integral_sub (hIqv (n + 1)) (hIqv n)).symm
    _ = ∫ ω, (μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n]) ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h1] with ω hω
        simpa [Pi.sub_apply] using hω
    _ = ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := integral_condExp (ℱ.le n)

/-- **Martingale `L²` growth bound** (blueprint `lem:mart_sq_growth`).
If every increment has second moment `≤ σ²`, then `E[M n ²] ≤ σ² n`. This is the
discrete Itô isometry combined with the telescoping of `⟨M⟩`. -/
lemma integral_sq_le_of_increment_bound [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ) (hM0 : M 0 =ᵐ[μ] 0) (σ2 : ℝ)
    (hd2 : ∀ n, Integrable (fun ω ↦ (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : ∀ n, Integrable (M n * (M (n + 1) - M n)) μ)
    (hinc : ∀ n, ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ ≤ σ2) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ ≤ σ2 * n := by
  have hqv : ∀ n, ∫ ω, predQuadVar M ℱ μ n ω ∂μ ≤ σ2 * n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hstep := integral_predQuadVar_succ_sub hM hM2 k (hd2 k) (hprod k)
      have heq : ∫ ω, predQuadVar M ℱ μ (k + 1) ω ∂μ
          = ∫ ω, predQuadVar M ℱ μ k ω ∂μ + ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by linarith
      rw [heq]
      have hcast : σ2 * ((k + 1 : ℕ) : ℝ) = σ2 * (k : ℝ) + σ2 := by push_cast; ring
      rw [hcast]
      linarith [ih, hinc k]
  rw [integral_sq_eq_integral_predQuadVar hM.stronglyAdapted hM2 hM0 n]
  exact hqv n

/-- **Product of conditionally orthogonal martingales is a martingale** (blueprint
`lem:qv_orthogonal`, first part). If `M`, `N` are martingales whose increments are
conditionally orthogonal, `μ[ΔM (i+1) · ΔN (i+1) | ℱ i] = 0`, then `M · N` is a
martingale. The integrability of the increment products is taken as hypotheses. -/
lemma martingale_mul [IsFiniteMeasure μ] {N : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hN : Martingale N ℱ μ)
    (hMN : ∀ n, Integrable (M n * N n) μ)
    (hB : ∀ i, Integrable (M i * (N (i + 1) - N i)) μ)
    (hC : ∀ i, Integrable (N i * (M (i + 1) - M i)) μ)
    (hD : ∀ i, Integrable ((M (i + 1) - M i) * (N (i + 1) - N i)) μ)
    (hortho : ∀ i, μ[(M (i + 1) - M i) * (N (i + 1) - N i) | ℱ i] =ᵐ[μ] 0) :
    Martingale (fun n ↦ M n * N n) ℱ μ := by
  refine martingale_nat
    (fun n ↦ (hM.stronglyMeasurable n).mul (hN.stronglyMeasurable n)) hMN (fun i ↦ ?_)
  -- Increments of `M` and `N` have vanishing conditional expectation.
  have hcdM : μ[M (i + 1) - M i | ℱ i] =ᵐ[μ] 0 := by
    have h3 : μ[M i | ℱ i] = M i :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hM.stronglyMeasurable i) (hM.integrable i)
    have h1 : μ[M (i + 1) - M i | ℱ i] =ᵐ[μ] μ[M (i + 1) | ℱ i] - μ[M i | ℱ i] :=
      condExp_sub (hM.integrable (i + 1)) (hM.integrable i) _
    rw [h3] at h1
    have h2 : μ[M (i + 1) | ℱ i] =ᵐ[μ] M i := hM.condExp_ae_eq (Nat.le_succ i)
    filter_upwards [h1, h2] with ω e1 e2
    simp only [Pi.sub_apply, Pi.zero_apply, e1, e2, sub_self]
  have hcdN : μ[N (i + 1) - N i | ℱ i] =ᵐ[μ] 0 := by
    have h3 : μ[N i | ℱ i] = N i :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hN.stronglyMeasurable i) (hN.integrable i)
    have h1 : μ[N (i + 1) - N i | ℱ i] =ᵐ[μ] μ[N (i + 1) | ℱ i] - μ[N i | ℱ i] :=
      condExp_sub (hN.integrable (i + 1)) (hN.integrable i) _
    rw [h3] at h1
    have h2 : μ[N (i + 1) | ℱ i] =ᵐ[μ] N i := hN.condExp_ae_eq (Nat.le_succ i)
    filter_upwards [h1, h2] with ω e1 e2
    simp only [Pi.sub_apply, Pi.zero_apply, e1, e2, sub_self]
  -- Conditional expectations of the four pieces of the product increment.
  have eA : μ[M i * N i | ℱ i] = M i * N i :=
    condExp_of_stronglyMeasurable (ℱ.le i)
      ((hM.stronglyMeasurable i).mul (hN.stronglyMeasurable i)) (hMN i)
  have eB : μ[M i * (N (i + 1) - N i) | ℱ i] =ᵐ[μ] 0 := by
    have hpull : μ[M i * (N (i + 1) - N i) | ℱ i] =ᵐ[μ] M i * μ[N (i + 1) - N i | ℱ i] :=
      condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable i) (hB i)
        ((hN.integrable (i + 1)).sub (hN.integrable i))
    filter_upwards [hpull, hcdN] with ω ep ec
    have hz : μ[N (i + 1) - N i | ℱ i] ω = 0 := by simpa using ec
    simp only [ep, Pi.mul_apply, hz, mul_zero, Pi.zero_apply]
  have eC : μ[N i * (M (i + 1) - M i) | ℱ i] =ᵐ[μ] 0 := by
    have hpull : μ[N i * (M (i + 1) - M i) | ℱ i] =ᵐ[μ] N i * μ[M (i + 1) - M i | ℱ i] :=
      condExp_mul_of_stronglyMeasurable_left (hN.stronglyMeasurable i) (hC i)
        ((hM.integrable (i + 1)).sub (hM.integrable i))
    filter_upwards [hpull, hcdM] with ω ep ec
    have hz : μ[M (i + 1) - M i | ℱ i] ω = 0 := by simpa using ec
    simp only [ep, Pi.mul_apply, hz, mul_zero, Pi.zero_apply]
  -- Pointwise decomposition of the product increment.
  have hdecomp : M (i + 1) * N (i + 1)
      = M i * N i + M i * (N (i + 1) - N i) + N i * (M (i + 1) - M i)
        + (M (i + 1) - M i) * (N (i + 1) - N i) := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  have hAB : Integrable (M i * N i + M i * (N (i + 1) - N i)) μ := (hMN i).add (hB i)
  have hABC : Integrable
      (M i * N i + M i * (N (i + 1) - N i) + N i * (M (i + 1) - M i)) μ := hAB.add (hC i)
  refine Filter.EventuallyEq.symm ?_
  rw [hdecomp]
  filter_upwards [condExp_add hABC (hD i) (ℱ i), condExp_add hAB (hC i) (ℱ i),
    condExp_add (hMN i) (hB i) (ℱ i), eB, eC, hortho i] with ω h1 h2 h3 hb hc hd
  simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 hb hc hd
  rw [h1, h2, h3, congrFun eA ω, hb, hc, hd]
  ring

/-- **Additivity of the quadratic variation for orthogonal martingales** (blueprint
`lem:qv_orthogonal`, second part). If `M · N` is a martingale (e.g. `M`, `N` are
conditionally orthogonal martingales, see `martingale_mul`), then
`⟨M + N⟩ = ⟨M⟩ + ⟨N⟩`. This is predictable-part linearity together with the fact
that the predictable part of the martingale `M · N` vanishes. -/
lemma predQuadVar_add_of_martingale_mul {N : ℕ → Ω → ℝ}
    (hM2 : ∀ n, Integrable (fun ω ↦ M n ω ^ 2) μ)
    (hN2 : ∀ n, Integrable (fun ω ↦ N n ω ^ 2) μ)
    (hMN : ∀ n, Integrable (M n * N n) μ)
    (hmart : Martingale (fun n ↦ M n * N n) ℱ μ) (n : ℕ) :
    predQuadVar (fun k ↦ M k + N k) ℱ μ n
      =ᵐ[μ] predQuadVar M ℱ μ n + predQuadVar N ℱ μ n := by
  have hproc : (fun k ↦ (M k + N k) ^ 2)
      = (fun k ↦ M k ^ 2) + (fun k ↦ N k ^ 2) + (2 : ℝ) • (fun k ↦ M k * N k) := by
    funext k ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.pow_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hMint : ∀ k, Integrable ((fun k ↦ M k ^ 2) k) μ := hM2
  have hNint : ∀ k, Integrable ((fun k ↦ N k ^ 2) k) μ := hN2
  have hMNint : ∀ k, Integrable (((2 : ℝ) • fun k ↦ M k * N k) k) μ := fun k ↦ by
    simpa using (hMN k).smul (2 : ℝ)
  -- Split `⟨M+N⟩` by linearity of the predictable part.
  have h1 : predQuadVar (fun k ↦ M k + N k) ℱ μ n
      =ᵐ[μ] predictablePart ((fun k ↦ M k ^ 2) + fun k ↦ N k ^ 2) ℱ μ n
        + predictablePart ((2 : ℝ) • fun k ↦ M k * N k) ℱ μ n := by
    rw [predQuadVar, hproc]
    exact predictablePart_add (fun k ↦ (hMint k).add (hNint k)) hMNint n
  have h2 : predictablePart ((fun k ↦ M k ^ 2) + fun k ↦ N k ^ 2) ℱ μ n
      =ᵐ[μ] predQuadVar M ℱ μ n + predQuadVar N ℱ μ n := by
    simpa only [predQuadVar] using predictablePart_add hMint hNint n
  have h3 : predictablePart ((2 : ℝ) • fun k ↦ M k * N k) ℱ μ n =ᵐ[μ] 0 := by
    have hs := predictablePart_smul (ℱ := ℱ) (μ := μ) (f := fun k ↦ M k * N k) (2 : ℝ) n
    have hz := hmart.predictablePart_eq_zero n
    filter_upwards [hs, hz] with ω es ez
    simp only [Pi.smul_apply, Pi.zero_apply] at es ez ⊢
    rw [es, ez, smul_zero]
  filter_upwards [h1, h2, h3] with ω a1 a2 a3
  simp only [Pi.add_apply, Pi.zero_apply] at a1 a2 a3 ⊢
  rw [a1, a2, a3, add_zero]

end AlphaRAR
