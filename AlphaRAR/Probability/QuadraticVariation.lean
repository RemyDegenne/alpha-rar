/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

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
  predictablePart (fun n => M n ^ 2) ℱ μ

@[simp] theorem predQuadVar_zero : predQuadVar M ℱ μ 0 = 0 := predictablePart_zero

/-- The increment of `⟨M⟩` is the conditional expectation of the increment of `M²`:
`⟨M⟩ (n+1) - ⟨M⟩ n = μ[M (n+1)² - M n² | ℱ n]` (blueprint `lem:qv_incr`, before the
martingale simplification of the cross term). -/
theorem predQuadVar_succ_sub (n : ℕ) :
    predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      = μ[(fun ω => M (n + 1) ω ^ 2) - fun ω => M n ω ^ 2 | ℱ n] := by
  rw [predQuadVar, predictablePart_add_one]
  abel

/-- **Increment of the quadratic variation** (blueprint `lem:qv_incr`).
For a martingale `M`, the increment of `⟨M⟩` is the conditional second moment of
the increment of `M`: `⟨M⟩ (n+1) - ⟨M⟩ n = μ[(M (n+1) - M n)² | ℱ n]` a.e.
(the cross term `2 Mₙ ΔMₙ` vanishes by the martingale property). -/
theorem predQuadVar_succ_sub_eq [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (n : ℕ)
    (hd2 : Integrable (fun ω => (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      =ᵐ[μ] μ[fun ω => (M (n + 1) ω - M n ω) ^ 2 | ℱ n] := by
  rw [predQuadVar_succ_sub]
  -- `M(n+1)² - Mₙ² = (M(n+1) - Mₙ)² + (Mₙ ΔMₙ + Mₙ ΔMₙ)` pointwise.
  have hfun : ((fun ω => M (n + 1) ω ^ 2) - fun ω => M n ω ^ 2)
      = (fun ω => (M (n + 1) ω - M n ω) ^ 2)
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
theorem predQuadVar_le_succ [IsFiniteMeasure μ] (hM : Martingale M ℱ μ) (n : ℕ)
    (hd2 : Integrable (fun ω => (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    predQuadVar M ℱ μ n ≤ᵐ[μ] predQuadVar M ℱ μ (n + 1) := by
  have hinc := predQuadVar_succ_sub_eq hM n hd2 hprod
  have hnn : (0 : Ω → ℝ) ≤ᵐ[μ] μ[fun ω => (M (n + 1) ω - M n ω) ^ 2 | ℱ n] := by
    refine condExp_nonneg ?_
    filter_upwards with ω
    simp only [Pi.zero_apply]
    positivity
  filter_upwards [hinc, hnn] with ω e hn
  simp only [Pi.sub_apply, Pi.zero_apply] at e hn
  linarith

/-- **A martingale has constant expectation**: `∫ N n = ∫ N 0` for every `n`.
Follows from `N 0 =ᵐ μ[N n | ℱ 0]` and the fact that conditional expectation
preserves the integral. -/
theorem martingale_integral_eq [IsFiniteMeasure μ] {N : ℕ → Ω → ℝ}
    (hN : Martingale N ℱ μ) (n : ℕ) : ∫ ω, N n ω ∂μ = ∫ ω, N 0 ω ∂μ := by
  calc ∫ ω, N n ω ∂μ
      = ∫ ω, (μ[N n | ℱ 0]) ω ∂μ := (integral_condExp (f := N n) (ℱ.le 0)).symm
    _ = ∫ ω, N 0 ω ∂μ := integral_congr_ae (hN.condExp_ae_eq (Nat.zero_le n))

/-- **`M² - ⟨M⟩` is a martingale** (blueprint `lem:qv_mart`).
For an adapted process `M` with square-integrable values, `M² - ⟨M⟩` is a
martingale, being the martingale part of `M²` in its Doob decomposition. -/
theorem martingale_sq_sub_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, Integrable (fun ω => M n ω ^ 2) μ) :
    Martingale (fun n => (fun ω => M n ω ^ 2) - predQuadVar M ℱ μ n) ℱ μ := by
  have hadapt : StronglyAdapted ℱ (fun n => fun ω => M n ω ^ 2) := fun n => (hM n).pow 2
  exact martingale_martingalePart hadapt hM2

/-- **`⟨M⟩ n` is integrable.** Since `M² - ⟨M⟩` is (the martingale part, hence)
integrable and `M²` is integrable, so is `⟨M⟩`. -/
theorem integrable_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, Integrable (fun ω => M n ω ^ 2) μ) (n : ℕ) :
    Integrable (predQuadVar M ℱ μ n) μ := by
  have hN := martingale_sq_sub_predQuadVar hM hM2
  have hNk : Integrable ((fun ω => M n ω ^ 2) - predQuadVar M ℱ μ n) μ := hN.integrable n
  have hid : predQuadVar M ℱ μ n
      = (fun ω => M n ω ^ 2) - ((fun ω => M n ω ^ 2) - predQuadVar M ℱ μ n) := by
    funext ω; simp [Pi.sub_apply]
  rw [hid]
  exact (hM2 n).sub hNk

/-- **Expected quadratic variation equals the second moment** (blueprint
`lem:qv_second_moment`). For a square-integrable martingale `M` with `M 0 = 0`,
`E[M n ²] = E[⟨M⟩ n]`. This is the discrete Itô isometry: `M² - ⟨M⟩` is a
martingale starting at `0`, so its expectation stays `0`. -/
theorem integral_sq_eq_integral_predQuadVar [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) (hM2 : ∀ n, Integrable (fun ω => M n ω ^ 2) μ)
    (hM0 : M 0 =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, M n ω ^ 2 ∂μ = ∫ ω, predQuadVar M ℱ μ n ω ∂μ := by
  have hN := martingale_sq_sub_predQuadVar hM hM2
  have hIqv := integrable_predQuadVar hM hM2
  -- `∫ (M n² - ⟨M⟩ n) = ∫ M n² - ∫ ⟨M⟩ n`.
  have e1 : ∫ ω, ((fun ω => M n ω ^ 2) - predQuadVar M ℱ μ n) ω ∂μ
      = ∫ ω, M n ω ^ 2 ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ :=
    integral_sub (hM2 n) (hIqv n)
  -- At time `0` the process is `M 0² - ⟨M⟩ 0 = 0` a.e.
  have e0 : ∫ ω, ((fun ω => M 0 ω ^ 2) - predQuadVar M ℱ μ 0) ω ∂μ = 0 := by
    have hz : ((fun ω => M 0 ω ^ 2) - predQuadVar M ℱ μ 0) =ᵐ[μ] 0 := by
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
theorem integral_predQuadVar_succ_sub [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, Integrable (fun ω => M n ω ^ 2) μ) (n : ℕ)
    (hd2 : Integrable (fun ω => (M (n + 1) ω - M n ω) ^ 2) μ)
    (hprod : Integrable (M n * (M (n + 1) - M n)) μ) :
    ∫ ω, predQuadVar M ℱ μ (n + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := by
  have hIqv := integrable_predQuadVar hM.stronglyAdapted hM2
  have h1 : predQuadVar M ℱ μ (n + 1) - predQuadVar M ℱ μ n
      =ᵐ[μ] μ[fun ω => (M (n + 1) ω - M n ω) ^ 2 | ℱ n] :=
    predQuadVar_succ_sub_eq hM n hd2 hprod
  calc ∫ ω, predQuadVar M ℱ μ (n + 1) ω ∂μ - ∫ ω, predQuadVar M ℱ μ n ω ∂μ
      = ∫ ω, (predQuadVar M ℱ μ (n + 1) ω - predQuadVar M ℱ μ n ω) ∂μ :=
        (integral_sub (hIqv (n + 1)) (hIqv n)).symm
    _ = ∫ ω, (μ[fun ω => (M (n + 1) ω - M n ω) ^ 2 | ℱ n]) ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h1] with ω hω
        simpa [Pi.sub_apply] using hω
    _ = ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := integral_condExp (ℱ.le n)

/-- **Martingale `L²` growth bound** (blueprint `lem:mart_sq_growth`).
If every increment has second moment `≤ σ²`, then `E[M n ²] ≤ σ² n`. This is the
discrete Itô isometry combined with the telescoping of `⟨M⟩`. -/
theorem integral_sq_le_of_increment_bound [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    (hM2 : ∀ n, Integrable (fun ω => M n ω ^ 2) μ) (hM0 : M 0 =ᵐ[μ] 0) (σ2 : ℝ)
    (hd2 : ∀ n, Integrable (fun ω => (M (n + 1) ω - M n ω) ^ 2) μ)
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

end AlphaRAR
