/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.LeanMachineLearning.PullCount
public import LeanMachineLearning.SequentialLearning.ActionIndicator
public import AlphaRAR.Mathlib.Filtration
public meta import LeanSpec

/-!
# Allocation counts

The allocation count `N n = ∑_{j<n} X j` of a single arm, for a sequence `X` of assignment
indicators. Stated over a general `AddCommMonoid` so that one definition serves both the
deterministic per-path counts (`X : ℕ → ℝ`, the deterministic analysis of `Deterministic.lean`)
and the process-level count (`X : ℕ → Ω → ℝ`, the count process compensated in `Assignment.lean`).

Besides the two defining equations, this file collects the identities that connect `count` to the
rest of the development: the simplex identities used by the deviation analysis, the adaptedness and
integrability of the count process, and the bridges identifying the count of an arm indicator with
the `LeanMachineLearning` pull counts `pullCount` / `pullCount'`.

## Main results

* `AlphaRAR.count_zero`, `AlphaRAR.count_succ`: the two equations that determine `count`.
* `AlphaRAR.counts_sum`: the arm counts sum to the time index.
* `AlphaRAR.count_indicator_eq_pullCount`, `AlphaRAR.histCount_eq`: the count of an arm indicator
  is the pull count, in process and history form.
-/

@[expose] public section

open Filter Finset MeasureTheory Learning

namespace AlphaRAR

/-! ### Definition -/

/-- Allocation count of a fixed arm, `N n = ∑_{j<n} X j` (blueprint `def:counts`). Stated for a
general `AddCommMonoid` so it serves both the deterministic per-path counts (`X : ℕ → ℝ`) and the
process-level count (`X : ℕ → Ω → ℝ`, the assignment count process of `Assignment.lean`). -/
def count {M : Type*} [AddCommMonoid M] (X : ℕ → M) (n : ℕ) : M := ∑ j ∈ range n, X j

@[simp, specifies count "fixes the base of the count; with `count_succ` it determines every value, \
and it records the 0-indexing convention: nothing has been counted before patient `0`"]
lemma count_zero {M : Type*} [AddCommMonoid M] (X : ℕ → M) : count X 0 = 0 := by
  simp [count]

/-- Increment of the count: `N (n+1) = N n + X n`. -/
@[specifies count "the step `n → n+1` adds patient `n`, so `count X n` covers patients \
`0, …, n-1` — the half-open convention every index computation in the development relies on"]
lemma count_succ {M : Type*} [AddCommMonoid M] (X : ℕ → M) (n : ℕ) :
    count X (n + 1) = count X n + X n := by
  unfold count
  rw [Finset.sum_range_succ]

/-! ### Simplex identities -/

/-- **Counts sum to time** (blueprint `lem:counts_sum`).
If the assignment vector sums to one at each time, then the arm counts sum to the
time index. -/
lemma counts_sum {ι : Type*} [Fintype ι] (Y : ℕ → ι → ℝ) (hY : ∀ j, ∑ k, Y j k = 1) (n : ℕ) :
    (∑ k, count (Y · k) n) = n := by
  simp only [count]
  rw [Finset.sum_comm]
  simp only [hY, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- **Deviation simplex identity** (backbone of the `lem:prop_dev` reverse step). If the assignment
vector and the target vector each sum to one, then the deviations `N_{n,k} - n r_k` sum to zero. -/
lemma sum_count_sub_smul_eq_zero {ι : Type*} [Fintype ι] (Y : ℕ → ι → ℝ) (r : ι → ℝ)
    (hY : ∀ j, ∑ k, Y j k = 1) (hr : ∑ k, r k = 1) (n : ℕ) :
    ∑ k, (count (Y · k) n - (n : ℝ) * r k) = 0 := by
  rw [Finset.sum_sub_distrib, counts_sum Y hY n, ← Finset.mul_sum, hr, mul_one, sub_self]

/-! ### The count process -/

section Process

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}

/-- The count process is adapted to the *previous-history* filtration `ℱ.shiftDown`: `count X n`
sums `X 0, …, X (n-1)`, each of which is already `ℱ (n-1)`-measurable. -/
lemma stronglyAdapted_count (hX : StronglyAdapted ℱ X) :
    StronglyAdapted ℱ.shiftDown (count X) := by
  intro n
  apply Finset.stronglyMeasurable_sum
  intro i hi
  rw [Finset.mem_range] at hi
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (hX i).mono (ℱ.mono (by omega : i ≤ m))

@[fun_prop]
lemma integrable_count (hX : ∀ n, Integrable (X n) μ) (n : ℕ) :
    Integrable (count X n) μ :=
  integrable_finsetSum' _ fun i _ ↦ hX i

end Process

/-! ### Bridges to the pull counts -/

section PullCount

variable {Ω 𝓐 : Type*} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}

/-- Count of a fixed arm is nonnegative. -/
lemma count_actionIndicator_nonneg (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ) (ω : Ω) :
    0 ≤ count (fun j ↦ actionIndicator A k j ω) n :=
  Finset.sum_nonneg fun j _ ↦ actionIndicator_nonneg A k j ω

variable [DecidableEq 𝓐]

/-- The deterministic count of the assignment-indicator sequence `𝟙{A · = k}` at a fixed
path `ω` equals the (real cast of the) pull count `N_{n,k}` of arm `k`. -/
lemma count_indicator_eq_pullCount (k : 𝓐) (n : ℕ) (ω : Ω) :
    count (fun j ↦ actionIndicator A k j ω) n = (pullCount A k n ω : ℝ) :=
  sum_actionIndicator_eq_pullCount A k n ω

/-- The process count `N_{n+1,k}` equals the history-level count on the history up to time `n`. -/
lemma histCount_eq (k : 𝓐) (n : ℕ) (ω : Ω) :
    count (fun j ↦ actionIndicator A k j ω) (n + 1) = (pullCount' n (history A Y n ω) k : ℝ) := by
  have hpc : pullCount A k (n + 1) ω = pullCount' n (history A Y n ω) k :=
    pullCount_add_one_eq_pullCount' (R' := Y)
  rw [count_indicator_eq_pullCount, hpc]

end PullCount

end AlphaRAR
