/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# Deterministic core of the auxiliary processes

Several lemmas in the model and auxiliary chapters of the blueprint are purely
algebraic identities about the counting and martingale processes: they hold
pathwise and do not use any probability. This file isolates that deterministic
core.

For a fixed arm we work with real sequences `X` (assignment indicator), `p`
(selection probability) and `ρ` (plug-in target), and define the count `N`, the
assignment martingale `M`, and the auxiliary process `U` by their defining sums.

## Main results

* `AlphaRAR.count_eq`: count decomposition `N n = ∑ p + M n` (blueprint
  `lem:count_decomp`).
* `AlphaRAR.counts_sum`: the counts sum to the time index (blueprint
  `lem:counts_sum`).
* `AlphaRAR.hitting_basic`: the last under-sampling time is non-decreasing and
  bounded by `n` (blueprint `lem:hitting_basic`).
-/

open Finset

namespace AlphaRAR

variable (X p ρ : ℕ → ℝ) (α : ℝ)

/-- Allocation count of a fixed arm, `N n = ∑_{j=1}^n X j` (blueprint `def:counts`). -/
def count (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, X j

/-- Assignment martingale of a fixed arm, `M n = ∑_{j=1}^n (X j - p j)`
(blueprint `def:M`). -/
def assignMG (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, (X j - p j)

/-- **Count decomposition** (blueprint `lem:count_decomp`).
`N n = ∑_{m=1}^n p m + M n`. -/
theorem count_eq (n : ℕ) : count X n = (∑ m ∈ Icc 1 n, p m) + assignMG X p n := by
  simp only [count, assignMG, Finset.sum_sub_distrib]
  grind

/-- Increment of the count: `N (n+1) = N n + X (n+1)`. -/
theorem count_succ (n : ℕ) : count X (n + 1) = count X n + X (n + 1) := by
  unfold count
  rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]

/-- Increment of the assignment martingale: `M (n+1) = M n + (X (n+1) - p (n+1))`. -/
theorem assignMG_succ (n : ℕ) :
    assignMG X p (n + 1) = assignMG X p n + (X (n + 1) - p (n + 1)) := by
  unfold assignMG
  rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]

/-- Auxiliary process `U n = ∑_{m=1}^{n-1} α ρ m + M n - n ρ n` (blueprint `def:U`). -/
def auxU (n : ℕ) : ℝ := (∑ m ∈ Icc 1 (n - 1), α * ρ m) + assignMG X p n - (n : ℝ) * ρ n

/-- Increment of the leading `α ρ` sum, for `n ≥ 1`. -/
theorem alphaSum_succ (n : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ Icc 1 n, α * ρ m) = (∑ m ∈ Icc 1 (n - 1), α * ρ m) + α * ρ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Finset.sum_Icc_succ_top (Nat.le_add_left 1 k)]

/-- **Increment of the auxiliary process** (blueprint `lem:U_increment`).

For `n ≥ 1`, writing `D n := N n - n ρ n`,
`U (n+1) - U n = α ρ n - p (n+1) + (D (n+1) - D n)`.
(This is the blueprint identity at time `n+1`; the leading term `α ρ_{n}`
requires `n ≥ 1`, since at `n = 0` the `α ρ`-sum does not yet grow.) -/
theorem auxU_succ_sub (n : ℕ) (hn : 1 ≤ n) :
    auxU X p ρ α (n + 1) - auxU X p ρ α n
      = α * ρ n - p (n + 1)
        + (((count X (n + 1) - (n + 1 : ℝ) * ρ (n + 1)) - (count X n - (n : ℝ) * ρ n))) := by
  unfold auxU
  simp only [Nat.add_sub_cancel]
  rw [assignMG_succ, alphaSum_succ ρ α n hn, count_succ]
  push_cast
  grind

/-- A telescoping identity for a real sequence over `Icc (ℓ+1) n`. -/
theorem sum_Icc_succ_sub (f : ℕ → ℝ) (ℓ : ℕ) :
    ∀ n, ℓ ≤ n → ∑ m ∈ Icc (ℓ + 1) n, (f m - f (m - 1)) = f n - f ℓ := by
  intro n
  induction n with
  | zero =>
    intro h
    have : ℓ = 0 := Nat.le_zero.mp h
    subst this
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ k ih =>
    intro h
    rcases Nat.lt_or_ge ℓ (k + 1) with hlt | hge
    · rw [Finset.sum_Icc_succ_top (by omega : ℓ + 1 ≤ k + 1), ih (by omega),
        Nat.add_sub_cancel]
      grind
    · have he : ℓ = k + 1 := by omega
      subst he
      rw [Finset.Icc_eq_empty (by omega)]
      simp

/-- **Telescoping identity for the auxiliary process** (blueprint `lem:U_telescope`).

For `1 ≤ ℓ ≤ n`, writing `D m := N m - m ρ m`,
`U n - U ℓ = ∑_{m=ℓ+1}^n (α ρ_{m-1} - p m) + (D n - D ℓ)`.
Rearranged, this is the blueprint's identity expressing `D n` in terms of `D ℓ`,
the summed throttling terms, and the increment of `U`. -/
theorem auxU_telescope (n ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) :
    auxU X p ρ α n - auxU X p ρ α ℓ
      = (∑ m ∈ Icc (ℓ + 1) n, (α * ρ (m - 1) - p m))
        + ((count X n - (n : ℝ) * ρ n) - (count X ℓ - (ℓ : ℝ) * ρ ℓ)) := by
  have hterm : ∀ m ∈ Icc (ℓ + 1) n,
      auxU X p ρ α m - auxU X p ρ α (m - 1)
        = (α * ρ (m - 1) - p m)
          + ((count X m - (m : ℝ) * ρ m) - (count X (m - 1) - ((m - 1 : ℕ) : ℝ) * ρ (m - 1))) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m - 1 := by omega
    have hmm : m - 1 + 1 = m := by omega
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
    have h := auxU_succ_sub X p ρ α (m - 1) hm1
    rw [hmm, hcast] at h
    exact h
  rw [← sum_Icc_succ_sub (auxU X p ρ α) ℓ n hℓn, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib]
  congr 1
  exact sum_Icc_succ_sub (fun m => count X m - (m : ℝ) * ρ m) ℓ n hℓn

/-- **Counts sum to time** (blueprint `lem:counts_sum`).
If the assignment vector sums to one at each time, then the arm counts sum to the
time index. -/
theorem counts_sum {K : ℕ} (Y : ℕ → Fin K → ℝ) (hY : ∀ j, ∑ k, Y j k = 1) (n : ℕ) :
    (∑ k, count (fun j => Y j k) n) = n := by
  simp only [count]
  rw [Finset.sum_comm]
  simp only [hY, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

/-- Last under-sampling time (blueprint `def:hitting`): the largest `m ≤ n` at
which the arm is under-sampled, encoded via `Nat.findGreatest` (which returns `0`
when no such `m` exists, matching the blueprint's convention). -/
def hitting (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ := Nat.findGreatest P n

/-- **Basic properties of the hitting time** (blueprint `lem:hitting_basic`):
`n ↦ hitting P n` is non-decreasing and bounded above by `n`. -/
theorem hitting_basic (P : ℕ → Prop) [DecidablePred P] :
    Monotone (hitting P) ∧ ∀ n, hitting P n ≤ n := by
  refine ⟨fun a b hab => Nat.findGreatest_mono_right P hab, fun n => Nat.findGreatest_le n⟩

/-- **Sign at the hitting time** (blueprint `lem:hitting_sign`, maximality part).
Strictly after the last under-sampling time (and up to `n`), the arm is no longer
under-sampled: `¬ P m` for `hitting P n < m ≤ n`. -/
theorem hitting_sign (P : ℕ → Prop) [DecidablePred P] {n m : ℕ}
    (hlt : hitting P n < m) (hle : m ≤ n) : ¬ P m :=
  Nat.findGreatest_is_greatest hlt hle

/-- **Key inequality** (blueprint `lem:preliminary_ineq`).

Whenever the throttling condition `p m ≤ α ρ_{m-1}` holds for all `ℓ+2 ≤ m ≤ n`,
`p (ℓ+1) ≤ 1`, and `0 ≤ α ρ_ℓ`, the gap `D n = N n - n ρ n` is controlled by its
value at `ℓ` plus the increment of `U`:
`D n ≤ 1 + D ℓ + (U n - U ℓ)`. -/
theorem preliminary_ineq (n ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (hp1 : p (ℓ + 1) ≤ 1) (hαρ : 0 ≤ α * ρ ℓ)
    (hthrottle : ∀ m ∈ Icc (ℓ + 2) n, p m ≤ α * ρ (m - 1)) :
    (count X n - (n : ℝ) * ρ n)
      ≤ 1 + (count X ℓ - (ℓ : ℝ) * ρ ℓ) + (auxU X p ρ α n - auxU X p ρ α ℓ) := by
  rcases hℓn.lt_or_eq with hlt | heq
  · -- `ℓ < n`: split off the first term of the telescoped sum.
    have htel := auxU_telescope X p ρ α n ℓ hℓ hℓn
    set T := ∑ m ∈ Icc (ℓ + 1) n, (α * ρ (m - 1) - p m) with hT
    have hTge : -1 ≤ T := by
      have hmemL : (ℓ + 1) ∈ Icc (ℓ + 1) n := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      have hsplit := Finset.add_sum_erase (Icc (ℓ + 1) n)
        (fun m => α * ρ (m - 1) - p m) hmemL
      have hrest : 0 ≤ ∑ m ∈ (Icc (ℓ + 1) n).erase (ℓ + 1), (α * ρ (m - 1) - p m) := by
        apply Finset.sum_nonneg
        intro m hm
        rw [Finset.mem_erase, Finset.mem_Icc] at hm
        have hmem2 : m ∈ Icc (ℓ + 2) n := Finset.mem_Icc.mpr ⟨by omega, hm.2.2⟩
        have := hthrottle m hmem2
        linarith
      rw [hT, ← hsplit]
      simp only [Nat.add_sub_cancel]
      linarith
    linarith
  · -- `ℓ = n`: the increment of `U` vanishes and `D n = D ℓ`.
    subst heq
    linarith

/-- **Smallness at the hitting time** (blueprint `lem:preliminary_small`).

If the predicate `P` implies under-sampling `N m ≤ m ρ m`, then at the last
under-sampling time the gap is nonpositive: `N ℓ - ℓ ρ ℓ ≤ 0` for
`ℓ = hitting P n`. (With the `Nat.findGreatest` convention this is the sharp
`≤ 0`, stronger than the blueprint's `≤ K m₀`.) -/
theorem preliminary_small (P : ℕ → Prop) [DecidablePred P] (n : ℕ)
    (hPspec : ∀ m, P m → count X m ≤ (m : ℝ) * ρ m) :
    count X (hitting P n) - (hitting P n : ℝ) * ρ (hitting P n) ≤ 0 := by
  rcases Nat.eq_zero_or_pos (hitting P n) with h0 | hpos
  · rw [h0]
    have hc0 : count X 0 = 0 := by simp [count]
    rw [hc0]
    simp
  · have hP : P (hitting P n) := Nat.findGreatest_of_ne_zero rfl (by omega)
    have := hPspec _ hP
    linarith

/-- Centered response martingale of a fixed arm,
`Q n = ∑_{j=1}^n X j (ξ j - θ)` (blueprint `def:Q`). -/
def respMG (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, X j * (ξ j - θ)

/-- `Q n = ∑ X ξ - θ N n`: the response martingale rewritten via the count. -/
theorem respMG_eq (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    respMG X ξ θ n = (∑ j ∈ Icc 1 n, X j * ξ j) - θ * count X n := by
  unfold respMG count
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Estimator error via `Q`** (blueprint `lem:theta_error_Q`).

On `{N n ≠ 0}`, the leading term of the estimator error equals `Q n / N n`:
`(∑ X ξ) / N n - θ = Q n / N n`. -/
theorem theta_error_Q (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) (hN : count X n ≠ 0) :
    (∑ j ∈ Icc 1 n, X j * ξ j) / count X n - θ = respMG X ξ θ n / count X n := by
  rw [respMG_eq, sub_div, mul_div_assoc, div_self hN, mul_one]

end AlphaRAR
