/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.Mathlib.Convergence
public import AlphaRAR.YDK2026.Count
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds
public meta import LeanSpec

/-!
# Deterministic core of the auxiliary processes

Several lemmas in the model and auxiliary chapters of the blueprint are purely
algebraic identities about the counting and martingale processes: they hold
pathwise and do not use any probability. This file isolates that deterministic
core.

For a fixed arm we work with real sequences `X` (assignment indicator), `p`
(selection probability) and `ρ` (plug-in target), and define the count `N`, the
assignment martingale `M`, and the auxiliary process `U` by their defining sums.

Indexing follows the `IsAlgEnvSeq` convention: patient `0` is the first patient,
so all processes sum over `Finset.range n` = patients `0, …, n-1`.

## Main results

* `AlphaRAR.count_eq`: count decomposition `N n = ∑ p + M n` (blueprint
  `lem:count_decomp`).
* `AlphaRAR.counts_sum`: the counts sum to the time index (blueprint
  `lem:counts_sum`).
* `AlphaRAR.hitting_basic`: the last under-sampling time is non-decreasing and
  bounded by `n` (blueprint `lem:hitting_basic`).
-/

@[expose] public section

open Finset Filter

open scoped Topology

namespace AlphaRAR

variable (X p ρ : ℕ → ℝ) (α : ℝ)

/-- Assignment martingale of a fixed arm, `M n = ∑_{j<n} (X j - p j)`
(blueprint `def:M`). -/
def assignMG (n : ℕ) : ℝ := ∑ j ∈ range n, (X j - p j)

/-- **Count decomposition** (blueprint `lem:count_decomp`).
`N n = ∑_{m<n} p m + M n`. -/
@[specifies assignMG "pins `M` exactly (no free additive constant): it is the count minus its \
compensator `∑ p`, which is what makes it the assignment *martingale* rather than any centring \
of the count"]
lemma count_eq (n : ℕ) : count X n = (∑ m ∈ range n, p m) + assignMG X p n := by
  simp only [count, assignMG, Finset.sum_sub_distrib]
  grind

/-- Increment of the assignment martingale: `M (n+1) = M n + (X n - p n)`. -/
@[specifies assignMG "the increment pairs the indicator `X n` with the selection probability `p n` \
at the *same* index — the alignment that makes each increment a martingale difference"]
lemma assignMG_succ (n : ℕ) :
    assignMG X p (n + 1) = assignMG X p n + (X n - p n) := by
  unfold assignMG
  rw [Finset.sum_range_succ]

/-- Auxiliary process `U n = ∑_{m<n} α ρ m + M n - n ρ n` (blueprint `def:U`). The leading `α ρ`
sum runs over `range n`, so at time `n` it uses the plug-in targets of patients `0, …, n-1`. -/
def auxU (n : ℕ) : ℝ := (∑ m ∈ range n, α * ρ m) + assignMG X p n - (n : ℝ) * ρ n

/-- **Increment of the auxiliary process** (blueprint `lem:U_increment`).

Writing `D n := N n - n ρ n`, `U (n+1) - U n = α ρ_n - p n + (D (n+1) - D n)`. The leading term
`α ρ_n` pairs the selection probability `p_n` with the plug-in target `ρ_n` at the same index, so
the throttle discharged downstream is `p_n ≤ α ρ_n` (patient `n` uses the target of patients
`0, …, n-1`). Valid for all `n` (the `α ρ`-sum grows at every step). -/
@[specifies auxU "the reason `U` is assembled this way: its increment is the throttle slack \
`α ρ_n - p_n` plus the increment of the gap `D = N - n ρ`, with `p_n` and `ρ_n` at the same index. \
Any other pairing of the two indices would not produce a sign-definite slack term"]
lemma auxU_succ_sub (n : ℕ) :
    auxU X p ρ α (n + 1) - auxU X p ρ α n
      = α * ρ n - p n
        + (((count X (n + 1) - (n + 1 : ℝ) * ρ (n + 1)) - (count X n - (n : ℝ) * ρ n))) := by
  unfold auxU
  rw [assignMG_succ, Finset.sum_range_succ, count_succ]
  push_cast
  ring

/-- A telescoping identity for a real sequence over `Ico ℓ n`. -/
lemma sum_Ico_succ_sub (f : ℕ → ℝ) (ℓ : ℕ) :
    ∀ n, ℓ ≤ n → ∑ m ∈ Ico ℓ n, (f (m + 1) - f m) = f n - f ℓ := by
  intro n
  induction n with
  | zero =>
    intro h
    have : ℓ = 0 := Nat.le_zero.mp h
    subst this
    simp
  | succ k ih =>
    intro h
    rcases Nat.lt_or_ge ℓ (k + 1) with hlt | hge
    · rw [Finset.sum_Ico_succ_top (by omega : ℓ ≤ k), ih (by omega)]
      ring
    · have he : ℓ = k + 1 := by omega
      subst he
      simp

/-- **Telescoping identity for the auxiliary process** (blueprint `lem:U_telescope`).

For `ℓ ≤ n`, writing `D m := N m - m ρ m`,
`U n - U ℓ = ∑_{m=ℓ}^{n-1} (α ρ_m - p m) + (D n - D ℓ)`.
Rearranged, this is the blueprint's identity expressing `D n` in terms of `D ℓ`,
the summed throttling terms, and the increment of `U`. -/
@[specifies auxU "what `U` is for: over any window it converts the accumulated throttle slack into \
a bound on the gap `D`, which is the only way `U` is ever used"]
lemma auxU_telescope (n ℓ : ℕ) (hℓn : ℓ ≤ n) :
    auxU X p ρ α n - auxU X p ρ α ℓ
      = (∑ m ∈ Ico ℓ n, (α * ρ m - p m))
        + ((count X n - (n : ℝ) * ρ n) - (count X ℓ - (ℓ : ℝ) * ρ ℓ)) := by
  have hterm : ∀ m ∈ Ico ℓ n,
      auxU X p ρ α (m + 1) - auxU X p ρ α m
        = (α * ρ m - p m)
          + ((count X (m + 1) - ((m + 1 : ℕ) : ℝ) * ρ (m + 1))
            - (count X m - (m : ℝ) * ρ m)) := by
    intro m hm
    have h := auxU_succ_sub X p ρ α m
    push_cast at h ⊢
    exact h
  rw [← sum_Ico_succ_sub (auxU X p ρ α) ℓ n hℓn, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib]
  congr 1
  exact sum_Ico_succ_sub (fun m ↦ count X m - (m : ℝ) * ρ m) ℓ n hℓn

/-- **Exact `M`-explicit `U`-increment identity** (algebraic backbone of blueprint
`lem:diff_U_decomp`).

For `ℓ ≤ n`, directly from the definition `U n = ∑_{m<n} α ρ_m + M n - n ρ n`,
`U n - U ℓ = ∑_{m=ℓ}^{n-1} α ρ_m + (M n - M ℓ) + (ℓ ρ_ℓ - n ρ_n)`,
keeping the assignment martingale `M = assignMG` explicit (unlike `auxU_telescope`, which expands it
through the throttling increments). This is the form the normality-chapter decomposition uses, since
the martingale LIL then applies to `M n - M ℓ`. -/
lemma auxU_sub (n ℓ : ℕ) (hℓn : ℓ ≤ n) :
    auxU X p ρ α n - auxU X p ρ α ℓ
      = (∑ m ∈ Ico ℓ n, α * ρ m) + (assignMG X p n - assignMG X p ℓ)
        + ((ℓ : ℝ) * ρ ℓ - (n : ℝ) * ρ n) := by
  unfold auxU
  rw [Finset.sum_Ico_eq_sub _ hℓn]
  ring

/-- **Windowed Cesàro drift bound** (drift-control behind blueprint `lem:diff_U_decomp`).

If `u m → v`, then for an arbitrary window sequence `ℓ_n ≤ n` (bounded or diverging), the deviation
sum over the window `[ℓ_n, n)` is `o(n - ℓ_n)`: for every `ε > 0`, eventually
`|∑_{m=ℓ_n}^{n-1} (u m - v)| ≤ ε (n - ℓ_n)`.

The window is split at a threshold `N` past which `|u m - v| ≤ ε/2`. The tail terms (`m ≥ N`)
contribute at most `(ε/2)(n - ℓ_n)`; the finitely many head terms (`m < N`) contribute at most a
fixed constant `S`, which is `≤ (ε/2)(n - ℓ_n)` once `n` is large (and vanishes outright once the
window starts past `N`). -/
lemma abs_sum_Ico_sub_le_of_tendsto {u : ℕ → ℝ} {v : ℝ} (hu : Tendsto u atTop (𝓝 v))
    {ℓ : ℕ → ℕ} (hℓ : ∀ n, ℓ n ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, |∑ m ∈ Ico (ℓ n) n, (u m - v)| ≤ ε * ((n : ℝ) - ℓ n) := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu (ε / 2) (by positivity)
  simp only [Real.dist_eq] at hN
  set S : ℝ := ∑ m ∈ range N, |u m - v| with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun m _ ↦ abs_nonneg _
  have hthresh : Tendsto (fun n : ℕ ↦ ε * ((n : ℝ) - N)) atTop atTop :=
    Tendsto.const_mul_atTop hε (tendsto_atTop_add_const_right atTop (-(N : ℝ))
      tendsto_natCast_atTop_atTop)
  filter_upwards [hthresh.eventually_ge_atTop (2 * S)] with n hn
  have hℓn : ℓ n ≤ n := hℓ n
  have hℓnR : (ℓ n : ℝ) ≤ n := by exact_mod_cast hℓn
  have hcard : (((Ico (ℓ n) n).filter (fun m ↦ ¬ m < N)).card : ℝ) ≤ (n : ℝ) - ℓ n := by
    calc (((Ico (ℓ n) n).filter (fun m ↦ ¬ m < N)).card : ℝ)
        ≤ ((Ico (ℓ n) n).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
      _ = (n : ℝ) - ℓ n := by rw [Nat.card_Ico, Nat.cast_sub hℓn]
  have hbad : (∑ m ∈ (Ico (ℓ n) n).filter (· < N), |u m - v|) ≤ ε / 2 * ((n : ℝ) - ℓ n) := by
    rcases Nat.lt_or_ge (ℓ n) N with hlN | hlN
    · have hbadS : (∑ m ∈ (Ico (ℓ n) n).filter (· < N), |u m - v|) ≤ S := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm ↦ ?_) (fun m _ _ ↦ abs_nonneg _)
        simp only [Finset.mem_filter, Finset.mem_Ico] at hm
        exact Finset.mem_range.mpr hm.2
      have hlNR : (ℓ n : ℝ) < N := by exact_mod_cast hlN
      nlinarith [hn, hbadS, hSnn]
    · have hempty : (Ico (ℓ n) n).filter (· < N) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro m hm
        simp only [Finset.mem_Ico] at hm
        omega
      rw [hempty, Finset.sum_empty]
      have : (0 : ℝ) ≤ (n : ℝ) - ℓ n := by linarith
      positivity
  have hgood : (∑ m ∈ (Ico (ℓ n) n).filter (fun m ↦ ¬ m < N), |u m - v|)
      ≤ ε / 2 * ((n : ℝ) - ℓ n) := by
    calc (∑ m ∈ (Ico (ℓ n) n).filter (fun m ↦ ¬ m < N), |u m - v|)
        ≤ ∑ _m ∈ (Ico (ℓ n) n).filter (fun m ↦ ¬ m < N), (ε / 2) := by
          refine Finset.sum_le_sum fun m hm ↦ ?_
          simp only [Finset.mem_filter, not_lt] at hm
          exact (hN m hm.2).le
      _ = (((Ico (ℓ n) n).filter (fun m ↦ ¬ m < N)).card : ℝ) * (ε / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) - ℓ n) * (ε / 2) := by
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ε / 2 * ((n : ℝ) - ℓ n) := by ring
  calc |∑ m ∈ Ico (ℓ n) n, (u m - v)|
      ≤ ∑ m ∈ Ico (ℓ n) n, |u m - v| := Finset.abs_sum_le_sum_abs _ _
    _ = (∑ m ∈ (Ico (ℓ n) n).filter (· < N), |u m - v|)
          + ∑ m ∈ (Ico (ℓ n) n).filter (fun m ↦ ¬ m < N), |u m - v| :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ ε / 2 * ((n : ℝ) - ℓ n) + ε / 2 * ((n : ℝ) - ℓ n) := add_le_add hbad hgood
    _ = ε * ((n : ℝ) - ℓ n) := by ring

/-- **Additive decomposition of the `U`-increment** (blueprint `lem:diff_U_decomp`).

If the plug-in target converges, `ρ n → v`, then for an arbitrary window `ℓ_n ≤ n`, the
`U`-increment equals its leading drift `(n - ℓ_n)(-(1-α)v)`, the increment `M_n - M_{ℓ_n}`, and the
boundary term `ℓ_n(ρ_{ℓ_n} - ρ_n)`, up to an `o(n - ℓ_n)` remainder: for every `ε > 0`, eventually
`|(U_n - U_{ℓ_n}) - [(n-ℓ_n)(-(1-α)v) + (M_n - M_{ℓ_n}) + ℓ_n(ρ_{ℓ_n} - ρ_n)]| ≤ ε (n - ℓ_n)`.

The exact identity is `auxU_sub`; the remainder `α·∑_{[ℓ_n,n)}(ρ_m - v) - (n-ℓ_n)(ρ_n - v)` is
controlled by the windowed Cesàro bound `abs_sum_Ico_sub_le_of_tendsto` (first term) and by
`ρ_n → v` (second term). -/
lemma diff_U_decomp {v : ℝ} (hρ : Tendsto ρ atTop (𝓝 v)) {ℓ : ℕ → ℕ} (hℓ : ∀ n, ℓ n ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, |auxU X p ρ α n - auxU X p ρ α (ℓ n)
        - (((n : ℝ) - ℓ n) * (-(1 - α) * v) + (assignMG X p n - assignMG X p (ℓ n))
          + (ℓ n : ℝ) * (ρ (ℓ n) - ρ n))| ≤ ε * ((n : ℝ) - ℓ n) := by
  have hε' : 0 < ε / (2 * (|α| + 1)) := by positivity
  have hces := abs_sum_Ico_sub_le_of_tendsto hρ hℓ hε'
  have hρev : ∀ᶠ n in atTop, |ρ n - v| ≤ ε / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hρ (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [← Real.dist_eq]; exact (hN n hn).le
  have hfactor : |α| * (ε / (2 * (|α| + 1))) ≤ ε / 2 := by
    have hp : (0 : ℝ) < 2 * (|α| + 1) := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hp]
    nlinarith [abs_nonneg α, hε.le]
  filter_upwards [hces, hρev] with n hcesn hρn
  have hℓn : ℓ n ≤ n := hℓ n
  have hℓnR : (ℓ n : ℝ) ≤ n := by exact_mod_cast hℓn
  have hdnn : (0 : ℝ) ≤ (n : ℝ) - ℓ n := by linarith
  have hsum : ∑ m ∈ Ico (ℓ n) n, α * ρ m
      = α * (∑ m ∈ Ico (ℓ n) n, (ρ m - v)) + α * ((n : ℝ) - ℓ n) * v := by
    have hsv : ∑ m ∈ Ico (ℓ n) n, (ρ m - v)
        = (∑ m ∈ Ico (ℓ n) n, ρ m) - ((n : ℝ) - ℓ n) * v := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hℓn]
    rw [hsv, ← Finset.mul_sum]
    ring
  have hdrift : auxU X p ρ α n - auxU X p ρ α (ℓ n)
        - (((n : ℝ) - ℓ n) * (-(1 - α) * v) + (assignMG X p n - assignMG X p (ℓ n))
          + (ℓ n : ℝ) * (ρ (ℓ n) - ρ n))
      = α * (∑ m ∈ Ico (ℓ n) n, (ρ m - v)) - ((n : ℝ) - ℓ n) * (ρ n - v) := by
    rw [auxU_sub X p ρ α n (ℓ n) hℓn, hsum]
    ring
  rw [hdrift]
  calc |α * (∑ m ∈ Ico (ℓ n) n, (ρ m - v)) - ((n : ℝ) - ℓ n) * (ρ n - v)|
      ≤ |α * (∑ m ∈ Ico (ℓ n) n, (ρ m - v))| + |((n : ℝ) - ℓ n) * (ρ n - v)| :=
        abs_sub _ _
    _ = |α| * |∑ m ∈ Ico (ℓ n) n, (ρ m - v)| + ((n : ℝ) - ℓ n) * |ρ n - v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hdnn]
    _ ≤ |α| * (ε / (2 * (|α| + 1)) * ((n : ℝ) - ℓ n)) + ((n : ℝ) - ℓ n) * (ε / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hcesn (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hρn hdnn)
    _ = ((n : ℝ) - ℓ n) * (|α| * (ε / (2 * (|α| + 1))) + ε / 2) := by ring
    _ ≤ ((n : ℝ) - ℓ n) * (ε / 2 + ε / 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hfactor]) hdnn
    _ = ε * ((n : ℝ) - ℓ n) := by ring

/-- Last under-sampling time (blueprint `def:hitting`): the largest `m ≤ n` at
which the arm is under-sampled, encoded via `Nat.findGreatest` (which returns `0`
when no such `m` exists, matching the blueprint's convention). -/
def hitting (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ := Nat.findGreatest P n

/-- **Basic properties of the hitting time** (blueprint `lem:hitting_basic`):
`n ↦ hitting P n` is non-decreasing and bounded above by `n`. -/
@[specifies hitting "the two facts that make it usable as a random time: it never looks past the \
horizon `n`, and enlarging the horizon can only move it forward"]
lemma hitting_basic (P : ℕ → Prop) [DecidablePred P] :
    Monotone (hitting P) ∧ ∀ n, hitting P n ≤ n := by
  refine ⟨fun a b hab ↦ Nat.findGreatest_mono_right P hab, fun n ↦ Nat.findGreatest_le n⟩

/-- **Sign at the hitting time** (blueprint `lem:hitting_sign`, maximality part).
Strictly after the last under-sampling time (and up to `n`), the arm is no longer
under-sampled: `¬ P m` for `hitting P n < m ≤ n`. -/
@[specifies hitting "the maximality that makes it the *last* such time rather than merely some \
such time: nothing in `(hitting P n, n]` satisfies `P`"]
lemma hitting_sign (P : ℕ → Prop) [DecidablePred P] {n m : ℕ}
    (hlt : hitting P n < m) (hle : m ≤ n) : ¬ P m :=
  Nat.findGreatest_is_greatest hlt hle

/-! ### Characterization of the hitting time

The two `@[specifies]` claims above are the halves of one description: `hitting P n` is the
**greatest** `m ≤ n` satisfying `P`, and `0` when there is none. `IsHitting` states that, including
the fallback, and it pins the value down exactly — a greatest element is unique, and the fallback
branch is what settles the empty case rather than leaving it free. -/

/-- **`m` is the last time up to `n` at which `P` holds**: `m ≤ n`, nothing in `(m, n]` satisfies
`P`, and `m` itself satisfies `P` unless it is the fallback `0`. -/
@[characterization property hitting "the greatest `m ≤ n` with `P m`, and `0` when there is none \
— including the fallback, which is the convention a reader has to be told"]
structure IsHitting (P : ℕ → Prop) (n m : ℕ) : Prop where
  /-- `m` does not look past the horizon. -/
  le : m ≤ n
  /-- `m` is the *last* such time: nothing strictly after it, up to `n`, satisfies `P`. -/
  greatest : ∀ j, m < j → j ≤ n → ¬ P j
  /-- `m` is itself such a time, unless it is the fallback. Both branches are needed: without the
  left one every non-hit would qualify, and without the right one there would be no value at all
  when `P` fails throughout `[0, n]`. -/
  hit_or_zero : P m ∨ m = 0

/-- **The hitting time is the last such time** — the existence half of the characterization. -/
@[characterization existence]
lemma isHitting_hitting (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : IsHitting P n (hitting P n) where
  le := Nat.findGreatest_le n
  greatest _ hlt hle := hitting_sign P hlt hle
  hit_or_zero := by
    rcases Nat.eq_zero_or_pos (hitting P n) with h | h
    · exact Or.inr h
    · obtain ⟨j, _, hjn, hj⟩ := Nat.findGreatest_pos.mp h
      exact Or.inl (Nat.findGreatest_spec hjn hj)

/-- **Nothing else is** — the uniqueness half: of two candidates the smaller one's maximality
rules the larger out, which forces the larger to be the fallback `0` and hence not larger at all. -/
@[characterization uniqueness]
lemma IsHitting.eq_hitting {P : ℕ → Prop} [DecidablePred P] {n m : ℕ} (hm : IsHitting P n m) :
    m = hitting P n := by
  have hh := isHitting_hitting P n
  by_contra hne
  rcases Nat.lt_or_ge m (hitting P n) with hlt | hge
  · rcases hh.hit_or_zero with hP | hz
    · exact hm.greatest _ hlt hh.le hP
    · omega
  · have hlt : hitting P n < m := lt_of_le_of_ne hge (Ne.symm hne)
    rcases hm.hit_or_zero with hP | hz
    · exact hh.greatest _ hlt hm.le hP
    · omega

/-- **Key inequality** (blueprint `lem:preliminary_ineq`).

Whenever the throttling condition `p m ≤ α ρ_m` holds for all `ℓ+1 ≤ m ≤ n-1`,
`p ℓ ≤ 1`, and `0 ≤ α ρ_ℓ`, the gap `D n = N n - n ρ n` is controlled by its
value at `ℓ` plus the increment of `U`:
`D n ≤ 1 + D ℓ + (U n - U ℓ)`. -/
lemma preliminary_ineq (n ℓ : ℕ) (hℓn : ℓ ≤ n)
    (hp1 : p ℓ ≤ 1) (hαρ : 0 ≤ α * ρ ℓ)
    (hthrottle : ∀ m ∈ Ico (ℓ + 1) n, p m ≤ α * ρ m) :
    (count X n - (n : ℝ) * ρ n)
      ≤ 1 + (count X ℓ - (ℓ : ℝ) * ρ ℓ) + (auxU X p ρ α n - auxU X p ρ α ℓ) := by
  rcases hℓn.lt_or_eq with hlt | heq
  · -- `ℓ < n`: split off the first term of the telescoped sum.
    have htel := auxU_telescope X p ρ α n ℓ hℓn
    set T := ∑ m ∈ Ico ℓ n, (α * ρ m - p m) with hT
    have hTge : -1 ≤ T := by
      have hmemL : ℓ ∈ Ico ℓ n := Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩
      have hsplit := Finset.add_sum_erase (Ico ℓ n) (fun m ↦ α * ρ m - p m) hmemL
      have hrest : 0 ≤ ∑ m ∈ (Ico ℓ n).erase ℓ, (α * ρ m - p m) := by
        apply Finset.sum_nonneg
        intro m hm
        rw [Finset.mem_erase, Finset.mem_Ico] at hm
        have := hthrottle m (Finset.mem_Ico.mpr ⟨by omega, hm.2.2⟩)
        linarith
      have hval : T = (α * ρ ℓ - p ℓ)
          + ∑ m ∈ (Ico ℓ n).erase ℓ, (α * ρ m - p m) := by
        rw [hT, ← hsplit]
      rw [hval]
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
lemma preliminary_small (P : ℕ → Prop) [DecidablePred P] (n : ℕ)
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

/-- **Generic key inequality from the aRTS throttle** (blueprint `eq:generic_ineq`, deterministic
packaging of `prop:aRTS_generic`). With `ℓ_n = hitting P n` the last under-sampling time, the aRTS
throttle `¬ P m → p_m ≤ α ρ_m` (whenever the arm is over-sampled at `m`, its selection probability
is throttled), together with `p ≤ 1` and `0 ≤ α ρ`, gives the generic inequality with constant `1`.
From `auxU_telescope`, `D n = D ℓ + (U n - U ℓ) + ∑_{m∈[ℓ,n)} (p_m - α ρ_m)`; each summand with
`m > ℓ` is `≤ 0` (by the throttle at `m`, over-sampled via `hitting_sign`), and the single boundary
term `m = ℓ` is `≤ 1` (by `p ≤ 1`), so the sum is `≤ 1`. No lower bound on `ℓ_n` is needed: the
identity holds at `ℓ_n = 0` too, since the `α ρ`-sum of `U` grows at every step. -/
lemma generic_ineq_of_hitting (P : ℕ → Prop) [DecidablePred P]
    (hthrottle : ∀ m, ¬ P m → p m ≤ α * ρ m)
    (hp1 : ∀ m, p m ≤ 1) (hαρ : ∀ m, 0 ≤ α * ρ m) (n : ℕ) :
    count X n - (n : ℝ) * ρ n
      ≤ 1 + (count X (hitting P n) - (hitting P n : ℝ) * ρ (hitting P n))
        + (auxU X p ρ α n - auxU X p ρ α (hitting P n)) := by
  let ℓ := hitting P n
  have htel := auxU_telescope X p ρ α n ℓ (Nat.findGreatest_le n)
  -- Each summand `p m - α ρ m` is `≤ 1` at the boundary index `m = ℓ`, `≤ 0` after.
  have hbound : ∑ m ∈ Finset.Ico ℓ n, (p m - α * ρ m) ≤ 1 := by
    have hterm : ∀ m ∈ Finset.Ico ℓ n,
        p m - α * ρ m ≤ (if m = ℓ then (1 : ℝ) else 0) := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      by_cases hm2 : m = ℓ
      · rw [ite_eq_left hm2]; linarith [hp1 m, hαρ m]
      · rw [ite_eq_right hm2]
        have hnotP : ¬ P m := hitting_sign P (n := n) (by omega) hm.2.le
        linarith [hthrottle m hnotP]
    calc ∑ m ∈ Finset.Ico ℓ n, (p m - α * ρ m)
        ≤ ∑ m ∈ Finset.Ico ℓ n, (if m = ℓ then (1 : ℝ) else 0) := Finset.sum_le_sum hterm
      _ = (((Finset.Ico ℓ n).filter (· = ℓ)).card : ℝ) := by rw [Finset.sum_boole]
      _ ≤ 1 := by
          have hcard : ((Finset.Ico ℓ n).filter (· = ℓ)).card ≤ 1 := by
            rw [Finset.filter_eq']
            split <;> simp
          exact_mod_cast hcard
  -- The reverse-signed sum, to rewrite `htel`.
  have hsum0 : (∑ m ∈ Finset.Ico ℓ n, (α * ρ m - p m))
      + (∑ m ∈ Finset.Ico ℓ n, (p m - α * ρ m)) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun m _ ↦ by ring
  linarith [htel, hbound, hsum0]

/-- **Generic smallness from the throttle** (blueprint `eq:generic_small`, deterministic packaging).
If `P` implies under-sampling (`P m → N_m ≤ m ρ_m`), then at the last under-sampling time the gap
is nonpositive (`preliminary_small`), so `(N_{ℓ_n} - ℓ_n ρ_{ℓ_n})/n < δ` eventually for `δ > 0`. -/
lemma generic_small_of_hitting (P : ℕ → Prop) [DecidablePred P]
    (hunder : ∀ m, P m → count X m ≤ (m : ℝ) * ρ m) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      (count X (hitting P n) - (hitting P n : ℝ) * ρ (hitting P n)) / (n : ℝ) < δ := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnum : count X (hitting P n) - (hitting P n : ℝ) * ρ (hitting P n) ≤ 0 :=
    preliminary_small X ρ P n hunder
  have hle : (count X (hitting P n) - (hitting P n : ℝ) * ρ (hitting P n)) / (n : ℝ) ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨hnum, hnR.le⟩)
  linarith

/-- Centered response martingale of a fixed arm,
`Q n = ∑_{j<n} X j (ξ j - θ)` (blueprint `def:Q`). -/
def respMG (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, X j * (ξ j - θ)

/-- `Q n = ∑ X ξ - θ N n`: the response martingale rewritten via the count. -/
@[specifies respMG "the centring is applied once per *pull*, not once per patient: `Q` subtracts \
`θ` times the count `N n`, not `θ n`"]
lemma respMG_eq (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    respMG X ξ θ n = (∑ j ∈ range n, X j * ξ j) - θ * count X n := by
  unfold respMG count
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Estimator error via `Q`** (blueprint `lem:theta_error_Q`).

On `{N n ≠ 0}`, the leading term of the estimator error equals `Q n / N n`:
`(∑ X ξ) / N n - θ = Q n / N n`. -/
@[specifies respMG "what `Q` is for: divided by the count it is exactly the sample-mean error, so \
every rate proved for `Q` is a rate for the estimator"]
lemma theta_error_Q (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) (hN : count X n ≠ 0) :
    (∑ j ∈ range n, X j * ξ j) / count X n - θ = respMG X ξ θ n / count X n := by
  rw [respMG_eq, sub_div, mul_div_assoc, div_self hN, mul_one]

/-- Sequential estimator of a fixed arm (blueprint `def:estimator`),
`θ̂ n = (∑_{j<n} X j ξ j + θ₀) / (N n + 1)`, with initial value `θ₀` and the `+1`
regularization in the denominator. -/
noncomputable def estimator (ξ : ℕ → ℝ) (θ₀ : ℝ) (n : ℕ) : ℝ :=
  ((∑ j ∈ range n, X j * ξ j) + θ₀) / (count X n + 1)

/-- **Exact estimator error** (blueprint `lem:estimator_bahadur`, exact form).

The regularized estimator has the *exact* error decomposition
`θ̂ n - θ = (Q n + (θ₀ - θ)) / (N n + 1)`, valid whenever `N n + 1 ≠ 0` (always, for
`{0,1}`-valued assignment indicators). Since `Q n = O(√(n \log n))` and the numerator offset
`θ₀ - θ` is constant, this is the Bahadur representation
`θ̂ n = \tfrac1{N n}∑ X ξ + o(N n^{-1/2})` in sharp, remainder-free form. -/
@[specifies estimator "accounts exactly for the `+θ₀` / `+1` regularization: it contributes the \
single constant `θ₀ - θ` to the numerator and nothing else, so the regularized estimator has the \
same error expansion as the plain sample mean with no remainder term"]
lemma estimator_sub_eq (ξ : ℕ → ℝ) (θ θ₀ : ℝ) (n : ℕ) (hN : count X n + 1 ≠ 0) :
    estimator X ξ θ₀ n - θ = (respMG X ξ θ n + (θ₀ - θ)) / (count X n + 1) := by
  rw [estimator, respMG_eq]
  field_simp
  ring

/-- **Estimator difference identity** (algebraic backbone of `lem:ell_rho_control`). The estimator
difference at two times splits into a "reweighting" term (carrying `Q_ℓ`, scaled by the count
increment `N_n - N_ℓ`) and an "increment" term (carrying `Q_n - Q_ℓ`):
`θ̂_ℓ - θ̂_n = (Q_ℓ + (θ₀-θ))(N_n - N_ℓ)/((N_ℓ+1)(N_n+1)) - (Q_n - Q_ℓ)/(N_n+1)`. -/
lemma estimator_diff_eq (ξ : ℕ → ℝ) (θ θ₀ : ℝ) (ℓ n : ℕ)
    (hℓ : count X ℓ + 1 ≠ 0) (hn : count X n + 1 ≠ 0) :
    estimator X ξ θ₀ ℓ - estimator X ξ θ₀ n
      = (respMG X ξ θ ℓ + (θ₀ - θ)) * (count X n - count X ℓ)
          / ((count X ℓ + 1) * (count X n + 1))
        - (respMG X ξ θ n - respMG X ξ θ ℓ) / (count X n + 1) := by
  have hℓ' := estimator_sub_eq X ξ θ θ₀ ℓ hℓ
  have hn' := estimator_sub_eq X ξ θ θ₀ n hn
  have hkey : estimator X ξ θ₀ ℓ - estimator X ξ θ₀ n
      = (estimator X ξ θ₀ ℓ - θ) - (estimator X ξ θ₀ n - θ) := by ring
  rw [hkey, hℓ', hn']
  field_simp
  ring

/-- **Deterministic increment bound for the scaled estimator difference** (deterministic core of
`lem:ell_rho_control`). For `{0,1}`-bounded increments `X` and `ℓ ≤ n`, the scaled difference
`ℓ|θ̂_ℓ - θ̂_n|` splits into a reweighting part `∝ (n-ℓ)` and an increment part `∝ |Q_n - Q_ℓ|`:
`ℓ|θ̂_ℓ - θ̂_n| ≤ ℓ(|Q_ℓ|+|θ₀-θ|)/((N_ℓ+1)(N_n+1))·(n-ℓ) + ℓ/(N_n+1)·|Q_n - Q_ℓ|`. -/
lemma abs_estimator_diff_le (hX0 : ∀ j, 0 ≤ X j) (hX1 : ∀ j, X j ≤ 1)
    (ξ : ℕ → ℝ) (θ θ₀ : ℝ) {ℓ n : ℕ} (hℓn : ℓ ≤ n) :
    (ℓ : ℝ) * |estimator X ξ θ₀ ℓ - estimator X ξ θ₀ n|
      ≤ (ℓ : ℝ) * (|respMG X ξ θ ℓ| + |θ₀ - θ|) / ((count X ℓ + 1) * (count X n + 1))
          * ((n : ℝ) - ℓ)
        + (ℓ : ℝ) / (count X n + 1) * |respMG X ξ θ n - respMG X ξ θ ℓ| := by
  have hNℓ : (0 : ℝ) ≤ count X ℓ := Finset.sum_nonneg fun j _ ↦ hX0 j
  have hNn : (0 : ℝ) ≤ count X n := Finset.sum_nonneg fun j _ ↦ hX0 j
  have hNℓ1 : (0 : ℝ) < count X ℓ + 1 := by linarith
  have hNn1 : (0 : ℝ) < count X n + 1 := by linarith
  have hΔ : count X n - count X ℓ = ∑ j ∈ Finset.Ico ℓ n, X j := (Finset.sum_Ico_eq_sub X hℓn).symm
  have hΔnn : (0 : ℝ) ≤ count X n - count X ℓ := by
    rw [hΔ]; exact Finset.sum_nonneg fun j _ ↦ hX0 j
  have hΔle : count X n - count X ℓ ≤ (n : ℝ) - ℓ := by
    rw [hΔ]
    calc ∑ j ∈ Finset.Ico ℓ n, X j
        ≤ ∑ _j ∈ Finset.Ico ℓ n, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ hX1 j
      _ = (n : ℝ) - ℓ := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hℓn]
  have hℓnn : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
  rw [estimator_diff_eq X ξ θ θ₀ ℓ n hNℓ1.ne' hNn1.ne']
  set A := (respMG X ξ θ ℓ + (θ₀ - θ)) * (count X n - count X ℓ)
    / ((count X ℓ + 1) * (count X n + 1)) with hAdef
  set B := (respMG X ξ θ n - respMG X ξ θ ℓ) / (count X n + 1) with hBdef
  have hAabs : |A| = |respMG X ξ θ ℓ + (θ₀ - θ)| * (count X n - count X ℓ)
      / ((count X ℓ + 1) * (count X n + 1)) := by
    rw [hAdef, abs_div, abs_mul, abs_of_nonneg hΔnn, abs_of_pos (mul_pos hNℓ1 hNn1)]
  have hBabs : |B| = |respMG X ξ θ n - respMG X ξ θ ℓ| / (count X n + 1) := by
    rw [hBdef, abs_div, abs_of_pos hNn1]
  have hDEN : (0 : ℝ) < (count X ℓ + 1) * (count X n + 1) := mul_pos hNℓ1 hNn1
  have hterm1 : (ℓ : ℝ) * |A| ≤ (ℓ : ℝ) * (|respMG X ξ θ ℓ| + |θ₀ - θ|)
      / ((count X ℓ + 1) * (count X n + 1)) * ((n : ℝ) - ℓ) := by
    rw [hAabs,
      show (ℓ : ℝ) * (|respMG X ξ θ ℓ + (θ₀ - θ)| * (count X n - count X ℓ)
          / ((count X ℓ + 1) * (count X n + 1)))
        = (ℓ * |respMG X ξ θ ℓ + (θ₀ - θ)| * (count X n - count X ℓ))
          / ((count X ℓ + 1) * (count X n + 1)) from by ring,
      show (ℓ : ℝ) * (|respMG X ξ θ ℓ| + |θ₀ - θ|) / ((count X ℓ + 1) * (count X n + 1))
          * ((n : ℝ) - ℓ)
        = (ℓ * (|respMG X ξ θ ℓ| + |θ₀ - θ|) * ((n : ℝ) - ℓ))
          / ((count X ℓ + 1) * (count X n + 1)) from by ring]
    gcongr
    exact abs_add_le _ _
  have hterm2 : (ℓ : ℝ) * |B|
      = (ℓ : ℝ) / (count X n + 1) * |respMG X ξ θ n - respMG X ξ θ ℓ| := by
    rw [hBabs]; ring
  calc (ℓ : ℝ) * |A - B|
      ≤ (ℓ : ℝ) * (|A| + |B|) := by gcongr; exact abs_sub A B
    _ = (ℓ : ℝ) * |A| + (ℓ : ℝ) * |B| := by ring
    _ ≤ (ℓ : ℝ) * (|respMG X ξ θ ℓ| + |θ₀ - θ|) / ((count X ℓ + 1) * (count X n + 1))
          * ((n : ℝ) - ℓ) + (ℓ : ℝ) / (count X n + 1) * |respMG X ξ θ n - respMG X ξ θ ℓ| :=
        add_le_add hterm1 (le_of_eq hterm2)

/-- **Coefficient bound for the increment term** (deterministic core of `lem:ell_rho_control`).
If the count grows linearly, `N_n / n → v > 0`, then `n / (N_n + 1) ≤ 2/v` eventually. In particular
`ℓ_n / (N_n + 1) ≤ 2/v` for `ℓ_n ≤ n`, so the coefficient `h_n = ℓ_n/(N_n+1)` is eventually
bounded. -/
lemma eventually_natCast_div_add_one_le {N : ℕ → ℝ} {v : ℝ} (hv : 0 < v)
    (hN : Tendsto (fun n : ℕ ↦ N n / (n : ℝ)) atTop (𝓝 v)) :
    ∀ᶠ n in atTop, ((n : ℕ) : ℝ) / (N n + 1) ≤ 2 / v := by
  have hadd : Tendsto (fun n : ℕ ↦ (N n + 1) / (n : ℝ)) atTop (𝓝 v) := by
    have hone : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h0 : Tendsto (fun n : ℕ ↦ N n / (n : ℝ) + 1 / (n : ℝ)) atTop (𝓝 (v + 0)) := hN.add hone
    rw [add_zero] at h0
    exact h0.congr fun n ↦ (add_div (N n) 1 (n : ℝ)).symm
  have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ) / (N n + 1)) atTop (𝓝 v⁻¹) :=
    (hadd.inv₀ hv.ne').congr fun n ↦ inv_div (N n + 1) (n : ℝ)
  refine (hinv.eventually_lt_const (show v⁻¹ < 2 / v from ?_)).mono fun n h ↦ h.le
  have hvi : (0 : ℝ) < v⁻¹ := inv_pos.mpr hv
  rw [div_eq_mul_inv]; linarith

/-- **Absolute estimator error bound**: `|θ̂ n - θ| ≤ (|Q n| + |θ₀ - θ|) / (N n + 1)`.
The pathwise backbone of the LIL rate `lem:theta_LIL`: with `|Q n| = O(√(n \log n))` and
`N n + 1 ≍ v_k n`, it gives `|θ̂ n - θ| = O(√(\log n / n))`. -/
lemma abs_estimator_sub_le (ξ : ℕ → ℝ) (θ θ₀ : ℝ) (n : ℕ) (hN : 0 < count X n + 1) :
    |estimator X ξ θ₀ n - θ| ≤ (|respMG X ξ θ n| + |θ₀ - θ|) / (count X n + 1) := by
  rw [estimator_sub_eq X ξ θ θ₀ n (ne_of_gt hN), abs_div, abs_of_pos hN]
  gcongr
  exact abs_add_le _ _

/-- **Generic estimator rate from an abstract martingale rate** (the shared core of the
`log` and `log log` LIL rates for the estimator, blueprint `lem:theta_LIL`).

If the response martingale is bounded by an abstract rate `r` — `|Q_n| ≤ C·r n` eventually — with
`1 ≤ r n` eventually (so the constant numerator offset `θ₀ - θ` is absorbed), and the allocation
proportion converges to a positive limit `N_n/n → v > 0`, then the estimator error is
`|θ̂_n - θ| ≤ C'·(r n / n)` eventually, with `C' = (2/v)(C + |θ₀-θ|)`. Specializing to
`r n = √(n log n)` gives the `log` rate (`abs_estimator_sub_le_rate`); `r n = √(n log log n)` gives
the `log log` rate. -/
lemma abs_estimator_sub_le_rate_gen (ξ : ℕ → ℝ) (θ θ₀ : ℝ) {v : ℝ} (hv : 0 < v)
    (hN : Tendsto (fun n ↦ count X n / (n : ℝ)) atTop (𝓝 v)) {C : ℝ} (hC : 0 ≤ C)
    {r : ℕ → ℝ} (hr : ∀ᶠ n in atTop, 1 ≤ r n)
    (hQ : ∀ᶠ n in atTop, |respMG X ξ θ n| ≤ C * r n) :
    ∃ C', ∀ᶠ n in atTop,
      |estimator X ξ θ₀ n - θ| ≤ C' * (r n / (n : ℝ)) := by
  refine ⟨2 / v * (C + |θ₀ - θ|), ?_⟩
  have hNhalf : ∀ᶠ n : ℕ in atTop, v / 2 < count X n / (n : ℝ) :=
    (tendsto_order.1 hN).1 (v / 2) (by linarith)
  filter_upwards [hQ, hNhalf, hr, eventually_gt_atTop 0] with n hq hNh hrn hn0
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hvn : 0 < v / 2 * (n : ℝ) := mul_pos (by linarith) hnpos
  have hNlow : v / 2 * (n : ℝ) < count X n := (lt_div_iff₀ hnpos).1 hNh
  have hden : v / 2 * (n : ℝ) < count X n + 1 := by linarith
  have hdenpos : 0 < count X n + 1 := lt_trans hvn hden
  have hnum : |respMG X ξ θ n + (θ₀ - θ)| ≤ C * r n + |θ₀ - θ| :=
    (abs_add_le _ _).trans (add_le_add hq le_rfl)
  have hnumnn : 0 ≤ C * r n + |θ₀ - θ| :=
    add_nonneg (mul_nonneg hC (by linarith)) (abs_nonneg _)
  rw [estimator_sub_eq X ξ θ θ₀ n (ne_of_gt hdenpos), abs_div, abs_of_pos hdenpos]
  calc |respMG X ξ θ n + (θ₀ - θ)| / (count X n + 1)
      ≤ (C * r n + |θ₀ - θ|) / (v / 2 * (n : ℝ)) :=
        div_le_div₀ hnumnn hnum hvn hden.le
    _ ≤ 2 / v * (C + |θ₀ - θ|) * (r n / (n : ℝ)) := by
        rw [div_le_iff₀ hvn]
        have hexpand : 2 / v * (C + |θ₀ - θ|) * (r n / (n : ℝ)) * (v / 2 * (n : ℝ))
            = (C + |θ₀ - θ|) * r n := by
          field_simp
        rw [hexpand, add_mul]
        have hkey := mul_le_mul_of_nonneg_left hrn (abs_nonneg (θ₀ - θ))
        rw [mul_one] at hkey
        linarith

/-- **LIL rate for the estimator** (blueprint `lem:theta_LIL`, pathwise core).

If the response martingale is `O(√(n log n))` — `|Q_n| ≤ C√(n log n)` eventually, supplied a.s. by
`lem:lil_truncation` — and the allocation proportion converges to a positive limit `N_n/n → v > 0`
(supplied a.s. by `lem:match`), then the estimator error is
`|θ̂_n - θ| ≤ C' · √(n log n)/n` eventually, i.e. `O(√(log n / n))` (since `√(n log n)/n =
√(log n / n)`). This is the `√(\log n / n)` rate of `lem:theta_LIL` (the `\log`, not `\log\log`,
form). Combining the exact error `θ̂_n - θ = (Q_n + (θ₀-θ))/(N_n+1)` with `|Q_n| ≤ C√(n log n)` and
`N_n + 1 ≳ (v/2) n` gives the bound with `C' = (2/v)(C + |θ₀-θ|)`. A special case of
`abs_estimator_sub_le_rate_gen` with `r n = √(n log n)`. -/
lemma abs_estimator_sub_le_rate (ξ : ℕ → ℝ) (θ θ₀ : ℝ) {v : ℝ} (hv : 0 < v)
    (hN : Tendsto (fun n ↦ count X n / (n : ℝ)) atTop (𝓝 v)) {C : ℝ} (hC : 0 ≤ C)
    (hQ : ∀ᶠ n in atTop, |respMG X ξ θ n| ≤ C * √((n : ℝ) * Real.log n)) :
    ∃ C', ∀ᶠ n in atTop,
      |estimator X ξ θ₀ n - θ| ≤ C' * (√((n : ℝ) * Real.log n) / (n : ℝ)) := by
  refine abs_estimator_sub_le_rate_gen X ξ θ θ₀ hv hN hC ?_ hQ
  filter_upwards [eventually_ge_atTop 3] with n hn3
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn1 : (1 : ℝ) ≤ Real.log n :=
    (Real.le_log_iff_exp_le hnpos).mpr (le_trans Real.exp_one_lt_d9.le (by linarith))
  rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- **Deterministic core of the limit of `U/n`** (blueprint `lem:U_over_n`).

If the plug-in target converges, `ρ n → u`, and the normalized assignment martingale vanishes,
`M n / n → 0`, then `U n / n → -(1-α) u`. Since
`U n / n = α · (average of ρ over the first n-1 patients) + M n / n - ρ n`, and the average tends
to `u` by Cesàro convergence (`Filter.Tendsto.cesaro`), the limit is `α u + 0 - u = -(1-α) u`.
Applied pathwise (with the a.s. limits from `lem:M_lln` and `lem:rho_converges`), this yields the
almost-sure statement `lem:U_over_n`. -/
lemma auxU_div_tendsto (u : ℝ) (hρ : Tendsto ρ atTop (𝓝 u))
    (hM : Tendsto (fun n ↦ assignMG X p n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ auxU X p ρ α n / (n : ℝ)) atTop (𝓝 (-(1 - α) * u)) := by
  -- Cesàro average of `ρ` over `range n` tends to `u`.
  have hcesaro : Tendsto (fun n ↦ (∑ m ∈ range n, ρ m) / (n : ℝ)) atTop (𝓝 u) := by
    simpa [smul_eq_mul, div_eq_inv_mul] using hρ.cesaro
  -- Combine the three pieces.
  have hlim : Tendsto (fun n ↦ α * ((∑ m ∈ range n, ρ m) / (n : ℝ))
      + assignMG X p n / (n : ℝ) - ρ n) atTop (𝓝 (α * u + 0 - u)) :=
    ((hcesaro.const_mul α).add hM).sub hρ
  rw [show α * u + 0 - u = -(1 - α) * u by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold auxU
  rw [← Finset.mul_sum (range n) ρ α]
  field_simp

/-- **Positive part of the proportion gap vanishes** (blueprint `lem:pos_part_vanishes`).

Pathwise core, for a fixed arm with assignment indicators `X`, selection probabilities `p`, plug-in
target `ρ`, throttling parameter `α`, and last under-sampling times `ℓ` (with `ℓ n ≤ n`). Assume:
* the plug-in target converges, `ρ n → u` with `u ∈ [0,1]` (blueprint `lem:rho_converges`);
* the normalized assignment martingale vanishes, `M n / n → 0` (blueprint `lem:M_lln`);
* the generic key inequality `hgen` (blueprint `eq:generic_ineq`, supplied by `preliminary_ineq`);
* generic smallness `hgs`, the operational form of `limsup (N_ℓ - ℓ ρ_ℓ)/n ≤ 0` (blueprint
  `eq:generic_small`, supplied by `preliminary_small`).

Then `(N n / n - ρ n)⁺ → 0`. The argument feeds the auxiliary-process limit `U n / n → -(1-α) u`
(`auxU_div_tendsto`) into the analytic positive-part lemma `tendsto_posPart_sub_div`
(blueprint `lem:convergence`), then squeezes. -/
lemma pos_part_vanishes {ℓ : ℕ → ℕ} {u C : ℝ} (hℓle : ∀ n, ℓ n ≤ n)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hρ : Tendsto ρ atTop (𝓝 u))
    (hM : Tendsto (fun n ↦ assignMG X p n / (n : ℝ)) atTop (𝓝 0))
    (hgen : ∀ n, count X n - (n : ℝ) * ρ n
      ≤ C + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) + (auxU X p ρ α n - auxU X p ρ α (ℓ n)))
    (hgs : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ) < δ) :
    Tendsto (fun n ↦ max (count X n / (n : ℝ) - ρ n) 0) atTop (𝓝 0) := by
  have hU : Tendsto (fun n ↦ auxU X p ρ α n / (n : ℝ)) atTop (𝓝 (-((1 - α) * u))) := by
    have h := auxU_div_tendsto X p ρ α u hρ hM
    rwa [neg_mul] at h
  have hα' : (1 - α) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hCn : Tendsto (fun n : ℕ ↦ C / (n : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul C
    simp only [mul_one_div, mul_zero] at h
    exact h
  have hε : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      C / (n : ℝ) + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ) < δ := by
    intro δ hδ
    filter_upwards [hCn.eventually_lt_const (show (0 : ℝ) < δ / 2 by linarith),
      hgs (δ / 2) (by linarith)] with n ha hb
    linarith
  have key := tendsto_posPart_sub_div (a := ℓ) (X := auxU X p ρ α)
    (ε := fun n : ℕ ↦ C / (n : ℝ) + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ))
    hℓle hα' hu hU hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds key
    (Eventually.of_forall fun n ↦ le_max_right _ _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnum : 0 ≤ C + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n))
      + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) - (count X n - (n : ℝ) * ρ n) := by
    linarith [hgen n]
  have expand : (C / (n : ℝ) + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ)
        + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) / (n : ℝ)) - (count X n / (n : ℝ) - ρ n)
      = (C + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n))
        + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) - (count X n - (n : ℝ) * ρ n)) / (n : ℝ) := by
    field_simp
  have hnn : 0 ≤ (C + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n))
        + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) - (count X n - (n : ℝ) * ρ n)) / (n : ℝ) :=
    div_nonneg hnum hnR.le
  have key2 : count X n / (n : ℝ) - ρ n
      ≤ C / (n : ℝ) + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ)
        + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) / (n : ℝ) := by
    linarith [expand, hnn]
  exact max_le_max key2 le_rfl

/-- **Negative part of the proportion gap vanishes** (blueprint `lem:neg_part_vanishes`).

Vector form over `K` arms. If every arm's positive gap `(N_{·,j}/n - r_{·,j})⁺` vanishes
(`pos_part_vanishes`), and both the allocation proportions and the target `r` lie on the simplex
(`∑_j Y_· j = 1` per patient, so `∑_j N_{·,j}/n = 1`; and `∑_j r_n j = 1`), then for each arm the
negative gap `(r_{·,k} - N_{·,k}/n)⁺` also vanishes. Indeed
`r_k - N_k/n = ∑_{j≠k}(N_j/n - r_j)`, whose positive part is dominated by
`∑_{j≠k}(N_j/n - r_j)⁺ → 0`. -/
lemma neg_part_vanishes {ι : Type*} [Fintype ι] (Y r : ℕ → ι → ℝ)
    (hY : ∀ j, ∑ k, Y j k = 1) (hr : ∀ n, ∑ k, r n k = 1)
    (hpos : ∀ j : ι,
      Tendsto (fun n ↦ max (count (Y · j) n / (n : ℝ) - r n j) 0) atTop (𝓝 0))
    (k : ι) :
    Tendsto (fun n ↦ max (r n k - count (Y · k) n / (n : ℝ)) 0) atTop (𝓝 0) := by
  classical
  have hsum : Tendsto (fun n ↦ ∑ j ∈ Finset.univ.erase k,
      max (count (Y · j) n / (n : ℝ) - r n j) 0) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ.erase k) (fun j _ ↦ hpos j)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n ↦ le_max_right _ _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (∑ j, count (Y · j) n / (n : ℝ)) = 1 := by
    rw [← Finset.sum_div, counts_sum Y hY n, div_self (ne_of_gt hn0)]
  have htot : (∑ j, (count (Y · j) n / (n : ℝ) - r n j)) = 0 := by
    rw [Finset.sum_sub_distrib, h1, hr n, sub_self]
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j ↦ count (Y · j) n / (n : ℝ) - r n j) (Finset.mem_univ k)
  have hid2 : (∑ j ∈ Finset.univ.erase k, (count (Y · j) n / (n : ℝ) - r n j))
      = r n k - count (Y · k) n / (n : ℝ) := by
    have hz : (count (Y · k) n / (n : ℝ) - r n k)
        + ∑ j ∈ Finset.univ.erase k, (count (Y · j) n / (n : ℝ) - r n j) = 0 := by
      rw [hsplit]; exact htot
    linarith
  rw [← hid2]
  refine max_le (Finset.sum_le_sum fun j _ ↦ le_max_left _ _)
    (Finset.sum_nonneg fun j _ ↦ le_max_right _ _)

/-- **Proportions match the plug-in target** (blueprint `lem:match`).

Single-arm form. If both the positive gap `(N_k/n - r_k)⁺` and the negative gap `(r_k - N_k/n)⁺`
vanish (from `pos_part_vanishes`, `neg_part_vanishes`), and the target converges `r_k → u_k`, then
the allocation proportion converges to the same limit, `N_k/n → u_k`. The gap itself vanishes
because `x = x⁺ - (-x)⁺`, so `N_k/n - r_k = (N_k/n - r_k)⁺ - (r_k - N_k/n)⁺ → 0`. -/
lemma match_proportion {ι : Type*} (Y r : ℕ → ι → ℝ) {uk : ℝ} (k : ι)
    (hpos : Tendsto (fun n ↦ max (count (Y · k) n / (n : ℝ) - r n k) 0) atTop (𝓝 0))
    (hneg : Tendsto (fun n ↦ max (r n k - count (Y · k) n / (n : ℝ)) 0) atTop (𝓝 0))
    (hr : Tendsto (r · k) atTop (𝓝 uk)) :
    Tendsto (fun n ↦ count (Y · k) n / (n : ℝ)) atTop (𝓝 uk) := by
  have hid : ∀ x : ℝ, max x 0 - max (-x) 0 = x := by
    intro x
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -x ≤ 0), sub_zero]
    · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -x), zero_sub, neg_neg]
  have hdiff : Tendsto (fun n ↦ count (Y · k) n / (n : ℝ) - r n k) atTop (𝓝 0) := by
    have h := hpos.sub hneg
    rw [sub_zero] at h
    refine h.congr fun n ↦ ?_
    rw [show r n k - count (Y · k) n / (n : ℝ)
        = -(count (Y · k) n / (n : ℝ) - r n k) from by ring]
    exact hid _
  have hlim := hdiff.add hr
  rw [zero_add] at hlim
  refine hlim.congr fun n ↦ ?_
  ring

/-- **All arms are sampled infinitely often** (blueprint `lem:all_arms_infinite`).

If the allocation proportion converges to a positive limit, `N_k/n → u_k > 0` (from
`match_proportion`), then the count diverges, `N_k → ∞`. Writing `N_k = (N_k/n) · n`, the first
factor tends to `u_k > 0` and the second to `∞`. -/
lemma all_arms_infinite {ι : Type*} (Y : ℕ → ι → ℝ) {uk : ℝ} (k : ι) (huk : 0 < uk)
    (hmatch : Tendsto (fun n ↦ count (Y · k) n / (n : ℝ)) atTop (𝓝 uk)) :
    Tendsto (fun n ↦ count (Y · k) n) atTop atTop := by
  have hmul : Tendsto (fun n : ℕ ↦ count (Y · k) n / (n : ℝ) * (n : ℝ)) atTop atTop :=
    hmatch.pos_mul_atTop huk tendsto_natCast_atTop_atTop
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_mul_cancel₀ _ hne]

end AlphaRAR
