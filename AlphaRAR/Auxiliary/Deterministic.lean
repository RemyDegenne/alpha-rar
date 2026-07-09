/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib
import AlphaRAR.Technical.Convergence

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

open Finset Filter

open scoped Topology

namespace AlphaRAR

variable (X p ρ : ℕ → ℝ) (α : ℝ)

/-- Allocation count of a fixed arm, `N n = ∑_{j<n} X j` (blueprint `def:counts`). -/
def count (n : ℕ) : ℝ := ∑ j ∈ range n, X j

/-- Assignment martingale of a fixed arm, `M n = ∑_{j<n} (X j - p j)`
(blueprint `def:M`). -/
def assignMG (n : ℕ) : ℝ := ∑ j ∈ range n, (X j - p j)

/-- **Count decomposition** (blueprint `lem:count_decomp`).
`N n = ∑_{m<n} p m + M n`. -/
theorem count_eq (n : ℕ) : count X n = (∑ m ∈ range n, p m) + assignMG X p n := by
  simp only [count, assignMG, Finset.sum_sub_distrib]
  grind

/-- Increment of the count: `N (n+1) = N n + X n`. -/
theorem count_succ (n : ℕ) : count X (n + 1) = count X n + X n := by
  unfold count
  rw [Finset.sum_range_succ]

/-- Increment of the assignment martingale: `M (n+1) = M n + (X n - p n)`. -/
theorem assignMG_succ (n : ℕ) :
    assignMG X p (n + 1) = assignMG X p n + (X n - p n) := by
  unfold assignMG
  rw [Finset.sum_range_succ]

/-- Auxiliary process `U n = ∑_{m<n-1} α ρ m + M n - n ρ n` (blueprint `def:U`). The
`α ρ` sum has one fewer term than `M`, so it runs over `range (n-1)`. -/
def auxU (n : ℕ) : ℝ := (∑ m ∈ range (n - 1), α * ρ m) + assignMG X p n - (n : ℝ) * ρ n

/-- Increment of the leading `α ρ` sum, for `n ≥ 1`. -/
theorem alphaSum_succ (n : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ range n, α * ρ m) = (∑ m ∈ range (n - 1), α * ρ m) + α * ρ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Finset.sum_range_succ]

/-- **Increment of the auxiliary process** (blueprint `lem:U_increment`).

For `n ≥ 1`, writing `D n := N n - n ρ n`,
`U (n+1) - U n = α ρ_{n-1} - p n + (D (n+1) - D n)`.
(The leading term `α ρ_{n-1}` requires `n ≥ 1`, since at `n = 0` the `α ρ`-sum
does not yet grow.) -/
theorem auxU_succ_sub (n : ℕ) (hn : 1 ≤ n) :
    auxU X p ρ α (n + 1) - auxU X p ρ α n
      = α * ρ (n - 1) - p n
        + (((count X (n + 1) - (n + 1 : ℝ) * ρ (n + 1)) - (count X n - (n : ℝ) * ρ n))) := by
  unfold auxU
  simp only [Nat.add_sub_cancel]
  rw [assignMG_succ, alphaSum_succ ρ α n hn, count_succ]
  push_cast
  grind

/-- A telescoping identity for a real sequence over `Ico ℓ n`. -/
theorem sum_Ico_succ_sub (f : ℕ → ℝ) (ℓ : ℕ) :
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

For `1 ≤ ℓ ≤ n`, writing `D m := N m - m ρ m`,
`U n - U ℓ = ∑_{m=ℓ}^{n-1} (α ρ_{m-1} - p m) + (D n - D ℓ)`.
Rearranged, this is the blueprint's identity expressing `D n` in terms of `D ℓ`,
the summed throttling terms, and the increment of `U`. -/
theorem auxU_telescope (n ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) :
    auxU X p ρ α n - auxU X p ρ α ℓ
      = (∑ m ∈ Ico ℓ n, (α * ρ (m - 1) - p m))
        + ((count X n - (n : ℝ) * ρ n) - (count X ℓ - (ℓ : ℝ) * ρ ℓ)) := by
  have hterm : ∀ m ∈ Ico ℓ n,
      auxU X p ρ α (m + 1) - auxU X p ρ α m
        = (α * ρ (m - 1) - p m)
          + ((count X (m + 1) - ((m + 1 : ℕ) : ℝ) * ρ (m + 1))
            - (count X m - (m : ℝ) * ρ m)) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have h := auxU_succ_sub X p ρ α m (by omega)
    push_cast at h ⊢
    exact h
  rw [← sum_Ico_succ_sub (auxU X p ρ α) ℓ n hℓn, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib]
  congr 1
  exact sum_Ico_succ_sub (fun m => count X m - (m : ℝ) * ρ m) ℓ n hℓn

/-- **Counts sum to time** (blueprint `lem:counts_sum`).
If the assignment vector sums to one at each time, then the arm counts sum to the
time index. -/
theorem counts_sum {K : ℕ} (Y : ℕ → Fin K → ℝ) (hY : ∀ j, ∑ k, Y j k = 1) (n : ℕ) :
    (∑ k, count (fun j => Y j k) n) = n := by
  simp only [count]
  rw [Finset.sum_comm]
  simp only [hY, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

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

Whenever the throttling condition `p m ≤ α ρ_{m-1}` holds for all `ℓ+1 ≤ m ≤ n-1`,
`p ℓ ≤ 1`, and `0 ≤ α ρ_{ℓ-1}`, the gap `D n = N n - n ρ n` is controlled by its
value at `ℓ` plus the increment of `U`:
`D n ≤ 1 + D ℓ + (U n - U ℓ)`. -/
theorem preliminary_ineq (n ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (hp1 : p ℓ ≤ 1) (hαρ : 0 ≤ α * ρ (ℓ - 1))
    (hthrottle : ∀ m ∈ Ico (ℓ + 1) n, p m ≤ α * ρ (m - 1)) :
    (count X n - (n : ℝ) * ρ n)
      ≤ 1 + (count X ℓ - (ℓ : ℝ) * ρ ℓ) + (auxU X p ρ α n - auxU X p ρ α ℓ) := by
  rcases hℓn.lt_or_eq with hlt | heq
  · -- `ℓ < n`: split off the first term of the telescoped sum.
    have htel := auxU_telescope X p ρ α n ℓ hℓ hℓn
    set T := ∑ m ∈ Ico ℓ n, (α * ρ (m - 1) - p m) with hT
    have hTge : -1 ≤ T := by
      have hmemL : ℓ ∈ Ico ℓ n := Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩
      have hsplit := Finset.add_sum_erase (Ico ℓ n) (fun m => α * ρ (m - 1) - p m) hmemL
      have hrest : 0 ≤ ∑ m ∈ (Ico ℓ n).erase ℓ, (α * ρ (m - 1) - p m) := by
        apply Finset.sum_nonneg
        intro m hm
        rw [Finset.mem_erase, Finset.mem_Ico] at hm
        have := hthrottle m (Finset.mem_Ico.mpr ⟨by omega, hm.2.2⟩)
        linarith
      have hval : T = (α * ρ (ℓ - 1) - p ℓ)
          + ∑ m ∈ (Ico ℓ n).erase ℓ, (α * ρ (m - 1) - p m) := by
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
`Q n = ∑_{j<n} X j (ξ j - θ)` (blueprint `def:Q`). -/
def respMG (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, X j * (ξ j - θ)

/-- `Q n = ∑ X ξ - θ N n`: the response martingale rewritten via the count. -/
theorem respMG_eq (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    respMG X ξ θ n = (∑ j ∈ range n, X j * ξ j) - θ * count X n := by
  unfold respMG count
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Estimator error via `Q`** (blueprint `lem:theta_error_Q`).

On `{N n ≠ 0}`, the leading term of the estimator error equals `Q n / N n`:
`(∑ X ξ) / N n - θ = Q n / N n`. -/
theorem theta_error_Q (ξ : ℕ → ℝ) (θ : ℝ) (n : ℕ) (hN : count X n ≠ 0) :
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
theorem estimator_sub_eq (ξ : ℕ → ℝ) (θ θ₀ : ℝ) (n : ℕ) (hN : count X n + 1 ≠ 0) :
    estimator X ξ θ₀ n - θ = (respMG X ξ θ n + (θ₀ - θ)) / (count X n + 1) := by
  rw [estimator, respMG_eq]
  field_simp
  ring

/-- **Absolute estimator error bound**: `|θ̂ n - θ| ≤ (|Q n| + |θ₀ - θ|) / (N n + 1)`.
The pathwise backbone of the LIL rate `lem:theta_LIL`: with `|Q n| = O(√(n \log n))` and
`N n + 1 ≍ v_k n`, it gives `|θ̂ n - θ| = O(√(\log n / n))`. -/
theorem abs_estimator_sub_le (ξ : ℕ → ℝ) (θ θ₀ : ℝ) (n : ℕ) (hN : 0 < count X n + 1) :
    |estimator X ξ θ₀ n - θ| ≤ (|respMG X ξ θ n| + |θ₀ - θ|) / (count X n + 1) := by
  rw [estimator_sub_eq X ξ θ θ₀ n (ne_of_gt hN), abs_div, abs_of_pos hN]
  gcongr
  exact abs_add_le _ _

/-- **Deterministic core of the limit of `U/n`** (blueprint `lem:U_over_n`).

If the plug-in target converges, `ρ n → u`, and the normalized assignment martingale vanishes,
`M n / n → 0`, then `U n / n → -(1-α) u`. Since
`U n / n = α · (average of ρ over the first n-1 patients) + M n / n - ρ n`, and the average tends
to `u` by Cesàro convergence (`Filter.Tendsto.cesaro`), the limit is `α u + 0 - u = -(1-α) u`.
Applied pathwise (with the a.s. limits from `lem:M_lln` and `lem:rho_converges`), this yields the
almost-sure statement `lem:U_over_n`. -/
theorem auxU_div_tendsto (u : ℝ) (hρ : Tendsto ρ atTop (𝓝 u))
    (hM : Tendsto (fun n => assignMG X p n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => auxU X p ρ α n / (n : ℝ)) atTop (𝓝 (-(1 - α) * u)) := by
  -- `(n)⁻¹ → 0`, and the once-shifted sequence `ρ (n-1) → u`.
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hpred : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun n hn => by omega⟩
  have hρpred : Tendsto (fun n => ρ (n - 1)) atTop (𝓝 u) := hρ.comp hpred
  -- Cesàro average of `ρ` over `range n` tends to `u`.
  have hcesaro : Tendsto (fun n => (∑ m ∈ range n, ρ m) / (n : ℝ)) atTop (𝓝 u) := by
    simpa [smul_eq_mul, div_eq_inv_mul] using hρ.cesaro
  -- `ρ (n-1) / n → 0`.
  have hshift0 : Tendsto (fun n => ρ (n - 1) / (n : ℝ)) atTop (𝓝 0) := by
    have h := hρpred.mul hinv
    simpa [div_eq_mul_inv] using h
  -- The average over `range (n-1)` also tends to `u` (it differs by the vanishing `ρ (n-1)/n`).
  have hshort : Tendsto (fun n => (∑ m ∈ range (n - 1), ρ m) / (n : ℝ)) atTop (𝓝 u) := by
    have hsub := hcesaro.sub hshift0
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sum_range_succ]
    ring
  -- Combine the three pieces.
  have hlim : Tendsto (fun n => α * ((∑ m ∈ range (n - 1), ρ m) / (n : ℝ))
      + assignMG X p n / (n : ℝ) - ρ n) atTop (𝓝 (α * u + 0 - u)) :=
    ((hshort.const_mul α).add hM).sub hρ
  rw [show α * u + 0 - u = -(1 - α) * u by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold auxU
  rw [← Finset.mul_sum (range (n - 1)) ρ α]
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
theorem pos_part_vanishes {ℓ : ℕ → ℕ} {u : ℝ} (hℓle : ∀ n, ℓ n ≤ n)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hρ : Tendsto ρ atTop (𝓝 u))
    (hM : Tendsto (fun n => assignMG X p n / (n : ℝ)) atTop (𝓝 0))
    (hgen : ∀ n, count X n - (n : ℝ) * ρ n
      ≤ 1 + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) + (auxU X p ρ α n - auxU X p ρ α (ℓ n)))
    (hgs : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ) < δ) :
    Tendsto (fun n => max (count X n / (n : ℝ) - ρ n) 0) atTop (𝓝 0) := by
  have hU : Tendsto (fun n => auxU X p ρ α n / (n : ℝ)) atTop (𝓝 (-((1 - α) * u))) := by
    have h := auxU_div_tendsto X p ρ α u hρ hM
    rwa [neg_mul] at h
  have hα' : (1 - α) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hε : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / (n : ℝ) + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ) < δ := by
    intro δ hδ
    have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n : ℝ) < δ / 2 :=
      tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (by linarith)
    filter_upwards [h1, hgs (δ / 2) (by linarith)] with n ha hb
    linarith
  have key := tendsto_posPart_sub_div (a := ℓ) (X := auxU X p ρ α)
    (ε := fun n : ℕ => (1 : ℝ) / (n : ℝ) + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ))
    hℓle hα' hu hU hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds key
    (Eventually.of_forall fun n => le_max_right _ _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnum : 0 ≤ 1 + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n))
      + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) - (count X n - (n : ℝ) * ρ n) := by
    linarith [hgen n]
  have expand : ((1 : ℝ) / (n : ℝ) + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ)
        + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) / (n : ℝ)) - (count X n / (n : ℝ) - ρ n)
      = (1 + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n))
        + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) - (count X n - (n : ℝ) * ρ n)) / (n : ℝ) := by
    field_simp
  have hnn : 0 ≤ (1 + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n))
        + (auxU X p ρ α n - auxU X p ρ α (ℓ n)) - (count X n - (n : ℝ) * ρ n)) / (n : ℝ) :=
    div_nonneg hnum hnR.le
  have key2 : count X n / (n : ℝ) - ρ n
      ≤ (1 : ℝ) / (n : ℝ) + (count X (ℓ n) - (ℓ n : ℝ) * ρ (ℓ n)) / (n : ℝ)
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
theorem neg_part_vanishes {K : ℕ} (Y r : ℕ → Fin K → ℝ)
    (hY : ∀ j, ∑ k, Y j k = 1) (hr : ∀ n, ∑ k, r n k = 1)
    (hpos : ∀ j : Fin K,
      Tendsto (fun n => max (count (fun i => Y i j) n / (n : ℝ) - r n j) 0) atTop (𝓝 0))
    (k : Fin K) :
    Tendsto (fun n => max (r n k - count (fun i => Y i k) n / (n : ℝ)) 0) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => ∑ j ∈ Finset.univ.erase k,
      max (count (fun i => Y i j) n / (n : ℝ) - r n j) 0) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ.erase k) (fun j _ => hpos j)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => le_max_right _ _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (∑ j, count (fun i => Y i j) n / (n : ℝ)) = 1 := by
    rw [← Finset.sum_div, counts_sum Y hY n, div_self (ne_of_gt hn0)]
  have htot : (∑ j, (count (fun i => Y i j) n / (n : ℝ) - r n j)) = 0 := by
    rw [Finset.sum_sub_distrib, h1, hr n, sub_self]
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j => count (fun i => Y i j) n / (n : ℝ) - r n j) (Finset.mem_univ k)
  have hid2 : (∑ j ∈ Finset.univ.erase k, (count (fun i => Y i j) n / (n : ℝ) - r n j))
      = r n k - count (fun i => Y i k) n / (n : ℝ) := by
    have hz : (count (fun i => Y i k) n / (n : ℝ) - r n k)
        + ∑ j ∈ Finset.univ.erase k, (count (fun i => Y i j) n / (n : ℝ) - r n j) = 0 := by
      rw [hsplit]; exact htot
    linarith
  rw [← hid2]
  refine max_le (Finset.sum_le_sum fun j _ => le_max_left _ _)
    (Finset.sum_nonneg fun j _ => le_max_right _ _)

/-- **Proportions match the plug-in target** (blueprint `lem:match`).

Single-arm form. If both the positive gap `(N_k/n - r_k)⁺` and the negative gap `(r_k - N_k/n)⁺`
vanish (from `pos_part_vanishes`, `neg_part_vanishes`), and the target converges `r_k → u_k`, then
the allocation proportion converges to the same limit, `N_k/n → u_k`. The gap itself vanishes
because `x = x⁺ - (-x)⁺`, so `N_k/n - r_k = (N_k/n - r_k)⁺ - (r_k - N_k/n)⁺ → 0`. -/
theorem match_proportion {K : ℕ} (Y r : ℕ → Fin K → ℝ) {uk : ℝ} (k : Fin K)
    (hpos : Tendsto (fun n => max (count (fun i => Y i k) n / (n : ℝ) - r n k) 0) atTop (𝓝 0))
    (hneg : Tendsto (fun n => max (r n k - count (fun i => Y i k) n / (n : ℝ)) 0) atTop (𝓝 0))
    (hr : Tendsto (fun n => r n k) atTop (𝓝 uk)) :
    Tendsto (fun n => count (fun i => Y i k) n / (n : ℝ)) atTop (𝓝 uk) := by
  have hid : ∀ x : ℝ, max x 0 - max (-x) 0 = x := by
    intro x
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -x ≤ 0), sub_zero]
    · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -x), zero_sub, neg_neg]
  have hdiff : Tendsto (fun n => count (fun i => Y i k) n / (n : ℝ) - r n k) atTop (𝓝 0) := by
    have h := hpos.sub hneg
    rw [sub_zero] at h
    refine h.congr fun n => ?_
    rw [show r n k - count (fun i => Y i k) n / (n : ℝ)
        = -(count (fun i => Y i k) n / (n : ℝ) - r n k) from by ring]
    exact hid _
  have hlim := hdiff.add hr
  rw [zero_add] at hlim
  refine hlim.congr fun n => ?_
  ring

/-- **All arms are sampled infinitely often** (blueprint `lem:all_arms_infinite`).

If the allocation proportion converges to a positive limit, `N_k/n → u_k > 0` (from
`match_proportion`), then the count diverges, `N_k → ∞`. Writing `N_k = (N_k/n) · n`, the first
factor tends to `u_k > 0` and the second to `∞`. -/
theorem all_arms_infinite {K : ℕ} (Y : ℕ → Fin K → ℝ) {uk : ℝ} (k : Fin K) (huk : 0 < uk)
    (hmatch : Tendsto (fun n => count (fun i => Y i k) n / (n : ℝ)) atTop (𝓝 uk)) :
    Tendsto (fun n => count (fun i => Y i k) n) atTop atTop := by
  have hmul : Tendsto (fun n : ℕ => count (fun i => Y i k) n / (n : ℝ) * (n : ℝ)) atTop atTop :=
    hmatch.pos_mul_atTop huk tendsto_natCast_atTop_atTop
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_mul_cancel₀ _ hne]

end AlphaRAR
