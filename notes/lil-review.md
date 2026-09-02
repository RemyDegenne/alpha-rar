# Review of the LIL files: what is reusable theory, and what would Mathlib want

Date: 2026-09-02 (rewritten the same day with a different yardstick). Files reviewed:
`AlphaRAR/Mathlib/LIL.lean`, `LILLogLog.lean`, `LILTruncation.lean`, `LILSharp.lean`,
`LILHartmanWintner.lean`, plus the new `LILCommon.lean` (Stage 1 below). Usage was checked
repo-wide with comments stripped, and every piece was compared against what Mathlib (rev
`17dadc59`, Lean `v4.34.0-rc2`) already provides.

**Yardstick.** The goal is not to prove the paper's results as cheaply as possible but to end up
with a body of theory that Mathlib would accept and other projects would reuse. The blueprint is
an auxiliary working document and imposes no constraint: a lemma is kept because it is the right
general statement, not because a `\lean` tag points at it. The repository's own consumers are the
only hard requirement, and they are few:

| Consumer | What it uses |
|---|---|
| `YDK2026/AssignmentRate.lean` | `ae_eventually_abs_le_sqrt_nat_mul_loglog_of_bdd` (bounded increments, unconditional) |
| `YDK2026/ResponseTruncation.lean` | the `√i`-increment log-rate chain of `LILTruncation.lean` |
| `YDK2026/ResponseLIL.lean` | `hw_eventually` (Hartman–Wintner, eventual form) |
| `Mathlib/AnscombeCLT.lean` | `natFiltLT`, `martingale_iidSum` |

Everything else in the five files is free to be reshaped.

**Summary.** The mathematics here is genuinely absent from Mathlib: Ville's inequality, the
predictable quadratic variation as a named object, the exponential supermartingale with
predictable variance, Freedman's inequality, any law of the iterated logarithm, and Kolmogorov's
medium-band estimate. That is a real contribution. The way it is written, however, is a repository
development, not a library: the same argument is instantiated five times with slightly different
parameters, the general (refined, base-ρ, horizon-`N_j`) versions coexist with their own
specializations, rates are stated as `∃ C, ∀ᶠ n, …` instead of `IsBigO`, deterministic stopping is
hand-rolled instead of using `stoppedProcess`, and repo-only tooling (`@[specifies]`,
`@[characterization]`, the `tendsto` tactic) is woven in. Section 3 lists what to change; Section 4
orders the work. Section 5 lists what is upstreamable as is.

---

## 1. What Mathlib has, and what it does not

Checked directly in the vendored Mathlib.

**Has.**
- Doob decomposition: `MeasureTheory.predictablePart`, `martingalePart` (`Martingale/Centering`).
  The project's `predQuadVar M ℱ μ` is `predictablePart (M ·^2) ℱ μ`, so the object exists; the API
  around it (increment formula, monotonicity, `⟨-M⟩ = ⟨M⟩`, linear bound from bounded increments,
  Itô isometry `∫ M_n² = ∫ ⟨M⟩_n`) does not.
- Stopping: `stoppedProcess`, `stoppedValue` with `WithTop`-valued stopping times,
  `Submartingale.stoppedProcess`, optional stopping (`expected_stoppedValue_mono`), `hittingBtwn`.
- Doob's maximal inequality for nonnegative *sub*martingales (`maximal_ineq`). Not Ville's
  inequality for nonnegative *super*martingales; `smul_measure_sup_le_integral_zero` fills that gap.
- Borel–Cantelli `ae_eventually_notMem` (`OuterMeasure/BorelCantelli`).
- Sub-Gaussian theory with conditional variants and Azuma–Hoeffding
  (`Probability/Moments/SubGaussian.lean`, `HasCondSubgaussianMGF`,
  `measure_sum_ge_le_of_HasCondSubgaussianMGF`). The variance proxies there are deterministic
  constants per increment; Freedman's inequality, with the random `⟨M⟩`, is not covered.
- `truncation` and its integrability API (`Probability/StrongLaw`), `Filtration.natural`, the SLLN.
- `Real.exp_bound`, `Real.abs_exp_sub_one_sub_id_le` (the crude one-step inequality).

**Does not have.** Ville's inequality; a predictable-quadratic-variation API; the exponential
supermartingale `exp(θM − ½(1+δ)θ²⟨M⟩)`; Freedman's inequality; a martingale LIL of any kind;
Hartman–Wintner; Kolmogorov's medium-band variance lemma; partial sums of independent centred
variables as a martingale (nor the strict-past filtration `natFiltLT`).

## 2. The reusable core, layer by layer

What follows is the shape a library version should have, and how the current files compare.

### L0. Analysis lemmas and Ville's inequality

Small, independent, and Mathlib-ready with light renaming: `smul_measure_sup_le_integral_zero`
(Ville), `exp_le_one_add_add_half_mul_sq` (state the witness `η = min 1 (9δ/4)` explicitly, so the
crude `η = 1` inequality is its `δ = 1` case), `sum_one_div_sqrt_le`, `summable_exp_neg_mul_sqrt`
and `summable_exp_neg_mul_sqrt_add`, `summable_exp_neg_mul_log_add` (a `p`-series), the
`log`/`log log` facts (`div_log_add_two_lt`, `one_lt_log_three`, `loglog_pos_of_three_le`,
`loglog_le_loglog`), `tendsto_add_two_div_pow`, `tendsto_log_add_two_div_pow`, `exists_pow_ge_le`,
`log_add_two_le_add_loglog`, and the truncation lemmas `abs_truncation_sub_le`,
`abs_integral_truncation_le`, `integral_sq_truncation_le`, `abs_truncation_sub_integral_le`,
`integral_truncation_sub_integral_sq_le`.

**Codomain of Ville's inequality (checked 2026-09-02).** Both forms are real-valued, like Mathlib's
`maximal_ineq`, although `Supermartingale` and `expected_stoppedValue_mono` are general for ordered
Banach spaces. A version for an ordered Banach lattice `E` (`μ.real s • ε ≤ ∫ Z 0` in `E`) is
feasible with the existing general `setIntegral_ge_of_const_le`, `setIntegral_le_integral` and
codomain-generic `hittingBtwn`, but needs a long typeclass list and has no application. An
`ℝ≥0∞`-valued version is out of reach: Mathlib has no conditional expectation, hence no
supermartingale notion, for `ℝ≥0∞`-valued processes; that would be a separate foundational project.
Nonnegative real processes already cover `ℝ≥0`-valued ones and a.e.-finite `ℝ≥0∞` ones via `toReal`.

### L1. Quadratic variation, exponential supermartingale, Freedman

The library statement is the refined one and only it: for a martingale with `|ΔM_i| ≤ c` and
`|θ| c ≤ η`, where `eˣ ≤ 1 + x + ½(1+δ)x²` on `|x| ≤ η`,

* `μ[exp(θ ΔM_i) | ℱ_i] ≤ 1 + ½(1+δ)θ² Δ⟨M⟩_i` (`condExp_exp_increment_le`);
* `exp(θ M_n − ½(1+δ)θ²⟨M⟩_n)` is a supermartingale (`supermartingale_expProcess`);
* `μ{∃ k ≤ n, λ ≤ M_k ∧ ⟨M⟩_k ≤ v} ≤ exp(−θλ + ½(1+δ)θ²v)` (`measure_exists_ge_le_exp`),
  its optimized form `exp(−λ²/(2(1+δ)v))`, its `n → ∞` form, and its horizon-local form.

The crude versions (`condExp_exp_increment_le`, `expProcess`, `supermartingale_expProcess`,
`measure_exists_ge_le_exp`, `_optimized`, `_all`, `_horizon`) are the `δ = 1, η = 1` instances and
should not exist as separate theorems in a library. `measure_exists_ge_le_exp` already is a
three-line instance; the others are re-proved from scratch and, worse, the horizon-local one at
`LIL.lean:530` and its refined twin at `LILSharp.lean:429` are byte-identical apart from the inner
call. The refined family belongs in `LIL.lean` next to the supermartingale, not in `LILSharp.lean`.

Two design points for upstream:

* **Deterministic stopping.** `stopMart M N m = M (min m N)` re-implements
  `stoppedProcess M (fun _ ↦ (N : WithTop ℕ))`. Mathlib's `Submartingale.stoppedProcess` (applied to
  `M` and `-M`) gives `martingale_stopMart`, and `predQuadVar_stopMart_of_le` becomes a lemma about
  `predictablePart` of a stopped process. Using the Mathlib object is what a reviewer will ask for.
* **Hypothesis packaging.** The one-step MGF bound is exactly a "conditionally sub-gamma
  increment with predictable variance `Δ⟨M⟩_i`". Mathlib's `HasCondSubgaussianMGF` is the
  deterministic-variance analogue. A structure of the same style (say
  `HasCondBernsteinMGF M ℱ δ η`) would let the supermartingale, Freedman and the LIL be stated
  once for any martingale satisfying it, with bounded increments as one instance and the
  truncated i.i.d. increments as another. This is the most valuable generalization on offer and
  costs little, since the proofs already go through the abstract `hη` hypothesis.

### L2. Block Borel–Cantelli and the least-block lemma

Now in `LILCommon.lean` (Stage 1). `ae_eventually_notMem_of_eventually_le` is a natural companion
to Mathlib's `ae_eventually_notMem`; `exists_pow_ge_le` and `log_add_two_le_add_loglog` are plain
real analysis. All Mathlib-ready.

### L3. The martingale LIL: one block engine, two repackagings

Today there are six chains of the same block argument:

| Chain | Increments | Exponent | Blocks | Conclusion | Live consumer |
|---|---|---|---|---|---|
| A (`LIL.lean`) | bounded | crude | `2^k` on `⟨M⟩` | `M_n = O(√(⟨M⟩ log⟨M⟩))` | none |
| B (`LILLogLog`) | bounded | crude | `2^k` on `⟨M⟩` | `O(√(⟨M⟩ loglog⟨M⟩))` | none |
| C (`LILLogLog`) | horizon-local `c_j` | crude | `2^j` on time | `O(√(n loglog n))` | `_of_bdd` → `AssignmentRate` |
| D (`LILSharp`) | bounded | refined | `ρ^k` on `⟨M⟩` | `limsup ≤ 1`, normalized by `⟨M⟩` | none |
| E (`LILSharp`) | horizon-local `c_j`, `c_j √(log(j+2)/N_j) → 0` | refined | `⌈ρ^j⌉` on time | `limsup ≤ 1`, normalized by `v n` | Hartman–Wintner low part |
| F (`LILTruncation`) | `a√i` | crude | `2^j` on time | `O(√(n log n))` | `ResponseTruncation` |

From a library standpoint:

* **A, B, C are not theorems anyone wants.** Their conclusions are `∃ C` corollaries of D and E
  (`∀ b > 1` gives `∃ C` in three lines; `log(k+2) ≤ k+1` gives A from B). C's one nominal
  advantage, a merely bounded rather than vanishing block quantity, is used by no consumer:
  `_of_bdd` has constant `c_j`, so it is E with `g ≡ c`, `v = c²`. Delete all three; keep
  `_of_bdd` as a corollary of E.
* **D and E are two genuinely different theorems**, and both are worth having: D normalizes by the
  random `⟨M⟩_n` (and needs `⟨M⟩_n → ∞`), E normalizes by the deterministic `v n` (and needs
  only `⟨M⟩_n ≤ v n`). Neither implies the other: E's hypotheses give no lower bound on `⟨M⟩`, so
  Stout-type conditions cannot be verified from them. What they should share is *all* of the
  engine: the per-block Freedman bound and the block Borel–Cantelli step, parameterized by the
  horizon sequence `N_j` (or the level sequence `v_j`), the threshold `λ_j`, the parameter `θ_j`
  and the increment bound `c_j`. E's `ae_eventually_lt_block_of_growing_loglog_sharp` is already
  that general in `N_j` and `c_j`; F's `ae_eventually_lt_block_of_growing` is the same lemma with
  `λ_j = C√(2^j j)` and `θ_j = 1/c_j`. One block lemma with an explicit `θ_j` and a hypothesis
  "the resulting exponents are summable" subsumes both, and F becomes an instance plus its own
  (log-scale) repackaging. F itself is not a library theorem (it is what the `√i` truncation of
  the response martingale happens to need) but as an instance of the general block lemma it costs
  nothing to keep.
* **The library-grade generalization of D is Stout's LIL** (1970): for
  `|ΔM_n| ≤ K_n √(⟨M⟩_n / loglog⟨M⟩_n)` with `K_n → 0`, `limsup M_n/√(2⟨M⟩_n loglog⟨M⟩_n) ≤ 1`
  a.s. on `{⟨M⟩_∞ = ∞}`. Its proof stops at the predictable times
  `τ_k = inf{n : ⟨M⟩_{n+1} > ρ^k}` (stopping times because `⟨M⟩` is predictable) and applies the
  refined Freedman bound to `stoppedProcess M τ_k`; this is the "quadratic-variation stopping"
  route the paper's appendix sketches and that was never formalized. It subsumes D and gives the
  Hartman–Wintner low part directly (there `⟨S̃⟩_n ~ σ² n` from `predQuadVar_iidSum_ge`, so
  Stout's condition reads `√(loglog n / log n) → 0`). This is new work, on the order of the
  existing `LILSharp.lean`, and it is what I would aim at for Mathlib; E stays as the
  deterministic-normalization companion.
* **State rates as `IsBigO`.** `∃ C, ∀ᶠ n in atTop, |M n ω| ≤ C * w n` is
  `(fun n ↦ M n ω) =O[atTop] w`, and `Tendsto (f / w) (𝓝 0)` is `f =o[atTop] w`. Using
  `Asymptotics.IsBigO`/`IsLittleO` is the Mathlib idiom, it makes the six two-sided `-M`
  wrappers disappear (`IsBigO` is about norms), and it composes with the existing calculus of
  `IsBigO`. Keep `limsup … ≤ 1` for the sharp constant, with `∀ b > 1, ∀ᶠ n, …` as the
  intermediate form.

### L4. Hartman–Wintner

`LILHartmanWintner.lean` is the most reusable file and the closest to library shape: the
three-level decomposition, `martingale_iidSum` with `predQuadVar_iidSum_le`/`_ge`, the sharp low
part from E, Kolmogorov's medium-band lemma (`medium_variance_summable`, the analytic heart), the
medium SLLN via `martingale_div_weight_ae_tendsto_zero`, the drift bound with the boundary-atom
trick, and `iid_hartmanWintner_limsup_le_one`. Points for upstream:

* Mathlib would want the full theorem, `limsup = 1` and `liminf = −1`; the lower half needs the
  second Borel–Cantelli lemma (independence) and a lower tail estimate, and is not started.
* `natFiltLT` (strict past `σ(Y_0,…,Y_{n−1})`) versus Mathlib's `Filtration.natural`
  (`σ(Y_0,…,Y_n)`): either add `natFiltLT` to Mathlib as "the natural filtration of the past", or
  state `martingale_iidSum` for `Filtration.natural` with the sum `∑_{j ≤ n}`. The
  `IsNatFiltLT` characterization bundle is repo tooling and would be stripped.
* `ae_eventually_abs_sum_le_sqrt_nat_mul_loglog_of_bounded` (bounded i.i.d. case) is a corollary
  of D and of the main theorem; drop. `predQuadVar_iidSum_ge`, its only user today, is the
  quadratic-variation lower bound that Stout's route needs; keep.

## 3. What to change in the current code

Beyond the chain surgery of L3, these are the recurring library-readiness issues.

- **Specializations kept next to their generalization.** The crude Freedman/Borel–Cantelli
  family (L1), chains A/B/C, `measure_exists_ge_le_exp_block_loglog` (= `_sharp` at `N_j = 2^j`,
  `δ = 1`), `summable_block_bound` (= `summable_exp_neg_mul_sqrt_add`), `div_log_add_two_le`
  (= `div_log_add_two_lt`), `exp_le_one_add_add_sq` once the witness is explicit. Each is a
  one-call instance of a lemma that sits a few hundred lines away.
- **Hand-rolled Mathlib objects.** `stopMart` (use `stoppedProcess`); the `∃ C` rate forms (use
  `IsBigO`); `M 0 =ᵐ[μ] 0` plus `∀ n, MemLp (M n) 2 μ` as hypotheses where the latter follows
  from bounded increments (derive it, as `_of_bdd` already does).
- **Repo-only tooling in library files.** `@[specifies]` and `@[characterization]` attributes,
  the `Characterization` import, and the custom `tendsto` tactic (`AlphaRAR.Mathlib.Tactic.Tendsto`,
  three uses in `LILSharp.lean`). Upstream files cannot depend on any of these; the tactic uses
  are one-line `Tendsto` lemma applications.
- **Naming.** Mathlib will not accept `_sharp'`, `_sharp_all`, `hw_`, `hloglogpos`, or `lam` for
  `λ`. Use dot-notation on `Martingale` (`Martingale.ae_limsup_div_sqrt_predQuadVar_loglog_le_one`
  or similar), one name per statement, and the same hypothesis name for the same hypothesis
  (`hb`, `hbd`, `hinc`, `hginc` all mean the increment bound today).
- **Generality of typeclasses.** Ville and Freedman only need `IsFiniteMeasure`; check which LIL
  statements really need `IsProbabilityMeasure`.
- **File layout for upstream.** `Ville.lean` (or a section of `OptionalStopping`),
  `QuadraticVariation.lean` (exists), `ExponentialSupermartingale.lean` (refined engine +
  Freedman, horizon via `stoppedProcess`), `BlockLIL.lean` (block engine, least-block lemma),
  `LIL.lean` (D, E, later Stout, with `IsBigO` corollaries), `HartmanWintner.lean`; the analysis
  lemmas of L0 grouped by where they would go in `Mathlib/Analysis`.
- **Docstrings.** Several describe the repository's history ("in progress", "the crude engine
  above", "successive refinements") rather than the theorem; a library docstring states the
  result and its hypotheses.

## 4. Order of work

1. **Stage 1 (done).** Shared helpers in `LILCommon.lean`, all duplicated proof blocks route
   through them; no declaration touched. Details in the status section below.
2. **One engine (done, see status below).** Move the refined Freedman/horizon/Borel–Cantelli lemmas into `LIL.lean`, switch
   the crude call sites (F's block lemma, chain C while it exists) to the refined lemmas at
   `δ = 1, η = 1`, delete the crude family and chain A. Replace `stopMart` by `stoppedProcess`.
3. **One block engine, two repackagings (done, see status below).** Generalize E's block lemma to an explicit `θ_j` and a
   summability hypothesis; make F's block lemma its instance; delete B and C; derive `_of_bdd`
   from E; state the `∃ C` corollaries as `IsBigO`. `AssignmentRate` then imports `LILSharp`.
4. **Library polish.** Strip the tooling attributes and the `tendsto` tactic from these files,
   rename to Mathlib conventions, relax `IsProbabilityMeasure` where possible, derive `MemLp`
   from increment bounds, rewrite docstrings, split files as in Section 3. At this point the L0
   lemmas, Ville, the quadratic-variation API and the exponential supermartingale + Freedman are
   ready to submit.
5. **New theory (optional, highest value).** A `HasCondBernsteinMGF`-style hypothesis structure;
   Stout's LIL via quadratic-variation stopping (subsumes D); the Hartman–Wintner lower half.

Stages 2 and 3 delete code; nothing in them is blocked by the blueprint any more.

## 5. Upstream candidates by readiness

- **Now, as small PRs:** Ville's inequality; `exists_pow_ge_le`; `log_add_two_le_add_loglog`;
  `ae_eventually_notMem_of_eventually_le`; the summability lemmas; `sum_one_div_sqrt_le`; the
  truncation moment lemmas; `div_log_add_two_lt`; the `log 3` facts;
  `exp_le_one_add_add_half_mul_sq` with explicit witness.
- **After Stage 4:** the `predQuadVar` API; the refined exponential supermartingale and Freedman's
  inequality (stated with `stoppedProcess`); `martingale_iidSum` and the quadratic variation of
  i.i.d. sums; Kolmogorov's medium-band lemma; theorems D and E with `IsBigO` corollaries.
- **After Stage 5:** Stout's martingale LIL; Hartman–Wintner in full.

---

## Status (2026-09-02): Stage 1 done, nothing deleted

The shared helpers live in `AlphaRAR/Mathlib/LILCommon.lean` (imported by `LIL.lean`, hence by
every LIL file), and every duplicated proof block calls them. No declaration was removed or
renamed; only proof bodies changed. The whole project builds with no warnings.

| Helper (in `LILCommon.lean`) | Replaces |
|---|---|
| `ae_eventually_notMem_of_eventually_le`, `ae_eventually_forall_lt_of_measure_le`, `ae_eventually_forall_le_lt_of_measure_le` | the 6 Borel–Cantelli blocks |
| `exists_pow_ge_le`, `log_add_two_le_add_loglog` | the `Nat.find` / `ρ^k ≤ ρV` / `log(k+2)` bookkeeping in all 6 repackagings |
| `abs_neg_increment`, `neg_ae_eq_zero`, `ae_exists_eventually_abs_le`, `ae_forall_one_lt_eventually_abs_le` | the 6 `-M` two-sided wrappers (to disappear entirely once rates are `IsBigO`) |
| `ae_forall_one_lt_eventually_le_of_forall_nat` | the 2 countable-`b` wrappers |
| `limsup_div_le_one_of_forall_one_lt`, `limsup_abs_div_le_one_of_forall_one_lt` | the 4 `limsup` wrappers, including the headline Hartman–Wintner theorem |
| `tendsto_add_two_div_pow`, `tendsto_log_add_two_div_pow` (moved from `LILSharp`) | `eventually_mul_add_two_le_two_pow` is now the `ρ = 2` instance |
| `one_lt_log_three`, `loglog_pos_of_three_le`, `loglog_pos_of_three_le_nat` | the 8 inline `1 < log 3` derivations in `LILHartmanWintner` |
| `summable_exp_neg_mul_sqrt_add` (in `LILTruncation.lean`) | the inline tail summability; `summable_block_bound` is now its instance |

Line counts: the five original files went from 4630 to 4166 lines; with the 276-line helper file
the total is 4442.

## Status (2026-09-02, later): Stage 2 done, one engine

`LIL.lean` now contains a single engine, parameterized by `(δ, η, hη)`: `exp_le_one_add_add_half_mul_sq`
(explicit window `min 1 (9δ/4)`, no hypothesis on `δ`), `condExp_exp_increment_le`, `expProcess`,
`supermartingale_expProcess`, Ville, `measure_exists_ge_le_exp`, `_optimized`, `_all`,
`measure_exists_ge_le_exp_horizon`, `ae_eventually_forall_lt_of_summable`. The `_refined` suffixes are
gone because there is nothing to contrast them with; `exp_le_one_add_add_sq` is the `δ = 1` window
and is what the remaining crude call sites (F's block lemma, chain C's block lemma, chain B's
Borel–Cantelli step) pass as `hη`.

Deleted: `condExp_exp_increment_le` (crude), `expProcess` (crude), `expProcessRefined_one`,
`supermartingale_expProcess` (crude), `measure_exists_ge_le_exp` (crude), `_optimized` (crude),
`_all` (crude), `_horizon` (crude), chain A (`ae_eventually_forall_lt_of_summable` crude,
`ae_eventually_forall_lt_dyadic`, `ae_eventually_le_sqrt_predQuadVar_mul_log`,
`ae_eventually_le_sqrt_nat_mul_log`), and `stopMart` with its three lemmas.

`stopMart` is replaced by Mathlib's `stoppedProcess M (fun _ ↦ (N : WithTop ℕ))`:
`stoppedProcess_const_of_le`/`_of_ge` (values below and past the horizon),
`martingale_stoppedProcess_const` (from `Submartingale.stoppedProcess` on `M` and `-M`),
`predQuadVar_stoppedProcess_const_of_le`. Two small Mathlib gaps surfaced and were added to
`LILCommon.lean`: `WithTop.untopA_coe` and `WithTop.untopA_natCast` (both `rfl`; note that
`(N : WithTop ℕ)` elaborates to `Nat.cast`, not `WithTop.some`, so the `Nat.cast` form is the one
`rw` needs). Gotcha: `rw [stoppedProcess_eq_of_ge h]` unifies `τ ω` with `↑N` as `τ := WithTop.some`,
`ω := N`; name `(τ := …)` explicitly.

Blueprint: CI runs `checkdecls`, so the three chain-A tags in `chap:pre_lil` were dropped and the two
`_refined` tags in `chap:pre_llil` renamed; all 48 tags in the two chapters resolve. Line count of the
LIL files: 4142 (from 4442 after Stage 1, 4630 originally). Full project build green.

## Status (2026-09-02, later still): Stage 3 done, one block engine

`LIL.lean` gained the time-block engine `ae_eventually_forall_le_lt_of_summable`: horizons `N_j`,
horizon-local increment bounds `c_j`, explicit parameters `θ_j` admissible eventually, thresholds
`λ_j`, levels `v_j`, and one hypothesis, summability of the Freedman exponents
`exp(-θ_j λ_j + ½(1+δ)θ_j² v_j)`. Both remaining growing-increment chains are now its instances,
each supplying only its schedule and the closed form of the exponent:

- E (`LILSharp`): `ae_eventually_lt_block_of_growing_loglog_sharp`, `θ_j = α√(log(j+2)/N_j)`,
  exponent `(½(1+δ)α²v − αC) log(j+2)`, a `p`-series (the square-root collapse is a
  `linear_combination` of `√a·√b = log(j+2)` and `√a²·N_j = log(j+2)`).
- F (`LILTruncation`): `ae_eventually_lt_block_of_growing`, `θ_j = 1/(a√(2^j))`, exponent
  `−(C/a)√j + v/a²`, summable by `summable_exp_neg_mul_sqrt_add`.

Deleted: chain B (`ae_eventually_forall_lt_of_summable_eventually`, `eventually_mul_add_two_le_two_pow`,
`ae_eventually_forall_lt_dyadic_loglog`, `ae_eventually_le_sqrt_predQuadVar_mul_loglog`,
`ae_eventually_le_sqrt_nat_mul_loglog`, `ae_eventually_abs_le_sqrt_nat_mul_loglog`,
`ae_eventually_abs_le_sqrt_predQuadVar_mul_loglog`), chain C (`measure_exists_ge_le_exp_block_loglog`,
`ae_eventually_lt_block_of_growing_loglog`, `ae_eventually_le_sqrt_nat_mul_loglog_of_growing`,
`ae_eventually_abs_le_sqrt_nat_mul_loglog_of_growing`), the per-block bounds
`measure_exists_ge_le_exp_block` and `measure_exists_ge_le_exp_block_loglog_sharp`,
`summable_block_bound`, `div_log_add_two_le`, the Hartman–Wintner bounded corollary
`ae_eventually_abs_sum_le_sqrt_nat_mul_loglog_of_bounded`, and the dead design wrapper
`measure_exists_truncRespMart_block`. With only the `p`-series lemma left, `LILLogLog.lean` was
removed (`summable_exp_neg_mul_log_add` now lives in `LILCommon.lean`); `LILSharp` imports `LIL`
directly and `AssignmentRate` imports `LILSharp`.

Added, in `LILSharp.lean`: `ae_isBigO_sqrt_predQuadVar_mul_loglog` (the `O`-rate corollary of the
sharp bounded LIL, `IsBigO` form), `ae_isBigO_sqrt_nat_mul_loglog_of_bdd` (the unconditional
bounded-increment LIL, `IsBigO` form, derived from E with constant growth `g ≡ c` via the new
`tendsto_sqrt_loglog_div_nat` in `LILCommon`), and `ae_eventually_abs_le_sqrt_nat_mul_loglog_of_bdd`
kept as its eventual-form unpacking for `AssignmentRate` (to be converted in Stage 4 together with
its consumers). `predQuadVar_iidSum_ge` is kept for the Stout route.

Blueprint: five chain-B/C tags retagged to the sharp lemmas or the `IsBigO` corollaries, two tags
dropped (`cor:hw_bounded`, `lem:trunc_block`), `lem:trunc_block_summable` retagged to
`summable_exp_neg_mul_sqrt_add`; all 43 tags in the two chapters resolve. Full project build green
with no warnings.

| | Lines |
|---|---|
| LIL files originally | 4630 |
| After Stage 1 (incl. `LILCommon`) | 4442 |
| After Stage 2 | 4142 |
| After Stage 3 (four files + `LILCommon`) | 3680 |

Remaining file roles: `LIL.lean` (engine: one-step inequality, exponential supermartingale,
Ville, Freedman, deterministic stopping, both block Borel–Cantelli steps), `LILSharp.lean` (sharp
bounded LIL D, sharp growing LIL E, `IsBigO` corollaries, unconditional bounded LIL),
`LILTruncation.lean` (truncation moment lemmas and the `√i`-increment log-rate chain F),
`LILHartmanWintner.lean`, `LILCommon.lean` (shared analysis and Borel–Cantelli helpers).
Next: Stage 4 (library polish) and Stage 5 (Stout's LIL, Hartman–Wintner lower half).

## Status (2026-09-02, last): Stage 4 done, library polish

- **`MemLp` is derived, not assumed.** `Martingale.memLp_of_abs_increment_le` (in
  `QuadraticVariation.lean`: `M 0 = 0` and bounded increments give `M n ∈ Lᵖ` on a finite
  measure) removed the `hM2 : ∀ n, MemLp (M n) 2 μ` hypothesis from the whole engine and every
  LIL statement; consumers no longer supply it (the design-level `integrable_truncRespMart_sq`
  became dead and was deleted).
- **No `tendsto` tactic in library files.** The two uses in the sharp growing chain are now
  `Tendsto.const_mul` plus `mul_zero`; the only remaining project use is in `ResponseCLT.lean`.
- **Rates as `IsBigO`.** `ae_isBigO_sqrt_nat_mul_log_of_growing` (chain F, two-sided) and
  `ae_isBigO_sqrt_nat_mul_loglog_of_bdd` are the statements; the `∃ C, ∀ᶠ` forms are gone and the
  two consumers (`ae_eventually_abs_truncRespMart_le_sqrt_nat_mul_log`,
  `ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog`) unpack `Asymptotics.isBigO_iff` locally,
  keeping their own paper-facing statements.
- **Typeclasses.** `condExp_exp_increment_le` and `supermartingale_expProcess` now need only
  `IsFiniteMeasure`; Freedman's inequality and the LILs keep `IsProbabilityMeasure` (they use
  `∫ Z_0 = 1`).
- **Names.** The `_sharp`/`_sharp'`/`_sharp_all` family, the `hw_*` prefixes, `hwCutoff`,
  `medium_crude`/`medium_tight`/`medium_sum_Icc_big`/`medium_inner_tsum_le`, and the `lam`
  binders are gone. The `∀ b > 1` statements are `ae_forall_one_lt_eventually_*`, fixed-parameter
  versions are `*_of_lt`, the trivial single-`b` wrapper for the bounded chain is inlined, the
  increment-bound hypothesis is `hb` everywhere. Full map: `ae_eventually_forall_lt_pow_loglog`,
  `ae_eventually_le_sqrt_predQuadVar_mul_loglog_of_lt`,
  `ae_forall_one_lt_eventually_le_sqrt_predQuadVar_mul_loglog`,
  `ae_forall_one_lt_eventually_abs_le_sqrt_predQuadVar_mul_loglog`,
  `ae_eventually_lt_block_of_growing_loglog`, `ae_eventually_le_sqrt_nat_mul_loglog_of_growing_of_lt`,
  `ae_eventually_le_sqrt_nat_mul_loglog_of_growing`,
  `ae_forall_one_lt_eventually_le_sqrt_nat_mul_loglog_of_growth`,
  `ae_forall_one_lt_eventually_abs_le_sqrt_nat_mul_loglog_of_growth`,
  `ae_forall_one_lt_eventually_abs_le_sqrt_nat_mul_loglog_centeredTruncation`,
  `ae_forall_one_lt_eventually_sum_le_sqrt_nat_mul_loglog` (ex `hw_eventually`),
  `sum_integral_truncation_add_mediumTrunc_le` (ex `hw_drift_bound`), `logCutoff` and
  `logCutoff_*` (ex `hwCutoff`, `cutoff_*`), `tendsto_sqrt_mul_loglog_atTop`,
  `tendsto_sqrt_div_sqrt_mul_loglog`, `sqrt_add_three_mul_loglog_le`,
  `lt_mul_sq_of_lt_mul_log_add_two`, `lt_mul_log_of_lt_mul_log_add_two`,
  `sum_Icc_one_div_mul_loglog_le`, `exists_sum_ite_one_div_mul_loglog_le`.
- **Files.** `LIL.lean` (the engine) is now `Freedman.lean`; `LILSharp.lean` (the LIL theorems)
  is now `LIL.lean`; `LILHartmanWintner.lean` is `HartmanWintner.lean`. `LILTruncation.lean` and
  `LILCommon.lean` keep their names. Imports, the root module and cross-references follow.
- **Ville over all times.** `smul_measure_exists_ge_le_integral_zero`:
  `ε · μ{∃ k, ε ≤ Z_k} ≤ E[Z_0]`, from the finite-horizon `smul_measure_sup_le_integral_zero` by
  continuity from below (the finite form mirrors Mathlib's `maximal_ineq`, so both are kept).
- **Kept deliberately.** The `@[specifies]` and `@[characterization]` annotations (the user's own
  LeanSpec tooling; they carry design intent, do not affect the mathematics, and are one-line
  deletions at PR time), and `predQuadVar_iidSum_ge` for the Stout route.
- Blueprint: all 42 `\lean` tags in the two chapters resolve; `cor:llil_nat` points at the `IsBigO`
  statement. Full project build green with no warnings.

| File | Lines |
|---|---|
| `Freedman.lean` | 550 |
| `LIL.lean` | 663 |
| `LILTruncation.lean` | 288 |
| `HartmanWintner.lean` | 1807 |
| `LILCommon.lean` | 339 |
| total (originally 4630) | 3647 |

Open: Stage 5 (a `HasCondBernsteinMGF`-style hypothesis structure, Stout's LIL via
quadratic-variation stopping, the Hartman–Wintner lower half) and the upstream submissions of
Section 5.

## Status (2026-09-02, later): quadratic-variation API review

`QuadraticVariation.lean` reviewed as a library file (`ℕ`-indexed only; continuous time is out of
scope). Build green, no warnings; blueprint tags for `lem:qv_incr` and `lem:qv_second_moment`
extended.

- **Hypothesis convention, now documented in the module docstring.** One-step lemmas
  (`predQuadVar_succ_sub_eq`, `predQuadVar_le_succ`) keep the minimal per-step integrability
  `hd2 : MemLp (ΔM_n) 2 μ`, `hprod : Integrable (M_n ΔM_n) μ` (strictly more general than `L²`:
  it covers `M_0 ∈ L¹` with bounded increments). Path-level lemmas (`predQuadVar_mono`,
  `predQuadVar_nonneg`, `predQuadVar_ae_eq_sum`, `submartingale_sq`, the Itô isometries) take the
  square-integrable martingale `hM2 : ∀ n, MemLp (M n) 2 μ`; every consumer already had it.
- **Hypothesis-free facts made hypothesis-free.** `integrable_predQuadVar` (a finite sum of
  conditional expectations; was asking for adaptedness and `L²`), `stronglyAdapted_predQuadVar`,
  `stronglyMeasurable_predQuadVar_succ`, `isStronglyPredictable_predQuadVar`. The last three
  replace five call-site leaks of `stronglyAdapted_predictablePart (f := fun n ↦ M n ^ 2)`.
- **New API.** `predQuadVar_eq_sum` (the defining sum, `rfl`), `predQuadVar_add_one` (mirrors
  `predictablePart_add_one`; replaces `predQuadVar_succ_sub`), `predQuadVar_zero_apply` (simp),
  `predQuadVar_const_smul` (`⟨c • M⟩ = c² ⟨M⟩`), `predQuadVar_ae_eq_sum`
  (`⟨M⟩_n = ∑_{i<n} μ[(ΔM_i)² | ℱ_i]`), the telescoping trio `predQuadVar_eq_sum_succ_sub`,
  `predQuadVar_le_sum_of_succ_sub_le`, `sum_le_predQuadVar_of_le_succ_sub` (increment bounds ⇒
  path bounds; `v : ℕ → Ω → ℝ` so random summands work), the general Itô isometry
  `integral_sq_eq_integral_sq_zero_add_integral_predQuadVar` (`E[M_n²] = E[M_0²] + E[⟨M⟩_n]`,
  no `M_0 = 0`), `integral_predQuadVar_eq_sum` and `integral_sq_eq_sum_integral_increment_sq`
  (`E[M_n²] = ∑_{k<n} E[(ΔM_k)²]`), and the general `Martingale.integral_eq` (constant expectation,
  any index/codomain; replaces `martingale_integral_eq`).
- **`IsPredQuadVar.predictable` is now Mathlib's `IsStronglyPredictable ℱ A`** rather than the
  hand-unfolded `StronglyAdapted ℱ fun n ↦ A (n + 1)`.
- **Proof simplifications.** `submartingale_sq` via `submartingale_nat` and the increment formula
  (no set-integral juggling); `predQuadVar_le_of_bound`, `integral_sq_le_of_increment_bound`
  through the telescoping/sum lemmas.
- **Consumers.** The hand-rolled telescoping in `predQuadVar_iidSum_le`/`_ge`
  (`HartmanWintner.lean`), the bracket bound and the two `∫ S_n² = ∑ ∫ (ΔS_k)²` derivations
  (`MartingaleSLLN.lean`, `HartmanWintner.lean`) and `predQuadVar_genRespMart_eq`
  (`ResponseTruncation.lean`, induction replaced by `predQuadVar_ae_eq_sum`) now call the API;
  net −40 lines outside the QV file.
- **Not done, deliberately.** No predictable covariation `⟨M, N⟩` (nothing needs it yet;
  `predQuadVar_add_of_martingale_mul` covers the orthogonal case), no martingale-transform lemma
  `⟨H·M⟩ = H²·⟨M⟩` (would be the right home for the `bracketSeries`/weighted-series QV computations;
  a natural next coherent area), and `predQuadVar_stoppedProcess_const_of_le` stays in
  `Freedman.lean` with the other deterministic-horizon lemmas.
