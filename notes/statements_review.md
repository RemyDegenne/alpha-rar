# Review of the main results reported in `formalization.yaml`

**Question asked.** Do the six declarations listed under `status.main_results` state what the paper
(`arxiv/sections/`, as compiled) says they state? Checked against the paper's LaTeX source, the Lean
statements and their definitional dependencies.

**Date.** 2026-09-01.

---

## 1. Mechanical claims — all verified

* `#print axioms` on the six main results, plus
  `estimator_sqrtN_joint_tendsto_multivariateGaussian` and
  `estimatorError_joint_tendsto_multivariateGaussian`: exactly
  `[propext, Classical.choice, Quot.sound]` for each.
* No `sorry` anywhere under `AlphaRAR/`.
* `lean_lines`, `theorems_and_lemmas`, `definitions` — all three exact.
* `comparator/Challenge_aRTS_LLN.lean` restates `AlphaRAR.aRTS_LLN` character-identically.

Core definitions match the paper: `estimator` is equation (1) including the `+θ₀ / +1`
regularization; `IsARTS.throttle` is condition (3) with the right index shift (`m = n+1`, via
`histTarget_eq`); Condition **A** is `MemLp id 2 (ν a)`, i.e. `E|ξ_{1,k}|² < ∞`; `IsLittleOpOne` is
the paper's `o_p`; `ν.means k = (ν k)[id] = θ_k`; `Var[id; ν k] = V_k`.

## 2. Statement-by-statement

| `formalization.yaml` claim | Lean conclusion | verdict |
|---|---|---|
| Thm 4.1 → `aRTS_LLN` | `N/n → v_k`, `θ̂_k → θ_k`, `θ̂_k − θ_k = O(√(loglog n/n))`, `ρ̂_k − v_k = O(√(loglog n/n))` | exact |
| Thm 4.2(ii) eq (9) → `aRTS_clt_joint` | `(√n(N_n/n−v), √n(ρ̂_n−v)) ⇒ 𝒩(0,Ω)`, all four blocks `G·diag(V_k/v_k)·Gᵀ` | exact |
| eq (5) → `aRTS_prop_dev` | `(N_{n,k} − n ρ̂_{n,k})/√n → 0` in measure | exact |
| eq (6) → `aRTS_prop_dev_ae` | `N_{n,k} − n ρ̂_{n,k} =O[atTop] √(n loglog n)` a.s. | exact |
| eq (7) → `aRTS_count_sub_smul_ae` | `N_{n,k} − n v_k =O[atTop] √(n loglog n)` a.s. | exact |
| Thm 5.2 → `aRTSFE_sparse_rate_of_isARTSFE` | `N→∞`, `N/n→v_k`, `|θ̂_k−θ_k| ≤ C√(loglog N_{n,k}/N_{n,k})` | exact |
| Cor 5.3 → `aRTSFE_sparse_clt_of_contDiffAt` | `D_n(Θ̂_n−Θ) ⇒ 𝒩(0, diag(V_1,…,V_K))` | conclusion exact; finding 1 |

Theorem 4.1's three conclusions are `aRTS_proportion_tendsto`, `aRTS_theta_rate` and
`aRTS_rho_rate`, bundled (together with the consistency `aRTS_theta_consistent`) into `aRTS_LLN`.

## 3. Findings

### 1. Corollary 5.3 carries two hypotheses beyond the documented `(⋆)`

`fidelity.divergences` item 2 describes only the schedule swap `h = o(√n)` → `(⋆)`.
`aRTSFE_sparse_clt_of_contDiffAt` (`AlphaRAR/YDK2026/ForcedExploration.lean`) additionally assumes

* `hshift` — schedule regularity `h(n − (K⌈h(n)⌉+1)) / h(n) → 1`;
* `hT2` — `T` is `C²` at `Θ` on the sparse coordinates (`T ν.means a = 0 → ContDiffAt ℝ 2 (T · a)`).

`hT2` is a genuine added assumption, since the paper states Corollary 5.3 under Condition **A**
alone. Both are documented in `maths/sparse-clt-fix.md` (the "Theorem (sparse componentwise CLT)"
box), and `sched23_satisfies_schedule_hypotheses` checks `hshift` and `(⋆)` for `h(n) = n^{2/3}`;
it is only the yaml summary that understates them.

### 2. No design is ever shown to be `IsARTSFE`

The αRTS side is anchored: `distance_isARTS`, `erade_isARTS`, `dTracking_isARTS`
(`AlphaRAR/YDK2026/ARTSDesigns.lean`), on top of LML's Ionescu–Tulcea construction of an
`IsAlgEnvSeq` process for any algorithm and environment. For αRTS-FE, `IsARTSFE` occurs only in its
own definition and in the bridge lemmas `throttle_of_isARTSFE` / `fe_of_isARTSFE` — the whole of
Section 5 (Thm 5.1, Thm 5.2, Cor 5.3) rests on a predicate with no exhibited instance. `sched23`
covers the *schedule* hypotheses only. Given that `status.scope` claims "Section 5 in full", this
deserves either an instance (D-Tracking with forced exploration) or an explicit caveat.

### 3. Condition **B**'s encoding differs from the paper in both directions

The paper has `ρ : H → Δ_K` twice differentiable on an open `H ⊇ I_1×…×I_K`. The Lean statements
take `T` **total**, simplex-valued *everywhere* (`hTnn`, `hTsum` quantified over all `z`), and
**globally** `LipschitzWith K` for the normality results — stronger than the paper — while requiring
only `DifferentiableAt`/`HasFDerivAt` at `Θ`, i.e. dropping `C²` — weaker. Divergence item 3 covers
dropped hypotheses but not the added global Lipschitz/simplex-valuedness, which restricts which `ρ`
are covered (in practice: one must extend `ρ` off `H`).

`hTpos` is stated on `attainableSet A Y (θ₀ k) k` — the closure of the estimator range along *this*
process — rather than the paper's `I_k` (all realizations), so it is a weaker demand than
Condition **B**, hence a stronger theorem. Positivity alone is assumed, not `ρ(z) ∈ (0,1)^K`, which
is equivalent given `hTnn`/`hTsum`.

### 4. Minor family-shape differences, none documented

* **Burn-in dropped.** `IsARTS`/`IsARTSFE` demand the throttle for *all* `m ≥ 1`; Definition 3.1
  asks it only for `m ≥ K m₀`. The paper's remark says `m₀` does not affect the proofs, but the
  formalized family is the `m₀ = 0` one.
* **`α ∈ [0,1]` vs the paper's `[0,1)`.** `aRTS_LLN` assumes only `hα : α ∈ Set.Icc 0 1`, so
  Theorem 4.1 holds for `α = 1` as well — a genuine generalization. The normality results keep
  `hα1 : α < 1`.
* **`IsARTSFE.forced` is weaker than Definition 5.1**: it requires mass `0` outside `S_m` rather
  than uniform `1/|S_m|` on it — a strictly larger family, and fine.
* **`IsExplorationSchedule` adds `Monotone h`**, which the paper does not require (harmless for the
  schedules of interest, but it is an extra demand).

### 5. Two conclusions have no design-level statement

* **Equation (8).** The `aRTS_clt_joint` note says the marginal estimator CLT "is
  `AlphaRAR.estimator_sqrtN_joint_tendsto_multivariateGaussian`", but that lemma
  (`AlphaRAR/YDK2026/ResponseCLTJoint.lean`) takes `N_{n,a}/n → v_a` as a *hypothesis*; there is no
  `aRTS_clt_theta`. Same for `clt_rho`. The instantiation is immediate from
  `aRTS_proportion_tendsto` + `hTpos`, but it is not in the development.
* **Theorem 5.1.** Of the five declarations, `aRTSFE_proportion_tendsto` concludes
  `∃ u, N/n → u ∧ ρ̂ → u` without identifying `u = v`, and the Theorem 4.1 rates for αRTS-FE are
  absent. The identification `N/n → T ν.means` does exist — under Condition **A** only — inside
  `aRTSFE_sparse_rate_of_isARTSFE`.

### 6. Two declarations attributed to the wrong module

`isBigOpOne_martingale_div_sqrt` and `isBigOpOne_of_bdd_increments` live in
`AlphaRAR/Mathlib/MartingaleRate.lean`, not `AlphaRAR.Mathlib.StochasticOrder` as the Appendix-C
alignment note says.

## 4. Divergences that check out

* **Item 1 (Lemma 4.5).** `estimatorError_joint_tendsto_multivariateGaussian` does assume regularity
  `N_{n,a}/c_{a,n} → v_a > 0` for a deterministic `c` (the yaml says "→ 1"; equivalent up to
  rescaling `c`). Theorems 4.1 and 4.2 get it for free, as claimed. Consistent with
  `notes/regularity-gap.md`.
* **Item 2 (Definition 5.1).** `IsExplorationSchedule` keeps `h → ∞` and `h = o(n)` and no result
  assumes `IsSqrtSmall`; `sched23_satisfies_schedule_hypotheses` and `not_isSqrtSmall_sched23` do
  establish non-vacuity outside the paper's condition. See finding 1 for what the summary omits.
* **Item 3 (generalizations).** The hitting-time interface, the unconditional bounded-increment LIL
  and 0-based indexing are as described.
