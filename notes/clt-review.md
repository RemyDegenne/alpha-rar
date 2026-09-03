# Martingale CLT review (2026-09-02)

Review of `AlphaRAR/Mathlib/MartingaleCLT.lean` from the Mathlib-reusability angle, after the
quadratic-variation review of the same day (`notes/lil-review.md`, last section). Scope: the
Lindeberg/Hall–Heyde martingale CLT for a triangular array and its analytic prerequisites; the
downstream design-level CLTs (`ResponseCLT*.lean`, `JointCLT.lean`, `AnscombeCLT.lean`) were only
touched where the API changed under them.

## What was found

- **Statement form.** `mart_clt` concluded with `Tendsto (β := ProbabilityMeasure ℝ)
  (fun n ↦ ⟨P.map (rowSum n), _⟩) atTop (𝓝 ⟨gaussianReal 0 σ², _⟩)`. Mathlib's own CLT
  (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) concludes
  `TendstoInDistribution X atTop Y (fun _ ↦ P) P'` for any `Y` with `HasLaw Y (gaussianReal …) P'`.
  The project form is a special case (`Y := id`, `HasLaw.id`, then `.tendsto`), and every
  `ProbabilityMeasure`-form Slutsky wrapper in the project exists only to bridge the two forms.
- **A byte-identical twin.** `mart_clt_bounded` (bounded predictable variation) had the same body
  as `mart_clt` apart from the inner call, and no user.
- **A 65-line ad-hoc proof of a standard fact.** Bounded convergence in probability
  (`tendsto_integral_of_tendstoInMeasure_zero` and its `‖·‖` half) was proved by an `ε/2` argument;
  it is the subsequence principle (`Filter.tendsto_of_subseq_tendsto`,
  `TendstoInMeasure.exists_seq_tendsto_ae`) plus dominated convergence, five lines.
- **Two unrelated developments living in the file.** The `ProbabilityMeasure`-form Slutsky lemmas
  (multiplicative here, additive in `AnscombeCLT.lean`, general continuous map here) are
  translations of Mathlib's `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`
  with no martingale content.
- **Small duplication**: the `hmono` block of `predVar_trunc_ae_eq_of_le` and
  `rowSum_trunc_ae_eq_of_le`; the unused `abs_exp_mul_one_sub_le` (the `y ≤ 1` bound, superseded by
  the primed `y²eʸ` form actually used); the array's predictable variation `predVar` never connected
  to `predQuadVar` although the blueprint says `V_n = ⟨M_n⟩_{k_n}`.
- **Fine as is.** `norm_expI_sub_taylor_le` and its two lower-order bounds: Mathlib's
  `Complex.norm_exp_sub_one_sub_id_le` needs `‖x‖ ≤ 1`, the CLT needs all real `x`, and the integral
  proofs are the standard ones (constants `min(2x², |x|³)` rather than the sharp `min(x², |x|³/6)`;
  sharpening would thread new constants through eight lemmas for no gain here). `MartDiffArray` as a
  bundled structure (data with the martingale-difference proofs) is the right shape for a
  triangular array; `condVar` is the uncentred conditional second moment, standard in the
  martingale literature, and `condVar_ae_eq_condVar` records that it is Mathlib's
  `ProbabilityTheory.condVar` a.e. `tendsto_integral_sq_indicator_gt`, `tendstoInMeasure_bdd_mul`,
  `tendstoInMeasure_zero_of_le`, `condExp_sq_le`, `condExp_min_le` are Mathlib-shaped and Mathlib
  lacks them.

## What was done

- `mart_clt` now concludes `TendstoInDistribution A.rowSum atTop Y (fun _ ↦ P) P'` from
  `hY : HasLaw Y (gaussianReal 0 σ².toNNReal) P'`, exactly the shape of Mathlib's CLT.
  `mart_clt_bounded` deleted. The two users (`respMart_div_sqrt_tendsto_gaussianReal`,
  `wLinComb_scaled_tendsto_gaussianReal`) pass `HasLaw.id`, take `.tendsto`, and simplify
  `Measure.map_id`; their statements are unchanged.
- `tendsto_integral_of_tendstoInMeasure`: the general bounded-convergence statement (limit `f`, not
  just `0`; `AEStronglyMeasurable`, `IsFiniteMeasure`), five lines. The `‖·‖` variant is gone.
- The three `ProbabilityMeasure`-form Slutsky wrappers were first moved to their own file
  (`Slutsky.lean`), then deleted the same day when the whole project moved to
  `TendstoInDistribution` (see *Left open*, first item).
- `partialVar_succ_le_predVar` factored out; `abs_exp_mul_one_sub_le` deleted (blueprint lemma
  removed with it); `martingale_partialSum` and `predVar_ae_eq_predQuadVar` added
  (`V_n = ⟨S_{n,·}⟩_{k_n}` a.e., via `predQuadVar_ae_eq_sum`), which is the coherence link between
  the CLT file and `QuadraticVariation.lean`.
- Blueprint: `lem:clt_truncation` tagged with the eight truncation lemmas; `thm:mart_clt` states
  the Mathlib form; the unused real bound is gone.

## Left open

- ~~**Project-wide statement form.**~~ Done the same day: every convergence in distribution in the
  project (twelve files, the two Comparator challenge statements included) is now
  `TendstoInDistribution X atTop id (fun _ ↦ P) ν` with `ν` the limit law. `Slutsky.lean` is gone;
  `AlphaRAR/Mathlib/TendstoInDistribution.lean` holds the five complements to Mathlib's API that
  the applications need (`congr'` with an eventual change of sequence, `comp` with a subsequence,
  `tendstoInDistribution_id_iff` to name a limit by its law or by a variable,
  `mul_of_tendstoInMeasure_const`, and the Cramér–Wold device `tendstoInDistribution_of_forall_inner`
  restated from the vendored `tendsto_map_of_tendsto_map_inner`). The Comparator challenge
  statements no longer mention any auxiliary measurability lemma, since measurability is a field of
  the conclusion; their configs list one target each. The tightness lemma became
  `tight_of_tendstoInDistribution`.
- **`predVar` versus `predQuadVar`.** With `predVar_ae_eq_predQuadVar` in place, the array could
  *define* `predVar` through `predQuadVar` of the row martingale; today the sum-of-`condVar` form is
  what the truncation argument manipulates, so this was not done.
- **Constants.** The sharp Taylor constants for `e^{ix}` if the file is upstreamed.
