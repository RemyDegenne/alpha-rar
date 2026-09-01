# Closing the sparse-CLT gap by reversing the exploration-schedule condition

**Claim of this note.** The condition $h(n)=o(\sqrt n)$ in Definition `def:rts-fe-def` is
(a) **not necessary** for the non-sparse theory, and (b) **exactly what blocks** the sparse
componentwise CLT. Replacing it by
$$\sqrt{n\log\log n}\ \ll\ h(n)\ =\ o(n) \tag{$\star$}$$
loses nothing and closes the gap identified in `notes/regularity-gap.md`.

Under $(\star)$ every sparse arm satisfies $N_{n,k}/h(n)\to1$ a.s., which is precisely the regularity
hypothesis the componentwise CLT needs — and it is already formalized
(`AlphaRAR.pullCount_div_sched_tendsto_one`, `AlphaRAR.aRTSFE_sparse_clt`).

A pleasant side effect: under $(\star)$ the D-Tracking schedule $h(n)=(\sqrt n-K/2)^+$ becomes
*admissible* for the non-sparse theory, which the paper currently has to exclude.

Notation follows the paper: $N_{n,k}$ counts, $\hat\rho_{n,k}=T(\hat\Theta_n)_k$, $v=T(\Theta)$,
$V_k$ the arm variances, $K=|\mathcal A|$, $\mathbf U_m=\{j:N_{m,j}\le h(m)\}$.

---

## 1. Where $h=o(\sqrt n)$ is actually used, and why it is not needed

In the paper, $h(n)=o(\sqrt n)$ enters in exactly one place: the proof of `thm:forced` bounds the
generic-condition gap by
$$N_{\ell_{n,k},k}-\ell_{n,k}\hat\rho_{\ell_{n,k},k}\ \le\ h(\ell_{n,k})\ =\ o(\sqrt n),$$
because `thm:normality` needs that gap to be $o_p(\sqrt n)$. Forced exploration can add up to
$h(n)$ pulls, so $h=o(\sqrt n)$ is a convenient *sufficient* condition.

It is not necessary, because under Condition **B** forced exploration switches itself off.

> **Proposition 1 (FE is eventually inactive under Condition B).** *(formalized:
> `AlphaRAR.underExplored_eventually_empty`)*
> Assume Condition **B** ($v_k>0$ for all $k$) and $h(n)=o(n)$. Then a.s. $\mathbf U_n=\emptyset$
> for all large $n$; consequently the $\aRTSFE$ design eventually coincides with an $\alpha$RTS
> design and `thm:LLN`, `thm:normality` hold verbatim.
>
> *Proof.* `thm:LLN` for $\aRTSFE$ needs only $h(n)=o(n)$ — the smallness input is
> $N_\ell-\ell\hat\rho_\ell\le h(\ell)=o(n)$ (in Lean: `aRTSFE_smallness_all`, which consumes
> `IsExplorationSchedule.div_tendsto_zero`, i.e. $h(n)/n\to0$). So $N_{n,k}/n\to v_k>0$, hence
> $$\frac{N_{n,k}}{h(n)}=\frac{N_{n,k}}{n}\cdot\frac{n}{h(n)}\longrightarrow v_k\cdot\infty=\infty .$$
> So $N_{n,k}>h(n)$ eventually, for every $k$; i.e. $\mathbf U_n=\emptyset$ eventually. From that
> point the forced-exploration clause of `def:rts-fe-def` is vacuous and the design satisfies the
> $\alpha$RTS throttle at every round, so the gap is eventually $0$ and all smallness conditions
> hold trivially. $\square$

There is no circularity: the LLN uses only $h=o(n)$, and the normality input is then obtained from
the LLN rather than from a bound on $h$.

**Consequence.** Condition (ii) of `def:rts-fe-def` may be weakened from $h(n)=o(\sqrt n)$ to
$h(n)=o(n)$ with no loss anywhere in the non-sparse theory. In particular D-Tracking's
$h(n)=(\sqrt n-K/2)^+$ — which the paper's Example must currently disqualify — becomes admissible.

*Formalization note.* `IsExplorationSchedule` has been weakened accordingly: its field is now
`div_tendsto_zero` ($h=o(m)$). Proposition 1 is wired all the way through, so **no declaration
assumes $h=o(\sqrt m)$**: the paper's condition survives only as the predicate `IsSqrtSmall`, which
is never taken as a hypothesis and is kept to record what the paper asks and to state that the
sparse regime lies outside it (`not_isSqrtSmall_sched23`). See §5.

## 2. What a sparse arm's count really is

Let $v_k=0$. Since $T\ge0$ (it takes values in the simplex) and $T(\Theta)_k=0$, the point $\Theta$
*minimises* $x\mapsto T(x)_k$. Hence $\nabla T_k(\Theta)=0$, and if $T_k$ is $C^2$ near $\Theta$,
$$\hat\rho_{m,k}=T(\hat\Theta_m)_k\ \le\ C\,\|\hat\Theta_m-\Theta\|^2 . \tag{2.1}$$

Two mechanisms feed arm $k$:

* **forced exploration**, contributing $\approx h(n)$ pulls;
* **targeting**, which under the tracking dynamics drives $N_{n,k}/n$ toward $\hat\rho_{n,k}$, i.e.
  contributes $\approx n\hat\rho_{n,k}$ pulls.

Using $\|\hat\Theta_m-\Theta\|^2\asymp V_k/N_{m,k}$ (the sparse arm is the least sampled, so it
dominates the error), the targeting contribution is $\asymp n/N_{n,k}$, and the self-consistent
solution of $N\asymp n/N$ is
$$\boxed{\,N_{n,k}\ \asymp\ \sqrt n\,}\qquad\text{(targeting-dominated).}$$

So **which mechanism wins is decided by comparing $h(n)$ with $\sqrt n$:**

| regime | dominant mechanism | $N_{n,k}$ | regularity? |
|---|---|---|---|
| $h(n)\ll\sqrt n$ (the paper's condition) | targeting | $\asymp\sqrt n$, coupled to $\hat\Theta$'s own fluctuation | **unclear** |
| $h(n)\gg\sqrt n$ | forced exploration | $\sim h(n)$, deterministic | **yes** |

The paper's condition (ii) puts us in the first row — the one where the CLT is not available. This
is the precise sense in which $h=o(\sqrt n)$ *causes* the gap.

## 3. The fix: $\sqrt{n\log\log n}\ll h(n)=o(n)$

Assume $(\star)$ and $T_k$ of class $C^2$ near $\Theta$. Fix a sparse arm $k$ ($v_k=0$). Write
$\mathcal E_n$ for the number of rounds $m<n$ at which arm $k$ was pulled with
$\mathbf U_m=\emptyset$ ("non-FE pulls").

The argument is a bootstrap, each step of which is already available (in Lean, where indicated).

> **Step 1 (unconditional lower bound).** Forced exploration alone gives
> $$N_{n,j}\ \ge\ h\big(n-K\lceil h(n)\rceil-1\big)\qquad\text{for every }j .$$
> *Lean:* `AlphaRAR.pullCount_ge_min_sched_of_fe`. The selected arm at an FE round is a
> least-sampled under-explored arm, hence at the global minimum, so the potential
> $D(m)=\sum_j(L-N_{m,j})^+$ drops by exactly one per round while the minimum is below $L$; as
> $D\le KL$, that lasts at most $KL$ rounds. Under $(\star)$ plus mild regularity of $h$ this reads
> $N_{n,j}\gtrsim h(n)$.

> **Step 2 (rate for the estimator).** *(the composition into the target is formalized:
> `AlphaRAR.aRTSTarget_le_loglog_of_quadratic`)* From Step 1 and the subsampled LIL,
> $$\|\hat\Theta_m-\Theta\|^2\ =\ O\!\Big(\frac{\log\log h(m)}{h(m)}\Big)\quad\text{a.s.}$$
> *Lean:* `AlphaRAR.abs_estimator_sub_le_rate_loglog_N` gives exactly
> $|\hat\theta_{m,k}-\theta_k|=O(\sqrt{\log\log N_{m,k}/N_{m,k}})$; the non-sparse coordinates
> contribute $O(\log\log m/m)$, which is smaller.

> **Step 3 (the throttle fires).** *(formalized: `AlphaRAR.not_aRTSFEUnder_of_sched_lt`)*
> Combining (2.1) with Step 2,
> $\hat\rho_{m,k}=O(\log\log h(m)/h(m))$. If $k\notin\mathbf U_m$ then $N_{m,k}>h(m)$, so
> $$\frac{N_{m,k}}{m}\ >\ \frac{h(m)}{m}\ \overset{?}{>}\ C\frac{\log\log h(m)}{h(m)}\ \ge\ \hat\rho_{m,k},$$
> and the middle inequality holds exactly when $h(m)^2\gg m\log\log m$ — i.e. **precisely under
> $(\star)$**. So whenever arm $k$ is not under-explored it *is* over-sampled relative to its target,
> and the $\alpha$RTS throttle applies: $p_{m+1,k}\le\alpha\hat\rho_{m,k}$.

> **Step 4 (non-FE pulls are negligible).**
> *If $\alpha=0$* (e.g. D-Tracking) — *(formalized:
> `AlphaRAR.not_pulled_of_sched_lt_of_alpha_zero`)*: Step 3 gives $p_{m,k}\le0$, and $p_{m,k}$ is a
> conditional expectation of a nonnegative function, so $p_{m,k}=0$; integrating over the
> ($\mathcal F_{m-1}$-measurable) event $\{h(m)<N_{m,k}\}$ forces $\mathbf 1\{A_m=k\}=0$ there. So
> $\mathcal E_n\equiv0$ — arm $k$ is a.s. fed *only* by forced exploration.
> *If $\alpha>0$* — *(formalized: `AlphaRAR.nonFE_count_div_sched_tendsto_zero`)*: the compensator of $\mathcal E_n$ is
> $\sum_{m<n}\alpha\hat\rho_{m,k}=O\!\big(n\log\log h(n)/h(n)\big)=o(h(n))$ under $(\star)$, and
> $\mathcal E_n$ minus its compensator is a martingale with increments in $[-1,1]$, hence
> $O(\sqrt{n\log\log n})=o(h(n))$ a.s. by the LIL. So $\mathcal E_n=o(h(n))$ either way.

> **Step 5 (upper bound and conclusion).** At an FE round the selected arm is under-explored, so a
> pull leaves it at $h(m)+1$; hence
> $$N_{n,k}\ \le\ h(n)+1+\mathcal E_n\ =\ h(n)(1+o(1)).$$
> *Lean:* `AlphaRAR.pullCount_le_sched_of_fe_except`, which carries a monotone counter $E$ of the
> non-FE pulls and needs only $E=o(h)$ — so it covers $\alpha>0$ as well as $\alpha=0$. With Step 1,
> $$\boxed{\ \frac{N_{n,k}}{h(n)}\ \longrightarrow\ 1\quad\text{a.s.}\ }$$

> **Theorem (sparse componentwise CLT).** Under Condition **A**, $(\star)$, $T$ of class $C^2$ near
> $\Theta$, and mild regularity of $h$, every $\aRTSFE$ design satisfies
> $$D_n(\hat\Theta_n-\Theta)\ \Longrightarrow\ \mathcal N\big(0,\operatorname{diag}(V_1,\dots,V_K)\big),\qquad D_n=\operatorname{diag}(\sqrt{N_{n,1}},\dots,\sqrt{N_{n,K}}),$$
> with no positivity assumption on $v$.
>
> *Proof.* Sparse arms are regular against $c_{k,n}=h(n)$ by Steps 1–5; non-sparse arms are regular
> against $c_{k,n}=v_kn$ by `thm:LLN` (which needs only $h=o(n)$). Feed the per-arm normalizers into
> the componentwise CLT. *Lean:* `AlphaRAR.aRTSFE_sparse_clt`, already proved — Steps 1–5 discharge
> its `FEfed` hypothesis. $\square$

### Sharpness of the exponent

Step 3 is where the smoothness of $T$ enters. With $T_k$ merely **differentiable** at $\Theta$ one
only gets $\hat\rho_{m,k}=o(\|\hat\Theta_m-\Theta\|)=o(h(m)^{-1/2})$, and the comparison in Step 3
becomes $h(m)/m\gg h(m)^{-1/2}$, i.e. $h(m)\gg m^{2/3}$. So:

| smoothness of $T_k$ at $\Theta$ | threshold for $h$ |
|---|---|
| $C^2$ | $h\gg\sqrt{n\log\log n}$ |
| differentiable only | $h\gg n^{2/3}$ |

A single safe choice covering both: **$h(n)=n^{3/4}$** (or any $n^{2/3}\ll h\ll n$).

## 4. The trade-off, and why nothing is lost

Giving sparse arms $h(n)\gg\sqrt n$ pulls perturbs the other arms' counts by $O(Kh(n))\gg\sqrt n$, so
one might fear breaking `thm:normality`. It does not, because the two situations are disjoint:

* `thm:normality` assumes Condition **B** — *no* sparse arms — and then Proposition 1 says forced
  exploration is eventually inactive, so there is no perturbation at all.
* The sparse CLT lives under Condition **A** only, where `thm:normality` is not claimed.

What genuinely fails under $(\star)$ with a sparse arm present is the $\sqrt n$-scaled *proportion*
statement $\sqrt n(N_{n,j}/n-v_j)\Rightarrow$ normal — but that is a Condition-**B** statement, so it
is never invoked in the sparse regime. The componentwise estimator CLT, which is what
`corr:componentwise` asserts, is untouched: it needs only $N_{n,j}/(v_jn)\to1$, which follows from
`thm:LLN` under $h=o(n)$.

So the two conditions serve disjoint theorems, and $(\star)$ is compatible with everything the paper
proves.

## 5. Formalization plan

Already done (build green):

* `underExplored_eventually_empty` — **Proposition 1**, the §1 claim that $h=o(\sqrt n)$ is
  unnecessary. Formalized, so that claim is verified rather than asserted.
* `pullCount_ge_min_sched_of_fe` — Step 1.
* `abs_estimator_sub_le_rate_loglog_N` — Step 2.
* `pullCount_le_sched_of_fe_except`, `pullCount_div_sched_tendsto_one` — Step 5, in the
  $E=o(h)$ form (so $\alpha>0$ is covered).
* `aRTSFE_sparse_clt` — the Theorem, given `FEfed`.

Also done:

* **`IsExplorationSchedule` relaxed, and $h=o(\sqrt m)$ eliminated everywhere.** Its `littleO`
  field ($h=o(\sqrt m)$) is replaced by `div_tendsto_zero` ($h=o(m)$), and **no declaration of the
  development assumes $h=o(\sqrt m)$** — the predicate `IsSqrtSmall` is kept only as a record of
  the paper's condition and to state that the sparse regime lies outside it
  (`not_isSqrtSmall_sched23`, `sched23_satisfies_schedule_hypotheses`).

  The four $\sqrt n$-scaled normality results (`aRTSFE_prop_dev`, `aRTSFE_prop_dev_ae`,
  `aRTSFE_count_sub_smul_ae`, `aRTSFE_clt_joint`) get their smallness from Proposition 1 instead of
  from a bound on $h$. The chain is:

  - `eventually_sched_lt_pullCount` — the single-arm form of Proposition 1: $N_{n,k}/n\to v>0$ and
    $h=o(n)$ give $h(n)<N_{n,k}$ for $n\ge n_0(\omega)$, i.e. arm $k$ is eventually never
    under-explored;
  - `aRTSFE_gap_le_sum_of_not_underExplored` — pathwise: past $n_0$ the hitting predicate can only
    fire through its *under-sampling* clause (gap $\le0$), so for **every** $n$ the gap is bounded
    by $C(\omega):=\sum_{m<n_0}(N_{m,k}-m\hat\rho_{m,k})^+$, a path constant;
  - `aRTSFE_smallness_op` / `aRTSFE_smallness_upper` — a constant is $o(\sqrt n)$ and
    $O(\sqrt{n\log\log n})$ for free (the $o_p$ form needs the gap to be measurable in $\omega$:
    `measurable_gap_hitting`).

  The Condition **B** input ($v>0$ and $N_{n,k}/n\to v$) is `target_pos_of_theta_consistent` and
  `proportion_tendsto_of_hitting`, both fed by `aRTSFE_smallness_all`, which uses only $h=o(m)$ —
  so there is no circularity.

  This is also what makes the sparse results *usable*: with `littleO` a field, the regularity
  theorem could only ever be discharged in the regime where forced exploration does **not**
  dominate.

* **Step 3** — `not_aRTSFEUnder_of_sched_lt`: at a round where arm $k$ is not under-explored and its
  target has decayed below $h(m)/m$, arm $k$ is over-sampled, i.e. `¬ aRTSFEUnder` — the antecedent
  of the throttle.
* **Step 4, $\alpha=0$** — `not_pulled_of_not_aRTSFEUnder_of_alpha_zero`: whenever arm $k$ is neither
  under-sampled nor under-explored it is a.s. not pulled. In this **pathwise** form it needs *no
  decay hypothesis at all*: the conditioning event $\{\lnot\,\mathtt{aRTSFEUnder}\}$ is itself
  previous-history measurable (`measurableSet_shiftDown_aRTSFEUnder` — both $N_{m,k}$ and
  $\hat\rho_{m,k}$ are built from data before $m$), so the throttle applies inside the conditional
  expectation directly, and Step 3 is applied pathwise afterwards. This discharges `FEfed` with
  $E\equiv0$ for D-Tracking-type designs. (The earlier `not_pulled_of_sched_lt_of_alpha_zero`, which
  took a deterministic decay bound, is superseded by it.)

* **A worked schedule, $h(n)=n^{2/3}$** (`sched23`): it *is* an exploration schedule in the weakened
  sense (`isExplorationSchedule_sched23`), it satisfies the schedule-regularity hypothesis `hshift`
  (`sched23_shift`) and the $(\star)$ comparison $\sqrt{n\log\log n}=o(h(n))$ (`sched23_sqrt`,
  reducing to $\log\log n=o(n^{1/3})$) — and, the punchline, it **fails** the paper's condition (ii)
  (`not_isSqrtSmall_sched23`). So the whole hypothesis stack is satisfiable, and satisfiable
  *precisely in the regime the paper's definition excludes*.

* **Step 4, $\alpha>0$** — `throttled_count_div_sched_tendsto_zero`: the count of *throttled* pulls
  (arm $k$ selected while neither under-sampled nor under-explored) satisfies
  $\mathcal E_n/h(n)\to0$ a.s. Doob-decompose for the indicator `throttledIndicator`, built on
  $\{\lnot\,\mathtt{aRTSFEUnder}\,i\}$; `condExp_indicator` pulls that previous-history event out of
  the compensator, so the throttle applies with **no side condition** and bounds every term by
  $\alpha\hat\rho_{i,k}$, and `ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog` handles the
  martingale part. The compensator is compared against the **random** $\sum_i\alpha\hat\rho_{i,k}$,
  so `m₀`, `g`, `hgh`, `hdecay` all disappear; `hsum` and `hsqrt` ask only that the two pieces be
  $o(h)$ almost surely — which is what $(\star)$ delivers.

* **Step 2 → the decay input** — `aRTSTarget_le_loglog_of_quadratic`: composes a local quadratic
  bound on $T_k$ at $\Theta$ with the per-arm loglog rate to give
  $\hat\rho_{m,k}=O(\log\log m/L(m))$, where $L$ is any deterministic lower bound on the counts
  (forced exploration supplies $L\asymp h$ via Step 1).

  **A structural correction this exposed.** The LIL constant is *random*
  (`abs_estimator_sub_le_rate_loglog_N` reads `∀ᵐ ω, ∃ C', …`), so the decay bound cannot have a
  deterministic constant. The `hdecay` hypothesis must therefore be read **pathwise** — which is how
  `not_aRTSFEUnder_of_sched_lt` (Step 3) is stated, so Step 3 composes directly. But
  `not_pulled_of_sched_lt_of_alpha_zero` and `nonFE_count_div_sched_tendsto_zero` currently take
  `hdecay` with a *deterministic* `g`, which is too strong to be discharged this way. See item 1.

* **Final assembly** — `fEfed_of_decay`: given the decay pathwise (`ρ̂_{m,k} ≤ g(m) < h(m)/m`
  eventually, with `g` and the threshold allowed to depend on `ω`), the counter
  `E n = count (throttledIndicator …) n` has all three properties `aRTSFE_sparse_clt`'s `FEfed`
  requires — monotone, increasing by one at every non-FE pull (Step 3 turns such a pull into a
  *throttled* one), and `o(h)` (Step 4). So `FEfed` is discharged.

* **The quadratic bound from $C^2$** — `hquad` is no longer a hypothesis. Three pieces:

  * `exists_eventually_norm_sub_fderiv_le_mul_sq` (in `AlphaRAR/Mathlib/TaylorRemainder.lean`): a
    $C^2$ map has a first-order Taylor remainder $O(\|x-\theta\|^2)$ near $\theta$. **No Hessian is
    named**: being $C^2$ makes $\mathrm{D}f$ a $C^1$ map, hence locally Lipschitz
    (`ContDiffAt.exists_lipschitzOnWith`), which is exactly the input the pre-existing
    `norm_sub_fderiv_le_mul_sq` consumes. So this is a four-line corollary of machinery already in
    the repo, not a new mean-value argument.
  * `exists_eventually_sub_le_mul_sq_of_isLocalMin`: at a local minimum Fermat's theorem kills the
    linear term, leaving $f(x)-f(\theta)\le K\|x-\theta\|^2$.
  * `exists_aRTSTarget_le_mul_sum_sq`: for a **sparse** arm, $T(\Theta)_k=v_k=0$ while $T\ge0$
    (simplex-valued), so $\Theta$ is a *global* minimum of $x\mapsto T(x)_k$ — sparsity is precisely
    what supplies the minimum. Consistency $\hat\theta_m\to\Theta$ puts the plug-in point inside the
    neighbourhood eventually, and `sq_norm_le_sum_sq` converts the sup norm of
    $\mathcal A\to\mathbb R$ into the coordinatewise sum the per-arm rates plug into.

  `exists_aRTSTarget_le_loglog_of_contDiffAt` then chains this into
  `aRTSTarget_le_loglog_of_quadratic`, and even consistency is not assumed: it follows from `hrate`
  together with $\log\log m/L(m)\to0$, which $L\gtrsim h\to\infty$ already gives.

* **Closing the chain** — `exists_decay_of_contDiffAt`: $C^2$ smoothness plus $(\star)$ produce the
  `hdecay` input of `fEfed_of_decay` verbatim. The comparison step is
  `eventually_mul_loglog_div_lt_of_star`, which is stated **uniformly in the constant** — necessarily
  so, since the LIL constant is random. And `sched23_star` verifies $(\star)$ for $h(n)=n^{2/3}$
  ($n\log\log n/h(n)^2=\log\log n/n^{1/3}\to0$), so, with `not_isSqrtSmall_sched23`, the hypothesis
  is satisfiable exactly in the regime the paper's condition (ii) excludes.

* **The capstone** — `aRTSFE_sparse_clt_of_contDiffAt`: the conclusion of `cor:sparse_clt` with the
  forced-exploration-fed hypothesis *discharged*. Three pieces were needed:

  * `eventually_schedShift_le_pullCount` — the **deterministic floor** $L(n)=h(n-W(n))$ that forced
    exploration puts under *every* count, $W(n)=K\lceil h(n)\rceil+1$ being the catch-up window.
    Extracted from the lower half of `pullCount_div_sched_tendsto_one`, which now reuses it.
  * `exists_rate_loglog_of_pullCount_ge` — **the one non-mechanical step**. The subsampled LIL
    measures the error against the arm's *own random* count $N_{m,j}$; the decay step needs it
    against a deterministic $L(m)$. Both directions are used at once:
    $\log\log N_{m,j}/N_{m,j}\le\log\log m/L(m)$ because $N_{m,j}\le m$ shrinks the numerator while
    $L(m)\le N_{m,j}$ shrinks the denominator. This is why the bound runs through $\log\log m$ and
    not the more natural-looking $\log\log L(m)$. Per-arm constants are merged as $\sum_j|C_j|$.
  * the assembly itself: `ae_all_iff.mpr` over arms, `fEfed_of_decay` on each sparse one.

  Only $(\star)$ (as $m\log\log m=o(h(m)^2)$), $C^2$-ness of $T$ at $\Theta$, and the design's own
  throttle/compensator data are assumed; `hLtop`, `hL0`, `hLnn`, `hsqrt` and the $L$-version of
  $(\star)$ are all *derived* from $(\star)$ and `hshift`.

  There is no `FEfed` predicate any more. `aRTSFE_sparse_clt` takes an abstract arm split because it
  *assumes* the FE-fed property; once that property is proved, the split is pinned — an arm is
  sparse iff $T(\Theta)_a=0$ — so the capstone instantiates it at that predicate and `hTzero`
  disappears. What is left on the non-sparse side, `hpos` and `hprop`, is Condition **B**'s
  non-sparsity in its usual form.

* **`IsARTSFE`** — the design's requirements are a single history-level predicate, the `IsARTS`
  analogue for $\aRTSFE$, with two fields: *forced exploration takes priority* (if some arm is
  under-explored, arms outside $\mathbf S_m$ get probability zero) and *outside it the design is
  throttled* (the `IsARTS` condition with the extra premise $h(m)<N_{m,k}$, since forced exploration
  is allowed to override the throttle). Nothing about a process, measure or filtration appears, so
  it is checkable design by design.

  `throttle_of_isARTSFE` mirrors `throttle_of_isARTS`. `fe_of_isARTSFE` is the new one: it needs
  `ae_action_ne_of_selProb_nonpos` — "a previous-history event on which $p_{m,k}\le0$ is never a
  pull" — obtained by generalising the $\alpha=0$ argument away from `aRTSFEUnder` to an arbitrary
  $\mathcal F_{m-1}$-measurable event family, which now serves both. Note the Lean predicate
  *weakens* the paper's $p_{m+1,a}=1/|\mathbf S_m|$ to $a\notin\mathbf S_m\Rightarrow p_{m+1,a}=0$;
  uniformity on $\mathbf S_m$ is never used.
  `sched23_satisfies_schedule_hypotheses` records that $h(n)=n^{2/3}$ satisfies all three schedule
  hypotheses while failing the paper's condition (ii), so the theorem is not vacuous.
  `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.

* **The compensator bound is also derived** — `tendsto_sum_div_sched_of_loglog_decay`. $(\star)$ is
  exactly strong enough to *sum* the decay, which is not obvious a priori. Writing $(\star)$ as
  $h(i)>\sqrt{i\log\log i}$, the majorant telescopes into a square root,
  $$\frac{\log\log i}{h(i)}\;\le\;\frac{\log\log i}{\sqrt{i\log\log i}}\;=\;\frac{\sqrt{\log\log i}}{\sqrt i},$$
  so $\sum_{i<n}\hat\rho_{i,a}\lesssim\sqrt{\log\log n}\sum_{i<n}i^{-1/2}\le2\sqrt{n\log\log n}$ by the
  project's existing `sum_one_div_sqrt_le` — and $\sqrt{n\log\log n}=o(h(n))$ is $(\star)$ again. The
  initial segment, where the decay has not started, is a constant, killed by $h(n)\to\infty$.

  This also **fixed a latent bug**: as a hypothesis, $\sum_i\alpha\hat\rho_{i,a}=o(h(n))$ had been
  stated for *all* arms, but on a non-sparse arm $\hat\rho_{i,a}\to T(\Theta)_a>0$, so the sum grows
  like $n\gg h(n)$. It was therefore false whenever $\alpha>0$, making the theorem vacuous in that
  case. Deriving it confines the claim to the sparse arms, where it holds.

* **Condition **A** is a single hypothesis** — `memLp_feedback`. $\mathtt{hY2}$
  ($Y_n\in L^2(P)$) need not be assumed alongside $\mathtt{h\nu k}$ ($\mathrm{id}\in L^2(\nu_a)$
  for each arm): disintegrating against the response's conditional law $\nu(A_n)$,
  $$\int\|Y_n\|^2\,dP=\int_{\mathcal A}\Big(\int\|y\|^2\,d\nu_a\Big)\,d(P\circ A_n^{-1})(a)\ \le\ \max_a\int\|y\|^2\,d\nu_a<\infty,$$
  the maximum being finite because there are finitely many arms. The general step is
  `memLp_two_of_hasCondDistrib`; the two cases of $n$ mirror `condExp_feedback_comp`.

Remaining: nothing on this chain.

## 6. Summary

1. $h(n)=o(\sqrt n)$ is **not necessary**: under Condition **B**, forced exploration turns itself off
   (Proposition 1), so $h(n)=o(n)$ suffices for the whole non-sparse theory. This also legalises
   D-Tracking's own schedule.
2. $h(n)=o(\sqrt n)$ is **exactly the obstruction** to the sparse CLT: it puts the sparse arm in the
   targeting-dominated regime $N_{n,k}\asymp\sqrt n$, where the count is coupled to the estimator's
   own fluctuations and no deterministic normalizer is available.
3. Reversing the condition to $(\star)$ puts the sparse arm in the forced-exploration-dominated
   regime $N_{n,k}\sim h(n)$, which is deterministic — and the CLT follows from machinery that is
   already formalized.

The moral is that the schedule $h$ has two jobs, and the paper's condition optimises the wrong one:
$h$ small keeps forced exploration from disturbing the $\sqrt n$-asymptotics (unnecessary — it
switches off by itself), whereas $h$ **large** is what makes forced exploration, rather than the
data-dependent targeting rule, decide a sparse arm's sample size. Only the latter earns a CLT.
