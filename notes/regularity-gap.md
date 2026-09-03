# A gap in Lemma `lem:componentwise`: the missing regularity hypothesis

**Verified against the paper** (`arxiv/sections/`), not only the blueprint.

**Summary.** Lemma `lem:componentwise` as stated is false: sampling every treatment infinitely
often does *not* imply the componentwise CLT. The proof in `appendixA.tex` verifies the Lindeberg
condition but then invokes "the martingale CLT theorem" for a *randomly normalized* martingale,
which requires a stabilization hypothesis that is never established. The non-sparse results are
recoverable (the missing hypothesis holds there for free); `corr:componentwise` — the sparse
corollary — is the one genuinely affected.

---

## 1. What the paper claims

`proof_sketch_emilie.tex:65`:

> **Lemma (Joint CLT with Componentwise Scaling).** Consider a RAR procedure under which
> $N_{n,k}\to\infty$ a.s. for all $k \in [K]$, then we have
> $$D_n(\hat\Theta_n-\Theta)\xrightarrow{\mathcal{D}}\mathcal N\!\big(0,\mathrm{diag}(V_1,\dots,V_K)\big),
> \qquad D_n:=\mathrm{diag}(\sqrt{N_{n,1}},\dots,\sqrt{N_{n,K}}).$$

This is not incidental — it is highlighted as a feature (`proof_sketch_emilie.tex:98`):

> "We emphasize that one component of the proof, Lemma \ref{lem:componentwise}, **only requires that
> each treatment is sampled infinitely often**."

and `corr:componentwise` (`forced_exploration.tex:90`) — the sparse CLT for $\alpha$RTS-FE — is
introduced as "a **direct consequence** of Lemma \ref{lem:componentwise}", with no separate proof in
`appendixB.tex`.

## 2. The exact step where the gap opens

`appendixA.tex`, proof of the lemma. **Step 1** (martingale, $\langle M_{\cdot,k}\rangle_n = V_kN_{n,k}$,
zero cross-variation) is correct. **Step 2** verifies the *self-normalized* Lindeberg condition

$$L_{n,k}(\varepsilon):=\frac{1}{\langle M_{\cdot,k}\rangle_n}\sum_{i=1}^n\mathbb E\Big[(\Delta M_{i,k})^2\mathbf 1_{\{|\Delta M_{i,k}|>\varepsilon\sqrt{\langle M_{\cdot,k}\rangle_n}\}}\ \Big|\ \mathcal F_{i-1}\Big]\ \overset{\mathbb P}{\longrightarrow}\ 0,$$

and then concludes (`appendixA.tex:~372`):

> "Therefore, the Lindeberg condition is verified, and **by the martingale CLT theorem**, we have
> $\frac{M_n}{\sqrt{\langle M \rangle_n}}\overset{\mathcal{D}}{\longrightarrow}\mathcal{N}(0,I_K)$."

**That implication is the gap.** No theorem is cited, and none of the standard ones applies:

* Hall–Heyde (Thm 3.2 / Cor 3.1) and every martingale CLT of that family normalize by a
  **deterministic** sequence $s_n$ and require $\langle M\rangle_n/s_n^2\to^{\mathbb P}\eta^2$.
  Random norming by $\sqrt{\langle M\rangle_n}$ is then legitimate via **stable** convergence, which
  divides out $\eta$ — but the stabilization hypothesis is still needed (η may be random; it may not
  be absent).
* The same is visible in this project's own formalized `thm:mart_clt`, whose `σ2` is a deterministic
  constant:

```lean
theorem mart_clt [IsProbabilityMeasure P] {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (hV : TendstoInMeasure P (fun n ↦ A.predVar n) atTop (fun _ ↦ σ2))   -- σ2 deterministic
    (hLindeberg : ∀ ε, 0 < ε → TendstoInMeasure P (fun n ↦ A.lindeberg n ε) atTop 0) : ...
```

The diagnosis in one line: **there is a CLT along the quadratic-variation clock, not at deterministic
times with random normalization.** For a continuous martingale, Dambis–Dubins–Schwarz gives
$M_t=B_{\langle M\rangle_t}$, so stopping when $\langle M\rangle$ *reaches a fixed level* gives
$\mathcal N(0,1)$; evaluating at a fixed time $n$, where $\langle M\rangle_n$ has been steered
adaptively, does not. The two coincide exactly when $\langle M\rangle_n$ is regular relative to a
deterministic scale.

## 3. A counterexample

Two arms; arm 1 has $\xi_i\sim\mathcal N(\theta,V)$ i.i.d. (Condition **A** holds). Write $S_m$ for
the sum of the first $m$ centred responses of arm 1. Let $a_{j+1}=2^{a_j}$ be deterministic blocks.

> **In block $j$** (rounds $[a_j,a_{j+1})$): pull arm 1 until the running statistic
> $S_m/\sqrt{Vm}$ first exceeds $1$; then park on arm 2 for the rest of the block.

This is an adapted allocation rule, so a legitimate RAR procedure. Both arms are pulled infinitely
often, so the lemma's hypothesis holds; the Step-2 Lindeberg condition also holds (i.i.d. increments
with finite variance and $N_{n,1}\to\infty$).

By the law of the iterated logarithm $\limsup_m S_m/\sqrt{Vm}=+\infty$ a.s., so crossings of level
$1$ occur infinitely often a.s.; since the blocks grow astronomically, $\mathbb P(\text{a crossing
occurs in block } j)\to 1$. On that event, throughout the parking stretch the arm-1 martingale is
**frozen**:

$$\frac{M_{n,1}}{\sqrt{\langle M_{\cdot,1}\rangle_n}}=\frac{S_{M}}{\sqrt{VM}}>1 .$$

Evaluating at the *deterministic* times $n_j:=a_{j+1}-1$,

$$\mathbb P\Big(M_{n_j,1}/\sqrt{\langle M_{\cdot,1}\rangle_{n_j}}>1\Big)\longrightarrow 1
\ \neq\ \mathbb P(Z>1)\approx 0.159 .$$

So there is no $\mathcal N(0,1)$ limit. Adaptive pausing just after a level crossing freezes the
self-normalized martingale at an atypical value — and $N_{n,k}\to\infty$ does nothing to prevent it.

Equivalently, and perhaps more familiar: $Q_{n,k}=S_{N_{n,k}}$ is an i.i.d. sum at a random,
adaptively chosen index. That is Anscombe/Rényi territory, and both classical theorems **require**
$N_n/c_n\to\eta>0$; there is no version assuming only $N_n\to\infty$.

## 4. Scope

| Result | Affected? | Why |
|---|---|---|
| `thm:LLN`, `thm:normality-gen-erade`, `thm:forced` | **No** | applied where $N_{n,k}/n\to v_k>0$, which supplies the missing hypothesis with $c_{k,n}=v_kn$ |
| `thm:sparse-rate` | **No** | proved via LLN + LIL (`appendixB.tex:49`), no CLT involved |
| `corr:componentwise` + `cor:sparse-clt` (Section 4) | **Yes** | stated as a "direct consequence" of the lemma, in exactly the regime where the hypothesis is unavailable |
| `lem:pearson` (Appendix B, $\chi^2$ test) | **Inherited** | invokes the lemma for "any $\alpha$RTS-FE design", hence in the sparse regime too |

So the *statements* of the non-sparse theorems stand; only the lemma's proof needs its hypothesis
strengthened, with each non-sparse application discharging it from $v_k>0$.

## 5. A minor separate typo

`appendixA.tex`, end of Step 2:

> "So $\mathbb{P}\left(L_{n,k}(\epsilon) \leq \eta\right) \leq \mathbb{P}\left(N_{n,k} \leq m\right) \to 0$"

The inequality is inverted — as written it asserts that $L_{n,k}$ is *not* small. It should read
$\mathbb P(L_{n,k}(\varepsilon)>\eta)\le\mathbb P(N_{n,k}<m)\to0$. The intent is clear and the step
is fine.

(Also worth a footnote: the truncation level $\varepsilon\sqrt{V_k}\sqrt{N_{n,k}}$ is not
$\mathcal F_{i-1}$-measurable, since $N_{n,k}$ depends on rounds after $i-1$. Passing to the event
$\{N_{n,k}\ge m\}$ with deterministic $m$ is what repairs this, and the proof does do that.)

## 6. What the formalization does instead

`lem:componentwise` was restated with the hypothesis the proof actually needs —

> for every $k$ there is a deterministic $c_{k,n}\to\infty$ with $N_{n,k}/c_{k,n}\to1$ a.s.

— and proved in that form: `AlphaRAR.estimatorError_joint_tendsto_multivariateGaussian`
(`AlphaRAR/YDK2026/ResponseCLTJoint.lean`). It is stated with **per-arm** deterministic
normalizers and covers both regimes as instances:

* $c_{k,n}=n$, $\rho=v>0$ → the non-sparse result (recovers Lemma 1 of `hu2006asymptotically`);
* per-arm $c_{k,n}$, $\rho\equiv1$ → the **sparse** conclusion, needing no positivity, i.e. exactly
  the statement of `corr:componentwise`.

The enabling device is that the weighted martingale array `AlphaRAR.wArray` carries **row-dependent**
weights $w^{(n)}_k=w_k/\sqrt{c_{k,n}}$, so one array covers a common normalizer and per-arm ones
alike. Cramér–Wold still applies because the arm indicators are disjoint, so a linear combination —
*even with a different normalizer per arm* — is again a single martingale-difference array. (The
Anscombe route does **not** jointify: a linear combination of random-time sums is not a random-time
sum. The Anscombe machinery is formalized too, for the per-arm statements:
`AlphaRAR.tendstoInDistribution_anscombe_iid`, `AlphaRAR.respMart_selfNorm_anscombe_tendsto`,
`AlphaRAR.estimator_sqrtN_anscombe_tendsto`.)

## 7. Closing it: what is now proved, and what stays open

### 7.1 Proved — forced exploration supplies the regularity for the arms it feeds

`AlphaRAR.pullCount_div_sched_tendsto_one` (`ForcedExploration.lean`): if arm $k$ is eventually fed
*only* by the forced-exploration mechanism, then

$$\frac{N_{n,k}}{h(n)}\longrightarrow 1 ,$$

i.e. the regularity holds with the **deterministic schedule itself** as $c_{k,n}$. Two-sided bound:

* **Upper** (`pullCount_le_sched_of_fe_except`): at a forced-exploration round the selected arm is
  itself under-explored, so a pull leaves it at $h(m)+1\le h(n)+1$; other rounds do not move it.
* **Lower** (`pullCount_ge_min_sched_of_fe`): the selected arm is a *least-sampled* under-explored
  arm, hence at the global minimum, so the potential $D(m)=\sum_j(L-N_{m,j})^+$ drops by exactly one
  per round while the minimum stays below $L$. As $D\le KL$, that persists at most $KL$ rounds — so
  in any longer window either the minimum reached $L$, or forced exploration stopped firing, which
  already means every count exceeds $h$. Same potential-function device as `lem:fe_no_starvation`.

A mild regularity of $h$ is assumed (shifting the argument by the $O(h(n))$ catch-up window does not
change $h$ to first order); $h(n)=(n^{1/3}-K/2)^+$ satisfies it.

`AlphaRAR.aRTSFE_sparse_clt` then delivers $D_n(\hat\Theta_n-\Theta)\Rightarrow\mathcal
N(0,\mathrm{diag}(V_k))$, splitting arms by a predicate `FEfed` and using the per-arm normalizer
$c_{k,n}=h(n)$ (FE-fed) or $v_kn$ (positive proportion). **The split is unavoidable**: not every arm
can be FE-fed, since $\sum_kN_{n,k}=n$ while $Kh(n)=o(\sqrt n)$.

### 7.2 Open — target-chasing designs

The FE-fed hypothesis is a real restriction. Since $T\ge0$ and $T(\Theta)_k=0$, the point $\Theta$
*minimises* $T_k$, so $\nabla T_k(\Theta)=0$ and $T(\hat\Theta_n)_k=O(\|\hat\Theta_n-\Theta\|^2)$.
A design that chases its target therefore gives arm $k$ about

$$N_{n,k}\ \approx\ n\,T(\hat\Theta_n)_k\ \asymp\ \frac{n}{N_{n,k}}
\qquad\Longrightarrow\qquad N_{n,k}\asymp\sqrt n ,$$

which **dominates** $h(n)=o(\sqrt n)$. So for such designs — including the paper's distance-based
example, where $\delta_{m,k}=(\hat\rho_{m,k}-N_{m,k}/m)^+>0$ keeps feeding arm $k$ — forced
exploration does *not* set the scale, and $N_{n,k}/h(n)\to1$ is false.

Whether $N_{n,k}/\sqrt n$ converges there is delicate: the sampling rate is driven by the
estimator's own squared error, so the sampling and the martingale are coupled. Note the feedback is
*stabilising* (a large error triggers more sampling, which shrinks the error), unlike the
adversarial pausing of §3 — so this is not obviously a counterexample either. By §3 the conclusion
cannot be obtained from $N_{n,k}\to\infty$ alone, so the case is genuinely open.

Note this is exactly the regime in which the condition $h(n)=o(\sqrt n)$ — imposed so that forced
exploration does not disturb the $\sqrt n$-CLT — simultaneously guarantees that forced exploration
cannot rescue the sparse CLT. The two roles of $h$ pull in opposite directions.
