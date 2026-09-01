# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
— without having to read (or trust) any of the 23k lines of Lean in `AlphaRAR/`.

Each challenge is **one self-contained file whose transitive imports resolve to Mathlib and Lean
core only**. That exact shape is what the [Palomar registry](https://palomar-registry.org/)'s
mechanical verification enforces: it compiles the challenge file standalone (plain `lean`, with a
search path containing nothing but the toolchain and the allowlisted Mathlib closure), so the
challenge can import no LML, no project modules, and no sibling helper modules.

## The trust story

For each headline result there is a **challenge** file and a JSON config:

| result (`formalization.yaml`) | challenge | config |
|---|---|---|
| `AlphaRAR.aRTS_LLN` | `Challenge_aRTS_LLN.lean` | `aRTS_LLN.json` |
| `AlphaRAR.aRTS_clt_joint` | `Challenge_aRTS_clt_joint.lean` | `aRTS_clt_joint.json` |
| `AlphaRAR.aRTS_prop_dev` | `Challenge_aRTS_prop_dev.lean` | `aRTS_prop_dev.json` |
| `AlphaRAR.aRTS_prop_dev_ae` | `Challenge_aRTS_prop_dev_ae.lean` | `aRTS_prop_dev_ae.json` |
| `AlphaRAR.aRTSFE_sparse_clt_of_contDiffAt` | `Challenge_aRTSFE_sparse_clt_of_contDiffAt.lean` | `aRTSFE_sparse_clt_of_contDiffAt.json` |
| `AlphaRAR.aRTSFE_sparse_rate_of_isARTSFE` | `Challenge_aRTSFE_sparse_rate.lean` | `aRTSFE_sparse_rate.json` |

Each challenge (320–390 lines) states the theorem with `sorry`, with **every** definition the
statement rests on inlined verbatim: the project's definitions, and the handful of
[LML](https://github.com/LeanMachineLearning/LML) declarations they build on (`Algorithm`,
`Environment`, `history`, `IsAlgEnvSeq`, `stationaryEnv`/`obliviousEnv`, `pullCount`,
`pullCount'`, `sumRewards'`), which appear as clearly marked "vendored from LML" sections. The
`sorry`s in these files are the point: they are restatements to be verified, not part of the
formalization, and are excluded from `formalization.yaml`'s `sorry_count` (as the v0.4 spec
prescribes).

`Solution.lean` is the other side: it just imports the project modules that prove the results.

A skeptical reader therefore only has to
1. read the one challenge file against the paper's statement, trusting only Mathlib for the
   imported notions, and
2. run comparator on the corresponding config.

If comparator succeeds, every theorem in the config's `theorem_names` is guaranteed to
1. be proved in this project **with exactly the challenged statement** (comparator checks that
   every constant in the statement's transitive closure — the inlined project definitions and
   the vendored LML declarations included, down to auxiliary `_proof_*` constants — is
   *identical* between the challenge and the project),
2. use no axioms beyond `propext`, `Classical.choice`, `Quot.sound`, and
3. be accepted by the Lean kernel, replayed from a `lean4export` dump inside a sandbox.

In particular the vendored LML sections cannot silently drift from upstream: comparator compares
them constant-for-constant against the LML package the project is built with.

Two configs list an auxiliary measurability lemma as a second target
(`AlphaRAR.measurable_jointSqrtNVec`, `AlphaRAR.measurable_estimatorErrorVec`): the CLT statements
mention these lemmas, because a `ProbabilityMeasure` bundles the pushforward measure with a proof.
Listing them as targets makes comparator verify their statements and proofs the same way, while
the challenge files leave them `sorry`.

The sparse-rate challenge states `AlphaRAR.aRTSFE_sparse_rate_of_isARTSFE`, blueprint
`thm:sparse_rate` from the history-level design predicate `IsARTSFE` (the same packaging as the
other headline results). That packaging is what makes the statement challengeable at all: a form
taking the process-level throttle as a hypothesis would mention LML's history filtration
`IsAlgEnvSeq.filtration`, whose definition rests on a *module-private* auxiliary constant (see
*Maintenance*) that no restatement outside LML can reproduce — so such a form cannot be challenged
under a Mathlib-only import closure. Every αRTS-FE result therefore states its design hypothesis
as `IsARTSFE` rather than as a throttle.

## Running it

```bash
scripts/comparator-verify.sh                 # all six configs
scripts/comparator-verify.sh aRTS_LLN        # one config
scripts/comparator-verify.sh --insecure ...  # without a landrun sandbox (see below)
```

The script clones and builds comparator and `lean4export` (pinned revision, project toolchain)
into `~/.cache/alpha-rar/comparator-tools`, then runs each config from the repository root as

```bash
lake env path/to/comparator comparator/<name>.json
```

Comparator's sandboxing needs [landrun](https://github.com/Zouuup/landrun) (built from its `main`
branch) in `PATH`. `--insecure` substitutes comparator's no-op development shim: the mathematical
checks are identical, but an adversarial repository could then attack your machine or the checker
during the build, so only use it on a repository you already trust — e.g. as a freshness check of
your own tree, which is what CI does. For the full guarantee against a hostile repository, run it
from a *fresh* checkout (never build the repo first: comparator must be the first thing that
elaborates the challenge), with real landrun, wrapped as comparator's README recommends:

```bash
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- bash -c 'scripts/comparator-verify.sh'
```

## Repository wiring

All comparator modules form the single `Comparator` lake library, whose **root** is the stub
`Comparator.lean` and whose real modules are `globs`. This is deliberate: `checkdecls` and referee
import every *root* of every library in the workspace, and the challenge modules redeclare
project and LML names, so they must never be roots. CI builds the library (so the challenges keep
compiling and the stub's olean exists when `checkdecls` runs) but never imports the challenges
together with `AlphaRAR`.

## Maintenance

The challenge files are generated by [Referee](https://github.com/LeanMachineLearning/exposition)'s
standalone extraction (`referee collect` + `referee extract`; the files land in
`<output>/html-multi/extracted/AlphaRAR___<name>.lean`), then post-processed: the LML imports of
the extraction's frontier are removed, `Mathlib.Probability.HasCondDistrib`, `…HasLaw` and
`…Martingale.BorelCantelli` are added, and the "vendored from LML" sections are spliced in after
the namespace stubs (the same block in every challenge — declarations copied verbatim from LML,
in original order).

Comparator's exact-identity check makes elaboration details load-bearing; the rules learned here:

- **One module, one owner for shared auxiliary proofs.** Identical embedded proof terms are
  deduplicated per module: the first declaration mints `<name>._proof_N`, later ones in the same
  module reuse it, but the same definitions split across two modules each mint their own. A
  single-file challenge can only reproduce the *one-module* pattern — which is why
  `propSqrtNVec`, `targetSqrtNVec` and `jointSqrtNVec` are deliberately defined together (and in
  that order) in `AlphaRAR/YDK2026/PluginTargetCLT.lean`; see the comment there. If a challenge
  fails with `Const does not match` on a `_proof_*`-bearing definition, check whether the
  project mints the constant under the name the single-file elaboration would choose.
- **Module-private auxiliary constants are fatal** (name scheme `_private.<module>.0.<decl>…`,
  e.g. minted by `grind` inside a definition): their names embed the defining module's name, so
  no restatement can reproduce them. If one enters a statement's closure, the statement itself
  has to avoid the offending definition — that is why the sparse-rate challenge targets the
  `IsARTSFE` form (see above).
- **Statements that mention lemmas** (e.g. through a `ProbabilityMeasure` subtype) get those
  lemmas listed as extra `theorem_names` targets, `sorry`d in the challenge.

If a headline statement (or a definition it rests on) changes, comparator fails with
`Const does not match …` — regenerate the affected challenge from a fresh extraction and re-apply
the post-processing. When adding a challenge module, add it to the `Comparator` library's `globs`
in `lakefile.toml` — never as a root, and never as its own library (see *Repository wiring*;
plain `lake exe mk_all --check` must also stay restricted to `--lib AlphaRAR`, since the glob
modules have no module directory). To pre-check Palomar's standalone compile locally, run `lean`
on the challenge with `LEAN_PATH` restricted to the Mathlib-closure packages under
`.lake/packages` — no LML, no `.lake/build`.
