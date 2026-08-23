# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
— without having to read (or trust) any of the 23k lines of Lean in `AlphaRAR/`, and with a
challenge import closure that bottoms out in **Mathlib alone** (as the
[Palomar registry](https://palomar-registry.org/) requires).

## The trust story

For each headline result there is a **challenge** file and a JSON config:

| result (`formalization.yaml`) | challenge | config |
|---|---|---|
| `AlphaRAR.aRTS_LLN` | `Challenge_aRTS_LLN.lean` | `aRTS_LLN.json` |
| `AlphaRAR.aRTS_clt_joint` | `Challenge_aRTS_clt_joint.lean` (+ `_Defs.lean`) | `aRTS_clt_joint.json` |
| `AlphaRAR.aRTS_prop_dev` | `Challenge_aRTS_prop_dev.lean` | `aRTS_prop_dev.json` |
| `AlphaRAR.aRTS_prop_dev_ae` | `Challenge_aRTS_prop_dev_ae.lean` | `aRTS_prop_dev_ae.json` |
| `AlphaRAR.aRTSFE_sparse_clt_of_contDiffAt` | `Challenge_aRTSFE_sparse_clt_of_contDiffAt.lean` | `aRTSFE_sparse_clt_of_contDiffAt.json` |
| `AlphaRAR.aRTSFE_sparse_rate_of_isARTSFE` | `Challenge_aRTSFE_sparse_rate.lean` | `aRTSFE_sparse_rate.json` |

Each challenge is a short, self-contained file: it states the theorem with `sorry`, with every
project definition the statement depends on **inlined verbatim**. The handful of declarations the
statements rest on from [LML](https://github.com/LeanMachineLearning/LML) — `Algorithm`,
`Environment`, `history`, `IsAlgEnvSeq`, `stationaryEnv`/`obliviousEnv`, `pullCount`,
`pullCount'`, `sumRewards'` — are vendored verbatim into the three `ChallengeVendor_*.lean`
modules, which import only Mathlib. So the transitive imports of every challenge resolve to
Mathlib (and Lean core) and nothing else; the `ChallengeVendor_*` files are part of the challenge
and are read the same way. The `sorry`s in these files are the point: they are restatements to be
verified, not part of the formalization, and are not counted in `formalization.yaml`'s
`sorry_count`.

`Solution.lean` is the other side: it just imports the project modules that prove the results.

A skeptical reader therefore only has to
1. read the challenge file (a couple of hundred lines) and the three vendor files (once, ~200
   lines total) against the paper's statement, trusting only Mathlib for the imported notions, and
2. run comparator on the corresponding config.

If comparator succeeds, every theorem in the config's `theorem_names` is guaranteed to
1. be proved in this project **with exactly the challenged statement** (comparator checks that
   every constant in the statement's transitive closure — the inlined definitions and the
   vendored LML declarations included, down to auxiliary `_proof_*` constants — is *identical*
   between the challenge and the project),
2. use no axioms beyond `propext`, `Classical.choice`, `Quot.sound`, and
3. be accepted by the Lean kernel, replayed from a `lean4export` dump inside a sandbox.

In particular the vendored copies cannot silently drift from upstream LML: comparator compares
them constant-for-constant against the LML package the project is built with.

Two configs list an auxiliary measurability lemma as a second target
(`AlphaRAR.measurable_jointSqrtNVec`, `AlphaRAR.measurable_estimatorErrorVec`): the CLT statements
mention these lemmas, because a `ProbabilityMeasure` bundles the pushforward measure with a proof.
Listing them as targets makes comparator verify their statements and proofs the same way, while
the challenge files leave them `sorry`.

The sparse-rate challenge states `AlphaRAR.aRTSFE_sparse_rate_of_isARTSFE`, blueprint
`thm:sparse_rate` from the history-level design predicate `IsARTSFE` (the same packaging as the
other headline results). The raw process-level form `AlphaRAR.aRTSFE_sparse_rate` says the same
thing but its throttle hypothesis mentions LML's history filtration `IsAlgEnvSeq.filtration`,
whose definition rests on a *module-private* auxiliary constant that no restatement outside LML
can reproduce — so that form cannot be challenged under a Mathlib-only import closure.

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
standalone extraction (`referee collect` + `referee extract`, the same pipeline CI uses for the
referee site; the files land in `<output>/html-multi/extracted/AlphaRAR___<name>.lean`), then
adjusted by hand where comparator's exact-identity check requires reproducing the original
elaboration:

- **LML imports are replaced by the `ChallengeVendor_*` imports** (extraction imports the
  external dependency frontier, which includes LML; Palomar's Mathlib-only closure does not).
  Each vendor file mirrors one original module — its declarations verbatim and in order, its
  Mathlib import surface, and `module`-mode elaboration — because auxiliary `_proof_*` constants,
  autoParam constants and instance paths are only reproduced under the original module's
  elaboration conditions.
- **`Challenge_aRTS_clt_joint` is split in two modules.** `AlphaRAR.propSqrtNVec` and
  `AlphaRAR.targetSqrtNVec` embed the *same* auxiliary proof term; elaborated in one module, the
  second definition reuses the first's `_proof_1` constant, whereas in the project each module
  minted its own. `_Defs.lean` mirrors the original module boundary
  (`PluginTargetCLT` vs `JointCLT`) so the auxiliary constants come out with the project's names.
- **Watch for module-private auxiliary constants** (name scheme `_private.<module>.0.<decl>…`,
  e.g. minted by `grind` inside a definition): their names embed the defining module's name, so
  no vendored copy can reproduce them. If one enters a statement's closure, the statement itself
  has to be reformulated to avoid the offending definition — that is why the sparse-rate
  challenge targets the `IsARTSFE` form (see above).

If a headline statement (or a definition it rests on) changes, comparator fails with
`Const does not match …` — regenerate the affected challenge from a fresh extraction and re-apply
the adjustments above. When adding a challenge module, add it to the `Comparator` library's
`globs` in `lakefile.toml` — never as a root, and never as its own library (see *Repository
wiring*; plain `lake exe mk_all --check` must also stay restricted to `--lib AlphaRAR`, since the
glob modules have no module directory).
