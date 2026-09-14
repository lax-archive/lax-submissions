# lax/ — the book *Transducers* as Lax submissions

Read `PLAN.md` (what is being built, Jan's decisions) and `CAMPAIGN.md` (where
each submission stands, the next leaf) before doing anything. This file is
the working method; it applies to every session and every subagent.

## The shape

One folder per submission (eight: `pcp-undecidability`, `mealy-machines`,
`rational-functions`, `regular-functions`, `mso-transductions`,
`regular-combinators`, `polyregular-functions`, `transducers-book`), each a
`lax init` scaffold with its id bound to an archive issue. Ids stay as they
are (six-digit); the package names embed them (`Lax765601`, `Lax765601Proofs`).

- `concepts/LaxN/*.lean` — written fresh, one module per reviewable idea, in
  the register of the archive's flagship submissions (`~/git/lax-submissions/README.md`
  §4): paper-level description, `# Formalization notes`, docstring on every
  declaration, zero axioms in a definition-concept, exactly one in a
  theorem-concept. Everything declared lives under `LaxN.<Module>`.
- `proofs/LaxNProofs/Source/<Part>/<File>.lean` — the source development
  `../transducer-lean/RequestProject/` copied **verbatim** by `tools/port.py`
  (imports and root namespaces rewritten; `Transducers` → `LaxNProofs.Transducers`).
  Never hand-edit a Source file except to fix a compile error against the
  epoch mathlib, and record every such edit in `CAMPAIGN.md`.
- `proofs/LaxNProofs/Bridge.lean` — each concept definition proved equal or
  equivalent to its source counterpart (`toSrc`/`ofSrc` for structures,
  `compClosure_iff` for the inductive closure, `Iff.rfl` where definitions
  unfold identically).
- `proofs/LaxNProofs/Results.lean` — the numbered results, one `theorem` per
  concept axiom with `conclusion:` frontmatter, a summary, `# Proof strategy`
  and `# Attribution` (book section + Aristotle), each a few lines through the
  bridge. A headline biconditional is glued from its two half-concepts *as
  assumptions* (see `aperiodic_iff_compClosure_flipFlop`).
- Root modules list every module of the package, one import per line, nothing
  else (regenerate with `find`, see the commands below).

`../transducer-lean/` is a read-only mirror of Aristotle's server. Never edit
it.

## Commands

    cd <submission>/concepts && lake build          # fast iteration
    cd <submission>/proofs   && lake build
    lax submit <submission> --force --allow-dirty   # submits committed, pushed HEAD as a draft,
                                                    # no local checks: the archive is the verdict
    lax sync                                        # then read ~/.lax/lax-database/lax-N/build-output.json

`lax build --replay <submission>` runs the archive's checks locally (clones and
builds every pinned dependency from source, 30–60 min). Run it when it tells you
something the archive would not tell you faster (a first submission of a large
proof package: the archive caps the kernel replay at 20 min of `leanchecker`
with 2 threads, and Part D hit that cap); skip it when it is plainly redundant
(a repin-only resubmit). Jan, 2026-09-07.

`lake` is `~/.elan/bin/lake`; builds read mathlib from the warm store, nothing
is downloaded. Porting a part:

    python3 tools/port.py --pkg LaxNProofs --dest <submission>/proofs \
        --dep LaxMProofs=<dep-submission>/proofs  <Part>/<File> ...

`--dep` resolves `import RequestProject.X` against the dependency's
`ported.txt` (at the submission root); `--provided X/Y` declares a module you wrote by hand
(`Source/PartB/PCPRed.lean` in S0 is the pattern: the few definitions a file
needs from a later part, copied on their own).

Regenerate a root module:

    (cd LaxNProofs && find . -name '*.lean' | sed 's|^\./||; s|\.lean$||; s|/|.|g' | sort | sed 's/^/import LaxNProofs./') > LaxNProofs.lean

## Cross-submission requires

Concept packages of later parts require the concept packages of earlier parts;
proof packages require the earlier proof packages too (the source development
of Part B uses the Mealy API of Part A). A require pins `(git, rev, subDir)` of
the dependency's **current archive record** (`lax sync`; `~/.lax/lax-database/lax-N/record.json`),
so a dependency is submitted as a draft before a dependent pins it, and every
re-submission of a dependency means repinning and resubmitting the dependents.
For the local loop, `~/git/lax-submissions/.claude/sibling-overrides.sh` shows
how to redirect pins to sibling folders with Lake package overrides; adapt it
here when the chain is long enough to hurt.

## Gotchas met so far

- The archive builds with `autoImplicit = false`; the source relied on it in a
  few Part B files (`PairWeighted.lean`: `K`). Add the binders.
- mathlib drift at the epoch: `Primrec.list_take`/`list_drop` now exist with
  flipped argument order (rename ours to `list_take'`/`list_drop'`), some
  `rw` on set-builder terms need the `Language A` ascription or `change`,
  `List.map Subtype.val` vs `List.unattach` normal forms in `CodeRat.lean`,
  a `generalize` in `PrimrecArith.lean` after `decode_ratSig`. `push_neg` is
  deprecated (warning only).
- Dot notation on a concept type does not work from a proof module (the prefix
  rule forbids declaring into `LaxN.*`), which is why Source keeps its own
  copies of the types and the bridge transports.
- A shared inductive type (S0's `Sym`) can be aliased in Source as an
  `abbrev` plus `@[match_pattern] abbrev` constructors, so that the source's
  pattern matches keep working on the concept's type.
- Every root-level namespace of a Source file must carry the package prefix
  (the archive checks it on every declaration, `lax build --replay` reports
  `statements · namespace`). `port.py` now rewrites all of them; a source
  file that `open`s a mathlib namespace of the same name as a rewritten one
  (`Primrec`) needs the `open` moved to the top level, before the namespace.
- Never `lake update` inside a submission: it clones mathlib and friends into
  `.lake/packages` (7.5 GB). mathlib is reached through the gitignored
  `.lake/package-overrides.json` that `lax build` writes (path entries into
  `~/.lax/warm/`); for a fresh proof package before its first `lax build`,
  copy that file from a sibling. To add or repin a git-pinned Lax package,
  `lake update <LaxDep> …` names only those packages, but it still clones
  mathlib and friends into `.lake/packages` next to them (overrides or not):
  delete those nine folders afterwards (`aesop batteries Cli importGraph
  LeanSearchClient mathlib plausible proofwidgets Qq`), the build resolves
  them through the overrides.
- Disk is tight on this machine (~10 GB). Build one submission at a time;
  `.lake/build` of a full part is 1–3 GB.

## Working rhythm

Land at every boundary: commit the submission folder (never `build-output.json`,
`lake-manifest.json`, `.lake/`), push, `lax submit --force --allow-dirty`, `lax
sync`, update `CAMPAIGN.md`. Subagents get one coherent leaf (one part's Source
port, or one part's concepts, or one bridge), narrow file ownership, and the
gate that decides it: `lake build` green (against sibling folders through
`.lake/package-overrides.json` while the pins are not yet on the archive), or
`lax build --replay` green for a large first submission. The supervisor
reviews the concrete result before landing.
