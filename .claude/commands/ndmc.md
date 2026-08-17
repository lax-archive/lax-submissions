---
description: Run the ND-MC formalization supervisor loop — pick ready leaves, dispatch a wave of subagents, gate, land, repeat until the ledger is complete
argument-hint: "[leaf-id | --wave N | --status]"
---

# /ndmc — the ND-MC formalization supervisor

You are the **supervisor**. You do not write proofs. You select leaves,
dispatch subagents, review what comes back, run the gates, land it, and
record it. Then you do it again, **without stopping to ask**, until the
ledger says the campaign is complete or a leaf is genuinely blocked.

Jan has authorized this loop to run unattended. Landing reviewed work onto
`main` at every boundary is standing policy (`CLAUDE.md`), so an ordinary
completed boundary is **not** an occasion to ask permission. Ask only for
the three things listed under **Stop conditions**.

## The two files that are the state

- `plans/nowhere-dense-model-checking/execution-plan.md` — **static**. The
  leaf DAG: for each leaf, its id, what it proves, the file it owns, its
  dependencies, its source pin, its gates, and its done criterion. Change
  it only when a leaf's *content* is found to be wrong.
- `plans/nowhere-dense-model-checking/execution-ledger.md` — **mutable**.
  One row per leaf: status, wave, commit, note. This is the campaign's
  memory. It must be accurate after every boundary, because a compacted
  context or a new session recovers everything from it and from `git log`.

If `$ARGUMENTS` is `--status`, print the ledger's open rows and stop.
If `$ARGUMENTS` names a leaf id, run just that leaf and stop after landing it.
Otherwise run the full loop below.

## The loop

Repeat until **done**:

**1. Select.** Read the ledger. A leaf is *ready* when its status is `ready`
and every dependency is `done`. Take all ready leaves that own **disjoint
files** — that is the only parallelism rule. Do not cap the wave at a fixed
number; cap it at what you can actually review. Two leaves that touch the
same file are sequential, whatever the DAG says.

If nothing is ready and something is `blocked`, go to **Stop conditions**.
If nothing is ready and nothing is blocked, the campaign is **done**.

**2. Seed.** One worktree per wave, from the main checkout:

```
git worktree add .claude/worktrees/<wave> -b worktree-<wave> main
.claude/worktree-seed.sh
```

Always name `main` explicitly. Run the seed with no arguments, once,
before any build or any lean-lsp call. Never run a cold `lake build` in an
unseeded worktree. If a package was never built in `main`, run
`lax build --only proofs nowhere-dense-model-checking` once instead.

**3. Dispatch.** One `Agent` subagent per leaf, all in a single message so
they run concurrently. **Never use the `Workflow` tool** — it needs Jan's
permission on every call, and this loop must not need him. Each subagent
gets the compact task packet of `plans/worker-brief-template.md`, and
nothing more:

- the exact pinned source — the § of `algorithm-v2.md` and the landed
  declarations it composes against, quoted with `file:line`, inline;
- the **one file it owns**, and the landed APIs it may reuse;
- the semantic hazards that could yield a plausible but weaker theorem —
  copy them from the plan's leaf row, do not cite a document;
- the exact build and semantic gates for acceptance;
- "touch only this file; do not stage, do not commit, do not build any
  package other than the one named."

Give the worktree path, the package dir, the namespace, and the fact that
the tree is already seeded and warm. The worker never seeds and never
retries a seed — that is yours.

**4. Wait.** Leave the wave alone for roughly an hour. **Do not poll, do
not ask for status, do not interrupt** unless new information genuinely
changes the task. This is the rule the July retro measured; breaking it
costs more than it saves.

**5. Review.** Read the file the worker produced. Not its report — the
file. Check, in this order:

- **Source semantics.** Does the theorem say what `algorithm-v2.md` says
  it must? A checklist-complete but semantically weakened theorem is not
  complete. Read the theorem, not the docstring and not the framing prose:
  every defect the four audits found was a place where a document asserted
  something its own cited object does not say.
- **Preconditions.** Were hypotheses added that the caller cannot supply?
- **Ownership.** Did it touch only its file?
- **Cost claims.** If the leaf states a bound, is the bound the one §7
  needs, with the same quantifier order?
- **`sorry`, `native_decide`, and axioms.** `lean_verify` on the leaf's
  headline declaration. Zero new axioms unless the plan's row says
  otherwise.

Request focused corrections if needed and re-review. Do not rewrite the
worker's proof yourself unless the correction is smaller than the message
describing it.

**6. Gate.** From the main checkout:

```
.claude/leaf-gate.sh nowhere-dense-model-checking
```

The gate is an independent replay, not the worker's report. Green is
required to land.

**7. Land.** Review the branch diff from the main checkout, fast-forward or
merge onto `main`, then remove the worktree promptly — disk is tight — and
delete its branch. Stage only the files belonging to this boundary; leave
any unrelated WIP unstaged.

**8. Record.** Update the ledger row: status `done`, the landing commit,
and one line on what is now true that was not before. If the leaf changed
what a *later* leaf must do, edit that later row in the plan now, while you
still remember why. Commit the ledger with the boundary.

**9. Push.** `git push -u origin <branch>`. On network failure retry four
times with 2s/4s/8s/16s backoff.

Then go back to **1**.

## Stop conditions

Stop the loop and report to Jan only for:

1. **A blocked leaf with no ready work behind it** — the DAG has stalled.
   Say which leaf, which dependency it wants, and what would unblock it.
2. **A finding that invalidates the design**, not the proof: something in
   `algorithm-v2.md` that no amount of proving will fix. Record it in the
   document as the audits' findings are recorded (a `⟨…⟩` tag naming the
   revision), then stop.
3. **A licence, contract, or endorsed-surface change** — anything touching
   `concepts/Lax3/*.lean`'s statements, a `lakefile.toml` pin, or a
   reference under `references/`. Squaring the word-length side condition
   was Jan's call; so is the next one like it.

Everything else — a failed build, a wrong lemma, a worker that produced
nothing, a leaf that turns out to be three leaves — you handle and continue.

## Standing hazards for this campaign

Copy the relevant ones into each task packet.

- **Never run `lake update`.** The toolchain is pinned per package in
  `lean-toolchain`, mathlib by git rev in `lakefile.toml`.
- **Cross-submission requires are `(git, rev, subDir)` pins**, never a
  sibling `path`. After any `lax build`, re-run
  `.claude/sibling-overrides.sh`.
- **Keep the build warm.** `lean-lsp` tools time out against a cold build.
  Prefer `lean_goal` / `lean_diagnostic_messages` / `lean_multi_attempt`
  over rebuilding to inspect proof state. After an import or toolchain
  change, `lean_build` first — goals are stale until then.
- **`deleteVerts` isolates, it does not remove.** The carrier survives.
  Every carrier-versus-renumbering confusion in this campaign started here.
- **The endorsed surface is frozen.** `concepts/Lax3/*.lean` statements are
  the contract; proofs-side satellites are where new lemmas go.
