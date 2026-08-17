# ND-MC execution ledger

The *mutable* half of the campaign state. `execution-plan.md` says what each
leaf is; this says where each one stands. `/ndmc` reads both.

**Keep this accurate after every boundary.** A compacted context or a fresh
session recovers the campaign from this file plus `git log` and nothing else.

Status values: `ready` (dependencies met, may be dispatched) · `waiting`
(dependency not yet `done`) · `wip` (dispatched, worker running) · `review`
(worker returned, supervisor reviewing) · `done` (landed on `main`) ·
`blocked` (cannot proceed; the note says what would unblock it).

| leaf | what it closes | status | wave | commit | note |
|---|---|---|---|---|---|
| E0 | cover time bound stated as an assumption; §8/§9 rewrite | wip | w1 | — | unblocked 2026-08-17: `references/nodm05/` + `nodm05i/` are the two NOdM papers GKS defer to; the chain now bottoms out in a proof |
| E1 | cover clusters are path-closed (§5) | wip | w1 | — | priced at ~10 lines, untested |
| E2 | `ctr` and the π-min identity (§4) | wip | w1 | — | priced at ~6 lines, untested |
| E3 | the edge half of (★) (§7) | wip | w1 | — | no counterpart in the surviving layer |
| E4 | the cost recurrence, amended and slackened (§7) | waiting | — | — | needs E3, E0. `c ≥ 6` must **disappear** — see plan |
| E5 | `ReachedR` generalized to `S`-moves (§8.2) | ready | — | — | five analogue lemmas; `hbatch` is an equality, not `⊆` |
| E6 | carrier transport for `ReachedR` (§9) | waiting | — | — | needs E5 |
| E7 | the compaction lemma (§5 step 3′, §8.4a) | ready | — | — | much smaller than Rev 3 priced it (D3) |
| E8 | locality decomposition as a function (§8.3, O2) | ready | — | — | buys a function, not decidability |
| E9 | the abstract algorithm — **hard gate** (§8.4) | waiting | — | — | needs E1,E2,E4,E5,E6,E7,E8; may split into fresh rows |
| E10 | unrolling the depth-`ℓ` recursion (§8.4b) | waiting | — | — | needs E9 |
| E11 | the `Refine` tower probe (§8.5) | ready | — | — | independent; run early and in parallel |
| E12 | `Arena` implementation and remaining routines (§8.6) | waiting | — | — | needs E9, E11 |
| E13 | compose to the headline (§8.7) | waiting | — | — | needs everything |

## Campaign log

One entry per landed boundary. What is now true that was not before — not what
was done.

### 2026-08-17 — the ledger opens

Nothing landed yet. **Wave 1 (`w1`) is E0, E1, E2, E3** — three small, disjoint
cover-layer satellites plus the one document leaf. Chosen because they are the
cheapest way to test whether the design's line-count estimates mean anything,
and because they land both of E4's dependencies, so wave 2 opens fully.

Four adversarial audits (29 + 9 agents) preceded this file. Their standing
result: the abstract core — §5's recursion, §7's shape, D2–D4, and both of Rev
3's inventions — has survived every attack. What repeatedly broke was the seams
between patches, the constants, and citations asserted rather than opened.

Two things changed on the day the ledger opened, and both shrink the plan:

- **§8 step 0b is not blocked.** GKS's bracket resolves to arXiv math/0508324v2,
  now at `references/nodm05/`. It supplies the round count and per-round cost
  Rev 4 recorded as absent everywhere. Its own Lemma 4.1 defers once more, to
  Lemma 6.1 of part I — arXiv math/0508323v1, now at `references/nodm05i/`,
  where it is proved in full. So the deferral chain is four links long, one
  longer than Rev 4 thought, and it **terminates in a proof**. What none of the
  four papers supplies is the nowhere-dense instantiation — part II's Theorem
  4.3 is a **bounded expansion** statement in time **O(n)** — and that
  adaptation, not the import, is E0's content.
- **§7 stops being tightened.** Jan's call: take the slack. `δ = ε/(ℓ+2)` and a
  freely chosen base constant `K`, in place of Rev 4's `ε/(ℓ+1)` and the forced
  `(2c)^{L+1}` shape that manufactured the `c ≥ 6` side condition. The headline
  is unchanged; three consecutive revisions got that paragraph's arithmetic
  wrong, and the tight inequality was the reason.

### 2026-08-17 — wave 1 dispatched, and the gate was red before it

`w1` is E0, E1, E2, E3, one worker each, on `worktree-w1` off `main`. Seed took
0.9 s; the packages were already warm.

**The baseline gate failed, and not because of a leaf.**
`.claude/leaf-gate.sh nowhere-dense-model-checking` was red on `main` at
`b9a049a`: both `lake build`s passed, and the statement audit rejected the
package with `Lax3Proofs must have no module docstring`. The `/-! -/` block
after the root module's import list is what the 2026-08-17 prune left behind;
no other section of that file uses one. Converted to `--` comments at `38c5243`
and the audit passes. What this cost is worth recording: **no leaf in this
campaign could have landed until it was fixed**, and it was invisible from the
ledger, which had never seen a gate run. Run the gate once at the start of a
campaign, not first at the first landing.

Also measured: a cold-ish full `leaf-gate.sh` is ~10 min (concepts 25 s, proofs
1 m31 s, inspector 36 s, plus the two prior `lake build`s); a re-run of the
`lax build` audit alone against a warm tree is ~16 s. Budget the gate per
landing, not per leaf.
