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
| E0 | cover time bound stated as an assumption; §8/§9 rewrite | ready | — | — | unblocked 2026-08-17: `references/nodm05/` is the NOdM paper GKS defer to |
| E1 | cover clusters are path-closed (§5) | ready | — | — | priced at ~10 lines, untested |
| E2 | `ctr` and the π-min identity (§4) | ready | — | — | priced at ~6 lines, untested |
| E3 | the edge half of (★) (§7) | ready | — | — | no counterpart in the surviving layer |
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

Nothing landed yet. Wave 1 (E1, E2, E3) is the intended first dispatch: three
small, disjoint cover-layer satellites, chosen because they are the cheapest
way to test whether this document's line-count estimates mean anything.

Four adversarial audits (29 + 9 agents) preceded this file. Their standing
result: the abstract core — §5's recursion, §7's shape, D2–D4, and both of Rev
3's inventions — has survived every attack. What repeatedly broke was the seams
between patches, the constants, and citations asserted rather than opened.

Two things changed on the day the ledger opened, and both shrink the plan:

- **§8 step 0b is not blocked.** GKS's bracket resolves to arXiv math/0508324v2,
  now at `references/nodm05/`. It supplies the round count and per-round cost
  Rev 4 recorded as absent everywhere. What it does *not* supply is the
  nowhere-dense instantiation — its Theorem 4.3 is a **bounded expansion**
  statement in time **O(n)** — and that adaptation, not the paper, is E0's
  content.
- **§7 stops being tightened.** Jan's call: take the slack. `δ = ε/(ℓ+2)` and a
  freely chosen base constant `K`, in place of Rev 4's `ε/(ℓ+1)` and the forced
  `(2c)^{L+1}` shape that manufactured the `c ≥ 6` side condition. The headline
  is unchanged; three consecutive revisions got that paragraph's arithmetic
  wrong, and the tight inequality was the reason.
