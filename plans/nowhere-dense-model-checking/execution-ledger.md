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
| E0 | cover time bound stated as an assumption; §8/§9 rewrite | done | w1 | 8709c19 | `CoverSpec.CoverOrderingTime`; only the `time` field is assumed, cover/degree derived; §8 0b + §9 O7 rewritten, pins spot-checked |
| E1 | cover clusters are path-closed (§5) | done | w1 | 8709c19 | `ClusterPaths`; delivered through to the induced graph, ~110 lines against the ~10-line estimate |
| E2 | `ctr` and the π-min identity (§4) | done | w1 | 8709c19 | `CoverCentres`; `ctr` is noncomputable (`Finset.min'` via `π`) — E12 must implement it; ~217 lines against the ~6-line estimate |
| E3 | the edge half of (★) (§7) | done | w1 | 8709c19 | `CoverEdgeSum.sum_clusterWeight_le_rpow`; hypotheses exactly `0 ≤ c_D`, `0 ≤ δ`, `1 ≤ ‖A‖`; ceiling carried into `c_D+1` |
| E4 | the cost recurrence, amended and slackened (§7) | done | w2 | b0444fa | `cost_root_le_chosenK`: `K^{ℓ+1}·n^{1+ε}` at `δ=ε/(ℓ+2)`, **no condition on `c`**; `star_of_cover_degree` bridges (★) to E3 |
| E5 | `ReachedR` generalized to `S`-moves (§8.2) | done | w2 | b0444fa | `ReachedS`; descend batch is an equality; `splitterWins_of_reachedS` via mixed histories — no `splitterWins_anti` needed |
| E6 | carrier transport for `ReachedR` (§9) | done | w3 | 55ba312 | `ArenaTransport`: one pushforward covers bijection + isolated cases; §5 line 8 was a **type error** — record kept at the root carrier, §5/§9 rewritten |
| E7 | the compaction lemma (§5 step 3′, §8.4a) | done | w2 | b0444fa | `sat_compact_iff_satWithin_deleteVerts_compl`; plain `Sat↔Sat` is false (`exU` sees isolated verts) — `SatWithin` is the true form; no order hypothesis |
| E8 | locality decomposition as a function (§8.3, O2) | done | w2 | b0444fa | `localityBC` via the Assembly discharge (axiom-free); `rfl`-irrelevant in the rank witness; atom lists for E9 |
| E9 | the abstract algorithm — **hard gate** (§8.4) | done | w4 | bf7baef | did **not** split: `Driver*` (5 files, 2125 lines); `tables_correct` unconditional, `mc_correct` for every ordering, `mkSetup_dcost_root_le` from `CoverOrderingTime` |
| E10 | unrolling the depth-`ℓ` recursion (§8.4b) | wip | w5 | — | `Unroll*` family; also owns threading `Inv` through the reified run tree |
| E11 | the `Refine` tower probe (§8.5) | done | w2 | b0444fa | charge is alive-summed + carrier-sized init per call: restrict-then-BFS **forced**, mask ≠ restrict; `SpaceBudgetProbe` is §11's natural home |
| E12 | `Arena` implementation and remaining routines (§8.6) | wip | w5 | — | `Impl*` family; expected to split — priorities: bfs/bfsSupports, guarded greedyScatter, BotTables evaluator, restrict |
| E13 | compose to the headline (§8.7) | waiting | — | — | needs everything |

## Campaign log

### 2026-08-18 — w4 lands: the hard gate is passed (`bf7baef`)

What is now true: **the abstract algorithm exists and is correct and
affordable.** `mc_correct` — the driver decides `φ` on every input, for every
ordering routine and every scatter choice; `mkSetup_dcost_root_le` — its cost
closes at `KD^{ℓ+1}·‖A₀‖^{1+ε}` from exactly one hypothesis, E0's
`CoverOrderingTime`; `eq_bot_of_inv_depth` — the leaf test is exhaustive in
budget, via the `ReachedS` invariant kept at the root carrier as E6 prescribed.
E9 did not split. E10 and E12 are both ready and disjoint — they are the next
wave, and E13 is the only leaf behind them.

Findings worth keeping:

- **The leaf IS `Sat`, and that is landed intent, not a shortcut**:
  `BotEval`'s docstring defines the base case as "returns `Sat` itself; an
  implementation has to evaluate that value" — its lemma set is the machine's
  evaluation bridge, consumed at E12, with the off-budget fuel-0 corner
  covered by `eq_bot_of_inv_depth`.
- **§5 step 3′ dissolves under reordering**: fusing the compaction with line
  16's restrict makes every later rewrite a landed lemma on the child carrier.
  The doc's stated order would have needed a genuinely new transport. Doc
  simplification available; not urgent.
- **D6 sharpened and scoped**: the abstract layer needs only `(vtx, arena)`
  pairs — `Classical.choose`-deterministic `pathSet` reconstructs identical
  supports at descent. The per-vertex lists are purely P1a avoidance on the
  machine; entirely E12's.
- **`IsCostRecurrence`'s `node` clause is not consumable at an arena-typed
  cost** (size-indexed sup does not exist once `hist` makes the type infinite
  per weight); E9 ran the induction directly, consuming `chosenK_step` + the
  E3 mass bounds. Optional refactor: an arena-shaped `node` clause. Not
  blocking anything.
- The augmentation-round instantiation is `R' := 3R, t := R` — slack absorbed
  as constants; the `≈3log₂(4rc)` depth naming stays an E12-side constant
  improvement.

### 2026-08-18 — w3 lands: E6, and §5's precondition is finally well-typed (`55ba312`)

What is now true: every dependency of E9 is `done`. The carrier seam D1 opened
is closed the cheap way — the play record lives at the root carrier and is
never re-typed; `ArenaTransport` supplies the wholesale transports anyway
(`reachedS_map`/`reachedS_restrict` along any embedding, `nextArenaS_mapRound`,
`ball_map`), and §5 line 8 now states the invariant that actually typechecks.
E6's one deviation from the plan is recorded in §9: general embeddings, not
`castLE` — the child-to-root composite of `up` maps lands on a cluster, not an
initial segment. One identity is explicitly booked for E12: `map emb B =
deleteVerts (deleteVerts A Xᶜ) W` at the implementation's restrict∘isolate
(line 16/21), which is what re-expresses a child's reached arena at the root.

**Wave 4 is E9 alone — the hard gate.** No ND-MC driver until it is complete
and reviewed.

### 2026-08-18 — w2 lands: every interface E9 composes against exists (`b0444fa`)

What is now true: the abstract driver's whole dependency surface is landed.
The cost induction is solved and slackened (`c ≥ 6` did disappear — the `L = 0`
step of the chosen `K` is an *equality* for all constants, so nothing could
hide in it); the cluster-restricted game record exists with the descend batch
an equality and Splitter's win transferred; the compaction transports `Sat`
along any bijection into `SatWithin`; the locality decomposition is one fixed
function with iterable atom lists; and the Refine probe returned with the
charge in hand. E9 now waits on E6 alone — wave 3 is E6, then E9 by itself.

Findings worth keeping:

- **E5 beat its audit estimate qualitatively**: `splitterWins_of_reachedS`
  needed neither `splitterWins_anti` nor the `W ↦ W ∩ S` batch map — Splitter's
  own rounds simply record `res := ball` (legal by `subset_rfl`) and the R
  proof replays on histories that mix cluster and ball rounds. One fewer
  dependency than the audit priced, and the changed-distances objection never
  arises.
- **E7 confirmed D3 in the object**: no order hypothesis, no dead-vertex
  correction. But note the *true* statement is `Sat B ↔ SatWithin X A` — the
  unrelativized `Sat ↔ Sat` is false because `exU` ranges over the kept
  carrier's isolated vertices. §5's chain must consume the `SatWithin` form.
- **E11's probe verdict**: the tower's BFS budget is alive-summed
  (`Σ_{alive}(deg_G+1)`) with a carrier-sized `bfs.init` per call — the
  §6.1 `O(‖ball‖)` shape appears only *after* `restrict`. The quadratic trap
  sits in the init term. E12 must call BFS on `B₀`, never mask-on-arena; a
  ball-shaped restatement of the tower spec would need a frontier-in-ball
  invariant (owed only if E12 wants §4's charge verbatim).
- E8's `localityBC` chooses from the **Assembly discharge**, not the endorsed
  axiom — footprint stays at the standard three. Same trick available any
  time a concept axiom has a proofs-side discharge.
- `Lax13Proofs` had never been elaborated in this checkout: E11 paid ~10 min
  compiling the ~11-file NREST closure of `Examples.Bfs` from source. The
  captures (`capture-seed.sh word-ram`) could have supplied it prebuilt;
  worth doing before E12, which imports much more of the tower.

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

### 2026-08-18 — the flow is cloud-adjusted: nothing may live only in the container

This session runs in an ephemeral claude.ai/code container — reclaimed on
inactivity, repo recloned fresh next time. Standing adjustments, Jan's call:

- **Push at every boundary** — `main` and the mirror `claude/ndmc-71wd6g`
  both (origin/main is live again as of `801d5df`; the stop hook watches it).
- **Checkpoint-push in-flight waves**: at every supervisor wake, commit the
  wave worktree's current files on its `worktree-w<N>` branch and push. Not a
  landing — never merge a checkpoint; review still happens on final state
  only. If the container dies mid-wave, recovery = fetch `worktree-w<N>`,
  diff against `main`, salvage or re-dispatch per leaf.
- **Delete the remote `worktree-w<N>` branch when the wave lands** (the
  landing supersedes it).
- A dead container also kills the wave's workers and any fallback timer;
  the ledger + `git log` on origin remain the whole recovery state, as
  designed.

### 2026-08-18 — w1 lands: the cover layer owes nothing but time (`8709c19`)

What is now true: the four guarantees §4/§5 demand of `cover` beyond the
endorsed `IsNeighborhoodCover` all exist proofs-side — path-closure into the
induced graph (E1), a named `ctr` with the π-min identity at the two distinct
radii (E2), the edge half of (★) with the ceiling absorbed into `c_D+1` (E3) —
and the one thing nobody can prove from material in-repo, the ordering phase's
step count, is a hypothesis with a name (`CoverOrderingTime`, E0) rather than a
gap with a citation. E4's dependencies are both landed; wave 2 is E4, E5, E7,
E8, E11.

Findings worth keeping:

- **The line-count estimates were off by an order of magnitude** — "~6 lines"
  (E2) landed at ~217, "~10 lines" (E1) at ~110. The *arguments* were exactly
  as priced (the math was right); the factor is statements, docstrings, and
  the private `withinDist_of_mem_support` E2 had to re-prove because
  `CoverConstruction` hides it. Price future leaves accordingly.
- `ctr` is noncomputable as defined. Fine for the abstract layer; E12 owes the
  computed version read off the cover sweep.
- E0 went past its packet in the right direction: `CoverDegree.AugChainData`
  lets the whole cover *structure* be derived rather than assumed, so the
  assumption surface is exactly one field (`IsCoverOrdering.time`), plus two
  controls (binder-order rationale, satisfiability on the empty class).
- Worker-report channel: all four completion notifications were lost;
  supervision recovered entirely from the files, which is what the review
  order prescribes anyway. E3's worker left five mechanical build errors
  (a misspelled lemma name, two `noncomputable`s, two casts through a `set`
  binder) — fixed at review, smaller than a correction round-trip.
