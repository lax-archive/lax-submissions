# JAN-PORT — launch polish of Jan's submissions (started 2026-09-15)

Goal (Jan, 2026-09-15): every submission Jan authors at the v4.33.0 epoch,
drafts moved to registered, the stray superseded RAM draft resolved,
already-ported feature-branch work incorporated. Jan gave full authority
for the session; registration of anything Jan is still editing waits.
This file is the running record; `README.md` beside it is the cloud
port's ledger (2026-09-14) and `FINISH.md` its hand-back runbook.

## Inventory (archive synced 2026-09-15, 77 records)

| folder / record | id | state | env | authors | what has to happen |
|---|---|---|---|---|---|
| word-ram | lax-67 | draft | v4.30 | Jan | port in place; see decision D1 |
| ram-linear-time | lax-11 | draft | v4.30 | Jan | port in place, repin Lax67 |
| refinement-tower | lax-62 | draft | v4.30 | Jan | port in place, repin Lax67 |
| nowhere-dense-model-checking | lax-3 | draft | v4.30 | Jan | port in place, repin Lax67/11/62, Lax12→Lax199508 |
| lax-introduction | lax-242665 | draft | record v4.30, tree v4.33 | Édouard, Jan, Clemens | resubmit from main (already pinned to lax-228581/199508/865980) |
| monadic-dependence-neighborhood-complexity | lax-5 | registered | v4.30 | Jan | successor at v4.33 (cloud port scaffolded it as phantom id lax-264807 → needs a real `lax port lax-5`) |
| sparsity-lectures | lax-12 | registered | v4.30 | Jan | done: lax-199508 registered (Clemens, 09-13) |
| finite-ramsey | lax-14 | registered | v4.30 | Jan | done: lax-345067 registered (Clemens, 09-13) |
| word-ram (lax-13 line) | lax-13 | registered | v4.30 | Jan | done: lax-865980 registered (Clemens, 09-13, = lax-13 content) |
| twin-width-treewidth-separation | lax-48 | registered | v4.30 | Édouard, Jan | done: lax-228581 registered from main @ 1e200ff (09-15) |
| twin-width-mixed-minor-number | lax-49 | registered | v4.30 | Édouard (Jan co-owner, not author) | Édouard's call; `lax port lax-49` now possible (Lax48 → lax-228581) |
| twin-width-exponential-in-treewidth | lax-65 | **deleted on archive 09-04** | — | Édouard, Jan | folder still in tree, 0 proofs (Jan's PLAN.md); untouched here |
| foo/ | lax-430526 | not on archive | — | — | untracked test folder, untouched |
| lax-50, lax-66 | init | — | — | Jan | live inits in ~/foodir and ~/git/abmw-mc/lax, not stray |
| Transducers (8 drafts) | lax-157538 … | draft | v4.33 | Bojańczyk (Jan owner) | not Jan-authored; live in ~/git/transducer-book/lax, registration open |
| lax-58 / lax-560851 | — | draft | v4.30 / v4.33 | Jan, Szymon (Szymon owner) | Szymon's repo, already has its v4.33 draft |

## Feature branches holding finished ports (not on main at start)

- `origin/claude/port-ndmc-latest-epoch-0slpbd` (cloud, 2026-09-14, 47
  commits over main @ 14235ab): word-ram, ram-linear-time,
  refinement-tower, nowhere-dense-model-checking ported in place and
  green at v4.33; lax-5 successor folder `monadic-dependence-neighborhood-complexity-v4-33`
  (phantom id lax-264807, never on the archive); lax-48 successor folder
  (phantom lax-768004 — obsolete, lax-228581 is registered from main);
  verbatim copies of `sparsity-lectures-v4-33/`, `finite-ramsey-v4-33/`;
  `.claude/local-overrides.py`. Conflicts with main only in
  lax-introduction (main wins: it is pinned to the registered lax-228581).
- `origin/ram-input-repair` (Édouard, 2026-09-09; Clemens 09-14; 24
  commits, merges clean): the reviewed RAM input/terminal-instruction
  repair (`7ac514c`, `ca86140`, smoke domains `542785f`) and the
  dependents' migration. **This is what the archive's current drafts
  lax-67 @ 512403f, lax-11/lax-62 @ d82625d, lax-3 @ 3dc030d are built
  from** — main never received it, and the cloud port ported main's
  pre-repair content. Its last commit `8e048cf` (Clemens) renames
  ram-linear-time's requires to Lax865980; it is a bare rename and is
  not taken (D1).
- `origin/codex/archive-v4.33-migration` (Clemens): sources of the
  registered lax-199508 / lax-345067 / lax-865980 (+ Édouard's and
  Clemens's own); nothing further to take.

## Decisions

**D1 — lax-67 stays; it is not the stray draft to delete.** Facts: (a)
lax-865980 (registered, Clemens) is lax-13's content at v4.33 — it lacks
the reviewed repair Jan approved on 2026-09-09 and ~700 proof-package
lines the dependents use (`Com.NoWrite` alone in 19 dependent files);
(b) lax-67 has external dependents: Édouard's lax-489179 (ETH/SETH) and
Clemens's lax-195003 (Welzl orders) — deleting retires the id and breaks
both; (c) deletion is irreversible, keeping is not. Resolution: port
lax-67 in place at v4.33 on the repaired content (ram-input-repair merged
into main), and claim `supersedes: lax-865980` so the archive shows one
line lax-13 → lax-865980 → lax-67 instead of two v4.33 "The Word RAM"
records. If the archive refuses the claim (lax-865980 is owned by
Clemens alone; a supersedes claim needs ownership of the superseded
record), lax-67 is submitted without a supersedes line and this item
goes back to Jan/Clemens. Registering lax-67 waits on that outcome.

**D2 — lax-768004 dropped.** lax-228581 (registered from main) already
supersedes lax-48; the cloud port's folder is deleted at landing.

**D3 — lax-5 successor gets a real id** via `lax port lax-5` on this
machine; the folder from the cloud port is renamed to it.

**D4 — registration.** Bottom-up once each record is at v4.33 and its
dependencies are registered: lax-5 successor; then lax-67 (if D1's
supersedes holds), lax-11, lax-62, lax-3. lax-introduction is NOT
registered here: Jan is editing its paper (main.tex dirty in the
checkout). Registered is permanent; a further RAM redesign (Jan's
ram-v3 plan) becomes a later successor, which is how the archive works.

## Draft-dependency rule (Jan, 2026-09-15: drafts may later be allowed as dependencies; today they are violations)

Records that require a **draft** record, from the synced archive
(deleted/init records excluded). Jan's own, on this repo:

| record | state | requires draft(s) | note |
|---|---|---|---|
| lax-3 nowhere-dense-model-checking | draft | lax-11, lax-62, lax-67 | resolved by registering the chain bottom-up (D4) |
| lax-11 ram-linear-time | draft | lax-67 | same |
| lax-62 refinement-tower | draft | lax-67 | same |
| lax-242665 lax-introduction | draft (v4.30 record) | lax-67 | main's tree already requires the registered lax-865980 instead; resolved by the resubmit |

Others (owners in brackets):

| record | state | requires draft(s) |
|---|---|---|
| lax-195003 welzl-orders [clemenskuske] | draft v4.30 | lax-11, lax-67 |
| lax-214022 cograph welzl orders [clemenskuske] | draft v4.30 | lax-195003 |
| lax-489179 ETH/SETH [EdouardBonnet] | draft v4.30 | lax-67 |
| lax-307052 Savitch [EdouardBonnet] | draft v4.30 | lax-554803 |
| lax-47 MIS inapproximability [EdouardBonnet] | draft v4.30 | lax-51 |
| lax-57 EH for P5 [EdouardBonnet] | draft v4.33 | lax-54 |
| lax-53 MSO tree automata [szymtor] | draft v4.30 | lax-52, lax-58 |
| lax-58 certified structures [szymtor] | draft v4.30 | lax-51 |
| lax-560851 certified structures [szymtor] | draft v4.33 | lax-759944 |
| lax-842588 MSO tree automata [szymtor] | draft v4.33 | lax-146103, lax-560851 |
| lax-678846 Fagin [szymtor] | draft v4.30 | lax-979537 |
| lax-988886 Fagin [szymtor] | draft v4.33 | lax-751879 |
| Transducers Parts B/C/C'/D and the umbrella lax-157538 [jan3er] | draft v4.33 | each other (A ← B ← C… ← umbrella) |

## Waves

| wave | leaf | worker | worktree | state |
|---|---|---|---|---|
| 1a | merge ram-input-repair + cloud port into main; re-port the four RAM folders on the repaired content; local builds green | opus | `.claude/worktrees/port-land` | dispatched 2026-09-15 |
| 1b | lax-5 successor: real id, rename, build, submit as draft | opus | `.claude/worktrees/ndmc-succ` | dispatched 2026-09-15 |
| 1c | lax-introduction resubmit from main (v4.33, registered deps) | supervisor | main | started 2026-09-15 |
| 2 | cascade resubmit word-ram → ram-linear-time, refinement-tower → nowhere-dense-model-checking (`.claude/resubmit-cascade.sh`), supersedes claim per D1 | after 1a | main | pending |
| 3 | registration per D4 | after 2 | main | pending |
