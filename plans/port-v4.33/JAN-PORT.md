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
| word-ram | lax-67 → **lax-808846** | lax-67 deleted 09-15; lax-808846 draft | v4.33 | Jan | done: stand-alone draft @ 5a2645e (D1) |
| ram-linear-time | lax-11 → **lax-271696** | lax-11 REGISTERED by Clemens 09-15 11:24 UTC (his port on Lax865980, @ f867352); lax-271696 = successor draft on Lax808846 | v4.33 | Jan | see D5 |
| refinement-tower | lax-62 | draft | v4.33 | Jan | done: draft @ 9d06d27 on Lax808846 |
| nowhere-dense-model-checking | lax-3 | draft | v4.33 | Jan | done: draft @ c474df4 on Lax808846/Lax271696/Lax62/Lax199508 |
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

**D1 — lax-67 DELETED (Jan, 2026-09-15, 13:05): "we delete the .30 ram
draft even if clemens and edouard still depend on it. that is okay."**
`lax delete --yes lax-67` retired the id; the archive listed lax-3,
lax-11, lax-62, lax-195003 (Welzl orders, Clemens) and lax-489179
(ETH/SETH, Édouard) as left broken — the last two are their owners' to
repin. The repaired word RAM gets the fresh id **lax-808846** (`lax init
--env v4.33.0`), the surface renames Lax67 → Lax808846 in word-ram and
its three dependents (219 files, mechanical), and the manifest claims
`supersedes: lax-865980` for the archive gate to accept or refuse (the
owner rule refused it for lax-67; if refused again the record stands
alone and the line is dropped). Facts that led here: lax-865980
(registered, Clemens) is lax-13's content at v4.33 without the reviewed
repair and without ~700 proof-package lines the dependents use;
`supersedes: lax-13` is taken by it for good.

**D5 — ram-linear-time gets the successor lax-271696 (supervisor, 2026-09-15
14:20).** While wave 2 was building, Clemens registered lax-11 (11:24 UTC,
source f867352: his own v4.33 port of ram-linear-time onto the registered
Lax865980, a 20-file/89-line delta from ours — the rename plus nothing
the repair needs). Registered is immutable, so the cascade's in-place
resubmit of lax-11 was refused. The chain on the repaired RAM therefore
continues as `lax-271696` (`lax init --env v4.33.0`, `supersedes: lax-11`
— Jan co-owns lax-11, so the owner rule should pass), surface renamed
Lax11 → Lax271696 in ram-linear-time and nowhere-dense-model-checking
(102 files). lax-11 stays as Clemens's Welzl-orders base. word-ram's
prose mentions of "Lax11" and welzl-orders are untouched.

**D2 — lax-768004 dropped.** lax-228581 (registered from main) already
supersedes lax-48; the cloud port's folder is deleted at landing.

**D3 — lax-5 successor = lax-710763** (draft, v4.33.0, `supersedes: lax-5`,
issue #117, source 5e97e29 on branch `worktree-ndmc-succ`; the folder is on
main since c874dee+1). `lax port lax-5` fails in lax 0.1.43 (refuses a
pre-six-digit source id; fixed upstream in an unreleased lax commit), so the
id came from `lax init --env v4.33.0` with `supersedes: lax-5` added by
hand. Same failure will hit `lax port lax-49` until lax is updated.
Cosmetic leftover: both lakefile comments in the folder still say
`Lax12`/`Lax14` (fixing them changes the content vs the record; do it at
the next resubmit). Stale `264807` mentions remain in the cloud port's
README/FINISH.md and `.claude/resubmit-cascade.sh:21` (comment).

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
| 1a | merge ram-input-repair + cloud port; re-port the four RAM folders on the repaired content; local builds green | opus | `.claude/worktrees/port-land` | BUILT 2026-09-15, branch `worktree-port-land` @ 611f0d9, reviewed by the supervisor, HELD (not landed) until D1 is decided. Result: ram-input-repair merges clean; 8e048cf reverted; cloud port merges with conflicts only in lax-introduction (main kept); **zero Lean edits needed** — repair and drift fixes are disjoint; word-ram 526+3030, ram-linear-time 1007+3083, refinement-tower 3+3343, ndmc 2048+3754 jobs green; `lax build --replay word-ram` green (51 s). Archive gate refuses BOTH supersedes claims for lax-67: `supersedes: lax-13` → supersedes-taken (lax-865980 holds it), `supersedes: lax-865980` → supersedes-owners (no owner of lax-865980 owns lax-67). Branch carries word-ram with no supersedes line. Worktree kept: it holds the v4.33 builds wave 2 needs. |
| 1b | lax-5 successor: real id, rename, build, submit as draft | opus | `.claude/worktrees/ndmc-succ` | DONE 2026-09-15: lax-710763 draft, 2080+2840 jobs green, archive accepted, concepts identical to lax-5 (archive extraction diffed field by field); landed on main, worktree removed, remote branch kept (the record points at it) |
| 1c | lax-introduction resubmit from main (v4.33, registered deps) | supervisor | main | DONE 2026-09-15: lax-242665 draft @ 2be112c, v4.33.0, requires Lax228581/Lax199508/Lax865980 (all registered); draft-dependency violation cleared |
| 1d | lax-introduction: drop the Bertrand network for the front page's (PrimeDivisor → Euclid) plus the twin prime conjecture as the open concept; front page carousel draws lax-242665's own cards | supervisor | main | DONE 2026-09-15: statements numbered from one counter (Def 1, Thm 2, Lem 3, Conj 4), boundary cases of all four concepts checked in Lean (no off-by-one), submitted @ f7c9272 and **REGISTERED** (Jan's go). Website `index.ts` + test still uncommitted in `~/git/lax-website`; deploy any time now that the archive holds `Lax242665.PrimeDivisor` |
| 1a′ | Lax67 → Lax808846 rename on the held branch, rebuild, land | supervisor | `port-land` | DONE 2026-09-15: four packages green (word-ram 70 s, rlt 3 min, tower 10 min, ndmc 20 min), landed on main @ 0bbb796 (phantom lax-264807 files dropped), worktree removed, builds moved into main |
| 2 | cascade resubmit word-ram → ram-linear-time, refinement-tower → nowhere-dense-model-checking (`.claude/resubmit-cascade.sh`, `LAX_SUBMIT_FLAGS=--force`) | supervisor | main | DONE 2026-09-15 ~15:30: lax-808846 @ 5a2645e (stand-alone; gate refused `supersedes: lax-865980` — supersedes-owners), lax-271696 @ 956e1cf (⊃ lax-11, accepted), lax-62 @ 9d06d27, lax-3 @ c474df4. Jan confirmed "continue rebasing on 808" after the two-RAM situation was laid out: lax-865980 (lax-13 port) carries the registered lax-11, lax-195003, lax-242665 and Szymon's drafts; lax-808846 (= lax-67 at v4.33, concepts byte-identical, two proof-site port fixes) carries lax-271696, lax-62, lax-3. Open: hand lax-808846 to Clemens as co-owner so it can claim `supersedes: lax-865980` (his call). Background `lake build`/`lax submit` get killed by the session's low-memory watchdog on this box; foreground `timeout 570` slices and `lax submit --resume` work. |
| 3 | registration per D4 | after 2 | main | DONE 2026-09-15: lax-710763, lax-242665 @ f7c9272, lax-808846 @ 9394e53 (Jan, `supersedes: lax-67`) registered. Then, on Jan's "register all my submissions", lax-271696 / lax-62 / lax-3 were registered with a STALE Lax808846 pin (5a2645e, one manifest-only commit behind 9394e53): the archive's Register checks dependencies by id only and re-runs no Resolution. Repaired the same evening on Jan's instruction: `npm run admin -- reset-draft` (lax-3 first, then lax-271696 and lax-62 in parallel), repin to 9394e53 @ 0503df0, resubmit both in parallel, repin lax-3 @ 0edafc2 and resubmit, then register all three with a zero-warning `.claude/sibling-overrides.sh` gate before each. Final: lax-271696 @ 0503df0, lax-62 @ 0503df0, lax-3 @ 0edafc2, all registered, all pins canonical. Pre-release db sanity check + "refuse draft dependencies" recorded in ~/git/lax TODO.md (Admin tool section) |
