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
| E10 | unrolling the depth-`ℓ` recursion (§8.4b) | done | w5 | a1d9294 | `Unroll`; iterative form = `tables` by fuel induction; frames **static**, peak `(ℓ+1)(2+c_S)·n²` absorbed by the squared guarantee; `mkSetup_memLeaf_eq_bot` closes E9's deferred composition |
| E11 | the `Refine` tower probe (§8.5) | done | w2 | b0444fa | charge is alive-summed + carrier-sized init per call: restrict-then-BFS **forced**, mask ≠ restrict; `SpaceBudgetProbe` is §11's natural home |
| E12 | `Arena` implementation (§8.6) — **split** | done (part) | w5 | a1d9294 | `Impl{Scatter,Bot,Bfs}` landed: guarded scatter (`t=0` guard is the cost statement), `botEval = Sat ⊥`, BFS at `B₀` with `chargeB0_total = 2‖B₀‖+d+2`; remainder is E12b/c/d |
| E12b | `restrict` + `isolate` (§6.1) | done | w6 | 84ae503 | scratch array **one per node**, amortization visible in the cost model; charge is `Σ_{s∈S} deg_A(s)`-shaped — `O(‖A[S]‖+|S|)` is FALSE (`K_{3,n−3}`) |
| E12c | the `cover` sweep + computed `ctr` (§6.2 ⟨B⟩) | done | w6 | 84ae503 | GKS's peeling sweep, `N_</N_>` split repr; identities to `Driver.cluster` and `CoverCentres.ctr`; (★) as GKS's accounting; expect 2 runs, schedule first |
| E12d | `recordProfiles` (§6.3) | done | w6 | 84ae503 | iterate single-source `chargeB0` `(m+L)` times; rows cumulative, measured in `preG` **before** isolation; identity target `Driver.childCol`'s slot families |
| E13 | compose to the headline (§8.7) | done | w7 | b2df405 | `headline_abstract`/`headline_encoded`: full iff at `FirstOrder.Sat`, cost at `(x.length+1)^{1+ε}` under `CoverOrderingTime` alone; remainder mapped in-file |
| F1 | ordering routine + `data` discharge | done | w8 | 2206f72 | **no hypothesis at all**; minimality via `sInf`; new `greedyStep` (landed `tightStep` fails `PiIncreasing` on greedy rounds); F5 owes exactly `time` |
| F2 | the CSR front end | done | w8 | 2206f72 | round trip is a graph **equality**; `chargeParse` total = `x.length` exactly |
| F3 | the frame program (NREST) | done | w8 | 2206f72 | `frameProg_le_spec`: the table IS `frameEval` given the two slots; charge ledger named; comparison deferred to F3c |
| F3b | multi-source profiles via a virtual source | done | w9 | 7ed61d3 | bridge survives source-revisits (strong recursion); `recordProfilesMS_eq_childCol` against the frozen target; marker free; §6.3's `(m+L)` shape restored |
| F3c | the program's charge, closed to the `T`-clause | done | w10 | 9b4cdfa | `exists_mcChargeMS_T` with **no `CoverOrderingTime` assumption**; route (b) forced (landed budget fails the headline — MS column swap + transfer lemmas); direct-κ vs `dcost` impossible; empty centres make node-aggregate essential |
| F4 | the driver program (ℓ+1 levels) | done | w9 | 7ed61d3 | `driverProg_le_spec` by level induction; `mcProg_headline` at the axiom's semantic object; fuel-0 edged branch dead on the class |
| F5 | the cover pipeline's cost, proved | done | w9 | 7ed61d3 | **`coverOrderingTime_of_nowhereDense`** with the honest witness `timedGreedyRoutine`; true exponent `1+δ`; no sort (the peel ranks); vacuity guarded (`le_chainCharge`) |
| F6 | codegen to the machine — **split** | done (part) | w10 | 9b4cdfa | `mc_computesInTime_of_solveSpec`: ONE named obligation (`SolveSpec`) from the axiom; parse `Spec` discharged; `mcD` verbatim; word-size condition spent (`mcB = q(|x|+1)²`) |
| F6b | arena materialization + profiles reroute + root eval | done | w11 | c4cde5b | `frameProgMS` at the MS budget; the CSR cells ARE the root arena; `solveSpec_of_rest` leaves one obligation; the sweep's BFS cut to F6d |
| F6c | the `ℓ+1` driver blocks — run 1 | done (part) | w11 | 7bad766 | frame contract + greedyScatter fully IMP+ (with an inlined marking BFS) + botEval's schedule fix; direct `Spec`-kit route validated; continuation split into F6c2/F6c3 + the post-F6d stages (supports, profilesMS, cover sweep, readback, frame/driver composition) |
| F6c2 | restrict + isolate as IMP+ | done | w13 | 7736b66 | both landed; fill amortized at the **parent** degree; forced the `setEquiv` repin (sorted `orderIsoOfFin` — the docstring lied about its own theorem, lesson #6); exact-length-region seam flagged for the composer |
| F6c3 | block 0's IMP+ table fill | done | w13 | 7736b66 | `botCom_spec` at the frame contract, table at `Sat A.G` under `hbot`; edgelessness a hypothesis, no machine edge scan; budget in `botC`'s shape |
| F6d | shared IMP+ BFS: generalize `markCom` | done | w12 | ab14f30 | `bfsCom_spec` literally at `ImplBfs.BallTable` (+ sentinel bound clause), `bfsK ≤ 69·(d+1)·(N+ns+1)`; markCom's invariant minus the mark coupling; gate green |
| F6c4 | supports stage as IMP+ | done | w13 | 7736b66 | least parent by min-in-cell; stored lists = `Impl.descend` verbatim; `d+1 ≤ hb` is the slot-capacity hypothesis the composer supplies |
| F6c5 | profilesMS stage as IMP+ | done | w13 | 7736b66 | lands under the frozen identity with `preG` by `rfl`; marker at zero BFS; per-class exact-length `vt` regions — the composer's windowed-contract seam |
| F6c6 | the frame + `ℓ+1` chain: close `SolveSpec` | done (part) | w14 | b3a5502 | windowed contract landed (`bigStepB_padA`, `specWindow`, `ArenaStW`/`TableBitsW`); botCom/restrictCom lifted; level chain proved (`chainCom_blockSpec`); leaf guard machine-tested (`ns_zero_iff_bot` ⟺ edgeless); **`solveSpec_of_chain`**: `SolveSpec` for `matCom ; rootLoadCom ; chainCom ; topCom scatCom` conditional on FOUR residuals — root `BlockSpec` (= FrameStep), root load, `TopScatterSpec`, `Adm` — budget `Ks`, `KsChargeBridge` named; supervisor decision: supports runs at radius **2R** (§5 l.17), `ProgFrame.supportsC`'s `S.R` slot is the stale figure |
| F6c7 | discharge the four chain residuals | done (part) | w15 | c148266 | all five stage lifts landed (`bfsCom/supportsCom/scatterCom/isolateCom/profilesCom_specW` — radius free, 2R instantiable; profiles at `preG`, batch exactly `mb`); `canonBotB` with every name condition off `lv`; **`solveSpec_closed`** from THREE residuals (`FrameStepAll`, `RootLoadSpec`, `TopScatterAll`) + Adm-side root facts; axioms = landed baseline; finding: `ProfNames.Ok` lacks up/hist freshness — taken as `lv`-dischargeable hypotheses; `KB` unpinned until FrameStep. Remainder → F6c8 |
| F6c8 | FrameStep glue + the last three residuals | done (part) | w16 | 1fb64b9 | guard/leaf branch, cover→loop seam, and the centre loop PROVED (`CLInv` invariant, budget = per-centre **sum** via tail-sum potential); `frameStepAll_of_cover_step` concludes verbatim `FrameStepAll` from `CoverAllIn` + `CentreStepAll`; `rootLoadSpec_of_csrLoad` concludes verbatim `RootLoadSpec` from `RootCsrLoadAll`. **Finding 1 (scope)**: `EncodesGraph` permits duplicate neighbours, `GraphCsr` forbids — root load must dedup (mark-array, O(n+m)). **Finding 2 (statement gap)**: `TopScatterSpec` pre is `BlockPost` alone, no scratch lengths — IMP+ can't allocate, no honest `scatCom` speccable; fix = length-only top-scratch descriptor threaded via `hscrLen` pattern. Remainder → F6c9a/b |
| F6c9a | `CentreStepAll` — the per-centre body | done (part) | w17 | b0c947c | the recursion window DISCHARGED: `centreStepAll_of_prep_read` concludes verbatim `CentreStepAll` at `centreBody prepC readC` from two straight-line residuals — **`CentrePrepAll`** (child construction: cluster-row read → restrict → BFS 2R → supports → profilesMS at `preG` → isolate → load, delivering verbatim `BlockPre` at `childArena`) and **`CentreReadAll`** (scatters on isolated child + `bcExpr` readback, `CLInv u → CLInv (u+1)`); parent invariant crosses the inner block by `Spec.frame` + level-name freshness; budget `KP + KB(child) + KR`; `frameStepAll_of_cover_prep_read` end-to-end. Verified non-gaps: `restrictEmb`/`childEquiv` `rfl`; `inv_child` any-centre ⇒ **F7's `Adm` must be `Inv`-based**. Remainder → F6c10 |
| F6c9b | TopScatter fix + `CoverAllIn` + `RootCsrLoadAll` | done (part) | w18 | f7f9f43 | the statement fix landed: `TopScatterSpec` pre gains a length-only `Scr` (threaded from `Scr 0` via `specArrsLength` + one `hscrLen0` hypothesis; conclusions/budgets unchanged); **`topScatterAll_of` discharges verbatim `TopScatterAll`** with a real per-atom program (glue + column extraction to `FinBitsW` + landed `scatterCom` verbatim + bit store; `av` reads exactly the written bits; `unrollAux ≡ unrolledTables` by `rfl`); duplicated atoms harmless. `CoverAllIn`/`RootCsrLoadAll` not started — **flag: the GKS sweep needs a peel-masked BFS** (`bfsCom_specW` computes distances in the full arena graph). Remainder → F6c10a/b |
| F6c10a | `CentrePrepAll` + `CentreReadAll` | done (part) | w19 | 945aeef | the seams PROVED: `unrollAux_succ_of_ne_bot` (recursive table = `RowEval` after the leaf guard), `tablePartial_succ`, `bcExprA` full evaluation (compiled row = `RowEval`'s bit under `1 < B`), atom membership in `levelFml (j+1)`; `centreStepAll_of_childLoad_rows` concludes verbatim `CentreStepAll` from TWO machine residuals — **`ChildLoadAll`** (restrict→bfs 2R→supports→profilesMS→isolate chain + glue, delivering the windowed contract at `Impl.ofArena childArena` with `htabF (j+1)`, level-`j` names untouched) and **`ReadRowsAll`** (write exactly the centre-`u` rows at `RowEval`'s bits). F7 notes: channel content per child arena; descriptor tower guarded to `j+1 ≤ depth`. Remainder → F6c11 |
| F6c10b | `CoverAllIn` + `RootCsrLoadAll` | done (part) | w20 | d7f22ca | **`RootCsrLoadAll` DISCHARGED outright** (`rootCsrLoadAll_csrLoadCom`: row-stamped mark-array dedup, O(n+m) at `70|x|+20`; scope findings — `adj_iff` is an iff ⇒ no self-loops, both directions present, dedup only). `CoverAllIn` split at its own seam: `coverAllIn_of_order_sweep` verbatim from **`CovOrderIn`** (rank array of `ord`'s order) + **`CovSweepIn`** (rank array → `CoverStageSpec` post). Findings: ordering must be computed inside `covC`; **`timedGreedyRoutine` NOT machine-matchable** (choice-picked `elimRank`) — headline binds `∃ ord`, F7 instantiates a machine-defined min-degree peel (attains `elimBound`, sInf clauses stay provable; residuals parametric in `ord`); peeled BFS must be a frontier-queue over a **deletable adjacency structure** (full-pass rounds bust `sweepCharge`). Remainder → F6c11 |
| F6c11 | the four machine passes | done (part) | w21+w22 | a2e8b61 | w21: `machChild_eq_ofArena` + `ChildLoadParts` + `htabF` canonicity kit + readback bit bridges (see w21 note in log). w22: `DelAdjSt` (deletable adjacency, full bridge algebra; deletion priced at CURRENT degree inside `sweepCharge`), `covSweepIn_of_build_peel` verbatim from **`CovAdjBuildIn`**+**`CovPeelIn`**; **`mdOrderingRoutine R`** — the machine ordering (min-degree peel, `mdRank` replacing the choice-picked `elimRank`) with the FULL six-clause `AugChainData` proved (`mdRank_backDegLE` resolves clauses 5–6: optimal elimination of the AUGMENTED graph); `covOrderIn_of_aug_mdPeel` verbatim from **`CovAugAdjIn`**+**`CovMdPeelIn`**. Remaining SIX program residuals → F6c12 |
| F6c12 | the six machine programs | wip | w23 | — | **w23 dispatched on four of the six** (see log); `CovPeelIn`+`CovAugAdjIn` held for w24. Scope finding: `AdjBuildIn`/`AdjDeleteIn` (`SolveSweepAdj.lean:308,325`) are contracts with **no programs** — three of the six consume them, so each is folded into the worker that needs it rather than minted as a leaf. per-centre: (1) `ChildLoadPartsAll` (`SolveMachPrep`: stage composition + glue at `machChild`), (2) `ReadRowsAll` (`SolveSegRead`: programs+frames only — bit bridges landed); cover: (3) `CovAdjBuildIn` (O(N+ns) build + rank inversion into `OrdArr`), (4) `CovPeelIn` (queue-BFS peel over `DelAdjSt` to `CtrArr`/`ClusterCsr`; `Lib.Queue`), (5) `CovAugAdjIn` (augmentation rounds leaving `DelAdjSt` of the augmented graph — E12's priced obligation), (6) `CovMdPeelIn` (min-degree peel to `RankArr` of `mdOrderingRoutine`); then KB pin + `KsChargeBridge`, then F7 (repin `ord := mdOrderingRoutine R`, owes `time` as before — F5's `coverOrderingTime_of_nowhereDense` used `timedGreedyRoutine`, check transfer or rerun at `mdOrderingRoutine`) |
| F7 | discharge the endorsed axiom | waiting | — | — | needs F6c10a+b, then KB pin + `KsChargeBridge`; `Adm` must be `Inv`-based (w17 finding); then: `Adm` at the run tree (`mkSetup_memLeaf_eq_bot`), instantiate `SolveSpec` via `solveSpec_closed`, `q`/`c` per `hspan`, `temps ≥` boolean depth, `T x := L.const·mcK`, reconcile `Ks` with `exists_mcChargeMS_T`, ∃-close with the `conclusion:` header |

## Campaign log

### 2026-08-24 — wave 23 dispatched: four of F6c12's six machine programs

Fresh session, fresh container, cold start from this ledger. Two environment
facts worth keeping, because both cost time before any leaf could move:

- **The container had no `.lake/build` at all.** `capture-seed.sh` installed
  all nine submissions (every sibling `identical`; ND-MC itself `DRIFTED —
  partial reuse`, its capture predating the whole campaign at
  `4af91eadd121`), after which `lake build` replayed ND-MC's own drift —
  3525 jobs, one-time. Seeding `w23` off that took 3 s and replays in 4 s.
  A worktree cannot be seeded before the main checkout is built; budget the
  main build first in any fresh container.
- **Local `main` is not this campaign.** `git merge-base main
  claude/ndmc-1om1vl` exits 1 — no common ancestor. `816e5cc` is an
  unrelated lineage; the campaign is `claude/ndmc-1om1vl` = `origin/main` =
  `783eb34`. Worktrees must name **`claude/ndmc-1om1vl`** as the base, and
  that branch is the supervisor's checkout. Naming `main` here would branch
  from a tree that has never seen the campaign.

**The baseline gate was run before dispatch and is green** (`concepts` 10 s,
`proofs` 1m55s, inspector 27 s; 8 pre-existing warnings, all
proof-dependency/draft-dependency). This is the w1 lesson applied: that gate
was red on `main` for a reason no leaf caused, and nothing could have landed
until it was fixed. Note `lax build` drops the sibling overrides — the run
was followed by `.claude/sibling-overrides.sh`, and main re-replays in 2 s.

Wave 23 is four workers on four disjoint **new** files in `worktree-w23`:
**W1** `SolveMachPrepRun` (`ChildLoadPartsAll` — the five landed stage lifts
composed with glue, landing at `machChild`'s five regions), **W2**
`SolveMachReadRun` (`ReadRowsAll` — programs and frames only; w21 landed the
bit bridges), **W3** `SolveSweepBuild` (`CovAdjBuildIn`, including the
`AdjBuildIn` program), **W4** `SolveSweepMdPeel` (the `AdjDeleteIn` program,
then `CovMdPeelIn`).

Held for w24: **`CovPeelIn`** (the frontier-queue BFS over `DelAdjSt` with
row emission, first-hit `ctr` marks and deletion — the pass `sweepCharge`
actually prices) and **`CovAugAdjIn`** (the `R` rounds of tight
transitive–fraternal augmentation, which `SolveSweepOrder.lean:410` itself
calls "E12's priced obligation"). Both are algorithmic heavyweights; width
was capped at what one supervisor can review, not at the DAG's fan-out.

Scope finding entered at dispatch: `AdjBuildIn` and `AdjDeleteIn` are named
contracts with **no programs** ("nothing here proves a program",
`SolveSweepAdj.lean:78`), and three of the six residuals consume them. Each
is folded into the worker that needs it rather than minted as a leaf.

### 2026-08-18 — wave 12 dispatched: F6d + the two BFS-free F6c runs

Fresh session, cold start from the ledger. Wave 12 is three workers on
disjoint new files in `worktree-w12`: **F6d** (`SolveBfs.lean` — the shared
BFS-by-rounds command, generalizing run 1's `markCom` to deliver exact
truncated distances at `ImplBfs.BallTable`, the seam `descend`/`bfsSupports`
and the `vsrc` route already consume), **F6c2** (`SolveBlocksRestrict.lean` —
`restrictCom`/`isolateCom` against `MArena.restrict`/`isolate`, rank-scratch
renumbering self-cleaned at touched entries), **F6c3**
(`SolveBlocksBotCom.lean` — the `firsts` table build + the compile-time
generated evaluator, target `botEvalT` verbatim). Chosen because they are
the only F6 stages that do not consume F6d's BFS; supports/profilesMS/cover
sweep/composition follow once F6d lands. Workers do not touch the root
module; the supervisor adds the three imports at landing.

### 2026-08-19 — w13 lands: the machine has every routine (`7736b66`)

All four remaining routine stages are IMP+ programs with `Spec`s landing on
the frozen abstract identities — 13.4k lines, the heaviest wave. What is now
true: **every §4 operation exists at every layer** — abstract, NREST, and
compiled-machine `Spec`. The remaining distance to the axiom is composition
(F6c6: the frame chain and `ℓ+1` levels closing `SolveSpec`, with the
windowed-region contract the exact-length seam demands) and then F7's
∃-close. Two findings entered the permanent record: `Driver.setEquiv` was
Classical-chosen while its consumer's docstring said "sorted" — repinned to
the sorted enumeration under D3/E7's any-bijection license (the read-the-
theorem lesson, sixth occurrence); and exact-length CSR regions cannot serve
a per-centre loop over different-sized children — the composer owes the
prefix-CSR variant. Process: one worker ran git against its packet (benign,
disclosed); two cross-file name collisions fixed at review; one worker
resumed cleanly after a connection drop.

### 2026-08-18 — w11 lands in full; the session closes here

F6c's run-1 report arrived during wrap-up and was reviewed and landed
(`9996e30`), after F6b (`c4cde5b`). The wave is complete. Two supervisor
cwd slips during the wrap-up landings (a doubled worktree path, and an edit
applied to the worktree's root module instead of main's) were both caught by
the gate and fixed — the gate earned its keep twice in twenty minutes.

**Correction, written minutes later:** a second supervisor session picked
the loop up from this ledger while this one was wrapping — it landed F6c
first (`7bad766`; this session's `9996e30` was a benign near-empty duplicate),
landed **F6d as `SolveBfs`** (`ab14f30`, the shared bounded BFS at
`BallTable`), and dispatched wave 12 (F6c2–F6c5). The remaining stretch is
theirs: the F6c2–F6c5 rows above, then **F7**'s ∃-close. Everything else —
the mathematics, the abstract algorithm, the cost chain to the axiom's own
`T`-clause, the codegen skeleton, the frame contract, and the first routines
down to IMP+ — is landed, gated, and pushed. This session ends here; the
ledger did its job twice over.

### (superseded by the entry above) session wrap-up (Jan's call): the state, and the road left

Jan closed the session mid-wave-11. Landed this session: **all seventeen E
rows and F1–F5, F3b/F3c, F6, F6b** — the abstract theorem, the machine layer,
the discharged cover-time bound, and the codegen skeleton one `SolveSpec`
hole from the endorsed axiom, with the `T`-clause number already proved
(`exists_mcChargeMS_T`).

**What remains, precisely** (the next session's cold start is this entry +
`git log`):

1. **F6c** — in flight at wrap-up; its checkpoint (if any files were written)
   is on `origin/worktree-w11`. Review against its packet, land or
   re-dispatch. Its scope: the per-frame state contract, the routine `Spec`s
   (botEval, greedyScatter, isolate, restrict, supports, profilesMS,
   cover-sweep), one conditional frame block.
2. **F6d** (minted at wrap-up) — the shared IMP+ marking-BFS command; three
   consumers wait on it (F6b's scatter sweep slot `hscat`, the supports
   stage, the profilesMS stage). Build it first.
3. **F7** — the ∃-close: instantiate `SolveSpec` from F6b's
   `solveSpec_of_rest` + F6c's blocks, pick `q`/`c` per
   `mcLayout_fitsWords`'s `hspan`, `temps ≥` the boolean depth (F6b's seam
   note), `T x := L.const·mcK`, reconcile `Ks` against
   `exists_mcChargeMS_T`, and write the theorem with the
   `conclusion: Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`
   header.

Known seams for the next workers: `Nat.decLe` vs `Classical.propDecidable`
at scatter guards (`if_congr` crosses it); zombie LSP servers of dead
worktrees eat container memory (kill by open-file path); pushes that report
"Everything up-to-date" wrongly — verify `ls-remote`, push by explicit
refspec.

### 2026-08-18 — w10 lands: one `Spec` obligation from the axiom (`9b4cdfa`)

What is now true: the endorsed axiom is reachable through exactly one named
hole. `mc_computesInTime_of_solveSpec` delivers `ComputesInTime` on the
axiom's input set verbatim, at `T = L.const · mcK`, conditional on
`SolveSpec` alone — the compiled solve stage's `Spec`. And the number that
fills `T` exists: `exists_mcChargeMS_T` bounds the whole program budget by
`c'·(|x|+1)^{1+ε}` with **no cover-time assumption** — F5's theorem consumed,
the honest routine pinned, the vacuity question answered in the object.

Hard-won shape facts, recorded so they are not relearned: the landed
`frameCharge` does NOT satisfy the headline (the profiles column gap is real
— F3b's MS budget is not an optimization but a correctness requirement of
the accounting); direct-κ against `dcost` is impossible (unbounded ratio);
empty centres are free in `dcost` but not in the program's ledger, so only
node-aggregate comparisons close. The session hit its usage limit mid-wave —
both workers resumed from transcripts with nothing lost — and zombie LSP
servers of deleted worktrees exhausted container memory (killed by open-file
path; future waves should expect this).

**The remaining work is F6b + F6c (the Sepref descent), then F7's ∃-close.**

### 2026-08-18 — w9 lands, and the design's one unproved claim is unproved no more (`7ed61d3`)

**`coverOrderingTime_of_nowhereDense` is a theorem.** O7 — "the one that
decides the project" — is decided: the cover's time bound, assumed since E0,
is discharged by the honest witness (`timedGreedyRoutine`, `steps :=
chainCharge`), at the true exponent `1+δ` (the interface's `1+2δ` a
weakening), with the greedy chain's in-degree bound found already landed by a
route the plan had mislabeled (`greedy_chain_joint_inDegLE`, not the wcol
chain's `:1076`). Vacuity honestly flagged: the Prop was always cheaply true
at `steps := 0`; the deliverable is the witness, and `le_chainCharge` pins it
as real. F3's profiles blocker dissolved consumer-side (F3b's virtual source;
the bridge's source-revisit subtlety handled by strong recursion). F4
composed the levels and landed `mcProg_headline`. Wave 10 is F3c + F6; then
F7 discharges the endorsed axiom.

### 2026-08-18 — the discharge campaign opens (Jan's authorization)

Jan, in his own words: *"Please discharge all the remaining ones."* The
remainder map of `Headline.lean` becomes the F DAG (execution-plan.md, F
section). Recon before minting: the greedy-chain assembly pieces are all
landed; `exists_augChain_inDeg_subpolynomial` already carries the md ≤ c·m^δ
per-round mathematics; and the Refine tower has a landed end-to-end
`ComputesInTime` precedent (`Codegen/Examples/EndToEnd.lean`), so the codegen
path is exercised, not hypothetical. **Wave 8 (`w8`) is F1, F2, F3.**

### 2026-08-18 — w7 lands E13, and the ledger is complete (`b2df405`)

**All thirteen leaves (plus the three E12 sub-leaves) are done.** What the
campaign now holds, end to end: the cover layer's four owed guarantees with
the time bound as one named hypothesis (`CoverOrderingTime`); the slackened
cost induction with no constant side conditions; the cluster-restricted game
record with its transports; the compaction; the schedule; the abstract driver,
correct for every ordering and affordable under the one hypothesis; the
`ℓ+1`-level unroll computing exactly the same tables at exactly the same cost,
with the run-tree invariant threaded end to end; the complete machine-routine
layer with charges and identities; and the composition `headline_encoded` —
the endorsed axiom's statement, reachable conditionally, at its own input
measure, with the full iff on every graph.

**What this campaign deliberately does not contain**, mapped precisely in
`Headline.lean`'s remainder section, is the successor work: (a) the composed
NREST driver program over the `Impl*` routines (the largest block), (b)
Sepref/Codegen to a `Lax13.Ram.Program` plus a CSR front end (which exists
nowhere yet), (c) the `CoverOrderingTime` discharge — the NOdM formalization,
a campaign of its own — (d) the word-size condition spent against the static
layout, (e) the machine-side `T` arithmetic. The endorsed axiom stands until
those exist; nothing found in seven waves contradicts its shape.

The loop's own termination condition is met: no leaf is ready, none is
blocked. **The campaign is complete.**

### 2026-08-18 — w6 lands: the machine layer is complete (`84ae503`)

What is now true: every routine of §4's table exists with its charge and its
identity to the abstract driver — twelve of thirteen leaves done, and only the
composition (E13) remains. Three findings from the wave:

- **E12c's fibre lemma holds with no side condition** — the peeled-ball IS
  the wreach fibre, at any radius; the strict peel and the non-strict
  endpoint clause are the same condition read through `not_lt`. But **(★)'s
  closing needs `1 ≤ r`**, which GKS assume silently and which is false at
  `r = 0` (a star refutes both `d_< ≤ |wreach|` and `N_> ⊆ X_v`). Explicit
  hypothesis, spent in two lemmas; the design's `R ≥ 1` supplies it.
- E12b's identities are `rfl` because it reuses the driver's own cluster
  enumeration — pick implementation names to match the abstraction's and the
  seam disappears.
- E12d's marker class is `univ`, so its naive per-member iteration prices
  `classSum ≥ n`; semantically the marker row is free (`y := z`). A
  consumer-side special-case lemma is available to E13 if the constant
  matters; it does not affect the exponent.

A container restart hit mid-gate; the filesystem survived, the gate was
re-run green, and nothing was lost — the checkpoint discipline was not
needed this time but would have bounded the loss to one wake interval.

### 2026-08-18 — w5 lands: the unroll, and the machine layer opens (`a1d9294`)

What is now true: §8 step 4b is closed — the driver runs as `ℓ+1` static
levels computing *exactly* `tables`, priced identically, with the run tree
reified and the invariant threaded end to end (`mkSetup_memLeaf_eq_bot`). And
the machine layer has its first three routines with their identities to the
abstract driver: the scatter atoms, the leaf evaluator, and BFS-at-`B₀`.
E12 split as predicted: E12b (restrict/isolate), E12c (the cover sweep — the
sole superlinear routine, scheduled first per §6.2 ⟨A⟩), E12d (recordProfiles).
E13 now waits on exactly those three.

Findings worth keeping:

- **`descend_spec` gives exact distances** — the tower's `Post` is strong
  enough to reconstruct the BFS tree consumer-side; no new tower program was
  needed for `bfsSupports`. The tower lacks multi-source BFS; E12d's honest
  route is `(m+L)` single-source calls, matching §6.3's charge.
- **`bfsSupports` delivers "IS a witness-walk support", not "= `genSet`'s
  chosen walks"** — the latter is neither provable (Classical choice) nor
  needed (the driver needs *some* walk support). Consistent with E9's D6
  scoping.
- Toolchain drift notes for future workers: `Fin.find` is proof-carrying now;
  `List.pairwise_lt_finRange` → `sortedLT_finRange`; `Finset.toList` is
  noncomputable — evaluators use `decide`.
- E12's worker flagged §7's "edge half is owed" as load-bearing context —
  it was stale (E3 landed it); fixed in this landing. Doc drift after a leaf
  lands is real: when a landing supersedes a design sentence, fix the
  sentence in the same boundary.

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
