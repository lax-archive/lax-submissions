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
| F6c12 | the six machine programs | wip | w23+w24 | — | **residual (4) `CovPeelIn` SPLIT, with the cost envelope PROVED** (w24, landed): `covPeelIn_of_sweep_group` verbatim from **`PeelSweepIn`** (the ascending peel: per-centre frontier BFS at `2R`, first-hit `ctr`, log append, delete via `AdjDeleteInW`) + **`PeelGroupIn`** (two stable counting sorts). The budget *shape* is pinned — `peelK a b c = a·N + b·mass + c·edge`, only constants free — and `peelBudget_le` proves it `≤ a·N + b·N·D + c·N·D²`, i.e. §7's `a·N^{1+2δ}`; `peelBudget_le_sweepCharge` ties it to the landed `sweepCharge`. Finding: **the sweep cannot emit `ClusterCsr` directly** — `ClusterCsr` anchors offsets in *carrier* order with rows *ascending*, the sweep runs in `π` order with BFS level order, and a per-centre sort is `Θ(N²)`, the same envelope break; hence the log + counting sorts at `O(N + mass)`. Second finding: the BFS budget is `Σ_{w∈X_u} d_<(w)` **only if** it does not expand the final level and clears marks by re-walking its own reached list; `ca` arrives uninitialized, so an `O(N)` sentinel pass is owed inside `a·N`. **residual (6) `CovMdPeelIn` DONE** (w23, landed) + the swap-delete program (`delAdjCom`, `kd d = 54d + 5` at the *current* degree; the unlink needs no degenerate branch because the loop peels `v`'s row from the end, so every intermediate state is a genuine region state). **`AdjDeleteIn` as landed is FALSE — proved** (`not_adjDeleteIn`, for every `B`, program and budget): it quantifies over every `N` and `DelAdjSt` state and relates none to `B`; at `N = B+2` with one edge the postcondition demands a store at index `B`, impossible under `Run B`. `AdjDeleteInW` = the same with one added hypothesis `N + N² < B`, discharged at `mcB` from `1 ≤ q`. This is the *proved* form of the `AdjBuildIn` gap below — both landed contracts of `SolveSweepAdj` §3 are defective, not merely hard. **⚠ COST: `Kmp = 86N² + 43N + 14` is a full carrier scan per round, NOT the bucket queue — it does NOT fit §7's cover term `a·N^{1+2δ}`. See F6c13; F7 cannot close until that lands.** **residual (3) `CovAdjBuildIn` DONE** (w23, landed): `covAdjBuildIn_bldCom` verbatim; `bldK N ns = 93N + 58ns + 30`, every pass priced; mate pass emits both copies at `u < w`, skips at `w < u`, so no mate is searched. **Statement-gap finding: `AdjBuildIn` (`SolveSweepAdj.lean:308`) is undischargeable as stated** — it quantifies `∀ {N} (G) (ns)` at one fixed `B` and one fixed command with both figures only in array lengths, and **IMP+ has no array-length primitive** (`Imp.lean:158` — `Com` is skip/assign/store/seq/ite/while/read/write). `AdjBuildAt` is the same contract with the figures in named cells `nN`/`nS` and inside the word bound; the residual routes through it off `ArenaStW`'s cells + `mcB`, no clause weakened. Same species as F6c8's `TopScatterSpec` gap. **`AdjDeleteIn` (`:325`) needs the same audit** — it names `vx` so it may not need `N`, but its stores still need the word bound. **residual (2) `ReadRowsAll` DONE** (w23, landed): `readRowsAll_of` verbatim at `readPassCom = topAtomsCom ; readLoopCom`; all five clauses incl. no-reallocation; axioms identical to the landed `topScatterAll_of`/`centreReadAll_of_rows`; budget exact (`Spec.mono` by `rfl`). Finding: the centre guard `ca[v] = ctr` is load-bearing — the cluster row enumerates `cluster u`, **strictly larger** than `{v | centre v = u}` (covers overlap by design; that is what `D(N)` counts), so clause 2 fails without it. **residual (1) `ChildLoadPartsAll` is BLOCKED — see the ⟨D⟩ finding in `algorithm-v2.md` §5 "The batch"**: `DriverArena.batchRoot` is `genSet`/`pathSet`, a `Classical.choose` walk no program can output, while `childArena.G` isolates `range batchFn` and `profilesCom_specW` requires the batch region to already hold it. Needs a decision on landed abstract files; `hwalk` is existential so the repair direction §5 line 17 already names (`bfsSupports`) is available. **w23 dispatched on four of the six** (see log); `CovPeelIn`+`CovAugAdjIn` held for w24. Scope finding: `AdjBuildIn`/`AdjDeleteIn` (`SolveSweepAdj.lean:308,325`) are contracts with **no programs** — three of the six consume them, so each is folded into the worker that needs it rather than minted as a leaf. per-centre: (1) `ChildLoadPartsAll` (`SolveMachPrep`: stage composition + glue at `machChild`), (2) `ReadRowsAll` (`SolveSegRead`: programs+frames only — bit bridges landed); cover: (3) `CovAdjBuildIn` (O(N+ns) build + rank inversion into `OrdArr`), (4) `CovPeelIn` (queue-BFS peel over `DelAdjSt` to `CtrArr`/`ClusterCsr`; `Lib.Queue`), (5) `CovAugAdjIn` (augmentation rounds leaving `DelAdjSt` of the augmented graph — E12's priced obligation), (6) `CovMdPeelIn` (min-degree peel to `RankArr` of `mdOrderingRoutine`); then KB pin + `KsChargeBridge`, then F7 (repin `ord := mdOrderingRoutine R`, owes `time` as before — F5's `coverOrderingTime_of_nowhereDense` used `timedGreedyRoutine`, check transfer or rerun at `mdOrderingRoutine`) |
| F6c13 | the min-degree peel at a **linear** budget | superseded | w24 | 433bfac | **BLOCKED on a tie-break decision — `O(N+m)` is impossible at the residual as stated.** w24 landed the amortization kit but not the discharge, and deliberately did not land a second quadratic. The obstruction is `minDegVert`, not the data structure: `CovMdPeelIn`'s postcondition pins the output to `mdPerm (mdChain A.G R).toGraph`, a function of the **graph**, while a bucket queue's `O(1)` pop is a function of the adjacency **row order**, which `DelAdjSt` deliberately leaves free — Matula–Beck is linear precisely *because* its pop is arbitrary. Three counterexample families kill the obvious canonical disciplines (perfect matching; hub+pendants; tail insertions). **Landed and reusable**: `livePot_erase` (peeling `v` drops the potential by exactly `2·|nbrsIn|`), `offF_eq_slotCount`, `sum_dg_eq_livePot`, **`peelLoop_linear`** / `peelLoop_linear_cursor` (a `while` whose turns cost `a + b·d` in the *current* degree runs inside `a·N + b·slotCount`), `minDeg_le_minDeg_erase_succ`, `eq_minDegVert_of_bucket`. **And the upstream unblock is PROVED**: `selOrderingRoutine_data` gives the full six-clause `AugChainData` at **any attaining selection**, with `selOrderingRoutine_mdSel` for conservativity — so re-pinning the tie-break costs the ordering routine nothing. Routes: (1) re-pin to a machine-canonical attaining selection (`SolveSweepOrder` edit, true `O(N+m)`, and P4 confirms it then serves **four** peel sites); (2) heap at `deg·N + index`, `O((N+m)·log N)`, no upstream change, still inside `a·N^{1+2δ}`. *Originally minted w23 from a cost defect the supervisor's own packet authorized.* The landed `covMdPeelIn_peelCom` is correct and verbatim but prices the peel at `86N² + 43N + 14` — a full carrier scan per round. §7 charges the whole cover routine (`covC = ordC ; swC`) at `a·N^{1+2δ}`, and at the root `N = n`, `δ = ε/(ℓ+2)`, so `N²` breaks the headline outright. The fix is the standard bucket-queue degeneracy ordering: buckets indexed by current degree, each vertex moving down one bucket per neighbour deletion, giving `O(N + m)` amortized — comfortably inside `N^{1+2δ}`. Owns a new file; restates `CovMdPeelIn` at the new `Kmp` and reuses the landed `delAdjCom`/`adjDeleteInW_delAdjCom` unchanged (the delete is already priced at the current degree, which is exactly what the amortization needs). `SolveSweepMdPeel`'s `eq_minDegVert` and `mdRankAux_peel_step` isolate the tie-break and the countdown, so the new selection only has to hit the same `Finset.min'`. |
| F6c13b | the linear peel at a **re-pinned** tie-break | done (part) | w25 | 4a411e3 | **Landed: the re-pinned residuals and the amortization; the program is F6c13c.** `covOrderIn_of_aug_selPeel` concludes `CovOrderIn … (selOrderingRoutine sel R) …` verbatim, same shape and summed budget as the `md` original; `CovAugAdjSelIn`/`CovSelPeelIn` are the two residuals at a freed tie-break, every clause identical; the conservativity bridges are **iffs**, so the `md` pair is the special case. **This corrects the supervisor's own route-1 spec** — "counting-sort the rows once" is *not* sufficient on the landed contracts: `delAdjCom` is a swap-delete (`adjCore_unlink` moves the row's last live entry into the hole) and `AdjDeleteInW`'s postcondition is just a `DelAdjSt`, which carries **no row-order information** (both verified against the definitions). A sort at entry does not survive deletion. Proved instead: `MinDegSel.ofMin` (a bucket pop *is* a `MinDegSel`), `selRankAux_peel_step`, `card_nbrsIn_pick_eq_minDeg`, `staticPot`/`_erase`/`_univ`, **`peelLoop_linear_static`** and **`peelLoop_linear_static_cursor`**. *Original decision:* **route 1.** Re-pin the tie-break to a machine-canonical *attaining* selection rather than accept a `log` factor — true `O(N+m)`, and one canonical peel then serves **four** sites (the base peel, the `R` fraternity peels, the final peel). Free by w24's `selOrderingRoutine_data` (six-clause `AugChainData` at any attaining selection) + `selOrderingRoutine_mdSel` (conservativity). Implemented by **adding**, not editing: new `CovSelPeelIn` + `covOrderIn_of_aug_selPeel` beside the landed pair, consuming w24's `peelLoop_linear`/`minDeg_le_minDeg_erase_succ` and w23's `delAdjCom` at `AdjDeleteInW`. Route 2 (heap at `deg·N + index`, `O((N+m)log N)`) rejected: still inside the envelope, but needs a δ-dependent `log N ≤ C_δ·N^{2δ}` in Lean, and buys a worse exponent for no less work. |
| F5b | the cover cost column at the **selection** | done | w25 | 0ee379a | **Landed.** Headline **`exists_mcChargeMS_T_selOrdering`** — axioms *identical* to the landed `exists_mcChargeMS_T`, and the setup-parametric `exists_mcChargeMS_chargeTotal_le_sel` sits at the clean three, confirming the fourth is statement-inherited. Exponent is F5's own `f·m^{1+δ}`, same constant shape, **not** the interface's `1+2δ` (the weakening is confined to the `_double` variant, where the interface asks for it). Hazard 2 resolved *by construction*: `mcChargeMS` reads its `OrderingRoutine` only through `.order` (`.steps` is read only by `Unroll.frameCost`, the abstract recursion), so both capstones are proved once for any `ord` agreeing on `.order`, then instantiated at `selOrderingRoutine`, `timedSelRoutine` and `mdOrderingRoutine` — **`KsChargeBridge`'s two sides can carry one `ord`**. Anti-vacuity kept (`le_selChainCharge`, `le_timedSelRoutine_steps`, `coverCSel_order_eq_steps`). Beyond the packet, and needed: `coverProgSel`/`coverProgSel_le_spec`, because `ProgCover.coverProg` names `timedGreedyRoutine` in the value it **returns**, so the cost transfer alone would not let F3's `hcover` be filled at the machine routine. Finding: `ProgCover.lean`'s module docstring cites `exists_chainCharge_le` for the order half, but the proof consumes `exists_chainCharge_le_double` — same bound, wrong citation. *Original mint:* | **The ledger's open F5-transfer question, settled by the panel and now dispatched.** The theorem does *not* transfer — `coverOrderingTime_of_nowhereDense` is a bare `∃ A`, so F7 cannot extract a routine from it, and the whole column (`chainCharge`, `coverC`, `exists_mcChargeMS_T`, `KsChargeBridge`) names `timedGreedyRoutine` **literally**. The *proof* transfers verbatim: `greedy_chain_joint_inDegLE` (`AugmentedDensity.lean:966`) is stated at an **arbitrary** chain and `mdChain` supplies all three hypotheses; the four `levelCharge` bounds are already at an arbitrary `Orientation`. Stated **parametrically at `selChain`/`selOrderingRoutine sel R`** so F6c13b's re-pin costs it nothing, with the `mdOrderingRoutine` corollaries via `selOrderingRoutine_mdSel`. Headline: the `exists_mcChargeMS_T` analogue — the one F7 consumes. **Required for F7 regardless of every other decision.** |
| F6c13c | the **static-adjacency** peel program | **done** | w26+w27 | see log | **`covSelPeelIn_bucketPeelCom` discharges `CovSelPeelIn` with every clause verbatim** at `Kmp = 313·A.N + 118·slotCount((selChain (bucketSel A.N) A.G R).toGraph) + 40` — **no `A.N²` term**. **`covOrderIn_bucketPeel` is w26's `covOrderIn_bucket` with `hmp` gone**, so `CovOrderIn` at `selOrderingRoutine bucketSel R` is unconditional on the peel side. This closes the chain that opened when w24 proved `O(N+m)` *impossible* at the original tie-break: w24 found the obstruction, w25 re-pinned and proved the re-pin free, w26 built the bucket machinery, w27 wrote the program. **Finding — w26's kit was true but inapplicable**: `peelLoop_linear_bucket` charges a round `a + b·|N_F(v)| + e·rise`, but a *lazily-cleaned* stack's stale skipping is bounded by **earlier** rounds' pushes, not this round's degree, so that rule cannot pay for it. `peelLoop_linear_static_cursor_lazy` / `peelLoop_linear_bucket_lazy` add a fourth potential term over cells in the stacks (total pushes `N + slotCount F`), leaving the budget *shape* unchanged. **`AdjSortIn` is BYPASSED, not discharged** — `rowList F v := (List.range N).filter (adjB F v)` is canonical by construction, so `orderEmbOfFin_unique` is unneeded and the entry sort is a concrete transpose at `27m + 22N + 6` rather than w26's unquantified `K`. That retires one of w27's two "the DAG is deeper" findings. Space: `Smp` asks `n²+n` stack cells — **space, not time**, the same shape as the adjacency region the pass already reads. | see log | Bucket selection built and composed, **but `CovSelPeelIn` is still a hypothesis, not discharged** — `covOrderIn_bucket` concludes `CovOrderIn … (selOrderingRoutine bucketSel R) …` *conditional* on it. Landed: `bucketSel`, `bucketPick_mem/_card/_bRun`, `guardPick_some`, `peelLoop_linear_bucket`, `selRank_eq_selRankAux_bRun`, `selRank_bPop`, `linearPeelBudget`. What remains is the round **program** meeting `CovSelPeelIn` at `bucketSel`. | The program F6c13b's amortization is waiting for. Design, forced by w25's finding: a peel that **never writes the adjacency arrays**, so one counting sort at entry makes the rows a function of `G` for the whole run and the bucket replay models only the buckets. A round then walks `v`'s **original** row — priced by `staticPot`, not `livePot`. Owes: the counting-sort pass + its spec; the abstract bucket replay with its partition invariant; the round program at `O(1) + O(\|N_F(v)\|) + O(cursor rise)`, fed to the landed `peelLoop_linear_static_cursor`. Est. 2500–3000 lines. Consumes `MinDegSel.ofMin` (the pop obligation is *attainment*, not least index) and `card_nbrsIn_pick_eq_minDeg` (which licenses the cursor via `minDeg_le_minDeg_erase_succ`). Note it must **not** use `delAdjCom`: that is the swap-delete whose row scrambling is the whole reason for this design. |
| G1 | ⟨D⟩: the batch off the **channel** | done | w26 | see log | **THE ⟨D⟩ FINDING IS REPAIRED.** `Arena` gains `chan : Fin N → ℕ → List (Fin N)` (ℕ-indexed field, so all 565 `Arena Λ n₀` ascriptions survive); `batchPar = {u} ∪ {z \| ∃ e < A.hist.length, z ∈ A.chan u e}`, `batchRoot = up '' batchPar` — **`genSet` and `pathSet` leave the driver entirely** (they stay live in `ReachedS`, proving Splitter wins). `Inv` gains the two channel clauses. **`batchSet_ncard_le`'s bound is unchanged** at `1 + A.hist.length*(2R+1)` (now taking the row-length clause as `hchan`), so `hwidth` and the schedule are untouched. Step 0 landed first: `ProgFrame`'s supports BFS runs at `2*S.R` (`SolveFrameStages:387`'s instruction; the w14 stale figure, fixed). Relocation file `DriverBfsTree` + mechanical fixes in `ImplBfs`/`ImplRestrict`/`ProgCharge`/`SolveBlocksSupports`/`SolveMachPrep`. **Headline axiom footprint unchanged** (`mkSetup_mc_correct`, `headline_abstract`, `headline_encoded` all verified). | **Supervisor decision (2026-08-24, full authority): Option 2**, per `decisions-2026-08-24.md`. Option 1 is dead as scoped (`pathSet` descends the round's *unrestricted* arena `e.2`; the affordable pass BFSes `preG` — the gradient walks provably differ, so canonicalizing only converts "no program can" into "only a `Θ(N·‖A‖)`-per-node program can"). Option 3 is semantically near-free (4 call sites in 3 lemmas, ~40 lines of real mathematics) but buys **no instance** — the per-round-recompute channel fails `hwalk` because ancestor connectors are edge-isolated, so the batch collapses to `{u}`, verbatim §5 ⟨A⟩'s recorded vacuity — and costs ~418 call-site edits. Two analysts converged independently on the **inherit-and-patch channel** (§5 line 23), and the machinery is already landed: `MArena.restrict` carries old columns down filtered (`ImplRestrict.lean:204`), `supportsCom_specW` writes exactly one column and inherits the rest (`SolveFrameStages.lean:410`) — both verified by the supervisor. Plan: (0) **prerequisite** — fix `ProgFrame.lean:392`'s supports radius `S.R → 2R` (`SolveFrameStages.lean:387` says instantiate `2R`, "never `S.R`"; inert today only because `_DT` is discarded — the same stale figure w14 flagged); (1) `chan : Fin N → ℕ → List (Fin N)` as an **`Arena` field**, ℕ-indexed (a field leaves all 565 `Arena Λ n₀` ascriptions valid; an index would not); (2) `batchPar := {u} ∪ {z \| ∃ e < A.hist.length, z ∈ A.chan u e}`, `genSet`/`pathSet` leaving the driver entirely (they stay live in `ReachedS`, proving a different theorem); (3) two new `Inv` clauses (length + walk witness). ~700–1100 lines, concentrated in `DriverCorrect.inv_child`. **Edits landed files — runs in its own wave, alone.** |
| F6c12-5a | the augmentation frame (base / rounds / sym) | done (part) | w27 | see log | **`covAugAdjIn_of_base_rounds_sym` concludes the landed `CovAugAdjIn` VERBATIM** at `sel = mdSel` (through w25's `covAugAdjSelIn_mdSel`), from `AugBaseIn`/`AugRoundIn`/`AugSymIn` and nothing else, at program `bsC ; (rdC)^R ; syC`. The chain is read off its definition, not assumed: **`selChain_zero` and `selChain_succ` are both `rfl`**, compiler-checked, and `AugRoundIn`'s postcondition is written in the `greedyStep` form the emit proves. Budget: three pinned shapes (constants free, the `peelK` model), each a term of `selChainCharge`; `augChainCost_le_selChainCharge` then `exists_augChainCost_le` gives `f·m^{1+δ} + O(R)` via w25 — **one δ inside §7, no new cost function defined, no `N²` anywhere**. `augSymIn_of_symCsr_build` is a real composition with the landed `adjBuildAt_bldAdjCom`. Findings: (i) **`AdjBuildAt` asks for a plain `GraphCsr`, whose `Csr` clause pins array lengths *exactly*, while the arena supplies its CSR only behind `winA`** — so the landed build is directly usable for the *symmetrization* (fresh arrays) but **not** for the base's build, which must go the `covAdjBuildIn_bldCom` route. That is the sole reason `AugBaseAdjIn` is stated rather than discharged. (ii) `sq_lt_mcB` was `private` — **un-privatised at this landing** so the next discharger need not reprove it. (iii) **the handshake `slotCount G = 2·arcCount (baseOr G π)` is not landed anywhere**; the base budgets are therefore stated at `arcCount (selChain … 0)` directly, keeping the conversion out of the interface. Remainder: `AugBaseAdjIn`/`AugBasePeelIn`/`AugBaseOrientIn`/`AugSymCsrIn` → **F6c12-5a-ii**. |
| F6c12-5a-ii | the frame's four small passes | done (part) | w27+w28 | see log | **2 of 4 done.** `AugBasePeelIn` discharged (w28) at `394·A.N + 352·arcCount + 64`, no `A.N²`; both slot terms convert **by equality**. **The composition fact no packet anticipated: `bucketPeelCom` CONSUMES the region it peels** — its write set contains `dg` and `mt`, two of `DelAdjSt`'s four arrays — so `CovSelPeelIn` drops the region from its postcondition while `AugBasePeelIn` demands it back. The pass peels then **rebuilds from the arena's own CSR**, which the peel never touches; the rebuild writes exactly `{bao,baj,bdg,bmt}` so the rank array survives (`RankArr.of_eq`). Hence the proof routes through `bucketPeelCom_spec` + frame lemmas, **not** through `covSelPeelIn_bucketPeelCom` — the contract's postcondition is the wrong shape, not the program. Coefficients: `bn = 475`, `ba = 468`, closing at `k = 475`; `k` rose from 81 because the rebuild costs 81, the price of region-preservation. `AugBaseAdjIn` done (w27). |
| F6c12-5a-iii | `AugSymCsrIn` — the merge | ready | — | — | The transpose is landed (`transposeIn_tpCom`); what remains is the **merge** of `inN v` with `outNbrs D v` into a `GraphCsr` of `D.toGraph` — a program leaf the size of `tpCom`'s, with no landed counterpart. Three facts landed w28 aim it: `symCsr_ns_eq`/`_le` (**the `ns ≤ 2·arcCount` clause is an *equality*** at `Orientation.orients_toGraph` — nothing to spend), **`toGraph_step_add`** (the merged offset function is the **pointwise sum** of the input CSR's and the transpose's, so the offset pass is one add and one store per vertex, **not** a prefix scan), and `symCsrSizes`/`symCsrSizes_exact`. **Finding — the `AdjBuildIn` trap one level up.** `AugSymCsrIn`'s postcondition is a bare `GraphCsr`, whose `Lib.Csr` clauses are array **equalities**, and IMP+ `store` is `List.set`, so **no run changes a length**. The pass must therefore be *handed* `soO j` at exactly `A.N + 1` cells and `stO j` at exactly `2·arcCount D`; the windowed `≥` allocations the arena and every scratch descriptor supply are **not enough**. Not falsity — a binding requirement invisible in the contract text. **Supervisor decision: do NOT restate the residual at the windowed `SrcCsr`.** The worker showed restating would ease the merge, but also *proved* the requirement satisfiable as it stands — `augStInN`'s `nA` cell already holds `arcCount D` and the arena's `nN` holds `A.N`, so `Srd`/`AugSt` pin both lengths in terms of `σ` alone (`symCsrSizes_exact`). Churning a landed residual plus `adjBuildAt_bldAdjCom`'s packaging for convenience is the worse trade; the merge leaf gets `symCsrSizes_exact` instead. | **1 of 4 discharged.** `augBaseAdjIn_bldAdjCom` concludes `AugBaseAdjIn` **verbatim** at `81·A.N + 116·arcCount(selChain sel A.G 0) + 24`, `sel` free — inside the coefficient bounds (`bn ≤ k`, `ba ≤ 3k`) at `k = 81`. The `AdjBuildAt` trap was confirmed independently. **Bonus: the handshake this ledger recorded as *not landed anywhere* is now proved** — `sum_ncard_neighborSet_eq_two_mul_arcCount` (`D.Orients G → ∑ v, (G.neighborSet v).ncard = 2·arcCount D`, via `inN v ⊎ outNbrs D v` by `Orientation.asymm` then `TgtCoupling.sum_card_outNbrs`), converting `bldAdj_spec`'s `58·ns` into `116·arcCount` **by equality**; stated generally so the transpose leaf can reuse it. **Two findings that deepen the remaining DAG**: (i) **`linearPeelBudget` is not a budget proved of any program** — `SolveSweepBucketProg` §5 says so in terms ("the shape a peel pass built on §1–§4 *can* meet"), and its entry sort **`AdjSortIn` (`:343`) is itself an undischarged residual**; the only landed peel *program* is the quadratic `covSelPeelIn_peelCom_mdSel`. (ii) **No landed theorem anywhere concludes an `InNCsr`** — `SolveAugFrat` only defines and reads it — so `AugBaseOrientIn` is a fresh count/prefix-sum/scatter construction, not assembly. Remaining: `AugBasePeelIn`, `AugBaseOrientIn`, `AugSymCsrIn` (the last is naturally downstream of `TransposeIn`). | `AugBaseAdjIn` (via `covAdjBuildIn_bldCom`, *not* `AdjBuildAt` — see 5a finding (i)), `AugBasePeelIn` (the linear peel, pinned), `AugBaseOrientIn`, `AugSymCsrIn` (the transpose, owing `ns ≤ 2·arcCount`). All four have pinned budget shapes already; this is program text against fixed targets. | The two *free* thirds of `CovAugAdjIn`'s split: base peel = `bldAdjCom ; peelCom` composed, symmetrization = `bldAdjCom` again. Both are landed programs; this row is composition only. Waits on F6c13b (the peel it composes must be the linear one). |
| F6c12-5b | `FratCsrIn` | done (part) | w26 | see log | `exists_fratCsr` + the CSR-prefix kit (`graphCsr_fratPref`, `csrPrefix_fratPref`, `fratOff_succ`, `InNCsr.rows`, `fratNs_le`). **Budget verified**: `fratK_le : fratK … ≤ a*n + (b+c)*fratPairCount D + d` — exactly the pre-verified target, linear in `n` and `fratPairCount`. `arcCount_le_fratPairCount` is the bridge. Full semantic review of the `Spec` still owed. | **Not blocked after all** — the supervisor's "waits on F6c13b" was over-cautious: the peel runs *after* the fraternal graph is built, so this pass never touches it. Dispatched w26. Budget target handed to the worker rather than chosen by it: `fratPairCount D = Σ_w \|inN w\|²` is exactly the enumeration's size and `levelCharge` (`ProgCoverCharge.lean:150`) already prices it inside §7's envelope — the first leaf this campaign has dispatched with its cost target *pre-verified*. The fraternal enumeration: for `w`, for `x,y ∈ inN w` with `x<y`, emit `{x,y}`; regroup + dedupe into an exact `GraphCsr (fratGraph D)` (counting sort + row-stamped mark array, the `SolveCovLoad` pattern). Count `Σ_w \|inN w\|² ≤ N·d²`. Est. 2000–3500 lines. Waits on F6c13b. |
| F6c12-5c-i | `TransCsrIn` | done | w26 | see log | `transCsrIn_trCom` + `transCsrAt_decides` (the both-directions `O(1)` test the `pick` filter needs) + `transCsrAt_row`, `trOff_owner`, `trOuter_scan`, `trRow_lt_sq`, `transCsrAt_slots_le`. **Budget verified**: `trK_le : trK n (arcCount D) (transPairCount D) ≤ n*(27 + 23d + 30d²) + 13` under `D.InDegLE d` — the `transPairCount` shape, `O(n·d²)`. **Spec review done: this one IS a real discharge** — `transCsrIn_trCom` proves `TransCsrIn B … (trCom …) trK` with `trCom` an actual `Com` and explicit `Run` steps. **Status: done.** |
| F6c12-1a | the channel pin + residual 1's three programs | done (part) | w27 | see log | **THE SEAM IS CLOSED.** `chanTab S ℓp j A v e := A.chan v ↑e` is the witness; `chanTab_chanPin` holds **by `rfl`**, and **`chanTab_hhtab` discharges `SolveMachPrep`'s seam hypothesis by `rfl`**, so **`centrePrepAll_of_parts_chanTab` concludes `CentrePrepAll` verbatim with no `hhtab` left**. `mem_batchSet_iff_chanRow`/`_level` then supply both hypotheses of `mem_batchSet_iff_restrictHist`, so §5 line 19 reads off `htabF j A` — the table `BlockPre` actually puts in the region. All six pins stated **and witnessed** (`stdPins`); `prepAdm` is not merely satisfiable but **preserved by the driver's own recursion** (`prepAdm_root`/`_child`/`_admChild`). **The cast, priced**: the `hbf` pin costs *nothing* (`hb` is not a type index, only the channel stride); the `ℓp` pin costs one cast at the hand-over and is **definitionally invisible on the canonical witness**, because `Fin.cast` preserves `.val` and `chanTab` reads its column only through `.val`. An `htabF` inspecting its `Fin` argument otherwise would pay a real transport — a second reason `chanTab` is the right witness. **Part 2**: cluster-row copy **done** (`clusterRowCom_spec`, `14k + 16`, absorbed by `restrictK`'s existing per-member charge — **adds no term to `prepStageK`, in particular no `A.N` term**). Two findings that shrink the batch builder: **`WidthPin` is not a new hypothesis** (`Driver.mkSetup_width_le` already proves it — `headlineSetup_widthPin`), and **`range_batchFn_eq_batchSet`** shows `isolateCom_specW`'s `W` and the scan's `batchSet` are the **same set**, so the builder writes **one** bit vector, not two. `BatchWidthScr` is the exact-`S.width` clause, and it rides `hscrLen` free. Remaining: the batch builder's two loops and the colour-region writer → **F6c12-1b**. |
| F6c12-1b | the batch builder | **done** | w27 | see log | **`mkBatchCom_batch`'s postcondition IS the two next stages' preconditions verbatim** — `FinBitsW bb (Set.range (batchFn …))` for isolate, and `BatchWidthScr bi S.width` with `bi[i] = batchFn … i` for profiles. **One** bit vector, not two, via `range_batchFn_eq_batchSet`. Programs `wipeBitsCom ; markRowCom ; emitSlotsCom ; padSlotsCom`, with the count-is-the-slot recurrence (`belowCnt` + six lemmas) carrying the carrier scan. New bridge `HistArrW` / `histArrW_of_arenaStW` gets the level's own `ArenaStW` into the builder. Budget `mkBatchK = 31·cN + (16·hb+25)·ℓp + 11·mb + 27`, and `mkBatchK_le_prepStageK` adds **no new term and no `A.N` term** — `restrictK`'s per-member charge absorbs all but the pad (**the builder reads one channel row where `restrictCom` copies `k`**), and the pad rides `profilesK`'s own `mb·batchK`. Axioms: the three standard only. |
| F6c12-1c | the colour-region writer | **done** | w28 | see log | `colWriteCom_machChild` delivers **every slot** of the colour region at `(machChild S A π u Dp Dc chan).col`, every carrier vertex, with every other array — profile tables included — preserved verbatim and no reallocation. Family-unrolled emitter in `profilesCom`'s own `batchSeq`/`classSeq` shape; `warrs_colWriteCom` writes exactly **one** array. **The design finding: the colour region is write-only.** The layout *looks* like it forces an in-place re-lay-out of the old colour rows (input stride `Λc`, output stride `isoPal Λc mb R`) with a genuine read/write aliasing hazard. It does not: under `ProfileTablesMS`, `Dc c` is a `BallTable` of `vsrc H (f c)`, so **`f c = {z | Dc c z.castSucc ≤ 1}`** (`oldRow_eq_thr_one`, via `colorTable_of_ballTable` at `b = 0`) — the `isoOld c` slot and the `isoPu c 0` slot hold the **same set off the same array**. Each `pu` block emits `R+2` cells instead of `R+1`, the writer never reads `ca`, and there is **no aliasing side condition, no scratch copy, no descending scan**. Budget `colWriteK ≤ profilesK ≤ prepStageK`: no new term, no `A.N` term, and without `mkBatchK`'s `1 ≤ cN` side condition — the loop's `14cN + 6` rides the **spare class slot** (`profilesK` is charged at `L := Λc+1` while the emitter has only `Λc` `pu` families, the marker being one of them). Axioms: the three standard or a subset; never reaches UQW. | **Blocked by nothing semantic — it is a second program of the batch builder's size.** `machChild.col` must be emitted over `isoPal (relPal Λ) S.width S.R` reading `mb` pd arrays and `Λ+1` pu arrays, and **IMP+ has no array indirection**, so it must be a *family-unrolled* emitter in `profilesCom`'s own `batchSeq`/`classSeq` shape — a `Nat`-recursive `.seq` of static copies plus the matching `warrs`/`wvars` induction — with a `ColBits` proof partitioning the palette. w27 landed the one fact nothing else states and it cannot start without: the slot numerals `isoOld_val`/`isoPd_val`/`isoPu_val` (all `rfl`) and `isoPal_cases`. Word bounds the composer owes: `childN·ℓp·(hbf+1) < B`, `childN < B`, `S.width < B`. | Nothing semantic blocks either. The builder is a channel-row marking scan plus a carrier scan whose invariant carries `{y ∈ batchSet ∧ y < a}.ncard` — `batchFn_eq_of_ncard_lt` and `batchFn_eq_centre_of_le_ncard` pin all `S.width` slots between them, and `range_batchFn_eq_batchSet` means one bit vector serves both consumers. The colour-region writer assembles `machChild.col = Impl.recordProfilesMS …` over the `isoPal` layout — `profilesCom_specW` leaves pd/pu in *separate* arrays and returns `ArenaStW` at the **same** arena, so it never touches the colour region. | (i) The **channel pin** `htabF j A v e = A.chan v e` for `e < A.hist.length` — F7-suppliable by *defining* `htabF j A v e := A.chan v ↑e`, but unstated today (see log). (ii) Also unstated: the **round-count pin** `Adm j A → A.hist.length = j` (the scan needs a compile-time column count) and the **column/width pins** `ℓp (j+1) = ℓp j`, `hbf (j+1) = hbf j`, `A.hist.length < ℓp (j+1)` — `restrictCom_specW` returns an `MArena` at the *parent's* `ℓp`/`hb` while the deliverable is at `ℓp (j+1)`/`hbf (j+1)`, and closing that needs a cast on a `Fin (ℓp ·)`-indexed family, a real cost to price. (iii) Three missing programs: the **cluster-row copy** (`ClusterCsr.read_row` is a *lemma*, the loop is unwritten), the **batch builder** (two regions — `profilesCom_specW`'s index region at length **exactly** `S.width`, an equality not a `≤`, so `Scr` must pin it since the frame clause forbids reallocation; plus `isolateCom_specW`'s `FinBitsW`), and the **colour-region writer** (`profilesCom_specW` leaves pd/pu in *separate* arrays and returns `ArenaStW` at the **same** arena, so nothing landed assembles `machChild.col` over the `isoPal` layout). |
| F6c12-5b-ii | `FratCsrIn`'s program | **done** | w27 | see log | **`fratCsrAt_fratCom` discharges `FratCsrAt … fratCom … fratKStd` verbatim**, with an `example` at concrete names discharging the whole hypothesis bundle — nothing vacuous. Axioms: the three standard only. Budget met with **≥2.5× headroom on every term** (n 76/240, m 42/120, f 73/200, const 31/60). Two strengthenings: `nS` is never read (both row bounds come from `o`), and the **mark region's restoration to all-zero is proved**, so one `n·n` window can be reused across rounds. **Finding — a lesson about residual shape**: `exists_fratCsr` was *not usable* and is not used. It existentially quantifies `R`, discarding the identity `R = Csr.row off tgt` through which the program's reads are stated; without that the sweep invariants cannot be connected to the array contents. True, but **too weak for a discharger** — an ∃-residual that hides the witness's identity is worth less than it looks. **Finding 3 (in-file)**: the natural emit invariant "`mk[x·n+y] = 1` iff `(x,y)` is still to come" is **false** — clearing at the first occurrence does not remove the pair from the remaining suffix; the stable invariant is `y ∈ fratOutRow n R x ∧ y ∉ outRow L x`. | **Split off from 5c and dispatched w26** — also not blocked (the peel runs after). The transitive enumeration: for `v`, for `w ∈ inN v`, for `u ∈ inN w`, emit `(u,v)`; regroup + dedupe. **Directed and not symmetric**, and the consumer's `pick` filter tests `TransLink D u v` *and* `TransLink D v u`, so the region must answer both in `O(1)` (CSR + transpose). Budget target pre-verified: `transPairCount D = Σ_v Σ_{w∈inN v} \|inN w\|`, priced by `levelCharge`. Note `TransLink` permits `u = v` as stated but `Orientation.asymm` makes that vacuous — to be *proved* vacuous, not assumed. |
| F6c12-5c-ii | `StepEmitIn` | done (part) | w27 | see log | **The equality is PROVED**: `emRow_eq_greedyStep` is a finset *equality* — `D.inN v ∪ emFrat ∪ emTrans = (greedyStep rk D).inN v`. The arbitration splits machine-realizably: `FratLink` is symmetric, so on the fraternal phase `¬(TransLink D v u ∨ FratLink D v u)` is **false** and the test collapses to the `rk`-compare; the transitive phase's forced-direction disjunct reduces to **one matrix read** because the frat side is excluded by the phase's own seen-stamp. `not_mem_self`/`asymm` **re-derived** on the emitted rows, not borrowed. `trInCsr_emit` leaves a discharger owing only loop text. Budget `emK = 300n + 300a + 200f + 240T + 80`, all four counts proved, and **`emK_le_levelCharge : emK ≤ 150·levelCharge D + 80`** — a constant multiple of the pre-verified charge, so `exists_chainCharge_le` closes it with **no exponent change**. Axioms: the three standard only (UQW not reached). Findings: (i) `StepEmitIn` needs `nf ≤ fratPairCount D` as a *precondition* — `CsrPrefix` alone says nothing about `nf`, so without it the `200·f` term prices nothing; `FratCsrAt`'s postcondition carries exactly that, so the seam closes. (ii) the two-cycle divergence from NOdM is load-bearing **three times, all in Lean's favour** — `not_transLink_self` removes a `u ≠ v` test, `emRow_asymm` is provable *only because* a both-ways-demanded pair gets arbitrated, and `¬D.Adjacent` needs the transpose a BEII transcription would not build. Remainder → **F6c12-5c-iii** (the IMP+ text). |
| F6c12-5c-iii | `TransposeIn` | **done** | w27 | see log | `transposeIn_tpCom` meets the landed contract **verbatim** at `tpCom = count ; prefix-sum ; scatter`, budget `tpK n a = 41n + 40a + 30` bounding the proved `41n + 39a + 29`; `tpK_le_emK` places it inside `emK`, leaving `259n + 260a + 200f + 240T + 50` for the rest of the round body. Axioms: the three standard. **`StepEmitIn` was left entirely untouched — no command text, no partial contract, no named-but-unproved declaration.** **Finding — the instructive contrast with `AdjBuildIn`**: `TransposeIn` is meetable with **no extra scalar cell**. A counting sort *looks* like it needs the slot count in a scalar — precisely the shape that makes `AdjBuildIn` false — but `ns = off n` is the input CSR's **last offset**, so `o[nN]` *is* it. The lesson: before concluding a contract needs a new cell, check whether the figure is already recoverable from the data. Two proof-engineering findings: the scatter's invariant should be an **address, not a set** (slot `outOff D u + tpCnt tgt (off a) u` holds head `a`), which makes `OutCsrAt.inj` a one-liner; and `OutCsrAt.complete` is cheaper **derived** by pigeonhole than carried as a clause on each of `2·arcCount D` steps. |
| F6c12-5c-iv | `StepEmitIn` | ready | — | — | The last program of the augmentation round. **Design worked out by w27's transpose worker and handed over**: four row scans per head with a *uniform* body `read u; ⟨cnd⟩; if em.c = 1 then {t'[p] := u; p++}; A[u] := v+1; j++`, instantiated as (1) input row, `A = ad`, cond `true` — this fuses stamping with the old-arc copy; (2) transpose row, `A = ad`, cond `false`; (3) frat row, `A = sd`, cond `ad[u] ≠ v+1 ∧ sg[u] < sg[v]`; (4) trans row, `A = dg` (scratch, dead after the transpose — **this keeps `cnd`'s reads disjoint from the loop's writes and avoids a case split**), cond `sd[u] ≠ v+1 ∧ ad[u] ≠ v+1 ∧ (sg[u] < sg[v] ∨ mk[u·n+v] = 0)`. One generic step+scan lemma parameterised by an abstract `Keep : ℕ → Prop`. Feed `trInCsr_emit` with `E v = Csr.row off tgt v ++ (Csr.row fof ftf v).filter keepF ++ (Csr.row (trOff D) ttF v).filter keepT`. **Missing kit: the `CsrPrefix` row read-back** (unwrap `winA` + `GraphCsr`'s existential `off`/`tgt`), ~60 lines. **Row stamps need no clearing sweep** — stamp `v+1`, invariant "every cell `≤ v`"; a per-head clear would be `n²` and would break `emK`'s `300·n`. | The IMP+ text for the emit round: a transpose (two nested loops) + adjacency stamping + the three-phase head loop, against the landed `trInCsr_emit` and `emRow_eq_greedyStep`. Estimated materially larger than `SolveAugTrans`'s ~1280 verified program lines. **Budget already pinned** (`emK`/`emK_le_levelCharge`), so this is loop text against a fixed target, not a design question. | Waits on 5b + 5c-i (it tests against their regions). The round body proper: transposes, the `¬D.Adjacent` filter and σ-arbitration, new in-CSR by counting sort; postcondition `= greedyStep σ D`, a `pick`-filter set-equality. **No source implementation exists** — NOdM permits 2-cycles ("at most two arcs may connect x and y"), Lean's `Orientation` forbids them (`asymm`, enforced by `AugStep.tight`), so this program has no reference to copy. Est. 2000–3000 lines. Waits on F6c13b. |
| F7 | discharge the endorsed axiom | waiting | — | — | **also blocked on F6c13b, F5b, G1** (the `N²` peel breaks §7's cover term). needs F6c10a+b, then KB pin + `KsChargeBridge`; `Adm` must be `Inv`-based (w17 finding); then: `Adm` at the run tree (`mkSetup_memLeaf_eq_bot`), instantiate `SolveSpec` via `solveSpec_closed`, `q`/`c` per `hspan`, `temps ≥` boolean depth, `T x := L.const·mcK`, reconcile `Ks` with `exists_mcChargeMS_T`, ∃-close with the `conclusion:` header |

## Campaign log

### 2026-08-25 — the staleness rule, strengthened after it failed twice

The rule recorded earlier — *an edit to a landed file must precede the wave's
seeding* — was too narrow, and the same class of failure recurred. `w28` was
seeded at `01adac3`; landings continued into `main` while its workers ran, so
the colour-writer worker found `SolveMachPrepBatch.lean` — carrying the §7
facts its leaf **cannot start without** — simply absent. It diagnosed the
divergence itself, copied the file in by `worktree-seed.sh`'s own mechanism,
and verified byte-identity against the campaign branch. Correct handling, but
it should not have had to.

**The rule is therefore: a worktree is a snapshot taken at seeding, and every
landing made during a wave is invisible to that wave's running workers.**
Either (a) dispatch a leaf only when everything it consumes is already in its
worktree, or (b) refresh the worktree — source *and* `.lake/build` artifacts —
when a landing lands something a running worker needs, or (c) tell the worker
in its packet exactly which file to copy in. Checking cost one command; not
checking cost a worker a diagnosis it should not have been doing.

### 2026-08-25 — a supervisor edit that never reached its wave

`sq_lt_mcB` was un-privatised in **main** *after* `w27` had been seeded, so no
worker in that wave ever saw it: w27's checkout still reads
`private theorem sq_lt_mcB` at `SolveSweepBuild.lean:1926`. The 5a-ii worker
detected the discrepancy against its packet, said so, and re-derived the fact
locally rather than assume the packet was right — the correct response.

**Rule for the rest of this campaign: an edit to a landed file must be made
before the wave's worktree is seeded, or the running workers must be told
explicitly.** A worktree is a snapshot; main moving under it is invisible to
them. This is the third supervisor-side slip of the session, after the §7
cost authorisation and the checkpoint that got merged.

### 2026-08-25 — the ⟨D⟩ repair has a seam the supervisor did not require

w27's residual-1 worker stopped rather than weaken the residual, and in doing
so found the gap G1 left. **`A.chan` appears in exactly two files —
`DriverArena.lean` and `DriverCorrect.lean`.** It occurs nowhere in the machine
layer. So `batchPar` is defined from `A.chan`, `BlockPre` holds `htabF j A`,
and *nothing relates them*: ⟨D⟩ is repaired at the abstract layer while the
abstract↔machine seam is still open. Verified by the supervisor against the
tree, not taken from the report.

**This is a defect in how G1 was specified, not in how it was executed.** The
packet said "define the batch off the channel" and that is exactly what landed;
it did not require the companion pin to the machine's own channel. The fix is
cheap and F7-suppliable *by construction* — `htabF`'s type is
`(j) → (A : Arena (S.pal j) n₀) → Fin A.N → Fin (ℓp j) → List (Fin A.N)` and
`A.chan : Fin A.N → ℕ → List (Fin A.N)`, so F7 may simply **define**
`htabF j A v e := A.chan v (e : ℕ)`. What is missing is that nobody has stated
it. Same shape as the landed `hhtab` seam.

Recorded as the campaign's ninth docstring-or-seam finding, and the second
where a *supervisor's* under-specification, not a worker's error, produced the
gap (the first was w23's `O(N)` scan authorised without checking §7).


### 2026-08-24 — overnight: the loop runs unattended, and how to recover it

Jan, going to bed: *"Keep the machine running all night until ndmc is fully
proven end to end."* Combined with the standing grant of full decision
authority, that is a mandate to select, dispatch, review, gate, land and
re-dispatch without stopping, and to resolve every decision that arises.

**If you are a fresh session reading this after a container reclaim, this
entry plus `git log` is your whole handover.** Do:

1. `git log --oneline -8` on `claude/ndmc-1om1vl` (the campaign branch —
   local `main` is an unrelated lineage with **no common ancestor**; always
   name the branch explicitly when creating worktrees).
2. Read the leaf table above for `ready`/`wip` rows.
3. `git fetch origin` and check for `worktree-w*` branches. A `wip` row with a
   pushed `worktree-w<N>` is an interrupted wave: diff it against the campaign
   branch, salvage what is complete, re-dispatch the rest.
4. The container starts with **no `.lake/build`**. Run `.claude/capture-seed.sh`
   then one `lake build` in `nowhere-dense-model-checking/{concepts,proofs}`
   before seeding any worktree — a worktree cannot be seeded from an unbuilt
   main checkout.

**Standing hazards, all earned this session:**

- **Check §7's cost envelope BEFORE authorizing an algorithm.** Three separate
  leaves this session hit it: w23's packet authorized an `O(N)` scan and got an
  `86N²` peel; w24 and w25 both correctly refused to land a quadratic. A named
  residual at the right budget beats a proved theorem at the wrong one.
- **`AdjDeleteIn` and `AdjBuildIn` (`SolveSweepAdj.lean:325`, `:308`) are false
  as landed.** Use `AdjDeleteInW` / `AdjBuildAt`. Three landed contracts have
  now been found unspeccable for want of length or word facts; audit any named
  contract before dispatching against it.
- **Read the theorem, not the docstring** — eight recorded instances, and one
  of them (`SolveMachPrep.lean:23-26`) cost a leaf outright.
- `lax build` strips the sibling overrides **every** time, gate runs included;
  re-run `.claude/sibling-overrides.sh` after each.
- The supervisor's cwd drifts into worktrees; use `git -C <repo>` for every
  landing command. Two near-misses this session.

### 2026-08-24 — the panel, and four decisions taken under full authority

Jan: *"You have full authority to resolve all decisions. Do not wait for input
from me."* Four read-only analysts scoped the two open questions, one per
option, each instructed to attack its own option first. The synthesis is
`decisions-2026-08-24.md`; the resolutions are:

1. **⟨D⟩ → Option 2** (the channel). Option 1 dead as scoped, Option 3 viable
   but instanceless. Two analysts converged independently on the
   inherit-and-patch channel §5 line 23 already prescribes. Minted as **G1**,
   with the `ProgFrame` radius fix as an explicit prerequisite.
2. **`CovAugAdjIn` → split-price-decide**, not build-now and not defer.
   Deferring was the tempting answer and is *not honest as the residual is
   written*: `agC`, `Kag`, `Sag` are all free, so F7 would be assuming **a
   program exists** with an unpinned budget — a first for this campaign, where
   every prior residual was discharged by exhibiting a `Com`. Minted as
   **F6c12-5a/b/c**; only 5b and 5c are genuinely new.
3. **The tie-break → route 1** (re-pin, true `O(N+m)`). Minted as **F6c13b**,
   dispatched w25.
4. **The F5 transfer → dispatch now, parametrically.** Minted as **F5b**,
   dispatched w25.

**A correction to this ledger's own record.** It has said the cover deferral
chain is "four links long and terminates in a proof." That elides which branch.
The *mathematical* branch does terminate in a proof (NOdM I Lemma 6.1) — and
the campaign already formalized that branch independently and better, so it
does not need the paper. The *algorithmic* branch does not: GKS's
`thm:computingorientation` is a Lemma with no proof; NOdM II's Theorem 4.3 is
stated **with no proof** and is a *bounded expansion* claim in time `O(n)`, not
nowhere-dense `n^{1+ε}`; and the step `CovAugAdjIn` actually needs is a single
**unproved sentence** (`BEII.tex:676-678`) covering four steps of the algorithm,
with no pseudocode. **`CovAugAdjIn` is the one place in this campaign where the
papers give nothing citable.** That is why (b) was rejected.

**Seventh docstring-vs-object finding**: `SolveMachPrep.lean:23-26` describes a
per-round channel recompute that no landed object requires and that
`supportsCom_specW`'s signature makes impossible for far ancestors. That
docstring is what produced the original ⟨D⟩ worker's second kill-shot — a false
docstring cost a leaf.

### 2026-08-24 — w24 lands both, and neither is a discharge

w24's two workers both declined to land a wrong-budget proof, and both were
right to. **`CovPeelIn`** was split at the seam its own output shape forces
(`covPeelIn_of_sweep_group`, `75bff4e`) — with the cost envelope **proved**:
`peelK`'s shape is pinned (only constants free) and `peelBudget_le` puts it
inside §7's `a·N^{1+2δ}`. Its finding: the sweep *cannot* emit `ClusterCsr`
directly, because `ClusterCsr` anchors offsets in carrier order with ascending
rows while the sweep runs in `π` order with BFS level order, and a per-centre
sort is `Θ(N²)` — the same envelope break from a different direction.
**F6c13** was not discharged at all (`433bfac`): `O(N+m)` is *impossible* at the
residual as stated, because the postcondition pins the output to a function of
the graph while a linear bucket pop is a function of adjacency row order.
Matula–Beck is linear precisely because its pop is arbitrary.

The lesson, third occurrence this session: **check the cost envelope before
authorizing an algorithm, not after.** w23's packet authorized an `O(N)` scan
without checking §7 and produced an `86N²` peel; w24's packets carried the
envelope up front and got two honest refusals instead of two bad landings.

### 2026-08-24 — w23 lands three of four, and finds two landed contracts defective

What is now true that was not before: **the cover sweep's build pass, the
min-degree peel, the swap-delete program and the scatter-and-readback pass all
exist as IMP+ programs with `Spec`s** — three of F6c12's six residuals
discharged verbatim (`5e8ff02`, `3734244`, `a5e5d24`), each gated
independently, each with an axiom footprint identical to the landed consumer
it feeds.

**The wave's real yield is three findings, and two of them are defects in
material that had already landed.**

1. **`AdjDeleteIn` (`SolveSweepAdj.lean:325`) is FALSE**, and w23 proves it —
   `not_adjDeleteIn`, for every `B`, every program, every budget. It
   quantifies over every `N` and every `DelAdjSt` state and relates none of
   them to `B`; at `N = B+2` with a single edge, its postcondition demands a
   store at index `B`, which `Run B` forbids. `AdjBuildIn` (`:308`) has the
   same shape and is undischargeable for the same reason, with a second cause:
   **IMP+ has no array-length primitive** (`Imp.lean:158`), so a fixed command
   cannot find the end of a carrier whose size lives only in a list length.
   Both repairs are one hypothesis wide — `AdjDeleteInW` adds `N + N² < B`,
   `AdjBuildAt` moves the two figures into named cells — and both are free at
   `mcB` from `1 ≤ q`. **The pattern is now three deep** (F6c8's
   `TopScatterSpec`, and these two): a contract stated at a `Spec` without the
   length or word facts its own program needs is not a hard leaf, it is a
   false one. Audit the remaining named contracts for it before dispatching
   against them.

2. **The batch is not machine-computable** — the ⟨D⟩ finding, recorded in
   `algorithm-v2.md` §5 and blocking residual (1). See that entry; it is Jan's
   decision, not a leaf's.

3. **A cost defect the supervisor's own packet authorized.** The packet told
   W4 that "a correct `O(N)` scan per round is acceptable — name the budget
   honestly", without first checking §7. §7 charges the whole cover routine at
   `a·N^{1+2δ}`, so the resulting `86N² + 43N + 14` breaks the headline at the
   root. The worker did exactly what it was told and flagged the gap in its
   report; the error is the packet's. Minted as **F6c13** (bucket-queue
   degeneracy ordering, `O(N + m)`), which now blocks F7. *Check the cost
   envelope before authorizing a slower algorithm, not after.*

Also measured: the leaf gate is ~30 s against a warm tree, so landing per
boundary is cheap — and `lax build` strips the sibling overrides **every**
time, gate runs included, so `sibling-overrides.sh` belongs after each one.

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
