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
| F5b | the cover cost column at the **selection** | done | w25+w31 | see log | **Degree clause exported (w31).** `exists_mcChargeMS_T_bucket_coverColumn` carries the `T` bound, the ledger bound **and** the cover-sweep column at one `cf ≥ 1`, at the machine's own routine `selOrderingRoutine bucketSel (3·S.R)`. Fix shape: export at the *same* `cf`, because `exists_coverChargeSel_le` already picks the degree constant as its witness and merely drops it (`exists_fratCsr`'s failure mode). `sweepCharge_mono_deg` proves the asymmetry that forces this: a charge bound never transfers up to a larger `D`, the degree clause does. **Second hole, not in the audit's account**: `0 ≤ cf` genuinely admits `cf = 0` (`⌈0·m^δ⌉₊ = 0`), so `peelBudget_le_sweepCharge`'s *second* hypothesis `1 ≤ D` was unavailable independently — now `1 ≤ cf` is exported too. Column closes **per node** (the shape every sibling column of `KsChargeBridge` uses); the node→root step is **not** a monotonicity step, because `driverChargeMS` places `covC j A` inside `frameChargeMS` only on the `A.G ≠ ⊥` branch. Axioms match the landed exports pair-for-pair. | **Landed.** Headline **`exists_mcChargeMS_T_selOrdering`** — axioms *identical* to the landed `exists_mcChargeMS_T`, and the setup-parametric `exists_mcChargeMS_chargeTotal_le_sel` sits at the clean three, confirming the fourth is statement-inherited. Exponent is F5's own `f·m^{1+δ}`, same constant shape, **not** the interface's `1+2δ` (the weakening is confined to the `_double` variant, where the interface asks for it). Hazard 2 resolved *by construction*: `mcChargeMS` reads its `OrderingRoutine` only through `.order` (`.steps` is read only by `Unroll.frameCost`, the abstract recursion), so both capstones are proved once for any `ord` agreeing on `.order`, then instantiated at `selOrderingRoutine`, `timedSelRoutine` and `mdOrderingRoutine` — **`KsChargeBridge`'s two sides can carry one `ord`**. Anti-vacuity kept (`le_selChainCharge`, `le_timedSelRoutine_steps`, `coverCSel_order_eq_steps`). Beyond the packet, and needed: `coverProgSel`/`coverProgSel_le_spec`, because `ProgCover.coverProg` names `timedGreedyRoutine` in the value it **returns**, so the cost transfer alone would not let F3's `hcover` be filled at the machine routine. Finding: `ProgCover.lean`'s module docstring cites `exists_chainCharge_le` for the order half, but the proof consumes `exists_chainCharge_le_double` — same bound, wrong citation. *Original mint:* | **The ledger's open F5-transfer question, settled by the panel and now dispatched.** The theorem does *not* transfer — `coverOrderingTime_of_nowhereDense` is a bare `∃ A`, so F7 cannot extract a routine from it, and the whole column (`chainCharge`, `coverC`, `exists_mcChargeMS_T`, `KsChargeBridge`) names `timedGreedyRoutine` **literally**. The *proof* transfers verbatim: `greedy_chain_joint_inDegLE` (`AugmentedDensity.lean:966`) is stated at an **arbitrary** chain and `mdChain` supplies all three hypotheses; the four `levelCharge` bounds are already at an arbitrary `Orientation`. Stated **parametrically at `selChain`/`selOrderingRoutine sel R`** so F6c13b's re-pin costs it nothing, with the `mdOrderingRoutine` corollaries via `selOrderingRoutine_mdSel`. Headline: the `exists_mcChargeMS_T` analogue — the one F7 consumes. **Required for F7 regardless of every other decision.** |
| F6c13c | the **static-adjacency** peel program | **done** | w26+w27 | see log | **`covSelPeelIn_bucketPeelCom` discharges `CovSelPeelIn` with every clause verbatim** at `Kmp = 313·A.N + 118·slotCount((selChain (bucketSel A.N) A.G R).toGraph) + 40` — **no `A.N²` term**. **`covOrderIn_bucketPeel` is w26's `covOrderIn_bucket` with `hmp` gone**, so `CovOrderIn` at `selOrderingRoutine bucketSel R` is unconditional on the peel side. This closes the chain that opened when w24 proved `O(N+m)` *impossible* at the original tie-break: w24 found the obstruction, w25 re-pinned and proved the re-pin free, w26 built the bucket machinery, w27 wrote the program. **Finding — w26's kit was true but inapplicable**: `peelLoop_linear_bucket` charges a round `a + b·|N_F(v)| + e·rise`, but a *lazily-cleaned* stack's stale skipping is bounded by **earlier** rounds' pushes, not this round's degree, so that rule cannot pay for it. `peelLoop_linear_static_cursor_lazy` / `peelLoop_linear_bucket_lazy` add a fourth potential term over cells in the stacks (total pushes `N + slotCount F`), leaving the budget *shape* unchanged. **`AdjSortIn` is BYPASSED, not discharged** — `rowList F v := (List.range N).filter (adjB F v)` is canonical by construction, so `orderEmbOfFin_unique` is unneeded and the entry sort is a concrete transpose at `27m + 22N + 6` rather than w26's unquantified `K`. That retires one of w27's two "the DAG is deeper" findings. Space: `Smp` asks `n²+n` stack cells — **space, not time**, the same shape as the adjacency region the pass already reads. | see log | Bucket selection built and composed, **but `CovSelPeelIn` is still a hypothesis, not discharged** — `covOrderIn_bucket` concludes `CovOrderIn … (selOrderingRoutine bucketSel R) …` *conditional* on it. Landed: `bucketSel`, `bucketPick_mem/_card/_bRun`, `guardPick_some`, `peelLoop_linear_bucket`, `selRank_eq_selRankAux_bRun`, `selRank_bPop`, `linearPeelBudget`. What remains is the round **program** meeting `CovSelPeelIn` at `bucketSel`. | The program F6c13b's amortization is waiting for. Design, forced by w25's finding: a peel that **never writes the adjacency arrays**, so one counting sort at entry makes the rows a function of `G` for the whole run and the bucket replay models only the buckets. A round then walks `v`'s **original** row — priced by `staticPot`, not `livePot`. Owes: the counting-sort pass + its spec; the abstract bucket replay with its partition invariant; the round program at `O(1) + O(\|N_F(v)\|) + O(cursor rise)`, fed to the landed `peelLoop_linear_static_cursor`. Est. 2500–3000 lines. Consumes `MinDegSel.ofMin` (the pop obligation is *attainment*, not least index) and `card_nbrsIn_pick_eq_minDeg` (which licenses the cursor via `minDeg_le_minDeg_erase_succ`). Note it must **not** use `delAdjCom`: that is the swap-delete whose row scrambling is the whole reason for this design. |
| G1 | ⟨D⟩: the batch off the **channel** | done | w26 | see log | **THE ⟨D⟩ FINDING IS REPAIRED.** `Arena` gains `chan : Fin N → ℕ → List (Fin N)` (ℕ-indexed field, so all 565 `Arena Λ n₀` ascriptions survive); `batchPar = {u} ∪ {z \| ∃ e < A.hist.length, z ∈ A.chan u e}`, `batchRoot = up '' batchPar` — **`genSet` and `pathSet` leave the driver entirely** (they stay live in `ReachedS`, proving Splitter wins). `Inv` gains the two channel clauses. **`batchSet_ncard_le`'s bound is unchanged** at `1 + A.hist.length*(2R+1)` (now taking the row-length clause as `hchan`), so `hwidth` and the schedule are untouched. Step 0 landed first: `ProgFrame`'s supports BFS runs at `2*S.R` (`SolveFrameStages:387`'s instruction; the w14 stale figure, fixed). Relocation file `DriverBfsTree` + mechanical fixes in `ImplBfs`/`ImplRestrict`/`ProgCharge`/`SolveBlocksSupports`/`SolveMachPrep`. **Headline axiom footprint unchanged** (`mkSetup_mc_correct`, `headline_abstract`, `headline_encoded` all verified). | **Supervisor decision (2026-08-24, full authority): Option 2**, per `decisions-2026-08-24.md`. Option 1 is dead as scoped (`pathSet` descends the round's *unrestricted* arena `e.2`; the affordable pass BFSes `preG` — the gradient walks provably differ, so canonicalizing only converts "no program can" into "only a `Θ(N·‖A‖)`-per-node program can"). Option 3 is semantically near-free (4 call sites in 3 lemmas, ~40 lines of real mathematics) but buys **no instance** — the per-round-recompute channel fails `hwalk` because ancestor connectors are edge-isolated, so the batch collapses to `{u}`, verbatim §5 ⟨A⟩'s recorded vacuity — and costs ~418 call-site edits. Two analysts converged independently on the **inherit-and-patch channel** (§5 line 23), and the machinery is already landed: `MArena.restrict` carries old columns down filtered (`ImplRestrict.lean:204`), `supportsCom_specW` writes exactly one column and inherits the rest (`SolveFrameStages.lean:410`) — both verified by the supervisor. Plan: (0) **prerequisite** — fix `ProgFrame.lean:392`'s supports radius `S.R → 2R` (`SolveFrameStages.lean:387` says instantiate `2R`, "never `S.R`"; inert today only because `_DT` is discarded — the same stale figure w14 flagged); (1) `chan : Fin N → ℕ → List (Fin N)` as an **`Arena` field**, ℕ-indexed (a field leaves all 565 `Arena Λ n₀` ascriptions valid; an index would not); (2) `batchPar := {u} ∪ {z \| ∃ e < A.hist.length, z ∈ A.chan u e}`, `genSet`/`pathSet` leaving the driver entirely (they stay live in `ReachedS`, proving a different theorem); (3) two new `Inv` clauses (length + walk witness). ~700–1100 lines, concentrated in `DriverCorrect.inv_child`. **Edits landed files — runs in its own wave, alone.** |
| F6c12-5a | the augmentation frame (base / rounds / sym) | done (part) | w27 | see log | **`covAugAdjIn_of_base_rounds_sym` concludes the landed `CovAugAdjIn` VERBATIM** at `sel = mdSel` (through w25's `covAugAdjSelIn_mdSel`), from `AugBaseIn`/`AugRoundIn`/`AugSymIn` and nothing else, at program `bsC ; (rdC)^R ; syC`. The chain is read off its definition, not assumed: **`selChain_zero` and `selChain_succ` are both `rfl`**, compiler-checked, and `AugRoundIn`'s postcondition is written in the `greedyStep` form the emit proves. Budget: three pinned shapes (constants free, the `peelK` model), each a term of `selChainCharge`; `augChainCost_le_selChainCharge` then `exists_augChainCost_le` gives `f·m^{1+δ} + O(R)` via w25 — **one δ inside §7, no new cost function defined, no `N²` anywhere**. `augSymIn_of_symCsr_build` is a real composition with the landed `adjBuildAt_bldAdjCom`. Findings: (i) **`AdjBuildAt` asks for a plain `GraphCsr`, whose `Csr` clause pins array lengths *exactly*, while the arena supplies its CSR only behind `winA`** — so the landed build is directly usable for the *symmetrization* (fresh arrays) but **not** for the base's build, which must go the `covAdjBuildIn_bldCom` route. That is the sole reason `AugBaseAdjIn` is stated rather than discharged. (ii) `sq_lt_mcB` was `private` — **un-privatised at this landing** so the next discharger need not reprove it. (iii) **the handshake `slotCount G = 2·arcCount (baseOr G π)` is not landed anywhere**; the base budgets are therefore stated at `arcCount (selChain … 0)` directly, keeping the conversion out of the interface. Remainder: `AugBaseAdjIn`/`AugBasePeelIn`/`AugBaseOrientIn`/`AugSymCsrIn` → **F6c12-5a-ii**. |
| F6c12-5a-ii | the frame's four small passes | done (part) | w27+w28 | see log | **3 of 4 done.** `AugBaseOrientIn` discharged (w28) at `orCom` (count/prefix-sum/scatter), budget `70·A.N + 86·arcCount + 25`, **the conversion an equality with no slack spent** (`43 → 86` because the source slot space is the degree sum `= 2·arcCount`). **`inNCsr_winA_of_trInCsr` is the first route in the tower from a machine state to a literal `InNCsr`** — nothing landed concluded one before. Two notes: the program reads **neither `bdg` nor `bmt`** (at `S = ∅` the live prefix is the whole row, so `ao[v+1]` bounds every inner scan and the degree clause appears only in the proof), and **no figure needs a scalar cell** — carrier from `nN`, row bounds from `ao`, slot count *produced* into `nA` rather than consumed. Running base total `bn = 545`, `ba = 554`, closing at `k = 545`. **Finding — the exact-length trap, third occurrence.** `augStInN` (`SolveAugCompose` §7) is **not producible by any pass as literally stated**: `InNCsr` goes through `Lib.Csr`, whose first two clauses pin `σ.arrs o`/`σ.arrs t` at **exact** lengths while a pass gets `≤`, and the slot count is the pass's own *output*, so no allocation could have been made that long. **Nothing is false** — `InNCsr` also sits in the *precondition* of the landed `FratCsrAt`, so producer and consumer move together and `specWindow` is the standing bridge. Delivered `augStInNW` (the `CsrPrefix` reading) plus the un-windowed `TrInCsr`. After `AdjBuildIn` and `SolveAugFrat`'s `GraphCsr`, the pattern is settled: **an exact-length `Csr` clause in a postcondition is a binding requirement on whoever establishes the precondition, and is invisible in the contract text.** Relayed to the round-body worker mid-flight. **2 of 4 done** was the prior state. | `AugBasePeelIn` discharged (w28) at `394·A.N + 352·arcCount + 64`, no `A.N²`; both slot terms convert **by equality**. **The composition fact no packet anticipated: `bucketPeelCom` CONSUMES the region it peels** — its write set contains `dg` and `mt`, two of `DelAdjSt`'s four arrays — so `CovSelPeelIn` drops the region from its postcondition while `AugBasePeelIn` demands it back. The pass peels then **rebuilds from the arena's own CSR**, which the peel never touches; the rebuild writes exactly `{bao,baj,bdg,bmt}` so the rank array survives (`RankArr.of_eq`). Hence the proof routes through `bucketPeelCom_spec` + frame lemmas, **not** through `covSelPeelIn_bucketPeelCom` — the contract's postcondition is the wrong shape, not the program. Coefficients: `bn = 475`, `ba = 468`, closing at `k = 475`; `k` rose from 81 because the rebuild costs 81, the price of region-preservation. `AugBaseAdjIn` done (w27). |
| F6c12-5a-iii | `AugSymCsrIn` — the merge | ready | — | — | The transpose is landed (`transposeIn_tpCom`); what remains is the **merge** of `inN v` with `outNbrs D v` into a `GraphCsr` of `D.toGraph` — a program leaf the size of `tpCom`'s, with no landed counterpart. Three facts landed w28 aim it: `symCsr_ns_eq`/`_le` (**the `ns ≤ 2·arcCount` clause is an *equality*** at `Orientation.orients_toGraph` — nothing to spend), **`toGraph_step_add`** (the merged offset function is the **pointwise sum** of the input CSR's and the transpose's, so the offset pass is one add and one store per vertex, **not** a prefix scan), and `symCsrSizes`/`symCsrSizes_exact`. **Finding — the `AdjBuildIn` trap one level up.** `AugSymCsrIn`'s postcondition is a bare `GraphCsr`, whose `Lib.Csr` clauses are array **equalities**, and IMP+ `store` is `List.set`, so **no run changes a length**. The pass must therefore be *handed* `soO j` at exactly `A.N + 1` cells and `stO j` at exactly `2·arcCount D`; the windowed `≥` allocations the arena and every scratch descriptor supply are **not enough**. Not falsity — a binding requirement invisible in the contract text. **Supervisor decision: do NOT restate the residual at the windowed `SrcCsr`.** The worker showed restating would ease the merge, but also *proved* the requirement satisfiable as it stands — `augStInN`'s `nA` cell already holds `arcCount D` and the arena's `nN` holds `A.N`, so `Srd`/`AugSt` pin both lengths in terms of `σ` alone (`symCsrSizes_exact`). Churning a landed residual plus `adjBuildAt_bldAdjCom`'s packaging for convenience is the worse trade; the merge leaf gets `symCsrSizes_exact` instead. | **1 of 4 discharged.** `augBaseAdjIn_bldAdjCom` concludes `AugBaseAdjIn` **verbatim** at `81·A.N + 116·arcCount(selChain sel A.G 0) + 24`, `sel` free — inside the coefficient bounds (`bn ≤ k`, `ba ≤ 3k`) at `k = 81`. The `AdjBuildAt` trap was confirmed independently. **Bonus: the handshake this ledger recorded as *not landed anywhere* is now proved** — `sum_ncard_neighborSet_eq_two_mul_arcCount` (`D.Orients G → ∑ v, (G.neighborSet v).ncard = 2·arcCount D`, via `inN v ⊎ outNbrs D v` by `Orientation.asymm` then `TgtCoupling.sum_card_outNbrs`), converting `bldAdj_spec`'s `58·ns` into `116·arcCount` **by equality**; stated generally so the transpose leaf can reuse it. **Two findings that deepen the remaining DAG**: (i) **`linearPeelBudget` is not a budget proved of any program** — `SolveSweepBucketProg` §5 says so in terms ("the shape a peel pass built on §1–§4 *can* meet"), and its entry sort **`AdjSortIn` (`:343`) is itself an undischarged residual**; the only landed peel *program* is the quadratic `covSelPeelIn_peelCom_mdSel`. (ii) **No landed theorem anywhere concludes an `InNCsr`** — `SolveAugFrat` only defines and reads it — so `AugBaseOrientIn` is a fresh count/prefix-sum/scatter construction, not assembly. Remaining: `AugBasePeelIn`, `AugBaseOrientIn`, `AugSymCsrIn` (the last is naturally downstream of `TransposeIn`). | `AugBaseAdjIn` (via `covAdjBuildIn_bldCom`, *not* `AdjBuildAt` — see 5a finding (i)), `AugBasePeelIn` (the linear peel, pinned), `AugBaseOrientIn`, `AugSymCsrIn` (the transpose, owing `ns ≤ 2·arcCount`). All four have pinned budget shapes already; this is program text against fixed targets. | The two *free* thirds of `CovAugAdjIn`'s split: base peel = `bldAdjCom ; peelCom` composed, symmetrization = `bldAdjCom` again. Both are landed programs; this row is composition only. Waits on F6c13b (the peel it composes must be the linear one). |
| F6c12-5b | `FratCsrIn` | done (part) | w26 | see log | `exists_fratCsr` + the CSR-prefix kit (`graphCsr_fratPref`, `csrPrefix_fratPref`, `fratOff_succ`, `InNCsr.rows`, `fratNs_le`). **Budget verified**: `fratK_le : fratK … ≤ a*n + (b+c)*fratPairCount D + d` — exactly the pre-verified target, linear in `n` and `fratPairCount`. `arcCount_le_fratPairCount` is the bridge. Full semantic review of the `Spec` still owed. | **Not blocked after all** — the supervisor's "waits on F6c13b" was over-cautious: the peel runs *after* the fraternal graph is built, so this pass never touches it. Dispatched w26. Budget target handed to the worker rather than chosen by it: `fratPairCount D = Σ_w \|inN w\|²` is exactly the enumeration's size and `levelCharge` (`ProgCoverCharge.lean:150`) already prices it inside §7's envelope — the first leaf this campaign has dispatched with its cost target *pre-verified*. The fraternal enumeration: for `w`, for `x,y ∈ inN w` with `x<y`, emit `{x,y}`; regroup + dedupe into an exact `GraphCsr (fratGraph D)` (counting sort + row-stamped mark array, the `SolveCovLoad` pattern). Count `Σ_w \|inN w\|² ≤ N·d²`. Est. 2000–3500 lines. Waits on F6c13b. |
| F6c12-5c-i | `TransCsrIn` | done | w26 | see log | `transCsrIn_trCom` + `transCsrAt_decides` (the both-directions `O(1)` test the `pick` filter needs) + `transCsrAt_row`, `trOff_owner`, `trOuter_scan`, `trRow_lt_sq`, `transCsrAt_slots_le`. **Budget verified**: `trK_le : trK n (arcCount D) (transPairCount D) ≤ n*(27 + 23d + 30d²) + 13` under `D.InDegLE d` — the `transPairCount` shape, `O(n·d²)`. **Spec review done: this one IS a real discharge** — `transCsrIn_trCom` proves `TransCsrIn B … (trCom …) trK` with `trCom` an actual `Com` and explicit `Run` steps. **Status: done.** |
| F6c12-1a | the channel pin + residual 1's three programs | done (part) | w27 | see log | **THE SEAM IS CLOSED.** `chanTab S ℓp j A v e := A.chan v ↑e` is the witness; `chanTab_chanPin` holds **by `rfl`**, and **`chanTab_hhtab` discharges `SolveMachPrep`'s seam hypothesis by `rfl`**, so **`centrePrepAll_of_parts_chanTab` concludes `CentrePrepAll` verbatim with no `hhtab` left**. `mem_batchSet_iff_chanRow`/`_level` then supply both hypotheses of `mem_batchSet_iff_restrictHist`, so §5 line 19 reads off `htabF j A` — the table `BlockPre` actually puts in the region. All six pins stated **and witnessed** (`stdPins`); `prepAdm` is not merely satisfiable but **preserved by the driver's own recursion** (`prepAdm_root`/`_child`/`_admChild`). **The cast, priced**: the `hbf` pin costs *nothing* (`hb` is not a type index, only the channel stride); the `ℓp` pin costs one cast at the hand-over and is **definitionally invisible on the canonical witness**, because `Fin.cast` preserves `.val` and `chanTab` reads its column only through `.val`. An `htabF` inspecting its `Fin` argument otherwise would pay a real transport — a second reason `chanTab` is the right witness. **Part 2**: cluster-row copy **done** (`clusterRowCom_spec`, `14k + 16`, absorbed by `restrictK`'s existing per-member charge — **adds no term to `prepStageK`, in particular no `A.N` term**). Two findings that shrink the batch builder: **`WidthPin` is not a new hypothesis** (`Driver.mkSetup_width_le` already proves it — `headlineSetup_widthPin`), and **`range_batchFn_eq_batchSet`** shows `isolateCom_specW`'s `W` and the scan's `batchSet` are the **same set**, so the builder writes **one** bit vector, not two. `BatchWidthScr` is the exact-`S.width` clause, and it rides `hscrLen` free. Remaining: the batch builder's two loops and the colour-region writer → **F6c12-1b**. |
| F6c12-1b | the batch builder | **done** | w27 | see log | **`mkBatchCom_batch`'s postcondition IS the two next stages' preconditions verbatim** — `FinBitsW bb (Set.range (batchFn …))` for isolate, and `BatchWidthScr bi S.width` with `bi[i] = batchFn … i` for profiles. **One** bit vector, not two, via `range_batchFn_eq_batchSet`. Programs `wipeBitsCom ; markRowCom ; emitSlotsCom ; padSlotsCom`, with the count-is-the-slot recurrence (`belowCnt` + six lemmas) carrying the carrier scan. New bridge `HistArrW` / `histArrW_of_arenaStW` gets the level's own `ArenaStW` into the builder. Budget `mkBatchK = 31·cN + (16·hb+25)·ℓp + 11·mb + 27`, and `mkBatchK_le_prepStageK` adds **no new term and no `A.N` term** — `restrictK`'s per-member charge absorbs all but the pad (**the builder reads one channel row where `restrictCom` copies `k`**), and the pad rides `profilesK`'s own `mb·batchK`. Axioms: the three standard only. |
| F6c12-1c | the colour-region writer | **done** | w28 | see log | `colWriteCom_machChild` delivers **every slot** of the colour region at `(machChild S A π u Dp Dc chan).col`, every carrier vertex, with every other array — profile tables included — preserved verbatim and no reallocation. Family-unrolled emitter in `profilesCom`'s own `batchSeq`/`classSeq` shape; `warrs_colWriteCom` writes exactly **one** array. **The design finding: the colour region is write-only.** The layout *looks* like it forces an in-place re-lay-out of the old colour rows (input stride `Λc`, output stride `isoPal Λc mb R`) with a genuine read/write aliasing hazard. It does not: under `ProfileTablesMS`, `Dc c` is a `BallTable` of `vsrc H (f c)`, so **`f c = {z | Dc c z.castSucc ≤ 1}`** (`oldRow_eq_thr_one`, via `colorTable_of_ballTable` at `b = 0`) — the `isoOld c` slot and the `isoPu c 0` slot hold the **same set off the same array**. Each `pu` block emits `R+2` cells instead of `R+1`, the writer never reads `ca`, and there is **no aliasing side condition, no scratch copy, no descending scan**. Budget `colWriteK ≤ profilesK ≤ prepStageK`: no new term, no `A.N` term, and without `mkBatchK`'s `1 ≤ cN` side condition — the loop's `14cN + 6` rides the **spare class slot** (`profilesK` is charged at `L := Λc+1` while the emitter has only `Λc` `pu` families, the marker being one of them). Axioms: the three standard or a subset; never reaches UQW. | **Blocked by nothing semantic — it is a second program of the batch builder's size.** `machChild.col` must be emitted over `isoPal (relPal Λ) S.width S.R` reading `mb` pd arrays and `Λ+1` pu arrays, and **IMP+ has no array indirection**, so it must be a *family-unrolled* emitter in `profilesCom`'s own `batchSeq`/`classSeq` shape — a `Nat`-recursive `.seq` of static copies plus the matching `warrs`/`wvars` induction — with a `ColBits` proof partitioning the palette. w27 landed the one fact nothing else states and it cannot start without: the slot numerals `isoOld_val`/`isoPd_val`/`isoPu_val` (all `rfl`) and `isoPal_cases`. Word bounds the composer owes: `childN·ℓp·(hbf+1) < B`, `childN < B`, `S.width < B`. | Nothing semantic blocks either. The builder is a channel-row marking scan plus a carrier scan whose invariant carries `{y ∈ batchSet ∧ y < a}.ncard` — `batchFn_eq_of_ncard_lt` and `batchFn_eq_centre_of_le_ncard` pin all `S.width` slots between them, and `range_batchFn_eq_batchSet` means one bit vector serves both consumers. The colour-region writer assembles `machChild.col = Impl.recordProfilesMS …` over the `isoPal` layout — `profilesCom_specW` leaves pd/pu in *separate* arrays and returns `ArenaStW` at the **same** arena, so it never touches the colour region. | (i) The **channel pin** `htabF j A v e = A.chan v e` for `e < A.hist.length` — F7-suppliable by *defining* `htabF j A v e := A.chan v ↑e`, but unstated today (see log). (ii) Also unstated: the **round-count pin** `Adm j A → A.hist.length = j` (the scan needs a compile-time column count) and the **column/width pins** `ℓp (j+1) = ℓp j`, `hbf (j+1) = hbf j`, `A.hist.length < ℓp (j+1)` — `restrictCom_specW` returns an `MArena` at the *parent's* `ℓp`/`hb` while the deliverable is at `ℓp (j+1)`/`hbf (j+1)`, and closing that needs a cast on a `Fin (ℓp ·)`-indexed family, a real cost to price. (iii) Three missing programs: the **cluster-row copy** (`ClusterCsr.read_row` is a *lemma*, the loop is unwritten), the **batch builder** (two regions — `profilesCom_specW`'s index region at length **exactly** `S.width`, an equality not a `≤`, so `Scr` must pin it since the frame clause forbids reallocation; plus `isolateCom_specW`'s `FinBitsW`), and the **colour-region writer** (`profilesCom_specW` leaves pd/pu in *separate* arrays and returns `ArenaStW` at the **same** arena, so nothing landed assembles `machChild.col` over the `isoPal` layout). |
| F6c12-5b-ii | `FratCsrIn`'s program | **done** | w27 | see log | **`fratCsrAt_fratCom` discharges `FratCsrAt … fratCom … fratKStd` verbatim**, with an `example` at concrete names discharging the whole hypothesis bundle — nothing vacuous. Axioms: the three standard only. Budget met with **≥2.5× headroom on every term** (n 76/240, m 42/120, f 73/200, const 31/60). Two strengthenings: `nS` is never read (both row bounds come from `o`), and the **mark region's restoration to all-zero is proved**, so one `n·n` window can be reused across rounds. **Finding — a lesson about residual shape**: `exists_fratCsr` was *not usable* and is not used. It existentially quantifies `R`, discarding the identity `R = Csr.row off tgt` through which the program's reads are stated; without that the sweep invariants cannot be connected to the array contents. True, but **too weak for a discharger** — an ∃-residual that hides the witness's identity is worth less than it looks. **Finding 3 (in-file)**: the natural emit invariant "`mk[x·n+y] = 1` iff `(x,y)` is still to come" is **false** — clearing at the first occurrence does not remove the pair from the remaining suffix; the stable invariant is `y ∈ fratOutRow n R x ∧ y ∉ outRow L x`. | **Split off from 5c and dispatched w26** — also not blocked (the peel runs after). The transitive enumeration: for `v`, for `w ∈ inN v`, for `u ∈ inN w`, emit `(u,v)`; regroup + dedupe. **Directed and not symmetric**, and the consumer's `pick` filter tests `TransLink D u v` *and* `TransLink D v u`, so the region must answer both in `O(1)` (CSR + transpose). Budget target pre-verified: `transPairCount D = Σ_v Σ_{w∈inN v} \|inN w\|`, priced by `levelCharge`. Note `TransLink` permits `u = v` as stated but `Orientation.asymm` makes that vacuous — to be *proved* vacuous, not assumed. |
| F6c12-5c-ii | `StepEmitIn` | done (part) | w27 | see log | **The equality is PROVED**: `emRow_eq_greedyStep` is a finset *equality* — `D.inN v ∪ emFrat ∪ emTrans = (greedyStep rk D).inN v`. The arbitration splits machine-realizably: `FratLink` is symmetric, so on the fraternal phase `¬(TransLink D v u ∨ FratLink D v u)` is **false** and the test collapses to the `rk`-compare; the transitive phase's forced-direction disjunct reduces to **one matrix read** because the frat side is excluded by the phase's own seen-stamp. `not_mem_self`/`asymm` **re-derived** on the emitted rows, not borrowed. `trInCsr_emit` leaves a discharger owing only loop text. Budget `emK = 300n + 300a + 200f + 240T + 80`, all four counts proved, and **`emK_le_levelCharge : emK ≤ 150·levelCharge D + 80`** — a constant multiple of the pre-verified charge, so `exists_chainCharge_le` closes it with **no exponent change**. Axioms: the three standard only (UQW not reached). Findings: (i) `StepEmitIn` needs `nf ≤ fratPairCount D` as a *precondition* — `CsrPrefix` alone says nothing about `nf`, so without it the `200·f` term prices nothing; `FratCsrAt`'s postcondition carries exactly that, so the seam closes. (ii) the two-cycle divergence from NOdM is load-bearing **three times, all in Lean's favour** — `not_transLink_self` removes a `u ≠ v` test, `emRow_asymm` is provable *only because* a both-ways-demanded pair gets arbitrated, and `¬D.Adjacent` needs the transpose a BEII transcription would not build. Remainder → **F6c12-5c-iii** (the IMP+ text). |
| F6c12-5c-iii | `TransposeIn` | **done** | w27 | see log | `transposeIn_tpCom` meets the landed contract **verbatim** at `tpCom = count ; prefix-sum ; scatter`, budget `tpK n a = 41n + 40a + 30` bounding the proved `41n + 39a + 29`; `tpK_le_emK` places it inside `emK`, leaving `259n + 260a + 200f + 240T + 50` for the rest of the round body. Axioms: the three standard. **`StepEmitIn` was left entirely untouched — no command text, no partial contract, no named-but-unproved declaration.** **Finding — the instructive contrast with `AdjBuildIn`**: `TransposeIn` is meetable with **no extra scalar cell**. A counting sort *looks* like it needs the slot count in a scalar — precisely the shape that makes `AdjBuildIn` false — but `ns = off n` is the input CSR's **last offset**, so `o[nN]` *is* it. The lesson: before concluding a contract needs a new cell, check whether the figure is already recoverable from the data. Two proof-engineering findings: the scatter's invariant should be an **address, not a set** (slot `outOff D u + tpCnt tgt (off a) u` holds head `a`), which makes `OutCsrAt.inj` a one-liner; and `OutCsrAt.complete` is cheaper **derived** by pigeonhole than carried as a clause on each of `2·arcCount D` steps. |
| F6c12-5c-iv | `StepEmitIn` | **done** | w28 | see log | **The pass the literature gives nothing for, discharged.** `stepEmitIn_emCom` meets the landed `StepEmitIn` verbatim with a real `Com`; `stepEmitIn_emCom_emK` restates it at `SolveAugEmit`'s pinned `emK`. Output `TrInCsr o' t' (greedyStep rk D)` via `trInCsr_emit`; extra hypotheses are **name hygiene only**, and an `example` exhibits a witness so the discharge is not vacuous. Budget `emComK = 107n + 94a + 39f + 53T + 43` against `emK`'s `300n + 300a + 200f + 240T + 80` — **no term tight**, worst ratio 107 vs 300. Also landed: the read-back kit the leaf was minted owing (`csrRows_of_csrPrefix` unwraps `winA` **and** `GraphCsr`'s existential into `TrInCsr`-shaped `getElem?` clauses), plus `rowPre_*`, `filter_prefix_filter`, and `row_mem`/`row_nodup`/`of_eq` for `TrInCsr`/`OutCsrAt`/`TransCsrAt`. **Finding — a primitive IMP+ does not have.** The stamp test must be **`<`, not `≠`**: IMP+ has no disequality, so the invariant is sharpened to "every cell `≤ v` on entry", making `ad[u] < v+1` exactly "stamped this round". That buys the missing primitive with **no second array and no clearing sweep** — and a clearing sweep would have been `n²`, breaking `emK`'s `300·n`. **Supervisor imprecision corrected**: the packet pointed at `sq_lt_mcB`, which is a *composition-layer* fact (`n·n < mcB q x`); a pass stated at abstract `B` needs `n·n < B`, already a clause of `StepEmitIn`'s own precondition. The pointer aimed one layer up. | The last program of the augmentation round. **Design worked out by w27's transpose worker and handed over**: four row scans per head with a *uniform* body `read u; ⟨cnd⟩; if em.c = 1 then {t'[p] := u; p++}; A[u] := v+1; j++`, instantiated as (1) input row, `A = ad`, cond `true` — this fuses stamping with the old-arc copy; (2) transpose row, `A = ad`, cond `false`; (3) frat row, `A = sd`, cond `ad[u] ≠ v+1 ∧ sg[u] < sg[v]`; (4) trans row, `A = dg` (scratch, dead after the transpose — **this keeps `cnd`'s reads disjoint from the loop's writes and avoids a case split**), cond `sd[u] ≠ v+1 ∧ ad[u] ≠ v+1 ∧ (sg[u] < sg[v] ∨ mk[u·n+v] = 0)`. One generic step+scan lemma parameterised by an abstract `Keep : ℕ → Prop`. Feed `trInCsr_emit` with `E v = Csr.row off tgt v ++ (Csr.row fof ftf v).filter keepF ++ (Csr.row (trOff D) ttF v).filter keepT`. **Missing kit: the `CsrPrefix` row read-back** (unwrap `winA` + `GraphCsr`'s existential `off`/`tgt`), ~60 lines. **Row stamps need no clearing sweep** — stamp `v+1`, invariant "every cell `≤ v`"; a per-head clear would be `n²` and would break `emK`'s `300·n`. | The IMP+ text for the emit round: a transpose (two nested loops) + adjacency stamping + the three-phase head loop, against the landed `trInCsr_emit` and `emRow_eq_greedyStep`. Estimated materially larger than `SolveAugTrans`'s ~1280 verified program lines. **Budget already pinned** (`emK`/`emK_le_levelCharge`), so this is loop text against a fixed target, not a design question. | Waits on 5b + 5c-i (it tests against their regions). The round body proper: transposes, the `¬D.Adjacent` filter and σ-arbitration, new in-CSR by counting sort; postcondition `= greedyStep σ D`, a `pick`-filter set-equality. **No source implementation exists** — NOdM permits 2-cycles ("at most two arcs may connect x and y"), Lean's `Orientation` forbids them (`asymm`, enforced by `AugStep.tight`), so this program has no reference to copy. Est. 2000–3000 lines. Waits on F6c13b. |
| F7 | discharge the endorsed axiom | waiting | — | — | **also blocked on F6c13b, F5b, G1** (the `N²` peel breaks §7's cover term). needs F6c10a+b, then KB pin + `KsChargeBridge`; `Adm` must be `Inv`-based (w17 finding); then: `Adm` at the run tree (`mkSetup_memLeaf_eq_bot`), instantiate `SolveSpec` via `solveSpec_closed`, `q`/`c` per `hspan`, `temps ≥` boolean depth, `T x := L.const·mcK`, reconcile `Ks` with `exists_mcChargeMS_T`, ∃-close with the `conclusion:` header |

## Campaign log

### 2026-08-26 — `hokS` becomes satisfiable, `F7Bridge` is discharged, and `hdom` disappears

Both repairs landed, plus a third defect found and fixed in the same pass.

**(1) `mcLayout eS eA t`.** The parameterization went exactly as specified —
`hspan` becomes `9 + t + |eS| + (2+|eA|)·q ≤ c` (the literal `11` was `2` temps
plus `9` parse scalars), `parseCom_ok` and `mcCom_ok` at `2 ≤ t`. Every changed
statement is a strict generalization: `t := 2` recovers the landed one verbatim,
and `f7close_modelChecking`'s conclusion is untouched — the
`example : F7Goal := …exists_almostLinearTime_program_modelChecking` still
checks. The cost claim was **proved rather than assumed**:
`mcLayout_const_eq : (mcLayout eS eA t).const = (mcLayout eS eA t').const` by
`rfl`, depending on **no axioms**, so `t` enters only `hspan`, additively, with
`c` chosen last. New generic machinery worth naming: `Ok` is monotone in `temps`
(`expr_ok_mono_temps`/`cond_ok_mono_temps`/`com_ok_mono_temps`), so every landed
compilability proof replays at its own depth and transports up.

**And `hokS` is now satisfiable, at a schedule constant.** `f7Temps S av :=
max 2 (exprTemps (bcExpr av (top S)))`, whose *type* carries the claim —
`{L} → Setup L → (ScatterSentence L → Expr) → ℕ`, no carrier, no graph, no word.
`exprTemps_bcExpr_le` shows the layout depth is the sentence's own left-nesting
height plus the compiled reads' depth, both fixed with `eS`/`eA` before the
input. Anti-vacuity is exact: `f7_bcExpr_ok_at_three` compiles at `t = 3` the
*same* term the no-go theorem refutes at `t = 2`.

**(2) `F7Bridge` discharged** (`f7_bridge_bucket`), and both halves of my
correction were checked rather than taken on trust. `cf` **is** produced before
`n`/`G` (confirmed by `#check`). `b7Cb`'s internals **are** schedule-only — the
`#check` output shows every one of `b7ScatC`/`b7EdgeC`/`b7Cen`/`b7BotA`/`b7M`/
`topEvalCost` taking only `{L}`, a `Setup L`, `ℓp` and ℕs. But `Kc` did sit
inside additively and is `Θ(n+m)`, exactly as relayed. **`crl` was *not* a
problem** — `hKrl` is already a rate (`Krl x ≤ crl·(|x|+1)`), so my message was
half wrong there. Repaired as sketched: both stage figures now ride the `|x|+1`
factor the right-hand side already carries, and the change *generalizes* the old
theorem (`ckc := Kc` recovers it).

**The top scatter is linear in the input at a schedule-only rate** — the question
I told the worker to stop on if it failed. `f7_topScatK_le` gives
`topScatK N ns atoms ≤ f7ScatRate atoms · (N + ns + 1)` with `f7ScatRate` reading
only the atoms' `r` and `t`, and `f7_carrier_slots_le` turns `N + ns + 1` into
`|x| + 1` off `EncodesGraph`. What is *not* proved is `∑ v, G.degree v =
2·edgeCount x`; that is `TopScatterAll`'s own column and enters as an inequality.

**A fourth defect, in the worker's own file, and the reason `hdom` is gone.**
`f7close_of_closed_scr` had `Kc : ℕ` **hoisted in front of `∀ n G w`** — with the
real stage that makes its own hypothesis unsatisfiable, the same quantifier
disease one level down. Generalizing it to a graph-indexed `Kctop` exposed a real
tension: `hdom` gives `graph-indexed ≤ Ks` while `F7Bridge` needs `Ks ≤ cB·(…)`,
the **opposite** direction, so no one-sided `hdom` can supply both. The
resolution is that **the word already determines the graph**: `EncodesGraph` pins
`n = vertexCount x` and adjacency via `adj_iff`, so `f7_encodes_congr` (no
`Classical.choice`) gives `f7Decode_eq` as an *equality* and `f7Ks_eq` prices the
pipeline exactly. **`hdom` is discharged, not carried** — it is absent from the
final composition.

**One more obstruction nobody had mentioned**: `F7Bridge`'s `∀ cf` is not free,
since the landed cover column holds at the produced `cf₀` and no smaller. It is
only a constant factor — `coverCFSel` depends on `cf` through `⌈cf·N^δ⌉₊` alone
and `sweepCharge` is *affine* in `D` — so `b7c_chargeTotal_coverCFSel_le_mul`
makes `ccov := ⌈cf₀⌉₊·(a+b+c)` work at every `cf ≥ 1`, uniformly.

**What remains in `f7close_of_closed_scr_bucket`**: `hclosed` (which
`f7s_solveSpec_closed_scr` already reduces to **`FrameStepAllScr` alone**),
`hKrl` (the sibling's `f7s_Krl_le` at `crl = 81`), `hKc` (the arithmetic is here;
the `ns` identification is `TopScatterAll`'s column), and `hokS`/`hnw` (reduced
to `rootLoadCom`, `chainCom`, `scatCom` and the read names at `t = f7Temps S av`).
No `hdom`, no `hbr`.

Elaboration 3–8 s across all eight files. One operational note from the worker's
worktree — which predates the string-length fix — is now moot: touching
`ProgCodegenLayout` invalidated `SolveMachPrepComp2` at 1501 s and OOM-killed
twice at 15 GB. In the main checkout that file is 9 s.

Left alone deliberately: `SolveMatTop.lean`'s layout note still says "`mcLayout`'s
base `temps = 2`", stale but compiling, in a file the concurrent top-scatter work
touches.

### 2026-08-26 — the 30-minute gate was `rfl` on a string length; the package now builds in 64 s

**Both standing hypotheses about the elaboration cost were wrong, and only the
profiler settled it.** Jan's was that ~21-minute elaborations are inherent to the
Isabelle-style refinement idiom. Mine, inherited from the file's author, was
`open Classical in` over statements mentioning `SimpleGraph.degree`, with
instance search re-deriving decidability under `Classical.propDecidable`. The
per-file numbers refuted Jan's (2245-line refinement files at 17 s against
978-line ones at 1236 s), but they said nothing about *which* construct was
paying, and I let a plausible mechanism stand unmeasured for several landings.

The profile: elaboration 947 ms, typeclass inference 467 ms, tactic execution
29.7 s, **type checking 1460 s**. The cost is entirely **kernel defeq**, in one
idiom — `lv_ne_of_base_ne (by rfl) …`, whose `by rfl` discharges
`s.length = t.length` at two distinct four-character string literals.

| goal | proof | time |
|---|---|---|
| `("sv.n" : String).length = ("sv.m" : String).length` | `by rfl` | **103 s** |
| same | `by decide` | 3 s |
| `("sv.n" : String).length = 4` | `by rfl` | 4 s |
| `("sv.n" : String) ≠ "sv.m"` | `by decide` | 3 s |

So the kernel will unfold `String.length` against a literal in seconds, but
proving two such lengths *equal to each other* by `rfl` costs ~104 s **per
declaration**. Cross-checks rule out both prior hypotheses outright: every
`SimpleGraph.degree` / `Set.ncard` / `open Classical` statement in the file type
checks in **106 ms**, and the eight `lv_notMem (by decide)` pool lemmas cost
**828 ms** together — while the seven "arena cells, pairwise" lemmas timed out at
200 s with `rfl` and take **3 s** with `decide`.

Fix: `(by rfl)` → `(by decide)` at `lv_ne_of_base_ne` / `lv_ne_lit` /
`lv_ne_of_level_ne`. `lv_inj (by rfl)` is left alone — both bases are the *same*
literal there, so that `rfl` is syntactic and free. No statement changed.

| | before | after |
|---|---|---|
| `SolveMachPrepComp2` | 1236 s | **9 s** |
| `SolveMachPrepComp` | 576 s | **7 s** |
| whole package | ~30 min gate | **64 s / 3565 jobs** |

The worker also found the same pathology in three files outside its ownership —
`SolveBlocks` **228 s → 5 s**, `SolveGlueLoop` 25 s → 4 s, `SolveScrFrameSat`
17 s → 4 s — and measured them on patched scratch copies rather than editing
them. Applied at this landing by the supervisor; a package-wide grep now finds
**no remaining occurrence** of the idiom.

**Lesson, and it is about supervision rather than Lean.** I was right that the
cost was localized and wrong about why, and I put the wrong mechanism into three
successive packets as "the standing suspect". A measurement that distinguishes
two hypotheses is cheap next to the four landings that ran at 30 minutes each.
Profile before propagating a diagnosis.

**Task 2 — the concrete blocker is gone.** Twelve write-set lemmas in the landed
`warrs_restrictCom` shape, all `rfl`: `clusterRowCom` writes `[la]`,
`mkBatchCom` writes the bit and index regions, and **`centreIdxCom` writes no
array at all**. With them, `warrs_prepC` gives the closed form the residual's
frame clauses want, and the three corollaries follow — `prepC_frame_deep`
(`prepScr_out`'s `hdeep`), `prepC_frame_level`, `prepC_frame_cover`.

**Task 3 — all nine stages wrapped, the chain not.** `SolveMachPrepComp3.lean`
(708 lines) wraps the seven remaining stages at `prepC`'s own names, BFS and
supports at `2·S.R` (never `S.R`), profiles at the pre-isolation child and the
**parent's** palette. `ChildLoadPartsScrAll` is **not** discharged — the fourteen
`Spec.seq` steps and their `hmid` obligations remain, and no partial or restated
version was landed in their place.

**Fourth invisible binding requirement of this pass: `PrepCoverNames`.**
`ChildLoadPartsScr` takes the cover's array names `ca`, `co`, `cm` as parameters
and relates them to nothing, yet its own postcondition demands the pass leave all
three untouched and `clusterRowCom_spec` asks for `la ≠ cm` outright — so the
**first** stage is unreachable without it. Named as a `Prop` bundle with
`prepCoverNames_exists` witnessing satisfiability, alongside two further
hypotheses put on their stages rather than buried (`2·S.R + 1 ≤ hbf j`, which is
not a landed pin, and the colour writer's `Dp`/`Dc` triple).

138 top-level theorems checked with `#print axioms`: zero `sorryAx`.

### 2026-08-26 — `CoverAllIn` closes down to `CovAugAdjSelIn`, and three augmentation seams are proved not to close

`covAllJoin_coverAllIn` (`SolveCoverAllJoin.lean`, 840 lines) discharges
`CoverAllIn` **verbatim** at `selOrderingRoutine bucketSel R`, with **exactly two
surviving hypotheses**: `1 ≤ q` and `CovAugAdjSelIn`. Every name bundle of both
inputs is discharged at concrete bases, and `covAllJoin_augRoundIn` restates the
round at the *real* `Smp`/`Ssw` (the landed `_std` pins them at `True`, which a
composition cannot use), so the rounds are not a seam.

Budget for the whole cover stage, coefficients stated:
`Kord = augChainCost 545 554 113 · 1025 455 588 305 287 · 484 432 124` — the
bucket peel folds into the augmentation's own shape via
`slotCount (D.toGraph) = 2·arcCount D` — and `Ksw = peelK (12R+362) 154 192`.
All eight gates of `augChainCost_le_selChainCharge` hold at `k = 545`, giving
`≤ f·m^{1+δ} + (238+287R)` on a nowhere dense class, one δ inside §7's envelope;
the sweep closes at `(12R+708)·chargeTotal (coverCFSel …)`. Every figure is
`A.N`, `arcCount`, `fratPairCount`, `transPairCount`, `clusterMass` or
`peelEdgeWork`. No term quadratic in the carrier.

**And then it declined to force the composition, with proofs.**
`covAugAdjSelIn_of_base_rounds_sym` cannot be instantiated from the landed
leaves: three shared parameters are over-determined.

1. **`coverAllBase_hSbd_unsatisfiable`** — `augBasePeelIn_bucketPeelBuild` *pins*
`Sbd` to three length clauses against the **root** carrier `n`, while
`augBaseOrientIn_orCom`'s `hSbd` asks the same `Sbd` to bound `io`/`it`/`cn`
against `σ.vars (arenaNames j).nN`, which it never constrains. A state whose
carrier cell exceeds every array refutes it — **unconditionally, for every choice
of the six names**. The three base leaves have no common `Sbd`.

2. **`coverAllBase_hSrd_not_ardSrd`** — `augBaseOrientIn_orCom`'s `hSrd` duty is
handed only an agreement-off-three-names clause and **no length clause**, while
`ardSrd` sizes `io j` and `it j` at `ardCap`. So for *every* `Sbd` satisfiable at
even one state, the duty fails. Repair is one line: add
`(∀ b, |σ'.arrs b| = |σ.arrs b|)` to `hSrd`/`hSmp`/`hSsw` — **the theorem's own
proof already has it** as `hlen` from `specArrsLength` and uses it two lines
later, and its sibling already passes it. **This also refutes a claim I made in
the w38 packet**: I said `Sbd` was a free parameter of `augBaseOrientIn_orCom`
and hence satisfiable by choice. It is not — (1) pins it. Recorded so the next
worker does not inherit the error.

3. **`coverAllSym_srd_forces_constant` / `_no_emission`** — the sharpest of the
three. `augSymCsrIn_symComW`'s `hSrd` asks the *round invariant* `Srd` for
`|σ.arrs (stO j)| = 2·σ.vars (nA j)`, an **equality**, because `AugSymCsrIn`'s
postcondition is a bare `GraphCsr`. But `ardCopyCom` advances `nA` each round and
no run changes a length, so `AugRoundIn` at `augStInNW` plus that `hSrd`
**proves** `arcCount (chain i) = arcCount (greedyStep …)` and hence, via
`arcCount_greedyStep`, that **every round emits no fraternal and no transitive
edge** — at every input, level, admissible non-edgeless arena and round. The
augmentation would be vacuous. Same shape as `augRd_augStInN_forces_constant`,
one level up.

So the exact-length trap has now appeared **eight** times, and (3) is the first
instance where the demanded figure *moves over the loop that must maintain it* —
which is what makes it lethal rather than inconvenient. That is the question to
ask at every future occurrence: is the demanded figure stable over the loop?

w39 dispatched off w38's branch (so it sees these no-go theorems as its
specification) to repair all three and finish `CovAugAdjSelIn`. Its packet
carries the correction to my `Sbd` claim, and requires that repair (3) be
**re-tested against the no-go theorem** — if the caller's obligation still forces
a constant emitted graph, the repair is not a repair.

Elaboration 11 s cold. Axioms clean on all fourteen results.

### 2026-08-26 — both seam residuals discharged, and `SolveSpec` now needs `FrameStepAllScr` ALONE

`SolveF7Seam.lean` (997 lines) discharges `RootLoadSpec` and `TopScatterAll`
verbatim, and the leaf's real discovery is that **they were never two leaves**.
Each already had a landed discharger (`rootLoadSpec_of_csrLoad` with its own
residual already closed, and `topScatterAll_of`), both stopping at a descriptor
hypothesis, and `solveSpec_closed_scr` needs **one** `Scr` meeting both *plus*
`hfr`/`hLVbt`/`hLRbot`/`hscr`. So it is a single descriptor with six demands.

The capstone: **`f7s_solveSpec_closed_scr` produces `SolveSpec` from
`FrameStepAllScr` alone** plus instantiator data. And `f7s_Krl_le`
(`Krl x ≤ 81·(|x|+1)`) discharges the ledger bridge's last hypothesis, so
`f7s_KsChargeBridge_bucket` **carries the bridge with nothing standing**.

Descriptor choice, and the reasoning is the right one: `RankScrTower` plus an
allocation tower, **not** `prepScr`. `RankScr` at the level window is the only
*content* clause either seam reads, and the weakest descriptor is correct
because `Scr` sits in both **preconditions**; `SolveScrFrameSat` already proves
`ScrFrame`/`ScrStep`/`hLVbt`/`hLRbot` for it; `ScrFrame.and_lens` makes the
allocation conjunction free; and every remaining demand is a length clause,
which is the only kind demandable at all since no IMP+ run changes a length.

**The trap, seventh occurrence — and this time the landed hypothesis is
inconsistent, not merely unavailable.** `f7s_hScr0_refuted` proves that
`SolveGlueLoad.rootLoadSpec_of_csrLoad`'s `hScr0`, at any content-carrying
descriptor with `0 < N`, yields `False`: raise the level-0 carrier cell, flip one
scratch cell — lengths unchanged, window dirty. So at any descriptor that
carries content, that landed theorem proves nothing. This is one seam further
out than the one `rankScr_not_length_only` closed, and it is the reason the file
needed its own §3 rather than reusing the landed assembly directly.

Three docstring drifts reported, none in the worker's files: `BlockPre`'s
(`SolveChain.lean:195`, contradicting its own file's §3b and module docstring),
`SolveGlueLoad.lean:41` (which describes the very hypothesis just refuted), and
`SolveSeamTop.lean:8-9`. The two the packet named had already been repaired.

**A cost note the worker raised that turned out to matter elsewhere.**
`Kc = topScatK n (∑ deg) atoms` is Θ(n + m) — linear in carrier and slots, no
`N²`, fine in itself — but `b7_KsChargeBridge` absorbs `Kc` into the bridge
constant `cB`. Under the landed `KsChargeBridge` that is harmless because `cB` is
chosen after `(n, G)`. Under **`F7Bridge`**, where `cB` must be fixed *before*
them, it is not — so my instruction to w37 that `b7Cb` is uniform was too strong:
its *internal* figures are schedule-only, but `Kc` and `crl` are parameters, and
both are input-sized. Relayed mid-flight with the repair's shape, which is
already visible in this leaf's own `f7s_Krl_le`: the bridge's right-hand side
carries a `|x|+1` factor, so an input-sized stage figure should ride that factor
rather than sit inside `cB`. Told w37 to stop and report if `Kc ≤ K_c0·(|x|+1)`
cannot be had with a schedule-only constant, since that would be a headline-level
finding rather than something to work around.

Integration note for whoever discharges `FrameStepAllScr`: `f7s_solveSpec_closed_scr`
pins residual 1 to `f7sScrH`. `PrepAlloc` and `BatchWidthScr` are length clauses
and drop straight into `F7sAlloc`, but `prepScr`'s `∀ i, σ.vars (arenaNames i).nN
≤ n₀` is a **cell** clause over all levels — not `and_lens`-compatible, and
outside `rankScrLV`'s pool at level `j`. Either restrict it to `i ≥ j` or widen
`LV i` to carry every carrier cell; the latter keeps `hLVbt` and `hctrLV`.

Elaboration ~6.5 s. Axioms clean on all 18 results — and an early draft of this
file *did* leak `sorryAx` with no literal `sorry`, caught by the `#print axioms`
gate. Fourth occurrence today.

### 2026-08-26 — the cover stage became composable while nobody was looking; w38 dispatched

Tracing what `FrameStepAllScr` still needs turned up a leaf that had quietly
become ready. `frameStepAll_of_cover_loopScr` has two content hypotheses,
`CoverAllIn` and `CentreLoopAllScr`. The second waits on the prep composition
(w34). **The first does not wait on anything any more** — every link in its
chain was discharged in the course of tonight, and no one had joined them:

`coverAllIn_of_order_sweep` ← `CovSweepIn` (w37's `sweepClose_covSweepIn`) +
`CovOrderIn` (`covOrderIn_bucketPeel`, unconditional on the peel side) ←
`CovAugAdjSelIn` (`covAugAdjSelIn_of_base_rounds_sym`) ← `AugBaseIn`
(`augBaseIn_of_adj_peel_orient`, its three leaves all discharged) + `AugRoundIn`
(w41, conditional only on `ArdWord`, which F7-c's `f7q` already bounds) +
`AugSymIn` (`augSymIn_of_symCsr_build` with **`augSymCsrIn_symComW`**, the
`augStInNW` variant w41 added — the un-`W` one cannot be used, since
`augStInNW → augStInN` is false).

Dispatched as w38 with the three pinned facts its predecessors paid for: `sel`
must be `bucketSel` (so `covAugAdjIn_of_base_rounds_sym` at `mdSel` is
unusable); the `it j` over-allocation `ardCap N = 2N³+N²+N+1` is a requirement on
the base pass's free `Sbd` and must be *chosen*, not discovered; and the
exact-length trap. Its cost clause names every legal currency explicitly, because
the last foreign-currency term to hide a `Θ(N²)` was inside this very sweep.

Four workers now: prep composition, the two seam residuals, the temps/bridge
repairs, and this. That is one per remaining piece of the axiom's proof.

### 2026-08-26 — F7-c closes the last mile, and finds three defects between `SolveSpec` and the axiom

`f7close_modelChecking` (`SolveF7Close.lean`, with `SolveF7CloseQ` and
`SolveF7CloseCompose`) concludes `F7Goal`, and `F7Goal` is checked to be the
endorsed axiom's type **on the nose**:

```lean
example : F7Goal := Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking
```

An `example`, so no declaration depends on the axiom, and it is the only mention
of it — it elaborates only if the two `Prop`s are defeq. Nothing weakened:
exponent `1+ε`, the axiom's set-builder verbatim, the side condition per-`(n,G,w)`
inside.

**Every constraint on `q`, collected and discharged** (`SolveF7CloseQ.lean`),
`f7q = 1 + f7qPrep + f7qB + (3K+2)`: the input/fit bound (free); `PrepWB` at
`B = mcB q x`, discharged in full; `solveSpec_closed_scr`'s `hB`, whose
`2^{pal ℓ}·(Kq+1)` term **makes `q` a tower in the quantifier rank** — harmless,
because `q` reaches the axiom only through `c`, never the exponent; and
`ardWordBound_of_inDegLE`'s `q ≥ 3K+2`, with `f7_exists_selChain_inDegLE_sq`
producing both halves at once at `δ' = 1/(2·16^R)` and
`K = ⌈((3c₀+5)^{16^R})²⌉₊ + 4^{16^R}` (the second summand is what handles `m = 0`).
`R` is fixed before `δ'`, so no circularity. Every other `< mcB q x` obligation in
landed files was swept and reduces to `1 ≤ q` or routes through
`ArdWord`/`PrepWB`/`hB`. The list is complete.

**Three defects, all between `SolveSpec` and the axiom, none previously visible.**

1. **`KsChargeBridge`'s quantifier order is wrong for F7** — genuinely, not
cosmetically. It puts `∃ cB` *inside* the fixed `(n,G,c,w)`. The axiom's `T` is
fixed **before** `n` and `G`, and an encoding `x` determines its own `(n,G)`, so a
per-graph family `{cB(n,G)}` cannot be uniformized after the fact and yields no
`T` at all. `F7Bridge` is the same statement with `cB` — and the cover constant
`cf`, which the landed charge theorem *produces* — pulled out front, and
`ksChargeBridge_of_f7Bridge` proves it implies the landed obligation at every
instance. **This lands on the bridge discharged hours earlier**, but should be
cheap there: `b7Cb`'s figures read only `S.R`, `S.width`, `S.pal`, `S.depth`,
`ℓp` and the level families — no carrier and no input word — so the constant is
already uniform in `(n, G)` and only the statement's binder order has to move.

2. **`solveSpec_closed_scr`'s budget mentions `G`** — `fun x => matK x + (Krl x +
(KB ℓ 0 (rootArena G col) + …))` is not a function of the word alone, so it
cannot be `ProgCodegen.mcK`'s `Ks`. Repaired rather than weakened by
`f7_solveSpec_mono_Ks` (a lift of `Spec.mono`), at the cost of one hypothesis
`hdom` that the ledger bridge has to prove in the same place anyway.

3. **`hokS` is unsatisfiable for the real pipeline as `mcLayout` stands.**
`mcLayout eS eA` hard-codes `temps = 2` (`f7_mcLayout_temps`, by `rfl`), while
`Expr.Ok` charges one temporary per level of **left** nesting and
`bcExpr (.and b c) = .mul (bcExpr b) (bcExpr c)` nests left — so three nested
conjunctions already need `temps ≥ 3`. Machine-checked witness:
`f7_bcExpr_not_ok_at_mcLayout` proves `¬ Expr.Ok (mcLayout eS eA) (bcExpr av
(.and (.and (.and .tru .tru) .tru) .tru)) 0` for **every** `eS`, `eA`, `av`.
Two landed docstrings assume F7 can raise `temps` — `ProgCodegenLayout`'s ("a
bigger `temps` only shifts the constant in `hspan`") and `SolveMatTop`'s ("F7
instantiates the layout with `temps ≥` the compiled combination's depth") — but
`mcLayout` has no such argument. The repair is one parameter on landed
definitions: `mcLayout eS eA t`, `hspan` becoming `9 + t + |eS| + (2+|eA|)·q ≤ c`
(the literal `11` is `2` temps plus `9` parse scalars), `parseCom_ok` needing
`2 ≤ t`, `mcCom_ok`'s epilogue `0 < t`. `Layout.const = 3·idxLen + 13` counts
**arrays**, so the machine constant and the time bound are untouched. Not made
here — those are landed files — and everything else in F7-c transports to the
parametric version verbatim.

The worker also hit the warned-about failure mode during development: an
elaboration error leaked `sorryAx` into three theorems in a file with no literal
`sorry`, caught only by `#print axioms`. Third occurrence today; the gate rule
holds.

Elaboration 4.8 / 3.7 / 3.7 s. `SolveF7Close.lean` adds `import Lax3.ModelChecking`
— the first time the proofs package imports the concept module, used only by the
verbatim-check `example`.

### 2026-08-26 — `KsChargeBridge` DISCHARGED: F7-b closes, and the two audit gaps are proved

`b7_KsChargeBridge` (`SolveF7Bridge.lean`, 1179 lines + `SolveF7BridgeCover.lean`,
207) concludes `KsChargeBridge` at **exactly** `solveSpec_closed_scr`'s budget,
with `KB := chainKB`. The concrete `cB` reads **only schedule constants** —
`S.R`, `S.width`, `S.pal`, `S.depth`, `ℓp`, the level families and their scatter
atoms. No carrier, no input word, nothing quadratic; the per-node terms go
against `allocC`'s `A.N` and `readC`'s `A.N·(1+|ℱ_j|)`, and every column's
argument is `childN`, `Σ_v preG.degree v`, or a cluster mass.

The capstone `b7c_KsChargeBridge_bucket` carries the landed `(cf, c', T)` of
`exists_mcChargeMS_T_bucket_coverColumn` **and** the bridge together, on every
member of the class, at the machine's real routine, column and budget — leaving
**`hKrl` as the single hypothesis**, which is a `RootLoadSpec` residual, not a
ledger one.

**(1) The ⊥-node excess: the bound exists and is better than feared.**
`b7_chainKB_bot` gives `chainKB k j A ≤ b7BotA(k)·A.N + b7BotB` at `A.G = ⊥`
with `b7BotA(k) = M₀ + k·(D + B')` — **linear in the fuel, not `2^k`** — because
the branching stops at carrier one (`childN_eq_one_of_bot`), so each level
multiplies by the node's own `A.N` rather than by a branching factor. Against
`chargeTotal (botC S j A) ≥ A.N` that is a schedule constant times the node's own
ledger entry. Both side conditions discharged at the real budgets:
`b7c_peelK_le_bot` proves `peelK a b c S A π = (a+b)·A.N` at `A.G = ⊥` outright
(every cluster a singleton, every back-degree `0`), and the glue's `hglue` is
only `6 ≤ Kglue`, met by the constant.

**(2) The scatter slack: the form I specified was false, and the worker said so.**
I asked for `scatterK ≤ c·(greedyScatterCost + N + ns + 1)`. In fact
`scatterK N ns r t = 41N + (markK+30)·t + 24` while `greedyScatterCost … t` is
`0` at `t = 0`, so **`scatterK ≤ c·greedyScatterCost` is false**, and the mixed
form needs the residue placed somewhere real. `b7_scatterK_le_greedy` proves
`scatterK ≤ 130·((t+1)(r+1))·(greedyScatterCost + N + ns + 1)` and
`b7_centreScatterK_le` charges the residue **against the supports column**
(`b7_supports_ge`), a cluster-mass figure the ledger already sums. `t` and `r`
are atom fields fixed by the schedule, so the factor is a constant per atom.

**A correction to my packet, and the right one.** I had the checkpoint asking
`hKcov` at *every* arena. That is not satisfiable by the machine's own cover
budget: `peelK_le_coverCFSel_total` and clause 3 of
`exists_mcChargeMS_T_bucket_coverColumn` both carry the weak-colouring side
condition `A.G ⊑ G`, a fact about arenas the run actually reaches, not about all
arenas. The fix is an `Adm` closed under the frame step's children plus an
`i ≤ S.depth` guard, discharged through `ardIsContained_of_chainAdm`;
`b7_KsChargeBridge_all` keeps the unrestricted form for anyone who wants it. And
`hKcovBot` deliberately stays unrestricted, because **`chainAdm` is genuinely not
closed under `childArena` at edgeless arenas** (`chainAdm_child` needs
`¬ A.G = ⊥`) — which is exactly why the two cover clauses have to be split
rather than unified. Second time today that the `⊥` branch has forced a split
nobody anticipated.

Elaboration: 7.7 s and 3.6 s — squarely in the refinement-style band, further
evidence the prep files' 576 s / 1236 s is a local pathology rather than the
idiom. Axioms: the three standard, plus UQW on exactly the three results quoting
`headlineSetup`; no `sorryAx`, confirmed by forced re-elaboration with the
oleans deleted and independently by `lean_verify` on both capstones.

**F7's remaining residuals after this**: `FrameStepAllScr` (the prep composition
is w34's), `RootLoadSpec`, `TopScatterAll`, and F7-c's constants (w35's).

### 2026-08-25 — overnight wave: the three remaining F7 pieces run in parallel

Jan's standing authority renewed for the night. Three workers, one per remaining
piece of F7, chosen so no two share a file and none blocks another:

- **w33 — `KsChargeBridge`** (F7-b). Continuation; its first task is the two
  elaboration errors leaking `sorryAx` into the checkpoint. Then the `⊥`-node
  excess (`chainKB` at an edgeless arena `≤ K·(A.N+1)`, needing `Kcov` and
  `Kglue` in `O(A.N+1)`) and the `σ.t = 0` scatter slack — the only two terms of
  the audit without a finished column.
- **w34 — the prep composition.** Elaboration fix first (the gate cannot afford
  30 minutes a landing for the rest of the campaign), then the three missing
  `warrs`/`wvars` lemmas, then `ChildLoadPartsScrAll`.
- **w35 — F7-c, the last mile.** From `mc_computesInTime_of_solveSpec`
  (`ProgCodegen.lean:221` — the axiom's `ComputesInTime` on the axiom's
  admissible set verbatim) to the endorsed axiom, taking `SolveSpec` and the
  ledger bridge as named hypotheses. Its real content is the constants: `eS`,
  `eA`, `q`, `c` with `hq`/`hqc`/`hspan`, and **`q` is not free** — the packet
  points it at `ardWordBound_of_inDegLE`'s `q ≥ 3K + 2` and at `PrepWB`'s own
  lower bound, and asks for every constraint on `q` collected in one place and
  maxed, rather than a number chosen blindly. `hokS`/`hnw` and the choice of
  `eS`/`eA` are one problem, not two: the name pools must contain everything the
  pipeline mentions.

Three workers on 4 cores is above the load I set earlier, accepted here because
the F7-c leaf is arithmetic and plumbing rather than program text, so its build
share is small.

### 2026-08-25 — second container restart, and the compile-the-checkpoint rule pays immediately

The container was replaced again; both running workers died. Recovery as before,
but this time the new rule was applied instead of stated: **I compiled the
surviving checkpoint before saying anything about it.**

`SolveF7Bridge.lean` (1051 lines, the ledger-bridge leaf's in-flight state)
**does not build**, and `#print axioms` reports **`sorryAx`** — in a file
containing no literal `sorry`. Two elaboration errors at `:982` (application
type mismatch) and `:999` (a `rewrite` that finds no occurrence) are leaking it
in. Under the old habit I would have run `grep -c sorry`, seen `0`, and
described the checkpoint as clean for the third time. The errors are now handed
to the continuation worker as its first task.

The other worktree had written nothing — that leaf restarts clean.

Both branches pushed to origin this time, not merely committed locally: the
first restart survived only because the *filesystem* survived, and that is not
something to rely on twice.

**Elaboration cost, measured rather than argued.** Jan's hypothesis was that
~21-minute elaborations are inherent to the Isabelle-style refinement idiom and
should be accepted. The per-file numbers from the gate say otherwise:

| file | lines | elaboration |
|---|---|---|
| `SolveMachPrepComp2` | 978 | **1236 s** |
| `SolveMachPrepComp` | 945 | **576 s** |
| `SolveAugSymMerge` | 2245 | 17 s |
| `SolveAugRoundIn` | 1961 | 14 s |
| `SolveAugRoundSeams` | 1398 | 10 s |

The last three are the same `Spec.seq`/`Spec.frame`/`Spec.mono` idiom over
machine programs with budgets, at twice the size — ~7 ms/line against
~1264 ms/line, a factor of ~180. The whole package is 3565 jobs and rebuilds
warm in ~4 minutes; these two files alone took the landing gate to ~30. So the
aggregate cost of the refinement style is already paid and is fine; what is here
is a localized pathology, and the standing suspect (`open Classical in` over
statements mentioning `SimpleGraph.degree`, making instance search re-derive
decidability under `Classical.propDecidable`) has exactly that signature. The
next leaf measures it with the profiler before touching anything, and is told a
correct diagnosis beats hitting the target.

### 2026-08-25 — the prep composition's side conditions, and a third invisible binding requirement

`ChildLoadPartsScrAll` is **not** discharged, and the leaf says so — no wiring
theorem was written either, so nothing in the branch is labelled a discharge
that isn't one. What it delivered instead is everything the fourteen `Spec.seq`
steps will need, and one finding that changes the residual's shape.

**Finding — `ChildLoadPartsScr` relates `B` to nothing.** It quantifies
internally over every `k j A u` and states no word bound, while every one of the
nine stage contracts demands them (`restrictCom_specW` alone wants `A.N < B`,
`A.N² < B`, `n₀ < B`, `A.N·Λc < B`, `A.N·ℓp·(hb+1) < B`; `profilesCom_specW`
five more). **This is the `AdjDeleteIn` shape a third time** — "quantifies over
every `N` and relates none to `B`", the defect that made `AdjDeleteIn` outright
false. The worker did **not** claim falsity here, and was right not to:
`ChildLoadPartsScrAll` is parametric in `Scr`, and `Scr := fun _ _ => False`
makes it vacuously true, so falsity is a claim about the *instantiation*, not
the definition. The repair is `PrepWB S ℓp hbf n₀ B` — four clauses at the
**root** carrier and the schedule only, hence uniform in `j`, `A`, `u` as the
residual's internal quantifiers require — with thirteen derived per-stage bounds
and `prepWB_exists` proving it satisfiable. At `B = mcB q x` it is a lower bound
on the schedule constant `q`, not a new obligation on the input.

**The allocation audit is the leaf's real content**: nineteen lemmas deriving
*every* allocation clause of *every* stage from `prepScr` alone, at each stage's
own data-dependent dimension. Two clauses would otherwise have been missed — the
child colour region must carry both `restrictCom_specW`'s `X.ncard · S.pal j`
**and** `colWriteCom`'s `childN · S.pal (j+1)`, the second being the larger,
which is *why* `PrepAlloc` is sized at the child's palette; and the batch index
region's clause is an **equality**, so a longer allocation would break it. The
recurring trap discharged as an audit rather than asserted.

**A third invisible binding requirement**: `clusterRowCom_spec` asks that every
cover offset fit a word, and nobody upstream states it.
`prep_clusterCsr_offset_le` gets it from `ClusterCsr`'s partial-sum structure
(offsets `≤ N²`) and closes it against `PrepWB`.

Also landed: the four stage scalar pools and the profiles stage's `ProfNames.Ok`
at the pass's family (21 clauses, uniform in batch width and class count), and
two stages fully instantiated at `prepC`'s own names with every side condition
discharged (`prep_restrictStage`: 13 name clauses, 5 word bounds, 7 allocations;
`prep_mkBatchStage`: 32 disequalities plus the index-region equality). Budgets
untouched — the wrappers carry the landed contracts' verbatim, and no `A.N` term
is introduced.

**Two costs recorded, both now leaves rather than notes.**
(i) `SolveMachPrepComp2` takes **21 minutes** to elaborate and
`SolveMachPrepComp` about 7 — a tax on every future gate. Suspect: `open
Classical in` on statements mentioning `SimpleGraph.degree`, where instance
search with `Classical.propDecidable` in scope is expensive; the ~120 `by decide`
string side conditions are *not* the hot spot.
(ii) **`prepC` has no `warrs` lemma and none can be assembled from landed
material**: `clusterRowCom`, `centreIdxCom` and `mkBatchCom` have no
`warrs`/`wvars` lemmas at all — their `Spec` postconditions carry the frame
instead. A chain can thread the frame through postconditions, but the closed-form
"`prepC` writes only these arrays" that `prepScr_out`'s `hdeep` and
`ChildLoadPartsScr`'s two frame clauses want needs those three added first. That
is the concrete blocker for the discharge.

**Supervisor error, second of its kind.** I checkpointed the interrupted
predecessor's file and reported it clean. It did **not compile** — three `Nodup`
bundles whose `simp only` set left a trailing `∧ ¬False`, so `refine` handed
`lv_ne_of_base_ne` a conjunction and its `by rfl` unified two base
metavariables into `?m ≠ ?m`. Fixed by adding `not_false_eq_true` to three
goal-side simp sets. Together with the `sorryAx` miss earlier today: **a
checkpoint is not evidence of anything until it builds.** I will not describe an
interrupted worker's file as clean again without compiling it.

### 2026-08-25 — `AugRoundIn` DISCHARGED, and F7's `q` gets a number

`augRoundIn_ardRoundCom` (`SolveAugRoundIn.lean`, 1961 lines) concludes
`AugRoundIn` **verbatim** at `AugSt := augStInNW io it nA`, program
`rdC j = frZero(ad); frZero(sd); frZero(dgE); augRdBody; ardClearCom; ardCopyCom`,
coefficients **`1025, 455, 588, 305, 287`** — conditional on **exactly one**
named hypothesis beyond name and frame conditions, `ArdWord`.
`augRoundIn_ardRoundCom_std` instantiates the whole bundle at 27 concrete names
with `Smp = Ssw = fun _ _ => True`, leaving `ArdWord` alone. `augRdRoundK_eq`
makes the budget an equality with `augRoundBudget`; the coefficient gates
`kn ≤ 3k, ka ≤ 2k, kf ≤ 4k, kt ≤ 2k` close at `k ≥ 342`, inside the landed
`k = 475`. Under `InDegLE d` the round is `n·(1025 + 455d + 893d²) + 287` — no
time term quadratic in the carrier.

**All four gaps closed.**
(a) The region mismatch that stopped the augmentation composing at all is
repaired **beside** the landed theorem, which is untouched: `augSymCsrIn_symComW`
restates the symmetrization at `augStInNW`. `SolveAugSymMerge`'s own Finding 3
was right — the pass reads the region only through `trInCsr_of_inNCsr` and
`hst.2`, both clauses of `augStInNW`. **The three residuals of
`covAugAdjSelIn_of_base_rounds_sym` now speak one `AugSt`.**
(b) `ardClearCom` discharges `TrClearAt` verbatim at `19n + 23T + 20`.
(c) `ardCopyCom` discharges `InCsrCopyAt` at `12n + 12a + 32`.
(d) See below.

**The verdict on the word bound, and the number F7 has been missing.** The
out-of-date half was indeed out of date: **`chainAdm` supplies the structural
half.** `Inv`'s third clause carries `ReachedS (2R) G_0 rounds (map A.up A.G)` on
every arena with an edge — exactly `AugRoundIn`'s case — and `reachedS_le` gives
`A.G` contained in `G_0`, which is what `exists_selChain_inDegLE_pow` consumes.
But turning `n*d^2` into `< mcB q x` is **not** a fact about any `Adm`: it
compares the class's density constant with the schedule's.
`ardWordBound_of_inDegLE` states and proves the inequality:

> if some `K` has `d^2 <= K*(N+1)` at every carrier `N`, then **`q >= 3*K + 2`**
> makes `N + N^2 + a + f + T + 1 < mcB q x` at every arena of every input.

The condition on `K` is a condition on the exponent: `d` is
`(3*ceil(c_0*m^delta')+2)^(16^R)`, so `d^2 <= K*(m+1)` asks
`delta' * 16^R <= 1/2` — **free**, because `exists_selChain_inDegLE_pow` holds at
every `delta' > 0` with `R` fixed first. So F7-c's "choose `q` per `hspan`" now
has an actual inequality to satisfy rather than a placeholder.

**Changes to material landed one commit earlier** (all in files the worker
owned, all reported rather than slipped in): `augRdBody_spec` gained
`hnNO : nN != nO` — a real if minor weakening — and a strengthened postcondition
(the transitive CSR witness, the carrier cell, length preservation, the frames)
without which the round cannot re-establish `ArenaStW`; `augRdFratHalf_spec`
gained its scalar frame; `InCsrCopyAt`'s word bound went from `n + arcCount D < B`
to `+ 1 < B` because the copy computes `n+1`; and the five coefficients were
re-measured from `1034 463 596 310 265`. This is the right way for a same-day
figure to move — measured, restated, and named.

**Pinned for the assembly leaf.** `Srd` is one predicate for all `R` rounds while
the counts grow and lengths cannot, so every allocation is sized by the carrier
alone: `ardCap N = 2N^3 + N^2 + N + 1` (space only — `arcCount <= N^2`,
`frat, trans <= N^3`). `exists_ardSrd` establishes all of it **except**
`(io j)`/`(it j)`, since reallocating those would destroy the region the round
reads — so `ardCap A.N <= |sigma.arrs (it j)|` is a requirement on the base
pass's `Sbd`, which is a free parameter of `augBaseOrientIn_orCom` and therefore
satisfiable, but must be *chosen* that way. And `covAugAdjIn_of_base_rounds_sym`
stays unusable — its hypotheses are at `mdSel` while the augmentation lands
`CovAugAdjSelIn ... bucketSel`; use `covAugAdjSelIn_of_base_rounds_sym`.

**Supervisor slip, caught by checking**: my first attempt to add the import and
gate ran from a drifted cwd (a `cd` into `Lax3Proofs/` earlier in the session),
so the root-module edit silently did not happen and the gate could not find its
script. Absolute paths for every landing command, not just for `git -C`.

### 2026-08-25 — the augmentation round's body, and a review method that failed

`SolveAugRoundSeams.lean` (1344 lines). **`AugRoundIn` is not discharged**, but
its three computational stages now compose: `augRdBody_spec` proves
`augRdBody = augRdFratHalf ; trCom ; emCom` carries the round's windowed
orientation region to a `TrInCsr` of `greedyStep (selRank (bucketSel n)
(fratGraph D)) D`, with the arc count in `nO` and the fraternal mark region
restored to all-zero at exactly `n·n` cells. Real composition —
`Spec.of_exists`/`Run.seq`/`Spec.frame`/`Spec.run` over the three landed
dischargers.

**The budget is an equality, not an estimate.** `augRdBodyK n a f T = 961n +
443a + 576f + 270T + 217`, and `augRdBodyK_eq` proves it equals
`augRoundBudget 961 443 576 270 217 D`. Every figure is already in
`levelCharge`'s currency (`n`, `arcCount`, `fratPairCount`, `transPairCount`);
the one conversion — the peel's `176·nf` at `nf ≤ fratPairCount D` — is routed
from `fratCom_spec`'s own existential rather than estimated. Cross-checks
against the inherited full-round figures with the difference accounted for
exactly by the three carrier sweeps and the two missing passes.

**A supervisor review method failed, and this is the correction.** I reported
the interrupted predecessor's checkpoint as "zero `sorry`" on the strength of
`grep -c sorry`. It was not: an elaboration error at its line 269 had leaked
**`sorryAx`** into `augRdStTr_of_augStInN`, which that grep cannot see.
`grep` for the token is not a soundness check — **only a green build or
`#print axioms` is.** Every future landing report of mine states which of the
two it rests on.

**A worker finding overturned, in the right direction.** The predecessor
concluded that the exact-length `InNCsr` blocks the round and a new windowed
region was owed. `SolveAugOrient.lean:1921` already defines `augStInNW` —
`augStInN` read at the truncation `winA` — `augBaseOrientIn_orCom` already
*delivers* it, and `SolveChainWin.specWindow` is the generic exact-to-windowed
transport. The predecessor's file did not import `SolveAugOrient`, which is why
it missed this; its no-go theorem is true and kept, only the conclusion drawn
from it was wrong. **Second time a worker's snapshot has hidden a fact that was
already landed** — the first being the un-privatised `sq_lt_mcB`.

**`sel` must be `fun m => bucketSel m`.** Confirmed rather than newly decided:
`fratPeelAt_fratPeelCom` delivers `selRank (bucketSel n) …` and nothing else,
and `selRank` genuinely depends on the tie-break. `SolveAugBaseFrame` §2 already
pins `AugBasePeelIn` there and `covAugAdjSelIn_of_base_rounds_sym` is stated at
arbitrary `sel`, so the three residuals still compose — but this **rules out**
`covAugAdjIn_of_base_rounds_sym` (`SolveAugCompose.lean:568`), whose hypotheses
are at `mdSel`.

**The peel's `n·n + n` gets a separate `sk`, not a widened `mkF`** — the
fraternal mark region must be *exactly* `n·n` for its restoration clause to
re-establish its own precondition, so widening it breaks the round at round 2;
and `bucketPeelCom` writes the whole block without restoring it. Space, not
time.

Inhabitation done to the `exists_symPre` standard: 23 concrete region names and
4 figure cells discharging every name bundle by `decide`, allocations produced
from *any* state, and the precondition satisfiable in full.

**Four gaps, pinned.**
(a) **`augSymCsrIn_symCom` is stated at `augStInN`** while the base pass and the
rounds both speak `augStInNW`, and `augStInNW → augStInN` is false (the
allocation exceeds the extent). Since `covAugAdjSelIn_of_base_rounds_sym` uses
one `AugSt` for all three residuals, **the rounds and the symmetrization cannot
currently meet.** The repair is one line in a landed file: `SolveAugSymMerge`'s
own Finding 3 records that it consumes the region *only* through
`trInCsr_of_inNCsr`, which is `augStInNW`'s first clause.
(b) The transitive mark matrix is never re-zeroed — `TrClearAt` states the
missing pass at `20n + 20T + 10`; program unwritten.
(c) The emit's output lands in `(o', t')` — `InCsrCopyAt` states the copy-back
at `20n + 20a + 20`; program unwritten. (b) and (c) are exactly what separates
`augRdBody_spec` from `AugRoundIn`.
(d) **The round's word bound has no landed route.** `augRdBody_spec` needs
`n + n² + a + f + T < B`; the landed material gives the first two terms and
nothing about the three counts, and no theorem turns `n·d²` into `< mcB q x`.
The worker recorded this as landing on `Adm`, "threaded through every residual
of the augmentation with no landed instantiation at all" — **that half is now
out of date**: `chainAdm` landed hours earlier in `SolveF7Adm.lean`, invisible
to a worktree cut before it. Whether `chainAdm`'s `Inv` half yields `n·d² < mcB
q x`, or whether this is genuinely F7-c's choice of `q`, is the next question,
not an open-ended one.

### 2026-08-25 — a container restart killed two workers; both recovered from their branches

The session's container was replaced. Every running subagent died with it —
`ListAgents` came back empty, which is how it was noticed. The recovery worked
exactly as the 2026-08-18 cloud-adjustment designed it to: **the worktree
branches were the whole recovery state**, and nothing was lost.

- **w29 / the prep composition**: `SolveMachPrepComp.lean` at 945 lines, **zero
  `sorry`**, §1–§6 complete — name pool, two previously unstated inter-stage
  seams, the concrete `prepC`, the budget with the O(1) scalar loads folded in
  (`prepKP_le`), the name discipline, and **the level's concrete scratch
  descriptor** `prepScr` with `prepScr_down`/`_htabLen`/`_alloc`/`_rank`/
  `_batchWidth`/`_out`. That descriptor is the first concrete `Scr` in this
  campaign carrying *content* rather than being a parameter constrained only
  through implications: `prepScr_rank` is the clean-window clause and
  `prepScr_batchWidth` the exact-`S.width` bit region. What remains is the final
  `Spec.seq` chain to `ChildLoadPartsScrAll`.
- **w31 / `AugRoundIn`**: `SolveAugRoundSeams.lean` at 558 lines, zero `sorry`.

Both checkpointed to their branches (`556aab5`, `ca426c9`) and re-dispatched as
continuations pointed at their predecessors' files, not restarts. Toolchain,
warm store and both seeded worktrees survived on disk; main rebuilt green at
3561 jobs.

**Two operational facts worth keeping.** (i) The checkpoint-push discipline is
what made this a ten-minute recovery instead of a lost afternoon — but note the
uncommitted deltas were recovered only because the *filesystem* survived; had
the container been replaced rather than the session, only the pushed branches
would remain. Push worker branches, not just checkpoint them locally.
(ii) **This machine has 4 cores.** Four workers each replaying `lake build`
alongside a gate put 14 `lean` processes on 4 CPUs and stretched one gate to
~50 minutes. Wave width is bounded by CPU, not only by review bandwidth; two
concurrent workers is the right load here.

### 2026-08-25 — the cover sweep closes, and a live quadratic is retired

W37, `SolveSweepClose.lean` (944 lines). `sweepClose_covPeelIn` concludes
`CovPeelIn` **verbatim** at `peelK (12·R + 239) 154 76` on a concrete program,
chaining `peelBfsIn_bfsTurnCom` → `peelSweepIn_of_bfs` →
`covPeelIn_of_sweep_group` with `peelGroupIn_grCom`:
`(12R+44, 39, 76) → (12R+86, 93, 76) → +(153, 61, 0)`. `hR : 1 ≤ R` is not a
hypothesis — it is `Setup.one_le_R`. **And nothing stood between `CovPeelIn` and
`CovSweepIn`**: the missing half is `CovAdjBuildIn`, which `covAdjBuildIn_bldCom`
already supplies, so `sweepClose_covSweepIn` concludes `CovSweepIn` verbatim at
`peelK (12·R + 362) 154 192`.

**The latent quadratic, found and retired.** The build pass's
`bldK A.N ns = 93·N + 58·ns + 30` charges `ns`, the arena's **degree sum** —
`Θ(A.N²)` on a dense arena, and the one figure in the cover sweep outside
`peelK`'s currency. Nothing landed had folded it in. `sweepClose_bldK_le_peelK`
retires it: `sum_induced_deg_le_two_sum_dlt` at `s = univ, H = G` gives
`Σ_v deg v ≤ 2·Σ_v d_<(v)`, and `self_mem_cluster` gives `Σ_v d_<(v) ≤
peelEdgeWork`, so `bldK ≤ peelK 123 0 116`. **This is the third time a term in a
different currency has hidden a quadratic** (after w23's `86N²` and the
`AdjSortIn` entry sort), and the second time it survived a supervisor cost
review. Rule: a budget term whose argument is not `A.N`, a cluster mass, or a
`peelK`-shaped figure is unconverted until a lemma says otherwise.

Budget columns: `sweepClose_covPeelIn_budget_le` gives `12·R + 469` against
`chargeTotal (coverCFSel …)` via `peelK_le_coverCFSel_total`; the whole sweep is
`12·R + 708`. Per node only — the node→root step was explicitly out of scope.

**Finding — `covPeelIn_of_sweep_group` is not composable with its own two
dischargers.** Its docstring says the sweep's postcondition *is* the grouping's
precondition, "the same six conjuncts in the same order". True of the five named
conjuncts; the sixth is the `Sgr` parameter, and `peelSweepIn_of_bfs` (which
fixes it to its own pre-descriptor) and `peelGroupIn_grCom` (which fixes it to
four allocation clauses about `cm/sb/cnt/cur`) instantiate it incompatibly. Not
false — unusable. Fixed additively: the four clauses are length-only, and an
IMP+ run never moves an array's length, so any length-stable invariant rides
through a `PeelSweepIn` for free (`sweepClose_peelSweepIn_conj`), plus the
contravariant precondition monotonicity `PeelGroupIn` has because `Sgr` occurs
only in its precondition.

Also recorded: an interface asymmetry — `peelSweepIn_of_bfs`'s `hSsc` includes a
full array-length-preservation clause while `covAdjBuildIn_bldCom`'s `hSpl` does
not, so a length-only descriptor rides the sweep free but needs seven extra name
disequalities to ride the build. Cheap to fix if anyone touches those statements.

**The integration audit that came with it is the most useful part.** Walking the
path from `CovSweepIn` to `CoverAllIn`, exactly two predicates were concluded by
no theorem in the tree: `AugRoundIn` and `AugSymCsrIn` — and W37's worktree
predates W26's landing by one commit, so `AugSymCsrIn` is in fact discharged.
**`AugRoundIn` is the only one left.** Dispatched as w31 immediately.

### 2026-08-25 — F7-a: `Adm` and `KB` pinned, and `frameK` cannot be the pin

W36, `SolveF7Adm.lean` (736 lines).

`chainAdm S G₀ j A := prepAdm S j A ∧ (j ≤ S.depth → Inv S G₀ j A)`. The
`j ≤ S.depth` guard is load-bearing: `centreStep_of_prep_read`'s `hAdmChild`
asks for the child step at **every** `j` with no side condition, while
`inv_child` needs `1 + j·(2R+1) ≤ S.width`, which `mkSetup_width_le` supplies
only below the leaf level; under the guard the step goes through at every `j`
(below the leaf the width is available, above it the conclusion is vacuous).
`prepAdm` stays unguarded because `RoundPin` is, and it costs nothing —
`Inv`'s first two clauses *are* `prepAdm`. Root, child (at the child the frame
step actually forms), and the fuel-`0` edgeless guard are all concrete theorems.
Anti-vacuity is proved at a stronger statement than asked: `chainAdm_of_memTree`
shows **every arena the driver's run tree visits** is admissible, and
`chainAdm_prepPins` exhibits the whole `PrepPins` bundle at it, so conjoining
`Inv` loses the prep segment nothing.

`chainKB` is structural recursion on the fuel index — Lean accepts it with no
`termination_by`, the recursive occurrence under the `nxK` lambda being the same
shape as the landed `driverChargeMS`. Both landed `hKB` obligations close by
`le_rfl` and are then run end to end through `botBlock_spec` and
`blockSpec_leaf_guard`, so the fit is typechecked rather than shape-matched.

**Finding 1 — `frameK` cannot be `KB (k+1) j ·`, under any instantiation.**
`blockSpec_leaf_guard`'s `hKB` demands
`4 + max (botComK A.N …) (KElse A) ≤ KB (k+1) j A` at **every** `A`, edgeless
ones included, because `Spec.ite` pays the max before the test runs; `frameK`
returns exactly `botComK A.N …` on `A.G = ⊥`, short by at least 4, for any
`Kcov`, `Kglue`, `nxK`, `KElse`. Verified independently at review against both
objects. Hence `frameElseK` (the else branch, unconditional), with
`frameK_eq_frameElseK_of_ne_bot` and `frameK_le_chainKB`. `SolveChain` §7's own
docstring anticipated that a mismatch here would be "a finding about *this
section*, not about the chain" — which is exactly what it is.

**Finding 2 — the `⊥` branch again, and this one costs the bridge a lemma.**
Even the corrected pin fails `frameStepAll_of_cover_prep_read`'s `hKB`, whose
`centreKC` slot holds `KB k (j+1) (childArena …)` **structurally** at every `A`.
`KP`/`KR`/`Kcov` are free on `⊥` arenas (their contracts all carry `¬ A.G = ⊥`)
so a discharger could zero those, but not the recursive slot. So the landed glue
forces `KB` to pay a whole frame's recursion at edgeless nodes, while
`frameChargeMS` pays only `botC` there and **stops recursing** — `chainKB`
traverses strictly more nodes than `driverChargeMS`. Chargeable, not fatal: §10
supplies `childN_eq_one_of_bot` (below an edgeless node every cluster is `{u}`)
and `childArena_G_eq_bot_of_bot` (that child is again edgeless), so the excess
is `N` chains of `≤ S.depth` one-vertex edgeless arenas against a `botC` charge
of `(1+|ℱ_j|)·N` at that node. The bridge needs `chainKB` at an edgeless arena
`≤ K·(A.N+1)`, hence `Kcov` and `Kglue` in `O(A.N+1)` at every node. **`Adm`
cannot help here** — the mismatch is between two recursions, not a missing
hypothesis.

**The term-by-term `KsChargeBridge` verdict**: every `chainKB` term has a ledger
column. `restrictK` exact at `hbf = fun _ => 2R+1`; `bfsK` *and* `supportsK` both
into the single supports column; `profilesK` an exact two-term match; `isolateK`
matched modulo one seam the bridge must check; `centreScatterK` at identical
index sets but needing slack, because at `σ.t = 0` `greedyScatterCost` is `0`
while `scatterK N ns r 0 = 41N + 24`; `Kcov` per node via
`peelK_le_coverCFSel_total`; `botComK` with additive per-node slack. Two things
remain beyond bookkeeping: the `⊥`-node excess and that scatter slack.

Cost envelope clean: worst term `A.N · c(j)` with `c(j)` free of `n`; the
structural terms are exactly `Σ_u (|X_u| + degSum + ns_u)`, §7's own shape. The
only `N²` in the chain is `n₀·n₀ < B`, a machine word-width requirement, not a
time charge.

### 2026-08-25 — `hscrLen` is gone from all five remaining sites, and the landed closure is retired

W34, seven files, no landed statement edited in place — verified, not taken on
report: the diff across the six landed files has 30 deleted lines and every one
is a docstring line. All new material sits beside the old under `…Scr`/`…_scr`
names, so `solveSpec_of_chain` and `KsChargeBridge` are untouched for W36.

New vocabulary in `SolveChain` §3b: per-level descriptor read pools `LV`/`LR`;
`ScrAgree`, `ScrFree` (syntactic — "this command writes no name the level-`j`
descriptor reads"), `ScrFrame` (`rankScr_frame`'s shape, lifted), `ScrStep`, and
`specScr`, the `specArrsLength` analogue that transports a descriptor with
*content*. Sites 1, 2 and 4 close on `ScrFrame` plus a `ScrFree` side condition;
sites 3 and 5 need `ScrStep` and `BlockPostScr`.

**My own correction to the packet was itself wrong, and this is the finding.**
I told W34 that site 3 (the inner block) was free via `Run.frame` plus
write-ownership from `j+1`. It is not: the inner block writes level `(j+1)`'s
rank scratch — its own prep does — so nothing frames the deeper half of `Scr j`.
The only route is to take that half from the block's *own restored* `Scr (j+1)`,
which exists only once `BlockPost` gains the conjunct. **Sites 3 and 5 are one
problem**, `BlockPostScr` is load-bearing twice, and that is why `ScrStep` exists
as a second premise rather than everything running through `ScrFrame`. Two
supervisor errors in a row on the same seam — the first was calling the clause a
trade-off, the second was pricing the inner block free. Both were errors of
*assuming a frame*, and both were caught only by someone writing the proof.

**The landed closure is retired.** `solveSpec_closed` / `solveSpec_of_chain` are
not vacuous — a purely length-based `Scr` satisfies `hscrLen0` — but
`rankScrTower_refutes_len` shows **no** descriptor implying `RankScr` at the
level's own window can, and the prep segment needs exactly that clause. So
`solveSpec_closed_scr` is the closure this campaign uses from here; the landed
one stands, unused, at an instantiation that cannot arise.

**The open question from the sixth-site entry is answered: `canonBotB` does
restore level-`depth`'s rank scratch — trivially, by never touching it.**
`warrs_botCom ⊆ [na, fa, ea, xa, tab]` and `wvars_botCom ⊆ btScalars`, so
`botBlock_specScr` costs two `decide`-able disjointness hypotheses and no stage
was strengthened. The root load is cheap too: at its exit
`σ.vars (arenaNames i).nN = 0` for `i > 0`, so the tower's deeper clauses are
`take 0 = []`.

Satisfiability is a checked object, in the new `SolveScrFrameSat.lean`:
`RankScrTower`, inhabited at every window size, proved to satisfy `ScrFrame`,
`ScrStep`, the prep segment's `hscrDown` and `restrictCom_specW`'s content
precondition — **and to fail `hscrLen`**, which is the point. It also survives
conjunction with any allocation-clause family, which is where `hscr`/`htabLen`
live. `hfreshV` turns out free from the landed `hfreshS`, the carrier cell being
already in `levelScalars`.

Five docstrings were wrong and are fixed (`SolveChain`'s header,
`TopScatterSpec`'s, `solveSpec_of_chain`'s, `SolveGlueStep`'s header,
`TopScatterAll`'s) — the eleventh through fifteenth drifts recorded, all caught
before landing. W34 also read a sibling's in-flight file unprompted and found a
stale paragraph contradicting a docstring ninety lines below it; relayed to its
author rather than patched at landing.

Left open deliberately, and named: `centreStepAll_of_prep_rowsScr` takes
`CentrePrepAll`, not `ChildLoadAll`, because the only in-file bridge still takes
`hscrLen` and its replacement is downstream in the import order. The join
`ChildLoadPartsScrAll → CentrePrepAll → CentreStepAllScr → FrameStepAllScr →
solveSpec_closed_scr` belongs in a file importing `SolveMachPrepSeam` — relayed
to W35, whose file is exactly that.

### 2026-08-25 — `AugSymCsrIn` discharged, and the precondition proved satisfiable in full

`augSymCsrIn_symCom` (`SolveAugSymMerge.lean`, 1932 lines) meets `AugSymCsrIn`
verbatim at `(tn, ta, tc) = (90, 80, 60)`, spending `87·N + 76·a + 51`. Five
sweeps, of which **the middle three are the landed `tpCom`** — the transpose is
reused, not rewritten, the same call the fraternal peel made. Through
`augSymIn_of_symCsr_build` this is `augSymBudget` at `(171, 196, 84)`, and
`sn ≤ 3k`, `sa ≤ 5k` hold for every `k ≥ 57` against the base passes' `k = 475`.
No `N²`. **This closes F6c12-5a-ii: all four of the frame's small passes are
discharged.**

The exact-length requirement is met exactly as the supervisor decision said it
could be, **with no landed residual restated**: `symCsrSizes_exact` turns the
descriptor into the two exact figures, and `symCsr_ns_le` closes the
`ns ≤ 2·arcCount D` clause on the nose. Two facts had to be proved for want of a
landed form: `InNCsr → TrInCsr` (the transpose's contract is windowed while
`augStInN` is exact-length; the only non-mechanical clause is `inj`, which is the
rows' `Nodup` read as injectivity), and `N + arcCount D ≤ N·N`, which is what
makes the word obligation follow from `sq_lt_mcB` alone.

**Sent back once, for the check this campaign keeps failing.** The first version
had no anti-vacuity witness: `Srd`, `Smp`, `Ssw` were parameters constrained only
through implications, so `Srd := fun _ _ => False` satisfied every hypothesis
while making the discharge true and empty — and `Srd j σ` is also a conjunct of
`AugSymCsrIn`'s own precondition. The correction is **stronger than what was
asked**. `exists_symPre`: from *any* state satisfying `ArenaStW` and `augStInN`,
there is one satisfying those **and** `symSrd`, obtained by allocating only the
nine regions the descriptor names — `soO`/`stO` at exactly the `N+1` and `2a`
demanded — with every scalar, both tapes and every other array unchanged, and
the reallocation's frame returned so the residual's remaining clauses survive
too. So the precondition is satisfiable **in full**, and the descriptor imposes
no constraint linking the two figures beyond cells `σ` already carries. That is
the checked form of the ledger's reason for not restating the residual at a
windowed `SrcCsr` — previously an argument in a report, now an object.

Named and *not* discharged: `exists_symPre` is conditional on the machine holding
an in-neighbour CSR of the **final** orientation with its arc count in `nA j` —
`AugRoundIn`'s postcondition at `i = R`, a sibling's residual. What §11
establishes is that the merge's own demand adds nothing to it.

**Second name collision in two landings.** `two_mul_arcCount_le_sq` already
existed in `SolveAugOrient` — and the two are *different statements*: the landed
one is about `baseOr G π`, this one about an arbitrary `Orientation N`, i.e.
strictly more general. Renamed to `two_mul_arcCount_le_sq_orient` at landing.
Cleanup candidate, not urgent: `SolveAugOrient`'s specific form is an instance of
the general one and could be derived from it. Both collisions were invisible to
their workers for the same reason, so the packet rule is now in force —
**build the root module, not just your own** — and the supervisor scans new
declaration names against the package before rebuilding.

### 2026-08-25 — w30 dispatched: `CovPeelIn` is composable for the first time

Both halves of the peel are now in one tree, and the chain
`peelBfsIn_bfsTurnCom` → `peelSweepIn_of_bfs` → `covPeelIn_of_sweep_group`
(with `peelGroupIn_grCom` on the grouping side) has no missing link. Dispatched
as a composition leaf in a fresh worktree off `94f706e`, with two deliverables:
`CovPeelIn` discharged at an explicit numeric budget, and an honest account of
how far that reaches toward `CovSweepIn` — a precisely pinned gap being a
first-class result rather than a failure.

The packet carries the summed-budget check against `peelK_le_coverCFSel_total`
explicitly, because this is the exact place the `86·N²` peel broke the headline
once already, and it carries the new naming rule from today's landing failure:
**build the root module, not just your own, or a name collision surfaces to the
supervisor instead of to you.**

### 2026-08-25 — `PeelBfsIn` discharged: the cluster sweep is a machine program end to end

`peelBfsIn_bfsTurnCom` (`SolveSweepBfsRun.lean`, 2183 lines) meets `PeelBfsIn`
**verbatim** at `(abf, bbf, cbf) = (12·R + 44, 39, 76)`. All three constants
came out as the design predicted — no correction. Composed with
`peelSweepIn_of_bfs` (w28), one centre's BFS carries the whole peel sweep.

The induction is the content. `bfsIters_run` runs `k` passes at a *shifted*
ball family (`BlS 0 = ∅`, `BlS (m+1) = ball H m u`), carrying both the row's
set and the expanded prefix's; `ball_succ_frontier` is the step — expanding
only the frontier advances exactly one radius, because the layer below had its
neighbours pushed already. The consequences are what the caller needs: the
marking phase leaves the row at `ball H R u` and *no more*, the plain phase at
`ball H (2R) u` = the cluster, and the expanded set is `BlS (2R) = ball H (2R-1) u`,
so **the final level is provably not expanded**. The level loop is
`Run.while_potential` at `Φ σ = Σ_{v ∈ L₀.drop bf.h} (25 + 38·deg v)` — the
frontier's own bill, dropping exactly one head term per turn.

`Ssc` is instantiated at the **concrete** `BfsClean (co j) n`, with no
allocation clause added: the clean-up runs at `min n |co|`, which is `≤ |co|`
for free and still covers `[0,n)` because an out-of-range `getD` is `0`. That
is the exact-length trap declined rather than paid — worth contrasting with the
five occurrences where it had to be paid.

**Two landed gaps, neither a falsity.** (i) `bfsClear_spec` **states no frame at
all** — nothing about arrays other than `co`, not even that `co`'s length
survives, while `SweepSt` demands `A.N + 1 ≤ |co|` back. Recovered by a new
general lemma, **`Run.arrs_length`**: a run never changes any array's length,
because the only array update in IMP+ is a store. That is the same fact the
exact-length trap keeps turning on, finally stated once as a lemma — export it.
(ii) `logPart_succ`'s `holdrow` and the clean-up's carrier range both need
pointwise frame facts no landed lemma supplies; carried as two reference clauses
inside the file's own `BfsRow`.

**Supervisor fix at review.** The file defined `Lax3Proofs.Prog.ScanInv`, which
collides with the landed `SolveSweepBucketRound`'s declaration of the same name
— genuinely different objects. Invisible to the worker, which built only its own
module; the root-module build is what catches it. Renamed to `BfsScanInv` at
landing (5 occurrences, mechanical). **Rule for future packets: a worker whose
gate is `lake build <its own module>` has not checked for a name collision.
Either require the root-module build or require a file-unique prefix.**

### 2026-08-25 — the sixth `hscrLen` site, and why it is the expensive one

Supervisor reading during wave 29, relayed to W34 mid-flight (new information
that genuinely changes the task — the one thing that justifies interrupting a
worker). The packet framed `hscrLen0` as a missing frame clause on the return
path. It is not. The real shape:

- `BlockPre S j … (Scr j) …` carries the scratch descriptor.
- `BlockPost S ord k j … = ArenaStW … ∧ TableBitsW …` (`SolveChain.lean:200`)
  carries **no `Scr` conjunct at all**.

So nothing about `Scr 0` survives `chainCom` on its own, and
`solveSpec_of_chain` bridges the gap by the only route open to it:
`specArrsLength` preserves every array *length*, and `hscrLen0` converts
length-preservation back into `Scr 0`. **That is precisely the mechanism
`rankScr_not_length_only` refutes.** `hscrLen0` is therefore not a convenience
to be dropped; it is load-bearing, and removing it forces `BlockPost` to gain
the conjunct — the same additive move `ChildLoadScr` made one layer down.

Two consequences priced into W34's leaf: the obligation propagates to **both**
producers of a `BlockSpec` — `FrameStep` (still undischarged, so there it is a
cheap statement change, and W35 is composing its prep segment against
`ChildLoadPartsScrAll`, which already delivers `Scr j σ'`) and **`botBlock_spec`**
(`SolveChain.lean:386`), which **is** discharged, so whether `canonBotB`
actually restores level-`depth`'s rank scratch is now an open question with a
name. And `TopScatterSpec` is a sixth *consumer*: its definition is clean (the
`Scr` is a parameter, length-only is not baked in), but its docstring and
`solveSpec_of_chain`'s both assert the top stage's descriptor arrives "for free
because it is length-only" — false the moment `hscrLen0` goes. Docstring drift
number eleven, caught before it landed.

### 2026-08-25 — wave 29 dispatched: the seam's five siblings, the prep composition, and F7 opens

Worktree `w29` off `45bec3b`, three leaves, file ownership disjoint and stated
in every packet (two siblings are still running in `w28` on `SolveAugSymMerge`
and `SolveSweepBfsRun`, so *five* workers now share no file).

- **W34 — the five `hscrLen` sites.** Owns the six landed files that still
  demand the length-only clause. Ownership is exclusive because these are
  *landed* files; the packet's hard constraint is that **every landed name keeps
  its current meaning** (restate beside, do not rewrite), because W36 is
  building on `solveSpec_of_chain` and `KsChargeBridge` as they stand.
- **W35 — `ChildLoadPartsAll`.** New files only (`SolveMachPrepComp*`). Targets
  the *strengthened* `ChildLoadPartsScrAll`, which weakens back, so one discharge
  serves both routes. Packet carries the exact-length trap and the IMP+ limits
  (no length primitive, no disequality) up front, because item (d) of its gap
  list — `bi` at length **exactly** `S.width` — is that trap for the sixth time.
- **W36 — F7-a.** New file only (`SolveF7Adm*`). Pins `Adm` and `KB`. Separable
  from residual 1 because it needs only the *statements* of `FrameStep` and
  `KsChargeBridge`. Packet asks it to check `KB`-vs-`KsChargeBridge` term by
  term and to report a term with no column rather than adjust `frameK`, and
  hands it the `⊥`-branch fact from today's F5b entry so it does not rediscover
  that the node→root step is not monotonicity.

### 2026-08-25 — F5b's dropped degree clause, and a second hole the audit missed

`ProgCoverChargeDeg.lean` (743 lines) repairs the export F5b proved and threw
away. `exists_coverChargeSel_le` **already picks the degree constant as its
witness** — its body is `obtain ⟨c, hc0, hdeg⟩ := exists_wreach_degree_…` and
then `refine ⟨c, f₁ + 2*(c+1)*(c+1), …⟩` — so the theorem is true with the
degree clause attached and simply does not say so. That is `exists_fratCsr`'s
failure mode a second time: **an ∃-export that hides a fact it has in hand is
worth less than it looks.**

Shape chosen: export the clause **at the same `cf`**, not at a fresh
existential and not at `max cdeg cs`. `sweepCharge_mono_deg` is the reason,
proved rather than asserted: `D` occurs only positively in `∑_v (|X_v|·D + …)`,
so a charge bound never transfers *up* to a larger `D` while the degree clause
does — the asymmetry that makes the two-constant route pay twice. The engines
are nevertheless stated constants-in/bound-out (`coverChargeSel_le_of_degree`,
`mcChargeMS_chargeTotal_le_sel_of`) so the witness's identity stays visible at
every level. `ProgCoverChargeSel.lean` was not edited.

**Second hole, absent from my readiness audit.** `0 ≤ cf` genuinely admits
`cf = 0` — `exists_wreach_degree_selOrderingRoutine` returns `max c 0` and
`⌈0·m^δ⌉₊ = 0` — so `peelBudget_le_sweepCharge`'s *second* hypothesis `1 ≤ D`
was unavailable too, independently of the degree clause. `1 ≤ cf` is now
exported (constant raised to `max cdeg 1`, charge re-derived there, sound
because §1 is parametric). At `A.N = 0` the hypothesis really is false and every
peel figure is an empty sum, handled separately.

Deliverable: **`exists_mcChargeMS_T_bucket_coverColumn`** — one `cf ≥ 1`, one
`T`, at `selOrderingRoutine bucketSel (3·S.R)`, the routine
`covOrderIn_bucketPeel` proves the machine's ordering pass against — carrying
the time clause, the ledger bound, and the cover-sweep column together.
Anti-vacuity is load-bearing rather than decorative: `peelK_le_coverCFSel_total`
absorbs its `a·A.N` term through `le_chargeTotal_coverCFSel`, i.e. through
`le_selChainCharge`, so no placeholder charge can meet it, and
`coverCFSel_order_eq_timedSelRoutine_steps` pins the `"cover.order"` entry to the
priced routine's own `steps`, ruling out the `steps := 0` reading of
`CoverOrderingTime`.

**What the column still waits on.** It closes **per node** — the shape every
sibling column of `KsChargeBridge` uses (`restrictK_le_childCharge`,
`isolateK_le_isolateCharge`, `profilesK_le`, `scatterK_le`, `botComK_le`). The
node→root step is **not** a monotonicity step: `driverChargeMS` places `covC j A`
inside `frameChargeMS` only on the branch `A.G ≠ ⊥` (`ProgCharge.lean:199-212`),
so a `⊥` node pays `botC` and carries no cover vector at all.
`chargeTotal (covC j A) ≤ chargeTotal (mcChargeMS …)` is therefore false as a
blanket statement and must follow the recursion's own admissibility — F7's job,
noted in the module docstring so it is not rediscovered.

### 2026-08-25 — the CLInv scratch seam: the escape hatch was not a trade-off, it was inconsistent

Residual 1's blocker (logged two entries below as "a content clause with nowhere
to live") is resolved, and entirely **additively** — `SolveMachPrepSeam.lean`
(737 lines) edits no landed statement. The clause the child-building pass owes
goes into the *pass's own postcondition* as `Scr j σ'`: `ChildLoadScr` is
verbatim `ChildLoad` plus that conjunct, `ChildLoadPartsScr` likewise, and both
weaken back (`childLoad_of_childLoadScr`, `childLoadParts_of_partsScr`), so
nothing that consumes the landed residuals is deprived.
`centrePrep_of_childLoadScr` then concludes **verbatim `CentrePrep`** with
`hscrLen` gone — only `hscrDown` and `htabLen` remain — and
`centrePrepAll_of_partsScr_chanTab` reproduces the whole prep segment at the
canonical channel witness (`chanTab_hhtab` still `rfl`).

**The finding that settles the design question.** My note in `SolveMachPrepAll`
§6 said carrying the clean-scratch clause inside `Scr` "forfeits the
`CentrePrepAll` corollary". `rankScr_not_length_only` proves something
stronger: a `Scr` that implies `RankScr` **and** satisfies `hscrLen`'s
length-only `∀ σ σ'` shape is **inconsistent** at any state with a non-empty
window — flip one scratch cell, every array length is unchanged, so `hscrLen`
would carry the clause to a state that plainly fails it. So the two were never
a trade-off to balance: `hscrLen` had to leave the prep segment. Recorded as a
theorem rather than a supervisor opinion.

`clInv_frame_scr` is the mechanism: the landed `clInv_frame` re-derives `Scr j`
from lengths alone; this variant takes `Scr j σ'` as a premise and then needs
**no** length clause at all, because `BlockPre`'s table bound rides the frame on
`(arenaNames j).tab`, already in the level's array pool. That is what lets a
pass which *writes and restores* an array outside `levelArrays j` still carry
the loop invariant.

**Follow-up leaf, minted here.** `hscrLen` is demanded at five more sites, all
on files this leaf did not own: `clInv_setVar_ctr`/`centreLoop_of_step`
(`SolveGlueLoop`), `frameElse_of_cover_loop` (`SolveGlueStep`),
`centreStep_of_prep_read` (`SolveStep`), `centreRead_of_rows` (`SolveSegRead`),
and `hscrLen0` in `solveSpec_of_chain` (`SolveChain`) / `solveSpec_closed`
(`SolveFrameBridge`). By the finding above a `RankScr`-carrying `Scr` kills all
five, and `rankScr_frame` is the shape that fixes them — free at the counter
bump and the inner block (`Run.frame`, ownership from `j+1`), but at the **cover
stage and the return path it must be stated**, because `CoverAll` and
`ReadRows` frame only `ca/co/cm :: levelArrays j`. §6 of the new module names
all five so nobody rediscovers them.

`ChildLoadPartsAll` itself is **not** discharged and is not a residual but a
multi-leaf job: `prepC j` undefined (~25 names, ~60 disequalities), four
unstated inter-stage seams (restrict's child `ArenaStW` → `HistArrW`;
`profilesCom_specW`'s tables → `colWriteCom_machChild`'s indexed `pdF`/`puF`
families; the `ℓp j → ℓp (j+1)` hand-over under `ColPin`; every allocation the
stages ask of `Scr`, including `bi` at length **exactly** `S.width`), and the
nine-`Spec.seq` budget summation into `prepPassK`.

### 2026-08-25 — the fraternal peel: the landed peel composed, and a pricing identity

`AugRoundIn`'s hidden obligation is discharged. `fratPeelAt_fratPeelCom` leaves
`RankAt sg (selRank (bucketSel n) (fratGraph D))` — **`StepEmitIn`'s exact
predicate** — from the fraternal `CsrPrefix`, at
`fratPeelCom = bldAdjCom ; bucketPeelCom`. **The landed peel composed; no
second peel was written** — which is what the packet required the worker to
stop and ask about rather than duplicate a 3,000-line program.

**The budget closes at *equality*, not an estimate.** `fratPeelK n nf =
394n + 176nf + 64`, and `Run.mono` shuts it exactly:
`(81n + 58nf + 24) + (313n + 118·slotCount + 40)` with
`nf = slotCount (fratGraph D)` by `graphCsr_ns_eq_slotCount`. That identity
*is* the pricing argument — the fraternal CSR's slot count **is** the figure
the peel is charged at, so there is nothing to estimate. Lands in
`augRoundBudget`'s `kn` and `kf`; `ka` and `kt` unused. Linear in the carrier,
so the `R+1` repetitions do not multiply.

**Correction to a supervisor brief.** It said `AdjBuildAt` is "directly usable
on fresh arrays". The `winA` trap indeed does not apply — but `AdjBuildAt` is
still **not** usable here, for a *second* reason: its precondition is
`GraphCsr`, which pins `|o| = N+1` and `|t| = ns` **exactly**, while
`fratCsrAt_fratCom` allocates at `fratPairCount D ≥ nf` and delivers only the
`≤`-sized `CsrPrefix`. The route is one level down — `bldAdj_spec` via
`srcCsr_of_graphCsr`. **Fifth occurrence** of an exact-length clause invisible
in the contract text.

**For the composer**: the peel needs `n·n + n` cells in `sk`. The round already
carries an `n·n` region (`FratCsrAt`'s mark matrix `mk`, proved restored to
all-zero) — but `n·n ≠ n·n + n`, so `mk` must be widened by `n` or a separate
allocation named. Time stays linear; only the space is quadratic.

### 2026-08-25 — `PeelGroupIn` discharged in full, and a nine-times-recorded drift finally cleaned

`peelGroupIn_grCom` concludes `PeelGroupIn` **verbatim**, every clause intact,
at `peelK 153 61 0` — **no edge term**, since the grouping never reads the
graph. **No residual left open.** `bgr = 61` is tight (17 + 22 + 22: exactly
the three passes over the mass); `agr` carries a folded constant and is slack
by ~`49/N`.

Two design points worth keeping: `cur` needs **no zeroing pass**, because `od`
is a bijection over ranks so every carrier cell is written once; and the second
sort needs **no second offset array**, because the first scatter leaves
`cnt[v]` at the bucket's *end* while the running pointer is its start.

**Cross-leaf constraint for the composition**: `Sgr` is a binding requirement
on the **sweep** half and is invisible in `PeelGroupIn`'s text — it cannot
mention the arena, so no scratch length can be stated in `A.N` or the mass. It
is instantiated against the log's own arrays (`|lm| ≤ |cm|`, `|lm| ≤ |sb|`,
`|co| ≤ |cnt|`, `|co| ≤ |cur|`), arena-free and exactly strong enough.
`PeelSweepIn` must leave it true. Checked separately: **`ClusterCsr` pins no
exact length** — both allocation clauses are `≤` — so it imposes nothing
hidden downstream.

**And the drift is cleaned.** `SolveBlocksRestrict`'s Finding 1 still said
`Driver.setEquiv` was `Classical`-chosen and flagged the `orderIsoOfFin` repin
as *future work*. The repin landed at `DriverArena.lean:140`, and the paragraph
had gone stale — the tenth instance of docstring-versus-object drift in this
campaign, and the first one caused by our own landing rather than inherited.
Corrected in place with a `⟨RESOLVED⟩` tag, keeping the reasoning because it
still explains why `ClusterList` exists. **`restrictEmb` is the sorted
enumeration and that is now a theorem** (`setEquiv_strictMono`,
`ncard_lt_setEquiv`) — which is precisely what makes `SolveSweepGroup`'s second
counting sort stable *by construction* and `SolveMachPrepBatch`'s
"running count is the slot" invariant true. Two landed proofs depend on the
fact the docstring was still denying.

### 2026-08-25 — the peel BFS: a hazard turned structural

`PeelBfsIn`'s program, both of its constraints as **theorems**, the clean-up
with its accounting (`bfsClear_spec` at `14·cnt + 6`), the state step
(`sweepSt_step_of_bfs`), the frame and the scratch descriptor
(`bfsClean_hSsc`, meeting `peelSweepIn_of_bfs`'s `hSsc` verbatim) are landed.
**Not discharged**: the induction over levels identifying the reached list with
the ball, and with it the `Run` accounting. The constants `abf = 12R + 44`,
`bbf = 39`, `cbf = 76` are **read off the program text, not proved** — the file
says so; the one proved figure is the clean-up's.

**The design decision worth keeping.** `.lit (2 * S.R)` **cannot be evaluated
at `mcB q x`** — nothing in `mcD`/`mcB` bounds `S.R` by `|x|` — so a level
counter would have created an *undischargeable word-bound obligation*. The
levels are therefore **unrolled**: `iterCom R (level true) ; iterCom R (level
false)`, with `0` and `1` the only literals. Consequence: **constraint 1 ("do
not expand the final level"), on which the entire edge budget rests, stops
being a guard the program must respect and becomes structural** — there is no
pass left that *could* expand distance `2R`. A failure mode removed rather
than defended against.

Two further decisions: **`Lib.Queue` is unusable here** — its relation pins the
*whole* backing array while `lm` holds every earlier row below the current
base — so the reached list **is** the log row `lm[b .. b+cnt)`, which is also
what lets constraint 2's clean-up walk what it just emitted instead of scanning
the carrier; and visited marks live in **`co`**, the only free carrier-sized
array in `SweepSt`, legal exactly because `hSsc`'s frame list omits it.

`hR : 1 ≤ S.R` is confirmed **genuinely load-bearing, not defensive**: at
`R = 0` the `2R-1` and `2R` radii collide and `cluster_eq_expand_of_ball` is
**false**. That is GKS's silent side condition, now explicit in two places.

### 2026-08-25 — `PeelSweepIn` reduced to one centre's BFS

`peelSweepIn_of_bfs` discharges `PeelSweepIn` — every clause intact — from a
**single** named residual **`PeelBfsIn`**: *one centre's BFS*, not the sweep.
The rest is a real program (`sweepInitCom ; while i < nn { v := od[i] ; bfC ;
delAdjCom ; i++ }`), with the deletion half the landed `delAdjCom` at
`AdjDeleteInW` and the loop's region invariant walking `DelAdjSt … (peelSet π
i)` up a rank per turn through `peelSet_succ`. `peelBudget_le` applies verbatim,
so the sweep closes at `O(N·D²)`.

**`bsw = bbf + 54` is tight against the landed delete** — `54` *is*
`AdjDeleteInW`'s per-edge-copy charge, and it reaches the mass term only via
`curDeg_at_deletion_le_cluster`, which is exactly where `1 ≤ S.R` is spent
(explicit hypothesis, not hidden). `csw = cbf`: the edge term is the BFS's
alone — nothing outside `bfC` reads an adjacency cell.

`PeelBfsIn`'s pre/post are the **same `SweepSt` at consecutive mark indices**,
so its discharger gets one obligation per clause and no loop overhead. It was
handed three state-level lemmas built for it — **`centre_eq_iff_first_hit`**
(the *converse* of `centre_eq_of_hit_first`: a marking pass must know it marks
nothing **extra**), `ctrPart_succ`, `logPart_succ` — plus `arena_sq_lt_mcB`.

**Fourth occurrence of the invisible-allocation trap**, and the sharpest yet:
`ClusterLog`'s `offL N ≤ (σ.arrs lm).length` binds whoever establishes
`PeelSweepIn`'s precondition, and nothing in `CovPeelIn`'s text says so. Worse,
since `Spl : ℕ → Env → Prop` **cannot mention `A`**, it *cannot* be stated as
`clusterMass ≤ |lm|`; it has to go in as `n·n ≤ |lm|` with `peelOff_le_sq`.
Any other discharger of this residual must solve it the same way.

### 2026-08-25 — residual 1's real blocker: a content clause with nowhere to live

The prep composition is **one seam** from discharge, and the seam is not
algorithmic. `restrictCom_specW`'s precondition carries a **content** clause —
`(σ.arrs ra).take A.N = arrOf A.N (fun _ => 0)`, a clean rank scratch — on an
array **outside `levelArrays j`**. `CLInv` offers exactly one slot for such a
thing, `Scr j`, and both landed transports move `Scr` with **`hscrLen`, which
is length-only**. No content clause survives that.

**Both obvious escapes are ruled out.** Carrying the clause in `Scr` alone
forfeits the `CentrePrepAll` corollary — the point of the chain. Wiping the
scratch inside `prepC` costs `Θ(A.N)` per centre, i.e. `Θ(A.N²)` overall:
**exactly §6.1's trap, and the reason `restrictK` deliberately has no `A.N`
term.** Supervisor decision: take the third way — re-establish `Scr` from the
pass's *actual postcondition* (array-frame plus restored scratch) rather than
from lengths. The fact that makes it exist: the pass **does** restore the
scratch, cleaning only the `|S|` entries it touched, per §6.1's "one scratch
array per node, cleared only at the touched entries, never one per child".
Nothing landed says so, which is the whole defect.

**Four seams the same wave closed**, none of which had been landed: nothing
computed `(centreChild : ℕ)` at all (`bfsCom_specW` needs it in `bf.v` and
`mkBatchCom_batch` took it as a *hypothesis*); the `ArenaStW` palette move
(`arenaStW_recol`); `restrictCom_specW` states **neither** a frame clause nor a
no-reallocation clause though `ChildLoadParts` demands both (`Spec.frameA`
supplies both for every stage at once); and the supports patch **is**
`Driver.childChan` — now a theorem (`supportsPatch_eq_childChan`) rather than a
docstring claim.

**A forced ordering nobody had stated**: the colour writer must run **before**
`isolateCom`. `isolateCom_specW` returns `ArenaStW` at the palette of the arena
it was handed, while `profilesCom_specW` requires the *parent's* palette — so
the only consistent order is `profiles → colWrite → isolate`, with the recolour
turning the pre-isolation child into an `isoPal` arena that isolate then
isolates. `isolate_recol_eq_machChild` is that identity, by `rfl`.

### 2026-08-25 — the F7 readiness audit, and a supervisor claim retracted

**Retraction.** The commit landing `StepEmitIn` said *"only the symmetrization
merge remains before F7"*. **That was wrong.** A read-only audit of
`solveSpec_closed`'s residual chain, leaf by leaf against the Lean text, finds
**five** open residuals under it, not one:

| residual | file:line | note |
|---|---|---|
| `ChildLoadPartsAll` | `SolveMachPrep.lean:299` | all three blocking sub-programs now landed; **only the composition is unwritten** |
| `AugRoundIn` | `SolveAugCompose.lean:391` | **bigger than the ledger implied** — see below |
| `AugSymCsrIn` | `SolveAugCompose.lean:604` | in flight (w28) |
| `PeelSweepIn` | `SolveSweepPeel.lean:328` | **confirmed undischarged** |
| `PeelGroupIn` | `SolveSweepPeel.lean:380` | **confirmed undischarged** |

`covPeelIn_of_sweep_group` is the *only* route to `CovPeelIn`, the only route to
`CovSweepIn`, required by the only route to `CoverAllIn`. So the peel pair is on
the critical path and was never dispatched.

**`AugRoundIn` owes a fraternal-graph peel nobody had named.** `StepEmitIn`
takes the ranking as an *arbitrary* `rk` via `RankAt sg rk σ`, while
`AugRoundIn`'s postcondition is at `greedyStep (selRank (sel A.N) (fratGraph
(selChain … i))) …` — and **nothing landed computes the selection rank of
`fratGraph D`**. Every landed peel works off a `DelAdjSt`/arena CSR, not the
`CsrPrefix fo ft (fratGraph D) nf` the round holds. It also owes per-round
zeroing of `ad`/`sd`/`dg`, all three demanded all-zero by `StepEmitIn`'s
precondition.

**Three further items the F7 row never named:**

1. **The `T`-uniformity step.** `mc_computesInTime_of_solveSpec` returns
   `T x = L.const · mcK Ks x`, and **`Ks` depends on `n` and `G`** (through
   `KB depth 0 (rootArena G _)`, `topScatK n (∑ v, G.degree v) atoms`, and
   `Krl x`). The axiom binds `T` **before** `n, G, w` and quantifies over *all*
   words. So F7 must produce a uniform majorant and weaken along it.
   `ComputesInTime` is trivially monotone in `T`, but **no such lemma is
   landed**. The ledger's `T x := L.const·mcK` is therefore **wrong**, and
   `ProgCodegen.lean:145-149`'s own continuation note repeats the error.
2. **`hokS : Com.Ok` and `hnw : NoWrite` for the whole composed command.**
   The package contains exactly **two** `Com.Ok` proofs (`parseCom_ok`,
   `matCom_ok`) and none for any routine. `OwnedFrom` constrains only *writes*,
   so it does not supply `Com.Ok`, which needs every *read* name plus expression
   depth. **The single largest unnamed item in the row.**
3. **`temps` is an edit, not a pick.** `mcLayout` hard-codes `temps = 2`, while
   `t[i] := a[j] + b[k]` already needs `≥ 3` and `bcExpr` is deeper.
   Parameterising it moves the literal `11` in `mcLayout_span_le`, hence `hspan`
   in three landed theorems.

**Corrections to landed beliefs**: `Adm := Inv` does **not** work (`hAdmChild`
is unrestricted in `j` while `inv_child`'s `hwidth` needs `j < depth`); the
guarded `prepAdm S j A ∧ (j ≤ S.depth → Inv S G j A)` does, and is not landed.
`headline_encoded` is **not on F7's path** — nothing consumes it. `KB` is still
unpinned and `frameK`, its advertised target, is consumed by nothing and has
the wrong shape. `AdjBuildIn` is dead (consumed by nothing); `AdjDeleteIn` is
refuted. E0 is no longer an assumption.

**Verdict: F7 is one leaf behind six others, and is itself three** — F7-a
(`Adm` + the `KB` fuel recursion), F7-b (`KsChargeBridge` in a *uniform-`cB`*
form, which the landed shape does not deliver since it binds `∃ cB` after `G`),
F7-c (codegen: `temps`, `eS`/`eA`, `Com.Ok`, `NoWrite`, `q`/`c`, the
`T`-monotonicity step, the ∃-close).

The lesson for the supervisor: **a leaf count is not a readiness measure.**
I had been tracking rows, and the rows understated the DAG because five
residuals lived inside one mega-row (F6c12) rather than as rows of their own.
They are minted below.


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
