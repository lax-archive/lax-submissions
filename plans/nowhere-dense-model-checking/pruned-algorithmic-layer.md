# ND-MC: the pruned algorithmic layer

2026-08-17. **This note exists so that nobody has to read the history.** On
Jan's instruction the whole algorithmic layer of `nowhere-dense-model-checking`
was deleted from the working tree, so that the redesign in `algorithm-v2.md`
could be done from first principles without being anchored by it.

Everything deleted is in git, unchanged, at

    816e5cc3bf14074676c56e0487af6802db7c2d2b     (parent of the prune commit)
    git show 816e5cc:nowhere-dense-model-checking/proofs/Lax3Proofs/<file>.lean

but the working assumption is that **it will not be consulted**. If you find
yourself wanting to, check §3a first — a short list of files is recoverable
*as-is*, and two of them have already been restored. For everything else the
right move is to write the piece fresh against `algorithm-v2.md`: the layer was
shaped by an architecture that `algorithm-v2.md` §1 rejects, so its lemmas carry
carrier-length arrays in their preconditions even when their statements look
reusable.

---

## §1 What was removed, and what survived

**Removed: 103 files, 102,545 lines** — the whole word-RAM realization plus the
abstract evaluator and its cost bookkeeping.

**Kept: 27 files, ~14,100 lines** — the mathematical layer, untouched, plus the
two files §3a recovered; green at 3410 jobs:

| group | files |
|---|---|
| locality engine (arXiv:2606.23180) | `WalkDistance` `Horizon` `SyntaxLemmas` `SemLocal` `Clusters` `ScatterCore` `Separation` `FarQuant` `BCAlgebra` `ScatterFml` `Assembly` |
| FO → distance logic | `Reduction` |
| isolation splitter game | `SplitterBasics` `SplitterMono` `SplitterWin` `SplitterWinRec` `UqwInstantiation` |
| sparse covers, GKS §6 | `CoverConstruction` `Augmentation` `AugmentedDensity` `OrderedCovers` `CoverDegree` |
| the two rewrites, and the leaf | `Relativize` `Isolate` `BotEval` |
| machine-independent arithmetic (restored, §3a) | `CostRecurrence` `TgtCoupling` |

`Assembly` discharges `Lax3.Locality.locality` and `Lax3.NormalForm.normalForm`
— those two concept axioms remain proved. The concepts package was **not
touched** by the prune: the endorsed statement of the headline theorem is
exactly what it was.

Stale prose references to deleted modules were rewritten in place in
`UqwInstantiation`, `CoverDegree` (six sites) and `SplitterWinRec`; the
mathematical content of those files is unchanged.

### The removed files

Grouped by what they were. Line counts are the deleted sizes.

**The abstract layer (1,416 lines).** `Evaluator` (757) — the recursion
descending the game tree, with correctness against `Sat` and a math-core
checkpoint that the evaluator decides every FO sentence on a nowhere dense
class. `FormulaTables` (659) — the per-depth formula lists, closed under the
step, with the padding trick that makes the palette depth-indexed rather than
batch-indexed. (`CostRecurrence` (646) and `TgtCoupling` (447) were removed in
the same sweep and have since been **restored** — see §3a.)

**The word-RAM passes (~11,000).** `RamBfs` (1273), `RamBfsPaths` (1167),
`RamCover` (1476), `RamElim` (3947), `RamAugment` (1008), `RamScatter` (1013),
`CsrWide` (320), `C0Probe` (246).

**The driver and its walks (~30,600).** `RamDriver` (4339), and the files
discharging its obligations: `RamDriverAugment` (6355), `RamDriverDescend`
(4568), `RamDriverCompose` (3464), `RamDriverBot` (2346), `RamDriverCluster`
(2008), `RamDriverWrites` (1827), `RamDriverDedup` (1773), `RamDriverOrder`
(1325), `RamDriverRoot` (1250), `RamDriverIO` (1178), `RamDriverBase` (1057),
`RamDriverFrames` (880).

**`Refine/` (~58,000, 71 files).** The block-scale rebuild: `ScatterSynth`
(2805), `ScatterDeadPass` (2782), `BlockLeaves` (1871), `DriverRootD` (1573),
`AugmentSynth` (1612), `ClusterSynth` (1528), `C0CloseProbe` (1527),
`OrderSynth` (1487), `ElimCompact` (1361), `ElimCompactCsr` (1289),
`BfsBlockMask` (1286), `ScatterDeadTurn` (1279), `AugCompact` (1256),
`ExpandSynth` (1237), `ElimSynth` (1199), `CoverSynth` (1175),
`ScatterBlockMask` (1133), `GapsDesign` (1118), `BfsBlock` (1107),
`ElimSynth5` (1105), `ElimSynth7` (1066), `ElimSynth2` (1054), `MassWeight`
(1023), `G2CostProbe` (900), `B4Design` (928), `KillPass` (860),
`SymCompact` (800), `MemThreadProbe` (783), `SlotSweep` (781),
`ScatterBlockProg` (722), `OrderSigProbe` (714), `DeadRowProbe` (680),
`CoverBlock` (666), `BridgeSeamProbe` (666), `ElimCompactWalks` (640),
`ScatterBlock` (641), `ScatterDeadFold` (611), `KillListWalk` (572),
`G2ExistsRevalidation` (560), `AugmentSynth2` (821), `ArenaWidth` (532),
`MassAlive` (528), `CompactPreps` (523), `OrderBridge` (511),
`OrderSigProbeM` (509), `ElimSynth4` (988), `ElimSynth3` (477),
`ElimSynth6` (764), `DeadSweep` (467), `ScatterBlockCost` (442),
`OrderEngineProbe` (414), `MassMath` (392), `BfsBridge` (385),
`BridgeCrossing` (343), `CoverWidth` (314), `OrderBlockProbe` (313),
`CostShapeProbe` (312), `DeadRow` (302), `ArenaSeam` (301),
`ScatterDeadEngine` (265), `ArenaBlock` (259), `BfsBlockDiff` (255),
`AugmentTwins` (233), `ArenaPointer` (223), `ScatterBlockMark` (222),
`ReachedBridge` (189), `BaseShed` (185), `ScatterBlockDiff` (185),
`MemThreadGate` (178), `KillListPass` (177), `ScatterBlockClear` (171),
`AugCompactScatter` (118), `BfsBlockCost` (113), `SigmaLoop` (108),
`ElimCompactSpec` (106), `DeadRowDomain` (104), `DeadRowSigma` (103),
`T1FriProbe` (79), `ScatterBlockBfs` (55), `TgtWidenProbe` (946).

The layer was `sorry`-free and axiom-free. It was not *wrong*; it did not
reach its target. §2 says why.

---

## §2 Why it did not close — the one finding that matters

> **Rev 2, 2026-08-17, after audit.** Rev 1 of this section justified the prune
> on two claims taken from `c0-road-plan.md` §1. A 7-agent adversarial audit
> against the deleted code found the first mislabelled and the second false.
> The decision survives; the reasons are replaced. What Rev 1 said, and what
> is true, are both recorded below, because the failure mode — reading a
> compiled theorem as evidence for a proposition its statement does not
> express — is the most important process finding of the whole campaign.

### What is true

**The program is cubic, by inspection of three definitions.** `RamCover.coverCom`
(`RamCover.lean:859-864`) is `while c < n` around `centreStep`, which contains
`emitLoop` (`:840-841`) `while z < n`; neither guard reads the alive mask.
`RamDriver.coverPhase` (`RamDriver.lean:2723-2728`) runs it **once per node**,
and `compactCom` yields `Θ(n)` depth-1 nodes, so at `ℓ ≥ 2` the program
executes `Ω(n³)` steps *on an edgeless input*. The deleted source concedes the
shape at `RamCover.lean:1053-1058`: *"the sharp charging of the emitted blocks,
`Σ |X_v| ≤ n^{1+δ}`, is the analysis's business and not the program's."* It is
not, and that sentence is the whole error in one line.

**A compiled theorem says the cover *contract* carries a per-node carrier floor
that no coefficient repairs.** `Refine/CoverBlock.lean:315`
`carrier_le_arena_of_coverOut` proves `n ≤ m` from `OrdersBy` + `CoverOut`
alone; its docstring: *"at depth ≥ 1 the copy really does read the carrier, and
no constant `k` makes `12·m + 6` fit `k·(w + 1)`."* The carrier-indexed object
is `RamCover.CoverOut` (`RamCover.lean:724-750`), **every clause of which
quantifies over the carrier**. That, not any single loop, is the defect.

So the structural diagnosis stands, and is an *understatement*:

> Every node of the recursion allocated and swept arrays of length `n`, while
> the source's cost argument charges each cluster `O(|V(G_X)| + |E(G_X)|)` and
> rests on `Σ_X n_X ≤ n^{1+δ}`.

Per node the cover phase alone is `coverCost n ns = 100n² + 50n·ns + …`,
independent of arena size — so the cost is `Θ(n² + n·ns)` per node, not
`Θ(n)`. Inside a turn, one depth-`j` cluster step executes roughly
`(sigL cap mb j + mb + 3)·cap + 2·sigL + mb + 2j + 12 + #atoms` carrier-wide
passes across six constructs (`fillUpto`, `expandCom`, `enumBatch`,
`outProbeCom`, `readbackCom`, `RamBfs.initDist`).

`algorithm-v2.md` §1 turns this into invariant **P1** — *below the root, no
array, loop bound, or quantifier ranges over the input vertex set* — and makes
it a review gate rather than a cost theorem discovered at the end.

### What Rev 1 claimed, corrected

**(1) "The compiled theorem refuted the target through its own root."**
Mislabelled. `Spec B P c Q K` means "at a cost of **at most** `K`"
(`word-ram/proofs/Lax13Proofs/Spec.lean:55-57`), so
`Refine/SlotSweep.lean:647`'s `128·n³ ≤ Kdec + (Kl 0 (n+ns) + Ksent)` is a
floor on the **budget parameters** the root's cost-slot interface can be
handed, not on steps executed. An exhaustive sweep of all 130 deleted files
found **no theorem anywhere lower-bounding a real `BigStepB` run**. So the
theorem refutes the *proof architecture*; the program is refuted separately and
by inspection, as above; and the *algorithm* is untouched by either. The three
levels must be stated separately.

Decomposing the floor (`SlotSweep.lean:569-579`) confirms the split:
`128 = 16` (descend) `+ 112` (the depth-1 cover phase at an **empty** arena).
The `112` is program-real. The `16` is accounting slack —
`RamDriverDescend.lean:2565-2567` bounds *one block's row* by the whole arena
length, discarding the `Xoff c ≤ p` its own loop invariant `CluScan` supplies
at `:2338`, while the program scans exactly `blockSize` iterations and the
campaign's own block re-measurement of the same pass is linear
(`blockLoadK m₁ m = 15·m₁ + 15·m + 30`, `BlockLeaves.lean:416`). So
`SlotSweep.lean:485-488`'s *"a turn pays `16·n²` before it has looked at its
block"* is **false of the program**. The same mechanism inflates `ballCost`'s
`n·ns`: `expandStep_spec` (`RamDriverDescend.lean:939-946`) charges the whole
edge count for a single vertex whose program text scans only its own CSR row.

**(2) "Twelve orders of magnitude."** `SlotSweep.lean:713` is
`(10^6)^2 * (10^8+4)^3 < (128 * (10^8)^3)^2` — eight orders unsquared at
`c = 10⁶, n = 10⁸`, sixteen in the guard's squared form. Never twelve. The
figure was copied from a line comment in the deleted source without checking.

**(3) "No constant closed the turn slot."** `G2CostProbe.lean:799`
`hKs_gap (ct ksc Kin cap j : ℕ) : ∃ n, ¬ (descendCost n 0 cap j ≤
turnCostSizeA ct ksc 0 Kin)` is genuinely universally quantified, but only over
budgets of `turnCostSizeA`'s *shape*, read at block size `0` and `ns = 0`. The
correct sentence is: no budget of that shape dominates the current
`descendCost`. After the accounting slack of (1) is removed the certified gap
is `Θ(n)` per turn, not `Θ(n²)`.

**(4) "ε = ½ clears with 10⁴–10⁶ of headroom; the algorithm is not a dead end;
the gap was shape, not headroom." — FALSE, and struck.** Four independent
failures:

- `#guard gateHalf famHalfMeasured` is evaluated at `kscProbe = 10⁴` and
  `CbProbe = 10⁴`, two numerals **the same file compiles as unrealisable**
  (`C0CloseProbe.lean:755` `landed_scatter_leaf_unbounded`, `:1469`
  `no_constant_Cb`). That file's own headline, 560 lines above the guard, reads
  *"The close does not hold at the landed constants"* (`:22-24`).
- "10⁴–10⁶ on every row" describes **3 of 8** rows; the table at `:563-570`
  prints `—` four times and `DEFICIT` once, and one of the three is annotated
  "(chosen)". The aggregate headroom in the gated quantity is **763×**, not
  10⁴ — the per-constant figures are sensitivities of a product.
- `ℓ = 3, D = 8` are hard-wired (`:581-583`). At the binding `ε = ½` gate the
  pass dies at `ℓ = 6`, and all four `(ℓ, D)` pairings the file offers as the
  ℓ-sensitivity mitigation pass the blind `ε = 1` gate and **fail** `gateHalf`.
  Across `D ∈ [1,79]` nothing clears past `ℓ ≈ 18`, against a class-forced
  `ℓ = N(2s+2)` at radius `2·9^12`.
- Even passing, `gateHalf` is a decidable predicate on an **n-free numeral**
  with no link to any `Spec`, cost function, or program. The theorem that does
  reach `n^{1+ε}` (`c0_shape_real`, `:417`) takes the cost bound as a
  *hypothesis* and yields `n^{1+ε}` for `ksc = 10^100`.

**Therefore: nothing in this repository supports — or refutes — the claim that
the algorithm can meet `n^{1+ε}`.** The compiled evidence bears only on this
implementation. The argument for the algorithm is the GKS paper's running-time
analysis, which is *not formalized here*, and `algorithm-v2.md` §7 is a fresh
derivation of it, not a transcription of anything compiled. Treat it as
unverified until it is proved.

### Was the prune right anyway

Yes, on (a) the cubic program above, (b) `carrier_le_arena_of_coverOut`'s
un-repairable contract floor, and (c) the fact that `c0-road-plan.md` §2's
repair programme never mentions `pdCom`, `puCom`, `colourCom`, `enumBatch`,
`outProbeCom` or `orderCom` — zero occurrences each — so its **76–180 wave**
estimate prices an incomplete programme. It was a judgement call with the odds
visibly against the retrofit, not a forced move.

---

## §3 What the layer established, and should not be re-derived

Nine facts. Each is worth keeping; none requires reading the code.

1. **Fidelity: the cost model is per cluster.** GKS charge each cluster
   `O(|V(G_X)| + |E(G_X)|)`, and the `n^{1+ε}` proof rests on
   `Σ_X n_X ≤ n^{1+δ}` (GKS, arXiv:1311.3899, the equation their §8 running-time
   argument closes on; the text is not in `references/` — refetch it if the
   line-level citation is wanted). Both passes the campaign disputed exist in
   the source at the same frequency — once per cluster. This is
   `algorithm-v2.md` P1.

2. **Isolation eliminates GKS §8's variant machinery with no residue.**
   Verified against the source before implementation. Their per-cluster step
   removes Splitter's batch, expands with exact-distance predicates
   `Q_{ij} = {v : dist(v,w_j) = i}`, then selects a rewritten `φ^θ` per atomic
   `q`-type `θ` of the removed tuple, and needs auxiliary `ξ_j(x̄,ȳ) = ξ(y_j)`
   to read truth *at* removed vertices. Under isolation: `Q_{ij}` becomes the
   capped profiles, `θ` is carried by the profile rows *at* the batch vertices
   (`w_i ∈ D_{j,a}` iff `T_{ij} = a`), the variant family collapses to a single
   `iso(φ)`, and the readout formulas have nothing to do — the vertices never
   left. This is `algorithm-v2.md` D2.

3. **The radius schedule is flat.** Every radius anywhere in the run is
   `≤ ρ⁻(0,q)`, with the sharper constant `ρ* = ρ⁻(0,q)` and not `ρ⁻(1,q)`.
   The reason is architectural and is the invariant to state: the isolation
   rewrite preserves distance rank, and every arena re-runs the locality
   theorem fresh at unchanged rank. `algorithm-v2.md` L0.

4. **`iso`'s metric kernel is one walk lemma.**
   `dist^A(x,y) = min( dist^{A∖W}(x,y), min_j (p_j(x) + p_j(y)) )` with
   `p_j(v) = dist^A(v,w_j)`. This survives in `Isolate.lean`.

5. **The one hard import for the cover degree** is the in-degree bound for
   transitive–fraternal augmentations on nowhere dense classes (GKS §6, cited
   there to Nešetřil–Ossona de Mendez). It is *not* in the sparsity notes and
   *not* in Lax12. It survives, discharged, in `AugmentedDensity.lean`.

6. **`tgt` widening is refuted, with a smallest witness.** The level's slot
   count does not dominate the round's: `K₁,₄` — a star on four leaves oriented
   into its centre — has fraternity graph `K₄` on the leaves, occupying 12
   slots against the star's 8. Any CSR-style representation that couples a
   target array's length to the last offset must widen, not reuse. Lives in
   `TgtCoupling.lean`, restored — see §3a.

7. **The base case is genuinely finite.** In an edgeless arena a witness is
   seen only through its color row and its equalities with the tuple in scope,
   so two off-tuple vertices with equal rows are interchangeable, and a search
   runs over `≤ k + 2^L` candidates however large `n` is. Survives in
   `BotEval.lean`, including the permutation trick the naive induction needs.

8. **Padding fixes the signature.** The isolation palette packed at the *actual*
   batch size is not a function of the depth, so it cannot index a table laid
   out before the run; always enumerating a batch by exactly `m` entries,
   repeating when it is smaller, makes the per-depth signature graph-independent
   — and padding is invisible to `iso`, which assumes no injectivity of the
   batch enumeration. Re-derive this in the new design; it is three lines and it
   is load-bearing for `algorithm-v2.md` D5.

9. **Noncomputability propagates from the concept surface.** The formula tables
   routed through `Classical.choose` (via the existential form of
   `Lax3.Locality.locality`), which made the *cost function* noncomputable and
   so unguardable by `#guard` — `RamDriver.lean:150-152` said so in as many
   words. This is `algorithm-v2.md` O2, and it is the reason O2 is scheduled
   before any table work.

Refuted and recorded so they are not re-proposed: deleting the `pu` color
family **as stated** (the invariant is not provable while `locality` is an
existential — but see `algorithm-v2.md` O3, which re-opens it *after* O2);
a `rfl` completeness lemma for the turn cost (vacuous in one spelling,
not a definitional equality in the other); and four framework migrations
audited and dominated (index-set framing, sub-array ownership, time credits,
asymptotic interfaces).

---

## §3a Recoverable as-is, and what was destroyed that should not have been

The audit's most concrete finding: **`algorithm-v2.md` §8 step 1 — "the
cost-recursion lemma, standalone, ~150 lines, do it first" — was already
compiled, and the prune deleted it.**

**Restored (done, green at 3410 jobs):**

| file | why |
|---|---|
| `CostRecurrence.lean` | Mathlib-only imports. `exists_driverCostsSigma` (`:441`) is `algorithm-v2.md` §7's recursion with its starred hypothesis `∑ bs c ≤ D·(m+1)` **verbatim**; `:511` is the geometric bound; `sigma_root_almostLinear` (`:610`) closes `C·(⌈c·n^{ε/ℓ}⌉+1)^ℓ·(n+1) ≤ C(c+2)^ℓ·(n+1)^{1+ε}`. §7 called this file "correct arithmetic for the wrong program"; that was wrong — the *affine* recursion in its opening prose is the driver's, but the Σ-form theorems below it are architecture-neutral. |
| `TgtCoupling.lean` | Imports `Augmentation` + Mathlib only. Carries the `K₁,₄` refutation (fact 6) **and** a positive half (`chainWidth`, `csrSlots_lt_chainWidth`, the in-degree bounds) that any implementation of §6.2 must size its arrays against. |

`CostRecurrence` is not a drop-in for §7: it assumes each level's own charge is
**linear** in arena weight (`hKo : Ko j m ≤ ko j·(m+1)`), where §7's cover phase
is `c·N^{1+δ}`, and it splits `ε` as `ε/ℓ` where §7 splits it as `ε/(ℓ+1)`.
Step 1 is therefore *amending a compiled proof*, not writing one.

**Recoverable but not restored**, because each needs the import re-layer that
would drag deleted driver files back in, and each belongs to the machine layer
that is deliberately absent until `algorithm-v2.md` §8 step 5 clears:
`SigmaLoop.lean:47` (`forRangeZeroSum`, the Σ-shaped loop rule, 108 lines —
needs `import Lax13Proofs.Reasoning` added), and `ElimCompact.lean:544`.

**Destroyed and genuinely reusable, listed so the rewrite is a rewrite and not
a rediscovery** — all architecture-neutral in *statement*, all carrying
carrier-length arrays somewhere in their preconditions, so re-deriving is
probably still right, but read them first:

- `BfsBlock` (~2.8k lines with kin): `bfsBlockK bw nb = 44·bw + 80·nb + 60`,
  **no carrier term** — this is `algorithm-v2.md` §4's `bfs` primitive, already
  costed at block scale.
- `ScatterBlock` (~3.6k): `scatBlockK = (44·bw + 110·nb + 140)·t + 65·mm + 30`
  with `greedySet` semantics — D3 and §6.5 exactly, including the greedy
  maximal set.
- the `ElimCompact` family (~6k): `bigStepB_padArrs`, `memGraph`,
  `elimCompactCost_le_arenaWeight` — this is `induce`/D1 at IMP+ level.

**Genuinely carrier-shot and rightly rewritten:** the driver contract layer
(`CoverOut`, `LevelImplements`, `OrderImplements`, `turnCost`) and the
descend/colour/order/cover program text.

---

## §4 Process findings

These are about how the work was run, and they are the reason
`algorithm-v2.md` §8 has a hard gate in it.

- **There was never a point at which the algorithm was finished as
  mathematics.** `Evaluator` proved the recursion correct but not efficient;
  the cost story lived only in the machine layer. So every machine-level
  difficulty was simultaneously an algorithm question, and neither could be
  settled without the other. `algorithm-v2.md` step 5 is a hard gate for
  exactly this reason.

- **Three artifacts, hand-synchronized.** Program text (`Com`), meaning
  (`Implements`), and charge (`turnCost`) were maintained separately and had to
  be re-aligned at every edit. The recorded hazard is verbatim: *"the program's
  cost fell and the stated budget did not."* `algorithm-v2.md` D7 makes them
  one artifact with three projections.

- **The measured rate** was ~800 net lines and ~54 minutes per wave, one wave
  at a time (4 cores, 1.4 GB per seeded worktree). The measured multiplier from
  *plan item* to *actual waves* was **2–4×**, with the campaign's own diagnosis:
  *"each blocker surfaced only when the previous cleared."* Price the new plan
  with that multiplier, not without it.

- **The recurring supervisor error**, recorded twice independently: ordering a
  two-blocker probe with the likelier refutation second. Attack the falsifier
  first.

- **The recurring worker-visible defect class** was frame breakage — changing a
  routine's write set without updating the frame lemmas that quote it. A
  combinator layer (D7) removes the class rather than managing it.

- **A cheaper route was repeatedly available and unpriced**: narrowing a
  contract clause instead of hoisting an engine. *Read what the program
  actually reads before designing a hoist — a precondition stronger than the
  program needs is indistinguishable, from the cost side, from a genuine
  program cost, and far cheaper to fix.*

---

## §5 Superseded documents

These stay in `plans/nowhere-dense-model-checking/` as evidence, and are
**not** live plans. Every one of them is written against the pruned
architecture and their process sections do not apply.

| file | what it is |
|---|---|
| `c0-road-plan.md` | the last road (2026-08-08), proposal, never adopted. §1 is the best single account of where the campaign stood; §2 onwards is retrofit work that `algorithm-v2.md` deletes. |
| `nd-mc-rebase-plan.md` | the plan of record it was proposed against (98 kB) |
| `nd-mc-plan.md`, `nd-mc-design.md` | the original campaign plan and its P0 design settlement. `nd-mc-design.md` (a)–(e) is the isolation-rewrite design and is still the best statement of §3 items 2–4. |
| `integration-design.md`, `e-mem-design.md`, `g2-cost-design.md`, `r18-design.md`, `p2-remaining-design.md`, `exl-guard-decision.md` | phase designs for pruned engines |

`plans/subagent-retro-2026-07.md` and `plans/worker-brief-template.md` are
campaign-independent and remain live.
