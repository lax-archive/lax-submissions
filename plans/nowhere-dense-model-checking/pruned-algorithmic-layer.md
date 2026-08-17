# ND-MC: the pruned algorithmic layer

2026-08-17. **This note exists so that nobody has to read the history.** On
Jan's instruction the whole algorithmic layer of `nowhere-dense-model-checking`
was deleted from the working tree, so that the redesign in `algorithm-v2.md`
could be done from first principles without being anchored by it.

Everything deleted is in git, unchanged, at

    816e5cc3bf14074676c56e0487af6802db7c2d2b     (parent of the prune commit)
    git show 816e5cc:nowhere-dense-model-checking/proofs/Lax3Proofs/<file>.lean

but the working assumption is that **it will not be consulted**. If you find
yourself wanting to, the right move is almost always to write the piece fresh
against `algorithm-v2.md` — the layer was shaped by an architecture that
`algorithm-v2.md` §1 rejects, so its lemmas carry that shape in their
hypotheses even when their statements look reusable.

---

## §1 What was removed, and what survived

**Removed: 105 files, 103,638 lines** — the whole word-RAM realization plus the
abstract evaluator and its cost bookkeeping.

**Kept: 25 files, ~13,000 lines** — the mathematical layer, untouched, green at
3407 jobs after the prune:

| group | files |
|---|---|
| locality engine (arXiv:2606.23180) | `WalkDistance` `Horizon` `SyntaxLemmas` `SemLocal` `Clusters` `ScatterCore` `Separation` `FarQuant` `BCAlgebra` `ScatterFml` `Assembly` |
| FO → distance logic | `Reduction` |
| isolation splitter game | `SplitterBasics` `SplitterMono` `SplitterWin` `SplitterWinRec` `UqwInstantiation` |
| sparse covers, GKS §6 | `CoverConstruction` `Augmentation` `AugmentedDensity` `OrderedCovers` `CoverDegree` |
| the two rewrites, and the leaf | `Relativize` `Isolate` `BotEval` |

`Assembly` discharges `Lax3.Locality.locality` and `Lax3.NormalForm.normalForm`
— those two concept axioms remain proved. The concepts package was **not
touched** by the prune: the endorsed statement of the headline theorem is
exactly what it was.

Stale prose references to deleted modules were rewritten in place in
`UqwInstantiation`, `CoverDegree` (six sites) and `SplitterWinRec`; the
mathematical content of those files is unchanged.

### The removed files

Grouped by what they were. Line counts are the deleted sizes.

**The abstract layer (2,509 lines).** `Evaluator` (757) — the recursion
descending the game tree, with correctness against `Sat` and a math-core
checkpoint that the evaluator decides every FO sentence on a nowhere dense
class. `FormulaTables` (659) — the per-depth formula lists, closed under the
step, with the padding trick that makes the palette depth-indexed rather than
batch-indexed. `CostRecurrence` (646) — the downward affine recursion
`Kl j ≥ a j + n·Kl (j+1)` solved, with least-solution and closed form.
`TgtCoupling` (447) — a refutation, see §3.

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

At the point of the prune, the campaign's own compiled theorem **refuted the
target through its own root**: `Refine/SlotSweep.lean:600`
(`driverRoot_decides_sentence_floored`) took the root theorem's hypotheses
verbatim and returned, alongside its specification, a *floor* of `128·n³` on
the cost — twelve orders of magnitude past the `ε = ½` budget — and
`Refine/G2CostProbe.lean:799` (`hKs_gap`) was universally quantified over the
cost parameters: **no constant closed the turn slot.**

The cause is structural, not numeric:

> Every node of the recursion allocated and swept arrays of length `n`, while
> the source's cost argument charges each cluster `O(|V(G_X)| + |E(G_X)|)` and
> rests on `Σ_X n_X ≤ n^{1+δ}`.

Concretely, in the deleted text: `readbackCom` was `while z < n` with the body
guarded by `asg[z] = cur`, so the *write set* was already the cluster but the
*walk* was the carrier; `clusterLoad` bounded a cluster scan by `n·n`;
`hasgB : ∀ v < n, asg v < B` was a carrier-wide invariant threaded through the
driver. With `n^δ` branching and depth `ℓ`, `Θ(n)` per node is `Θ(n^{2+ℓδ})`.

The last two months of the campaign were the retrofit of "block scale" onto a
carrier-scale program: §2.2–§2.6 of `c0-road-plan.md`, estimated there at
**76–180 waves, 7–15 sessions, 2–4 calendar weeks**, and that estimate assumed
no further surprises in a campaign whose measured plan-item-to-wave multiplier
was 2–4×.

`algorithm-v2.md` §1 turns this into invariant **P1** — *below the root, no
array, loop bound, or quantifier ranges over the input vertex set* — and makes
it a review gate rather than a cost theorem discovered at the end.

**The good news, and it is compiled evidence, not optimism.** At every measured
constant the `ε = ½` close cleared with 10⁴–10⁶ of headroom on every row
(`Refine/C0CloseProbe.lean:586-588`). The algorithm is not a dead end. The gap
was *shape*, not headroom. That is why `algorithm-v2.md` changes the
architecture and nothing about the mathematics.

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
   target array's length to the last offset must widen, not reuse. (Was
   `TgtCoupling.lean`.)

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
