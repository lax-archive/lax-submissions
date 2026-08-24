# Two decisions, and the panel that scoped them (2026-08-24)

Four read-only analysts, one per option, each instructed to attack its own
option first. This is their synthesis, with the supervisor's recommendation.
Nothing here is a landing; the ledger records what landed.

---

## Decision 1 — ⟨D⟩: the batch is not machine-computable

**The finding.** `batchRoot` (`DriverArena.lean:246`) `= genSet (2R) A.hist (A.up u)`;
`genSet` unions `pathSet` (`SplitterWin.lean:192`); `pathSet` (`:152`) is
`(withinDist_iff.mp h).choose.support` — a **`Classical.choose`-picked walk**.
But `childArena.G = deleteVerts preG (Set.range (batchFn …))` and
`profilesCom_specW` (`SolveFrameStages.lean:802`) *requires the batch region to
already hold `batchFn`'s values*. So the child-construction pass must compute
the batch exactly, and no program can. `pathSet` appears in **no** machine-layer
file. This blocks F6c12 residual 1.

### What the panel found

**Option 1 — canonicalize `pathSet`. DEAD as scoped, but a needed ingredient.**
Canonicalization is cheap (~200–300 lines, mostly relocation) and breaks
*nothing*: `hfits`, `hself` and `hwalk` all survive verbatim, and
`reachedS_descend`'s own docstring says "the program owes no equation between
the walk it found and any other walk." The kill-shot is the **graph**:
`pathSet`'s argument is `e.2`, the round's *unrestricted* arena, while the
affordable pass BFSes `preG` (the cluster restriction), because stage order is
restrict-then-BFS and keeping the BFS inside `A[X_u]` is what §5's
path-closedness invention exists to license. The gradient walks provably differ
(a vertex `c` with `π c < π u` adjacent to both endpoints is outside `X_u`, so
`Finset.min'` picks differently). Option 1 alone converts "no program can output
it" into "only a `Θ(N·‖A‖)`-per-node program can", moving the failure into the
cost chain.

**Option 2 — define the batch off the channel. VIABLE.** All four kill-shots
fail, and the two structural ones were verified against the objects:

- `MArena.restrict` (`ImplRestrict.lean:204`) sets
  `hist := fun a r => (A.hist (restrictEmb S a) r).filterMap (toLocal S)` —
  **old columns are carried down, correctly filtered, for free**.
- `supportsCom_specW` (`SolveFrameStages.lean:410`) leaves
  `{ A with hist := fun v p => if p = e then descendCol A.G D d v else A.hist v p }`
  — **exactly one column written, the rest inherited**.

So the machine needs a source only for the *current* round, and that source is
`centreChild`, which exists by construction. Far ancestors need no name. This is
§5 line 17/23 realized with the landed stages, one BFS.

**Shape matters**: the channel must become a **field** of `Arena`, ℕ-indexed —
an added *field* leaves all 565 `Arena Λ n₀` ascriptions valid; an added *index*
does not. `Round` need not be extended; wave 4's scoping survives.

**Option 3 — parameterise over the three properties. VIABLE, but no instance.**
Semantically free: correctness and the *entire* cost layer are provably
batch-agnostic (`DriverCost` mentions `batchFn` once, immediately projected to
`.1`), and the abstract layer's whole coupling to `genSet` is **4 call sites in
3 lemmas**, ~40 lines of real mathematics. No type depends on the batch, so no
cast work. But it costs ~138 signatures / ~418 call sites across 27 files, 56 of
98 modules rebuilding — 1–1.5 worker-weeks, or 3–5 days spelled as a `Setup`
field. **And it does not by itself produce an instance**: the per-round-recompute
channel provably fails `hwalk`, because every ancestor round's connector is
edge-isolated in the current arena, so a BFS from it reaches nothing and the
batch degenerates to `{u}` — verbatim the vacuity §5 ⟨A⟩ already recorded.

### The convergence

Two analysts, working independently on different options, arrived at the same
place: **the substance is the inherit-and-patch channel** (recompute the current
column, inherit the rest). Option 3's `IsBatch` is packaging around it; Option 1
is an ingredient of it.

### Recommendation — Option 2, with one prerequisite

1. **Fix the radius mismatch first.** `ProgFrame.lean:392` runs the supports BFS
   at `S.R`, but the cluster is the wreach fibre at `2R`, and
   `SolveFrameStages.lean:387` says outright that the discharger instantiates
   `2R`, "never `S.R`". Today `_DT` is discarded so the mismatch is inert; under
   Option 2 the column must be at `2R` or it does not cover the cluster. *This
   is the same stale figure the w14 entry already flagged.* Cheap, and it is
   what makes the new invariant clause true.
2. Add `chan : Fin N → ℕ → List (Fin N)` as an `Arena` field.
3. Define `batchPar := {u} ∪ {z | ∃ e < A.hist.length, z ∈ A.chan u e}`;
   `genSet`/`pathSet` leave the driver entirely (they stay live in `ReachedS`,
   where they prove Splitter wins — a different theorem).
4. Strengthen `Inv` with two channel clauses (length, and the walk witness).
5. **Skip Option 3's parameterisation.** It buys no instance and costs days of
   pure churn. Its one real merit — the obligation becoming three checkable
   clauses instead of a definitional equation — is worth a lemma, not a refactor.

Estimate: 700–1100 lines (budget 1200–1800), plus 300–600 for the batch-assembly
glue this unblocks. The concentration is `DriverCorrect.inv_child`, roughly
tripling.

**Seventh docstring-vs-object finding**: `SolveMachPrep.lean:23-26` describes a
per-round channel recompute that no landed object requires and that
`supportsCom_specW`'s signature makes impossible for far ancestors. That
docstring is what produced the original worker's second kill-shot.

---

## Decision 2 — `CovAugAdjIn`: build, or defer?

**Recommendation: neither as posed — split, price, decide.**

**(a) Build now** — 5,000–8,000 lines, 3–5 worker sessions, 2–3 waves; larger
than `SolveBlocksRestrict` + `SolveBlocksProfiles` combined. The right *end
state*, the wrong *next move*: it is blocked on F6c13, which is itself blocked,
and dispatching it as one leaf repeats the w23 packet error at four times the
scale.

**(b) Defer as an F7 hypothesis** — **not honest as the residual is currently
written**. `agC`, `Kag` and `Sag` are all free parameters, so F7 would be
assuming *a program exists*, with an unpinned budget. This campaign has never
done that: every prior residual was discharged by exhibiting a `Com`, and
`CoverOrderingTime` was categorically different — a statement about an abstract
routine with an abstract `steps : ℝ`, decidable inside Lean, which F5 decided.
If (b) is taken anyway, three things must be written down first: pin `Kag` to a
named `augCharge` and prove it inside the envelope; pin `Sag` to a length-only
descriptor; and record the statement audit (which came back **clean** —
`CovAugAdjIn` does *not* have the `AdjDeleteIn`/`AdjBuildIn` defect).

**(c) Split at the seam the landed programs already draw** — `AugBaseIn` (free:
`bldAdjCom ; peelCom` composed), `AugRoundIn`, `AugSymIn` (free: `bldAdjCom`
again); then split `AugRoundIn` into **`FratCsrIn`** and **`StepEmitIn`**, the
only genuinely new passes. Same discipline that turned `CoverAllIn` into four
programs, one level deeper, and it makes each pass's cost checkable *before*
anyone writes code — the F6c13 lesson.

### The cost envelope fits — the trap is elsewhere

F5 already prices this pipeline: `levelCharge` and `exists_chainCharge_le`
(`ProgCoverCharge.lean:150`, `:381`) give `chainCharge ≤ f·m^{1+δ}`, one δ
*inside* the envelope, by running the chain at inner exponent `δ/(2·16^R)`. The
augmentation is **not** at the boundary the way w23's peel was.

The trap is that the augmentation runs the min-degree peel `R+1` more times, and
every landed peel is `86N²`. So `CovAugAdjIn` **strictly depends on F6c13**.

### Correction to this ledger's own record

The ledger says the deferral chain is "four links long and terminates in a
proof." That elides which branch:

- The **mathematical** branch does terminate in a proof (NOdM I Lemma 6.1,
  proved in full) — but the campaign already formalized that branch
  independently and better (`AugmentedDensity`, `CoverDegree`), and does not
  need the paper.
- The **algorithmic** branch does not. GKS's `thm:computingorientation` is a
  Lemma with no proof, deferring to NOdM II; NOdM II's Theorem 4.3 is stated
  with **no proof** and is a *bounded expansion* claim in time `O(n)`, not
  nowhere-dense `n^{1+ε}`; and the step this leaf actually needs is a single
  **unproved sentence** (`BEII.tex:676-678`) covering steps 3–6 of the
  algorithm, with no pseudocode.

Blunt version: **`CovAugAdjIn` is the one place in this campaign where the
papers give nothing citable.** That strengthens the case against (b).

### The F5 transfer question — settled

The ledger left this open. Answer: **the theorem does not transfer; the proof
does, cheaply.** `coverOrderingTime_of_nowhereDense` is a bare `∃ A`, so F7
cannot extract a routine from it; and the whole cost column (`chainCharge`,
`coverC`, `exists_mcChargeMS_T`, `KsChargeBridge`) names `timedGreedyRoutine`
literally. But `greedy_chain_joint_inDegLE` (`AugmentedDensity.lean:966`) is
stated for an **arbitrary** chain, and `mdChain` supplies all three hypotheses;
`arcCount_le`/`fratPairCount_le`/`transPairCount_le`/`levelCharge_le` are
already at an arbitrary `Orientation`. Estimate: one session, ~400–600 lines.
**Required for F7 regardless of every other decision here.**

---

## The critical path

1. **The `minDegVert` tie-break** — gates both decisions. It unblocks F6c13
   *and* removes the `(R+1)·86N²` trap from the augmentation. The mathematics
   is **proved free**: `selOrderingRoutine_data` (w24) gives the six-clause
   `AugChainData` at *any* attaining selection, and `selOrderingRoutine_mdSel`
   gives conservativity; independently, `mdRankAux_props` uses only membership
   and attainment, never `min'`. One canonical linear peel would then serve
   **four** sites: the base peel, the `R` fraternity peels, and the final peel.
2. **The F5 transfer** — independent of everything, needed regardless.
   Dispatchable now; state it parametrically at the selection so it covers both
   the current and any re-pinned routine.
3. Then F6c13 unblocks, then `CovAugAdjIn`'s split.
</content>
</invoke>
