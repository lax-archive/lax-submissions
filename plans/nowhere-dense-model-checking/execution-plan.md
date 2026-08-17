# ND-MC execution plan — §8 of `algorithm-v2.md`, expanded into leaves

**Status: ready to execute. Written 2026-08-17, the session after Rev 4.**

This is the *static* half of the campaign state. It expands `algorithm-v2.md`
§8 into leaves a single subagent can own, with the file each owns, what it must
prove, and what it must survive. The *mutable* half is
`execution-ledger.md` — status, wave, landing commit — and the supervisor loop
that reads both is `/ndmc` (`.claude/commands/ndmc.md`).

Nothing here re-derives the design. Every leaf's source pin is a § of
`algorithm-v2.md` and a landed declaration; a leaf that cannot be traced to one
is a defect in that document, not a licence to improvise.

---

## Standing rules for every leaf

**Ownership.** One leaf owns exactly one `.lean` file, and new lemmas go into
new proofs-side satellite files. `concepts/Lax3/*.lean` is the endorsed
surface: its **statements are frozen**, and a leaf that wants one changed stops
and says so (`/ndmc` stop condition 3).

**The root module is the supervisor's.** `proofs/Lax3Proofs.lean` is a curated
import list and every new satellite needs a line in it. Workers must **not**
touch it — parallel leaves would collide on one file. The supervisor adds the
import at landing, in the commented section the file belongs to, and the
`lax build --only proofs` root-module audit is what catches a miss.

**Gates.** Every leaf: `.claude/leaf-gate.sh nowhere-dense-model-checking`
green, zero `sorry`, zero new axioms, and `lean_verify` on the leaf's headline
declaration. Leaves with an extra gate say so in their row.

**The hazard that has cost this campaign four times.** Read the theorem, not
the docstring and not the file's framing prose. Every defect the four audits
found was a place where a document asserted something its own cited object does
not say. A worker quoting a docstring back as justification has not done the
leaf.

**`deleteVerts` isolates, it does not remove.** The carrier survives
(`Lax12/UniformQuasiWideness.lean:54-57`, `DistFO.lean:119-127`). D1 renumbers.
Every carrier confusion in this campaign started at that gap; E7 is the leaf
that closes it and several other leaves depend on being careful about it.

---

## The DAG

```
  no dependencies                    gated                    final

  E0 ─┐
  E3 ─┴─→ E4 ─┐
  E1 ─────────┤
  E2 ─────────┤
  E5 ─→ E6 ───┼─→ E9 ─┬─→ E10 ─┐
  E7 ─────────┤       │        ├─→ E13
  E8 ─────────┘       └─→ E12 ─┘
  E11 ────────────────────┘
```

Read it as: **E0, E1, E2, E3, E5, E7, E8 and E11 are dispatchable on day one** —
eight of the thirteen, all independent. E4 waits on E0+E3, E6 on E5, E9 on
everything above it, E12 on E9+E11, E13 on E10+E12.

Suggested waves — but **width is the supervisor's call at dispatch time**, set
by review bandwidth, not by this diagram:

- **Wave 1 (`w1`)** — E0, E1, E2, E3. Three small, disjoint cover-layer
  satellites plus the one document leaf. The cheapest possible first wave, it
  de-risks the two lemmas §5 and §4 price at "roughly six lines" and "~10
  lines" — figures nobody has tested — and it lands **both** of E4's
  dependencies, so wave 2 opens fully.
- **Wave 2 (`w2`)** — E4, E5, E7, E8, E11. All disjoint, all unblocked by w1.
  The widest wave in the campaign; split it if review bandwidth says so.
- **Wave 3 (`w3`)** — E6, then E9 **alone**. E9 is the hard gate: no ND-MC
  driver is written until it is complete and reviewed.
- **Wave 4 (`w4`)** — E10, E12. **Wave 5 (`w5`)** — E13.

---

## E0 — the cover's time bound, written as the assumption it is

**§8 step 0b, §9 O7.** Not a proof leaf: a statement-and-record leaf, and it
gates E4's parameterisation.

Rev 4 declared this blocked on an external paper. **It is no longer blocked** —
`references/nodm05/BEII.tex` is arXiv math/0508324v2, and GKS's bracket
*[Nešetřil–Ossona de Mendez 2005, Corollary 4.2, Theorem 4.3]* resolves onto
its §4 exactly. Read `references/nodm05/README` first; it maps the file.

**And the chain now terminates.** Part II's Lemma 4.1 is itself only a
citation — *"special case of Lemma 6.1 of [POMNI]"* — so the deferral went one
level deeper than Rev 4 knew. `[POMNI]` is part **I**, now at
`references/nodm05i/`, where Lemma 6.1 is **proved in full** (`BEI.tex:1064`,
the ball-family argument), with Corollary 6.2 bounding `md(G_i)` along the
chain. Nothing below it is deferred. The leaf must not repeat the mistake that
produced this whole situation: open each link and read the statement, rather
than recording that a citation exists.

What the leaf must produce:

1. A named hypothesis in the proofs layer — a structure or a `Prop`-valued
   assumption — asserting that `cover A r` runs in `f(r,ε)·‖A‖^{1+2δ}` and
   returns an ordering, clusters and `ctr` with the guarantees §4 lists. It is
   an *assumption*, stated as one, not an axiom smuggled into a definition.
2. The honest account of what remains to be imported, written into
   `algorithm-v2.md` §8/§9: NOdM Theorem 4.3 is stated for classes of
   **bounded expansion** in time **`O(n)`**, while GKS cite it for **nowhere
   dense** with `Δ⁻ ≤ n^ε` in `f(r,ε)·n^{1+ε}`. Those are different statements.
   The paper *does* supply the round count and the per-round cost
   (`O(md²·n)`, `md(G_{i+1}) ≤ md(G_i)² + 2∇₀(G_i)`, `BEII.tex:570-680`) that
   Rev 4 recorded as absent everywhere. The gap is the nowhere-dense
   instantiation and the low-indegree orientation step — much smaller than
   importing a paper, and it is what step 0b actually owes.

**Owns:** `Lax3Proofs/CoverSpec.lean` (new), plus the §8/§9 edit.
**Deps:** none. **Gate:** the assumption's statement quantifies `f` before the
graph, and `δ` appears with the exponent E4 uses.

## E1 — cover clusters are path-closed

**§5, "The repair, and it is free".** For `X_u := {w | u ∈ wreach_π(A,2R,w)}`
and any `w ∈ X_u`, there is a walk `u → w` of length `≤ 2R` whose support lies
inside `X_u`; hence `dist_{A[X_u]}(u,w) ≤ 2R`.

Proof, and Rev 4 audited it against the definition: `wreach`
(`Lax12/ColoringNumbers.lean:64-67`) is
`{u | ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y}` — the
minimality clause is **non-strict**, over the **whole support**, about the
**endpoint**. So for `z ∈ p.support`, `p.dropUntil z` has support `⊆ p.support`
and length `≤ p.length`, and its clause holds verbatim, giving `z ∈ X_u`.
Mathlib supplies `support_dropUntil_subset` and `length_dropUntil_le`.

**Owns:** `Lax3Proofs/ClusterPaths.lean` (new). **Deps:** none.
**Hazards:** `dropUntil` needs `DecidableEq` and a membership hypothesis —
check what Mathlib's actually requires before assuming the ten-line estimate.
The fibre is `{w : u ∈ wreach π A 2R w}`, a fibre and not the wreach set
itself; getting that transposed breaks the lemma silently.

## E2 — `ctr`, and the π-min identity

**§4.** Define `ctr v := π-min(wreach_π(A,R,v))` and prove
`π-min(ball_R(v)) = ctr v`, hence `ball_R(v) ⊆ X_{ctr v}` (GKS tex:1443).

Rev 4 prices this at "roughly six lines": (1) `wreach ⊆ ball` from
`mem_wreach_iff`; (2) writing `u* := π-min(ball_R(v))`, any walk `v → u*` of
length `≤ R` has all its support inside `ball_R(v)`, so `π u* ≤ π y` for every
support vertex — which is exactly `wreach`'s third conjunct, so `u* ∈ wreach`;
the two minima therefore coincide.

**Owns:** `Lax3Proofs/CoverCentres.lean` (new). **Deps:** none.
**Hazards:** `IsNeighborhoodCover.ball_subset` is an **existential**
(`NeighborhoodCovers.lean:53`) — it does not hand you `ctr`, which is why this
leaf exists. Nothing in `OrderedCovers.lean` mentions `ctr`. Report the true
line count; the six-line estimate is untested.

## E3 — the edge half of (★)

**§7.** An edge of `A[X_u]` lies in at most `D` clusters, because both
endpoints must; hence `Σ_u ‖A[X_u]‖ ≤ (c_D+1)·‖A‖^{1+δ}`.

**Owns:** `Lax3Proofs/CoverEdgeSum.lean` (new). **Deps:** none.
**Hazards:** `CoverDegree.lean:512/524/535` are **pure vertex counts** — the
edge half has no counterpart in the surviving layer, which is why Rev 4 books
it as owed. Do not cite a vertex-count lemma as if it were the edge bound. The
`+1` is the ceiling in `D(N) = ⌈c_D·N^δ⌉` and it is load-bearing: at
`c_D = 1, δ = ½, N = 2` it is `4 > 2.83`.

## E4 — the cost recurrence, amended and **slackened**

**§7, §8 step 1.** `CostRecurrence.exists_driverCostsSigma` (`:441`) already
carries (★) as `∑_{c<t} bs c ≤ D·(m+1)` and `sigma_root_almostLinear` (`:610`)
already closes the exponent. This leaf amends them; it does not rebuild them.

Three changes, and the third is a **decision Jan took on 2026-08-17**:

1. Generalize `hKo`/`hKc` from arena-**linear** per-level charge to
   `a·N^{1+2δ}` — the honest cover exponent (GKS's own accounting for their own
   algorithm is `2n^{1+2δ}`, `gks tex:1459-1517`, where they set `δ := ε/2`).
2. Re-split `ε` over **`ℓ+2`**, not `ℓ` and not Rev 4's `ℓ+1`: the cover's own
   `2δ` costs one δ beyond what (★) accumulates per level.
3. **Take the slack; do not tighten.** Prove
   `T_j(N) ≤ K^{L+1}·N^{1+(L+2)δ}` with `L := ℓ−j`, where `A := a + c(c_D+1)`
   is a node's total non-recursive charge and the base constant is **chosen**,
   `K := c_D + 1 + A`, rather than forced into the shape `(2c)^{L+1}` with `c`
   also carrying every routine's constant. The step condition is then
   `K^L·(K − c_D − 1) ≥ A`, and the choice makes its left side exactly `K^L·A`.
   **Rev 4's `c ≥ 6` condition disappears** — it was an artifact of coupling
   the exponential's base to the routine constants, and that coupling
   is what made this the most error-prone paragraph in the document: Rev 1
   dropped the middle term, Rev 3 dropped a `c` and a `+1`, Rev 4 rewrote it
   again. A tight inequality nobody needs is a defect surface, not a result.

**Owns:** `Lax3Proofs/CostRecurrence.lean`. **Deps:** E3, E0.
**Gate:** the headline is `T_0(n) ≤ K^{ℓ+1}·n^{1+ε}` at `δ = ε/(ℓ+2)`, with
`K` and `δ` fixed before `n`, and **no** side condition on `c`. If a constant
condition survives, the leaf is not done — say which term forced it.

## E5 — `ReachedR` generalized to `S`-moves

**§8 step 2, §9 O1/O5.** Generalize `SplitterWinRec.ReachedR` from ball-moves
to `S`-moves and prove the five analogues: `isolatedR`, `mem_ball_of_roundR`,
`no_full_survivalR`, `reachedR_descend`, `reachedR_length_lt`.

The design restricts to `X_u ⊆ ball`, while `nextArenaR` restricts to
`ball e.arena r e.vtx` (`SplitterWinRec.lean:153-154`). That is the gap.
Audit-settled: the generalized `(v,S)` game **is** won — the induction closes
in ~15 lines from `SplitterMono.splitterWins_anti` plus the batch map
`W ↦ W ∩ S`, the changed-distances objection absorbed because the hypothesis is
universally quantified over graphs.

**Owns:** `Lax3Proofs/ReachedS.lean` (new); `SplitterWinRec.lean` stays frozen.
**Deps:** none. **Hazards:** *"its strategy reads only `A[S]`"* is **false** —
do not try to prove it. `SplitterWin.batch` is noncomputable and takes the
ancestor arena stack; `ReachedR` records the batch as *data of the round*,
which is the interface a program can meet. `reachedR_descend`'s `hbatch`
(`:533-538`) proves `batchR = W` **exactly**; a lemma that only proves `⊆` is
the weakened version and does not discharge the leaf.

## E6 — carrier transport for `ReachedR`

**§9, third bullet.** `RoundR n` fixes `arena : SimpleGraph (Fin n)`
(`SplitterWinRec.lean:129-135`) and `ReachedR` types `A : SimpleGraph (Fin n)`
(`:192-193`), so §5's `# pre:` line does **not** typecheck against D1's
renumbered `A : SimpleGraph (Fin N_j)`. Prove transport under adding isolated
vertices and under renumbering along a bijection.

**Owns:** `Lax3Proofs/ArenaTransport.lean` (new). **Deps:** E5.
**Gate:** §5 line 8's precondition typechecks as written after this leaf, or
the leaf says exactly what §5 must be rewritten to.

## E7 — the compaction lemma (`Sat`-transport along a bijection)

**§5 step 3′, §8 step 4a.** Transport `DistFO.Sat` between the carrier-kept
arena (`deleteVerts` on `Fin n`) and the renumbered arena (`Fin N`) along a
bijection `Fin N ≃ X`.

**This is now much smaller than Rev 3 priced it.** Rev 3 required the
transport to be *order-preserving* and to carry a *dead-vertex correction*;
Rev 4's D3 records why both clauses are phantom — the compaction comes
**before** `locality`, `DistFO.Sat` has no order-sensitive constructor, so any
bijection serves, and no greedy value crosses the boundary because scatter
atoms are evaluated at `B` on `B`'s own carrier
(`ScatterSentences.lean:180-184`, `greedySet :126-133`).

**Owns:** `Lax3Proofs/Compaction.lean` (new). **Deps:** none.
**Hazards:** the only transport lemma in the surviving layer is
`BotEval.sat_congr_bot_of_bij`, restricted to the **edgeless** graph — it is a
model to copy, not a lemma to apply. If the leaf finds it *does* need
order-preservation, that contradicts D3 and is a stop-condition-2 finding, not
a thing to quietly add as a hypothesis.

## E8 — the locality decomposition as a function

**§8 step 3, §9 O2.** D5 requires the rewrites to be **functions**, not
existentials. `rel` and `iso` already are; the locality decomposition is not.

**Owns:** `Lax3Proofs/LocalityFun.lean` (new). **Deps:** none.
**Hazards:** the payoff is smaller than Rev 1 claimed and the leaf should not
over-promise: `ℓ`, `m`, `c_D` remain `Classical.choose`, so `ℱ_j` stays
noncomputable regardless. What this buys is a *function*, not decidability.
`locality` pins its rank's first argument to the arity
(`Locality.lean:103-105`), so below the root it is only ever invoked at `k = 1`.

## E9 — the abstract algorithm — **hard gate**

**§8 step 4.** §5's pseudocode over the `Arena` interface of §4 taken
abstractly: correctness by §5's chain, cost by §7. **No ND-MC driver is
written until this is complete and reviewed.**

**Owns:** `Lax3Proofs/AbstractDriver.lean` (new), and likely more than one
file — if it splits, it splits into leaves with a fresh row each, decided at
dispatch. **Deps:** E1, E2, E4, E5, E6, E7, E8.
**Hazards:** the whole of §5's chain, but especially: profiles are
**cumulative** (`≤ a`, not `= a`) and measured in `B₀` *before* isolation —
measuring them after gives `∅` for every `a ≥ 1` and the rewrite is **unsound**,
not lossy (`Isolate.lean:751-757`, walk kernel at `:536`); the batch must be
**padded** to exactly `m`; and `greedyScatter` must guard `t = 0` explicitly or
it is `Θ(N²)` silently with a correct answer (`ScatterSentences.lean:193`).

## E10 — unrolling the depth-`ℓ` recursion

**§8 step 4b.** Lax13's machine has no call stack: unroll §5's recursion into
`ℓ+1` depth-indexed levels. Say whether the frames are laid out **statically**
at the maximum arena per depth or **dynamically**, and price it against §11.

**Owns:** new file, named at dispatch. **Deps:** E9.

## E11 — the `Refine` tower probe

**§8 step 5.** Instantiate `Lax13Proofs.Refine` — 127 landed files: a
cost-carrying NREST monad with time and data refinement, Sepref with
amortization and heap allocation, an IR with weakest-preconditions and a
separation solver, `Iicf` collections, `Asymptotics/Recurrences`, and a
`Codegen` landing on the endorsed boundary (`Refine/Codegen/Cash.lean:407-419`
concludes `ComputesInTime`) — on **one** ND-MC routine: bounded-depth BFS,
which the tower already carries as an acceptance program. Check the charge
falls out.

**Owns:** new file under `Lax3Proofs/`. **Deps:** none — run it early and in
parallel; it is a one-week probe with a landed example to copy, **not** a layer
to build (D7). `SpaceBudgetProbe`/`HeapAlloc` are also where §11 gets
confronted. **Gate:** report what the charge actually was, not that it worked.

## E12 — the `Arena` implementation and the remaining routines

**§8 step 6.** `restrict`, `isolate`, `bfs`, `bfsSupports`, `recordProfiles`,
`cover`, `greedyScatter`, `BotTables`, and `ctr` computed from the sweep.

**Deps:** E9, E11. **Hazards:** §6.1's scratch array is **one per node**,
reused across children and cleared only at the `|S|` touched entries — one per
child is `Θ(A.N²)`. The `restrict` charge is `O(Σ_{s∈S} deg_A(s) + …)` and
**no data structure achieves `O(‖A[S]‖ + |S|)`** (`K_{3,n−3}` witness, §4);
a worker who "optimizes" to the latter has proved something false.

## E13 — compose to the headline

**§8 step 7.** `Lax3.ModelChecking`'s
`exists_almostLinearTime_program_modelChecking`, at the **squared** word-length
side condition (`ModelChecking.lean:115` for the axiom, `:122` for the side
condition). **Deps:** everything.

---

## What is deliberately not a leaf

- **§8 step 0a, the space half.** Settled and *unconditional*: a cover degree
  is at most the carrier size, so `Σ_u |X_u| ≤ N²` for every `ε` and `δ` with
  no hypothesis (`wreach_fibre_eq` `CoverDegree.lean:584`, `sum_ncard_le_mul`
  `:512`), and the guarantee is `2^w ≥ c·(|x|+1)²` (`ModelChecking.lean:122`).
  Nothing to probe. Do not spend a week on it.
- **Streaming the cover, and bounding the augmentation chain's live memory**
  (§11 repairs 1 and 2). Real, and they would let the *linear* side condition
  be restored — but off the critical path.
- **Formalizing NOdM 2005.** E0 states the cover's time bound as an
  assumption. Discharging it is a campaign, not a leaf.
