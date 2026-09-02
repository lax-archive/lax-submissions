# lax-65 — proof plan

Status: PROPOSAL 2026-09-02. The concept package is complete and builds
(14 concepts, 0 proofs); every statement below is an open axiom. This file
is the plan for discharging them. It is not submission content.

## 1. What has to be proved

Eight statements, one concept module each. Definitions they use are in
the five definition modules of the same package (`FeedbackVertexSet`,
`BonnetDepresGraph`, `OrientedTwinWidth`, `GridNumber`, `GraphFamily`),
plus `Lax48.Treewidth` and `Lax48.TwinWidth` (registered lax-48 @
`b999c28`).

| id | paper | statement |
|----|-------|-----------|
| `TreewidthOfBonnetDepres.treewidth_le` | Lemma 6 | tw(G_{t,ε}) ≤ t+1 |
| `TwinWidthOfBonnetDepres.two_rpow_lt_twinWidth` | Lemma 7 | 2^{(1−ε)t} < tww(G_{t,ε}) |
| `OrientedTwinWidthOfBonnetDepres.orientedTwinWidth_le` | Lemma 8 (§4) | otww(G_{t,ε}) ≤ t+1 |
| `GridNumberOfBonnetDepres.gridNumber_le` | Lemma 9 (§4) | gn(G_{t,ε}) ≤ t+2 |
| `ExponentialSeparation.exists_feedbackVertexSet_and_two_rpow_lt_twinWidth` | Theorem 1 | ∃ G on `Fin n` with a fvs of size t and 2^{(1−ε)t} < tww(G) |
| `TreewidthCorollary.exists_family_two_rpow_treewidth_lt_twinWidth` | Corollary 2 | family, tww > 2^{(1−ε)(tw−1)} |
| `GridNumberCorollary.exists_family_two_rpow_gridNumber_lt_twinWidth` | Corollary 3 | family, tww > 2^{(1−ε)(gn−2)} |
| `OrientedTwinWidthCorollary.exists_family_two_rpow_orientedTwinWidth_lt_twinWidth` | Corollary 4 | family, tww > 2^{(1−ε)(otww−1)} |
| `ApexCorollary.exists_family_twinWidth_deleteVertex_lt_twinWidth` | Corollary 5 | family, ∃ v, (2−ε)·tww(G−v) < tww(G) |

All four lemmas carry the paper's standing hypotheses `0 < ε ≤ 1/2`,
`1/ε < t` as explicit arguments; the corollaries quantify over every
`ε > 0`.

## 2. What lax-48 already provides

`twin-width-treewidth-separation/proofs` (`Lax48Proofs`, same commit as
the registered concepts) contains a complete proof of the instance
ε = 1/2, t = 2k+3, bound 2^k:

- `Source/TwinWidth/Contraction/{Trigraph,TwinWidth}.lean` — trigraph
  contraction sequences with explicit black/red state; generic in the
  graph. Reusable as is.
- `Source/TwinWidth/Graph/{Partition,Treewidth,TreewidthContract}.lean`
  — bag partitions, the treewidth API (`treewidth_le_of_hasTreewidthAtMost`
  and friends). Reusable as is.
- `Source/TwinWidth/Graph/BonnetDepres.lean` (≈570 lines) — the tree
  `FullTreeNode branch depth`, parent/child/level lemmas, the apex
  adjacency by binary bits, the tree decomposition of width t+1 and
  `bonnetDepres_treewidth_le`. **Specialised**: branch = 2^(2k+3), child
  labels are `Fin branch` decoded bitwise, depth is the explicit
  `bonnetDepresDepth k`.
- `Source/TwinWidth/Graph/BonnetDepresLowerBasic.lean` +
  `BonnetDepresLower.lean` (≈3500 lines) — the paper's Lemma 7 with every
  threshold a power of two: `d ≤ 2^k` for 2^{(1−ε)t}, `manyChildrenThreshold k`
  for 2^{εt}, and a depth chosen so that the final count closes over ℕ.
- `Main.lean` — the bridge between source trigraph sequences and
  `Lax48.TwinWidth.PartitionSequence` (both directions, `redDegree`
  transport, `lt_twinWidth_of_not_hasTwinWidthAtMost`,
  `mapIsoPartitionSequence` for relabelling along a graph isomorphism).
  Generic in the graph; reusable as is.

Recommended reuse: `proofs/lakefile.toml` requires `Lax48Proofs` at
`b999c28` (`subDir = "twin-width-treewidth-separation/proofs"`; the spec
admits proof-package requires with a warning) for the contraction layer,
the treewidth API, and the bridge. The two `BonnetDepres*` files are
copied into `Lax65Proofs/Source/` and generalised; they are not imported.
Alternative if the warning is unwanted: copy the four generic files too
(no semantic change, ~1500 more lines to own).

## 3. Parameter translation

The concept's vertex type differs from lax-48's: child labels are
`Finset (Fin t)` (the neighbourhood itself) instead of bit-decoded
`Fin (2^t)`, and the depth is `f ε t : ℕ` computed from reals. The
paper's thresholds are reals; all counting is over ℕ. Fix the integer
thresholds once, in `Lax65Proofs/Source/Constants.lean`:

- `lowBound ε t := ⌊2^{(1−ε)t}⌋₊` — an integer `d` satisfies
  `d ≤ 2^{(1−ε)t}` iff `d ≤ lowBound`; the lemma's conclusion
  `2^{(1−ε)t} < tww` is `¬ HasTwinWidthAtMost G (lowBound ε t)` after
  `Nat.floor` arithmetic.
- `manyChildren ε t := ⌈2^{εt}⌉₊` — the "at least 2^{εt} children in one
  part" of property P.
- `apexBudget ε t := ⌊C ε t⌋₊` — the bound on |B|.

The real-analysis facts the paper uses, each a lemma in that file
(hypotheses `0 < ε ≤ 1/2`, `1/ε < t`):

1. `2^{t−1} > lowBound` — Claims X, X-T (needs εt > 1).
2. `(manyChildren − 1)·(lowBound + 1) < 2^t − 1` — Claim
   large-children-batch (needs ε ≤ 1/2; the paper writes ε < 1/2, check
   the boundary case ε = 1/2 explicitly, and if it fails there, the
   concept hypothesis `ε ≤ 1/2` is the paper's and the claim must be
   re-derived with the weak inequality).
3. `manyChildren ≥ 2` — Claim p-implies-q.
4. `f ε t ≥ 3` — Claim X-T; also `t ≥ 3` from `1/ε < t`, `ε ≤ 1/2`.
5. `|B|·⌈εt⌉ ≤ t·lowBound` hence `|B| ≤ apexBudget` — each part of B is
   red-adjacent to ≥ log₂(manyChildren) ≥ εt apex singletons.
6. The closing chain: with `s := ⌊log₂((f−2)/|B|)/((1−ε)t)⌋ − 1`,
   `(s − |B|)/|B| > lowBound` — this is exactly where `f ε t` is used;
   derive from the definition of `f` and (5).

Refute before prove (standing practice): evaluate 1–6 numerically at
(ε, t) ∈ {(1/2, 3), (1/2, 5), (1/4, 5), (1/10, 11)} with `norm_num`/`#eval`
on rationals before any proof; `f ε t` is astronomically large, so
evaluate the inequality in log form.

Everything else in the lower bound is combinatorial and mirrors the
lax-48 source proofs with `2^k`, `manyChildrenThreshold k` and
`bonnetDepresDepth k` replaced by the named constants.

## 4. Leaves and DAG

Each leaf is one worker in one seeded worktree (CLAUDE.md workflow),
landed on `main` after review. Gates for every leaf: `lake build` of
`proofs/`, `lax build twin-width-exponential-in-treewidth`, and
`lean_verify` on each new `conclusion:` theorem showing only background
axioms plus required-package statements.

- **L0 scaffolding** — proofs lakefile requires `Lax48Proofs`; module
  layout `Lax65Proofs/Source/{Constants,BonnetDepres,Treewidth,Lower,
  Oriented,Grid}.lean`, `Lax65Proofs/{Lemmas,Theorem,Corollaries}.lean`.
  `lax build` green with 0 proofs. Sequential, first.
- **L1 constants** — §3 items 1–6 with their numeric refutation. No
  dependency. Parallel with L2.
- **L2 graph structure** — port `BonnetDepres.lean` to
  `Lax65.BonnetDepresGraph`: parent uniqueness and levels, children of a
  node indexed by `Finset (Fin t)` (`2^t` of them, distinct
  neighbourhoods), root has no apex neighbour, apex set independent,
  `Fintype.card` of levels, the tree part is a tree (`IsTree` of the
  induced graph on `Sum.inr`, needed for the feedback vertex set). No
  dependency. Parallel with L1.
- **L3 treewidth** — tree decomposition with bags `X ∪ {v, parent v}`
  indexed by the tree, width t+1; discharges Lemma 6. Depends on L2.
- **L4 lower bound** — the port of `BonnetDepresLowerBasic` +
  `BonnetDepresLower` against L1's constants, in the paper's claim order:
  (a) apex parts are singletons before the first root-child contraction
  (Claims X, X-T, X-sing); (b) properties P and Q, Claims
  large-children-batch(2), hereditary, p-implies-q; (c) Claim branches;
  (d) |B| ≤ apexBudget; (e) the B' chain; (f) the final count. Then the
  bridge through `Lax48Proofs.Main` to `Lax48.TwinWidth.twinWidth`;
  discharges Lemma 7. Depends on L1, L2. Largest leaf; split (a)–(c) and
  (d)–(f) into two sequential workers if the first exceeds a day. Claims
  are not concepts; keep them as named theorems in the source files.
- **L5 Theorem 1** — from L2 (X is a fvs: the tree is acyclic) and L4;
  relabel `G_{t,ε}` onto `Fin n` by `Fintype.equivFin`, transport the fvs
  and twin-width along the isomorphism (`mapIsoPartitionSequence`).
  Depends on L4.
- **L6 oriented twin-width** — new proof. Build the oriented sequence:
  contract T bottom-up (a deepest leaf into a sibling leaf when one
  exists, else into its parent), each merge's red arcs leave the merged
  part and there is at most one (toward the parent), so the tree part is
  an oriented 1-sequence; then the remaining t+1 parts contract in any
  order with out-degree ≤ t. Discharges Lemma 8. Depends on L2. Parallel
  with L4.
- **L7 grid number** — new proof. The ordering ≺ (X first, then leaves,
  preleaves, …, root); `gn(M) ≤ gn(M_T) + t` for deleting t rows and
  columns; no 3-grid minor in `M_T` because above the diagonal no two
  1-entries are in strictly decreasing position. Both steps are terse in
  the paper; expect this to be the longest new development after L4.
  Discharges Lemma 9. Depends on L2. Parallel with L4, L6.
- **L8 Corollaries 2–4** — one family for all three:
  `F = {G_{t,ε'} : t > 1/ε'}` with `ε' = min ε (1/2)`; unbounded
  twin-width from Lemma 7 (2^{(1−ε')t} → ∞), and the bounds from Lemmas
  6, 8, 9 since `tw−1, otww−1, gn−2 ≤ t` and the exponent is monotone.
  Depends on L3+L4, L6, L7 respectively; three short theorems.
- **L9 Corollary 5** — needs two generic lemmas not in lax-48:
  twin-width is monotone under induced subgraphs, and `tww(T) ≤ 2` for
  the tree (from the sequence of L6, counting in-arcs too, or the
  classical 2-sequence for trees). Then the chain
  `T ⊂ T+x₁ ⊂ … ⊂ T+X = G_{t,ε'}`: the product of the successive ratios
  is `tww(G)/tww(T) > 2^{(1−ε')t}/2`. For a target M, the prefix of
  steps with `tww ≤ M` contributes at most `M/2` by telescoping, so the
  suffix contributes more than `2^{(1−ε')t}/M` over at most t steps and
  some step has ratio `> 2^{1−ε'}/M^{1/t}`, which exceeds `2−ε` for
  small `ε'` and large t. The family is the set of these `T+{x₁..x_j}`
  over all M; v is x_j. Depends on L4 and the two generic lemmas
  (their own leaf, parallel with L4).
- **L10 close** — `conclusion:` frontmatter on the eight theorems,
  `lax build`, resubmit the draft. Sequential, last.

Critical path: L0 → L2 → L4 → L5 → L10; L1, L6, L7, L9's generic lemmas
run beside it.

## 5. Risks

- The boundary case ε = 1/2 in §3 item 2: the paper's Claim uses
  ε < 1/2 strictly while Theorem 1 admits ε ≤ 1/2. Check numerically
  first; if the strict inequality is needed, the claim's count has one
  unit of slack elsewhere (2^t − 1 vs 2^t) to absorb it.
- `f ε t` is a `Nat.ceil` of a real expression; keep every use behind
  the two facts `f ≥ 3` and the closing inequality (item 6), never
  unfold it in combinatorial files.
- The oriented twin-width concept records arcs by the rule "all red
  edges incident to the merged part leave it". L6 must build sequences
  satisfying that literal rule, including its restriction to current
  parts.
- The grid-number concept fixes adjacency matrices by bijections
  `Fin n ≃ V`; L7 has to name the ordering ≺ as such a bijection and
  reason about consecutive index intervals, not about sets.

## 6. Open decisions for Jan

- `supersedes: lax-48` is set in `manifest.yaml`; the link becomes
  permanent only when lax-65 registers. Drop it if lax-48 should stay the
  canonical entry.
- lax-65 is owned by jan3er only; lax-48 also lists EdouardBonnet.
  `lax owners` adds him if wanted, before registration.
- Whether to require `Lax48Proofs` (one warning, ~1500 lines reused) or
  copy the generic files (§2).
