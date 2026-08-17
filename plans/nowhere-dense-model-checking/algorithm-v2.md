# ND-MC: the algorithm, rethought from first principles

Rev 1, 2026-08-17. Status: **design for review.** Written after pruning the
whole algorithmic layer (`pruned-algorithmic-layer.md`); nothing below is
inherited from it except three *facts* that the prune note records and that are
cited here by name.

The purpose of this document is to be the thing the formalization is written
*against*: the pseudocode, its running time, and the interface each piece needs
from its neighbours. If a future Lean file cannot be traced back to a numbered
line or a numbered decision here, that is a defect in this document, not a
licence to improvise.

---

## §0 The one-paragraph algorithm

Evaluate the sentence by descending the isolation splitter game tree. At each
node the current *arena* is covered by clusters of bounded radius and small
degree; each cluster becomes one child, obtained by restricting the arena to
the cluster **and** isolating Splitter's batch in a single operation, with the
distances that the isolation destroys recorded as colors. The formula each
child must answer is determined by the parent's formula alone, by a purely
syntactic rewrite — so the whole formula schedule is a compile-time constant.
Splitter wins in `ℓ` rounds, so at depth `ℓ` the arena is edgeless and every
formula is decided by reading color rows. Information then flows back up: each
child returns a table of truth values, one bit per (vertex, tabled formula),
and the parent's table is a boolean combination of its children's entries and
of finitely many *scatter counts* — sizes of greedy maximal scattered sets,
capped at a constant. The top level is nothing but such counts.

Two traversals of one tree: **down** builds arenas, **up** fills tables.

---

## §1 What went wrong last time, in one sentence

> Every node of the recursion allocated and swept arrays of length `n`, while
> the cost argument requires every node's work to be proportional to *its own*
> arena.

The tree has `n^δ` branching and depth `ℓ`, so there are up to `n^{ℓδ}` nodes;
`Θ(n)` per node is `Θ(n^{1+ℓδ+1})`, not `Θ(n^{1+ε})`. The three years of
constant-chasing were attempts to close a gap that is not a constant. Every
design decision below is downstream of fixing this.

**Invariant P1, the one invariant this design is organised around.**

> Below the root, no array, loop bound, or quantifier ranges over the input
> vertex set. Every array a node allocates has length `O(‖A‖)` for *its own*
> arena `A`, and every loop it runs is over its own vertices, its own edges, or
> a constant.

P1 is checkable by reading a program. It is not a theorem discovered at the
end. Anything that violates it is rejected at review, whatever its cost lemma
says.

---

## §2 Standing decisions

Each decision is stated with the alternative it beats and why. These are the
things that must *not* be relitigated per-wave.

**D1 — Materialize, do not view.** A child arena is a freshly built compact
structure with its own vertex numbering `0 … N−1`, not a (parent, mask) pair
interpreted lazily.

*Alternative:* represent a child as a filter over the parent, copying nothing.
*Why it loses:* adjacency iteration then costs the **parent's** degree, so a
vertex of huge parent-degree sitting in a tiny cluster is paid for in full at
every level — `Θ(deg_root)` per access at depth `ℓ`. Materializing costs
`O(‖A[X_u]‖)` once and `Σ_u ‖A[X_u]‖ ≤ D·‖A‖` by the cover degree bound.
Memory is not a counterargument: the tree is traversed depth-first, so at most
`ℓ+1` arenas are live, each of size at most `n`.

The old layer took D1's cost model and the alternative's memory layout, which
is exactly P1's violation.

**D2 — Isolation, not deletion, and fused with the restriction.** Splitter's
move keeps the batch's vertices and drops their incident edges. The cluster
restriction and the isolation are *one* operation, `induce(A, S, W)`.

*Why:* with deletion, a vertex can leave the arena, so the formula rewrite must
case-split on whether a variable lands on a removed vertex — this is exactly
GKS §8's atomic-type-indexed formula family `φ^θ` and their readout formulas
`ξ_j`. With isolation the carrier is untouched by Splitter's move, equality
needs no readout, and **one** uniform rewrite `iso` serves every tuple with no
side condition. Both pieces of GKS machinery vanish with no residue. Fusing
with the restriction means a node performs exactly one structural operation per
child.

A second payoff, needed in §5: because vertices persist, a vertex named by an
ancestor is still present in every later arena that contains it, so bounded
history can be carried in local names.

**D3 — Greedy scatter, never distance-`r` independent set.** Scatter sentences
are Dreier–Toruńczyk's *weak* form: `A ⊨ scatter(r, β, t)` iff the fixed
inclusion-wise maximal `r`-scattered subset of `{a : A ⊨ β(a)}` has size `≥ t`,
under the **greedy choice** of that set.

*Why it matters:* under the Gaifman/GKS reading, a scatter sentence asserts
*existence* of an `r`-scattered set of size `t`, which is at least as hard as
distance-`r` independent set and needs a separate algorithm (GKS Theorem 5.1).
Under the greedy reading it is one pass. And `t ≤ k+q` is a constant, so the
greedy process may **stop after `t` picks**: we never need the true size, only
`min(size, t)`. Cost `O(t·‖A‖)`, with `t` constant.

This is the single largest simplification the source note buys us over GKS and
it should be visible in the code as a ten-line routine.

**D4 — One-variable tables, everywhere.** The only semantic objects the
recursion ever computes are bits `tab[v][β]` for `β` a one-variable local
formula. There is no `k`-ary type, no tuple table, no per-tuple index.

*Why it is available:* a sentence's locality decomposition at rank `(0,q)`
consists of local *sentences* — which are constants, see L1 below — and scatter
sentences, whose `β` has one free variable. Decomposing a one-variable formula
yields one-variable local atoms and, again, scatter sentences with one-variable
`β`. The fixed point is one variable. (`Lax3Proofs.BotEval` already records the
seed of this: a local sentence guards over the empty variable set, so its
quantifier is vacuously false.)

**D5 — The formula schedule is a compile-time constant.** The list `ℱ_j` of
formulas tabled at depth `j`, and for each `β ∈ ℱ_j` its decomposition, depend
only on `(φ, ε, C)` — never on the input graph. They are computed once, before
the graph is read.

*Requirement this imposes:* the rewrites must be **functions**, not
existentials. `rel` and `iso` already are (`Relativize`, `Isolate`). The
locality decomposition is not — see O2.

**D6 — Every node is self-contained.** A node receives an arena, a round
budget, a constant-size history, and nothing else. It never reads its parent's
arrays and never writes outside its own. The only channel upward is the table
it returns, and the only channel downward is what `induce` builds.

**D7 — Cost is written, not discovered.** Every routine is written in a
combinator layer that produces its machine text, its meaning, and its step
count *together* (§7). No routine has a separately maintained cost function.

*Why:* the pruned layer's most-repeated recorded failure was drift between
three separately maintained artifacts — `Com` text, `Implements` relation,
`turnCost` numeral — with the recorded hazard *"the program's cost fell and the
stated budget did not."*

---

## §3 Constants, fixed before the input is read

Given the class `C`, the sentence `φ`, and `ε > 0`:

```
q  := qr(φ)                              -- top quantifier rank
R  := ρ⁻(0, q) = 9^{q(q+1)}              -- the global radius cap
ℓ, m := splitter parameters of C at radius 2R     -- rounds, batch size
δ  := ε / (ℓ + 1)
D(N) := ⌈c_D · N^δ⌉                      -- cover degree at arena size N
```

**L0 (radius cap).** Every distance atom radius, every local-quantifier guard
radius, and every scatter radius occurring anywhere in the run is `≤ R`.

*Reason.* Rank travels along the schedule `(0,q) → (1,q−1) → … → (q,0)`, on
which `ρ⁻(j, q−j) = 9^{(q+1)(q−j)}` is decreasing, so `ρ⁻(0,q)` is the maximum;
guards satisfy `ρ⁺(k+1,q−1) ≤ ρ⁻(k,q)`; scatter radii satisfy
`r ≤ 9^{k+i}ρ⁻(k+i,q−i) ≤ ρ⁻(k,q)`. Crucially the isolation rewrite **preserves
distance rank exactly** and every arena re-runs the locality theorem fresh at
unchanged rank, so the descent never re-inflates a radius. One number `R`
governs the entire run: covers are taken at radius `R`, the game is played at
radius `2R`, and distance profiles are capped at `R`.

**L1 (local sentences are constants).** A local `DistFO` formula with no free
variables has the same truth value in every colored graph, computable from its
syntax.

*Reason.* With no variables in scope there are no atoms, and a local quantifier
`exL r g ψ` at arity `0` has `g ⊆ ∅`, so it ranges over the vertices within `r`
of nothing and is false. The formula is therefore a boolean combination of `⊥`.

*Consequence.* The top-level decomposition of `φ` is, after discarding
constants, a boolean combination **of scatter sentences alone**. The entire
algorithm is: compute finitely many capped greedy-scatter counts of
one-variable local formulas, and combine them.

---

## §4 The data structure

One type, one interesting operation.

```
structure Arena where
  N    : ℕ                    -- vertices, named 0 … N−1
  adj  : CSR over N           -- edges of this arena;  M := ‖adj‖/2
  L    : ℕ                    -- number of colors
  col  : Fin N → Fin L → Bool -- color rows
  up   : Fin N → ℕ            -- this vertex's name in the parent arena
  own  : Fin N → Bool         -- "this node answers for this vertex"

‖A‖ := A.N + A.M
```

`up` and `own` are the *only* link to the parent, and both are read by
iterating over the child's own vertices — never by indexing an array of parent
size. That is what makes the readback in line 17 of §5 cost `O(N_child)`
instead of `O(N_parent)`.

### Operations and their charges

| operation | result | charge |
|---|---|---|
| `induce A S W` | the arena on `S ⊆ V(A)` carrying the edges of `A[S]` not incident to `W`, with `up` set to the `A`-names | `O(‖A[S]‖ + \|S\|)`, `S` given sorted |
| `bfs A v d` | the `≤ d`-ball of `v` with exact distances, `d ≤ 2R` | `O(‖ball_d(v)‖)` |
| `pushColor A P` | append one color row | `O(A.N)` |
| `cover A r` | ordering `π`, clusters `X_u ⊆ ball_{2r}(u)`, assignment `ctr` with `ball_r(v) ⊆ X_{ctr v}`, degree `≤ D(‖A‖)` | `O(‖A‖^{1+δ})` — §6.2 |
| `greedyScatter A r P t` | `min(t, size of the greedy maximal r-scattered subset of P)` | `O(t·‖A‖)` |

**Nothing else touches the graph.** Note what is *absent*: no deletion, no
compaction, no re-indexing, no persistent/undo structure, no incremental
maintenance. `induce` subsumes all of it, because D1 says a child is built
once and never mutated, and D2 says restriction and isolation are the same
act. The "abstract data structure that allows all the modifications we need in
the right run times" is, on this design, a *builder*, not a mutable structure —
and that is the discovery that makes the whole thing small.

Every graph primitive above except `cover` is bounded-depth BFS or a linear
scan. `cover` is the only superlinear one and the only one with real content.

---

## §5 The pseudocode

```
── compile time; depends on (C, φ, ε) only ────────────────────────────────
 0  q, R, ℓ, m, δ  as in §3
 0  ℱ_0 … ℱ_ℓ      : lists of one-variable local formulas          (D5)
 0  dec_j          : for β ∈ ℱ_j, a boolean combination over
 0                   (local atoms ⊆ ℱ_{j+1}) ⊎ (scatter sentences over ℱ_{j+1})
 0  top            : a boolean combination over scatter sentences over ℱ_0  (L1)

── run time ───────────────────────────────────────────────────────────────
 1  MC(G):
 2      A := arena of G;  own ≡ true;  up := id;  hist := []
 3      T := Tables(A, 0, hist)                        -- T[v][β], β ∈ ℱ_0
 4      s := ( greedyScatter(A, σ.r, {v : T[v][σ.β]}, σ.t) ≥ σ.t
 5             for each scatter sentence σ of `top` )
 6      return eval(top, s)

 7  Tables(A, j, hist) : Fin A.N → ℱ_j → Bool
 8      # pre:  SplitterWins m 2R (ℓ−j) A      and   hist is the ancestors'
 9      #       connector vertices surviving into A, |hist| ≤ ℓ
10      if j = ℓ or A has no edges:                            -- leaf, O(‖A‖)
11          return BotTables(A, j)                             -- §6.4
12
13      (π, X, ctr) := cover(A, R)                             -- §6.2
14      tab := uninitialised table of size A.N × |ℱ_j|
15      for each centre u with X_u ≠ ∅:                        -- one child each
16          B := induce(A, X_u, batch(A, X_u, u, hist))        -- §6.1, D2
17          B := recordProfiles(B, ...)                        -- §6.3
18          B.own := (fun v => ctr (B.up v) = u)
19          sub := Tables(B, j+1, u :: hist ↾ B)               -- recurse
20          sc  := ( greedyScatter(B, σ.r, {w : sub[w][σ.β]}, σ.t) ≥ σ.t
21                   for each scatter sentence σ occurring in dec_j )
22          for v with B.own v:                                -- read back
23              for β ∈ ℱ_j:
24                  tab[B.up v][β] := eval(dec_j β, sub[v], sc)
25      return tab
```

### Why line 24 is correct

Fix `β ∈ ℱ_j` local of rank `(1, q_j)`, and `v` with `ctr v = u`.

```
A ⊨ β(v)
 ⟺ A[X_u] ⊨ β(v)                     β is semantically R-local and
                                      ball_R(v) ⊆ X_u                [cover]
 ⟺ B₀ ⊨ rel(β)(v)                     B₀ = A[X_u] + cluster colour   [Relativize]
 ⟺ B  ⊨ iso(rel β)(v)                 B  = B₀ with W isolated
                                           + capped distance profiles [Isolate]
 ⟺ B  ⊨ eval(dec_j β)                 locality theorem at rank (1,q_j) [Assembly]
 ⟺ eval(dec_j β, sub[v], sc)          local atoms are ℱ_{j+1} entries at v;
                                      scatter atoms are the counts of line 20
```

Every step is a lemma that already exists in the surviving math layer. The
recursion's induction hypothesis is exactly the postcondition of line 7. Note
what the chain does **not** contain: no case on whether `v ∈ W`, no readout
formula, no atomic-type index. That is D2 paying out.

### Why every table entry is written exactly once

Each `v ∈ V(A)` has one centre `ctr v = u`, and `ball_R(v) ⊆ X_u` implies
`v ∈ X_u`, so `v` occurs in child `u` with `own = true` and in no other child
with `own = true`. Total readback cost `Σ_u |X_u| ≤ D·A.N`.

### The batch (line 16)

`batch(A, S, u, hist)` returns `≤ m` vertices of `S` to isolate. It is computed
**inside `A[S]`** — shortest paths within the cluster from `u` to the surviving
history vertices, the path-maintenance strategy of the lecture notes read at
cluster scale. Cost `O(ℓ · ‖A[S]‖)`, which is the budget P1 allows. The history
survives into `S` in local names because isolation never removes a vertex (D2).

The proof obligation this creates is O1 below, and it is the one genuinely open
mathematical item in this design.

---

## §6 The five routines, with their charges

Let `N = ‖A‖` be the node's arena size.

### 6.1 `induce A S W` — `O(‖A[S]‖ + |S|)`
Rank the members of `S` to get local names; scan each `s ∈ S`'s adjacency,
keeping the neighbours that are in `S`, dropping every edge with an endpoint in
`W`; write the CSR; copy the color rows; set `up`. One pass, no search.

### 6.2 `cover A R` — `O(N^{1+δ})`, the only superlinear routine
The Grohe–Kreutzer–Siebertz §6 construction: build a transitive–fraternal
augmentation chain, read off an ordering `π`, and take `X_u := {w : u ∈
wreach_π(A, 2R, w)}`. The degree bound `wcol ≤ c·N^δ` is Lax12's subpolynomial
weak coloring numbers on a nowhere dense class, and it is uniform over
subgraphs — which is what lets it be re-applied at every node. The surviving
math layer already carries the whole chain: `Augmentation`,
`AugmentedDensity`, `OrderedCovers`, `CoverDegree`.

This routine deserves its own cost analysis; it is the one place where
`O(N^{1+δ})` is a claim rather than an inspection. Treat it as a separate
milestone (§8, step 7) and do not let it block the rest.

### 6.3 `recordProfiles B W` — `O((m + L) · ‖B‖)`
One BFS to depth `R` from each `w ∈ W` (there are `≤ m`) and from each old
color class (there are `L_j`, a constant), recording capped distances as new
color rows. The metric kernel that makes this sound is the one walk lemma of
`Isolate`:

```
dist^A(x,y) = min( dist^{A∖W}(x,y),  min_j ( p_j(x) + p_j(y) ) )
```

with `p_j(v) = dist^A(v, w_j)`. Everything the isolation rewrite reads is a
capped `p_j`.

### 6.4 `BotTables A j` — `O(‖A‖)`
In an edgeless arena every distance is `0` or `∞`, so every atom reduces to two
questions about the environment — which entries are equal, and which colors
each entry carries. A local quantifier collapses to a disjunction over its
guard set, so a one-variable local formula is decided by reading `v`'s color
row. `Lax3Proofs.BotEval` has this, including the row-interchangeability
argument that bounds an unrestricted witness search by `k + 2^L` candidates.

### 6.5 `greedyScatter A r P t` — `O(t · ‖A‖)`
```
picked := 0 ; marked := ∅
for v in order:
    if P(v) and v ∉ marked:
        picked += 1
        if picked = t: return t
        marked := marked ∪ ball_r(v)          -- one BFS, O(‖ball_r(v)‖)
return picked
```
At most `t` BFS runs, each `O(‖A‖)`, plus one scan. `t ≤ k+q` is constant. This
is D3, and it is the whole of it.

---

## §7 The cost analysis

Per node at depth `j < ℓ` with arena size `N`, summing §6:

```
        cover      Σ_u induce + profiles + batch + scatter + readback
 T_j(N) ≤ c·N^{1+δ}  +  c·Σ_u N_u          +  Σ_u T_{j+1}(N_u)
```

with, from the cover degree bound,

```
 Σ_u N_u  ≤  D(N) · N  ≤  c_D · N^{1+δ}                                   (★)
```

(each vertex lies in `≤ D` clusters, and an edge lies in `X_u` only if both its
endpoints do, so edges are covered `≤ D` times too), and `N_u ≤ N`. The leaf
charge is `T_ℓ(N) ≤ c·N`.

**Claim.** `T_j(N) ≤ (2c)^{ℓ−j+1} · N^{1+(ℓ−j+1)δ}`.

*Proof.* Downward induction on `j`. At `j = ℓ` immediate. Otherwise
```
T_j(N) ≤ c·N^{1+δ} + Σ_u (2c)^{ℓ−j}·N_u^{1+(ℓ−j)δ}
       ≤ c·N^{1+δ} + (2c)^{ℓ−j}·(Σ_u N_u)·N^{(ℓ−j)δ}          [N_u ≤ N]
       ≤ c·N^{1+δ} + (2c)^{ℓ−j}·c_D·N^{1+δ}·N^{(ℓ−j)δ}        [(★)]
       ≤ (2c)^{ℓ−j+1}·N^{1+(ℓ−j+1)δ}.                          ∎
```

At the root, `j = 0` and `δ = ε/(ℓ+1)`:

```
 T_0(n)  ≤  (2c)^{ℓ+1} · n^{1+ε}.
```

**That is the entire running-time argument: one induction and one inequality.**
It is a self-contained lemma about a recursion tree with parameters
`(c, c_D, δ, ℓ)` and no reference to graphs, formulas, or machines. It should
be the *first* thing formalized (§8 step 1), because it is the specification
every routine in §6 is then written against: hit `c·N^{1+δ}` per node with your
own arena's `N`, and you are done. Nothing downstream ever needs to know a
numeral.

Contrast with what was pruned: a downward affine recursion `Kl j ≥ a j + n·Kl
(j+1)` over ~30 named constants tied together by hypothesis slots at a
19-argument root theorem. That recursion is *correct arithmetic for the wrong
program* — its per-level coefficient is `n` precisely because the program swept
the carrier, i.e. it is P1's violation written as a recurrence.

---

## §8 The order of work

Each step is a landing boundary. Steps 1–4 are infrastructure and are
independent of each other; step 5 is the milestone.

1. **The cost-recursion lemma** of §7. Standalone, ~150 lines, no dependency on
   anything in this submission. Do it first so that every later charge has a
   target.
2. **The `Prog` combinator layer** (D7): one structure carrying machine text,
   meaning, and charge together, with one soundness lemma per combinator
   (`seq`, `ite`, `forRange`, `whileDec`) over Lax13's IMP+.
   **Prototype on one routine — bounded-depth BFS — and stop.** If the layer
   does not make BFS's cost fall out by `simp`, we learn that in a week rather
   than in a year. This is the highest-variance item in the plan and it is
   deliberately scheduled where failure is cheap.
3. **Expose the locality rewriting as a function** (O2 below).
4. **Expose the splitter strategy as a function** (O1 below).
5. **The abstract algorithm.** §5 as a Lean function over the `Arena` interface
   of §4 taken as an abstract structure of operations-with-charges; correctness
   against `DistFO.Sat` by the chain of §5; cost by §7.
   **This is the milestone, and it is a hard gate: no machine-level work
   starts until it is complete and reviewed.** It is also exactly the "high
   level pseudocode argument" this whole redesign is for — at this point the
   theorem "there is an algorithm deciding `φ` with `O(n^{1+ε})` arena
   operations" is proved, and everything after it is implementation.
6. **The `Arena` implementation** over CSR, discharging §4's charges.
7. **`cover`** (§6.2) — the largest single item, and the only one whose charge
   is a claim rather than an inspection.
8. **Compose to the headline** and discharge
   `Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`.

The gate at step 5 is the process change that matters. The pruned campaign
never had a point at which the algorithm was finished as mathematics, so every
machine-level difficulty was simultaneously an algorithm question, and neither
could be settled without the other.

---

## §9 Open questions

**O1 — Is Splitter's strategy cluster-local?** (blocks step 4, and §5 line 16.)
The algorithm computes the batch inside `A[X_u]`, using shortest paths within
the cluster. The lecture notes' path-maintenance strategy maintains paths in
the current *arena*, which here is `A[ball_{2R}(u)] ⊇ A[X_u]`. Two ways out,
and the first is much better:

  (a) prove the win for the **generalized game** in which Connector plays a
      pair `(v, S)` with `S ⊆ ball_r(v)` and the arena becomes `A[S]`. This is
      formally a stronger theorem (Connector has more moves) but it should
      follow from the ball version by `SplitterMono` at the level of the
      winning-position predicate, and its strategy reads only `A[S]`;
  (b) compute the batch in `A[ball_{2R}(u)]` and intersect with `X_u`. This
      **breaks the cost argument**: `Σ_u ‖ball_{2R}(u)‖` is not bounded by
      `D·‖A‖` — a star has `ball_1 = V` — so (b) is a non-starter and is
      recorded here only so that nobody rediscovers it.

Settle O1 by reading `SplitterWin.lean`'s actual proof before anything else in
step 4. If (a) fails, the design needs a different cover, not a different
strategy.

**O2 — Make the locality decomposition a function.** `Lax3.Locality.locality`
is stated existentially, so consumers reach it through `Classical.choose`; the
pruned layer's formula tables were therefore noncomputable, which in turn made
their cost function noncomputable and unguardable. The source note's proof *is*
a syntactic rewriting and says so explicitly ("this boolean combination can be
effectively computed"), and `Assembly` constructs it. Exposing
`loc : DistFO L k → BC (…)` with a soundness lemma proofs-side costs a
refactor, not new mathematics, and buys three things: `ℱ_j` becomes computable
(D5), the schedule can be `#eval`'d and sanity-checked at small `q`, and O3
becomes provable.

Note the concept surface need not change: `Lax3.Locality.locality` stays the
endorsed existential, and `loc` is a proofs-side function that implies it. The
same applies to O1, where the concept deliberately "quantifies the strategy
away". Both of those choices were right for the *statement* and wrong as the
only thing available to a *consumer*; the fix is to add the function
proofs-side, not to change what is endorsed.

**O3 — Can the `pu` color family be dropped?** The isolation rewrite carries
two profile families: distances to the batch (`pd`) and distances to the old
color classes (`pu`). `pu` exists only to translate the *unary* distance atom
`dist(x, Y) < r`. If `loc` (O2) provably never introduces a unary distance
atom, then no formula in any `ℱ_j` has one, `pu` disappears, and the palette
grows additively (`L_{j+1} = L_j + 1 + (m+1)(R+1)`) instead of multiplicatively
(`L_{j+1} ≈ L_j·(R+2) + …`), i.e. `L_ℓ` drops from a tower of height `ℓ` to
`O(ℓ·m·R)`. Recorded as refuted-as-stated in the pruned layer *because the
existential form of `locality` admits unary distance atoms* — which is exactly
what O2 removes. Re-open it after O2, not before.

**O4 — Is there an intermediate machine layer?** Steps 6–8 are where the
pruned campaign spent ~100k lines. Before starting them, check whether an
"abstract RAM with unit-cost arrays", formalized once and mapped to Lax13's
word RAM by a single generic simulation theorem, cuts that work materially —
and whether `ram-linear-time` (Lax11, Courcelle on the same machine) already
has such a layer to reuse. This factors the headline; it does not weaken it.

---

## §10 What this design owes to the pruned layer

Three facts, and nothing else:

1. The cost model of the source is **per cluster**, not per carrier: GKS charge
   each cluster `O(|V(G_X)| + |E(G_X)|)` and the whole `n^{1+ε}` proof rests on
   `Σ_X n_X ≤ n^{1+δ}`. Both of the passes the pruned campaign disputed exist
   in the source at the same frequency — once per cluster. This is P1.
2. The isolation variant genuinely eliminates GKS §8's `θ`-variant formula
   family and readout formulas, with no residue. This is D2, and it was
   verified against the source before it was implemented.
3. `n^{1+ε}` at `ε = ½` clears at every measured constant with 10⁴–10⁶ of
   headroom on every row. **The algorithm is not a dead end; the gap was shape,
   not headroom.** That is why this document redesigns the shape and changes
   nothing about the mathematics.
