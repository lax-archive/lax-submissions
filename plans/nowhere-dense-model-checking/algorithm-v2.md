# ND-MC: the algorithm, rethought from first principles

**Rev 5, 2026-08-17.** Status: **design closed; execution has begun.** The
abstract core is unshaken by three adversarial audits, the constants are
slackened rather than tightened, and the external import that Rev 4 called the
critical path is neither external nor blocking.

> **Next milestone: `/ndmc`.** Design work on this document is finished. The
> operational expansion is `execution-plan.md` (§8 as thirteen leaves, E0–E13,
> each with its owned file, dependencies, source pin and hazards) and
> `execution-ledger.md` (where each stands). Amend this document when a leaf
> proves it wrong — do not re-audit it.
>
> **Two things changed on the day execution opened, and both shrink the plan.**
>
> *§8 step 0b is not blocked.* GKS's bracket resolves to arXiv math/0508324v2,
> now checked in at `references/nodm05/`; its own Lemma 4.1 defers once more, to
> Lemma 6.1 of arXiv math/0508323v1 at `references/nodm05i/`, where it is
> **proved in full**. The deferral chain is four links and terminates in a
> proof. Rev 4 wrote that this "cannot be formalized from any document this
> project holds" and that Jan should be asked for the paper; it took one
> bibliography lookup. What none of the four papers states — and what E0
> therefore owes — is the **nowhere-dense instantiation**: NOdM's Theorem 4.3 is
> a *bounded expansion* statement in time *O(n)*, while GKS cite it for
> *nowhere dense* with `Δ⁻ ≤ n^ε` in `f(r,ε)·n^{1+ε}`.
>
> *§7 stops being tightened* (⟨C⟩ below, Jan's call). `δ = ε/(ℓ+2)` and a
> chosen base constant `K`, in place of Rev 4's `ε/(ℓ+1)` and the forced
> `(2c)^{L+1}` shape that manufactured `c ≥ 6`. The headline is unchanged. The
> cover's honest exponent is `1+2δ`, which Rev 4 quoted in §6.2 and charged as
> `1+δ` in §4 without reconciling the two.

Rev 1 was written in one pass after pruning the algorithmic layer. Two
adversarial audits followed, 20 agents in total: one on the evidence the prune
rested on (`pruned-algorithmic-layer.md` §2 Rev 2 records its outcome), one on
this document. **Rev 3 is the repair.** Findings that survived their verifier
are folded in and marked ⟨A⟩; where the repair is known it is in the text, and
where it is not the claim is withdrawn rather than softened.

The audit's summary judgement is worth stating up front, because it is neither
"fine" nor "start over": *the abstract core — §5's recursion, §7's recurrence,
D2–D4 — is sound modulo specific repairs; but one previously unexamined issue
is fatal as written, and it is not in the algorithm. It is the seam between the
algorithm and the endorsed axiom's word length.* See §11 — which Jan resolved
the same day by squaring the concept's word-length side condition, the one
change in this revision that touches the endorsed surface.

The purpose of this document is to be the thing the formalization is written
*against*. If a future Lean file cannot be traced back to a numbered line or a
numbered decision here, that is a defect in this document, not a licence to
improvise.

---

## §0 The one-paragraph algorithm

Evaluate the sentence by descending the isolation splitter game tree. At each
node the current *arena* is covered by clusters of bounded radius and small
degree; each cluster becomes one child, obtained by restricting the arena to
the cluster, recording the distances to Splitter's batch as colors, and then
isolating that batch. The formula each child must answer is determined by the
parent's formula alone, by a purely syntactic rewrite — so the whole formula
schedule is a compile-time constant. ⟨B⟩ The play cannot record more than `ℓ`
rounds, so by depth `ℓ` the arena is edgeless and every formula is decided by
reading color rows. *Rev 3 still said here "Splitter wins in `ℓ` rounds, so at
depth `ℓ` the arena is edgeless" — verbatim the inference §9 records as
underivable and §5 was patched to avoid. The depth bound is
`reachedR_length_lt`, which bounds the play's length without naming a batch.*
Information then flows back up: each child returns a table of truth values, one
bit per (vertex, tabled formula), and the parent's table is a boolean
combination of its children's entries and of finitely many *scatter counts* —
sizes of greedy maximal scattered sets, capped at a constant. The top level is
nothing but such counts.

Two traversals of one tree: **down** builds arenas, **up** fills tables.

---

## §1 What went wrong last time

> Every node of the recursion allocated and swept arrays of length `n`, while
> the cost argument requires every node's work to be proportional to *its own*
> arena.

⟨A⟩ **Rev 1's arithmetic here was wrong twice and is replaced.** It claimed
`n^δ` branching; `n^δ` is the cover *degree* — how many clusters contain a
given vertex — and bounds nothing about fan-out, which is up to `|V(A)|`
(`NeighborhoodCovers.lean:50-57` bounds only `{u | v ∈ X u}.ncard`, and the
deleted layer's `Refine.MassAlive.block_nonempty` proved no cover block is ever
empty, so every level ran exactly `n` turns). It then wrote the conclusion as
`Θ(n^{1+ℓδ+1})`, which under its own node count would have proved the *old*
design met its target.

The correct statement needs neither depth nor `δ`:

> With `S_j` the total arena weight at depth `j`, `(★)` gives
> `S_{j+1} ≤ c_D·N^δ·S_j`, so `S_j ≤ c_D^j·n^{1+jδ}` and the node count at
> depth `j` is at most that. **At depth 1 alone there are `Θ(n)` nodes.** So
> `Θ(n)` work per node is already `Ω(n²)`, and `Θ(n²)` per node — which is what
> the deleted cover phase actually cost — is `Ω(n³)`.

**Invariant P1, the invariant this design is organised around.** ⟨A⟩ Rev 1's
second sentence was strictly too strong: it forbade the very `N^{1+δ}` that §7
budgets, so the gate would have rejected §6.2 first.

> **P1a.** Below the root, no array, loop bound, or quantifier ranges over the
> *input* vertex set. Every loop a node runs is over its own vertices, its own
> edges, its own cover output, or a constant.
>
> **P1b.** Every array a node allocates has length `O(‖A‖^{1+δ})` for *its own*
> arena `A`, and all but the cover output has length `O(‖A‖)`.

P1a is checkable by reading a program. It is not a theorem discovered at the
end. Anything that violates it is rejected at review, whatever its cost lemma
says. P1b is the space counterpart, and §11 is what makes it affordable: under
the concept's original linear word-length side condition it was unsatisfiable.

---

## §2 Standing decisions

Each decision names the alternative it beats. ⟨A⟩ Rev 1 claimed this of all
seven and delivered it for three; D4–D7 are re-argued below.

**D1 — Materialize, do not view.** A child arena is a freshly built compact
structure with its own vertex numbering `0 … N−1`, not a (parent, mask) pair
interpreted lazily.

*Alternative:* represent a child as a filter over the parent, copying nothing.
*Why it loses:* adjacency iteration then costs the **parent's** degree at
*every access*, so a vertex of huge parent-degree in a tiny cluster is paid for
again at every level — `Θ(deg_root)` per access at depth `ℓ`. ⟨A⟩ The honest
statement of D1's advantage is **once per child, not once per access**:
materializing also pays the parent's degree (see §6.1), but pays it once.

⟨A⟩ *Cost of D1, previously hidden:* the lemmas the correctness chain is built
on all keep the carrier (`deleteVerts` isolates, it does not remove —
`Lax12/UniformQuasiWideness.lean:54-57`, and `DistFO.lean:119-127` says so),
while D1 renumbers. That gap is a **missing lemma**, not bookkeeping: see §5's
step 3′ and §8 step 4a.

⟨A⟩ *Memory, corrected.* Rev 1 said "at most `ℓ+1` arenas are live, each of
size at most `n`". That omitted the cover output, which a node cannot release
until its whole subtree finishes, so peak live memory is `Θ(n^{1+δ})`,
dominated by the root's cover. That is the quantity §11 is about, and the
squared side condition is what makes it addressable.

**D2 — Isolation, not deletion. ⟨A⟩ But *not* fused with the restriction.**
Splitter's move keeps the batch's vertices and drops their incident edges.

*Why isolation:* with deletion, a vertex can leave the arena, so the formula
rewrite must case-split on whether a variable lands on a removed vertex — GKS
§8's atomic-type-indexed family `φ^θ` and their readout formulas `ξ_j`. With
isolation the carrier is untouched by Splitter's move, equality needs no
readout, and **one** uniform rewrite `iso` serves every tuple with no side
condition. Both pieces of GKS machinery vanish with no residue.

⟨A⟩ **Rev 1 additionally fused restriction and isolation into one `induce(A,
S, W)`, and that is unsound.** `Isolate.sat_iso` (`Isolate.lean:751-757`)
requires its profile colors to hold `WithinDist **A** a v (w j)` — distances in
the arena *before* the batch is isolated; that is the whole content of the walk
kernel at `Isolate.lean:536`. Measuring them in the fused result gives `∅` for
every `a ≥ 1`, because every batch vertex is isolated there by construction, so
`hpd` is unsatisfiable and the rewrite is unsound rather than lossy. The node
therefore performs **one pass and one filter**:

```
B₀ := restrict(A, X_u)          -- induced arena on the cluster, carrier kept
B₀ := recordProfiles(B₀, W)     -- distances measured HERE, in B₀
B  := isolate(B₀, W)            -- linear edge filter
```

Cost is unchanged. Only D2's "one structural operation per child" slogan dies.

⟨A⟩ The profile slots are **cumulative** (`≤ a`, not `= a`) — that is what
`sat_iso`'s `hpd`/`hpu` say, and Rev 1's prose said "exact distance". And the
batch must be **padded** to exactly `m` entries by repetition, so the palette
is a function of depth alone; `iso` assumes no injectivity of the batch
enumeration, so padding is invisible to it. (This was fact 8 of the prune note
and Rev 1 failed to carry it.)

**D3 — Greedy scatter, never distance-`r` independent set.** Scatter sentences
are Dreier–Toruńczyk's *weak* form: `A ⊨ scatter(r, β, t)` iff the fixed
inclusion-wise maximal `r`-scattered subset of `{a : A ⊨ β(a)}` has size `≥ t`,
under the **greedy choice** of that set.

*Alternative it beats:* the Gaifman/GKS reading, where a scatter sentence
asserts *existence* of an `r`-scattered set of size `t` — at least as hard as
distance-`r` independent set, needing a separate algorithm (GKS Thm 5.1).
Under the greedy reading it is one pass, and since `t ≤ k+q` is constant the
process may **stop after `t` picks**. ⟨A⟩ Guard `t = 0` explicitly: the stop
test fires only after an increment, so at `t = 0` the routine runs the full
greedy — `Θ(N)` BFS calls, `Θ(N²)` at that node, silently, with a correct
answer. Nothing in `ScatterSentences.lean:193` rules `t = 0` out.

⟨A⟩ The greedy choice is order-dependent by definition (`greedyChoice`
recurses on `Fin n`'s canonical order).

⟨B⟩ **Rev 3 drew two consequences from that and both are phantom.** It made
§6.1's "`S` given sorted" load-bearing *for correctness*, and made the
compaction lemma of §5 step 3′ an *order-preserving* one with a *dead-vertex
correction*. Neither is needed, and the reason is inside Rev 3's own sentence:
step 3′ says the compaction "must come **before** `locality`", and that is
exactly what removes the rest. Step 3′ transports `DistFO.Sat`, which has no
order-sensitive constructor, so *any* bijection `Fin N ≃ X` serves and
monotonicity of `up` buys nothing semantic. Scatter values enter only through
`locality`'s output (`Locality.lean:104-110`), applied at `B`, and the program
computes them at `B` too (§5 lines 25-26); `ScatterSentence.Sat` is evaluated
per graph on that graph's own carrier (`ScatterSentences.lean:180-184`) and
`greedySet` recurses on that carrier's own `Fin N` order (`:126-133`). **No
greedy value ever crosses the compaction boundary, so nothing needs
correcting.** Sortedness in §6.1 is a CSR-build cost matter, not correctness.
This deletes the only two clauses that made §8 step 4a hard.

**D4 — One-variable tables, everywhere.** The only semantic objects the
recursion computes are bits `tab[v][β]` for `β` a one-variable local formula.
No `k`-ary type, no tuple table.

*Alternative it beats:* GKS-style tables of atomic `q`-types of tuples, which
is what the deleted layer's `FormulaTables` grew out of and what makes the
palette a function of the batch rather than of the depth.
*Why one variable is available:* a sentence's decomposition at rank `(0,q)`
gives local *sentences* (constants, L1) and scatter sentences, whose `β` has
one free variable (`ScatterSentences.lean:175`); decomposing a one-variable
formula gives one-variable local atoms and again such scatter sentences. And
the endorsed `locality` pins its rank's first argument to the *arity*
(`Locality.lean:103-105`), so below the root it can only ever be invoked at
`k = 1`.

**D5 — The formula schedule depends only on `(φ, ε, C)`,** never on the input
graph.

*Alternative it beats:* selecting formulas at runtime from the graph, which is
what forces a per-instance palette.
*Requirement:* the rewrites must be **functions**, not existentials. `rel` and
`iso` already are. The locality decomposition is not — see O2.
⟨A⟩ Rev 1 said the schedule is "computed once, before the graph is read".
Withdrawn: `ℓ`, `m` come from `splitterWins_of_nowhereDense`'s existential and
`c_D` from Lax12's, so the schedule is `Classical.choose`-dependent whatever O2
does, and `#eval`-ability is available only at *chosen* concrete `(ℓ, m, R)`.
This is harmless for the theorem — the program is existentially quantified —
but the payoff Rev 1 claimed for O2 was overstated.

**D6 — A node reads only its own arrays, plus a bounded downward channel that
`restrict` maintains.** ⟨A⟩ Rev 1's D6 was "an arena, a round budget, a
constant-size history, and nothing else", unargued, and its own §9 then
declared it broken. Restated:

*Alternative it beats:* letting a node reach into ancestor arrays on demand,
which is what the deleted `ancestorStep` did — one carrier-wide BFS per
ancestor per turn, a P1a violation and a principal source of the old cost.
*What the channel must carry:* per earlier round, enough to certify
`SplitterWinRec.ReachedR.step`'s `hwalk` **in that round's own arena** — see
§5's batch and O1.

⟨B⟩ **Rev 3 said "a recorded parent-pointer path of `≤ 2R` vertices per round
suffices, so the channel is `O(ℓ·R)`, still constant". That is wrong, and it is
the finding four independent auditors converged on.** Two things are being
confused, and they are mutually exclusive:

- `ReachedR.step`'s `hwalk` (`SplitterWinRec.lean:195-198`) is quantified over
  **every** `e ∈ rounds` and demands a walk in `e.arena` from `e.vtx` to *the
  new connector* — a vertex that is not known when round `e` is played, and is
  a different vertex at every descendant. So the round-`e` datum must answer
  "path from `e.vtx` to `x`" for arbitrary `x` in the whole subtree below `e`.
  That is arena-proportional data, not one path.
- Concatenation cannot rescue it: `path(e.vtx→u') ++ path(u'→u'')` has length
  up to `4R > 2R`, and no fresh BFS from `e.vtx` is available later because
  `e.vtx` is edge-isolated in every later arena (`isolatedR`, `:251-260`).
- And a *parent array* cannot be carried either, because restriction destroys
  parent chains: if the recorded chain is `u_e — a — b — c` and an intermediate
  round isolates `b` while `a` and `c` stay joined through another vertex, then
  `b ∉ X''` and walking parents back from `c` stops at `b`, missing `a`. But
  `reachedR_descend`'s `hbatch` (`:533-538`) proves `batchR = W` *exactly*, so a
  missing element makes the arena the program built differ from the game's, and
  the round is not a round of the game. Re-entry is not a corner case; it is
  the generic effect of ancestor isolation on a path recorded before it.

**The channel, restated.** For each ancestor round `e` and each vertex `x` of
the current arena, store the `≤ 2R+1` names of `support(p_{e.vtx → x})`. So the
channel is `O(ℓ·R)` **per vertex**, i.e. `O(ℓ·R·‖A‖)` per node. Filtering at
`restrict` is sound because carriers are nested: `(S ∩ X₁) ∩ X₂ = S ∩ X₂` for
`X₂ ⊆ X₁`, so a support list filtered to the child carrier is still the support
of a walk of the ancestor's arena. Line 19's batch is then an `O(ℓ·R)` lookup.

*This costs nothing that matters and it is P1-legal.* The channel is
own-arena-proportional (P1a and P1b hold), the `restrict` copy costs
`O(ℓ·R·|S|)`, which aggregates over a node's children to
`O(ℓ·R·c_D·‖A‖^{1+δ})` and is absorbed by the cover term exactly as the
`Σ deg` column is (§4), and §11's peak grows by `Θ(ℓ·R·n)`, affordable under the
squared side condition. What dies is only D6's slogan "constant-size channel",
§4's `hist : List Path` type, and the omission of a `hist` term from
`restrict`'s charge — all three corrected below.

**D7 — Cost is written, not discovered.** Every routine is written in a layer
that produces its machine text, its meaning, and its step count *together*.

*Alternative it beats:* three hand-synchronized artifacts, with the recorded
hazard *"the program's cost fell and the stated budget did not."*
⟨A⟩ **The layer already exists and is already a pinned dependency.** Rev 1
proposed building it. `nowhere-dense-model-checking/proofs/lakefile.toml`
requires `Lax13Proofs` at rev `d35ba57`, which contains `Lax13Proofs/Refine/` —
127 files: a cost-carrying NREST monad with time and data refinement, Sepref
with amortization and heap allocation, an IR with weakest-preconditions and a
separation solver, `Iicf` collections, `Asymptotics/Recurrences`, and a
`Codegen` that lands on the endorsed boundary
(`Refine/Codegen/Cash.lean:407-419` concludes `ComputesInTime`). D7 is
therefore **"instantiate the landed tower"**, not "build a combinator layer",
and §8 is re-scoped accordingly.

---

## §3 Constants, fixed before the input is read

Given the class `C`, the sentence `φ`, and `ε > 0`:

```
q  := qr(φ)                              -- top quantifier rank
R  := ρ⁻(0, q) = 9^{q(q+1)}              -- the global radius cap
N, s := Lax12 UQW witnesses of C at radius 2R    -- ⟨B⟩ via exists_roundBudget
ℓ  := N (2s + 2)                         -- ⟨B⟩ the round budget, NOT an axiom's ℓ
m  := ℓ · (2R + 1)                       -- ⟨B⟩ the batch width, and it is proved
δ  := ε / (ℓ + 2)                        -- ⟨C⟩ ℓ+2, not ℓ+1; the cover costs 2δ
c_D  from Lax12's subpolynomial wcol;  D(N) := ⌈c_D · N^δ⌉
c  := max(every routine's constant, c_D)             -- ⟨C⟩ no numeric floor
a  := c + (2 + ℓ·R)·c_D                  -- ⟨C⟩ cover + restrict/hist aggregate
A  := a + c·(c_D + 1)                    -- ⟨C⟩ ALL of a node's non-recursive charge
K  := c_D + 1 + A                        -- ⟨C⟩ chosen, not constrained; see §7
```

⟨B⟩ **`ℓ` and `m` were mis-sourced, and the repair is a repin, not new
mathematics.** Rev 3 took both from `NowhereDenseSplitter.splitterWins_of_
nowhereDense` (`concepts/Lax3/NowhereDenseSplitter.lean:57-60`), a bare
`∃ ℓ m, ∀ n G, C n G → SplitterWins m r ℓ G`. But §9's O1 repair replaced the
precondition with `ReachedR`, and **`ReachedR` consumes neither number** —
`SplitterWinRec.lean:54-56` says in as many words that *"No size clause is
imposed on a recorded round"*. So the axiom's pair was consumed by nothing,
while `ℓ` drives `δ`, the schedule `ℱ_0 … ℱ_ℓ`, §8 step 4b's frame count and the
headline `K^{ℓ+1}`. Worse, had the axiom's `ℓ` been smaller than `N(2s+2)`,
§5's leaf test would have called `BotTables` on an arena with edges and §6.4's
premise would fail *silently*. The numbers with proofs behind them are:

- `ℓ = N(2s+2)` — `UqwInstantiation.exists_roundBudget C hC R` (`:96-100`)
  returns exactly `∃ N s ℓ, ℓ = N (2s+2) ∧ …`, and the depth bound that uses it
  is `SplitterWinRec.reachedR_length_lt` (`:561-567`), concluding
  `rounds.length < N (2s+2)`. Note `exists_roundBudget` instantiates the UQW at
  `2 * cap`, so `cap := R` is the game radius `2R`.
- `m = ℓ·(2R+1)` — `SplitterWinRec.splitterWins_of_reachedR` (`:459-465`)
  concludes `SplitterWins (N (2s+2) * (r+1)) r b A`.

**Consequence: the batch of §5 line 19 is legal, and it is not an invention.**
`SplitterWin.genSet` (`:192-194`) is literally `genSet r (e :: rest) v =
pathSet e.2 r e.1 v ∪ genSet r rest v` — the connector plus one recorded path
per earlier round, which is §5 line 19's set — and `genSet_ncard_le` (`:217-218`)
proves `≤ 1 + rounds.length·(r+1)`. At depth `j ≤ ℓ−1` that is
`|W| ≤ 1 + (ℓ−1)(2R+1) ≤ ℓ(2R+1) = m`. Rev 3 worried this batch might be
illegal; under the corrected `m` it is legal, by a landed lemma.

⟨B⟩ **`R` is the radius; the augmentation chain's depth is a different number
and the document never named it.** `CoverDegree.exists_cover_degree` takes `rc`
(cover radius), `R` (augmentation *rounds*) and `t` with `3t ≤ R`,
`2·rc ≤ 2^t` (`CoverDegree.lean:366-370`). Passing `R := rc := 9^{q(q+1)}`
satisfies both side conditions, but the returned constant is
`6·(3·max c₀ 0 + 5)^(2·16^R)`, so instantiating the *round* parameter at the
*radius* costs a two-level tower for nothing. The chain depth needed is
`≈ 3⌈log₂(4·rc)⌉`; GKS have the same slack and flag it (tex:1369-1372: a
`⌈log_{3/2} r⌉+1`-augmentation would suffice). Name the depth separately.

⟨A⟩ **Standing remark: constants are free, `n^δ` is not.** Every constant above
is fixed before `n` is read, and against the endorsed axiom a larger `c` both
loosens the time bound and *shrinks* the admissible input set
(⟨B⟩ `ModelChecking.lean:115` for the axiom and `:122` for the side condition;
Rev 3 cited `:81/84`, which are docstring lines), so `R = 9^{q(q+1)}`, `L_ℓ`,
`K^{ℓ+1}` and the
`ℓ+1` live frames are all absorbable. **The only quantity in the entire design
that is neither constant nor linear in the input is `D(N)`, and it enters in
exactly one place: `cover`.** Every space failure (§11) and the whole of §7's
`δ`-machinery trace to that one routine. The next auditor should look there
first.

**L0 (radius cap).** Every distance-atom radius, local-guard radius and scatter
radius occurring anywhere in the run is `≤ R`.

⟨A⟩ *Rev 1's reason was wrong; the cap is right and in fact generous (the true
supremum over the run is `9^{q²}`).* The run does **not** traverse the
antidiagonal `(0,q) → (1,q−1) → … → (q,0)`. The only ranks that occur are
`(0,q)` at the root and the **fixed** rank `(1, q−1)` at every node below it:
`locality` pins the first coordinate to the arity, which is 1 by D4; a scatter
sentence's `β` is natively at `(1+i, q−1−i)` and is traded straight back to
`(1, q−1)` by `ScatterFml.drank_succ_pred_of_drank` composed with
`SyntaxLemmas.DRank.antidiagonal`; and `rel`, `iso` preserve rank exactly
(`Relativize.drank_rel`, `Isolate.drank_iso`). So `ρ⁻(1,q−1) = 9^{q²−1} ≤
ρ⁻(0,q) = R`, and the root's own radii are `≤ ρ⁻(0,q)` by
`ScatterFml.r_le_rhoMinus_of_drank`.

This matters concretely: read Rev 1's way, `ℱ_j` would sit at rank `(j, q−j)`
and the schedule would be exhausted at depth `q`, while the recursion depth is
`ℓ` — the splitter round count at radius `2R`, with no relation to `q` and
normally `≫ q`. A formalizer following Rev 1's L0 would build a schedule that
runs out.

**L1 (local sentences are constants).** A local `DistFO` formula with no free
variables has the same truth value in every colored graph, computable from its
syntax: with no variables in scope there are no atoms, and `exL r g ψ` at arity
`0` has `g ⊆ ∅`, so it ranges over the vertices within `r` of nothing and is
false. ⟨A⟩ Verified against `DistFO.lean`'s constructors and `Sat`, all four
sub-claims holding.

*Consequence.* The top-level decomposition of `φ` is, after discarding
constants, a boolean combination **of scatter sentences alone**. The whole
algorithm is: compute finitely many capped greedy-scatter counts of
one-variable local formulas, and combine them.

---

## §4 The data structure

```
structure Arena where
  N    : ℕ                    -- vertices, named 0 … N−1
  adj  : CSR over N           -- edges of this arena;  M := ‖adj‖/2
  L    : ℕ                    -- number of colors
  col  : Fin N → Fin L → Bool -- color rows
  up   : Fin N → ℕ            -- this vertex's name in the parent (monotone)
  own  : Fin N → Bool         -- "this node answers for this vertex"
  hist : Fin N → Fin ℓ → List (Fin N)
       -- ⟨B⟩ D6's channel, CORRECTED: per vertex and per ancestor round,
       -- the ≤ 2R+1 support names of that round's walk to this vertex.
       -- NOT `List Path`: see D6 for why one path per round cannot work.

‖A‖ := A.N + A.M
```

`up` is **monotone** — ⟨B⟩ for the one-pass CSR construction of §6.1, not for
any semantic reason. *Rev 3 said it was load-bearing because the greedy scatter
choice is order-defined and the compaction must preserve it; D3 above records
why that is phantom.*

| operation | result | charge |
|---|---|---|
| `restrict A S` | the arena on `S ⊆ V(A)` with the edges of `A[S]`, `up` set to the `A`-names, `hist` filtered | ⟨B⟩ `O(Σ_{s∈S} deg_A(s) + \|S\|·(L + ℓ·R))` |
| `isolate B W` | drop the edges incident to `W` | `O(‖B‖)` |
| `bfs A v d` | the `≤ d`-ball of `v` with distances, `d ≤ 2R` | `O(‖ball_d(v)‖)` |
| `bfsSupports A v d` | ⟨B⟩ one BFS from `v` materialising the `≤ d+1` support names at every reached vertex | `O(d·‖ball_d(v)‖)` |
| `recordProfiles B W` | ⟨B⟩ §6.3 — cumulative capped distance rows for the batch and colour classes | `O((m + L)·‖B‖·(R+1))` |
| `cover A r` | ordering `π`, clusters `X_u`, assignment `ctr` | ⟨C⟩ `O(‖A‖^{1+2δ})` — §6.2, §8 step 0b, §11 |
| `greedyScatter A r P t` | `min(t, size of the greedy maximal r-scattered subset of P)` | `O(t·‖A‖)` |
| `BotTables A j` | ⟨B⟩ §6.4 — the leaf's table, read off colour rows | `O(‖A‖)` |

⟨B⟩ *Rev 3's table omitted `recordProfiles` — the routine the D2 unfusing
created, and the one carrying the tower-sized `L` — and `BotTables`, while
listing a `pushColor` that nothing in §5 calls. The table is the document's
inventory of charged operations; §7 cannot be checked against a pseudocode it
does not cover.*

⟨A⟩ **The `restrict` charge is not `O(‖A[S]‖ + |S|)`, and no data structure
achieves that.** Scanning `s`'s CSR row costs `deg_A(s)`, not `deg_{A[S]}(s)`.
Refutation inside the intended regime: `A = K_{3,n−3}` (nowhere dense), `S` the
3-side. Then `‖A[S]‖ + |S| = 6`, a constant, while the build reads
`3(n−3) = Θ(n)` entries; and certifying the absent edges any other way costs
`|S|²` binary searches. **The aggregate survives, which is why this is a
repair and not a refutation:**

```
Σ_u Σ_{s∈X_u} deg_A(s) = Σ_{s} deg_A(s)·|{u : s ∈ X_u}| ≤ D·2A.M ≤ 2c_D·‖A‖^{1+δ}
```

so the whole children-building column is absorbed by the cover term in §7.

⟨A⟩ **`cover` must also return `ctr`, and nothing in the surviving layer
produces it.** `IsNeighborhoodCover.ball_subset` is an existential
(`NeighborhoodCovers.lean:53`); §6.2's `X_u := {w : u ∈ wreach_π(A,2R,w)}`
never mentions `ctr`; `OrderedCovers.lean` has no occurrence of it. Use
`ctr v := π-min(wreach_π(A,R,v))`, computed from the same wreach fibres the
cover already builds.

⟨B⟩ **Two corrections to Rev 3's account of this, both in the reader's favour.**

*It is not a repair of GKS; it is GKS.* Rev 3 attributed `ctr v := π-min(ball_R(v))`
to GKS and rejected it at `Θ(n²)` on a star. That sum appears nowhere in GKS:
their ball-minimum occurs only in the *existence* proof (tex:1444-1451), which
is a proof, not an algorithm. Their algorithm is the Remark at tex:1522-1538 —
*"we associate with `v` the set `X_{2r}[G,<,u]` for the `<`-minimal `u` such
that `v ∈ N_r^{G∖S(u)}(u)` … As the sets are computed in increasing order, this
can be done at no extra cost"* — and by their own Claim (tex:1468-1471)
`X_r[G,<,u] = N_r^{G∖S(u)}(u)`, so that `u` **is** `π-min(wreach_π(A,R,v))`.
Rev 3 reinvented the source in wreach language and then argued with it.

*And the owed identity is near-free, so §8 step 6's estimate is inflated.*
Write `u* := π-min(ball_R(v))`. (1) `wreach ⊆ ball`, immediate from
`mem_wreach_iff`. (2) `u* ∈ wreach_R(π,v)`: any walk `v→u*` of length `≤ R` has
every support vertex within `R` of `v`, hence in `ball_R(v)`, hence `π u* ≤ π y`
by minimality of `u*` — which is exactly `wreach`'s third conjunct. So the two
`π`-minima coincide, and `ball_R(v) ⊆ X_{ctr v}` is GKS tex:1443 transcribed:
roughly six lines, not a design risk.

---

## §5 The pseudocode

```
── compile time; depends on (C, φ, ε) only ────────────────────────────────
 0  q, R, ℓ, m, δ  as in §3
 0  ℱ_0 … ℱ_ℓ      : one-variable local formulas, all at rank (1, q−1)   (L0)
 0  dec_j          : for β ∈ ℱ_j, a boolean combination over
 0                   (local atoms ⊆ ℱ_{j+1}) ⊎ (scatter sentences over ℱ_{j+1})
 0  top            : a boolean combination over scatter sentences over ℱ_0  (L1)

── run time ───────────────────────────────────────────────────────────────
 1  MC(G):
 2      A := arena of G;  own ≡ true;  up := id;  hist := []
 3      T := Tables(A, 0)
 4      s := ( greedyScatter(A, σ.r, {v : T[v][σ.β]}, σ.t) ≥ σ.t
 5             for each scatter sentence σ of `top` )
 6      return eval(top, s)

 7  Tables(A, j) : Fin A.N → ℱ_j → Bool
 8      # pre:  ReachedR 2R G rounds A  — a record of the play so far     ⟨A⟩
 9      #       (NOT `SplitterWins m 2R (ℓ−j) A`; see O1)
10      if j = ℓ or A has no edges:                            -- leaf, O(‖A‖)
11          return BotTables(A, j)                             -- §6.4
12
13      (π, X, ctr) := cover(A, R)                             -- §6.2, §11
14      tab := uninitialised table of size A.N × |ℱ_j|
15      for each centre u with X_u ≠ ∅:                        -- one child each
16          B₀ := restrict(A, X_u)                             -- §6.1, filters hist
17          S  := bfsSupports(B₀, u, 2R)                       -- ⟨B⟩ ONE BFS; at each w,
18                                                             --  the ≤2R+1 support names
18                                                             --  of the u→w walk
19          W  := pad_m( {u} ∪ ⋃_{e ∈ rounds} B₀.hist[u][e] )  -- ⟨B⟩ = genSet, |W| ≤ m
20          B₀ := recordProfiles(B₀, W)                        -- §6.3, BEFORE isolating
21          B  := isolate(B₀, W)                               -- ⟨A⟩ D2, unfused
22          B.own  := (fun v => ctr (B.up v) = u)
23          B.hist := fun w e => if e = now then S[w]          -- ⟨B⟩ per vertex, not
23                               else B₀.hist[w][e]            --  one path per round
24          sub := Tables(B, j+1)                              -- recurse
25          sc  := ( greedyScatter(B, σ.r, {w : sub[w][σ.β]}, σ.t) ≥ σ.t
26                   for each scatter sentence σ occurring in dec_j )
27          for v with B.own v:                                -- read back
28              for β ∈ ℱ_j:  tab[B.up v][β] := eval(dec_j β, sub[v], sc)
29      return tab
```

### The batch (lines 17–19) — ⟨A⟩ Rev 1's version was *vacuous*

Rev 1 computed the batch as "shortest paths within the cluster from `u` to the
surviving history vertices". **That set is always `{u}`.** Isolation is
permanent (`SplitterWinRec.lean:251-252` `isolatedR`: every vertex of an earlier
round's batch has no incident edge in the current arena) and each round's
connector is in its own batch (`:238` `selfR`), so every history vertex is
edge-isolated in `A`, hence in `A[X_u]`, and a BFS from `u` reaches none of
them. The file even ships the worked witness at `:642`/`:648`.

What the game needs is a walk in the **ancestor's own arena**
(`SplitterWinRec.lean:197-198`: `∃ p : e.arena.Walk e.vtx v, p.length ≤ r`),
searched *before* that ancestor's connector was isolated. The deleted driver
did exactly that, with one fresh BFS per ancestor per turn — a P1a violation
and a principal source of its cost.

**The repair, and it is free: wreach clusters are path-closed.** With
`X_u = {w | u ∈ wreach_π(A, 2R, w)}` (`OrderedCovers.lean:106`), take
`w ∈ X_u` and a witnessing walk `p : A.Walk w u` of length `≤ 2R` all of whose
support is `π`-above `u` (`CoverConstruction.lean:34-37`). For any
`z ∈ p.support`, `p.dropUntil z` is a walk `z → u` with support `⊆ p.support`
and length `≤ 2R`, so its `π`-minimality clause holds verbatim and `z ∈ X_u`.
Hence `p.support ⊆ X_u`: **`p` is a walk of `A[X_u]`, so
`dist_{A[X_u]}(u, w) ≤ 2R` for every `w ∈ X_u`.** Since the game radius is
exactly `2R`, one parent-recording BFS from `u` inside `A[X_u]` — cost
`O(‖A[X_u]‖)`, so `Σ_u` within budget — supplies a walk of length `≤ 2R` from
`u` to *every* vertex of every descendant carrier, in the arena of `u`'s own
round. Record it at line 17, carry it down at line 23, and at a descendant the
batch is the connector plus the recorded ancestor paths intersected with the
descendant's carrier.

This needs a **fourth guarantee on `cover`**: *for every `w ∈ X_u` there is a
`u`–`w` path of length `≤ 2R` inside `X_u`*. The `dropUntil` argument above is
its proof, ~10 lines. It is not in the endorsed `IsNeighborhoodCover` and must
be added proofs-side.

⟨B⟩ **The lemma is true — audited against the definition, and the source proves
it twice over.** `Lax12.ColoringNumbers.wreach` (`ColoringNumbers.lean:64-67`)
is `{u | ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y}`: the
`π`-minimality clause is **non-strict**, over the **whole support**, about the
**endpoint** — exactly as Rev 3 read it, so `dropUntil` preserves it verbatim
and Mathlib's `support_dropUntil_subset` / `length_dropUntil_le` supply the
rest. The audit's suspicion that the clause was subtly different (about `w`'s
own position, or strict) is refuted by the definition. GKS prove the same fact
by a shorter route: `X_{2r}[G,<,v] = N_{2r}^{G∖S(v)}(v)` (tex:1468-1471) is a
*ball in the peeled graph*, and a BFS tree of a ball lies inside that ball.

**What the invention does not supply is the channel.** One BFS from `u` does
give the walk `hwalk` demands for every descendant connector, because every
descendant carrier `⊆ X_u`. But `hwalk` is quantified over every earlier round
and the connector is unknown when the BFS runs, so the *record* must be
per-vertex, not one path. That is D6's correction, and line 17 above is written
for it: `bfsSupports`, not `bfsParents`.

### Why line 28 is correct

Fix `β ∈ ℱ_j`, local of rank `(1, q−1)`, and `v` with `ctr v = u`.

```
A ⊨ β(v)
 1  ⟺ SatWithin X_u A col β(v)         β semantically ρ⁻(1,q−1)-local ≤ R,
                                        ball_R(v) ⊆ X_u                 [cover]
 2  ⟺ B_full ⊨ rel(β)(v)                B_full = deleteVerts A X_uᶜ,
                                        cluster recorded as a marker colour
                                        — carrier still Fin n     [Relativize]
 3  ⟺ B_full' ⊨ iso(rel β)(v)           profiles measured in B_full,
                                        then batch isolated       [Isolate]
 3′ ⟺ B ⊨ iso(rel β)(v')                ⟨A⟩ COMPACTION — the missing lemma
 4  ⟺ B ⊨ eval(dec_j β)                 locality applied AT B      [Assembly]
 5  ⟺ eval(dec_j β, sub[v], sc)         child's table and counts
```

⟨A⟩ **Step 3′ is new and Rev 1's claim that "every step is a lemma that already
exists" was false at it.** `Relativize.sat_rel` and `Isolate.sat_iso` both keep
the carrier `Fin n` — `deleteVerts` isolates rather than removes — while D1's
`B` lives on `Fin N`. The only isomorphism-transport lemma in the surviving
layer is `BotEval.sat_congr_bot_of_bij`, restricted to the edgeless graph.

This is not bookkeeping: the two readings **disagree on a value the algorithm
computes**. Applying `locality` at `B_full'` evaluates its scatter atoms over
all of `Fin n`, where every vertex outside `X_u` is isolated *and colourless*,
and greedy picks them; applying it at `B` evaluates over `X_u` only. So the
compaction must come *before* `locality`. Owed lemma, §8 step 4a.

⟨B⟩ **And that is the whole of it — Rev 3's two extra clauses are deleted.**
Rev 3 added that the compaction "must be **order-preserving** (D3) and carry a
**dead-vertex correction** for the greedy choice". Once it comes before
`locality`, neither is needed: step 3′ transports `DistFO.Sat`, which has no
order-sensitive constructor, so any bijection serves; and no greedy value
crosses the boundary, because scatter atoms are evaluated at `B` on `B`'s own
carrier (D3). *A correction is in fact constructible for the route the design
already abandoned — dead vertices are isolated and colour-identical, hence
mutually automorphic and never blocking, so the greedy set shifts by `0` or
`|dead|` — which is only further evidence that moving the compaction before
`locality` was right.* §8 step 4a shrinks accordingly: it is a plain
`Sat`-transport along a bijection.

### Why every table entry is written exactly once

Each `v ∈ V(A)` has one centre `ctr v = u`, and `ball_R(v) ⊆ X_u` implies
`v ∈ X_u`, so `v` occurs in child `u` with `own = true` and nowhere else.
Total readback `Σ_u |X_u| ≤ D·A.N`.

---

## §6 The routines

`N = ‖A‖` is the node's own arena size.

### 6.1 `restrict A S` — ⟨B⟩ `O(Σ_{s∈S} deg_A(s) + |S|·(L + ℓ·R))`
Rank `S` (given sorted — ⟨B⟩ a CSR-build cost matter, *not* correctness; see
D3) to get local names; scan each `s ∈ S`'s CSR row keeping neighbours in `S`;
write the CSR; copy the `L` colour rows; set `up`; **filter `hist`** — for each
`s ∈ S` and each ancestor round, intersect the stored support list with `S`,
sound because carriers are nested (D6). Aggregates to `O((1 + ℓ·R)·c_D·‖A‖^{1+δ})`
over a node's children (§4), still absorbed by the cover term.

The membership test needs a parent-name-indexed lookup. Allocate **one** scratch
array of length `A.N` per *node*, reused across children and cleared only at the
`|S|` touched entries — never one per child, which would be `Θ(A.N²)`.

### 6.2 `cover A R` — the only superlinear routine, and the falsifier
Build a transitive–fraternal augmentation chain, read off an ordering `π`, take
`X_u := {w : u ∈ wreach_π(A,2R,w)}` and `ctr v := π-min(wreach_π(A,R,v))`.
Degree from Lax12's subpolynomial `wcol`, uniform over subgraphs — which is
what lets it be re-applied at every node. `Augmentation`, `AugmentedDensity`,
`OrderedCovers`, `CoverDegree` carry the mathematics.

⟨A⟩ **This routine is now scheduled first, not seventh.** It is (i) the sole
superlinear routine, (ii) the sole source of `D(N)`, (iii) therefore the sole
reason §7 needs `δ` and `(★)`, and (iv) the sole reason §11 exists. Rev 1
isolated its most uncertain claim and then scheduled it after the gate — the
exact error the prune note records as *"attack the falsifier first"*.

⟨B⟩ **What this section describes is the ordering, not the cover algorithm.**
Reading the clusters off `π` is itself a real routine, and GKS give it
(tex:1459-1520): process vertices in **ascending `π` order**; from `v`, run
`2r` BFS levels in the *peeled* graph `G ∖ S(v)`; then **delete `v`**.
Correctness is `X_{2r}[G,<,v] = N_{2r}^{G∖S(v)}(v)` (tex:1468-1471). It needs a
specific representation — edges split into `N_<`/`N_>` lists, built in
`O(n^{1+δ})`, with `d_<(v) ≤ |wreach_{2r}[G,<,v]| ≤ n^δ` — and its accounting
is `Σ_v(|X_v|·n^δ + Σ_{w∈N_>(v)} d_<(w)) ≤ 2n^δ·Σ_v|X_v| ≤ 2n^{1+2δ}`. Note
this **is** `(★)`: the design's starred bound is GKS's own accounting identity,
not merely the design's. Two consequences for this document: the peeling sweep
**mutates the arena**, which §4's operation table does not model; and `ctr`
falls out of the same sweep for free (§4).

⟨B⟩ **Two side conditions the document never states.** (i) GKS's cover theorem
holds only for `n ≥ f(r,ε)`; the design applies `cover` at *every* node, and
arenas shrink with depth, so most deep nodes are below any fixed threshold. It
is absorbable — below threshold the arena is of constant size — but "constants
are free" (§3) is about constant *factors*, and this is a domain restriction.
(ii) The **degree** half carries no such threshold in Lean:
`CoverDegree.exists_cover_degree` (`:366-378`) is `∀ (m) (G : SimpleGraph (Fin m)),
G ⊑ Gn → …` with `m = 0` discharged separately and `c` uniform — quantified over
every subgraph copy on its **own** carrier, which is exactly what licenses
re-applying it at every node, and is stronger than GKS's statement. The
threshold worry therefore applies to the time half alone, which is §8 step 0b.

### 6.3 `recordProfiles B₀ W` — `O((m + L)·‖B₀‖·(R+1))`
BFS to depth `R` from each of the `m` padded batch vertices and from each of the
`L` colour classes (multi-source), recording **cumulative** capped distances as
new colour rows. ⟨A⟩ Rev 1 omitted the `(R+1)` row factor. The kernel is
`dist^A(x,y) = min(dist^{A∖W}(x,y), min_j (p_j(x)+p_j(y)))`.

⟨A⟩ `L` is constant in `n` but grows in `j`, and as a *tower* of height `ℓ` if
the `pu` family survives (O3). Constants are free (§3), so this does not break
the charge — but the charge is `O(L_ℓ · ‖B₀‖)` with `L_ℓ` tower-sized, and that
should be said rather than hidden behind "a constant".

### 6.4 `BotTables A j` — `O(‖A‖)`
In an edgeless arena every distance is `0` or `∞`; a local quantifier collapses
to a disjunction over its guard set, so a one-variable local formula is decided
by reading `v`'s colour row. `BotEval` has this, including the
row-interchangeability argument bounding a witness search by `k + 2^L`.

### 6.5 `greedyScatter A r P t` — `O(t·‖A‖)`
```
if t = 0 then return 0                    -- ⟨A⟩ without this the routine is Θ(N²)
picked := 0 ; marked := ∅
for v in order:
    if P(v) and v ∉ marked:
        picked += 1
        if picked = t: return t
        marked := marked ∪ ball_r(v)
return picked
```

---

## §7 The cost analysis

Per node at depth `j < ℓ` with arena size `N`:

```
 T_j(N) ≤ a·N^{1+2δ}  +  c·Σ_u N_u  +  Σ_u T_{j+1}(N_u)
          └ cover ┘      └ children ┘   └ recursion ┘
```

⟨C⟩ **The cover's exponent is `1+2δ`, not `1+δ`.** §6.2 transcribes GKS's own
accounting for their own cover algorithm as `≤ 2n^{1+2δ}` (tex:1459-1517), and
they set `δ := ε/2` at the head of that proof precisely so `2δ = ε`. Rev 4
charged the routine at `N^{1+δ}` in §4 and then quoted the `2δ` bound in §6.2
without reconciling the two. `δ` is the wcol parameter; the cover costs two of
it.

⟨A⟩ Rev 1 dropped the middle term from the induction — the whole column §6
spends five subsections charging. It is absorbable but it tightens the constant
condition, so it is carried.

```
 Σ_u N_u  ≤  D(N)·N  ≤  (c_D + 1)·N^{1+δ}                                (★)
```

⟨A⟩ The `+1` is the ceiling in `D(N) = ⌈c_D·N^δ⌉`, and it is not pedantry:
at `c_D = 1, δ = ½, N = 2`, `D(N)·N = 4 > 2^{1.5} = 2.83`. The surviving Lean
produces exactly this shape (`CoverDegree.lean:366-378` concludes at
`⌈c·m^δ⌉₊`). The edge half of (★) — an edge of `A[X_u]` lies in `≤ D` clusters
because both endpoints must — has **no counterpart in the surviving layer**
(`CoverDegree.lean:512/524/535` are pure vertex counts) and is an owed lemma.

**Standing hypotheses:** `N ≥ 1` and `c_D ≤ c`. ⟨C⟩ *That is the whole list.
There is no lower bound on `c`.*

⟨C⟩ **The middle term is the wrong quantity, and the leading one absorbs it.**
§4 charges `restrict A S` at `O(Σ_{s∈S} deg_A(s) + |S|(L + ℓ·R))` and *proves*
no data structure achieves `O(‖A[S]‖ + |S|)` (the `K_{3,n−3}` witness), so
`c·Σ_u N_u` does not dominate the restrict column for any constant `c`. §4's
own aggregate — `Σ_u Σ_{s∈X_u} deg_A(s) ≤ 2c_D‖A‖^{1+δ}`, plus §6.1's channel
copy at `ℓ·R·c_D‖A‖^{1+δ}` — is what does, and it belongs in the leading
coefficient: `a := c + (2 + ℓ·R)·c_D`, as §3 now defines it. *Rev 4 wrote
`a := c + 2c_D` and dropped the `ℓ·R` factor its own D6 had just introduced.*

**Claim.** ⟨C⟩ `T_j(N) ≤ K^{L+1} · N^{1+(L+2)δ}` with `L := ℓ−j`, whence at the
root with `δ = ε/(ℓ+2)`:  `T_0(n) ≤ K^{ℓ+1} · n^{1+ε}`. *The headline shape is
unchanged; the split moves by one level and the constant is now chosen.*

*Proof.* Downward induction. Using `(★)`, `N_u ≤ N` and `N ≥ 1`:

```
 recursion  K^L·Σ_u N_u^{1+(L+1)δ} ≤ K^L·N^{(L+1)δ}·(c_D+1)N^{1+δ}
                                    = K^L(c_D+1)·N^{1+(L+2)δ}
 children   c·Σ_u N_u               ≤ c(c_D+1)·N^{1+δ}      ≤ … ·N^{1+(L+2)δ}
 cover      a·N^{1+2δ}                                       ≤ … ·N^{1+(L+2)δ}
```

Both non-recursive lines sit against `N^{1+(L+2)δ}`, and `A := a + c(c_D+1)`
is §3's name for their total, so the step is `K^L·(c_D+1) + A ≤ K^{L+1}`, i.e.

```
 K^L·(K − c_D − 1)  ≥  A.
```

⟨C⟩ **`K` is defined, not constrained.** §3 sets `K := c_D + 1 + A`, so
`K − c_D − 1 = A` exactly and `K^L ≥ 1`: the step holds at every `L ≥ 0` with
nothing to check and nothing to choose. The base at `j = ℓ` is the leaf,
charged linearly at `c·N ≤ K·N^{1+2δ}` — and `K ≥ c` holds outright, since
`A ≥ c(c_D+1) ≥ c`. There are `ℓ+2` levels of exponent to divide `ε` among —
`ℓ+1` levels of recursion, each spending one `δ` through `(★)`, plus the
cover's own second `δ`. ∎

⟨C⟩ **Rev 4's `c ≥ 6` is retired, and so is the shape that produced it.** Rev 4
forced the constant into the form `(2c)^{L+1}` with the *same* `c` that carries
every routine's constant, which couples the base of the exponential to
quantities it has no reason to touch and turns the induction step into a tight
numeric inequality — `3c² + 6c ≤ 4c²`, tight at `c = 6`. Decoupling `K` from
`c` dissolves it. **This is Jan's call, 2026-08-17: take the slack, do not
tighten.** The justification is empirical rather than aesthetic. This paragraph
has been wrong in three consecutive revisions — Rev 1 dropped the middle term,
Rev 3 dropped a `c` and the `+1`, Rev 4 dropped the `ℓ·R` factor and reported
`c ≥ 6` where the same page's `a` gives a different figure — and every one of
those was a dropped term in a *tight* inequality that a slack one would have
swallowed. GKS never meet such a condition because they never tighten: their
`δ = ε/(2ℓ)` (tex:2621) is slacker still and would also serve here. A tight
constant nobody needs is a defect surface, not a result.

**This is an amendment of a compiled proof, not new work.** The restored
`CostRecurrence.lean` (`pruned-algorithmic-layer.md` §3a) has
`exists_driverCostsSigma` (`:441`) carrying `(★)` as `∑_{c<t} bs c ≤ D·(m+1)`
verbatim, and `sigma_root_almostLinear` (`:610`) closing the exponent. Rev 1
called that file *"correct arithmetic for the wrong program"* — reading its
framing prose instead of its statements, which is the same error this redesign
exists to stop making. Two gaps remain and are step 1's content: it assumes each
level's charge is **linear** in arena weight where §6.2's cover is ⟨C⟩ `a·N^{1+2δ}`,
and it splits `ε` as `ε/ℓ` rather than ⟨C⟩ `ε/(ℓ+2)`.

---

## §8 The order of work

⟨A⟩ Rev 1's ordering had three defects: it scheduled machine-level work three
steps before a gate forbidding machine-level work; it scheduled the falsifier
(`cover`) last; and it called steps 1–4 "independent" when two of them gate the
shape of the others. Re-ordered:

0. ⟨B⟩ **Split — Rev 3's step 0 bundled two questions that are not the same
   question, one of which is already answered and the other of which cannot be
   closed with the documents in hand.** A reader who follows Rev 3's step 0
   spends a week and lands nothing.
   - 0a. **The space half is settled; do not spend a week on it.** §11's
     conclusion is right and is in fact *unconditional* — see §11 as rewritten.
     Nothing to probe.
   - 0b. **⟨C⟩ The time half is neither a probe nor an import: the deferral
     chain was opened link by link on 2026-08-17, it is four links long, and it
     terminates in a proof.** Rev 4's text below this point said the opposite —
     "blocked pending NOdM 2005, which is not in this repository, ask Jan" — and
     was wrong within one bibliography lookup. The chain, each link read rather
     than recorded: (1) GKS's cover theorem, `thm:alg-covers`
     (`gks tex:1254-1263`). (2) Its only superlinear stage,
     `thm:computingorientation` (tex:1342-1352), whose whole proof is the
     bracket *[NOdM 2005, Cor 4.2, Thm 4.3]*; GKS's only remark on rounds is
     the aside at tex:1369-1372. (3) The bracket resolves onto
     `references/nodm05/BEII.tex` §4, where the algorithm is given in full:
     transitivity arcs in `O(md²·n)` (`:615-620`), fraternity edges in
     `O(md²·n)` with `|L| ≤ md²·n/2` (`:672-674`), simplification +
     low-indegree orientation + merge in `O(md²·n)` (`:676-678`), the
     in-degree recurrence `md(G_{i+1}) ≤ md(G_i)² + 2∇₀(G_i)` (`:570-571`),
     and the orientation step proved unconditionally — acyclic, in-degree
     `⌊2∇₀(G)⌋`, `O(n+m)` (`:446-499`). (4) Part II's own Lemma 4.1
     (`:530-542`) is *"special case of Lemma 6.1 of [POMNI]"* — part I,
     `references/nodm05i/BEI.tex:1064-1091`, where it is **proved in full**,
     with Corollary 6.2 (`:1092-1101`) bounding `md(G_i)` along the chain.
     Nothing below that is deferred. **What no paper in the chain states is
     the nowhere-dense instantiation**: Theorem 4.3 (`BEII.tex:679-688`) is a
     *bounded expansion* statement at fixed `c` in time *O(n)*, and Corollary
     4.2 (`:545-567`) likewise opens with bounded expansion, while GKS cite
     both for *nowhere dense* with `Δ⁻ ≤ n^ε` in `f(r,ε)·n^{1+ε}`. The owed
     work is exactly that adaptation — `∇_s` subpolynomial through the round
     recursion, and the `O(md²·n)` accounting at `md = n^δ` instead of
     `md = O(1)` — not the import of a paper. Until it is done, the cover's
     time bound is an assumption of the design, and it now **is** written as
     one: `Lax3Proofs.CoverSpec.CoverOrderingTime` (`CoverSpec.lean`), whose
     `IsCoverOrdering.time` field is the single unproved claim and whose
     cover, radius, covering and degree clauses are all derived from the
     landed layer, not assumed.
1. **Amend the cost-recursion lemma** of §7 — already compiled as
   `CostRecurrence.exists_driverCostsSigma` / `sigma_root_almostLinear`.
   Generalize `hKo`/`hKc` from arena-linear to ⟨C⟩ `a·N^{1+2δ}` (the cover's
   honest exponent — §7), re-split `ε` over ⟨C⟩ `ℓ+2`,
   add the standing hypotheses, and prove (★)'s owed edge half.
   Mathlib-only. **Note it is not independent of step 0b:** a different cover
   changes `D`, hence `(★)`, hence the parameterisation.
2. **Resolve O1/O5 together** — generalize `SplitterWinRec.ReachedR` from
   ball-moves to `S`-moves and prove the analogues of `isolatedR`,
   `mem_ball_of_roundR`, `no_full_survivalR`, `reachedR_descend`,
   `reachedR_length_lt`; add the cover's path-closure guarantee (§5) and the
   carrier-transport lemma. ⟨A⟩ **Not** "expose the strategy as a function":
   `SplitterWin.batch` is noncomputable and takes the ancestor arena stack, and
   `ReachedR` already records the batch as *data of the round*, which is the
   interface a program can meet.
3. **Expose the locality rewriting as a function** (O2).
4. **The abstract algorithm** — §5 over the `Arena` interface of §4 taken
   abstractly; correctness by §5's chain; cost by §7. **Hard gate: no ND-MC
   driver is written until this is complete and reviewed.**
   - 4a. the compaction/transport lemma of step 3′ — ⟨B⟩ a plain `Sat`-transport
     along a bijection `Fin N ≃ X`. *Rev 3 required it to be order-preserving
     and to carry a dead-vertex correction; D3 and §5 record why both clauses
     are phantom. Still owed, but much smaller than Rev 3 priced it.*
   - 4b. unrolling §5's depth-`ℓ` recursion into `ℓ+1` depth-indexed levels:
     Lax13's machine has no call stack, so this is a real step and Rev 1
     assigned it to nobody. Say whether the `ℓ+1` frames are laid out
     statically at the maximum arena per depth, or dynamically.
5. **Instantiate `Lax13Proofs.Refine`** — the landed NREST/Sepref tower — on one
   ND-MC routine (bounded-depth BFS, which the tower already has as an
   acceptance program) and check the charge falls out. ⟨A⟩ A one-week probe
   with a landed example to copy, not a layer to build. Its
   `SpaceBudgetProbe`/`HeapAlloc` layers are also the natural place to confront
   §11.
6. **The `Arena` implementation** and the remaining routines, including `ctr`'s
   `π-min` identity (§4).
7. **Compose to the headline.**

---

## §9 Open questions

**O1/O5 — the splitter interface.** ⟨A⟩ Substantially resolved, and the
resolution changed the design (§5 lines 17–23). Settled by audit: the
generalized `(v,S)` game *is* won — the induction closes in ~15 lines from
`SplitterMono.splitterWins_anti` plus the batch map `W ↦ W ∩ S`, with the
changed-distances objection absorbed because the hypothesis is universally
quantified over graphs. But *"its strategy reads only `A[S]`"* is **false**, and
Rev 1's line 16 was vacuous (§5). The repair is the path-closure route. What
remains genuinely open:

- the `S`-generalized `ReachedR` and its five analogue lemmas (step 2);
- ⟨A⟩ **the precondition is not inductive as Rev 1 stated it.** `SplitterWins`
  gives *some* batch `W`; the algorithm isolates its own, and isolating fewer
  vertices gives a *larger* graph while `splitterWins_anti` only goes down. So
  the leaf's edgelessness is not derivable. Replace the precondition with the
  play-record `ReachedR` and take the leaf from `reachedR_length_lt`, which
  bounds depth without ever naming a batch — which is what the deleted driver
  did (`RamDriver.lean:41-45`) and Rev 1 lost;
- carrier transport for `ReachedR` under adding isolated vertices. ⟨B⟩ Note
  `RoundR n` fixes `arena : SimpleGraph (Fin n)` (`SplitterWinRec.lean:129-135`)
  and `ReachedR` types `A : SimpleGraph (Fin n)` (`:192-193`), so §5's `# pre:`
  line does **not** typecheck against D1's renumbered `A : SimpleGraph (Fin N_j)`;
  and `nextArenaR` restricts to `ball e.arena r e.vtx` (`:153-154`) where the
  design restricts to `X_u ⊆ ball`. Both are booked here and at §8 step 2, but
  §5's precondition is written in a notation that presumes them discharged.

⟨B⟩ **Resolved by this audit, and struck from the open list:** whether the
algorithm's self-built batch is a legal move. It is — see §3. The batch is
`SplitterWin.genSet`, its size bound `genSet_ncard_le` is landed, and the
correct `m = ℓ(2R+1)` comes from `splitterWins_of_reachedR`. What made this look
open was reading `m` off the wrong existential.

**O2 — make the locality decomposition a function.** Unchanged, but ⟨A⟩ its
payoff is smaller than Rev 1 claimed: `ℓ`, `m`, `c_D` remain
`Classical.choose`, so `ℱ_j` stays noncomputable regardless (D5).

**O3 — can the `pu` colour family be dropped?** Unchanged; re-open after O2.
⟨A⟩ Note the interaction §6.3 records: if `pu` survives, `L_ℓ` is a tower of
height `ℓ`, which is affordable but should be stated.

**O4 — ⟨A⟩ withdrawn; it pointed at the wrong submission.** The intermediate
machine layer Rev 1 asked whether to build already exists as
`Lax13Proofs.Refine`, a pinned dependency of this package (D7). The live
question is not whether to build one but how much of the tower to instantiate,
and that is step 5.

**O6 — ⟨A⟩ new, and the one that decides the project: what does `cover` cost in
*space*?** See §11. ⟨B⟩ **Closed by the third audit: the squared side condition
suffices unconditionally**, because a cover degree is at most the carrier size,
so the peak is `≤ N²` for every `ε` and `δ` with no hypothesis. §11 carries the
argument. The space question is no longer what decides the project.

**O7 — ⟨B⟩ new, and it replaces O6 as the one that decides the project: can the
cover's *time* bound be obtained at all?** ⟨C⟩ **Narrowed by E0, not closed.**
Rev 4 wrote here that GKS defer to a paper this repository lacks and that the
claim "cannot be discharged by working harder on material already here"; both
NOdM papers are now at `references/nodm05{,i}/` and the second clause is false —
see §8 step 0b for the chain, opened link by link, terminating in part I's
Lemma 6.1 with the algorithm and its per-round `O(md²·n)` costs given in full
in part II. The bound is still load-bearing and still unproved: it stands as
the hypothesis `Lax3Proofs.CoverSpec.CoverOrderingTime` — `f` quantified
before the graph, exponent `1+2δ` — with everything else about the cover
derived, so the open question is now exactly the `time` field. What would
close it: (i) the nowhere-dense instantiation of Corollary 4.2 — `∇_s`
subpolynomial through the round recursion `md(G_{i+1}) ≤ md(G_i)² + 2∇₀(G_i)`,
with an explicit threshold `n ≥ f(r,ε)`; (ii) the `O(md²·n)` accounting of
the augmentation and orientation rounds at `md = n^δ` rather than `md = O(1)`.
Formalizing that is a campaign, not a leaf (`execution-plan.md`, "what is
deliberately not a leaf"); the design consumes the hypothesis.

---

## §10 What this design owes to the pruned layer

*(Rev 1 claimed "three facts, and nothing else". Not honest: L0, D5, §6.4, O2,
O3, D7 and §8 each import a further finding, and §7 rests on a compiled lemma
from it — `pruned-algorithmic-layer.md` §3a.)*

1. The cost model of the source is **per cluster**, not per carrier.
2. The isolation variant genuinely eliminates GKS §8's `θ`-variant family and
   readout formulas, with no residue.
3. ~~`n^{1+ε}` at `ε = ½` clears with headroom; the algorithm is not a dead
   end.~~ **Struck: false** (`pruned-algorithmic-layer.md` §2 (4)). Nothing in
   this repository supports *or* refutes the claim that the algorithm meets
   `n^{1+ε}`; the support is the GKS paper's analysis, which is not formalized
   here. **§7 is therefore a fresh derivation and the design's load-bearing
   unproved claim.**

---

## §11 ⟨A⟩ Space against word length — found by audit, resolved by contract

*New in Rev 3. No claim group was assigned this; the completeness critic found
it. It was fatal as written and is now resolved; the resolution is recorded at
the end of this section.*

**The machine's memory is its word length.** Lax13's RAM has `2^w` cells and
every address is taken mod `2^w` (`Lax13/Ram.lean:9-10, 25, 231-237`), so a cell
above `2^w` does not merely fail — it *aliases*.

**The endorsed axiom affords only linear space.** `ModelChecking.lean:84`
admits `x` when `∀ v ∈ x, c·(x.length + v + 1) ≤ 2^w`, and `:82` quantifies
`∀ w`. So the program must work at the *smallest* admissible `w`, where
`2^w < 2c·(|x| + max x + 1)` — `Θ(c·|x|)` addressable cells, with `c` fixed
before the instance.

**The design needs `Θ(n^{1+δ})`.** By D1's corrected memory account, a node
cannot release its cover output until its subtree finishes, and that output has
`Σ_u |X_u| ≤ D·N` entries; the augmentation chain's fraternity graphs are
`Θ(N^{1+δ})` too. Constants are free (§3) and `n^δ` is not.

**The deleted layer hit this exact seam and proved a theorem of its shape** —
`Refine/BridgeSeamProbe.no_word_size_for_sparse`, whose own prose reads: *"the
statement quantifies over all `w`, so the smallest admissible one is in scope,
where `2^w ≤ 2·c·(|x| + max x + 1)`. On a sparse member that is linear in `n`
where the driver needs `n²`."* Rev 1 contained no occurrence of "space", "word
length" or `2^w`.

**Resolved 2026-08-17 by Jan: the side condition is squared.**
`Lax3.ModelChecking` now admits `x` at word length `w` when
`c·(|x| + v + 1)² ≤ 2^w`, so the smallest admissible word length moves from
`log|x| + O(1)` to `2·log|x| + O(1)` — a constant factor in `w`, a quadratic
factor in addressable memory, and enough for any `n^{1+δ}` with `δ ≤ 1`. The
deviation is recorded in full in the concept's own docstring, including what it
costs: the program is excused from the narrowest word lengths, and that is a
genuine weakening. It touches no other submission — the side condition lives in
this submission's own concept file, and Lax11's Courcelle axiom keeps the linear
form, which is correct for it since Courcelle runs in linear space.

⟨A⟩ **Correction to Rev 3 as first written:** that revision said this change
would collide with Lax11 and with the thirteen lakefiles pinning `word-ram`. It
does not. Nothing outside `concepts/Lax3/ModelChecking.lean` mentions the
condition, and no package consumes the axiom.

**The exponent is `2`, not `1 + δ`,** because a side condition varying with the
class and `ε` would be harder to read and to reuse than one fixed by the
encoding.

⟨B⟩ **The change is sufficient — it is the one decision in Rev 3 the audit
could not shake — but two of its four stated reasons were false, and the true
reason is stronger than the one given.**

- *Struck: "enough for any `n^{1+δ}` with `δ ≤ 1`."* `δ ≤ 1` is nowhere
  established and **fails at `ε > ℓ+2`**, since ⟨C⟩ `δ = ε/(ℓ+2)`.
- *Struck: "it should be a property of the encoding alone."* The admissible set
  **already** varies with `(C, φ, ε)` through `c`, under either exponent. The
  exponent's stability is a convenience, not a principle.
- **The true argument needs no hypothesis at all.** A cover degree is at most
  the carrier size, so `Σ_u |X_u| ≤ N²` for *every* `ε` and `δ`
  (`wreach_fibre_eq`, `CoverDegree.lean:584`; `sum_ncard_le_mul`, `:512`), and
  the same holds for the augmentation chain's round graphs. The guarantee is
  `2^w ≥ c·(|x|+1)² ≥ c·n²` (`ModelChecking.lean:122`). Choose `c` large enough
  to absorb the `ℓ+1` live frames and their constants — legal, since `c` is
  bound by the `∃` under `∀ C φ ε` and `ComputesInTime` is `∀ x ∈ D`, so a
  larger `c` loosens the time bound and shrinks the obligation together. **It
  fits for every `ε` and `δ`, unconditionally.** Keep the exponent; the
  concept's docstring should carry this reason rather than the two struck ones.

**This does not close O6, it unblocks it.** The two space repairs below remain
worth having, because they would let the *linear* side condition be restored and
the statement strengthened — which is why the concept writes `^ 2` out rather
than folding it into `c`:

1. **Stream the cover.** Nothing forces the cluster family to be materialized:
   the tree is walked depth-first, so if `X_u` can be produced on demand from
   the ordering `π` alone, peak memory is `O(max cluster + n)` per level.
   ⟨B⟩ *Rev 3 recorded an obstacle here — "computing one fibre without the whole
   wreach relation is not obviously possible" — and the source refutes it:
   `X_{2r}[G,<,v] = N_{2r}^{G∖S(v)}(v)` (GKS tex:1468-1471), so **one cluster is
   one BFS in the peeled graph**, no wreach relation required. Streaming would
   still not restore the linear side condition, so this stays off the critical
   path — but the stated obstacle is not the reason.*
2. **Bound the augmentation chain's live memory** independently of its output
   size, or recompute rather than store.

Neither is on the critical path now. `cover` stays §8 step 0b for its *time*
bound, which is still the design's falsifier.

---

## §12 ⟨B⟩ The third audit — what it changed, and what it could not shake

Nine agents, 1.35M tokens, four attack groups each followed by an adversarial
verifier told to refute the auditor, then a synthesizer. Nine findings survived
at **major**; none was in the algorithm. Recorded here so the next session
inherits the evidence instead of re-deriving it.

**What survived unshaken.** §5's recursion, §7's *shape*, D2–D4, and **both** of
Rev 3's new inventions. The path-closure lemma is true (§5, verified against
`wreach`'s definition and independently against GKS tex:1468-1471). The
compaction lemma is true and *smaller* than Rev 3 thought (D3, §5, §8 4a). The
squared side condition is sufficient **unconditionally** (§11). Rev 3 was a
real repair; what it did not do was reconcile its twenty patches with each
other.

**The four real defects, all seam defects.**

1. **The channel** (D6, §4, §5 lines 17-23). `bfsParents` records a *tree*;
   `hist : List Path` declares a *path*; `ReachedR.step` needs a per-vertex
   answer. All three differ, and Rev 3 asserted the cheapest one. Repaired to
   per-vertex support lists at `O(ℓ·R·‖A‖)` per node.
2. **`ℓ` and `m` were mis-sourced** (§3). The O1 precondition swap cut them from
   the axiom they were read out of, and nothing noticed. Repaired to
   `ℓ := N(2s+2)` and `m := ℓ(2R+1)`, both landed — and under the corrected `m`
   the batch is legal and *is* `SplitterWin.genSet`, already in the repository.
3. **§7's constant arithmetic** (§7). Two dropped terms and a false hypothesis,
   in the paragraph written to repair the previous audit's counterexample.
   Repaired to a three-term recurrence with `c ≥ 6`.
4. **§8's work order** (§8 step 0). The step scheduled first bundled a settled
   question with an unclosable one.

**The finding that changes the plan.** The cover's `O(N^{1+δ})` *time* bound is
true in the literature and unformalizable from anything this project holds: GKS
defer their only superlinear stage to Nešetřil–Ossona de Mendez 2005, which is
not in this repository, and the Lean cover layer carries the degree half only.
Get that paper before step 0b.

**The process rule, earned a fourth time.** Every defect above is a place where
the document asserted something its own cited object does not say — `List Path`
against what line 23 stores, an axiom's `ℓ` against the lemma actually used, a
printed inequality against the recurrence above it, GKS's `ctr` against GKS's
Remark. *Read the theorem, not the docstring, and not the file's framing prose.*
The one place Rev 3 did read the definition — the `wreach` minimality clause —
is the one place its invention survived intact.
