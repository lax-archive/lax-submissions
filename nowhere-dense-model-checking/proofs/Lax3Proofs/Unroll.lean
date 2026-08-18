import Lax3Proofs.Driver

/-!
# Unrolling the depth-`ℓ` recursion (E10, §8 step 4b) — and the run tree

Two halves.

## Half 1 — the unroll

Lax13's machine has no call stack, so §5's depth-`ℓ` recursion must be
expressed as `ℓ+1` depth-indexed levels. At the abstract layer that
means: factor `tablesAux` into

* `frameEval` — **the code of one frame**: the body of `tablesAux`'s
  recursive case at depth `j`, with the recursive call abstracted into
  an oracle `next` for the depth-`j+1` tables. `frameEval` contains no
  self-reference: everything a frame does is one call pattern into the
  level below.
* `botFrame` — the bottom frame: fuel exhausted, `BotTables` through its
  spec (the table IS satisfaction, which at an edgeless arena a machine
  evaluates by row lookups — `Lax3Proofs.BotEval`).
* `unrollAux` — the levels laid out: `unrollAux (k+1) j` is *defined* as
  `frameEval` at `j` wired to `unrollAux k (j+1)`. The recursion is on
  the **level index**, bounded by `ℓ` at the root, never on the
  function's own value at the same level: the machine realizes it as
  `ℓ+1` static code blocks, block `j` jumping only into block `j+1`,
  with one frame of live state per block.

`unrollAux_eq_tablesAux` / `unrolledTables_eq_tables` state that the
iterative form computes **exactly** `Driver.tables` — the same
traversal, mirrored structurally, so the proof is induction on the fuel
with no appeal to the write-once discipline. `unrolledMC` closes the
root the same way, and `unrolledMC_correct` inherits E9's correctness
verbatim. The cost side is free by the same mirroring:
`unrolledCost_eq_dcost` says the charge of the iterative form is
`Driver.dcost` on the nose.

## The frame layout decision (§8 step 4b's owed sentence, priced against §11)

**Decision: static.** Frame `j` (`0 ≤ j ≤ ℓ`) is laid out at the
per-depth maximum arena, at a base offset computed once at startup from
`n` alone; no allocation happens during the run.

The arithmetic. A child carrier is a cluster of its parent
(`childN = (cluster …).ncard ≤ A.N`), and `deleteVerts` *isolates, it
does not remove* — so carriers do not shrink along a branch beyond the
cluster restriction and the per-depth maximum carrier is the root's `n`
at **every** depth: nothing telescopes. What frame `j` must hold until
its subtree returns (D1's memory account): the arena
(`≤ n + |E| ≤ n²` words), the node's cover output
`Σ_u |X_u| ≤ D_j·N_j ≤ N_j² ≤ n²` (a cover degree is at most the
carrier — §11's unconditional bound, `wreach_fibre_eq` +
`sum_ncard_le_mul`), the per-vertex support lists (`m = ℓ(2R+1)` root
names per vertex: `m·n` words), the color rows (`pal j` rows — a
constant of the schedule — of `n` bits each) and the child-table
readback (`|ℱ_(j+1)|·n` bits). Per frame that is
`≤ 2n² + c_S·n ≤ (2 + c_S)·n²` words with `c_S` a constant of the
schedule alone, so the whole static layout is
`≤ (ℓ+1)·(2 + c_S)·n²` words. The endorsed word-length guarantee is
`2^w ≥ c·(|x|+1)² ≥ c·n²` (`ModelChecking.lean:122`), and `c` is fixed
after `(C, φ, ε)` and *before* the input — choosing
`c ≥ (ℓ+1)·(2 + c_S)` absorbs the whole layout, for every `ε` and `δ`,
unconditionally. This is exactly §11's own resolution ("choose `c`
large enough to absorb the `ℓ+1` live frames and their constants"),
here spent on the static layout.

**Why not dynamic.** A dynamic layout — each frame allocated at its
node's actual sizes — saves only the gap between per-depth actual and
per-depth maximum, a constant factor at best: the depth-`j` peak is
genuinely `Θ(n²)` in the worst case at every depth (the cover output
does not telescope), so no exponent improves. And it costs an
allocator/free-pointer discipline that Lax13's RAM does not have and
that E12 would have to build and verify. Constants are free (§3) and
the squared side condition already pays for the static worst case.

## Half 2 — the run tree, reified (E9's deferred composition)

E9 delivered `Inv`, `inv_root`, `inv_child` and `eq_bot_of_inv_depth`
per step and deferred the composition over the whole recursion tree of
one run. Here the run is reified: `RunTree`/`runTreeAux` is the tree of
arenas one `tables` evaluation visits — one node per `(depth, arena)`,
one child per vertex `v`, namely the child arena of `centre v`, exactly
the arena `tablesAux`'s entry at `v` recurses into. (It is written down
for every `v` whether or not some schedule formula actually reads it —
a superset of any single run's reads, so every theorem below covers
every read.) `MemTree`/`MemLeaf` are visitation and bottoming-out.

The composed theorems:

* `inv_of_memTree` — **`Inv` threads through the whole tree**: from
  `Inv` at the tree's root, every visited arena satisfies `Inv` at its
  own depth (`inv_child` at every edge).
* `memLeaf_eq_bot` — **the payoff**: within the UQW budget, every arena
  at which the run bottoms out is edgeless. A leaf is either the
  edgeless branch (nothing to show) or fuel exhaustion, which the depth
  accounting places exactly at depth `ℓ`, where `eq_bot_of_inv_depth`
  applies. Hence **`tablesAux`'s fuel-0-with-edges branch is never
  taken**: the structural fuel never truncates a node with edges.
* `memTree_depth_le` — the traversal really is `ℓ+1` frames deep:
  every visited depth lies in `[j, j+fuel]`, so `[0, ℓ]` from the root.

`mkSetup_inv_of_memTree`, `mkSetup_memTree_depth_eq_bot` and
`mkSetup_memLeaf_eq_bot` restate all of it at the campaign setup, on a
member of the class, with every hypothesis discharged by E9's `mkSetup`
lemmas (`mkSetup_margin`, `mkSetup_depth`, `mkSetup_width_le`,
`inv_root`).
-/

namespace Lax3Proofs.Unroll

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.UniformQuasiWideness Lax12.ColoringNumbers
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ### Half 1: the frames -/

/-- **The bottom frame** (fuel exhausted): `BotTables` through its
spec — the table is satisfaction at the node's own (by the invariant:
edgeless) arena. -/
def botFrame (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀) :
    Fin A.N → DistFO (S.pal j) 1 → Prop :=
  fun v β => Sat A.G A.col (fun _ => v) β

open Classical in
/-- **The code of one frame**: the body of `tablesAux`'s recursive case
at depth `j`, with the recursive call abstracted into the oracle `next`
for the depth-`j+1` tables. No self-reference: a frame's only exit is
one call pattern into the level below. -/
noncomputable def frameEval (S : Setup L) (ord : CoverSpec.OrderingRoutine) (j : ℕ)
    (next : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (A : Arena (S.pal j) n₀) : Fin A.N → DistFO (S.pal j) 1 → Prop :=
  if A.G = ⊥ then fun v β => Sat A.G A.col (fun _ => v) β
  else fun v β =>
    let π := (ord A.N A.G).order
    let u := centre S A π v
    let B := childArena S A π u
    let vc : Fin B.N := (childEquiv S A π u).symm ⟨v, mem_cluster_centre S A π v⟩
    if h : IsLocal β ∧ DRank 1 (S.q - 1) β then
      (dec S (j := j) ⟨β, h.1, h.2⟩).eval
        (Sum.elim (fun ψ => next B vc ψ)
          (fun σ => σ.t ≤ S.choice.size B.G σ.r {a | next B a σ.β}))
    else True

/-- **The unrolled driver**: `k` levels below depth `j`, laid out by
recursion on the *level index* — level `j` is `frameEval` wired to
level `j+1`, and the bottom is `botFrame`. No level refers to itself,
so a machine realizes this as `k+1` static code blocks with one frame
of live state each; at the root `k = ℓ`. -/
noncomputable def unrollAux (S : Setup L) (ord : CoverSpec.OrderingRoutine) :
    (k : ℕ) → (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → DistFO (S.pal j) 1 → Prop
  | 0, j, A => botFrame S j A
  | k + 1, j, A => frameEval S ord j (fun B => unrollAux S ord k (j + 1) B) A

/-- **§8 step 4b's iterative form of `tables`**: the `ℓ+1` depth-indexed
levels at depths `j … ℓ`. -/
noncomputable def unrolledTables (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀) : Fin A.N → DistFO (S.pal j) 1 → Prop :=
  unrollAux S ord (S.depth - j) j A

/-- **The iterative form computes exactly `tablesAux`**, at every fuel —
by induction on the fuel: the two definitions mirror each other level
by level, so no write-once argument is consumed. -/
theorem unrollAux_eq_tablesAux (S : Setup L) (ord : CoverSpec.OrderingRoutine) :
    ∀ (k j : ℕ) (A : Arena (S.pal j) n₀),
      unrollAux (n₀ := n₀) S ord k j A = tablesAux S ord k j A := by
  intro k
  induction k with
  | zero => intro j A; rfl
  | succ k ih =>
    intro j A
    rw [unrollAux, tablesAux, frameEval]
    simp only [ih]

/-- **The iterative form computes exactly `Driver.tables`** — §8 step
4b's owed theorem. -/
theorem unrolledTables_eq_tables (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀) :
    unrolledTables (n₀ := n₀) S ord j A = tables S ord j A :=
  unrollAux_eq_tablesAux S ord (S.depth - j) j A

/-- §5's `MC`, over the unrolled driver. -/
noncomputable def unrolledMC (S : Setup L) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L) : Prop :=
  (top S).eval (Sum.elim (fun ψ => localConst ψ)
    (fun σ => σ.t ≤ S.choice.size G σ.r
      {v : Fin n | unrolledTables S ord 0 (rootArena G col) v σ.β}))

theorem unrolledMC_eq_MC (S : Setup L) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L) :
    unrolledMC S ord G col = MC S ord G col := by
  rw [unrolledMC, MC, unrolledTables_eq_tables]

/-- The unrolled driver decides `φ` — E9's `mc_correct`, inherited. -/
theorem unrolledMC_correct (S : Setup L) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L) :
    unrolledMC S ord G col ↔ Sat G col Fin.elim0 S.φ := by
  rw [unrolledMC_eq_MC]
  exact mc_correct S ord G col

/-! ### Half 2: the run tree -/

/-- The shape of one run: a tree of arenas, one node per `(depth,
arena)`, children one level down. -/
inductive RunTree {L : ℕ} (S : Setup L) (n₀ : ℕ) : ℕ → Type where
  /-- A node the run bottoms out at (edgeless, or fuel exhausted). -/
  | leaf {j : ℕ} (A : Arena (S.pal j) n₀) : RunTree S n₀ j
  /-- A node the run descends from: for each vertex `v`, the subtree of
  the child arena its entry recurses into. -/
  | node {j : ℕ} (A : Arena (S.pal j) n₀)
      (child : (v : Fin A.N) → RunTree S n₀ (j + 1)) : RunTree S n₀ j

open Classical in
/-- **The run tree of one `tablesAux` evaluation**: mirrors the fuel
recursion. At a node with fuel left and an edge, the child at `v` is
the child arena of `centre v` — exactly the arena the entry at `v`
recurses into (whether or not some schedule formula reads it; the tree
is a superset of any single run's reads). -/
noncomputable def runTreeAux (S : Setup L) (ord : CoverSpec.OrderingRoutine) :
    (k : ℕ) → (j : ℕ) → Arena (S.pal j) n₀ → RunTree S n₀ j
  | 0, _, A => .leaf A
  | k + 1, j, A =>
    if A.G = ⊥ then .leaf A
    else .node A (fun v => runTreeAux S ord k (j + 1)
      (childArena S A ((ord A.N A.G).order)
        (centre S A ((ord A.N A.G).order) v)))

/-- The run tree of `tables` at a depth-`j` node: fuel `ℓ − j`, the
mate of `Driver.tables`. -/
noncomputable def runTree (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀) : RunTree S n₀ j :=
  runTreeAux S ord (S.depth - j) j A

/-- Visitation: the arena `A'` (at its depth `j'`) occurs somewhere in
the tree. -/
inductive MemTree {L : ℕ} (S : Setup L) (n₀ : ℕ) :
    {j' : ℕ} → Arena (S.pal j') n₀ → {j : ℕ} → RunTree S n₀ j → Prop where
  /-- The arena of a leaf is visited. -/
  | leaf {j : ℕ} (A : Arena (S.pal j) n₀) : MemTree S n₀ A (.leaf A)
  /-- The arena of an inner node is visited. -/
  | root {j : ℕ} (A : Arena (S.pal j) n₀)
      (child : (v : Fin A.N) → RunTree S n₀ (j + 1)) :
      MemTree S n₀ A (.node A child)
  /-- Whatever a subtree visits, the tree visits. -/
  | child {j' j : ℕ} {A' : Arena (S.pal j') n₀} {A : Arena (S.pal j) n₀}
      {ch : (v : Fin A.N) → RunTree S n₀ (j + 1)} (v : Fin A.N) :
      MemTree S n₀ A' (ch v) → MemTree S n₀ A' (.node A ch)

/-- Bottoming out: the arena `A'` is one at which the run stops —
a leaf of the tree. -/
inductive MemLeaf {L : ℕ} (S : Setup L) (n₀ : ℕ) :
    {j' : ℕ} → Arena (S.pal j') n₀ → {j : ℕ} → RunTree S n₀ j → Prop where
  /-- A leaf bottoms out at its own arena. -/
  | leaf {j : ℕ} (A : Arena (S.pal j) n₀) : MemLeaf S n₀ A (.leaf A)
  /-- Wherever a subtree bottoms out, the tree does. -/
  | child {j' j : ℕ} {A' : Arena (S.pal j') n₀} {A : Arena (S.pal j) n₀}
      {ch : (v : Fin A.N) → RunTree S n₀ (j + 1)} (v : Fin A.N) :
      MemLeaf S n₀ A' (ch v) → MemLeaf S n₀ A' (.node A ch)

/-- A node the run bottoms out at is, in particular, visited. -/
theorem memTree_of_memLeaf {S : Setup L} {j' j : ℕ}
    {A' : Arena (S.pal j') n₀} {t : RunTree S n₀ j}
    (h : MemLeaf S n₀ A' t) : MemTree S n₀ A' t := by
  induction h with
  | leaf A => exact .leaf A
  | child v _ ih => exact .child v ih

/-- **The traversal is `fuel+1` frames deep**: every visited depth lies
in `[j, j + fuel]` — at the root, `[0, ℓ]`, so `ℓ+1` levels ever hold a
live frame. -/
theorem memTree_depth_le (S : Setup L) (ord : CoverSpec.OrderingRoutine) :
    ∀ (k j : ℕ) (A : Arena (S.pal j) n₀) {j' : ℕ} {A' : Arena (S.pal j') n₀},
      MemTree S n₀ A' (runTreeAux S ord k j A) → j ≤ j' ∧ j' ≤ j + k := by
  intro k
  induction k with
  | zero =>
    intro j A j' A' hmem
    rw [runTreeAux] at hmem
    cases hmem
    omega
  | succ k ih =>
    intro j A j' A' hmem
    rw [runTreeAux] at hmem
    by_cases hbot : A.G = ⊥
    · rw [if_pos hbot] at hmem
      cases hmem
      omega
    · rw [if_neg hbot] at hmem
      cases hmem with
      | root => omega
      | child v h' =>
        have h := ih (j + 1) _ h'
        omega

/-! ### The composed invariant: `Inv` over the whole run -/

/-- **E9's deferred composition** — the invariant, threaded through the
whole recursion tree of one run: from `Inv` at the tree's root, every
arena the run visits satisfies `Inv` at its own depth. Induction on the
fuel; `inv_child` at every edge (the width hypothesis is §3's
`m = ℓ(2R+1)` at every depth below `ℓ`, exactly `inv_child`'s shape). -/
theorem inv_of_memTree (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {G₀ : SimpleGraph (Fin n₀)}
    (hwidth : ∀ i, i < S.depth → 1 + i * (2 * S.R + 1) ≤ S.width) :
    ∀ (k j : ℕ), j + k ≤ S.depth → ∀ (A : Arena (S.pal j) n₀), Inv S G₀ j A →
      ∀ {j' : ℕ} {A' : Arena (S.pal j') n₀},
        MemTree S n₀ A' (runTreeAux S ord k j A) → Inv S G₀ j' A' := by
  intro k
  induction k with
  | zero =>
    intro j hj A hInv j' A' hmem
    rw [runTreeAux] at hmem
    cases hmem
    exact hInv
  | succ k ih =>
    intro j hj A hInv j' A' hmem
    rw [runTreeAux] at hmem
    by_cases hbot : A.G = ⊥
    · rw [if_pos hbot] at hmem
      cases hmem
      exact hInv
    · rw [if_neg hbot] at hmem
      cases hmem with
      | root => exact hInv
      | child v h' =>
        exact ih (j + 1) (by omega) _
          (inv_child S _ _ hInv hbot (hwidth j (by omega))) h'

/-- **The composed payoff: the fuel-0-with-edges branch is never
taken.** Within the UQW budget (the margin at game radius `2R`, the
budget identity `ℓ = N(2s+2)`, the width at every depth), every arena
at which a run within its fuel bottoms out is edgeless: a leaf is
either the edgeless branch or fuel exhaustion, and the depth accounting
places fuel exhaustion exactly at depth `ℓ`, where
`eq_bot_of_inv_depth` applies. -/
theorem memLeaf_eq_bot (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {G₀ : SimpleGraph (Fin n₀)} {N : ℕ → ℕ} {s : ℕ}
    (hQ : Lax3Proofs.UqwInstantiation.SplitterMargin G₀ N s S.R)
    (hd : S.depth = N (2 * s + 2))
    (hwidth : ∀ i, i < S.depth → 1 + i * (2 * S.R + 1) ≤ S.width) :
    ∀ (k j : ℕ), j + k = S.depth → ∀ (A : Arena (S.pal j) n₀), Inv S G₀ j A →
      ∀ {j' : ℕ} {A' : Arena (S.pal j') n₀},
        MemLeaf S n₀ A' (runTreeAux S ord k j A) → A'.G = ⊥ := by
  intro k
  induction k with
  | zero =>
    intro j hj A hInv j' A' hmem
    rw [runTreeAux] at hmem
    cases hmem
    have hje : j = S.depth := by omega
    subst hje
    exact eq_bot_of_inv_depth S hQ hd hInv
  | succ k ih =>
    intro j hj A hInv j' A' hmem
    rw [runTreeAux] at hmem
    by_cases hbot : A.G = ⊥
    · rw [if_pos hbot] at hmem
      cases hmem
      exact hbot
    · rw [if_neg hbot] at hmem
      cases hmem with
      | child v h' =>
        exact ih (j + 1) (by omega) _
          (inv_child S _ _ hInv hbot (hwidth j (by omega))) h'

/-! ### At the campaign setup, on a member of the class -/

/-- The composed invariant at the campaign setup: on a run of `tables`
from the root arena of any input, every visited arena satisfies the
run invariant at its depth. (Membership of the class is not needed for
the threading — only for the leaf payoff below.) -/
theorem mkSetup_inv_of_memTree (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L)
    {j' : ℕ} {A' : Arena ((mkSetup C hC φ hφ choice).pal j') n}
    (h : MemTree (mkSetup C hC φ hφ choice) n A'
      (runTree (mkSetup C hC φ hφ choice) ord 0 (rootArena G col))) :
    Inv (mkSetup C hC φ hφ choice) G j' A' :=
  inv_of_memTree (mkSetup C hC φ hφ choice) ord
    (fun _ hi => mkSetup_width_le C hC φ hφ choice hi)
    ((mkSetup C hC φ hφ choice).depth - 0) 0 (by omega)
    (rootArena G col) (inv_root (mkSetup C hC φ hφ choice) G col) h

/-- Every arena a root run visits at depth `ℓ` is edgeless, on a member
of the class — the visited-node form of the payoff. -/
theorem mkSetup_memTree_depth_eq_bot (C : GraphClass) (hC : NowhereDense C)
    {q : ℕ} (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    {G : SimpleGraph (Fin n)} (hG : C n G) (col : Coloring n L)
    {j' : ℕ} {A' : Arena ((mkSetup C hC φ hφ choice).pal j') n}
    (h : MemTree (mkSetup C hC φ hφ choice) n A'
      (runTree (mkSetup C hC φ hφ choice) ord 0 (rootArena G col)))
    (hj' : j' = (mkSetup C hC φ hφ choice).depth) : A'.G = ⊥ :=
  mkSetup_eq_bot_of_inv_depth C hC φ hφ choice hG
    (hj' ▸ mkSetup_inv_of_memTree C hC φ hφ choice ord G col h)

/-- **E9's deferred composition, closed at the campaign setup**: on a
member of the class, every arena at which the run of `tables` from the
root bottoms out is edgeless — `tablesAux`'s fuel-0-with-edges branch
is never taken, at any node of any run on the class. -/
theorem mkSetup_memLeaf_eq_bot (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    {G : SimpleGraph (Fin n)} (hG : C n G) (col : Coloring n L)
    {j' : ℕ} {A' : Arena ((mkSetup C hC φ hφ choice).pal j') n}
    (h : MemLeaf (mkSetup C hC φ hφ choice) n A'
      (runTree (mkSetup C hC φ hφ choice) ord 0 (rootArena G col))) :
    A'.G = ⊥ :=
  memLeaf_eq_bot (mkSetup C hC φ hφ choice) ord
    (mkSetup_margin C hC φ hφ choice hG)
    (mkSetup_depth C hC φ hφ choice)
    (fun _ hi => mkSetup_width_le C hC φ hφ choice hi)
    ((mkSetup C hC φ hφ choice).depth - 0) 0 (by omega)
    (rootArena G col) (inv_root (mkSetup C hC φ hφ choice) G col) h

/-! ### The cost of the iterative form -/

open Classical in
/-- The charge of one frame: the body of `dcostAux`'s recursive case at
depth `j`, with the recursive charge abstracted into the oracle `next`.
The mirror of `frameEval` on the accounting side. -/
noncomputable def frameCost (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (c : ℝ) (j : ℕ) (next : Arena (S.pal (j + 1)) n₀ → ℝ)
    (A : Arena (S.pal j) n₀) : ℝ :=
  if A.G = ⊥ then c * (weight A : ℝ)
  else
    (ord A.N A.G).steps +
      ∑ u : Fin A.N,
        (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
          (c * (nodeCharge S j : ℝ)) *
              (weight (childArena S A ((ord A.N A.G).order) u) : ℝ)
            + next (childArena S A ((ord A.N A.G).order) u)
        else 0)

/-- The charge of the unrolled driver: `frameCost` per level, wired
exactly as `unrollAux`. -/
noncomputable def unrollCostAux (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (c : ℝ) : (k : ℕ) → (j : ℕ) → Arena (S.pal j) n₀ → ℝ
  | 0, _, A => c * (weight A : ℝ)
  | k + 1, j, A => frameCost S ord c j (unrollCostAux S ord c k (j + 1)) A

/-- The charge of the iterative form at a depth-`j` node, at fuel
`ℓ − j` — the mate of `Driver.dcost`. -/
noncomputable def unrolledCost (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (c : ℝ) (j : ℕ) (A : Arena (S.pal j) n₀) : ℝ :=
  unrollCostAux S ord c (S.depth - j) j A

/-- The iterative form's charge is `dcostAux` on the nose, at every
fuel — the same level-by-level mirroring as `unrollAux_eq_tablesAux`. -/
theorem unrollCostAux_eq_dcostAux (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (c : ℝ) : ∀ (k j : ℕ) (A : Arena (S.pal j) n₀),
      unrollCostAux (n₀ := n₀) S ord c k j A = dcostAux S ord c k j A := by
  intro k
  induction k with
  | zero => intro j A; rfl
  | succ k ih =>
    intro j A
    rw [unrollCostAux, dcostAux, frameCost]
    simp only [ih]

/-- **The charge of the iterative form equals `Driver.dcost`** — so
every cost theorem of `DriverCost` (`dcost_node_le`, `dcostAux_le`,
`dcost_root_le`, `mkSetup_dcost_root_le`) prices the unrolled driver
verbatim. -/
theorem unrolledCost_eq_dcost (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (c : ℝ) (j : ℕ) (A : Arena (S.pal j) n₀) :
    unrolledCost (n₀ := n₀) S ord c j A = dcost S ord c j A :=
  unrollCostAux_eq_dcostAux S ord c (S.depth - j) j A

end Lax3Proofs.Unroll
