import Lax11.GraphEncoding
import Lax3Proofs.DriverArena
import Lax13Proofs.Refine.Cost.ACost

/-!
# The CSR front end (F2) — parsing the endorsed axiom's input word

The endorsed axiom (`Lax3.ModelChecking.
exists_almostLinearTime_program_modelChecking`) hands the machine its
input as a CSR word `x : List ℕ` satisfying
`Lax11.GraphEncoding.EncodesGraph x n G`: two header entries `n, m`,
then `n + 1` offsets, then a target array of length `2m` listing each
vertex's block of neighbors. No module of `Lax3Proofs` before this one
turns such a word back into the driver's structures (`Headline.lean`
Part 3(b) records the gap). This file is that parse.

## §1 The parse

`EncodesGraph`'s adjacency clause (`adj_iff`) reads

    G.Adj u v ↔ ∃ j, offset x u ≤ j ∧ j < offset x (u+1) ∧ target x j = v

— membership of `v` in `u`'s block, here `blockMem x u v` (a bounded
search over `Finset.Ico`, hence decidable). On an *arbitrary* word
nothing forces this relation to be symmetric or irreflexive, so the
parse cleans it into a `SimpleGraph` the only way that is the identity
on genuine encodings: `parseGraphAt x n` has the edge `u ~ v` iff
`u ≠ v` and `v` is in `u`'s block *or* `u` is in `v`'s
(symmetrization + loop removal). On a word with `EncodesGraph x n G`
the clause `adj_iff` makes `blockMem` itself symmetric and loop-free —
`G.Adj` is — so the cleaning is invisible there and the recovery is
exact. `parse x` packages the whole front end: the declared vertex
count `vertexCount x` (header cell 0) and the parsed graph at that
count.

## §2 The round trip, and its slack

`parseGraphAt_eq : EncodesGraph x n G → parseGraphAt x n = G` — graph
*equality*, no adjacency slack: `adj_iff` is an iff, so the blocks
determine `G.Adj` completely and the parse inverts every admissible
encoding exactly. `parse_encodesGraph` restates it for the packaged
pair: `parse x = ⟨n, G⟩`. The slack `EncodesGraph` deliberately
permits lives entirely on the *word* side, not the graph side: blocks
may repeat neighbors and list them in any order, and `edgeCount x` is
only `≥ |E(G)|` (`Headline.ncard_edgeSet_le_edgeCount`), so `parse` is
far from injective and the declared `m` is *not* recoverable from `G`
— but `(n, G)` is recovered on the nose, which is the direction the
driver consumes.

## §3 The identity to the driver's root

`parse_rootArena`: on an encoding of `G`, the root arena built from
the parsed graph IS `Driver.rootArena G col` — so everything proved
against `rootArena G col` in `Headline`'s chain (`tables`, `MC`,
`dcost`) is a statement about the arena the front end materializes
from `x`. At the axiom's palette `L = 0` the coloring argument is
vacuous data: every `Coloring n 0` equals `trivialColoring n`
(`coloring_zero_eq`), so the identity at the trivial coloring
(`parse_rootArena_trivial`) loses nothing.

## §4 The charge (`O(x.length)` — in fact exactly `x.length`)

`chargeParse x` is the front end's account in the tower's cost algebra
(`ACost String ℕ`, `ImplBfs.chargeB0`'s house style): one linear
copying pass that materializes the root frame's state —

    parse.header    2                    (the two header cells)
    parse.offsets   vertexCount x + 1    (the offset array)
    parse.targets   2 * edgeCount x      (the target array)

`chargeParse_total` sums the three currencies to
`3 + vertexCount x + 2·edgeCount x`, and on a well-formed input
`length_eq` closes it to **exactly `x.length`**
(`chargeParse_total_eq_length`) — one cell read per cell of the word,
the linear charge `Headline` Part 3(b) asks the front end to carry.
The charge is stated abstractly rather than as an NREST program:
`parseGraphAt`/`blockMem` are *definitions of the value* (like
`ImplBfs.descend`, they re-search the word because that defines the
answer), while the machine's parse is a single pass laying the word
out in the frame; F6 programs that pass against this spec and this
charge. Per-adjacency-query costs after the parse belong to the
consumers reading the materialized arrays, not to the front end. The
axiom's word-size side condition (`c·(x.length+v+1)² ≤ 2^w`) is
likewise not consumed here — F6 spends it at codegen time.
-/

namespace Lax3Proofs.Impl

open Lax11.GraphEncoding
open Lax3.ColoredGraphs (Coloring)
open Lax13Proofs.Refine (ACost)

/-! ### §1 The parse -/

/-- **Block membership**: `v` occurs in the CSR block of `u` — the raw
adjacency relation the word stores, exactly the right-hand side of
`EncodesGraph.adj_iff` as a bounded (hence decidable) search. -/
def blockMem (x : List ℕ) (u v : ℕ) : Prop :=
  ∃ j ∈ Finset.Ico (offset x u) (offset x (u + 1)), target x j = v

instance instDecidableBlockMem (x : List ℕ) (u v : ℕ) :
    Decidable (blockMem x u v) := by
  unfold blockMem; infer_instance

/-- `blockMem` in the exact shape of `EncodesGraph.adj_iff`'s
right-hand side. -/
theorem blockMem_iff (x : List ℕ) (u v : ℕ) :
    blockMem x u v ↔
      ∃ j, offset x u ≤ j ∧ j < offset x (u + 1) ∧ target x j = v := by
  simp [blockMem, Finset.mem_Ico, and_assoc]

/-- **The parsed graph at a given carrier size**: the adjacency the
word's blocks encode, symmetrized and loop-cleaned. On a word
satisfying `EncodesGraph x n G` the cleaning is the identity
(`parseGraphAt_eq`): `adj_iff` makes the raw block relation symmetric
and irreflexive because `G.Adj` is. -/
def parseGraphAt (x : List ℕ) (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (blockMem x u v ∨ blockMem x v u)
  symm := by
    rintro u v ⟨hne, h⟩
    exact ⟨hne.symm, h.symm⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance instDecidableRelParseAdj (x : List ℕ) (n : ℕ) :
    DecidableRel (parseGraphAt x n).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (blockMem x u v ∨ blockMem x v u)))

/-- The parsed graph at the word's own declared vertex count. -/
def parseGraph (x : List ℕ) : SimpleGraph (Fin (vertexCount x)) :=
  parseGraphAt x (vertexCount x)

/-- **The parse**: from a word, the declared vertex count (header cell
0) and the graph its blocks encode — the front end's whole output, in
the root-arena vocabulary `(n, SimpleGraph (Fin n))`. -/
def parse (x : List ℕ) : (n : ℕ) × SimpleGraph (Fin n) :=
  ⟨vertexCount x, parseGraph x⟩

/-! ### §2 The round trip -/

/-- On an encoding of `G`, block membership IS adjacency — `adj_iff`
read through `blockMem`. -/
theorem blockMem_iff_adj {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : EncodesGraph x n G) (u v : Fin n) :
    blockMem x ↑u ↑v ↔ G.Adj u v := by
  rw [blockMem_iff, ← h.adj_iff u v]

/-- **The round trip, exactly**: the parse at the encoded vertex count
recovers the encoded graph — graph equality, no adjacency slack, since
`adj_iff` pins `G.Adj` to the blocks completely. (The word-side slack
`EncodesGraph` permits — repeated neighbors, unordered blocks, a
declared `edgeCount` exceeding `|E(G)|` — makes `parse` non-injective
but does not disturb this direction.) -/
theorem parseGraphAt_eq {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : EncodesGraph x n G) : parseGraphAt x n = G := by
  ext u v
  show (u ≠ v ∧ (blockMem x ↑u ↑v ∨ blockMem x ↑v ↑u)) ↔ G.Adj u v
  rw [blockMem_iff_adj h u v, blockMem_iff_adj h v u]
  constructor
  · rintro ⟨-, hadj | hadj⟩
    · exact hadj
    · exact hadj.symm
  · exact fun hadj => ⟨G.ne_of_adj hadj, Or.inl hadj⟩

/-- The round trip for the packaged pair: the parse of an encoding of
`(n, G)` is `⟨n, G⟩`. -/
theorem parse_encodesGraph {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : EncodesGraph x n G) : parse x = ⟨n, G⟩ := by
  have hn : vertexCount x = n := h.vertexCount_eq
  subst hn
  simp only [parse, parseGraph, parseGraphAt_eq h]

/-! ### §3 The identity to the driver's root -/

/-- The trivial coloring at the empty palette — the axiom's graphs are
uncolored, and `L = 0` has no color rows to fill. -/
def trivialColoring (n : ℕ) : Coloring n 0 := fun i => i.elim0

/-- Every coloring of the empty palette is the trivial one: the
coloring argument at `L = 0` is vacuous data. -/
theorem coloring_zero_eq {n : ℕ} (col : Coloring n 0) :
    col = trivialColoring n :=
  funext fun i => i.elim0

/-- **The front end lands on the driver's root**: on an encoding of
`G`, the root arena built from the parsed graph is `Driver.rootArena G
col` — the object `Headline`'s whole chain (`tables`, `MC`, `dcost`)
is stated against. -/
theorem parse_rootArena {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : EncodesGraph x n G) (col : Coloring n 0) :
    Driver.rootArena (parseGraphAt x n) col = Driver.rootArena G col := by
  rw [parseGraphAt_eq h]

/-- `parse_rootArena` at the trivial coloring — by `coloring_zero_eq`
this specialization loses nothing. -/
theorem parse_rootArena_trivial {x : List ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} (h : EncodesGraph x n G) :
    Driver.rootArena (parseGraphAt x n) (trivialColoring n) =
      Driver.rootArena G (trivialColoring n) :=
  parse_rootArena h (trivialColoring n)

/-! ### §4 The charge -/

/-- **The front end's charge**: one linear pass over the word,
materializing the root frame's state — the two header cells, the
`n + 1` offsets, the `2m` targets. Stated abstractly in the tower's
cost algebra (`chargeB0`'s house style); F6 programs the pass against
this account. -/
def chargeParse (x : List ℕ) : ACost String ℕ :=
  ACost.cost "parse.header" 2 + ACost.cost "parse.offsets" (vertexCount x + 1)
    + ACost.cost "parse.targets" (2 * edgeCount x)

@[simp] theorem chargeParse_apply_header (x : List ℕ) :
    (chargeParse x).toFun "parse.header" = 2 := by
  simp [chargeParse]

@[simp] theorem chargeParse_apply_offsets (x : List ℕ) :
    (chargeParse x).toFun "parse.offsets" = vertexCount x + 1 := by
  simp [chargeParse]

@[simp] theorem chargeParse_apply_targets (x : List ℕ) :
    (chargeParse x).toFun "parse.targets" = 2 * edgeCount x := by
  simp [chargeParse]

/-- Every currency other than the three named ones is uncharged. -/
theorem chargeParse_apply_ne (x : List ℕ) (key : String)
    (h₁ : key ≠ "parse.header") (h₂ : key ≠ "parse.offsets")
    (h₃ : key ≠ "parse.targets") : (chargeParse x).toFun key = 0 := by
  simp [chargeParse, h₁, h₂, h₃]

/-- The whole account: the three currencies sum to
`3 + vertexCount x + 2·edgeCount x` — the word's declared layout size,
one read per cell. -/
theorem chargeParse_total (x : List ℕ) :
    (chargeParse x).toFun "parse.header"
      + (chargeParse x).toFun "parse.offsets"
      + (chargeParse x).toFun "parse.targets"
      = 3 + vertexCount x + 2 * edgeCount x := by
  simp
  omega

/-- **The charge is linear in the input — exactly `x.length`**: on a
well-formed word, `length_eq` closes the account to one read per cell
of the word, the `O(x.length)` shape the assembled program's
accounting (Headline Part 3(b)/(e)) consumes. -/
theorem chargeParse_total_eq_length {x : List ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} (h : EncodesGraph x n G) :
    (chargeParse x).toFun "parse.header"
      + (chargeParse x).toFun "parse.offsets"
      + (chargeParse x).toFun "parse.targets" = x.length := by
  rw [chargeParse_total, h.vertexCount_eq, h.length_eq]

end Lax3Proofs.Impl
