import Lax3Proofs.SolveSweepOrder

/-!
# F6c12 — the delete program, and the min-degree peel pass

`SolveSweepAdj`'s §3 names two contracts for the machine wave and
proves neither ("Both are contracts for the machine wave; nothing here
proves a program"). This file owns the **delete** one, and
`SolveSweepOrder`'s **`CovMdPeelIn`** — the min-degree peel — on top of
it. It also carries a finding about the delete contract as landed.

## Finding — `AdjDeleteIn` as landed is false, for every `B`

`not_adjDeleteIn` (§7) proves `¬ AdjDeleteIn B ao aj dg mt vx delC kd`
for **every** word bound `B`, **every** program `delC` and **every**
budget `kd`, whenever the four region names are distinct.

The defect is in the statement, not the algorithm. `AdjDeleteIn`
quantifies over every carrier size `N`, every graph and every state
satisfying `DelAdjSt`, and relates none of them to `B`. So it also
speaks about `N = B + 2` and the graph whose only edge joins the
vertices `B` and `B + 1`: the region exists, `dg` holds `1` at index
`B`, and the postcondition demands `0` there. Writing that cell needs a
store whose index expression evaluates to `B`; under `Run B` every
value an expression produces is `< B` (`bigStepB_getElem?_high`), so
*no* program can perform it. The sibling `AdjBuildIn` has the same
shape and is presumably affected the same way; that contract is another
worker's and is not touched here.

`AdjDeleteInW` (§6) is `AdjDeleteIn` with the single missing hypothesis
`N + N² < B` — the closed form of "every slot index fits in a word",
since the slot space is at most `N²` cells wide (`offF_le_sq`). Nothing
else is changed: same precondition, same postcondition, same budget
shape. `adjDeleteInW_delAdjCom` proves it for `delAdjCom` at
`kd d = 54·d + 5`, affine in `v`'s *current* degree as the contract
asks.

The bound is not an extra obligation for the sweep: at the peel's own
word bound `mcB q x = q·(|x|+1)²` it follows from `1 ≤ q` and
`A.N ≤ n < |x|` alone, and §10 discharges it there.

## The delete (§1–§7)

* §1 `AdjFrame`/`AdjCore` — `DelAdjSt` split into its shape clauses
  (offsets and allocations, which no mutating pass touches) and its
  content clauses at an explicit *current* graph. `delAdjSt_iff` is the
  equivalence: the landed invariant's separate treatment of the deleted
  set is exactly the content clauses at `deleteVerts G S`, because
  `deleteVerts` isolates and an isolated vertex's current degree is
  already `0`.
* §2 the geometry of the slot space: distinct rows are disjoint
  (`offF_slot_ne`), a live slot is inside the space (`offF_slot_lt`),
  the space is `≤ N²` wide (`offF_le_sq`), and a live prefix is
  duplicate-free (`AdjCore.slot_inj`, the landed `DelAdjSt.slot_injOn`
  pigeonhole at this shape). No no-duplicates clause is *carried*
  anywhere.
* §3 `cutTo H v T` — `H` with `v`'s neighbourhood cut down to `T`. The
  delete loop passes through these states and no others, which is what
  lets its invariant be a genuine region invariant rather than a
  bespoke half-deleted one: the loop peels `v`'s row **from the end**,
  so `dg[v]` shrinks in step with the graph.
* §4 `adjCore_unlink` — one turn, at the region level. The mate repair
  is the four-way round trip of `SolveSweepAdj:166-172` re-established
  at the *moved* copy: `mt` at the vacated slot `p` and at the moved
  edge's far end `q` name each other, and `aj` at both ends still names
  the opposite endpoint. The degenerate case — `v` sitting at its
  neighbour's own last live slot — needs no branch: both writes are
  then identities on the live prefix and both slots leave the live
  range in the same turn.
* §5–§6 the program `delAdjCom`, its loop and `AdjDeleteInW`.
* §7 the finding above.

## The peel (§8–§10)

* §8 the two places the pass can go silently wrong, isolated:
  `eq_minDegVert` (the tie-break: a live vertex minimising the live
  degree and `≤` every other minimiser *is* `minDegVert`'s
  `Finset.min'`) and `mdRankAux_peel_step` (the countdown: the round's
  vertex gets `S.card - 1`, so the first vertex peeled from a live set
  of `N` gets `N - 1`, and every survivor keeps its whole-peel rank).
  `ncard_neighborSet_deleteVerts_compl` identifies the region's live
  degree with `mdRankAux`'s `nbrsIn`.
* §9 the programs. `peelKey` folds liveness and degree into **one**
  comparison: a live vertex still holds the sentinel `N` in its rank
  cell, so its key is its live degree (`< N`), while a ranked vertex
  contributes at least one full `N`. One scan, one `<` test, least
  index wins. `peelCom_spec` leaves `RankArr (mdPerm F)` — the
  routine's order, definitionally, since `(mdPerm F v : ℕ) = mdRank F v`
  by `rfl`.
* §10 `covMdPeelIn_peelCom` discharges `CovMdPeelIn` verbatim.

## The budget, honestly

`Kmp j A = 86·A.N² + 43·A.N + 14`. The `N²` is a **full scan of the
carrier per round**, not the bucket queue over degrees the residual's
docstring mentions; that amortization is not proved here. Each round's
delete costs `54·d + 5` in `v`'s current degree and is absorbed by the
scan term. A discharger who needs the sweep's `2·D²·N` envelope should
price this `N²` against it rather than assume the `O(1)` minimum.

The scratch descriptor the pass asks for is
`Smp j σ := n ≤ (σ.arrs (ra j)).length` — the rank region's allocation
and nothing else, so the augmentation pass preserves it for free
(array lengths are invariant under `Run`).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.SplitterBasics (deleteVerts_adj)

/-! ## §1 The region at an explicit offset function and current graph -/

/-- The three *shape* clauses of `DelAdjSt`: the offset function, the
offset region, and the three allocations. None of them is touched by a
mutating pass. -/
def AdjFrame (ao aj dg mt : String) {N : ℕ} (offF : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (σ : Env) : Prop :=
  offF 0 = 0 ∧
  (∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) ∧
  N + 1 ≤ (σ.arrs ao).length ∧
  (∀ i, i ≤ N → (σ.arrs ao).getD i 0 = offF i) ∧
  offF N ≤ (σ.arrs aj).length ∧
  offF N ≤ (σ.arrs mt).length ∧
  N ≤ (σ.arrs dg).length

/-- The three *content* clauses of `DelAdjSt`, at an explicit offset
function and an explicit current graph `H`: the degree clause, per-slot
soundness with a consistent mate, and completeness. Isolated vertices
need no separate clause — a vertex with no `H`-neighbour has live
length `0`, and both remaining clauses are then vacuous at it. -/
def AdjCore (aj dg mt : String) {N : ℕ} (offF : ℕ → ℕ)
    (H : SimpleGraph (Fin N)) (σ : Env) : Prop :=
  (∀ u : Fin N, (σ.arrs dg).getD (u : ℕ) 0 = (H.neighborSet u).ncard) ∧
  (∀ u : Fin N, ∀ t : ℕ, t < (σ.arrs dg).getD (u : ℕ) 0 →
    ∃ z : Fin N, H.Adj u z ∧ (σ.arrs aj).getD (offF (u : ℕ) + t) 0 = (z : ℕ) ∧
      ∃ s : ℕ, s < (σ.arrs dg).getD (z : ℕ) 0 ∧
        (σ.arrs mt).getD (offF (u : ℕ) + t) 0 = offF (z : ℕ) + s ∧
        (σ.arrs aj).getD (offF (z : ℕ) + s) 0 = (u : ℕ) ∧
        (σ.arrs mt).getD (offF (z : ℕ) + s) 0 = offF (u : ℕ) + t) ∧
  (∀ u z : Fin N, H.Adj u z →
    ∃ t : ℕ, t < (σ.arrs dg).getD (u : ℕ) 0 ∧
      (σ.arrs aj).getD (offF (u : ℕ) + t) 0 = (z : ℕ))

/-- A vertex of the deleted set is isolated, so the two forms of the
degree clause agree. -/
theorem ncard_neighborSet_deleteVerts_eq_zero {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Set (Fin N)} {v : Fin N} (hv : v ∈ S) :
    ((deleteVerts G S).neighborSet v).ncard = 0 := by
  have : (deleteVerts G S).neighborSet v = ∅ := by
    ext z
    simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
    intro h
    exact (deleteVerts_adj.mp h).2.1 hv
  rw [this, Set.ncard_empty]

/-- **`DelAdjSt`, split into shape and content.** The `S`-clauses of the
landed invariant are exactly the content clauses at
`H := deleteVerts G S`: a deleted vertex is isolated there, so its live
length `0` *is* its current degree, and soundness and completeness are
vacuous at it. -/
theorem delAdjSt_iff {ao aj dg mt : String} {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Set (Fin N)} {σ : Env} :
    DelAdjSt ao aj dg mt G S σ ↔
      ∃ offF : ℕ → ℕ, AdjFrame ao aj dg mt offF G σ ∧
        AdjCore aj dg mt offF (deleteVerts G S) σ := by
  constructor
  · rintro ⟨offF, h0, hstep, hao, haoR, haj, hmt, hdg, hdead, hdeg, hsound, hcomp⟩
    refine ⟨offF, ⟨h0, hstep, hao, haoR, haj, hmt, hdg⟩, ?_, ?_, ?_⟩
    · intro u
      by_cases hu : u ∈ S
      · rw [hdead u hu, ncard_neighborSet_deleteVerts_eq_zero hu]
      · exact hdeg u hu
    · intro u t ht
      by_cases hu : u ∈ S
      · rw [hdead u hu] at ht; omega
      · exact hsound u hu t ht
    · intro u z hz
      exact hcomp u (deleteVerts_adj.mp hz).2.1 z hz
  · rintro ⟨offF, ⟨h0, hstep, hao, haoR, haj, hmt, hdg⟩, hdeg, hsound, hcomp⟩
    refine ⟨offF, h0, hstep, hao, haoR, haj, hmt, hdg, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [hdeg v, ncard_neighborSet_deleteVerts_eq_zero hv]
    · intro v _
      exact hdeg v
    · intro v _ t ht
      exact hsound v t ht
    · intro v _ z hz
      exact hcomp v z hz

/-! ## §2 The geometry of the slot space -/

/-- Two distinct rows of the base CSR are disjoint: the slot of row `x`
at offset `a` is never the slot of row `y` at offset `b`. -/
theorem offF_slot_ne {N : ℕ} {G : SimpleGraph (Fin N)} {offF : ℕ → ℕ}
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    {x y : Fin N} (hxy : x ≠ y) {a b : ℕ}
    (ha : a < (G.neighborSet x).ncard) (hb : b < (G.neighborSet y).ncard) :
    offF (x : ℕ) + a ≠ offF (y : ℕ) + b := by
  have key : ∀ x y : Fin N, (x : ℕ) < (y : ℕ) → ∀ a b : ℕ,
      a < (G.neighborSet x).ncard → offF (x : ℕ) + a ≠ offF (y : ℕ) + b := by
    intro x y hlt a b ha
    have h1 : offF (x : ℕ) + a < offF ((x : ℕ) + 1) := by rw [hstep x]; omega
    have h2 : offF ((x : ℕ) + 1) ≤ offF (y : ℕ) :=
      offF_mono hstep (y : ℕ) (le_of_lt y.isLt) ((x : ℕ) + 1) (by omega)
    omega
  rcases lt_trichotomy (x : ℕ) (y : ℕ) with h | h | h
  · exact key x y h a b ha
  · exact absurd (Fin.ext h) hxy
  · exact fun hc => key y x h b a hb hc.symm

/-- A live slot of a row lies inside the slot space. -/
theorem offF_slot_lt {N : ℕ} {G : SimpleGraph (Fin N)} {offF : ℕ → ℕ}
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    {x : Fin N} {a : ℕ} (ha : a < (G.neighborSet x).ncard) :
    offF (x : ℕ) + a < offF N := by
  have h1 : offF (x : ℕ) + a < offF ((x : ℕ) + 1) := by rw [hstep x]; omega
  exact lt_of_lt_of_le h1 (offF_mono hstep N le_rfl ((x : ℕ) + 1) x.isLt)

/-- The slot space is at most `N²` cells wide — the word bound of every
index a mutating pass computes, in a closed form. -/
theorem offF_le_sq {N : ℕ} {G : SimpleGraph (Fin N)} {offF : ℕ → ℕ}
    (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    ∀ i, i ≤ N → offF i ≤ i * N := by
  intro i
  induction i with
  | zero => intro _; rw [h0]; omega
  | succ k ih =>
      intro hk
      have hkN : k < N := hk
      have hdeg : (G.neighborSet ⟨k, hkN⟩).ncard ≤ N := by
        have := Set.ncard_le_ncard (Set.subset_univ (G.neighborSet ⟨k, hkN⟩))
          (Set.toFinite _)
        simpa using this
      have := ih (by omega)
      rw [hstep ⟨k, hkN⟩]
      calc offF k + (G.neighborSet ⟨k, hkN⟩).ncard ≤ k * N + N := by omega
        _ = (k + 1) * N := by ring

/-- A live prefix has no duplicates (pigeonhole, as for the landed
region): completeness makes the current neighbourhood a subset of the
image of the prefix, and the degree clause equates the cardinalities. -/
theorem AdjCore.slot_inj {aj dg mt : String} {N : ℕ} {offF : ℕ → ℕ}
    {H : SimpleGraph (Fin N)} {σ : Env} (h : AdjCore aj dg mt offF H σ)
    (u : Fin N) {a b : ℕ} (ha : a < (σ.arrs dg).getD (u : ℕ) 0)
    (hb : b < (σ.arrs dg).getD (u : ℕ) 0)
    (hab : (σ.arrs aj).getD (offF (u : ℕ) + a) 0
      = (σ.arrs aj).getD (offF (u : ℕ) + b) 0) : a = b := by
  classical
  obtain ⟨hdeg, -, hcomp⟩ := h
  have hdv := hdeg u
  have h1 : (Fin.val '' (H.neighborSet u)) ⊆
      ↑((Finset.range ((σ.arrs dg).getD (u : ℕ) 0)).image
        (fun t => (σ.arrs aj).getD (offF (u : ℕ) + t) 0)) := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨t, ht, hval⟩ := hcomp u z hz
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, hval⟩)
  have h2 : (σ.arrs dg).getD (u : ℕ) 0 ≤
      ((Finset.range ((σ.arrs dg).getD (u : ℕ) 0)).image
        (fun t => (σ.arrs aj).getD (offF (u : ℕ) + t) 0)).card :=
    calc (σ.arrs dg).getD (u : ℕ) 0
        = (H.neighborSet u).ncard := hdv
      _ = (Fin.val '' (H.neighborSet u)).ncard :=
          (Set.ncard_image_of_injective _ Fin.val_injective).symm
      _ ≤ _ := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ((Finset.range ((σ.arrs dg).getD (u : ℕ) 0)).image
      (fun t => (σ.arrs aj).getD (offF (u : ℕ) + t) 0)).card =
        (Finset.range ((σ.arrs dg).getD (u : ℕ) 0)).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_range]; exact h2)
  exact Finset.injOn_of_card_image_eq h3 (Finset.mem_coe.mpr (Finset.mem_range.mpr ha))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hb)) hab

/-! ## §3 One vertex's neighbourhood, cut down -/

/-- `H` with the neighbourhood of `v` cut down to `T` — the shape of the
partially-deleted state the delete loop passes through: `v`'s row has
been unlinked from the neighbours outside `T` and from nothing else. -/
def cutTo {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) (T : Set (Fin N)) :
    SimpleGraph (Fin N) where
  Adj a b := H.Adj a b ∧ (a = v → b ∈ T) ∧ (b = v → a ∈ T)
  symm := fun {_ _} h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun a h => H.loopless.irrefl a h.1⟩

theorem cutTo_adj {N : ℕ} {H : SimpleGraph (Fin N)} {v : Fin N} {T : Set (Fin N)}
    {a b : Fin N} :
    (cutTo H v T).Adj a b ↔ H.Adj a b ∧ (a = v → b ∈ T) ∧ (b = v → a ∈ T) := Iff.rfl

theorem cutTo_le {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) (T : Set (Fin N)) :
    cutTo H v T ≤ H := fun _ _ h => h.1

/-- Cutting to the whole neighbourhood changes nothing. -/
theorem cutTo_self {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) :
    cutTo H v (H.neighborSet v) = H := by
  ext a b
  refine ⟨fun h => h.1, fun h => cutTo_adj.mpr ⟨h, ?_, ?_⟩⟩
  · rintro rfl; exact h
  · rintro rfl; exact h.symm

/-- Cutting to nothing isolates `v`. -/
theorem cutTo_empty {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) :
    cutTo H v (∅ : Set (Fin N)) = deleteVerts H {v} := by
  ext a b
  simp only [cutTo_adj, deleteVerts_adj, Set.mem_empty_iff_false, imp_false,
    Set.mem_singleton_iff]

/-- Isolating one more vertex of `G` is cutting the isolation of `S` at
that vertex. -/
theorem deleteVerts_insert {N : ℕ} (G : SimpleGraph (Fin N)) (S : Set (Fin N))
    (v : Fin N) :
    deleteVerts G (S ∪ {v}) = cutTo (deleteVerts G S) v (∅ : Set (Fin N)) := by
  ext a b
  simp only [cutTo_adj, deleteVerts_adj, Set.mem_empty_iff_false, imp_false,
    Set.mem_union, Set.mem_singleton_iff, not_or]
  tauto

/-- The cut neighbourhood at `v` itself. -/
theorem neighborSet_cutTo_self {N : ℕ} {H : SimpleGraph (Fin N)} {v : Fin N}
    {T : Set (Fin N)} (hT : T ⊆ H.neighborSet v) :
    (cutTo H v T).neighborSet v = T := by
  ext z
  constructor
  · intro hz
    exact (cutTo_adj.mp hz).2.1 rfl
  · intro hz
    refine cutTo_adj.mpr ⟨hT hz, fun _ => hz, ?_⟩
    rintro rfl
    exact hz

/-- Away from `v` the cut only forbids `v` itself as a neighbour of the
vertices outside `T`. -/
theorem neighborSet_cutTo_of_ne {N : ℕ} {H : SimpleGraph (Fin N)} {v : Fin N}
    {T : Set (Fin N)} {x : Fin N} (hx : x ≠ v) :
    (cutTo H v T).neighborSet x = {z | H.Adj x z ∧ (z = v → x ∈ T)} := by
  ext z
  constructor
  · intro hz
    exact ⟨(cutTo_adj.mp hz).1, (cutTo_adj.mp hz).2.2⟩
  · intro hz
    exact cutTo_adj.mpr ⟨hz.1, fun hc => absurd hc hx, hz.2⟩

/-- Removing one element of a finite set drops its cardinality by one. -/
theorem ncard_sdiff_singleton {N : ℕ} {T : Set (Fin N)} {a : Fin N} (h : a ∈ T) :
    (T \ {a}).ncard + 1 = T.ncard := by
  rw [← Set.ncard_insert_of_notMem (fun hc => hc.2 rfl), Set.insert_diff_singleton,
    Set.insert_eq_of_mem h]


/-! ## §4 The unlink step -/

set_option maxHeartbeats 1000000 in
/-- **One turn of the swap-delete**, at the region level and with the
four writes given as their read-back equations. The state holds the
region at `cutTo H v T` with `v`'s live length `i + 1`; `w` is the
vertex at `v`'s last live slot, `p` its mate slot (the copy of `v` in
`w`'s row), `d` is `w`'s live length, `u` the vertex at `w`'s last live
slot and `q` its mate slot. Writing `u` into `p`, re-pointing the two
mate cells of the moved copy at each other, and shrinking both `dg[w]`
and `dg[v]` leaves the region at `cutTo H v (T \ {w})` — `v` unlinked
from `w`, and nothing else changed.

The four-way round trip of `SolveSweepAdj`'s mate clause is
re-established at the *moved* copy as well: `mt` at `p` and at `q` name
each other, and `aj` at both ends still names the opposite endpoint.
The degenerate case `p = l` — `v` sitting at `w`'s own last live slot —
needs no branch: the two `aj`/`mt` writes are then identities on the
live prefix, and both slots leave the live range in the same turn. -/
theorem adjCore_unlink {aj dg mt : String} {N : ℕ} {offF : ℕ → ℕ}
    {G H : SimpleGraph (Fin N)}
    (hstep : ∀ x : Fin N, offF ((x : ℕ) + 1) = offF (x : ℕ) + (G.neighborSet x).ncard)
    (hHG : H ≤ G) {v : Fin N} {T : Set (Fin N)} (hT : T ⊆ H.neighborSet v)
    {σ σ' : Env} (hcore : AdjCore aj dg mt offF (cutTo H v T) σ)
    {i : ℕ} (hdgv : (σ.arrs dg).getD (v : ℕ) 0 = i + 1)
    {w u : Fin N} {p q d : ℕ}
    (hw : (σ.arrs aj).getD (offF (v : ℕ) + i) 0 = (w : ℕ))
    (hp : (σ.arrs mt).getD (offF (v : ℕ) + i) 0 = p)
    (hd : (σ.arrs dg).getD (w : ℕ) 0 = d)
    (hu : (σ.arrs aj).getD (offF (w : ℕ) + (d - 1)) 0 = (u : ℕ))
    (hq : (σ.arrs mt).getD (offF (w : ℕ) + (d - 1)) 0 = q)
    (hajp : (σ'.arrs aj).getD p 0 = (u : ℕ))
    (hajo : ∀ k, k ≠ p → (σ'.arrs aj).getD k 0 = (σ.arrs aj).getD k 0)
    (hmtp : (σ'.arrs mt).getD p 0 = q)
    (hmtq : (σ'.arrs mt).getD q 0 = p)
    (hmto : ∀ k, k ≠ p → k ≠ q → (σ'.arrs mt).getD k 0 = (σ.arrs mt).getD k 0)
    (hdgv' : (σ'.arrs dg).getD (v : ℕ) 0 = i)
    (hdgw' : (σ'.arrs dg).getD (w : ℕ) 0 = d - 1)
    (hdgo : ∀ y : Fin N, y ≠ v → y ≠ w →
      (σ'.arrs dg).getD (y : ℕ) 0 = (σ.arrs dg).getD (y : ℕ) 0) :
    AdjCore aj dg mt offF (cutTo H v (T \ {w})) σ' := by
  classical
  have hinj := AdjCore.slot_inj hcore
  obtain ⟨hdeg, hsound, hcomp⟩ := hcore
  -- the current degrees fit the base rows, so distinct rows are disjoint
  have hfit : ∀ x : Fin N, (σ.arrs dg).getD (x : ℕ) 0 ≤ (G.neighborSet x).ncard := by
    intro x
    rw [hdeg x]
    exact Set.ncard_le_ncard (fun _ hz => hHG hz.1) (Set.toFinite _)
  have hrow : ∀ x y : Fin N, x ≠ y → ∀ a b : ℕ,
      a < (σ.arrs dg).getD (x : ℕ) 0 → b < (σ.arrs dg).getD (y : ℕ) 0 →
      offF (x : ℕ) + a ≠ offF (y : ℕ) + b :=
    fun x y hxy a b ha hb =>
      offF_slot_ne hstep hxy (lt_of_lt_of_le ha (hfit x)) (lt_of_lt_of_le hb (hfit y))
  -- `v`'s last live slot, and the copy of `v` in `w`'s row
  have hilt : i < (σ.arrs dg).getD (v : ℕ) 0 := by omega
  obtain ⟨w0, hKvw, hajv0, s, hs, hmtv0, hajw0, hmtw0⟩ := hsound v i hilt
  have hw0 : w0 = w := Fin.val_injective (by rw [← hajv0, hw])
  rw [hw0] at hKvw hs hmtv0 hajw0 hmtw0
  have hp' : p = offF (w : ℕ) + s := by rw [← hp]; exact hmtv0
  rw [hd] at hs
  -- `w`'s last live slot, and the mate of the copy it holds
  have hd1 : d - 1 < (σ.arrs dg).getD (w : ℕ) 0 := by rw [hd]; omega
  obtain ⟨u0, hKwu, hajl0, s2, hs2, hmtl0, hajq0, hmtq0⟩ := hsound w (d - 1) hd1
  have hu0 : u0 = u := Fin.val_injective (by rw [← hajl0, hu])
  rw [hu0] at hKwu hs2 hmtl0 hajq0 hmtq0
  have hq' : q = offF (u : ℕ) + s2 := by rw [← hq]; exact hmtl0
  have hvw : v ≠ w := hKvw.ne
  have hwu : w ≠ u := hKwu.ne
  have hwT : w ∈ T := (cutTo_adj.mp hKvw).2.1 rfl
  -- reading a slot index back as a row and an offset
  have hkp : ∀ (x : Fin N) (t : ℕ), t < (σ.arrs dg).getD (x : ℕ) 0 →
      offF (x : ℕ) + t = p → x = w ∧ t = s := by
    intro x t ht hc
    rw [hp'] at hc
    have hxw : x = w := by
      by_contra hne
      exact hrow x w hne t s ht (by rw [hd]; exact hs) hc
    refine ⟨hxw, ?_⟩
    rw [hxw] at hc
    omega
  have hkq : ∀ (x : Fin N) (t : ℕ), t < (σ.arrs dg).getD (x : ℕ) 0 →
      offF (x : ℕ) + t = q → x = u ∧ t = s2 := by
    intro x t ht hc
    rw [hq'] at hc
    have hxu : x = u := by
      by_contra hne
      exact hrow x u hne t s2 ht hs2 hc
    refine ⟨hxu, ?_⟩
    rw [hxu] at hc
    omega
  have hpq : p ≠ q := by
    intro hc
    have h1 : (σ.arrs aj).getD p 0 = (v : ℕ) := by rw [hp']; exact hajw0
    have h2 : (σ.arrs aj).getD q 0 = (w : ℕ) := by rw [hq']; exact hajq0
    rw [hc, h2] at h1
    exact hvw (Fin.val_injective h1).symm
  -- the degenerate case, characterised
  have huv_iff : u = v ↔ s = d - 1 := by
    constructor
    · intro huv
      refine hinj w (by rw [hd]; exact hs) (by rw [hd]; omega) ?_
      rw [hajw0, hu, huv]
    · intro hsd1
      exact Fin.val_injective (by rw [← hu, ← hsd1]; exact hajw0)
  have hdgle : ∀ x : Fin N, (σ'.arrs dg).getD (x : ℕ) 0 ≤ (σ.arrs dg).getD (x : ℕ) 0 := by
    intro x
    by_cases hxv : x = v
    · rw [hxv, hdgv', hdgv]; omega
    by_cases hxw : x = w
    · rw [hxw, hdgw', hd]; omega
    · rw [hdgo x hxv hxw]
  -- the three neighbourhood identities
  have hT' : T \ {w} ⊆ H.neighborSet v := fun _ hz => hT hz.1
  have hnv : (cutTo H v (T \ {w})).neighborSet v = T \ {w} := neighborSet_cutTo_self hT'
  have hnvT : (cutTo H v T).neighborSet v = T := neighborSet_cutTo_self hT
  have hnw : (cutTo H v (T \ {w})).neighborSet w
      = (cutTo H v T).neighborSet w \ {v} := by
    rw [neighborSet_cutTo_of_ne (Ne.symm hvw), neighborSet_cutTo_of_ne (Ne.symm hvw)]
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun _ => hwT⟩, ?_⟩
      intro hzv
      exact (h2 hzv).2 rfl
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, fun hzv => absurd hzv h2⟩
  have hnx : ∀ x : Fin N, x ≠ v → x ≠ w →
      (cutTo H v (T \ {w})).neighborSet x = (cutTo H v T).neighborSet x := by
    intro x hxv hxw
    rw [neighborSet_cutTo_of_ne hxv, neighborSet_cutTo_of_ne hxv]
    ext z
    exact ⟨fun h => ⟨h.1, fun hzv => (h.2 hzv).1⟩,
      fun h => ⟨h.1, fun hzv => ⟨h.2 hzv, hxw⟩⟩⟩
  have hwu_new : u ≠ v → (cutTo H v (T \ {w})).Adj w u := by
    intro hne
    have hmem : u ∈ (cutTo H v (T \ {w})).neighborSet w := by
      rw [hnw]; exact ⟨hKwu, hne⟩
    exact hmem
  refine ⟨?_, ?_, ?_⟩
  · -- the degree clause
    intro x
    by_cases hxv : x = v
    · rw [hxv, hdgv', hnv]
      have hTc : T.ncard = i + 1 := by rw [← hnvT, ← hdeg v]; exact hdgv
      have h2 := ncard_sdiff_singleton (T := T) (a := w) hwT
      omega
    by_cases hxw : x = w
    · rw [hxw, hdgw', hnw]
      have hmem : v ∈ (cutTo H v T).neighborSet w := hKvw.symm
      have h2 := ncard_sdiff_singleton (T := (cutTo H v T).neighborSet w) (a := v) hmem
      have h3 : ((cutTo H v T).neighborSet w).ncard = d := by rw [← hdeg w]; exact hd
      omega
    · rw [hdgo x hxv hxw, hnx x hxv hxw]; exact hdeg x
  · -- soundness with a consistent mate
    intro x t ht
    have ht0 : t < (σ.arrs dg).getD (x : ℕ) 0 := lt_of_lt_of_le ht (hdgle x)
    by_cases hcp : offF (x : ℕ) + t = p
    · -- the vacated slot, now holding the moved copy
      obtain ⟨hxw, hts⟩ := hkp x t ht0 hcp
      have hslt : s < d - 1 := by
        have h := ht; rw [hxw, hdgw'] at h; omega
      have huvne : u ≠ v := fun hc => by have := huv_iff.mp hc; omega
      refine ⟨u, ?_, ?_, s2, ?_, ?_, ?_, ?_⟩
      · rw [hxw]; exact hwu_new huvne
      · rw [hcp]; exact hajp
      · rw [hdgo u huvne (Ne.symm hwu)]; exact hs2
      · rw [hcp, hmtp]; exact hq'
      · rw [← hq', hajo q (Ne.symm hpq), hq', hxw]; exact hajq0
      · rw [← hq', hmtq, hxw, hts]; exact hp'
    by_cases hcq : offF (x : ℕ) + t = q
    · -- the far end of the moved copy
      obtain ⟨hxu, hts⟩ := hkq x t ht0 hcq
      have huvne : u ≠ v := by
        intro huv
        have hsd1 : s = d - 1 := huv_iff.mp huv
        have hqv : q = offF (v : ℕ) + i := by rw [← hq, ← hsd1]; exact hmtw0
        have hxv : x = v := by rw [hxu, huv]
        rw [hqv, hxv] at hcq
        rw [hxv, hdgv'] at ht
        omega
      have hslt : s < d - 1 := by
        rcases Nat.lt_or_ge s (d - 1) with h | h
        · exact h
        · exact absurd (huv_iff.mpr (by omega)) huvne
      refine ⟨w, ?_, ?_, s, ?_, ?_, ?_, ?_⟩
      · rw [hxu]; exact (hwu_new huvne).symm
      · rw [hcq, hajo q (Ne.symm hpq), hq']; exact hajq0
      · rw [hdgw']; exact hslt
      · rw [hcq, hmtq]; exact hp'
      · rw [← hp', hajp, hxu]
      · rw [← hp', hmtp, hxu, hts]; exact hq'
    · -- every other slot keeps its old content and its old mate
      obtain ⟨z, hKxz, hajk, s3, hs3, hmtk, hajm, hmtm⟩ := hsound x t ht0
      have hmp : offF (z : ℕ) + s3 ≠ p := by
        intro hc
        have heq : offF (x : ℕ) + t = offF (v : ℕ) + i := by
          rw [← hmtm, hc, hp']; exact hmtw0
        have hxv : x = v := by
          by_contra hne
          exact hrow x v hne t i ht0 hilt heq
        rw [hxv] at heq
        rw [hxv, hdgv'] at ht
        omega
      have hmq : offF (z : ℕ) + s3 ≠ q := by
        intro hc
        have heq : offF (x : ℕ) + t = offF (w : ℕ) + (d - 1) := by
          rw [← hmtm, hc, hq']; exact hmtq0
        have hxw : x = w := by
          by_contra hne
          exact hrow x w hne t (d - 1) ht0 hd1 heq
        rw [hxw] at heq
        rw [hxw, hdgw'] at ht
        omega
      have hznew : (cutTo H v (T \ {w})).Adj x z := by
        by_cases hxv : x = v
        · rw [hxv] at hajk hKxz ⊢
          have hzT : z ∈ T := by rw [← hnvT]; exact hKxz
          have hzw : z ≠ w := by
            intro hzw
            have hti : t = i := by
              refine hinj v (by rw [hxv] at ht0; exact ht0) hilt ?_
              rw [hajk, hw, hzw]
            rw [hxv, hdgv'] at ht
            omega
          have hmem : z ∈ (cutTo H v (T \ {w})).neighborSet v := by
            rw [hnv]; exact ⟨hzT, hzw⟩
          exact hmem
        by_cases hxw : x = w
        · rw [hxw] at hajk hKxz hcp ⊢
          have hzvne : z ≠ v := by
            intro hzvv
            have hts : t = s := by
              refine hinj w (by rw [hxw] at ht0; exact ht0) (by rw [hd]; exact hs) ?_
              rw [hajk, hzvv, hajw0]
            exact hcp (by rw [hp', hts])
          have hmem : z ∈ (cutTo H v (T \ {w})).neighborSet w := by
            rw [hnw]; exact ⟨hKxz, hzvne⟩
          exact hmem
        · have hmem : z ∈ (cutTo H v (T \ {w})).neighborSet x := by
            rw [hnx x hxv hxw]; exact hKxz
          exact hmem
      refine ⟨z, hznew, ?_, s3, ?_, ?_, ?_, ?_⟩
      · rw [hajo _ hcp]; exact hajk
      · by_cases hzvv : z = v
        · rw [hzvv, hdgv']
          by_contra hcon
          have hs3lt : s3 < i + 1 := by rw [hzvv, hdgv] at hs3; exact hs3
          have hs3i : s3 = i := by omega
          exact hcp (by rw [← hp, ← hmtm, hzvv, hs3i])
        by_cases hzw : z = w
        · rw [hzw, hdgw']
          by_contra hcon
          have hs3lt : s3 < d := by rw [hzw, hd] at hs3; exact hs3
          have hs3d : s3 = d - 1 := by omega
          exact hcq (by rw [← hq, ← hmtm, hzw, hs3d])
        · rw [hdgo z hzvv hzw]; exact hs3
      · rw [hmto _ hcp hcq]; exact hmtk
      · rw [hajo _ hmp]; exact hajm
      · rw [hmto _ hmp hmq]; exact hmtm
  · -- completeness
    intro x z hxz
    by_cases hcase : x = w ∧ z = u
    · obtain ⟨hxw, hzu⟩ := hcase
      rw [hxw] at hxz
      have hzvne : z ≠ v := by
        have hmem : z ∈ (cutTo H v T).neighborSet w \ {v} := by
          rw [← hnw]; exact hxz
        simp only [Set.mem_diff, Set.mem_singleton_iff] at hmem
        exact hmem.2
      have huvne : u ≠ v := by rw [← hzu]; exact hzvne
      have hslt : s < d - 1 := by
        rcases Nat.lt_or_ge s (d - 1) with h | h
        · exact h
        · exact absurd (huv_iff.mpr (by omega)) huvne
      refine ⟨s, ?_, ?_⟩
      · rw [hxw, hdgw']; exact hslt
      · rw [hxw, ← hp', hajp, hzu]
    · have hxzold : (cutTo H v T).Adj x z := by
        refine cutTo_adj.mpr ⟨(cutTo_adj.mp hxz).1, ?_, ?_⟩
        · intro hxv; exact ((cutTo_adj.mp hxz).2.1 hxv).1
        · intro hzv; exact ((cutTo_adj.mp hxz).2.2 hzv).1
      obtain ⟨t, ht, hajk⟩ := hcomp x z hxzold
      have hcp : offF (x : ℕ) + t ≠ p := by
        intro hc
        obtain ⟨hxw, hts⟩ := hkp x t ht hc
        have hzvv : z = v := Fin.val_injective (by rw [← hajk, hxw, hts]; exact hajw0)
        rw [hxw] at hxz
        have hmem : z ∈ (cutTo H v T).neighborSet w \ {v} := by
          rw [← hnw]; exact hxz
        simp only [Set.mem_diff, Set.mem_singleton_iff] at hmem
        exact hmem.2 hzvv
      refine ⟨t, ?_, by rw [hajo _ hcp]; exact hajk⟩
      by_cases hxv : x = v
      · rw [hxv, hdgv']
        by_contra hcon
        have hlt : t < i + 1 := by rw [hxv, hdgv] at ht; exact ht
        have hti : t = i := by omega
        have hzw : z = w := Fin.val_injective (by rw [← hajk, hxv, hti]; exact hw)
        rw [hxv] at hxz
        have hmem : z ∈ T \ {w} := by rw [← hnv]; exact hxz
        simp only [Set.mem_diff, Set.mem_singleton_iff] at hmem
        exact hmem.2 hzw
      by_cases hxw : x = w
      · rw [hxw, hdgw']
        by_contra hcon
        have hlt : t < d := by rw [hxw, hd] at ht; exact ht
        have htd : t = d - 1 := by omega
        have hzu : z = u := Fin.val_injective (by rw [← hajk, hxw, htd]; exact hu)
        exact hcase ⟨hxw, hzu⟩
      · rw [hdgo x hxv hxw]; exact ht

/-! ## §5 The delete program -/

theorem getD_set_self {l : List ℕ} {i x : ℕ} (h : i < l.length) :
    (l.set i x).getD i 0 = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by simpa using h)]
  rfl

theorem getD_set_of_ne {l : List ℕ} {i j x : ℕ} (h : j ≠ i) :
    (l.set i x).getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (by omega)]

/-- The scratch scalars of the delete pass: the index of `v`'s last live
slot, the neighbour it names, that neighbour's copy of `v`, the
neighbour's last live slot, the vertex there and its mate. -/
def delAdjBody (ao aj dg mt vx : String) : Com :=
  .seq (.assign "dl.i" (.sub (.get dg (.var vx)) (.lit 1)))
  (.seq (.assign "dl.w" (.get aj (.add (.get ao (.var vx)) (.var "dl.i"))))
  (.seq (.assign "dl.p" (.get mt (.add (.get ao (.var vx)) (.var "dl.i"))))
  (.seq (.assign "dl.l"
      (.sub (.add (.get ao (.var "dl.w")) (.get dg (.var "dl.w"))) (.lit 1)))
  (.seq (.assign "dl.u" (.get aj (.var "dl.l")))
  (.seq (.assign "dl.q" (.get mt (.var "dl.l")))
  (.seq (.store aj (.var "dl.p") (.var "dl.u"))
  (.seq (.store mt (.var "dl.p") (.var "dl.q"))
  (.seq (.store mt (.var "dl.q") (.var "dl.p"))
  (.seq (.store dg (.var "dl.w") (.sub (.get dg (.var "dl.w")) (.lit 1)))
        (.store dg (.var vx) (.var "dl.i")))))))))))

/-- **The delete program**: unlink `v` from one neighbour per turn,
swapping that neighbour's last live slot into the vacated one and
shrinking both live lengths, until `v`'s own live length is `0`. -/
def delAdjCom (ao aj dg mt vx : String) : Com :=
  .while (.lt (.lit 0) (.get dg (.var vx))) (delAdjBody ao aj dg mt vx)

/-- The loop invariant of the delete: the shape clauses, the region at
`v`'s neighbourhood cut down to some `T`, and the scalar still naming
`v`. -/
def DelInv (ao aj dg mt vx : String) {N : ℕ} (offF : ℕ → ℕ)
    (G H : SimpleGraph (Fin N)) (v : Fin N) (σ : Env) : Prop :=
  AdjFrame ao aj dg mt offF G σ ∧
  (∃ T : Set (Fin N), T ⊆ H.neighborSet v ∧ AdjCore aj dg mt offF (cutTo H v T) σ) ∧
  σ.vars vx = (v : ℕ)

set_option maxHeartbeats 400000 in
/-- **The post-state of one delete turn**, read off the four array
equations the block leaves: the region has moved to `T \ {w}`, the
shape clauses survive (only lengths matter and `List.set` preserves
them), and `v`'s live length has dropped. -/
theorem delStep_post {ao aj dg mt vx : String}
    {N : ℕ} {offF : ℕ → ℕ} {G H : SimpleGraph (Fin N)} (hHG : H ≤ G)
    {v : Fin N} {T : Set (Fin N)} (hT : T ⊆ H.neighborSet v)
    {σ τ : Env}
    (hframe : AdjFrame ao aj dg mt offF G σ)
    (hcore : AdjCore aj dg mt offF (cutTo H v T) σ)
    (hvx : σ.vars vx = (v : ℕ)) (hpos : 0 < (σ.arrs dg).getD (v : ℕ) 0)
    {w u : Fin N} {s s2 : ℕ}
    (hajw : (σ.arrs aj).getD (offF (v : ℕ) + ((σ.arrs dg).getD (v : ℕ) 0 - 1)) 0 = (w : ℕ))
    (hmtw : (σ.arrs mt).getD (offF (v : ℕ) + ((σ.arrs dg).getD (v : ℕ) 0 - 1)) 0
      = offF (w : ℕ) + s)
    (hajl : (σ.arrs aj).getD (offF (w : ℕ) + ((σ.arrs dg).getD (w : ℕ) 0 - 1)) 0 = (u : ℕ))
    (hmtl : (σ.arrs mt).getD (offF (w : ℕ) + ((σ.arrs dg).getD (w : ℕ) 0 - 1)) 0
      = offF (u : ℕ) + s2)
    (hs : s < (σ.arrs dg).getD (w : ℕ) 0) (hs2 : s2 < (σ.arrs dg).getD (u : ℕ) 0)
    (hajp0 : (σ.arrs aj).getD (offF (w : ℕ) + s) 0 = (v : ℕ))
    (hajq0 : (σ.arrs aj).getD (offF (u : ℕ) + s2) 0 = (w : ℕ))
    (hvw : v ≠ w)
    (haoT : τ.arrs ao = σ.arrs ao)
    (hajT : τ.arrs aj = (σ.arrs aj).set (offF (w : ℕ) + s) (u : ℕ))
    (hmtT : τ.arrs mt = ((σ.arrs mt).set (offF (w : ℕ) + s) (offF (u : ℕ) + s2)).set
      (offF (u : ℕ) + s2) (offF (w : ℕ) + s))
    (hdgT : τ.arrs dg = ((σ.arrs dg).set (w : ℕ) ((σ.arrs dg).getD (w : ℕ) 0 - 1)).set
      (v : ℕ) ((σ.arrs dg).getD (v : ℕ) 0 - 1))
    (hvxT : τ.vars vx = σ.vars vx) :
    DelInv ao aj dg mt vx offF G H v τ ∧
      (τ.arrs dg).getD (v : ℕ) 0 < (σ.arrs dg).getD (v : ℕ) 0 := by
  obtain ⟨h0, hstep, haoLen, haoR, hajLen, hmtLen, hdgLen⟩ := hframe
  have hfitG : ∀ x : Fin N, (σ.arrs dg).getD (x : ℕ) 0 ≤ (G.neighborSet x).ncard := by
    intro x
    rw [hcore.1 x]
    exact Set.ncard_le_ncard (fun _ hz => hHG hz.1) (Set.toFinite _)
  have hslotP : offF (w : ℕ) + s < offF N :=
    offF_slot_lt hstep (lt_of_lt_of_le hs (hfitG w))
  have hslotQ : offF (u : ℕ) + s2 < offF N :=
    offF_slot_lt hstep (lt_of_lt_of_le hs2 (hfitG u))
  have hPaj : offF (w : ℕ) + s < (σ.arrs aj).length := by omega
  have hPmt : offF (w : ℕ) + s < (σ.arrs mt).length := by omega
  have hQmt : offF (u : ℕ) + s2 < (σ.arrs mt).length := by omega
  have hpq : offF (w : ℕ) + s ≠ offF (u : ℕ) + s2 := by
    intro hc
    exact hvw (Fin.val_injective (by rw [← hajp0, hc, hajq0]))
  have hvN : (v : ℕ) < N := v.isLt
  have hwN : (w : ℕ) < N := w.isLt
  have hvdg : (v : ℕ) < (σ.arrs dg).length := by omega
  have hwdg : (w : ℕ) < (σ.arrs dg).length := by omega
  have hwv : (w : ℕ) ≠ (v : ℕ) := fun hc => hvw (Fin.val_injective hc).symm
  have hdgvT : (τ.arrs dg).getD (v : ℕ) 0 = (σ.arrs dg).getD (v : ℕ) 0 - 1 := by
    rw [hdgT]; exact getD_set_self (by simpa using hvdg)
  refine ⟨⟨⟨h0, hstep, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨T \ {w}, fun _ hz => hT (Set.mem_of_mem_diff hz), ?_⟩, ?_⟩, by rw [hdgvT]; omega⟩
  · rw [haoT]; exact haoLen
  · rw [haoT]; exact haoR
  · rw [hajT]; simpa using hajLen
  · rw [hmtT]; simpa using hmtLen
  · rw [hdgT]; simpa using hdgLen
  · refine adjCore_unlink hstep hHG hT hcore (by omega) hajw hmtw rfl hajl hmtl
      ?_ ?_ ?_ ?_ ?_ hdgvT ?_ ?_
    · rw [hajT]; exact getD_set_self hPaj
    · intro k hk; rw [hajT]; exact getD_set_of_ne hk
    · rw [hmtT, getD_set_of_ne hpq]; exact getD_set_self hPmt
    · rw [hmtT]; exact getD_set_self (by simpa using hQmt)
    · intro k h1 h2; rw [hmtT, getD_set_of_ne h2]; exact getD_set_of_ne h1
    · rw [hdgT, getD_set_of_ne hwv]; exact getD_set_self hwdg
    · intro y h1 h2
      rw [hdgT, getD_set_of_ne (fun hc => h1 (Fin.val_injective hc)),
        getD_set_of_ne (fun hc => h2 (Fin.val_injective hc))]
  · rw [hvxT]; exact hvx

set_option maxHeartbeats 1000000 in
/-- **One turn of the delete loop.** -/
theorem delAdjBody_spec {ao aj dg mt vx : String}
    (hoa : ao ≠ aj) (hom : ao ≠ mt) (hod : ao ≠ dg)
    (ham : aj ≠ mt) (had : aj ≠ dg) (hmd : mt ≠ dg)
    (hx1 : vx ≠ "dl.i") (hx2 : vx ≠ "dl.w") (hx3 : vx ≠ "dl.p")
    (hx4 : vx ≠ "dl.l") (hx5 : vx ≠ "dl.u") (hx6 : vx ≠ "dl.q")
    {B N : ℕ} (hB : N + N * N < B) {offF : ℕ → ℕ}
    {G H : SimpleGraph (Fin N)} (hHG : H ≤ G) (v : Fin N) :
    Spec B
      (fun σ => DelInv ao aj dg mt vx offF G H v σ ∧ 0 < (σ.arrs dg).getD (v : ℕ) 0)
      (delAdjBody ao aj dg mt vx)
      (fun σ σ' => DelInv ao aj dg mt vx offF G H v σ' ∧
        (σ'.arrs dg).getD (v : ℕ) 0 < (σ.arrs dg).getD (v : ℕ) 0)
      49 := by
  intro σ hσ
  obtain ⟨⟨hframe, ⟨T, hT, hcore⟩, hvx⟩, hpos⟩ := hσ
  obtain ⟨h0, hstep, haoLen, haoR, hajLen, hmtLen, hdgLen⟩ := hframe
  have hNB : N < B := by omega
  have hoffN : offF N ≤ N * N := offF_le_sq h0 hstep N le_rfl
  have hoffB : offF N < B := by omega
  have hdegN : ∀ x : Fin N, (σ.arrs dg).getD (x : ℕ) 0 ≤ N := by
    intro x
    rw [hcore.1 x]
    have := Set.ncard_le_ncard (Set.subset_univ ((cutTo H v T).neighborSet x))
      (Set.toFinite _)
    simpa using this
  have hfitG : ∀ x : Fin N, (σ.arrs dg).getD (x : ℕ) 0 ≤ (G.neighborSet x).ncard := by
    intro x
    rw [hcore.1 x]
    exact Set.ncard_le_ncard (fun _ hz => hHG hz.1) (Set.toFinite _)
  have hvN : (v : ℕ) < N := v.isLt
  have hdgv : (σ.arrs dg).getD (v : ℕ) 0 = ((σ.arrs dg).getD (v : ℕ) 0 - 1) + 1 := by omega
  have haoV : (σ.arrs ao).getD (v : ℕ) 0 = offF (v : ℕ) := haoR (v : ℕ) (le_of_lt v.isLt)
  obtain ⟨w, hKvw, hajw, s, hs, hmtw, hajp0, hmtp0⟩ :=
    hcore.2.1 v ((σ.arrs dg).getD (v : ℕ) 0 - 1) (by omega)
  have hwN : (w : ℕ) < N := w.isLt
  have haoW : (σ.arrs ao).getD (w : ℕ) 0 = offF (w : ℕ) := haoR (w : ℕ) (le_of_lt w.isLt)
  obtain ⟨u, hKwu, hajl, s2, hs2, hmtl, hajq0, hmtq0⟩ :=
    hcore.2.1 w ((σ.arrs dg).getD (w : ℕ) 0 - 1) (by omega)
  have huN : (u : ℕ) < N := u.isLt
  have hvw : v ≠ w := hKvw.ne
  have hwu : w ≠ u := hKwu.ne
  have hslotV : offF (v : ℕ) + ((σ.arrs dg).getD (v : ℕ) 0 - 1) < offF N :=
    offF_slot_lt hstep (lt_of_lt_of_le (by omega) (hfitG v))
  have hslotP : offF (w : ℕ) + s < offF N :=
    offF_slot_lt hstep (lt_of_lt_of_le hs (hfitG w))
  have hslotL : offF (w : ℕ) + ((σ.arrs dg).getD (w : ℕ) 0 - 1) < offF N :=
    offF_slot_lt hstep (lt_of_lt_of_le (by omega) (hfitG w))
  have hslotQ : offF (u : ℕ) + s2 < offF N :=
    offF_slot_lt hstep (lt_of_lt_of_le hs2 (hfitG u))
  have ham' : mt ≠ aj := Ne.symm ham
  have had' : dg ≠ aj := Ne.symm had
  have hmd' : dg ≠ mt := Ne.symm hmd
  have hLeq : offF (w : ℕ) + (σ.arrs dg).getD (w : ℕ) 0 - 1
      = offF (w : ℕ) + ((σ.arrs dg).getD (w : ℕ) 0 - 1) := by omega
  have hdgvxN : (σ.arrs dg).getD (σ.vars vx) 0 ≤ N := by rw [hvx]; exact hdegN v
  have hLle : offF (w : ℕ) + (σ.arrs dg).getD (w : ℕ) 0 ≤ offF N := by
    have h1 : offF ((w : ℕ) + 1) = offF (w : ℕ) + (G.neighborSet w).ncard := hstep w
    have h2 : offF ((w : ℕ) + 1) ≤ offF N :=
      offF_mono hstep N le_rfl ((w : ℕ) + 1) w.isLt
    have h3 := hfitG w
    omega
  have hdgwN : (σ.arrs dg).getD (w : ℕ) 0 ≤ N := hdegN w
  have hdguN : (σ.arrs dg).getD (u : ℕ) 0 ≤ N := hdegN u
  have haovxN : (σ.arrs ao).getD (σ.vars vx) 0 ≤ offF N := by
    rw [hvx, haoV]
    exact offF_mono hstep N le_rfl (v : ℕ) (le_of_lt v.isLt)
  run_vcg
  · refine delStep_post hHG hT ⟨h0, hstep, haoLen, haoR, hajLen, hmtLen, hdgLen⟩
      hcore hvx hpos hajw hmtw hajl hmtl hs hs2 hajp0 hajq0 hvw ?_ ?_ ?_ ?_ ?_ <;>
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, hvx, hx1, hx2, hx3,
      hx4, hx5, hx6, hoa, hom, hod, ham, had, hmd, ham', had', hmd',
      haoV, hajw, hmtw, haoW, hLeq, hajl, hmtl, if_true, if_false, ite_true, ite_false,
      String.reduceEq, reduceIte, List.length_set]
  all_goals
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, hvx, hx1, hx2, hx3,
      hx4, hx5, hx6, hoa, hom, hod, ham, had, hmd, ham', had', hmd',
      haoV, hajw, hmtw, haoW, hLeq, hajl, hmtl, if_true, if_false, ite_true, ite_false,
      String.reduceEq, reduceIte, List.length_set]
  all_goals omega

/-! ## §6 The delete contract -/

set_option maxHeartbeats 1000000 in
/-- **The delete loop.** Started at `v`'s live length `D`, it unlinks
one neighbour per turn and stops with `v` isolated, at cost `54·D + 5`
— affine in `v`'s *current* degree, as the contract asks. -/
theorem delAdjCom_spec {ao aj dg mt vx : String}
    (hoa : ao ≠ aj) (hom : ao ≠ mt) (hod : ao ≠ dg)
    (ham : aj ≠ mt) (had : aj ≠ dg) (hmd : mt ≠ dg)
    (hx1 : vx ≠ "dl.i") (hx2 : vx ≠ "dl.w") (hx3 : vx ≠ "dl.p")
    (hx4 : vx ≠ "dl.l") (hx5 : vx ≠ "dl.u") (hx6 : vx ≠ "dl.q")
    {B N : ℕ} (hB : N + N * N < B) {offF : ℕ → ℕ}
    {G H : SimpleGraph (Fin N)} (hHG : H ≤ G) (v : Fin N) (D : ℕ) :
    Spec B
      (fun σ => DelInv ao aj dg mt vx offF G H v σ ∧ (σ.arrs dg).getD (v : ℕ) 0 = D)
      (delAdjCom ao aj dg mt vx)
      (fun _ σ' => AdjFrame ao aj dg mt offF G σ' ∧
        AdjCore aj dg mt offF (cutTo H v (∅ : Set (Fin N))) σ' ∧ σ'.vars vx = (v : ℕ))
      (54 * D + 5) := by
  have hvN : (v : ℕ) < N := v.isLt
  have hNB : N < B := by omega
  -- the loop test, evaluated
  have hcond : ∀ σ, DelInv ao aj dg mt vx offF G H v σ →
      (Cond.lt (.lit 0) (.get dg (.var vx))).evalB B σ
        = some (decide (0 < (σ.arrs dg).getD (v : ℕ) 0)) := by
    intro σ hI
    obtain ⟨hframe, ⟨T, hT, hcore⟩, hvx⟩ := hI
    have hdgN : (σ.arrs dg).getD (v : ℕ) 0 ≤ N := by
      rw [hcore.1 v]
      have := Set.ncard_le_ncard (Set.subset_univ ((cutTo H v T).neighborSet v))
        (Set.toFinite _)
      simpa using this
    have h1 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
    have h2 : (Expr.get dg (.var vx)).evalB B σ
        = some ((σ.arrs dg).getD (σ.vars vx) 0) :=
      RunStep.eval_get B σ dg (.var vx) (σ.vars vx) (evalB_var (by rw [hvx]; omega))
        (by rw [hvx]; have := hframe.2.2.2.2.2.2; omega)
        (by rw [hvx]; omega)
    rw [hvx] at h2
    simp [Cond.evalB, h1, h2]
  refine (Spec.while_count (DelInv ao aj dg mt vx offF G H v)
    (fun σ => (σ.arrs dg).getD (v : ℕ) 0) 49 ?_ ?_ (fun σ hσ => hσ.1) ?_).post ?_
  · intro σ hI
    exact ⟨_, hcond σ hI⟩
  · refine (delAdjBody_spec hoa hom hod ham had hmd hx1 hx2 hx3 hx4 hx5 hx6
      hB hHG v).pre ?_
    rintro σ ⟨hI, htrue⟩
    refine ⟨hI, ?_⟩
    rw [hcond σ hI] at htrue
    simpa using htrue
  · intro σ hσ
    simp only [hσ.2, size_condLt, size_get, size_var, size_lit]
    omega
  · rintro σ σ' hσ ⟨hI, hfalse⟩
    obtain ⟨hframe, ⟨T, hT, hcore⟩, hvx⟩ := hI
    rw [hcond σ' ⟨hframe, ⟨T, hT, hcore⟩, hvx⟩] at hfalse
    have hzero : (σ'.arrs dg).getD (v : ℕ) 0 = 0 := by simpa using hfalse
    have hTc : T.ncard = 0 := by
      rw [← neighborSet_cutTo_self hT, ← hcore.1 v, hzero]
    have hTe : T = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hTc
    exact ⟨hframe, hTe ▸ hcore, hvx⟩

/-- **The delete contract, with the word bound the landed
`AdjDeleteIn` omits** — `N + N² < B`, which is what makes every index
the pass computes fit into a word. See `not_adjDeleteIn` below: without
it the landed statement is *false*, for every `B`, program and budget.
Everything else is `AdjDeleteIn` verbatim. -/
def AdjDeleteInW (B : ℕ) (ao aj dg mt vx : String) (delC : Com)
    (kd : ℕ → ℕ) : Prop :=
  ∀ {N : ℕ} (G : SimpleGraph (Fin N)) (S : Set (Fin N)) (v : Fin N),
    v ∉ S → N + N * N < B →
    Spec B
      (fun σ => DelAdjSt ao aj dg mt G S σ ∧ σ.vars vx = (v : ℕ))
      delC
      (fun _ σ' => DelAdjSt ao aj dg mt G (S ∪ {v}) σ')
      (kd (((deleteVerts G S).neighborSet v).ncard))

/-- **The delete program meets the delete contract** at the budget
`54·d + 5`, `d` the deleted vertex's current degree: one turn of `49`
per removed edge copy, plus the loop's own test. -/
theorem adjDeleteInW_delAdjCom {ao aj dg mt vx : String}
    (hoa : ao ≠ aj) (hom : ao ≠ mt) (hod : ao ≠ dg)
    (ham : aj ≠ mt) (had : aj ≠ dg) (hmd : mt ≠ dg)
    (hx1 : vx ≠ "dl.i") (hx2 : vx ≠ "dl.w") (hx3 : vx ≠ "dl.p")
    (hx4 : vx ≠ "dl.l") (hx5 : vx ≠ "dl.u") (hx6 : vx ≠ "dl.q") (B : ℕ) :
    AdjDeleteInW B ao aj dg mt vx (delAdjCom ao aj dg mt vx)
      (fun d => 54 * d + 5) := by
  intro N G S v _ hB σ hσ
  obtain ⟨hdel, hvx⟩ := hσ
  obtain ⟨offF, hframe, hcore⟩ := delAdjSt_iff.mp hdel
  have hHG : deleteVerts G S ≤ G := Lax3Proofs.WalkDistance.deleteVerts_le G S
  have hcore' : AdjCore aj dg mt offF
      (cutTo (deleteVerts G S) v ((deleteVerts G S).neighborSet v)) σ := by
    rw [cutTo_self]; exact hcore
  have hD : (σ.arrs dg).getD (v : ℕ) 0 = ((deleteVerts G S).neighborSet v).ncard :=
    hcore.1 v
  obtain ⟨σ', hrun, hframe', hcore'', hvx'⟩ :=
    (delAdjCom_spec hoa hom hod ham had hmd hx1 hx2 hx3 hx4 hx5 hx6 hB hHG v
      (((deleteVerts G S).neighborSet v).ncard)).run
      ⟨⟨hframe, ⟨(deleteVerts G S).neighborSet v, subset_rfl, hcore'⟩, hvx⟩, hD⟩
  refine ⟨σ', hrun, delAdjSt_iff.mpr ⟨offF, hframe', ?_⟩⟩
  rw [deleteVerts_insert]
  exact hcore''

/-! ## §7 The landed `AdjDeleteIn` is unsatisfiable -/

/-- **No run can write above the word bound.** Every store's index is
the value of an expression and `evalB` refuses a value reaching `B`, so
a cell at index `≥ B` is exactly as the run found it. -/
theorem bigStepB_getElem?_high {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) : ∀ (arr : String) (j : ℕ), B ≤ j →
      (σ'.arrs arr)[j]? = (σ.arrs arr)[j]? := by
  induction h with
  | skip => intro arr j _; rfl
  | assign _ => intro arr j _; rfl
  | store hi _ _ =>
      intro arr j hj
      have hklt := Expr.lt_of_evalB hi
      rw [arrs_setArr]
      split
      · next hae => rw [hae]; exact List.getElem?_set_ne (by omega)
      · rfl
  | seq _ _ ih ih' => intro arr j hj; rw [ih' arr j hj, ih arr j hj]
  | ite_true _ _ ih => intro arr j hj; exact ih arr j hj
  | ite_false _ _ ih => intro arr j hj; exact ih arr j hj
  | while_true _ _ _ ih ih' => intro arr j hj; rw [ih' arr j hj, ih arr j hj]
  | while_false _ => intro arr j _; rfl
  | read _ => intro arr j _; rfl
  | write _ => intro arr j _; rfl

theorem run_getD_high {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : Run B c σ σ' K) (arr : String) (j : ℕ) (hj : B ≤ j) :
    (σ'.arrs arr).getD j 0 = (σ.arrs arr).getD j 0 := by
  obtain ⟨k, -, hb⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    bigStepB_getElem?_high hb arr j hj]

/-- The graph with exactly one edge. -/
def oneEdge {n : ℕ} (x y : Fin n) (hxy : x ≠ y) : SimpleGraph (Fin n) where
  Adj a b := (a = x ∧ b = y) ∨ (a = y ∧ b = x)
  symm := fun {_ _} h => h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
  loopless := ⟨fun _ h =>
    h.elim (fun h => hxy (h.1.symm.trans h.2)) (fun h => hxy (h.2.symm.trans h.1))⟩

theorem deleteVerts_empty {N : ℕ} (G : SimpleGraph (Fin N)) :
    deleteVerts G (∅ : Set (Fin N)) = G := by
  ext a b
  exact ⟨fun h => h.1, fun h => ⟨h, by simp, by simp⟩⟩

theorem getD_range_map {n : ℕ} (f : ℕ → ℕ) {i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  have hlen : i < ((List.range n).map f).length := by simpa using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

/-- The witness state of `not_adjDeleteIn`: the four regions of the
one-edge graph on `Fin (B + 2)` whose only edge joins `B` and `B + 1`,
with the scalar naming the vertex `B`. -/
def cexEnv (ao aj dg mt vx : String) (B : ℕ) : Env where
  vars := fun y => if y = vx then B else 0
  arrs := fun c =>
    if c = ao then (List.range (B + 3)).map (fun i => i - B)
    else if c = aj then [B + 1, B]
    else if c = dg then (List.range (B + 2)).map (fun i => if B ≤ i then 1 else 0)
    else if c = mt then [1, 0]
    else []
  inp := []
  out := []

set_option maxHeartbeats 1000000 in
/-- **The landed delete contract is false** — for every word bound,
every program and every budget, as soon as the four region names are
distinct.

The reason is the *statement*, not the algorithm: `AdjDeleteIn`
quantifies over every carrier size `N` and every state satisfying
`DelAdjSt`, with no hypothesis relating either to `B`. Take
`N = B + 2` and the graph whose only edge joins the vertices `B` and
`B + 1`. The region exists, `dg` holds `1` at index `B`, and the
postcondition asks for `0` there — which needs a store at index `B`.
Under `Run B` every store's index is a bounded evaluation, hence `< B`
(`bigStepB_getElem?_high`), so no program at all can meet it.

`AdjDeleteInW` is the same statement with the one missing hypothesis
`N + N² < B`, and `adjDeleteInW_delAdjCom` discharges it. -/
theorem not_adjDeleteIn {ao aj dg mt vx : String}
    (hoa : ao ≠ aj) (hom : ao ≠ mt) (hod : ao ≠ dg)
    (ham : aj ≠ mt) (had : aj ≠ dg) (hmd : mt ≠ dg)
    (B : ℕ) (delC : Com) (kd : ℕ → ℕ) :
    ¬ AdjDeleteIn B ao aj dg mt vx delC kd := by
  intro hcon
  obtain ⟨a, ha⟩ : ∃ a : Fin (B + 2), (a : ℕ) = B := ⟨⟨B, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (B + 2), (b : ℕ) = B + 1 := ⟨⟨B + 1, by omega⟩, rfl⟩
  have hab : a ≠ b := by intro hc; rw [hc, hb] at ha; omega
  set G : SimpleGraph (Fin (B + 2)) := oneEdge a b hab with hG
  set σ : Env := cexEnv ao aj dg mt vx B with hσ
  have hAo : σ.arrs ao = (List.range (B + 3)).map (fun i => i - B) := by
    simp [hσ, cexEnv]
  have hAj : σ.arrs aj = [B + 1, B] := by simp [hσ, cexEnv, Ne.symm hoa]
  have hDg : σ.arrs dg =
      (List.range (B + 2)).map (fun i => if B ≤ i then 1 else 0) := by
    simp [hσ, cexEnv, Ne.symm hod, Ne.symm had]
  have hMt : σ.arrs mt = [1, 0] := by
    simp [hσ, cexEnv, Ne.symm hom, Ne.symm ham, hmd]
  have hvxa : σ.vars vx = (a : ℕ) := by simp [hσ, cexEnv, ha]
  -- the neighbourhoods of the one-edge graph
  have hnb : ∀ x : Fin (B + 2), (G.neighborSet x).ncard
      = if B ≤ (x : ℕ) then 1 else 0 := by
    intro x
    have hx2 : (x : ℕ) < B + 2 := x.isLt
    by_cases hxa : (x : ℕ) = B
    · have hxa' : x = a := Fin.ext (by rw [hxa, ha])
      have hset : G.neighborSet x = {b} := by
        ext z
        constructor
        · rintro (⟨-, rfl⟩ | ⟨h1, -⟩)
          · rfl
          · exact absurd (hxa'.symm.trans h1) hab
        · rintro rfl
          exact Or.inl ⟨hxa', rfl⟩
      rw [hset, Set.ncard_singleton, if_pos (by omega)]
    by_cases hxb : (x : ℕ) = B + 1
    · have hxb' : x = b := Fin.ext (by rw [hxb, hb])
      have hset : G.neighborSet x = {a} := by
        ext z
        constructor
        · rintro (⟨h1, -⟩ | ⟨-, rfl⟩)
          · exact absurd (h1.symm.trans hxb') hab
          · rfl
        · rintro rfl
          exact Or.inr ⟨hxb', rfl⟩
      rw [hset, Set.ncard_singleton, if_pos (by omega)]
    · have hset : G.neighborSet x = ∅ := by
        ext z
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact hxa (by rw [h1, ha])
        · exact hxb (by rw [h1, hb])
      rw [hset, Set.ncard_empty, if_neg (by omega)]
  -- the shape clauses
  have hframe : AdjFrame ao aj dg mt (fun i => i - B) G σ := by
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [hnb x]
      dsimp only
      have hx2 : (x : ℕ) < B + 2 := x.isLt
      by_cases hxB : B ≤ (x : ℕ)
      · rw [if_pos hxB]; omega
      · rw [if_neg hxB]; omega
    · rw [hAo]; simp
    · intro i hi
      rw [hAo, getD_range_map _ (by omega)]
    · rw [hAj]; simp
    · rw [hMt]; simp
    · rw [hDg]; simp
  -- the content clauses
  have hcore : AdjCore aj dg mt (fun i => i - B)
      (deleteVerts G (∅ : Set (Fin (B + 2)))) σ := by
    rw [deleteVerts_empty]
    refine ⟨?_, ?_, ?_⟩
    · intro u
      rw [hnb u, hDg, getD_range_map _ u.isLt]
    · intro u t ht
      have hu2 : (u : ℕ) < B + 2 := u.isLt
      rw [hDg, getD_range_map _ hu2] at ht
      by_cases huB : B ≤ (u : ℕ)
      · rw [if_pos huB] at ht
        have ht0 : t = 0 := by simpa using ht
        subst ht0
        rcases Nat.lt_or_ge (u : ℕ) (B + 1) with hu | hu
        · have hu' : (u : ℕ) = B := by omega
          have hua : u = a := Fin.ext (by rw [hu', ha])
          refine ⟨b, Or.inl ⟨hua, rfl⟩, ?_, 0, ?_, ?_, ?_, ?_⟩
          · rw [hAj, hu', hb]; simp
          · rw [hDg, getD_range_map _ b.isLt, hb]; simp
          · rw [hMt, hu', hb]; simp
          · rw [hAj, hb, hu']; simp
          · rw [hMt, hb, hu']; simp
        · have hu' : (u : ℕ) = B + 1 := by omega
          have hub : u = b := Fin.ext (by rw [hu', hb])
          refine ⟨a, Or.inr ⟨hub, rfl⟩, ?_, 0, ?_, ?_, ?_, ?_⟩
          · rw [hAj, hu', ha]; simp
          · rw [hDg, getD_range_map _ a.isLt, ha]; simp
          · rw [hMt, hu', ha]; simp
          · rw [hAj, ha, hu']; simp
          · rw [hMt, ha, hu']; simp
      · rw [if_neg huB] at ht; omega
    · intro u z huz
      rcases huz with ⟨hua, hzb⟩ | ⟨hub, hza⟩
      · refine ⟨0, ?_, ?_⟩
        · rw [hDg, getD_range_map _ u.isLt, hua, ha]; simp
        · rw [hAj, hua, ha, hzb, hb]; simp
      · refine ⟨0, ?_, ?_⟩
        · rw [hDg, getD_range_map _ u.isLt, hub, hb]; simp
        · rw [hAj, hub, hb, hza, ha]; simp
  obtain ⟨σ', hrun, hpost⟩ :=
    (hcon G ∅ a (by simp)).run
      ⟨delAdjSt_iff.mpr ⟨fun i => i - B, hframe, hcore⟩, hvxa⟩
  obtain ⟨offF', hfr', hcore'⟩ := delAdjSt_iff.mp hpost
  have hzero : (σ'.arrs dg).getD (a : ℕ) 0 = 0 := by
    have h := hcore'.1 a
    rw [ncard_neighborSet_deleteVerts_eq_zero (S := (∅ : Set (Fin (B + 2))) ∪ {a})
      (v := a) (by simp)] at h
    exact h
  rw [ha, run_getD_high hrun dg B le_rfl, hDg, getD_range_map _ (by omega)] at hzero
  simp at hzero

/-! ## §8 The min-degree peel, abstractly

What the peel pass reads off the region is a *live degree*; what
`mdRankAux` recurses on is a *live set*. These three facts are the
bridge, and they are the two places the pass can go silently wrong:
the tie-break (`eq_minDegVert`) and the countdown
(`mdRankAux_peel_step`). -/

open Lax3Proofs.CoverRoutine (minDegVert minDegVert_mem card_nbrsIn_minDegVert
  mdRankAux mdRankAux_of_nonempty mdRank mdPerm)
open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)

/-- **The region's live degree is the peel's live degree.** The peel's
state after some rounds is the region at the isolation of the
*complement* of the live set `S`; at a live vertex the current degree
there is its degree inside `S`, which is what `mdRankAux` compares. -/
theorem ncard_neighborSet_deleteVerts_compl {N : ℕ} (F : SimpleGraph (Fin N))
    (S : Finset (Fin N)) {x : Fin N} (hx : x ∈ S) :
    ((deleteVerts F ((↑S : Set (Fin N))ᶜ)).neighborSet x).ncard
      = (nbrsIn F S x).card := by
  classical
  have hset : (deleteVerts F ((↑S : Set (Fin N))ᶜ)).neighborSet x
      = ↑(nbrsIn F S x) := by
    ext z
    simp only [SimpleGraph.mem_neighborSet, Finset.mem_coe, mem_nbrsIn]
    constructor
    · intro h
      obtain ⟨hadj, -, hz⟩ := deleteVerts_adj.mp h
      exact ⟨by simpa using hz, hadj.symm⟩
    · rintro ⟨hz, hadj⟩
      exact deleteVerts_adj.mpr ⟨hadj.symm, by simpa using hx, by simpa using hz⟩
  rw [hset, Set.ncard_coe_finset]

/-- **The scan's answer is the pinned choice.** A live vertex that
minimises the live degree and is `≤` every other minimiser *is*
`minDegVert` — the `Finset.min'` of the minimum-degree filter, spelled
as what a left-to-right scan with a strict `<` test leaves behind. -/
theorem eq_minDegVert {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty) {b : Fin N} (hbS : b ∈ S)
    (hmin : ∀ x ∈ S, (nbrsIn F S b).card < (nbrsIn F S x).card ∨
      ((nbrsIn F S b).card = (nbrsIn F S x).card ∧ (b : ℕ) ≤ (x : ℕ))) :
    b = minDegVert F S hS := by
  classical
  have hle : ∀ x ∈ S, (nbrsIn F S b).card ≤ (nbrsIn F S x).card := by
    intro x hx
    rcases hmin x hx with h | ⟨h, -⟩ <;> omega
  have hinf : (nbrsIn F S b).card = S.inf' hS (fun v => (nbrsIn F S v).card) :=
    le_antisymm (Finset.le_inf' hS _ hle) (Finset.inf'_le _ hbS)
  have hbmem : b ∈ S.filter (fun v => (nbrsIn F S v).card
      = S.inf' hS fun v => (nbrsIn F S v).card) := Finset.mem_filter.mpr ⟨hbS, hinf⟩
  refine le_antisymm ?_ ?_
  · rcases hmin _ (minDegVert_mem F S hS) with h | ⟨-, h⟩
    · exfalso
      have := card_nbrsIn_minDegVert F S hS
      omega
    · exact h
  · rw [minDegVert]
    exact Finset.min'_le _ _ hbmem

/-- **One round of the countdown**, against `mdRankAux`'s own
recursion: the round's vertex is `minDegVert` of the live set, its rank
is the live count minus one — so the *first* vertex peeled from a live
set of `N` gets `N - 1` — and every still-live vertex keeps the rank
the whole peel gives it. -/
theorem mdRankAux_peel_step {N : ℕ} (F : SimpleGraph (Fin N)) {S : Finset (Fin N)}
    (hS : S.Nonempty) :
    mdRankAux F S (minDegVert F S hS) = S.card - 1 ∧
      ∀ x ∈ S.erase (minDegVert F S hS),
        mdRankAux F S x = mdRankAux F (S.erase (minDegVert F S hS)) x := by
  refine ⟨by rw [mdRankAux_of_nonempty F hS, if_pos rfl], ?_⟩
  intro x hx
  rw [mdRankAux_of_nonempty F hS, if_neg (Finset.ne_of_mem_erase hx)]

/-! ## §9 The peel pass -/

/-- Fill the rank region with the sentinel `N` — the peel's marker for
"still live". It is unambiguous: every rank the peel writes is `< N`
(`mdRank_lt`). -/
def peelInitCom (ra nn ux : String) : Com :=
  .seq (.assign ux (.lit 0))
    (.while (.lt (.var ux) (.var nn))
      (.seq (.store ra (.var ux) (.var nn))
        (.assign ux (.add (.var ux) (.lit 1)))))

/-- The sentinel pass leaves the whole rank region at `N`. -/
theorem peelInit_spec {ra nn ux : String} (hnu : nn ≠ ux) {B N : ℕ} (hNB : N < B) :
    Spec B
      (fun σ => σ.vars nn = N ∧ N ≤ (σ.arrs ra).length)
      (peelInitCom ra nn ux)
      (fun _ σ' => σ'.vars nn = N ∧ N ≤ (σ'.arrs ra).length ∧
        ∀ i, i < N → (σ'.arrs ra).getD i 0 = N)
      (11 * N + 6) := by
  refine (Spec.forRangeZero ux nn
    (fun σ => σ.vars nn = N ∧ N ≤ (σ.arrs ra).length ∧ σ.vars ux ≤ N ∧
      ∀ i, i < σ.vars ux → (σ.arrs ra).getD i 0 = N) N 7 hNB
    (fun _ hI => hI.2.2.1) (fun _ hI => hI.1) ?_).conseq ?_ ?_ (by omega)
  · rintro σ ⟨⟨hnn, hlen, hux, hfill⟩, hlt⟩
    run_vcg
    · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa [hnu] using hnn
      · simpa using hlen
      · simp only [vars_setVar, vars_setArr, eq_self_iff_true, if_true]; omega
      · simp only [vars_setVar, arrs_setVar, arrs_setArr, vars_setArr,
          eq_self_iff_true, if_true]
        intro i hi
        by_cases hie : i = σ.vars ux
        · rw [hie, getD_set_self (by omega), hnn]
        · rw [getD_set_of_ne hie]
          exact hfill i (by omega)
      · simp
  · rintro σ ⟨hnn, hlen⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hnu, hnn, hlen]
  · rintro σ σ' - ⟨⟨hnn, hlen, -, hfill⟩, hux⟩
    exact ⟨hnn, hlen, fun i hi => hfill i (by omega)⟩

/-- A current degree is smaller than the carrier: a vertex is not its
own neighbour. -/
theorem ncard_neighborSet_lt {N : ℕ} (H : SimpleGraph (Fin N)) (x : Fin N) :
    (H.neighborSet x).ncard < N := by
  have hsub : H.neighborSet x ⊆ (Set.univ : Set (Fin N)) \ {x} := by
    intro z hz
    refine ⟨Set.mem_univ _, ?_⟩
    intro hc
    exact H.irrefl (by rwa [hc] at hz)
  have h1 : ((Set.univ : Set (Fin N)) \ {x}).ncard + 1
      = (Set.univ : Set (Fin N)).ncard := ncard_sdiff_singleton (Set.mem_univ x)
  have h2 : (Set.univ : Set (Fin N)).ncard = N := by simp
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- **The scan's key**: the live vertices come first (their rank cell
still holds the sentinel `N`, so the leading term vanishes) and among
them the key is the live degree; a vertex already ranked contributes at
least one full `N`, and every live degree is `< N`. So the minimum of
the key over the whole carrier is attained exactly at the
minimum-degree live vertices, and the least index among them is the
scan's answer. One expression, one comparison — no nested test on
liveness. -/
def peelKey (ra dg : String) (N : ℕ) (σ : Env) (x : ℕ) : ℕ :=
  (N - (σ.arrs ra).getD x 0) * N + (σ.arrs dg).getD x 0

/-- The key, as an IMP+ expression. -/
def peelKeyExpr (ra dg nn ux : String) : Expr :=
  .add (.mul (.sub (.var nn) (.get ra (.var ux))) (.var nn)) (.get dg (.var ux))

/-- One turn of the scan: keep the strictly smaller key, so the least
index among the minimisers survives. -/
def peelScanBody (ra dg nn ux bx bd : String) : Com :=
  .seq (.ite (.lt (peelKeyExpr ra dg nn ux) (.var bd))
      (.seq (.assign bx (.var ux)) (.assign bd (peelKeyExpr ra dg nn ux)))
      .skip)
    (.assign ux (.add (.var ux) (.lit 1)))

/-- **The minimum-degree scan**: one pass over the carrier. The
sentinel `N² + N` starts above every key. -/
def peelScanCom (ra dg nn ux bx bd : String) : Com :=
  .seq (.assign bx (.var nn))
  (.seq (.assign bd (.add (.mul (.var nn) (.var nn)) (.var nn)))
    (.seq (.assign ux (.lit 0))
      (.while (.lt (.var ux) (.var nn)) (peelScanBody ra dg nn ux bx bd))))

/-- The scan's loop invariant: `bx` is the least index attaining the
least key seen so far and `bd` is that key, or nothing has been seen. -/
def PeelScanInv (ra dg nn ux bx bd : String) (B N : ℕ) (σ : Env) : Prop :=
  σ.vars nn = N ∧ σ.vars ux ≤ N ∧
  N ≤ (σ.arrs ra).length ∧ N ≤ (σ.arrs dg).length ∧
  (∀ i, i < N → (σ.arrs ra).getD i 0 ≤ N) ∧
  (∀ i, i < N → (σ.arrs dg).getD i 0 < N) ∧
  σ.vars bd < B ∧ σ.vars bx ≤ N ∧
  (∀ i, i < σ.vars ux → σ.vars bd < peelKey ra dg N σ i ∨
    (σ.vars bd = peelKey ra dg N σ i ∧ σ.vars bx ≤ i)) ∧
  ((σ.vars bx = N ∧ σ.vars bd = N * N + N) ∨
    (σ.vars bx < σ.vars ux ∧ σ.vars bd = peelKey ra dg N σ (σ.vars bx)))

/-- Every key is below the scan's starting sentinel. -/
theorem peelKey_lt {ra dg : String} {N : ℕ} {σ : Env}
    (hral : ∀ i, i < N → (σ.arrs ra).getD i 0 ≤ N)
    (hdgl : ∀ i, i < N → (σ.arrs dg).getD i 0 < N)
    {i : ℕ} (hi : i < N) : peelKey ra dg N σ i < N * N + N := by
  have h1 := hral i hi
  have h2 := hdgl i hi
  have h3 : (N - (σ.arrs ra).getD i 0) * N ≤ N * N :=
    Nat.mul_le_mul_right N (by omega)
  rw [peelKey]
  omega

set_option maxHeartbeats 1000000 in
/-- One turn of the scan keeps the invariant and advances the counter. -/
theorem peelScanBody_spec {ra dg nn ux bx bd : String}
    (hnu : nn ≠ ux) (hnb : nn ≠ bx) (hnd : nn ≠ bd)
    (hxb : ux ≠ bx) (hxd : ux ≠ bd) (hbd : bx ≠ bd)
    {B N : ℕ} (hB : N + N * N + 1 < B) :
    Spec B
      (fun σ => PeelScanInv ra dg nn ux bx bd B N σ ∧ σ.vars ux < N)
      (peelScanBody ra dg nn ux bx bd)
      (fun σ σ' => PeelScanInv ra dg nn ux bx bd B N σ' ∧
        σ'.vars ux = σ.vars ux + 1)
      28 := by
  rintro σ ⟨⟨hnn, hux, hral, hdgl, hrab, hdgb, hbdB, hbxN, h9, h10⟩, hlt⟩
  have hkey : peelKey ra dg N σ (σ.vars ux) < N * N + N :=
    peelKey_lt hrab hdgb hlt
  have hkeyB : peelKey ra dg N σ (σ.vars ux) < B := by omega
  have hraB : (σ.arrs ra).getD (σ.vars ux) 0 ≤ N := hrab _ hlt
  have hdgB : (σ.arrs dg).getD (σ.vars ux) 0 < N := hdgb _ hlt
  have hmulB : (N - (σ.arrs ra).getD (σ.vars ux) 0) * N ≤ N * N :=
    Nat.mul_le_mul_right N (by omega)
  have hkeyval : peelKey ra dg N σ (σ.vars ux)
      = (N - (σ.arrs ra).getD (σ.vars ux) 0) * N
        + (σ.arrs dg).getD (σ.vars ux) 0 := rfl
  have hmulB2 : (σ.vars nn - (σ.arrs ra).getD (σ.vars ux) 0) * σ.vars nn ≤ N * N := by
    rw [hnn]; exact hmulB
  have hkeyB2 : (σ.vars nn - (σ.arrs ra).getD (σ.vars ux) 0) * σ.vars nn
      + (σ.arrs dg).getD (σ.vars ux) 0 < B := by rw [hnn]; omega
  have hun : ux ≠ nn := Ne.symm hnu
  have hbn : bx ≠ nn := Ne.symm hnb
  have hdn : bd ≠ nn := Ne.symm hnd
  have hbu : bx ≠ ux := Ne.symm hxb
  have hdu : bd ≠ ux := Ne.symm hxd
  have hdb : bd ≠ bx := Ne.symm hbd
  simp only [peelScanBody, peelKeyExpr]
  run_vcg
  · -- the key is strictly smaller: the new candidate wins
    rename_i hcase
    have hlt' : (N - (σ.arrs ra).getD (σ.vars ux) 0) * N
        + (σ.arrs dg).getD (σ.vars ux) 0 < σ.vars bd := by
      simpa [hnn] using hcase
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, peelKey,
        hnu, hnb, hnd, hxb, hxd, hbd, hun, hbn, hdn, hbu, hdu, hdb, hnn,
        eq_self_iff_true, if_true, if_false, String.reduceEq, reduceIte]
    case refine_2 => omega
    case refine_3 => exact hral
    case refine_4 => exact hdgl
    case refine_5 => exact hrab
    case refine_6 => exact hdgb
    case refine_7 => omega
    case refine_8 => omega
    case refine_9 =>
      intro i hi
      by_cases hie : i = σ.vars ux
      · exact Or.inr ⟨by rw [hie], by omega⟩
      · have h := h9 i (by omega)
        rw [peelKey] at h
        left
        rcases h with h | ⟨h, -⟩ <;> omega
    case refine_10 => exact Or.inr ⟨by omega, trivial⟩
  · -- the key is not smaller: the old candidate survives
    rename_i hcase
    have hge : σ.vars bd ≤ (N - (σ.arrs ra).getD (σ.vars ux) 0) * N
        + (σ.arrs dg).getD (σ.vars ux) 0 := by
      simpa [hnn] using hcase
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, peelKey,
        hnu, hnb, hnd, hxb, hxd, hbd, hun, hbn, hdn, hbu, hdu, hdb, hnn,
        eq_self_iff_true, if_true, if_false, String.reduceEq, reduceIte]
    case refine_2 => omega
    case refine_3 => exact hral
    case refine_4 => exact hdgl
    case refine_5 => exact hrab
    case refine_6 => exact hdgb
    case refine_7 => exact hbdB
    case refine_8 => exact hbxN
    case refine_9 =>
      intro i hi
      by_cases hie : i = σ.vars ux
      · rw [hie]
        rcases Nat.lt_or_ge (σ.vars bd)
            ((N - (σ.arrs ra).getD (σ.vars ux) 0) * N
              + (σ.arrs dg).getD (σ.vars ux) 0) with h | h
        · exact Or.inl h
        · refine Or.inr ⟨by omega, ?_⟩
          rcases h10 with ⟨-, hbdv⟩ | ⟨hbxlt, -⟩
          · exfalso
            rw [hkeyval] at hkey
            omega
          · omega
      · have h := h9 i (by omega)
        rw [peelKey] at h
        exact h
    case refine_10 =>
      rcases h10 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · rw [peelKey] at h2
        exact Or.inr ⟨by omega, h2⟩
  all_goals (try simp only [vars_setVar, arrs_setVar, hnu, hnb, hnd, hxb, hxd, hbd,
    hun, hbn, hdn, hbu, hdu, hdb, hnn, eq_self_iff_true, if_true, if_false,
    String.reduceEq, reduceIte])
  all_goals omega

/-- The scan leaves in `bx` the least index attaining the least key,
and in `bd` that key. -/
theorem peelScan_spec {ra dg nn ux bx bd : String}
    (hnu : nn ≠ ux) (hnb : nn ≠ bx) (hnd : nn ≠ bd)
    (hxb : ux ≠ bx) (hxd : ux ≠ bd) (hbd : bx ≠ bd)
    {B N : ℕ} (hB : N + N * N + 1 < B) :
    Spec B
      (fun σ => σ.vars nn = N ∧
        N ≤ (σ.arrs ra).length ∧ N ≤ (σ.arrs dg).length ∧
        (∀ i, i < N → (σ.arrs ra).getD i 0 ≤ N) ∧
        (∀ i, i < N → (σ.arrs dg).getD i 0 < N))
      (peelScanCom ra dg nn ux bx bd)
      (fun _ σ' => σ'.vars nn = N ∧
        (∀ i, i < N → σ'.vars bd < peelKey ra dg N σ' i ∨
          (σ'.vars bd = peelKey ra dg N σ' i ∧ σ'.vars bx ≤ i)) ∧
        ((σ'.vars bx = N ∧ σ'.vars bd = N * N + N) ∨
          (σ'.vars bx < N ∧ σ'.vars bd = peelKey ra dg N σ' (σ'.vars bx))))
      (32 * N + 14) := by
  have hNB : N < B := by omega
  have hloop := Spec.forRangeZero (B := B) ux nn
    (PeelScanInv ra dg nn ux bx bd B N) N 28 hNB
    (fun _ hI => hI.2.1) (fun _ hI => hI.1)
    (peelScanBody_spec hnu hnb hnd hxb hxd hbd hB)
  have hbdA : Spec B
      (fun σ => σ.vars nn = N ∧ σ.vars bx = N ∧
        N ≤ (σ.arrs ra).length ∧ N ≤ (σ.arrs dg).length ∧
        (∀ i, i < N → (σ.arrs ra).getD i 0 ≤ N) ∧
        (∀ i, i < N → (σ.arrs dg).getD i 0 < N))
      (.assign bd (.add (.mul (.var nn) (.var nn)) (.var nn)))
      (fun σ σ' => σ' = σ.setVar bd (N * N + N)) 6 := by
    refine (Spec.assign (f := fun _ => N * N + N) ?_).mono (by simp)
    rintro σ ⟨hnn, -, -, -, -, -⟩
    have h1 : (Expr.var nn).evalB B σ = some N := by
      rw [← hnn]; exact evalB_var (by omega)
    exact evalB_bin (evalB_bin h1 h1 (by simp only [Bop.apply_mul]; omega)) h1
      (by simp only [Bop.apply_mul, Bop.apply_add]; omega)
  have hun : ux ≠ nn := Ne.symm hnu
  have hbn : bx ≠ nn := Ne.symm hnb
  have hdn : bd ≠ nn := Ne.symm hnd
  have hbu : bx ≠ ux := Ne.symm hxb
  have hdu : bd ≠ ux := Ne.symm hxd
  have hdb : bd ≠ bx := Ne.symm hbd
  refine (Spec.seq
    (Spec.assign (x := bx) (e := .var nn) (f := fun _ => N) ?_)
    (Spec.seq hbdA hloop ?_ (fun _ _ _ _ _ hq => hq)) ?_ ?_).mono (by simp; omega)
  · rintro σ ⟨hnn, -, -, -, -⟩
    rw [← hnn]
    exact evalB_var (by omega)
  · rintro σ σ' ⟨hnn, hbx, hral, hdgl, hrab, hdgb⟩ rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hnd, hnu] using hnn
    · simp
    · simpa using hral
    · simpa using hdgl
    · simpa using hrab
    · simpa using hdgb
    · simp only [vars_setVar, hdu, hdn, if_false, eq_self_iff_true, if_true,
        String.reduceEq, reduceIte]
      omega
    · simp only [vars_setVar, hbu, hbd, if_false, String.reduceEq, reduceIte]
      omega
    · intro i hi
      simp only [vars_setVar, eq_self_iff_true, if_true] at hi
      omega
    · refine Or.inl ⟨?_, ?_⟩
      · simp only [vars_setVar, hbu, hbd, if_false, String.reduceEq, reduceIte]
        omega
      · simp only [vars_setVar, hdu, if_false, eq_self_iff_true, if_true,
          String.reduceEq, reduceIte]
  · rintro σ σ' ⟨hnn, hral, hdgl, hrab, hdgb⟩ rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hnb] using hnn
    · simp
    · simpa using hral
    · simpa using hdgl
    · simpa using hrab
    · simpa using hdgb
  · rintro σ σ' σ'' - - ⟨⟨hnn, -, -, -, -, -, -, -, h9, h10⟩, huxN⟩
    refine ⟨hnn, ?_, ?_⟩
    · intro i hi
      exact h9 i (by omega)
    · rcases h10 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨by omega, h2⟩


/-- Peeling one more vertex is erasing it from the live set. -/
theorem compl_coe_erase {N : ℕ} (S : Finset (Fin N)) (v : Fin N) :
    ((↑S : Set (Fin N))ᶜ) ∪ {v} = ((↑(S.erase v) : Set (Fin N))ᶜ) := by
  ext z
  simp only [Set.mem_union, Set.mem_compl_iff, Finset.mem_coe, Set.mem_singleton_iff,
    Finset.mem_erase, not_and]
  constructor
  · rintro (h | rfl) hzv
    · exact h
    · exact absurd rfl hzv
  · intro h
    by_cases hzv : z = v
    · exact Or.inr hzv
    · exact Or.inl (h hzv)

/-- **The peel loop's invariant**: a live set `S`, the region at the
isolation of its complement, the rank region holding the sentinel on
`S` and the finished ranks off it, the counter at `|S|`, and — the
clause that makes the countdown right — every live vertex's whole-peel
rank is already its rank in the peel *restricted to `S`*. -/
def PeelInv (ao aj dg mt ra nn rx : String) {N : ℕ} (F : SimpleGraph (Fin N))
    (σ : Env) : Prop :=
  ∃ S : Finset (Fin N),
    DelAdjSt ao aj dg mt F ((↑S : Set (Fin N))ᶜ) σ ∧
    N ≤ (σ.arrs ra).length ∧
    σ.vars nn = N ∧ σ.vars rx = S.card ∧
    (∀ x : Fin N, x ∈ S → (σ.arrs ra).getD (x : ℕ) 0 = N) ∧
    (∀ x : Fin N, x ∉ S → (σ.arrs ra).getD (x : ℕ) 0 = mdRank F x) ∧
    (∀ x : Fin N, x ∈ S → mdRank F x = mdRankAux F S x)

/-- The invariant reads five arrays and two cells. -/
theorem PeelInv.of_eq {ao aj dg mt ra nn rx : String} {N : ℕ}
    {F : SimpleGraph (Fin N)} {σ σ' : Env}
    (h : PeelInv ao aj dg mt ra nn rx F σ)
    (hao : σ'.arrs ao = σ.arrs ao) (haj : σ'.arrs aj = σ.arrs aj)
    (hdg : σ'.arrs dg = σ.arrs dg) (hmt : σ'.arrs mt = σ.arrs mt)
    (hra : σ'.arrs ra = σ.arrs ra)
    (hnn : σ'.vars nn = σ.vars nn) (hrx : σ'.vars rx = σ.vars rx) :
    PeelInv ao aj dg mt ra nn rx F σ' := by
  obtain ⟨S, hdel, hralen, hnnv, hrxv, hlive, hdead, hrank⟩ := h
  exact ⟨S, hdel.of_eq hao haj hdg hmt, by rw [hra]; exact hralen,
    by rw [hnn]; exact hnnv, by rw [hrx]; exact hrxv,
    by rw [hra]; exact hlive, by rw [hra]; exact hdead, hrank⟩

/-- Every live length is below the carrier size. -/
theorem delAdjSt_dg_lt {ao aj dg mt : String} {N : ℕ} {F : SimpleGraph (Fin N)}
    {S : Set (Fin N)} {σ : Env} (h : DelAdjSt ao aj dg mt F S σ) (x : Fin N) :
    (σ.arrs dg).getD (x : ℕ) 0 < N := by
  obtain ⟨offF, -, -, -, -, -, -, -, hdead, hdeg, -, -⟩ := h
  by_cases hx : x ∈ S
  · rw [hdead x hx]
    have := x.isLt
    omega
  · rw [hdeg x hx]
    exact ncard_neighborSet_lt _ x

/-- **One round of the peel**: scan for the minimum-degree live vertex,
count down, write its rank, delete it. The scratch scalars are fixed
names, disjoint from the delete pass's own. -/
def peelRoundCom (ao aj dg mt ra : String) : Com :=
  .seq (peelScanCom ra dg "mp.n" "mp.u" "mp.b" "mp.k")
  (.seq (.assign "mp.r" (.sub (.var "mp.r") (.lit 1)))
  (.seq (.store ra (.var "mp.b") (.var "mp.r"))
  (.seq (.assign "mp.v" (.var "mp.b"))
        (delAdjCom ao aj dg mt "mp.v"))))

set_option maxHeartbeats 1000000 in
/-- One round keeps the invariant and drops the counter. -/
theorem peelRound_spec {ao aj dg mt ra : String}
    (hoa : ao ≠ aj) (hom : ao ≠ mt) (hod : ao ≠ dg)
    (ham : aj ≠ mt) (had : aj ≠ dg) (hmd : mt ≠ dg)
    (hro : ra ≠ ao) (hrj : ra ≠ aj) (hrd : ra ≠ dg) (hrm : ra ≠ mt)
    {B N : ℕ} (hB : N + N * N + 1 < B) {F : SimpleGraph (Fin N)} :
    Spec B
      (fun σ => PeelInv ao aj dg mt ra "mp.n" "mp.r" F σ ∧ 0 < σ.vars "mp.r")
      (peelRoundCom ao aj dg mt ra)
      (fun σ σ' => PeelInv ao aj dg mt ra "mp.n" "mp.r" F σ' ∧
        σ'.vars "mp.r" < σ.vars "mp.r")
      (86 * N + 28) := by
  classical
  intro σ hσ
  obtain ⟨⟨S, hdel, hralen, hnnv, hrxv, hlive, hdead, hrank⟩, hrpos⟩ := hσ
  obtain ⟨offF, hframe, hcore⟩ := delAdjSt_iff.mp hdel
  have hdglen : N ≤ (σ.arrs dg).length := hframe.2.2.2.2.2.2
  have hScard : 0 < S.card := by omega
  have hS : S.Nonempty := Finset.card_pos.mp hScard
  have hcardN : S.card ≤ N := by
    have := Finset.card_le_card (Finset.subset_univ S)
    simpa using this
  have hN : 0 < N := by omega
  -- the two bounds the scan asks for
  have hrab : ∀ i, i < N → (σ.arrs ra).getD i 0 ≤ N := by
    intro i hi
    by_cases hmem : (⟨i, hi⟩ : Fin N) ∈ S
    · rw [hlive _ hmem]
    · rw [hdead _ hmem]
      exact le_of_lt (Lax3Proofs.CoverRoutine.mdRank_lt F _)
  have hdgb : ∀ i, i < N → (σ.arrs dg).getD i 0 < N := fun i hi =>
    delAdjSt_dg_lt hdel ⟨i, hi⟩
  -- the scan
  obtain ⟨σ1, hrun1, ⟨hnn1, hmin1, hcase1⟩, hfv1, hfa1, -, -⟩ :=
    (peelScan_spec (ra := ra) (dg := dg) (nn := "mp.n") (ux := "mp.u")
      (bx := "mp.b") (bd := "mp.k") (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hB).frame.run
      ⟨hnnv, hralen, hdglen, hrab, hdgb⟩
  have hfaS : ∀ a : String, σ1.arrs a = σ.arrs a := fun a =>
    hfa1 a (by simp [peelScanCom, peelScanBody, Com.warrs])
  have hfr1 : σ1.vars "mp.r" = σ.vars "mp.r" :=
    hfv1 _ (by simp [peelScanCom, peelScanBody, Com.wvars])
  -- the scan found a live vertex
  obtain ⟨y, hyS⟩ := id hS
  have hkeyy : peelKey ra dg N σ1 (y : ℕ) = (σ.arrs dg).getD (y : ℕ) 0 := by
    rw [peelKey, hfaS ra, hfaS dg, hlive y hyS]
    simp
  have hbdy : σ1.vars "mp.k" ≤ (σ.arrs dg).getD (y : ℕ) 0 := by
    have h := hmin1 (y : ℕ) y.isLt
    rw [hkeyy] at h
    rcases h with h | ⟨h, -⟩ <;> omega
  have hbdN : σ1.vars "mp.k" < N := by
    have := hdgb (y : ℕ) y.isLt
    omega
  have hbxlt : σ1.vars "mp.b" < N ∧
      σ1.vars "mp.k" = peelKey ra dg N σ1 (σ1.vars "mp.b") := by
    rcases hcase1 with ⟨-, h2⟩ | h
    · exfalso
      have : N ≤ N * N + N := by nlinarith
      omega
    · exact h
  obtain ⟨hbxN, hbdkey⟩ := hbxlt
  obtain ⟨v, hvval⟩ : ∃ v : Fin N, (v : ℕ) = σ1.vars "mp.b" := ⟨⟨_, hbxN⟩, rfl⟩
  have hkv : (N - (σ.arrs ra).getD (v : ℕ) 0) * N + (σ.arrs dg).getD (v : ℕ) 0
      = σ1.vars "mp.k" := by
    rw [hbdkey, peelKey, hfaS ra, hfaS dg, hvval]
  have hravN : (σ.arrs ra).getD (v : ℕ) 0 = N := by
    have hle := hrab (v : ℕ) v.isLt
    rcases Nat.eq_zero_or_pos (N - (σ.arrs ra).getD (v : ℕ) 0) with h | h
    · omega
    · exfalso
      have : N ≤ (N - (σ.arrs ra).getD (v : ℕ) 0) * N := Nat.le_mul_of_pos_left N h
      omega
  have hvS : v ∈ S := by
    by_contra hc
    have h1 := hdead v hc
    have h2 := Lax3Proofs.CoverRoutine.mdRank_lt F v
    omega
  have hbdv : σ1.vars "mp.k" = (σ.arrs dg).getD (v : ℕ) 0 := by
    rw [← hkv, hravN]
    simp
  -- the scan's answer is the pinned choice
  have hdgeq : ∀ x : Fin N, x ∈ S →
      (σ.arrs dg).getD (x : ℕ) 0 = (nbrsIn F S x).card := by
    intro x hx
    rw [hcore.1 x]
    exact ncard_neighborSet_deleteVerts_compl F S hx
  have hvmin : v = minDegVert F S hS := by
    refine eq_minDegVert F S hS hvS ?_
    intro x hx
    have h := hmin1 (x : ℕ) x.isLt
    have hkx : peelKey ra dg N σ1 (x : ℕ) = (σ.arrs dg).getD (x : ℕ) 0 := by
      rw [peelKey, hfaS ra, hfaS dg, hlive x hx]
      simp
    rw [hkx] at h
    rw [← hdgeq x hx, ← hdgeq v hvS, ← hbdv, hvval]
    exact h
  -- the countdown, the rank write and the naming of the victim
  have hrxv1 : σ1.vars "mp.r" = S.card := by rw [hfr1]; exact hrxv
  have hrunA : Run B (.assign "mp.r" (.sub (.var "mp.r") (.lit 1))) σ1
      (σ1.setVar "mp.r" (S.card - 1)) 4 := by
    refine (Run.assign (v := S.card - 1) ?_).mono (by simp)
    have h1 : (Expr.var "mp.r").evalB B σ1 = some S.card := by
      rw [← hrxv1]; exact evalB_var (by omega)
    have h2 := evalB_bin (op := .sub) h1 (evalB_lit (B := B) (n := 1) (by omega))
      (by simp only [Bop.apply_sub]; omega)
    simpa using h2
  have hrunB : Run B (.store ra (.var "mp.b") (.var "mp.r"))
      (σ1.setVar "mp.r" (S.card - 1))
      ((σ1.setVar "mp.r" (S.card - 1)).setArr ra (σ1.vars "mp.b") (S.card - 1)) 3 := by
    refine (Run.store (idx := σ1.vars "mp.b") (v := S.card - 1) ?_ ?_ ?_).mono (by simp)
    · exact evalB_var (by simp; omega)
    · exact evalB_var (by simp; omega)
    · simp only [arrs_setVar]
      rw [hfaS ra, ← hvval]
      have := v.isLt
      omega
  have hrunC : Run B (.assign "mp.v" (.var "mp.b"))
      ((σ1.setVar "mp.r" (S.card - 1)).setArr ra (σ1.vars "mp.b") (S.card - 1))
      (((σ1.setVar "mp.r" (S.card - 1)).setArr ra (σ1.vars "mp.b")
        (S.card - 1)).setVar "mp.v" (σ1.vars "mp.b")) 2 := by
    refine (Run.assign (v := σ1.vars "mp.b") ?_).mono (by simp)
    exact evalB_var (by simp; omega)
  set σ4 : Env := ((σ1.setVar "mp.r" (S.card - 1)).setArr ra (σ1.vars "mp.b")
    (S.card - 1)).setVar "mp.v" (σ1.vars "mp.b") with hσ4
  have harr4 : ∀ a : String, a ≠ ra → σ4.arrs a = σ.arrs a := by
    intro a hane
    simp only [hσ4, arrs_setVar, arrs_setArr, if_neg hane]
    exact hfaS a
  have hra4 : σ4.arrs ra = (σ.arrs ra).set (σ1.vars "mp.b") (S.card - 1) := by
    simp only [hσ4, arrs_setVar, arrs_setArr, eq_self_iff_true, if_true]
    rw [hfaS ra]
  have hdel4 : DelAdjSt ao aj dg mt F ((↑S : Set (Fin N))ᶜ) σ4 :=
    hdel.of_eq (harr4 ao (Ne.symm hro)) (harr4 aj (Ne.symm hrj))
      (harr4 dg (Ne.symm hrd)) (harr4 mt (Ne.symm hrm))
  have hvx4 : σ4.vars "mp.v" = (v : ℕ) := by
    simp only [hσ4, vars_setVar, eq_self_iff_true, if_true]
    exact hvval.symm
  -- the delete
  obtain ⟨σ5, hrun5, hdel5, hfv5, hfa5, -, -⟩ :=
    (adjDeleteInW_delAdjCom hoa hom hod ham had hmd (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) B
      F ((↑S : Set (Fin N))ᶜ) v (by simpa using hvS) (by omega)).frame.run
      ⟨hdel4, hvx4⟩
  have hra5 : σ5.arrs ra = σ4.arrs ra :=
    hfa5 ra (by simp [delAdjCom, delAdjBody, Com.warrs, hrj, hrd, hrm])
  have hn5 : σ5.vars "mp.n" = σ4.vars "mp.n" :=
    hfv5 _ (by simp [delAdjCom, delAdjBody, Com.wvars])
  have hr5 : σ5.vars "mp.r" = σ4.vars "mp.r" :=
    hfv5 _ (by simp [delAdjCom, delAdjBody, Com.wvars])
  rw [compl_coe_erase S v] at hdel5
  -- the new invariant
  have hvne : ∀ x : Fin N, x ≠ v → (x : ℕ) ≠ σ1.vars "mp.b" := by
    intro x hx hc
    exact hx (Fin.val_injective (by rw [hc, hvval]))
  have hvlen : σ1.vars "mp.b" < (σ.arrs ra).length := by
    rw [← hvval]
    have := v.isLt
    omega
  have hrankv : mdRank F v = S.card - 1 := by
    rw [hrank v hvS, hvmin]
    exact (mdRankAux_peel_step F hS).1
  have hdle : ((deleteVerts F ((↑S : Set (Fin N))ᶜ)).neighborSet v).ncard ≤ N :=
    le_of_lt (ncard_neighborSet_lt _ v)
  refine ⟨σ5, (hrun1.seq (hrunA.seq (hrunB.seq (hrunC.seq hrun5)))).mono
      (by first | omega | (simp only []; omega)),
    ⟨S.erase v, hdel5, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hra5, hra4]
    simpa using hralen
  · rw [hn5]
    simp only [hσ4, vars_setVar, vars_setArr, String.reduceEq, reduceIte]
    exact hnn1
  · rw [hr5, Finset.card_erase_of_mem hvS]
    simp only [hσ4, vars_setVar, vars_setArr, String.reduceEq, reduceIte,
      eq_self_iff_true, if_true]
  · intro x hx
    rw [hra5, hra4, getD_set_of_ne (hvne x (Finset.ne_of_mem_erase hx))]
    exact hlive x (Finset.mem_of_mem_erase hx)
  · intro x hx
    by_cases hxv : x = v
    · rw [hxv, hra5, hra4, hvval, getD_set_self hvlen, hrankv]
    · rw [hra5, hra4, getD_set_of_ne (hvne x hxv)]
      refine hdead x ?_
      intro hc
      exact hx (Finset.mem_erase.mpr ⟨hxv, hc⟩)
  · intro x hx
    rw [hrank x (Finset.mem_of_mem_erase hx), hvmin]
    refine (mdRankAux_peel_step F hS).2 x ?_
    rwa [← hvmin]
  · rw [hr5, hrxv]
    simp only [hσ4, vars_setVar, vars_setArr, String.reduceEq, reduceIte,
      eq_self_iff_true, if_true]
    omega


/-- **The min-degree peel pass**: fill the rank region with the
sentinel, set the countdown to the carrier size, then peel one vertex
per round. -/
def peelCom (ao aj dg mt ra nnSrc : String) : Com :=
  .seq (.assign "mp.n" (.var nnSrc))
  (.seq (peelInitCom ra "mp.n" "mp.u")
  (.seq (.assign "mp.r" (.var "mp.n"))
    (.while (.lt (.lit 0) (.var "mp.r")) (peelRoundCom ao aj dg mt ra))))

set_option maxHeartbeats 1000000 in
/-- **The peel pass leaves the pinned min-degree elimination ranking**
— `RankArr` at `mdPerm F`, whose value at `v` *is* `mdRank F v`. The
ranks are written counting down: the first vertex peeled — the
minimum-degree vertex of the whole carrier, least index first — gets
`N - 1`, matching `mdRankAux`'s own `S.card - 1`. -/
theorem peelCom_spec {ao aj dg mt ra nnSrc : String}
    (hoa : ao ≠ aj) (hom : ao ≠ mt) (hod : ao ≠ dg)
    (ham : aj ≠ mt) (had : aj ≠ dg) (hmd : mt ≠ dg)
    (hro : ra ≠ ao) (hrj : ra ≠ aj) (hrd : ra ≠ dg) (hrm : ra ≠ mt)
    {B N : ℕ} (hB : N + N * N + 1 < B) {F : SimpleGraph (Fin N)} :
    Spec B
      (fun σ => DelAdjSt ao aj dg mt F (∅ : Set (Fin N)) σ ∧
        N ≤ (σ.arrs ra).length ∧ σ.vars nnSrc = N)
      (peelCom ao aj dg mt ra nnSrc)
      (fun _ σ' => RankArr ra (mdPerm F) σ')
      (86 * N * N + 43 * N + 14) := by
  classical
  have hNB : N < B := by omega
  rintro σ ⟨hdel0, hralen0, hnsrc⟩
  -- name the carrier size
  have hrun1 : Run B (.assign "mp.n" (.var nnSrc)) σ (σ.setVar "mp.n" N) 2 := by
    refine (Run.assign (v := N) ?_).mono (by simp)
    rw [← hnsrc]
    exact evalB_var (by omega)
  -- the sentinel pass
  obtain ⟨σ2, hrun2, ⟨hnn2, hralen2, hfill2⟩, hfv2, hfa2, -, -⟩ :=
    (peelInit_spec (ra := ra) (nn := "mp.n") (ux := "mp.u") (by decide) hNB).frame.run
      (σ := σ.setVar "mp.n" N) ⟨by simp, by simpa using hralen0⟩
  have hfa2' : ∀ a : String, a ≠ ra → σ2.arrs a = σ.arrs a := by
    intro a hane
    exact hfa2 a (by simp [peelInitCom, Com.warrs, hane])
  have hrun3 : Run B (.assign "mp.r" (.var "mp.n")) σ2 (σ2.setVar "mp.r" N) 2 := by
    refine (Run.assign (v := N) ?_).mono (by simp)
    rw [← hnn2]
    exact evalB_var (by omega)
  set σ3 : Env := σ2.setVar "mp.r" N with hσ3
  -- the loop
  have hcond : ∀ τ : Env, PeelInv ao aj dg mt ra "mp.n" "mp.r" F τ →
      (Cond.lt (.lit 0) (.var "mp.r")).evalB B τ
        = some (decide (0 < τ.vars "mp.r")) := by
    intro τ hI
    obtain ⟨T, -, -, -, hrxv, -, -, -⟩ := hI
    have hTc : T.card ≤ N := by
      have := Finset.card_le_card (Finset.subset_univ T)
      simpa using this
    have h1 : (Expr.lit 0).evalB B τ = some 0 := evalB_lit (by omega)
    have h2 : (Expr.var "mp.r").evalB B τ = some (τ.vars "mp.r") :=
      evalB_var (by omega)
    simp [Cond.evalB, h1, h2]
  have hloop := Spec.while_count (B := B) (P := PeelInv ao aj dg mt ra "mp.n" "mp.r" F)
    (PeelInv ao aj dg mt ra "mp.n" "mp.r" F) (fun τ => τ.vars "mp.r") (86 * N + 28)
    (fun τ hI => ⟨_, hcond τ hI⟩)
    ((peelRound_spec hoa hom hod ham had hmd hro hrj hrd hrm hB).pre
      (by
        rintro τ ⟨hI, htrue⟩
        refine ⟨hI, ?_⟩
        rw [hcond τ hI] at htrue
        simpa using htrue))
    (fun _ hI => hI)
    (K := (1 + 3 + (86 * N + 28)) * N + 4)
    (by
      rintro τ ⟨T, -, -, -, hrxv, -, -, -⟩
      have hTc : T.card ≤ N := by
        have := Finset.card_le_card (Finset.subset_univ T)
        simpa using this
      have hsz : (Cond.lt (Expr.lit 0) (Expr.var "mp.r")).size = 3 := by simp
      simp only [hsz]
      have hmul : (1 + 3 + (86 * N + 28)) * τ.vars "mp.r"
          ≤ (1 + 3 + (86 * N + 28)) * N := Nat.mul_le_mul_left _ (by omega)
      omega)
  -- the initial invariant
  have hunivc : ((↑(Finset.univ : Finset (Fin N)) : Set (Fin N))ᶜ) = (∅ : Set (Fin N)) := by
    ext z; simp
  have hinv3 : PeelInv ao aj dg mt ra "mp.n" "mp.r" F σ3 := by
    refine ⟨Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hunivc]
      refine hdel0.of_eq ?_ ?_ ?_ ?_ <;>
        simp only [hσ3, arrs_setVar] <;>
        first
          | exact hfa2' ao (Ne.symm hro) | exact hfa2' aj (Ne.symm hrj)
          | exact hfa2' dg (Ne.symm hrd) | exact hfa2' mt (Ne.symm hrm)
    · simp only [hσ3, arrs_setVar]; exact hralen2
    · simp only [hσ3, vars_setVar, String.reduceEq, reduceIte]; exact hnn2
    · simp only [hσ3, vars_setVar, eq_self_iff_true, if_true, Finset.card_univ,
        Fintype.card_fin]
    · intro x _
      simp only [hσ3, arrs_setVar]
      exact hfill2 (x : ℕ) x.isLt
    · intro x hx
      exact absurd (Finset.mem_univ x) hx
    · intro x _
      rfl
  obtain ⟨σ4, hrun4, hinv4, hfalse4⟩ := hloop.run hinv3
  have hrx0 : σ4.vars "mp.r" = 0 := by
    rw [hcond σ4 hinv4] at hfalse4
    simpa using hfalse4
  obtain ⟨T, hdelT, hralenT, hnnT, hrxT, hliveT, hdeadT, -⟩ := hinv4
  have hTempty : T = ∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨σ4, (hrun1.seq (hrun2.seq (hrun3.seq hrun4))).mono (by nlinarith), ?_, ?_⟩
  · exact hralenT
  · intro x
    rw [hdeadT x (by rw [hTempty]; simp)]
    rfl

/-! ## §10 The peel pass at `CovMdPeelIn` -/

/-- The peel writes four arrays and nothing else. -/
theorem peelCom_arrs_eq {ao aj dg mt ra nnSrc : String} {B K : ℕ} {σ σ' : Env}
    (h : Run B (peelCom ao aj dg mt ra nnSrc) σ σ' K) (b : String)
    (h1 : b ≠ ra) (h2 : b ≠ aj) (h3 : b ≠ dg) (h4 : b ≠ mt) :
    σ'.arrs b = σ.arrs b :=
  h.frame_arr b (by
    simp [peelCom, peelInitCom, peelRoundCom, peelScanCom, peelScanBody,
      delAdjCom, delAdjBody, Com.warrs, h1, h2, h3, h4])

/-- The peel assigns to twelve scratch scalars and nothing else. -/
theorem peelCom_vars_eq {ao aj dg mt ra nnSrc : String} {B K : ℕ} {σ σ' : Env}
    (h : Run B (peelCom ao aj dg mt ra nnSrc) σ σ' K) (y : String)
    (h1 : y ≠ "mp.n") (h2 : y ≠ "mp.u") (h3 : y ≠ "mp.b") (h4 : y ≠ "mp.k")
    (h5 : y ≠ "mp.r") (h6 : y ≠ "mp.v") (h7 : y ≠ "dl.i") (h8 : y ≠ "dl.w")
    (h9 : y ≠ "dl.p") (h10 : y ≠ "dl.l") (h11 : y ≠ "dl.u") (h12 : y ≠ "dl.q") :
    σ'.vars y = σ.vars y :=
  h.frame_var y (by
    simp [peelCom, peelInitCom, peelRoundCom, peelScanCom, peelScanBody,
      delAdjCom, delAdjBody, Com.wvars, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12])

/-- A level-tagged name of a four-character base is never one of the
peel's four-character scratch names, unless the bases coincide. -/
theorem lv_ne_len4 {s t : String} (hs : s.length = 4) (ht : t.length = 4)
    (hst : s ≠ t) (j : ℕ) : lv s j ≠ t := by
  intro hc
  have hl : (lv s j).length = t.length := by rw [hc]
  rw [lv_length, hs, ht] at hl
  have hj : j = 0 := by omega
  rw [hj, lv_zero] at hc
  exact hst hc

/-- The arena's two cells survive the peel: they are level-tagged
copies of four-character bases distinct from every scratch name. -/
theorem arena_vars_eq_of_peel {ao aj dg mt ra nnSrc : String} {B K : ℕ}
    {σ σ' : Env} (h : Run B (peelCom ao aj dg mt ra nnSrc) σ σ' K) (j : ℕ) :
    σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN ∧
      σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS := by
  constructor <;>
    refine peelCom_vars_eq h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact lv_ne_len4 (by decide) (by decide) (by decide) j

open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.CoverRoutine (mdChain mdPerm)

set_option maxHeartbeats 1000000 in
/-- **Named residual (1a-ii) of `SolveSweepOrder`, discharged
verbatim**: the min-degree peel pass, at the concrete program
`peelCom` and the budget `86·N² + 43·N + 14`.

The scratch descriptor `Smp` the pass asks for is the rank region's
allocation and nothing else. The budget counts an `O(N)` scan per
round, not the bucket queue the residual's docstring mentions: the
`N²` term is the scan, the `54·d` of each round's delete is absorbed
in it. -/
theorem covMdPeelIn_peelCom (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Ssw : ℕ → Env → Prop) (hq : 1 ≤ q)
    (hnd : ∀ j, aoO j ≠ ajO j ∧ aoO j ≠ mtO j ∧ aoO j ≠ dgO j ∧
      ajO j ≠ mtO j ∧ ajO j ≠ dgO j ∧ mtO j ≠ dgO j ∧
      ra j ≠ aoO j ∧ ra j ≠ ajO j ∧ ra j ≠ dgO j ∧ ra j ≠ mtO j)
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ ra j ∧ b ≠ ajO j ∧ b ≠ dgO j ∧ b ≠ mtO j)
    (hSsw : ∀ (j : ℕ) (σ σ' : Env),
      (∀ b : String, b ≠ ra j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
        σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ≠ "mp.n" → y ≠ "mp.u" → y ≠ "mp.b" → y ≠ "mp.k" →
        y ≠ "mp.r" → y ≠ "mp.v" → y ≠ "dl.i" → y ≠ "dl.w" → y ≠ "dl.p" →
        y ≠ "dl.l" → y ≠ "dl.u" → y ≠ "dl.q" → σ'.vars y = σ.vars y) →
      Ssw j σ → Ssw j σ') :
    CovMdPeelIn C hC φ R G c w q ℓp htabF hbf Adm ca co ra aoO ajO dgO mtO
      (fun j σ => n ≤ (σ.arrs (ra j)).length) Ssw
      (fun j => peelCom (aoO j) (ajO j) (dgO j) (mtO j) (ra j) (arenaNames j).nN)
      (fun _ A => 86 * A.N * A.N + 43 * A.N + 14) := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hAW, hdel, hca, hco, hSmp, hSswσ⟩ := hσ
  obtain ⟨ho1, ho2, ho3, ha1, ha2, hm1, hr1, hr2, hr3, hr4⟩ := hnd j
  have henc : EncodesGraph x n G := hx.1
  have hlen := henc.length_eq
  have hAN : A.N ≤ n := by
    have h := Fintype.card_le_of_embedding A.up
    simpa using h
  have hBnd : A.N + A.N * A.N + 1 < mcB q x := by
    have h1 : A.N * A.N ≤ n * n := Nat.mul_le_mul hAN hAN
    have h2 : (x.length + 1) * (x.length + 1) ≤ mcB q x := by
      rw [mcB, pow_two]
      exact Nat.le_mul_of_pos_left _ hq
    have h3 : n * n + n + 1 < (x.length + 1) * (x.length + 1) := by nlinarith
    omega
  have hnN : σ.vars (arenaNames j).nN = A.N := hAW.n_eq
  obtain ⟨σ', hrun, hrank⟩ :=
    (peelCom_spec ho1 ho2 ho3 ha1 ha2 hm1 hr1 hr2 hr3 hr4 hBnd
      (F := (mdChain A.G R).toGraph) (nnSrc := (arenaNames j).nN)).run
      ⟨hdel, le_trans hAN hSmp, hnN⟩
  have hlenEq := run_arrs_length_eq hrun
  have harrs : ∀ b : String, b ≠ ra j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
      σ'.arrs b = σ.arrs b := fun b h1 h2 h3 h4 => peelCom_arrs_eq hrun b h1 h2 h3 h4
  have hvars : ∀ y : String, y ≠ "mp.n" → y ≠ "mp.u" → y ≠ "mp.b" → y ≠ "mp.k" →
      y ≠ "mp.r" → y ≠ "mp.v" → y ≠ "dl.i" → y ≠ "dl.w" → y ≠ "dl.p" →
      y ≠ "dl.l" → y ≠ "dl.u" → y ≠ "dl.q" → σ'.vars y = σ.vars y :=
    fun y => peelCom_vars_eq hrun y
  obtain ⟨hnNeq, hnSeq⟩ := arena_vars_eq_of_peel hrun j
  refine ⟨σ', hrun, ?_, hrank, ?_, ?_, hSsw j σ σ' harrs hlenEq hvars hSswσ⟩
  · refine arenaStW_of_eq hAW hnNeq hnSeq ?_ ?_ ?_ ?_ ?_
    · obtain ⟨k1, k2, k3, k4⟩ := harn j _ (Or.inl rfl)
      exact harrs _ k1 k2 k3 k4
    · obtain ⟨k1, k2, k3, k4⟩ := harn j _ (Or.inr (Or.inl rfl))
      exact harrs _ k1 k2 k3 k4
    · obtain ⟨k1, k2, k3, k4⟩ := harn j _ (Or.inr (Or.inr (Or.inl rfl)))
      exact harrs _ k1 k2 k3 k4
    · obtain ⟨k1, k2, k3, k4⟩ := harn j _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      exact harrs _ k1 k2 k3 k4
    · obtain ⟨k1, k2, k3, k4⟩ := harn j _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      exact harrs _ k1 k2 k3 k4
  · rw [hlenEq (ca j)]; exact hca
  · rw [hlenEq (co j)]; exact hco

end Lax3Proofs.Prog
