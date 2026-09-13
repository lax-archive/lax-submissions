import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fintype.EquivFin
import Lax17Proofs.Source.ExpanderMinor

namespace Lax17Proofs

universe u v w

/-!
# The subcubic target expansion for Theorem 8.1

The first reduction in the proof of Theorem 8.1 of `expander.pdf` replaces an
arbitrary finite target graph `H` by a graph of maximum degree at most three
which contains `H` as a minor and has linear vertices-plus-edges complexity.

For each vertex `w` of `H`, the expansion has a path with `degree w + 1`
vertices.  Each incident edge of `H` is assigned to one distinct position of
this path, using an arbitrary finite ordering of the neighbor set of `w`; the
two assigned positions for an edge are then joined by a cross-edge.  Contracting
each path recovers the original target graph.
-/

namespace SimpleGraph


open Finset

set_option linter.unusedSectionVars false

variable {W : Type u} [Fintype W] [DecidableEq W]

namespace SubcubicExpansion

variable (H : _root_.SimpleGraph W) [DecidableRel H.Adj]

/-- Vertices of the standard subcubic expansion of `H`: a path of length
`degree w + 1` over each original vertex `w`. -/
abbrev Vertex : Type u :=
  Sigma fun w : W => Fin (H.degree w + 1)

instance instFintypeVertex : Fintype (Vertex H) := by
  dsimp [Vertex]
  infer_instance

instance instDecidableEqVertex : DecidableEq (Vertex H) := by
  classical
  infer_instance

/-- The index assigned to a neighbor in the finite ordering of `w`'s neighbor
set. -/
noncomputable def neighborIndex {w v : W} (h : H.Adj w v) :
    Fin (H.degree w) :=
  (H.neighborFinset w).equivFin ⟨v, (H.mem_neighborFinset w v).2 h⟩

/-- The neighbor occupying a given incident-edge slot at `w`. -/
noncomputable def neighborAt (w : W) (i : Fin (H.degree w)) : W :=
  ((H.neighborFinset w).equivFin.symm i).1

theorem neighborAt_adj (w : W) (i : Fin (H.degree w)) :
    H.Adj w (neighborAt H w i) := by
  classical
  have hmem :
      ((H.neighborFinset w).equivFin.symm i).1 ∈ H.neighborFinset w :=
    ((H.neighborFinset w).equivFin.symm i).2
  exact (H.mem_neighborFinset w _).1 hmem

@[simp] theorem neighborAt_neighborIndex {w v : W} (h : H.Adj w v) :
    neighborAt H w (neighborIndex H h) = v := by
  classical
  let hv : v ∈ H.neighborFinset w := (H.mem_neighborFinset w v).2 h
  have hsub :
      (H.neighborFinset w).equivFin.symm
          ((H.neighborFinset w).equivFin ⟨v, hv⟩) = ⟨v, hv⟩ := by
    exact (H.neighborFinset w).equivFin.symm_apply_apply ⟨v, hv⟩
  exact congrArg Subtype.val hsub

/-- Two expansion vertices are consecutive along one of the vertex-fiber paths. -/
def PathAdj (x y : Vertex H) : Prop :=
  x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)

/-- Two expansion vertices are the two slots assigned to an original edge of
`H`. -/
def CrossAdj (x y : Vertex H) : Prop :=
  ∃ h : H.Adj x.1 y.1,
    x.2.val = (neighborIndex H h).val ∧
      y.2.val = (neighborIndex H h.symm).val

theorem PathAdj.symm {x y : Vertex H} (h : PathAdj H x y) :
    PathAdj H y x := by
  rcases h with ⟨hxy, hidx⟩
  exact ⟨hxy.symm, hidx.symm⟩

theorem CrossAdj.symm {x y : Vertex H} (h : CrossAdj H x y) :
    CrossAdj H y x := by
  rcases h with ⟨hxy, hx, hy⟩
  exact ⟨hxy.symm, hy, hx⟩

theorem PathAdj.not_loop (x : Vertex H) : ¬ PathAdj H x x := by
  intro h
  rcases h with ⟨_, hidx | hidx⟩ <;> omega

theorem CrossAdj.not_loop (x : Vertex H) : ¬ CrossAdj H x x := by
  intro h
  rcases h with ⟨hxx, _, _⟩
  exact H.loopless.irrefl x.1 hxx

/-- The standard subcubic expansion graph.  It is the union of all fiber paths
and all cross-edges corresponding to original edges of `H`. -/
noncomputable def graph : _root_.SimpleGraph (Vertex H) where
  Adj x y := PathAdj H x y ∨ CrossAdj H x y
  symm := by
    intro x y h
    rcases h with hpath | hcross
    · exact Or.inl hpath.symm
    · exact Or.inr hcross.symm
  loopless := ⟨by
    intro x h
    rcases h with hpath | hcross
    · exact PathAdj.not_loop H x hpath
    · exact CrossAdj.not_loop H x hcross⟩

noncomputable instance instDecidableRelGraph : DecidableRel (graph H).Adj := by
  classical
  dsimp [graph, PathAdj, CrossAdj]
  infer_instance

noncomputable instance instFintypeEdgeSetGraph : Fintype (graph H).edgeSet := by
  classical
  infer_instance

@[simp] theorem graph_adj {x y : Vertex H} :
    (graph H).Adj x y ↔ PathAdj H x y ∨ CrossAdj H x y :=
  Iff.rfl

/-- The predecessor of an expansion vertex on its fiber path, if it exists. -/
def pathPred? (x : Vertex H) : Option (Vertex H) :=
  if h : 0 < x.2.val then
    some ⟨x.1, ⟨x.2.val - 1, by omega⟩⟩
  else
    none

/-- The successor of an expansion vertex on its fiber path, if it exists. -/
def pathSucc? (x : Vertex H) : Option (Vertex H) :=
  if h : x.2.val + 1 < H.degree x.1 + 1 then
    some ⟨x.1, ⟨x.2.val + 1, h⟩⟩
  else
    none

/-- The cross-neighbor of an expansion vertex, if its fiber position is assigned
to an original edge. -/
noncomputable def crossNeighbor? (x : Vertex H) : Option (Vertex H) :=
  if h : x.2.val < H.degree x.1 then
    let v := neighborAt H x.1 ⟨x.2.val, h⟩
    let hvx : H.Adj v x.1 := (neighborAt_adj H x.1 ⟨x.2.val, h⟩).symm
    some ⟨v, ⟨(neighborIndex H hvx).val, by
      exact Nat.lt_trans (neighborIndex H hvx).isLt (Nat.lt_succ_self _)⟩⟩
  else
    none

/-- A three-element candidate set containing all neighbors of an expansion
vertex. -/
noncomputable def neighborCandidates (x : Vertex H) : Finset (Vertex H) :=
  (pathPred? H x).toFinset ∪ (pathSucc? H x).toFinset ∪
    (crossNeighbor? H x).toFinset

theorem card_option_toFinset_le_one {α : Type*} [DecidableEq α]
    (o : Option α) : o.toFinset.card ≤ 1 := by
  cases o <;> simp

theorem neighborCandidates_card_le_three (x : Vertex H) :
    (neighborCandidates H x).card ≤ 3 := by
  classical
  unfold neighborCandidates
  calc
    ((pathPred? H x).toFinset ∪ (pathSucc? H x).toFinset ∪
        (crossNeighbor? H x).toFinset).card
        ≤ ((pathPred? H x).toFinset ∪ (pathSucc? H x).toFinset).card +
            (crossNeighbor? H x).toFinset.card := Finset.card_union_le _ _
    _ ≤ ((pathPred? H x).toFinset.card + (pathSucc? H x).toFinset.card) +
            (crossNeighbor? H x).toFinset.card := by
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (1 + 1) + 1 := by
          exact Nat.add_le_add
            (Nat.add_le_add (card_option_toFinset_le_one _)
              (card_option_toFinset_le_one _))
            (card_option_toFinset_le_one _)
    _ = 3 := by omega

theorem pathPred?_mem_of_adj {x y : Vertex H}
    (hxy : PathAdj H x y) (hyx : y.2.val + 1 = x.2.val) :
    y ∈ (pathPred? H x).toFinset := by
  classical
  rcases x with ⟨wx, ix⟩
  rcases y with ⟨wy, iy⟩
  dsimp [PathAdj] at hxy hyx ⊢
  have hfirst : wy = wx := hxy.1.symm
  subst wy
  have hpos : 0 < ix.val := by omega
  have hval : iy.val = ix.val - 1 := by omega
  simp [pathPred?, hpos]
  apply Fin.ext
  exact hval

theorem pathSucc?_mem_of_adj {x y : Vertex H}
    (hxy : PathAdj H x y) (hxy' : x.2.val + 1 = y.2.val) :
    y ∈ (pathSucc? H x).toFinset := by
  classical
  rcases x with ⟨wx, ix⟩
  rcases y with ⟨wy, iy⟩
  dsimp [PathAdj] at hxy hxy' ⊢
  have hfirst : wy = wx := hxy.1.symm
  subst wy
  have hlt : ix.val + 1 < H.degree wx + 1 := by
    rw [hxy']
    exact iy.isLt
  simp [pathSucc?, hlt]
  apply Fin.ext
  exact hxy'.symm

theorem crossNeighbor?_mem_of_adj {x y : Vertex H}
    (hxy : CrossAdj H x y) :
    y ∈ (crossNeighbor? H x).toFinset := by
  classical
  rcases x with ⟨wx, ix⟩
  rcases y with ⟨wy, iy⟩
  dsimp [CrossAdj] at hxy ⊢
  rcases hxy with ⟨h, hxidx, hyidx⟩
  have hxlt : ix.val < H.degree wx := by
    rw [hxidx]
    exact (neighborIndex H h).isLt
  simp [crossNeighbor?, hxlt]
  have hwy : wy = neighborAt H wx ⟨ix.val, hxlt⟩ := by
    simp [neighborAt_neighborIndex H h, hxidx]
  constructor
  · exact hwy
  · subst wy
    apply heq_of_eq
    apply Fin.ext
    simp [hyidx]

theorem mem_neighborCandidates_of_adj {x y : Vertex H}
    (hxy : (graph H).Adj x y) :
    y ∈ neighborCandidates H x := by
  classical
  rcases hxy with hpath | hcross
  · rcases hpath.2 with hsucc | hpred
    · exact by
        unfold neighborCandidates
        simp [pathSucc?_mem_of_adj H hpath hsucc]
    · exact by
        unfold neighborCandidates
        simp [pathPred?_mem_of_adj H hpath hpred]
  · exact by
      unfold neighborCandidates
      simp [crossNeighbor?_mem_of_adj H hcross]

theorem degreeAtMost_three (x : Vertex H) :
    DegreeAtMost (graph H) x 3 := by
  classical
  refine ⟨(neighborCandidates H x).filter fun y => (graph H).Adj x y, ?_, ?_⟩
  intro y
  constructor
  · intro hy
    exact (Finset.mem_filter.1 hy).2
  · intro hxy
    exact Finset.mem_filter.2 ⟨mem_neighborCandidates_of_adj H hxy, hxy⟩
  · exact (Finset.card_filter_le _ _).trans (neighborCandidates_card_le_three H x)

/-- The expansion graph has maximum degree at most three. -/
theorem maxDegreeAtMost_three :
    MaxDegreeAtMost (graph H) 3 := by
  intro x
  exact degreeAtMost_three H x

/-- The branch set corresponding to `w`: the whole fiber path over `w`. -/
noncomputable def branchSet (w : W) : Finset (Vertex H) :=
  Finset.univ.filter fun x => x.1 = w

@[simp] theorem mem_branchSet {w : W} {x : Vertex H} :
    x ∈ branchSet H w ↔ x.1 = w := by
  simp [branchSet]

theorem branchSet_nonempty (w : W) : (branchSet H w).Nonempty := by
  classical
  exact ⟨⟨w, 0⟩, by simp⟩

/-- The path graph on a fiber maps onto the induced branch-set graph. -/
noncomputable def fiberPathHom (w : W) :
    _root_.SimpleGraph.pathGraph (H.degree w + 1) →g
      (graph H).induce {x : Vertex H | x ∈ branchSet H w} where
  toFun i := ⟨⟨w, i⟩, by simp⟩
  map_rel' := by
    intro i j hij
    rw [_root_.SimpleGraph.pathGraph_adj] at hij
    exact Or.inl ⟨rfl, hij⟩

theorem fiberPathHom_surjective (w : W) :
    Function.Surjective (fiberPathHom H w) := by
  classical
  intro x
  rcases x with ⟨x, hx⟩
  rcases x with ⟨w', i⟩
  have hw : w' = w := by simpa using hx
  subst w'
  refine ⟨i, ?_⟩
  apply Subtype.ext
  rfl

theorem branchSet_connected (w : W) :
    ((graph H).induce {x : Vertex H | x ∈ branchSet H w}).Connected := by
  classical
  exact _root_.SimpleGraph.Connected.map (fiberPathHom H w)
    (fiberPathHom_surjective H w)
    (_root_.SimpleGraph.pathGraph_connected (H.degree w))

theorem branchSet_disjoint {u v : W} (huv : u ≠ v) :
    Disjoint (branchSet H u) (branchSet H v) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxu hxv
  have hu : x.1 = u := (mem_branchSet H).1 hxu
  have hv : x.1 = v := (mem_branchSet H).1 hxv
  exact huv (hu.symm.trans hv)

theorem branchSet_adjacent {u v : W} (huv : H.Adj u v) :
    ∃ x ∈ branchSet H u, ∃ y ∈ branchSet H v, (graph H).Adj x y := by
  classical
  let x : Vertex H :=
    ⟨u, ⟨(neighborIndex H huv).val,
      Nat.lt_trans (neighborIndex H huv).isLt (Nat.lt_succ_self _)⟩⟩
  let y : Vertex H :=
    ⟨v, ⟨(neighborIndex H huv.symm).val,
      Nat.lt_trans (neighborIndex H huv.symm).isLt (Nat.lt_succ_self _)⟩⟩
  refine ⟨x, by simp [x], y, by simp [y], ?_⟩
  exact Or.inr ⟨huv, rfl, rfl⟩

/-- Contracting each fiber path in the expansion recovers `H`. -/
theorem isMinor_graph : IsMinor H (graph H) :=
  IsMinor.of_branchSets (branchSet H) (branchSet_nonempty H)
    (branchSet_connected H) (fun {_ _} huv => branchSet_disjoint (H := H) huv)
    (fun {_ _} huv => branchSet_adjacent (H := H) huv)

/-- The finset-neighborhood degree bound implies mathlib's numerical degree
bound. -/
theorem degree_le_of_degreeAtMost {X : Type*} [Fintype X] [DecidableEq X]
    {G : _root_.SimpleGraph X} [DecidableRel G.Adj] {x : X} {d : ℕ}
    (h : DegreeAtMost G x d) :
    G.degree x ≤ d := by
  rcases h with ⟨N, hN, hcard⟩
  have hN_eq : N = G.neighborFinset x := by
    ext y
    exact (hN y).trans (G.mem_neighborFinset x y).symm
  simpa [hN_eq] using hcard

/-- A finite subcubic graph has at most three times as many edges as vertices.
This deliberately avoids division by two; the weaker linear bound is enough
for the target-size reduction. -/
theorem edgeFinset_card_le_three_mul_card_of_maxDegreeAtMost_three
    {X : Type*} [Fintype X] [DecidableEq X]
    {G : _root_.SimpleGraph X} [DecidableRel G.Adj]
    (hmax : MaxDegreeAtMost G 3) :
    G.edgeFinset.card ≤ 3 * Fintype.card X := by
  classical
  have hsum_le : (∑ x : X, G.degree x) ≤ ∑ _x : X, 3 := by
    exact Finset.sum_le_sum fun x _ =>
      degree_le_of_degreeAtMost (hmax x)
  have htwice : 2 * G.edgeFinset.card ≤ 3 * Fintype.card X := by
    calc
      2 * G.edgeFinset.card = ∑ x : X, G.degree x := by
        exact (G.sum_degrees_eq_twice_card_edges).symm
      _ ≤ ∑ _x : X, 3 := hsum_le
      _ = 3 * Fintype.card X := by
        simp [Finset.sum_const, mul_comm]
  omega

/-- The expansion has `|V(H)| + 2|E(H)|` vertices. -/
theorem card_vertex_eq :
    Fintype.card (Vertex H) =
      Fintype.card W + 2 * H.edgeFinset.card := by
  classical
  calc
    Fintype.card (Vertex H)
        = ∑ w : W, Fintype.card (Fin (H.degree w + 1)) := by
          change Fintype.card (Sigma fun w : W => Fin (H.degree w + 1)) =
            ∑ w : W, Fintype.card (Fin (H.degree w + 1))
          exact Fintype.card_sigma
    _ = ∑ w : W, (H.degree w + 1) := by
          simp
    _ = (∑ w : W, H.degree w) + ∑ _w : W, 1 := by
          rw [Finset.sum_add_distrib]
    _ = 2 * H.edgeFinset.card + Fintype.card W := by
          rw [H.sum_degrees_eq_twice_card_edges]
          simp
    _ = Fintype.card W + 2 * H.edgeFinset.card := by
          omega

/-- The standard expansion has linear vertices-plus-edges complexity. -/
theorem targetComplexity_graph_le :
    targetComplexity (graph H) ≤ 8 * targetComplexity H := by
  classical
  let n := Fintype.card W
  let e := H.edgeFinset.card
  let n' := Fintype.card (Vertex H)
  let e' := (graph H).edgeFinset.card
  have hn' : n' = n + 2 * e := by
    simpa [n', n, e] using card_vertex_eq H
  have he' : e' ≤ 3 * n' := by
    simpa [e', n'] using
      edgeFinset_card_le_three_mul_card_of_maxDegreeAtMost_three
        (G := graph H) (maxDegreeAtMost_three H)
  calc
    targetComplexity (graph H) = n' + e' := by
      simp [targetComplexity, n', e']
    _ ≤ n' + 3 * n' := by
      exact Nat.add_le_add_left he' n'
    _ = 4 * n' := by omega
    _ = 4 * (n + 2 * e) := by rw [hn']
    _ ≤ 8 * (n + e) := by omega
    _ = 8 * targetComplexity H := by
      simp [targetComplexity, n, e, mul_add]

end SubcubicExpansion

/-- Concrete provider for the standard reduction from arbitrary finite targets
to subcubic targets in Theorem 8.1. -/
theorem subcubicMinorExpansionProvider :
    SubcubicMinorExpansionProvider.{u} 8 := by
  intro W _ _ H hEdge
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  refine ⟨{
    W' := SubcubicExpansion.Vertex H
    instFintype := SubcubicExpansion.instFintypeVertex H
    instDecidableEq := SubcubicExpansion.instDecidableEqVertex H
    H' := SubcubicExpansion.graph H
    instDecidableRel := SubcubicExpansion.instDecidableRelGraph H
    instEdgeSet := SubcubicExpansion.instFintypeEdgeSetGraph H
    maxDegree := SubcubicExpansion.maxDegreeAtMost_three H
    minor := SubcubicExpansion.isMinor_graph H
    complexity_bound := ?_
  }⟩
  have htarget_eq :
      @targetComplexity W _ H H.fintypeEdgeSet =
        @targetComplexity W _ H hEdge := by
    unfold targetComplexity
    congr 1
    congr 1
    ext e
    simp
  simpa [htarget_eq] using SubcubicExpansion.targetComplexity_graph_le H

/-- Full fixed-constant Theorem 8.1 from the subcubic reservoir alternative,
using the concrete target-splitting construction above. -/
theorem expanderMinorTheoremAt_of_reservoirAlternativeAt
    {separatorScale branchScale subcubicTargetScale targetScale n₀ : ℕ}
    (hsubTarget : 3 * separatorScale * branchScale ≤ subcubicTargetScale)
    (htarget : subcubicTargetScale * 8 ≤ targetScale)
    (halt : Theorem81ReservoirAlternativeAt.{u, u}
      separatorScale branchScale subcubicTargetScale n₀) :
    ExpanderMinorTheoremAt.{u, u} separatorScale targetScale n₀ :=
  expanderMinorTheoremAt_of_subcubicExpansion_and_reservoirAlternativeAt
    hsubTarget htarget subcubicMinorExpansionProvider halt

end SimpleGraph

end Lax17Proofs
