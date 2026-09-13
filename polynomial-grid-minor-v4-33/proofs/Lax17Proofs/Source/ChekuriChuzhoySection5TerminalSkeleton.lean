import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic
import Lax17Proofs.Source.Menger

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 terminal skeleton

This file formalizes the output language of Chekuri--Chuzhoy, journal
Theorem 5.12.  The auxiliary graph is represented by a
finite edge index type and two endpoint maps.  In particular, different edge
indices may have the same endpoints, so the parallel edges created by doubling
and splitting are not collapsed by `SimpleGraph`.

The definitions below include a concrete producer from finite vertex-Menger
for the terminal-clean, grouped, node-disjoint part of the output.  The
Hind--Oellermann/Mader connectivity-and-degree producer is proved in
`ChekuriChuzhoySection5MaderElimination`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

/-! ## Finite edge-indexed multigraphs -/

/-- A finite loopless undirected multigraph with named edge copies.

The endpoint order is bookkeeping only.  Parallel edges are preserved because
`Edge` is an index type rather than a set of unordered vertex pairs. -/
structure FiniteEdgeIndexedGraph (W : Type u) where
  Edge : Type
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  left : Edge -> W
  right : Edge -> W
  end_ne : ∀ e, left e ≠ right e

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

instance (H : FiniteEdgeIndexedGraph W) : Fintype H.Edge := H.edgeFintype
instance (H : FiniteEdgeIndexedGraph W) : DecidableEq H.Edge := H.edgeDecidableEq

/-- The finite set of named edge copies incident with `w`. -/
noncomputable def incidentEdges (H : FiniteEdgeIndexedGraph W) (w : W) : Finset H.Edge := by
  classical
  exact Finset.univ.filter fun e => H.left e = w ∨ H.right e = w

/-- Degree counts edge copies, and therefore counts parallel edges separately. -/
noncomputable def degree (H : FiniteEdgeIndexedGraph W) (w : W) : Nat :=
  (H.incidentEdges w).card

/-- Whether a named edge has exactly one endpoint in `X`. -/
def Crosses (H : FiniteEdgeIndexedGraph W) (X : Finset W) (e : H.Edge) : Prop :=
  (H.left e ∈ X ∧ H.right e ∉ X) ∨
    (H.right e ∈ X ∧ H.left e ∉ X)

/-- Named edge copies crossing a vertex cut. -/
noncomputable def boundary (H : FiniteEdgeIndexedGraph W) (X : Finset W) : Finset H.Edge := by
  classical
  exact Finset.univ.filter (H.Crosses X)

@[simp] theorem mem_incidentEdges (H : FiniteEdgeIndexedGraph W) (w : W) (e : H.Edge) :
    e ∈ H.incidentEdges w ↔ H.left e = w ∨ H.right e = w := by
  simp [incidentEdges]

@[simp] theorem mem_boundary (H : FiniteEdgeIndexedGraph W) (X : Finset W) (e : H.Edge) :
    e ∈ H.boundary X ↔ H.Crosses X e := by
  simp [boundary]

theorem crosses_compl (H : FiniteEdgeIndexedGraph W) (X : Finset W) (e : H.Edge) :
    H.Crosses Xᶜ e ↔ H.Crosses X e := by
  simp only [Crosses, mem_compl]
  tauto

@[simp] theorem boundary_compl (H : FiniteEdgeIndexedGraph W) (X : Finset W) :
    H.boundary Xᶜ = H.boundary X := by
  ext e
  simp [H.crosses_compl X e]

@[simp] theorem boundary_empty (H : FiniteEdgeIndexedGraph W) :
    H.boundary ∅ = ∅ := by
  ext e
  simp [Crosses]

@[simp] theorem boundary_univ (H : FiniteEdgeIndexedGraph W) :
    H.boundary Finset.univ = ∅ := by
  ext e
  simp [Crosses]

/-- In a loopless edge-indexed graph, the singleton cut at `w` is its full
incidence set. -/
theorem boundary_singleton (H : FiniteEdgeIndexedGraph W) (w : W) :
    H.boundary {w} = H.incidentEdges w := by
  ext e
  simp only [mem_boundary, mem_incidentEdges, Crosses, mem_singleton]
  constructor
  · tauto
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨h, fun hr => H.end_ne e (h.trans hr.symm)⟩
    · exact Or.inr ⟨h, fun hl => H.end_ne e (hl.trans h.symm)⟩

/-- Cut-form terminal edge-connectivity for a finite edge-indexed multigraph. -/
def IsEdgeConnected (H : FiniteEdgeIndexedGraph W) (k : Nat) : Prop :=
  ∀ X : Finset W, X.Nonempty -> X ≠ Finset.univ -> k <= (H.boundary X).card

theorem IsEdgeConnected.mono {H : FiniteEdgeIndexedGraph W} {k l : Nat}
    (h : H.IsEdgeConnected k) (hlk : l <= k) : H.IsEdgeConnected l := by
  intro X hX hXproper
  exact hlk.trans (h X hX hXproper)

theorem IsEdgeConnected.le_degree_of_exists_ne
    {H : FiniteEdgeIndexedGraph W} {k : Nat} (h : H.IsEdgeConnected k)
    (w : W) (hex : ∃ z : W, z ≠ w) : k <= H.degree w := by
  have hsingleton : ({w} : Finset W) ≠ Finset.univ := by
    rintro heq
    rcases hex with ⟨z, hzw⟩
    have hz : z ∈ ({w} : Finset W) := by simp [heq]
    exact hzw (Finset.mem_singleton.mp hz)
  simpa [degree, H.boundary_singleton w] using
    h ({w} : Finset W) (by simp) hsingleton

/-- Delete one named edge copy.  Other parallel copies remain present. -/
def deleteEdge (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) :
    FiniteEdgeIndexedGraph W where
  Edge := {e : H.Edge // e ≠ e0}
  left e := H.left e.1
  right e := H.right e.1
  end_ne e := H.end_ne e.1

@[simp] theorem deleteEdge_left (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (e : (H.deleteEdge e0).Edge) :
    (H.deleteEdge e0).left e = H.left e.1 := rfl

@[simp] theorem deleteEdge_right (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (e : (H.deleteEdge e0).Edge) :
    (H.deleteEdge e0).right e = H.right e.1 := rfl

theorem deleteEdge_edgeCard (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) :
    Fintype.card (H.deleteEdge e0).Edge = Fintype.card H.Edge - 1 := by
  classical
  change Fintype.card {e : H.Edge // e ≠ e0} = Fintype.card H.Edge - 1
  rw [Fintype.card_subtype]
  rw [show (Finset.univ.filter fun e : H.Edge => e ≠ e0) =
      Finset.univ.erase e0 by ext e; simp]
  exact Finset.card_erase_of_mem (Finset.mem_univ e0)

theorem deleteEdge_degree_le (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (w : W) :
    (H.deleteEdge e0).degree w <= H.degree w := by
  classical
  let f : (H.deleteEdge e0).incidentEdges w -> H.incidentEdges w := fun e =>
    ⟨e.1.1, by
      apply (H.mem_incidentEdges w e.1.1).2
      rcases ((H.deleteEdge e0).mem_incidentEdges w e.1).1 e.2 with h | h
      · exact Or.inl h
      · exact Or.inr h⟩
  have hf : Function.Injective f := by
    intro e e' he
    have hval : e.1.1 = e'.1.1 :=
      congrArg (fun z : H.incidentEdges w => z.1) he
    exact Subtype.ext (Subtype.ext hval)
  unfold degree
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective f hf

theorem deleteEdge_boundary_le (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (X : Finset W) :
    ((H.deleteEdge e0).boundary X).card <= (H.boundary X).card := by
  classical
  let f : (H.deleteEdge e0).boundary X -> H.boundary X := fun e =>
    ⟨e.1.1, by
      apply (H.mem_boundary X e.1.1).2
      rcases ((H.deleteEdge e0).mem_boundary X e.1).1 e.2 with h | h
      · exact Or.inl h
      · exact Or.inr h⟩
  have hf : Function.Injective f := by
    intro e e' he
    have hval : e.1.1 = e'.1.1 :=
      congrArg (fun z : H.boundary X => z.1) he
    exact Subtype.ext (Subtype.ext hval)
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective f hf

/-! ## Split-off bookkeeping -/

/-- Two distinct edges incident with `s`, together with their other endpoints,
form a loopless split-off pair when the other endpoints are distinct. -/
structure SplitPair (H : FiniteEdgeIndexedGraph W) (s : W) where
  first : H.Edge
  second : H.Edge
  edge_ne : first ≠ second
  firstOther : W
  secondOther : W
  first_ends :
    (H.left first = s ∧ H.right first = firstOther) ∨
      (H.right first = s ∧ H.left first = firstOther)
  second_ends :
    (H.left second = s ∧ H.right second = secondOther) ∨
      (H.right second = s ∧ H.left second = secondOther)
  other_ne : firstOther ≠ secondOther

/-- Split off a pair at `s`: remove the two named copies and add one new copy
between their other endpoints. -/
def splitOff (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.SplitPair s) :
    FiniteEdgeIndexedGraph W where
  Edge := {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕ Unit
  left e := Sum.elim (fun f => H.left f.1) (fun _ => p.firstOther) e
  right e := Sum.elim (fun f => H.right f.1) (fun _ => p.secondOther) e
  end_ne e := by
    cases e with
    | inl f => exact H.end_ne f.1
    | inr _ => exact p.other_ne

@[simp] theorem splitOff_new_left (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.SplitPair s) :
    (H.splitOff p).left (Sum.inr ()) = p.firstOther := rfl

@[simp] theorem splitOff_new_right (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.SplitPair s) :
    (H.splitOff p).right (Sum.inr ()) = p.secondOther := rfl

@[simp] theorem splitOff_old_left (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.SplitPair s) (e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    (H.splitOff p).left (Sum.inl e) = H.left e.1 := rfl

@[simp] theorem splitOff_old_right (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.SplitPair s) (e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    (H.splitOff p).right (Sum.inl e) = H.right e.1 := rfl

theorem SplitPair.firstOther_ne_center {H : FiniteEdgeIndexedGraph W} {s : W}
    (p : H.SplitPair s) : p.firstOther ≠ s := by
  rcases p.first_ends with h | h
  · intro hs
    exact H.end_ne p.first (h.1.trans (h.2.trans hs).symm)
  · intro hs
    exact H.end_ne p.first ((h.2.trans hs).trans h.1.symm)

theorem SplitPair.secondOther_ne_center {H : FiniteEdgeIndexedGraph W} {s : W}
    (p : H.SplitPair s) : p.secondOther ≠ s := by
  rcases p.second_ends with h | h
  · intro hs
    exact H.end_ne p.second (h.1.trans (h.2.trans hs).symm)
  · intro hs
    exact H.end_ne p.second ((h.2.trans hs).trans h.1.symm)

theorem splitOff_edgeCard (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.SplitPair s) :
    Fintype.card (H.splitOff p).Edge = Fintype.card H.Edge - 1 := by
  classical
  change Fintype.card ({e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕ Unit) =
    Fintype.card H.Edge - 1
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_subtype]
  have hfirst : p.first ∈ (Finset.univ : Finset H.Edge) := Finset.mem_univ _
  have hsecond : p.second ∈ (Finset.univ.erase p.first : Finset H.Edge) := by
    simp [p.edge_ne.symm]
  have hpos : 0 < (Finset.univ.erase p.first : Finset H.Edge).card :=
    Finset.card_pos.mpr ⟨p.second, hsecond⟩
  have hcardErase : (Finset.univ.erase p.first : Finset H.Edge).card =
      Fintype.card H.Edge - 1 := by
    rw [Finset.card_erase_of_mem hfirst, Finset.card_univ]
  rw [show (Finset.univ.filter fun e : H.Edge => e ≠ p.first ∧ e ≠ p.second) =
      (Finset.univ.erase p.first).erase p.second by ext e; simp [and_comm]]
  rw [Finset.card_erase_of_mem hsecond, Finset.card_erase_of_mem hfirst]
  rw [hcardErase] at hpos
  rw [Finset.card_univ]
  omega

theorem even_ne_three {n : Nat} (h : Even n) : n ≠ 3 := by
  rcases h with ⟨m, rfl⟩
  omega

theorem even_eq_zero_or_two_le {n : Nat} (h : Even n) : n = 0 ∨ 2 <= n := by
  rcases h with ⟨m, rfl⟩
  omega

theorem even_sub_two {n : Nat} (h : Even n) : Even (n - 2) := by
  rcases h with ⟨m, rfl⟩
  by_cases hm : m = 0
  · simp [hm]
  · refine ⟨m - 1, by omega⟩

end FiniteEdgeIndexedGraph

/-! ## Terminal path skeletons and paper invariants -/

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {terminals : Finset V}

/-- The abstract vertices are exactly the designated host-graph terminals. -/
abbrev TerminalVertex (terminals : Finset V) := {v : V // v ∈ terminals}

/-- A finite parallel-edge-preserving terminal multigraph, one host path per
edge copy, and a genuine partition of the edge copies into nonempty groups. -/
structure TerminalPathSkeleton (G : _root_.SimpleGraph V)
    (terminals : Finset V) where
  graph : FiniteEdgeIndexedGraph (TerminalVertex terminals)
  hostPath : graph.Edge -> GraphPath G
  host_source : ∀ e, (hostPath e).source = (graph.left e).1
  host_target : ∀ e, (hostPath e).target = (graph.right e).1
  groups : Finpartition (Finset.univ : Finset graph.Edge)

namespace TerminalPathSkeleton

instance (S : TerminalPathSkeleton G terminals) : Fintype S.graph.Edge :=
  S.graph.edgeFintype

instance (S : TerminalPathSkeleton G terminals) : DecidableEq S.graph.Edge :=
  S.graph.edgeDecidableEq

/-- Number of routed abstract edge copies using one host edge. -/
noncomputable def hostEdgeLoad (S : TerminalPathSkeleton G terminals)
    (e : Sym2 V) : Nat :=
  (Finset.univ.filter fun a : S.graph.Edge => e ∈ (S.hostPath a).edgeSet).card

/-- A host edge is incident with the designated terminal set. -/
def HostEdgeIncidentToTerminals (e : Sym2 V) : Prop :=
  ∃ t ∈ terminals, t ∈ e

/-- Every abstract terminal cut has at least `k` named edge copies. -/
def TerminalEdgeConnected (S : TerminalPathSkeleton G terminals) (k : Nat) : Prop :=
  S.graph.IsEdgeConnected k

/-- Every group has at most `k` edge copies. -/
def GroupSizeAtMost (S : TerminalPathSkeleton G terminals) (k : Nat) : Prop :=
  ∀ U ∈ S.groups.parts, U.card <= k

/-- Abstract terminal degrees are bounded by a multiple of host degrees. -/
def TerminalDegreeCongestionAtMost
    (S : TerminalPathSkeleton G terminals) (c : Nat) : Prop :=
  ∀ t : TerminalVertex terminals,
    S.graph.degree t <= c * (G.neighborSet t.1).ncard

/-- Host edges incident with terminals occur in at most `c` routed paths. -/
def EndpointCongestionAtMost
    (S : TerminalPathSkeleton G terminals) (c : Nat) : Prop :=
  ∀ e : Sym2 V, e ∈ G.edgeSet ->
    HostEdgeIncidentToTerminals (terminals := terminals) e -> S.hostEdgeLoad e <= c

/-- No routed path has a designated terminal as an internal vertex. -/
def InternallyAvoidsTerminals (S : TerminalPathSkeleton G terminals) : Prop :=
  ∀ e : S.graph.Edge, (S.hostPath e).InternallyDisjointFromSet terminals

/-- `I` chooses exactly one edge copy from every group. -/
def IsGroupTransversal (S : TerminalPathSkeleton G terminals)
    (I : Finset S.graph.Edge) : Prop :=
  ∀ U ∈ S.groups.parts, (I ∩ U).card = 1

/-- Every one-per-group choice gives host paths that are node-disjoint except
for possible common endpoints. -/
def OnePerGroupInternallyNodeDisjoint
    (S : TerminalPathSkeleton G terminals) : Prop :=
  ∀ I : Finset S.graph.Edge, S.IsGroupTransversal I ->
    ∀ ⦃e⦄, e ∈ I -> ∀ ⦃f⦄, f ∈ I -> e ≠ f ->
      (S.hostPath e).InternallyDisjoint (S.hostPath f)

theorem TerminalEdgeConnected.mono {S : TerminalPathSkeleton G terminals}
    {k l : Nat} (h : S.TerminalEdgeConnected k) (hlk : l <= k) :
    S.TerminalEdgeConnected l :=
  FiniteEdgeIndexedGraph.IsEdgeConnected.mono h hlk

theorem GroupSizeAtMost.mono {S : TerminalPathSkeleton G terminals}
    {k l : Nat} (h : S.GroupSizeAtMost k) (hkl : k <= l) :
    S.GroupSizeAtMost l := by
  intro U hU
  exact (h U hU).trans hkl

theorem EndpointCongestionAtMost.mono {S : TerminalPathSkeleton G terminals}
    {c d : Nat} (h : S.EndpointCongestionAtMost c) (hcd : c <= d) :
    S.EndpointCongestionAtMost d := by
  intro e heG heT
  exact (h e heG heT).trans hcd

theorem terminal_mem_hostPath_isEndpoint
    (S : TerminalPathSkeleton G terminals) (havoid : S.InternallyAvoidsTerminals)
    (e : S.graph.Edge) {t : V} (htPath : t ∈ (S.hostPath e).vertexSet)
    (ht : t ∈ terminals) :
    t = (S.graph.left e).1 ∨ t = (S.graph.right e).1 := by
  rcases havoid e htPath ht with hsource | htarget
  · exact Or.inl (hsource.trans (S.host_source e))
  · exact Or.inr (htarget.trans (S.host_target e))

theorem hostPath_connects_terminal_endpoints
    (S : TerminalPathSkeleton G terminals) (e : S.graph.Edge) :
    (S.hostPath e).Connects ({(S.graph.left e).1} : Finset V)
      ({(S.graph.right e).1} : Finset V) := by
  exact Or.inl ⟨by simp [S.host_source e], by simp [S.host_target e]⟩

theorem hostPath_source_mem_terminals
    (S : TerminalPathSkeleton G terminals) (e : S.graph.Edge) :
    (S.hostPath e).source ∈ terminals := by
  rw [S.host_source e]
  exact (S.graph.left e).2

theorem hostPath_target_mem_terminals
    (S : TerminalPathSkeleton G terminals) (e : S.graph.Edge) :
    (S.hostPath e).target ∈ terminals := by
  rw [S.host_target e]
  exact (S.graph.right e).2

/-! ## A concrete skeleton producer from a path packing -/

variable {A B : Finset V}

/-- Clean a node-disjoint `A`--`B` packing and regard each path as one named
abstract edge.  Singleton groups make this a terminal skeleton on `A ∪ B`. -/
noncomputable def ofPathPacking (P : PathPacking G A B) (hAB : Disjoint A B) :
    TerminalPathSkeleton G (A ∪ B) where
  graph :=
    { Edge := P.Index
      left := fun i =>
        ⟨(P.cleanToTerminals.path i).source,
          Finset.mem_union_left B
            ((P.path i).cleanBetweenTerminalSets_source_mem (P.connects i))⟩
      right := fun i =>
        ⟨(P.cleanToTerminals.path i).target,
          Finset.mem_union_right A
            ((P.path i).cleanBetweenTerminalSets_target_mem (P.connects i))⟩
      end_ne := by
        intro i heq
        have hsourceA :=
          (P.path i).cleanBetweenTerminalSets_source_mem (P.connects i)
        have htargetB :=
          (P.path i).cleanBetweenTerminalSets_target_mem (P.connects i)
        have heqval : (P.cleanToTerminals.path i).source =
            (P.cleanToTerminals.path i).target := congrArg Subtype.val heq
        have heqval' :
            ((P.path i).cleanBetweenTerminalSets (P.connects i)).source =
              ((P.path i).cleanBetweenTerminalSets (P.connects i)).target := by
          simpa [PathPacking.cleanToTerminals] using heqval
        exact Finset.disjoint_left.mp hAB hsourceA (by
          rw [heqval']
          exact htargetB) }
  hostPath := P.cleanToTerminals.path
  host_source := fun _ => rfl
  host_target := fun _ => rfl
  groups := (⊥ : Finpartition (Finset.univ : Finset P.Index))

@[simp] theorem ofPathPacking_edgeCard (P : PathPacking G A B)
    (hAB : Disjoint A B) :
    Fintype.card (ofPathPacking P hAB).graph.Edge = P.card := rfl

theorem ofPathPacking_internallyAvoidsTerminals
    (P : PathPacking G A B) (hAB : Disjoint A B) :
    (ofPathPacking P hAB).InternallyAvoidsTerminals := by
  intro i
  exact P.cleanToTerminals_terminalClean i

theorem ofPathPacking_onePerGroupInternallyNodeDisjoint
    (P : PathPacking G A B) (hAB : Disjoint A B) :
    (ofPathPacking P hAB).OnePerGroupInternallyNodeDisjoint := by
  intro I _hI e _he f _hf hef
  have hnode := P.cleanToTerminals.node_disjoint hef
  intro v hve hvf
  exact False.elim (Finset.disjoint_left.mp hnode hve hvf)

theorem ofPathPacking_groupSizeAtMost_terminalCard
    (P : PathPacking G A B) (hAB : Disjoint A B) :
    (ofPathPacking P hAB).GroupSizeAtMost (A ∪ B).card := by
  intro U hU
  dsimp only [ofPathPacking] at hU
  rw [Finpartition.parts_bot] at hU
  rcases Finset.mem_map.mp hU with ⟨i, _hi, hUi⟩
  subst U
  have hnonempty : 1 <= (A ∪ B).card := by
    apply Finset.one_le_card.mpr
    exact ⟨(P.cleanToTerminals.path i).source,
      Finset.mem_union_left B
        ((P.path i).cleanBetweenTerminalSets_source_mem (P.connects i))⟩
  change 1 <= (A ∪ B).card
  exact hnonempty

theorem ofPathPacking_hostEdgeLoad_le_one
    (P : PathPacking G A B) (hAB : Disjoint A B) (e : Sym2 V) :
    (ofPathPacking P hAB).hostEdgeLoad e <= 1 := by
  classical
  rw [hostEdgeLoad, Finset.card_le_one]
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  by_contra hij
  have hnode := P.cleanToTerminals.node_disjoint hij
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hiEdges : s(x, y) ∈ (P.cleanToTerminals.path i).walk.edges :=
        List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using hi)
      have hjEdges : s(x, y) ∈ (P.cleanToTerminals.path j).walk.edges :=
        List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using hj)
      have hxi : x ∈ (P.cleanToTerminals.path i).vertexSet := by
        simpa [GraphPath.vertexSet] using
          (P.cleanToTerminals.path i).walk.fst_mem_support_of_mem_edges hiEdges
      have hxj : x ∈ (P.cleanToTerminals.path j).vertexSet := by
        simpa [GraphPath.vertexSet] using
          (P.cleanToTerminals.path j).walk.fst_mem_support_of_mem_edges hjEdges
      exact Finset.disjoint_left.mp hnode hxi hxj

theorem ofPathPacking_endpointCongestionAtMost_one
    (P : PathPacking G A B) (hAB : Disjoint A B) :
    (ofPathPacking P hAB).EndpointCongestionAtMost 1 := by
  intro e _heG _heT
  exact ofPathPacking_hostEdgeLoad_le_one P hAB e

/-- Finite Menger produces an exact-size terminal skeleton with all invariants
that only require node-disjoint cleaned paths, or a strictly smaller vertex
separator.  This is a genuine producer, not a provider-shaped restatement. -/
theorem exists_terminalSkeleton_or_separator
    (G : _root_.SimpleGraph V) (A B : Finset V) (k : Nat)
    (hAB : Disjoint A B) :
    (∃ S : TerminalPathSkeleton G (A ∪ B),
        Fintype.card S.graph.Edge = k ∧
        S.GroupSizeAtMost (A ∪ B).card ∧
        S.EndpointCongestionAtMost 1 ∧
        S.InternallyAvoidsTerminals ∧
        S.OnePerGroupInternallyNodeDisjoint) ∨
      ∃ X : Finset V, X.card < k ∧ STSeparator G A B X := by
  rcases Menger.finite_vertex_menger_sharp G A B k with hpaths | hsep
  · rcases HasAtLeastDisjointPaths.exists_exact hpaths with ⟨P, hPcard⟩
    left
    refine ⟨ofPathPacking P hAB, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hPcard
    · exact ofPathPacking_groupSizeAtMost_terminalCard P hAB
    · exact ofPathPacking_endpointCongestionAtMost_one P hAB
    · exact ofPathPacking_internallyAvoidsTerminals P hAB
    · exact ofPathPacking_onePerGroupInternallyNodeDisjoint P hAB
  · exact Or.inr hsep

end TerminalPathSkeleton

/-! ## Element-connectivity input and terminal-skeleton output -/

/-- A family of paths with common terminal endpoints, disjoint in host edges
and in all nonterminal vertices.  Sharing designated terminals is allowed. -/
structure TerminalElementPathPacking
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (a b : TerminalVertex terminals) where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  path : Index -> GraphPath G
  source_eq : ∀ i, (path i).source = a.1
  target_eq : ∀ i, (path i).target = b.1
  edge_disjoint : Pairwise fun i j => (path i).EdgeDisjoint (path j)
  nonterminal_disjoint :
    Pairwise fun i j => ∀ ⦃x : V⦄,
      x ∈ (path i).vertexSet -> x ∈ (path j).vertexSet -> x ∈ terminals

namespace TerminalElementPathPacking

instance {a b : TerminalVertex terminals}
    (P : TerminalElementPathPacking G terminals a b) : Fintype P.Index :=
  P.indexFintype

instance {a b : TerminalVertex terminals}
    (P : TerminalElementPathPacking G terminals a b) : DecidableEq P.Index :=
  P.indexDecidableEq

noncomputable def card {a b : TerminalVertex terminals}
    (P : TerminalElementPathPacking G terminals a b) : Nat :=
  Fintype.card P.Index

end TerminalElementPathPacking

/-- Every distinct terminal pair has at least `mu` element-disjoint paths. -/
def TerminalsElementConnectedAtLeast
    (G : _root_.SimpleGraph V) (terminals : Finset V) (mu : Nat) : Prop :=
  ∀ (a b : TerminalVertex terminals), a ≠ b ->
    ∃ P : TerminalElementPathPacking G terminals a b, mu <= P.card

theorem TerminalsElementConnectedAtLeast.mono {mu nu : Nat}
    (h : TerminalsElementConnectedAtLeast G terminals mu) (hnu : nu <= mu) :
    TerminalsElementConnectedAtLeast G terminals nu := by
  intro a b hab
  rcases h a b hab with ⟨P, hP⟩
  exact ⟨P, hnu.trans hP⟩

/-- All five semantic conclusions of journal Theorem 5.12, including its
parallel-edge-sensitive degree and connectivity bounds. -/
structure IsTheorem512Output
    (G : _root_.SimpleGraph V) (terminals : Finset V) (mu : Nat)
    (S : TerminalPathSkeleton G terminals) : Prop where
  terminal_edge_connected : S.TerminalEdgeConnected (2 * mu)
  group_size : S.GroupSizeAtMost terminals.card
  terminal_degree : S.TerminalDegreeCongestionAtMost 2
  endpoint_congestion : S.EndpointCongestionAtMost 2
  internal_terminal_avoidance : S.InternallyAvoidsTerminals
  one_per_group_node_disjoint : S.OnePerGroupInternallyNodeDisjoint

/-- Journal Theorem 5.12, stripped of its algorithmic running-time claim. -/
def Theorem512Statement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (terminals : Finset V) (mu : Nat),
      1 <= mu -> TerminalsElementConnectedAtLeast G terminals mu ->
        ∃ S : TerminalPathSkeleton G terminals,
          IsTheorem512Output G terminals mu S

end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
