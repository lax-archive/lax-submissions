import Lax17Proofs.Source.ChekuriChuzhoySection5HostBridge
import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Named-walk realization in the host graph

This module supplies finite support and containment utilities for
`FiniteEdgeIndexedGraph.NamedEdgeWalk`.  For the canonical finite naming of a
simple host graph, it also forgets the edge names to obtain a mathlib walk and
then cycle-erases that walk to a `GraphPath`.  The realization records exact
walk support and edge provenance before cycle erasure, and subset guarantees
after cycle erasure.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph
namespace NamedEdgeWalk


open Finset

variable {W : Type u} [DecidableEq W]
variable {H : FiniteEdgeIndexedGraph W} {x y z : W}

/-! ## Finite vertex support -/

/-- The finite set of vertices visited by a named-edge walk. -/
def vertexSet {x y : W} : H.NamedEdgeWalk x y -> Finset W
  | .nil x => {x}
  | .cons _ _ tail => insert x tail.vertexSet

@[simp] theorem vertexSet_nil (x : W) :
    (NamedEdgeWalk.nil (H := H) x).vertexSet = {x} := rfl

@[simp] theorem vertexSet_cons {a b c : W} (e : H.Edge)
    (he : H.Joins e a b) (P : H.NamedEdgeWalk b c) :
    (NamedEdgeWalk.cons e he P).vertexSet = insert a P.vertexSet := rfl

@[simp] theorem mem_vertexSet_nil {a v : W} :
    v ∈ (NamedEdgeWalk.nil (H := H) a).vertexSet ↔ v = a := by
  simp

@[simp] theorem mem_vertexSet_cons {a b c v : W} (e : H.Edge)
    (he : H.Joins e a b) (P : H.NamedEdgeWalk b c) :
    v ∈ (NamedEdgeWalk.cons e he P).vertexSet ↔
      v = a ∨ v ∈ P.vertexSet := by
  simp

@[simp] theorem source_mem_vertexSet (P : H.NamedEdgeWalk x y) :
    x ∈ P.vertexSet := by
  induction P with
  | nil => simp
  | cons e he P ih => simp

@[simp] theorem target_mem_vertexSet (P : H.NamedEdgeWalk x y) :
    y ∈ P.vertexSet := by
  induction P with
  | nil => simp
  | cons e he P ih => simp [ih]

@[simp] theorem vertexSet_append (P : H.NamedEdgeWalk x y)
    (Q : H.NamedEdgeWalk y z) :
    (P.append Q).vertexSet = P.vertexSet ∪ Q.vertexSet := by
  induction P generalizing z with
  | nil a =>
      change Q.vertexSet = {a} ∪ Q.vertexSet
      symm
      exact Finset.union_eq_right.mpr (by
        intro v hv
        have hva : v = a := Finset.mem_singleton.mp hv
        subst v
        exact source_mem_vertexSet Q)
  | @cons a b c e he P ih =>
      change insert a (P.append Q).vertexSet =
        insert a P.vertexSet ∪ Q.vertexSet
      rw [ih]
      exact (Finset.insert_union a P.vertexSet Q.vertexSet).symm

/-- Every vertex of `P` belongs to `X`. -/
def StaysIn (P : H.NamedEdgeWalk x y) (X : Finset W) : Prop :=
  P.vertexSet ⊆ X

@[simp] theorem staysIn_nil (a : W) (X : Finset W) :
    (NamedEdgeWalk.nil (H := H) a).StaysIn X ↔ a ∈ X := by
  simp [StaysIn]

@[simp] theorem staysIn_cons {a b c : W} (e : H.Edge)
    (he : H.Joins e a b) (P : H.NamedEdgeWalk b c) (X : Finset W) :
    (NamedEdgeWalk.cons e he P).StaysIn X ↔
      a ∈ X ∧ P.StaysIn X := by
  constructor
  · intro h
    refine ⟨h (by simp), ?_⟩
    intro v hv
    exact h (by simp [hv])
  · rintro ⟨ha, hP⟩ v hv
    simp only [vertexSet_cons, mem_insert] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact hP hv

@[simp] theorem staysIn_append (P : H.NamedEdgeWalk x y)
    (Q : H.NamedEdgeWalk y z) (X : Finset W) :
    (P.append Q).StaysIn X ↔ P.StaysIn X ∧ Q.StaysIn X := by
  rw [StaysIn, StaysIn, StaysIn, vertexSet_append]
  constructor
  · intro h
    exact ⟨fun _ hv => h (Finset.mem_union_left _ hv),
      fun _ hv => h (Finset.mem_union_right _ hv)⟩
  · rintro ⟨hP, hQ⟩ v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hP hv
    · exact hQ hv

theorem mem_of_staysIn {P : H.NamedEdgeWalk x y} {X : Finset W}
    (hP : P.StaysIn X) {v : W} (hv : v ∈ P.vertexSet) :
    v ∈ X :=
  hP hv

theorem StaysIn.mono {P : H.NamedEdgeWalk x y} {X Y : Finset W}
    (hP : P.StaysIn X) (hXY : X ⊆ Y) :
    P.StaysIn Y :=
  fun _ hv => hXY (hP hv)

/-! ## Realization in a finite simple host graph -/

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : _root_.SimpleGraph V) [Fintype G.edgeSet]

/-- A named host edge joining `a` to `b` is an adjacency of the host graph. -/
theorem host_adj_of_joins {e : (hostEdgeIndexedGraph G).Edge} {a b : V}
    (he : (hostEdgeIndexedGraph G).Joins e a b) :
    G.Adj a b := by
  have hmem := hostEdgeIndexedOrigin_mem G e
  rw [← hostEdgeIndexedOrigin_endpoints G e] at hmem
  have hadj :
      G.Adj ((hostEdgeIndexedGraph G).left e)
        ((hostEdgeIndexedGraph G).right e) := by
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hmem
  rcases he with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
  · rw [hleft, hright] at hadj
    exact hadj
  · rw [hleft, hright] at hadj
    exact hadj.symm

/-- The unordered host edge represented by a name that joins `a` and `b`. -/
theorem hostEdgeIndexedOrigin_eq_of_joins
    {e : (hostEdgeIndexedGraph G).Edge} {a b : V}
    (he : (hostEdgeIndexedGraph G).Joins e a b) :
    hostEdgeIndexedOrigin G e = s(a, b) := by
  rcases he with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
  · calc
      hostEdgeIndexedOrigin G e =
          s((hostEdgeIndexedGraph G).left e,
            (hostEdgeIndexedGraph G).right e) :=
        (hostEdgeIndexedOrigin_endpoints G e).symm
      _ = s(a, b) := by rw [hleft, hright]
  · calc
      hostEdgeIndexedOrigin G e =
          s((hostEdgeIndexedGraph G).left e,
            (hostEdgeIndexedGraph G).right e) :=
        (hostEdgeIndexedOrigin_endpoints G e).symm
      _ = s((hostEdgeIndexedGraph G).right e,
            (hostEdgeIndexedGraph G).left e) := Sym2.eq_swap
      _ = s(a, b) := by rw [hright, hleft]

/-- Forget the finite edge names of a named host walk. -/
noncomputable def toHostWalk {a b : V} :
    (hostEdgeIndexedGraph G).NamedEdgeWalk a b -> G.Walk a b
  | .nil _ => .nil
  | .cons _ he tail =>
      .cons (host_adj_of_joins G he) (toHostWalk tail)

@[simp] theorem toHostWalk_nil (a : V) :
    toHostWalk G (NamedEdgeWalk.nil (H := hostEdgeIndexedGraph G) a) =
      _root_.SimpleGraph.Walk.nil := rfl

@[simp] theorem toHostWalk_cons {a b c : V}
    (e : (hostEdgeIndexedGraph G).Edge)
    (he : (hostEdgeIndexedGraph G).Joins e a b)
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk b c) :
    toHostWalk G (NamedEdgeWalk.cons e he P) =
      _root_.SimpleGraph.Walk.cons (host_adj_of_joins G he)
        (toHostWalk G P) := rfl

/-- The host edges represented by the edge names traversed by `P`. -/
noncomputable def hostEdgeSet {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) : Finset (Sym2 V) :=
  (P.edgeList.map (hostEdgeIndexedOrigin G)).toFinset

@[simp] theorem hostEdgeSet_nil (a : V) :
    hostEdgeSet G
      (NamedEdgeWalk.nil (H := hostEdgeIndexedGraph G) a) = ∅ := by
  simp [hostEdgeSet]

@[simp] theorem hostEdgeSet_cons {a b c : V}
    (e : (hostEdgeIndexedGraph G).Edge)
    (he : (hostEdgeIndexedGraph G).Joins e a b)
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk b c) :
    hostEdgeSet G (NamedEdgeWalk.cons e he P) =
      insert (hostEdgeIndexedOrigin G e) (hostEdgeSet G P) := by
  simp [hostEdgeSet]

/-- Forgetting names preserves the visited vertex set exactly. -/
@[simp] theorem toHostWalk_support_toFinset {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) :
    (toHostWalk G P).support.toFinset = P.vertexSet := by
  induction P with
  | nil => simp
  | cons e he P ih => simp [ih]

/-- Forgetting names maps each traversed name to precisely its host edge. -/
theorem toHostWalk_edges {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) :
    (toHostWalk G P).edges =
      P.edgeList.map (hostEdgeIndexedOrigin G) := by
  induction P with
  | nil => rfl
  | cons e he P ih =>
      simp [ih, hostEdgeIndexedOrigin_eq_of_joins G he]

/-- Finite edge support is preserved exactly when edge names are forgotten. -/
@[simp] theorem toHostWalk_edges_toFinset {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) :
    (toHostWalk G P).edges.toFinset = hostEdgeSet G P := by
  rw [toHostWalk_edges]
  rfl

/-- Cycle-erase the realized host walk. -/
noncomputable def toHostPath {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) :
    GraphPath G :=
  GraphPath.ofWalk (toHostWalk G P)

@[simp] theorem toHostPath_source {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) :
    (toHostPath G P).source = a := rfl

@[simp] theorem toHostPath_target {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) :
    (toHostPath G P).target = b := rfl

/-- Cycle erasure introduces no vertex outside the named walk. -/
theorem toHostPath_vertexSet_subset {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) :
    (toHostPath G P).vertexSet ⊆ P.vertexSet := by
  intro v hv
  have hv' :=
    GraphPath.ofWalk_vertexSet_subset (toHostWalk G P) hv
  simpa using hv'

/-- Cycle erasure introduces no host edge outside the represented edge names. -/
theorem toHostPath_edgeSet_subset {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) :
    (toHostPath G P).edgeSet ⊆ hostEdgeSet G P := by
  intro e he
  have he' :=
    GraphPath.ofWalk_edgeSet_subset (toHostWalk G P) he
  simpa using he'

/-- A named walk staying in `X` realizes to a cycle-erased path staying in
`X`. -/
theorem toHostPath_staysIn {a b : V}
    (P : (hostEdgeIndexedGraph G).NamedEdgeWalk a b) (X : Finset V)
    (hP : P.StaysIn X) :
    (toHostPath G P).vertexSet ⊆ X :=
  subset_trans (toHostPath_vertexSet_subset G P) hP

end NamedEdgeWalk
end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
