import Lax17Proofs.Source.ChekuriChuzhoySection5RealizedHind
import Lax17Proofs.Source.ChekuriChuzhoySection5MaderElimination
import Lax17Proofs.Source.ChekuriChuzhoySection5WalkRealization

namespace Lax17Proofs

universe u v w

/-!
# Edge-disjoint histories for Mader splitting

This module records how every edge present during a one-center Mader
decomposition is realized by a named-edge walk in the graph before any split.
The invariant needed downstream is exact: distinct current edges use disjoint
sets of base edge copies.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {H : FiniteEdgeIndexedGraph W} {x y z : W}

namespace NamedEdgeWalk

/-- Change only the endpoint indices of a named-edge walk. -/
def copy (P : H.NamedEdgeWalk x y) {x' y' : W}
    (hx : x = x') (hy : y = y') : H.NamedEdgeWalk x' y' :=
  hx ▸ hy ▸ P

@[simp] theorem edgeList_copy (P : H.NamedEdgeWalk x y)
    {x' y' : W} (hx : x = x') (hy : y = y') :
    (P.copy hx hy).edgeList = P.edgeList := by
  subst x'
  subst y'
  rfl

@[simp] theorem vertexSet_copy (P : H.NamedEdgeWalk x y)
    {x' y' : W} (hx : x = x') (hy : y = y') :
    (P.copy hx hy).vertexSet = P.vertexSet := by
  subst x'
  subst y'
  rfl

/-- Reverse `P` onto an accumulator whose source is the source of `P`. -/
protected def reverseAux {x y z : W} :
    H.NamedEdgeWalk x y → H.NamedEdgeWalk x z → H.NamedEdgeWalk y z
  | .nil _, Q => Q
  | .cons e he tail, Q =>
      tail.reverseAux
        (.cons e ((H.joins_comm e _ _).mp he) Q)

/-- Reverse a named-edge walk, reversing the order and orientation of all
traversed edge copies. -/
def reverse (P : H.NamedEdgeWalk x y) : H.NamedEdgeWalk y x :=
  P.reverseAux (.nil x)

theorem edgeList_reverseAux (P : H.NamedEdgeWalk x y)
    {w : W} (Q : H.NamedEdgeWalk x w) :
    (P.reverseAux Q).edgeList = P.edgeList.reverse ++ Q.edgeList := by
  induction P generalizing w with
  | nil => rfl
  | cons e he P ih =>
      simpa [NamedEdgeWalk.reverseAux, List.append_assoc] using
        ih (.cons e ((H.joins_comm e _ _).mp he) Q)

@[simp] theorem edgeList_reverse (P : H.NamedEdgeWalk x y) :
    P.reverse.edgeList = P.edgeList.reverse := by
  simp [reverse, edgeList_reverseAux]

theorem vertexSet_reverseAux (P : H.NamedEdgeWalk x y)
    {w : W} (Q : H.NamedEdgeWalk x w) :
    (P.reverseAux Q).vertexSet = P.vertexSet ∪ Q.vertexSet := by
  induction P generalizing w with
  | nil a =>
      change Q.vertexSet = {a} ∪ Q.vertexSet
      symm
      exact Finset.union_eq_right.mpr (by
        intro v hv
        have hva : v = a := Finset.mem_singleton.mp hv
        subst v
        exact source_mem_vertexSet Q)
  | @cons a b c e he P ih =>
      rw [NamedEdgeWalk.reverseAux, ih]
      simp only [vertexSet_cons]
      have hb : b ∈ P.vertexSet := source_mem_vertexSet P
      have ha : a ∈ Q.vertexSet := source_mem_vertexSet Q
      calc
        P.vertexSet ∪ insert b Q.vertexSet =
            P.vertexSet ∪ Q.vertexSet := by
          rw [Finset.union_insert,
            Finset.insert_eq_self.mpr (Finset.mem_union_left _ hb)]
        _ = insert a P.vertexSet ∪ Q.vertexSet := by
          rw [Finset.insert_union,
            Finset.insert_eq_self.mpr (Finset.mem_union_right _ ha)]

@[simp] theorem vertexSet_reverse (P : H.NamedEdgeWalk x y) :
    P.reverse.vertexSet = P.vertexSet := by
  rw [reverse, vertexSet_reverseAux]
  exact Finset.union_eq_left.mpr (by
    intro v hv
    have hvx : v = x := Finset.mem_singleton.mp hv
    subst v
    exact source_mem_vertexSet P)

@[simp] theorem append_nil (P : H.NamedEdgeWalk x y) :
    P.append (.nil y) = P := by
  induction P with
  | nil => rfl
  | cons e he P ih =>
      simp [append, ih]

theorem append_assoc (P : H.NamedEdgeWalk x y)
    (Q : H.NamedEdgeWalk y z) {w : W} (R : H.NamedEdgeWalk z w) :
    (P.append Q).append R = P.append (Q.append R) := by
  induction P with
  | nil => rfl
  | cons e he P ih =>
      simp [append, ih]

@[simp] theorem append_reverseAux (P : H.NamedEdgeWalk x y)
    (Q : H.NamedEdgeWalk y z) {w : W} (R : H.NamedEdgeWalk x w) :
    (P.append Q).reverseAux R = Q.reverseAux (P.reverseAux R) := by
  induction P with
  | nil => rfl
  | cons e he P ih =>
      exact ih Q (.cons e ((H.joins_comm e _ _).mp he) R)

@[simp] theorem reverseAux_append (P : H.NamedEdgeWalk x y)
    (Q : H.NamedEdgeWalk x z) {w : W} (R : H.NamedEdgeWalk z w) :
    (P.reverseAux Q).append R = P.reverseAux (Q.append R) := by
  induction P with
  | nil => rfl
  | cons e he P ih =>
      exact ih (.cons e ((H.joins_comm e _ _).mp he) Q)

theorem reverseAux_eq_reverse_append (P : H.NamedEdgeWalk x y)
    (Q : H.NamedEdgeWalk x z) :
    P.reverseAux Q = P.reverse.append Q := by
  rw [reverse, reverseAux_append]
  rfl

@[simp] theorem reverse_append (P : H.NamedEdgeWalk x y)
    (Q : H.NamedEdgeWalk y z) :
    (P.append Q).reverse = Q.reverse.append P.reverse := by
  change (P.append Q).reverseAux (.nil x) =
    (Q.reverseAux (.nil y)).append (P.reverseAux (.nil x))
  rw [append_reverseAux, reverseAux_eq_reverse_append]
  rfl

end NamedEdgeWalk

/-! ## Histories and one-step transport -/

/-- A realization of every edge of `current` by an edge-nonempty walk in
`base`, with disjoint base-edge support for distinct current edges. -/
structure MaderEdgeHistory
    (base current : FiniteEdgeIndexedGraph W) where
  route :
    (e : current.Edge) →
      base.NamedEdgeWalk (current.left e) (current.right e)
  routeEdges_nonempty :
    ∀ e, (route e).edgeList.toFinset.Nonempty
  route_nodup :
    ∀ e, (route e).edgeList.Nodup
  routeEdges_pairwise_disjoint :
    ∀ {e f}, e ≠ f →
      Disjoint (route e).edgeList.toFinset (route f).edgeList.toFinset

namespace MaderEdgeHistory

variable {base current : FiniteEdgeIndexedGraph W}

/-- The base edge copies used by the route of a current edge. -/
def routeEdges (R : MaderEdgeHistory base current)
    (e : current.Edge) : Finset base.Edge :=
  (R.route e).edgeList.toFinset

theorem routeEdges_nonempty' (R : MaderEdgeHistory base current)
    (e : current.Edge) : (R.routeEdges e).Nonempty :=
  R.routeEdges_nonempty e

theorem routeEdges_pairwise_disjoint'
    (R : MaderEdgeHistory base current) {e f : current.Edge}
    (hef : e ≠ f) :
    Disjoint (R.routeEdges e) (R.routeEdges f) :=
  R.routeEdges_pairwise_disjoint hef

/-- The history before any splitting: every edge is represented by its
one-edge walk. -/
def identity (base : FiniteEdgeIndexedGraph W) :
    MaderEdgeHistory base base where
  route e :=
    .cons e (Or.inl ⟨rfl, rfl⟩) (.nil (base.right e))
  routeEdges_nonempty := by
    intro e
    simp
  route_nodup := by
    intro e
    simp
  routeEdges_pairwise_disjoint := by
    intro e f hef
    simpa using hef

/-- Follow the route of `e` in either of its two valid orientations. -/
def routeAlong (R : MaderEdgeHistory base current)
    (e : current.Edge) {a b : W} (he : current.Joins e a b) :
    base.NamedEdgeWalk a b :=
  if hleft : current.left e = a then
    let hright : current.right e = b := by
      rcases he with hforward | hbackward
      · exact hforward.2
      · exfalso
        exact current.end_ne e (hleft.trans hbackward.1.symm)
    (R.route e).copy hleft hright
  else
    let hbackward := he.resolve_left (fun hforward => hleft hforward.1)
    (R.route e).reverse.copy hbackward.1 hbackward.2

@[simp] theorem routeAlong_routeEdges
    (R : MaderEdgeHistory base current)
    (e : current.Edge) {a b : W} (he : current.Joins e a b) :
    (R.routeAlong e he).edgeList.toFinset = R.routeEdges e := by
  by_cases hleft : current.left e = a
  · simp [routeAlong, hleft, routeEdges]
  · simp [routeAlong, hleft, routeEdges]

theorem routeAlong_nodup
    (R : MaderEdgeHistory base current)
    (e : current.Edge) {a b : W} (he : current.Joins e a b) :
    (R.routeAlong e he).edgeList.Nodup := by
  by_cases hleft : current.left e = a
  · simpa [routeAlong, hleft] using
      R.route_nodup e
  · simpa [routeAlong, hleft] using
      R.route_nodup e

/-- The route introduced by splitting `p`: traverse the first route from its
other endpoint to the center, then the second route away from the center. -/
def splitNewRoute (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s) :
    base.NamedEdgeWalk p.firstOther p.secondOther :=
  (R.routeAlong p.first
      ((current.joins_comm p.first s p.firstOther).mp p.first_ends)).append
    (R.routeAlong p.second p.second_ends)

@[simp] theorem splitNewRoute_routeEdges
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s) :
    (R.splitNewRoute p).edgeList.toFinset =
      R.routeEdges p.first ∪ R.routeEdges p.second := by
  simp [splitNewRoute]

theorem splitNewRoute_nodup
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s) :
    (R.splitNewRoute p).edgeList.Nodup := by
  rw [splitNewRoute, NamedEdgeWalk.edgeList_append]
  apply (R.routeAlong_nodup p.first
    ((current.joins_comm p.first s p.firstOther).mp p.first_ends)).append
      (R.routeAlong_nodup p.second p.second_ends)
  apply List.disjoint_toFinset_iff_disjoint.mp
  rw [R.routeAlong_routeEdges p.first,
    R.routeAlong_routeEdges p.second]
  exact R.routeEdges_pairwise_disjoint p.edge_ne

/-- Route assignment after one Mader split.  Old edges retain their routes;
the optional new edge receives `splitNewRoute`. -/
def splitRoute (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (e : (current.maderSplit p).Edge) :
    base.NamedEdgeWalk
      ((current.maderSplit p).left e) ((current.maderSplit p).right e) :=
  match e with
  | .inl f => R.route f.1
  | .inr _ => R.splitNewRoute p

@[simp] theorem splitRoute_old
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (e : {e : current.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    R.splitRoute p (.inl e) = R.route e.1 :=
  rfl

@[simp] theorem splitRoute_new
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (u : {u : Unit // p.firstOther ≠ p.secondOther}) :
    R.splitRoute p (.inr u) = R.splitNewRoute p :=
  rfl

private theorem splitRoute_routeEdges_nonempty
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (e : (current.maderSplit p).Edge) :
    (R.splitRoute p e).edgeList.toFinset.Nonempty := by
  cases e with
  | inl e =>
      simpa using R.routeEdges_nonempty e.1
  | inr u =>
      rcases R.routeEdges_nonempty p.first with ⟨f, hf⟩
      have hunion :
          (R.routeEdges p.first ∪ R.routeEdges p.second).Nonempty :=
        ⟨f, Finset.mem_union_left _ hf⟩
      rw [splitRoute_new]
      exact (R.splitNewRoute_routeEdges p).symm ▸ hunion

private theorem splitRoute_route_nodup
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (e : (current.maderSplit p).Edge) :
    (R.splitRoute p e).edgeList.Nodup := by
  cases e with
  | inl e =>
      simpa using R.route_nodup e.1
  | inr u =>
      simpa using R.splitNewRoute_nodup p

private theorem splitRoute_routeEdges_pairwise_disjoint
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    {e f : (current.maderSplit p).Edge} (hef : e ≠ f) :
    Disjoint (R.splitRoute p e).edgeList.toFinset
      (R.splitRoute p f).edgeList.toFinset := by
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          apply R.routeEdges_pairwise_disjoint
          intro h
          apply hef
          exact congrArg Sum.inl (Subtype.ext h)
      | inr u =>
          rw [splitRoute_old, splitRoute_new]
          have hunion := Finset.disjoint_union_right.mpr
            ⟨R.routeEdges_pairwise_disjoint e.2.1,
              R.routeEdges_pairwise_disjoint e.2.2⟩
          exact (R.splitNewRoute_routeEdges p).symm ▸ hunion
  | inr u =>
      cases f with
      | inl f =>
          rw [splitRoute_new, splitRoute_old]
          have hunion := Finset.disjoint_union_left.mpr
            ⟨R.routeEdges_pairwise_disjoint f.2.1.symm,
              R.routeEdges_pairwise_disjoint f.2.2.symm⟩
          exact (R.splitNewRoute_routeEdges p).symm ▸ hunion
      | inr v =>
          have huv : u = v := Subsingleton.elim u v
          exact (hef (congrArg Sum.inr huv)).elim

/-- Transport an edge-disjoint history through one Mader split. -/
def split (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s) :
    MaderEdgeHistory base (current.maderSplit p) where
  route := R.splitRoute p
  routeEdges_nonempty := R.splitRoute_routeEdges_nonempty p
  route_nodup := R.splitRoute_route_nodup p
  routeEdges_pairwise_disjoint :=
    R.splitRoute_routeEdges_pairwise_disjoint p

@[simp] theorem split_route_old
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (e : {e : current.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    (R.split p).route (.inl e) = R.route e.1 :=
  rfl

@[simp] theorem split_route_new
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (u : {u : Unit // p.firstOther ≠ p.secondOther}) :
    (R.split p).route (.inr u) = R.splitNewRoute p :=
  rfl

@[simp] theorem split_routeEdges_old
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (e : {e : current.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    (R.split p).routeEdges (.inl e) = R.routeEdges e.1 :=
  rfl

@[simp] theorem split_routeEdges_new
    (R : MaderEdgeHistory base current)
    {s : W} (p : current.MaderSplitPair s)
    (u : {u : Unit // p.firstOther ≠ p.secondOther}) :
    (R.split p).routeEdges (.inr u) =
      R.routeEdges p.first ∪ R.routeEdges p.second := by
  exact R.splitNewRoute_routeEdges p

end MaderEdgeHistory

/-! ## Iteration through a complete one-center decomposition -/

namespace MaderEvenDecomposition

/-- Iterate an existing history through every split in a complete
decomposition. -/
def edgeHistory {base H : FiniteEdgeIndexedGraph W} {s : W}
    (D : MaderEvenDecomposition s H) (R : MaderEdgeHistory base H) :
    MaderEdgeHistory base D.finalGraph :=
  match D with
  | .done _ _ => R
  | .step _ p _ tail => tail.edgeHistory (R.split p)

/-- The canonical edge history of a complete decomposition, measured in its
initial graph. -/
def initialEdgeHistory {H : FiniteEdgeIndexedGraph W} {s : W}
    (D : MaderEvenDecomposition s H) :
    MaderEdgeHistory H D.finalGraph :=
  D.edgeHistory (MaderEdgeHistory.identity H)

end MaderEvenDecomposition

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
