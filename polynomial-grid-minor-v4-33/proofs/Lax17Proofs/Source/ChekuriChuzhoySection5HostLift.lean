import Lax17Proofs.Source.ChekuriChuzhoySection5RealizedHind
import Lax17Proofs.Source.ChekuriChuzhoySection5WalkRealization

namespace Lax17Proofs

universe u v w

/-!
# Lifting Mader routes through realized contraction fibers

A Mader edge is first represented by a named walk in the doubled
Hind--Oellermann normal form.  This module lifts such a walk to the original
named host graph.  Traversed normal-form edges use their retained input names;
between consecutive edges, the lift stays inside the corresponding connected
contraction fiber.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

namespace NamedEdgeWalk

theorem ContainedIn.staysIn {H : FiniteEdgeIndexedGraph W}
    {x y : W} {P : H.NamedEdgeWalk x y} {X : Finset W}
    (hP : P.ContainedIn X) : P.StaysIn X := by
  induction P with
  | nil =>
      simpa using hP.1
  | cons e he tail ih =>
      rw [staysIn_cons]
      have hcons := (containedIn_cons_iff e he tail X).1 hP
      exact ⟨hcons.1, ih hcons.2⟩

end NamedEdgeWalk

namespace RealizedHindReduction

variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
variable (R : H.RealizedHindReduction terminals k)

/-- Union of the original-graph fibers indexed by `X`. -/
noncomputable def fiberUnion (X : Finset R.Vertex) : Finset W :=
  X.biUnion R.fiber

theorem mem_fiberUnion {X : Finset R.Vertex} {w : W} :
    w ∈ R.fiberUnion X ↔ ∃ z ∈ X, w ∈ R.fiber z := by
  classical
  simp [fiberUnion]

theorem fiber_subset_fiberUnion {X : Finset R.Vertex} {z : R.Vertex}
    (hz : z ∈ X) :
    R.fiber z ⊆ R.fiberUnion X := by
  intro w hw
  exact R.mem_fiberUnion.mpr ⟨z, hz, hw⟩

/-- Orient the retained original edge according to an oriented doubled edge
of the normal form. -/
theorem exists_edgeOrigin_joins_fibers
    (e : R.graph.doubleEdges.Edge) {a b : R.Vertex}
    (he : R.graph.doubleEdges.Joins e a b) :
    ∃ x y : W, H.Joins (R.edgeOrigin e.1) x y ∧
      x ∈ R.fiber a ∧ y ∈ R.fiber b := by
  rcases R.edgeOrigin_crosses_fibers e.1 with horigin | horigin
  · rcases he with he | he
    · have hleft : R.graph.left e.1 = a := by simpa using he.1
      have hright : R.graph.right e.1 = b := by simpa using he.2
      exact ⟨H.left (R.edgeOrigin e.1), H.right (R.edgeOrigin e.1),
        Or.inl ⟨rfl, rfl⟩, by simpa [hleft] using horigin.1,
        by simpa [hright] using horigin.2⟩
    · have hright : R.graph.right e.1 = a := by simpa using he.1
      have hleft : R.graph.left e.1 = b := by simpa using he.2
      exact ⟨H.right (R.edgeOrigin e.1), H.left (R.edgeOrigin e.1),
        Or.inr ⟨rfl, rfl⟩, by simpa [hright] using horigin.2,
        by simpa [hleft] using horigin.1⟩
  · rcases he with he | he
    · have hleft : R.graph.left e.1 = a := by simpa using he.1
      have hright : R.graph.right e.1 = b := by simpa using he.2
      exact ⟨H.right (R.edgeOrigin e.1), H.left (R.edgeOrigin e.1),
        Or.inr ⟨rfl, rfl⟩, by simpa [hleft] using horigin.1,
        by simpa [hright] using horigin.2⟩
    · have hright : R.graph.right e.1 = a := by simpa using he.1
      have hleft : R.graph.left e.1 = b := by simpa using he.2
      exact ⟨H.left (R.edgeOrigin e.1), H.right (R.edgeOrigin e.1),
        Or.inl ⟨rfl, rfl⟩, by simpa [hright] using horigin.2,
        by simpa [hleft] using horigin.1⟩

/-- Every edge used by a lifted walk is either the retained origin of a
normal-form edge in `P`, or lies wholly inside one contraction fiber visited
by `P`. -/
def IsLiftOf {a b : R.Vertex}
    (P : R.graph.doubleEdges.NamedEdgeWalk a b)
    {x y : W} (Q : H.NamedEdgeWalk x y) : Prop :=
  ∀ q ∈ Q.edgeList,
    (∃ e ∈ P.edgeList, q = R.edgeOrigin e.1) ∨
      ∃ z ∈ P.vertexSet,
        H.left q ∈ R.fiber z ∧ H.right q ∈ R.fiber z

/-- Lift a doubled normal-form walk between arbitrary prescribed
representatives of its endpoint fibers. -/
theorem exists_liftDoubledWalk
    {a b : R.Vertex}
    (P : R.graph.doubleEdges.NamedEdgeWalk a b)
    {x y : W} (hx : x ∈ R.fiber a) (hy : y ∈ R.fiber b) :
    ∃ Q : H.NamedEdgeWalk x y,
      Q.ContainedIn (R.fiberUnion P.vertexSet) ∧ R.IsLiftOf P Q := by
  classical
  induction P generalizing x with
  | nil a =>
      rcases R.fiber_connected a x hx y hy with ⟨Q, hQ⟩
      refine ⟨Q, hQ.mono ?_, ?_⟩
      · exact R.fiber_subset_fiberUnion (by simp)
      · intro q hq
        exact Or.inr ⟨a, by simp, (hQ.2.2 q hq)⟩
  | @cons a c b e he tail ih =>
      rcases R.exists_edgeOrigin_joins_fibers e he with
        ⟨u, v, huv, hu, hv⟩
      rcases R.fiber_connected a x hx u hu with ⟨B, hB⟩
      rcases ih hv hy with ⟨Q, hQcontained, hQlift⟩
      let E : H.NamedEdgeWalk u v :=
        .cons (R.edgeOrigin e.1) huv (.nil v)
      have haVertex :
          a ∈ (NamedEdgeWalk.cons e he tail).vertexSet := by simp
      have htailSubset :
          R.fiberUnion tail.vertexSet ⊆
            R.fiberUnion (NamedEdgeWalk.cons e he tail).vertexSet := by
        intro w hw
        rcases R.mem_fiberUnion.mp hw with ⟨z, hz, hwz⟩
        exact R.mem_fiberUnion.mpr ⟨z, by simp [hz], hwz⟩
      have hBfull :
          B.ContainedIn
            (R.fiberUnion (NamedEdgeWalk.cons e he tail).vertexSet) :=
        hB.mono (R.fiber_subset_fiberUnion haVertex)
      have hEfull :
          E.ContainedIn
            (R.fiberUnion (NamedEdgeWalk.cons e he tail).vertexSet) := by
        rw [NamedEdgeWalk.containedIn_cons_iff]
        refine ⟨R.fiber_subset_fiberUnion haVertex hu, ?_⟩
        simp only [NamedEdgeWalk.containedIn_nil]
        exact R.fiber_subset_fiberUnion (by simp) hv
      have hQfull :
          Q.ContainedIn
            (R.fiberUnion (NamedEdgeWalk.cons e he tail).vertexSet) :=
        hQcontained.mono htailSubset
      refine ⟨B.append (E.append Q),
        hBfull.append (hEfull.append hQfull), ?_⟩
      intro q hq
      simp only [NamedEdgeWalk.edgeList_append, List.mem_append] at hq
      rcases hq with hq | hq | hq
      · exact Or.inr ⟨a, haVertex, (hB.2.2 q hq)⟩
      · simp only [E, NamedEdgeWalk.edgeList_cons,
          NamedEdgeWalk.edgeList_nil, List.mem_singleton] at hq
        subst q
        exact Or.inl ⟨e, by simp, rfl⟩
      · rcases hQlift q hq with hroute | hinterior
        · rcases hroute with ⟨f, hf, rfl⟩
          exact Or.inl ⟨f, by simp [hf], rfl⟩
        · rcases hinterior with ⟨z, hz, hqz⟩
          exact Or.inr ⟨z, by simp [hz], hqz⟩

end RealizedHindReduction
end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
