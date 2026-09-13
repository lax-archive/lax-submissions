import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Lax17Proofs.Source.Degree

namespace Lax17Proofs

universe u v w

/-!
# Singh--Lau bounded-degree spanning-tree rounding

Chekuri--Chuzhoy Claim 5.17 invokes the bounded-degree spanning-tree theorem
of Singh and Lau.  The paper is an external dependency and is intentionally
recorded here as the exact unweighted LP-rounding statement consumed by
Section 5: a feasible point of the spanning-tree polytope with fractional
degree at most `B` yields a spanning tree of maximum degree at most `B + 1`.

The cost objective and the algorithmic running-time assertion are omitted
because neither is used by the existential grid-minor proof.  The complete
paper obligation is isolated as `BoundedDegreeSpanningTreeStatement`; the
axiom below only inhabits that proposition.

`SinghLauRounding.lean` proves `BoundedDegreeSpanningTreeStatement` as
`boundedDegreeSpanningTree_proved`.  The axiom below is retained only as the
original documentary contract; downstream proved code does not use it.
-/

namespace SimpleGraph
namespace SinghLau


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Whether both endpoints of an unordered pair lie in `S`. -/
def PairInside (S : Finset V) : Sym2 V → Prop :=
  Sym2.lift
    ⟨fun u v => u ∈ S ∧ v ∈ S, by
      intro u v
      exact propext and_comm⟩

@[simp] theorem pairInside_mk (S : Finset V) (u v : V) :
    PairInside S s(u, v) ↔ u ∈ S ∧ v ∈ S := by
  simp [PairInside]

/-- Host edges with both endpoints in `S`. -/
noncomputable def internalEdges
    (G : _root_.SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (PairInside S)

/-- Host edge copies incident with `v`, represented inside `edgeFinset`. -/
noncomputable def incidentEdges
    (G : _root_.SimpleGraph V) (v : V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e => v ∈ e

/-- Feasibility for the unweighted bounded-degree spanning-tree relaxation
used by Singh--Lau. -/
structure FeasibleBoundedDegreePoint
    (G : _root_.SimpleGraph V) (B : Nat) where
  weight : Sym2 V → Rat
  nonnegative : ∀ e ∈ G.edgeFinset, 0 ≤ weight e
  total :
    ∑ e ∈ G.edgeFinset, weight e = (Fintype.card V - 1 : Nat)
  forest :
    ∀ S : Finset V, S ≠ Finset.univ →
      ∑ e ∈ internalEdges G S, weight e ≤ (S.card - 1 : Nat)
  degree :
    ∀ v : V, ∑ e ∈ incidentEdges G v, weight e ≤ B

/-- The complete Singh--Lau paper obligation used by WP1C: additive-one
rounding of the bounded-degree spanning-tree polytope, with zero edge costs. -/
def BoundedDegreeSpanningTreeStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (B : Nat),
      1 < Fintype.card V →
        FeasibleBoundedDegreePoint G B →
          ∃ T : _root_.SimpleGraph V,
            T ≤ G ∧ T.IsTree ∧ MaxDegreeAtMost T (B + 1)



end SinghLau
end SimpleGraph

end Lax17Proofs
