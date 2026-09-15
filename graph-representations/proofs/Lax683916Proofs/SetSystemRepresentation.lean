import Lax683916.SetSystemRepresentation

namespace Lax683916Proofs.SetSystemRepresentation

open Lax683916.TwoUniformSetSystems
open Lax683916.SetSystemRepresentation

universe u

variable {V : Type u}

private theorem setSystem_ext {S T : TwoUniformSetSystem V} (h : S.sets = T.sets) : S = T := by
  rcases S with ⟨s, hs⟩
  rcases T with ⟨t, ht⟩
  simp only at h
  subst t
  rfl

/-- The 2-uniform set system consisting of the endpoint sets of a graph's edges. -/
def toSetSystem (G : SimpleGraph V) : TwoUniformSetSystem V where
  sets := {s | ∃ u v, G.Adj u v ∧ s = {u, v}}
  twoUniform s := by
    rintro ⟨u, v, huv, rfl⟩
    exact Set.ncard_pair huv.ne

/-- The simple graph whose edges are the members of a 2-uniform set system. -/
def toSimpleGraph (S : TwoUniformSetSystem V) : SimpleGraph V where
  Adj u v := {u, v} ∈ S.sets
  symm := ⟨fun u v h ↦ Set.pair_comm u v ▸ h⟩
  loopless := ⟨fun u h ↦ by
    have hcard := S.twoUniform {u, u} h
    simp at hcard⟩

/-- Endpoint pairs belong to a graph's set-system image exactly when they are edges. -/
theorem pair_mem_toSetSystem_iff (G : SimpleGraph V) (u v : V) :
    {u, v} ∈ (toSetSystem G).sets ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, hpair⟩
    rcases Set.pair_eq_pair_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm
  · intro huv
    exact ⟨u, v, huv, rfl⟩

private theorem left_inverse (G : SimpleGraph V) :
    toSimpleGraph (toSetSystem G) = G := by
  ext u v
  exact pair_mem_toSetSystem_iff G u v

private theorem right_inverse (S : TwoUniformSetSystem V) :
    toSetSystem (toSimpleGraph S) = S := by
  apply setSystem_ext
  ext s
  constructor
  · rintro ⟨u, v, huv, rfl⟩
    exact huv
  · intro hs
    obtain ⟨u, v, _, rfl⟩ := Set.ncard_eq_two.mp (S.twoUniform s hs)
    exact ⟨u, v, hs, rfl⟩

/-- The explicit equivalence underlying the representation theorem. -/
def equivalence (V : Type u) :
    SimpleGraph V ≃ TwoUniformSetSystem V where
  toFun := toSetSystem
  invFun := toSimpleGraph
  left_inv := left_inverse
  right_inv := right_inverse

/--
---
conclusion: Lax683916.SetSystemRepresentation.simpleGraphEquiv
---
Edges are sent to their two-element endpoint sets, and a 2-uniform family is
read back as an adjacency relation.

# Proof strategy

For the graph round trip, equality of two-element sets says that their
endpoints agree either directly or after swapping. For the set-system round
trip, 2-uniformity writes every member uniquely as a pair of distinct
elements.

# Attribution

Direct elementary correspondence between graph edges and two-element sets.
-/
theorem simpleGraphEquiv (V : Type u) :
    Nonempty (RepresentationEquiv V) :=
  ⟨{
    toEquiv := equivalence V
    map_pair := pair_mem_toSetSystem_iff }⟩

end Lax683916Proofs.SetSystemRepresentation
