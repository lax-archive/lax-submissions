import Lax17.Paths

/-!
---
title: Linked terminal sets
type: definition
---
Two terminal sets are linked inside a cluster when equally large subsets can
be joined by that many vertex-disjoint paths contained in the cluster.  A
terminal set is node-well-linked when every two disjoint equally large subsets
of it are linked.  The edge versions replace vertex-disjointness by
edge-disjointness.
-/

namespace Lax17.Linkedness

universe u

open Lax17.Paths

/-- `A` and `B` are node-linked by the maximum possible number of
vertex-disjoint paths contained in `C`. -/
def NodeLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) : Prop :=
  A ⊆ C ∧ B ⊆ C ∧ Disjoint A B ∧
    ∀ ⦃A' B' : Finset V⦄, A' ⊆ A → B' ⊆ B →
      ∃ P : VertexLinkage G A' B' (min A'.card B'.card),
        ∀ i : Fin (min A'.card B'.card), (P.path i).StaysIn C

/-- `X` is node-well-linked inside `C`. -/
def NodeWellLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C X : Finset V) : Prop :=
  X ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ X → B ⊆ X → Disjoint A B →
      ∃ P : VertexLinkage G A B (min A.card B.card),
        ∀ i : Fin (min A.card B.card), (P.path i).StaysIn C

/-- `A` and `B` are edge-linked by the maximum possible number of
edge-disjoint paths contained in `C`. -/
def EdgeLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) : Prop :=
  A ⊆ C ∧ B ⊆ C ∧ Disjoint A B ∧
    ∀ ⦃A' B' : Finset V⦄, A' ⊆ A → B' ⊆ B →
      ∃ P : EdgeLinkage G A' B' (min A'.card B'.card),
        ∀ i : Fin (min A'.card B'.card), (P.path i).StaysIn C

/-- `X` is edge-well-linked inside `C`. -/
def EdgeWellLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C X : Finset V) : Prop :=
  X ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ X → B ⊆ X → Disjoint A B →
      ∃ P : EdgeLinkage G A B (min A.card B.card),
        ∀ i : Fin (min A.card B.card), (P.path i).StaysIn C

/-- Cut-based edge well-linkedness with parameter `numerator / denominator`.
Every partition of the whole vertex set cuts the corresponding fraction of
the smaller terminal side. -/
def ScaledEdgeWellLinked {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V)
    (numerator denominator : ℕ) : Prop :=
  0 < numerator ∧ numerator ≤ denominator ∧
    ∀ X Y : Finset V,
      X ∪ Y = Finset.univ → Disjoint X Y →
        numerator * min (X ∩ T).card (Y ∩ T).card ≤
          denominator * (edgeBoundary G X Y).card

end Lax17.Linkedness
