import Lax17Proofs.Source.Section46
import Lax17Proofs.Source.TreeOfSets

namespace Lax17Proofs

universe u v w

/-!
# Bandwidth certificates for tree-of-sets systems

Chekuri--Chuzhoy Theorem 4.3 (Theorem 4.1 in the preprint) first constructs
an ordinary tree-of-sets system.  Its additional invariant is that the
boundary of every cluster is cut-well-linked.  Lemma 4.5 uses that invariant
to retain coherent node-well-linked interfaces and obtain a strong system.

`BandwidthTreeOfSetsSystem` records exactly the part of that intermediate
output consumed by strongification.  The certified reserve may contain more
vertices than the connector endpoints, matching the source's full cluster
interface `Gamma_G(S)`.
-/

namespace SimpleGraph


/-- An ordinary tree-of-sets system together with a scaled cut-well-linked
reserve in every cluster that contains all incident connector interfaces. -/
structure BandwidthTreeOfSetsSystem {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (m w alphaNum alphaDen : ℕ)
    extends TreeOfSetsSystem G m w where
  /-- The cluster boundary reserve used by the strongification argument. -/
  boundaryReserve : Fin m → Finset V
  /-- Every boundary reserve lies in its cluster. -/
  boundaryReserve_subset_cluster :
    ∀ i : Fin m, boundaryReserve i ⊆ cluster i
  /-- Every connector interface is contained in the corresponding reserve. -/
  interface_subset_boundaryReserve :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      interface i j hij ⊆ boundaryReserve i
  /-- The reserve has the bandwidth promised by Theorem 4.3. -/
  boundaryReserve_scaledEdgeWellLinked :
    ∀ i : Fin m,
      Section46.ScaledEdgeWellLinkedIn
        G (cluster i) (boundaryReserve i) alphaNum alphaDen

namespace BandwidthTreeOfSetsSystem

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {m w alphaNum alphaDen : ℕ}

/-- Each individual incident interface inherits the cluster bandwidth. -/
theorem interface_scaledEdgeWellLinked
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    Section46.ScaledEdgeWellLinkedIn
      G (T.cluster i) (T.interface i j hij) alphaNum alphaDen := by
  exact Section46.ScaledEdgeWellLinkedIn.mono_terminals
    (T.boundaryReserve_scaledEdgeWellLinked i)
    (T.interface_subset_boundaryReserve i j hij)

/-- The union of two incident interfaces inherits the cluster bandwidth. -/
theorem interface_union_scaledEdgeWellLinked
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    {i j k : Fin m} (hij : T.metaTree.Adj i j)
    (hik : T.metaTree.Adj i k) :
    Section46.ScaledEdgeWellLinkedIn G (T.cluster i)
      (T.interface i j hij ∪ T.interface i k hik) alphaNum alphaDen := by
  apply Section46.ScaledEdgeWellLinkedIn.mono_terminals
    (T.boundaryReserve_scaledEdgeWellLinked i)
  exact Finset.union_subset
    (T.interface_subset_boundaryReserve i j hij)
    (T.interface_subset_boundaryReserve i k hik)

/-- The union of three incident interfaces inherits the cluster bandwidth. -/
theorem interface_triple_union_scaledEdgeWellLinked
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    {i j k l : Fin m} (hij : T.metaTree.Adj i j)
    (hik : T.metaTree.Adj i k) (hil : T.metaTree.Adj i l) :
    Section46.ScaledEdgeWellLinkedIn G (T.cluster i)
      (T.interface i j hij ∪ T.interface i k hik ∪ T.interface i l hil)
      alphaNum alphaDen := by
  apply Section46.ScaledEdgeWellLinkedIn.mono_terminals
    (T.boundaryReserve_scaledEdgeWellLinked i)
  exact Finset.union_subset
    (Finset.union_subset
      (T.interface_subset_boundaryReserve i j hij)
      (T.interface_subset_boundaryReserve i k hik))
    (T.interface_subset_boundaryReserve i l hil)

end BandwidthTreeOfSetsSystem

end SimpleGraph

end Lax17Proofs
