import Lax17Proofs.Source.ChekuriChuzhoySection5Clustering
import Lax17Proofs.Source.EdgeMenger
import Lax17Proofs.Source.PathOfSets

namespace Lax17Proofs

universe u v w

/-!
# Router front end for Chekuri--Chuzhoy Section 5

This module records the nonalgorithmic good-router object and proves the first
branch of journal Theorem 5.11 (preprint Theorem 5.9): a candidate router
either sends the requested number of integral edge-disjoint paths to the
terminal set or finite edge-Menger returns the small cut used by `SEPARATE`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Routers


open scoped Classical

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A cut separating a candidate router from the distinguished terminals.
The two sides partition the whole host vertex set. -/
structure RouterTerminalCut
    (G : _root_.SimpleGraph V) (router terminals : Finset V) (r : ℕ) where
  routerSide : Finset V
  terminalSide : Finset V
  cover : routerSide ∪ terminalSide = Finset.univ
  disjoint : Disjoint routerSide terminalSide
  router_subset : router ⊆ routerSide
  terminals_subset : terminals ⊆ terminalSide
  boundary_lt :
    (EdgeMenger.edgeBoundary G routerSide terminalSide).card < r

/-- Repackage the edge-Menger cut in the Section 5 router terminology. -/
def RouterTerminalCut.ofCutPartition
    {router terminals : Finset V} {r : ℕ}
    (C : EdgeMenger.CutPartition G Finset.univ router terminals r) :
    RouterTerminalCut G router terminals r where
  routerSide := C.X
  terminalSide := C.Y
  cover := C.cover
  disjoint := C.disjoint
  router_subset := C.left_subset
  terminals_subset := C.right_subset
  boundary_lt := C.boundary_lt

/-- The exact integral routing-or-separating-cut dichotomy used before the two
phases of the good-router-family construction. -/
theorem hasEdgeDisjointPaths_or_routerTerminalCut
    (router terminals : Finset V) (r : ℕ)
    (hdisj : Disjoint router terminals) :
    EdgeMenger.HasEdgeDisjointPathsIn G Finset.univ router terminals r ∨
      Nonempty (RouterTerminalCut G router terminals r) := by
  classical
  by_cases hroute :
      EdgeMenger.HasEdgeDisjointPathsIn G Finset.univ router terminals r
  · exact Or.inl hroute
  · have hrouter : router ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
    have hterminals : terminals ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
    rcases EdgeMenger.edge_menger_cut G Finset.univ router terminals r
        hrouter hterminals hdisj hroute with ⟨C⟩
    exact Or.inr ⟨RouterTerminalCut.ofCutPartition C⟩

/-- Edge-disjoint paths crossing a finite partition inject into its boundary
edges. -/
theorem edgePathPacking_card_le_edgeBoundary_of_partition
    {A B X Y : Finset V} (P : EdgePathPacking G A B)
    (hcover : X ∪ Y = Finset.univ) (hXY : Disjoint X Y)
    (hAX : A ⊆ X) (hBY : B ⊆ Y) :
    P.card ≤ (EdgeMenger.edgeBoundary G X Y).card := by
  classical
  have hcross : ∀ i : P.Index,
      ∃ e ∈ (P.path i).edgeSet, e ∈ EdgeMenger.edgeBoundary G X Y := by
    intro i
    have hsub : (P.path i).vertexSet ⊆ X ∪ Y := by
      intro v _hv
      rw [hcover]
      simp
    rcases P.connects i with hconn | hconn
    · have hsourceX : (P.path i).source ∈ X := hAX hconn.1
      have htargetY : (P.path i).target ∈ Y := hBY hconn.2
      apply Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
        (P.path i) hsub hsourceX
      intro hallX
      exact Finset.disjoint_left.mp hXY (hallX (GraphPath.target_mem_vertexSet _))
        htargetY
    · have htargetX : (P.path i).target ∈ X := hAX hconn.2
      have hsourceY : (P.path i).source ∈ Y := hBY hconn.1
      apply Section44.GraphPath.exists_edgeBoundary_of_target_mem_left_of_not_subset_left
        (P.path i) hsub htargetX
      intro hallX
      exact Finset.disjoint_left.mp hXY (hallX (GraphPath.source_mem_vertexSet _))
        hsourceY
  let charge : P.Index →
      {e : Sym2 V // e ∈ EdgeMenger.edgeBoundary G X Y} := fun i =>
    ⟨Classical.choose (hcross i), (Classical.choose_spec (hcross i)).2⟩
  have hcharge_mem : ∀ i, (charge i).1 ∈ (P.path i).edgeSet := fun i =>
    (Classical.choose_spec (hcross i)).1
  have hcharge_inj : Function.Injective charge := by
    intro i j hij
    by_contra hne
    have hedge : (charge i).1 = (charge j).1 := congrArg Subtype.val hij
    have hjmem : (charge i).1 ∈ (P.path j).edgeSet := by
      simpa [hedge] using hcharge_mem j
    exact Finset.disjoint_left.mp (P.edge_disjoint hne) (hcharge_mem i) hjmem
  have hcard := Fintype.card_le_of_injective charge hcharge_inj
  simpa [EdgePathPacking.card] using hcard

/-- The integral path certificate in a good router.  This is the semantic
finite content of "send `r` flow units to the terminals with no edge
congestion" in Section 5. -/
def RoutesToTerminals
    (G : _root_.SimpleGraph V) (router terminals : Finset V) (r : ℕ) : Prop :=
  EdgeMenger.HasEdgeDisjointPathsIn G Finset.univ router terminals r

/-- A good router with the exact properties used by the Section 5 assembly.
Bandwidth is truncated at `bandwidthCap`, matching the paper's acceptable
clustering invariant. -/
structure GoodRouter
    (G : _root_.SimpleGraph V) (terminals router : Finset V)
    (w0 bandwidthCap alphaNum alphaDen routeValue : ℕ) : Prop where
  terminal_disjoint : Disjoint router terminals
  connected : IsCluster G router
  large :
    ChekuriChuzhoySection5Clustering.IsLargeCluster G w0 router
  bandwidth :
    ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
      G router bandwidthCap alphaNum alphaDen
  routes : RoutesToTerminals G router terminals routeValue

namespace GoodRouter

variable {terminals router : Finset V}
variable {w0 bandwidthCap alphaNum alphaDen routeValue : ℕ}

/-- The small-cut alternative is incompatible with the integral routing field
of a good router. -/
theorem not_routerTerminalCut
    (R : GoodRouter G terminals router
      w0 bandwidthCap alphaNum alphaDen routeValue) :
    ¬ Nonempty (RouterTerminalCut G router terminals routeValue) := by
  rintro ⟨C⟩
  rcases R.routes with ⟨P, hroute, _hstay⟩
  have hbound := edgePathPacking_card_le_edgeBoundary_of_partition P
    C.cover C.disjoint C.router_subset C.terminals_subset
  have hcut := C.boundary_lt
  omega

end GoodRouter

/-- A finite family of pairwise vertex-disjoint good routers. -/
structure GoodRouterFamily
    (G : _root_.SimpleGraph V) (terminals : Finset V) (count : ℕ)
    (w0 bandwidthCap alphaNum alphaDen routeValue : ℕ) where
  router : Fin count → Finset V
  good : ∀ i, GoodRouter G terminals (router i)
    w0 bandwidthCap alphaNum alphaDen routeValue
  pairwise_disjoint : Pairwise fun i j => Disjoint (router i) (router j)

end ChekuriChuzhoySection5Routers
end SimpleGraph

end Lax17Proofs
