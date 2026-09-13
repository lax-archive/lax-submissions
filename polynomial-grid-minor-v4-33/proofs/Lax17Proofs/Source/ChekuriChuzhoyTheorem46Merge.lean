import Lax17Proofs.Source.ChekuriChuzhoyLemma219
import Lax17Proofs.Source.EndpointCleanPackingOps
import Lax17Proofs.Source.PathOfSetsJoin
import Lax17Proofs.Source.PathPackingFirstHit
import Lax17Proofs.Source.ChekuriChuzhoyTheorem47
import Lax17Proofs.Source.ChekuriChuzhoyPendantTransport

namespace Lax17Proofs

universe u v w

/-!
# The two-child merge in Chekuri--Chuzhoy Theorem 4.6

This file packages the two applications of Lemma 2.19 used at a branching
cluster in Step 2 of the many-leaves proof.  The records expose the retained
large-family paths and the rerouted small family separately; this is exactly
the reserve accounting used by the DFS induction.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical
open ChekuriChuzhoyRootedTreeComponents

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {U₁ U₂ T : Finset V}

section LeafReserves

variable {m W ell : ℕ}
variable {Tsys : StrongTreeOfSetsSystem G m W}

/-- Two disjoint half-size terminal reserves inside every selected leaf target
of the global Theorem 4.7 routing. -/
structure Theorem47LeafReserveData
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {A : Finset V}
    (R : Theorem47SubtreeRoutingData S S.root A (W / ell)) where
  left : Fin m → Finset V
  right : Fin m → Finset V
  left_empty : ∀ x, x ∉ S.leaves → left x = ∅
  right_empty : ∀ x, x ∉ S.leaves → right x = ∅
  left_subset : ∀ x, x ∈ S.leaves → left x ⊆ R.leafTarget x
  right_subset : ∀ x, x ∈ S.leaves → right x ⊆ R.leafTarget x
  disjoint : ∀ x, Disjoint (left x) (right x)
  left_card : ∀ x, x ∈ S.leaves → (left x).card = W / (2 * ell)
  right_card : ∀ x, x ∈ S.leaves → (right x).card = W / (2 * ell)

private theorem two_mul_halfQuota_le_quota
    (W ell : ℕ) :
    2 * (W / (2 * ell)) ≤ W / ell := by
  by_cases hell : ell = 0
  · simp [hell]
  have hrewrite : W / (2 * ell) = (W / ell) / 2 := by
    calc
      W / (2 * ell) = W / (ell * 2) := by rw [Nat.mul_comm 2 ell]
      _ = (W / ell) / 2 := (Nat.div_div_eq_div_mul W ell 2).symm
  rw [hrewrite]
  exact Nat.mul_div_le (W / ell) 2

/-- Split one finite leaf target into two disjoint half-quota reserves. -/
theorem exists_two_leaf_reserves
    (Q : Finset V) {W ell : ℕ}
    (hQ : Q.card = W / ell) :
    ∃ L R : Finset V,
      L ⊆ Q ∧ R ⊆ Q ∧ Disjoint L R ∧
        L.card = W / (2 * ell) ∧ R.card = W / (2 * ell) := by
  classical
  let h := W / (2 * ell)
  have h2 : 2 * h ≤ Q.card := by
    simpa [h, hQ] using two_mul_halfQuota_le_quota W ell
  have hhQ : h ≤ Q.card := by omega
  rcases Finset.exists_subset_card_eq hhQ with ⟨L, hLQ, hLcard⟩
  have hRle : h ≤ (Q \ L).card := by
    rw [Finset.card_sdiff_of_subset hLQ, hLcard]
    omega
  rcases Finset.exists_subset_card_eq hRle with ⟨R, hRdiff, hRcard⟩
  refine ⟨L, R, hLQ, ?_, ?_, hLcard, hRcard⟩
  · exact hRdiff.trans Finset.sdiff_subset
  · exact Finset.disjoint_left.mpr (by
      intro x hxL hxR
      exact (Finset.mem_sdiff.mp (hRdiff hxR)).2 hxL)

/-- The global Theorem 4.7 routing supplies coherent left/right reserves at
all selected leaves. -/
theorem exists_theorem47LeafReserveData
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {A : Finset V}
    (R : Theorem47SubtreeRoutingData S S.root A (W / ell)) :
    Nonempty (Theorem47LeafReserveData S R) := by
  classical
  have hroot : S.selectedBelow S.root = S.leaves :=
    S.selectedBelow_root_eq_leaves
  let split : ∀ x : Fin m, x ∈ S.leaves →
      Finset V × Finset V :=
    fun x hx =>
      let hcard : (R.leafTarget x).card = W / ell :=
        R.leafTarget_card x (by simpa [hroot] using hx)
      let E := exists_two_leaf_reserves (R.leafTarget x) hcard
      (Classical.choose E, Classical.choose (Classical.choose_spec E))
  let left : Fin m → Finset V :=
    fun x => if hx : x ∈ S.leaves then (split x hx).1 else ∅
  let right : Fin m → Finset V :=
    fun x => if hx : x ∈ S.leaves then (split x hx).2 else ∅
  refine ⟨{
    left := left
    right := right
    left_empty := by
      intro x hx
      simp [left, hx]
    right_empty := by
      intro x hx
      simp [right, hx]
    left_subset := by
      intro x hx
      have hs := Classical.choose_spec
        (Classical.choose_spec
          (exists_two_leaf_reserves (R.leafTarget x)
            (R.leafTarget_card x (by simpa [hroot] using hx))))
      simpa [left, split, hx] using hs.1
    right_subset := by
      intro x hx
      have hs := Classical.choose_spec
        (Classical.choose_spec
          (exists_two_leaf_reserves (R.leafTarget x)
            (R.leafTarget_card x (by simpa [hroot] using hx))))
      simpa [right, split, hx] using hs.2.1
    disjoint := by
      intro x
      by_cases hx : x ∈ S.leaves
      · have hs := Classical.choose_spec
          (Classical.choose_spec
            (exists_two_leaf_reserves (R.leafTarget x)
              (R.leafTarget_card x (by simpa [hroot] using hx))))
        simpa [left, right, split, hx] using hs.2.2.1
      · simp [left, right, hx]
    left_card := by
      intro x hx
      have hs := Classical.choose_spec
        (Classical.choose_spec
          (exists_two_leaf_reserves (R.leafTarget x)
            (R.leafTarget_card x (by simpa [hroot] using hx))))
      simpa [left, split, hx] using hs.2.2.2.1
    right_card := by
      intro x hx
      have hs := Classical.choose_spec
        (Classical.choose_spec
          (exists_two_leaf_reserves (R.leafTarget x)
            (R.leafTarget_card x (by simpa [hroot] using hx))))
      simpa [right, split, hx] using hs.2.2.2.2 }⟩

/-- Restrict the global subtree routing to a chosen subset of one leaf's
targets. -/
noncomputable def Theorem47SubtreeRoutingData.restrictLeafTarget
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v : Fin m} {A : Finset V} {q : ℕ}
    (E : Theorem47SubtreeRoutingData S v A q)
    {x : Fin m} (hx : x ∈ S.selectedBelow v)
    (Q : Finset V) (hQ : Q ⊆ E.leafTarget x) :
    PerfectPathPacking G
      (E.packing.sourceSet
        (E.packing.targetIndexSetOfSubset Q))
      Q :=
  E.packing.restrictTargetSet Q (by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨x, hx, hQ hz⟩)

/-- The chosen leaf reserve, directed upward and truncated at its first
encounter with the current cluster.  This is the formal `v_Q` construction in
Step 2. -/
theorem Theorem47SubtreeRoutingData.exists_reserveFirstHit
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v : Fin m} {A : Finset V} {q : ℕ}
    (E : Theorem47SubtreeRoutingData S v A q)
    (hAcluster : A ⊆ Tsys.cluster v)
    {x : Fin m} (hx : x ∈ S.selectedBelow v)
    (Q : Finset V) (hQ : Q ⊆ E.leafTarget x) :
    Nonempty
      ((E.restrictLeafTarget S hx Q hQ).reverse.FirstHitData
        (Tsys.cluster v)) := by
  let P := E.restrictLeafTarget S hx Q hQ
  have htarget :
      E.packing.sourceSet (E.packing.targetIndexSetOfSubset Q) ⊆
        Tsys.cluster v := by
    intro z hz
    exact hAcluster (E.packing.sourceSet_subset_left _ hz)
  exact (P.reverse).exists_firstHitData htarget

/-- Singleton-system data with the chosen nails exposed for the DFS
invariant. -/
structure LeafSingletonStrongPathData
    (C L R : Finset V) (w : ℕ) where
  leftNails : Finset V
  rightNails : Finset V
  left_subset : leftNails ⊆ L
  right_subset : rightNails ⊆ R
  system : StrongPathOfSetsSystem G 1 w
  cluster_eq : system.cluster system.toPathOfSetsSystem.firstIndex = C
  left_eq : system.left system.toPathOfSetsSystem.firstIndex = leftNails
  right_eq : system.right system.toPathOfSetsSystem.lastIndex = rightNails

/-- A selected leaf with two disjoint reserves containing `w` terminals gives
the singleton strong path-of-sets system used at the DFS base case. -/
theorem Theorem47SubtreeRoutingData.exists_leafSingletonStrongPathData
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v : Fin m} {A : Finset V} {q w : ℕ}
    (E : Theorem47SubtreeRoutingData S v A q)
    {x : Fin m} (hx : x ∈ S.selectedBelow v)
    (L R : Finset V)
    (hL : L ⊆ E.leafTarget x)
    (hR : R ⊆ E.leafTarget x)
    (hLR : Disjoint L R)
    (hw : 0 < w)
    (hwL : w ≤ L.card)
    (hwR : w ≤ R.card) :
    Nonempty (LeafSingletonStrongPathData (G := G)
      (Tsys.cluster x) L R w) := by
  classical
  rcases Finset.exists_subset_card_eq hwL with ⟨L', hL'L, hL'card⟩
  rcases Finset.exists_subset_card_eq hwR with ⟨R', hR'R, hR'card⟩
  have hL'target : L' ⊆ E.leafTarget x := hL'L.trans hL
  have hR'target : R' ⊆ E.leafTarget x := hR'R.trans hR
  have hdisj : Disjoint L' R' :=
    hLR.mono hL'L hR'R
  have hNW :=
    E.leafTarget_nodeWellLinked x hx
  let P : StrongPathOfSetsSystem G 1 w := {
    length_pos := by omega
    width_pos := hw
    cluster := fun _ => Tsys.cluster x
    cluster_connected := fun _ => Tsys.cluster_connected x
    cluster_disjoint := by
      intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))
    left := fun _ => L'
    right := fun _ => R'
    left_subset_cluster := fun _ =>
      hL'target.trans (E.leafTarget_subset x hx)
    right_subset_cluster := fun _ =>
      hR'target.trans (E.leafTarget_subset x hx)
    left_right_disjoint := fun _ => hdisj
    left_card := fun _ => hL'card
    right_card := fun _ => hR'card
    connector := by
      intro i hi
      exact False.elim (by omega)
    connector_card := by
      intro i hi
      exact False.elim (by omega)
    connector_internally_disjoint_clusters := by
      intro i hi
      exact False.elim (by omega)
    connector_mutually_nodeDisjoint := by
      intro i j hi
      exact False.elim (by omega)
    left_nodeWellLinked := fun _ =>
      NodeWellLinkedIn.mono_terminals hNW hL'target
    right_nodeWellLinked := fun _ =>
      NodeWellLinkedIn.mono_terminals hNW hR'target
    left_right_nodeLinked := fun _ =>
      NodeWellLinkedIn.nodeLinkedIn_between_disjoint_subsets
        hNW hL'target hR'target hdisj }
  exact ⟨{
    leftNails := L'
    rightNails := R'
    left_subset := hL'L
    right_subset := hR'R
    system := P
    cluster_eq := rfl
    left_eq := rfl
    right_eq := rfl }⟩

end LeafReserves

section DfsInvariant

variable {m W ell w q : ℕ}
variable {Tsys : StrongTreeOfSetsSystem G m W}

/-- The bottom-up invariant from Step 2 of Theorem 4.6.

The system contains precisely the selected leaves below `v`.  Its two outer
reserves are still unused paths of the current Theorem 4.7 routing, and those
paths are node-disjoint from every connector already installed in the system.
The cardinality inequality is the division-free form of the paper's
`W/(2*ell) - 8*height*w` reserve bound; descendant count is a sufficient upper
bound on the number of branching losses. -/
structure Theorem46DfsState
    (S : Theorem46LeafExtractionSetup Tsys ell)
    (v : Fin m) (A : Finset V)
    (E : Theorem47SubtreeRoutingData S v A q) where
  active : (S.selectedBelow v).Nonempty
  system :
    StrongPathOfSetsSystem G (S.selectedBelow v).card w
  leafOrder :
    Fin (S.selectedBelow v).card → {x : Fin m // x ∈ S.selectedBelow v}
  leafOrder_bijective : Function.Bijective leafOrder
  cluster_eq :
    ∀ i, system.cluster i = Tsys.cluster (leafOrder i).1
  leftReserve : Finset V
  rightReserve : Finset V
  leftReserve_subset :
    leftReserve ⊆
      E.leafTarget
        (leafOrder system.toPathOfSetsSystem.firstIndex).1
  rightReserve_subset :
    rightReserve ⊆
      E.leafTarget
        (leafOrder system.toPathOfSetsSystem.lastIndex).1
  left_nails_subset :
    system.left system.toPathOfSetsSystem.firstIndex ⊆ leftReserve
  right_nails_subset :
    system.right system.toPathOfSetsSystem.lastIndex ⊆ rightReserve
  left_reserve_count :
    W / (2 * ell) ≤
      leftReserve.card +
        8 * ((S.selectedBelow v).card - 1) * w
  right_reserve_count :
    W / (2 * ell) ≤
      rightReserve.card +
        8 * ((S.selectedBelow v).card - 1) * w
  connectors_stayIn :
    ∀ i hi,
      (system.connector i hi).toPathPacking.StaysIn (S.subtreeRegion v)
  leftReserve_disjoint_connectors :
    ∀ (i : Fin (S.selectedBelow v).card)
      (hi : i.1 + 1 < (S.selectedBelow v).card),
      PathPacking.MutuallyNodeDisjoint
        ((E.restrictLeafTarget S
        (leafOrder system.toPathOfSetsSystem.firstIndex).2
        leftReserve leftReserve_subset).reverse.toPathPacking)
        (system.connector i hi).toPathPacking
  rightReserve_disjoint_connectors :
    ∀ (i : Fin (S.selectedBelow v).card)
      (hi : i.1 + 1 < (S.selectedBelow v).card),
      PathPacking.MutuallyNodeDisjoint
        ((E.restrictLeafTarget S
        (leafOrder system.toPathOfSetsSystem.lastIndex).2
        rightReserve rightReserve_subset).reverse.toPathPacking)
        (system.connector i hi).toPathPacking

/-- The DFS invariant at a selected leaf.  No connector has yet been
installed, so both global-routing reserves are completely available. -/
theorem exists_theorem46DfsState_leaf
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v : Fin m} {A : Finset V}
    (E : Theorem47SubtreeRoutingData S v A q)
    (hv : v ∈ S.leaves)
    (L R : Finset V)
    (hL : L ⊆ E.leafTarget v)
    (hR : R ⊆ E.leafTarget v)
    (hLR : Disjoint L R)
    (hLcard : L.card = W / (2 * ell))
    (hRcard : R.card = W / (2 * ell))
    (hw : 0 < w)
    (hwHalf : w ≤ W / (2 * ell)) :
    Nonempty (Theorem46DfsState (w := w) S v A E) := by
  classical
  have hbelow : S.selectedBelow v = {v} :=
    S.selectedBelow_eq_singleton_of_mem_leaves hv
  have hvbelow : v ∈ S.selectedBelow v := by simp [hbelow]
  let O := (S.selectedBelow v).equivFin.symm
  have hOeq : ∀ i, (O i).1 = v := by
    intro i
    have : (O i).1 ∈ ({v} : Finset (Fin m)) := by
      simpa [hbelow] using (O i).2
    simpa using this
  rcases E.exists_leafSingletonStrongPathData S hvbelow L R hL hR hLR
      hw (by simpa [hLcard] using hwHalf)
      (by simpa [hRcard] using hwHalf) with
    ⟨D⟩
  have hcard : (S.selectedBelow v).card = 1 := by simp [hbelow]
  let P : StrongPathOfSetsSystem G (S.selectedBelow v).card w := {
    length_pos := by omega
    width_pos := hw
    cluster := fun _ => Tsys.cluster v
    cluster_connected := fun _ => Tsys.cluster_connected v
    cluster_disjoint := by
      intro i j hij
      exact False.elim (hij (by
        apply Fin.ext
        have hi := i.2
        have hj := j.2
        omega))
    left := fun _ => D.leftNails
    right := fun _ => D.rightNails
    left_subset_cluster := fun _ =>
      D.left_subset.trans hL |>.trans (E.leafTarget_subset v hvbelow)
    right_subset_cluster := fun _ =>
      D.right_subset.trans hR |>.trans (E.leafTarget_subset v hvbelow)
    left_right_disjoint := fun _ =>
      hLR.mono D.left_subset D.right_subset
    left_card := fun _ => by
      simpa [D.left_eq] using D.system.left_card
        D.system.toPathOfSetsSystem.firstIndex
    right_card := fun _ => by
      simpa [D.right_eq] using D.system.right_card
        D.system.toPathOfSetsSystem.lastIndex
    connector := by
      intro i hi
      exact False.elim (by omega)
    connector_card := by
      intro i hi
      exact False.elim (by omega)
    connector_internally_disjoint_clusters := by
      intro i hi
      exact False.elim (by omega)
    connector_mutually_nodeDisjoint := by
      intro i j hi
      exact False.elim (by omega)
    left_nodeWellLinked := fun _ =>
      NodeWellLinkedIn.mono_terminals
        (E.leafTarget_nodeWellLinked v hvbelow)
        (D.left_subset.trans hL)
    right_nodeWellLinked := fun _ =>
      NodeWellLinkedIn.mono_terminals
        (E.leafTarget_nodeWellLinked v hvbelow)
        (D.right_subset.trans hR)
    left_right_nodeLinked := fun _ =>
      NodeWellLinkedIn.nodeLinkedIn_between_disjoint_subsets
        (E.leafTarget_nodeWellLinked v hvbelow)
        (D.left_subset.trans hL) (D.right_subset.trans hR)
        (hLR.mono D.left_subset D.right_subset) }
  exact ⟨{
    active := ⟨v, hvbelow⟩
    system := P
    leafOrder := O
    leafOrder_bijective := O.bijective
    cluster_eq := by
      intro i
      simp [P, hOeq i]
    leftReserve := L
    rightReserve := R
    leftReserve_subset := by
      simpa [hOeq] using hL
    rightReserve_subset := by
      simpa [hOeq] using hR
    left_nails_subset := by
      simpa [P] using D.left_subset
    right_nails_subset := by
      simpa [P] using D.right_subset
    left_reserve_count := by simpa [hLcard, hcard]
    right_reserve_count := by simpa [hRcard, hcard]
    connectors_stayIn := by
      intro i hi
      simp [hcard] at hi
    leftReserve_disjoint_connectors := by
      intro i hi
      simp [hcard] at hi
    rightReserve_disjoint_connectors := by
      intro i hi
      simp [hcard] at hi }⟩

end DfsInvariant

section RoutedDfsInvariant

variable {m W ell w : ℕ}
variable {Tsys : StrongTreeOfSetsSystem G m W}

/-- Bottom-up Step 2 state with the two surviving Step 1 route families
exposed.  Their targets lie in the input set at the current rooted cluster;
this is the formulation that is stable under one-child extension and is
consumed directly by the two-child rerouting argument. -/
structure Theorem46RoutedDfsState
    (S : Theorem46LeafExtractionSetup Tsys ell)
    (v : Fin m) (A : Finset V) where
  active : (S.selectedBelow v).Nonempty
  system : StrongPathOfSetsSystem G (S.selectedBelow v).card w
  leafOrder :
    Fin (S.selectedBelow v).card → {x : Fin m // x ∈ S.selectedBelow v}
  leafOrder_bijective : Function.Bijective leafOrder
  cluster_eq :
    ∀ i, system.cluster i = Tsys.cluster (leafOrder i).1
  leftReserve : Finset V
  rightReserve : Finset V
  leftAmbient : Finset V
  rightAmbient : Finset V
  leftAnchor : Finset V
  rightAnchor : Finset V
  leftRoute : PerfectPathPacking G leftReserve leftAnchor
  rightRoute : PerfectPathPacking G rightReserve rightAnchor
  leftAnchor_subset : leftAnchor ⊆ A
  rightAnchor_subset : rightAnchor ⊆ A
  leftAmbient_subset_leaf :
    leftAmbient ⊆ Tsys.cluster
      (leafOrder system.toPathOfSetsSystem.firstIndex).1
  rightAmbient_subset_leaf :
    rightAmbient ⊆ Tsys.cluster
      (leafOrder system.toPathOfSetsSystem.lastIndex).1
  leftAmbient_nodeWellLinked :
    NodeWellLinkedIn G
      (Tsys.cluster
        (leafOrder system.toPathOfSetsSystem.firstIndex).1) leftAmbient
  rightAmbient_nodeWellLinked :
    NodeWellLinkedIn G
      (Tsys.cluster
        (leafOrder system.toPathOfSetsSystem.lastIndex).1) rightAmbient
  outerAmbient_eq_of_singleton :
    system.toPathOfSetsSystem.firstIndex =
        system.toPathOfSetsSystem.lastIndex →
      leftAmbient = rightAmbient
  outerAmbient_linked_of_singleton :
    system.toPathOfSetsSystem.firstIndex =
        system.toPathOfSetsSystem.lastIndex →
      ∀ {L R : Finset V},
        L ⊆ leftAmbient → R ⊆ rightAmbient → Disjoint L R →
          NodeLinkedIn G
            (Tsys.cluster
              (leafOrder system.toPathOfSetsSystem.firstIndex).1) L R
  leftReserve_subset_ambient : leftReserve ⊆ leftAmbient
  rightReserve_subset_ambient : rightReserve ⊆ rightAmbient
  leftReserve_disjoint_firstRight :
    Disjoint leftReserve
      (system.right system.toPathOfSetsSystem.firstIndex)
  rightReserve_disjoint_lastLeft :
    Disjoint
      (system.left system.toPathOfSetsSystem.lastIndex) rightReserve
  first_left_subset_ambient :
    system.left system.toPathOfSetsSystem.firstIndex ⊆ leftAmbient
  first_right_subset_ambient :
    system.right system.toPathOfSetsSystem.firstIndex ⊆ leftAmbient
  last_left_subset_ambient :
    system.left system.toPathOfSetsSystem.lastIndex ⊆ rightAmbient
  last_right_subset_ambient :
    system.right system.toPathOfSetsSystem.lastIndex ⊆ rightAmbient
  leftReserve_subset_leaf :
    leftReserve ⊆ Tsys.cluster
      (leafOrder system.toPathOfSetsSystem.firstIndex).1
  rightReserve_subset_leaf :
    rightReserve ⊆ Tsys.cluster
      (leafOrder system.toPathOfSetsSystem.lastIndex).1
  left_nails_subset :
    system.left system.toPathOfSetsSystem.firstIndex ⊆ leftReserve
  right_nails_subset :
    system.right system.toPathOfSetsSystem.lastIndex ⊆ rightReserve
  left_reserve_count :
    W / (2 * ell) ≤ leftReserve.card +
      8 * ((S.selectedBelow v).card - 1) * w
  right_reserve_count :
    W / (2 * ell) ≤ rightReserve.card +
      8 * ((S.selectedBelow v).card - 1) * w
  leftRoute_staysIn :
    leftRoute.toPathPacking.StaysIn (S.subtreeRegion v)
  rightRoute_staysIn :
    rightRoute.toPathPacking.StaysIn (S.subtreeRegion v)
  leftRoute_internallyDisjoint_leafCluster :
    ∀ x, x ∈ S.selectedBelow v →
      leftRoute.toPathPacking.InternallyDisjointFromSet (Tsys.cluster x)
  rightRoute_internallyDisjoint_leafCluster :
    ∀ x, x ∈ S.selectedBelow v →
      rightRoute.toPathPacking.InternallyDisjointFromSet (Tsys.cluster x)
  leftRoute_trivial_of_root_selected :
    v ∈ S.leaves →
      ∀ i : leftRoute.Index,
        (leftRoute.path i).source = (leftRoute.path i).target
  rightRoute_trivial_of_root_selected :
    v ∈ S.leaves →
      ∀ i : rightRoute.Index,
        (rightRoute.path i).source = (rightRoute.path i).target
  outerRoutes_disjoint :
    leftRoute.toPathPacking.MutuallyNodeDisjoint rightRoute.toPathPacking
  connectors_stayIn :
    ∀ (i : Fin (S.selectedBelow v).card)
      (hi : i.1 + 1 < (S.selectedBelow v).card),
      (system.connector i hi).toPathPacking.StaysIn (S.subtreeRegion v)
  leftRoute_disjoint_connectors :
    ∀ (i : Fin (S.selectedBelow v).card)
      (hi : i.1 + 1 < (S.selectedBelow v).card),
      leftRoute.toPathPacking.MutuallyNodeDisjoint
        (system.connector i hi).toPathPacking
  rightRoute_disjoint_connectors :
    ∀ (i : Fin (S.selectedBelow v).card)
      (hi : i.1 + 1 < (S.selectedBelow v).card),
      rightRoute.toPathPacking.MutuallyNodeDisjoint
        (system.connector i hi).toPathPacking

/-- Extend a leaf-to-current route backwards through a parent-to-current
transition.  The resulting anchor is the set of parent-side sources matched
to the prescribed current anchors. -/
structure RouteExtensionData
    {X U A B C : Finset V}
    (P : PerfectPathPacking G X U)
    (Q : PerfectPathPacking G A B)
    (hU : U ⊆ B)
    (hPstay : P.toPathPacking.StaysIn C)
    (hQinternal : Q.toPathPacking.InternallyDisjointFromSet C)
    (hAdisj : Disjoint A C) where
  anchor : Finset V
  anchor_subset : anchor ⊆ A
  route : PerfectPathPacking G X anchor
  route_staysIn :
    route.toPathPacking.StaysIn
      (C ∪ Q.toPathPacking.vertexSet)
  route_path_subset :
    ∀ i : route.Index,
      ∃ p : P.Index, ∃ q : Q.Index,
        (Q.path q).target ∈ U ∧
        (route.path i).vertexSet ⊆
          (P.path p).vertexSet ∪ (Q.path q).vertexSet
  route_internallyDisjoint :
    ∀ {K : Finset V},
      P.toPathPacking.InternallyDisjointFromSet K →
      Q.toPathPacking.InternallyDisjointFromSet K →
      Disjoint U K →
      route.toPathPacking.InternallyDisjointFromSet K
  route_internallyDisjoint_of_trivial_glue :
    ∀ {K : Finset V},
      P.toPathPacking.InternallyDisjointFromSet K →
      Q.toPathPacking.InternallyDisjointFromSet K →
      (∀ i : P.Index,
        (P.path i).target ∈ K →
          (P.path i).source = (P.path i).target) →
      route.toPathPacking.InternallyDisjointFromSet K

/-- Source-faithful construction of a route extension. -/
theorem exists_routeExtensionData
    {X U A B C : Finset V}
    (P : PerfectPathPacking G X U)
    (Q : PerfectPathPacking G A B)
    (hU : U ⊆ B)
    (hPstay : P.toPathPacking.StaysIn C)
    (hQinternal : Q.toPathPacking.InternallyDisjointFromSet C)
    (hAdisj : Disjoint A C) :
    Nonempty (RouteExtensionData P Q hU hPstay hQinternal hAdisj) := by
  classical
  let QR := Q.restrictTargetSet U hU
  let anchor := Q.sourceSet (Q.targetIndexSetOfSubset U)
  have hQRinternal :
      QR.reverse.toPathPacking.InternallyDisjointFromSet C :=
    PerfectPathPacking.reverse_internallyDisjointFromSet QR
      (Q.restrictTargetSet_internallyDisjointFromSet U hU hQinternal)
  have hAnchorDisj : Disjoint anchor C :=
    Finset.disjoint_of_subset_left (Q.sourceSet_subset_left _) hAdisj
  let R :=
    P.concatOfFirstStaysInSecondInternallyDisjoint
      QR.reverse hPstay hQRinternal hAnchorDisj
  exact ⟨{
    anchor := anchor
    anchor_subset := Q.sourceSet_subset_left _
    route := R
    route_staysIn := by
      have hQRstay :
          QR.reverse.toPathPacking.StaysIn Q.toPathPacking.vertexSet :=
        PerfectPathPacking.reverse_staysIn QR
          (Q.restrictTargetSet_staysIn_vertexSet U hU)
      exact
        P.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
          QR.reverse hPstay hQRinternal hAnchorDisj hQRstay
    route_path_subset := by
      intro i
      refine ⟨i, (P.indexOfSourceTarget QR.reverse i).1,
        (Q.mem_targetIndexSetOfSubset U
          (P.indexOfSourceTarget QR.reverse i).1).1
            (P.indexOfSourceTarget QR.reverse i).2, ?_⟩
      simpa [R, QR] using
        P.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          QR.reverse hPstay hQRinternal hAnchorDisj i
    route_internallyDisjoint := by
      intro K hPK hQK hUK
      have hQRK :
          QR.reverse.toPathPacking.InternallyDisjointFromSet K :=
        PerfectPathPacking.reverse_internallyDisjointFromSet QR
          (Q.restrictTargetSet_internallyDisjointFromSet U hU hQK)
      exact
        P.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
          QR.reverse hPstay hQRinternal hAnchorDisj
          hPK hQRK hUK
    route_internallyDisjoint_of_trivial_glue := by
      intro K hPK hQK htrivial
      have hQRK :
          QR.reverse.toPathPacking.InternallyDisjointFromSet K :=
        PerfectPathPacking.reverse_internallyDisjointFromSet QR
          (Q.restrictTargetSet_internallyDisjointFromSet U hU hQK)
      intro i z hz hzK
      have hsplit :=
        P.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          QR.reverse hPstay hQRinternal hAnchorDisj i hz
      let j := P.indexOfSourceTarget QR.reverse i
      have hmatch :
          (QR.reverse.path j).source = (P.path i).target :=
        P.source_indexOfSourceTarget QR.reverse i
      rcases Finset.mem_union.mp hsplit with hzP | hzQ
      · rcases hPK i hzP hzK with hsource | htarget
        · exact Or.inl (by simpa [R] using hsource)
        · have htriv := htrivial i (by simpa [htarget] using hzK)
          exact Or.inl (by simpa [R, htarget] using htriv.symm)
      · rcases hQRK j hzQ hzK with hsource | htarget
        · have htriv := htrivial i (by
            simpa [hsource, hmatch] using hzK)
          exact Or.inl (by simpa [R, hsource, hmatch] using htriv.symm)
        · exact Or.inr (by simpa [R, j] using htarget) }⟩

/-- Extending a route preserves disjointness from every packing contained in
the old region. -/
theorem RouteExtensionData.route_mutuallyNodeDisjoint
    {X U A B C Y Z : Finset V}
    {P : PerfectPathPacking G X U}
    {Q : PerfectPathPacking G A B}
    {hU : U ⊆ B}
    {hPstay : P.toPathPacking.StaysIn C}
    {hQinternal : Q.toPathPacking.InternallyDisjointFromSet C}
    {hAdisj : Disjoint A C}
    (D : RouteExtensionData P Q hU hPstay hQinternal hAdisj)
    (K : PathPacking G Y Z)
    (hKstay : K.StaysIn C)
    (hPK : P.toPathPacking.MutuallyNodeDisjoint K) :
    D.route.toPathPacking.MutuallyNodeDisjoint K := by
  intro i j
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro z hzD hzK
  rcases D.route_path_subset i with ⟨p, q, hqU, hsubset⟩
  rcases Finset.mem_union.mp (hsubset hzD) with hzP | hzQ
  · exact Finset.disjoint_left.mp (hPK p j) hzP hzK
  · have hzC : z ∈ C := hKstay j hzK
    rcases hQinternal q hzQ hzC with hzSource | hzTarget
    · have hzA : z ∈ A := by
        rw [hzSource]
        exact Q.source_mem q
      exact Finset.disjoint_left.mp hAdisj hzA hzC
    · have hzU : z ∈ U := by
        simpa [hzTarget] using hqU
      rcases P.target_bijective.2 ⟨z, hzU⟩ with ⟨p', hp'⟩
      have hpTarget : (P.path p').target = z :=
        congrArg Subtype.val hp'
      exact Finset.disjoint_left.mp (hPK p' j)
        (by simpa [hpTarget] using
          GraphPath.target_mem_vertexSet (P.path p')) hzK

/-- Split a perfect packing by a disjoint partition of its source terminals.
The two restricted outputs inherit containment and are mutually
node-disjoint. -/
structure RouteSourceSplitData
    {S₁ S₂ T : Finset V}
    (P : PerfectPathPacking G (S₁ ∪ S₂) T) where
  leftAnchor : Finset V
  rightAnchor : Finset V
  leftRoute : PerfectPathPacking G S₁ leftAnchor
  rightRoute : PerfectPathPacking G S₂ rightAnchor
  leftAnchor_subset : leftAnchor ⊆ T
  rightAnchor_subset : rightAnchor ⊆ T
  routes_disjoint :
    leftRoute.toPathPacking.MutuallyNodeDisjoint rightRoute.toPathPacking
  left_staysIn :
    ∀ {C : Finset V}, P.toPathPacking.StaysIn C →
      leftRoute.toPathPacking.StaysIn C
  right_staysIn :
    ∀ {C : Finset V}, P.toPathPacking.StaysIn C →
      rightRoute.toPathPacking.StaysIn C
  left_internal :
    ∀ {C : Finset V}, P.toPathPacking.InternallyDisjointFromSet C →
      leftRoute.toPathPacking.InternallyDisjointFromSet C
  right_internal :
    ∀ {C : Finset V}, P.toPathPacking.InternallyDisjointFromSet C →
      rightRoute.toPathPacking.InternallyDisjointFromSet C
  left_disjoint_of :
    ∀ {Y Z : Finset V} (K : PathPacking G Y Z),
      P.toPathPacking.MutuallyNodeDisjoint K →
        leftRoute.toPathPacking.MutuallyNodeDisjoint K
  right_disjoint_of :
    ∀ {Y Z : Finset V} (K : PathPacking G Y Z),
      P.toPathPacking.MutuallyNodeDisjoint K →
        rightRoute.toPathPacking.MutuallyNodeDisjoint K

theorem exists_routeSourceSplitData
    {S₁ S₂ T : Finset V}
    (P : PerfectPathPacking G (S₁ ∪ S₂) T)
    (hS : Disjoint S₁ S₂) :
    Nonempty (RouteSourceSplitData P) := by
  classical
  have hS₁ : S₁ ⊆ S₁ ∪ S₂ := Finset.subset_union_left
  have hS₂ : S₂ ⊆ S₁ ∪ S₂ := Finset.subset_union_right
  let L := P.restrictSourceSet S₁ hS₁
  let R := P.restrictSourceSet S₂ hS₂
  exact ⟨{
    leftAnchor := P.targetSet (P.sourceIndexSetOfSubset S₁)
    rightAnchor := P.targetSet (P.sourceIndexSetOfSubset S₂)
    leftRoute := L
    rightRoute := R
    leftAnchor_subset := P.targetSet_subset_right _
    rightAnchor_subset := P.targetSet_subset_right _
    routes_disjoint := by
      intro i j
      apply P.node_disjoint
      intro hij
      have hiS₁ : (P.path i.1).source ∈ S₁ := by
        exact (P.mem_sourceIndexSetOfSubset S₁ i.1).1 i.2
      have hjS₂ : (P.path j.1).source ∈ S₂ := by
        exact (P.mem_sourceIndexSetOfSubset S₂ j.1).1 j.2
      exact Finset.disjoint_left.mp hS hiS₁ (by simpa [hij] using hjS₂)
    left_staysIn := by
      intro C hP
      exact P.restrictSourceSet_staysIn S₁ hS₁ hP
    right_staysIn := by
      intro C hP
      exact P.restrictSourceSet_staysIn S₂ hS₂ hP
    left_internal := by
      intro C hP
      exact P.restrictSourceSet_internallyDisjointFromSet S₁ hS₁ hP
    right_internal := by
      intro C hP
      exact P.restrictSourceSet_internallyDisjointFromSet S₂ hS₂ hP
    left_disjoint_of := by
      intro Y Z K hPK i j
      exact hPK i.1 j
    right_disjoint_of := by
      intro Y Z K hPK i j
      exact hPK i.1 j }⟩

/-- Combine two disjoint route families, extend them together through one
transition, and split them again.  Extending the union once makes the
post-extension mutual disjointness automatic. -/
structure PairedRouteExtensionData
    {X₁ U₁ X₂ U₂ A B C : Finset V}
    (P₁ : PerfectPathPacking G X₁ U₁)
    (P₂ : PerfectPathPacking G X₂ U₂)
    (Q : PerfectPathPacking G A B) where
  leftAnchor : Finset V
  rightAnchor : Finset V
  leftRoute : PerfectPathPacking G X₁ leftAnchor
  rightRoute : PerfectPathPacking G X₂ rightAnchor
  leftAnchor_subset : leftAnchor ⊆ A
  rightAnchor_subset : rightAnchor ⊆ A
  leftRoute_staysIn :
    leftRoute.toPathPacking.StaysIn (C ∪ Q.toPathPacking.vertexSet)
  rightRoute_staysIn :
    rightRoute.toPathPacking.StaysIn (C ∪ Q.toPathPacking.vertexSet)
  routes_disjoint :
    leftRoute.toPathPacking.MutuallyNodeDisjoint rightRoute.toPathPacking
  left_internal_of_trivial_glue :
    ∀ {K : Finset V},
      P₁.toPathPacking.InternallyDisjointFromSet K →
      P₂.toPathPacking.InternallyDisjointFromSet K →
      (∀ i : P₁.Index, (P₁.path i).target ∈ K →
        (P₁.path i).source = (P₁.path i).target) →
      (∀ i : P₂.Index, (P₂.path i).target ∈ K →
        (P₂.path i).source = (P₂.path i).target) →
      Q.toPathPacking.InternallyDisjointFromSet K →
      leftRoute.toPathPacking.InternallyDisjointFromSet K
  right_internal_of_trivial_glue :
    ∀ {K : Finset V},
      P₁.toPathPacking.InternallyDisjointFromSet K →
      P₂.toPathPacking.InternallyDisjointFromSet K →
      (∀ i : P₁.Index, (P₁.path i).target ∈ K →
        (P₁.path i).source = (P₁.path i).target) →
      (∀ i : P₂.Index, (P₂.path i).target ∈ K →
        (P₂.path i).source = (P₂.path i).target) →
      Q.toPathPacking.InternallyDisjointFromSet K →
      rightRoute.toPathPacking.InternallyDisjointFromSet K
  left_disjoint_old :
    ∀ {Y Z : Finset V} (K : PathPacking G Y Z),
      K.StaysIn C →
      P₁.toPathPacking.MutuallyNodeDisjoint K →
      P₂.toPathPacking.MutuallyNodeDisjoint K →
      leftRoute.toPathPacking.MutuallyNodeDisjoint K
  right_disjoint_old :
    ∀ {Y Z : Finset V} (K : PathPacking G Y Z),
      K.StaysIn C →
      P₁.toPathPacking.MutuallyNodeDisjoint K →
      P₂.toPathPacking.MutuallyNodeDisjoint K →
      rightRoute.toPathPacking.MutuallyNodeDisjoint K

theorem exists_pairedRouteExtensionData
    {X₁ U₁ X₂ U₂ A B C : Finset V}
    (P₁ : PerfectPathPacking G X₁ U₁)
    (P₂ : PerfectPathPacking G X₂ U₂)
    (Q : PerfectPathPacking G A B)
    (hP₁stay : P₁.toPathPacking.StaysIn C)
    (hP₂stay : P₂.toPathPacking.StaysIn C)
    (hPnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    (hU : U₁ ∪ U₂ ⊆ B)
    (hQinternal : Q.toPathPacking.InternallyDisjointFromSet C)
    (hAdisj : Disjoint A C) :
    Nonempty (PairedRouteExtensionData (C := C) P₁ P₂ Q) := by
  classical
  have hXdisj :=
    PerfectPathPacking.source_disjoint_of_mutuallyNodeDisjoint P₁ P₂ hPnode
  have hUdisj :=
    PerfectPathPacking.target_disjoint_of_mutuallyNodeDisjoint P₁ P₂ hPnode
  let P := P₁.disjointUnion P₂ hXdisj hUdisj hPnode
  have hPstay : P.toPathPacking.StaysIn C :=
    P₁.disjointUnion_staysIn P₂ hXdisj hUdisj hPnode
      hP₁stay hP₂stay
  let E := Classical.choice
    (exists_routeExtensionData P Q hU hPstay hQinternal hAdisj)
  let Split := Classical.choice
    (exists_routeSourceSplitData E.route hXdisj)
  have hEdisjoint :
      ∀ {Y Z : Finset V} (K : PathPacking G Y Z),
        K.StaysIn C →
        P₁.toPathPacking.MutuallyNodeDisjoint K →
        P₂.toPathPacking.MutuallyNodeDisjoint K →
        E.route.toPathPacking.MutuallyNodeDisjoint K := by
    intro Y Z K hK h₁ h₂
    apply E.route_mutuallyNodeDisjoint K hK
    intro i j
    cases i with
    | inl a => exact h₁ a j
    | inr b => exact h₂ b j
  exact ⟨{
    leftAnchor := Split.leftAnchor
    rightAnchor := Split.rightAnchor
    leftRoute := Split.leftRoute
    rightRoute := Split.rightRoute
    leftAnchor_subset := Split.leftAnchor_subset.trans E.anchor_subset
    rightAnchor_subset := Split.rightAnchor_subset.trans E.anchor_subset
    leftRoute_staysIn := Split.left_staysIn E.route_staysIn
    rightRoute_staysIn := Split.right_staysIn E.route_staysIn
    routes_disjoint := Split.routes_disjoint
    left_internal_of_trivial_glue := by
      intro K h₁ h₂ ht₁ ht₂ hQK
      apply Split.left_internal
      apply E.route_internallyDisjoint_of_trivial_glue
      · exact PerfectPathPacking.disjointUnion_internallyDisjointFromSet
          P₁ P₂ hXdisj hUdisj hPnode h₁ h₂
      · exact hQK
      · intro i hi
        cases i with
        | inl a =>
            simpa [P, PerfectPathPacking.disjointUnion] using ht₁ a hi
        | inr b =>
            simpa [P, PerfectPathPacking.disjointUnion] using ht₂ b hi
    right_internal_of_trivial_glue := by
      intro K h₁ h₂ ht₁ ht₂ hQK
      apply Split.right_internal
      apply E.route_internallyDisjoint_of_trivial_glue
      · exact PerfectPathPacking.disjointUnion_internallyDisjointFromSet
          P₁ P₂ hXdisj hUdisj hPnode h₁ h₂
      · exact hQK
      · intro i hi
        cases i with
        | inl a =>
            simpa [P, PerfectPathPacking.disjointUnion] using ht₁ a hi
        | inr b =>
            simpa [P, PerfectPathPacking.disjointUnion] using ht₂ b hi
    left_disjoint_old := by
      intro Y Z K hK h₁ h₂
      exact Split.left_disjoint_of K (hEdisjoint K hK h₁ h₂)
    right_disjoint_old := by
      intro Y Z K hK h₁ h₂
      exact Split.right_disjoint_of K (hEdisjoint K hK h₁ h₂) }⟩

/-- Packings supported in disjoint vertex regions are mutually node-disjoint. -/
theorem PathPacking.mutuallyNodeDisjoint_of_staysIn_disjoint
    {S₁ T₁ S₂ T₂ C₁ C₂ : Finset V}
    (P : PathPacking G S₁ T₁) (Q : PathPacking G S₂ T₂)
    (hP : P.StaysIn C₁) (hQ : Q.StaysIn C₂)
    (hC : Disjoint C₁ C₂) :
    P.MutuallyNodeDisjoint Q := by
  intro i j
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro x hxP hxQ
  exact Finset.disjoint_left.mp hC (hP i hxP) (hQ j hxQ)

/-- Extend the four exposed routes of two child states through one common
parent transition.  They are first combined into two child groups and then
into one packing, so all post-extension routes remain mutually disjoint. -/
structure TwoGroupRouteExtensionData
    {X₁₁ U₁₁ X₁₂ U₁₂ X₂₁ U₂₁ X₂₂ U₂₂ A B C : Finset V}
    (P₁₁ : PerfectPathPacking G X₁₁ U₁₁)
    (P₁₂ : PerfectPathPacking G X₁₂ U₁₂)
    (P₂₁ : PerfectPathPacking G X₂₁ U₂₁)
    (P₂₂ : PerfectPathPacking G X₂₂ U₂₂)
    (Q : PerfectPathPacking G A B) where
  firstAnchor : Finset V
  secondAnchor : Finset V
  firstRoute : PerfectPathPacking G (X₁₁ ∪ X₁₂) firstAnchor
  secondRoute : PerfectPathPacking G (X₂₁ ∪ X₂₂) secondAnchor
  firstAnchor_subset : firstAnchor ⊆ A
  secondAnchor_subset : secondAnchor ⊆ A
  firstRoute_staysIn :
    firstRoute.toPathPacking.StaysIn (C ∪ Q.toPathPacking.vertexSet)
  secondRoute_staysIn :
    secondRoute.toPathPacking.StaysIn (C ∪ Q.toPathPacking.vertexSet)
  routes_disjoint :
    firstRoute.toPathPacking.MutuallyNodeDisjoint secondRoute.toPathPacking

theorem exists_twoGroupRouteExtensionData
    {X₁₁ U₁₁ X₁₂ U₁₂ X₂₁ U₂₁ X₂₂ U₂₂ A B C : Finset V}
    (P₁₁ : PerfectPathPacking G X₁₁ U₁₁)
    (P₁₂ : PerfectPathPacking G X₁₂ U₁₂)
    (P₂₁ : PerfectPathPacking G X₂₁ U₂₁)
    (P₂₂ : PerfectPathPacking G X₂₂ U₂₂)
    (Q : PerfectPathPacking G A B)
    (h₁₂ : P₁₁.toPathPacking.MutuallyNodeDisjoint P₁₂.toPathPacking)
    (h₃₄ : P₂₁.toPathPacking.MutuallyNodeDisjoint P₂₂.toPathPacking)
    (h₁₁₂₁ :
      P₁₁.toPathPacking.MutuallyNodeDisjoint P₂₁.toPathPacking)
    (h₁₁₂₂ :
      P₁₁.toPathPacking.MutuallyNodeDisjoint P₂₂.toPathPacking)
    (h₁₂₂₁ :
      P₁₂.toPathPacking.MutuallyNodeDisjoint P₂₁.toPathPacking)
    (h₁₂₂₂ :
      P₁₂.toPathPacking.MutuallyNodeDisjoint P₂₂.toPathPacking)
    (h₁₁stay : P₁₁.toPathPacking.StaysIn C)
    (h₁₂stay : P₁₂.toPathPacking.StaysIn C)
    (h₂₁stay : P₂₁.toPathPacking.StaysIn C)
    (h₂₂stay : P₂₂.toPathPacking.StaysIn C)
    (hU : (U₁₁ ∪ U₁₂) ∪ (U₂₁ ∪ U₂₂) ⊆ B)
    (hQinternal : Q.toPathPacking.InternallyDisjointFromSet C)
    (hAdisj : Disjoint A C) :
    Nonempty
      (TwoGroupRouteExtensionData
        (C := C) P₁₁ P₁₂ P₂₁ P₂₂ Q) := by
  classical
  have hX₁ :=
    PerfectPathPacking.source_disjoint_of_mutuallyNodeDisjoint
      P₁₁ P₁₂ h₁₂
  have hU₁ :=
    PerfectPathPacking.target_disjoint_of_mutuallyNodeDisjoint
      P₁₁ P₁₂ h₁₂
  have hX₂ :=
    PerfectPathPacking.source_disjoint_of_mutuallyNodeDisjoint
      P₂₁ P₂₂ h₃₄
  have hU₂ :=
    PerfectPathPacking.target_disjoint_of_mutuallyNodeDisjoint
      P₂₁ P₂₂ h₃₄
  let P₁ := P₁₁.disjointUnion P₁₂ hX₁ hU₁ h₁₂
  let P₂ := P₂₁.disjointUnion P₂₂ hX₂ hU₂ h₃₄
  have hP₁₂ : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking := by
    intro i j
    cases i with
    | inl i =>
        cases j with
        | inl j => exact h₁₁₂₁ i j
        | inr j => exact h₁₁₂₂ i j
    | inr i =>
        cases j with
        | inl j => exact h₁₂₂₁ i j
        | inr j => exact h₁₂₂₂ i j
  have hP₁stay : P₁.toPathPacking.StaysIn C :=
    P₁₁.disjointUnion_staysIn P₁₂ hX₁ hU₁ h₁₂ h₁₁stay h₁₂stay
  have hP₂stay : P₂.toPathPacking.StaysIn C :=
    P₂₁.disjointUnion_staysIn P₂₂ hX₂ hU₂ h₃₄ h₂₁stay h₂₂stay
  let E := Classical.choice
    (exists_pairedRouteExtensionData P₁ P₂ Q
      hP₁stay hP₂stay hP₁₂ hU hQinternal hAdisj)
  exact ⟨{
    firstAnchor := E.leftAnchor
    secondAnchor := E.rightAnchor
    firstRoute := E.leftRoute
    secondRoute := E.rightRoute
    firstAnchor_subset := E.leftAnchor_subset
    secondAnchor_subset := E.rightAnchor_subset
    firstRoute_staysIn := E.leftRoute_staysIn
    secondRoute_staysIn := E.rightRoute_staysIn
    routes_disjoint := E.routes_disjoint }⟩

/-- Combine the two outer routes of one child and stop at the parent-side
interface.  Besides the ordinary route-extension data, the result records
internal disjointness from the parent cluster; this is the first-entry prefix
used as `Q'_X ∪ Q'_Y` in Step 2. -/
structure ChildGroupPrefixData
    {X₁ U₁ X₂ U₂ A B C K : Finset V}
    (P₁ : PerfectPathPacking G X₁ U₁)
    (P₂ : PerfectPathPacking G X₂ U₂)
    (Q : PerfectPathPacking G A B) where
  anchor : Finset V
  anchor_subset : anchor ⊆ A
  route : PerfectPathPacking G (X₁ ∪ X₂) anchor
  route_staysIn :
    route.toPathPacking.StaysIn
      (C ∪ Q.toPathPacking.vertexSet)
  route_internallyDisjoint_parent :
    route.toPathPacking.InternallyDisjointFromSet K
  route_internal_of_trivial_glue :
    ∀ {L : Finset V},
      P₁.toPathPacking.InternallyDisjointFromSet L →
      P₂.toPathPacking.InternallyDisjointFromSet L →
      (∀ i : P₁.Index, (P₁.path i).target ∈ L →
        (P₁.path i).source = (P₁.path i).target) →
      (∀ i : P₂.Index, (P₂.path i).target ∈ L →
        (P₂.path i).source = (P₂.path i).target) →
      Q.toPathPacking.InternallyDisjointFromSet L →
      route.toPathPacking.InternallyDisjointFromSet L
  route_disjoint_old :
    ∀ {Y Z : Finset V} (R : PathPacking G Y Z),
      R.StaysIn C →
      P₁.toPathPacking.MutuallyNodeDisjoint R →
      P₂.toPathPacking.MutuallyNodeDisjoint R →
      route.toPathPacking.MutuallyNodeDisjoint R

theorem exists_childGroupPrefixData
    {X₁ U₁ X₂ U₂ A B C K : Finset V}
    (P₁ : PerfectPathPacking G X₁ U₁)
    (P₂ : PerfectPathPacking G X₂ U₂)
    (Q : PerfectPathPacking G A B)
    (hPnode :
      P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    (hP₁stay : P₁.toPathPacking.StaysIn C)
    (hP₂stay : P₂.toPathPacking.StaysIn C)
    (hU : U₁ ∪ U₂ ⊆ B)
    (hQinternalC : Q.toPathPacking.InternallyDisjointFromSet C)
    (hAdisjC : Disjoint A C)
    (hCdisjK : Disjoint C K)
    (hQinternalK : Q.toPathPacking.InternallyDisjointFromSet K)
    (hBdisjK : Disjoint B K) :
    Nonempty (ChildGroupPrefixData (C := C) (K := K) P₁ P₂ Q) := by
  classical
  have hX :=
    PerfectPathPacking.source_disjoint_of_mutuallyNodeDisjoint
      P₁ P₂ hPnode
  have hUdisj :=
    PerfectPathPacking.target_disjoint_of_mutuallyNodeDisjoint
      P₁ P₂ hPnode
  let P := P₁.disjointUnion P₂ hX hUdisj hPnode
  have hPstay : P.toPathPacking.StaysIn C :=
    P₁.disjointUnion_staysIn P₂ hX hUdisj hPnode hP₁stay hP₂stay
  have hPinternalK :
      P.toPathPacking.InternallyDisjointFromSet K := by
    intro i x hx hxK
    exact False.elim
      (Finset.disjoint_left.mp hCdisjK (hPstay i hx) hxK)
  let E := Classical.choice
    (exists_routeExtensionData P Q hU hPstay hQinternalC hAdisjC)
  have hrouteInternal :
      E.route.toPathPacking.InternallyDisjointFromSet K := by
    exact E.route_internallyDisjoint hPinternalK hQinternalK
      (Finset.disjoint_of_subset_left hU hBdisjK)
  exact ⟨{
    anchor := E.anchor
    anchor_subset := E.anchor_subset
    route := E.route
    route_staysIn := E.route_staysIn
    route_internallyDisjoint_parent := hrouteInternal
    route_internal_of_trivial_glue := by
      intro L hP₁L hP₂L ht₁ ht₂ hQL
      apply E.route_internallyDisjoint_of_trivial_glue
      · exact PerfectPathPacking.disjointUnion_internallyDisjointFromSet
          P₁ P₂ hX hUdisj hPnode hP₁L hP₂L
      · exact hQL
      · intro i hi
        cases i with
        | inl i =>
            simpa [P, PerfectPathPacking.disjointUnion] using ht₁ i hi
        | inr i =>
            simpa [P, PerfectPathPacking.disjointUnion] using ht₂ i hi
    route_disjoint_old := by
      intro Y Z R hR hP₁R hP₂R
      apply E.route_mutuallyNodeDisjoint R hR
      intro i j
      cases i with
      | inl i => exact hP₁R i j
      | inr i => exact hP₂R i j }⟩

/-- Direct source-faithful bridge at a branching cluster.  Equal `4*w`
subsets of the two parent-side anchor sets are linked inside the parent
cluster, then concatenated with the corresponding first-entry child routes.
The exposed source and target sets are precisely the child reserves consumed
by the bridge. -/
structure DirectChildBridgeData
    {X₁ A₁ X₂ A₂ C₁ C₂ K : Finset V}
    (P₁ : PerfectPathPacking G X₁ A₁)
    (P₂ : PerfectPathPacking G X₂ A₂)
    (w : ℕ) where
  usedFirst : Finset V
  usedSecond : Finset V
  usedFirst_subset : usedFirst ⊆ X₁
  usedSecond_subset : usedSecond ⊆ X₂
  usedFirst_card : usedFirst.card = 4 * w
  usedSecond_card : usedSecond.card = 4 * w
  connector : PerfectPathPacking G usedFirst usedSecond
  connector_card : connector.card = 4 * w
  connector_staysIn :
    connector.toPathPacking.StaysIn (C₁ ∪ (K ∪ C₂))

set_option maxHeartbeats 3000000 in
/-- Build the direct `4*w` bridge used by the two-child DFS merge. -/
theorem exists_directChildBridgeData
    {X₁ A₁ X₂ A₂ C₁ C₂ K : Finset V}
    (P₁ : PerfectPathPacking G X₁ A₁)
    (P₂ : PerfectPathPacking G X₂ A₂)
    (w : ℕ)
    (hP₁stay : P₁.toPathPacking.StaysIn C₁)
    (hP₂stay : P₂.toPathPacking.StaysIn C₂)
    (hP₁internalK : P₁.toPathPacking.InternallyDisjointFromSet K)
    (hP₂internalK : P₂.toPathPacking.InternallyDisjointFromSet K)
    (hPdisj :
      P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    (hlink : NodeLinkedIn G K A₁ A₂)
    (hC₁C₂ : Disjoint C₁ C₂)
    (hX₁K : Disjoint X₁ K)
    (hX₂K : Disjoint X₂ K)
    (hfour₁ : 4 * w ≤ P₁.card)
    (hfour₂ : 4 * w ≤ P₂.card) :
    Nonempty
      (DirectChildBridgeData
        (C₁ := C₁) (C₂ := C₂) (K := K) P₁ P₂ w) := by
  classical
  have hA₁card : A₁.card = P₁.card := P₁.card_eq_right_card.symm
  have hA₂card : A₂.card = P₂.card := P₂.card_eq_right_card.symm
  obtain ⟨A₄, hA₄, hA₄card⟩ :=
    Finset.exists_subset_card_eq (s := A₁)
      (by simpa [hA₁card] using hfour₁)
  obtain ⟨A₂₄, hA₂₄, hA₂₄card⟩ :=
    Finset.exists_subset_card_eq (s := A₂)
      (by simpa [hA₂card] using hfour₂)
  have hAcard : A₄.card = A₂₄.card :=
    hA₄card.trans hA₂₄card.symm
  obtain ⟨Q, hQcard, hQstay⟩ :=
    NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      (hlink.mono_terminals hA₄ hA₂₄) hAcard
  let R₁ := P₁.restrictTargetSet A₄ hA₄
  let R₂ := P₂.restrictTargetSet A₂₄ hA₂₄
  have hR₁stay : R₁.toPathPacking.StaysIn C₁ :=
    P₁.restrictTargetSet_staysIn A₄ hA₄ hP₁stay
  have hR₂stay : R₂.toPathPacking.StaysIn C₂ :=
    P₂.restrictTargetSet_staysIn A₂₄ hA₂₄ hP₂stay
  have hR₁internalK :
      R₁.toPathPacking.InternallyDisjointFromSet K :=
    P₁.restrictTargetSet_internallyDisjointFromSet A₄ hA₄ hP₁internalK
  have hR₂internalK :
      R₂.toPathPacking.InternallyDisjointFromSet K :=
    P₂.restrictTargetSet_internallyDisjointFromSet A₂₄ hA₂₄ hP₂internalK
  have hR₁sourceK :
      Disjoint
        (P₁.sourceSet (P₁.targetIndexSetOfSubset A₄)) K :=
    Finset.disjoint_of_subset_left
      (P₁.sourceSet_subset_left _) hX₁K
  let H :=
    R₁.concatOfFirstInternallyDisjointSecondStaysIn
      Q hR₁internalK hQstay hR₁sourceK
  have hR₂revInternalC₁ :
      R₂.reverse.toPathPacking.InternallyDisjointFromSet C₁ := by
    apply PerfectPathPacking.reverse_internallyDisjointFromSet
    intro i z hz hzC₁
    exact False.elim
      (Finset.disjoint_left.mp hC₁C₂ hzC₁ (hR₂stay i hz))
  have hR₂revInternalK :
      R₂.reverse.toPathPacking.InternallyDisjointFromSet K :=
    PerfectPathPacking.reverse_internallyDisjointFromSet R₂ hR₂internalK
  have hR₂revInternal :
      R₂.reverse.toPathPacking.InternallyDisjointFromSet (C₁ ∪ K) := by
    intro i z hz hzUnion
    rcases Finset.mem_union.mp hzUnion with hzC₁ | hzK
    · exact hR₂revInternalC₁ i hz hzC₁
    · exact hR₂revInternalK i hz hzK
  have hR₂revStay :
      R₂.reverse.toPathPacking.StaysIn C₂ :=
    PerfectPathPacking.reverse_staysIn R₂ hR₂stay
  have hHstay :
      H.toPathPacking.StaysIn (C₁ ∪ K) :=
    R₁.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
      Q hR₁internalK hQstay hR₁sourceK hR₁stay
  have hR₂targetDisj :
      Disjoint
        (P₂.sourceSet (P₂.targetIndexSetOfSubset A₂₄))
        (C₁ ∪ K) := by
    rw [Finset.disjoint_left]
    intro x hxSource hxUnion
    have hxX₂ : x ∈ X₂ := P₂.sourceSet_subset_left _ hxSource
    rcases Finset.mem_union.mp hxUnion with hxC₁ | hxK
    · rcases P₂.source_bijective.2 ⟨x, hxX₂⟩ with ⟨i, hi⟩
      have hi' : (P₂.path i).source = x := congrArg Subtype.val hi
      have hxC₂ : x ∈ C₂ := hP₂stay i (by
        simpa [hi'] using GraphPath.source_mem_vertexSet (P₂.path i))
      exact Finset.disjoint_left.mp hC₁C₂ hxC₁ hxC₂
    · exact Finset.disjoint_left.mp hX₂K hxX₂ hxK
  let B :=
    H.concatOfFirstStaysInSecondInternallyDisjoint
      R₂.reverse hHstay hR₂revInternal hR₂targetDisj
  have hBstay :
      B.toPathPacking.StaysIn ((C₁ ∪ K) ∪ C₂) :=
    H.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
      R₂.reverse hHstay hR₂revInternal hR₂targetDisj hR₂revStay
  exact ⟨{
    usedFirst := P₁.sourceSet (P₁.targetIndexSetOfSubset A₄)
    usedSecond := P₂.sourceSet (P₂.targetIndexSetOfSubset A₂₄)
    usedFirst_subset := P₁.sourceSet_subset_left _
    usedSecond_subset := P₂.sourceSet_subset_left _
    usedFirst_card := by
      calc
        (P₁.sourceSet (P₁.targetIndexSetOfSubset A₄)).card =
            (P₁.targetIndexSetOfSubset A₄).card :=
          P₁.sourceSet_card _
        _ = A₄.card := P₁.targetIndexSetOfSubset_card hA₄
        _ = 4 * w := hA₄card
    usedSecond_card := by
      calc
        (P₂.sourceSet (P₂.targetIndexSetOfSubset A₂₄)).card =
            (P₂.targetIndexSetOfSubset A₂₄).card :=
          P₂.sourceSet_card _
        _ = A₂₄.card := P₂.targetIndexSetOfSubset_card hA₂₄
        _ = 4 * w := hA₂₄card
    connector := B
    connector_card := by
      calc
        B.card = H.card := by simp [B]
        _ = R₁.card := by simp [H]
        _ = A₄.card := by simp [R₁]
        _ = 4 * w := hA₄card
    connector_staysIn := by
      simpa [Finset.union_assoc] using hBstay }⟩

/-- Routed base case at one selected leaf. -/
theorem exists_theorem46RoutedDfsState_leaf
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v : Fin m} {A : Finset V} {q : ℕ}
    (E : Theorem47SubtreeRoutingData S v A q)
    (hv : v ∈ S.leaves)
    (L R : Finset V)
    (hL : L ⊆ E.leafTarget v)
    (hR : R ⊆ E.leafTarget v)
    (hLR : Disjoint L R)
    (hLcard : L.card = W / (2 * ell))
    (hRcard : R.card = W / (2 * ell))
    (hw : 0 < w)
    (hwHalf : w ≤ W / (2 * ell)) :
    Nonempty (Theorem46RoutedDfsState (w := w) S v A) := by
  classical
  have hbelow := S.selectedBelow_eq_singleton_of_mem_leaves hv
  have hvbelow : v ∈ S.selectedBelow v := by simp [hbelow]
  rcases E.exists_leafSingletonStrongPathData S hvbelow L R hL hR hLR
      hw (by simpa [hLcard] using hwHalf)
      (by simpa [hRcard] using hwHalf) with
    ⟨D⟩
  let PL := E.restrictLeafTarget S hvbelow L hL
  let PR := E.restrictLeafTarget S hvbelow R hR
  let O := (S.selectedBelow v).equivFin.symm
  have hOeq : ∀ i, (O i).1 = v := by
    intro i
    have : (O i).1 ∈ ({v} : Finset (Fin m)) := by
      simpa [hbelow] using (O i).2
    simpa using this
  have hcard : (S.selectedBelow v).card = 1 := by simp [hbelow]
  let P : StrongPathOfSetsSystem G (S.selectedBelow v).card w := {
    length_pos := by omega
    width_pos := hw
    cluster := fun _ => Tsys.cluster v
    cluster_connected := fun _ => Tsys.cluster_connected v
    cluster_disjoint := by
      intro i j hij
      exact False.elim (hij (by apply Fin.ext; omega))
    left := fun _ => D.leftNails
    right := fun _ => D.rightNails
    left_subset_cluster := fun _ =>
      D.left_subset.trans hL |>.trans (E.leafTarget_subset v hvbelow)
    right_subset_cluster := fun _ =>
      D.right_subset.trans hR |>.trans (E.leafTarget_subset v hvbelow)
    left_right_disjoint := fun _ => hLR.mono D.left_subset D.right_subset
    left_card := fun _ => by
      simpa [D.left_eq] using
        D.system.left_card D.system.toPathOfSetsSystem.firstIndex
    right_card := fun _ => by
      simpa [D.right_eq] using
        D.system.right_card D.system.toPathOfSetsSystem.lastIndex
    connector := by intro i hi; exact False.elim (by omega)
    connector_card := by intro i hi; exact False.elim (by omega)
    connector_internally_disjoint_clusters := by
      intro i hi; exact False.elim (by omega)
    connector_mutually_nodeDisjoint := by
      intro i j hi; exact False.elim (by omega)
    left_nodeWellLinked := fun _ =>
      NodeWellLinkedIn.mono_terminals
        (E.leafTarget_nodeWellLinked v hvbelow) (D.left_subset.trans hL)
    right_nodeWellLinked := fun _ =>
      NodeWellLinkedIn.mono_terminals
        (E.leafTarget_nodeWellLinked v hvbelow) (D.right_subset.trans hR)
    left_right_nodeLinked := fun _ =>
      NodeWellLinkedIn.nodeLinkedIn_between_disjoint_subsets
        (E.leafTarget_nodeWellLinked v hvbelow)
        (D.left_subset.trans hL) (D.right_subset.trans hR)
        (hLR.mono D.left_subset D.right_subset) }
  exact ⟨{
    active := ⟨v, hvbelow⟩
    system := P
    leafOrder := O
    leafOrder_bijective := O.bijective
    cluster_eq := by intro i; simp [P, hOeq i]
    leftReserve := L
    rightReserve := R
    leftAmbient := E.leafTarget v
    rightAmbient := E.leafTarget v
    leftAnchor := E.packing.sourceSet
      (E.packing.targetIndexSetOfSubset L)
    rightAnchor := E.packing.sourceSet
      (E.packing.targetIndexSetOfSubset R)
    leftRoute := PL.reverse
    rightRoute := PR.reverse
    leftAnchor_subset := E.packing.sourceSet_subset_left _
    rightAnchor_subset := E.packing.sourceSet_subset_left _
    leftAmbient_subset_leaf := by
      simpa [hOeq] using E.leafTarget_subset v hvbelow
    rightAmbient_subset_leaf := by
      simpa [hOeq] using E.leafTarget_subset v hvbelow
    leftAmbient_nodeWellLinked := by
      simpa [hOeq] using E.leafTarget_nodeWellLinked v hvbelow
    rightAmbient_nodeWellLinked := by
      simpa [hOeq] using E.leafTarget_nodeWellLinked v hvbelow
    outerAmbient_eq_of_singleton := by
      intro _
      rfl
    outerAmbient_linked_of_singleton := by
      intro _ L' R' hL' hR' hdisj
      simpa [hOeq] using
        NodeWellLinkedIn.nodeLinkedIn_between_disjoint_subsets
          (E.leafTarget_nodeWellLinked v hvbelow) hL' hR' hdisj
    leftReserve_subset_ambient := hL
    rightReserve_subset_ambient := hR
    leftReserve_disjoint_firstRight := by
      simpa [P] using
        Finset.disjoint_of_subset_right D.right_subset hLR
    rightReserve_disjoint_lastLeft := by
      simpa [P] using
        Finset.disjoint_of_subset_left D.left_subset hLR
    first_left_subset_ambient := by
      simpa [P] using D.left_subset.trans hL
    first_right_subset_ambient := by
      simpa [P] using D.right_subset.trans hR
    last_left_subset_ambient := by
      simpa [P] using D.left_subset.trans hL
    last_right_subset_ambient := by
      simpa [P] using D.right_subset.trans hR
    leftReserve_subset_leaf := by
      simpa [hOeq] using hL.trans (E.leafTarget_subset v hvbelow)
    rightReserve_subset_leaf := by
      simpa [hOeq] using hR.trans (E.leafTarget_subset v hvbelow)
    left_nails_subset := by simpa [P] using D.left_subset
    right_nails_subset := by simpa [P] using D.right_subset
    left_reserve_count := by simpa [hLcard, hcard]
    right_reserve_count := by simpa [hRcard, hcard]
    leftRoute_staysIn :=
      PerfectPathPacking.reverse_staysIn PL
        (E.packing.restrictTargetSet_staysIn L (by
          intro z hz
          exact Finset.mem_biUnion.mpr ⟨v, hvbelow, hL hz⟩)
          E.packing_staysIn)
    rightRoute_staysIn :=
      PerfectPathPacking.reverse_staysIn PR
        (E.packing.restrictTargetSet_staysIn R (by
          intro z hz
          exact Finset.mem_biUnion.mpr ⟨v, hvbelow, hR hz⟩)
          E.packing_staysIn)
    leftRoute_internallyDisjoint_leafCluster := by
      intro x hx
      have hxv : x = v := by simpa [hbelow] using hx
      subst x
      apply PerfectPathPacking.reverse_internallyDisjointFromSet
      exact E.packing.restrictTargetSet_internallyDisjointFromSet L
        (by
          intro z hz
          exact Finset.mem_biUnion.mpr ⟨v, hvbelow, hL hz⟩)
        (E.packing_internallyDisjoint_leafCluster v hvbelow)
    rightRoute_internallyDisjoint_leafCluster := by
      intro x hx
      have hxv : x = v := by simpa [hbelow] using hx
      subst x
      apply PerfectPathPacking.reverse_internallyDisjointFromSet
      exact E.packing.restrictTargetSet_internallyDisjointFromSet R
        (by
          intro z hz
          exact Finset.mem_biUnion.mpr ⟨v, hvbelow, hR hz⟩)
        (E.packing_internallyDisjoint_leafCluster v hvbelow)
    leftRoute_trivial_of_root_selected := by
      intro _ i
      change (E.packing.path i.1).target = (E.packing.path i.1).source
      exact (E.packing_trivial_of_root_selected hv i.1).symm
    rightRoute_trivial_of_root_selected := by
      intro _ i
      change (E.packing.path i.1).target = (E.packing.path i.1).source
      exact (E.packing_trivial_of_root_selected hv i.1).symm
    outerRoutes_disjoint := by
      intro i j
      change GraphPath.NodeDisjoint
        (PL.path i).reverse (PR.path j).reverse
      simpa [GraphPath.NodeDisjoint] using
        E.packing.node_disjoint (by
          intro hij
          have hiL : (E.packing.path i.1).target ∈ L := by
            exact (E.packing.mem_targetIndexSetOfSubset L i.1).1 i.2
          have hjR : (E.packing.path j.1).target ∈ R := by
            exact (E.packing.mem_targetIndexSetOfSubset R j.1).1 j.2
          exact Finset.disjoint_left.mp hLR hiL (by simpa [hij] using hjR))
    connectors_stayIn := by intro i hi; simp [hcard] at hi
    leftRoute_disjoint_connectors := by intro i hi; simp [hcard] at hi
    rightRoute_disjoint_connectors := by intro i hi; simp [hcard] at hi }⟩

/-- A degree-two meta-vertex only transports the two exposed reserve routes
through its Step 1 transition.  The installed path-of-sets system is unchanged
up to the equality of selected descendant sets. -/
theorem Theorem46RoutedDfsState.liftOneChild
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v p c : Fin m}
    {hpv : Tsys.metaTree.Adj v p} {hvc : Tsys.metaTree.Adj v c}
    {A : Finset V}
    (hc : IsChild Tsys.meta_isTree S.root v c)
    (hbelow : S.selectedBelow v = S.selectedBelow c)
    (hAcluster : A ⊆ Tsys.cluster v)
    (D : Theorem47OneChildTransitionData Tsys hpv hvc A)
    (C : Theorem46RoutedDfsState (w := w) S c D.childIncoming) :
    Nonempty (Theorem46RoutedDfsState (w := w) S v A) := by
  classical
  have hcard :
      (S.selectedBelow v).card = (S.selectedBelow c).card :=
    congrArg Finset.card hbelow
  have hvcEq : hvc = S.adj_child hc := Subsingleton.elim _ _
  have hDinternal :
      D.transition.toPathPacking.InternallyDisjointFromSet
        (S.subtreeRegion c) := by
    apply S.transition_internallyDisjoint_subtreeRegion
      hc D.transition (Z := ∅)
    · simpa [hvcEq] using D.transition_staysIn
    · simpa [hvcEq] using D.transition_internallyDisjoint_child
    · exact Finset.disjoint_empty_left _
  have hAdisj : Disjoint A (S.subtreeRegion c) :=
    Finset.disjoint_of_subset_left hAcluster
      (S.cluster_disjoint_subtreeRegion hc)
  have hanchors :
      C.leftAnchor ∪ C.rightAnchor ⊆ D.childIncoming :=
    Finset.union_subset C.leftAnchor_subset C.rightAnchor_subset
  let E := Classical.choice
    (exists_pairedRouteExtensionData C.leftRoute C.rightRoute D.transition
      C.leftRoute_staysIn C.rightRoute_staysIn C.outerRoutes_disjoint
      hanchors hDinternal hAdisj)
  have htransitionStay :
      D.transition.toPathPacking.StaysIn (S.subtreeRegion v) := by
    intro i x hx
    rcases Finset.mem_union.mp (D.transition_staysIn i hx) with hxV | hxQ
    · exact S.cluster_subset_subtreeRegion v hxV
    · exact (by
        apply S.childConnector_subset_subtreeRegion hc
        simpa [hvcEq] using hxQ)
  have hrouteSupport :
      S.subtreeRegion c ∪ D.transition.toPathPacking.vertexSet ⊆
        S.subtreeRegion v := by
    apply Finset.union_subset
    · exact S.subtreeRegion_mono_child hc
    · intro x hx
      rcases D.transition.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
      exact htransitionStay i hi
  let Psys : StrongPathOfSetsSystem G (S.selectedBelow v).card w :=
    C.system.castLength hcard.symm
  let O :
      Fin (S.selectedBelow v).card →
        {x : Fin m // x ∈ S.selectedBelow v} :=
    fun i =>
      ⟨(C.leafOrder (Fin.cast hcard i)).1,
        by simpa [hbelow] using
          (C.leafOrder (Fin.cast hcard i)).2⟩
  have hfirst :
      Fin.cast hcard Psys.toPathOfSetsSystem.firstIndex =
        C.system.toPathOfSetsSystem.firstIndex := rfl
  have hlast :
      Fin.cast hcard Psys.toPathOfSetsSystem.lastIndex =
        C.system.toPathOfSetsSystem.lastIndex := by
    apply Fin.ext
    exact congrArg (fun n => n - 1) hcard
  exact ⟨{
    active := by simpa [hbelow] using C.active
    system := Psys
    leafOrder := O
    leafOrder_bijective := by
      constructor
      · intro i j hij
        have hc :
            C.leafOrder (Fin.cast hcard i) =
              C.leafOrder (Fin.cast hcard j) := by
          apply Subtype.ext
          simpa [O] using congrArg Subtype.val hij
        exact (Fin.cast_injective hcard)
          (C.leafOrder_bijective.1 hc)
      · intro x
        let xc : {z : Fin m // z ∈ S.selectedBelow c} :=
          ⟨x.1, by simpa [hbelow] using x.2⟩
        rcases C.leafOrder_bijective.2 xc with ⟨i, hi⟩
        refine ⟨Fin.cast hcard.symm i, ?_⟩
        apply Subtype.ext
        simpa [O, xc] using congrArg Subtype.val hi
    cluster_eq := by
      intro i
      simpa [Psys, O] using C.cluster_eq (Fin.cast hcard i)
    leftReserve := C.leftReserve
    rightReserve := C.rightReserve
    leftAmbient := C.leftAmbient
    rightAmbient := C.rightAmbient
    leftAnchor := E.leftAnchor
    rightAnchor := E.rightAnchor
    leftRoute := E.leftRoute
    rightRoute := E.rightRoute
    leftAnchor_subset := E.leftAnchor_subset
    rightAnchor_subset := E.rightAnchor_subset
    leftAmbient_subset_leaf := by
      simpa [O, hfirst] using C.leftAmbient_subset_leaf
    rightAmbient_subset_leaf := by
      simpa [O, hlast] using C.rightAmbient_subset_leaf
    leftAmbient_nodeWellLinked := by
      simpa [O, hfirst] using C.leftAmbient_nodeWellLinked
    rightAmbient_nodeWellLinked := by
      simpa [O, hlast] using C.rightAmbient_nodeWellLinked
    outerAmbient_eq_of_singleton := by
      intro h
      have h' :
          C.system.toPathOfSetsSystem.firstIndex =
            C.system.toPathOfSetsSystem.lastIndex := by
        apply Fin.ext
        have hv := congrArg Fin.val h
        have hv' :
            0 = (S.selectedBelow v).card - 1 := by
          simpa [Psys] using hv
        change 0 = (S.selectedBelow c).card - 1
        rw [← hcard]
        exact hv'
      exact C.outerAmbient_eq_of_singleton h'
    outerAmbient_linked_of_singleton := by
      intro h L R hL hR hdisj
      have h' :
          C.system.toPathOfSetsSystem.firstIndex =
            C.system.toPathOfSetsSystem.lastIndex := by
        apply Fin.ext
        have hv := congrArg Fin.val h
        have hv' :
            0 = (S.selectedBelow v).card - 1 := by
          simpa [Psys] using hv
        change 0 = (S.selectedBelow c).card - 1
        rw [← hcard]
        exact hv'
      simpa [O, hfirst] using
        C.outerAmbient_linked_of_singleton h' hL hR hdisj
    leftReserve_subset_ambient := C.leftReserve_subset_ambient
    rightReserve_subset_ambient := C.rightReserve_subset_ambient
    leftReserve_disjoint_firstRight := by
      simpa [Psys, hfirst] using C.leftReserve_disjoint_firstRight
    rightReserve_disjoint_lastLeft := by
      simpa [Psys, hlast] using C.rightReserve_disjoint_lastLeft
    first_left_subset_ambient := by
      simpa [Psys, hfirst] using C.first_left_subset_ambient
    first_right_subset_ambient := by
      simpa [Psys, hfirst] using C.first_right_subset_ambient
    last_left_subset_ambient := by
      simpa [Psys, hlast] using C.last_left_subset_ambient
    last_right_subset_ambient := by
      simpa [Psys, hlast] using C.last_right_subset_ambient
    leftReserve_subset_leaf := by
      simpa [O, hfirst] using C.leftReserve_subset_leaf
    rightReserve_subset_leaf := by
      simpa [O, hlast] using C.rightReserve_subset_leaf
    left_nails_subset := by
      simpa [Psys, hfirst] using C.left_nails_subset
    right_nails_subset := by
      simpa [Psys, hlast] using C.right_nails_subset
    left_reserve_count := by
      simpa [hcard] using C.left_reserve_count
    right_reserve_count := by
      simpa [hcard] using C.right_reserve_count
    leftRoute_staysIn := fun i x hx =>
      hrouteSupport (E.leftRoute_staysIn i hx)
    rightRoute_staysIn := fun i x hx =>
      hrouteSupport (E.rightRoute_staysIn i hx)
    leftRoute_internallyDisjoint_leafCluster := by
      intro x hx
      have hxc : x ∈ S.selectedBelow c := by simpa [hbelow] using hx
      have hclusterSub :
          Tsys.cluster x ⊆ S.subtreeRegion c :=
        S.cluster_subset_subtreeRegion_of_mem
          (S.selectedBelow_subset_descendants c hxc)
      apply E.left_internal_of_trivial_glue
      · exact C.leftRoute_internallyDisjoint_leafCluster x hxc
      · exact C.rightRoute_internallyDisjoint_leafCluster x hxc
      · intro i hi
        by_cases hxcEq : x = c
        · subst x
          exact C.leftRoute_trivial_of_root_selected
            (S.selectedBelow_subset_leaves c hxc) i
        · exact False.elim
            (Finset.disjoint_left.mp (Tsys.cluster_disjoint hxcEq)
              hi
              (D.childIncoming_subset
                (C.leftAnchor_subset (C.leftRoute.target_mem i)) |>
                  Tsys.interface_subset_cluster c v hvc.symm))
      · intro i hi
        by_cases hxcEq : x = c
        · subst x
          exact C.rightRoute_trivial_of_root_selected
            (S.selectedBelow_subset_leaves c hxc) i
        · exact False.elim
            (Finset.disjoint_left.mp (Tsys.cluster_disjoint hxcEq)
              hi
              (D.childIncoming_subset
                (C.rightAnchor_subset (C.rightRoute.target_mem i)) |>
                  Tsys.interface_subset_cluster c v hvc.symm))
      · intro i z hz hzCluster
        exact hDinternal i hz (hclusterSub hzCluster)
    rightRoute_internallyDisjoint_leafCluster := by
      intro x hx
      have hxc : x ∈ S.selectedBelow c := by simpa [hbelow] using hx
      have hclusterSub :
          Tsys.cluster x ⊆ S.subtreeRegion c :=
        S.cluster_subset_subtreeRegion_of_mem
          (S.selectedBelow_subset_descendants c hxc)
      apply E.right_internal_of_trivial_glue
      · exact C.leftRoute_internallyDisjoint_leafCluster x hxc
      · exact C.rightRoute_internallyDisjoint_leafCluster x hxc
      · intro i hi
        by_cases hxcEq : x = c
        · subst x
          exact C.leftRoute_trivial_of_root_selected
            (S.selectedBelow_subset_leaves c hxc) i
        · exact False.elim
            (Finset.disjoint_left.mp (Tsys.cluster_disjoint hxcEq)
              hi
              (D.childIncoming_subset
                (C.leftAnchor_subset (C.leftRoute.target_mem i)) |>
                  Tsys.interface_subset_cluster c v hvc.symm))
      · intro i hi
        by_cases hxcEq : x = c
        · subst x
          exact C.rightRoute_trivial_of_root_selected
            (S.selectedBelow_subset_leaves c hxc) i
        · exact False.elim
            (Finset.disjoint_left.mp (Tsys.cluster_disjoint hxcEq)
              hi
              (D.childIncoming_subset
                (C.rightAnchor_subset (C.rightRoute.target_mem i)) |>
                  Tsys.interface_subset_cluster c v hvc.symm))
      · intro i z hz hzCluster
        exact hDinternal i hz (hclusterSub hzCluster)
    leftRoute_trivial_of_root_selected := by
      intro hv
      have hcMem :
          c ∈ children Tsys.meta_isTree S.root v :=
        (mem_children Tsys.meta_isTree S.root v c).2 hc
      exact False.elim (by
        rw [S.children_eq_empty_of_mem_leaves hv] at hcMem
        simpa using hcMem)
    rightRoute_trivial_of_root_selected := by
      intro hv
      have hcMem :
          c ∈ children Tsys.meta_isTree S.root v :=
        (mem_children Tsys.meta_isTree S.root v c).2 hc
      exact False.elim (by
        rw [S.children_eq_empty_of_mem_leaves hv] at hcMem
        simpa using hcMem)
    outerRoutes_disjoint := E.routes_disjoint
    connectors_stayIn := by
      intro i hi j x hx
      apply S.subtreeRegion_mono_child hc
      exact C.connectors_stayIn (Fin.cast hcard i) (by
          change i.1 + 1 < (S.selectedBelow c).card
          rw [← hcard]
          exact hi) j
        (by simpa [Psys] using hx)
    leftRoute_disjoint_connectors := by
      intro i hi
      apply E.left_disjoint_old (Psys.connector i hi).toPathPacking
      · intro j x hx
        exact C.connectors_stayIn (Fin.cast hcard i) (by
            change i.1 + 1 < (S.selectedBelow c).card
            rw [← hcard]
            exact hi) j
          (by simpa [Psys] using hx)
      · simpa [Psys] using
          C.leftRoute_disjoint_connectors (Fin.cast hcard i) (by
            change i.1 + 1 < (S.selectedBelow c).card
            rw [← hcard]
            exact hi)
      · simpa [Psys] using
          C.rightRoute_disjoint_connectors (Fin.cast hcard i) (by
            change i.1 + 1 < (S.selectedBelow c).card
            rw [← hcard]
            exact hi)
    rightRoute_disjoint_connectors := by
      intro i hi
      apply E.right_disjoint_old (Psys.connector i hi).toPathPacking
      · intro j x hx
        exact C.connectors_stayIn (Fin.cast hcard i) (by
            change i.1 + 1 < (S.selectedBelow c).card
            rw [← hcard]
            exact hi) j
          (by simpa [Psys] using hx)
      · simpa [Psys] using
          C.leftRoute_disjoint_connectors (Fin.cast hcard i) (by
            change i.1 + 1 < (S.selectedBelow c).card
            rw [← hcard]
            exact hi)
      · simpa [Psys] using
          C.rightRoute_disjoint_connectors (Fin.cast hcard i) (by
            change i.1 + 1 < (S.selectedBelow c).card
            rw [← hcard]
            exact hi) }⟩

/-- Reverse a routed DFS state.  This normalizes every two-child merge so that
the consumed bridge reserve is the right reserve of the first child and the
left reserve of the second child. -/
noncomputable def Theorem46RoutedDfsState.reverse
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v : Fin m} {A : Finset V}
    (C : Theorem46RoutedDfsState (w := w) S v A) :
    Theorem46RoutedDfsState (w := w) S v A := by
  classical
  let n := (S.selectedBelow v).card
  let P := C.system.reverse
  let O :
      Fin n → {x : Fin m // x ∈ S.selectedBelow v} :=
    fun i => C.leafOrder i.rev
  have hPfirst :
      P.toPathOfSetsSystem.firstIndex.rev =
        C.system.toPathOfSetsSystem.lastIndex := by
    apply Fin.ext
    simp [P, n]
  have hPlast :
      P.toPathOfSetsSystem.lastIndex.rev =
        C.system.toPathOfSetsSystem.firstIndex := by
    apply Fin.ext
    have hn := C.system.length_pos
    simp [P, n]
    omega
  refine {
    active := C.active
    system := P
    leafOrder := O
    leafOrder_bijective := ?_
    cluster_eq := ?_
    leftReserve := C.rightReserve
    rightReserve := C.leftReserve
    leftAmbient := C.rightAmbient
    rightAmbient := C.leftAmbient
    leftAnchor := C.rightAnchor
    rightAnchor := C.leftAnchor
    leftRoute := C.rightRoute
    rightRoute := C.leftRoute
    leftAnchor_subset := C.rightAnchor_subset
    rightAnchor_subset := C.leftAnchor_subset
    leftAmbient_subset_leaf := ?_
    rightAmbient_subset_leaf := ?_
    leftAmbient_nodeWellLinked := ?_
    rightAmbient_nodeWellLinked := ?_
    outerAmbient_eq_of_singleton := ?_
    outerAmbient_linked_of_singleton := ?_
    leftReserve_subset_ambient := C.rightReserve_subset_ambient
    rightReserve_subset_ambient := C.leftReserve_subset_ambient
    leftReserve_disjoint_firstRight := ?_
    rightReserve_disjoint_lastLeft := ?_
    first_left_subset_ambient := ?_
    first_right_subset_ambient := ?_
    last_left_subset_ambient := ?_
    last_right_subset_ambient := ?_
    leftReserve_subset_leaf := ?_
    rightReserve_subset_leaf := ?_
    left_nails_subset := ?_
    right_nails_subset := ?_
    left_reserve_count := C.right_reserve_count
    right_reserve_count := C.left_reserve_count
    leftRoute_staysIn := C.rightRoute_staysIn
    rightRoute_staysIn := C.leftRoute_staysIn
    leftRoute_internallyDisjoint_leafCluster :=
      C.rightRoute_internallyDisjoint_leafCluster
    rightRoute_internallyDisjoint_leafCluster :=
      C.leftRoute_internallyDisjoint_leafCluster
    leftRoute_trivial_of_root_selected :=
      C.rightRoute_trivial_of_root_selected
    rightRoute_trivial_of_root_selected :=
      C.leftRoute_trivial_of_root_selected
    outerRoutes_disjoint := ?_
    connectors_stayIn := ?_
    leftRoute_disjoint_connectors := ?_
    rightRoute_disjoint_connectors := ?_ }
  · exact C.leafOrder_bijective.comp Fin.rev_bijective
  · intro i
    simpa [P, O] using C.cluster_eq i.rev
  · simpa [P, O, hPfirst] using C.rightAmbient_subset_leaf
  · simpa [P, O, hPlast] using C.leftAmbient_subset_leaf
  · simpa [P, O, hPfirst] using C.rightAmbient_nodeWellLinked
  · simpa [P, O, hPlast] using C.leftAmbient_nodeWellLinked
  · intro h
    have h' :
        C.system.toPathOfSetsSystem.firstIndex =
          C.system.toPathOfSetsSystem.lastIndex := by
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp [P, n] at hv ⊢
      omega
    exact (C.outerAmbient_eq_of_singleton h').symm
  · intro h L R hL hR hdisj
    have h' :
        C.system.toPathOfSetsSystem.firstIndex =
          C.system.toPathOfSetsSystem.lastIndex := by
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp [P, n] at hv ⊢
      omega
    have hlink :=
      C.outerAmbient_linked_of_singleton h' hR hL hdisj.symm
    simpa [P, O, hPfirst, hPlast, h'] using
      StrongPathOfSetsSystem.nodeLinkedIn_symm_public hlink
  · simpa [P, hPfirst] using C.rightReserve_disjoint_lastLeft.symm
  · simpa [P, hPlast] using C.leftReserve_disjoint_firstRight.symm
  · simpa [P, hPfirst] using C.last_right_subset_ambient
  · simpa [P, hPfirst] using C.last_left_subset_ambient
  · simpa [P, hPlast] using C.first_right_subset_ambient
  · simpa [P, hPlast] using C.first_left_subset_ambient
  · simpa [P, O, hPfirst] using C.rightReserve_subset_leaf
  · simpa [P, O, hPlast] using C.leftReserve_subset_leaf
  · simpa [P, hPfirst] using C.right_nails_subset
  · simpa [P, hPlast] using C.left_nails_subset
  · intro i j
    exact GraphPath.nodeDisjoint_symm (C.outerRoutes_disjoint j i)
  · intro i hi j x hx
    let k : Fin n := ⟨n - 2 - i.1, by
      have hn := C.system.length_pos
      dsimp [n]
      omega⟩
    have hk : k.1 + 1 < n := by
      dsimp [k]
      have hn := C.system.length_pos
      dsimp [n] at hn ⊢
      omega
    exact C.connectors_stayIn k hk j (by
      simpa [P, StrongPathOfSetsSystem.reverse, k,
        GraphPath.reverse_vertexSet] using hx)
  · intro i hi a b
    let k : Fin n := ⟨n - 2 - i.1, by
      have hn := C.system.length_pos
      dsimp [n]
      omega⟩
    have hk : k.1 + 1 < n := by
      dsimp [k]
      have hn := C.system.length_pos
      dsimp [n] at hn ⊢
      omega
    have h := C.rightRoute_disjoint_connectors k hk a b
    simpa [P, StrongPathOfSetsSystem.reverse, k,
      GraphPath.NodeDisjoint] using h
  · intro i hi a b
    let k : Fin n := ⟨n - 2 - i.1, by
      have hn := C.system.length_pos
      dsimp [n]
      omega⟩
    have hk : k.1 + 1 < n := by
      dsimp [k]
      have hn := C.system.length_pos
      dsimp [n] at hn ⊢
      omega
    have h := C.leftRoute_disjoint_connectors k hk a b
    simpa [P, StrongPathOfSetsSystem.reverse, k,
      GraphPath.NodeDisjoint] using h

end RoutedDfsInvariant

/-- The output of one Lemma 2.19 application, split into the paths with the
prescribed small-family origins and the retained large-family origins. -/
structure Lemma219SplitData
    (large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T) where
  rerouted : EndpointCleanPathPacking G (U₁ ∪ U₂) T
  rerouted_card : rerouted.card = large.card
  small_origins : U₂ ⊆ rerouted.sourceSet
  retainedOrigins : Finset V
  retainedOrigins_eq : retainedOrigins = rerouted.sourceSet ∩ U₁
  retained_count :
    retainedOrigins.card + small.card = large.card
  support :
    rerouted.toPathPacking.edgeSet ⊆
      large.toPathPacking.edgeSet ∪ small.toPathPacking.edgeSet
  retained_path_original :
    ∀ i : rerouted.Index,
      (rerouted.path i).source ∈ U₁ →
        ∃ r : large.Index,
          (rerouted.path i).vertexSet = (large.path r).vertexSet

/-- The rerouted subfamily starting at all prescribed small-family origins. -/
noncomputable def Lemma219SplitData.smallPart
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small) :
    EndpointCleanPathPacking G (U₁ ∪ U₂) T :=
  D.rerouted.restrictSources U₂

@[simp] theorem Lemma219SplitData.smallPart_card
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small) :
    D.smallPart.card = U₂.card :=
  D.rerouted.restrictSources_card U₂ D.small_origins

@[simp] theorem Lemma219SplitData.smallPart_sourceSet
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small) :
    D.smallPart.sourceSet = U₂ :=
  D.rerouted.restrictSources_sourceSet_eq U₂ D.small_origins

/-- The paths retained from the large origin class. -/
noncomputable def Lemma219SplitData.retainedPart
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small) :
    EndpointCleanPathPacking G (U₁ ∪ U₂) T :=
  D.rerouted.restrictSources D.retainedOrigins

@[simp] theorem Lemma219SplitData.retainedPart_card
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small) :
    D.retainedPart.card = D.retainedOrigins.card := by
  apply D.rerouted.restrictSources_card D.retainedOrigins
  rw [D.retainedOrigins_eq]
  exact Finset.inter_subset_left

@[simp] theorem Lemma219SplitData.retainedPart_sourceSet
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small) :
    D.retainedPart.sourceSet = D.retainedOrigins := by
  apply D.rerouted.restrictSources_sourceSet_eq D.retainedOrigins
  rw [D.retainedOrigins_eq]
  exact Finset.inter_subset_left

/-- Every path in the retained part is literally one of the original large
paths (at the level of vertex sets). -/
theorem Lemma219SplitData.retainedPart_path_original
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small)
    (i : D.retainedPart.Index) :
    ∃ r : large.Index,
      (D.retainedPart.path i).vertexSet = (large.path r).vertexSet := by
  apply D.retained_path_original i.1
  have hiRet := (Finset.mem_filter.mp i.2).2
  have hsub : D.retainedOrigins ⊆ U₁ := by
    rw [D.retainedOrigins_eq]
    exact Finset.inter_subset_right
  exact hsub hiRet

/-- The prescribed small-origin subfamily stays in the union of the two input
families, as required for the second Lemma 2.19 application. -/
theorem Lemma219SplitData.smallPart_edgeSet_subset
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small) :
    D.smallPart.toPathPacking.edgeSet ⊆
      large.toPathPacking.edgeSet ∪ small.toPathPacking.edgeSet := by
  intro e he
  apply D.support
  rcases D.smallPart.toPathPacking.mem_edgeSet.mp he with ⟨i, hi⟩
  exact D.rerouted.toPathPacking.mem_edgeSet.mpr
    ⟨i.1, by simpa [Lemma219SplitData.smallPart,
      EndpointCleanPathPacking.restrictSources,
      EndpointCleanPathPacking.restrictIndexSet] using hi⟩

/-- Every rerouted path stays in the union of the two input path families.
This vertex form includes the possible zero-edge endpoint case and is the
form needed to preserve disjointness in the second rerouting. -/
theorem Lemma219SplitData.rerouted_path_vertexSet_subset
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small)
    (hlargeSources : large.sourceSet = U₁)
    (hsmallSources : small.sourceSet = U₂)
    (i : D.rerouted.Index) :
    (D.rerouted.path i).vertexSet ⊆
      large.toPathPacking.vertexSet ∪ small.toPathPacking.vertexSet := by
  classical
  intro x hx
  by_cases hst :
      (D.rerouted.path i).source = (D.rerouted.path i).target
  · have hxSource :=
      GraphPath.eq_source_of_source_eq_target_of_mem_vertexSet
        (D.rerouted.path i) hst hx
    have hsourceUnion :
        (D.rerouted.path i).source ∈ U₁ ∪ U₂ :=
      (D.rerouted.endpoint_clean i).source_mem
    rcases Finset.mem_union.mp hsourceUnion with hU₁ | hU₂
    · have hmemLarge :
          (D.rerouted.path i).source ∈ large.sourceSet := by
        simpa [hlargeSources] using hU₁
      rcases large.exists_index_source_eq_of_mem_sourceSet hmemLarge with
        ⟨j, hj⟩
      apply Finset.mem_union_left
      apply large.toPathPacking.mem_vertexSet.mpr
      refine ⟨j, ?_⟩
      simpa [hxSource, hj] using
        GraphPath.source_mem_vertexSet (large.path j)
    · have hmemSmall :
          (D.rerouted.path i).source ∈ small.sourceSet := by
        simpa [hsmallSources] using hU₂
      rcases small.exists_index_source_eq_of_mem_sourceSet hmemSmall with
        ⟨j, hj⟩
      apply Finset.mem_union_right
      apply small.toPathPacking.mem_vertexSet.mpr
      refine ⟨j, ?_⟩
      simpa [hxSource, hj] using
        GraphPath.source_mem_vertexSet (small.path j)
  · rcases
      (D.rerouted.path i)
        |>.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target hst hx
      with ⟨e, he, hxe⟩
    have heUnion : e ∈
        large.toPathPacking.edgeSet ∪ small.toPathPacking.edgeSet := by
      apply D.support
      exact D.rerouted.toPathPacking.mem_edgeSet.mpr ⟨i, he⟩
    rcases Finset.mem_union.mp heUnion with heLarge | heSmall
    · rcases large.toPathPacking.mem_edgeSet.mp heLarge with ⟨j, hej⟩
      apply Finset.mem_union_left
      apply large.toPathPacking.mem_vertexSet.mpr
      refine ⟨j, ?_⟩
      rcases Sym2.mem_iff_exists.mp hxe with ⟨y, hey⟩
      subst e
      exact (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        (large.path j) hej).1
    · rcases small.toPathPacking.mem_edgeSet.mp heSmall with ⟨j, hej⟩
      apply Finset.mem_union_right
      apply small.toPathPacking.mem_vertexSet.mpr
      refine ⟨j, ?_⟩
      rcases Sym2.mem_iff_exists.mp hxe with ⟨y, hey⟩
      subst e
      exact (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        (small.path j) hej).1

/-- The retained and prescribed-small parts of one rerouted packing are
mutually node-disjoint. -/
theorem Lemma219SplitData.retainedPart_mutuallyNodeDisjoint_smallPart
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small)
    (hdisjoint : Disjoint U₁ U₂) :
    D.retainedPart.toPathPacking.MutuallyNodeDisjoint
      D.smallPart.toPathPacking := by
  intro i j
  apply D.rerouted.node_disjoint
  intro hij
  have hiU₁ :
      (D.rerouted.path i.1).source ∈ U₁ :=
    by
      have hiRet := (Finset.mem_filter.mp i.2).2
      have hsub : D.retainedOrigins ⊆ U₁ := by
        rw [D.retainedOrigins_eq]
        exact Finset.inter_subset_right
      exact hsub hiRet
  have hjU₂ :
      (D.rerouted.path j.1).source ∈ U₂ :=
    (Finset.mem_filter.mp j.2).2
  exact Finset.disjoint_left.mp hdisjoint hiU₁ (by
    simpa [hij] using hjU₂)

/-- The original large-family paths selected by the retained origins. -/
noncomputable def Lemma219SplitData.originalRetainedPart
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small) :
    EndpointCleanPathPacking G (U₁ ∪ U₂) T :=
  large.restrictSources D.retainedOrigins

@[simp] theorem Lemma219SplitData.originalRetainedPart_sourceSet
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small)
    (hlargeSources : large.sourceSet = U₁) :
    D.originalRetainedPart.sourceSet = D.retainedOrigins := by
  apply large.restrictSources_sourceSet_eq
  rw [D.retainedOrigins_eq, hlargeSources]
  exact Finset.inter_subset_right

/-- The rerouted small-family destinations avoid the destinations of all
original large paths selected by the retained origins.  This is the endpoint
separation needed to reattach the untouched first-hit prefixes in Theorem
4.6. -/
theorem Lemma219SplitData.smallPart_targetSet_disjoint_originalRetainedPart
    {large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (D : Lemma219SplitData large small)
    (hlargeSources : large.sourceSet = U₁)
    (hdisjoint : Disjoint U₁ U₂) :
    Disjoint D.smallPart.targetSet D.originalRetainedPart.targetSet := by
  classical
  rw [Finset.disjoint_left]
  intro x hxSmall hxLarge
  rcases D.smallPart.exists_index_target_eq_of_mem_targetSet hxSmall with
    ⟨i, hi⟩
  rcases D.originalRetainedPart.exists_index_target_eq_of_mem_targetSet
      hxLarge with ⟨j, hj⟩
  have hjSourceRet :
      (large.path j.1).source ∈ D.retainedOrigins :=
    (Finset.mem_filter.mp j.2).2
  have hjSourcePart :
      (large.path j.1).source ∈ D.retainedPart.sourceSet := by
    simpa [D.retainedPart_sourceSet] using hjSourceRet
  rcases D.retainedPart.exists_index_source_eq_of_mem_sourceSet
      hjSourcePart with ⟨k, hk⟩
  rcases D.retainedPart_path_original k with ⟨r, hr⟩
  have hkSourceU₁ :
      (D.retainedPart.path k).source ∈ U₁ := by
    have hkRet :
        (D.retainedPart.path k).source ∈ D.retainedOrigins := by
      simpa [D.retainedPart_sourceSet] using
        D.retainedPart.source_mem_sourceSet k
    have hsub : D.retainedOrigins ⊆ U₁ := by
      rw [D.retainedOrigins_eq]
      exact Finset.inter_subset_right
    exact hsub hkRet
  have hkSourceEqR :
      (D.retainedPart.path k).source = (large.path r).source := by
    apply (large.endpoint_clean r).left_eq_source
    · rw [← hr]
      exact GraphPath.source_mem_vertexSet (D.retainedPart.path k)
    · exact Finset.mem_union_left _ hkSourceU₁
  have hrj : r = j.1 := by
    apply large.source_injective
    exact hkSourceEqR.symm.trans hk
  have hxRetained :
      x ∈ (D.retainedPart.path k).vertexSet := by
    rw [hr, hrj]
    have hjTarget :
        (large.path j.1).target = x := by
      simpa [Lemma219SplitData.originalRetainedPart,
        EndpointCleanPathPacking.restrictSources,
        EndpointCleanPathPacking.restrictIndexSet] using hj
    simpa [hjTarget] using
      GraphPath.target_mem_vertexSet (large.path j.1)
  have hxSmallPath :
      x ∈ (D.smallPart.path i).vertexSet := by
    have hiTarget : (D.smallPart.path i).target = x := hi
    simpa [hiTarget] using GraphPath.target_mem_vertexSet (D.smallPart.path i)
  exact Finset.disjoint_left.mp
    (D.retainedPart_mutuallyNodeDisjoint_smallPart hdisjoint k i)
    hxRetained hxSmallPath

/-- One source-faithful application of Lemma 2.19, with the two useful
subfamilies exposed. -/
theorem exists_lemma219SplitData
    (large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T)
    (hlargeSources : large.sourceSet = U₁)
    (hsmallSources : small.sourceSet = U₂)
    (hdisjoint : Disjoint U₁ U₂)
    (hcard : small.card ≤ large.card) :
    Nonempty (Lemma219SplitData large small) := by
  rcases exists_lemma219_rerouting large small hlargeSources hsmallSources
      hdisjoint hcard with
    ⟨R, hRcard, hU₂, hcount, hsupport, horiginal⟩
  exact ⟨{
    rerouted := R
    rerouted_card := hRcard
    small_origins := hU₂
    retainedOrigins := R.sourceSet ∩ U₁
    retainedOrigins_eq := rfl
    retained_count := hcount
    support := hsupport
    retained_path_original := horiginal }⟩

/-! ## Lemma 2.19 without an endpoint-clean input hypothesis -/

open ChekuriChuzhoyPendantVertex

/-- Source-faithful Lemma 2.19 after adding and then stripping the artificial
degree-one origins used in the paper's Appendix A.3 proof.

The input families need only be perfect packings.  Their paths may pass
through origins of the other family; the fresh pendant copies remove exactly
that mismatch. -/
structure GeneralLemma219SplitData
    {X₁ A₁ X₂ A₂ C K : Finset V}
    (large : PerfectPathPacking G X₁ A₁)
    (small : PerfectPathPacking G X₂ A₂) where
  retainedSources : Finset V
  retainedTargets : Finset V
  retainedSources_subset : retainedSources ⊆ X₁
  retainedTargets_subset : retainedTargets ⊆ A₁
  retained_count :
    retainedSources.card + small.card = large.card
  retainedInside :
    PerfectPathPacking G retainedSources retainedTargets
  retainedInside_path_subset :
    ∀ i : retainedInside.Index,
      (retainedInside.path i).vertexSet ⊆
        large.toPathPacking.vertexSet
  reroutedTargets : Finset V
  reroutedTargets_subset : reroutedTargets ⊆ C
  reroutedSmall :
    PerfectPathPacking G X₂ reroutedTargets
  reroutedSmall_card : reroutedSmall.card = small.card
  retainedInside_mutuallyNodeDisjoint_reroutedSmall :
    retainedInside.toPathPacking.MutuallyNodeDisjoint
      reroutedSmall.toPathPacking
  reroutedSmall_path_subset :
    ∀ i : reroutedSmall.Index,
      (reroutedSmall.path i).vertexSet ⊆
        large.toPathPacking.vertexSet ∪
          small.toPathPacking.vertexSet
  reroutedSmall_staysIn :
    reroutedSmall.toPathPacking.StaysIn K
  reroutedSmall_internallyDisjoint_targetRegion :
    reroutedSmall.toPathPacking.InternallyDisjointFromSet C
  target_disjoint :
    Disjoint reroutedTargets retainedTargets

/-- The artificial-source form of Lemma 2.19. -/
theorem exists_generalLemma219SplitData
    {X₁ A₁ X₂ A₂ C K : Finset V}
    (large : PerfectPathPacking G X₁ A₁)
    (small : PerfectPathPacking G X₂ A₂)
    (hX : Disjoint X₁ X₂)
    (hA₁C : A₁ ⊆ C) (hA₂C : A₂ ⊆ C)
    (hX₁C : Disjoint X₁ C) (hX₂C : Disjoint X₂ C)
    (hlargeInternal :
      large.toPathPacking.InternallyDisjointFromSet C)
    (hsmallInternal :
      small.toPathPacking.InternallyDisjointFromSet C)
    (hlargeStay : large.toPathPacking.StaysIn K)
    (hsmallStay : small.toPathPacking.StaysIn K)
    (hcard : small.card ≤ large.card) :
    Nonempty
      (GeneralLemma219SplitData
        (C := C) (K := K) large small) := by
  classical
  let Z := X₁ ∪ X₂
  have hX₁Z : X₁ ⊆ Z := Finset.subset_union_left
  have hX₂Z : X₂ ⊆ Z := Finset.subset_union_right
  let L₁ := leavesOf (X := Z) X₁ hX₁Z
  let L₂ := leavesOf (X := Z) X₂ hX₂Z
  let oldC := oldImage (X := Z) C
  let oldK := oldImage (X := Z) K
  let P₁ :=
    prependLeafSourcesPerfectPathPacking (X := Z) hX₁Z large
  let P₂ :=
    prependLeafSourcesPerfectPathPacking (X := Z) hX₂Z small
  have hP₁stay :
      P₁.toPathPacking.StaysIn (L₁ ∪ oldK) := by
    simpa [P₁, L₁, oldK] using
      prependLeafSourcesPerfectPathPacking_staysIn_region
        hX₁Z large hlargeStay
  have hP₂stay :
      P₂.toPathPacking.StaysIn (L₂ ∪ oldK) := by
    simpa [P₂, L₂, oldK] using
      prependLeafSourcesPerfectPathPacking_staysIn_region
        hX₂Z small hsmallStay
  have hL₁L₂ : Disjoint L₁ L₂ := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    rcases Finset.mem_image.mp hz₁ with ⟨x, _hx, hzx⟩
    rcases Finset.mem_image.mp hz₂ with ⟨y, _hy, hzy⟩
    have hxy : x.1 = y.1 := by
      rw [← hzx] at hzy
      injection hzy with hsub
      exact (congrArg (fun q : {x : V // x ∈ Z} => q.1) hsub).symm
    exact Finset.disjoint_left.mp hX x.2 (by simpa [hxy] using y.2)
  have hP₁avoidL₂ :
      ∀ i : P₁.Index, Disjoint (P₁.path i).vertexSet L₂ := by
    intro i
    rw [Finset.disjoint_left]
    intro z hz hz₂
    rcases Finset.mem_union.mp (hP₁stay i hz) with hz₁ | hzOld
    · exact Finset.disjoint_left.mp hL₁L₂ hz₁ hz₂
    · exact Finset.disjoint_left.mp
        (leavesOf_disjoint_oldImage (X := Z) X₂ K hX₂Z)
        hz₂ hzOld
  have hP₂avoidL₁ :
      ∀ i : P₂.Index, Disjoint (P₂.path i).vertexSet L₁ := by
    intro i
    rw [Finset.disjoint_left]
    intro z hz hz₁
    rcases Finset.mem_union.mp (hP₂stay i hz) with hz₂ | hzOld
    · exact Finset.disjoint_left.mp hL₁L₂ hz₁ hz₂
    · exact Finset.disjoint_left.mp
        (leavesOf_disjoint_oldImage (X := Z) X₁ K hX₁Z)
        hz₁ hzOld
  have hP₁target :
      oldImage (X := Z) A₁ ⊆ oldC := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact mem_oldImage.mpr (hA₁C hx)
  have hP₂target :
      oldImage (X := Z) A₂ ⊆ oldC := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact mem_oldImage.mpr (hA₂C hx)
  have hL₁oldC : Disjoint L₁ oldC :=
    leavesOf_disjoint_oldImage (X := Z) X₁ C hX₁Z
  have hL₂oldC : Disjoint L₂ oldC :=
    leavesOf_disjoint_oldImage (X := Z) X₂ C hX₂Z
  have hP₁internal :
      P₁.toPathPacking.InternallyDisjointFromSet oldC := by
    simpa [P₁, oldC] using
      prependLeafSourcesPerfectPathPacking_internallyDisjoint_oldImage
        hX₁Z large hlargeInternal hX₁C
  have hP₂internal :
      P₂.toPathPacking.InternallyDisjointFromSet oldC := by
    simpa [P₂, oldC] using
      prependLeafSourcesPerfectPathPacking_internallyDisjoint_oldImage
        hX₂Z small hsmallInternal hX₂C
  let largeEC :
      EndpointCleanPathPacking
        (graph (X := Z) G) (L₁ ∪ L₂) oldC :=
    EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion
      P₁ hP₁avoidL₂ hP₁target hL₁oldC hP₁internal
  let smallEC :
      EndpointCleanPathPacking
        (graph (X := Z) G) (L₁ ∪ L₂) oldC :=
    (EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion
      P₂ hP₂avoidL₁ hP₂target hL₂oldC hP₂internal).swapSourceUnion
  have hlargeSource : largeEC.sourceSet = L₁ := by
    simpa [largeEC] using
      EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion_sourceSet
        P₁ hP₁avoidL₂ hP₁target hL₁oldC hP₁internal
  have hsmallSource : smallEC.sourceSet = L₂ := by
    dsimp [smallEC]
    exact
      EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion_sourceSet
        P₂ hP₂avoidL₁ hP₂target hL₂oldC hP₂internal
  let D := Classical.choice
    (exists_lemma219SplitData largeEC smallEC
      hlargeSource hsmallSource hL₁L₂
      (by simpa [largeEC, smallEC, P₁, P₂] using hcard))
  let S := D.smallPart
  have hSsource :
      S.toPathPacking.sourceSet = L₂ := by
    simpa [S, D, hsmallSource] using D.smallPart_sourceSet
  let SP₀ := S.toPathPacking.toPerfectUsedTerminals
  let SP :
      PerfectPathPacking (graph (X := Z) G) L₂
        S.toPathPacking.targetSet :=
    SP₀.copyTerminals hSsource rfl
  have hSPtargetOld :
      S.toPathPacking.targetSet ⊆
        oldRegion (V := V) (X := Z) := by
    intro z hz
    have hzC : z ∈ oldC :=
      S.toPathPacking.targetSet_subset_right hz
    exact Finset.mem_image.mpr
      (by
        rcases Finset.mem_image.mp hzC with ⟨x, hx, rfl⟩
        exact ⟨x, by simp, rfl⟩)
  let Q :=
    ChekuriChuzhoyPendantVertex.PerfectPathPacking.projectSourceLeaves
      hX₂Z SP hSPtargetOld
  have hDretLeaves :
      D.retainedOrigins ⊆ leaves (V := V) (X := Z) := by
    rw [D.retainedOrigins_eq]
    exact (Finset.inter_subset_right.trans
      (leavesOf_subset_leaves X₁ hX₁Z))
  let Rsrc := baseSet D.retainedOrigins hDretLeaves
  have hRsrcZ : Rsrc ⊆ Z :=
    baseSet_subset D.retainedOrigins hDretLeaves
  have hLeavesRsrc :
      leavesOf (X := Z) Rsrc hRsrcZ = D.retainedOrigins := by
    apply Finset.eq_of_subset_of_card_le
    · exact leavesOf_baseSet_subset
        D.retainedOrigins hDretLeaves Rsrc Finset.Subset.rfl
    · rw [leavesOf_card, baseSet_card]
  let Rtarget :=
    projectOldSet (X := Z) D.originalRetainedPart.targetSet
  let RP₀ :=
    D.originalRetainedPart.toPathPacking.toPerfectUsedTerminals
  let RP :
      PerfectPathPacking (graph (X := Z) G)
        (leavesOf (X := Z) Rsrc hRsrcZ)
        D.originalRetainedPart.targetSet :=
    RP₀.copyTerminals (by
      simpa [hLeavesRsrc] using
        D.originalRetainedPart_sourceSet hlargeSource) (by simp [RP₀])
  have hRPtargetOld :
      D.originalRetainedPart.targetSet ⊆
        oldRegion (V := V) (X := Z) := by
    intro z hz
    have hzC : z ∈ oldC :=
      D.originalRetainedPart.targetSet_subset_right hz
    rcases Finset.mem_image.mp hzC with ⟨x, hx, rfl⟩
    exact mem_oldImage.mpr (by simp)
  let Rinside :=
    ChekuriChuzhoyPendantVertex.PerfectPathPacking.projectSourceLeaves
      hRsrcZ RP hRPtargetOld
  let Qtarget :=
    projectOldSet (X := Z) S.toPathPacking.targetSet
  have hQsupport :
      ∀ i : Q.Index,
        (Q.path i).vertexSet ⊆
          large.toPathPacking.vertexSet ∪
            small.toPathPacking.vertexSet := by
    intro i x hx
    have hxLift :
        old (X := Z) x ∈ (SP.path i).vertexSet :=
      ChekuriChuzhoyPendantVertex.PerfectPathPacking.projectSourceLeaves_path_lifts
        hX₂Z SP hSPtargetOld i x hx
    have hxS :
        old (X := Z) x ∈ (S.path i).vertexSet := by
      simpa [SP, SP₀, PathPacking.toPerfectUsedTerminals,
        PerfectPathPacking.copyTerminals,
        EndpointCleanPathPacking.toPathPacking_orient_path] using hxLift
    have hxD :
        old (X := Z) x ∈ (D.rerouted.path i.1).vertexSet := by
      simpa [S, Lemma219SplitData.smallPart,
        EndpointCleanPathPacking.restrictSources,
        EndpointCleanPathPacking.restrictIndexSet] using hxS
    have hxUnion :=
      D.rerouted_path_vertexSet_subset
        hlargeSource hsmallSource i.1 hxD
    rcases Finset.mem_union.mp hxUnion with hx₁ | hx₂
    · rcases largeEC.toPathPacking.mem_vertexSet.mp hx₁ with ⟨j, hj⟩
      exact Finset.mem_union_left _
        (prependLeafSourcesPerfectPathPacking_old_vertex_mem_originalVertexSet
          hX₁Z large j (by simpa [largeEC, P₁] using hj))
    · rcases smallEC.toPathPacking.mem_vertexSet.mp hx₂ with ⟨j, hj⟩
      exact Finset.mem_union_right _
        (prependLeafSourcesPerfectPathPacking_old_vertex_mem_originalVertexSet
          hX₂Z small j (by simpa [smallEC, P₂] using hj))
  refine ⟨{
    retainedSources := Rsrc
    retainedTargets := Rtarget
    retainedSources_subset := ?_
    retainedTargets_subset := ?_
    retained_count := ?_
    retainedInside := Rinside
    retainedInside_path_subset := ?_
    reroutedTargets := Qtarget
    reroutedTargets_subset := ?_
    reroutedSmall := Q
    reroutedSmall_card := ?_
    retainedInside_mutuallyNodeDisjoint_reroutedSmall := ?_
    reroutedSmall_path_subset := hQsupport
    reroutedSmall_staysIn := ?_
    reroutedSmall_internallyDisjoint_targetRegion := ?_
    target_disjoint := ?_ }⟩
  · exact baseSet_subset_of_subset_leavesOf
      D.retainedOrigins _ X₁ hX₁Z (by
        rw [D.retainedOrigins_eq]
        exact Finset.inter_subset_right)
  · intro x hx
    have hxOld :
        old (X := Z) x ∈ D.originalRetainedPart.targetSet :=
      mem_projectOldSet.mp hx
    rcases
        D.originalRetainedPart.exists_index_target_eq_of_mem_targetSet hxOld
      with ⟨i, hi⟩
    have hi' :
        (largeEC.path i.1).target = old (X := Z) x := by
      simpa [Lemma219SplitData.originalRetainedPart,
        EndpointCleanPathPacking.restrictSources,
        EndpointCleanPathPacking.restrictIndexSet] using hi
    have htarget :
        (largeEC.path i.1).target ∈ oldImage (X := Z) A₁ := by
      simpa [largeEC, P₁] using P₁.target_mem i.1
    exact mem_oldImage.mp (hi' ▸ htarget)
  · calc
      Rsrc.card + small.card =
          D.retainedOrigins.card + small.card := by
            simp [Rsrc, baseSet_card]
      _ = D.retainedOrigins.card + smallEC.card := by
            simp [smallEC, P₂]
      _ = largeEC.card := D.retained_count
      _ = large.card := by simp [largeEC, P₁]
  · intro i x hx
    have hxLift :
        old (X := Z) x ∈ (RP.path i).vertexSet :=
      ChekuriChuzhoyPendantVertex.PerfectPathPacking.projectSourceLeaves_path_lifts
        hRsrcZ RP hRPtargetOld i x hx
    have hxD :
        old (X := Z) x ∈
          (D.originalRetainedPart.path i).vertexSet := by
      simpa [RP, RP₀, PathPacking.toPerfectUsedTerminals,
        PerfectPathPacking.copyTerminals,
        EndpointCleanPathPacking.toPathPacking_orient_path] using hxLift
    have hxLarge :
        old (X := Z) x ∈ (largeEC.path i.1).vertexSet := by
      simpa [Lemma219SplitData.originalRetainedPart,
        EndpointCleanPathPacking.restrictSources,
        EndpointCleanPathPacking.restrictIndexSet] using hxD
    exact
      prependLeafSourcesPerfectPathPacking_old_vertex_mem_originalVertexSet
        hX₁Z large i.1 (by simpa [largeEC, P₁] using hxLarge)
  · intro x hx
    have hxOld :
        old (X := Z) x ∈ S.toPathPacking.targetSet :=
      mem_projectOldSet.mp hx
    have hxC : old (X := Z) x ∈ oldC :=
      S.toPathPacking.targetSet_subset_right hxOld
    exact mem_oldImage.mp hxC
  · calc
      Q.card = SP.card := rfl
      _ = S.card := by simp [SP, SP₀]
      _ = L₂.card := D.smallPart_card
      _ = X₂.card := leavesOf_card X₂ hX₂Z
      _ = small.card := small.card_eq_left_card.symm
  · intro i j
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxR hxQ
    have hxRLift :
        old (X := Z) x ∈ (RP.path i).vertexSet :=
      ChekuriChuzhoyPendantVertex.PerfectPathPacking.projectSourceLeaves_path_lifts
        hRsrcZ RP hRPtargetOld i x hxR
    have hxQLift :
        old (X := Z) x ∈ (SP.path j).vertexSet :=
      ChekuriChuzhoyPendantVertex.PerfectPathPacking.projectSourceLeaves_path_lifts
        hX₂Z SP hSPtargetOld j x hxQ
    have hxD :
        old (X := Z) x ∈
          (D.originalRetainedPart.path i).vertexSet := by
      simpa [RP, RP₀, PathPacking.toPerfectUsedTerminals,
        PerfectPathPacking.copyTerminals,
        EndpointCleanPathPacking.toPathPacking_orient_path] using hxRLift
    have hxS :
        old (X := Z) x ∈ (S.path j).vertexSet := by
      simpa [SP, SP₀, PathPacking.toPerfectUsedTerminals,
        PerfectPathPacking.copyTerminals,
        EndpointCleanPathPacking.toPathPacking_orient_path] using hxQLift
    have hiSourceRet :
        (largeEC.path i.1).source ∈ D.retainedOrigins :=
      (Finset.mem_filter.mp i.2).2
    have hiSourcePart :
        (largeEC.path i.1).source ∈ D.retainedPart.sourceSet := by
      simpa [D.retainedPart_sourceSet] using hiSourceRet
    rcases D.retainedPart.exists_index_source_eq_of_mem_sourceSet
        hiSourcePart with ⟨k, hk⟩
    rcases D.retainedPart_path_original k with ⟨r, hr⟩
    have hkSourceU₁ :
        (D.retainedPart.path k).source ∈ L₁ := by
      have hkRet :
          (D.retainedPart.path k).source ∈ D.retainedOrigins := by
        simpa [D.retainedPart_sourceSet] using
          D.retainedPart.source_mem_sourceSet k
      rw [D.retainedOrigins_eq] at hkRet
      exact Finset.inter_subset_right hkRet
    have hkSourceEqR :
        (D.retainedPart.path k).source =
          (largeEC.path r).source := by
      apply (largeEC.endpoint_clean r).left_eq_source
      · rw [← hr]
        exact GraphPath.source_mem_vertexSet (D.retainedPart.path k)
      · exact Finset.mem_union_left _ hkSourceU₁
    have hri : r = i.1 := by
      apply largeEC.source_injective
      exact hkSourceEqR.symm.trans hk
    have hxRetained :
        old (X := Z) x ∈ (D.retainedPart.path k).vertexSet := by
      rw [hr, hri]
      simpa [Lemma219SplitData.originalRetainedPart,
        EndpointCleanPathPacking.restrictSources,
        EndpointCleanPathPacking.restrictIndexSet] using hxD
    exact Finset.disjoint_left.mp
      (D.retainedPart_mutuallyNodeDisjoint_smallPart
        hL₁L₂ k j) hxRetained hxS
  · intro i x hx
    rcases Finset.mem_union.mp (hQsupport i hx) with hxLarge | hxSmall
    · rcases large.toPathPacking.mem_vertexSet.mp hxLarge with ⟨j, hj⟩
      exact hlargeStay j hj
    · rcases small.toPathPacking.mem_vertexSet.mp hxSmall with ⟨j, hj⟩
      exact hsmallStay j hj
  · intro i x hx hxC
    have hxLift :
        old (X := Z) x ∈ (SP.path i).vertexSet :=
      ChekuriChuzhoyPendantVertex.PerfectPathPacking.projectSourceLeaves_path_lifts
        hX₂Z SP hSPtargetOld i x hx
    have hxS :
        old (X := Z) x ∈ (S.path i).vertexSet := by
      simpa [SP, SP₀, PathPacking.toPerfectUsedTerminals,
        PerfectPathPacking.copyTerminals,
        EndpointCleanPathPacking.toPathPacking_orient_path] using hxLift
    have heq :=
      (S.endpoint_clean i).right_eq_target hxS (mem_oldImage.mpr hxC)
    apply Or.inr
    apply old_injective (V := V) (X := Z)
    calc
      old (X := Z) x = (S.path i).target := heq
      _ = (SP.path i).target := by
        simp [SP, SP₀, PathPacking.toPerfectUsedTerminals,
          PerfectPathPacking.copyTerminals,
          EndpointCleanPathPacking.toPathPacking_orient_path]
      _ = old (X := Z) (Q.path i).target := by
        exact
          (ChekuriChuzhoyPendantVertex.PerfectPathPacking.projectSourceLeaves_target_lifts
            hX₂Z SP hSPtargetOld i).symm
  · apply projectOldSet_disjoint
    simpa [S] using
      D.smallPart_targetSet_disjoint_originalRetainedPart
        hlargeSource hL₁L₂

/-- The source-faithful output of the two Lemma 2.19 applications at a
branching cluster.  The two retained origin sets are the new reserves, while
the perfect bridge has `4*w` paths and is supported by the two incoming route
families plus the current cluster. -/
structure TwoChildReroutingData
    {X₁ A₁ X₂ A₂ K : Finset V}
    (P₁ : PerfectPathPacking G X₁ A₁)
    (P₂ : PerfectPathPacking G X₂ A₂)
    (w : ℕ) where
  retainedFirst : Finset V
  retainedSecond : Finset V
  retainedFirst_subset : retainedFirst ⊆ X₁
  retainedSecond_subset : retainedSecond ⊆ X₂
  retainedFirst_count : retainedFirst.card + 4 * w = P₁.card
  retainedSecond_count : retainedSecond.card + 4 * w = P₂.card
  retainedFirstTarget : Finset V
  retainedSecondTarget : Finset V
  retainedFirstTarget_subset : retainedFirstTarget ⊆ A₁
  retainedSecondTarget_subset : retainedSecondTarget ⊆ A₂
  retainedFirstInside :
    PerfectPathPacking G retainedFirst retainedFirstTarget
  retainedSecondInside :
    PerfectPathPacking G retainedSecond retainedSecondTarget
  retainedFirstInside_path_subset :
    ∀ i : retainedFirstInside.Index,
      (retainedFirstInside.path i).vertexSet ⊆
        P₁.toPathPacking.vertexSet
  retainedSecondInside_path_subset :
    ∀ i : retainedSecondInside.Index,
      (retainedSecondInside.path i).vertexSet ⊆
        P₂.toPathPacking.vertexSet
  bridgeSource : Finset V
  bridgeTarget : Finset V
  bridgeSource_subset : bridgeSource ⊆ A₁
  bridgeTarget_subset : bridgeTarget ⊆ A₂
  bridge : PerfectPathPacking G bridgeSource bridgeTarget
  bridge_card : bridge.card = 4 * w
  bridgeSource_disjoint_retainedFirstTarget :
    Disjoint bridgeSource retainedFirstTarget
  bridgeTarget_disjoint_retainedSecondTarget :
    Disjoint bridgeTarget retainedSecondTarget
  bridge_internallyDisjoint_firstTarget :
    bridge.toPathPacking.InternallyDisjointFromSet A₁
  bridge_internallyDisjoint_secondTarget :
    bridge.toPathPacking.InternallyDisjointFromSet A₂
  bridge_path_subset :
    ∀ i : bridge.Index,
      (bridge.path i).vertexSet ⊆
        P₁.toPathPacking.vertexSet ∪
          (P₂.toPathPacking.vertexSet ∪ K)

/-- The two source-faithful Lemma 2.19 applications from Section 4.2.
`P₁` and `P₂` are the four reserve routes grouped by child. -/
theorem exists_twoChildReroutingData
    {X₁ A₁ X₂ A₂ K : Finset V}
    (P₁ : PerfectPathPacking G X₁ A₁)
    (P₂ : PerfectPathPacking G X₂ A₂)
    (w : ℕ)
    (hPdisj :
      P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    (hlink : NodeLinkedIn G K A₁ A₂)
    (hX₁K : Disjoint X₁ K) (hX₂K : Disjoint X₂ K)
    (hfour₁ : 4 * w ≤ P₁.card)
    (hfour₂ : 4 * w ≤ P₂.card) :
    Nonempty (TwoChildReroutingData (K := K) P₁ P₂ w) := by
  classical
  have hA₁A₂ :
      Disjoint A₁ A₂ :=
    PerfectPathPacking.target_disjoint_of_mutuallyNodeDisjoint
      P₁ P₂ hPdisj
  have hA₁card : A₁.card = P₁.card := P₁.card_eq_right_card.symm
  have hA₂card : A₂.card = P₂.card := P₂.card_eq_right_card.symm
  obtain ⟨A₄, hA₄, hA₄card⟩ :=
    Finset.exists_subset_card_eq (s := A₁)
      (by simpa [hA₁card] using hfour₁)
  obtain ⟨B₄, hB₄, hB₄card⟩ :=
    Finset.exists_subset_card_eq (s := A₂)
      (by simpa [hA₂card] using hfour₂)
  have hA₄B₄ : Disjoint A₄ B₄ := hA₁A₂.mono hA₄ hB₄
  obtain ⟨Q, hQcard, hQstay⟩ :=
    NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      (hlink.mono_terminals hA₄ hB₄)
      (hA₄card.trans hB₄card.symm)
  let H₁ := Classical.choice
    (PerfectPathPacking.exists_firstHitData (C := A₁) Q.reverse (by
      intro x hx
      simpa using hA₄ hx))
  have hQavoidX₁ :
      ∀ i : H₁.packing.Index,
        Disjoint (H₁.packing.path i).vertexSet X₁ := by
    intro i
    rw [Finset.disjoint_left]
    intro x hx hxX
    rcases H₁.path_vertexSet_subset i with ⟨j, hj⟩
    have hxQ : x ∈ (Q.path j).vertexSet := by
      simpa using hj hx
    exact Finset.disjoint_left.mp hX₁K hxX (hQstay j hxQ)
  have hB₄A₁ : Disjoint B₄ A₁ := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    exact Finset.disjoint_left.mp hA₁A₂ hxA (hB₄ hxB)
  let small₁ :
      EndpointCleanPathPacking G (X₁ ∪ B₄) A₁ :=
    (EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion
      H₁.packing hQavoidX₁ H₁.hit_subset hB₄A₁
        H₁.packing_internallyDisjoint).swapSourceUnion
  have hP₁avoidB₄ :
      ∀ i : P₁.Index, Disjoint (P₁.path i).vertexSet B₄ := by
    intro i
    rw [Finset.disjoint_left]
    intro x hx hxB
    have hxA₂ : x ∈ A₂ := hB₄ hxB
    rcases P₂.target_bijective.2 ⟨x, hxA₂⟩ with ⟨j, hj⟩
    have hxP₂ : x ∈ (P₂.path j).vertexSet := by
      have : (P₂.path j).target = x := congrArg Subtype.val hj
      simpa [this] using GraphPath.target_mem_vertexSet (P₂.path j)
    exact Finset.disjoint_left.mp (hPdisj i j) hx hxP₂
  let large₁ :
      EndpointCleanPathPacking G (X₁ ∪ B₄) A₁ :=
    EndpointCleanPathPacking.ofPerfectWithExtraSources P₁ hP₁avoidB₄
  have hsmall₁source : small₁.sourceSet = B₄ := by
    simpa [small₁] using
      EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion_sourceSet
        H₁.packing hQavoidX₁ H₁.hit_subset hB₄A₁
          H₁.packing_internallyDisjoint
  have hlarge₁source : large₁.sourceSet = X₁ := by
    simpa [large₁] using
      EndpointCleanPathPacking.ofPerfectWithExtraSources_sourceSet
        P₁ hP₁avoidB₄
  have hsmall₁card : small₁.card = 4 * w := by
    calc
      small₁.card = H₁.packing.card := rfl
      _ = Q.reverse.card := H₁.packing_card
      _ = Q.card := rfl
      _ = A₄.card := hQcard
      _ = 4 * w := hA₄card
  have hX₁B₄ : Disjoint X₁ B₄ := by
    apply Finset.disjoint_of_subset_right
      (hB₄.trans hlink.2.1)
    exact hX₁K
  let D₁ := Classical.choice
    (exists_lemma219SplitData large₁ small₁
      hlarge₁source hsmall₁source
      hX₁B₄
      (by simpa [hsmall₁card, large₁] using hfour₁))
  let S₁ := D₁.smallPart
  let R₁ := S₁.toPathPacking.toPerfectUsedTerminals.reverse
  have hR₁target : S₁.toPathPacking.sourceSet ⊆ A₂ := by
    intro x hx
    have hxB₄ : x ∈ B₄ := by
      simpa [S₁, D₁, hsmall₁source] using hx
    exact hB₄ hxB₄
  let H₂ := Classical.choice
    (PerfectPathPacking.exists_firstHitData (C := A₂) R₁ hR₁target)
  have hR₂sourceA₁ : S₁.toPathPacking.targetSet ⊆ A₁ := by
    intro x hx
    have hxS₁target : x ∈ S₁.targetSet := by simpa using hx
    exact S₁.targetSet_subset_right hxS₁target
  have hH₂avoidX₂ :
      ∀ i : H₂.packing.Index,
        Disjoint (H₂.packing.path i).vertexSet X₂ := by
    intro i
    rw [Finset.disjoint_left]
    intro x hx hxX₂
    rcases H₂.path_vertexSet_subset i with ⟨j, hj⟩
    have hxS₁ : x ∈ (S₁.path j).vertexSet := by
      have hxR₁ : x ∈ (R₁.path j).vertexSet := hj hx
      simpa [R₁, PathPacking.toPerfectUsedTerminals,
        PathPacking.orient_path_vertexSet] using hxR₁
    have hxD₁ : x ∈ (D₁.rerouted.path j.1).vertexSet := by
      simpa [S₁, Lemma219SplitData.smallPart,
        EndpointCleanPathPacking.restrictSources,
        EndpointCleanPathPacking.restrictIndexSet] using hxS₁
    have hxUnion :=
      D₁.rerouted_path_vertexSet_subset
        hlarge₁source hsmall₁source j.1 hxD₁
    rcases Finset.mem_union.mp hxUnion with hxLarge | hxSmall
    · rcases large₁.toPathPacking.mem_vertexSet.mp hxLarge with ⟨a, ha⟩
      have hxP₁ : x ∈ (P₁.path a).vertexSet := by
        simpa [large₁,
          EndpointCleanPathPacking.ofPerfectWithExtraSources] using ha
      rcases P₂.source_bijective.2 ⟨x, hxX₂⟩ with ⟨b, hb⟩
      have hxP₂ : x ∈ (P₂.path b).vertexSet := by
        have : (P₂.path b).source = x := congrArg Subtype.val hb
        simpa [this] using GraphPath.source_mem_vertexSet (P₂.path b)
      exact Finset.disjoint_left.mp (hPdisj a b) hxP₁ hxP₂
    · rcases small₁.toPathPacking.mem_vertexSet.mp hxSmall with ⟨a, ha⟩
      rcases H₁.path_vertexSet_subset a with ⟨b, hb⟩
      have hxQ : x ∈ (Q.path b).vertexSet := by
        simpa [small₁,
          EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion]
          using hb ha
      exact Finset.disjoint_left.mp hX₂K hxX₂ (hQstay b hxQ)
  have hSource₂A₂ :
      Disjoint S₁.toPathPacking.targetSet A₂ :=
    Finset.disjoint_of_subset_left hR₂sourceA₁ hA₁A₂
  let small₂ :
      EndpointCleanPathPacking G
        (X₂ ∪ S₁.toPathPacking.targetSet) A₂ :=
    (EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion
      H₂.packing hH₂avoidX₂ H₂.hit_subset hSource₂A₂
        H₂.packing_internallyDisjoint).swapSourceUnion
  have hP₂avoidSource :
      ∀ i : P₂.Index,
        Disjoint (P₂.path i).vertexSet S₁.toPathPacking.targetSet := by
    intro i
    rw [Finset.disjoint_left]
    intro x hxP₂ hxS
    have hxA₁ : x ∈ A₁ := hR₂sourceA₁ hxS
    rcases P₁.target_bijective.2 ⟨x, hxA₁⟩ with ⟨j, hj⟩
    have hxP₁ : x ∈ (P₁.path j).vertexSet := by
      have : (P₁.path j).target = x := congrArg Subtype.val hj
      simpa [this] using GraphPath.target_mem_vertexSet (P₁.path j)
    exact Finset.disjoint_left.mp (hPdisj j i) hxP₁ hxP₂
  let large₂ :
      EndpointCleanPathPacking G
        (X₂ ∪ S₁.toPathPacking.targetSet) A₂ :=
    EndpointCleanPathPacking.ofPerfectWithExtraSources P₂ hP₂avoidSource
  have hsmall₂source :
      small₂.sourceSet = S₁.toPathPacking.targetSet := by
    simpa [small₂] using
      EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion_sourceSet
        H₂.packing hH₂avoidX₂ H₂.hit_subset hSource₂A₂
          H₂.packing_internallyDisjoint
  have hlarge₂source : large₂.sourceSet = X₂ := by
    simpa [large₂] using
      EndpointCleanPathPacking.ofPerfectWithExtraSources_sourceSet
        P₂ hP₂avoidSource
  have hsmall₂card : small₂.card = 4 * w := by
    calc
      small₂.card = H₂.packing.card := by simp [small₂]
      _ = R₁.card := H₂.packing_card
      _ = S₁.card := by simp [R₁]
      _ = B₄.card := by simp [S₁, D₁]
      _ = 4 * w := hB₄card
  have hX₂S₁target :
      Disjoint X₂ S₁.toPathPacking.targetSet := by
    apply Finset.disjoint_of_subset_right
      (hR₂sourceA₁.trans hlink.1)
    exact hX₂K
  let D₂ := Classical.choice
    (exists_lemma219SplitData large₂ small₂
      hlarge₂source hsmall₂source
      hX₂S₁target
      (by simpa [hsmall₂card, large₂] using hfour₂))
  let bridge :=
    D₂.smallPart.toPathPacking.toPerfectUsedTerminals
  let RF₀ :=
    D₁.originalRetainedPart.toPathPacking.toPerfectUsedTerminals
  let RF :
      PerfectPathPacking G D₁.retainedOrigins
        D₁.originalRetainedPart.targetSet :=
    RF₀.copyTerminals (by
      simpa using
        D₁.originalRetainedPart_sourceSet hlarge₁source) (by simp)
  let RS₀ :=
    D₂.originalRetainedPart.toPathPacking.toPerfectUsedTerminals
  let RS :
      PerfectPathPacking G D₂.retainedOrigins
        D₂.originalRetainedPart.targetSet :=
    RS₀.copyTerminals (by
      simpa using
        D₂.originalRetainedPart_sourceSet hlarge₂source) (by simp)
  exact ⟨{
    retainedFirst := D₁.retainedOrigins
    retainedSecond := D₂.retainedOrigins
    retainedFirst_subset := by
      rw [D₁.retainedOrigins_eq]
      exact Finset.inter_subset_right
    retainedSecond_subset := by
      rw [D₂.retainedOrigins_eq]
      exact Finset.inter_subset_right
    retainedFirst_count := by
      simpa [hsmall₁card, large₁] using D₁.retained_count
    retainedSecond_count := by
      simpa [hsmall₂card, large₂] using D₂.retained_count
    retainedFirstTarget := D₁.originalRetainedPart.targetSet
    retainedSecondTarget := D₂.originalRetainedPart.targetSet
    retainedFirstTarget_subset :=
      D₁.originalRetainedPart.targetSet_subset_right
    retainedSecondTarget_subset :=
      D₂.originalRetainedPart.targetSet_subset_right
    retainedFirstInside := RF
    retainedSecondInside := RS
    retainedFirstInside_path_subset := by
      intro i x hx
      have hxD :
          x ∈ (D₁.originalRetainedPart.path i).vertexSet := by
        simpa [RF, RF₀, PathPacking.toPerfectUsedTerminals,
          PerfectPathPacking.copyTerminals,
          EndpointCleanPathPacking.toPathPacking_orient_path] using hx
      have hxP :
          x ∈ (large₁.path i.1).vertexSet := by
        simpa [Lemma219SplitData.originalRetainedPart,
          EndpointCleanPathPacking.restrictSources,
          EndpointCleanPathPacking.restrictIndexSet] using hxD
      exact large₁.toPathPacking.path_vertexSet_subset_vertexSet i.1
        (by simpa [large₁,
          EndpointCleanPathPacking.ofPerfectWithExtraSources] using hxP)
    retainedSecondInside_path_subset := by
      intro i x hx
      have hxD :
          x ∈ (D₂.originalRetainedPart.path i).vertexSet := by
        simpa [RS, RS₀, PathPacking.toPerfectUsedTerminals,
          PerfectPathPacking.copyTerminals,
          EndpointCleanPathPacking.toPathPacking_orient_path] using hx
      have hxP :
          x ∈ (large₂.path i.1).vertexSet := by
        simpa [Lemma219SplitData.originalRetainedPart,
          EndpointCleanPathPacking.restrictSources,
          EndpointCleanPathPacking.restrictIndexSet] using hxD
      exact large₂.toPathPacking.path_vertexSet_subset_vertexSet i.1
        (by simpa [large₂,
          EndpointCleanPathPacking.ofPerfectWithExtraSources] using hxP)
    bridgeSource := D₂.smallPart.toPathPacking.sourceSet
    bridgeTarget := D₂.smallPart.toPathPacking.targetSet
    bridgeSource_subset := by
      intro x hx
      have : x ∈ D₂.smallPart.sourceSet := by
        simpa [bridge] using hx
      have hxH₂ : x ∈ S₁.toPathPacking.targetSet := by
        simpa [D₂.smallPart_sourceSet, hsmall₂source] using this
      exact hR₂sourceA₁ hxH₂
    bridgeTarget_subset := by
      intro x hx
      have : x ∈ D₂.smallPart.targetSet := by
        simpa [bridge] using hx
      exact D₂.smallPart.targetSet_subset_right this
    bridge := bridge
    bridge_card := by
      calc
        bridge.card = D₂.smallPart.card := by simp [bridge]
        _ = S₁.toPathPacking.targetSet.card := D₂.smallPart_card
        _ = small₂.sourceSet.card := by rw [hsmall₂source]
        _ = small₂.card := EndpointCleanPathPacking.sourceSet_card small₂
        _ = 4 * w := hsmall₂card
    bridgeSource_disjoint_retainedFirstTarget := by
      have h :=
        D₁.smallPart_targetSet_disjoint_originalRetainedPart
          hlarge₁source hX₁B₄
      simpa [bridge, D₂.smallPart_sourceSet, hsmall₂source,
        S₁, EndpointCleanPathPacking.toPathPacking_sourceSet] using h
    bridgeTarget_disjoint_retainedSecondTarget := by
      have h :=
        D₂.smallPart_targetSet_disjoint_originalRetainedPart
          hlarge₂source hX₂S₁target
      simpa [bridge, EndpointCleanPathPacking.toPathPacking_targetSet] using h
    bridge_internallyDisjoint_firstTarget := by
      intro i x hx hxA₁
      have hxD₂ : x ∈ (D₂.rerouted.path i.1).vertexSet := by
        simpa [bridge, Lemma219SplitData.smallPart,
          EndpointCleanPathPacking.restrictSources,
          EndpointCleanPathPacking.restrictIndexSet,
          PathPacking.toPerfectUsedTerminals] using hx
      have hxUnion :=
        D₂.rerouted_path_vertexSet_subset
          hlarge₂source hsmall₂source i.1 hxD₂
      rcases Finset.mem_union.mp hxUnion with hxLarge | hxSmall
      · rcases large₂.toPathPacking.mem_vertexSet.mp hxLarge with ⟨j, hj⟩
        have hxP₂ : x ∈ (P₂.path j).vertexSet := by
          simpa [large₂,
            EndpointCleanPathPacking.ofPerfectWithExtraSources] using hj
        rcases P₁.target_bijective.2 ⟨x, hxA₁⟩ with ⟨k, hk⟩
        have hxP₁ : x ∈ (P₁.path k).vertexSet := by
          have hk' : (P₁.path k).target = x := congrArg Subtype.val hk
          simpa [hk'] using GraphPath.target_mem_vertexSet (P₁.path k)
        exact False.elim
          (Finset.disjoint_left.mp (hPdisj k j) hxP₁ hxP₂)
      · rcases small₂.toPathPacking.mem_vertexSet.mp hxSmall with ⟨j, hj⟩
        change H₂.packing.Index at j
        rcases H₂.path_vertexSet_subset j with ⟨a, ha⟩
        have hxS₁ : x ∈ (S₁.path a).vertexSet := by
          simpa [small₂,
            EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion,
            R₁, PathPacking.toPerfectUsedTerminals] using ha hj
        have hxS₁Target :
            x = (S₁.path a).target :=
          (S₁.endpoint_clean a).right_eq_target hxS₁ hxA₁
        have hxSourceClass :
            x ∈ S₁.toPathPacking.targetSet := by
          apply Finset.mem_image.mpr
          refine ⟨a, by simp, ?_⟩
          simpa [EndpointCleanPathPacking.toPathPacking_orient_path]
            using hxS₁Target.symm
        have hxAmbient :
            x ∈ X₂ ∪ S₁.toPathPacking.targetSet :=
          Finset.mem_union_right _ hxSourceClass
        apply Or.inl
        simpa [bridge, Lemma219SplitData.smallPart,
          EndpointCleanPathPacking.restrictSources,
          EndpointCleanPathPacking.restrictIndexSet,
          PathPacking.toPerfectUsedTerminals] using
          ((D₂.rerouted.endpoint_clean i.1).left_eq_source hxD₂ hxAmbient)
    bridge_internallyDisjoint_secondTarget := by
      intro i x hx hxA₂
      have hxD₂ : x ∈ (D₂.rerouted.path i.1).vertexSet := by
        simpa [bridge, Lemma219SplitData.smallPart,
          EndpointCleanPathPacking.restrictSources,
          EndpointCleanPathPacking.restrictIndexSet,
          PathPacking.toPerfectUsedTerminals] using hx
      apply Or.inr
      simpa [bridge, Lemma219SplitData.smallPart,
        EndpointCleanPathPacking.restrictSources,
        EndpointCleanPathPacking.restrictIndexSet,
        PathPacking.toPerfectUsedTerminals] using
        ((D₂.rerouted.endpoint_clean i.1).right_eq_target hxD₂ hxA₂)
    bridge_path_subset := by
      intro i x hx
      have hxD₂ : x ∈ (D₂.rerouted.path i.1).vertexSet := by
        simpa [bridge, Lemma219SplitData.smallPart,
          EndpointCleanPathPacking.restrictSources,
          EndpointCleanPathPacking.restrictIndexSet,
          PathPacking.toPerfectUsedTerminals] using hx
      have hxUnion :=
        D₂.rerouted_path_vertexSet_subset
          hlarge₂source hsmall₂source i.1 hxD₂
      rcases Finset.mem_union.mp hxUnion with hxLarge | hxSmall
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        simpa [large₂,
          EndpointCleanPathPacking.ofPerfectWithExtraSources] using hxLarge
      · rcases small₂.toPathPacking.mem_vertexSet.mp hxSmall with ⟨j, hj⟩
        change H₂.packing.Index at j
        rcases H₂.path_vertexSet_subset j with ⟨a, ha⟩
        have hxS₁ : x ∈ (S₁.path a).vertexSet := by
          simpa [small₂,
            EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion,
            R₁, PathPacking.toPerfectUsedTerminals] using ha hj
        have hxD₁ : x ∈ (D₁.rerouted.path a.1).vertexSet := by
          simpa [S₁, Lemma219SplitData.smallPart,
            EndpointCleanPathPacking.restrictSources,
            EndpointCleanPathPacking.restrictIndexSet] using hxS₁
        have hxUnion₁ :=
          D₁.rerouted_path_vertexSet_subset
            hlarge₁source hsmall₁source a.1 hxD₁
        rcases Finset.mem_union.mp hxUnion₁ with hxP | hxQ
        · exact Finset.mem_union_left _ (by
            simpa [large₁,
              EndpointCleanPathPacking.ofPerfectWithExtraSources] using hxP)
        · apply Finset.mem_union_right
          apply Finset.mem_union_right
          rcases small₁.toPathPacking.mem_vertexSet.mp hxQ with ⟨j, hj⟩
          rcases H₁.path_vertexSet_subset j with ⟨b, hb⟩
          exact hQstay b (by
            simpa [small₁,
              EndpointCleanPathPacking.ofPerfectWithExtraSourcesAndTargetRegion]
              using hb hj) }⟩

/-- If four finite classes carry at least `4*w` objects in total, one class
contains at least `w` objects.  This is the final pigeonhole step of the
two-child merge. -/
theorem exists_fin4_le_of_four_mul_le_sum
    {w : ℕ} (f : Fin 4 → ℕ)
    (h : 4 * w ≤ ∑ i, f i) :
    ∃ i, w ≤ f i := by
  by_contra hn
  push_neg at hn
  have h0 := hn (0 : Fin 4)
  have h1 := hn (1 : Fin 4)
  have h2 := hn (2 : Fin 4)
  have h3 := hn (3 : Fin 4)
  have hsum :
      (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
    rw [Fin.sum_univ_four]
  rw [hsum] at h
  omega

/-- Four-way endpoint pigeonhole, in the exact form used after the two
reroutings. -/
theorem exists_bridge_index_class
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L₁ R₁ L₂ R₂ : Finset V)
    (origin₁ origin₂ : ι → V)
    (horigin₁ : ∀ i, origin₁ i ∈ L₁ ∪ R₁)
    (horigin₂ : ∀ i, origin₂ i ∈ L₂ ∪ R₂)
    {w : ℕ} (hfour : 4 * w ≤ Fintype.card ι) :
    ∃ b₁ b₂ : Bool, ∃ I : Finset ι,
      I.card = w ∧
        ∀ i ∈ I,
          origin₁ i ∈ (if b₁ then L₁ else R₁) ∧
          origin₂ i ∈ (if b₂ then L₂ else R₂) := by
  classical
  let all : Finset ι := Finset.univ
  let p : ι → Prop := fun i => origin₁ i ∈ L₁
  let q : ι → Prop := fun i => origin₂ i ∈ L₂
  let Itt := all.filter fun i => p i ∧ q i
  let Itf := all.filter fun i => p i ∧ ¬ q i
  let Ift := all.filter fun i => ¬ p i ∧ q i
  let Iff := all.filter fun i => ¬ p i ∧ ¬ q i
  have hsum :
      Itt.card + Itf.card + Ift.card + Iff.card =
        Fintype.card ι := by
    have hp :=
      Finset.card_filter_add_card_filter_not (s := all) p
    have hpq :=
      Finset.card_filter_add_card_filter_not
        (s := all.filter p) q
    have hnpq :=
      Finset.card_filter_add_card_filter_not
        (s := all.filter fun i => ¬ p i) q
    have hItt :
        ((all.filter p).filter q) = Itt := by
      ext i
      simp [Itt, p, q, and_assoc]
    have hItf :
        ((all.filter p).filter fun i => ¬ q i) = Itf := by
      ext i
      simp [Itf, p, q, and_assoc]
    have hIft :
        ((all.filter fun i => ¬ p i).filter q) = Ift := by
      ext i
      simp [Ift, p, q, and_assoc]
    have hIff :
        ((all.filter fun i => ¬ p i).filter fun i => ¬ q i) = Iff := by
      ext i
      simp [Iff, p, q, and_assoc]
    have hpq' :
        Itt.card + Itf.card = (all.filter p).card := by
      simpa [hItt, hItf] using hpq
    have hnpq' :
        Ift.card + Iff.card =
          (all.filter fun i => ¬ p i).card := by
      simpa [hIft, hIff] using hnpq
    have hp' :
        (all.filter p).card +
            (all.filter fun i => ¬ p i).card =
          Fintype.card ι := by
      simpa [all] using hp
    omega
  have hlarge :
      w ≤ Itt.card ∨ w ≤ Itf.card ∨
        w ≤ Ift.card ∨ w ≤ Iff.card := by
    omega
  rcases hlarge with htt | htf | hft | hff
  · rcases Finset.exists_subset_card_eq htt with ⟨I, hI, hIcard⟩
    refine ⟨true, true, I, hIcard, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hI hi)).2
  · rcases Finset.exists_subset_card_eq htf with ⟨I, hI, hIcard⟩
    refine ⟨true, false, I, hIcard, ?_⟩
    intro i hi
    have hi' := (Finset.mem_filter.mp (hI hi)).2
    refine ⟨hi'.1, ?_⟩
    rcases Finset.mem_union.mp (horigin₂ i) with hiL | hiR
    · exact False.elim (hi'.2 hiL)
    · exact hiR
  · rcases Finset.exists_subset_card_eq hft with ⟨I, hI, hIcard⟩
    refine ⟨false, true, I, hIcard, ?_⟩
    intro i hi
    have hi' := (Finset.mem_filter.mp (hI hi)).2
    refine ⟨?_, hi'.2⟩
    rcases Finset.mem_union.mp (horigin₁ i) with hiL | hiR
    · exact False.elim (hi'.1 hiL)
    · exact hiR
  · rcases Finset.exists_subset_card_eq hff with ⟨I, hI, hIcard⟩
    refine ⟨false, false, I, hIcard, ?_⟩
    intro i hi
    have hi' := (Finset.mem_filter.mp (hI hi)).2
    constructor
    · rcases Finset.mem_union.mp (horigin₁ i) with hiL | hiR
      · exact False.elim (hi'.1 hiL)
      · exact hiR
    · rcases Finset.mem_union.mp (horigin₂ i) with hiL | hiR
      · exact False.elim (hi'.2 hiL)
      · exact hiR

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
