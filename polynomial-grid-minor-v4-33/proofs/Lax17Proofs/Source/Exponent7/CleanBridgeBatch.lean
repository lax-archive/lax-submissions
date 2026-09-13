import Lax17Proofs.Source.Exponent7.RectangularSection45Input

namespace Lax17Proofs

/-!
# Clean simultaneous bridge batches

Start with node-well-linked anchors on a node-disjoint row family. After
routing two equal halves, trim each path between its last visit to the source
row and its first visit to another selected row. The resulting bridges are
pairwise node-disjoint and internally disjoint from every selected row.

Using “selected row” is essential: the first row met outside the source row
may otherwise lie outside the auxiliary multigraph used by the matching/hub
argument.

The maximum-matching/hub dichotomy gives

`q ≤ 12 * batchSize + 1`,

and hence `q ≤ 13 * batchSize` for a nonempty batch. The additive term accounts
for the possible odd-cardinality endpoint.
-/

namespace SimpleGraph
namespace Exponent7

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- The union of the vertices of the rows whose indices lie in `I`. -/
noncomputable def selectedRowVertexSet
    (R : PathPacking G S T) (I : Finset R.Index) : Finset V :=
  I.biUnion fun r => (R.path r).vertexSet

theorem mem_selectedRowVertexSet
    (R : PathPacking G S T) (I : Finset R.Index) {v : V} :
    v ∈ selectedRowVertexSet R I ↔
      ∃ r ∈ I, v ∈ (R.path r).vertexSet := by
  classical
  simp [selectedRowVertexSet]

theorem path_vertexSet_subset_selectedRowVertexSet
    (R : PathPacking G S T) {I : Finset R.Index}
    {r : R.Index} (hr : r ∈ I) :
    (R.path r).vertexSet ⊆ selectedRowVertexSet R I := by
  intro v hv
  exact (mem_selectedRowVertexSet R I).2 ⟨r, hr, hv⟩

theorem selectedRowVertexSet_insert_erase
    (R : PathPacking G S T) {I : Finset R.Index}
    {r : R.Index} (hr : r ∈ I) :
    selectedRowVertexSet R I =
      (R.path r).vertexSet ∪ selectedRowVertexSet R (I.erase r) := by
  classical
  rw [← Finset.insert_erase hr]
  simp [selectedRowVertexSet]

/-- Choosing one anchor on every row gives an injective anchor map, because
different rows in a path packing are node-disjoint. -/
theorem rowAnchor_injective
    (R : PathPacking G S T) (anchor : R.Index → V)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet) :
    Function.Injective anchor := by
  intro r s hrs
  by_contra hne
  exact Finset.disjoint_left.mp (R.node_disjoint hne)
    (hanchor r) (by simpa [hrs] using hanchor s)

/-- A finite set contains two disjoint subsets of half its cardinality; a
possible odd element is discarded. -/
theorem exists_disjoint_halves
    {α : Type*} [DecidableEq α] (I : Finset α) :
    ∃ U V : Finset α,
      U ⊆ I ∧ V ⊆ I ∧ Disjoint U V ∧
        U.card = I.card / 2 ∧ V.card = I.card / 2 := by
  classical
  obtain ⟨U, hUI, hUcard⟩ :=
    Finset.exists_subset_card_eq (Nat.div_le_self I.card 2)
  have hhalf_le_compl : I.card / 2 ≤ (I \ U).card := by
    rw [Finset.card_sdiff_of_subset hUI, hUcard]
    omega
  obtain ⟨V, hVdiff, hVcard⟩ :=
    Finset.exists_subset_card_eq hhalf_le_compl
  refine ⟨U, V, hUI, ?_, ?_, hUcard, hVcard⟩
  · exact fun x hx => (Finset.mem_sdiff.mp (hVdiff hx)).1
  · rw [Finset.disjoint_left]
    intro x hxU hxV
    exact (Finset.mem_sdiff.mp (hVdiff hxV)).2 hxU

/-- The balanced routing supplied by node-well-linked anchor vertices. -/
structure BalancedAnchorRouting
    (R : PathPacking G S T) (anchor : R.Index → V)
    (I : Finset R.Index) (C : Finset V) where
  U : Finset R.Index
  W : Finset R.Index
  U_subset : U ⊆ I
  W_subset : W ⊆ I
  halves_disjoint : Disjoint U W
  U_card : U.card = I.card / 2
  W_card : W.card = I.card / 2
  routes :
    PerfectPathPacking G (U.image anchor) (W.image anchor)
  routes_card : routes.card = I.card / 2
  routes_stay : routes.toPathPacking.StaysIn C

/-- Node-well-linked anchors route two disjoint halves by a perfect,
node-disjoint path packing. -/
noncomputable def balancedAnchorRouting
    (R : PathPacking G S T) (anchor : R.Index → V)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)
    (I : Finset R.Index) (C : Finset V)
    (hwell :
      NodeWellLinkedIn G C
        ((Finset.univ : Finset R.Index).image anchor)) :
    BalancedAnchorRouting R anchor I C := by
  classical
  let halves := Classical.choose (exists_disjoint_halves I)
  let W := Classical.choose (Classical.choose_spec (exists_disjoint_halves I))
  have hhalves :=
    Classical.choose_spec
      (Classical.choose_spec (exists_disjoint_halves I))
  let U := halves
  have hUI : U ⊆ I := hhalves.1
  have hWI : W ⊆ I := hhalves.2.1
  have hUW : Disjoint U W := hhalves.2.2.1
  have hUcard : U.card = I.card / 2 := hhalves.2.2.2.1
  have hWcard : W.card = I.card / 2 := hhalves.2.2.2.2
  have hinj : Function.Injective anchor :=
    rowAnchor_injective R anchor hanchor
  have hUsub :
      U.image anchor ⊆
        (Finset.univ : Finset R.Index).image anchor := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
  have hWsub :
      W.image anchor ⊆
        (Finset.univ : Finset R.Index).image anchor := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
  have hUWimage : Disjoint (U.image anchor) (W.image anchor) := by
    rw [Finset.disjoint_left]
    intro v hvU hvW
    rcases Finset.mem_image.mp hvU with ⟨r, hrU, hrv⟩
    rcases Finset.mem_image.mp hvW with ⟨s, hsW, hsv⟩
    have hrs : r = s := hinj (hrv.trans hsv.symm)
    exact Finset.disjoint_left.mp hUW hrU (by simpa [hrs] using hsW)
  let routed := Classical.choose (hwell.2 hUsub hWsub hUWimage)
  have hrouted :=
    Classical.choose_spec (hwell.2 hUsub hWsub hUWimage)
  let P := routed
  have hPcard :
      P.card = min (U.image anchor).card (W.image anchor).card := by
    simpa [P, routed] using hrouted.1
  have hPstay : P.StaysIn C := by
    simpa [P, routed] using hrouted.2
  have hUimageCard : (U.image anchor).card = I.card / 2 := by
    rw [Finset.card_image_of_injective]
    · exact hUcard
    · exact hinj
  have hWimageCard : (W.image anchor).card = I.card / 2 := by
    rw [Finset.card_image_of_injective]
    · exact hWcard
    · exact hinj
  have hPcardU : P.card = (U.image anchor).card := by
    simpa [hUimageCard, hWimageCard] using hPcard
  have hPcardW : P.card = (W.image anchor).card := by
    simpa [hUimageCard, hWimageCard] using hPcard
  let Pperfect := P.toPerfectOfCardEq hPcardU hPcardW
  exact
    { U := U
      W := W
      U_subset := hUI
      W_subset := hWI
      halves_disjoint := hUW
      U_card := hUcard
      W_card := hWcard
      routes := Pperfect
      routes_card := by
        simpa [Pperfect, PerfectPathPacking.card,
          PathPacking.toPerfectOfCardEq, PathPacking.card,
          hUimageCard] using hPcardU
      routes_stay := by
        simpa [Pperfect, PathPacking.toPerfectOfCardEq] using
          PathPacking.orient_staysIn hPstay }

namespace BalancedAnchorRouting

variable
    {R : PathPacking G S T} {anchor : R.Index → V}
    {I : Finset R.Index} {C : Finset V}

/-- The routed path whose source is the anchor of `u`. -/
noncomputable def routeIndex
    (B : BalancedAnchorRouting R anchor I C)
    (u : {r : R.Index // r ∈ B.U}) : B.routes.Index :=
  B.routes.indexOfSource
    ⟨anchor u.1, Finset.mem_image.mpr ⟨u.1, u.2, rfl⟩⟩

@[simp] theorem route_source
    (B : BalancedAnchorRouting R anchor I C)
    (u : {r : R.Index // r ∈ B.U}) :
    (B.routes.path (B.routeIndex u)).source = anchor u.1 := by
  exact congrArg Subtype.val
    (B.routes.source_indexOfSource
      ⟨anchor u.1, Finset.mem_image.mpr ⟨u.1, u.2, rfl⟩⟩)

theorem routeIndex_injective
    (B : BalancedAnchorRouting R anchor I C)
    (hanchorInj : Function.Injective anchor) :
    Function.Injective B.routeIndex := by
  intro u v huv
  apply Subtype.ext
  apply hanchorInj
  rw [← B.route_source u, ← B.route_source v, huv]

/-- A single routed path, cleaned between the last source-row hit and the
first hit of another selected row. -/
structure CleanTailBridge
    (B : BalancedAnchorRouting R anchor I C)
    (u : {r : R.Index // r ∈ B.U}) where
  head : R.Index
  head_mem : head ∈ I
  head_ne_tail : head ≠ u.1
  path : GraphPath G
  source_mem_tail :
    path.source ∈ (R.path u.1).vertexSet
  target_mem_head :
    path.target ∈ (R.path head).vertexSet
  internallyDisjoint_selectedRows :
    path.InternallyDisjointFromSet (selectedRowVertexSet R I)
  vertexSet_subset_route :
    path.vertexSet ⊆
      (B.routes.path (B.routeIndex u)).vertexSet

/-- Existence of the cleaned bridge attached to one routed source row. -/
noncomputable def cleanTailBridge
    (B : BalancedAnchorRouting R anchor I C)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)
    (u : {r : R.Index // r ∈ B.U}) :
    B.CleanTailBridge u := by
  classical
  let O : GraphPath G := B.routes.path (B.routeIndex u)
  have huI : u.1 ∈ I := B.U_subset u.2
  have htargetW : O.target ∈ B.W.image anchor :=
    B.routes.target_mem (B.routeIndex u)
  have hwExists :
      ∃ w ∈ B.W, anchor w = O.target :=
    Finset.mem_image.mp htargetW
  let w := Classical.choose hwExists
  have hwSpec := Classical.choose_spec hwExists
  have hwW : w ∈ B.W := hwSpec.1
  have htarget : anchor w = O.target := hwSpec.2
  have hwI : w ∈ I := B.W_subset hwW
  have hwu : w ≠ u.1 := by
    intro h
    exact Finset.disjoint_left.mp B.halves_disjoint u.2
      (by simpa [h] using hwW)
  let otherRows := selectedRowVertexSet R (I.erase u.1)
  have htargetOther : O.target ∈ otherRows := by
    apply (mem_selectedRowVertexSet R (I.erase u.1)).2
    refine ⟨w, Finset.mem_erase.mpr ⟨hwu, hwI⟩, ?_⟩
    simpa [htarget] using hanchor w
  have hsourceTail : O.source ∈ (R.path u.1).vertexSet := by
    simpa [O, B.route_source u] using hanchor u.1
  have hconnects :
      O.Connects (R.path u.1).vertexSet otherRows :=
    Or.inl ⟨hsourceTail, htargetOther⟩
  let P := O.cleanBetweenTerminalSets hconnects
  have hPtargetOther : P.target ∈ otherRows := by
    simpa [P] using O.cleanBetweenTerminalSets_target_mem hconnects
  have hheadExists :
      ∃ head ∈ I.erase u.1,
        P.target ∈ (R.path head).vertexSet :=
    (mem_selectedRowVertexSet R (I.erase u.1)).1 hPtargetOther
  let head := Classical.choose hheadExists
  have hheadSpec := Classical.choose_spec hheadExists
  have hheadErase : head ∈ I.erase u.1 := hheadSpec.1
  have hheadTarget : P.target ∈ (R.path head).vertexSet :=
    hheadSpec.2
  have hrows :
      selectedRowVertexSet R I =
        (R.path u.1).vertexSet ∪ otherRows := by
    simpa [otherRows] using selectedRowVertexSet_insert_erase R huI
  exact
    { head := head
      head_mem := Finset.mem_of_mem_erase hheadErase
      head_ne_tail := (Finset.mem_erase.mp hheadErase).1
      path := P
      source_mem_tail := by
        simpa [P] using O.cleanBetweenTerminalSets_source_mem hconnects
      target_mem_head := hheadTarget
      internallyDisjoint_selectedRows := by
        rw [hrows]
        exact O.cleanBetweenTerminalSets_internallyDisjointFromSet_union
          hconnects
      vertexSet_subset_route := by
        simpa [P, O] using
          O.cleanBetweenTerminalSets_vertexSet_subset hconnects }

/-- The whole family of cleaned source-row bridges. -/
structure CleanTailBridgeFamily
    (B : BalancedAnchorRouting R anchor I C) where
  data : ∀ u : {r : R.Index // r ∈ B.U}, B.CleanTailBridge u

/-- Clean every routed path independently. -/
noncomputable def cleanTailBridgeFamily
    (B : BalancedAnchorRouting R anchor I C)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet) :
    B.CleanTailBridgeFamily where
  data := fun u => B.cleanTailBridge hanchor u

namespace CleanTailBridgeFamily

theorem node_disjoint
    (B : BalancedAnchorRouting R anchor I C)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)
    (F := B.cleanTailBridgeFamily hanchor)
    {u v : {r : R.Index // r ∈ B.U}} (huv : u ≠ v) :
    GraphPath.NodeDisjoint (F.data u).path (F.data v).path := by
  have hinj := rowAnchor_injective R anchor hanchor
  have hrouteNe : B.routeIndex u ≠ B.routeIndex v :=
    fun h => huv (B.routeIndex_injective hinj h)
  exact (B.routes.node_disjoint hrouteNe).mono
    (F.data u).vertexSet_subset_route
    (F.data v).vertexSet_subset_route

theorem target_injective_on_same_head
    (B : BalancedAnchorRouting R anchor I C)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)
    (F := B.cleanTailBridgeFamily hanchor)
    {u v : {r : R.Index // r ∈ B.U}}
    (huv : u ≠ v)
    (hhead : (F.data u).head = (F.data v).head) :
    (F.data u).path.target ≠ (F.data v).path.target := by
  intro htarget
  exact Finset.disjoint_left.mp (node_disjoint B hanchor (F := F) huv)
    (GraphPath.target_mem_vertexSet (F.data u).path)
    (by
      rw [htarget]
      exact GraphPath.target_mem_vertexSet (F.data v).path)

end CleanTailBridgeFamily
end BalancedAnchorRouting

/-! ## Finite endpoint matching -/

/-- A subfamily is support-disjoint when distinct indices have disjoint
finite supports.  This is the finite-set form of a matching and, unlike a
simple graph edge set, retains parallel occurrences. -/
def SupportDisjointFamily
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (M : Finset α) : Prop :=
  (↑M : Set α).Pairwise fun i j => Disjoint (support i) (support j)

theorem supportDisjointFamily_mono
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {support : α → Finset β} {M N : Finset α}
    (hN : SupportDisjointFamily support N) (hMN : M ⊆ N) :
    SupportDisjointFamily support M := by
  intro i hi j hj hij
  exact hN (hMN hi) (hMN hj) hij

theorem supportDisjointFamily_insert
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {support : α → Finset β} {M : Finset α} {i : α}
    (hM : SupportDisjointFamily support M)
    (hi :
      ∀ j ∈ M, j ≠ i →
        Disjoint (support i) (support j)) :
    SupportDisjointFamily support (insert i M) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact (hab rfl).elim
  · exact hi b hb hab.symm
  · exact (hi a ha hab).symm
  · exact hM ha hb hab

/-- Candidate support-disjoint subfamilies of `all`. -/
noncomputable def supportDisjointCandidates
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (all : Finset α) :
    Finset (Finset α) := by
  classical
  exact all.powerset.filter (SupportDisjointFamily support)

@[simp] theorem mem_supportDisjointCandidates
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (all M : Finset α) :
    M ∈ supportDisjointCandidates support all ↔
      M ⊆ all ∧ SupportDisjointFamily support M := by
  classical
  simp [supportDisjointCandidates]

/-- A maximum-cardinality support-disjoint subfamily. -/
noncomputable def maximumSupportDisjointSubfamily
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (all : Finset α) :
    Finset α := by
  classical
  have hne : (supportDisjointCandidates support all).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [SupportDisjointFamily]
  exact Classical.choose
    ((supportDisjointCandidates support all).exists_maximalFor
      Finset.card hne)

theorem maximumSupportDisjointSubfamily_spec
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (all : Finset α) :
    maximumSupportDisjointSubfamily support all ⊆ all ∧
      SupportDisjointFamily support
        (maximumSupportDisjointSubfamily support all) ∧
      ∀ N ⊆ all, SupportDisjointFamily support N →
        N.card ≤
          (maximumSupportDisjointSubfamily support all).card := by
  classical
  have hne : (supportDisjointCandidates support all).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [SupportDisjointFamily]
  have hmax :
      MaximalFor
        (· ∈ supportDisjointCandidates support all)
        Finset.card
        (maximumSupportDisjointSubfamily support all) := by
    unfold maximumSupportDisjointSubfamily
    exact Classical.choose_spec
      ((supportDisjointCandidates support all).exists_maximalFor
        Finset.card hne)
  have hmem :
      maximumSupportDisjointSubfamily support all ∈
        supportDisjointCandidates support all :=
    hmax.1
  have hspec :=
    (mem_supportDisjointCandidates support all
      (maximumSupportDisjointSubfamily support all)).mp hmem
  refine ⟨hspec.1, hspec.2, ?_⟩
  intro N hNall hN
  have hNC :
      N ∈ supportDisjointCandidates support all :=
    (mem_supportDisjointCandidates support all N).mpr
      ⟨hNall, hN⟩
  by_contra hnot
  have hle :
      (maximumSupportDisjointSubfamily support all).card ≤ N.card := by
    omega
  exact hnot (hmax.2 hNC hle)

/-- Maximality forces every occurrence to meet the support used by the
maximum disjoint subfamily. -/
theorem exists_support_overlap_maximum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (all : Finset α)
    {i : α} (hi : i ∈ all) (hsi : (support i).Nonempty) :
    ∃ j ∈ maximumSupportDisjointSubfamily support all,
      ¬ Disjoint (support i) (support j) := by
  classical
  let M := maximumSupportDisjointSubfamily support all
  by_contra hnone
  push_neg at hnone
  have hiM : i ∉ M := by
    intro hiM
    exact hsi.ne_empty (disjoint_self.mp (hnone i hiM))
  have hinsertSubset : insert i M ⊆ all := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact (maximumSupportDisjointSubfamily_spec support all).1 hj
  have hinsertDisjoint :
      SupportDisjointFamily support (insert i M) := by
    apply supportDisjointFamily_insert
    · exact
        (maximumSupportDisjointSubfamily_spec support all).2.1
    · intro j hj hji
      exact hnone j hj
  have hcard :=
    (maximumSupportDisjointSubfamily_spec support all).2.2
      (insert i M) hinsertSubset hinsertDisjoint
  rw [Finset.card_insert_of_notMem hiM] at hcard
  dsimp [M] at hcard
  omega

/-- The union of the supports used by a finite occurrence family. -/
noncomputable def supportFamilyUnion
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (M : Finset α) : Finset β := by
  classical
  exact M.biUnion support

theorem supportFamilyUnion_card_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (M : Finset α) {k : ℕ}
    (hcard : ∀ i ∈ M, (support i).card ≤ k) :
    (supportFamilyUnion support M).card ≤ k * M.card := by
  classical
  calc
    (supportFamilyUnion support M).card ≤
        ∑ i ∈ M, (support i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ M, k :=
      Finset.sum_le_sum fun i hi => hcard i hi
    _ = k * M.card := by simp [Nat.mul_comm]

/-! ## The maximum row-endpoint matching -/

namespace BalancedAnchorRouting.CleanTailBridgeFamily

variable
    {R : PathPacking G S T} {anchor : R.Index → V}
    {I : Finset R.Index} {C : Finset V}
    (B : BalancedAnchorRouting R anchor I C)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)

/-- The two row indices used by one cleaned bridge occurrence. -/
noncomputable def endpointRows
    (F := B.cleanTailBridgeFamily hanchor)
    (u : {r : R.Index // r ∈ B.U}) : Finset R.Index :=
  {u.1, (F.data u).head}

theorem endpointRows_card
    (F := B.cleanTailBridgeFamily hanchor)
    (u : {r : R.Index // r ∈ B.U}) :
    (endpointRows B hanchor (F := F) u).card = 2 := by
  simp [endpointRows, (F.data u).head_ne_tail.symm]

/-- A maximum occurrence matching.  It is indexed by cleaned bridge
occurrences, so opposite parallel bridges are not collapsed. -/
noncomputable def maximumEndpointMatching
    (F := B.cleanTailBridgeFamily hanchor) :
    Finset {r : R.Index // r ∈ B.U} :=
  maximumSupportDisjointSubfamily
    (endpointRows B hanchor (F := F)) Finset.univ

/-- The rows saturated by the maximum occurrence matching. -/
noncomputable def maximumEndpointRows
    (F := B.cleanTailBridgeFamily hanchor) : Finset R.Index :=
  supportFamilyUnion
    (endpointRows B hanchor (F := F))
    (maximumEndpointMatching B hanchor (F := F))

theorem maximumEndpointMatching_disjoint
    (F := B.cleanTailBridgeFamily hanchor) :
    SupportDisjointFamily
      (endpointRows B hanchor (F := F))
      (maximumEndpointMatching B hanchor (F := F)) :=
  (maximumSupportDisjointSubfamily_spec
    (endpointRows B hanchor (F := F)) Finset.univ).2.1

theorem maximumEndpointRows_card_le
    (F := B.cleanTailBridgeFamily hanchor) :
    (maximumEndpointRows B hanchor (F := F)).card ≤
      2 * (maximumEndpointMatching B hanchor (F := F)).card := by
  apply supportFamilyUnion_card_le
  intro u hu
  exact (endpointRows_card B hanchor (F := F) u).le

theorem maximumEndpointRows_subset
    (F := B.cleanTailBridgeFamily hanchor) :
    maximumEndpointRows B hanchor (F := F) ⊆ I := by
  classical
  intro r hr
  rcases Finset.mem_biUnion.mp hr with ⟨u, hu, hru⟩
  have huAll :
      u ∈ (Finset.univ :
        Finset {r : R.Index // r ∈ B.U}) :=
    (maximumSupportDisjointSubfamily_spec
      (endpointRows B hanchor (F := F)) Finset.univ).1 hu
  have hcases : r = u.1 ∨ r = (F.data u).head := by
    simpa [endpointRows] using hru
  rcases hcases with rfl | rfl
  · exact B.U_subset u.2
  · exact (F.data u).head_mem

/-- Every cleaned bridge has a tail or head row saturated by the maximum
matching. -/
theorem tail_mem_or_head_mem_maximumEndpointRows
    (F := B.cleanTailBridgeFamily hanchor)
    (u : {r : R.Index // r ∈ B.U}) :
    u.1 ∈ maximumEndpointRows B hanchor (F := F) ∨
      (F.data u).head ∈
        maximumEndpointRows B hanchor (F := F) := by
  classical
  let support :=
    endpointRows B hanchor (F := F)
  let M := maximumEndpointMatching B hanchor (F := F)
  obtain ⟨j, hjM, hoverlap⟩ :=
    exists_support_overlap_maximum support Finset.univ
      (Finset.mem_univ u)
      (by
        refine ⟨u.1, ?_⟩
        simp [support, endpointRows])
  rw [Finset.not_disjoint_iff] at hoverlap
  rcases hoverlap with ⟨r, hru, hrj⟩
  have hrRows :
      r ∈ maximumEndpointRows B hanchor (F := F) := by
    exact Finset.mem_biUnion.mpr ⟨j, hjM, hrj⟩
  have hru' : r = u.1 ∨ r = (F.data u).head := by
    simpa [support, endpointRows] using hru
  rcases hru' with rfl | rfl
  · exact Or.inl hrRows
  · exact Or.inr hrRows

/-- Hence a bridge whose tail avoids the saturated rows has its head in
them. -/
theorem head_mem_maximumEndpointRows_of_tail_not_mem
    (F := B.cleanTailBridgeFamily hanchor)
    (u : {r : R.Index // r ∈ B.U})
    (hu :
      u.1 ∉ maximumEndpointRows B hanchor (F := F)) :
    (F.data u).head ∈
      maximumEndpointRows B hanchor (F := F) :=
  (tail_mem_or_head_mem_maximumEndpointRows
    B hanchor (F := F) u).resolve_left hu

/-- Cleaned bridges whose tail row is not saturated by the maximum
matching.  Their head rows are necessarily saturated. -/
noncomputable def unsaturatedTails
    (F := B.cleanTailBridgeFamily hanchor) :
    Finset {r : R.Index // r ∈ B.U} :=
  Finset.univ.filter fun u =>
    u.1 ∉ maximumEndpointRows B hanchor (F := F)

@[simp] theorem mem_unsaturatedTails
    (F := B.cleanTailBridgeFamily hanchor)
    (u : {r : R.Index // r ∈ B.U}) :
    u ∈ unsaturatedTails B hanchor (F := F) ↔
      u.1 ∉ maximumEndpointRows B hanchor (F := F) := by
  classical
  simp [unsaturatedTails]

theorem unsaturated_head_mem
    (F := B.cleanTailBridgeFamily hanchor)
    {u : {r : R.Index // r ∈ B.U}}
    (hu : u ∈ unsaturatedTails B hanchor (F := F)) :
    (F.data u).head ∈
      maximumEndpointRows B hanchor (F := F) := by
  exact head_mem_maximumEndpointRows_of_tail_not_mem
    B hanchor (F := F) u
      ((mem_unsaturatedTails B hanchor (F := F) u).1 hu)

/-- At most one routed tail is removed for each saturated row. -/
theorem saturatedTails_card_le_rows
    (F := B.cleanTailBridgeFamily hanchor) :
    ((Finset.univ :
        Finset {r : R.Index // r ∈ B.U}).filter
      (fun u =>
        u.1 ∈ maximumEndpointRows B hanchor (F := F))).card ≤
      (maximumEndpointRows B hanchor (F := F)).card := by
  classical
  let removed :=
    (Finset.univ :
      Finset {r : R.Index // r ∈ B.U}).filter
        (fun u =>
          u.1 ∈ maximumEndpointRows B hanchor (F := F))
  have hcardImage :
      (removed.image (fun u => u.1)).card = removed.card := by
    rw [Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hsub :
      removed.image (fun u => u.1) ⊆
        maximumEndpointRows B hanchor (F := F) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨u, hu, rfl⟩
    exact (Finset.mem_filter.mp hu).2
  rw [← hcardImage]
  exact Finset.card_le_card hsub

/-- The unsaturated tail count loses at most the number of saturated rows. -/
theorem U_card_le_unsaturated_add_rows
    (F := B.cleanTailBridgeFamily hanchor) :
    B.U.card ≤
      (unsaturatedTails B hanchor (F := F)).card +
        (maximumEndpointRows B hanchor (F := F)).card := by
  classical
  let removed :=
    (Finset.univ :
      Finset {r : R.Index // r ∈ B.U}).filter
        (fun u =>
          u.1 ∈ maximumEndpointRows B hanchor (F := F))
  have hpartition :
      (unsaturatedTails B hanchor (F := F)).card +
          removed.card =
        (Finset.univ :
          Finset {r : R.Index // r ∈ B.U}).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext u
      by_cases hp :
          u.1 ∈ maximumEndpointRows B hanchor (F := F)
      · simp [unsaturatedTails, removed, hp]
      · simp [unsaturatedTails, removed, hp]
    · rw [Finset.disjoint_left]
      intro u hu hru
      exact (Finset.mem_filter.mp hu).2
        (Finset.mem_filter.mp hru).2
  have hremoved :
      removed.card ≤
        (maximumEndpointRows B hanchor (F := F)).card := by
    simpa [removed] using
      saturatedTails_card_le_rows B hanchor (F := F)
  simpa using
    (calc
      B.U.card =
          (Finset.univ :
            Finset {r : R.Index // r ∈ B.U}).card := by simp
      _ = (unsaturatedTails B hanchor (F := F)).card +
          removed.card := hpartition.symm
      _ ≤ (unsaturatedTails B hanchor (F := F)).card +
          (maximumEndpointRows B hanchor (F := F)).card :=
        Nat.add_le_add_left hremoved _)

/-- Unsaturated tails routed into one saturated hub row. -/
noncomputable def hubTails
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) :
    Finset {r : R.Index // r ∈ B.U} :=
  (unsaturatedTails B hanchor (F := F)).filter
    fun u => (F.data u).head = c

@[simp] theorem mem_hubTails
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) (u : {r : R.Index // r ∈ B.U}) :
    u ∈ hubTails B hanchor (F := F) c ↔
      u ∈ unsaturatedTails B hanchor (F := F) ∧
        (F.data u).head = c := by
  classical
  simp [hubTails]

/-- The hub fibers partition all unsaturated tails. -/
theorem unsaturated_card_eq_sum_hubTails
    (F := B.cleanTailBridgeFamily hanchor) :
    (unsaturatedTails B hanchor (F := F)).card =
      ∑ c ∈ maximumEndpointRows B hanchor (F := F),
        (hubTails B hanchor (F := F) c).card := by
  classical
  apply Finset.card_eq_sum_card_fiberwise
  intro u hu
  exact unsaturated_head_mem B hanchor (F := F) hu

/-- Number of pairs obtained by pairing consecutive attachments independently
on every saturated hub row. -/
noncomputable def hubPairCount
    (F := B.cleanTailBridgeFamily hanchor) : ℕ :=
  ∑ c ∈ maximumEndpointRows B hanchor (F := F),
    (hubTails B hanchor (F := F) c).card / 2

/-- Pairing within every hub loses at most one tail per hub. -/
theorem unsaturated_card_le_two_mul_hubPairCount_add_rows
    (F := B.cleanTailBridgeFamily hanchor) :
    (unsaturatedTails B hanchor (F := F)).card ≤
      2 * hubPairCount B hanchor (F := F) +
        (maximumEndpointRows B hanchor (F := F)).card := by
  classical
  rw [unsaturated_card_eq_sum_hubTails B hanchor (F := F)]
  calc
    (∑ c ∈ maximumEndpointRows B hanchor (F := F),
        (hubTails B hanchor (F := F) c).card) ≤
        ∑ c ∈ maximumEndpointRows B hanchor (F := F),
          (2 * ((hubTails B hanchor (F := F) c).card / 2) + 1) := by
      exact Finset.sum_le_sum fun c _hc => by omega
    _ = 2 * hubPairCount B hanchor (F := F) +
          (maximumEndpointRows B hanchor (F := F)).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Nat.nsmul_eq_mul, hubPairCount]
      rw [Finset.mul_sum]
      ring

/-- Counting form of the matching/hub dichotomy.  Either the maximum
endpoint matching is large, or the hub pairing contains enough pairs. -/
theorem matching_large_or_hub_count
    (F := B.cleanTailBridgeFamily hanchor) :
    B.U.card ≤
        6 * (maximumEndpointMatching B hanchor (F := F)).card ∨
      B.U.card ≤ 6 * hubPairCount B hanchor (F := F) := by
  by_cases hlarge :
      B.U.card ≤
        6 * (maximumEndpointMatching B hanchor (F := F)).card
  · exact Or.inl hlarge
  · right
    have hrows :=
      maximumEndpointRows_card_le B hanchor (F := F)
    have hU :=
      U_card_le_unsaturated_add_rows B hanchor (F := F)
    have hunsat :=
      unsaturated_card_le_two_mul_hubPairCount_add_rows
        B hanchor (F := F)
    omega

end BalancedAnchorRouting.CleanTailBridgeFamily

/-! ## Bridge-batch output -/

/-- A simultaneous batch of row-to-row bridges.

`usedRows` is exactly the row set from which the bridge endpoints are drawn.
The bridge interiors avoid those rows.  They may use other rows as hubs;
this flexibility is needed by the small-matching branch. -/
structure CleanBridgeBatch
    (R : PathPacking G S T) (I : Finset R.Index) where
  BridgeIndex : Type
  [bridgeFintype : Fintype BridgeIndex]
  [bridgeDecidableEq : DecidableEq BridgeIndex]
  usedRows : Finset R.Index
  usedRows_subset : usedRows ⊆ I
  left : BridgeIndex → R.Index
  right : BridgeIndex → R.Index
  left_mem : ∀ b, left b ∈ usedRows
  right_mem : ∀ b, right b ∈ usedRows
  left_ne_right : ∀ b, left b ≠ right b
  row_pairs_disjoint :
    Pairwise fun b c =>
      Disjoint ({left b, right b} : Finset R.Index)
        ({left c, right c} : Finset R.Index)
  path : BridgeIndex → GraphPath G
  source_mem :
    ∀ b, (path b).source ∈ (R.path (left b)).vertexSet
  target_mem :
    ∀ b, (path b).target ∈ (R.path (right b)).vertexSet
  internallyDisjoint_usedRows :
    ∀ b,
      (path b).InternallyDisjointFromSet
        (selectedRowVertexSet R usedRows)
  node_disjoint :
    Pairwise fun b c => GraphPath.NodeDisjoint (path b) (path c)

namespace CleanBridgeBatch

variable {R : PathPacking G S T} {I : Finset R.Index}

instance (B : CleanBridgeBatch R I) : Fintype B.BridgeIndex :=
  B.bridgeFintype

instance (B : CleanBridgeBatch R I) : DecidableEq B.BridgeIndex :=
  B.bridgeDecidableEq

def card (B : CleanBridgeBatch R I) : ℕ :=
  Fintype.card B.BridgeIndex

end CleanBridgeBatch

namespace BalancedAnchorRouting.CleanTailBridgeFamily

variable
    {R : PathPacking G S T} {anchor : R.Index → V}
    {I : Finset R.Index} {C : Finset V}
    (B : BalancedAnchorRouting R anchor I C)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)

/-- The clean bridges indexed by the maximum endpoint matching already form
a simultaneous bridge batch. -/
noncomputable def matchingBridgeBatch
    (F := B.cleanTailBridgeFamily hanchor) :
    CleanBridgeBatch R I := by
  classical
  let M := maximumEndpointMatching B hanchor (F := F)
  let Rows := maximumEndpointRows B hanchor (F := F)
  refine
    { BridgeIndex := {u : {r : R.Index // r ∈ B.U} // u ∈ M}
      usedRows := Rows
      usedRows_subset := ?_
      left := fun u => u.1.1
      right := fun u => (F.data u.1).head
      left_mem := ?_
      right_mem := ?_
      left_ne_right := ?_
      row_pairs_disjoint := ?_
      path := fun u => (F.data u.1).path
      source_mem := ?_
      target_mem := ?_
      internallyDisjoint_usedRows := ?_
      node_disjoint := ?_ }
  · exact maximumEndpointRows_subset B hanchor (F := F)
  · intro u
    exact Finset.mem_biUnion.mpr
      ⟨u.1, u.2, by simp [endpointRows]⟩
  · intro u
    exact Finset.mem_biUnion.mpr
      ⟨u.1, u.2, by simp [endpointRows]⟩
  · intro u
    exact (F.data u.1).head_ne_tail.symm
  · intro u v huv
    apply maximumEndpointMatching_disjoint B hanchor (F := F)
    · exact u.2
    · exact v.2
    · intro huv'
      exact huv (Subtype.ext huv')
  · intro u
    exact (F.data u.1).source_mem_tail
  · intro u
    exact (F.data u.1).target_mem_head
  · intro u
    intro v hvPath hvRows
    apply (F.data u.1).internallyDisjoint_selectedRows hvPath
    rcases
        (mem_selectedRowVertexSet R Rows).1 hvRows with
      ⟨r, hrRows, hvr⟩
    exact (mem_selectedRowVertexSet R I).2
      ⟨r,
        maximumEndpointRows_subset B hanchor (F := F) hrRows,
        hvr⟩
  · intro u v huv
    apply node_disjoint B hanchor (F := F)
    intro huv'
    exact huv (Subtype.ext huv')

@[simp] theorem matchingBridgeBatch_card
    (F := B.cleanTailBridgeFamily hanchor) :
    (matchingBridgeBatch B hanchor (F := F)).card =
      (maximumEndpointMatching B hanchor (F := F)).card := by
  classical
  simp [matchingBridgeBatch, CleanBridgeBatch.card,
    maximumEndpointMatching]

/-- Tails ending on one fixed saturated hub, with membership retained in the
type. -/
abbrev HubTail
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) :=
  {u : {r : R.Index // r ∈ B.U} //
    u ∈ hubTails B hanchor (F := F) c}

theorem hubTail_head_eq
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) (u : HubTail B hanchor (F := F) c) :
    (F.data u.1).head = c :=
  (mem_hubTails B hanchor (F := F) c u.1).1 u.2 |>.2

theorem hubTail_tail_not_mem_rows
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) (u : HubTail B hanchor (F := F) c) :
    u.1.1 ∉ maximumEndpointRows B hanchor (F := F) :=
  (mem_unsaturatedTails B hanchor (F := F) u.1).1
    ((mem_hubTails B hanchor (F := F) c u.1).1 u.2).1

theorem hubTail_target_mem_row
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) (u : HubTail B hanchor (F := F) c) :
    (F.data u.1).path.target ∈ (R.path c).vertexSet := by
  simpa [hubTail_head_eq B hanchor (F := F) c u] using
    (F.data u.1).target_mem_head

/-- Distinct tails ending at one hub have distinct attachment vertices. -/
theorem hubTail_target_injective
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) :
    Function.Injective
      (fun u : HubTail B hanchor (F := F) c =>
        (F.data u.1).path.target) := by
  intro u v huv
  apply Subtype.ext
  by_contra hne
  exact
    (target_injective_on_same_head B hanchor (F := F)
      hne
      ((hubTail_head_eq B hanchor (F := F) c u).trans
        (hubTail_head_eq B hanchor (F := F) c v).symm))
      huv

/-- Consecutive attachment pairs on one hub row, listed in row order. -/
structure HubAttachmentPairing
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) where
  first :
    Fin ((hubTails B hanchor (F := F) c).card / 2) →
      HubTail B hanchor (F := F) c
  second :
    Fin ((hubTails B hanchor (F := F) c).card / 2) →
      HubTail B hanchor (F := F) c
  first_injective : Function.Injective first
  second_injective : Function.Injective second
  first_ne_second :
    ∀ a b, first a ≠ second b
  first_before_second :
    ∀ a,
      (R.path c).Before
        (F.data (first a).1).path.target
        (F.data (second a).1).path.target
  ordered :
    ∀ ⦃a b⦄, a.1 < b.1 →
      (R.path c).Before
        (F.data (second a).1).path.target
        (F.data (first b).1).path.target

/-- Sort the attachments by their vertex indices on the hub row and pair
positions `(0,1), (2,3), ...`. -/
noncomputable def hubAttachmentPairing
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index) :
    HubAttachmentPairing B hanchor (F := F) c := by
  classical
  let D := (hubTails B hanchor (F := F) c).card
  let key : HubTail B hanchor (F := F) c → ℕ :=
    fun u => (R.path c).vertexIndex (F.data u.1).path.target
  have hkey : Function.Injective key := by
    intro u v huv
    apply hubTail_target_injective B hanchor (F := F) c
    apply (R.path c).before_antisymm
    · apply (R.path c).before_iff_vertexIndex_le |>.2
      exact
        ⟨hubTail_target_mem_row B hanchor (F := F) c u,
          hubTail_target_mem_row B hanchor (F := F) c v,
          huv.le⟩
    · apply (R.path c).before_iff_vertexIndex_le |>.2
      exact
        ⟨hubTail_target_mem_row B hanchor (F := F) c v,
          hubTail_target_mem_row B hanchor (F := F) c u,
          huv.ge⟩
  letI : LinearOrder (HubTail B hanchor (F := F) c) :=
    LinearOrder.lift' key hkey
  let E : Fin D ≃o HubTail B hanchor (F := F) c :=
    Fintype.orderIsoFinOfCardEq
      (HubTail B hanchor (F := F) c) (by simp [D])
  let evenPos :
      Fin (D / 2) → Fin D :=
    fun a => ⟨2 * a.1, by
      have ha := a.2
      omega⟩
  let oddPos :
      Fin (D / 2) → Fin D :=
    fun a => ⟨2 * a.1 + 1, by
      have ha := a.2
      omega⟩
  refine
    { first := fun a => E (evenPos a)
      second := fun a => E (oddPos a)
      first_injective := ?_
      second_injective := ?_
      first_ne_second := ?_
      first_before_second := ?_
      ordered := ?_ }
  · intro a b hab
    apply Fin.ext
    have := congrArg
      (fun u : HubTail B hanchor (F := F) c =>
        (E.symm u).1) hab
    simpa [evenPos] using this
  · intro a b hab
    apply Fin.ext
    have := congrArg
      (fun u : HubTail B hanchor (F := F) c =>
        (E.symm u).1) hab
    simpa [oddPos] using this
  · intro a b hab
    have hpos :
        evenPos a = oddPos b := by
      exact E.injective hab
    have hval := congrArg Fin.val hpos
    simp [evenPos, oddPos] at hval
    omega
  · intro a
    apply (R.path c).before_iff_vertexIndex_le |>.2
    refine
      ⟨hubTail_target_mem_row B hanchor (F := F) c (E (evenPos a)),
        hubTail_target_mem_row B hanchor (F := F) c (E (oddPos a)),
        ?_⟩
    have hlt : E (evenPos a) < E (oddPos a) :=
      E.lt_iff_lt.2 (by simp [evenPos, oddPos])
    exact Nat.le_of_lt hlt
  · intro a b hab
    apply (R.path c).before_iff_vertexIndex_le |>.2
    refine
      ⟨hubTail_target_mem_row B hanchor (F := F) c (E (oddPos a)),
        hubTail_target_mem_row B hanchor (F := F) c (E (evenPos b)),
        ?_⟩
    have hlt : E (oddPos a) < E (evenPos b) :=
      E.lt_iff_lt.2 (by
        simp only [oddPos, evenPos, Fin.mk_lt_mk]
        omega)
    exact Nat.le_of_lt hlt

/-- The row segment joining one consecutive pair of hub attachments. -/
noncomputable def hubPairSegment
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    (a : Fin ((hubTails B hanchor (F := F) c).card / 2)) :
    GraphPath G :=
  (R.path c).segmentOfBefore
    ((hubAttachmentPairing B hanchor (F := F) c).first_before_second a)

@[simp] theorem hubPairSegment_source
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    (a : Fin ((hubTails B hanchor (F := F) c).card / 2)) :
    (hubPairSegment B hanchor (F := F) c a).source =
      (F.data
        ((hubAttachmentPairing B hanchor (F := F) c).first a).1).path.target := by
  simp [hubPairSegment]

@[simp] theorem hubPairSegment_target
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    (a : Fin ((hubTails B hanchor (F := F) c).card / 2)) :
    (hubPairSegment B hanchor (F := F) c a).target =
      (F.data
        ((hubAttachmentPairing B hanchor (F := F) c).second a).1).path.target := by
  simp [hubPairSegment]

theorem hubPairSegment_vertexSet_subset
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    (a : Fin ((hubTails B hanchor (F := F) c).card / 2)) :
    (hubPairSegment B hanchor (F := F) c a).vertexSet ⊆
      (R.path c).vertexSet := by
  exact (R.path c).segmentOfBefore_vertexSet_subset
    ((hubAttachmentPairing B hanchor (F := F) c).first_before_second a)

/-- Join two cleaned tails through the row segment between their consecutive
hub attachments.  Cycle erasure is harmless here and makes simplicity
automatic; all later disjointness proofs use the supplied carrier subset. -/
noncomputable def hubPairConnector
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    (a : Fin ((hubTails B hanchor (F := F) c).card / 2)) :
    GraphPath G :=
  (F.data
      ((hubAttachmentPairing B hanchor (F := F) c).first a).1).path
    |>.append3WithEqToPath
    (hubPairSegment B hanchor (F := F) c a)
    (F.data
      ((hubAttachmentPairing B hanchor (F := F) c).second a).1).path.reverse
    (by simp)
    (by simp)

@[simp] theorem hubPairConnector_source
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    (a : Fin ((hubTails B hanchor (F := F) c).card / 2)) :
    (hubPairConnector B hanchor (F := F) c a).source =
      (F.data
        ((hubAttachmentPairing B hanchor (F := F) c).first a).1).path.source := by
  simp [hubPairConnector]

@[simp] theorem hubPairConnector_target
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    (a : Fin ((hubTails B hanchor (F := F) c).card / 2)) :
    (hubPairConnector B hanchor (F := F) c a).target =
      (F.data
        ((hubAttachmentPairing B hanchor (F := F) c).second a).1).path.source := by
  simp [hubPairConnector]

theorem hubPairConnector_vertexSet_subset
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    (a : Fin ((hubTails B hanchor (F := F) c).card / 2)) :
    (hubPairConnector B hanchor (F := F) c a).vertexSet ⊆
      (F.data
          ((hubAttachmentPairing B hanchor (F := F) c).first a).1).path.vertexSet ∪
        (hubPairSegment B hanchor (F := F) c a).vertexSet ∪
        (F.data
          ((hubAttachmentPairing B hanchor (F := F) c).second a).1).path.vertexSet := by
  simpa [hubPairConnector] using
    (F.data
      ((hubAttachmentPairing B hanchor (F := F) c).first a).1).path
        |>.append3WithEqToPath_vertexSet_subset
          (hubPairSegment B hanchor (F := F) c a)
          (F.data
            ((hubAttachmentPairing B hanchor (F := F) c).second a).1).path.reverse
          (by simp) (by simp)

/-- All consecutive hub pairs, tagged by their saturated hub row. -/
abbrev HubPairIndex
    (F := B.cleanTailBridgeFamily hanchor) :=
  Σ c : {c : R.Index //
      c ∈ maximumEndpointRows B hanchor (F := F)},
    Fin ((hubTails B hanchor (F := F) c.1).card / 2)

/-- The first cleaned tail occurrence of a global hub pair. -/
noncomputable def hubPairFirst
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    {r : R.Index // r ∈ B.U} :=
  ((hubAttachmentPairing B hanchor (F := F) p.1.1).first p.2).1

/-- The second cleaned tail occurrence of a global hub pair. -/
noncomputable def hubPairSecond
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    {r : R.Index // r ∈ B.U} :=
  ((hubAttachmentPairing B hanchor (F := F) p.1.1).second p.2).1

/-- Two occurrence slots for every hub pair. -/
abbrev HubOccurrence
    (F := B.cleanTailBridgeFamily hanchor) :=
  HubPairIndex B hanchor (F := F) × Fin 2

/-- The cleaned tail occupying one occurrence slot. -/
noncomputable def hubOccurrenceTail
    (F := B.cleanTailBridgeFamily hanchor)
    (o : HubOccurrence B hanchor (F := F)) :
    {r : R.Index // r ∈ B.U} :=
  if o.2.1 = 0 then
    hubPairFirst B hanchor (F := F) o.1
  else
    hubPairSecond B hanchor (F := F) o.1

theorem hubPairFirst_head_eq
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    (F.data (hubPairFirst B hanchor (F := F) p)).head =
      p.1.1 := by
  exact hubTail_head_eq B hanchor (F := F) p.1.1
    ((hubAttachmentPairing B hanchor (F := F) p.1.1).first p.2)

theorem hubPairSecond_head_eq
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    (F.data (hubPairSecond B hanchor (F := F) p)).head =
      p.1.1 := by
  exact hubTail_head_eq B hanchor (F := F) p.1.1
    ((hubAttachmentPairing B hanchor (F := F) p.1.1).second p.2)

theorem hubOccurrence_head_eq
    (F := B.cleanTailBridgeFamily hanchor)
    (o : HubOccurrence B hanchor (F := F)) :
    (F.data (hubOccurrenceTail B hanchor (F := F) o)).head =
      o.1.1.1 := by
  rcases o with ⟨p, s⟩
  fin_cases s <;>
    simp [hubOccurrenceTail, hubPairFirst_head_eq,
      hubPairSecond_head_eq]

/-- Every selected attachment occurrence is used exactly once. -/
theorem hubOccurrenceTail_injective
    (F := B.cleanTailBridgeFamily hanchor) :
    Function.Injective
      (hubOccurrenceTail B hanchor (F := F)) := by
  rintro ⟨⟨c, a⟩, s⟩ ⟨⟨d, b⟩, t⟩ htail
  have hhead :
      (F.data
          (hubOccurrenceTail B hanchor (F := F)
            ⟨⟨c, a⟩, s⟩)).head =
        (F.data
          (hubOccurrenceTail B hanchor (F := F)
            ⟨⟨d, b⟩, t⟩)).head :=
    congrArg (fun u => (F.data u).head) htail
  have hcd : c.1 = d.1 := by
    simpa [hubOccurrence_head_eq] using hhead
  have hcd' : c = d := Subtype.ext hcd
  subst d
  fin_cases s <;> fin_cases t
  · have hab :
        (hubAttachmentPairing B hanchor (F := F) c.1).first a =
          (hubAttachmentPairing B hanchor (F := F) c.1).first b := by
        apply Subtype.ext
        simpa [hubOccurrenceTail, hubPairFirst] using htail
    have := (hubAttachmentPairing B hanchor (F := F) c.1).first_injective hab
    subst b
    rfl
  · exact False.elim
      ((hubAttachmentPairing B hanchor (F := F) c.1).first_ne_second a b
        (by
          apply Subtype.ext
          simpa [hubOccurrenceTail, hubPairFirst, hubPairSecond] using
            htail))
  · exact False.elim
      ((hubAttachmentPairing B hanchor (F := F) c.1).first_ne_second b a
        (by
          apply Subtype.ext
          simpa [hubOccurrenceTail, hubPairFirst, hubPairSecond] using
            htail.symm))
  · have hab :
        (hubAttachmentPairing B hanchor (F := F) c.1).second a =
          (hubAttachmentPairing B hanchor (F := F) c.1).second b := by
        apply Subtype.ext
        simpa [hubOccurrenceTail, hubPairSecond] using htail
    have := (hubAttachmentPairing B hanchor (F := F) c.1).second_injective hab
    subst b
    rfl

/-- Endpoint rows of all hub-paired connectors. -/
noncomputable def hubUsedRows
    (F := B.cleanTailBridgeFamily hanchor) : Finset R.Index :=
  (Finset.univ :
      Finset (HubOccurrence B hanchor (F := F))).image
    fun o => (hubOccurrenceTail B hanchor (F := F) o).1

theorem hubUsedRows_subset
    (F := B.cleanTailBridgeFamily hanchor) :
    hubUsedRows B hanchor (F := F) ⊆ I := by
  classical
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨o, _ho, rfl⟩
  exact B.U_subset (hubOccurrenceTail B hanchor (F := F) o).2

theorem hubOccurrenceTail_mem_unsaturated
    (F := B.cleanTailBridgeFamily hanchor)
    (o : HubOccurrence B hanchor (F := F)) :
    hubOccurrenceTail B hanchor (F := F) o ∈
      unsaturatedTails B hanchor (F := F) := by
  rcases o with ⟨q, s⟩
  unfold hubOccurrenceTail
  split
  · exact
      ((mem_hubTails B hanchor (F := F) q.1.1
        ((hubAttachmentPairing B hanchor (F := F)
          q.1.1).first q.2).1).1
          ((hubAttachmentPairing B hanchor (F := F)
            q.1.1).first q.2).2).1
  · exact
      ((mem_hubTails B hanchor (F := F) q.1.1
        ((hubAttachmentPairing B hanchor (F := F)
          q.1.1).second q.2).1).1
          ((hubAttachmentPairing B hanchor (F := F)
            q.1.1).second q.2).2).1

theorem hub_row_not_mem_usedRows
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    p.1.1 ∉ hubUsedRows B hanchor (F := F) := by
  classical
  intro hp
  rcases Finset.mem_image.mp hp with ⟨o, _ho, ho⟩
  have htailNot :
      (hubOccurrenceTail B hanchor (F := F) o).1 ∉
        maximumEndpointRows B hanchor (F := F) :=
    (mem_unsaturatedTails B hanchor (F := F)
      (hubOccurrenceTail B hanchor (F := F) o)).1
        (hubOccurrenceTail_mem_unsaturated
          B hanchor (F := F) o)
  apply htailNot
  rw [ho]
  exact p.1.2

@[simp] theorem fintype_card_hubPairIndex
    (F := B.cleanTailBridgeFamily hanchor) :
    Fintype.card (HubPairIndex B hanchor (F := F)) =
      hubPairCount B hanchor (F := F) := by
  classical
  simp only [HubPairIndex, Fintype.card_sigma, Fintype.card_fin,
    hubPairCount]
  rw [← Finset.attach_eq_univ]
  exact
    (Finset.sum_attach
      (maximumEndpointRows B hanchor (F := F))
      (fun c =>
        (hubTails B hanchor (F := F) c).card / 2))

/-- The original row carrying any endpoint occurrence. -/
noncomputable def hubOccurrenceRow
    (F := B.cleanTailBridgeFamily hanchor)
    (o : HubOccurrence B hanchor (F := F)) : R.Index :=
  (hubOccurrenceTail B hanchor (F := F) o).1

theorem hubOccurrenceRow_injective
    (F := B.cleanTailBridgeFamily hanchor) :
    Function.Injective
      (hubOccurrenceRow B hanchor (F := F)) := by
  intro o p hop
  apply hubOccurrenceTail_injective B hanchor (F := F)
  exact Subtype.ext hop

/-- The globally tagged connector routed through a saturated hub. -/
noncomputable def globalHubConnector
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    GraphPath G :=
  hubPairConnector B hanchor (F := F) p.1.1 p.2

@[simp] theorem globalHubConnector_source
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    (globalHubConnector B hanchor (F := F) p).source =
      (F.data (hubPairFirst B hanchor (F := F) p)).path.source := by
  simp [globalHubConnector, hubPairFirst]

@[simp] theorem globalHubConnector_target
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    (globalHubConnector B hanchor (F := F) p).target =
      (F.data (hubPairSecond B hanchor (F := F) p)).path.source := by
  simp [globalHubConnector, hubPairSecond]

theorem globalHubConnector_vertexSet_subset
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    (globalHubConnector B hanchor (F := F) p).vertexSet ⊆
      (F.data (hubPairFirst B hanchor (F := F) p)).path.vertexSet ∪
        (hubPairSegment B hanchor (F := F) p.1.1 p.2).vertexSet ∪
        (F.data (hubPairSecond B hanchor (F := F) p)).path.vertexSet := by
  simpa [globalHubConnector, hubPairFirst, hubPairSecond] using
    hubPairConnector_vertexSet_subset
      B hanchor (F := F) p.1.1 p.2

theorem hubPairFirst_mem_usedRows
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    (hubPairFirst B hanchor (F := F) p).1 ∈
      hubUsedRows B hanchor (F := F) := by
  classical
  apply Finset.mem_image.mpr
  refine
    ⟨(p, (0 : Fin 2)), Finset.mem_univ _, ?_⟩
  simp [hubOccurrenceRow, hubOccurrenceTail, hubPairFirst]

theorem hubPairSecond_mem_usedRows
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    (hubPairSecond B hanchor (F := F) p).1 ∈
      hubUsedRows B hanchor (F := F) := by
  classical
  apply Finset.mem_image.mpr
  refine
    ⟨(p, (1 : Fin 2)), Finset.mem_univ _, ?_⟩
  simp [hubOccurrenceRow, hubOccurrenceTail, hubPairSecond]

theorem hubPair_endpoint_rows_disjoint
    (F := B.cleanTailBridgeFamily hanchor) :
    Pairwise fun p q : HubPairIndex B hanchor (F := F) =>
      Disjoint
        ({(hubPairFirst B hanchor (F := F) p).1,
          (hubPairSecond B hanchor (F := F) p).1} :
          Finset R.Index)
        ({(hubPairFirst B hanchor (F := F) q).1,
          (hubPairSecond B hanchor (F := F) q).1} :
          Finset R.Index) := by
  intro p q hpq
  rw [Finset.disjoint_left]
  intro r hrp hrq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrp hrq
  rcases hrp with rfl | rfl <;> rcases hrq with h | h
  · have ho :
        (p, (0 : Fin 2)) = (q, (0 : Fin 2)) :=
      hubOccurrenceRow_injective B hanchor (F := F) (by
        simpa [hubOccurrenceRow, hubOccurrenceTail, hubPairFirst] using h)
    exact hpq (congrArg Prod.fst ho)
  · have ho :
        (p, (0 : Fin 2)) = (q, (1 : Fin 2)) :=
      hubOccurrenceRow_injective B hanchor (F := F) (by
        simpa [hubOccurrenceRow, hubOccurrenceTail,
          hubPairFirst, hubPairSecond] using h)
    exact Fin.zero_ne_one (congrArg Prod.snd ho)
  · have ho :
        (p, (1 : Fin 2)) = (q, (0 : Fin 2)) :=
      hubOccurrenceRow_injective B hanchor (F := F) (by
        simpa [hubOccurrenceRow, hubOccurrenceTail,
          hubPairFirst, hubPairSecond] using h)
    exact Fin.zero_ne_one (congrArg Prod.snd ho).symm
  · have ho :
        (p, (1 : Fin 2)) = (q, (1 : Fin 2)) :=
      hubOccurrenceRow_injective B hanchor (F := F) (by
        simpa [hubOccurrenceRow, hubOccurrenceTail, hubPairSecond] using h)
    exact hpq (congrArg Prod.fst ho)

theorem hubPairFirst_ne_first_of_ne
    (F := B.cleanTailBridgeFamily hanchor)
    {p q : HubPairIndex B hanchor (F := F)} (hpq : p ≠ q) :
    hubPairFirst B hanchor (F := F) p ≠
      hubPairFirst B hanchor (F := F) q := by
  intro h
  have ho :
      (p, (0 : Fin 2)) = (q, (0 : Fin 2)) :=
    hubOccurrenceTail_injective B hanchor (F := F) (by
      simpa [hubOccurrenceTail, hubPairFirst] using h)
  exact hpq (congrArg Prod.fst ho)

theorem hubPairFirst_ne_second_of_ne
    (F := B.cleanTailBridgeFamily hanchor)
    {p q : HubPairIndex B hanchor (F := F)} (hpq : p ≠ q) :
    hubPairFirst B hanchor (F := F) p ≠
      hubPairSecond B hanchor (F := F) q := by
  intro h
  have ho :
      (p, (0 : Fin 2)) = (q, (1 : Fin 2)) :=
    hubOccurrenceTail_injective B hanchor (F := F) (by
      simpa [hubOccurrenceTail, hubPairFirst, hubPairSecond] using h)
  exact Fin.zero_ne_one (congrArg Prod.snd ho)

theorem hubPairSecond_ne_first_of_ne
    (F := B.cleanTailBridgeFamily hanchor)
    {p q : HubPairIndex B hanchor (F := F)} (hpq : p ≠ q) :
    hubPairSecond B hanchor (F := F) p ≠
      hubPairFirst B hanchor (F := F) q := by
  exact fun h =>
    hubPairFirst_ne_second_of_ne B hanchor (F := F) hpq.symm h.symm

theorem hubPairSecond_ne_second_of_ne
    (F := B.cleanTailBridgeFamily hanchor)
    {p q : HubPairIndex B hanchor (F := F)} (hpq : p ≠ q) :
    hubPairSecond B hanchor (F := F) p ≠
      hubPairSecond B hanchor (F := F) q := by
  intro h
  have ho :
      (p, (1 : Fin 2)) = (q, (1 : Fin 2)) :=
    hubOccurrenceTail_injective B hanchor (F := F) (by
      simpa [hubOccurrenceTail, hubPairSecond] using h)
  exact hpq (congrArg Prod.fst ho)

/-- The first attachment of one pair is outside every other paired segment
on the same hub row. -/
theorem hubPairFirst_target_not_mem_otherSegment
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    {a b : Fin ((hubTails B hanchor (F := F) c).card / 2)}
    (hab : a ≠ b) :
    (F.data
        ((hubAttachmentPairing B hanchor (F := F) c).first a).1).path.target ∉
      (hubPairSegment B hanchor (F := F) c b).vertexSet := by
  let P := hubAttachmentPairing B hanchor (F := F) c
  have htargetNe :
      (F.data (P.first a).1).path.target ≠
        (F.data (P.first b).1).path.target := by
    intro h
    exact hab
      (P.first_injective
        (hubTail_target_injective B hanchor (F := F) c h))
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hablt | hbalt
  · have hz :
        (R.path c).Before
          (F.data (P.first a).1).path.target
          (F.data (P.first b).1).path.target :=
      (R.path c).before_trans
        (P.first_before_second a) (P.ordered hablt)
    exact (R.path c).not_mem_segmentOfBefore_of_before_source
      (P.first_before_second b) hz htargetNe
  · have hz :
        (R.path c).Before
          (F.data (P.second b).1).path.target
          (F.data (P.first a).1).path.target :=
      P.ordered hbalt
    have hne :
        (F.data (P.first a).1).path.target ≠
          (F.data (P.second b).1).path.target := by
      intro h
      exact P.first_ne_second a b
        (hubTail_target_injective B hanchor (F := F) c h)
    exact (R.path c).not_mem_segmentOfBefore_of_target_before
      (P.first_before_second b) hz hne

/-- The second attachment of one pair is outside every other paired segment
on the same hub row. -/
theorem hubPairSecond_target_not_mem_otherSegment
    (F := B.cleanTailBridgeFamily hanchor)
    (c : R.Index)
    {a b : Fin ((hubTails B hanchor (F := F) c).card / 2)}
    (hab : a ≠ b) :
    (F.data
        ((hubAttachmentPairing B hanchor (F := F) c).second a).1).path.target ∉
      (hubPairSegment B hanchor (F := F) c b).vertexSet := by
  let P := hubAttachmentPairing B hanchor (F := F) c
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hablt | hbalt
  · have hz := P.ordered hablt
    have hne :
        (F.data (P.second a).1).path.target ≠
          (F.data (P.first b).1).path.target := by
      intro h
      exact P.first_ne_second b a
        (hubTail_target_injective B hanchor (F := F) c h.symm)
    exact (R.path c).not_mem_segmentOfBefore_of_before_source
      (P.first_before_second b) hz hne
  · have hz :
        (R.path c).Before
          (F.data (P.second b).1).path.target
          (F.data (P.second a).1).path.target :=
      (R.path c).before_trans
        (P.ordered hbalt) (P.first_before_second a)
    have hne :
        (F.data (P.second a).1).path.target ≠
          (F.data (P.second b).1).path.target := by
      intro h
      exact hab
        (P.second_injective
          (hubTail_target_injective B hanchor (F := F) c h))
    exact (R.path c).not_mem_segmentOfBefore_of_target_before
      (P.first_before_second b) hz hne

/-- Row segments belonging to distinct global hub pairs are disjoint. -/
theorem hubPairSegments_nodeDisjoint
    (F := B.cleanTailBridgeFamily hanchor)
    {p q : HubPairIndex B hanchor (F := F)} (hpq : p ≠ q) :
    Disjoint
      (hubPairSegment B hanchor (F := F) p.1.1 p.2).vertexSet
      (hubPairSegment B hanchor (F := F) q.1.1 q.2).vertexSet := by
  rcases p with ⟨c, a⟩
  rcases q with ⟨d, b⟩
  by_cases hcd : c = d
  · subst d
    have hab : a ≠ b := by
      intro hab
      apply hpq
      exact Sigma.ext rfl (heq_of_eq hab)
    let P := hubAttachmentPairing B hanchor (F := F) c.1
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hablt | hbalt
    · have hne :
          (F.data (P.second a).1).path.target ≠
            (F.data (P.first b).1).path.target := by
        intro h
        exact P.first_ne_second b a
          (hubTail_target_injective B hanchor (F := F) c.1 h.symm)
      simpa [hubPairSegment, P] using
        (R.path c.1).segmentOfBefore_disjoint_of_strict_target_before_source
          (P.first_before_second a) (P.first_before_second b)
          (P.ordered hablt) hne
    · have hne :
          (F.data (P.second b).1).path.target ≠
            (F.data (P.first a).1).path.target := by
        intro h
        exact P.first_ne_second a b
          (hubTail_target_injective B hanchor (F := F) c.1 h.symm)
      exact (by
        simpa [hubPairSegment, P] using
          ((R.path c.1)
            |>.segmentOfBefore_disjoint_of_strict_target_before_source
              (P.first_before_second b) (P.first_before_second a)
              (P.ordered hbalt) hne).symm)
  · have hcdv : c.1 ≠ d.1 :=
      fun h => hcd (Subtype.ext h)
    exact (R.node_disjoint hcdv).mono
      (hubPairSegment_vertexSet_subset
        B hanchor (F := F) c.1 a)
      (hubPairSegment_vertexSet_subset
        B hanchor (F := F) d.1 b)

/-- The first cleaned bridge of one hub pair is disjoint from every other
hub-pair row segment. -/
theorem hubPairFirst_bridge_disjoint_otherSegment
    (F := B.cleanTailBridgeFamily hanchor)
    {p q : HubPairIndex B hanchor (F := F)} (hpq : p ≠ q) :
    Disjoint
      (F.data (hubPairFirst B hanchor (F := F) p)).path.vertexSet
      (hubPairSegment B hanchor (F := F) q.1.1 q.2).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvBridge hvSegment
  have hvQHub :
      v ∈ (R.path q.1.1).vertexSet :=
    hubPairSegment_vertexSet_subset
      B hanchor (F := F) q.1.1 q.2 hvSegment
  have hvQI :
      v ∈ selectedRowVertexSet R I :=
    (mem_selectedRowVertexSet R I).2
      ⟨q.1.1,
        maximumEndpointRows_subset B hanchor (F := F) q.1.2,
        hvQHub⟩
  rcases
      (F.data (hubPairFirst B hanchor (F := F) p))
        |>.internallyDisjoint_selectedRows hvBridge hvQI with
    hsource | htarget
  · have hvTail :
        v ∈ (R.path
          (hubPairFirst B hanchor (F := F) p).1).vertexSet := by
      simpa [hsource] using
        (F.data (hubPairFirst B hanchor (F := F) p)).source_mem_tail
    have htailNe :
        (hubPairFirst B hanchor (F := F) p).1 ≠ q.1.1 := by
      intro h
      have hnot :=
        hubTail_tail_not_mem_rows B hanchor (F := F)
          p.1.1
          ((hubAttachmentPairing B hanchor (F := F) p.1.1).first p.2)
      have h' :
          ((hubAttachmentPairing B hanchor (F := F) p.1.1).first p.2).1.1 =
            q.1.1 := by
        simpa [hubPairFirst] using h
      apply hnot
      rw [h']
      exact q.1.2
    exact Finset.disjoint_left.mp (R.node_disjoint htailNe)
      hvTail hvQHub
  · by_cases hhub : p.1 = q.1
    · rcases p with ⟨c, a⟩
      rcases q with ⟨d, b⟩
      simp only at hhub
      subst d
      have hab : a ≠ b := by
        intro hab
        apply hpq
        exact Sigma.ext rfl (heq_of_eq hab)
      apply
        hubPairFirst_target_not_mem_otherSegment
          B hanchor (F := F) c.1 hab
      simpa [hubPairFirst, htarget] using hvSegment
    · have hhubv : p.1.1 ≠ q.1.1 :=
        fun h => hhub (Subtype.ext h)
      have hvPHub :
          v ∈ (R.path p.1.1).vertexSet := by
        simpa [htarget, hubPairFirst_head_eq B hanchor (F := F) p] using
          (F.data (hubPairFirst B hanchor (F := F) p)).target_mem_head
      exact Finset.disjoint_left.mp (R.node_disjoint hhubv)
        hvPHub hvQHub

/-- The second cleaned bridge of one hub pair is disjoint from every other
hub-pair row segment. -/
theorem hubPairSecond_bridge_disjoint_otherSegment
    (F := B.cleanTailBridgeFamily hanchor)
    {p q : HubPairIndex B hanchor (F := F)} (hpq : p ≠ q) :
    Disjoint
      (F.data (hubPairSecond B hanchor (F := F) p)).path.vertexSet
      (hubPairSegment B hanchor (F := F) q.1.1 q.2).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvBridge hvSegment
  have hvQHub :
      v ∈ (R.path q.1.1).vertexSet :=
    hubPairSegment_vertexSet_subset
      B hanchor (F := F) q.1.1 q.2 hvSegment
  have hvQI :
      v ∈ selectedRowVertexSet R I :=
    (mem_selectedRowVertexSet R I).2
      ⟨q.1.1,
        maximumEndpointRows_subset B hanchor (F := F) q.1.2,
        hvQHub⟩
  rcases
      (F.data (hubPairSecond B hanchor (F := F) p))
        |>.internallyDisjoint_selectedRows hvBridge hvQI with
    hsource | htarget
  · have hvTail :
        v ∈ (R.path
          (hubPairSecond B hanchor (F := F) p).1).vertexSet := by
      simpa [hsource] using
        (F.data (hubPairSecond B hanchor (F := F) p)).source_mem_tail
    have htailNe :
        (hubPairSecond B hanchor (F := F) p).1 ≠ q.1.1 := by
      intro h
      have hnot :=
        hubTail_tail_not_mem_rows B hanchor (F := F)
          p.1.1
          ((hubAttachmentPairing B hanchor (F := F) p.1.1).second p.2)
      have h' :
          ((hubAttachmentPairing B hanchor (F := F) p.1.1).second p.2).1.1 =
            q.1.1 := by
        simpa [hubPairSecond] using h
      apply hnot
      rw [h']
      exact q.1.2
    exact Finset.disjoint_left.mp (R.node_disjoint htailNe)
      hvTail hvQHub
  · by_cases hhub : p.1 = q.1
    · rcases p with ⟨c, a⟩
      rcases q with ⟨d, b⟩
      simp only at hhub
      subst d
      have hab : a ≠ b := by
        intro hab
        apply hpq
        exact Sigma.ext rfl (heq_of_eq hab)
      apply
        hubPairSecond_target_not_mem_otherSegment
          B hanchor (F := F) c.1 hab
      simpa [hubPairSecond, htarget] using hvSegment
    · have hhubv : p.1.1 ≠ q.1.1 :=
        fun h => hhub (Subtype.ext h)
      have hvPHub :
          v ∈ (R.path p.1.1).vertexSet := by
        simpa [htarget, hubPairSecond_head_eq B hanchor (F := F) p] using
          (F.data (hubPairSecond B hanchor (F := F) p)).target_mem_head
      exact Finset.disjoint_left.mp (R.node_disjoint hhubv)
        hvPHub hvQHub

/-- A row outside an index set is vertex-disjoint from the union of the rows
in that set. -/
theorem row_vertex_not_mem_selectedRowVertexSet
    {J : Finset R.Index} {c : R.Index} (hc : c ∉ J)
    {v : V} (hv : v ∈ (R.path c).vertexSet) :
    v ∉ selectedRowVertexSet R J := by
  intro hvJ
  rcases (mem_selectedRowVertexSet R J).1 hvJ with
    ⟨r, hrJ, hvr⟩
  by_cases hrc : r = c
  · exact hc (hrc ▸ hrJ)
  · exact Finset.disjoint_left.mp (R.node_disjoint hrc)
      hvr hv

/-- A hub connector is internally disjoint from all endpoint rows of the
global hub batch. -/
theorem globalHubConnector_internallyDisjoint_usedRows
    (F := B.cleanTailBridgeFamily hanchor)
    (p : HubPairIndex B hanchor (F := F)) :
    (globalHubConnector B hanchor (F := F) p)
      |>.InternallyDisjointFromSet
        (selectedRowVertexSet R
          (hubUsedRows B hanchor (F := F))) := by
  intro v hvPath hvUsed
  have hvCarrier :=
    globalHubConnector_vertexSet_subset
      B hanchor (F := F) p hvPath
  rcases Finset.mem_union.mp hvCarrier with hvFirstOrSegment | hvSecond
  · rcases Finset.mem_union.mp hvFirstOrSegment with hvFirst | hvSegment
    · rcases
        (F.data (hubPairFirst B hanchor (F := F) p))
          |>.internallyDisjoint_selectedRows hvFirst
            (by
              rcases
                  (mem_selectedRowVertexSet R
                    (hubUsedRows B hanchor (F := F))).1 hvUsed with
                ⟨r, hr, hvr⟩
              exact (mem_selectedRowVertexSet R I).2
                ⟨r, hubUsedRows_subset B hanchor (F := F) hr, hvr⟩) with
      hsource | htarget
      · exact Or.inl (by simpa [hsource])
      · have hvHub :
            v ∈ (R.path p.1.1).vertexSet := by
          simpa [htarget, hubPairFirst_head_eq B hanchor (F := F) p] using
            (F.data (hubPairFirst B hanchor (F := F) p)).target_mem_head
        exact False.elim
          (row_vertex_not_mem_selectedRowVertexSet
            (R := R) (hub_row_not_mem_usedRows B hanchor (F := F) p)
            hvHub hvUsed)
    · have hvHub :
          v ∈ (R.path p.1.1).vertexSet :=
        hubPairSegment_vertexSet_subset
          B hanchor (F := F) p.1.1 p.2 hvSegment
      exact False.elim
        (row_vertex_not_mem_selectedRowVertexSet
          (R := R) (hub_row_not_mem_usedRows B hanchor (F := F) p)
          hvHub hvUsed)
  · rcases
          (F.data (hubPairSecond B hanchor (F := F) p))
            |>.internallyDisjoint_selectedRows hvSecond
              (by
                rcases
                    (mem_selectedRowVertexSet R
                      (hubUsedRows B hanchor (F := F))).1 hvUsed with
                  ⟨r, hr, hvr⟩
                exact (mem_selectedRowVertexSet R I).2
                  ⟨r, hubUsedRows_subset B hanchor (F := F) hr, hvr⟩) with
      hsource | htarget
    · exact Or.inr (by simpa [hsource])
    · have hvHub :
          v ∈ (R.path p.1.1).vertexSet := by
        simpa [htarget, hubPairSecond_head_eq B hanchor (F := F) p] using
          (F.data (hubPairSecond B hanchor (F := F) p)).target_mem_head
      exact False.elim
        (row_vertex_not_mem_selectedRowVertexSet
          (R := R) (hub_row_not_mem_usedRows B hanchor (F := F) p)
          hvHub hvUsed)

/-- Distinct hub-paired connectors are node-disjoint.  This is the
nine-piece check for the two cleaned bridge pieces and the intervening hub
segment. -/
theorem globalHubConnector_nodeDisjoint
    (F := B.cleanTailBridgeFamily hanchor) :
    Pairwise fun p q : HubPairIndex B hanchor (F := F) =>
      GraphPath.NodeDisjoint
        (globalHubConnector B hanchor (F := F) p)
        (globalHubConnector B hanchor (F := F) q) := by
  intro p q hpq
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvp hvq
  have hpCarrier :=
    globalHubConnector_vertexSet_subset
      B hanchor (F := F) p hvp
  have hqCarrier :=
    globalHubConnector_vertexSet_subset
      B hanchor (F := F) q hvq
  rcases Finset.mem_union.mp hpCarrier with hpFirstOrSegment | hpSecond
  · rcases Finset.mem_union.mp hpFirstOrSegment with hpFirst | hpSegment
    · rcases Finset.mem_union.mp hqCarrier with hqFirstOrSegment | hqSecond
      · rcases Finset.mem_union.mp hqFirstOrSegment with hqFirst | hqSegment
        · exact
            Finset.disjoint_left.mp
              (node_disjoint B hanchor (F := F)
                (hubPairFirst_ne_first_of_ne
                  B hanchor (F := F) hpq))
              hpFirst hqFirst
        · exact
            Finset.disjoint_left.mp
              (hubPairFirst_bridge_disjoint_otherSegment
                B hanchor (F := F) hpq)
              hpFirst hqSegment
      · exact
          Finset.disjoint_left.mp
            (node_disjoint B hanchor (F := F)
              (hubPairFirst_ne_second_of_ne
                B hanchor (F := F) hpq))
            hpFirst hqSecond
    · rcases Finset.mem_union.mp hqCarrier with hqFirstOrSegment | hqSecond
      · rcases Finset.mem_union.mp hqFirstOrSegment with hqFirst | hqSegment
        · exact
            Finset.disjoint_left.mp
              (hubPairFirst_bridge_disjoint_otherSegment
                B hanchor (F := F) hpq.symm).symm
              hpSegment hqFirst
        · exact
            Finset.disjoint_left.mp
              (hubPairSegments_nodeDisjoint
                B hanchor (F := F) hpq)
              hpSegment hqSegment
      · exact
          Finset.disjoint_left.mp
            (hubPairSecond_bridge_disjoint_otherSegment
              B hanchor (F := F) hpq.symm).symm
            hpSegment hqSecond
  · rcases Finset.mem_union.mp hqCarrier with hqFirstOrSegment | hqSecond
    · rcases Finset.mem_union.mp hqFirstOrSegment with hqFirst | hqSegment
      · exact
          Finset.disjoint_left.mp
            (node_disjoint B hanchor (F := F)
              (hubPairSecond_ne_first_of_ne
                B hanchor (F := F) hpq))
            hpSecond hqFirst
      · exact
          Finset.disjoint_left.mp
            (hubPairSecond_bridge_disjoint_otherSegment
              B hanchor (F := F) hpq)
            hpSecond hqSegment
    · exact
        Finset.disjoint_left.mp
          (node_disjoint B hanchor (F := F)
            (hubPairSecond_ne_second_of_ne
              B hanchor (F := F) hpq))
          hpSecond hqSecond

/-- Pairing consecutive attachments at every saturated hub produces the
second bridge batch in the maximal-matching dichotomy. -/
noncomputable def hubBridgeBatch
    (F := B.cleanTailBridgeFamily hanchor) :
    CleanBridgeBatch R I := by
  classical
  refine
    { BridgeIndex := HubPairIndex B hanchor (F := F)
      usedRows := hubUsedRows B hanchor (F := F)
      usedRows_subset := hubUsedRows_subset B hanchor (F := F)
      left := fun p => (hubPairFirst B hanchor (F := F) p).1
      right := fun p => (hubPairSecond B hanchor (F := F) p).1
      left_mem := hubPairFirst_mem_usedRows B hanchor (F := F)
      right_mem := hubPairSecond_mem_usedRows B hanchor (F := F)
      left_ne_right := ?_
      row_pairs_disjoint :=
        hubPair_endpoint_rows_disjoint B hanchor (F := F)
      path := globalHubConnector B hanchor (F := F)
      source_mem := ?_
      target_mem := ?_
      internallyDisjoint_usedRows :=
        globalHubConnector_internallyDisjoint_usedRows
          B hanchor (F := F)
      node_disjoint :=
        globalHubConnector_nodeDisjoint B hanchor (F := F) }
  · intro p h
    have ho :
        (p, (0 : Fin 2)) = (p, (1 : Fin 2)) :=
      hubOccurrenceRow_injective B hanchor (F := F) (by
        simpa [hubOccurrenceRow, hubOccurrenceTail,
          hubPairFirst, hubPairSecond] using h)
    exact Fin.zero_ne_one (congrArg Prod.snd ho)
  · intro p
    simpa using
      (F.data (hubPairFirst B hanchor (F := F) p)).source_mem_tail
  · intro p
    simpa using
      (F.data (hubPairSecond B hanchor (F := F) p)).source_mem_tail

@[simp] theorem hubBridgeBatch_card
    (F := B.cleanTailBridgeFamily hanchor) :
    (hubBridgeBatch B hanchor (F := F)).card =
      hubPairCount B hanchor (F := F) := by
  change
    Fintype.card (HubPairIndex B hanchor (F := F)) =
      hubPairCount B hanchor (F := F)
  exact fintype_card_hubPairIndex B hanchor (F := F)

end BalancedAnchorRouting.CleanTailBridgeFamily

/-! ## Public bridge-batch theorem -/

/-- Node-well-linked anchors on selected disjoint rows produce a linear-size
simultaneous clean bridge batch. The additive `+ 1` accounts for a possible
odd anchor discarded before routing two equal halves. -/
theorem cleanBridgeBatch_of_nodeWellLinked
    (R : PathPacking G S T) (anchor : R.Index → V)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)
    (I : Finset R.Index) (C : Finset V)
    (hwell :
      NodeWellLinkedIn G C
        ((Finset.univ : Finset R.Index).image anchor)) :
    ∃ Batch : CleanBridgeBatch R I,
      I.card ≤ 12 * Batch.card + 1 := by
  classical
  let B := balancedAnchorRouting R anchor hanchor I C hwell
  let F := B.cleanTailBridgeFamily hanchor
  rcases
      BalancedAnchorRouting.CleanTailBridgeFamily.matching_large_or_hub_count
        B hanchor (F := F) with
    hmatching | hhub
  · refine
      ⟨BalancedAnchorRouting.CleanTailBridgeFamily.matchingBridgeBatch
          B hanchor (F := F), ?_⟩
    rw [BalancedAnchorRouting.CleanTailBridgeFamily.matchingBridgeBatch_card
      B hanchor (F := F)]
    have hhalf := B.U_card
    omega
  · refine
      ⟨BalancedAnchorRouting.CleanTailBridgeFamily.hubBridgeBatch
          B hanchor (F := F), ?_⟩
    rw [BalancedAnchorRouting.CleanTailBridgeFamily.hubBridgeBatch_card
      B hanchor (F := F)]
    have hhalf := B.U_card
    omega

/-- A multiplicative-only corollary for nontrivial selected row sets. -/
theorem cleanBridgeBatch_thirteen_of_nodeWellLinked
    (R : PathPacking G S T) (anchor : R.Index → V)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)
    (I : Finset R.Index) (C : Finset V)
    (hI : 2 ≤ I.card)
    (hwell :
      NodeWellLinkedIn G C
        ((Finset.univ : Finset R.Index).image anchor)) :
    ∃ Batch : CleanBridgeBatch R I,
      I.card ≤ 13 * Batch.card := by
  obtain ⟨Batch, hBatch⟩ :=
    cleanBridgeBatch_of_nodeWellLinked
      R anchor hanchor I C hwell
  refine ⟨Batch, ?_⟩
  have hpositive : 0 < Batch.card := by omega
  omega

end Exponent7
end SimpleGraph

end Lax17Proofs
