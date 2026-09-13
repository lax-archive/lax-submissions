import Lax17Proofs.Source.ChekuriChuzhoyPendantTransport
import Lax17Proofs.Source.EdgeMenger

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Claim 4.8

This module proves the quota-splitting linkage used at every branching
cluster in the top-down proof of Theorem 4.7 (journal Section 4.1).

The paper proves the claim by a fractional vertex-capacitated flow followed
by integrality.  Here the same integrality step is expressed through the
already proved finite vertex-Menger augmentation theorem.  Pendant copies
make the prescribed interface endpoints genuine degree-one terminals, so
augmentation retains the required child quota exactly.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical
open ChekuriChuzhoyPendantVertex

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A perfect linkage which stays in `C` can be regarded as a linkage in the
spanning graph obtained by deleting every edge with an endpoint outside `C`.

Keeping the original vertex type is useful below: pendant copies can then be
added without transporting terminal sets through an induced-subgraph subtype. -/
noncomputable def PerfectPathPacking.transferToRestrictToVertexSet
    {C A B : Finset V} (P : PerfectPathPacking G A B)
    (hP : P.toPathPacking.StaysIn C) :
    PerfectPathPacking (EdgeMenger.restrictToVertexSet G C) A B :=
  P.transfer (EdgeMenger.restrictToVertexSet G C) (by
    classical
    intro i e he
    have heout : s(e.out.1, e.out.2) = e := by
      rw [Sym2.mk, e.out_eq]
    have hePath :
        s(e.out.1, e.out.2) ∈ (P.path i).edgeSet := by
      rw [heout]
      simpa [GraphPath.edgeSet] using he
    have hendpoints :=
      GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) hePath
    rw [← heout]
    change
      G.Adj e.out.1 e.out.2 ∧
        e.out.1 ∈ C ∧ e.out.2 ∈ C
    exact
      ⟨(P.path i).walk.adj_of_mem_edges (by simpa [heout] using he),
        hP i hendpoints.1, hP i hendpoints.2⟩)

@[simp] theorem PerfectPathPacking.transferToRestrictToVertexSet_card
    {C A B : Finset V} (P : PerfectPathPacking G A B)
    (hP : P.toPathPacking.StaysIn C) :
    (PerfectPathPacking.transferToRestrictToVertexSet P hP).card =
      P.card := rfl

@[simp] theorem PerfectPathPacking.transferToRestrictToVertexSet_vertexSet
    {C A B : Finset V} (P : PerfectPathPacking G A B)
    (hP : P.toPathPacking.StaysIn C) :
    (PerfectPathPacking.transferToRestrictToVertexSet P hP).toPathPacking.vertexSet =
        P.toPathPacking.vertexSet := by
  classical
  apply Finset.biUnion_congr rfl
  intro i _hi
  exact GraphPath.transfer_vertexSet _ _ _

/-- Basis extension in the form used by Claim 4.8: a smaller endpoint-clean
packing can be augmented to the cardinality of any larger packing between the
same terminal sets, while retaining every endpoint of the smaller packing. -/
theorem EndpointCleanPathPacking.exists_extension_to_witness_card
    {S T : Finset V}
    (small large : EndpointCleanPathPacking G S T)
    (hcard : small.card ≤ large.card) :
    ∃ R : EndpointCleanPathPacking G S T,
      R.card = large.card ∧
        small.sourceSet ⊆ R.sourceSet ∧
          small.targetSet ⊆ R.targetSet := by
  classical
  have hrank :
      large.card ≤ Menger.minSeparatorSize G S T := by
    rw [← Menger.minSeparator_card]
    exact Menger.PathPacking.card_le_of_blocks large.toPathPacking
      Menger.minSeparator_blocks
  exact Menger.EndpointCleanPathPacking.exists_extension_card
    small hcard hrank

/-- Strip the pendant endpoint edges from an endpoint-clean packing between
fresh leaves.  Pairwise node-disjointness survives because every projected
vertex lifts to the corresponding input path. -/
theorem exists_projected_pendant_pathPacking
    {X : Finset V}
    {S T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : EndpointCleanPathPacking (graph (X := X) G) S T)
    (hS : S ⊆ leaves (V := V) (X := X))
    (hT : T ⊆ leaves (V := V) (X := X))
    (hST : Disjoint S T) :
    ∃ Q : PathPacking G (baseSet S hS) (baseSet T hT),
      Q.card = P.card ∧
        ∃ e : Q.Index ≃ P.Index,
          ∀ i : Q.Index,
            (Q.path i).source =
                (leafValue (hS ((P.endpoint_clean (e i)).source_mem))).1 ∧
              (Q.path i).target =
                (leafValue (hT ((P.endpoint_clean (e i)).target_mem))).1 := by
  classical
  let sourceMem : ∀ i : P.Index, (P.path i).source ∈ S :=
    fun i => (P.endpoint_clean i).source_mem
  let targetMem : ∀ i : P.Index, (P.path i).target ∈ T :=
    fun i => (P.endpoint_clean i).target_mem
  let a : P.Index → {x : V // x ∈ X} :=
    fun i => leafValue (hS (sourceMem i))
  let b : P.Index → {x : V // x ∈ X} :=
    fun i => leafValue (hT (targetMem i))
  have hsource (i : P.Index) :
      (P.path i).source = leaf (a i) := by
    exact leafValue_spec (hS (sourceMem i))
  have htarget (i : P.Index) :
      (P.path i).target = leaf (b i) := by
    exact leafValue_spec (hT (targetMem i))
  have hne (i : P.Index) :
      (P.path i).source ≠ (P.path i).target := by
    intro heq
    exact Finset.disjoint_left.mp hST
      (sourceMem i) (by simpa [← heq] using targetMem i)
  have hproject (i : P.Index) :
      ∃ R : GraphPath G,
        R.source = (a i).1 ∧ R.target = (b i).1 ∧
          ∀ x ∈ R.vertexSet,
            old (X := X) x ∈ (P.path i).vertexSet :=
    GraphPath.exists_projected_of_leaf_endpoints
      (P.path i) (a i) (b i) (hsource i) (htarget i) (hne i)
  let path : P.Index → GraphPath G :=
    fun i => Classical.choose (hproject i)
  have path_spec (i : P.Index) :
      (path i).source = (a i).1 ∧
        (path i).target = (b i).1 ∧
          ∀ x ∈ (path i).vertexSet,
            old (X := X) x ∈ (P.path i).vertexSet :=
    Classical.choose_spec (hproject i)
  let Q : PathPacking G (baseSet S hS) (baseSet T hT) :=
    { Index := P.Index
      path := path
      connects := by
        intro i
        refine Or.inl ⟨?_, ?_⟩
        · rw [(path_spec i).1]
          exact Finset.mem_image.mpr
            ⟨⟨(P.path i).source, sourceMem i⟩, by simp, rfl⟩
        · rw [(path_spec i).2.1]
          exact Finset.mem_image.mpr
            ⟨⟨(P.path i).target, targetMem i⟩, by simp, rfl⟩
      node_disjoint := by
        intro i j hij
        rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
        intro x hxi hxj
        exact Finset.disjoint_left.mp (P.node_disjoint hij)
          ((path_spec i).2.2 x hxi)
          ((path_spec j).2.2 x hxj) }
  refine ⟨Q, rfl, Equiv.refl P.Index, ?_⟩
  intro i
  exact ⟨(path_spec i).1, (path_spec i).2.1⟩

/-- Project an endpoint-clean pendant packing onto precisely the original
vertices which it actually uses as endpoints.  Because endpoint-clean
packings use distinct endpoints, the projected packing is perfect on these
two projected endpoint sets. -/
theorem exists_projected_pendant_perfectPathPacking
    {X : Finset V}
    {S T : Finset (ChekuriChuzhoyPendantVertex V X)}
    (P : EndpointCleanPathPacking (graph (X := X) G) S T)
    (hS : S ⊆ leaves (V := V) (X := X))
    (hT : T ⊆ leaves (V := V) (X := X))
    (hST : Disjoint S T) :
    let hPS : P.sourceSet ⊆ leaves (V := V) (X := X) :=
      subset_trans P.sourceSet_subset_left hS
    let hPT : P.targetSet ⊆ leaves (V := V) (X := X) :=
      subset_trans P.targetSet_subset_right hT
    ∃ Q : PerfectPathPacking G
        (baseSet P.sourceSet hPS) (baseSet P.targetSet hPT),
      Q.card = P.card := by
  classical
  dsimp only
  let hPS : P.sourceSet ⊆ leaves (V := V) (X := X) :=
    subset_trans P.sourceSet_subset_left hS
  let hPT : P.targetSet ⊆ leaves (V := V) (X := X) :=
    subset_trans P.targetSet_subset_right hT
  have hUsedDisj : Disjoint P.sourceSet P.targetSet := by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    exact Finset.disjoint_left.mp hST
      (P.sourceSet_subset_left hzS) (P.targetSet_subset_right hzT)
  let Pused :
      EndpointCleanPathPacking (graph (X := X) G)
        P.sourceSet P.targetSet :=
    { Index := P.Index
      path := P.path
      endpoint_clean := by
        intro i
        refine
          { source_mem := P.source_mem_sourceSet i
            target_mem := P.target_mem_targetSet i
            left_eq_source := ?_
            right_eq_target := ?_ }
        · intro z hz hzS
          exact (P.endpoint_clean i).left_eq_source hz
            (P.sourceSet_subset_left hzS)
        · intro z hz hzT
          exact (P.endpoint_clean i).right_eq_target hz
            (P.targetSet_subset_right hzT)
      node_disjoint := P.node_disjoint }
  rcases exists_projected_pendant_pathPacking
      (G := G) Pused hPS hPT hUsedDisj with
    ⟨Q, hQcard, _e⟩
  have hQleft :
      Q.card = (baseSet P.sourceSet hPS).card := by
    calc
      Q.card = P.card := hQcard
      _ = P.sourceSet.card := P.sourceSet_card.symm
      _ = (baseSet P.sourceSet hPS).card := by simp
  have hQright :
      Q.card = (baseSet P.targetSet hPT).card := by
    calc
      Q.card = P.card := hQcard
      _ = P.targetSet.card := P.targetSet_card.symm
      _ = (baseSet P.targetSet hPT).card := by simp
  exact ⟨Q.toPerfectOfCardEq hQleft hQright, by
    simpa using hQcard⟩

/-- Projecting all pendant copies of `U` recovers exactly `U`. -/
@[simp] theorem baseSet_leavesOf
    {X U : Finset V} (hU : U ⊆ X) :
    baseSet (leavesOf (X := X) U hU)
      (leavesOf_subset_leaves U hU) = U := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, _hz, hzx⟩
    rcases Finset.mem_image.mp z.2 with ⟨u, _hu, hzu⟩
    have hleaf :
        leaf (leafValue
          ((leavesOf_subset_leaves (X := X) U hU) z.2)) = z.1 :=
      (leafValue_spec
        ((leavesOf_subset_leaves (X := X) U hU) z.2)).symm
    have hvalue :
        (leafValue
          ((leavesOf_subset_leaves (X := X) U hU) z.2)).1 = u.1 := by
      have heq := hleaf.trans hzu.symm
      injection heq with hsub
      exact congrArg Subtype.val hsub
    have hxu : x = u.1 := hzx.symm.trans hvalue
    simpa [hxu] using u.2
  · simp

/-- Pendant copies preserve disjointness of terminal subsets. -/
theorem leavesOf_disjoint
    {X A B : Finset V} (hA : A ⊆ X) (hB : B ⊆ X)
    (hAB : Disjoint A B) :
    Disjoint (leavesOf (X := X) A hA)
      (leavesOf (X := X) B hB) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzA hzB
  rcases Finset.mem_image.mp hzA with ⟨a, _ha, hza⟩
  rcases Finset.mem_image.mp hzB with ⟨b, _hb, hzb⟩
  have hab : a.1 = b.1 := by
    have heq := hza.trans hzb.symm
    injection heq with hsub
    exact congrArg Subtype.val hsub
  exact Finset.disjoint_left.mp hAB a.2 (by simpa [hab] using b.2)

/-- Inclusion of base terminal sets induces inclusion of their pendant
copies. -/
theorem leavesOf_mono
    {X A B : Finset V} (hA : A ⊆ X) (hB : B ⊆ X)
    (hAB : A ⊆ B) :
    leavesOf (X := X) A hA ⊆ leavesOf (X := X) B hB := by
  classical
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨a, _ha, hza⟩
  refine Finset.mem_image.mpr
    ⟨⟨a.1, hAB a.2⟩, by simp, ?_⟩
  simpa only using hza

/-- Projection of leaf sets is monotone. -/
theorem baseSet_mono
    {X : Finset V}
    {A B : Finset (ChekuriChuzhoyPendantVertex V X)}
    (hA : A ⊆ leaves (V := V) (X := X))
    (hB : B ⊆ leaves (V := V) (X := X))
    (hAB : A ⊆ B) :
    baseSet A hA ⊆ baseSet B hB := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨a, _ha, hax⟩
  have haB : a.1 ∈ B := hAB a.2
  refine Finset.mem_image.mpr
    ⟨⟨a.1, haB⟩, by simp, ?_⟩
  have hvalue :
      leafValue (hA a.2) = leafValue (hB haB) := by
    have hleft := leafValue_spec (hA a.2)
    have hright := leafValue_spec (hB haB)
    have heq := hleft.symm.trans hright
    injection heq
  simpa [hvalue] using hax

/-- Membership in a pendant-copy set is reflected by `leafValue`. -/
theorem leafValue_mem_of_mem_leavesOf
    {X U : Finset V} (hU : U ⊆ X)
    {z : ChekuriChuzhoyPendantVertex V X}
    (hz : z ∈ leavesOf (X := X) U hU) :
    (leafValue ((leavesOf_subset_leaves (X := X) U hU) hz)).1 ∈ U := by
  classical
  rcases Finset.mem_image.mp hz with ⟨u, _hu, hzu⟩
  have hleaf :=
    leafValue_spec ((leavesOf_subset_leaves (X := X) U hU) hz)
  have heq := hzu.trans hleaf
  injection heq with hsub
  have hvalue := congrArg Subtype.val hsub
  rw [← hvalue]
  exact u.2

/-- Output data of Claim 4.8.  The incoming terminals are linked to prescribed
quotas in the two child interfaces, and all paths stay in the current
cluster. -/
structure Claim48QuotaSplitData
    (C A B₁ B₂ : Finset V) (k₁ k₂ : ℕ) where
  leftTargets : Finset V
  rightTargets : Finset V
  leftTargets_subset : leftTargets ⊆ B₁
  rightTargets_subset : rightTargets ⊆ B₂
  leftTargets_card : leftTargets.card = k₁
  rightTargets_card : rightTargets.card = k₂
  targets_disjoint : Disjoint leftTargets rightTargets
  packing :
    PerfectPathPacking G A (leftTargets ∪ rightTargets)
  packing_card : packing.card = A.card
  packing_staysIn : packing.toPathPacking.StaysIn C

/-- Chekuri--Chuzhoy Claim 4.8, in exact integral quota form.

The hypotheses are the two linked child interfaces available at a branching
cluster.  Starting with a full linkage to `B₁` and a `k₂`-linkage to `B₂`,
finite Menger augmentation in the pendant-terminal graph retains the latter
quota and grows the family to all `A.card = k₁ + k₂` incoming terminals. -/
theorem exists_claim48_quotaSplitData
    {C A B₁ B₂ : Finset V} {k₁ k₂ : ℕ}
    (hlink₁ : NodeLinkedIn G C A B₁)
    (hlink₂ : NodeLinkedIn G C A B₂)
    (hB₁B₂ : Disjoint B₁ B₂)
    (hAcard : A.card = k₁ + k₂)
    (hAleB₁ : A.card ≤ B₁.card)
    (hAleB₂ : A.card ≤ B₂.card) :
    Nonempty (Claim48QuotaSplitData (G := G) C A B₁ B₂ k₁ k₂) := by
  classical
  have hk₂A : k₂ ≤ A.card := by omega
  have hk₂B₂ : k₂ ≤ B₂.card := hk₂A.trans hAleB₂
  rcases Finset.exists_subset_card_eq hAleB₁ with
    ⟨B₁full, hB₁full, hB₁fullCard⟩
  rcases Finset.exists_subset_card_eq hk₂B₂ with
    ⟨B₂quota, hB₂quota, hB₂quotaCard⟩
  rcases Finset.exists_subset_card_eq hk₂A with
    ⟨A₂, hA₂, hA₂Card⟩
  have hAB₁full : Disjoint A B₁full :=
    Finset.disjoint_of_subset_right hB₁full hlink₁.2.2.1
  have hA₂B₂quota : Disjoint A₂ B₂quota :=
    Finset.disjoint_of_subset_left hA₂
      (Finset.disjoint_of_subset_right hB₂quota hlink₂.2.2.1)
  have hB₁fullB₂quota : Disjoint B₁full B₂quota :=
    Finset.disjoint_of_subset_left hB₁full
      (Finset.disjoint_of_subset_right hB₂quota hB₁B₂)
  have hAcardB₁full : A.card = B₁full.card :=
    hB₁fullCard.symm
  have hA₂cardB₂quota : A₂.card = B₂quota.card :=
    hA₂Card.trans hB₂quotaCard.symm
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      (hlink₁.mono_terminals subset_rfl hB₁full) hAcardB₁full with
    ⟨P₁, hP₁card, hP₁stay⟩
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      (hlink₂.mono_terminals hA₂ hB₂quota) hA₂cardB₂quota with
    ⟨P₂, hP₂card, hP₂stay⟩
  let H := EdgeMenger.restrictToVertexSet G C
  let P₁H : PerfectPathPacking H A B₁full :=
    PerfectPathPacking.transferToRestrictToVertexSet P₁ hP₁stay
  let P₂H : PerfectPathPacking H A₂ B₂quota :=
    PerfectPathPacking.transferToRestrictToVertexSet P₂ hP₂stay
  let X : Finset V := A ∪ B₁full ∪ B₂quota
  have hAX : A ⊆ X := by
    intro x hx
    simp [X, hx]
  have hA₂X : A₂ ⊆ X := hA₂.trans hAX
  have hB₁X : B₁full ⊆ X := by
    intro x hx
    simp [X, hx]
  have hB₂X : B₂quota ⊆ X := by
    intro x hx
    simp [X, hx]
  have hATargets : Disjoint A (B₁full ∪ B₂quota) := by
    rw [Finset.disjoint_left]
    intro x hxA hxT
    rcases Finset.mem_union.mp hxT with hx₁ | hx₂
    · exact Finset.disjoint_left.mp hAB₁full hxA hx₁
    · exact Finset.disjoint_left.mp
        (Finset.disjoint_of_subset_right hB₂quota hlink₂.2.2.1)
        hxA hx₂
  let SA := leavesOf (X := X) A hAX
  let SA₂ := leavesOf (X := X) A₂ hA₂X
  let TB₁ := leavesOf (X := X) B₁full hB₁X
  let TB₂ := leavesOf (X := X) B₂quota hB₂X
  let TB := TB₁ ∪ TB₂
  have hSA₂SA : SA₂ ⊆ SA := by
    exact leavesOf_mono hA₂X hAX hA₂
  have hTB₁TB : TB₁ ⊆ TB := Finset.subset_union_left
  have hTB₂TB : TB₂ ⊆ TB := Finset.subset_union_right
  have hSATB : Disjoint SA TB := by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    rcases Finset.mem_union.mp hzT with hz₁ | hz₂
    · exact Finset.disjoint_left.mp
        (leavesOf_disjoint hAX hB₁X hAB₁full) hzS hz₁
    · exact Finset.disjoint_left.mp
        (leavesOf_disjoint hAX hB₂X
          (Finset.disjoint_of_subset_right hB₂quota hlink₂.2.2.1))
        hzS hz₂
  have hSAleaves :
      SA ⊆ leaves (V := V) (X := X) :=
    leavesOf_subset_leaves A hAX
  have hTBleaves :
      TB ⊆ leaves (V := V) (X := X) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz₁ | hz₂
    · exact leavesOf_subset_leaves B₁full hB₁X hz₁
    · exact leavesOf_subset_leaves B₂quota hB₂X hz₂
  have hSAdegree :
      ∀ z ∈ SA, DegreeEquals (graph (X := X) H) z 1 := by
    intro z hz
    exact terminal_degree_one (hSAleaves hz)
  have hTBdegree :
      ∀ z ∈ TB, DegreeEquals (graph (X := X) H) z 1 := by
    intro z hz
    exact terminal_degree_one (hTBleaves hz)
  let L₁ : PerfectPathPacking (graph (X := X) H) SA TB₁ :=
    augmentPerfectPathPacking (X := X) hAX hB₁X hAB₁full P₁H
  let L₂ : PerfectPathPacking (graph (X := X) H) SA₂ TB₂ :=
    augmentPerfectPathPacking (X := X) hA₂X hB₂X hA₂B₂quota P₂H
  let large : EndpointCleanPathPacking (graph (X := X) H) SA TB :=
    L₁.toEndpointCleanInOfTerminalDegreeOne
      subset_rfl hTB₁TB hSATB hSAdegree hTBdegree
  let small : EndpointCleanPathPacking (graph (X := X) H) SA TB :=
    L₂.toEndpointCleanInOfTerminalDegreeOne
      hSA₂SA hTB₂TB hSATB hSAdegree hTBdegree
  have hsmalllarge : small.card ≤ large.card := by
    calc
      small.card = L₂.card := rfl
      _ = SA₂.card := L₂.card_eq_left_card
      _ = A₂.card := by simp [SA₂]
      _ ≤ A.card := Finset.card_le_card hA₂
      _ = SA.card := by simp [SA]
      _ = L₁.card := L₁.card_eq_left_card.symm
      _ = large.card := rfl
  rcases EndpointCleanPathPacking.exists_extension_to_witness_card
      small large hsmalllarge with
    ⟨R, hRcard, _hRsource, hRtarget⟩
  have hTB₂R : TB₂ ⊆ R.targetSet := by
    have hsmallTarget : small.targetSet = TB₂ := by
      simp [small, L₂]
    simpa [hsmallTarget] using hRtarget
  rcases exists_projected_pendant_perfectPathPacking
      (G := H) R hSAleaves hTBleaves hSATB with
    ⟨Q, hQcard⟩
  let hRS :
      R.sourceSet ⊆ leaves (V := V) (X := X) :=
    subset_trans R.sourceSet_subset_left hSAleaves
  let hRT :
      R.targetSet ⊆ leaves (V := V) (X := X) :=
    subset_trans R.targetSet_subset_right hTBleaves
  let sourceBase : Finset V := baseSet R.sourceSet hRS
  let targetBase : Finset V := baseSet R.targetSet hRT
  have hRcardA : R.card = A.card := by
    calc
      R.card = large.card := hRcard
      _ = L₁.card := rfl
      _ = SA.card := L₁.card_eq_left_card
      _ = A.card := leavesOf_card A hAX
  have hRsourceEq : R.sourceSet = SA := by
    apply Finset.eq_of_subset_of_card_le R.sourceSet_subset_left
    rw [R.sourceSet_card, hRcardA, show SA.card = A.card by simp [SA]]
  have hsourceBase : sourceBase = A := by
    dsimp [sourceBase, hRS]
    simpa [hRsourceEq, SA] using (baseSet_leavesOf hAX)
  have htargetBaseSubset : targetBase ⊆ B₁full ∪ B₂quota := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, _hz, hzx⟩
    have hzTB : z.1 ∈ TB := R.targetSet_subset_right z.2
    rcases Finset.mem_union.mp hzTB with hz₁ | hz₂
    · exact Finset.mem_union_left _
        (by
          rw [← hzx]
          exact leafValue_mem_of_mem_leavesOf hB₁X hz₁)
    · exact Finset.mem_union_right _
        (by
          rw [← hzx]
          exact leafValue_mem_of_mem_leavesOf hB₂X hz₂)
  have hB₂targetBase : B₂quota ⊆ targetBase := by
    have hmono :=
      baseSet_mono
        (leavesOf_subset_leaves B₂quota hB₂X) hRT hTB₂R
    simpa [targetBase] using hmono
  let D₂ : Finset V := B₂quota
  let D₁ : Finset V := targetBase \ D₂
  have hD₁B₁ : D₁ ⊆ B₁ := by
    intro x hx
    have hxBase := (Finset.mem_sdiff.mp hx).1
    have hxNotD₂ := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_union.mp (htargetBaseSubset hxBase) with hx₁ | hx₂
    · exact hB₁full hx₁
    · exact False.elim (hxNotD₂ hx₂)
  have hD₂B₂ : D₂ ⊆ B₂ := by
    exact hB₂quota
  have hD₁D₂ : Disjoint D₁ D₂ := Finset.sdiff_disjoint
  have htargetUnion : D₁ ∪ D₂ = targetBase := by
    rw [Finset.sdiff_union_of_subset]
    exact hB₂targetBase
  have htargetBaseCard : targetBase.card = A.card := by
    calc
      targetBase.card = R.targetSet.card := baseSet_card _ _
      _ = R.card := R.targetSet_card
      _ = A.card := hRcardA
  have hD₂card : D₂.card = k₂ := by
    exact hB₂quotaCard
  have hD₁card : D₁.card = k₁ := by
    have hcard :
        D₁.card + D₂.card = targetBase.card := by
      rw [← htargetUnion, Finset.card_union_of_disjoint hD₁D₂]
    omega
  let Q' : PerfectPathPacking H A (D₁ ∪ D₂) :=
    Q.copyTerminals hsourceBase htargetUnion.symm
  have hQ'stay : Q'.toPathPacking.StaysIn C := by
    intro i x hx
    exact
      EdgeMenger.restrictToVertexSet_path_vertexSet_subset
        (G := G) (P := Q'.path i)
        (hlink₁.1 (Q'.source_mem i)) hx
  let QG : PerfectPathPacking G A (D₁ ∪ D₂) :=
    Q'.mapLe (EdgeMenger.restrictToVertexSet_le G C)
  exact ⟨{
    leftTargets := D₁
    rightTargets := D₂
    leftTargets_subset := hD₁B₁
    rightTargets_subset := hD₂B₂
    leftTargets_card := hD₁card
    rightTargets_card := hD₂card
    targets_disjoint := hD₁D₂
    packing := QG
    packing_card := by
      dsimp [QG, Q']
      simpa using hQcard.trans hRcardA
    packing_staysIn := by
      intro i x hx
      change x ∈ ((Q'.path i).mapLe
        (EdgeMenger.restrictToVertexSet_le G C)).vertexSet at hx
      rw [GraphPath.mapLe_vertexSet] at hx
      exact hQ'stay i hx }⟩

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
