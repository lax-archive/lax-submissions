import Lax17Proofs.Source.TreewidthSparsifierTheorem51RailOwner

namespace Lax17Proofs

universe u v w

/-!
# The whole-rail quotient for Theorem 5.1

This module contracts the complete red rails constructed by the physical
cut-matching transcript.  Parallel physical edges are retained as named
edges.  The quotient is used only for cut counting, so contracting whole rails
is sufficient; the short-segment refinement in the algorithmic source is
needed only for its routing lift.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame
open ChekuriChuzhoySection5TerminalSkeleton


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

/-- Physical edges whose two rail owners differ. -/
noncomputable def ownerCrossingEdges
    (H : _root_.SimpleGraph V) (owner : V → Fin h) :
    Finset (Sym2 V) := by
  classical
  exact H.edgeFinset.filter fun e =>
    owner e.out.1 ≠ owner e.out.2

/-- The physical edge represented by a canonical finite index. -/
noncomputable def ownerCrossingEdgeAt
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (i : Fin (ownerCrossingEdges H owner).card) : Sym2 V :=
  ((ownerCrossingEdges H owner).equivFin.symm i).1

/-- Named non-loop edges obtained from a same-vertex graph by applying a
vertex-owner map.  The `Fin` edge index keeps the multigraph API universe
independent of the host vertex universe.  `Sym2.out` merely chooses an
orientation; every physical edge still occurs exactly once. -/
noncomputable def ownerQuotient
    (H : _root_.SimpleGraph V) (owner : V → Fin h) :
    FiniteEdgeIndexedGraph (Fin h) := by
  classical
  exact {
    Edge := Fin (ownerCrossingEdges H owner).card
    left := fun e => owner (ownerCrossingEdgeAt H owner e).out.1
    right := fun e => owner (ownerCrossingEdgeAt H owner e).out.2
    end_ne := by
      intro e
      exact Finset.mem_filter.mp
        ((ownerCrossingEdges H owner).equivFin.symm e).2 |>.2
  }

/-- The physical vertices whose owner lies in an abstract vertex set. -/
noncomputable def ownerSide
    (owner : V → Fin h) (S : Finset (Fin h)) : Finset V := by
  classical
  exact Finset.univ.filter fun v => owner v ∈ S

@[simp] theorem mem_ownerSide
    (owner : V → Fin h) (S : Finset (Fin h)) (v : V) :
    v ∈ ownerSide owner S ↔ owner v ∈ S := by
  classical
  simp [ownerSide]

/-- The canonical quotient index of a physical owner-crossing edge. -/
noncomputable def ownerQuotientIndex
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (e : Sym2 V) (he : e ∈ ownerCrossingEdges H owner) :
    (ownerQuotient H owner).Edge :=
  (ownerCrossingEdges H owner).equivFin
    ⟨e, he⟩

@[simp] theorem ownerCrossingEdgeAt_ownerQuotientIndex
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (e : Sym2 V) (he : e ∈ ownerCrossingEdges H owner) :
    ownerCrossingEdgeAt H owner
      (ownerQuotientIndex H owner e he) = e := by
  classical
  exact congrArg Subtype.val
    ((ownerCrossingEdges H owner).equivFin.symm_apply_apply
      ⟨e, he⟩)

/-- A physical edge across the two owner sides has owner endpoints across the
corresponding abstract cut, independently of the orientation selected by
`Sym2.out`. -/
theorem owner_crosses_of_mem_edgeBoundary_ownerSides
    (K : _root_.SimpleGraph V) (owner : V → Fin h)
    (S : Finset (Fin h)) (e : Sym2 V)
    (he : e ∈ Section44.edgeBoundary K
      (ownerSide owner S) (ownerSide owner Sᶜ)) :
    (owner e.out.1 ∈ S ∧ owner e.out.2 ∉ S) ∨
      (owner e.out.2 ∈ S ∧ owner e.out.1 ∉ S) := by
  rcases
      (Section44.mem_edgeBoundary
        (G := K) (ownerSide owner S) (ownerSide owner Sᶜ) e).mp he with
    ⟨_heK, a, ha, b, hb, heab⟩
  have haS : owner a ∈ S := (mem_ownerSide owner S a).mp ha
  have hbS : owner b ∉ S := by
    have := (mem_ownerSide owner Sᶜ b).mp hb
    simpa using this
  have hout : s(e.out.1, e.out.2) = s(a, b) := by
    calc
      s(e.out.1, e.out.2) = e := by
        rw [Sym2.mk, e.out_eq]
      _ = s(a, b) := heab
  rw [Sym2.eq_iff] at hout
  rcases hout with h | h
  · exact Or.inl ⟨h.1 ▸ haS, by simpa [h.2] using hbS⟩
  · exact Or.inr ⟨h.2 ▸ haS, by simpa [h.1] using hbS⟩

/-- The canonical quotient index of an owner-crossing physical edge crosses
the same abstract cut. -/
theorem ownerQuotientIndex_crosses
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (S : Finset (Fin h)) (e : Sym2 V)
    (he : e ∈ ownerCrossingEdges H owner)
    (hcross :
      (owner e.out.1 ∈ S ∧ owner e.out.2 ∉ S) ∨
        (owner e.out.2 ∈ S ∧ owner e.out.1 ∉ S)) :
    (ownerQuotient H owner).Crosses S
      (ownerQuotientIndex H owner e he) := by
  change
    (owner (ownerCrossingEdgeAt H owner
          (ownerQuotientIndex H owner e he)).out.1 ∈ S ∧
        owner (ownerCrossingEdgeAt H owner
          (ownerQuotientIndex H owner e he)).out.2 ∉ S) ∨
      (owner (ownerCrossingEdgeAt H owner
          (ownerQuotientIndex H owner e he)).out.2 ∈ S ∧
        owner (ownerCrossingEdgeAt H owner
          (ownerQuotientIndex H owner e he)).out.1 ∉ S)
  simpa using hcross

namespace BuildState.ExpanderBlocks

/-- The physical blue path realizing a matching edge of record `j`. -/
noncomputable def localBluePath
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left}) :
    GraphPath (E.recordAt j).layer.localGraph :=
  let R := E.recordAt j
  R.layer.blue.path
    (R.layer.blue.indexOfSource
      (labelledImageEquiv R.label R.cut.left x))

@[simp] theorem localBluePath_source
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left}) :
    (E.localBluePath j x).source =
      ((E.recordAt j).label x.1).1 := by
  have hs := congrArg Subtype.val
    ((E.recordAt j).layer.blue.source_indexOfSource
      (labelledImageEquiv
        (E.recordAt j).label (E.recordAt j).cut.left x))
  simpa [localBluePath, labelledImageEquiv] using hs

@[simp] theorem localBluePath_target
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left}) :
    (E.localBluePath j x).target =
      ((E.recordAt j).label
        ((E.recordAt j).round.matching.rightEndpoint x)).1 := by
  let i :=
    (E.recordAt j).layer.blue.indexOfSource
      (labelledImageEquiv
        (E.recordAt j).label (E.recordAt j).cut.left x)
  let y :=
    (labelledImageEquiv
      (E.recordAt j).label (E.recordAt j).cut.right).symm
      ((E.recordAt j).layer.blue.targetEquiv i)
  change
    ((E.recordAt j).layer.blue.path i).target =
      ((E.recordAt j).label y.1).1
  have h :=
    (labelledImageEquiv
      (E.recordAt j).label (E.recordAt j).cut.right).apply_symm_apply
      ((E.recordAt j).layer.blue.targetEquiv i)
  exact (congrArg Subtype.val h).symm

/-- The owner of a blue path's source is its abstract matching source. -/
theorem railOwner_localBluePath_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h)
    (j : Fin E.finalState.records.length)
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left}) :
    E.railOwner hbudget fallback (E.localBluePath j x).source = x.1 := by
  apply E.railOwner_eq_of_redCarrier hbudget fallback
  left
  refine ⟨j, ?_⟩
  rw [E.localBluePath_source, ← E.localRedPath_source j x.1]
  exact GraphPath.source_mem_vertexSet _

/-- The owner of a blue path's target is its abstract matching target. -/
theorem railOwner_localBluePath_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h)
    (j : Fin E.finalState.records.length)
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left}) :
    E.railOwner hbudget fallback (E.localBluePath j x).target =
      (E.recordAt j).round.matching.rightEndpoint x := by
  apply E.railOwner_eq_of_redCarrier hbudget fallback
  left
  refine ⟨j, ?_⟩
  rw [E.localBluePath_target,
    ← E.localRedPath_source j
      ((E.recordAt j).round.matching.rightEndpoint x)]
  exact GraphPath.source_mem_vertexSet _

/-- The whole-rail quotient of any selected same-vertex support graph. -/
noncomputable def railQuotient
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (H : _root_.SimpleGraph V) :
    FiniteEdgeIndexedGraph (Fin h) :=
  ownerQuotient H (E.railOwner hbudget fallback)

/-- Every local graph selected by a record is present in the assembled
red/blue support. -/
theorem recordAt_localGraph_le_assembledSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length) :
    (E.recordAt j).layer.localGraph ≤ E.assembledSupport hbudget := by
  rw [(E.recordAt j).layer.support_eq]
  apply sup_le
  · exact
      ((le_iSup
          (fun k : Fin E.finalState.records.length =>
            (E.recordAt k).layer.red.toPathPacking.spanningGraph) j).trans
        le_sup_left).trans le_sup_left
  · exact
      (le_iSup
          (fun k : Fin E.finalState.records.length =>
            (E.recordAt k).layer.blue.toPathPacking.spanningGraph) j).trans
        le_sup_right

/-- Every vertex of a local blue path lies in its record's cluster. -/
theorem localBluePath_vertex_mem_cluster
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left})
    {v : V} (hv : v ∈ (E.localBluePath j x).vertexSet) :
    v ∈ P.cluster (E.recordAt j).index := by
  have hne :
      (E.localBluePath j x).source ≠
        (E.localBluePath j x).target := by
    intro heq
    have hleft : x.1 ∈ (E.recordAt j).cut.left := x.2
    have hright :
        (E.recordAt j).round.matching.rightEndpoint x ∈
          (E.recordAt j).cut.right :=
      (E.recordAt j).round.matching.rightEndpoint_mem x
    exact (E.recordAt j).cut.not_mem_left_of_mem_right hright
      (by
        have howners := congrArg
          (E.railOwner hbudget x.1) heq
        rw [E.railOwner_localBluePath_source hbudget x.1 j x,
          E.railOwner_localBluePath_target hbudget x.1 j x] at howners
        simpa [howners] using hleft)
  rcases
      (E.localBluePath j x)
        |>.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
          hne hv with
    ⟨e, he, hve⟩
  rcases Sym2.mem_iff_exists.mp hve with ⟨w, rfl⟩
  have hadj :
      (E.recordAt j).layer.localGraph.Adj v w := by
    simpa using GraphPath.edgeSet_subset_edgeSet
      (E.localBluePath j x) he
  exact ((E.recordAt j).layer.localGraph_le_induced hadj).2.1

/-- Distinct abstract matching sources select distinct blue paths in one
record. -/
theorem localBluePath_index_injective
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) :
    Function.Injective
      (fun x : {x : Fin h // x ∈ (E.recordAt j).cut.left} =>
        (E.recordAt j).layer.blue.indexOfSource
          (labelledImageEquiv
            (E.recordAt j).label (E.recordAt j).cut.left x)) := by
  intro x y hxy
  have hsource := congrArg
    (fun i => ((E.recordAt j).layer.blue.path i).source) hxy
  apply Subtype.ext
  have hx := E.localBluePath_source j x
  have hy := E.localBluePath_source j y
  apply (E.recordAt j).label.injective
  apply Subtype.ext
  exact hx.symm.trans (hsource.trans hy)

/-- Blue paths in one record have a unique abstract matching source. -/
theorem localBluePath_label_unique
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    {x y : {x : Fin h // x ∈ (E.recordAt j).cut.left}}
    {v : V}
    (hvx : v ∈ (E.localBluePath j x).vertexSet)
    (hvy : v ∈ (E.localBluePath j y).vertexSet) :
    x = y := by
  by_contra hxy
  have hindex :
      (E.recordAt j).layer.blue.indexOfSource
          (labelledImageEquiv
            (E.recordAt j).label (E.recordAt j).cut.left x) ≠
        (E.recordAt j).layer.blue.indexOfSource
          (labelledImageEquiv
            (E.recordAt j).label (E.recordAt j).cut.left y) :=
    fun h => hxy (E.localBluePath_index_injective j h)
  exact Finset.disjoint_left.mp
    ((E.recordAt j).layer.blue.node_disjoint hindex) hvx hvy

/-- Blue paths in different realized records are disjoint. -/
theorem localBluePath_record_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {j k : Fin E.finalState.records.length}
    {x : {x : Fin h // x ∈ (E.recordAt j).cut.left}}
    {y : {x : Fin h // x ∈ (E.recordAt k).cut.left}}
    {v : V}
    (hvx : v ∈ (E.localBluePath j x).vertexSet)
    (hvy : v ∈ (E.localBluePath k y).vertexSet) :
    j = k := by
  have hvj := E.localBluePath_vertex_mem_cluster hbudget j x hvx
  have hvk := E.localBluePath_vertex_mem_cluster hbudget k y hvy
  have hindex : (E.recordAt j).index = (E.recordAt k).index := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvj hvk
  apply Fin.ext
  rw [← E.recordAt_index_eq hbudget j,
    ← E.recordAt_index_eq hbudget k]
  exact congrArg Fin.val hindex

/-- Every abstract matching edge crossing `S` contributes a named edge of the
whole-rail quotient crossing `S`.  The named quotient edge is represented by
an actual edge of the corresponding physical blue path. -/
theorem exists_railQuotient_edge_of_localBlue_crosses
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h)
    (j : Fin E.finalState.records.length)
    (S : Finset (Fin h))
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left})
    (hcross : (E.recordAt j).round.edgeCrosses S x) :
    ∃ q :
        (ownerQuotient (E.assembledSupport hbudget)
          (E.railOwner hbudget fallback)).Edge,
      (ownerQuotient (E.assembledSupport hbudget)
          (E.railOwner hbudget fallback)).Crosses S q ∧
        ownerCrossingEdgeAt
            (E.assembledSupport hbudget)
            (E.railOwner hbudget fallback) q ∈
          (E.localBluePath j x).edgeSet := by
  classical
  let owner := E.railOwner hbudget fallback
  let A := ownerSide owner S
  let D := ownerSide owner Sᶜ
  have hcover : A ∪ D = (Finset.univ : Finset V) := by
    ext v
    by_cases hv : owner v ∈ S <;>
      simp [A, D, ownerSide, hv]
  have hsub : (E.localBluePath j x).vertexSet ⊆ A ∪ D := by
    rw [hcover]
    exact Finset.subset_univ _
  have hsourceOwner :
      owner (E.localBluePath j x).source = x.1 :=
    E.railOwner_localBluePath_source hbudget fallback j x
  have htargetOwner :
      owner (E.localBluePath j x).target =
        (E.recordAt j).round.matching.rightEndpoint x :=
    E.railOwner_localBluePath_target hbudget fallback j x
  have hedge :
      ∃ e ∈ (E.localBluePath j x).edgeSet,
        e ∈ Section44.edgeBoundary
          (E.recordAt j).layer.localGraph A D := by
    rcases hcross with hcross | hcross
    · have hsourceA : (E.localBluePath j x).source ∈ A := by
        apply (mem_ownerSide owner S _).mpr
        rw [hsourceOwner]
        exact hcross.1
      have htargetNotA :
          (E.localBluePath j x).target ∉ A := by
        rw [mem_ownerSide, htargetOwner]
        exact hcross.2
      exact
        Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
          (E.localBluePath j x) hsub hsourceA
          (fun h => htargetNotA
            (h (GraphPath.target_mem_vertexSet _)))
    · have htargetA : (E.localBluePath j x).target ∈ A := by
        apply (mem_ownerSide owner S _).mpr
        rw [htargetOwner]
        exact hcross.1
      have hsourceNotA :
          (E.localBluePath j x).source ∉ A := by
        rw [mem_ownerSide, hsourceOwner]
        exact hcross.2
      exact
        Section44.GraphPath.exists_edgeBoundary_of_target_mem_left_of_not_subset_left
          (E.localBluePath j x) hsub htargetA
          (fun h => hsourceNotA
            (h (GraphPath.source_mem_vertexSet _)))
  rcases hedge with ⟨e, hePath, heBoundary⟩
  have heLocal : e ∈ (E.recordAt j).layer.localGraph.edgeSet :=
    GraphPath.edgeSet_subset_edgeSet (E.localBluePath j x) hePath
  have heAssembled : e ∈ (E.assembledSupport hbudget).edgeSet :=
    _root_.SimpleGraph.edgeSet_mono
      (E.recordAt_localGraph_le_assembledSupport hbudget j) heLocal
  have howners :=
    owner_crosses_of_mem_edgeBoundary_ownerSides
      (E.recordAt j).layer.localGraph owner S e heBoundary
  have hne : owner e.out.1 ≠ owner e.out.2 := by
    intro heq
    rcases howners with h | h
    · exact h.2 (heq ▸ h.1)
    · exact h.2 (heq.symm ▸ h.1)
  have heCrossing :
      e ∈ ownerCrossingEdges
        (E.assembledSupport hbudget) owner := by
    exact Finset.mem_filter.mpr
      ⟨_root_.SimpleGraph.mem_edgeFinset.mpr heAssembled, hne⟩
  let q :=
    ownerQuotientIndex
      (E.assembledSupport hbudget) owner e heCrossing
  refine ⟨q, ?_, ?_⟩
  · exact ownerQuotientIndex_crosses
      (E.assembledSupport hbudget) owner S e heCrossing howners
  · change
      ownerCrossingEdgeAt (E.assembledSupport hbudget) owner q ∈
        (E.localBluePath j x).edgeSet
    rw [show q =
      ownerQuotientIndex
        (E.assembledSupport hbudget) owner e heCrossing by rfl,
      ownerCrossingEdgeAt_ownerQuotientIndex]
    exact hePath

/-- Matching-boundary instances indexed by the realized physical record
list. -/
abbrev RecordBoundary
    (E : ExpanderBlocks P count) (S : Finset (Fin h)) :=
  Σ j : Fin E.finalState.records.length,
    {x :
        {x : Fin h // x ∈ (E.recordAt j).cut.left} //
      x ∈ (E.recordAt j).round.edgeBoundary S}

/-- Select one physical quotient edge from each abstract matching-boundary
instance. -/
noncomputable def recordBoundaryQuotientEdge
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (S : Finset (Fin h))
    (z : E.RecordBoundary S) :
    (ownerQuotient (E.assembledSupport hbudget)
      (E.railOwner hbudget fallback)).Edge :=
  Classical.choose
    (E.exists_railQuotient_edge_of_localBlue_crosses
      hbudget fallback z.1 S z.2.1
      (LazyRound.mem_edgeBoundary.mp z.2.2))

theorem recordBoundaryQuotientEdge_crosses
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (S : Finset (Fin h))
    (z : E.RecordBoundary S) :
    (ownerQuotient (E.assembledSupport hbudget)
      (E.railOwner hbudget fallback)).Crosses S
        (E.recordBoundaryQuotientEdge hbudget fallback S z) :=
  (Classical.choose_spec
    (E.exists_railQuotient_edge_of_localBlue_crosses
      hbudget fallback z.1 S z.2.1
      (LazyRound.mem_edgeBoundary.mp z.2.2))).1

theorem recordBoundaryQuotientEdge_mem_localBluePath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (S : Finset (Fin h))
    (z : E.RecordBoundary S) :
    ownerCrossingEdgeAt
        (E.assembledSupport hbudget)
        (E.railOwner hbudget fallback)
        (E.recordBoundaryQuotientEdge hbudget fallback S z) ∈
      (E.localBluePath z.1 z.2.1).edgeSet :=
  (Classical.choose_spec
    (E.exists_railQuotient_edge_of_localBlue_crosses
      hbudget fallback z.1 S z.2.1
      (LazyRound.mem_edgeBoundary.mp z.2.2))).2

/-- Distinct abstract boundary instances select distinct named quotient
edges.  Different records occupy disjoint clusters; within one record the
blue paths are node-disjoint. -/
theorem recordBoundaryQuotientEdge_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (S : Finset (Fin h)) :
    Function.Injective
      (E.recordBoundaryQuotientEdge hbudget fallback S) := by
  classical
  rintro ⟨j, x⟩ ⟨k, y⟩ hq
  let e :=
    ownerCrossingEdgeAt
      (E.assembledSupport hbudget)
      (E.railOwner hbudget fallback)
      (E.recordBoundaryQuotientEdge hbudget fallback S ⟨j, x⟩)
  have hex :
      e ∈ (E.localBluePath j x.1).edgeSet := by
    exact E.recordBoundaryQuotientEdge_mem_localBluePath
      hbudget fallback S ⟨j, x⟩
  have hey :
      e ∈ (E.localBluePath k y.1).edgeSet := by
    have hy := E.recordBoundaryQuotientEdge_mem_localBluePath
      hbudget fallback S ⟨k, y⟩
    simpa [e, hq] using hy
  have heout : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  have hex' :
      s(e.out.1, e.out.2) ∈ (E.localBluePath j x.1).edgeSet := by
    simpa [heout] using hex
  have hey' :
      s(e.out.1, e.out.2) ∈ (E.localBluePath k y.1).edgeSet := by
    simpa [heout] using hey
  have hvx :
      e.out.1 ∈ (E.localBluePath j x.1).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath j x.1) hex').1
  have hvy :
      e.out.1 ∈ (E.localBluePath k y.1).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath k y.1) hey').1
  have hjk := E.localBluePath_record_unique hbudget hvx hvy
  subst k
  have hxy : x.1 = y.1 :=
    E.localBluePath_label_unique j hvx hvy
  have hxy' : x = y := Subtype.ext hxy
  subst y
  rfl

/-- The record-indexed boundary type has exactly the flattened transcript's
boundary count. -/
theorem recordBoundary_card_eq_edgeBoundaryCount
    (E : ExpanderBlocks P count) (S : Finset (Fin h)) :
    Fintype.card (E.RecordBoundary S) =
      edgeBoundaryCount (List.ofFn E.rounds).flatten S := by
  classical
  calc
    Fintype.card (E.RecordBoundary S) =
        ∑ j : Fin E.finalState.records.length,
          ((E.recordAt j).round.edgeBoundary S).card := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.refl _)
    _ = (List.ofFn fun j : Fin E.finalState.records.length =>
          ((E.recordAt j).round.edgeBoundary S).card).sum := by
      rw [List.sum_ofFn]
    _ = (E.finalState.records.map fun R =>
          (R.round.edgeBoundary S).card).sum := by
      congr 1
      calc
        List.ofFn (fun j : Fin E.finalState.records.length =>
            ((E.recordAt j).round.edgeBoundary S).card) =
            (List.ofFn E.finalState.records.get).map
              (fun R => (R.round.edgeBoundary S).card) := by
                rw [List.map_ofFn]
                rfl
        _ = E.finalState.records.map
              (fun R => (R.round.edgeBoundary S).card) := by
                rw [List.ofFn_get]
    _ = edgeBoundaryCount (BuildState.trace P E.finalState) S := by
      simp [BuildState.trace, edgeBoundaryCount, List.map_map,
        Function.comp_def]
    _ = edgeBoundaryCount (List.ofFn E.rounds).flatten S := by
      rw [E.trace_eq]

/-- Abstract matching-boundary instances inject into the corresponding
quotient cut. -/
theorem recordBoundary_card_le_railQuotient_boundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (S : Finset (Fin h)) :
    Fintype.card (E.RecordBoundary S) ≤
      ((E.railQuotient hbudget fallback
        (E.assembledSupport hbudget)).boundary S).card := by
  classical
  let f :
      E.RecordBoundary S →
        {q :
            (E.railQuotient hbudget fallback
              (E.assembledSupport hbudget)).Edge //
          q ∈
            (E.railQuotient hbudget fallback
              (E.assembledSupport hbudget)).boundary S} :=
    fun z =>
      ⟨E.recordBoundaryQuotientEdge hbudget fallback S z,
        FiniteEdgeIndexedGraph.mem_boundary
          (E.railQuotient hbudget fallback
            (E.assembledSupport hbudget)) S _
          |>.mpr (E.recordBoundaryQuotientEdge_crosses
            hbudget fallback S z)⟩
  have hf : Function.Injective f := by
    intro z w h
    apply E.recordBoundaryQuotientEdge_injective hbudget fallback S
    exact congrArg Subtype.val h
  calc
    Fintype.card (E.RecordBoundary S) ≤
        Fintype.card
          {q :
              (E.railQuotient hbudget fallback
                (E.assembledSupport hbudget)).Edge //
            q ∈
              (E.railQuotient hbudget fallback
                (E.assembledSupport hbudget)).boundary S} :=
      Fintype.card_le_of_injective f hf
    _ = ((E.railQuotient hbudget fallback
          (E.assembledSupport hbudget)).boundary S).card := by
      calc
        Fintype.card
            {q :
                (E.railQuotient hbudget fallback
                  (E.assembledSupport hbudget)).Edge //
              q ∈
                (E.railQuotient hbudget fallback
                  (E.assembledSupport hbudget)).boundary S} =
            Fintype.card
              (Fin
                ((E.railQuotient hbudget fallback
                  (E.assembledSupport hbudget)).boundary S).card) :=
          Fintype.card_congr
            ((E.railQuotient hbudget fallback
              (E.assembledSupport hbudget)).boundary S).equivFin
        _ = ((E.railQuotient hbudget fallback
              (E.assembledSupport hbudget)).boundary S).card :=
          Fintype.card_fin _

/-- The unthinned whole-rail quotient has edge connectivity at least half the
number of independently restarted half-expanders. -/
theorem railQuotient_isEdgeConnected
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) :
    (E.railQuotient hbudget fallback
      (E.assembledSupport hbudget)).IsEdgeConnected (count / 2) := by
  classical
  intro S hS hproper
  have hScard : S.card ≤ h := by
    simpa using Finset.card_le_univ S
  by_cases hhalf : 2 * S.card ≤ h
  · have hexpand :=
      count_mul_card_le_two_mul_edgeBoundaryCount P E S
        (Finset.card_pos.mpr hS) hhalf
    have hcount : count ≤
        2 * edgeBoundaryCount (List.ofFn E.rounds).flatten S := by
      exact (Nat.le_mul_of_pos_right count
        (Finset.card_pos.mpr hS)).trans hexpand
    have hrecord :
        edgeBoundaryCount (List.ofFn E.rounds).flatten S ≤
          ((E.railQuotient hbudget fallback
            (E.assembledSupport hbudget)).boundary S).card := by
      rw [← E.recordBoundary_card_eq_edgeBoundaryCount S]
      exact E.recordBoundary_card_le_railQuotient_boundary
        hbudget fallback S
    omega
  · have hcomp : (Sᶜ : Finset (Fin h)).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hc
      apply hproper
      have hc' := congrArg (fun T : Finset (Fin h) => Tᶜ) hc
      simpa using hc'
    have hcompCard :
        (Sᶜ : Finset (Fin h)).card = h - S.card := by
      simpa using Finset.card_compl S
    have hcompHalf : 2 * (Sᶜ : Finset (Fin h)).card ≤ h := by
      omega
    have hexpand :=
      count_mul_card_le_two_mul_edgeBoundaryCount P E Sᶜ
        (Finset.card_pos.mpr hcomp) hcompHalf
    have hcount : count ≤
        2 * edgeBoundaryCount
          (List.ofFn E.rounds).flatten Sᶜ := by
      exact (Nat.le_mul_of_pos_right count
        (Finset.card_pos.mpr hcomp)).trans hexpand
    have hrecord :
        edgeBoundaryCount (List.ofFn E.rounds).flatten Sᶜ ≤
          ((E.railQuotient hbudget fallback
            (E.assembledSupport hbudget)).boundary Sᶜ).card := by
      rw [← E.recordBoundary_card_eq_edgeBoundaryCount Sᶜ]
      exact E.recordBoundary_card_le_railQuotient_boundary
        hbudget fallback Sᶜ
    rw [FiniteEdgeIndexedGraph.boundary_compl] at hrecord
    omega

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
