import Lax17Proofs.Source.TreewidthSparsifierTheorem51SegmentLinks

namespace Lax17Proofs

universe u v w

/-!
# Lower-tail concentration for complete suppressed blue links

Chekuri--Chuzhoy, *Degree-3 Treewidth Sparsifiers*, Theorem 5.1, Step 2.
After contracting red segments, one blue quotient edge represents the whole
blue subpath between two consecutive red intersections.  This file proves the
fixed-cut estimate for those complete subpaths.  The endpoint-disjoint
subfamily supplied by `TreewidthSparsifierTheorem51SegmentLinks` makes their
two endpoint choices independent; carrier cleanliness shows that these are
the only choices capable of deleting an edge of the subpath.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame
open ThinningConcentration


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count t : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks
namespace SegmentLinkFamily

variable (E : ExpanderBlocks P count)
variable (hbudget :
  count *
      (realizedRoundConstant *
        Nat.log 2 h) ≤ ell)
variable (hrecords : 0 < E.finalState.records.length)
variable (B : ℕ) (hB : 0 < B)
variable (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
variable
  (M : Finset
    (E.BlueSegmentTransition hbudget hrecords B hB fallback))
variable
  (hdisjoint :
    E.BlueSegmentTransitionFamilyVertexDisjoint
      hbudget hrecords B hB fallback M)
variable (hcard : M.card = 16 * t)

/-- Canonical enumeration of an exact `16t` transition subfamily. -/
noncomputable def transitionAt (i : Fin (16 * t)) :
    E.BlueSegmentTransition hbudget hrecords B hB fallback :=
  (M.equivFin.symm (Fin.cast hcard.symm i)).1

theorem transitionAt_mem (i : Fin (16 * t)) :
    transitionAt E hbudget hrecords B hB fallback M hcard i ∈ M :=
  (M.equivFin.symm (Fin.cast hcard.symm i)).2

theorem transitionAt_injective :
    Function.Injective
      (transitionAt E hbudget hrecords B hB fallback M hcard) := by
  intro i j hij
  have hsub :
      M.equivFin.symm (Fin.cast hcard.symm i) =
        M.equivFin.symm (Fin.cast hcard.symm j) :=
    Subtype.ext hij
  have hcast :
      Fin.cast hcard.symm i = Fin.cast hcard.symm j :=
    M.equivFin.symm.injective hsub
  exact Fin.cast_injective hcard.symm hcast

/-- Complete physical blue link at index `i`. -/
noncomputable def linkAt (i : Fin (16 * t)) :
    GraphPath (E.assembledSupport hbudget) :=
  E.blueSegmentTransitionPath hbudget hrecords B hB fallback
    (transitionAt E hbudget hrecords B hB fallback M hcard i)

theorem linkAt_source_ne_target (i : Fin (16 * t)) :
    (linkAt E hbudget hrecords B hB fallback M hcard i).source ≠
      (linkAt E hbudget hrecords B hB fallback M hcard i).target :=
  E.blueSegmentTransitionPath_source_ne_target
    hbudget hrecords B hB fallback
    (transitionAt E hbudget hrecords B hB fallback M hcard i)

/-- Endpoint zero is the source and endpoint one is the target. -/
noncomputable def endpoint (i : Fin (16 * t)) (k : Fin 2) : V :=
  if k = 0 then
    (linkAt E hbudget hrecords B hB fallback M hcard i).source
  else
    (linkAt E hbudget hrecords B hB fallback M hcard i).target

theorem endpoint_mem_vertexSet (i : Fin (16 * t)) (k : Fin 2) :
    endpoint E hbudget hrecords B hB fallback M hcard i k ∈
      (linkAt E hbudget hrecords B hB fallback M hcard i).vertexSet := by
  fin_cases k
  · exact GraphPath.source_mem_vertexSet _
  · exact GraphPath.target_mem_vertexSet _

theorem endpoint_isEndpoint (i : Fin (16 * t)) (k : Fin 2) :
    (linkAt E hbudget hrecords B hB fallback M hcard i).IsEndpoint
      (endpoint E hbudget hrecords B hB fallback M hcard i k) := by
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem endpoint_mem_transitionEndpoints
    (i : Fin (16 * t)) (k : Fin 2) :
    endpoint E hbudget hrecords B hB fallback M hcard i k ∈
      E.blueSegmentTransitionEndpoints hbudget hrecords B hB fallback
        (transitionAt E hbudget hrecords B hB fallback M hcard i) := by
  rw [← E.blueSegmentTransitionPath_endpoints
    hbudget hrecords B hB fallback
      (transitionAt E hbudget hrecords B hB fallback M hcard i)]
  fin_cases k <;> simp [endpoint, linkAt]

/-- The two endpoint slots of all selected links are distinct. -/
theorem endpoint_injective
    (hdisjoint :
      E.BlueSegmentTransitionFamilyVertexDisjoint
        hbudget hrecords B hB fallback M) :
    Function.Injective
      (fun z : Fin (16 * t) × Fin 2 =>
        endpoint E hbudget hrecords B hB fallback M hcard z.1 z.2) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ heq
  change
    endpoint E hbudget hrecords B hB fallback M hcard i k =
      endpoint E hbudget hrecords B hB fallback M hcard j l at heq
  have hij : i = j := by
    by_contra hij
    let ei :=
      transitionAt E hbudget hrecords B hB fallback M hcard i
    let ej :=
      transitionAt E hbudget hrecords B hB fallback M hcard j
    let pi :=
      E.blueSegmentTransitionEndpoints hbudget hrecords B hB fallback ei
    let pj :=
      E.blueSegmentTransitionEndpoints hbudget hrecords B hB fallback ej
    have heiM : ei ∈ M :=
      transitionAt_mem E hbudget hrecords B hB fallback M hcard i
    have hejM : ej ∈ M :=
      transitionAt_mem E hbudget hrecords B hB fallback M hcard j
    have hpi :
        pi ∈ M.image
          (E.blueSegmentTransitionEndpoints
            hbudget hrecords B hB fallback) :=
      Finset.mem_image.mpr ⟨ei, heiM, rfl⟩
    have hpj :
        pj ∈ M.image
          (E.blueSegmentTransitionEndpoints
            hbudget hrecords B hB fallback) :=
      Finset.mem_image.mpr ⟨ej, hejM, rfl⟩
    have hpne : pi ≠ pj := by
      intro hp
      apply hij
      exact transitionAt_injective
        E hbudget hrecords B hB fallback M hcard
        (E.blueSegmentTransitionEndpoints_injective
          hbudget hrecords B hB fallback hp)
    have hd :
        Disjoint pi.toFinset pj.toFinset := by
      exact hdisjoint hpi hpj hpne
    rw [Finset.disjoint_left] at hd
    exact False.elim
      (hd
        (Sym2.mem_toFinset.mpr
          (endpoint_mem_transitionEndpoints
            E hbudget hrecords B hB fallback M hcard i k))
        (by
          rw [heq]
          exact Sym2.mem_toFinset.mpr
            (endpoint_mem_transitionEndpoints
              E hbudget hrecords B hB fallback M hcard j l)))
  subst j
  have hkl : k = l := by
    fin_cases k <;> fin_cases l
    · rfl
    · exact False.elim
        ((linkAt_source_ne_target
          E hbudget hrecords B hB fallback M hcard i)
          (by simpa [endpoint] using heq))
    · exact False.elim
        ((linkAt_source_ne_target
          E hbudget hrecords B hB fallback M hcard i)
          (by simpa [endpoint] using heq.symm))
    · rfl
  subst l
  rfl

/-- A genuine degree-four endpoint uses its thinning coordinate; an
unconditional endpoint gets a private dummy coordinate. -/
noncomputable def slotCoordinate
    (z : Fin (16 * t) × Fin 2) :
    {v : V // v ∈ degreeFourVertices (E.assembledSupport hbudget)} ⊕
      (Fin (16 * t) × Fin 2) := by
  classical
  exact if hv :
      endpoint E hbudget hrecords B hB fallback M hcard z.1 z.2 ∈
        degreeFourVertices (E.assembledSupport hbudget)
    then
      Sum.inl
        ⟨endpoint E hbudget hrecords B hB fallback M hcard z.1 z.2,
          hv⟩
    else Sum.inr z

theorem slotCoordinate_injective
    (hdisjoint :
      E.BlueSegmentTransitionFamilyVertexDisjoint
        hbudget hrecords B hB fallback M) :
    Function.Injective
      (slotCoordinate E hbudget hrecords B hB fallback M hcard) := by
  intro z w hzw
  classical
  unfold slotCoordinate at hzw
  split at hzw <;> split at hzw
  · have hendpoint :
        endpoint E hbudget hrecords B hB fallback M hcard z.1 z.2 =
          endpoint E hbudget hrecords B hB fallback M hcard w.1 w.2 :=
      congrArg
        (fun q => q.elim Subtype.val
          (fun x =>
            endpoint E hbudget hrecords B hB fallback M hcard x.1 x.2))
        hzw
    exact endpoint_injective E hbudget hrecords B hB fallback
      M hcard hdisjoint hendpoint
  · cases hzw
  · cases hzw
  · exact Sum.inr_injective hzw

/-- The canonical edge incident with endpoint `k` of link `i`. -/
noncomputable def endpointEdge
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (M : Finset
      (E.BlueSegmentTransition hbudget hrecords B hB fallback))
    (hcard : M.card = 16 * t)
    (i : Fin (16 * t)) (k : Fin 2) : Sym2 V :=
  Classical.choose
    ((linkAt E hbudget hrecords B hB fallback M hcard i)
      |>.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
        (linkAt_source_ne_target
          E hbudget hrecords B hB fallback M hcard i)
        (endpoint_mem_vertexSet
          E hbudget hrecords B hB fallback M hcard i k))

theorem endpointEdge_mem_link
    (i : Fin (16 * t)) (k : Fin 2) :
    endpointEdge E hbudget hrecords B hB fallback M hcard i k ∈
      (linkAt E hbudget hrecords B hB fallback M hcard i).edgeSet :=
  (Classical.choose_spec
    ((linkAt E hbudget hrecords B hB fallback M hcard i)
      |>.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
        (linkAt_source_ne_target
          E hbudget hrecords B hB fallback M hcard i)
        (endpoint_mem_vertexSet
          E hbudget hrecords B hB fallback M hcard i k))).1

theorem endpoint_mem_endpointEdge
    (i : Fin (16 * t)) (k : Fin 2) :
    endpoint E hbudget hrecords B hB fallback M hcard i k ∈
      endpointEdge E hbudget hrecords B hB fallback M hcard i k :=
  (Classical.choose_spec
    ((linkAt E hbudget hrecords B hB fallback M hcard i)
      |>.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
        (linkAt_source_ne_target
          E hbudget hrecords B hB fallback M hcard i)
        (endpoint_mem_vertexSet
          E hbudget hrecords B hB fallback M hcard i k))).2

theorem edge_eq_endpointEdge_of_endpoint_mem
    (i : Fin (16 * t)) (k : Fin 2)
    {e : Sym2 V}
    (he :
      e ∈ (linkAt E hbudget hrecords B hB fallback M hcard i).edgeSet)
    (hendpoint :
      endpoint E hbudget hrecords B hB fallback M hcard i k ∈ e) :
    e = endpointEdge E hbudget hrecords B hB fallback M hcard i k :=
  graphPath_edge_eq_of_endpoint_incident
    (linkAt E hbudget hrecords B hB fallback M hcard i)
    (endpoint_isEndpoint
      E hbudget hrecords B hB fallback M hcard i k)
    he
    (endpointEdge_mem_link
      E hbudget hrecords B hB fallback M hcard i k)
    hendpoint
    (endpoint_mem_endpointEdge
      E hbudget hrecords B hB fallback M hcard i k)

theorem endpointEdge_mem_assembled
    (i : Fin (16 * t)) (k : Fin 2) :
    endpointEdge E hbudget hrecords B hB fallback M hcard i k ∈
      (E.assembledSupport hbudget).edgeSet := by
  exact GraphPath.edgeSet_subset_edgeSet
    (linkAt E hbudget hrecords B hB fallback M hcard i)
    (endpointEdge_mem_link
      E hbudget hrecords B hB fallback M hcard i k)

theorem endpointEdge_mem_blue
    (i : Fin (16 * t)) (k : Fin 2) :
    let e : (E.assembledSupport hbudget).edgeSet :=
      ⟨endpointEdge E hbudget hrecords B hB fallback M hcard i k,
        endpointEdge_mem_assembled
          E hbudget hrecords B hB fallback M hcard i k⟩
    e ∈ (E.blueThinningInput hbudget).blue := by
  classical
  let e : (E.assembledSupport hbudget).edgeSet :=
    ⟨endpointEdge E hbudget hrecords B hB fallback M hcard i k,
      endpointEdge_mem_assembled
        E hbudget hrecords B hB fallback M hcard i k⟩
  change
    e ∈ edgesOfSubgraph
      (E.assembledSupport hbudget) E.blueSupport le_sup_right
  rw [mem_edgesOfSubgraph]
  have hblue :
      endpointEdge E hbudget hrecords B hB fallback M hcard i k ∈
        E.blueSupport.edgeSet :=
    E.blueSegmentTransitionPath_edgeSet_subset_blue
      hbudget hrecords B hB fallback
      (transitionAt E hbudget hrecords B hB fallback M hcard i)
      _
      (endpointEdge_mem_link
        E hbudget hrecords B hB fallback M hcard i k)
  exact hblue

/-- Safe endpoint value for one link endpoint. -/
noncomputable def expected
    (z : Fin (16 * t) × Fin 2) : Fin 2 := by
  classical
  let e : (E.assembledSupport hbudget).edgeSet :=
    ⟨endpointEdge E hbudget hrecords B hB fallback M hcard z.1 z.2,
      endpointEdge_mem_assembled
        E hbudget hrecords B hB fallback M hcard z.1 z.2⟩
  by_cases hv :
      endpoint E hbudget hrecords B hB fallback M hcard z.1 z.2 ∈
        degreeFourVertices (E.assembledSupport hbudget)
  · let v :
        {v : V // v ∈
          degreeFourVertices (E.assembledSupport hbudget)} :=
      ⟨endpoint E hbudget hrecords B hB fallback M hcard z.1 z.2, hv⟩
    exact
      (E.blueThinningInput hbudget).avoidingChoice e
        (endpointEdge_mem_blue
          E hbudget hrecords B hB fallback M hcard z.1 z.2)
        v
        (BlueThinningInput.edgeIncident_of_mem e
          (endpoint_mem_endpointEdge
            E hbudget hrecords B hB fallback M hcard z.1 z.2))
  · exact 0

theorem expected_eq_avoiding
    (z : Fin (16 * t) × Fin 2)
    (hv :
      endpoint E hbudget hrecords B hB fallback M hcard z.1 z.2 ∈
        degreeFourVertices (E.assembledSupport hbudget)) :
    let e : (E.assembledSupport hbudget).edgeSet :=
      ⟨endpointEdge E hbudget hrecords B hB fallback M hcard z.1 z.2,
        endpointEdge_mem_assembled
          E hbudget hrecords B hB fallback M hcard z.1 z.2⟩
    let v :
        {v : V // v ∈
          degreeFourVertices (E.assembledSupport hbudget)} :=
      ⟨endpoint E hbudget hrecords B hB fallback M hcard z.1 z.2, hv⟩
    expected E hbudget hrecords B hB fallback M hcard z =
      (E.blueThinningInput hbudget).avoidingChoice e
        (endpointEdge_mem_blue
          E hbudget hrecords B hB fallback M hcard z.1 z.2)
        v
        (BlueThinningInput.edgeIncident_of_mem e
          (endpoint_mem_endpointEdge
            E hbudget hrecords B hB fallback M hcard z.1 z.2)) := by
  classical
  simp [expected, hv]

/-- A transition survives when every physical edge of its complete blue link
is retained. -/
def Survives
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) : Prop :=
  ∀ f ∈
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).edgeSet,
    f ∈ ((E.blueThinningInput hbudget).thinnedGraph outcome).edgeSet

/-- Number of transitions in `M` whose complete links survive. -/
noncomputable def retained
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) : ℕ := by
  classical
  exact (M.filter fun e =>
    Survives E hbudget hrecords B hB fallback outcome e).card

/-- Prescribing the two safe endpoint bits preserves the whole link. -/
theorem linkAt_survives_of_safe
    (ω :
      {v : V // v ∈ degreeFourVertices (E.assembledSupport hbudget)} ⊕
        (Fin (16 * t) × Fin 2) → Fin 2)
    (i : Fin (16 * t))
    (hsafe :
      ∀ k,
        ω (slotCoordinate
          E hbudget hrecords B hB fallback M hcard (i, k)) =
          expected E hbudget hrecords B hB fallback M hcard (i, k)) :
    Survives E hbudget hrecords B hB fallback
      (fun v => ω (Sum.inl v))
      (transitionAt E hbudget hrecords B hB fallback M hcard i) := by
  classical
  let C := linkAt E hbudget hrecords B hB fallback M hcard i
  intro e he
  have heAssembled : e ∈ (E.assembledSupport hbudget).edgeSet :=
    GraphPath.edgeSet_subset_edgeSet C he
  let named : (E.assembledSupport hbudget).edgeSet :=
    ⟨e, heAssembled⟩
  have heblue : named ∈ (E.blueThinningInput hbudget).blue := by
    change
      named ∈ edgesOfSubgraph
        (E.assembledSupport hbudget) E.blueSupport le_sup_right
    rw [mem_edgesOfSubgraph]
    have hblue :
        e ∈ E.blueSupport.edgeSet :=
      E.blueSegmentTransitionPath_edgeSet_subset_blue
        hbudget hrecords B hB fallback
        (transitionAt E hbudget hrecords B hB fallback M hcard i) e he
    exact hblue
  apply
    (E.blueThinningInput hbudget).edge_mem_thinned_of_endpoint_avoiding
      named heblue (fun v => ω (Sum.inl v))
  intro v hv
  rcases Sym2.mem_iff_exists.mp hv with ⟨w, heOriented⟩
  have hePath : s(v.1, w) ∈ C.edgeSet := by
    rw [← heOriented]
    exact he
  have hvPath : v.1 ∈ C.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet C hePath).1
  obtain ⟨x, hvCarrier⟩ :=
    E.degreeFour_has_redCarrier hbudget v.2
  have hvCarrierSet :
      v.1 ∈ E.redCarrierVertices hbudget :=
    (E.mem_redCarrierVertices hbudget v.1).2 ⟨x, hvCarrier⟩
  have hvEndpoint : C.IsEndpoint v.1 :=
    E.blueSegmentTransitionPath_internally_carrier_clean
      hbudget hrecords B hB fallback
      (transitionAt E hbudget hrecords B hB fallback M hcard i)
      hvPath hvCarrierSet
  rcases hvEndpoint with hvSource | hvTarget
  · have hbad :
        endpoint E hbudget hrecords B hB fallback M hcard i 0 ∈
          degreeFourVertices (E.assembledSupport hbudget) := by
      simpa [endpoint, C, hvSource] using v.2
    have hvEq :
        (⟨endpoint E hbudget hrecords B hB fallback M hcard i 0, hbad⟩ :
          {v : V // v ∈
            degreeFourVertices (E.assembledSupport hbudget)}) = v := by
      apply Subtype.ext
      simpa [endpoint, C] using hvSource.symm
    have hslot :
        slotCoordinate E hbudget hrecords B hB fallback M hcard (i, 0) =
          Sum.inl v := by
      simp only [slotCoordinate, dif_pos hbad]
      rw [hvEq]
    have hs := hsafe 0
    rw [hslot] at hs
    have hendpoint :
        endpoint E hbudget hrecords B hB fallback M hcard i 0 ∈ e := by
      simpa [endpoint, C, hvSource] using hv
    have heEq :
        e = endpointEdge
          E hbudget hrecords B hB fallback M hcard i 0 :=
      edge_eq_endpointEdge_of_endpoint_mem
        E hbudget hrecords B hB fallback M hcard i 0 he hendpoint
    subst e
    calc
      ω (Sum.inl v) =
          expected E hbudget hrecords B hB fallback M hcard (i, 0) := hs
      _ = (E.blueThinningInput hbudget).avoidingChoice
          named heblue v
          (BlueThinningInput.edgeIncident_of_mem named hv) := by
        simpa [named, hvEq] using
          expected_eq_avoiding
            E hbudget hrecords B hB fallback M hcard (i, 0) hbad
  · have hbad :
        endpoint E hbudget hrecords B hB fallback M hcard i 1 ∈
          degreeFourVertices (E.assembledSupport hbudget) := by
      simpa [endpoint, C, hvTarget] using v.2
    have hvEq :
        (⟨endpoint E hbudget hrecords B hB fallback M hcard i 1, hbad⟩ :
          {v : V // v ∈
            degreeFourVertices (E.assembledSupport hbudget)}) = v := by
      apply Subtype.ext
      simpa [endpoint, C] using hvTarget.symm
    have hslot :
        slotCoordinate E hbudget hrecords B hB fallback M hcard (i, 1) =
          Sum.inl v := by
      simp only [slotCoordinate, dif_pos hbad]
      rw [hvEq]
    have hs := hsafe 1
    rw [hslot] at hs
    have hendpoint :
        endpoint E hbudget hrecords B hB fallback M hcard i 1 ∈ e := by
      simpa [endpoint, C, hvTarget] using hv
    have heEq :
        e = endpointEdge
          E hbudget hrecords B hB fallback M hcard i 1 :=
      edge_eq_endpointEdge_of_endpoint_mem
        E hbudget hrecords B hB fallback M hcard i 1 he hendpoint
    subst e
    calc
      ω (Sum.inl v) =
          expected E hbudget hrecords B hB fallback M hcard (i, 1) := hs
      _ = (E.blueThinningInput hbudget).avoidingChoice
          named heblue v
          (BlueThinningInput.edgeIncident_of_mem named hv) := by
        simpa [named, hvEq] using
          expected_eq_avoiding
            E hbudget hrecords B hB fallback M hcard (i, 1) hbad

/-- Locally safe indices inject into fully surviving links. -/
theorem safe_word_le_retained
    (ω :
      {v : V // v ∈ degreeFourVertices (E.assembledSupport hbudget)} ⊕
        (Fin (16 * t) × Fin 2) → Fin 2) :
    safeCount
        (wordEquiv
          (expected E hbudget hrecords B hB fallback M hcard)
          fun z =>
            ω (slotCoordinate
              E hbudget hrecords B hB fallback M hcard z)) ≤
      retained E hbudget hrecords B hB fallback M
        (fun v => ω (Sum.inl v)) := by
  classical
  let safe : Finset (Fin (16 * t)) :=
    Finset.univ.filter fun i =>
      wordEquiv
          (expected E hbudget hrecords B hB fallback M hcard)
          (fun z =>
            ω (slotCoordinate
              E hbudget hrecords B hB fallback M hcard z)) i = 0
  let surviving :
      Finset
        (E.BlueSegmentTransition hbudget hrecords B hB fallback) :=
    M.filter fun e =>
      Survives E hbudget hrecords B hB fallback
        (fun v => ω (Sum.inl v)) e
  let f :
      {i : Fin (16 * t) // i ∈ safe} →
        {e : E.BlueSegmentTransition hbudget hrecords B hB fallback //
          e ∈ surviving} :=
    fun i =>
      ⟨transitionAt E hbudget hrecords B hB fallback M hcard i.1, by
        have hsafe :
            ∀ k,
              ω (slotCoordinate
                E hbudget hrecords B hB fallback M hcard (i.1, k)) =
                expected E hbudget hrecords B hB fallback M hcard
                  (i.1, k) :=
          (wordEquiv_apply_eq_zero_iff
            (expected E hbudget hrecords B hB fallback M hcard)
            (fun z =>
              ω (slotCoordinate
                E hbudget hrecords B hB fallback M hcard z))
            i.1).mp (Finset.mem_filter.mp i.2).2
        exact Finset.mem_filter.mpr
          ⟨transitionAt_mem
              E hbudget hrecords B hB fallback M hcard i.1,
            linkAt_survives_of_safe
              E hbudget hrecords B hB fallback M hcard ω i.1 hsafe⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply transitionAt_injective
      E hbudget hrecords B hB fallback M hcard
    simpa [f] using congrArg Subtype.val hij
  calc
    safeCount
        (wordEquiv
          (expected E hbudget hrecords B hB fallback M hcard)
          fun z =>
            ω (slotCoordinate
              E hbudget hrecords B hB fallback M hcard z)) =
        safe.card := by rfl
    _ = Fintype.card {i : Fin (16 * t) // i ∈ safe} := by
      rw [Fintype.card_coe]
    _ ≤ Fintype.card
        {e : E.BlueSegmentTransition hbudget hrecords B hB fallback //
          e ∈ surviving} :=
      Fintype.card_le_of_injective f hf
    _ = surviving.card := by rw [Fintype.card_coe]
    _ = retained E hbudget hrecords B hB fallback M
        (fun v => ω (Sum.inl v)) := by
      rfl

/-- Fixed-family concentration for complete blue links. -/
theorem bad_outcomes_mul_failureFactor_le_total
    (hdisjoint :
      E.BlueSegmentTransitionFamilyVertexDisjoint
        hbudget hrecords B hB fallback M)
    (hcard : M.card = 16 * t) :
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget) =>
        retained E hbudget hrecords B hB fallback M outcome < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) := by
  classical
  exact
    binaryOutcomes_bad_mul_failureFactor_le_total
      t
      (slotCoordinate E hbudget hrecords B hB fallback M hcard)
      (slotCoordinate_injective
        E hbudget hrecords B hB fallback M hcard hdisjoint)
      (expected E hbudget hrecords B hB fallback M hcard)
      (retained E hbudget hrecords B hB fallback M)
      (safe_word_le_retained
        E hbudget hrecords B hB fallback M hcard)

end SegmentLinkFamily

/-- Number of complete links from `T` retained by one outcome. -/
noncomputable def survivingBlueSegmentTransitionCount
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (T : Finset
      (E.BlueSegmentTransition hbudget hrecords B hB fallback))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) : ℕ := by
  classical
  exact (T.filter fun e =>
    SegmentLinkFamily.Survives
      E hbudget hrecords B hB fallback outcome e).card

/-- If a fixed quotient cut contains at least `128t` blue transitions, its
probability of retaining fewer than `t` complete links has the required
exponential lower-tail bound. -/
theorem survivingBlueSegmentTransitionCount_bad_mul_failureFactor_le_total
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (T : Finset
      (E.BlueSegmentTransition hbudget hrecords B hB fallback))
    {t : ℕ} (hlarge : 128 * t ≤ T.card) :
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget) =>
        survivingBlueSegmentTransitionCount
          E hbudget hrecords B hB fallback T outcome < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) := by
  classical
  obtain ⟨M, hMT, hMdisjoint, hMcard⟩ :=
    E.exists_blueSegmentTransition_subfamily_card
      hbudget hrecords B hB fallback T hlarge
  have hfixed :=
    SegmentLinkFamily.bad_outcomes_mul_failureFactor_le_total
      E hbudget hrecords B hB fallback M hMdisjoint hMcard
  let badAll :
      Finset
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) :=
    Finset.univ.filter fun outcome =>
      survivingBlueSegmentTransitionCount
        E hbudget hrecords B hB fallback T outcome < t
  let badM :
      Finset
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) :=
    Finset.univ.filter fun outcome =>
      SegmentLinkFamily.retained
        E hbudget hrecords B hB fallback M outcome < t
  have hbadSubset : badAll ⊆ badM := by
    intro outcome houtcome
    have hbadAll :
        survivingBlueSegmentTransitionCount
          E hbudget hrecords B hB fallback T outcome < t := by
      simpa [badAll] using houtcome
    have hcount :
        SegmentLinkFamily.retained
            E hbudget hrecords B hB fallback M outcome ≤
          survivingBlueSegmentTransitionCount
            E hbudget hrecords B hB fallback T outcome := by
      apply Finset.card_le_card
      intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨hMT he.1, he.2⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcount.trans_lt hbadAll⟩
  calc
    (Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget) =>
        survivingBlueSegmentTransitionCount
          E hbudget hrecords B hB fallback T outcome < t).card *
        4 ^ (t + 1) =
        badAll.card * 4 ^ (t + 1) := by rfl
    _ ≤ badM.card * 4 ^ (t + 1) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hbadSubset)
    _ ≤ Fintype.card
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) := by
      simpa [badM] using hfixed

/-- Blue transition representatives crossing a fixed segment-quotient cut. -/
noncomputable def blueSegmentBoundaryTransitions
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (S : Finset
      (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    Finset (E.BlueSegmentTransition hbudget hrecords B hB fallback) := by
  classical
  exact Finset.univ.filter fun e =>
    e.1 ∈ E.segmentBoundaryEdges hbudget hrecords B hB fallback S

/-- Underlying blue physical representatives crossing the quotient cut. -/
noncomputable def blueSegmentBoundaryEdges
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (S : Finset
      (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    Finset (Sym2 V) := by
  classical
  exact
    (E.segmentBoundaryEdges hbudget hrecords B hB fallback S).filter
      fun e => e ∈ E.blueSupport.edgeSet

/-- Nonblue representatives crossing a fixed segment-quotient cut.  These
edges survive deterministically. -/
noncomputable def nonBlueSegmentBoundaryEdges
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (S : Finset
      (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    Finset (Sym2 V) := by
  classical
  exact
    (E.segmentBoundaryEdges hbudget hrecords B hB fallback S).filter
      fun e => e ∉ E.blueSupport.edgeSet

theorem blueSegmentBoundaryTransitions_image
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (S : Finset
      (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    (E.blueSegmentBoundaryTransitions
        hbudget hrecords B hB fallback S).image Subtype.val =
      E.blueSegmentBoundaryEdges
        hbudget hrecords B hB fallback S := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨f, hf, rfl⟩
    have hfBoundary :
        f.1 ∈ E.segmentBoundaryEdges
          hbudget hrecords B hB fallback S :=
      (Finset.mem_filter.mp hf).2
    exact Finset.mem_filter.mpr ⟨hfBoundary, f.2.2⟩
  · intro he
    rcases Finset.mem_filter.mp he with ⟨heBoundary, heBlue⟩
    have heCross :
        e ∈ E.segmentCrossingEdges
          hbudget hrecords B hB fallback :=
      (Finset.mem_filter.mp heBoundary).1
    let f :
        E.BlueSegmentTransition hbudget hrecords B hB fallback :=
      ⟨e, heCross, heBlue⟩
    exact Finset.mem_image.mpr
      ⟨f, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, heBoundary⟩, rfl⟩

theorem blueSegmentBoundaryTransitions_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (S : Finset
      (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    (E.blueSegmentBoundaryTransitions
        hbudget hrecords B hB fallback S).card =
      (E.blueSegmentBoundaryEdges
        hbudget hrecords B hB fallback S).card := by
  classical
  calc
    (E.blueSegmentBoundaryTransitions
        hbudget hrecords B hB fallback S).card =
        ((E.blueSegmentBoundaryTransitions
          hbudget hrecords B hB fallback S).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = (E.blueSegmentBoundaryEdges
          hbudget hrecords B hB fallback S).card :=
      congrArg Finset.card
        (E.blueSegmentBoundaryTransitions_image
          hbudget hrecords B hB fallback S)

/-- The quotient boundary partitions into blue transition representatives and
deterministically retained nonblue edges. -/
theorem blue_add_nonBlue_segmentBoundary_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (S : Finset
      (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    (E.blueSegmentBoundaryTransitions
        hbudget hrecords B hB fallback S).card +
      (E.nonBlueSegmentBoundaryEdges
        hbudget hrecords B hB fallback S).card =
      (E.segmentBoundaryEdges
        hbudget hrecords B hB fallback S).card := by
  classical
  rw [E.blueSegmentBoundaryTransitions_card
    hbudget hrecords B hB fallback S]
  unfold blueSegmentBoundaryEdges nonBlueSegmentBoundaryEdges
  exact
    Finset.card_filter_add_card_filter_not
      (s := E.segmentBoundaryEdges hbudget hrecords B hB fallback S)
      (p := fun e => e ∈ E.blueSupport.edgeSet)

/-- Number of quotient-cut connections usable after thinning: every nonblue
edge is a one-edge connection, and every counted blue transition contributes
its complete surviving suppressed path. -/
noncomputable def usableSegmentBoundaryCount
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (S : Finset
      (ExactRailSegmentIndex E hbudget hrecords B hB))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) : ℕ :=
  (E.nonBlueSegmentBoundaryEdges
      hbudget hrecords B hB fallback S).card +
    E.survivingBlueSegmentTransitionCount
      hbudget hrecords B hB fallback
      (E.blueSegmentBoundaryTransitions
        hbudget hrecords B hB fallback S) outcome

/-- Complete-link fixed-cut estimate.  The factor `256` combines the
one-half red/blue dichotomy with the `128` endpoint-disjoint selection and
four-valued concentration estimate. -/
theorem usableSegmentBoundaryCount_bad_mul_failureFactor_le_total
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : E.ExactRailSegmentIndex hbudget hrecords B hB)
    (S : Finset
      (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    let q :=
      (E.segmentBoundaryEdges
        hbudget hrecords B hB fallback S).card / 256
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget) =>
        E.usableSegmentBoundaryCount
          hbudget hrecords B hB fallback S outcome < q).card) *
        4 ^ (q + 1) ≤
      Fintype.card
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) := by
  classical
  dsimp only
  let boundary :=
    E.segmentBoundaryEdges hbudget hrecords B hB fallback S
  let T :=
    E.blueSegmentBoundaryTransitions
      hbudget hrecords B hB fallback S
  let R :=
    E.nonBlueSegmentBoundaryEdges
      hbudget hrecords B hB fallback S
  let q := boundary.card / 256
  have hpartition : T.card + R.card = boundary.card := by
    simpa [T, R, boundary] using
      E.blue_add_nonBlue_segmentBoundary_card
        hbudget hrecords B hB fallback S
  by_cases hRq : q ≤ R.card
  · have hempty :
        (Finset.univ.filter fun outcome :
          BlueThinningInput.Outcome
            (H := E.assembledSupport hbudget) =>
          E.usableSegmentBoundaryCount
            hbudget hrecords B hB fallback S outcome < q) = ∅ := by
      ext outcome
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show outcome ∈
          (∅ : Finset
            (BlueThinningInput.Outcome
              (H := E.assembledSupport hbudget))) ↔ False by simp]
      constructor
      · intro hbad
        have hRle :
            R.card ≤
              E.usableSegmentBoundaryCount
                hbudget hrecords B hB fallback S outcome := by
          simp only [usableSegmentBoundaryCount, R]
          omega
        exact Nat.not_lt_of_ge (hRq.trans hRle) hbad
      · intro hfalse
        exact False.elim hfalse
    rw [hempty]
    simp
  · have hRlt : R.card < q := Nat.lt_of_not_ge hRq
    have hqmul : 256 * q ≤ boundary.card := by
      exact Nat.mul_div_le boundary.card 256
    have hlarge : 128 * q ≤ T.card := by
      omega
    have hfixed :=
      E.survivingBlueSegmentTransitionCount_bad_mul_failureFactor_le_total
        hbudget hrecords B hB fallback T hlarge
    let badAll :
        Finset
          (BlueThinningInput.Outcome
            (H := E.assembledSupport hbudget)) :=
      Finset.univ.filter fun outcome =>
        E.usableSegmentBoundaryCount
          hbudget hrecords B hB fallback S outcome < q
    let badBlue :
        Finset
          (BlueThinningInput.Outcome
            (H := E.assembledSupport hbudget)) :=
      Finset.univ.filter fun outcome =>
        E.survivingBlueSegmentTransitionCount
          hbudget hrecords B hB fallback T outcome < q
    have hbadSubset : badAll ⊆ badBlue := by
      intro outcome houtcome
      have hbad :
          E.usableSegmentBoundaryCount
            hbudget hrecords B hB fallback S outcome < q := by
        simpa [badAll] using houtcome
      have hblueBad :
          E.survivingBlueSegmentTransitionCount
            hbudget hrecords B hB fallback T outcome < q := by
        simpa [usableSegmentBoundaryCount, T, R] using
          (lt_of_le_of_lt
            (Nat.le_add_left
              (E.survivingBlueSegmentTransitionCount
                hbudget hrecords B hB fallback T outcome) R.card)
            hbad)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hblueBad⟩
    calc
      (Finset.univ.filter fun outcome :
          BlueThinningInput.Outcome
            (H := E.assembledSupport hbudget) =>
          E.usableSegmentBoundaryCount
            hbudget hrecords B hB fallback S outcome < q).card *
          4 ^ (q + 1) =
          badAll.card * 4 ^ (q + 1) := by rfl
      _ ≤ badBlue.card * 4 ^ (q + 1) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hbadSubset)
      _ ≤ Fintype.card
          (BlueThinningInput.Outcome
            (H := E.assembledSupport hbudget)) := by
        simpa [badBlue] using hfixed

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
