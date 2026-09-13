import Lax17Proofs.Source.TreewidthSparsifierTheorem51Chunks

namespace Lax17Proofs

universe u v w

/-!
# Lower-tail concentration for carrier-clean chunks

For one abstract rail cut, choose `16t` matching-boundary instances.  Their
carrier-clean physical chunks are pairwise vertex-disjoint.  Every
degree-four vertex on a chunk is one of its two endpoints, so prescribing one
avoiding bit at each endpoint preserves the whole chunk.  The elementary
four-valued lower-tail estimate therefore applies to complete connecting
chunks, rather than merely to isolated quotient edges.
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
namespace ChunkFamily

variable (E : ExpanderBlocks P count)
variable (hbudget :
  count *
      (realizedRoundConstant *
        Nat.log 2 h) ≤ ell)
variable (S : Finset (Fin h))
variable (M : Finset (E.RecordBoundary S))
variable (hcard : M.card = 16 * t)

/-- Canonical enumeration of an exact `16t`-subfamily of boundary records. -/
noncomputable def recordAt (i : Fin (16 * t)) :
    E.RecordBoundary S :=
  (M.equivFin.symm (Fin.cast hcard.symm i)).1

theorem recordAt_mem (i : Fin (16 * t)) :
    recordAt E S M hcard i ∈ M :=
  (M.equivFin.symm (Fin.cast hcard.symm i)).2

theorem recordAt_injective :
    Function.Injective (recordAt E S M hcard) := by
  intro i j hij
  have hsub :
      M.equivFin.symm (Fin.cast hcard.symm i) =
        M.equivFin.symm (Fin.cast hcard.symm j) :=
    Subtype.ext hij
  have hcast :
      Fin.cast hcard.symm i = Fin.cast hcard.symm j :=
    M.equivFin.symm.injective hsub
  exact Fin.cast_injective hcard.symm hcast

/-- The selected carrier-clean chunk at index `i`. -/
noncomputable def chunkAt (i : Fin (16 * t)) :=
  E.crossingChunk hbudget S (recordAt E S M hcard i)

theorem chunkAt_source_ne_target (i : Fin (16 * t)) :
    (chunkAt E hbudget S M hcard i).path.source ≠
      (chunkAt E hbudget S M hcard i).path.target :=
  E.crossingChunk_source_ne_target hbudget S
    (recordAt E S M hcard i)

/-- Endpoint zero is the source and endpoint one is the target. -/
noncomputable def endpoint (i : Fin (16 * t)) (k : Fin 2) : V :=
  (chunkAt E hbudget S M hcard i).endpoint k

theorem endpoint_mem_vertexSet (i : Fin (16 * t)) (k : Fin 2) :
    endpoint E hbudget S M hcard i k ∈
      (chunkAt E hbudget S M hcard i).path.vertexSet :=
  (chunkAt E hbudget S M hcard i).endpoint_mem_vertexSet k

/-- The `2 * 16t` endpoint slots are distinct because distinct chunks are
vertex-disjoint and each chunk is nontrivial. -/
theorem endpoint_injective :
    Function.Injective
      (fun z : Fin (16 * t) × Fin 2 =>
        endpoint E hbudget S M hcard z.1 z.2) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ heq
  change
    endpoint E hbudget S M hcard i k =
      endpoint E hbudget S M hcard j l at heq
  have hij : i = j := by
    by_contra hij
    have hrecords :
        recordAt E S M hcard i ≠ recordAt E S M hcard j :=
      fun h => hij (recordAt_injective E S M hcard h)
    have hdisj :=
      E.crossingChunk_vertex_disjoint hbudget S hrecords
    rw [Finset.disjoint_left] at hdisj
    exact False.elim
      (hdisj
        (endpoint_mem_vertexSet E hbudget S M hcard i k)
        (by
          rw [heq]
          exact endpoint_mem_vertexSet E hbudget S M hcard j l))
  subst j
  have hkl : k = l := by
    fin_cases k <;> fin_cases l
    · rfl
    · exact False.elim
        ((chunkAt_source_ne_target E hbudget S M hcard i)
          (by simpa [endpoint, CrossingChunk.endpoint] using heq))
    · exact False.elim
        ((chunkAt_source_ne_target E hbudget S M hcard i)
          (by simpa [endpoint, CrossingChunk.endpoint] using heq.symm))
    · rfl
  subst l
  rfl

/-- A real degree-four endpoint uses its genuine thinning coordinate; an
unconditional endpoint gets a private dummy coordinate. -/
noncomputable def slotCoordinate
    (z : Fin (16 * t) × Fin 2) :
    {v : V // v ∈ degreeFourVertices (E.assembledSupport hbudget)} ⊕
      (Fin (16 * t) × Fin 2) := by
  classical
  exact if hv :
      endpoint E hbudget S M hcard z.1 z.2 ∈
        degreeFourVertices (E.assembledSupport hbudget)
    then Sum.inl ⟨endpoint E hbudget S M hcard z.1 z.2, hv⟩
    else Sum.inr z

theorem slotCoordinate_injective :
    Function.Injective
      (slotCoordinate E hbudget S M hcard) := by
  intro z w hzw
  classical
  unfold slotCoordinate at hzw
  split at hzw <;> split at hzw
  · have hendpoint :
        endpoint E hbudget S M hcard z.1 z.2 =
          endpoint E hbudget S M hcard w.1 w.2 :=
      congrArg
        (fun q => q.elim Subtype.val
          (fun x => endpoint E hbudget S M hcard x.1 x.2)) hzw
    exact endpoint_injective E hbudget S M hcard hendpoint
  · cases hzw
  · cases hzw
  · exact Sum.inr_injective hzw

/-- The canonical edge incident with one endpoint of one selected chunk. -/
noncomputable def endpointEdge
    (i : Fin (16 * t)) (k : Fin 2) : Sym2 V :=
  (chunkAt E hbudget S M hcard i).endpointEdge
    (chunkAt_source_ne_target E hbudget S M hcard i) k

theorem endpointEdge_mem_chunk
    (i : Fin (16 * t)) (k : Fin 2) :
    endpointEdge E hbudget S M hcard i k ∈
      (chunkAt E hbudget S M hcard i).path.edgeSet :=
  (chunkAt E hbudget S M hcard i).endpointEdge_mem_edgeSet
    (chunkAt_source_ne_target E hbudget S M hcard i) k

theorem endpoint_mem_endpointEdge
    (i : Fin (16 * t)) (k : Fin 2) :
    endpoint E hbudget S M hcard i k ∈
      endpointEdge E hbudget S M hcard i k :=
  (chunkAt E hbudget S M hcard i).endpoint_mem_endpointEdge
    (chunkAt_source_ne_target E hbudget S M hcard i) k

theorem endpointEdge_mem_assembled
    (i : Fin (16 * t)) (k : Fin 2) :
    endpointEdge E hbudget S M hcard i k ∈
      (E.assembledSupport hbudget).edgeSet := by
  exact _root_.SimpleGraph.edgeSet_mono le_sup_right
    (E.crossingChunk_edge_mem_blueSupport hbudget S
      (recordAt E S M hcard i)
      (endpointEdge_mem_chunk E hbudget S M hcard i k))

theorem endpointEdge_mem_blue
    (i : Fin (16 * t)) (k : Fin 2) :
    let e :
        (E.assembledSupport hbudget).edgeSet :=
      ⟨endpointEdge E hbudget S M hcard i k,
        endpointEdge_mem_assembled E hbudget S M hcard i k⟩
    e ∈ (E.blueThinningInput hbudget).blue := by
  classical
  let e :
      (E.assembledSupport hbudget).edgeSet :=
    ⟨endpointEdge E hbudget S M hcard i k,
      endpointEdge_mem_assembled E hbudget S M hcard i k⟩
  change
    e ∈ edgesOfSubgraph
      (E.assembledSupport hbudget) E.blueSupport le_sup_right
  rw [mem_edgesOfSubgraph]
  exact
    E.crossingChunk_edge_mem_blueSupport hbudget S
      (recordAt E S M hcard i)
      (endpointEdge_mem_chunk E hbudget S M hcard i k)

/-- The safe value at a real endpoint is the local avoiding choice. -/
noncomputable def expected
    (z : Fin (16 * t) × Fin 2) : Fin 2 := by
  classical
  let e : (E.assembledSupport hbudget).edgeSet :=
    ⟨endpointEdge E hbudget S M hcard z.1 z.2,
      endpointEdge_mem_assembled E hbudget S M hcard z.1 z.2⟩
  by_cases hv :
      endpoint E hbudget S M hcard z.1 z.2 ∈
        degreeFourVertices (E.assembledSupport hbudget)
  · let v :
        {v : V // v ∈
          degreeFourVertices (E.assembledSupport hbudget)} :=
      ⟨endpoint E hbudget S M hcard z.1 z.2, hv⟩
    exact
      (E.blueThinningInput hbudget).avoidingChoice e
        (endpointEdge_mem_blue E hbudget S M hcard z.1 z.2)
        v
        (BlueThinningInput.edgeIncident_of_mem e
          (endpoint_mem_endpointEdge E hbudget S M hcard z.1 z.2))
  · exact 0

theorem expected_eq_avoiding
    (z : Fin (16 * t) × Fin 2)
    (hv :
      endpoint E hbudget S M hcard z.1 z.2 ∈
        degreeFourVertices (E.assembledSupport hbudget)) :
    let e : (E.assembledSupport hbudget).edgeSet :=
      ⟨endpointEdge E hbudget S M hcard z.1 z.2,
        endpointEdge_mem_assembled E hbudget S M hcard z.1 z.2⟩
    let v :
        {v : V // v ∈
          degreeFourVertices (E.assembledSupport hbudget)} :=
      ⟨endpoint E hbudget S M hcard z.1 z.2, hv⟩
    expected E hbudget S M hcard z =
      (E.blueThinningInput hbudget).avoidingChoice e
        (endpointEdge_mem_blue E hbudget S M hcard z.1 z.2)
        v
        (BlueThinningInput.edgeIncident_of_mem e
          (endpoint_mem_endpointEdge E hbudget S M hcard z.1 z.2)) := by
  classical
  simp [expected, hv]

/-- A chunk survives when all its physical edges remain in the thinned
graph. -/
def Survives
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (z : E.RecordBoundary S) : Prop :=
  ∀ e ∈ (E.crossingChunk hbudget S z).path.edgeSet,
    e ∈ ((E.blueThinningInput hbudget).thinnedGraph outcome).edgeSet

/-- Number of members of `M` whose complete chunks survive. -/
noncomputable def retained
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) : ℕ := by
  classical
  exact (M.filter fun z => Survives E hbudget S outcome z).card

/-- If both prescribed endpoint bits are present at index `i`, the entire
carrier-clean chunk at `i` survives. -/
theorem chunkAt_survives_of_safe
    (ω :
      {v : V // v ∈ degreeFourVertices (E.assembledSupport hbudget)} ⊕
        (Fin (16 * t) × Fin 2) → Fin 2)
    (i : Fin (16 * t))
    (hsafe :
      ∀ k,
        ω (slotCoordinate E hbudget S M hcard (i, k)) =
          expected E hbudget S M hcard (i, k)) :
    Survives E hbudget S
      (fun v => ω (Sum.inl v))
      (recordAt E S M hcard i) := by
  classical
  let C := chunkAt E hbudget S M hcard i
  intro e he
  have heBlueSupport :
      e ∈ E.blueSupport.edgeSet :=
    E.crossingChunk_edge_mem_blueSupport hbudget S
      (recordAt E S M hcard i) he
  have heAssembled :
      e ∈ (E.assembledSupport hbudget).edgeSet :=
    _root_.SimpleGraph.edgeSet_mono le_sup_right heBlueSupport
  let named : (E.assembledSupport hbudget).edgeSet :=
    ⟨e, heAssembled⟩
  have heblue :
      named ∈ (E.blueThinningInput hbudget).blue := by
    change
      named ∈ edgesOfSubgraph
        (E.assembledSupport hbudget) E.blueSupport le_sup_right
    rw [mem_edgesOfSubgraph]
    exact heBlueSupport
  apply
    (E.blueThinningInput hbudget).edge_mem_thinned_of_endpoint_avoiding
      named heblue (fun v => ω (Sum.inl v))
  intro v hv
  rcases Sym2.mem_iff_exists.mp hv with ⟨w, heOriented⟩
  have hePath : s(v.1, w) ∈ C.path.edgeSet := by
    rw [← heOriented]
    exact he
  have hvPath : v.1 ∈ C.path.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet C.path hePath).1
  obtain ⟨x, hvCarrier⟩ :=
    E.degreeFour_has_redCarrier hbudget v.2
  have hvCarrierSet :
      v.1 ∈ E.redCarrierVertices hbudget :=
    (E.mem_redCarrierVertices hbudget v.1).2 ⟨x, hvCarrier⟩
  have hvEndpoint :
      C.path.IsEndpoint v.1 :=
    C.internally_carrier_clean hvPath hvCarrierSet
  rcases hvEndpoint with hvSource | hvTarget
  · have hbad :
        endpoint E hbudget S M hcard i 0 ∈
          degreeFourVertices (E.assembledSupport hbudget) := by
      simpa [endpoint, chunkAt, CrossingChunk.endpoint, C, hvSource] using v.2
    have hvEq :
        (⟨endpoint E hbudget S M hcard i 0, hbad⟩ :
          {v : V // v ∈
            degreeFourVertices (E.assembledSupport hbudget)}) = v := by
      apply Subtype.ext
      simpa [endpoint, chunkAt, CrossingChunk.endpoint, C] using hvSource.symm
    have hslot :
        slotCoordinate E hbudget S M hcard (i, 0) = Sum.inl v := by
      simp only [slotCoordinate, dif_pos hbad]
      rw [hvEq]
    have hs := hsafe 0
    rw [hslot] at hs
    have hendpoint :
        C.endpoint 0 ∈ e := by
      simpa [CrossingChunk.endpoint, hvSource] using hv
    have heEq :
        e =
          endpointEdge E hbudget S M hcard i 0 := by
      exact
        C.edge_eq_endpointEdge_of_endpoint_mem
          (chunkAt_source_ne_target E hbudget S M hcard i) 0 he
          hendpoint
    subst e
    calc
      ω (Sum.inl v) =
          expected E hbudget S M hcard (i, 0) := hs
      _ = (E.blueThinningInput hbudget).avoidingChoice
          named heblue v
          (BlueThinningInput.edgeIncident_of_mem named hv) := by
        simpa [named, hvEq] using
          expected_eq_avoiding E hbudget S M hcard (i, 0) hbad
  · have hbad :
        endpoint E hbudget S M hcard i 1 ∈
          degreeFourVertices (E.assembledSupport hbudget) := by
      simpa [endpoint, chunkAt, CrossingChunk.endpoint, C, hvTarget] using v.2
    have hvEq :
        (⟨endpoint E hbudget S M hcard i 1, hbad⟩ :
          {v : V // v ∈
            degreeFourVertices (E.assembledSupport hbudget)}) = v := by
      apply Subtype.ext
      simpa [endpoint, chunkAt, CrossingChunk.endpoint, C] using hvTarget.symm
    have hslot :
        slotCoordinate E hbudget S M hcard (i, 1) = Sum.inl v := by
      simp only [slotCoordinate, dif_pos hbad]
      rw [hvEq]
    have hs := hsafe 1
    rw [hslot] at hs
    have hendpoint :
        C.endpoint 1 ∈ e := by
      simpa [CrossingChunk.endpoint, hvTarget] using hv
    have heEq :
        e =
          endpointEdge E hbudget S M hcard i 1 := by
      exact
        C.edge_eq_endpointEdge_of_endpoint_mem
          (chunkAt_source_ne_target E hbudget S M hcard i) 1 he
          hendpoint
    subst e
    calc
      ω (Sum.inl v) =
          expected E hbudget S M hcard (i, 1) := hs
      _ = (E.blueThinningInput hbudget).avoidingChoice
          named heblue v
          (BlueThinningInput.edgeIncident_of_mem named hv) := by
        simpa [named, hvEq] using
          expected_eq_avoiding E hbudget S M hcard (i, 1) hbad

/-- The number of locally safe indices is at most the number of fully
surviving chunks. -/
theorem safe_word_le_retained
    (ω :
      {v : V // v ∈ degreeFourVertices (E.assembledSupport hbudget)} ⊕
        (Fin (16 * t) × Fin 2) → Fin 2) :
    safeCount
        (wordEquiv (expected E hbudget S M hcard)
          fun z => ω (slotCoordinate E hbudget S M hcard z)) ≤
      retained E hbudget S M (fun v => ω (Sum.inl v)) := by
  classical
  let safe : Finset (Fin (16 * t)) :=
    Finset.univ.filter fun i =>
      wordEquiv (expected E hbudget S M hcard)
        (fun z => ω (slotCoordinate E hbudget S M hcard z)) i = 0
  let surviving : Finset (E.RecordBoundary S) :=
    M.filter fun z =>
      Survives E hbudget S (fun v => ω (Sum.inl v)) z
  let f :
      {i : Fin (16 * t) // i ∈ safe} →
        {z : E.RecordBoundary S // z ∈ surviving} :=
    fun i =>
      ⟨recordAt E S M hcard i.1, by
        have hsafe :
            ∀ k,
              ω (slotCoordinate E hbudget S M hcard (i.1, k)) =
                expected E hbudget S M hcard (i.1, k) :=
          (wordEquiv_apply_eq_zero_iff
            (expected E hbudget S M hcard)
            (fun z => ω (slotCoordinate E hbudget S M hcard z))
            i.1).mp (Finset.mem_filter.mp i.2).2
        exact Finset.mem_filter.mpr
          ⟨recordAt_mem E S M hcard i.1,
            chunkAt_survives_of_safe E hbudget S M hcard ω i.1 hsafe⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply recordAt_injective E S M hcard
    simpa [f] using congrArg Subtype.val hij
  calc
    safeCount
        (wordEquiv (expected E hbudget S M hcard)
          fun z => ω (slotCoordinate E hbudget S M hcard z)) =
        safe.card := by rfl
    _ = Fintype.card {i : Fin (16 * t) // i ∈ safe} := by
      rw [Fintype.card_coe]
    _ ≤ Fintype.card
        {z : E.RecordBoundary S // z ∈ surviving} :=
      Fintype.card_le_of_injective f hf
    _ = surviving.card := by rw [Fintype.card_coe]
    _ = retained E hbudget S M (fun v => ω (Sum.inl v)) := by
      rfl

/-- Fixed-cut concentration for complete carrier-clean chunks. -/
theorem bad_outcomes_mul_failureFactor_le_total :
    M.card = 16 * t →
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget) =>
        retained E hbudget S M outcome < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) := by
  classical
  intro hcard
  exact
    binaryOutcomes_bad_mul_failureFactor_le_total
      t
      (slotCoordinate E hbudget S M hcard)
      (slotCoordinate_injective E hbudget S M hcard)
      (expected E hbudget S M hcard)
      (retained E hbudget S M)
      (safe_word_le_retained E hbudget S M hcard)

end ChunkFamily

/-- Number of all matching-boundary chunks which survive one outcome. -/
noncomputable def survivingChunkCount
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun z : E.RecordBoundary S =>
      ChunkFamily.Survives E hbudget S outcome z).card

/-- Fixed-cut lower tail for complete matching chunks.  Only the factor
sixteen from the four-valued estimate is lost; no degree-based edge
subselection is needed because the chunks themselves are vertex-disjoint. -/
theorem survivingChunkCount_bad_mul_failureFactor_le_total
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) :
    let t := Fintype.card (E.RecordBoundary S) / 16
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget) =>
        survivingChunkCount E hbudget S outcome < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) := by
  classical
  let t := Fintype.card (E.RecordBoundary S) / 16
  have hlarge :
      16 * t ≤ Fintype.card (E.RecordBoundary S) := by
    exact Nat.mul_div_le _ _
  have hlargeUniv :
      16 * t ≤ (Finset.univ : Finset (E.RecordBoundary S)).card := by
    simpa using hlarge
  obtain ⟨M, hMuniv, hMcard⟩ :=
    Finset.exists_subset_card_eq hlargeUniv
  have hfixed :=
    ChunkFamily.bad_outcomes_mul_failureFactor_le_total
      E hbudget S M hMcard
  let badAll :
      Finset
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) :=
    Finset.univ.filter fun outcome =>
      survivingChunkCount E hbudget S outcome < t
  let badM :
      Finset
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) :=
    Finset.univ.filter fun outcome =>
      ChunkFamily.retained E hbudget S M outcome < t
  have hbadSubset : badAll ⊆ badM := by
    intro outcome houtcome
    have hbadAll :
        survivingChunkCount E hbudget S outcome < t := by
      simpa [badAll] using houtcome
    have hcount :
        ChunkFamily.retained E hbudget S M outcome ≤
          survivingChunkCount E hbudget S outcome := by
      apply Finset.card_le_card
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨Finset.mem_univ _, hz.2⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcount.trans_lt hbadAll⟩
  calc
    (Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget) =>
        survivingChunkCount E hbudget S outcome < t).card *
        4 ^ (t + 1) =
        badAll.card * 4 ^ (t + 1) := by rfl
    _ ≤ badM.card * 4 ^ (t + 1) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hbadSubset)
    _ ≤ Fintype.card
        (BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget)) := by
      simpa [badM] using hfixed

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
