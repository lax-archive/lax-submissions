import Lax17Proofs.Source.TreewidthSparsifierThinningBoundary

namespace Lax17Proofs

universe u v w

/-!
# Actual blue-thinning outcomes

This module connects the finite four-valued concentration lemma to the binary
choice made at every degree-four vertex.  For a named blue edge and an
incident degree-four vertex there is exactly one local bit that deletes the
edge; `avoidingChoice` is the other bit.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {H : _root_.SimpleGraph V}

namespace BlueThinningInput

variable (I : BlueThinningInput H)

/-- The nontrivial involution of `Fin 2`. -/
def otherBit (b : Fin 2) : Fin 2 :=
  Equiv.swap 0 1 b

theorem otherBit_ne (b : Fin 2) : otherBit b ≠ b := by
  fin_cases b <;> decide

/-- A blue edge belongs to the two local choices at every incident
degree-four vertex. -/
theorem edge_mem_choices
    (e : H.edgeSet) (heblue : e ∈ I.blue)
    (v : {v : V // v ∈ degreeFourVertices H})
    (hincident : EdgeIncident H v.1 e) :
    e ∈ I.choices v := by
  classical
  exact Finset.mem_filter.mpr ⟨heblue, hincident⟩

/-- The unique bit that selects a given incident blue edge. -/
noncomputable def deletingChoice
    (e : H.edgeSet) (heblue : e ∈ I.blue)
    (v : {v : V // v ∈ degreeFourVertices H})
    (hincident : EdgeIncident H v.1 e) : Fin 2 :=
  (I.choiceEquiv v).symm
    ⟨e, I.edge_mem_choices e heblue v hincident⟩

/-- The other local bit, which certainly does not select the named edge. -/
noncomputable def avoidingChoice
    (e : H.edgeSet) (heblue : e ∈ I.blue)
    (v : {v : V // v ∈ degreeFourVertices H})
    (hincident : EdgeIncident H v.1 e) : Fin 2 :=
  otherBit (I.deletingChoice e heblue v hincident)

theorem selectedEdge_ne_of_eq_avoidingChoice
    (e : H.edgeSet) (heblue : e ∈ I.blue)
    (v : {v : V // v ∈ degreeFourVertices H})
    (hincident : EdgeIncident H v.1 e)
    (outcome : Outcome (H := H))
    (houtcome :
      outcome v = I.avoidingChoice e heblue v hincident) :
    I.selectedEdge outcome v ≠ e := by
  intro heq
  have heqSubtype :
      I.choiceEquiv v (outcome v) =
        ⟨e, I.edge_mem_choices e heblue v hincident⟩ := by
    apply Subtype.ext
    exact heq
  have hbit :
      outcome v = I.deletingChoice e heblue v hincident := by
    exact (I.choiceEquiv v).injective
      (heqSubtype.trans
        ((I.choiceEquiv v).apply_symm_apply
          ⟨e, I.edge_mem_choices e heblue v hincident⟩).symm)
  rw [houtcome] at hbit
  exact otherBit_ne _ hbit

/-- An incidence witness from membership in an undirected edge. -/
theorem edgeIncident_of_mem
    (e : H.edgeSet) {v : V} (hv : v ∈ (e.1 : Sym2 V)) :
    EdgeIncident H v e := by
  rcases hv with ⟨w, he⟩
  have hedge := e.2
  rw [he, _root_.SimpleGraph.mem_edgeSet] at hedge
  refine ⟨w, ?_, ?_⟩
  · exact hedge
  · exact he

/-- If every degree-four endpoint uses its avoiding bit, the blue edge is not
deleted. -/
theorem edge_not_deleted_of_endpoint_avoiding
    (e : H.edgeSet) (heblue : e ∈ I.blue)
    (outcome : Outcome (H := H))
    (havoid :
      ∀ v : {v : V // v ∈ degreeFourVertices H},
        ∀ hv : v.1 ∈ (e.1 : Sym2 V),
          outcome v =
            I.avoidingChoice e heblue v
              (edgeIncident_of_mem e hv)) :
    (e.1 : Sym2 V) ∉ I.deletedEdges outcome := by
  intro hdeleted
  rcases hdeleted with ⟨v, hev⟩
  have hincident := I.selectedEdge_incident outcome v
  rcases hincident with ⟨w, _hvw, hselected⟩
  have hvEdge : v.1 ∈ (e.1 : Sym2 V) := by
    rw [hev, hselected]
    exact Sym2.mem_mk_left _ _
  have havoidv := havoid v hvEdge
  have hne :=
    I.selectedEdge_ne_of_eq_avoidingChoice
      e heblue v (edgeIncident_of_mem e hvEdge)
      outcome havoidv
  apply hne
  apply Subtype.ext
  exact hev.symm

/-- The same criterion expressed as adjacency in the thinned graph. -/
theorem edge_mem_thinned_of_endpoint_avoiding
    (e : H.edgeSet) (heblue : e ∈ I.blue)
    (outcome : Outcome (H := H))
    (havoid :
      ∀ v : {v : V // v ∈ degreeFourVertices H},
        ∀ hv : v.1 ∈ (e.1 : Sym2 V),
          outcome v =
            I.avoidingChoice e heblue v
              (edgeIncident_of_mem e hv)) :
    (e.1 : Sym2 V) ∈ (I.thinnedGraph outcome).edgeSet := by
  have hnot :=
    I.edge_not_deleted_of_endpoint_avoiding
      e heblue outcome havoid
  have heout : s((e.1 : Sym2 V).out.1, (e.1 : Sym2 V).out.2) =
      (e.1 : Sym2 V) := by
    rw [Sym2.mk, (e.1 : Sym2 V).out_eq]
  rw [← heout]
  rw [_root_.SimpleGraph.mem_edgeSet]
  change
    (H.deleteEdges (I.deletedEdges outcome)).Adj
      (e.1 : Sym2 V).out.1 (e.1 : Sym2 V).out.2
  rw [_root_.SimpleGraph.deleteEdges_adj]
  constructor
  · rw [← _root_.SimpleGraph.mem_edgeSet, heout]
    exact e.2
  · rw [heout]
    exact hnot

/-- An edge outside the blue support is never selected for deletion. -/
theorem edge_mem_thinned_of_not_blue
    (e : H.edgeSet) (heblue : e ∉ I.blue)
    (outcome : Outcome (H := H)) :
    (e.1 : Sym2 V) ∈ (I.thinnedGraph outcome).edgeSet := by
  have hnot : (e.1 : Sym2 V) ∉ I.deletedEdges outcome := by
    intro hdeleted
    rcases hdeleted with ⟨v, hev⟩
    apply heblue
    have hselected := I.selectedEdge_blue outcome v
    have heq : I.selectedEdge outcome v = e := by
      apply Subtype.ext
      exact hev.symm
    simpa [heq] using hselected
  have heout :
      s((e.1 : Sym2 V).out.1, (e.1 : Sym2 V).out.2) =
        (e.1 : Sym2 V) := by
    rw [Sym2.mk, (e.1 : Sym2 V).out_eq]
  rw [← heout, _root_.SimpleGraph.mem_edgeSet]
  change
    (H.deleteEdges (I.deletedEdges outcome)).Adj
      (e.1 : Sym2 V).out.1 (e.1 : Sym2 V).out.2
  rw [_root_.SimpleGraph.deleteEdges_adj]
  exact ⟨by
    rw [← _root_.SimpleGraph.mem_edgeSet, heout]
    exact e.2, by simpa [heout] using hnot⟩

end BlueThinningInput

namespace BoundaryFamily

open ThinningConcentration

variable (I : BlueThinningInput H)
variable {t : ℕ} (M : Finset (Sym2 V))
variable (hcard : M.card = 16 * t)

/-- Canonical enumeration of an exact `16t`-edge family. -/
noncomputable def edgeAt (i : Fin (16 * t)) : Sym2 V :=
  (M.equivFin.symm (Fin.cast hcard.symm i)).1

theorem edgeAt_mem (i : Fin (16 * t)) :
    edgeAt M hcard i ∈ M :=
  (M.equivFin.symm (Fin.cast hcard.symm i)).2

theorem edgeAt_injective :
    Function.Injective (edgeAt M hcard) := by
  intro i j hij
  have hsub :
      M.equivFin.symm (Fin.cast hcard.symm i) =
        M.equivFin.symm (Fin.cast hcard.symm j) := by
    exact Subtype.ext hij
  have hcast :
      Fin.cast hcard.symm i = Fin.cast hcard.symm j :=
    M.equivFin.symm.injective hsub
  exact Fin.cast_injective hcard.symm hcast

/-- Endpoint slot zero is the first `Sym2.out` endpoint; slot one is the
second. -/
noncomputable def endpoint (i : Fin (16 * t)) (k : Fin 2) : V :=
  if k = 0 then (edgeAt M hcard i).out.1
  else (edgeAt M hcard i).out.2

theorem endpoint_mem (i : Fin (16 * t)) (k : Fin 2) :
    endpoint M hcard i k ∈ edgeAt M hcard i := by
  fin_cases k
  · exact Sym2.out_fst_mem _
  · exact Sym2.out_snd_mem _

theorem edgeAt_out_ne
    (hMH : M ⊆ H.edgeFinset) (i : Fin (16 * t)) :
    (edgeAt M hcard i).out.1 ≠ (edgeAt M hcard i).out.2 := by
  have hedgeFin := hMH (edgeAt_mem M hcard i)
  have hedgeSet :
      edgeAt M hcard i ∈ H.edgeSet := by
    simpa using hedgeFin
  have hadj :
      H.Adj (edgeAt M hcard i).out.1
        (edgeAt M hcard i).out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk] using hedgeSet
  exact hadj.ne

theorem endpoint_injective
    (hMH : M ⊆ H.edgeFinset)
    (hdisjoint : EdgeFamilyVertexDisjoint M) :
    Function.Injective
      (fun z : Fin (16 * t) × Fin 2 =>
        endpoint M hcard z.1 z.2) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ heq
  have hij : i = j := by
    by_contra hij
    have hedgeNe :
        edgeAt M hcard i ≠ edgeAt M hcard j :=
      fun h => hij (edgeAt_injective M hcard h)
    have hdisj :=
      hdisjoint
        (edgeAt_mem M hcard i)
        (edgeAt_mem M hcard j) hedgeNe
    change Disjoint
      (edgeAt M hcard i).toFinset
      (edgeAt M hcard j).toFinset at hdisj
    rw [Finset.disjoint_left] at hdisj
    apply hdisj (a := endpoint M hcard i k)
    · exact Sym2.mem_toFinset.mpr (endpoint_mem M hcard i k)
    · have heq' :
          endpoint M hcard i k = endpoint M hcard j l := heq
      rw [heq']
      exact Sym2.mem_toFinset.mpr (endpoint_mem M hcard j l)
  subst j
  have hkl : k = l := by
    fin_cases k <;> fin_cases l
    · rfl
    · exact False.elim
        ((edgeAt_out_ne M hcard hMH i) (by simpa [endpoint] using heq))
    · exact False.elim
        ((edgeAt_out_ne M hcard hMH i) (by simpa [endpoint] using heq.symm))
    · rfl
  subst l
  rfl

/-- A real degree-four endpoint uses its genuine outcome coordinate; a
non-degree-four endpoint gets a private dummy coordinate. -/
noncomputable def slotCoordinate
    (H : _root_.SimpleGraph V)
    (z : Fin (16 * t) × Fin 2) :
    {v : V // v ∈ degreeFourVertices H} ⊕
      (Fin (16 * t) × Fin 2) := by
  classical
  exact if hv : endpoint M hcard z.1 z.2 ∈ degreeFourVertices H
    then Sum.inl ⟨endpoint M hcard z.1 z.2, hv⟩
    else Sum.inr z

theorem slotCoordinate_injective
    (hMH : M ⊆ H.edgeFinset)
    (hdisjoint : EdgeFamilyVertexDisjoint M) :
    Function.Injective (slotCoordinate M hcard H) := by
  intro z w hzw
  classical
  unfold slotCoordinate at hzw
  split at hzw <;> split at hzw
  · have hendpoint :
        endpoint M hcard z.1 z.2 =
          endpoint M hcard w.1 w.2 :=
      congrArg (fun q => q.elim Subtype.val
        (fun x => endpoint M hcard x.1 x.2)) hzw
    exact endpoint_injective M hcard hMH hdisjoint hendpoint
  · cases hzw
  · cases hzw
  · exact Sum.inr_injective hzw

/-- The safe local value in a real endpoint slot is the avoiding choice for
that edge; dummy slots use zero. -/
noncomputable def expected
    (hMH : M ⊆ H.edgeFinset)
    (hMblue :
      ∀ e ∈ M, ∀ heH : e ∈ H.edgeSet,
        (⟨e, heH⟩ : H.edgeSet) ∈ I.blue)
    (z : Fin (16 * t) × Fin 2) : Fin 2 := by
  classical
  let e : H.edgeSet :=
    ⟨edgeAt M hcard z.1, by
      simpa using hMH (edgeAt_mem M hcard z.1)⟩
  by_cases hv :
      endpoint M hcard z.1 z.2 ∈ degreeFourVertices H
  · let v : {v : V // v ∈ degreeFourVertices H} :=
      ⟨endpoint M hcard z.1 z.2, hv⟩
    have heblue : e ∈ I.blue :=
      hMblue _ (edgeAt_mem M hcard z.1) _
    exact I.avoidingChoice e
      heblue v
      (BlueThinningInput.edgeIncident_of_mem e
        (endpoint_mem M hcard z.1 z.2))
  · exact 0

/-- Number of indexed family edges surviving a genuine thinning outcome. -/
noncomputable def retained
    (outcome : BlueThinningInput.Outcome (H := H)) : ℕ := by
  classical
  exact (M.filter fun e =>
    e ∈ (I.thinnedGraph outcome).edgeSet).card

theorem expected_eq_avoiding
    (hMH : M ⊆ H.edgeFinset)
    (hMblue :
      ∀ e ∈ M, ∀ heH : e ∈ H.edgeSet,
        (⟨e, heH⟩ : H.edgeSet) ∈ I.blue)
    (z : Fin (16 * t) × Fin 2)
    (hv : endpoint M hcard z.1 z.2 ∈ degreeFourVertices H) :
    let e : H.edgeSet :=
      ⟨edgeAt M hcard z.1, by
        simpa using hMH (edgeAt_mem M hcard z.1)⟩
    let v : {v : V // v ∈ degreeFourVertices H} :=
      ⟨endpoint M hcard z.1 z.2, hv⟩
    expected I M hcard hMH hMblue z =
      I.avoidingChoice e
        (hMblue _ (edgeAt_mem M hcard z.1) _) v
        (BlueThinningInput.edgeIncident_of_mem e
          (endpoint_mem M hcard z.1 z.2)) := by
  classical
  simp [expected, hv]

theorem safe_word_le_retained
    (hMH : M ⊆ H.edgeFinset)
    (hMblue :
      ∀ e ∈ M, ∀ heH : e ∈ H.edgeSet,
        (⟨e, heH⟩ : H.edgeSet) ∈ I.blue)
    (hdisjoint : EdgeFamilyVertexDisjoint M)
    (ω :
      {v : V // v ∈ degreeFourVertices H} ⊕
        (Fin (16 * t) × Fin 2) → Fin 2) :
    safeCount
        (wordEquiv (expected I M hcard hMH hMblue)
          fun z => ω (slotCoordinate M hcard H z)) ≤
      retained I M (fun v => ω (Sum.inl v)) := by
  classical
  let safe : Finset (Fin (16 * t)) :=
    Finset.univ.filter fun i =>
      wordEquiv (expected I M hcard hMH hMblue)
        (fun z => ω (slotCoordinate M hcard H z)) i = 0
  let surviving : Finset (Sym2 V) :=
    M.filter fun e =>
      e ∈ (I.thinnedGraph (fun v => ω (Sum.inl v))).edgeSet
  let f : {i : Fin (16 * t) // i ∈ safe} →
      {e : Sym2 V // e ∈ surviving} :=
    fun i => ⟨edgeAt M hcard i.1, by
      have hsafe :
          ∀ k,
            ω (slotCoordinate M hcard H (i.1, k)) =
              expected I M hcard hMH hMblue (i.1, k) := by
        exact
          (wordEquiv_apply_eq_zero_iff
            (expected I M hcard hMH hMblue)
            (fun z => ω (slotCoordinate M hcard H z)) i.1).mp
            (Finset.mem_filter.mp i.2).2
      have hedgeSet :
          edgeAt M hcard i.1 ∈ H.edgeSet := by
        simpa using hMH (edgeAt_mem M hcard i.1)
      let e : H.edgeSet := ⟨edgeAt M hcard i.1, hedgeSet⟩
      have heblue : e ∈ I.blue :=
        hMblue _ (edgeAt_mem M hcard i.1) _
      have havoid :
          ∀ v : {v : V // v ∈ degreeFourVertices H},
            ∀ hv : v.1 ∈ (e.1 : Sym2 V),
              (fun q => ω (Sum.inl q)) v =
                I.avoidingChoice e heblue v
                  (BlueThinningInput.edgeIncident_of_mem e hv) := by
        intro v hv
        have heout :
            s((e.1 : Sym2 V).out.1,
              (e.1 : Sym2 V).out.2) = (e.1 : Sym2 V) := by
          rw [Sym2.mk, (e.1 : Sym2 V).out_eq]
        have hvCases :
            v.1 = (e.1 : Sym2 V).out.1 ∨
              v.1 = (e.1 : Sym2 V).out.2 := by
          rw [← heout, Sym2.mem_iff] at hv
          exact hv
        rcases hvCases with hv0 | hv1
        · have hs := hsafe 0
          have hbad :
              endpoint M hcard i.1 0 ∈ degreeFourVertices H := by
            simpa [endpoint, hv0] using v.2
          have hvEq :
              (⟨endpoint M hcard i.1 0, hbad⟩ :
                {v : V // v ∈ degreeFourVertices H}) = v := by
            apply Subtype.ext
            simpa [endpoint] using hv0.symm
          have hslot :
              slotCoordinate M hcard H (i.1, 0) = Sum.inl v := by
            simp only [slotCoordinate, dif_pos hbad]
            rw [hvEq]
          rw [hslot] at hs
          calc
            ω (Sum.inl v) =
                expected I M hcard hMH hMblue (i.1, 0) := hs
            _ = I.avoidingChoice e heblue v
                (BlueThinningInput.edgeIncident_of_mem e hv) := by
              simpa [hvEq] using
                expected_eq_avoiding I M hcard hMH hMblue
                  (i.1, 0) hbad
        · have hs := hsafe 1
          have hbad :
              endpoint M hcard i.1 1 ∈ degreeFourVertices H := by
            simpa [endpoint, hv1] using v.2
          have hvEq :
              (⟨endpoint M hcard i.1 1, hbad⟩ :
                {v : V // v ∈ degreeFourVertices H}) = v := by
            apply Subtype.ext
            simpa [endpoint] using hv1.symm
          have hslot :
              slotCoordinate M hcard H (i.1, 1) = Sum.inl v := by
            simp only [slotCoordinate, dif_pos hbad]
            rw [hvEq]
          rw [hslot] at hs
          calc
            ω (Sum.inl v) =
                expected I M hcard hMH hMblue (i.1, 1) := hs
            _ = I.avoidingChoice e heblue v
                (BlueThinningInput.edgeIncident_of_mem e hv) := by
              simpa [hvEq] using
                expected_eq_avoiding I M hcard hMH hMblue
                  (i.1, 1) hbad
      have hsurvive :=
        I.edge_mem_thinned_of_endpoint_avoiding
          e heblue (fun v => ω (Sum.inl v)) havoid
      exact Finset.mem_filter.mpr
        ⟨edgeAt_mem M hcard i.1, hsurvive⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply edgeAt_injective M hcard
    simpa [f] using congrArg Subtype.val hij
  calc
    safeCount
        (wordEquiv (expected I M hcard hMH hMblue)
          fun z => ω (slotCoordinate M hcard H z)) =
        safe.card := by rfl
    _ = Fintype.card {i : Fin (16 * t) // i ∈ safe} := by
      rw [Fintype.card_coe]
    _ ≤ Fintype.card {e : Sym2 V // e ∈ surviving} :=
      Fintype.card_le_of_injective f hf
    _ = surviving.card := by rw [Fintype.card_coe]
    _ = retained I M (fun v => ω (Sum.inl v)) := by rfl

/-- Fixed-boundary concentration for genuine thinning outcomes. -/
theorem bad_outcomes_mul_failureFactor_le_total
    (hcard : M.card = 16 * t)
    (hMH : M ⊆ H.edgeFinset)
    (hMblue :
      ∀ e ∈ M, ∀ heH : e ∈ H.edgeSet,
        (⟨e, heH⟩ : H.edgeSet) ∈ I.blue)
    (hdisjoint : EdgeFamilyVertexDisjoint M) :
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome (H := H) =>
        retained I M outcome < t).card) * 4 ^ (t + 1) ≤
      Fintype.card (BlueThinningInput.Outcome (H := H)) := by
  classical
  exact
    binaryOutcomes_bad_mul_failureFactor_le_total
      t (slotCoordinate M hcard H)
      (slotCoordinate_injective M hcard hMH hdisjoint)
      (expected I M hcard hMH hMblue)
      (fun outcome => retained I M outcome)
      (safe_word_le_retained I M hcard hMH hMblue hdisjoint)

end BoundaryFamily

/-! The segment quotient has both blue edges and deterministic red edges.
The following mixed version of the fixed-boundary estimate treats a non-blue
edge as automatically retained, while retaining the same four-valued
lower-tail estimate. -/

namespace MixedBoundaryFamily

open ThinningConcentration

variable (I : BlueThinningInput H)
variable {t : ℕ} (M : Finset (Sym2 V))
variable (hcard : M.card = 16 * t)

/-- The prescribed endpoint word for a mixed boundary family.  Blue edges
use their avoiding choices; non-blue edges use dummy zero bits because their
survival is deterministic. -/
noncomputable def expected
    (hMH : M ⊆ H.edgeFinset)
    (z : Fin (16 * t) × Fin 2) : Fin 2 := by
  classical
  let e : H.edgeSet :=
    ⟨BoundaryFamily.edgeAt M hcard z.1, by
      simpa using hMH (BoundaryFamily.edgeAt_mem M hcard z.1)⟩
  by_cases heblue : e ∈ I.blue
  · by_cases hv :
      BoundaryFamily.endpoint M hcard z.1 z.2 ∈
        degreeFourVertices H
    · let v : {v : V // v ∈ degreeFourVertices H} :=
        ⟨BoundaryFamily.endpoint M hcard z.1 z.2, hv⟩
      exact
        I.avoidingChoice e heblue v
          (BlueThinningInput.edgeIncident_of_mem e
            (BoundaryFamily.endpoint_mem M hcard z.1 z.2))
    · exact 0
  · exact 0

theorem expected_eq_avoiding
    (hMH : M ⊆ H.edgeFinset)
    (z : Fin (16 * t) × Fin 2)
    (heblue :
      let e : H.edgeSet :=
        ⟨BoundaryFamily.edgeAt M hcard z.1, by
          simpa using hMH (BoundaryFamily.edgeAt_mem M hcard z.1)⟩
      e ∈ I.blue)
    (hv :
      BoundaryFamily.endpoint M hcard z.1 z.2 ∈
        degreeFourVertices H) :
    let e : H.edgeSet :=
      ⟨BoundaryFamily.edgeAt M hcard z.1, by
        simpa using hMH (BoundaryFamily.edgeAt_mem M hcard z.1)⟩
    let v : {v : V // v ∈ degreeFourVertices H} :=
      ⟨BoundaryFamily.endpoint M hcard z.1 z.2, hv⟩
    expected I M hcard hMH z =
      I.avoidingChoice e heblue v
        (BlueThinningInput.edgeIncident_of_mem e
          (BoundaryFamily.endpoint_mem M hcard z.1 z.2)) := by
  classical
  simp [expected, heblue, hv]

/-- A safe endpoint word retains every selected mixed-family edge: the blue
case uses the avoiding-choice lemma, and the non-blue case is automatic. -/
theorem safe_word_le_retained
    (hMH : M ⊆ H.edgeFinset)
    (hdisjoint : EdgeFamilyVertexDisjoint M)
    (ω :
      {v : V // v ∈ degreeFourVertices H} ⊕
        (Fin (16 * t) × Fin 2) → Fin 2) :
    safeCount
        (wordEquiv (expected I M hcard hMH)
          fun z => ω (BoundaryFamily.slotCoordinate M hcard H z)) ≤
      BoundaryFamily.retained I M (fun v => ω (Sum.inl v)) := by
  classical
  let safe : Finset (Fin (16 * t)) :=
    Finset.univ.filter fun i =>
      wordEquiv (expected I M hcard hMH)
        (fun z => ω (BoundaryFamily.slotCoordinate M hcard H z)) i = 0
  let surviving : Finset (Sym2 V) :=
    M.filter fun e =>
      e ∈ (I.thinnedGraph (fun v => ω (Sum.inl v))).edgeSet
  let f : {i : Fin (16 * t) // i ∈ safe} →
      {e : Sym2 V // e ∈ surviving} :=
    fun i =>
      ⟨BoundaryFamily.edgeAt M hcard i.1, by
        have hsafe :
            ∀ k,
              ω (BoundaryFamily.slotCoordinate M hcard H (i.1, k)) =
                expected I M hcard hMH (i.1, k) :=
          (wordEquiv_apply_eq_zero_iff
            (expected I M hcard hMH)
            (fun z => ω (BoundaryFamily.slotCoordinate M hcard H z))
            i.1).mp (Finset.mem_filter.mp i.2).2
        have hedgeSet :
            BoundaryFamily.edgeAt M hcard i.1 ∈ H.edgeSet := by
          simpa using hMH (BoundaryFamily.edgeAt_mem M hcard i.1)
        let e : H.edgeSet :=
          ⟨BoundaryFamily.edgeAt M hcard i.1, hedgeSet⟩
        have hsurvive :
            (e.1 : Sym2 V) ∈
              (I.thinnedGraph (fun v => ω (Sum.inl v))).edgeSet := by
          by_cases heblue : e ∈ I.blue
          · apply
              I.edge_mem_thinned_of_endpoint_avoiding
                e heblue (fun v => ω (Sum.inl v))
            intro v hv
            have heout :
                s((e.1 : Sym2 V).out.1,
                  (e.1 : Sym2 V).out.2) = (e.1 : Sym2 V) := by
              rw [Sym2.mk, (e.1 : Sym2 V).out_eq]
            have hvCases :
                v.1 = (e.1 : Sym2 V).out.1 ∨
                  v.1 = (e.1 : Sym2 V).out.2 := by
              rw [← heout, Sym2.mem_iff] at hv
              exact hv
            rcases hvCases with hv0 | hv1
            · have hs := hsafe 0
              have hbad :
                  BoundaryFamily.endpoint M hcard i.1 0 ∈
                    degreeFourVertices H := by
                simpa [BoundaryFamily.endpoint, hv0] using v.2
              have hvEq :
                  (⟨BoundaryFamily.endpoint M hcard i.1 0, hbad⟩ :
                    {v : V // v ∈ degreeFourVertices H}) = v := by
                apply Subtype.ext
                simpa [BoundaryFamily.endpoint] using hv0.symm
              have hslot :
                  BoundaryFamily.slotCoordinate M hcard H (i.1, 0) =
                    Sum.inl v := by
                simp only [BoundaryFamily.slotCoordinate, dif_pos hbad]
                rw [hvEq]
              rw [hslot] at hs
              calc
                ω (Sum.inl v) =
                    expected I M hcard hMH (i.1, 0) := hs
                _ = I.avoidingChoice e heblue v
                    (BlueThinningInput.edgeIncident_of_mem e hv) := by
                  simpa [hvEq] using
                    expected_eq_avoiding I M hcard hMH
                      (i.1, 0) heblue hbad
            · have hs := hsafe 1
              have hbad :
                  BoundaryFamily.endpoint M hcard i.1 1 ∈
                    degreeFourVertices H := by
                simpa [BoundaryFamily.endpoint, hv1] using v.2
              have hvEq :
                  (⟨BoundaryFamily.endpoint M hcard i.1 1, hbad⟩ :
                    {v : V // v ∈ degreeFourVertices H}) = v := by
                apply Subtype.ext
                simpa [BoundaryFamily.endpoint] using hv1.symm
              have hslot :
                  BoundaryFamily.slotCoordinate M hcard H (i.1, 1) =
                    Sum.inl v := by
                simp only [BoundaryFamily.slotCoordinate, dif_pos hbad]
                rw [hvEq]
              rw [hslot] at hs
              calc
                ω (Sum.inl v) =
                    expected I M hcard hMH (i.1, 1) := hs
                _ = I.avoidingChoice e heblue v
                    (BlueThinningInput.edgeIncident_of_mem e hv) := by
                  simpa [hvEq] using
                    expected_eq_avoiding I M hcard hMH
                      (i.1, 1) heblue hbad
          · exact
              I.edge_mem_thinned_of_not_blue
                e heblue (fun v => ω (Sum.inl v))
        exact Finset.mem_filter.mpr
          ⟨BoundaryFamily.edgeAt_mem M hcard i.1, hsurvive⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply BoundaryFamily.edgeAt_injective M hcard
    simpa [f] using congrArg Subtype.val hij
  calc
    safeCount
        (wordEquiv (expected I M hcard hMH)
          fun z => ω (BoundaryFamily.slotCoordinate M hcard H z)) =
        safe.card := by rfl
    _ = Fintype.card {i : Fin (16 * t) // i ∈ safe} := by
      rw [Fintype.card_coe]
    _ ≤ Fintype.card {e : Sym2 V // e ∈ surviving} :=
      Fintype.card_le_of_injective f hf
    _ = surviving.card := by rw [Fintype.card_coe]
    _ = BoundaryFamily.retained I M (fun v => ω (Sum.inl v)) := by
      rfl

/-- Fixed-boundary concentration for a mixed red/blue edge family. -/
theorem bad_outcomes_mul_failureFactor_le_total
    (hcard : M.card = 16 * t)
    (hMH : M ⊆ H.edgeFinset)
    (hdisjoint : EdgeFamilyVertexDisjoint M) :
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome (H := H) =>
        BoundaryFamily.retained I M outcome < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card (BlueThinningInput.Outcome (H := H)) := by
  classical
  exact
    binaryOutcomes_bad_mul_failureFactor_le_total
      t (BoundaryFamily.slotCoordinate M hcard H)
      (BoundaryFamily.slotCoordinate_injective M hcard hMH hdisjoint)
      (expected I M hcard hMH)
      (fun outcome => BoundaryFamily.retained I M outcome)
      (safe_word_le_retained I M hcard hMH hdisjoint)

end MixedBoundaryFamily

/-- Number of edges of a physical family retained by an outcome. -/
noncomputable def retainedEdgeCount
    (I : BlueThinningInput H) (B : Finset (Sym2 V))
    (outcome : BlueThinningInput.Outcome (H := H)) : ℕ := by
  classical
  exact (B.filter fun e =>
    e ∈ (I.thinnedGraph outcome).edgeSet).card

/-- The fixed-family lower-tail bound.  A maximum-degree-four family first
loses a factor eight when made vertex-disjoint and a factor sixteen in the
four-valued concentration estimate. -/
theorem retainedEdgeCount_bad_mul_failureFactor_le_total
    (I : BlueThinningInput H)
    (B : Finset (Sym2 V))
    (hBH : B ⊆ H.edgeFinset)
    (hBblue :
      ∀ e ∈ B, ∀ heH : e ∈ H.edgeSet,
        (⟨e, heH⟩ : H.edgeSet) ∈ I.blue) :
    let t := B.card / 128
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome (H := H) =>
          retainedEdgeCount I B outcome < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card (BlueThinningInput.Outcome (H := H)) := by
  classical
  let t := B.card / 128
  have hlarge : 128 * t ≤ B.card := by
    exact Nat.mul_div_le B.card 128
  obtain ⟨M, hMB, hMdisjoint, hMcard⟩ :=
    exists_vertexDisjoint_subfamily_card
      H I.max_degree_four B hBH hlarge
  have hMblue :
      ∀ e ∈ M, ∀ heH : e ∈ H.edgeSet,
        (⟨e, heH⟩ : H.edgeSet) ∈ I.blue := by
    intro e heM heH
    exact hBblue e (hMB heM) heH
  have hfixed :=
    BoundaryFamily.bad_outcomes_mul_failureFactor_le_total
      I M hMcard
        (by
          intro e heM
          simpa using hBH (hMB heM))
        hMblue hMdisjoint
  let badB : Finset (BlueThinningInput.Outcome (H := H)) :=
    Finset.univ.filter fun outcome =>
      retainedEdgeCount I B outcome < t
  let badM : Finset (BlueThinningInput.Outcome (H := H)) :=
    Finset.univ.filter fun outcome =>
      BoundaryFamily.retained I M outcome < t
  have hbadSubset : badB ⊆ badM := by
    intro outcome houtcome
    have hbadB :
        retainedEdgeCount I B outcome < t := by
      simpa [badB] using houtcome
    have hcount :
        BoundaryFamily.retained I M outcome ≤
          retainedEdgeCount I B outcome := by
      apply Finset.card_le_card
      intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨hMB he.1, he.2⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcount.trans_lt hbadB⟩
  calc
    (Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome (H := H) =>
          retainedEdgeCount I B outcome < t).card *
        4 ^ (t + 1) =
        badB.card * 4 ^ (t + 1) := by rfl
    _ ≤ badM.card * 4 ^ (t + 1) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hbadSubset)
    _ ≤ Fintype.card (BlueThinningInput.Outcome (H := H)) := by
      simpa [badM] using hfixed

/-- Mixed red/blue version of the retained-edge lower-tail estimate.  This is
the form required by the physical segment quotient. -/
theorem retainedEdgeCount_mixed_bad_mul_failureFactor_le_total
    (I : BlueThinningInput H)
    (B : Finset (Sym2 V))
    (hBH : B ⊆ H.edgeFinset) :
    let t := B.card / 128
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome (H := H) =>
          retainedEdgeCount I B outcome < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card (BlueThinningInput.Outcome (H := H)) := by
  classical
  let t := B.card / 128
  have hlarge : 128 * t ≤ B.card := Nat.mul_div_le B.card 128
  obtain ⟨M, hMB, hMdisjoint, hMcard⟩ :=
    exists_vertexDisjoint_subfamily_card
      H I.max_degree_four B hBH hlarge
  have hfixed :=
    MixedBoundaryFamily.bad_outcomes_mul_failureFactor_le_total
      I M hMcard
        (by
          intro e heM
          simpa using hBH (hMB heM))
        hMdisjoint
  let badB : Finset (BlueThinningInput.Outcome (H := H)) :=
    Finset.univ.filter fun outcome =>
      retainedEdgeCount I B outcome < t
  let badM : Finset (BlueThinningInput.Outcome (H := H)) :=
    Finset.univ.filter fun outcome =>
      BoundaryFamily.retained I M outcome < t
  have hbadSubset : badB ⊆ badM := by
    intro outcome houtcome
    have hbadB : retainedEdgeCount I B outcome < t := by
      simpa [badB] using houtcome
    have hcount :
        BoundaryFamily.retained I M outcome ≤
          retainedEdgeCount I B outcome := by
      apply Finset.card_le_card
      intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨hMB he.1, he.2⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcount.trans_lt hbadB⟩
  calc
    (Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome (H := H) =>
          retainedEdgeCount I B outcome < t).card *
        4 ^ (t + 1) =
        badB.card * 4 ^ (t + 1) := by rfl
    _ ≤ badM.card * 4 ^ (t + 1) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hbadSubset)
    _ ≤ Fintype.card (BlueThinningInput.Outcome (H := H)) := by
      simpa [badM] using hfixed

/-- Instance-stable form of the mixed fixed-family estimate.  Stating the
support hypothesis in `edgeSet` avoids exposing the implementation `Fintype`
chosen when `edgeFinset` is elaborated in another module. -/
theorem retainedEdgeCount_mixed_bad_mul_failureFactor_le_total_of_edgeSet
    (I : BlueThinningInput H)
    (B : Finset (Sym2 V))
    (hBH : ∀ e ∈ B, e ∈ H.edgeSet) :
    let t := B.card / 128
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome (H := H) =>
          retainedEdgeCount I B outcome < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card (BlueThinningInput.Outcome (H := H)) := by
  apply retainedEdgeCount_mixed_bad_mul_failureFactor_le_total I B
  intro e he
  exact _root_.SimpleGraph.mem_edgeFinset.mpr (hBH e he)

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
