import Lax17Proofs.Source.TreewidthSparsifierTheorem51Outcome

namespace Lax17Proofs

universe u v w

/-!
# Initial terminals and red rails

This module identifies the first left nail set with the abstract rail labels
used by the physical cut-matching transcript.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- A half-expander on at least two vertices contains a round. -/
theorem rounds_nonempty
    (E : ExpanderBlocks P count)
    (hheight : 2 ≤ h) (i : Fin count) :
    0 < (E.rounds i).length := by
  by_contra hempty
  have hempty' : E.rounds i = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have : 0 < (E.rounds i).length := List.length_pos_of_mem hx
    omega
  let x : Fin h := ⟨0, by omega⟩
  let S : Finset (Fin h) := {x}
  have hbound :=
    (CutMatchingGame.isHalfEdgeExpander_iff (E.rounds i)).mp
      (E.each_halfExpander i) S (by simp [S])
      (by simp [S]; omega)
  simp [hempty', S, edgeBoundaryCount] at hbound

/-- Positive restart count gives at least one physically recorded layer. -/
theorem records_nonempty
    (E : ExpanderBlocks P count)
    (hheight : 2 ≤ h) (hcount : 0 < count) :
    0 < E.finalState.records.length := by
  have hi : (0 : ℕ) < count := hcount
  let i : Fin count := ⟨0, hi⟩
  have hroundPos : 0 < (E.rounds i).length :=
    E.rounds_nonempty hheight i
  have hflatPos :
      0 < (List.ofFn E.rounds).flatten.length := by
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_pos'
      (fun _ _ => Nat.zero_le _)
      ⟨i, Finset.mem_univ i, hroundPos⟩
  rw [← E.records_length_eq_flattened_length] at hflatPos
  exact hflatPos

/-- The first stored record. -/
def firstRecord
    (E : ExpanderBlocks P count)
    (hrecords : 0 < E.finalState.records.length) :
    Fin E.finalState.records.length :=
  ⟨0, hrecords⟩

/-- Under the physical width budget, the first record is realized in the
first path-of-sets cluster. -/
theorem firstRecord_index_eq_firstIndex
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length) :
    (E.recordAt (E.firstRecord hrecords)).index = P.firstIndex := by
  apply Fin.ext
  rw [E.recordAt_index_eq hbudget]
  rfl

/-- Every initial terminal lies on exactly one labelled red rail. -/
theorem initialTerminal_has_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {v : V} (hv : v ∈ P.left P.firstIndex) :
    ∃ x : Fin h, E.RedCarrier hbudget v x := by
  classical
  let j := E.firstRecord hrecords
  have hindex := E.firstRecord_index_eq_firstIndex hbudget hrecords
  let named :
      {z : V // z ∈ P.left (E.recordAt j).index} :=
    ⟨v, by rw [hindex]; exact hv⟩
  let x : Fin h := (E.recordAt j).label.symm named
  refine ⟨x, Or.inl ⟨j, ?_⟩⟩
  have hsource :
      (E.localRedPath j x).source = v := by
    rw [E.localRedPath_source]
    exact congrArg Subtype.val
      ((E.recordAt j).label.apply_symm_apply named)
  rw [← hsource]
  exact GraphPath.source_mem_vertexSet _

/-- The rail owner is injective on the first terminal set. -/
theorem railOwner_injective_on_initialTerminals
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (fallback : Fin h) :
    Set.InjOn (E.railOwner hbudget fallback)
      (P.left P.firstIndex : Set V) := by
  intro v hv w hw howner
  classical
  obtain ⟨x, hvx⟩ :=
    E.initialTerminal_has_redCarrier hbudget hrecords hv
  obtain ⟨y, hwy⟩ :=
    E.initialTerminal_has_redCarrier hbudget hrecords hw
  have hxy : x = y := by
    rw [E.railOwner_eq_of_redCarrier hbudget fallback hvx,
      E.railOwner_eq_of_redCarrier hbudget fallback hwy] at howner
    exact howner
  let j := E.firstRecord hrecords
  have hindex := E.firstRecord_index_eq_firstIndex hbudget hrecords
  let vx :
      {z : V // z ∈ P.left (E.recordAt j).index} :=
    ⟨v, by rw [hindex]; exact hv⟩
  let wy :
      {z : V // z ∈ P.left (E.recordAt j).index} :=
    ⟨w, by rw [hindex]; exact hw⟩
  have hvx' :
      E.RedCarrier hbudget v ((E.recordAt j).label.symm vx) := by
    refine Or.inl ⟨j, ?_⟩
    have hsource :
        (E.localRedPath j ((E.recordAt j).label.symm vx)).source = v := by
      rw [E.localRedPath_source]
      exact congrArg Subtype.val
        ((E.recordAt j).label.apply_symm_apply vx)
    rw [← hsource]
    exact GraphPath.source_mem_vertexSet _
  have hwy' :
      E.RedCarrier hbudget w ((E.recordAt j).label.symm wy) := by
    refine Or.inl ⟨j, ?_⟩
    have hsource :
        (E.localRedPath j ((E.recordAt j).label.symm wy)).source = w := by
      rw [E.localRedPath_source]
      exact congrArg Subtype.val
        ((E.recordAt j).label.apply_symm_apply wy)
    rw [← hsource]
    exact GraphPath.source_mem_vertexSet _
  have hvLabel :
      (E.recordAt j).label.symm vx = x := by
    exact E.redCarrier_unique hbudget hvx' hvx
  have hwLabel :
      (E.recordAt j).label.symm wy = y := by
    exact E.redCarrier_unique hbudget hwy' hwy
  have hvw : vx = wy := by
    apply (E.recordAt j).label.symm.injective
    simpa [hvLabel, hwLabel, hxy]
  exact congrArg Subtype.val hvw

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
