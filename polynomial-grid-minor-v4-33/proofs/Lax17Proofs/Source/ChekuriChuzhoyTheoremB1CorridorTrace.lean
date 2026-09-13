import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorCore

namespace Lax17Proofs

universe u v w

/-!
# Full columns through an auxiliary degree-two corridor

This module isolates the boundary-to-boundary trace argument used during hill
elimination in Chekuri--Chuzhoy Appendix B.  A column is kept as a full path
between the two boundary rows.  Contacts with the active rows are consequences,
not fields of the column state.

The contact trace is built from the same endpoint-padded contact list used by
`CompleteLinkageContactTrace`.  That older structure is tied to an
`IndexedAuxiliaryPrefix`; the definitions below apply to an arbitrary current
linkage and an arbitrary finite corridor inside its auxiliary graph.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

open IndexedAuxiliaryPrefix

namespace AuxiliaryCorridor

variable {L : PerfectPathPacking G A B} {activeCount : ℕ}

/-- The lower boundary row. -/
def lowerIndex (C : AuxiliaryCorridor L activeCount) : L.Index :=
  C.index ⟨0, by omega⟩

/-- The upper boundary row. -/
def upperIndex (C : AuxiliaryCorridor L activeCount) : L.Index :=
  C.index ⟨activeCount + 1, by omega⟩

/-- The graph path of the row at corridor position `r`. -/
def rowPath (C : AuxiliaryCorridor L activeCount)
    (r : Fin (activeCount + 2)) : GraphPath G :=
  L.path (C.index r)

/-- Distinct corridor positions name distinct linkage paths. -/
theorem index_ne_of_ne (C : AuxiliaryCorridor L activeCount)
    {r s : Fin (activeCount + 2)} (hrs : r ≠ s) :
    C.index r ≠ C.index s := by
  intro h
  exact hrs (C.index_injective h)

/-- The two boundary rows are distinct. -/
theorem lowerIndex_ne_upperIndex
    (C : AuxiliaryCorridor L activeCount) :
    C.lowerIndex ≠ C.upperIndex := by
  apply C.index_ne_of_ne
  intro h
  have hval : 0 = activeCount + 1 := congrArg Fin.val h
  omega

/-- A path avoids the linkage outside a corridor when every linkage path not
named by a corridor row is vertex-disjoint from it. -/
def AvoidsOutside (C : AuxiliaryCorridor L activeCount)
    (P : GraphPath G) : Prop :=
  ∀ j : L.Index, j ∉ Set.range C.index →
    Disjoint P.vertexSet (L.path j).vertexSet

/-- Boundary membership makes both endpoints linkage vertices. -/
theorem endpoints_mem_linkage
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet) :
    P.source ∈ L.toPathPacking.vertexSet ∧
      P.target ∈ L.toPathPacking.vertexSet := by
  constructor
  · exact (L.toPathPacking.mem_vertexSet).2 ⟨C.lowerIndex, hsource⟩
  · exact (L.toPathPacking.mem_vertexSet).2 ⟨C.upperIndex, htarget⟩

/-- A boundary-to-boundary corridor path is nontrivial because the two boundary
rows are distinct paths of a path packing. -/
theorem source_ne_target
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet) :
    P.source ≠ P.target := by
  intro h
  have hdisj :
      Disjoint
        (L.path C.lowerIndex).vertexSet
        (L.path C.upperIndex).vertexSet :=
    L.toPathPacking.node_disjoint C.lowerIndex_ne_upperIndex
  exact Finset.disjoint_left.mp hdisj hsource (by simpa [h] using htarget)

/-- Every endpoint-padded linkage contact of an outside-avoiding path belongs
to a unique corridor row. -/
theorem exists_unique_row_of_endpointContact
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet)
    (havoid : C.AvoidsOutside P)
    (r : Fin (endpointContactTraceLen L P + 1)) :
    ∃! q : Fin (activeCount + 2),
      C.index q =
        endpointContactIndex L P
          (C.endpoints_mem_linkage P hsource htarget).1
          (C.endpoints_mem_linkage P hsource htarget).2 r := by
  classical
  let hs := (C.endpoints_mem_linkage P hsource htarget).1
  let ht := (C.endpoints_mem_linkage P hsource htarget).2
  let j := endpointContactIndex L P hs ht r
  have hex : ∃ q : Fin (activeCount + 2), C.index q = j := by
    by_contra hno
    have hjOutside : j ∉ Set.range C.index := by
      simpa [Set.mem_range] using hno
    have hdisj := havoid j hjOutside
    exact Finset.disjoint_left.mp hdisj
      (endpointContact_mem_path L P r)
      (endpointContact_mem_contactIndex_path L P hs ht r)
  rcases hex with ⟨q, hq⟩
  refine ⟨q, by simpa [j, hs, ht] using hq, ?_⟩
  intro q' hq'
  apply C.index_injective
  exact hq'.trans (by simpa [j, hs, ht] using hq.symm)

/-- The corridor position of an endpoint-padded linkage contact. -/
noncomputable def endpointContactPosition
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet)
    (havoid : C.AvoidsOutside P)
    (r : Fin (endpointContactTraceLen L P + 1)) :
    Fin (activeCount + 2) :=
  Classical.choose
    (C.exists_unique_row_of_endpointContact P hsource htarget havoid r)

theorem row_endpointContactPosition
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet)
    (havoid : C.AvoidsOutside P)
    (r : Fin (endpointContactTraceLen L P + 1)) :
    C.index (C.endpointContactPosition P hsource htarget havoid r) =
      endpointContactIndex L P
        (C.endpoints_mem_linkage P hsource htarget).1
        (C.endpoints_mem_linkage P hsource htarget).2 r :=
  (Classical.choose_spec
    (C.exists_unique_row_of_endpointContact P hsource htarget havoid r)).1

/-- The numeric corridor positions of consecutive endpoint contacts form a
unit-step trace. -/
theorem endpointContactPosition_unitStep
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet)
    (havoid : C.AvoidsOutside P) :
    UnitStepNatTrace (endpointContactTraceLen L P)
      (fun r => (C.endpointContactPosition P hsource htarget havoid r).1) := by
  classical
  let hs := (C.endpoints_mem_linkage P hsource htarget).1
  let ht := (C.endpoints_mem_linkage P hsource htarget).2
  have hne := C.source_ne_target P hsource htarget
  intro r
  let q0 :=
    C.endpointContactPosition P hsource htarget havoid
      ⟨r.1, by omega⟩
  let q1 :=
    C.endpointContactPosition P hsource htarget havoid
      ⟨r.1 + 1, by omega⟩
  have hrow0 :
      C.index q0 =
        endpointContactIndex L P hs ht ⟨r.1, by omega⟩ := by
    simpa [q0, hs, ht] using
      C.row_endpointContactPosition P hsource htarget havoid
        ⟨r.1, by omega⟩
  have hrow1 :
      C.index q1 =
        endpointContactIndex L P hs ht ⟨r.1 + 1, by omega⟩ := by
    simpa [q1, hs, ht] using
      C.row_endpointContactPosition P hsource htarget havoid
        ⟨r.1 + 1, by omega⟩
  have haux :
      endpointContactIndex L P hs ht ⟨r.1, by omega⟩ =
          endpointContactIndex L P hs ht ⟨r.1 + 1, by omega⟩ ∨
        (linkageAuxGraph L).Adj
          (endpointContactIndex L P hs ht ⟨r.1, by omega⟩)
          (endpointContactIndex L P hs ht ⟨r.1 + 1, by omega⟩) := by
    exact aux_adj_or_eq_of_clean_segment
      (L := L)
      (P.segmentOfBefore
        (endpointContact_before_succ_of_source_ne_target L P hne r))
      (by
        simpa using
          endpointContact_mem_contactIndex_path L P hs ht
            ⟨r.1, by omega⟩)
      (by
        simpa using
          endpointContact_mem_contactIndex_path L P hs ht
            ⟨r.1 + 1, by omega⟩)
      (endpointContactsCleanConsecutive_of_source_ne_target L P hne r)
  rcases haux with heq | hadj
  · have hq : q0 = q1 :=
      C.index_injective (hrow0.trans (heq.trans hrow1.symm))
    simp [q0, q1, hq]
  · have hcon : FinConsecutive q0 q1 :=
      C.adj_iff_consecutive.mp (by simpa [hrow0, hrow1] using hadj)
    rcases hcon with hforward | hbackward
    · constructor <;> dsimp [q0, q1] <;> omega
    · constructor <;> dsimp [q0, q1] <;> omega

/-- The first contact has corridor position zero. -/
theorem endpointContactPosition_zero
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet)
    (havoid : C.AvoidsOutside P) :
    (C.endpointContactPosition P hsource htarget havoid
      ⟨0, by simp [endpointContactTraceLen]⟩).1 = 0 := by
  let hs := (C.endpoints_mem_linkage P hsource htarget).1
  let ht := (C.endpoints_mem_linkage P hsource htarget).2
  have hrow :=
    C.row_endpointContactPosition P hsource htarget havoid
      ⟨0, by simp [endpointContactTraceLen]⟩
  have hidx :
      endpointContactIndex L P hs ht
          ⟨0, by simp [endpointContactTraceLen]⟩ =
        C.index ⟨0, by omega⟩ := by
    exact endpointContactIndex_zero_eq_of_source_mem
      L P hs ht hsource
  have hpos :
      C.endpointContactPosition P hsource htarget havoid
          ⟨0, by simp [endpointContactTraceLen]⟩ =
        (⟨0, by omega⟩ : Fin (activeCount + 2)) := by
    apply C.index_injective
    have hrow' :
        C.index
            (C.endpointContactPosition P hsource htarget havoid
              ⟨0, by simp [endpointContactTraceLen]⟩) =
          endpointContactIndex L P hs ht
            ⟨0, by simp [endpointContactTraceLen]⟩ := by
      simpa [hs, ht] using hrow
    exact hrow'.trans hidx
  exact congrArg Fin.val hpos

/-- The last contact has the upper-boundary corridor position. -/
theorem endpointContactPosition_last
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet)
    (havoid : C.AvoidsOutside P) :
    (C.endpointContactPosition P hsource htarget havoid
      ⟨endpointContactTraceLen L P, by omega⟩).1 =
        activeCount + 1 := by
  let hs := (C.endpoints_mem_linkage P hsource htarget).1
  let ht := (C.endpoints_mem_linkage P hsource htarget).2
  have hrow :=
    C.row_endpointContactPosition P hsource htarget havoid
      ⟨endpointContactTraceLen L P, by omega⟩
  have hidx :
      endpointContactIndex L P hs ht
          ⟨endpointContactTraceLen L P, by omega⟩ =
        C.index ⟨activeCount + 1, by omega⟩ := by
    exact endpointContactIndex_last_eq_of_target_mem
      L P hs ht htarget
  have hpos :
      C.endpointContactPosition P hsource htarget havoid
          ⟨endpointContactTraceLen L P, by omega⟩ =
        (⟨activeCount + 1, by omega⟩ : Fin (activeCount + 2)) := by
    apply C.index_injective
    have hrow' :
        C.index
            (C.endpointContactPosition P hsource htarget havoid
              ⟨endpointContactTraceLen L P, by omega⟩) =
          endpointContactIndex L P hs ht
            ⟨endpointContactTraceLen L P, by omega⟩ := by
      simpa [hs, ht] using hrow
    exact hrow'.trans hidx
  exact congrArg Fin.val hpos

/-- Generic boundary-to-boundary no-skip theorem.  The only path hypotheses are
the two boundary endpoint contacts and avoidance of linkage paths outside the
ordered corridor.  In particular, contact with active rows is derived. -/
theorem path_hits_every_row
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G)
    (hsource : P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet)
    (htarget :
      P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet)
    (havoid : C.AvoidsOutside P) :
    ∀ q : Fin (activeCount + 2), HitsLinkagePath (L := L) P (C.index q) := by
  classical
  intro q
  let pos : Fin (endpointContactTraceLen L P + 1) → ℕ :=
    fun r => (C.endpointContactPosition P hsource htarget havoid r).1
  have hstep : UnitStepNatTrace (endpointContactTraceLen L P) pos := by
    simpa [pos] using
      C.endpointContactPosition_unitStep P hsource htarget havoid
  have hfirst : pos ⟨0, by omega⟩ ≤ q.1 := by
    change
      (C.endpointContactPosition P hsource htarget havoid
        ⟨0, by omega⟩).1 ≤ q.1
    rw [C.endpointContactPosition_zero P hsource htarget havoid]
    exact Nat.zero_le _
  have hlast :
      q.1 ≤ pos ⟨endpointContactTraceLen L P, by omega⟩ := by
    change q.1 ≤
      (C.endpointContactPosition P hsource htarget havoid
        ⟨endpointContactTraceLen L P, by omega⟩).1
    rw [C.endpointContactPosition_last P hsource htarget havoid]
    omega
  rcases UnitStepNatTrace.exists_eq_of_le hstep hfirst hlast with ⟨r, hr⟩
  let qr := C.endpointContactPosition P hsource htarget havoid r
  have hqr : qr = q := by
    apply Fin.ext
    simpa [pos, qr] using hr
  refine ⟨endpointContact L P r, Finset.mem_inter.2
    ⟨endpointContact_mem_path L P r, ?_⟩⟩
  have hcontact :=
    endpointContact_mem_contactIndex_path L P
      (C.endpoints_mem_linkage P hsource htarget).1
      (C.endpoints_mem_linkage P hsource htarget).2 r
  have hrow :=
    C.row_endpointContactPosition P hsource htarget havoid r
  rw [← hrow] at hcontact
  simpa [qr, hqr] using hcontact

end AuxiliaryCorridor

/-- A family of full, pairwise vertex-disjoint columns between the two
boundary rows of a corridor.

The singleton equalities retain the exact boundary endpoints and assert unique
boundary contact.  No active-row contact is stored: it follows from
`AuxiliaryCorridor.path_hits_every_row`. -/
structure FullBoundaryColumnFamily
    (L : PerfectPathPacking G A B) (activeCount : ℕ)
    (ι : Type w) (C : AuxiliaryCorridor L activeCount) where
  column : ι → GraphPath G
  pairwise_nodeDisjoint :
    Pairwise fun i j : ι => (column i).NodeDisjoint (column j)
  lower_contact :
    ∀ i : ι,
      (column i).vertexSet ∩
          (C.rowPath ⟨0, by omega⟩).vertexSet =
        {(column i).source}
  upper_contact :
    ∀ i : ι,
      (column i).vertexSet ∩
          (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet =
        {(column i).target}
  avoidsOutside : ∀ i : ι, C.AvoidsOutside (column i)

namespace FullBoundaryColumnFamily

variable {ι : Type w} {L : PerfectPathPacking G A B} {activeCount : ℕ}
variable {C : AuxiliaryCorridor L activeCount}

/-- The retained lower endpoint lies on the lower boundary row. -/
theorem source_mem_lower
    (F : FullBoundaryColumnFamily L activeCount ι C) (i : ι) :
    (F.column i).source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet := by
  have h :
      (F.column i).source ∈
        (F.column i).vertexSet ∩
          (C.rowPath ⟨0, by omega⟩).vertexSet := by
    rw [F.lower_contact i]
    simp
  exact (Finset.mem_inter.1 h).2

/-- The retained upper endpoint lies on the upper boundary row. -/
theorem target_mem_upper
    (F : FullBoundaryColumnFamily L activeCount ι C) (i : ι) :
    (F.column i).target ∈
      (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet := by
  have h :
      (F.column i).target ∈
        (F.column i).vertexSet ∩
          (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet := by
    rw [F.upper_contact i]
    simp
  exact (Finset.mem_inter.1 h).2

/-- Every stored full column meets every row of the corridor. -/
theorem column_hits_every_row
    (F : FullBoundaryColumnFamily L activeCount ι C) (i : ι)
    (q : Fin (activeCount + 2)) :
    HitsLinkagePath (L := L) (F.column i) (C.index q) :=
  C.path_hits_every_row (F.column i)
    (F.source_mem_lower i) (F.target_mem_upper i) (F.avoidsOutside i) q

/-- A replacement path with the same two retained boundary endpoints and the
same outside-avoidance property still meets every corridor row.  This is the
form used after cycle erasure in hill elimination. -/
theorem replacement_hits_every_row
    (F : FullBoundaryColumnFamily L activeCount ι C) (i : ι)
    (P : GraphPath G)
    (hsource : P.source = (F.column i).source)
    (htarget : P.target = (F.column i).target)
    (havoid : C.AvoidsOutside P)
    (q : Fin (activeCount + 2)) :
    HitsLinkagePath (L := L) P (C.index q) := by
  apply C.path_hits_every_row P
  · simpa [hsource] using F.source_mem_lower i
  · simpa [htarget] using F.target_mem_upper i
  · exact havoid

end FullBoundaryColumnFamily

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
