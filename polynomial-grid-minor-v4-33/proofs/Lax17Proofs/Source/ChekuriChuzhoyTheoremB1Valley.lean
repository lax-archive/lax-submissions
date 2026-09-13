import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1HillReplacement

namespace Lax17Proofs

universe u v w

/-!
# Appendix B.1: valleys in a full boundary-to-boundary column

This file formalizes the contact-trace part of Claim B.3 in the proof of
Chekuri--Chuzhoy Appendix B, Theorem B.1.  Columns are not trimmed: every
column remains a full path from the lower boundary row to the upper boundary
row.  Its endpoint-padded linkage-contact list therefore starts at row `0`,
ends at row `activeCount + 1`, and changes corridor position by at most one.

The definitions below deliberately distinguish:

* the automatic trace facts, which follow from the auxiliary degree-two
  corridor;
* the local no-bump assertion, which says that a consecutive same-row atom
  really follows that row; and
* the geometric blocker step in the paper's valley argument.

No connected-intersection or common-order conclusion is stored as input data.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

open IndexedAuxiliaryPrefix

namespace AuxiliaryCorridor

variable {L : PerfectPathPacking G A B} {activeCount : ℕ}

/-- The union of the vertex sets of all rows, including the two boundaries. -/
noncomputable def allRowVertexSet
    (C : AuxiliaryCorridor L activeCount) : Finset V :=
  Finset.univ.biUnion fun r : Fin (activeCount + 2) =>
    (C.rowPath r).vertexSet

/-- The union of the edge sets of all rows, including the two boundaries. -/
noncomputable def allRowEdgeSet
    (C : AuxiliaryCorridor L activeCount) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun r : Fin (activeCount + 2) =>
    (C.rowPath r).edgeSet

theorem rowPath_vertexSet_subset_allRowVertexSet
    (C : AuxiliaryCorridor L activeCount) (r : Fin (activeCount + 2)) :
    (C.rowPath r).vertexSet ⊆ C.allRowVertexSet := by
  classical
  intro v hv
  exact Finset.mem_biUnion.2 ⟨r, Finset.mem_univ _, hv⟩

theorem rowPath_edgeSet_subset_allRowEdgeSet
    (C : AuxiliaryCorridor L activeCount) (r : Fin (activeCount + 2)) :
    (C.rowPath r).edgeSet ⊆ C.allRowEdgeSet := by
  classical
  intro e he
  exact Finset.mem_biUnion.2 ⟨r, Finset.mem_univ _, he⟩

/-- Distinct corridor rows are vertex-disjoint because they are distinct
members of the linkage packing. -/
theorem rowPath_nodeDisjoint
    (C : AuxiliaryCorridor L activeCount)
    {r s : Fin (activeCount + 2)} (hrs : r ≠ s) :
    (C.rowPath r).NodeDisjoint (C.rowPath s) := by
  simpa [AuxiliaryCorridor.rowPath, GraphPath.NodeDisjoint] using
    L.toPathPacking.node_disjoint (C.index_ne_of_ne hrs)

end AuxiliaryCorridor

/-- The complete, endpoint-padded row-contact trace of one full column.

Only the primitive boundary and avoidance facts are fields.  Contacts,
corridor positions, completeness, and unit-step behavior are all derived. -/
structure CorridorColumnTrace
    (L : PerfectPathPacking G A B) (activeCount : ℕ)
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G) where
  source_mem_lower :
    P.source ∈ (C.rowPath ⟨0, by omega⟩).vertexSet
  target_mem_upper :
    P.target ∈ (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet
  avoidsOutside : C.AvoidsOutside P

namespace CorridorColumnTrace

variable {L : PerfectPathPacking G A B} {activeCount : ℕ}
variable {C : AuxiliaryCorridor L activeCount} {P : GraphPath G}

/-- Number of gaps in the endpoint-padded contact list. -/
noncomputable def len (_T : CorridorColumnTrace L activeCount C P) : ℕ :=
  endpointContactTraceLen L P

/-- The `r`-th contact of the full column with the linkage. -/
noncomputable def contact
    (T : CorridorColumnTrace L activeCount C P)
    (r : Fin (T.len + 1)) : V :=
  endpointContact L P r

/-- The corridor row containing the `r`-th contact. -/
noncomputable def row
    (T : CorridorColumnTrace L activeCount C P)
    (r : Fin (T.len + 1)) : Fin (activeCount + 2) :=
  C.endpointContactPosition P T.source_mem_lower T.target_mem_upper
    T.avoidsOutside r

theorem source_ne_target (T : CorridorColumnTrace L activeCount C P) :
    P.source ≠ P.target :=
  C.source_ne_target P T.source_mem_lower T.target_mem_upper

theorem endpoints_mem_linkage
    (T : CorridorColumnTrace L activeCount C P) :
    P.source ∈ L.toPathPacking.vertexSet ∧
      P.target ∈ L.toPathPacking.vertexSet :=
  C.endpoints_mem_linkage P T.source_mem_lower T.target_mem_upper

theorem contact_mem_column
    (T : CorridorColumnTrace L activeCount C P)
    (r : Fin (T.len + 1)) :
    T.contact r ∈ P.vertexSet := by
  exact endpointContact_mem_path L P r

theorem contact_mem_row
    (T : CorridorColumnTrace L activeCount C P)
    (r : Fin (T.len + 1)) :
    T.contact r ∈ (C.rowPath (T.row r)).vertexSet := by
  have hmem :=
    endpointContact_mem_contactIndex_path L P
      T.endpoints_mem_linkage.1 T.endpoints_mem_linkage.2 r
  have hrow :=
    C.row_endpointContactPosition P T.source_mem_lower T.target_mem_upper
      T.avoidsOutside r
  rw [← hrow] at hmem
  exact hmem

/-- Every column vertex on a corridor row occurs in the complete contact
trace. -/
theorem contact_complete
    (T : CorridorColumnTrace L activeCount C P)
    {v : V} (hvP : v ∈ P.vertexSet)
    {q : Fin (activeCount + 2)}
    (hvrow : v ∈ (C.rowPath q).vertexSet) :
    ∃ r : Fin (T.len + 1), T.contact r = v := by
  have hvL : v ∈ L.toPathPacking.vertexSet := by
    exact (L.toPathPacking.mem_vertexSet).2 ⟨C.index q, hvrow⟩
  have hvlist :=
    mem_endpointContactVertexList_of_mem_path_of_mem_linkage L P hvP hvL
  rcases List.mem_iff_get.mp hvlist with ⟨r, hr⟩
  refine ⟨⟨r.1, by
    simpa [CorridorColumnTrace.len, endpointContactTraceLen_add_one] using
      r.2⟩, ?_⟩
  simpa [CorridorColumnTrace.contact, endpointContact] using hr

/-- A contact cannot lie on a second corridor row. -/
theorem contact_row_unique
    (T : CorridorColumnTrace L activeCount C P)
    (r : Fin (T.len + 1)) (q : Fin (activeCount + 2))
    (hmem : T.contact r ∈ (C.rowPath q).vertexSet) :
    q = T.row r := by
  by_contra hne
  exact Finset.disjoint_left.mp (C.rowPath_nodeDisjoint hne)
    hmem (T.contact_mem_row r)

theorem contact_before_iff_le
    (T : CorridorColumnTrace L activeCount C P)
    (r s : Fin (T.len + 1)) :
    P.Before (T.contact r) (T.contact s) ↔ r.1 ≤ s.1 := by
  exact endpointContact_before_iff_le_of_source_ne_target L P
    T.source_ne_target r s

theorem contact_injective
    (T : CorridorColumnTrace L activeCount C P) :
    Function.Injective T.contact := by
  intro r s hrs
  have hrsBefore : P.Before (T.contact r) (T.contact s) := by
    rw [hrs]
    exact P.before_refl (T.contact_mem_column s)
  have hsrBefore : P.Before (T.contact s) (T.contact r) := by
    rw [hrs]
    exact P.before_refl (T.contact_mem_column s)
  apply Fin.ext
  have hrsLe := (T.contact_before_iff_le r s).1 hrsBefore
  have hsrLe := (T.contact_before_iff_le s r).1 hsrBefore
  omega

/-- The atom between two consecutive contacts. -/
noncomputable def atom
    (T : CorridorColumnTrace L activeCount C P) (r : Fin T.len) :
    GraphPath G :=
  P.segmentOfBefore
    ((T.contact_before_iff_le
      ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self T.len)⟩
      ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).2 (Nat.le_succ r.1))

@[simp] theorem atom_source
    (T : CorridorColumnTrace L activeCount C P) (r : Fin T.len) :
    (T.atom r).source = T.contact ⟨r.1, by omega⟩ := by
  simp [atom]

@[simp] theorem atom_target
    (T : CorridorColumnTrace L activeCount C P) (r : Fin T.len) :
    (T.atom r).target = T.contact ⟨r.1 + 1, by omega⟩ := by
  simp [atom]

theorem atom_vertexSet_subset_column
    (T : CorridorColumnTrace L activeCount C P) (r : Fin T.len) :
    (T.atom r).vertexSet ⊆ P.vertexSet := by
  exact P.segmentOfBefore_vertexSet_subset
    ((T.contact_before_iff_le
      ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self T.len)⟩
      ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).2 (Nat.le_succ r.1))

theorem atom_edgeSet_subset_column
    (T : CorridorColumnTrace L activeCount C P) (r : Fin T.len) :
    (T.atom r).edgeSet ⊆ P.edgeSet := by
  exact P.segmentOfBefore_edgeSet_subset
    ((T.contact_before_iff_le
      ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self T.len)⟩
      ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).2 (Nat.le_succ r.1))

/-- A contact atom has no linkage vertex in its interior, hence no corridor
row vertex in its interior. -/
theorem atom_internallyDisjoint_linkage
    (T : CorridorColumnTrace L activeCount C P) (r : Fin T.len) :
    (T.atom r).InternallyDisjointFromSet L.toPathPacking.vertexSet := by
  simpa [atom] using
    endpointContactsCleanConsecutive_of_source_ne_target
      L P T.source_ne_target r

theorem atom_internallyDisjoint_rows
    (T : CorridorColumnTrace L activeCount C P) (r : Fin T.len) :
    (T.atom r).InternallyDisjointFromSet C.allRowVertexSet := by
  intro v hv hrows
  rw [AuxiliaryCorridor.allRowVertexSet, Finset.mem_biUnion] at hrows
  rcases hrows with ⟨q, _hq, hvq⟩
  exact T.atom_internallyDisjoint_linkage r hv
    ((L.toPathPacking.mem_vertexSet).2 ⟨C.index q, hvq⟩)

/-- Consecutive contacts stay on one row or move to an adjacent corridor row.
In particular, every off-row bridge joins consecutive rows. -/
theorem row_eq_or_consecutive
    (T : CorridorColumnTrace L activeCount C P) (r : Fin T.len) :
    T.row ⟨r.1, by omega⟩ = T.row ⟨r.1 + 1, by omega⟩ ∨
      FinConsecutive
        (T.row ⟨r.1, by omega⟩)
        (T.row ⟨r.1 + 1, by omega⟩) := by
  let q0 := T.row ⟨r.1, by omega⟩
  let q1 := T.row ⟨r.1 + 1, by omega⟩
  have haux :
      C.index q0 = C.index q1 ∨
        (linkageAuxGraph L).Adj (C.index q0) (C.index q1) := by
    exact aux_adj_or_eq_of_clean_segment
      (L := L) (T.atom r)
      (by
        simpa [q0, atom] using T.contact_mem_row ⟨r.1, by omega⟩)
      (by
        simpa [q1, atom] using T.contact_mem_row ⟨r.1 + 1, by omega⟩)
      (T.atom_internallyDisjoint_linkage r)
  rcases haux with heq | hadj
  · exact Or.inl (C.index_injective heq)
  · exact Or.inr (C.adj_iff_consecutive.mp hadj)

theorem unitStep
    (T : CorridorColumnTrace L activeCount C P) :
    UnitStepNatTrace T.len (fun r => (T.row r).1) := by
  simpa [CorridorColumnTrace.len, CorridorColumnTrace.row] using
    C.endpointContactPosition_unitStep P T.source_mem_lower
      T.target_mem_upper T.avoidsOutside

theorem row_zero
    (T : CorridorColumnTrace L activeCount C P) :
    (T.row ⟨0, by omega⟩).1 = 0 := by
  simpa [CorridorColumnTrace.len, CorridorColumnTrace.row] using
    C.endpointContactPosition_zero P T.source_mem_lower
      T.target_mem_upper T.avoidsOutside

theorem row_last
    (T : CorridorColumnTrace L activeCount C P) :
    (T.row ⟨T.len, by omega⟩).1 = activeCount + 1 := by
  simpa [CorridorColumnTrace.len, CorridorColumnTrace.row] using
    C.endpointContactPosition_last P T.source_mem_lower
      T.target_mem_upper T.avoidsOutside

theorem row_zero_eq
    (T : CorridorColumnTrace L activeCount C P) :
    T.row ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  apply Fin.ext
  exact T.row_zero

theorem row_last_eq
    (T : CorridorColumnTrace L activeCount C P) :
    T.row ⟨T.len, by omega⟩ =
      ⟨activeCount + 1, by omega⟩ := by
  apply Fin.ext
  exact T.row_last

/-- A concrete bump atom: two consecutive linkage contacts lie on the same
row, but the intervening column atom uses an edge outside that row.  Its
interior is automatically row-free by
`atom_internallyDisjoint_rows`, so this is exactly the local configuration
removed in the bump phase. -/
structure Bump (T : CorridorColumnTrace L activeCount C P) where
  step : Fin T.len
  same_row :
    T.row ⟨step.1, by omega⟩ =
      T.row ⟨step.1 + 1, by omega⟩
  off_row_edge : Sym2 V
  off_row_edge_mem : off_row_edge ∈ (T.atom step).edgeSet
  off_row_edge_not_mem :
    off_row_edge ∉
      (C.rowPath (T.row ⟨step.1, by omega⟩)).edgeSet

/-- There is no remaining bump atom. -/
def NoBump (T : CorridorColumnTrace L activeCount C P) : Prop :=
  ¬ Nonempty T.Bump

/-- Bumps on active rows have been eliminated.  Boundary-row bumps are
excluded separately by uniqueness of the stored boundary contact. -/
def NoActiveBump (T : CorridorColumnTrace L activeCount C P) : Prop :=
  ∀ D : T.Bump,
    0 < (T.row ⟨D.step.1, by omega⟩).1 →
    (T.row ⟨D.step.1, by omega⟩).1 < activeCount + 1 →
    False

theorem atom_edgeSet_subset_row_of_noBump
    (T : CorridorColumnTrace L activeCount C P)
    (hno : T.NoBump) (r : Fin T.len)
    (hsame :
      T.row ⟨r.1, by omega⟩ =
        T.row ⟨r.1 + 1, by omega⟩) :
    (T.atom r).edgeSet ⊆
      (C.rowPath (T.row ⟨r.1, by omega⟩)).edgeSet := by
  intro e he
  by_contra hnot
  exact hno ⟨{
    step := r
    same_row := hsame
    off_row_edge := e
    off_row_edge_mem := he
    off_row_edge_not_mem := hnot
  }⟩

/-- After bump elimination, a consecutive same-row atom is wholly contained
in that row, not merely endpoint-supported there. -/
theorem atom_vertexSet_subset_row_of_noBump
    (T : CorridorColumnTrace L activeCount C P)
    (hno : T.NoBump) (r : Fin T.len)
    (hsame :
      T.row ⟨r.1, by omega⟩ =
        T.row ⟨r.1 + 1, by omega⟩) :
    (T.atom r).vertexSet ⊆
      (C.rowPath (T.row ⟨r.1, by omega⟩)).vertexSet := by
  classical
  let base : Fin (activeCount + 2) := T.row ⟨r.1, by omega⟩
  apply graphPath_vertexSet_subset_row_of_edgeSet_subset_pairwiseUnion
    C.rowPath
    (by
      intro i j hij
      exact C.rowPath_nodeDisjoint hij)
    base (T.atom r)
  · simpa [base] using T.contact_mem_row ⟨r.1, by omega⟩
  · intro e he
    exact Finset.mem_biUnion.2
      ⟨base, Finset.mem_univ _, by
        simpa [base] using
          T.atom_edgeSet_subset_row_of_noBump hno r hsame he⟩

/-- Weakly increasing row positions along the full-column trace. -/
def MonotoneRows (T : CorridorColumnTrace L activeCount C P) : Prop :=
  ∀ r s : Fin (T.len + 1), r.1 ≤ s.1 → (T.row r).1 ≤ (T.row s).1

/-- Successor inequalities imply monotonicity on a finite index interval. -/
theorem nat_trace_monotone_on_of_le_succ
    {n : ℕ} {f : Fin (n + 1) → ℕ} {lo hi : ℕ}
    (hstep :
      ∀ r : Fin n, lo ≤ r.1 → r.1 + 1 ≤ hi →
        f ⟨r.1, by omega⟩ ≤ f ⟨r.1 + 1, by omega⟩)
    {a b : Fin (n + 1)}
    (hlo_a : lo ≤ a.1) (hab : a.1 ≤ b.1) (hb_hi : b.1 ≤ hi) :
    f a ≤ f b := by
  classical
  let d : ℕ := b.1 - a.1
  have hbEq : a.1 + d = b.1 := by
    dsimp [d]
    omega
  have H : ∀ m : ℕ, m ≤ d → ∀ hidx : a.1 + m < n + 1,
      f a ≤ f ⟨a.1 + m, hidx⟩ := by
    intro m hm
    induction m with
    | zero =>
        intro hidx
        simp
    | succ m ih =>
        intro hidxSucc
        have hmLe : m ≤ d := by omega
        have hidxPrev : a.1 + m < n + 1 := by omega
        have haPrev : f a ≤ f ⟨a.1 + m, hidxPrev⟩ :=
          ih hmLe hidxPrev
        have hidxStep : a.1 + m < n := by omega
        have hprevNext :
            f ⟨a.1 + m, hidxPrev⟩ ≤
              f ⟨(a.1 + m) + 1, by omega⟩ := by
          have hlo : lo ≤ a.1 + m := by
            exact le_trans hlo_a (Nat.le_add_right a.1 m)
          have htoB : (a.1 + m) + 1 ≤ b.1 := by
            rw [← hbEq]
            omega
          have hhi : (a.1 + m) + 1 ≤ hi :=
            le_trans htoB hb_hi
          exact hstep ⟨a.1 + m, hidxStep⟩ hlo hhi
        have hnext :
            f ⟨a.1 + (m + 1), hidxSucc⟩ =
              f ⟨(a.1 + m) + 1, by omega⟩ := by
          congr 2
        rw [hnext]
        exact le_trans haPrev hprevNext
  have hfin :
      (⟨a.1 + d, by omega⟩ : Fin (n + 1)) = b :=
    Fin.ext hbEq
  simpa [hfin] using H d le_rfl (by omega)

/-- A compressed valley in the row-contact trace.  Between its two contacts
on `rowTop`, every other row contact is on the immediately lower row.  Equal
row stutters are therefore absorbed into the interval. -/
structure Valley (T : CorridorColumnTrace L activeCount C P) where
  left : Fin (T.len + 1)
  right : Fin (T.len + 1)
  rowTop : Fin (activeCount + 2)
  rowLower : Fin (activeCount + 2)
  left_lt_right : left.1 < right.1
  left_row : T.row left = rowTop
  right_row : T.row right = rowTop
  lower_succ : rowLower.1 + 1 = rowTop.1
  hit_lower :
    ∃ mid : Fin (T.len + 1),
      left.1 ≤ mid.1 ∧ mid.1 ≤ right.1 ∧ T.row mid = rowLower
  contacts_only_lower_or_endpoints :
    ∀ r : Fin (T.len + 1),
      left.1 ≤ r.1 → r.1 ≤ right.1 →
        T.row r ≠ rowLower → r = left ∨ r = right

namespace Valley

variable {T : CorridorColumnTrace L activeCount C P}

theorem top_ne_lower (D : T.Valley) : D.rowTop ≠ D.rowLower := by
  intro h
  have hs := D.lower_succ
  rw [h] at hs
  omega

theorem hit_lower_strict (D : T.Valley) :
    ∃ mid : Fin (T.len + 1),
      D.left.1 < mid.1 ∧ mid.1 < D.right.1 ∧
        T.row mid = D.rowLower := by
  rcases D.hit_lower with ⟨mid, hl, hr, hm⟩
  have hneLeft : mid ≠ D.left := by
    intro h
    apply D.top_ne_lower
    calc
      D.rowTop = T.row D.left := D.left_row.symm
      _ = T.row mid := by rw [h]
      _ = D.rowLower := hm
  have hneRight : mid ≠ D.right := by
    intro h
    apply D.top_ne_lower
    calc
      D.rowTop = T.row D.right := D.right_row.symm
      _ = T.row mid := by rw [h]
      _ = D.rowLower := hm
  exact ⟨mid, by omega, by omega, hm⟩

/-- The portion of the full column between the two top-row contacts. -/
noncomputable def columnSegment (D : T.Valley) : GraphPath G :=
  P.segmentOfBefore
    ((T.contact_before_iff_le D.left D.right).2
      (Nat.le_of_lt D.left_lt_right))

theorem columnSegment_vertexSet_subset_column (D : T.Valley) :
    D.columnSegment.vertexSet ⊆ P.vertexSet := by
  exact P.segmentOfBefore_vertexSet_subset
    ((T.contact_before_iff_le D.left D.right).2
      (Nat.le_of_lt D.left_lt_right))

theorem columnSegment_edgeSet_subset_column (D : T.Valley) :
    D.columnSegment.edgeSet ⊆ P.edgeSet := by
  exact P.segmentOfBefore_edgeSet_subset
    ((T.contact_before_iff_le D.left D.right).2
      (Nat.le_of_lt D.left_lt_right))

@[simp] theorem columnSegment_source (D : T.Valley) :
    D.columnSegment.source = T.contact D.left := by
  simp [columnSegment]

@[simp] theorem columnSegment_target (D : T.Valley) :
    D.columnSegment.target = T.contact D.right := by
  simp [columnSegment]

theorem left_mem_top (D : T.Valley) :
    T.contact D.left ∈ (C.rowPath D.rowTop).vertexSet := by
  simpa [D.left_row] using T.contact_mem_row D.left

theorem right_mem_top (D : T.Valley) :
    T.contact D.right ∈ (C.rowPath D.rowTop).vertexSet := by
  simpa [D.right_row] using T.contact_mem_row D.right

theorem top_contacts_order (D : T.Valley) :
    (C.rowPath D.rowTop).Before
        (T.contact D.left) (T.contact D.right) ∨
      (C.rowPath D.rowTop).Before
        (T.contact D.right) (T.contact D.left) :=
  ClaimB2Atom.graphPath_before_or_before_of_mem
    (C.rowPath D.rowTop) D.left_mem_top D.right_mem_top

/-- The row interval whose occupation by another column blocks this valley
from being a hill.  It is oriented according to the row path. -/
noncomputable def rowInterval (D : T.Valley) : GraphPath G := by
  classical
  by_cases h :
      (C.rowPath D.rowTop).Before
        (T.contact D.left) (T.contact D.right)
  · exact (C.rowPath D.rowTop).segmentOfBefore h
  · exact (C.rowPath D.rowTop).segmentOfBefore
      (D.top_contacts_order.resolve_left h)

theorem rowInterval_vertexSet_subset_top (D : T.Valley) :
    D.rowInterval.vertexSet ⊆ (C.rowPath D.rowTop).vertexSet := by
  classical
  dsimp [rowInterval]
  split
  · apply (C.rowPath D.rowTop).segmentOfBefore_vertexSet_subset
  · apply (C.rowPath D.rowTop).segmentOfBefore_vertexSet_subset

theorem left_mem_rowInterval (D : T.Valley) :
    T.contact D.left ∈ D.rowInterval.vertexSet := by
  classical
  by_cases h :
      (C.rowPath D.rowTop).Before
        (T.contact D.left) (T.contact D.right)
  · simpa [rowInterval, h] using GraphPath.source_mem_vertexSet
      ((C.rowPath D.rowTop).segmentOfBefore h)
  · let hr :
        (C.rowPath D.rowTop).Before
          (T.contact D.right) (T.contact D.left) :=
      D.top_contacts_order.resolve_left h
    simpa [rowInterval, h, hr] using GraphPath.target_mem_vertexSet
      ((C.rowPath D.rowTop).segmentOfBefore hr)

theorem right_mem_rowInterval (D : T.Valley) :
    T.contact D.right ∈ D.rowInterval.vertexSet := by
  classical
  by_cases h :
      (C.rowPath D.rowTop).Before
        (T.contact D.left) (T.contact D.right)
  · simpa [rowInterval, h] using GraphPath.target_mem_vertexSet
      ((C.rowPath D.rowTop).segmentOfBefore h)
  · let hr :
        (C.rowPath D.rowTop).Before
          (T.contact D.right) (T.contact D.left) :=
      D.top_contacts_order.resolve_left h
    simpa [rowInterval, h, hr] using GraphPath.source_mem_vertexSet
      ((C.rowPath D.rowTop).segmentOfBefore hr)

/-- Membership in the hill-row interval is exactly numerical betweenness
between its two endpoint contacts, allowing either row orientation. -/
theorem rowInterval_vertexIndex_between
    (D : T.Valley) {x : V} (hx : x ∈ D.rowInterval.vertexSet) :
    ((C.rowPath D.rowTop).vertexIndex (T.contact D.left) ≤
        (C.rowPath D.rowTop).vertexIndex x ∧
      (C.rowPath D.rowTop).vertexIndex x ≤
        (C.rowPath D.rowTop).vertexIndex (T.contact D.right)) ∨
    ((C.rowPath D.rowTop).vertexIndex (T.contact D.right) ≤
        (C.rowPath D.rowTop).vertexIndex x ∧
      (C.rowPath D.rowTop).vertexIndex x ≤
        (C.rowPath D.rowTop).vertexIndex (T.contact D.left)) := by
  classical
  by_cases h :
      (C.rowPath D.rowTop).Before
        (T.contact D.left) (T.contact D.right)
  · left
    have hl :=
      (C.rowPath D.rowTop).before_of_mem_segmentOfBefore_left h
        (by simpa [rowInterval, h] using hx)
    have hr :=
      (C.rowPath D.rowTop).before_of_mem_segmentOfBefore_right h
        (by simpa [rowInterval, h] using hx)
    exact
      ⟨((C.rowPath D.rowTop).before_iff_vertexIndex_le).1 hl |>.2.2,
       ((C.rowPath D.rowTop).before_iff_vertexIndex_le).1 hr |>.2.2⟩
  · right
    let hr :
        (C.rowPath D.rowTop).Before
          (T.contact D.right) (T.contact D.left) :=
      D.top_contacts_order.resolve_left h
    have hl :=
      (C.rowPath D.rowTop).before_of_mem_segmentOfBefore_left hr
        (by simpa [rowInterval, h, hr] using hx)
    have hright :=
      (C.rowPath D.rowTop).before_of_mem_segmentOfBefore_right hr
        (by simpa [rowInterval, h, hr] using hx)
    exact
      ⟨((C.rowPath D.rowTop).before_iff_vertexIndex_le).1 hl |>.2.2,
       ((C.rowPath D.rowTop).before_iff_vertexIndex_le).1 hright |>.2.2⟩

theorem mem_rowInterval_of_vertexIndex_between
    (D : T.Valley) {x : V}
    (hxRow : x ∈ (C.rowPath D.rowTop).vertexSet)
    (hbetween :
      ((C.rowPath D.rowTop).vertexIndex (T.contact D.left) ≤
          (C.rowPath D.rowTop).vertexIndex x ∧
        (C.rowPath D.rowTop).vertexIndex x ≤
          (C.rowPath D.rowTop).vertexIndex (T.contact D.right)) ∨
      ((C.rowPath D.rowTop).vertexIndex (T.contact D.right) ≤
          (C.rowPath D.rowTop).vertexIndex x ∧
        (C.rowPath D.rowTop).vertexIndex x ≤
          (C.rowPath D.rowTop).vertexIndex (T.contact D.left))) :
    x ∈ D.rowInterval.vertexSet := by
  classical
  by_cases h :
      (C.rowPath D.rowTop).Before
        (T.contact D.left) (T.contact D.right)
  · have hlr :=
      ((C.rowPath D.rowTop).before_iff_vertexIndex_le).1 h |>.2.2
    have hidx :
        (C.rowPath D.rowTop).vertexIndex (T.contact D.left) ≤
            (C.rowPath D.rowTop).vertexIndex x ∧
          (C.rowPath D.rowTop).vertexIndex x ≤
            (C.rowPath D.rowTop).vertexIndex (T.contact D.right) := by
      rcases hbetween with hb | hb <;> omega
    have hl :
        (C.rowPath D.rowTop).Before (T.contact D.left) x :=
      ((C.rowPath D.rowTop).before_iff_vertexIndex_le).2
        ⟨D.left_mem_top, hxRow, hidx.1⟩
    have hr :
        (C.rowPath D.rowTop).Before x (T.contact D.right) :=
      ((C.rowPath D.rowTop).before_iff_vertexIndex_le).2
        ⟨hxRow, D.right_mem_top, hidx.2⟩
    simpa [rowInterval, h] using
      (C.rowPath D.rowTop).mem_segmentOfBefore_of_before_of_before h hl hr
  · let hr :
        (C.rowPath D.rowTop).Before
          (T.contact D.right) (T.contact D.left) :=
      D.top_contacts_order.resolve_left h
    have hrl :=
      ((C.rowPath D.rowTop).before_iff_vertexIndex_le).1 hr |>.2.2
    have hidx :
        (C.rowPath D.rowTop).vertexIndex (T.contact D.right) ≤
            (C.rowPath D.rowTop).vertexIndex x ∧
          (C.rowPath D.rowTop).vertexIndex x ≤
            (C.rowPath D.rowTop).vertexIndex (T.contact D.left) := by
      rcases hbetween with hb | hb <;> omega
    have hl :
        (C.rowPath D.rowTop).Before (T.contact D.right) x :=
      ((C.rowPath D.rowTop).before_iff_vertexIndex_le).2
        ⟨D.right_mem_top, hxRow, hidx.1⟩
    have hright :
        (C.rowPath D.rowTop).Before x (T.contact D.left) :=
      ((C.rowPath D.rowTop).before_iff_vertexIndex_le).2
        ⟨hxRow, D.left_mem_top, hidx.2⟩
    simpa [rowInterval, h, hr] using
      (C.rowPath D.rowTop).mem_segmentOfBefore_of_before_of_before
        hr hl hright

theorem left_lt_len (D : T.Valley) : D.left.1 < T.len := by
  have hr := D.right.2
  have hlr := D.left_lt_right
  omega

theorem right_pos (D : T.Valley) : 0 < D.right.1 := by
  have hlr := D.left_lt_right
  omega

theorem left_succ_row (D : T.Valley) :
    T.row ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩ =
      D.rowLower := by
  by_contra hnot
  let nxt : Fin (T.len + 1) :=
    ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩
  rcases D.contacts_only_lower_or_endpoints
      nxt (by simp [nxt]) (by
        rcases D.hit_lower_strict with ⟨mid, hl, hr, _⟩
        simp [nxt]
        omega) hnot with h | h
  · have := congrArg Fin.val h
    simp [nxt] at this
  · rcases D.hit_lower_strict with ⟨mid, hl, hr, _⟩
    have := congrArg Fin.val h
    simp [nxt] at this
    omega

theorem right_pred_row (D : T.Valley) :
    T.row ⟨D.right.1 - 1,
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩ = D.rowLower := by
  by_contra hnot
  let pred : Fin (T.len + 1) :=
    ⟨D.right.1 - 1,
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩
  rcases D.contacts_only_lower_or_endpoints
      pred (by
        rcases D.hit_lower_strict with ⟨mid, hl, hr, _⟩
        simp [pred]
        omega) (by simp [pred]) hnot with h | h
  · rcases D.hit_lower_strict with ⟨mid, hl, hr, _⟩
    have := congrArg Fin.val h
    simp [pred] at this
    omega
  · have := congrArg Fin.val h
    simp [pred] at this
    have hp := D.right_pos
    omega

theorem left_succ_le_right_pred (D : T.Valley) :
    D.left.1 + 1 ≤ D.right.1 - 1 := by
  rcases D.hit_lower_strict with ⟨mid, hl, hr, _⟩
  omega

theorem row_eq_lower_of_internal
    (D : T.Valley) (r : Fin (T.len + 1))
    (hleft : D.left.1 + 1 ≤ r.1)
    (hright : r.1 ≤ D.right.1 - 1) :
    T.row r = D.rowLower := by
  by_contra hnot
  rcases D.contacts_only_lower_or_endpoints r
      (by omega) (by omega) hnot with h | h
  · have hv := congrArg Fin.val h
    omega
  · have hv := congrArg Fin.val h
    have hp := D.right_pos
    omega

end Valley

/-- A downward unit step in a full boundary-to-boundary trace produces a
valley.  We choose the last downward step.  The trace is weakly increasing
after it; its first subsequent return to the upper level therefore has only
the lower level in between. -/
theorem valley_of_down_step
    (T : CorridorColumnTrace L activeCount C P)
    (hex :
      ∃ r : Fin T.len,
        (T.row ⟨r.1 + 1, by omega⟩).1 + 1 =
          (T.row ⟨r.1, by omega⟩).1) :
    Nonempty T.Valley := by
  classical
  let f : Fin (T.len + 1) → ℕ := fun r => (T.row r).1
  let Down : ℕ → Prop := fun n =>
    ∃ hn : n < T.len,
      f ⟨n + 1, Nat.succ_lt_succ hn⟩ + 1 =
        f ⟨n, Nat.lt_trans hn (Nat.lt_succ_self T.len)⟩
  have hexDown : ∃ n, Down n := by
    rcases hex with ⟨r, hr⟩
    exact ⟨r.1, r.2, by simpa [f] using hr⟩
  let k : ℕ := Nat.findGreatest Down T.len
  have hkDown : Down k := by
    rcases hexDown with ⟨m, hm⟩
    rcases hm with ⟨hmLen, hmStep⟩
    exact Nat.findGreatest_spec
      (P := Down) (m := m) (n := T.len) (by omega)
      ⟨hmLen, hmStep⟩
  rcases hkDown with ⟨hkLen, hkStep⟩
  let left : Fin (T.len + 1) :=
    ⟨k, Nat.lt_trans hkLen (Nat.lt_succ_self T.len)⟩
  let mid : Fin (T.len + 1) := ⟨k + 1, Nat.succ_lt_succ hkLen⟩
  let lower : ℕ := f mid
  let top : ℕ := f left
  have htop : lower + 1 = top := by
    simpa [left, mid, lower, top] using hkStep
  have htopLeLast :
      top ≤ f ⟨T.len, by omega⟩ := by
    have htopBound : top ≤ activeCount + 1 := by
      have hlt := (T.row left).2
      dsimp [top, f]
      omega
    simpa [f, T.row_last] using htopBound
  let Rise : ℕ → Prop := fun m =>
    ∃ hm : m ≤ T.len,
      k + 1 ≤ m ∧ top ≤ f ⟨m, by omega⟩
  have hexRise : ∃ m, Rise m := by
    exact ⟨T.len, le_rfl, by omega, htopLeLast⟩
  let t : ℕ := Nat.find hexRise
  have htRise : Rise t := Nat.find_spec hexRise
  rcases htRise with ⟨htLe, hkOneLe, htTop⟩
  have hkOneLt : k + 1 < t := by
    by_contra hnot
    have hEq : t = k + 1 := by omega
    have hle : top ≤ lower := by
      simpa [hEq, mid, lower] using htTop
    omega
  have htPos : 0 < t := by omega
  let pred : Fin T.len := ⟨t - 1, by omega⟩
  have hpredSucc : pred.1 + 1 = t := by
    simp [pred]
    omega
  have hpredGe : k + 1 ≤ pred.1 := by
    simp [pred]
    omega
  have hpredNotRise : ¬ Rise pred.1 := by
    have hpredLt : pred.1 < t := by
      dsimp [pred]
      omega
    exact Nat.find_min hexRise hpredLt
  have hpredLtTop :
      f ⟨pred.1, by omega⟩ < top := by
    have hpredLeLen : pred.1 ≤ T.len := by omega
    have hnotTop : ¬ top ≤ f ⟨pred.1, by omega⟩ := by
      intro h
      exact hpredNotRise ⟨hpredLeLen, hpredGe, h⟩
    omega
  have htLeTop :
      f ⟨t, by omega⟩ ≤ top := by
    have hstep := T.unitStep pred
    have hle :
        f ⟨pred.1 + 1, by omega⟩ ≤
          f ⟨pred.1, by omega⟩ + 1 := hstep.1
    simpa [hpredSucc] using (show
      f ⟨pred.1 + 1, by omega⟩ ≤ top by omega)
  have htEqTop : f ⟨t, by omega⟩ = top :=
    le_antisymm htLeTop htTop
  have hnoDownAfter :
      ∀ r : Fin T.len, k + 1 ≤ r.1 → r.1 + 1 ≤ t →
        f ⟨r.1, by omega⟩ ≤ f ⟨r.1 + 1, by omega⟩ := by
    intro r hkr hrt
    have hklt : k < r.1 := by omega
    have hrle : r.1 ≤ T.len := by omega
    have hnotDown : ¬ Down r.1 := by
      simpa [k] using
        (Nat.findGreatest_is_greatest
          (P := Down) (n := T.len) (k := r.1) hklt hrle)
    have hunit := T.unitStep r
    change
      f ⟨r.1 + 1, by omega⟩ ≤ f ⟨r.1, by omega⟩ + 1 ∧
        f ⟨r.1, by omega⟩ ≤ f ⟨r.1 + 1, by omega⟩ + 1 at hunit
    by_contra hnotLe
    have heq :
        f ⟨r.1 + 1, by omega⟩ + 1 =
          f ⟨r.1, by omega⟩ := by
      omega
    exact hnotDown ⟨r.2, heq⟩
  let right : Fin (T.len + 1) := ⟨t, by omega⟩
  refine ⟨{
    left := left
    right := right
    rowTop := T.row left
    rowLower := T.row mid
    left_lt_right := by simp [left, right]; omega
    left_row := rfl
    right_row := ?_
    lower_succ := ?_
    hit_lower := ?_
    contacts_only_lower_or_endpoints := ?_
  }⟩
  · apply Fin.ext
    simpa [f, top, left, right] using htEqTop
  · simpa [f, lower, top, mid, left] using htop
  · exact ⟨mid, by simp [left, mid], by simp [mid, right]; omega, rfl⟩
  · intro q hlq hqr hqNotLower
    by_cases hqLeft : q = left
    · exact Or.inl hqLeft
    by_cases hqRight : q = right
    · exact Or.inr hqRight
    have hqGe : k + 1 ≤ q.1 := by
      dsimp [left] at hlq
      have hkltq : k < q.1 := Nat.lt_of_le_of_ne hlq (by
        intro h
        exact hqLeft (Fin.ext h.symm))
      omega
    have hqLt : q.1 < t := by
      dsimp [right] at hqr
      exact Nat.lt_of_le_of_ne hqr (by
        intro h
        exact hqRight (Fin.ext h))
    have hlowerLe :
        lower ≤ f q := by
      have hmono :=
        nat_trace_monotone_on_of_le_succ
          (f := f) (lo := k + 1) (hi := t)
          (by
            intro r hlo hhi
            exact hnoDownAfter r hlo hhi)
          (a := mid) (b := q) (by simp [mid]) (by simp [mid]; omega)
          (by omega)
      simpa [lower, mid] using hmono
    have hqNotRise : ¬ Rise q.1 :=
      Nat.find_min hexRise hqLt
    have hqLtTop : f q < top := by
      have hqLeLen : q.1 ≤ T.len := by omega
      have hnot : ¬ top ≤ f q := by
        intro h
        exact hqNotRise ⟨hqLeLen, hqGe, by simpa using h⟩
      omega
    have hqEqLower : f q = lower := by omega
    exfalso
    apply hqNotLower
    apply Fin.ext
    simpa [f, lower, mid] using hqEqLower

/-- Absence of valleys forces the full row trace to be weakly increasing. -/
theorem monotoneRows_of_noValley
    (T : CorridorColumnTrace L activeCount C P)
    (hnoValley : ¬ Nonempty T.Valley) :
    T.MonotoneRows := by
  have hsucc :
      ∀ r : Fin T.len,
        (T.row ⟨r.1, by omega⟩).1 ≤
          (T.row ⟨r.1 + 1, by omega⟩).1 := by
    intro r
    by_contra hnot
    have hdown :
        (T.row ⟨r.1 + 1, by omega⟩).1 + 1 =
          (T.row ⟨r.1, by omega⟩).1 := by
      have hunit := T.unitStep r
      change
        (T.row ⟨r.1 + 1, by omega⟩).1 ≤
              (T.row ⟨r.1, by omega⟩).1 + 1 ∧
          (T.row ⟨r.1, by omega⟩).1 ≤
              (T.row ⟨r.1 + 1, by omega⟩).1 + 1 at hunit
      omega
    exact hnoValley (T.valley_of_down_step ⟨r, hdown⟩)
  intro r s hrs
  exact nat_trace_monotone_on_of_le_succ
    (f := fun q : Fin (T.len + 1) => (T.row q).1)
    (lo := 0) (hi := T.len)
    (by
      intro k _ _
      exact hsucc k)
    (a := r) (b := s) (by omega) hrs (by omega)

/-- One concrete row-free bridge in the strip between rows `q` and `q+1`.
The path is a consecutive contact atom; `connects` allows either orientation
along the full column. -/
structure StripBridge
    (T : CorridorColumnTrace L activeCount C P)
    (q : Fin (activeCount + 1)) where
  step : Fin T.len
  lower : V
  upper : V
  lower_mem :
    lower ∈ (C.rowPath ⟨q.1, by omega⟩).vertexSet
  upper_mem :
    upper ∈ (C.rowPath ⟨q.1 + 1, by omega⟩).vertexSet
  connects :
    ((T.atom step).source = lower ∧ (T.atom step).target = upper) ∨
      ((T.atom step).source = upper ∧ (T.atom step).target = lower)

namespace StripBridge

variable {T : CorridorColumnTrace L activeCount C P}
variable {q : Fin (activeCount + 1)}

theorem lower_mem_column (D : T.StripBridge q) :
    D.lower ∈ P.vertexSet := by
  rcases D.connects with h | h
  · rw [← h.1]
    exact T.atom_vertexSet_subset_column D.step
      (GraphPath.source_mem_vertexSet (T.atom D.step))
  · rw [← h.2]
    exact T.atom_vertexSet_subset_column D.step
      (GraphPath.target_mem_vertexSet (T.atom D.step))

theorem upper_mem_column (D : T.StripBridge q) :
    D.upper ∈ P.vertexSet := by
  rcases D.connects with h | h
  · rw [← h.2]
    exact T.atom_vertexSet_subset_column D.step
      (GraphPath.target_mem_vertexSet (T.atom D.step))
  · rw [← h.1]
    exact T.atom_vertexSet_subset_column D.step
      (GraphPath.source_mem_vertexSet (T.atom D.step))

end StripBridge

namespace Valley

variable {T : CorridorColumnTrace L activeCount C P}

/-- Strip immediately below the top row of a valley. -/
def lowerStrip (D : T.Valley) : Fin (activeCount + 1) :=
  ⟨D.rowLower.1, by
    have ht := D.rowTop.2
    have hs := D.lower_succ
    omega⟩

/-- First atom of a valley, oriented from the lower row to the top row. -/
noncomputable def leftBridge (D : T.Valley) :
    T.StripBridge D.lowerStrip where
  step := ⟨D.left.1, D.left_lt_len⟩
  lower :=
    T.contact
      ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩
  upper := T.contact D.left
  lower_mem := by
    simpa [lowerStrip, D.left_succ_row] using
      T.contact_mem_row
        ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩
  upper_mem := by
    have hs := D.lower_succ
    simpa [lowerStrip, D.left_row, hs] using
      T.contact_mem_row D.left
  connects := Or.inr ⟨by simp, by simp⟩

/-- Last atom of a valley, oriented from the lower row to the top row. -/
noncomputable def rightBridge (D : T.Valley) :
    T.StripBridge D.lowerStrip := by
  let r : Fin T.len := ⟨D.right.1 - 1, by
    have hr := D.right.2
    have hp := D.right_pos
    omega⟩
  have hrSucc : r.1 + 1 = D.right.1 := by
    have hone : 1 ≤ D.right.1 := D.right_pos
    simpa [r] using Nat.sub_add_cancel hone
  refine {
    step := r
    lower := T.contact ⟨r.1, by omega⟩
    upper := T.contact D.right
    lower_mem := ?_
    upper_mem := ?_
    connects := Or.inl ⟨?_, ?_⟩
  }
  · have hpred := D.right_pred_row
    have hfin :
        (⟨r.1, by omega⟩ : Fin (T.len + 1)) =
          ⟨D.right.1 - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩ := by
      apply Fin.ext
      simp [r]
    simpa [lowerStrip, hfin, hpred] using
      T.contact_mem_row ⟨r.1, by omega⟩
  · have hs := D.lower_succ
    simpa [lowerStrip, D.right_row, hs] using
      T.contact_mem_row D.right
  · simp
  · simp
    congr 2

@[simp] theorem leftBridge_upper (D : T.Valley) :
    D.leftBridge.upper = T.contact D.left := rfl

@[simp] theorem leftBridge_lower (D : T.Valley) :
    D.leftBridge.lower =
      T.contact ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩ := rfl

@[simp] theorem rightBridge_upper (D : T.Valley) :
    D.rightBridge.upper = T.contact D.right := by
  simp [rightBridge]

@[simp] theorem rightBridge_lower (D : T.Valley) :
    D.rightBridge.lower =
      T.contact
        ⟨D.right.1 - 1,
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩ := by
  simp [rightBridge]

end Valley

/-- Under a monotone full-column trace, every strip has a concrete upward
bridge atom. -/
theorem exists_stripBridge_of_monotoneRows
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows)
    (q : Fin (activeCount + 1)) :
    Nonempty (T.StripBridge q) := by
  classical
  let lowerRow : Fin (activeCount + 2) := ⟨q.1, by omega⟩
  let upperRow : Fin (activeCount + 2) := ⟨q.1 + 1, by omega⟩
  have hexLower : ∃ r : Fin (T.len + 1), T.row r = lowerRow := by
    rcases C.path_hits_every_row P T.source_mem_lower T.target_mem_upper
        T.avoidsOutside lowerRow with ⟨v, hv⟩
    rcases Finset.mem_inter.1 hv with ⟨hvP, hvRow⟩
    rcases T.contact_complete hvP hvRow with ⟨r, hr⟩
    exact ⟨r, (T.contact_row_unique r lowerRow
      (by simpa [hr] using hvRow)).symm⟩
  have hexUpper : ∃ r : Fin (T.len + 1), T.row r = upperRow := by
    rcases C.path_hits_every_row P T.source_mem_lower T.target_mem_upper
        T.avoidsOutside upperRow with ⟨v, hv⟩
    rcases Finset.mem_inter.1 hv with ⟨hvP, hvRow⟩
    rcases T.contact_complete hvP hvRow with ⟨r, hr⟩
    exact ⟨r, (T.contact_row_unique r upperRow
      (by simpa [hr] using hvRow)).symm⟩
  let p : Fin (T.len + 1) := Classical.choose hexLower
  let s : Fin (T.len + 1) := Classical.choose hexUpper
  have hpRow : T.row p = lowerRow := by
    exact Classical.choose_spec hexLower
  have hsRow : T.row s = upperRow := by
    exact Classical.choose_spec hexUpper
  have hps : p.1 < s.1 := by
    by_contra hnot
    have hsp : s.1 ≤ p.1 := Nat.le_of_not_gt hnot
    have hbad := hmono s p hsp
    have hbad' : upperRow.1 ≤ lowerRow.1 := by
      simpa [hpRow, hsRow] using hbad
    dsimp [lowerRow, upperRow] at hbad'
    omega
  let f : Fin (T.len + 1) → ℕ := fun r => (T.row r).1
  let Cross : ℕ → Prop := fun n =>
    ∃ hn : n < T.len + 1,
      p.1 < n ∧ n ≤ s.1 ∧
        upperRow.1 ≤ f ⟨n, hn⟩
  have hex : ∃ n, Cross n := by
    exact ⟨s.1, s.2, hps, le_rfl, by simp [f, hsRow]⟩
  let k : ℕ := Nat.find hex
  have hkCross : Cross k := Nat.find_spec hex
  rcases hkCross with ⟨hkBound, hpLtK, hkLeS, hkUpper⟩
  let r : Fin T.len := ⟨k - 1, by omega⟩
  have hrSucc : r.1 + 1 = k := by
    simp [r]
    omega
  have hpLeR : p.1 ≤ r.1 := by
    simp [r]
    omega
  have hrSuccLeS : r.1 + 1 ≤ s.1 := by omega
  have hprevNotCross : ¬ Cross r.1 := by
    have hrLt : r.1 < k := by omega
    exact Nat.find_min hex hrLt
  have hprevLtUpper :
      f ⟨r.1, by omega⟩ < upperRow.1 := by
    have hrBound : r.1 < T.len + 1 := by omega
    have hpLtR_or_eq : p.1 < r.1 ∨ p.1 = r.1 := by omega
    have hnot :
        ¬ upperRow.1 ≤ f ⟨r.1, by omega⟩ := by
      intro h
      rcases hpLtR_or_eq with hpLtR | hpEqR
      · exact hprevNotCross ⟨hrBound, hpLtR, by omega, h⟩
      · have hpVal : f ⟨r.1, by omega⟩ = lowerRow.1 := by
          have hfin : (⟨r.1, by omega⟩ : Fin (T.len + 1)) = p :=
            Fin.ext hpEqR.symm
          simpa [hfin, f, hpRow]
        dsimp [lowerRow, upperRow] at h hpVal
        omega
    omega
  have hlowerLePrev :
      lowerRow.1 ≤ f ⟨r.1, by omega⟩ := by
    have hpfin : p.1 ≤ (⟨r.1, by omega⟩ : Fin (T.len + 1)).1 := hpLeR
    have hm := hmono p ⟨r.1, by omega⟩ hpfin
    simpa [f, hpRow] using hm
  have hprevEq :
      T.row ⟨r.1, by omega⟩ = lowerRow := by
    apply Fin.ext
    have hupperSucc :
        upperRow.1 = lowerRow.1 + 1 := by
      simp [lowerRow, upperRow]
    have hle :
        f ⟨r.1, by omega⟩ ≤ lowerRow.1 := by
      omega
    change f ⟨r.1, by omega⟩ = lowerRow.1
    exact le_antisymm hle hlowerLePrev
  have hnextLeUpper :
      f ⟨r.1 + 1, by omega⟩ ≤ upperRow.1 := by
    have hunit := T.unitStep r
    change
      f ⟨r.1 + 1, by omega⟩ ≤ f ⟨r.1, by omega⟩ + 1 ∧
        f ⟨r.1, by omega⟩ ≤ f ⟨r.1 + 1, by omega⟩ + 1 at hunit
    have hprevVal : f ⟨r.1, by omega⟩ = lowerRow.1 := by
      simpa [f] using congrArg Fin.val hprevEq
    dsimp [lowerRow, upperRow] at hprevVal ⊢
    omega
  have hnextGeUpper :
      upperRow.1 ≤ f ⟨r.1 + 1, by omega⟩ := by
    have hfin :
        (⟨r.1 + 1, by omega⟩ : Fin (T.len + 1)) =
          ⟨k, hkBound⟩ := Fin.ext hrSucc
    simpa [hfin] using hkUpper
  have hnextEq :
      T.row ⟨r.1 + 1, by omega⟩ = upperRow := by
    apply Fin.ext
    simpa [f] using le_antisymm hnextLeUpper hnextGeUpper
  refine ⟨{
    step := r
    lower := T.contact ⟨r.1, by omega⟩
    upper := T.contact ⟨r.1 + 1, by omega⟩
    lower_mem := by
      simpa [hprevEq, lowerRow] using T.contact_mem_row ⟨r.1, by omega⟩
    upper_mem := by
      simpa [hnextEq, upperRow] using
        T.contact_mem_row ⟨r.1 + 1, by omega⟩
    connects := Or.inl ⟨by simp, by simp⟩
  }⟩

/-- Canonically chosen upward bridge through one strip. -/
noncomputable def stripBridge
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows)
    (q : Fin (activeCount + 1)) : T.StripBridge q :=
  Classical.choice (T.exists_stripBridge_of_monotoneRows hmono q)

/-- A non-row column vertex lies between a unique adjacent pair of contacts;
existence of such a bracket is the part needed for trace convexity. -/
theorem exists_atom_bracketing_of_not_mem_rows
    (T : CorridorColumnTrace L activeCount C P)
    {v : V} (hvP : v ∈ P.vertexSet)
    (hvNotRows : v ∉ C.allRowVertexSet) :
    ∃ r : Fin T.len,
      P.Before (T.contact ⟨r.1, by omega⟩) v ∧
        P.Before v (T.contact ⟨r.1 + 1, by omega⟩) ∧
        (∀ k : Fin (T.len + 1),
          P.Before (T.contact k) v → k.1 ≤ r.1) ∧
        (∀ k : Fin (T.len + 1),
          P.Before v (T.contact k) → r.1 + 1 ≤ k.1) := by
  classical
  have hex :
      ∃ n : ℕ, ∃ hn : n < T.len + 1,
        P.Before v (T.contact ⟨n, hn⟩) := by
    refine ⟨T.len, by omega, ?_⟩
    simpa [CorridorColumnTrace.contact, CorridorColumnTrace.len] using
      P.before_target_of_mem hvP
  let n : ℕ := Nat.find hex
  have hspec :
      ∃ hn : n < T.len + 1,
        P.Before v (T.contact ⟨n, hn⟩) :=
    Nat.find_spec hex
  rcases hspec with ⟨hn, hvn⟩
  have hn_pos : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
    let z : Fin (T.len + 1) := ⟨0, by omega⟩
    have hzv : P.Before (T.contact z) v := by
      simpa [CorridorColumnTrace.contact, z] using P.source_before_of_mem hvP
    have hvz : P.Before v (T.contact z) := by
      simpa [z, hn0] using hvn
    have hvEq : v = T.contact z := P.before_antisymm hvz hzv
    exact hvNotRows (by
      rw [hvEq]
      exact C.rowPath_vertexSet_subset_allRowVertexSet (T.row z)
        (T.contact_mem_row z))
  have hn_le : n ≤ T.len := by omega
  let r : Fin T.len := ⟨n - 1, by omega⟩
  have hrsucc : r.1 + 1 = n := by
    simp [r]
    omega
  have hvSucc :
      P.Before v (T.contact ⟨r.1 + 1, by omega⟩) := by
    have hfin :
        (⟨r.1 + 1, by omega⟩ : Fin (T.len + 1)) = ⟨n, hn⟩ := by
      exact Fin.ext hrsucc
    simpa [hfin] using hvn
  have hnotBefore :
      ¬ P.Before v (T.contact ⟨r.1, by omega⟩) := by
    intro h
    have hrlt : r.1 < n := by omega
    exact (Nat.find_min hex hrlt) ⟨by omega, h⟩
  have hcontactP :
      T.contact ⟨r.1, by omega⟩ ∈ P.vertexSet :=
    T.contact_mem_column ⟨r.1, by omega⟩
  have hleft :
      P.Before (T.contact ⟨r.1, by omega⟩) v := by
    rcases ClaimB2Atom.graphPath_before_or_before_of_mem
        P hcontactP hvP with h | h
    · exact h
    · exact False.elim (hnotBefore h)
  have hcontact_ne_v :
      ∀ k : Fin (T.len + 1), T.contact k ≠ v := by
    intro k hEq
    exact hvNotRows (by
      rw [← hEq]
      exact C.rowPath_vertexSet_subset_allRowVertexSet (T.row k)
        (T.contact_mem_row k))
  have hbeforeBound :
      ∀ k : Fin (T.len + 1),
        P.Before (T.contact k) v → k.1 ≤ r.1 := by
    intro k hkv
    by_contra hnot
    have hnle : n ≤ k.1 := by omega
    have hnk :
        P.Before (T.contact ⟨n, hn⟩) (T.contact k) :=
      (T.contact_before_iff_le ⟨n, hn⟩ k).2 hnle
    have hvk : P.Before v (T.contact k) := P.before_trans hvn hnk
    have hvEq : v = T.contact k := P.before_antisymm hvk hkv
    exact hcontact_ne_v k hvEq.symm
  have hafterBound :
      ∀ k : Fin (T.len + 1),
        P.Before v (T.contact k) → r.1 + 1 ≤ k.1 := by
    intro k hvk
    by_contra hnot
    have hklt : k.1 < n := by omega
    exact (Nat.find_min hex hklt) ⟨k.2, hvk⟩
  exact ⟨r, hleft, hvSucc, hbeforeBound, hafterBound⟩

/-- A monotone full-column trace meets every fixed corridor row in a convex
subpath, once same-row atoms have been normalized by bump elimination. -/
theorem rowTraceConvex_of_monotoneRows_of_noBump
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) :
    GraphPathTraceConvex P (C.rowPath q).vertexSet := by
  classical
  intro a b c ha hc hbP hab hbc
  rcases Finset.mem_inter.1 ha with ⟨haP, haRow⟩
  rcases Finset.mem_inter.1 hc with ⟨hcP, hcRow⟩
  rcases T.contact_complete haP haRow with ⟨p, hp⟩
  rcases T.contact_complete hcP hcRow with ⟨s, hs⟩
  have hpRow : T.row p = q := by
    exact (T.contact_row_unique p q (by simpa [hp] using haRow)).symm
  have hsRow : T.row s = q := by
    exact (T.contact_row_unique s q (by simpa [hs] using hcRow)).symm
  have hps : p.1 ≤ s.1 := by
    exact (T.contact_before_iff_le p s).1 (by
      simpa [hp, hs] using P.before_trans hab hbc)
  by_cases hbRows : b ∈ C.allRowVertexSet
  · rw [AuxiliaryCorridor.allRowVertexSet, Finset.mem_biUnion] at hbRows
    rcases hbRows with ⟨qb, _hqb, hbRow⟩
    rcases T.contact_complete hbP hbRow with ⟨m, hm⟩
    have hpm : p.1 ≤ m.1 := by
      exact (T.contact_before_iff_le p m).1 (by simpa [hp, hm] using hab)
    have hms : m.1 ≤ s.1 := by
      exact (T.contact_before_iff_le m s).1 (by simpa [hm, hs] using hbc)
    have hqmLower : q.1 ≤ (T.row m).1 := by
      simpa [hpRow] using hmono p m hpm
    have hqmUpper : (T.row m).1 ≤ q.1 := by
      simpa [hsRow] using hmono m s hms
    have hmRow : T.row m = q := Fin.ext (le_antisymm hqmUpper hqmLower)
    simpa [hm, hmRow] using T.contact_mem_row m
  · rcases T.exists_atom_bracketing_of_not_mem_rows hbP hbRows with
      ⟨r, hleft, hright, hbeforeBound, hafterBound⟩
    let cur : Fin (T.len + 1) :=
      ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self T.len)⟩
    let nxt : Fin (T.len + 1) :=
      ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩
    have hpcur : p.1 ≤ cur.1 := by
      simpa [cur] using hbeforeBound p (by simpa [hp] using hab)
    have hnxts : nxt.1 ≤ s.1 := by
      simpa [nxt] using hafterBound s (by simpa [hs] using hbc)
    have hcurLower : q.1 ≤ (T.row cur).1 := by
      simpa [hpRow] using hmono p cur hpcur
    have hcurUpper : (T.row cur).1 ≤ q.1 := by
      have hcur_nxt : cur.1 ≤ nxt.1 := by simp [cur, nxt]
      exact le_trans (hmono cur nxt hcur_nxt)
        (by simpa [hsRow] using hmono nxt s hnxts)
    have hcurRow : T.row cur = q :=
      Fin.ext (le_antisymm hcurUpper hcurLower)
    have hnxtLower : q.1 ≤ (T.row nxt).1 := by
      exact le_trans hcurLower (hmono cur nxt (by simp [cur, nxt]))
    have hnxtUpper : (T.row nxt).1 ≤ q.1 := by
      simpa [hsRow] using hmono nxt s hnxts
    have hnxtRow : T.row nxt = q :=
      Fin.ext (le_antisymm hnxtUpper hnxtLower)
    have hsame : T.row cur = T.row nxt := hcurRow.trans hnxtRow.symm
    have habAtom : P.Before (T.contact cur) (T.contact nxt) :=
      (T.contact_before_iff_le cur nxt).2 (by simp [cur, nxt])
    have hbAtom : b ∈ (T.atom r).vertexSet := by
      exact P.mem_segmentOfBefore_of_before_of_before habAtom
        (by simpa [cur] using hleft) (by simpa [nxt] using hright)
    have hsubset :=
      T.atom_vertexSet_subset_row_of_noBump hnoBump r
        (by simpa [cur, nxt] using hsame)
    simpa [hcurRow, cur] using hsubset hbAtom

/-- Every row occurs in the complete contact trace.  This is the indexed
version of `AuxiliaryCorridor.path_hits_every_row`. -/
theorem exists_contact_on_row
    (T : CorridorColumnTrace L activeCount C P)
    (q : Fin (activeCount + 2)) :
    ∃ r : Fin (T.len + 1), T.row r = q := by
  rcases C.path_hits_every_row P T.source_mem_lower T.target_mem_upper
      T.avoidsOutside q with ⟨v, hv⟩
  rcases Finset.mem_inter.1 hv with ⟨hvP, hvRow⟩
  rcases T.contact_complete hvP hvRow with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  exact (T.contact_row_unique r q (by simpa [hr] using hvRow)).symm

/-- A canonical contact of the column with a specified corridor row. -/
noncomputable def contactAtRowIndex
    (T : CorridorColumnTrace L activeCount C P)
    (q : Fin (activeCount + 2)) : Fin (T.len + 1) :=
  Classical.choose (T.exists_contact_on_row q)

noncomputable def contactAtRow
    (T : CorridorColumnTrace L activeCount C P)
    (q : Fin (activeCount + 2)) : V :=
  T.contact (T.contactAtRowIndex q)

@[simp] theorem row_contactAtRowIndex
    (T : CorridorColumnTrace L activeCount C P)
    (q : Fin (activeCount + 2)) :
    T.row (T.contactAtRowIndex q) = q :=
  Classical.choose_spec (T.exists_contact_on_row q)

theorem contactAtRow_mem_column
    (T : CorridorColumnTrace L activeCount C P)
    (q : Fin (activeCount + 2)) :
    T.contactAtRow q ∈ P.vertexSet :=
  T.contact_mem_column (T.contactAtRowIndex q)

theorem contactAtRow_mem_row
    (T : CorridorColumnTrace L activeCount C P)
    (q : Fin (activeCount + 2)) :
    T.contactAtRow q ∈ (C.rowPath q).vertexSet := by
  simpa [contactAtRow, T.row_contactAtRowIndex q] using
    T.contact_mem_row (T.contactAtRowIndex q)

/-- The exact row-column intersection is path-shaped. -/
theorem traceOnRow_of_monotoneRows_of_noBump
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) :
    P.TraceOn (C.rowPath q).vertexSet := by
  apply graphPath_traceOn_of_traceConvex
  · exact ⟨T.contactAtRow q, Finset.mem_inter.2
      ⟨T.contactAtRow_mem_column q, T.contactAtRow_mem_row q⟩⟩
  · exact T.rowTraceConvex_of_monotoneRows_of_noBump hmono hnoBump q

/-- Canonical path whose vertices are exactly one row-column intersection. -/
noncomputable def intersectionPath
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) : GraphPath G :=
  Classical.choose (T.traceOnRow_of_monotoneRows_of_noBump hmono hnoBump q)

@[simp] theorem intersectionPath_vertexSet
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) :
    (T.intersectionPath hmono hnoBump q).vertexSet =
      P.vertexSet ∩ (C.rowPath q).vertexSet :=
  Classical.choose_spec
    (T.traceOnRow_of_monotoneRows_of_noBump hmono hnoBump q)

theorem intersectionPath_nonempty
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) :
    (T.intersectionPath hmono hnoBump q).vertexSet.Nonempty := by
  rw [T.intersectionPath_vertexSet hmono hnoBump q]
  exact ⟨T.contactAtRow q, Finset.mem_inter.2
    ⟨T.contactAtRow_mem_column q, T.contactAtRow_mem_row q⟩⟩

/-- Every row vertex lying between the endpoints of a same-row run of contacts
belongs to the column.  This local form is used in the blocker barrier before
global monotonicity has been established. -/
theorem mem_column_of_between_same_row_run
    (T : CorridorColumnTrace L activeCount C P)
    (hnoBump : T.NoBump)
    {q : Fin (activeCount + 2)}
    {p s : Fin (T.len + 1)}
    (hps : p.1 ≤ s.1)
    (hrows :
      ∀ k : Fin (T.len + 1), p.1 ≤ k.1 → k.1 ≤ s.1 →
        T.row k = q)
    {x : V} (hxRow : x ∈ (C.rowPath q).vertexSet)
    (hbetween :
      ((C.rowPath q).vertexIndex (T.contact p) ≤
          (C.rowPath q).vertexIndex x ∧
        (C.rowPath q).vertexIndex x ≤
          (C.rowPath q).vertexIndex (T.contact s)) ∨
      ((C.rowPath q).vertexIndex (T.contact s) ≤
          (C.rowPath q).vertexIndex x ∧
        (C.rowPath q).vertexIndex x ≤
          (C.rowPath q).vertexIndex (T.contact p))) :
    x ∈ P.vertexSet := by
  classical
  let Row : GraphPath G := C.rowPath q
  by_cases hEq : p.1 = s.1
  · have hpsEq : p = s := Fin.ext hEq
    have hpRow : T.row p = q := hrows p le_rfl hps
    have hpMem : T.contact p ∈ Row.vertexSet := by
      simpa [Row, hpRow] using T.contact_mem_row p
    have hidx :
        Row.vertexIndex x = Row.vertexIndex (T.contact p) := by
      rcases hbetween with h | h
      · have hxle :
            Row.vertexIndex x ≤ Row.vertexIndex (T.contact p) := by
          simpa [Row, hpsEq] using h.2
        exact le_antisymm hxle h.1
      · have hple :
            Row.vertexIndex (T.contact p) ≤ Row.vertexIndex x := by
          simpa [Row, hpsEq] using h.1
        exact le_antisymm h.2 hple
    have hxBefore :
        Row.Before x (T.contact p) :=
      (Row.before_iff_vertexIndex_le).2 ⟨hxRow, hpMem, by omega⟩
    have hpBefore :
        Row.Before (T.contact p) x :=
      (Row.before_iff_vertexIndex_le).2 ⟨hpMem, hxRow, by omega⟩
    have hxEq : x = T.contact p := Row.before_antisymm hxBefore hpBefore
    simpa [hxEq] using T.contact_mem_column p
  · have hplt : p.1 < s.1 := Nat.lt_of_le_of_ne hps hEq
    rcases exists_adjacent_straddle
        (n := T.len)
        (c := Row.vertexIndex x)
        (f := fun r : Fin (T.len + 1) =>
          Row.vertexIndex (T.contact r))
        hplt (by simpa [Row] using hbetween) with
      ⟨r, hp_r, hr_s, hpair⟩
    let cur : Fin (T.len + 1) :=
      ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self T.len)⟩
    let nxt : Fin (T.len + 1) :=
      ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩
    have hcurRow : T.row cur = q :=
      hrows cur (by simpa [cur] using hp_r) (by simp [cur]; omega)
    have hnxtRow : T.row nxt = q :=
      hrows nxt (by simp [nxt]; omega) (by simpa [nxt] using hr_s)
    have hsame : T.row cur = T.row nxt := hcurRow.trans hnxtRow.symm
    have hAtomV :
        (T.atom r).vertexSet ⊆ Row.vertexSet := by
      simpa [Row, cur, hcurRow] using
        T.atom_vertexSet_subset_row_of_noBump hnoBump r
          (by simpa [cur, nxt] using hsame)
    have hAtomE :
        (T.atom r).edgeSet ⊆ Row.edgeSet := by
      simpa [Row, cur, hcurRow] using
        T.atom_edgeSet_subset_row_of_noBump hnoBump r
          (by simpa [cur, nxt] using hsame)
    have hxAtom : x ∈ (T.atom r).vertexSet := by
      apply GraphPath.mem_of_vertexIndex_between_endpoints_of_edgeSet_subset
        Row (T.atom r) hAtomV hAtomE hxRow
      simpa [Row, cur, nxt] using hpair
    exact T.atom_vertexSet_subset_column r hxAtom

/-- Every row vertex lying between two equal-row contacts belongs to the
column.  The proof locates an adjacent contact atom whose row endpoints
straddle the vertex and then uses the no-bump edge containment of that atom. -/
theorem mem_column_of_between_equal_row_contacts
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    {q : Fin (activeCount + 2)}
    {p s : Fin (T.len + 1)}
    (hps : p.1 ≤ s.1)
    (hpRow : T.row p = q) (hsRow : T.row s = q)
    {x : V} (hxRow : x ∈ (C.rowPath q).vertexSet)
    (hbetween :
      ((C.rowPath q).vertexIndex (T.contact p) ≤
          (C.rowPath q).vertexIndex x ∧
        (C.rowPath q).vertexIndex x ≤
          (C.rowPath q).vertexIndex (T.contact s)) ∨
      ((C.rowPath q).vertexIndex (T.contact s) ≤
          (C.rowPath q).vertexIndex x ∧
        (C.rowPath q).vertexIndex x ≤
          (C.rowPath q).vertexIndex (T.contact p))) :
    x ∈ P.vertexSet := by
  classical
  let Row : GraphPath G := C.rowPath q
  by_cases hEq : p.1 = s.1
  · have hpsEq : p = s := Fin.ext hEq
    have hpMem : T.contact p ∈ Row.vertexSet := by
      simpa [Row, hpRow] using T.contact_mem_row p
    have hidx :
        Row.vertexIndex x = Row.vertexIndex (T.contact p) := by
      rcases hbetween with h | h
      · have hxle :
            Row.vertexIndex x ≤ Row.vertexIndex (T.contact p) := by
          simpa [Row, hpsEq] using h.2
        exact le_antisymm hxle h.1
      · have hple :
            Row.vertexIndex (T.contact p) ≤ Row.vertexIndex x := by
          simpa [Row, hpsEq] using h.1
        exact le_antisymm h.2 hple
    have hxBefore :
        Row.Before x (T.contact p) :=
      (Row.before_iff_vertexIndex_le).2 ⟨hxRow, hpMem, by omega⟩
    have hpBefore :
        Row.Before (T.contact p) x :=
      (Row.before_iff_vertexIndex_le).2 ⟨hpMem, hxRow, by omega⟩
    have hxEq : x = T.contact p := Row.before_antisymm hxBefore hpBefore
    simpa [hxEq] using T.contact_mem_column p
  · have hplt : p.1 < s.1 := Nat.lt_of_le_of_ne hps hEq
    rcases exists_adjacent_straddle
        (n := T.len)
        (c := Row.vertexIndex x)
        (f := fun r : Fin (T.len + 1) =>
          Row.vertexIndex (T.contact r))
        hplt (by simpa [Row] using hbetween) with
      ⟨r, hp_r, hr_s, hpair⟩
    let cur : Fin (T.len + 1) :=
      ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self T.len)⟩
    let nxt : Fin (T.len + 1) :=
      ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩
    have hcurLower : q.1 ≤ (T.row cur).1 := by
      simpa [hpRow] using hmono p cur (by simpa [cur] using hp_r)
    have hcurUpper : (T.row cur).1 ≤ q.1 := by
      have hcur_s : cur.1 ≤ s.1 := by
        simp [cur]
        omega
      simpa [hsRow] using hmono cur s hcur_s
    have hcurRow : T.row cur = q :=
      Fin.ext (le_antisymm hcurUpper hcurLower)
    have hnxtLower : q.1 ≤ (T.row nxt).1 := by
      have hp_nxt : p.1 ≤ nxt.1 := by
        simp [nxt]
        omega
      simpa [hpRow] using hmono p nxt hp_nxt
    have hnxtUpper : (T.row nxt).1 ≤ q.1 := by
      simpa [hsRow, nxt] using hmono nxt s (by simpa [nxt] using hr_s)
    have hnxtRow : T.row nxt = q :=
      Fin.ext (le_antisymm hnxtUpper hnxtLower)
    have hsame : T.row cur = T.row nxt := hcurRow.trans hnxtRow.symm
    have hAtomV :
        (T.atom r).vertexSet ⊆ Row.vertexSet := by
      simpa [Row, cur, hcurRow] using
        T.atom_vertexSet_subset_row_of_noBump hnoBump r
          (by simpa [cur, nxt] using hsame)
    have hAtomE :
        (T.atom r).edgeSet ⊆ Row.edgeSet := by
      simpa [Row, cur, hcurRow] using
        T.atom_edgeSet_subset_row_of_noBump hnoBump r
          (by simpa [cur, nxt] using hsame)
    have hxAtom : x ∈ (T.atom r).vertexSet := by
      apply GraphPath.mem_of_vertexIndex_between_endpoints_of_edgeSet_subset
        Row (T.atom r) hAtomV hAtomE hxRow
      simpa [Row, cur, nxt] using hpair
    exact T.atom_vertexSet_subset_column r hxAtom

/-- The same intersection is convex in the row order.  This is the horizontal
counterpart of `rowTraceConvex_of_monotoneRows_of_noBump`. -/
theorem rowTraceConvexColumn_of_monotoneRows_of_noBump
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) :
    GraphPathTraceConvex (C.rowPath q) P.vertexSet := by
  classical
  intro a b c ha hc hbRow hab hbc
  rcases Finset.mem_inter.1 ha with ⟨haRow, haP⟩
  rcases Finset.mem_inter.1 hc with ⟨hcRow, hcP⟩
  rcases T.contact_complete haP haRow with ⟨p, hp⟩
  rcases T.contact_complete hcP hcRow with ⟨s, hs⟩
  have hpRow : T.row p = q := by
    exact (T.contact_row_unique p q (by simpa [hp] using haRow)).symm
  have hsRow : T.row s = q := by
    exact (T.contact_row_unique s q (by simpa [hs] using hcRow)).symm
  have hbetween :
      ((C.rowPath q).vertexIndex (T.contact p) ≤
          (C.rowPath q).vertexIndex b ∧
        (C.rowPath q).vertexIndex b ≤
          (C.rowPath q).vertexIndex (T.contact s)) ∨
      ((C.rowPath q).vertexIndex (T.contact s) ≤
          (C.rowPath q).vertexIndex b ∧
        (C.rowPath q).vertexIndex b ≤
          (C.rowPath q).vertexIndex (T.contact p)) := by
    left
    exact
      ⟨by
        simpa [hp] using
          ((C.rowPath q).before_iff_vertexIndex_le).1 hab |>.2.2,
       by
        simpa [hs] using
          ((C.rowPath q).before_iff_vertexIndex_le).1 hbc |>.2.2⟩
  by_cases hps : p.1 ≤ s.1
  · exact T.mem_column_of_between_equal_row_contacts hmono hnoBump
      hps hpRow hsRow hbRow hbetween
  · have hsp : s.1 ≤ p.1 := Nat.le_of_not_ge hps
    exact T.mem_column_of_between_equal_row_contacts hmono hnoBump
      hsp hsRow hpRow hbRow hbetween.symm

/-- Row-oriented trace-on certificate for the exact intersection. -/
theorem rowTraceOnColumn_of_monotoneRows_of_noBump
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) :
    (C.rowPath q).TraceOn P.vertexSet := by
  apply graphPath_traceOn_of_traceConvex
  · exact ⟨T.contactAtRow q, Finset.mem_inter.2
      ⟨T.contactAtRow_mem_row q, T.contactAtRow_mem_column q⟩⟩
  · exact T.rowTraceConvexColumn_of_monotoneRows_of_noBump
      hmono hnoBump q

/-- Canonical row subpath whose vertices are exactly the row-column
intersection. -/
noncomputable def rowIntersectionPath
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) : GraphPath G :=
  Classical.choose
    (T.rowTraceOnColumn_of_monotoneRows_of_noBump hmono hnoBump q)

@[simp] theorem rowIntersectionPath_vertexSet
    (T : CorridorColumnTrace L activeCount C P)
    (hmono : T.MonotoneRows) (hnoBump : T.NoBump)
    (q : Fin (activeCount + 2)) :
    (T.rowIntersectionPath hmono hnoBump q).vertexSet =
      (C.rowPath q).vertexSet ∩ P.vertexSet :=
  Classical.choose_spec
    (T.rowTraceOnColumn_of_monotoneRows_of_noBump hmono hnoBump q)

/-- The maximal contiguous run of contacts on one fixed row.  The two
maximality fields are stated only when the corresponding neighboring raw
contact exists. -/
structure SameRowBlock
    (T : CorridorColumnTrace L activeCount C P)
    (q : Fin (activeCount + 2)) where
  first : Fin (T.len + 1)
  last : Fin (T.len + 1)
  first_le_last : first.1 ≤ last.1
  row_eq :
    ∀ r : Fin (T.len + 1), first.1 ≤ r.1 → r.1 ≤ last.1 →
      T.row r = q
  first_maximal :
    ∀ hpos : 0 < first.1,
      T.row ⟨first.1 - 1, by omega⟩ ≠ q
  last_maximal :
    ∀ hlt : last.1 < T.len,
      T.row ⟨last.1 + 1, by omega⟩ ≠ q

/-- Every contact belongs to a maximal same-row contact block. -/
theorem exists_sameRowBlock_at
    (T : CorridorColumnTrace L activeCount C P)
    (m : Fin (T.len + 1)) :
    ∃ B : T.SameRowBlock (T.row m),
      B.first.1 ≤ m.1 ∧ m.1 ≤ B.last.1 := by
  classical
  let q : Fin (activeCount + 2) := T.row m
  let Start : ℕ → Prop := fun n =>
    n ≤ m.1 ∧
      ∀ k : Fin (T.len + 1), n ≤ k.1 → k.1 ≤ m.1 →
        T.row k = q
  have hexStart : ∃ n, Start n := by
    refine ⟨m.1, le_rfl, ?_⟩
    intro k hmk hkm
    have hk : k = m := Fin.ext (Nat.le_antisymm hkm hmk)
    simpa [q, hk]
  let a : ℕ := Nat.find hexStart
  have ha : Start a := Nat.find_spec hexStart
  have haBound : a < T.len + 1 := by
    exact lt_of_le_of_lt ha.1 m.2
  let first : Fin (T.len + 1) := ⟨a, haBound⟩

  let Finish : ℕ → Prop := fun n =>
    m.1 ≤ n ∧ n ≤ T.len ∧
      ∀ k : Fin (T.len + 1), m.1 ≤ k.1 → k.1 ≤ n →
        T.row k = q
  have hmFinish : Finish m.1 := by
    refine ⟨le_rfl, by omega, ?_⟩
    intro k hmk hkm
    have hk : k = m := Fin.ext (Nat.le_antisymm hkm hmk)
    simpa [q, hk]
  let b : ℕ := Nat.findGreatest Finish T.len
  have hb : Finish b :=
    Nat.findGreatest_spec
      (P := Finish) (m := m.1) (n := T.len) (by omega) hmFinish
  have hbBound : b < T.len + 1 := by omega
  let last : Fin (T.len + 1) := ⟨b, hbBound⟩

  have hfirstMax :
      ∀ hpos : 0 < first.1,
        T.row ⟨first.1 - 1, by omega⟩ ≠ q := by
    intro hpos hprev
    have hnot : ¬ Start (a - 1) :=
      Nat.find_min hexStart (m := a - 1)
        (by dsimp [first] at hpos; omega)
    apply hnot
    refine ⟨by dsimp [first] at hpos ⊢; omega, ?_⟩
    intro k hak hkm
    by_cases hkprev : k.1 = a - 1
    · have hk :
          k = (⟨first.1 - 1, by omega⟩ : Fin (T.len + 1)) := by
        apply Fin.ext
        simpa [first] using hkprev
      simpa [hk] using hprev
    · have hak' : a ≤ k.1 := by
        dsimp [first] at hpos
        omega
      exact ha.2 k hak' hkm
  have hlastMax :
      ∀ hlt : last.1 < T.len,
        T.row ⟨last.1 + 1, by omega⟩ ≠ q := by
    intro hlt hnext
    have hnot : ¬ Finish (b + 1) :=
      Nat.findGreatest_is_greatest
        (P := Finish) (n := T.len) (k := b + 1)
        (by omega) (by simpa [last] using hlt)
    apply hnot
    refine ⟨by exact le_trans hb.1 (Nat.le_succ b),
      by dsimp [last] at hlt ⊢; omega, ?_⟩
    intro k hmk hkb
    by_cases hknext : k.1 = b + 1
    · have hk :
          k = (⟨last.1 + 1, by omega⟩ : Fin (T.len + 1)) := by
        apply Fin.ext
        simpa [last] using hknext
      simpa [hk] using hnext
    · have hkb' : k.1 ≤ b := by omega
      exact hb.2.2 k hmk hkb'

  let Block : T.SameRowBlock q := {
    first := first
    last := last
    first_le_last := by
      dsimp [first, last]
      exact le_trans ha.1 hb.1
    row_eq := by
      intro k hak hkb
      by_cases hkm : k.1 ≤ m.1
      · exact ha.2 k (by simpa [first] using hak) hkm
      · exact hb.2.2 k (by omega) (by simpa [last] using hkb)
    first_maximal := hfirstMax
    last_maximal := hlastMax
  }
  refine ⟨?_, ?_, ?_⟩
  · simpa [q] using Block
  · simpa [Block, first] using ha.1
  · simpa [Block, last] using hb.1

end CorridorColumnTrace

/-- Two disjoint convex traces on a path have a well-defined block order:
the order of one chosen pair of representatives is the order of every pair. -/
theorem graphPath_before_of_disjoint_traceConvex
    {Row : GraphPath G} {U W : Finset V}
    (hdisj : Disjoint U W)
    (hconvU : GraphPathTraceConvex Row U)
    (hconvW : GraphPathTraceConvex Row W)
    {u0 w0 u w : V}
    (hu0 : u0 ∈ Row.vertexSet ∩ U)
    (hw0 : w0 ∈ Row.vertexSet ∩ W)
    (hu : u ∈ Row.vertexSet ∩ U)
    (hw : w ∈ Row.vertexSet ∩ W)
    (hbase : Row.Before u0 w0) :
    Row.Before u w := by
  classical
  rcases Finset.mem_inter.1 hu0 with ⟨hu0Row, hu0U⟩
  rcases Finset.mem_inter.1 hw0 with ⟨hw0Row, hw0W⟩
  rcases Finset.mem_inter.1 hu with ⟨huRow, huU⟩
  rcases Finset.mem_inter.1 hw with ⟨hwRow, hwW⟩
  apply (Row.before_iff_vertexIndex_le).2
  refine ⟨huRow, hwRow, ?_⟩
  by_contra hnot
  have hwu : Row.vertexIndex w ≤ Row.vertexIndex u := by omega
  have hu0w0 :
      Row.vertexIndex u0 ≤ Row.vertexIndex w0 :=
    ((Row.before_iff_vertexIndex_le).1 hbase).2.2
  by_cases hu0w : Row.vertexIndex u0 ≤ Row.vertexIndex w
  · have hu0BeforeW : Row.Before u0 w :=
      (Row.before_iff_vertexIndex_le).2 ⟨hu0Row, hwRow, hu0w⟩
    have hwBeforeU : Row.Before w u :=
      (Row.before_iff_vertexIndex_le).2 ⟨hwRow, huRow, hwu⟩
    have hwU : w ∈ U :=
      hconvU hu0 hu hwRow hu0BeforeW hwBeforeU
    exact Finset.disjoint_left.mp hdisj hwU hwW
  · have hwu0 : Row.vertexIndex w ≤ Row.vertexIndex u0 := by omega
    have hwBeforeU0 : Row.Before w u0 :=
      (Row.before_iff_vertexIndex_le).2 ⟨hwRow, hu0Row, hwu0⟩
    have hu0BeforeW0 : Row.Before u0 w0 :=
      hbase
    have hu0W : u0 ∈ W :=
      hconvW hw hw0 hu0Row hwBeforeU0 hu0BeforeW0
    exact Finset.disjoint_left.mp hdisj hu0U hu0W

namespace FullBoundaryColumnFamily

variable {ι : Type w} {L : PerfectPathPacking G A B} {activeCount : ℕ}
variable {C : AuxiliaryCorridor L activeCount}

/-- The complete trace attached to one stored full column. -/
def trace (F : FullBoundaryColumnFamily L activeCount ι C) (i : ι) :
    CorridorColumnTrace L activeCount C (F.column i) where
  source_mem_lower := F.source_mem_lower i
  target_mem_upper := F.target_mem_upper i
  avoidsOutside := F.avoidsOutside i

theorem trace_index_eq_zero_of_row_zero
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (i : ι) (r : Fin ((F.trace i).len + 1))
    (hr :
      (F.trace i).row r = (⟨0, by omega⟩ : Fin (activeCount + 2))) :
    r.1 = 0 := by
  let T := F.trace i
  have hmem :
      T.contact r ∈ (F.column i).vertexSet ∩
        (C.rowPath ⟨0, by omega⟩).vertexSet :=
    Finset.mem_inter.2
      ⟨T.contact_mem_column r, by simpa [hr] using T.contact_mem_row r⟩
  have hsource : T.contact r = (F.column i).source := by
    rw [F.lower_contact i] at hmem
    simpa using hmem
  have hzero :
      T.contact ⟨0, by omega⟩ = (F.column i).source := by
    change
      endpointContact L (F.column i)
          ⟨0, by simp [endpointContactTraceLen]⟩ =
        (F.column i).source
    exact endpointContact_zero L (F.column i)
  have hrzero :
      r = (⟨0, by omega⟩ : Fin (T.len + 1)) :=
    T.contact_injective (hsource.trans hzero.symm)
  exact congrArg Fin.val hrzero

theorem trace_index_eq_last_of_row_upper
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (i : ι) (r : Fin ((F.trace i).len + 1))
    (hr :
      (F.trace i).row r =
        (⟨activeCount + 1, by omega⟩ : Fin (activeCount + 2))) :
    r.1 = (F.trace i).len := by
  let T := F.trace i
  have hmem :
      T.contact r ∈ (F.column i).vertexSet ∩
        (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet :=
    Finset.mem_inter.2
      ⟨T.contact_mem_column r, by simpa [hr] using T.contact_mem_row r⟩
  have htarget : T.contact r = (F.column i).target := by
    rw [F.upper_contact i] at hmem
    simpa using hmem
  have hlast :
      T.contact ⟨T.len, by omega⟩ = (F.column i).target := by
    change
      endpointContact L (F.column i)
          ⟨endpointContactTraceLen L (F.column i), by omega⟩ =
        (F.column i).target
    exact endpointContact_last L (F.column i)
  have hrlast :
      r = (⟨T.len, by omega⟩ : Fin (T.len + 1)) :=
    T.contact_injective (htarget.trans hlast.symm)
  exact congrArg Fin.val hrlast

/-- Active-row bump-freeness is enough for a full boundary-to-boundary
column: a same-row atom on either boundary would give two distinct contacts
at its unique boundary endpoint. -/
theorem trace_noBump_of_noActiveBump
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (i : ι) (hno : (F.trace i).NoActiveBump) :
    (F.trace i).NoBump := by
  rintro ⟨D⟩
  let T := F.trace i
  let cur : Fin (T.len + 1) := ⟨D.step.1, by omega⟩
  let nxt : Fin (T.len + 1) := ⟨D.step.1 + 1, by omega⟩
  have hsame : T.row cur = T.row nxt := by
    simpa [T, cur, nxt] using D.same_row
  by_cases hpos : 0 < (T.row cur).1
  · by_cases hlt : (T.row cur).1 < activeCount + 1
    · apply hno D
      · simpa [T, cur] using hpos
      · simpa only [T, cur] using hlt
    · have hupper :
          T.row cur =
            (⟨activeCount + 1, by omega⟩ : Fin (activeCount + 2)) := by
        apply Fin.ext
        change (T.row cur).1 = activeCount + 1
        have hbound := (T.row cur).2
        omega
      have hcurLast :=
        F.trace_index_eq_last_of_row_upper i cur hupper
      have hnxtLast :=
        F.trace_index_eq_last_of_row_upper i nxt
          (by simpa [hsame] using hupper)
      dsimp [cur, nxt] at hcurLast hnxtLast
      omega
  · have hlower :
        T.row cur = (⟨0, by omega⟩ : Fin (activeCount + 2)) := by
      apply Fin.ext
      change (T.row cur).1 = 0
      omega
    have hcurZero :=
      F.trace_index_eq_zero_of_row_zero i cur hlower
    have hnxtZero :=
      F.trace_index_eq_zero_of_row_zero i nxt
        (by simpa [hsame] using hlower)
    dsimp [cur, nxt] at hcurZero hnxtZero
    omega

/-- A valley cannot descend to the lower boundary, whose column contact is
the unique source. -/
theorem valley_lower_pos
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (i : ι) (D : (F.trace i).Valley) :
    0 < D.rowLower.1 := by
  by_contra hnot
  have hlower :
      D.rowLower = (⟨0, by omega⟩ : Fin (activeCount + 2)) :=
    Fin.ext (Nat.eq_zero_of_not_pos hnot)
  rcases D.hit_lower_strict with ⟨mid, hleft, _hright, hmid⟩
  have hmzero :
      mid.1 = 0 :=
    F.trace_index_eq_zero_of_row_zero i mid (by simpa [hlower] using hmid)
  omega

/-- A valley's top row is not the upper boundary, whose column contact is the
unique target. -/
theorem valley_top_lt_upper
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (i : ι) (D : (F.trace i).Valley) :
    D.rowTop.1 < activeCount + 1 := by
  by_contra hnot
  have htop :
      D.rowTop =
        (⟨activeCount + 1, by omega⟩ : Fin (activeCount + 2)) := by
    apply Fin.ext
    change D.rowTop.1 = activeCount + 1
    have hbound := D.rowTop.2
    omega
  have hleftLast :=
    F.trace_index_eq_last_of_row_upper i D.left
      (by simpa [htop] using D.left_row)
  have hrightLast :=
    F.trace_index_eq_last_of_row_upper i D.right
      (by simpa [htop] using D.right_row)
  have hleftRight := D.left_lt_right
  omega

/-- A valley is a hill when its top-row interval is disjoint from every other
column. -/
def IsHill
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (i : ι) (D : (F.trace i).Valley) : Prop :=
  ∀ j : ι, j ≠ i →
    Disjoint D.rowInterval.vertexSet (F.column j).vertexSet

/-- Hill elimination has terminated. -/
def NoHill
    (F : FullBoundaryColumnFamily L activeCount ι C) : Prop :=
  ∀ i : ι, ∀ D : (F.trace i).Valley, ¬ F.IsHill i D

/-- A surviving valley in a no-hill family has a concrete blocking column. -/
theorem exists_blocking_column_of_noHill
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hnoHill : F.NoHill)
    (i : ι) (D : (F.trace i).Valley) :
    ∃ j : ι, j ≠ i ∧
      ¬ Disjoint D.rowInterval.vertexSet (F.column j).vertexSet := by
  classical
  by_contra hnone
  apply hnoHill i D
  intro j hji
  by_contra hnotDisjoint
  exact hnone ⟨j, hji, hnotDisjoint⟩

/-- A finite family cannot contain valleys if every valley produces another
one on a strictly higher row.  This is the formal maximal-level argument in
Claim B.3. -/
theorem noValley_of_strictly_higher
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hraise :
      ∀ i : ι, ∀ D : (F.trace i).Valley,
        ∃ j : ι, ∃ E : (F.trace j).Valley,
          D.rowTop.1 < E.rowTop.1) :
    ∀ i : ι, ¬ Nonempty (F.trace i).Valley := by
  classical
  let remaining :
      (Σ i : ι, (F.trace i).Valley) → ℕ :=
    fun X => activeCount + 1 - X.2.rowTop.1
  have H :
      ∀ n : ℕ,
        ∀ X : Σ i : ι, (F.trace i).Valley,
          remaining X = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro X hn
        rcases hraise X.1 X.2 with ⟨j, E, htop⟩
        let Y : Σ i : ι, (F.trace i).Valley := ⟨j, E⟩
        have hXBound : X.2.rowTop.1 ≤ activeCount + 1 := by
          have := X.2.rowTop.2
          omega
        have hYBound : E.rowTop.1 ≤ activeCount + 1 := by
          have := E.rowTop.2
          omega
        have hrem : remaining Y < remaining X := by
          dsimp [remaining, Y]
          omega
        exact ih (remaining Y) (by simpa [hn] using hrem) Y rfl
  intro i hvalley
  rcases hvalley with ⟨D⟩
  exact H (remaining ⟨i, D⟩) ⟨i, D⟩ rfl

/-- A concrete cross of two column atoms in one strip. -/
structure Cross
    (F : FullBoundaryColumnFamily L activeCount ι C) where
  strip : Fin (activeCount + 1)
  first : ι
  second : ι
  first_ne_second : first ≠ second
  firstBridge : (F.trace first).StripBridge strip
  secondBridge : (F.trace second).StripBridge strip
  lower_reversed :
    (C.rowPath ⟨strip.1, by omega⟩).Before
      firstBridge.lower secondBridge.lower
  upper_reversed :
    (C.rowPath ⟨strip.1 + 1, by omega⟩).Before
      secondBridge.upper firstBridge.upper

/-- No pair of row-free column atoms crosses in any strip. -/
def NoCross (F : FullBoundaryColumnFamily L activeCount ι C) : Prop :=
  ¬ Nonempty F.Cross

/-- No cross remains in a strip whose two rows are both active.  The bump/cross
switching loop modifies active rows only, so this is the source-faithful
terminal invariant. -/
def NoActiveCross
    (F : FullBoundaryColumnFamily L activeCount ι C) : Prop :=
  ∀ X : F.Cross, 0 < X.strip.1 → X.strip.1 < activeCount → False

theorem column_vertexSet_disjoint
    (F : FullBoundaryColumnFamily L activeCount ι C)
    {i j : ι} (hij : i ≠ j) :
    Disjoint (F.column i).vertexSet (F.column j).vertexSet :=
  F.pairwise_nodeDisjoint hij

/-- A same-row contact run of a blocking column cannot leave a valley's row
interval.  Otherwise it skips one endpoint of that interval; no-bump makes
the skipped row segment part of the blocker column, contradicting column
disjointness. -/
theorem sameRow_contacts_stay_in_valleyInterval
    (F : FullBoundaryColumnFamily L activeCount ι C)
    {i j : ι} (hij : i ≠ j)
    (D : (F.trace i).Valley)
    (hnoBump : (F.trace j).NoBump)
    {p s : Fin ((F.trace j).len + 1)}
    (hrows :
      ∀ k : Fin ((F.trace j).len + 1),
        Nat.min p.1 s.1 ≤ k.1 → k.1 ≤ Nat.max p.1 s.1 →
          (F.trace j).row k = D.rowTop)
    (hpMem : (F.trace j).contact p ∈ D.rowInterval.vertexSet) :
    (F.trace j).contact s ∈ D.rowInterval.vertexSet := by
  classical
  let Ti := F.trace i
  let Tj := F.trace j
  let Row := C.rowPath D.rowTop
  have hpRow : Tj.contact p ∈ Row.vertexSet := by
    have hrow := hrows p (by simp) (by simp)
    simpa [Tj, Row, hrow] using Tj.contact_mem_row p
  have hsRow : Tj.contact s ∈ Row.vertexSet := by
    have hrow := hrows s (by simp) (by simp)
    simpa [Tj, Row, hrow] using Tj.contact_mem_row s
  by_contra hsNot
  have hpBetween := D.rowInterval_vertexIndex_between hpMem
  have hpBetween' :
      ((Row.vertexIndex (Ti.contact D.left) ≤
            Row.vertexIndex (Tj.contact p) ∧
          Row.vertexIndex (Tj.contact p) ≤
            Row.vertexIndex (Ti.contact D.right)) ∨
        (Row.vertexIndex (Ti.contact D.right) ≤
            Row.vertexIndex (Tj.contact p) ∧
          Row.vertexIndex (Tj.contact p) ≤
            Row.vertexIndex (Ti.contact D.left))) := by
    simpa [Ti, Tj, Row] using hpBetween
  have hsNotBetween :
      ¬ ((Row.vertexIndex (Ti.contact D.left) ≤
            Row.vertexIndex (Tj.contact s) ∧
          Row.vertexIndex (Tj.contact s) ≤
            Row.vertexIndex (Ti.contact D.right)) ∨
        (Row.vertexIndex (Ti.contact D.right) ≤
            Row.vertexIndex (Tj.contact s) ∧
          Row.vertexIndex (Tj.contact s) ≤
            Row.vertexIndex (Ti.contact D.left))) := by
    intro hb
    exact hsNot (D.mem_rowInterval_of_vertexIndex_between hsRow
      (by simpa [Ti, Tj, Row] using hb))
  have hskipped :
      ∃ e : Fin (Ti.len + 1),
        (e = D.left ∨ e = D.right) ∧
        ((Row.vertexIndex (Tj.contact p) ≤
              Row.vertexIndex (Ti.contact e) ∧
            Row.vertexIndex (Ti.contact e) ≤
              Row.vertexIndex (Tj.contact s)) ∨
          (Row.vertexIndex (Tj.contact s) ≤
              Row.vertexIndex (Ti.contact e) ∧
            Row.vertexIndex (Ti.contact e) ≤
              Row.vertexIndex (Tj.contact p))) := by
    rcases hpBetween' with hpForward | hpReverse
    · have horder :
          Row.vertexIndex (Ti.contact D.left) ≤
            Row.vertexIndex (Ti.contact D.right) := by omega
      have hsOutside :
          Row.vertexIndex (Tj.contact s) <
              Row.vertexIndex (Ti.contact D.left) ∨
            Row.vertexIndex (Ti.contact D.right) <
              Row.vertexIndex (Tj.contact s) := by
        omega
      rcases hsOutside with hsLeft | hsRight
      · exact ⟨D.left, Or.inl rfl, Or.inr ⟨by omega, by omega⟩⟩
      · exact ⟨D.right, Or.inr rfl, Or.inl ⟨by omega, by omega⟩⟩
    · have horder :
          Row.vertexIndex (Ti.contact D.right) ≤
            Row.vertexIndex (Ti.contact D.left) := by omega
      have hsOutside :
          Row.vertexIndex (Tj.contact s) <
              Row.vertexIndex (Ti.contact D.right) ∨
            Row.vertexIndex (Ti.contact D.left) <
              Row.vertexIndex (Tj.contact s) := by
        omega
      rcases hsOutside with hsRight | hsLeft
      · exact ⟨D.right, Or.inr rfl, Or.inr ⟨by omega, by omega⟩⟩
      · exact ⟨D.left, Or.inl rfl, Or.inl ⟨by omega, by omega⟩⟩
  rcases hskipped with ⟨e, he, heBetween⟩
  have heRow : Ti.contact e ∈ Row.vertexSet := by
    rcases he with rfl | rfl
    · simpa [Ti, Row] using D.left_mem_top
    · simpa [Ti, Row] using D.right_mem_top
  have heBlocker : Ti.contact e ∈ (F.column j).vertexSet := by
    by_cases hps : p.1 ≤ s.1
    · apply Tj.mem_column_of_between_same_row_run hnoBump hps
      · intro k hpk hks
        exact hrows k (by simp [Nat.min_eq_left hps]; exact hpk)
          (by simp [Nat.max_eq_right hps]; exact hks)
      · simpa [Row] using heRow
      · simpa [Ti, Tj, Row] using heBetween
    · have hsp : s.1 ≤ p.1 := Nat.le_of_not_ge hps
      apply Tj.mem_column_of_between_same_row_run hnoBump hsp
      · intro k hsk hkp
        exact hrows k (by simp [Nat.min_eq_right hsp]; exact hsk)
          (by simp [Nat.max_eq_left hsp]; exact hkp)
      · simpa [Row] using heRow
      · simpa [Ti, Tj, Row] using heBetween.symm
  have heOriginal : Ti.contact e ∈ (F.column i).vertexSet :=
    Ti.contact_mem_column e
  exact Finset.disjoint_left.mp (F.column_vertexSet_disjoint hij)
    heOriginal heBlocker

/-- The entire maximal blocker block containing a contact in the valley
interval has both endpoint contacts in that interval. -/
theorem sameRowBlock_endpoints_mem_valleyInterval
    (F : FullBoundaryColumnFamily L activeCount ι C)
    {i j : ι} (hij : i ≠ j)
    (D : (F.trace i).Valley)
    (hnoBump : (F.trace j).NoBump)
    {m : Fin ((F.trace j).len + 1)}
    (hmMem : (F.trace j).contact m ∈ D.rowInterval.vertexSet)
    (K : (F.trace j).SameRowBlock D.rowTop)
    (hfirst : K.first.1 ≤ m.1) (hlast : m.1 ≤ K.last.1) :
    (F.trace j).contact K.first ∈ D.rowInterval.vertexSet ∧
      (F.trace j).contact K.last ∈ D.rowInterval.vertexSet := by
  constructor
  · apply F.sameRow_contacts_stay_in_valleyInterval hij D hnoBump
      (p := m) (s := K.first)
    · intro k hkMin hkMax
      apply K.row_eq k
      · have hmin : Nat.min m.1 K.first.1 = K.first.1 :=
          Nat.min_eq_right hfirst
        simpa [hmin] using hkMin
      · have hmax : Nat.max m.1 K.first.1 = m.1 :=
          Nat.max_eq_left hfirst
        have hkm : k.1 ≤ m.1 := by simpa [hmax] using hkMax
        exact le_trans hkm hlast
    · exact hmMem
  · apply F.sameRow_contacts_stay_in_valleyInterval hij D hnoBump
      (p := m) (s := K.last)
    · intro k hkMin hkMax
      apply K.row_eq k
      · have hmin : Nat.min m.1 K.last.1 = m.1 :=
          Nat.min_eq_left hlast
        have hmk : m.1 ≤ k.1 := by simpa [hmin] using hkMin
        exact le_trans hfirst hmk
      · have hmax : Nat.max m.1 K.last.1 = K.last.1 :=
          Nat.max_eq_right hlast
        simpa [hmax] using hkMax
    · exact hmMem

/-- In one active strip, no-cross transfers the order of two bridge endpoints
from the upper row to the lower row. -/
theorem lower_order_of_upper_order
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hnoCross : F.NoActiveCross)
    {i j : ι} (hij : i ≠ j)
    {q : Fin (activeCount + 1)}
    (hqPos : 0 < q.1) (hqLt : q.1 < activeCount)
    (Bi : (F.trace i).StripBridge q)
    (Bj : (F.trace j).StripBridge q)
    (hupper :
      (C.rowPath ⟨q.1 + 1, by omega⟩).Before Bi.upper Bj.upper) :
    (C.rowPath ⟨q.1, by omega⟩).Before Bi.lower Bj.lower := by
  rcases ClaimB2Atom.graphPath_before_or_before_of_mem
      (C.rowPath ⟨q.1, by omega⟩) Bi.lower_mem Bj.lower_mem with
    hlower | hlowerRev
  · exact hlower
  · exact False.elim (hnoCross {
      strip := q
      first := j
      second := i
      first_ne_second := hij.symm
      firstBridge := Bj
      secondBridge := Bi
      lower_reversed := hlowerRev
      upper_reversed := hupper
    } hqPos hqLt)

/-- A bridge of another column cannot meet the interior row interval of a
valley and then descend to the valley's lower row.  The two valley boundary
bridges bracket it on the top row; no-cross brackets its lower endpoint
between the two lower contacts, where no-bump forces it onto the valley
column. -/
theorem impossible_bridge_through_valley
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hnoCross : F.NoActiveCross)
    {i j : ι} (hij : i ≠ j)
    (hnoBump : (F.trace i).NoBump)
    (D : (F.trace i).Valley)
    (M : (F.trace j).StripBridge D.lowerStrip)
    (hMmem : M.upper ∈ D.rowInterval.vertexSet) :
    False := by
  classical
  let Ti := F.trace i
  let Tj := F.trace j
  let Top := C.rowPath D.rowTop
  let Lower := C.rowPath D.rowLower
  have hqPos : 0 < D.lowerStrip.1 := by
    simpa [CorridorColumnTrace.Valley.lowerStrip] using
      F.valley_lower_pos i D
  have hqLt : D.lowerStrip.1 < activeCount := by
    have htop := F.valley_top_lt_upper i D
    have hs := D.lower_succ
    simp only [CorridorColumnTrace.Valley.lowerStrip]
    omega
  have htopEq :
      (⟨D.lowerStrip.1 + 1, by omega⟩ : Fin (activeCount + 2)) =
        D.rowTop := by
    apply Fin.ext
    simp [CorridorColumnTrace.Valley.lowerStrip]
    exact D.lower_succ
  have hlowerEq :
      (⟨D.lowerStrip.1, by omega⟩ : Fin (activeCount + 2)) =
        D.rowLower := by
    apply Fin.ext
    simp [CorridorColumnTrace.Valley.lowerStrip]
  have hMTop : M.upper ∈ Top.vertexSet := by
    simpa [Top, htopEq] using M.upper_mem
  have hMLower : M.lower ∈ Lower.vertexSet := by
    simpa [Lower, hlowerEq] using M.lower_mem
  have hMbetween := D.rowInterval_vertexIndex_between hMmem
  have hMbetween' :
      ((Top.vertexIndex (Ti.contact D.left) ≤ Top.vertexIndex M.upper ∧
          Top.vertexIndex M.upper ≤ Top.vertexIndex (Ti.contact D.right)) ∨
        (Top.vertexIndex (Ti.contact D.right) ≤ Top.vertexIndex M.upper ∧
          Top.vertexIndex M.upper ≤ Top.vertexIndex (Ti.contact D.left))) := by
    simpa [Ti, Top] using hMbetween
  have hLowerBetween :
      ((Lower.vertexIndex
            (Ti.contact
              ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩) ≤
          Lower.vertexIndex M.lower ∧
        Lower.vertexIndex M.lower ≤
          Lower.vertexIndex
            (Ti.contact
              ⟨D.right.1 - 1,
                Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩)) ∨
       (Lower.vertexIndex
            (Ti.contact
              ⟨D.right.1 - 1,
                Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩) ≤
          Lower.vertexIndex M.lower ∧
        Lower.vertexIndex M.lower ≤
          Lower.vertexIndex
            (Ti.contact
              ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩))) := by
    rcases hMbetween' with hForward | hReverse
    · have hLeftM :
          Top.Before (Ti.contact D.left) M.upper :=
        (Top.before_iff_vertexIndex_le).2
          ⟨by simpa [Ti, Top] using D.left_mem_top, hMTop, hForward.1⟩
      have hMRight :
          Top.Before M.upper (Ti.contact D.right) :=
        (Top.before_iff_vertexIndex_le).2
          ⟨hMTop, by simpa [Ti, Top] using D.right_mem_top, hForward.2⟩
      have hLeftLower :=
        F.lower_order_of_upper_order hnoCross hij hqPos hqLt
          D.leftBridge M (by
            rw [htopEq]
            simpa only [Ti] using hLeftM)
      have hRightLower :=
        F.lower_order_of_upper_order hnoCross hij.symm hqPos hqLt
          M D.rightBridge (by
            rw [htopEq]
            simpa only [Ti] using hMRight)
      have hLeftLower' :
          Lower.Before
            (Ti.contact
              ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩)
            M.lower := by
        simpa only [Lower, hlowerEq,
          CorridorColumnTrace.Valley.leftBridge_lower, Ti] using hLeftLower
      have hRightLower' :
          Lower.Before M.lower
            (Ti.contact
              ⟨D.right.1 - 1,
                Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩) := by
        simpa only [Lower, hlowerEq,
          CorridorColumnTrace.Valley.rightBridge_lower, Ti] using hRightLower
      left
      exact
        ⟨(Lower.before_iff_vertexIndex_le).1 hLeftLower' |>.2.2,
         (Lower.before_iff_vertexIndex_le).1 hRightLower' |>.2.2⟩
    · have hRightM :
          Top.Before (Ti.contact D.right) M.upper :=
        (Top.before_iff_vertexIndex_le).2
          ⟨by simpa [Ti, Top] using D.right_mem_top, hMTop, hReverse.1⟩
      have hMLeft :
          Top.Before M.upper (Ti.contact D.left) :=
        (Top.before_iff_vertexIndex_le).2
          ⟨hMTop, by simpa [Ti, Top] using D.left_mem_top, hReverse.2⟩
      have hRightLower :=
        F.lower_order_of_upper_order hnoCross hij hqPos hqLt
          D.rightBridge M (by
            rw [htopEq]
            simpa only [Ti] using hRightM)
      have hLeftLower :=
        F.lower_order_of_upper_order hnoCross hij.symm hqPos hqLt
          M D.leftBridge (by
            rw [htopEq]
            simpa only [Ti] using hMLeft)
      have hRightLower' :
          Lower.Before
            (Ti.contact
              ⟨D.right.1 - 1,
                Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩)
            M.lower := by
        simpa only [Lower, hlowerEq,
          CorridorColumnTrace.Valley.rightBridge_lower, Ti] using hRightLower
      have hLeftLower' :
          Lower.Before M.lower
            (Ti.contact
              ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩) := by
        simpa only [Lower, hlowerEq,
          CorridorColumnTrace.Valley.leftBridge_lower, Ti] using hLeftLower
      right
      exact
        ⟨(Lower.before_iff_vertexIndex_le).1 hRightLower' |>.2.2,
         (Lower.before_iff_vertexIndex_le).1 hLeftLower' |>.2.2⟩
  have hMonOriginal : M.lower ∈ (F.column i).vertexSet := by
    apply Ti.mem_column_of_between_same_row_run hnoBump
      (p :=
        ⟨D.left.1 + 1, Nat.succ_lt_succ D.left_lt_len⟩)
      (s :=
        ⟨D.right.1 - 1,
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) D.right.2⟩)
      D.left_succ_le_right_pred
    · intro k hleft hright
      exact D.row_eq_lower_of_internal k hleft hright
    · simpa [Lower] using hMLower
    · simpa [Ti, Lower] using hLowerBetween
  exact Finset.disjoint_left.mp (F.column_vertexSet_disjoint hij)
    hMonOriginal M.lower_mem_column

/-- The concrete blocker barrier of Claim B.3.  A blocking contact is extended
to its maximal same-row block.  Its two neighboring atoms cannot come from
the lower row by `impossible_bridge_through_valley`, so unit-step forces both
neighbors onto the row above, producing the next valley. -/
theorem higher_valley_of_blocker
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hnoBump : ∀ k : ι, (F.trace k).NoBump)
    (hnoCross : F.NoActiveCross)
    {i j : ι} (hij : i ≠ j)
    (D : (F.trace i).Valley)
    (hblocked :
      ¬ Disjoint D.rowInterval.vertexSet (F.column j).vertexSet) :
    ∃ E : (F.trace j).Valley, E.rowLower = D.rowTop := by
  classical
  let Ti := F.trace i
  let Tj := F.trace j
  rcases Finset.not_disjoint_iff.1 hblocked with ⟨x, hxInterval, hxColumn⟩
  have hxTop : x ∈ (C.rowPath D.rowTop).vertexSet :=
    D.rowInterval_vertexSet_subset_top hxInterval
  rcases Tj.contact_complete hxColumn hxTop with ⟨m, hm⟩
  have hmRow : Tj.row m = D.rowTop := by
    exact (Tj.contact_row_unique m D.rowTop
      (by simpa [hm] using hxTop)).symm
  have hmInterval : Tj.contact m ∈ D.rowInterval.vertexSet := by
    simpa [hm] using hxInterval
  have hexK :
      ∃ K : Tj.SameRowBlock D.rowTop,
        K.first.1 ≤ m.1 ∧ m.1 ≤ K.last.1 := by
    rw [← hmRow]
    exact Tj.exists_sameRowBlock_at m
  rcases hexK with ⟨K, hfirstM', hmLast'⟩
  have hKends :=
    F.sameRowBlock_endpoints_mem_valleyInterval hij D (hnoBump j)
      hmInterval K hfirstM' hmLast'
  have hfirstPos : 0 < K.first.1 := by
    by_contra hnot
    have hfirstZero : K.first.1 = 0 := Nat.eq_zero_of_not_pos hnot
    have hrow := K.row_eq K.first le_rfl K.first_le_last
    have hz := Tj.row_zero
    have hs := D.lower_succ
    have hlowerPos := F.valley_lower_pos i D
    have hfin :
        K.first = (⟨0, by omega⟩ : Fin (Tj.len + 1)) :=
      Fin.ext hfirstZero
    rw [hfin] at hrow
    have hval := congrArg Fin.val hrow
    omega
  have hlastLt : K.last.1 < Tj.len := by
    by_contra hnot
    have hlastEq : K.last.1 = Tj.len := by
      have hbound := K.last.2
      omega
    have hrow := K.row_eq K.last K.first_le_last le_rfl
    have hlast := Tj.row_last
    have htop := F.valley_top_lt_upper i D
    have hfin :
        K.last = (⟨Tj.len, by omega⟩ : Fin (Tj.len + 1)) :=
      Fin.ext hlastEq
    rw [hfin] at hrow
    have hval := congrArg Fin.val hrow
    omega
  let prev : Fin (Tj.len + 1) := ⟨K.first.1 - 1, by omega⟩
  let next : Fin (Tj.len + 1) := ⟨K.last.1 + 1, by omega⟩
  have hprevNot : Tj.row prev ≠ D.rowTop := by
    simpa [prev] using K.first_maximal hfirstPos
  have hnextNot : Tj.row next ≠ D.rowTop := by
    simpa [next] using K.last_maximal hlastLt
  have hprevConsecutive : FinConsecutive (Tj.row prev) D.rowTop := by
    let e : Fin Tj.len := ⟨K.first.1 - 1, by omega⟩
    have hnextIndex :
        (⟨e.1 + 1, by omega⟩ : Fin (Tj.len + 1)) = K.first := by
      apply Fin.ext
      simp [e]
      omega
    have hprevIndex :
        (⟨e.1, by omega⟩ : Fin (Tj.len + 1)) = prev := by
      apply Fin.ext
      simp [e, prev]
    have hfirstRow :
        Tj.row K.first = D.rowTop :=
      K.row_eq K.first le_rfl K.first_le_last
    rcases Tj.row_eq_or_consecutive e with heq | hcon
    · exfalso
      apply hprevNot
      simpa [hprevIndex, hnextIndex, hfirstRow] using heq
    · simpa [hprevIndex, hnextIndex, hfirstRow] using hcon
  have hnextConsecutive : FinConsecutive D.rowTop (Tj.row next) := by
    let e : Fin Tj.len := ⟨K.last.1, hlastLt⟩
    have hcurIndex :
        (⟨e.1, by omega⟩ : Fin (Tj.len + 1)) = K.last := by
      apply Fin.ext
      simp [e]
    have hnextIndex :
        (⟨e.1 + 1, by omega⟩ : Fin (Tj.len + 1)) = next := by
      apply Fin.ext
      simp [e, next]
    have hlastRow := K.row_eq K.last K.first_le_last le_rfl
    rcases Tj.row_eq_or_consecutive e with heq | hcon
    · exfalso
      apply hnextNot
      calc
        Tj.row next = Tj.row K.last := by
          simpa [hcurIndex, hnextIndex] using heq.symm
        _ = D.rowTop := hlastRow
    · have hcon' :
          FinConsecutive (Tj.row K.last) (Tj.row next) := by
        simpa [hcurIndex, hnextIndex] using hcon
      simpa [hlastRow] using hcon'
  have hprevUpper :
      D.rowTop.1 + 1 = (Tj.row prev).1 := by
    rcases hprevConsecutive with hprevLower | hprevUpper
    · have hprevLowerRow : Tj.row prev = D.rowLower := by
        apply Fin.ext
        have hs := D.lower_succ
        omega
      let e : Fin Tj.len := ⟨K.first.1 - 1, by omega⟩
      let M : Tj.StripBridge D.lowerStrip := {
        step := e
        lower := Tj.contact prev
        upper := Tj.contact K.first
        lower_mem := by
          have hmem := Tj.contact_mem_row prev
          have hlower :
              (⟨D.lowerStrip.1, by omega⟩ : Fin (activeCount + 2)) =
                D.rowLower := by
            apply Fin.ext
            simp [CorridorColumnTrace.Valley.lowerStrip]
          simpa [hprevLowerRow, hlower] using hmem
        upper_mem := by
          have hmem := Tj.contact_mem_row K.first
          have hrow := K.row_eq K.first le_rfl K.first_le_last
          have htop :
              (⟨D.lowerStrip.1 + 1, by omega⟩ :
                Fin (activeCount + 2)) = D.rowTop := by
            apply Fin.ext
            simp [CorridorColumnTrace.Valley.lowerStrip]
            exact D.lower_succ
          simpa [hrow, htop] using hmem
        connects := by
          left
          constructor
          · simp [e, prev]
          · have hidx :
                (⟨e.1 + 1, by omega⟩ : Fin (Tj.len + 1)) =
                  K.first := by
              apply Fin.ext
              simp [e]
              omega
            simpa [hidx]
      }
      exact False.elim
        (F.impossible_bridge_through_valley hnoCross hij (hnoBump i)
          D M (by simpa [M] using hKends.1))
    · exact hprevUpper
  have hnextUpper :
      D.rowTop.1 + 1 = (Tj.row next).1 := by
    rcases hnextConsecutive with hnextUpper | hnextLower
    · exact hnextUpper
    · have hnextLowerRow : Tj.row next = D.rowLower := by
        apply Fin.ext
        have hs := D.lower_succ
        omega
      let e : Fin Tj.len := ⟨K.last.1, hlastLt⟩
      let M : Tj.StripBridge D.lowerStrip := {
        step := e
        lower := Tj.contact next
        upper := Tj.contact K.last
        lower_mem := by
          have hmem := Tj.contact_mem_row next
          have hlower :
              (⟨D.lowerStrip.1, by omega⟩ : Fin (activeCount + 2)) =
                D.rowLower := by
            apply Fin.ext
            simp [CorridorColumnTrace.Valley.lowerStrip]
          simpa [hnextLowerRow, hlower] using hmem
        upper_mem := by
          have hmem := Tj.contact_mem_row K.last
          have hrow := K.row_eq K.last K.first_le_last le_rfl
          have htop :
              (⟨D.lowerStrip.1 + 1, by omega⟩ :
                Fin (activeCount + 2)) = D.rowTop := by
            apply Fin.ext
            simp [CorridorColumnTrace.Valley.lowerStrip]
            exact D.lower_succ
          simpa [hrow, htop] using hmem
        connects := by
          right
          constructor
          · simp [e]
          · simp [e, next]
      }
      exact False.elim
        (F.impossible_bridge_through_valley hnoCross hij (hnoBump i)
          D M (by simpa [M] using hKends.2))
  have htopRows : Tj.row next = Tj.row prev := by
    apply Fin.ext
    omega
  refine ⟨{
    left := prev
    right := next
    rowTop := Tj.row prev
    rowLower := D.rowTop
    left_lt_right := by
      dsimp [prev, next]
      have hle := K.first_le_last
      omega
    left_row := rfl
    right_row := htopRows
    lower_succ := hprevUpper
    hit_lower := ?_
    contacts_only_lower_or_endpoints := ?_
  }, rfl⟩
  · refine ⟨K.first, ?_, ?_,
      K.row_eq K.first le_rfl K.first_le_last⟩
    · dsimp [prev]
      omega
    · dsimp [next]
      omega
  · intro r hleft hright hnotLower
    by_cases hrPrev : r = prev
    · exact Or.inl hrPrev
    by_cases hrNext : r = next
    · exact Or.inr hrNext
    have hfirstLe : K.first.1 ≤ r.1 := by
      dsimp [prev] at hleft
      have hne : r.1 ≠ K.first.1 - 1 := by
        intro heq
        apply hrPrev
        exact Fin.ext heq
      omega
    have hrLast : r.1 ≤ K.last.1 := by
      dsimp [next] at hright
      have hne : r.1 ≠ K.last.1 + 1 := by
        intro heq
        apply hrNext
        exact Fin.ext heq
      omega
    exact False.elim (hnotLower (K.row_eq r hfirstLe hrLast))

/-- In a no-cross family, the order of two intersection blocks is preserved
from one row to the next. -/
theorem adjacent_contactAtRow_order
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hmono : ∀ i, (F.trace i).MonotoneRows)
    (hnoBump : ∀ i, (F.trace i).NoBump)
    (hnoCross : F.NoCross)
    {i j : ι} (hij : i ≠ j)
    (q : Fin (activeCount + 1)) :
    (C.rowPath ⟨q.1, by omega⟩).Before
        ((F.trace i).contactAtRow ⟨q.1, by omega⟩)
        ((F.trace j).contactAtRow ⟨q.1, by omega⟩) ↔
      (C.rowPath ⟨q.1 + 1, by omega⟩).Before
        ((F.trace i).contactAtRow ⟨q.1 + 1, by omega⟩)
        ((F.trace j).contactAtRow ⟨q.1 + 1, by omega⟩) := by
  classical
  let lower : Fin (activeCount + 2) := ⟨q.1, by omega⟩
  let upper : Fin (activeCount + 2) := ⟨q.1 + 1, by omega⟩
  let Ti := F.trace i
  let Tj := F.trace j
  let Bi := Ti.stripBridge (hmono i) q
  let Bj := Tj.stripBridge (hmono j) q
  have hdisj := F.column_vertexSet_disjoint hij
  have hconvIL :
      GraphPathTraceConvex (C.rowPath lower) (F.column i).vertexSet :=
    Ti.rowTraceConvexColumn_of_monotoneRows_of_noBump
      (hmono i) (hnoBump i) lower
  have hconvJL :
      GraphPathTraceConvex (C.rowPath lower) (F.column j).vertexSet :=
    Tj.rowTraceConvexColumn_of_monotoneRows_of_noBump
      (hmono j) (hnoBump j) lower
  have hconvIU :
      GraphPathTraceConvex (C.rowPath upper) (F.column i).vertexSet :=
    Ti.rowTraceConvexColumn_of_monotoneRows_of_noBump
      (hmono i) (hnoBump i) upper
  have hconvJU :
      GraphPathTraceConvex (C.rowPath upper) (F.column j).vertexSet :=
    Tj.rowTraceConvexColumn_of_monotoneRows_of_noBump
      (hmono j) (hnoBump j) upper
  have hrepIL :
      Ti.contactAtRow lower ∈
        (C.rowPath lower).vertexSet ∩ (F.column i).vertexSet :=
    Finset.mem_inter.2
      ⟨Ti.contactAtRow_mem_row lower, Ti.contactAtRow_mem_column lower⟩
  have hrepJL :
      Tj.contactAtRow lower ∈
        (C.rowPath lower).vertexSet ∩ (F.column j).vertexSet :=
    Finset.mem_inter.2
      ⟨Tj.contactAtRow_mem_row lower, Tj.contactAtRow_mem_column lower⟩
  have hrepIU :
      Ti.contactAtRow upper ∈
        (C.rowPath upper).vertexSet ∩ (F.column i).vertexSet :=
    Finset.mem_inter.2
      ⟨Ti.contactAtRow_mem_row upper, Ti.contactAtRow_mem_column upper⟩
  have hrepJU :
      Tj.contactAtRow upper ∈
        (C.rowPath upper).vertexSet ∩ (F.column j).vertexSet :=
    Finset.mem_inter.2
      ⟨Tj.contactAtRow_mem_row upper, Tj.contactAtRow_mem_column upper⟩
  have hbridgeIL :
      Bi.lower ∈
        (C.rowPath lower).vertexSet ∩ (F.column i).vertexSet := by
    exact Finset.mem_inter.2
      ⟨by simpa [Bi, lower] using Bi.lower_mem,
       by simpa [Ti, Bi] using Bi.lower_mem_column⟩
  have hbridgeJL :
      Bj.lower ∈
        (C.rowPath lower).vertexSet ∩ (F.column j).vertexSet := by
    exact Finset.mem_inter.2
      ⟨by simpa [Bj, lower] using Bj.lower_mem,
       by simpa [Tj, Bj] using Bj.lower_mem_column⟩
  have hbridgeIU :
      Bi.upper ∈
        (C.rowPath upper).vertexSet ∩ (F.column i).vertexSet := by
    exact Finset.mem_inter.2
      ⟨by simpa [Bi, upper] using Bi.upper_mem,
       by simpa [Ti, Bi] using Bi.upper_mem_column⟩
  have hbridgeJU :
      Bj.upper ∈
        (C.rowPath upper).vertexSet ∩ (F.column j).vertexSet := by
    exact Finset.mem_inter.2
      ⟨by simpa [Bj, upper] using Bj.upper_mem,
       by simpa [Tj, Bj] using Bj.upper_mem_column⟩
  constructor
  · intro hLower
    have hBridgeLower :
        (C.rowPath lower).Before Bi.lower Bj.lower :=
      graphPath_before_of_disjoint_traceConvex hdisj hconvIL hconvJL
        hrepIL hrepJL hbridgeIL hbridgeJL (by simpa [lower] using hLower)
    rcases ClaimB2Atom.graphPath_before_or_before_of_mem
        (C.rowPath upper)
        (Finset.mem_inter.1 hrepIU).1
        (Finset.mem_inter.1 hrepJU).1 with hUpper | hUpperRev
    · simpa [upper] using hUpper
    · have hBridgeUpperRev :
          (C.rowPath upper).Before Bj.upper Bi.upper :=
        graphPath_before_of_disjoint_traceConvex hdisj.symm hconvJU hconvIU
          hrepJU hrepIU hbridgeJU hbridgeIU hUpperRev
      exact False.elim (hnoCross ⟨{
        strip := q
        first := i
        second := j
        first_ne_second := hij
        firstBridge := Bi
        secondBridge := Bj
        lower_reversed := by simpa [lower] using hBridgeLower
        upper_reversed := by simpa [upper] using hBridgeUpperRev
      }⟩)
  · intro hUpper
    rcases ClaimB2Atom.graphPath_before_or_before_of_mem
        (C.rowPath lower)
        (Finset.mem_inter.1 hrepIL).1
        (Finset.mem_inter.1 hrepJL).1 with hLower | hLowerRev
    · simpa [lower] using hLower
    · have hBridgeLowerRev :
          (C.rowPath lower).Before Bj.lower Bi.lower :=
        graphPath_before_of_disjoint_traceConvex hdisj.symm hconvJL hconvIL
          hrepJL hrepIL hbridgeJL hbridgeIL hLowerRev
      have hBridgeUpper :
          (C.rowPath upper).Before Bi.upper Bj.upper :=
        graphPath_before_of_disjoint_traceConvex hdisj hconvIU hconvJU
          hrepIU hrepJU hbridgeIU hbridgeJU (by simpa [upper] using hUpper)
      exact False.elim (hnoCross ⟨{
        strip := q
        first := j
        second := i
        first_ne_second := Ne.symm hij
        firstBridge := Bj
        secondBridge := Bi
        lower_reversed := by simpa [lower] using hBridgeLowerRev
        upper_reversed := by simpa [upper] using hBridgeUpper
      }⟩)

/-- Every row gives the same order on a fixed pair of distinct columns. -/
theorem common_contactAtRow_order
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hmono : ∀ i, (F.trace i).MonotoneRows)
    (hnoBump : ∀ i, (F.trace i).NoBump)
    (hnoCross : F.NoCross)
    {i j : ι} (hij : i ≠ j)
    (q r : Fin (activeCount + 2)) :
    (C.rowPath q).Before
        ((F.trace i).contactAtRow q)
        ((F.trace j).contactAtRow q) ↔
      (C.rowPath r).Before
        ((F.trace i).contactAtRow r)
        ((F.trace j).contactAtRow r) := by
  classical
  let zero : Fin (activeCount + 2) := ⟨0, by omega⟩
  have H :
      ∀ n : ℕ, ∀ s : Fin (activeCount + 2), s.1 = n →
        ((C.rowPath zero).Before
            ((F.trace i).contactAtRow zero)
            ((F.trace j).contactAtRow zero) ↔
          (C.rowPath s).Before
            ((F.trace i).contactAtRow s)
            ((F.trace j).contactAtRow s)) := by
    intro n
    induction n with
    | zero =>
        intro s hs
        have hsz : s = zero := Fin.ext hs
        simp [hsz]
    | succ n ih =>
        intro s hs
        have hnBound : n < activeCount + 1 := by omega
        let prev : Fin (activeCount + 2) := ⟨n, by omega⟩
        let strip : Fin (activeCount + 1) := ⟨n, hnBound⟩
        have hsSucc :
            s = (⟨n + 1, by omega⟩ : Fin (activeCount + 2)) :=
          Fin.ext hs
        have hprev := ih prev rfl
        have hadj :=
          F.adjacent_contactAtRow_order hmono hnoBump hnoCross hij strip
        have hadj' :
            (C.rowPath prev).Before
                ((F.trace i).contactAtRow prev)
                ((F.trace j).contactAtRow prev) ↔
              (C.rowPath s).Before
                ((F.trace i).contactAtRow s)
                ((F.trace j).contactAtRow s) := by
          simpa [prev, strip, hsSucc] using hadj
        exact hprev.trans hadj'
  have hq := H q.1 q rfl
  have hr := H r.1 r rfl
  exact hq.symm.trans hr

/-- Terminal row/column geometry obtained after the valley argument.

The fields are exactly the three primitive terminal properties.  Convex
intersection paths and the common column order are theorems below, not fields
that a caller may postulate independently. -/
structure TerminalGeometry
    (F : FullBoundaryColumnFamily L activeCount ι C) where
  monotoneRows : ∀ i, (F.trace i).MonotoneRows
  noBump : ∀ i, (F.trace i).NoBump
  noCross : F.NoCross

namespace TerminalGeometry

variable {F : FullBoundaryColumnFamily L activeCount ι C}

/-- Finish Claim B.3 from the paper's blocker-barrier lemma.

The final argument is fully formal: no-hill gives a blocker, the barrier gives
a higher valley, finite ascent rules out every valley, and no-valley yields a
monotone trace.  The displayed `higher_valley_of_blocker` argument is the
single geometric lemma isolated by this module; it is not hidden in a
proof-data structure. -/
noncomputable def of_noHill_of_higherValleyBlocker
    (hnoBump : ∀ i, (F.trace i).NoBump)
    (hnoCross : F.NoCross)
    (hnoHill : F.NoHill)
    (higher_valley_of_blocker :
      ∀ i : ι, ∀ D : (F.trace i).Valley,
        ∀ j : ι, j ≠ i →
          ¬ Disjoint D.rowInterval.vertexSet (F.column j).vertexSet →
            ∃ E : (F.trace j).Valley, E.rowLower = D.rowTop) :
    F.TerminalGeometry := by
  have hraise :
      ∀ i : ι, ∀ D : (F.trace i).Valley,
        ∃ j : ι, ∃ E : (F.trace j).Valley,
          D.rowTop.1 < E.rowTop.1 := by
    intro i D
    rcases F.exists_blocking_column_of_noHill hnoHill i D with
      ⟨j, hji, hblocked⟩
    rcases higher_valley_of_blocker i D j hji hblocked with ⟨E, hlower⟩
    refine ⟨j, E, ?_⟩
    have hs := E.lower_succ
    rw [hlower] at hs
    omega
  have hnoValley : ∀ i : ι, ¬ Nonempty (F.trace i).Valley :=
    F.noValley_of_strictly_higher hraise
  exact {
    monotoneRows := fun i =>
      (F.trace i).monotoneRows_of_noValley (hnoValley i)
    noBump := hnoBump
    noCross := hnoCross
  }

theorem columnTraceConvex
    (D : F.TerminalGeometry) (i : ι)
    (q : Fin (activeCount + 2)) :
    GraphPathTraceConvex (F.column i) (C.rowPath q).vertexSet :=
  (F.trace i).rowTraceConvex_of_monotoneRows_of_noBump
    (D.monotoneRows i) (D.noBump i) q

theorem rowTraceConvex
    (D : F.TerminalGeometry) (i : ι)
    (q : Fin (activeCount + 2)) :
    GraphPathTraceConvex (C.rowPath q) (F.column i).vertexSet :=
  (F.trace i).rowTraceConvexColumn_of_monotoneRows_of_noBump
    (D.monotoneRows i) (D.noBump i) q

/-- Column-oriented intersection path. -/
noncomputable def columnIntersectionPath
    (D : F.TerminalGeometry) (i : ι)
    (q : Fin (activeCount + 2)) : GraphPath G :=
  (F.trace i).intersectionPath (D.monotoneRows i) (D.noBump i) q

@[simp] theorem columnIntersectionPath_vertexSet
    (D : F.TerminalGeometry) (i : ι)
    (q : Fin (activeCount + 2)) :
    (D.columnIntersectionPath i q).vertexSet =
      (F.column i).vertexSet ∩ (C.rowPath q).vertexSet :=
  (F.trace i).intersectionPath_vertexSet
    (D.monotoneRows i) (D.noBump i) q

/-- Row-oriented intersection path, used for horizontal connectors. -/
noncomputable def rowIntersectionPath
    (D : F.TerminalGeometry) (i : ι)
    (q : Fin (activeCount + 2)) : GraphPath G :=
  (F.trace i).rowIntersectionPath (D.monotoneRows i) (D.noBump i) q

@[simp] theorem rowIntersectionPath_vertexSet
    (D : F.TerminalGeometry) (i : ι)
    (q : Fin (activeCount + 2)) :
    (D.rowIntersectionPath i q).vertexSet =
      (C.rowPath q).vertexSet ∩ (F.column i).vertexSet :=
  (F.trace i).rowIntersectionPath_vertexSet
    (D.monotoneRows i) (D.noBump i) q

theorem commonOrder
    (D : F.TerminalGeometry)
    {i j : ι} (hij : i ≠ j)
    (q r : Fin (activeCount + 2)) :
    (C.rowPath q).Before
        ((F.trace i).contactAtRow q)
        ((F.trace j).contactAtRow q) ↔
      (C.rowPath r).Before
        ((F.trace i).contactAtRow r)
        ((F.trace j).contactAtRow r) :=
  F.common_contactAtRow_order D.monotoneRows D.noBump D.noCross hij q r

end TerminalGeometry

end FullBoundaryColumnFamily

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
