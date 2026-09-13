import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1Valley

namespace Lax17Proofs

universe u v w

/-!
# The concrete hill descent in Chekuri--Chuzhoy Appendix B.1

This module connects the trace-level definition of a hill with the
cycle-erased full-column replacement.  In particular, the replacement input
below is constructed from an actual valley; it is not a semantic hypothesis.
The last part packages the strict non-row-edge decrease into the finite
descent used in Claim B.3.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


open IndexedAuxiliaryPrefix

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {L : PerfectPathPacking G A B} {activeCount : ℕ}
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {C : AuxiliaryCorridor L activeCount}

/-- Two simple graph paths sharing at most one vertex share no edge. -/
theorem graphPath_edgeSet_disjoint_of_inter_subset_singleton
    (P Q : GraphPath G) (v : V)
    (hinter : P.vertexSet ∩ Q.vertexSet ⊆ {v}) :
    Disjoint P.edgeSet Q.edgeSet := by
  classical
  rw [Finset.disjoint_left]
  intro e heP heQ
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxyP := P.endpoints_mem_vertexSet_of_edgeSet heP
      have hxyQ := Q.endpoints_mem_vertexSet_of_edgeSet heQ
      have hxv : x = v := by
        simpa using hinter (Finset.mem_inter.2 ⟨hxyP.1, hxyQ.1⟩)
      have hyv : y = v := by
        simpa using hinter (Finset.mem_inter.2 ⟨hxyP.2, hxyQ.2⟩)
      subst x
      subst y
      have hvv : v ≠ v :=
        G.not_isDiag_of_mem_edgeSet
          (P.edgeSet_subset_edgeSet heP)
      exact hvv rfl

/-- A nontrivial path whose edges all lie on another path has all of its
vertices on that path.  Nontriviality removes the isolated-endpoint exception
that otherwise makes an edge-support statement insufficient. -/
theorem graphPath_vertexSet_subset_of_edgeSet_subset_of_source_ne_target
    (P Q : GraphPath G) (hne : Q.source ≠ Q.target)
    (hedges : Q.edgeSet ⊆ P.edgeSet) :
    Q.vertexSet ⊆ P.vertexSet := by
  classical
  intro v hv
  have hvWalk : v ∈ Q.walk.support := by
    simpa [GraphPath.vertexSet] using hv
  have hnotNil : ¬ Q.walk.Nil :=
    Q.walk_not_nil_of_source_ne_target hne
  rcases
      (_root_.SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
        hnotNil).1 hvWalk with
    ⟨e, heQ, hve⟩
  have heP : e ∈ P.walk.edges := by
    have heQ' : e ∈ Q.edgeSet := by
      simpa [GraphPath.edgeSet] using heQ
    simpa [GraphPath.edgeSet] using hedges heQ'
  have hvP : v ∈ P.walk.support :=
    P.walk.mem_support_of_mem_edges heP hve
  simpa [GraphPath.vertexSet] using hvP

namespace CorridorColumnTrace.StripBridge

variable {P : GraphPath G}
variable {T : CorridorColumnTrace L activeCount C P}
variable {q : Fin (activeCount + 1)}

/-- A clean strip atom shares no edge with any corridor row.  It may meet its
two endpoint rows, but linkage cleanliness restricts each such intersection
to one endpoint, which cannot contain an edge. -/
theorem atom_edgeSet_disjoint_rowPath
    (D : T.StripBridge q) (r : Fin (activeCount + 2)) :
    Disjoint (T.atom D.step).edgeSet (C.rowPath r).edgeSet := by
  classical
  let lower : Fin (activeCount + 2) := ⟨q.1, by omega⟩
  let upper : Fin (activeCount + 2) := ⟨q.1 + 1, by omega⟩
  have hlower_ne_upper : lower ≠ upper := by
    intro h
    have hv := congrArg Fin.val h
    simp [lower, upper] at hv
  have hconnects :
      (T.atom D.step).Connects {D.lower} {D.upper} := by
    rcases D.connects with h | h
    · exact Or.inl ⟨by simpa using h.1, by simpa using h.2⟩
    · exact Or.inr ⟨by simpa using h.1, by simpa using h.2⟩
  let Q : GraphPath G := (T.atom D.step).orientBetween hconnects
  have hQclean :
      Q.InternallyDisjointFromSet L.toPathPacking.vertexSet := by
    intro v hvQ hvL
    have hold :
        (T.atom D.step).IsEndpoint v :=
      T.atom_internallyDisjoint_linkage D.step
        (by
          simpa [Q, GraphPath.orientBetween_vertexSet] using hvQ)
        hvL
    change ((T.atom D.step).orient hconnects).IsEndpoint v
    exact (GraphPath.orient_isEndpoint (T.atom D.step) hconnects).2 hold
  have hQsource : Q.source = D.lower := by simp [Q]
  have hQtarget : Q.target = D.upper := by simp [Q]
  have hresult : Disjoint Q.edgeSet (C.rowPath r).edgeSet := by
    by_cases hrLower : r = lower
    · subst r
      have htargetNot :
          Q.target ∉ (C.rowPath lower).vertexSet := by
        rw [hQtarget]
        intro hupperLower
        exact Finset.disjoint_left.mp
          (C.rowPath_nodeDisjoint hlower_ne_upper)
          hupperLower (by simpa [upper] using D.upper_mem)
      have hinter :
          Q.vertexSet ∩ (C.rowPath lower).vertexSet = {Q.source} := by
        simpa [AuxiliaryCorridor.rowPath, hQsource] using
          inter_linkage_path_eq_singleton_source_of_internallyDisjointFromSet
            (L := L) Q hQclean
            (by simpa [hQsource, lower] using D.lower_mem)
            htargetNot
      exact graphPath_edgeSet_disjoint_of_inter_subset_singleton
        Q (C.rowPath lower) Q.source (by simpa [hinter])
    · by_cases hrUpper : r = upper
      · subst r
        have hsourceNot :
            Q.source ∉ (C.rowPath upper).vertexSet := by
          rw [hQsource]
          intro hlowerUpper
          exact Finset.disjoint_left.mp
            (C.rowPath_nodeDisjoint hlower_ne_upper)
            (by simpa [lower] using D.lower_mem) hlowerUpper
        have hinter :
            Q.vertexSet ∩ (C.rowPath upper).vertexSet = {Q.target} := by
          simpa [AuxiliaryCorridor.rowPath, hQtarget] using
            inter_linkage_path_eq_singleton_target_of_internallyDisjointFromSet
              (L := L) Q hQclean hsourceNot
              (by simpa [hQtarget, upper] using D.upper_mem)
        exact graphPath_edgeSet_disjoint_of_inter_subset_singleton
          Q (C.rowPath upper) Q.target (by simpa [hinter])
      · have hsourceNot :
            Q.source ∉ (C.rowPath r).vertexSet := by
          rw [hQsource]
          intro hmem
          exact Finset.disjoint_left.mp
            (C.rowPath_nodeDisjoint (Ne.symm hrLower))
            (by simpa [lower] using D.lower_mem) hmem
        have htargetNot :
            Q.target ∉ (C.rowPath r).vertexSet := by
          rw [hQtarget]
          intro hmem
          exact Finset.disjoint_left.mp
            (C.rowPath_nodeDisjoint (Ne.symm hrUpper))
            (by simpa [upper] using D.upper_mem) hmem
        have hdisj :
            Disjoint Q.vertexSet (C.rowPath r).vertexSet := by
          simpa [AuxiliaryCorridor.rowPath] using
            disjoint_linkage_path_of_internallyDisjointFromSet
              (L := L) Q hQclean hsourceNot htargetNot
        exact graphPath_edgeSet_disjoint_of_inter_subset_singleton
          Q (C.rowPath r) Q.source (by
            intro x hx
            exact False.elim
              (Finset.disjoint_left.mp hdisj
                (Finset.mem_inter.1 hx).1 (Finset.mem_inter.1 hx).2))
  simpa [Q] using hresult

/-- Consequently a strip atom uses no active-row edge. -/
theorem atom_edgeSet_disjoint_activeEdgeSet
    (D : T.StripBridge q) :
    Disjoint (T.atom D.step).edgeSet C.activeEdgeSet := by
  classical
  rw [AuxiliaryCorridor.activeEdgeSet, Finset.disjoint_left]
  intro e heAtom heRows
  rcases Finset.mem_biUnion.1 heRows with ⟨r, _hr, her⟩
  exact Finset.disjoint_left.mp
    (D.atom_edgeSet_disjoint_rowPath (C.activePosition r))
    heAtom (by
      simpa [AuxiliaryCorridor.activePath, AuxiliaryCorridor.path,
        AuxiliaryCorridor.rowPath] using her)

end CorridorColumnTrace.StripBridge

namespace CorridorColumnTrace.Valley

variable {P : GraphPath G}
variable {T : CorridorColumnTrace L activeCount C P}

/-- The top of a valley is not the lower boundary. -/
theorem rowTop_pos (D : T.Valley) : 0 < D.rowTop.1 := by
  have hs := D.lower_succ
  omega

end CorridorColumnTrace.Valley

namespace FullBoundaryColumnFamily

variable (F : FullBoundaryColumnFamily L activeCount ι C)

/-- The active-row index represented by the top of a valley. -/
def valleyActiveTop
    (i : ι) (D : (F.trace i).Valley) : Fin activeCount :=
  ⟨D.rowTop.1 - 1, by
    have hpos := D.rowTop_pos
    have hlt := F.valley_top_lt_upper i D
    omega⟩

theorem activePosition_valleyActiveTop
    (i : ι) (D : (F.trace i).Valley) :
    C.activePosition (F.valleyActiveTop i D) = D.rowTop := by
  apply Fin.ext
  have hpos := D.rowTop_pos
  simp [AuxiliaryCorridor.activePosition, valleyActiveTop]
  omega

theorem activePath_valleyActiveTop
    (i : ι) (D : (F.trace i).Valley) :
    C.activePath (F.valleyActiveTop i D) = C.rowPath D.rowTop := by
  simp only [AuxiliaryCorridor.activePath, AuxiliaryCorridor.path,
    AuxiliaryCorridor.rowPath]
  rw [F.activePosition_valleyActiveTop i D]

end FullBoundaryColumnFamily

namespace CorridorColumnTrace.Valley

variable {P : GraphPath G}
variable {T : CorridorColumnTrace L activeCount C P}

/-- The top-row interval, oriented in the direction in which the full column
encounters the two top contacts. -/
noncomputable def orientedRowInterval (D : T.Valley) : GraphPath G := by
  classical
  by_cases h :
      (C.rowPath D.rowTop).Before
        (T.contact D.left) (T.contact D.right)
  · exact (C.rowPath D.rowTop).segmentOfBefore h
  · exact
      ((C.rowPath D.rowTop).segmentOfBefore
        (D.top_contacts_order.resolve_left h)).reverse

@[simp] theorem orientedRowInterval_source (D : T.Valley) :
    D.orientedRowInterval.source = T.contact D.left := by
  classical
  simp only [orientedRowInterval]
  split
  · simp
  · simp

@[simp] theorem orientedRowInterval_target (D : T.Valley) :
    D.orientedRowInterval.target = T.contact D.right := by
  classical
  simp only [orientedRowInterval]
  split
  · simp
  · simp

theorem orientedRowInterval_vertexSet_subset_top (D : T.Valley) :
    D.orientedRowInterval.vertexSet ⊆
      (C.rowPath D.rowTop).vertexSet := by
  classical
  simp only [orientedRowInterval]
  split
  · exact (C.rowPath D.rowTop).segmentOfBefore_vertexSet_subset _
  · simpa using
      (C.rowPath D.rowTop).segmentOfBefore_vertexSet_subset
        (D.top_contacts_order.resolve_left ‹_›)

theorem orientedRowInterval_edgeSet_subset_top (D : T.Valley) :
    D.orientedRowInterval.edgeSet ⊆
      (C.rowPath D.rowTop).edgeSet := by
  classical
  simp only [orientedRowInterval]
  split
  · exact (C.rowPath D.rowTop).segmentOfBefore_edgeSet_subset _
  · simpa using
      (C.rowPath D.rowTop).segmentOfBefore_edgeSet_subset
        (D.top_contacts_order.resolve_left ‹_›)

@[simp] theorem orientedRowInterval_vertexSet_eq_rowInterval
    (D : T.Valley) :
    D.orientedRowInterval.vertexSet = D.rowInterval.vertexSet := by
  classical
  simp only [orientedRowInterval, rowInterval]
  split <;> simp_all

@[simp] theorem orientedRowInterval_edgeSet_eq_rowInterval
    (D : T.Valley) :
    D.orientedRowInterval.edgeSet = D.rowInterval.edgeSet := by
  classical
  simp only [orientedRowInterval, rowInterval]
  split <;> simp_all

/-- A valley excursion contains a vertex on its lower row. -/
theorem columnSegment_hits_lower (D : T.Valley) :
    HitsGraphPath D.columnSegment (C.rowPath D.rowLower) := by
  rcases D.hit_lower_strict with ⟨mid, hleft, hright, hrow⟩
  refine ⟨T.contact mid, Finset.mem_inter.2 ⟨?_, ?_⟩⟩
  · apply P.mem_segmentOfBefore_of_before_of_before
      ((T.contact_before_iff_le D.left D.right).2
        (Nat.le_of_lt D.left_lt_right))
    · exact (T.contact_before_iff_le D.left mid).2 (by omega)
    · exact (T.contact_before_iff_le mid D.right).2 (by omega)
  · simpa [hrow] using T.contact_mem_row mid

end CorridorColumnTrace.Valley

namespace FullBoundaryColumnFamily

variable (F : FullBoundaryColumnFamily L activeCount ι C)

/-- The down-and-back part of a valley uses an edge outside the union of the
active rows.  We first obtain an edge outside all corridor rows, which is the
stronger conclusion and also covers a valley reaching a boundary row. -/
theorem valley_exists_edge_not_active
    (i : ι) (D : (F.trace i).Valley) :
    ∃ e : Sym2 V, e ∈ D.columnSegment.edgeSet ∧
      e ∉ C.activeEdgeSet := by
  classical
  have hpairwise :
      Pairwise fun r s : Fin (activeCount + 2) =>
        (C.rowPath r).NodeDisjoint (C.rowPath s) := by
    intro r s hrs
    exact C.rowPath_nodeDisjoint hrs
  rcases
      exists_edge_not_mem_pairwiseRowEdgeUnion_of_hits_other
        C.rowPath hpairwise D.top_ne_lower D.columnSegment
        (by simpa using D.left_mem_top)
        D.columnSegment_hits_lower with
    ⟨e, he, heall⟩
  refine ⟨e, he, ?_⟩
  intro heactive
  apply heall
  rw [AuxiliaryCorridor.activeEdgeSet] at heactive
  rcases Finset.mem_biUnion.1 heactive with ⟨r, _hr, her⟩
  exact C.rowPath_edgeSet_subset_allRowEdgeSet (C.activePosition r)
    (by
      simpa [AuxiliaryCorridor.activePath, AuxiliaryCorridor.path,
        AuxiliaryCorridor.rowPath] using her)

/-- An actual hill is an input to the verified cycle-erased column
replacement, with no additional geometric premise. -/
noncomputable def hillInput
    (i : ι) (D : (F.trace i).Valley) (hHill : F.IsHill i D) :
    FullBoundaryColumnHillInput C.activeEdgeSet F i where
  left := (F.trace i).contact D.left
  right := (F.trace i).contact D.right
  left_mem_column := (F.trace i).contact_mem_column D.left
  right_mem_column := (F.trace i).contact_mem_column D.right
  left_before_right :=
    ((F.trace i).contact_before_iff_le D.left D.right).2
      (Nat.le_of_lt D.left_lt_right)
  rowInterval := D.orientedRowInterval
  rowInterval_source := D.orientedRowInterval_source
  rowInterval_target := D.orientedRowInterval_target
  rowInterval_edgeSet_subset_rows := by
    intro e he
    rw [AuxiliaryCorridor.activeEdgeSet]
    exact Finset.mem_biUnion.2
      ⟨F.valleyActiveTop i D, Finset.mem_univ _, by
        rw [F.activePath_valleyActiveTop i D]
        exact D.orientedRowInterval_edgeSet_subset_top he⟩
  rowInterval_avoids_lowerBoundary := by
    apply Finset.disjoint_of_subset_left
      D.orientedRowInterval_vertexSet_subset_top
    exact C.rowPath_nodeDisjoint (by
      intro heq
      have hval := congrArg Fin.val heq
      exact (Nat.ne_of_gt D.rowTop_pos) (by simpa using hval))
  rowInterval_avoids_upperBoundary := by
    apply Finset.disjoint_of_subset_left
      D.orientedRowInterval_vertexSet_subset_top
    exact C.rowPath_nodeDisjoint (by
      intro heq
      have hval := congrArg Fin.val heq
      have hlt := F.valley_top_lt_upper i D
      simp at hval
      omega)
  rowInterval_avoidsOutside := by
    intro j hj
    apply Finset.disjoint_of_subset_left
      D.orientedRowInterval_vertexSet_subset_top
    simpa [AuxiliaryCorridor.rowPath] using
      L.toPathPacking.node_disjoint (by
        intro heq
        apply hj
        exact ⟨D.rowTop, heq⟩)
  rowInterval_nodeDisjoint_other := by
    intro j hji
    simpa using hHill j hji
  deleted_nonRow_edge := by
    simpa [CorridorColumnTrace.Valley.columnSegment] using
      F.valley_exists_edge_not_active i D

/-- If hill elimination has not terminated, the concrete cycle-erased
replacement strictly decreases the paper's non-row-edge measure. -/
theorem exists_hillReplacement_of_not_noHill
    (hnot : ¬ F.NoHill) :
    ∃ F' : FullBoundaryColumnFamily L activeCount ι C,
      fullColumnNonRowEdgeMeasure C.activeEdgeSet F'.column <
        fullColumnNonRowEdgeMeasure C.activeEdgeSet F.column := by
  classical
  have hex :
      ∃ i : ι, ∃ D : (F.trace i).Valley, F.IsHill i D := by
    by_contra hnone
    apply hnot
    intro i D hhill
    exact hnone ⟨i, D, hhill⟩
  rcases hex with ⟨i, D, hHill⟩
  let H := F.hillInput i D hHill
  exact ⟨H.replacedFamily, H.replacedFamily_nonRowMeasure_strict⟩

/-- Hill elimination terminates at a concrete full-column family. -/
theorem exists_noHillFamily
    (F₀ : FullBoundaryColumnFamily L activeCount ι C) :
    ∃ F : FullBoundaryColumnFamily L activeCount ι C, F.NoHill := by
  classical
  let measure :
      FullBoundaryColumnFamily L activeCount ι C → ℕ :=
    fun F => fullColumnNonRowEdgeMeasure C.activeEdgeSet F.column
  have hstep :
      ∀ F : FullBoundaryColumnFamily L activeCount ι C,
        ¬ F.NoHill →
          False ∨
            ∃ F' : FullBoundaryColumnFamily L activeCount ι C,
              measure F' < measure F := by
    intro F hnot
    exact Or.inr (F.exists_hillReplacement_of_not_noHill hnot)
  rcases
      output_or_exists_terminal_of_nat_descent
        measure
        (fun F : FullBoundaryColumnFamily L activeCount ι C => F.NoHill)
        hstep F₀ with hfalse | hterminal
  · exact False.elim hfalse
  · exact hterminal

/-- The same descent while carrying any invariant proved stable under the
concrete hill replacement.  The later Claim B.3 application instantiates
`Inv` with active bump- and cross-freeness. -/
theorem exists_noHillFamily_preserving
    (Inv : FullBoundaryColumnFamily L activeCount ι C → Prop)
    (F₀ : FullBoundaryColumnFamily L activeCount ι C)
    (hInv₀ : Inv F₀)
    (hpreserve :
      ∀ (F : FullBoundaryColumnFamily L activeCount ι C)
        (i : ι) (D : (F.trace i).Valley) (hHill : F.IsHill i D),
          Inv F → Inv (F.hillInput i D hHill).replacedFamily) :
    ∃ F : FullBoundaryColumnFamily L activeCount ι C,
      Inv F ∧ F.NoHill := by
  classical
  let State :=
    {F : FullBoundaryColumnFamily L activeCount ι C // Inv F}
  let measure : State → ℕ :=
    fun S =>
      fullColumnNonRowEdgeMeasure C.activeEdgeSet S.1.column
  have hstep :
      ∀ S : State, ¬ S.1.NoHill →
        False ∨ ∃ S' : State, measure S' < measure S := by
    intro S hnot
    have hex :
        ∃ i : ι, ∃ D : (S.1.trace i).Valley, S.1.IsHill i D := by
      by_contra hnone
      apply hnot
      intro i D hHill
      exact hnone ⟨i, D, hHill⟩
    rcases hex with ⟨i, D, hHill⟩
    let H := S.1.hillInput i D hHill
    let S' : State :=
      ⟨H.replacedFamily, hpreserve S.1 i D hHill S.2⟩
    exact Or.inr
      ⟨S', by
        simpa [measure, S', H] using
          H.replacedFamily_nonRowMeasure_strict⟩
  rcases
      output_or_exists_terminal_of_nat_descent
        measure
        (fun S : State => S.1.NoHill)
        hstep (⟨F₀, hInv₀⟩ : State) with hfalse | hterminal
  · exact False.elim hfalse
  · rcases hterminal with ⟨S, hnoHill⟩
    exact ⟨S.1, S.2, hnoHill⟩

/-- Every current column uses only edges of its pre-hill column or active
rows.  This support invariant is stable under cycle erasure and is stronger
than the edge statement needed to rule out newly created off-row atoms. -/
def SupportedByColumnsAndActiveRows
    (base : ι → GraphPath G)
    (F : FullBoundaryColumnFamily L activeCount ι C) : Prop :=
  ∀ i : ι,
    (F.column i).edgeSet ⊆
      (base i).edgeSet ∪ C.activeEdgeSet

/-- A clean bridge between consecutive corridor rows cannot use an active-row
edge.  Hence the support invariant identifies the entire bridge with a
subpath of its original pre-hill column. -/
theorem stripBridge_atom_edgeSet_subset_base
    {base : ι → GraphPath G}
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hsupport : SupportedByColumnsAndActiveRows base F)
    (i : ι) {q : Fin (activeCount + 1)}
    (D : (F.trace i).StripBridge q) :
    ((F.trace i).atom D.step).edgeSet ⊆
      (base i).edgeSet := by
  intro e he
  have heColumn :
      e ∈ (F.column i).edgeSet :=
    (F.trace i).atom_edgeSet_subset_column D.step he
  rcases Finset.mem_union.1 (hsupport i heColumn) with heBase | heActive
  · exact heBase
  · exact False.elim
      (Finset.disjoint_left.mp D.atom_edgeSet_disjoint_activeEdgeSet
        he heActive)

/-- Vertex support of the same bridge lies on its original pre-hill column.
The two corridor rows are disjoint, so the bridge is nontrivial and its edge
support determines all of its vertices. -/
theorem stripBridge_atom_vertexSet_subset_base
    {base : ι → GraphPath G}
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (hsupport : SupportedByColumnsAndActiveRows base F)
    (i : ι) {q : Fin (activeCount + 1)}
    (D : (F.trace i).StripBridge q) :
    ((F.trace i).atom D.step).vertexSet ⊆
      (base i).vertexSet := by
  let lowerRow : Fin (activeCount + 2) :=
    ⟨q.1, by omega⟩
  let upperRow : Fin (activeCount + 2) :=
    ⟨q.1 + 1, by omega⟩
  have hrowsNe : lowerRow ≠ upperRow := by
    intro hrows
    have hvals := congrArg Fin.val hrows
    simp [lowerRow, upperRow] at hvals
  have hlowerUpper : D.lower ≠ D.upper := by
    intro hvertices
    exact Finset.disjoint_left.mp
      (C.rowPath_nodeDisjoint hrowsNe)
      (by simpa [lowerRow] using D.lower_mem)
      (by simpa [upperRow, hvertices] using D.upper_mem)
  have hends :
      ((F.trace i).atom D.step).source ≠
        ((F.trace i).atom D.step).target := by
    rcases D.connects with h | h
    · intro heq
      apply hlowerUpper
      exact h.1.symm.trans (heq.trans h.2)
    · intro heq
      apply hlowerUpper
      exact h.2.symm.trans (heq.symm.trans h.1)
  exact
    graphPath_vertexSet_subset_of_edgeSet_subset_of_source_ne_target
      (base i) ((F.trace i).atom D.step) hends
      (F.stripBridge_atom_edgeSet_subset_base hsupport i D)

theorem supportedByColumnsAndActiveRows_refl
    (F : FullBoundaryColumnFamily L activeCount ι C) :
    SupportedByColumnsAndActiveRows F.column F := by
  intro i e he
  exact Finset.mem_union_left _ he

/-- One concrete hill replacement preserves the support invariant relative
to the columns with which the hill phase began. -/
theorem hillInput_supportedByColumnsAndActiveRows
    {base : ι → GraphPath G}
    (F : FullBoundaryColumnFamily L activeCount ι C)
    (i : ι) (D : (F.trace i).Valley) (hHill : F.IsHill i D)
    (hsupport : SupportedByColumnsAndActiveRows base F) :
    SupportedByColumnsAndActiveRows base
      (F.hillInput i D hHill).replacedFamily := by
  classical
  let H := F.hillInput i D hHill
  intro j e he
  by_cases hji : j = i
  · subst j
    have heReplacement : e ∈ H.replacementPath.edgeSet := by
      simpa [FullBoundaryColumnHillInput.replacedFamily,
        replaceFullColumn] using he
    rcases Finset.mem_union.1
        (H.toFullColumnHillInput.replacementPath_edgeSet_subset_old_union_rowInterval
          heReplacement) with heOld | heRowInterval
    · exact hsupport i heOld
    · exact Finset.mem_union_right _
        (H.rowInterval_edgeSet_subset_rows heRowInterval)
  · have heOld : e ∈ (F.column j).edgeSet := by
      simpa [FullBoundaryColumnHillInput.replacedFamily,
        replaceFullColumn, hji] using he
    exact hsupport j heOld

/-- Hill elimination terminates while retaining the exact per-column support
relation to the pre-hill family. -/
theorem exists_noHillFamily_supported
    (F₀ : FullBoundaryColumnFamily L activeCount ι C) :
    ∃ F : FullBoundaryColumnFamily L activeCount ι C,
      SupportedByColumnsAndActiveRows F₀.column F ∧ F.NoHill :=
  F₀.exists_noHillFamily_preserving
    (SupportedByColumnsAndActiveRows F₀.column)
    (supportedByColumnsAndActiveRows_refl F₀)
    (fun F i D hHill hsupport =>
      hillInput_supportedByColumnsAndActiveRows
        F i D hHill hsupport)

end FullBoundaryColumnFamily

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
