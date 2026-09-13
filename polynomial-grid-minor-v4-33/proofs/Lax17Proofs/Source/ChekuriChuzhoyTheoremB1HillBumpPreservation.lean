import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1HillNormalization

namespace Lax17Proofs

universe u v w

/-!
# Hill normalization preserves active bump-freeness

Chekuri--Chuzhoy Appendix B.1 keeps the rows fixed during hill elimination.
The cycle-erased columns may acquire row edges, but a new clean bump cannot
use one: cleanliness forces both endpoints of such an edge to be the atom
endpoints, making the atom a one-edge path and contradicting its stored
off-row edge.  The remaining atom is supported on the corresponding pre-hill
column and reconstructs a pre-hill bump.
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

namespace FullBoundaryColumnFamily

variable
    (base current : FullBoundaryColumnFamily L activeCount ι C)

/-- A bump atom is nontrivial because it contains its stored off-row edge. -/
theorem bump_atom_source_ne_target
    (i : ι) (D : (current.trace i).Bump) :
    ((current.trace i).atom D.step).source ≠
      ((current.trace i).atom D.step).target := by
  classical
  let Q := (current.trace i).atom D.step
  intro hst
  have hfst :
      D.off_row_edge.out.1 ∈ Q.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet D.off_row_edge_mem
      (Sym2.out_fst_mem D.off_row_edge)
  have hsnd :
      D.off_row_edge.out.2 ∈ Q.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet D.off_row_edge_mem
      (Sym2.out_snd_mem D.off_row_edge)
  have hfstEq : D.off_row_edge.out.1 = Q.source :=
    Q.eq_source_of_source_eq_target_of_mem_vertexSet hst hfst
  have hsndEq : D.off_row_edge.out.2 = Q.source :=
    Q.eq_source_of_source_eq_target_of_mem_vertexSet hst hsnd
  have heG : D.off_row_edge ∈ G.edgeSet :=
    Q.edgeSet_subset_edgeSet D.off_row_edge_mem
  have hadj :
      G.Adj D.off_row_edge.out.1 D.off_row_edge.out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, D.off_row_edge.out_eq] using heG
  have hne : D.off_row_edge.out.1 ≠ D.off_row_edge.out.2 :=
    hadj.ne
  exact hne (hfstEq.trans hsndEq.symm)

/-- A clean bump atom shares no edge with the union of active linkage rows. -/
theorem bump_atom_edgeSet_disjoint_activeEdgeSet
    (i : ι) (D : (current.trace i).Bump) :
    Disjoint ((current.trace i).atom D.step).edgeSet
      C.activeEdgeSet := by
  classical
  let T := current.trace i
  let Q := T.atom D.step
  let cur : Fin (T.len + 1) := ⟨D.step.1, by omega⟩
  let nxt : Fin (T.len + 1) := ⟨D.step.1 + 1, by omega⟩
  let rowQ : Fin (activeCount + 2) := T.row cur
  have hQsource : Q.source = T.contact cur := by
    simpa [Q, T, cur] using T.atom_source D.step
  have hQtarget : Q.target = T.contact nxt := by
    simpa [Q, T, nxt] using T.atom_target D.step
  have hsourceRow : Q.source ∈ (C.rowPath rowQ).vertexSet := by
    rw [hQsource]
    simpa [rowQ, cur] using T.contact_mem_row cur
  have htargetRow : Q.target ∈ (C.rowPath rowQ).vertexSet := by
    rw [hQtarget]
    have hmem := T.contact_mem_row nxt
    have hsame : T.row nxt = rowQ := by
      simpa [rowQ, cur, nxt] using D.same_row.symm
    simpa [hsame] using hmem
  have hclean :
      Q.InternallyDisjointFromSet L.toPathPacking.vertexSet := by
    simpa [Q, T] using T.atom_internallyDisjoint_linkage D.step
  rw [AuxiliaryCorridor.activeEdgeSet, Finset.disjoint_left]
  intro e heQ heActive
  rcases Finset.mem_biUnion.1 heActive with ⟨r, _hr, her⟩
  let R : GraphPath G := C.activePath r
  have hfstQ :
      e.out.1 ∈ Q.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet heQ (Sym2.out_fst_mem e)
  have hsndQ :
      e.out.2 ∈ Q.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet heQ (Sym2.out_snd_mem e)
  have hfstR :
      e.out.1 ∈ R.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet her (Sym2.out_fst_mem e)
  have hsndR :
      e.out.2 ∈ R.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet her (Sym2.out_snd_mem e)
  have hfstL :
      e.out.1 ∈ L.toPathPacking.vertexSet := by
    exact (L.toPathPacking.mem_vertexSet).2
      ⟨C.index (C.activePosition r), by
        simpa [R, AuxiliaryCorridor.activePath, AuxiliaryCorridor.path,
          AuxiliaryCorridor.rowPath] using hfstR⟩
  have hsndL :
      e.out.2 ∈ L.toPathPacking.vertexSet := by
    exact (L.toPathPacking.mem_vertexSet).2
      ⟨C.index (C.activePosition r), by
        simpa [R, AuxiliaryCorridor.activePath, AuxiliaryCorridor.path,
          AuxiliaryCorridor.rowPath] using hsndR⟩
  have hfstEnd : Q.IsEndpoint e.out.1 := hclean hfstQ hfstL
  have hsndEnd : Q.IsEndpoint e.out.2 := hclean hsndQ hsndL
  have heG : e ∈ G.edgeSet := Q.edgeSet_subset_edgeSet heQ
  have hadj : G.Adj e.out.1 e.out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, e.out_eq] using heG
  have heEnds : e = s(Q.source, Q.target) := by
    rw [← e.out_eq, Sym2.eq_iff]
    rcases hfstEnd with hfs | hft <;>
        rcases hsndEnd with hss | hst
    · exact False.elim (hadj.ne (hfs.trans hss.symm))
    · exact Or.inl ⟨hfs, hst⟩
    · exact Or.inr ⟨hft, hss⟩
    · exact False.elim (hadj.ne (hft.trans hst.symm))
  have hlenLe : Q.walk.length ≤ 1 := by
    have hindex :=
      Q.edge_vertexIndex_le_succ
        (u := Q.source) (v := Q.target) (by simpa [heEnds] using heQ)
    simpa using hindex
  have hcardPos : 0 < Q.edgeSet.card :=
    Finset.card_pos.2 ⟨e, heQ⟩
  have hlenPos : 0 < Q.walk.length := by
    simpa using hcardPos
  have hlen : Q.walk.length = 1 := by omega
  have hcard : Q.edgeSet.card = 1 := by
    simpa [GraphPath.edgeSet_card, hlen]
  rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
  have hoffQ : D.off_row_edge ∈ Q.edgeSet := by
    simpa [Q, T] using D.off_row_edge_mem
  have heQ' : e ∈ Q.edgeSet := by
    simpa [Q, T] using heQ
  have hoffA : D.off_row_edge = a := by
    simpa [ha] using hoffQ
  have heA : e = a := by
    simpa [ha] using heQ'
  have hoffEq : D.off_row_edge = e := hoffA.trans heA.symm
  have hsourceR : Q.source ∈ R.vertexSet := by
    have hedge : s(Q.source, Q.target) ∈ R.edgeSet := by
      simpa [heEnds] using her
    exact (R.endpoints_mem_vertexSet_of_edgeSet hedge).1
  have hrowEq : C.activePosition r = rowQ := by
    have hmem :
        T.contact cur ∈
          (C.rowPath (C.activePosition r)).vertexSet := by
      rw [← hQsource]
      simpa [R, AuxiliaryCorridor.activePath, AuxiliaryCorridor.path,
        AuxiliaryCorridor.rowPath] using hsourceR
    exact T.contact_row_unique cur (C.activePosition r) hmem
  have heRow :
      e ∈ (C.rowPath rowQ).edgeSet := by
    simpa [R, AuxiliaryCorridor.activePath, AuxiliaryCorridor.path,
      AuxiliaryCorridor.rowPath, hrowEq] using her
  exact D.off_row_edge_not_mem (by simpa [hoffEq] using heRow)

/-- Under the support invariant, every edge of a current bump atom lies on
the corresponding pre-hill column. -/
theorem bump_atom_edgeSet_subset_base
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (i : ι) (D : (current.trace i).Bump) :
    ((current.trace i).atom D.step).edgeSet ⊆
      (base.column i).edgeSet := by
  intro e he
  have heColumn :
      e ∈ (current.column i).edgeSet :=
    (current.trace i).atom_edgeSet_subset_column D.step he
  rcases Finset.mem_union.1 (hsupport i heColumn) with heBase | heActive
  · exact heBase
  · exact False.elim
      (Finset.disjoint_left.mp
        (current.bump_atom_edgeSet_disjoint_activeEdgeSet i D)
        he heActive)

/-- The same atom's vertices lie on its pre-hill column. -/
theorem bump_atom_vertexSet_subset_base
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (i : ι) (D : (current.trace i).Bump) :
    ((current.trace i).atom D.step).vertexSet ⊆
      (base.column i).vertexSet :=
  graphPath_vertexSet_subset_of_edgeSet_subset_of_source_ne_target
    (base.column i) ((current.trace i).atom D.step)
    (current.bump_atom_source_ne_target i D)
    (base.bump_atom_edgeSet_subset_base current hsupport i D)

/-- If every vertex of a nontrivial path is one of its endpoints, every path
edge is the unordered endpoint edge. -/
theorem edge_eq_source_target_of_vertexSet_subset_endpoints
    (P : GraphPath G) (hne : P.source ≠ P.target)
    (hvertices :
      P.vertexSet ⊆ ({P.source, P.target} : Finset V))
    {e : Sym2 V} (he : e ∈ P.edgeSet) :
    e = s(P.source, P.target) := by
  classical
  have hfstMem :
      e.out.1 ∈ P.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet he (Sym2.out_fst_mem e)
  have hsndMem :
      e.out.2 ∈ P.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet he (Sym2.out_snd_mem e)
  have hfst :
      e.out.1 = P.source ∨ e.out.1 = P.target := by
    simpa using hvertices hfstMem
  have hsnd :
      e.out.2 = P.source ∨ e.out.2 = P.target := by
    simpa using hvertices hsndMem
  have heG : e ∈ G.edgeSet := P.edgeSet_subset_edgeSet he
  have hadj : G.Adj e.out.1 e.out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, e.out_eq] using heG
  rw [← e.out_eq, Sym2.eq_iff]
  rcases hfst with hfs | hft <;> rcases hsnd with hss | hst
  · exact False.elim (hadj.ne (hfs.trans hss.symm))
  · exact Or.inl ⟨hfs, hst⟩
  · exact Or.inr ⟨hft, hss⟩
  · exact False.elim (hadj.ne (hft.trans hst.symm))

/-- Once the current bump atom has been identified with a simple subpath of
the base column, the corresponding consecutive base atom still contains an
edge outside the common row. -/
theorem exists_base_atom_off_row_edge
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (i : ι) (D : (current.trace i).Bump)
    (step : Fin (base.trace i).len)
    (hconnects :
      ((current.trace i).atom D.step).Connects
        {((base.trace i).atom step).source}
        {((base.trace i).atom step).target}) :
    ∃ e : Sym2 V,
      e ∈ ((base.trace i).atom step).edgeSet ∧
        e ∉
          (C.rowPath
            ((current.trace i).row
              ⟨D.step.1, by omega⟩)).edgeSet := by
  classical
  let T := current.trace i
  let T₀ := base.trace i
  let Q : GraphPath G := T.atom D.step
  let R : GraphPath G := T₀.atom step
  let Q' : GraphPath G := Q.orientBetween hconnects
  let rowQ : Fin (activeCount + 2) :=
    T.row ⟨D.step.1, by omega⟩
  have hQedges : Q.edgeSet ⊆ (base.column i).edgeSet :=
    base.bump_atom_edgeSet_subset_base current hsupport i D
  have hQvertices : Q.vertexSet ⊆ (base.column i).vertexSet :=
    base.bump_atom_vertexSet_subset_base current hsupport i D
  have hQ'edges : Q'.edgeSet ⊆ (base.column i).edgeSet := by
    simpa [Q', GraphPath.orientBetween_edgeSet] using hQedges
  have hQ'vertices : Q'.vertexSet ⊆ (base.column i).vertexSet := by
    simpa [Q', GraphPath.orientBetween_vertexSet] using hQvertices
  have hRedges : R.edgeSet ⊆ (base.column i).edgeSet := by
    simpa [R, T₀] using T₀.atom_edgeSet_subset_column step
  have hRvertices : R.vertexSet ⊆ (base.column i).vertexSet := by
    simpa [R, T₀] using T₀.atom_vertexSet_subset_column step
  have hQ'source : Q'.source = R.source := by
    change (Q.orientBetween hconnects).source = R.source
    exact GraphPath.orientBetween_source Q hconnects
  have hQ'target : Q'.target = R.target := by
    change (Q.orientBetween hconnects).target = R.target
    exact GraphPath.orientBetween_target Q hconnects
  have hRne : R.source ≠ R.target := by
    intro heq
    let a : Fin (T₀.len + 1) := ⟨step.1, by omega⟩
    let b : Fin (T₀.len + 1) := ⟨step.1 + 1, by omega⟩
    have hab : a ≠ b := by
      intro heq'
      have hval := congrArg Fin.val heq'
      simp [a, b] at hval
    apply hab
    apply T₀.contact_injective
    simpa [R, T₀, a, b] using heq
  have hQ'ne : Q'.source ≠ Q'.target := by
    simpa [hQ'source, hQ'target] using hRne
  have hQ'subsetR : Q'.vertexSet ⊆ R.vertexSet := by
    apply GraphPath.vertexSet_subset_of_edgeSet_subset_same_endpoints
      (base.column i) Q' R hQ'vertices hQ'edges hRvertices hRedges
    · exact hQ'source
    · exact hQ'target
  have hRsubsetQ' : R.vertexSet ⊆ Q'.vertexSet := by
    apply GraphPath.vertexSet_subset_of_edgeSet_subset_same_endpoints
      (base.column i) R Q' hRvertices hRedges hQ'vertices hQ'edges
    · exact hQ'source.symm
    · exact hQ'target.symm
  by_contra hnone
  have hRrow : R.edgeSet ⊆ (C.rowPath rowQ).edgeSet := by
    intro e he
    by_contra hnot
    exact hnone ⟨e, he, hnot⟩
  have hRverticesRow : R.vertexSet ⊆ (C.rowPath rowQ).vertexSet :=
    graphPath_vertexSet_subset_of_edgeSet_subset_of_source_ne_target
      (C.rowPath rowQ) R hRne hRrow
  have hQ'verticesRow :
      Q'.vertexSet ⊆ (C.rowPath rowQ).vertexSet :=
    fun v hv => hRverticesRow (hQ'subsetR hv)
  have hQ'clean :
      Q'.InternallyDisjointFromSet L.toPathPacking.vertexSet := by
    intro v hvQ' hvL
    have hold : Q.IsEndpoint v :=
      T.atom_internallyDisjoint_linkage D.step
        (by
          simpa [Q', GraphPath.orientBetween_vertexSet] using hvQ') hvL
    change (Q.orient hconnects).IsEndpoint v
    exact (GraphPath.orient_isEndpoint Q hconnects).2 hold
  have hQ'verticesEndpoints :
      Q'.vertexSet ⊆ ({Q'.source, Q'.target} : Finset V) := by
    intro v hv
    have hvL : v ∈ L.toPathPacking.vertexSet := by
      exact (L.toPathPacking.mem_vertexSet).2
        ⟨C.index rowQ, hQ'verticesRow hv⟩
    simpa [GraphPath.IsEndpoint] using hQ'clean hv hvL
  have hRverticesEndpoints :
      R.vertexSet ⊆ ({R.source, R.target} : Finset V) := by
    intro v hv
    have hvQ' := hRsubsetQ' hv
    have hend := hQ'verticesEndpoints hvQ'
    simpa [hQ'source, hQ'target] using hend
  have hoffQ' :
      D.off_row_edge ∈ Q'.edgeSet := by
    simpa [Q', Q, GraphPath.orientBetween_edgeSet] using
      D.off_row_edge_mem
  have hoffEq :
      D.off_row_edge = s(Q'.source, Q'.target) :=
    edge_eq_source_target_of_vertexSet_subset_endpoints
      Q' hQ'ne hQ'verticesEndpoints hoffQ'
  rcases R.edgeSet_nonempty_of_source_ne_target hRne with ⟨e, heR⟩
  have heEq :
      e = s(R.source, R.target) :=
    edge_eq_source_target_of_vertexSet_subset_endpoints
      R hRne hRverticesEndpoints heR
  have hoffER : D.off_row_edge = e := by
    calc
      D.off_row_edge = s(Q'.source, Q'.target) := hoffEq
      _ = s(R.source, R.target) := by rw [hQ'source, hQ'target]
      _ = e := heEq.symm
  exact D.off_row_edge_not_mem
    (by simpa [rowQ, hoffER] using hRrow heR)

/-- A current bump supported by its pre-hill column and the active rows
reconstructs a bump of that pre-hill column.  The returned equality identifies
the two bump rows and therefore transports active-row bounds. -/
theorem supportedBumpToBase
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (i : ι) (D : (current.trace i).Bump) :
    ∃ D₀ : (base.trace i).Bump,
      (base.trace i).row ⟨D₀.step.1, by omega⟩ =
        (current.trace i).row ⟨D.step.1, by omega⟩ := by
  classical
  let T := current.trace i
  let T₀ := base.trace i
  let Q : GraphPath G := T.atom D.step
  let cur : Fin (T.len + 1) := ⟨D.step.1, by omega⟩
  let nxt : Fin (T.len + 1) := ⟨D.step.1 + 1, by omega⟩
  let x : V := T.contact cur
  let y : V := T.contact nxt
  let rowQ : Fin (activeCount + 2) := T.row cur
  have hQsource : Q.source = x := by
    simpa [Q, T, x, cur] using T.atom_source D.step
  have hQtarget : Q.target = y := by
    simpa [Q, T, y, nxt] using T.atom_target D.step
  have hxQ : x ∈ Q.vertexSet := by
    rw [← hQsource]
    exact Q.source_mem_vertexSet
  have hyQ : y ∈ Q.vertexSet := by
    rw [← hQtarget]
    exact Q.target_mem_vertexSet
  have hxRow : x ∈ (C.rowPath rowQ).vertexSet := by
    simpa [x, rowQ, cur] using T.contact_mem_row cur
  have hyRow : y ∈ (C.rowPath rowQ).vertexSet := by
    have hmem := T.contact_mem_row nxt
    have hsame : T.row nxt = rowQ := by
      simpa [rowQ, cur, nxt] using D.same_row.symm
    simpa [y, hsame] using hmem
  have hQedges : Q.edgeSet ⊆ (base.column i).edgeSet := by
    simpa [Q, T] using
      base.bump_atom_edgeSet_subset_base current hsupport i D
  have hQvertices : Q.vertexSet ⊆ (base.column i).vertexSet := by
    simpa [Q, T] using
      base.bump_atom_vertexSet_subset_base current hsupport i D
  let xContact : Fin (T₀.len + 1) :=
    Classical.choose (T₀.contact_complete (hQvertices hxQ) hxRow)
  have hxContact : T₀.contact xContact = x :=
    Classical.choose_spec (T₀.contact_complete (hQvertices hxQ) hxRow)
  let yContact : Fin (T₀.len + 1) :=
    Classical.choose (T₀.contact_complete (hQvertices hyQ) hyRow)
  have hyContact : T₀.contact yContact = y :=
    Classical.choose_spec (T₀.contact_complete (hQvertices hyQ) hyRow)
  have hxy : x ≠ y := by
    intro h
    apply current.bump_atom_source_ne_target i D
    exact hQsource.trans (h.trans hQtarget.symm)
  have hcontactsNe : xContact ≠ yContact := by
    intro h
    apply hxy
    rw [← hxContact, h, hyContact]
  have hQclean :
      Q.InternallyDisjointFromSet L.toPathPacking.vertexSet := by
    simpa [Q, T] using T.atom_internallyDisjoint_linkage D.step
  have hQconnects :
      Q.Connects {x} {y} :=
    Or.inl
      ⟨by simpa using hQsource,
        by simpa using hQtarget⟩
  have hconsecutiveOfLt :
      ∀ (a b : Fin (T₀.len + 1)) (u v : V),
        T₀.contact a = u →
        T₀.contact b = v →
        a.1 < b.1 →
        Q.Connects {u} {v} →
        b.1 = a.1 + 1 := by
    intro a b u v hau hbv hab hconnects
    by_contra hnot
    have hgap : a.1 + 1 < b.1 := by omega
    let k : Fin (T₀.len + 1) := ⟨a.1 + 1, by omega⟩
    have habBefore : (base.column i).Before u v := by
      simpa [hau, hbv] using
        (T₀.contact_before_iff_le a b).2 (Nat.le_of_lt hab)
    let R : GraphPath G :=
      (base.column i).segmentOfBefore habBefore
    let Q' : GraphPath G := Q.orientBetween hconnects
    have hQ'vertices :
        Q'.vertexSet ⊆ (base.column i).vertexSet := by
      simpa [Q', GraphPath.orientBetween_vertexSet] using hQvertices
    have hQ'edges :
        Q'.edgeSet ⊆ (base.column i).edgeSet := by
      simpa [Q', GraphPath.orientBetween_edgeSet] using hQedges
    have hRvertices :
        R.vertexSet ⊆ (base.column i).vertexSet :=
      (base.column i).segmentOfBefore_vertexSet_subset habBefore
    have hRedges :
        R.edgeSet ⊆ (base.column i).edgeSet :=
      (base.column i).segmentOfBefore_edgeSet_subset habBefore
    have hRsubsetQ' : R.vertexSet ⊆ Q'.vertexSet := by
      apply GraphPath.vertexSet_subset_of_edgeSet_subset_same_endpoints
        (base.column i) R Q'
        hRvertices hRedges hQ'vertices hQ'edges
      · simp [R, Q', hau]
      · simp [R, Q', hbv]
    have hkR : T₀.contact k ∈ R.vertexSet := by
      apply (base.column i).mem_segmentOfBefore_of_before_of_before
        habBefore
      · rw [← hau]
        exact (T₀.contact_before_iff_le a k).2 (by simp [k])
      · rw [← hbv]
        exact (T₀.contact_before_iff_le k b).2 (by
          simp [k]
          omega)
    have hkQ' : T₀.contact k ∈ Q'.vertexSet :=
      hRsubsetQ' hkR
    have hkLinkage :
        T₀.contact k ∈ L.toPathPacking.vertexSet :=
      (L.toPathPacking.mem_vertexSet).2
        ⟨C.index (T₀.row k), T₀.contact_mem_row k⟩
    have hQ'clean :
        Q'.InternallyDisjointFromSet
          L.toPathPacking.vertexSet := by
      intro z hzQ' hzL
      have hold : Q.IsEndpoint z :=
        hQclean (by
          simpa [Q', GraphPath.orientBetween_vertexSet] using hzQ') hzL
      change (Q.orient hconnects).IsEndpoint z
      exact (GraphPath.orient_isEndpoint Q hconnects).2 hold
    have hend := hQ'clean hkQ' hkLinkage
    rcases hend with hend | hend
    · have hku : T₀.contact k = u := by
        simpa [Q'] using hend
      have hka : k = a :=
        T₀.contact_injective (hku.trans hau.symm)
      have hvals := congrArg Fin.val hka
      simp [k] at hvals
    · have hkv : T₀.contact k = v := by
        simpa [Q'] using hend
      have hkb : k = b :=
        T₀.contact_injective (hkv.trans hbv.symm)
      have hvals := congrArg Fin.val hkb
      simp [k] at hvals
      omega
  have hxBaseRow : rowQ = T₀.row xContact :=
    T₀.contact_row_unique xContact rowQ (by simpa [hxContact] using hxRow)
  have hyBaseRow : rowQ = T₀.row yContact :=
    T₀.contact_row_unique yContact rowQ (by simpa [hyContact] using hyRow)
  by_cases hxyOrder : xContact.1 < yContact.1
  · have hstep :
        yContact.1 = xContact.1 + 1 :=
      hconsecutiveOfLt xContact yContact x y
        hxContact hyContact hxyOrder hQconnects
    let step : Fin T₀.len := ⟨xContact.1, by
      have hb := yContact.2
      omega⟩
    let R : GraphPath G := T₀.atom step
    have hRsource : R.source = x := by
      simpa [R, step, hxContact] using T₀.atom_source step
    have hRtarget : R.target = y := by
      calc
        R.target = T₀.contact ⟨step.1 + 1, by omega⟩ := by
          simpa [R] using T₀.atom_target step
        _ = T₀.contact yContact := by
          congr 1
          apply Fin.ext
          simp [step, hstep]
        _ = y := hyContact
    have hconnects : Q.Connects {R.source} {R.target} :=
      Or.inl
        ⟨by simpa using hQsource.trans hRsource.symm,
          by simpa using hQtarget.trans hRtarget.symm⟩
    rcases base.exists_base_atom_off_row_edge current hsupport i D
        step hconnects with ⟨e, heR, heNotRow⟩
    have hsame :
        T₀.row ⟨step.1, by omega⟩ =
          T₀.row ⟨step.1 + 1, by omega⟩ := by
      have hrows : T₀.row xContact = T₀.row yContact :=
        hxBaseRow.symm.trans hyBaseRow
      have hcur :
          (⟨step.1, by omega⟩ : Fin (T₀.len + 1)) = xContact := by
        apply Fin.ext
        simp [step]
      have hnxt :
          (⟨step.1 + 1, by omega⟩ : Fin (T₀.len + 1)) =
            yContact := by
        apply Fin.ext
        simp [step, hstep]
      rw [hcur, hnxt]
      exact hrows
    let D₀ : T₀.Bump := {
      step := step
      same_row := hsame
      off_row_edge := e
      off_row_edge_mem := heR
      off_row_edge_not_mem := by
        have hbaseRow :
            T₀.row ⟨step.1, by omega⟩ = rowQ := by
          simpa [step] using hxBaseRow.symm
        simpa [hbaseRow, rowQ, cur] using heNotRow
    }
    refine ⟨D₀, ?_⟩
    simpa [D₀, step, rowQ, cur] using hxBaseRow.symm
  · have hyxOrder : yContact.1 < xContact.1 := by
      have hvalsNe : xContact.1 ≠ yContact.1 := by
        intro h
        exact hcontactsNe (Fin.ext h)
      omega
    have hreverseConnects :
        Q.Connects {y} {x} := by
      rcases hQconnects with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hstep :
        xContact.1 = yContact.1 + 1 :=
      hconsecutiveOfLt yContact xContact y x
        hyContact hxContact hyxOrder hreverseConnects
    let step : Fin T₀.len := ⟨yContact.1, by
      have hb := xContact.2
      omega⟩
    let R : GraphPath G := T₀.atom step
    have hRsource : R.source = y := by
      simpa [R, step, hyContact] using T₀.atom_source step
    have hRtarget : R.target = x := by
      calc
        R.target = T₀.contact ⟨step.1 + 1, by omega⟩ := by
          simpa [R] using T₀.atom_target step
        _ = T₀.contact xContact := by
          congr 1
          apply Fin.ext
          simp [step, hstep]
        _ = x := hxContact
    have hconnects : Q.Connects {R.source} {R.target} :=
      Or.inr
        ⟨by simpa using hQsource.trans hRtarget.symm,
          by simpa using hQtarget.trans hRsource.symm⟩
    rcases base.exists_base_atom_off_row_edge current hsupport i D
        step hconnects with ⟨e, heR, heNotRow⟩
    have hsame :
        T₀.row ⟨step.1, by omega⟩ =
          T₀.row ⟨step.1 + 1, by omega⟩ := by
      have hrows : T₀.row yContact = T₀.row xContact :=
        hyBaseRow.symm.trans hxBaseRow
      have hcur :
          (⟨step.1, by omega⟩ : Fin (T₀.len + 1)) = yContact := by
        apply Fin.ext
        simp [step]
      have hnxt :
          (⟨step.1 + 1, by omega⟩ : Fin (T₀.len + 1)) =
            xContact := by
        apply Fin.ext
        simp [step, hstep]
      rw [hcur, hnxt]
      exact hrows
    let D₀ : T₀.Bump := {
      step := step
      same_row := hsame
      off_row_edge := e
      off_row_edge_mem := heR
      off_row_edge_not_mem := by
        have hbaseRow :
            T₀.row ⟨step.1, by omega⟩ = rowQ := by
          simpa [step] using hyBaseRow.symm
        simpa [hbaseRow, rowQ, cur] using heNotRow
    }
    refine ⟨D₀, ?_⟩
    simpa [D₀, step, rowQ, cur] using hyBaseRow.symm

/-- Active bump-freeness is inherited by every post-hill family whose
columns remain supported on their original columns and the fixed active
rows. -/
theorem noActiveBump_of_supported
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (hbase : ∀ i : ι, (base.trace i).NoActiveBump) :
    ∀ i : ι, (current.trace i).NoActiveBump := by
  intro i D hpos hlt
  rcases base.supportedBumpToBase current hsupport i D with
    ⟨D₀, hrow⟩
  exact hbase i D₀
    (by simpa [hrow] using hpos)
    (by simpa [hrow] using hlt)

/-- Boundary-contact uniqueness upgrades transported active bump-freeness to
full bump-freeness for the boundary-to-boundary column family. -/
theorem noBump_of_supported_noActiveBump
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (hbase : ∀ i : ι, (base.trace i).NoActiveBump) :
    ∀ i : ι, (current.trace i).NoBump := by
  intro i
  exact current.trace_noBump_of_noActiveBump i
    (base.noActiveBump_of_supported current hsupport hbase i)

end FullBoundaryColumnFamily

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
