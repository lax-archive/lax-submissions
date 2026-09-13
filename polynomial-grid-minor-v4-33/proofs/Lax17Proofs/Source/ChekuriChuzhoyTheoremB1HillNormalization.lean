import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1HillDescent
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1RowDescent

namespace Lax17Proofs

universe u v w

/-!
# Hill normalization preserves the row-normal column geometry

This module supplies the contact-transport argument implicit in
Chekuri--Chuzhoy Appendix B.1.  If hill replacement leaves a clean bridge
supported on its pre-hill column together with active-row edges, cleanliness
removes the active-row edges.  The bridge is then the subpath between two
consecutive linkage contacts of the pre-hill column.
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

/-- A supported strip bridge of the post-hill family is a strip bridge of the
same pre-hill column.  The proof reconstructs its consecutive endpoint
contacts rather than assuming that cycle erasure preserves a contact list. -/
noncomputable def supportedStripBridgeToBase
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (i : ι) {q : Fin (activeCount + 1)}
    (D : (current.trace i).StripBridge q) :
    (base.trace i).StripBridge q := by
  classical
  let Q : GraphPath G := (current.trace i).atom D.step
  let T₀ := base.trace i
  have hQedges : Q.edgeSet ⊆ (base.column i).edgeSet := by
    simpa [Q] using
      current.stripBridge_atom_edgeSet_subset_base hsupport i D
  have hQvertices : Q.vertexSet ⊆ (base.column i).vertexSet := by
    simpa [Q] using
      current.stripBridge_atom_vertexSet_subset_base hsupport i D
  have hlowerQ : D.lower ∈ Q.vertexSet := by
    rcases D.connects with h | h
    · rw [← h.1]
      exact GraphPath.source_mem_vertexSet Q
    · rw [← h.2]
      exact GraphPath.target_mem_vertexSet Q
  have hupperQ : D.upper ∈ Q.vertexSet := by
    rcases D.connects with h | h
    · rw [← h.2]
      exact GraphPath.target_mem_vertexSet Q
    · rw [← h.1]
      exact GraphPath.source_mem_vertexSet Q
  let lowerContact : Fin (T₀.len + 1) :=
    Classical.choose
      (T₀.contact_complete (hQvertices hlowerQ) D.lower_mem)
  have hlowerContact : T₀.contact lowerContact = D.lower :=
    Classical.choose_spec
      (T₀.contact_complete (hQvertices hlowerQ) D.lower_mem)
  let upperContact : Fin (T₀.len + 1) :=
    Classical.choose
      (T₀.contact_complete (hQvertices hupperQ) D.upper_mem)
  have hupperContact : T₀.contact upperContact = D.upper :=
    Classical.choose_spec
      (T₀.contact_complete (hQvertices hupperQ) D.upper_mem)
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
  have hcontactsNe : lowerContact ≠ upperContact := by
    intro h
    apply hlowerUpper
    rw [← hlowerContact, ← hupperContact, h]
  have hQclean :
      Q.InternallyDisjointFromSet L.toPathPacking.vertexSet := by
    simpa [Q] using
      (current.trace i).atom_internallyDisjoint_linkage D.step
  have hconsecutiveOfLt :
      ∀ (a b : Fin (T₀.len + 1)) (x y : V),
        T₀.contact a = x →
        T₀.contact b = y →
        a.1 < b.1 →
        Q.Connects {x} {y} →
        b.1 = a.1 + 1 := by
    intro a b x y hax hby hab hconnects
    by_contra hnot
    have hgap : a.1 + 1 < b.1 := by omega
    let k : Fin (T₀.len + 1) := ⟨a.1 + 1, by omega⟩
    have habBefore : (base.column i).Before x y := by
      simpa [hax, hby] using
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
        R.vertexSet ⊆ (base.column i).vertexSet := by
      exact (base.column i).segmentOfBefore_vertexSet_subset habBefore
    have hRedges :
        R.edgeSet ⊆ (base.column i).edgeSet := by
      exact (base.column i).segmentOfBefore_edgeSet_subset habBefore
    have hRsubsetQ' : R.vertexSet ⊆ Q'.vertexSet := by
      apply GraphPath.vertexSet_subset_of_edgeSet_subset_same_endpoints
        (base.column i) R Q'
        hRvertices hRedges hQ'vertices hQ'edges
      · simp [R, Q', hax]
      · simp [R, Q', hby]
    have hkR : T₀.contact k ∈ R.vertexSet := by
      apply (base.column i).mem_segmentOfBefore_of_before_of_before
        habBefore
      · rw [← hax]
        exact (T₀.contact_before_iff_le a k).2 (by simp [k])
      · rw [← hby]
        exact (T₀.contact_before_iff_le k b).2 (by
          simp [k]
          omega)
    have hkQ' : T₀.contact k ∈ Q'.vertexSet :=
      hRsubsetQ' hkR
    have hkLinkage :
        T₀.contact k ∈ L.toPathPacking.vertexSet := by
      exact (L.toPathPacking.mem_vertexSet).2
        ⟨C.index (T₀.row k), T₀.contact_mem_row k⟩
    have hQ'clean :
        Q'.InternallyDisjointFromSet
          L.toPathPacking.vertexSet := by
      intro v hvQ' hvL
      have hold : Q.IsEndpoint v :=
        hQclean (by
          simpa [Q', GraphPath.orientBetween_vertexSet] using hvQ') hvL
      change (Q.orient hconnects).IsEndpoint v
      exact (GraphPath.orient_isEndpoint Q hconnects).2 hold
    have hend := hQ'clean hkQ' hkLinkage
    rcases hend with hend | hend
    · have hkx : T₀.contact k = x := by
        simpa [Q'] using hend
      have hka : k = a :=
        T₀.contact_injective (hkx.trans hax.symm)
      have hvals := congrArg Fin.val hka
      simp [k] at hvals
    · have hky : T₀.contact k = y := by
        simpa [Q'] using hend
      have hkb : k = b :=
        T₀.contact_injective (hky.trans hby.symm)
      have hvals := congrArg Fin.val hkb
      simp [k] at hvals
      omega
  by_cases hlowerBefore : lowerContact.1 < upperContact.1
  · have hstep :
        upperContact.1 = lowerContact.1 + 1 :=
      hconsecutiveOfLt lowerContact upperContact D.lower D.upper
        hlowerContact hupperContact hlowerBefore D.atom_connects
    let step : Fin T₀.len := ⟨lowerContact.1, by
      have hb := upperContact.2
      omega⟩
    exact
      { step := step
        lower := D.lower
        upper := D.upper
        lower_mem := D.lower_mem
        upper_mem := D.upper_mem
        connects := Or.inl ⟨by
          simpa [step, hlowerContact] using T₀.atom_source step, by
          calc
            (T₀.atom step).target =
                T₀.contact ⟨step.1 + 1, by omega⟩ :=
              T₀.atom_target step
            _ = T₀.contact upperContact := by
              congr 1
              apply Fin.ext
              simp [step, hstep]
            _ = D.upper := hupperContact⟩ }
  · have hupperBefore : upperContact.1 < lowerContact.1 := by
      have hvalsNe : lowerContact.1 ≠ upperContact.1 := by
        intro h
        exact hcontactsNe (Fin.ext h)
      omega
    have hreverseConnects :
        Q.Connects {D.upper} {D.lower} := by
      rcases D.atom_connects with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hstep :
        lowerContact.1 = upperContact.1 + 1 :=
      hconsecutiveOfLt upperContact lowerContact D.upper D.lower
        hupperContact hlowerContact hupperBefore hreverseConnects
    let step : Fin T₀.len := ⟨upperContact.1, by
      have hb := lowerContact.2
      omega⟩
    exact
      { step := step
        lower := D.lower
        upper := D.upper
        lower_mem := D.lower_mem
        upper_mem := D.upper_mem
        connects := Or.inr ⟨by
          simpa [step, hupperContact] using T₀.atom_source step, by
          calc
            (T₀.atom step).target =
                T₀.contact ⟨step.1 + 1, by omega⟩ :=
              T₀.atom_target step
            _ = T₀.contact lowerContact := by
              congr 1
              apply Fin.ext
              simp [step, hstep]
            _ = D.lower := hlowerContact⟩ }

@[simp] theorem supportedStripBridgeToBase_lower
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (i : ι) {q : Fin (activeCount + 1)}
    (D : (current.trace i).StripBridge q) :
    (base.supportedStripBridgeToBase current hsupport i D).lower =
      D.lower := by
  classical
  simp only [supportedStripBridgeToBase]
  split <;> rfl

@[simp] theorem supportedStripBridgeToBase_upper
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (i : ι) {q : Fin (activeCount + 1)}
    (D : (current.trace i).StripBridge q) :
    (base.supportedStripBridgeToBase current hsupport i D).upper =
      D.upper := by
  classical
  simp only [supportedStripBridgeToBase]
  split <;> rfl

/-- Active-strip cross-freeness is preserved by hill elimination.  Both
post-hill bridge atoms transport to the corresponding pre-hill columns with
the same four row endpoints, so a new cross would already have been present
before the hill phase. -/
theorem noActiveCross_of_supported
    (hsupport : SupportedByColumnsAndActiveRows base.column current)
    (hbase : base.NoActiveCross) :
    current.NoActiveCross := by
  classical
  intro X hstripPos hstripLt
  let Xbase : base.Cross :=
    { strip := X.strip
      first := X.first
      second := X.second
      first_ne_second := X.first_ne_second
      firstBridge :=
        base.supportedStripBridgeToBase current hsupport
          X.first X.firstBridge
      secondBridge :=
        base.supportedStripBridgeToBase current hsupport
          X.second X.secondBridge
      lower_reversed := by
        simpa using X.lower_reversed
      upper_reversed := by
        simpa using X.upper_reversed }
  exact hbase Xbase hstripPos hstripLt

end FullBoundaryColumnFamily

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
