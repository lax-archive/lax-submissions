import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1InitialColumns
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1Measures

namespace Lax17Proofs

universe u v w

/-!
# Common row-rerouting state for Theorem B.1

The paper's type-one and type-two branches use the same rerouting argument on
different subintervals of the displayed auxiliary two-path.  This state keeps
exactly the common information:

* the current `A`--`B` linkage;
* an auxiliary-graph isomorphism back to the linkage with which the branch
  started;
* the ordered degree-two corridor, including its outside neighbours;
* one fixed family of full boundary-to-boundary columns.

The columns are parameters of the state, so bump/cross rerouting cannot
silently replace them.  They are changed only in the later hill-elimination
state.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

open IndexedAuxiliaryPrefix

/-- A linkage together with an ordered corridor and a fixed column family. -/
structure CorridorRowState
    (original : PerfectPathPacking G A B) (activeCount : ℕ)
    (ι : Type w) (fixedColumn : ι → GraphPath G) where
  originalCorridor : AuxiliaryCorridor original activeCount
  linkage : PerfectPathPacking G A B
  auxEquiv : original.Index ≃ linkage.Index
  auxAdj_iff :
    ∀ i j : original.Index,
      (linkageAuxGraph original).Adj i j ↔
        (linkageAuxGraph linkage).Adj (auxEquiv i) (auxEquiv j)
  corridor : AuxiliaryCorridor linkage activeCount
  corridor_index_eq :
    ∀ k, corridor.index k = auxEquiv (originalCorridor.index k)
  columns :
    FullBoundaryColumnFamily linkage activeCount ι corridor
  column_eq : columns.column = fixedColumn

namespace CorridorRowState

variable {original : PerfectPathPacking G A B}
variable {activeCount : ℕ} {ι : Type w}
variable {fixedColumn : ι → GraphPath G}

/-- The explicit equivalence fields give the ordinary auxiliary-isomorphism
proposition used by the existing degree-count API. -/
theorem auxIso
    (S : CorridorRowState original activeCount ι fixedColumn) :
    AuxGraphsIsomorphic original S.linkage :=
  ⟨S.auxEquiv, S.auxAdj_iff⟩

/-- The fixed union of column edges used by the row descent measure. -/
noncomputable def fixedColumnEdgeSet [Fintype ι]
    (S : CorridorRowState original activeCount ι fixedColumn) :
    Finset (Sym2 V) :=
  Finset.univ.biUnion fun i : ι => (fixedColumn i).edgeSet

/-- The paper's first measure: active-row edges outside the fixed columns. -/
noncomputable def rowMeasure [Fintype ι]
    (S : CorridorRowState original activeCount ι fixedColumn) : ℕ :=
  outsideFixedMeasure S.corridor.activeEdgeSet S.fixedColumnEdgeSet

/-- The stored column family really uses the fixed paths. -/
theorem column_eq_fixed
    (S : CorridorRowState original activeCount ι fixedColumn) (i : ι) :
    S.columns.column i = fixedColumn i := by
  exact congrFun S.column_eq i

/-- Every fixed column meets every current corridor row. -/
theorem fixedColumn_hits_every_row
    (S : CorridorRowState original activeCount ι fixedColumn)
    (i : ι) (q : Fin (activeCount + 2)) :
    HitsLinkagePath (L := S.linkage) (fixedColumn i)
      (S.corridor.index q) := by
  simpa [S.column_eq_fixed i] using
    S.columns.column_hits_every_row i q

/-- A strict degree-two drop from the current linkage is also a strict drop
from the branch's original linkage. -/
theorem degree_drop_lt_original
    [Fintype V]
    (S : CorridorRowState original activeCount ι fixedColumn)
    {L' : PerfectPathPacking G A B}
    (hlt :
      linkageAuxDegreeTwoCount L' <
        linkageAuxDegreeTwoCount S.linkage) :
    linkageAuxDegreeTwoCount L' <
      linkageAuxDegreeTwoCount original := by
  rw [S.auxIso.degreeTwoCount_eq]
  exact hlt

/-- Repackage a row-rerouting successor once the local auxiliary analysis has
shown that the new auxiliary graph is isomorphic to the old one.

Only the two boundary paths and linkage paths outside the corridor need to be
unchanged as graph paths.  Active corridor paths may be replaced. -/
noncomputable def successorOfAuxEquiv
    (S : CorridorRowState original activeCount ι fixedColumn)
    {linkage' : PerfectPathPacking G A B}
    (e : S.linkage.Index ≃ linkage'.Index)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph S.linkage).Adj i j ↔
          (linkageAuxGraph linkage').Adj (e i) (e j))
    (hlower :
      linkage'.path (e (S.corridor.index ⟨0, by omega⟩)) =
        S.linkage.path (S.corridor.index ⟨0, by omega⟩))
    (hupper :
      linkage'.path
          (e (S.corridor.index ⟨activeCount + 1, by omega⟩)) =
        S.linkage.path
          (S.corridor.index ⟨activeCount + 1, by omega⟩))
    (houtside :
      ∀ j : S.linkage.Index, j ∉ Set.range S.corridor.index →
        linkage'.path (e j) = S.linkage.path j) :
    CorridorRowState original activeCount ι fixedColumn := by
  classical
  let corridor' : AuxiliaryCorridor linkage' activeCount :=
    S.corridor.transport e hadj
  let columns' :
      FullBoundaryColumnFamily linkage' activeCount ι corridor' :=
    { column := fixedColumn
      pairwise_nodeDisjoint := by
        intro i j hij
        simpa [S.column_eq_fixed i, S.column_eq_fixed j] using
          S.columns.pairwise_nodeDisjoint hij
      lower_contact := by
        intro i
        have hold := S.columns.lower_contact i
        change
          (fixedColumn i).vertexSet ∩
              (linkage'.path
                (e (S.corridor.index ⟨0, by omega⟩))).vertexSet =
            {(fixedColumn i).source}
        rw [hlower]
        simpa [S.column_eq_fixed i] using hold
      upper_contact := by
        intro i
        have hold := S.columns.upper_contact i
        change
          (fixedColumn i).vertexSet ∩
              (linkage'.path
                (e (S.corridor.index
                  ⟨activeCount + 1, by omega⟩))).vertexSet =
            {(fixedColumn i).target}
        rw [hupper]
        simpa [S.column_eq_fixed i] using hold
      avoidsOutside := by
        intro i j hj
        let jold : S.linkage.Index := e.symm j
        have hjold : jold ∉ Set.range S.corridor.index := by
          intro hrange
          rcases hrange with ⟨q, hq⟩
          apply hj
          refine ⟨q, ?_⟩
          change e (S.corridor.index q) = j
          simpa [jold] using congrArg e hq
        have hold := S.columns.avoidsOutside i jold hjold
        have hpath : linkage'.path j = S.linkage.path jold := by
          have := houtside jold hjold
          simpa [jold] using this
        simpa [S.column_eq_fixed i, hpath] using hold }
  refine
    { originalCorridor := S.originalCorridor
      linkage := linkage'
      auxEquiv := S.auxEquiv.trans e
      auxAdj_iff := ?_
      corridor := corridor'
      corridor_index_eq := ?_
      columns := columns'
      column_eq := rfl }
  · intro i j
    exact (S.auxAdj_iff i j).trans (hadj (S.auxEquiv i) (S.auxEquiv j))
  · intro k
    change e (S.corridor.index k) =
      e (S.auxEquiv (S.originalCorridor.index k))
    exact congrArg e (S.corridor_index_eq k)

/-- Initial common state for a type-one majority family. -/
noncomputable def ofTypeOne
    {h : ℕ} {R : IndexedAuxiliaryPrefix original h} {hpos : 0 < h}
    {Q : PerfectPathPacking G R.X R.Y}
    (F : TypeOneQStarFamily R hpos Q) :
    CorridorRowState original (z h) (Fin h)
      (F.toFullBoundaryColumnFamily.column) where
  originalCorridor := R.typeOneAuxiliaryCorridor hpos
  linkage := original
  auxEquiv := Equiv.refl _
  auxAdj_iff := by
    intro i j
    rfl
  corridor := R.typeOneAuxiliaryCorridor hpos
  corridor_index_eq := by
    intro k
    rfl
  columns := F.toFullBoundaryColumnFamily
  column_eq := rfl

/-- Initial common state for a type-two majority family. -/
noncomputable def ofTypeTwo
    {h : ℕ} {R : IndexedAuxiliaryPrefix original h} {hpos : 0 < h}
    {Q : PerfectPathPacking G R.X R.Y}
    (F : TypeTwoQStarFamily R hpos Q) :
    CorridorRowState original (z h) (Fin h)
      (F.toFullBoundaryColumnFamily.column) where
  originalCorridor := R.typeTwoAuxiliaryCorridor hpos
  linkage := original
  auxEquiv := Equiv.refl _
  auxAdj_iff := by
    intro i j
    rfl
  corridor := R.typeTwoAuxiliaryCorridor hpos
  corridor_index_eq := by
    intro k
    rfl
  columns := F.toFullBoundaryColumnFamily
  column_eq := rfl

end CorridorRowState

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
