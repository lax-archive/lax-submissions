import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1Conclusion
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1TerminalGrid
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1HillNormalization
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1HillBumpPreservation

namespace Lax17Proofs

universe u v w

/-!
# Appendix B.1: the row-normal corridor conclusion

This module is the final handoff from the two finite normalizations to the
terminal sparse-grid construction.  Starting with a row-normal corridor
state, hill descent produces a supported no-hill family.  Support transports
active-strip no-cross from the pre-hill family, and the terminal theorem then
extracts the grid.

The only fact isolated by the first theorem is preservation of no-bump under
the supported hill descent.  It is stated as a hypothesis so that the
dedicated hill/bump preservation module can be plugged in without duplicating
the corridor assembly.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

open IndexedAuxiliaryPrefix

namespace CorridorRowState

/-- Exact corridor conclusion once supported hill replacement is known to
preserve the already established no-bump invariant. -/
theorem rowNormal_containsGridMinor_of_supported_noBump
    {L : PerfectPathPacking G A B} {h : ℕ}
    {fixedColumn : Fin h → GraphPath G}
    (S : CorridorRowState L (z h) (Fin h) fixedColumn)
    (hnormal : S.RowNormal)
    (supported_noBump :
      ∀ (F : FullBoundaryColumnFamily
          S.linkage (z h) (Fin h) S.corridor),
        FullBoundaryColumnFamily.SupportedByColumnsAndActiveRows
          S.columns.column F →
        (∀ i : Fin h, (S.columns.trace i).NoBump) →
          ∀ i : Fin h, (F.trace i).NoBump) :
    ContainsGridMinor G h := by
  classical
  have hbaseNoBump :
      ∀ i : Fin h, (S.columns.trace i).NoBump :=
    fun i =>
      S.columns.trace_noBump_of_noActiveBump i
        (CorridorRowState.RowNormal.noActiveBump S hnormal i)
  rcases S.columns.exists_noHillFamily_supported with
    ⟨F, hsupport, hnoHill⟩
  have hnoBump : ∀ i : Fin h, (F.trace i).NoBump :=
    supported_noBump F hsupport hbaseNoBump
  have hnoActiveCross : F.NoActiveCross :=
    S.columns.noActiveCross_of_supported F hsupport
      (CorridorRowState.RowNormal.noActiveCross S hnormal)
  exact
    FullBoundaryColumnFamily.ActiveTerminalGeometry.containsGridMinor_of_noHill
      hnoBump hnoActiveCross hnoHill

/-- A row-normal corridor already has the terminal grid outcome.  Hill
descent preserves its active bump- and cross-freeness, and boundary-contact
uniqueness upgrades active bump-freeness to full bump-freeness. -/
theorem rowNormal_containsGridMinor
    {L : PerfectPathPacking G A B} {h : ℕ}
    {fixedColumn : Fin h → GraphPath G}
    (S : CorridorRowState L (z h) (Fin h) fixedColumn)
    (hnormal : S.RowNormal) :
    ContainsGridMinor G h := by
  apply S.rowNormal_containsGridMinor_of_supported_noBump hnormal
  intro F hsupport _hbaseNoBump
  exact
    S.columns.noBump_of_supported_noActiveBump F hsupport
      (fun i =>
        CorridorRowState.RowNormal.noActiveBump S hnormal i)

end CorridorRowState

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
