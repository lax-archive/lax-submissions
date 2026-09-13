import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1RowDescent
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1HillDescent
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1TerminalGrid

namespace Lax17Proofs

universe u v w

/-!
# Appendix B.1: common corridor conclusion and page-60 assembly

The type-one and type-two majority branches of Chekuri--Chuzhoy Theorem B.1
start the same corridor argument on different intervals of the displayed
auxiliary two-path.  This module keeps that common argument explicit:

* the finite bump/cross descent reduces a corridor state either to a strict
  degree-two drop or to a row-normal state;
* one row-normal-to-grid theorem therefore closes either corridor branch;
* the existing page-60 pigeonhole theorem invokes the common corridor theorem
  in both the type-one and the type-two cases.

No branch is discarded under a "without loss of generality" convention.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

open IndexedAuxiliaryPrefix

namespace CorridorRowState

/-- Once every row-normal corridor state yields the requested grid minor, the
finite row descent gives the complete rerouting conclusion for any initial
corridor state. -/
theorem reroutingConclusion_of_rowNormal_grid
    [Fintype V]
    {L : PerfectPathPacking G A B} {h : ℕ}
    {fixedColumn : Fin h → GraphPath G}
    (S₀ : CorridorRowState L (z h) (Fin h) fixedColumn)
    (hterminal :
      ∀ S : CorridorRowState L (z h) (Fin h) fixedColumn,
        S.RowNormal → ContainsGridMinor G h) :
    ReroutingConclusion G h L := by
  classical
  rcases S₀.degree_drop_or_exists_rowNormal with
    ⟨L', hdrop⟩ | ⟨S, hnormal⟩
  · exact Or.inr ⟨L', hdrop⟩
  · exact Or.inl (hterminal S hnormal)

end CorridorRowState

/-- Page-60 assembly from a single theorem valid for every common corridor
state.  Both majority branches are instantiated explicitly. -/
theorem reroutingConclusion_of_common_corridor
    [Fintype V]
    {L : PerfectPathPacking G A B} {h : ℕ}
    (hbad : ¬ GoodLinkage L h)
    (hlink : NodeLinkedIn G Finset.univ A B)
    (hpos : 0 < h)
    (hcorridor :
      ∀ {fixedColumn : Fin h → GraphPath G},
        CorridorRowState L (z h) (Fin h) fixedColumn →
          ReroutingConclusion G h L) :
    ReroutingConclusion G h L := by
  apply reroutingConclusion_of_page60_branch_handlers
      (L := L) (h := h) hbad hlink hpos
  · intro R Q T
    exact hcorridor (CorridorRowState.ofTypeOne T.Q0)
  · intro R Q T
    exact hcorridor (CorridorRowState.ofTypeTwo T.Q0)

/-- The exact remaining geometric handoff after the compiled row descent:
prove that every row-normal common corridor contains the requested grid.
This theorem then closes the full statement of Theorem B.1, including both
page-60 majority branches. -/
theorem theoremB1Statement_of_rowNormal_grid
    [Fintype V]
    {L : PerfectPathPacking G A B} {h : ℕ}
    (hterminal :
      ∀ {fixedColumn : Fin h → GraphPath G}
        (S : CorridorRowState L (z h) (Fin h) fixedColumn),
          S.RowNormal → ContainsGridMinor G h) :
    TheoremB1Statement G h L := by
  intro _hconnected hlink hh hbad
  have hpos : 0 < h := by omega
  refine reroutingConclusion_of_common_corridor
    (L := L) (h := h) hbad hlink hpos ?_
  intro fixedColumn S
  exact S.reroutingConclusion_of_rowNormal_grid
    (fun S' hnormal => hterminal S' hnormal)

/-- Equivalent top-level assembly when the common corridor conclusion itself
has already been proved. -/
theorem theoremB1Statement_of_common_corridor
    [Fintype V]
    {L : PerfectPathPacking G A B} {h : ℕ}
    (hcorridor :
      ∀ {fixedColumn : Fin h → GraphPath G},
        CorridorRowState L (z h) (Fin h) fixedColumn →
          ReroutingConclusion G h L) :
    TheoremB1Statement G h L := by
  intro _hconnected hlink hh hbad
  have hpos : 0 < h := by omega
  exact reroutingConclusion_of_common_corridor
    (L := L) (h := h) hbad hlink hpos hcorridor

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
