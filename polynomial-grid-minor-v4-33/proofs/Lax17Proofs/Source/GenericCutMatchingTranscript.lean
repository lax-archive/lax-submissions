import Lax17Proofs.Source.CutMatchingGamePeeling

namespace Lax17Proofs

universe u v w

/-!
# Generic cut-matching transcripts with responder provenance

This file strengthens the generic sixteen-phase peeling theorem by retaining
the fact that every round was produced by the supplied sequential responder.
-/

namespace SimpleGraph
namespace CutMatchingGame


variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Sixteen independent entropy phases followed by the final peeling
bisection produce a half-edge-expander whose complete transcript follows the
supplied sequential responder. -/
theorem exists_list_halfExpander_with_followsResponder
    {m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ)
    (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (k : ℝ)) :
    ∃ rounds : List (LazyRound X),
      rounds.length = 16 * k + 1 ∧
        IsHalfEdgeExpander rounds ∧
          FollowsResponder responder 0 rounds := by
  let phaseRounds :=
    sparseCutPlayMany (X := X) 1 4 m hm responder k 16
  have hbal :
      IsBalancedEdgeExpanderWith (X := X) phaseRounds 1 4 4 1 := by
    simpa [phaseRounds] using
      sparseCutPlayMany_balancedExpander_four_of_potential_budget
        (X := X) hm responder k hn hbudget
  rcases exists_final_bisection_halfExpander_of_balancedExpander_four
      (X := X) (rounds := phaseRounds) hm hbal hn responder (16 * k) with
    ⟨B, hhalf⟩
  refine
    ⟨phaseRounds ++ [LazyRound.ofResponder responder (16 * k) B], ?_, hhalf, ?_⟩
  · have hphaseLen : phaseRounds.length = 16 * k := by
      simpa [phaseRounds] using
        sparseCutPlayMany_length (X := X) 1 4 m hm responder k 16
    simp [hphaseLen]
  · have hphaseFollow :
        FollowsResponder responder 0 phaseRounds := by
      simpa [phaseRounds] using
        sparseCutPlayMany_followsResponder (X := X)
          1 4 m hm responder k 16
    have hphaseLen : phaseRounds.length = 16 * k := by
      simpa [phaseRounds] using
        sparseCutPlayMany_length (X := X) 1 4 m hm responder k 16
    have hfinalFollow :
        FollowsResponder responder phaseRounds.length
          [LazyRound.ofResponder responder (16 * k) B] := by
      simpa [hphaseLen] using
        followsResponder_singleton (X := X) responder (16 * k) B
    exact
      followsResponder_append (X := X) (offset := 0)
        (rounds := phaseRounds)
        (extra := [LazyRound.ofResponder responder (16 * k) B])
        hphaseFollow (by simpa using hfinalFollow)

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
