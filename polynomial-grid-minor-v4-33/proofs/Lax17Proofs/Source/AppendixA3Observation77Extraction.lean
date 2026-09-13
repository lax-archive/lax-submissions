import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3PruningStep
import Lax17Proofs.Source.AppendixA3Observation77Crossing

namespace Lax17Proofs

universe u v w

/-!
# Extracting the first original-terminal crossing

The pruning relation records every guarded retained-side transition.  This
file isolates the small induction needed by Observation 7.7: if the initial
original-terminal mass is above three quarters and a reachable state is at or
below three quarters, one of the recorded transitions crosses the threshold.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

private abbrev originalBoundary
    (S T : Finset V) : Finset V :=
  AppendixA3ClusterSplit.augmentedBoundaryVertices G S T

private abbrev originalMass
    (S T U : Finset V) : ℕ :=
  (U ∩ originalBoundary (G := G) S T).card

/-- A reachable pruning state whose original-terminal mass is at most three
quarters has a first guarded transition from a state above three quarters.

The returned predecessor is itself reachable.  The successor is definitionally
the `retainLeft` state built with all four guards appearing in the pruning
relation, so later applications can use the crossing theorem directly. -/
theorem exists_guarded_original_three_quarter_crossing
    {S T : Finset V} {state : PruningState G S T}
    (hreachable : PruningReachable G S T state)
    (hinitial :
      3 * (originalBoundary (G := G) S T).card <
        4 * (originalBoundary (G := G) S T).card)
    (hterminal :
      4 * (originalMass (G := G) S T state.U) ≤
        3 * (originalBoundary (G := G) S T).card) :
    ∃ (successor previous : PruningState G S T) (A B : Finset V),
      PruningReachable G S T successor ∧
      PruningReachable G S T previous ∧
      3 * (originalBoundary (G := G) S T).card <
        4 * (originalMass (G := G) S T previous.U) ∧
      ∃ (hcover : A ∪ B = previous.U) (hdisj : Disjoint A B)
          (horient :
            (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
                G previous.U T).card ≤
              (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
                G previous.U T).card)
          (hsparse :
            9 * (Section44.edgeBoundary G A B).card <
              (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
                G previous.U T).card),
        successor = previous.retainLeft hcover hdisj horient hsparse ∧
      4 * (originalMass (G := G) S T successor.U) ≤
            3 * (originalBoundary (G := G) S T).card := by
  revert hterminal
  induction hreachable with
  | initial =>
      intro hterminal
      have hsubset :
          originalBoundary (G := G) S T ⊆ S := by
        intro v hv
        change v ∈ AppendixA3ClusterSplit.boundaryVertices G S ∪ (T ∩ S)
          at hv
        rcases Finset.mem_union.mp hv with hvBoundary | hvTerminal
        · exact
            ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1
              hvBoundary).1
        · exact (Finset.mem_inter.mp hvTerminal).2
      have hmass_eq :
          originalMass (G := G) S T S =
            (originalBoundary (G := G) S T).card := by
        simp only [originalMass, Finset.inter_eq_right.mpr hsubset]
      exfalso
      rw [PruningState.initial, hmass_eq] at hterminal
      omega
  | @retainLeft previous hprevious A B hcover hdisj horient hsparse ih =>
      change 4 * (originalMass (G := G) S T
          (previous.retainLeft hcover hdisj horient hsparse).U) ≤
        3 * (originalBoundary (G := G) S T).card → _
      intro hterminal
      by_cases hpreviousBelow :
          4 * (originalMass (G := G) S T previous.U) ≤
            3 * (originalBoundary (G := G) S T).card
      · exact ih hpreviousBelow
      · refine ⟨previous.retainLeft hcover hdisj horient hsparse,
          previous, A, B, ?_⟩
        exact ⟨PruningReachable.retainLeft hprevious hcover hdisj horient hsparse,
          hprevious, by omega,
          ⟨hcover, hdisj, horient, hsparse, rfl, hterminal⟩⟩

end
end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
