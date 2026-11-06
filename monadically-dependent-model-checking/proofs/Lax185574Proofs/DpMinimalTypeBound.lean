import Lax185574.DpMinimalFlips
import Lax185574.DpMinimalPatterns
import Lax185574.DpMinimalTypeBound
import Lax185574.DpMinimalVC
import Lax185574Proofs.TypeBound

namespace Lax185574Proofs.DpMinimalTypeBound

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.DpMinimality Lax185574.PhiPsiPatterns Lax185574.PhiPatterns
open Lax185574.FirstOrderTypes Lax185574.Colorings Lax185574.FlipsMonadicallyDependent
open Lax185574Proofs.Interface

theorem forbidden_phiPsi_toOld (C : GraphClass) (hC : DpMinimal C) {p p' : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), toOld C n G → ¬ HasPattern G φ ψ t t := by
  obtain ⟨t, ht⟩ := Lax185574.DpMinimalPatterns.forbidden_phiPsi_patterns C hC φ ψ
  exact ⟨t, fun n G hG => ht (Graph.ofSimpleGraph G) hG⟩

theorem forbidsPhiPatterns_toOld (C : GraphClass) (hC : DpMinimal C) :
    BallTypes.ForbidsPhiPatterns (toOld C) := fun φ =>
  ForbiddenPhiPatterns.forbidden_phi_patterns_of_phiPsi _ φ
    (forbidden_phiPsi_toOld C hC φ edgeFormula) (forbidden_phiPsi_toOld C hC φ edgeFormula.not)

theorem boundedVCOfDefinableFlips_toOld (C : GraphClass) (hC : DpMinimal C) :
    ClosureTheorem.BoundedVCOfDefinableFlips (toOld C) := by
  intro s
  obtain ⟨d, hd⟩ := Lax185574.DpMinimalVC.exists_vcDim_le _
    (Lax185574.DpMinimalFlips.dpMinimal_definableFlipClass C hC s)
  exact ⟨d, fun n G H hG hH => hd (Graph.ofSimpleGraph H)
    ⟨Graph.ofSimpleGraph G, hG, H, hH, rfl⟩⟩

/--
---
conclusion: Lax185574.DpMinimalTypeBound.typeCountOver_le
---
The proof of the type bound for monadically dependent classes, which
uses its assumption on the class in two places only. The first is that
φ-patterns of bounded order are excluded: a φ-pattern is a
`(φ, E)`-pattern or a `(φ, ¬E)`-pattern, and these are excluded in a
dp-minimal class by the lemma on `(φ, ψ)`-patterns. This gives the
ball-types lemma. The second is that, for every `s`, the `s`-definable
flips of the graphs of the class have bounded VC-dimension: they form a
dp-minimal class, and dp-minimal classes have bounded VC-dimension. With
the ball-types lemma this gives the closure theorem, the closure theorem
for tuples and the type bound, by the same arguments.

The argument is carried out for the graph classes of the archive, and
transferred to the graph classes used here.
-/
theorem typeCountOver_le (C : GraphClass) (hC : DpMinimal C) (k q : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ, ∀ G ∈ C,
      ∀ (colors : Fin c → Set (Fin G.n)) (U : Finset (Fin G.n)),
        typeCountOver (expansion G.toSimpleGraph colors) k q Set.univ (U : Set (Fin G.n)) ≤
          F * (U.card + 1) ^ a := by
  have hBT := BallTypes.ball_types_of_forbidsPhiPatterns (toOld C) (forbidsPhiPatterns_toOld C hC)
  have hcl := ClosureTheorem.closure_theorem_of_ballTypes (toOld C) hBT
    (boundedVCOfDefinableFlips_toOld C hC)
  obtain ⟨a, h⟩ := TypeBound.typeCountOver_le_of_closureTuples (toOld C)
    (ClosureTheoremTuples.closure_theorem_tuples_of_closure (toOld C) hcl) k q
  refine ⟨a, fun c => ?_⟩
  obtain ⟨F, hF⟩ := h c
  exact ⟨F, fun G hG => hF G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.DpMinimalTypeBound
