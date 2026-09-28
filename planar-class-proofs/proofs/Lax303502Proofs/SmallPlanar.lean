import Lax303502Proofs.PlaneCells
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.NatCard

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.StraightLineDrawings

/-- A triangle and one point strictly inside it give a drawing of `K₄`. -/
def fourPoint (i : Fin 4) : Point := ![(0,0),(3,0),(0,3),(1,1)] i

set_option maxRecDepth 2048 in
private theorem four_clean : SP.Clean (⊤ : SimpleGraph (Fin 4)) fourPoint := by
  intro a b c d u v _ _ hu hu' hv hv' he
  by_contra hn
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [SP.Shared] at hn
  all_goals norm_num [SP.mix,fourPoint,Prod.mk.injEq] at he
  all_goals nlinarith [he]

noncomputable def completeFourDrawing : StraightLineDrawing (⊤ : SimpleGraph (Fin 4)) :=
  SP.clean_drawing four_clean (by ext v; simp)

/-- Pull a drawing back along an injective graph homomorphism. -/
def drawing_pullback {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (D : StraightLineDrawing H) (f : G →g H) (hf : Function.Injective f) :
    StraightLineDrawing G where
  point := D.point ∘ f
  injective := D.injective.comp hf
  noVertexOnEdge hab hca hcb :=
    D.noVertexOnEdge (f.map_rel hab) (hf.ne hca) (hf.ne hcb)
  disjointEdges hab hcd hdis := by
    apply D.disjointEdges (f.map_rel hab) (f.map_rel hcd)
    simpa only [Set.image_insert_eq,Set.image_singleton] using
      Set.disjoint_image_of_injective hf hdis

/-- Every graph with at most four vertices has a straight-line drawing. -/
theorem planar_card_le_four {V : Type*} [Finite V] (G : SimpleGraph V)
    (hcard : Nat.card V ≤ 4) : Lax68.Planar.IsPlanar G := by
  classical
  let := Fintype.ofFinite V
  have hc : Fintype.card V ≤ Fintype.card (Fin 4) := by simpa using hcard
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  let g : G →g (⊤ : SimpleGraph (Fin 4)) := ⟨f,fun h => f.injective.ne h.ne⟩
  exact ⟨drawing_pullback completeFourDrawing g f.injective⟩

end Lax303502Proofs
