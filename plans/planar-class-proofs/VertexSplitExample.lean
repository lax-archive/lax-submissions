import Lax303502Proofs.VertexSplit

set_option autoImplicit false
namespace Lax303502Proofs.VertexSplitExample
open Lax68.StraightLineDrawings

/-- A four-cycle with a hub: contract `0--4` to obtain `K₄`. -/
def wheel : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b =>
  (a,b) ∈ ([(0,1),(0,2),(0,4),(1,2),(1,3),(2,3),(2,4),(3,4)] : List (Fin 5 × Fin 5)))

def index (v : {v : Fin 5 // v ≠ 4}) : Fin 4 := ⟨v.val.val, by
  have hv := v.val.isLt
  have hn : v.val.val ≠ 4 := fun h => v.property (Fin.ext h)
  omega⟩

theorem index_injective : Function.Injective index := by
  intro a b h
  exact Subtype.ext (Fin.ext (congrArg (fun i : Fin 4 => i.val) h))

noncomputable def contractedDrawing : StraightLineDrawing
    (edgeContract wheel (show (0 : Fin 5) ≠ 4 by decide)) :=
  drawing_pullback completeFourDrawing
    ⟨index,fun h => index_injective.ne h.ne⟩ index_injective

def splitPoint : Fin 5 → Point := ![(0,0),(3,0),(0,3),(1,1),(0,0)]

theorem split_direction : SplitDirection wheel
    (contractedDrawing.point ∘ contractMap (show (0 : Fin 5) ≠ 4 by decide)) 0 4 (1,2) := by
  have hp : contractedDrawing.point ∘ contractMap (show (0 : Fin 5) ≠ 4 by decide) =
      splitPoint := by
    funext v
    fin_cases v <;> rfl
  rw [hp]
  intro a b ha hb hay hbx hab
  have hx : ∀ a, DrawingCell wheel 0 a → a ≠ 4 → a = 0 ∨ a = 1 ∨ a = 2 := by
    unfold DrawingCell wheel
    decide
  have hy : ∀ b, DrawingCell wheel 4 b → b ≠ 0 → b = 2 ∨ b = 3 ∨ b = 4 := by
    unfold DrawingCell wheel
    decide
  rcases hx a ha hay with rfl | rfl | rfl <;>
    rcases hy b hb hbx with rfl | rfl | rfl
  all_goals try exact (hab rfl).elim
  all_goals solve
    | refine ⟨LinearMap.fst ℝ ℝ ℝ, ?_⟩; norm_num [splitPoint,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four]
    | refine ⟨LinearMap.snd ℝ ℝ ℝ, ?_⟩; norm_num [splitPoint,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four]

/-- The general split lemma supplies this drawing without choosing a numerical epsilon. -/
theorem wheel_planar : Lax68.Planar.IsPlanar wheel :=
  planar_of_vertex_split (by decide) contractedDrawing split_direction

#print axioms Lax303502Proofs.vertex_split_small
#print axioms Lax303502Proofs.planar_of_vertex_split
#print axioms Lax303502Proofs.VertexSplitExample.wheel_planar
end Lax303502Proofs.VertexSplitExample
