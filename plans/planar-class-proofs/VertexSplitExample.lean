import Lax303502Proofs.ConvexVertexSplit

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

theorem contracted_points :
    contractedDrawing.point ∘ contractMap (show (0 : Fin 5) ≠ 4 by decide) = splitPoint := by
  funext v
  fin_cases v <;> rfl

theorem split_direction : SplitDirection wheel
    (contractedDrawing.point ∘ contractMap (show (0 : Fin 5) ≠ 4 by decide)) 0 4 (1,2) := by
  rw [contracted_points]
  apply splitDirection_of_sector (u := (1,0)) (v := (0,1))
  · intro a ha hay
    have hx : ∀ a, DrawingCell wheel 0 a → a ≠ 4 → a = 0 ∨ a = 1 ∨ a = 2 := by
      unfold DrawingCell wheel
      decide
    rcases hx a ha hay with rfl | rfl | rfl
    all_goals norm_num [splitPoint,cross,Matrix.cons_val_two]
  · intro b hb hbx
    have hy : ∀ b, DrawingCell wheel 4 b → b ≠ 0 → b = 2 ∨ b = 3 ∨ b = 4 := by
      unfold DrawingCell wheel
      decide
    rcases hy b hb hbx with rfl | rfl | rfl
    all_goals norm_num [splitPoint,cross,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four]
  all_goals norm_num [cross]

/-- Four bounded polygons and the outer triangle, all oriented counterclockwise. -/
def boundaryLength : Fin 5 → ℕ := ![1,0,0,0,0]

def boundary : (f : Fin 5) → Fin (boundaryLength f+3) → Fin 5
  | 0 => ![0,1,3,4]
  | 1 => ![0,4,2]
  | 2 => ![4,3,2]
  | 3 => ![1,2,3]
  | 4 => ![0,1,2]

def Opens {n : ℕ} (c : Fin (n+3) → Fin 5) : Prop :=
  ∀ i j, j ≠ i → j ≠ i+1 →
    0 < area (splitPoint (c i)) (splitPoint (c (i+1))) (splitPoint (c j)) ∨
    (area (splitPoint (c i)) (splitPoint (c (i+1))) (splitPoint (c j)) = 0 ∧
      0 < splitAreaSlope splitPoint 4 (1,2) (c i) (c (i+1)) (c j))

/-- Check every old supporting-edge inequality, including the zero areas
created by contraction and the last-to-first edges of all five polygons. -/
theorem boundary_opens : ∀ f, Opens (boundary f) := by
  intro f
  fin_cases f
  all_goals first
    | change Opens (![0,1,3,4] : Fin 4 → Fin 5)
    | change Opens (![0,4,2] : Fin 3 → Fin 5)
    | change Opens (![4,3,2] : Fin 3 → Fin 5)
    | change Opens (![1,2,3] : Fin 3 → Fin 5)
    | change Opens (![0,1,2] : Fin 3 → Fin 5)
  all_goals intro i j hji hjn; fin_cases i <;> fin_cases j
  all_goals norm_num [splitPoint,area,cross,splitAreaSlope,Fin.add_def,Fin.ext_iff,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four] at *

/-- The same epsilon certifies the drawing and all five convex boundaries. -/
theorem wheel_convex_split : ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε →
    SeparatedPlacement wheel (splitPlacement splitPoint 4 (1,2) t) ∧
    ∀ f, StrictConvexBoundary (splitPlacement splitPoint 4 (1,2) t ∘ boundary f) := by
  have h := vertex_split_convex_small (by decide) contractedDrawing split_direction
    boundaryLength boundary
  rw [contracted_points] at h
  exact h boundary_opens

/-- A triangle with its first vertex duplicated at the end of the list. -/
def outerPoint : Fin 4 → Point := ![(0,0),(3,0),(0,3),(0,0)]

/-- Moving the duplicate outward opens a strictly convex quadrilateral. -/
theorem outer_boundary_split : ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε →
    StrictConvexBoundary (splitPlacement outerPoint 3 (-1,1) t) := by
  have h := split_boundaries_small outerPoint 3 (-1,1) (fun _ : Unit => 1)
    (fun _ => id)
  have hc : ∀ (_ : Unit) (i j : Fin 4), j ≠ i → j ≠ i+1 →
      0 < area (outerPoint i) (outerPoint (i+1)) (outerPoint j) ∨
        (area (outerPoint i) (outerPoint (i+1)) (outerPoint j) = 0 ∧
          0 < splitAreaSlope outerPoint 3 (-1,1) i (i+1) j) := by
    intro _ i j hji hjn
    fin_cases i <;> fin_cases j
    all_goals norm_num [outerPoint,area,cross,splitAreaSlope,Fin.add_def,Fin.ext_iff,
      Matrix.cons_val_two,Matrix.cons_val_three] at *
  simpa only [Function.comp_id,forall_const] using h hc

/-- Reversing that displacement fails convexity, so the signs in
our certificate are essential. -/
theorem reversed_outer_split_not_convex {t : ℝ} (ht : 0 < t) :
    ¬StrictConvexBoundary (splitPlacement outerPoint 3 (1,-1) t) := by
  intro h
  have hc := h 3 1 (by decide) (by decide)
  norm_num [outerPoint,splitPlacement,area,cross,Matrix.cons_val_three,Fin.add_def,Fin.ext_iff] at hc
  nlinarith

/-- The general split lemma supplies this drawing without choosing a numerical epsilon. -/
theorem wheel_planar : Lax68.Planar.IsPlanar wheel :=
  planar_of_vertex_split (by decide) contractedDrawing split_direction

#print axioms Lax303502Proofs.VertexSplitExample.outer_boundary_split
#print axioms Lax303502Proofs.exists_convex_split_direction
#print axioms Lax303502Proofs.vertex_split_convex_small
#print axioms Lax303502Proofs.VertexSplitExample.wheel_convex_split
#print axioms Lax303502Proofs.vertex_split_small
#print axioms Lax303502Proofs.planar_of_vertex_split
#print axioms Lax303502Proofs.VertexSplitExample.wheel_planar
end Lax303502Proofs.VertexSplitExample
