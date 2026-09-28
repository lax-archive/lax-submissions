import Lax303502Proofs.SubdivisionGeometry
import Lax303502Proofs.Topology.Graph.K33Land
import Lax68.Planar
import Lax303502Proofs.KuratowskiMinorBridge

set_option autoImplicit false

namespace Lax303502Proofs
namespace Polygonal

open Lax68.StraightLineDrawings Lax68.GraphMinors Lax68.GraphTopologicalMinors

/-- Identify the product model of the plane with its Euclidean-space model. -/
def toPlane (p : Point) : Schoenflies.Plane := Schoenflies.Plane.mk p.1 p.2

theorem toPlane_injective : Function.Injective toPlane := by
  intro p q h
  exact Prod.ext (congrArg (fun x : Schoenflies.Plane => x 0) h)
    (congrArg (fun x : Schoenflies.Plane => x 1) h)

theorem continuous_toPlane : Continuous toPlane := by
  change Continuous (fun p : Point => WithLp.toLp 2 ![p.1,p.2])
  fun_prop

/-- An injective path in the product plane gives an arc in the separation library. -/
theorem isArcBetween_path {p q : Point} (A : Path p q) (hA : Function.Injective A) :
    Schoenflies.IsArcBetween (toPlane '' Set.range A) (toPlane p) (toPlane q) := by
  refine ⟨toPlane ∘ A.extend,(continuous_toPlane.comp A.continuous_extend).continuousOn,?_,?_,?_,?_⟩
  · intro s hs t ht h
    change toPlane (A.extend s) = toPlane (A.extend t) at h
    rw [A.extend_apply hs,A.extend_apply ht] at h
    have he : A ⟨s,hs⟩ = A ⟨t,ht⟩ := toPlane_injective h
    exact congrArg Subtype.val (hA he)
  · rw [Set.image_comp]
    exact congrArg (Set.image toPlane) (A.image_extend_of_subset Set.Subset.rfl)
  · simp [Function.comp_apply]
  · simp [Function.comp_apply]

/-- The utility graph has no polygonal drawing. The separation argument is the
three-chord proof of Álvaro Begué's Jordan–Schönflies development: two of the
three alternating chords of a six-cycle would lie on the same side. -/
theorem no_polygonalDrawing_k33 (D : PolygonalDrawing K33) : False := by
  let x (i : Fin 3) := toPlane (D.point (.inl i))
  let y (j : Fin 3) := toPlane (D.point (.inr j))
  have adj (i j : Fin 3) : K33.Adj (.inl i) (.inr j) := by simp
  let P (i j : Fin 3) := toPlane '' Set.range (D.arc (adj i j))
  apply Graph.IsArcK33.elim (x := x) (y := y) (P := P)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j
    exact isArcBetween_path (D.arc (adj i j)) (D.arc_injective (adj i j))
  · intro i k h
    exact Sum.inl.inj (D.injective (toPlane_injective h))
  · intro j l h
    exact Sum.inr.inj (D.injective (toPlane_injective h))
  · intro i j h
    exact Sum.inl_ne_inr (D.injective (toPlane_injective h))
  · intro i j k l hne z hz
    obtain ⟨u,hu,rfl⟩ := hz.1
    obtain ⟨v,hv,huv⟩ := hz.2
    have he : v = u := toPlane_injective huv
    subst v
    obtain ⟨w,hw,hw',rfl⟩ := D.arc_intersection (adj i j) (adj k l) (by
      rintro (⟨h,h'⟩ | ⟨h,h'⟩)
      · exact hne (Prod.ext (Sum.inl.inj h) (Sum.inr.inj h'))
      · exact Sum.inl_ne_inr h) u hu hv
    constructor
    · rcases hw with rfl | rfl <;> simp [x,y]
    · rcases hw' with rfl | rfl <;> simp [x,y]

/-- A straight-line planar graph contains no subdivision of the utility graph.
This proves the `K₃,₃` obstruction in the original Kuratowski statement. -/
theorem not_topologicalMinor_k33_of_planar {V : Type*} {G : SimpleGraph V}
    (hG : Lax68.Planar.IsPlanar G) : ¬ IsTopologicalMinor K33 G := by
  obtain ⟨D⟩ := hG
  rintro ⟨M⟩
  let e := Fintype.equivFin (Fin 3 ⊕ Fin 3)
  let : LinearOrder (Fin 3 ⊕ Fin 3) := LinearOrder.lift' e e.injective
  exact no_polygonalDrawing_k33 (subdivisionDrawing D M)

/-- A planar graph has no utility-graph minor, by the degree-three
minor-to-subdivision conversion. -/
theorem not_minor_k33_of_planar {V : Type*} {G : SimpleGraph V}
    (hG : Lax68.Planar.IsPlanar G) : ¬ IsMinor K33 G :=
  fun hM => not_topologicalMinor_k33_of_planar hG (k33_minor_topological hM)

end Polygonal
end Lax303502Proofs
