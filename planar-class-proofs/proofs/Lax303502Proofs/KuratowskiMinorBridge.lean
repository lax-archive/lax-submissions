import Lax303502Proofs.MinorRouting
import Lax303502Proofs.TopologicalToMinor
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.GraphMinors Lax68.GraphTopologicalMinors

def k33NeighborEquiv (a : Fin 3 ⊕ Fin 3) : Fin 3 ≃ K33.neighborSet a := by
  cases a with
  | inl a =>
    refine ⟨fun i => ⟨Sum.inr i,by simp⟩,?_,?_,?_⟩
    · rintro ⟨b,hb⟩
      cases b with
      | inl b => exact False.elim (by simp at hb)
      | inr b => exact b
    · intro i; rfl
    · rintro ⟨b,hb⟩
      cases b with
      | inl b => simp at hb
      | inr b => rfl
  | inr a =>
    refine ⟨fun i => ⟨Sum.inl i,by simp⟩,?_,?_,?_⟩
    · rintro ⟨b,hb⟩
      cases b with
      | inl b => exact b
      | inr b => exact False.elim (by simp at hb)
    · intro i; rfl
    · rintro ⟨b,hb⟩
      cases b with
      | inl b => rfl
      | inr b => simp at hb

/-- The degree-three case of Diestel's minor/subdivision conversion. -/
theorem k33_minor_topological {V : Type*} {G : SimpleGraph V} (hM : IsMinor K33 G) :
    IsTopologicalMinor K33 G := by
  classical
  let e := Fintype.equivFin (Fin 3 ⊕ Fin 3)
  let : LinearOrder (Fin 3 ⊕ Fin 3) := LinearOrder.lift' e e.injective
  obtain ⟨M⟩ := hM
  let P := minorPorts M
  have hF a : Nonempty (PathFan (G.induce (M.branchSet a)) (P.terminal a)) :=
    connected_fan_three_equiv (M.connected a).preconnected (k33NeighborEquiv a) (P.terminal a)
  exact ⟨minor_topological_of_fans M P (fun a => Classical.choice (hF a))⟩

def k5NeighborEquiv (a : Fin 5) : Fin 4 ≃ K5.neighborSet a :=
  (finSuccAboveEquiv a).trans
    { toFun := fun b => ⟨b,by exact Ne.symm b.property⟩
      invFun := fun b => ⟨b,by exact Ne.symm b.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Lax303502Proofs
