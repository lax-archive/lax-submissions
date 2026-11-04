import Lax185574Proofs.Interface.MDBridge

/-!
Monadic dependence passes to subclasses, for the graph classes of
`Lax185574.Graphs` and for those of the archive.

These facts, with `monadicallyDependent_toOld` and
`monadicallyDependent_ofOld_iff`, turn a statement about the classes of
the archive into one about graph classes and back.
-/

namespace Lax185574Proofs.Interface

open Lax185574.Graphs Lax185574.MonadicDependence

theorem transducesAllGraphs_mono {C C' : GraphClass} (h : C ⊆ C')
    (hT : TransducesAllGraphs C) : TransducesAllGraphs C' := by
  obtain ⟨k, ψ, hψ⟩ := hT
  refine ⟨k, ψ, fun H => ?_⟩
  obtain ⟨G, hG, hrest⟩ := hψ H
  exact ⟨G, h hG, hrest⟩

/-- A subclass of a monadically dependent class is monadically
dependent. -/
theorem monadicallyDependent_mono {C C' : GraphClass} (h : C ⊆ C')
    (hC' : MonadicallyDependent C') : MonadicallyDependent C :=
  fun hT => hC' (transducesAllGraphs_mono h hT)

/-- A subclass of a monadically dependent class of the archive is
monadically dependent. -/
theorem monadicallyDependent_old_mono {D D' : Lax199508.GraphClasses.GraphClass}
    (h : ∀ n H, D n H → D' n H) (hD' : Lax710763.MonadicDependence.MonadicallyDependent D') :
    Lax710763.MonadicDependence.MonadicallyDependent D :=
  (monadicallyDependent_ofOld_iff D).mp
    (monadicallyDependent_mono (fun G hG => h G.n G.toSimpleGraph hG)
      ((monadicallyDependent_ofOld_iff D').mpr hD'))

end Lax185574Proofs.Interface
