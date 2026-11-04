import Lax185574Proofs.Interface.DefinableFlipClass

/-!
The statement of `Lax185574.FlipsMonadicallyDependent` for the classes
of the archive, derived from the concept.
-/

namespace Lax185574Proofs.Shim.FlipsMonadicallyDependent

open Lax185574Proofs.Interface

theorem monadicallyDependent_definableFlipClass (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax710763.MonadicDependence.MonadicallyDependent C) (s : ℕ) :
    Lax710763.MonadicDependence.MonadicallyDependent (Old.definableFlipClass C s) :=
  monadicallyDependent_old_mono (old_definableFlipClass_le C s)
    (monadicallyDependent_toOld
      (Lax185574.FlipsMonadicallyDependent.monadicallyDependent_definableFlipClass (ofOld C)
        ((monadicallyDependent_ofOld_iff C).mpr hC) s))

end Lax185574Proofs.Shim.FlipsMonadicallyDependent
