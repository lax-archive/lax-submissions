import Lax185574Proofs.Interface.IndependenceProperty

/-!
The two statements of `Lax185574.IndependenceProperty` in the form for
mathlib formulas over the classes of the archive, `Old.HasIP`, derived
from the concept.
-/

namespace Lax185574Proofs.Shim.IndependenceProperty

open FirstOrder FirstOrder.Language
open Lax710763.Transductions Lax185574Proofs.Interface

theorem monadicallyDependent_iff_forall_not_hasIP (C : Lax199508.GraphClasses.GraphClass) :
    Lax710763.MonadicDependence.MonadicallyDependent C ↔
      ∀ (k : ℕ) (φ : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1)),
        ¬ Old.HasIP C φ :=
  (monadicallyDependent_ofOld_iff C).symm.trans
    ((Lax185574.IndependenceProperty.monadicallyDependent_iff_forall_not_hasIP (ofOld C)).trans
      (forall_not_hasIP_toOld_iff (ofOld C)).symm)

theorem not_hasIP_of_monadicallyDependent (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax710763.MonadicDependence.MonadicallyDependent C) {k p p' : ℕ}
    (φ : (withColors Language.graph k).Formula (Fin p ⊕ Fin p')) :
    ¬ Old.HasIP C φ := fun h =>
  Lax185574.IndependenceProperty.not_hasIP_of_monadicallyDependent (ofOld C)
    ((monadicallyDependent_ofOld_iff C).mpr hC) _ (hasIP_ofOld h)

end Lax185574Proofs.Shim.IndependenceProperty
