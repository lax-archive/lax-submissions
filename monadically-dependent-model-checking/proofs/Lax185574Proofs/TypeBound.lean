import Lax185574.DpMinimalTypeBound
import Lax185574.MonadicDependenceDpMinimal
import Lax185574.TypeBound

namespace Lax185574Proofs.TypeBound

open Lax185574.Graphs Lax185574.MonadicDependence
open Lax185574.FirstOrderTypes Lax185574.Colorings

/--
---
conclusion: Lax185574.TypeBound.typeCountOver_le
---
A monadically dependent class is dp-minimal, and the type bound holds
for every dp-minimal class.
-/
theorem typeCountOver_le (C : GraphClass) (hC : MonadicallyDependent C)
    (k q : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ, ∀ G ∈ C,
      ∀ (colors : Fin c → Set (Fin G.n)) (U : Finset (Fin G.n)),
        typeCountOver (expansion G.toSimpleGraph colors) k q Set.univ (U : Set (Fin G.n)) ≤
          F * (U.card + 1) ^ a :=
  Lax185574.DpMinimalTypeBound.typeCountOver_le C
    (Lax185574.MonadicDependenceDpMinimal.dpMinimal_of_monadicallyDependent C hC) k q

end Lax185574Proofs.TypeBound
