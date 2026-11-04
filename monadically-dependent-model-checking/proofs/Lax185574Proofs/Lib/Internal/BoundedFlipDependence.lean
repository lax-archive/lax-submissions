import Lax185574Proofs.Lib.PartitionMetricConversionDefs
import Lax185574Proofs.Lib.DefinableFlipsDefs
import Lax710763.MonadicDependence
import Lax710763.Transductions

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-! Internal definitions used by the proof implementation. -/

namespace Lax185574Proofs.Lib.Internal.BoundedFlipDependence

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax185574Proofs.Lib.PartitionMetricConversion

/-- All partition flips with a uniformly bounded number of parts. -/
def BoundedFlipImage (C : GraphClass) (P : ℕ) : GraphClass :=
  fun n H => ∃ G : SimpleGraph (Fin n), C n G ∧
    ∃ (p : ℕ) (_ : p ≤ P) (part : Fin n → Fin p)
      (toggle : Fin p → Fin p → Bool) (hsymm : ∀ i j, toggle i j = toggle j i),
      H = flip G part toggle hsymm



/-- All flips definable over at most s vertices of a member of C. -/
def DefinableFlipImage (C : GraphClass) (s : ℕ) : GraphClass :=
  fun n H => ∃ G : SimpleGraph (Fin n), C n G ∧
    Lax185574Proofs.Lib.DefinableFlips.IsDefinableFlip G H s



end Lax185574Proofs.Lib.Internal.BoundedFlipDependence
