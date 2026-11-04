import Lax710763.MonadicDependence
import Lax710763.Transductions
import Lax185574Proofs.Lib.TransductionCalculus

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-!
Graph-class corollaries of the generic transduction composition proof
adapted in `TransductionCalculus`. No closure axiom from the concept
package is used by these proofs.
-/

namespace Lax185574Proofs.Lib.MonadicDependenceClosure

open Lax199508.GraphClasses Lax710763.MonadicDependence

/--
Apply relational-language composition to the graph structure classes.
-/
theorem graph_transduces_trans {C D E : GraphClass}
    (hCD : Lax710763.GraphTransductions.Transduces C D)
    (hDE : Lax710763.GraphTransductions.Transduces D E) :
    Lax710763.GraphTransductions.Transduces C E :=
  TransductionCalculus.Transduces.trans hCD hDE

/--
A hypothetical transduction of all graphs from the target class would
compose to one from the original class, contradicting monadic dependence.
-/
theorem monadicallyDependent_of_transduces {C D : GraphClass}
    (hC : MonadicallyDependent C)
    (hCD : Lax710763.GraphTransductions.Transduces C D) :
    MonadicallyDependent D :=
  fun hD => hC (graph_transduces_trans hCD hD)

end Lax185574Proofs.Lib.MonadicDependenceClosure
