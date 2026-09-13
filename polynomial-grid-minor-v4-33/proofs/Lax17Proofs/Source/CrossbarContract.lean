import Lax17Proofs.Source.Crossbar
import Lax17Proofs.Source.CrossbarPower
import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.Degree
import Mathlib.Data.Nat.Log

namespace Lax17Proofs

universe u v w


/-!
# Contract for the crossbar dichotomy

This file states Chuzhoy--Tan Theorem 3.1 in the language of the formalized
objects: from three large terminal sets `A`, `B`, and `X` with the two required
linkage packings, either a crossbar exists or a minor contains a large strong
Path-of-Sets System.
-/

namespace SimpleGraph
namespace CrossbarContract

/-- `G` has a minor that contains a strong Path-of-Sets System of length `ell`
and width `w`. -/
def HasStrongPathOfSetsMinor {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (ell w : ℕ) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
    (H : _root_.SimpleGraph W),
      IsMinor H G ∧ Nonempty (StrongPathOfSetsSystem H ell w)


end CrossbarContract
end SimpleGraph

end Lax17Proofs
