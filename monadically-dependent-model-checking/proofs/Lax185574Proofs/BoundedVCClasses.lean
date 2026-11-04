import Lax185574.BoundedVCClasses
import Lax185574Proofs.BoundedVC
import Lax185574Proofs.Interface.MDBridge

/-!
Proof of obs:md-vc (`BoundedVCClasses`) from the characterization of
monadic dependence by the independence property
(`IndependenceProperty`).
-/

namespace Lax185574Proofs.BoundedVCClasses

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax185574.VCDimension

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem exists_vcDim_le_old (C : GraphClass) (hC : MonadicallyDependent C) :
    ∃ d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → vcDim G ≤ d :=
  Lax185574Proofs.BoundedVC.exists_vcDim_le C hC

end Lax185574Proofs.BoundedVCClasses

namespace Lax185574Proofs.BoundedVCClasses

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.VCDimension
open Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.BoundedVCClasses.exists_vcDim_le
---
A monadically dependent class has bounded VC-dimension, since otherwise
the edge formula has the independence property on it.

The argument is carried out for the graph classes of the archive and
their monadic dependence, and transferred to the graph classes used
here.
-/
theorem exists_vcDim_le (C : GraphClass) (hC : MonadicallyDependent C) :
    ∃ d : ℕ, ∀ G ∈ C, vcDim G.toSimpleGraph ≤ d := by
  obtain ⟨d, hd⟩ := exists_vcDim_le_old (toOld C) (monadicallyDependent_toOld hC)
  exact ⟨d, fun G hG => hd G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.BoundedVCClasses
