import Lax185574Proofs.Lib.BoundedVCDualityDefs
import Lax185574Proofs.Lib.DefinableFlipsDefs

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/




namespace Lax185574Proofs.Lib.BallFlips

open Lax185574Proofs.Lib.PartitionMetricConversion Lax185574Proofs.Lib.BoundedVCDuality
open Lax185574Proofs.Lib.DefinableFlips

universe u

noncomputable def ball {V : Type u} [Fintype V] (G : SimpleGraph V)
    (C : Finset V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ c ∈ C, Within G r c v)

noncomputable def trace {V : Type u} (G : SimpleGraph V) (A : Finset V)
    (v : V) : Finset V := by
  classical
  exact A.filter (G.Adj v)

noncomputable def traces {V : Type u} (G : SimpleGraph V) (A B : Finset V) :
    Finset (Finset V) := by
  classical
  exact B.image (trace G A)



end Lax185574Proofs.Lib.BallFlips
