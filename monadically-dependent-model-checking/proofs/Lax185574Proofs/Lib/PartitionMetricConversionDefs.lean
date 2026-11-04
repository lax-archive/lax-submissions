import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Fintype.Fin

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/




namespace Lax185574Proofs.Lib.PartitionMetricConversion

universe u

/-- Toggle adjacency on selected pairs of partition labels, excluding loops. -/
def flip {V : Type u} {p : ℕ} (G : SimpleGraph V) (part : V → Fin p)
    (toggle : Fin p → Fin p → Bool) (hsymm : ∀ i j, toggle i j = toggle j i) :
    SimpleGraph V where
  Adj u v := u ≠ v ∧ Xor (G.Adj u v) (toggle (part u) (part v) = true)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    simpa only [G.adj_comm, hsymm (part v) (part u)] using h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Closed graph distance bound, expressed without assigning a finite
distance to vertices in different components. -/
def Within {V : Type u} (G : SimpleGraph V) (r : ℕ) (u v : V) : Prop :=
  ∃ w : G.Walk u v, w.length ≤ r

/-- Closed ball in the maximum metric over all flips on `part`. -/
def partitionBall {V : Type u} {p : ℕ} (G : SimpleGraph V)
    (part : V → Fin p) (r : ℕ) (v : V) : Set V :=
  {u | ∀ (toggle : Fin p → Fin p → Bool) (hsymm : ∀ i j, toggle i j = toggle j i),
    Within (flip G part toggle hsymm) r v u}



end Lax185574Proofs.Lib.PartitionMetricConversion
