import Lax185574Proofs.Lib.PartitionMetricConversionDefs
import Mathlib.Data.Finset.Card

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/




namespace Lax185574Proofs.Lib.DefinableFlips

universe u

noncomputable def atomicProfile {V : Type u} (G : SimpleGraph V)
    (A : Finset V) (v : V) : Finset V × Finset V := by
  classical
  exact (A.filter (G.Adj v), A.filter (fun a => v = a))

def IsBasedFlip {V : Type u} (G : SimpleGraph V) (S : Finset V)
    (H : SimpleGraph V) : Prop :=
  ∃ toggle : V → V → Prop,
    (∀ u v, toggle u v ↔ toggle v u) ∧
    (∀ u u' v v', atomicProfile G S u = atomicProfile G S u' →
      atomicProfile G S v = atomicProfile G S v' →
      (toggle u v ↔ toggle u' v')) ∧
    ∀ u v, H.Adj u v ↔ u ≠ v ∧ Xor (G.Adj u v) (toggle u v)

def IsDefinableFlip {V : Type u} (G H : SimpleGraph V) (s : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≤ s ∧ IsBasedFlip G S H





end Lax185574Proofs.Lib.DefinableFlips
