import Mathlib.Data.Fintype.Powerset
import Mathlib.Computability.Partrec

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/




namespace Lax185574Proofs.Lib.BipartiteRamsey

universe u v

def neighborhoodFamily {L : Type u} {R : Type v}
    [Fintype L] [Fintype R] [DecidableEq R]
    (E : L → R → Prop) [DecidableRel E] : Finset (Finset R) :=
  Finset.univ.image (fun x => Finset.univ.filter (E x))

/-- The selected rectangle is a matching, co-matching, or half-graph.
Injectivity of the tuples is imposed separately by the theorem. -/
def AtomicallyMatched {L : Type u} {R : Type v} {ℓ : ℕ}
    (E : L → R → Prop) (a : Fin ℓ → L) (b : Fin ℓ → R) : Prop :=
  (∀ i j, E (a i) (b j) ↔ i = j) ∨
  (∀ i j, E (a i) (b j) ↔ i ≠ j) ∨
  (∀ i j, E (a i) (b j) ↔ i ≤ j)



end Lax185574Proofs.Lib.BipartiteRamsey
