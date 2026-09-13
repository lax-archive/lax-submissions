import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Finite descent for Chuzhoy Section 7

The two pruning procedures in Section 7 repeatedly replace the current vertex
set by a proper subset while preserving their state invariants.  This module
isolates termination from the graph-specific preservation proof.  A minimum
natural-valued measure state is terminal; no executable loop or finite state
type is required.
-/

namespace SimpleGraph
namespace AppendixA3FiniteDescent

/-- A valid state has a terminal representative whenever every nonterminal
valid state admits a valid successor of strictly smaller natural measure. -/
theorem exists_terminal_of_measure_descent
    {State : Type*} (measure : State → ℕ)
    (Valid Good : State → Prop) (initial : State)
    (hinitial : Valid initial)
    (hstep :
      ∀ state, Valid state → ¬ Good state →
        ∃ next, Valid next ∧ measure next < measure state) :
    ∃ state, Valid state ∧ Good state := by
  classical
  let HasMeasure : ℕ → Prop := fun n =>
    ∃ state, Valid state ∧ measure state = n
  have hExists : ∃ n : ℕ, HasMeasure n :=
    ⟨measure initial, initial, hinitial, rfl⟩
  rcases Nat.find_spec hExists with ⟨state, hvalid, hmeasure⟩
  refine ⟨state, hvalid, ?_⟩
  by_contra hgood
  rcases hstep state hvalid hgood with ⟨next, hnext, hdecrease⟩
  have hnextMeasure : HasMeasure (measure next) :=
    ⟨next, hnext, rfl⟩
  have hminimal : Nat.find hExists ≤ measure next :=
    Nat.find_min' (H := hExists) hnextMeasure
  omega

/-- Finset specialization: if every bad subset of `S` has a strictly smaller
badness-preserving replacement, some subset of `S` is good. -/
theorem exists_good_subset_of_strict_descent
    {V : Type*} [DecidableEq V] (S : Finset V)
    (Good : Finset V → Prop)
    (hstep :
      ∀ U, U ⊆ S → ¬ Good U →
        ∃ A, A ⊂ U ∧ A ⊆ S) :
    ∃ U, U ⊆ S ∧ Good U := by
  apply exists_terminal_of_measure_descent
    (measure := Finset.card)
    (Valid := fun U => U ⊆ S)
    (Good := Good)
    (initial := S)
    (by exact Finset.Subset.rfl)
  intro U hUS hbad
  rcases hstep U hUS hbad with ⟨A, hproper, hAS⟩
  exact ⟨A, hAS, Finset.card_lt_card hproper⟩

end AppendixA3FiniteDescent
end SimpleGraph

end Lax17Proofs
