import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

/-!
---
title: Welzl orders
type: definition
---
Let `𝓕` be a set system on a finite ground set. A set `X ∈ 𝓕` crosses
a total order whenever two consecutive elements lie on opposite sides of
`X`. Its crossing count is the number of such consecutive pairs, and the
crossing number of the order is the largest crossing count over all sets in
`𝓕`. A Welzl order of crossing number at most *k* is a total order whose
crossing number is at most *k*.

# Formalization notes

A total order of `Fin n` is represented by a permutation `π`, with `π v` the
position of `v`. Consecutive pairs are counted by their earlier endpoint:
`u` contributes exactly when some `v` has natural-number position
`(π u).val + 1` and precisely one of `u` and `v` lies in the set. Comparing
the natural values, rather than adding inside `Fin n`, avoids turning the
last and first positions into an artificial cyclic pair.

The crossing number is a natural supremum. Every crossing count is at most
`n - 1`, so the set is bounded; for an empty family the natural convention
`sSup ∅ = 0` gives the expected crossing number zero. `IsWelzlOrder` is a
`Prop`-valued bound rather than a structure carrying data derivable from the
order and the set system.

-/

namespace Lax195003.WelzlOrders

/-- A set system on `α`: a family of subsets of the ground set `α`. -/
abbrev SetSystem (α : Type*) := Set (Set α)

/-- The number of consecutive pairs in the order `π` with exactly one
endpoint in `X`. -/
noncomputable def crossingCount {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) : ℕ :=
  {u : Fin n | ∃ v : Fin n,
    (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)}.ncard

/-- The crossing number of `π` with respect to `𝓕`: the largest crossing
count of a member of the set system. -/
noncomputable def crossingNumber {n : ℕ} (𝓕 : SetSystem (Fin n))
    (π : Equiv.Perm (Fin n)) : ℕ :=
  sSup {k : ℕ | ∃ X ∈ 𝓕, k = crossingCount π X}

/-- The order `π` is a Welzl order of crossing number at most `k` for the
set system `𝓕`. -/
def IsWelzlOrder {n : ℕ} (𝓕 : SetSystem (Fin n))
    (π : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  crossingNumber 𝓕 π ≤ k

end Lax195003.WelzlOrders
