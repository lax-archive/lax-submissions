import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
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

For a graph and a radius *k*, the relevant set system consists of the open
*k*-neighborhoods of its vertices. A graph Welzl order of radius *k* and
crossing number at most *ℓ* is therefore crossed at most *ℓ* times by every
*k*-neighborhood.

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

An output order is the list of vertices in increasing position. The graph
specialization packages only the existence of a permutation represented by
that list and satisfying the crossing bound; it does not prescribe which of
the potentially many good orders an algorithm must choose.

The open `k`-neighborhood of `v` consists of the vertices other than `v` that
are reachable from it by a walk of length at most `k`. Thus radius one
recovers the ordinary open neighborhood used by the graph theorem, while
larger radii give the requested `k`-neighborhood systems. The radius and the
crossing bound are separate arguments.
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

/-- The vertices reachable from `v` by a walk of length at most `k`. -/
def withinDistance {n : ℕ} (G : SimpleGraph (Fin n))
    (k : ℕ) (v u : Fin n) : Prop :=
  ∃ w : G.Walk v u, w.length ≤ k

/-- The open `k`-neighborhood of `v`: vertices other than `v` within walk
distance `k`. -/
def kNeighborhood {n : ℕ} (G : SimpleGraph (Fin n))
    (k : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | u ≠ v ∧ withinDistance G k v u}

/-- The `k`-neighborhood set system of a graph: the open `k`-neighborhood of
every vertex. -/
def kNeighborhoodSetSystem {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    SetSystem (Fin n) :=
  {X | ∃ v : Fin n, X = kNeighborhood G k v}

/-- The list encoding of an order: vertices listed from first to last. -/
def EncodesOrder {n : ℕ} (y : List ℕ) (π : Equiv.Perm (Fin n)) : Prop :=
  y = List.ofFn (fun i : Fin n => (π.symm i).val)

/-- The word `y` encodes a Welzl order of crossing number at most
`crossingBound` for the `radius`-neighborhood set system of `G`. -/
def EncodesGraphWelzlOrder {n : ℕ} (G : SimpleGraph (Fin n))
    (radius crossingBound : ℕ) (y : List ℕ) : Prop :=
  ∃ π : Equiv.Perm (Fin n),
    EncodesOrder y π ∧
      IsWelzlOrder (kNeighborhoodSetSystem G radius) π crossingBound

end Lax195003.WelzlOrders
