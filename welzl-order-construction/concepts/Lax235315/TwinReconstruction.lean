import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.SymmDiff

/-!
---
title: Checked twin-contraction reconstruction
type: definition
---
A reconstruction starts with an order on a small remaining ground set and
undoes checked contraction rounds. In each round it inserts removed ground
vertices next to twins over the retained set-side representatives. Every
old set-side vertex has a retained representative whose neighborhood differs
on at most k active ground vertices.

# Formalization notes

The two sides are subsets of the same canonical vertex type, as in the
graph-neighborhood bipartite representation. A round records concrete lists,
actual adjacent twin insertions, and the checked symmetric-difference bound.
It does not assume any crossing-number conclusion.
The run relation describes deterministic reconstruction certificates. A
separate implementation proof must show that the machine produces one.
-/

namespace Lax235315.TwinReconstruction
open scoped symmDiff

/-- Insert x immediately after the first occurrence of a, if a is present. -/
def insertAfter {n : ℕ} (a x : Fin n) : List (Fin n) → List (Fin n)
  | [] => []
  | b :: rest => if b = a then b :: x :: rest else b :: insertAfter a x rest

/-- A list contains each member of A exactly once and contains no other vertex. -/
def Enumerates {n : ℕ} (A : Set (Fin n)) (l : List (Fin n)) : Prop :=
  l.Nodup ∧ ∀ v : Fin n, v ∈ l ↔ v ∈ A

/-- A sequence of insertions of fresh vertices next to twins over B. -/
inductive TwinExpansion {n : ℕ} (G : SimpleGraph (Fin n)) (B : Set (Fin n)) :
    List (Fin n) → List (Fin n) → Prop
  /-- No insertion is needed to expand a list to itself. -/
  | refl (l : List (Fin n)) : TwinExpansion G B l l
  /-- Restore a fresh vertex immediately after a present twin. -/
  | insert {small current : List (Fin n)} {a x : Fin n}
      (previous : TwinExpansion G B small current)
      (present : a ∈ current) (fresh : x ∉ current)
      (twins : ∀ b ∈ B, (G.Adj b a ↔ G.Adj b x)) :
      TwinExpansion G B small (insertAfter a x current)

/-- The data checked when one contraction round is reconstructed. -/
structure Reduction {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (A B A' B' : Set (Fin n)) (small big : List (Fin n)) where
  /-- The contracted list enumerates the retained ground vertices. -/
  small_enumerates : Enumerates A' small
  /-- The reconstructed list enumerates the preceding ground vertices. -/
  big_enumerates : Enumerates A big
  /-- Reconstruction uses only genuine twin insertions over B'. -/
  expands : TwinExpansion G B' small big
  /-- The representative assigned to each set-side vertex. -/
  representative : Fin n → Fin n
  /-- Representatives of active vertices belong to the retained side. -/
  representative_mem : ∀ b ∈ B, representative b ∈ B'
  /-- The checked distance to each representative on the active ground set. -/
  near : ∀ b ∈ B,
    ((G.neighborSet b ∩ A) ∆ (G.neighborSet (representative b) ∩ A)).ncard ≤ k

/-- A complete reconstruction, indexed by the number of undone rounds. -/
inductive Run {n : ℕ} (G : SimpleGraph (Fin n)) (k q : ℕ) :
    ℕ → Set (Fin n) → Set (Fin n) → List (Fin n) → Prop
  /-- Start with any order on a ground set of at most q vertices. -/
  | base {A B : Set (Fin n)} {l : List (Fin n)}
      (enumerates : Enumerates A l) (small : A.ncard ≤ q) :
      Run G k q 0 A B l
  /-- Undo one checked contraction and continue the recorded reconstruction. -/
  | step {rounds : ℕ} {A B A' B' : Set (Fin n)}
      {small big : List (Fin n)}
      (reduction : Reduction G k A B A' B' small big)
      (tail : Run G k q rounds A' B' small) :
      Run G k q (rounds + 1) A B big

end Lax235315.TwinReconstruction
