import Lax235315Proofs.Construction.ListCrossing
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
The reconstruction argument of the Welzl-order algorithm.

This module deliberately separates the paper's combinatorial certificate
from its implementation.  A `Reduction` records one checked iteration: a
near-twin representative for every set-side vertex and a sequence of genuine
twin insertions on the ground-set side.  `CertifiedRun` chains reductions
backwards from the small base instance.  The main theorem is the paper's
crossing-number induction, independent of sampling and of the RAM.
-/

namespace Lax235315Proofs.Construction.Reconstruction

open scoped symmDiff
open Lax235315Proofs.Construction.ListCrossing

noncomputable section

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- A duplicate-free list enumerates exactly the set `A`. -/
def Enumerates (A : Set (Fin n)) (l : List (Fin n)) : Prop :=
  l.Nodup ∧ ∀ v : Fin n, v ∈ l ↔ v ∈ A

lemma Enumerates.length_eq_ncard {A : Set (Fin n)} {l : List (Fin n)}
    (h : Enumerates A l) :
    l.length = A.ncard := by
  classical
  rw [← List.toFinset_card_of_nodup h.1, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp [h.2]

/-- Starting with `small`, repeatedly insert a fresh vertex immediately
after a representative having the same adjacency to every vertex of `B`.
This is the reconstruction operation of Lemma 2.1. -/
inductive TwinExpansion (B : Set (Fin n)) :
    List (Fin n) → List (Fin n) → Prop
  | refl (l : List (Fin n)) : TwinExpansion B l l
  | insert {small current : List (Fin n)} {a x : Fin n}
      (h : TwinExpansion B small current)
      (ha : a ∈ current) (hx : x ∉ current)
      (htwin : ∀ b ∈ B, (G.Adj b a ↔ G.Adj b x)) :
      TwinExpansion B small (insertAfter a x current)

lemma TwinExpansion.nodup {B : Set (Fin n)} {small big : List (Fin n)}
    (h : TwinExpansion G B small big) (hsmall : small.Nodup) :
    big.Nodup := by
  induction h with
  | refl => exact hsmall
  | insert h ha hx _ ih => exact nodup_insertAfter ih ha hx

/-- Inserting ground-side twins preserves every crossing count represented
by `B`. -/
lemma TwinExpansion.crossingCount_eq {B : Set (Fin n)}
    {small big : List (Fin n)} (h : TwinExpansion G B small big)
    {b : Fin n} (hb : b ∈ B) :
    crossingCount (G.neighborSet b) big =
      crossingCount (G.neighborSet b) small := by
  induction h with
  | refl => rfl
  | insert h ha _ htwin ih =>
      rw [crossingCount_insertAfter ha]
      · exact ih
      · simpa using htwin b hb

/-- One checked iteration of the paper's algorithm, in the direction used
by reconstruction. -/
structure Reduction (k : ℕ) (A B A' B' : Set (Fin n))
    (small big : List (Fin n)) where
  /-- The smaller and larger lists enumerate their active ground sets. -/
  small_enumerates : Enumerates A' small
  /-- The expanded list enumerates the preceding active ground set. -/
  big_enumerates : Enumerates A big
  /-- Removed ground vertices are restored only by twin insertions over `B'`. -/
  expands : TwinExpansion G B' small big
  /-- The representative chosen for each set-side vertex. -/
  representative : Fin n → Fin n
  /-- Every active set-side vertex has an active representative. -/
  representative_mem : ∀ b ∈ B, representative b ∈ B'
  /-- The checked near-twin guarantee, restricted to the active ground set. -/
  near : ∀ b ∈ B,
    ((G.neighborSet b ∩ A) ∆
      (G.neighborSet (representative b) ∩ A)).ncard ≤ k

lemma Reduction.crossingCount_le {k m : ℕ}
    {A B A' B' : Set (Fin n)} {small big : List (Fin n)}
    (h : Reduction G k A B A' B' small big)
    (hsmall : ∀ b ∈ B', crossingCount (G.neighborSet b) small ≤ m) :
    ∀ b ∈ B, crossingCount (G.neighborSet b) big ≤ m + 2 * k := by
  intro b hb
  let r := h.representative b
  have hr : r ∈ B' := h.representative_mem b hb
  let X := G.neighborSet b ∩ A
  let Y := G.neighborSet r ∩ A
  have hX : crossingCount (G.neighborSet b) big = crossingCount X big :=
    crossingCount_congr_on fun v hv => by
      have hvA := (h.big_enumerates.2 v).mp hv
      simp [X, hvA]
  have hY : crossingCount Y big = crossingCount (G.neighborSet r) big :=
    crossingCount_congr_on fun v hv => by
      have hvA := (h.big_enumerates.2 v).mp hv
      simp [Y, hvA]
  calc
    crossingCount (G.neighborSet b) big = crossingCount X big := hX
    _ ≤ crossingCount Y big + 2 * (X ∆ Y).ncard :=
      crossingCount_le_add_two_mul_symmDiff X Y h.big_enumerates.1
    _ ≤ crossingCount Y big + 2 * k := by
      have hnear := h.near b hb
      change (X ∆ Y).ncard ≤ k at hnear
      omega
    _ = crossingCount (G.neighborSet r) big + 2 * k := by rw [hY]
    _ = crossingCount (G.neighborSet r) small + 2 * k := by
      rw [h.expands.crossingCount_eq G hr]
    _ ≤ m + 2 * k := Nat.add_le_add_right (hsmall r hr) _

lemma add_round_bound (rounds k q : ℕ) (hkq : 2 * k ≤ q) :
    (rounds + 1) * q + 2 * k ≤ (rounds + 1 + 1) * q := by
  calc
    (rounds + 1) * q + 2 * k ≤ (rounds + 1) * q + q :=
      Nat.add_le_add_left hkq _
    _ = (rounds + 1 + 1) * q := by
      simp [Nat.add_mul, Nat.add_assoc]
      omega

/-- A complete successful paper run, read backwards from its base case.
The index is the number of reduction rounds. -/
inductive CertifiedRun (k q : ℕ) :
    ℕ → Set (Fin n) → Set (Fin n) → List (Fin n) → Prop
  | base {A B : Set (Fin n)} {l : List (Fin n)}
      (henum : Enumerates A l) (hcard : A.ncard ≤ q) :
      CertifiedRun k q 0 A B l
  | step {rounds : ℕ} {A B A' B' : Set (Fin n)}
      {small big : List (Fin n)}
      (hreduction : Reduction G k A B A' B' small big)
      (htail : CertifiedRun k q rounds A' B' small) :
      CertifiedRun k q (rounds + 1) A B big

lemma CertifiedRun.enumerates {k q rounds : ℕ}
    {A B : Set (Fin n)} {l : List (Fin n)}
    (h : CertifiedRun G k q rounds A B l) : Enumerates A l := by
  cases h with
  | base henum _ => exact henum
  | step hreduction _ => exact hreduction.big_enumerates

/-- The crossing-number induction of Theorem 3.2 in the paper. -/
lemma CertifiedRun.crossingCount_le {k q rounds : ℕ}
    {A B : Set (Fin n)} {l : List (Fin n)}
    (h : CertifiedRun G k q rounds A B l) (hkq : 2 * k ≤ q) :
    ∀ b ∈ B, crossingCount (G.neighborSet b) l ≤ (rounds + 1) * q := by
  induction h with
  | base henum hcard =>
      intro b _
      exact (crossingCount_le_length _ _).trans <| by
        rw [henum.length_eq_ncard]
        exact hcard.trans (by omega)
  | step hreduction htail ih =>
      intro b hb
      have hstep := hreduction.crossingCount_le G
        (fun r hr => ih r hr) b hb
      exact hstep.trans (add_round_bound _ _ _ hkq)

end

end Lax235315Proofs.Construction.Reconstruction
