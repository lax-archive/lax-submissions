import Lax17Proofs.Source.Section43

namespace Lax17Proofs

/-!
# Additive form of Chuzhoy--Tan Lemma 4.8

This experimental exponent-eight module exposes the counting invariant that
already drives the proof of Lemma 4.8 in `Section43.lean`.

The pruning trace does more than retain half of the auxiliary paths.  If
`Afinal` and `Bfinal` are its surviving left and right families, respectively,
then

`|(B \ Bfinal)| * D <= |(A \ Afinal)| * w`.

In the path-packing specialization this is

`|(Qset \ Q')| * Dhat <= |(Rset \ R')| * wHat`,

which immediately implies the coarser bound requested by the recursive
Section 5 bookkeeping:

`|(Qset \ Q')| * Dhat <= |Rset| * wHat`.

Unlike the half-retention corollary, the additive statement needs neither the
global cardinality inequality nor positivity of `Dhat`.
-/

namespace SimpleGraph

universe u

namespace FiniteBipartitePruning

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (rel : α → β → Prop) [∀ a b, Decidable (rel a b)]
variable {wHat Dhat : ℕ}

namespace PruneTrace

variable {rel}

/-- Additive strengthening of the generic finite pruning lemma underlying
Chuzhoy--Tan Lemma 4.8.

The output records the exact charge inequality.  This is the invariant from
which the old half-retention conclusion is derived after additionally assuming
`2 * A.card * wHat <= Dhat * B.card` and `0 < Dhat`. -/
theorem exists_intersecting_subsets_additive_core
    (A : Finset α) (B : Finset β)
    (hdense :
      ∀ b ∈ B, 2 * Dhat ≤ (A.bipartiteBelow rel b).card) :
    ∃ Afinal : Finset α, ∃ Bfinal : Finset β,
      Afinal ⊆ A ∧
        Bfinal ⊆ B ∧
          (∀ a ∈ Afinal,
            wHat ≤ (Bfinal.bipartiteAbove rel a).card) ∧
            (∀ b ∈ Bfinal,
              Dhat ≤ (Afinal.bipartiteBelow rel b).card) ∧
              (B \ Bfinal).card * Dhat ≤
                (A \ Afinal).card * wHat ∧
                ∀ a ∈ A \ Afinal,
                  (Bfinal.bipartiteAbove rel a).card ≤ wHat := by
  classical
  let tr := build (rel := rel) (w := wHat) (D := Dhat) A B
  rcases tr with ⟨Afinal, Bfinal, htrace⟩
  have hAsub := final_left_subset (rel := rel) htrace
  have hBsub := final_right_subset (rel := rel) htrace
  have hgoodA := final_left_good (rel := rel) htrace
  have hgoodB := final_right_good (rel := rel) htrace
  have hdeletedA := deleted_left_hits_final_le (rel := rel) htrace
  have hdenseRoot :
      ∀ b ∈ B,
        2 * Dhat ≤
          (((∅ : Finset α) ∪ A).bipartiteBelow rel b).card := by
    simpa using hdense
  have hcharge :
      (B \ Bfinal).card * Dhat ≤
        (((∅ : Finset α) ∪ (A \ Afinal)).card) * wHat :=
    deleted_right_mul_le_deleted_left_mul
      (rel := rel) htrace (∅ : Finset α)
      (by simp) (by simp) hdenseRoot
  have hcharge' :
      (B \ Bfinal).card * Dhat ≤ (A \ Afinal).card * wHat := by
    simpa using hcharge
  exact
    ⟨Afinal, Bfinal, hAsub, hBsub, hgoodA, hgoodB, hcharge', hdeletedA⟩

/-- The literal additive strengthening of Lemma 4.8: it retains every
conclusion of `exists_intersecting_subsets` and additionally exposes the exact
loss charged by deleted left vertices.

The half-retention conclusion is now a short arithmetic corollary of
`exists_intersecting_subsets_additive_core`; the pruning construction and its
charge count are not repeated. -/
theorem exists_intersecting_subsets_additive
    (A : Finset α) (B : Finset β)
    (hDhat : 0 < Dhat)
    (hdense :
      ∀ b ∈ B, 2 * Dhat ≤ (A.bipartiteBelow rel b).card)
    (hcard : 2 * A.card * wHat ≤ Dhat * B.card) :
    ∃ Afinal : Finset α, ∃ Bfinal : Finset β,
      Afinal ⊆ A ∧
        Bfinal ⊆ B ∧
          (∀ a ∈ Afinal,
            wHat ≤ (Bfinal.bipartiteAbove rel a).card) ∧
            (∀ b ∈ Bfinal,
              Dhat ≤ (Afinal.bipartiteBelow rel b).card) ∧
              (B \ Bfinal).card * Dhat ≤
                (A \ Afinal).card * wHat ∧
                B.card ≤ 2 * Bfinal.card ∧
                  ∀ a ∈ A \ Afinal,
                    (Bfinal.bipartiteAbove rel a).card ≤ wHat := by
  rcases exists_intersecting_subsets_additive_core
      (rel := rel) (wHat := wHat) (Dhat := Dhat) A B hdense
      with ⟨Afinal, Bfinal, hAsub, hBsub, hgoodA, hgoodB, hloss, hsparse⟩
  have hAdelete_le : (A \ Afinal).card ≤ A.card :=
    Finset.card_le_card Finset.sdiff_subset
  have htwice_delete_mul :
      2 * ((B \ Bfinal).card * Dhat) ≤ Dhat * B.card := by
    calc
      2 * ((B \ Bfinal).card * Dhat)
          ≤ 2 * ((A \ Afinal).card * wHat) :=
            Nat.mul_le_mul_left 2 hloss
      _ ≤ 2 * (A.card * wHat) := by
        exact Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_right wHat hAdelete_le)
      _ ≤ Dhat * B.card := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcard
  have hdel_twice : 2 * (B \ Bfinal).card ≤ B.card := by
    have hrewrite :
        Dhat * (2 * (B \ Bfinal).card) ≤ Dhat * B.card := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        htwice_delete_mul
    exact Nat.le_of_mul_le_mul_left hrewrite hDhat
  have hsplit : B.card = Bfinal.card + (B \ Bfinal).card := by
    have := Finset.card_sdiff_add_card_eq_card hBsub
    omega
  have hhalf : B.card ≤ 2 * Bfinal.card := by
    rw [hsplit]
    omega
  exact
    ⟨Afinal, Bfinal, hAsub, hBsub, hgoodA, hgoodB, hloss, hhalf, hsparse⟩

end PruneTrace

end FiniteBipartitePruning

namespace PathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T S' T' : Finset V}

/-- Chuzhoy--Tan Lemma 4.8 with its additive loss exposed.

The inequality with `(Rset \ R').card` is stronger than the version using
`Rset.card`, and is the form that composes cleanly through recursive slicing
rounds. -/
theorem exists_intersecting_path_subfamilies_additive_core
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (Qset : Finset Q.Index)
    {wHat Dhat : ℕ}
    (hdense :
      ∀ q ∈ Qset,
        2 * Dhat ≤ (R.intersectingLeftIndices Q Rset q).card) :
    ∃ R' : Finset R.Index, ∃ Q' : Finset Q.Index,
      R' ⊆ Rset ∧
        Q' ⊆ Qset ∧
          IntersectingPathSetPair R Q R' Q' wHat Dhat ∧
            (Qset \ Q').card * Dhat ≤
              (Rset \ R').card * wHat ∧
              ∀ r ∈ Rset \ R',
                (R.intersectingRightIndices Q Q' r).card ≤ wHat := by
  classical
  let rel : R.Index → Q.Index → Prop :=
    fun r q => PathsIntersect (R.path r) (Q.path q)
  have hdense' :
      ∀ q ∈ Qset,
        2 * Dhat ≤ (Rset.bipartiteBelow rel q).card := by
    intro q hq
    simpa [intersectingLeftIndices, rel] using hdense q hq
  rcases
    FiniteBipartitePruning.PruneTrace.exists_intersecting_subsets_additive_core
      (rel := rel) (wHat := wHat) (Dhat := Dhat) Rset Qset hdense'
      with ⟨R', Q', hRsub, hQsub, hleft, hright, hloss, hdeleted⟩
  refine ⟨R', Q', hRsub, hQsub, ?_, hloss, ?_⟩
  · constructor
    · intro r hr
      simpa [intersectingRightIndices, rel] using hleft r hr
    · intro q hq
      simpa [intersectingLeftIndices, rel] using hright q hq
  · intro r hr
    simpa [intersectingRightIndices, rel] using hdeleted r hr

/-- Chuzhoy--Tan Lemma 4.8 with the exact additive loss added to its original
conclusions. -/
theorem exists_intersecting_path_subfamilies_additive
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (Qset : Finset Q.Index)
    {wHat Dhat : ℕ}
    (hDhat : 0 < Dhat)
    (hdense :
      ∀ q ∈ Qset,
        2 * Dhat ≤ (R.intersectingLeftIndices Q Rset q).card)
    (hcard : 2 * Rset.card * wHat ≤ Dhat * Qset.card) :
    ∃ R' : Finset R.Index, ∃ Q' : Finset Q.Index,
      R' ⊆ Rset ∧
        Q' ⊆ Qset ∧
          IntersectingPathSetPair R Q R' Q' wHat Dhat ∧
            (Qset \ Q').card * Dhat ≤
              (Rset \ R').card * wHat ∧
              Qset.card ≤ 2 * Q'.card ∧
                ∀ r ∈ Rset \ R',
                  (R.intersectingRightIndices Q Q' r).card ≤ wHat := by
  classical
  let rel : R.Index → Q.Index → Prop :=
    fun r q => PathsIntersect (R.path r) (Q.path q)
  have hdense' :
      ∀ q ∈ Qset,
        2 * Dhat ≤ (Rset.bipartiteBelow rel q).card := by
    intro q hq
    simpa [intersectingLeftIndices, rel] using hdense q hq
  rcases
    FiniteBipartitePruning.PruneTrace.exists_intersecting_subsets_additive
      (rel := rel) (wHat := wHat) (Dhat := Dhat)
      Rset Qset hDhat hdense' hcard
      with
        ⟨R', Q', hRsub, hQsub, hleft, hright, hloss, hhalf, hdeleted⟩
  refine ⟨R', Q', hRsub, hQsub, ?_, hloss, hhalf, ?_⟩
  · constructor
    · intro r hr
      simpa [intersectingRightIndices, rel] using hleft r hr
    · intro q hq
      simpa [intersectingLeftIndices, rel] using hright q hq
  · intro r hr
    simpa [intersectingRightIndices, rel] using hdeleted r hr

/-- Coarse additive loss, with the original row-family cardinality on the
right-hand side.  This corollary keeps the old half-retention statement too. -/
theorem exists_intersecting_path_subfamilies_additive_coarse
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (Qset : Finset Q.Index)
    {wHat Dhat : ℕ}
    (hDhat : 0 < Dhat)
    (hdense :
      ∀ q ∈ Qset,
        2 * Dhat ≤ (R.intersectingLeftIndices Q Rset q).card)
    (hcard : 2 * Rset.card * wHat ≤ Dhat * Qset.card) :
    ∃ R' : Finset R.Index, ∃ Q' : Finset Q.Index,
      R' ⊆ Rset ∧
        Q' ⊆ Qset ∧
          IntersectingPathSetPair R Q R' Q' wHat Dhat ∧
            (Qset \ Q').card * Dhat ≤ Rset.card * wHat ∧
              Qset.card ≤ 2 * Q'.card ∧
                ∀ r ∈ Rset \ R',
                  (R.intersectingRightIndices Q Q' r).card ≤ wHat := by
  rcases
    exists_intersecting_path_subfamilies_additive
      R Q Rset Qset hDhat hdense hcard
      with ⟨R', Q', hRsub, hQsub, hinter, hloss, hhalf, hsparse⟩
  refine ⟨R', Q', hRsub, hQsub, hinter, hloss.trans ?_, hhalf, hsparse⟩
  exact Nat.mul_le_mul_right wHat
    (Finset.card_le_card Finset.sdiff_subset)

end PathPacking

end SimpleGraph

end Lax17Proofs
