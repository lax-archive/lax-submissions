import Lax214022.CographWelzlLowerBound
import Lax214022Proofs.CographWelzlUpperBound
import Lax214022Proofs.LowerObstruction

/-!
# Logarithmic lower bound for cographs

The hard graph of height `k` consists of a universal root above three
disjoint copies of the graph of height `k - 1`.  The ternary choice is what
makes the order argument work: after locating the root in an arbitrary
linear order, one branch avoids both vertices immediately beside the root.
Induction inside that branch therefore leaves an additional isolated `true`
at the root in the selected neighborhood row.
-/

namespace Lax214022Proofs.CographWelzlLowerBound

open Lax48Proofs.Main
open Lax214022.Cographs
open Lax214022Proofs.HardCographs
open Lax214022Proofs.LowerObstruction
open Lax214022Proofs.ListCrossings
open Lax214022Proofs.CographWelzlUpperBound
open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersNeighborhoodSetSystem

noncomputable section

/-- Every row occurring in a finite set system is bounded above by its
crossing number. -/
private theorem crossingCount_le_crossingNumber {n : ℕ}
    (F : SetSystem (Fin n)) (π : Equiv.Perm (Fin n))
    {X : Set (Fin n)} (hX : X ∈ F) :
    crossingCount π X ≤ crossingNumber F π := by
  unfold crossingNumber
  let S : Set ℕ := {q | ∃ Y ∈ F, q = crossingCount π Y}
  have hcc : ∀ Y : Set (Fin n), crossingCount π Y ≤ n := by
    intro Y
    unfold crossingCount
    calc
      _ ≤ Set.univ.ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = n := by simp
  have hbdd : BddAbove S := by
    refine ⟨n, ?_⟩
    intro q hq
    rcases hq with ⟨Y, hY, rfl⟩
    exact hcc Y
  exact le_csSup hbdd ⟨X, hX, rfl⟩

/-- Relabeling the hard graph does not change the Boolean neighborhood row
read in the relabeled order. -/
private theorem relabeled_row {k n : ℕ} (e : Vertex k ≃ Fin n)
    (π : Equiv.Perm (Fin n)) (v : Vertex k)
    [DecidableRel (graph k).Adj]
    [DecidablePred fun u =>
      u ∈ ((graph k).map e.toEmbedding).neighborSet (e v)] :
    crossingCount π
        (((graph k).map e.toEmbedding).neighborSet (e v)) =
      crossingCountInList ((graph k).Adj v)
        (List.ofFn fun i : Fin n => e.symm (π.symm i)) := by
  rw [crossingCount_eq_crossingCountInList]
  unfold crossingCountInList
  rw [List.map_ofFn, List.map_ofFn]
  apply congrArg changes
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Function.comp_apply]
  simpa using
    (SimpleGraph.map_adj_apply (G := graph k) (f := e.toEmbedding)
      (a := v) (b := e.symm (π.symm i)))

/--
---
conclusion: Lax214022.CographWelzlLowerBound.exists_cograph_requiring_crossingNumber_at_least
---
For each `k`, a cograph with between `3^k` and `4^k` vertices forces at
least `k` crossings in some open-neighborhood row of every order.

# Proof strategy

Use a universal root above three recursive copies.  In any linear order,
one copy avoids the branches of both immediate neighbors of the root.
Restricting the order to that copy preserves the inductive row, while the
universal root is a `true` entry separated from it by `false` entries and
therefore contributes one new crossing.  A binary cotree supplies a
width-zero contraction sequence, and a graph isomorphism relabels the
result onto `Fin n`.

# Attribution

The ternary construction and order obstruction are the standard lower-bound
argument for cograph contiguity due to Crespelle and Gambette.  The present
proof is adapted to crossing counts of open-neighborhood rows.
-/
theorem exists_cograph_requiring_crossingNumber_at_least (k : ℕ) :
    ∃ n : ℕ, 3 ^ k ≤ n ∧ n ≤ 4 ^ k ∧
      ∃ G : SimpleGraph (Fin n), IsCograph G ∧
        ∀ π : Equiv.Perm (Fin n),
          k ≤ crossingNumber (neighborhoodSetSystem G 1) π := by
  classical
  let n := Fintype.card (Vertex k)
  let e : Vertex k ≃ Fin n := Fintype.equivFin (Vertex k)
  let G : SimpleGraph (Fin n) := (graph k).map e.toEmbedding
  refine ⟨n, three_pow_le_card_vertex k, card_vertex_le_four_pow k,
    G, ?_, ?_⟩
  · rcases isCograph_graph k with ⟨S⟩
    exact ⟨mapIsoPartitionSequence (SimpleGraph.Iso.map e (graph k)) S⟩
  · intro π
    let L : List (Vertex k) :=
      List.ofFn fun i : Fin n => e.symm (π.symm i)
    have hL : L.Nodup := by
      rw [List.nodup_ofFn]
      exact e.symm.injective.comp π.symm.injective
    have hall : ∀ v : Vertex k, v ∈ L := by
      intro v
      rw [List.mem_ofFn]
      exact ⟨π (e v), by simp⟩
    obtain ⟨v, hv⟩ := exists_row_with_k_changes k L hL hall
    let X : Set (Fin n) := G.neighborSet (e v)
    have hX : X ∈ neighborhoodSetSystem G 1 := by
      exact ⟨e v, (radius_one_set_eq_neighborSet G (e v)).symm⟩
    calc
      k ≤ crossingCountInList ((graph k).Adj v) L := hv
      _ = crossingCount π X := by
        symm
        exact relabeled_row e π v
      _ ≤ crossingNumber (neighborhoodSetSystem G 1) π :=
        crossingCount_le_crossingNumber _ _ hX

end

end Lax214022Proofs.CographWelzlLowerBound
