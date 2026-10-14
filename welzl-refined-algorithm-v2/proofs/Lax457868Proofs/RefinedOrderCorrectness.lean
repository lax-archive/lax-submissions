import Lax457868Proofs.ReductionPath
import Lax457868Proofs.RoundReconstruction
import Lax457868Proofs.ListOrderBounds
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
Deterministic reconstruction turns an actual successful reduction path into
a duplicate-free graph order with the stated radius-one crossing bound.
-/

namespace Lax457868Proofs.RefinedOrderCorrectness

open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax457868Proofs.ReductionPath
open Lax457868Proofs.ReductionPath.SuccessfulReductionPath
open Lax457868Proofs.RoundReconstruction
open Lax457868Proofs.ListOrderBounds
open Lax457868Proofs.TwinExpansion

/-- Reconstruct the active ground set by replaying each round's stored
representatives, starting with the terminal retained set. -/
noncomputable def outputOrder {n : ℕ} {G : SimpleGraph (Fin n)}
    {c k : ℕ} {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)} : SuccessfulReductionPath G c k hG A B → List (Fin n)
  | .stop _ => A.toList
  | .step W _ contraction _ tail =>
      reconstructRound G A B W contraction (outputOrder tail)

/-- The reconstructed order has exactly the active ground set as its
underlying finite set. -/
lemma outputToFinset {n : ℕ} {G : SimpleGraph (Fin n)} {c k : ℕ}
    {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)} (path : SuccessfulReductionPath G c k hG A B) :
    (outputOrder path).toFinset = A := by
  induction path with
  | stop hstop =>
      rename_i A0 B0
      change A0.toList.toFinset = A0
      simp
  | step W hsample contraction hcontinue tail ih =>
      rename_i A0 B0
      simpa [outputOrder] using
        reconstructRound_toFinset G A0 B0 W contraction (outputOrder tail) ih

/-- The reconstructed order lists each vertex of its active ground set once. -/
lemma outputNodup {n : ℕ} {G : SimpleGraph (Fin n)} {c k : ℕ}
    {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)} (path : SuccessfulReductionPath G c k hG A B) :
    (outputOrder path).Nodup := by
  induction path with
  | stop hstop =>
      rename_i A0 B0
      simpa [outputOrder] using Finset.nodup_toList A0
  | step W hsample contraction hcontinue tail ih =>
      rename_i A0 B0
      exact reconstructRound_nodup G A0 B0 W contraction (outputOrder tail) ih
        (outputToFinset tail)

/-- Each original neighborhood has crossing count at most `2k` times one
more than the number of contractions in the stored path. -/
lemma output_crossing_bound {n : ℕ} {G : SimpleGraph (Fin n)} {c k : ℕ}
    {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)}
    (path : SuccessfulReductionPath G c k hG A B) :
    ∀ b ∈ B, crossingCount (contains (G.neighborSet b)) (outputOrder path) ≤
      2 * k * (rounds path + 1) := by
  induction path with
  | stop hstop =>
      rename_i A0 B0
      intro b hb
      simp only [outputOrder, rounds, Nat.zero_add, Nat.mul_one]
      calc
        crossingCount (contains (G.neighborSet b)) A0.toList ≤
            A0.toList.length := crossingCount_le_length _ _
        _ ≤ 2 * k := by simpa only [Finset.length_toList] using hstop
  | step W hsample contraction hcontinue tail ih =>
      rename_i A0 B0
      intro b hb
      have hround := reconstructed_crossing_bound (G := G) A0 B0 W hsample contraction
        (outputOrder tail) (outputNodup tail) (outputToFinset tail)
        (fun b hb => ih b hb)
      have h := hround b hb
      calc
        crossingCount (contains (G.neighborSet b))
            (reconstructRound G A0 B0 W contraction (outputOrder tail))
            ≤ 2 * k * (rounds tail + 1) + 2 * k := h
        _ = 2 * k * (rounds tail + 2) := by ring
        _ = 2 * k * (rounds (SuccessfulReductionPath.step W hsample
              contraction hcontinue tail) + 1) := by simp [rounds]

/-- Under the exact refined cutoff, all original neighborhoods obey the
paper's `2k log₂(|A|)` crossing bound. -/
lemma output_crossing_bound_exact {n : ℕ} {G : SimpleGraph (Fin n)}
    {c : ℕ} {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)} (hc : 2 ≤ c) (hA : 2 ≤ A.card)
    (path : SuccessfulReductionPath G c
      (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
      hG A B) :
    ∀ b ∈ B, crossingCount (contains (G.neighborSet b)) (outputOrder path) ≤
      2 * (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1) *
        Nat.clog 2 A.card := by
  have hrounds := refined_path_round_bound hc hA path
  have hbound := output_crossing_bound path
  intro b hb
  exact (hbound b hb).trans (Nat.mul_le_mul_left _ hrounds)

/-- When both sides are the full vertex set, the actual reconstructed list
encodes a radius-one graph Welzl order with the exact cutoff. -/
lemma output_encodes_graphWelzlOrder {n c : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hn : 2 ≤ n)
    (path : SuccessfulReductionPath G c
      (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
      hG Finset.univ Finset.univ) :
    Lax195003.WelzlOrdersInGraphs.EncodesGraphWelzlOrder G 1
      (2 * (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1) *
        Nat.clog 2 n) ((outputOrder path).map Fin.val) := by
  let l := outputOrder path
  have hnodup : l.Nodup := outputNodup path
  have hset : l.toFinset = Finset.univ := outputToFinset path
  have hall : ∀ v : Fin n, v ∈ l := by
    intro v
    have hv : v ∈ l.toFinset := by rw [hset]; simp
    exact List.mem_toFinset.mp hv
  have hlen : l.length = n := by
    have hcard : l.toFinset.card = n := by rw [hset]; simp
    rw [← List.toFinset_card_of_nodup hnodup]
    exact hcard
  have hcross := output_crossing_bound_exact hc (by simpa using hn) path
  have hcross' : ∀ v : Fin n,
      crossingCount (contains (G.neighborSet v)) l ≤
        2 * (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1) *
          Nat.clog 2 n := by
    intro v
    have hv : v ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ v
    simpa [l] using hcross v hv
  exact encodesGraphWelzlOrder_of_list_bound G l hnodup hall hlen hcross'

end Lax457868Proofs.RefinedOrderCorrectness
