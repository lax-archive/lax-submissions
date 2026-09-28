import Lax235315Proofs.Construction.PositionFailureBounds
import Lax235315Proofs.Construction.RandomKeyEquiv
import Mathlib.Tactic

/-! Count bad source bit blocks by the exact equivalence with finite key
assignments on active scan positions. -/

namespace Lax235315Proofs.Construction.PositionFailureBits

open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax235315Proofs.Construction.PositionFailureBounds
open Lax235315Proofs.Construction.KeyFailureBounds
open Lax235315Proofs.Construction.FiniteRandomKeys
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.ScanSampleTransport
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.Sampling

noncomputable section

def badRoundBits (a L s : ℕ) (hL : 0 < L)
    (badSamples : Finset (Finset (Fin a))) :
    Finset (Fin ((a * 8) * L) → Bool) :=
  Finset.univ.filter fun ρ =>
    roundAssignmentEquiv a L hL ρ ∈
      failingAssignments ((2 ^ L) ^ 8) s badSamples

lemma card_badRoundBits (a L s : ℕ) (hL : 0 < L)
    (badSamples : Finset (Finset (Fin a))) :
    (badRoundBits a L s hL badSamples).card =
      (failingAssignments ((2 ^ L) ^ 8) s badSamples).card := by
  classical
  let e := roundAssignmentEquiv a L hL
  have himage : (badRoundBits a L s hL badSamples).image e =
      failingAssignments ((2 ^ L) ^ 8) s badSamples := by
    ext f
    constructor
    · intro hf
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hf
      exact (Finset.mem_filter.mp hρ).2
    · intro hf
      apply Finset.mem_image.mpr
      refine ⟨e.symm f, ?_, by simp [e]⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e] using hf⟩
  calc
    (badRoundBits a L s hL badSamples).card =
        ((badRoundBits a L s hL badSamples).image e).card := by
          rw [Finset.card_image_of_injective _ e.injective]
    _ = _ := by rw [himage]

lemma card_allAssignments_eq_pow_bits (a L : ℕ) (hL : 0 < L) :
    (allAssignments (Fin a) ((2 ^ L) ^ 8)).card = 2 ^ ((a * 8) * L) := by
  have hcard := Fintype.card_congr (roundAssignmentEquiv a L hL)
  rw [card_allAssignments]
  simpa using hcard.symm

/-- The concrete bad-block event consumes at most the paper's one-round
rational failure budget of the entire Boolean block space. -/
lemma badRoundBits_fraction_le {n c L : ℕ} {G : SimpleGraph (Fin n)}
    (activeA activeB : ℕ → ℕ) (hc : 1 ≤ c)
    (hA : (activeFinset (n := n) activeA).Nonempty)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hNpow : n ≤ 2 ^ L) (hL : 0 < L) :
    let A := activeFinset (n := n) activeA
    let B := activeFinset (n := n) activeB
    let bad := familyBadSamples (traceFamily G A B) id A c L
    let a := (activeVertices n activeA).card
    let s := sampleSize A.card c
    let badPositions := badPositionSamples activeA n bad
    ((badRoundBits a L s hL badPositions).card : ℚ) ≤
      (1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n) * (2 : ℚ) ^ ((a * 8) * L) := by
  dsimp
  let A := activeFinset (n := n) activeA
  let B := activeFinset (n := n) activeB
  let a := (activeVertices n activeA).card
  let s := sampleSize A.card c
  let bad := familyBadSamples (traceFamily G A B) id A c L
  let badPositions := badPositionSamples activeA n bad
  have hfrac := position_assignment_failure_le activeA activeB hc hA hG hNpow
  have htot : (allAssignments (Fin a) ((2 ^ L) ^ 8)).card = 2 ^ ((a * 8) * L) :=
    card_allAssignments_eq_pow_bits a L hL
  have htotpos : (0 : ℚ) < (allAssignments (Fin a) ((2 ^ L) ^ 8)).card := by
    rw [htot]
    positivity
  have hcross := (div_le_iff₀ htotpos).mp hfrac
  rw [card_badRoundBits]
  simpa [htot, A, B, a, s, bad, badPositions] using hcross

end

end Lax235315Proofs.Construction.PositionFailureBits
