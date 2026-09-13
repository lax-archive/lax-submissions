import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Arithmetic for Chuzhoy Lemma 7.5

This module isolates the natural-number arithmetic in the proof of Lemma 7.5.
All fractional bounds from the source are denominator-cleared, and no graph
structure is used here.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75

/-- The `7/8` boundary contraction in the main iteration of Lemma 7.5.

The retained old augmented boundary has mass at most `3n/4`, the new cut
contributes at most `n/8` endpoints, and the new augmented boundary is covered
by those two parts. -/
theorem eight_mul_newBoundary_le_seven_mul_oldBoundary
    {n retained cutEndpoints newBoundary : ℕ}
    (hretained : 4 * retained ≤ 3 * n)
    (hcutEndpoints : 8 * cutEndpoints ≤ n)
    (hnewBoundary : newBoundary ≤ retained + cutEndpoints) :
    8 * newBoundary ≤ 7 * n := by
  omega

/-- The lower boundary estimate in the same Lemma 7.5 iteration.

The chosen side retains at least half of the old augmented boundary, and every
retained old-boundary vertex belongs to the new augmented boundary. -/
theorem oldBoundary_le_two_mul_newBoundary
    {n retained newBoundary : ℕ}
    (hretained : n ≤ 2 * retained)
    (hretained_le : retained ≤ newBoundary) :
    n ≤ 2 * newBoundary := by
  omega

/-- The denominator-cleared budget update in the proof of Observation 7.7.

The source assigns budget `1/8` to each current augmented-boundary vertex and
unit budget to each deleted edge.  After multiplying the invariant by eight,
the discarded old mass pays for one new endpoint and eight units for each new
cut edge; the violating-cut bound supplies the required factor nine. -/
theorem denominator_cleared_budget_update
    {oldMass retained discarded newMass newCutEndpoints cutEdges deleted
      budget : ℕ}
    (hsplit : oldMass = retained + discarded)
    (hnewMass : newMass ≤ retained + newCutEndpoints)
    (hnewCutEndpoints : newCutEndpoints ≤ cutEdges)
    (hcutEdges : 9 * cutEdges ≤ discarded)
    (hbudget : oldMass + 8 * deleted ≤ budget) :
    newMass + 8 * (deleted + cutEdges) ≤ budget := by
  omega

/-- Pure current-mass arithmetic at a last half-threshold crossing.

Immediately before the selected iteration the current augmented-boundary mass
is above half of the initial mass, while the next mass is at least half of the
current mass and is no longer above half of the initial mass.  Thus the next
current mass lies between one quarter and three quarters of the initial mass.

These inequalities alone do *not* make the resulting cut quarter-balanced
with respect to the original augmented boundary: the next augmented boundary
may contain new cut endpoints.  The repaired Observation 7.7 argument instead
tracks original terminals through a three-quarter crossing. -/
theorem quarter_balance_bounds_of_last_half_crossing
    {initialMass oldMass newMass : ℕ}
    (hbefore : initialMass < 2 * oldMass)
    (hretained : oldMass ≤ 2 * newMass)
    (hafter : 2 * newMass ≤ initialMass) :
    initialMass ≤ 4 * newMass ∧ 4 * newMass ≤ 3 * initialMass := by
  omega

/-- The final cut-size estimate in Observation 7.7.

The candidate `1/4`-balanced cut is contained in the accumulated deleted-edge
set.  The denominator-cleared budget invariant therefore bounds it by one
eighth of the initial boundary mass, contradicting the strict lower bound
assumed for every such balanced cut. -/
theorem eight_mul_cutEdges_le_initialMass_of_budget
    {initialMass newMass deleted cutEdges : ℕ}
    (hcutEdges : cutEdges ≤ deleted)
    (hbudget : newMass + 8 * deleted ≤ initialMass) :
    8 * cutEdges ≤ initialMass := by
  omega

end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
