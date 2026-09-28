import Lax235315Proofs.Construction.GraphAdaptiveProtocol
import Lax235315Proofs.Construction.RoundPotential
import Mathlib.Tactic

/-! A stopping adaptive graph protocol with the source loop's bit reserve.
The next-state function may depend on all previously sampled blocks. -/

namespace Lax235315Proofs.Construction.GuardedAdaptiveProtocol

open Lax235315Proofs.Construction.AdaptiveBitBlocks
open Lax235315Proofs.Construction.AdaptiveTapeCounting
open Lax235315Proofs.Construction.AdaptiveStateProtocol
open Lax235315Proofs.Construction.GraphAdaptiveProtocol
open Lax235315Proofs.Construction.PositionFailureBits
open Lax235315Proofs.Construction.RoundPotential

noncomputable section

structure GuardedState (n c L : ℕ) extends GraphQueryState n where
  large : 12 * c ^ 2 * L < (Lax235315Proofs.Construction.MarkingMath.activeVertices
    n activeA).card

def width {n c L : ℕ} : Option (GuardedState n c L) → ℕ
  | none => 0
  | some s => queryWidth n L s.toGraphQueryState

def bad {n c L : ℕ} (G : SimpleGraph (Fin n)) (hL : 0 < L) :
    ∀ state : Option (GuardedState n c L), Finset (Tape (width state))
  | none => ∅
  | some s => badBlock G c L hL s.toGraphQueryState

def potential {n c L : ℕ} : Option (GuardedState n c L) → ℕ
  | none => 0
  | some s => 24 * L *
      (Lax235315Proofs.Construction.MarkingMath.activeVertices n s.activeA).card

lemma locallyBounded_guarded_queries {n c L : ℕ}
    {G : SimpleGraph (Fin n)}
    (hc : 1 ≤ c)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hNpow : n ≤ 2 ^ L) (hL : 0 < L)
    (next : ∀ state : Option (GuardedState n c L),
      Tape (width state) → Option (GuardedState n c L)) :
    ∀ R state, LocallyBounded
      (1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n)
      (protocol width (bad G hL) next R state) := by
  apply AdaptiveStateProtocol.locallyBounded
    (width := width) (bad := bad G hL) (next := next)
  intro state
  cases state with
  | none =>
      simp [bad, width]
      positivity
  | some s =>
      simpa [bad, width, queryWidth, badBlock] using
        (badRoundBits_fraction_le s.activeA s.activeB hc s.nonemptyA hG hNpow hL)

/-- Every transition that continues the guarded loop obeys the existing
two-thirds contraction. Rejection and loop exit move to `none`. -/
lemma maxConsumedBits_le_initial_reserve {n c L : ℕ}
    (hL : 1 ≤ L)
    (next : ∀ state : Option (GuardedState n c L),
      Tape (width state) → Option (GuardedState n c L))
    (hstop : ∀ bits, next none bits = none)
    (hshrink : ∀ s bits s', next (some s) bits = some s' →
      (Lax235315Proofs.Construction.MarkingMath.activeVertices n s'.activeA).card ≤
        (Lax235315Proofs.Construction.MarkingMath.activeVertices n s.activeA).card / 2 + c ^ 2)
    (G : SimpleGraph (Fin n)) (hLpos : 0 < L) :
    ∀ R s, maxConsumedBits (protocol width (bad G hLpos) next R (some s)) ≤
      potential (some s) := by
  have hstep : ∀ state bits, width state + potential (next state bits) ≤
      potential state := by
    intro state bits
    cases state with
    | none => simp [width, potential, hstop]
    | some s =>
        cases hnext : next (some s) bits with
        | none =>
            simp [width, potential, queryWidth, hnext]
            nlinarith
        | some s' =>
            have hs := hshrink s bits s' hnext
            have hpay := bit_reserve_step hL s.large hs
            simpa [width, potential, queryWidth, hnext, Nat.mul_assoc,
              Nat.mul_comm, Nat.mul_left_comm] using hpay
  intro R s
  exact AdaptiveStateProtocol.maxConsumedBits_le_potential
    (width := width) (bad := bad G hLpos) (next := next)
    potential hstep R (some s)

/-- The source's initial `24 L n` tape reserve fits every guarded query
tree rooted at any active subset of the `n` vertices. -/
lemma maxConsumedBits_le_tape {n c L T : ℕ}
    (hL : 1 ≤ L) (hreserve : 24 * L * n ≤ T)
    (next : ∀ state : Option (GuardedState n c L),
      Tape (width state) → Option (GuardedState n c L))
    (hstop : ∀ bits, next none bits = none)
    (hshrink : ∀ s bits s', next (some s) bits = some s' →
      (Lax235315Proofs.Construction.MarkingMath.activeVertices n s'.activeA).card ≤
        (Lax235315Proofs.Construction.MarkingMath.activeVertices n s.activeA).card / 2 + c ^ 2)
    (G : SimpleGraph (Fin n)) (hLpos : 0 < L) :
    ∀ R s, maxConsumedBits (protocol width (bad G hLpos) next R (some s)) ≤ T := by
  intro R s
  have hbits := maxConsumedBits_le_initial_reserve hL next hstop hshrink G hLpos R s
  have hcount := Lax235315Proofs.Construction.MarkingMath.activeVertices_card_le n s.activeA
  have hmul := Nat.mul_le_mul_left (24 * L) hcount
  exact hbits.trans (hmul.trans hreserve)

end

end Lax235315Proofs.Construction.GuardedAdaptiveProtocol
