import Lax17Proofs.Source.TreewidthSparsifierThinningUnion

namespace Lax17Proofs

universe u v w

/-!
# A single quotient-cut-preserving thinning outcome

The restart count below is deliberately generous.  It keeps the source
`O(log h)` bound while making the finite Karger union-bound arithmetic
transparent over natural numbers.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open ChekuriChuzhoySection5TerminalSkeleton
open ThinningUnion


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

/-- Explicit number of independent half-expander blocks used in Theorem 5.1. -/
def restartCount (h : ℕ) : ℕ :=
  4096 * (Nat.log 2 h + 1)

theorem restartCount_half (h : ℕ) :
    restartCount h / 2 = 2048 * (Nat.log 2 h + 1) := by
  unfold restartCount
  rw [show 4096 * (Nat.log 2 h + 1) =
      (2048 * (Nat.log 2 h + 1)) * 2 by ring]
  simp

theorem restartCount_half_pos (h : ℕ) :
    0 < restartCount h / 2 := by
  rw [restartCount_half]
  positivity

/-- The numerical capacity which pays simultaneously for Karger's number of
cuts at scale `a` and the geometric union bound. -/
theorem restartCount_failure_capacity
    {h a : ℕ} (hh : 2 ≤ h) (ha : 0 < a) :
    (2 * h ^ (2 * (a + 1))) * 2 ^ (a + 2) ≤
      4 ^ ((a * (restartCount h / 2)) / 128 + 1) := by
  let L := Nat.log 2 h + 1
  have hL : 0 < L := by
    simp [L]
  have hhpow : h ≤ 2 ^ L := by
    exact (Nat.lt_pow_succ_log_self (by norm_num) h).le
  have hpow :
      h ^ (2 * (a + 1)) ≤
        (2 ^ L) ^ (2 * (a + 1)) :=
    Nat.pow_le_pow_left hhpow _
  have hC :
      restartCount h / 2 = 2048 * L := by
    simp [restartCount_half, L]
  have hdiv :
      (a * (2048 * L)) / 128 = 16 * a * L := by
    have heq :
        a * (2048 * L) = 128 * (16 * a * L) := by ring
    rw [heq]
    simp
  have hexp :
      1 + L * (2 * (a + 1)) + (a + 2) ≤
        2 * (16 * a * L + 1) := by
    nlinarith
  calc
    (2 * h ^ (2 * (a + 1))) * 2 ^ (a + 2) ≤
        (2 * (2 ^ L) ^ (2 * (a + 1))) *
          2 ^ (a + 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hpow)
    _ = 2 ^ (1 + L * (2 * (a + 1)) + (a + 2)) := by
      rw [← pow_mul]
      change
        2 ^ 1 * 2 ^ (L * (2 * (a + 1))) * 2 ^ (a + 2) =
          2 ^ (1 + L * (2 * (a + 1)) + (a + 2))
      rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ (2 * (16 * a * L + 1)) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    _ = 4 ^ (16 * a * L + 1) := by
      rw [pow_mul]
      norm_num
    _ = 4 ^ ((a * (restartCount h / 2)) / 128 + 1) := by
      rw [hC, hdiv]

namespace BuildState.ExpanderBlocks

/-- One degree-three thinning outcome preserves every nontrivial cut of the
whole-rail quotient up to the explicit factor `128`. -/
theorem exists_quotient_cut_preserving_outcome
    (E : ExpanderBlocks P count)
    (hcount : count = restartCount h)
    (hheight : 2 ≤ h)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) :
    ∃ outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget),
      ∀ S : Finset (Fin h),
        S.Nonempty → S ≠ Finset.univ →
          ((E.railQuotient hbudget fallback
              (E.assembledSupport hbudget)).boundary S).card / 128 ≤
            ((E.railQuotient hbudget fallback
              ((E.blueThinningInput hbudget).thinnedGraph outcome)).boundary
                S).card := by
  classical
  let H := E.assembledSupport hbudget
  let owner := E.railOwner hbudget fallback
  let I := E.blueThinningInput hbudget
  let Q := ownerQuotient H owner
  let Q' :
      BlueThinningInput.Outcome (H := H) →
        FiniteEdgeIndexedGraph (Fin h) :=
    fun outcome => ownerQuotient (I.thinnedGraph outcome) owner
  let C := count / 2
  have hC : 0 < C := by
    dsimp [C]
    rw [hcount]
    exact restartCount_half_pos h
  have hconn : Q.IsEdgeConnected C := by
    exact E.railQuotient_isEdgeConnected hbudget fallback
  have htail :
      ∀ S ∈ ThinningUnion.nontrivialCuts,
        (ThinningUnion.badForCut Q Q' 128 S).card *
            4 ^ ((Q.boundary S).card / 128 + 1) ≤
          Fintype.card
            (BlueThinningInput.Outcome (H := H)) := by
    intro S _hS
    have hfixed :=
      E.quotientBoundary_bad_mul_failureFactor_le_total
        hbudget fallback S
    simpa [H, owner, I, Q, Q',
      ThinningUnion.badForCut] using hfixed
  have hcapacity :
      ∀ a, 0 < a →
        (ThinningUnion.scaleCuts Q C a).card * 2 ^ (a + 2) ≤
          4 ^ ((a * C) / 128 + 1) := by
    intro a ha
    have hscaleSmall :=
      ThinningUnion.card_scaleCuts_le_smallCuts
        (a := a) Q hC
    have hkarger :=
      Karger.card_smallCuts_le_two_mul_vertexCard_pow_all
        Q hC (by omega : 0 < a + 1) hconn
        (by simpa using hheight)
    have hscale :
        (ThinningUnion.scaleCuts Q C a).card ≤
          2 * h ^ (2 * (a + 1)) := by
      exact hscaleSmall.trans (by simpa using hkarger)
    have hnum :=
      restartCount_failure_capacity hheight ha
    rw [← hcount] at hnum
    exact (Nat.mul_le_mul_right _ hscale).trans hnum
  have hall :=
    ThinningUnion.exists_outcome_preserving_all_cuts
      Q Q' hC (by norm_num : 0 < 128) hconn htail hcapacity
  simpa [H, owner, I, Q, Q', C] using hall

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
