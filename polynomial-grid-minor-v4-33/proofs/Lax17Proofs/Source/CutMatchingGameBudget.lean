import Lax17Proofs.Source.CutMatchingGamePeeling
import Lax17Proofs.Source.HairyCrossbarGridExpander

namespace Lax17Proofs

universe u v w

/-!
# Quantitative budget for the cut-matching game

This file isolates the real-valued arithmetic that turns the entropy
increment lower bound into `O(log g)` cut-matching rounds on the `g × g`
coordinate set.
-/

namespace SimpleGraph
namespace CutMatchingGame

open scoped BigOperators

/-- On power-of-two grid-coordinate sets, the natural logarithm of the vertex
count is at most twice the binary logarithm of the grid order.  The estimate is
deliberately coarse: it uses `log 2 <= 1`, which is enough for choosing a
universal phase constant. -/
theorem real_log_card_gridVertex_le_two_natLog
    {g : ℕ} (hpow : CrossbarContract.IsPowerOfTwo g) :
    Real.log (Fintype.card (GridVertex g) : ℝ) ≤
      2 * (Nat.log 2 g : ℝ) := by
  rcases hpow with ⟨r, rfl⟩
  rw [card_gridVertex]
  have hpow_nat : 2 ^ r * 2 ^ r = 2 ^ (2 * r) := by
    rw [← pow_add]
    congr
    omega
  rw [hpow_nat]
  have hlog :
      Real.log ((2 ^ (2 * r) : ℕ) : ℝ) =
        (2 * r : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hnatlog : Nat.log 2 (2 ^ r) = r :=
    Nat.log_pow (by decide : 1 < 2) r
  have hlogtwo_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    norm_num at h
    exact h
  rw [hlog, hnatlog]
  nlinarith [hlogtwo_le_one]

/-- There is a positive phase constant large enough to dominate the reciprocal
of the entropy gap. -/
theorem exists_phaseRoundConstant :
    ∃ C : ℕ, 0 < C ∧ 64 < entropyGapConstant * (C : ℝ) := by
  have hgap : 0 < entropyGapConstant := entropyGapConstant_pos
  rcases exists_nat_gt (64 / entropyGapConstant) with ⟨C, hC⟩
  refine ⟨max 1 C, by omega, ?_⟩
  have hCle : (C : ℝ) ≤ (max 1 C : ℕ) := by
    exact_mod_cast le_max_right 1 C
  have hCmul : 64 < entropyGapConstant * (C : ℝ) := by
    have h := (div_lt_iff₀ hgap).mp hC
    nlinarith
  exact hCmul.trans_le (by
    exact mul_le_mul_of_nonneg_left hCle (le_of_lt hgap))

/-- A phase constant satisfying `64 < gap*C` gives the entropy budget needed
for one `c=1/4` phase on a power-of-two `g × g` coordinate set. -/
theorem gridVertex_phase_budget
    {C g : ℕ}
    (hC : 64 < entropyGapConstant * (C : ℝ))
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g) :
    (Fintype.card (GridVertex g) : ℝ) *
        Real.log (Fintype.card (GridVertex g) : ℝ) <
      sparseCutRoundIncrement (GridVertex g) 1 4 *
        ((C * Nat.log 2 g : ℕ) : ℝ) := by
  have hNpos_nat : 0 < Fintype.card (GridVertex g) :=
    by
      rw [card_gridVertex]
      nlinarith
  have hNpos : 0 < (Fintype.card (GridVertex g) : ℝ) := by
    exact_mod_cast hNpos_nat
  have hLpos_nat : 0 < Nat.log 2 g :=
    Nat.log_pos (by decide : 1 < 2) hg
  have hLpos : 0 < (Nat.log 2 g : ℝ) := by
    exact_mod_cast hLpos_nat
  have hlog_bound :=
    real_log_card_gridVertex_le_two_natLog hpow
  have hgap_pos : 0 < entropyGapConstant := entropyGapConstant_pos
  have hright_gt :
      2 * (Nat.log 2 g : ℝ) <
        entropyGapConstant * ((C * Nat.log 2 g : ℕ) : ℝ) / 32 := by
    have hcast :
        ((C * Nat.log 2 g : ℕ) : ℝ) =
          (C : ℝ) * (Nat.log 2 g : ℝ) := by
      norm_num
    rw [hcast]
    nlinarith [hC, hLpos]
  calc
    (Fintype.card (GridVertex g) : ℝ) *
        Real.log (Fintype.card (GridVertex g) : ℝ)
        ≤ (Fintype.card (GridVertex g) : ℝ) *
            (2 * (Nat.log 2 g : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlog_bound (le_of_lt hNpos)
    _ < (Fintype.card (GridVertex g) : ℝ) *
          (entropyGapConstant *
            ((C * Nat.log 2 g : ℕ) : ℝ) / 32) := by
          exact mul_lt_mul_of_pos_left hright_gt hNpos
    _ = sparseCutRoundIncrement (GridVertex g) 1 4 *
          ((C * Nat.log 2 g : ℕ) : ℝ) := by
          unfold sparseCutRoundIncrement
          ring_nf

/-- The `g × g` coordinate set has even cardinality when `g` is a power of two
and `2 <= g`. -/
theorem two_mul_half_card_gridVertex_of_isPowerOfTwo
    {g : ℕ} (hg : 2 ≤ g) (hpow : CrossbarContract.IsPowerOfTwo g) :
    2 * (Fintype.card (GridVertex g) / 2) =
      Fintype.card (GridVertex g) := by
  rcases hpow with ⟨r, rfl⟩
  cases r with
  | zero =>
      norm_num at hg
  | succ r =>
      rw [card_gridVertex]
      have hdiv : (2 ^ (r * 2) * 4) / 2 = 2 ^ (r * 2) * 2 := by
        omega
      ring_nf
      omega

/-- Abstract fixed-round cut-matching theorem on `GridVertex g`: for a
universal constant `cRound`, every sequential matching responder admits a
prefix of at most `cRound * log_2 g` rounds whose matching union is a
half-edge-expander. -/
theorem exists_gridVertex_fixedRound_list_halfExpander :
    ∃ cRound : ℕ, 0 < cRound ∧
      ∀ {g : ℕ}, 2 ≤ g → CrossbarContract.IsPowerOfTwo g →
        ∀ _responder : SequentialResponder (GridVertex g),
          ∃ rounds : List (LazyRound (GridVertex g)),
            rounds.length ≤ cRound * Nat.log 2 g ∧
              IsHalfEdgeExpander rounds := by
  rcases exists_phaseRoundConstant with ⟨C, hCpos, hC⟩
  refine ⟨16 * C + 1, by omega, ?_⟩
  intro g hg hpow responder
  let k := C * Nat.log 2 g
  have hm :
      2 * (Fintype.card (GridVertex g) / 2) =
        Fintype.card (GridVertex g) :=
    two_mul_half_card_gridVertex_of_isPowerOfTwo hg hpow
  have hn : 0 < Fintype.card (GridVertex g) := by
    rw [card_gridVertex]
    nlinarith
  have hbudget :
      (Fintype.card (GridVertex g) : ℝ) *
          Real.log (Fintype.card (GridVertex g) : ℝ) <
        sparseCutRoundIncrement (GridVertex g) 1 4 * (k : ℝ) := by
    simpa [k] using gridVertex_phase_budget hC hg hpow
  rcases exists_list_halfExpander_of_sixteen_phases_and_peeling
      (X := GridVertex g)
      (m := Fintype.card (GridVertex g) / 2)
      hm responder k hn hbudget with
    ⟨rounds, hlen, hhalf⟩
  refine ⟨rounds, ?_, hhalf⟩
  have hLpos : 0 < Nat.log 2 g :=
    Nat.log_pos (by decide : 1 < 2) hg
  rw [hlen]
  dsimp [k]
  nlinarith

/-- Exact fixed-round version of the abstract cut-matching theorem on
`GridVertex g`.  The additional `FollowsResponder` conclusion records that the
returned transcript really uses the supplied responder at each global round
index; this is the bookkeeping needed for the transported crossbar bridge. -/
theorem exists_gridVertex_fixedRound_exact_list_halfExpander :
    ∃ cRound : ℕ, 0 < cRound ∧
      ∀ {g : ℕ}, 2 ≤ g → CrossbarContract.IsPowerOfTwo g →
        ∀ responder : SequentialResponder (GridVertex g),
          ∃ rounds : List (LazyRound (GridVertex g)),
            rounds.length = cRound * Nat.log 2 g ∧
              IsHalfEdgeExpander rounds ∧
                FollowsResponder responder 0 rounds := by
  rcases exists_phaseRoundConstant with ⟨C, hCpos, hC⟩
  refine ⟨16 * C + 1, by omega, ?_⟩
  intro g hg hpow responder
  let L := Nat.log 2 g
  let k := C * L
  let m := Fintype.card (GridVertex g) / 2
  have hm : 2 * m = Fintype.card (GridVertex g) :=
    two_mul_half_card_gridVertex_of_isPowerOfTwo hg hpow
  have hn : 0 < Fintype.card (GridVertex g) := by
    rw [card_gridVertex]
    nlinarith
  have hbudget :
      (Fintype.card (GridVertex g) : ℝ) *
          Real.log (Fintype.card (GridVertex g) : ℝ) <
        sparseCutRoundIncrement (GridVertex g) 1 4 * (k : ℝ) := by
    simpa [k, L] using gridVertex_phase_budget hC hg hpow
  let phaseRounds :=
    sparseCutPlayMany (X := GridVertex g) 1 4 m hm responder k 16
  have hbal :
      IsBalancedEdgeExpanderWith (X := GridVertex g) phaseRounds 1 4 4 1 := by
    simpa [phaseRounds] using
      sparseCutPlayMany_balancedExpander_four_of_potential_budget
        (X := GridVertex g) hm responder k hn hbudget
  rcases exists_final_bisection_halfExpander_of_balancedExpander_four
      (X := GridVertex g) (rounds := phaseRounds) hm hbal hn responder (16 * k)
    with ⟨B, hcoreHalf⟩
  let coreRounds := phaseRounds ++ [LazyRound.ofResponder responder (16 * k) B]
  let roundBound := (16 * C + 1) * L
  let padding :=
    fillerRounds (X := GridVertex g) hm responder coreRounds.length
      (roundBound - coreRounds.length)
  refine ⟨coreRounds ++ padding, ?_, ?_, ?_⟩
  · have hphaseLen : phaseRounds.length = 16 * k := by
      simpa [phaseRounds] using
        sparseCutPlayMany_length (X := GridVertex g) 1 4 m hm responder k 16
    have hcoreLen : coreRounds.length = 16 * k + 1 := by
      simp [coreRounds, hphaseLen]
    have hLpos : 0 < L :=
      Nat.log_pos (by decide : 1 < 2) hg
    have hcoreLe : coreRounds.length ≤ roundBound := by
      have hcoreLen' : coreRounds.length = 16 * C * L + 1 := by
        rw [hcoreLen]
        dsimp [k]
        ring
      have hroundBound : roundBound = 16 * C * L + L := by
        dsimp [roundBound]
        ring
      rw [hcoreLen', hroundBound]
      omega
    calc
      (coreRounds ++ padding).length = coreRounds.length + padding.length := by
        rw [List.length_append]
      _ = coreRounds.length + (roundBound - coreRounds.length) := by
        rw [fillerRounds_length]
      _ = roundBound := Nat.add_sub_of_le hcoreLe
      _ = (16 * C + 1) * Nat.log 2 g := by
        rfl
  · exact hcoreHalf.append
  · have hphaseFollow :
        FollowsResponder responder 0 phaseRounds := by
      simpa [phaseRounds] using
        sparseCutPlayMany_followsResponder (X := GridVertex g)
          1 4 m hm responder k 16
    have hphaseLen : phaseRounds.length = 16 * k := by
      simpa [phaseRounds] using
        sparseCutPlayMany_length (X := GridVertex g) 1 4 m hm responder k 16
    have hsingle :
        FollowsResponder responder phaseRounds.length
          [LazyRound.ofResponder responder (16 * k) B] := by
      simpa [hphaseLen] using
        followsResponder_singleton (X := GridVertex g) responder (16 * k) B
    have hcoreFollow :
        FollowsResponder responder 0 coreRounds := by
      change
        FollowsResponder responder 0
          (phaseRounds ++ [LazyRound.ofResponder responder (16 * k) B])
      exact
        followsResponder_append (X := GridVertex g) (offset := 0)
          (rounds := phaseRounds)
          (extra := [LazyRound.ofResponder responder (16 * k) B])
          hphaseFollow (by simpa using hsingle)
    have hpaddingFollow :
        FollowsResponder responder (0 + coreRounds.length) padding := by
      simpa [padding] using
        fillerRounds_followsResponder (X := GridVertex g) hm responder
          coreRounds.length (roundBound - coreRounds.length)
    change FollowsResponder responder 0 (coreRounds ++ padding)
    exact
      followsResponder_append (X := GridVertex g) (offset := 0)
        (rounds := coreRounds) (extra := padding)
        hcoreFollow hpaddingFollow

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
