/-
**The pieces of the record-breaker decomposition as pieces of the chain of
stage 1.**

`RequestProject/PartC/SnakePieceIdent.lean` identifies the pieces of the
record-breaker decomposition -- the two halves of each excursion of a
record-breaking column, the progress parts and the final piece -- with the whole
runs of window transducers, and reads off their outputs.  This file repeats that
identification in the form that the chain of stage 1 needs: the packages
`Transducers.TwoWay.Chk.CrossOK` and `Transducers.TwoWay.Chk.HaltOK` of
`RequestProject/PartC/SnakeChkCross.lean`, which record the window condition
together with the cuts and the states at the two ends of the piece.

It also names the two times that delimit the `r`-th piece slot of the pair `i`
(`Transducers.TwoWay.Chk.pcStart` and `Transducers.TwoWay.Chk.pcEnd`) and proves
that consecutive slots meet: that is what makes the pieces a chain.
-/
import Lax916827Proofs.Source.PartC.SnakeChkCross
import Lax916827Proofs.Source.PartC.SnakeData
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

variable {A B Q : Type} {M : TwoWay A B Q} {w : List A} {T K : ℕ}

/-! ## The times of the piece slots -/

/-- The time at which the `r`-th piece of the pair `i` starts: the `2j`-th slot
is the first half of the `j`-th excursion of the `i`-th record-breaking column,
the `2j+1`-st slot its second half, and the `2K`-th slot the progress part. -/
noncomputable def pcStart (M : TwoWay A B Q) (w : List A) (K i r : ℕ) : ℕ :=
  if r = 2 * K then rbLast M w i
  else if r % 2 = 0 then excT M w i (r / 2) else excS M w i (r / 2)

/-- The time at which the `r`-th piece of the pair `i` ends.  The last piece of
the last pair halts, so for it the end time is set to the start time. -/
noncomputable def pcEnd (M : TwoWay A B Q) (w : List A) (K i r : ℕ) : ℕ :=
  if r = 2 * K then (if i < rbN M w then rbFirst M w (i + 1) else rbLast M w i)
  else if r % 2 = 0 then excS M w i (r / 2) else excT M w i (r / 2 + 1)

lemma pcStart_zero (hK : 0 < K) (i : ℕ) : pcStart M w K i 0 = rbFirst M w i := by
  rw [pcStart, if_neg (by omega), if_pos (by omega)]
  exact excT_zero i

/-- Consecutive pieces of a pair meet in time. -/
lemma pcEnd_succ (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w K) {i r : ℕ}
    (hr : r < 2 * K) : pcEnd M w K i r = pcStart M w K i (r + 1) := by
  rw [pcEnd, if_neg (by omega)]
  by_cases hpar : r % 2 = 0
  · rw [if_pos hpar, pcStart, if_neg (by omega), if_neg (by omega),
      show (r + 1) / 2 = r / 2 from by omega]
  · rw [if_neg hpar, pcStart]
    by_cases hlast : r + 1 = 2 * K
    · rw [if_pos hlast, show r / 2 + 1 = K from by omega]
      exact excT_stab hT hwidth i
    · rw [if_neg hlast, if_pos (by omega), show (r + 1) / 2 = r / 2 + 1 from by omega]

/-- The last piece of a pair and the first piece of the next one meet in time. -/
lemma pcEnd_pair (hK : 0 < K) {i : ℕ} (hi : i < rbN M w) :
    pcEnd M w K i (2 * K) = pcStart M w K (i + 1) 0 := by
  rw [pcEnd, if_pos rfl, if_pos hi, pcStart_zero hK]

/-! ## The two halves of an excursion -/

/-- **The two halves of an excursion of a record-breaking column are two pieces
of the chain**, on the window delimited by the record-breaking column and the
column furthest from it that the excursion reaches. -/
theorem exists_crossOK_exc (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w K)
    (hK : 2 ≤ K) (i j : ℕ) :
    ∃ p₁ p₂ : PieceParam A Q,
      CrossOK M w (K - 1) (excT M w i j) (excS M w i j)
          (min (rbCol M w i) (excC M w i j)) (max (rbCol M w i) (excC M w i j)) p₁ ∧
        CrossOK M w (K - 1) (excS M w i j) (excT M w i (j + 1))
          (min (rbCol M w i) (excC M w i j)) (max (rbCol M w i) (excC M w i j)) p₂ := by
  classical
  have hab : excT M w i j ≤ excT M w i (j + 1) := excT_mono_step i j
  have has : excT M w i j ≤ excS M w i j := (excS_bounds i j).1
  have hsb : excS M w i j ≤ excT M w i (j + 1) := (excS_bounds i j).2
  have hbE : excT M w i (j + 1) ≤ endT M w := le_trans (excT_le i (j + 1)) (rbLast_le_endT i)
  have hpa : traj M w (excT M w i j) = rbCol M w i := pos_excT i j
  have hpb : traj M w (excT M w i (j + 1)) = rbCol M w i := pos_excT i (j + 1)
  have hps : traj M w (excS M w i j) = excC M w i j := Walk.pos_excSplit hab
  have hposA : posAt M w (excT M w i j) = some (rbCol M w i) := by
    rw [posAt_traj hT (le_trans hab hbE), hpa]
  have hposB : posAt M w (excT M w i (j + 1)) = some (rbCol M w i) := by
    rw [posAt_traj hT hbE, hpb]
  have hposS : posAt M w (excS M w i j) = some (excC M w i j) := by
    rw [posAt_traj hT (le_trans hsb hbE), hps]
  have hhalves := excHalves_visitsLe hT hwidth hK i j
  have hmid : ∀ t, excT M w i j < t → t < excT M w i (j + 1) → traj M w t ≠ rbCol M w i :=
    fun t h1 h2 => Walk.visSeq_no_mid h1 h2
  have key : (∀ t, excT M w i j ≤ t → t ≤ excT M w i (j + 1) →
        min (rbCol M w i) (excC M w i j) ≤ traj M w t ∧
          traj M w t ≤ max (rbCol M w i) (excC M w i j)) ∧
      (excT M w i j < excS M w i j ∨ excT M w i j = excT M w i (j + 1)) := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · have hseq : excS M w i j = excT M w i j := by omega
      have hcol : excC M w i j = rbCol M w i := by rw [← hps, hseq, hpa]
      refine ⟨?_, Or.inr heq⟩
      intro t h1 h2
      have ht : t = excT M w i j := by omega
      rw [ht, hpa, hcol]
      simp
    · have hwalk := isWalk_trajE M w hT
      have hab2 : excT M w i j + 1 < excT M w i (j + 1) := by
        rcases eq_or_lt_of_le (show excT M w i j + 1 ≤ excT M w i (j + 1) from hlt) with h | h
        · exfalso
          rcases hwalk (excT M w i j) (by omega) with hst | hst <;> rw [← h] at hpb <;> omega
        · exact h
      rcases Walk.loop_one_sided hwalk hbE hpa hmid with hside | hside
      · have hcol : excC M w i j = Walk.excMax (traj M w) (excT M w i j) (excT M w i (j + 1)) :=
          Walk.excCol_right hwalk hbE hlt hpa hpb hside
        have hrange : ∀ t, excT M w i j ≤ t → t ≤ excT M w i (j + 1) →
            rbCol M w i ≤ traj M w t ∧ traj M w t ≤ excC M w i j := by
          intro t h1 h2
          rw [hcol]
          exact Walk.exc_range_right hab hpa hpb hside h1 h2
        have hltc : rbCol M w i < excC M w i j := by
          have h1 := hside (excT M w i j + 1) (by omega) (by omega)
          have h2 := (hrange (excT M w i j + 1) (by omega) (by omega)).2
          omega
        refine ⟨fun t h1 h2 => ?_, Or.inl ?_⟩
        · have h := hrange t h1 h2
          rw [min_eq_left (le_of_lt hltc), max_eq_right (le_of_lt hltc)]
          exact h
        · rcases eq_or_lt_of_le has with h | h
          · exfalso; rw [← h] at hps; omega
          · exact h
      · have hcol : excC M w i j = Walk.excMin (traj M w) (excT M w i j) (excT M w i (j + 1)) :=
          Walk.excCol_left hwalk hbE hlt hpa hpb hside
        have hrange : ∀ t, excT M w i j ≤ t → t ≤ excT M w i (j + 1) →
            excC M w i j ≤ traj M w t ∧ traj M w t ≤ rbCol M w i := by
          intro t h1 h2
          rw [hcol]
          exact Walk.exc_range_left hab hpa hpb hside h1 h2
        have hltc : excC M w i j < rbCol M w i := by
          have h1 := hside (excT M w i j + 1) (by omega) (by omega)
          have h2 := (hrange (excT M w i j + 1) (by omega) (by omega)).1
          omega
        refine ⟨fun t h1 h2 => ?_, Or.inl ?_⟩
        · have h := hrange t h1 h2
          rw [min_eq_right (le_of_lt hltc), max_eq_left (le_of_lt hltc)]
          exact h
        · rcases eq_or_lt_of_le has with h | h
          · exfalso; rw [← h] at hps; omega
          · exact h
  obtain ⟨hrange, hS⟩ := key
  obtain ⟨p₁, hp₁⟩ := exists_crossOK M w has hposA hposS
    (fun t h1 h2 => ⟨traj M w t, posAt_traj hT (by omega), hrange t h1 (by omega)⟩)
    (fun t h1 h2 hcon => by
      rw [posAt_traj hT (by omega)] at hcon
      exact Walk.excSplit_first hab h1 h2 (by simpa using hcon))
    hhalves.1
  obtain ⟨p₂, hp₂⟩ := exists_crossOK M w hsb hposS hposB
    (fun t h1 h2 => ⟨traj M w t, posAt_traj hT (by omega), by
      rw [min_comm (excC M w i j), max_comm (excC M w i j)]
      exact hrange t (by omega) h2⟩)
    (fun t h1 h2 hcon => by
      rw [posAt_traj hT (by omega)] at hcon
      have hne : excT M w i j < t := by omega
      exact hmid t hne h2 (by simpa using hcon))
    hhalves.2
  rw [min_comm (excC M w i j), max_comm (excC M w i j)] at hp₂
  exact ⟨p₁, p₂, hp₁, hp₂⟩

/-! ## The progress part -/

/-- **The progress part of a record-breaking column that is not the last one is a
piece of the chain**, on the window between that record-breaking column and the
next one. -/
theorem exists_crossOK_prog (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w K)
    (hK : 2 ≤ K) {i : ℕ} (hi : i < rbN M w) :
    ∃ p : PieceParam A Q, CrossOK M w (K - 1) (rbLast M w i) (rbFirst M w (i + 1))
      (rbCol M w i) (rbCol M w (i + 1)) p := by
  classical
  have hwalk := isWalk_trajE M w hT
  have hns : ¬ Walk.RecStable (traj M w) 0 (endT M w) i := Walk.not_recStable_of_lt_recN hi
  have hab : rbLast M w i ≤ rbFirst M w (i + 1) := Walk.recLast_le_recFirst_succ hns
  have haE : rbLast M w i ≤ endT M w := rbLast_le_endT i
  have hbE : rbFirst M w (i + 1) ≤ endT M w := rbFirst_le_endT (i + 1)
  have hpa : traj M w (rbLast M w i) = rbCol M w i := pos_rbLast i
  have hpb : traj M w (rbFirst M w (i + 1)) = rbCol M w (i + 1) := pos_rbFirst (i + 1)
  have hltc : rbCol M w i < rbCol M w (i + 1) := Walk.lt_recSeq_succ hns
  have hposA : posAt M w (rbLast M w i) = some (rbCol M w i) := by rw [posAt_traj hT haE, hpa]
  have hposB : posAt M w (rbFirst M w (i + 1)) = some (rbCol M w (i + 1)) := by
    rw [posAt_traj hT hbE, hpb]
  have hrange : ∀ t, rbLast M w i ≤ t → t ≤ rbFirst M w (i + 1) →
      rbCol M w i ≤ traj M w t ∧ traj M w t ≤ rbCol M w (i + 1) := by
    intro t h1 h2
    refine ⟨?_, Walk.le_recSeq_of_le_recFirst hwalk (Nat.zero_le _) (le_refl _)
      (Nat.zero_le _) h2⟩
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h, hpa]
    · exact le_of_lt (Walk.recSeq_lt_of_recLast_lt hwalk (Nat.zero_le _) (le_refl _) hns h
        (by omega))
  obtain ⟨p, hp⟩ := exists_crossOK M w hab hposA hposB
    (fun t h1 h2 => ⟨traj M w t, posAt_traj hT (by omega), by
      rw [min_eq_left (le_of_lt hltc), max_eq_right (le_of_lt hltc)]
      exact hrange t h1 h2⟩)
    (fun t h1 h2 hcon => by
      rw [posAt_traj hT (by omega)] at hcon
      have hvis : t ∈ Walk.visitSet (traj M w) 0 (endT M w) (rbCol M w (i + 1)) :=
        ⟨Nat.zero_le _, by omega, by simpa using hcon⟩
      have h2' : rbFirst M w (i + 1) ≤ t := Walk.firstV_le hvis
      omega)
    (prog_visitsLe hT hwidth hK hi)
  rw [min_eq_left (le_of_lt hltc), max_eq_right (le_of_lt hltc)] at hp
  exact ⟨p, hp⟩

/-! ## The final piece -/

/-- **The final piece of the record-breaker decomposition -- from the last visit
to the last record-breaking column to the halting of the run -- is a halting
piece of the chain.**  It runs to the right or to the left of that column; in
the second case its window is bounded on the left by any column `x` to the right
of which the run stays. -/
theorem exists_haltOK_final (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w K)
    (hK : 2 ≤ K) {x : ℕ} (hx : x ≤ rbCol M w (rbN M w))
    (hlow : ∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w → x ≤ traj M w t) :
    (∃ p : PieceParam A Q, HaltOK M w (K - 1) (rbLast M w (rbN M w))
        (rbCol M w (rbN M w)) w.length p) ∨
      (∃ p : PieceParam A Q, HaltOK M w (K - 1) (rbLast M w (rbN M w))
        x (rbCol M w (rbN M w)) p) := by
  classical
  have hT1 : 1 ≤ T := one_le_of_halt hT
  have hTe : endT M w = T - 1 := endT_eq M w hT
  have hwalk := isWalk_trajE M w hT
  have haE : rbLast M w (rbN M w) ≤ endT M w := rbLast_le_endT (rbN M w)
  have hpa : traj M w (rbLast M w (rbN M w)) = rbCol M w (rbN M w) := pos_rbLast (rbN M w)
  have hposA : posAt M w (rbLast M w (rbN M w)) = some (rbCol M w (rbN M w)) := by
    rw [posAt_traj hT haE, hpa]
  have hcw : rbCol M w (rbN M w) ≤ w.length := posAt_le_length M w hposA
  have hhalt : cfgAt M w (endT M w + 1) = some Cfg.halt := by
    rw [hTe, show T - 1 + 1 = T from by omega]; exact hT
  have hvis : ∀ t, rbLast M w (rbN M w) < t → t ≤ endT M w →
      traj M w t ≠ rbCol M w (rbN M w) := by
    intro t h1 h2 h3
    have h5 : t ≤ Walk.lastV (traj M w) 0 (endT M w) (rbCol M w (rbN M w)) :=
      Walk.le_lastV ⟨Nat.zero_le _, h2, h3⟩
    rw [← rbLast_eq_lastV] at h5
    omega
  have hkw := finalProg_visitsLe hT hwidth hK
  have hside : (∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w →
        rbCol M w (rbN M w) ≤ traj M w t) ∨
      (∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w →
        traj M w t ≤ rbCol M w (rbN M w)) := by
    rcases eq_or_lt_of_le haE with heq | hlt
    · left
      intro t h1 h2
      have ht : t = rbLast M w (rbN M w) := by omega
      rw [ht, hpa]
    · rcases Nat.lt_or_ge (rbCol M w (rbN M w)) (traj M w (rbLast M w (rbN M w) + 1)) with
        hgt | hle
      · left
        intro t h1 h2
        rcases eq_or_lt_of_le h1 with h | h
        · rw [← h, hpa]
        · by_contra hcon
          push_neg at hcon
          obtain ⟨τ, hτ1, hτ2, hτ3⟩ := Walk.exists_eq_between hwalk
            (show rbLast M w (rbN M w) + 1 ≤ t from by omega) h2
            (Or.inr ⟨le_of_lt hcon, le_of_lt hgt⟩)
          exact hvis τ (by omega) (by omega) hτ3
      · have hne := hvis (rbLast M w (rbN M w) + 1) (by omega) (by omega)
        have hlt' : traj M w (rbLast M w (rbN M w) + 1) < rbCol M w (rbN M w) := by omega
        right
        intro t h1 h2
        rcases eq_or_lt_of_le h1 with h | h
        · rw [← h, hpa]
        · by_contra hcon
          push_neg at hcon
          obtain ⟨τ, hτ1, hτ2, hτ3⟩ := Walk.exists_eq_between hwalk
            (show rbLast M w (rbN M w) + 1 ≤ t from by omega) h2
            (Or.inl ⟨le_of_lt hlt', le_of_lt hcon⟩)
          exact hvis τ (by omega) (by omega) hτ3
  rcases hside with hside | hside
  · exact Or.inl (exists_haltOK_right M w haE hposA
      (fun t h1 h2 => ⟨traj M w t, posAt_traj hT h2, hside t h1 h2⟩) hhalt hkw)
  · exact Or.inr (exists_haltOK_left M w haE hx hcw hposA
      (fun t h1 h2 => ⟨traj M w t, posAt_traj hT h2, hlow t h1 h2, hside t h1 h2⟩) hhalt hkw)

end Chk

end TwoWay

end Lax916827Proofs.Transducers
