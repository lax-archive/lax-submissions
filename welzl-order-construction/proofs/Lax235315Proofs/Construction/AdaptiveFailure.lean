import Lax235315Proofs.Construction.KeyFailureBounds
import Mathlib.Tactic

set_option maxHeartbeats 500000

/-!
An adaptive finite-tape union bound. At each round the next choice is fresh
and uniform over the same finite alphabet, while the bad set may depend on
the entire state reached so far. A stopped process is represented by an
absorbing state with no bad choices.
-/

namespace Lax235315Proofs.Construction.AdaptiveFailure
open Classical

/-- A tape is a function assigning one fresh choice to every round. -/
abbrev Tape (β : Type) (r : ℕ) := Fin r → β

/-- Tapes whose first bad choice occurs at some step; after the first failure
the unused suffix is arbitrary. -/
noncomputable def failingTapes {α β : Type} [Fintype β] [DecidableEq β]
    (advance : α → β → α) (bad : α → β → Prop) :
    (r : ℕ) → α → Finset (Tape β r)
  | 0, _ => ∅
  | r + 1, state => by
      classical
      exact (Finset.univ : Finset β).biUnion fun choice =>
        (if bad state choice then (Finset.univ : Finset (Tape β r))
         else failingTapes advance bad r (advance state choice)).image
          (Fin.cases choice)

/-- The first-failure decomposition counts disjoint branches by their first
choice. -/
theorem card_failingTapes_succ {α β : Type} [Fintype β] [DecidableEq β]
    (advance : α → β → α) (bad : α → β → Prop)
    (r : ℕ) (state : α) :
    (failingTapes advance bad (r + 1) state).card =
      ∑ choice : β,
        if bad state choice then Fintype.card (Tape β r)
        else (failingTapes advance bad r (advance state choice)).card := by
  classical
  simp only [failingTapes]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro choice hchoice
    have hinj : Function.Injective (Fin.cases choice : Tape β r → Tape β (r + 1)) := by
      intro x y h
      funext i
      exact congrFun h i.succ
    by_cases hbad : bad state choice
    · simp [hbad, Finset.card_image_of_injective, hinj]
    · simp [hbad, Finset.card_image_of_injective, hinj]
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro tape ht hu
    rcases Finset.mem_image.mp ht with ⟨tail₁, -, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨tail₂, -, hpair⟩
    have hfirst : b = c := by
      have h' := congrFun hpair.symm 0
      simpa using h'
    exact hne hfirst

/-- The total number of tapes is the expected alphabet-size power. -/
theorem card_tape (β : Type) [Fintype β] (r : ℕ) :
    Fintype.card (Tape β r) = Fintype.card β ^ r := by
  simp [Tape]

/-- If every state has at most an ε fraction of bad next choices, then
among all length-r tapes at most an r ε fraction encounter a bad choice.
The state after each choice is unrestricted, so the estimate applies to
adaptive histories and does not assume independent bad events. -/
theorem failingTapes_fraction_le {α β : Type} [Fintype β] [DecidableEq β]
    (advance : α → β → α) (bad : α → β → Prop)
    (ε : ℚ) (hε : 0 ≤ ε)
    (hlocal : ∀ state,
      ((Finset.univ.filter (fun choice : β => bad state choice)).card : ℚ) ≤
        ε * Fintype.card β) :
    ∀ r state,
      ((failingTapes advance bad r state).card : ℚ) ≤
        (r : ℚ) * ε * (Fintype.card β : ℚ) ^ r := by
  classical
  intro r
  induction r with
  | zero =>
      intro state
      simp [failingTapes]
  | succ r ih =>
      intro state
      rw [card_failingTapes_succ]
      simp only [Nat.cast_sum, Nat.cast_ite]
      rw [card_tape]
      simp only [Nat.cast_pow]
      let m : ℚ := Fintype.card β
      let tailBound : ℚ := (r : ℚ) * ε * m ^ r
      have htail : ∀ choice : β,
          ((failingTapes advance bad r (advance state choice)).card : ℚ) ≤
            tailBound := by
        intro choice
        simpa [tailBound, m] using ih (advance state choice)
      have hpoint : ∀ choice : β,
          (if bad state choice then m ^ r
           else (failingTapes advance bad r (advance state choice)).card) ≤
            tailBound + (if bad state choice then m ^ r else 0) := by
        intro choice
        by_cases hbad : bad state choice
        · simp [hbad]
          positivity
        · simp [hbad, htail choice]
      have hsum := Finset.sum_le_sum (s := Finset.univ)
        (fun choice _ => hpoint choice)
      have hbadCount :
          ((Finset.univ.filter (fun choice : β => bad state choice)).card : ℚ) ≤
            ε * m := by
        simpa [m] using hlocal state
      have hbadSum :
          (∑ choice : β, if bad state choice then m ^ r else 0) ≤
            ε * m * m ^ r := by
        calc
          (∑ choice : β, if bad state choice then m ^ r else 0) =
              ((Finset.univ.filter (fun choice : β => bad state choice)).card : ℚ)
                * m ^ r := by
                  simp [Finset.sum_ite, Finset.sum_const]
          _ ≤ (ε * m) * m ^ r :=
            mul_le_mul_of_nonneg_right hbadCount (by positivity)
      calc
        (∑ choice : β,
            if bad state choice then m ^ r
            else (failingTapes advance bad r (advance state choice)).card) ≤
            ∑ choice : β, (tailBound +
              (if bad state choice then m ^ r else 0)) := hsum
        _ = (Fintype.card β : ℚ) * tailBound +
              ∑ choice : β, if bad state choice then m ^ r else 0 := by
            simp [Finset.sum_add_distrib, m, tailBound]
        _ ≤ (Fintype.card β : ℚ) * tailBound + ε * m * m ^ r :=
            add_le_add_right hbadSum ((Fintype.card β : ℚ) * tailBound)
        _ = ((r + 1 : ℕ) : ℚ) * ε * (Fintype.card β : ℚ) ^ (r + 1) := by
            simp only [tailBound, m, Nat.cast_add, Nat.cast_one, pow_succ]
            ring

end Lax235315Proofs.Construction.AdaptiveFailure
