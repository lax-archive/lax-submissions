import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Positivity

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-! A finite family of distinct sets contains a long separating staircase.
The exponential bound is deliberately coarse. -/

namespace Lax185574Proofs.Lib.BipartiteStaircase

universe u
variable {R : Type u} [DecidableEq R]

theorem split_family (F : Finset (Finset R)) (n : ℕ) (hn : 0 < n)
    (hF : 2 * n ≤ F.card) :
    ∃ (b : R) (a : Finset R) (T : Finset (Finset R)) (t : Bool),
      a ∈ F ∧ T ⊆ F ∧ n ≤ T.card ∧
      (b ∈ a ↔ t = false) ∧ ∀ x ∈ T, (b ∈ x ↔ t = true) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < F.card by omega)
  have hdiff : ∃ b, ¬ (b ∈ x ↔ b ∈ y) := by
    by_contra! h
    exact hxy (Finset.ext h)
  obtain ⟨b, hb⟩ := hdiff
  have hp : ∃ x ∈ F, b ∈ x := by
    by_cases hbx : b ∈ x
    · exact ⟨x, hx, hbx⟩
    · exact ⟨y, hy, by tauto⟩
  have hn' : ∃ x ∈ F, b ∉ x := by
    by_cases hbx : b ∈ x
    · exact ⟨y, hy, by tauto⟩
    · exact ⟨x, hx, hbx⟩
  have hsum := Finset.card_filter_add_card_filter_not (s := F) (p := fun x => b ∈ x)
  by_cases hbig : n ≤ (F.filter fun x => b ∈ x).card
  · obtain ⟨a, ha, hba⟩ := hn'
    refine ⟨b, a, F.filter (fun x => b ∈ x), true, ha,
      Finset.filter_subset _ _, hbig, by simp [hba], ?_⟩
    intro z hz
    simp [(Finset.mem_filter.mp hz).2]
  · obtain ⟨a, ha, hba⟩ := hp
    refine ⟨b, a, F.filter (fun x => b ∉ x), false, ha,
      Finset.filter_subset _ _, by omega, by simp [hba], ?_⟩
    intro z hz
    simp [(Finset.mem_filter.mp hz).2]

structure Staircase (F : Finset (Finset R)) (m : ℕ) where
  row : Fin m → Finset R
  column : Fin m → R
  bit : Fin m → Bool
  lastRow : Finset R
  row_mem : ∀ i, row i ∈ F
  last_mem : lastRow ∈ F
  diagonal : ∀ i, column i ∈ row i ↔ bit i = false
  lower : ∀ i j, i < j → (column i ∈ row j ↔ bit i = true)
  last : ∀ i, column i ∈ lastRow ↔ bit i = true

theorem exists_staircase (m : ℕ) (F : Finset (Finset R)) (hF : 2 ^ m ≤ F.card) :
    Nonempty (Staircase F m) := by
  classical
  induction m generalizing F with
  | zero =>
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < F.card by simpa using hF)
    exact ⟨⟨Fin.elim0, Fin.elim0, Fin.elim0, z, (fun i => i.elim0), hz,
      (fun i => i.elim0), (fun i => i.elim0), (fun i => i.elim0)⟩⟩
  | succ m ih =>
    obtain ⟨b, a, T, t, ha, hT, hcard, hdiag, hbit⟩ :=
      split_family F (2 ^ m) (by positivity) (by simpa [pow_succ, Nat.mul_comm] using hF)
    obtain ⟨s⟩ := ih T hcard
    refine ⟨⟨Fin.cons a s.row, Fin.cons b s.column, Fin.cons t s.bit,
      s.lastRow, ?_, hT s.last_mem, ?_, ?_, ?_⟩⟩
    · intro i
      refine Fin.cases ha (fun j => hT (s.row_mem j)) i
    · intro i
      refine Fin.cases hdiag (fun j => s.diagonal j) i
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro j
        refine Fin.cases (fun h => (lt_irrefl _ h).elim) (fun j' _ => ?_) j
        exact hbit _ (s.row_mem j')
      · intro j
        refine Fin.cases (fun h => (Fin.not_lt_zero _ h).elim) (fun j' h => ?_) j
        exact s.lower i' j' (Fin.succ_lt_succ_iff.mp h)
    · intro i
      refine Fin.cases (hbit _ s.last_mem) (fun j => s.last j) i

omit [DecidableEq R] in
theorem Staircase.row_injective {F : Finset (Finset R)} {m : ℕ} (s : Staircase F m) :
    Function.Injective s.row := by
  have hlt (i j : Fin m) (hij : i < j) : s.row i ≠ s.row j := by
    intro h
    have hd := s.diagonal i
    have hl := s.lower i j hij
    rw [h] at hd
    cases s.bit i <;> simp_all
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hlt i j hij h
  · exact hlt j i hji h.symm

omit [DecidableEq R] in
theorem Staircase.column_injective {F : Finset (Finset R)} {m : ℕ} (s : Staircase F m) :
    Function.Injective s.column := by
  have hlt (i j : Fin m) (hij : i < j) : s.column i ≠ s.column j := by
    intro h
    have hi := s.lower i j hij
    have hiz := s.last i
    have hj := s.diagonal j
    have hjz := s.last j
    rw [h] at hi hiz
    cases s.bit i <;> cases s.bit j <;> simp_all
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hlt i j hij h
  · exact hlt j i hji h.symm

end Lax185574Proofs.Lib.BipartiteStaircase
