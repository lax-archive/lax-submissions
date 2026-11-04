import Lax185574Proofs.IP.Ramsey
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
Order types of tuples in a grid.

The positions `0, …, N·g - 1` are arranged in `N` columns of height `g`:
`pos s d` is the `d`-th position of column `s`, and positions are ordered
first by column and then by height. If two tuples have their entries in
the same columns, and inside each column the heights are ordered alike,
the tuples have the same order type. The lemma `otp_append_cols` is the
case of a tuple `r` followed by three entries, with the entries of `r` at
heights depending only on their column.
-/

namespace Lax185574Proofs.IP

open Lax185574Proofs.Lib.TupleRamsey

/-- The position of height `d` in column `s`. -/
def pos {N g : ℕ} (s : Fin N) (d : Fin g) : Fin (N * g) := finProdFinEquiv (s, d)

theorem pos_lt_pos {N g : ℕ} (s s' : Fin N) (d d' : Fin g) :
    pos s d < pos s' d' ↔ s < s' ∨ (s = s' ∧ d < d') := by
  show d.val + g * s.val < d'.val + g * s'.val ↔ _
  have hd := d.isLt
  have hd' := d'.isLt
  rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]
  constructor
  · intro h
    rcases lt_trichotomy s.val s'.val with h1 | h1 | h1
    · exact Or.inl h1
    · right; refine ⟨h1, ?_⟩; rw [h1] at h; omega
    · exfalso
      have : g * (s'.val + 1) ≤ g * s.val := Nat.mul_le_mul_left g h1
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
  · rintro (h1 | ⟨h1, h2⟩)
    · have : g * (s.val + 1) ≤ g * s'.val := Nat.mul_le_mul_left g h1
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · rw [h1]; omega

theorem pos_injective {N g : ℕ} {s s' : Fin N} {d d' : Fin g} (h : pos s d = pos s' d') :
    s = s' ∧ d = d' := by
  have := finProdFinEquiv.injective h
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- Tuples with the same order on every pair of entries have the same order
type. -/
theorem otp_eq_of_lt_iff {ℓ L : ℕ} {τ τ' : Fin ℓ → Fin L}
    (h : ∀ a b, τ a < τ b ↔ τ' a < τ' b) : otp τ = otp τ' := by
  funext q
  unfold otp
  rcases lt_trichotomy (τ q.1) (τ q.2) with h1 | h1 | h1
  · rw [compare_lt_iff_lt.mpr h1, compare_lt_iff_lt.mpr ((h _ _).mp h1)]
  · have h2 : ¬ τ' q.1 < τ' q.2 := fun h' => by
      have := (h _ _).mpr h'; rw [h1] at this; exact lt_irrefl _ this
    have h3 : ¬ τ' q.2 < τ' q.1 := fun h' => by
      have := (h _ _).mpr h'; rw [h1] at this; exact lt_irrefl _ this
    have : τ' q.1 = τ' q.2 := le_antisymm (not_lt.mp h3) (not_lt.mp h2)
    rw [compare_eq_iff_eq.mpr h1, compare_eq_iff_eq.mpr this]
  · rw [compare_gt_iff_gt.mpr h1, compare_gt_iff_gt.mpr ((h _ _).mp h1)]

/-- Tuples in the same columns, with heights ordered alike in each column,
have the same order type. -/
theorem otp_eq_of_cols {ℓ N g : ℕ} (S : Fin ℓ → Fin N) (E E' : Fin ℓ → Fin g)
    (h : ∀ a b, S a = S b → (E a < E b ↔ E' a < E' b)) :
    otp (fun a => pos (S a) (E a)) = otp (fun a => pos (S a) (E' a)) := by
  apply otp_eq_of_lt_iff
  intro a b
  simp only [pos_lt_pos]
  by_cases hab : S a = S b
  · simp only [hab, lt_irrefl, false_or, true_and]
    exact h a b hab
  · simp [hab]

/-- The case of a tuple `r` followed by three entries. -/
theorem otp_append_cols {m N g : ℕ} (rc : Fin m → Fin N) (D D' : Fin N → Fin g)
    (cx cy cz : Fin N) (dx dy dz dx' dy' dz' : Fin g)
    (hrx : ∀ s, rc s = cx → (D (rc s) < dx ↔ D' (rc s) < dx') ∧ (dx < D (rc s) ↔ dx' < D' (rc s)))
    (hry : ∀ s, rc s = cy → (D (rc s) < dy ↔ D' (rc s) < dy') ∧ (dy < D (rc s) ↔ dy' < D' (rc s)))
    (hrz : ∀ s, rc s = cz → (D (rc s) < dz ↔ D' (rc s) < dz') ∧ (dz < D (rc s) ↔ dz' < D' (rc s)))
    (hxy : cx = cy → (dx < dy ↔ dx' < dy') ∧ (dy < dx ↔ dy' < dx'))
    (hxz : cx = cz → (dx < dz ↔ dx' < dz') ∧ (dz < dx ↔ dz' < dx'))
    (hyz : cy = cz → (dy < dz ↔ dy' < dz') ∧ (dz < dy ↔ dz' < dy')) :
    otp (Fin.append (fun s => pos (rc s) (D (rc s))) ![pos cx dx, pos cy dy, pos cz dz]) =
      otp (Fin.append (fun s => pos (rc s) (D' (rc s))) ![pos cx dx', pos cy dy', pos cz dz']) := by
  let S : Fin (m + 3) → Fin N := Fin.append rc ![cx, cy, cz]
  let E : Fin (m + 3) → Fin g := Fin.append (D ∘ rc) ![dx, dy, dz]
  let E' : Fin (m + 3) → Fin g := Fin.append (D' ∘ rc) ![dx', dy', dz']
  have e1 : Fin.append (fun s => pos (rc s) (D (rc s))) ![pos cx dx, pos cy dy, pos cz dz] =
      fun a => pos (S a) (E a) := by
    funext a
    refine Fin.addCases (fun s => ?_) (fun u => ?_) a
    · simp [S, E, Fin.append_left]
    · simp only [S, E, Fin.append_right]
      fin_cases u <;> rfl
  have e2 : Fin.append (fun s => pos (rc s) (D' (rc s))) ![pos cx dx', pos cy dy', pos cz dz'] =
      fun a => pos (S a) (E' a) := by
    funext a
    refine Fin.addCases (fun s => ?_) (fun u => ?_) a
    · simp [S, E', Fin.append_left]
    · simp only [S, E', Fin.append_right]
      fin_cases u <;> rfl
  rw [e1, e2]
  apply otp_eq_of_cols
  intro a b hab
  induction a using Fin.addCases with
  | left s =>
    induction b using Fin.addCases with
    | left t =>
      simp only [S, E, E', Fin.append_left, Function.comp_apply] at hab ⊢
      rw [hab]; simp
    | right v =>
      simp only [S, E, E', Fin.append_left, Fin.append_right, Function.comp_apply] at hab ⊢
      fin_cases v
      · exact (hrx s hab).1
      · exact (hry s hab).1
      · exact (hrz s hab).1
  | right u =>
    induction b using Fin.addCases with
    | left t =>
      simp only [S, E, E', Fin.append_left, Fin.append_right, Function.comp_apply] at hab ⊢
      fin_cases u
      · exact (hrx t hab.symm).2
      · exact (hry t hab.symm).2
      · exact (hrz t hab.symm).2
    | right v =>
      simp only [S, E, E', Fin.append_right] at hab ⊢
      fin_cases u <;> fin_cases v
      · simp
      · exact (hxy hab).1
      · exact (hxz hab).1
      · exact (hxy hab.symm).2
      · simp
      · exact (hyz hab).1
      · exact (hxz hab.symm).2
      · exact (hyz hab.symm).2
      · simp

end Lax185574Proofs.IP
