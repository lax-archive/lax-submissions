/-
The state of a flip-flop machine, in terms of the last resetting letter.

In a flip-flop machine (Definition `def:prime-mealy-machines`) every letter either leaves
the state unchanged or resets it to a fixed state.  Hence the state reached after reading a prefix
of the input is the target of the *last* resetting letter of that prefix, and the initial state if
the prefix has no resetting letter.  This is the combinatorial content of the fact that flip-flop
machines are first-order definable, used in Theorem `thm:logic-aperiodic`; the corresponding
formulas are built in `RequestProject/PartC/FOMealy.lean`. -/
import Lax765601Proofs.Source.PartA.MealyBasic
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace Mealy
export Lax765601Proofs.Transducers.Mealy (trans_cons trans_append)

variable {A B Q : Type}

open scoped Classical in
/-- The state to which a letter resets the machine, if it is not the identity. -/
noncomputable def resetTo (M : Mealy A B Q) (a : A) : Option Q :=
  if M.letterTrans a = id then none else some (M.letterTrans a M.init)

lemma letterTrans_of_resetTo_none {M : Mealy A B Q} {a : A} (h : Mealy.resetTo M a = none) (q : Q) :
    M.letterTrans a q = q := by
  by_cases hid : M.letterTrans a = id
  · rw [hid]; rfl
  · rw [resetTo, if_neg hid] at h; exact absurd h (by simp)

lemma letterTrans_of_resetTo_some {M : Mealy A B Q} (hM : M.FlipFlop) {a : A} {q₀ : Q}
    (h : Mealy.resetTo M a = some q₀) (q : Q) : M.letterTrans a q = q₀ := by
  by_cases hid : M.letterTrans a = id
  · rw [resetTo, if_pos hid] at h; exact absurd h (by simp)
  · rw [resetTo, if_neg hid] at h
    obtain ⟨q₁, hq₁⟩ := (hM a).resolve_left hid
    have : q₀ = M.letterTrans a M.init := by simpa using h.symm
    rw [this, hq₁ q, hq₁ M.init]

/-- A string of letters that do not reset the machine does not change the
state. -/
lemma trans_of_all_resetTo_none {M : Mealy A B Q} :
    ∀ (u : List A), (∀ a ∈ u, Mealy.resetTo M a = none) → ∀ q : Q, M.trans u q = q := by
  intro u
  induction u with
  | nil => intro _ q; rfl
  | cons a u ih =>
      intro h q
      rw [trans_cons, letterTrans_of_resetTo_none (h a (by simp)) q]
      exact ih (fun c hc => h c (by simp [hc])) q

/-- The letters of a segment of a string, with their positions. -/
lemma exists_pos_of_mem_segment {w : List A} (s t : ℕ) (a : A)
    (ha : a ∈ (w.drop s).take t) : ∃ z, s ≤ z ∧ z < s + t ∧ w[z]? = some a := by
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
  have hlen := List.length_take (l := w.drop s) (i := t)
  have hlt : i < t := by omega
  have hi' : s + i < w.length := by
    have h1 : i < (w.drop s).length := by omega
    rw [List.length_drop] at h1
    omega
  refine ⟨s + i, by omega, by omega, ?_⟩
  rw [List.getElem?_eq_getElem hi']
  congr 1
  rw [← hia]
  simp [List.getElem_take, List.getElem_drop]

/-- If the last resetting letter of the prefix of length `p` is at the position
`j`, then the state after that prefix is its target. -/
lemma trans_take_of_last_reset {M : Mealy A B Q} (hM : M.FlipFlop) {w : List A} {p j : ℕ}
    {a : A} {q₀ : Q} (hj : j < p) (hwj : w[j]? = some a) (hreset : Mealy.resetTo M a = some q₀)
    (hlast : ∀ z a', j < z → z < p → w[z]? = some a' → Mealy.resetTo M a' = none) :
    M.trans (w.take p) M.init = q₀ := by
  have hjw : j < w.length := by
    rcases List.getElem?_eq_some_iff.mp hwj with ⟨h, -⟩
    exact h
  have hsplit : w.take p = w.take (j + 1) ++ (w.drop (j + 1)).take (p - (j + 1)) := by
    rw [← List.take_add]
    congr 1
    omega
  have hwa : w[j] = a := by
    rcases List.getElem?_eq_some_iff.mp hwj with ⟨h', h⟩
    exact h
  have hstep : M.trans (w.take (j + 1)) M.init = q₀ := by
    have htake : w.take (j + 1) = w.take j ++ [a] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjw, hwa]
      rfl
    rw [htake, trans_append, trans_cons, letterTrans_of_resetTo_some hM hreset]
    rfl
  rw [hsplit, trans_append, hstep]
  refine trans_of_all_resetTo_none _ ?_ q₀
  intro c hc
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_pos_of_mem_segment (w := w) (j + 1) (p - (j + 1)) c hc
  exact hlast z c (by omega) (by omega) hz3

/-- If no letter of the prefix of length `p` resets the machine, the state after
that prefix is the initial state. -/
lemma trans_take_of_no_reset {M : Mealy A B Q} {w : List A} {p : ℕ}
    (hnone : ∀ z a', z < p → w[z]? = some a' → Mealy.resetTo M a' = none) :
    M.trans (w.take p) M.init = M.init := by
  refine trans_of_all_resetTo_none _ ?_ M.init
  intro c hc
  obtain ⟨z, -, hz2, hz3⟩ := exists_pos_of_mem_segment (w := w) 0 p c (by simpa using hc)
  exact hnone z c (by omega) hz3

/-- The last position below a bound at which a property holds. -/
lemma exists_last_lt (P : ℕ → Prop) (p : ℕ) (h : ∃ j, j < p ∧ P j) :
    ∃ j₀, j₀ < p ∧ P j₀ ∧ ∀ z, j₀ < z → z < p → ¬ P z := by
  classical
  induction p with
  | zero => obtain ⟨j, hj, -⟩ := h; omega
  | succ p ih =>
      by_cases hp : P p
      · exact ⟨p, by omega, hp, fun z hz1 hz2 => by omega⟩
      · obtain ⟨j, hj, hPj⟩ := h
        have hjp : j < p := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
          · exact h'
          · exact absurd hPj hp
        obtain ⟨j₀, h1, h2, h3⟩ := ih ⟨j, hjp, hPj⟩
        refine ⟨j₀, by omega, h2, fun z hz1 hz2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hz2 with h' | rfl
        · exact h3 z hz1 h'
        · exact hp

/-- The state of a flip-flop machine after reading a prefix of the input: it is
the target of the last resetting letter of the prefix, and the initial state if
there is none. -/
theorem trans_take_eq_iff {M : Mealy A B Q} (hM : M.FlipFlop) (w : List A) (p : ℕ) (q : Q) :
    M.trans (w.take p) M.init = q ↔
      ((∃ j < p, ∃ a, w[j]? = some a ∧ Mealy.resetTo M a = some q ∧
          ∀ z a', j < z → z < p → w[z]? = some a' → Mealy.resetTo M a' = none)
        ∨ (q = M.init ∧ ∀ z a', z < p → w[z]? = some a' → Mealy.resetTo M a' = none)) := by
  classical
  constructor
  · intro htr
    by_cases hres : ∃ j < p, ∃ a, w[j]? = some a ∧ (Mealy.resetTo M a).isSome
    · -- there is a resetting letter before `p`; take the last one
      obtain ⟨j₀, hj₀p, ⟨a₀, hwj₀, hsome₀⟩, hmax⟩ :=
        exists_last_lt (fun j => ∃ a, w[j]? = some a ∧ (Mealy.resetTo M a).isSome) p
          (by obtain ⟨j, hjp, hj⟩ := hres; exact ⟨j, hjp, hj⟩)
      obtain ⟨q₀, hq₀⟩ := Option.isSome_iff_exists.mp hsome₀
      have hlast : ∀ z a', j₀ < z → z < p → w[z]? = some a' → Mealy.resetTo M a' = none := by
        intro z a' hz1 hz2 hz3
        have hnot := hmax z hz1 hz2
        cases hr : Mealy.resetTo M a' with
        | none => rfl
        | some q' => exact absurd ⟨a', hz3, by rw [hr]; rfl⟩ hnot
      have hst := trans_take_of_last_reset hM hj₀p hwj₀ hq₀ hlast
      rw [htr] at hst
      exact Or.inl ⟨j₀, hj₀p, a₀, hwj₀, by rw [hq₀, hst], hlast⟩
    · push_neg at hres
      have hnone : ∀ z a', z < p → w[z]? = some a' → Mealy.resetTo M a' = none := by
        intro z a' hz hwz
        have := hres z hz a' hwz
        cases hr : Mealy.resetTo M a' with
        | none => rfl
        | some q' =>
            rw [hr] at this
            exact absurd (by simp : (some q').isSome = true) this
      refine Or.inr ⟨?_, hnone⟩
      rw [trans_take_of_no_reset hnone] at htr
      exact htr.symm
  · rintro (⟨j, hj, a, hwj, hreset, hlast⟩ | ⟨rfl, hnone⟩)
    · exact trans_take_of_last_reset hM hj hwj hreset hlast
    · exact trans_take_of_no_reset hnone

end Mealy
end Lax314295Proofs.Transducers
