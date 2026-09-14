/- Auxiliary lemmas for the composition of two two-way transducers (Theorem
`thm:composition-of-two-way-transducers` of *Transducers*, M. Bojańczyk).

This file collects the bookkeeping that the construction of `TwoWayComp.lean`
needs: the output word produced by a transition, the splitting of the output of
a stretch of the run, and the letters read off the annotation.
-/
import Lax916827Proofs.Source.PartC.TwoWayAnnotBim
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q S : Type}

/-- The output produced by a transition. -/
def outWord {B Q : Type} : List B ⊕ (Q × List B × Bool) → List B
  | Sum.inl o => o
  | Sum.inr (_, o, _) => o

/-! ### Generic list lemmas -/

lemma take_getLast?' {α : Type} (l : List α) {i : ℕ} (hi : i ≤ l.length) :
    (l.take i).getLast? = if i = 0 then none else l[i - 1]? := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [List.take_zero, if_pos rfl]
    rfl
  · rw [List.getLast?_eq_getElem?, List.length_take, min_eq_left hi, List.getElem?_take,
      if_pos (by omega), if_neg (by omega)]

/-- A list of length `m + 1` whose last letter is `b` has `[b]` as its final
segment starting at `m`. -/
lemma drop_eq_singleton_last {α : Type} {O : List α} {m : ℕ} {b : α} (hlen : O.length = m + 1)
    (hlast : O.getLast? = some b) : O.drop m = [b] := by
  have hm : m < O.length := by omega
  rw [List.drop_eq_getElem_cons hm, List.drop_eq_nil_of_le (by omega)]
  congr 1
  rw [List.getLast?_eq_getElem?, hlen] at hlast
  simp only [Nat.add_sub_cancel] at hlast
  rw [List.getElem?_eq_getElem hm] at hlast
  exact Option.some_injective _ hlast

lemma take_dropLast {α : Type} (O : List α) {j : ℕ} (hj : j ≤ O.length) :
    (O.take j).dropLast = O.take (j - 1) := by
  rw [List.dropLast_eq_take, List.length_take, min_eq_left hj, List.take_take]
  congr 1
  omega

lemma dropLast_eq_take_of_length {α : Type} {O : List α} {m : ℕ} (hlen : O.length = m + 1) :
    O.dropLast = O.take m := by
  rw [List.dropLast_eq_take, hlen]
  simp

/-! ### The output of a transition and of a stretch of the run -/

lemma stepCfg_outWord {M : TwoWay A B Q} {u v : List A} {q : Q} {o : List B} {c' : Cfg A Q}
    (h : M.stepCfg (Cfg.conf u q v) = some (o, c')) :
    o = outWord (M.step u.getLast? q v.head?) := by
  rcases hM : M.step u.getLast? q v.head? with o' | ⟨q', o', dir⟩
  · rw [stepCfg_halt_eq M hM] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  · cases dir with
    | true =>
        cases v with
        | nil => rw [stepCfg_right_nil M hM] at h; exact absurd h (by simp)
        | cons a v' =>
            rw [stepCfg_right_cons M hM] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            rfl
    | false =>
        rcases hu : u.getLast? with _ | a
        · rw [stepCfg_left_none M hu hM] at h; exact absurd h (by simp)
        · rw [stepCfg_left_some M hu hM] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          rfl

/-- The configuration reached by a transition that moves the head to the
right. -/
lemma stepCfg_move_right {M : TwoWay A B Q} {u v : List A} {q q' : Q} {oM o : List B}
    {c₁ : Cfg A Q} (hMs : M.step u.getLast? q v.head? = Sum.inr (q', oM, true))
    (hstep : M.stepCfg (Cfg.conf u q v) = some (o, c₁)) :
    ∃ (a : A) (v' : List A), v = a :: v' ∧ c₁ = Cfg.conf (u ++ [a]) q' v' := by
  cases v with
  | nil =>
      rw [stepCfg_right_nil M hMs] at hstep
      exact absurd hstep (by simp)
  | cons a v' =>
      refine ⟨a, v', rfl, ?_⟩
      rw [stepCfg_right_cons M hMs] at hstep
      exact (congrArg Prod.snd (Option.some_injective _ hstep)).symm

/-- The configuration reached by a transition that moves the head to the
left. -/
lemma stepCfg_move_left {M : TwoWay A B Q} {u v : List A} {q q' : Q} {oM o : List B}
    {c₁ : Cfg A Q} (hMs : M.step u.getLast? q v.head? = Sum.inr (q', oM, false))
    (hstep : M.stepCfg (Cfg.conf u q v) = some (o, c₁)) :
    ∃ a : A, u.getLast? = some a ∧ c₁ = Cfg.conf u.dropLast q' (a :: v) := by
  rcases hgl : u.getLast? with _ | a
  · rw [stepCfg_left_none M hgl hMs] at hstep
    exact absurd hstep (by simp)
  · refine ⟨a, rfl, ?_⟩
    rw [stepCfg_left_some M hgl hMs] at hstep
    exact (congrArg Prod.snd (Option.some_injective _ hstep)).symm

variable (M : TwoWay A B Q) (w : List A)

lemma exists_step_of_succ {t : ℕ} {c : Cfg A Q} (hc : cfgAt M w t = some c)
    (hnext : cfgAt M w (t + 1) ≠ none) : ∃ o c', M.stepCfg c = some (o, c') := by
  rw [cfgAt_succ, hc] at hnext
  simp only [Option.bind_some] at hnext
  rcases hs : M.stepCfg c with _ | ⟨o, c'⟩
  · rw [hs] at hnext; simp at hnext
  · exact ⟨o, c', rfl⟩

lemma outRange_succ (a b : ℕ) (hab : a ≤ b) :
    outRange M w a (b + 1) = outRange M w a b ++ outAt M w b := by
  rw [outRange, outRange, show b + 1 - a = (b - a) + 1 from by omega, List.range'_concat]
  simp [show a + (b - a) = b from by omega]

lemma outRange_cons (a b : ℕ) (hab : a < b) :
    outRange M w a b = outAt M w a ++ outRange M w (a + 1) b := by
  rw [outRange, outRange, show b - a = (b - (a + 1)) + 1 from by omega, List.range'_succ]
  simp

@[simp] lemma outRange_self (a : ℕ) : outRange M w a a = [] := by
  simp [outRange]

/-- If the run does not stop at time `s`, the transition taken then produces an
output of the uniform length, ending with the fixed letter. -/
lemma outAt_len_last {s m : ℕ} {b₀ : B} (hne : cfgAt M w (s + 1) ≠ none)
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀) :
    (outAt M w s).length = m + 1 ∧ (outAt M w s).getLast? = some b₀ := by
  rcases hc : cfgAt M w s with _ | cs
  · exact absurd (cfgAt_none_succ M w hc) hne
  · cases cs with
    | halt => exact absurd (cfgAt_halt_succ M w hc) hne
    | conf u q v =>
        obtain ⟨oo, c', hstep⟩ := exists_step_of_succ M w hc hne
        have ho : outAt M w s = oo := outAt_of_step M w hc hstep
        have hoo : oo = outWord (M.step u.getLast? q v.head?) := stepCfg_outWord hstep
        rw [ho, hoo]
        exact ⟨houtlen _ _ _, houtlast _ _ _⟩

/-- The output produced up to a positive time ends with the fixed letter. -/
lemma outRange_getLast? {t m : ℕ} {b₀ : B} (ht : 0 < t) (hne : cfgAt M w t ≠ none)
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀) :
    (outRange M w 0 t).getLast? = some b₀ := by
  obtain ⟨hlen, hlast⟩ := outAt_len_last M w (s := t - 1)
    (by rw [show t - 1 + 1 = t from by omega]; exact hne) houtlen houtlast
  rw [show t = (t - 1) + 1 from by omega, outRange_succ M w 0 (t - 1) (Nat.zero_le _),
    List.getLast?_append_of_ne_nil _ (by intro hnil; rw [hnil] at hlen; simp at hlen)]
  exact hlast

/-- Removing the last letter of the output produced up to a positive time `t`
amounts to removing the last letter of the transition taken at `t - 1`. -/
lemma outRange_dropLast {t m : ℕ} {b₀ : B} (ht : 0 < t) (hne : cfgAt M w t ≠ none)
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀) :
    (outRange M w 0 t).dropLast = outRange M w 0 (t - 1) ++ (outAt M w (t - 1)).take m ∧
      (outAt M w (t - 1)).drop m = [b₀] := by
  obtain ⟨hlen, hlast⟩ := outAt_len_last M w (s := t - 1)
    (by rw [show t - 1 + 1 = t from by omega]; exact hne) houtlen houtlast
  have hne' : outAt M w (t - 1) ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen
  refine ⟨?_, drop_eq_singleton_last hlen hlast⟩
  conv_lhs => rw [show t = (t - 1) + 1 from by omega,
    outRange_succ M w 0 (t - 1) (Nat.zero_le _)]
  rw [List.dropLast_append_of_ne_nil hne', dropLast_eq_take_of_length hlen]

/-! ### The letters read off the annotation -/


lemma annot_getElem?_letter (D : DFA (Marked A Q) S) (w : List A) (i : ℕ) :
    ((annot D w)[i]?).map AnnLet.letter = w[i]? := by
  rcases Nat.lt_or_ge i w.length with h | h
  · rw [annot_getElem D w h, List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem?_eq_none (by rw [annot_length]; omega), List.getElem?_eq_none h]
    rfl

lemma prevLet_annot_letter (D : DFA (Marked A Q) S) (w : List A) (i : ℕ) :
    (prevLet (annot D w) i).map AnnLet.letter = if i = 0 then none else w[i - 1]? := by
  rcases Nat.eq_zero_or_pos i with rfl | h
  · rw [prevLet_zero, if_pos rfl]
    rfl
  · rw [prevLet_pos (by omega), if_neg (by omega), annot_getElem?_letter]

lemma annot_letters_at (D : DFA (Marked A Q) S) {u v w : List A} (huv : u ++ v = w) :
    (prevLet (annot D w) u.length).map AnnLet.letter = u.getLast? ∧
      ((annot D w)[u.length]?).map AnnLet.letter = v.head? := by
  have hu : w.take u.length = u := by rw [← huv]; simp
  have hv : w.drop u.length = v := by rw [← huv]; simp
  have hiw : u.length ≤ w.length := by rw [← huv]; simp
  refine ⟨?_, ?_⟩
  · rw [prevLet_annot_letter]
    conv_rhs => rw [← hu]
    rw [take_getLast?' w hiw]
  · rw [annot_getElem?_letter, ← hv, List.head?_drop]

lemma prevLet_annot_isNone (D : DFA (Marked A Q) S) (w : List A) {i : ℕ} (hi : i ≤ w.length) :
    (prevLet (annot D w) i).isNone = true ↔ i = 0 := by
  constructor
  · intro h
    by_contra hne
    rw [prevLet_pos hne, List.getElem?_eq_getElem
      (show i - 1 < (annot D w).length by rw [annot_length]; omega)] at h
    simp at h
  · rintro rfl
    rfl

end TwoWay

end Lax916827Proofs.Transducers
