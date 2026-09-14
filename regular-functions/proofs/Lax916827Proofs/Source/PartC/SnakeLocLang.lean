/-
**Local conditions are regular.**

Two elementary families of regular languages, used by the checking automaton of
the book's first stage in the proof of the snake lemma
(`RequestProject/PartC/SnakeStage1.lean`).

* `SnakeLoc.PairsOK`: every pair of consecutive letters of the string -- and, at
  the two ends, the pair formed by the first (last) letter and the absent letter
  beyond the end -- satisfies a fixed condition.  A condition on the letter at a
  position together with the letter before it *or* the letter after it is of
  this shape.
* `SnakeLoc.MidOK`: in a doubly marked string, every letter strictly between the
  two marks satisfies a fixed condition.

Both are recognised by a `foldl` over a finite state space, hence regular
(`RegAut.isRegular_foldl`).
-/
import Lax916827Proofs.Source.PartC.MarkStr
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace SnakeLoc

open MarkStr

variable {Γ : Type}

/-! ## Conditions on pairs of consecutive letters -/

/-- The letter preceding the position `i` of `u`. -/
def prevAt (u : List Γ) (i : ℕ) : Option Γ := if i = 0 then none else u[i - 1]?

@[simp] lemma prevAt_zero (u : List Γ) : prevAt u 0 = none := rfl

lemma prevAt_length (u : List Γ) : prevAt u u.length = u.getLast? := by
  rcases u.eq_nil_or_concat with rfl | ⟨v, c, rfl⟩
  · rfl
  · rw [prevAt, if_neg (by simp)]
    exact List.getLast?_eq_getElem?.symm

lemma prevAt_append_one {u : List Γ} {c : Γ} {i : ℕ} (hi : i ≤ u.length) :
    prevAt (u ++ [c]) i = prevAt u i := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rfl
  · rw [prevAt, prevAt, if_neg (by omega), if_neg (by omega),
      List.getElem?_append_left (by omega)]

/-- Every pair of consecutive letters of `u` satisfies `good`; the pairs at the
two ends of the string are `(none, u[0])` and `(u[n-1], none)`. -/
def PairsOK (good : Option Γ → Option Γ → Bool) (u : List Γ) : Prop :=
  ∀ i ≤ u.length, good (prevAt u i) u[i]? = true

/-- The state of the automaton recognising `PairsOK`: the previous letter and
the conjunction of the conditions checked so far. -/
private def pstep (good : Option Γ → Option Γ → Bool) :
    Option Γ × Bool → Γ → Option Γ × Bool :=
  fun s c => (some c, s.2 && good s.1 (some c))

private lemma foldl_pstep_fst (good : Option Γ → Option Γ → Bool) (u : List Γ) :
    (u.foldl (pstep good) (none, true)).1 = u.getLast? := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton v c ih => rw [List.foldl_append]; simp [pstep]

private lemma foldl_pstep_snd (good : Option Γ → Option Γ → Bool) (u : List Γ) :
    (u.foldl (pstep good) (none, true)).2 = true ↔
      ∀ i < u.length, good (prevAt u i) u[i]? = true := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton v c ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, pstep, Bool.and_eq_true]
      rw [ih, foldl_pstep_fst good v, ← prevAt_length v]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rw [List.length_append, List.length_singleton] at hi
        rcases Nat.lt_or_ge i v.length with hlt | hge
        · rw [prevAt_append_one (le_of_lt hlt), List.getElem?_append_left hlt]
          exact h1 i hlt
        · have hiv : i = v.length := by omega
          subst hiv
          rw [prevAt_append_one (le_refl _)]
          simpa using h2
      · intro h
        refine ⟨fun i hi => ?_, ?_⟩
        · have := h i (by simp; omega)
          rwa [prevAt_append_one (le_of_lt hi), List.getElem?_append_left hi] at this
        · have := h v.length (by simp)
          rwa [prevAt_append_one (le_refl _), List.getElem?_append_right (le_refl _),
            Nat.sub_self] at this

/-- **A condition on pairs of consecutive letters defines a regular
language.** -/
lemma isRegular_pairsOK [Finite Γ] (good : Option Γ → Option Γ → Bool) :
    Language.IsRegular {u : List Γ | PairsOK good u} := by
  have h := RegAut.isRegular_foldl (Γ := Γ) (pstep good) (none, true)
    {s : Option Γ × Bool | s.2 = true ∧ good s.1 none = true}
  refine RegAut.isRegular_of_eq h (fun u => ?_)
  simp only [Set.mem_setOf_eq, PairsOK]
  constructor
  · intro h
    refine ⟨(foldl_pstep_snd good u).2 (fun i hi => h i (le_of_lt hi)), ?_⟩
    have := h u.length (le_refl _)
    rwa [prevAt_length, List.getElem?_eq_none (le_refl _), ← foldl_pstep_fst good u] at this
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_or_ge i u.length with hlt | hge
    · exact (foldl_pstep_snd good u).1 h1 i hlt
    · have hiu : i = u.length := by omega
      subst hiu
      rw [prevAt_length, List.getElem?_eq_none (le_refl _), foldl_pstep_fst good u] at *
      exact h2

/-! ## Conditions on the letters between the two marks -/

/-- Is one of the letters marked by the first mark? -/
def hasM1 (z : List (Mark2 Γ)) : Bool := z.any (fun c => c.2.1)

/-- Is one of the letters marked by the second mark? -/
def hasM2 (z : List (Mark2 Γ)) : Bool := z.any (fun c => c.2.2)

/-- The state of the automaton recognising `MidOK`: whether each of the two
marks has been seen, and the conjunction of the conditions checked so far. -/
private def mstep (P : Γ → Bool) : Bool × Bool × Bool → Mark2 Γ → Bool × Bool × Bool :=
  fun s c => (s.1 || c.2.1, s.2.1 || c.2.2,
    if s.1 && !s.2.1 && !c.2.1 && !c.2.2 then s.2.2 && P c.1 else s.2.2)

/-- **Every letter strictly between the two marks satisfies `P`.** -/
def MidOK (P : Γ → Bool) : Language (Mark2 Γ) :=
  {z | (z.foldl (mstep P) (false, false, true)).2.2 = true}

lemma hasM1_concat (v : List (Mark2 Γ)) (c : Mark2 Γ) :
    hasM1 (v ++ [c]) = (hasM1 v || c.2.1) := by simp [hasM1]

lemma hasM2_concat (v : List (Mark2 Γ)) (c : Mark2 Γ) :
    hasM2 (v ++ [c]) = (hasM2 v || c.2.2) := by simp [hasM2]

private lemma foldl_mstep_fst (P : Γ → Bool) (z : List (Mark2 Γ)) :
    (z.foldl (mstep P) (false, false, true)).1 = hasM1 z ∧
      (z.foldl (mstep P) (false, false, true)).2.1 = hasM2 z := by
  induction z using List.reverseRecOn with
  | nil => simp [hasM1, hasM2]
  | append_singleton v c ih =>
      rw [List.foldl_append]
      refine ⟨?_, ?_⟩
      · simp [mstep, hasM1_concat, ih.1]
      · simp [mstep, hasM2_concat, ih.2]

private lemma foldl_mstep_snd (P : Γ → Bool) (z : List (Mark2 Γ)) :
    (z.foldl (mstep P) (false, false, true)).2.2 = true ↔
      ∀ i, ∀ h : i < z.length, hasM1 (z.take i) = true → hasM2 (z.take (i + 1)) = false →
        (z[i]'h).2.1 = false → P (z[i]'h).1 = true := by
  induction z using List.reverseRecOn with
  | nil => simp
  | append_singleton v c ih =>
      have hv1 := (foldl_mstep_fst P v).1
      have hv2 := (foldl_mstep_fst P v).2
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, mstep]
      rw [hv1, hv2]
      have htake : ∀ i ≤ v.length, (v ++ [c]).take i = v.take i :=
        fun i hi => List.take_append_of_le_length hi
      have hget : ∀ (i : ℕ) (h : i < v.length), (v ++ [c])[i]'(by simp; omega) = v[i]'h :=
        fun i h => List.getElem_append_left h
      have hlast : ((v ++ [c]).take (v.length + 1)) = v ++ [c] :=
        List.take_of_length_le (by simp)
      have hsplit : (∀ i, ∀ h : i < (v ++ [c]).length,
            hasM1 ((v ++ [c]).take i) = true → hasM2 ((v ++ [c]).take (i + 1)) = false →
              ((v ++ [c])[i]'h).2.1 = false → P ((v ++ [c])[i]'h).1 = true)
          ↔ ((∀ i, ∀ h : i < v.length, hasM1 (v.take i) = true →
                hasM2 (v.take (i + 1)) = false → (v[i]'h).2.1 = false → P (v[i]'h).1 = true)
              ∧ (hasM1 v = true → hasM2 (v ++ [c]) = false → c.2.1 = false → P c.1 = true)) := by
        constructor
        · intro h
          refine ⟨fun i hi => ?_, ?_⟩
          · have := h i (by simp; omega)
            rw [htake i (le_of_lt hi), htake (i + 1) (by omega), hget i hi] at this
            exact this
          · have := h v.length (by simp)
            rw [htake v.length (le_refl _), List.take_length, hlast] at this
            simpa using this
        · rintro ⟨h1, h2⟩ i hi
          rcases Nat.lt_or_ge i v.length with hlt | hge
          · rw [htake i (le_of_lt hlt), htake (i + 1) (by omega), hget i hlt]
            exact h1 i hlt
          · have hiv : i = v.length := by simp at hi; omega
            subst hiv
            rw [htake v.length (le_refl _), List.take_length, hlast]
            simpa using h2
      rw [hsplit, ← ih]
      by_cases hc : hasM1 v && !hasM2 v && !c.2.1 && !c.2.2
      · rw [if_pos hc]
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hc
        have hm2 : hasM2 (v ++ [c]) = false := by rw [hasM2_concat, hc2, hc4]; rfl
        rw [Bool.and_eq_true]
        constructor
        · rintro ⟨ha, hb⟩
          exact ⟨ha, fun _ _ _ => hb⟩
        · rintro ⟨ha, hb⟩
          exact ⟨ha, hb hc1 hm2 hc3⟩
      · rw [if_neg hc]
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and_or, Bool.not_eq_false] at hc
        constructor
        · intro ha
          refine ⟨ha, fun h1 h2 h3 => ?_⟩
          rw [hasM2_concat, Bool.or_eq_false_iff] at h2
          rcases hc with (((h | h) | h) | h)
          · exact absurd h1 (by simp [h])
          · exact absurd h2.1 (by simp [h])
          · exact absurd h3 (by simp [h])
          · exact absurd h2.2 (by simp [h])
        · exact fun h => h.1

end SnakeLoc
end Lax916827Proofs.Transducers
