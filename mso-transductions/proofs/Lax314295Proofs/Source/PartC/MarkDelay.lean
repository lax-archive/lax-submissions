/-
A "delayed" automaton, used in the proof of Lemma `lem:logic-precomputation` of *Transducers*
(M. Bojańczyk).

Fix an automaton `D` over the doubly marked alphabet `Mark2 A`, and an alphabet
`C` of letters that carry a letter of `A` (`lt`), a state of `D` (`st`) and a
state transformation of `D` (`tr`).  A nonempty string `c₀ … c_{n-1}` over `C`
is accepted by the delayed automaton when

  `tr c_{n-1} (D.step … (st c₀) …) ∈ D.accept`,

where the run in the middle is the run of `D` on the string `lt c₀ … lt c_{n-1}`
with the first and the last position marked (`MarkStr.midMark`).  This cannot be
computed by a plain deterministic automaton reading the string letter by letter,
because whether a position is the last one is only known at the end of the run;
so the automaton keeps the last letter it has read pending, and processes it
only when it reads the next letter (or, at the end of the run, in the acceptance
condition).
-/
import Lax314295Proofs.Source.PartC.MarkBimach
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace MarkDelay

open MarkStr

variable {A C S : Type}

/-! ## Two recursive descriptions of lists -/

/-- The last element of the nonempty list `c :: t`. -/
def lastC (c : C) : List C → C
  | [] => c
  | d :: t => lastC d t

lemma lastC_cons (c d : C) (t : List C) : lastC c (d :: t) = lastC d t := rfl

lemma lastC_eq_getElem (c : C) (t : List C) :
    lastC c t = (c :: t)[t.length]'(by simp) := by
  induction t generalizing c with
  | nil => rfl
  | cons d t ih =>
      rw [lastC_cons, ih d]
      simp

/-- The marking of a list of letters in which the first position carries the
flag `b`, the last position is marked, and no other position is marked. -/
def markFL : List A → Bool → List (Mark2 A)
  | [], _ => []
  | a :: v, b => (a, b, decide (v = [])) :: markFL v false

lemma markGen_cons (g : A → ℕ → C) (a : A) (v : List A) (m : ℕ) :
    markGen g (a :: v) m = g a m :: markGen g v (m + 1) := by
  simp [markGen, List.zipIdx_cons]

lemma markGen_eq_markFL (v : List A) (m n : ℕ) (h : n = m + v.length) :
    markGen (fun a i => (a, decide (i = 0), decide (i + 1 = n))) v m
      = markFL v (decide (m = 0)) := by
  induction v generalizing m with
  | nil => rfl
  | cons a v ih =>
      rw [markGen_cons, markFL, ih (m + 1) (by simp only [List.length_cons] at h; omega)]
      have hb : decide (m + 1 = 0) = false := by simp
      have hl : decide (m + 1 = n) = decide (v = []) := by
        simp only [List.length_cons] at h
        rcases v with - | ⟨a', v'⟩
        · simp only [List.length_nil] at h
          simp
          omega
        · simp only [List.length_cons] at h
          simp
          omega
      rw [hb, hl]

lemma midMark_eq_markFL (v : List A) : midMark v = markFL v true := by
  rw [midMark, markGen_eq_markFL v 0 v.length (by simp)]
  simp

/-- The marks put on the letters that the delayed automaton has already
processed: the pending letter `c` (with its flag `b`) followed by all but the
last letter of `t`. -/
def pendMarks (lt : C → A) : C → Bool → List C → List (Mark2 A)
  | _, _, [] => []
  | c, b, d :: t => (lt c, b, false) :: pendMarks lt d false t

lemma markFL_map (lt : C → A) (t : List C) (c : C) (b : Bool) :
    markFL ((c :: t).map lt) b =
      pendMarks lt c b t ++ [(lt (lastC c t), (if t = [] then b else false), true)] := by
  induction t generalizing c b with
  | nil => simp [markFL, pendMarks, lastC]
  | cons d t ih =>
      rw [List.map_cons, List.map_cons, markFL, ← List.map_cons, ih d false]
      simp [pendMarks, lastC_cons]

/-! ## The delayed automaton -/

variable (lt : C → A) (D : DFA (Mark2 A) S) (st : C → S) (tr : C → S → S)

/-- The transition function: the pending letter is processed when the next
letter arrives. -/
def delayStep : Option (S × C × Bool) → C → Option (S × C × Bool)
  | none, c => some (st c, c, true)
  | some (s, c, b), c' => some (D.step s (lt c, b, false), c', false)

/-- The accepting states: the pending letter is processed as the last letter of
the string, and the state transformation it carries is applied. -/
def delayAcc : Set (Option (S × C × Bool)) :=
  {q | ∃ s c b, q = some (s, c, b) ∧ tr c (D.step s (lt c, b, true)) ∈ D.accept}

/-- The language of the delayed automaton. -/
def delayLang : Language C :=
  {u : List C | u.foldl (delayStep lt D st) none ∈ delayAcc lt D tr}

lemma foldl_delay (t : List C) (s : S) (c : C) (b : Bool) :
    t.foldl (delayStep lt D st) (some (s, c, b)) =
      some ((pendMarks lt c b t).foldl D.step s, lastC c t,
        if t = [] then b else false) := by
  induction t generalizing s c b with
  | nil => simp [lastC, pendMarks]
  | cons d t ih =>
      show t.foldl (delayStep lt D st) (delayStep lt D st (some (s, c, b)) d) = _
      rw [show delayStep lt D st (some (s, c, b)) d
            = some (D.step s (lt c, b, false), d, false) from rfl, ih]
      simp [pendMarks, lastC_cons]

lemma mem_delayLang (c : C) (t : List C) :
    (c :: t) ∈ delayLang lt D st tr ↔
      tr (lastC c t) ((midMark ((c :: t).map lt)).foldl D.step (st c)) ∈ D.accept := by
  have hfold : (c :: t).foldl (delayStep lt D st) none =
      some ((pendMarks lt c true t).foldl D.step (st c), lastC c t,
        if t = [] then true else false) := by
    show t.foldl (delayStep lt D st) (delayStep lt D st none c) = _
    rw [show delayStep lt D st none c = some (st c, c, true) from rfl, foldl_delay]
  rw [midMark_eq_markFL, markFL_map lt t c true, List.foldl_append]
  change (c :: t).foldl (delayStep lt D st) none ∈ delayAcc lt D tr ↔ _
  rw [hfold, delayAcc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, c', b, heq, hacc⟩
    obtain ⟨rfl, rfl, rfl⟩ : s = (pendMarks lt c true t).foldl D.step (st c) ∧
        c' = lastC c t ∧ b = (if t = [] then true else false) := by
      simpa [Prod.ext_iff] using heq.symm
    simpa using hacc
  · intro hacc
    exact ⟨_, _, _, rfl, by simpa using hacc⟩

lemma isRegular_delayLang [Finite S] [Finite C] : (delayLang lt D st tr).IsRegular :=
  RegAut.isRegular_foldl (delayStep lt D st) none (delayAcc lt D tr)

end MarkDelay
end Lax314295Proofs.Transducers
