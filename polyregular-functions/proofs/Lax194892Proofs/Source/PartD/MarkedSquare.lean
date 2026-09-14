/-
Marked squaring (Example 33 of *Transducers*, M. Bojańczyk) and its continuity,
which is the missing ingredient in the proof of Theorem `thm:polyregular-functions-are-continuous`.

The definition of marked squaring itself lives in this file, so that the
construction below can be developed before the statements of Part D.

Continuity is proved by running a deterministic automaton `D` for the target
language on the marked square, from right to left.  After the suffix `y` of the
input has been read, the automaton remembers two pieces of information:

* the state transformation `p ↦ D.evalFrom p (y underlined by `Sum.inr`)`, and
* the map sending the state transformation `t` of the underlined prefix to the
  state transformation of the part of the marked square that is contributed by
  the positions of `y`.

Both live in a finite set, so this is a deterministic automaton reading the
input backwards; regularity of the inverse image then follows because regular
languages are closed under reversal.
-/
import Lax916827Proofs.Source.PartC.Statements
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-- **Example 33 (Marked squaring).**  The input string of length `n` is copied
`n` times, and in the `i`-th copy the first `i` letters are underlined
(`Sum.inl` marks an underlined letter). -/
def markedSquare (A : Type) (w : List A) : List (A ⊕ A) :=
  ((List.range w.length).map
    (fun i => (w.take (i + 1)).map Sum.inl ++ (w.drop (i + 1)).map Sum.inr)).flatten

section

variable {A : Type}

/-- The part of the marked square of `x ++ y` that is contributed by the
positions of `y`: for every position of `y`, the prefix `x` and the part of `y`
up to that position are underlined. -/
def msBlocks (x y : List A) : List (A ⊕ A) :=
  ((List.range y.length).map
    (fun i => (x ++ y.take (i + 1)).map Sum.inl ++ (y.drop (i + 1)).map Sum.inr)).flatten

lemma markedSquare_eq_msBlocks (w : List A) : markedSquare A w = msBlocks [] w := by
  simp [markedSquare, msBlocks]

@[simp] lemma msBlocks_nil (x : List A) : msBlocks x [] = [] := by simp [msBlocks]

lemma msBlocks_cons (x : List A) (a : A) (y : List A) :
    msBlocks x (a :: y)
      = ((x ++ [a]).map Sum.inl ++ y.map Sum.inr) ++ msBlocks (x ++ [a]) y := by
  unfold msBlocks
  rw [show (a :: y).length = y.length + 1 from rfl, List.range_succ_eq_map]
  simp only [List.map_cons, List.flatten_cons, List.map_map]
  congr 1
  simp [Function.comp_def]

variable {σ : Type} (D : DFA (A ⊕ A) σ)

/-- The state transformation of an underlined string. -/
def msAlpha (u : List A) : σ → σ := fun p => D.evalFrom p (u.map Sum.inl)

/-- The state transformation of a string that is not underlined. -/
def msBeta (u : List A) : σ → σ := fun p => D.evalFrom p (u.map Sum.inr)

@[simp] lemma msAlpha_nil : msAlpha D ([] : List A) = id := rfl

lemma msAlpha_append_singleton (x : List A) (a : A) :
    msAlpha D (x ++ [a]) = fun q => D.step (msAlpha D x q) (Sum.inl a) := by
  funext q
  simp [msAlpha, DFA.evalFrom]

/-- The state of the right-to-left automaton after reading the suffix `y`. -/
def msState : List A → ((σ → σ) → (σ → σ)) × (σ → σ)
  | [] => (fun _ => id, id)
  | a :: y =>
      (fun t p => (msState y).1 (fun q => D.step (t q) (Sum.inl a))
          ((msState y).2 (D.step (t p) (Sum.inl a))),
       fun p => (msState y).2 (D.step p (Sum.inr a)))

lemma msState_snd (y : List A) : (msState D y).2 = msBeta D y := by
  induction y with
  | nil => rfl
  | cons a y ih =>
      funext p
      show (msState D y).2 (D.step p (Sum.inr a)) = _
      rw [ih]
      simp [msBeta, DFA.evalFrom]

lemma msState_fst (y : List A) : ∀ (x : List A) (p : σ),
    (msState D y).1 (msAlpha D x) p = D.evalFrom p (msBlocks x y) := by
  induction y with
  | nil => intro x p; simp [msState]
  | cons a y ih =>
      intro x p
      show (msState D y).1 (fun q => D.step (msAlpha D x q) (Sum.inl a))
          ((msState D y).2 (D.step (msAlpha D x p) (Sum.inl a))) = _
      rw [← msAlpha_append_singleton, msState_snd,
        show D.step (msAlpha D x p) (Sum.inl a) = msAlpha D (x ++ [a]) p by
          rw [msAlpha_append_singleton], ih (x ++ [a])]
      rw [msBlocks_cons, DFA.evalFrom_of_append, DFA.evalFrom_of_append]
      rfl

/-- The automaton reading the input from right to left. -/
def msDFA : DFA A (((σ → σ) → (σ → σ)) × (σ → σ)) where
  step := fun s a =>
    (fun t p => s.1 (fun q => D.step (t q) (Sum.inl a)) (s.2 (D.step (t p) (Sum.inl a))),
     fun p => s.2 (D.step p (Sum.inr a)))
  start := (fun _ => id, id)
  accept := {s | s.1 id D.start ∈ D.accept}

lemma msDFA_eval_reverse (y : List A) : (msDFA D).eval y.reverse = msState D y := by
  induction y with
  | nil => rfl
  | cons a y ih =>
      rw [List.reverse_cons, DFA.eval, DFA.evalFrom_of_append, ← DFA.eval, ih]
      rfl

end

/-- Marked squaring is continuous. -/
theorem continuous_markedSquare (A : Type) : Continuous (markedSquare A) := by
  rintro L ⟨σ, hσ, D, rfl⟩
  haveI : Finite σ := Finite.of_fintype σ
  haveI : Fintype (((σ → σ) → (σ → σ)) × (σ → σ)) := Fintype.ofFinite _
  have hreg : ((msDFA D).accepts).IsRegular := ⟨_, inferInstance, msDFA D, rfl⟩
  convert hreg.reverse using 1
  ext w
  have h := msState_fst D w [] D.start
  simp only [msAlpha_nil] at h
  show markedSquare A w ∈ D.accepts ↔ _
  rw [DFA.mem_accepts, DFA.eval, markedSquare_eq_msBlocks, ← h]
  constructor
  · intro hw
    show w.reverse ∈ (msDFA D).accepts
    rw [DFA.mem_accepts, msDFA_eval_reverse]
    exact hw
  · intro hw
    have hw' : w.reverse ∈ (msDFA D).accepts := hw
    rw [DFA.mem_accepts, msDFA_eval_reverse] at hw'
    exact hw'

end Lax194892Proofs.Transducers
