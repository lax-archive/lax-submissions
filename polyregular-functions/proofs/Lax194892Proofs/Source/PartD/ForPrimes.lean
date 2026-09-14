/-
Part D: the prime polyregular functions are computed by for-transducers.

This file proves that each of the prime polyregular functions -- the rational functions (through
the bimachines that compute them, Theorem `thm:bimachines`), map reverse, map duplicate and
marked squaring -- is computed by a for-transducer.  Map reverse and map duplicate are treated
in `RequestProject/PartD/ForMapRev.lean`.  Together with Lemma
`lem:for-closed-under-composition` this gives the left-to-right inclusion of Theorem
`thm:for-transducers-are-polyregular`, in `RequestProject/PartD/ForPolyreg.lean`.

Every construction is written in the machine language of
`RequestProject/PartD/ForMachine.lean` and compiled by `Transducers.isForTransducer_of_mprog`.
-/
import Lax194892Proofs.Source.PartD.ForMachine
import Lax194892Proofs.Source.PartD.ForMapRev
import Lax194892Proofs.Source.PartD.PolyDef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-! ## Running a machine program whose state is trivial -/

lemma runList_snd_unit {α B : Type} (step : Unit → α → Unit × List B) (as : List α) (s : Unit) :
    (runList step as s).2 = (as.map (fun a => (step () a).2)).flatten := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [runList_cons, List.map_cons, List.flatten_cons]
      exact congrArg (fun l => (step s a).2 ++ l) (ih _)

/-- Reading the letters of a string through `getElem?` along the range of its length. -/
lemma flatten_map_singleton {A γ : Type} (g : A → γ) (w : List A) :
    ((w.map (fun a => [g a])).flatten) = w.map g := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

/-- Reading the letters of a string through `getElem?` along the range of its length. -/
lemma map_range_getElem?_elim {A γ : Type} (g : A → List γ) (w : List A) :
    (List.range w.length).map (fun p => (w[p]?).elim [] g) = w.map g := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      have hcomp : (fun p => ((a :: w)[p]?).elim [] g) ∘ Nat.succ
          = (fun p => (w[p]?).elim [] g) := by
        funext p; simp
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, hcomp, ih]
      simp

/-! ## Homomorphisms -/

/-- The machine program computing a homomorphism: one forward loop that outputs `φ a` at every
position. -/
def homProg {A B : Type} (φ : A → List B) : MProg A B Unit :=
  MProg.loop true 0 (MProg.act2 0 0 (fun q oa _ _ _ => (q, oa.elim [] φ)))

lemma sem_homProg {A B : Type} (φ : A → List B) (w : List A) (pos : ℕ → ℕ) :
    ((homProg φ).sem w pos ()).2 = homOf φ w := by
  rw [homProg, MProg.sem_loop, runList_snd_unit]
  simp only [loopRange_true, MProg.sem_act2, Function.update_self]
  rw [map_range_getElem?_elim]
  rfl

/-- **A homomorphism is computed by a for-transducer.** -/
theorem isForTransducer_homOf {A B : Type} [Finite A] (φ : A → List B) :
    IsForTransducer (homOf φ) :=
  isForTransducer_of_mprog (homProg φ) () _ (fun w => sem_homProg φ w _)

/-! ## Marked squaring -/

/-- One copy of the marked square, read off position by position. -/
lemma flatten_mark {A : Type} : ∀ (w : List A) (i : ℕ),
    ((List.range w.length).map (fun j =>
        (w[j]?).elim [] (fun a => [if j ≤ i then Sum.inl a else Sum.inr a]))).flatten
      = (w.take (i + 1)).map Sum.inl ++ (w.drop (i + 1)).map Sum.inr := by
  intro w
  induction w with
  | nil => intro i; rfl
  | cons a w ih =>
      intro i
      cases i with
      | zero =>
          have hcomp : (fun j => ((a :: w)[j]?).elim []
                (fun b => [if j ≤ 0 then Sum.inl b else Sum.inr b])) ∘ Nat.succ
              = (fun j => (w[j]?).elim [] (fun b => [(Sum.inr b : A ⊕ A)])) := by
            funext j; simp
          rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, hcomp,
            List.flatten_cons, map_range_getElem?_elim, flatten_map_singleton]
          simp
      | succ i =>
          have hcomp : (fun j => ((a :: w)[j]?).elim []
                (fun b => [if j ≤ i + 1 then Sum.inl b else Sum.inr b])) ∘ Nat.succ
              = (fun j => (w[j]?).elim []
                  (fun b => [if j ≤ i then (Sum.inl b : A ⊕ A) else Sum.inr b])) := by
            funext j
            simp
          rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, hcomp,
            List.flatten_cons, ih i]
          simp

/-- The machine program computing marked squaring: two nested forward loops, the letter at the
inner position being underlined exactly when it is at most the outer position. -/
def msProg (A : Type) : MProg A (A ⊕ A) Unit :=
  MProg.loop true 1 (MProg.loop true 2
    (MProg.act2 2 1 (fun q oa _ c₁ _ => (q, oa.elim [] (fun a => [if c₁ then Sum.inl a else Sum.inr a])))))

lemma sem_msProg (A : Type) (w : List A) (pos : ℕ → ℕ) :
    ((msProg A).sem w pos ()).2 = markedSquare A w := by
  rw [msProg, MProg.sem_loop, runList_snd_unit]
  simp only [loopRange_true, MProg.sem_loop]
  rw [markedSquare]
  congr 1
  refine List.map_congr_left ?_
  intro i _
  rw [runList_snd_unit]
  simp only [MProg.sem_act2, Function.update_self,
    Function.update_of_ne (show (1 : ℕ) ≠ 2 by decide)]
  rw [← flatten_mark w i]
  congr 1
  refine List.map_congr_left ?_
  intro j _
  simp

/-- **Marked squaring is computed by a for-transducer.** -/
theorem isForTransducer_markedSquare (A : Type) [Finite A] :
    IsForTransducer (markedSquare A) :=
  isForTransducer_of_mprog (msProg A) () _ (fun w => sem_msProg A w _)

/-! ## Rational functions -/

section Bimach

variable {A B P S : Type}

/-! Three folding lemmas used to compute the semantics of the machine program below. -/

/-- A fold whose state is a pair, and whose steps only touch the second component. -/
lemma runList_pair_snd {T S α B : Type} (f : S → α → S × List B) (as : List α) (t : T) (s : S) :
    runList (fun (q : T × S) (a : α) => ((q.1, (f q.2 a).1), (f q.2 a).2)) as (t, s)
      = ((t, (runList f as s).1), (runList f as s).2) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp only [runList_cons, ih]

/-- A fold whose state is a pair, and whose steps read only the first component. -/
lemma runList_pair_fst {T S α B : Type} (f : T → α → T × List B) (h : T → α → S) (as : List α) :
    ∀ (t : T) (s : S),
      (runList (fun (q : T × S) (a : α) => (((f q.1 a).1, h q.1 a), (f q.1 a).2)) as (t, s)).1.1
          = (runList f as t).1 ∧
      (runList (fun (q : T × S) (a : α) => (((f q.1 a).1, h q.1 a), (f q.1 a).2)) as (t, s)).2
          = (runList f as t).2 := by
  induction as with
  | nil => intro t s; exact ⟨rfl, rfl⟩
  | cons a as ih =>
      intro t s
      simp only [runList_cons]
      exact ⟨(ih (f t a).1 (h t a)).1, congrArg (fun l => (f t a).2 ++ l) (ih (f t a).1 (h t a)).2⟩

/-- A backward loop that applies the transition `step` at every position at least `x` runs the
automaton on the reverse of the suffix starting at `x`. -/
lemma runList_back_suffix {A S B : Type} (step : S → A → S) (w : List A) (x : ℕ) :
    ∀ (n : ℕ), n ≤ w.length → ∀ s : S,
      runList (fun (s' : S) (p : ℕ) =>
          ((if x ≤ p then (w[p]?).elim s' (fun a => step s' a) else s'), ([] : List B)))
        (List.range n).reverse s
        = (strTrans step ((w.take n).drop x).reverse s, []) := by
  intro n
  induction n with
  | zero => intro _ s; simp [strTrans]
  | succ n ih =>
      intro hn s
      have hnw : n < w.length := by omega
      have hlen : (w.take n).length = n := by
        simp [Nat.min_eq_left (le_of_lt hnw)]
      have hsucc : w.take (n + 1) = w.take n ++ [w[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hnw]; rfl
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      rw [runList_cons, ih (by omega)]
      simp only [List.nil_append]
      refine Prod.ext ?_ rfl
      by_cases hx : x ≤ n
      · have hd : (w.take (n + 1)).drop x = (w.take n).drop x ++ [w[n]] := by
          rw [hsucc, List.drop_append_of_le_length (by omega)]
        simp only [hd, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append, if_pos hx,
          List.getElem?_eq_getElem hnw, Option.elim_some]
        rfl
      · have h1 : (w.take (n + 1)).drop x = [] := by
          refine List.drop_eq_nil_of_le ?_
          have : (w.take (n + 1)).length ≤ n + 1 := by simp
          omega
        have h2 : (w.take n).drop x = [] := by
          refine List.drop_eq_nil_of_le ?_
          omega
        simp only [h1, h2, if_neg hx]

/-- A forward loop that applies the transition `step` at every position and emits `g` computed
from the state reached so far. -/
lemma runList_range_scan {A P B : Type} (step : P → A → P) (g : P → ℕ → List B) (w : List A) :
    ∀ (n : ℕ), n ≤ w.length → ∀ p : P,
      runList (fun (p' : P) (i : ℕ) => ((w[i]?).elim p' (fun a => step p' a), g p' i))
        (List.range n) p
      = (strTrans step (w.take n) p,
         ((List.range n).map (fun i => g (strTrans step (w.take i) p) i)).flatten) := by
  intro n
  induction n with
  | zero => intro _ p; simp [strTrans]
  | succ n ih =>
      intro hn p
      have hnw : n < w.length := by omega
      have hsucc : w.take (n + 1) = w.take n ++ [w[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hnw]; rfl
      rw [List.range_succ, runList_append, ih (by omega)]
      simp only [runList_cons, runList_nil, List.getElem?_eq_getElem hnw, Option.elim_some,
        List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      refine Prod.ext ?_ rfl
      rw [hsucc, strTrans, strTrans, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The state of the suffix automaton at the gap before position `i`. -/
def bimSuf (M : Bimachine A B P S) (w : List A) (i : ℕ) : S :=
  strTrans M.suffixStep (w.drop i).reverse M.suffixInit

/-- The step of the outer loop of the machine program computing a bimachine: the prefix
automaton advances and the output at the gap before the current position is emitted. -/
def bimStep (M : Bimachine A B P S) (w : List A) (p : P) (i : ℕ) : P × List B :=
  ((w[i]?).elim p (fun a => M.prefixStep p a), M.out p (bimSuf M w i))

/-- The body of the outer loop: the suffix automaton is reset and run backwards over the
positions at least the current one, then the output at the current gap is emitted and the prefix
automaton advances. -/
def bimBody (M : Bimachine A B P S) : MProg A B (P × S) :=
  MProg.seq (MProg.act (fun q => ((q.1, M.suffixInit), [])))
    (MProg.seq
      (MProg.loop false 1 (MProg.act2 1 0 (fun q oa _ _ c₂ =>
        ((q.1, if c₂ then oa.elim q.2 (fun a => M.suffixStep q.2 a) else q.2), []))))
      (MProg.act2 0 0 (fun q oa _ _ _ =>
        ((oa.elim q.1 (fun a => M.prefixStep q.1 a), q.2), M.out q.1 q.2))))

/-- The machine program computing a bimachine. -/
def bimProg (M : Bimachine A B P S) : MProg A B (P × S) :=
  MProg.seq (MProg.loop true 0 (bimBody M))
    (MProg.act (fun q => (q, M.out q.1 M.suffixInit)))

lemma sem_bimBody (M : Bimachine A B P S) (w : List A) (pos : ℕ → ℕ) (i : ℕ) (q : P × S) :
    MProg.sem w (bimBody M) (Function.update pos 0 i) q
      = (((bimStep M w q.1 i).1, bimSuf M w i), (bimStep M w q.1 i).2) := by
  have hupd0 : ∀ p : ℕ, (Function.update (Function.update pos 0 i) 1 p) 0 = i := by
    intro p
    rw [Function.update_of_ne (by decide), Function.update_self]
  have hupd1 : ∀ p : ℕ, (Function.update (Function.update pos 0 i) 1 p) 1 = p := by
    intro p; rw [Function.update_self]
  rw [bimBody]
  simp only [MProg.sem_seq, MProg.sem_act, MProg.sem_loop, MProg.sem_act2, loopRange_false,
    hupd0, hupd1, decide_eq_true_eq]
  have hinner : runList (fun (q' : P × S) (p : ℕ) =>
        ((q'.1, if i ≤ p then (w[p]?).elim q'.2 (fun a => M.suffixStep q'.2 a) else q'.2),
          ([] : List B)))
      (List.range w.length).reverse (q.1, M.suffixInit)
      = ((q.1, bimSuf M w i), []) := by
    rw [runList_pair_snd (f := fun (s : S) (p : ℕ) =>
      ((if i ≤ p then (w[p]?).elim s (fun a => M.suffixStep s a) else s), ([] : List B)))]
    rw [runList_back_suffix M.suffixStep w i w.length le_rfl]
    simp only [List.take_length, bimSuf]
  rw [hinner]
  simp only [Function.update_self, bimStep, List.nil_append]

lemma sem_bimProg (M : Bimachine A B P S) (w : List A) (pos : ℕ → ℕ) :
    ((bimProg M).sem w pos (M.prefixInit, M.suffixInit)).2 = M.eval w := by
  have hstep : (fun (q : P × S) (p : ℕ) =>
        MProg.sem w (bimBody M) (Function.update pos 0 p) q)
      = (fun (q : P × S) (i : ℕ) =>
          (((bimStep M w q.1 i).1, bimSuf M w i), (bimStep M w q.1 i).2)) :=
    funext fun q => funext fun i => sem_bimBody M w pos i q
  rw [bimProg, MProg.sem_seq, MProg.sem_loop, loopRange_true, hstep]
  obtain ⟨h1, h2⟩ := runList_pair_fst (bimStep M w) (fun (_ : P) (i : ℕ) => bimSuf M w i)
    (List.range w.length) M.prefixInit M.suffixInit
  simp only [MProg.sem_act]
  rw [h1, h2]
  have hbs : bimStep M w
      = fun (p : P) (i : ℕ) =>
          ((w[i]?).elim p (fun a => M.prefixStep p a), M.out p (bimSuf M w i)) := rfl
  rw [hbs, runList_range_scan M.prefixStep (fun p i => M.out p (bimSuf M w i)) w w.length le_rfl]
  rw [Bimachine.eval, List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.take_length, bimSuf,
    List.drop_length, List.reverse_nil, strTrans, List.foldl_nil]

/-- **A bimachine is simulated by a for-transducer.** -/
theorem isForTransducer_of_isBimachine {A B : Type} [Finite A] {f : List A → List B}
    (hf : IsBimachine f) : IsForTransducer f := by
  obtain ⟨P, S, hP, hS, M, hM⟩ := hf
  haveI := hP
  haveI := hS
  exact isForTransducer_of_mprog (bimProg M) (M.prefixInit, M.suffixInit) f
    (fun w => by rw [sem_bimProg M w]; exact congrFun hM w)

end Bimach

/-- **A rational function is computed by a for-transducer.** -/
theorem isForTransducer_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : IsForTransducer f :=
  isForTransducer_of_isBimachine (isBimachine_of_rationalFun hf)

end Lax194892Proofs.Transducers
