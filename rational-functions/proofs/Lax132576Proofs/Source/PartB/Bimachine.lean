/-
Bimachines (Definition `def:bimachine`) and the easy implication of Theorem `thm:bimachines`: every
function computed by a bimachine is rational.

The definitions of a bimachine and of its semantics are here (moved from
`RequestProject/PartB/RationalStatements.lean`) so that they can be used in the proofs
of Theorem `thm:bimachines`.

A bimachine is turned into an nfa with output by guessing, at each position, the
state of the suffix automaton at the *next* gap: the automaton reads the input
from left to right in a state `(p, s)` consisting of the state of the prefix
automaton at the current gap and the state of the suffix automaton at the same
gap, which it verifies step by step.
-/
import Lax132576Proofs.Source.PartB.Uniform
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-- **Definition `def:bimachine` (Bimachine).**  A bimachine consists of a deterministic
prefix automaton, a deterministic suffix automaton (which is run on the reverse
of the suffix) and an output function on pairs of states. -/
structure Bimachine (A B P S : Type) where
  /-- Initial state of the prefix automaton. -/
  prefixInit : P
  /-- Transition function of the prefix automaton. -/
  prefixStep : P → A → P
  /-- Initial state of the suffix automaton. -/
  suffixInit : S
  /-- Transition function of the suffix automaton. -/
  suffixStep : S → A → S
  /-- The output function. -/
  out : P → S → List B

namespace Bimachine

variable {A B P S : Type}

/-- The output of a bimachine on the string `w`, when the prefix automaton
starts in the state `p`. -/
def evalFrom (M : Bimachine A B P S) (p : P) (w : List A) : List B :=
  ((List.range (w.length + 1)).map (fun i =>
    M.out (strTrans M.prefixStep (w.take i) p)
          (strTrans M.suffixStep (w.drop i).reverse M.suffixInit))).flatten

/-- The semantics of a bimachine: for every gap of the input string, the prefix
automaton is run on the prefix, the suffix automaton on the reverse of the
suffix, and the corresponding pieces of output are concatenated. -/
def eval (M : Bimachine A B P S) (w : List A) : List B :=
  ((List.range (w.length + 1)).map (fun i =>
    M.out (strTrans M.prefixStep (w.take i) M.prefixInit)
          (strTrans M.suffixStep (w.drop i).reverse M.suffixInit))).flatten

lemma eval_eq_evalFrom (M : Bimachine A B P S) (w : List A) :
    M.eval w = M.evalFrom M.prefixInit w := rfl

@[simp] lemma evalFrom_nil (M : Bimachine A B P S) (p : P) :
    M.evalFrom p [] = M.out p M.suffixInit := by
  simp [evalFrom, strTrans]

lemma evalFrom_cons (M : Bimachine A B P S) (p : P) (a : A) (w : List A) :
    M.evalFrom p (a :: w) =
      M.out p (strTrans M.suffixStep (a :: w).reverse M.suffixInit) ++
        M.evalFrom (M.prefixStep p a) w := by
  have key : ∀ (n : ℕ) (g : ℕ → List B),
      ((List.range (n + 1)).map g).flatten =
        g 0 ++ ((List.range n).map (fun i => g (i + 1))).flatten := by
    intro n g
    rw [List.range_succ_eq_map]
    simp [Function.comp_def]
  rw [evalFrom]
  simp only [List.length_cons]
  rw [key]
  have e1 : M.out (strTrans M.prefixStep ((a :: w).take 0) p)
      (strTrans M.suffixStep ((a :: w).drop 0).reverse M.suffixInit)
      = M.out p (strTrans M.suffixStep (a :: w).reverse M.suffixInit) := by simp [strTrans]
  have e2 : ((List.range (w.length + 1)).map (fun i =>
      M.out (strTrans M.prefixStep ((a :: w).take (i + 1)) p)
        (strTrans M.suffixStep ((a :: w).drop (i + 1)).reverse M.suffixInit))).flatten
      = M.evalFrom (M.prefixStep p a) w := by
    rw [evalFrom]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i _
    simp [strTrans]
  rw [e1, e2]

end Bimachine

/-- A string-to-string function computed by a bimachine. -/
def IsBimachine {A B : Type} (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S), M.eval = f

/-- A function computed by an *aperiodic* bimachine: both the prefix and the
suffix automaton are aperiodic (Section *The first-order fragment*). -/
def IsAperiodicBimachine {A B : Type} (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S),
    M.eval = f ∧ TransAperiodic M.prefixStep ∧ TransAperiodic M.suffixStep

namespace BimachRat

open LabAut NFAO

variable {A B P S : Type} (M : Bimachine A B P S)

/-- The states of the nfa with output associated with a bimachine: a state of
the prefix automaton together with the guessed state of the suffix automaton,
plus a final sink. -/
abbrev St (P S : Type) : Type := Option (P × S)

/-- The nfa with output associated with a bimachine. -/
def aut [Finite A] [Finite P] [Finite S] : NFAO A B (St P S) where
  init := {z | ∃ s : S, z = some (M.prefixInit, s)}
  final := {none}
  δ := {z | ∃ (p : P) (s' : S) (a : A),
      z = (some (p, M.suffixStep s' a), [a], M.out p (M.suffixStep s' a),
        some (M.prefixStep p a, s'))} ∪
    {z | ∃ p : P, z = (some (p, M.suffixInit), [], M.out p M.suffixInit, none)}
  δ_finite := by
    refine Set.Finite.union ?_ ?_
    · refine Set.Finite.subset (Set.finite_range (fun x : P × S × A =>
        (some (x.1, M.suffixStep x.2.1 x.2.2), [x.2.2], M.out x.1 (M.suffixStep x.2.1 x.2.2),
          some (M.prefixStep x.1 x.2.2, x.2.1)))) ?_
      rintro z ⟨p, s', a, rfl⟩
      exact ⟨(p, s', a), rfl⟩
    · refine Set.Finite.subset (Set.finite_range (fun p : P =>
        (some (p, M.suffixInit), ([] : List A), M.out p M.suffixInit, (none : St P S)))) ?_
      rintro z ⟨p, rfl⟩
      exact ⟨p, rfl⟩

variable [Finite A] [Finite P] [Finite S]

lemma aut_delta_mem {z : St P S × List A × List B × St P S} :
    z ∈ (aut M).δ ↔
      (∃ (p : P) (s' : S) (a : A),
        z = (some (p, M.suffixStep s' a), [a], M.out p (M.suffixStep s' a),
          some (M.prefixStep p a, s'))) ∨
      (∃ p : P, z = (some (p, M.suffixInit), [], M.out p M.suffixInit, none)) := Iff.rfl

/-- Every run of the automaton ending in the sink computes the output of the
bimachine on the remaining suffix. -/
lemma relFrom_to_none {q : St P S} {w : List A} {v : List B}
    (h : (aut M).relFrom q w v none) :
    (∀ (p : P) (s : S), q = some (p, s) →
      s = strTrans M.suffixStep w.reverse M.suffixInit ∧ v = M.evalFrom p w) ∧
    (q = none → w = [] ∧ v = []) := by
  refine NFAO.relFrom_induction (M := aut M)
    (motive := fun q w v =>
      (∀ (p : P) (s : S), q = some (p, s) →
        s = strTrans M.suffixStep w.reverse M.suffixInit ∧ v = M.evalFrom p w) ∧
      (q = none → w = [] ∧ v = [])) ?_ ?_ h
  · exact ⟨fun p s hps => absurd hps (by simp), fun _ => ⟨rfl, rfl⟩⟩
  · rintro q q' u x w v ht - ih
    rcases (aut_delta_mem M).mp ht with ⟨p, s', a, heq⟩ | ⟨p, heq⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      obtain ⟨h1, -⟩ := ih
      obtain ⟨hs', hv⟩ := h1 (M.prefixStep p a) s' rfl
      refine ⟨fun p₀ s₀ hps => ?_, fun hnone => absurd hnone (by simp)⟩
      obtain ⟨rfl, rfl⟩ : p₀ = p ∧ s₀ = M.suffixStep s' a := by
        have := Option.some.inj hps
        exact ⟨(Prod.mk.injEq .. ▸ this).1.symm, (Prod.mk.injEq .. ▸ this).2.symm⟩
      constructor
      · rw [hs']
        simp [strTrans]
      · rw [List.singleton_append, M.evalFrom_cons, hv]
        congr 2
        rw [hs']
        simp [strTrans]
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      obtain ⟨-, h2⟩ := ih
      obtain ⟨rfl, rfl⟩ := h2 rfl
      refine ⟨fun p₀ s₀ hps => ?_, fun hnone => absurd hnone (by simp)⟩
      obtain ⟨rfl, rfl⟩ : p₀ = p ∧ s₀ = M.suffixInit := by
        have := Option.some.inj hps
        exact ⟨(Prod.mk.injEq .. ▸ this).1.symm, (Prod.mk.injEq .. ▸ this).2.symm⟩
      exact ⟨by simp [strTrans], by simp⟩

/-- Conversely, the run guessing the correct suffix states exists. -/
lemma relFrom_exists (p : P) (w : List A) :
    (aut M).relFrom (some (p, strTrans M.suffixStep w.reverse M.suffixInit))
      w (M.evalFrom p w) none := by
  induction w generalizing p with
  | nil =>
      have : (some (p, M.suffixInit), ([] : List A), M.out p M.suffixInit, (none : St P S)) ∈
          (aut M).δ := Or.inr ⟨p, rfl⟩
      simpa [strTrans] using NFAO.relFrom_single this
  | cons a w ih =>
      have hstep : strTrans M.suffixStep (a :: w).reverse M.suffixInit =
          M.suffixStep (strTrans M.suffixStep w.reverse M.suffixInit) a := by
        simp [strTrans]
      have ht : (some (p, M.suffixStep (strTrans M.suffixStep w.reverse M.suffixInit) a), [a],
          M.out p (M.suffixStep (strTrans M.suffixStep w.reverse M.suffixInit) a),
          some (M.prefixStep p a, strTrans M.suffixStep w.reverse M.suffixInit)) ∈ (aut M).δ :=
        Or.inl ⟨p, strTrans M.suffixStep w.reverse M.suffixInit, a, rfl⟩
      have := NFAO.relFrom_step ht (ih (M.prefixStep p a))
      rw [hstep]
      rw [M.evalFrom_cons, hstep]
      simpa using this

/-- The automaton computes the function of the bimachine. -/
theorem aut_rel (w : List A) (v : List B) : (aut M).rel w v ↔ v = M.eval w := by
  rw [NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨q, ⟨s, rfl⟩, p, hp, hrel⟩
    have hp' : p = none := hp
    subst hp'
    obtain ⟨h1, -⟩ := relFrom_to_none M hrel
    exact (h1 M.prefixInit s rfl).2
  · rintro rfl
    exact ⟨some (M.prefixInit, strTrans M.suffixStep w.reverse M.suffixInit),
      ⟨_, rfl⟩, none, rfl, relFrom_exists M M.prefixInit w⟩

end BimachRat

/-- A function computed by a bimachine is rational. -/
theorem rationalFun_of_isBimachine {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsBimachine f) : IsRationalFun f := by
  obtain ⟨P, S, hP, hS, M, rfl⟩ := hf
  exact ⟨BimachRat.St P S, inferInstance, BimachRat.aut M,
    fun w v => (BimachRat.aut_rel M w v).symm⟩

end Lax132576Proofs.Transducers
