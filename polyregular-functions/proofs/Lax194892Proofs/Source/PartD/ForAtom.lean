/-
Part D: for-transducers -- atomic tests, constant programs and the letters of a program.

Three small preparations for the proof of Lemma `lem:for-closed-under-composition`.

The first one is the *atomisation* of a program: pushing the Boolean connectives of a test out of
the test and into the program, `Transducers.ForProg.atomize` turns every program into an equivalent
one all of whose conditionals test an atomic test -- a Boolean variable, a comparison of two
position variables or a label test.  This is what lets the translation of the outer for-transducer
compute, in one Boolean flag, the answer to the single label test of a conditional.

The second one is `Transducers.constProg`, the program that outputs a fixed string, and the third
one is the observation that the run of a program only depends on the input through its length and
through the positions of the (finitely many) letters that the program mentions.
-/
import Lax194892Proofs.Source.PartD.ForResim

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B C : Type}

/-! ## Atomic tests -/

namespace ForTest

/-- A test with no Boolean connective. -/
def Atomic : ForTest A → Prop
  | boolVar _ => True
  | eqPos _ _ => True
  | lePos _ _ => True
  | label _ _ => True
  | not _ => False
  | and _ _ => False
  | or _ _ => False

end ForTest

namespace ForProg

/-- A program all of whose conditionals test an atomic test. -/
def AllAtomic : ForProg A B → Prop
  | skip => True
  | output _ => True
  | assign _ _ => True
  | seq P Q => AllAtomic P ∧ AllAtomic Q
  | ite t P Q => t.Atomic ∧ AllAtomic P ∧ AllAtomic Q
  | loop _ _ P => AllAtomic P

/-- The conditional on an arbitrary test, expanded into conditionals on atomic tests. -/
def iteAtom : ForTest A → ForProg A B → ForProg A B → ForProg A B
  | ForTest.not t, P, R => iteAtom t R P
  | ForTest.and t s, P, R => iteAtom t (iteAtom s P R) R
  | ForTest.or t s, P, R => iteAtom t P (iteAtom s P R)
  | ForTest.boolVar i, P, R => ForProg.ite (ForTest.boolVar i) P R
  | ForTest.eqPos i j, P, R => ForProg.ite (ForTest.eqPos i j) P R
  | ForTest.lePos i j, P, R => ForProg.ite (ForTest.lePos i j) P R
  | ForTest.label i a, P, R => ForProg.ite (ForTest.label i a) P R

lemma exec_iteAtom (w : List A) : ∀ (t : ForTest A) (P R : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool), exec w (iteAtom t P R) pos bv
      = if ForTest.Holds w pos bv t then exec w P pos bv else exec w R pos bv := by
  intro t
  induction t with
  | boolVar i => intro P R pos bv; rfl
  | eqPos i j => intro P R pos bv; rfl
  | lePos i j => intro P R pos bv; rfl
  | label i a => intro P R pos bv; rfl
  | not t ih =>
      intro P R pos bv
      rw [iteAtom, ih]
      simp only [ForTest.Holds]
      by_cases h : ForTest.Holds w pos bv t
      · rw [if_pos h, if_neg (not_not_intro h)]
      · rw [if_neg h, if_pos h]
  | and t s iht ihs =>
      intro P R pos bv
      rw [iteAtom, iht, ihs]
      simp only [ForTest.Holds]
      by_cases h : ForTest.Holds w pos bv t
      · rw [if_pos h]
        by_cases h' : ForTest.Holds w pos bv s
        · rw [if_pos h', if_pos ⟨h, h'⟩]
        · rw [if_neg h', if_neg (fun hc => h' hc.2)]
      · rw [if_neg h, if_neg (fun hc => h hc.1)]
  | or t s iht ihs =>
      intro P R pos bv
      rw [iteAtom, iht, ihs]
      simp only [ForTest.Holds]
      by_cases h : ForTest.Holds w pos bv t
      · rw [if_pos h, if_pos (Or.inl h)]
      · rw [if_neg h]
        by_cases h' : ForTest.Holds w pos bv s
        · rw [if_pos h', if_pos (Or.inr h')]
        · rw [if_neg h', if_neg (fun hc => hc.elim h h')]

lemma allAtomic_iteAtom : ∀ (t : ForTest A) (P R : ForProg A B), P.AllAtomic → R.AllAtomic →
    (iteAtom t P R).AllAtomic := by
  intro t
  induction t with
  | boolVar i => exact fun P R hP hR => ⟨trivial, hP, hR⟩
  | eqPos i j => exact fun P R hP hR => ⟨trivial, hP, hR⟩
  | lePos i j => exact fun P R hP hR => ⟨trivial, hP, hR⟩
  | label i a => exact fun P R hP hR => ⟨trivial, hP, hR⟩
  | not t ih => exact fun P R hP hR => ih R P hR hP
  | and t s iht ihs => exact fun P R hP hR => iht _ R (ihs P R hP hR) hR
  | or t s iht ihs => exact fun P R hP hR => iht P _ hP (ihs P R hP hR)

/-- **Atomising a program.**  Every conditional is expanded so that it tests an atomic test. -/
def atomize : ForProg A B → ForProg A B
  | skip => skip
  | output c => output c
  | assign i v => assign i v
  | seq P Q => seq (atomize P) (atomize Q)
  | ite t P Q => iteAtom t (atomize P) (atomize Q)
  | loop d x P => loop d x (atomize P)

lemma allAtomic_atomize : ∀ P : ForProg A B, (atomize P).AllAtomic := by
  intro P
  induction P with
  | skip => trivial
  | output c => trivial
  | assign i v => trivial
  | seq P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | ite t P Q ihP ihQ => exact allAtomic_iteAtom t _ _ ihP ihQ
  | loop d x P ih => exact ih

lemma exec_atomize (w : List A) : ∀ (P : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool),
    exec w (atomize P) pos bv = exec w P pos bv := by
  intro P
  induction P with
  | skip => intro pos bv; rfl
  | output c => intro pos bv; rfl
  | assign i v => intro pos bv; rfl
  | seq P Q ihP ihQ =>
      intro pos bv
      show exec w (seq (atomize P) (atomize Q)) pos bv = _
      rw [exec_seq, exec_seq, ihP, ihQ]
  | ite t P Q ihP ihQ =>
      intro pos bv
      show exec w (iteAtom t (atomize P) (atomize Q)) pos bv = _
      rw [exec_iteAtom, ihP, ihQ]
      by_cases h : ForTest.Holds w pos bv t
      · rw [if_pos h, exec_ite_pos _ _ _ _ _ _ h]
      · rw [if_neg h, exec_ite_neg _ _ _ _ _ _ h]
  | loop d x P ih =>
      intro pos bv
      show exec w (loop d x (atomize P)) pos bv = _
      simp only [exec]
      refine congrArg (fun f => forLoopRun f _ bv) ?_
      funext bv' q
      exact ih _ _

/-! ## Constant programs -/

end ForProg

/-- The program that outputs a fixed string. -/
def constProg : List C → ForProg A C
  | [] => ForProg.skip
  | c :: l => ForProg.seq (ForProg.output c) (constProg l)

lemma exec_constProg (w : List A) : ∀ (l : List C) (pos : ℕ → ℕ) (bv : ℕ → Bool),
    ForProg.exec w (constProg l) pos bv = (bv, l) := by
  intro l
  induction l with
  | nil => intro pos bv; rfl
  | cons c l ih =>
      intro pos bv
      show ForProg.exec w (ForProg.seq (ForProg.output c) (constProg l)) pos bv = _
      rw [exec_seq, ih]
      rfl

/-! ## The letters that a program mentions -/

lemma ForTest.holds_congr_letters (w w' : List A) (t : ForTest A)
    (h : ∀ a ∈ t.letters, ∀ i : ℕ, (w[i]? = some a ↔ w'[i]? = some a)) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) : Holds w pos bv t ↔ Holds w' pos bv t := by
  induction t with
  | boolVar i => rfl
  | eqPos i j => rfl
  | lePos i j => rfl
  | label i a => exact h a (by simp [letters]) (pos i)
  | not t ih => exact not_congr (ih h)
  | and t s iht ihs =>
      exact and_congr (iht (fun a ha => h a (by simp [letters, ha])))
        (ihs (fun a ha => h a (by simp [letters, ha])))
  | or t s iht ihs =>
      exact or_congr (iht (fun a ha => h a (by simp [letters, ha])))
        (ihs (fun a ha => h a (by simp [letters, ha])))

/-- **A program only sees the letters it mentions.**  Two inputs of the same length on which the
letters of the program sit at the same positions give the same run. -/
lemma ForProg.exec_congr_letters (w w' : List A) (hlen : w.length = w'.length) :
    ∀ (P : ForProg A B), (∀ a ∈ P.letters, ∀ i : ℕ, (w[i]? = some a ↔ w'[i]? = some a)) →
      ∀ (pos : ℕ → ℕ) (bv : ℕ → Bool), exec w P pos bv = exec w' P pos bv := by
  intro P
  induction P with
  | skip => intro _ pos bv; rfl
  | output c => intro _ pos bv; rfl
  | assign i v => intro _ pos bv; rfl
  | seq P Q ihP ihQ =>
      intro h pos bv
      rw [exec_seq, exec_seq, ihP (fun a ha => h a (by simp [letters, ha])),
        ihQ (fun a ha => h a (by simp [letters, ha]))]
  | ite t P Q ihP ihQ =>
      intro h pos bv
      have ht := ForTest.holds_congr_letters w w' t
        (fun a ha => h a (by simp [letters, ha])) pos bv
      by_cases hT : ForTest.Holds w pos bv t
      · rw [exec_ite_pos _ _ _ _ _ _ hT, exec_ite_pos _ _ _ _ _ _ (ht.mp hT),
          ihP (fun a ha => h a (by simp [letters, ha]))]
      · rw [exec_ite_neg _ _ _ _ _ _ hT, exec_ite_neg _ _ _ _ _ _ (fun hc => hT (ht.mpr hc)),
          ihQ (fun a ha => h a (by simp [letters, ha]))]
  | loop d x P ih =>
      intro h pos bv
      simp only [exec, hlen]
      refine congrArg (fun f => forLoopRun f _ bv) ?_
      funext bv' q
      exact ih (fun a ha => h a (by simp [letters, ha])) _ _

end Lax194892Proofs.Transducers
