/-
# The acceptance problem `A_TM` (Sipser, Section 4.2)

This file formalizes Section 4.2 of Sipser, *Introduction to the Theory of Computation*
(3rd ed.): the undecidability of

  `A_TM = {⟨M, w⟩ | M is a Turing machine and M accepts w}`  (Theorem 4.11),

together with the surrounding results of that section: the existence of languages that
are not Turing-recognizable (Corollary 4.18), the characterization of decidable languages
as those that are both Turing-recognizable and co-Turing-recognizable (Theorem 4.22), and
the fact that the complement of `A_TM` is not Turing-recognizable (Corollary 4.23).

## The machine model

Sipser's theorem is about an arbitrary universal model of computation.  We take as our
machines the *partial recursive programs* of Mathlib, `Nat.Partrec.Code`; this model comes
with the two ingredients that Sipser's proof needs and that no formalization can do
without:

* a universal machine (`Nat.Partrec.Code.eval_part`: the evaluation function
  `(M, w) ↦ M(w)` is itself computable), and
* the possibility of *programming*: every partial recursive function is the behaviour of
  some machine (`Nat.Partrec.Code.exists_code`), which is what makes Sipser's step
  "now we construct a new Turing machine `D` with `H` as a subroutine" rigorous.

A machine on an input either accepts (halts with output `1`), rejects (halts with output
`0`), or loops (does not halt); this is exactly Sipser's trichotomy, and it is what makes
the difference between recognizing and deciding a language meaningful.  Languages are
sets of natural numbers, natural numbers playing the role of strings.
-/
import Mathlib

namespace Lax251941Proofs.Acceptance

/-- A machine of our model: a partial recursive program. -/
abbrev Machine := Nat.Partrec.Code

/-- `M` *accepts* `w` if it halts on `w` with output `1`. -/
def Accepts (M : Machine) (w : ℕ) : Prop := M.eval w = Part.some 1

/-- `M` *rejects* `w` if it halts on `w` with output `0`. -/
def Rejects (M : Machine) (w : ℕ) : Prop := M.eval w = Part.some 0

/-- A *decider* is a machine that halts on every input, accepting or rejecting it. -/
def IsDecider (M : Machine) : Prop := ∀ w, Accepts M w ∨ Rejects M w

/-- The description `⟨M⟩` of a machine, as a string (i.e. a natural number). -/
def enc (M : Machine) : ℕ := Encodable.encode M

/-- A machine *recognizes* a language if it accepts exactly the strings in it. -/
def Recognizes (M : Machine) (A : Set ℕ) : Prop := ∀ w, w ∈ A ↔ Accepts M w

/-- A machine *decides* a language if it recognizes it and halts on every input. -/
def Decides (M : Machine) (A : Set ℕ) : Prop := IsDecider M ∧ Recognizes M A

/-- A language is *Turing-recognizable* if some machine recognizes it. -/
def TuringRecognizable (A : Set ℕ) : Prop := ∃ M, Recognizes M A

/-- A language is *decidable* if some machine decides it. -/
def TuringDecidable (A : Set ℕ) : Prop := ∃ M, Decides M A

/-- `A_TM = {⟨M, w⟩ | M is a machine and M accepts w}`, the pair `⟨M, w⟩` being encoded
by Cantor pairing. -/
def ATM : Set ℕ := {n | Accepts (Denumerable.ofNat Machine n.unpair.1) n.unpair.2}

@[simp] lemma ofNat_enc (M : Machine) : Denumerable.ofNat Machine (enc M) = M :=
  Denumerable.ofNat_encode M

@[simp] lemma pair_mem_ATM (M : Machine) (w : ℕ) :
    Nat.pair (enc M) w ∈ ATM ↔ Accepts M w := by
  simp [ATM]

lemma not_accepts_and_rejects {M : Machine} {w : ℕ} (ha : Accepts M w) (hr : Rejects M w) :
    False := by
  rw [Accepts] at ha; rw [Rejects] at hr
  rw [ha] at hr
  exact absurd (Part.some_injective hr) (by decide)

/-! ## The diagonalization method

The heart of Sipser's proof of Theorem 4.11 is the following triviality: no machine can
accept the description of a machine exactly when that machine does *not* accept its own
description, since it would then have to do the opposite of itself.  We state it for an
arbitrary notion of machine, input, acceptance and encoding, since nothing else is used.
-/

/-- **The diagonalization argument.**  There is no machine `D` accepting the description
`⟨N⟩` of a machine `N` exactly when `N` does not accept `⟨N⟩`: running `D` on its own
description gives a contradiction. -/
theorem no_diagonal_machine {Mach Str : Type*} (Acc : Mach → Str → Prop) (code : Mach → Str)
    (D : Mach) (hD : ∀ N : Mach, Acc D (code N) ↔ ¬ Acc N (code N)) : False := by
  have h := hD D
  tauto

/-! ## Theorem 4.11: `A_TM` is undecidable -/

/-- Sipser's machine `D`: given a decider `H` for `A_TM`, there is a machine that accepts
the description `⟨N⟩` of a machine `N` precisely when `N` does not accept `⟨N⟩`.  It runs
`H` on `⟨N, ⟨N⟩⟩` and outputs the opposite. -/
theorem exists_flip_machine {H : Machine} (hH : Decides H ATM) :
    ∃ D : Machine, ∀ N : Machine, Accepts D (enc N) ↔ ¬ Accepts N (enc N) := by
  obtain ⟨hdec, hrec⟩ := hH
  -- the behaviour of `D`: run `H` on `⟨N, ⟨N⟩⟩` and output the opposite
  have hpartrec : Partrec fun m : ℕ => Part.map (fun v => 1 - v) (H.eval (Nat.pair m m)) :=
    (Nat.Partrec.Code.eval_part.comp (Computable.const H)
      (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp).map
      (Primrec.nat_sub.comp (Primrec.const 1) Primrec.snd).to₂.to_comp
  obtain ⟨D, hD⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hpartrec)
  refine ⟨D, fun N => ?_⟩
  set m := enc N with hm
  have hDm : D.eval m = Part.map (fun v => 1 - v) (H.eval (Nat.pair m m)) := by
    rw [hD]
  have hmem : Nat.pair m m ∈ ATM ↔ Accepts N m := by rw [hm, pair_mem_ATM]
  constructor
  · intro hacc hN
    have hH1 : H.eval (Nat.pair m m) = Part.some 1 := (hrec _).1 (hmem.2 hN)
    rw [Accepts, hDm, hH1] at hacc
    simp at hacc
  · intro hN
    have hH0 : H.eval (Nat.pair m m) = Part.some 0 := by
      rcases hdec (Nat.pair m m) with h | h
      · exact absurd (hmem.1 ((hrec _).2 h)) hN
      · exact h
    rw [Accepts, hDm, hH0]
    simp

/-- **Theorem 4.11.**  The acceptance problem `A_TM` is undecidable. -/
theorem atm_not_turingDecidable : ¬ TuringDecidable ATM := by
  rintro ⟨H, hH⟩
  obtain ⟨D, hD⟩ := exists_flip_machine hH
  exact no_diagonal_machine Accepts enc D hD

/-! ## `A_TM` is Turing-recognizable: the universal machine -/

/-- **The universal machine.**  `A_TM` is Turing-recognizable: a machine can simulate the
machine given to it in its input (Sipser's machine `U`, page 202). -/
theorem turingRecognizable_ATM : TuringRecognizable ATM := by
  have hpartrec : Partrec fun n : ℕ =>
      Nat.Partrec.Code.eval (Denumerable.ofNat Machine n.unpair.1) n.unpair.2 :=
    Nat.Partrec.Code.eval_part.comp
      ((Computable.ofNat _).comp (Primrec.fst.comp Primrec.unpair).to_comp)
      (Primrec.snd.comp Primrec.unpair).to_comp
  obtain ⟨U, hU⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hpartrec)
  exact ⟨U, fun w => by simp [ATM, Accepts, hU]⟩

/-! ## Comparison with the computability predicates of Mathlib -/

private lemma primrec_decide_snd_eq_one : Primrec fun p : ℕ × ℕ => decide (p.2 = 1) := by
  obtain ⟨_, h⟩ :=
    (Primrec.eq.comp Primrec.snd (Primrec.const 1) : PrimrecPred fun p : ℕ × ℕ => p.2 = 1)
  exact h.of_eq fun p => by simp

/-- A language is Turing-recognizable exactly when it is recursively enumerable. -/
theorem turingRecognizable_iff_rePred (A : Set ℕ) :
    TuringRecognizable A ↔ REPred (· ∈ A) := by
  classical
  constructor
  · rintro ⟨M, hM⟩
    have hp : Partrec fun w : ℕ => (M.eval w).bind
        (fun v => bif (decide (v = 1)) then Part.some () else Part.none) :=
      (Nat.Partrec.Code.eval_part.comp (Computable.const M) Computable.id).bind
        (Partrec.cond primrec_decide_snd_eq_one.to_comp (Partrec.const' (Part.some ()))
          (Partrec.const' Part.none))
    have heq : (fun w : ℕ => w ∈ A) = fun w : ℕ => ((M.eval w).bind
        (fun v => bif (decide (v = 1)) then Part.some () else Part.none)).Dom := by
      funext w
      refine propext ?_
      constructor
      · intro hw
        have h1 : M.eval w = Part.some 1 := (hM w).1 hw
        simp [h1]
      · intro hdom
        simp only [Part.bind_dom] at hdom
        obtain ⟨hd, hv⟩ := hdom
        refine (hM w).2 ?_
        by_cases hone : (M.eval w).get hd = 1
        · rw [Accepts, Part.eq_some_iff]
          exact hone ▸ Part.get_mem hd
        · simp [hone] at hv
    rw [show REPred (· ∈ A) = REPred _ from congrArg _ heq]
    exact hp.dom_re
  · intro h
    have hp : Partrec fun w : ℕ =>
        Part.map (fun _ => 1) (Part.assert (w ∈ A) fun _ => Part.some ()) :=
      h.map (Computable.const 1).to₂
    obtain ⟨M, hM⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hp)
    refine ⟨M, fun w => ?_⟩
    rw [Accepts, hM]
    by_cases hw : w ∈ A <;> simp [hw, Part.assert_pos, Part.assert_neg]

/-- A language is decidable exactly when its membership predicate is computable. -/
theorem turingDecidable_iff_computablePred (A : Set ℕ) :
    TuringDecidable A ↔ ComputablePred (· ∈ A) := by
  classical
  constructor
  · rintro ⟨M, hdec, hrec⟩
    refine ⟨Classical.decPred _, ?_⟩
    have hp : Partrec fun w : ℕ => Part.map (fun v => decide (v = 1)) (M.eval w) :=
      (Nat.Partrec.Code.eval_part.comp (Computable.const M) Computable.id).map
        primrec_decide_snd_eq_one.to₂.to_comp
    refine hp.of_eq fun w => ?_
    rcases hdec w with h | h
    · have hA : w ∈ A := (hrec w).2 h
      rw [Accepts] at h
      simp [h, hA]
    · have hA : w ∉ A := fun hw => not_accepts_and_rejects ((hrec w).1 hw) h
      rw [Rejects] at h
      simp [h, hA]
  · rintro ⟨inst, hcomp⟩
    have hc : Computable fun w : ℕ => bif (decide (w ∈ A)) then 1 else 0 :=
      Computable.cond hcomp (Computable.const 1) (Computable.const 0)
    obtain ⟨M, hM⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hc)
    have hval : ∀ w, M.eval w = Part.some (bif (decide (w ∈ A)) then 1 else 0) := by
      intro w; rw [hM]; rfl
    refine ⟨M, fun w => ?_, fun w => ?_⟩
    · by_cases hw : w ∈ A
      · exact Or.inl (by rw [Accepts, hval w]; simp [hw])
      · exact Or.inr (by rw [Rejects, hval w]; simp [hw])
    · rw [Accepts, hval w]
      by_cases hw : w ∈ A <;> simp [hw]

/-! ## Corollary 4.18, Theorem 4.22 and Corollary 4.23 -/

/-- **Corollary 4.18.**  Some languages are not Turing-recognizable: there are only
countably many machines but uncountably many languages. -/
theorem exists_not_turingRecognizable : ∃ A : Set ℕ, ¬ TuringRecognizable A := by
  by_contra hcon
  push_neg at hcon
  refine Function.cantor_surjective
    (fun n : ℕ => {w | Accepts (Denumerable.ofNat Machine n) w}) fun A => ?_
  obtain ⟨M, hM⟩ := hcon A
  exact ⟨enc M, by ext w; simpa using (hM w).symm⟩

/-- **Theorem 4.22.**  A language is decidable if and only if both it and its complement
are Turing-recognizable. -/
theorem turingDecidable_iff (A : Set ℕ) :
    TuringDecidable A ↔ TuringRecognizable A ∧ TuringRecognizable Aᶜ := by
  classical
  rw [turingDecidable_iff_computablePred, ComputablePred.computable_iff_re_compl_re,
    turingRecognizable_iff_rePred, turingRecognizable_iff_rePred]
  rfl

/-! ## Sanity checks

The notions above are not vacuous: there really are deciders, and machines really do
accept things, so that `TuringDecidable` is a nontrivial property. -/

/-- The language `{0}` is decidable. -/
theorem turingDecidable_singleton_zero : TuringDecidable {n : ℕ | n = 0} := by
  rw [turingDecidable_iff_computablePred]
  refine ⟨inferInstance, ?_⟩
  obtain ⟨_, h⟩ := (Primrec.eq.comp Primrec.id (Primrec.const 0) : PrimrecPred fun n : ℕ => n = 0)
  exact (h.of_eq fun n => by simp).to_comp

/-- Some machine accepts some input. -/
theorem exists_accepting_machine : ∃ (M : Machine) (w : ℕ), Accepts M w := by
  obtain ⟨M, -, hrec⟩ := turingDecidable_singleton_zero
  exact ⟨M, 0, (hrec 0).1 rfl⟩

/-- **Corollary 4.23.**  The complement of `A_TM` is not Turing-recognizable. -/
theorem not_turingRecognizable_compl_ATM : ¬ TuringRecognizable ATMᶜ := by
  intro h
  exact atm_not_turingDecidable ((turingDecidable_iff ATM).2 ⟨turingRecognizable_ATM, h⟩)

end Lax251941Proofs.Acceptance
