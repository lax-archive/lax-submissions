/-
**Guess and check** (Nivat's theorem): a regular language of annotated strings,
read through two homomorphisms, is a rational relation.

This is the shape in which a string-to-string function is defined when one says
"*a nondeterministic automaton with output can guess the annotation and then
check that it satisfies the conditions*", as the book does in the first stage of
the proof of the snake lemma (`RequestProject/PartC/SnakeStage1.lean`).  Let `Γ`
be a finite alphabet of annotated letters, let `f : Γ → A*` and `g : Γ → B*` be
two maps -- typically `f` erases the annotation and `g` turns it into the string
that is to be produced -- and let `L ⊆ Γ*` be a *regular* language of correct
annotations.  Then

  `R w v  ⟺  ∃ u ∈ L, homOf f u = w ∧ homOf g u = v`

is a rational relation (`Transducers.isRationalRel_of_regular_nivat`): the nfa
with output runs a deterministic automaton for `L` on the annotation `u` that it
guesses, reading `f γ` and writing `g γ` at each letter `γ` of `u`.  This is one
half of Nivat's theorem; the other half is not needed here.

Together with `Transducers.exists_rationalFun_of_total_rel` (Lemma `lem:uniformisation`,
`RequestProject/PartB/UniformFun.lean`) this turns a regular language of correct
annotations that has at least one member over every input into a *rational
function* producing a correct output, with no functionality of the guessing to
be proved.
-/
import Lax132576Proofs.Source.PartB.LabAut
import Mathlib.Computability.DFA
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

open LabAut NFAO

variable {A B Γ σ : Type}

/-- The nfa with output that guesses an annotated string `u`, reads `homOf f u`,
writes `homOf g u`, and runs the deterministic automaton `D` on `u`. -/
def guessAut [Finite Γ] [Finite σ] (f : Γ → List A) (g : Γ → List B) (D : DFA Γ σ) :
    NFAO A B σ where
  init := {D.start}
  final := D.accept
  δ := Set.range (fun p : σ × Γ => (p.1, f p.2, g p.2, D.step p.1 p.2))
  δ_finite := Set.finite_range _

@[simp] lemma guessAut_init [Finite Γ] [Finite σ] (f : Γ → List A) (g : Γ → List B)
    (D : DFA Γ σ) : (guessAut f g D).init = {D.start} := rfl

@[simp] lemma guessAut_final [Finite Γ] [Finite σ] (f : Γ → List A) (g : Γ → List B)
    (D : DFA Γ σ) : (guessAut f g D).final = D.accept := rfl

lemma guessAut_mem_δ [Finite Γ] [Finite σ] (f : Γ → List A) (g : Γ → List B) (D : DFA Γ σ)
    (q : σ) (c : Γ) : (q, f c, g c, D.step q c) ∈ (guessAut f g D).δ := ⟨(q, c), rfl⟩

/-- The paths of `guessAut f g D` are exactly the runs of `D`. -/
lemma guessAut_relFrom_iff [Finite Γ] [Finite σ] (f : Γ → List A) (g : Γ → List B)
    (D : DFA Γ σ) (q p : σ) (w : List A) (v : List B) :
    (guessAut f g D).relFrom q w v p ↔
      ∃ u : List Γ, D.evalFrom q u = p ∧ homOf f u = w ∧ homOf g u = v := by
  constructor
  · refine NFAO.relFrom_induction (M := guessAut f g D)
      (motive := fun q w v => ∃ u : List Γ, D.evalFrom q u = p ∧ homOf f u = w ∧ homOf g u = v)
      ⟨[], rfl, rfl, rfl⟩ ?_
    rintro q q' u x w v ⟨⟨s, c⟩, hs⟩ - ⟨z, hev, hf, hg⟩
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    refine ⟨c :: z, ?_, ?_, ?_⟩
    · rw [DFA.evalFrom_cons, hev]
    · rw [homOf, List.map_cons, List.flatten_cons, ← homOf, hf]
    · rw [homOf, List.map_cons, List.flatten_cons, ← homOf, hg]
  · rintro ⟨u, rfl, rfl, rfl⟩
    induction u generalizing q with
    | nil => simpa [homOf] using (guessAut f g D).relFrom_nil q
    | cons c u ih =>
        have := NFAO.relFrom_step (guessAut_mem_δ f g D q c) (ih (D.step q c))
        simpa [homOf, DFA.evalFrom_cons] using this

/-- **Guess and check** (one half of Nivat's theorem).  If `L` is a regular
language of annotated strings, then the relation obtained by reading an
annotation through the homomorphism `homOf f` and writing it through the
homomorphism `homOf g` is rational. -/
theorem isRationalRel_of_regular_nivat [Finite Γ] (f : Γ → List A) (g : Γ → List B)
    {L : Language Γ} (hL : L.IsRegular) :
    IsRationalRel (fun (w : List A) (v : List B) =>
      ∃ u ∈ L, homOf f u = w ∧ homOf g u = v) := by
  classical
  obtain ⟨σ, hσ, D, hD⟩ := hL
  haveI : Fintype σ := hσ
  refine ⟨σ, inferInstance, guessAut f g D, fun w v => ?_⟩
  rw [NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨u, hu, rfl, rfl⟩
    refine ⟨D.start, rfl, D.evalFrom D.start u, ?_, ?_⟩
    · have : u ∈ D.accepts := by rw [hD]; exact hu
      exact (D.mem_accepts).1 this
    · exact (guessAut_relFrom_iff f g D _ _ _ _).2 ⟨u, rfl, rfl, rfl⟩
  · rintro ⟨q, hq, p, hp, hrel⟩
    obtain ⟨u, hev, hf, hg⟩ := (guessAut_relFrom_iff f g D q p _ _).1 hrel
    have hq' : q = D.start := hq
    subst hq'
    refine ⟨u, ?_, hf, hg⟩
    rw [← hD]
    refine (D.mem_accepts).2 ?_
    rw [DFA.eval, hev]
    exact hp

/-- The special case in which the annotation itself is the output. -/
theorem isRationalRel_of_regular_proj [Finite Γ] (f : Γ → List A)
    {L : Language Γ} (hL : L.IsRegular) :
    IsRationalRel (fun (w : List A) (v : List Γ) => v ∈ L ∧ homOf f v = w) := by
  have h := isRationalRel_of_regular_nivat f (fun c : Γ => [c]) hL
  refine (?_ : (fun w (v : List Γ) => v ∈ L ∧ homOf f v = w) =
      fun w v => ∃ u ∈ L, homOf f u = w ∧ homOf (fun c : Γ => [c]) u = v) ▸ h
  funext w v
  have hid : ∀ u : List Γ, homOf (fun c : Γ => [c]) u = u := by
    intro u; induction u with
    | nil => rfl
    | cons c u ih => rw [homOf, List.map_cons, List.flatten_cons, ← homOf, ih, List.singleton_append]
  simp only [eq_iff_iff]
  constructor
  · rintro ⟨hv, rfl⟩
    exact ⟨v, hv, rfl, hid v⟩
  · rintro ⟨u, hu, rfl, hgu⟩
    rw [hid u] at hgu
    subst hgu
    exact ⟨hu, rfl⟩

end Lax132576Proofs.Transducers
