/-
Subsequential transducers (Section *Subsequential functions* of *Transducers*, M. Bojańczyk) and the
easy implication of Theorem `thm:subsequential-functions`.

A subsequential transducer is a sequential transducer with a partial
end-of-input function, which is applied to the last state of the computation.
The definitions are stated here (rather than in `WeightedStatements.lean`) so
that the constructions used in the proof of Theorem `thm:subsequential-functions` can be developed
before the statements of the numbered results, as elsewhere in the project.

This file also contains the easy implication of Theorem `thm:subsequential-functions`: a
subsequential function is continuous and has bounded variation. -/
import Lax132576Proofs.Source.PartB.SeqChar
import Lax132576Proofs.Source.PartB.Lcp
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-- A subsequential transducer: a sequential transducer with a partial
end-of-input function, which is applied to the last state of the computation. -/
structure Subsequential (A B Q : Type) extends Sequential A B Q where
  /-- The partial end-of-input function. -/
  endOfInput : Q → Option (List B)

namespace Subsequential

variable {A B Q : Type}

/-- The semantics of a subsequential transducer: a partial function. -/
def eval (T : Subsequential A B Q) (w : List A) : Option (List B) :=
  (T.endOfInput (strTrans T.toSequential.transFun w T.toSequential.init)).map
    (fun u => T.toSequential.eval w ++ u)

end Subsequential

/-- A partial function computed by a subsequential transducer. -/
def IsSubsequential {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (T : Subsequential A B Q), T.eval = f

/-- The bounded variation property of Theorem `thm:subsequential-functions`: for all `w₁, w₂` the
left distances `‖f (w w₁), f (w w₂)‖` are bounded, where `w` ranges over the strings for which both
outputs are defined. -/
def BoundedVariation {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∀ w₁ w₂ : List A, ∃ K : ℕ, ∀ (w : List A) (v₁ v₂ : List B),
    f (w ++ w₁) = some v₁ → f (w ++ w₂) = some v₂ → leftDist v₁ v₂ ≤ K

namespace Subsequential

variable {A B Q : Type}

/-- The dfa obtained by feeding the output of a subsequential transducer to a
dfa over the output alphabet: it accepts the inputs whose (defined) output is
accepted by the dfa. -/
def dfaComp (T : Subsequential A B Q) {σ : Type} (D : DFA B σ) : DFA A (Q × σ) where
  step := fun qs a => ((T.toSequential.step qs.1 a).1,
    D.evalFrom qs.2 (T.toSequential.step qs.1 a).2)
  start := (T.toSequential.init, D.start)
  accept := {qs | ∃ u, T.endOfInput qs.1 = some u ∧ D.evalFrom qs.2 u ∈ D.accept}

lemma dfaComp_evalFrom (T : Subsequential A B Q) {σ : Type} (D : DFA B σ)
    (w : List A) (q : Q) (s : σ) :
    (T.dfaComp D).evalFrom (q, s) w =
      (strTrans T.toSequential.transFun w q, D.evalFrom s (T.toSequential.run q w)) := by
  induction w generalizing q s with
  | nil => simp [DFA.evalFrom, strTrans]
  | cons a w ih =>
      rw [DFA.evalFrom_cons, ih]
      simp only [dfaComp, Sequential.run, strTrans, Sequential.transFun, List.foldl_cons]
      congr 1
      rw [DFA.evalFrom_of_append]

lemma dfaComp_accepts (T : Subsequential A B Q) {σ : Type} (D : DFA B σ) :
    (T.dfaComp D).accepts = {w : List A | ∃ v, T.eval w = some v ∧ v ∈ D.accepts} := by
  ext w
  rw [DFA.mem_accepts]
  show (T.dfaComp D).evalFrom (T.dfaComp D).start w ∈ (T.dfaComp D).accept ↔ _
  rw [show (T.dfaComp D).start = (T.toSequential.init, D.start) from rfl, dfaComp_evalFrom]
  simp only [dfaComp, Set.mem_setOf_eq, eval, Sequential.eval, Option.map_eq_some_iff,
    DFA.mem_accepts, DFA.eval]
  constructor
  · rintro ⟨u, hu, hacc⟩
    exact ⟨_, ⟨u, hu, rfl⟩, by rw [DFA.evalFrom_of_append]; exact hacc⟩
  · rintro ⟨v, ⟨u, hu, rfl⟩, hacc⟩
    exact ⟨u, hu, by rw [← DFA.evalFrom_of_append]; exact hacc⟩

end Subsequential

/-! ## The easy implication of Theorem `thm:subsequential-functions` -/

lemma IsSubsequential.partialContinuous {A B : Type} [Finite A] [Finite B]
    {f : List A → Option (List B)} (hf : IsSubsequential f) : PartialContinuous f := by
  obtain ⟨Q, hQ, T, rfl⟩ := hf
  intro L hL
  obtain ⟨σ, hσ, D, rfl⟩ := hL
  haveI : Fintype Q := Fintype.ofFinite Q
  exact ⟨Q × σ, inferInstance, T.dfaComp D, T.dfaComp_accepts D⟩

lemma IsSubsequential.boundedVariation {A B : Type} [Finite A]
    {f : List A → Option (List B)} (hf : IsSubsequential f) : BoundedVariation f := by
  obtain ⟨Q, hQ, T, rfl⟩ := hf
  intro w₁ w₂
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  -- the outputs produced while reading `w₁` (resp. `w₂`) and the end-of-input outputs
  -- are bounded in length
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℕ, ∀ q : Q, (T.toSequential.run q w₁).length ≤ K₁ :=
    ⟨Finset.univ.sup (fun q : Q => (T.toSequential.run q w₁).length), fun q =>
      Finset.le_sup (f := fun q : Q => (T.toSequential.run q w₁).length) (Finset.mem_univ q)⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℕ, ∀ q : Q, (T.toSequential.run q w₂).length ≤ K₂ :=
    ⟨Finset.univ.sup (fun q : Q => (T.toSequential.run q w₂).length), fun q =>
      Finset.le_sup (f := fun q : Q => (T.toSequential.run q w₂).length) (Finset.mem_univ q)⟩
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℕ, ∀ q : Q, ∀ u, T.endOfInput q = some u → u.length ≤ K₃ :=
    ⟨Finset.univ.sup (fun q : Q => ((T.endOfInput q).getD []).length), by
      intro q u hu
      have : ((T.endOfInput q).getD []).length ≤
          Finset.univ.sup (fun q : Q => ((T.endOfInput q).getD []).length) :=
        Finset.le_sup (f := fun q : Q => ((T.endOfInput q).getD []).length) (Finset.mem_univ q)
      simpa [hu] using this⟩
  refine ⟨max (K₁ + K₃) (K₂ + K₃), fun w v₁ v₂ h₁ h₂ => ?_⟩
  simp only [Subsequential.eval, Option.map_eq_some_iff, Sequential.eval] at h₁ h₂
  obtain ⟨u₁, hu₁, rfl⟩ := h₁
  obtain ⟨u₂, hu₂, rfl⟩ := h₂
  refine leftDist_le (v := T.toSequential.run T.toSequential.init w)
    (v₁ := T.toSequential.run (strTrans T.toSequential.transFun w T.toSequential.init) w₁ ++ u₁)
    (v₂ := T.toSequential.run (strTrans T.toSequential.transFun w T.toSequential.init) w₂ ++ u₂)
    ?_ ?_ ?_ ?_
  · rw [Sequential.run_append]; simp [List.append_assoc]
  · rw [Sequential.run_append]; simp [List.append_assoc]
  · have := hK₁ (strTrans T.toSequential.transFun w T.toSequential.init)
    have := hK₃ _ _ hu₁
    simp only [List.length_append]
    omega
  · have := hK₂ (strTrans T.toSequential.transFun w T.toSequential.init)
    have := hK₃ _ _ hu₂
    simp only [List.length_append]
    omega

end Lax132576Proofs.Transducers
