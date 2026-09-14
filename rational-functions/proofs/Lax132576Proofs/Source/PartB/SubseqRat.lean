/-
A subsequential transducer is a special case of an nfa with output: the graph of
a subsequential function is a rational relation.

The nfa with output has the states of the transducer together with one extra
final state; the transitions of the transducer are kept, and from every state
whose end-of-input output is defined there is an additional transition to the
extra state which reads nothing and writes that output.
-/
import Lax132576Proofs.Source.PartB.SubseqDef
import Lax132576Proofs.Source.PartB.LabAut
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace SubseqRat

variable {A B Q : Type}

/-- The nfa with output associated with a subsequential transducer. -/
noncomputable def aut (T : Subsequential A B Q) [Finite A] [Finite Q] :
    NFAO A B (Option Q) where
  init := {some T.toSequential.init}
  final := {none}
  δ := {t | (∃ (q : Q) (a : A), t = (some q, [a], (T.toSequential.step q a).2,
        some (T.toSequential.transFun q a))) ∨
      (∃ (q : Q) (u : List B), T.endOfInput q = some u ∧ t = (some q, [], u, none))}
  δ_finite := by
    classical
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Fintype Q := Fintype.ofFinite Q
    have h1 : {t : Option Q × List A × List B × Option Q |
        ∃ (q : Q) (a : A), t = (some q, [a], (T.toSequential.step q a).2,
          some (T.toSequential.transFun q a))}.Finite := by
      have : {t : Option Q × List A × List B × Option Q |
          ∃ (q : Q) (a : A), t = (some q, [a], (T.toSequential.step q a).2,
            some (T.toSequential.transFun q a))}
          = Set.range (fun p : Q × A => (some p.1, [p.2], (T.toSequential.step p.1 p.2).2,
              some (T.toSequential.transFun p.1 p.2))) := by
        ext t
        constructor
        · rintro ⟨q, a, rfl⟩; exact ⟨(q, a), rfl⟩
        · rintro ⟨⟨q, a⟩, rfl⟩; exact ⟨q, a, rfl⟩
      rw [this]
      exact Set.finite_range _
    have h2 : {t : Option Q × List A × List B × Option Q |
        ∃ (q : Q) (u : List B), T.endOfInput q = some u ∧ t = (some q, [], u, none)}.Finite := by
      refine Set.Finite.subset (Set.finite_range
        (fun q : Q => ((some q, [], (T.endOfInput q).getD [], none) :
          Option Q × List A × List B × Option Q))) ?_
      rintro t ⟨q, u, hu, rfl⟩
      exact ⟨q, by simp [hu]⟩
    exact h1.union h2

variable (T : Subsequential A B Q) [Finite A] [Finite Q]

lemma letter_mem (q : Q) (a : A) :
    (some q, [a], (T.toSequential.step q a).2, some (T.toSequential.transFun q a))
      ∈ (aut T).δ := Or.inl ⟨q, a, rfl⟩

lemma end_mem {q : Q} {u : List B} (hu : T.endOfInput q = some u) :
    (some q, ([] : List A), u, (none : Option Q)) ∈ (aut T).δ := Or.inr ⟨q, u, hu, rfl⟩

/-- Running the transducer gives a path in the automaton. -/
lemma relFrom_run (q : Q) (w : List A) :
    (aut T).relFrom (some q) w (T.toSequential.run q w)
      (some (strTrans T.toSequential.transFun w q)) := by
  induction w generalizing q with
  | nil => simpa [strTrans] using (aut T).relFrom_nil (some q)
  | cons a w ih =>
    have h := NFAO.relFrom_step (letter_mem T q a) (ih (T.toSequential.transFun q a))
    have hst : strTrans T.toSequential.transFun w (T.toSequential.transFun q a)
        = strTrans T.toSequential.transFun (a :: w) q := by simp [strTrans]
    rw [hst] at h
    simpa [Sequential.run, Sequential.transFun] using h

/-- There are no transitions out of the extra final state. -/
lemma relFrom_none {w : List A} {v : List B} (h : (aut T).relFrom none w v none) :
    w = [] ∧ v = [] := by
  obtain ⟨ts, hts, hin, hout⟩ := h
  cases hts with
  | nil q => exact ⟨by simpa using hin.symm, by simpa using hout.symm⟩
  | cons ht _ =>
    rcases ht with ⟨q, a, hq⟩ | ⟨q, u, _, hq⟩ <;>
      · exfalso
        have := congrArg (fun t => t.1) hq
        simp at this

/-- The relation computed by the automaton, from a state of the transducer. -/
lemma relFrom_iff (q : Q) (w : List A) (v : List B) :
    (aut T).relFrom (some q) w v none ↔
      ∃ u, T.endOfInput (strTrans T.toSequential.transFun w q) = some u ∧
        v = T.toSequential.run q w ++ u := by
  constructor
  · intro h
    have key : ∀ {s : Option Q} {w : List A} {v : List B}, (aut T).relFrom s w v none →
        ((∀ q : Q, s = some q →
          ∃ u, T.endOfInput (strTrans T.toSequential.transFun w q) = some u ∧
            v = T.toSequential.run q w ++ u) ∧ (s = none → w = [] ∧ v = [])) := by
      intro s w v hrel
      refine NFAO.relFrom_induction (M := aut T)
        (motive := fun s w v =>
          ((∀ q : Q, s = some q →
            ∃ u, T.endOfInput (strTrans T.toSequential.transFun w q) = some u ∧
              v = T.toSequential.run q w ++ u) ∧ (s = none → w = [] ∧ v = [])))
        ?_ ?_ hrel
      · exact ⟨by simp, fun _ => ⟨rfl, rfl⟩⟩
      · intro s s' u x w' v' ht _ ih
        rcases ht with ⟨q₀, a, hq⟩ | ⟨q₀, y, hy, hq⟩
        · have hs : s = some q₀ := by
            have := congrArg (fun t => t.1) hq; simpa using this
          have hu : u = [a] := by have := congrArg (fun t => t.2.1) hq; simpa using this
          have hx : x = (T.toSequential.step q₀ a).2 := by
            have := congrArg (fun t => t.2.2.1) hq; simpa using this
          have hs' : s' = some (T.toSequential.transFun q₀ a) := by
            have := congrArg (fun t => t.2.2.2) hq; simpa using this
          refine ⟨?_, by simp [hs]⟩
          intro q hq'
          have hqq : q = q₀ := by rw [hs] at hq'; exact (Option.some_injective _ hq').symm
          subst hqq
          obtain ⟨z, hz, hvz⟩ := ih.1 (T.toSequential.transFun q a) (by rw [hs'])
          refine ⟨z, ?_, ?_⟩
          · rw [hu, show strTrans T.toSequential.transFun ([a] ++ w') q
                = strTrans T.toSequential.transFun w' (T.toSequential.transFun q a) by
              simp [strTrans]]
            exact hz
          · rw [hu, hx, hvz]
            simp [Sequential.run, Sequential.transFun, List.append_assoc]
        · have hs : s = some q₀ := by
            have := congrArg (fun t => t.1) hq; simpa using this
          have hu : u = [] := by have := congrArg (fun t => t.2.1) hq; simpa using this
          have hx : x = y := by have := congrArg (fun t => t.2.2.1) hq; simpa using this
          have hs' : s' = none := by
            have := congrArg (fun t => t.2.2.2) hq; simpa using this
          obtain ⟨hw', hv'⟩ := ih.2 hs'
          refine ⟨?_, by simp [hs]⟩
          intro q hq'
          have hqq : q = q₀ := by rw [hs] at hq'; exact (Option.some_injective _ hq').symm
          subst hqq
          refine ⟨y, ?_, ?_⟩
          · rw [hu, hw']
            simpa [strTrans] using hy
          · rw [hu, hw', hx, hv']
            simp
    exact (key h).1 q rfl
  · rintro ⟨u, hu, rfl⟩
    have h1 := relFrom_run T q w
    have h2 : (aut T).relFrom (some (strTrans T.toSequential.transFun w q)) [] u none :=
      NFAO.relFrom_single (end_mem T hu)
    simpa using NFAO.relFrom_trans h1 h2

lemma rel_iff (w : List A) (v : List B) : (aut T).rel w v ↔ T.eval w = some v := by
  rw [NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨q, hq, p, hp, hrel⟩
    have hq' : q = some T.toSequential.init := hq
    have hp' : p = none := hp
    subst hq'
    subst hp'
    obtain ⟨u, hu, rfl⟩ := (relFrom_iff T _ w v).1 hrel
    simp only [Subsequential.eval, Sequential.eval]
    rw [hu]
    rfl
  · intro hv
    refine ⟨some T.toSequential.init, rfl, none, rfl, ?_⟩
    rw [relFrom_iff]
    simp only [Subsequential.eval] at hv
    rcases hend : T.endOfInput (strTrans T.toSequential.transFun w T.toSequential.init) with _ | u
    · rw [hend] at hv; simp at hv
    · rw [hend] at hv
      simp only [Option.map_some, Option.some.injEq] at hv
      exact ⟨u, rfl, hv.symm⟩

end SubseqRat

/-- The graph of a subsequential function is a rational relation. -/
theorem isRationalRel_of_isSubsequential {A B : Type} [Finite A]
    {g : List A → Option (List B)} (hg : IsSubsequential g) :
    IsRationalRel (fun w v => g w = some v) := by
  obtain ⟨Q, hQ, T, rfl⟩ := hg
  haveI : Finite Q := hQ
  exact ⟨Option Q, inferInstance, SubseqRat.aut T, fun w v => (SubseqRat.rel_iff T w v).symm⟩

end Lax132576Proofs.Transducers
