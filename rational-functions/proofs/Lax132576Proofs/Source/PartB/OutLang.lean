/-
The set of outputs of a fixed input.

For an nfa with output `M` whose transitions read at most one letter and write
at most one letter, and for a fixed input string `w`, the set of strings that
`M` can write while reading `w` (from a state of `S` to a state of `T`) is a
regular language over the output alphabet.

The automaton witnessing this is an ε-automaton over the output alphabet whose
states are pairs (state of `M`, position in `w`): a transition of `M` that reads
nothing keeps the position, and a transition that reads the letter at the
current position advances it.
-/
import Lax132576Proofs.Source.PartB.Atomize
import Lax132576Proofs.Source.PartB.RatCont
import Lax132576Proofs.Source.PartB.LenNormalForm
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-- A segment of length one. -/
lemma seg_succ {A : Type} (w : List A) {i : ℕ} (h : i < w.length) : seg w i (i + 1) = [w[i]] := by
  rw [seg_eq, Nat.add_sub_cancel_left, List.drop_eq_getElem_cons h]
  rfl

namespace OutLang

variable {A B Q : Type} (M : NFAO A B Q) (S T : Set Q) (w : List A)

/-- The ε-automaton over the output alphabet recognising the outputs of `M` on
the input `w`. -/
def outNFA : εNFA B (Q × Fin (w.length + 1)) where
  step := fun s ob =>
    {s' | ((s.1, [], ob.toList, s'.1) ∈ M.δ ∧ s'.2 = s.2) ∨
      (∃ h : (s.2 : ℕ) < w.length,
        (s.1, [w[(s.2 : ℕ)]], ob.toList, s'.1) ∈ M.δ ∧ (s'.2 : ℕ) = (s.2 : ℕ) + 1)}
  start := {s | s.1 ∈ S ∧ (s.2 : ℕ) = 0}
  accept := {s | s.1 ∈ T ∧ (s.2 : ℕ) = w.length}

/-- Every run of `M` on a suffix of `w` gives a run of the ε-automaton. -/
lemma isPath_of_relFrom (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    {q q' : Q} {w' : List A} {x : List B} (h : M.relFrom q w' x q') :
    ∀ i : Fin (w.length + 1), w' = w.drop (i : ℕ) →
      ∃ y : List (Option B), y.reduceOption = x ∧
        (outNFA M S T w).IsPath (q, i) (q', ⟨w.length, by omega⟩) y := by
  refine NFAO.relFrom_induction (M := M)
    (motive := fun q w' x => ∀ i : Fin (w.length + 1), w' = w.drop (i : ℕ) →
      ∃ y : List (Option B), y.reduceOption = x ∧
        (outNFA M S T w).IsPath (q, i) (q', ⟨w.length, by omega⟩) y) ?_ ?_ h
  · intro i hi
    have hlen : w.length ≤ (i : ℕ) := List.drop_eq_nil_iff.1 hi.symm
    have hival : (i : ℕ) = w.length := by have := i.isLt; omega
    refine ⟨[], rfl, ?_⟩
    have heq : ((q', i) : Q × Fin (w.length + 1)) = (q', ⟨w.length, by omega⟩) := by
      simp [Prod.ext_iff, Fin.ext_iff, hival]
    rw [heq]
    exact εNFA.IsPath.nil _
  · intro q₀ q₁ u b w'' x'' ht _ ih i hi
    have hu : u.length ≤ 1 := (hatom _ ht).1
    have hb : b.length ≤ 1 := (hatom _ ht).2
    obtain ⟨ob, hob⟩ : ∃ ob : Option B, ob.toList = b := by
      match b, hb with
      | [], _ => exact ⟨none, rfl⟩
      | [c], _ => exact ⟨some c, rfl⟩
    match u, hu with
    | [], _ =>
        have hw'' : w'' = w.drop (i : ℕ) := by simpa using hi
        obtain ⟨y, hy, hpath⟩ := ih i hw''
        refine ⟨ob :: y, ?_, ?_⟩
        · cases ob <;> simp [← hob, hy]
        · refine εNFA.IsPath.cons (q₁, i) _ _ ob y ?_ hpath
          exact Or.inl ⟨by rw [hob]; exact ht, rfl⟩
    | [a], _ =>
        have hne : ¬ (w.length ≤ (i : ℕ)) := by
          intro hle
          rw [List.drop_eq_nil_iff.2 hle] at hi
          simp at hi
        have hlt : (i : ℕ) < w.length := by omega
        rw [List.drop_eq_getElem_cons hlt] at hi
        simp only [List.cons_append, List.cons.injEq] at hi
        obtain ⟨ha, hw''⟩ := hi
        have hi' : (i : ℕ) + 1 < w.length + 1 := by omega
        obtain ⟨y, hy, hpath⟩ := ih ⟨(i : ℕ) + 1, hi'⟩ (by simpa using hw'')
        refine ⟨ob :: y, ?_, ?_⟩
        · cases ob <;> simp [← hob, hy]
        · refine εNFA.IsPath.cons (q₁, ⟨(i : ℕ) + 1, hi'⟩) _ _ ob y ?_ hpath
          exact Or.inr ⟨hlt, by rw [hob, ← ha]; exact ht, rfl⟩

/-- Every run of the ε-automaton gives a run of `M`. -/
lemma relFrom_of_isPath : ∀ (y : List (Option B)) (s s' : Q × Fin (w.length + 1)),
    (outNFA M S T w).IsPath s s' y →
      M.relFrom s.1 (seg w (s.2 : ℕ) (s'.2 : ℕ)) y.reduceOption s'.1 ∧ (s.2 : ℕ) ≤ (s'.2 : ℕ) := by
  intro y
  induction y with
  | nil =>
      intro s s' hp
      cases hp
      exact ⟨by simpa using M.relFrom_nil s.1, le_rfl⟩
  | cons ob y ih =>
      intro s s' hp
      cases hp with
      | cons t _ _ _ _ hstep hrest =>
          obtain ⟨hrel, hle⟩ := ih t s' hrest
          have hred : (ob :: y).reduceOption = ob.toList ++ y.reduceOption := by
            cases ob <;> simp
          rcases hstep with ⟨hδ, hidx⟩ | ⟨hlt, hδ, hidx⟩
          · refine ⟨?_, by omega⟩
            rw [hred, show (s.2 : ℕ) = (t.2 : ℕ) by rw [hidx]]
            simpa using M.relFrom_step hδ hrel
          · refine ⟨?_, by omega⟩
            rw [hred, ← seg_concat w (by omega : (s.2 : ℕ) ≤ (s.2 : ℕ) + 1) (by omega),
              seg_succ w hlt]
            rw [hidx] at hrel
            exact M.relFrom_step hδ hrel

/-- The outputs of `M` on the input `w`, from a state of `S` to a state of
`T`. -/
def outputs : Language B := {x | ∃ q ∈ S, ∃ q' ∈ T, M.relFrom q w x q'}

lemma outNFA_accepts (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) :
    (outNFA M S T w).accepts = outputs M S T w := by
  ext x
  rw [εNFA.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨⟨q, i⟩, ⟨q', j⟩, y, ⟨hq, hi⟩, ⟨hq', hj⟩, rfl, hpath⟩
    obtain ⟨hrel, -⟩ := relFrom_of_isPath M S T w y (q, i) (q', j) hpath
    refine ⟨q, hq, q', hq', ?_⟩
    dsimp only at hi hj hrel
    rw [hi, hj] at hrel
    simpa [seg] using hrel
  · rintro ⟨q, hq, q', hq', hrel⟩
    obtain ⟨y, hy, hpath⟩ := isPath_of_relFrom M S T w hatom hrel ⟨0, by omega⟩ (by simp)
    exact ⟨(q, ⟨0, by omega⟩), (q', ⟨w.length, by omega⟩), y, ⟨hq, rfl⟩, ⟨hq', rfl⟩, hy, hpath⟩

end OutLang

/-- For an nfa with output whose transitions read at most one letter and write
at most one letter, the set of outputs on a fixed input is a regular language
over the output alphabet. -/
lemma outputs_isRegular {A B Q : Type} [Finite Q] (M : NFAO A B Q) (S T : Set Q) (w : List A)
    (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) :
    (OutLang.outputs M S T w).IsRegular := by
  rw [← OutLang.outNFA_accepts M S T w hatom]
  exact isRegular_of_εNFA _

end Lax132576Proofs.Transducers
