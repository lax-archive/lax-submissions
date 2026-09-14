/-
Automata with labelled transitions: the common basis of nondeterministic
automata with output (Definition `def:nfa-with-output`) and of weighted automata
(Definition `def:weighted-automaton`) of *Transducers* (M. Bojanczyk).

This file contains the definitions themselves (moved here from
`RequestProject/PartB/RationalStatements.lean`, so that the constructions of Part B can be
developed before the statements of the numbered results) together with a
convenient reformulation of the semantics of an nfa with output: the ternary
relation `relFrom q w v p`, which says that some path from `q` to `p` reads `w`
and writes `v`.  All later constructions are carried out with this relation,
which enjoys a simple induction principle.
-/
import Lax765601Proofs.Source.PartA.MealyBasic
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-! ## Automata with labelled transitions

Both nondeterministic automata with output (Definition `def:nfa-with-output`) and weighted
automata (Definition `def:weighted-automaton`) are automata whose transitions are labelled
by an input string together with a label from some set `L` (output strings in the first case,
semiring elements in the second).  We therefore define them at once. -/

/-- An automaton whose finitely many transitions are labelled by an input string
and a label from `L`, with distinguished sets of initial and final states. -/
structure LabAut (A L Q : Type) where
  /-- The set of initial states. -/
  init : Set Q
  /-- The set of final states. -/
  final : Set Q
  /-- The transition relation. -/
  δ : Set (Q × List A × L × Q)
  /-- There are only finitely many transitions. -/
  δ_finite : δ.Finite

namespace LabAut

variable {A L Q : Type}

/-- A path in the automaton, given as the list of transitions that it uses. -/
inductive Path (M : LabAut A L Q) : Q → List (Q × List A × L × Q) → Q → Prop
  | nil (q : Q) : Path M q [] q
  | cons {q : Q} {u : List A} {l : L} {q' : Q} {ts : List (Q × List A × L × Q)} {p : Q} :
      (q, u, l, q') ∈ M.δ → Path M q' ts p → Path M q ((q, u, l, q') :: ts) p

/-- The input string of a path. -/
def inputOf (ts : List (Q × List A × L × Q)) : List A := (ts.map (fun t => t.2.1)).flatten

/-- The list of labels along a path. -/
def labelsOf (ts : List (Q × List A × L × Q)) : List L := ts.map (fun t => t.2.2.1)

/-- A path is accepting if it starts in an initial state and ends in a final
state. -/
def Accepting (M : LabAut A L Q) (ts : List (Q × List A × L × Q)) : Prop :=
  ∃ q ∈ M.init, ∃ p ∈ M.final, M.Path q ts p

/-- The set of accepting paths with a given input string. -/
def acceptingOn (M : LabAut A L Q) (w : List A) : Set (List (Q × List A × L × Q)) :=
  {ts | M.Accepting ts ∧ inputOf ts = w}

@[simp] lemma inputOf_nil : inputOf ([] : List (Q × List A × L × Q)) = [] := rfl

@[simp] lemma inputOf_cons (t : Q × List A × L × Q) (ts : List (Q × List A × L × Q)) :
    inputOf (t :: ts) = t.2.1 ++ inputOf ts := rfl

@[simp] lemma labelsOf_nil : labelsOf ([] : List (Q × List A × L × Q)) = [] := rfl

@[simp] lemma labelsOf_cons (t : Q × List A × L × Q) (ts : List (Q × List A × L × Q)) :
    labelsOf (t :: ts) = t.2.2.1 :: labelsOf ts := rfl

lemma Path.append {M : LabAut A L Q} {q r p : Q} {ts ts' : List (Q × List A × L × Q)}
    (h : M.Path q ts r) (h' : M.Path r ts' p) : M.Path q (ts ++ ts') p := by
  induction h with
  | nil q => simpa using h'
  | cons ht _ ih => exact Path.cons ht (ih h')

end LabAut

/-! ## Weighted automata

The semantics of a weighted automaton (Definition `def:weighted-automaton`) is also given
here, so that the constructions of Section *Rational relations and weighted automata* can be
developed before the statements of the numbered results; the statements themselves are in
`RequestProject/PartB/WeightedStatements.lean`. -/

namespace LabAut

variable {A S Q : Type} [Semiring S]

/-- The weight of a path: the product of the weights of its transitions, taken
in the order in which they occur. -/
def weightOf (ts : List (Q × List A × S × Q)) : S := (labelsOf ts).prod

@[simp] lemma weightOf_nil : weightOf ([] : List (Q × List A × S × Q)) = 1 := rfl

@[simp] lemma weightOf_cons (t : Q × List A × S × Q) (ts : List (Q × List A × S × Q)) :
    weightOf (t :: ts) = t.2.2.1 * weightOf ts := rfl

lemma weightOf_append (ts ts' : List (Q × List A × S × Q)) :
    weightOf (ts ++ ts') = weightOf ts * weightOf ts' := by
  simp [weightOf, labelsOf]

/-- **Definition `def:weighted-automaton` (Weighted automaton), semantics.**  The output on
an input string `w` is the sum of the weights of the accepting runs over `w`. -/
noncomputable def wEval (M : LabAut A S Q) (w : List A) : S :=
  ∑ᶠ ts ∈ M.acceptingOn w, weightOf ts

/-- The requirement, part of Definition `def:weighted-automaton`, that every input string
has only finitely many accepting runs. -/
def FinitelyManyRuns (M : LabAut A S Q) : Prop := ∀ w : List A, (M.acceptingOn w).Finite

end LabAut

/-- A function `A* → S` computed by a weighted automaton over the semiring
`S`. -/
def IsWeighted {A S : Type} [Semiring S] (f : List A → S) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : LabAut A S Q),
    M.FinitelyManyRuns ∧ M.wEval = f

/-! ## Rational relations -/

/-- **Definition `def:nfa-with-output` (nfa with output).**  A nondeterministic automaton
with output is an automaton whose transitions are labelled by pairs of an input string and an output
string. -/
abbrev NFAO (A B Q : Type) := LabAut A (List B) Q

namespace NFAO

variable {A B Q : Type}

/-- The output string of a path in an nfa with output. -/
def outputOf (ts : List (Q × List A × List B × Q)) : List B :=
  (LabAut.labelsOf ts).flatten

@[simp] lemma outputOf_nil : outputOf ([] : List (Q × List A × List B × Q)) = [] := rfl

@[simp] lemma outputOf_cons (t : Q × List A × List B × Q)
    (ts : List (Q × List A × List B × Q)) : outputOf (t :: ts) = t.2.2.1 ++ outputOf ts := rfl

/-- The relation computed by an nfa with output. -/
def rel (M : NFAO A B Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ outputOf ts = v

/-- An nfa with output is unambiguous if every input string has exactly one
accepting run. -/
def Unambiguous (M : NFAO A B Q) : Prop :=
  ∀ w : List A, ∃! ts, M.Accepting ts ∧ LabAut.inputOf ts = w

/-! ### The relation computed between two given states -/

/-- `M.relFrom q w v p` holds if some path from `q` to `p` reads the input `w`
and writes the output `v`. -/
def relFrom (M : NFAO A B Q) (q : Q) (w : List A) (v : List B) (p : Q) : Prop :=
  ∃ ts, M.Path q ts p ∧ LabAut.inputOf ts = w ∧ outputOf ts = v

lemma relFrom_nil (M : NFAO A B Q) (q : Q) : M.relFrom q [] [] q :=
  ⟨[], LabAut.Path.nil q, rfl, rfl⟩

lemma relFrom_step {M : NFAO A B Q} {q q' p : Q} {u : List A} {x : List B}
    {w : List A} {v : List B} (ht : (q, u, x, q') ∈ M.δ) (h : M.relFrom q' w v p) :
    M.relFrom q (u ++ w) (x ++ v) p := by
  obtain ⟨ts, hts, hin, hout⟩ := h
  exact ⟨(q, u, x, q') :: ts, LabAut.Path.cons ht hts, by simp [hin], by simp [hout]⟩

lemma relFrom_single {M : NFAO A B Q} {q q' : Q} {u : List A} {x : List B}
    (ht : (q, u, x, q') ∈ M.δ) : M.relFrom q u x q' := by
  simpa using relFrom_step ht (M.relFrom_nil q')

lemma relFrom_trans {M : NFAO A B Q} {q r p : Q} {w w' : List A} {v v' : List B}
    (h : M.relFrom q w v r) (h' : M.relFrom r w' v' p) :
    M.relFrom q (w ++ w') (v ++ v') p := by
  obtain ⟨ts, hts, rfl, rfl⟩ := h
  obtain ⟨ts', hts', rfl, rfl⟩ := h'
  refine ⟨ts ++ ts', hts.append hts', ?_, ?_⟩
  · simp [LabAut.inputOf]
  · simp [outputOf, LabAut.labelsOf]

/-- The induction principle for `relFrom`: a path is either empty, or starts
with a transition. -/
lemma relFrom_induction {M : NFAO A B Q} {motive : Q → List A → List B → Prop} {p : Q}
    (hnil : motive p [] [])
    (hcons : ∀ (q q' : Q) (u : List A) (x : List B) (w : List A) (v : List B),
      (q, u, x, q') ∈ M.δ → M.relFrom q' w v p → motive q' w v → motive q (u ++ w) (x ++ v)) :
    ∀ {q : Q} {w : List A} {v : List B}, M.relFrom q w v p → motive q w v := by
  rintro q w v ⟨ts, hts, rfl, rfl⟩
  induction hts with
  | nil q => simpa using hnil
  | @cons q u l q' ts p ht hpath ih =>
      simpa using hcons q q' u l (LabAut.inputOf ts) (outputOf ts) ht ⟨ts, hpath, rfl, rfl⟩ (ih hnil hcons)

lemma rel_iff_relFrom (M : NFAO A B Q) (w : List A) (v : List B) :
    M.rel w v ↔ ∃ q ∈ M.init, ∃ p ∈ M.final, M.relFrom q w v p := by
  constructor
  · rintro ⟨ts, ⟨q, hq, p, hp, hpath⟩, hin, hout⟩
    exact ⟨q, hq, p, hp, ts, hpath, hin, hout⟩
  · rintro ⟨q, hq, p, hp, ts, hpath, hin, hout⟩
    exact ⟨ts, ⟨q, hq, p, hp, hpath⟩, hin, hout⟩

end NFAO

/-- A state of an nfa with output is *productive* if it appears in some
accepting run. -/
def Productive {A B Q : Type} (M : NFAO A B Q) (q : Q) : Prop :=
  ∃ q₀ ∈ M.init, ∃ p ∈ M.final, ∃ ts₁ ts₂, M.Path q₀ ts₁ q ∧ M.Path q ts₂ p

/-- **Definition `def:rational-relation` (Rational relation).**  A relation is rational if it is
computed by a nondeterministic automaton with output. -/
def IsRationalRel {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), ∀ w v, R w v ↔ M.rel w v

/-- A relation computed by an *unambiguous* nfa with output. -/
def IsUnambiguousRel {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), M.Unambiguous ∧ ∀ w v, R w v ↔ M.rel w v

/-- **Definition `def:rational-function` (Rational function).**  A (total) string-to-string
function is rational if its graph is a rational relation. -/
def IsRationalFun {A B : Type} (f : List A → List B) : Prop :=
  IsRationalRel (fun w v => v = f w)

/-- The string homomorphism induced by a map `A → B*`. -/
def homOf {A B : Type} (φ : A → List B) : List A → List B := fun w => (w.map φ).flatten

end Lax132576Proofs.Transducers
