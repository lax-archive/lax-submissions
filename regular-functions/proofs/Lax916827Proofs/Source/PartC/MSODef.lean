/-
Part C, Section *Logic*: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

The *definitions* of Section *Logic*: monadic second-order logic over strings, mso relabellings and
mso transductions.  They were originally stated in `RequestProject/PartC/MSO.lean`; they have been
moved here, unchanged, so that the automata constructions used in the proofs of Theorem
`thm:mso-logic-languages`, Lemma `lem:mso-free-variables` and Claim
`claim:mso-annotation-regular` can be developed before the statements of the numbered
results. `RequestProject/PartC/MSO.lean` imports this file, so all names are unchanged.

Two conventions are used.

* Variables are named by natural numbers; a valuation assigns a position to
  every first-order variable and a set of positions to every second-order
  variable.  A formula with `k` free first-order variables is used with the
  variables `0, …, k-1`.
* The book uses an extended syntax in which first-order variables have polynomial types `τ = n^{d₁}
  + ⋯ + n^{d_k}` (Section *Regular functions in terms of logic*).  For the linear types `τ = k · n +
  c` that are used in mso transductions, quantification over an element of `τ (w)` is the same as a
  case distinction over the `k + c` variants, and a variable of type `2^τ` is the same as `k` set
  variables plus `c` Booleans.  Accordingly, `MSOTransduction` below is presented by families of
  ordinary mso formulas indexed by the variants, which is equivalent to the presentation in
  Definition `def:mso-transduction`.
-/
import Lax132576Proofs.Source.PartB.WeightedStatements
import Lax916827Proofs.Source.PartC.ContAux
import Lax916827Proofs.Source.PartC.TwoWayCont
import Lax916827Proofs.Source.PartC.TwoWayPrecomp
import Lax916827Proofs.Source.PartC.TwoWayRat
import Lax916827Proofs.Source.PartC.TwoWayCompFinal
import Lax916827Proofs.Source.PartC.TwoWayRegular
import Lax916827Proofs.Source.PartC.RegClosure
import Lax916827Proofs.Source.PartC.SSTRegular
import Lax916827Proofs.Source.PartC.SSTTwoWay
import Lax916827Proofs.Source.PartC.KTypes
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## Monadic second-order logic -/

/-- Formulas of monadic second-order logic over strings with letters in `A`.
First-order variables range over positions, second-order variables over sets of
positions; both kinds of variables are named by natural numbers. -/
inductive MSO (A : Type) : Type
  /-- The order test `x_i ≤ x_j`. -/
  | le : ℕ → ℕ → MSO A
  /-- The label test `a (x_i)`. -/
  | lab : A → ℕ → MSO A
  /-- The membership test `x_i ∈ X_j`. -/
  | mem : ℕ → ℕ → MSO A
  /-- Negation. -/
  | not : MSO A → MSO A
  /-- Conjunction. -/
  | and : MSO A → MSO A → MSO A
  /-- Disjunction. -/
  | or : MSO A → MSO A → MSO A
  /-- First-order existential quantification `∃ x_i`. -/
  | exFO : ℕ → MSO A → MSO A
  /-- Second-order existential quantification `∃ X_i`. -/
  | exSO : ℕ → MSO A → MSO A

namespace MSO

variable {A : Type}

/-- Satisfaction of a formula in a string, under a valuation of the first-order
variables (by positions) and of the second-order variables (by sets of
positions). -/
def Sat (w : List A) : (ℕ → ℕ) → (ℕ → Set ℕ) → MSO A → Prop
  | fo, _, le i j => fo i ≤ fo j
  | fo, _, lab a i => w[fo i]? = some a
  | fo, so, mem i j => fo i ∈ so j
  | fo, so, not φ => ¬ Sat w fo so φ
  | fo, so, and φ ψ => Sat w fo so φ ∧ Sat w fo so ψ
  | fo, so, or φ ψ => Sat w fo so φ ∨ Sat w fo so ψ
  | fo, so, exFO i φ => ∃ p < w.length, Sat w (Function.update fo i p) so φ
  | fo, so, exSO i φ => ∃ S ⊆ {p | p < w.length}, Sat w fo (Function.update so i S) φ

/-- A formula is first-order if it uses neither set quantification nor set
membership. -/
def IsFO : MSO A → Prop
  | le _ _ => True
  | lab _ _ => True
  | mem _ _ => False
  | not φ => IsFO φ
  | and φ ψ => IsFO φ ∧ IsFO ψ
  | or φ ψ => IsFO φ ∧ IsFO ψ
  | exFO _ φ => IsFO φ
  | exSO _ _ => False

/-- The quantifier rank of a formula: the maximal number of nested
quantifiers. -/
def qrank : MSO A → ℕ
  | le _ _ => 0
  | lab _ _ => 0
  | mem _ _ => 0
  | not φ => qrank φ
  | and φ ψ => max (qrank φ) (qrank ψ)
  | or φ ψ => max (qrank φ) (qrank ψ)
  | exFO _ φ => qrank φ + 1
  | exSO _ φ => qrank φ + 1

/-- The free first-order variables of a formula. -/
def freeFO : MSO A → Set ℕ
  | le i j => {i, j}
  | lab _ i => {i}
  | mem i _ => {i}
  | not φ => freeFO φ
  | and φ ψ => freeFO φ ∪ freeFO ψ
  | or φ ψ => freeFO φ ∪ freeFO ψ
  | exFO i φ => freeFO φ \ {i}
  | exSO _ φ => freeFO φ

/-- The free second-order variables of a formula. -/
def freeSO : MSO A → Set ℕ
  | le _ _ => ∅
  | lab _ _ => ∅
  | mem _ j => {j}
  | not φ => freeSO φ
  | and φ ψ => freeSO φ ∪ freeSO ψ
  | or φ ψ => freeSO φ ∪ freeSO ψ
  | exFO _ φ => freeSO φ
  | exSO i φ => freeSO φ \ {i}

end MSO

/-- A language is definable in monadic second-order logic. -/
def MSODefinable {A : Type} (L : Language A) : Prop :=
  ∃ φ : MSO A, ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat w fo so φ ↔ w ∈ L

/-- A language is definable in first-order logic. -/
def FODefinable {A : Type} (L : Language A) : Prop :=
  ∃ φ : MSO A, φ.IsFO ∧
    ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat w fo so φ ↔ w ∈ L

open scoped Classical in
/-- The annotation `w ⊗ {x₁} ⊗ ⋯ ⊗ {x_k} ⊗ X₁ ⊗ ⋯ ⊗ X_l` of a string by the
values of `k` first-order and `l` second-order variables. -/
noncomputable def annotate {A : Type} (k l : ℕ) (w : List A)
    (fo : Fin k → ℕ) (so : Fin l → Set ℕ) : List (A × (Fin k → Bool) × (Fin l → Bool)) :=
  w.zipIdx.map (fun z => (z.1, fun i => decide (fo i = z.2), fun j => decide (z.2 ∈ so j)))

/-- Extend a valuation of the variables `0, …, k-1` to all variables. -/
def extFO (k : ℕ) (fo : Fin k → ℕ) : ℕ → ℕ :=
  fun i => if h : i < k then fo ⟨i, h⟩ else 0

/-- Extend a valuation of the set variables `0, …, l-1` to all variables. -/
def extSO (l : ℕ) (so : Fin l → Set ℕ) : ℕ → Set ℕ :=
  fun j => if h : j < l then so ⟨j, h⟩ else ∅

/-! ## Rational functions in terms of logic -/

/-- **Definition `def:mso-relabeling` (mso relabelling).**  A finite family of mso formulas
with one free first-order variable (the variable `0`), exactly one of which
holds in each position, together with an output string for each formula and an
output string for the empty input. -/
structure MSORelabelling (A B : Type) where
  /-- The (finite) index set of the formulas. -/
  Idx : Type
  /-- Finiteness of the index set. -/
  finIdx : Finite Idx
  /-- The formulas, each with one free first-order variable `x₀`. -/
  form : Idx → MSO A
  /-- The output string of each formula. -/
  out : Idx → List B
  /-- The output string for the empty input. -/
  emptyOut : List B
  /-- In every position of every input string exactly one formula holds. -/
  unique : ∀ (w : List A) (p : ℕ), p < w.length →
    ∃! i : Idx, MSO.Sat w (fun _ => p) (fun _ => ∅) (form i)

namespace MSORelabelling

variable {A B : Type}

/-- The function defined by an mso relabelling: each position contributes the
output string of the unique formula that holds in it. -/
def Relabels (R : MSORelabelling A B) (w : List A) (v : List B) : Prop :=
  (w = [] ∧ v = R.emptyOut) ∨
  (w ≠ [] ∧ ∃ g : ℕ → R.Idx,
    (∀ p < w.length, MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form (g p))) ∧
    v = ((List.range w.length).map (fun p => R.out (g p))).flatten)

/-- All formulas of the relabelling are first-order. -/
def AllFO (R : MSORelabelling A B) : Prop := ∀ i, (R.form i).IsFO

end MSORelabelling

/-- A function defined by an mso relabelling. -/
def IsMSORelabelling {A B : Type} (f : List A → List B) : Prop :=
  ∃ R : MSORelabelling A B, ∀ w, R.Relabels w (f w)

/-- A function defined by a first-order relabelling. -/
def IsFORelabelling {A B : Type} (f : List A → List B) : Prop :=
  ∃ R : MSORelabelling A B, R.AllFO ∧ ∀ w, R.Relabels w (f w)

/-! ## Regular functions in terms of logic -/

/-- **Definition `def:mso-transduction` (string-to-string mso transduction).**  The elements of
the output universe come from a linear type `τ = k · n + c`: `k` copies of the
positions of the input string, and `c` extra elements.  The universe, letter and
order formulas are given by families indexed by the variants of `τ`. -/
structure MSOTransduction (A B : Type) where
  /-- The number of copies of the input positions. -/
  copies : ℕ
  /-- The number of extra (constant) elements. -/
  extra : ℕ
  /-- Universe formulas for the copies of the positions; free variable `x₀`. -/
  univP : Fin copies → MSO A
  /-- Universe formulas for the extra elements; sentences. -/
  univC : Fin extra → MSO A
  /-- Letter formulas for the copies of the positions; free variable `x₀`. -/
  labP : Fin copies → B → MSO A
  /-- Letter formulas for the extra elements; sentences. -/
  labC : Fin extra → B → MSO A
  /-- Order formulas between two copies of positions; free variables `x₀, x₁`. -/
  ordPP : Fin copies → Fin copies → MSO A
  /-- Order formulas between a copy of a position and an extra element. -/
  ordPC : Fin copies → Fin extra → MSO A
  /-- Order formulas between an extra element and a copy of a position. -/
  ordCP : Fin extra → Fin copies → MSO A
  /-- Order formulas between two extra elements. -/
  ordCC : Fin extra → Fin extra → MSO A

namespace MSOTransduction

variable {A B : Type}

/-- The elements of the type `τ = k · n + c`, before selection by the universe
formulas. -/
abbrev Elt (T : MSOTransduction A B) : Type := (Fin T.copies × ℕ) ⊕ Fin T.extra

/-- The elements selected by the universe formulas. -/
def selected (T : MSOTransduction A B) (w : List A) : T.Elt → Prop
  | Sum.inl (i, p) => p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (T.univP i)
  | Sum.inr j => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.univC j)

/-- The order defined by the order formulas. -/
def ordRel (T : MSOTransduction A B) (w : List A) : T.Elt → T.Elt → Prop
  | Sum.inl (i, p), Sum.inl (i', p') =>
      MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅) (T.ordPP i i')
  | Sum.inl (i, p), Sum.inr j => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordPC i j)
  | Sum.inr j, Sum.inl (i, p) => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordCP j i)
  | Sum.inr j, Sum.inr j' => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.ordCC j j')

/-- The labelling defined by the letter formulas. -/
def labRel (T : MSOTransduction A B) (w : List A) : T.Elt → B → Prop
  | Sum.inl (i, p), b => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.labP i b)
  | Sum.inr j, b => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.labC j b)

/-- The semantics of an mso transduction: the output string consists of the
selected elements, ordered by the order formula and labelled by the letter
formulas. -/
def Outputs (T : MSOTransduction A B) (w : List A) (v : List B) : Prop :=
  ∃ es : List T.Elt,
    es.Nodup ∧
    (∀ x, x ∈ es ↔ T.selected w x) ∧
    (∀ (i j : ℕ) (hi : i < es.length) (hj : j < es.length),
      i < j → T.ordRel w (es.get ⟨i, hi⟩) (es.get ⟨j, hj⟩)) ∧
    es.length = v.length ∧
    ∀ (i : ℕ) (hi : i < es.length) (hi' : i < v.length),
      T.labRel w (es.get ⟨i, hi⟩) (v.get ⟨i, hi'⟩)

/-- The two requirements that Definition `def:mso-transduction` imposes on the formulas of an
mso transduction: for every input string, every element selected by the
universe formula satisfies *exactly one* letter formula, and the order formula
defines a *linear order* on the selected elements (reflexive, antisymmetric,
transitive and total on them).

These requirements are part of Definition `def:mso-transduction` in the book; they were missing
from the first formalisation of this file, and without them Theorem `thm:logic-regular-functions` is
false -- see `Transducers.exists_weakMSOTransduction_not_regular` in
`RequestProject/PartC/MSOWeak.lean`. -/
def Proper (T : MSOTransduction A B) : Prop :=
  ∀ w : List A,
    (∀ x, T.selected w x → ∃! b, T.labRel w x b) ∧
    (∀ x, T.selected w x → T.ordRel w x x) ∧
    (∀ x y, T.selected w x → T.selected w y →
      T.ordRel w x y → T.ordRel w y x → x = y) ∧
    (∀ x y z, T.selected w x → T.selected w y → T.selected w z →
      T.ordRel w x y → T.ordRel w y z → T.ordRel w x z) ∧
    (∀ x y, T.selected w x → T.selected w y → T.ordRel w x y ∨ T.ordRel w y x)

/-- All formulas of the transduction are first-order. -/
def AllFO (T : MSOTransduction A B) : Prop :=
  (∀ i, (T.univP i).IsFO) ∧ (∀ j, (T.univC j).IsFO) ∧
  (∀ i b, (T.labP i b).IsFO) ∧ (∀ j b, (T.labC j b).IsFO) ∧
  (∀ i i', (T.ordPP i i').IsFO) ∧ (∀ i j, (T.ordPC i j).IsFO) ∧
  (∀ j i, (T.ordCP j i).IsFO) ∧ (∀ j j', (T.ordCC j j').IsFO)

end MSOTransduction

/-- A function defined by a string-to-string mso transduction, in the sense of
Definition `def:mso-transduction`: the transduction has to satisfy the requirements
`MSOTransduction.Proper` of that definition (exactly one letter formula per
selected element, and a linear order on the selected elements). -/
def IsMSOTransduction {A B : Type} (f : List A → List B) : Prop :=
  ∃ T : MSOTransduction A B, T.Proper ∧ ∀ w, T.Outputs w (f w)

/-- A function defined by a first-order transduction. -/
def IsFOTransduction {A B : Type} (f : List A → List B) : Prop :=
  ∃ T : MSOTransduction A B, T.Proper ∧ T.AllFO ∧ ∀ w, T.Outputs w (f w)

/-- The variant of `IsMSOTransduction` in which the requirements of
Definition `def:mso-transduction` collected in `MSOTransduction.Proper` are dropped.  It is
*strictly* weaker: `Transducers.exists_weakMSOTransduction_not_regular` exhibits
a function that is a weak mso transduction and is not regular. -/
def IsWeakMSOTransduction {A B : Type} (f : List A → List B) : Prop :=
  ∃ T : MSOTransduction A B, ∀ w, T.Outputs w (f w)

end Lax916827Proofs.Transducers
