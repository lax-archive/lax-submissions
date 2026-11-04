import Lax185574Proofs.Gaifman.FirstOrder

/-!
Gaifman distance and local formulas.

Two distinct elements of a relational structure are Gaifman-adjacent when they
occur together in a tuple belonging to an interpreted relation. The predicate
`distanceAtMost A r a b` says that the Gaifman graph has a walk of length at
most `r` from `a` to `b`.

An `r`-local formula around a tuple of anchor variables is represented by a
syntax in which every quantifier is explicitly restricted to the union of the
radius-`r` balls around those anchors and around the interpretations of all
vocabulary constants. Its atomic terms may refer to anchors, locally bound
variables, and vocabulary constants. This is the syntactic notion of locality
used by Gaifman's normal-form theorem, not merely a semantic invariance
property.

# Formalization notes

Anchor variables and locally bound variables have separate types. This prevents
a newly quantified variable from silently becoming an additional centre of the
neighbourhood. The semantics of the local existential constructor chooses an
element in the ball around one of the original anchors or a vocabulary constant
and extends only the bound-variable environment. Negation supplies restricted
universal quantification in the usual way. Including constants as centres is
the extension made immediately before Theorem 4.22 in Libkin's *Elements of
Finite Model Theory*.

Distance is defined by bounded walks instead of a minimum taking the value
infinity. At radius zero it is equality. The successor clause either uses a
shorter walk or takes one Gaifman edge followed by a shorter walk.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`concepts/Lax512892/Locality.lean`.
-/

namespace Lax185574Proofs.Gaifman.Locality

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.FirstOrder

/-- Adjacency in the Gaifman graph of a relational structure. -/
def gaifmanAdjacent {σ : Vocabulary} {M : Type*} (A : Structure σ M) (a b : M) : Prop :=
  a ≠ b ∧
    ∃ (R : σ.Relation) (tuple : Fin (σ.arity R) → M),
      A.relation R tuple ∧
        ∃ i j : Fin (σ.arity R), i ≠ j ∧ tuple i = a ∧ tuple j = b

/-- `distanceAtMost A r a b` holds when a walk of at most `r` Gaifman edges
joins `a` to `b`. -/
def distanceAtMost {σ : Vocabulary} {M : Type*} (A : Structure σ M) :
    ℕ → M → M → Prop
  | 0, a, b => a = b
  | r + 1, a, b =>
      distanceAtMost A r a b ∨
        ∃ c : M, gaifmanAdjacent A a c ∧ distanceAtMost A r c b

/-- Membership in the union of the radius-`r` balls around `anchors` and the
interpretations of all vocabulary constants. -/
def inBallAround {σ : Vocabulary} {M : Type*} (A : Structure σ M)
    (r : ℕ) {k : ℕ} (anchors : Fin k → M) (x : M) : Prop :=
  (∃ i : Fin k, distanceAtMost A r (anchors i) x) ∨
    ∃ c : σ.Constant, distanceAtMost A r (A.constant c) x

/-- A term in a local formula, distinguishing the fixed anchor variables from
variables introduced by restricted quantifiers. -/
inductive LocalTerm (σ : Vocabulary) (anchorCount boundCount : ℕ) : Type
  /-- One of the fixed variables around which locality is measured. -/
  | anchor (i : Fin anchorCount)
  /-- A variable introduced by a restricted quantifier. -/
  | bound (i : Fin boundCount)
  /-- A constant of the vocabulary. -/
  | const (c : σ.Constant)

/-- Formulas whose quantifiers are all restricted to the radius-`r` balls
around the original `anchorCount` variables and the vocabulary constants. -/
inductive LocalFormula (σ : Vocabulary) (anchorCount r : ℕ) : ℕ → Type
  /-- A relation atom. -/
  | rel {boundCount : ℕ} (R : σ.Relation)
      (args : Fin (σ.arity R) → LocalTerm σ anchorCount boundCount) :
      LocalFormula σ anchorCount r boundCount
  /-- Equality of local terms. -/
  | eq {boundCount : ℕ} (left right : LocalTerm σ anchorCount boundCount) :
      LocalFormula σ anchorCount r boundCount
  /-- Negation. -/
  | not {boundCount : ℕ} (φ : LocalFormula σ anchorCount r boundCount) :
      LocalFormula σ anchorCount r boundCount
  /-- Disjunction. -/
  | or {boundCount : ℕ} (φ ψ : LocalFormula σ anchorCount r boundCount) :
      LocalFormula σ anchorCount r boundCount
  /-- Existential quantification restricted to the radius-`r` balls around the
  original anchors and the vocabulary constants. -/
  | ex {boundCount : ℕ} (φ : LocalFormula σ anchorCount r (boundCount + 1)) :
      LocalFormula σ anchorCount r boundCount

namespace LocalTerm

/-- Interpretation of a term occurring in a local formula. -/
def eval {σ : Vocabulary} {M : Type*} {anchorCount boundCount : ℕ}
    (A : Structure σ M)
    (anchors : Fin anchorCount → M) (bound : Fin boundCount → M) :
    LocalTerm σ anchorCount boundCount → M
  | .anchor i => anchors i
  | .bound i => bound i
  | .const c => A.constant c

end LocalTerm

namespace LocalFormula

/-- Satisfaction for a syntactically local formula. Every existential witness
is required to lie in the fixed neighbourhood of the anchor tuple. -/
def Sat {σ : Vocabulary} {M : Type*} {anchorCount r : ℕ}
    (A : Structure σ M)
    (anchors : Fin anchorCount → M) :
    {boundCount : ℕ} → LocalFormula σ anchorCount r boundCount →
      (Fin boundCount → M) → Prop
  | _, .rel R args, bound =>
      A.relation R (fun i => (args i).eval A anchors bound)
  | _, .eq left right, bound =>
      left.eval A anchors bound = right.eval A anchors bound
  | _, .not φ, bound => ¬ Sat A anchors φ bound
  | _, .or φ ψ, bound => Sat A anchors φ bound ∨ Sat A anchors ψ bound
  | _, .ex φ, bound =>
      ∃ x : M, inBallAround A r anchors x ∧ Sat A anchors φ (Fin.snoc bound x)

end LocalFormula

end Lax185574Proofs.Gaifman.Locality
