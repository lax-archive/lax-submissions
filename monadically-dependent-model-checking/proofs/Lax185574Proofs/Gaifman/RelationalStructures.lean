import Mathlib.Data.Fin.Tuple.Basic

/-!
Finite relational vocabularies and structures.

A finite relational vocabulary consists of finitely many relation symbols, each
with a specified finite arity, and finitely many constant symbols. A structure
interprets every relation symbol as a relation of the corresponding arity and
every constant symbol as an element of its carrier.

This is the notion of relational vocabulary used in the stated version of
Gaifman's theorem. Function symbols of positive arity are deliberately absent.
The theorem will quantify over finite carrier types, while the definitions in
this file make sense over any carrier type.

# Formalization notes

The relation symbols are the elements of `Fin relationCount`, each with its
arity (the original stores the arities as a list). Thus finiteness is built
into the type of a vocabulary, rather than imposed by a typeclass side
condition. Constants are represented by
`Fin constantCount`. A structure on an empty carrier can exist exactly when the
vocabulary has no constants, matching the usual convention.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`concepts/Lax512892/RelationalStructures.lean`.
-/

namespace Lax185574Proofs.Gaifman.RelationalStructures

/-- A finite relational vocabulary: finitely many relation symbols, each with
an arity, and a finite number of constant symbols. -/
structure Vocabulary where
  /-- The number of relation symbols. -/
  relationCount : ℕ
  /-- The arity of each relation symbol. -/
  relationArity : Fin relationCount → ℕ
  /-- The number of constant symbols. -/
  constantCount : ℕ

namespace Vocabulary

/-- The finite type of relation symbols of `σ`. -/
abbrev Relation (σ : Vocabulary) := Fin σ.relationCount

/-- The arity of a relation symbol. -/
def arity (σ : Vocabulary) (R : σ.Relation) : ℕ :=
  σ.relationArity R

/-- The finite type of constant symbols of `σ`. -/
abbrev Constant (σ : Vocabulary) := Fin σ.constantCount

end Vocabulary

/-- An interpretation of the relational vocabulary `σ` on the carrier `M`. -/
structure Structure (σ : Vocabulary) (M : Type*) where
  /-- Interpretation of every relation symbol as a relation of its arity. -/
  relation : (R : σ.Relation) → (Fin (σ.arity R) → M) → Prop
  /-- Interpretation of every constant symbol. -/
  constant : σ.Constant → M

end Lax185574Proofs.Gaifman.RelationalStructures
