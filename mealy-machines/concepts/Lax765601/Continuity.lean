import Mathlib.Computability.DFA

/-!
---
title: Continuous string-to-string functions
type: definition
---
A function $f : A^* \to B^*$ between the sets of strings over two alphabets is
*continuous* if for every regular language $L \subseteq B^*$ over the output
alphabet, the inverse image $f^{-1}(L)$ is a regular language over the input
alphabet (Definition 0.1 of *Transducers*). Continuity is the compatibility with
regular languages that every transducer model of the book is required to have:
for functions with two possible outputs it is exactly regularity of a language,
and composing a continuous function with a regular language, seen as a
string-to-Boolean function, gives a regular language again.

The same requirement makes sense for a relation $R \subseteq A^* \times B^*$ and
for a partial function: the set of input strings that are related to (respectively,
mapped to) some string of $L$ has to be regular. The relational form is the one
Part B proves for rational relations, and the partial form the one it proves for
subsequential functions.

# Formalization notes

Strings over an alphabet `A` are `List A`, languages are mathlib's `Language A`
(a set of strings), and regularity is mathlib's `Language.IsRegular`: recognition
by a deterministic finite automaton with a finite state set. This dictionary is
used by every concept of the book and is not repeated.

Alphabets are arbitrary types here. The finiteness of the alphabets, which the
book assumes throughout, is an instance hypothesis `[Finite A]` on the statements
that need it, so that a definition never carries a hypothesis it does not use. A
partial function is a function into `Option (List B)`, with `none` for
"undefined".
-/

namespace Lax765601.Continuity

/-- A string-to-string function is *continuous* if the inverse image of every
regular language over the output alphabet is a regular language. -/
def Continuous {A B : Type} (f : List A → List B) : Prop :=
  ∀ L : Language B, L.IsRegular → Language.IsRegular ({w : List A | f w ∈ L} : Language A)

/-- A relation `R ⊆ A* × B*` is continuous if, for every regular language `L` over
the output alphabet, the set of input strings related to some string of `L` is
regular. -/
def RelContinuous {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∀ L : Language B, L.IsRegular →
    Language.IsRegular ({w : List A | ∃ v, R w v ∧ v ∈ L} : Language A)

/-- A partial function is continuous if, for every regular language `L` over the
output alphabet, the set of input strings whose output is defined and belongs to
`L` is regular. -/
def PartialContinuous {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∀ L : Language B, L.IsRegular →
    Language.IsRegular ({w : List A | ∃ v, f w = some v ∧ v ∈ L} : Language A)

end Lax765601.Continuity
