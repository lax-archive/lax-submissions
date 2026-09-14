/-
**Claim `claim:from-child-configuration-graph-to-children`.**

The claim of *Transducers* (M. Bojańczyk) reads:

> There is a for-transducer which inputs the string representation of a child configuration graph,
> and outputs the concatenation of the string representations of the corresponding child
> configurations.

Here the string representation of a child configuration graph is a word over the alphabet
`Transducers.CG.CGLetter A Q k` of `RequestProject/PartD/ChildGraph.lean`, and the string
representation of the children is the word `Transducers.CG.cgOut` over the alphabet
`Transducers.CG.ConfLetter A Q k` of configuration letters; the predicate
`Transducers.CG.CGOutIs u v` says that `v` is the string representation of the children of the
graph represented by `u`, and it determines `v` (`Transducers.CG.cgOutIs_unique`).

The for-transducer is obtained from the two-pebble transducer
`Transducers.CG.cgAut` of `RequestProject/PartD/ChildGraphAut.lean` through Theorem
`thm:pebble-are-for` (`Transducers.pebble_iff_forTransducer`).  This is a divergence from the
book, which proves the claim directly by induction on the width of the graph, as in
Lemma `lem:output-of-snake-graph-is-regular`; the statement obtained is the same.
-/
import Lax194892Proofs.Source.PartD.ChildGraphRun
import Lax194892Proofs.Source.PartD.Statements
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers
open Lax314295Proofs Lax314295Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CG

variable {A Q : Type} {k : ℕ} [Finite Q]

/-- The function computed by the machine `cgAut`: on a well-formed string representation of a
child configuration graph it is the concatenation of the string representations of the children,
and on every other string it is whatever the (total) machine happens to print. -/
noncomputable def cgFun (u : List (CGLetter A Q k)) : List (ConfLetter A Q k) :=
  (cgAut_halts u).choose

lemma cgAut_computes_cgFun (u : List (CGLetter A Q k)) : cgAut.Computes u (cgFun u) :=
  (cgAut_halts u).choose_spec

lemma cgFun_isPebbleTransducer : IsPebbleTransducer (cgFun (A := A) (Q := Q) (k := k)) :=
  ⟨2, PSt Q, inferInstance, cgAut, cgAut_computes_cgFun⟩

lemma cgFun_eq_of_cgOutIs {u : List (CGLetter A Q k)} {v : List (ConfLetter A Q k)}
    (h : CGOutIs u v) : cgFun u = v := by
  obtain ⟨m, p, hp, rfl⟩ := h
  exact Pebble.computes_unique (cgAut_computes_cgFun u) (cgAut_computes_cgOut hp)

end CG

/-- **Claim `claim:from-child-configuration-graph-to-children`.**  There is a for-transducer which
inputs the string representation of a child configuration graph, and outputs the concatenation of
the string representations of the corresponding child configurations. -/
theorem from_child_configuration_graph_to_children
    {A Q : Type} [Finite A] [Finite Q] (k : ℕ) :
    ∃ f : List (CG.CGLetter A Q k) → List (CG.ConfLetter A Q k),
      IsForTransducer f ∧ ∀ u v, CG.CGOutIs u v → f u = v :=
  ⟨CG.cgFun, (pebble_iff_forTransducer _).1 CG.cgFun_isPebbleTransducer,
    fun _ _ h => CG.cgFun_eq_of_cgOutIs h⟩

end Lax194892Proofs.Transducers
