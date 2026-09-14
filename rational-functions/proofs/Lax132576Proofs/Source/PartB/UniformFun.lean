/-
**Uniformisation, in the form of a function** (Lemma `lem:uniformisation`).

`Transducers.uniformisation` (`RequestProject/PartB/Uniform.lean`) states the
book's Lemma `lem:uniformisation`: a total rational relation contains an *unambiguous* rational
relation.  An unambiguous nfa with output has exactly one accepting run over
every input, so the relation it computes is the graph of a (total) function,
which is therefore a rational function contained in the original relation.  That
form of the lemma -- *a total rational relation contains the graph of a rational
function* -- is what one uses when a string-to-string function is defined by
"guess an annotation of the input and check it": the checking need not determine
the annotation uniquely.
-/
import Lax132576Proofs.Source.PartB.Uniform
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

open LabAut NFAO

/-- **Uniformisation as a function** (Lemma `lem:uniformisation`).  A total rational relation
contains the graph of a rational function. -/
theorem exists_rationalFun_of_total_rel {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (htotal : ∀ w, ∃ v, R w v) :
    ∃ f : List A → List B, IsRationalFun f ∧ ∀ w, R w (f w) := by
  classical
  obtain ⟨S, hSR, P, hP, N, hunamb, hSN⟩ := uniformisation_aux hR htotal
  refine ⟨fun w => outputOf (hunamb w).choose, ⟨P, hP, N, ?_⟩, ?_⟩
  · intro w v
    obtain ⟨⟨hacc, hin⟩, huniq⟩ := (hunamb w).choose_spec
    constructor
    · rintro rfl
      exact ⟨(hunamb w).choose, hacc, hin, rfl⟩
    · rintro ⟨ts, hts, htsin, rfl⟩
      rw [huniq ts ⟨hts, htsin⟩]
  · intro w
    obtain ⟨⟨hacc, hin⟩, -⟩ := (hunamb w).choose_spec
    exact hSR w _ ((hSN w _).mpr ⟨(hunamb w).choose, hacc, hin, rfl⟩)

end Lax132576Proofs.Transducers
