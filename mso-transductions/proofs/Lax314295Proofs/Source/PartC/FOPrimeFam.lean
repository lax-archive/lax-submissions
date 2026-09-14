/-
The family of prime first-order regular functions.

The definition `Transducers.FORegularFam` was originally stated in
`RequestProject/PartC/MSOOpen.lean`, next to Theorem `nolabel:thm-fo-transduction-into-primes`
(which has since been removed from the formalised theorems at the user's request); it has been moved
here, unchanged, so that the proof that compositions of primes are first-order transductions can be
developed on its own (`RequestProject/PartC/FOTransPrimeComp.lean`). -/
import Lax916827Proofs.Source.PartC.MSODef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

/-- The family of prime first-order regular functions: first-order rational
functions (equivalently, first-order relabellings), map reverse and map
duplicate. -/
def FORegularFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsFORelabelling f ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapReverse A₀ (w.map e)).map e'.symm) ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapDuplicate A₀ (w.map e)).map e'.symm)

end Lax314295Proofs.Transducers
