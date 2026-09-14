/-
Every composition of prime first-order regular functions is a first-order
transduction.

The proof is an induction on the composition, using that first-order
transductions are closed under composition
(`Transducers.isFOTransduction_comp`) and that each prime is a first-order
transduction: first-order relabellings
(`Transducers.isFOTransduction_of_isFORelabelling`), map reverse
(`Transducers.isFOTransduction_mapReverse`) and map duplicate
(`Transducers.isFOTransduction_mapDuplicate`), the last two conjugated by the
letter-to-letter renamings `Transducers.isFOTransduction_map_equiv`.
-/
import Lax314295Proofs.Source.PartC.FOPrimeFam
import Lax314295Proofs.Source.PartC.FOTransComp
import Lax314295Proofs.Source.PartC.FORelabTrans
import Lax314295Proofs.Source.PartC.FOTransRev
import Lax314295Proofs.Source.PartC.FOTransDup
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

/-- Being a first-order transduction only depends on the values of the
function. -/
lemma IsFOTransduction.congr {A B : Type} {f g : List A → List B} (hf : IsFOTransduction f)
    (h : ∀ w, f w = g w) : IsFOTransduction g := by
  have : f = g := funext h
  exact this ▸ hf

/-- Every prime first-order regular function is a first-order transduction. -/
theorem isFOTransduction_of_foRegularFam {A B : Type} {f : List A → List B}
    (hf : FORegularFam A B f) : IsFOTransduction f := by
  rcases hf with h | ⟨A₀, e, e', h⟩ | ⟨A₀, e, e', h⟩
  · exact isFOTransduction_of_isFORelabelling h
  · refine IsFOTransduction.congr ?_ (fun w => (h w).symm)
    have h₁ : IsFOTransduction (fun w : List A => w.map e) := isFOTransduction_map_equiv e
    have h₂ : IsFOTransduction (mapReverse A₀) := isFOTransduction_mapReverse A₀
    have h₃ : IsFOTransduction (fun v : List (Option A₀) => v.map e'.symm) :=
      isFOTransduction_map_equiv e'.symm
    exact isFOTransduction_comp (isFOTransduction_comp h₁ h₂) h₃
  · refine IsFOTransduction.congr ?_ (fun w => (h w).symm)
    have h₁ : IsFOTransduction (fun w : List A => w.map e) := isFOTransduction_map_equiv e
    have h₂ : IsFOTransduction (mapDuplicate A₀) := isFOTransduction_mapDuplicate A₀
    have h₃ : IsFOTransduction (fun v : List (Option A₀) => v.map e'.symm) :=
      isFOTransduction_map_equiv e'.symm
    exact isFOTransduction_comp (isFOTransduction_comp h₁ h₂) h₃

/-- Every composition of first-order relabellings, map reverse and map duplicate is a first-order
transduction.  (This was the easy inclusion of Theorem `nolabel:thm-fo-transduction-into-primes`,
which has been removed from the formalised theorems at the user's request.) -/
theorem isFOTransduction_of_compClosure {A B : Type} {f : List A → List B}
    (hf : CompClosure FORegularFam A B f) : IsFOTransduction f := by
  induction hf with
  | base h => exact isFOTransduction_of_foRegularFam h
  | id A => exact isFOTransduction_id A
  | comp _ _ ih₁ ih₂ => exact isFOTransduction_comp ih₁ ih₂

end Lax314295Proofs.Transducers
