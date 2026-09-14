/-
Every regular function is computed by a streaming string transducer: the
"regular to sst" half of Theorem `theorem:sst-two-way-equivalence` of *Transducers* (M. Bojańczyk).

The book's argument is that sst's are closed under post-composition with each of
the prime regular functions -- rational functions (`SSTMealy.lean`), map reverse
(`SSTMapRev.lean`) and map duplicate (`SSTMapDup.lean`).  Since a regular
function is a composition of primes, sst's are closed under post-composition
with every regular function; applying this to the identity sst gives the
statement.
-/
import Lax916827Proofs.Source.PartC.RegularDef
import Lax916827Proofs.Source.PartC.SSTMealy
import Lax916827Proofs.Source.PartC.SSTMapDup
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- sst's are closed under post-composition with a prime regular function. -/
lemma isSST_comp_regularFam {B C : Type} [Finite B] [Finite C] {p : List B → List C}
    (hp : RegularFam B C p) {A : Type} {f : List A → List B} (hf : IsSST f) :
    IsSST (fun w => p (f w)) := by
  rcases hp with hrat | ⟨A₀, e, e', hpe⟩ | ⟨A₀, e, e', hpe⟩
  · exact isSST_comp_rational hrat hf
  · exact (isSST_comp_map (isSST_comp_mapReverse (isSST_comp_map hf (e : B → Option A₀)))
      (e'.symm : Option A₀ → C)).congr (fun w => (hpe (f w)).symm)
  · exact (isSST_comp_map (isSST_comp_mapDuplicate (isSST_comp_map hf (e : B → Option A₀)))
      (e'.symm : Option A₀ → C)).congr (fun w => (hpe (f w)).symm)

/-- sst's are closed under post-composition with a composition of prime regular
functions. -/
lemma isSST_comp_compClosureRegular {B C : Type} {p : List B → List C}
    (hp : CompClosure RegularFam B C p) :
    Finite B → Finite C → ∀ {A : Type} {f : List A → List B}, IsSST f →
      IsSST (fun w => p (f w)) := by
  induction hp with
  | base h =>
      intro hB hC A f hf
      haveI := hB; haveI := hC
      exact isSST_comp_regularFam h hf
  | id B => intro _ _ A f hf; exact hf
  | @comp B M C hM p₁ p₂ _ _ ih₁ ih₂ =>
      intro hB hC A f hf
      exact ih₂ hM hC (ih₁ hB hM hf)

/-- **sst's are closed under post-composition with a regular function.** -/
theorem isSST_comp_regular {B C : Type} [Finite B] [Finite C] {p : List B → List C}
    (hp : IsRegularFun p) {A : Type} {f : List A → List B} (hf : IsSST f) :
    IsSST (fun w => p (f w)) :=
  isSST_comp_compClosureRegular hp inferInstance inferInstance hf

/-- **Theorem `theorem:sst-two-way-equivalence`, right-to-left implication.**  Every regular
function is computed by a streaming string transducer. -/
theorem isSST_of_isRegularFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsSST f :=
  (isSST_comp_regular hf (isSST_id (A := A))).congr (fun _ => rfl)

end Lax916827Proofs.Transducers
