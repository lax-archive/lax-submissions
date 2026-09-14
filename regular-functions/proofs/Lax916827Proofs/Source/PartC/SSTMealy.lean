/-
Post-composition of a streaming string transducer with a Mealy machine, and
hence with an arbitrary rational function (a step of the "regular to sst" half
of Theorem `theorem:sst-two-way-equivalence` of *Transducers*, M. Bojańczyk).

As the book explains, the naive construction -- keep, for every register `X` of
the sst and every state `q` of the Mealy machine, a register `X_q` holding the
Mealy image of the content of `X` read from the state `q` -- is *not* copyless:
simulating a concatenation `X ↦ Y Z` needs `Z_{q'}` where `q'` is the state
reached after the content of `Y`, and the map `q ↦ q'` need not be injective.
The book therefore uses the Krohn-Rhodes decomposition (Theorem `thm:krohn-rhodes`, already
available in this development through `PrimeMealyFam`) and does the construction
for the two kinds of prime Mealy machines:

* **reversible machines**, where `q ↦ q'` is injective and the naive
  construction works;
* **flip-flop machines**, where every letter either keeps the state or resets it
  to a fixed one; there, each register is split into a *left* part (up to and
  including the first reset letter, kept in `|Q|` copies, one for each starting
  state) and a *right* part (the rest, which does not depend on the starting
  state).

The two constructions are the contents of `isSST_comp_reversibleMealy` and
`isSST_comp_flipFlopMealy`; everything else in this file is bookkeeping.
-/
import Lax132576Proofs.Source.PartB.RationalStatements
import Lax916827Proofs.Source.PartC.SSTMealyRev
import Lax916827Proofs.Source.PartC.SSTMealyFF
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A B C : Type}

/-- sst's are closed under post-composition with a prime Mealy machine. -/
theorem isSST_comp_primeMealy {p : List B → List C} (hp : PrimeMealyFam B C p)
    {f : List A → List B} (hf : IsSST f) : IsSST (fun w => p (f w)) := by
  rcases hp with ⟨Q, hQ, M, rfl, hM⟩ | ⟨Q, hQ, M, rfl, hM⟩
  · haveI := hQ
    exact isSST_comp_reversibleMealy hf M hM
  · haveI := hQ
    exact isSST_comp_flipFlopMealy hf M hM

/-- sst's are closed under post-composition with a prime rational function. -/
theorem isSST_comp_primeRational {p : List B → List C} (hp : PrimeRationalFam B C p)
    {f : List A → List B} (hf : IsSST f) : IsSST (fun w => p (f w)) := by
  rcases hp with hM | hM | ⟨φ, rfl⟩ | ⟨e, rfl⟩
  · exact isSST_comp_primeMealy hM hf
  · -- a right-to-left prime Mealy machine: `p v = (g v.reverse).reverse` for the
    -- left-to-right machine `g`
    have h1 : IsSST (fun w => (f w).reverse) := isSST_comp_reverse hf
    have h2 := isSST_comp_primeMealy hM h1
    have h3 := isSST_comp_reverse h2
    exact h3.congr (fun w => by simp)
  · exact isSST_comp_hom hf φ
  · exact isSST_comp_append (isSST_comp_map hf (fun b => e (some b))) [e none]

/-- sst's are closed under post-composition with a composition of prime rational
functions. -/
lemma isSST_comp_compClosureRational {B C : Type} {p : List B → List C}
    (hp : CompClosure PrimeRationalFam B C p) :
    ∀ {A : Type} {f : List A → List B}, IsSST f → IsSST (fun w => p (f w)) := by
  induction hp with
  | base h => exact fun hf => isSST_comp_primeRational h hf
  | id B => exact fun hf => hf
  | comp _ _ ih₁ ih₂ => exact fun hf => ih₂ (ih₁ hf)

/-- **sst's are closed under post-composition with a rational function.** -/
theorem isSST_comp_rational [Finite B] [Finite C] {p : List B → List C}
    (hp : IsRationalFun p) {f : List A → List B} (hf : IsSST f) :
    IsSST (fun w => p (f w)) :=
  isSST_comp_compClosureRational ((rational_iff_prime_composition p).1 hp) hf

end Lax916827Proofs.Transducers
