/-
Closure properties of compositions of prime Mealy machines, used in the proof of
the Krohn-Rhodes Theorem (Theorem `thm:krohn-rhodes`) of *Transducers*
(M. Bojańczyk, June 25, 2026).

The book uses freely the fact that "a prime Mealy machine can always be adapted
so that it includes a copy of the input string in its output".  This file makes
that precise: prime machines are stable under pairing the output with the input
letter, and under acting on the second component of a product alphabet, and
therefore so are compositions of prime machines.
-/
import Lax765601Proofs.Source.PartA.MealyBasic

namespace Lax765601Proofs.Transducers

variable {A B C D Q P : Type}

/-! ## Letter-to-letter homomorphisms -/

/-- The one-state Mealy machine of a letter-to-letter homomorphism. -/
def homMealy (h : A → B) : Mealy A B Unit where
  init := ()
  step := fun _ a => ((), h a)

@[simp] lemma homMealy_eval (h : A → B) : (homMealy h).eval = List.map h := by
  funext w
  show (homMealy h).run () w = _
  induction w with
  | nil => rfl
  | cons a w ih => simpa [homMealy] using ih

lemma homMealy_flipFlop (h : A → B) : (homMealy h).FlipFlop :=
  fun _ => Or.inr ⟨(), fun _ => rfl⟩

/-- A letter-to-letter homomorphism is a prime Mealy machine. -/
lemma prime_map (h : A → B) : PrimeMealyFam A B (List.map h) :=
  Or.inr ⟨Unit, inferInstance, homMealy h, homMealy_eval h, homMealy_flipFlop h⟩

/-! ## Pairing the output with the input -/

/-- The function that pairs every input letter with the corresponding output
letter of `f`. -/
def zipInput (f : List A → List B) (w : List A) : List (A × B) := w.zip (f w)

/-- The Mealy machine that pairs every input letter with the corresponding
output letter. -/
def Mealy.withInput (M : Mealy A B Q) : Mealy A (A × B) Q where
  init := M.init
  step := fun q a => ((M.step q a).1, (a, (M.step q a).2))

@[simp] lemma Mealy.withInput_letterTrans (M : Mealy A B Q) (a : A) :
    M.withInput.letterTrans a = M.letterTrans a := rfl

lemma Mealy.withInput_run (M : Mealy A B Q) (q : Q) (w : List A) :
    M.withInput.run q w = w.zip (M.run q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => simpa [Mealy.withInput] using ih _

lemma Mealy.withInput_eval (M : Mealy A B Q) : M.withInput.eval = zipInput M.eval := by
  funext w
  exact M.withInput_run M.init w

lemma Mealy.withInput_reversible (M : Mealy A B Q) (h : M.Reversible) :
    M.withInput.Reversible := h

lemma Mealy.withInput_flipFlop (M : Mealy A B Q) (h : M.FlipFlop) :
    M.withInput.FlipFlop := h

/-- Pairing the output with the input preserves primality. -/
lemma prime_zipInput {f : List A → List B} (h : PrimeMealyFam A B f) :
    PrimeMealyFam A (A × B) (zipInput f) := by
  rcases h with ⟨Q, hQ, M, hM, hr⟩ | ⟨Q, hQ, M, hM, hr⟩
  · exact Or.inl ⟨Q, hQ, M.withInput, by rw [M.withInput_eval, hM], M.withInput_reversible hr⟩
  · exact Or.inr ⟨Q, hQ, M.withInput, by rw [M.withInput_eval, hM], M.withInput_flipFlop hr⟩

/-! ## Acting on the second component -/

/-- The function that applies `g` to the second components of the input
letters, leaving the first components unchanged. -/
def liftSndFun (A : Type) (g : List B → List C) (w : List (A × B)) : List (A × C) :=
  (w.map Prod.fst).zip (g (w.map Prod.snd))

/-- The Mealy machine that runs `N` on the second components of the input
letters, leaving the first components unchanged. -/
def Mealy.liftSnd (A : Type) (N : Mealy B C P) : Mealy (A × B) (A × C) P where
  init := N.init
  step := fun p ab => ((N.step p ab.2).1, (ab.1, (N.step p ab.2).2))

lemma Mealy.liftSnd_run (N : Mealy B C P) (p : P) (w : List (A × B)) :
    (N.liftSnd A).run p w = (w.map Prod.fst).zip (N.run p (w.map Prod.snd)) := by
  induction w generalizing p with
  | nil => rfl
  | cons ab w ih => simpa [Mealy.liftSnd] using ih _

lemma Mealy.liftSnd_eval (N : Mealy B C P) :
    (N.liftSnd A).eval = liftSndFun A N.eval := by
  funext w
  exact N.liftSnd_run N.init w

lemma Mealy.liftSnd_reversible (N : Mealy B C P) (h : N.Reversible) :
    (N.liftSnd A).Reversible := fun ab => h ab.2

lemma Mealy.liftSnd_flipFlop (N : Mealy B C P) (h : N.FlipFlop) :
    (N.liftSnd A).FlipFlop := fun ab => h ab.2

/-- Acting on the second component preserves primality. -/
lemma prime_liftSnd {g : List B → List C} (h : PrimeMealyFam B C g) :
    PrimeMealyFam (A × B) (A × C) (liftSndFun A g) := by
  rcases h with ⟨P, hP, N, hN, hr⟩ | ⟨P, hP, N, hN, hr⟩
  · exact Or.inl ⟨P, hP, N.liftSnd A, by rw [N.liftSnd_eval, hN], N.liftSnd_reversible hr⟩
  · exact Or.inr ⟨P, hP, N.liftSnd A, by rw [N.liftSnd_eval, hN], N.liftSnd_flipFlop hr⟩

/-! ## Compositions -/

/-- Every composition of prime Mealy machines is letter-to-letter. -/
lemma lengthPreserving_of_compClosure {f : List A → List B}
    (h : CompClosure PrimeMealyFam A B f) : LengthPreserving f := by
  induction h with
  | base hf =>
      rcases hf with ⟨Q, hQ, M, hM, _⟩ | ⟨Q, hQ, M, hM, _⟩ <;>
        exact fun w => by rw [← hM]; simp
  | id A => exact fun w => rfl
  | comp _ _ ihf ihg => exact fun w => by rw [Function.comp_apply, ihg, ihf]

/-- `liftSndFun` commutes with composition, for letter-to-letter functions. -/
lemma liftSndFun_comp {g₁ : List B → List C} {g₂ : List C → List D}
    (h : LengthPreserving g₁) :
    liftSndFun A (g₂ ∘ g₁) = liftSndFun A g₂ ∘ liftSndFun A g₁ := by
  funext w
  have hlen : (g₁ (w.map Prod.snd)).length = (w.map Prod.fst).length := by
    rw [h (w.map Prod.snd)]
    simp
  show (w.map Prod.fst).zip (g₂ (g₁ (w.map Prod.snd)))
      = ((liftSndFun A g₁ w).map Prod.fst).zip (g₂ ((liftSndFun A g₁ w).map Prod.snd))
  rw [liftSndFun, List.map_fst_zip (le_of_eq hlen.symm), List.map_snd_zip (le_of_eq hlen)]

/-- `zipInput` of a composition, for letter-to-letter functions. -/
lemma zipInput_comp {f : List A → List B} {g : List B → List C}
    (h : LengthPreserving f) :
    zipInput (g ∘ f) = liftSndFun A g ∘ zipInput f := by
  funext w
  have hlen : (f w).length = w.length := h w
  show w.zip (g (f w)) = ((zipInput f w).map Prod.fst).zip (g ((zipInput f w).map Prod.snd))
  rw [zipInput, List.map_fst_zip (le_of_eq hlen.symm), List.map_snd_zip (le_of_eq hlen)]

/-- Acting on the second component preserves decompositions into primes. -/
lemma compClosure_liftSnd [Finite A] {g : List B → List C}
    (h : CompClosure PrimeMealyFam B C g) :
    CompClosure PrimeMealyFam (A × B) (A × C) (liftSndFun A g) := by
  induction h with
  | base hg => exact CompClosure.base (prime_liftSnd hg)
  | id B =>
      have : liftSndFun A (id : List B → List B) = id := by
        funext w
        show (w.map Prod.fst).zip (w.map Prod.snd) = w
        induction w with
        | nil => rfl
        | cons ab w ih => simpa using ih
      rw [this]
      exact CompClosure.id _
  | @comp B₁ B₂ B₃ hfin g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      haveI : Finite (A × B₂) := inferInstance
      rw [liftSndFun_comp (lengthPreserving_of_compClosure hg₁)]
      exact CompClosure.comp ih₁ ih₂

/-- Pairing the output with the input preserves decompositions into primes. -/
lemma compClosure_zipInput {A B : Type} {f : List A → List B} (hA : Finite A)
    (h : CompClosure PrimeMealyFam A B f) :
    CompClosure PrimeMealyFam A (A × B) (zipInput f) := by
  revert hA
  induction h with
  | base hf => exact fun _ => CompClosure.base (prime_zipInput hf)
  | id A =>
      intro _
      have hid : zipInput (id : List A → List A) = List.map (fun a => (a, a)) := by
        funext w
        show w.zip w = _
        induction w with
        | nil => rfl
        | cons a w ih => simpa using ih
      rw [hid]
      exact CompClosure.base (prime_map _)
  | @comp A₁ B₁ C₁ hfin f₁ g₁ hf₁ hg₁ ih₁ _ =>
      intro hA₁
      haveI := hA₁
      haveI : Finite (A₁ × B₁) := inferInstance
      rw [zipInput_comp (lengthPreserving_of_compClosure hf₁)]
      exact CompClosure.comp (ih₁ hA₁) (compClosure_liftSnd hg₁)

end Lax765601Proofs.Transducers