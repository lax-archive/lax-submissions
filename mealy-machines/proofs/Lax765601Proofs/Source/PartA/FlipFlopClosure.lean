/-
Closure properties of compositions of flip-flop Mealy machines.

These are the analogues, for the family `FlipFlopFam`, of the closure properties
of `PrimeMealyFam` proved in `RequestProject/PartA/PrimeClosure.lean` and
`RequestProject/PartA/MapLift.lean`.  They are what is needed to run the Krohn-Rhodes
construction of Lemma `lem:Mealy-map-lifting` inside the class of flip-flop machines, which is the
missing implication of Theorem `thm:aperiodic-mealy` of *Transducers* (M. Bojańczyk).
-/
import Lax765601Proofs.Source.PartA.MapLift

namespace Lax765601Proofs.Transducers

variable {A B C D P Q : Type}

/-- A letter-to-letter homomorphism is a flip-flop machine. -/
lemma flipFlop_map (h : A → B) : FlipFlopFam A B (List.map h) :=
  ⟨Unit, inferInstance, homMealy h, homMealy_eval h, homMealy_flipFlop h⟩

/-- Pairing the output with the input preserves being a flip-flop. -/
lemma flipFlop_zipInput {f : List A → List B} (h : FlipFlopFam A B f) :
    FlipFlopFam A (A × B) (zipInput f) := by
  obtain ⟨Q, hQ, M, hM, hr⟩ := h
  exact ⟨Q, hQ, M.withInput, by rw [M.withInput_eval, hM], M.withInput_flipFlop hr⟩

/-- Acting on the second component preserves being a flip-flop. -/
lemma flipFlop_liftSnd {g : List B → List C} (h : FlipFlopFam B C g) :
    FlipFlopFam (A × B) (A × C) (liftSndFun A g) := by
  obtain ⟨P, hP, N, hN, hr⟩ := h
  exact ⟨P, hP, N.liftSnd A, by rw [N.liftSnd_eval, hN], N.liftSnd_flipFlop hr⟩

/-- Every composition of flip-flop Mealy machines is letter-to-letter. -/
lemma lengthPreserving_of_compClosure_flipFlop {f : List A → List B}
    (h : CompClosure FlipFlopFam A B f) : LengthPreserving f := by
  induction h with
  | base hf =>
      obtain ⟨Q, hQ, M, hM, _⟩ := hf
      exact fun w => by rw [← hM]; simp
  | id A => exact fun _ => rfl
  | comp _ _ ihf ihg => exact fun w => by rw [Function.comp_apply, ihg, ihf]

/-- Every composition of flip-flop Mealy machines produces one output letter per
input letter. -/
lemma oneStep_of_compClosure_flipFlop {f : List A → List B}
    (h : CompClosure FlipFlopFam A B f) : OneStep f := by
  induction h with
  | base hf =>
      obtain ⟨Q, hQ, M, hM, _⟩ := hf
      exact hM ▸ M.oneStep
  | id A => exact oneStep_id
  | comp _ _ ihf ihg => exact ihf.comp ihg

/-- Acting on the second component preserves decompositions into flip-flops. -/
lemma compClosure_liftSnd_flipFlop [Finite A] {g : List B → List C}
    (h : CompClosure FlipFlopFam B C g) :
    CompClosure FlipFlopFam (A × B) (A × C) (liftSndFun A g) := by
  induction h with
  | base hg => exact CompClosure.base (flipFlop_liftSnd hg)
  | id B =>
      have hid : liftSndFun A (id : List B → List B) = id := by
        funext w
        show (w.map Prod.fst).zip (w.map Prod.snd) = w
        induction w with
        | nil => rfl
        | cons ab w ih => simpa using ih
      rw [hid]
      exact CompClosure.id _
  | @comp B₁ B₂ B₃ hfin g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      haveI : Finite (A × B₂) := inferInstance
      rw [liftSndFun_comp (lengthPreserving_of_compClosure_flipFlop hg₁)]
      exact CompClosure.comp ih₁ ih₂

/-- Pairing the output with the input preserves decompositions into
flip-flops. -/
lemma compClosure_zipInput_flipFlop {A B : Type} {f : List A → List B} (hA : Finite A)
    (h : CompClosure FlipFlopFam A B f) :
    CompClosure FlipFlopFam A (A × B) (zipInput f) := by
  revert hA
  induction h with
  | base hf => exact fun _ => CompClosure.base (flipFlop_zipInput hf)
  | id A =>
      intro _
      have hid : zipInput (id : List A → List A) = List.map (fun a => (a, a)) := by
        funext w
        show w.zip w = _
        induction w with
        | nil => rfl
        | cons a w ih => simpa using ih
      rw [hid]
      exact CompClosure.base (flipFlop_map _)
  | @comp A₁ B₁ C₁ hfin f₁ g₁ hf₁ hg₁ ih₁ _ =>
      intro hA₁
      haveI := hA₁
      haveI : Finite (A₁ × B₁) := inferInstance
      rw [zipInput_comp (lengthPreserving_of_compClosure_flipFlop hf₁)]
      exact CompClosure.comp (ih₁ hA₁) (compClosure_liftSnd_flipFlop hg₁)

/-- The map lifting of a decomposition into flip-flops is a decomposition into flip-flops.  This is
the flip-flop version of Lemma `lem:map-lifting-decomposition-mealy`; here it is even simpler, since
the map lifting of a single flip-flop machine is again a single flip-flop machine. -/
theorem mapLift_compClosure_flipFlop {A B : Type} {f : List A → List B} (hA : Finite A)
    (hf : CompClosure FlipFlopFam A B f) :
    CompClosure FlipFlopFam (Option A) (Option B) (mapLift f) := by
  revert hA
  induction hf with
  | base hp => exact fun _ => CompClosure.base (mapLift_flipFlop hp)
  | id A =>
      intro _
      rw [mapLift_id]
      exact CompClosure.id _
  | @comp A₁ B₁ C₁ hfin f₁ g₁ hf₁ hg₁ ihf ihg =>
      intro hA₁
      haveI := hA₁
      haveI : Finite (Option B₁) := inferInstance
      rw [mapLift_comp (oneStep_of_compClosure_flipFlop hf₁)
        (oneStep_of_compClosure_flipFlop hg₁)]
      exact CompClosure.comp (ihf hA₁) (ihg hfin)

end Lax765601Proofs.Transducers