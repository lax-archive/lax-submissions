/-
Part D: the enumeration of the tuples of positions is a polyregular function.

The transducer of one step is a streaming string transducer, hence computes a regular function
(Theorem `theorem:sst-two-way-equivalence`), and marked squaring is a prime polyregular function.
Since the enumeration of a nest of `k+1` loops is obtained from the enumeration of the first `k`
loops by marked squaring followed by that transducer
(`Transducers.PolyEnum.stepFun_enum`), an induction on the list of loops shows that the
enumeration is polyregular.
-/
import Lax194892Proofs.Source.PartD.PolyStepTop
import Lax194892Proofs.Source.PartD.PolyDef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PolyEnum

variable {A : Type}

/-! ## The transducer of one step computes a regular function -/

instance : Finite BS := by
  have h : Function.Injective (fun q : BS =>
      match q with
      | BS.empty => (0 : Fin 4)
      | BS.allL => 1
      | BS.trans => 2
      | BS.allR => 3) := by
    intro q q' h
    cases q <;> cases q' <;> simp_all
  exact Finite.of_injective _ h

/-- The transducer of one step is a streaming string transducer. -/
lemma isSST_stepFun (d : Bool) (A : Type) (k : ℕ) : IsSST (stepFun d A k) :=
  ⟨BS, Reg, inferInstance, inferInstance, stepSST d A k, rfl⟩

/-- The transducer of one step computes a regular function. -/
lemma isRegularFun_stepFun [Finite A] (d : Bool) (k : ℕ) :
    IsRegularFun (stepFun d A k) :=
  (sst_iff_regular _).mp (isSST_stepFun d A k)

/-- The transducer of one step computes a polyregular function. -/
lemma isPolyregular_stepFun [Finite A] (d : Bool) (k : ℕ) :
    IsPolyregular (stepFun d A k) :=
  IsPolyregular.of_regular (isRegularFun_stepFun d k)

/-! ## The enumeration of the tuples of no loop at all -/

lemma blockFrom_zero_eq_map (t : List ℕ) (e : Fin 0 → Bool) :
    ∀ (i : ℕ) (w : List A), blockFrom 0 t i w = w.map (fun a => Ann.letter a e) := by
  intro i w
  induction w generalizing i with
  | nil => rfl
  | cons a w ih =>
      have he : annOf 0 t i = e := by funext j; exact absurd j.2 (by omega)
      simp [blockFrom_cons, he, ih]

lemma enum_nil_eq [Finite A] (e : Fin 0 → Bool) (w : List A) :
    enum 0 [] w = w.map (fun a => Ann.letter a e) ++ [Ann.sep, Ann.eos] := by
  simp only [enum, tuplesOf_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    blockAt, blockFrom_zero_eq_map (A := A) [] e 0 w]
  simp

/-- The enumeration of the tuples of the empty nest of loops -- one annotated copy of the input,
followed by the separator and the end marker -- is a regular function. -/
lemma isRegularFun_enum_nil [Finite A] : IsRegularFun (fun w : List A => enum 0 [] w) := by
  classical
  have h : IsRegularFun (fun w : List A =>
      w.map (fun a => Ann.letter a (fun j : Fin 0 => j.elim0))
        ++ ([Ann.sep, Ann.eos] : List (Ann A 0))) :=
    isRegularFun_concat (isRegularFun_map _)
      (IsRegularFun.of_rational (isRationalFun_const _))
  exact h.congr (fun w => (enum_nil_eq (fun j : Fin 0 => j.elim0) w).symm)

/-! ## The enumeration is polyregular -/

/-- **The enumeration of the tuples of positions visited by a nest of loops is polyregular.** -/
theorem isPolyregular_enum [Finite A] :
    ∀ (L : List (Bool × ℕ)) (k : ℕ) (_ : L.length = k),
      IsPolyregular (fun w : List A => enum k L w) := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
      intro k hk
      subst hk
      exact IsPolyregular.of_regular isRegularFun_enum_nil
  | append_singleton L a ih =>
      obtain ⟨d, x⟩ := a
      intro k hk
      have hk' : k = L.length + 1 := by simpa using hk.symm
      subst hk'
      haveI : Finite (Ann A L.length) := inferInstance
      refine IsPolyregular.comp' (g := stepFun d A L.length)
        ((ih L.length rfl).comp' (isPolyregular_markedSquare (Ann A L.length))
          (fun w => rfl))
        (isPolyregular_stepFun d L.length) (fun w => ?_)
      exact (stepFun_enum d x L w).symm

end PolyEnum

end Lax194892Proofs.Transducers
