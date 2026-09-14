/-
Part D: a for-transducer computes a polyregular function.

This is the right-to-left inclusion of Theorem `thm:for-transducers-are-polyregular`.  By Lemma
`lemma:prenex-normal-form` every for-transducer is equivalent to one in prenex form, a nest of
loops with a loop-free body followed by a loop-free epilogue.  Such a program is the composition
of two functions:

* the enumeration of the tuples of positions visited by the nest -- one annotated copy of the
  input per tuple -- which is polyregular (`Transducers.PolyEnum.isPolyregular_enum`);
* the scan of that enumeration, which runs the body once per copy and the epilogue at the end,
  and which is computed by a streaming string transducer, hence is a regular function
  (`Transducers.PolyEnum.scan_enum`).
-/
import Lax194892Proofs.Source.PartD.PolyScan
import Lax194892Proofs.Source.PartD.ForPrenexTop
import Lax194892Proofs.Source.PartD.ForPolyreg
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PolyEnum

open scoped Classical

variable {A B : Type}

/-! ## The scan of the enumeration is a regular function -/

/-- The scanning machine is a streaming string transducer. -/
lemma isSST_scanFun [Finite A] (k m : ℕ) (body epilogue : ForProg A B)
    (vf : ℕ → Fin (k + 1)) : IsSST (scanFun k m body epilogue vf) :=
  ⟨ScanSt A k m, Unit, inferInstance, inferInstance, scanSST k m body epilogue vf, rfl⟩

/-- The scan of the enumeration is a regular function. -/
lemma isRegularFun_scanFun [Finite A] [Finite B] (k m : ℕ) (body epilogue : ForProg A B)
    (vf : ℕ → Fin (k + 1)) : IsRegularFun (scanFun k m body epilogue vf) :=
  (sst_iff_regular _).mp (isSST_scanFun k m body epilogue vf)

/-- The scan of the enumeration is polyregular. -/
lemma isPolyregular_scanFun [Finite A] [Finite B] (k m : ℕ) (body epilogue : ForProg A B)
    (vf : ℕ → Fin (k + 1)) : IsPolyregular (scanFun k m body epilogue vf) :=
  IsPolyregular.of_regular (isRegularFun_scanFun k m body epilogue vf)

/-! ## A program in prenex form computes a polyregular function -/

/-- **A for-transducer in prenex form computes a polyregular function.** -/
theorem isPolyregular_of_prenex [Finite A] [Finite B] {P : ForProg A B} (hP : P.PrenexForm) :
    IsPolyregular P.eval := by
  classical
  obtain ⟨L, body, epilogue, hbody, hepi, -, rfl⟩ := hP
  set k := L.length with hk
  set m := maxList body.boolVars + 1 with hm
  have hmlt : ∀ i ∈ body.boolVars, i < m := by
    intro i hi
    have := le_maxList body.boolVars i hi
    omega
  refine IsPolyregular.comp' (g := scanFun k m body epilogue
      (fun i => ⟨virt L i, Nat.lt_succ_of_le (virt_le L i)⟩))
    (isPolyregular_enum L k hk.symm) (isPolyregular_scanFun _ _ _ _ _) (fun w => ?_)
  exact (scan_enum k m body epilogue _ hk.symm hbody hepi (fun _ => rfl) hmlt w).symm

/-- **Every function computed by a for-transducer is polyregular.** -/
theorem isPolyregular_of_isForTransducer [Finite A] [Finite B] {f : List A → List B}
    (hf : IsForTransducer f) : IsPolyregular f := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨P', hpre, hval⟩ := forTransducer_prenex_aux P
  exact (isPolyregular_of_prenex hpre).congr (fun w => by rw [hval w, hP w])

end PolyEnum

end Lax194892Proofs.Transducers
