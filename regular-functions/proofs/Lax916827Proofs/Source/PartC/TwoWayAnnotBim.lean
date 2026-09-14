/-
The annotation of `TwoWayAnnot.lean` is computed by a bimachine, and is
therefore a rational function (Theorem `thm:bimachines`).  The prefix automaton is the
automaton `D` itself; the suffix automaton computes, for the suffix that is
still to be read, the acceptance function `s ↦ (D accepts the suffix from s)`,
together with the two letters that the output function needs.
-/
import Lax916827Proofs.Source.PartC.TwoWayAnnot
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open scoped Classical

variable {A Q S : Type} (D : DFA (Marked A Q) S)

/-! ## The bimachine computing the annotation -/

/-- The bimachine computing the annotation. -/
noncomputable def annBimach (D : DFA (Marked A Q) S) :
    Bimachine A (AnnLet A S) (S × Option A) ((S → Bool) × (S → Bool) × Option A × Option A) where
  prefixInit := (D.start, none)
  prefixStep := fun p a => (D.step p.1 (a, none), some a)
  suffixInit := ((fun s => decide (s ∈ D.accept)), (fun _ => false), none, none)
  suffixStep := fun s a => ((fun t => s.1 (D.step t (a, none))), s.1, some a, s.2.2.1)
  out := fun p s =>
    match s.2.2.1 with
    | none => []
    | some a => [((p.2, a, s.2.2.2), p.1, s.2.1)]

/-- The state of the suffix automaton of `annBimach D` on the suffix `v`. -/
noncomputable def annSfx (D : DFA (Marked A Q) S) (v : List A) :
    (S → Bool) × (S → Bool) × Option A × Option A :=
  strTrans (annBimach D).suffixStep v.reverse (annBimach D).suffixInit

lemma annSfx_nil : annSfx D ([] : List A) = (annBimach D).suffixInit := rfl

lemma annSfx_cons (a : A) (v : List A) :
    annSfx D (a :: v) = (annBimach D).suffixStep (annSfx D v) a := by
  rw [annSfx, annSfx, List.reverse_cons]
  simp [strTrans]

lemma annSfx_fst (v : List A) : (annSfx D v).1 = rhoOf D v := by
  induction v with
  | nil => rfl
  | cons a rest ih =>
      rw [annSfx_cons]
      show (fun t => (annSfx D rest).1 (D.step t (a, none))) = rhoOf D (a :: rest)
      rw [ih]
      funext t
      rw [rhoOf_cons]

lemma annSfx_head (v : List A) : (annSfx D v).2.2.1 = v.head? := by
  cases v with
  | nil => rfl
  | cons a rest => rw [annSfx_cons]; rfl

lemma annSfx_cons_snd (a : A) (v : List A) : (annSfx D (a :: v)).2.1 = rhoOf D v := by
  rw [annSfx_cons]
  show (annSfx D v).1 = rhoOf D v
  exact annSfx_fst D v

lemma annSfx_cons_next (a : A) (v : List A) : (annSfx D (a :: v)).2.2.2 = v.head? := by
  rw [annSfx_cons]
  show (annSfx D v).2.2.1 = v.head?
  exact annSfx_head D v

lemma annBimach_evalFrom (p : S × Option A) (w : List A) :
    (annBimach D).evalFrom p w = annotFrom D p.1 p.2 w := by
  induction w generalizing p with
  | nil =>
      rw [Bimachine.evalFrom_nil]
      rfl
  | cons a rest ih =>
      rw [Bimachine.evalFrom_cons, ih]
      have hout : (annBimach D).out p (annSfx D (a :: rest))
          = [((p.2, a, rest.head?), p.1, rhoOf D rest)] := by
        show (match (annSfx D (a :: rest)).2.2.1 with
              | none => []
              | some b => [((p.2, b, (annSfx D (a :: rest)).2.2.2), p.1,
                  (annSfx D (a :: rest)).2.1)]) = _
        rw [annSfx_head, annSfx_cons_next, annSfx_cons_snd]
        rfl
      rw [show strTrans (annBimach D).suffixStep (a :: rest).reverse (annBimach D).suffixInit
            = annSfx D (a :: rest) from rfl, hout]
      rfl

theorem annBimach_eval (w : List A) : (annBimach D).eval w = annot D w :=
  annBimach_evalFrom D _ w

/-- The annotation is a rational function. -/
theorem isRationalFun_annot [Finite A] [Finite S] : IsRationalFun (annot D) := by
  refine rationalFun_of_isBimachine ⟨S × Option A, (S → Bool) × (S → Bool) × Option A × Option A,
    inferInstance, inferInstance, annBimach D, ?_⟩
  funext w
  exact annBimach_eval D w

end TwoWay

end Lax916827Proofs.Transducers
