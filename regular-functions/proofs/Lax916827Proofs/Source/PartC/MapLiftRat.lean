/- The map lifting of a rational function is rational.  This is the first step of the proof of the
first item of Lemma `lem:regular-closure-properties` of *Transducers* (M. Bojańczyk).

If `f` is computed by a bimachine `M`, then `mapLift f` is computed by the
bimachine which resets the prefix automaton of `M` at every separator, resets
the suffix automaton of `M` at every separator (which happens automatically,
since the suffix automaton is run on the reverse of the suffix), remembers in
the suffix automaton the letter that follows the current gap, and outputs the
block produced by `M`, followed by a separator when the next letter is a
separator.
-/
import Lax916827Proofs.Source.PartC.RatBuild
import Lax916827Proofs.Source.PartC.MapLiftAux
import Lax132576Proofs.Source.PartB.RatBimach
import Lax916827Proofs.Source.PartC.ContAux
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace MapLiftBim

variable {A B P S : Type}

/-- The bimachine computing the map lifting of the function computed by `M`. -/
def lift (M : Bimachine A B P S) : Bimachine (Option A) (Option B) P (S × Option (Option A)) where
  prefixInit := M.prefixInit
  prefixStep := fun p x => match x with
    | none => M.prefixInit
    | some a => M.prefixStep p a
  suffixInit := (M.suffixInit, none)
  suffixStep := fun s x =>
    ((match x with | none => M.suffixInit | some a => M.suffixStep s.1 a), some x)
  out := fun p s =>
    (M.out p s.1).map some ++ (match s.2 with | some none => [none] | _ => [])

/-- On a block, the suffix automaton of the lifted bimachine simulates the
suffix automaton of `M`. -/
lemma bmSfx_lift_map_some (M : Bimachine A B P S) (b : List A) :
    (bmSfx (lift M) (b.map some)).1 = bmSfx M b := by
  induction b with
  | nil => rfl
  | cons a b ih =>
      rw [List.map_cons, bmSfx_cons, bmSfx_cons]
      show (match (some a : Option A) with
        | none => M.suffixInit | some a => M.suffixStep (bmSfx (lift M) (b.map some)).1 a)
        = M.suffixStep (bmSfx M b) a
      rw [ih]

/-- The same, for a block that is followed by a separator. -/
lemma bmSfx_lift_map_some_cons_none (M : Bimachine A B P S) (b : List A)
    (w : List (Option A)) :
    (bmSfx (lift M) (b.map some ++ none :: w)).1 = bmSfx M b := by
  induction b with
  | nil => rw [List.map_nil, List.nil_append, bmSfx_cons]; rfl
  | cons a b ih =>
      rw [List.map_cons, List.cons_append, bmSfx_cons, bmSfx_cons]
      show (match (some a : Option A) with
        | none => M.suffixInit
        | some a => M.suffixStep (bmSfx (lift M) (b.map some ++ none :: w)).1 a)
        = M.suffixStep (bmSfx M b) a
      rw [ih]

/-- The output of the lifted bimachine on a string without separators. -/
lemma lift_evalFrom_map_some (M : Bimachine A B P S) (b : List A) (p : P) :
    (lift M).evalFrom p (b.map some) = (M.evalFrom p b).map some := by
  induction b generalizing p with
  | nil => simp [lift]
  | cons a b ih =>
      rw [List.map_cons, Bimachine.evalFrom_cons', Bimachine.evalFrom_cons']
      have hs : bmSfx (lift M) (some a :: b.map some)
          = (M.suffixStep (bmSfx M b) a, some (some a)) := by
        rw [bmSfx_cons]
        refine Prod.ext ?_ rfl
        show (match (some a : Option A) with
          | none => M.suffixInit
          | some a => M.suffixStep (bmSfx (lift M) (b.map some)).1 a)
          = M.suffixStep (bmSfx M b) a
        rw [bmSfx_lift_map_some]
      rw [hs, bmSfx_cons]
      show (M.out p (M.suffixStep (bmSfx M b) a)).map some ++ [] ++
        (lift M).evalFrom (M.prefixStep p a) (b.map some) = _
      rw [ih]
      simp

/-- The output of the lifted bimachine on a string whose first separator is
explicit. -/
lemma lift_evalFrom_map_some_cons_none (M : Bimachine A B P S) (b : List A)
    (w : List (Option A)) (p : P) :
    (lift M).evalFrom p (b.map some ++ none :: w)
      = (M.evalFrom p b).map some ++ none :: (lift M).evalFrom M.prefixInit w := by
  induction b generalizing p with
  | nil =>
      rw [List.map_nil, List.nil_append, Bimachine.evalFrom_cons']
      have hs : bmSfx (lift M) (none :: w) = (M.suffixInit, some none) := by
        rw [bmSfx_cons]; rfl
      rw [hs]
      show (M.out p M.suffixInit).map some ++ [none] ++ (lift M).evalFrom M.prefixInit w = _
      simp
  | cons a b ih =>
      rw [List.map_cons, List.cons_append, Bimachine.evalFrom_cons',
        Bimachine.evalFrom_cons']
      have hs : bmSfx (lift M) (some a :: (b.map some ++ none :: w))
          = (M.suffixStep (bmSfx M b) a, some (some a)) := by
        rw [bmSfx_cons]
        refine Prod.ext ?_ rfl
        show (match (some a : Option A) with
          | none => M.suffixInit
          | some a => M.suffixStep (bmSfx (lift M) (b.map some ++ none :: w)).1 a)
          = M.suffixStep (bmSfx M b) a
        rw [bmSfx_lift_map_some_cons_none]
      rw [hs, bmSfx_cons]
      show (M.out p (M.suffixStep (bmSfx M b) a)).map some ++ [] ++
        (lift M).evalFrom (M.prefixStep p a) (b.map some ++ none :: w) = _
      rw [ih]
      simp

/-- The lifted bimachine computes the map lifting. -/
lemma lift_eval (M : Bimachine A B P S) (w : List (Option A)) :
    (lift M).eval w = mapLift M.eval w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
      subst hn
      rcases sep_decomp w with ⟨b, rfl⟩ | ⟨b, w', rfl, hlen⟩
      · rw [Bimachine.eval_eq_evalFrom,
          show ((lift M).prefixInit) = M.prefixInit from rfl,
          lift_evalFrom_map_some, mapLift_map_some]
        rfl
      · rw [Bimachine.eval_eq_evalFrom,
          show ((lift M).prefixInit) = M.prefixInit from rfl,
          lift_evalFrom_map_some_cons_none, mapLift_map_some_cons_none,
          show (lift M).evalFrom M.prefixInit w' = (lift M).eval w' from rfl,
          ih w'.length hlen w' rfl]
        rfl

end MapLiftBim

/-- The map lifting of a rational function is rational. -/
theorem isRationalFun_mapLift {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : IsRationalFun (mapLift f) := by
  obtain ⟨P, S, hP, hS, M, hM⟩ := isBimachine_of_rationalFun hf
  haveI := hP; haveI := hS
  refine isRationalFun_of_bimachine (MapLiftBim.lift M) (fun w => ?_)
  rw [MapLiftBim.lift_eval, hM]

end Lax916827Proofs.Transducers
