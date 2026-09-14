/- The equivalence relation of Theorem `thm:machine-independent-rational-functions` and the easy
implication of that theorem: a rational function is continuous and the relation has finite index.

Two input strings are equivalent when the left distances of the outputs of their
common extensions on the left are bounded (`BoundedVarRel`).  This is an
equivalence relation, because the left distance is a metric, and it is a *left*
congruence.

For a rational function, presented as a bimachine by Theorem `thm:bimachines`, two strings
that give the same state of the suffix automaton are equivalent: the output of
the bimachine on `w w₁` splits as the part produced at the positions of `w`,
which only depends on `w` and on the state of the suffix automaton after `w₁`,
followed by a part of bounded length.  Hence the relation has finite index.
-/
import Lax132576Proofs.Source.PartB.Lcp
import Lax132576Proofs.Source.PartB.RatBimach
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-- The equivalence relation on input strings used in Theorem
`thm:machine-independent-rational-functions`: `w₁ ∼ w₂` if the left distances `‖f (w w₁), f (w w₂)‖`
are bounded uniformly in `w`. -/
def BoundedVarRel {A B : Type} (f : List A → List B) (w₁ w₂ : List A) : Prop :=
  ∃ K : ℕ, ∀ w : List A, leftDist (f (w ++ w₁)) (f (w ++ w₂)) ≤ K

namespace BoundedVarRel

variable {A B : Type} {f : List A → List B}

lemma refl (w : List A) : BoundedVarRel f w w :=
  ⟨0, fun v => by simp [leftDist_self]⟩

lemma symm {w₁ w₂ : List A} (h : BoundedVarRel f w₁ w₂) : BoundedVarRel f w₂ w₁ := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun w => by rw [leftDist_comm]; exact hK w⟩

lemma trans {w₁ w₂ w₃ : List A} (h₁ : BoundedVarRel f w₁ w₂) (h₂ : BoundedVarRel f w₂ w₃) :
    BoundedVarRel f w₁ w₃ := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  refine ⟨K₁ + K₂, fun w => ?_⟩
  exact le_trans (leftDist_triangle _ (f (w ++ w₂)) _) (Nat.add_le_add (hK₁ w) (hK₂ w))

/-- The relation is a left congruence: prepending a letter only shrinks the
range of the supremum. -/
lemma cons {w₁ w₂ : List A} (h : BoundedVarRel f w₁ w₂) (a : A) :
    BoundedVarRel f (a :: w₁) (a :: w₂) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun w => ?_⟩
  have h1 : w ++ a :: w₁ = (w ++ [a]) ++ w₁ := by simp
  have h2 : w ++ a :: w₂ = (w ++ [a]) ++ w₂ := by simp
  rw [h1, h2]
  exact hK _

/-- The relation is a left congruence. -/
lemma append_left {w₁ w₂ : List A} (h : BoundedVarRel f w₁ w₂) (u : List A) :
    BoundedVarRel f (u ++ w₁) (u ++ w₂) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun w => ?_⟩
  rw [← List.append_assoc, ← List.append_assoc]
  exact hK _

end BoundedVarRel

namespace BimachIndex

variable {A B P S : Type}

lemma strTrans_append {Q : Type} (δ : Q → A → Q) (x y : List A) (q : Q) :
    strTrans δ (x ++ y) q = strTrans δ y (strTrans δ x q) := by
  simp [strTrans]

/-- The state of the suffix automaton of a bimachine on a string. -/
def sfx (M : Bimachine A B P S) (w : List A) : S :=
  strTrans M.suffixStep w.reverse M.suffixInit

/-- The output that a bimachine produces at the positions of `u`, when the
suffix automaton is in the state `s` after the part of the input that follows
`u`. -/
def bmPref (M : Bimachine A B P S) : P → List A → S → List B
  | _, [], _ => []
  | p, a :: u, s =>
    M.out p (strTrans M.suffixStep (a :: u).reverse s) ++ bmPref M (M.prefixStep p a) u s

/-- Splitting the output of a bimachine at a position of the input: the first
part only depends on the prefix and on the state of the suffix automaton after
the suffix. -/
lemma evalFrom_append (M : Bimachine A B P S) (p : P) (u v : List A) :
    M.evalFrom p (u ++ v) = bmPref M p u (sfx M v) ++ M.evalFrom (strTrans M.prefixStep u p) v := by
  induction u generalizing p with
  | nil => simp [bmPref, strTrans]
  | cons a u ih =>
    rw [List.cons_append, Bimachine.evalFrom_cons, ih]
    have hs : strTrans M.suffixStep (a :: (u ++ v)).reverse M.suffixInit
        = strTrans M.suffixStep (a :: u).reverse (sfx M v) := by
      simp only [List.reverse_cons, List.reverse_append, sfx]
      rw [List.append_assoc, strTrans_append, strTrans_append]
    have hp : strTrans M.prefixStep u (M.prefixStep p a)
        = strTrans M.prefixStep (a :: u) p := by
      simp [strTrans]
    rw [hs, hp, bmPref, List.append_assoc]

/-- Two strings that give the same state of the suffix automaton are
equivalent. -/
lemma boundedVarRel_of_sfx_eq (M : Bimachine A B P S) [Finite P] {w₁ w₂ : List A}
    (h : sfx M w₁ = sfx M w₂) : BoundedVarRel M.eval w₁ w₂ := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  refine ⟨Finset.univ.sup
    (fun p : P => max (M.evalFrom p w₁).length (M.evalFrom p w₂).length), fun w => ?_⟩
  rw [Bimachine.eval_eq_evalFrom, Bimachine.eval_eq_evalFrom, evalFrom_append, evalFrom_append, h]
  refine leftDist_le rfl rfl ?_ ?_
  · exact le_trans (le_max_left _ (M.evalFrom (strTrans M.prefixStep w M.prefixInit) w₂).length)
      (Finset.le_sup (f := fun p : P => max (M.evalFrom p w₁).length (M.evalFrom p w₂).length)
        (Finset.mem_univ _))
  · exact le_trans (le_max_right (M.evalFrom (strTrans M.prefixStep w M.prefixInit) w₁).length _)
      (Finset.le_sup (f := fun p : P => max (M.evalFrom p w₁).length (M.evalFrom p w₂).length)
        (Finset.mem_univ _))

end BimachIndex

/-- **The easy half of Theorem `thm:machine-independent-rational-functions`.**  For a rational
function the relation `BoundedVarRel` has finite index. -/
theorem finiteIndex_of_isRationalFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) :
    {C : Set (List A) | ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}.Finite := by
  classical
  obtain ⟨P, S, hP, hS, M, hM⟩ := isBimachine_of_rationalFun hf
  subst hM
  haveI : Finite P := hP
  haveI : Finite S := hS
  set cls : List A → Set (List A) := fun w₁ => {w₂ | BoundedVarRel M.eval w₁ w₂} with hcls
  have hfac : ∀ w w' : List A, BimachIndex.sfx M w = BimachIndex.sfx M w' → cls w = cls w' := by
    intro w w' h
    have hb : BoundedVarRel M.eval w w' := BimachIndex.boundedVarRel_of_sfx_eq M h
    ext w₂
    simp only [hcls, Set.mem_setOf_eq]
    exact ⟨fun h2 => hb.symm.trans h2, fun h2 => hb.trans h2⟩
  refine Set.Finite.subset (Set.finite_range
    (fun s : S => if h : ∃ w, BimachIndex.sfx M w = s then cls h.choose else ∅)) ?_
  rintro C ⟨w₁, rfl⟩
  refine ⟨BimachIndex.sfx M w₁, ?_⟩
  have hex : ∃ w, BimachIndex.sfx M w = BimachIndex.sfx M w₁ := ⟨w₁, rfl⟩
  simp only
  rw [dif_pos hex]
  exact hfac _ _ hex.choose_spec

end Lax132576Proofs.Transducers
