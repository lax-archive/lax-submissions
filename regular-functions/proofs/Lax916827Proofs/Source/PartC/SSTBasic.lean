/-
Basic API for streaming string transducers (Section *Streaming string transducers* of *Transducers*,
M. Bojańczyk).

This file collects the elementary facts about the semantics of an sst that all
the constructions of Section *Streaming string transducers* use:

* the substitution `SST.subst` of register contents into a string over `X + B`,
  and its compatibility with concatenation;
* a workable criterion for the copyless restriction (`Transducers.copyless_iff`);
* the *simulation lemma* `Transducers.SST.eval_of_sim`, which is how every construction in the proof
  of Theorem `theorem:sst-two-way-equivalence` is verified: to see that a new sst computes `p ∘
  T.eval` it suffices to exhibit an invariant relating the configurations of the two machines.
-/
import Lax916827Proofs.Source.PartC.SSTDef
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- The list of register names occurring in a string over `X + B`. -/
def regsOf {X B : Type} (s : List (X ⊕ B)) : List X :=
  s.filterMap (fun z => match z with | Sum.inl x => some x | Sum.inr _ => none)

namespace regsOf

variable {X B : Type}

@[simp] lemma nil : regsOf ([] : List (X ⊕ B)) = [] := rfl

@[simp] lemma cons_inl (x : X) (s : List (X ⊕ B)) :
    regsOf (Sum.inl x :: s) = x :: regsOf s := rfl

@[simp] lemma cons_inr (b : B) (s : List (X ⊕ B)) :
    regsOf (Sum.inr b :: s) = regsOf s := rfl

@[simp] lemma append (s t : List (X ⊕ B)) : regsOf (s ++ t) = regsOf s ++ regsOf t := by
  simp [regsOf]

lemma mem_iff {x : X} {s : List (X ⊕ B)} : x ∈ regsOf s ↔ Sum.inl x ∈ s := by
  induction s with
  | nil => simp
  | cons z s ih => cases z <;> simp [ih]

end regsOf

/-- The copyless restriction, spelled out: the register names occurring in a
single `u x` are pairwise distinct, and no register name occurs in two different
`u x`'s. -/
lemma copyless_iff {X B : Type} [Fintype X] (u : X → List (X ⊕ B)) :
    Copyless u ↔ (∀ x : X, (regsOf (u x)).Nodup) ∧
      ∀ x x' : X, x ≠ x' → ∀ y : X, y ∈ regsOf (u x) → y ∉ regsOf (u x') := by
  have hC : Copyless u ↔ ((Finset.univ.toList.map (fun x => regsOf (u x))).flatten).Nodup := by
    unfold Copyless regsOf
    rw [List.filterMap_flatten, List.map_map]
    rfl
  rw [hC, List.nodup_flatten]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x => h1 _ (List.mem_map_of_mem (by simp)), ?_⟩
    intro x x' hxx' y hy hy'
    rw [List.pairwise_map] at h2
    have hsymm : Symmetric (fun a b : X => List.Disjoint (regsOf (u a)) (regsOf (u b))) :=
      fun a b hab => hab.symm
    exact (h2.forall hsymm (by simp) (by simp) hxx') hy hy'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro l hl
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      exact h1 x
    · rw [List.pairwise_map]
      refine (Finset.nodup_toList _).pairwise_of_forall_ne ?_
      intro a _ b _ hab y hy hy'
      exact h2 a b hab y hy hy'

namespace SST

variable {A B Q X : Type}

@[simp] lemma subst_nil (η : X → List B) : subst η [] = [] := rfl

@[simp] lemma subst_cons_inl (η : X → List B) (x : X) (s : List (X ⊕ B)) :
    subst η (Sum.inl x :: s) = η x ++ subst η s := rfl

@[simp] lemma subst_cons_inr (η : X → List B) (b : B) (s : List (X ⊕ B)) :
    subst η (Sum.inr b :: s) = b :: subst η s := rfl

lemma subst_append (η : X → List B) (s t : List (X ⊕ B)) :
    subst η (s ++ t) = subst η s ++ subst η t := by
  simp [subst]

@[simp] lemma subst_map_inr (η : X → List B) (v : List B) :
    subst η (v.map Sum.inr) = v := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [ih]

lemma subst_congr {η η' : X → List B} {s : List (X ⊕ B)}
    (h : ∀ x, Sum.inl x ∈ s → η x = η' x) : subst η s = subst η' s := by
  induction s with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl x =>
          rw [subst_cons_inl, subst_cons_inl, h x (by simp),
            ih (fun y hy => h y (by simp [hy]))]
      | inr b => rw [subst_cons_inr, subst_cons_inr, ih (fun y hy => h y (by simp [hy]))]

/-! ### Runs -/

@[simp] lemma runConfig_nil [Fintype X] (T : SST A B Q X) :
    T.runConfig [] = (T.init, fun _ => []) := rfl

lemma runConfig_append [Fintype X] (T : SST A B Q X) (u v : List A) :
    T.runConfig (u ++ v) = v.foldl T.stepConfig (T.runConfig u) := by
  simp [runConfig, List.foldl_append]

/-! ### The simulation lemma -/

/-- **The simulation lemma.**  If the configurations of two sst's `T` and `T'`
reading the same input can be related by an invariant that holds initially, is
preserved by one step, and guarantees that the output of `T'` is the image under
`p` of the output of `T`, then `T'` computes `p ∘ T.eval`. -/
theorem eval_of_sim {A B C Q X Q' X' : Type} [Fintype X] [Fintype X']
    {T : SST A B Q X} {T' : SST A C Q' X'} {p : List B → List C}
    (Inv : Q × (X → List B) → Q' × (X' → List C) → Prop)
    (hinit : Inv (T.init, fun _ => []) (T'.init, fun _ => []))
    (hstep : ∀ c c' a, Inv c c' → Inv (T.stepConfig c a) (T'.stepConfig c' a))
    (hfin : ∀ c c', Inv c c' → subst c'.2 (T'.final c'.1) = p (subst c.2 (T.final c.1)))
    (w : List A) : T'.eval w = p (T.eval w) := by
  have key : ∀ (w : List A) c c', Inv c c' →
      Inv (w.foldl T.stepConfig c) (w.foldl T'.stepConfig c') := by
    intro w
    induction w with
    | nil => intro c c' h; exact h
    | cons a w ih => intro c c' h; exact ih _ _ (hstep c c' a h)
  exact hfin _ _ (key w _ _ hinit)

end SST

end Lax916827Proofs.Transducers
