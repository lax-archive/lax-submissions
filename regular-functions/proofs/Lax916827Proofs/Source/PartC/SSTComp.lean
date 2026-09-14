/-
The easy cases of the closure of the streaming string transducers under
post-composition with the prime regular functions (the "regular to sst" half of
Theorem `theorem:sst-two-way-equivalence` of *Transducers*, M. Bojańczyk).

The book's proof of that half of Theorem `theorem:sst-two-way-equivalence` shows that

  sst · primes ⊆ sst,

that is, that the composition of an sst with a prime function is again an sst.
This file contains the identity sst and the three easy cases:

* post-composition with a string homomorphism (in particular with a
  letter-to-letter map),
* post-composition with the end-of-string function `w ↦ w#`,
* post-composition with the reversal `w ↦ reverse w`.

The last one is not one of the primes of the book, but it makes the *right to
left* Mealy machines a consequence of the left-to-right ones: a right-to-left
Mealy machine is `reverse ∘ M.eval ∘ reverse`.

All the constructions are verified with the simulation lemma
`Transducers.SST.eval_of_sim` of `RequestProject/PartC/SSTBasic.lean`.
-/
import Lax132576Proofs.Source.PartB.LabAut
import Lax916827Proofs.Source.PartC.SSTBasic
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SST

variable {A B C Q X : Type}

/-! ### Post-composition with a homomorphism -/

/-- Applying a homomorphism to the output letters of a string over `X + B`. -/
def homStr (φ : B → List C) (s : List (X ⊕ B)) : List (X ⊕ C) :=
  s.flatMap (fun z => match z with | Sum.inl x => [Sum.inl x] | Sum.inr b => (φ b).map Sum.inr)

@[simp] lemma homStr_nil (φ : B → List C) : homStr (X := X) φ [] = [] := rfl

@[simp] lemma homStr_cons_inl (φ : B → List C) (x : X) (s : List (X ⊕ B)) :
    homStr φ (Sum.inl x :: s) = Sum.inl x :: homStr φ s := by
  simp [homStr]

@[simp] lemma homStr_cons_inr (φ : B → List C) (b : B) (s : List (X ⊕ B)) :
    homStr (X := X) φ (Sum.inr b :: s) = (φ b).map Sum.inr ++ homStr φ s := by
  simp [homStr]

@[simp] lemma regsOf_map_inr (v : List B) : regsOf ((v.map Sum.inr : List (X ⊕ B))) = [] := by
  induction v with
  | nil => rfl
  | cons b v ih => simpa using ih

@[simp] lemma regsOf_homStr (φ : B → List C) (s : List (X ⊕ B)) :
    regsOf (homStr φ s) = regsOf s := by
  induction s with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl x => simp [ih]
      | inr b => simp [ih]

lemma homOf_nil (φ : B → List C) : homOf φ [] = [] := rfl

lemma homOf_append (φ : B → List C) (u v : List B) :
    homOf φ (u ++ v) = homOf φ u ++ homOf φ v := by
  simp [homOf]

lemma homOf_singleton_map (ρ : B → C) (v : List B) :
    homOf (fun b => [ρ b]) v = v.map ρ := by
  induction v with
  | nil => rfl
  | cons b v ih => simpa [homOf] using ih

lemma subst_homStr (φ : B → List C) (η : X → List B) (s : List (X ⊕ B)) :
    subst (fun x => homOf φ (η x)) (homStr φ s) = homOf φ (subst η s) := by
  induction s with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl x =>
          rw [homStr_cons_inl, subst_cons_inl, subst_cons_inl, ih, homOf_append]
      | inr b =>
          rw [homStr_cons_inr, subst_append, ih, subst_cons_inr, subst_map_inr]
          simp [homOf]

lemma regsOf_reverse (s : List (X ⊕ B)) : regsOf s.reverse = (regsOf s).reverse := by
  induction s with
  | nil => rfl
  | cons z s ih => cases z <;> simp [ih]

lemma subst_reverse (η : X → List B) (s : List (X ⊕ B)) :
    subst (fun x => (η x).reverse) s.reverse = (subst η s).reverse := by
  induction s with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl x => simp [subst_append, ih, subst_cons_inl]
      | inr b => simp [subst_append, ih, subst_cons_inr]

variable [Fintype X]

/-- The sst obtained by applying a homomorphism to the output letters. -/
def homSST (T : SST A B Q X) (φ : B → List C) : SST A C Q X where
  init := T.init
  step := fun q a => ((T.step q a).1, fun x => homStr φ ((T.step q a).2 x))
  step_copyless := by
    intro q a
    have h := T.step_copyless q a
    rw [copyless_iff] at h ⊢
    simpa using h
  final := fun q => homStr φ (T.final q)

lemma homSST_eval (T : SST A B Q X) (φ : B → List C) (w : List A) :
    (T.homSST φ).eval w = homOf φ (T.eval w) := by
  refine eval_of_sim (T := T) (T' := T.homSST φ) (p := homOf φ)
    (fun c c' => c' = (c.1, fun x => homOf φ (c.2 x))) (by simp [homSST, homOf_nil]) ?_ ?_ w
  · rintro ⟨q, η⟩ c' a rfl
    show ((T.step q a).1, fun x => subst (fun y => homOf φ (η y)) (homStr φ ((T.step q a).2 x))) =
      ((T.step q a).1, fun x => homOf φ (subst η ((T.step q a).2 x)))
    exact congrArg _ (funext fun x => subst_homStr φ η _)
  · rintro ⟨q, η⟩ c' rfl
    exact subst_homStr φ η (T.final q)

/-! ### Post-composition with the reversal -/

/-- The sst obtained by reversing the contents of every register. -/
def revSST (T : SST A B Q X) : SST A B Q X where
  init := T.init
  step := fun q a => ((T.step q a).1, fun x => ((T.step q a).2 x).reverse)
  step_copyless := by
    intro q a
    have h := T.step_copyless q a
    rw [copyless_iff] at h ⊢
    refine ⟨fun x => ?_, fun x x' hxx' y hy hy' => ?_⟩
    · rw [regsOf_reverse]
      exact List.nodup_reverse.2 (h.1 x)
    · rw [regsOf_reverse] at hy hy'
      exact h.2 x x' hxx' y (by simpa using hy) (by simpa using hy')
  final := fun q => (T.final q).reverse

lemma revSST_eval (T : SST A B Q X) (w : List A) :
    T.revSST.eval w = (T.eval w).reverse := by
  refine eval_of_sim (T := T) (T' := T.revSST) (p := List.reverse)
    (fun c c' => c' = (c.1, fun x => (c.2 x).reverse)) (by simp [revSST]) ?_ ?_ w
  · rintro ⟨q, η⟩ c' a rfl
    show ((T.step q a).1, fun x => subst (fun y => (η y).reverse) (((T.step q a).2 x).reverse)) =
      ((T.step q a).1, fun x => (subst η ((T.step q a).2 x)).reverse)
    exact congrArg _ (funext fun x => subst_reverse η _)
  · rintro ⟨q, η⟩ c' rfl
    exact subst_reverse η (T.final q)

/-! ### Appending a fixed string to the output -/

/-- The sst obtained by appending a fixed string to the output. -/
def appendSST (T : SST A B Q X) (v : List B) : SST A B Q X where
  init := T.init
  step := T.step
  step_copyless := T.step_copyless
  final := fun q => T.final q ++ v.map Sum.inr

lemma appendSST_eval (T : SST A B Q X) (v : List B) (w : List A) :
    (T.appendSST v).eval w = T.eval w ++ v := by
  show subst _ (T.final _ ++ v.map Sum.inr) = _
  rw [subst_append, subst_map_inr]
  rfl

end SST

/-! ### The identity, and the closure properties in terms of `IsSST` -/

variable {A B C : Type}

/-- The sst that copies its input into a single register. -/
def idSST (A : Type) : SST A A Unit Unit where
  init := ()
  step := fun _ a => ((), fun _ => [Sum.inl (), Sum.inr a])
  step_copyless := by
    intro q a
    rw [copyless_iff]
    exact ⟨fun x => by simp [regsOf], fun x x' hxx' => absurd (Subsingleton.elim x x') hxx'⟩
  final := fun _ => [Sum.inl ()]

lemma idSST_eval (w : List A) : (idSST A).eval w = w := by
  have key : ∀ w : List A, (idSST A).runConfig w = ((), fun _ => w) := by
    intro w
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton u a ih =>
        rw [SST.runConfig_append, ih]
        simp [SST.stepConfig, SST.subst, idSST]
  show SST.subst ((idSST A).runConfig w).2 _ = w
  rw [key]
  simp [SST.subst, idSST]

/-- The identity is computed by an sst. -/
theorem isSST_id : IsSST (id : List A → List A) :=
  ⟨Unit, Unit, inferInstance, inferInstance, idSST A, funext idSST_eval⟩

/-- An sst computes the same function as any function equal to it. -/
lemma IsSST.congr {f g : List A → List B} (hf : IsSST f) (h : ∀ w, f w = g w) : IsSST g := by
  obtain ⟨Q, X, hQ, hX, T, hT⟩ := hf
  exact ⟨Q, X, hQ, hX, T, by rw [hT]; exact funext h⟩

/-- sst's are closed under post-composition with a homomorphism. -/
theorem isSST_comp_hom {f : List A → List B} (hf : IsSST f) (φ : B → List C) :
    IsSST (fun w => homOf φ (f w)) := by
  obtain ⟨Q, X, hQ, hX, T, rfl⟩ := hf
  exact ⟨Q, X, hQ, hX, T.homSST φ, funext fun w => T.homSST_eval φ w⟩

/-- sst's are closed under post-composition with a letter-to-letter map. -/
theorem isSST_comp_map {f : List A → List B} (hf : IsSST f) (ρ : B → C) :
    IsSST (fun w => (f w).map ρ) :=
  (isSST_comp_hom hf (fun b => [ρ b])).congr (fun w => SST.homOf_singleton_map ρ (f w))

/-- sst's are closed under post-composition with the reversal. -/
theorem isSST_comp_reverse {f : List A → List B} (hf : IsSST f) :
    IsSST (fun w => (f w).reverse) := by
  obtain ⟨Q, X, hQ, hX, T, rfl⟩ := hf
  exact ⟨Q, X, hQ, hX, T.revSST, funext fun w => T.revSST_eval w⟩

/-- sst's are closed under appending a fixed string to the output. -/
theorem isSST_comp_append {f : List A → List B} (hf : IsSST f) (v : List B) :
    IsSST (fun w => f w ++ v) := by
  obtain ⟨Q, X, hQ, hX, T, rfl⟩ := hf
  exact ⟨Q, X, hQ, hX, T.appendSST v, funext fun w => T.appendSST_eval v w⟩

end Lax916827Proofs.Transducers
