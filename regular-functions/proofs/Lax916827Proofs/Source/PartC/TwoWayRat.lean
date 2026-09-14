/- Pre-composition of two-way transducers with rational functions (Corollary
`cor:2dfa-closure-under-composition` of *Transducers*, M. Bojańczyk).

By Theorem `thm:rational-primes` a rational function is a composition of prime rational
functions: prime Mealy machines, their right-to-left variants, homomorphisms,
and the function `w ↦ w#` appending a fresh separator.  Pre-composition with a
prime Mealy machine is Lemma `lem:2dfa-precomposition-with-mealy`, and reversal transports it to the
right-to-left variant.  An arbitrary homomorphism is the composition of a
homomorphism whose blocks all have the same length (`TwoWayBlock.lean`), the
blocks being padded with a fresh letter, and of the erasing homomorphism that
deletes the padding (`TwoWayErase.lean`).  Finally `w ↦ w#` is a letter-to-letter
homomorphism followed by appending a fixed letter (`TwoWayHom.lean`).
-/
import Lax916827Proofs.Source.PartC.TwoWayErase
import Lax132576Proofs.Source.PartB.PrimeRat
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## Pre-composition with an arbitrary homomorphism -/

section Hom

variable {A B C : Type}

/-- The blocks of `φ`, padded with a fresh letter so that they all have
length `L`. -/
def padHom (φ : A → List B) (L : ℕ) (a : A) : List (Option B) :=
  (φ a).map some ++ List.replicate (L - (φ a).length) none

lemma padHom_length {φ : A → List B} {L : ℕ} (hL : ∀ a, (φ a).length ≤ L) (a : A) :
    (padHom φ L a).length = L := by
  have := hL a
  simp only [padHom, List.length_append, List.length_map, List.length_replicate]
  omega

lemma filterMap_padHom (φ : A → List B) (L : ℕ) (a : A) :
    (padHom φ L a).filterMap id = φ a := by
  simp [padHom, List.filterMap_append, List.filterMap_map]

lemma filterMap_homOf_padHom (φ : A → List B) (L : ℕ) (w : List A) :
    (homOf (padHom φ L) w).filterMap id = homOf φ w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [homOf_cons, homOf_cons, List.filterMap_append, filterMap_padHom, ih]

/-- The length of the blocks of a homomorphism on a finite alphabet is
bounded. -/
lemma exists_block_bound [Finite A] (φ : A → List B) : ∃ L : ℕ, ∀ a, (φ a).length ≤ L := by
  obtain ⟨L, hL⟩ := (Set.finite_range fun a => (φ a).length).bddAbove
  exact ⟨L, fun a => hL (Set.mem_range_self a)⟩

/-- Two-way transducers are closed under pre-composition with an arbitrary
homomorphism. -/
theorem isTwoWay_comp_hom [Finite A] [Finite B] {g : List B → List C} (hg : IsTwoWay g)
    (φ : A → List B) : IsTwoWay (fun w => g (homOf φ w)) := by
  obtain ⟨L, hL⟩ := exists_block_bound φ
  have hL' : ∀ a, (φ a).length ≤ L + 1 := fun a => le_trans (hL a) (Nat.le_succ L)
  -- erase the padding
  have hg' : IsTwoWay (fun v : List (Option B) => g (v.filterMap id)) :=
    isTwoWay_comp_filterMap hg id
  -- read the padded blocks
  have hb := isTwoWay_comp_blockHom hg' (padHom φ (L + 1)) (Nat.succ_pos L)
    (padHom_length hL')
  simp only [filterMap_homOf_padHom] at hb
  exact hb

/-- A letter-to-letter map is a homomorphism, so two-way transducers are closed
under pre-composition with it. -/
lemma isTwoWay_comp_map {g : List B → List C} (hg : IsTwoWay g) (ρ : A → B) :
    IsTwoWay (fun w => g (w.map ρ)) := by
  have h := isTwoWay_comp_blockHom hg (fun a => [ρ a]) Nat.one_pos (fun _ => rfl)
  have hmap : ∀ w : List A, homOf (fun a => [ρ a]) w = w.map ρ := by
    intro w
    induction w with
    | nil => rfl
    | cons a w ih => rw [homOf_cons, ih]; simp
  simpa [hmap] using h

end Hom

/-! ## Pre-composition with a prime rational function -/

/-- Pre-composition of a two-way transducer with a prime rational function. -/
lemma isTwoWay_comp_primeRat {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : PrimeRationalFam A B f) {C : Type} {g : List B → List C} (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f) := by
  rcases hf with hM | hM | ⟨φ, rfl⟩ | ⟨e, rfl⟩
  · exact isTwoWay_comp_prime hM hg
  · -- a right-to-left prime Mealy machine
    set h : List A → List B := fun w => (f w.reverse).reverse with hh
    have hfh : ∀ w : List A, f w = (h w.reverse).reverse := by
      intro w; simp [hh]
    have hg₁ : IsTwoWay (fun v : List B => g v.reverse) := isTwoWay_comp_reverse hg
    have hgh : IsTwoWay ((fun v : List B => g v.reverse) ∘ h) := isTwoWay_comp_prime hM hg₁
    have := isTwoWay_comp_reverse hgh
    refine (?_ : (fun w : List A => ((fun v : List B => g v.reverse) ∘ h) w.reverse) = g ∘ f) ▸ this
    funext w
    simp [Function.comp, hfh w]
  · exact isTwoWay_comp_hom hg φ
  · -- `w ↦ w #`
    have hg₂ : IsTwoWay (fun v : List B => g (v ++ [e none])) := isTwoWay_comp_append hg (e none)
    have := isTwoWay_comp_map hg₂ (fun a : A => e (some a))
    exact this

/-- Pre-composition of a two-way transducer with a composition of prime rational
functions. -/
lemma isTwoWay_comp_compClosureRat {A B : Type} {f : List A → List B}
    (hf : CompClosure PrimeRationalFam A B f) :
    Finite A → Finite B → ∀ {C : Type} {g : List B → List C}, IsTwoWay g → IsTwoWay (g ∘ f) := by
  induction hf with
  | base h =>
      intro hA hB C g hg
      haveI := hA; haveI := hB
      exact isTwoWay_comp_primeRat h hg
  | id A => intro _ _ C g hg; simpa using hg
  | @comp A B C hB f g _ _ ih₁ ih₂ =>
      intro hA hC D k hk
      have h2 := ih₂ hB hC hk
      have h1 := ih₁ hA hB h2
      simpa [Function.comp_assoc] using h1

/-- **Corollary `cor:2dfa-closure-under-composition`.**  Two-way transducers are closed under
pre-composition with rational functions. -/
theorem isTwoWay_comp_rational {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) {C : Type} {g : List B → List C} (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f) :=
  isTwoWay_comp_compClosureRat ((rational_iff_prime_composition f).1 hf)
    inferInstance inferInstance hg

end Lax916827Proofs.Transducers
