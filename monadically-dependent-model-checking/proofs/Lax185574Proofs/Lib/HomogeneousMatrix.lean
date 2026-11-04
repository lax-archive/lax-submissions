import Lax185574Proofs.Lib.ExplicitRamsey
import Lax185574Proofs.Lib.BipartiteStaircase

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-! Order-preserving Ramsey extraction, applied to the staircase matrix. -/

namespace Lax185574Proofs.Lib.HomogeneousMatrix

open SimpleGraph

theorem ordered_homogeneous {m : ℕ} (n : ℕ) (T : Finset (Fin m))
    (hT : 3 ^ (n + n) ≤ T.card) (P : Fin m → Fin m → Prop) :
    ∃ (d : Bool) (e : Fin n ↪o Fin m), (∀ i, e i ∈ T) ∧
      ∀ i j, i < j → (P (e i) (e j) ↔ d = true) := by
  classical
  let G : SimpleGraph T := {
    Adj := fun x y => x ≠ y ∧ if x < y then P x y else P y x
    symm := ⟨by
      intro x y h
      refine ⟨h.1.symm, ?_⟩
      by_cases hxy : x < y
      · simpa [hxy, not_lt_of_ge hxy.le] using h.2
      · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) h.1.symm
        simpa [hxy, hyx] using h.2⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have hcard : 3 ^ (n + n) ≤ Fintype.card T := by simpa using hT
  rcases ExplicitRamsey.ramsey n n G hcard with h | h
  · obtain ⟨S, hS⟩ := Classical.not_forall.mp h
    have hS : G.IsNClique n S := not_not.mp hS
    let f : Fin n ↪o T := S.orderEmbOfFin hS.2
    let e : Fin n ↪o Fin m := f.trans (OrderEmbedding.subtype _)
    refine ⟨true, e, fun i => (f i).2, ?_⟩
    intro i j hij
    have hi : f i ∈ S := S.orderEmbOfFin_mem hS.2 i
    have hj : f j ∈ S := S.orderEmbOfFin_mem hS.2 j
    have hne : f i ≠ f j := f.injective.ne hij.ne
    have hadj := hS.1 hi hj hne
    have hlt : f i < f j := f.strictMono hij
    simpa [G, hlt, e] using hadj.2
  · obtain ⟨S, hS⟩ := Classical.not_forall.mp h
    have hS : Gᶜ.IsNClique n S := not_not.mp hS
    let f : Fin n ↪o T := S.orderEmbOfFin hS.2
    let e : Fin n ↪o Fin m := f.trans (OrderEmbedding.subtype _)
    refine ⟨false, e, fun i => (f i).2, ?_⟩
    intro i j hij
    have hi : f i ∈ S := S.orderEmbOfFin_mem hS.2 i
    have hj : f j ∈ S := S.orderEmbOfFin_mem hS.2 j
    have hne : f i ≠ f j := f.injective.ne hij.ne
    have hadj := hS.1 hi hj hne
    have hlt : f i < f j := f.strictMono hij
    have hp : ¬ P (e i) (e j) := by
      intro hp
      exact hadj.2 ⟨hne, by simpa [G, hlt, e] using hp⟩
    simp [hp]

theorem bool_pigeonhole (r : ℕ) (f : Fin (2 * r) → Bool) :
    ∃ (t : Bool) (T : Finset (Fin (2 * r))),
      r ≤ T.card ∧ ∀ i ∈ T, f i = t := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun i => f i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  by_cases h : r ≤ (Finset.univ.filter fun i => f i = true).card
  · exact ⟨true, Finset.univ.filter (fun i => f i = true), h,
      fun i hi => (Finset.mem_filter.mp hi).2⟩
  · refine ⟨false, Finset.univ.filter (fun i => ¬f i = true), by omega, ?_⟩
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    cases hf : f i <;> simp_all

open BipartiteStaircase

universe u
variable {R : Type u} [DecidableEq R]

/-- The two halves of the off-diagonal rectangle are constant, and the
diagonal is opposite to the lower half. -/
theorem extract_matrix (n : ℕ) (F : Finset (Finset R))
    (hF : 2 ^ (2 * 3 ^ (n + n)) ≤ F.card) :
    ∃ (a : Fin n → Finset R) (b : Fin n → R) (t d : Bool),
      Function.Injective a ∧ Function.Injective b ∧ (∀ i, a i ∈ F) ∧
      (∀ i, b i ∈ a i ↔ t = false) ∧
      (∀ i j, j < i → (b j ∈ a i ↔ t = true)) ∧
      (∀ i j, i < j → (b j ∈ a i ↔ d = true)) := by
  classical
  obtain ⟨s⟩ := exists_staircase (2 * 3 ^ (n + n)) F hF
  obtain ⟨t, T, hT, ht⟩ := bool_pigeonhole (3 ^ (n + n)) s.bit
  obtain ⟨d, e, he, hd⟩ := ordered_homogeneous n T hT
    (fun i j => s.column j ∈ s.row i)
  refine ⟨s.row ∘ e, s.column ∘ e, t, d,
    s.row_injective.comp e.injective, s.column_injective.comp e.injective,
    fun i => s.row_mem (e i), ?_, ?_, ?_⟩
  · intro i
    simpa [ht _ (he i)] using s.diagonal (e i)
  · intro i j hji
    simpa [ht _ (he j)] using s.lower (e j) (e i) (e.strictMono hji)
  · exact hd

end Lax185574Proofs.Lib.HomogeneousMatrix
