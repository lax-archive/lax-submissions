import Lax185574Proofs.Lib.BallFlipTraces
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.BallFlipParameters

open Lax185574Proofs.Lib.BoundedVCDuality Lax185574Proofs.Lib.BallFlips
open BallFlipTraces
open scoped BigOperators

universe u

/-- Choose one duality outcome for each ordered pair in a finite family. -/
theorem exists_duality_parameters {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hdual : ∀ X Y : Finset V,
      (∃ W : Finset V, W ⊆ X ∧ W.card ≤ k ∧ Dominates G W Y) ∨
      (∃ W : Finset V, W ⊆ Y ∧ W.card ≤ k ∧ Antidominates G W X))
    (Z : Finset (Finset V)) (R : Finset V) :
    ∃ S : Finset V, R ⊆ S ∧ S.card ≤ R.card + Z.card * Z.card * k ∧
      ∀ X ∈ Z, ∀ Y ∈ Z,
        Dominates G (S ∩ X) Y ∨ Antidominates G (S ∩ Y) X := by
  classical
  have hw (xy : Finset V × Finset V) : ∃ W : Finset V, W.card ≤ k ∧
      ((W ⊆ xy.1 ∧ Dominates G W xy.2) ∨
        (W ⊆ xy.2 ∧ Antidominates G W xy.1)) := by
    rcases hdual xy.1 xy.2 with ⟨W, hs, hc, hW⟩ | ⟨W, hs, hc, hW⟩
    · exact ⟨W, hc, Or.inl ⟨hs, hW⟩⟩
    · exact ⟨W, hc, Or.inr ⟨hs, hW⟩⟩
  choose witness hcard hcase using hw
  let S := R ∪ (Z ×ˢ Z).biUnion witness
  have hwS {X Y : Finset V} (hX : X ∈ Z) (hY : Y ∈ Z) : witness (X, Y) ⊆ S := by
    intro v hv
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨(X, Y), Finset.mem_product.mpr ⟨hX, hY⟩, hv⟩)
  refine ⟨S, Finset.subset_union_left, ?_, ?_⟩
  · calc
      S.card ≤ R.card + ((Z ×ˢ Z).biUnion witness).card := Finset.card_union_le _ _
      _ ≤ R.card + ∑ xy ∈ Z ×ˢ Z, (witness xy).card :=
        Nat.add_le_add_left (Finset.card_biUnion_le) _
      _ ≤ R.card + ∑ _xy ∈ Z ×ˢ Z, k :=
        Nat.add_le_add_left (Finset.sum_le_sum (fun xy _ => hcard xy)) _
      _ = R.card + Z.card * Z.card * k := by simp
  · intro X hX Y hY
    rcases hcase (X, Y) with ⟨hsub, hdom⟩ | ⟨hsub, hanti⟩
    · left
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hdom y hy
      exact ⟨x, Finset.mem_inter.mpr ⟨hwS hX hY hx, hsub hx⟩, hxy⟩
    · right
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hanti x hx
      exact ⟨y, Finset.mem_inter.mpr ⟨hwS hX hY hy, hsub hy⟩, hxy⟩

theorem exists_control_parameters {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (k t : ℕ)
    (hdual : ∀ X Y : Finset V,
      (∃ W : Finset V, W ⊆ X ∧ W.card ≤ k ∧ Dominates G W Y) ∨
      (∃ W : Finset V, W ⊆ Y ∧ W.card ≤ k ∧ Antidominates G W X))
    (A B D : Finset V) (ht : (traces G A B).card ≤ t) :
    ∃ S : Finset V,
      S.card ≤ 2 ^ t + t + (2 ^ t + t + 1) * (2 ^ t + t + 1) * k ∧
      (∀ a ∈ A, ∃ a₀ ∈ S, a₀ ∈ A ∧ trace G B a₀ = trace G B a) ∧
      (∀ b ∈ B, ∃ b₀ ∈ S, b₀ ∈ B ∧ trace G A b₀ = trace G A b) ∧
      (∀ a ∈ A, ∀ a' ∈ A,
        Dominates G (S ∩ traceClass G A B a) (traceClass G A B a') ∨
        Antidominates G (S ∩ traceClass G A B a') (traceClass G A B a)) ∧
      (∀ b ∈ B,
        Dominates G (S ∩ D) (traceClass G B A b) ∨
        Antidominates G (S ∩ traceClass G B A b) D) := by
  classical
  obtain ⟨A₀, B₀, hA₀, hB₀, hAc, hBc, hrepA, hrepB⟩ :=
    exists_trace_representatives G A B t ht
  let Z := insert D (A₀.image (traceClass G A B) ∪ B₀.image (traceClass G B A))
  have hAZ {a : V} (ha : a ∈ A) : traceClass G A B a ∈ Z := by
    obtain ⟨a₀, ha₀, heq⟩ := hrepA a ha
    have hclass : traceClass G A B a₀ = traceClass G A B a := by
      ext x
      simp only [mem_traceClass, heq]
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨a₀, ha₀, hclass⟩))
  have hBZ {b : V} (hb : b ∈ B) : traceClass G B A b ∈ Z := by
    obtain ⟨b₀, hb₀, heq⟩ := hrepB b hb
    have hclass : traceClass G B A b₀ = traceClass G B A b := by
      ext x
      simp only [mem_traceClass, heq]
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨b₀, hb₀, hclass⟩))
  have hZc : Z.card ≤ 2 ^ t + t + 1 := by
    have hi := Finset.card_insert_le D
      (A₀.image (traceClass G A B) ∪ B₀.image (traceClass G B A))
    have hu := Finset.card_union_le
      (A₀.image (traceClass G A B)) (B₀.image (traceClass G B A))
    have ha := Finset.card_image_le (s := A₀) (f := traceClass G A B)
    have hb := Finset.card_image_le (s := B₀) (f := traceClass G B A)
    dsimp only [Z]
    omega
  obtain ⟨S, hRS, hSc, hSD⟩ := exists_duality_parameters G k hdual Z (A₀ ∪ B₀)
  have hRc : (A₀ ∪ B₀).card ≤ 2 ^ t + t :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hAc hBc)
  refine ⟨S, hSc.trans (Nat.add_le_add hRc
    (Nat.mul_le_mul_right k (Nat.mul_le_mul hZc hZc))), ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a₀, ha₀, htr⟩ := hrepA a ha
    exact ⟨a₀, hRS (Finset.mem_union_left _ ha₀), hA₀ ha₀, htr⟩
  · intro b hb
    obtain ⟨b₀, hb₀, htr⟩ := hrepB b hb
    exact ⟨b₀, hRS (Finset.mem_union_right _ hb₀), hB₀ hb₀, htr⟩
  · intro a ha a' ha'
    exact hSD _ (hAZ ha) _ (hAZ ha')
  · intro b hb
    exact hSD D (Finset.mem_insert_self _ _) _ (hBZ hb)

end Lax185574Proofs.Lib.BallFlipParameters
