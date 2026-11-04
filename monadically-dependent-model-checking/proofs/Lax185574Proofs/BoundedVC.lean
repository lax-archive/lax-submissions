import Lax185574Proofs.Interface.Shim.IndependenceProperty
import Lax185574.VCDimension

/-!
Monadically dependent classes have bounded VC-dimension: the edge
formula `E(x, y)` does not have the independence property.
-/

namespace Lax185574Proofs.BoundedVC

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.MonadicDependence Lax710763.Transductions
open Lax185574.VCDimension Lax185574Proofs.Interface.Old

universe u

/-- The edge formula `E(x, y)` of colored graphs, with `x` on the left
and `y` on the right. -/
def edgeFormula (k : ℕ) : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1) :=
  (LHom.sumInl : Language.graph →ᴸ withColors Language.graph k).onFormula
    (Relations.formula₂ Language.adj (Term.var (Sum.inl 0)) (Term.var (Sum.inr 0)))

theorem realizeIn_edgeFormula {n k : ℕ} (G : SimpleGraph (Fin n))
    (colors : Fin k → Set (Fin n)) (v : Fin 1 ⊕ Fin 1 → Fin n) :
    RealizeIn G.structure colors (edgeFormula k) v ↔ G.Adj (v (Sum.inl 0)) (v (Sum.inr 0)) := by
  unfold RealizeIn edgeFormula
  let _ := G.structure
  let _ := colorStructure colors
  rw [LHom.realize_onFormula]
  simp only [Formula.realize_rel₂, Term.realize_var]
  rfl

/-- Subsets of shattered sets are shattered. -/
theorem shatters_mono {V : Type u} {G : SimpleGraph V} {A B : Finset V} (hBA : B ⊆ A)
    (h : Shatters G A) : Shatters G B := by
  intro C hC
  obtain ⟨v, hv⟩ := h C (hC.trans hBA)
  exact ⟨v, fun a ha => hv a (hBA ha)⟩

/-- If every shattered set has fewer than `m` elements, the VC-dimension
is at most `m`. -/
theorem vcDim_le_of_forall_card_lt {V : Type u} (G : SimpleGraph V) (m : ℕ)
    (h : ∀ A : Finset V, Shatters G A → A.card < m) : vcDim G ≤ m := by
  refine iSup₂_le fun A hA => ?_
  exact_mod_cast (h A hA).le

/-- A graph class on which `E(x, y)` does not have the independence
property has bounded VC-dimension. -/
theorem exists_vcDim_le_of_not_hasIP (C : GraphClass) (h : ¬ HasIP C (edgeFormula 0)) :
    ∃ d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → vcDim G ≤ d := by
  classical
  unfold HasIP at h
  push Not at h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun n G hG => vcDim_le_of_forall_card_lt G m fun A hA => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨A', hA'A, hA'⟩ := Finset.exists_subset_card_eq hlt
  have hsh : Shatters G A' := shatters_mono hA'A hA
  let e : Fin m ≃ A' := (A'.equivFinOfCardEq hA').symm
  let a : Fin m → Fin 1 → Fin n := fun i _ => (e i : Fin n)
  have hb : ∀ J : Finset (Fin m), ∃ v : Fin n, ∀ x ∈ A',
      (G.Adj v x ↔ x ∈ J.image fun i => (e i : Fin n)) := fun J =>
    hsh _ (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (e i).2)
  choose b hb using hb
  obtain ⟨i, J, hiJ⟩ := hm n G hG Fin.elim0 a (fun J _ => b J)
  have key : RealizeIn G.structure Fin.elim0 (edgeFormula 0)
      (Sum.elim (a i) fun _ => b J) ↔ i ∈ J := by
    rw [realizeIn_edgeFormula]
    simp only [Sum.elim_inl, Sum.elim_inr, a]
    rw [G.adj_comm, hb J _ (e i).2, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, hji⟩
      exact (e.injective (Subtype.ext hji)) ▸ hj
    · intro hi; exact ⟨i, hi, rfl⟩
  rcases hiJ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (key.mp h1)
  · exact h1 (key.mpr h2)

/-- Monadically dependent classes have bounded VC-dimension. -/
theorem exists_vcDim_le (C : GraphClass) (hC : MonadicallyDependent C) :
    ∃ d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → vcDim G ≤ d :=
  exists_vcDim_le_of_not_hasIP C
    ((Lax185574Proofs.Shim.IndependenceProperty.monadicallyDependent_iff_forall_not_hasIP C).mp hC 0
      (edgeFormula 0))

end Lax185574Proofs.BoundedVC
