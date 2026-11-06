import Lax185574.DpMinimalVC
import Lax185574Proofs.BoundedVC
import Lax185574Proofs.DefinableFlipFormula

/-!
The VC-dimension of a dp-minimal class is bounded: a shattered set of
size `2t` carries a clean pattern of order `t × t` for the edge formula.
-/

namespace Lax185574Proofs.DpMinimalVC

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.PhiPsiPatterns Lax185574.DpMinimality
open Lax185574.VCDimension
open Lax185574Proofs.BoundedVC Lax185574Proofs.DefinableFlipFormula

universe u

variable {V : Type u}

/-- The edge formula `E(x, z)`. -/
def edgeF : Language.graph.Formula (Fin 1 ⊕ Fin 1) := adjF (Sum.inl 0) (Sum.inr 0)

theorem holds_edgeF (G : SimpleGraph V) (a : Fin 1 → V) (c : V) :
    Holds G edgeF a c ↔ G.Adj (a 0) c :=
  Iff.rfl

/-- A shattered set of size at least `2t` carries a clean
`(E, E)`-pattern of order `t × t`. -/
theorem hasCleanPattern_of_shatters {G : SimpleGraph V} {A : Finset V} (hA : Shatters G A)
    {t : ℕ} (ht : 2 * t ≤ A.card) : HasCleanPattern G edgeF edgeF t t := by
  classical
  obtain ⟨A', hA'A, hA'⟩ := Finset.exists_subset_card_eq ht
  have hsh : Shatters G A' := shatters_mono hA'A hA
  let e : Fin (t + t) ≃ A' := (A'.equivFinOfCardEq (by omega)).symm
  let a : Fin t → V := fun i => e (Fin.castAdd t i)
  let b : Fin t → V := fun j => e (Fin.natAdd t j)
  have hmem : ∀ k, (e k : V) ∈ A' := fun k => (e k).2
  have hinj : ∀ k k', (e k : V) = e k' ↔ k = k' := fun k k' =>
    ⟨fun h => e.injective (Subtype.ext h), fun h => by rw [h]⟩
  have haa : ∀ i i', a i' = a i ↔ i' = i := fun i i' => by
    simp only [a, hinj, Fin.castAdd_inj]
  have hbb : ∀ j j', b j' = b j ↔ j' = j := fun j j' => by
    simp only [b, hinj, Fin.natAdd_inj]
  have hab : ∀ i j, a i ≠ b j := fun i j h => by
    have h' := congrArg Fin.val ((hinj _ _).mp h)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  have wit : ∀ i j, ∃ v, ∀ x ∈ A', (G.Adj v x ↔ x ∈ ({a i, b j} : Finset V)) := fun i j => by
    refine hsh _ fun x hx => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem _
    · exact hmem _
  choose c hc using wit
  refine ⟨fun i _ => a i, fun j _ => b j, c, fun i j => ⟨fun i' => ?_, fun j' => ?_⟩⟩
  · rw [holds_edgeF, G.adj_comm, hc i j _ (hmem _), Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (haa i i').mp fun h => absurd h (hab i' j), fun h => Or.inl (by rw [h])⟩
  · rw [holds_edgeF, G.adj_comm, hc i j _ (hmem _), Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun h => absurd h.symm (hab i j')) (hbb j j').mp,
      fun h => Or.inr (by rw [h])⟩

/--
---
conclusion: Lax185574.DpMinimalVC.exists_vcDim_le
---
Let `t` be such that no graph of the class contains a clean
`(E, E)`-pattern of order `t × t` for the edge formula `E(x, z)`. A set
shattered in a graph of the class has fewer than `2t` elements. Otherwise
it contains distinct vertices `a₁, …, a_t, b₁, …, b_t`, and for all `i, j`
shattering gives a vertex `c_{i,j}` whose neighbors among these are
exactly `aᵢ` and `bⱼ`. These form a clean pattern of order `t × t`.
-/
theorem exists_vcDim_le (C : GraphClass) (hC : DpMinimal C) :
    ∃ d : ℕ, ∀ G ∈ C, vcDim G.toSimpleGraph ≤ d := by
  obtain ⟨t, ht⟩ := hC edgeF edgeF
  refine ⟨2 * t, fun G hG => vcDim_le_of_forall_card_lt _ _ fun A hA => ?_⟩
  by_contra hlt
  exact ht G hG (hasCleanPattern_of_shatters hA (not_lt.mp hlt))

end Lax185574Proofs.DpMinimalVC
