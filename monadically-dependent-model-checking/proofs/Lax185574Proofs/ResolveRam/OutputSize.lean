import Lax185574Proofs.ResolveRam.FarMapOf
import Lax185574Proofs.ResolveRam.SizeBound

/-!
The size of the output trees of lem:resolve-lift (its last sentence). By
the recursion of the lemma, the tree in `H = resolve^±_{P,Q}(G)` of a tuple
is a function of its tree in `G`. So the number of trees in `H` of tuples
from a ball is at most the number of their trees in `G`, which is at most
`T`. The colors that meet the ball are at most `T` as well, since the tree
of a vertex records its color. By lem:locality applied to `H`, the tree
of a vertex in `H` has size polynomial in such a bound.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

/-- Correct data of the resolve for `G` at the rank `(k, q)`. -/
theorem exists_resolveData (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k q : ℕ) :
    ∃ D : ResolveData, D.P = P ∧ D.Q = Q ∧ D.sign = s ∧ D.Spec G k q := by
  classical
  let adj : Fin n → List (Fin n) := fun u => (Finset.univ.filter fun v => G.resolved.Adj u v).toList
  have hadj : ∀ u v, v ∈ adj u ↔ G.resolved.Adj u v := by
    intro u v
    simp [adj]
  exact ⟨_, rfl, rfl, rfl, resolveData_spec hadj P Q s k q⟩

/-- **The tree after the resolve is a function of the tree before.** -/
theorem exists_lift (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k q : ℕ) :
    ∃ F : (i m ℓ : ℕ) → Node m ℓ → Node m ℓ, ∀ (i m ℓ : ℕ) (u : Fin ℓ → Fin n),
      i ≤ q → m = q - i → 1 ≤ ℓ → ℓ ≤ k + i →
        F i m ℓ (node G (k + i) m u) = node (resolveBy G s P Q) (k + i) m u := by
  obtain ⟨D, rfl, rfl, rfl, hD⟩ := exists_resolveData G P Q s k q
  refine ⟨fun i m _ t => resolveNodeF D (farMapOf G) (k + i) m t, ?_⟩
  intro i m ℓ u hi hm h1 hℓ
  exact resolveNodeF_node D (farMapOf G) hD (farSpec_farMapOf G) m (k + i) u h1 hℓ (by omega)
    (by omega)

/-- The set whose size is `T` at the vertex `a`. -/
def treeSet (G H : PartialGraph (Fin n)) (k q : ℕ) (a : Fin n) : Set TypeTree :=
  {τ : TypeTree | ∃ (i ℓ : ℕ) (v : Fin ℓ → Fin n), i ≤ q ∧ 1 ≤ ℓ ∧ ℓ ≤ k + i ∧
      (∀ j, v j ∈ H.ball (rhoPlus k q) a) ∧ τ = tree G (k + i) (q - i) v}

theorem treeSet_finite (G H : PartialGraph (Fin n)) (k q : ℕ) (a : Fin n) :
    (treeSet G H k q a).Finite := by
  refine (Set.Finite.biUnion (Set.finite_Iic q) fun i _ =>
    Set.Finite.biUnion (Set.finite_Iic (k + q)) fun ℓ _ =>
      Set.finite_range fun v : Fin ℓ → Fin n => tree G (k + i) (q - i) v).subset ?_
  rintro τ ⟨i, ℓ, v, hi, -, hℓ, -, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_range]
  exact ⟨i, hi, ℓ, by omega, v, rfl⟩

theorem ncard_treeSet_le (G H : PartialGraph (Fin n)) (k q : ℕ) (a : Fin n) :
    (treeSet G H k q a).ncard ≤ treeCount G H k q :=
  Finset.le_sup (f := fun a => (treeSet G H k q a).ncard) (Finset.mem_univ a)

/-- The counting hypotheses hold in `H` with `K = T`. -/
theorem ballCounts_resolve (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k q : ℕ)
    (hk : 1 ≤ k) (a : Fin n) :
    BallCounts (resolveBy G s P Q) k q a (treeCount G (resolveBy G s P Q) k q) := by
  classical
  set H := resolveBy G s P Q
  set X := H.ball (rhoPlus k q) a
  set S := treeSet G H k q a
  have hHc : H.color = G.color := resolveBy_color G s P Q
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ (ncard_treeSet_le G H k q a)
    have hrep : ∀ Y ∈ H.color '' X, ∃ u ∈ X, H.color u = Y := fun Y hY => hY
    have : Nonempty (Fin n) := ⟨a⟩
    choose! rep hrepX hrepc using hrep
    refine Set.ncard_le_ncard_of_injOn (fun Y => tree G k q ![rep Y]) ?_ ?_ (treeSet_finite G H k q a)
    · intro Y hY
      exact ⟨0, 1, ![rep Y], Nat.zero_le q, le_rfl, by omega,
        fun j => by fin_cases j; exact hrepX Y hY, rfl⟩
    · intro Y hY Y' hY' h
      simp only [tree, TypeTree.mk.injEq, heq_eq_eq, true_and] at h
      have hm : DistFO.color Y (0 : Fin 1) ∈ Node.atoms (node G k q ![rep Y]) :=
        (mem_atoms_node G k q _ _).2 ⟨trivial, .color _ _, by
          simpa [Sat, hHc] using hrepc Y hY⟩
      rw [h] at hm
      obtain ⟨-, -, hs⟩ := (mem_atoms_node G k q _ _).1 hm
      have h' := hrepc Y' hY'
      rw [hHc] at h'
      simp only [Sat, Matrix.cons_val_fin_one] at hs
      rw [← hs, h']
  · intro i m ℓ hi hm h1 hℓ
    obtain ⟨F, hF⟩ := exists_lift G P Q s k q
    let NG : Set (Node m ℓ) := {μ | ∃ u : Fin ℓ → Fin n, (∀ t, u t ∈ X) ∧ μ = node G (k + i) m u}
    have hNGfin : NG.Finite :=
      (Set.finite_range fun u : Fin ℓ → Fin n => node G (k + i) m u).subset
        (by rintro μ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)
    have hsub : {μ : Node m ℓ | ∃ u : Fin ℓ → Fin n, (∀ t, u t ∈ X) ∧
        μ = node H (k + i) m u} ⊆ F i m ℓ '' NG := by
      rintro μ ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, hF i m ℓ u hi hm h1 hℓ⟩
    have hG : NG.ncard ≤ S.ncard := by
      refine Set.ncard_le_ncard_of_injOn (fun μ => (⟨k + i, m, ℓ, μ⟩ : TypeTree)) ?_ ?_
        (treeSet_finite G H k q a)
      · rintro μ ⟨u, hu, rfl⟩
        refine ⟨i, ℓ, u, hi, h1, hℓ, hu, ?_⟩
        subst hm
        rfl
      · intro μ _ μ' _ h
        simp only [TypeTree.mk.injEq, heq_eq_eq, true_and] at h
        exact h
    calc _ ≤ (F i m ℓ '' NG).ncard := Set.ncard_le_ncard hsub (hNGfin.image _)
      _ ≤ NG.ncard := Set.ncard_image_le hNGfin
      _ ≤ S.ncard := hG
      _ ≤ _ := ncard_treeSet_le G H k q a

/-- **Output size of lem:resolve-lift.** Each output tree has size
polynomial in `T`. -/
theorem output_size (k q : ℕ) (hk : 1 ≤ k) :
    ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (b : Fin n),
      wordLength (tree (resolveBy G s P Q) k q ![b]) ≤
        c * (treeCount G (resolveBy G s P Q) k q + 1) ^ a := by
  obtain ⟨c, a, h⟩ := tree_length_le_of k q hk
  exact ⟨c, a, fun n G P Q s b => h n _ b _ (ballCounts_resolve G P Q s k q hk b)⟩

end Lax185574Proofs.ResolveRam
