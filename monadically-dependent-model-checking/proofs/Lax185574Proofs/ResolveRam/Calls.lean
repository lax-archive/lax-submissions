import Lax185574Proofs.ResolveRam.OutputSize

/-!
The number of calls of the recursion of lem:resolve-lift (the paragraph
"Number of calls" of its proof). A call at depth `j` below a vertex `a`
is on the tree in `G` of a tuple reached from `a` by guarded extensions in
`H = resolve^±_{P,Q}(G)`. Its candidate extensions are trees in `G` of
tuples from the ball of radius `ρ⁺(k, q)` around `a` in `H`, by
lem:locality applied to `H`. So a call has at most `(j+1) T` distinct
candidates.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.TypeTrees Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax185574Proofs.TypeTreeSizes
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

/-- At most `T` nodes in `G` of rank `(k+i, q−i)` and arity `ℓ` belong to
tuples from the ball around `a` in `H`. -/
theorem ncard_nodes_treeCount (G H : PartialGraph (Fin n)) (k q : ℕ) (a : Fin n)
    (i m ℓ : ℕ) (hi : i ≤ q) (hm : m = q - i) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ k + i) :
    {μ : Node m ℓ | ∃ u : Fin ℓ → Fin n, (∀ t, u t ∈ H.ball (rhoPlus k q) a) ∧
      μ = node G (k + i) m u}.ncard ≤ treeCount G H k q := by
  refine le_trans ?_ (ncard_treeSet_le G H k q a)
  refine Set.ncard_le_ncard_of_injOn (fun μ => (⟨k + i, m, ℓ, μ⟩ : TypeTree)) ?_ ?_
    (treeSet_finite G H k q a)
  · rintro μ ⟨u, hu, rfl⟩
    refine ⟨i, ℓ, u, hi, h1, hℓ, hu, ?_⟩
    subst hm
    rfl
  · intro μ _ μ' _ h
    simp only [TypeTree.mk.injEq, heq_eq_eq, true_and] at h
    exact h

/-- **Number of candidates of a call.** At a tuple reached from `a` by
guarded extensions in `H`, the recursion has at most `(j+1) T` candidate
extensions. -/
theorem card_candidatesF_le (G : PartialGraph (Fin n)) (D : ResolveData) (ft : FarMap)
    {k q : ℕ} (hk : 1 ≤ k) (hD : D.Spec G k q) (hft : FarSpec G ft) (a : Fin n) (j m : ℕ)
    (hj : j + (m + 1) = q) (w : Fin (j + 1) → Fin n) (hw0 : w 0 = a)
    (hw : Guarded (resolveBy G D.sign D.P D.Q) k q j w) :
    (candidatesF D ft (k + j) m (j + 1) (node G (k + j) (m + 1) w)).card ≤
      (j + 1) * treeCount G (resolveBy G D.sign D.P D.Q) k q := by
  set H := resolveBy G D.sign D.P D.Q
  let Ch : Set (Node m (j + 1 + 1)) := {μ | ∃ u : Fin (j + 1 + 1) → Fin n,
    (∀ t, u t ∈ H.ball (rhoPlus k q) a) ∧ μ = node G (k + (j + 1)) m u}
  have hCh : Ch.ncard ≤ treeCount G H k q :=
    ncard_nodes_treeCount G H k q a (j + 1) m (j + 1 + 1) (by omega) (by omega) (by omega)
      (by omega)
  have hChfin : Ch.Finite :=
    (Set.finite_range fun u : Fin (j + 1 + 1) → Fin n => node G (k + (j + 1)) m u).subset
      (by rintro μ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)
  have hsub : (↑(candidatesF D ft (k + j) m (j + 1) (node G (k + j) (m + 1) w)) :
      Set (Fin (j + 1) × Node m (j + 1 + 1))) ⊆ (Set.univ : Set (Fin (j + 1))) ×ˢ Ch := by
    intro e he
    obtain ⟨i, b, hb, rfl⟩ := (mem_candidatesF D ft hD hft w (by omega) (by omega) (by omega)
      (by omega) e).1 he
    have hg : Guarded H k q (j + 1) (Fin.snoc w b) := by
      refine guarded_snoc hw i b ?_
      rwa [show q - (j + 1) = m by omega]
    refine ⟨Set.mem_univ _, Fin.snoc w b, fun t => ?_, rfl⟩
    have hloc := (Lax185574.TreeLocality.ball_of_guarded H k q (j + 1) (by omega)
      (Fin.snoc w b) hg).1 t
    rwa [snoc_zero, hw0] at hloc
  rw [← Set.ncard_coe_finset]
  calc _ ≤ ((Set.univ : Set (Fin (j + 1))) ×ˢ Ch).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_univ.prod hChfin)
    _ = (j + 1) * Ch.ncard := by
        rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    _ ≤ _ := Nat.mul_le_mul_left _ hCh

end Lax185574Proofs.ResolveRam
