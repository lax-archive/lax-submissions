import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Positivity

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-!
An explicit (deliberately generous) two-color Ramsey bound.

The induction below is adapted from
`Lax345067Proofs.PairRamsey.ramsey`, finite-ramsey-v4-33, commit
feabf43dcd6967ac912b2064003ea715e06e58f9, originally ported from the
monadic-dependence and neighborhood-complexity submission. The only
mathematical change is to majorize the recursive thresholds by `3^(a+b)`.
This retains a directly computable bound for bipartite pattern extraction.
-/

namespace Lax185574Proofs.Lib.ExplicitRamsey

universe u
open SimpleGraph Finset

theorem compl_induce_eq {V : Type u} {s : Set V} (G : SimpleGraph V) :
    (G.induce s)ᶜ = Gᶜ.induce s := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  simp only [compl_adj, induce_adj, ne_eq, Subtype.mk.injEq]

theorem ramsey (a b : ℕ) {V : Type u} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : 3 ^ (a + b) ≤ Fintype.card V) :
    ¬G.CliqueFree a ∨ ¬Gᶜ.CliqueFree b := by
  classical
  suffices h : ∀ n a b, a + b = n →
      ∀ {V : Type u} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
      3 ^ n ≤ Fintype.card V → ¬G.CliqueFree a ∨ ¬Gᶜ.CliqueFree b from
    h (a + b) a b rfl G hcard
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a b hab
    -- Base cases: a = 0 or b = 0
    match a, b, hab with
    | 0, _, _ =>
      exact fun _ _ _ _ _ _ => Or.inl not_cliqueFree_zero
    | _, 0, _ =>
      exact fun _ _ _ _ _ _ => Or.inr not_cliqueFree_zero
    | a' + 1, b' + 1, hab =>
      -- IH for (a', b'+1) and (a'+1, b')
      let N1 := 3 ^ (a' + b' + 1)
      let N2 := N1
      have hN1 : ∀ {W : Type u} [DecidableEq W] [Fintype W]
          (H : SimpleGraph W) [DecidableRel H.Adj], N1 ≤ Fintype.card W →
          ¬H.CliqueFree a' ∨ ¬Hᶜ.CliqueFree (b' + 1) :=
        ih (a' + b' + 1) (by omega) a' (b' + 1) (by omega)
      have hN2 : ∀ {W : Type u} [DecidableEq W] [Fintype W]
          (H : SimpleGraph W) [DecidableRel H.Adj], N2 ≤ Fintype.card W →
          ¬H.CliqueFree (a' + 1) ∨ ¬Hᶜ.CliqueFree b' :=
        ih (a' + b' + 1) (by omega) (a' + 1) b' (by omega)
      intro V _ _ G _ hcard
      have hp : 0 < N1 := by dsimp [N1]; positivity
      have hbound : N1 + N2 + 1 ≤ Fintype.card V := by
        have he : n = (a' + b' + 1) + 1 := by omega
        rw [he, pow_succ] at hcard
        dsimp [N1, N2] at *
        omega
      -- Pick a vertex v
      have hne : 0 < Fintype.card V := by omega
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hne
      -- Neighbors and non-neighbors of v
      set A := G.neighborFinset v with hA_def
      set B := Finset.univ.erase v \ A with hB_def
      -- A ⊆ univ.erase v (since v is not its own neighbor)
      have hA_sub : A ⊆ Finset.univ.erase v := by
        intro w hw
        rw [Finset.mem_erase]
        exact ⟨(G.ne_of_adj ((G.mem_neighborFinset v w).mp hw)).symm, Finset.mem_univ _⟩
      -- |A| + |B| = |V| - 1
      have hAB : A.card + B.card + 1 = Fintype.card V := by
        have h1 : B ∪ A = Finset.univ.erase v :=
          Finset.sdiff_union_of_subset hA_sub
        have h2 : Disjoint B A := Finset.sdiff_disjoint
        have h3 := Finset.card_union_of_disjoint h2
        have h4 := Finset.card_erase_of_mem (Finset.mem_univ v)
        rw [h1] at h3; rw [Finset.card_univ] at h4
        omega
      -- Pigeonhole: |A| ≥ N1 or |B| ≥ N2
      rcases Nat.lt_or_ge A.card N1 with hAlt | hAge
      · -- Case 2: |A| < N1, so |B| ≥ N2
        have hBge : N2 ≤ B.card := by omega
        have hcB : N2 ≤ Fintype.card ↑(B : Set V) := by
          rw [Fintype.card_of_finset' B (fun x => Iff.rfl)]
          exact hBge
        rcases hN2 (G.induce (↑B : Set V)) hcB with h1 | h2
        · exact Or.inl <| mt
            (SimpleGraph.CliqueFree.comap
              (G := G) (H := G.induce (↑B : Set V))
              (SimpleGraph.Embedding.induce (G := G) (↑B : Set V)).isContained)
            h1
        · have h2' : ¬(Gᶜ.induce (↑B : Set V)).CliqueFree b' := by
            simpa [compl_induce_eq G] using h2
          obtain ⟨t, ht⟩ := Classical.not_forall.mp h2'
          have ht : (Gᶜ.induce (↑B : Set V)).IsNClique b' t := not_not.mp ht
          let t' : Finset V := t.map ⟨Subtype.val, Subtype.val_injective⟩
          have ht' : Gᶜ.IsNClique b' t' := by
            exact (ht.map (f := ⟨Subtype.val, Subtype.val_injective⟩)).mono
              (SimpleGraph.spanningCoe_induce_le (G := Gᶜ) (↑B : Set V))
          have hv_adj : ∀ w ∈ t', Gᶜ.Adj v w := by
            intro w hw
            rcases Finset.mem_map.mp hw with ⟨x, hx, rfl⟩
            have hxB : x.1 ∈ Finset.univ.erase v \ A := by
              exact hB_def ▸ x.2
            have hxsdiff : x.1 ∈ Finset.univ.erase v ∧ x.1 ∉ A := by
              exact Finset.mem_sdiff.mp hxB
            have hxne : v ≠ x.1 := by
              exact (Finset.mem_erase.mp hxsdiff.1).1.symm
            have hxnotadj : ¬G.Adj v x.1 := by
              intro hvx
              exact hxsdiff.2 ((G.mem_neighborFinset v x.1).2 hvx)
            rw [SimpleGraph.compl_adj]
            exact ⟨hxne, hxnotadj⟩
          exact Or.inr (ht'.insert hv_adj).not_cliqueFree
      · -- Case 1: |A| ≥ N1 — apply IH to G.induce ↑A
        have hcA : N1 ≤ Fintype.card ↑(A : Set V) := by
          rw [Fintype.card_of_finset' A (fun x => Iff.rfl)]
          exact hAge
        rcases hN1 (G.induce (↑A : Set V)) hcA with h1 | h2
        · -- Found a'-clique in induced subgraph — extend with v
          obtain ⟨s, hs⟩ := Classical.not_forall.mp h1
          have hs : (G.induce (↑A : Set V)).IsNClique a' s := not_not.mp hs
          let s' : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
          have hs' : G.IsNClique a' s' := by
            exact (hs.map (f := ⟨Subtype.val, Subtype.val_injective⟩)).mono
              (SimpleGraph.spanningCoe_induce_le (G := G) (↑A : Set V))
          have hv_adj : ∀ w ∈ s', G.Adj v w := by
            intro w hw
            rcases Finset.mem_map.mp hw with ⟨x, hx, rfl⟩
            have hxA : x.1 ∈ G.neighborFinset v := by
              exact x.2
            simpa using (G.mem_neighborFinset v x.1).mp hxA
          exact Or.inl (hs'.insert hv_adj).not_cliqueFree
        · -- Found (b'+1)-independent set — transfer to Gᶜ
          have h2' : ¬(Gᶜ.induce (↑A : Set V)).CliqueFree (b' + 1) := by
            simpa [compl_induce_eq G] using h2
          exact Or.inr <| mt
            (SimpleGraph.CliqueFree.comap
              (G := Gᶜ) (H := Gᶜ.induce (↑A : Set V))
              (SimpleGraph.Embedding.induce (G := Gᶜ) (↑A : Set V)).isContained)
            h2'


end Lax185574Proofs.Lib.ExplicitRamsey
