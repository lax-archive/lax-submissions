import Lax185574.ScatterTypes
import Lax185574Proofs.WalkDistance

/-!
Properties of the greedy scattered set `S_r(X)` of def:stp: its members
lie in `X`, are pairwise at distance larger than `r`, and every vertex of
`X` is within distance `r` of a member. So it is an inclusion-wise maximal
`r`-scattered subset of `X`, as lem:clustering requires.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.ScatterTypes
open Lax185574Proofs.WalkDistance

variable {n : ℕ}

theorem greedy_foldl (G : PartialGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    ∀ (L S : List (Fin n)), (∀ x ∈ S, x ∈ X) →
      S.Pairwise (fun x y => ¬ WithinDist G.resolved r x y) →
      let T := (open Classical in L.foldl (fun S v =>
        if v ∈ X ∧ ∀ u ∈ S, ¬ WithinDist G.resolved r u v then S ++ [v] else S) S)
      (∀ x ∈ T, x ∈ X) ∧ T.Pairwise (fun x y => ¬ WithinDist G.resolved r x y) ∧
        (∀ y ∈ S, y ∈ T) ∧ (∀ x ∈ L, x ∈ X → ∃ y ∈ T, WithinDist G.resolved r y x)
  | [], S, hX, hP => by
    simp only [List.foldl_nil, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hX, hP, fun _ h => h⟩
  | v :: L, S, hX, hP => by
    simp only [List.foldl_cons]
    split_ifs with hv
    · have hX' : ∀ x ∈ S ++ [v], x ∈ X := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hX x hx
        · rw [List.mem_singleton.1 hx]; exact hv.1
      have hP' : (S ++ [v]).Pairwise (fun x y => ¬ WithinDist G.resolved r x y) := by
        rw [List.pairwise_append]
        exact ⟨hP, List.pairwise_singleton _ _, fun a ha b hb => by
          rw [List.mem_singleton.1 hb]; exact hv.2 a ha⟩
      obtain ⟨h1, h2, h3, h4⟩ := greedy_foldl G r X L (S ++ [v]) hX' hP'
      refine ⟨h1, h2, fun y hy => h3 y (List.mem_append_left _ hy), ?_⟩
      intro x hx hxX
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨x, h3 x (List.mem_append_right _ (List.mem_singleton_self x)),
          withinDist_refl _ _ _⟩
      · exact h4 x hx hxX
    · obtain ⟨h1, h2, h3, h4⟩ := greedy_foldl G r X L S hX hP
      refine ⟨h1, h2, h3, ?_⟩
      intro x hx hxX
      rcases List.mem_cons.1 hx with rfl | hx
      · have : ∃ u ∈ S, WithinDist G.resolved r u x := by
          by_contra hc
          push Not at hc
          exact hv ⟨hxX, hc⟩
        obtain ⟨u, hu, hux⟩ := this
        exact ⟨u, h3 u hu, hux⟩
      · exact h4 x hx hxX

/-- The members of `S_r(X)` lie in `X`, are pairwise not within distance
`r`, and cover `X` within distance `r`. -/
theorem greedyScattered_spec (G : PartialGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    (∀ x ∈ greedyScattered G r X, x ∈ X) ∧
      (greedyScattered G r X).Pairwise (fun x y => ¬ WithinDist G.resolved r x y) ∧
      (∀ x ∈ X, ∃ y ∈ greedyScattered G r X, WithinDist G.resolved r y x) := by
  obtain ⟨h1, h2, -, h4⟩ := greedy_foldl G r X (List.finRange n) [] (by simp) List.Pairwise.nil
  exact ⟨h1, h2, fun x hx => h4 x (List.mem_finRange x) hx⟩

theorem greedyScattered_nodup (G : PartialGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    (greedyScattered G r X).Nodup :=
  (greedyScattered_spec G r X).2.1.imp fun {a b} h hab => by subst hab; exact h (withinDist_refl _ _ _)

/-- The set of members of `S_r(X)`, as used in lem:clustering. -/
theorem greedyScattered_set (G : PartialGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    let S : Set (Fin n) := {x | x ∈ greedyScattered G r X}
    S ⊆ X ∧ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ WithinDist G.resolved r x y) ∧
      (∀ x ∈ X, ∃ y ∈ S, WithinDist G.resolved r x y) ∧
      S.ncard = (greedyScattered G r X).length := by
  obtain ⟨h1, h2, h3⟩ := greedyScattered_spec G r X
  refine ⟨fun x hx => h1 x hx, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have : Std.Symm (fun x y : Fin n => ¬ WithinDist G.resolved r x y) :=
      ⟨fun a b h h' => h (withinDist_symm h')⟩
    exact h2.forall hx hy hxy
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := h3 x hx
    exact ⟨y, hy, withinDist_symm hyx⟩
  · have := List.toFinset_card_of_nodup (greedyScattered_nodup G r X)
    rw [← this, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp

end Lax185574Proofs.TreeAlgo
