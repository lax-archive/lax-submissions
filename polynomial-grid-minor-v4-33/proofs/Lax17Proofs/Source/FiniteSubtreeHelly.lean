import Lax17Proofs.Source.TreewidthBramble

namespace Lax17Proofs

universe u v w

/-!
# The finite subtree Helly property

Pairwise-intersecting connected induced subgraphs of a finite tree have a
common vertex.  The proof removes a leaf.  If the leaf is not common to the
whole family, every member containing it also contains its unique neighbour,
so deleting the leaf preserves connectedness and pairwise intersection.
-/

namespace SimpleGraph

namespace TreewidthBramble

private theorem connected_induce_delete_leaf
    {N : Type*} [Fintype N] [DecidableEq N]
    (T : _root_.SimpleGraph N) (S : Set N) (v : N)
    (hS : (T.induce S).Connected)
    (hv : (T.neighborSet v).Subsingleton)
    (hne : (S \ {v}).Nonempty) :
    ((T.induce {v}ᶜ).induce
      ({x : ({v}ᶜ : Set N) | (x : N) ∈ S} : Set ({v}ᶜ : Set N))).Connected := by
  classical
  rw [_root_.SimpleGraph.connected_iff]
  constructor
  · rintro ⟨⟨a, haS⟩, ha⟩ ⟨⟨b, hbS⟩, hb⟩
    obtain ⟨q, hq⟩ := hS.exists_isPath ⟨a, ha⟩ ⟨b, hb⟩
    let p : T.Walk a b :=
      q.map (_root_.SimpleGraph.Embedding.induce S).toHom
    have hp : p.IsPath := by
      change
        (q.map (_root_.SimpleGraph.Embedding.induce S).toHom).IsPath
      exact
        _root_.SimpleGraph.Walk.map_isPath_of_injective
          Subtype.val_injective hq
    have hvp : v ∉ p.support :=
      hp.isTrail.not_mem_support_of_subsingleton_neighborSet
        (Ne.symm (Set.mem_compl_singleton_iff.mp haS))
        (Ne.symm (Set.mem_compl_singleton_iff.mp hbS)) hv
    have hp_compl : ∀ x ∈ p.support, x ∈ ({v}ᶜ : Set N) := by
      intro x hx
      exact Set.mem_compl_singleton_iff.mpr fun h => hvp (h ▸ hx)
    have hp_S : ∀ x ∈ p.support, x ∈ S := by
      intro x hx
      change
        x ∈
          (q.map (_root_.SimpleGraph.Embedding.induce S).toHom).support at hx
      rw [_root_.SimpleGraph.Walk.support_map] at hx
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
      rw [← hyx]
      exact y.property
    let p' := p.induce ({v}ᶜ : Set N) hp_compl
    have hp'_S : ∀ x ∈ p'.support, (x : N) ∈ S := by
      intro x hx
      have hx' : (x : N) ∈ p.support := by
        simpa [p'] using hx
      exact hp_S x hx'
    let p'' := p'.induce
      ({x : ({v}ᶜ : Set N) | (x : N) ∈ S} : Set ({v}ᶜ : Set N)) hp'_S
    exact ⟨p''.copy (by rfl) (by rfl)⟩
  · obtain ⟨x, hxS, hxv⟩ := hne
    exact ⟨⟨⟨x, by simpa⟩, hxS⟩⟩

private theorem finiteSubtreeHelly_card (n : ℕ) :
    ∀ {I : Type*} [Fintype I] [DecidableEq I]
      {N : Type*} [Fintype N] [DecidableEq N]
      (T : _root_.SimpleGraph N) (S : I → Set N),
      Fintype.card N = n →
      T.IsTree →
      (∀ i, (T.induce (S i)).Connected) →
      (∀ i j, (S i ∩ S j).Nonempty) →
      ∃ x : N, ∀ i, x ∈ S i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro I _ _ N _ _ T S hcard hT hconn hinter
      classical
      by_cases hN : Nontrivial N
      · letI : Nontrivial N := hN
        obtain ⟨v, hvdeg⟩ := hT.exists_vert_degree_one_of_nontrivial
        by_cases hvall : ∀ i, v ∈ S i
        · exact ⟨v, hvall⟩
        · push Not at hvall
          obtain ⟨i₀, hi₀⟩ := hvall
          obtain ⟨u, hvu, hu⟩ :=
            _root_.SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hvdeg
          have hne : ∀ i, (S i \ {v}).Nonempty := by
            intro i
            obtain ⟨x, hxi, hxi₀⟩ := hinter i i₀
            exact ⟨x, hxi, fun hxv => hi₀ (hxv ▸ hxi₀)⟩
          have huS : ∀ i, v ∈ S i → u ∈ S i := by
            intro i hvi
            obtain ⟨x, hxi, hxv⟩ := hne i
            obtain ⟨q⟩ := hconn i ⟨v, hvi⟩ ⟨x, hxi⟩
            have hnq : ¬q.Nil :=
              _root_.SimpleGraph.Walk.not_nil_of_ne (by
              intro h
              exact hxv (Subtype.ext_iff.mp h).symm)
            let y := q.snd
            have hvy : T.Adj v y := q.adj_snd hnq
            have hyS : (y : N) ∈ S i := y.property
            simpa [hu _ hvy] using hyS
          let N' := ({v}ᶜ : Set N)
          let T' : _root_.SimpleGraph N' := T.induce ({v}ᶜ : Set N)
          let S' : I → Set N' := fun i => {x | (x : N) ∈ S i}
          have hT' : T'.IsTree := by
            constructor
            · exact hT.connected.induce_compl_singleton_of_degree_eq_one hvdeg
            · exact hT.isAcyclic.induce _
          have hconn' : ∀ i, (T'.induce (S' i)).Connected := by
            intro i
            exact connected_induce_delete_leaf T (S i) v (hconn i)
              (by
                intro a ha b hb
                exact (hu a ha).trans (hu b hb).symm)
              (hne i)
          have hinter' : ∀ i j, (S' i ∩ S' j).Nonempty := by
            intro i j
            obtain ⟨x, hxi, hxj⟩ := hinter i j
            by_cases hxv : x = v
            · refine ⟨⟨u, ?_⟩, huS i (hxv ▸ hxi), huS j (hxv ▸ hxj)⟩
              exact Set.mem_compl_singleton_iff.mpr hvu.ne.symm
            · exact ⟨⟨x, Set.mem_compl_singleton_iff.mpr hxv⟩, hxi, hxj⟩
          have hcard' : Fintype.card N' < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (p := fun x : N => x ∈ ({v}ᶜ : Set N))
              (x := v) (by simp)
          obtain ⟨⟨x, hxv⟩, hx⟩ :=
            ih (Fintype.card N') hcard' T' S' rfl hT' hconn' hinter'
          exact ⟨x, hx⟩
      · haveI : Subsingleton N := not_nontrivial_iff_subsingleton.mp hN
        let x := hT.connected.nonempty.some
        refine ⟨x, fun i => ?_⟩
        obtain ⟨y⟩ := (hconn i).nonempty
        simpa [Subsingleton.elim y.1 x] using y.property

/-- Pairwise-intersecting connected induced subgraphs of a finite tree have a
common vertex. -/
theorem finiteSubtreeHelly (I : Type*) [Fintype I] [DecidableEq I] :
    TreewidthBramble.FiniteSubtreeHelly I := by
  intro N _ _ T S hT hconn hinter
  exact finiteSubtreeHelly_card (Fintype.card N) T S rfl hT hconn hinter

end TreewidthBramble

end SimpleGraph

end Lax17Proofs
