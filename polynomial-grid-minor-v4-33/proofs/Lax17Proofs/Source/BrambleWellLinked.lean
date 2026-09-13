import Lax17Proofs.Source.Menger
import Lax17Proofs.Source.TreewidthSparsifierContract

namespace Lax17Proofs

universe u v w

/-!
# Minimum bramble transversals are node-well-linked

This file formalizes the Harvey--Wood argument.  If a small separator split
two equally large subsets of a minimum bramble hitting set, all bramble sets
avoiding the separator would lie in one component of the graph with the
separator deleted.  Replacing the part of the hitting set outside that
component by the separator would then give a smaller hitting set.
-/

namespace SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Two finite vertex sets touch if they intersect or an edge has one endpoint
in each set. -/
def FinsetTouching (G : _root_.SimpleGraph V) (A B : Finset V) : Prop :=
  (A ∩ B).Nonempty ∨
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

/-- A finite bramble: a finite family of nonempty connected vertex sets whose
distinct members pairwise touch. -/
structure FiniteBramble (G : _root_.SimpleGraph V) where
  sets : Finset (Finset V)
  nonempty : ∀ ⦃A⦄, A ∈ sets → A.Nonempty
  connected : ∀ ⦃A⦄, A ∈ sets →
    (G.induce {v : V | v ∈ A}).Connected
  touching : ∀ ⦃A⦄, A ∈ sets → ∀ ⦃B⦄, B ∈ sets →
    A ≠ B → FinsetTouching G A B

namespace FiniteBramble

variable {G : _root_.SimpleGraph V}

/-- A finite vertex set hits a bramble if it meets every member. -/
def IsHittingSet (B : FiniteBramble G) (H : Finset V) : Prop :=
  ∀ A ∈ B.sets, ∃ v ∈ A, v ∈ H

/-- A minimum hitting set has minimum cardinality among all bramble hitting
sets. -/
def IsMinimumHittingSet (B : FiniteBramble G) (H : Finset V) : Prop :=
  B.IsHittingSet H ∧
    ∀ H' : Finset V, B.IsHittingSet H' → H.card ≤ H'.card

/-- Every finite bramble has a minimum-cardinality hitting set. -/
theorem exists_minimumHittingSet (B : FiniteBramble G) :
    ∃ H : Finset V, B.IsMinimumHittingSet H := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ H : Finset V, B.IsHittingSet H ∧ H.card = n
  have hex : ∃ n, P n := by
    refine ⟨Fintype.card V, Finset.univ, ?_, by simp⟩
    intro A hAB
    rcases B.nonempty hAB with ⟨v, hvA⟩
    exact ⟨v, hvA, by simp⟩
  rcases Nat.find_spec hex with ⟨H, hHhit, hHcard⟩
  refine ⟨H, hHhit, ?_⟩
  intro H' hH'hit
  have hmin : Nat.find hex ≤ H'.card :=
    Nat.find_min' hex ⟨H', hH'hit, rfl⟩
  simpa [hHcard] using hmin

private abbrev deletedGraph (G : _root_.SimpleGraph V) (X : Finset V) :=
  G.induce {v : V | v ∉ X}

private theorem component_eq_of_connected_finset
    {X A : Finset V}
    (hconn : (G.induce {v : V | v ∈ A}).Connected)
    (hAX : Disjoint A X) {a b : V} (ha : a ∈ A) (hb : b ∈ A) :
    (deletedGraph G X).connectedComponentMk
        ⟨a, Finset.disjoint_left.mp hAX ha⟩ =
      (deletedGraph G X).connectedComponentMk
        ⟨b, Finset.disjoint_left.mp hAX hb⟩ := by
  let f : G.induce {v : V | v ∈ A} →g deletedGraph G X :=
    _root_.SimpleGraph.induceHom (_root_.SimpleGraph.Hom.id) (by
      intro v hv
      exact Finset.disjoint_left.mp hAX hv)
  apply _root_.SimpleGraph.ConnectedComponent.sound
  exact (hconn.preconnected ⟨a, ha⟩ ⟨b, hb⟩).map f

private theorem component_eq_of_touching_finsets
    {X A B : Finset V}
    (hAconn : (G.induce {v : V | v ∈ A}).Connected)
    (hBconn : (G.induce {v : V | v ∈ B}).Connected)
    (hAX : Disjoint A X) (hBX : Disjoint B X)
    (htouch : FinsetTouching G A B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    (deletedGraph G X).connectedComponentMk
        ⟨a, Finset.disjoint_left.mp hAX ha⟩ =
      (deletedGraph G X).connectedComponentMk
        ⟨b, Finset.disjoint_left.mp hBX hb⟩ := by
  rcases htouch with hinter | hadj
  · rcases hinter with ⟨z, hz⟩
    have hzA : z ∈ A := (Finset.mem_inter.mp hz).1
    have hzB : z ∈ B := (Finset.mem_inter.mp hz).2
    exact
      (component_eq_of_connected_finset hAconn hAX ha hzA).trans
        (component_eq_of_connected_finset hBconn hBX hb hzB).symm
  · rcases hadj with ⟨x, hxA, y, hyB, hxy⟩
    have hxX : x ∉ X := Finset.disjoint_left.mp hAX hxA
    have hyX : y ∉ X := Finset.disjoint_left.mp hBX hyB
    have hxy' : (deletedGraph G X).Adj ⟨x, hxX⟩ ⟨y, hyX⟩ := hxy
    exact
      (component_eq_of_connected_finset hAconn hAX ha hxA).trans
        ((_root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy').trans
          (component_eq_of_connected_finset hBconn hBX hb hyB).symm)

private theorem not_deleted_reachable_of_separator
    {S T X : Finset V} (hsep : STSeparator G S T X)
    {s t : V} (hs : s ∈ S) (ht : t ∈ T) (hsX : s ∉ X) (htX : t ∉ X) :
    ¬ (deletedGraph G X).Reachable ⟨s, hsX⟩ ⟨t, htX⟩ := by
  intro hreach
  rcases hreach with ⟨W⟩
  let e : deletedGraph G X →g G :=
    (_root_.SimpleGraph.Embedding.induce (G := G) {v : V | v ∉ X}).toHom
  let W' : G.Walk s t := W.map e
  let P : GraphPath G := GraphPath.ofWalk W'
  have hconnects : P.Connects S T := Or.inl ⟨hs, ht⟩
  rcases hsep P hconnects with ⟨v, hvP, hvX⟩
  have hvW' : v ∈ W'.support.toFinset :=
    GraphPath.ofWalk_vertexSet_subset W' hvP
  have hvOutside : v ∉ X := by
    have hvList : v ∈ W'.support := by simpa using hvW'
    change v ∈ (W.map e).support at hvList
    rw [_root_.SimpleGraph.Walk.support_map] at hvList
    rcases List.mem_map.mp hvList with ⟨w, _hwW, hwv⟩
    change (w : V) = v at hwv
    exact hwv ▸ w.2
  exact hvOutside hvX

private theorem replacement_card_lt
    {H X C S : Finset V}
    (hSH : S ⊆ H) (hcard : X.card < S.card)
    (hSC : Disjoint (S \ X) C) :
    (X ∪ H.filter fun v => v ∈ C).card < H.card := by
  let H' := X ∪ H.filter fun v => v ∈ C
  have hadd : H' \ H ⊆ X \ H := by
    intro v hv
    have hvH' : v ∈ H' := (Finset.mem_sdiff.mp hv).1
    have hvH : v ∉ H := (Finset.mem_sdiff.mp hv).2
    have hvX : v ∈ X := by
      rcases Finset.mem_union.mp hvH' with hvX | hvfilter
      · exact hvX
      · exact False.elim (hvH (Finset.mem_filter.mp hvfilter).1)
    exact Finset.mem_sdiff.mpr ⟨hvX, hvH⟩
  have hremove : S \ X ⊆ H \ H' := by
    intro v hv
    have hvS : v ∈ S := (Finset.mem_sdiff.mp hv).1
    have hvX : v ∉ X := (Finset.mem_sdiff.mp hv).2
    have hvC : v ∉ C := by
      intro hvC
      exact Finset.disjoint_left.mp hSC hv hvC
    refine Finset.mem_sdiff.mpr ⟨hSH hvS, ?_⟩
    intro hvH'
    rcases Finset.mem_union.mp hvH' with hvX' | hvfilter
    · exact hvX hvX'
    · exact hvC (Finset.mem_filter.mp hvfilter).2
  have hinter_card : (S ∩ X).card ≤ (X ∩ H).card := by
    apply Finset.card_le_card
    intro v hv
    have hvS : v ∈ S := (Finset.mem_inter.mp hv).1
    have hvX : v ∈ X := (Finset.mem_inter.mp hv).2
    exact Finset.mem_inter.mpr ⟨hvX, hSH hvS⟩
  have hnew_lt_removed : (X \ H).card < (S \ X).card := by
    have hXparts := Finset.card_sdiff_add_card_inter X H
    have hSparts := Finset.card_sdiff_add_card_inter S X
    omega
  have hdiff : (H' \ H).card < (H \ H').card :=
    (Finset.card_le_card hadd).trans_lt
      (hnew_lt_removed.trans_le (Finset.card_le_card hremove))
  exact (Finset.card_sdiff_lt_card_sdiff_iff).mp hdiff

/-- A minimum-cardinality hitting set of a finite bramble is node-well-linked
in the paper's equal-size perfect-packing sense. -/
theorem minimumHittingSet_paperNodeWellLinked
    (B : FiniteBramble G) {H : Finset V}
    (hH : B.IsMinimumHittingSet H) :
    TreewidthSparsifier.PaperNodeWellLinked G H := by
  classical
  refine ⟨by simp, ?_⟩
  intro A D hAH hDH hcardAD
  let k := A.card
  rcases Menger.finite_vertex_menger_sharp (G := G) A D k with hpaths | hsmall
  · rcases HasAtLeastDisjointPaths.exists_exact hpaths with ⟨P, hPcard⟩
    have hPcardD : P.card = D.card := hPcard.trans hcardAD
    let Q : PerfectPathPacking G A D := P.toPerfectOfCardEq hPcard hPcardD
    refine ⟨Q, ?_⟩
    intro i v hv
    simp
  · rcases hsmall with ⟨X, hXcard, hsep⟩
    have hXltA : X.card < A.card := by simpa [k] using hXcard
    by_cases hXhits : B.IsHittingSet X
    · have hAHcard : A.card ≤ H.card := Finset.card_le_card hAH
      have hmin := hH.2 X hXhits
      omega
    · have havoid_exists : ∃ W ∈ B.sets, Disjoint W X := by
        by_contra hnone
        apply hXhits
        intro W hWB
        have hnWX : ¬ Disjoint W X := by
          intro hWX
          exact hnone ⟨W, hWB, hWX⟩
        rw [Finset.not_disjoint_iff] at hnWX
        rcases hnWX with ⟨v, hvW, hvX⟩
        exact ⟨v, hvW, hvX⟩
      rcases havoid_exists with ⟨W₀, hW₀B, hW₀X⟩
      rcases B.nonempty hW₀B with ⟨r, hrW₀⟩
      have hrX : r ∉ X := Finset.disjoint_left.mp hW₀X hrW₀
      let K := deletedGraph G X
      let c := K.connectedComponentMk ⟨r, hrX⟩
      let C : Finset V := Finset.univ.filter fun v =>
        ∃ hvX : v ∉ X, K.connectedComponentMk ⟨v, hvX⟩ = c
      have havoiding_subset_C :
          ∀ ⦃W : Finset V⦄, W ∈ B.sets → Disjoint W X → W ⊆ C := by
        intro W hWB hWX v hvW
        have hvX : v ∉ X := Finset.disjoint_left.mp hWX hvW
        have hcomp : K.connectedComponentMk ⟨v, hvX⟩ = c := by
          by_cases hEq : W = W₀
          · subst W
            exact component_eq_of_connected_finset (B.connected hW₀B) hW₀X hvW hrW₀
          · exact component_eq_of_touching_finsets
              (B.connected hWB) (B.connected hW₀B) hWX hW₀X
              (B.touching hWB hW₀B hEq) hvW hrW₀
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hvX, hcomp⟩
      have hside : Disjoint (A \ X) C ∨ Disjoint (D \ X) C := by
        by_cases hAC : Disjoint (A \ X) C
        · exact Or.inl hAC
        · right
          rw [Finset.disjoint_left]
          intro b hbD hbC
          rcases Finset.not_disjoint_iff.mp hAC with ⟨a, haA, haC⟩
          rcases Finset.mem_filter.mp haC with ⟨_haU, haComp⟩
          rcases haComp with ⟨haX, haEq⟩
          rcases Finset.mem_filter.mp hbC with ⟨_hbU, hbComp⟩
          rcases hbComp with ⟨hbX, hbEq⟩
          have habEq : K.connectedComponentMk ⟨a, haX⟩ =
              K.connectedComponentMk ⟨b, hbX⟩ := haEq.trans hbEq.symm
          have habReach : K.Reachable ⟨a, haX⟩ ⟨b, hbX⟩ :=
            _root_.SimpleGraph.ConnectedComponent.exact habEq
          exact not_deleted_reachable_of_separator hsep
            (Finset.mem_sdiff.mp haA).1 (Finset.mem_sdiff.mp hbD).1 haX hbX habReach
      let H' := X ∪ H.filter fun v => v ∈ C
      have hH'hits : B.IsHittingSet H' := by
        intro W hWB
        by_cases hWX : Disjoint W X
        · rcases hH.1 W hWB with ⟨v, hvW, hvH⟩
          have hvC : v ∈ C := havoiding_subset_C hWB hWX hvW
          exact ⟨v, hvW, Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hvH, hvC⟩))⟩
        · rw [Finset.not_disjoint_iff] at hWX
          rcases hWX with ⟨v, hvW, hvX⟩
          exact ⟨v, hvW, Finset.mem_union.mpr (Or.inl hvX)⟩
      have hH'lt : H'.card < H.card := by
        rcases hside with hAC | hDC
        · exact replacement_card_lt hAH hXltA hAC
        · apply replacement_card_lt hDH
          · simpa [hcardAD] using hXltA
          · exact hDC
      exact False.elim ((not_lt_of_ge (hH.2 H' hH'hits)) hH'lt)

/-- A bramble whose hitting sets certify a treewidth lower bound produces the
node-well-linked terminal set needed by the grid-minor development. -/
theorem exists_paperNodeWellLinked_of_bramble
    (B : FiniteBramble G)
    (hlower : ∀ H : Finset V, B.IsHittingSet H → treewidth G ≤ H.card) :
    ∃ H : Finset V,
      TreewidthSparsifier.PaperNodeWellLinked G H ∧
        treewidth G ≤ H.card := by
  rcases B.exists_minimumHittingSet with ⟨H, hH⟩
  exact ⟨H, B.minimumHittingSet_paperNodeWellLinked hH, hlower H hH.1⟩

end FiniteBramble

end SimpleGraph

end Lax17Proofs
