import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.IntervalCases
import Lax909950.EulerFormula
import Lax909950.EdgeDensity
import Lax909950Proofs.Forest

/-!
Edge density of planar graphs. For a connected graph with a cycle, every face is
bounded by a cycle, so each face is a side face of at least three edges; since every
edge has at most two side faces, $3f \leq 2e$, and Euler's formula gives
$e \leq 3v - 6$. Disconnected graphs are handled by induction on the number of
vertices.
-/

namespace Lax909950Proofs

open Lax68.StraightLineDrawings Lax909950.EulerFormula Topology
open Set hiding image

namespace EdgeDensityAux

variable {V : Type*} {G : SimpleGraph V}

/-- The subgraph of the edges having `F` as one of their two side faces. -/
noncomputable def sideGraph [Finite V] (D : StraightLineDrawing G) (F : Set Point) :
    SimpleGraph V where
  Adj a b := G.Adj a b ∧ (F = edgeFace D a b true ∨ F = edgeFace D a b false)
  symm := ⟨fun a b => by
    rintro ⟨hab, h⟩
    refine ⟨hab.symm, ?_⟩
    rw [edgeFace_swap D hab, edgeFace_swap D hab]
    exact h.symm⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem sideGraph_le [Finite V] (D : StraightLineDrawing G) (F : Set Point) :
    sideGraph D F ≤ G := fun _ _ h => h.1

theorem mem_image_iff (D : StraightLineDrawing G) {x : Point} :
    x ∈ image D ↔ x ∈ range D.point ∨
      ∃ a b, G.Adj a b ∧ x ∈ segment ℝ (D.point a) (D.point b) := by
  simp [image, mem_iUnion]

/-- Every face is a side face of the edges of some cycle. -/
theorem not_isAcyclic_sideGraph [Finite V] (D : StraightLineDrawing G) (hG : ¬ G.IsAcyclic)
    {F : Set Point} (hF : F ∈ faces D) : ¬ (sideGraph D F).IsAcyclic := by
  intro hH
  have hFopen := isOpen_of_mem_faces D hF
  obtain ⟨x, hx, rfl⟩ := hF
  set F := connectedComponentIn (image D)ᶜ x
  set H := sideGraph D F
  set DH := restrictDrawing D (sideGraph_le D F)
  obtain ⟨F0, hF0⟩ := Set.encard_eq_one.1 (encard_faces_of_isAcyclic DH hH)
  have hsub : (image D)ᶜ ⊆ (image DH)ᶜ :=
    compl_subset_compl.2 (image_restrictDrawing_subset D _)
  have hxF : x ∈ F := mem_connectedComponentIn hx
  have hxS : x ∈ (image DH)ᶜ := hsub hx
  set K := connectedComponentIn (image DH)ᶜ x
  -- the complement of `image DH` is a single component
  have hSK : (image DH)ᶜ ⊆ K := by
    intro y hy
    have h1 : connectedComponentIn (image DH)ᶜ y ∈ faces DH := ⟨y, hy, rfl⟩
    have h2 : K ∈ faces DH := ⟨x, hxS, rfl⟩
    rw [hF0] at h1 h2
    rw [mem_singleton_iff] at h1 h2
    rw [h2, ← h1]
    exact mem_connectedComponentIn hy
  -- `F` is relatively clopen in `K`
  have hKF : K ⊆ F := by
    refine (isPreconnected_connectedComponentIn).subset_of_closure_inter_subset hFopen
      ⟨x, mem_connectedComponentIn hxS, hxF⟩ ?_
    rintro y ⟨hyc, hyK⟩
    have hyS : y ∉ image DH := connectedComponentIn_subset _ _ hyK
    by_contra hyF
    have hyfr : y ∈ frontier F := by
      rw [frontier, hFopen.interior_eq]; exact ⟨hyc, hyF⟩
    have hyI := frontier_subset_image D ⟨x, hx, rfl⟩ hyfr
    apply hyS
    rw [mem_image_iff] at hyI ⊢
    rcases hyI with hr | ⟨a, b, hab, hseg⟩
    · exact Or.inl hr
    · rw [← insert_endpoints_openSegment] at hseg
      rcases hseg with rfl | rfl | hopen
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inl ⟨b, rfl⟩
      · refine Or.inr ⟨a, b, ⟨hab, ?_⟩, openSegment_subset_segment _ _ _ hopen⟩
        exact eq_edgeFace_of_mem_closure D hab ⟨x, hx, rfl⟩ hopen hyc
  -- hence every edge of `G` belongs to `H`
  have hGH : G ≤ H := by
    intro a b hab
    by_contra hnot
    let m : Point := (1 / 2 : ℝ) • D.point a + (1 / 2 : ℝ) • D.point b
    have hm : m ∈ edgeSeg D a b :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hmI : m ∈ image D := edgeSeg_subset_image D hab hm
    have hmS : m ∉ image DH := by
      rw [mem_image_iff]
      rintro (hr | ⟨c, d, hcd, hseg⟩)
      · exact Set.disjoint_left.1 (edgeSeg_disjoint_range D hab) hm hr
      · have he := edgeSeg_inter_image D hab hm hcd.1 hseg
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hnot hcd
        · exact hnot hcd.symm
    exact absurd hmI (connectedComponentIn_subset _ _ (hKF (hSK hmS)))
  exact hG (hH.anti hGH)

/-- Each face is a side face of at least three edges. -/
theorem three_le_card_sideGraph [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : StraightLineDrawing G) (hG : ¬ G.IsAcyclic)
    {F : Set Point} (hF : F ∈ faces D) [DecidablePred (· ∈ (sideGraph D F).edgeSet)] :
    3 ≤ (G.edgeFinset.filter (fun e => e ∈ (sideGraph D F).edgeSet)).card := by
  have h := not_isAcyclic_sideGraph D hG hF
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at h
  obtain ⟨v, c, hc⟩ := h
  have hsub : c.edges.toFinset ⊆
      G.edgeFinset.filter (fun e => e ∈ (sideGraph D F).edgeSet) := by
    intro e he
    rw [List.mem_toFinset] at he
    have := c.edges_subset_edgeSet he
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    exact ⟨SimpleGraph.edgeSet_mono (sideGraph_le D F) this, this⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hc.edges_nodup, SimpleGraph.Walk.length_edges] at this
  have := hc.three_le_length
  omega

/-- Three times the number of faces is at most twice the number of edges. -/
theorem three_mul_card_faces_le [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : StraightLineDrawing G) (hG : ¬ G.IsAcyclic) (hfin : (faces D).Finite) :
    hfin.toFinset.card * 3 ≤ G.edgeFinset.card * 2 := by
  classical
  refine Finset.card_mul_le_card_mul (fun F e => e ∈ (sideGraph D F).edgeSet) ?_ ?_
  · intro F hF
    rw [Set.Finite.mem_toFinset] at hF
    exact three_le_card_sideGraph D hG hF
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    refine (Finset.card_le_card (t := {edgeFace D a b true, edgeFace D a b false}) ?_).trans
      Finset.card_le_two
    intro F hF
    rw [Finset.mem_bipartiteBelow] at hF
    rcases hF.2.2 with h | h <;> simp [h]

/-- The edge bound: $3v - 6$ for $v \geq 3$, and $v - 1$ for smaller $v$. -/
def bound (n : ℕ) : ℕ := if n ≤ 2 then n - 1 else 3 * n - 6

/-- The bound for connected graphs with a cycle. -/
theorem connected_not_acyclic [Finite V] (hc : G.Connected) (hG : ¬ G.IsAcyclic)
    (D : StraightLineDrawing G) : G.edgeSet.ncard + 6 ≤ 3 * Nat.card V := by
  classical
  have := Fintype.ofFinite V
  have hE := euler_formula hc D
  have hEfin : G.edgeSet.encard = (G.edgeFinset.card : ℕ∞) := by
    rw [← SimpleGraph.coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard]
  have hfin : (faces D).Finite := by
    rw [← Set.encard_ne_top_iff]
    intro htop
    rw [htop, hEfin] at hE
    simp at hE
    exact absurd hE.symm (by simp)
  rw [hfin.encard_eq_coe_toFinset_card, hEfin] at hE
  have hE' : Nat.card V + hfin.toFinset.card = G.edgeFinset.card + 2 := by
    exact_mod_cast hE
  have h3 := three_mul_card_faces_le D hG hfin
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega

/-- The bound for connected graphs. -/
theorem connected_bound [Finite V] (hc : G.Connected) (hG : Lax68.Planar.IsPlanar G) :
    G.edgeSet.ncard ≤ bound (Nat.card V) := by
  classical
  have := Fintype.ofFinite V
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, Nat.card_eq_fintype_card]
  unfold bound
  split_ifs with hv
  · have h := G.card_edgeFinset_le_card_choose_two
    interval_cases hn : Fintype.card V <;> simp_all
  · by_cases hac : G.IsAcyclic
    · have := (SimpleGraph.IsTree.mk hc hac).card_edgeFinset
      omega
    · have h := connected_not_acyclic hc hac hG.some
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, Nat.card_eq_fintype_card] at h
      omega

/-- A drawing of `G` induces a drawing of its pullback along an embedding. -/
def drawingComap' {W : Type*} {G : SimpleGraph W} (D : StraightLineDrawing G)
    (f : V ↪ W) : StraightLineDrawing (G.comap f) where
  point := D.point ∘ f
  injective := D.injective.comp f.injective
  noVertexOnEdge := fun hab hca hcb =>
    D.noVertexOnEdge hab (f.injective.ne hca) (f.injective.ne hcb)
  disjointEdges := fun {a b c d} hab hcd hdisj => by
    refine D.disjointEdges hab hcd ?_
    simp only [Set.disjoint_insert_left, Set.disjoint_insert_right, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.disjoint_singleton, ne_eq] at hdisj ⊢
    simpa only [f.injective.eq_iff] using hdisj

theorem isPlanar_induce' (hG : Lax68.Planar.IsPlanar G) (s : Set V) :
    Lax68.Planar.IsPlanar (G.induce s) :=
  ⟨drawingComap' hG.some (Function.Embedding.subtype _)⟩

/-- The edges of an induced subgraph, viewed as edges of `G`. -/
theorem mem_image_induce {s : Set V} {e : Sym2 V}
    (he : e ∈ Sym2.map Subtype.val '' (G.induce s).edgeSet) :
    e ∈ G.edgeSet ∧ ∀ x ∈ e, x ∈ s := by
  obtain ⟨e', he', rfl⟩ := he
  induction e' using Sym2.ind with
  | h a b =>
  simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet, Sym2.mem_iff] at he' ⊢
  refine ⟨by simpa using he', ?_⟩
  rintro x (rfl | rfl)
  · exact a.2
  · exact b.2

/-- If no edge leaves `s`, the edges of `G` split into those of `G[s]` and `G[sᶜ]`. -/
theorem ncard_edgeSet_split [Finite V] (s : Set V)
    (hs : ∀ a b, G.Adj a b → (a ∈ s ↔ b ∈ s)) :
    G.edgeSet.ncard = (G.induce s).edgeSet.ncard + (G.induce sᶜ).edgeSet.ncard := by
  have hunion : G.edgeSet = Sym2.map Subtype.val '' (G.induce s).edgeSet ∪
      Sym2.map Subtype.val '' (G.induce sᶜ).edgeSet := by
    apply Set.Subset.antisymm
    · intro e he
      induction e using Sym2.ind with
      | h a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      by_cases ha : a ∈ s
      · have hb : b ∈ s := (hs a b he).1 ha
        exact Or.inl ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa using he, rfl⟩
      · have hb : b ∉ s := fun hb => ha ((hs a b he).2 hb)
        exact Or.inr ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa using he, rfl⟩
    · rintro e (he | he)
      · exact (mem_image_induce he).1
      · exact (mem_image_induce he).1
  have hdisj : Disjoint (Sym2.map Subtype.val '' (G.induce s).edgeSet)
      (Sym2.map Subtype.val '' (G.induce sᶜ).edgeSet) := by
    rw [Set.disjoint_left]
    intro e h1 h2
    obtain ⟨he, h1⟩ := mem_image_induce h1
    obtain ⟨-, h2⟩ := mem_image_induce h2
    induction e using Sym2.ind with
    | h a b => exact h2 a (Sym2.mem_mk_left a b) (h1 a (Sym2.mem_mk_left a b))
  rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]

theorem bound_add {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : bound a + bound b ≤ bound (a + b) := by
  unfold bound
  split_ifs <;> omega

universe u

theorem edge_bound : ∀ (n : ℕ) (V : Type u) [Finite V] (G : SimpleGraph V),
    Nat.card V = n → Lax68.Planar.IsPlanar G → G.edgeSet.ncard ≤ bound n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G hn hG
  subst hn
  by_cases hc : G.Connected
  · exact connected_bound hc hG
  rcases isEmpty_or_nonempty V with hV | hV
  · have : G.edgeSet = ∅ := by
      ext e; induction e using Sym2.ind with
      | h a b => exact isEmptyElim a
    simp [this]
  have : ¬ G.Preconnected := fun h => hc ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at this
  obtain ⟨u, w, huw⟩ := this
  set s : Set V := {x | G.Reachable u x}
  have hs : ∀ a b, G.Adj a b → (a ∈ s ↔ b ∈ s) := fun a b hab =>
    ⟨fun h => h.trans hab.reachable, fun h => h.trans hab.symm.reachable⟩
  have hus : u ∈ s := SimpleGraph.Reachable.refl u
  have hws : w ∈ sᶜ := huw
  have h1 : 0 < s.ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨u, hus⟩
  have h2 : 0 < sᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨w, hws⟩
  have hsum := Set.ncard_add_ncard_compl s
  have e1 := ih _ (by omega) s (G.induce s) (Nat.card_coe_set_eq s) (isPlanar_induce' hG s)
  have e2 := ih _ (by omega) (sᶜ : Set V) (G.induce sᶜ) (Nat.card_coe_set_eq sᶜ)
    (isPlanar_induce' hG sᶜ)
  rw [ncard_edgeSet_split s hs, ← hsum]
  exact (add_le_add e1 e2).trans (bound_add h1 h2)

end EdgeDensityAux

/--
---
conclusion: Lax909950.EdgeDensity.edge_density
---
For a connected graph with a cycle, every face is a side face of the edges of a
cycle, hence of at least $3$ edges; each edge has at most $2$ side faces, so
$3f \leq 2e$, and Euler's formula $v - e + f = 2$ gives $e \leq 3v - 6$. Trees have
$v - 1 \leq 3v - 6$ edges. Disconnected graphs split into a component and the rest,
and the bound is superadditive.
-/
theorem edge_density {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : Lax68.Planar.IsPlanar G) (hV : 3 ≤ Nat.card V) :
    G.edgeSet.ncard ≤ 3 * Nat.card V - 6 := by
  have h := EdgeDensityAux.edge_bound _ V G rfl hG
  unfold EdgeDensityAux.bound at h
  rwa [if_neg (by omega)] at h

end Lax909950Proofs
