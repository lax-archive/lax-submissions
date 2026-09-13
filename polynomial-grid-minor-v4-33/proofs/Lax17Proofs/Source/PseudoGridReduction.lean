import Lax17Proofs.Source.TreewidthSparsifierSection2
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Observation 4.4: contraction tools

This module supplies the path-packing operations used by the two contraction
loops in Section 4.2.  The edge-contraction graph itself is the axiom-free
construction from `TreewidthSparsifierSection2`.

Unlike the earlier sparsifier helper, the perfect-packing construction below
allows the contracted edge to meet a terminal.  Injectivity of the projected
terminal maps follows from the stronger and source-faithful hypothesis that
both endpoints lie on one path of the node-disjoint packing.
-/

namespace SimpleGraph


namespace Section4Reduction

open TreewidthSparsifier

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Finite edge count for a node-disjoint path packing -/

theorem GraphPath.edgeSet_card_add_one_eq_vertexSet_card
    {G : _root_.SimpleGraph V} (P : GraphPath G) :
    P.edgeSet.card + 1 = P.vertexSet.card := by
  classical
  rw [GraphPath.edgeSet_card, GraphPath.vertexSet]
  rw [List.toFinset_card_of_nodup P.isPath.support_nodup]
  exact P.walk.length_support.symm

/-- A node-disjoint packing with `k` path components has
`|E| + k = |V|`.  This is the counting fact used in the final uniqueness
argument of Observation 4.4. -/
theorem PathPacking.edgeSet_card_add_card_eq_vertexSet_card
    {G : _root_.SimpleGraph V} {S T : Finset V}
    (P : PathPacking G S T) :
    P.edgeSet.card + P.card = P.vertexSet.card := by
  classical
  have hvertex :
      (↑(Finset.univ : Finset P.Index) : Set P.Index).PairwiseDisjoint
        (fun i => (P.path i).vertexSet) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i _hi j _hj hnonempty
    by_contra hij
    rcases hnonempty with ⟨v, hv⟩
    exact Finset.disjoint_left.mp (P.node_disjoint hij)
      (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2
  have hedge :
      (↑(Finset.univ : Finset P.Index) : Set P.Index).PairwiseDisjoint
        (fun i => (P.path i).edgeSet) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i _hi j _hj hnonempty
    rcases hnonempty with ⟨e, he⟩
    have hei : e ∈ (P.path i).edgeSet := (Finset.mem_inter.mp he).1
    have hej : e ∈ (P.path j).edgeSet := (Finset.mem_inter.mp he).2
    by_contra hij
    have heq : s(e.out.1, e.out.2) = e := e.out_eq
    have hei' : s(e.out.1, e.out.2) ∈ (P.path i).edgeSet := by
      rw [heq]
      exact hei
    have hej' : s(e.out.1, e.out.2) ∈ (P.path j).edgeSet := by
      rw [heq]
      exact hej
    have hvi :
        e.out.1 ∈ (P.path i).vertexSet :=
      (P.path i).endpoints_mem_vertexSet_of_edgeSet
        hei' |>.1
    have hvj :
        e.out.1 ∈ (P.path j).vertexSet :=
      (P.path j).endpoints_mem_vertexSet_of_edgeSet
        hej' |>.1
    exact Finset.disjoint_left.mp (P.node_disjoint hij) hvi hvj
  rw [PathPacking.edgeSet, PathPacking.vertexSet,
    Finset.card_biUnion hedge, Finset.card_biUnion hvertex]
  change
    (∑ i : P.Index, (P.path i).edgeSet.card) +
        Fintype.card P.Index =
      ∑ i : P.Index, (P.path i).vertexSet.card
  rw [show Fintype.card P.Index = ∑ _i : P.Index, 1 by simp,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact GraphPath.edgeSet_card_add_one_eq_vertexSet_card (P.path i)

/-- The edges of the path graph on `n + 1` vertices are canonically indexed
by their lower endpoints. -/
noncomputable def pathGraphEdgeEquiv (n : ℕ) :
    Fin n ≃ (_root_.SimpleGraph.pathGraph (n + 1)).edgeSet := by
  classical
  let f : Fin n → (_root_.SimpleGraph.pathGraph (n + 1)).edgeSet := fun i =>
    ⟨s(i.castSucc, i.succ), by
      rw [_root_.SimpleGraph.mem_edgeSet, _root_.SimpleGraph.pathGraph_adj]
      exact Or.inl (by simp)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have h := congrArg
      (fun e : (_root_.SimpleGraph.pathGraph (n + 1)).edgeSet => e.1) hij
    dsimp [f] at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact Fin.ext (by simpa using congrArg Fin.val h.1)
    · have h1 := congrArg Fin.val h.1
      have h2 := congrArg Fin.val h.2
      simp at h1 h2
      omega
  · intro e
    have hadj :
        (_root_.SimpleGraph.pathGraph (n + 1)).Adj e.1.out.1 e.1.out.2 := by
      rw [← _root_.SimpleGraph.mem_edgeSet]
      simpa only [e.1.out_eq] using e.2
    rw [_root_.SimpleGraph.pathGraph_adj] at hadj
    rcases hadj with hadj | hadj
    · let i : Fin n := ⟨e.1.out.1.1, by omega⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      dsimp [f, i]
      calc
        s(e.1.out.1, ⟨e.1.out.1.1 + 1, by omega⟩) =
            s(e.1.out.1, e.1.out.2) := by
              apply Sym2.eq_iff.mpr
              exact Or.inl ⟨rfl, Fin.ext (by simpa using hadj)⟩
        _ = e.1 := e.1.out_eq
    · let i : Fin n := ⟨e.1.out.2.1, by omega⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      dsimp [f, i]
      calc
        s(e.1.out.2, ⟨e.1.out.2.1 + 1, by omega⟩) =
            s(e.1.out.1, e.1.out.2) := by
              apply Sym2.eq_iff.mpr
              exact Or.inr ⟨rfl, Fin.ext (by simpa using hadj)⟩
        _ = e.1 := e.1.out_eq

/-- The finite path graph is a tree. -/
theorem pathGraph_isTree (n : ℕ) :
    (_root_.SimpleGraph.pathGraph (n + 1)).IsTree := by
  rw [_root_.SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact _root_.SimpleGraph.pathGraph_connected n
  · rw [Nat.card_eq_fintype_card,
      ← Fintype.card_congr (pathGraphEdgeEquiv n)]
    simp

/-- A connected subpath of a simple path contains every ambient path edge
whose two endpoints it contains.  This is the convexity fact needed when an
edge common to a row and an original `Q` path is contracted: a retained
`Q''` subpath either avoids an endpoint or itself uses that edge. -/
theorem GraphPath.edge_mem_of_edge_subset_of_endpoints_mem
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {a b : V}
    (hsub : Q.edgeSet ⊆ P.edgeSet)
    (ha : a ∈ Q.vertexSet) (hb : b ∈ Q.vertexSet)
    (he : s(a, b) ∈ P.edgeSet) :
    s(a, b) ∈ Q.edgeSet := by
  classical
  have hab : a ≠ b :=
    G.not_isDiag_of_mem_edgeSet (P.edgeSet_subset_edgeSet he)
  have haP : a ∈ P.vertexSet :=
    (P.endpoints_mem_vertexSet_of_edgeSet he).1
  have hbP : b ∈ P.vertexSet :=
    (P.endpoints_mem_vertexSet_of_edgeSet he).2
  have core :
      ∀ {x y : V}, x ∈ Q.vertexSet → y ∈ Q.vertexSet →
        x ∈ P.vertexSet → y ∈ P.vertexSet →
        Q.Before x y → s(x, y) ∈ P.edgeSet →
          s(x, y) ∈ Q.edgeSet := by
    intro x y hxQ hyQ hxP hyP hxy hxyEdge
    let Z := Q.segmentOfBefore hxy
    have hZsubQ : Z.edgeSet ⊆ Q.edgeSet :=
      Q.segmentOfBefore_edgeSet_subset hxy
    have hZsubP : Z.edgeSet ⊆ P.edgeSet := hZsubQ.trans hsub
    have hxyNe : x ≠ y :=
      G.not_isDiag_of_mem_edgeSet (P.edgeSet_subset_edgeSet hxyEdge)
    have hZnil : ¬Z.walk.Nil :=
      _root_.SimpleGraph.Walk.not_nil_of_ne (by simpa [Z] using hxyNe)
    have hle : Z.walk.toSubgraph ≤ P.walk.toSubgraph := by
      rw [_root_.SimpleGraph.Walk.toSubgraph_le_iff hZnil]
      intro e heZ
      have heZ' : e ∈ Z.edgeSet := by
        simpa [GraphPath.edgeSet] using heZ
      have heP' : e ∈ P.edgeSet := hZsubP heZ'
      simpa [GraphPath.edgeSet] using heP'
    let incl : Z.walk.toSubgraph.coe →g P.walk.toSubgraph.coe :=
      _root_.SimpleGraph.Subgraph.inclusion hle
    let WZ := Z.walk.mapToSubgraph.map incl
    have hWZpath : WZ.IsPath := by
      apply _root_.SimpleGraph.Walk.map_isPath_of_injective
        (f := incl) (by
          intro u v huv
          have hv : (incl u).1 = (incl v).1 :=
            congrArg
              (fun z : P.walk.toSubgraph.verts => z.1) huv
          exact Subtype.ext hv)
      apply _root_.SimpleGraph.Walk.IsPath.of_map
        (f := Z.walk.toSubgraph.hom)
      simpa only [Z.walk.map_mapToSubgraph_hom] using Z.isPath
    let xp : P.walk.toSubgraph.verts := ⟨x, by
      simpa [GraphPath.vertexSet] using hxP⟩
    let yp : P.walk.toSubgraph.verts := ⟨y, by
      simpa [GraphPath.vertexSet] using hyP⟩
    have hxyAdj : P.walk.toSubgraph.coe.Adj xp yp := by
      rw [_root_.SimpleGraph.Subgraph.coe_adj,
        _root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
      simpa [GraphPath.edgeSet] using hxyEdge
    let WE : P.walk.toSubgraph.coe.Walk xp yp :=
      _root_.SimpleGraph.Walk.cons hxyAdj _root_.SimpleGraph.Walk.nil
    have hWEpath : WE.IsPath := by
      simp [WE, hxyNe, xp, yp]
    have htree : P.walk.toSubgraph.coe.IsTree := by
      rw [← (P.isPath.pathGraphIsoToSubgraph).isTree_iff]
      exact pathGraph_isTree P.walk.length
    have hpaths :
        (⟨WZ, hWZpath⟩ :
            P.walk.toSubgraph.coe.Path xp yp) =
          ⟨WE, hWEpath⟩ := by
      exact htree.isAcyclic.path_unique _ _
    have hwalk : WZ = WE := congrArg Subtype.val hpaths
    have hedgeWZ : s(xp, yp) ∈ WZ.edges := by
      rw [hwalk]
      exact List.mem_cons_self
    have hedgeMapped :
        s(x, y) ∈ (WZ.map P.walk.toSubgraph.hom).edges := by
      rw [_root_.SimpleGraph.Walk.edges_map]
      exact List.mem_map.2 ⟨s(xp, yp), hedgeWZ, by simp [xp, yp]⟩
    have hEdges :
        (WZ.map P.walk.toSubgraph.hom).edges = Z.walk.edges := by
      calc
        (WZ.map P.walk.toSubgraph.hom).edges =
            (Z.walk.mapToSubgraph.map Z.walk.toSubgraph.hom).edges := by
              dsimp only [WZ]
              simp only [_root_.SimpleGraph.Walk.edges_map, List.map_map]
              congr 1
              funext e
              induction e using Sym2.inductionOn with
              | _ x y => rfl
        _ = Z.walk.edges :=
          congrArg _ Z.walk.map_mapToSubgraph_hom
    rw [hEdges] at hedgeMapped
    exact hZsubQ (by simpa [GraphPath.edgeSet] using hedgeMapped)
  rcases le_total (Q.vertexIndex a) (Q.vertexIndex b) with habIdx | hbaIdx
  · exact core ha hb haP hbP
      ((Q.before_iff_vertexIndex_le).2 ⟨ha, hb, habIdx⟩) he
  · have hba := core hb ha hbP haP
      ((Q.before_iff_vertexIndex_le).2 ⟨hb, ha, hbaIdx⟩)
      (by simpa only [Sym2.eq_swap] using he)
    simpa only [Sym2.eq_swap] using hba

/-- Two distinct vertices are identified by an edge contraction exactly when
they are the endpoints of the contracted edge. -/
theorem EdgeContractVertex.projection_eq_iff_sym2_eq
    {G : _root_.SimpleGraph V} {a b x y : V} (hab : G.Adj a b)
    (hxy : x ≠ y) :
    EdgeContractVertex.projection (V := V) (u := a) (v := b) x =
        EdgeContractVertex.projection (V := V) (u := a) (v := b) y ↔
      s(x, y) = s(a, b) := by
  constructor
  · intro hproj
    rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
        (V := V) (u := a) (v := b) hproj with h | h
    · exact (hxy h).elim
    · rcases h.1 with rfl | rfl <;>
        rcases h.2 with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · simp
      · exact (hxy rfl).elim
  · intro hedge
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst x
      subst y
      simp
    · subst x
      subst y
      simp

/-- Bypassing a walk that is already simple does nothing. -/
theorem Walk.bypass_eq_self_of_isPath :
    {G : _root_.SimpleGraph V} → {x y : V} → (W : G.Walk x y) →
      W.IsPath → W.bypass = W
  | _, x, _, _root_.SimpleGraph.Walk.nil' _, _ => rfl
  | _, x, _, _root_.SimpleGraph.Walk.cons' _ y _ h W, hpath => by
      rw [_root_.SimpleGraph.Walk.cons_isPath_iff] at hpath
      have htail : W.IsPath := hpath.1
      have hnot : x ∉ W.support := hpath.2
      simp [_root_.SimpleGraph.Walk.bypass,
        Walk.bypass_eq_self_of_isPath W htail, hnot]

namespace ProjectionWalk

variable {G : _root_.SimpleGraph V} {a b : V} {hab : G.Adj a b}

/-- Projection suppresses precisely the occurrences of the contracted edge.
This length identity is the bookkeeping lemma used to show that projecting a
simple path through one of its own edges remains a simple path. -/
theorem length_add_edge_count :
    ∀ {x y : V} (W : G.Walk x y),
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) W).length +
          W.edges.count s(a, b) =
        W.length := by
  intro x y W
  induction W with
  | nil =>
      simp [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk]
  | @cons x y z h W ih =>
      by_cases hsame :
          EdgeContractVertex.projection (V := V) (u := a) (v := b) x =
            EdgeContractVertex.projection (V := V) (u := a) (v := b) y
      · have hedge : s(x, y) = s(a, b) :=
          (EdgeContractVertex.projection_eq_iff_sym2_eq hab h.ne).1 hsame
        simp [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
          hsame, hedge]
        omega
      · have hedge : s(x, y) ≠ s(a, b) := by
          intro hedge
          exact hsame
            ((EdgeContractVertex.projection_eq_iff_sym2_eq hab h.ne).2 hedge)
        simp [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
          hsame, hedge]
        omega

/-- Projection preserves the projected vertex set, even though it suppresses
the contracted step. -/
theorem support_toFinset_eq_image :
    {x y : V} → (W : G.Walk x y) →
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) W).support.toFinset =
        W.support.toFinset.image
          (EdgeContractVertex.projection (V := V) (u := a) (v := b))
  | x, _, _root_.SimpleGraph.Walk.nil' _ => by
      simp [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk]
  | x, _, _root_.SimpleGraph.Walk.cons' _ y _ h W => by
      by_cases hsame :
          EdgeContractVertex.projection (V := V) (u := a) (v := b) x =
            EdgeContractVertex.projection (V := V) (u := a) (v := b) y
      · have hy :
          EdgeContractVertex.projection (V := V) (u := a) (v := b) y ∈
            W.support.toFinset.image
              (EdgeContractVertex.projection (V := V) (u := a) (v := b)) := by
          exact Finset.mem_image.2 ⟨y, by simp, rfl⟩
        simp [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
          hsame, support_toFinset_eq_image W, hy]
      · simp [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
          hsame, support_toFinset_eq_image W]

/-- Every edge of a projected walk is the projection of an edge of the old
walk. -/
theorem exists_edge_of_mem_edges :
    ∀ {x y : V} (W : G.Walk x y) {e' : Sym2 (EdgeContractVertex V a b)},
      e' ∈
          (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
            (G := G) (huv := hab) W).edges →
        ∃ p q : V, s(p, q) ∈ W.edges ∧
          s(EdgeContractVertex.projection
              (V := V) (u := a) (v := b) p,
            EdgeContractVertex.projection
              (V := V) (u := a) (v := b) q) = e' := by
  intro x y W
  induction W with
  | nil =>
      intro e' he'
      simp [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk] at he'
  | @cons x y z h W ih =>
      intro e' he'
      by_cases hsame :
          EdgeContractVertex.projection (V := V) (u := a) (v := b) x =
            EdgeContractVertex.projection (V := V) (u := a) (v := b) y
      · have heTail :
            e' ∈
              (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
                (G := G) (huv := hab) W).edges := by
          simpa [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
            hsame] using he'
        rcases ih heTail with ⟨p, q, hpq, hmap⟩
        exact ⟨p, q, by simp [hpq], hmap⟩
      · have heCases :
            e' =
                s(EdgeContractVertex.projection
                    (V := V) (u := a) (v := b) x,
                  EdgeContractVertex.projection
                    (V := V) (u := a) (v := b) y) ∨
              e' ∈
                (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
                  (G := G) (huv := hab) W).edges := by
          simpa [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
            hsame] using he'
        rcases heCases with heHead | heTail
        · exact ⟨x, y, by simp, heHead.symm⟩
        · rcases ih heTail with ⟨p, q, hpq, hmap⟩
          exact ⟨p, q, by simp [hpq], hmap⟩

/-- A non-collapsed old walk edge occurs in the projected walk. -/
theorem map_edge_mem_edges
    {x y : V} (W : G.Walk x y) {p q : V}
    (he : s(p, q) ∈ W.edges)
    (hne :
      EdgeContractVertex.projection (V := V) (u := a) (v := b) p ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q) :
    s(EdgeContractVertex.projection (V := V) (u := a) (v := b) p,
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q) ∈
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
        (G := G) (huv := hab) W).edges := by
  induction W with
  | nil => simp at he
  | @cons x y z h W ih =>
      simp only [_root_.SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      by_cases hsame :
          EdgeContractVertex.projection (V := V) (u := a) (v := b) x =
            EdgeContractVertex.projection (V := V) (u := a) (v := b) y
      · rcases he with heHead | heTail
        · rw [Sym2.eq_iff] at heHead
          rcases heHead with ⟨hp, hq⟩ | ⟨hp, hq⟩
          · exact (hne (by simpa [hp, hq] using hsame)).elim
          · exact (hne (by simpa [hp, hq] using hsame.symm)).elim
        · simpa [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
            hsame] using ih heTail
      · rcases he with heHead | heTail
        · have hmap :
              s(EdgeContractVertex.projection
                    (V := V) (u := a) (v := b) p,
                  EdgeContractVertex.projection
                    (V := V) (u := a) (v := b) q) =
                s(EdgeContractVertex.projection
                    (V := V) (u := a) (v := b) x,
                  EdgeContractVertex.projection
                    (V := V) (u := a) (v := b) y) := by
            exact congrArg
              (Sym2.map
                (EdgeContractVertex.projection
                  (V := V) (u := a) (v := b))) heHead
          simpa [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
            hsame] using Or.inl hmap
        · simpa [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk,
            hsame] using Or.inr (ih heTail)

/-- On a finite set containing both endpoints, contraction decreases the
cardinality of the projected image by exactly one. -/
theorem card_image_projection_of_mem
    (hne : a ≠ b) (S : Finset V) (ha : a ∈ S) (hb : b ∈ S) :
    (S.image
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))).card =
      S.card - 1 := by
  let S' := S.erase b
  have himage :
      S.image
          (EdgeContractVertex.projection (V := V) (u := a) (v := b)) =
        S'.image
          (EdgeContractVertex.projection (V := V) (u := a) (v := b)) := by
    apply Finset.Subset.antisymm
    · intro z hz
      rcases Finset.mem_image.1 hz with ⟨x, hxS, rfl⟩
      by_cases hxb : x = b
      · subst x
        exact Finset.mem_image.2
          ⟨a, by simp [S', ha, hne], by simp⟩
      · exact Finset.mem_image.2 ⟨x, by simp [S', hxS, hxb], rfl⟩
    · exact Finset.image_mono _ (Finset.erase_subset _ _)
  have hinj :
      Set.InjOn
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))
        (S' : Set V) := by
    intro x hx y hy hproj
    rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
        (V := V) (u := a) (v := b) hproj with hxy | hend
    · exact hxy
    · have hxb : x ≠ b := (by simpa [S'] using hx : x ∈ S ∧ x ≠ b).2
      have hyb : y ≠ b := (by simpa [S'] using hy : y ∈ S ∧ y ≠ b).2
      have hxa : x = a := hend.1.resolve_right hxb
      have hya : y = a := hend.2.resolve_right hyb
      exact hxa.trans hya.symm
  rw [himage, (Finset.card_image_iff.2 hinj)]
  exact Finset.card_erase_of_mem hb

/-- If the contracted edge lies on a simple graph path, its projected walk is
already a path; no later `Walk.toPath` bypass can erase contacts. -/
theorem ofWalk_isPath_of_edge_mem
    (R : GraphPath G) (he : s(a, b) ∈ R.edgeSet) :
    (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
        (G := G) (huv := hab) R.walk).IsPath := by
  classical
  have habmem := R.endpoints_mem_vertexSet_of_edgeSet he
  have hcount : R.walk.edges.count s(a, b) = 1 := by
    exact List.count_eq_one_of_mem R.isPath.isTrail.edges_nodup
      (by simpa [GraphPath.edgeSet] using he)
  have hlength :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).length + 1 =
        R.walk.length := by
    simpa [hcount] using
      length_add_edge_count (G := G) (hab := hab) R.walk
  have hsupportCard :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).support.toFinset.card =
        R.walk.length := by
    rw [support_toFinset_eq_image (G := G) (hab := hab) R.walk]
    rw [card_image_projection_of_mem hab.ne
      R.walk.support.toFinset
      (by simpa [GraphPath.vertexSet] using habmem.1)
      (by simpa [GraphPath.vertexSet] using habmem.2)]
    have hvertexCard :
        R.walk.support.toFinset.card = R.walk.length + 1 := by
      rw [List.toFinset_card_of_nodup R.isPath.support_nodup,
        _root_.SimpleGraph.Walk.length_support]
    omega
  rw [_root_.SimpleGraph.Walk.isPath_def]
  let L :=
    (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
      (G := G) (huv := hab) R.walk).support
  have hcard : L.toFinset.card = L.length := by
    dsimp [L]
    rw [_root_.SimpleGraph.Walk.length_support, hsupportCard]
    omega
  have hmulti :
      (↑L : Multiset (EdgeContractVertex V a b)).Nodup := by
    apply Multiset.toFinset_card_eq_card_iff_nodup.mp
    simpa using hcard
  simpa [L] using hmulti

/-- Under an on-path contraction, the `toGraphPath` vertex set is exactly the
projection of the original vertex set. -/
theorem toGraphPath_vertexSet_eq_image_of_edge_mem
    (R : GraphPath G) (he : s(a, b) ∈ R.edgeSet) :
    (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.toGraphPath
        (G := G) (huv := hab) R).vertexSet =
      R.vertexSet.image
        (EdgeContractVertex.projection (V := V) (u := a) (v := b)) := by
  classical
  have hpath := ofWalk_isPath_of_edge_mem (G := G) (hab := hab) R he
  have hbypass :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).bypass =
        TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk := by
    exact Walk.bypass_eq_self_of_isPath _ hpath
  change
    (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
        (G := G) (huv := hab) R.walk).bypass.support.toFinset =
      R.walk.support.toFinset.image
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))
  rw [hbypass]
  exact support_toFinset_eq_image (G := G) (hab := hab) R.walk

/-- If the left contraction endpoint is absent from a simple path, its
projected walk remains simple. -/
theorem ofWalk_isPath_of_left_not_mem
    (R : GraphPath G) (ha : a ∉ R.vertexSet) :
    (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
        (G := G) (huv := hab) R.walk).IsPath := by
  classical
  have hedge : s(a, b) ∉ R.edgeSet := by
    intro he
    exact ha (R.endpoints_mem_vertexSet_of_edgeSet he).1
  have hcount : R.walk.edges.count s(a, b) = 0 := by
    rw [List.count_eq_zero]
    simpa [GraphPath.edgeSet] using hedge
  have hlength :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).length =
        R.walk.length := by
    have hlen := length_add_edge_count (G := G) (hab := hab) R.walk
    omega
  have hinj :
      Set.InjOn
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))
        (R.vertexSet : Set V) := by
    intro x hx y hy hproj
    rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
        (V := V) (u := a) (v := b) hproj with hxy | hend
    · exact hxy
    · have hxa : x ≠ a := by
        intro h
        exact ha (by simpa [h] using hx)
      have hya : y ≠ a := by
        intro h
        exact ha (by simpa [h] using hy)
      exact
        (hend.1.resolve_left hxa).trans
          (hend.2.resolve_left hya).symm
  have hsupportCard :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).support.toFinset.card =
        R.walk.length + 1 := by
    rw [support_toFinset_eq_image (G := G) (hab := hab) R.walk]
    change
      (R.vertexSet.image
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))).card =
          R.walk.length + 1
    rw [Finset.card_image_iff.2 hinj]
    exact (by
      rw [GraphPath.vertexSet, List.toFinset_card_of_nodup
        R.isPath.support_nodup, _root_.SimpleGraph.Walk.length_support])
  rw [_root_.SimpleGraph.Walk.isPath_def]
  let L :=
    (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
      (G := G) (huv := hab) R.walk).support
  have hcard : L.toFinset.card = L.length := by
    dsimp [L]
    rw [_root_.SimpleGraph.Walk.length_support, hsupportCard, hlength]
  have hmulti :
      (↑L : Multiset (EdgeContractVertex V a b)).Nodup := by
    apply Multiset.toFinset_card_eq_card_iff_nodup.mp
    simpa using hcard
  simpa [L] using hmulti

/-- If the left contraction endpoint is absent from a simple path, projection
is injective on that path and therefore preserves its full projected vertex
set. -/
theorem toGraphPath_vertexSet_eq_image_of_left_not_mem
    (R : GraphPath G) (ha : a ∉ R.vertexSet) :
    (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.toGraphPath
        (G := G) (huv := hab) R).vertexSet =
      R.vertexSet.image
        (EdgeContractVertex.projection (V := V) (u := a) (v := b)) := by
  classical
  have hpath := ofWalk_isPath_of_left_not_mem (G := G) (hab := hab) R ha
  have hbypass :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).bypass =
        TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk :=
    Walk.bypass_eq_self_of_isPath _ hpath
  change
    (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
        (G := G) (huv := hab) R.walk).bypass.support.toFinset =
      R.walk.support.toFinset.image
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))
  rw [hbypass]
  exact support_toFinset_eq_image (G := G) (hab := hab) R.walk

/-- Every projected graph-path edge has an old path edge as a preimage when
the contraction edge lies on the old path. -/
theorem toGraphPath_edge_preimage_of_edge_mem
    (R : GraphPath G) (hcontract : s(a, b) ∈ R.edgeSet)
    {e' : Sym2 (EdgeContractVertex V a b)}
    (he' :
      e' ∈
        (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.toGraphPath
          (G := G) (huv := hab) R).edgeSet) :
    ∃ p q : V, s(p, q) ∈ R.edgeSet ∧
      EdgeContractVertex.projection (V := V) (u := a) (v := b) p ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q ∧
      s(EdgeContractVertex.projection (V := V) (u := a) (v := b) p,
          EdgeContractVertex.projection (V := V) (u := a) (v := b) q) = e' := by
  classical
  have hpath := ofWalk_isPath_of_edge_mem (G := G) (hab := hab) R hcontract
  have hbypass :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).bypass =
        TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk :=
    Walk.bypass_eq_self_of_isPath _ hpath
  have heWalk :
      e' ∈
        (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).edges := by
    simp only
      [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.toGraphPath,
        GraphPath.edgeSet, _root_.SimpleGraph.Walk.toPath] at he'
    rw [hbypass] at he'
    simpa using he'
  rcases exists_edge_of_mem_edges (G := G) (hab := hab) R.walk heWalk with
    ⟨p, q, hpq, hmap⟩
  have hpqPath : s(p, q) ∈ R.edgeSet := by
    simpa [GraphPath.edgeSet] using hpq
  have hne : e' ∉ Sym2.diagSet :=
    (TreewidthSparsifier.contractEdgeGraph G hab).not_isDiag_of_mem_edgeSet
      (GraphPath.edgeSet_subset_edgeSet _ he')
  have hprojNe :
      EdgeContractVertex.projection (V := V) (u := a) (v := b) p ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q := by
    intro h
    apply hne
    rw [← hmap, h]
    simp
  exact ⟨p, q, hpqPath, hprojNe, hmap⟩

/-- Every edge of `toGraphPath` has a non-collapsed old preimage whenever the
projected walk is already simple. -/
theorem toGraphPath_edge_preimage_of_isPath
    (R : GraphPath G)
    (hpath :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
        (G := G) (huv := hab) R.walk).IsPath)
    {e' : Sym2 (EdgeContractVertex V a b)}
    (he' :
      e' ∈
        (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.toGraphPath
          (G := G) (huv := hab) R).edgeSet) :
    ∃ p q : V, s(p, q) ∈ R.edgeSet ∧
      EdgeContractVertex.projection (V := V) (u := a) (v := b) p ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q ∧
      s(EdgeContractVertex.projection (V := V) (u := a) (v := b) p,
          EdgeContractVertex.projection (V := V) (u := a) (v := b) q) = e' := by
  classical
  have hbypass :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).bypass =
        TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk :=
    Walk.bypass_eq_self_of_isPath _ hpath
  have heWalk :
      e' ∈
        (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).edges := by
    simp only
      [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.toGraphPath,
        GraphPath.edgeSet, _root_.SimpleGraph.Walk.toPath] at he'
    rw [hbypass] at he'
    simpa using he'
  rcases exists_edge_of_mem_edges (G := G) (hab := hab) R.walk heWalk with
    ⟨p, q, hpq, hmap⟩
  have hpqPath : s(p, q) ∈ R.edgeSet := by
    simpa [GraphPath.edgeSet] using hpq
  have hne : e' ∉ Sym2.diagSet :=
    (TreewidthSparsifier.contractEdgeGraph G hab).not_isDiag_of_mem_edgeSet
      (GraphPath.edgeSet_subset_edgeSet _ he')
  have hprojNe :
      EdgeContractVertex.projection (V := V) (u := a) (v := b) p ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q := by
    intro h
    apply hne
    rw [← hmap, h]
    simp
  exact ⟨p, q, hpqPath, hprojNe, hmap⟩

/-- A non-collapsed old edge survives in `toGraphPath` whenever the projected
walk is already simple. -/
theorem mem_toGraphPath_edgeSet_of_mem_of_isPath
    (R : GraphPath G)
    (hpath :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
        (G := G) (huv := hab) R.walk).IsPath)
    {p q : V} (he : s(p, q) ∈ R.edgeSet)
    (hne :
      EdgeContractVertex.projection (V := V) (u := a) (v := b) p ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q) :
    s(EdgeContractVertex.projection (V := V) (u := a) (v := b) p,
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q) ∈
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.toGraphPath
        (G := G) (huv := hab) R).edgeSet := by
  have hbypass :
      (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk).bypass =
        TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := G) (huv := hab) R.walk :=
    Walk.bypass_eq_self_of_isPath _ hpath
  have heWalk : s(p, q) ∈ R.walk.edges := by
    simpa [GraphPath.edgeSet] using he
  have hmap :=
    map_edge_mem_edges (G := G) (hab := hab) R.walk heWalk hne
  simp only
    [TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.toGraphPath,
      GraphPath.edgeSet, _root_.SimpleGraph.Walk.toPath]
  rw [hbypass]
  simpa using hmap

end ProjectionWalk

/-- Membership in a canonical contraction branch set is exactly projection to
the corresponding contracted vertex. -/
theorem EdgeContractVertex.projection_eq_iff_mem_branchSet
    {a b x : V} {z : EdgeContractVertex V a b} :
    EdgeContractVertex.projection (V := V) (u := a) (v := b) x = z ↔
      x ∈ EdgeContractVertex.branchSet z := by
  classical
  cases z with
  | merged =>
      simpa using
        (EdgeContractVertex.projection_eq_merged_iff
          (V := V) (u := a) (v := b) (x := x))
  | keep z =>
      constructor
      · intro h
        have hne : x ≠ a ∧ x ≠ b := by
          by_contra hnot
          have hx : x = a ∨ x = b := by tauto
          have hm :
              EdgeContractVertex.projection
                  (V := V) (u := a) (v := b) x =
                (EdgeContractVertex.merged :
                  EdgeContractVertex V a b) := by
            exact (EdgeContractVertex.projection_eq_merged_iff
              (V := V) (u := a) (v := b)).2 hx
          rw [h] at hm
          cases hm
        have hk :
            EdgeContractVertex.ofVertex
                (V := V) (u := a) (v := b) x hne =
              EdgeContractVertex.keep z := by
          simpa [EdgeContractVertex.projection_eq_of_ne hne.1 hne.2] using h
        injection hk with hz
        simpa using congrArg Subtype.val hz
      · intro hx
        have hval : x = z.1 := by simpa using hx
        subst x
        simp [EdgeContractVertex.projection_eq_of_ne z.2.1 z.2.2,
          EdgeContractVertex.ofVertex]

/-- Suppose `P` consists of node-disjoint subpaths of distinct paths of the
node-disjoint packing `Q`.  If an edge of a `Q`-path is not used by `P`, then
at least one endpoint of that edge is unused by the whole packing `P`.

This is the choice needed in the first contraction loop of Observation 4.4:
if the contracted row edge is not itself on a retained `Q''` path, orient the
edge so that its unused endpoint is the left endpoint and apply
`PathPacking.contractEdgeOfLeftUnused`. -/
theorem PathPacking.left_or_right_not_mem_vertexSet_of_subpaths
    {G K : _root_.SimpleGraph V}
    {S T S' T' : Finset V}
    (P : PathPacking G S T) (Q : PathPacking K S' T')
    (hGK : G ≤ K)
    (parent : P.Index → Q.Index)
    (hparent : Function.Injective parent)
    (hvertex :
      ∀ i : P.Index, (P.path i).vertexSet ⊆ (Q.path (parent i)).vertexSet)
    (hedge :
      ∀ i : P.Index, (P.path i).edgeSet ⊆ (Q.path (parent i)).edgeSet)
    {i₀ : Q.Index} {a b : V}
    (he : s(a, b) ∈ (Q.path i₀).edgeSet)
    (heP : s(a, b) ∉ P.edgeSet) :
    a ∉ P.vertexSet ∨ b ∉ P.vertexSet := by
  classical
  by_contra hnot
  push_neg at hnot
  rcases (P.mem_vertexSet).1 hnot.1 with ⟨i, hai⟩
  rcases (P.mem_vertexSet).1 hnot.2 with ⟨j, hbj⟩
  have haQ₀ : a ∈ (Q.path i₀).vertexSet :=
    (Q.path i₀).endpoints_mem_vertexSet_of_edgeSet he |>.1
  have hbQ₀ : b ∈ (Q.path i₀).vertexSet :=
    (Q.path i₀).endpoints_mem_vertexSet_of_edgeSet he |>.2
  have haQi : a ∈ (Q.path (parent i)).vertexSet := hvertex i hai
  have hbQj : b ∈ (Q.path (parent j)).vertexSet := hvertex j hbj
  have hi : parent i = i₀ := by
    by_contra hne
    exact Finset.disjoint_left.mp (Q.node_disjoint hne) haQi haQ₀
  have hj : parent j = i₀ := by
    by_contra hne
    exact Finset.disjoint_left.mp (Q.node_disjoint hne) hbQj hbQ₀
  have hij : i = j := hparent (hi.trans hj.symm)
  subst j
  apply heP
  exact (P.mem_edgeSet).2
    ⟨i, by
      let Pi : GraphPath K := (P.path i).mapLe hGK
      have hPiEdge :
          Pi.edgeSet ⊆ (Q.path (parent i)).edgeSet := by
        simpa only [Pi, GraphPath.mapLe_edgeSet] using hedge i
      have haPi : a ∈ Pi.vertexSet := by
        simpa only [Pi, GraphPath.mapLe_vertexSet] using hai
      have hbPi : b ∈ Pi.vertexSet := by
        simpa only [Pi, GraphPath.mapLe_vertexSet] using hbj
      have hmem :=
        GraphPath.edge_mem_of_edge_subset_of_endpoints_mem
          (Q.path (parent i)) Pi hPiEdge haPi hbPi (by simpa [hi] using he)
      simpa only [Pi, GraphPath.mapLe_edgeSet] using hmem⟩

/-- Edge contraction is monotone in the ambient graph when the contracted
edge already belongs to the smaller graph. -/
theorem contractEdgeGraph_mono
    {H K : _root_.SimpleGraph V} {a b : V}
    (hHK : H ≤ K) (hab : H.Adj a b) :
    contractEdgeGraph H hab ≤ contractEdgeGraph K (hHK hab) := by
  intro x y hxy
  rcases hxy with ⟨hxy_ne, p, hp, q, hq, hpq⟩
  exact ⟨hxy_ne, p, hp, q, hq, hHK hpq⟩

/-- Projection is injective on every set that avoids the left endpoint of the
contracted edge. -/
theorem EdgeContractVertex.projection_injOn_of_left_not_mem
    {a b : V} {U : Finset V} (ha : a ∉ U) :
    Set.InjOn
      (EdgeContractVertex.projection (V := V) (u := a) (v := b))
      (U : Set V) := by
  intro x hx y hy hproj
  rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
      (V := V) (u := a) (v := b) hproj with hxy | hend
  · exact hxy
  · have hxa : x ≠ a := by
      intro h
      exact ha (by simpa [h] using hx)
    have hya : y ≠ a := by
      intro h
      exact ha (by simpa [h] using hy)
    exact
      (hend.1.resolve_left hxa).trans
        (hend.2.resolve_left hya).symm

/-- Projection is injective on the source terminals of a perfect packing when
both contraction endpoints lie on one packing path. -/
theorem PerfectPathPacking.projection_injOn_left_of_same_path
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B)
    {a b : V} (i₀ : P.Index)
    (ha : a ∈ (P.path i₀).vertexSet)
    (hb : b ∈ (P.path i₀).vertexSet) :
    Set.InjOn
      (EdgeContractVertex.projection (V := V) (u := a) (v := b))
      (A : Set V) := by
  intro x hx y hy hproj
  rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
      (V := V) (u := a) (v := b) hproj with hxy | hend
  · exact hxy
  · have hxPath : x ∈ (P.path i₀).vertexSet := by
      rcases hend.1 with rfl | rfl
      · exact ha
      · exact hb
    have hyPath : y ∈ (P.path i₀).vertexSet := by
      rcases hend.2 with rfl | rfl
      · exact ha
      · exact hb
    exact
      (P.eq_source_of_mem_left_of_mem_path_vertexSet i₀ hx hxPath).trans
        (P.eq_source_of_mem_left_of_mem_path_vertexSet i₀ hy hyPath).symm

/-- The analogous projection injectivity on target terminals. -/
theorem PerfectPathPacking.projection_injOn_right_of_same_path
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B)
    {a b : V} (i₀ : P.Index)
    (ha : a ∈ (P.path i₀).vertexSet)
    (hb : b ∈ (P.path i₀).vertexSet) :
    Set.InjOn
      (EdgeContractVertex.projection (V := V) (u := a) (v := b))
      (B : Set V) := by
  intro x hx y hy hproj
  rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
      (V := V) (u := a) (v := b) hproj with hxy | hend
  · exact hxy
  · have hxPath : x ∈ (P.path i₀).vertexSet := by
      rcases hend.1 with rfl | rfl
      · exact ha
      · exact hb
    have hyPath : y ∈ (P.path i₀).vertexSet := by
      rcases hend.2 with rfl | rfl
      · exact ha
      · exact hb
    exact
      (P.eq_target_of_mem_right_of_mem_path_vertexSet i₀ hx hxPath).trans
        (P.eq_target_of_mem_right_of_mem_path_vertexSet i₀ hy hyPath).symm

/-- Deleting a surviving quotient edge commutes with lifting through one edge
contraction.  The deleted old edge is required to differ from the contracted
edge, so the merged branch set remains connected. -/
noncomputable def contractEdgeGraph.deleteEdgeMinorModel
    {G : _root_.SimpleGraph V} {a b x y : V}
    (hab : G.Adj a b) (hxy : G.Adj x y)
    (hdiff : s(x, y) ≠ s(a, b))
    (hproj :
      EdgeContractVertex.projection (V := V) (u := a) (v := b) x ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) y) :
    MinorModel
      ((contractEdgeGraph G hab).deleteEdges
        ({s(EdgeContractVertex.projection
              (V := V) (u := a) (v := b) x,
            EdgeContractVertex.projection
              (V := V) (u := a) (v := b) y)} :
          Set (Sym2 (EdgeContractVertex V a b))))
      (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) where
  branchSet := EdgeContractVertex.branchSet
  branch_nonempty := EdgeContractVertex.branchSet_nonempty
  branch_connected := by
    intro z
    cases z with
    | merged =>
        have hab' :
            (G.deleteEdges ({s(x, y)} : Set (Sym2 V))).Adj a b := by
          rw [_root_.SimpleGraph.deleteEdges_adj]
          exact ⟨hab, by simpa using hdiff.symm⟩
        change
          ((G.deleteEdges ({s(x, y)} : Set (Sym2 V))).induce
            {v : V | v ∈ ({a, b} : Finset V)}).Connected
        have hset :
            {v : V | v ∈ ({a, b} : Finset V)} = ({a, b} : Set V) := by
          ext v
          simp
        rw [hset]
        exact _root_.SimpleGraph.induce_pair_connected_of_adj hab'
    | keep z =>
        simpa [EdgeContractVertex.branchSet] using
          GraphPath.connected_induce_vertexSet
            (GraphPath.refl
              (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) z.1)
  branch_disjoint := by
    intro z w hzw
    exact EdgeContractVertex.branchSet_disjoint hzw
  adjacent := by
    intro z w hzw
    have hzwContract :
        (contractEdgeGraph G hab).Adj z w :=
      (_root_.SimpleGraph.deleteEdges_adj.mp hzw).1
    rcases hzwContract.2 with ⟨p, hp, q, hq, hpq⟩
    refine ⟨p, hp, q, hq, ?_⟩
    rw [_root_.SimpleGraph.deleteEdges_adj]
    refine ⟨hpq, ?_⟩
    intro hpqDeleted
    have hpqEq : s(p, q) = s(x, y) := by simpa using hpqDeleted
    have hpz :
        EdgeContractVertex.projection (V := V) (u := a) (v := b) p = z :=
      (EdgeContractVertex.projection_eq_iff_mem_branchSet).2 hp
    have hqw :
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q = w :=
      (EdgeContractVertex.projection_eq_iff_mem_branchSet).2 hq
    have hquot :
        s(z, w) =
          s(EdgeContractVertex.projection
              (V := V) (u := a) (v := b) x,
            EdgeContractVertex.projection
              (V := V) (u := a) (v := b) y) := by
      rw [← hpz, ← hqw]
      simpa using congrArg
        (Sym2.map
          (EdgeContractVertex.projection
            (V := V) (u := a) (v := b))) hpqEq
    exact (_root_.SimpleGraph.deleteEdges_adj.mp hzw).2
      (by simpa [hquot])

/-- A chosen preimage in a finite set under the edge-contraction projection. -/
noncomputable def edgeContractImagePreimage
    {a b : V} (A : Finset V)
    {z : EdgeContractVertex V a b}
    (hz : z ∈ edgeContractImageSet (a := a) (b := b) A) :
    {x : V // x ∈ A} :=
  Classical.choose (Finset.mem_image.1 hz)

theorem projection_edgeContractImagePreimage
    {a b : V} (A : Finset V)
    {z : EdgeContractVertex V a b}
    (hz : z ∈ edgeContractImageSet (a := a) (b := b) A) :
    EdgeContractVertex.projection (V := V) (u := a) (v := b)
        (edgeContractImagePreimage A hz).1 = z := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.1 hz)).2

/-- Pulling a bijection onto a contraction image back through the chosen
preimages gives a bijection onto the original finite set, provided projection
is injective there. -/
theorem edgeContractImagePreimage_comp_bijective
    {ι : Type*} {a b : V}
    (A : Finset V)
    (hinj :
      Set.InjOn
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))
        (A : Set V))
    (f : ι →
      {z : EdgeContractVertex V a b //
        z ∈ edgeContractImageSet (a := a) (b := b) A})
    (hf : Function.Bijective f) :
    Function.Bijective
      (fun i : ι => edgeContractImagePreimage A (f i).2) := by
  classical
  constructor
  · intro i j hij
    apply hf.1
    apply Subtype.ext
    have hproj := congrArg
      (fun x : {v : V // v ∈ A} =>
        EdgeContractVertex.projection (V := V) (u := a) (v := b) x.1) hij
    simpa [projection_edgeContractImagePreimage] using hproj
  · intro x
    let z :
        {z : EdgeContractVertex V a b //
          z ∈ edgeContractImageSet (a := a) (b := b) A} :=
      ⟨EdgeContractVertex.projection (V := V) (u := a) (v := b) x.1,
        mem_edgeContractImageSet_projection x.2⟩
    rcases hf.2 z with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply hinj
    · exact (edgeContractImagePreimage A (f i).2).2
    · exact x.2
    have hfi :
        (f i).1 =
          EdgeContractVertex.projection (V := V) (u := a) (v := b) x.1 :=
      congrArg Subtype.val hi
    exact
      (projection_edgeContractImagePreimage A (f i).2).trans hfi

/-- Lift a perfect packing after deleting a surviving quotient edge back
through the contraction.  This is the formal path-uncontraction step in the
proof of Observation 4.4. -/
noncomputable def liftPerfectPathPacking_deleteEdgeContract
    {G : _root_.SimpleGraph V} {a b x y : V}
    (hab : G.Adj a b) (hxy : G.Adj x y)
    (hdiff : s(x, y) ≠ s(a, b))
    (hproj :
      EdgeContractVertex.projection (V := V) (u := a) (v := b) x ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) y)
    {A B : Finset V}
    (hAinj :
      Set.InjOn
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))
        (A : Set V))
    (hBinj :
      Set.InjOn
        (EdgeContractVertex.projection (V := V) (u := a) (v := b))
        (B : Set V))
    (P : PerfectPathPacking
      ((contractEdgeGraph G hab).deleteEdges
        ({s(EdgeContractVertex.projection
              (V := V) (u := a) (v := b) x,
            EdgeContractVertex.projection
              (V := V) (u := a) (v := b) y)} :
          Set (Sym2 (EdgeContractVertex V a b))))
      (edgeContractImageSet (a := a) (b := b) A)
      (edgeContractImageSet (a := a) (b := b) B)) :
    PerfectPathPacking
      (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) A B := by
  classical
  let M :=
    contractEdgeGraph.deleteEdgeMinorModel hab hxy hdiff hproj
  let src : P.Index → {v : V // v ∈ A} := fun i =>
    edgeContractImagePreimage A (P.source_mem i)
  let tgt : P.Index → {v : V // v ∈ B} := fun i =>
    edgeContractImagePreimage B (P.target_mem i)
  let hs : ∀ i : P.Index, (src i).1 ∈ M.branchSet (P.path i).source := by
    intro i
    apply EdgeContractVertex.projection_eq_iff_mem_branchSet.mp
    exact projection_edgeContractImagePreimage A (P.source_mem i)
  let ht : ∀ i : P.Index, (tgt i).1 ∈ M.branchSet (P.path i).target := by
    intro i
    apply EdgeContractVertex.projection_eq_iff_mem_branchSet.mp
    exact projection_edgeContractImagePreimage B (P.target_mem i)
  refine
    { toPathPacking :=
        { Index := P.Index
          path := fun i =>
            MinorModel.liftGraphPath M (P.path i) (hs i) (ht i)
          connects := ?_
          node_disjoint := ?_ }
      source_mem := fun i => (src i).2
      target_mem := fun i => (tgt i).2
      source_bijective := ?_
      target_bijective := ?_ }
  · intro i
    exact Or.inl ⟨by simp [src], by simp [tgt]⟩
  · intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvi hvj
    have hminor :
        Disjoint (P.path i).vertexSet (P.path j).vertexSet := by
      simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij
    have hunion :
        Disjoint (M.walkBranchUnion (P.path i).walk)
          (M.walkBranchUnion (P.path j).walk) :=
      MinorModel.walkBranchUnion_disjoint_of_vertexSet_disjoint M hminor
    have hviU : v ∈ M.walkBranchUnion (P.path i).walk :=
      MinorModel.liftGraphPath_vertexSet_subset_walkBranchUnion
        M (P.path i) (hs i) (ht i) hvi
    have hvjU : v ∈ M.walkBranchUnion (P.path j).walk :=
      MinorModel.liftGraphPath_vertexSet_subset_walkBranchUnion
        M (P.path j) (hs j) (ht j) hvj
    exact Finset.disjoint_left.mp hunion hviU hvjU
  · change Function.Bijective src
    exact edgeContractImagePreimage_comp_bijective A hAinj
      (fun i => ⟨(P.path i).source, P.source_mem i⟩)
      P.source_bijective
  · change Function.Bijective tgt
    exact edgeContractImagePreimage_comp_bijective B hBinj
      (fun i => ⟨(P.path i).target, P.target_mem i⟩)
      P.target_bijective

/-- Project a path packing through the contraction of an edge whose endpoints
lie on one member of the packing. -/
noncomputable def PathPacking.contractEdgeOfSamePath
    {G : _root_.SimpleGraph V} {S T : Finset V}
    (P : PathPacking G S T)
    {a b : V} (hab : G.Adj a b)
    (i0 : P.Index)
    (ha : a ∈ (P.path i0).vertexSet)
    (hb : b ∈ (P.path i0).vertexSet) :
    PathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) S)
      (edgeContractImageSet (a := a) (b := b) T) where
  Index := P.Index
  path := fun i =>
    contractEdgeGraph.ProjectionWalk.toGraphPath
      (G := G) (huv := hab) (P.path i)
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl
        ⟨by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.1,
         by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.2⟩
    · exact Or.inr
        ⟨by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.1,
         by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.2⟩
  node_disjoint := by
    classical
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro z hzi hzj
    rcases
        contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := G) (huv := hab) (P.path i) z hzi with
      ⟨x, hx, hxz⟩
    rcases
        contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := G) (huv := hab) (P.path j) z hzj with
      ⟨y, hy, hyz⟩
    have hproj :
        EdgeContractVertex.projection (V := V) (u := a) (v := b) x =
          EdgeContractVertex.projection (V := V) (u := a) (v := b) y :=
      hxz.trans hyz.symm
    rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
        (V := V) (u := a) (v := b) hproj with hxy | hend
    · subst y
      exact Finset.disjoint_left.mp (P.node_disjoint hij) hx hy
    · have hxi0 : x ∈ (P.path i0).vertexSet := by
        rcases hend.1 with rfl | rfl
        · exact ha
        · exact hb
      have hyi0 : y ∈ (P.path i0).vertexSet := by
        rcases hend.2 with rfl | rfl
        · exact ha
        · exact hb
      have hi : i = i0 := by
        by_contra hne
        exact Finset.disjoint_left.mp (P.node_disjoint hne) hx hxi0
      have hj : j = i0 := by
        by_contra hne
        exact Finset.disjoint_left.mp (P.node_disjoint hne) hy hyi0
      exact hij (hi.trans hj.symm)

/-- Every non-collapsed packing edge survives contraction of an edge lying on
one path of that packing. -/
theorem PathPacking.mem_edgeSet_contractEdgeOfSamePath
    {G : _root_.SimpleGraph V} {S T : Finset V}
    (P : PathPacking G S T)
    {a b : V} (hab : G.Adj a b)
    (i₀ : P.Index)
    (hcontract : s(a, b) ∈ (P.path i₀).edgeSet)
    {p q : V} (he : s(p, q) ∈ P.edgeSet)
    (hne :
      EdgeContractVertex.projection (V := V) (u := a) (v := b) p ≠
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q) :
    s(EdgeContractVertex.projection (V := V) (u := a) (v := b) p,
        EdgeContractVertex.projection (V := V) (u := a) (v := b) q) ∈
      (Section4Reduction.PathPacking.contractEdgeOfSamePath P hab i₀
        ((P.path i₀).endpoints_mem_vertexSet_of_edgeSet hcontract).1
        ((P.path i₀).endpoints_mem_vertexSet_of_edgeSet hcontract).2).edgeSet := by
  classical
  rcases (P.mem_edgeSet).1 he with ⟨i, hei⟩
  rw [PathPacking.mem_edgeSet]
  refine ⟨i, ?_⟩
  by_cases hi : i = i₀
  · subst i
    exact ProjectionWalk.mem_toGraphPath_edgeSet_of_mem_of_isPath
      (P.path i₀)
      (ProjectionWalk.ofWalk_isPath_of_edge_mem
        (G := G) (hab := hab) (P.path i₀) hcontract)
      hei hne
  · have ha_not : a ∉ (P.path i).vertexSet := by
      intro hai
      exact Finset.disjoint_left.mp (P.node_disjoint hi) hai
        ((P.path i₀).endpoints_mem_vertexSet_of_edgeSet hcontract).1
    exact ProjectionWalk.mem_toGraphPath_edgeSet_of_mem_of_isPath
      (P.path i)
      (ProjectionWalk.ofWalk_isPath_of_left_not_mem
        (G := G) (hab := hab) (P.path i) ha_not)
      hei hne

/-- Project a path packing when the left endpoint of the contracted edge is
unused by the whole packing. -/
noncomputable def PathPacking.contractEdgeOfLeftUnused
    {G : _root_.SimpleGraph V} {S T : Finset V}
    (P : PathPacking G S T)
    {a b : V} (hab : G.Adj a b)
    (ha : a ∉ P.vertexSet) :
    PathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) S)
      (edgeContractImageSet (a := a) (b := b) T) where
  Index := P.Index
  path := fun i =>
    contractEdgeGraph.ProjectionWalk.toGraphPath
      (G := G) (huv := hab) (P.path i)
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl
        ⟨by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.1,
         by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.2⟩
    · exact Or.inr
        ⟨by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.1,
         by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.2⟩
  node_disjoint := by
    classical
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro z hzi hzj
    rcases
        contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := G) (huv := hab) (P.path i) z hzi with
      ⟨x, hx, hxz⟩
    rcases
        contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := G) (huv := hab) (P.path j) z hzj with
      ⟨y, hy, hyz⟩
    have hproj :
        EdgeContractVertex.projection (V := V) (u := a) (v := b) x =
          EdgeContractVertex.projection (V := V) (u := a) (v := b) y :=
      hxz.trans hyz.symm
    rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
        (V := V) (u := a) (v := b) hproj with hxy | hend
    · subst y
      exact Finset.disjoint_left.mp (P.node_disjoint hij) hx hy
    · have hxa : x ≠ a := by
        intro h
        apply ha
        exact (P.mem_vertexSet).2 ⟨i, by simpa [h] using hx⟩
      have hya : y ≠ a := by
        intro h
        apply ha
        exact (P.mem_vertexSet).2 ⟨j, by simpa [h] using hy⟩
      have hxb : x = b := hend.1.resolve_left hxa
      have hyb : y = b := hend.2.resolve_left hya
      subst x
      subst y
      exact Finset.disjoint_left.mp (P.node_disjoint hij) hx hy

/-- Project a path packing when the right endpoint of the contracted edge is
unused by the whole packing. -/
noncomputable def PathPacking.contractEdgeOfRightUnused
    {G : _root_.SimpleGraph V} {S T : Finset V}
    (P : PathPacking G S T)
    {a b : V} (hab : G.Adj a b)
    (hb : b ∉ P.vertexSet) :
    PathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) S)
      (edgeContractImageSet (a := a) (b := b) T) where
  Index := P.Index
  path := fun i =>
    contractEdgeGraph.ProjectionWalk.toGraphPath
      (G := G) (huv := hab) (P.path i)
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl
        ⟨by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.1,
         by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.2⟩
    · exact Or.inr
        ⟨by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.1,
         by
          simpa [contractEdgeGraph.ProjectionWalk.toGraphPath] using
            mem_edgeContractImageSet_projection (a := a) (b := b) h.2⟩
  node_disjoint := by
    classical
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro z hzi hzj
    rcases
        contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := G) (huv := hab) (P.path i) z hzi with
      ⟨x, hx, hxz⟩
    rcases
        contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := G) (huv := hab) (P.path j) z hzj with
      ⟨y, hy, hyz⟩
    have hproj :
        EdgeContractVertex.projection (V := V) (u := a) (v := b) x =
          EdgeContractVertex.projection (V := V) (u := a) (v := b) y :=
      hxz.trans hyz.symm
    rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
        (V := V) (u := a) (v := b) hproj with hxy | hend
    · subst y
      exact Finset.disjoint_left.mp (P.node_disjoint hij) hx hy
    · have hxb : x ≠ b := by
        intro h
        apply hb
        exact (P.mem_vertexSet).2 ⟨i, by simpa [h] using hx⟩
      have hyb : y ≠ b := by
        intro h
        apply hb
        exact (P.mem_vertexSet).2 ⟨j, by simpa [h] using hy⟩
      have hxa : x = a := hend.1.resolve_right hxb
      have hya : y = a := hend.2.resolve_right hyb
      subst x
      subst y
      exact Finset.disjoint_left.mp (P.node_disjoint hij) hx hy

/-- Contract an edge lying on one path of a perfect packing.  Terminal
vertices are allowed: no two different terminal images are identified because
the two contracted endpoints belong to the same packing path. -/
noncomputable def PerfectPathPacking.contractEdgeOfSamePath
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B)
    {a b : V} (hab : G.Adj a b)
    (i0 : P.Index)
    (ha : a ∈ (P.path i0).vertexSet)
    (hb : b ∈ (P.path i0).vertexSet) :
    PerfectPathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) A)
      (edgeContractImageSet (a := a) (b := b) B) where
  toPathPacking :=
    Section4Reduction.PathPacking.contractEdgeOfSamePath
      P.toPathPacking hab i0 ha hb
  source_mem := by
    intro i
    exact mem_edgeContractImageSet_projection
      (a := a) (b := b) (P.source_mem i)
  target_mem := by
    intro i
    exact mem_edgeContractImageSet_projection
      (a := a) (b := b) (P.target_mem i)
  source_bijective := by
    constructor
    · intro i j hij
      by_contra hne
      have hproj :
          EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path i).source =
            EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path j).source :=
        congrArg Subtype.val hij
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := V) (u := a) (v := b) hproj with hsrc | hend
      · exact hne (P.source_bijective.1 (Subtype.ext hsrc))
      · have hi0 : i = i0 := by
          by_contra hi
          exact Finset.disjoint_left.mp (P.node_disjoint hi)
            (GraphPath.source_mem_vertexSet (P.path i))
            (by
              rcases hend.1 with h | h
              · simpa [h] using ha
              · simpa [h] using hb)
        have hj0 : j = i0 := by
          by_contra hj
          exact Finset.disjoint_left.mp (P.node_disjoint hj)
            (GraphPath.source_mem_vertexSet (P.path j))
            (by
              rcases hend.2 with h | h
              · simpa [h] using ha
              · simpa [h] using hb)
        exact hne (hi0.trans hj0.symm)
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.source_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have hsource : (P.path i).source = y.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.contractEdgeOfSamePath,
        contractEdgeGraph.ProjectionWalk.toGraphPath, hsource] using hyx
  target_bijective := by
    constructor
    · intro i j hij
      by_contra hne
      have hproj :
          EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path i).target =
            EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path j).target :=
        congrArg Subtype.val hij
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := V) (u := a) (v := b) hproj with htgt | hend
      · exact hne (P.target_bijective.1 (Subtype.ext htgt))
      · have hi0 : i = i0 := by
          by_contra hi
          exact Finset.disjoint_left.mp (P.node_disjoint hi)
            (GraphPath.target_mem_vertexSet (P.path i))
            (by
              rcases hend.1 with h | h
              · simpa [h] using ha
              · simpa [h] using hb)
        have hj0 : j = i0 := by
          by_contra hj
          exact Finset.disjoint_left.mp (P.node_disjoint hj)
            (GraphPath.target_mem_vertexSet (P.path j))
            (by
              rcases hend.2 with h | h
              · simpa [h] using ha
              · simpa [h] using hb)
        exact hne (hi0.trans hj0.symm)
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.target_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have htarget : (P.path i).target = y.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.contractEdgeOfSamePath,
        contractEdgeGraph.ProjectionWalk.toGraphPath, htarget] using hyx

/-- Project a perfect packing when the left endpoint of the contracted edge is
unused.  The other endpoint may be a packing terminal: projection is still
injective on both terminal sets because the unused endpoint cannot occur
there. -/
noncomputable def PerfectPathPacking.contractEdgeOfLeftUnused
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B)
    {a b : V} (hab : G.Adj a b)
    (ha : a ∉ P.toPathPacking.vertexSet) :
    PerfectPathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) A)
      (edgeContractImageSet (a := a) (b := b) B) where
  toPathPacking :=
    Section4Reduction.PathPacking.contractEdgeOfLeftUnused
      P.toPathPacking hab ha
  source_mem := by
    intro i
    exact mem_edgeContractImageSet_projection
      (a := a) (b := b) (P.source_mem i)
  target_mem := by
    intro i
    exact mem_edgeContractImageSet_projection
      (a := a) (b := b) (P.target_mem i)
  source_bijective := by
    constructor
    · intro i j hij
      have hproj :
          EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path i).source =
            EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path j).source :=
        congrArg Subtype.val hij
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := V) (u := a) (v := b) hproj with hsrc | hend
      · exact P.source_bijective.1 (Subtype.ext hsrc)
      · have hia : (P.path i).source ≠ a := by
          intro h
          apply ha
          exact (P.toPathPacking.mem_vertexSet).2
            ⟨i, by simpa [h] using GraphPath.source_mem_vertexSet (P.path i)⟩
        have hja : (P.path j).source ≠ a := by
          intro h
          apply ha
          exact (P.toPathPacking.mem_vertexSet).2
            ⟨j, by simpa [h] using GraphPath.source_mem_vertexSet (P.path j)⟩
        have hi : (P.path i).source = b := hend.1.resolve_left hia
        have hj : (P.path j).source = b := hend.2.resolve_left hja
        exact P.source_bijective.1 (Subtype.ext (hi.trans hj.symm))
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.source_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have hsource : (P.path i).source = y.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.contractEdgeOfLeftUnused,
        contractEdgeGraph.ProjectionWalk.toGraphPath, hsource] using hyx
  target_bijective := by
    constructor
    · intro i j hij
      have hproj :
          EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path i).target =
            EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path j).target :=
        congrArg Subtype.val hij
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := V) (u := a) (v := b) hproj with htgt | hend
      · exact P.target_bijective.1 (Subtype.ext htgt)
      · have hia : (P.path i).target ≠ a := by
          intro h
          apply ha
          exact (P.toPathPacking.mem_vertexSet).2
            ⟨i, by simpa [h] using GraphPath.target_mem_vertexSet (P.path i)⟩
        have hja : (P.path j).target ≠ a := by
          intro h
          apply ha
          exact (P.toPathPacking.mem_vertexSet).2
            ⟨j, by simpa [h] using GraphPath.target_mem_vertexSet (P.path j)⟩
        have hi : (P.path i).target = b := hend.1.resolve_left hia
        have hj : (P.path j).target = b := hend.2.resolve_left hja
        exact P.target_bijective.1 (Subtype.ext (hi.trans hj.symm))
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.target_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have htarget : (P.path i).target = y.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.contractEdgeOfLeftUnused,
        contractEdgeGraph.ProjectionWalk.toGraphPath, htarget] using hyx

/-- Project a perfect packing when the right endpoint of the contracted edge
is unused. -/
noncomputable def PerfectPathPacking.contractEdgeOfRightUnused
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B)
    {a b : V} (hab : G.Adj a b)
    (hb : b ∉ P.toPathPacking.vertexSet) :
    PerfectPathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) A)
      (edgeContractImageSet (a := a) (b := b) B) where
  toPathPacking :=
    Section4Reduction.PathPacking.contractEdgeOfRightUnused
      P.toPathPacking hab hb
  source_mem := by
    intro i
    exact mem_edgeContractImageSet_projection
      (a := a) (b := b) (P.source_mem i)
  target_mem := by
    intro i
    exact mem_edgeContractImageSet_projection
      (a := a) (b := b) (P.target_mem i)
  source_bijective := by
    constructor
    · intro i j hij
      have hproj :
          EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path i).source =
            EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path j).source :=
        congrArg Subtype.val hij
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := V) (u := a) (v := b) hproj with hsrc | hend
      · exact P.source_bijective.1 (Subtype.ext hsrc)
      · have hib : (P.path i).source ≠ b := by
          intro h
          apply hb
          exact (P.toPathPacking.mem_vertexSet).2
            ⟨i, by simpa [h] using GraphPath.source_mem_vertexSet (P.path i)⟩
        have hjb : (P.path j).source ≠ b := by
          intro h
          apply hb
          exact (P.toPathPacking.mem_vertexSet).2
            ⟨j, by simpa [h] using GraphPath.source_mem_vertexSet (P.path j)⟩
        have hi : (P.path i).source = a := hend.1.resolve_right hib
        have hj : (P.path j).source = a := hend.2.resolve_right hjb
        exact P.source_bijective.1 (Subtype.ext (hi.trans hj.symm))
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.source_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have hsource : (P.path i).source = y.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.contractEdgeOfRightUnused,
        contractEdgeGraph.ProjectionWalk.toGraphPath, hsource] using hyx
  target_bijective := by
    constructor
    · intro i j hij
      have hproj :
          EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path i).target =
            EdgeContractVertex.projection (V := V) (u := a) (v := b)
              (P.path j).target :=
        congrArg Subtype.val hij
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := V) (u := a) (v := b) hproj with htgt | hend
      · exact P.target_bijective.1 (Subtype.ext htgt)
      · have hib : (P.path i).target ≠ b := by
          intro h
          apply hb
          exact (P.toPathPacking.mem_vertexSet).2
            ⟨i, by simpa [h] using GraphPath.target_mem_vertexSet (P.path i)⟩
        have hjb : (P.path j).target ≠ b := by
          intro h
          apply hb
          exact (P.toPathPacking.mem_vertexSet).2
            ⟨j, by simpa [h] using GraphPath.target_mem_vertexSet (P.path j)⟩
        have hi : (P.path i).target = a := hend.1.resolve_right hib
        have hj : (P.path j).target = a := hend.2.resolve_right hjb
        exact P.target_bijective.1 (Subtype.ext (hi.trans hj.symm))
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.target_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have htarget : (P.path i).target = y.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.contractEdgeOfRightUnused,
        contractEdgeGraph.ProjectionWalk.toGraphPath, htarget] using hyx

end Section4Reduction

end SimpleGraph

end Lax17Proofs
