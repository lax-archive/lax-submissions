import Lax17Proofs.Source.TreewidthSparsifierDefs
import Lax17Proofs.Source.MinorTransitivity
import Lax17Proofs.Source.UniqueLinkageOrdering

namespace Lax17Proofs

universe u v w

/-!
# Section 2 of `treewidth-sparsifier.pdf`

This file starts the self-contained proof route for Chekuri--Chuzhoy,
*Degree-3 Treewidth Sparsifiers*, Theorem 1.3.

The paper proves Theorem 1.3 through a minimal-minor argument and a red/blue
chain labeling theorem.  The code below formalizes and proves the final
counting step: once the chain-label certificate promised by Theorem 2.2 is
available for two perfect routings, the number of vertices of degree more than
two in the union graph is at most `4 k^4`, hence certainly within the
`8 k^4 + 8 k` bound used by Theorem 1.3.

The remaining graph-theoretic work is to construct this certificate from the
minimal-minor proof and the red/blue chain construction.  This file imports
only the axiom-free `TreewidthSparsifierDefs` boundary, so the proved Section 2
lemmas below do not depend on the old one-line Theorem 1.3 contract axiom.
-/

namespace SimpleGraph
namespace TreewidthSparsifier


open scoped Classical

variable {V : Type u} [DecidableEq V]

/-- Passing to a spanning subgraph cannot increase a local degree bound. -/
theorem degreeAtMost_of_le
    {G H : _root_.SimpleGraph V} {v : V} {d : ℕ}
    (hG : DegreeAtMost G v d) (hHG : H ≤ G) :
    DegreeAtMost H v d := by
  classical
  rcases hG with ⟨N, hN, hcard⟩
  let N' := N.filter fun u => H.Adj v u
  refine ⟨N', ?_, ?_⟩
  · intro u
    constructor
    · intro hu
      exact (Finset.mem_filter.mp hu).2
    · intro huv
      exact Finset.mem_filter.mpr ⟨(hN u).2 (hHG huv), huv⟩
  · exact (Finset.card_filter_le _ _).trans hcard

/-- Exact degree bounds are also upper bounds. -/
theorem degreeAtMost_of_degreeEquals
    {G : _root_.SimpleGraph V} {v : V} {d : ℕ}
    (h : DegreeEquals G v d) :
    DegreeAtMost G v d := by
  rcases h with ⟨N, hN, hcard⟩
  exact ⟨N, hN, by omega⟩

/-- To prove a degree bound it is enough to exhibit a finite superset of the
actual neighbor set with the desired cardinality. -/
theorem degreeAtMost_of_adj_subset_finset
    [Fintype V]
    {G : _root_.SimpleGraph V} {v : V} {d : ℕ}
    (N : Finset V)
    (hsub : ∀ u : V, G.Adj v u → u ∈ N)
    (hcard : N.card ≤ d) :
    DegreeAtMost G v d := by
  classical
  let A : Finset V := Finset.univ.filter fun u : V => G.Adj v u
  refine ⟨A, ?_, ?_⟩
  · intro u
    simp [A]
  · have hA : A ⊆ N := by
      intro u hu
      exact hsub u (by simpa [A] using hu)
    exact (Finset.card_le_card hA).trans hcard

/-- If all neighbors in `G` are either neighbors in a locally bounded graph
`L` or belong to a small exceptional set, then `G` inherits the summed degree
bound. -/
theorem degreeAtMost_of_adj_imp_local_or_mem
    [Fintype V]
    {G L : _root_.SimpleGraph V} {v : V} {d e : ℕ}
    (hlocal : DegreeAtMost L v d)
    (E : Finset V)
    (hsub : ∀ u : V, G.Adj v u → L.Adj v u ∨ u ∈ E)
    (hEcard : E.card ≤ e) :
    DegreeAtMost G v (d + e) := by
  classical
  rcases hlocal with ⟨N, hN, hNcard⟩
  refine degreeAtMost_of_adj_subset_finset (N ∪ E) ?_ ?_
  · intro u huv
    rcases hsub u huv with huvLocal | huE
    · exact Finset.mem_union.2 (Or.inl ((hN u).2 huvLocal))
    · exact Finset.mem_union.2 (Or.inr huE)
  · exact (Finset.card_union_le N E).trans (Nat.add_le_add hNcard hEcard)

/-- The finite set counted by the paper's `τ(G)`: vertices of degree more than
two.  The contract exposes only its cardinality; Section 2 also needs the set
itself to state the chain-label injection. -/
noncomputable def branchVertexFinset
    {α : Type*} [Fintype α] (G : _root_.SimpleGraph α) : Finset α := by
  classical
  exact Finset.univ.filter fun v : α => ¬ DegreeAtMost G v 2

@[simp] theorem branchVertexFinset_card
    {α : Type*} [Fintype α] (G : _root_.SimpleGraph α) :
    (branchVertexFinset G).card = branchVertexCount G := by
  simp [branchVertexFinset, branchVertexCount]

theorem degreeAtMost_pullback_of_injective_adj
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    {G : _root_.SimpleGraph α} {H : _root_.SimpleGraph β}
    (f : α → β) (hf : Function.Injective f)
    (hadj : ∀ ⦃u v : α⦄, G.Adj u v → H.Adj (f u) (f v))
    {x : α} {d : ℕ}
    (hH : DegreeAtMost H (f x) d) :
    DegreeAtMost G x d := by
  classical
  rcases hH with ⟨N, hN, hcard⟩
  let N' : Finset α := Finset.univ.filter fun u : α => G.Adj x u
  refine ⟨N', ?_, ?_⟩
  · intro u
    simp [N']
  · have himage_sub : N'.image f ⊆ N := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
      exact (hN (f u)).2 (hadj ((Finset.mem_filter.mp hu).2))
    have hcard_image :
        (N'.image f).card = N'.card := by
      rw [Finset.card_image_of_injective]
      exact hf
    calc
      N'.card = (N'.image f).card := hcard_image.symm
      _ ≤ N.card := Finset.card_le_card himage_sub
      _ ≤ d := hcard

theorem branchVertexCount_le_of_injective_adj
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {G : _root_.SimpleGraph α} {H : _root_.SimpleGraph β}
    (f : α → β) (hf : Function.Injective f)
    (hadj : ∀ ⦃u v : α⦄, G.Adj u v → H.Adj (f u) (f v)) :
    branchVertexCount G ≤ branchVertexCount H := by
  classical
  let B := branchVertexFinset G
  let C := branchVertexFinset H
  have hsub : B.image f ⊆ C := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxBranch : ¬ DegreeAtMost G x 2 := by
      simpa [B, branchVertexFinset] using hx
    have hfxBranch : ¬ DegreeAtMost H (f x) 2 := by
      intro hH
      exact hxBranch
        (degreeAtMost_pullback_of_injective_adj
          (G := G) (H := H) f hf hadj hH)
    simpa [C, branchVertexFinset, hfxBranch]
  have hcard_image :
      (B.image f).card = B.card := by
    rw [Finset.card_image_of_injective]
    exact hf
  calc
    branchVertexCount G = B.card := by simp [B]
    _ = (B.image f).card := hcard_image.symm
    _ ≤ C.card := Finset.card_le_card hsub
    _ = branchVertexCount H := by simp [C]

namespace GraphPath

/-- Two vertices on a simple graph path are comparable in the path order. -/
theorem before_total_of_mem {G : _root_.SimpleGraph V}
    (P : GraphPath G) {u v : V}
    (hu : u ∈ P.vertexSet) (hv : v ∈ P.vertexSet) :
    P.Before u v ∨ P.Before v u := by
  classical
  rcases le_total (P.vertexIndex u) (P.vertexIndex v) with huv | hvu
  · exact Or.inl ((P.before_iff_vertexIndex_le).2 ⟨hu, hv, huv⟩)
  · exact Or.inr ((P.before_iff_vertexIndex_le).2 ⟨hv, hu, hvu⟩)

/-- The one-edge graph path associated with an adjacency. -/
noncomputable def ofAdj {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) : GraphPath G :=
  GraphPath.ofWalk (_root_.SimpleGraph.Walk.cons huv _root_.SimpleGraph.Walk.nil)

@[simp] theorem ofAdj_source {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) :
    (ofAdj huv).source = u := rfl

@[simp] theorem ofAdj_target {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) :
    (ofAdj huv).target = v := rfl

theorem ofAdj_vertexSet_subset_pair {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) :
    (ofAdj huv).vertexSet ⊆ ({u, v} : Finset V) := by
  classical
  intro x hx
  have hxWalk :
      x ∈ ((_root_.SimpleGraph.Walk.cons huv _root_.SimpleGraph.Walk.nil).support.toFinset) :=
    GraphPath.ofWalk_vertexSet_subset
      (_root_.SimpleGraph.Walk.cons huv _root_.SimpleGraph.Walk.nil) hx
  simpa [ofAdj] using hxWalk

theorem ofAdj_internallyDisjointFromSet
    {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (U : Finset V) :
    (ofAdj huv).InternallyDisjointFromSet U := by
  classical
  intro x hx _hxU
  have hxPair := ofAdj_vertexSet_subset_pair huv hx
  simp at hxPair
  rcases hxPair with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ofAdj_edgeSet_subset_singleton {G : _root_.SimpleGraph V} {u v : V}
    (huv : G.Adj u v) :
    (ofAdj huv).edgeSet ⊆ ({s(u, v)} : Finset (Sym2 V)) := by
  classical
  intro e he
  have heWalk :
      e ∈ ((_root_.SimpleGraph.Walk.cons huv _root_.SimpleGraph.Walk.nil).edges.toFinset) :=
    GraphPath.ofWalk_edgeSet_subset
      (_root_.SimpleGraph.Walk.cons huv _root_.SimpleGraph.Walk.nil) he
  simpa [ofAdj] using heWalk

/-- If an unordered edge occurs on a graph path, both of its endpoints occur
on the path. -/
theorem endpoints_mem_vertexSet_of_edgeSet {G : _root_.SimpleGraph V}
    (P : GraphPath G) {u v : V} (he : s(u, v) ∈ P.edgeSet) :
    u ∈ P.vertexSet ∧ v ∈ P.vertexSet := by
  classical
  have heWalk : s(u, v) ∈ P.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using he)
  constructor
  · simpa [GraphPath.vertexSet] using
      P.walk.fst_mem_support_of_mem_edges heWalk
  · simpa [GraphPath.vertexSet] using
      P.walk.snd_mem_support_of_mem_edges heWalk

/-- A simple path with equal endpoints has no edges. -/
theorem edgeSet_eq_empty_of_source_eq_target {G : _root_.SimpleGraph V}
    (P : GraphPath G) (hst : P.source = P.target) :
    P.edgeSet = ∅ := by
  classical
  have hnone : ∀ e : Sym2 V, e ∉ P.edgeSet := by
    rw [Sym2.forall]
    intro a b he
    have ha : a ∈ P.vertexSet :=
      (endpoints_mem_vertexSet_of_edgeSet P he).1
    have hb : b ∈ P.vertexSet :=
      (endpoints_mem_vertexSet_of_edgeSet P he).2
    have ha_eq : a = P.source :=
      P.eq_source_of_source_eq_target_of_mem_vertexSet hst ha
    have hb_eq : b = P.source :=
      P.eq_source_of_source_eq_target_of_mem_vertexSet hst hb
    have hadj : G.Adj a b :=
      GraphPath.edgeSet_subset_edgeSet P he
    exact hadj.ne (by simpa [ha_eq, hb_eq])
  ext e
  constructor
  · intro he
    exact False.elim (hnone e he)
  · intro he
    simp at he

/-- On a simple path, the path-order index determines a vertex. -/
theorem eq_of_vertexIndex_eq {G : _root_.SimpleGraph V}
    (P : GraphPath G) {x y : V}
    (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet)
    (hidx : P.vertexIndex x = P.vertexIndex y) :
    x = y := by
  have hxy : P.Before x y :=
    (P.before_iff_vertexIndex_le).2 ⟨hx, hy, le_of_eq hidx⟩
  have hyx : P.Before y x :=
    (P.before_iff_vertexIndex_le).2 ⟨hy, hx, le_of_eq hidx.symm⟩
  exact P.before_antisymm hxy hyx

private theorem list_reverse_idxOf_le_of_idxOf_le
    {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : l.idxOf a ≤ l.idxOf b) :
    l.reverse.idxOf b ≤ l.reverse.idxOf a := by
  classical
  let ia := l.idxOf a
  let ib := l.idxOf b
  have hlen_rev : l.reverse.length = l.length := by
    simp
  have hia_lt : ia < l.length := by
    simpa [ia] using (List.idxOf_lt_length_iff.2 ha)
  have hib_lt : ib < l.length := by
    simpa [ib] using (List.idxOf_lt_length_iff.2 hb)
  let ra := l.length - 1 - ia
  let rb := l.length - 1 - ib
  have hra_lt : ra < l.reverse.length := by
    rw [List.length_reverse]
    simp [ra, ia]
    omega
  have hrb_lt : rb < l.reverse.length := by
    rw [List.length_reverse]
    simp [rb, ib]
    omega
  have hrev_get_a : l.reverse[ra]'hra_lt = a := by
    have hget : l.reverse[ra]'hra_lt = l[ia]'hia_lt := by
      have hidx_eq : l.length - 1 - ra = ia := by
        simp [ra, ia]
        omega
      have hget0 :=
        List.get_reverse' l ⟨ra, hra_lt⟩ (by
          rw [hidx_eq]
          exact hia_lt)
      change l.reverse.get ⟨ra, hra_lt⟩ = l.get ⟨ia, hia_lt⟩
      rw [hget0]
      congr
    have hidx : l[ia]'hia_lt = a := by
      simp [ia]
    exact hget.trans hidx
  have hrev_get_b : l.reverse[rb]'hrb_lt = b := by
    have hget : l.reverse[rb]'hrb_lt = l[ib]'hib_lt := by
      have hidx_eq : l.length - 1 - rb = ib := by
        simp [rb, ib]
        omega
      have hget0 :=
        List.get_reverse' l ⟨rb, hrb_lt⟩ (by
          rw [hidx_eq]
          exact hib_lt)
      change l.reverse.get ⟨rb, hrb_lt⟩ = l.get ⟨ib, hib_lt⟩
      rw [hget0]
      congr
    have hidx : l[ib]'hib_lt = b := by
      simp [ib]
    exact hget.trans hidx
  have hidx_a : l.reverse.idxOf a = ra := by
    have h := (List.nodup_reverse.mpr hl).idxOf_getElem ra hra_lt
    simpa [hrev_get_a] using h
  have hidx_b : l.reverse.idxOf b = rb := by
    have h := (List.nodup_reverse.mpr hl).idxOf_getElem rb hrb_lt
    simpa [hrev_get_b] using h
  rw [hidx_a, hidx_b]
  simp [ra, rb, ia, ib]
  omega

/-- Reversing a graph path reverses its path order. -/
theorem reverse_before_of_before {G : _root_.SimpleGraph V}
    (P : GraphPath G) {x y : V}
    (hxy : P.Before x y) :
    P.reverse.Before y x := by
  classical
  have hdata := (P.before_iff_vertexIndex_le).1 hxy
  have hx : x ∈ P.vertexSet := hdata.1
  have hy : y ∈ P.vertexSet := hdata.2.1
  have hxSupport : x ∈ P.walk.support := by
    simpa [GraphPath.vertexSet] using hx
  have hySupport : y ∈ P.walk.support := by
    simpa [GraphPath.vertexSet] using hy
  have hleSupport :
      P.walk.support.reverse.idxOf y ≤ P.walk.support.reverse.idxOf x :=
    list_reverse_idxOf_le_of_idxOf_le P.isPath.support_nodup
      hxSupport hySupport (by
        simpa [GraphPath.vertexIndex] using hdata.2.2)
  have hleRev :
      P.reverse.vertexIndex y ≤ P.reverse.vertexIndex x := by
    simpa [GraphPath.vertexIndex, GraphPath.reverse,
      _root_.SimpleGraph.Walk.support_reverse] using hleSupport
  exact (P.reverse.before_iff_vertexIndex_le).2
    ⟨by simpa using hy, by simpa using hx, hleRev⟩

omit [DecidableEq V] in
@[simp] theorem reverse_reverse {G : _root_.SimpleGraph V}
    (P : GraphPath G) :
    P.reverse.reverse = P := by
  cases P
  simp [GraphPath.reverse, _root_.SimpleGraph.Walk.reverse_reverse]

/-- Vertices adjacent to `v` through edges of a single simple path. -/
noncomputable def pathNeighborFinset {G : _root_.SimpleGraph V}
    (P : GraphPath G) (v : V) : Finset V :=
  P.vertexSet.filter fun w => s(v, w) ∈ P.edgeSet

theorem mem_pathNeighborFinset {G : _root_.SimpleGraph V}
    (P : GraphPath G) {v w : V} :
    w ∈ pathNeighborFinset P v ↔ w ∈ P.vertexSet ∧ s(v, w) ∈ P.edgeSet := by
  classical
  simp [pathNeighborFinset]

/-- A simple path contributes at most two neighbors to any vertex. -/
theorem pathNeighborFinset_card_le_two {G : _root_.SimpleGraph V}
    (P : GraphPath G) (v : V) :
    (pathNeighborFinset P v).card ≤ 2 := by
  classical
  let N := pathNeighborFinset P v
  have hcard_image :
      (N.image P.vertexIndex).card = N.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hxV : x ∈ P.vertexSet := (mem_pathNeighborFinset P).mp hx |>.1
    have hyV : y ∈ P.vertexSet := (mem_pathNeighborFinset P).mp hy |>.1
    exact eq_of_vertexIndex_eq P hxV hyV hxy
  have hsubset :
      N.image P.vertexIndex ⊆
        ({P.vertexIndex v - 1, P.vertexIndex v + 1} : Finset ℕ) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨w, hwN, rfl⟩
    have hwV : w ∈ P.vertexSet := (mem_pathNeighborFinset P).mp hwN |>.1
    have he : s(v, w) ∈ P.edgeSet := (mem_pathNeighborFinset P).mp hwN |>.2
    have hvV : v ∈ P.vertexSet :=
      (endpoints_mem_vertexSet_of_edgeSet P he).1
    have hne : w ≠ v := by
      intro hwv
      subst w
      have hadj : G.Adj v v := by
        simpa using P.edgeSet_subset_edgeSet he
      exact hadj.ne rfl
    have hidx_ne : P.vertexIndex w ≠ P.vertexIndex v := by
      intro hidx
      exact hne (eq_of_vertexIndex_eq P hwV hvV hidx)
    have hle_next : P.vertexIndex w ≤ P.vertexIndex v + 1 :=
      P.edge_vertexIndex_le_succ he
    have he_swap : s(w, v) ∈ P.edgeSet := by
      simpa [Sym2.eq_swap] using he
    have hle_prev : P.vertexIndex v ≤ P.vertexIndex w + 1 :=
      P.edge_vertexIndex_le_succ he_swap
    have hcase :
        P.vertexIndex w + 1 = P.vertexIndex v ∨
          P.vertexIndex w = P.vertexIndex v + 1 := by
      omega
    rcases hcase with hprev | hnext
    · have hwm : P.vertexIndex w = P.vertexIndex v - 1 := by
        omega
      simp [hwm]
    · simp [hnext]
  calc
    N.card = (N.image P.vertexIndex).card := hcard_image.symm
    _ ≤ ({P.vertexIndex v - 1, P.vertexIndex v + 1} : Finset ℕ).card :=
      Finset.card_le_card hsubset
    _ ≤ 2 := by
      simp

/-- An internal vertex of a simple path has two distinct path-neighbors. -/
theorem exists_two_distinct_path_neighbors_of_internal
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) {x : V}
    (hx : x ∈ P.vertexSet) (hx_source : x ≠ P.source)
    (hx_target : x ≠ P.target) :
    ∃ a b : V,
      a ≠ b ∧ s(x, a) ∈ P.edgeSet ∧ s(x, b) ∈ P.edgeSet := by
  classical
  let Q := P.takeUntil hx
  have hQne : Q.source ≠ Q.target := by
    intro h
    exact hx_source (by simpa [Q] using h.symm)
  let a : V := Q.penultimate
  let e₁ : Sym2 V := s(a, x)
  have he₁Qwalk : e₁ ∈ Q.walk.edges := by
    exact Q.walk.mk_penultimate_end_mem_edges
      (Q.walk_not_nil_of_source_ne_target hQne)
  have he₁Q : e₁ ∈ Q.edgeSet := by
    exact List.mem_toFinset.mpr
      (by simpa [Q, e₁, GraphPath.edgeSet] using he₁Qwalk)
  have he₁P : e₁ ∈ P.edgeSet := P.takeUntil_edgeSet_subset hx he₁Q
  let R := P.dropUntil hx
  have hRne : R.source ≠ R.target := by
    intro h
    exact hx_target (by simpa [R] using h)
  let b : V := R.walk.snd
  let e₂ : Sym2 V := s(x, b)
  have he₂Rwalk : e₂ ∈ R.walk.edges := by
    exact R.walk.mk_start_snd_mem_edges
      (R.walk_not_nil_of_source_ne_target hRne)
  have he₂R : e₂ ∈ R.edgeSet := by
    exact List.mem_toFinset.mpr
      (by simpa [R, e₂, GraphPath.edgeSet] using he₂Rwalk)
  have he₂P : e₂ ∈ P.edgeSet := P.dropUntil_edgeSet_subset hx he₂R
  have hne_edges : e₁ ≠ e₂ := by
    intro heq
    have hxwalk : x ∈ P.walk.support := by
      simpa [GraphPath.vertexSet] using hx
    have hdisj := P.isPath.isTrail.disjoint_edges_takeUntil_dropUntil hxwalk
    have he₁List : e₁ ∈ (P.walk.takeUntil x hxwalk).edges := by
      simpa [Q, e₁, GraphPath.takeUntil] using he₁Qwalk
    have he₂List : e₂ ∈ (P.walk.dropUntil x hxwalk).edges := by
      simpa [R, e₂, GraphPath.dropUntil] using he₂Rwalk
    exact hdisj he₁List (by simpa [heq] using he₂List)
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro hab
    exact hne_edges (by simp [e₁, e₂, hab, Sym2.eq_swap])
  · simpa [e₁, Sym2.eq_swap] using he₁P
  · simpa [e₂] using he₂P

/-- A simple path has at most one forward edge leaving a given vertex. -/
theorem forward_edge_unique
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) {u v w : V}
    (huvEdge : s(u, v) ∈ P.edgeSet) (huv : P.Before u v)
    (huv_ne : u ≠ v)
    (huwEdge : s(u, w) ∈ P.edgeSet) (huw : P.Before u w)
    (huw_ne : u ≠ w) :
    v = w := by
  classical
  have huV : u ∈ P.vertexSet :=
    (endpoints_mem_vertexSet_of_edgeSet P huvEdge).1
  have hvV : v ∈ P.vertexSet :=
    (endpoints_mem_vertexSet_of_edgeSet P huvEdge).2
  have hwV : w ∈ P.vertexSet :=
    (endpoints_mem_vertexSet_of_edgeSet P huwEdge).2
  have huvLe : P.vertexIndex u ≤ P.vertexIndex v :=
    ((P.before_iff_vertexIndex_le).1 huv).2.2
  have huwLe : P.vertexIndex u ≤ P.vertexIndex w :=
    ((P.before_iff_vertexIndex_le).1 huw).2.2
  have huvLt : P.vertexIndex u < P.vertexIndex v := by
    refine lt_of_le_of_ne huvLe ?_
    intro hidx
    exact huv_ne (eq_of_vertexIndex_eq P huV hvV hidx)
  have huwLt : P.vertexIndex u < P.vertexIndex w := by
    refine lt_of_le_of_ne huwLe ?_
    intro hidx
    exact huw_ne (eq_of_vertexIndex_eq P huV hwV hidx)
  have hvLe : P.vertexIndex v ≤ P.vertexIndex u + 1 :=
    P.edge_vertexIndex_le_succ huvEdge
  have hwLe : P.vertexIndex w ≤ P.vertexIndex u + 1 :=
    P.edge_vertexIndex_le_succ huwEdge
  have hvIdx : P.vertexIndex v = P.vertexIndex u + 1 := by omega
  have hwIdx : P.vertexIndex w = P.vertexIndex u + 1 := by omega
  exact eq_of_vertexIndex_eq P hvV hwV (hvIdx.trans hwIdx.symm)

/-- A simple path has at most one backward edge entering a given vertex. -/
theorem backward_edge_unique
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) {u v w : V}
    (hvuEdge : s(v, u) ∈ P.edgeSet) (hvu : P.Before v u)
    (hvu_ne : v ≠ u)
    (hwuEdge : s(w, u) ∈ P.edgeSet) (hwu : P.Before w u)
    (hwu_ne : w ≠ u) :
    v = w := by
  classical
  have huvRev : P.reverse.Before u v := by
    exact GraphPath.reverse_before_of_before P hvu
  have huwRev : P.reverse.Before u w := by
    exact GraphPath.reverse_before_of_before P hwu
  have huvEdgeRev : s(u, v) ∈ P.reverse.edgeSet := by
    simpa [Sym2.eq_swap] using hvuEdge
  have huwEdgeRev : s(u, w) ∈ P.reverse.edgeSet := by
    simpa [Sym2.eq_swap] using hwuEdge
  exact GraphPath.forward_edge_unique P.reverse
    huvEdgeRev huvRev hvu_ne.symm huwEdgeRev huwRev hwu_ne.symm

/-- A path endpoint has at most one neighbor through path edges. -/
theorem pathNeighborFinset_card_le_one_of_isEndpoint
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) {x : V}
    (hx : P.IsEndpoint x) :
    (pathNeighborFinset P x).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro y z hy hz
  rcases hx with hxSource | hxTarget
  · subst x
    have hyData := (mem_pathNeighborFinset P).1 hy
    have hzData := (mem_pathNeighborFinset P).1 hz
    have hy_ne : P.source ≠ y := by
      intro h
      have hadj : G.Adj P.source y := by
        simpa using GraphPath.edgeSet_subset_edgeSet P hyData.2
      exact hadj.ne h
    have hz_ne : P.source ≠ z := by
      intro h
      have hadj : G.Adj P.source z := by
        simpa using GraphPath.edgeSet_subset_edgeSet P hzData.2
      exact hadj.ne h
    exact GraphPath.forward_edge_unique P
      hyData.2 (P.source_before_of_mem hyData.1) hy_ne
      hzData.2 (P.source_before_of_mem hzData.1) hz_ne
  · subst x
    have hyData := (mem_pathNeighborFinset P).1 hy
    have hzData := (mem_pathNeighborFinset P).1 hz
    have hy_ne : y ≠ P.target := by
      intro h
      have hadj : G.Adj P.target y := by
        simpa using GraphPath.edgeSet_subset_edgeSet P hyData.2
      exact hadj.ne h.symm
    have hz_ne : z ≠ P.target := by
      intro h
      have hadj : G.Adj P.target z := by
        simpa using GraphPath.edgeSet_subset_edgeSet P hzData.2
      exact hadj.ne h.symm
    exact GraphPath.backward_edge_unique P
      (by simpa [Sym2.eq_swap] using hyData.2)
      (P.before_target_of_mem hyData.1) hy_ne
      (by simpa [Sym2.eq_swap] using hzData.2)
      (P.before_target_of_mem hzData.1) hz_ne

/-- Every non-target vertex of a simple path has a forward edge. -/
theorem exists_forward_edge_of_mem_not_target
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) {u : V}
    (hu : u ∈ P.vertexSet) (hu_target : u ≠ P.target) :
    ∃ v : V, s(u, v) ∈ P.edgeSet ∧ P.Before u v ∧ u ≠ v := by
  classical
  let R := P.dropUntil hu
  have hRne : R.source ≠ R.target := by
    simpa [R] using hu_target
  let v : V := R.walk.snd
  have heRwalk : s(R.source, v) ∈ R.walk.edges := by
    exact R.walk.mk_start_snd_mem_edges
      (R.walk_not_nil_of_source_ne_target hRne)
  have heR : s(R.source, v) ∈ R.edgeSet := by
    exact List.mem_toFinset.mpr
      (by simpa [v, GraphPath.edgeSet] using heRwalk)
  have heP : s(u, v) ∈ P.edgeSet := by
    simpa [R] using P.dropUntil_edgeSet_subset hu heR
  have hvR : v ∈ R.vertexSet :=
    (endpoints_mem_vertexSet_of_edgeSet R heR).2
  have hbefore : P.Before u v := ⟨hu, by simpa [R] using hvR⟩
  have hne : u ≠ v := by
    have hadj : G.Adj R.source v := by
      simpa [v] using R.walk.adj_snd
        (R.walk_not_nil_of_source_ne_target hRne)
    simpa [R] using hadj.ne
  exact ⟨v, heP, hbefore, hne⟩

/-- Every non-source vertex of a simple path has an incoming edge from its
path predecessor. -/
theorem exists_backward_edge_of_mem_not_source
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) {u : V}
    (hu : u ∈ P.vertexSet) (hu_source : u ≠ P.source) :
    ∃ v : V, s(v, u) ∈ P.edgeSet ∧ P.Before v u ∧ v ≠ u := by
  classical
  have huRev : u ∈ P.reverse.vertexSet := by
    simpa using hu
  have huRevTarget : u ≠ P.reverse.target := by
    simpa using hu_source
  rcases exists_forward_edge_of_mem_not_target
      P.reverse huRev huRevTarget with
    ⟨v, heRev, hRevBefore, hne⟩
  have heP : s(v, u) ∈ P.edgeSet := by
    simpa [Sym2.eq_swap] using heRev
  have hbefore : P.Before v u := by
    have huvOrig := reverse_before_of_before P.reverse hRevBefore
    simpa [GraphPath.reverse] using huvOrig
  exact ⟨v, heP, hbefore, hne.symm⟩

/-- If a walk is already simple, mathlib's cycle-erasure operation leaves it
unchanged. -/
theorem walk_bypass_eq_self_of_isPath
    {G : _root_.SimpleGraph V} {s t : V} (W : G.Walk s t)
    (hW : W.IsPath) :
    W.bypass = W := by
  induction W with
  | nil =>
      rfl
  | cons hxy W ih =>
      have htail :=
        (_root_.SimpleGraph.Walk.cons_isPath_iff hxy W).1 hW
      simp only [_root_.SimpleGraph.Walk.bypass]
      split_ifs with hmem
      · exact False.elim
          (htail.2 (_root_.SimpleGraph.Walk.support_bypass_subset W hmem))
      · simp [ih htail.1]

/-- For a simple walk, `GraphPath.ofWalk` has exactly the original walk's
edge set; no cycle-erasure occurs. -/
theorem ofWalk_edgeSet_eq_of_isPath
    {G : _root_.SimpleGraph V} {s t : V} (W : G.Walk s t)
    (hW : W.IsPath) :
    (Lax17Proofs.SimpleGraph.GraphPath.ofWalk W).edgeSet =
      W.edges.toFinset := by
  classical
  change W.bypass.edges.toFinset = W.edges.toFinset
  rw [walk_bypass_eq_self_of_isPath W hW]

/-- For a simple walk, `GraphPath.ofWalk` has exactly the original walk's
vertex set; no cycle-erasure occurs. -/
theorem ofWalk_vertexSet_eq_of_isPath
    {G : _root_.SimpleGraph V} {s t : V} (W : G.Walk s t)
    (hW : W.IsPath) :
    (Lax17Proofs.SimpleGraph.GraphPath.ofWalk W).vertexSet =
      W.support.toFinset := by
  classical
  change W.bypass.support.toFinset = W.support.toFinset
  rw [walk_bypass_eq_self_of_isPath W hW]

end GraphPath

namespace TopologicalMinorModel

variable {V₀ W : Type u} [Fintype V₀] [DecidableEq V₀]
variable [Fintype W] [DecidableEq W]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V₀}

/-- Pattern edges of a topological-minor model incident with `x`, using the
model's chosen orientation of pattern edges. -/
noncomputable def incidentEdgeFinset
    (M : TopologicalMinorModel H G) (x : W) : Finset H.edgeSet :=
  (Finset.univ : Finset H.edgeSet).filter fun e =>
    M.edgeSource e = x ∨ M.edgeTarget e = x

theorem mem_incidentEdgeFinset
    (M : TopologicalMinorModel H G) (x : W) (e : H.edgeSet) :
    e ∈ M.incidentEdgeFinset x ↔
      M.edgeSource e = x ∨ M.edgeTarget e = x := by
  classical
  simp [incidentEdgeFinset]

/-- The endpoint of an oriented pattern edge opposite `x`.  For non-incident
edges this returns the source endpoint; the lemmas below only use it on the
incident-edge finset. -/
def incidentOther (M : TopologicalMinorModel H G) (x : W)
    (e : H.edgeSet) : W :=
  if M.edgeSource e = x then M.edgeTarget e else M.edgeSource e

theorem edge_eq_mk_self_incidentOther
    (M : TopologicalMinorModel H G) {x : W} {e : H.edgeSet}
    (he : e ∈ M.incidentEdgeFinset x) :
    s(x, M.incidentOther x e) = (e : Sym2 W) := by
  classical
  have hinc := (M.mem_incidentEdgeFinset x e).1 he
  by_cases hsource : M.edgeSource e = x
  · simpa [incidentOther, hsource] using M.edge_eq e
  · have htarget : M.edgeTarget e = x := by
      rcases hinc with h | h
      · exact False.elim (hsource h)
      · exact h
    have h := M.edge_eq e
    simpa [incidentOther, hsource, htarget, Sym2.eq_swap] using h

theorem incidentOther_injective_on
    (M : TopologicalMinorModel H G) (x : W) :
    Set.InjOn (M.incidentOther x) (M.incidentEdgeFinset x : Set H.edgeSet) := by
  classical
  intro e he f hf hother
  apply Subtype.ext
  have heq := M.edge_eq_mk_self_incidentOther he
  have hfq := M.edge_eq_mk_self_incidentOther hf
  calc
    (e : Sym2 W) = s(x, M.incidentOther x e) := heq.symm
    _ = s(x, M.incidentOther x f) := by rw [hother]
    _ = (f : Sym2 W) := hfq

theorem incidentOther_mem_neighborFinset
    (M : TopologicalMinorModel H G) {d : ℕ}
    (hH : MaxDegreeAtMost H d) {x : W} {e : H.edgeSet}
    (he : e ∈ M.incidentEdgeFinset x) :
    M.incidentOther x e ∈ MaxDegreeAtMost.neighborFinset hH x := by
  classical
  have hinc := (M.mem_incidentEdgeFinset x e).1 he
  refine (MaxDegreeAtMost.mem_neighborFinset hH x
    (M.incidentOther x e)).2 ?_
  by_cases hsource : M.edgeSource e = x
  · simpa [incidentOther, hsource] using M.edge_adj e
  · have htarget : M.edgeTarget e = x := by
      rcases hinc with h | h
      · exact False.elim (hsource h)
      · exact h
    simpa [incidentOther, hsource, htarget] using (M.edge_adj e).symm

theorem incidentEdgeFinset_card_le
    (M : TopologicalMinorModel H G) {d : ℕ}
    (hH : MaxDegreeAtMost H d) (x : W) :
    (M.incidentEdgeFinset x).card ≤ d := by
  classical
  have hcard_image :
      ((M.incidentEdgeFinset x).image (M.incidentOther x)).card =
        (M.incidentEdgeFinset x).card := by
    apply Finset.card_image_of_injOn
    intro e he f hf hother
    exact M.incidentOther_injective_on x he hf hother
  have hsub :
      (M.incidentEdgeFinset x).image (M.incidentOther x) ⊆
        MaxDegreeAtMost.neighborFinset hH x := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨e, he, rfl⟩
    exact M.incidentOther_mem_neighborFinset hH he
  calc
    (M.incidentEdgeFinset x).card =
        ((M.incidentEdgeFinset x).image (M.incidentOther x)).card :=
      hcard_image.symm
    _ ≤ (MaxDegreeAtMost.neighborFinset hH x).card :=
      Finset.card_le_card hsub
    _ ≤ d := MaxDegreeAtMost.card_neighborFinset_le hH x

/-- The neighbors of a branch vertex in the model support graph, grouped by
incident pattern edges. -/
noncomputable def branchSupportNeighborFinset
    (M : TopologicalMinorModel H G) (x : W) : Finset V₀ :=
  (M.incidentEdgeFinset x).biUnion fun e =>
    GraphPath.pathNeighborFinset (M.edgePathInSupportGraph e) (M.branchVertex x)

theorem branchVertex_isEndpoint_edgePath_of_mem_incident
    (M : TopologicalMinorModel H G) {x : W} {e : H.edgeSet}
    (he : e ∈ M.incidentEdgeFinset x) :
    (M.edgePathInSupportGraph e).IsEndpoint (M.branchVertex x) := by
  classical
  have hinc := (M.mem_incidentEdgeFinset x e).1 he
  rcases hinc with hsource | htarget
  · left
    rw [edgePathInSupportGraph_source, M.edgePath_source e, hsource]
  · right
    rw [edgePathInSupportGraph_target, M.edgePath_target e, htarget]

theorem branchSupportNeighborFinset_card_le_incident
    (M : TopologicalMinorModel H G) (x : W) :
    (M.branchSupportNeighborFinset x).card ≤
      (M.incidentEdgeFinset x).card := by
  classical
  have hunion :
      (M.branchSupportNeighborFinset x).card ≤
        ∑ e ∈ M.incidentEdgeFinset x,
          (GraphPath.pathNeighborFinset
            (M.edgePathInSupportGraph e) (M.branchVertex x)).card := by
    simpa [branchSupportNeighborFinset] using
      (Finset.card_biUnion_le
        (s := M.incidentEdgeFinset x)
        (t := fun e =>
          GraphPath.pathNeighborFinset
            (M.edgePathInSupportGraph e) (M.branchVertex x)))
  have hsum :
      (∑ e ∈ M.incidentEdgeFinset x,
          (GraphPath.pathNeighborFinset
            (M.edgePathInSupportGraph e) (M.branchVertex x)).card) ≤
        ∑ _e ∈ M.incidentEdgeFinset x, 1 := by
    refine Finset.sum_le_sum ?_
    intro e he
    exact GraphPath.pathNeighborFinset_card_le_one_of_isEndpoint
      (M.edgePathInSupportGraph e)
      (M.branchVertex_isEndpoint_edgePath_of_mem_incident he)
  exact hunion.trans (by
    simpa using hsum)

theorem branchSupportNeighborFinset_card_le
    (M : TopologicalMinorModel H G) {d : ℕ}
    (hH : MaxDegreeAtMost H d) (x : W) :
    (M.branchSupportNeighborFinset x).card ≤ d :=
  (M.branchSupportNeighborFinset_card_le_incident x).trans
    (M.incidentEdgeFinset_card_le hH x)

theorem branchSupportNeighborFinset_contains_adj
    (M : TopologicalMinorModel H G) {x : W} {u : V₀}
    (hu : M.supportGraph.Adj (M.branchVertex x) u) :
    u ∈ M.branchSupportNeighborFinset x := by
  classical
  rw [supportGraph, _root_.SimpleGraph.fromEdgeSet_adj] at hu
  rcases Finset.mem_biUnion.mp hu.1 with ⟨e, _he, hedge⟩
  have hbranch_vertex :
      M.branchVertex x ∈ (M.edgePath e).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (M.edgePath e) hedge).1
  have hincident : e ∈ M.incidentEdgeFinset x := by
    rw [M.mem_incidentEdgeFinset x e]
    by_cases hsource : x = M.edgeSource e
    · exact Or.inl hsource.symm
    by_cases htarget : x = M.edgeTarget e
    · exact Or.inr htarget.symm
    exfalso
    have hnot_source :
        M.branchVertex x ≠ (M.edgePath e).source := by
      intro h
      apply hsource
      apply M.branch_injective
      simpa [M.edgePath_source e] using h
    have hnot_target :
        M.branchVertex x ≠ (M.edgePath e).target := by
      intro h
      apply htarget
      apply M.branch_injective
      simpa [M.edgePath_target e] using h
    have hinternal :
        M.branchVertex x ∈ pathInternalVertexSet (M.edgePath e) := by
      simp [pathInternalVertexSet, hbranch_vertex, hnot_source, hnot_target]
    exact M.edgePath_internal_disjoint_branches e x hsource htarget hinternal
  have hedge_support :
      s(M.branchVertex x, u) ∈ (M.edgePathInSupportGraph e).edgeSet := by
    simpa using hedge
  have hu_vertex :
      u ∈ (M.edgePathInSupportGraph e).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.edgePathInSupportGraph e) hedge_support).2
  exact Finset.mem_biUnion.mpr ⟨e, hincident,
    (GraphPath.mem_pathNeighborFinset (M.edgePathInSupportGraph e)).2
      ⟨hu_vertex, hedge_support⟩⟩

theorem branchVertex_supportGraph_degreeAtMost
    (M : TopologicalMinorModel H G) {d : ℕ}
    (hH : MaxDegreeAtMost H d) (x : W) :
    DegreeAtMost M.supportGraph (M.branchVertex x) d :=
  degreeAtMost_of_adj_subset_finset (M.branchSupportNeighborFinset x)
    (fun _u hu => M.branchSupportNeighborFinset_contains_adj hu)
    (M.branchSupportNeighborFinset_card_le hH x)

/-- A vertex on a realizing path that is not a model branch vertex is internal
to that realizing path. -/
theorem mem_internal_of_mem_edgePath_of_not_branch
    (M : TopologicalMinorModel H G) {v : V₀}
    (hvBranch : ∀ x : W, v ≠ M.branchVertex x)
    {e : H.edgeSet} (hv : v ∈ (M.edgePath e).vertexSet) :
    v ∈ pathInternalVertexSet (M.edgePath e) := by
  classical
  have hnot_source : v ≠ (M.edgePath e).source := by
    intro h
    exact hvBranch (M.edgeSource e) (by
      simpa [M.edgePath_source e] using h)
  have hnot_target : v ≠ (M.edgePath e).target := by
    intro h
    exact hvBranch (M.edgeTarget e) (by
      simpa [M.edgePath_target e] using h)
  simp [pathInternalVertexSet, hv, hnot_source, hnot_target]

theorem edge_eq_of_internal_and_edgePath_edge
    (M : TopologicalMinorModel H G) {v u : V₀}
    (hvBranch : ∀ x : W, v ≠ M.branchVertex x)
    {e f : H.edgeSet}
    (he : v ∈ pathInternalVertexSet (M.edgePath e))
    (hfedge : s(v, u) ∈ (M.edgePath f).edgeSet) :
    f = e := by
  classical
  by_contra hfe
  have hvf_vertex :
      v ∈ (M.edgePath f).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (M.edgePath f) hfedge).1
  have hf_internal :
      v ∈ pathInternalVertexSet (M.edgePath f) :=
    M.mem_internal_of_mem_edgePath_of_not_branch hvBranch hvf_vertex
  exact Finset.disjoint_left.mp
    (M.edgePath_pairwise_internal_disjoint hfe) hf_internal he

theorem internalVertex_supportGraph_degreeAtMost_two
    (M : TopologicalMinorModel H G) {v : V₀}
    (hvBranch : ∀ x : W, v ≠ M.branchVertex x)
    {e : H.edgeSet}
    (he : v ∈ pathInternalVertexSet (M.edgePath e)) :
    DegreeAtMost M.supportGraph v 2 := by
  classical
  refine degreeAtMost_of_adj_subset_finset
    (GraphPath.pathNeighborFinset (M.edgePathInSupportGraph e) v) ?_
    (GraphPath.pathNeighborFinset_card_le_two (M.edgePathInSupportGraph e) v)
  intro u huv
  rw [supportGraph, _root_.SimpleGraph.fromEdgeSet_adj] at huv
  rcases Finset.mem_biUnion.mp huv.1 with ⟨f, _hf, hfedge⟩
  have hfe : f = e :=
    M.edge_eq_of_internal_and_edgePath_edge hvBranch he hfedge
  subst f
  have hedge_support :
      s(v, u) ∈ (M.edgePathInSupportGraph e).edgeSet := by
    simpa using hfedge
  have hu_vertex :
      u ∈ (M.edgePathInSupportGraph e).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.edgePathInSupportGraph e) hedge_support).2
  exact (GraphPath.mem_pathNeighborFinset (M.edgePathInSupportGraph e)).2
    ⟨hu_vertex, hedge_support⟩

theorem supportGraph_degreeAtMost_zero_of_not_branch_not_internal
    (M : TopologicalMinorModel H G) {v : V₀}
    (hvBranch : ∀ x : W, v ≠ M.branchVertex x)
    (hvInternal : ∀ e : H.edgeSet,
      v ∉ pathInternalVertexSet (M.edgePath e)) :
    DegreeAtMost M.supportGraph v 0 := by
  classical
  refine degreeAtMost_of_adj_subset_finset (∅ : Finset V₀) ?_ (by simp)
  intro u huv
  rw [supportGraph, _root_.SimpleGraph.fromEdgeSet_adj] at huv
  rcases Finset.mem_biUnion.mp huv.1 with ⟨e, _he, hedge⟩
  have hv_vertex :
      v ∈ (M.edgePath e).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (M.edgePath e) hedge).1
  have hv_internal :
      v ∈ pathInternalVertexSet (M.edgePath e) :=
    M.mem_internal_of_mem_edgePath_of_not_branch hvBranch hv_vertex
  exact False.elim (hvInternal e hv_internal)

theorem supportGraph_maxDegreeAtMost_of_maxDegreeAtMost
    (M : TopologicalMinorModel H G)
    (hH : MaxDegreeAtMost H 3) :
    MaxDegreeAtMost M.supportGraph 3 := by
  classical
  intro v
  by_cases hbranch : ∃ x : W, v = M.branchVertex x
  · rcases hbranch with ⟨x, rfl⟩
    exact M.branchVertex_supportGraph_degreeAtMost hH x
  · have hvBranch : ∀ x : W, v ≠ M.branchVertex x := by
      intro x hv
      exact hbranch ⟨x, hv⟩
    by_cases hinternal :
        ∃ e : H.edgeSet, v ∈ pathInternalVertexSet (M.edgePath e)
    · rcases hinternal with ⟨e, he⟩
      exact DegreeAtMost.mono
        (M.internalVertex_supportGraph_degreeAtMost_two hvBranch he)
        (by omega)
    · have hvInternal : ∀ e : H.edgeSet,
          v ∉ pathInternalVertexSet (M.edgePath e) := by
        intro e he
        exact hinternal ⟨e, he⟩
      exact DegreeAtMost.mono
        (M.supportGraph_degreeAtMost_zero_of_not_branch_not_internal
          hvBranch hvInternal)
        (by omega)

end TopologicalMinorModel

/-- Three distinct neighbors contradict a degree-at-most-two certificate. -/
theorem not_degreeAtMost_two_of_three_adj
    {G : _root_.SimpleGraph V} {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ DegreeAtMost G v 2 := by
  classical
  rintro ⟨N, hN, hcard⟩
  let T : Finset V := {a, b, c}
  have hTsubset : T ⊆ N := by
    intro x hx
    simp [T] at hx
    rcases hx with hx | hx | hx
    · subst x
      exact (hN a).2 ha
    · subst x
      exact (hN b).2 hb
    · subst x
      exact (hN c).2 hc
  have hTcard : T.card = 3 := by
    simp [T, hab, hac, hbc]
  have hle : 3 ≤ N.card := by
    simpa [hTcard] using Finset.card_le_card hTsubset
  omega

/-- Two distinct neighbors contradict a degree-at-most-one certificate. -/
theorem not_degreeAtMost_one_of_two_adj
    {G : _root_.SimpleGraph V} {v a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) :
    ¬ DegreeAtMost G v 1 := by
  classical
  rintro ⟨N, hN, hcard⟩
  let T : Finset V := {a, b}
  have hTsubset : T ⊆ N := by
    intro x hx
    simp [T] at hx
    rcases hx with hx | hx
    · subst x
      exact (hN a).2 ha
    · subst x
      exact (hN b).2 hb
  have hTcard : T.card = 2 := by
    simp [T, hab]
  have hle : 2 ≤ N.card := by
    simpa [hTcard] using Finset.card_le_card hTsubset
  omega

namespace GraphPath

/-- A vertex of degree at most one in the ambient graph can only occur as a
path endpoint. -/
theorem isEndpoint_of_mem_vertexSet_of_degreeAtMost_one
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) {x : V}
    (hdeg : DegreeAtMost G x 1)
    (hx : x ∈ P.vertexSet) :
    P.IsEndpoint x := by
  classical
  by_cases hx_source : x = P.source
  · exact Or.inl hx_source
  by_cases hx_target : x = P.target
  · exact Or.inr hx_target
  rcases exists_two_distinct_path_neighbors_of_internal P
      hx hx_source hx_target with
    ⟨a, b, hab, haEdge, hbEdge⟩
  have haAdj : G.Adj x a := by
    simpa using GraphPath.edgeSet_subset_edgeSet P haEdge
  have hbAdj : G.Adj x b := by
    simpa using GraphPath.edgeSet_subset_edgeSet P hbEdge
  exact False.elim
    (not_degreeAtMost_one_of_two_adj haAdj hbAdj hab hdeg)

/-- If a finite vertex set is closed under taking graph neighbors, then a
path whose source lies in that set stays in that set. -/
theorem vertexSet_subset_of_source_mem_of_adj_closed
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) (U : Finset V)
    (hsource : P.source ∈ U)
    (hclosed : ∀ ⦃x y : V⦄, x ∈ U → G.Adj x y → y ∈ U) :
    P.vertexSet ⊆ U := by
  classical
  intro z hz
  have hzSupport : z ∈ P.walk.support := by
    simpa [GraphPath.vertexSet] using hz
  have hwalk :
      ∀ {a b : V} (p : G.Walk a b), a ∈ U →
        ∀ z : V, z ∈ p.support → z ∈ U := by
    intro a b p
    induction p with
    | nil =>
        intro ha z hz
        simp at hz
        simpa [hz] using ha
    | cons hxy p ih =>
        intro ha z hz
        simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ha
        · exact ih (hclosed ha hxy) z hz
  exact hwalk P.walk hsource z hzSupport

end GraphPath

@[simp] theorem perfectPathPacking_reverse_vertexSet
    {G : _root_.SimpleGraph V} {S T : Finset V}
    (P : PerfectPathPacking G S T) :
    P.reverse.toPathPacking.vertexSet = P.toPathPacking.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet, PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨i, hv⟩
    exact ⟨i, by simpa using hv⟩
  · rintro ⟨i, hv⟩
    exact ⟨i, by simpa using hv⟩

@[simp] theorem perfectPathPacking_reverse_edgeSet
    {G : _root_.SimpleGraph V} {S T : Finset V}
    (P : PerfectPathPacking G S T) :
    P.reverse.toPathPacking.edgeSet = P.toPathPacking.edgeSet := by
  classical
  ext e
  rw [PathPacking.mem_edgeSet, PathPacking.mem_edgeSet]
  constructor
  · rintro ⟨i, he⟩
    exact ⟨i, by simpa using he⟩
  · rintro ⟨i, he⟩
    exact ⟨i, by simpa using he⟩

@[simp] theorem perfectPathPacking_reverse_spanningGraph
    {G : _root_.SimpleGraph V} {S T : Finset V}
    (P : PerfectPathPacking G S T) :
    P.reverse.toPathPacking.spanningGraph = P.toPathPacking.spanningGraph := by
  classical
  ext u v
  simp [PathPacking.spanningGraph]

namespace GraphPath

/-- Regard a single graph path as a one-path perfect packing between its
singleton endpoint sets. -/
noncomputable def singletonPerfectPathPacking
    {G : _root_.SimpleGraph V} (P : GraphPath G) :
    PerfectPathPacking G {P.source} {P.target} where
  toPathPacking := {
    Index := PUnit
    path := fun _ => P
    connects := by
      intro _
      exact Or.inl ⟨by simp, by simp⟩
    node_disjoint := by
      intro i j hij
      cases i
      cases j
      exact False.elim (hij rfl) }
  source_mem := fun _ => by simp
  target_mem := fun _ => by simp
  source_bijective := by
    constructor
    · intro i j _h
      cases i
      cases j
      rfl
    · intro v
      refine ⟨PUnit.unit, ?_⟩
      apply Subtype.ext
      have hvMem : v.1 ∈ ({P.source} : Finset V) := v.2
      have hv : v.1 = P.source := Finset.mem_singleton.mp hvMem
      simpa [hv]
  target_bijective := by
    constructor
    · intro i j _h
      cases i
      cases j
      rfl
    · intro v
      refine ⟨PUnit.unit, ?_⟩
      apply Subtype.ext
      have hvMem : v.1 ∈ ({P.target} : Finset V) := v.2
      have hv : v.1 = P.target := Finset.mem_singleton.mp hvMem
      simpa [hv]

@[simp] theorem singletonPerfectPathPacking_path
    {G : _root_.SimpleGraph V} (P : GraphPath G)
    (i : (singletonPerfectPathPacking P).Index) :
    (singletonPerfectPathPacking P).path i = P := rfl

@[simp] theorem singletonPerfectPathPacking_card
    {G : _root_.SimpleGraph V} (P : GraphPath G) :
    (singletonPerfectPathPacking P).card = 1 := by
  rfl

@[simp] theorem singletonPerfectPathPacking_vertexSet
    {G : _root_.SimpleGraph V} (P : GraphPath G) :
    (singletonPerfectPathPacking P).toPathPacking.vertexSet = P.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨i, hv⟩
    simpa using hv
  · intro hv
    exact ⟨PUnit.unit, by simpa using hv⟩

/-- A singleton path packing has degree at most one at an endpoint of its
single path. -/
theorem singletonPerfectPathPacking_spanningGraph_degreeAtMost_one_of_isEndpoint
    {G : _root_.SimpleGraph V}
    (P : GraphPath G) {x : V}
    (hx : P.IsEndpoint x) :
    DegreeAtMost
      (singletonPerfectPathPacking P).toPathPacking.spanningGraph x 1 := by
  classical
  let N := pathNeighborFinset P x
  refine ⟨N, ?_, pathNeighborFinset_card_le_one_of_isEndpoint P hx⟩
  intro y
  constructor
  · intro hy
    have he : s(x, y) ∈ P.edgeSet :=
      (mem_pathNeighborFinset P).1 hy |>.2
    have hne : x ≠ y := by
      have hadj : G.Adj x y := by
        simpa using GraphPath.edgeSet_subset_edgeSet P he
      exact hadj.ne
    simp [singletonPerfectPathPacking,
      PathPacking.spanningGraph_adj_iff_exists_path_edge, he, hne]
  · intro hxy
    rcases
        (PathPacking.spanningGraph_adj_iff_exists_path_edge
          ((singletonPerfectPathPacking P).toPathPacking)).1 hxy with
      ⟨⟨i, he⟩, _hne⟩
    have heP : s(x, y) ∈ P.edgeSet := by
      simpa [singletonPerfectPathPacking] using he
    have hyP : y ∈ P.vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet P heP).2
    exact (mem_pathNeighborFinset P).2 ⟨hyP, heP⟩

/-- The oriented segment of `P` from `x` to `y`.  If `x` occurs after `y` in
the stored orientation of `P`, the ordered segment is reversed. -/
noncomputable def segmentBetween
    {G : _root_.SimpleGraph V} (P : GraphPath G)
    {x y : V} (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet) :
    GraphPath G := by
  classical
  by_cases hxy : P.vertexIndex x ≤ P.vertexIndex y
  · exact P.segmentOfBefore
      ((P.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩)
  · have hyx : P.vertexIndex y ≤ P.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    exact (P.segmentOfBefore
      ((P.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩)).reverse

@[simp] theorem segmentBetween_source
    {G : _root_.SimpleGraph V} (P : GraphPath G)
    {x y : V} (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet) :
    (segmentBetween P hx hy).source = x := by
  classical
  unfold segmentBetween
  split <;> simp

@[simp] theorem segmentBetween_target
    {G : _root_.SimpleGraph V} (P : GraphPath G)
    {x y : V} (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet) :
    (segmentBetween P hx hy).target = y := by
  classical
  unfold segmentBetween
  split <;> simp

theorem segmentBetween_vertexSet_subset
    {G : _root_.SimpleGraph V} (P : GraphPath G)
    {x y : V} (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet) :
    (segmentBetween P hx hy).vertexSet ⊆ P.vertexSet := by
  classical
  intro z hz
  by_cases hxy : P.vertexIndex x ≤ P.vertexIndex y
  · let hbefore : P.Before x y :=
      (P.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩
    have hz' : z ∈ (P.segmentOfBefore hbefore).vertexSet := by
      simpa [segmentBetween, hxy, hbefore] using hz
    exact P.segmentOfBefore_vertexSet_subset hbefore hz'
  · have hyx : P.vertexIndex y ≤ P.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    let hbefore : P.Before y x :=
      (P.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩
    have hz' : z ∈ (P.segmentOfBefore hbefore).vertexSet := by
      simpa [segmentBetween, hxy, hbefore, hyx] using hz
    exact P.segmentOfBefore_vertexSet_subset hbefore hz'

theorem segmentBetween_edgeSet_subset
    {G : _root_.SimpleGraph V} (P : GraphPath G)
    {x y : V} (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet) :
    (segmentBetween P hx hy).edgeSet ⊆ P.edgeSet := by
  classical
  intro e he
  by_cases hxy : P.vertexIndex x ≤ P.vertexIndex y
  · let hbefore : P.Before x y :=
      (P.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩
    have he' : e ∈ (P.segmentOfBefore hbefore).edgeSet := by
      simpa [segmentBetween, hxy, hbefore] using he
    exact P.segmentOfBefore_edgeSet_subset hbefore he'
  · have hyx : P.vertexIndex y ≤ P.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    let hbefore : P.Before y x :=
      (P.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩
    have he' : e ∈ (P.segmentOfBefore hbefore).edgeSet := by
      simpa [segmentBetween, hxy, hbefore, hyx] using he
    exact P.segmentOfBefore_edgeSet_subset hbefore he'

theorem source_not_mem_segmentBetween_of_ne
    {G : _root_.SimpleGraph V} (P : GraphPath G)
    {x y : V} (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet)
    (hsx : P.source ≠ x) (hsy : P.source ≠ y) :
    P.source ∉ (segmentBetween P hx hy).vertexSet := by
  classical
  by_cases hxy : P.vertexIndex x ≤ P.vertexIndex y
  · let hbefore : P.Before x y :=
      (P.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩
    have hnot :
        P.source ∉ (P.segmentOfBefore hbefore).vertexSet :=
      P.not_mem_segmentOfBefore_of_before_source hbefore
        (P.source_before_of_mem hx) hsx
    simpa [segmentBetween, hxy, hbefore] using hnot
  · have hyx : P.vertexIndex y ≤ P.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    let hbefore : P.Before y x :=
      (P.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩
    have hnot :
        P.source ∉ (P.segmentOfBefore hbefore).vertexSet :=
      P.not_mem_segmentOfBefore_of_before_source hbefore
        (P.source_before_of_mem hy) hsy
    simpa [segmentBetween, hxy, hbefore, hyx] using hnot

theorem target_not_mem_segmentBetween_of_ne
    {G : _root_.SimpleGraph V} (P : GraphPath G)
    {x y : V} (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet)
    (hxt : x ≠ P.target) (hyt : y ≠ P.target) :
    P.target ∉ (segmentBetween P hx hy).vertexSet := by
  classical
  by_cases hxy : P.vertexIndex x ≤ P.vertexIndex y
  · let hbefore : P.Before x y :=
      (P.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩
    have hnot :
        P.target ∉ (P.segmentOfBefore hbefore).vertexSet :=
      P.not_mem_segmentOfBefore_of_target_before hbefore
        (P.before_target_of_mem hy) hyt.symm
    simpa [segmentBetween, hxy, hbefore] using hnot
  · have hyx : P.vertexIndex y ≤ P.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    let hbefore : P.Before y x :=
      (P.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩
    have hnot :
        P.target ∉ (P.segmentOfBefore hbefore).vertexSet :=
      P.not_mem_segmentOfBefore_of_target_before hbefore
        (P.before_target_of_mem hx) hxt.symm
    simpa [segmentBetween, hxy, hbefore, hyx] using hnot

/-- Prefix of `Q` up to its first intersection with `R`. -/
noncomputable def cleanReroutePrefix
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) : GraphPath G :=
  Q.cleanPrefixToSet R.vertexSet hne

/-- Suffix of `Q` after its last intersection with `R`. -/
noncomputable def cleanRerouteSuffix
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) : GraphPath G :=
  Q.cleanSuffixFromSet R.vertexSet hne

/-- Red segment connecting the first and last vertices where `Q` meets `R`. -/
noncomputable def cleanRerouteMiddle
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) : GraphPath G :=
  segmentBetween R
    (Q.firstHitVertex_mem_set R.vertexSet hne)
    (Q.lastHitVertex_mem_set R.vertexSet hne)

/-- Replace the portion of `Q` between its first and last intersections with
`R` by the corresponding segment of `R`, then erase any cycle. -/
noncomputable def cleanRerouteThrough
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) : GraphPath G :=
  (cleanReroutePrefix R Q hne).append3WithEqToPath
    (cleanRerouteMiddle R Q hne)
    (cleanRerouteSuffix R Q hne)
    (by simp [cleanReroutePrefix, cleanRerouteMiddle])
    (by simp [cleanRerouteMiddle, cleanRerouteSuffix])

@[simp] theorem cleanRerouteThrough_source
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) :
    (cleanRerouteThrough R Q hne).source = Q.source := by
  simp [cleanRerouteThrough, cleanReroutePrefix]

@[simp] theorem cleanRerouteThrough_target
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) :
    (cleanRerouteThrough R Q hne).target = Q.target := by
  simp [cleanRerouteThrough, cleanRerouteSuffix]

theorem cleanRerouteThrough_edgeSet_subset
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) :
    (cleanRerouteThrough R Q hne).edgeSet ⊆
      (cleanReroutePrefix R Q hne).edgeSet ∪
        (cleanRerouteMiddle R Q hne).edgeSet ∪
          (cleanRerouteSuffix R Q hne).edgeSet := by
  simpa [cleanRerouteThrough] using
    (cleanReroutePrefix R Q hne).append3WithEqToPath_edgeSet_subset
      (cleanRerouteMiddle R Q hne)
      (cleanRerouteSuffix R Q hne)
      (by simp [cleanReroutePrefix, cleanRerouteMiddle])
      (by simp [cleanRerouteMiddle, cleanRerouteSuffix])

theorem cleanRerouteThrough_vertexSet_subset
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) :
    (cleanRerouteThrough R Q hne).vertexSet ⊆
      Q.vertexSet ∪ R.vertexSet := by
  classical
  intro x hx
  have hparts :
      x ∈ (cleanReroutePrefix R Q hne).vertexSet ∪
          (cleanRerouteMiddle R Q hne).vertexSet ∪
            (cleanRerouteSuffix R Q hne).vertexSet := by
    simpa [cleanRerouteThrough] using
      (cleanReroutePrefix R Q hne).append3WithEqToPath_vertexSet_subset
        (cleanRerouteMiddle R Q hne)
        (cleanRerouteSuffix R Q hne)
        (by simp [cleanReroutePrefix, cleanRerouteMiddle])
        (by simp [cleanRerouteMiddle, cleanRerouteSuffix]) hx
  rcases Finset.mem_union.1 hparts with hprefixMiddle | hsuffix
  · rcases Finset.mem_union.1 hprefixMiddle with hprefix | hmiddle
    · exact Finset.mem_union.2 <| Or.inl
        ((Q.cleanPrefixToSet_vertexSet_subset R.vertexSet hne)
          (by simpa [cleanReroutePrefix] using hprefix))
    · exact Finset.mem_union.2 <| Or.inr
        (segmentBetween_vertexSet_subset R
          (Q.firstHitVertex_mem_set R.vertexSet hne)
          (Q.lastHitVertex_mem_set R.vertexSet hne)
          (by simpa [cleanRerouteMiddle] using hmiddle))
  · exact Finset.mem_union.2 <| Or.inl
      ((Q.cleanSuffixFromSet_vertexSet_subset R.vertexSet hne)
        (by simpa [cleanRerouteSuffix] using hsuffix))

/-- The paper's local blue connector: keep `Q` when it is disjoint from the
red connector `R`; otherwise reroute `Q` through `R` between the first and last
intersections. -/
noncomputable def cleanOrDisjointReroute
    {G : _root_.SimpleGraph V} (R Q : GraphPath G) : GraphPath G :=
  if hne : (Q.vertexSet ∩ R.vertexSet).Nonempty then
    cleanRerouteThrough R Q hne
  else
    Q

@[simp] theorem cleanOrDisjointReroute_source
    {G : _root_.SimpleGraph V} (R Q : GraphPath G) :
    (cleanOrDisjointReroute R Q).source = Q.source := by
  classical
  by_cases hne : (Q.vertexSet ∩ R.vertexSet).Nonempty
  · simp [cleanOrDisjointReroute, hne]
  · simp [cleanOrDisjointReroute, hne]

@[simp] theorem cleanOrDisjointReroute_target
    {G : _root_.SimpleGraph V} (R Q : GraphPath G) :
    (cleanOrDisjointReroute R Q).target = Q.target := by
  classical
  by_cases hne : (Q.vertexSet ∩ R.vertexSet).Nonempty
  · simp [cleanOrDisjointReroute, hne]
  · simp [cleanOrDisjointReroute, hne]

theorem cleanOrDisjointReroute_vertexSet_subset
    {G : _root_.SimpleGraph V} (R Q : GraphPath G) :
    (cleanOrDisjointReroute R Q).vertexSet ⊆ Q.vertexSet ∪ R.vertexSet := by
  classical
  by_cases hne : (Q.vertexSet ∩ R.vertexSet).Nonempty
  · intro x hx
    exact cleanRerouteThrough_vertexSet_subset R Q hne
      (by simpa [cleanOrDisjointReroute, hne] using hx)
  · intro x hx
    exact Finset.mem_union.2 <| Or.inl (by
      simpa [cleanOrDisjointReroute, hne] using hx)

/-- Away from the first and last intersections, every edge of the rerouted
path incident with the red path is itself a red-path edge. -/
theorem cleanRerouteThrough_incident_subset_red_except
    {G : _root_.SimpleGraph V} (R Q : GraphPath G)
    (hne : (Q.vertexSet ∩ R.vertexSet).Nonempty) :
    ∀ x : V, x ∈ R.vertexSet →
      x ≠ Q.firstHitVertex R.vertexSet hne →
        x ≠ Q.lastHitVertex R.vertexSet hne →
          ∀ y : V,
            s(x, y) ∈ (cleanRerouteThrough R Q hne).edgeSet →
              s(x, y) ∈ R.edgeSet := by
  classical
  intro x hxR hxFirst hxLast y he
  have hparts :=
    cleanRerouteThrough_edgeSet_subset R Q hne he
  rcases Finset.mem_union.1 hparts with hPrefixMiddle | heSuffix
  · rcases Finset.mem_union.1 hPrefixMiddle with hePrefix | heMiddle
    · have hxPrefix :
        x ∈ (cleanReroutePrefix R Q hne).vertexSet :=
        (endpoints_mem_vertexSet_of_edgeSet
          (cleanReroutePrefix R Q hne) hePrefix).1
      have hxInter :
          x ∈ R.vertexSet ∩ (Q.cleanPrefixToSet R.vertexSet hne).vertexSet := by
        exact Finset.mem_inter.2
          ⟨hxR, by simpa [cleanReroutePrefix] using hxPrefix⟩
      have hxSingle :
          x ∈ ({(Q.cleanPrefixToSet R.vertexSet hne).target} : Finset V) := by
        simpa [Q.cleanPrefixToSet_inter_eq_singleton_target R.vertexSet hne]
          using hxInter
      have hxEq : x = Q.firstHitVertex R.vertexSet hne := by
        simpa using Finset.mem_singleton.1 hxSingle
      exact False.elim (hxFirst hxEq)
    · exact
        (segmentBetween_edgeSet_subset R
          (Q.firstHitVertex_mem_set R.vertexSet hne)
          (Q.lastHitVertex_mem_set R.vertexSet hne)) (by
            simpa [cleanRerouteMiddle] using heMiddle)
  · have hxSuffix :
        x ∈ (cleanRerouteSuffix R Q hne).vertexSet :=
      (endpoints_mem_vertexSet_of_edgeSet
        (cleanRerouteSuffix R Q hne) heSuffix).1
    have hxInter :
        x ∈ R.vertexSet ∩
          (Q.cleanSuffixFromSet R.vertexSet hne).vertexSet := by
      exact Finset.mem_inter.2
        ⟨hxR, by simpa [cleanRerouteSuffix] using hxSuffix⟩
    have hxSingle :
        x ∈ ({(Q.cleanSuffixFromSet R.vertexSet hne).source} : Finset V) := by
      simpa [Q.cleanSuffixFromSet_inter_eq_singleton_source R.vertexSet hne]
        using hxInter
    have hxEq : x = Q.lastHitVertex R.vertexSet hne := by
      simpa using Finset.mem_singleton.1 hxSingle
    exact False.elim (hxLast hxEq)

/-- If the source of `Q` already lies in `U`, then it is the first hit of
`U` along `Q`. -/
theorem source_eq_firstHitVertex_of_source_mem_set
    {G : _root_.SimpleGraph V} (Q : GraphPath G) (U : Finset V)
    (hne : (Q.vertexSet ∩ U).Nonempty)
    (hsource : Q.source ∈ U) :
    Q.source = Q.firstHitVertex U hne := by
  have hfirst_source :
      Q.Before (Q.firstHitVertex U hne) Q.source :=
    Q.firstHitVertex_before_of_mem_set U hne
      (GraphPath.source_mem_vertexSet Q) hsource
  have hsource_first :
      Q.Before Q.source (Q.firstHitVertex U hne) :=
    Q.source_before_of_mem (Q.firstHitVertex_mem_vertexSet U hne)
  exact Q.before_antisymm hsource_first hfirst_source

/-- If the target of `Q` lies in `U`, then it is the last hit of `U` along
`Q`. -/
theorem target_eq_lastHitVertex_of_target_mem_set
    {G : _root_.SimpleGraph V} (Q : GraphPath G) (U : Finset V)
    (hne : (Q.vertexSet ∩ U).Nonempty)
    (htarget : Q.target ∈ U) :
    Q.target = Q.lastHitVertex U hne := by
  have htarget_last :
      Q.Before Q.target (Q.lastHitVertex U hne) :=
    Q.before_lastHitVertex_of_mem_set U hne
      (GraphPath.target_mem_vertexSet Q) htarget
  have hlast_target :
      Q.Before (Q.lastHitVertex U hne) Q.target :=
    Q.before_target_of_mem (Q.lastHitVertex_mem_vertexSet U hne)
  exact Q.before_antisymm htarget_last hlast_target

end GraphPath

namespace MinorModel

variable {W : Type w} [DecidableEq W]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}

/-- A chosen host-side endpoint in the `u` branch set realizing a minor edge
`u -- v`. -/
noncomputable def edgeLeft
    (M : MinorModel H G) {u v : W} (huv : H.Adj u v) : V :=
  Classical.choose (M.adjacent huv)

/-- A chosen host-side endpoint in the `v` branch set realizing a minor edge
`u -- v`. -/
noncomputable def edgeRight
    (M : MinorModel H G) {u v : W} (huv : H.Adj u v) : V :=
  Classical.choose (Classical.choose_spec (M.adjacent huv)).2

theorem edgeLeft_mem_branchSet
    (M : MinorModel H G) {u v : W} (huv : H.Adj u v) :
    edgeLeft M huv ∈ M.branchSet u := by
  classical
  simpa [edgeLeft] using (Classical.choose_spec (M.adjacent huv)).1

theorem edgeRight_mem_branchSet
    (M : MinorModel H G) {u v : W} (huv : H.Adj u v) :
    edgeRight M huv ∈ M.branchSet v := by
  classical
  simpa [edgeRight] using
    (Classical.choose_spec (Classical.choose_spec (M.adjacent huv)).2).1

theorem eq_left_of_edgeLeft_mem_branchSet
    (M : MinorModel H G) {u v w : W} (huv : H.Adj u v)
    (hw : edgeLeft M huv ∈ M.branchSet w) :
    w = u := by
  classical
  by_contra hwu
  exact Finset.disjoint_left.mp (M.branch_disjoint hwu)
    hw (edgeLeft_mem_branchSet M huv)

theorem eq_right_of_edgeRight_mem_branchSet
    (M : MinorModel H G) {u v w : W} (huv : H.Adj u v)
    (hw : edgeRight M huv ∈ M.branchSet w) :
    w = v := by
  classical
  by_contra hwv
  exact Finset.disjoint_left.mp (M.branch_disjoint hwv)
    hw (edgeRight_mem_branchSet M huv)

theorem branch_eq_left_or_right_of_mem_crossing_edge
    (M : MinorModel H G) {u v w : W} (huv : H.Adj u v) {x : V}
    (hxw : x ∈ M.branchSet w)
    (hx :
      x ∈ s(edgeLeft M huv, edgeRight M huv)) :
    w = u ∨ w = v := by
  classical
  rcases (Sym2.mem_iff.mp hx) with hxLeft | hxRight
  · exact Or.inl
      (eq_left_of_edgeLeft_mem_branchSet M huv (by simpa [hxLeft] using hxw))
  · exact Or.inr
      (eq_right_of_edgeRight_mem_branchSet M huv (by simpa [hxRight] using hxw))

theorem edgeLeft_adj_edgeRight
    (M : MinorModel H G) {u v : W} (huv : H.Adj u v) :
    G.Adj (edgeLeft M huv) (edgeRight M huv) := by
  classical
  exact (Classical.choose_spec (Classical.choose_spec (M.adjacent huv)).2).2

/-- A chosen simple connector inside one branch set. -/
noncomputable def branchConnector
    (M : MinorModel H G) (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w) : GraphPath G :=
  GraphPath.ofConnectedInduce
    (M.branchSet w) (M.branch_connected w) s t hs ht

@[simp] theorem branchConnector_source
    (M : MinorModel H G) (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w) :
    (branchConnector M w hs ht).source = s := rfl

@[simp] theorem branchConnector_target
    (M : MinorModel H G) (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w) :
    (branchConnector M w hs ht).target = t := rfl

theorem branchConnector_vertexSet_subset_branchSet
    (M : MinorModel H G) (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w) :
    (branchConnector M w hs ht).vertexSet ⊆ M.branchSet w := by
  exact GraphPath.ofConnectedInduce_vertexSet_subset
    (M.branchSet w) (M.branch_connected w) s t hs ht

/-- A fixed host vertex in a minor branch set, used as a fallback when a local
routing does not use that branch set. -/
noncomputable def branchPoint (M : MinorModel H G) (w : W) : V :=
  Classical.choose (M.branch_nonempty w)

theorem branchPoint_mem_branchSet
    (M : MinorModel H G) (w : W) :
    branchPoint M w ∈ M.branchSet w :=
  Classical.choose_spec (M.branch_nonempty w)

/-- The length-zero fallback connector inside a branch set. -/
noncomputable def trivialBranchConnector
    (M : MinorModel H G) (w : W) : GraphPath G :=
  GraphPath.refl G (branchPoint M w)

theorem trivialBranchConnector_vertexSet_subset_branchSet
    (M : MinorModel H G) (w : W) :
    (trivialBranchConnector M w).vertexSet ⊆ M.branchSet w := by
  intro x hx
  have hx' : x = branchPoint M w := by
    simpa [trivialBranchConnector] using hx
  simpa [hx'] using branchPoint_mem_branchSet M w

/-- A structured expansion of a minor walk.  It follows the minor walk edge by
edge, connects the two incident minor-edge endpoints inside the current branch
set, crosses the chosen host edge realizing the minor edge, and recurses. -/
noncomputable def liftWalkStructured
    (M : MinorModel H G) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      s ∈ M.branchSet a → t ∈ M.branchSet b → G.Walk s t
  | a, _, _root_.SimpleGraph.Walk.nil' _, s, t, hs, ht =>
      (branchConnector M a hs ht).walk
  | a, c, _root_.SimpleGraph.Walk.cons' _ b _ hab P, s, t, hs, ht =>
      let L :=
        branchConnector M a hs (edgeLeft_mem_branchSet M hab)
      let R :=
        liftWalkStructured M P
          (edgeRight_mem_branchSet M hab) ht
      L.walk.append
        (_root_.SimpleGraph.Walk.cons
          (edgeLeft_adj_edgeRight M hab) R)

@[simp] theorem liftWalkStructured_nil
    (M : MinorModel H G) (a : W) {s t : V}
    (hs : s ∈ M.branchSet a) (ht : t ∈ M.branchSet a) :
    liftWalkStructured M (_root_.SimpleGraph.Walk.nil : H.Walk a a) hs ht =
      (branchConnector M a hs ht).walk := rfl

theorem liftWalkStructured_support_subset_walkBranchUnion
    (M : MinorModel H G) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      (hs : s ∈ M.branchSet a) → (ht : t ∈ M.branchSet b) →
        (liftWalkStructured M P hs ht).support.toFinset ⊆
          M.walkBranchUnion P
  | a, _, _root_.SimpleGraph.Walk.nil' _, s, t, hs, ht => by
      intro x hx
      have hxPath :
          x ∈ (branchConnector M a hs ht).vertexSet := by
        simpa [GraphPath.vertexSet] using hx
      have hxBranch :
          x ∈ M.branchSet a :=
        branchConnector_vertexSet_subset_branchSet M a hs ht hxPath
      simpa [MinorModel.walkBranchUnion] using hxBranch
  | a, c, _root_.SimpleGraph.Walk.cons' _ b _ hab P, s, t, hs, ht => by
      classical
      intro x hx
      let L :=
        branchConnector M a hs (edgeLeft_mem_branchSet M hab)
      let R :=
        liftWalkStructured M P
          (edgeRight_mem_branchSet M hab) ht
      have hxSupport :
          x ∈ (L.walk.append
            (_root_.SimpleGraph.Walk.cons
              (edgeLeft_adj_edgeRight M hab) R)).support.toFinset := by
        simpa [liftWalkStructured, L, R] using hx
      have hxSupportList :
          x ∈ (L.walk.append
            (_root_.SimpleGraph.Walk.cons
              (edgeLeft_adj_edgeRight M hab) R)).support := by
        simpa using hxSupport
      have hxSplit :
          x ∈ L.walk.support ∨
            x ∈ (_root_.SimpleGraph.Walk.cons
              (edgeLeft_adj_edgeRight M hab) R).support := by
        simpa [_root_.SimpleGraph.Walk.mem_support_append_iff] using hxSupportList
      rcases hxSplit with hxL | hxCons
      · have hxPath : x ∈ L.vertexSet := by
          simpa [GraphPath.vertexSet] using hxL
        have hxBranch :
            x ∈ M.branchSet a :=
          branchConnector_vertexSet_subset_branchSet M a
            hs (edgeLeft_mem_branchSet M hab) hxPath
        exact M.mem_walkBranchUnion_of_mem_branch (by simp) hxBranch
      · have hxCons' :
            x = edgeLeft M hab ∨
              x ∈ R.support := by
          simpa [_root_.SimpleGraph.Walk.support_cons] using hxCons
        rcases hxCons' with rfl | hxR
        · exact M.mem_walkBranchUnion_of_mem_branch
            (by simp) (edgeLeft_mem_branchSet M hab)
        · have hxTail :
              x ∈ M.walkBranchUnion P :=
            liftWalkStructured_support_subset_walkBranchUnion M P
              (edgeRight_mem_branchSet M hab) ht (by simpa using hxR)
          rw [MinorModel.walkBranchUnion] at hxTail ⊢
          rcases Finset.mem_biUnion.1 hxTail with ⟨z, hz, hxz⟩
          exact Finset.mem_biUnion.2 ⟨z, by simp [hz], hxz⟩

/-- Structured lift of a graph path in a minor to a host-graph path. -/
noncomputable def structuredLiftGraphPath
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) : GraphPath G :=
  GraphPath.ofWalk (liftWalkStructured M P.walk hs ht)

@[simp] theorem structuredLiftGraphPath_source
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (structuredLiftGraphPath M P hs ht).source = s := rfl

@[simp] theorem structuredLiftGraphPath_target
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (structuredLiftGraphPath M P hs ht).target = t := rfl

theorem structuredLiftGraphPath_vertexSet_subset_walkBranchUnion
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (structuredLiftGraphPath M P hs ht).vertexSet ⊆
      M.walkBranchUnion P.walk := by
  intro x hx
  have hxWalk :
      x ∈ (liftWalkStructured M P.walk hs ht).support.toFinset :=
    GraphPath.ofWalk_vertexSet_subset
      (liftWalkStructured M P.walk hs ht) hx
  exact liftWalkStructured_support_subset_walkBranchUnion
    M P.walk hs ht hxWalk

/-- A family of local branch-set connectors with their endpoint and containment
certificates.  Bundling the endpoint equalities keeps the generic walk lift
usable for rerouted connectors, whose endpoints are no longer definitional. -/
structure BranchConnectorChoice (M : MinorModel H G) where
  path : ∀ (w : W) {s t : V},
    s ∈ M.branchSet w → t ∈ M.branchSet w → GraphPath G
  source_eq : ∀ (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w),
      (path w hs ht).source = s
  target_eq : ∀ (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w),
      (path w hs ht).target = t
  vertexSet_subset : ∀ (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w),
      (path w hs ht).vertexSet ⊆ M.branchSet w

namespace BranchConnectorChoice

/-- The default local connector: any path inside the connected branch set. -/
noncomputable def default (M : MinorModel H G) : BranchConnectorChoice M where
  path := fun w {s} {t} hs ht => branchConnector M w (s := s) (t := t) hs ht
  source_eq := by
    intro w s t hs ht
    rfl
  target_eq := by
    intro w s t hs ht
    rfl
  vertexSet_subset := by
    intro w s t hs ht
    exact branchConnector_vertexSet_subset_branchSet M w hs ht

/-- Prefer a prescribed path in branch set `w` whenever its endpoints are exactly
the requested connector endpoints; otherwise fall back to the ordinary connected
branch-set connector. -/
noncomputable def prefer
    (M : MinorModel H G)
    (R : W → GraphPath G)
    (hR : ∀ w : W, (R w).vertexSet ⊆ M.branchSet w) :
    BranchConnectorChoice M where
  path := fun w {s} {t} hs ht =>
    if h : (R w).source = s ∧ (R w).target = t then
      { source := s
        target := t
        walk := (R w).walk.copy h.1 h.2
        isPath :=
          (_root_.SimpleGraph.Walk.isPath_copy (R w).walk h.1 h.2).2
            (R w).isPath }
    else
      branchConnector M w (s := s) (t := t) hs ht
  source_eq := by
    intro w s t hs ht
    by_cases h : (R w).source = s ∧ (R w).target = t
    · simp [h]
    · simp [h]
  target_eq := by
    intro w s t hs ht
    by_cases h : (R w).source = s ∧ (R w).target = t
    · simp [h]
    · simp [h]
  vertexSet_subset := by
    intro w s t hs ht x hx
    by_cases h : (R w).source = s ∧ (R w).target = t
    · have hxR : x ∈ (R w).vertexSet := by
        have hxCopy :
            x ∈
              ({ source := s
                 target := t
                 walk := (R w).walk.copy h.1 h.2
                 isPath :=
                  (_root_.SimpleGraph.Walk.isPath_copy (R w).walk h.1 h.2).2
                    (R w).isPath } : GraphPath G).vertexSet := by
          simpa [h] using hx
        simpa [GraphPath.vertexSet] using hxCopy
      exact hR w hxR
    · exact branchConnector_vertexSet_subset_branchSet M w hs ht
        (by simpa [h] using hx)

/-- Reroute each local branch-set connector through a prescribed local red path
inside that branch set.  If the preliminary connector is disjoint from the red
path, it is left unchanged; otherwise it is rerouted between first and last
intersection. -/
noncomputable def rerouteThrough
    (M : MinorModel H G)
    (R : W → GraphPath G)
    (hR : ∀ w : W, (R w).vertexSet ⊆ M.branchSet w) :
    BranchConnectorChoice M where
  path := fun w {s} {t} hs ht =>
    GraphPath.cleanOrDisjointReroute
      (R w) (branchConnector M w (s := s) (t := t) hs ht)
  source_eq := by
    intro w s t hs ht
    simp
  target_eq := by
    intro w s t hs ht
    simp
  vertexSet_subset := by
    intro w s t hs ht x hx
    have hxUnion :
        x ∈ (branchConnector M w (s := s) (t := t) hs ht).vertexSet ∪
          (R w).vertexSet :=
      GraphPath.cleanOrDisjointReroute_vertexSet_subset
        (R w) (branchConnector M w (s := s) (t := t) hs ht) hx
    rcases Finset.mem_union.1 hxUnion with hxQ | hxR
    · exact branchConnector_vertexSet_subset_branchSet M w hs ht hxQ
    · exact hR w hxR

/-- Prefer a prescribed already-rerouted connector whenever its endpoints match
the requested branch-set connector endpoints; otherwise perform the generic
reroute-through construction from the ordinary branch connector. -/
noncomputable def preferRerouteThrough
    (M : MinorModel H G)
    (R B : W → GraphPath G)
    (hR : ∀ w : W, (R w).vertexSet ⊆ M.branchSet w)
    (hB : ∀ w : W, (B w).vertexSet ⊆ M.branchSet w) :
    BranchConnectorChoice M where
  path := fun w {s} {t} hs ht =>
    let Q := GraphPath.cleanOrDisjointReroute (R w) (B w)
    if h : (B w).source = s ∧ (B w).target = t then
      { source := s
        target := t
        walk := Q.walk.copy (by simpa [Q] using h.1) (by simpa [Q] using h.2)
        isPath :=
          (_root_.SimpleGraph.Walk.isPath_copy Q.walk
              (by simpa [Q] using h.1) (by simpa [Q] using h.2)).2
            Q.isPath }
    else
      GraphPath.cleanOrDisjointReroute
        (R w) (branchConnector M w (s := s) (t := t) hs ht)
  source_eq := by
    intro w s t hs ht
    by_cases h : (B w).source = s ∧ (B w).target = t
    · simp [h]
    · simp [h]
  target_eq := by
    intro w s t hs ht
    by_cases h : (B w).source = s ∧ (B w).target = t
    · simp [h]
    · simp [h]
  vertexSet_subset := by
    intro w s t hs ht x hx
    let Q := GraphPath.cleanOrDisjointReroute (R w) (B w)
    by_cases h : (B w).source = s ∧ (B w).target = t
    · have hxQ : x ∈ Q.vertexSet := by
        have hxCopy :
            x ∈
              ({ source := s
                 target := t
                 walk := Q.walk.copy (by simpa [Q] using h.1) (by simpa [Q] using h.2)
                 isPath :=
                  (_root_.SimpleGraph.Walk.isPath_copy Q.walk
                      (by simpa [Q] using h.1) (by simpa [Q] using h.2)).2
                    Q.isPath } : GraphPath G).vertexSet := by
          simpa [Q, h] using hx
        simpa [GraphPath.vertexSet] using hxCopy
      have hxUnion : x ∈ (B w).vertexSet ∪ (R w).vertexSet :=
        GraphPath.cleanOrDisjointReroute_vertexSet_subset
          (R w) (B w) hxQ
      rcases Finset.mem_union.1 hxUnion with hxB | hxR
      · exact hB w hxB
      · exact hR w hxR
    · have hxFallback :
          x ∈ (GraphPath.cleanOrDisjointReroute
            (R w) (branchConnector M w (s := s) (t := t) hs ht)).vertexSet := by
        simpa [Q, h] using hx
      have hxUnion :
          x ∈ (branchConnector M w (s := s) (t := t) hs ht).vertexSet ∪
            (R w).vertexSet :=
        GraphPath.cleanOrDisjointReroute_vertexSet_subset
          (R w) (branchConnector M w (s := s) (t := t) hs ht) hxFallback
      rcases Finset.mem_union.1 hxUnion with hxBranch | hxR
      · exact branchConnector_vertexSet_subset_branchSet M w hs ht hxBranch
      · exact hR w hxR

/-- If the prescribed connector has exactly the requested endpoints, `prefer`
uses that connector and hence has the same edge set. -/
theorem prefer_path_edgeSet_eq
    (M : MinorModel H G)
    (R : W → GraphPath G)
    (hR : ∀ w : W, (R w).vertexSet ⊆ M.branchSet w)
    (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w)
    (hsource : (R w).source = s) (htarget : (R w).target = t) :
    ((prefer M R hR).path w hs ht).edgeSet = (R w).edgeSet := by
  classical
  have h : (R w).source = s ∧ (R w).target = t := ⟨hsource, htarget⟩
  dsimp [prefer]
  rw [dif_pos h]
  simp [GraphPath.edgeSet]

/-- If the preliminary blue connector has exactly the requested endpoints,
`preferRerouteThrough` uses the already cleaned/rerouted blue connector. -/
theorem preferRerouteThrough_path_edgeSet_eq
    (M : MinorModel H G)
    (R B : W → GraphPath G)
    (hR : ∀ w : W, (R w).vertexSet ⊆ M.branchSet w)
    (hB : ∀ w : W, (B w).vertexSet ⊆ M.branchSet w)
    (w : W) {s t : V}
    (hs : s ∈ M.branchSet w) (ht : t ∈ M.branchSet w)
    (hsource : (B w).source = s) (htarget : (B w).target = t) :
    ((preferRerouteThrough M R B hR hB).path w hs ht).edgeSet =
      (GraphPath.cleanOrDisjointReroute (R w) (B w)).edgeSet := by
  classical
  have h : (B w).source = s ∧ (B w).target = t := ⟨hsource, htarget⟩
  dsimp [preferRerouteThrough]
  rw [dif_pos h]
  simp [GraphPath.edgeSet]

end BranchConnectorChoice

/-- A branch-by-branch walk lift using a caller-supplied local connector inside
each branch set.  This is the common engine for the red expansion and for the
blue expansion after the paper's local rerouting step. -/
noncomputable def liftWalkWithBranchConnectors
    (M : MinorModel H G) (C : BranchConnectorChoice M) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      s ∈ M.branchSet a → t ∈ M.branchSet b → G.Walk s t
  | a, _, _root_.SimpleGraph.Walk.nil' _, s, t, hs, ht =>
      (C.path a hs ht).walk.copy
        (C.source_eq a hs ht) (C.target_eq a hs ht)
  | a, c, _root_.SimpleGraph.Walk.cons' _ b _ hab P, s, t, hs, ht =>
      let L := C.path a hs (edgeLeft_mem_branchSet M hab)
      let Lwalk :=
        L.walk.copy
          (C.source_eq a hs (edgeLeft_mem_branchSet M hab))
          (C.target_eq a hs (edgeLeft_mem_branchSet M hab))
      let R :=
        liftWalkWithBranchConnectors M C P
          (edgeRight_mem_branchSet M hab) ht
      Lwalk.append
        (_root_.SimpleGraph.Walk.cons
          (edgeLeft_adj_edgeRight M hab) R)

/-- The local connector instances actually used by
`liftWalkWithBranchConnectors`.  The indices remember the two host endpoints
requested from the connector choice at the corresponding minor vertex. -/
inductive LiftWalkLocalUse (M : MinorModel H G) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      s ∈ M.branchSet a → t ∈ M.branchSet b →
        W → V → V → Prop
  | nil {a : W} {s t : V}
      (hs : s ∈ M.branchSet a) (ht : t ∈ M.branchSet a) :
      LiftWalkLocalUse M (_root_.SimpleGraph.Walk.nil : H.Walk a a)
        hs ht a s t
  | cons_head {a b c : W} {hab : H.Adj a b} {P : H.Walk b c}
      {s t : V} (hs : s ∈ M.branchSet a) (ht : t ∈ M.branchSet c) :
      LiftWalkLocalUse M (_root_.SimpleGraph.Walk.cons hab P)
        hs ht a s (edgeLeft M hab)
  | cons_tail {a b c : W} {hab : H.Adj a b} {P : H.Walk b c}
      {s t : V} {hs : s ∈ M.branchSet a} {ht : t ∈ M.branchSet c}
      {z : W} {p q : V}
      (h :
        LiftWalkLocalUse M P (edgeRight_mem_branchSet M hab) ht z p q) :
      LiftWalkLocalUse M (_root_.SimpleGraph.Walk.cons hab P)
        hs ht z p q

/-- The directed minor edges whose chosen host representatives are crossed by
`liftWalkWithBranchConnectors`. -/
inductive LiftWalkCrossingUse (M : MinorModel H G) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      s ∈ M.branchSet a → t ∈ M.branchSet b →
        ∀ u v : W, H.Adj u v → Prop
  | cons_head {a b c : W} {hab : H.Adj a b} {P : H.Walk b c}
      {s t : V} (hs : s ∈ M.branchSet a) (ht : t ∈ M.branchSet c) :
      LiftWalkCrossingUse M (_root_.SimpleGraph.Walk.cons hab P)
        hs ht a b hab
  | cons_tail {a b c u v : W} {hab : H.Adj a b} {huv : H.Adj u v}
      {P : H.Walk b c} {s t : V}
      {hs : s ∈ M.branchSet a} {ht : t ∈ M.branchSet c}
      (h :
        LiftWalkCrossingUse M P (edgeRight_mem_branchSet M hab) ht u v huv) :
      LiftWalkCrossingUse M (_root_.SimpleGraph.Walk.cons hab P)
        hs ht u v huv

/-- Every minor vertex visited by a walk lift has a corresponding local
connector occurrence in `liftWalkWithBranchConnectors`. -/
theorem liftWalkLocalUse_exists_of_mem_support
    (M : MinorModel H G) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      (hs : s ∈ M.branchSet a) → (ht : t ∈ M.branchSet b) →
        ∀ {w : W}, w ∈ P.support.toFinset →
          ∃ (p q : V) (hp : p ∈ M.branchSet w)
            (hq : q ∈ M.branchSet w),
              LiftWalkLocalUse M P hs ht w p q
  | a, _, _root_.SimpleGraph.Walk.nil' _, s, t, hs, ht, w, hw => by
      have hwa : w = a := by simpa using hw
      subst w
      exact ⟨s, t, hs, ht, LiftWalkLocalUse.nil hs ht⟩
  | a, c, _root_.SimpleGraph.Walk.cons' _ b _ hab P,
      s, t, hs, ht, w, hw => by
      classical
      have hwCases : w = a ∨ w ∈ P.support.toFinset := by
        simpa [_root_.SimpleGraph.Walk.support_cons] using hw
      rcases hwCases with rfl | hwTail
      · exact
          ⟨s, edgeLeft M hab, hs, edgeLeft_mem_branchSet M hab,
            LiftWalkLocalUse.cons_head hs ht⟩
      · rcases
          liftWalkLocalUse_exists_of_mem_support M P
            (edgeRight_mem_branchSet M hab) ht hwTail with
          ⟨p, q, hp, hq, huse⟩
        exact ⟨p, q, hp, hq, LiftWalkLocalUse.cons_tail huse⟩

theorem liftWalkWithBranchConnectors_edge_localUse_or_crossingUse
    (M : MinorModel H G) (C : BranchConnectorChoice M) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      (hs : s ∈ M.branchSet a) → (ht : t ∈ M.branchSet b) →
        ∀ {e : Sym2 V},
          e ∈ (liftWalkWithBranchConnectors M C P hs ht).edges.toFinset →
            (∃ (z : W) (p q : V) (hp : p ∈ M.branchSet z)
                (hq : q ∈ M.branchSet z),
                LiftWalkLocalUse M P hs ht z p q ∧
                  e ∈ (C.path z hp hq).edgeSet) ∨
            (∃ (u v : W) (huv : H.Adj u v),
                LiftWalkCrossingUse M P hs ht u v huv ∧
                  e = s(edgeLeft M huv, edgeRight M huv))
  | a, _, _root_.SimpleGraph.Walk.nil' _, s, t, hs, ht, e, he => by
      left
      refine ⟨a, s, t, hs, ht, ?_, ?_⟩
      · exact LiftWalkLocalUse.nil hs ht
      · simpa [GraphPath.edgeSet, liftWalkWithBranchConnectors,
          _root_.SimpleGraph.Walk.edges_copy] using he
  | a, c, _root_.SimpleGraph.Walk.cons' _ b _ hab P, s, t, hs, ht, e, he => by
      classical
      let L := C.path a hs (edgeLeft_mem_branchSet M hab)
      let Lwalk :=
        L.walk.copy
          (C.source_eq a hs (edgeLeft_mem_branchSet M hab))
          (C.target_eq a hs (edgeLeft_mem_branchSet M hab))
      let R :=
        liftWalkWithBranchConnectors M C P
          (edgeRight_mem_branchSet M hab) ht
      have heList0 :
          e ∈
            (liftWalkWithBranchConnectors M C
              (_root_.SimpleGraph.Walk.cons hab P) hs ht).edges := by
        exact List.mem_toFinset.mp he
      have heList :
          e ∈ (Lwalk.append
            (_root_.SimpleGraph.Walk.cons
              (edgeLeft_adj_edgeRight M hab) R)).edges := by
        simpa [liftWalkWithBranchConnectors, L, Lwalk, R] using heList0
      have heCases :
          e ∈ Lwalk.edges ∨
            e = s(edgeLeft M hab, edgeRight M hab) ∨ e ∈ R.edges := by
        simpa [_root_.SimpleGraph.Walk.edges_append,
          _root_.SimpleGraph.Walk.edges_cons] using heList
      rcases heCases with heL | heRest
      · left
        refine ⟨a, s, edgeLeft M hab, hs,
          edgeLeft_mem_branchSet M hab, ?_, ?_⟩
        · exact LiftWalkLocalUse.cons_head hs ht
        · simpa [GraphPath.edgeSet, L, Lwalk,
            _root_.SimpleGraph.Walk.edges_copy] using heL
      rcases heRest with rfl | heR
      · right
        refine ⟨a, b, hab, ?_, rfl⟩
        exact LiftWalkCrossingUse.cons_head hs ht
      · have heRfin :
            e ∈ R.edges.toFinset := by
          simpa using heR
        have htail :=
          liftWalkWithBranchConnectors_edge_localUse_or_crossingUse
            M C P (edgeRight_mem_branchSet M hab) ht heRfin
        rcases htail with hlocal | hcross
        · left
          rcases hlocal with ⟨z, p, q, hp, hq, huse, hez⟩
          refine ⟨z, p, q, hp, hq, ?_, hez⟩
          exact LiftWalkLocalUse.cons_tail huse
        · right
          rcases hcross with ⟨u, v, huv, huse, heq⟩
          refine ⟨u, v, huv, ?_, heq⟩
          exact LiftWalkCrossingUse.cons_tail huse

/-- Converse to the local-use half of
`liftWalkWithBranchConnectors_edge_localUse_or_crossingUse`: every edge of a
connector occurrence selected by the lifted walk is indeed an edge of the
lifted walk. -/
theorem liftWalkWithBranchConnectors_localUse_edge_mem
    (M : MinorModel H G) (C : BranchConnectorChoice M) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      (hs : s ∈ M.branchSet a) → (ht : t ∈ M.branchSet b) →
        ∀ {z : W} {p q : V}
          {hp : p ∈ M.branchSet z} {hq : q ∈ M.branchSet z},
          LiftWalkLocalUse M P hs ht z p q →
            ∀ {e : Sym2 V},
              e ∈ (C.path z hp hq).edgeSet →
                e ∈ (liftWalkWithBranchConnectors M C P hs ht).edges.toFinset
  | a, _, _root_.SimpleGraph.Walk.nil' _, s, t, hs, ht,
      z, p, q, hp, hq, huse, e, he => by
      cases huse
      simpa [liftWalkWithBranchConnectors, GraphPath.edgeSet,
        _root_.SimpleGraph.Walk.edges_copy] using he
  | a, c, _root_.SimpleGraph.Walk.cons' _ b _ hab P, s, t, hs, ht,
      z, p, q, hp, hq, huse, e, he => by
      classical
      let L := C.path a hs (edgeLeft_mem_branchSet M hab)
      let Lwalk :=
        L.walk.copy
          (C.source_eq a hs (edgeLeft_mem_branchSet M hab))
          (C.target_eq a hs (edgeLeft_mem_branchSet M hab))
      let R :=
        liftWalkWithBranchConnectors M C P
          (edgeRight_mem_branchSet M hab) ht
      cases huse with
      | cons_head =>
          have heList : e ∈ Lwalk.edges := by
            simpa [L, Lwalk, GraphPath.edgeSet,
              _root_.SimpleGraph.Walk.edges_copy] using he
          have heLift :
              e ∈
                (Lwalk.append
                  (_root_.SimpleGraph.Walk.cons
                    (edgeLeft_adj_edgeRight M hab) R)).edges := by
            simpa [_root_.SimpleGraph.Walk.edges_append] using Or.inl heList
          exact List.mem_toFinset.mpr (by
            simpa [liftWalkWithBranchConnectors, L, Lwalk, R] using heLift)
      | cons_tail htail =>
          have heTail :
              e ∈ R.edges.toFinset :=
            liftWalkWithBranchConnectors_localUse_edge_mem
              M C P (edgeRight_mem_branchSet M hab) ht htail he
          have heTailList : e ∈ R.edges := List.mem_toFinset.mp heTail
          have heLift :
              e ∈
                (Lwalk.append
                  (_root_.SimpleGraph.Walk.cons
                    (edgeLeft_adj_edgeRight M hab) R)).edges := by
            simp [_root_.SimpleGraph.Walk.edges_append,
              _root_.SimpleGraph.Walk.edges_cons, heTailList]
          exact List.mem_toFinset.mpr (by
            simpa [liftWalkWithBranchConnectors, L, Lwalk, R] using heLift)

theorem liftWalkLocalUse_left_endpoint_or_crossing
    (M : MinorModel H G)
    {a b : W} {P : H.Walk a b} {s t : V}
    {hs : s ∈ M.branchSet a} {ht : t ∈ M.branchSet b}
    {w : W} {p q : V}
    (huse : LiftWalkLocalUse M P hs ht w p q) :
    (w = a ∧ p = s) ∨
      ∃ (prev : W) (hprev : H.Adj prev w),
        LiftWalkCrossingUse M P hs ht prev w hprev ∧
          p = edgeRight M hprev := by
  induction huse with
  | nil hs ht =>
      left
      simp
  | cons_head hs ht =>
      left
      simp
  | cons_tail htail ih =>
      rcases ih with hstart | hcross
      · rcases hstart with ⟨rfl, rfl⟩
        right
        exact ⟨_, _, LiftWalkCrossingUse.cons_head _ _, rfl⟩
      · rcases hcross with ⟨prev, hprev, hcrossUse, hp⟩
        right
        exact ⟨prev, hprev, LiftWalkCrossingUse.cons_tail hcrossUse, hp⟩

theorem liftWalkLocalUse_right_endpoint_or_crossing
    (M : MinorModel H G)
    {a b : W} {P : H.Walk a b} {s t : V}
    {hs : s ∈ M.branchSet a} {ht : t ∈ M.branchSet b}
    {w : W} {p q : V}
    (huse : LiftWalkLocalUse M P hs ht w p q) :
    (w = b ∧ q = t) ∨
      ∃ (next : W) (hnext : H.Adj w next),
        LiftWalkCrossingUse M P hs ht w next hnext ∧
          q = edgeLeft M hnext := by
  induction huse with
  | nil hs ht =>
      left
      simp
  | cons_head hs ht =>
      right
      exact ⟨_, _, LiftWalkCrossingUse.cons_head _ _, rfl⟩
  | cons_tail htail ih =>
      rcases ih with hend | hcross
      · rcases hend with ⟨rfl, rfl⟩
        left
        simp
      · rcases hcross with ⟨next, hnext, hcrossUse, hq⟩
        right
        exact ⟨next, hnext, LiftWalkCrossingUse.cons_tail hcrossUse, hq⟩

theorem liftWalkCrossingUse_support_index_le
    (M : MinorModel H G) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      (hs : s ∈ M.branchSet a) → (ht : t ∈ M.branchSet b) →
        ∀ {u v : W} {huv : H.Adj u v},
          P.IsPath →
          LiftWalkCrossingUse M P hs ht u v huv →
            u ∈ P.support.toFinset ∧
              v ∈ P.support.toFinset ∧
                P.support.idxOf u ≤ P.support.idxOf v
  | _, _, _root_.SimpleGraph.Walk.nil' _, _, _, _, _, _, _, _, _, huse => by
      cases huse
  | a, _, _root_.SimpleGraph.Walk.cons' _ b _ hab P,
      s, t, hs, ht, u, v, huv, hpath, huse => by
      cases huse with
      | cons_head =>
      constructor
      · simp [_root_.SimpleGraph.Walk.support_cons]
      constructor
      · simp [_root_.SimpleGraph.Walk.support_cons]
      · have hne : _ ≠ _ := hab.ne
        simp [_root_.SimpleGraph.Walk.support_cons, hne.symm]
      | cons_tail htail =>
      have htailPath :
          P.IsPath :=
        (_root_.SimpleGraph.Walk.cons_isPath_iff hab P).1 hpath |>.1
      have ha_not_tail :
          a ∉ P.support :=
        (_root_.SimpleGraph.Walk.cons_isPath_iff hab P).1 hpath |>.2
      have hrec :=
        liftWalkCrossingUse_support_index_le M P
          (edgeRight_mem_branchSet M hab) ht htailPath htail
      rcases hrec with ⟨huTail, hvTail, hidxTail⟩
      have huTailList : u ∈ P.support := by
        simpa using huTail
      have hvTailList : v ∈ P.support := by
        simpa using hvTail
      have hau : a ≠ u := by
        intro h
        exact ha_not_tail (by simpa [h] using huTailList)
      have hav : a ≠ v := by
        intro h
        exact ha_not_tail (by simpa [h] using hvTailList)
      constructor
      · simp [_root_.SimpleGraph.Walk.support_cons, huTailList]
      constructor
      · simp [_root_.SimpleGraph.Walk.support_cons, hvTailList]
      · simp [_root_.SimpleGraph.Walk.support_cons, hau, hav, hidxTail]

theorem liftWalkCrossingUse_mem_edges
    (M : MinorModel H G) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      (hs : s ∈ M.branchSet a) → (ht : t ∈ M.branchSet b) →
        ∀ {u v : W} {huv : H.Adj u v},
          LiftWalkCrossingUse M P hs ht u v huv →
            s(u, v) ∈ P.edges.toFinset
  | _, _, _root_.SimpleGraph.Walk.nil' _, _, _, _, _, _, _, _, huse => by
      cases huse
  | _, _, _root_.SimpleGraph.Walk.cons' _ _ _ hab P,
      _, _, _, ht, u, v, _, huse => by
      cases huse with
      | cons_head =>
      simp [_root_.SimpleGraph.Walk.edges_cons]
      | cons_tail htail =>
      have htailEdge : s(u, v) ∈ P.edges.toFinset :=
        liftWalkCrossingUse_mem_edges M P
          (edgeRight_mem_branchSet M hab) ht htail
      simp [_root_.SimpleGraph.Walk.edges_cons, htailEdge]

theorem liftWalkCrossingUse_edgeSet_before
    (M : MinorModel H G)
    (P : GraphPath H) {s t : V}
    (hs : s ∈ M.branchSet P.source) (ht : t ∈ M.branchSet P.target)
    {u v : W} {huv : H.Adj u v}
    (huse : LiftWalkCrossingUse M P.walk hs ht u v huv) :
    s(u, v) ∈ P.edgeSet ∧ P.Before u v ∧ u ≠ v := by
  classical
  have hidx :=
    liftWalkCrossingUse_support_index_le M P.walk hs ht P.isPath huse
  have hu : u ∈ P.vertexSet := by
    simpa [GraphPath.vertexSet] using hidx.1
  have hv : v ∈ P.vertexSet := by
    simpa [GraphPath.vertexSet] using hidx.2.1
  have hbefore : P.Before u v :=
    (P.before_iff_vertexIndex_le).2
      ⟨hu, hv, by simpa [GraphPath.vertexIndex] using hidx.2.2⟩
  have hedge : s(u, v) ∈ P.edgeSet := by
    simpa [GraphPath.edgeSet] using liftWalkCrossingUse_mem_edges M P.walk hs ht huse
  exact ⟨hedge, hbefore, huv.ne⟩

theorem liftWalkWithBranchConnectors_support_subset_walkBranchUnion
    (M : MinorModel H G) (C : BranchConnectorChoice M) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      (hs : s ∈ M.branchSet a) → (ht : t ∈ M.branchSet b) →
        (liftWalkWithBranchConnectors M C P hs ht).support.toFinset ⊆
          M.walkBranchUnion P
  | a, _, _root_.SimpleGraph.Walk.nil' _, s, t, hs, ht => by
      intro x hx
      have hxPath : x ∈ (C.path a hs ht).vertexSet := by
        simpa [GraphPath.vertexSet, liftWalkWithBranchConnectors] using hx
      have hxBranch : x ∈ M.branchSet a := C.vertexSet_subset a hs ht hxPath
      simpa [MinorModel.walkBranchUnion] using hxBranch
  | a, c, _root_.SimpleGraph.Walk.cons' _ b _ hab P, s, t, hs, ht => by
      classical
      intro x hx
      let L := C.path a hs (edgeLeft_mem_branchSet M hab)
      let Lwalk :=
        L.walk.copy
          (C.source_eq a hs (edgeLeft_mem_branchSet M hab))
          (C.target_eq a hs (edgeLeft_mem_branchSet M hab))
      let R :=
        liftWalkWithBranchConnectors M C P
          (edgeRight_mem_branchSet M hab) ht
      have hxSupport :
          x ∈ (Lwalk.append
            (_root_.SimpleGraph.Walk.cons
              (edgeLeft_adj_edgeRight M hab) R)).support.toFinset := by
        simpa [liftWalkWithBranchConnectors, L, Lwalk, R] using hx
      have hxSupportList :
          x ∈ (Lwalk.append
            (_root_.SimpleGraph.Walk.cons
              (edgeLeft_adj_edgeRight M hab) R)).support := by
        simpa using hxSupport
      have hxSplit :
          x ∈ Lwalk.support ∨
            x ∈ (_root_.SimpleGraph.Walk.cons
              (edgeLeft_adj_edgeRight M hab) R).support := by
        simpa [_root_.SimpleGraph.Walk.mem_support_append_iff] using hxSupportList
      rcases hxSplit with hxL | hxCons
      · have hxPath : x ∈ L.vertexSet := by
          simpa [GraphPath.vertexSet, Lwalk] using hxL
        have hxBranch : x ∈ M.branchSet a :=
          C.vertexSet_subset a hs (edgeLeft_mem_branchSet M hab) hxPath
        exact M.mem_walkBranchUnion_of_mem_branch (by simp) hxBranch
      · have hxCons' :
            x = edgeLeft M hab ∨ x ∈ R.support := by
          simpa [_root_.SimpleGraph.Walk.support_cons] using hxCons
        rcases hxCons' with rfl | hxR
        · exact M.mem_walkBranchUnion_of_mem_branch
            (by simp) (edgeLeft_mem_branchSet M hab)
        · have hxTail :
              x ∈ M.walkBranchUnion P :=
            liftWalkWithBranchConnectors_support_subset_walkBranchUnion
              M C P (edgeRight_mem_branchSet M hab) ht
              (by simpa using hxR)
          rw [MinorModel.walkBranchUnion] at hxTail ⊢
          rcases Finset.mem_biUnion.1 hxTail with ⟨z, hz, hxz⟩
          exact Finset.mem_biUnion.2 ⟨z, by simp [hz], hxz⟩

/-- Classification of the raw edges in a connector-parametrized lifted walk.
Every edge is either inside one of the local branch-set connectors used at a
visited minor vertex, or is one of the fixed host edges realizing a traversed
minor edge. -/
theorem liftWalkWithBranchConnectors_edge_local_or_crossing
    (M : MinorModel H G) (C : BranchConnectorChoice M) :
    {a b : W} → (P : H.Walk a b) → {s t : V} →
      (hs : s ∈ M.branchSet a) → (ht : t ∈ M.branchSet b) →
        ∀ {e : Sym2 V},
          e ∈ (liftWalkWithBranchConnectors M C P hs ht).edges.toFinset →
            (∃ z : W, z ∈ P.support.toFinset ∧
              ∃ (p q : V) (hp : p ∈ M.branchSet z)
                (hq : q ∈ M.branchSet z),
                e ∈ (C.path z hp hq).edgeSet) ∨
            (∃ (u v : W) (huv : H.Adj u v),
              s(u, v) ∈ P.edges.toFinset ∧
                e = s(edgeLeft M huv, edgeRight M huv))
  | a, _, _root_.SimpleGraph.Walk.nil' _, s, t, hs, ht, e, he => by
      left
      refine ⟨a, by simp, s, t, hs, ht, ?_⟩
      simpa [GraphPath.edgeSet, liftWalkWithBranchConnectors,
        _root_.SimpleGraph.Walk.edges_copy] using he
  | a, c, _root_.SimpleGraph.Walk.cons' _ b _ hab P, s, t, hs, ht, e, he => by
      classical
      let L := C.path a hs (edgeLeft_mem_branchSet M hab)
      let Lwalk :=
        L.walk.copy
          (C.source_eq a hs (edgeLeft_mem_branchSet M hab))
          (C.target_eq a hs (edgeLeft_mem_branchSet M hab))
      let R :=
        liftWalkWithBranchConnectors M C P
          (edgeRight_mem_branchSet M hab) ht
      have heList0 :
          e ∈
            (liftWalkWithBranchConnectors M C
              (_root_.SimpleGraph.Walk.cons hab P) hs ht).edges := by
        exact List.mem_toFinset.mp he
      have heList :
          e ∈ (Lwalk.append
            (_root_.SimpleGraph.Walk.cons
              (edgeLeft_adj_edgeRight M hab) R)).edges := by
        simpa [liftWalkWithBranchConnectors, L, Lwalk, R] using heList0
      have heCases :
          e ∈ Lwalk.edges ∨
            e = s(edgeLeft M hab, edgeRight M hab) ∨ e ∈ R.edges := by
        simpa [_root_.SimpleGraph.Walk.edges_append,
          _root_.SimpleGraph.Walk.edges_cons] using heList
      rcases heCases with heL | heRest
      · left
        refine ⟨a, by simp, s, edgeLeft M hab, hs,
          edgeLeft_mem_branchSet M hab, ?_⟩
        simpa [GraphPath.edgeSet, L, Lwalk,
          _root_.SimpleGraph.Walk.edges_copy] using heL
      rcases heRest with rfl | heR
      · right
        refine ⟨a, b, hab, ?_, rfl⟩
        simp [_root_.SimpleGraph.Walk.edges_cons]
      · have heRfin :
            e ∈ R.edges.toFinset := by
          simpa using heR
        have htail :=
          liftWalkWithBranchConnectors_edge_local_or_crossing
            M C P (edgeRight_mem_branchSet M hab) ht heRfin
        rcases htail with hlocal | hcross
        · left
          rcases hlocal with ⟨z, hz, p, q, hp, hq, hez⟩
          refine ⟨z, ?_, p, q, hp, hq, hez⟩
          have hzList : z ∈ P.support := by
            simpa using hz
          simp [_root_.SimpleGraph.Walk.support_cons, hzList]
        · right
          rcases hcross with ⟨u, v, huv, huvEdge, heq⟩
          refine ⟨u, v, huv, ?_, heq⟩
          have huvEdgeList : s(u, v) ∈ P.edges := by
            simpa using huvEdge
          simp [_root_.SimpleGraph.Walk.edges_cons, huvEdgeList]

/-- Graph-path wrapper around `liftWalkWithBranchConnectors`. -/
noncomputable def liftGraphPathWithBranchConnectors
    (M : MinorModel H G) (C : BranchConnectorChoice M)
    (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) : GraphPath G :=
  GraphPath.ofWalk (liftWalkWithBranchConnectors M C P.walk hs ht)

/-- Edge classification for the graph-path wrapper of the connector-parametrized
walk lift. -/
theorem liftGraphPathWithBranchConnectors_edge_local_or_crossing
    (M : MinorModel H G) (C : BranchConnectorChoice M)
    (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target)
    {e : Sym2 V}
    (he : e ∈ (liftGraphPathWithBranchConnectors M C P hs ht).edgeSet) :
      (∃ z : W, z ∈ P.walk.support.toFinset ∧
        ∃ (p q : V) (hp : p ∈ M.branchSet z)
          (hq : q ∈ M.branchSet z),
          e ∈ (C.path z hp hq).edgeSet) ∨
      (∃ (u v : W) (huv : H.Adj u v),
        s(u, v) ∈ P.walk.edges.toFinset ∧
          e = s(edgeLeft M huv, edgeRight M huv)) := by
  exact
    liftWalkWithBranchConnectors_edge_local_or_crossing
      M C P.walk hs ht
      (GraphPath.ofWalk_edgeSet_subset
        (liftWalkWithBranchConnectors M C P.walk hs ht) he)

/-- Refined edge classification for the graph-path wrapper of the
connector-parametrized walk lift, retaining the local-use/crossing-use
derivation. -/
theorem liftGraphPathWithBranchConnectors_edge_localUse_or_crossingUse
    (M : MinorModel H G) (C : BranchConnectorChoice M)
    (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target)
    {e : Sym2 V}
    (he : e ∈ (liftGraphPathWithBranchConnectors M C P hs ht).edgeSet) :
      (∃ (z : W) (p q : V) (hp : p ∈ M.branchSet z)
          (hq : q ∈ M.branchSet z),
          LiftWalkLocalUse M P.walk hs ht z p q ∧
            e ∈ (C.path z hp hq).edgeSet) ∨
      (∃ (u v : W) (huv : H.Adj u v),
          LiftWalkCrossingUse M P.walk hs ht u v huv ∧
            e = s(edgeLeft M huv, edgeRight M huv)) := by
  exact
    liftWalkWithBranchConnectors_edge_localUse_or_crossingUse
      M C P.walk hs ht
      (GraphPath.ofWalk_edgeSet_subset
        (liftWalkWithBranchConnectors M C P.walk hs ht) he)

/-- Converse local-use membership for the graph-path wrapper. -/
theorem liftGraphPathWithBranchConnectors_localUse_edge_mem
    (M : MinorModel H G) (C : BranchConnectorChoice M)
    (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target)
    (hsimple :
      (liftWalkWithBranchConnectors M C P.walk hs ht).IsPath)
    {z : W} {p q : V}
    {hp : p ∈ M.branchSet z} {hq : q ∈ M.branchSet z}
    (huse : LiftWalkLocalUse M P.walk hs ht z p q)
    {e : Sym2 V}
    (he : e ∈ (C.path z hp hq).edgeSet) :
    e ∈ (liftGraphPathWithBranchConnectors M C P hs ht).edgeSet := by
  have heWalk :
      e ∈ (liftWalkWithBranchConnectors M C P.walk hs ht).edges.toFinset :=
    liftWalkWithBranchConnectors_localUse_edge_mem
      M C P.walk hs ht huse he
  have hEdgeSet :
      (liftGraphPathWithBranchConnectors M C P hs ht).edgeSet =
        (liftWalkWithBranchConnectors M C P.walk hs ht).edges.toFinset := by
    simpa [liftGraphPathWithBranchConnectors] using
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofWalk_edgeSet_eq_of_isPath
        (liftWalkWithBranchConnectors M C P.walk hs ht) hsimple
  simpa [hEdgeSet] using heWalk

@[simp] theorem liftGraphPathWithBranchConnectors_source
    (M : MinorModel H G) (C : BranchConnectorChoice M)
    (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPathWithBranchConnectors M C P hs ht).source = s := rfl

@[simp] theorem liftGraphPathWithBranchConnectors_target
    (M : MinorModel H G) (C : BranchConnectorChoice M)
    (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPathWithBranchConnectors M C P hs ht).target = t := rfl

theorem liftGraphPathWithBranchConnectors_vertexSet_subset_walkBranchUnion
    (M : MinorModel H G) (C : BranchConnectorChoice M)
    (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPathWithBranchConnectors M C P hs ht).vertexSet ⊆
      M.walkBranchUnion P.walk := by
  intro x hx
  have hxWalk :
      x ∈ (liftWalkWithBranchConnectors M C P.walk hs ht).support.toFinset :=
    GraphPath.ofWalk_vertexSet_subset
      (liftWalkWithBranchConnectors M C P.walk hs ht) hx
  exact liftWalkWithBranchConnectors_support_subset_walkBranchUnion
    M C P.walk hs ht hxWalk

/-- Lift a graph path in a minor to a host-graph path between prescribed
vertices in the endpoint branch sets.  The chosen path stays inside the union
of branch sets visited by the minor path. -/
noncomputable def liftGraphPath
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) : GraphPath G :=
  GraphPath.ofConnectedInduce
    (M.walkBranchUnion P.walk)
    (M.walkBranchUnion_connected P.walk)
    s t
    (M.mem_walkBranchUnion_of_mem_branch (by simp) hs)
    (M.mem_walkBranchUnion_of_mem_branch (by simp) ht)

@[simp] theorem liftGraphPath_source
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPath M P hs ht).source = s := rfl

@[simp] theorem liftGraphPath_target
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPath M P hs ht).target = t := rfl

/-- The lifted path uses only branch sets visited by the minor path. -/
theorem liftGraphPath_vertexSet_subset_walkBranchUnion
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPath M P hs ht).vertexSet ⊆ M.walkBranchUnion P.walk := by
  exact GraphPath.ofConnectedInduce_vertexSet_subset
    (M.walkBranchUnion P.walk)
    (M.walkBranchUnion_connected P.walk)
    s t
    (M.mem_walkBranchUnion_of_mem_branch (by simp) hs)
    (M.mem_walkBranchUnion_of_mem_branch (by simp) ht)

/-- Disjoint minor paths have disjoint branch unions in the host. -/
theorem walkBranchUnion_disjoint_of_vertexSet_disjoint
    (M : MinorModel H G) {P Q : GraphPath H}
    (hdisj : Disjoint P.vertexSet Q.vertexSet) :
    Disjoint (M.walkBranchUnion P.walk) (M.walkBranchUnion Q.walk) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvQ
  rw [MinorModel.walkBranchUnion] at hvP hvQ
  rcases Finset.mem_biUnion.1 hvP with ⟨x, hxP, hvx⟩
  rcases Finset.mem_biUnion.1 hvQ with ⟨y, hyQ, hvy⟩
  by_cases hxy : x = y
  · subst y
    have hxP' : x ∈ P.vertexSet := by
      simpa [GraphPath.vertexSet] using hxP
    have hxQ' : x ∈ Q.vertexSet := by
      simpa [GraphPath.vertexSet] using hyQ
    exact Finset.disjoint_left.mp hdisj hxP' hxQ'
  · exact Finset.disjoint_left.mp (M.branch_disjoint hxy) hvx hvy

/-- If a host vertex lies both in the branch set of `w` and in the branch
union of a lifted minor path, then `w` is a vertex of that minor path. -/
theorem vertex_mem_of_branchSet_mem_walkBranchUnion
    (M : MinorModel H G) {P : GraphPath H} {w : W} {x : V}
    (hxw : x ∈ M.branchSet w)
    (hxU : x ∈ M.walkBranchUnion P.walk) :
    w ∈ P.vertexSet := by
  classical
  rw [MinorModel.walkBranchUnion] at hxU
  rcases Finset.mem_biUnion.1 hxU with ⟨z, hz, hxz⟩
  have hzw : z = w := by
    by_contra hne
    exact Finset.disjoint_left.mp (M.branch_disjoint hne) hxz hxw
  subst z
  simpa [GraphPath.vertexSet] using hz

end MinorModel

/-- The four terminal sets used in Section 2. -/
def twoPairTerminalSet
    (S₁ T₁ S₂ T₂ : Finset V) : Finset V :=
  ((S₁ ∪ T₁) ∪ S₂) ∪ T₂

theorem twoPairTerminalSet_swap_first
    (S₁ T₁ S₂ T₂ : Finset V) :
    twoPairTerminalSet T₁ S₁ S₂ T₂ =
      twoPairTerminalSet S₁ T₁ S₂ T₂ := by
  classical
  ext v
  simp [twoPairTerminalSet, or_left_comm]

/-- The union of four terminal sets has size at most the sum of their sizes. -/
theorem twoPairTerminalSet_card_le_sum
    (S₁ T₁ S₂ T₂ : Finset V) :
    (twoPairTerminalSet S₁ T₁ S₂ T₂).card ≤
      S₁.card + T₁.card + S₂.card + T₂.card := by
  classical
  have h₁ : (S₁ ∪ T₁).card ≤ S₁.card + T₁.card :=
    Finset.card_union_le S₁ T₁
  have h₂ : ((S₁ ∪ T₁) ∪ S₂).card ≤ (S₁ ∪ T₁).card + S₂.card :=
    Finset.card_union_le (S₁ ∪ T₁) S₂
  have h₃ :
      (((S₁ ∪ T₁) ∪ S₂) ∪ T₂).card ≤
        ((S₁ ∪ T₁) ∪ S₂).card + T₂.card :=
    Finset.card_union_le ((S₁ ∪ T₁) ∪ S₂) T₂
  dsimp [twoPairTerminalSet]
  omega

/-- If each terminal set has size at most `k`, the four terminal sets contain
at most `4k` vertices. -/
theorem twoPairTerminalSet_card_le_four_mul
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    (twoPairTerminalSet S₁ T₁ S₂ T₂).card ≤ 4 * k := by
  have hsum := twoPairTerminalSet_card_le_sum S₁ T₁ S₂ T₂
  omega

theorem subset_twoPairTerminalSet_S₁
    (S₁ T₁ S₂ T₂ : Finset V) :
    S₁ ⊆ twoPairTerminalSet S₁ T₁ S₂ T₂ := by
  intro v hv
  simp [twoPairTerminalSet, hv]

theorem subset_twoPairTerminalSet_T₁
    (S₁ T₁ S₂ T₂ : Finset V) :
    T₁ ⊆ twoPairTerminalSet S₁ T₁ S₂ T₂ := by
  intro v hv
  simp [twoPairTerminalSet, hv]

theorem subset_twoPairTerminalSet_S₂
    (S₁ T₁ S₂ T₂ : Finset V) :
    S₂ ⊆ twoPairTerminalSet S₁ T₁ S₂ T₂ := by
  intro v hv
  simp [twoPairTerminalSet, hv]

theorem subset_twoPairTerminalSet_T₂
    (S₁ T₁ S₂ T₂ : Finset V) :
    T₂ ⊆ twoPairTerminalSet S₁ T₁ S₂ T₂ := by
  intro v hv
  simp [twoPairTerminalSet, hv]

/-- The paper's Theorem 2.1 assumes that the four terminal sets are pairwise
disjoint.  This bundled predicate keeps the six disjointness obligations
explicit at the proof-facing boundary. -/
def TwoPairTerminalSetsDisjoint
    (S₁ T₁ S₂ T₂ : Finset V) : Prop :=
  Disjoint S₁ T₁ ∧ Disjoint S₁ S₂ ∧ Disjoint S₁ T₂ ∧
    Disjoint T₁ S₂ ∧ Disjoint T₁ T₂ ∧ Disjoint S₂ T₂

omit [DecidableEq V] in
theorem TwoPairTerminalSetsDisjoint.swap_first
    {S₁ T₁ S₂ T₂ : Finset V}
    (h : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    TwoPairTerminalSetsDisjoint T₁ S₁ S₂ T₂ := by
  rcases h with ⟨hS₁T₁, hS₁S₂, hS₁T₂, hT₁S₂, hT₁T₂, hS₂T₂⟩
  exact ⟨hS₁T₁.symm, hT₁S₂, hT₁T₂, hS₁S₂, hS₁T₂, hS₂T₂⟩

/-! ## X-respecting minors and good two-pair minors -/

/-- A branch-set minor model that keeps a specified host set `X` as singleton
branch sets in the pattern graph.

This is the paper's `X`-respecting minor model: every `x ∈ X` has a distinct
representative vertex in the minor whose branch set is exactly `{x}`. -/
structure XRespectingMinorModel
    {W : Type w} [DecidableEq W]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V)
    (X : Finset V) where
  /-- The underlying branch-set minor model. -/
  model : MinorModel H G
  /-- The representative vertex of the minor corresponding to a host terminal. -/
  terminalVertex : ∀ x : V, x ∈ X → W
  /-- Distinct host terminals have distinct representative vertices. -/
  terminal_injective :
    ∀ ⦃x y : V⦄ (hx : x ∈ X) (hy : y ∈ X),
      terminalVertex x hx = terminalVertex y hy → x = y
  /-- The representative branch set is the singleton host terminal. -/
  terminal_branchSet :
    ∀ (x : V) (hx : x ∈ X),
      model.branchSet (terminalVertex x hx) = {x}

namespace XRespectingMinorModel

variable {W : Type w} [DecidableEq W]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
variable {X : Finset V}

/-- The terminal set in the minor corresponding to a host-side subset of `X`. -/
noncomputable def terminalImage
    (M : XRespectingMinorModel H G X)
    (S : Finset V) (hS : S ⊆ X) : Finset W :=
  S.attach.image fun x => M.terminalVertex x.1 (hS x.2)

omit [DecidableEq V] in
/-- The terminal image has the same cardinality as the host-side subset. -/
theorem terminalImage_card
    (M : XRespectingMinorModel H G X)
    (S : Finset V) (hS : S ⊆ X) :
    (M.terminalImage S hS).card = S.card := by
  classical
  unfold terminalImage
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Subtype.ext
    exact M.terminal_injective (hS a.2) (hS b.2) hab

omit [DecidableEq V] in
/-- Membership in a terminal image is membership as the representative of one
of the host-side terminals. -/
theorem mem_terminalImage_iff
    (M : XRespectingMinorModel H G X)
    (S : Finset V) (hS : S ⊆ X) (w : W) :
    w ∈ M.terminalImage S hS ↔
      ∃ x : V, ∃ hx : x ∈ S, w = M.terminalVertex x (hS hx) := by
  classical
  unfold terminalImage
  constructor
  · intro hw
    rcases Finset.mem_image.mp hw with ⟨x, _hx, hxw⟩
    exact ⟨x.1, x.2, hxw.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨x, hx⟩, by simp, rfl⟩

omit [DecidableEq V] in
/-- A chosen host-side preimage of a vertex in a terminal image. -/
noncomputable def terminalImagePreimage
    (M : XRespectingMinorModel H G X)
    (S : Finset V) (hS : S ⊆ X)
    {w : W} (hw : w ∈ M.terminalImage S hS) : {x : V // x ∈ S} :=
  let h := (M.mem_terminalImage_iff S hS w).1 hw
  let x := Classical.choose h
  let hxw := Classical.choose_spec h
  let hx := Classical.choose hxw
  ⟨x, hx⟩

omit [DecidableEq V] in
/-- Reapplying `terminalVertex` to the chosen terminal-image preimage recovers
the image vertex. -/
theorem terminalVertex_terminalImagePreimage
    (M : XRespectingMinorModel H G X)
    (S : Finset V) (hS : S ⊆ X)
    {w : W} (hw : w ∈ M.terminalImage S hS) :
    M.terminalVertex
      (M.terminalImagePreimage S hS hw).1
      (hS (M.terminalImagePreimage S hS hw).2) = w := by
  classical
  let h := (M.mem_terminalImage_iff S hS w).1 hw
  let x := Classical.choose h
  let hxw := Classical.choose_spec h
  let hx := Classical.choose hxw
  have hrepr :
      w = M.terminalVertex x (hS hx) :=
    Classical.choose_spec hxw
  simpa [terminalImagePreimage, h, x, hxw, hx] using hrepr.symm

omit [DecidableEq V] in
/-- The terminal representative does not depend on the proof that the host
vertex belongs to the terminal set. -/
theorem terminalVertex_proof_irrel
    (M : XRespectingMinorModel H G X) {x : V}
    (hx hx' : x ∈ X) :
    M.terminalVertex x hx = M.terminalVertex x hx' := by
  congr

omit [DecidableEq V] in
/-- Pulling a bijection onto a terminal image back through
`terminalImagePreimage` gives a bijection onto the original terminal set. -/
theorem terminalImagePreimage_comp_bijective
    {ι : Type*}
    (M : XRespectingMinorModel H G X)
    (S : Finset V) (hS : S ⊆ X)
    (f : ι → {w : W // w ∈ M.terminalImage S hS})
    (hf : Function.Bijective f) :
    Function.Bijective
      (fun i : ι => M.terminalImagePreimage S hS (f i).2) := by
  classical
  constructor
  · intro i j hij
    apply hf.1
    apply Subtype.ext
    let xi := M.terminalImagePreimage S hS (f i).2
    let xj := M.terminalImagePreimage S hS (f j).2
    let term : {x : V // x ∈ S} → W :=
      fun x => M.terminalVertex x.1 (hS x.2)
    have hterm :
        M.terminalVertex xi.1 (hS xi.2) =
          M.terminalVertex xj.1 (hS xj.2) := by
      have hterm' : term xi = term xj := congrArg term hij
      simpa [term, xi, xj] using hterm'
    have hi :
        M.terminalVertex xi.1 (hS xi.2) = (f i).1 := by
      simpa [xi] using
        M.terminalVertex_terminalImagePreimage S hS (f i).2
    have hj :
        M.terminalVertex xj.1 (hS xj.2) = (f j).1 := by
      simpa [xj] using
        M.terminalVertex_terminalImagePreimage S hS (f j).2
    exact hi.symm.trans (hterm.trans hj)
  · intro x
    let w : {w : W // w ∈ M.terminalImage S hS} :=
      ⟨M.terminalVertex x.1 (hS x.2),
        (M.mem_terminalImage_iff S hS _).2 ⟨x.1, x.2, rfl⟩⟩
    rcases hf.2 w with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    let xi := M.terminalImagePreimage S hS (f i).2
    have hfi : (f i).1 = M.terminalVertex x.1 (hS x.2) := by
      exact congrArg Subtype.val hi
    have hrepr :
        M.terminalVertex xi.1 (hS xi.2) = (f i).1 := by
      simpa [xi] using
        M.terminalVertex_terminalImagePreimage S hS (f i).2
    exact M.terminal_injective (hS xi.2) (hS x.2) (hrepr.trans hfi)

/-- Reuse an `X`-respecting model after rewriting the terminal set. -/
def copyTerminalSet
    (M : XRespectingMinorModel H G X) {Y : Finset V}
    (hXY : X = Y) : XRespectingMinorModel H G Y where
  model := M.model
  terminalVertex := fun x hx =>
    M.terminalVertex x (by simpa [hXY] using hx)
  terminal_injective := by
    intro x y hx hy hxy
    exact M.terminal_injective
      (by simpa [hXY] using hx)
      (by simpa [hXY] using hy)
      hxy
  terminal_branchSet := by
    intro x hx
    exact M.terminal_branchSet x (by simpa [hXY] using hx)

omit [DecidableEq V] in
@[simp] theorem copyTerminalSet_terminalImage
    (M : XRespectingMinorModel H G X) {Y : Finset V}
    (hXY : X = Y) (S : Finset V) (hS : S ⊆ Y) :
    (M.copyTerminalSet hXY).terminalImage S hS =
      M.terminalImage S (by simpa [hXY] using hS) := by
  classical
  ext w
  simp [terminalImage, copyTerminalSet]

/-- Lift a perfect path packing through an `X`-respecting minor model.  The
terminal-image endpoint bijections are pulled back to the original host
terminal sets, while each minor path is expanded inside the union of the
branch sets it visits. -/
noncomputable def liftPerfectPathPacking
    (M : XRespectingMinorModel H G X)
    {S T : Finset V} (hS : S ⊆ X) (hT : T ⊆ X)
    (P : PerfectPathPacking H (M.terminalImage S hS)
      (M.terminalImage T hT)) :
    PerfectPathPacking G S T := by
  classical
  let src : P.Index → {x : V // x ∈ S} :=
    fun i => M.terminalImagePreimage S hS (P.source_mem i)
  let tgt : P.Index → {x : V // x ∈ T} :=
    fun i => M.terminalImagePreimage T hT (P.target_mem i)
  let hs : ∀ i : P.Index, (src i).1 ∈ M.model.branchSet (P.path i).source := by
    intro i
    have hrepr :
        M.terminalVertex (src i).1 (hS (src i).2) =
          (P.path i).source := by
      simpa [src] using
        M.terminalVertex_terminalImagePreimage S hS (P.source_mem i)
    rw [← hrepr, M.terminal_branchSet]
    simp
  let ht : ∀ i : P.Index, (tgt i).1 ∈ M.model.branchSet (P.path i).target := by
    intro i
    have hrepr :
        M.terminalVertex (tgt i).1 (hT (tgt i).2) =
          (P.path i).target := by
      simpa [tgt] using
        M.terminalVertex_terminalImagePreimage T hT (P.target_mem i)
    rw [← hrepr, M.terminal_branchSet]
    simp
  refine
    { toPathPacking := {
        Index := P.Index
        path := fun i =>
          MinorModel.liftGraphPath M.model (P.path i) (hs i) (ht i)
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
        Disjoint (M.model.walkBranchUnion (P.path i).walk)
          (M.model.walkBranchUnion (P.path j).walk) :=
      MinorModel.walkBranchUnion_disjoint_of_vertexSet_disjoint M.model hminor
    have hviU :
        v ∈ M.model.walkBranchUnion (P.path i).walk :=
      MinorModel.liftGraphPath_vertexSet_subset_walkBranchUnion
        M.model (P.path i) (hs i) (ht i) hvi
    have hvjU :
        v ∈ M.model.walkBranchUnion (P.path j).walk :=
      MinorModel.liftGraphPath_vertexSet_subset_walkBranchUnion
        M.model (P.path j) (hs j) (ht j) hvj
    exact Finset.disjoint_left.mp hunion hviU hvjU
  · change Function.Bijective src
    exact M.terminalImagePreimage_comp_bijective S hS
      (fun i => ⟨(P.path i).source, P.source_mem i⟩)
      P.source_bijective
  · change Function.Bijective tgt
    exact M.terminalImagePreimage_comp_bijective T hT
      (fun i => ⟨(P.path i).target, P.target_mem i⟩)
      P.target_bijective

/-- Each path produced by `liftPerfectPathPacking` stays inside the union of
the branch sets visited by its original minor path. -/
theorem liftPerfectPathPacking_path_vertexSet_subset_walkBranchUnion
    (M : XRespectingMinorModel H G X)
    {S T : Finset V} (hS : S ⊆ X) (hT : T ⊆ X)
    (P : PerfectPathPacking H (M.terminalImage S hS)
      (M.terminalImage T hT))
    (i : P.Index) :
    ((M.liftPerfectPathPacking hS hT P).path i).vertexSet ⊆
      M.model.walkBranchUnion (P.path i).walk := by
  classical
  unfold liftPerfectPathPacking
  dsimp
  exact MinorModel.liftGraphPath_vertexSet_subset_walkBranchUnion
    M.model (P.path i) _ _

/-- Structured version of `liftPerfectPathPacking`: each minor path is
expanded branch-by-branch, rather than by a single arbitrary connected path in
the whole branch union. -/
noncomputable def structuredLiftPerfectPathPacking
    (M : XRespectingMinorModel H G X)
    {S T : Finset V} (hS : S ⊆ X) (hT : T ⊆ X)
    (P : PerfectPathPacking H (M.terminalImage S hS)
      (M.terminalImage T hT)) :
    PerfectPathPacking G S T := by
  classical
  let src : P.Index → {x : V // x ∈ S} :=
    fun i => M.terminalImagePreimage S hS (P.source_mem i)
  let tgt : P.Index → {x : V // x ∈ T} :=
    fun i => M.terminalImagePreimage T hT (P.target_mem i)
  let hs : ∀ i : P.Index, (src i).1 ∈ M.model.branchSet (P.path i).source := by
    intro i
    have hrepr :
        M.terminalVertex (src i).1 (hS (src i).2) =
          (P.path i).source := by
      simpa [src] using
        M.terminalVertex_terminalImagePreimage S hS (P.source_mem i)
    rw [← hrepr, M.terminal_branchSet]
    simp
  let ht : ∀ i : P.Index, (tgt i).1 ∈ M.model.branchSet (P.path i).target := by
    intro i
    have hrepr :
        M.terminalVertex (tgt i).1 (hT (tgt i).2) =
          (P.path i).target := by
      simpa [tgt] using
        M.terminalVertex_terminalImagePreimage T hT (P.target_mem i)
    rw [← hrepr, M.terminal_branchSet]
    simp
  refine
    { toPathPacking := {
        Index := P.Index
        path := fun i =>
          MinorModel.structuredLiftGraphPath M.model (P.path i) (hs i) (ht i)
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
        Disjoint (M.model.walkBranchUnion (P.path i).walk)
          (M.model.walkBranchUnion (P.path j).walk) :=
      MinorModel.walkBranchUnion_disjoint_of_vertexSet_disjoint M.model hminor
    have hviU :
        v ∈ M.model.walkBranchUnion (P.path i).walk :=
      MinorModel.structuredLiftGraphPath_vertexSet_subset_walkBranchUnion
        M.model (P.path i) (hs i) (ht i) hvi
    have hvjU :
        v ∈ M.model.walkBranchUnion (P.path j).walk :=
      MinorModel.structuredLiftGraphPath_vertexSet_subset_walkBranchUnion
        M.model (P.path j) (hs j) (ht j) hvj
    exact Finset.disjoint_left.mp hunion hviU hvjU
  · change Function.Bijective src
    exact M.terminalImagePreimage_comp_bijective S hS
      (fun i => ⟨(P.path i).source, P.source_mem i⟩)
      P.source_bijective
  · change Function.Bijective tgt
    exact M.terminalImagePreimage_comp_bijective T hT
      (fun i => ⟨(P.path i).target, P.target_mem i⟩)
      P.target_bijective

/-- Each path produced by `structuredLiftPerfectPathPacking` stays inside the
union of branch sets visited by its original minor path. -/
theorem structuredLiftPerfectPathPacking_path_vertexSet_subset_walkBranchUnion
    (M : XRespectingMinorModel H G X)
    {S T : Finset V} (hS : S ⊆ X) (hT : T ⊆ X)
    (P : PerfectPathPacking H (M.terminalImage S hS)
      (M.terminalImage T hT))
    (i : P.Index) :
    ((M.structuredLiftPerfectPathPacking hS hT P).path i).vertexSet ⊆
      M.model.walkBranchUnion (P.path i).walk := by
  classical
  unfold structuredLiftPerfectPathPacking
  dsimp
  exact MinorModel.structuredLiftGraphPath_vertexSet_subset_walkBranchUnion
    M.model (P.path i) _ _

/-- Connector-parametrized version of `structuredLiftPerfectPathPacking`.  The
local connector choice is shared across all lifted paths, which is the hook used
for the paper's red/blue branch-set rerouting. -/
noncomputable def liftPerfectPathPackingWithBranchConnectors
    (M : XRespectingMinorModel H G X)
    (C : MinorModel.BranchConnectorChoice M.model)
    {S T : Finset V} (hS : S ⊆ X) (hT : T ⊆ X)
    (P : PerfectPathPacking H (M.terminalImage S hS)
      (M.terminalImage T hT)) :
    PerfectPathPacking G S T := by
  classical
  let src : P.Index → {x : V // x ∈ S} :=
    fun i => M.terminalImagePreimage S hS (P.source_mem i)
  let tgt : P.Index → {x : V // x ∈ T} :=
    fun i => M.terminalImagePreimage T hT (P.target_mem i)
  let hs : ∀ i : P.Index, (src i).1 ∈ M.model.branchSet (P.path i).source := by
    intro i
    have hrepr :
        M.terminalVertex (src i).1 (hS (src i).2) =
          (P.path i).source := by
      simpa [src] using
        M.terminalVertex_terminalImagePreimage S hS (P.source_mem i)
    rw [← hrepr, M.terminal_branchSet]
    simp
  let ht : ∀ i : P.Index, (tgt i).1 ∈ M.model.branchSet (P.path i).target := by
    intro i
    have hrepr :
        M.terminalVertex (tgt i).1 (hT (tgt i).2) =
          (P.path i).target := by
      simpa [tgt] using
        M.terminalVertex_terminalImagePreimage T hT (P.target_mem i)
    rw [← hrepr, M.terminal_branchSet]
    simp
  refine
    { toPathPacking := {
        Index := P.Index
        path := fun i =>
          MinorModel.liftGraphPathWithBranchConnectors
            M.model C (P.path i) (hs i) (ht i)
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
        Disjoint (M.model.walkBranchUnion (P.path i).walk)
          (M.model.walkBranchUnion (P.path j).walk) :=
      MinorModel.walkBranchUnion_disjoint_of_vertexSet_disjoint M.model hminor
    have hviU :
        v ∈ M.model.walkBranchUnion (P.path i).walk :=
      MinorModel.liftGraphPathWithBranchConnectors_vertexSet_subset_walkBranchUnion
        M.model C (P.path i) (hs i) (ht i) hvi
    have hvjU :
        v ∈ M.model.walkBranchUnion (P.path j).walk :=
      MinorModel.liftGraphPathWithBranchConnectors_vertexSet_subset_walkBranchUnion
        M.model C (P.path j) (hs j) (ht j) hvj
    exact Finset.disjoint_left.mp hunion hviU hvjU
  · change Function.Bijective src
    exact M.terminalImagePreimage_comp_bijective S hS
      (fun i => ⟨(P.path i).source, P.source_mem i⟩)
      P.source_bijective
  · change Function.Bijective tgt
    exact M.terminalImagePreimage_comp_bijective T hT
      (fun i => ⟨(P.path i).target, P.target_mem i⟩)
      P.target_bijective

/-- Each path produced by the connector-parametrized lift stays inside the union
of branch sets visited by its original minor path. -/
theorem liftPerfectPathPackingWithBranchConnectors_path_vertexSet_subset_walkBranchUnion
    (M : XRespectingMinorModel H G X)
    (C : MinorModel.BranchConnectorChoice M.model)
    {S T : Finset V} (hS : S ⊆ X) (hT : T ⊆ X)
    (P : PerfectPathPacking H (M.terminalImage S hS)
      (M.terminalImage T hT))
    (i : P.Index) :
    ((M.liftPerfectPathPackingWithBranchConnectors C hS hT P).path i).vertexSet ⊆
      M.model.walkBranchUnion (P.path i).walk := by
  classical
  unfold liftPerfectPathPackingWithBranchConnectors
  dsimp
  exact MinorModel.liftGraphPathWithBranchConnectors_vertexSet_subset_walkBranchUnion
    M.model C (P.path i) _ _

/-- Edge classification for one path of the connector-parametrized lifted
packing, retaining the local-use/crossing-use derivation from the underlying
walk lift. -/
theorem liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
    (M : XRespectingMinorModel H G X)
    (C : MinorModel.BranchConnectorChoice M.model)
    {S T : Finset V} (hS : S ⊆ X) (hT : T ⊆ X)
    (P : PerfectPathPacking H (M.terminalImage S hS)
      (M.terminalImage T hT))
    (i : P.Index) {e : Sym2 V}
    (he :
      e ∈
        ((M.liftPerfectPathPackingWithBranchConnectors C hS hT P).path i).edgeSet) :
      let src : P.Index → {x : V // x ∈ S} :=
        fun i => M.terminalImagePreimage S hS (P.source_mem i)
      let tgt : P.Index → {x : V // x ∈ T} :=
        fun i => M.terminalImagePreimage T hT (P.target_mem i)
      let hs : ∀ i : P.Index,
          (src i).1 ∈ M.model.branchSet (P.path i).source := by
        intro i
        have hrepr :
            M.terminalVertex (src i).1 (hS (src i).2) =
              (P.path i).source := by
          simpa [src] using
            M.terminalVertex_terminalImagePreimage S hS (P.source_mem i)
        rw [← hrepr, M.terminal_branchSet]
        simp
      let ht : ∀ i : P.Index,
          (tgt i).1 ∈ M.model.branchSet (P.path i).target := by
        intro i
        have hrepr :
            M.terminalVertex (tgt i).1 (hT (tgt i).2) =
              (P.path i).target := by
          simpa [tgt] using
            M.terminalVertex_terminalImagePreimage T hT (P.target_mem i)
        rw [← hrepr, M.terminal_branchSet]
        simp
      (∃ (z : W) (p q : V) (hp : p ∈ M.model.branchSet z)
          (hq : q ∈ M.model.branchSet z),
          MinorModel.LiftWalkLocalUse M.model (P.path i).walk (hs i) (ht i)
            z p q ∧
            e ∈ (C.path z hp hq).edgeSet) ∨
      (∃ (u v : W) (huv : H.Adj u v),
          MinorModel.LiftWalkCrossingUse M.model (P.path i).walk (hs i) (ht i)
            u v huv ∧
            e =
              s(MinorModel.edgeLeft M.model huv,
                MinorModel.edgeRight M.model huv)) := by
  classical
  dsimp only
  let src : P.Index → {x : V // x ∈ S} :=
    fun i => M.terminalImagePreimage S hS (P.source_mem i)
  let tgt : P.Index → {x : V // x ∈ T} :=
    fun i => M.terminalImagePreimage T hT (P.target_mem i)
  let hs : ∀ i : P.Index,
      (src i).1 ∈ M.model.branchSet (P.path i).source := by
    intro i
    have hrepr :
        M.terminalVertex (src i).1 (hS (src i).2) =
          (P.path i).source := by
      simpa [src] using
        M.terminalVertex_terminalImagePreimage S hS (P.source_mem i)
    rw [← hrepr, M.terminal_branchSet]
    simp
  let ht : ∀ i : P.Index,
      (tgt i).1 ∈ M.model.branchSet (P.path i).target := by
    intro i
    have hrepr :
        M.terminalVertex (tgt i).1 (hT (tgt i).2) =
          (P.path i).target := by
      simpa [tgt] using
        M.terminalVertex_terminalImagePreimage T hT (P.target_mem i)
    rw [← hrepr, M.terminal_branchSet]
    simp
  have heLift :
      e ∈
        (MinorModel.liftGraphPathWithBranchConnectors
          M.model C (P.path i) (hs i) (ht i)).edgeSet := by
    simpa [liftPerfectPathPackingWithBranchConnectors, src, tgt, hs, ht] using he
  simpa [src, tgt, hs, ht] using
    MinorModel.liftGraphPathWithBranchConnectors_edge_localUse_or_crossingUse
      M.model C (P.path i) (hs i) (ht i) heLift

end XRespectingMinorModel

/-- The identity minor model is `X`-respecting for every terminal set `X`. -/
noncomputable def XRespectingMinorModel.refl
    (G : _root_.SimpleGraph V) (X : Finset V) :
    XRespectingMinorModel G G X where
  model := MinorModel.refl G
  terminalVertex := fun x _hx => x
  terminal_injective := by
    intro x y _hx _hy hxy
    exact hxy
  terminal_branchSet := by
    intro x _hx
    rfl

namespace XRespectingMinorModel

@[simp] theorem refl_terminalImage
    (G : _root_.SimpleGraph V) (X S : Finset V) (hS : S ⊆ X) :
    (XRespectingMinorModel.refl G X).terminalImage S hS = S := by
  classical
  ext x
  constructor
  · intro hx
    rcases
        ((XRespectingMinorModel.refl G X).mem_terminalImage_iff S hS x).1 hx with
      ⟨y, hy, hyx⟩
    simpa [XRespectingMinorModel.refl] using hyx ▸ hy
  · intro hx
    exact
      ((XRespectingMinorModel.refl G X).mem_terminalImage_iff S hS x).2
        ⟨x, hx, rfl⟩

/-- A degree-one host terminal has degree at most one at its representative in
an `X`-respecting minor. -/
theorem terminalVertex_degreeAtMost_one_of_host_degreeEquals_one
    {W : Type w} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {X : Finset V} (M : XRespectingMinorModel H G X)
    {x : V} (hx : x ∈ X)
    (hdeg : DegreeEquals G x 1) :
    DegreeAtMost H (M.terminalVertex x hx) 1 := by
  classical
  let t := M.terminalVertex x hx
  let N : Finset W := Finset.univ.filter fun y : W => H.Adj t y
  have huniq : ∀ y z : W, H.Adj t y → H.Adj t z → y = z := by
    intro y z hty htz
    by_contra hyz
    rcases M.model.adjacent hty with ⟨a, ha, b, hb, hab⟩
    rcases M.model.adjacent htz with ⟨a', ha', c, hc, hac⟩
    have ha_eq : a = x := by
      have hbranch := M.terminal_branchSet x hx
      simpa [t, hbranch] using ha
    have ha'_eq : a' = x := by
      have hbranch := M.terminal_branchSet x hx
      simpa [t, hbranch] using ha'
    subst a
    subst a'
    have hbc : b = c := DegreeEquals.one_adj_eq hdeg hab hac
    have hdis := M.model.branch_disjoint hyz
    exact Finset.disjoint_left.mp hdis hb (by simpa [hbc] using hc)
  refine ⟨N, ?_, ?_⟩
  · intro y
    simp [N, t]
  · rw [Finset.card_le_one_iff]
    intro y z hy hz
    exact huniq y z (by simpa [N] using hy) (by simpa [N] using hz)

omit [DecidableEq V] in
/-- Disjoint host-side terminal subsets have disjoint terminal images in an
`X`-respecting minor. -/
theorem terminalImage_disjoint
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {X : Finset V} (M : XRespectingMinorModel H G X)
    {A B : Finset V} (hA : A ⊆ X) (hB : B ⊆ X)
    (hdisj : Disjoint A B) :
    Disjoint (M.terminalImage A hA) (M.terminalImage B hB) := by
  classical
  rw [Finset.disjoint_left]
  intro y hyA hyB
  rcases (M.mem_terminalImage_iff A hA y).1 hyA with
    ⟨a, ha, hya⟩
  rcases (M.mem_terminalImage_iff B hB y).1 hyB with
    ⟨b, hb, hyb⟩
  have hab : a = b :=
    M.terminal_injective (hA ha) (hB hb) (hya.symm.trans hyb)
  exact Finset.disjoint_left.mp hdisj ha (by simpa [hab] using hb)

end XRespectingMinorModel

/-- `H` is an `X`-respecting minor of `G`. -/
def IsXRespectingMinor
    {W : Type w} [DecidableEq W]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V)
    (X : Finset V) : Prop :=
  Nonempty (XRespectingMinorModel H G X)

/-- A contracted edge avoids the terminal representatives of an
`X`-respecting model. -/
def EdgeAvoidsTerminalRepresentatives
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {X : Finset V}
    (M : XRespectingMinorModel H G X) (a b : W) : Prop :=
  ∀ x : V, ∀ hx : x ∈ X,
    M.terminalVertex x hx ≠ a ∧ M.terminalVertex x hx ≠ b

/-- In a node-disjoint path packing, a vertex belongs to at most one indexed
path. -/
theorem pathPacking_index_eq_of_mem_vertexSet
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PathPacking H A B) {i j : P.Index} {v : W}
    (hvi : v ∈ (P.path i).vertexSet)
    (hvj : v ∈ (P.path j).vertexSet) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp (P.node_disjoint hij) hvi hvj

/-- A paper-literal good minor for the two-pair routing instance: it is
`X`-respecting for the four terminal sets and both terminal pairs are routable
inside the minor. -/
structure TwoPairGoodMinor
    {W : Type w} [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (S₁ T₁ S₂ T₂ : Finset V) where
  /-- The minor model preserves the four host-side terminal sets as singleton
  branch sets. -/
  respecting :
    XRespectingMinorModel H G (twoPairTerminalSet S₁ T₁ S₂ T₂)
  /-- The first terminal pair is routable in the minor. -/
  redRouting :
    PerfectPathPacking H
      (respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
  /-- The second terminal pair is routable in the minor. -/
  blueRouting :
    PerfectPathPacking H
      (respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))

namespace TwoPairGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V}
variable {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- The four terminal images inside a good minor. -/
noncomputable def terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) : Finset W :=
  twoPairTerminalSet
    (N.respecting.terminalImage S₁
      (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
    (N.respecting.terminalImage T₁
      (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
    (N.respecting.terminalImage S₂
      (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
    (N.respecting.terminalImage T₂
      (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))

/-- Every terminal representative belongs to the terminal set of the minor. -/
theorem terminalVertex_mem_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (x : V) (hx : x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂) :
    N.respecting.terminalVertex x hx ∈ N.terminalSet := by
  classical
  have hxCases : x ∈ S₁ ∨ x ∈ T₁ ∨ x ∈ S₂ ∨ x ∈ T₂ := by
    simpa [twoPairTerminalSet] using hx
  rcases hxCases with hxS₁ | hxT₁ | hxS₂ | hxT₂
  · have hmem :
        N.respecting.terminalVertex x
            ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hxS₁) ∈
          N.respecting.terminalImage S₁
            (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) :=
      (N.respecting.mem_terminalImage_iff S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) _).2
        ⟨x, hxS₁, rfl⟩
    have hrep :
        N.respecting.terminalVertex x
            ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hxS₁) =
          N.respecting.terminalVertex x hx := by
      congr
    exact subset_twoPairTerminalSet_S₁ _ _ _ _ (by simpa [hrep] using hmem)
  · have hmem :
        N.respecting.terminalVertex x
            ((subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hxT₁) ∈
          N.respecting.terminalImage T₁
            (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) :=
      (N.respecting.mem_terminalImage_iff T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) _).2
        ⟨x, hxT₁, rfl⟩
    have hrep :
        N.respecting.terminalVertex x
            ((subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hxT₁) =
          N.respecting.terminalVertex x hx := by
      congr
    exact subset_twoPairTerminalSet_T₁ _ _ _ _ (by simpa [hrep] using hmem)
  · have hmem :
        N.respecting.terminalVertex x
            ((subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hxS₂) ∈
          N.respecting.terminalImage S₂
            (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) :=
      (N.respecting.mem_terminalImage_iff S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) _).2
        ⟨x, hxS₂, rfl⟩
    have hrep :
        N.respecting.terminalVertex x
            ((subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hxS₂) =
          N.respecting.terminalVertex x hx := by
      congr
    exact subset_twoPairTerminalSet_S₂ _ _ _ _ (by simpa [hrep] using hmem)
  · have hmem :
        N.respecting.terminalVertex x
            ((subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hxT₂) ∈
          N.respecting.terminalImage T₂
            (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) :=
      (N.respecting.mem_terminalImage_iff T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) _).2
        ⟨x, hxT₂, rfl⟩
    have hrep :
        N.respecting.terminalVertex x
            ((subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hxT₂) =
          N.respecting.terminalVertex x hx := by
      congr
    exact subset_twoPairTerminalSet_T₂ _ _ _ _ (by simpa [hrep] using hmem)

/-- Lift the red routing of a good minor back to the original host graph. -/
noncomputable def liftRedRouting
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    PerfectPathPacking G S₁ T₁ :=
  N.respecting.liftPerfectPathPacking
    (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
    (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
    N.redRouting

/-- Lift the blue routing of a good minor back to the original host graph. -/
noncomputable def liftBlueRouting
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    PerfectPathPacking G S₂ T₂ :=
  N.respecting.liftPerfectPathPacking
    (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
    (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
    N.blueRouting

/-- A good minor certifies host-side routability of both terminal pairs. -/
theorem routableIn_host
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    RoutableIn G S₁ T₁ ∧ RoutableIn G S₂ T₂ :=
  ⟨⟨N.liftRedRouting⟩, ⟨N.liftBlueRouting⟩⟩

/-- If both endpoints lie outside the terminal images, the edge avoids all
terminal representatives. -/
theorem edgeAvoidsTerminalRepresentatives_of_not_mem_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) {a b : W}
    (ha : a ∉ N.terminalSet) (hb : b ∉ N.terminalSet) :
    EdgeAvoidsTerminalRepresentatives N.respecting a b := by
  intro x hx
  constructor
  · intro hxa
    exact ha (by simpa [hxa] using N.terminalVertex_mem_terminalSet x hx)
  · intro hxb
    exact hb (by simpa [hxb] using N.terminalVertex_mem_terminalSet x hx)

/-- The source endpoint of a red routing path is a terminal in the minor. -/
theorem red_source_mem_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (i : N.redRouting.Index) :
    (N.redRouting.path i).source ∈ N.terminalSet :=
  subset_twoPairTerminalSet_S₁ _ _ _ _ (N.redRouting.source_mem i)

/-- The target endpoint of a red routing path is a terminal in the minor. -/
theorem red_target_mem_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (i : N.redRouting.Index) :
    (N.redRouting.path i).target ∈ N.terminalSet :=
  subset_twoPairTerminalSet_T₁ _ _ _ _ (N.redRouting.target_mem i)

/-- The source endpoint of a blue routing path is a terminal in the minor. -/
theorem blue_source_mem_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (j : N.blueRouting.Index) :
    (N.blueRouting.path j).source ∈ N.terminalSet :=
  subset_twoPairTerminalSet_S₂ _ _ _ _ (N.blueRouting.source_mem j)

/-- The target endpoint of a blue routing path is a terminal in the minor. -/
theorem blue_target_mem_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (j : N.blueRouting.Index) :
    (N.blueRouting.path j).target ∈ N.terminalSet :=
  subset_twoPairTerminalSet_T₂ _ _ _ _ (N.blueRouting.target_mem j)

/-- A nonterminal vertex on a red routing path is internal to that path. -/
theorem red_internal_of_mem_vertexSet_of_not_terminal
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {v : W} (hv : v ∉ N.terminalSet)
    {i : N.redRouting.Index} :
    v ≠ (N.redRouting.path i).source ∧
      v ≠ (N.redRouting.path i).target := by
  constructor
  · intro h
    exact hv (by simpa [h] using N.red_source_mem_terminalSet i)
  · intro h
    exact hv (by simpa [h] using N.red_target_mem_terminalSet i)

/-- A nonterminal vertex on a blue routing path is internal to that path. -/
theorem blue_internal_of_mem_vertexSet_of_not_terminal
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {v : W} (hv : v ∉ N.terminalSet)
    {j : N.blueRouting.Index} :
    v ≠ (N.blueRouting.path j).source ∧
      v ≠ (N.blueRouting.path j).target := by
  constructor
  · intro h
    exact hv (by simpa [h] using N.blue_source_mem_terminalSet j)
  · intro h
    exact hv (by simpa [h] using N.blue_target_mem_terminalSet j)

/-- The red routing is node-disjoint, so a minor vertex lies on at most one red
path. -/
theorem redRouting_index_eq_of_mem_vertexSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {i j : N.redRouting.Index} {v : W}
    (hvi : v ∈ (N.redRouting.path i).vertexSet)
    (hvj : v ∈ (N.redRouting.path j).vertexSet) :
    i = j :=
  pathPacking_index_eq_of_mem_vertexSet N.redRouting.toPathPacking hvi hvj

/-- The blue routing is node-disjoint, so a minor vertex lies on at most one blue
path. -/
theorem blueRouting_index_eq_of_mem_vertexSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {i j : N.blueRouting.Index} {v : W}
    (hvi : v ∈ (N.blueRouting.path i).vertexSet)
    (hvj : v ∈ (N.blueRouting.path j).vertexSet) :
    i = j :=
  pathPacking_index_eq_of_mem_vertexSet N.blueRouting.toPathPacking hvi hvj

/-- The red local connector used by the paper's minor-expansion paragraph.

If `w` is an internal vertex of the selected red routing, this is the connector
inside the branch set of `w` between the host endpoints of the preceding and
following red minor edges.  If `w` is not such an internal red vertex, the
connector is the trivial path at a fixed branch-set point; those fallback
connectors are never charged as red local segments. -/
noncomputable def redLocalConnector
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) : GraphPath G := by
  classical
  by_cases h : w ∈ N.redRouting.toPathPacking.vertexSet ∧ w ∉ N.terminalSet
  · let i : N.redRouting.Index :=
      Classical.choose ((N.redRouting.toPathPacking.mem_vertexSet).1 h.1)
    have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
      Classical.choose_spec ((N.redRouting.toPathPacking.mem_vertexSet).1 h.1)
    have hwInternal :=
      N.red_internal_of_mem_vertexSet_of_not_terminal (v := w) h.2 (i := i)
    let prevExists :=
      GraphPath.exists_backward_edge_of_mem_not_source
        (N.redRouting.path i) hwPath hwInternal.1
    let prev : W := Classical.choose prevExists
    have hprevEdge : s(prev, w) ∈ (N.redRouting.path i).edgeSet :=
      (Classical.choose_spec prevExists).1
    let nextExists :=
      GraphPath.exists_forward_edge_of_mem_not_target
        (N.redRouting.path i) hwPath hwInternal.2
    let next : W := Classical.choose nextExists
    have hnextEdge : s(w, next) ∈ (N.redRouting.path i).edgeSet :=
      (Classical.choose_spec nextExists).1
    have hprevAdj : H.Adj prev w := by
      have hEdge : s(prev, w) ∈ H.edgeSet :=
        GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i) hprevEdge
      simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
    have hnextAdj : H.Adj w next := by
      have hEdge : s(w, next) ∈ H.edgeSet :=
        GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i) hnextEdge
      simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
    exact
      MinorModel.branchConnector N.respecting.model w
        (s := MinorModel.edgeRight N.respecting.model hprevAdj)
        (t := MinorModel.edgeLeft N.respecting.model hnextAdj)
        (MinorModel.edgeRight_mem_branchSet N.respecting.model hprevAdj)
        (MinorModel.edgeLeft_mem_branchSet N.respecting.model hnextAdj)
  · exact MinorModel.trivialBranchConnector N.respecting.model w

theorem redLocalConnector_vertexSet_subset_branchSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) :
    (N.redLocalConnector w).vertexSet ⊆ N.respecting.model.branchSet w := by
  classical
  unfold redLocalConnector
  by_cases h : w ∈ N.redRouting.toPathPacking.vertexSet ∧ w ∉ N.terminalSet
  · let i : N.redRouting.Index :=
      Classical.choose ((N.redRouting.toPathPacking.mem_vertexSet).1 h.1)
    have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
      Classical.choose_spec ((N.redRouting.toPathPacking.mem_vertexSet).1 h.1)
    have hwInternal :=
      N.red_internal_of_mem_vertexSet_of_not_terminal (v := w) h.2 (i := i)
    let prevExists :=
      GraphPath.exists_backward_edge_of_mem_not_source
        (N.redRouting.path i) hwPath hwInternal.1
    let prev : W := Classical.choose prevExists
    have hprevEdge : s(prev, w) ∈ (N.redRouting.path i).edgeSet :=
      (Classical.choose_spec prevExists).1
    let nextExists :=
      GraphPath.exists_forward_edge_of_mem_not_target
        (N.redRouting.path i) hwPath hwInternal.2
    let next : W := Classical.choose nextExists
    have hnextEdge : s(w, next) ∈ (N.redRouting.path i).edgeSet :=
      (Classical.choose_spec nextExists).1
    have hprevAdj : H.Adj prev w := by
      have hEdge : s(prev, w) ∈ H.edgeSet :=
        GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i) hprevEdge
      simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
    have hnextAdj : H.Adj w next := by
      have hEdge : s(w, next) ∈ H.edgeSet :=
        GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i) hnextEdge
      simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
    simpa [h] using
      MinorModel.branchConnector_vertexSet_subset_branchSet
        N.respecting.model w
        (MinorModel.edgeRight_mem_branchSet N.respecting.model hprevAdj)
        (MinorModel.edgeLeft_mem_branchSet N.respecting.model hnextAdj)
  · simpa [h] using
      MinorModel.trivialBranchConnector_vertexSet_subset_branchSet
        N.respecting.model w

/-- The source of the red local connector is the host endpoint chosen for the
incoming red minor edge. -/
theorem redLocalConnector_source_eq_of_backward_edge
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {i : N.redRouting.Index} {prev : W}
    (hwPath : w ∈ (N.redRouting.path i).vertexSet)
    (hwT : w ∉ N.terminalSet)
    (hprevEdge : s(prev, w) ∈ (N.redRouting.path i).edgeSet)
    (hprevBefore : (N.redRouting.path i).Before prev w)
    (hprev_ne : prev ≠ w) :
    (N.redLocalConnector w).source =
      MinorModel.edgeRight N.respecting.model
        (by
          have hEdge : s(prev, w) ∈ H.edgeSet :=
            GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i) hprevEdge
          simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge) := by
  classical
  have hwPack : w ∈ N.redRouting.toPathPacking.vertexSet :=
    (N.redRouting.toPathPacking.mem_vertexSet).2 ⟨i, hwPath⟩
  unfold redLocalConnector
  rw [dif_pos ⟨hwPack, hwT⟩]
  let i₀ : N.redRouting.Index :=
    Classical.choose ((N.redRouting.toPathPacking.mem_vertexSet).1 hwPack)
  have hwPath₀ : w ∈ (N.redRouting.path i₀).vertexSet :=
    Classical.choose_spec ((N.redRouting.toPathPacking.mem_vertexSet).1 hwPack)
  have hi₀ : i₀ = i :=
    N.redRouting_index_eq_of_mem_vertexSet hwPath₀ hwPath
  subst i₀
  let hwInternal :=
    N.red_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (i := i)
  let prevExists :=
    GraphPath.exists_backward_edge_of_mem_not_source
      (N.redRouting.path i) hwPath hwInternal.1
  let prev₀ : W := Classical.choose prevExists
  have hprev₀Edge : s(prev₀, w) ∈ (N.redRouting.path i).edgeSet :=
    (Classical.choose_spec prevExists).1
  have hprev₀Before : (N.redRouting.path i).Before prev₀ w :=
    (Classical.choose_spec prevExists).2.1
  have hprev₀_ne : prev₀ ≠ w :=
    (Classical.choose_spec prevExists).2.2
  have hprev_eq : prev₀ = prev :=
    (GraphPath.backward_edge_unique (N.redRouting.path i)
      hprev₀Edge hprev₀Before hprev₀_ne
      hprevEdge hprevBefore hprev_ne)
  subst prev
  simp [MinorModel.branchConnector_source]
  congr <;> simp [hi₀]

/-- The target of the red local connector is the host endpoint chosen for the
outgoing red minor edge. -/
theorem redLocalConnector_target_eq_of_forward_edge
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {i : N.redRouting.Index} {next : W}
    (hwPath : w ∈ (N.redRouting.path i).vertexSet)
    (hwT : w ∉ N.terminalSet)
    (hnextEdge : s(w, next) ∈ (N.redRouting.path i).edgeSet)
    (hnextBefore : (N.redRouting.path i).Before w next)
    (hnext_ne : w ≠ next) :
    (N.redLocalConnector w).target =
      MinorModel.edgeLeft N.respecting.model
        (by
          have hEdge : s(w, next) ∈ H.edgeSet :=
            GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i) hnextEdge
          simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge) := by
  classical
  have hwPack : w ∈ N.redRouting.toPathPacking.vertexSet :=
    (N.redRouting.toPathPacking.mem_vertexSet).2 ⟨i, hwPath⟩
  unfold redLocalConnector
  rw [dif_pos ⟨hwPack, hwT⟩]
  let i₀ : N.redRouting.Index :=
    Classical.choose ((N.redRouting.toPathPacking.mem_vertexSet).1 hwPack)
  have hwPath₀ : w ∈ (N.redRouting.path i₀).vertexSet :=
    Classical.choose_spec ((N.redRouting.toPathPacking.mem_vertexSet).1 hwPack)
  have hi₀ : i₀ = i :=
    N.redRouting_index_eq_of_mem_vertexSet hwPath₀ hwPath
  subst i₀
  let hwInternal :=
    N.red_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (i := i)
  let nextExists :=
    GraphPath.exists_forward_edge_of_mem_not_target
      (N.redRouting.path i) hwPath hwInternal.2
  let next₀ : W := Classical.choose nextExists
  have hnext₀Edge : s(w, next₀) ∈ (N.redRouting.path i).edgeSet :=
    (Classical.choose_spec nextExists).1
  have hnext₀Before : (N.redRouting.path i).Before w next₀ :=
    (Classical.choose_spec nextExists).2.1
  have hnext₀_ne : w ≠ next₀ :=
    (Classical.choose_spec nextExists).2.2
  have hnext_eq : next₀ = next :=
    GraphPath.forward_edge_unique (N.redRouting.path i)
      hnext₀Edge hnext₀Before hnext₀_ne
      hnextEdge hnextBefore hnext_ne
  subst next
  simp [MinorModel.branchConnector_target]
  congr <;> simp [hi₀]

/-- The preliminary blue local connector before rerouting through the selected
red local connector.  This is the paper's arbitrary path `R₂` inside the branch
set. -/
noncomputable def bluePreliminaryLocalConnector
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) : GraphPath G := by
  classical
  by_cases h : w ∈ N.blueRouting.toPathPacking.vertexSet ∧ w ∉ N.terminalSet
  · let j : N.blueRouting.Index :=
      Classical.choose ((N.blueRouting.toPathPacking.mem_vertexSet).1 h.1)
    have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
      Classical.choose_spec ((N.blueRouting.toPathPacking.mem_vertexSet).1 h.1)
    have hwInternal :=
      N.blue_internal_of_mem_vertexSet_of_not_terminal (v := w) h.2 (j := j)
    let prevExists :=
      GraphPath.exists_backward_edge_of_mem_not_source
        (N.blueRouting.path j) hwPath hwInternal.1
    let prev : W := Classical.choose prevExists
    have hprevEdge : s(prev, w) ∈ (N.blueRouting.path j).edgeSet :=
      (Classical.choose_spec prevExists).1
    let nextExists :=
      GraphPath.exists_forward_edge_of_mem_not_target
        (N.blueRouting.path j) hwPath hwInternal.2
    let next : W := Classical.choose nextExists
    have hnextEdge : s(w, next) ∈ (N.blueRouting.path j).edgeSet :=
      (Classical.choose_spec nextExists).1
    have hprevAdj : H.Adj prev w := by
      have hEdge : s(prev, w) ∈ H.edgeSet :=
        GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j) hprevEdge
      simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
    have hnextAdj : H.Adj w next := by
      have hEdge : s(w, next) ∈ H.edgeSet :=
        GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j) hnextEdge
      simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
    exact
      MinorModel.branchConnector N.respecting.model w
        (s := MinorModel.edgeRight N.respecting.model hprevAdj)
        (t := MinorModel.edgeLeft N.respecting.model hnextAdj)
        (MinorModel.edgeRight_mem_branchSet N.respecting.model hprevAdj)
        (MinorModel.edgeLeft_mem_branchSet N.respecting.model hnextAdj)
  · exact MinorModel.trivialBranchConnector N.respecting.model w

theorem bluePreliminaryLocalConnector_vertexSet_subset_branchSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) :
    (N.bluePreliminaryLocalConnector w).vertexSet ⊆
      N.respecting.model.branchSet w := by
  classical
  unfold bluePreliminaryLocalConnector
  by_cases h : w ∈ N.blueRouting.toPathPacking.vertexSet ∧ w ∉ N.terminalSet
  · let j : N.blueRouting.Index :=
      Classical.choose ((N.blueRouting.toPathPacking.mem_vertexSet).1 h.1)
    have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
      Classical.choose_spec ((N.blueRouting.toPathPacking.mem_vertexSet).1 h.1)
    have hwInternal :=
      N.blue_internal_of_mem_vertexSet_of_not_terminal (v := w) h.2 (j := j)
    let prevExists :=
      GraphPath.exists_backward_edge_of_mem_not_source
        (N.blueRouting.path j) hwPath hwInternal.1
    let prev : W := Classical.choose prevExists
    have hprevEdge : s(prev, w) ∈ (N.blueRouting.path j).edgeSet :=
      (Classical.choose_spec prevExists).1
    let nextExists :=
      GraphPath.exists_forward_edge_of_mem_not_target
        (N.blueRouting.path j) hwPath hwInternal.2
    let next : W := Classical.choose nextExists
    have hnextEdge : s(w, next) ∈ (N.blueRouting.path j).edgeSet :=
      (Classical.choose_spec nextExists).1
    have hprevAdj : H.Adj prev w := by
      have hEdge : s(prev, w) ∈ H.edgeSet :=
        GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j) hprevEdge
      simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
    have hnextAdj : H.Adj w next := by
      have hEdge : s(w, next) ∈ H.edgeSet :=
        GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j) hnextEdge
      simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
    simpa [h] using
      MinorModel.branchConnector_vertexSet_subset_branchSet
        N.respecting.model w
        (MinorModel.edgeRight_mem_branchSet N.respecting.model hprevAdj)
        (MinorModel.edgeLeft_mem_branchSet N.respecting.model hnextAdj)
  · simpa [h] using
      MinorModel.trivialBranchConnector_vertexSet_subset_branchSet
        N.respecting.model w

/-- The source of the preliminary blue local connector is the host endpoint
chosen for the incoming blue minor edge. -/
theorem bluePreliminaryLocalConnector_source_eq_of_backward_edge
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {j : N.blueRouting.Index} {prev : W}
    (hwPath : w ∈ (N.blueRouting.path j).vertexSet)
    (hwT : w ∉ N.terminalSet)
    (hprevEdge : s(prev, w) ∈ (N.blueRouting.path j).edgeSet)
    (hprevBefore : (N.blueRouting.path j).Before prev w)
    (hprev_ne : prev ≠ w) :
    (N.bluePreliminaryLocalConnector w).source =
      MinorModel.edgeRight N.respecting.model
        (by
          have hEdge : s(prev, w) ∈ H.edgeSet :=
            GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j) hprevEdge
          simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge) := by
  classical
  have hwPack : w ∈ N.blueRouting.toPathPacking.vertexSet :=
    (N.blueRouting.toPathPacking.mem_vertexSet).2 ⟨j, hwPath⟩
  unfold bluePreliminaryLocalConnector
  rw [dif_pos ⟨hwPack, hwT⟩]
  let j₀ : N.blueRouting.Index :=
    Classical.choose ((N.blueRouting.toPathPacking.mem_vertexSet).1 hwPack)
  have hwPath₀ : w ∈ (N.blueRouting.path j₀).vertexSet :=
    Classical.choose_spec ((N.blueRouting.toPathPacking.mem_vertexSet).1 hwPack)
  have hj₀ : j₀ = j :=
    N.blueRouting_index_eq_of_mem_vertexSet hwPath₀ hwPath
  subst j₀
  let hwInternal :=
    N.blue_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (j := j)
  let prevExists :=
    GraphPath.exists_backward_edge_of_mem_not_source
      (N.blueRouting.path j) hwPath hwInternal.1
  let prev₀ : W := Classical.choose prevExists
  have hprev₀Edge : s(prev₀, w) ∈ (N.blueRouting.path j).edgeSet :=
    (Classical.choose_spec prevExists).1
  have hprev₀Before : (N.blueRouting.path j).Before prev₀ w :=
    (Classical.choose_spec prevExists).2.1
  have hprev₀_ne : prev₀ ≠ w :=
    (Classical.choose_spec prevExists).2.2
  have hprev_eq : prev₀ = prev :=
    (GraphPath.backward_edge_unique (N.blueRouting.path j)
      hprev₀Edge hprev₀Before hprev₀_ne
      hprevEdge hprevBefore hprev_ne)
  subst prev
  simp [MinorModel.branchConnector_source]
  congr <;> simp [hj₀]

/-- The target of the preliminary blue local connector is the host endpoint
chosen for the outgoing blue minor edge. -/
theorem bluePreliminaryLocalConnector_target_eq_of_forward_edge
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {j : N.blueRouting.Index} {next : W}
    (hwPath : w ∈ (N.blueRouting.path j).vertexSet)
    (hwT : w ∉ N.terminalSet)
    (hnextEdge : s(w, next) ∈ (N.blueRouting.path j).edgeSet)
    (hnextBefore : (N.blueRouting.path j).Before w next)
    (hnext_ne : w ≠ next) :
    (N.bluePreliminaryLocalConnector w).target =
      MinorModel.edgeLeft N.respecting.model
        (by
          have hEdge : s(w, next) ∈ H.edgeSet :=
            GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j) hnextEdge
          simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge) := by
  classical
  have hwPack : w ∈ N.blueRouting.toPathPacking.vertexSet :=
    (N.blueRouting.toPathPacking.mem_vertexSet).2 ⟨j, hwPath⟩
  unfold bluePreliminaryLocalConnector
  rw [dif_pos ⟨hwPack, hwT⟩]
  let j₀ : N.blueRouting.Index :=
    Classical.choose ((N.blueRouting.toPathPacking.mem_vertexSet).1 hwPack)
  have hwPath₀ : w ∈ (N.blueRouting.path j₀).vertexSet :=
    Classical.choose_spec ((N.blueRouting.toPathPacking.mem_vertexSet).1 hwPack)
  have hj₀ : j₀ = j :=
    N.blueRouting_index_eq_of_mem_vertexSet hwPath₀ hwPath
  subst j₀
  let hwInternal :=
    N.blue_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (j := j)
  let nextExists :=
    GraphPath.exists_forward_edge_of_mem_not_target
      (N.blueRouting.path j) hwPath hwInternal.2
  let next₀ : W := Classical.choose nextExists
  have hnext₀Edge : s(w, next₀) ∈ (N.blueRouting.path j).edgeSet :=
    (Classical.choose_spec nextExists).1
  have hnext₀Before : (N.blueRouting.path j).Before w next₀ :=
    (Classical.choose_spec nextExists).2.1
  have hnext₀_ne : w ≠ next₀ :=
    (Classical.choose_spec nextExists).2.2
  have hnext_eq : next₀ = next :=
    GraphPath.forward_edge_unique (N.blueRouting.path j)
      hnext₀Edge hnext₀Before hnext₀_ne
      hnextEdge hnextBefore hnext_ne
  subst next
  simp [MinorModel.branchConnector_target]
  congr <;> simp [hj₀]

/-- The paper's final blue local connector inside a branch set: it is either the
preliminary blue connector, if disjoint from the red local connector, or the
clean rerouting through that red connector. -/
noncomputable def blueLocalConnector
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) : GraphPath G :=
  GraphPath.cleanOrDisjointReroute
    (N.redLocalConnector w) (N.bluePreliminaryLocalConnector w)

/-- The first possible high-degree splice vertex in branch set `w` from the
paper's local rerouting paragraph.  In the disjoint case there are no such
intersections; choosing the preliminary blue source gives a harmless
two-point superset. -/
noncomputable def paperLocalSpliceFirst
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) : V := by
  classical
  by_cases hne :
      ((N.bluePreliminaryLocalConnector w).vertexSet ∩
        (N.redLocalConnector w).vertexSet).Nonempty
  · exact
      (N.bluePreliminaryLocalConnector w).firstHitVertex
        (N.redLocalConnector w).vertexSet hne
  · exact (N.bluePreliminaryLocalConnector w).source

/-- The last possible high-degree splice vertex in branch set `w` from the
paper's local rerouting paragraph.  In the disjoint case there are no such
intersections; choosing the preliminary blue target gives a harmless
two-point superset. -/
noncomputable def paperLocalSpliceLast
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) : V := by
  classical
  by_cases hne :
      ((N.bluePreliminaryLocalConnector w).vertexSet ∩
        (N.redLocalConnector w).vertexSet).Nonempty
  · exact
      (N.bluePreliminaryLocalConnector w).lastHitVertex
        (N.redLocalConnector w).vertexSet hne
  · exact (N.bluePreliminaryLocalConnector w).target

theorem paperLocalSpliceFirst_eq_of_inter_nonempty
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W)
    (hne :
      ((N.bluePreliminaryLocalConnector w).vertexSet ∩
        (N.redLocalConnector w).vertexSet).Nonempty) :
    N.paperLocalSpliceFirst w =
      (N.bluePreliminaryLocalConnector w).firstHitVertex
        (N.redLocalConnector w).vertexSet hne := by
  classical
  simp [paperLocalSpliceFirst, hne]

theorem paperLocalSpliceLast_eq_of_inter_nonempty
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W)
    (hne :
      ((N.bluePreliminaryLocalConnector w).vertexSet ∩
        (N.redLocalConnector w).vertexSet).Nonempty) :
    N.paperLocalSpliceLast w =
      (N.bluePreliminaryLocalConnector w).lastHitVertex
        (N.redLocalConnector w).vertexSet hne := by
  classical
  simp [paperLocalSpliceLast, hne]

theorem paperLocalSpliceFirst_eq_of_inter_empty
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W)
    (hne :
      ¬ ((N.bluePreliminaryLocalConnector w).vertexSet ∩
        (N.redLocalConnector w).vertexSet).Nonempty) :
    N.paperLocalSpliceFirst w = (N.bluePreliminaryLocalConnector w).source := by
  classical
  simp [paperLocalSpliceFirst, hne]

theorem paperLocalSpliceLast_eq_of_inter_empty
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W)
    (hne :
      ¬ ((N.bluePreliminaryLocalConnector w).vertexSet ∩
        (N.redLocalConnector w).vertexSet).Nonempty) :
    N.paperLocalSpliceLast w = (N.bluePreliminaryLocalConnector w).target := by
  classical
  simp [paperLocalSpliceLast, hne]

theorem blueLocalConnector_vertexSet_subset_branchSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) :
    (N.blueLocalConnector w).vertexSet ⊆
      N.respecting.model.branchSet w := by
  intro x hx
  have hxUnion :
      x ∈ (N.bluePreliminaryLocalConnector w).vertexSet ∪
        (N.redLocalConnector w).vertexSet :=
    GraphPath.cleanOrDisjointReroute_vertexSet_subset
      (N.redLocalConnector w) (N.bluePreliminaryLocalConnector w) hx
  rcases Finset.mem_union.1 hxUnion with hxBlue | hxRed
  · exact N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet w hxBlue
  · exact N.redLocalConnector_vertexSet_subset_branchSet w hxRed

/-- The red routing obtained by the paper's branch-by-branch expansion. -/
noncomputable def paperRedRouting
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    PerfectPathPacking G S₁ T₁ :=
  N.respecting.liftPerfectPathPackingWithBranchConnectors
    (MinorModel.BranchConnectorChoice.prefer
      N.respecting.model N.redLocalConnector
      N.redLocalConnector_vertexSet_subset_branchSet)
    (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
    (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
    N.redRouting

/-- The blue routing obtained by the paper's branch-by-branch expansion: each
local blue connector is rerouted through the selected red local connector in the
same branch set. -/
noncomputable def paperBlueRouting
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    PerfectPathPacking G S₂ T₂ :=
  N.respecting.liftPerfectPathPackingWithBranchConnectors
    (MinorModel.BranchConnectorChoice.preferRerouteThrough
      N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
      N.redLocalConnector_vertexSet_subset_branchSet
      N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet)
    (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
    (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
    N.blueRouting

/-- A red paper-expanded path edge incident with a host vertex in branch set
`w` is either an edge of the red local connector of `w`, or it is incident at
one of the two endpoints where the red path enters/leaves that branch set. -/
theorem paperRedRouting_path_edge_incident_branchSet_local_or_endpoint
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x y : V} {i : N.redRouting.Index}
    (hwT : w ∉ N.terminalSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (he : s(x, y) ∈ (N.paperRedRouting.path i).edgeSet) :
    s(x, y) ∈ (N.redLocalConnector w).edgeSet ∨
      x = (N.redLocalConnector w).source ∨
        x = (N.redLocalConnector w).target := by
  classical
  let C :=
    MinorModel.BranchConnectorChoice.prefer
      N.respecting.model N.redLocalConnector
      N.redLocalConnector_vertexSet_subset_branchSet
  have hclass :=
    N.respecting.liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
      C
      (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
      (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
      N.redRouting i
      (by simpa [TwoPairGoodMinor.paperRedRouting, C] using he)
  dsimp only at hclass
  rcases hclass with hlocal | hcross
  · rcases hlocal with ⟨z, p, q, hp, hq, huse, heC⟩
    have hxC : x ∈ (C.path z hp hq).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (C.path z hp hq) heC).1
    have hxz : x ∈ N.respecting.model.branchSet z :=
      C.vertexSet_subset z hp hq hxC
    have hzw : z = w := by
      by_contra hne
      exact Finset.disjoint_left.mp (N.respecting.model.branch_disjoint hne)
        hxz hxw
    subst z
    have hsrc : (N.redLocalConnector w).source = p := by
      rcases
          MinorModel.liftWalkLocalUse_left_endpoint_or_crossing
            N.respecting.model huse with hstart | hprev
      · rcases hstart with ⟨hwSource, _hp⟩
        exact False.elim
          (hwT (by
            simpa [hwSource] using N.red_source_mem_terminalSet i))
      · rcases hprev with ⟨prev, hprev, hcrossUse, hpEq⟩
        have hdata :=
          MinorModel.liftWalkCrossingUse_edgeSet_before
            N.respecting.model (N.redRouting.path i) _ _ hcrossUse
        have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (N.redRouting.path i) hdata.1).2
        exact
          (N.redLocalConnector_source_eq_of_backward_edge
            hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hpEq.symm
    have htgt : (N.redLocalConnector w).target = q := by
      rcases
          MinorModel.liftWalkLocalUse_right_endpoint_or_crossing
            N.respecting.model huse with hend | hnext
      · rcases hend with ⟨hwTarget, _hq⟩
        exact False.elim
          (hwT (by
            simpa [hwTarget] using N.red_target_mem_terminalSet i))
      · rcases hnext with ⟨next, hnext, hcrossUse, hqEq⟩
        have hdata :=
          MinorModel.liftWalkCrossingUse_edgeSet_before
            N.respecting.model (N.redRouting.path i) _ _ hcrossUse
        have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (N.redRouting.path i) hdata.1).1
        exact
          (N.redLocalConnector_target_eq_of_forward_edge
            hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hqEq.symm
    have hEdgeSet :
        (C.path w hp hq).edgeSet = (N.redLocalConnector w).edgeSet :=
      MinorModel.BranchConnectorChoice.prefer_path_edgeSet_eq
        N.respecting.model N.redLocalConnector
        N.redLocalConnector_vertexSet_subset_branchSet w hp hq hsrc htgt
    left
    simpa [hEdgeSet] using heC
  · rcases hcross with ⟨u, v, huv, huse, heq⟩
    have hxEdge : x ∈ s(MinorModel.edgeLeft N.respecting.model huv,
        MinorModel.edgeRight N.respecting.model huv) := by
      have hxxy : x ∈ s(x, y) := by simp
      simpa [heq] using hxxy
    rcases
        MinorModel.branch_eq_left_or_right_of_mem_crossing_edge
          N.respecting.model huv hxw hxEdge with hwu | hwv
    · subst u
      have hxLeft : x = MinorModel.edgeLeft N.respecting.model huv := by
        rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
        · exact hxLeft
        · have hw_eq_v : w = v :=
            MinorModel.eq_right_of_edgeRight_mem_branchSet
              N.respecting.model huv (by simpa [hxRight] using hxw)
          exact False.elim (huv.ne hw_eq_v)
      have hdata :=
        MinorModel.liftWalkCrossingUse_edgeSet_before
          N.respecting.model (N.redRouting.path i) _ _ huse
      have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (N.redRouting.path i) hdata.1).1
      have htarget :
          (N.redLocalConnector w).target =
            MinorModel.edgeLeft N.respecting.model huv :=
        N.redLocalConnector_target_eq_of_forward_edge
          hwPath hwT hdata.1 hdata.2.1 hdata.2.2
      right
      right
      exact hxLeft.trans htarget.symm
    · subst v
      have hxRight : x = MinorModel.edgeRight N.respecting.model huv := by
        rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
        · have hw_eq_u : w = u :=
            MinorModel.eq_left_of_edgeLeft_mem_branchSet
              N.respecting.model huv (by simpa [hxLeft] using hxw)
          exact False.elim (huv.ne hw_eq_u.symm)
        · exact hxRight
      have hdata :=
        MinorModel.liftWalkCrossingUse_edgeSet_before
          N.respecting.model (N.redRouting.path i) _ _ huse
      have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (N.redRouting.path i) hdata.1).2
      have hsource :
          (N.redLocalConnector w).source =
            MinorModel.edgeRight N.respecting.model huv :=
        N.redLocalConnector_source_eq_of_backward_edge
          hwPath hwT hdata.1 hdata.2.1 hdata.2.2
      right
      left
      exact hxRight.trans hsource.symm

/-- A blue paper-expanded path edge incident with a host vertex in branch set
`w` is either an edge of the cleaned/rerouted blue local connector of `w`, or
it is incident at one of the two endpoints where the blue path enters/leaves
that branch set. -/
theorem paperBlueRouting_path_edge_incident_branchSet_local_or_endpoint
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x y : V} {j : N.blueRouting.Index}
    (hwT : w ∉ N.terminalSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (he : s(x, y) ∈ (N.paperBlueRouting.path j).edgeSet) :
    s(x, y) ∈ (N.blueLocalConnector w).edgeSet ∨
      x = (N.blueLocalConnector w).source ∨
        x = (N.blueLocalConnector w).target := by
  classical
  let C :=
    MinorModel.BranchConnectorChoice.preferRerouteThrough
      N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
      N.redLocalConnector_vertexSet_subset_branchSet
      N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet
  have hclass :=
    N.respecting.liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
      C
      (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
      (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
      N.blueRouting j
      (by simpa [TwoPairGoodMinor.paperBlueRouting, C] using he)
  dsimp only at hclass
  rcases hclass with hlocal | hcross
  · rcases hlocal with ⟨z, p, q, hp, hq, huse, heC⟩
    have hxC : x ∈ (C.path z hp hq).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (C.path z hp hq) heC).1
    have hxz : x ∈ N.respecting.model.branchSet z :=
      C.vertexSet_subset z hp hq hxC
    have hzw : z = w := by
      by_contra hne
      exact Finset.disjoint_left.mp (N.respecting.model.branch_disjoint hne)
        hxz hxw
    subst z
    have hsrcPre : (N.bluePreliminaryLocalConnector w).source = p := by
      rcases
          MinorModel.liftWalkLocalUse_left_endpoint_or_crossing
            N.respecting.model huse with hstart | hprev
      · rcases hstart with ⟨hwSource, _hp⟩
        exact False.elim
          (hwT (by
            simpa [hwSource] using N.blue_source_mem_terminalSet j))
      · rcases hprev with ⟨prev, hprev, hcrossUse, hpEq⟩
        have hdata :=
          MinorModel.liftWalkCrossingUse_edgeSet_before
            N.respecting.model (N.blueRouting.path j) _ _ hcrossUse
        have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (N.blueRouting.path j) hdata.1).2
        exact
          (N.bluePreliminaryLocalConnector_source_eq_of_backward_edge
            hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hpEq.symm
    have htgtPre : (N.bluePreliminaryLocalConnector w).target = q := by
      rcases
          MinorModel.liftWalkLocalUse_right_endpoint_or_crossing
            N.respecting.model huse with hend | hnext
      · rcases hend with ⟨hwTarget, _hq⟩
        exact False.elim
          (hwT (by
            simpa [hwTarget] using N.blue_target_mem_terminalSet j))
      · rcases hnext with ⟨next, hnext, hcrossUse, hqEq⟩
        have hdata :=
          MinorModel.liftWalkCrossingUse_edgeSet_before
            N.respecting.model (N.blueRouting.path j) _ _ hcrossUse
        have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (N.blueRouting.path j) hdata.1).1
        exact
          (N.bluePreliminaryLocalConnector_target_eq_of_forward_edge
            hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hqEq.symm
    have hEdgeSet :
        (C.path w hp hq).edgeSet = (N.blueLocalConnector w).edgeSet := by
      simpa [TwoPairGoodMinor.blueLocalConnector] using
        MinorModel.BranchConnectorChoice.preferRerouteThrough_path_edgeSet_eq
          N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
          N.redLocalConnector_vertexSet_subset_branchSet
          N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet
          w hp hq hsrcPre htgtPre
    left
    simpa [hEdgeSet] using heC
  · rcases hcross with ⟨u, v, huv, huse, heq⟩
    have hxEdge : x ∈ s(MinorModel.edgeLeft N.respecting.model huv,
        MinorModel.edgeRight N.respecting.model huv) := by
      have hxxy : x ∈ s(x, y) := by simp
      simpa [heq] using hxxy
    rcases
        MinorModel.branch_eq_left_or_right_of_mem_crossing_edge
          N.respecting.model huv hxw hxEdge with hwu | hwv
    · subst u
      have hxLeft : x = MinorModel.edgeLeft N.respecting.model huv := by
        rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
        · exact hxLeft
        · have hw_eq_v : w = v :=
            MinorModel.eq_right_of_edgeRight_mem_branchSet
              N.respecting.model huv (by simpa [hxRight] using hxw)
          exact False.elim (huv.ne hw_eq_v)
      have hdata :=
        MinorModel.liftWalkCrossingUse_edgeSet_before
          N.respecting.model (N.blueRouting.path j) _ _ huse
      have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (N.blueRouting.path j) hdata.1).1
      have htarget :
          (N.bluePreliminaryLocalConnector w).target =
            MinorModel.edgeLeft N.respecting.model huv :=
        N.bluePreliminaryLocalConnector_target_eq_of_forward_edge
          hwPath hwT hdata.1 hdata.2.1 hdata.2.2
      right
      right
      simpa [TwoPairGoodMinor.blueLocalConnector] using hxLeft.trans htarget.symm
    · subst v
      have hxRight : x = MinorModel.edgeRight N.respecting.model huv := by
        rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
        · have hw_eq_u : w = u :=
            MinorModel.eq_left_of_edgeLeft_mem_branchSet
              N.respecting.model huv (by simpa [hxLeft] using hxw)
          exact False.elim (huv.ne hw_eq_u.symm)
        · exact hxRight
      have hdata :=
        MinorModel.liftWalkCrossingUse_edgeSet_before
          N.respecting.model (N.blueRouting.path j) _ _ huse
      have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (N.blueRouting.path j) hdata.1).2
      have hsource :
          (N.bluePreliminaryLocalConnector w).source =
            MinorModel.edgeRight N.respecting.model huv :=
        N.bluePreliminaryLocalConnector_source_eq_of_backward_edge
          hwPath hwT hdata.1 hdata.2.1 hdata.2.2
      right
      left
      simpa [TwoPairGoodMinor.blueLocalConnector] using hxRight.trans hsource.symm

/-- An edge of the red local connector appears as an adjacency in the local
two-connector union for branch set `w`. -/
theorem paperLocalUnion_adj_of_redLocal_edge
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x y : V}
    (he : s(x, y) ∈ (N.redLocalConnector w).edgeSet) :
    (twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))).Adj x y := by
  have hne : x ≠ y := by
    have hadj : G.Adj x y :=
      GraphPath.edgeSet_subset_edgeSet (N.redLocalConnector w) he
    exact hadj.ne
  simp [twoPackingUnionGraph, PathPacking.spanningGraph_adj_iff_exists_path_edge,
    GraphPath.singletonPerfectPathPacking, he, hne]

/-- An edge of the blue local connector appears as an adjacency in the local
two-connector union for branch set `w`. -/
theorem paperLocalUnion_adj_of_blueLocal_edge
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x y : V}
    (he : s(x, y) ∈ (N.blueLocalConnector w).edgeSet) :
    (twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))).Adj x y := by
  have hne : x ≠ y := by
    have hadj : G.Adj x y :=
      GraphPath.edgeSet_subset_edgeSet (N.blueLocalConnector w) he
    exact hadj.ne
  simp [twoPackingUnionGraph, PathPacking.spanningGraph_adj_iff_exists_path_edge,
    GraphPath.singletonPerfectPathPacking, he, hne]

/-- A global paper-routing adjacency incident with a vertex in a nonterminal
branch set is either already local to the two selected connectors in that
branch, or it leaves/enters the branch at one of the four connector endpoints. -/
theorem paperRouting_adj_incident_branchSet_local_or_endpoint
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x y : V}
    (hwT : w ∉ N.terminalSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxy :
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting).Adj x y) :
    (twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))).Adj x y ∨
      x = (N.redLocalConnector w).source ∨
        x = (N.redLocalConnector w).target ∨
          x = (N.blueLocalConnector w).source ∨
            x = (N.blueLocalConnector w).target := by
  classical
  have hcases :
      N.paperRedRouting.toPathPacking.spanningGraph.Adj x y ∨
        N.paperBlueRouting.toPathPacking.spanningGraph.Adj x y := by
    simpa [twoPackingUnionGraph] using hxy
  rcases hcases with hred | hblue
  · rcases
      (N.paperRedRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
        hred with
      ⟨⟨i, he⟩, _hne⟩
    rcases
        N.paperRedRouting_path_edge_incident_branchSet_local_or_endpoint
          hwT hxw he with heLocal | hsource | htarget
    · left
      exact N.paperLocalUnion_adj_of_redLocal_edge heLocal
    · right
      left
      exact hsource
    · right
      right
      left
      exact htarget
  · rcases
      (N.paperBlueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
        hblue with
      ⟨⟨j, he⟩, _hne⟩
    rcases
        N.paperBlueRouting_path_edge_incident_branchSet_local_or_endpoint
          hwT hxw he with heLocal | hsource | htarget
    · left
      exact N.paperLocalUnion_adj_of_blueLocal_edge heLocal
    · right
      right
      right
      left
      exact hsource
    · right
      right
      right
      right
      exact htarget

/-- If all original terminals have degree one in the host graph, then every
terminal image in a good minor has degree at most one. -/
theorem degreeAtMost_one_of_mem_terminalSet
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    {y : W} (hy : y ∈ N.terminalSet) :
    DegreeAtMost H y 1 := by
  classical
  simp [terminalSet, twoPairTerminalSet] at hy
  rcases hy with hy | hy | hy | hy
  · rcases
        (N.respecting.mem_terminalImage_iff S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) y).1 hy with
      ⟨x, hx, rfl⟩
    exact N.respecting.terminalVertex_degreeAtMost_one_of_host_degreeEquals_one
      ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hx)
      (hdeg x ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hx))
  · rcases
        (N.respecting.mem_terminalImage_iff T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) y).1 hy with
      ⟨x, hx, rfl⟩
    exact N.respecting.terminalVertex_degreeAtMost_one_of_host_degreeEquals_one
      ((subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hx)
      (hdeg x ((subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hx))
  · rcases
        (N.respecting.mem_terminalImage_iff S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) y).1 hy with
      ⟨x, hx, rfl⟩
    exact N.respecting.terminalVertex_degreeAtMost_one_of_host_degreeEquals_one
      ((subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hx)
      (hdeg x ((subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hx))
  · rcases
        (N.respecting.mem_terminalImage_iff T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) y).1 hy with
      ⟨x, hx, rfl⟩
    exact N.respecting.terminalVertex_degreeAtMost_one_of_host_degreeEquals_one
      ((subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hx)
      (hdeg x ((subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hx))

/-- A terminal image vertex can occur on a simple path in the minor only as an
endpoint, provided original terminals have degree one in the host. -/
theorem isEndpoint_of_mem_terminalSet_of_mem_path
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    {y : W} (hy : y ∈ N.terminalSet)
    (P : GraphPath H) (hyP : y ∈ P.vertexSet) :
    P.IsEndpoint y :=
  GraphPath.isEndpoint_of_mem_vertexSet_of_degreeAtMost_one P
    (N.degreeAtMost_one_of_mem_terminalSet hdeg hy) hyP

/-- The images of two disjoint host-side terminal subsets are disjoint in the
minor. -/
theorem terminalImage_disjoint
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {A B : Finset V}
    (hA : A ⊆ twoPairTerminalSet S₁ T₁ S₂ T₂)
    (hB : B ⊆ twoPairTerminalSet S₁ T₁ S₂ T₂)
    (hdisj : Disjoint A B) :
    Disjoint
      (N.respecting.terminalImage A hA)
      (N.respecting.terminalImage B hB) :=
  N.respecting.terminalImage_disjoint hA hB hdisj

/-- Host-side terminal disjointness transfers to the four terminal images of a
good minor. -/
theorem terminalImagesDisjoint
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    Disjoint
        (N.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
        (N.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)) ∧
      Disjoint
        (N.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
        (N.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)) ∧
      Disjoint
        (N.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
        (N.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) ∧
      Disjoint
        (N.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
        (N.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)) ∧
      Disjoint
        (N.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
        (N.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) ∧
      Disjoint
        (N.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
        (N.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) := by
  rcases hdisj with ⟨hS₁T₁, hS₁S₂, hS₁T₂, hT₁S₂, hT₁T₂, hS₂T₂⟩
  exact
    ⟨N.terminalImage_disjoint
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hS₁T₁,
      N.terminalImage_disjoint
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hS₁S₂,
      N.terminalImage_disjoint
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hS₁T₂,
      N.terminalImage_disjoint
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hT₁S₂,
      N.terminalImage_disjoint
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hT₁T₂,
      N.terminalImage_disjoint
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hS₂T₂⟩

/-- A terminal image from `S₁` cannot be a vertex of a blue routing path when
original terminals have degree one and the four terminal sets are disjoint. -/
theorem not_blue_vertex_of_mem_S₁_terminalImage
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {y : W}
    (hyS₁ :
      y ∈ N.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
    {j : N.blueRouting.Index}
    (hyB : y ∈ (N.blueRouting.path j).vertexSet) :
    False := by
  classical
  have hyTerm : y ∈ N.terminalSet :=
    subset_twoPairTerminalSet_S₁ _ _ _ _ hyS₁
  rcases N.isEndpoint_of_mem_terminalSet_of_mem_path hdeg hyTerm
      (N.blueRouting.path j) hyB with hsrc | htgt
  · have hyS₂ :
        y ∈ N.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
      simpa [hsrc] using N.blueRouting.source_mem j
    have hS₁S₂ := (N.terminalImagesDisjoint hdisj).2.1
    exact Finset.disjoint_left.mp hS₁S₂ hyS₁ hyS₂
  · have hyT₂ :
        y ∈ N.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
      simpa [htgt] using N.blueRouting.target_mem j
    have hS₁T₂ := (N.terminalImagesDisjoint hdisj).2.2.1
    exact Finset.disjoint_left.mp hS₁T₂ hyS₁ hyT₂

/-- A terminal image from `T₁` cannot be a vertex of a blue routing path. -/
theorem not_blue_vertex_of_mem_T₁_terminalImage
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {y : W}
    (hyT₁ :
      y ∈ N.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
    {j : N.blueRouting.Index}
    (hyB : y ∈ (N.blueRouting.path j).vertexSet) :
    False := by
  classical
  have hyTerm : y ∈ N.terminalSet :=
    subset_twoPairTerminalSet_T₁ _ _ _ _ hyT₁
  rcases N.isEndpoint_of_mem_terminalSet_of_mem_path hdeg hyTerm
      (N.blueRouting.path j) hyB with hsrc | htgt
  · have hyS₂ :
        y ∈ N.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
      simpa [hsrc] using N.blueRouting.source_mem j
    have hT₁S₂ := (N.terminalImagesDisjoint hdisj).2.2.2.1
    exact Finset.disjoint_left.mp hT₁S₂ hyT₁ hyS₂
  · have hyT₂ :
        y ∈ N.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
      simpa [htgt] using N.blueRouting.target_mem j
    have hT₁T₂ := (N.terminalImagesDisjoint hdisj).2.2.2.2.1
    exact Finset.disjoint_left.mp hT₁T₂ hyT₁ hyT₂

/-- A terminal image from `S₂` cannot be a vertex of a red routing path. -/
theorem not_red_vertex_of_mem_S₂_terminalImage
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {y : W}
    (hyS₂ :
      y ∈ N.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
    {i : N.redRouting.Index}
    (hyR : y ∈ (N.redRouting.path i).vertexSet) :
    False := by
  classical
  have hyTerm : y ∈ N.terminalSet :=
    subset_twoPairTerminalSet_S₂ _ _ _ _ hyS₂
  rcases N.isEndpoint_of_mem_terminalSet_of_mem_path hdeg hyTerm
      (N.redRouting.path i) hyR with hsrc | htgt
  · have hyS₁ :
        y ∈ N.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
      simpa [hsrc] using N.redRouting.source_mem i
    have hS₁S₂ := (N.terminalImagesDisjoint hdisj).2.1
    exact Finset.disjoint_left.mp hS₁S₂ hyS₁ hyS₂
  · have hyT₁ :
        y ∈ N.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
      simpa [htgt] using N.redRouting.target_mem i
    have hT₁S₂ := (N.terminalImagesDisjoint hdisj).2.2.2.1
    exact Finset.disjoint_left.mp hT₁S₂ hyT₁ hyS₂

/-- A terminal image from `T₂` cannot be a vertex of a red routing path. -/
theorem not_red_vertex_of_mem_T₂_terminalImage
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {y : W}
    (hyT₂ :
      y ∈ N.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))
    {i : N.redRouting.Index}
    (hyR : y ∈ (N.redRouting.path i).vertexSet) :
    False := by
  classical
  have hyTerm : y ∈ N.terminalSet :=
    subset_twoPairTerminalSet_T₂ _ _ _ _ hyT₂
  rcases N.isEndpoint_of_mem_terminalSet_of_mem_path hdeg hyTerm
      (N.redRouting.path i) hyR with hsrc | htgt
  · have hyS₁ :
        y ∈ N.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
      simpa [hsrc] using N.redRouting.source_mem i
    have hS₁T₂ := (N.terminalImagesDisjoint hdisj).2.2.1
    exact Finset.disjoint_left.mp hS₁T₂ hyS₁ hyT₂
  · have hyT₁ :
        y ∈ N.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
      simpa [htgt] using N.redRouting.target_mem i
    have hT₁T₂ := (N.terminalImagesDisjoint hdisj).2.2.2.2.1
    exact Finset.disjoint_left.mp hT₁T₂ hyT₁ hyT₂

/-- A terminal image from `S₁` cannot be a vertex of any blue routing path
between the blue terminal images. -/
theorem not_blue_vertex_of_mem_S₁_terminalImage_of_routing
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (B : PerfectPathPacking H
      (N.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (N.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)))
    {y : W}
    (hyS₁ :
      y ∈ N.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
    {j : B.Index}
    (hyB : y ∈ (B.path j).vertexSet) :
    False := by
  classical
  have hyTerm : y ∈ N.terminalSet :=
    subset_twoPairTerminalSet_S₁ _ _ _ _ hyS₁
  rcases N.isEndpoint_of_mem_terminalSet_of_mem_path hdeg hyTerm
      (B.path j) hyB with hsrc | htgt
  · have hyS₂ :
        y ∈ N.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
      simpa [hsrc] using B.source_mem j
    have hS₁S₂ := (N.terminalImagesDisjoint hdisj).2.1
    exact Finset.disjoint_left.mp hS₁S₂ hyS₁ hyS₂
  · have hyT₂ :
        y ∈ N.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
      simpa [htgt] using B.target_mem j
    have hS₁T₂ := (N.terminalImagesDisjoint hdisj).2.2.1
    exact Finset.disjoint_left.mp hS₁T₂ hyS₁ hyT₂

/-- A terminal image from `T₁` cannot be a vertex of any blue routing path. -/
theorem not_blue_vertex_of_mem_T₁_terminalImage_of_routing
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (B : PerfectPathPacking H
      (N.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (N.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)))
    {y : W}
    (hyT₁ :
      y ∈ N.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
    {j : B.Index}
    (hyB : y ∈ (B.path j).vertexSet) :
    False := by
  classical
  have hyTerm : y ∈ N.terminalSet :=
    subset_twoPairTerminalSet_T₁ _ _ _ _ hyT₁
  rcases N.isEndpoint_of_mem_terminalSet_of_mem_path hdeg hyTerm
      (B.path j) hyB with hsrc | htgt
  · have hyS₂ :
        y ∈ N.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
      simpa [hsrc] using B.source_mem j
    have hT₁S₂ := (N.terminalImagesDisjoint hdisj).2.2.2.1
    exact Finset.disjoint_left.mp hT₁S₂ hyT₁ hyS₂
  · have hyT₂ :
        y ∈ N.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
      simpa [htgt] using B.target_mem j
    have hT₁T₂ := (N.terminalImagesDisjoint hdisj).2.2.2.2.1
    exact Finset.disjoint_left.mp hT₁T₂ hyT₁ hyT₂

/-- A terminal image from `S₂` cannot be a vertex of any red routing path. -/
theorem not_red_vertex_of_mem_S₂_terminalImage_of_routing
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (R : PerfectPathPacking H
      (N.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (N.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)))
    {y : W}
    (hyS₂ :
      y ∈ N.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
    {i : R.Index}
    (hyR : y ∈ (R.path i).vertexSet) :
    False := by
  classical
  have hyTerm : y ∈ N.terminalSet :=
    subset_twoPairTerminalSet_S₂ _ _ _ _ hyS₂
  rcases N.isEndpoint_of_mem_terminalSet_of_mem_path hdeg hyTerm
      (R.path i) hyR with hsrc | htgt
  · have hyS₁ :
        y ∈ N.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
      simpa [hsrc] using R.source_mem i
    have hS₁S₂ := (N.terminalImagesDisjoint hdisj).2.1
    exact Finset.disjoint_left.mp hS₁S₂ hyS₁ hyS₂
  · have hyT₁ :
        y ∈ N.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
      simpa [htgt] using R.target_mem i
    have hT₁S₂ := (N.terminalImagesDisjoint hdisj).2.2.2.1
    exact Finset.disjoint_left.mp hT₁S₂ hyT₁ hyS₂

/-- A terminal image from `T₂` cannot be a vertex of any red routing path. -/
theorem not_red_vertex_of_mem_T₂_terminalImage_of_routing
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (R : PerfectPathPacking H
      (N.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (N.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)))
    {y : W}
    (hyT₂ :
      y ∈ N.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))
    {i : R.Index}
    (hyR : y ∈ (R.path i).vertexSet) :
    False := by
  classical
  have hyTerm : y ∈ N.terminalSet :=
    subset_twoPairTerminalSet_T₂ _ _ _ _ hyT₂
  rcases N.isEndpoint_of_mem_terminalSet_of_mem_path hdeg hyTerm
      (R.path i) hyR with hsrc | htgt
  · have hyS₁ :
        y ∈ N.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
      simpa [hsrc] using R.source_mem i
    have hS₁T₂ := (N.terminalImagesDisjoint hdisj).2.2.1
    exact Finset.disjoint_left.mp hS₁T₂ hyS₁ hyT₂
  · have hyT₁ :
        y ∈ N.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
      simpa [htgt] using R.target_mem i
    have hT₁T₂ := (N.terminalImagesDisjoint hdisj).2.2.2.2.1
    exact Finset.disjoint_left.mp hT₁T₂ hyT₁ hyT₂

/-- A red edge and a blue edge cannot coincide at a terminal vertex under the
paper's Theorem 2.1 terminal hypotheses. -/
theorem false_of_red_and_blue_edge_incident_terminal
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {v y : W}
    (hy : y ∈ N.terminalSet)
    (hred : s(v, y) ∈ N.redRouting.toPathPacking.edgeSet)
    (hblue : s(v, y) ∈ N.blueRouting.toPathPacking.edgeSet) :
    False := by
  classical
  rcases (N.redRouting.toPathPacking.mem_edgeSet).1 hred with ⟨i, hri⟩
  rcases (N.blueRouting.toPathPacking.mem_edgeSet).1 hblue with ⟨j, hbj⟩
  have hyR : y ∈ (N.redRouting.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (N.redRouting.path i) hri).2
  have hyB : y ∈ (N.blueRouting.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (N.blueRouting.path j) hbj).2
  simp [terminalSet, twoPairTerminalSet] at hy
  rcases hy with hyS₁ | hyT₁ | hyS₂ | hyT₂
  · exact N.not_blue_vertex_of_mem_S₁_terminalImage hdeg hdisj hyS₁ hyB
  · exact N.not_blue_vertex_of_mem_T₁_terminalImage hdeg hdisj hyT₁ hyB
  · exact N.not_red_vertex_of_mem_S₂_terminalImage hdeg hdisj hyS₂ hyR
  · exact N.not_red_vertex_of_mem_T₂_terminalImage hdeg hdisj hyT₂ hyR

/-- An arbitrary red routing and the selected blue routing cannot share an
edge incident with a terminal vertex under the paper's terminal hypotheses. -/
theorem false_of_redRouting_and_blue_edge_incident_terminal
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (R : PerfectPathPacking H
      (N.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (N.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)))
    {v y : W}
    (hy : y ∈ N.terminalSet)
    (hred : s(v, y) ∈ R.toPathPacking.edgeSet)
    (hblue : s(v, y) ∈ N.blueRouting.toPathPacking.edgeSet) :
    False := by
  classical
  rcases (R.toPathPacking.mem_edgeSet).1 hred with ⟨i, hri⟩
  rcases (N.blueRouting.toPathPacking.mem_edgeSet).1 hblue with ⟨j, hbj⟩
  have hyR : y ∈ (R.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (R.path i) hri).2
  have hyB : y ∈ (N.blueRouting.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (N.blueRouting.path j) hbj).2
  simp [terminalSet, twoPairTerminalSet] at hy
  rcases hy with hyS₁ | hyT₁ | hyS₂ | hyT₂
  · exact N.not_blue_vertex_of_mem_S₁_terminalImage hdeg hdisj hyS₁ hyB
  · exact N.not_blue_vertex_of_mem_T₁_terminalImage hdeg hdisj hyT₁ hyB
  · exact N.not_red_vertex_of_mem_S₂_terminalImage_of_routing
      hdeg hdisj R hyS₂ hyR
  · exact N.not_red_vertex_of_mem_T₂_terminalImage_of_routing
      hdeg hdisj R hyT₂ hyR

/-- The selected red routing and an arbitrary blue routing cannot share an
edge incident with a terminal vertex under the paper's terminal hypotheses. -/
theorem false_of_red_edge_and_blueRouting_incident_terminal
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (B : PerfectPathPacking H
      (N.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (N.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)))
    {v y : W}
    (hy : y ∈ N.terminalSet)
    (hred : s(v, y) ∈ N.redRouting.toPathPacking.edgeSet)
    (hblue : s(v, y) ∈ B.toPathPacking.edgeSet) :
    False := by
  classical
  rcases (N.redRouting.toPathPacking.mem_edgeSet).1 hred with ⟨i, hri⟩
  rcases (B.toPathPacking.mem_edgeSet).1 hblue with ⟨j, hbj⟩
  have hyR : y ∈ (N.redRouting.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (N.redRouting.path i) hri).2
  have hyB : y ∈ (B.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (B.path j) hbj).2
  simp [terminalSet, twoPairTerminalSet] at hy
  rcases hy with hyS₁ | hyT₁ | hyS₂ | hyT₂
  · exact N.not_blue_vertex_of_mem_S₁_terminalImage_of_routing
      hdeg hdisj B hyS₁ hyB
  · exact N.not_blue_vertex_of_mem_T₁_terminalImage_of_routing
      hdeg hdisj B hyT₁ hyB
  · exact N.not_red_vertex_of_mem_S₂_terminalImage hdeg hdisj hyS₂ hyR
  · exact N.not_red_vertex_of_mem_T₂_terminalImage hdeg hdisj hyT₂ hyR

/-- The original graph is a good minor of itself whenever the two terminal
pairs are routed in it. -/
noncomputable def ofRoutings
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) :
    TwoPairGoodMinor G G S₁ T₁ S₂ T₂ where
  respecting :=
    XRespectingMinorModel.refl G (twoPairTerminalSet S₁ T₁ S₂ T₂)
  redRouting := by
    refine P.copyTerminals ?_ ?_
    · rw [XRespectingMinorModel.refl_terminalImage]
    · rw [XRespectingMinorModel.refl_terminalImage]
  blueRouting := by
    refine Q.copyTerminals ?_ ?_
    · rw [XRespectingMinorModel.refl_terminalImage]
    · rw [XRespectingMinorModel.refl_terminalImage]

/-- Reverse the first routing pair in a good minor. -/
noncomputable def reverseRed
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    TwoPairGoodMinor G H T₁ S₁ S₂ T₂ := by
  classical
  let R :=
    N.respecting.copyTerminalSet
      (twoPairTerminalSet_swap_first S₁ T₁ S₂ T₂).symm
  refine
    { respecting := R
      redRouting := ?_
      blueRouting := ?_ }
  · refine N.redRouting.reverse.copyTerminals ?_ ?_
    · simp [R]
    · simp [R]
  · refine N.blueRouting.copyTerminals ?_ ?_
    · simp [R]
    · simp [R]

@[simp] theorem reverseRed_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    N.reverseRed.terminalSet = N.terminalSet := by
  classical
  rw [terminalSet, terminalSet]
  simp [reverseRed, twoPairTerminalSet_swap_first]

end TwoPairGoodMinor

/-! ## Single-edge contraction -/

/-- Vertices of the graph obtained by contracting the edge `u -- v`.

The vertex `merged` represents the contracted edge, and `keep x` represents an
original vertex different from both endpoints of the contracted edge. -/
inductive EdgeContractVertex (V : Type u) (u v : V) where
  | merged : EdgeContractVertex V u v
  | keep : {x : V // x ≠ u ∧ x ≠ v} → EdgeContractVertex V u v
deriving DecidableEq

namespace EdgeContractVertex

variable {u v : V}

noncomputable instance instFintype [Fintype V] :
    Fintype (EdgeContractVertex V u v) := by
  classical
  refine
    Fintype.ofEquiv (Unit ⊕ {x : V // x ≠ u ∧ x ≠ v}) ?_
  refine
    { toFun := fun z =>
        match z with
        | Sum.inl _ => merged
        | Sum.inr x => keep x
      invFun := fun x =>
        match x with
        | merged => Sum.inl ()
        | keep z => Sum.inr z
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    cases z with
    | inl z => cases z <;> rfl
    | inr z => rfl
  · intro x
    cases x <;> rfl

/-- The branch set represented by one vertex after contracting `u -- v`. -/
noncomputable def branchSet (x : EdgeContractVertex V u v) : Finset V :=
  match x with
  | merged => {u, v}
  | keep z => {z.1}

@[simp] theorem branchSet_merged :
    branchSet (V := V) (u := u) (v := v) merged = ({u, v} : Finset V) :=
  rfl

@[simp] theorem branchSet_keep (z : {x : V // x ≠ u ∧ x ≠ v}) :
    branchSet (keep z : EdgeContractVertex V u v) = ({z.1} : Finset V) :=
  rfl

/-- The canonical vertex representing an original non-endpoint vertex. -/
def ofVertex (x : V) (hx : x ≠ u ∧ x ≠ v) :
    EdgeContractVertex V u v :=
  keep ⟨x, hx⟩

/-- Project an original vertex to the graph where `u -- v` is contracted. -/
noncomputable def projection (x : V) : EdgeContractVertex V u v :=
  if hx : x = u ∨ x = v then
    merged
  else
    ofVertex x ⟨fun hxu => hx (Or.inl hxu), fun hxv => hx (Or.inr hxv)⟩

@[simp] theorem projection_eq_merged_of_eq_left :
    projection (V := V) (u := u) (v := v) u = merged := by
  simp [projection]

@[simp] theorem projection_eq_merged_of_eq_right :
    projection (V := V) (u := u) (v := v) v = merged := by
  simp [projection]

theorem projection_eq_of_ne {x : V} (hxu : x ≠ u) (hxv : x ≠ v) :
    projection (V := V) (u := u) (v := v) x =
      ofVertex (V := V) (u := u) (v := v) x ⟨hxu, hxv⟩ := by
  simp [projection, hxu, hxv]

@[simp] theorem projection_eq_merged_iff {x : V} :
    projection (V := V) (u := u) (v := v) x = merged ↔
      x = u ∨ x = v := by
  by_cases hx : x = u ∨ x = v
  · simp [projection, hx]
  · constructor
    · intro h
      have hkeep :
          ofVertex (V := V) (u := u) (v := v) x
              ⟨fun hxu => hx (Or.inl hxu), fun hxv => hx (Or.inr hxv)⟩ =
            merged := by
        simpa [projection, hx] using h
      cases hkeep
    · intro hx'
      exact (hx hx').elim

/-- Equality after edge-contraction projection either comes from equality
before projection, or from both original vertices being endpoints of the
contracted edge. -/
theorem eq_or_endpoint_pair_of_projection_eq {x y : V}
    (h :
      projection (V := V) (u := u) (v := v) x =
        projection (V := V) (u := u) (v := v) y) :
    x = y ∨ (x = u ∨ x = v) ∧ (y = u ∨ y = v) := by
  by_cases hx : x = u ∨ x = v
  · exact Or.inr ⟨hx, by
      rw [← projection_eq_merged_iff (V := V) (u := u) (v := v)]
      simpa [projection, hx] using h.symm⟩
  · by_cases hy : y = u ∨ y = v
    · have hxmerged :
          projection (V := V) (u := u) (v := v) x = merged := by
        simpa [projection, hy] using h
      exact False.elim (hx
        ((projection_eq_merged_iff (V := V) (u := u) (v := v)).1 hxmerged))
    · left
      have hkeep :
          ofVertex (V := V) (u := u) (v := v) x
              ⟨fun hxu => hx (Or.inl hxu), fun hxv => hx (Or.inr hxv)⟩ =
            ofVertex (V := V) (u := u) (v := v) y
              ⟨fun hyu => hy (Or.inl hyu), fun hyv => hy (Or.inr hyv)⟩ := by
        simpa [projection, hx, hy] using h
      injection hkeep with hsub
      exact congrArg Subtype.val hsub

@[simp] theorem mem_branchSet_ofVertex
    (x : V) (hx : x ≠ u ∧ x ≠ v) :
    x ∈ branchSet (ofVertex (V := V) (u := u) (v := v) x hx) := by
  simp [ofVertex]

/-- Projection sends a vertex to a contracted vertex whose branch set contains
the original vertex. -/
theorem mem_branchSet_projection (x : V) :
    x ∈ branchSet (projection (V := V) (u := u) (v := v) x) := by
  by_cases hx : x = u ∨ x = v
  · rcases hx with rfl | rfl
    · simp
    · simp
  · simp [projection, hx, ofVertex]

@[simp] theorem mem_branchSet_merged_left :
    u ∈ branchSet (V := V) (u := u) (v := v) merged := by
  simp

@[simp] theorem mem_branchSet_merged_right :
    v ∈ branchSet (V := V) (u := u) (v := v) merged := by
  simp

/-- Every contracted-edge vertex has a nonempty branch set. -/
theorem branchSet_nonempty (x : EdgeContractVertex V u v) :
    (branchSet x).Nonempty := by
  cases x with
  | merged =>
      exact ⟨u, by simp⟩
  | keep z =>
      exact ⟨z.1, by simp⟩

/-- Distinct contracted-edge vertices have disjoint branch sets. -/
theorem branchSet_disjoint {x y : EdgeContractVertex V u v}
    (hxy : x ≠ y) :
    Disjoint (branchSet x) (branchSet y) := by
  classical
  cases x with
  | merged =>
      cases y with
      | merged => exact (hxy rfl).elim
      | keep z =>
          rw [Finset.disjoint_left]
          intro a ha hb
          have haz : a = z.1 := by simpa using hb
          have hauv : a = u ∨ a = v := by simpa using ha
          rcases hauv with rfl | rfl
          · exact z.2.1 haz.symm
          · exact z.2.2 haz.symm
  | keep z =>
      cases y with
      | merged =>
          rw [Finset.disjoint_left]
          intro a ha hb
          have haz : a = z.1 := by simpa using ha
          have hauv : a = u ∨ a = v := by simpa using hb
          rcases hauv with rfl | rfl
          · exact z.2.1 haz.symm
          · exact z.2.2 haz.symm
      | keep w =>
          rw [Finset.disjoint_left]
          intro a ha hb
          have haz : a = z.1 := by simpa using ha
          have haw : a = w.1 := by simpa using hb
          apply hxy
          apply congrArg keep
          exact Subtype.ext (haz.symm.trans haw)

/-- A representative original vertex for each contracted vertex.  The merged
vertex is represented by the left endpoint. -/
def representative (x : EdgeContractVertex V u v) : V :=
  match x with
  | merged => u
  | keep z => z.1

theorem representative_injective (huv : u ≠ v) :
    Function.Injective (representative (V := V) (u := u) (v := v)) := by
  intro x y hxy
  cases x with
  | merged =>
      cases y with
      | merged => rfl
      | keep z =>
          exfalso
          exact z.2.1 hxy.symm
  | keep z =>
      cases y with
      | merged =>
          exfalso
          exact z.2.1 hxy
      | keep w =>
          apply congrArg keep
          exact Subtype.ext hxy

theorem representative_not_surjective (huv : u ≠ v) :
    ¬ Function.Surjective
      (representative (V := V) (u := u) (v := v)) := by
  intro hsurj
  rcases hsurj v with ⟨x, hx⟩
  cases x with
  | merged =>
      exact huv hx
  | keep z =>
      exact z.2.2 hx

theorem card_lt_of_ne [Fintype V] (huv : u ≠ v) :
    Fintype.card (EdgeContractVertex V u v) < Fintype.card V :=
  Fintype.card_lt_of_injective_not_surjective
    (representative (V := V) (u := u) (v := v))
    (representative_injective (V := V) (u := u) (v := v) huv)
    (representative_not_surjective (V := V) (u := u) (v := v) huv)

end EdgeContractVertex

/-- The simple graph obtained from `G` by contracting the edge `u -- v`.

Two contracted vertices are adjacent when some original edge runs between their
branch sets.  Loops created by the contraction are discarded. -/
noncomputable def contractEdgeGraph
    (G : _root_.SimpleGraph V) {u v : V} (_huv : G.Adj u v) :
    _root_.SimpleGraph (EdgeContractVertex V u v) where
  Adj x y :=
    x ≠ y ∧
      ∃ a ∈ EdgeContractVertex.branchSet x,
        ∃ b ∈ EdgeContractVertex.branchSet y, G.Adj a b
  symm := by
    intro x y hxy
    rcases hxy with ⟨hne, a, ha, b, hb, hab⟩
    exact ⟨hne.symm, b, hb, a, ha, G.symm hab⟩
  loopless := ⟨by
    intro x hxx
    exact hxx.1 rfl⟩

namespace contractEdgeGraph

variable {G : _root_.SimpleGraph V} {u v : V} {huv : G.Adj u v}

@[simp] theorem adj_iff (x y : EdgeContractVertex V u v) :
    (contractEdgeGraph G huv).Adj x y ↔
      x ≠ y ∧
        ∃ a ∈ EdgeContractVertex.branchSet x,
          ∃ b ∈ EdgeContractVertex.branchSet y, G.Adj a b :=
  Iff.rfl

/-- An original edge whose endpoints project to distinct contracted vertices
gives an edge in the contracted graph. -/
theorem projection_adj_of_adj_of_ne {x y : V}
    (hxy : G.Adj x y)
    (hne :
      EdgeContractVertex.projection (V := V) (u := u) (v := v) x ≠
        EdgeContractVertex.projection (V := V) (u := u) (v := v) y) :
    (contractEdgeGraph G huv).Adj
      (EdgeContractVertex.projection (V := V) (u := u) (v := v) x)
      (EdgeContractVertex.projection (V := V) (u := u) (v := v) y) := by
  exact ⟨hne, x,
    EdgeContractVertex.mem_branchSet_projection (V := V) (u := u) (v := v) x,
    y,
    EdgeContractVertex.mem_branchSet_projection (V := V) (u := u) (v := v) y,
    hxy⟩

namespace ProjectionWalk

/-- Project a walk to the contracted-edge graph, suppressing steps whose
endpoints are identified by the contraction. -/
noncomputable def ofWalk : {x y : V} → (W : G.Walk x y) →
    (contractEdgeGraph G huv).Walk
      (EdgeContractVertex.projection (V := V) (u := u) (v := v) x)
      (EdgeContractVertex.projection (V := V) (u := u) (v := v) y)
  | x, _, _root_.SimpleGraph.Walk.nil' _ =>
      _root_.SimpleGraph.Walk.nil
  | x, z, _root_.SimpleGraph.Walk.cons' _ y _ h W => by
      let ih := ofWalk W
      by_cases hsame :
        EdgeContractVertex.projection (V := V) (u := u) (v := v) x =
          EdgeContractVertex.projection (V := V) (u := u) (v := v) y
      · exact ih.copy hsame.symm rfl
      · exact _root_.SimpleGraph.Walk.cons
          (projection_adj_of_adj_of_ne (G := G) (huv := huv) h hsame) ih

/-- Every vertex of a projected walk is the projection of some vertex of the
original walk. -/
theorem support_subset_projection : {x y : V} → (W : G.Walk x y) →
    ∀ z ∈ (ofWalk (G := G) (huv := huv) W).support,
      ∃ a ∈ W.support,
        EdgeContractVertex.projection (V := V) (u := u) (v := v) a = z
  | x, _, _root_.SimpleGraph.Walk.nil' _ => by
      intro z hz
      have hz' :
          z = EdgeContractVertex.projection (V := V) (u := u) (v := v) x := by
        simpa [ofWalk] using hz
      exact ⟨x, by simp, hz'.symm⟩
  | x, _, _root_.SimpleGraph.Walk.cons' _ y _ h W => by
      intro z hz
      by_cases hsame :
        EdgeContractVertex.projection (V := V) (u := u) (v := v) x =
          EdgeContractVertex.projection (V := V) (u := u) (v := v) y
      · have hzTail : z ∈ (ofWalk (G := G) (huv := huv) W).support := by
          simpa [ofWalk, hsame] using hz
        rcases support_subset_projection W z hzTail with
          ⟨a, ha, haz⟩
        exact ⟨a, by simp [ha], haz⟩
      · have hzCons :
            z = EdgeContractVertex.projection (V := V) (u := u) (v := v) x ∨
              z ∈ (ofWalk (G := G) (huv := huv) W).support := by
          simpa [ofWalk, hsame, _root_.SimpleGraph.Walk.support_cons] using hz
        rcases hzCons with hzHead | hzTail
        · exact ⟨x, by simp, hzHead.symm⟩
        · rcases support_subset_projection W z hzTail with
            ⟨a, ha, haz⟩
          exact ⟨a, by simp [ha], haz⟩

/-- Turn a projected walk into a simple graph path. -/
noncomputable def toGraphPath (R : GraphPath G) :
    GraphPath (contractEdgeGraph G huv) where
  source := EdgeContractVertex.projection (V := V) (u := u) (v := v) R.source
  target := EdgeContractVertex.projection (V := V) (u := u) (v := v) R.target
  walk := (ofWalk (G := G) (huv := huv) R.walk).toPath.val
  isPath := (ofWalk (G := G) (huv := huv) R.walk).toPath.property

/-- Vertices of the projected graph path come from projecting vertices of the
original path. -/
theorem toGraphPath_vertexSet_subset_projection (R : GraphPath G) :
    ∀ z ∈ (toGraphPath (G := G) (huv := huv) R).vertexSet,
      ∃ a ∈ R.vertexSet,
        EdgeContractVertex.projection (V := V) (u := u) (v := v) a = z := by
  classical
  intro z hz
  have hzSupport :
      z ∈ ((ofWalk (G := G) (huv := huv) R.walk).toPath :
        (contractEdgeGraph G huv).Walk
          (EdgeContractVertex.projection (V := V) (u := u) (v := v) R.source)
          (EdgeContractVertex.projection (V := V) (u := u) (v := v) R.target)).support := by
    simpa [toGraphPath, GraphPath.vertexSet] using hz
  have hzWalk :
      z ∈ (ofWalk (G := G) (huv := huv) R.walk).support :=
    _root_.SimpleGraph.Walk.support_toPath_subset
      (ofWalk (G := G) (huv := huv) R.walk) hzSupport
  rcases support_subset_projection (G := G) (huv := huv) R.walk z hzWalk with
    ⟨a, ha, haz⟩
  exact ⟨a, by simpa [GraphPath.vertexSet] using ha, haz⟩

end ProjectionWalk

/-- Branch sets of vertices in the contracted-edge graph are connected in the
original graph. -/
theorem branch_connected (huv : G.Adj u v) (x : EdgeContractVertex V u v) :
    (G.induce {a : V | a ∈ EdgeContractVertex.branchSet x}).Connected := by
  classical
  cases x with
  | merged =>
      have hset :
          {a : V | a ∈ ({u, v} : Finset V)} = ({u, v} : Set V) := by
        ext a
        simp
      rw [EdgeContractVertex.branchSet_merged, hset]
      exact _root_.SimpleGraph.induce_pair_connected_of_adj (G := G) huv
  | keep z =>
      simpa [EdgeContractVertex.branchSet] using
        GraphPath.connected_induce_vertexSet (GraphPath.refl G z.1)

/-- The canonical branch-set model witnessing an edge contraction as a minor. -/
noncomputable def minorModel :
    MinorModel (contractEdgeGraph G huv) G where
  branchSet := EdgeContractVertex.branchSet
  branch_nonempty := EdgeContractVertex.branchSet_nonempty
  branch_connected := branch_connected (G := G) huv
  branch_disjoint := by
    intro x y hxy
    exact EdgeContractVertex.branchSet_disjoint hxy
  adjacent := by
    intro x y hxy
    exact hxy.2

/-- Contracting an edge produces a minor of the original graph. -/
theorem isMinor :
    IsMinor (contractEdgeGraph G huv) G := by
  exact ⟨minorModel (G := G) (huv := huv)⟩

end contractEdgeGraph

/-- Image of a finite vertex set under the edge-contraction projection. -/
noncomputable def edgeContractImageSet
    {W : Type w} [DecidableEq W] {a b : W}
    (A : Finset W) : Finset (EdgeContractVertex W a b) :=
  A.attach.image fun x =>
    EdgeContractVertex.projection (V := W) (u := a) (v := b) x.1

@[simp] theorem mem_edgeContractImageSet_projection
    {W : Type w} [DecidableEq W] {a b : W}
    {A : Finset W} {x : W} (hx : x ∈ A) :
    EdgeContractVertex.projection (V := W) (u := a) (v := b) x ∈
      edgeContractImageSet (a := a) (b := b) A := by
  classical
  exact Finset.mem_image.mpr ⟨⟨x, hx⟩, by simp, rfl⟩

/-- Project a perfect path packing through an edge contraction, assuming the
contracted edge lies on one of the paths and neither endpoint is a terminal of
the packing. -/
noncomputable def perfectPathPacking_contractEdge
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PerfectPathPacking H A B)
    {a b : W} (hab : H.Adj a b)
    (i₀ : P.Index)
    (ha : a ∈ (P.path i₀).vertexSet)
    (hb : b ∈ (P.path i₀).vertexSet)
    (hAavoid : ∀ x ∈ A, x ≠ a ∧ x ≠ b)
    (hBavoid : ∀ x ∈ B, x ≠ a ∧ x ≠ b) :
    PerfectPathPacking (contractEdgeGraph H hab)
      (edgeContractImageSet (a := a) (b := b) A)
      (edgeContractImageSet (a := a) (b := b) B) where
  toPathPacking := {
    Index := P.Index
    path := fun i =>
      contractEdgeGraph.ProjectionWalk.toGraphPath (G := H) (huv := hab) (P.path i)
    connects := by
      intro i
      rcases P.toPathPacking.connects i with h | h
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
      rcases contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := H) (huv := hab) (P.path i) z hzi with
        ⟨x, hx, hxz⟩
      rcases contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := H) (huv := hab) (P.path j) z hzj with
        ⟨y, hy, hyz⟩
      have hproj :
          EdgeContractVertex.projection (V := W) (u := a) (v := b) x =
            EdgeContractVertex.projection (V := W) (u := a) (v := b) y :=
        hxz.trans hyz.symm
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := W) (u := a) (v := b) hproj with hxy | hend
      · subst y
        exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hx hy
      · have hx_on_i₀ : x ∈ (P.path i₀).vertexSet := by
          rcases hend.1 with rfl | rfl
          · exact ha
          · exact hb
        have hy_on_i₀ : y ∈ (P.path i₀).vertexSet := by
          rcases hend.2 with rfl | rfl
          · exact ha
          · exact hb
        have hi : i = i₀ := by
          by_contra hne
          exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hne)
            hx hx_on_i₀
        have hj : j = i₀ := by
          by_contra hne
          exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hne)
            hy hy_on_i₀
        exact hij (hi.trans hj.symm)
  }
  source_mem := by
    intro i
    exact mem_edgeContractImageSet_projection (a := a) (b := b) (P.source_mem i)
  target_mem := by
    intro i
    exact mem_edgeContractImageSet_projection (a := a) (b := b) (P.target_mem i)
  source_bijective := by
    constructor
    · intro i j hij_proj
      apply P.source_bijective.1
      have hproj :
          EdgeContractVertex.projection (V := W) (u := a) (v := b)
              (P.path i).source =
            EdgeContractVertex.projection (V := W) (u := a) (v := b)
              (P.path j).source := by
        exact congrArg Subtype.val hij_proj
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := W) (u := a) (v := b) hproj with hsrc | hend
      · exact Subtype.ext hsrc
      · exfalso
        have havoid := hAavoid (P.path i).source (P.source_mem i)
        rcases hend.1 with hleft | hright
        · exact havoid.1 hleft
        · exact havoid.2 hright
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.source_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have hsource : (P.path i).source = y.1 := congrArg Subtype.val hi
      simpa [contractEdgeGraph.ProjectionWalk.toGraphPath, hsource] using hyx
  target_bijective := by
    constructor
    · intro i j hij_proj
      apply P.target_bijective.1
      have hproj :
          EdgeContractVertex.projection (V := W) (u := a) (v := b)
              (P.path i).target =
            EdgeContractVertex.projection (V := W) (u := a) (v := b)
              (P.path j).target := by
        exact congrArg Subtype.val hij_proj
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := W) (u := a) (v := b) hproj with htgt | hend
      · exact Subtype.ext htgt
      · exfalso
        have havoid := hBavoid (P.path i).target (P.target_mem i)
        rcases hend.1 with hleft | hright
        · exact havoid.1 hleft
        · exact havoid.2 hright
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.target_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have htarget : (P.path i).target = y.1 := congrArg Subtype.val hi
      simpa [contractEdgeGraph.ProjectionWalk.toGraphPath, htarget] using hyx

/-- Project a perfect path packing through an edge contraction when one
endpoint of the contracted edge is unused by the packing.

This is the complementary contraction tool to `perfectPathPacking_contractEdge`:
the contracted edge need not lie on one of the paths of `P`.  The hypothesis
that `a` is unused ensures that projection cannot identify vertices from two
different paths; the other endpoint `b` may lie on one path of the packing. -/
noncomputable def perfectPathPacking_contractEdge_of_left_not_mem_vertexSet
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PerfectPathPacking H A B)
    {a b : W} (hab : H.Adj a b)
    (ha_unused : a ∉ P.toPathPacking.vertexSet)
    (hAavoid : ∀ x ∈ A, x ≠ a ∧ x ≠ b)
    (hBavoid : ∀ x ∈ B, x ≠ a ∧ x ≠ b) :
    PerfectPathPacking (contractEdgeGraph H hab)
      (edgeContractImageSet (a := a) (b := b) A)
      (edgeContractImageSet (a := a) (b := b) B) where
  toPathPacking := {
    Index := P.Index
    path := fun i =>
      contractEdgeGraph.ProjectionWalk.toGraphPath (G := H) (huv := hab) (P.path i)
    connects := by
      intro i
      rcases P.toPathPacking.connects i with h | h
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
      rcases contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := H) (huv := hab) (P.path i) z hzi with
        ⟨x, hx, hxz⟩
      rcases contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
          (G := H) (huv := hab) (P.path j) z hzj with
        ⟨y, hy, hyz⟩
      have hproj :
          EdgeContractVertex.projection (V := W) (u := a) (v := b) x =
            EdgeContractVertex.projection (V := W) (u := a) (v := b) y :=
        hxz.trans hyz.symm
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := W) (u := a) (v := b) hproj with hxy | hend
      · subst y
        exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hx hy
      · have hx_ne_a : x ≠ a := by
          intro hxa
          exact ha_unused ((P.toPathPacking.mem_vertexSet).2 ⟨i, by simpa [hxa] using hx⟩)
        have hy_ne_a : y ≠ a := by
          intro hya
          exact ha_unused ((P.toPathPacking.mem_vertexSet).2 ⟨j, by simpa [hya] using hy⟩)
        have hx_eq_b : x = b := by
          rcases hend.1 with hxa | hxb
          · exact False.elim (hx_ne_a hxa)
          · exact hxb
        have hy_eq_b : y = b := by
          rcases hend.2 with hya | hyb
          · exact False.elim (hy_ne_a hya)
          · exact hyb
        subst x
        subst y
        exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hx hy
  }
  source_mem := by
    intro i
    exact mem_edgeContractImageSet_projection (a := a) (b := b) (P.source_mem i)
  target_mem := by
    intro i
    exact mem_edgeContractImageSet_projection (a := a) (b := b) (P.target_mem i)
  source_bijective := by
    constructor
    · intro i j hij_proj
      apply P.source_bijective.1
      have hproj :
          EdgeContractVertex.projection (V := W) (u := a) (v := b)
              (P.path i).source =
            EdgeContractVertex.projection (V := W) (u := a) (v := b)
              (P.path j).source := by
        exact congrArg Subtype.val hij_proj
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := W) (u := a) (v := b) hproj with hsrc | hend
      · exact Subtype.ext hsrc
      · exfalso
        have havoid := hAavoid (P.path i).source (P.source_mem i)
        rcases hend.1 with hleft | hright
        · exact havoid.1 hleft
        · exact havoid.2 hright
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.source_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have hsource : (P.path i).source = y.1 := congrArg Subtype.val hi
      simpa [contractEdgeGraph.ProjectionWalk.toGraphPath, hsource] using hyx
  target_bijective := by
    constructor
    · intro i j hij_proj
      apply P.target_bijective.1
      have hproj :
          EdgeContractVertex.projection (V := W) (u := a) (v := b)
              (P.path i).target =
            EdgeContractVertex.projection (V := W) (u := a) (v := b)
              (P.path j).target := by
        exact congrArg Subtype.val hij_proj
      rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := W) (u := a) (v := b) hproj with htgt | hend
      · exact Subtype.ext htgt
      · exfalso
        have havoid := hBavoid (P.path i).target (P.target_mem i)
        rcases hend.1 with hleft | hright
        · exact havoid.1 hleft
        · exact havoid.2 hright
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨y, _hy, hyx⟩
      rcases P.target_bijective.2 ⟨y.1, y.2⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have htarget : (P.path i).target = y.1 := congrArg Subtype.val hi
      simpa [contractEdgeGraph.ProjectionWalk.toGraphPath, htarget] using hyx

namespace XRespectingMinorModel

variable {W : Type w} [DecidableEq W]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
variable {X : Finset V}

/-- Deleting edges from the minor graph preserves an `X`-respecting model, as
long as any needed routings remain in the deleted graph. -/
noncomputable def deleteEdges
    (M : XRespectingMinorModel H G X) (E : Set (Sym2 W)) :
    XRespectingMinorModel (H.deleteEdges E) G X where
  model := {
    branchSet := M.model.branchSet
    branch_nonempty := M.model.branch_nonempty
    branch_connected := M.model.branch_connected
    branch_disjoint := M.model.branch_disjoint
    adjacent := by
      intro a b hab
      exact M.model.adjacent ((_root_.SimpleGraph.deleteEdges_adj.mp hab).1)
  }
  terminalVertex := M.terminalVertex
  terminal_injective := M.terminal_injective
  terminal_branchSet := M.terminal_branchSet

/-- Contracting an edge whose endpoints are not terminal representatives
preserves the `X`-respecting part of the minor model. -/
noncomputable def contractNonterminalEdge
    (M : XRespectingMinorModel H G X)
    {a b : W} (hab : H.Adj a b)
    (havoid :
      ∀ x : V, ∀ hx : x ∈ X,
        M.terminalVertex x hx ≠ a ∧ M.terminalVertex x hx ≠ b) :
    XRespectingMinorModel (contractEdgeGraph H hab) G X where
  model := (contractEdgeGraph.minorModel (G := H) (huv := hab)).trans M.model
  terminalVertex := fun x hx =>
    EdgeContractVertex.ofVertex (M.terminalVertex x hx) (havoid x hx)
  terminal_injective := by
    intro x y hx hy hxy
    apply M.terminal_injective hx hy
    have hval :
        (fun z : EdgeContractVertex W a b =>
          match z with
          | EdgeContractVertex.merged => a
          | EdgeContractVertex.keep z => z.1)
            (EdgeContractVertex.ofVertex (M.terminalVertex x hx) (havoid x hx))
          =
        (fun z : EdgeContractVertex W a b =>
          match z with
          | EdgeContractVertex.merged => a
          | EdgeContractVertex.keep z => z.1)
            (EdgeContractVertex.ofVertex (M.terminalVertex y hy) (havoid y hy)) :=
      congrArg
        (fun z : EdgeContractVertex W a b =>
          match z with
          | EdgeContractVertex.merged => a
          | EdgeContractVertex.keep z => z.1)
        hxy
    simpa [EdgeContractVertex.ofVertex] using hval
  terminal_branchSet := by
    intro x hx
    ext y
    change
      y ∈ MinorModel.composeBranchSet
        (contractEdgeGraph.minorModel (G := H) (huv := hab)) M.model
        (EdgeContractVertex.ofVertex (M.terminalVertex x hx) (havoid x hx)) ↔
      y ∈ ({x} : Finset V)
    rw [MinorModel.mem_composeBranchSet]
    constructor
    · rintro ⟨z, hz, hyz⟩
      have hz_eq : z = M.terminalVertex x hx := by
        simpa [contractEdgeGraph.minorModel, EdgeContractVertex.ofVertex] using hz
      subst z
      simpa [M.terminal_branchSet x hx] using hyz
    · intro hy
      refine ⟨M.terminalVertex x hx, ?_, ?_⟩
      · simp [contractEdgeGraph.minorModel, EdgeContractVertex.ofVertex]
      · simpa [M.terminal_branchSet x hx] using hy

omit [DecidableEq V] in
/-- The terminal images of a contracted `X`-respecting model are exactly the
edge-contraction projections of the old terminal images. -/
theorem edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
    (M : XRespectingMinorModel H G X)
    (S : Finset V) (hS : S ⊆ X)
    {a b : W} (hab : H.Adj a b)
    (havoid :
      ∀ x : V, ∀ hx : x ∈ X,
        M.terminalVertex x hx ≠ a ∧ M.terminalVertex x hx ≠ b) :
    edgeContractImageSet (a := a) (b := b) (M.terminalImage S hS) =
      (M.contractNonterminalEdge hab havoid).terminalImage S hS := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨w, _hw, hwz⟩
    rcases (M.mem_terminalImage_iff S hS w.1).1 w.2 with ⟨x, hx, hwterm⟩
    have hproj :
        EdgeContractVertex.projection (V := W) (u := a) (v := b)
            w.1 =
          EdgeContractVertex.ofVertex
            (M.terminalVertex x (hS hx)) (havoid x (hS hx)) := by
      simpa [hwterm] using
        EdgeContractVertex.projection_eq_of_ne
        (V := W) (u := a) (v := b)
        (havoid x (hS hx)).1 (havoid x (hS hx)).2
    rw [← hwz, hproj]
    exact
      ((M.contractNonterminalEdge hab havoid).mem_terminalImage_iff S hS _).2
        ⟨x, hx, rfl⟩
  · intro hz
    rcases
        ((M.contractNonterminalEdge hab havoid).mem_terminalImage_iff S hS z).1 hz with
      ⟨x, hx, hzterm⟩
    let w := M.terminalVertex x (hS hx)
    have hw : w ∈ M.terminalImage S hS :=
      (M.mem_terminalImage_iff S hS w).2 ⟨x, hx, rfl⟩
    have hproj :
        EdgeContractVertex.projection (V := W) (u := a) (v := b) w =
          EdgeContractVertex.ofVertex w (havoid x (hS hx)) := by
      exact EdgeContractVertex.projection_eq_of_ne
        (V := W) (u := a) (v := b)
        (havoid x (hS hx)).1 (havoid x (hS hx)).2
    exact Finset.mem_image.mpr
      ⟨⟨w, hw⟩, by simp, by
        rw [hzterm]
        simpa [w, XRespectingMinorModel.contractNonterminalEdge] using hproj⟩

end XRespectingMinorModel

namespace XRespectingMinorModel

variable {W : Type w} [DecidableEq W]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
variable {X : Finset V}

/-- Restrict an `X`-respecting minor model to an induced subgraph of the
minor, provided all terminal representatives remain in the retained vertex
set. -/
noncomputable def induceVertices
    (M : XRespectingMinorModel H G X) (U : Finset W)
    (hterm : ∀ x : V, ∀ hx : x ∈ X, M.terminalVertex x hx ∈ U) :
    XRespectingMinorModel (H.induce {w : W | w ∈ U}) G X where
  model := {
    branchSet := fun w => M.model.branchSet w.1
    branch_nonempty := fun w => M.model.branch_nonempty w.1
    branch_connected := fun w => M.model.branch_connected w.1
    branch_disjoint := by
      intro a b hab
      exact M.model.branch_disjoint (by
        intro h
        exact hab (Subtype.ext h))
    adjacent := by
      intro a b hab
      exact M.model.adjacent (by
        simpa using hab)
  }
  terminalVertex := fun x hx => ⟨M.terminalVertex x hx, hterm x hx⟩
  terminal_injective := by
    intro x y hx hy hxy
    exact M.terminal_injective hx hy (congrArg Subtype.val hxy)
  terminal_branchSet := by
    intro x hx
    exact M.terminal_branchSet x hx

omit [DecidableEq V] in
/-- Terminal images in an induced `X`-respecting model are exactly subtype
images of the old terminal images. -/
theorem terminalImage_induceVertices_eq_subtypeFinset
    (M : XRespectingMinorModel H G X) (U : Finset W)
    (hterm : ∀ x : V, ∀ hx : x ∈ X, M.terminalVertex x hx ∈ U)
    (S : Finset V) (hS : S ⊆ X)
    (hOld : M.terminalImage S hS ⊆ U) :
    (M.induceVertices U hterm).terminalImage S hS =
      PathPacking.subtypeFinset (M.terminalImage S hS) U hOld := by
  classical
  ext z
  constructor
  · intro hz
    rcases
        ((M.induceVertices U hterm).mem_terminalImage_iff S hS z).1 hz with
      ⟨x, hx, hz_eq⟩
    exact (PathPacking.mem_subtypeFinset hOld z).2
      ((M.mem_terminalImage_iff S hS z.1).2 ⟨x, hx, by
        exact congrArg Subtype.val hz_eq⟩)
  · intro hz
    have hzOld : z.1 ∈ M.terminalImage S hS :=
      (PathPacking.mem_subtypeFinset hOld z).1 hz
    rcases (M.mem_terminalImage_iff S hS z.1).1 hzOld with
      ⟨x, hx, hz_eq⟩
    exact
      ((M.induceVertices U hterm).mem_terminalImage_iff S hS z).2
        ⟨x, hx, Subtype.ext hz_eq⟩

end XRespectingMinorModel

namespace TwoPairGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V}
variable {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

omit [DecidableEq V] in
/-- Restrict a good minor to an induced subgraph that contains all vertices
used by both selected routings and all terminal representatives. -/
noncomputable def induceVertices
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (U : Finset W)
    (hterm :
      ∀ x : V, ∀ hx : x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂,
        N.respecting.terminalVertex x hx ∈ U)
    (hred : N.redRouting.toPathPacking.StaysIn U)
    (hblue : N.blueRouting.toPathPacking.StaysIn U) :
    TwoPairGoodMinor G (H.induce {w : W | w ∈ U}) S₁ T₁ S₂ T₂ := by
  classical
  let M' := N.respecting.induceVertices U hterm
  have hS₁old :
      N.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) ⊆ U := by
    intro y hy
    rcases
        (N.respecting.mem_terminalImage_iff S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) y).1 hy with
      ⟨x, hx, rfl⟩
    exact hterm x ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hx)
  have hT₁old :
      N.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) ⊆ U := by
    intro y hy
    rcases
        (N.respecting.mem_terminalImage_iff T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) y).1 hy with
      ⟨x, hx, rfl⟩
    exact hterm x ((subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hx)
  have hS₂old :
      N.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) ⊆ U := by
    intro y hy
    rcases
        (N.respecting.mem_terminalImage_iff S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) y).1 hy with
      ⟨x, hx, rfl⟩
    exact hterm x ((subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hx)
  have hT₂old :
      N.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) ⊆ U := by
    intro y hy
    rcases
        (N.respecting.mem_terminalImage_iff T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) y).1 hy with
      ⟨x, hx, rfl⟩
    exact hterm x ((subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hx)
  have hS₁eq :
      PathPacking.subtypeFinset
          (N.respecting.terminalImage S₁
            (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)) U hS₁old =
        M'.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
    simpa [M'] using
      (N.respecting.terminalImage_induceVertices_eq_subtypeFinset U hterm
        S₁ (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hS₁old).symm
  have hT₁eq :
      PathPacking.subtypeFinset
          (N.respecting.terminalImage T₁
            (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)) U hT₁old =
        M'.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
    simpa [M'] using
      (N.respecting.terminalImage_induceVertices_eq_subtypeFinset U hterm
        T₁ (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hT₁old).symm
  have hS₂eq :
      PathPacking.subtypeFinset
          (N.respecting.terminalImage S₂
            (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)) U hS₂old =
        M'.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
    simpa [M'] using
      (N.respecting.terminalImage_induceVertices_eq_subtypeFinset U hterm
        S₂ (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hS₂old).symm
  have hT₂eq :
      PathPacking.subtypeFinset
          (N.respecting.terminalImage T₂
            (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) U hT₂old =
        M'.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
    simpa [M'] using
      (N.respecting.terminalImage_induceVertices_eq_subtypeFinset U hterm
        T₂ (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hT₂old).symm
  exact {
    respecting := M'
    redRouting := (N.redRouting.induce U hred hS₁old hT₁old).copyTerminals
      hS₁eq hT₁eq
    blueRouting := (N.blueRouting.induce U hblue hS₂old hT₂old).copyTerminals
      hS₂eq hT₂eq
  }

omit [DecidableEq V] in
/-- If a nonterminal vertex is unused by both selected routings, then deleting
that vertex preserves the good-minor property. -/
noncomputable def deleteUnusedNonterminalVertex
    [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) {v : W}
    (hvT : v ∉ N.terminalSet)
    (hvR : v ∉ N.redRouting.toPathPacking.vertexSet)
    (hvB : v ∉ N.blueRouting.toPathPacking.vertexSet) :
    TwoPairGoodMinor G
      (H.induce {w : W | w ∈ (Finset.univ.erase v : Finset W)})
      S₁ T₁ S₂ T₂ := by
  classical
  let U : Finset W := Finset.univ.erase v
  have hterm :
      ∀ x : V, ∀ hx : x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂,
        N.respecting.terminalVertex x hx ∈ U := by
    intro x hx
    change N.respecting.terminalVertex x hx ∈ (Finset.univ.erase v : Finset W)
    rw [Finset.mem_erase]
    constructor
    · intro hrep
      exact hvT (by
        simpa [hrep] using N.terminalVertex_mem_terminalSet x hx)
    · exact Finset.mem_univ _
  have hred : N.redRouting.toPathPacking.StaysIn U := by
    intro i y hy
    change y ∈ (Finset.univ.erase v : Finset W)
    rw [Finset.mem_erase]
    constructor
    · intro hyv
      exact hvR ((N.redRouting.toPathPacking.mem_vertexSet).2 ⟨i, by
        simpa [hyv] using hy⟩)
    · exact Finset.mem_univ _
  have hblue : N.blueRouting.toPathPacking.StaysIn U := by
    intro i y hy
    change y ∈ (Finset.univ.erase v : Finset W)
    rw [Finset.mem_erase]
    constructor
    · intro hyv
      exact hvB ((N.blueRouting.toPathPacking.mem_vertexSet).2 ⟨i, by
        simpa [hyv] using hy⟩)
    · exact Finset.mem_univ _
  exact N.induceVertices U hterm hred hblue

end TwoPairGoodMinor

/-! ## Minimal good minors: deletion side -/

/-- The result of transferring a perfect path packing across deletion of an
edge that none of its paths uses. -/
noncomputable def perfectPathPacking_deleteUnusedEdge
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PerfectPathPacking H A B) {a b : W}
    (hunused : s(a, b) ∉ P.toPathPacking.edgeSet) :
    PerfectPathPacking (H.deleteEdges ({s(a, b)} : Set (Sym2 W))) A B :=
  P.transfer (H.deleteEdges ({s(a, b)} : Set (Sym2 W))) (by
    intro i e he
    rw [_root_.SimpleGraph.edgeSet_deleteEdges]
    constructor
    · exact (P.path i).walk.edges_subset_edgeSet he
    · intro hemem
      have heq : e = s(a, b) := by
        simpa using hemem
      exact hunused (by
        rw [← heq]
        exact (P.toPathPacking.mem_edgeSet).2
          ⟨i, by
            exact List.mem_toFinset.mpr (by
              simpa [GraphPath.edgeSet] using he)⟩)
  )

/-- Transfer a perfect path packing to the graph obtained by deleting an
arbitrary edge that no packed path uses. -/
noncomputable def perfectPathPacking_deleteUnusedSym2Edge
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PerfectPathPacking H A B) (e₀ : Sym2 W)
    (hunused : e₀ ∉ P.toPathPacking.edgeSet) :
    PerfectPathPacking (H.deleteEdges ({e₀} : Set (Sym2 W))) A B :=
  P.transfer (H.deleteEdges ({e₀} : Set (Sym2 W))) (by
    intro i e he
    rw [_root_.SimpleGraph.edgeSet_deleteEdges]
    constructor
    · exact (P.path i).walk.edges_subset_edgeSet he
    · intro hemem
      have heq : e = e₀ := by
        simpa using hemem
      exact hunused (by
        rw [← heq]
        exact (P.toPathPacking.mem_edgeSet).2
          ⟨i, by
            exact List.mem_toFinset.mpr (by
              simpa [GraphPath.edgeSet] using he)⟩)
  )

/-- A vertex on one path of a path packing has degree at most two in the
packing's spanning graph. -/
theorem pathPacking_spanningGraph_degreeAtMost_two_of_mem_path
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PathPacking H A B) {v : W} (i : P.Index)
    (hvi : v ∈ (P.path i).vertexSet) :
    DegreeAtMost P.spanningGraph v 2 := by
  classical
  let N := GraphPath.pathNeighborFinset (P.path i) v
  refine ⟨N, ?_, ?_⟩
  · intro w
    constructor
    · intro hw
      have he : s(v, w) ∈ (P.path i).edgeSet :=
        (GraphPath.mem_pathNeighborFinset (P.path i)).mp hw |>.2
      have hne : v ≠ w := by
        have hadj : H.Adj v w := by
          simpa using GraphPath.edgeSet_subset_edgeSet (P.path i) he
        exact hadj.ne
      exact (P.spanningGraph_adj_iff_exists_path_edge).2
        ⟨⟨i, he⟩, hne⟩
    · intro hvw
      rcases (P.spanningGraph_adj_iff_exists_path_edge).1 hvw with
        ⟨⟨j, hej⟩, _hne⟩
      have hvj : v ∈ (P.path j).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path j) hej).1
      have hwj : w ∈ (P.path j).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path j) hej).2
      have hji : j = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (P.node_disjoint hne) hvj hvi
      subst j
      exact (GraphPath.mem_pathNeighborFinset (P.path i)).2 ⟨hwj, hej⟩
  · exact GraphPath.pathNeighborFinset_card_le_two (P.path i) v

/-- A vertex outside all paths of a packing is isolated in the packing's
spanning graph. -/
theorem pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PathPacking H A B) {v : W}
    (hv : v ∉ P.vertexSet) :
    DegreeAtMost P.spanningGraph v 0 := by
  classical
  refine ⟨∅, ?_, by simp⟩
  intro w
  constructor
  · intro hw
    simp at hw
  · intro hvw
    rcases (P.spanningGraph_adj_iff_exists_path_edge).1 hvw with
      ⟨⟨i, hei⟩, _hne⟩
    have hvi : v ∈ (P.path i).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) hei).1
    exact False.elim (hv ((P.mem_vertexSet).2 ⟨i, hvi⟩))

/-- Degree bounds add under graph union. -/
theorem degreeAtMost_sup
    {W : Type w} [DecidableEq W]
    {G₁ G₂ : _root_.SimpleGraph W} {v : W} {d₁ d₂ : ℕ}
    (h₁ : DegreeAtMost G₁ v d₁) (h₂ : DegreeAtMost G₂ v d₂) :
    DegreeAtMost (G₁ ⊔ G₂) v (d₁ + d₂) := by
  classical
  rcases h₁ with ⟨N₁, hN₁, hcard₁⟩
  rcases h₂ with ⟨N₂, hN₂, hcard₂⟩
  refine ⟨N₁ ∪ N₂, ?_, ?_⟩
  · intro w
    simp [hN₁ w, hN₂ w]
  · exact (Finset.card_union_le N₁ N₂).trans
      (Nat.add_le_add hcard₁ hcard₂)

/-- Every vertex has degree at most two in the spanning graph of one perfect
path packing. -/
theorem perfectPathPacking_spanningGraph_degreeAtMost_two
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PerfectPathPacking H A B) (v : W) :
    DegreeAtMost P.toPathPacking.spanningGraph v 2 := by
  classical
  by_cases hv : v ∈ P.toPathPacking.vertexSet
  · rcases (P.toPathPacking.mem_vertexSet).1 hv with ⟨i, hvi⟩
    exact pathPacking_spanningGraph_degreeAtMost_two_of_mem_path
      P.toPathPacking i hvi
  · exact DegreeAtMost.mono
      (pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem P.toPathPacking hv)
      (by omega)

/-- A path packing with no indices has bottom spanning graph. -/
theorem pathPacking_spanningGraph_eq_bot_of_card_eq_zero
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PathPacking H A B) (hcard : P.card = 0) :
    P.spanningGraph = ⊥ := by
  classical
  ext v w
  constructor
  · intro hvw
    rcases (P.spanningGraph_adj_iff_exists_path_edge).1 hvw with
      ⟨⟨i, _hi⟩, _hne⟩
    have hIndex : Fintype.card P.Index = 0 := by
      simpa [PathPacking.card] using hcard
    have hEmpty : IsEmpty P.Index :=
      Fintype.card_eq_zero_iff.mp hIndex
    exact False.elim (hEmpty.false i)
  · intro hbot
    simp at hbot

/-- A perfect path packing with no paths has bottom spanning graph. -/
theorem perfectPathPacking_spanningGraph_eq_bot_of_card_eq_zero
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W} {A B : Finset W}
    (P : PerfectPathPacking H A B) (hcard : P.card = 0) :
    P.toPathPacking.spanningGraph = ⊥ := by
  exact pathPacking_spanningGraph_eq_bot_of_card_eq_zero
    P.toPathPacking (by simpa using hcard)

/-- The bottom graph has degree zero at every vertex. -/
theorem degreeAtMost_bot
    {W : Type w} [DecidableEq W] (v : W) :
    DegreeAtMost (⊥ : _root_.SimpleGraph W) v 0 := by
  classical
  refine ⟨∅, ?_, by simp⟩
  intro w
  constructor
  · intro hw
    simp at hw
  · intro h
    simp at h

/-- If every vertex has degree at most two, then the branch-vertex count is
zero. -/
theorem branchVertexCount_eq_zero_of_degreeAtMost_two
    {W : Type w} [Fintype W] [DecidableEq W]
    (H : _root_.SimpleGraph W)
    (hdeg : ∀ v : W, DegreeAtMost H v 2) :
    branchVertexCount H = 0 := by
  classical
  have hfilter :
      (Finset.univ.filter fun v : W => ¬ DegreeAtMost H v 2) = ∅ := by
    ext v
    simp [hdeg v]
  simp [branchVertexCount, hfilter]

omit [DecidableEq V] in
/-- If every high-degree vertex is assigned to one of finitely many buckets
with at most two high-degree vertices in each bucket, then the branch-vertex
count is at most twice the number of buckets. -/
theorem branchVertexCount_le_two_mul_of_fiber_bound
    {W : Type w} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph V} [Fintype V]
    (branchOf : {v : V // ¬ DegreeAtMost H v 2} → W)
    (hfiber :
      ∀ w : W,
        Fintype.card
          {x : {v : V // ¬ DegreeAtMost H v 2} // branchOf x = w} ≤ 2) :
    branchVertexCount H ≤ 2 * Fintype.card W := by
  classical
  let B := {v : V // ¬ DegreeAtMost H v 2}
  have hbranch :
      branchVertexCount H = Fintype.card B := by
    change (Finset.univ.filter fun v : V => ¬ DegreeAtMost H v 2).card =
      Fintype.card B
    simpa [B] using
      (Fintype.card_subtype (fun v : V => ¬ DegreeAtMost H v 2)).symm
  let buckets : Finset W := Finset.univ
  have hmaps :
      ((Finset.univ : Finset B) : Set B).MapsTo branchOf buckets := by
    intro x _hx
    simp [buckets]
  have hcard :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset B)) (t := buckets)
      (f := branchOf) hmaps
  have hfiberFinset :
      ∀ w : W,
        ({x ∈ (Finset.univ : Finset B) | branchOf x = w}).card ≤ 2 := by
    intro w
    have hcardFiber :
        ({x ∈ (Finset.univ : Finset B) | branchOf x = w}).card =
          Fintype.card {x : B // branchOf x = w} := by
      simpa using
        (Fintype.card_subtype (fun x : B => branchOf x = w)).symm
    rw [hcardFiber]
    exact hfiber w
  have hsum_le :
      (∑ w ∈ buckets,
        ({x ∈ (Finset.univ : Finset B) | branchOf x = w}).card) ≤
        ∑ _w ∈ buckets, 2 := by
    refine Finset.sum_le_sum ?_
    intro w _hw
    exact hfiberFinset w
  have hB :
      Fintype.card B ≤ Fintype.card W * 2 := by
    calc
      Fintype.card B = (Finset.univ : Finset B).card := by simp
      _ =
          ∑ w ∈ buckets,
            ({x ∈ (Finset.univ : Finset B) | branchOf x = w}).card := hcard
      _ ≤ ∑ _w ∈ buckets, 2 := hsum_le
      _ = Fintype.card W * 2 := by
        simp [buckets, Finset.sum_const]
  rw [hbranch]
  simpa [Nat.mul_comm] using hB

/-- The output of the paper's minor-expansion paragraph: two host-side
routings, together with a map assigning every high-degree vertex in their
union to a minor vertex, with at most two high-degree vertices assigned to
each minor vertex. -/
structure TwoPairControlledExpansion
    {W : Type w} [Fintype W] [DecidableEq W]
    [Fintype V]
    (G : _root_.SimpleGraph V)
    (S₁ T₁ S₂ T₂ : Finset V) where
  red : PerfectPathPacking G S₁ T₁
  blue : PerfectPathPacking G S₂ T₂
  branchOf :
    {v : V // ¬ DegreeAtMost (twoPackingUnionGraph red blue) v 2} → W
  fiber_le_two :
    ∀ w : W,
      Fintype.card
        {x : {v : V // ¬ DegreeAtMost (twoPackingUnionGraph red blue) v 2} //
          branchOf x = w} ≤ 2

namespace TwoPairControlledExpansion

variable {W : Type w} [Fintype W] [DecidableEq W]
variable {G : _root_.SimpleGraph V}
variable {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- Build a controlled expansion from branch-set-local high-degree bounds.

This is the counting shell for the paper's expansion paragraph: once the
expanded red and blue routings are built, it is enough to know that every
high-degree host vertex belongs to some branch set of the minor model and that
each branch set contains at most two such vertices. -/
noncomputable def ofBranchSetLocalBound
    [Fintype V]
    (M : MinorModel H G)
    (red : PerfectPathPacking G S₁ T₁)
    (blue : PerfectPathPacking G S₂ T₂)
    (hcover :
      ∀ x : {v : V // ¬ DegreeAtMost (twoPackingUnionGraph red blue) v 2},
        ∃ w : W, x.1 ∈ M.branchSet w)
    (hlocal :
      ∀ w : W,
        Fintype.card
          {x : {v : V // ¬ DegreeAtMost (twoPackingUnionGraph red blue) v 2} //
            x.1 ∈ M.branchSet w} ≤ 2) :
    TwoPairControlledExpansion (W := W) G S₁ T₁ S₂ T₂ where
  red := red
  blue := blue
  branchOf := fun x => Classical.choose (hcover x)
  fiber_le_two := by
    classical
    intro w
    let B :=
      {v : V // ¬ DegreeAtMost (twoPackingUnionGraph red blue) v 2}
    let Fw : Type _ := {x : B // Classical.choose (hcover x) = w}
    let Lw : Type _ := {x : B // x.1 ∈ M.branchSet w}
    have hinj : Fw ↪ Lw := {
      toFun := fun x =>
        ⟨x.1, by
          have hxmem :
              x.1.1 ∈ M.branchSet (Classical.choose (hcover x.1)) :=
            Classical.choose_spec (hcover x.1)
          simpa [x.2] using hxmem⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : Lw => z.1) hxy
    }
    have hcard : Fintype.card Fw ≤ Fintype.card Lw :=
      Fintype.card_le_of_injective _ hinj.injective
    exact hcard.trans (hlocal w)

/-- Pair-subset form of `ofBranchSetLocalBound`: if every high-degree vertex
inside a branch set is one of two named local splice vertices, then each
branch set contributes at most two high-degree vertices. -/
noncomputable def ofBranchSetLocalPairBound
    [Fintype V]
    (M : MinorModel H G)
    (red : PerfectPathPacking G S₁ T₁)
    (blue : PerfectPathPacking G S₂ T₂)
    (hcover :
      ∀ x : {v : V // ¬ DegreeAtMost (twoPackingUnionGraph red blue) v 2},
        ∃ w : W, x.1 ∈ M.branchSet w)
    (a b : W → V)
    (hlocal :
      ∀ w : W,
        ∀ x : {v : V //
            ¬ DegreeAtMost (twoPackingUnionGraph red blue) v 2},
          x.1 ∈ M.branchSet w →
            x.1 = a w ∨ x.1 = b w) :
    TwoPairControlledExpansion (W := W) G S₁ T₁ S₂ T₂ :=
  ofBranchSetLocalBound M red blue hcover (by
    classical
    intro w
    let B :=
      {v : V // ¬ DegreeAtMost (twoPackingUnionGraph red blue) v 2}
    let Lw : Type _ := {x : B // x.1 ∈ M.branchSet w}
    let code : Lw → Fin 2 := fun x =>
      if x.1.1 = a w then ⟨0, by omega⟩ else ⟨1, by omega⟩
    have hcode_inj : Function.Injective code := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      by_cases hxA : x.1.1 = a w
      · by_cases hyA : y.1.1 = a w
        · exact hxA.trans hyA.symm
        · have hcode_xy :
              code x = ⟨0, by omega⟩ := by simp [code, hxA]
          have hcode_y :
              code y = ⟨1, by omega⟩ := by simp [code, hyA]
          have h01 : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
            hcode_xy.symm.trans (hxy.trans hcode_y)
          exact False.elim (by
            have hval : (0 : ℕ) = 1 := congrArg Fin.val h01
            norm_num at hval)
      · by_cases hyA : y.1.1 = a w
        · have hcode_x :
              code x = ⟨1, by omega⟩ := by simp [code, hxA]
          have hcode_y :
              code y = ⟨0, by omega⟩ := by simp [code, hyA]
          have h10 : (⟨1, by omega⟩ : Fin 2) = ⟨0, by omega⟩ :=
            hcode_x.symm.trans (hxy.trans hcode_y)
          exact False.elim (by
            have hval : (1 : ℕ) = 0 := congrArg Fin.val h10
            norm_num at hval)
        · rcases hlocal w x.1 x.2 with hxEq | hxEq
          · exact False.elim (hxA hxEq)
          · rcases hlocal w y.1 y.2 with hyEq | hyEq
            · exact False.elim (hyA hyEq)
            · exact hxEq.trans hyEq.symm
    exact (Fintype.card_le_of_injective code hcode_inj).trans (by simp))

end TwoPairControlledExpansion

namespace TwoPairControlledExpansion

variable {W : Type w} [Fintype W] [DecidableEq W]
variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- A controlled expansion over a bounded minor vertex set gives the final
Theorem 1.3 sparsifier inequality in the original host graph. -/
theorem toRoutingSparsifier
    [Fintype V]
    (E : TwoPairControlledExpansion (W := W) G S₁ T₁ S₂ T₂)
    {k : ℕ}
    (hW : Fintype.card W ≤ 4 * k ^ 4 + 4 * k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  refine ⟨E.red, E.blue, ?_⟩
  have hbranch :
      branchVertexCount (twoPackingUnionGraph E.red E.blue) ≤
        2 * Fintype.card W :=
    branchVertexCount_le_two_mul_of_fiber_bound E.branchOf E.fiber_le_two
  nlinarith [hbranch, hW, Nat.zero_le (k ^ 4), Nat.zero_le k]

end TwoPairControlledExpansion

/-- If both packings are empty, their union contributes no branch vertices. -/
theorem branchVertexCount_twoPackingUnionGraph_eq_zero_of_card_eq_zero
    {W : Type w} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset W}
    (P : PerfectPathPacking H S₁ T₁)
    (Q : PerfectPathPacking H S₂ T₂)
    (hP : P.card = 0) (hQ : Q.card = 0) :
    branchVertexCount (twoPackingUnionGraph P Q) = 0 := by
  classical
  have hPred :
      P.toPathPacking.spanningGraph = ⊥ :=
    perfectPathPacking_spanningGraph_eq_bot_of_card_eq_zero P hP
  have hQblue :
      Q.toPathPacking.spanningGraph = ⊥ :=
    perfectPathPacking_spanningGraph_eq_bot_of_card_eq_zero Q hQ
  have hunion : twoPackingUnionGraph P Q = (⊥ : _root_.SimpleGraph W) := by
    simp [twoPackingUnionGraph, hPred, hQblue]
  rw [hunion]
  exact branchVertexCount_eq_zero_of_degreeAtMost_two _
    (fun v => DegreeAtMost.mono (degreeAtMost_bot v) (by omega))

/-- If the blue packing is empty, the union is just one path packing and has
no branch vertices. -/
theorem branchVertexCount_twoPackingUnionGraph_eq_zero_of_blue_card_eq_zero
    {W : Type w} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset W}
    (P : PerfectPathPacking H S₁ T₁)
    (Q : PerfectPathPacking H S₂ T₂)
    (hQ : Q.card = 0) :
    branchVertexCount (twoPackingUnionGraph P Q) = 0 := by
  classical
  have hQblue :
      Q.toPathPacking.spanningGraph = ⊥ :=
    perfectPathPacking_spanningGraph_eq_bot_of_card_eq_zero Q hQ
  have hunion :
      twoPackingUnionGraph P Q = P.toPathPacking.spanningGraph := by
    ext v w
    simp [twoPackingUnionGraph, hQblue]
  rw [hunion]
  exact branchVertexCount_eq_zero_of_degreeAtMost_two _
    (fun v => perfectPathPacking_spanningGraph_degreeAtMost_two P v)

/-- If the red packing is empty, the union is just one path packing and has no
branch vertices. -/
theorem branchVertexCount_twoPackingUnionGraph_eq_zero_of_red_card_eq_zero
    {W : Type w} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset W}
    (P : PerfectPathPacking H S₁ T₁)
    (Q : PerfectPathPacking H S₂ T₂)
    (hP : P.card = 0) :
    branchVertexCount (twoPackingUnionGraph P Q) = 0 := by
  classical
  have hPred :
      P.toPathPacking.spanningGraph = ⊥ :=
    perfectPathPacking_spanningGraph_eq_bot_of_card_eq_zero P hP
  have hunion :
      twoPackingUnionGraph P Q = Q.toPathPacking.spanningGraph := by
    ext v w
    simp [twoPackingUnionGraph, hPred]
  rw [hunion]
  exact branchVertexCount_eq_zero_of_degreeAtMost_two _
    (fun v => perfectPathPacking_spanningGraph_degreeAtMost_two Q v)

/-- If a vertex is absent from the red packing, the red/blue union has degree
at most two at that vertex. -/
theorem twoPackingUnionGraph_degreeAtMost_two_of_not_mem_red
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset W}
    (P : PerfectPathPacking H S₁ T₁)
    (Q : PerfectPathPacking H S₂ T₂) {v : W}
    (hv : v ∉ P.toPathPacking.vertexSet) :
    DegreeAtMost (twoPackingUnionGraph P Q) v 2 := by
  classical
  have hred0 :
      DegreeAtMost P.toPathPacking.spanningGraph v 0 :=
    pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem P.toPathPacking hv
  have hblue2 :
      DegreeAtMost Q.toPathPacking.spanningGraph v 2 :=
    perfectPathPacking_spanningGraph_degreeAtMost_two Q v
  simpa [twoPackingUnionGraph] using
    DegreeAtMost.mono (degreeAtMost_sup hred0 hblue2) (by omega)

/-- If a vertex is absent from the blue packing, the red/blue union has degree
at most two at that vertex. -/
theorem twoPackingUnionGraph_degreeAtMost_two_of_not_mem_blue
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset W}
    (P : PerfectPathPacking H S₁ T₁)
    (Q : PerfectPathPacking H S₂ T₂) {v : W}
    (hv : v ∉ Q.toPathPacking.vertexSet) :
    DegreeAtMost (twoPackingUnionGraph P Q) v 2 := by
  classical
  have hred2 :
      DegreeAtMost P.toPathPacking.spanningGraph v 2 :=
    perfectPathPacking_spanningGraph_degreeAtMost_two P v
  have hblue0 :
      DegreeAtMost Q.toPathPacking.spanningGraph v 0 :=
    pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem Q.toPathPacking hv
  simpa [twoPackingUnionGraph, Nat.add_comm] using
    DegreeAtMost.mono (degreeAtMost_sup hred2 hblue0) (by omega)

/-- The union graph of two path packings is a subgraph of their common host. -/
theorem twoPackingUnionGraph_le
    {W : Type w} [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset W}
    (P : PerfectPathPacking H S₁ T₁)
    (Q : PerfectPathPacking H S₂ T₂) :
    twoPackingUnionGraph P Q ≤ H := by
  intro u v huv
  rcases (show
      P.toPathPacking.spanningGraph.Adj u v ∨
        Q.toPathPacking.spanningGraph.Adj u v by
      simpa [twoPackingUnionGraph] using huv) with hred | hblue
  · exact P.toPathPacking.spanningGraph_le hred
  · exact Q.toPathPacking.spanningGraph_le hblue

/-- Deleting an existing edge strictly decreases the finite edge count. -/
theorem edgeFinset_deleteEdges_singleton_card_lt
    {W : Type w} [Fintype W] [DecidableEq W]
    (H : _root_.SimpleGraph W) {a b : W} (hab : H.Adj a b) :
    ((H.deleteEdges ({s(a, b)} : Set (Sym2 W))).edgeFinset).card <
      H.edgeFinset.card := by
  classical
  let e : Sym2 W := s(a, b)
  have hsubset :
      (H.deleteEdges ({e} : Set (Sym2 W))).edgeFinset ⊆ H.edgeFinset := by
    intro f hf
    rw [_root_.SimpleGraph.mem_edgeFinset] at hf ⊢
    rw [_root_.SimpleGraph.edgeSet_deleteEdges] at hf
    exact hf.1
  have hproper :
      (H.deleteEdges ({e} : Set (Sym2 W))).edgeFinset ⊂ H.edgeFinset := by
    refine ⟨hsubset, ?_⟩
    intro heq
    have heH : e ∈ H.edgeFinset := by
      rw [_root_.SimpleGraph.mem_edgeFinset]
      simpa [_root_.SimpleGraph.mem_edgeSet, e] using hab
    have heDel : e ∈ (H.deleteEdges ({e} : Set (Sym2 W))).edgeFinset := by
      exact heq heH
    have heDelSet :
        e ∈ (H.deleteEdges ({e} : Set (Sym2 W))).edgeSet := by
      simpa [_root_.SimpleGraph.mem_edgeFinset] using heDel
    rw [_root_.SimpleGraph.edgeSet_deleteEdges] at heDelSet
    exact heDelSet.2 (by simp [e])
  exact Finset.card_lt_card hproper

/-- Deleting an existing edge strictly decreases the cardinality of the edge
set.  This formulation is independent of the particular finite-set instance
used to enumerate the edges. -/
theorem edgeSet_deleteEdges_singleton_ncard_lt
    {W : Type w} [Fintype W] [DecidableEq W]
    (H : _root_.SimpleGraph W) {a b : W} (hab : H.Adj a b) :
    ((H.deleteEdges ({s(a, b)} : Set (Sym2 W))).edgeSet).ncard <
      H.edgeSet.ncard := by
  classical
  let e : Sym2 W := s(a, b)
  have heH : e ∈ H.edgeSet := by
    simpa [_root_.SimpleGraph.mem_edgeSet, e] using hab
  rw [_root_.SimpleGraph.edgeSet_deleteEdges]
  have hcard :
      (H.edgeSet \ ({e} : Set (Sym2 W))).ncard + 1 =
        H.edgeSet.ncard :=
    Set.ncard_diff_singleton_add_one heH (Set.toFinite H.edgeSet)
  exact (Nat.lt_succ_self _).trans_eq hcard

namespace TwoPairGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- Every high-degree vertex in the union of the naively lifted red and blue
routings lies in some branch set of the minor model.  The remaining expansion
work is therefore local to individual branch sets. -/
theorem liftedRouting_highVertex_mem_branchSet
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    ∀ x : {v : V //
        ¬ DegreeAtMost
          (twoPackingUnionGraph N.liftRedRouting N.liftBlueRouting) v 2},
      ∃ w : W, x.1 ∈ N.respecting.model.branchSet w := by
  classical
  intro x
  have hxRed :
      x.1 ∈ N.liftRedRouting.toPathPacking.vertexSet := by
    by_contra hxRed
    exact x.2
      (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_red
        N.liftRedRouting N.liftBlueRouting hxRed)
  rcases (N.liftRedRouting.toPathPacking.mem_vertexSet).1 hxRed with
    ⟨i, hxi⟩
  have hxWalk :
      x.1 ∈ N.respecting.model.walkBranchUnion
        (N.redRouting.path i).walk := by
    exact
      (N.respecting.liftPerfectPathPacking_path_vertexSet_subset_walkBranchUnion
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
        N.redRouting i)
        (by simpa [TwoPairGoodMinor.liftRedRouting] using hxi)
  rw [MinorModel.walkBranchUnion] at hxWalk
  rcases Finset.mem_biUnion.1 hxWalk with ⟨w, _hw, hxw⟩
  exact ⟨w, hxw⟩

/-- If a high-degree host vertex in the lifted red/blue union belongs to a
minor branch set `w`, then `w` lies on both selected minor routings. -/
theorem liftedRouting_highVertex_branchSet_minorVertex_mem_red_blue
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {x : V} {w : W}
    (hxHigh :
      ¬ DegreeAtMost
        (twoPackingUnionGraph N.liftRedRouting N.liftBlueRouting) x 2)
    (hxw : x ∈ N.respecting.model.branchSet w) :
    w ∈ N.redRouting.toPathPacking.vertexSet ∧
      w ∈ N.blueRouting.toPathPacking.vertexSet := by
  classical
  have hxRed :
      x ∈ N.liftRedRouting.toPathPacking.vertexSet := by
    by_contra hxRed
    exact hxHigh
      (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_red
        N.liftRedRouting N.liftBlueRouting hxRed)
  have hxBlue :
      x ∈ N.liftBlueRouting.toPathPacking.vertexSet := by
    by_contra hxBlue
    exact hxHigh
      (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_blue
        N.liftRedRouting N.liftBlueRouting hxBlue)
  constructor
  · rcases (N.liftRedRouting.toPathPacking.mem_vertexSet).1 hxRed with
      ⟨i, hxi⟩
    have hxWalk :
        x ∈ N.respecting.model.walkBranchUnion
          (N.redRouting.path i).walk := by
      exact
        (N.respecting.liftPerfectPathPacking_path_vertexSet_subset_walkBranchUnion
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
          N.redRouting i)
          (by simpa [TwoPairGoodMinor.liftRedRouting] using hxi)
    have hwPath :
        w ∈ (N.redRouting.path i).vertexSet :=
      MinorModel.vertex_mem_of_branchSet_mem_walkBranchUnion
        N.respecting.model hxw hxWalk
    exact (N.redRouting.toPathPacking.mem_vertexSet).2 ⟨i, hwPath⟩
  · rcases (N.liftBlueRouting.toPathPacking.mem_vertexSet).1 hxBlue with
      ⟨j, hxj⟩
    have hxWalk :
        x ∈ N.respecting.model.walkBranchUnion
          (N.blueRouting.path j).walk := by
      exact
        (N.respecting.liftPerfectPathPacking_path_vertexSet_subset_walkBranchUnion
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
          N.blueRouting j)
          (by simpa [TwoPairGoodMinor.liftBlueRouting] using hxj)
    have hwPath :
        w ∈ (N.blueRouting.path j).vertexSet :=
      MinorModel.vertex_mem_of_branchSet_mem_walkBranchUnion
        N.respecting.model hxw hxWalk
    exact (N.blueRouting.toPathPacking.mem_vertexSet).2 ⟨j, hwPath⟩

/-- Every high-degree vertex in the union of the paper-expanded red and blue
routings lies in some branch set of the minor model. -/
theorem paperRouting_highVertex_mem_branchSet
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    ∀ x : {v : V //
        ¬ DegreeAtMost
          (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) v 2},
      ∃ w : W, x.1 ∈ N.respecting.model.branchSet w := by
  classical
  intro x
  have hxRed :
      x.1 ∈ N.paperRedRouting.toPathPacking.vertexSet := by
    by_contra hxRed
    exact x.2
      (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_red
        N.paperRedRouting N.paperBlueRouting hxRed)
  rcases (N.paperRedRouting.toPathPacking.mem_vertexSet).1 hxRed with
    ⟨i, hxi⟩
  have hxWalk :
      x.1 ∈ N.respecting.model.walkBranchUnion
        (N.redRouting.path i).walk := by
      exact
        (N.respecting.liftPerfectPathPackingWithBranchConnectors_path_vertexSet_subset_walkBranchUnion
        (MinorModel.BranchConnectorChoice.prefer
          N.respecting.model N.redLocalConnector
          N.redLocalConnector_vertexSet_subset_branchSet)
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
        N.redRouting i)
        (by simpa [TwoPairGoodMinor.paperRedRouting] using hxi)
  rw [MinorModel.walkBranchUnion] at hxWalk
  rcases Finset.mem_biUnion.1 hxWalk with ⟨w, _hw, hxw⟩
  exact ⟨w, hxw⟩

/-- If a high-degree host vertex in the paper-expanded red/blue union belongs
to a minor branch set `w`, then `w` lies on both selected minor routings. -/
theorem paperRouting_highVertex_branchSet_minorVertex_mem_red_blue
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {x : V} {w : W}
    (hxHigh :
      ¬ DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2)
    (hxw : x ∈ N.respecting.model.branchSet w) :
    w ∈ N.redRouting.toPathPacking.vertexSet ∧
      w ∈ N.blueRouting.toPathPacking.vertexSet := by
  classical
  have hxRed :
      x ∈ N.paperRedRouting.toPathPacking.vertexSet := by
    by_contra hxRed
    exact hxHigh
      (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_red
        N.paperRedRouting N.paperBlueRouting hxRed)
  have hxBlue :
      x ∈ N.paperBlueRouting.toPathPacking.vertexSet := by
    by_contra hxBlue
    exact hxHigh
      (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_blue
        N.paperRedRouting N.paperBlueRouting hxBlue)
  constructor
  · rcases (N.paperRedRouting.toPathPacking.mem_vertexSet).1 hxRed with
      ⟨i, hxi⟩
    have hxWalk :
        x ∈ N.respecting.model.walkBranchUnion
          (N.redRouting.path i).walk := by
      exact
        (N.respecting.liftPerfectPathPackingWithBranchConnectors_path_vertexSet_subset_walkBranchUnion
          (MinorModel.BranchConnectorChoice.prefer
            N.respecting.model N.redLocalConnector
            N.redLocalConnector_vertexSet_subset_branchSet)
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
          N.redRouting i)
          (by simpa [TwoPairGoodMinor.paperRedRouting] using hxi)
    have hwPath :
        w ∈ (N.redRouting.path i).vertexSet :=
      MinorModel.vertex_mem_of_branchSet_mem_walkBranchUnion
        N.respecting.model hxw hxWalk
    exact (N.redRouting.toPathPacking.mem_vertexSet).2 ⟨i, hwPath⟩
  · rcases (N.paperBlueRouting.toPathPacking.mem_vertexSet).1 hxBlue with
      ⟨j, hxj⟩
    have hxWalk :
        x ∈ N.respecting.model.walkBranchUnion
          (N.blueRouting.path j).walk := by
      exact
        (N.respecting.liftPerfectPathPackingWithBranchConnectors_path_vertexSet_subset_walkBranchUnion
          (MinorModel.BranchConnectorChoice.preferRerouteThrough
            N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
            N.redLocalConnector_vertexSet_subset_branchSet
            N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet)
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
          N.blueRouting j)
          (by simpa [TwoPairGoodMinor.paperBlueRouting] using hxj)
    have hwPath :
        w ∈ (N.blueRouting.path j).vertexSet :=
      MinorModel.vertex_mem_of_branchSet_mem_walkBranchUnion
        N.respecting.model hxw hxWalk
    exact (N.blueRouting.toPathPacking.mem_vertexSet).2 ⟨j, hwPath⟩

/-- A host vertex lying in a terminal branch set of a good minor is one of
the original host terminals. -/
theorem host_mem_terminalSet_of_mem_branchSet_terminal
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {x : V} {w : W}
    (hw : w ∈ N.terminalSet)
    (hxw : x ∈ N.respecting.model.branchSet w) :
    x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ := by
  classical
  have hwCases :
      w ∈ N.respecting.terminalImage S₁
            (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) ∨
        w ∈ N.respecting.terminalImage T₁
            (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) ∨
          w ∈ N.respecting.terminalImage S₂
              (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) ∨
            w ∈ N.respecting.terminalImage T₂
                (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
    simpa [terminalSet, twoPairTerminalSet] using hw
  rcases hwCases with hwS₁ | hwT₁ | hwS₂ | hwT₂
  · rcases
        (N.respecting.mem_terminalImage_iff S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) w).1 hwS₁ with
        ⟨t, ht, htw⟩
    have hbranch :
        N.respecting.model.branchSet
          (N.respecting.terminalVertex t
            ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) ht)) = {t} :=
      N.respecting.terminal_branchSet t
        ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) ht)
    have hxSingleton : x ∈ ({t} : Finset V) := by
      simpa [htw, hbranch] using hxw
    have hxt : x = t := by simpa using hxSingleton
    exact subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂ (by simpa [hxt] using ht)
  · rcases
        (N.respecting.mem_terminalImage_iff T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) w).1 hwT₁ with
        ⟨t, ht, htw⟩
    have hbranch :
        N.respecting.model.branchSet
          (N.respecting.terminalVertex t
            ((subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) ht)) = {t} :=
      N.respecting.terminal_branchSet t
        ((subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) ht)
    have hxSingleton : x ∈ ({t} : Finset V) := by
      simpa [htw, hbranch] using hxw
    have hxt : x = t := by simpa using hxSingleton
    exact subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂ (by simpa [hxt] using ht)
  · rcases
        (N.respecting.mem_terminalImage_iff S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) w).1 hwS₂ with
        ⟨t, ht, htw⟩
    have hbranch :
        N.respecting.model.branchSet
          (N.respecting.terminalVertex t
            ((subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) ht)) = {t} :=
      N.respecting.terminal_branchSet t
        ((subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) ht)
    have hxSingleton : x ∈ ({t} : Finset V) := by
      simpa [htw, hbranch] using hxw
    have hxt : x = t := by simpa using hxSingleton
    exact subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂ (by simpa [hxt] using ht)
  · rcases
        (N.respecting.mem_terminalImage_iff T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) w).1 hwT₂ with
        ⟨t, ht, htw⟩
    have hbranch :
        N.respecting.model.branchSet
          (N.respecting.terminalVertex t
            ((subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) ht)) = {t} :=
      N.respecting.terminal_branchSet t
        ((subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) ht)
    have hxSingleton : x ∈ ({t} : Finset V) := by
      simpa [htw, hbranch] using hxw
    have hxt : x = t := by simpa using hxSingleton
    exact subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂ (by simpa [hxt] using ht)

/-- Host terminals of degree one in the original graph cannot become
high-degree vertices in the union of the lifted good-minor routings. -/
theorem liftedRouting_degreeAtMost_two_of_mem_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    {x : V}
    (hxT : x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂) :
    DegreeAtMost
      (twoPackingUnionGraph N.liftRedRouting N.liftBlueRouting) x 2 := by
  have hG : DegreeAtMost G x 1 :=
    degreeAtMost_of_degreeEquals (hdeg x hxT)
  have hUnion : DegreeAtMost
      (twoPackingUnionGraph N.liftRedRouting N.liftBlueRouting) x 1 :=
    degreeAtMost_of_le hG
      (twoPackingUnionGraph_le N.liftRedRouting N.liftBlueRouting)
  exact DegreeAtMost.mono hUnion (by omega)

/-- Host terminals of degree one in the original graph cannot become
high-degree vertices in the union of the paper-expanded good-minor routings. -/
theorem paperRouting_degreeAtMost_two_of_mem_terminalSet
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    {x : V}
    (hxT : x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂) :
    DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
  have hG : DegreeAtMost G x 1 :=
    degreeAtMost_of_degreeEquals (hdeg x hxT)
  have hUnion : DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 1 :=
    degreeAtMost_of_le hG
      (twoPackingUnionGraph_le N.paperRedRouting N.paperBlueRouting)
  exact DegreeAtMost.mono hUnion (by omega)

/-- Local branch-set bound for the concrete red/blue routings obtained by
lifting a good minor's routings to the host graph. -/
def LiftedRoutingBranchSetLocalBound
    [Fintype V] [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) : Prop :=
  ∀ w : W,
    Fintype.card
      {x : {v : V //
          ¬ DegreeAtMost
            (twoPackingUnionGraph N.liftRedRouting N.liftBlueRouting) v 2} //
        x.1 ∈ N.respecting.model.branchSet w} ≤ 2

/-- Local branch-set bound for the paper-expanded routings: after blue local
connectors are cleaned or rerouted through the selected red local connector,
each minor branch set contributes at most two high-degree host vertices. -/
def PaperRoutingBranchSetLocalBound
    [Fintype V] [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) : Prop :=
  ∀ w : W,
    Fintype.card
      {x : {v : V //
          ¬ DegreeAtMost
            (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) v 2} //
        x.1 ∈ N.respecting.model.branchSet w} ≤ 2

/-- The naively lifted routings form a controlled expansion as soon as their
high-degree vertices have the paper's local `≤ 2` bound inside every branch
set. -/
noncomputable def controlledExpansionOfLiftedRoutingLocalBound
    [Fintype V] [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hlocal : N.LiftedRoutingBranchSetLocalBound) :
    TwoPairControlledExpansion (W := W) G S₁ T₁ S₂ T₂ :=
  TwoPairControlledExpansion.ofBranchSetLocalBound
    N.respecting.model N.liftRedRouting N.liftBlueRouting
    N.liftedRouting_highVertex_mem_branchSet hlocal

/-- The paper-expanded routings form a controlled expansion as soon as the
local branch-set `≤ 2` bound has been proved. -/
noncomputable def controlledExpansionOfPaperRoutingLocalBound
    [Fintype V] [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (hlocal : N.PaperRoutingBranchSetLocalBound) :
    TwoPairControlledExpansion (W := W) G S₁ T₁ S₂ T₂ :=
  TwoPairControlledExpansion.ofBranchSetLocalBound
    N.respecting.model N.paperRedRouting N.paperBlueRouting
    N.paperRouting_highVertex_mem_branchSet hlocal

/-- Pair-subset version of
`controlledExpansionOfLiftedRoutingLocalBound`, matching the paper's two
local splice vertices per branch set. -/
noncomputable def controlledExpansionOfLiftedRoutingPairBound
    [Fintype V] [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (a b : W → V)
    (hlocal :
      ∀ w : W,
        ∀ x : {v : V //
            ¬ DegreeAtMost
              (twoPackingUnionGraph N.liftRedRouting N.liftBlueRouting) v 2},
          x.1 ∈ N.respecting.model.branchSet w →
            x.1 = a w ∨ x.1 = b w) :
    TwoPairControlledExpansion (W := W) G S₁ T₁ S₂ T₂ :=
  TwoPairControlledExpansion.ofBranchSetLocalPairBound
    N.respecting.model N.liftRedRouting N.liftBlueRouting
    N.liftedRouting_highVertex_mem_branchSet a b hlocal

end TwoPairGoodMinor

/-- For two individual paths, every high-degree vertex in their union lies in
the intersection of the two path vertex sets.  Consequently, any finite set
covering that intersection bounds the branch-vertex count. -/
theorem branchVertexCount_twoSingletonPathUnion_le_of_inter_subset
    {G : _root_.SimpleGraph V} [Fintype V]
    (P Q : GraphPath G) {U : Finset V}
    (hU : P.vertexSet ∩ Q.vertexSet ⊆ U) :
    branchVertexCount
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking Q)) ≤ U.card := by
  classical
  change
    (Finset.univ.filter fun v : V =>
      ¬ DegreeAtMost
        (twoPackingUnionGraph
          (GraphPath.singletonPerfectPathPacking P)
          (GraphPath.singletonPerfectPathPacking Q)) v 2).card ≤ U.card
  refine Finset.card_le_card ?_
  intro v hv
  have hvHigh :
      ¬ DegreeAtMost
        (twoPackingUnionGraph
          (GraphPath.singletonPerfectPathPacking P)
          (GraphPath.singletonPerfectPathPacking Q)) v 2 :=
    (Finset.mem_filter.1 hv).2
  have hvP : v ∈ P.vertexSet := by
    by_contra hvP
    exact hvHigh
      (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_red
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking Q)
        (by simpa using hvP))
  have hvQ : v ∈ Q.vertexSet := by
    by_contra hvQ
    exact hvHigh
      (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_blue
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking Q)
        (by simpa using hvQ))
  exact hU (Finset.mem_inter.2 ⟨hvP, hvQ⟩)

/-- A two-path union has at most two branch vertices when the two paths meet
only inside a prescribed two-element set. -/
theorem branchVertexCount_twoSingletonPathUnion_le_two_of_inter_subset_pair
    {G : _root_.SimpleGraph V} [Fintype V]
    (P Q : GraphPath G) {u v : V}
    (hU : P.vertexSet ∩ Q.vertexSet ⊆ ({u, v} : Finset V)) :
    branchVertexCount
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking Q)) ≤ 2 := by
  have h :=
    branchVertexCount_twoSingletonPathUnion_le_of_inter_subset P Q hU
  exact h.trans (by
    calc
      ({u, v} : Finset V).card ≤ ({v} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp)

/-- If every blue path edge incident to `x` is already a red path edge, then
`x` has degree at most two in the union of the two singleton path packings. -/
theorem twoSingletonPathUnion_degreeAtMost_two_of_blue_incident_subset_red
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {x : V}
    (hsub : ∀ y : V, s(x, y) ∈ Q.edgeSet → s(x, y) ∈ P.edgeSet) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking Q)) x 2 := by
  classical
  let N := GraphPath.pathNeighborFinset P x
  refine ⟨N, ?_, GraphPath.pathNeighborFinset_card_le_two P x⟩
  intro y
  constructor
  · intro hy
    have he : s(x, y) ∈ P.edgeSet :=
      (GraphPath.mem_pathNeighborFinset P).mp hy |>.2
    have hne : x ≠ y := by
      have hadj : G.Adj x y := by
        simpa using GraphPath.edgeSet_subset_edgeSet P he
      exact hadj.ne
    exact (by
      simp [twoPackingUnionGraph, PathPacking.spanningGraph_adj_iff_exists_path_edge,
        GraphPath.singletonPerfectPathPacking, he, hne])
  · intro hxy
    have hred_or_blue :
        s(x, y) ∈ P.edgeSet ∨ s(x, y) ∈ Q.edgeSet := by
      have hxy' :
          ((GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph ⊔
            (GraphPath.singletonPerfectPathPacking Q).toPathPacking.spanningGraph).Adj x y := by
        simpa [twoPackingUnionGraph] using hxy
      rcases hxy' with hred | hblue
      · rcases
          (PathPacking.spanningGraph_adj_iff_exists_path_edge
            ((GraphPath.singletonPerfectPathPacking P).toPathPacking)).1 hred with
          ⟨⟨i, he⟩, _hne⟩
        exact Or.inl (by simpa using he)
      · rcases
          (PathPacking.spanningGraph_adj_iff_exists_path_edge
            ((GraphPath.singletonPerfectPathPacking Q).toPathPacking)).1 hblue with
          ⟨⟨i, he⟩, _hne⟩
        exact Or.inr (by simpa using he)
    have heP : s(x, y) ∈ P.edgeSet := by
      rcases hred_or_blue with he | he
      · exact he
      · exact hsub y he
    have hyP : y ∈ P.vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet P heP).2
    exact (GraphPath.mem_pathNeighborFinset P).2 ⟨hyP, heP⟩

/-- If a vertex does not lie in the intersection of two paths, then the union
of their singleton path packings has degree at most two at that vertex. -/
theorem twoSingletonPathUnion_degreeAtMost_two_of_not_mem_inter
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {x : V}
    (hx : x ∉ P.vertexSet ∩ Q.vertexSet) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking Q)) x 2 := by
  classical
  by_cases hxP : x ∈ P.vertexSet
  · have hxQ : x ∉ Q.vertexSet := by
      intro hxQ
      exact hx (Finset.mem_inter.2 ⟨hxP, hxQ⟩)
    have hred2 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph
          x 2 :=
      perfectPathPacking_spanningGraph_degreeAtMost_two
        (GraphPath.singletonPerfectPathPacking P) x
    have hblue0 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking Q).toPathPacking.spanningGraph
          x 0 :=
      pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem
        (GraphPath.singletonPerfectPathPacking Q).toPathPacking
        (by simpa [GraphPath.singletonPerfectPathPacking_vertexSet] using hxQ)
    simpa [twoPackingUnionGraph] using
      DegreeAtMost.mono (degreeAtMost_sup hred2 hblue0) (by omega)
  · have hred0 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph
          x 0 :=
      pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem
        (GraphPath.singletonPerfectPathPacking P).toPathPacking
        (by simpa [GraphPath.singletonPerfectPathPacking_vertexSet] using hxP)
    have hblue2 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking Q).toPathPacking.spanningGraph
          x 2 :=
      perfectPathPacking_spanningGraph_degreeAtMost_two
        (GraphPath.singletonPerfectPathPacking Q) x
    simpa [twoPackingUnionGraph] using
      DegreeAtMost.mono (degreeAtMost_sup hred0 hblue2) (by omega)

/-- Endpoint-strengthened version of
`twoSingletonPathUnion_degreeAtMost_two_of_blue_incident_subset_red`: if `x`
is an endpoint of the red path, then the local union has degree at most one at
`x`. -/
theorem twoSingletonPathUnion_degreeAtMost_one_of_red_endpoint_blue_incident_subset_red
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {x : V}
    (hxEndpoint : P.IsEndpoint x)
    (hsub : ∀ y : V, s(x, y) ∈ Q.edgeSet → s(x, y) ∈ P.edgeSet) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking Q)) x 1 := by
  classical
  let N := GraphPath.pathNeighborFinset P x
  refine ⟨N, ?_,
    GraphPath.pathNeighborFinset_card_le_one_of_isEndpoint P hxEndpoint⟩
  intro y
  constructor
  · intro hy
    have he : s(x, y) ∈ P.edgeSet :=
      (GraphPath.mem_pathNeighborFinset P).mp hy |>.2
    have hne : x ≠ y := by
      have hadj : G.Adj x y := by
        simpa using GraphPath.edgeSet_subset_edgeSet P he
      exact hadj.ne
    exact (by
      simp [twoPackingUnionGraph, PathPacking.spanningGraph_adj_iff_exists_path_edge,
        GraphPath.singletonPerfectPathPacking, he, hne])
  · intro hxy
    have hred_or_blue :
        s(x, y) ∈ P.edgeSet ∨ s(x, y) ∈ Q.edgeSet := by
      have hxy' :
          ((GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph ⊔
            (GraphPath.singletonPerfectPathPacking Q).toPathPacking.spanningGraph).Adj x y := by
        simpa [twoPackingUnionGraph] using hxy
      rcases hxy' with hred | hblue
      · rcases
          (PathPacking.spanningGraph_adj_iff_exists_path_edge
            ((GraphPath.singletonPerfectPathPacking P).toPathPacking)).1 hred with
          ⟨⟨i, he⟩, _hne⟩
        exact Or.inl (by simpa using he)
      · rcases
          (PathPacking.spanningGraph_adj_iff_exists_path_edge
            ((GraphPath.singletonPerfectPathPacking Q).toPathPacking)).1 hblue with
          ⟨⟨i, he⟩, _hne⟩
        exact Or.inr (by simpa using he)
    have heP : s(x, y) ∈ P.edgeSet := by
      rcases hred_or_blue with he | he
      · exact he
      · exact hsub y he
    have hyP : y ∈ P.vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet P heP).2
    exact (GraphPath.mem_pathNeighborFinset P).2 ⟨hyP, heP⟩

/-- A two-path union has at most two branch vertices when, away from two
splice vertices on the red path, every incident blue edge is already a red
path edge.  This is the local counting form used by the paper's branch-set
expansion. -/
theorem branchVertexCount_twoSingletonPathUnion_le_two_of_blue_incident_subset_red_except
    {G : _root_.SimpleGraph V} [Fintype V]
    (P Q : GraphPath G) {u v : V}
    (hsub :
      ∀ x : V, x ∈ P.vertexSet → x ≠ u → x ≠ v →
        ∀ y : V, s(x, y) ∈ Q.edgeSet → s(x, y) ∈ P.edgeSet) :
    branchVertexCount
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking Q)) ≤ 2 := by
  classical
  change
    (Finset.univ.filter fun x : V =>
      ¬ DegreeAtMost
        (twoPackingUnionGraph
          (GraphPath.singletonPerfectPathPacking P)
          (GraphPath.singletonPerfectPathPacking Q)) x 2).card ≤ 2
  have hsubset :
      (Finset.univ.filter fun x : V =>
        ¬ DegreeAtMost
          (twoPackingUnionGraph
            (GraphPath.singletonPerfectPathPacking P)
            (GraphPath.singletonPerfectPathPacking Q)) x 2) ⊆
        ({u, v} : Finset V) := by
    intro x hx
    have hxHigh :
        ¬ DegreeAtMost
          (twoPackingUnionGraph
            (GraphPath.singletonPerfectPathPacking P)
            (GraphPath.singletonPerfectPathPacking Q)) x 2 :=
      (Finset.mem_filter.1 hx).2
    by_cases hxu : x = u
    · simp [hxu]
    by_cases hxv : x = v
    · simp [hxv]
    have hxP : x ∈ P.vertexSet := by
      by_contra hxP
      exact hxHigh
        (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_red
          (GraphPath.singletonPerfectPathPacking P)
          (GraphPath.singletonPerfectPathPacking Q)
          (by simpa using hxP))
    exact False.elim
      (hxHigh
        (twoSingletonPathUnion_degreeAtMost_two_of_blue_incident_subset_red
          P Q (hsub x hxP hxu hxv)))
  exact (Finset.card_le_card hsubset).trans (by
    calc
      ({u, v} : Finset V).card ≤ ({v} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp)

/-- The paper's local branch-set rerouting count: a path plus a path rerouted
through it has at most two vertices of degree more than two. -/
theorem branchVertexCount_twoSingletonPathUnion_cleanRerouteThrough_le_two
    {G : _root_.SimpleGraph V} [Fintype V]
    (P Q : GraphPath G)
    (hne : (Q.vertexSet ∩ P.vertexSet).Nonempty) :
    branchVertexCount
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanRerouteThrough P Q hne))) ≤ 2 := by
  exact
    branchVertexCount_twoSingletonPathUnion_le_two_of_blue_incident_subset_red_except
      P (GraphPath.cleanRerouteThrough P Q hne)
      (u := Q.firstHitVertex P.vertexSet hne)
      (v := Q.lastHitVertex P.vertexSet hne)
      (GraphPath.cleanRerouteThrough_incident_subset_red_except P Q hne)

/-- Degree version of the local rerouting count: away from the first and last
intersections of the preliminary blue path with the red path, the union of the
red path and the rerouted blue path has degree at most two. -/
theorem twoSingletonPathUnion_cleanRerouteThrough_degreeAtMost_two_except
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G)
    (hne : (Q.vertexSet ∩ P.vertexSet).Nonempty)
    {x : V}
    (hxFirst : x ≠ Q.firstHitVertex P.vertexSet hne)
    (hxLast : x ≠ Q.lastHitVertex P.vertexSet hne) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanRerouteThrough P Q hne))) x 2 := by
  classical
  by_cases hxP : x ∈ P.vertexSet
  · exact
      twoSingletonPathUnion_degreeAtMost_two_of_blue_incident_subset_red
        P (GraphPath.cleanRerouteThrough P Q hne)
        (GraphPath.cleanRerouteThrough_incident_subset_red_except
          P Q hne x hxP hxFirst hxLast)
  · have hred0 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph
          x 0 :=
      pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem
        (GraphPath.singletonPerfectPathPacking P).toPathPacking
        (by simpa [GraphPath.singletonPerfectPathPacking_vertexSet] using hxP)
    have hblue2 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking
            (GraphPath.cleanRerouteThrough P Q hne)).toPathPacking.spanningGraph
          x 2 :=
      perfectPathPacking_spanningGraph_degreeAtMost_two
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanRerouteThrough P Q hne)) x
    simpa [twoPackingUnionGraph] using
      DegreeAtMost.mono (degreeAtMost_sup hred0 hblue2) (by omega)

/-- The local count for the paper's case split: if the preliminary blue
connector is disjoint from the red connector there are no local branch
vertices; otherwise `cleanRerouteThrough` leaves at most the two splice
vertices. -/
theorem branchVertexCount_twoSingletonPathUnion_cleanOrDisjointReroute_le_two
    {G : _root_.SimpleGraph V} [Fintype V]
    (P Q : GraphPath G) :
    branchVertexCount
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanOrDisjointReroute P Q))) ≤ 2 := by
  classical
  by_cases hne : (Q.vertexSet ∩ P.vertexSet).Nonempty
  · unfold GraphPath.cleanOrDisjointReroute
    rw [dif_pos hne]
    exact
      branchVertexCount_twoSingletonPathUnion_cleanRerouteThrough_le_two
        P Q hne
  · have hinter_empty :
        P.vertexSet ∩ Q.vertexSet ⊆ (∅ : Finset V) := by
      intro x hx
      have hx' : x ∈ Q.vertexSet ∩ P.vertexSet := by
        exact Finset.mem_inter.2
          ⟨(Finset.mem_inter.1 hx).2, (Finset.mem_inter.1 hx).1⟩
      exact False.elim (hne ⟨x, hx'⟩)
    have hzero :
        branchVertexCount
          (twoPackingUnionGraph
            (GraphPath.singletonPerfectPathPacking P)
            (GraphPath.singletonPerfectPathPacking Q)) ≤ 0 :=
      branchVertexCount_twoSingletonPathUnion_le_of_inter_subset
        P Q hinter_empty
    have htwo :
        branchVertexCount
          (twoPackingUnionGraph
            (GraphPath.singletonPerfectPathPacking P)
            (GraphPath.singletonPerfectPathPacking Q)) ≤ 2 :=
      hzero.trans (by omega)
    unfold GraphPath.cleanOrDisjointReroute
    rw [dif_neg hne]
    exact htwo

/-- Pointwise form of the paper's local case split: away from the two splice
vertices selected in the intersecting case, the local union of a red connector
and the cleaned-or-disjoint blue connector has degree at most two.  In the
disjoint case the blue connector is unchanged and the two paths have empty
intersection. -/
theorem twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_two_except
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {x : V}
    (hxFirst :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.firstHitVertex P.vertexSet hne)
    (hxLast :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.lastHitVertex P.vertexSet hne) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanOrDisjointReroute P Q))) x 2 := by
  classical
  by_cases hne : (Q.vertexSet ∩ P.vertexSet).Nonempty
  · unfold GraphPath.cleanOrDisjointReroute
    rw [dif_pos hne]
    exact
      twoSingletonPathUnion_cleanRerouteThrough_degreeAtMost_two_except
        P Q hne (hxFirst hne) (hxLast hne)
  · have hxNotInter : x ∉ P.vertexSet ∩ Q.vertexSet := by
      intro hx
      exact hne ⟨x, Finset.mem_inter.2
        ⟨(Finset.mem_inter.1 hx).2, (Finset.mem_inter.1 hx).1⟩⟩
    unfold GraphPath.cleanOrDisjointReroute
    rw [dif_neg hne]
    exact twoSingletonPathUnion_degreeAtMost_two_of_not_mem_inter P Q hxNotInter

namespace TwoPairGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- The paper's local count inside one branch set: the red local connector and
the cleaned/rerouted blue local connector have at most two high-degree vertices
in their union. -/
theorem localConnector_branchVertexCount_le_two
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) :
    branchVertexCount
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
        (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))) ≤ 2 := by
  simpa [TwoPairGoodMinor.blueLocalConnector] using
    branchVertexCount_twoSingletonPathUnion_cleanOrDisjointReroute_le_two
      (N.redLocalConnector w) (N.bluePreliminaryLocalConnector w)

/-- Pointwise local degree bound for one branch set, away from the paper's two
splice vertices. -/
theorem localConnector_degreeAtMost_two_of_not_splice
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) {x : V}
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
        (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))) x 2 := by
  classical
  have hFirst :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).firstHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hfirst :
        N.paperLocalSpliceFirst w =
          (N.bluePreliminaryLocalConnector w).firstHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceFirst_eq_of_inter_nonempty w hne
    intro hx
    exact hxFirst (hx.trans hfirst.symm)
  have hLast :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).lastHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hlast :
        N.paperLocalSpliceLast w =
          (N.bluePreliminaryLocalConnector w).lastHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceLast_eq_of_inter_nonempty w hne
    intro hx
    exact hxLast (hx.trans hlast.symm)
  simpa [TwoPairGoodMinor.blueLocalConnector] using
    twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_two_except
      (N.redLocalConnector w) (N.bluePreliminaryLocalConnector w)
      (x := x) hFirst hLast

/-- Global paper-routing degree bound for a nonterminal branch vertex that is
neither a local splice nor one of the four branch-boundary connector endpoints.
The only global adjacencies not present in the local two-connector union are
the boundary crossings, and those are excluded by the endpoint hypotheses. -/
theorem paperRouting_degreeAtMost_two_of_mem_branchSet_not_endpoint_not_splice
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x : V}
    (hwT : w ∉ N.terminalSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w)
    (hxRedSource : x ≠ (N.redLocalConnector w).source)
    (hxRedTarget : x ≠ (N.redLocalConnector w).target)
    (hxBlueSource : x ≠ (N.blueLocalConnector w).source)
    (hxBlueTarget : x ≠ (N.blueLocalConnector w).target) :
    DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
  classical
  let L :=
    twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))
  have hlocal : DegreeAtMost L x 2 := by
    simpa [L] using N.localConnector_degreeAtMost_two_of_not_splice
      w hxFirst hxLast
  have hglobal :
      DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x
        (2 + 0) := by
    refine degreeAtMost_of_adj_imp_local_or_mem hlocal ∅ ?_ (by simp)
    intro y hxy
    rcases
        N.paperRouting_adj_incident_branchSet_local_or_endpoint
          hwT hxw hxy with hxyLocal | hEndpoint
    · exact Or.inl (by simpa [L] using hxyLocal)
    · rcases hEndpoint with hRedSource | hEndpoint
      · exact False.elim (hxRedSource hRedSource)
      · rcases hEndpoint with hRedTarget | hEndpoint
        · exact False.elim (hxRedTarget hRedTarget)
        · rcases hEndpoint with hBlueSource | hBlueTarget
          · exact False.elim (hxBlueSource hBlueSource)
          · exact False.elim (hxBlueTarget hBlueTarget)
  simpa using hglobal

end TwoPairGoodMinor

/-- Endpoint form of the local branch-set rerouting count: away from the two
splice vertices, a red endpoint has local degree at most one after the blue
path is rerouted through the red path. -/
theorem twoSingletonPathUnion_cleanRerouteThrough_degreeAtMost_one_of_red_endpoint_except
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G)
    (hne : (Q.vertexSet ∩ P.vertexSet).Nonempty)
    {x : V}
    (hxEndpoint : P.IsEndpoint x)
    (hxFirst : x ≠ Q.firstHitVertex P.vertexSet hne)
    (hxLast : x ≠ Q.lastHitVertex P.vertexSet hne) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanRerouteThrough P Q hne))) x 1 := by
  have hxP : x ∈ P.vertexSet := by
    rcases hxEndpoint with rfl | rfl
    · exact GraphPath.source_mem_vertexSet P
    · exact GraphPath.target_mem_vertexSet P
  exact
    twoSingletonPathUnion_degreeAtMost_one_of_red_endpoint_blue_incident_subset_red
      P (GraphPath.cleanRerouteThrough P Q hne) hxEndpoint
      (GraphPath.cleanRerouteThrough_incident_subset_red_except
        P Q hne x hxP hxFirst hxLast)

/-- Symmetric endpoint form for the rerouted blue connector: away from the
two splice vertices, a blue endpoint has local degree at most one in the
red/rerouted-blue union. -/
theorem twoSingletonPathUnion_cleanRerouteThrough_degreeAtMost_one_of_blue_endpoint_except
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G)
    (hne : (Q.vertexSet ∩ P.vertexSet).Nonempty)
    {x : V}
    (hxEndpoint : (GraphPath.cleanRerouteThrough P Q hne).IsEndpoint x)
    (hxFirst : x ≠ Q.firstHitVertex P.vertexSet hne)
    (hxLast : x ≠ Q.lastHitVertex P.vertexSet hne) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanRerouteThrough P Q hne))) x 1 := by
  classical
  have hxBlueEndpointQ : x = Q.source ∨ x = Q.target := by
    rcases hxEndpoint with hx | hx
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by simpa using hx)
  by_cases hxP : x ∈ P.vertexSet
  · rcases hxBlueEndpointQ with hxSource | hxTarget
    · have hsourceFirst :
          Q.source = Q.firstHitVertex P.vertexSet hne :=
        GraphPath.source_eq_firstHitVertex_of_source_mem_set
          Q P.vertexSet hne (by simpa [hxSource] using hxP)
      exact False.elim (hxFirst (hxSource.trans hsourceFirst))
    · have htargetLast :
          Q.target = Q.lastHitVertex P.vertexSet hne :=
        GraphPath.target_eq_lastHitVertex_of_target_mem_set
          Q P.vertexSet hne (by simpa [hxTarget] using hxP)
      exact False.elim (hxLast (hxTarget.trans htargetLast))
  · have hred0 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph
          x 0 :=
      pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem
        (GraphPath.singletonPerfectPathPacking P).toPathPacking
        (by simpa [GraphPath.singletonPerfectPathPacking_vertexSet] using hxP)
    have hblue1 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking
            (GraphPath.cleanRerouteThrough P Q hne)).toPathPacking.spanningGraph
          x 1 :=
      GraphPath.singletonPerfectPathPacking_spanningGraph_degreeAtMost_one_of_isEndpoint
        (GraphPath.cleanRerouteThrough P Q hne) hxEndpoint
    simpa [twoPackingUnionGraph] using
      DegreeAtMost.mono (degreeAtMost_sup hred0 hblue1) (by omega)

/-- Endpoint form for the paper's local case split: away from the two splice
vertices, a red endpoint has local degree at most one whether the preliminary
blue connector is disjoint from the red connector or rerouted through it. -/
theorem twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_one_of_red_endpoint_except
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {x : V}
    (hxEndpoint : P.IsEndpoint x)
    (hxFirst :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.firstHitVertex P.vertexSet hne)
    (hxLast :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.lastHitVertex P.vertexSet hne) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanOrDisjointReroute P Q))) x 1 := by
  classical
  by_cases hne : (Q.vertexSet ∩ P.vertexSet).Nonempty
  · unfold GraphPath.cleanOrDisjointReroute
    rw [dif_pos hne]
    exact
      twoSingletonPathUnion_cleanRerouteThrough_degreeAtMost_one_of_red_endpoint_except
        P Q hne hxEndpoint (hxFirst hne) (hxLast hne)
  · have hxP : x ∈ P.vertexSet := by
      rcases hxEndpoint with rfl | rfl
      · exact GraphPath.source_mem_vertexSet P
      · exact GraphPath.target_mem_vertexSet P
    have hxQ : x ∉ Q.vertexSet := by
      intro hxQ
      exact hne ⟨x, Finset.mem_inter.2 ⟨hxQ, hxP⟩⟩
    have hred1 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph
          x 1 :=
      GraphPath.singletonPerfectPathPacking_spanningGraph_degreeAtMost_one_of_isEndpoint
        P hxEndpoint
    have hblue0 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking Q).toPathPacking.spanningGraph
          x 0 :=
      pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem
        (GraphPath.singletonPerfectPathPacking Q).toPathPacking
        (by simpa [GraphPath.singletonPerfectPathPacking_vertexSet] using hxQ)
    unfold GraphPath.cleanOrDisjointReroute
    rw [dif_neg hne]
    simpa [twoPackingUnionGraph] using
      DegreeAtMost.mono (degreeAtMost_sup hred1 hblue0) (by omega)

/-- Symmetric endpoint form for the paper's local case split: away from the
two splice vertices, a blue endpoint has local degree at most one whether the
preliminary blue connector is disjoint from the red connector or rerouted
through it. -/
theorem twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_one_of_blue_endpoint_except
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {x : V}
    (hxEndpoint : (GraphPath.cleanOrDisjointReroute P Q).IsEndpoint x)
    (hxFirst :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.firstHitVertex P.vertexSet hne)
    (hxLast :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.lastHitVertex P.vertexSet hne) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanOrDisjointReroute P Q))) x 1 := by
  classical
  by_cases hne : (Q.vertexSet ∩ P.vertexSet).Nonempty
  · unfold GraphPath.cleanOrDisjointReroute at hxEndpoint ⊢
    rw [dif_pos hne] at hxEndpoint ⊢
    exact
      twoSingletonPathUnion_cleanRerouteThrough_degreeAtMost_one_of_blue_endpoint_except
        P Q hne hxEndpoint (hxFirst hne) (hxLast hne)
  · unfold GraphPath.cleanOrDisjointReroute at hxEndpoint ⊢
    rw [dif_neg hne] at hxEndpoint ⊢
    have hxQ : x ∈ Q.vertexSet := by
      rcases hxEndpoint with rfl | rfl
      · exact GraphPath.source_mem_vertexSet Q
      · exact GraphPath.target_mem_vertexSet Q
    have hxP : x ∉ P.vertexSet := by
      intro hxP
      exact hne ⟨x, Finset.mem_inter.2 ⟨hxQ, hxP⟩⟩
    have hred0 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph
          x 0 :=
      pathPacking_spanningGraph_degreeAtMost_zero_of_not_mem
        (GraphPath.singletonPerfectPathPacking P).toPathPacking
        (by simpa [GraphPath.singletonPerfectPathPacking_vertexSet] using hxP)
    have hblue1 :
        DegreeAtMost
          (GraphPath.singletonPerfectPathPacking Q).toPathPacking.spanningGraph
          x 1 :=
      GraphPath.singletonPerfectPathPacking_spanningGraph_degreeAtMost_one_of_isEndpoint
        Q hxEndpoint
    simpa [twoPackingUnionGraph] using
      DegreeAtMost.mono (degreeAtMost_sup hred0 hblue1) (by omega)

/-- If the red connector has collapsed to a point, then away from the two
splice positions the local red/rerouted-blue union has degree zero at that
point. -/
theorem twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_zero_of_red_source_eq_target_except
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {x : V}
    (hxSource : x = P.source)
    (hxTarget : x = P.target)
    (hxFirst :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.firstHitVertex P.vertexSet hne)
    (hxLast :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.lastHitVertex P.vertexSet hne) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanOrDisjointReroute P Q))) x 0 := by
  classical
  have hxP : x ∈ P.vertexSet := by
    simpa [hxSource] using GraphPath.source_mem_vertexSet P
  have hst : P.source = P.target := hxSource.symm.trans hxTarget
  have hPempty : P.edgeSet = ∅ :=
    GraphPath.edgeSet_eq_empty_of_source_eq_target P hst
  refine ⟨∅, ?_, by simp⟩
  intro y
  constructor
  · intro hy
    simp at hy
  · intro hxy
    have hcases :
        (GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph.Adj x y ∨
          (GraphPath.singletonPerfectPathPacking
            (GraphPath.cleanOrDisjointReroute P Q)).toPathPacking.spanningGraph.Adj x y := by
      simpa [twoPackingUnionGraph] using hxy
    rcases hcases with hred | hblue
    · rcases
        (PathPacking.spanningGraph_adj_iff_exists_path_edge
          ((GraphPath.singletonPerfectPathPacking P).toPathPacking)).1
          hred with
        ⟨⟨i, he⟩, _hne⟩
      have heP : s(x, y) ∈ P.edgeSet := by
        simpa using he
      simp [hPempty] at heP
    · rcases
        (PathPacking.spanningGraph_adj_iff_exists_path_edge
          ((GraphPath.singletonPerfectPathPacking
            (GraphPath.cleanOrDisjointReroute P Q)).toPathPacking)).1
          hblue with
        ⟨⟨i, he⟩, _hne⟩
      by_cases hne : (Q.vertexSet ∩ P.vertexSet).Nonempty
      · have heBlue :
            s(x, y) ∈ (GraphPath.cleanRerouteThrough P Q hne).edgeSet := by
          simpa [GraphPath.cleanOrDisjointReroute, hne] using he
        have heP :
            s(x, y) ∈ P.edgeSet :=
          GraphPath.cleanRerouteThrough_incident_subset_red_except
            P Q hne x hxP (hxFirst hne) (hxLast hne) y heBlue
        simp [hPempty] at heP
      · have heQ :
            s(x, y) ∈ Q.edgeSet := by
          simpa [GraphPath.cleanOrDisjointReroute, hne] using he
        have hxQ : x ∈ Q.vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q heQ).1
        exact False.elim
          (hne ⟨x, Finset.mem_inter.2 ⟨hxQ, hxP⟩⟩)

/-- Symmetric degenerate local bound: if the cleaned blue connector has
collapsed to a point, then away from the two splice positions the local
red/blue union has degree zero at that point. -/
theorem twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_zero_of_blue_source_eq_target_except
    {G : _root_.SimpleGraph V}
    (P Q : GraphPath G) {x : V}
    (hxSource : x = (GraphPath.cleanOrDisjointReroute P Q).source)
    (hxTarget : x = (GraphPath.cleanOrDisjointReroute P Q).target)
    (hxFirst :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.firstHitVertex P.vertexSet hne)
    (hxLast :
      ∀ hne : (Q.vertexSet ∩ P.vertexSet).Nonempty,
        x ≠ Q.lastHitVertex P.vertexSet hne) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking P)
        (GraphPath.singletonPerfectPathPacking
          (GraphPath.cleanOrDisjointReroute P Q))) x 0 := by
  classical
  have hxQSource : x = Q.source := by
    simpa using hxSource
  have hxQTarget : x = Q.target := by
    simpa using hxTarget
  have hxQ : x ∈ Q.vertexSet := by
    simpa [hxQSource] using GraphPath.source_mem_vertexSet Q
  have hQst : Q.source = Q.target := hxQSource.symm.trans hxQTarget
  refine ⟨∅, ?_, by simp⟩
  intro y
  constructor
  · intro hy
    simp at hy
  · intro hxy
    have hcases :
        (GraphPath.singletonPerfectPathPacking P).toPathPacking.spanningGraph.Adj x y ∨
          (GraphPath.singletonPerfectPathPacking
            (GraphPath.cleanOrDisjointReroute P Q)).toPathPacking.spanningGraph.Adj x y := by
      simpa [twoPackingUnionGraph] using hxy
    rcases hcases with hred | hblue
    · rcases
        (PathPacking.spanningGraph_adj_iff_exists_path_edge
          ((GraphPath.singletonPerfectPathPacking P).toPathPacking)).1
          hred with
        ⟨⟨i, he⟩, _hne⟩
      have hxP : x ∈ P.vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet P (by simpa using he)).1
      have hne : (Q.vertexSet ∩ P.vertexSet).Nonempty :=
        ⟨x, Finset.mem_inter.2 ⟨hxQ, hxP⟩⟩
      have hsourceFirst :
          Q.source = Q.firstHitVertex P.vertexSet hne :=
        GraphPath.source_eq_firstHitVertex_of_source_mem_set
          Q P.vertexSet hne (by simpa [hxQSource] using hxP)
      exact False.elim (hxFirst hne (hxQSource.trans hsourceFirst))
    · rcases
        (PathPacking.spanningGraph_adj_iff_exists_path_edge
          ((GraphPath.singletonPerfectPathPacking
            (GraphPath.cleanOrDisjointReroute P Q)).toPathPacking)).1
          hblue with
        ⟨⟨i, he⟩, _hne⟩
      have hBlueEmpty :
          (GraphPath.cleanOrDisjointReroute P Q).edgeSet = ∅ :=
        GraphPath.edgeSet_eq_empty_of_source_eq_target
          (GraphPath.cleanOrDisjointReroute P Q)
          (hxSource.symm.trans hxTarget)
      have heBlue :
          s(x, y) ∈ (GraphPath.cleanOrDisjointReroute P Q).edgeSet := by
        simpa using he
      simp [hBlueEmpty] at heBlue

namespace TwoPairGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- Local endpoint bound inside one branch set for a red connector endpoint,
away from the two paper splice vertices. -/
theorem localConnector_degreeAtMost_one_of_red_endpoint_not_splice
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) {x : V}
    (hxEndpoint : (N.redLocalConnector w).IsEndpoint x)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
        (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))) x 1 := by
  classical
  have hFirst :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).firstHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hfirst :
        N.paperLocalSpliceFirst w =
          (N.bluePreliminaryLocalConnector w).firstHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceFirst_eq_of_inter_nonempty w hne
    intro hx
    exact hxFirst (hx.trans hfirst.symm)
  have hLast :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).lastHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hlast :
        N.paperLocalSpliceLast w =
          (N.bluePreliminaryLocalConnector w).lastHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceLast_eq_of_inter_nonempty w hne
    intro hx
    exact hxLast (hx.trans hlast.symm)
  simpa [TwoPairGoodMinor.blueLocalConnector] using
    twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_one_of_red_endpoint_except
      (N.redLocalConnector w) (N.bluePreliminaryLocalConnector w)
      (x := x) hxEndpoint hFirst hLast

/-- Local endpoint bound inside one branch set for a blue connector endpoint,
away from the two paper splice vertices. -/
theorem localConnector_degreeAtMost_one_of_blue_endpoint_not_splice
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) {x : V}
    (hxEndpoint : (N.blueLocalConnector w).IsEndpoint x)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
        (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))) x 1 := by
  classical
  have hFirst :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).firstHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hfirst :
        N.paperLocalSpliceFirst w =
          (N.bluePreliminaryLocalConnector w).firstHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceFirst_eq_of_inter_nonempty w hne
    intro hx
    exact hxFirst (hx.trans hfirst.symm)
  have hLast :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).lastHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hlast :
        N.paperLocalSpliceLast w =
          (N.bluePreliminaryLocalConnector w).lastHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceLast_eq_of_inter_nonempty w hne
    intro hx
    exact hxLast (hx.trans hlast.symm)
  simpa [TwoPairGoodMinor.blueLocalConnector] using
    twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_one_of_blue_endpoint_except
      (N.redLocalConnector w) (N.bluePreliminaryLocalConnector w)
      (x := x) (by simpa [TwoPairGoodMinor.blueLocalConnector] using hxEndpoint)
      hFirst hLast

/-- Degenerate local red endpoint bound: when the red connector source and
target coincide, a non-splice copy of that endpoint has no local incident
edges in the red/cleaned-blue union. -/
theorem localConnector_degreeAtMost_zero_of_red_source_eq_target_not_splice
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) {x : V}
    (hxSource : x = (N.redLocalConnector w).source)
    (hxTarget : x = (N.redLocalConnector w).target)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
        (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))) x 0 := by
  classical
  have hFirst :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).firstHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hfirst :
        N.paperLocalSpliceFirst w =
          (N.bluePreliminaryLocalConnector w).firstHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceFirst_eq_of_inter_nonempty w hne
    intro hx
    exact hxFirst (hx.trans hfirst.symm)
  have hLast :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).lastHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hlast :
        N.paperLocalSpliceLast w =
          (N.bluePreliminaryLocalConnector w).lastHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceLast_eq_of_inter_nonempty w hne
    intro hx
    exact hxLast (hx.trans hlast.symm)
  simpa [TwoPairGoodMinor.blueLocalConnector] using
    twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_zero_of_red_source_eq_target_except
      (N.redLocalConnector w) (N.bluePreliminaryLocalConnector w)
      (x := x) hxSource hxTarget hFirst hLast

/-- Degenerate local blue endpoint bound: when the cleaned blue connector
source and target coincide, a non-splice copy of that endpoint has no local
incident edges in the red/cleaned-blue union. -/
theorem localConnector_degreeAtMost_zero_of_blue_source_eq_target_not_splice
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W) {x : V}
    (hxSource : x = (N.blueLocalConnector w).source)
    (hxTarget : x = (N.blueLocalConnector w).target)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w) :
    DegreeAtMost
      (twoPackingUnionGraph
        (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
        (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))) x 0 := by
  classical
  have hFirst :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).firstHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hfirst :
        N.paperLocalSpliceFirst w =
          (N.bluePreliminaryLocalConnector w).firstHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceFirst_eq_of_inter_nonempty w hne
    intro hx
    exact hxFirst (hx.trans hfirst.symm)
  have hLast :
      ∀ hne :
          ((N.bluePreliminaryLocalConnector w).vertexSet ∩
            (N.redLocalConnector w).vertexSet).Nonempty,
        x ≠ (N.bluePreliminaryLocalConnector w).lastHitVertex
          (N.redLocalConnector w).vertexSet hne := by
    intro hne
    have hlast :
        N.paperLocalSpliceLast w =
          (N.bluePreliminaryLocalConnector w).lastHitVertex
            (N.redLocalConnector w).vertexSet hne :=
      N.paperLocalSpliceLast_eq_of_inter_nonempty w hne
    intro hx
    exact hxLast (hx.trans hlast.symm)
  simpa [TwoPairGoodMinor.blueLocalConnector] using
    twoSingletonPathUnion_cleanOrDisjointReroute_degreeAtMost_zero_of_blue_source_eq_target_except
      (N.redLocalConnector w) (N.bluePreliminaryLocalConnector w)
      (x := x)
      (by simpa [TwoPairGoodMinor.blueLocalConnector] using hxSource)
      (by simpa [TwoPairGoodMinor.blueLocalConnector] using hxTarget)
      hFirst hLast

/-- If the source of the cleaned blue connector lies on the red local
connector, it is exactly the first paper splice vertex. -/
theorem blueLocalConnector_source_eq_spliceFirst_of_mem_red
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W)
    (hx :
      (N.blueLocalConnector w).source ∈
        (N.redLocalConnector w).vertexSet) :
    (N.blueLocalConnector w).source = N.paperLocalSpliceFirst w := by
  classical
  let Q := N.bluePreliminaryLocalConnector w
  let R := N.redLocalConnector w
  have hxQ : Q.source ∈ R.vertexSet := by
    simpa [Q, R, TwoPairGoodMinor.blueLocalConnector] using hx
  by_cases hne : (Q.vertexSet ∩ R.vertexSet).Nonempty
  · have hsource :
        Q.source = Q.firstHitVertex R.vertexSet hne :=
      GraphPath.source_eq_firstHitVertex_of_source_mem_set
        Q R.vertexSet hne hxQ
    have hsplice :
        N.paperLocalSpliceFirst w =
          Q.firstHitVertex R.vertexSet hne := by
      simpa [Q, R] using N.paperLocalSpliceFirst_eq_of_inter_nonempty w hne
    simpa [Q, R, TwoPairGoodMinor.blueLocalConnector, hsource, hsplice]
  · have hsplice :
        N.paperLocalSpliceFirst w = Q.source := by
      simpa [Q, R] using N.paperLocalSpliceFirst_eq_of_inter_empty w hne
    simpa [Q, R, TwoPairGoodMinor.blueLocalConnector, hsplice]

/-- If the target of the cleaned blue connector lies on the red local
connector, it is exactly the last paper splice vertex. -/
theorem blueLocalConnector_target_eq_spliceLast_of_mem_red
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) (w : W)
    (hx :
      (N.blueLocalConnector w).target ∈
        (N.redLocalConnector w).vertexSet) :
    (N.blueLocalConnector w).target = N.paperLocalSpliceLast w := by
  classical
  let Q := N.bluePreliminaryLocalConnector w
  let R := N.redLocalConnector w
  have hxQ : Q.target ∈ R.vertexSet := by
    simpa [Q, R, TwoPairGoodMinor.blueLocalConnector] using hx
  by_cases hne : (Q.vertexSet ∩ R.vertexSet).Nonempty
  · have htarget :
        Q.target = Q.lastHitVertex R.vertexSet hne :=
      GraphPath.target_eq_lastHitVertex_of_target_mem_set
        Q R.vertexSet hne hxQ
    have hsplice :
        N.paperLocalSpliceLast w =
          Q.lastHitVertex R.vertexSet hne := by
      simpa [Q, R] using N.paperLocalSpliceLast_eq_of_inter_nonempty w hne
    simpa [Q, R, TwoPairGoodMinor.blueLocalConnector, htarget, hsplice]
  · have hsplice :
        N.paperLocalSpliceLast w = Q.target := by
      simpa [Q, R] using N.paperLocalSpliceLast_eq_of_inter_empty w hne
    simpa [Q, R, TwoPairGoodMinor.blueLocalConnector, hsplice]

/-- A non-splice red-source boundary vertex has global degree at most two,
provided it is not also the red target or a blue boundary endpoint.  The local
two-connector union contributes at most one neighbor, and the only remaining
red adjacency is the unique crossing edge into the branch set. -/
theorem paperRouting_degreeAtMost_two_of_mem_branchSet_red_source_not_other_endpoint
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x : V}
    (hwT : w ∉ N.terminalSet)
    (hwR : w ∈ N.redRouting.toPathPacking.vertexSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w)
    (hxSource : x = (N.redLocalConnector w).source)
    (hxNotRedTarget : x ≠ (N.redLocalConnector w).target)
    (hxNotBlueSource : x ≠ (N.blueLocalConnector w).source)
    (hxNotBlueTarget : x ≠ (N.blueLocalConnector w).target) :
    DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
  classical
  rcases (N.redRouting.toPathPacking.mem_vertexSet).1 hwR with
    ⟨i₀, hwPath₀⟩
  have hwInternal₀ :=
    N.red_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (i := i₀)
  let prevExists :=
    GraphPath.exists_backward_edge_of_mem_not_source
      (N.redRouting.path i₀) hwPath₀ hwInternal₀.1
  let prev₀ : W := Classical.choose prevExists
  have hprev₀Edge : s(prev₀, w) ∈ (N.redRouting.path i₀).edgeSet :=
    (Classical.choose_spec prevExists).1
  have hprev₀Before : (N.redRouting.path i₀).Before prev₀ w :=
    (Classical.choose_spec prevExists).2.1
  have hprev₀_ne : prev₀ ≠ w :=
    (Classical.choose_spec prevExists).2.2
  have hprev₀Adj : H.Adj prev₀ w := by
    have hEdge : s(prev₀, w) ∈ H.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i₀) hprev₀Edge
    simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
  let z : V := MinorModel.edgeLeft N.respecting.model hprev₀Adj
  let L :=
    twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))
  have hlocal : DegreeAtMost L x 1 := by
    have hxEndpoint : (N.redLocalConnector w).IsEndpoint x := Or.inl hxSource
    simpa [L] using
      N.localConnector_degreeAtMost_one_of_red_endpoint_not_splice
        w hxEndpoint hxFirst hxLast
  have hglobal :
      DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x
        (1 + 1) := by
    refine degreeAtMost_of_adj_imp_local_or_mem hlocal {z} ?_ (by simp)
    intro y hxy
    have hcases :
        N.paperRedRouting.toPathPacking.spanningGraph.Adj x y ∨
          N.paperBlueRouting.toPathPacking.spanningGraph.Adj x y := by
      simpa [twoPackingUnionGraph] using hxy
    rcases hcases with hred | hblue
    · rcases
        (N.paperRedRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hred with
        ⟨⟨i, he⟩, _hne⟩
      let C :=
        MinorModel.BranchConnectorChoice.prefer
          N.respecting.model N.redLocalConnector
          N.redLocalConnector_vertexSet_subset_branchSet
      have hclass :=
        N.respecting.liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
          C
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
          N.redRouting i
          (by simpa [TwoPairGoodMinor.paperRedRouting, C] using he)
      dsimp only at hclass
      rcases hclass with hlocalUse | hcross
      · rcases hlocalUse with ⟨z₀, p, q, hp, hq, huse, heC⟩
        have hxC : x ∈ (C.path z₀ hp hq).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet (C.path z₀ hp hq) heC).1
        have hxz₀ : x ∈ N.respecting.model.branchSet z₀ :=
          C.vertexSet_subset z₀ hp hq hxC
        have hz₀w : z₀ = w := by
          by_contra hne
          exact Finset.disjoint_left.mp (N.respecting.model.branch_disjoint hne)
            hxz₀ hxw
        subst z₀
        have hsrc : (N.redLocalConnector w).source = p := by
          rcases
              MinorModel.liftWalkLocalUse_left_endpoint_or_crossing
                N.respecting.model huse with hstart | hprev
          · rcases hstart with ⟨hwSource, _hp⟩
            exact False.elim
              (hwT (by
                simpa [hwSource] using N.red_source_mem_terminalSet i))
          · rcases hprev with ⟨prev, hprev, hcrossUse, hpEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.redRouting.path i) _ _ hcrossUse
            have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.redRouting.path i) hdata.1).2
            exact
              (N.redLocalConnector_source_eq_of_backward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hpEq.symm
        have htgt : (N.redLocalConnector w).target = q := by
          rcases
              MinorModel.liftWalkLocalUse_right_endpoint_or_crossing
                N.respecting.model huse with hend | hnext
          · rcases hend with ⟨hwTarget, _hq⟩
            exact False.elim
              (hwT (by
                simpa [hwTarget] using N.red_target_mem_terminalSet i))
          · rcases hnext with ⟨next, hnext, hcrossUse, hqEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.redRouting.path i) _ _ hcrossUse
            have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.redRouting.path i) hdata.1).1
            exact
              (N.redLocalConnector_target_eq_of_forward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hqEq.symm
        have hEdgeSet :
            (C.path w hp hq).edgeSet = (N.redLocalConnector w).edgeSet :=
          MinorModel.BranchConnectorChoice.prefer_path_edgeSet_eq
            N.respecting.model N.redLocalConnector
            N.redLocalConnector_vertexSet_subset_branchSet w hp hq hsrc htgt
        have heLocal : s(x, y) ∈ (N.redLocalConnector w).edgeSet := by
          simpa [hEdgeSet] using heC
        exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_redLocal_edge heLocal)
      · rcases hcross with ⟨u, v, huv, huse, heq⟩
        have hxEdge : x ∈ s(MinorModel.edgeLeft N.respecting.model huv,
            MinorModel.edgeRight N.respecting.model huv) := by
          have hxxy : x ∈ s(x, y) := by simp
          simpa [heq] using hxxy
        rcases
            MinorModel.branch_eq_left_or_right_of_mem_crossing_edge
              N.respecting.model huv hxw hxEdge with hwu | hwv
        · subst u
          have hxLeft :
              x = MinorModel.edgeLeft N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · exact hxLeft
            · have hw_eq_v : w = v :=
                MinorModel.eq_right_of_edgeRight_mem_branchSet
                  N.respecting.model huv (by simpa [hxRight] using hxw)
              exact False.elim (huv.ne hw_eq_v)
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.redRouting.path i) _ _ huse
          have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.redRouting.path i) hdata.1).1
          have htarget :
              (N.redLocalConnector w).target =
                MinorModel.edgeLeft N.respecting.model huv :=
            N.redLocalConnector_target_eq_of_forward_edge
              hwPath hwT hdata.1 hdata.2.1 hdata.2.2
          exact False.elim (hxNotRedTarget (hxLeft.trans htarget.symm))
        · subst v
          have hxRight :
              x = MinorModel.edgeRight N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · have hw_eq_u : w = u :=
                MinorModel.eq_left_of_edgeLeft_mem_branchSet
                  N.respecting.model huv (by simpa [hxLeft] using hxw)
              exact False.elim (huv.ne hw_eq_u.symm)
            · exact hxRight
          have hyLeft :
              y = MinorModel.edgeLeft N.respecting.model huv := by
            have hyEdge : y ∈ s(MinorModel.edgeLeft N.respecting.model huv,
                MinorModel.edgeRight N.respecting.model huv) := by
              have hyxy : y ∈ s(x, y) := by simp
              simpa [heq] using hyxy
            rcases Sym2.mem_iff.mp hyEdge with hyLeft | hyRight
            · exact hyLeft
            · exact False.elim
                (hxy.ne (hxRight.trans hyRight.symm))
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.redRouting.path i) _ _ huse
          have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.redRouting.path i) hdata.1).2
          have hi : i = i₀ :=
            N.redRouting_index_eq_of_mem_vertexSet hwPath hwPath₀
          subst i
          have hu_eq_prev₀ : u = prev₀ :=
            GraphPath.backward_edge_unique (N.redRouting.path i₀)
              hdata.1 hdata.2.1 hdata.2.2
              hprev₀Edge hprev₀Before hprev₀_ne
          subst u
          have hleft_eq :
              MinorModel.edgeLeft N.respecting.model huv = z := by
            simp [z]
          exact Or.inr (by simp [hyLeft, hleft_eq])
    · rcases
        (N.paperBlueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hblue with
        ⟨⟨j, he⟩, _hne⟩
      rcases
          N.paperBlueRouting_path_edge_incident_branchSet_local_or_endpoint
            hwT hxw he with heLocal | hsource | htarget
      · exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_blueLocal_edge heLocal)
      · exact False.elim (hxNotBlueSource hsource)
      · exact False.elim (hxNotBlueTarget htarget)
  simpa using hglobal

/-- A non-splice red-target boundary vertex has global degree at most two,
provided it is not also the red source or a blue boundary endpoint. -/
theorem paperRouting_degreeAtMost_two_of_mem_branchSet_red_target_not_other_endpoint
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x : V}
    (hwT : w ∉ N.terminalSet)
    (hwR : w ∈ N.redRouting.toPathPacking.vertexSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w)
    (hxTarget : x = (N.redLocalConnector w).target)
    (hxNotRedSource : x ≠ (N.redLocalConnector w).source)
    (hxNotBlueSource : x ≠ (N.blueLocalConnector w).source)
    (hxNotBlueTarget : x ≠ (N.blueLocalConnector w).target) :
    DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
  classical
  rcases (N.redRouting.toPathPacking.mem_vertexSet).1 hwR with
    ⟨i₀, hwPath₀⟩
  have hwInternal₀ :=
    N.red_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (i := i₀)
  let nextExists :=
    GraphPath.exists_forward_edge_of_mem_not_target
      (N.redRouting.path i₀) hwPath₀ hwInternal₀.2
  let next₀ : W := Classical.choose nextExists
  have hnext₀Edge : s(w, next₀) ∈ (N.redRouting.path i₀).edgeSet :=
    (Classical.choose_spec nextExists).1
  have hnext₀Before : (N.redRouting.path i₀).Before w next₀ :=
    (Classical.choose_spec nextExists).2.1
  have hnext₀_ne : w ≠ next₀ :=
    (Classical.choose_spec nextExists).2.2
  have hnext₀Adj : H.Adj w next₀ := by
    have hEdge : s(w, next₀) ∈ H.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i₀) hnext₀Edge
    simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
  let z : V := MinorModel.edgeRight N.respecting.model hnext₀Adj
  let L :=
    twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))
  have hlocal : DegreeAtMost L x 1 := by
    have hxEndpoint : (N.redLocalConnector w).IsEndpoint x := Or.inr hxTarget
    simpa [L] using
      N.localConnector_degreeAtMost_one_of_red_endpoint_not_splice
        w hxEndpoint hxFirst hxLast
  have hglobal :
      DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x
        (1 + 1) := by
    refine degreeAtMost_of_adj_imp_local_or_mem hlocal {z} ?_ (by simp)
    intro y hxy
    have hcases :
        N.paperRedRouting.toPathPacking.spanningGraph.Adj x y ∨
          N.paperBlueRouting.toPathPacking.spanningGraph.Adj x y := by
      simpa [twoPackingUnionGraph] using hxy
    rcases hcases with hred | hblue
    · rcases
        (N.paperRedRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hred with
        ⟨⟨i, he⟩, _hne⟩
      let C :=
        MinorModel.BranchConnectorChoice.prefer
          N.respecting.model N.redLocalConnector
          N.redLocalConnector_vertexSet_subset_branchSet
      have hclass :=
        N.respecting.liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
          C
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
          N.redRouting i
          (by simpa [TwoPairGoodMinor.paperRedRouting, C] using he)
      dsimp only at hclass
      rcases hclass with hlocalUse | hcross
      · rcases hlocalUse with ⟨z₀, p, q, hp, hq, huse, heC⟩
        have hxC : x ∈ (C.path z₀ hp hq).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet (C.path z₀ hp hq) heC).1
        have hxz₀ : x ∈ N.respecting.model.branchSet z₀ :=
          C.vertexSet_subset z₀ hp hq hxC
        have hz₀w : z₀ = w := by
          by_contra hne
          exact Finset.disjoint_left.mp (N.respecting.model.branch_disjoint hne)
            hxz₀ hxw
        subst z₀
        have hsrc : (N.redLocalConnector w).source = p := by
          rcases
              MinorModel.liftWalkLocalUse_left_endpoint_or_crossing
                N.respecting.model huse with hstart | hprev
          · rcases hstart with ⟨hwSource, _hp⟩
            exact False.elim
              (hwT (by
                simpa [hwSource] using N.red_source_mem_terminalSet i))
          · rcases hprev with ⟨prev, hprev, hcrossUse, hpEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.redRouting.path i) _ _ hcrossUse
            have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.redRouting.path i) hdata.1).2
            exact
              (N.redLocalConnector_source_eq_of_backward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hpEq.symm
        have htgt : (N.redLocalConnector w).target = q := by
          rcases
              MinorModel.liftWalkLocalUse_right_endpoint_or_crossing
                N.respecting.model huse with hend | hnext
          · rcases hend with ⟨hwTarget, _hq⟩
            exact False.elim
              (hwT (by
                simpa [hwTarget] using N.red_target_mem_terminalSet i))
          · rcases hnext with ⟨next, hnext, hcrossUse, hqEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.redRouting.path i) _ _ hcrossUse
            have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.redRouting.path i) hdata.1).1
            exact
              (N.redLocalConnector_target_eq_of_forward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hqEq.symm
        have hEdgeSet :
            (C.path w hp hq).edgeSet = (N.redLocalConnector w).edgeSet :=
          MinorModel.BranchConnectorChoice.prefer_path_edgeSet_eq
            N.respecting.model N.redLocalConnector
            N.redLocalConnector_vertexSet_subset_branchSet w hp hq hsrc htgt
        have heLocal : s(x, y) ∈ (N.redLocalConnector w).edgeSet := by
          simpa [hEdgeSet] using heC
        exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_redLocal_edge heLocal)
      · rcases hcross with ⟨u, v, huv, huse, heq⟩
        have hxEdge : x ∈ s(MinorModel.edgeLeft N.respecting.model huv,
            MinorModel.edgeRight N.respecting.model huv) := by
          have hxxy : x ∈ s(x, y) := by simp
          simpa [heq] using hxxy
        rcases
            MinorModel.branch_eq_left_or_right_of_mem_crossing_edge
              N.respecting.model huv hxw hxEdge with hwu | hwv
        · subst u
          have hxLeft :
              x = MinorModel.edgeLeft N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · exact hxLeft
            · have hw_eq_v : w = v :=
                MinorModel.eq_right_of_edgeRight_mem_branchSet
                  N.respecting.model huv (by simpa [hxRight] using hxw)
              exact False.elim (huv.ne hw_eq_v)
          have hyRight :
              y = MinorModel.edgeRight N.respecting.model huv := by
            have hyEdge : y ∈ s(MinorModel.edgeLeft N.respecting.model huv,
                MinorModel.edgeRight N.respecting.model huv) := by
              have hyxy : y ∈ s(x, y) := by simp
              simpa [heq] using hyxy
            rcases Sym2.mem_iff.mp hyEdge with hyLeft | hyRight
            · exact False.elim
                (hxy.ne (hxLeft.trans hyLeft.symm))
            · exact hyRight
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.redRouting.path i) _ _ huse
          have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.redRouting.path i) hdata.1).1
          have hi : i = i₀ :=
            N.redRouting_index_eq_of_mem_vertexSet hwPath hwPath₀
          subst i
          have hv_eq_next₀ : v = next₀ :=
            GraphPath.forward_edge_unique (N.redRouting.path i₀)
              hdata.1 hdata.2.1 hdata.2.2
              hnext₀Edge hnext₀Before hnext₀_ne
          subst v
          have hright_eq :
              MinorModel.edgeRight N.respecting.model huv = z := by
            simp [z]
          exact Or.inr (by simp [hyRight, hright_eq])
        · subst v
          have hxRight :
              x = MinorModel.edgeRight N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · have hw_eq_u : w = u :=
                MinorModel.eq_left_of_edgeLeft_mem_branchSet
                  N.respecting.model huv (by simpa [hxLeft] using hxw)
              exact False.elim (huv.ne hw_eq_u.symm)
            · exact hxRight
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.redRouting.path i) _ _ huse
          have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.redRouting.path i) hdata.1).2
          have hsource :
              (N.redLocalConnector w).source =
                MinorModel.edgeRight N.respecting.model huv :=
            N.redLocalConnector_source_eq_of_backward_edge
              hwPath hwT hdata.1 hdata.2.1 hdata.2.2
          exact False.elim (hxNotRedSource (hxRight.trans hsource.symm))
    · rcases
        (N.paperBlueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hblue with
        ⟨⟨j, he⟩, _hne⟩
      rcases
          N.paperBlueRouting_path_edge_incident_branchSet_local_or_endpoint
            hwT hxw he with heLocal | hsource | htarget
      · exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_blueLocal_edge heLocal)
      · exact False.elim (hxNotBlueSource hsource)
      · exact False.elim (hxNotBlueTarget htarget)
  simpa using hglobal

/-- A non-splice blue-source boundary vertex has global degree at most two,
provided it is not a red boundary endpoint and not also the blue target. -/
theorem paperRouting_degreeAtMost_two_of_mem_branchSet_blue_source_not_other_endpoint
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x : V}
    (hwT : w ∉ N.terminalSet)
    (hwB : w ∈ N.blueRouting.toPathPacking.vertexSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w)
    (hxSource : x = (N.blueLocalConnector w).source)
    (hxNotRedSource : x ≠ (N.redLocalConnector w).source)
    (hxNotRedTarget : x ≠ (N.redLocalConnector w).target)
    (hxNotBlueTarget : x ≠ (N.blueLocalConnector w).target) :
    DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
  classical
  rcases (N.blueRouting.toPathPacking.mem_vertexSet).1 hwB with
    ⟨j₀, hwPath₀⟩
  have hwInternal₀ :=
    N.blue_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (j := j₀)
  let prevExists :=
    GraphPath.exists_backward_edge_of_mem_not_source
      (N.blueRouting.path j₀) hwPath₀ hwInternal₀.1
  let prev₀ : W := Classical.choose prevExists
  have hprev₀Edge : s(prev₀, w) ∈ (N.blueRouting.path j₀).edgeSet :=
    (Classical.choose_spec prevExists).1
  have hprev₀Before : (N.blueRouting.path j₀).Before prev₀ w :=
    (Classical.choose_spec prevExists).2.1
  have hprev₀_ne : prev₀ ≠ w :=
    (Classical.choose_spec prevExists).2.2
  have hprev₀Adj : H.Adj prev₀ w := by
    have hEdge : s(prev₀, w) ∈ H.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j₀) hprev₀Edge
    simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
  let z : V := MinorModel.edgeLeft N.respecting.model hprev₀Adj
  let L :=
    twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))
  have hlocal : DegreeAtMost L x 1 := by
    have hxEndpoint : (N.blueLocalConnector w).IsEndpoint x := Or.inl hxSource
    simpa [L] using
      N.localConnector_degreeAtMost_one_of_blue_endpoint_not_splice
        w hxEndpoint hxFirst hxLast
  have hglobal :
      DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x
        (1 + 1) := by
    refine degreeAtMost_of_adj_imp_local_or_mem hlocal {z} ?_ (by simp)
    intro y hxy
    have hcases :
        N.paperRedRouting.toPathPacking.spanningGraph.Adj x y ∨
          N.paperBlueRouting.toPathPacking.spanningGraph.Adj x y := by
      simpa [twoPackingUnionGraph] using hxy
    rcases hcases with hred | hblue
    · rcases
        (N.paperRedRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hred with
        ⟨⟨i, he⟩, _hne⟩
      rcases
          N.paperRedRouting_path_edge_incident_branchSet_local_or_endpoint
            hwT hxw he with heLocal | hsource | htarget
      · exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_redLocal_edge heLocal)
      · exact False.elim (hxNotRedSource hsource)
      · exact False.elim (hxNotRedTarget htarget)
    · rcases
        (N.paperBlueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hblue with
        ⟨⟨j, he⟩, _hne⟩
      let C :=
        MinorModel.BranchConnectorChoice.preferRerouteThrough
          N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
          N.redLocalConnector_vertexSet_subset_branchSet
          N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet
      have hclass :=
        N.respecting.liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
          C
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
          N.blueRouting j
          (by simpa [TwoPairGoodMinor.paperBlueRouting, C] using he)
      dsimp only at hclass
      rcases hclass with hlocalUse | hcross
      · rcases hlocalUse with ⟨z₀, p, q, hp, hq, huse, heC⟩
        have hxC : x ∈ (C.path z₀ hp hq).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet (C.path z₀ hp hq) heC).1
        have hxz₀ : x ∈ N.respecting.model.branchSet z₀ :=
          C.vertexSet_subset z₀ hp hq hxC
        have hz₀w : z₀ = w := by
          by_contra hne
          exact Finset.disjoint_left.mp (N.respecting.model.branch_disjoint hne)
            hxz₀ hxw
        subst z₀
        have hsrcPre : (N.bluePreliminaryLocalConnector w).source = p := by
          rcases
              MinorModel.liftWalkLocalUse_left_endpoint_or_crossing
                N.respecting.model huse with hstart | hprev
          · rcases hstart with ⟨hwSource, _hp⟩
            exact False.elim
              (hwT (by
                simpa [hwSource] using N.blue_source_mem_terminalSet j))
          · rcases hprev with ⟨prev, hprev, hcrossUse, hpEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.blueRouting.path j) _ _ hcrossUse
            have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.blueRouting.path j) hdata.1).2
            exact
              (N.bluePreliminaryLocalConnector_source_eq_of_backward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hpEq.symm
        have htgtPre : (N.bluePreliminaryLocalConnector w).target = q := by
          rcases
              MinorModel.liftWalkLocalUse_right_endpoint_or_crossing
                N.respecting.model huse with hend | hnext
          · rcases hend with ⟨hwTarget, _hq⟩
            exact False.elim
              (hwT (by
                simpa [hwTarget] using N.blue_target_mem_terminalSet j))
          · rcases hnext with ⟨next, hnext, hcrossUse, hqEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.blueRouting.path j) _ _ hcrossUse
            have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.blueRouting.path j) hdata.1).1
            exact
              (N.bluePreliminaryLocalConnector_target_eq_of_forward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hqEq.symm
        have hEdgeSet :
            (C.path w hp hq).edgeSet = (N.blueLocalConnector w).edgeSet := by
          simpa [TwoPairGoodMinor.blueLocalConnector] using
            MinorModel.BranchConnectorChoice.preferRerouteThrough_path_edgeSet_eq
              N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
              N.redLocalConnector_vertexSet_subset_branchSet
              N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet
              w hp hq hsrcPre htgtPre
        have heLocal : s(x, y) ∈ (N.blueLocalConnector w).edgeSet := by
          simpa [hEdgeSet] using heC
        exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_blueLocal_edge heLocal)
      · rcases hcross with ⟨u, v, huv, huse, heq⟩
        have hxEdge : x ∈ s(MinorModel.edgeLeft N.respecting.model huv,
            MinorModel.edgeRight N.respecting.model huv) := by
          have hxxy : x ∈ s(x, y) := by simp
          simpa [heq] using hxxy
        rcases
            MinorModel.branch_eq_left_or_right_of_mem_crossing_edge
              N.respecting.model huv hxw hxEdge with hwu | hwv
        · subst u
          have hxLeft :
              x = MinorModel.edgeLeft N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · exact hxLeft
            · have hw_eq_v : w = v :=
                MinorModel.eq_right_of_edgeRight_mem_branchSet
                  N.respecting.model huv (by simpa [hxRight] using hxw)
              exact False.elim (huv.ne hw_eq_v)
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.blueRouting.path j) _ _ huse
          have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.blueRouting.path j) hdata.1).1
          have htarget :
              (N.bluePreliminaryLocalConnector w).target =
                MinorModel.edgeLeft N.respecting.model huv :=
            N.bluePreliminaryLocalConnector_target_eq_of_forward_edge
              hwPath hwT hdata.1 hdata.2.1 hdata.2.2
          exact False.elim
            (hxNotBlueTarget
              (by simpa [TwoPairGoodMinor.blueLocalConnector]
                using hxLeft.trans htarget.symm))
        · subst v
          have hxRight :
              x = MinorModel.edgeRight N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · have hw_eq_u : w = u :=
                MinorModel.eq_left_of_edgeLeft_mem_branchSet
                  N.respecting.model huv (by simpa [hxLeft] using hxw)
              exact False.elim (huv.ne hw_eq_u.symm)
            · exact hxRight
          have hyLeft :
              y = MinorModel.edgeLeft N.respecting.model huv := by
            have hyEdge : y ∈ s(MinorModel.edgeLeft N.respecting.model huv,
                MinorModel.edgeRight N.respecting.model huv) := by
              have hyxy : y ∈ s(x, y) := by simp
              simpa [heq] using hyxy
            rcases Sym2.mem_iff.mp hyEdge with hyLeft | hyRight
            · exact hyLeft
            · exact False.elim
                (hxy.ne (hxRight.trans hyRight.symm))
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.blueRouting.path j) _ _ huse
          have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.blueRouting.path j) hdata.1).2
          have hj : j = j₀ :=
            N.blueRouting_index_eq_of_mem_vertexSet hwPath hwPath₀
          subst j
          have hu_eq_prev₀ : u = prev₀ :=
            GraphPath.backward_edge_unique (N.blueRouting.path j₀)
              hdata.1 hdata.2.1 hdata.2.2
              hprev₀Edge hprev₀Before hprev₀_ne
          subst u
          have hleft_eq :
              MinorModel.edgeLeft N.respecting.model huv = z := by
            simp [z]
          exact Or.inr (by simp [hyLeft, hleft_eq])
  simpa using hglobal

/-- A non-splice blue-target boundary vertex has global degree at most two,
provided it is not a red boundary endpoint and not also the blue source. -/
theorem paperRouting_degreeAtMost_two_of_mem_branchSet_blue_target_not_other_endpoint
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x : V}
    (hwT : w ∉ N.terminalSet)
    (hwB : w ∈ N.blueRouting.toPathPacking.vertexSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w)
    (hxTarget : x = (N.blueLocalConnector w).target)
    (hxNotRedSource : x ≠ (N.redLocalConnector w).source)
    (hxNotRedTarget : x ≠ (N.redLocalConnector w).target)
    (hxNotBlueSource : x ≠ (N.blueLocalConnector w).source) :
    DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
  classical
  rcases (N.blueRouting.toPathPacking.mem_vertexSet).1 hwB with
    ⟨j₀, hwPath₀⟩
  have hwInternal₀ :=
    N.blue_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (j := j₀)
  let nextExists :=
    GraphPath.exists_forward_edge_of_mem_not_target
      (N.blueRouting.path j₀) hwPath₀ hwInternal₀.2
  let next₀ : W := Classical.choose nextExists
  have hnext₀Edge : s(w, next₀) ∈ (N.blueRouting.path j₀).edgeSet :=
    (Classical.choose_spec nextExists).1
  have hnext₀Before : (N.blueRouting.path j₀).Before w next₀ :=
    (Classical.choose_spec nextExists).2.1
  have hnext₀_ne : w ≠ next₀ :=
    (Classical.choose_spec nextExists).2.2
  have hnext₀Adj : H.Adj w next₀ := by
    have hEdge : s(w, next₀) ∈ H.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j₀) hnext₀Edge
    simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
  let z : V := MinorModel.edgeRight N.respecting.model hnext₀Adj
  let L :=
    twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))
  have hlocal : DegreeAtMost L x 1 := by
    have hxEndpoint : (N.blueLocalConnector w).IsEndpoint x := Or.inr hxTarget
    simpa [L] using
      N.localConnector_degreeAtMost_one_of_blue_endpoint_not_splice
        w hxEndpoint hxFirst hxLast
  have hglobal :
      DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x
        (1 + 1) := by
    refine degreeAtMost_of_adj_imp_local_or_mem hlocal {z} ?_ (by simp)
    intro y hxy
    have hcases :
        N.paperRedRouting.toPathPacking.spanningGraph.Adj x y ∨
          N.paperBlueRouting.toPathPacking.spanningGraph.Adj x y := by
      simpa [twoPackingUnionGraph] using hxy
    rcases hcases with hred | hblue
    · rcases
        (N.paperRedRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hred with
        ⟨⟨i, he⟩, _hne⟩
      rcases
          N.paperRedRouting_path_edge_incident_branchSet_local_or_endpoint
            hwT hxw he with heLocal | hsource | htarget
      · exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_redLocal_edge heLocal)
      · exact False.elim (hxNotRedSource hsource)
      · exact False.elim (hxNotRedTarget htarget)
    · rcases
        (N.paperBlueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hblue with
        ⟨⟨j, he⟩, _hne⟩
      let C :=
        MinorModel.BranchConnectorChoice.preferRerouteThrough
          N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
          N.redLocalConnector_vertexSet_subset_branchSet
          N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet
      have hclass :=
        N.respecting.liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
          C
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
          N.blueRouting j
          (by simpa [TwoPairGoodMinor.paperBlueRouting, C] using he)
      dsimp only at hclass
      rcases hclass with hlocalUse | hcross
      · rcases hlocalUse with ⟨z₀, p, q, hp, hq, huse, heC⟩
        have hxC : x ∈ (C.path z₀ hp hq).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet (C.path z₀ hp hq) heC).1
        have hxz₀ : x ∈ N.respecting.model.branchSet z₀ :=
          C.vertexSet_subset z₀ hp hq hxC
        have hz₀w : z₀ = w := by
          by_contra hne
          exact Finset.disjoint_left.mp (N.respecting.model.branch_disjoint hne)
            hxz₀ hxw
        subst z₀
        have hsrcPre : (N.bluePreliminaryLocalConnector w).source = p := by
          rcases
              MinorModel.liftWalkLocalUse_left_endpoint_or_crossing
                N.respecting.model huse with hstart | hprev
          · rcases hstart with ⟨hwSource, _hp⟩
            exact False.elim
              (hwT (by
                simpa [hwSource] using N.blue_source_mem_terminalSet j))
          · rcases hprev with ⟨prev, hprev, hcrossUse, hpEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.blueRouting.path j) _ _ hcrossUse
            have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.blueRouting.path j) hdata.1).2
            exact
              (N.bluePreliminaryLocalConnector_source_eq_of_backward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hpEq.symm
        have htgtPre : (N.bluePreliminaryLocalConnector w).target = q := by
          rcases
              MinorModel.liftWalkLocalUse_right_endpoint_or_crossing
                N.respecting.model huse with hend | hnext
          · rcases hend with ⟨hwTarget, _hq⟩
            exact False.elim
              (hwT (by
                simpa [hwTarget] using N.blue_target_mem_terminalSet j))
          · rcases hnext with ⟨next, hnext, hcrossUse, hqEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.blueRouting.path j) _ _ hcrossUse
            have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.blueRouting.path j) hdata.1).1
            exact
              (N.bluePreliminaryLocalConnector_target_eq_of_forward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hqEq.symm
        have hEdgeSet :
            (C.path w hp hq).edgeSet = (N.blueLocalConnector w).edgeSet := by
          simpa [TwoPairGoodMinor.blueLocalConnector] using
            MinorModel.BranchConnectorChoice.preferRerouteThrough_path_edgeSet_eq
              N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
              N.redLocalConnector_vertexSet_subset_branchSet
              N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet
              w hp hq hsrcPre htgtPre
        have heLocal : s(x, y) ∈ (N.blueLocalConnector w).edgeSet := by
          simpa [hEdgeSet] using heC
        exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_blueLocal_edge heLocal)
      · rcases hcross with ⟨u, v, huv, huse, heq⟩
        have hxEdge : x ∈ s(MinorModel.edgeLeft N.respecting.model huv,
            MinorModel.edgeRight N.respecting.model huv) := by
          have hxxy : x ∈ s(x, y) := by simp
          simpa [heq] using hxxy
        rcases
            MinorModel.branch_eq_left_or_right_of_mem_crossing_edge
              N.respecting.model huv hxw hxEdge with hwu | hwv
        · subst u
          have hxLeft :
              x = MinorModel.edgeLeft N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · exact hxLeft
            · have hw_eq_v : w = v :=
                MinorModel.eq_right_of_edgeRight_mem_branchSet
                  N.respecting.model huv (by simpa [hxRight] using hxw)
              exact False.elim (huv.ne hw_eq_v)
          have hyRight :
              y = MinorModel.edgeRight N.respecting.model huv := by
            have hyEdge : y ∈ s(MinorModel.edgeLeft N.respecting.model huv,
                MinorModel.edgeRight N.respecting.model huv) := by
              have hyxy : y ∈ s(x, y) := by simp
              simpa [heq] using hyxy
            rcases Sym2.mem_iff.mp hyEdge with hyLeft | hyRight
            · exact False.elim
                (hxy.ne (hxLeft.trans hyLeft.symm))
            · exact hyRight
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.blueRouting.path j) _ _ huse
          have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.blueRouting.path j) hdata.1).1
          have hj : j = j₀ :=
            N.blueRouting_index_eq_of_mem_vertexSet hwPath hwPath₀
          subst j
          have hv_eq_next₀ : v = next₀ :=
            GraphPath.forward_edge_unique (N.blueRouting.path j₀)
              hdata.1 hdata.2.1 hdata.2.2
              hnext₀Edge hnext₀Before hnext₀_ne
          subst v
          have hright_eq :
              MinorModel.edgeRight N.respecting.model huv = z := by
            simp [z]
          exact Or.inr (by simp [hyRight, hright_eq])
        · subst v
          have hxRight :
              x = MinorModel.edgeRight N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · have hw_eq_u : w = u :=
                MinorModel.eq_left_of_edgeLeft_mem_branchSet
                  N.respecting.model huv (by simpa [hxLeft] using hxw)
              exact False.elim (huv.ne hw_eq_u.symm)
            · exact hxRight
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.blueRouting.path j) _ _ huse
          have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.blueRouting.path j) hdata.1).2
          have hsource :
              (N.bluePreliminaryLocalConnector w).source =
                MinorModel.edgeRight N.respecting.model huv :=
            N.bluePreliminaryLocalConnector_source_eq_of_backward_edge
              hwPath hwT hdata.1 hdata.2.1 hdata.2.2
          exact False.elim
            (hxNotBlueSource
              (by simpa [TwoPairGoodMinor.blueLocalConnector]
                using hxRight.trans hsource.symm))
  simpa using hglobal

/-- A non-splice red boundary vertex whose red source and red target coincide
has global degree at most two, provided it is not a blue boundary endpoint. -/
theorem paperRouting_degreeAtMost_two_of_mem_branchSet_red_source_target_not_blue_endpoint
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x : V}
    (hwT : w ∉ N.terminalSet)
    (hwR : w ∈ N.redRouting.toPathPacking.vertexSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w)
    (hxSource : x = (N.redLocalConnector w).source)
    (hxTarget : x = (N.redLocalConnector w).target)
    (hxNotBlueSource : x ≠ (N.blueLocalConnector w).source)
    (hxNotBlueTarget : x ≠ (N.blueLocalConnector w).target) :
    DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
  classical
  rcases (N.redRouting.toPathPacking.mem_vertexSet).1 hwR with
    ⟨i₀, hwPath₀⟩
  have hwInternal₀ :=
    N.red_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (i := i₀)
  let prevExists :=
    GraphPath.exists_backward_edge_of_mem_not_source
      (N.redRouting.path i₀) hwPath₀ hwInternal₀.1
  let prev₀ : W := Classical.choose prevExists
  have hprev₀Edge : s(prev₀, w) ∈ (N.redRouting.path i₀).edgeSet :=
    (Classical.choose_spec prevExists).1
  have hprev₀Before : (N.redRouting.path i₀).Before prev₀ w :=
    (Classical.choose_spec prevExists).2.1
  have hprev₀_ne : prev₀ ≠ w :=
    (Classical.choose_spec prevExists).2.2
  have hprev₀Adj : H.Adj prev₀ w := by
    have hEdge : s(prev₀, w) ∈ H.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i₀) hprev₀Edge
    simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
  let nextExists :=
    GraphPath.exists_forward_edge_of_mem_not_target
      (N.redRouting.path i₀) hwPath₀ hwInternal₀.2
  let next₀ : W := Classical.choose nextExists
  have hnext₀Edge : s(w, next₀) ∈ (N.redRouting.path i₀).edgeSet :=
    (Classical.choose_spec nextExists).1
  have hnext₀Before : (N.redRouting.path i₀).Before w next₀ :=
    (Classical.choose_spec nextExists).2.1
  have hnext₀_ne : w ≠ next₀ :=
    (Classical.choose_spec nextExists).2.2
  have hnext₀Adj : H.Adj w next₀ := by
    have hEdge : s(w, next₀) ∈ H.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet (N.redRouting.path i₀) hnext₀Edge
    simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
  let zPrev : V := MinorModel.edgeLeft N.respecting.model hprev₀Adj
  let zNext : V := MinorModel.edgeRight N.respecting.model hnext₀Adj
  let L :=
    twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))
  have hlocal : DegreeAtMost L x 0 := by
    simpa [L] using
      N.localConnector_degreeAtMost_zero_of_red_source_eq_target_not_splice
        w hxSource hxTarget hxFirst hxLast
  have hglobal :
      DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x
        (0 + 2) := by
    have hEcard : ({zPrev, zNext} : Finset V).card ≤ 2 := by
      calc
        ({zPrev, zNext} : Finset V).card ≤ ({zNext} : Finset V).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp
    refine degreeAtMost_of_adj_imp_local_or_mem hlocal {zPrev, zNext} ?_ hEcard
    intro y hxy
    have hcases :
        N.paperRedRouting.toPathPacking.spanningGraph.Adj x y ∨
          N.paperBlueRouting.toPathPacking.spanningGraph.Adj x y := by
      simpa [twoPackingUnionGraph] using hxy
    rcases hcases with hred | hblue
    · rcases
        (N.paperRedRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hred with
        ⟨⟨i, he⟩, _hne⟩
      let C :=
        MinorModel.BranchConnectorChoice.prefer
          N.respecting.model N.redLocalConnector
          N.redLocalConnector_vertexSet_subset_branchSet
      have hclass :=
        N.respecting.liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
          C
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
          N.redRouting i
          (by simpa [TwoPairGoodMinor.paperRedRouting, C] using he)
      dsimp only at hclass
      rcases hclass with hlocalUse | hcross
      · rcases hlocalUse with ⟨z₀, p, q, hp, hq, huse, heC⟩
        have hxC : x ∈ (C.path z₀ hp hq).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet (C.path z₀ hp hq) heC).1
        have hxz₀ : x ∈ N.respecting.model.branchSet z₀ :=
          C.vertexSet_subset z₀ hp hq hxC
        have hz₀w : z₀ = w := by
          by_contra hne
          exact Finset.disjoint_left.mp (N.respecting.model.branch_disjoint hne)
            hxz₀ hxw
        subst z₀
        have hsrc : (N.redLocalConnector w).source = p := by
          rcases
              MinorModel.liftWalkLocalUse_left_endpoint_or_crossing
                N.respecting.model huse with hstart | hprev
          · rcases hstart with ⟨hwSource, _hp⟩
            exact False.elim
              (hwT (by
                simpa [hwSource] using N.red_source_mem_terminalSet i))
          · rcases hprev with ⟨prev, hprev, hcrossUse, hpEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.redRouting.path i) _ _ hcrossUse
            have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.redRouting.path i) hdata.1).2
            exact
              (N.redLocalConnector_source_eq_of_backward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hpEq.symm
        have htgt : (N.redLocalConnector w).target = q := by
          rcases
              MinorModel.liftWalkLocalUse_right_endpoint_or_crossing
                N.respecting.model huse with hend | hnext
          · rcases hend with ⟨hwTarget, _hq⟩
            exact False.elim
              (hwT (by
                simpa [hwTarget] using N.red_target_mem_terminalSet i))
          · rcases hnext with ⟨next, hnext, hcrossUse, hqEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.redRouting.path i) _ _ hcrossUse
            have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.redRouting.path i) hdata.1).1
            exact
              (N.redLocalConnector_target_eq_of_forward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hqEq.symm
        have hEdgeSet :
            (C.path w hp hq).edgeSet = (N.redLocalConnector w).edgeSet :=
          MinorModel.BranchConnectorChoice.prefer_path_edgeSet_eq
            N.respecting.model N.redLocalConnector
            N.redLocalConnector_vertexSet_subset_branchSet w hp hq hsrc htgt
        have heLocal : s(x, y) ∈ (N.redLocalConnector w).edgeSet := by
          simpa [hEdgeSet] using heC
        exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_redLocal_edge heLocal)
      · rcases hcross with ⟨u, v, huv, huse, heq⟩
        have hxEdge : x ∈ s(MinorModel.edgeLeft N.respecting.model huv,
            MinorModel.edgeRight N.respecting.model huv) := by
          have hxxy : x ∈ s(x, y) := by simp
          simpa [heq] using hxxy
        rcases
            MinorModel.branch_eq_left_or_right_of_mem_crossing_edge
              N.respecting.model huv hxw hxEdge with hwu | hwv
        · subst u
          have hxLeft :
              x = MinorModel.edgeLeft N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · exact hxLeft
            · have hw_eq_v : w = v :=
                MinorModel.eq_right_of_edgeRight_mem_branchSet
                  N.respecting.model huv (by simpa [hxRight] using hxw)
              exact False.elim (huv.ne hw_eq_v)
          have hyRight :
              y = MinorModel.edgeRight N.respecting.model huv := by
            have hyEdge : y ∈ s(MinorModel.edgeLeft N.respecting.model huv,
                MinorModel.edgeRight N.respecting.model huv) := by
              have hyxy : y ∈ s(x, y) := by simp
              simpa [heq] using hyxy
            rcases Sym2.mem_iff.mp hyEdge with hyLeft | hyRight
            · exact False.elim
                (hxy.ne (hxLeft.trans hyLeft.symm))
            · exact hyRight
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.redRouting.path i) _ _ huse
          have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.redRouting.path i) hdata.1).1
          have hi : i = i₀ :=
            N.redRouting_index_eq_of_mem_vertexSet hwPath hwPath₀
          subst i
          have hv_eq_next₀ : v = next₀ :=
            GraphPath.forward_edge_unique (N.redRouting.path i₀)
              hdata.1 hdata.2.1 hdata.2.2
              hnext₀Edge hnext₀Before hnext₀_ne
          subst v
          have hright_eq :
              MinorModel.edgeRight N.respecting.model huv = zNext := by
            simp [zNext]
          exact Or.inr (by simp [hyRight, hright_eq])
        · subst v
          have hxRight :
              x = MinorModel.edgeRight N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · have hw_eq_u : w = u :=
                MinorModel.eq_left_of_edgeLeft_mem_branchSet
                  N.respecting.model huv (by simpa [hxLeft] using hxw)
              exact False.elim (huv.ne hw_eq_u.symm)
            · exact hxRight
          have hyLeft :
              y = MinorModel.edgeLeft N.respecting.model huv := by
            have hyEdge : y ∈ s(MinorModel.edgeLeft N.respecting.model huv,
                MinorModel.edgeRight N.respecting.model huv) := by
              have hyxy : y ∈ s(x, y) := by simp
              simpa [heq] using hyxy
            rcases Sym2.mem_iff.mp hyEdge with hyLeft | hyRight
            · exact hyLeft
            · exact False.elim
                (hxy.ne (hxRight.trans hyRight.symm))
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.redRouting.path i) _ _ huse
          have hwPath : w ∈ (N.redRouting.path i).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.redRouting.path i) hdata.1).2
          have hi : i = i₀ :=
            N.redRouting_index_eq_of_mem_vertexSet hwPath hwPath₀
          subst i
          have hu_eq_prev₀ : u = prev₀ :=
            GraphPath.backward_edge_unique (N.redRouting.path i₀)
              hdata.1 hdata.2.1 hdata.2.2
              hprev₀Edge hprev₀Before hprev₀_ne
          subst u
          have hleft_eq :
              MinorModel.edgeLeft N.respecting.model huv = zPrev := by
            simp [zPrev]
          exact Or.inr (by simp [hyLeft, hleft_eq])
    · rcases
        (N.paperBlueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hblue with
        ⟨⟨j, he⟩, _hne⟩
      rcases
          N.paperBlueRouting_path_edge_incident_branchSet_local_or_endpoint
            hwT hxw he with heLocal | hsource | htarget
      · exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_blueLocal_edge heLocal)
      · exact False.elim (hxNotBlueSource hsource)
      · exact False.elim (hxNotBlueTarget htarget)
  simpa using hglobal

/-- A non-splice blue boundary vertex whose cleaned blue source and target
coincide has global degree at most two, provided it is not a red boundary
endpoint. -/
theorem paperRouting_degreeAtMost_two_of_mem_branchSet_blue_source_target_not_red_endpoint
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x : V}
    (hwT : w ∉ N.terminalSet)
    (hwB : w ∈ N.blueRouting.toPathPacking.vertexSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxFirst : x ≠ N.paperLocalSpliceFirst w)
    (hxLast : x ≠ N.paperLocalSpliceLast w)
    (hxSource : x = (N.blueLocalConnector w).source)
    (hxTarget : x = (N.blueLocalConnector w).target)
    (hxNotRedSource : x ≠ (N.redLocalConnector w).source)
    (hxNotRedTarget : x ≠ (N.redLocalConnector w).target) :
    DegreeAtMost
      (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
  classical
  rcases (N.blueRouting.toPathPacking.mem_vertexSet).1 hwB with
    ⟨j₀, hwPath₀⟩
  have hwInternal₀ :=
    N.blue_internal_of_mem_vertexSet_of_not_terminal (v := w) hwT (j := j₀)
  let prevExists :=
    GraphPath.exists_backward_edge_of_mem_not_source
      (N.blueRouting.path j₀) hwPath₀ hwInternal₀.1
  let prev₀ : W := Classical.choose prevExists
  have hprev₀Edge : s(prev₀, w) ∈ (N.blueRouting.path j₀).edgeSet :=
    (Classical.choose_spec prevExists).1
  have hprev₀Before : (N.blueRouting.path j₀).Before prev₀ w :=
    (Classical.choose_spec prevExists).2.1
  have hprev₀_ne : prev₀ ≠ w :=
    (Classical.choose_spec prevExists).2.2
  have hprev₀Adj : H.Adj prev₀ w := by
    have hEdge : s(prev₀, w) ∈ H.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j₀) hprev₀Edge
    simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
  let nextExists :=
    GraphPath.exists_forward_edge_of_mem_not_target
      (N.blueRouting.path j₀) hwPath₀ hwInternal₀.2
  let next₀ : W := Classical.choose nextExists
  have hnext₀Edge : s(w, next₀) ∈ (N.blueRouting.path j₀).edgeSet :=
    (Classical.choose_spec nextExists).1
  have hnext₀Before : (N.blueRouting.path j₀).Before w next₀ :=
    (Classical.choose_spec nextExists).2.1
  have hnext₀_ne : w ≠ next₀ :=
    (Classical.choose_spec nextExists).2.2
  have hnext₀Adj : H.Adj w next₀ := by
    have hEdge : s(w, next₀) ∈ H.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet (N.blueRouting.path j₀) hnext₀Edge
    simpa [_root_.SimpleGraph.mem_edgeSet] using hEdge
  let zPrev : V := MinorModel.edgeLeft N.respecting.model hprev₀Adj
  let zNext : V := MinorModel.edgeRight N.respecting.model hnext₀Adj
  let L :=
    twoPackingUnionGraph
      (GraphPath.singletonPerfectPathPacking (N.redLocalConnector w))
      (GraphPath.singletonPerfectPathPacking (N.blueLocalConnector w))
  have hlocal : DegreeAtMost L x 0 := by
    simpa [L] using
      N.localConnector_degreeAtMost_zero_of_blue_source_eq_target_not_splice
        w hxSource hxTarget hxFirst hxLast
  have hglobal :
      DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x
        (0 + 2) := by
    have hEcard : ({zPrev, zNext} : Finset V).card ≤ 2 := by
      calc
        ({zPrev, zNext} : Finset V).card ≤ ({zNext} : Finset V).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp
    refine degreeAtMost_of_adj_imp_local_or_mem hlocal {zPrev, zNext} ?_ hEcard
    intro y hxy
    have hcases :
        N.paperRedRouting.toPathPacking.spanningGraph.Adj x y ∨
          N.paperBlueRouting.toPathPacking.spanningGraph.Adj x y := by
      simpa [twoPackingUnionGraph] using hxy
    rcases hcases with hred | hblue
    · rcases
        (N.paperRedRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hred with
        ⟨⟨i, he⟩, _hne⟩
      rcases
          N.paperRedRouting_path_edge_incident_branchSet_local_or_endpoint
            hwT hxw he with heLocal | hsource | htarget
      · exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_redLocal_edge heLocal)
      · exact False.elim (hxNotRedSource hsource)
      · exact False.elim (hxNotRedTarget htarget)
    · rcases
        (N.paperBlueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1
          hblue with
        ⟨⟨j, he⟩, _hne⟩
      let C :=
        MinorModel.BranchConnectorChoice.preferRerouteThrough
          N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
          N.redLocalConnector_vertexSet_subset_branchSet
          N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet
      have hclass :=
        N.respecting.liftPerfectPathPackingWithBranchConnectors_path_edge_localUse_or_crossingUse
          C
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
          N.blueRouting j
          (by simpa [TwoPairGoodMinor.paperBlueRouting, C] using he)
      dsimp only at hclass
      rcases hclass with hlocalUse | hcross
      · rcases hlocalUse with ⟨z₀, p, q, hp, hq, huse, heC⟩
        have hxC : x ∈ (C.path z₀ hp hq).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet (C.path z₀ hp hq) heC).1
        have hxz₀ : x ∈ N.respecting.model.branchSet z₀ :=
          C.vertexSet_subset z₀ hp hq hxC
        have hz₀w : z₀ = w := by
          by_contra hne
          exact Finset.disjoint_left.mp (N.respecting.model.branch_disjoint hne)
            hxz₀ hxw
        subst z₀
        have hsrcPre : (N.bluePreliminaryLocalConnector w).source = p := by
          rcases
              MinorModel.liftWalkLocalUse_left_endpoint_or_crossing
                N.respecting.model huse with hstart | hprev
          · rcases hstart with ⟨hwSource, _hp⟩
            exact False.elim
              (hwT (by
                simpa [hwSource] using N.blue_source_mem_terminalSet j))
          · rcases hprev with ⟨prev, hprev, hcrossUse, hpEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.blueRouting.path j) _ _ hcrossUse
            have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.blueRouting.path j) hdata.1).2
            exact
              (N.bluePreliminaryLocalConnector_source_eq_of_backward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hpEq.symm
        have htgtPre : (N.bluePreliminaryLocalConnector w).target = q := by
          rcases
              MinorModel.liftWalkLocalUse_right_endpoint_or_crossing
                N.respecting.model huse with hend | hnext
          · rcases hend with ⟨hwTarget, _hq⟩
            exact False.elim
              (hwT (by
                simpa [hwTarget] using N.blue_target_mem_terminalSet j))
          · rcases hnext with ⟨next, hnext, hcrossUse, hqEq⟩
            have hdata :=
              MinorModel.liftWalkCrossingUse_edgeSet_before
                N.respecting.model (N.blueRouting.path j) _ _ hcrossUse
            have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (N.blueRouting.path j) hdata.1).1
            exact
              (N.bluePreliminaryLocalConnector_target_eq_of_forward_edge
                hwPath hwT hdata.1 hdata.2.1 hdata.2.2).trans hqEq.symm
        have hEdgeSet :
            (C.path w hp hq).edgeSet = (N.blueLocalConnector w).edgeSet := by
          simpa [TwoPairGoodMinor.blueLocalConnector] using
            MinorModel.BranchConnectorChoice.preferRerouteThrough_path_edgeSet_eq
              N.respecting.model N.redLocalConnector N.bluePreliminaryLocalConnector
              N.redLocalConnector_vertexSet_subset_branchSet
              N.bluePreliminaryLocalConnector_vertexSet_subset_branchSet
              w hp hq hsrcPre htgtPre
        have heLocal : s(x, y) ∈ (N.blueLocalConnector w).edgeSet := by
          simpa [hEdgeSet] using heC
        exact Or.inl (by
          simpa [L] using N.paperLocalUnion_adj_of_blueLocal_edge heLocal)
      · rcases hcross with ⟨u, v, huv, huse, heq⟩
        have hxEdge : x ∈ s(MinorModel.edgeLeft N.respecting.model huv,
            MinorModel.edgeRight N.respecting.model huv) := by
          have hxxy : x ∈ s(x, y) := by simp
          simpa [heq] using hxxy
        rcases
            MinorModel.branch_eq_left_or_right_of_mem_crossing_edge
              N.respecting.model huv hxw hxEdge with hwu | hwv
        · subst u
          have hxLeft :
              x = MinorModel.edgeLeft N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · exact hxLeft
            · have hw_eq_v : w = v :=
                MinorModel.eq_right_of_edgeRight_mem_branchSet
                  N.respecting.model huv (by simpa [hxRight] using hxw)
              exact False.elim (huv.ne hw_eq_v)
          have hyRight :
              y = MinorModel.edgeRight N.respecting.model huv := by
            have hyEdge : y ∈ s(MinorModel.edgeLeft N.respecting.model huv,
                MinorModel.edgeRight N.respecting.model huv) := by
              have hyxy : y ∈ s(x, y) := by simp
              simpa [heq] using hyxy
            rcases Sym2.mem_iff.mp hyEdge with hyLeft | hyRight
            · exact False.elim
                (hxy.ne (hxLeft.trans hyLeft.symm))
            · exact hyRight
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.blueRouting.path j) _ _ huse
          have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.blueRouting.path j) hdata.1).1
          have hj : j = j₀ :=
            N.blueRouting_index_eq_of_mem_vertexSet hwPath hwPath₀
          subst j
          have hv_eq_next₀ : v = next₀ :=
            GraphPath.forward_edge_unique (N.blueRouting.path j₀)
              hdata.1 hdata.2.1 hdata.2.2
              hnext₀Edge hnext₀Before hnext₀_ne
          subst v
          have hright_eq :
              MinorModel.edgeRight N.respecting.model huv = zNext := by
            simp [zNext]
          exact Or.inr (by simp [hyRight, hright_eq])
        · subst v
          have hxRight :
              x = MinorModel.edgeRight N.respecting.model huv := by
            rcases Sym2.mem_iff.mp hxEdge with hxLeft | hxRight
            · have hw_eq_u : w = u :=
                MinorModel.eq_left_of_edgeLeft_mem_branchSet
                  N.respecting.model huv (by simpa [hxLeft] using hxw)
              exact False.elim (huv.ne hw_eq_u.symm)
            · exact hxRight
          have hyLeft :
              y = MinorModel.edgeLeft N.respecting.model huv := by
            have hyEdge : y ∈ s(MinorModel.edgeLeft N.respecting.model huv,
                MinorModel.edgeRight N.respecting.model huv) := by
              have hyxy : y ∈ s(x, y) := by simp
              simpa [heq] using hyxy
            rcases Sym2.mem_iff.mp hyEdge with hyLeft | hyRight
            · exact hyLeft
            · exact False.elim
                (hxy.ne (hxRight.trans hyRight.symm))
          have hdata :=
            MinorModel.liftWalkCrossingUse_edgeSet_before
              N.respecting.model (N.blueRouting.path j) _ _ huse
          have hwPath : w ∈ (N.blueRouting.path j).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (N.blueRouting.path j) hdata.1).2
          have hj : j = j₀ :=
            N.blueRouting_index_eq_of_mem_vertexSet hwPath hwPath₀
          subst j
          have hu_eq_prev₀ : u = prev₀ :=
            GraphPath.backward_edge_unique (N.blueRouting.path j₀)
              hdata.1 hdata.2.1 hdata.2.2
              hprev₀Edge hprev₀Before hprev₀_ne
          subst u
          have hleft_eq :
              MinorModel.edgeLeft N.respecting.model huv = zPrev := by
            simp [zPrev]
          exact Or.inr (by simp [hyLeft, hleft_eq])
  simpa using hglobal

/-- In a nonterminal branch set, every high-degree vertex of the paper
red/blue expansion is one of the two local splice vertices. -/
theorem paperRouting_highVertex_branchSet_eq_splice
    [Fintype V]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    {w : W} {x : V}
    (hwT : w ∉ N.terminalSet)
    (hwRB :
      w ∈ N.redRouting.toPathPacking.vertexSet ∧
        w ∈ N.blueRouting.toPathPacking.vertexSet)
    (hxw : x ∈ N.respecting.model.branchSet w)
    (hxHigh :
      ¬ DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2) :
    x = N.paperLocalSpliceFirst w ∨ x = N.paperLocalSpliceLast w := by
  classical
  by_contra hnot
  have hxFirst : x ≠ N.paperLocalSpliceFirst w := by
    intro hx
    exact hnot (Or.inl hx)
  have hxLast : x ≠ N.paperLocalSpliceLast w := by
    intro hx
    exact hnot (Or.inr hx)
  have hblueSourceSplice
      (hxBlueSource : x = (N.blueLocalConnector w).source)
      (hxRedMem : x ∈ (N.redLocalConnector w).vertexSet) :
      False := by
    have hmem :
        (N.blueLocalConnector w).source ∈
          (N.redLocalConnector w).vertexSet := by
      simpa [hxBlueSource] using hxRedMem
    have hsplice :=
      N.blueLocalConnector_source_eq_spliceFirst_of_mem_red w hmem
    exact hxFirst (hxBlueSource.trans hsplice)
  have hblueTargetSplice
      (hxBlueTarget : x = (N.blueLocalConnector w).target)
      (hxRedMem : x ∈ (N.redLocalConnector w).vertexSet) :
      False := by
    have hmem :
        (N.blueLocalConnector w).target ∈
          (N.redLocalConnector w).vertexSet := by
      simpa [hxBlueTarget] using hxRedMem
    have hsplice :=
      N.blueLocalConnector_target_eq_spliceLast_of_mem_red w hmem
    exact hxLast (hxBlueTarget.trans hsplice)
  have hdeg :
      DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) x 2 := by
    by_cases hxRedSource : x = (N.redLocalConnector w).source
    · have hxRedMem : x ∈ (N.redLocalConnector w).vertexSet := by
        simpa [hxRedSource] using
          GraphPath.source_mem_vertexSet (N.redLocalConnector w)
      by_cases hxRedTarget : x = (N.redLocalConnector w).target
      · by_cases hxBlueSource : x = (N.blueLocalConnector w).source
        · exact False.elim (hblueSourceSplice hxBlueSource hxRedMem)
        · by_cases hxBlueTarget : x = (N.blueLocalConnector w).target
          · exact False.elim (hblueTargetSplice hxBlueTarget hxRedMem)
          · exact
              N.paperRouting_degreeAtMost_two_of_mem_branchSet_red_source_target_not_blue_endpoint
                hwT hwRB.1 hxw hxFirst hxLast hxRedSource hxRedTarget
                hxBlueSource hxBlueTarget
      · by_cases hxBlueSource : x = (N.blueLocalConnector w).source
        · exact False.elim (hblueSourceSplice hxBlueSource hxRedMem)
        · by_cases hxBlueTarget : x = (N.blueLocalConnector w).target
          · exact False.elim (hblueTargetSplice hxBlueTarget hxRedMem)
          · exact
              N.paperRouting_degreeAtMost_two_of_mem_branchSet_red_source_not_other_endpoint
                hwT hwRB.1 hxw hxFirst hxLast hxRedSource hxRedTarget
                hxBlueSource hxBlueTarget
    · by_cases hxRedTarget : x = (N.redLocalConnector w).target
      · have hxRedMem : x ∈ (N.redLocalConnector w).vertexSet := by
          simpa [hxRedTarget] using
            GraphPath.target_mem_vertexSet (N.redLocalConnector w)
        by_cases hxBlueSource : x = (N.blueLocalConnector w).source
        · exact False.elim (hblueSourceSplice hxBlueSource hxRedMem)
        · by_cases hxBlueTarget : x = (N.blueLocalConnector w).target
          · exact False.elim (hblueTargetSplice hxBlueTarget hxRedMem)
          · exact
              N.paperRouting_degreeAtMost_two_of_mem_branchSet_red_target_not_other_endpoint
                hwT hwRB.1 hxw hxFirst hxLast hxRedTarget hxRedSource
                hxBlueSource hxBlueTarget
      · by_cases hxBlueSource : x = (N.blueLocalConnector w).source
        · by_cases hxBlueTarget : x = (N.blueLocalConnector w).target
          · exact
              N.paperRouting_degreeAtMost_two_of_mem_branchSet_blue_source_target_not_red_endpoint
                hwT hwRB.2 hxw hxFirst hxLast hxBlueSource hxBlueTarget
                hxRedSource hxRedTarget
          · exact
              N.paperRouting_degreeAtMost_two_of_mem_branchSet_blue_source_not_other_endpoint
                hwT hwRB.2 hxw hxFirst hxLast hxBlueSource
                hxRedSource hxRedTarget hxBlueTarget
        · by_cases hxBlueTarget : x = (N.blueLocalConnector w).target
          · exact
              N.paperRouting_degreeAtMost_two_of_mem_branchSet_blue_target_not_other_endpoint
                hwT hwRB.2 hxw hxFirst hxLast hxBlueTarget
                hxRedSource hxRedTarget hxBlueSource
          · exact
              N.paperRouting_degreeAtMost_two_of_mem_branchSet_not_endpoint_not_splice
                hwT hxw hxFirst hxLast hxRedSource hxRedTarget
                hxBlueSource hxBlueTarget
  exact hxHigh hdeg

/-- Pair-subset form of the paper local branch-set bound. -/
theorem PaperRoutingBranchSetLocalBound_of_pairBound
    [Fintype V] [Fintype W]
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂)
    (a b : W → V)
    (hlocal :
      ∀ w : W,
        ∀ x : {v : V //
            ¬ DegreeAtMost
              (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) v 2},
          x.1 ∈ N.respecting.model.branchSet w →
            x.1 = a w ∨ x.1 = b w) :
    N.PaperRoutingBranchSetLocalBound := by
  classical
  intro w
  let B :=
    {v : V //
      ¬ DegreeAtMost
        (twoPackingUnionGraph N.paperRedRouting N.paperBlueRouting) v 2}
  let Lw : Type _ := {x : B // x.1 ∈ N.respecting.model.branchSet w}
  let code : Lw → Fin 2 := fun x =>
    if x.1.1 = a w then ⟨0, by omega⟩ else ⟨1, by omega⟩
  have hcode_inj : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    by_cases hxA : x.1.1 = a w
    · by_cases hyA : y.1.1 = a w
      · exact hxA.trans hyA.symm
      · have hcode_x :
            code x = ⟨0, by omega⟩ := by simp [code, hxA]
        have hcode_y :
            code y = ⟨1, by omega⟩ := by simp [code, hyA]
        have h01 : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
          hcode_x.symm.trans (hxy.trans hcode_y)
        exact False.elim (by
          have hval : (0 : ℕ) = 1 := congrArg Fin.val h01
          norm_num at hval)
    · by_cases hyA : y.1.1 = a w
      · have hcode_x :
            code x = ⟨1, by omega⟩ := by simp [code, hxA]
        have hcode_y :
            code y = ⟨0, by omega⟩ := by simp [code, hyA]
        have h10 : (⟨1, by omega⟩ : Fin 2) = ⟨0, by omega⟩ :=
          hcode_x.symm.trans (hxy.trans hcode_y)
        exact False.elim (by
          have hval : (1 : ℕ) = 0 := congrArg Fin.val h10
          norm_num at hval)
      · rcases hlocal w x.1 x.2 with hxEq | hxEq
        · exact False.elim (hxA hxEq)
        · rcases hlocal w y.1 y.2 with hyEq | hyEq
          · exact False.elim (hyA hyEq)
          · exact hxEq.trans hyEq.symm
  have hcard : Fintype.card Lw ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_injective code hcode_inj
  simpa [Lw, B] using hcard

end TwoPairGoodMinor

/-- A paper-literal minimal good minor for the two-pair instance, with the two
minimality tests separated into edge deletion and nonterminal edge
contraction. -/
structure TwoPairMinimalGoodMinor
    {W : Type w} [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (S₁ T₁ S₂ T₂ : Finset V) where
  /-- The minor is good for the two routing pairs. -/
  good : TwoPairGoodMinor G H S₁ T₁ S₂ T₂
  /-- Deleting any edge destroys goodness. -/
  edgeDeletion_not_good :
    ∀ ⦃a b : W⦄, H.Adj a b →
      ¬ Nonempty (TwoPairGoodMinor G
        (H.deleteEdges ({s(a, b)} : Set (Sym2 W))) S₁ T₁ S₂ T₂)
  /-- Contracting any nonterminal edge destroys goodness. -/
  edgeContraction_not_good :
    ∀ ⦃a b : W⦄ (hab : H.Adj a b),
      EdgeAvoidsTerminalRepresentatives good.respecting a b →
        ¬ Nonempty
          (TwoPairGoodMinor G (contractEdgeGraph H hab) S₁ T₁ S₂ T₂)

namespace TwoPairMinimalGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- Reverse the first terminal pair in a minimal good minor. -/
noncomputable def reverseRed
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂) :
    TwoPairMinimalGoodMinor G H T₁ S₁ S₂ T₂ where
  good := M.good.reverseRed
  edgeDeletion_not_good := by
    intro a b hab hgood
    rcases hgood with ⟨Ndel⟩
    exact M.edgeDeletion_not_good hab ⟨Ndel.reverseRed⟩
  edgeContraction_not_good := by
    intro a b hab havoid hgood
    have havoidOld :
        EdgeAvoidsTerminalRepresentatives M.good.respecting a b := by
      intro x hx
      have hx' :
          x ∈ twoPairTerminalSet T₁ S₁ S₂ T₂ := by
        simpa [twoPairTerminalSet_swap_first S₁ T₁ S₂ T₂] using hx
      have hcopy :
          (M.good.reverseRed.respecting).terminalVertex x hx' =
            M.good.respecting.terminalVertex x hx := by
        change
          (M.good.respecting.copyTerminalSet
              (twoPairTerminalSet_swap_first S₁ T₁ S₂ T₂).symm).terminalVertex
              x hx' =
            M.good.respecting.terminalVertex x hx
        simp [XRespectingMinorModel.copyTerminalSet]
      rcases havoid x hx' with ⟨ha, hb⟩
      exact ⟨fun hxa => ha (hcopy.trans hxa),
        fun hxb => hb (hcopy.trans hxb)⟩
    rcases hgood with ⟨Ncon⟩
    exact M.edgeContraction_not_good hab havoidOld ⟨Ncon.reverseRed⟩

/-- If the minimality notion also forbids deleting an unused nonterminal
vertex, then every nonterminal vertex belongs to at least one of the two
selected routings. -/
theorem vertex_mem_red_or_blue_of_vertexDeletion_not_good
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hvertexDeletion :
      ∀ ⦃v : W⦄,
        v ∉ M.good.terminalSet →
          ¬ Nonempty
            (TwoPairGoodMinor G
              (H.induce {w : W | w ∈ (Finset.univ.erase v : Finset W)})
              S₁ T₁ S₂ T₂))
    {v : W} (hvT : v ∉ M.good.terminalSet) :
    v ∈ M.good.redRouting.toPathPacking.vertexSet ∨
      v ∈ M.good.blueRouting.toPathPacking.vertexSet := by
  classical
  by_cases hvR : v ∈ M.good.redRouting.toPathPacking.vertexSet
  · exact Or.inl hvR
  by_cases hvB : v ∈ M.good.blueRouting.toPathPacking.vertexSet
  · exact Or.inr hvB
  exact False.elim
    (hvertexDeletion hvT
      ⟨M.good.deleteUnusedNonterminalVertex hvT hvR hvB⟩)

/-- In a minimal good minor, every edge is used by the red routing or by the
blue routing.  This is the formal edge-deletion argument from Section 2. -/
theorem edge_mem_red_or_blue
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W} (hab : H.Adj a b) :
    s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet ∨
      s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet := by
  classical
  by_contra hunusedBoth
  have hredUnused :
      s(a, b) ∉ M.good.redRouting.toPathPacking.edgeSet := by
    intro hred
    exact hunusedBoth (Or.inl hred)
  have hblueUnused :
      s(a, b) ∉ M.good.blueRouting.toPathPacking.edgeSet := by
    intro hblue
    exact hunusedBoth (Or.inr hblue)
  have hgoodDeleted :
      TwoPairGoodMinor G
        (H.deleteEdges ({s(a, b)} : Set (Sym2 W))) S₁ T₁ S₂ T₂ := {
    respecting := M.good.respecting.deleteEdges ({s(a, b)} : Set (Sym2 W))
    redRouting := perfectPathPacking_deleteUnusedEdge M.good.redRouting hredUnused
    blueRouting := perfectPathPacking_deleteUnusedEdge M.good.blueRouting hblueUnused
  }
  exact M.edgeDeletion_not_good hab ⟨hgoodDeleted⟩

/-- Every edge of a minimal good minor appears in the union of the chosen red
and blue routings. -/
theorem edge_le_twoPackingUnionGraph
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂) :
    H ≤ twoPackingUnionGraph M.good.redRouting M.good.blueRouting := by
  classical
  intro a b hab
  rcases M.edge_mem_red_or_blue hab with hred | hblue
  · have hredAdj :
        M.good.redRouting.toPathPacking.spanningGraph.Adj a b := by
      exact
        (M.good.redRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
          ⟨(M.good.redRouting.toPathPacking.mem_edgeSet).1 hred, hab.ne⟩
    simpa [twoPackingUnionGraph] using Or.inl hredAdj
  · have hblueAdj :
        M.good.blueRouting.toPathPacking.spanningGraph.Adj a b := by
      exact
        (M.good.blueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
          ⟨(M.good.blueRouting.toPathPacking.mem_edgeSet).1 hblue, hab.ne⟩
    simpa [twoPackingUnionGraph] using Or.inr hblueAdj

/-- In a minimal good minor, the graph is exactly the union of the chosen red
and blue routing graphs. -/
theorem twoPackingUnionGraph_eq
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂) :
    twoPackingUnionGraph M.good.redRouting M.good.blueRouting = H := by
  ext a b
  constructor
  · intro hab
    rcases (show
        M.good.redRouting.toPathPacking.spanningGraph.Adj a b ∨
          M.good.blueRouting.toPathPacking.spanningGraph.Adj a b by
        simpa [twoPackingUnionGraph] using hab) with hred | hblue
    · exact M.good.redRouting.toPathPacking.spanningGraph_le hred
    · exact M.good.blueRouting.toPathPacking.spanningGraph_le hblue
  · intro hab
    exact M.edge_le_twoPackingUnionGraph hab

/-- A terminal image avoids a nonterminal edge whenever the underlying
`X`-respecting model avoids that edge at all host terminals. -/
theorem terminalImage_avoids
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (havoid :
      EdgeAvoidsTerminalRepresentatives M.good.respecting a b)
    (S : Finset V) (hS : S ⊆ twoPairTerminalSet S₁ T₁ S₂ T₂) :
    ∀ y ∈ M.good.respecting.terminalImage S hS, y ≠ a ∧ y ≠ b := by
  intro y hy
  rcases (M.good.respecting.mem_terminalImage_iff S hS y).1 hy with
    ⟨x, hx, rfl⟩
  exact havoid x (hS hx)

/-- In a minimal good minor, a nonterminal edge cannot be used by both chosen
routings.  This is the formal edge-contraction argument from Section 2. -/
theorem not_red_and_blue
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W} (hab : H.Adj a b)
    (havoid :
      EdgeAvoidsTerminalRepresentatives M.good.respecting a b) :
    ¬ (s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet ∧
      s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet) := by
  classical
  rintro ⟨hred, hblue⟩
  let X := twoPairTerminalSet S₁ T₁ S₂ T₂
  let R := M.good.redRouting
  let B := M.good.blueRouting
  let Mc := M.good.respecting.contractNonterminalEdge hab havoid
  rcases (R.toPathPacking.mem_edgeSet).1 hred with ⟨ir, hir⟩
  rcases (B.toPathPacking.mem_edgeSet).1 hblue with ⟨ib, hib⟩
  have hared : a ∈ (R.path ir).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (R.path ir) hir).1
  have hbred : b ∈ (R.path ir).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (R.path ir) hir).2
  have hablu : a ∈ (B.path ib).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (B.path ib) hib).1
  have hbblu : b ∈ (B.path ib).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (B.path ib) hib).2
  have hS₁avoid :
      ∀ y ∈ M.good.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid S₁
      (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
  have hT₁avoid :
      ∀ y ∈ M.good.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid T₁
      (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
  have hS₂avoid :
      ∀ y ∈ M.good.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid S₂
      (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
  have hT₂avoid :
      ∀ y ∈ M.good.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid T₂
      (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
  let Rcontract :=
    perfectPathPacking_contractEdge R hab ir hared hbred hS₁avoid hT₁avoid
  let Bcontract :=
    perfectPathPacking_contractEdge B hab ib hablu hbblu hS₂avoid hT₂avoid
  have hS₁eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage S₁
            (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        S₁ (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hab havoid
  have hT₁eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage T₁
            (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        T₁ (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hab havoid
  have hS₂eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage S₂
            (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        S₂ (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hab havoid
  have hT₂eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage T₂
            (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        T₂ (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hab havoid
  have hgoodContract :
      TwoPairGoodMinor G (contractEdgeGraph H hab) S₁ T₁ S₂ T₂ := {
    respecting := Mc
    redRouting := Rcontract.copyTerminals hS₁eq hT₁eq
    blueRouting := Bcontract.copyTerminals hS₂eq hT₂eq
  }
  exact M.edgeContraction_not_good hab havoid ⟨hgoodContract⟩

/-- A nonterminal edge of a minimal good minor cannot be used by both chosen
routings.  This packages the paper's contraction-minimality argument with the
terminal-image avoidance condition. -/
theorem not_red_and_blue_of_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W} (hab : H.Adj a b)
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet) :
    ¬ (s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet ∧
      s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet) := by
  exact M.not_red_and_blue hab
    (M.good.edgeAvoidsTerminalRepresentatives_of_not_mem_terminalSet ha hb)

/-- Direct contradiction form of
`not_red_and_blue_of_not_mem_terminalSet`. -/
theorem false_of_red_and_blue_of_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W} (hab : H.Adj a b)
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hred : s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet)
    (hblue : s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet) :
    False :=
  M.not_red_and_blue_of_not_mem_terminalSet hab ha hb ⟨hred, hblue⟩

/-- A red edge and a blue edge cannot coincide on an edge incident to a
nonterminal vertex, under the terminal hypotheses of Theorem 2.1.

If the other endpoint is nonterminal this is the contraction-minimality
argument.  If the other endpoint is terminal, the terminal degree-one and
terminal-disjointness hypotheses force the terminal to belong to only its own
color of routing, contradicting the shared edge. -/
theorem false_of_red_and_blue_incident_nonterminal
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {v w : W}
    (hv : v ∉ M.good.terminalSet)
    (hred : s(v, w) ∈ M.good.redRouting.toPathPacking.edgeSet)
    (hblue : s(v, w) ∈ M.good.blueRouting.toPathPacking.edgeSet) :
    False := by
  classical
  by_cases hw : w ∈ M.good.terminalSet
  · exact M.good.false_of_red_and_blue_edge_incident_terminal hdeg hdisj
      hw hred hblue
  · have hedge : s(v, w) ∈ H.edgeSet :=
      M.good.redRouting.toPathPacking.edgeSet_subset_edgeSet hred
    have hab : H.Adj v w := by
      simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
    exact M.false_of_red_and_blue_of_not_mem_terminalSet
      hab hv hw hred hblue

/-- Under the Theorem 2.1 terminal hypotheses, no edge of a minimal good minor
is used by both selected routings. -/
theorem false_of_red_and_blue_edge
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {a b : W}
    (hred : s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet)
    (hblue : s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet) :
    False := by
  classical
  by_cases ha : a ∈ M.good.terminalSet
  · have hred' : s(b, a) ∈ M.good.redRouting.toPathPacking.edgeSet := by
      simpa [Sym2.eq_swap] using hred
    have hblue' : s(b, a) ∈ M.good.blueRouting.toPathPacking.edgeSet := by
      simpa [Sym2.eq_swap] using hblue
    exact M.good.false_of_red_and_blue_edge_incident_terminal
      hdeg hdisj ha hred' hblue'
  · exact M.false_of_red_and_blue_incident_nonterminal
      hdeg hdisj ha hred hblue

/-- A nonterminal minor vertex lying on both selected routings is a branch
vertex of their union.  The proof is the local core-incidence argument from
the paper: two red incidences and one blue incidence are distinct because a
minimal good minor has no shared red/blue edge incident with a nonterminal. -/
theorem branchVertex_of_red_blue_vertex_of_not_mem_terminalSet
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {v : W}
    (hvT : v ∉ M.good.terminalSet)
    (hvR : v ∈ M.good.redRouting.toPathPacking.vertexSet)
    (hvB : v ∈ M.good.blueRouting.toPathPacking.vertexSet) :
    v ∈ branchVertexFinset
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) := by
  classical
  rcases (M.good.redRouting.toPathPacking.mem_vertexSet).1 hvR with
    ⟨i, hvi⟩
  rcases (M.good.blueRouting.toPathPacking.mem_vertexSet).1 hvB with
    ⟨j, hvj⟩
  have hredInternal :=
    M.good.red_internal_of_mem_vertexSet_of_not_terminal (v := v) hvT
      (i := i)
  have hblueInternal :=
    M.good.blue_internal_of_mem_vertexSet_of_not_terminal (v := v) hvT
      (j := j)
  rcases
      GraphPath.exists_two_distinct_path_neighbors_of_internal
        (M.good.redRouting.path i) hvi hredInternal.1 hredInternal.2 with
    ⟨r₁, r₂, hr₁r₂, hr₁Edge, hr₂Edge⟩
  rcases
      GraphPath.exists_two_distinct_path_neighbors_of_internal
        (M.good.blueRouting.path j) hvj hblueInternal.1 hblueInternal.2 with
    ⟨b₁, _b₂, _hb₁b₂, hb₁Edge, _hb₂Edge⟩
  have hr₁Pack :
      s(v, r₁) ∈ M.good.redRouting.toPathPacking.edgeSet :=
    (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨i, hr₁Edge⟩
  have hr₂Pack :
      s(v, r₂) ∈ M.good.redRouting.toPathPacking.edgeSet :=
    (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨i, hr₂Edge⟩
  have hb₁Pack :
      s(v, b₁) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
    (M.good.blueRouting.toPathPacking.mem_edgeSet).2 ⟨j, hb₁Edge⟩
  have hb₁_ne_r₁ : b₁ ≠ r₁ := by
    intro h
    exact M.false_of_red_and_blue_incident_nonterminal hdeg hdisj hvT
      (by simpa [h] using hr₁Pack)
      (by simpa [h] using hb₁Pack)
  have hb₁_ne_r₂ : b₁ ≠ r₂ := by
    intro h
    exact M.false_of_red_and_blue_incident_nonterminal hdeg hdisj hvT
      (by simpa [h] using hr₂Pack)
      (by simpa [h] using hb₁Pack)
  have hv_ne_r₁ : v ≠ r₁ := by
    have hadj : H.Adj v r₁ := by
      simpa using GraphPath.edgeSet_subset_edgeSet
        (M.good.redRouting.path i) hr₁Edge
    exact hadj.ne
  have hv_ne_r₂ : v ≠ r₂ := by
    have hadj : H.Adj v r₂ := by
      simpa using GraphPath.edgeSet_subset_edgeSet
        (M.good.redRouting.path i) hr₂Edge
    exact hadj.ne
  have hv_ne_b₁ : v ≠ b₁ := by
    have hadj : H.Adj v b₁ := by
      simpa using GraphPath.edgeSet_subset_edgeSet
        (M.good.blueRouting.path j) hb₁Edge
    exact hadj.ne
  have hAdjR₁ :
      M.good.redRouting.toPathPacking.spanningGraph.Adj v r₁ :=
    (M.good.redRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
      ⟨⟨i, hr₁Edge⟩, hv_ne_r₁⟩
  have hAdjR₂ :
      M.good.redRouting.toPathPacking.spanningGraph.Adj v r₂ :=
    (M.good.redRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
      ⟨⟨i, hr₂Edge⟩, hv_ne_r₂⟩
  have hAdjB₁ :
      M.good.blueRouting.toPathPacking.spanningGraph.Adj v b₁ :=
    (M.good.blueRouting.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
      ⟨⟨j, hb₁Edge⟩, hv_ne_b₁⟩
  have hUnionR₁ :
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting).Adj v r₁ := by
    simpa [twoPackingUnionGraph] using Or.inl hAdjR₁
  have hUnionR₂ :
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting).Adj v r₂ := by
    simpa [twoPackingUnionGraph] using Or.inl hAdjR₂
  have hUnionB₁ :
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting).Adj v b₁ := by
    simpa [twoPackingUnionGraph] using Or.inr hAdjB₁
  have hnotDegree :
      ¬ DegreeAtMost
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) v 2 :=
    not_degreeAtMost_two_of_three_adj
      hUnionR₁ hUnionR₂ hUnionB₁
      hr₁r₂ hb₁_ne_r₁.symm hb₁_ne_r₂.symm
  exact Finset.mem_filter.2 ⟨Finset.mem_univ v, hnotDegree⟩

/-- Every high-degree host vertex of the lifted routings belongs to a branch
set whose minor vertex is high-degree in the selected minor red/blue union. -/
theorem liftedRouting_highVertex_branchSet_minor_branchVertex
    [Fintype V] [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x : V} {w : W}
    (hxHigh :
      ¬ DegreeAtMost
        (twoPackingUnionGraph
          M.good.liftRedRouting M.good.liftBlueRouting) x 2)
    (hxw : x ∈ M.good.respecting.model.branchSet w) :
    w ∈ branchVertexFinset
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) := by
  classical
  have hwRB :
      w ∈ M.good.redRouting.toPathPacking.vertexSet ∧
        w ∈ M.good.blueRouting.toPathPacking.vertexSet :=
    M.good.liftedRouting_highVertex_branchSet_minorVertex_mem_red_blue
      hxHigh hxw
  by_cases hwT : w ∈ M.good.terminalSet
  · have hxT :
        x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ :=
      M.good.host_mem_terminalSet_of_mem_branchSet_terminal hwT hxw
    exact False.elim
      (hxHigh
        (M.good.liftedRouting_degreeAtMost_two_of_mem_terminalSet hdeg hxT))
  · exact
      M.branchVertex_of_red_blue_vertex_of_not_mem_terminalSet
        hdeg hdisj hwT hwRB.1 hwRB.2

/-- Every high-degree host vertex of the paper-expanded routings belongs to a
branch set whose minor vertex is high-degree in the selected minor red/blue
union. -/
theorem paperRouting_highVertex_branchSet_minor_branchVertex
    [Fintype V] [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x : V} {w : W}
    (hxHigh :
      ¬ DegreeAtMost
        (twoPackingUnionGraph
          M.good.paperRedRouting M.good.paperBlueRouting) x 2)
    (hxw : x ∈ M.good.respecting.model.branchSet w) :
    w ∈ branchVertexFinset
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) := by
  classical
  have hwRB :
      w ∈ M.good.redRouting.toPathPacking.vertexSet ∧
        w ∈ M.good.blueRouting.toPathPacking.vertexSet :=
    M.good.paperRouting_highVertex_branchSet_minorVertex_mem_red_blue
      hxHigh hxw
  by_cases hwT : w ∈ M.good.terminalSet
  · have hxT :
        x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ :=
      M.good.host_mem_terminalSet_of_mem_branchSet_terminal hwT hxw
    exact False.elim
      (hxHigh
        (M.good.paperRouting_degreeAtMost_two_of_mem_terminalSet hdeg hxT))
  · exact
      M.branchVertex_of_red_blue_vertex_of_not_mem_terminalSet
        hdeg hdisj hwT hwRB.1 hwRB.2

/-- The paper-expanded routings satisfy the branch-set-local `≤ 2` bound:
inside each branch set, every high-degree host vertex is one of the two local
splice vertices. -/
theorem paperRoutingBranchSetLocalBound
    [Fintype V] [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    M.good.PaperRoutingBranchSetLocalBound := by
  classical
  refine
    M.good.PaperRoutingBranchSetLocalBound_of_pairBound
      M.good.paperLocalSpliceFirst M.good.paperLocalSpliceLast ?_
  intro w x hxw
  by_cases hwT : w ∈ M.good.terminalSet
  · have hxT :
        x.1 ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ :=
      M.good.host_mem_terminalSet_of_mem_branchSet_terminal hwT hxw
    exact False.elim
      (x.2 (M.good.paperRouting_degreeAtMost_two_of_mem_terminalSet hdeg hxT))
  · have hwRB :
        w ∈ M.good.redRouting.toPathPacking.vertexSet ∧
          w ∈ M.good.blueRouting.toPathPacking.vertexSet :=
      M.good.paperRouting_highVertex_branchSet_minorVertex_mem_red_blue
        x.2 hxw
    exact
      M.good.paperRouting_highVertex_branchSet_eq_splice
        hwT hwRB hxw x.2

/-- The lifted routings give a controlled expansion whose buckets are only
the branch vertices of the minor red/blue union. -/
noncomputable def controlledExpansionOfLiftedRoutingMinorBranchVertices
    [Fintype V] [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (hlocal : M.good.LiftedRoutingBranchSetLocalBound) :
    TwoPairControlledExpansion
      (W :=
        {w : W //
          w ∈ branchVertexFinset
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)})
      G S₁ T₁ S₂ T₂ := by
  classical
  let U :=
    twoPackingUnionGraph M.good.liftRedRouting M.good.liftBlueRouting
  let B := {v : V // ¬ DegreeAtMost U v 2}
  let R :=
    branchVertexFinset
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)
  let branchOf : B → {w : W // w ∈ R} := fun x =>
    let w := Classical.choose (M.good.liftedRouting_highVertex_mem_branchSet x)
    ⟨w, by
      have hxw :
          x.1 ∈ M.good.respecting.model.branchSet w :=
        Classical.choose_spec (M.good.liftedRouting_highVertex_mem_branchSet x)
      exact
        M.liftedRouting_highVertex_branchSet_minor_branchVertex
          hdeg hdisj (by simpa [U] using x.2) hxw⟩
  refine
    { red := M.good.liftRedRouting
      blue := M.good.liftBlueRouting
      branchOf := branchOf
      fiber_le_two := ?_ }
  intro b
  let Fw : Type _ := {x : B // branchOf x = b}
  let Lw : Type _ :=
    {x : B // x.1 ∈ M.good.respecting.model.branchSet b.1}
  change Fintype.card Fw ≤ 2
  have hinj : Fw ↪ Lw := {
    toFun := fun x =>
      ⟨x.1, by
        have hxmem :
            x.1.1 ∈ M.good.respecting.model.branchSet
              (Classical.choose
                (M.good.liftedRouting_highVertex_mem_branchSet x.1)) :=
          Classical.choose_spec
            (M.good.liftedRouting_highVertex_mem_branchSet x.1)
        have hbranch :
            Classical.choose
                (M.good.liftedRouting_highVertex_mem_branchSet x.1) =
              b.1 :=
          congrArg Subtype.val x.2
        simpa [hbranch] using hxmem⟩
    inj' := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : Lw => z.1) hxy
  }
  have hcard : Fintype.card Fw ≤ Fintype.card Lw :=
    Fintype.card_le_of_injective _ hinj.injective
  have hlocal_b : Fintype.card Lw ≤ 2 := by
    simpa [Lw, B, U] using hlocal b.1
  exact hcard.trans hlocal_b

/-- The paper-expanded routings give a controlled expansion whose buckets are
only the branch vertices of the minor red/blue union, once the paper's local
branch-set bound is available. -/
noncomputable def controlledExpansionOfPaperRoutingMinorBranchVertices
    [Fintype V] [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (hlocal : M.good.PaperRoutingBranchSetLocalBound) :
    TwoPairControlledExpansion
      (W :=
        {w : W //
          w ∈ branchVertexFinset
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)})
      G S₁ T₁ S₂ T₂ := by
  classical
  let U :=
    twoPackingUnionGraph M.good.paperRedRouting M.good.paperBlueRouting
  let B := {v : V // ¬ DegreeAtMost U v 2}
  let R :=
    branchVertexFinset
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)
  let branchOf : B → {w : W // w ∈ R} := fun x =>
    let w := Classical.choose (M.good.paperRouting_highVertex_mem_branchSet x)
    ⟨w, by
      have hxw :
          x.1 ∈ M.good.respecting.model.branchSet w :=
        Classical.choose_spec (M.good.paperRouting_highVertex_mem_branchSet x)
      exact
        M.paperRouting_highVertex_branchSet_minor_branchVertex
          hdeg hdisj (by simpa [U] using x.2) hxw⟩
  refine
    { red := M.good.paperRedRouting
      blue := M.good.paperBlueRouting
      branchOf := branchOf
      fiber_le_two := ?_ }
  intro b
  let Fw : Type _ := {x : B // branchOf x = b}
  let Lw : Type _ :=
    {x : B // x.1 ∈ M.good.respecting.model.branchSet b.1}
  change Fintype.card Fw ≤ 2
  have hinj : Fw ↪ Lw := {
    toFun := fun x =>
      ⟨x.1, by
        have hxmem :
            x.1.1 ∈ M.good.respecting.model.branchSet
              (Classical.choose
                (M.good.paperRouting_highVertex_mem_branchSet x.1)) :=
          Classical.choose_spec
            (M.good.paperRouting_highVertex_mem_branchSet x.1)
        have hbranch :
            Classical.choose
                (M.good.paperRouting_highVertex_mem_branchSet x.1) =
              b.1 :=
          congrArg Subtype.val x.2
        simpa [hbranch] using hxmem⟩
    inj' := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : Lw => z.1) hxy
  }
  have hcard : Fintype.card Fw ≤ Fintype.card Lw :=
    Fintype.card_le_of_injective _ hinj.injective
  have hlocal_b : Fintype.card Lw ≤ 2 := by
    simpa [Lw, B, U] using hlocal b.1
  exact hcard.trans hlocal_b

/-- Under the Theorem 2.1 terminal hypotheses, every edge of a minimal good
minor has exactly one of the two colors. -/
theorem edge_mem_red_xor_blue
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {a b : W} (hab : H.Adj a b) :
    (s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet ∧
        s(a, b) ∉ M.good.blueRouting.toPathPacking.edgeSet) ∨
      (s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet ∧
        s(a, b) ∉ M.good.redRouting.toPathPacking.edgeSet) := by
  classical
  rcases M.edge_mem_red_or_blue hab with hred | hblue
  · exact Or.inl
      ⟨hred, fun hblue =>
        M.false_of_red_and_blue_edge hdeg hdisj hred hblue⟩
  · exact Or.inr
      ⟨hblue, fun hred =>
        M.false_of_red_and_blue_edge hdeg hdisj hred hblue⟩

/-- No arbitrary red routing can use an edge of the selected blue routing in a
minimal good minor under the Theorem 2.1 terminal hypotheses. -/
theorem false_of_redRouting_and_blue_edge
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (R' : PerfectPathPacking H
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)))
    {a b : W}
    (hred : s(a, b) ∈ R'.toPathPacking.edgeSet)
    (hblue : s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet) :
    False := by
  classical
  by_cases ha : a ∈ M.good.terminalSet
  · have hred' : s(b, a) ∈ R'.toPathPacking.edgeSet := by
      simpa [Sym2.eq_swap] using hred
    have hblue' : s(b, a) ∈ M.good.blueRouting.toPathPacking.edgeSet := by
      simpa [Sym2.eq_swap] using hblue
    exact M.good.false_of_redRouting_and_blue_edge_incident_terminal
      hdeg hdisj R' ha hred' hblue'
  · by_cases hb : b ∈ M.good.terminalSet
    · exact M.good.false_of_redRouting_and_blue_edge_incident_terminal
        hdeg hdisj R' hb hred hblue
    · have hedge : s(a, b) ∈ H.edgeSet :=
        M.good.blueRouting.toPathPacking.edgeSet_subset_edgeSet hblue
      have hab : H.Adj a b := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
      let X := twoPairTerminalSet S₁ T₁ S₂ T₂
      let Mc := M.good.respecting.contractNonterminalEdge hab
        (M.good.edgeAvoidsTerminalRepresentatives_of_not_mem_terminalSet ha hb)
      rcases (R'.toPathPacking.mem_edgeSet).1 hred with ⟨ir, hir⟩
      rcases (M.good.blueRouting.toPathPacking.mem_edgeSet).1 hblue with
        ⟨ib, hib⟩
      have hared : a ∈ (R'.path ir).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet (R'.path ir) hir).1
      have hbred : b ∈ (R'.path ir).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet (R'.path ir) hir).2
      have hablu : a ∈ (M.good.blueRouting.path ib).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (M.good.blueRouting.path ib) hib).1
      have hbblu : b ∈ (M.good.blueRouting.path ib).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (M.good.blueRouting.path ib) hib).2
      have havoid :
          EdgeAvoidsTerminalRepresentatives M.good.respecting a b :=
        M.good.edgeAvoidsTerminalRepresentatives_of_not_mem_terminalSet ha hb
      have hS₁avoid :
          ∀ y ∈ M.good.respecting.terminalImage S₁
              (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂),
            y ≠ a ∧ y ≠ b :=
        M.terminalImage_avoids havoid S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
      have hT₁avoid :
          ∀ y ∈ M.good.respecting.terminalImage T₁
              (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂),
            y ≠ a ∧ y ≠ b :=
        M.terminalImage_avoids havoid T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
      have hS₂avoid :
          ∀ y ∈ M.good.respecting.terminalImage S₂
              (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂),
            y ≠ a ∧ y ≠ b :=
        M.terminalImage_avoids havoid S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
      have hT₂avoid :
          ∀ y ∈ M.good.respecting.terminalImage T₂
              (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂),
            y ≠ a ∧ y ≠ b :=
        M.terminalImage_avoids havoid T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
      let Rcontract :=
        perfectPathPacking_contractEdge R' hab ir hared hbred hS₁avoid hT₁avoid
      let Bcontract :=
        perfectPathPacking_contractEdge M.good.blueRouting hab ib hablu hbblu
          hS₂avoid hT₂avoid
      have hS₁eq :
          edgeContractImageSet (a := a) (b := b)
              (M.good.respecting.terminalImage S₁
                (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)) =
            Mc.terminalImage S₁
              (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
        simpa [Mc] using
          M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
            S₁ (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hab havoid
      have hT₁eq :
          edgeContractImageSet (a := a) (b := b)
              (M.good.respecting.terminalImage T₁
                (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)) =
            Mc.terminalImage T₁
              (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
        simpa [Mc] using
          M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
            T₁ (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hab havoid
      have hS₂eq :
          edgeContractImageSet (a := a) (b := b)
              (M.good.respecting.terminalImage S₂
                (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)) =
            Mc.terminalImage S₂
              (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
        simpa [Mc] using
          M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
            S₂ (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hab havoid
      have hT₂eq :
          edgeContractImageSet (a := a) (b := b)
              (M.good.respecting.terminalImage T₂
                (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) =
            Mc.terminalImage T₂
              (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
        simpa [Mc] using
          M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
            T₂ (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hab havoid
      have hgoodContract :
          TwoPairGoodMinor G (contractEdgeGraph H hab) S₁ T₁ S₂ T₂ := {
        respecting := Mc
        redRouting := Rcontract.copyTerminals hS₁eq hT₁eq
        blueRouting := Bcontract.copyTerminals hS₂eq hT₂eq
      }
      exact M.edgeContraction_not_good hab havoid ⟨hgoodContract⟩

/-- Symmetric form: no arbitrary blue routing can use an edge of the selected
red routing in a minimal good minor. -/
theorem false_of_red_edge_and_blueRouting
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (B' : PerfectPathPacking H
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)))
    {a b : W}
    (hred : s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet)
    (hblue : s(a, b) ∈ B'.toPathPacking.edgeSet) :
    False := by
  classical
  by_cases ha : a ∈ M.good.terminalSet
  · have hred' : s(b, a) ∈ M.good.redRouting.toPathPacking.edgeSet := by
      simpa [Sym2.eq_swap] using hred
    have hblue' : s(b, a) ∈ B'.toPathPacking.edgeSet := by
      simpa [Sym2.eq_swap] using hblue
    exact M.good.false_of_red_edge_and_blueRouting_incident_terminal
      hdeg hdisj B' ha hred' hblue'
  · by_cases hb : b ∈ M.good.terminalSet
    · exact M.good.false_of_red_edge_and_blueRouting_incident_terminal
        hdeg hdisj B' hb hred hblue
    · have hedge : s(a, b) ∈ H.edgeSet :=
        M.good.redRouting.toPathPacking.edgeSet_subset_edgeSet hred
      have hab : H.Adj a b := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
      let Mc := M.good.respecting.contractNonterminalEdge hab
        (M.good.edgeAvoidsTerminalRepresentatives_of_not_mem_terminalSet ha hb)
      rcases (M.good.redRouting.toPathPacking.mem_edgeSet).1 hred with
        ⟨ir, hir⟩
      rcases (B'.toPathPacking.mem_edgeSet).1 hblue with ⟨ib, hib⟩
      have hared : a ∈ (M.good.redRouting.path ir).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (M.good.redRouting.path ir) hir).1
      have hbred : b ∈ (M.good.redRouting.path ir).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (M.good.redRouting.path ir) hir).2
      have hablu : a ∈ (B'.path ib).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet (B'.path ib) hib).1
      have hbblu : b ∈ (B'.path ib).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet (B'.path ib) hib).2
      have havoid :
          EdgeAvoidsTerminalRepresentatives M.good.respecting a b :=
        M.good.edgeAvoidsTerminalRepresentatives_of_not_mem_terminalSet ha hb
      have hS₁avoid :
          ∀ y ∈ M.good.respecting.terminalImage S₁
              (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂),
            y ≠ a ∧ y ≠ b :=
        M.terminalImage_avoids havoid S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
      have hT₁avoid :
          ∀ y ∈ M.good.respecting.terminalImage T₁
              (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂),
            y ≠ a ∧ y ≠ b :=
        M.terminalImage_avoids havoid T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
      have hS₂avoid :
          ∀ y ∈ M.good.respecting.terminalImage S₂
              (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂),
            y ≠ a ∧ y ≠ b :=
        M.terminalImage_avoids havoid S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
      have hT₂avoid :
          ∀ y ∈ M.good.respecting.terminalImage T₂
              (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂),
            y ≠ a ∧ y ≠ b :=
        M.terminalImage_avoids havoid T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
      let Rcontract :=
        perfectPathPacking_contractEdge M.good.redRouting hab ir hared hbred
          hS₁avoid hT₁avoid
      let Bcontract :=
        perfectPathPacking_contractEdge B' hab ib hablu hbblu hS₂avoid hT₂avoid
      have hS₁eq :
          edgeContractImageSet (a := a) (b := b)
              (M.good.respecting.terminalImage S₁
                (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)) =
            Mc.terminalImage S₁
              (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
        simpa [Mc] using
          M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
            S₁ (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hab havoid
      have hT₁eq :
          edgeContractImageSet (a := a) (b := b)
              (M.good.respecting.terminalImage T₁
                (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)) =
            Mc.terminalImage T₁
              (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
        simpa [Mc] using
          M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
            T₁ (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hab havoid
      have hS₂eq :
          edgeContractImageSet (a := a) (b := b)
              (M.good.respecting.terminalImage S₂
                (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)) =
            Mc.terminalImage S₂
              (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
        simpa [Mc] using
          M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
            S₂ (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hab havoid
      have hT₂eq :
          edgeContractImageSet (a := a) (b := b)
              (M.good.respecting.terminalImage T₂
                (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) =
            Mc.terminalImage T₂
              (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
        simpa [Mc] using
          M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
            T₂ (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hab havoid
      have hgoodContract :
          TwoPairGoodMinor G (contractEdgeGraph H hab) S₁ T₁ S₂ T₂ := {
        respecting := Mc
        redRouting := Rcontract.copyTerminals hS₁eq hT₁eq
        blueRouting := Bcontract.copyTerminals hS₂eq hT₂eq
      }
      exact M.edgeContraction_not_good hab havoid ⟨hgoodContract⟩

/-- A red edge between nonterminals cannot have its left endpoint outside the
blue routing.  Contracting such an edge preserves the red routing directly and
preserves the blue routing by projection, because the left endpoint is unused
by every blue path. -/
theorem false_of_red_edge_left_not_blue_vertex_of_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hred : s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet)
    (haBlue : a ∉ M.good.blueRouting.toPathPacking.vertexSet) :
    False := by
  classical
  have hedge : s(a, b) ∈ H.edgeSet :=
    M.good.redRouting.toPathPacking.edgeSet_subset_edgeSet hred
  have hab : H.Adj a b := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
  have havoid :
      EdgeAvoidsTerminalRepresentatives M.good.respecting a b :=
    M.good.edgeAvoidsTerminalRepresentatives_of_not_mem_terminalSet ha hb
  let Mc := M.good.respecting.contractNonterminalEdge hab havoid
  rcases (M.good.redRouting.toPathPacking.mem_edgeSet).1 hred with
    ⟨ir, hir⟩
  have hared : a ∈ (M.good.redRouting.path ir).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.good.redRouting.path ir) hir).1
  have hbred : b ∈ (M.good.redRouting.path ir).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.good.redRouting.path ir) hir).2
  have hS₁avoid :
      ∀ y ∈ M.good.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid S₁
      (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
  have hT₁avoid :
      ∀ y ∈ M.good.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid T₁
      (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
  have hS₂avoid :
      ∀ y ∈ M.good.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid S₂
      (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
  have hT₂avoid :
      ∀ y ∈ M.good.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid T₂
      (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
  let Rcontract :=
    perfectPathPacking_contractEdge M.good.redRouting hab ir hared hbred
      hS₁avoid hT₁avoid
  let Bcontract :=
    perfectPathPacking_contractEdge_of_left_not_mem_vertexSet
      M.good.blueRouting hab haBlue hS₂avoid hT₂avoid
  have hS₁eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage S₁
            (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        S₁ (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hab havoid
  have hT₁eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage T₁
            (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        T₁ (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hab havoid
  have hS₂eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage S₂
            (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        S₂ (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hab havoid
  have hT₂eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage T₂
            (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        T₂ (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hab havoid
  have hgoodContract :
      TwoPairGoodMinor G (contractEdgeGraph H hab) S₁ T₁ S₂ T₂ := {
    respecting := Mc
    redRouting := Rcontract.copyTerminals hS₁eq hT₁eq
    blueRouting := Bcontract.copyTerminals hS₂eq hT₂eq
  }
  exact M.edgeContraction_not_good hab havoid ⟨hgoodContract⟩

/-- Right-endpoint version of
`false_of_red_edge_left_not_blue_vertex_of_not_mem_terminalSet`. -/
theorem false_of_red_edge_right_not_blue_vertex_of_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hred : s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet)
    (hbBlue : b ∉ M.good.blueRouting.toPathPacking.vertexSet) :
    False := by
  exact
    M.false_of_red_edge_left_not_blue_vertex_of_not_mem_terminalSet
      hb ha (by simpa [Sym2.eq_swap] using hred) hbBlue

/-- Blue analogue of
`false_of_red_edge_left_not_blue_vertex_of_not_mem_terminalSet`. -/
theorem false_of_blue_edge_left_not_red_vertex_of_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hblue : s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet)
    (haRed : a ∉ M.good.redRouting.toPathPacking.vertexSet) :
    False := by
  classical
  have hedge : s(a, b) ∈ H.edgeSet :=
    M.good.blueRouting.toPathPacking.edgeSet_subset_edgeSet hblue
  have hab : H.Adj a b := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
  have havoid :
      EdgeAvoidsTerminalRepresentatives M.good.respecting a b :=
    M.good.edgeAvoidsTerminalRepresentatives_of_not_mem_terminalSet ha hb
  let Mc := M.good.respecting.contractNonterminalEdge hab havoid
  rcases (M.good.blueRouting.toPathPacking.mem_edgeSet).1 hblue with
    ⟨ib, hib⟩
  have hablue : a ∈ (M.good.blueRouting.path ib).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.good.blueRouting.path ib) hib).1
  have hbblue : b ∈ (M.good.blueRouting.path ib).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.good.blueRouting.path ib) hib).2
  have hS₁avoid :
      ∀ y ∈ M.good.respecting.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid S₁
      (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)
  have hT₁avoid :
      ∀ y ∈ M.good.respecting.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid T₁
      (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)
  have hS₂avoid :
      ∀ y ∈ M.good.respecting.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid S₂
      (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)
  have hT₂avoid :
      ∀ y ∈ M.good.respecting.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂),
        y ≠ a ∧ y ≠ b :=
    M.terminalImage_avoids havoid T₂
      (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)
  let Rcontract :=
    perfectPathPacking_contractEdge_of_left_not_mem_vertexSet
      M.good.redRouting hab haRed hS₁avoid hT₁avoid
  let Bcontract :=
    perfectPathPacking_contractEdge M.good.blueRouting hab ib hablue hbblue
      hS₂avoid hT₂avoid
  have hS₁eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage S₁
            (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage S₁
          (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        S₁ (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hab havoid
  have hT₁eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage T₁
            (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage T₁
          (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        T₁ (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) hab havoid
  have hS₂eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage S₂
            (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage S₂
          (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        S₂ (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) hab havoid
  have hT₂eq :
      edgeContractImageSet (a := a) (b := b)
          (M.good.respecting.terminalImage T₂
            (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) =
        Mc.terminalImage T₂
          (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
    simpa [Mc] using
      M.good.respecting.edgeContractImageSet_terminalImage_eq_contractNonterminalEdge
        T₂ (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) hab havoid
  have hgoodContract :
      TwoPairGoodMinor G (contractEdgeGraph H hab) S₁ T₁ S₂ T₂ := {
    respecting := Mc
    redRouting := Rcontract.copyTerminals hS₁eq hT₁eq
    blueRouting := Bcontract.copyTerminals hS₂eq hT₂eq
  }
  exact M.edgeContraction_not_good hab havoid ⟨hgoodContract⟩

/-- Right-endpoint version of
`false_of_blue_edge_left_not_red_vertex_of_not_mem_terminalSet`. -/
theorem false_of_blue_edge_right_not_red_vertex_of_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hblue : s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet)
    (hbRed : b ∉ M.good.redRouting.toPathPacking.vertexSet) :
    False := by
  exact
    M.false_of_blue_edge_left_not_red_vertex_of_not_mem_terminalSet
      hb ha (by simpa [Sym2.eq_swap] using hblue) hbRed

/-- If a red edge joins two nonterminals, then its left endpoint is forced to
belong to the blue routing. -/
theorem blue_vertex_of_red_edge_left_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hred : s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet) :
    a ∈ M.good.blueRouting.toPathPacking.vertexSet := by
  classical
  by_contra haBlue
  exact M.false_of_red_edge_left_not_blue_vertex_of_not_mem_terminalSet
    ha hb hred haBlue

/-- If a red edge joins two nonterminals, then its right endpoint is forced to
belong to the blue routing. -/
theorem blue_vertex_of_red_edge_right_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hred : s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet) :
    b ∈ M.good.blueRouting.toPathPacking.vertexSet := by
  classical
  by_contra hbBlue
  exact M.false_of_red_edge_right_not_blue_vertex_of_not_mem_terminalSet
    ha hb hred hbBlue

/-- If a blue edge joins two nonterminals, then its left endpoint is forced to
belong to the red routing. -/
theorem red_vertex_of_blue_edge_left_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hblue : s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet) :
    a ∈ M.good.redRouting.toPathPacking.vertexSet := by
  classical
  by_contra haRed
  exact M.false_of_blue_edge_left_not_red_vertex_of_not_mem_terminalSet
    ha hb hblue haRed

/-- If a blue edge joins two nonterminals, then its right endpoint is forced
to belong to the red routing. -/
theorem red_vertex_of_blue_edge_right_not_mem_terminalSet
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {a b : W}
    (ha : a ∉ M.good.terminalSet) (hb : b ∉ M.good.terminalSet)
    (hblue : s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet) :
    b ∈ M.good.redRouting.toPathPacking.vertexSet := by
  classical
  by_contra hbRed
  exact M.false_of_blue_edge_right_not_red_vertex_of_not_mem_terminalSet
    ha hb hblue hbRed

/-- Every selected red edge of a minimal good minor is unavoidable for any
other routing of the red terminal pair.  Otherwise deleting that edge would
preserve the alternate red routing and, because no selected edge is both red
and blue, preserve the selected blue routing as well. -/
theorem red_edge_mem_of_any_redRouting
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (R' : PerfectPathPacking H
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)))
    {e : Sym2 W}
    (heRed : e ∈ M.good.redRouting.toPathPacking.edgeSet) :
    e ∈ R'.toPathPacking.edgeSet := by
  classical
  by_contra heR'
  let a : W := e.out.1
  let b : W := e.out.2
  have heout : s(a, b) = e := by
    have heout0 : s(e.out.1, e.out.2) = e := by
      rw [Sym2.mk, e.out_eq]
    simpa [a, b] using heout0
  have heRed' : s(a, b) ∈ M.good.redRouting.toPathPacking.edgeSet := by
    simpa [heout] using heRed
  have heR'unused : s(a, b) ∉ R'.toPathPacking.edgeSet := by
    intro h
    exact heR' (by simpa [heout] using h)
  have heBlueUnused :
      s(a, b) ∉ M.good.blueRouting.toPathPacking.edgeSet := by
    intro hblue
    exact M.false_of_red_and_blue_edge hdeg hdisj heRed' hblue
  have hedge : s(a, b) ∈ H.edgeSet :=
    M.good.redRouting.toPathPacking.edgeSet_subset_edgeSet heRed'
  have hab : H.Adj a b := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
  have hgoodDeleted :
      TwoPairGoodMinor G
        (H.deleteEdges ({s(a, b)} : Set (Sym2 W))) S₁ T₁ S₂ T₂ := {
    respecting := M.good.respecting.deleteEdges ({s(a, b)} : Set (Sym2 W))
    redRouting := perfectPathPacking_deleteUnusedEdge R' heR'unused
    blueRouting :=
      perfectPathPacking_deleteUnusedEdge M.good.blueRouting heBlueUnused
  }
  exact M.edgeDeletion_not_good hab ⟨hgoodDeleted⟩

/-- Blue analogue of `red_edge_mem_of_any_redRouting`. -/
theorem blue_edge_mem_of_any_blueRouting
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (B' : PerfectPathPacking H
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)))
    {e : Sym2 W}
    (heBlue : e ∈ M.good.blueRouting.toPathPacking.edgeSet) :
    e ∈ B'.toPathPacking.edgeSet := by
  classical
  by_contra heB'
  let a : W := e.out.1
  let b : W := e.out.2
  have heout : s(a, b) = e := by
    have heout0 : s(e.out.1, e.out.2) = e := by
      rw [Sym2.mk, e.out_eq]
    simpa [a, b] using heout0
  have heBlue' : s(a, b) ∈ M.good.blueRouting.toPathPacking.edgeSet := by
    simpa [heout] using heBlue
  have heB'unused : s(a, b) ∉ B'.toPathPacking.edgeSet := by
    intro h
    exact heB' (by simpa [heout] using h)
  have heRedUnused :
      s(a, b) ∉ M.good.redRouting.toPathPacking.edgeSet := by
    intro hred
    exact M.false_of_red_and_blue_edge hdeg hdisj hred heBlue'
  have hedge : s(a, b) ∈ H.edgeSet :=
    M.good.blueRouting.toPathPacking.edgeSet_subset_edgeSet heBlue'
  have hab : H.Adj a b := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
  have hgoodDeleted :
      TwoPairGoodMinor G
        (H.deleteEdges ({s(a, b)} : Set (Sym2 W))) S₁ T₁ S₂ T₂ := {
    respecting := M.good.respecting.deleteEdges ({s(a, b)} : Set (Sym2 W))
    redRouting :=
      perfectPathPacking_deleteUnusedEdge M.good.redRouting heRedUnused
    blueRouting := perfectPathPacking_deleteUnusedEdge B' heB'unused
  }
  exact M.edgeDeletion_not_good hab ⟨hgoodDeleted⟩

/-- Every edge used by an arbitrary red routing is one of the selected red
edges.  If it were a selected blue edge, the alternate red routing and the
selected blue routing would survive contracting that edge. -/
theorem redRouting_edgeSet_subset_selected
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (R' : PerfectPathPacking H
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))) :
    R'.toPathPacking.edgeSet ⊆ M.good.redRouting.toPathPacking.edgeSet := by
  classical
  intro e heR'
  let a : W := e.out.1
  let b : W := e.out.2
  have heout : s(a, b) = e := by
    have heout0 : s(e.out.1, e.out.2) = e := by
      rw [Sym2.mk, e.out_eq]
    simpa [a, b] using heout0
  have heR'ab : s(a, b) ∈ R'.toPathPacking.edgeSet := by
    simpa [heout] using heR'
  have hedge : s(a, b) ∈ H.edgeSet :=
    R'.toPathPacking.edgeSet_subset_edgeSet heR'ab
  have hab : H.Adj a b := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
  rcases M.edge_mem_red_or_blue hab with hred | hblue
  · simpa [heout] using hred
  · exact False.elim
      (M.false_of_redRouting_and_blue_edge hdeg hdisj R' heR'ab hblue)

/-- Every edge used by an arbitrary blue routing is one of the selected blue
edges. -/
theorem blueRouting_edgeSet_subset_selected
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (B' : PerfectPathPacking H
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))) :
    B'.toPathPacking.edgeSet ⊆ M.good.blueRouting.toPathPacking.edgeSet := by
  classical
  intro e heB'
  let a : W := e.out.1
  let b : W := e.out.2
  have heout : s(a, b) = e := by
    have heout0 : s(e.out.1, e.out.2) = e := by
      rw [Sym2.mk, e.out_eq]
    simpa [a, b] using heout0
  have heB'ab : s(a, b) ∈ B'.toPathPacking.edgeSet := by
    simpa [heout] using heB'
  have hedge : s(a, b) ∈ H.edgeSet :=
    B'.toPathPacking.edgeSet_subset_edgeSet heB'ab
  have hab : H.Adj a b := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using hedge
  rcases M.edge_mem_red_or_blue hab with hred | hblue
  · exact False.elim
      (M.false_of_red_edge_and_blueRouting hdeg hdisj B' hred heB'ab)
  · simpa [heout] using hblue

/-- The selected red routing is unique up to edge set. -/
theorem redRouting_edgeSet_eq_selected
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (R' : PerfectPathPacking H
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))) :
    R'.toPathPacking.edgeSet = M.good.redRouting.toPathPacking.edgeSet := by
  classical
  ext e
  constructor
  · intro he
    exact M.redRouting_edgeSet_subset_selected hdeg hdisj R' he
  · intro he
    exact M.red_edge_mem_of_any_redRouting hdeg hdisj R' he

/-- The selected blue routing is unique up to edge set. -/
theorem blueRouting_edgeSet_eq_selected
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (B' : PerfectPathPacking H
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))) :
    B'.toPathPacking.edgeSet = M.good.blueRouting.toPathPacking.edgeSet := by
  classical
  ext e
  constructor
  · intro he
    exact M.blueRouting_edgeSet_subset_selected hdeg hdisj B' he
  · intro he
    exact M.blue_edge_mem_of_any_blueRouting hdeg hdisj B' he

end TwoPairMinimalGoodMinor

/-! ## Existence of minimal good minors -/

/-- A finite good-minor witness, packaged so we can minimize over the vertex
type and graph without exposing the intermediate type in the theorem
statement. -/
structure TwoPairGoodMinorPackage
    (G : _root_.SimpleGraph V)
    (S₁ T₁ S₂ T₂ : Finset V) where
  W : Type u
  instFintype : Fintype W
  instDecidableEq : DecidableEq W
  H : _root_.SimpleGraph W
  good :
    letI : DecidableEq W := instDecidableEq
    TwoPairGoodMinor G H S₁ T₁ S₂ T₂

namespace TwoPairGoodMinorPackage

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- Package an already constructed finite good minor. -/
noncomputable def ofGood
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    TwoPairGoodMinorPackage G S₁ T₁ S₂ T₂ where
  W := W
  instFintype := inferInstance
  instDecidableEq := inferInstance
  H := H
  good := N

/-- Number of vertices of the packaged minor. -/
noncomputable def vertexCount
    (P : TwoPairGoodMinorPackage G S₁ T₁ S₂ T₂) : ℕ := by
  letI : Fintype P.W := P.instFintype
  exact Fintype.card P.W

/-- Number of edges of the packaged minor. -/
noncomputable def edgeCount
    (P : TwoPairGoodMinorPackage G S₁ T₁ S₂ T₂) : ℕ := by
  exact P.H.edgeSet.ncard

end TwoPairGoodMinorPackage

/-- From any finite good minor, choose one that is minimal under edge deletion
and nonterminal edge contraction.  The construction first minimizes the number
of minor vertices and then, among those, the number of minor edges. -/
theorem exists_minimalGoodMinor_of_good
    {W : Type u} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V}
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) :
    ∃ (W' : Type u), ∃ (_ : Fintype W'), ∃ (_ : DecidableEq W'),
      ∃ H' : _root_.SimpleGraph W',
        Nonempty (TwoPairMinimalGoodMinor G H' S₁ T₁ S₂ T₂) := by
  classical
  let Package := TwoPairGoodMinorPackage G S₁ T₁ S₂ T₂
  let HasVertexCount : ℕ → Prop := fun n =>
    ∃ P : Package, P.vertexCount = n
  have hVertexExists : ∃ n : ℕ, HasVertexCount n := by
    let P₀ : Package := TwoPairGoodMinorPackage.ofGood N
    exact ⟨P₀.vertexCount, P₀, rfl⟩
  let vertexMin := Nat.find hVertexExists
  rcases Nat.find_spec hVertexExists with ⟨P₁, hP₁vertex⟩
  let HasEdgeCount : ℕ → Prop := fun m =>
    ∃ P : Package, P.vertexCount = vertexMin ∧ P.edgeCount = m
  have hEdgeExists : ∃ m : ℕ, HasEdgeCount m := by
    exact ⟨P₁.edgeCount, P₁, hP₁vertex, rfl⟩
  let edgeMin := Nat.find hEdgeExists
  rcases Nat.find_spec hEdgeExists with
    ⟨Pmin, hPminVertex, hPminEdge⟩
  letI : Fintype Pmin.W := Pmin.instFintype
  letI : DecidableEq Pmin.W := Pmin.instDecidableEq
  refine ⟨Pmin.W, Pmin.instFintype, Pmin.instDecidableEq, Pmin.H, ?_⟩
  refine ⟨?_⟩
  refine
    { good := Pmin.good
      edgeDeletion_not_good := ?_
      edgeContraction_not_good := ?_ }
  · intro a b hab hgoodDeleted
    rcases hgoodDeleted with ⟨Ndel⟩
    let Pdel : Package := {
      W := Pmin.W
      instFintype := Pmin.instFintype
      instDecidableEq := Pmin.instDecidableEq
      H := Pmin.H.deleteEdges ({s(a, b)} : Set (Sym2 Pmin.W))
      good := Ndel }
    have hPdelVertex : Pdel.vertexCount = vertexMin := by
      simpa [Pdel, TwoPairGoodMinorPackage.vertexCount] using hPminVertex
    have hPdelCandidate : HasEdgeCount Pdel.edgeCount :=
      ⟨Pdel, hPdelVertex, rfl⟩
    have hMinLe : edgeMin ≤ Pdel.edgeCount :=
      Nat.find_min' (H := hEdgeExists) hPdelCandidate
    have hDelLt : Pdel.edgeCount < Pmin.edgeCount := by
      simpa [Pdel, TwoPairGoodMinorPackage.edgeCount] using
        edgeSet_deleteEdges_singleton_ncard_lt Pmin.H hab
    omega
  · intro a b hab havoid hgoodContract
    rcases hgoodContract with ⟨Ncon⟩
    let Pcon : Package := {
      W := EdgeContractVertex Pmin.W a b
      instFintype := inferInstance
      instDecidableEq := inferInstance
      H := contractEdgeGraph Pmin.H hab
      good := Ncon }
    have hPconCandidate : HasVertexCount Pcon.vertexCount :=
      ⟨Pcon, rfl⟩
    have hMinLe : vertexMin ≤ Pcon.vertexCount :=
      Nat.find_min' (H := hVertexExists) hPconCandidate
    have hConLt : Pcon.vertexCount < Pmin.vertexCount := by
      simpa [Pcon, TwoPairGoodMinorPackage.vertexCount] using
        EdgeContractVertex.card_lt_of_ne
          (V := Pmin.W) (u := a) (v := b) hab.ne
    omega

/-- Routability in the original graph supplies a finite minimal good minor
via the identity good minor followed by finite minimization. -/
theorem exists_minimalGoodMinor_of_routable
    [Fintype V] {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (h₁ : RoutableIn G S₁ T₁)
    (h₂ : RoutableIn G S₂ T₂) :
    ∃ (W' : Type u), ∃ (_ : Fintype W'), ∃ (_ : DecidableEq W'),
      ∃ H' : _root_.SimpleGraph W',
        Nonempty (TwoPairMinimalGoodMinor G H' S₁ T₁ S₂ T₂) := by
  rcases h₁ with ⟨P⟩
  rcases h₂ with ⟨Q⟩
  exact exists_minimalGoodMinor_of_good (TwoPairGoodMinor.ofRoutings P Q)

end TreewidthSparsifier

/-! ## Edge-unique linkage cycles -/

namespace PathSlicing

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B : Finset V}

/-- The dependency-cycle rerouting contradiction only needs edge-set
uniqueness.  The stronger repository predicate `IsUniqueLinkage` also includes
a spanning condition used for separator orderings, but Section 2's red/blue
cycle exclusion needs only this edge-set part. -/
theorem linkageDependencyCycle_false_of_edgeSet_unique
    {R : PerfectPathPacking G A B}
    (C : LinkageDependencyCycle R)
    (hunique :
      ∀ R' : PerfectPathPacking G A B,
        R'.toPathPacking.edgeSet = R.toPathPacking.edgeSet) :
    False := by
  classical
  let i0 : C.Index := Classical.choice inferInstance
  let R' : PerfectPathPacking G A B := C.reroutedPerfectPathPacking
  have hR'edge :
      s(C.vertex i0, C.witness (C.pred i0)) ∈ R'.toPathPacking.edgeSet := by
    simpa [R'] using C.reroutedPerfectPathPacking_cross_edge_mem i0
  have hEq := hunique R'
  have hRedge :
      s(C.vertex i0, C.witness (C.pred i0)) ∈ R.toPathPacking.edgeSet := by
    simpa [hEq] using hR'edge
  exact C.cross_edge_not_mem_original i0 hRedge

/-- Appendix B's dependency relation is acyclic under edge-set uniqueness.

This is the same proof as `linkageDependency_acyclic_of_unique`, but the final
rerouting contradiction uses only equality of edge sets for every alternate
perfect linkage. -/
theorem linkageDependency_acyclic_of_edgeSet_unique
    [Fintype V]
    {R : PerfectPathPacking G A B}
    (hunique :
      ∀ R' : PerfectPathPacking G A B,
        R'.toPathPacking.edgeSet = R.toPathPacking.edgeSet) :
    ∀ v : V, ¬ Relation.TransGen (LinkageDependency R) v v := by
  classical
  intro v hvv
  have hex :
      ∃ p : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) p :=
    RelationSeries.exists_closed_of_transGen_cycle
      (rel := LinkageDependency R) hvv
  let p :=
    RelationSeries.minimalClosedSeries
      (rel := LinkageDependency R) hex
  have hpclosed :
      RelationSeries.Closed (rel := LinkageDependency R) p := by
    simpa [p] using
      RelationSeries.minimalClosedSeries_closed
        (rel := LinkageDependency R) hex
  have hmin :
      ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) q →
          p.length ≤ q.length := by
    intro q hq
    simpa [p] using
      RelationSeries.minimalClosedSeries_min
        (rel := LinkageDependency R) hex hq
  have hnotype1 :=
    closed_dependency_series_no_type1_edge_of_minimal
      (R := R) p hpclosed hmin
  haveI : NeZero p.length := ⟨Nat.pos_iff_ne_zero.mp hpclosed.2⟩
  let next : Equiv.Perm (Fin p.length) :=
    Equiv.addRight (1 : Fin p.length)
  let vertex : Fin p.length → V := fun i => p i.castSucc
  have hvertex_next : ∀ i : Fin p.length, vertex (next i) = p i.succ := by
    intro i
    by_cases hi : i.1 + 1 < p.length
    · have hnext : next i = ⟨i.1 + 1, hi⟩ := by
        simpa [next] using fin_addRight_one_apply_of_lt i hi
      simp [vertex, hnext]
      apply congrArg p.toFun
      ext
      simp [Fin.val_succ]
    · have hnext : next i = 0 := by
        simpa [next] using fin_addRight_one_apply_of_not_lt i hi
      have hisucc : i.succ = (Fin.last p.length) := by
        ext
        simp [Fin.val_succ]
        omega
      calc
        vertex (next i) = p.head := by simp [vertex, hnext, RelSeries.head]
        _ = p.last := hpclosed.1
        _ = p i.succ := by simp [RelSeries.last, hisucc]
  let Dp : ∀ i : Fin p.length,
      Type2DependencyData R (p i.castSucc) (p i.succ) := fun i =>
    Classical.choice
      (Type2DependencyData.exists_of_dependency_of_not_type1
        (R := R)
        (u := p i.castSucc) (v := p i.succ)
        (by simpa [relationSetRel] using p.step i)
        (hnotype1 i))
  have hrowinjp :
      Function.Injective fun i : Fin p.length => (Dp i).row :=
    closed_dependency_series_type2_rows_injective_of_minimal
      (R := R) p hpclosed hmin Dp
  let D : ∀ i : Fin p.length,
      Type2DependencyData R (vertex i) (vertex (next i)) := fun i =>
    { row := (Dp i).row
      row' := (Dp i).row'
      row_ne := (Dp i).row_ne
      u_mem := by simpa [vertex] using (Dp i).u_mem
      v_mem := by simpa [hvertex_next i] using (Dp i).v_mem
      witness := (Dp i).witness
      witness_mem := (Dp i).witness_mem
      before_witness := by simpa [vertex] using (Dp i).before_witness
      u_ne_witness := by simpa [vertex] using (Dp i).u_ne_witness
      adj := by simpa [hvertex_next i] using (Dp i).adj }
  have hrowinj : Function.Injective fun i : Fin p.length => (D i).row := by
    intro i j hij
    apply hrowinjp
    simpa [D] using hij
  let C : LinkageDependencyCycle R :=
    LinkageDependencyCycle.ofType2Family
      (R := R) next vertex D hrowinj
  exact linkageDependencyCycle_false_of_edgeSet_unique C hunique

/-- Edge-set uniqueness forbids a shortcut edge that jumps over a nonempty
segment of one linkage row. -/
theorem false_of_shortcut_edge_of_edgeSet_unique
    {R : PerfectPathPacking G A B}
    (hunique :
      ∀ R' : PerfectPathPacking G A B,
        R'.toPathPacking.edgeSet = R.toPathPacking.edgeSet)
    {r : R.Index} {u x v : V}
    (hux : (R.path r).Before u x)
    (hxv : (R.path r).Before x v)
    (hux_ne : u ≠ x) (hxv_ne : x ≠ v)
    (huv : G.Adj u v) :
    False := by
  classical
  have hu : u ∈ (R.path r).vertexSet :=
    ((R.path r).before_iff_vertexIndex_le).1 hux |>.1
  have hshortcutNotRow :
      s(u, v) ∉ (R.path r).edgeSet :=
    TopologicalRank.shortcut_edge_not_mem_row
      (R.path r) hux hxv hux_ne hxv_ne
  have hshortcutNotR :
      s(u, v) ∉ R.toPathPacking.edgeSet := by
    intro he
    rcases (R.toPathPacking.mem_edgeSet).1 he with ⟨i, hei⟩
    by_cases hir : i = r
    · subst i
      exact hshortcutNotRow hei
    · have heWalk : s(u, v) ∈ (R.path i).walk.edges := by
        exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using hei)
      have hu_i : u ∈ (R.path i).vertexSet := by
        have huSupport : u ∈ (R.path i).walk.support :=
          (R.path i).walk.fst_mem_support_of_mem_edges heWalk
        simpa [GraphPath.vertexSet] using huSupport
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hir)
        hu_i hu
  rcases GraphPath.exists_shortcutAround
      (R.path r) hux hxv hux_ne huv with
    ⟨Q, hQsource, hQtarget, hQsubset, hQedge⟩
  let newPath : R.Index → GraphPath G := fun i =>
    if i = r then Q else R.path i
  have newPath_source_mem : ∀ i : R.Index, (newPath i).source ∈ A := by
    intro i
    by_cases hir : i = r
    · subst i
      simpa [newPath, hQsource] using R.source_mem r
    · simpa [newPath, hir] using R.source_mem i
  have newPath_target_mem : ∀ i : R.Index, (newPath i).target ∈ B := by
    intro i
    by_cases hir : i = r
    · subst i
      simpa [newPath, hQtarget] using R.target_mem r
    · simpa [newPath, hir] using R.target_mem i
  let R' : PerfectPathPacking G A B := {
    toPathPacking := {
      Index := R.Index
      path := newPath
      connects := by
        intro i
        exact Or.inl ⟨newPath_source_mem i, newPath_target_mem i⟩
      node_disjoint := by
        intro i j hij
        by_cases hir : i = r
        · by_cases hjr : j = r
          · exact False.elim (hij (hir.trans hjr.symm))
          · subst i
            dsimp [newPath]
            rw [if_pos rfl, if_neg hjr]
            exact Finset.disjoint_of_subset_left hQsubset
              (R.toPathPacking.node_disjoint (by
                intro hrj
                exact hjr hrj.symm))
        · by_cases hjr : j = r
          · subst j
            dsimp [newPath]
            rw [if_neg hir, if_pos rfl]
            exact Finset.disjoint_of_subset_right hQsubset
              (R.toPathPacking.node_disjoint (by
                intro hir'
                exact hir hir'))
          · dsimp [newPath]
            rw [if_neg hir, if_neg hjr]
            exact R.toPathPacking.node_disjoint hij
    }
    source_mem := newPath_source_mem
    target_mem := newPath_target_mem
    source_bijective := by
      have hfun :
          (fun i : R.Index =>
            (⟨(newPath i).source, newPath_source_mem i⟩ : {w // w ∈ A})) =
          (fun i : R.Index =>
            (⟨(R.path i).source, R.source_mem i⟩ : {w // w ∈ A})) := by
        funext i
        apply Subtype.ext
        by_cases hir : i = r
        · subst i
          simp [newPath, hQsource]
        · simp [newPath, hir]
      simpa [hfun] using R.source_bijective
    target_bijective := by
      have hfun :
          (fun i : R.Index =>
            (⟨(newPath i).target, newPath_target_mem i⟩ : {w // w ∈ B})) =
          (fun i : R.Index =>
            (⟨(R.path i).target, R.target_mem i⟩ : {w // w ∈ B})) := by
        funext i
        apply Subtype.ext
        by_cases hir : i = r
        · subst i
          simp [newPath, hQtarget]
        · simp [newPath, hir]
      simpa [hfun] using R.target_bijective
  }
  have hR'edge : s(u, v) ∈ R'.toPathPacking.edgeSet := by
    apply (R'.toPathPacking.mem_edgeSet).2
    refine ⟨r, ?_⟩
    simpa [R', newPath] using hQedge
  have hEq := hunique R'
  have hRedge : s(u, v) ∈ R.toPathPacking.edgeSet := by
    simpa [hEq] using hR'edge
  exact hshortcutNotR hRedge

/-- A dependency edge whose endpoints lie on the same linkage row follows the
row order.  Type-2 dependency edges necessarily move between distinct rows, so
they are impossible under the two same-row membership hypotheses. -/
theorem linkageDependency_before_of_same_row
    {R : PerfectPathPacking G A B} {u v : V} {r : R.Index}
    (huv : LinkageDependency R u v)
    (hu : u ∈ (R.path r).vertexSet)
    (hv : v ∈ (R.path r).vertexSet) :
    (R.path r).Before u v := by
  classical
  rcases huv with htype1 | htype2
  · rcases htype1 with ⟨r', hu', _hv', hbefore, _hne⟩
    have hrr' : r' = r := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
        hu' hu
    subst r'
    exact hbefore
  · rcases htype2 with
      ⟨r₁, r₂, hr₁r₂, hu₁, hv₂, _w, _hw, _hbefore, _hne, _hadj⟩
    have hr₁ : r₁ = r := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
        hu₁ hu
    have hr₂ : r₂ = r := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
        hv₂ hv
    exact False.elim (hr₁r₂ (hr₁.trans hr₂.symm))

end PathSlicing

namespace TreewidthSparsifier

variable {V : Type u} [DecidableEq V]

namespace TwoPairMinimalGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

/-- A dependency cycle for the selected red routing contradicts the red
edge-set uniqueness proved from minimality. -/
theorem red_linkageDependencyCycle_false
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (C : Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependencyCycle
      M.good.redRouting) :
    False :=
  PathSlicing.linkageDependencyCycle_false_of_edgeSet_unique C
    (fun R' => M.redRouting_edgeSet_eq_selected hdeg hdisj R')

/-- The selected red routing has an acyclic dependency relation, using only
edge-set uniqueness from minimality. -/
theorem red_linkageDependency_acyclic
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    ∀ v : W,
      ¬ Relation.TransGen
        (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
          M.good.redRouting) v v :=
  PathSlicing.linkageDependency_acyclic_of_edgeSet_unique
    (fun R' => M.redRouting_edgeSet_eq_selected hdeg hdisj R')

/-- A dependency-topological rank for the selected red routing. -/
noncomputable def redDependencyRank
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    Lax17Proofs.SimpleGraph.PathSlicing.TopologicalRank
      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
        M.good.redRouting) :=
  PathSlicing.topologicalRankOfAcyclicRelation
    (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
      M.good.redRouting)
    (M.red_linkageDependency_acyclic hdeg hdisj)

/-- A dependency cycle for the selected blue routing contradicts the blue
edge-set uniqueness proved from minimality. -/
theorem blue_linkageDependencyCycle_false
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (C : Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependencyCycle
      M.good.blueRouting) :
    False :=
  PathSlicing.linkageDependencyCycle_false_of_edgeSet_unique C
    (fun B' => M.blueRouting_edgeSet_eq_selected hdeg hdisj B')

/-- The selected blue routing has an acyclic dependency relation, using only
edge-set uniqueness from minimality. -/
theorem blue_linkageDependency_acyclic
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    ∀ v : W,
      ¬ Relation.TransGen
        (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
          M.good.blueRouting) v v :=
  PathSlicing.linkageDependency_acyclic_of_edgeSet_unique
    (fun B' => M.blueRouting_edgeSet_eq_selected hdeg hdisj B')

/-- A dependency-topological rank for the selected blue routing. -/
noncomputable def blueDependencyRank
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    Lax17Proofs.SimpleGraph.PathSlicing.TopologicalRank
      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
        M.good.blueRouting) :=
  PathSlicing.topologicalRankOfAcyclicRelation
    (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
      M.good.blueRouting)
    (M.blue_linkageDependency_acyclic hdeg hdisj)

end TwoPairMinimalGoodMinor

variable [Fintype V]

/-- Theorem 2.2's order-labeling conclusion for the original red orientation.

The constructive chain proof still has to provide this object.  Once it does,
the downstream counting arguments in this file no longer need to know how the
labels were built. -/
structure TwoPairForwardLabeling
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- The label assigned to each vertex. -/
  label : V → Fin (2 * k)
  /-- Equal labels force agreement of red and blue order. -/
  same_label_order :
    ∀ ⦃x y : V⦄ (i : P.Index) (j : Q.Index),
      x ∈ (P.path i).vertexSet →
        y ∈ (P.path i).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              label x = label y →
                (P.path i).Before x y →
                  (Q.path j).Before x y

/-- Theorem 2.2 applied after reversing the red paths, restated in the
original red orientation.

If `x` precedes `y` on an original red path, then after red reversal `y`
precedes `x`; agreement with the blue order in the reversed instance therefore
becomes the blue-order reversal recorded here. -/
structure TwoPairReverseRedLabeling
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- The label assigned to each vertex in the reversed-red instance. -/
  label : V → Fin (2 * k)
  /-- Equal reversed-red labels force disagreement of original red and blue
  order. -/
  same_reverseLabel_order :
    ∀ ⦃x y : V⦄ (i : P.Index) (j : Q.Index),
      x ∈ (P.path i).vertexSet →
        y ∈ (P.path i).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              label x = label y →
                (P.path i).Before x y →
                  (Q.path j).Before y x

namespace TwoPairForwardLabeling

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- Forward labels for the instance with red paths reversed are exactly the
reverse-red labels needed for the original orientation. -/
noncomputable def toReverseRedLabelingOfReverse
    (L : TwoPairForwardLabeling P.reverse Q k) :
    TwoPairReverseRedLabeling P Q k where
  label := L.label
  same_reverseLabel_order := by
    intro x y i j hxR hyR hxB hyB hlabel hxyR
    have hyRev : y ∈ ((P.reverse).path i).vertexSet := by
      simpa using hyR
    have hxRev : x ∈ ((P.reverse).path i).vertexSet := by
      simpa using hxR
    have hyxRev : ((P.reverse).path i).Before y x := by
      simpa [PerfectPathPacking.reverse] using
        GraphPath.reverse_before_of_before (P.path i) hxyR
    exact L.same_label_order i j hyRev hxRev hyB hxB hlabel.symm hyxRev

end TwoPairForwardLabeling

/-- The minimal-core incidence fact that each high-degree union vertex lies on
a selected red path and a selected blue path. -/
structure TwoPairBranchCarrier
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) where
  /-- The red path containing a high-degree union vertex. -/
  redIndex :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → P.Index
  /-- The blue path containing a high-degree union vertex. -/
  blueIndex :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Q.Index
  /-- Membership in the selected red path. -/
  red_mem :
    ∀ ⦃v : V⦄ (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      v ∈ (P.path (redIndex v hv)).vertexSet
  /-- Membership in the selected blue path. -/
  blue_mem :
    ∀ ⦃v : V⦄ (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      v ∈ (Q.path (blueIndex v hv)).vertexSet

namespace TwoPairBranchCarrier

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}

/-- A high-degree vertex of the union must lie on a red path. -/
theorem red_vertexSet_mem_of_branchVertex
    {v : V}
    (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)) :
    v ∈ P.toPathPacking.vertexSet := by
  classical
  have hnot :
      ¬ DegreeAtMost (twoPackingUnionGraph P Q) v 2 :=
    (Finset.mem_filter.mp hv).2
  by_contra hvP
  exact hnot (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_red P Q hvP)

/-- A high-degree vertex of the union must lie on a blue path. -/
theorem blue_vertexSet_mem_of_branchVertex
    {v : V}
    (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)) :
    v ∈ Q.toPathPacking.vertexSet := by
  classical
  have hnot :
      ¬ DegreeAtMost (twoPackingUnionGraph P Q) v 2 :=
    (Finset.mem_filter.mp hv).2
  by_contra hvQ
  exact hnot (twoPackingUnionGraph_degreeAtMost_two_of_not_mem_blue P Q hvQ)

/-- Construct the branch-carrier data needed in the counting proof directly
from the two routings. -/
noncomputable def ofPackings
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) :
    TwoPairBranchCarrier P Q where
  redIndex := fun v hv =>
    Classical.choose
      ((P.toPathPacking.mem_vertexSet).1
        (red_vertexSet_mem_of_branchVertex (P := P) (Q := Q) hv))
  blueIndex := fun v hv =>
    Classical.choose
      ((Q.toPathPacking.mem_vertexSet).1
        (blue_vertexSet_mem_of_branchVertex (P := P) (Q := Q) hv))
  red_mem := by
    intro v hv
    exact Classical.choose_spec
      ((P.toPathPacking.mem_vertexSet).1
        (red_vertexSet_mem_of_branchVertex (P := P) (Q := Q) hv))
  blue_mem := by
    intro v hv
    exact Classical.choose_spec
      ((Q.toPathPacking.mem_vertexSet).1
        (blue_vertexSet_mem_of_branchVertex (P := P) (Q := Q) hv))

end TwoPairBranchCarrier

/-! ## Finite minimizers for two routings -/

/-- The objective used when choosing a sparse pair of routings directly in a
fixed graph: the number of high-degree vertices in the union of the two
packings. -/
noncomputable def twoPairRoutingBranchCount
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) : ℕ :=
  branchVertexCount (twoPackingUnionGraph P Q)

/-- A pair of routings with minimum high-degree-vertex count among all
routings of the same two terminal pairs. -/
def IsMinimumTwoPairRoutingBranchCount
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) : Prop :=
  ∀ (P' : PerfectPathPacking G S₁ T₁)
    (Q' : PerfectPathPacking G S₂ T₂),
      twoPairRoutingBranchCount P Q ≤ twoPairRoutingBranchCount P' Q'

/-- Among two nonempty routing families, a pair minimizing the number of
high-degree vertices in the union exists. -/
theorem exists_minimumTwoPairRoutingBranchCount
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₀ : PerfectPathPacking G S₁ T₁)
    (Q₀ : PerfectPathPacking G S₂ T₂) :
    ∃ (P : PerfectPathPacking G S₁ T₁)
      (Q : PerfectPathPacking G S₂ T₂),
        IsMinimumTwoPairRoutingBranchCount P Q := by
  classical
  let HasCount : ℕ → Prop := fun n =>
    ∃ (P : PerfectPathPacking G S₁ T₁)
      (Q : PerfectPathPacking G S₂ T₂),
        twoPairRoutingBranchCount P Q = n
  have hExists : ∃ n : ℕ, HasCount n :=
    ⟨twoPairRoutingBranchCount P₀ Q₀, P₀, Q₀, rfl⟩
  rcases Nat.find_spec hExists with ⟨P, Q, hPQ⟩
  refine ⟨P, Q, ?_⟩
  intro P' Q'
  have hP' : HasCount (twoPairRoutingBranchCount P' Q') := ⟨P', Q', rfl⟩
  have hmin : Nat.find hExists ≤ twoPairRoutingBranchCount P' Q' :=
    Nat.find_min' (H := hExists) hP'
  simpa [hPQ] using hmin

/-- Routability hypotheses provide a minimum-`τ` pair of routings. -/
theorem exists_minimumTwoPairRoutingBranchCount_of_routable
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (h₁ : RoutableIn G S₁ T₁)
    (h₂ : RoutableIn G S₂ T₂) :
    ∃ (P : PerfectPathPacking G S₁ T₁)
      (Q : PerfectPathPacking G S₂ T₂),
        IsMinimumTwoPairRoutingBranchCount P Q := by
  rcases h₁ with ⟨P₀⟩
  rcases h₂ with ⟨Q₀⟩
  exact exists_minimumTwoPairRoutingBranchCount P₀ Q₀

/-! ## Directed red/blue edges for the chain construction -/

/-- The two colors used by the Section 2 alternating-chain construction. -/
inductive TwoPairColor where
  | red
  | blue
deriving DecidableEq, Fintype

namespace TwoPairColor

/-- Switch to the other color in an alternating red/blue chain. -/
def swap : TwoPairColor → TwoPairColor
  | red => blue
  | blue => red

@[simp] theorem swap_red : swap red = blue := rfl
@[simp] theorem swap_blue : swap blue = red := rfl
@[simp] theorem swap_swap (c : TwoPairColor) : swap (swap c) = c := by
  cases c <;> rfl

end TwoPairColor

/-- A directed red or blue edge, oriented according to the corresponding
routing path.  The underlying graph remains undirected; the direction is the
order along the selected path packing. -/
def TwoPairColorEdge
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (c : TwoPairColor) (u v : V) : Prop :=
  match c with
  | TwoPairColor.red =>
      ∃ i : P.Index,
        s(u, v) ∈ (P.path i).edgeSet ∧
          (P.path i).Before u v ∧ u ≠ v
  | TwoPairColor.blue =>
      ∃ j : Q.Index,
        s(u, v) ∈ (Q.path j).edgeSet ∧
          (Q.path j).Before u v ∧ u ≠ v

namespace TwoPairColorEdge

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}

omit [Fintype V] in
/-- A red directed edge is an edge of the union graph. -/
theorem red_adj_union {u v : V}
    (h : TwoPairColorEdge P Q TwoPairColor.red u v) :
    (twoPackingUnionGraph P Q).Adj u v := by
  rcases h with ⟨i, he, _hbefore, hne⟩
  have hred :
      P.toPathPacking.spanningGraph.Adj u v :=
    (P.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
      ⟨⟨i, he⟩, hne⟩
  simpa [twoPackingUnionGraph] using Or.inl hred

omit [Fintype V] in
/-- A blue directed edge is an edge of the union graph. -/
theorem blue_adj_union {u v : V}
    (h : TwoPairColorEdge P Q TwoPairColor.blue u v) :
    (twoPackingUnionGraph P Q).Adj u v := by
  rcases h with ⟨j, he, _hbefore, hne⟩
  have hblue :
      Q.toPathPacking.spanningGraph.Adj u v :=
    (Q.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
      ⟨⟨j, he⟩, hne⟩
  simpa [twoPackingUnionGraph] using Or.inr hblue

omit [Fintype V] in
/-- Every directed color edge is an edge of the red/blue union graph. -/
theorem adj_union {c : TwoPairColor} {u v : V}
    (h : TwoPairColorEdge P Q c u v) :
    (twoPackingUnionGraph P Q).Adj u v := by
  cases c with
  | red => exact red_adj_union (P := P) (Q := Q) h
  | blue => exact blue_adj_union (P := P) (Q := Q) h

omit [Fintype V] in
/-- A path edge has one of the two path-order orientations. -/
theorem red_or_reverse_of_mem_red_edge {u v : V} {i : P.Index}
    (he : s(u, v) ∈ (P.path i).edgeSet) :
    TwoPairColorEdge P Q TwoPairColor.red u v ∨
      TwoPairColorEdge P Q TwoPairColor.red v u := by
  classical
  have hu : u ∈ (P.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) he).1
  have hv : v ∈ (P.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) he).2
  have hne : u ≠ v := by
    have hadj : G.Adj u v := by
      simpa using GraphPath.edgeSet_subset_edgeSet (P.path i) he
    exact hadj.ne
  rcases GraphPath.before_total_of_mem (P.path i) hu hv with huv | hvu
  · exact Or.inl ⟨i, he, huv, hne⟩
  · exact Or.inr ⟨i, by simpa [Sym2.eq_swap] using he, hvu, hne.symm⟩

omit [Fintype V] in
/-- Blue analogue of `red_or_reverse_of_mem_red_edge`. -/
theorem blue_or_reverse_of_mem_blue_edge {u v : V} {j : Q.Index}
    (he : s(u, v) ∈ (Q.path j).edgeSet) :
    TwoPairColorEdge P Q TwoPairColor.blue u v ∨
      TwoPairColorEdge P Q TwoPairColor.blue v u := by
  classical
  have hu : u ∈ (Q.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j) he).1
  have hv : v ∈ (Q.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j) he).2
  have hne : u ≠ v := by
    have hadj : G.Adj u v := by
      simpa using GraphPath.edgeSet_subset_edgeSet (Q.path j) he
    exact hadj.ne
  rcases GraphPath.before_total_of_mem (Q.path j) hu hv with huv | hvu
  · exact Or.inl ⟨j, he, huv, hne⟩
  · exact Or.inr ⟨j, by simpa [Sym2.eq_swap] using he, hvu, hne.symm⟩

omit [Fintype V] in
/-- The forward red successor of a vertex, when it exists, is unique. -/
theorem red_unique {u v w : V}
    (huv : TwoPairColorEdge P Q TwoPairColor.red u v)
    (huw : TwoPairColorEdge P Q TwoPairColor.red u w) :
    v = w := by
  classical
  rcases huv with ⟨i, huvEdge, huvBefore, huv_ne⟩
  rcases huw with ⟨i', huwEdge, huwBefore, huw_ne⟩
  have hu_i : u ∈ (P.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) huvEdge).1
  have hu_i' : u ∈ (P.path i').vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i') huwEdge).1
  have hii' : i = i' := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hne)
      hu_i hu_i'
  subst i'
  exact GraphPath.forward_edge_unique (P.path i)
    huvEdge huvBefore huv_ne huwEdge huwBefore huw_ne

omit [Fintype V] in
/-- The forward blue successor of a vertex, when it exists, is unique. -/
theorem blue_unique {u v w : V}
    (huv : TwoPairColorEdge P Q TwoPairColor.blue u v)
    (huw : TwoPairColorEdge P Q TwoPairColor.blue u w) :
    v = w := by
  classical
  rcases huv with ⟨j, huvEdge, huvBefore, huv_ne⟩
  rcases huw with ⟨j', huwEdge, huwBefore, huw_ne⟩
  have hu_j : u ∈ (Q.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j) huvEdge).1
  have hu_j' : u ∈ (Q.path j').vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j') huwEdge).1
  have hjj' : j = j' := by
    by_contra hne
    exact Finset.disjoint_left.mp (Q.toPathPacking.node_disjoint hne)
      hu_j hu_j'
  subst j'
  exact GraphPath.forward_edge_unique (Q.path j)
    huvEdge huvBefore huv_ne huwEdge huwBefore huw_ne

omit [Fintype V] in
/-- The incoming predecessor of a vertex along red directed edges is unique
when it exists. -/
theorem red_left_unique {u v w : V}
    (huv : TwoPairColorEdge P Q TwoPairColor.red u v)
    (hwv : TwoPairColorEdge P Q TwoPairColor.red w v) :
    u = w := by
  classical
  rcases huv with ⟨i, huvEdge, huvBefore, huv_ne⟩
  rcases hwv with ⟨i', hwvEdge, hwvBefore, hwv_ne⟩
  have hv_i : v ∈ (P.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) huvEdge).2
  have hv_i' : v ∈ (P.path i').vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i') hwvEdge).2
  have hii' : i = i' := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hne)
      hv_i hv_i'
  subst i'
  exact GraphPath.backward_edge_unique (P.path i)
    huvEdge huvBefore huv_ne hwvEdge hwvBefore hwv_ne

omit [Fintype V] in
/-- The incoming predecessor of a vertex along blue directed edges is unique
when it exists. -/
theorem blue_left_unique {u v w : V}
    (huv : TwoPairColorEdge P Q TwoPairColor.blue u v)
    (hwv : TwoPairColorEdge P Q TwoPairColor.blue w v) :
    u = w := by
  classical
  rcases huv with ⟨j, huvEdge, huvBefore, huv_ne⟩
  rcases hwv with ⟨j', hwvEdge, hwvBefore, hwv_ne⟩
  have hv_j : v ∈ (Q.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j) huvEdge).2
  have hv_j' : v ∈ (Q.path j').vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j') hwvEdge).2
  have hjj' : j = j' := by
    by_contra hne
    exact Finset.disjoint_left.mp (Q.toPathPacking.node_disjoint hne)
      hv_j hv_j'
  subst j'
  exact GraphPath.backward_edge_unique (Q.path j)
    huvEdge huvBefore huv_ne hwvEdge hwvBefore hwv_ne

omit [Fintype V] in
/-- A non-target vertex on a red path has an outgoing red edge. -/
theorem exists_red_forward_of_mem_not_target
    {u : V} {i : P.Index}
    (hu : u ∈ (P.path i).vertexSet)
    (hu_target : u ≠ (P.path i).target) :
    ∃ v : V, TwoPairColorEdge P Q TwoPairColor.red u v := by
  rcases GraphPath.exists_forward_edge_of_mem_not_target
      (P.path i) hu hu_target with
    ⟨v, he, hbefore, hne⟩
  exact ⟨v, i, he, hbefore, hne⟩

omit [Fintype V] in
/-- A non-target vertex on a blue path has an outgoing blue edge. -/
theorem exists_blue_forward_of_mem_not_target
    {u : V} {j : Q.Index}
    (hu : u ∈ (Q.path j).vertexSet)
    (hu_target : u ≠ (Q.path j).target) :
    ∃ v : V, TwoPairColorEdge P Q TwoPairColor.blue u v := by
  rcases GraphPath.exists_forward_edge_of_mem_not_target
      (Q.path j) hu hu_target with
    ⟨v, he, hbefore, hne⟩
  exact ⟨v, j, he, hbefore, hne⟩

omit [Fintype V] in
/-- A non-source vertex on a red path has an incoming red edge. -/
theorem exists_red_backward_of_mem_not_source
    {u : V} {i : P.Index}
    (hu : u ∈ (P.path i).vertexSet)
    (hu_source : u ≠ (P.path i).source) :
    ∃ v : V, TwoPairColorEdge P Q TwoPairColor.red v u := by
  rcases GraphPath.exists_backward_edge_of_mem_not_source
      (P.path i) hu hu_source with
    ⟨v, he, hbefore, hne⟩
  exact ⟨v, i, he, hbefore, hne⟩

omit [Fintype V] in
/-- A non-source vertex on a blue path has an incoming blue edge. -/
theorem exists_blue_backward_of_mem_not_source
    {u : V} {j : Q.Index}
    (hu : u ∈ (Q.path j).vertexSet)
    (hu_source : u ≠ (Q.path j).source) :
    ∃ v : V, TwoPairColorEdge P Q TwoPairColor.blue v u := by
  rcases GraphPath.exists_backward_edge_of_mem_not_source
      (Q.path j) hu hu_source with
    ⟨v, he, hbefore, hne⟩
  exact ⟨v, j, he, hbefore, hne⟩

omit [Fintype V] in
/-- A red step followed by a blue step gives a red-linkage dependency when
the blue step lands on a different red row. -/
theorem red_then_blue_linkageDependency_of_target_red_row_ne
    {x y z : V} {i i' : P.Index}
    (hredEdge : s(x, y) ∈ (P.path i).edgeSet)
    (hredBefore : (P.path i).Before x y)
    (hxy_ne : x ≠ y)
    (hblue : TwoPairColorEdge P Q TwoPairColor.blue y z)
    (hzRed : z ∈ (P.path i').vertexSet)
    (hrow_ne : i ≠ i') :
    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency P x z := by
  classical
  have hxRed : x ∈ (P.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) hredEdge).1
  have hyRed : y ∈ (P.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) hredEdge).2
  have hyzAdj : G.Adj y z := by
    rcases hblue with ⟨j, hblueEdge, _hbefore, _hne⟩
    exact GraphPath.edgeSet_subset_edgeSet (Q.path j) hblueEdge
  exact Or.inr
    ⟨i, i', hrow_ne, hxRed, hzRed, y, hyRed,
      hredBefore, hxy_ne, hyzAdj⟩

omit [Fintype V] in
/-- A red step followed by a blue step gives a red-linkage dependency when
the blue step lands later on the same red row. -/
theorem red_then_blue_linkageDependency_of_target_red_after
    {x y z : V} {i : P.Index}
    (hredEdge : s(x, y) ∈ (P.path i).edgeSet)
    (_hredBefore : (P.path i).Before x y)
    (_hxy_ne : x ≠ y)
    (hzRed : z ∈ (P.path i).vertexSet)
    (hxzBefore : (P.path i).Before x z)
    (hxz_ne : x ≠ z) :
    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency P x z := by
  classical
  have hxRed : x ∈ (P.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) hredEdge).1
  exact Or.inl ⟨i, hxRed, hzRed, hxzBefore, hxz_ne⟩

omit [Fintype V] in
/-- A blue step followed by a red step gives a blue-linkage dependency when
the red step lands on a different blue row. -/
theorem blue_then_red_linkageDependency_of_target_blue_row_ne
    {x y z : V} {j j' : Q.Index}
    (hblueEdge : s(x, y) ∈ (Q.path j).edgeSet)
    (hblueBefore : (Q.path j).Before x y)
    (hxy_ne : x ≠ y)
    (hred : TwoPairColorEdge P Q TwoPairColor.red y z)
    (hzBlue : z ∈ (Q.path j').vertexSet)
    (hrow_ne : j ≠ j') :
    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency Q x z := by
  classical
  have hxBlue : x ∈ (Q.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j) hblueEdge).1
  have hyBlue : y ∈ (Q.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j) hblueEdge).2
  have hyzAdj : G.Adj y z := by
    rcases hred with ⟨i, hredEdge, _hbefore, _hne⟩
    exact GraphPath.edgeSet_subset_edgeSet (P.path i) hredEdge
  exact Or.inr
    ⟨j, j', hrow_ne, hxBlue, hzBlue, y, hyBlue,
      hblueBefore, hxy_ne, hyzAdj⟩

omit [Fintype V] in
/-- A blue step followed by a red step gives a blue-linkage dependency when
the red step lands later on the same blue row. -/
theorem blue_then_red_linkageDependency_of_target_blue_after
    {x y z : V} {j : Q.Index}
    (hblueEdge : s(x, y) ∈ (Q.path j).edgeSet)
    (_hblueBefore : (Q.path j).Before x y)
    (_hxy_ne : x ≠ y)
    (hzBlue : z ∈ (Q.path j).vertexSet)
    (hxzBefore : (Q.path j).Before x z)
    (hxz_ne : x ≠ z) :
    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency Q x z := by
  classical
  have hxBlue : x ∈ (Q.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j) hblueEdge).1
  exact Or.inl ⟨j, hxBlue, hzBlue, hxzBefore, hxz_ne⟩

end TwoPairColorEdge

/-- State space for the greedy alternating-chain construction.

The first coordinate is the current vertex and the second coordinate is the
color of the next edge to follow. -/
abbrev TwoPairAltState (V : Type u) := V × TwoPairColor

/-- One step of the directed alternating-chain walk: follow the state's next
color and then switch the next color. -/
def TwoPairAltStep
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) :
    TwoPairAltState V → TwoPairAltState V → Prop :=
  fun x y =>
    TwoPairColorEdge P Q x.2 x.1 y.1 ∧ y.2 = x.2.swap

namespace TwoPairAltStep

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}

omit [Fintype V] in
/-- The alternating-chain successor is unique when it exists. -/
theorem rightUnique :
    Relator.RightUnique (TwoPairAltStep P Q) := by
  intro x y z hxy hxz
  rcases x with ⟨u, c⟩
  rcases y with ⟨v, cy⟩
  rcases z with ⟨w, cz⟩
  rcases hxy with ⟨huv, hcy⟩
  rcases hxz with ⟨huw, hcz⟩
  cases c with
  | red =>
      have hvw :
          v = w :=
        TwoPairColorEdge.red_unique (P := P) (Q := Q) huv huw
      subst w
      have hcy' : cy = TwoPairColor.blue := by
        simpa using hcy
      have hcz' : cz = TwoPairColor.blue := by
        simpa using hcz
      subst cy
      subst cz
      rfl
  | blue =>
      have hvw :
          v = w :=
        TwoPairColorEdge.blue_unique (P := P) (Q := Q) huv huw
      subst w
      have hcy' : cy = TwoPairColor.red := by
        simpa using hcy
      have hcz' : cz = TwoPairColor.red := by
        simpa using hcz
      subst cy
      subst cz
      rfl

omit [Fintype V] in
/-- The alternating-chain predecessor is unique when it exists. -/
theorem leftUnique :
    Relator.LeftUnique (TwoPairAltStep P Q) := by
  intro x y z hxz hyz
  rcases x with ⟨u, cu⟩
  rcases y with ⟨v, cv⟩
  rcases z with ⟨w, cw⟩
  rcases hxz with ⟨huw, hcw⟩
  rcases hyz with ⟨hvw, hcw'⟩
  cases cw with
  | red =>
      have hcu : cu = TwoPairColor.blue := by
        cases cu <;> simp at hcw ⊢
      have hcv : cv = TwoPairColor.blue := by
        cases cv <;> simp at hcw' ⊢
      subst cu
      subst cv
      have huv :
          u = v :=
        TwoPairColorEdge.blue_left_unique (P := P) (Q := Q) huw hvw
      subst v
      rfl
  | blue =>
      have hcu : cu = TwoPairColor.red := by
        cases cu <;> simp at hcw ⊢
      have hcv : cv = TwoPairColor.red := by
        cases cv <;> simp at hcw' ⊢
      subst cu
      subst cv
      have huv :
          u = v :=
        TwoPairColorEdge.red_left_unique (P := P) (Q := Q) huw hvw
      subst v
      rfl

omit [Fintype V] in
/-- Any two states reached from the same alternating-chain start are comparable
along that deterministic chain. -/
theorem comparable_of_same_start
    {start x y : TwoPairAltState V}
    (hx : Relation.ReflTransGen (TwoPairAltStep P Q) start x)
    (hy : Relation.ReflTransGen (TwoPairAltStep P Q) start y) :
    Relation.ReflTransGen (TwoPairAltStep P Q) x y ∨
      Relation.ReflTransGen (TwoPairAltStep P Q) y x :=
  Relation.ReflTransGen.total_of_right_unique
    (rightUnique (P := P) (Q := Q)) hx hy

omit [Fintype V] in
/-- Dual comparability: any two states that can reach the same later state are
comparable along the deterministic alternating chain. -/
theorem comparable_of_same_end
    {finish x y : TwoPairAltState V}
    (hx : Relation.ReflTransGen (TwoPairAltStep P Q) x finish)
    (hy : Relation.ReflTransGen (TwoPairAltStep P Q) y finish) :
    Relation.ReflTransGen (TwoPairAltStep P Q) x y ∨
      Relation.ReflTransGen (TwoPairAltStep P Q) y x := by
  classical
  have hx' :
      Relation.ReflTransGen (flip (TwoPairAltStep P Q)) finish x :=
    Relation.ReflTransGen.swap hx
  have hy' :
      Relation.ReflTransGen (flip (TwoPairAltStep P Q)) finish y :=
    Relation.ReflTransGen.swap hy
  have hright :
      Relator.RightUnique (flip (TwoPairAltStep P Q)) :=
    (leftUnique (P := P) (Q := Q)).flip
  rcases Relation.ReflTransGen.total_of_right_unique hright hx' hy' with
    hxy | hyx
  · exact Or.inr (Relation.ReflTransGen.swap hxy)
  · exact Or.inl (Relation.ReflTransGen.swap hyx)

end TwoPairAltStep

omit [DecidableEq V] [Fintype V] in
/-- Embed any finite type of size at most `n` into `Fin n`. -/
noncomputable def fintypeEmbeddingFinOfCardLe
    (α : Type*) [Fintype α] {n : ℕ}
    (hcard : Fintype.card α ≤ n) : α ↪ Fin n where
  toFun a :=
    ⟨(Fintype.equivFin α a).1,
      lt_of_lt_of_le (Fintype.equivFin α a).2 hcard⟩
  inj' := by
    intro a b hab
    have hval :
        ((Fintype.equivFin α) a).1 = ((Fintype.equivFin α) b).1 := by
      exact congrArg (fun x : Fin n => x.1) hab
    exact (Fintype.equivFin α).injective (Fin.ext hval)

omit [DecidableEq V] in
/-- In a finite acyclic directed relation, every vertex has a backwards
ancestor with no predecessor.

The proof chooses, among all ancestors of `x`, one of minimum topological rank.
Any predecessor of that ancestor would be another ancestor of smaller rank. -/
theorem exists_reflTransGen_minimal_predecessor
    {α : Type*} [Fintype α] (rel : α → α → Prop)
    (rho : Lax17Proofs.SimpleGraph.PathSlicing.TopologicalRank rel)
    (x : α) :
    ∃ s : α,
      Relation.ReflTransGen rel s x ∧
        ∀ p : α, ¬ rel p s := by
  classical
  let Anc : Finset α :=
    Finset.univ.filter fun s => Relation.ReflTransGen rel s x
  have hAnc_nonempty : Anc.Nonempty := by
    refine ⟨x, ?_⟩
    simp [Anc, Relation.ReflTransGen.refl]
  have hRank_nonempty : (Anc.image rho.rank).Nonempty :=
    hAnc_nonempty.image _
  let rmin := (Anc.image rho.rank).min' hRank_nonempty
  have hrmin_mem : rmin ∈ Anc.image rho.rank :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.1 hrmin_mem with ⟨s, hsAnc, hsRank⟩
  have hsReach : Relation.ReflTransGen rel s x :=
    (Finset.mem_filter.1 hsAnc).2
  refine ⟨s, hsReach, ?_⟩
  intro p hps
  have hpAnc : p ∈ Anc := by
    simp [Anc, Relation.ReflTransGen.head hps hsReach]
  have hpRank_mem : rho.rank p ∈ Anc.image rho.rank :=
    Finset.mem_image.2 ⟨p, hpAnc, rfl⟩
  have hmin_le : rmin ≤ rho.rank p :=
    Finset.min'_le _ _ hpRank_mem
  have hs_le_p : rho.rank s ≤ rho.rank p := by
    simpa [hsRank] using hmin_le
  have hp_lt_s : rho.rank p < rho.rank s :=
    rho.rel_lt hps
  exact (not_lt_of_ge hs_le_p) hp_lt_s

/-- The chain starts in Theorem 2.2: one start at every red source and one
start at every blue source. -/
abbrev TwoPairStartIndex
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) :=
  P.Index ⊕ Q.Index

namespace TwoPairStartIndex

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}

instance : Fintype (TwoPairStartIndex P Q) := inferInstance
instance : DecidableEq (TwoPairStartIndex P Q) := inferInstance

omit [Fintype V] in
/-- The number of red/blue chain starts is the sum of the two routing sizes. -/
@[simp] theorem card :
    Fintype.card (TwoPairStartIndex P Q) = P.card + Q.card := by
  simp [TwoPairStartIndex, PerfectPathPacking.card]

/-- The canonical start labels embed into `Fin (2*k)` when both routing
families have size at most `k`. -/
noncomputable def labelEmbedding {k : ℕ}
    (hP : P.card ≤ k) (hQ : Q.card ≤ k) :
    TwoPairStartIndex P Q ↪ Fin (2 * k) :=
  fintypeEmbeddingFinOfCardLe (TwoPairStartIndex P Q) (by
    rw [card]
    omega)

/-- The alternating state at a start: red sources next follow red, blue
sources next follow blue. -/
def state
    (a : TwoPairStartIndex P Q) : TwoPairAltState V :=
  match a with
  | Sum.inl i => ((P.path i).source, TwoPairColor.red)
  | Sum.inr j => ((Q.path j).source, TwoPairColor.blue)

/-- Reachability from one of the canonical chain starts. -/
def Reaches
    (a : TwoPairStartIndex P Q) (x : TwoPairAltState V) : Prop :=
  Relation.ReflTransGen (TwoPairAltStep P Q) (state (P := P) (Q := Q) a) x

end TwoPairStartIndex

/-- Reachability-cover form of Theorem 2.2.

Instead of storing the alternating chains as `GraphPath`s, this stores a
deterministic alternating state reached by each vertex from one of the `2k`
starts.  The two order fields are Claim 2.6 in reachability form. -/
structure TwoPairForwardReachCover
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- The start state of each chain label. -/
  start : Fin (2 * k) → TwoPairAltState V
  /-- The selected label/start for each vertex. -/
  label : V → Fin (2 * k)
  /-- The occurrence state of each vertex on its selected chain. -/
  state : V → TwoPairAltState V
  /-- The occurrence state really is an occurrence of that vertex. -/
  state_vertex : ∀ v : V, (state v).1 = v
  /-- Each vertex is reached from its selected start. -/
  reaches :
    ∀ v : V,
      Relation.ReflTransGen (TwoPairAltStep P Q) (start (label v)) (state v)
  /-- Claim 2.6 for red paths, stated for alternating reachability. -/
  red_order_of_reach :
    ∀ (i : P.Index) ⦃x y : V⦄,
      Relation.ReflTransGen (TwoPairAltStep P Q) (state x) (state y) →
        x ∈ (P.path i).vertexSet →
          y ∈ (P.path i).vertexSet →
            (P.path i).Before x y
  /-- Claim 2.6 for blue paths, stated for alternating reachability. -/
  blue_order_of_reach :
    ∀ (j : Q.Index) ⦃x y : V⦄,
      Relation.ReflTransGen (TwoPairAltStep P Q) (state x) (state y) →
        x ∈ (Q.path j).vertexSet →
          y ∈ (Q.path j).vertexSet →
            (Q.path j).Before x y

namespace TwoPairForwardReachCover

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- Build a reachability cover from the canonical starts once every vertex has
some alternating state reachable from one of those starts.

The extra `defaultState` is used only on labels in `Fin (2*k)` that are not in
the image of the canonical start embedding.  Those labels are never selected
by the constructed `label` map. -/
noncomputable def ofCanonicalReach
    (defaultState : TwoPairAltState V)
    (hP : P.card ≤ k) (hQ : Q.card ≤ k)
    (hreach :
      ∀ v : V,
        ∃ a : TwoPairStartIndex P Q, ∃ c : TwoPairColor,
          Relation.ReflTransGen (TwoPairAltStep P Q)
            (TwoPairStartIndex.state (P := P) (Q := Q) a) (v, c))
    (hred :
      ∀ (i : P.Index) ⦃sx sy : TwoPairAltState V⦄,
        Relation.ReflTransGen (TwoPairAltStep P Q) sx sy →
          sx.1 ∈ (P.path i).vertexSet →
            sy.1 ∈ (P.path i).vertexSet →
              (P.path i).Before sx.1 sy.1)
    (hblue :
      ∀ (j : Q.Index) ⦃sx sy : TwoPairAltState V⦄,
        Relation.ReflTransGen (TwoPairAltStep P Q) sx sy →
          sx.1 ∈ (Q.path j).vertexSet →
            sy.1 ∈ (Q.path j).vertexSet →
              (Q.path j).Before sx.1 sy.1) :
    TwoPairForwardReachCover P Q k := by
  classical
  let emb := TwoPairStartIndex.labelEmbedding (P := P) (Q := Q) hP hQ
  let startIndex : V → TwoPairStartIndex P Q := fun v =>
    Classical.choose (hreach v)
  let stateColor : V → TwoPairColor := fun v =>
    Classical.choose (Classical.choose_spec (hreach v))
  let label : V → Fin (2 * k) := fun v => emb (startIndex v)
  let state : V → TwoPairAltState V := fun v => (v, stateColor v)
  let start : Fin (2 * k) → TwoPairAltState V := fun l =>
    if h : ∃ a : TwoPairStartIndex P Q, emb a = l then
      TwoPairStartIndex.state (P := P) (Q := Q) (Classical.choose h)
    else
      defaultState
  refine
    { start := start
      label := label
      state := state
      state_vertex := ?_
      reaches := ?_
      red_order_of_reach := ?_
      blue_order_of_reach := ?_ }
  · intro v
    rfl
  · intro v
    have hstart_exists :
        ∃ a : TwoPairStartIndex P Q, emb a = label v :=
      ⟨startIndex v, rfl⟩
    have hchoose :
        Classical.choose hstart_exists = startIndex v :=
      emb.injective (Classical.choose_spec hstart_exists)
    have hstart :
        start (label v) =
          TwoPairStartIndex.state (P := P) (Q := Q) (startIndex v) := by
      dsimp [start]
      rw [dif_pos hstart_exists]
      simpa [hchoose]
    have hreach_v :
        Relation.ReflTransGen (TwoPairAltStep P Q)
          (TwoPairStartIndex.state (P := P) (Q := Q) (startIndex v))
          (v, stateColor v) :=
      Classical.choose_spec (Classical.choose_spec (hreach v))
    simpa [state, hstart] using hreach_v
  · intro i x y hxy hx hy
    exact hred i hxy hx hy
  · intro j x y hxy hx hy
    exact hblue j hxy hx hy

/-- The reachability-cover form gives the forward Theorem 2.2 labeling. -/
noncomputable def toForwardLabeling
    (Z : TwoPairForwardReachCover P Q k) :
    TwoPairForwardLabeling P Q k where
  label := Z.label
  same_label_order := by
    intro x y i j hxR hyR hxB hyB hlabel hxyR
    classical
    have hxReach :
        Relation.ReflTransGen (TwoPairAltStep P Q)
          (Z.start (Z.label x)) (Z.state x) :=
      Z.reaches x
    have hyReach :
        Relation.ReflTransGen (TwoPairAltStep P Q)
          (Z.start (Z.label x)) (Z.state y) := by
      simpa [hlabel] using Z.reaches y
    rcases TwoPairAltStep.comparable_of_same_start
        (P := P) (Q := Q) hxReach hyReach with hxyState | hyxState
    · exact Z.blue_order_of_reach j hxyState hxB hyB
    · have hyxR : (P.path i).Before y x :=
        Z.red_order_of_reach i hyxState hyR hxR
      have hxy : x = y := (P.path i).before_antisymm hxyR hyxR
      subst y
      exact (Q.path j).before_refl hxB

end TwoPairForwardReachCover

/-- Reachability-cover form of Theorem 2.2 after reversing all red paths,
translated back to the original red orientation. -/
structure TwoPairReverseRedReachCover
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- The start state of each reversed-red chain label. -/
  start : Fin (2 * k) → TwoPairAltState V
  /-- The selected reversed-red label/start for each vertex. -/
  label : V → Fin (2 * k)
  /-- The occurrence state of each vertex on its selected reversed-red chain. -/
  state : V → TwoPairAltState V
  /-- The occurrence state really is an occurrence of that vertex. -/
  state_vertex : ∀ v : V, (state v).1 = v
  /-- Each vertex is reached from its selected start in the reversed-red
  alternating relation. -/
  reaches :
    ∀ v : V,
      Relation.ReflTransGen (TwoPairAltStep P.reverse Q)
        (start (label v)) (state v)
  /-- Claim 2.6 for reversed red paths, translated back to original red
  order. -/
  red_reverse_order_of_reach :
    ∀ (i : P.Index) ⦃x y : V⦄,
      Relation.ReflTransGen (TwoPairAltStep P.reverse Q) (state x) (state y) →
        x ∈ (P.path i).vertexSet →
          y ∈ (P.path i).vertexSet →
            (P.path i).Before y x
  /-- Claim 2.6 for blue paths in the reversed-red instance. -/
  blue_order_of_reach :
    ∀ (j : Q.Index) ⦃x y : V⦄,
      Relation.ReflTransGen (TwoPairAltStep P.reverse Q) (state x) (state y) →
        x ∈ (Q.path j).vertexSet →
          y ∈ (Q.path j).vertexSet →
            (Q.path j).Before x y

namespace TwoPairReverseRedReachCover

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- The reversed-red reachability-cover form gives the second Theorem 2.2
labeling used in the counting proof. -/
noncomputable def toReverseRedLabeling
    (Z : TwoPairReverseRedReachCover P Q k) :
    TwoPairReverseRedLabeling P Q k where
  label := Z.label
  same_reverseLabel_order := by
    intro x y i j hxR hyR hxB hyB hlabel hxyR
    classical
    have hxReach :
        Relation.ReflTransGen (TwoPairAltStep P.reverse Q)
          (Z.start (Z.label x)) (Z.state x) :=
      Z.reaches x
    have hyReach :
        Relation.ReflTransGen (TwoPairAltStep P.reverse Q)
          (Z.start (Z.label x)) (Z.state y) := by
      simpa [hlabel] using Z.reaches y
    rcases TwoPairAltStep.comparable_of_same_start
        (P := P.reverse) (Q := Q) hxReach hyReach with hxyState | hyxState
    · have hyxR : (P.path i).Before y x :=
        Z.red_reverse_order_of_reach i hxyState hxR hyR
      have hxy : x = y := (P.path i).before_antisymm hxyR hyxR
      subst y
      exact (Q.path j).before_refl hxB
    · exact Z.blue_order_of_reach j hyxState hyB hxB

end TwoPairReverseRedReachCover

namespace TwoPairForwardReachCover

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- A forward reachability cover for the instance with the red paths reversed
is exactly the reversed-red reachability cover needed for the original
orientation. -/
noncomputable def toReverseRedReachCoverOfReverse
    (Z : TwoPairForwardReachCover P.reverse Q k) :
    TwoPairReverseRedReachCover P Q k where
  start := Z.start
  label := Z.label
  state := Z.state
  state_vertex := Z.state_vertex
  reaches := Z.reaches
  red_reverse_order_of_reach := by
    intro i x y hxy hx hy
    have hxRev : x ∈ ((P.reverse).path i).vertexSet := by
      simpa using hx
    have hyRev : y ∈ ((P.reverse).path i).vertexSet := by
      simpa using hy
    have hrev :
        ((P.reverse).path i).Before x y :=
      Z.red_order_of_reach i hxy hxRev hyRev
    have hback :
        (((P.reverse).path i).reverse).Before y x :=
      GraphPath.reverse_before_of_before ((P.reverse).path i) hrev
    simpa [PerfectPathPacking.reverse] using hback
  blue_order_of_reach := by
    intro j x y hxy hx hy
    exact Z.blue_order_of_reach j hxy hx hy

end TwoPairForwardReachCover

/-- Branch-vertex restricted version of the forward labeling from Theorem 2.2.

The singleton-terminal minor model can create one-color terminal stubs.  They
are harmless for Theorem 1.3, because the theorem counts only vertices of
degree more than two in the red/blue union.  This structure records exactly the
label-order property needed on those high-degree vertices. -/
structure TwoPairBranchForwardLabeling
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- Label assigned to a high-degree union vertex. -/
  label :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Fin (2 * k)
  /-- Equal labels force agreement of red and blue order on high-degree
  vertices. -/
  same_label_order :
    ∀ ⦃x y : V⦄
      (hx : x ∈ branchVertexFinset (twoPackingUnionGraph P Q))
      (hy : y ∈ branchVertexFinset (twoPackingUnionGraph P Q))
      (i : P.Index) (j : Q.Index),
      x ∈ (P.path i).vertexSet →
        y ∈ (P.path i).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              label x hx = label y hy →
                (P.path i).Before x y →
                  (Q.path j).Before x y

/-- Branch-vertex restricted reversed-red labeling. -/
structure TwoPairBranchReverseRedLabeling
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- Reversed-red label assigned to a high-degree union vertex. -/
  label :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Fin (2 * k)
  /-- Equal reversed-red labels force disagreement of original red and blue
  order on high-degree vertices. -/
  same_reverseLabel_order :
    ∀ ⦃x y : V⦄
      (hx : x ∈ branchVertexFinset (twoPackingUnionGraph P Q))
      (hy : y ∈ branchVertexFinset (twoPackingUnionGraph P Q))
      (i : P.Index) (j : Q.Index),
      x ∈ (P.path i).vertexSet →
        y ∈ (P.path i).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              label x hx = label y hy →
                (P.path i).Before x y →
                  (Q.path j).Before y x

/-- Branch-restricted reachability cover for the forward alternating chains. -/
structure TwoPairBranchForwardReachCover
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- The start state of each label. -/
  start : Fin (2 * k) → TwoPairAltState V
  /-- Label selected for each high-degree union vertex. -/
  label :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Fin (2 * k)
  /-- The occurrence state selected for each high-degree union vertex. -/
  state :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → TwoPairAltState V
  /-- The occurrence state is really an occurrence of the labelled vertex. -/
  state_vertex :
    ∀ ⦃v : V⦄
      (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      (state v hv).1 = v
  /-- Each selected occurrence is reached from its selected start. -/
  reaches :
    ∀ ⦃v : V⦄
      (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      Relation.ReflTransGen (TwoPairAltStep P Q)
        (start (label v hv)) (state v hv)
  /-- Claim 2.6 for red paths, in reachability form. -/
  red_order_of_reach :
    ∀ (i : P.Index) ⦃sx sy : TwoPairAltState V⦄,
      Relation.ReflTransGen (TwoPairAltStep P Q) sx sy →
        sx.1 ∈ (P.path i).vertexSet →
          sy.1 ∈ (P.path i).vertexSet →
            (P.path i).Before sx.1 sy.1
  /-- Claim 2.6 for blue paths, in reachability form. -/
  blue_order_of_reach :
    ∀ (j : Q.Index) ⦃sx sy : TwoPairAltState V⦄,
      Relation.ReflTransGen (TwoPairAltStep P Q) sx sy →
        sx.1 ∈ (Q.path j).vertexSet →
          sy.1 ∈ (Q.path j).vertexSet →
            (Q.path j).Before sx.1 sy.1

namespace TwoPairBranchForwardReachCover

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- Build a branch-restricted reach cover from canonical starts, assuming only
that high-degree union vertices have reachable alternating occurrences. -/
noncomputable def ofCanonicalBranchReach
    (defaultState : TwoPairAltState V)
    (hP : P.card ≤ k) (hQ : Q.card ≤ k)
    (hreach :
      ∀ ⦃v : V⦄,
        v ∈ branchVertexFinset (twoPackingUnionGraph P Q) →
          ∃ a : TwoPairStartIndex P Q, ∃ c : TwoPairColor,
            Relation.ReflTransGen (TwoPairAltStep P Q)
              (TwoPairStartIndex.state (P := P) (Q := Q) a) (v, c))
    (hred :
      ∀ (i : P.Index) ⦃sx sy : TwoPairAltState V⦄,
        Relation.ReflTransGen (TwoPairAltStep P Q) sx sy →
          sx.1 ∈ (P.path i).vertexSet →
            sy.1 ∈ (P.path i).vertexSet →
              (P.path i).Before sx.1 sy.1)
    (hblue :
      ∀ (j : Q.Index) ⦃sx sy : TwoPairAltState V⦄,
        Relation.ReflTransGen (TwoPairAltStep P Q) sx sy →
          sx.1 ∈ (Q.path j).vertexSet →
            sy.1 ∈ (Q.path j).vertexSet →
              (Q.path j).Before sx.1 sy.1) :
    TwoPairBranchForwardReachCover P Q k := by
  classical
  let emb := TwoPairStartIndex.labelEmbedding (P := P) (Q := Q) hP hQ
  let startIndex :
      ∀ v : V,
        v ∈ branchVertexFinset (twoPackingUnionGraph P Q) →
          TwoPairStartIndex P Q := fun v hv =>
    Classical.choose (hreach hv)
  let stateColor :
      ∀ v : V,
        v ∈ branchVertexFinset (twoPackingUnionGraph P Q) →
          TwoPairColor := fun v hv =>
    Classical.choose (Classical.choose_spec (hreach hv))
  let label :
      ∀ v : V,
        v ∈ branchVertexFinset (twoPackingUnionGraph P Q) →
          Fin (2 * k) := fun v hv => emb (startIndex v hv)
  let state :
      ∀ v : V,
        v ∈ branchVertexFinset (twoPackingUnionGraph P Q) →
          TwoPairAltState V := fun v hv => (v, stateColor v hv)
  let start : Fin (2 * k) → TwoPairAltState V := fun l =>
    if h : ∃ a : TwoPairStartIndex P Q, emb a = l then
      TwoPairStartIndex.state (P := P) (Q := Q) (Classical.choose h)
    else
      defaultState
  refine
    { start := start
      label := label
      state := state
      state_vertex := ?_
      reaches := ?_
      red_order_of_reach := ?_
      blue_order_of_reach := ?_ }
  · intro v hv
    rfl
  · intro v hv
    have hstart_exists :
        ∃ a : TwoPairStartIndex P Q, emb a = label v hv :=
      ⟨startIndex v hv, rfl⟩
    have hchoose :
        Classical.choose hstart_exists = startIndex v hv :=
      emb.injective (Classical.choose_spec hstart_exists)
    have hstart :
        start (label v hv) =
          TwoPairStartIndex.state (P := P) (Q := Q) (startIndex v hv) := by
      dsimp [start]
      rw [dif_pos hstart_exists]
      simpa [hchoose]
    have hreach_v :
        Relation.ReflTransGen (TwoPairAltStep P Q)
          (TwoPairStartIndex.state (P := P) (Q := Q) (startIndex v hv))
          (v, stateColor v hv) :=
      Classical.choose_spec (Classical.choose_spec (hreach hv))
    simpa [state, hstart] using hreach_v
  · intro i sx sy hxy hx hy
    exact hred i hxy hx hy
  · intro j sx sy hxy hx hy
    exact hblue j hxy hx hy

/-- A branch-restricted reach cover gives the branch-restricted forward
labeling. -/
noncomputable def toBranchForwardLabeling
    (Z : TwoPairBranchForwardReachCover P Q k) :
    TwoPairBranchForwardLabeling P Q k where
  label := Z.label
  same_label_order := by
    intro x y hx hy i j hxR hyR hxB hyB hlabel hxyR
    classical
    have hxReach :
        Relation.ReflTransGen (TwoPairAltStep P Q)
          (Z.start (Z.label x hx)) (Z.state x hx) :=
      Z.reaches hx
    have hyReach :
        Relation.ReflTransGen (TwoPairAltStep P Q)
          (Z.start (Z.label x hx)) (Z.state y hy) := by
      simpa [hlabel] using Z.reaches hy
    rcases TwoPairAltStep.comparable_of_same_start
        (P := P) (Q := Q) hxReach hyReach with hxyState | hyxState
    · have hxyB :=
        Z.blue_order_of_reach j hxyState
        (by simpa [Z.state_vertex hx] using hxB)
        (by simpa [Z.state_vertex hy] using hyB)
      simpa [Z.state_vertex hx, Z.state_vertex hy] using hxyB
    · have hyxR : (P.path i).Before y x :=
        by
          have hyxR' :
              (P.path i).Before (Z.state y hy).1 (Z.state x hx).1 :=
            Z.red_order_of_reach i hyxState
              (by simpa [Z.state_vertex hy] using hyR)
              (by simpa [Z.state_vertex hx] using hxR)
          simpa [Z.state_vertex hy, Z.state_vertex hx] using hyxR'
      have hxy : x = y := (P.path i).before_antisymm hxyR hyxR
      subst y
      exact (Q.path j).before_refl hxB

end TwoPairBranchForwardReachCover

/-- Branch-restricted reachability cover for the reversed-red instance. -/
structure TwoPairBranchReverseRedReachCover
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- The start state of each reversed-red label. -/
  start : Fin (2 * k) → TwoPairAltState V
  /-- Label selected for each high-degree union vertex. -/
  label :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Fin (2 * k)
  /-- The occurrence state selected for each high-degree union vertex. -/
  state :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → TwoPairAltState V
  /-- The occurrence state is really an occurrence of the labelled vertex. -/
  state_vertex :
    ∀ ⦃v : V⦄
      (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      (state v hv).1 = v
  /-- Each selected occurrence is reached from its selected start in the
  reversed-red alternating relation. -/
  reaches :
    ∀ ⦃v : V⦄
      (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      Relation.ReflTransGen (TwoPairAltStep P.reverse Q)
        (start (label v hv)) (state v hv)
  /-- Claim 2.6 for reversed red paths, translated to original red order. -/
  red_reverse_order_of_reach :
    ∀ (i : P.Index) ⦃sx sy : TwoPairAltState V⦄,
      Relation.ReflTransGen (TwoPairAltStep P.reverse Q) sx sy →
        sx.1 ∈ (P.path i).vertexSet →
          sy.1 ∈ (P.path i).vertexSet →
            (P.path i).Before sy.1 sx.1
  /-- Claim 2.6 for blue paths in the reversed-red instance. -/
  blue_order_of_reach :
    ∀ (j : Q.Index) ⦃sx sy : TwoPairAltState V⦄,
      Relation.ReflTransGen (TwoPairAltStep P.reverse Q) sx sy →
        sx.1 ∈ (Q.path j).vertexSet →
          sy.1 ∈ (Q.path j).vertexSet →
            (Q.path j).Before sx.1 sy.1

namespace TwoPairBranchReverseRedReachCover

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- A branch-restricted reversed-red reach cover gives the branch-restricted
reversed-red labeling. -/
noncomputable def toBranchReverseRedLabeling
    (Z : TwoPairBranchReverseRedReachCover P Q k) :
    TwoPairBranchReverseRedLabeling P Q k where
  label := Z.label
  same_reverseLabel_order := by
    intro x y hx hy i j hxR hyR hxB hyB hlabel hxyR
    classical
    have hxReach :
        Relation.ReflTransGen (TwoPairAltStep P.reverse Q)
          (Z.start (Z.label x hx)) (Z.state x hx) :=
      Z.reaches hx
    have hyReach :
        Relation.ReflTransGen (TwoPairAltStep P.reverse Q)
          (Z.start (Z.label x hx)) (Z.state y hy) := by
      simpa [hlabel] using Z.reaches hy
    rcases TwoPairAltStep.comparable_of_same_start
        (P := P.reverse) (Q := Q) hxReach hyReach with hxyState | hyxState
    · have hyxR : (P.path i).Before y x :=
        by
          have hyxR' :
              (P.path i).Before (Z.state y hy).1 (Z.state x hx).1 :=
            Z.red_reverse_order_of_reach i hxyState
              (by simpa [Z.state_vertex hx] using hxR)
              (by simpa [Z.state_vertex hy] using hyR)
          simpa [Z.state_vertex hy, Z.state_vertex hx] using hyxR'
      have hxy : x = y := (P.path i).before_antisymm hxyR hyxR
      subst y
      exact (Q.path j).before_refl hxB
    · have hyxB :=
        Z.blue_order_of_reach j hyxState
        (by simpa [Z.state_vertex hy] using hyB)
        (by simpa [Z.state_vertex hx] using hxB)
      simpa [Z.state_vertex hy, Z.state_vertex hx] using hyxB

end TwoPairBranchReverseRedReachCover

namespace TwoPairBranchForwardReachCover

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- A branch-restricted forward reachability cover for the red-reversed
instance is exactly a branch-restricted reversed-red reachability cover for
the original instance. -/
noncomputable def toBranchReverseRedReachCoverOfReverse
    (Z : TwoPairBranchForwardReachCover P.reverse Q k) :
    TwoPairBranchReverseRedReachCover P Q k where
  start := Z.start
  label := by
    intro v hv
    exact Z.label v (by simpa [twoPackingUnionGraph] using hv)
  state := by
    intro v hv
    exact Z.state v (by simpa [twoPackingUnionGraph] using hv)
  state_vertex := by
    intro v hv
    exact Z.state_vertex
      (by simpa [twoPackingUnionGraph] using hv)
  reaches := by
    intro v hv
    exact Z.reaches
      (by simpa [twoPackingUnionGraph] using hv)
  red_reverse_order_of_reach := by
    intro i sx sy hxy hx hy
    have hxRev : sx.1 ∈ ((P.reverse).path i).vertexSet := by
      simpa using hx
    have hyRev : sy.1 ∈ ((P.reverse).path i).vertexSet := by
      simpa using hy
    have hrev :
        ((P.reverse).path i).Before sx.1 sy.1 :=
      Z.red_order_of_reach i hxy hxRev hyRev
    have hback :
        (((P.reverse).path i).reverse).Before sy.1 sx.1 :=
      GraphPath.reverse_before_of_before ((P.reverse).path i) hrev
    simpa [PerfectPathPacking.reverse] using hback
  blue_order_of_reach := by
    intro j sx sy hxy hx hy
    exact Z.blue_order_of_reach j hxy hx hy

end TwoPairBranchForwardReachCover

/-- Branch-restricted chain-label certificate consumed by the counting proof. -/
structure TwoPairBranchChainLabelCertificate
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- First branch label. -/
  label :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Fin (2 * k)
  /-- Reversed-red branch label. -/
  reverseLabel :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Fin (2 * k)
  /-- The red path containing a high-degree union vertex. -/
  redIndex :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → P.Index
  /-- The blue path containing a high-degree union vertex. -/
  blueIndex :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Q.Index
  /-- Membership in the selected red path. -/
  red_mem :
    ∀ ⦃v : V⦄ (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      v ∈ (P.path (redIndex v hv)).vertexSet
  /-- Membership in the selected blue path. -/
  blue_mem :
    ∀ ⦃v : V⦄ (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      v ∈ (Q.path (blueIndex v hv)).vertexSet
  /-- Equal first labels force agreement of red and blue order. -/
  same_label_order :
    ∀ ⦃x y : V⦄
      (hx : x ∈ branchVertexFinset (twoPackingUnionGraph P Q))
      (hy : y ∈ branchVertexFinset (twoPackingUnionGraph P Q))
      (i : P.Index) (j : Q.Index),
      x ∈ (P.path i).vertexSet →
        y ∈ (P.path i).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              label x hx = label y hy →
                (P.path i).Before x y →
                  (Q.path j).Before x y
  /-- Equal reversed-red labels force disagreement of original red and blue
  order. -/
  same_reverseLabel_order :
    ∀ ⦃x y : V⦄
      (hx : x ∈ branchVertexFinset (twoPackingUnionGraph P Q))
      (hy : y ∈ branchVertexFinset (twoPackingUnionGraph P Q))
      (i : P.Index) (j : Q.Index),
      x ∈ (P.path i).vertexSet →
        y ∈ (P.path i).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              reverseLabel x hx = reverseLabel y hy →
                (P.path i).Before x y →
                  (Q.path j).Before y x

namespace TwoPairBranchChainLabelCertificate

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- Assemble branch-restricted labelings with the automatic branch-path
carrier. -/
noncomputable def ofBranchLabelings
    (L : TwoPairBranchForwardLabeling P Q k)
    (Lrev : TwoPairBranchReverseRedLabeling P Q k) :
    TwoPairBranchChainLabelCertificate P Q k where
  label := L.label
  reverseLabel := Lrev.label
  redIndex := (TwoPairBranchCarrier.ofPackings P Q).redIndex
  blueIndex := (TwoPairBranchCarrier.ofPackings P Q).blueIndex
  red_mem := (TwoPairBranchCarrier.ofPackings P Q).red_mem
  blue_mem := (TwoPairBranchCarrier.ofPackings P Q).blue_mem
  same_label_order := L.same_label_order
  same_reverseLabel_order := Lrev.same_reverseLabel_order

/-- The tuple used in the branch-restricted pigeonhole/counting step. -/
noncomputable def branchTuple
    (C : TwoPairBranchChainLabelCertificate P Q k)
    (v : {x : V // x ∈ branchVertexFinset (twoPackingUnionGraph P Q)}) :
    P.Index × Q.Index × Fin (2 * k) × Fin (2 * k) :=
  (C.redIndex v.1 v.2, C.blueIndex v.1 v.2,
    C.label v.1 v.2, C.reverseLabel v.1 v.2)

/-- The branch-label tuple is injective on high-degree vertices. -/
theorem branchTuple_injective
    (C : TwoPairBranchChainLabelCertificate P Q k) :
    Function.Injective C.branchTuple := by
  classical
  intro x y hxy
  apply Subtype.ext
  dsimp [branchTuple] at hxy
  have hred :
      C.redIndex x.1 x.2 = C.redIndex y.1 y.2 :=
    congrArg Prod.fst hxy
  have hblue :
      C.blueIndex x.1 x.2 = C.blueIndex y.1 y.2 := by
    exact congrArg (fun z => z.2.1) hxy
  have hlabel : C.label x.1 x.2 = C.label y.1 y.2 := by
    exact congrArg (fun z => z.2.2.1) hxy
  have hrev : C.reverseLabel x.1 x.2 = C.reverseLabel y.1 y.2 := by
    exact congrArg (fun z => z.2.2.2) hxy
  let i := C.redIndex x.1 x.2
  let j := C.blueIndex x.1 x.2
  have hxR : x.1 ∈ (P.path i).vertexSet := by
    simpa [i] using C.red_mem x.2
  have hyR : y.1 ∈ (P.path i).vertexSet := by
    simpa [i, hred] using C.red_mem y.2
  have hxB : x.1 ∈ (Q.path j).vertexSet := by
    simpa [j] using C.blue_mem x.2
  have hyB : y.1 ∈ (Q.path j).vertexSet := by
    simpa [j, hblue] using C.blue_mem y.2
  rcases GraphPath.before_total_of_mem (P.path i) hxR hyR with hxyR | hyxR
  · have hxyB : (Q.path j).Before x.1 y.1 :=
      C.same_label_order x.2 y.2 i j hxR hyR hxB hyB hlabel hxyR
    have hyxB : (Q.path j).Before y.1 x.1 :=
      C.same_reverseLabel_order x.2 y.2 i j hxR hyR hxB hyB hrev hxyR
    exact (Q.path j).before_antisymm hxyB hyxB
  · have hyxLabel : C.label y.1 y.2 = C.label x.1 x.2 := hlabel.symm
    have hyxRev : C.reverseLabel y.1 y.2 = C.reverseLabel x.1 x.2 := hrev.symm
    have hyxB : (Q.path j).Before y.1 x.1 :=
      C.same_label_order y.2 x.2 i j hyR hxR hyB hxB hyxLabel hyxR
    have hxyB : (Q.path j).Before x.1 y.1 :=
      C.same_reverseLabel_order y.2 x.2 i j hyR hxR hyB hxB hyxRev hyxR
    exact ((Q.path j).before_antisymm hyxB hxyB).symm

/-- Branch-count bound from branch-restricted labels. -/
theorem branchVertexCount_le_tuple_count
    (C : TwoPairBranchChainLabelCertificate P Q k) :
    branchVertexCount (twoPackingUnionGraph P Q) ≤
      P.card * Q.card * (2 * k) * (2 * k) := by
  classical
  let B := branchVertexFinset (twoPackingUnionGraph P Q)
  have hcard :
      B.card ≤
        Fintype.card (P.Index × Q.Index × Fin (2 * k) × Fin (2 * k)) := by
    simpa [B] using
      (Fintype.card_le_of_injective C.branchTuple C.branchTuple_injective)
  have htuple :
      Fintype.card (P.Index × Q.Index × Fin (2 * k) × Fin (2 * k)) =
        P.card * Q.card * (2 * k) * (2 * k) := by
    simp [PerfectPathPacking.card, Nat.mul_assoc]
  simpa [branchVertexCount, B, htuple] using hcard

/-- The Section 2 branch-count bound following from the branch-restricted
certificate. -/
theorem branchVertexCount_le_four_mul_pow
    (C : TwoPairBranchChainLabelCertificate P Q k)
    (hPcard : P.card ≤ k) (hQcard : Q.card ≤ k) :
    branchVertexCount (twoPackingUnionGraph P Q) ≤ 4 * k ^ 4 := by
  classical
  have htuple := C.branchVertexCount_le_tuple_count
  have hle :
      P.card * Q.card * (2 * k) * (2 * k) ≤
        k * k * (2 * k) * (2 * k) := by
    gcongr
  calc
    branchVertexCount (twoPackingUnionGraph P Q)
        ≤ P.card * Q.card * (2 * k) * (2 * k) := htuple
    _ ≤ k * k * (2 * k) * (2 * k) := hle
    _ = 4 * k ^ 4 := by ring

/-- The Theorem 1.3 numerical bound follows from the branch-restricted
certificate. -/
theorem branchVertexCount_le_theorem13_bound
    (C : TwoPairBranchChainLabelCertificate P Q k)
    (hPcard : P.card ≤ k) (hQcard : Q.card ≤ k) :
    branchVertexCount (twoPackingUnionGraph P Q) ≤ 8 * k ^ 4 + 8 * k := by
  have hfour := C.branchVertexCount_le_four_mul_pow hPcard hQcard
  nlinarith [hfour, Nat.zero_le (k ^ 4), Nat.zero_le k]

end TwoPairBranchChainLabelCertificate

namespace TwoPairMinimalGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

omit [Fintype V] in
/-- Under the Theorem 2.1 terminal hypotheses, a directed red edge and a
directed blue edge cannot use the same underlying edge. -/
theorem false_of_redColorEdge_and_blueColorEdge
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {u v : W}
    (hred :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.red u v)
    (hblue :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.blue u v) :
    False := by
  rcases hred with ⟨_i, hredEdge, _hredBefore, _hne⟩
  rcases hblue with ⟨_j, hblueEdge, _hblueBefore, _hne'⟩
  have hredPack :
      s(u, v) ∈ M.good.redRouting.toPathPacking.edgeSet :=
    (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨_i, hredEdge⟩
  have hbluePack :
      s(u, v) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
    (M.good.blueRouting.toPathPacking.mem_edgeSet).2 ⟨_j, hblueEdge⟩
  exact M.false_of_red_and_blue_edge hdeg hdisj hredPack hbluePack

omit [Fintype V] in
/-- Reversed-orientation version of
`false_of_redColorEdge_and_blueColorEdge`. -/
theorem false_of_redColorEdge_and_reverse_blueColorEdge
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {u v : W}
    (hred :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.red u v)
    (hblue :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.blue v u) :
    False := by
  rcases hred with ⟨_i, hredEdge, _hredBefore, _hne⟩
  rcases hblue with ⟨_j, hblueEdge, _hblueBefore, _hne'⟩
  have hredPack :
      s(u, v) ∈ M.good.redRouting.toPathPacking.edgeSet :=
    (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨_i, hredEdge⟩
  have hbluePack :
      s(u, v) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
    (M.good.blueRouting.toPathPacking.mem_edgeSet).2
      ⟨_j, by simpa [Sym2.eq_swap] using hblueEdge⟩
  exact M.false_of_red_and_blue_edge hdeg hdisj hredPack hbluePack

omit [Fintype V] in
/-- Every edge of a minimal good minor receives a directed red or blue
orientation under the Theorem 2.1 terminal hypotheses. -/
theorem colorEdge_or_reverse_of_adj
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {u v : W} (huv : H.Adj u v) :
    (TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.red u v ∨
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.red v u) ∨
    (TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.blue u v ∨
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.blue v u) := by
  classical
  rcases M.edge_mem_red_xor_blue hdeg hdisj huv with hred | hblue
  · rcases (M.good.redRouting.toPathPacking.mem_edgeSet).1 hred.1 with
      ⟨i, hi⟩
    exact Or.inl
      (TwoPairColorEdge.red_or_reverse_of_mem_red_edge
        (P := M.good.redRouting) (Q := M.good.blueRouting) (i := i) hi)
  · rcases (M.good.blueRouting.toPathPacking.mem_edgeSet).1 hblue.1 with
      ⟨j, hj⟩
    exact Or.inr
      (TwoPairColorEdge.blue_or_reverse_of_mem_blue_edge
        (P := M.good.redRouting) (Q := M.good.blueRouting) (j := j) hj)

omit [Fintype V] in
/-- A terminal cannot be entered by one color and then left by the other
color in an alternating chain under the Section 2 terminal hypotheses. -/
theorem false_of_colorEdge_into_terminal_and_swapped_colorEdge_out
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x y z : W} {c : TwoPairColor}
    (hy : y ∈ M.good.terminalSet)
    (hin :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting c x y)
    (hout :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting c.swap y z) :
    False := by
  classical
  cases c with
  | red =>
      rcases hin with ⟨i, hredEdge, _hredBefore, _hxy_ne⟩
      rcases hout with ⟨j, hblueEdge, _hblueBefore, _hyz_ne⟩
      have hredPack :
          s(x, y) ∈ M.good.redRouting.toPathPacking.edgeSet :=
        (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨i, hredEdge⟩
      have hbluePack_yz :
          s(y, z) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
        (M.good.blueRouting.toPathPacking.mem_edgeSet).2 ⟨j, hblueEdge⟩
      by_cases hxz : x = z
      · have hbluePack :
            s(x, y) ∈ M.good.blueRouting.toPathPacking.edgeSet := by
          simpa [hxz, Sym2.eq_swap] using hbluePack_yz
        exact M.good.false_of_red_and_blue_edge_incident_terminal
          hdeg hdisj hy hredPack hbluePack
      · have hxyAdj : H.Adj y x := by
          exact H.symm (GraphPath.edgeSet_subset_edgeSet
            (M.good.redRouting.path i) hredEdge)
        have hyzAdj : H.Adj y z :=
          GraphPath.edgeSet_subset_edgeSet
            (M.good.blueRouting.path j) hblueEdge
        exact
          (not_degreeAtMost_one_of_two_adj hxyAdj hyzAdj hxz)
            (M.good.degreeAtMost_one_of_mem_terminalSet hdeg hy)
  | blue =>
      rcases hin with ⟨j, hblueEdge, _hblueBefore, _hxy_ne⟩
      rcases hout with ⟨i, hredEdge, _hredBefore, _hyz_ne⟩
      have hbluePack :
          s(x, y) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
        (M.good.blueRouting.toPathPacking.mem_edgeSet).2 ⟨j, hblueEdge⟩
      have hredPack_yz :
          s(y, z) ∈ M.good.redRouting.toPathPacking.edgeSet :=
        (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨i, hredEdge⟩
      by_cases hxz : x = z
      · have hredPack :
            s(x, y) ∈ M.good.redRouting.toPathPacking.edgeSet := by
          simpa [hxz, Sym2.eq_swap] using hredPack_yz
        exact M.good.false_of_red_and_blue_edge_incident_terminal
          hdeg hdisj hy hredPack hbluePack
      · have hxyAdj : H.Adj y x := by
          exact H.symm (GraphPath.edgeSet_subset_edgeSet
            (M.good.blueRouting.path j) hblueEdge)
        have hyzAdj : H.Adj y z :=
          GraphPath.edgeSet_subset_edgeSet
            (M.good.redRouting.path i) hredEdge
        exact
          (not_degreeAtMost_one_of_two_adj hxyAdj hyzAdj hxz)
            (M.good.degreeAtMost_one_of_mem_terminalSet hdeg hy)

omit [Fintype V] in
/-- A blue edge cannot jump backward along a red routing path in a minimal
good minor.  If it is the immediate predecessor edge, it is a forbidden shared
edge; otherwise it is a forbidden shortcut of the unique red routing. -/
theorem false_of_blueColorEdge_backward_on_red_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {i : M.good.redRouting.Index}
    (hblue :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.blue x z)
    (hx : x ∈ (M.good.redRouting.path i).vertexSet)
    (hz : z ∈ (M.good.redRouting.path i).vertexSet)
    (hzxBefore : (M.good.redRouting.path i).Before z x)
    (hxz_ne : x ≠ z) :
    False := by
  classical
  rcases hblue with ⟨j, hblueEdge, _hblueBefore, _hxzBlue_ne⟩
  have hblueAdj : H.Adj x z :=
    GraphPath.edgeSet_subset_edgeSet
      (M.good.blueRouting.path j) hblueEdge
  have hbluePack :
      s(x, z) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
    (M.good.blueRouting.toPathPacking.mem_edgeSet).2 ⟨j, hblueEdge⟩
  have hzx_ne : z ≠ x := fun h => hxz_ne h.symm
  have hz_not_target : z ≠ (M.good.redRouting.path i).target := by
    intro hz_target
    have hxt : (M.good.redRouting.path i).Before x
        (M.good.redRouting.path i).target :=
      (M.good.redRouting.path i).before_target_of_mem hx
    have htx : (M.good.redRouting.path i).Before
        (M.good.redRouting.path i).target x := by
      simpa [hz_target] using hzxBefore
    have htarget_x : (M.good.redRouting.path i).target = x :=
      (M.good.redRouting.path i).before_antisymm htx hxt
    exact hxz_ne (by simpa [hz_target, htarget_x])
  rcases GraphPath.exists_forward_edge_of_mem_not_target
      (M.good.redRouting.path i) hz hz_not_target with
    ⟨w, hredEdge, hzwBefore, hzw_ne⟩
  have hw : w ∈ (M.good.redRouting.path i).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.good.redRouting.path i) hredEdge).2
  have hzData :=
    ((M.good.redRouting.path i).before_iff_vertexIndex_le).1 hzxBefore
  have hzwData :=
    ((M.good.redRouting.path i).before_iff_vertexIndex_le).1 hzwBefore
  have hz_lt_x :
      (M.good.redRouting.path i).vertexIndex z <
        (M.good.redRouting.path i).vertexIndex x := by
    refine lt_of_le_of_ne hzData.2.2 ?_
    intro hidx
    exact hzx_ne
      (GraphPath.eq_of_vertexIndex_eq
        (M.good.redRouting.path i) hz hx hidx)
  have hz_lt_w :
      (M.good.redRouting.path i).vertexIndex z <
        (M.good.redRouting.path i).vertexIndex w := by
    refine lt_of_le_of_ne hzwData.2.2 ?_
    intro hidx
    exact hzw_ne
      (GraphPath.eq_of_vertexIndex_eq
        (M.good.redRouting.path i) hz hw hidx)
  have hw_le_succ :
      (M.good.redRouting.path i).vertexIndex w ≤
        (M.good.redRouting.path i).vertexIndex z + 1 :=
    (M.good.redRouting.path i).edge_vertexIndex_le_succ hredEdge
  have hw_before_x :
      (M.good.redRouting.path i).Before w x := by
    refine ((M.good.redRouting.path i).before_iff_vertexIndex_le).2
      ⟨hw, hx, ?_⟩
    omega
  by_cases hwx : w = x
  · have hredPack :
        s(x, z) ∈ M.good.redRouting.toPathPacking.edgeSet := by
      have hredPack' :
          s(z, w) ∈ M.good.redRouting.toPathPacking.edgeSet :=
        (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨i, hredEdge⟩
      simpa [hwx, Sym2.eq_swap] using hredPack'
    exact M.false_of_red_and_blue_edge hdeg hdisj hredPack hbluePack
  · exact
      PathSlicing.false_of_shortcut_edge_of_edgeSet_unique
        (R := M.good.redRouting)
        (fun R' => M.redRouting_edgeSet_eq_selected hdeg hdisj R')
        hzwBefore hw_before_x hzw_ne hwx (H.symm hblueAdj)

omit [Fintype V] in
/-- Red symmetric version of
`false_of_blueColorEdge_backward_on_red_path`. -/
theorem false_of_redColorEdge_backward_on_blue_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {j : M.good.blueRouting.Index}
    (hred :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.red x z)
    (hx : x ∈ (M.good.blueRouting.path j).vertexSet)
    (hz : z ∈ (M.good.blueRouting.path j).vertexSet)
    (hzxBefore : (M.good.blueRouting.path j).Before z x)
    (hxz_ne : x ≠ z) :
    False := by
  classical
  rcases hred with ⟨i, hredEdge, _hredBefore, _hxzRed_ne⟩
  have hredAdj : H.Adj x z :=
    GraphPath.edgeSet_subset_edgeSet
      (M.good.redRouting.path i) hredEdge
  have hredPack :
      s(x, z) ∈ M.good.redRouting.toPathPacking.edgeSet :=
    (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨i, hredEdge⟩
  have hzx_ne : z ≠ x := fun h => hxz_ne h.symm
  have hz_not_target : z ≠ (M.good.blueRouting.path j).target := by
    intro hz_target
    have hxt : (M.good.blueRouting.path j).Before x
        (M.good.blueRouting.path j).target :=
      (M.good.blueRouting.path j).before_target_of_mem hx
    have htx : (M.good.blueRouting.path j).Before
        (M.good.blueRouting.path j).target x := by
      simpa [hz_target] using hzxBefore
    have htarget_x : (M.good.blueRouting.path j).target = x :=
      (M.good.blueRouting.path j).before_antisymm htx hxt
    exact hxz_ne (by simpa [hz_target, htarget_x])
  rcases GraphPath.exists_forward_edge_of_mem_not_target
      (M.good.blueRouting.path j) hz hz_not_target with
    ⟨w, hblueEdge, hzwBefore, hzw_ne⟩
  have hw : w ∈ (M.good.blueRouting.path j).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.good.blueRouting.path j) hblueEdge).2
  have hzData :=
    ((M.good.blueRouting.path j).before_iff_vertexIndex_le).1 hzxBefore
  have hzwData :=
    ((M.good.blueRouting.path j).before_iff_vertexIndex_le).1 hzwBefore
  have hz_lt_x :
      (M.good.blueRouting.path j).vertexIndex z <
        (M.good.blueRouting.path j).vertexIndex x := by
    refine lt_of_le_of_ne hzData.2.2 ?_
    intro hidx
    exact hzx_ne
      (GraphPath.eq_of_vertexIndex_eq
        (M.good.blueRouting.path j) hz hx hidx)
  have hz_lt_w :
      (M.good.blueRouting.path j).vertexIndex z <
        (M.good.blueRouting.path j).vertexIndex w := by
    refine lt_of_le_of_ne hzwData.2.2 ?_
    intro hidx
    exact hzw_ne
      (GraphPath.eq_of_vertexIndex_eq
        (M.good.blueRouting.path j) hz hw hidx)
  have hw_le_succ :
      (M.good.blueRouting.path j).vertexIndex w ≤
        (M.good.blueRouting.path j).vertexIndex z + 1 :=
    (M.good.blueRouting.path j).edge_vertexIndex_le_succ hblueEdge
  have hw_before_x :
      (M.good.blueRouting.path j).Before w x := by
    refine ((M.good.blueRouting.path j).before_iff_vertexIndex_le).2
      ⟨hw, hx, ?_⟩
    omega
  by_cases hwx : w = x
  · have hbluePack :
        s(x, z) ∈ M.good.blueRouting.toPathPacking.edgeSet := by
      have hbluePack' :
          s(z, w) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
        (M.good.blueRouting.toPathPacking.mem_edgeSet).2 ⟨j, hblueEdge⟩
      simpa [hwx, Sym2.eq_swap] using hbluePack'
    exact M.false_of_red_and_blue_edge hdeg hdisj hredPack hbluePack
  · exact
      PathSlicing.false_of_shortcut_edge_of_edgeSet_unique
        (R := M.good.blueRouting)
        (fun B' => M.blueRouting_edgeSet_eq_selected hdeg hdisj B')
        hzwBefore hw_before_x hzw_ne hwx (H.symm hredAdj)

omit [Fintype V] in
/-- In a minimal good minor, every red step followed by a blue step induces a
dependency edge for the red routing.  The same-row backward case is excluded
by the shortcut/rerouting argument. -/
theorem red_then_blue_linkageDependency
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x y z : W} {i i' : M.good.redRouting.Index}
    (hredEdge : s(x, y) ∈ (M.good.redRouting.path i).edgeSet)
    (hredBefore : (M.good.redRouting.path i).Before x y)
    (hxy_ne : x ≠ y)
    (hblue :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.blue y z)
    (hzRed : z ∈ (M.good.redRouting.path i').vertexSet) :
    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
      M.good.redRouting x z := by
  classical
  rcases hblue with ⟨j, hblueEdge, hblueBefore, hyz_ne⟩
  have hblueColor :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.blue y z :=
    ⟨j, hblueEdge, hblueBefore, hyz_ne⟩
  by_cases hrow : i = i'
  · subst i'
    have hxRed : x ∈ (M.good.redRouting.path i).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        (M.good.redRouting.path i) hredEdge).1
    by_cases hxz : x = z
    · have hredPack :
          s(x, y) ∈ M.good.redRouting.toPathPacking.edgeSet :=
        (M.good.redRouting.toPathPacking.mem_edgeSet).2 ⟨i, hredEdge⟩
      have hbluePack :
          s(x, y) ∈ M.good.blueRouting.toPathPacking.edgeSet := by
        have hbluePack' :
            s(y, z) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
          (M.good.blueRouting.toPathPacking.mem_edgeSet).2
            ⟨j, hblueEdge⟩
        simpa [hxz, Sym2.eq_swap] using hbluePack'
      exact False.elim
        (M.false_of_red_and_blue_edge hdeg hdisj hredPack hbluePack)
    · rcases GraphPath.before_total_of_mem
        (M.good.redRouting.path i) hxRed hzRed with hxzBefore | hzxBefore
      · exact
          TwoPairColorEdge.red_then_blue_linkageDependency_of_target_red_after
            (P := M.good.redRouting)
            hredEdge hredBefore hxy_ne hzRed hxzBefore hxz
      · have hblueAdj : H.Adj y z :=
          GraphPath.edgeSet_subset_edgeSet
            (M.good.blueRouting.path j) hblueEdge
        exact False.elim
          (PathSlicing.false_of_shortcut_edge_of_edgeSet_unique
            (R := M.good.redRouting)
            (fun R' => M.redRouting_edgeSet_eq_selected hdeg hdisj R')
            hzxBefore hredBefore (fun hzx => hxz hzx.symm) hxy_ne
            (H.symm hblueAdj))
  · exact
      TwoPairColorEdge.red_then_blue_linkageDependency_of_target_red_row_ne
        (P := M.good.redRouting) (Q := M.good.blueRouting)
        hredEdge hredBefore hxy_ne hblueColor hzRed hrow

omit [Fintype V] in
/-- Blue analogue of `red_then_blue_linkageDependency`. -/
theorem blue_then_red_linkageDependency
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x y z : W} {j j' : M.good.blueRouting.Index}
    (hblueEdge : s(x, y) ∈ (M.good.blueRouting.path j).edgeSet)
    (hblueBefore : (M.good.blueRouting.path j).Before x y)
    (hxy_ne : x ≠ y)
    (hred :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.red y z)
    (hzBlue : z ∈ (M.good.blueRouting.path j').vertexSet) :
    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
      M.good.blueRouting x z := by
  classical
  rcases hred with ⟨i, hredEdge, hredBefore, hyz_ne⟩
  have hredColor :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.red y z :=
    ⟨i, hredEdge, hredBefore, hyz_ne⟩
  by_cases hrow : j = j'
  · subst j'
    have hxBlue : x ∈ (M.good.blueRouting.path j).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        (M.good.blueRouting.path j) hblueEdge).1
    by_cases hxz : x = z
    · have hbluePack :
          s(x, y) ∈ M.good.blueRouting.toPathPacking.edgeSet :=
        (M.good.blueRouting.toPathPacking.mem_edgeSet).2 ⟨j, hblueEdge⟩
      have hredPack :
          s(x, y) ∈ M.good.redRouting.toPathPacking.edgeSet := by
        have hredPack' :
            s(y, z) ∈ M.good.redRouting.toPathPacking.edgeSet :=
          (M.good.redRouting.toPathPacking.mem_edgeSet).2
            ⟨i, hredEdge⟩
        simpa [hxz, Sym2.eq_swap] using hredPack'
      exact False.elim
        (M.false_of_red_and_blue_edge hdeg hdisj hredPack hbluePack)
    · rcases GraphPath.before_total_of_mem
        (M.good.blueRouting.path j) hxBlue hzBlue with hxzBefore | hzxBefore
      · exact
          TwoPairColorEdge.blue_then_red_linkageDependency_of_target_blue_after
            (Q := M.good.blueRouting)
            hblueEdge hblueBefore hxy_ne hzBlue hxzBefore hxz
      · have hredAdj : H.Adj y z :=
          GraphPath.edgeSet_subset_edgeSet
            (M.good.redRouting.path i) hredEdge
        exact False.elim
          (PathSlicing.false_of_shortcut_edge_of_edgeSet_unique
            (R := M.good.blueRouting)
            (fun B' => M.blueRouting_edgeSet_eq_selected hdeg hdisj B')
            hzxBefore hblueBefore (fun hzx => hxz hzx.symm) hxy_ne
            (H.symm hredAdj))
  · exact
      TwoPairColorEdge.blue_then_red_linkageDependency_of_target_blue_row_ne
        (P := M.good.redRouting) (Q := M.good.blueRouting)
        hblueEdge hblueBefore hxy_ne hredColor hzBlue hrow

omit [Fintype V] in
/-- The red dependency rank strictly increases across every red-then-blue
two-step alternating move. -/
theorem redDependencyRank_lt_of_red_then_blue
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x y z : W} {i i' : M.good.redRouting.Index}
    (hredEdge : s(x, y) ∈ (M.good.redRouting.path i).edgeSet)
    (hredBefore : (M.good.redRouting.path i).Before x y)
    (hxy_ne : x ≠ y)
    (hblue :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.blue y z)
    (hzRed : z ∈ (M.good.redRouting.path i').vertexSet) :
    (M.redDependencyRank hdeg hdisj).rank x <
      (M.redDependencyRank hdeg hdisj).rank z :=
  (M.redDependencyRank hdeg hdisj).rel_lt
    (M.red_then_blue_linkageDependency hdeg hdisj
      hredEdge hredBefore hxy_ne hblue hzRed)

omit [Fintype V] in
/-- The blue dependency rank strictly increases across every blue-then-red
two-step alternating move. -/
theorem blueDependencyRank_lt_of_blue_then_red
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x y z : W} {j j' : M.good.blueRouting.Index}
    (hblueEdge : s(x, y) ∈ (M.good.blueRouting.path j).edgeSet)
    (hblueBefore : (M.good.blueRouting.path j).Before x y)
    (hxy_ne : x ≠ y)
    (hred :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting
        TwoPairColor.red y z)
    (hzBlue : z ∈ (M.good.blueRouting.path j').vertexSet) :
    (M.blueDependencyRank hdeg hdisj).rank x <
      (M.blueDependencyRank hdeg hdisj).rank z :=
  (M.blueDependencyRank hdeg hdisj).rel_lt
    (M.blue_then_red_linkageDependency hdeg hdisj
      hblueEdge hblueBefore hxy_ne hred hzBlue)

/-- A two-step alternating move that starts with a red edge and then follows a
blue edge, landing again on a red routing path. -/
def RedBlueTwoStep
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (x z : W) : Prop :=
  ∃ y : W, ∃ i i' : M.good.redRouting.Index,
    s(x, y) ∈ (M.good.redRouting.path i).edgeSet ∧
      (M.good.redRouting.path i).Before x y ∧
        x ≠ y ∧
          TwoPairColorEdge M.good.redRouting M.good.blueRouting
            TwoPairColor.blue y z ∧
            z ∈ (M.good.redRouting.path i').vertexSet

/-- A two-step alternating move that starts with a blue edge and then follows a
red edge, landing again on a blue routing path. -/
def BlueRedTwoStep
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (x z : W) : Prop :=
  ∃ y : W, ∃ j j' : M.good.blueRouting.Index,
    s(x, y) ∈ (M.good.blueRouting.path j).edgeSet ∧
      (M.good.blueRouting.path j).Before x y ∧
        x ≠ y ∧
          TwoPairColorEdge M.good.redRouting M.good.blueRouting
            TwoPairColor.red y z ∧
            z ∈ (M.good.blueRouting.path j').vertexSet

omit [Fintype V] in
/-- Two consecutive alternating-chain state steps, starting with red, give the
red-blue two-step relation used in the dependency-rank argument whenever the
landing vertex lies on a red routing path. -/
theorem redBlueTwoStep_of_altStep_pair
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x y z : W}
    (hxy :
      TwoPairAltStep M.good.redRouting M.good.blueRouting
        (x, TwoPairColor.red) (y, TwoPairColor.blue))
    (hyz :
      TwoPairAltStep M.good.redRouting M.good.blueRouting
        (y, TwoPairColor.blue) (z, TwoPairColor.red))
    (hzRed :
      ∃ i' : M.good.redRouting.Index,
        z ∈ (M.good.redRouting.path i').vertexSet) :
    M.RedBlueTwoStep x z := by
  rcases hxy with ⟨hred, _⟩
  rcases hyz with ⟨hblue, _⟩
  rcases hred with ⟨i, hredEdge, hredBefore, hxy_ne⟩
  rcases hzRed with ⟨i', hzRed⟩
  exact ⟨y, i, i', hredEdge, hredBefore, hxy_ne, hblue, hzRed⟩

omit [Fintype V] in
/-- Blue-starting analogue of `redBlueTwoStep_of_altStep_pair`. -/
theorem blueRedTwoStep_of_altStep_pair
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x y z : W}
    (hxy :
      TwoPairAltStep M.good.redRouting M.good.blueRouting
        (x, TwoPairColor.blue) (y, TwoPairColor.red))
    (hyz :
      TwoPairAltStep M.good.redRouting M.good.blueRouting
        (y, TwoPairColor.red) (z, TwoPairColor.blue))
    (hzBlue :
      ∃ j' : M.good.blueRouting.Index,
        z ∈ (M.good.blueRouting.path j').vertexSet) :
    M.BlueRedTwoStep x z := by
  rcases hxy with ⟨hblue, _⟩
  rcases hyz with ⟨hred, _⟩
  rcases hblue with ⟨j, hblueEdge, hblueBefore, hxy_ne⟩
  rcases hzBlue with ⟨j', hzBlue⟩
  exact ⟨y, j, j', hblueEdge, hblueBefore, hxy_ne, hred, hzBlue⟩

omit [Fintype V] in
/-- The source of a red-blue two-step move lies on a red path. -/
theorem red_mem_of_redBlueTwoStep_source
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x z : W} (hxz : M.RedBlueTwoStep x z) :
    ∃ i : M.good.redRouting.Index,
      x ∈ (M.good.redRouting.path i).vertexSet := by
  rcases hxz with
    ⟨_y, i, _i', hredEdge, _hredBefore, _hxy_ne, _hblue, _hzRed⟩
  exact ⟨i,
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.good.redRouting.path i) hredEdge).1⟩

omit [Fintype V] in
/-- The source of a blue-red two-step move lies on a blue path. -/
theorem blue_mem_of_blueRedTwoStep_source
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x z : W} (hxz : M.BlueRedTwoStep x z) :
    ∃ j : M.good.blueRouting.Index,
      x ∈ (M.good.blueRouting.path j).vertexSet := by
  rcases hxz with
    ⟨_y, j, _j', hblueEdge, _hblueBefore, _hxy_ne, _hred, _hzBlue⟩
  exact ⟨j,
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (M.good.blueRouting.path j) hblueEdge).1⟩

omit [Fintype V] in
/-- If a red-blue two-step walk ends on a red path, then its source also lies
on a red path. -/
theorem red_mem_of_redBlueTwoStep_reflTransGen_source
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x z : W}
    (hzRed :
      ∃ i : M.good.redRouting.Index,
        z ∈ (M.good.redRouting.path i).vertexSet)
    (hxz : Relation.ReflTransGen M.RedBlueTwoStep x z) :
    ∃ i : M.good.redRouting.Index,
      x ∈ (M.good.redRouting.path i).vertexSet := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxz with hEq | htr
  · subst z
    exact hzRed
  · rcases Relation.TransGen.head'_iff.1 htr with ⟨y, hxy, _hyz⟩
    exact M.red_mem_of_redBlueTwoStep_source hxy

omit [Fintype V] in
/-- If a blue-red two-step walk ends on a blue path, then its source also lies
on a blue path. -/
theorem blue_mem_of_blueRedTwoStep_reflTransGen_source
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x z : W}
    (hzBlue :
      ∃ j : M.good.blueRouting.Index,
        z ∈ (M.good.blueRouting.path j).vertexSet)
    (hxz : Relation.ReflTransGen M.BlueRedTwoStep x z) :
    ∃ j : M.good.blueRouting.Index,
      x ∈ (M.good.blueRouting.path j).vertexSet := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxz with hEq | htr
  · subst z
    exact hzBlue
  · rcases Relation.TransGen.head'_iff.1 htr with ⟨y, hxy, _hyz⟩
    exact M.blue_mem_of_blueRedTwoStep_source hxy

omit [Fintype V] in
/-- Alternating reachability from a red state to a red state is exactly
red-blue two-step reachability after grouping consecutive pairs of edges. -/
theorem redBlueTwoStep_reflTransGen_of_altStep_red_to_red
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x z : W}
    (hzRed :
      ∃ i : M.good.redRouting.Index,
        z ∈ (M.good.redRouting.path i).vertexSet)
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (z, TwoPairColor.red)) :
    Relation.ReflTransGen M.RedBlueTwoStep x z := by
  classical
  let Good : TwoPairAltState W → Prop := fun st =>
    match st.2 with
    | TwoPairColor.red =>
        Relation.ReflTransGen M.RedBlueTwoStep st.1 z
    | TwoPairColor.blue =>
        ∃ w : W,
          TwoPairAltStep M.good.redRouting M.good.blueRouting
            st (w, TwoPairColor.red) ∧
          (∃ i : M.good.redRouting.Index,
            w ∈ (M.good.redRouting.path i).vertexSet) ∧
          Relation.ReflTransGen M.RedBlueTwoStep w z
  have hgood : Good (x, TwoPairColor.red) := by
    refine Relation.ReflTransGen.head_induction_on hxz ?_ ?_
    · exact Relation.ReflTransGen.refl
    · intro a c hac hcz ih
      rcases a with ⟨aV, aC⟩
      rcases c with ⟨cV, cC⟩
      have hac0 :
          TwoPairAltStep M.good.redRouting M.good.blueRouting
            (aV, aC) (cV, cC) := hac
      rcases hac with ⟨hEdge, hcC⟩
      cases aC with
      | red =>
          have hcBlue : cC = TwoPairColor.blue := by
            simpa using hcC
          subst cC
          rcases ih with ⟨w, hcw, hwRed, hwz⟩
          have hstep :
              M.RedBlueTwoStep aV w :=
            M.redBlueTwoStep_of_altStep_pair (by simpa using hac0) hcw hwRed
          exact Relation.ReflTransGen.head hstep hwz
      | blue =>
          have hcRed : cC = TwoPairColor.red := by
            simpa using hcC
          subst cC
          have hczRB :
              Relation.ReflTransGen M.RedBlueTwoStep cV z := by
            simpa [Good] using ih
          have hcRedMem :
              ∃ i : M.good.redRouting.Index,
                cV ∈ (M.good.redRouting.path i).vertexSet :=
            M.red_mem_of_redBlueTwoStep_reflTransGen_source hzRed hczRB
          exact ⟨cV, by simpa using hac0, hcRedMem, hczRB⟩
  simpa [Good] using hgood

omit [Fintype V] in
/-- Blue analogue of
`redBlueTwoStep_reflTransGen_of_altStep_red_to_red`. -/
theorem blueRedTwoStep_reflTransGen_of_altStep_blue_to_blue
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x z : W}
    (hzBlue :
      ∃ j : M.good.blueRouting.Index,
        z ∈ (M.good.blueRouting.path j).vertexSet)
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (z, TwoPairColor.blue)) :
    Relation.ReflTransGen M.BlueRedTwoStep x z := by
  classical
  let Good : TwoPairAltState W → Prop := fun st =>
    match st.2 with
    | TwoPairColor.blue =>
        Relation.ReflTransGen M.BlueRedTwoStep st.1 z
    | TwoPairColor.red =>
        ∃ w : W,
          TwoPairAltStep M.good.redRouting M.good.blueRouting
            st (w, TwoPairColor.blue) ∧
          (∃ j : M.good.blueRouting.Index,
            w ∈ (M.good.blueRouting.path j).vertexSet) ∧
          Relation.ReflTransGen M.BlueRedTwoStep w z
  have hgood : Good (x, TwoPairColor.blue) := by
    refine Relation.ReflTransGen.head_induction_on hxz ?_ ?_
    · exact Relation.ReflTransGen.refl
    · intro a c hac hcz ih
      rcases a with ⟨aV, aC⟩
      rcases c with ⟨cV, cC⟩
      have hac0 :
          TwoPairAltStep M.good.redRouting M.good.blueRouting
            (aV, aC) (cV, cC) := hac
      rcases hac with ⟨hEdge, hcC⟩
      cases aC with
      | red =>
          have hcBlue : cC = TwoPairColor.blue := by
            simpa using hcC
          subst cC
          have hczBR :
              Relation.ReflTransGen M.BlueRedTwoStep cV z := by
            simpa [Good] using ih
          have hcBlueMem :
              ∃ j : M.good.blueRouting.Index,
                cV ∈ (M.good.blueRouting.path j).vertexSet :=
            M.blue_mem_of_blueRedTwoStep_reflTransGen_source hzBlue hczBR
          exact ⟨cV, by simpa using hac0, hcBlueMem, hczBR⟩
      | blue =>
          have hcRed : cC = TwoPairColor.red := by
            simpa using hcC
          subst cC
          rcases ih with ⟨w, hcw, hwBlue, hwz⟩
          have hstep :
              M.BlueRedTwoStep aV w :=
            M.blueRedTwoStep_of_altStep_pair (by simpa using hac0) hcw hwBlue
          exact Relation.ReflTransGen.head hstep hwz
  simpa [Good] using hgood

omit [Fintype V] in
/-- Red-blue two-step moves strictly increase the red dependency rank. -/
theorem redDependencyRank_lt_of_redBlueTwoStep
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} (hxz : M.RedBlueTwoStep x z) :
    (M.redDependencyRank hdeg hdisj).rank x <
      (M.redDependencyRank hdeg hdisj).rank z := by
  rcases hxz with
    ⟨y, i, i', hredEdge, hredBefore, hxy_ne, hblue, hzRed⟩
  exact M.redDependencyRank_lt_of_red_then_blue hdeg hdisj
    hredEdge hredBefore hxy_ne hblue hzRed

omit [Fintype V] in
/-- Blue-red two-step moves strictly increase the blue dependency rank. -/
theorem blueDependencyRank_lt_of_blueRedTwoStep
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} (hxz : M.BlueRedTwoStep x z) :
    (M.blueDependencyRank hdeg hdisj).rank x <
      (M.blueDependencyRank hdeg hdisj).rank z := by
  rcases hxz with
    ⟨y, j, j', hblueEdge, hblueBefore, hxy_ne, hred, hzBlue⟩
  exact M.blueDependencyRank_lt_of_blue_then_red hdeg hdisj
    hblueEdge hblueBefore hxy_ne hred hzBlue

omit [Fintype V] in
/-- A red-blue two-step move is a dependency edge for the selected red
routing. -/
theorem red_linkageDependency_of_redBlueTwoStep
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} (hxz : M.RedBlueTwoStep x z) :
    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
      M.good.redRouting x z := by
  rcases hxz with
    ⟨y, i, i', hredEdge, hredBefore, hxy_ne, hblue, hzRed⟩
  exact M.red_then_blue_linkageDependency hdeg hdisj
    hredEdge hredBefore hxy_ne hblue hzRed

omit [Fintype V] in
/-- A blue-red two-step move is a dependency edge for the selected blue
routing. -/
theorem blue_linkageDependency_of_blueRedTwoStep
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} (hxz : M.BlueRedTwoStep x z) :
    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
      M.good.blueRouting x z := by
  rcases hxz with
    ⟨y, j, j', hblueEdge, hblueBefore, hxy_ne, hred, hzBlue⟩
  exact M.blue_then_red_linkageDependency hdeg hdisj
    hblueEdge hblueBefore hxy_ne hred hzBlue

omit [Fintype V] in
/-- Red-blue two-step reachability respects the order of any red path on
which its endpoints both lie.  This is the reachability form of the red half
of Claim 2.6 for the two-step relation. -/
theorem red_order_of_redBlueTwoStep_reflTransGen_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {i : M.good.redRouting.Index}
    (hxz : Relation.ReflTransGen M.RedBlueTwoStep x z)
    (hx : x ∈ (M.good.redRouting.path i).vertexSet)
    (hz : z ∈ (M.good.redRouting.path i).vertexSet) :
    (M.good.redRouting.path i).Before x z := by
  classical
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxz with hzx | htr
  · subst z
    exact (M.good.redRouting.path i).before_refl hx
  · have hdep :
        Relation.TransGen
          (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
            M.good.redRouting) x z :=
      Relation.TransGen.mono
        (fun a b hab =>
          M.red_linkageDependency_of_redBlueTwoStep hdeg hdisj hab) htr
    rcases GraphPath.before_total_of_mem (M.good.redRouting.path i) hx hz with
      hxzBefore | hzxBefore
    · exact hxzBefore
    · by_cases hxzeq : x = z
      · subst z
        exact (M.good.redRouting.path i).before_refl hx
      · have hzx_ne : z ≠ x := fun h => hxzeq h.symm
        have hcycle :
            Relation.TransGen
              (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                M.good.redRouting) z z :=
          Lax17Proofs.SimpleGraph.PathSlicing.transGen_linkageDependency_of_before
            hzxBefore hzx_ne hdep
        exact False.elim ((M.red_linkageDependency_acyclic hdeg hdisj) z hcycle)

omit [Fintype V] in
/-- Blue-red two-step reachability respects the order of any blue path on
which its endpoints both lie. -/
theorem blue_order_of_blueRedTwoStep_reflTransGen_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {j : M.good.blueRouting.Index}
    (hxz : Relation.ReflTransGen M.BlueRedTwoStep x z)
    (hx : x ∈ (M.good.blueRouting.path j).vertexSet)
    (hz : z ∈ (M.good.blueRouting.path j).vertexSet) :
    (M.good.blueRouting.path j).Before x z := by
  classical
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxz with hzx | htr
  · subst z
    exact (M.good.blueRouting.path j).before_refl hx
  · have hdep :
        Relation.TransGen
          (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
            M.good.blueRouting) x z :=
      Relation.TransGen.mono
        (fun a b hab =>
          M.blue_linkageDependency_of_blueRedTwoStep hdeg hdisj hab) htr
    rcases GraphPath.before_total_of_mem (M.good.blueRouting.path j) hx hz with
      hxzBefore | hzxBefore
    · exact hxzBefore
    · by_cases hxzeq : x = z
      · subst z
        exact (M.good.blueRouting.path j).before_refl hx
      · have hzx_ne : z ≠ x := fun h => hxzeq h.symm
        have hcycle :
            Relation.TransGen
              (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                M.good.blueRouting) z z :=
          Lax17Proofs.SimpleGraph.PathSlicing.transGen_linkageDependency_of_before
            hzxBefore hzx_ne hdep
        exact False.elim ((M.blue_linkageDependency_acyclic hdeg hdisj) z hcycle)

omit [Fintype V] in
/-- Alternating reachability from a red state to a red state respects every
red path containing the two endpoint vertices. -/
theorem red_order_of_altStep_red_to_red_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {i : M.good.redRouting.Index}
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (z, TwoPairColor.red))
    (hx : x ∈ (M.good.redRouting.path i).vertexSet)
    (hz : z ∈ (M.good.redRouting.path i).vertexSet) :
    (M.good.redRouting.path i).Before x z := by
  have htwo :
      Relation.ReflTransGen M.RedBlueTwoStep x z :=
    M.redBlueTwoStep_reflTransGen_of_altStep_red_to_red ⟨i, hz⟩ hxz
  exact M.red_order_of_redBlueTwoStep_reflTransGen_same_path
    hdeg hdisj htwo hx hz

omit [Fintype V] in
/-- Alternating reachability from a blue state to a blue state respects every
blue path containing the two endpoint vertices. -/
theorem blue_order_of_altStep_blue_to_blue_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {j : M.good.blueRouting.Index}
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (z, TwoPairColor.blue))
    (hx : x ∈ (M.good.blueRouting.path j).vertexSet)
    (hz : z ∈ (M.good.blueRouting.path j).vertexSet) :
    (M.good.blueRouting.path j).Before x z := by
  have htwo :
      Relation.ReflTransGen M.BlueRedTwoStep x z :=
    M.blueRedTwoStep_reflTransGen_of_altStep_blue_to_blue ⟨j, hz⟩ hxz
  exact M.blue_order_of_blueRedTwoStep_reflTransGen_same_path
    hdeg hdisj htwo hx hz

omit [Fintype V] in
/-- Alternating reachability from a red state to a blue state respects every
red path containing the endpoint vertices.  This is the odd-length parity case
obtained by splitting off the final red edge and applying the red-to-red
two-step order lemma to the prefix. -/
theorem red_order_of_altStep_red_to_blue_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {i : M.good.redRouting.Index}
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (z, TwoPairColor.blue))
    (hx : x ∈ (M.good.redRouting.path i).vertexSet)
    (hz : z ∈ (M.good.redRouting.path i).vertexSet) :
    (M.good.redRouting.path i).Before x z := by
  classical
  rcases Relation.ReflTransGen.cases_tail hxz with hEq | htail
  · cases hEq
  · rcases htail with ⟨st, hxst, hstz⟩
    rcases st with ⟨w, cw⟩
    rcases hstz with ⟨hcolor, hswap⟩
    cases cw with
    | red =>
        rcases hcolor with ⟨i', hredEdge, hredBefore, _hwz_ne⟩
        have hz_i' : z ∈ (M.good.redRouting.path i').vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.redRouting.path i') hredEdge).2
        have hi' : i' = i := by
          by_contra hne
          exact Finset.disjoint_left.mp
            (M.good.redRouting.toPathPacking.node_disjoint hne)
            hz_i' hz
        subst i'
        have hw : w ∈ (M.good.redRouting.path i).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.redRouting.path i) hredEdge).1
        have hxw :
            (M.good.redRouting.path i).Before x w :=
          M.red_order_of_altStep_red_to_red_same_path hdeg hdisj
            hxst hx hw
        exact (M.good.redRouting.path i).before_trans hxw hredBefore
    | blue =>
        simp at hswap

omit [Fintype V] in
/-- Blue analogue of `red_order_of_altStep_red_to_blue_same_path`. -/
theorem blue_order_of_altStep_blue_to_red_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {j : M.good.blueRouting.Index}
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (z, TwoPairColor.red))
    (hx : x ∈ (M.good.blueRouting.path j).vertexSet)
    (hz : z ∈ (M.good.blueRouting.path j).vertexSet) :
    (M.good.blueRouting.path j).Before x z := by
  classical
  rcases Relation.ReflTransGen.cases_tail hxz with hEq | htail
  · cases hEq
  · rcases htail with ⟨st, hxst, hstz⟩
    rcases st with ⟨w, cw⟩
    rcases hstz with ⟨hcolor, hswap⟩
    cases cw with
    | red =>
        simp at hswap
    | blue =>
        rcases hcolor with ⟨j', hblueEdge, hblueBefore, _hwz_ne⟩
        have hz_j' : z ∈ (M.good.blueRouting.path j').vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.blueRouting.path j') hblueEdge).2
        have hj' : j' = j := by
          by_contra hne
          exact Finset.disjoint_left.mp
            (M.good.blueRouting.toPathPacking.node_disjoint hne)
            hz_j' hz
        subst j'
        have hw : w ∈ (M.good.blueRouting.path j).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.blueRouting.path j) hblueEdge).1
        have hxw :
            (M.good.blueRouting.path j).Before x w :=
          M.blue_order_of_altStep_blue_to_blue_same_path hdeg hdisj
            hxst hx hw
        exact (M.good.blueRouting.path j).before_trans hxw hblueBefore

omit [Fintype V] in
/-- Alternating reachability from a red state to a red state gives
reachability in the red linkage-dependency digraph. -/
theorem red_linkageDependency_reflTransGen_of_altStep_red_to_red
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W}
    (hzRed :
      ∃ i : M.good.redRouting.Index,
        z ∈ (M.good.redRouting.path i).vertexSet)
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (z, TwoPairColor.red)) :
    Relation.ReflTransGen
      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
        M.good.redRouting) x z := by
  have htwo :
      Relation.ReflTransGen M.RedBlueTwoStep x z :=
    M.redBlueTwoStep_reflTransGen_of_altStep_red_to_red hzRed hxz
  exact Relation.ReflTransGen.mono
    (fun a b hab =>
      M.red_linkageDependency_of_redBlueTwoStep hdeg hdisj hab) htwo

omit [Fintype V] in
/-- Alternating reachability from a red state to a blue state gives
reachability in the red linkage-dependency digraph, provided the endpoint lies
on a red routing path. -/
theorem red_linkageDependency_reflTransGen_of_altStep_red_to_blue
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W}
    (hzRed :
      ∃ i : M.good.redRouting.Index,
        z ∈ (M.good.redRouting.path i).vertexSet)
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (z, TwoPairColor.blue)) :
    Relation.ReflTransGen
      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
        M.good.redRouting) x z := by
  classical
  rcases Relation.ReflTransGen.cases_tail hxz with hEq | htail
  · cases hEq
  · rcases htail with ⟨st, hxst, hstz⟩
    rcases st with ⟨w, cw⟩
    rcases hstz with ⟨hcolor, hswap⟩
    cases cw with
    | red =>
        rcases hcolor with ⟨i, hredEdge, hredBefore, hwz_ne⟩
        have hwRed :
            ∃ i : M.good.redRouting.Index,
              w ∈ (M.good.redRouting.path i).vertexSet :=
          ⟨i,
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.redRouting.path i) hredEdge).1⟩
        have hz_i : z ∈ (M.good.redRouting.path i).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.redRouting.path i) hredEdge).2
        have hprefix :
            Relation.ReflTransGen
              (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                M.good.redRouting) x w :=
          M.red_linkageDependency_reflTransGen_of_altStep_red_to_red
            hdeg hdisj hwRed hxst
        have hlast :
            Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
              M.good.redRouting w z :=
          Or.inl ⟨i,
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.redRouting.path i) hredEdge).1,
            hz_i, hredBefore, hwz_ne⟩
        exact hprefix.trans (Relation.ReflTransGen.single hlast)
    | blue =>
        simp at hswap

omit [Fintype V] in
/-- Transitive, nonempty form of
`red_linkageDependency_reflTransGen_of_altStep_red_to_blue`. -/
theorem red_linkageDependency_transGen_of_altStep_red_to_blue
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W}
    (hzRed :
      ∃ i : M.good.redRouting.Index,
        z ∈ (M.good.redRouting.path i).vertexSet)
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (z, TwoPairColor.blue)) :
    Relation.TransGen
      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
        M.good.redRouting) x z := by
  classical
  rcases Relation.ReflTransGen.cases_tail hxz with hEq | htail
  · cases hEq
  · rcases htail with ⟨st, hxst, hstz⟩
    rcases st with ⟨w, cw⟩
    rcases hstz with ⟨hcolor, hswap⟩
    cases cw with
    | red =>
        rcases hcolor with ⟨i, hredEdge, hredBefore, hwz_ne⟩
        have hwRed :
            ∃ i : M.good.redRouting.Index,
              w ∈ (M.good.redRouting.path i).vertexSet :=
          ⟨i,
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.redRouting.path i) hredEdge).1⟩
        have hz_i : z ∈ (M.good.redRouting.path i).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.redRouting.path i) hredEdge).2
        have hprefix :
            Relation.ReflTransGen
              (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                M.good.redRouting) x w :=
          M.red_linkageDependency_reflTransGen_of_altStep_red_to_red
            hdeg hdisj hwRed hxst
        have hlast :
            Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
              M.good.redRouting w z :=
          Or.inl ⟨i,
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.redRouting.path i) hredEdge).1,
            hz_i, hredBefore, hwz_ne⟩
        exact Relation.TransGen.tail' hprefix hlast
    | blue =>
        simp at hswap

omit [Fintype V] in
/-- Blue analogue of
`red_linkageDependency_reflTransGen_of_altStep_red_to_red`. -/
theorem blue_linkageDependency_reflTransGen_of_altStep_blue_to_blue
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W}
    (hzBlue :
      ∃ j : M.good.blueRouting.Index,
        z ∈ (M.good.blueRouting.path j).vertexSet)
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (z, TwoPairColor.blue)) :
    Relation.ReflTransGen
      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
        M.good.blueRouting) x z := by
  have htwo :
      Relation.ReflTransGen M.BlueRedTwoStep x z :=
    M.blueRedTwoStep_reflTransGen_of_altStep_blue_to_blue hzBlue hxz
  exact Relation.ReflTransGen.mono
    (fun a b hab =>
      M.blue_linkageDependency_of_blueRedTwoStep hdeg hdisj hab) htwo

omit [Fintype V] in
/-- Blue analogue of
`red_linkageDependency_reflTransGen_of_altStep_red_to_blue`. -/
theorem blue_linkageDependency_reflTransGen_of_altStep_blue_to_red
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W}
    (hzBlue :
      ∃ j : M.good.blueRouting.Index,
        z ∈ (M.good.blueRouting.path j).vertexSet)
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (z, TwoPairColor.red)) :
    Relation.ReflTransGen
      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
        M.good.blueRouting) x z := by
  classical
  rcases Relation.ReflTransGen.cases_tail hxz with hEq | htail
  · cases hEq
  · rcases htail with ⟨st, hxst, hstz⟩
    rcases st with ⟨w, cw⟩
    rcases hstz with ⟨hcolor, hswap⟩
    cases cw with
    | red =>
        simp at hswap
    | blue =>
        rcases hcolor with ⟨j, hblueEdge, hblueBefore, hwz_ne⟩
        have hwBlue :
            ∃ j : M.good.blueRouting.Index,
              w ∈ (M.good.blueRouting.path j).vertexSet :=
          ⟨j,
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.blueRouting.path j) hblueEdge).1⟩
        have hz_j : z ∈ (M.good.blueRouting.path j).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.blueRouting.path j) hblueEdge).2
        have hprefix :
            Relation.ReflTransGen
              (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                M.good.blueRouting) x w :=
          M.blue_linkageDependency_reflTransGen_of_altStep_blue_to_blue
            hdeg hdisj hwBlue hxst
        have hlast :
            Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
              M.good.blueRouting w z :=
          Or.inl ⟨j,
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.blueRouting.path j) hblueEdge).1,
            hz_j, hblueBefore, hwz_ne⟩
        exact hprefix.trans (Relation.ReflTransGen.single hlast)

omit [Fintype V] in
/-- Transitive, nonempty form of
`blue_linkageDependency_reflTransGen_of_altStep_blue_to_red`. -/
theorem blue_linkageDependency_transGen_of_altStep_blue_to_red
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W}
    (hzBlue :
      ∃ j : M.good.blueRouting.Index,
        z ∈ (M.good.blueRouting.path j).vertexSet)
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (z, TwoPairColor.red)) :
    Relation.TransGen
      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
        M.good.blueRouting) x z := by
  classical
  rcases Relation.ReflTransGen.cases_tail hxz with hEq | htail
  · cases hEq
  · rcases htail with ⟨st, hxst, hstz⟩
    rcases st with ⟨w, cw⟩
    rcases hstz with ⟨hcolor, hswap⟩
    cases cw with
    | red =>
        simp at hswap
    | blue =>
        rcases hcolor with ⟨j, hblueEdge, hblueBefore, hwz_ne⟩
        have hwBlue :
            ∃ j : M.good.blueRouting.Index,
              w ∈ (M.good.blueRouting.path j).vertexSet :=
          ⟨j,
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.blueRouting.path j) hblueEdge).1⟩
        have hz_j : z ∈ (M.good.blueRouting.path j).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.blueRouting.path j) hblueEdge).2
        have hprefix :
            Relation.ReflTransGen
              (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                M.good.blueRouting) x w :=
          M.blue_linkageDependency_reflTransGen_of_altStep_blue_to_blue
            hdeg hdisj hwBlue hxst
        have hlast :
            Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
              M.good.blueRouting w z :=
          Or.inl ⟨j,
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (M.good.blueRouting.path j) hblueEdge).1,
            hz_j, hblueBefore, hwz_ne⟩
        exact Relation.TransGen.tail' hprefix hlast

omit [Fintype V] in
/-- Alternating reachability from a blue state to a blue state respects every
red path containing the endpoint vertices.  This is the first mixed-color
case of Claim 2.6. -/
theorem red_order_of_altStep_blue_to_blue_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {i : M.good.redRouting.Index}
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (z, TwoPairColor.blue))
    (hx : x ∈ (M.good.redRouting.path i).vertexSet)
    (hz : z ∈ (M.good.redRouting.path i).vertexSet) :
    (M.good.redRouting.path i).Before x z := by
  classical
  rcases GraphPath.before_total_of_mem
      (M.good.redRouting.path i) hx hz with hxzBefore | hzxBefore
  · exact hxzBefore
  · by_cases hxzeq : x = z
    · subst z
      exact (M.good.redRouting.path i).before_refl hx
    · exfalso
      have hzx_ne : z ≠ x := fun h => hxzeq h.symm
      rcases Relation.ReflTransGen.cases_head hxz with hEq | hhead
      · exact hxzeq (congrArg Prod.fst hEq)
      · rcases hhead with ⟨st, hxst, hstz⟩
        rcases st with ⟨a, ca⟩
        rcases hxst with ⟨hblueStep, hswap⟩
        cases ca with
        | red =>
            rcases hblueStep with ⟨j, hblueEdge, _hblueBefore, hxa_ne⟩
            have hxaAdj : H.Adj x a :=
              GraphPath.edgeSet_subset_edgeSet
                (M.good.blueRouting.path j) hblueEdge
            have hdepRest :
                Relation.TransGen
                  (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                    M.good.redRouting) a z :=
              M.red_linkageDependency_transGen_of_altStep_red_to_blue
                hdeg hdisj ⟨i, hz⟩ hstz
            have haRed :
                ∃ ia : M.good.redRouting.Index,
                  a ∈ (M.good.redRouting.path ia).vertexSet := by
              rcases Relation.ReflTransGen.cases_head hstz with hRestEq | hRestHead
              · cases hRestEq
              · rcases hRestHead with ⟨st₂, hast₂, _hst₂z⟩
                rcases st₂ with ⟨b, cb⟩
                rcases hast₂ with ⟨hredStep, hswap₂⟩
                cases cb with
                | red =>
                    simp at hswap₂
                | blue =>
                    rcases hredStep with ⟨ia, hredEdge, _hredBefore, _hab_ne⟩
                    exact ⟨ia,
                      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                        (M.good.redRouting.path ia) hredEdge).1⟩
            rcases haRed with ⟨ia, haia⟩
            by_cases haz : a = z
            · subst a
              exact (M.red_linkageDependency_acyclic hdeg hdisj z) hdepRest
            · have hclosing :
                  Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                    M.good.redRouting z a := by
                by_cases hia : ia = i
                · subst ia
                  rcases GraphPath.before_total_of_mem
                      (M.good.redRouting.path i) hz haia with hza | hazBefore
                  · exact Or.inl ⟨i, hz, haia, hza, fun hza_eq => haz hza_eq.symm⟩
                  · exact False.elim
                      (PathSlicing.false_of_shortcut_edge_of_edgeSet_unique
                        (R := M.good.redRouting)
                        (fun R' => M.redRouting_edgeSet_eq_selected hdeg hdisj R')
                        hazBefore hzxBefore haz hzx_ne (H.symm hxaAdj))
                · exact Or.inr
                    ⟨i, ia, (fun hii => hia hii.symm), hz, haia, x, hx, hzxBefore,
                      hzx_ne, hxaAdj⟩
              have hcycle :
                  Relation.TransGen
                    (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                      M.good.redRouting) z z :=
                Relation.TransGen.head hclosing hdepRest
              exact (M.red_linkageDependency_acyclic hdeg hdisj z) hcycle
        | blue =>
            simp at hswap

omit [Fintype V] in
/-- Alternating reachability from a red state to a red state respects every
blue path containing the endpoint vertices.  This is the blue symmetric
mixed-color case of Claim 2.6. -/
theorem blue_order_of_altStep_red_to_red_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {j : M.good.blueRouting.Index}
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (z, TwoPairColor.red))
    (hx : x ∈ (M.good.blueRouting.path j).vertexSet)
    (hz : z ∈ (M.good.blueRouting.path j).vertexSet) :
    (M.good.blueRouting.path j).Before x z := by
  classical
  rcases GraphPath.before_total_of_mem
      (M.good.blueRouting.path j) hx hz with hxzBefore | hzxBefore
  · exact hxzBefore
  · by_cases hxzeq : x = z
    · subst z
      exact (M.good.blueRouting.path j).before_refl hx
    · exfalso
      have hzx_ne : z ≠ x := fun h => hxzeq h.symm
      rcases Relation.ReflTransGen.cases_head hxz with hEq | hhead
      · exact hxzeq (congrArg Prod.fst hEq)
      · rcases hhead with ⟨st, hxst, hstz⟩
        rcases st with ⟨a, ca⟩
        rcases hxst with ⟨hredStep, hswap⟩
        cases ca with
        | red =>
            simp at hswap
        | blue =>
            rcases hredStep with ⟨i, hredEdge, _hredBefore, _hxa_ne⟩
            have hxaAdj : H.Adj x a :=
              GraphPath.edgeSet_subset_edgeSet
                (M.good.redRouting.path i) hredEdge
            have hdepRest :
                Relation.TransGen
                  (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                    M.good.blueRouting) a z :=
              M.blue_linkageDependency_transGen_of_altStep_blue_to_red
                hdeg hdisj ⟨j, hz⟩ hstz
            have haBlue :
                ∃ ja : M.good.blueRouting.Index,
                  a ∈ (M.good.blueRouting.path ja).vertexSet := by
              rcases Relation.ReflTransGen.cases_head hstz with hRestEq | hRestHead
              · cases hRestEq
              · rcases hRestHead with ⟨st₂, hast₂, _hst₂z⟩
                rcases st₂ with ⟨b, cb⟩
                rcases hast₂ with ⟨hblueStep, hswap₂⟩
                cases cb with
                | red =>
                    rcases hblueStep with ⟨ja, hblueEdge, _hblueBefore, _hab_ne⟩
                    exact ⟨ja,
                      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                        (M.good.blueRouting.path ja) hblueEdge).1⟩
                | blue =>
                    simp at hswap₂
            rcases haBlue with ⟨ja, haja⟩
            by_cases haz : a = z
            · subst a
              exact (M.blue_linkageDependency_acyclic hdeg hdisj z) hdepRest
            · have hclosing :
                  Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                    M.good.blueRouting z a := by
                by_cases hja : ja = j
                · subst ja
                  rcases GraphPath.before_total_of_mem
                      (M.good.blueRouting.path j) hz haja with hza | hazBefore
                  · exact Or.inl ⟨j, hz, haja, hza, fun hza_eq => haz hza_eq.symm⟩
                  · exact False.elim
                      (PathSlicing.false_of_shortcut_edge_of_edgeSet_unique
                        (R := M.good.blueRouting)
                        (fun B' => M.blueRouting_edgeSet_eq_selected hdeg hdisj B')
                        hazBefore hzxBefore haz hzx_ne (H.symm hxaAdj))
                · exact Or.inr
                    ⟨j, ja, (fun hjj => hja hjj.symm), hz, haja, x, hx,
                      hzxBefore, hzx_ne, hxaAdj⟩
              have hcycle :
                  Relation.TransGen
                    (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                      M.good.blueRouting) z z :=
                Relation.TransGen.head hclosing hdepRest
              exact (M.blue_linkageDependency_acyclic hdeg hdisj z) hcycle

omit [Fintype V] in
/-- Alternating reachability from a blue state to a red state respects every
red path containing the endpoint vertices. -/
theorem red_order_of_altStep_blue_to_red_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {i : M.good.redRouting.Index}
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (z, TwoPairColor.red))
    (hx : x ∈ (M.good.redRouting.path i).vertexSet)
    (hz : z ∈ (M.good.redRouting.path i).vertexSet) :
    (M.good.redRouting.path i).Before x z := by
  classical
  rcases GraphPath.before_total_of_mem
      (M.good.redRouting.path i) hx hz with hxzBefore | hzxBefore
  · exact hxzBefore
  · by_cases hxzeq : x = z
    · subst z
      exact (M.good.redRouting.path i).before_refl hx
    · exfalso
      have hzx_ne : z ≠ x := fun h => hxzeq h.symm
      rcases Relation.ReflTransGen.cases_head hxz with hEq | hhead
      · cases hEq
      · rcases hhead with ⟨st, hxst, hstz⟩
        rcases st with ⟨a, ca⟩
        rcases hxst with ⟨hblueStep, hswap⟩
        cases ca with
        | red =>
            have hblueColor :
                TwoPairColorEdge M.good.redRouting M.good.blueRouting
                  TwoPairColor.blue x a :=
              hblueStep
            rcases hblueStep with ⟨j, hblueEdge, _hblueBefore, _hxa_ne⟩
            have hxaAdj : H.Adj x a :=
              GraphPath.edgeSet_subset_edgeSet
                (M.good.blueRouting.path j) hblueEdge
            have hdepRestRT :
                Relation.ReflTransGen
                  (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                    M.good.redRouting) a z :=
              M.red_linkageDependency_reflTransGen_of_altStep_red_to_red
                hdeg hdisj ⟨i, hz⟩ hstz
            rcases Relation.reflTransGen_iff_eq_or_transGen.1 hdepRestRT with
              hazEq | hdepRest
            · subst a
              exact M.false_of_blueColorEdge_backward_on_red_path
                hdeg hdisj hblueColor hx hz hzxBefore hxzeq
            · have htwo :
                  Relation.ReflTransGen M.RedBlueTwoStep a z :=
                M.redBlueTwoStep_reflTransGen_of_altStep_red_to_red
                  ⟨i, hz⟩ hstz
              have haRed :
                  ∃ ia : M.good.redRouting.Index,
                    a ∈ (M.good.redRouting.path ia).vertexSet :=
                M.red_mem_of_redBlueTwoStep_reflTransGen_source ⟨i, hz⟩ htwo
              rcases haRed with ⟨ia, haia⟩
              by_cases haz : a = z
              · subst a
                exact (M.red_linkageDependency_acyclic hdeg hdisj z) hdepRest
              · have hclosing :
                    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                      M.good.redRouting z a := by
                  by_cases hia : ia = i
                  · subst ia
                    rcases GraphPath.before_total_of_mem
                        (M.good.redRouting.path i) hz haia with hza | hazBefore
                    · exact Or.inl ⟨i, hz, haia, hza, fun hza_eq => haz hza_eq.symm⟩
                    · exact False.elim
                        (PathSlicing.false_of_shortcut_edge_of_edgeSet_unique
                          (R := M.good.redRouting)
                          (fun R' => M.redRouting_edgeSet_eq_selected hdeg hdisj R')
                          hazBefore hzxBefore haz hzx_ne (H.symm hxaAdj))
                  · exact Or.inr
                      ⟨i, ia, (fun hii => hia hii.symm), hz, haia, x, hx,
                        hzxBefore, hzx_ne, hxaAdj⟩
                have hcycle :
                    Relation.TransGen
                      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                        M.good.redRouting) z z :=
                  Relation.TransGen.head hclosing hdepRest
                exact (M.red_linkageDependency_acyclic hdeg hdisj z) hcycle
        | blue =>
            simp at hswap

omit [Fintype V] in
/-- Alternating reachability from a red state to a blue state respects every
blue path containing the endpoint vertices. -/
theorem blue_order_of_altStep_red_to_blue_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x z : W} {j : M.good.blueRouting.Index}
    (hxz :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (z, TwoPairColor.blue))
    (hx : x ∈ (M.good.blueRouting.path j).vertexSet)
    (hz : z ∈ (M.good.blueRouting.path j).vertexSet) :
    (M.good.blueRouting.path j).Before x z := by
  classical
  rcases GraphPath.before_total_of_mem
      (M.good.blueRouting.path j) hx hz with hxzBefore | hzxBefore
  · exact hxzBefore
  · by_cases hxzeq : x = z
    · subst z
      exact (M.good.blueRouting.path j).before_refl hx
    · exfalso
      have hzx_ne : z ≠ x := fun h => hxzeq h.symm
      rcases Relation.ReflTransGen.cases_head hxz with hEq | hhead
      · cases hEq
      · rcases hhead with ⟨st, hxst, hstz⟩
        rcases st with ⟨a, ca⟩
        rcases hxst with ⟨hredStep, hswap⟩
        cases ca with
        | red =>
            simp at hswap
        | blue =>
            have hredColor :
                TwoPairColorEdge M.good.redRouting M.good.blueRouting
                  TwoPairColor.red x a :=
              hredStep
            rcases hredStep with ⟨i, hredEdge, _hredBefore, _hxa_ne⟩
            have hxaAdj : H.Adj x a :=
              GraphPath.edgeSet_subset_edgeSet
                (M.good.redRouting.path i) hredEdge
            have hdepRestRT :
                Relation.ReflTransGen
                  (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                    M.good.blueRouting) a z :=
              M.blue_linkageDependency_reflTransGen_of_altStep_blue_to_blue
                hdeg hdisj ⟨j, hz⟩ hstz
            rcases Relation.reflTransGen_iff_eq_or_transGen.1 hdepRestRT with
              hazEq | hdepRest
            · subst a
              exact M.false_of_redColorEdge_backward_on_blue_path
                hdeg hdisj hredColor hx hz hzxBefore hxzeq
            · have htwo :
                  Relation.ReflTransGen M.BlueRedTwoStep a z :=
                M.blueRedTwoStep_reflTransGen_of_altStep_blue_to_blue
                  ⟨j, hz⟩ hstz
              have haBlue :
                  ∃ ja : M.good.blueRouting.Index,
                    a ∈ (M.good.blueRouting.path ja).vertexSet :=
                M.blue_mem_of_blueRedTwoStep_reflTransGen_source ⟨j, hz⟩ htwo
              rcases haBlue with ⟨ja, haja⟩
              by_cases haz : a = z
              · subst a
                exact (M.blue_linkageDependency_acyclic hdeg hdisj z) hdepRest
              · have hclosing :
                    Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                      M.good.blueRouting z a := by
                  by_cases hja : ja = j
                  · subst ja
                    rcases GraphPath.before_total_of_mem
                        (M.good.blueRouting.path j) hz haja with hza | hazBefore
                    · exact Or.inl ⟨j, hz, haja, hza, fun hza_eq => haz hza_eq.symm⟩
                    · exact False.elim
                        (PathSlicing.false_of_shortcut_edge_of_edgeSet_unique
                          (R := M.good.blueRouting)
                          (fun B' => M.blueRouting_edgeSet_eq_selected hdeg hdisj B')
                          hazBefore hzxBefore haz hzx_ne (H.symm hxaAdj))
                  · exact Or.inr
                      ⟨j, ja, (fun hjj => hja hjj.symm), hz, haja, x, hx,
                        hzxBefore, hzx_ne, hxaAdj⟩
                have hcycle :
                    Relation.TransGen
                      (Lax17Proofs.SimpleGraph.PathSlicing.LinkageDependency
                        M.good.blueRouting) z z :=
                  Relation.TransGen.head hclosing hdepRest
                exact (M.blue_linkageDependency_acyclic hdeg hdisj z) hcycle

omit [Fintype V] in
/-- Claim 2.6 in reachability form for red paths, with arbitrary endpoint
state colors. -/
theorem red_order_of_altStep_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {sx sy : TwoPairAltState W} {i : M.good.redRouting.Index}
    (hxy :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting) sx sy)
    (hx : sx.1 ∈ (M.good.redRouting.path i).vertexSet)
    (hy : sy.1 ∈ (M.good.redRouting.path i).vertexSet) :
    (M.good.redRouting.path i).Before sx.1 sy.1 := by
  rcases sx with ⟨x, cx⟩
  rcases sy with ⟨y, cy⟩
  cases cx <;> cases cy
  · exact M.red_order_of_altStep_red_to_red_same_path hdeg hdisj hxy hx hy
  · exact M.red_order_of_altStep_red_to_blue_same_path hdeg hdisj hxy hx hy
  · exact M.red_order_of_altStep_blue_to_red_same_path hdeg hdisj hxy hx hy
  · exact M.red_order_of_altStep_blue_to_blue_same_path hdeg hdisj hxy hx hy

omit [Fintype V] in
/-- Claim 2.6 in reachability form for blue paths, with arbitrary endpoint
state colors. -/
theorem blue_order_of_altStep_same_path
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {sx sy : TwoPairAltState W} {j : M.good.blueRouting.Index}
    (hxy :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting) sx sy)
    (hx : sx.1 ∈ (M.good.blueRouting.path j).vertexSet)
    (hy : sy.1 ∈ (M.good.blueRouting.path j).vertexSet) :
    (M.good.blueRouting.path j).Before sx.1 sy.1 := by
  rcases sx with ⟨x, cx⟩
  rcases sy with ⟨y, cy⟩
  cases cx <;> cases cy
  · exact M.blue_order_of_altStep_red_to_red_same_path hdeg hdisj hxy hx hy
  · exact M.blue_order_of_altStep_red_to_blue_same_path hdeg hdisj hxy hx hy
  · exact M.blue_order_of_altStep_blue_to_red_same_path hdeg hdisj hxy hx hy
  · exact M.blue_order_of_altStep_blue_to_blue_same_path hdeg hdisj hxy hx hy

omit [Fintype V] in
/-- Red-blue two-step reachability is acyclic. -/
theorem redBlueTwoStep_acyclic
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    ∀ x : W, ¬ Relation.TransGen M.RedBlueTwoStep x x := by
  intro x hcycle
  let rho := M.redDependencyRank hdeg hdisj
  have hpath_rank :
      ∀ {y : W}, Relation.TransGen M.RedBlueTwoStep x y →
        rho.rank x < rho.rank y := by
    intro y hxy
    induction hxy with
    | single h =>
      exact M.redDependencyRank_lt_of_redBlueTwoStep hdeg hdisj h
    | tail _hyz hzx ih =>
      exact ih.trans
        (M.redDependencyRank_lt_of_redBlueTwoStep hdeg hdisj hzx)
  have hltcycle : rho.rank x < rho.rank x := by
    exact hpath_rank hcycle
  exact Nat.lt_irrefl _ hltcycle

omit [Fintype V] in
/-- Blue-red two-step reachability is acyclic. -/
theorem blueRedTwoStep_acyclic
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    ∀ x : W, ¬ Relation.TransGen M.BlueRedTwoStep x x := by
  intro x hcycle
  let rho := M.blueDependencyRank hdeg hdisj
  have hpath_rank :
      ∀ {y : W}, Relation.TransGen M.BlueRedTwoStep x y →
        rho.rank x < rho.rank y := by
    intro y hxy
    induction hxy with
    | single h =>
      exact M.blueDependencyRank_lt_of_blueRedTwoStep hdeg hdisj h
    | tail _hyz hzx ih =>
      exact ih.trans
        (M.blueDependencyRank_lt_of_blueRedTwoStep hdeg hdisj hzx)
  have hltcycle : rho.rank x < rho.rank x := by
    exact hpath_rank hcycle
  exact Nat.lt_irrefl _ hltcycle

omit [Fintype V] in
/-- A nonempty alternating cycle based at a red state groups into a nonempty
red-blue two-step cycle. -/
theorem redBlueTwoStep_transGen_of_altStep_red_cycle
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x : W}
    (hcycle :
      Relation.TransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.red) (x, TwoPairColor.red)) :
    Relation.TransGen M.RedBlueTwoStep x x := by
  rcases Relation.TransGen.head'_iff.1 hcycle with
    ⟨st₁, h01, h1x⟩
  rcases st₁ with ⟨y, cy⟩
  have h01' :
      TwoPairAltStep M.good.redRouting M.good.blueRouting
        (x, TwoPairColor.red) (y, cy) := h01
  rcases h01 with ⟨hred, hcy⟩
  have hcyBlue : cy = TwoPairColor.blue := by
    simpa using hcy
  subst cy
  rcases hred with ⟨i, hredEdge, _hredBefore, _hxy_ne⟩
  have hxRed :
      ∃ i : M.good.redRouting.Index,
        x ∈ (M.good.redRouting.path i).vertexSet :=
    ⟨i,
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        (M.good.redRouting.path i) hredEdge).1⟩
  rcases Relation.ReflTransGen.cases_head h1x with hEq | hhead
  · have hcolor :
        TwoPairColor.blue = TwoPairColor.red :=
      congrArg Prod.snd hEq
    cases hcolor
  · rcases hhead with ⟨st₂, h12, h2x⟩
    rcases st₂ with ⟨z, cz⟩
    have h12' :
        TwoPairAltStep M.good.redRouting M.good.blueRouting
          (y, TwoPairColor.blue) (z, cz) := h12
    rcases h12 with ⟨_hblue, hcz⟩
    have hczRed : cz = TwoPairColor.red := by
      simpa using hcz
    subst cz
    have hrest :
        Relation.ReflTransGen M.RedBlueTwoStep z x :=
      M.redBlueTwoStep_reflTransGen_of_altStep_red_to_red hxRed h2x
    have hzRed :
        ∃ i : M.good.redRouting.Index,
          z ∈ (M.good.redRouting.path i).vertexSet :=
      M.red_mem_of_redBlueTwoStep_reflTransGen_source hxRed hrest
    have hfirst : M.RedBlueTwoStep x z :=
      M.redBlueTwoStep_of_altStep_pair h01' h12' hzRed
    exact Relation.TransGen.head' hfirst hrest

omit [Fintype V] in
/-- A nonempty alternating cycle based at a blue state groups into a nonempty
blue-red two-step cycle. -/
theorem blueRedTwoStep_transGen_of_altStep_blue_cycle
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    {x : W}
    (hcycle :
      Relation.TransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, TwoPairColor.blue) (x, TwoPairColor.blue)) :
    Relation.TransGen M.BlueRedTwoStep x x := by
  rcases Relation.TransGen.head'_iff.1 hcycle with
    ⟨st₁, h01, h1x⟩
  rcases st₁ with ⟨y, cy⟩
  have h01' :
      TwoPairAltStep M.good.redRouting M.good.blueRouting
        (x, TwoPairColor.blue) (y, cy) := h01
  rcases h01 with ⟨hblue, hcy⟩
  have hcyRed : cy = TwoPairColor.red := by
    simpa using hcy
  subst cy
  rcases hblue with ⟨j, hblueEdge, _hblueBefore, _hxy_ne⟩
  have hxBlue :
      ∃ j : M.good.blueRouting.Index,
        x ∈ (M.good.blueRouting.path j).vertexSet :=
    ⟨j,
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        (M.good.blueRouting.path j) hblueEdge).1⟩
  rcases Relation.ReflTransGen.cases_head h1x with hEq | hhead
  · have hcolor :
        TwoPairColor.red = TwoPairColor.blue :=
      congrArg Prod.snd hEq
    cases hcolor
  · rcases hhead with ⟨st₂, h12, h2x⟩
    rcases st₂ with ⟨z, cz⟩
    have h12' :
        TwoPairAltStep M.good.redRouting M.good.blueRouting
          (y, TwoPairColor.red) (z, cz) := h12
    rcases h12 with ⟨_hred, hcz⟩
    have hczBlue : cz = TwoPairColor.blue := by
      simpa using hcz
    subst cz
    have hrest :
        Relation.ReflTransGen M.BlueRedTwoStep z x :=
      M.blueRedTwoStep_reflTransGen_of_altStep_blue_to_blue hxBlue h2x
    have hzBlue :
        ∃ j : M.good.blueRouting.Index,
          z ∈ (M.good.blueRouting.path j).vertexSet :=
      M.blue_mem_of_blueRedTwoStep_reflTransGen_source hxBlue hrest
    have hfirst : M.BlueRedTwoStep x z :=
      M.blueRedTwoStep_of_altStep_pair h01' h12' hzBlue
    exact Relation.TransGen.head' hfirst hrest

omit [Fintype V] in
/-- The alternating state relation has no directed cycle in a minimal good
minor under the Section 2 terminal hypotheses. -/
theorem altStep_acyclic
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    ∀ st : TwoPairAltState W,
      ¬ Relation.TransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting) st st := by
  rintro ⟨x, c⟩ hcycle
  cases c with
  | red =>
      exact M.redBlueTwoStep_acyclic hdeg hdisj x
        (M.redBlueTwoStep_transGen_of_altStep_red_cycle hcycle)
  | blue =>
      exact M.blueRedTwoStep_acyclic hdeg hdisj x
        (M.blueRedTwoStep_transGen_of_altStep_blue_cycle hcycle)

end TwoPairMinimalGoodMinor

/-- The chain cover produced in the proof of Theorem 2.2 for the original red
orientation, abstracted down to exactly the data needed to assign labels.

The chains themselves are represented as simple paths in the union graph.  The
omitted construction work is to prove that the greedy alternating walks exist,
cover every vertex, and satisfy the order property recorded below. -/
structure TwoPairForwardChainCover
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- The `2k` chains, indexed directly by their eventual labels. -/
  chain : Fin (2 * k) → GraphPath (twoPackingUnionGraph P Q)
  /-- Every vertex is on at least one chain. -/
  covers : ∀ v : V, ∃ c : Fin (2 * k), v ∈ (chain c).vertexSet
  /-- Claim 2.6 for red paths: chain order agrees with red-path order. -/
  red_order :
    ∀ (c : Fin (2 * k)) (i : P.Index) ⦃x y : V⦄,
      x ∈ (chain c).vertexSet →
        y ∈ (chain c).vertexSet →
          x ∈ (P.path i).vertexSet →
            y ∈ (P.path i).vertexSet →
              (chain c).Before x y →
                (P.path i).Before x y
  /-- Claim 2.6 for blue paths: chain order agrees with blue-path order. -/
  blue_order :
    ∀ (c : Fin (2 * k)) (j : Q.Index) ⦃x y : V⦄,
      x ∈ (chain c).vertexSet →
        y ∈ (chain c).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              (chain c).Before x y →
                (Q.path j).Before x y

namespace TwoPairForwardChainCover

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- Choose one covering chain for a vertex; this is the label assignment at
the end of the proof of Theorem 2.2. -/
noncomputable def label (Z : TwoPairForwardChainCover P Q k) (v : V) :
    Fin (2 * k) :=
  Classical.choose (Z.covers v)

omit [Fintype V] in
/-- The chosen label chain contains the vertex it labels. -/
theorem label_mem (Z : TwoPairForwardChainCover P Q k) (v : V) :
    v ∈ (Z.chain (Z.label v)).vertexSet :=
  Classical.choose_spec (Z.covers v)

/-- A chain cover with Claim 2.6's order property gives Theorem 2.2's forward
same-order labeling. -/
noncomputable def toForwardLabeling
    (Z : TwoPairForwardChainCover P Q k) :
    TwoPairForwardLabeling P Q k where
  label := Z.label
  same_label_order := by
    intro x y i j hxR hyR hxB hyB hlabel hxyR
    classical
    let c := Z.label x
    have hxC : x ∈ (Z.chain c).vertexSet := by
      simpa [c] using Z.label_mem x
    have hyC : y ∈ (Z.chain c).vertexSet := by
      have hyC' : y ∈ (Z.chain (Z.label y)).vertexSet := Z.label_mem y
      simpa [c, hlabel] using hyC'
    rcases GraphPath.before_total_of_mem (Z.chain c) hxC hyC with hxyC | hyxC
    · exact Z.blue_order c j hxC hyC hxB hyB hxyC
    · have hyxR : (P.path i).Before y x :=
        Z.red_order c i hyC hxC hyR hxR hyxC
      have hxy : x = y := (P.path i).before_antisymm hxyR hyxR
      subst y
      exact (Q.path j).before_refl hxB

end TwoPairForwardChainCover

/-- The chain cover for the instance where red paths are reversed, restated in
the original red orientation. -/
structure TwoPairReverseRedChainCover
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- The `2k` chains, indexed directly by their eventual labels. -/
  chain : Fin (2 * k) → GraphPath (twoPackingUnionGraph P Q)
  /-- Every vertex is on at least one chain. -/
  covers : ∀ v : V, ∃ c : Fin (2 * k), v ∈ (chain c).vertexSet
  /-- Claim 2.6 for reversed red paths, translated back to the original red
  orientation. -/
  red_reverse_order :
    ∀ (c : Fin (2 * k)) (i : P.Index) ⦃x y : V⦄,
      x ∈ (chain c).vertexSet →
        y ∈ (chain c).vertexSet →
          x ∈ (P.path i).vertexSet →
            y ∈ (P.path i).vertexSet →
              (chain c).Before x y →
                (P.path i).Before y x
  /-- Claim 2.6 for blue paths in the reversed-red instance. -/
  blue_order :
    ∀ (c : Fin (2 * k)) (j : Q.Index) ⦃x y : V⦄,
      x ∈ (chain c).vertexSet →
        y ∈ (chain c).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              (chain c).Before x y →
                (Q.path j).Before x y

namespace TwoPairReverseRedChainCover

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- Choose one covering chain for a vertex in the reversed-red chain cover. -/
noncomputable def label (Z : TwoPairReverseRedChainCover P Q k) (v : V) :
    Fin (2 * k) :=
  Classical.choose (Z.covers v)

omit [Fintype V] in
/-- The chosen reversed-red label chain contains the vertex it labels. -/
theorem label_mem (Z : TwoPairReverseRedChainCover P Q k) (v : V) :
    v ∈ (Z.chain (Z.label v)).vertexSet :=
  Classical.choose_spec (Z.covers v)

/-- A reversed-red chain cover gives the second Theorem 2.2 labeling, stated
back in the original red orientation. -/
noncomputable def toReverseRedLabeling
    (Z : TwoPairReverseRedChainCover P Q k) :
    TwoPairReverseRedLabeling P Q k where
  label := Z.label
  same_reverseLabel_order := by
    intro x y i j hxR hyR hxB hyB hlabel hxyR
    classical
    let c := Z.label x
    have hxC : x ∈ (Z.chain c).vertexSet := by
      simpa [c] using Z.label_mem x
    have hyC : y ∈ (Z.chain c).vertexSet := by
      have hyC' : y ∈ (Z.chain (Z.label y)).vertexSet := Z.label_mem y
      simpa [c, hlabel] using hyC'
    rcases GraphPath.before_total_of_mem (Z.chain c) hxC hyC with hxyC | hyxC
    · have hyxR : (P.path i).Before y x :=
        Z.red_reverse_order c i hxC hyC hxR hyR hxyC
      have hxy : x = y := (P.path i).before_antisymm hxyR hyxR
      subst y
      exact (Q.path j).before_refl hxB
    · exact Z.blue_order c j hyC hxC hyB hxB hyxC

end TwoPairReverseRedChainCover

/-- A proof-facing version of the two labelings produced in Section 2.

For every high-degree vertex of the union of the red and blue routings we
record the red path and blue path containing it.  The two label maps encode
Theorem 2.2 applied once in the original red orientation and once after
reversing all red paths:

* equal `label` means the red and blue orders agree;
* equal `reverseLabel` means the original red order and blue order disagree.

Those two facts force any two high-degree vertices with the same red path,
blue path, and two labels to be equal. -/
structure TwoPairChainLabelCertificate
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) (k : ℕ) where
  /-- First chain-labeling from Theorem 2.2. -/
  label : V → Fin (2 * k)
  /-- Chain-labeling after reversing the red paths. -/
  reverseLabel : V → Fin (2 * k)
  /-- The red path containing a high-degree union vertex. -/
  redIndex :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → P.Index
  /-- The blue path containing a high-degree union vertex. -/
  blueIndex :
    ∀ v : V,
      v ∈ branchVertexFinset (twoPackingUnionGraph P Q) → Q.Index
  /-- Membership in the selected red path. -/
  red_mem :
    ∀ ⦃v : V⦄ (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      v ∈ (P.path (redIndex v hv)).vertexSet
  /-- Membership in the selected blue path. -/
  blue_mem :
    ∀ ⦃v : V⦄ (hv : v ∈ branchVertexFinset (twoPackingUnionGraph P Q)),
      v ∈ (Q.path (blueIndex v hv)).vertexSet
  /-- Equal first labels force agreement of red and blue order. -/
  same_label_order :
    ∀ ⦃x y : V⦄ (i : P.Index) (j : Q.Index),
      x ∈ (P.path i).vertexSet →
        y ∈ (P.path i).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              label x = label y →
                (P.path i).Before x y →
                  (Q.path j).Before x y
  /-- Equal reversed-red labels force disagreement of original red and blue
  order. -/
  same_reverseLabel_order :
    ∀ ⦃x y : V⦄ (i : P.Index) (j : Q.Index),
      x ∈ (P.path i).vertexSet →
        y ∈ (P.path i).vertexSet →
          x ∈ (Q.path j).vertexSet →
            y ∈ (Q.path j).vertexSet →
              reverseLabel x = reverseLabel y →
                (P.path i).Before x y →
                  (Q.path j).Before y x

namespace TwoPairChainLabelCertificate

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- Assemble the two Theorem 2.2 labelings and the branch-path incidence data
into the single certificate consumed by the counting proof. -/
def ofLabelings
    (L : TwoPairForwardLabeling P Q k)
    (Lrev : TwoPairReverseRedLabeling P Q k)
    (B : TwoPairBranchCarrier P Q) :
    TwoPairChainLabelCertificate P Q k where
  label := L.label
  reverseLabel := Lrev.label
  redIndex := B.redIndex
  blueIndex := B.blueIndex
  red_mem := B.red_mem
  blue_mem := B.blue_mem
  same_label_order := L.same_label_order
  same_reverseLabel_order := Lrev.same_reverseLabel_order

end TwoPairChainLabelCertificate

namespace TwoPairChainLabelCertificate

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- Assemble the two Theorem 2.2 labelings into the certificate consumed by the
counting proof.  The branch-path incidence is forced for any two routings: a
vertex outside one routing has degree at most two in the union, so every
high-degree vertex lies on both a red and a blue path. -/
noncomputable def ofLabelingsAndPackings
    (L : TwoPairForwardLabeling P Q k)
    (Lrev : TwoPairReverseRedLabeling P Q k) :
    TwoPairChainLabelCertificate P Q k :=
  ofLabelings L Lrev (TwoPairBranchCarrier.ofPackings P Q)

end TwoPairChainLabelCertificate

namespace TwoPairChainLabelCertificate

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}
variable {k : ℕ}

/-- The tuple used in the pigeonhole/counting step. -/
noncomputable def branchTuple
    (C : TwoPairChainLabelCertificate P Q k)
    (v : {x : V // x ∈ branchVertexFinset (twoPackingUnionGraph P Q)}) :
    P.Index × Q.Index × Fin (2 * k) × Fin (2 * k) :=
  (C.redIndex v.1 v.2, C.blueIndex v.1 v.2, C.label v.1, C.reverseLabel v.1)

/-- The chain-label tuple is injective on high-degree vertices. -/
theorem branchTuple_injective
    (C : TwoPairChainLabelCertificate P Q k) :
    Function.Injective C.branchTuple := by
  classical
  intro x y hxy
  apply Subtype.ext
  dsimp [branchTuple] at hxy
  have hred :
      C.redIndex x.1 x.2 = C.redIndex y.1 y.2 :=
    congrArg Prod.fst hxy
  have hblue :
      C.blueIndex x.1 x.2 = C.blueIndex y.1 y.2 := by
    exact congrArg (fun z => z.2.1) hxy
  have hlabel : C.label x.1 = C.label y.1 := by
    exact congrArg (fun z => z.2.2.1) hxy
  have hrev : C.reverseLabel x.1 = C.reverseLabel y.1 := by
    exact congrArg (fun z => z.2.2.2) hxy
  let i := C.redIndex x.1 x.2
  let j := C.blueIndex x.1 x.2
  have hxR : x.1 ∈ (P.path i).vertexSet := by
    simpa [i] using C.red_mem x.2
  have hyR : y.1 ∈ (P.path i).vertexSet := by
    simpa [i, hred] using C.red_mem y.2
  have hxB : x.1 ∈ (Q.path j).vertexSet := by
    simpa [j] using C.blue_mem x.2
  have hyB : y.1 ∈ (Q.path j).vertexSet := by
    simpa [j, hblue] using C.blue_mem y.2
  rcases GraphPath.before_total_of_mem (P.path i) hxR hyR with hxyR | hyxR
  · have hxyB : (Q.path j).Before x.1 y.1 :=
      C.same_label_order i j hxR hyR hxB hyB hlabel hxyR
    have hyxB : (Q.path j).Before y.1 x.1 :=
      C.same_reverseLabel_order i j hxR hyR hxB hyB hrev hxyR
    exact (Q.path j).before_antisymm hxyB hyxB
  · have hyxLabel : C.label y.1 = C.label x.1 := hlabel.symm
    have hyxRev : C.reverseLabel y.1 = C.reverseLabel x.1 := hrev.symm
    have hyxB : (Q.path j).Before y.1 x.1 :=
      C.same_label_order i j hyR hxR hyB hxB hyxLabel hyxR
    have hxyB : (Q.path j).Before x.1 y.1 :=
      C.same_reverseLabel_order i j hyR hxR hyB hxB hyxRev hyxR
    exact ((Q.path j).before_antisymm hyxB hxyB).symm

/-- The high-degree vertices in the union of two routings are bounded by the
number of possible red path, blue path, and two-label tuples. -/
theorem branchVertexCount_le_tuple_count
    (C : TwoPairChainLabelCertificate P Q k) :
    branchVertexCount (twoPackingUnionGraph P Q) ≤
      P.card * Q.card * (2 * k) * (2 * k) := by
  classical
  let B := branchVertexFinset (twoPackingUnionGraph P Q)
  have hcard :
      B.card ≤
        Fintype.card (P.Index × Q.Index × Fin (2 * k) × Fin (2 * k)) := by
    simpa [B] using
      (Fintype.card_le_of_injective C.branchTuple C.branchTuple_injective)
  have htuple :
      Fintype.card (P.Index × Q.Index × Fin (2 * k) × Fin (2 * k)) =
        P.card * Q.card * (2 * k) * (2 * k) := by
    simp [PerfectPathPacking.card, Nat.mul_assoc]
  simpa [branchVertexCount, B, htuple] using hcard

/-- The Section 2 counting bound following from the chain-label certificate. -/
theorem branchVertexCount_le_four_mul_pow
    (C : TwoPairChainLabelCertificate P Q k)
    (hPcard : P.card ≤ k) (hQcard : Q.card ≤ k) :
    branchVertexCount (twoPackingUnionGraph P Q) ≤ 4 * k ^ 4 := by
  classical
  have htuple := C.branchVertexCount_le_tuple_count
  have hle :
      P.card * Q.card * (2 * k) * (2 * k) ≤
        k * k * (2 * k) * (2 * k) := by
    gcongr
  calc
    branchVertexCount (twoPackingUnionGraph P Q)
        ≤ P.card * Q.card * (2 * k) * (2 * k) := htuple
    _ ≤ k * k * (2 * k) * (2 * k) := hle
    _ = 4 * k ^ 4 := by ring

/-- The exact numerical bound used by Theorem 1.3 follows immediately from
the sharper chain-label count. -/
theorem branchVertexCount_le_theorem13_bound
    (C : TwoPairChainLabelCertificate P Q k)
    (hPcard : P.card ≤ k) (hQcard : Q.card ≤ k) :
    branchVertexCount (twoPackingUnionGraph P Q) ≤ 8 * k ^ 4 + 8 * k := by
  have hfour := C.branchVertexCount_le_four_mul_pow hPcard hQcard
  nlinarith [hfour, Nat.zero_le (k ^ 4), Nat.zero_le k]

end TwoPairChainLabelCertificate

/-! ## Theorem 2.1 counting closure -/

/-- The minimal-core consequence used after Theorem 2.2 in the paper.

For a minimal two-pair minor, every non-terminal vertex lies on one red path
and one blue path and has degree four in the union graph.  This structure keeps
that graph-theoretic consequence explicit, so the purely counting part of
Theorem 2.1 is proved below without hiding it in the old Theorem 1.3 axiom. -/
structure TwoPairMinimalCoreCertificate
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) where
  /-- Every non-terminal vertex is counted by `τ` in the union of the red and
  blue routing graphs. -/
  nonterminal_branch :
    ∀ ⦃v : V⦄,
      v ∉ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        v ∈ branchVertexFinset (twoPackingUnionGraph P Q)

/-- Proof-facing version of the paper's local minimality consequences.

The Section 2 minimal-minor argument supplies these three facts before the
counting step:
* each nonterminal is internal to one red path;
* each nonterminal is internal to one blue path;
* no nonterminal incident edge is used by both routings.

From these facts, every nonterminal has at least three distinct neighbors in
the red/blue union and hence is counted by `τ`. -/
structure TwoPairInternalCoreCertificate
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂) where
  /-- Every nonterminal is an internal vertex of a red path. -/
  red_internal :
    ∀ ⦃v : V⦄,
      v ∉ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        ∃ i : P.Index,
          v ∈ (P.path i).vertexSet ∧
            v ≠ (P.path i).source ∧ v ≠ (P.path i).target
  /-- Every nonterminal is an internal vertex of a blue path. -/
  blue_internal :
    ∀ ⦃v : V⦄,
      v ∉ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        ∃ j : Q.Index,
          v ∈ (Q.path j).vertexSet ∧
            v ≠ (Q.path j).source ∧ v ≠ (Q.path j).target
  /-- A nonterminal incident edge cannot be simultaneously red and blue. -/
  no_nonterminal_shared_edge :
    ∀ ⦃v w : V⦄,
      v ∉ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        s(v, w) ∈ P.toPathPacking.edgeSet →
          s(v, w) ∈ Q.toPathPacking.edgeSet →
            False

namespace TwoPairInternalCoreCertificate

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}

/-- The local internal-incidence and no-shared-edge facts imply the
minimal-core `τ` condition used by Theorem 2.1's counting proof. -/
theorem toMinimalCoreCertificate
    (C : TwoPairInternalCoreCertificate P Q) :
    TwoPairMinimalCoreCertificate P Q where
  nonterminal_branch := by
    classical
    intro v hvT
    rcases C.red_internal hvT with
      ⟨i, hvRi, hvRsource, hvRtarget⟩
    rcases C.blue_internal hvT with
      ⟨j, hvBj, hvBsource, hvBtarget⟩
    rcases
        GraphPath.exists_two_distinct_path_neighbors_of_internal
          (P.path i) hvRi hvRsource hvRtarget with
      ⟨r₁, r₂, hr₁r₂, hr₁Edge, hr₂Edge⟩
    rcases
        GraphPath.exists_two_distinct_path_neighbors_of_internal
          (Q.path j) hvBj hvBsource hvBtarget with
      ⟨b₁, _b₂, _hb₁b₂, hb₁Edge, _hb₂Edge⟩
    have hr₁Pack :
        s(v, r₁) ∈ P.toPathPacking.edgeSet :=
      (P.toPathPacking.mem_edgeSet).2 ⟨i, hr₁Edge⟩
    have hr₂Pack :
        s(v, r₂) ∈ P.toPathPacking.edgeSet :=
      (P.toPathPacking.mem_edgeSet).2 ⟨i, hr₂Edge⟩
    have hb₁Pack :
        s(v, b₁) ∈ Q.toPathPacking.edgeSet :=
      (Q.toPathPacking.mem_edgeSet).2 ⟨j, hb₁Edge⟩
    have hb₁_ne_r₁ : b₁ ≠ r₁ := by
      intro h
      exact C.no_nonterminal_shared_edge hvT
        (by simpa [h] using hr₁Pack)
        (by simpa [h] using hb₁Pack)
    have hb₁_ne_r₂ : b₁ ≠ r₂ := by
      intro h
      exact C.no_nonterminal_shared_edge hvT
        (by simpa [h] using hr₂Pack)
        (by simpa [h] using hb₁Pack)
    have hv_ne_r₁ : v ≠ r₁ := by
      have hadj : G.Adj v r₁ := by
        simpa using GraphPath.edgeSet_subset_edgeSet (P.path i) hr₁Edge
      exact hadj.ne
    have hv_ne_r₂ : v ≠ r₂ := by
      have hadj : G.Adj v r₂ := by
        simpa using GraphPath.edgeSet_subset_edgeSet (P.path i) hr₂Edge
      exact hadj.ne
    have hv_ne_b₁ : v ≠ b₁ := by
      have hadj : G.Adj v b₁ := by
        simpa using GraphPath.edgeSet_subset_edgeSet (Q.path j) hb₁Edge
      exact hadj.ne
    have hAdjR₁ :
        P.toPathPacking.spanningGraph.Adj v r₁ :=
      (P.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
        ⟨⟨i, hr₁Edge⟩, hv_ne_r₁⟩
    have hAdjR₂ :
        P.toPathPacking.spanningGraph.Adj v r₂ :=
      (P.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
        ⟨⟨i, hr₂Edge⟩, hv_ne_r₂⟩
    have hAdjB₁ :
        Q.toPathPacking.spanningGraph.Adj v b₁ :=
      (Q.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
        ⟨⟨j, hb₁Edge⟩, hv_ne_b₁⟩
    have hUnionR₁ :
        (twoPackingUnionGraph P Q).Adj v r₁ := by
      simpa [twoPackingUnionGraph] using Or.inl hAdjR₁
    have hUnionR₂ :
        (twoPackingUnionGraph P Q).Adj v r₂ := by
      simpa [twoPackingUnionGraph] using Or.inl hAdjR₂
    have hUnionB₁ :
        (twoPackingUnionGraph P Q).Adj v b₁ := by
      simpa [twoPackingUnionGraph] using Or.inr hAdjB₁
    have hnotDegree :
        ¬ DegreeAtMost (twoPackingUnionGraph P Q) v 2 :=
      not_degreeAtMost_two_of_three_adj
        hUnionR₁ hUnionR₂ hUnionB₁
        hr₁r₂ hb₁_ne_r₁.symm hb₁_ne_r₂.symm
    exact Finset.mem_filter.2 ⟨Finset.mem_univ v, hnotDegree⟩

end TwoPairInternalCoreCertificate

/-! ## Good-minor local core incidence -/

/-- The local incidence facts about a good minor that the paper obtains from
minimality before applying the chain-label counting proof. -/
structure TwoPairGoodMinorCoreIncidence
    {W : Type w} [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V}
    (N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂) where
  /-- Every nonterminal vertex lies on a red path. -/
  red_vertex :
    ∀ ⦃v : W⦄,
      v ∉ N.terminalSet →
        v ∈ N.redRouting.toPathPacking.vertexSet
  /-- Every nonterminal vertex lies on a blue path. -/
  blue_vertex :
    ∀ ⦃v : W⦄,
      v ∉ N.terminalSet →
        v ∈ N.blueRouting.toPathPacking.vertexSet
  /-- A nonterminal incident edge cannot be simultaneously red and blue. -/
  no_nonterminal_shared_edge :
    ∀ ⦃v w : W⦄,
      v ∉ N.terminalSet →
        s(v, w) ∈ N.redRouting.toPathPacking.edgeSet →
          s(v, w) ∈ N.blueRouting.toPathPacking.edgeSet →
            False

namespace TwoPairGoodMinorCoreIncidence

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {N : TwoPairGoodMinor G H S₁ T₁ S₂ T₂}

omit [Fintype V] in
/-- Convert good-minor incidence into the internal-core certificate used by
the counting theorem. -/
theorem toInternalCoreCertificate
    (C : TwoPairGoodMinorCoreIncidence N) :
    TwoPairInternalCoreCertificate N.redRouting N.blueRouting where
  red_internal := by
    intro v hv
    change v ∉ N.terminalSet at hv
    rcases (N.redRouting.toPathPacking.mem_vertexSet).1 (C.red_vertex hv) with
      ⟨i, hvi⟩
    exact ⟨i, hvi, (N.red_internal_of_mem_vertexSet_of_not_terminal hv).1,
      (N.red_internal_of_mem_vertexSet_of_not_terminal hv).2⟩
  blue_internal := by
    intro v hv
    change v ∉ N.terminalSet at hv
    rcases (N.blueRouting.toPathPacking.mem_vertexSet).1 (C.blue_vertex hv) with
      ⟨j, hvj⟩
    exact ⟨j, hvj, (N.blue_internal_of_mem_vertexSet_of_not_terminal hv).1,
      (N.blue_internal_of_mem_vertexSet_of_not_terminal hv).2⟩
  no_nonterminal_shared_edge := by
    intro v w hv hred hblue
    change v ∉ N.terminalSet at hv
    exact C.no_nonterminal_shared_edge hv hred hblue

omit [Fintype V] in
/-- Convert good-minor core-incidence facts directly into the minimal-core
certificate consumed by the counting theorem. -/
theorem toMinimalCoreCertificate
    [Fintype W]
    (C : TwoPairGoodMinorCoreIncidence N) :
    TwoPairMinimalCoreCertificate N.redRouting N.blueRouting :=
  C.toInternalCoreCertificate.toMinimalCoreCertificate

omit [Fintype V] in
/-- Core-incidence facts are unchanged when the first routing pair is
reversed. -/
noncomputable def reverseRed
    (C : TwoPairGoodMinorCoreIncidence N) :
    TwoPairGoodMinorCoreIncidence N.reverseRed where
  red_vertex := by
    intro v hv
    have hvOld : v ∉ N.terminalSet := by
      intro h
      exact hv (by
        simpa using h)
    simpa [TwoPairGoodMinor.reverseRed] using C.red_vertex hvOld
  blue_vertex := by
    intro v hv
    have hvOld : v ∉ N.terminalSet := by
      intro h
      exact hv (by
        simpa using h)
    simpa [TwoPairGoodMinor.reverseRed] using C.blue_vertex hvOld
  no_nonterminal_shared_edge := by
    intro v w hv hred hblue
    have hvOld : v ∉ N.terminalSet := by
      intro h
      exact hv (by
        simpa using h)
    exact C.no_nonterminal_shared_edge hvOld
      (by simpa [TwoPairGoodMinor.reverseRed] using hred)
      (by simpa [TwoPairGoodMinor.reverseRed] using hblue)

end TwoPairGoodMinorCoreIncidence

namespace TwoPairMinimalGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

omit [Fintype V] in
/-- Under the degree-one terminal hypothesis, no terminal image is a
high-degree vertex of the selected red/blue union in a minimal good minor. -/
theorem not_branchVertex_of_mem_terminalSet
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    {v : W}
    (hvTerm : v ∈ M.good.terminalSet) :
    v ∉ branchVertexFinset
      (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) := by
  classical
  intro hvBranch
  have hnot :
      ¬ DegreeAtMost
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) v 2 :=
    (Finset.mem_filter.mp hvBranch).2
  have hleH : DegreeAtMost H v 2 :=
    DegreeAtMost.mono (M.good.degreeAtMost_one_of_mem_terminalSet hdeg hvTerm)
      (by omega)
  exact hnot (by
    rw [M.twoPackingUnionGraph_eq]
    exact hleH)

omit [Fintype V] in
/-- High-degree vertices of the selected red/blue union are nonterminals under
the degree-one terminal hypothesis. -/
theorem not_mem_terminalSet_of_branchVertex
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    {v : W}
    (hvBranch :
      v ∈ branchVertexFinset
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)) :
    v ∉ M.good.terminalSet := by
  intro hvTerm
  exact M.not_branchVertex_of_mem_terminalSet hdeg hvTerm hvBranch

omit [Fintype V] in
/-- A backwards-minimal state that can still reach a high-degree union vertex
is one of the canonical source states.

This is the branch-restricted replacement for the paper's all-nonterminal
core-incidence step.  Terminal stubs can occur with the singleton-terminal
minor model, but they cannot lie on a nontrivial alternating prefix that still
reaches a branch vertex. -/
theorem exists_startIndex_state_eq_of_no_predecessor_of_reaches_branchVertex
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {target x : W} {c ctarget : TwoPairColor}
    (htarget :
      target ∈ branchVertexFinset
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting))
    (hreach :
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (x, c) (target, ctarget))
    (hnopred :
      ∀ st : TwoPairAltState W,
        ¬ TwoPairAltStep M.good.redRouting M.good.blueRouting st (x, c)) :
    ∃ a : TwoPairStartIndex M.good.redRouting M.good.blueRouting,
      TwoPairStartIndex.state
        (P := M.good.redRouting) (Q := M.good.blueRouting) a = (x, c) := by
  classical
  let P := M.good.redRouting
  let Q := M.good.blueRouting
  have htargetNonterminal :
      target ∉ M.good.terminalSet :=
    M.not_mem_terminalSet_of_branchVertex hdeg htarget
  have htargetRed :
      target ∈ P.toPathPacking.vertexSet :=
    TwoPairBranchCarrier.red_vertexSet_mem_of_branchVertex
      (P := P) (Q := Q) htarget
  have htargetBlue :
      target ∈ Q.toPathPacking.vertexSet :=
    TwoPairBranchCarrier.blue_vertexSet_mem_of_branchVertex
      (P := P) (Q := Q) htarget
  rcases Relation.ReflTransGen.cases_head hreach with hEq | hhead
  · cases hEq
    cases c with
    | red =>
        rcases (Q.toPathPacking.mem_vertexSet).1 htargetBlue with
          ⟨j, htBlue⟩
        have ht_not_source :
            target ≠ (Q.path j).source :=
          (M.good.blue_internal_of_mem_vertexSet_of_not_terminal
            htargetNonterminal).1
        rcases TwoPairColorEdge.exists_blue_backward_of_mem_not_source
            (P := P) (Q := Q) htBlue ht_not_source with ⟨z, hblue⟩
        exact False.elim
          (hnopred (z, TwoPairColor.blue) ⟨hblue, by simp⟩)
    | blue =>
        rcases (P.toPathPacking.mem_vertexSet).1 htargetRed with
          ⟨i, htRed⟩
        have ht_not_source :
            target ≠ (P.path i).source :=
          (M.good.red_internal_of_mem_vertexSet_of_not_terminal
            htargetNonterminal).1
        rcases TwoPairColorEdge.exists_red_backward_of_mem_not_source
            (P := P) (Q := Q) htRed ht_not_source with ⟨z, hred⟩
        exact False.elim
          (hnopred (z, TwoPairColor.red) ⟨hred, by simp⟩)
  · rcases hhead with ⟨st, hxst, hstTarget⟩
    rcases st with ⟨y, cy⟩
    have hxst0 :
        TwoPairAltStep P Q (x, c) (y, cy) := hxst
    rcases hxst with ⟨hcolor, hcy⟩
    cases c with
    | red =>
        have hcyBlue : cy = TwoPairColor.blue := by
          simpa using hcy
        subst cy
        rcases hcolor with ⟨i, hredEdge, hredBefore, hxy_ne⟩
        have hxRed : x ∈ (P.path i).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (P.path i) hredEdge).1
        by_cases hxTerm : x ∈ M.good.terminalSet
        · rcases M.good.isEndpoint_of_mem_terminalSet_of_mem_path
              hdeg hxTerm (P.path i) hxRed with hsource | htarget'
          · refine ⟨Sum.inl i, ?_⟩
            simp [TwoPairStartIndex.state, P, Q, hsource]
          · have hyRed : y ∈ (P.path i).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (P.path i) hredEdge).2
            have hyt : (P.path i).Before y (P.path i).target :=
              (P.path i).before_target_of_mem hyRed
            have hty : (P.path i).Before (P.path i).target y := by
              simpa [htarget'] using hredBefore
            have hy_eq_target : y = (P.path i).target :=
              (P.path i).before_antisymm hyt hty
            exact False.elim (hxy_ne (by simpa [htarget', hy_eq_target]))
        · by_cases hyTerm : y ∈ M.good.terminalSet
          · rcases Relation.ReflTransGen.cases_head hstTarget with hEqTail | htail
            · have hytarget : y = target := congrArg Prod.fst hEqTail
              exact False.elim
                (htargetNonterminal (by simpa [hytarget] using hyTerm))
            · rcases htail with ⟨st₂, hyst₂, _hst₂Target⟩
              rcases st₂ with ⟨z, cz⟩
              rcases hyst₂ with ⟨hnext, hcz⟩
              have hczRed : cz = TwoPairColor.red := by
                simpa using hcz
              subst cz
              exact False.elim
                (M.false_of_colorEdge_into_terminal_and_swapped_colorEdge_out
                  hdeg hdisj hyTerm
                  (c := TwoPairColor.red)
                  ⟨i, hredEdge, hredBefore, hxy_ne⟩ hnext)
          · have hredPack :
                s(x, y) ∈ P.toPathPacking.edgeSet :=
              (P.toPathPacking.mem_edgeSet).2 ⟨i, hredEdge⟩
            have hxBlue :
                x ∈ Q.toPathPacking.vertexSet :=
              M.blue_vertex_of_red_edge_left_not_mem_terminalSet
                hxTerm hyTerm hredPack
            rcases (Q.toPathPacking.mem_vertexSet).1 hxBlue with
              ⟨j, hxBluePath⟩
            have hx_not_blue_source :
                x ≠ (Q.path j).source :=
              (M.good.blue_internal_of_mem_vertexSet_of_not_terminal
                hxTerm).1
            rcases TwoPairColorEdge.exists_blue_backward_of_mem_not_source
                (P := P) (Q := Q) hxBluePath hx_not_blue_source with
              ⟨z, hblue⟩
            exact False.elim
              (hnopred (z, TwoPairColor.blue) ⟨hblue, by simp⟩)
    | blue =>
        have hcyRed : cy = TwoPairColor.red := by
          simpa using hcy
        subst cy
        rcases hcolor with ⟨j, hblueEdge, hblueBefore, hxy_ne⟩
        have hxBlue : x ∈ (Q.path j).vertexSet :=
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (Q.path j) hblueEdge).1
        by_cases hxTerm : x ∈ M.good.terminalSet
        · rcases M.good.isEndpoint_of_mem_terminalSet_of_mem_path
              hdeg hxTerm (Q.path j) hxBlue with hsource | htarget'
          · refine ⟨Sum.inr j, ?_⟩
            simp [TwoPairStartIndex.state, P, Q, hsource]
          · have hyBlue : y ∈ (Q.path j).vertexSet :=
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (Q.path j) hblueEdge).2
            have hyt : (Q.path j).Before y (Q.path j).target :=
              (Q.path j).before_target_of_mem hyBlue
            have hty : (Q.path j).Before (Q.path j).target y := by
              simpa [htarget'] using hblueBefore
            have hy_eq_target : y = (Q.path j).target :=
              (Q.path j).before_antisymm hyt hty
            exact False.elim (hxy_ne (by simpa [htarget', hy_eq_target]))
        · by_cases hyTerm : y ∈ M.good.terminalSet
          · rcases Relation.ReflTransGen.cases_head hstTarget with hEqTail | htail
            · have hytarget : y = target := congrArg Prod.fst hEqTail
              exact False.elim
                (htargetNonterminal (by simpa [hytarget] using hyTerm))
            · rcases htail with ⟨st₂, hyst₂, _hst₂Target⟩
              rcases st₂ with ⟨z, cz⟩
              rcases hyst₂ with ⟨hnext, hcz⟩
              have hczBlue : cz = TwoPairColor.blue := by
                simpa using hcz
              subst cz
              exact False.elim
                (M.false_of_colorEdge_into_terminal_and_swapped_colorEdge_out
                  hdeg hdisj hyTerm
                  (c := TwoPairColor.blue)
                  ⟨j, hblueEdge, hblueBefore, hxy_ne⟩ hnext)
          · have hbluePack :
                s(x, y) ∈ Q.toPathPacking.edgeSet :=
              (Q.toPathPacking.mem_edgeSet).2 ⟨j, hblueEdge⟩
            have hxRed :
                x ∈ P.toPathPacking.vertexSet :=
              M.red_vertex_of_blue_edge_left_not_mem_terminalSet
                hxTerm hyTerm hbluePack
            rcases (P.toPathPacking.mem_vertexSet).1 hxRed with
              ⟨i, hxRedPath⟩
            have hx_not_red_source :
                x ≠ (P.path i).source :=
              (M.good.red_internal_of_mem_vertexSet_of_not_terminal
                hxTerm).1
            rcases TwoPairColorEdge.exists_red_backward_of_mem_not_source
                (P := P) (Q := Q) hxRedPath hx_not_red_source with
              ⟨z, hred⟩
            exact False.elim
              (hnopred (z, TwoPairColor.red) ⟨hred, by simp⟩)

omit [Fintype V] in
/-- Branch-restricted Claim 2.5: every high-degree vertex has an alternating
occurrence reached from one of the canonical red/blue source states. -/
theorem exists_start_reaches_branchVertex
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {v : W}
    (hv :
      v ∈ branchVertexFinset
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)) :
    ∃ a : TwoPairStartIndex M.good.redRouting M.good.blueRouting,
      ∃ c : TwoPairColor,
        Relation.ReflTransGen
          (TwoPairAltStep M.good.redRouting M.good.blueRouting)
          (TwoPairStartIndex.state
            (P := M.good.redRouting) (Q := M.good.blueRouting) a)
          (v, c) := by
  classical
  let rel :=
    TwoPairAltStep M.good.redRouting M.good.blueRouting
  let rho :=
    Lax17Proofs.SimpleGraph.PathSlicing.topologicalRankOfAcyclicRelation
      rel (M.altStep_acyclic hdeg hdisj)
  rcases exists_reflTransGen_minimal_predecessor rel rho
      (v, TwoPairColor.blue) with
    ⟨s, hsv, hs_min⟩
  rcases s with ⟨sx, sc⟩
  rcases M.exists_startIndex_state_eq_of_no_predecessor_of_reaches_branchVertex
      hdeg hdisj hv hsv (by
        intro st hpred
        exact hs_min st hpred) with
    ⟨a, ha⟩
  refine ⟨a, TwoPairColor.blue, ?_⟩
  simpa [ha] using hsv

omit [Fintype V] in
/-- A backwards-minimal alternating state that has an outgoing colored edge is
one of the canonical source states. -/
theorem exists_startIndex_state_eq_of_no_predecessor_of_colorEdge
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x y : W} {c : TwoPairColor}
    (hout :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting c x y)
    (hnopred :
      ∀ st : TwoPairAltState W,
        ¬ TwoPairAltStep M.good.redRouting M.good.blueRouting st (x, c)) :
    ∃ a : TwoPairStartIndex M.good.redRouting M.good.blueRouting,
      TwoPairStartIndex.state
        (P := M.good.redRouting) (Q := M.good.blueRouting) a = (x, c) := by
  classical
  cases c with
  | red =>
      rcases hout with ⟨i, hredEdge, hredBefore, hxy_ne⟩
      have hxRed : x ∈ (M.good.redRouting.path i).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (M.good.redRouting.path i) hredEdge).1
      by_cases hxTerm : x ∈ M.good.terminalSet
      · rcases M.good.isEndpoint_of_mem_terminalSet_of_mem_path
            hdeg hxTerm (M.good.redRouting.path i) hxRed with hsource | htarget
        · refine ⟨Sum.inl i, ?_⟩
          simp [TwoPairStartIndex.state, hsource]
        · have hyRed : y ∈ (M.good.redRouting.path i).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.redRouting.path i) hredEdge).2
          have hyt :
              (M.good.redRouting.path i).Before y
                (M.good.redRouting.path i).target :=
            (M.good.redRouting.path i).before_target_of_mem hyRed
          have hty :
              (M.good.redRouting.path i).Before
                (M.good.redRouting.path i).target y := by
            simpa [htarget] using hredBefore
          have hy_eq_target :
              y = (M.good.redRouting.path i).target :=
            (M.good.redRouting.path i).before_antisymm hyt hty
          exact False.elim (hxy_ne (by simpa [htarget, hy_eq_target]))
      · rcases (M.good.blueRouting.toPathPacking.mem_vertexSet).1
            (C.blue_vertex hxTerm) with ⟨j, hxBlue⟩
        have hx_not_blue_source :
            x ≠ (M.good.blueRouting.path j).source :=
          (M.good.blue_internal_of_mem_vertexSet_of_not_terminal hxTerm).1
        rcases TwoPairColorEdge.exists_blue_backward_of_mem_not_source
            (P := M.good.redRouting) (Q := M.good.blueRouting)
            hxBlue hx_not_blue_source with ⟨z, hzxBlue⟩
        exact False.elim
          (hnopred (z, TwoPairColor.blue) ⟨hzxBlue, by simp⟩)
  | blue =>
      rcases hout with ⟨j, hblueEdge, hblueBefore, hxy_ne⟩
      have hxBlue : x ∈ (M.good.blueRouting.path j).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (M.good.blueRouting.path j) hblueEdge).1
      by_cases hxTerm : x ∈ M.good.terminalSet
      · rcases M.good.isEndpoint_of_mem_terminalSet_of_mem_path
            hdeg hxTerm (M.good.blueRouting.path j) hxBlue with hsource | htarget
        · refine ⟨Sum.inr j, ?_⟩
          simp [TwoPairStartIndex.state, hsource]
        · have hyBlue : y ∈ (M.good.blueRouting.path j).vertexSet :=
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (M.good.blueRouting.path j) hblueEdge).2
          have hyt :
              (M.good.blueRouting.path j).Before y
                (M.good.blueRouting.path j).target :=
            (M.good.blueRouting.path j).before_target_of_mem hyBlue
          have hty :
              (M.good.blueRouting.path j).Before
                (M.good.blueRouting.path j).target y := by
            simpa [htarget] using hblueBefore
          have hy_eq_target :
              y = (M.good.blueRouting.path j).target :=
            (M.good.blueRouting.path j).before_antisymm hyt hty
          exact False.elim (hxy_ne (by simpa [htarget, hy_eq_target]))
      · rcases (M.good.redRouting.toPathPacking.mem_vertexSet).1
            (C.red_vertex hxTerm) with ⟨i, hxRed⟩
        have hx_not_red_source :
            x ≠ (M.good.redRouting.path i).source :=
          (M.good.red_internal_of_mem_vertexSet_of_not_terminal hxTerm).1
        rcases TwoPairColorEdge.exists_red_backward_of_mem_not_source
            (P := M.good.redRouting) (Q := M.good.blueRouting)
            hxRed hx_not_red_source with ⟨z, hzxRed⟩
        exact False.elim
          (hnopred (z, TwoPairColor.red) ⟨hzxRed, by simp⟩)

omit [Fintype V] in
/-- Claim 2.5 for the tail of a directed colored edge: the state immediately
before traversing that edge is reached from a canonical source state. -/
theorem exists_start_reaches_tail_of_colorEdge
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x y : W} {c : TwoPairColor}
    (hout :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting c x y) :
    ∃ a : TwoPairStartIndex M.good.redRouting M.good.blueRouting,
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (TwoPairStartIndex.state
          (P := M.good.redRouting) (Q := M.good.blueRouting) a)
        (x, c) := by
  classical
  let rel :=
    TwoPairAltStep M.good.redRouting M.good.blueRouting
  let rho :=
    Lax17Proofs.SimpleGraph.PathSlicing.topologicalRankOfAcyclicRelation
      rel (M.altStep_acyclic hdeg hdisj)
  rcases exists_reflTransGen_minimal_predecessor rel rho (x, c) with
    ⟨s, hsx, hs_min⟩
  have hs_out : ∃ t : TwoPairAltState W, rel s t := by
    rcases Relation.ReflTransGen.cases_head hsx with hEq | hhead
    · subst s
      exact ⟨(y, c.swap), ⟨hout, rfl⟩⟩
    · rcases hhead with ⟨t, hst, _htx⟩
      exact ⟨t, hst⟩
  rcases s with ⟨sx, sc⟩
  rcases hs_out with ⟨t, hst⟩
  rcases t with ⟨ty, tc⟩
  have hst' :
      TwoPairAltStep M.good.redRouting M.good.blueRouting
        (sx, sc) (ty, tc) := hst
  rcases hst with ⟨hcolor, _htc⟩
  rcases M.exists_startIndex_state_eq_of_no_predecessor_of_colorEdge
      C hdeg hdisj hcolor (by
        intro st hpred
        exact hs_min st hpred) with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [ha] using hsx

omit [Fintype V] in
/-- Claim 2.5 for the head of a directed colored edge. -/
theorem exists_start_reaches_head_of_colorEdge
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {x y : W} {c : TwoPairColor}
    (hout :
      TwoPairColorEdge M.good.redRouting M.good.blueRouting c x y) :
    ∃ a : TwoPairStartIndex M.good.redRouting M.good.blueRouting,
      Relation.ReflTransGen
        (TwoPairAltStep M.good.redRouting M.good.blueRouting)
        (TwoPairStartIndex.state
          (P := M.good.redRouting) (Q := M.good.blueRouting) a)
        (y, c.swap) := by
  rcases M.exists_start_reaches_tail_of_colorEdge C hdeg hdisj hout with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  exact Relation.ReflTransGen.tail ha ⟨hout, rfl⟩

omit [Fintype V] in
/-- Claim 2.5 in vertex form: every vertex has some alternating occurrence
reached from one of the canonical red/blue source states. -/
theorem exists_start_reaches_vertex
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (v : W) :
    ∃ a : TwoPairStartIndex M.good.redRouting M.good.blueRouting,
      ∃ c : TwoPairColor,
        Relation.ReflTransGen
          (TwoPairAltStep M.good.redRouting M.good.blueRouting)
          (TwoPairStartIndex.state
            (P := M.good.redRouting) (Q := M.good.blueRouting) a)
          (v, c) := by
  classical
  by_cases hvTerm : v ∈ M.good.terminalSet
  · have hvCases :
        v ∈ M.good.respecting.terminalImage S₁
              (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) ∨
          v ∈ M.good.respecting.terminalImage T₁
              (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂) ∨
          v ∈ M.good.respecting.terminalImage S₂
              (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) ∨
          v ∈ M.good.respecting.terminalImage T₂
              (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂) := by
      simpa [TwoPairGoodMinor.terminalSet, twoPairTerminalSet] using hvTerm
    rcases hvCases with hvS₁ | hvT₁ | hvS₂ | hvT₂
    · let i :=
        M.good.redRouting.indexOfSource ⟨v, hvS₁⟩
      have hsource :
          (M.good.redRouting.path i).source = v := by
        exact congrArg Subtype.val
          (M.good.redRouting.source_indexOfSource ⟨v, hvS₁⟩)
      refine ⟨Sum.inl i, TwoPairColor.red, ?_⟩
      change
        Relation.ReflTransGen
          (TwoPairAltStep M.good.redRouting M.good.blueRouting)
          ((M.good.redRouting.path i).source, TwoPairColor.red)
          (v, TwoPairColor.red)
      simpa [hsource] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen
            (TwoPairAltStep M.good.redRouting M.good.blueRouting)
            ((M.good.redRouting.path i).source, TwoPairColor.red)
            ((M.good.redRouting.path i).source, TwoPairColor.red))
    · let i :=
        M.good.redRouting.indexOfTarget ⟨v, hvT₁⟩
      have htarget :
          (M.good.redRouting.path i).target = v := by
        exact congrArg Subtype.val
          (M.good.redRouting.target_indexOfTarget ⟨v, hvT₁⟩)
      have hvPath : v ∈ (M.good.redRouting.path i).vertexSet := by
        simpa [htarget] using
          GraphPath.target_mem_vertexSet (M.good.redRouting.path i)
      have hsource_ne_target :
          (M.good.redRouting.path i).source ≠
            (M.good.redRouting.path i).target := by
        intro hst
        have hvS₁' :
            v ∈ M.good.respecting.terminalImage S₁
              (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) := by
          simpa [htarget, hst] using M.good.redRouting.source_mem i
        have hS₁T₁ := (M.good.terminalImagesDisjoint hdisj).1
        exact Finset.disjoint_left.mp hS₁T₁ hvS₁' hvT₁
      have hv_not_source :
          v ≠ (M.good.redRouting.path i).source := by
        intro hvsrc
        exact hsource_ne_target (by simpa [hvsrc, htarget])
      rcases TwoPairColorEdge.exists_red_backward_of_mem_not_source
          (P := M.good.redRouting) (Q := M.good.blueRouting)
          hvPath hv_not_source with ⟨z, hred⟩
      rcases M.exists_start_reaches_head_of_colorEdge
          C hdeg hdisj hred with ⟨a, ha⟩
      exact ⟨a, TwoPairColor.blue, by simpa using ha⟩
    · let j :=
        M.good.blueRouting.indexOfSource ⟨v, hvS₂⟩
      have hsource :
          (M.good.blueRouting.path j).source = v := by
        exact congrArg Subtype.val
          (M.good.blueRouting.source_indexOfSource ⟨v, hvS₂⟩)
      refine ⟨Sum.inr j, TwoPairColor.blue, ?_⟩
      change
        Relation.ReflTransGen
          (TwoPairAltStep M.good.redRouting M.good.blueRouting)
          ((M.good.blueRouting.path j).source, TwoPairColor.blue)
          (v, TwoPairColor.blue)
      simpa [hsource] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen
            (TwoPairAltStep M.good.redRouting M.good.blueRouting)
            ((M.good.blueRouting.path j).source, TwoPairColor.blue)
            ((M.good.blueRouting.path j).source, TwoPairColor.blue))
    · let j :=
        M.good.blueRouting.indexOfTarget ⟨v, hvT₂⟩
      have htarget :
          (M.good.blueRouting.path j).target = v := by
        exact congrArg Subtype.val
          (M.good.blueRouting.target_indexOfTarget ⟨v, hvT₂⟩)
      have hvPath : v ∈ (M.good.blueRouting.path j).vertexSet := by
        simpa [htarget] using
          GraphPath.target_mem_vertexSet (M.good.blueRouting.path j)
      have hsource_ne_target :
          (M.good.blueRouting.path j).source ≠
            (M.good.blueRouting.path j).target := by
        intro hst
        have hvS₂' :
            v ∈ M.good.respecting.terminalImage S₂
              (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂) := by
          simpa [htarget, hst] using M.good.blueRouting.source_mem j
        have hS₂T₂ := (M.good.terminalImagesDisjoint hdisj).2.2.2.2.2
        exact Finset.disjoint_left.mp hS₂T₂ hvS₂' hvT₂
      have hv_not_source :
          v ≠ (M.good.blueRouting.path j).source := by
        intro hvsrc
        exact hsource_ne_target (by simpa [hvsrc, htarget])
      rcases TwoPairColorEdge.exists_blue_backward_of_mem_not_source
          (P := M.good.redRouting) (Q := M.good.blueRouting)
          hvPath hv_not_source with ⟨z, hblue⟩
      rcases M.exists_start_reaches_head_of_colorEdge
          C hdeg hdisj hblue with ⟨a, ha⟩
      exact ⟨a, TwoPairColor.red, by simpa using ha⟩
  · rcases (M.good.redRouting.toPathPacking.mem_vertexSet).1
        (C.red_vertex hvTerm) with ⟨i, hvRed⟩
    have hv_not_source :
        v ≠ (M.good.redRouting.path i).source :=
      (M.good.red_internal_of_mem_vertexSet_of_not_terminal hvTerm).1
    rcases TwoPairColorEdge.exists_red_backward_of_mem_not_source
        (P := M.good.redRouting) (Q := M.good.blueRouting)
        hvRed hv_not_source with ⟨z, hred⟩
    rcases M.exists_start_reaches_head_of_colorEdge
        C hdeg hdisj hred with ⟨a, ha⟩
    exact ⟨a, TwoPairColor.blue, by simpa using ha⟩

omit [Fintype V] in
/-- The forward reachability-cover form of Theorem 2.2 for a minimal good
minor, assuming the local core-incidence facts from the minimality argument. -/
noncomputable def forwardReachCoverOfCoreIncidence
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {k : ℕ}
    (defaultState : TwoPairAltState W)
    (hredCard : M.good.redRouting.card ≤ k)
    (hblueCard : M.good.blueRouting.card ≤ k) :
    TwoPairForwardReachCover M.good.redRouting M.good.blueRouting k :=
  TwoPairForwardReachCover.ofCanonicalReach defaultState hredCard hblueCard
    (M.exists_start_reaches_vertex C hdeg hdisj)
    (fun i _sx _sy hxy hx hy =>
      M.red_order_of_altStep_same_path hdeg hdisj hxy hx hy)
    (fun j _sx _sy hxy hx hy =>
      M.blue_order_of_altStep_same_path hdeg hdisj hxy hx hy)

omit [Fintype V] in
/-- The reversed-red reachability-cover form of Theorem 2.2 for a minimal
good minor, obtained by applying the forward construction to the instance with
the first terminal pair reversed. -/
noncomputable def reverseRedReachCoverOfCoreIncidence
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {k : ℕ}
    (defaultState : TwoPairAltState W)
    (hredCard : M.good.redRouting.card ≤ k)
    (hblueCard : M.good.blueRouting.card ≤ k) :
    TwoPairReverseRedReachCover M.good.redRouting M.good.blueRouting k := by
  classical
  let Mrev := M.reverseRed
  have hdegSwap :
      ∀ x : V, x ∈ twoPairTerminalSet T₁ S₁ S₂ T₂ →
        DegreeEquals G x 1 := by
    intro x hx
    exact hdeg x (by
      simpa [twoPairTerminalSet_swap_first S₁ T₁ S₂ T₂] using hx)
  have hredCardRev : Mrev.good.redRouting.card ≤ k := by
    simpa [Mrev, TwoPairMinimalGoodMinor.reverseRed, TwoPairGoodMinor.reverseRed]
      using hredCard
  have hblueCardRev : Mrev.good.blueRouting.card ≤ k := by
    simpa [Mrev, TwoPairMinimalGoodMinor.reverseRed, TwoPairGoodMinor.reverseRed]
      using hblueCard
  let Z :=
    Mrev.forwardReachCoverOfCoreIncidence
      C.reverseRed hdegSwap hdisj.swap_first defaultState
      hredCardRev hblueCardRev
  have Z' :
      TwoPairForwardReachCover M.good.redRouting.reverse
        M.good.blueRouting k := by
    simpa [Z, Mrev, TwoPairMinimalGoodMinor.reverseRed,
      TwoPairGoodMinor.reverseRed] using Z
  exact Z'.toReverseRedReachCoverOfReverse

omit [Fintype V] in
/-- Branch-restricted forward reachability-cover form of Theorem 2.2 for a
minimal good minor, assuming the local core-incidence facts. -/
noncomputable def branchForwardReachCoverOfCoreIncidence
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {k : ℕ}
    (defaultState : TwoPairAltState W)
    (hredCard : M.good.redRouting.card ≤ k)
    (hblueCard : M.good.blueRouting.card ≤ k) :
    TwoPairBranchForwardReachCover M.good.redRouting M.good.blueRouting k :=
  TwoPairBranchForwardReachCover.ofCanonicalBranchReach
    defaultState hredCard hblueCard
    (fun {v} _hv => M.exists_start_reaches_vertex C hdeg hdisj v)
    (fun i _sx _sy hxy hx hy =>
      M.red_order_of_altStep_same_path hdeg hdisj hxy hx hy)
    (fun j _sx _sy hxy hx hy =>
      M.blue_order_of_altStep_same_path hdeg hdisj hxy hx hy)

omit [Fintype V] in
/-- Branch-restricted reversed-red reachability-cover form of Theorem 2.2 for
a minimal good minor, assuming the local core-incidence facts. -/
noncomputable def branchReverseRedReachCoverOfCoreIncidence
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {k : ℕ}
    (defaultState : TwoPairAltState W)
    (hredCard : M.good.redRouting.card ≤ k)
    (hblueCard : M.good.blueRouting.card ≤ k) :
    TwoPairBranchReverseRedReachCover M.good.redRouting M.good.blueRouting k := by
  classical
  let Mrev := M.reverseRed
  have hdegSwap :
      ∀ x : V, x ∈ twoPairTerminalSet T₁ S₁ S₂ T₂ →
        DegreeEquals G x 1 := by
    intro x hx
    exact hdeg x (by
      simpa [twoPairTerminalSet_swap_first S₁ T₁ S₂ T₂] using hx)
  have hredCardRev : Mrev.good.redRouting.card ≤ k := by
    simpa [Mrev, TwoPairMinimalGoodMinor.reverseRed, TwoPairGoodMinor.reverseRed]
      using hredCard
  have hblueCardRev : Mrev.good.blueRouting.card ≤ k := by
    simpa [Mrev, TwoPairMinimalGoodMinor.reverseRed, TwoPairGoodMinor.reverseRed]
      using hblueCard
  let Z :=
    Mrev.branchForwardReachCoverOfCoreIncidence
      C.reverseRed hdegSwap hdisj.swap_first defaultState
      hredCardRev hblueCardRev
  have Z' :
      TwoPairBranchForwardReachCover M.good.redRouting.reverse
        M.good.blueRouting k := by
    simpa [Z, Mrev, TwoPairMinimalGoodMinor.reverseRed,
      TwoPairGoodMinor.reverseRed] using Z
  exact Z'.toBranchReverseRedReachCoverOfReverse

omit [Fintype V] in
/-- Branch-restricted forward reachability-cover form of Theorem 2.2 for a
minimal good minor, derived directly from minimality. -/
noncomputable def branchForwardReachCoverOfMinimality
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {k : ℕ}
    (defaultState : TwoPairAltState W)
    (hredCard : M.good.redRouting.card ≤ k)
    (hblueCard : M.good.blueRouting.card ≤ k) :
    TwoPairBranchForwardReachCover M.good.redRouting M.good.blueRouting k :=
  TwoPairBranchForwardReachCover.ofCanonicalBranchReach
    defaultState hredCard hblueCard
    (fun {v} hv => M.exists_start_reaches_branchVertex hdeg hdisj hv)
    (fun i _sx _sy hxy hx hy =>
      M.red_order_of_altStep_same_path hdeg hdisj hxy hx hy)
    (fun j _sx _sy hxy hx hy =>
      M.blue_order_of_altStep_same_path hdeg hdisj hxy hx hy)

omit [Fintype V] in
/-- Branch-restricted reversed-red reachability-cover form of Theorem 2.2 for
a minimal good minor, derived directly from minimality. -/
noncomputable def branchReverseRedReachCoverOfMinimality
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    {k : ℕ}
    (defaultState : TwoPairAltState W)
    (hredCard : M.good.redRouting.card ≤ k)
    (hblueCard : M.good.blueRouting.card ≤ k) :
    TwoPairBranchReverseRedReachCover M.good.redRouting M.good.blueRouting k := by
  classical
  let Mrev := M.reverseRed
  have hdegSwap :
      ∀ x : V, x ∈ twoPairTerminalSet T₁ S₁ S₂ T₂ →
        DegreeEquals G x 1 := by
    intro x hx
    exact hdeg x (by
      simpa [twoPairTerminalSet_swap_first S₁ T₁ S₂ T₂] using hx)
  have hredCardRev : Mrev.good.redRouting.card ≤ k := by
    simpa [Mrev, TwoPairMinimalGoodMinor.reverseRed, TwoPairGoodMinor.reverseRed]
      using hredCard
  have hblueCardRev : Mrev.good.blueRouting.card ≤ k := by
    simpa [Mrev, TwoPairMinimalGoodMinor.reverseRed, TwoPairGoodMinor.reverseRed]
      using hblueCard
  let Z :=
    Mrev.branchForwardReachCoverOfMinimality
      hdegSwap hdisj.swap_first defaultState hredCardRev hblueCardRev
  have Z' :
      TwoPairBranchForwardReachCover M.good.redRouting.reverse
        M.good.blueRouting k := by
    simpa [Z, Mrev, TwoPairMinimalGoodMinor.reverseRed,
      TwoPairGoodMinor.reverseRed] using Z
  exact Z'.toBranchReverseRedReachCoverOfReverse

end TwoPairMinimalGoodMinor

namespace TwoPairMinimalGoodMinor

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S₁ T₁ S₂ T₂ : Finset V}

omit [Fintype V] in
/-- A minimal-core certificate for the selected routings supplies the local
core-incidence facts used by the reachability construction. -/
theorem coreIncidence_of_minimalCoreCertificate
    [Fintype W]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (K :
      TwoPairMinimalCoreCertificate
        M.good.redRouting M.good.blueRouting)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    TwoPairGoodMinorCoreIncidence M.good where
  red_vertex := by
    classical
    intro v hv
    have hvT :
        v ∉ twoPairTerminalSet
          (M.good.respecting.terminalImage S₁
            (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
          (M.good.respecting.terminalImage T₁
            (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
          (M.good.respecting.terminalImage S₂
            (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
          (M.good.respecting.terminalImage T₂
            (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) := by
      simpa [TwoPairGoodMinor.terminalSet] using hv
    exact TwoPairBranchCarrier.red_vertexSet_mem_of_branchVertex
      (P := M.good.redRouting) (Q := M.good.blueRouting)
      (K.nonterminal_branch hvT)
  blue_vertex := by
    classical
    intro v hv
    have hvT :
        v ∉ twoPairTerminalSet
          (M.good.respecting.terminalImage S₁
            (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
          (M.good.respecting.terminalImage T₁
            (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
          (M.good.respecting.terminalImage S₂
            (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
          (M.good.respecting.terminalImage T₂
            (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)) := by
      simpa [TwoPairGoodMinor.terminalSet] using hv
    exact TwoPairBranchCarrier.blue_vertexSet_mem_of_branchVertex
      (P := M.good.redRouting) (Q := M.good.blueRouting)
      (K.nonterminal_branch hvT)
  no_nonterminal_shared_edge := by
    intro v w hv hred hblue
    exact M.false_of_red_and_blue_incident_nonterminal
      hdeg hdisj hv hred hblue

end TwoPairMinimalGoodMinor

namespace TwoPairMinimalCoreCertificate

variable {G : _root_.SimpleGraph V}
variable {S₁ T₁ S₂ T₂ : Finset V}
variable {P : PerfectPathPacking G S₁ T₁}
variable {Q : PerfectPathPacking G S₂ T₂}

/-- If all nonterminals are high-degree vertices in the union graph, then the
total vertex count is at most `τ` plus the number of terminals. -/
theorem vertexCount_le_branchVertexCount_add_terminalCount
    (M : TwoPairMinimalCoreCertificate P Q) :
    Fintype.card V ≤
      branchVertexCount (twoPackingUnionGraph P Q) +
        (twoPairTerminalSet S₁ T₁ S₂ T₂).card := by
  classical
  let B := branchVertexFinset (twoPackingUnionGraph P Q)
  let T := twoPairTerminalSet S₁ T₁ S₂ T₂
  have huniv : (Finset.univ : Finset V) ⊆ B ∪ T := by
    intro v _
    by_cases hT : v ∈ T
    · exact Finset.mem_union.2 (Or.inr hT)
    · exact Finset.mem_union.2 (Or.inl (M.nonterminal_branch hT))
  have hcard :
      Fintype.card V ≤ (B ∪ T).card := by
    simpa using Finset.card_le_card huniv
  have hunion : (B ∪ T).card ≤ B.card + T.card :=
    Finset.card_union_le B T
  have hmain : Fintype.card V ≤ B.card + T.card :=
    hcard.trans hunion
  simpa [B, T, branchVertexCount, branchVertexFinset] using hmain

end TwoPairMinimalCoreCertificate

/-- Theorem 2.1's numerical conclusion from the Section 2 structural
minimal-core facts and the two chain labelings. -/
theorem theorem21_minimal_core_bound_of_chainLabelCertificate
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (C : TwoPairChainLabelCertificate P Q k)
    (M : TwoPairMinimalCoreCertificate P Q)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card V ≤ 4 * k ^ 4 + 4 * k := by
  have hPcard : P.card ≤ k := by
    rw [P.card_eq_left_card]
    exact hS₁
  have hQcard : Q.card ≤ k := by
    rw [Q.card_eq_left_card]
    exact hS₂
  have hbranch :
      branchVertexCount (twoPackingUnionGraph P Q) ≤ 4 * k ^ 4 :=
    C.branchVertexCount_le_four_mul_pow hPcard hQcard
  have hterm :
      (twoPairTerminalSet S₁ T₁ S₂ T₂).card ≤ 4 * k :=
    twoPairTerminalSet_card_le_four_mul hS₁ hT₁ hS₂ hT₂
  exact
    (M.vertexCount_le_branchVertexCount_add_terminalCount).trans
      (Nat.add_le_add hbranch hterm)

/-- Theorem 2.1's numerical conclusion from the split Section 2 ingredients:
forward labels, reversed-red labels, branch-path incidence, and the minimal-core
nonterminal condition. -/
theorem theorem21_minimal_core_bound_of_labelings
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (L : TwoPairForwardLabeling P Q k)
    (Lrev : TwoPairReverseRedLabeling P Q k)
    (M : TwoPairMinimalCoreCertificate P Q)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card V ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_core_bound_of_chainLabelCertificate P Q
    (TwoPairChainLabelCertificate.ofLabelingsAndPackings L Lrev) M
    hS₁ hT₁ hS₂ hT₂

/-- Theorem 2.1's numerical conclusion from the paper's local internal-core
minimality consequences and the two Theorem 2.2 labelings. -/
theorem theorem21_minimal_core_bound_of_internalCore_and_labelings
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (L : TwoPairForwardLabeling P Q k)
    (Lrev : TwoPairReverseRedLabeling P Q k)
    (C : TwoPairInternalCoreCertificate P Q)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card V ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_core_bound_of_labelings P Q L Lrev
    C.toMinimalCoreCertificate hS₁ hT₁ hS₂ hT₂

/-- Theorem 2.1's numerical conclusion from the reachability-cover form of
Theorem 2.2 and the minimal-core facts. -/
theorem theorem21_minimal_core_bound_of_reachCovers
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (Z : TwoPairForwardReachCover P Q k)
    (Zrev : TwoPairReverseRedReachCover P Q k)
    (M : TwoPairMinimalCoreCertificate P Q)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card V ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_core_bound_of_labelings P Q
    Z.toForwardLabeling Zrev.toReverseRedLabeling M
    hS₁ hT₁ hS₂ hT₂

/-- Theorem 2.1's numerical conclusion from the local internal-core facts and
the reachability-cover form of Theorem 2.2. -/
theorem theorem21_minimal_core_bound_of_internalCore_and_reachCovers
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (Z : TwoPairForwardReachCover P Q k)
    (Zrev : TwoPairReverseRedReachCover P Q k)
    (C : TwoPairInternalCoreCertificate P Q)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card V ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_core_bound_of_reachCovers P Q Z Zrev
    C.toMinimalCoreCertificate hS₁ hT₁ hS₂ hT₂

/-- Theorem 2.1's numerical conclusion from the chain-cover form of Theorem
2.2 and the minimal-core facts. -/
theorem theorem21_minimal_core_bound_of_chainCovers
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (Z : TwoPairForwardChainCover P Q k)
    (Zrev : TwoPairReverseRedChainCover P Q k)
    (M : TwoPairMinimalCoreCertificate P Q)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card V ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_core_bound_of_labelings P Q
    Z.toForwardLabeling Zrev.toReverseRedLabeling M
    hS₁ hT₁ hS₂ hT₂

/-- Theorem 2.1's numerical conclusion from the paper's local internal-core
minimality consequences and the chain-cover form of Theorem 2.2. -/
theorem theorem21_minimal_core_bound_of_internalCore_and_chainCovers
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (Z : TwoPairForwardChainCover P Q k)
    (Zrev : TwoPairReverseRedChainCover P Q k)
    (C : TwoPairInternalCoreCertificate P Q)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card V ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_core_bound_of_internalCore_and_labelings P Q
    Z.toForwardLabeling Zrev.toReverseRedLabeling C
    hS₁ hT₁ hS₂ hT₂

omit [Fintype V] in
/-- Theorem 2.1 in the good-minor setting, once the Section 2 internal-core
facts and chain covers have been constructed in the minimal minor. -/
theorem theorem21_minimal_good_bound_of_internalCore_and_chainCovers
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (Z : TwoPairForwardChainCover M.good.redRouting M.good.blueRouting k)
    (Zrev : TwoPairReverseRedChainCover M.good.redRouting M.good.blueRouting k)
    (C : TwoPairInternalCoreCertificate M.good.redRouting M.good.blueRouting)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card W ≤ 4 * k ^ 4 + 4 * k := by
  have hS₁' :
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hS₁
  have hT₁' :
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hT₁
  have hS₂' :
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hS₂
  have hT₂' :
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hT₂
  exact theorem21_minimal_core_bound_of_internalCore_and_chainCovers
    M.good.redRouting M.good.blueRouting Z Zrev C
    hS₁' hT₁' hS₂' hT₂'

omit [Fintype V] in
/-- Theorem 2.1 in the good-minor setting, once the Section 2 internal-core
facts and reachability covers have been constructed in the minimal minor. -/
theorem theorem21_minimal_good_bound_of_internalCore_and_reachCovers
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (Z : TwoPairForwardReachCover M.good.redRouting M.good.blueRouting k)
    (Zrev : TwoPairReverseRedReachCover M.good.redRouting M.good.blueRouting k)
    (C : TwoPairInternalCoreCertificate M.good.redRouting M.good.blueRouting)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card W ≤ 4 * k ^ 4 + 4 * k := by
  have hS₁' :
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hS₁
  have hT₁' :
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hT₁
  have hS₂' :
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hS₂
  have hT₂' :
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hT₂
  exact theorem21_minimal_core_bound_of_internalCore_and_reachCovers
    M.good.redRouting M.good.blueRouting Z Zrev C
    hS₁' hT₁' hS₂' hT₂'

omit [Fintype V] in
/-- Theorem 2.1 in the good-minor setting, using the local incidence facts
derived from minimality and the chain-cover form of Theorem 2.2. -/
theorem theorem21_minimal_good_bound_of_coreIncidence_and_chainCovers
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (Z : TwoPairForwardChainCover M.good.redRouting M.good.blueRouting k)
    (Zrev : TwoPairReverseRedChainCover M.good.redRouting M.good.blueRouting k)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card W ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_good_bound_of_internalCore_and_chainCovers
    M Z Zrev C.toInternalCoreCertificate hS₁ hT₁ hS₂ hT₂

omit [Fintype V] in
/-- Theorem 2.1 in the good-minor setting, using the local incidence facts
derived from minimality and the reachability-cover form of Theorem 2.2. -/
theorem theorem21_minimal_good_bound_of_coreIncidence_and_reachCovers
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (Z : TwoPairForwardReachCover M.good.redRouting M.good.blueRouting k)
    (Zrev : TwoPairReverseRedReachCover M.good.redRouting M.good.blueRouting k)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card W ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_good_bound_of_internalCore_and_reachCovers
    M Z Zrev C.toInternalCoreCertificate hS₁ hT₁ hS₂ hT₂

omit [Fintype V] in
/-- Theorem 2.1 in the good-minor setting from the paper's local
core-incidence facts alone; the two Theorem 2.2 reachability covers are built
internally. -/
theorem theorem21_minimal_good_bound_of_coreIncidence
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card W ≤ 4 * k ^ 4 + 4 * k := by
  have hredCard : M.good.redRouting.card ≤ k := by
    rw [M.good.redRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₁
  have hblueCard : M.good.blueRouting.card ≤ k := by
    rw [M.good.blueRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₂
  let Z :=
    M.forwardReachCoverOfCoreIncidence
      C hdeg hdisj defaultState hredCard hblueCard
  let Zrev :=
    M.reverseRedReachCoverOfCoreIncidence
      C hdeg hdisj defaultState hredCard hblueCard
  exact theorem21_minimal_good_bound_of_coreIncidence_and_reachCovers
    M Z Zrev C hS₁ hT₁ hS₂ hT₂

omit [Fintype V] in
/-- Theorem 2.1 in the good-minor setting from the minimal-core condition
used by the paper after the minimality argument. -/
theorem theorem21_minimal_good_bound_of_minimalCoreCertificate
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (K :
      TwoPairMinimalCoreCertificate
        M.good.redRouting M.good.blueRouting)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    Fintype.card W ≤ 4 * k ^ 4 + 4 * k := by
  exact theorem21_minimal_good_bound_of_coreIncidence M
    (M.coreIncidence_of_minimalCoreCertificate K hdeg hdisj)
    hdeg hdisj defaultState hS₁ hT₁ hS₂ hT₂

/-- The degenerate `k₁ = 0` instance of Theorem 1.3.  Routability gives empty
perfect packings, so their union has no high-degree vertices. -/
theorem theorem13_two_pair_routability_sparsifier_zero
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₂ : ℕ}
    (hS₁ : S₁.card = 0) (_hT₁ : T₁.card = 0)
    (hS₂ : S₂.card = k₂) (_hT₂ : T₂.card = k₂)
    (hk₂ : k₂ ≤ 0)
    (hR₁ : RoutableIn G S₁ T₁)
    (hR₂ : RoutableIn G S₂ T₂) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ 0 := by
  classical
  rcases hR₁ with ⟨P⟩
  rcases hR₂ with ⟨Q⟩
  refine ⟨P, Q, ?_⟩
  have hk₂zero : k₂ = 0 := Nat.eq_zero_of_le_zero hk₂
  have hPcard : P.card = 0 := by
    rw [P.card_eq_left_card, hS₁]
  have hQcard : Q.card = 0 := by
    rw [Q.card_eq_left_card, hS₂, hk₂zero]
  have hbranch :
      branchVertexCount (twoPackingUnionGraph P Q) = 0 :=
    branchVertexCount_twoPackingUnionGraph_eq_zero_of_card_eq_zero
      P Q hPcard hQcard
  simp [hbranch]

/-- Theorem 1.3 when the second pair has size zero.  The chosen blue routing is
empty, so the union is a single path packing and has no branch vertices. -/
theorem theorem13_two_pair_routability_sparsifier_blue_empty
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ : ℕ}
    (_hS₁ : S₁.card = k₁) (_hT₁ : T₁.card = k₁)
    (hS₂ : S₂.card = 0) (_hT₂ : T₂.card = 0)
    (_hk₂ : 0 ≤ k₁)
    (hR₁ : RoutableIn G S₁ T₁)
    (hR₂ : RoutableIn G S₂ T₂) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  classical
  rcases hR₁ with ⟨P⟩
  rcases hR₂ with ⟨Q⟩
  refine ⟨P, Q, ?_⟩
  have hQcard : Q.card = 0 := by
    rw [Q.card_eq_left_card, hS₂]
  have hbranch :
      branchVertexCount (twoPackingUnionGraph P Q) = 0 :=
    branchVertexCount_twoPackingUnionGraph_eq_zero_of_blue_card_eq_zero
      P Q hQcard
  simp [hbranch]

omit [Fintype V] in
/-- Theorem 1.3's sparsifier conclusion inside the bounded minimal good minor
constructed by Section 2.  This is the final Section 2 output before expanding
the minor-model routings back to the original graph. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_minimalCore
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (K :
      TwoPairMinimalCoreCertificate
        M.good.redRouting M.good.blueRouting)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    TwoPairRoutingSparsifier H
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))
      k := by
  classical
  refine ⟨M.good.redRouting, M.good.blueRouting, ?_⟩
  have hcard :
      Fintype.card W ≤ 4 * k ^ 4 + 4 * k :=
    theorem21_minimal_good_bound_of_minimalCoreCertificate
      M K hdeg hdisj defaultState hS₁ hT₁ hS₂ hT₂
  have hbranch_card :
      branchVertexCount
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) ≤
        Fintype.card W := by
    change
      (Finset.univ.filter fun v : W =>
        ¬ DegreeAtMost
          (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) v 2).card ≤
        Fintype.card W
    simpa using
      Finset.card_le_univ
        (Finset.univ.filter fun v : W =>
          ¬ DegreeAtMost
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) v 2)
  have hsmall :
      branchVertexCount
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) ≤
          4 * k ^ 4 + 4 * k :=
    hbranch_card.trans hcard
  nlinarith [hsmall, Nat.zero_le (k ^ 4), Nat.zero_le k]

omit [Fintype V] in
/-- The final Section 2 implication in the original host graph, once the
minor-model expansion has been controlled so that each minor branch set
contributes at most two high-degree vertices to the expanded union. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_minimalCore_expansion
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    [Fintype V]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (K :
      TwoPairMinimalCoreCertificate
        M.good.redRouting M.good.blueRouting)
    (E : TwoPairControlledExpansion (W := W) G S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  have hcard :
      Fintype.card W ≤ 4 * k ^ 4 + 4 * k :=
    theorem21_minimal_good_bound_of_minimalCoreCertificate
      M K hdeg hdisj defaultState hS₁ hT₁ hS₂ hT₂
  exact E.toRoutingSparsifier hcard

/-- Host-side Theorem 1.3 implication from a bounded minimal good minor using
the paper's local core-incidence facts directly, together with the controlled
minor-model expansion back to the host graph. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_coreIncidence_expansion
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (E : TwoPairControlledExpansion (W := W) G S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  have hcard :
      Fintype.card W ≤ 4 * k ^ 4 + 4 * k :=
    theorem21_minimal_good_bound_of_coreIncidence
      M C hdeg hdisj defaultState hS₁ hT₁ hS₂ hT₂
  exact E.toRoutingSparsifier hcard

/-- Host-side Theorem 1.3 implication from a minimal good minor with
core-incidence facts, once the naive lifted routings have the local branch-set
`≤ 2` bound. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_coreIncidence_liftedLocalBound
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hlocal : M.good.LiftedRoutingBranchSetLocalBound)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  exact
    theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_coreIncidence_expansion
      M C (M.good.controlledExpansionOfLiftedRoutingLocalBound hlocal)
      hdeg hdisj defaultState hS₁ hT₁ hS₂ hT₂

/-- Host-side Theorem 1.3 implication from a minimal good minor with
core-incidence facts in the paper's two-splice-vertices-per-branch-set form. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_coreIncidence_liftedPairBound
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (a b : W → V)
    (hlocal :
      ∀ w : W,
        ∀ x : {v : V //
            ¬ DegreeAtMost
              (twoPackingUnionGraph
                M.good.liftRedRouting M.good.liftBlueRouting) v 2},
          x.1 ∈ M.good.respecting.model.branchSet w →
            x.1 = a w ∨ x.1 = b w)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  exact
    theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_coreIncidence_expansion
      M C (M.good.controlledExpansionOfLiftedRoutingPairBound a b hlocal)
      hdeg hdisj defaultState hS₁ hT₁ hS₂ hT₂

/-- Host-side Theorem 1.3 implication from a minimal good minor once the
paper's local branch-set expansion bound has been proved for the lifted
routings. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_minimalCore_liftedLocalBound
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    [Fintype V]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (K :
      TwoPairMinimalCoreCertificate
        M.good.redRouting M.good.blueRouting)
    (hlocal : M.good.LiftedRoutingBranchSetLocalBound)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  exact
    theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_minimalCore_expansion
      M K (M.good.controlledExpansionOfLiftedRoutingLocalBound hlocal)
      hdeg hdisj defaultState hS₁ hT₁ hS₂ hT₂

/-- Host-side Theorem 1.3 implication from a minimal good minor in the
paper's splice-vertex form: each branch set has two named vertices containing
all high-degree vertices of the lifted red/blue union. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_minimalCore_liftedPairBound
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    [Fintype V]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (K :
      TwoPairMinimalCoreCertificate
        M.good.redRouting M.good.blueRouting)
    (a b : W → V)
    (hlocal :
      ∀ w : W,
        ∀ x : {v : V //
            ¬ DegreeAtMost
              (twoPackingUnionGraph
                M.good.liftRedRouting M.good.liftBlueRouting) v 2},
          x.1 ∈ M.good.respecting.model.branchSet w →
            x.1 = a w ∨ x.1 = b w)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hT₁ : T₁.card ≤ k)
    (hS₂ : S₂.card ≤ k) (hT₂ : T₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  exact
    theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_minimalCore_expansion
      M K (M.good.controlledExpansionOfLiftedRoutingPairBound a b hlocal)
      hdeg hdisj defaultState hS₁ hT₁ hS₂ hT₂

/-- Theorem 1.3 from the branch-restricted Section 2 chain-label certificate
for the chosen routings.  This is the counting form needed when the formal
minimal-minor model contains harmless one-color terminal stubs. -/
theorem theorem13_two_pair_routability_sparsifier_of_branchChainLabelCertificate
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (C : TwoPairBranchChainLabelCertificate P Q k₁)
    (hS₁ : S₁.card = k₁) (hS₂ : S₂.card ≤ k₁) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  refine ⟨P, Q, ?_⟩
  have hPcard : P.card ≤ k₁ := by
    rw [P.card_eq_left_card, hS₁]
  have hQcard : Q.card ≤ k₁ := by
    rw [Q.card_eq_left_card]
    exact hS₂
  exact C.branchVertexCount_le_theorem13_bound hPcard hQcard

/-- Cardinality-inequality form of the branch-restricted chain-label
certificate conclusion. -/
theorem theorem13_two_pair_routability_sparsifier_of_branchChainLabelCertificate_cardLe
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (C : TwoPairBranchChainLabelCertificate P Q k)
    (hPcard : P.card ≤ k) (hQcard : Q.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  refine ⟨P, Q, ?_⟩
  exact C.branchVertexCount_le_theorem13_bound hPcard hQcard

/-- Theorem 1.3's routing sparsifier conclusion from branch-restricted
forward and reversed-red labelings. -/
theorem theorem13_two_pair_routability_sparsifier_of_branchLabelings
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (L : TwoPairBranchForwardLabeling P Q k₁)
    (Lrev : TwoPairBranchReverseRedLabeling P Q k₁)
    (hS₁ : S₁.card = k₁) (hS₂ : S₂.card ≤ k₁) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  exact
    theorem13_two_pair_routability_sparsifier_of_branchChainLabelCertificate
      S₁ T₁ S₂ T₂ P Q
      (TwoPairBranchChainLabelCertificate.ofBranchLabelings L Lrev)
      hS₁ hS₂

/-- Cardinality-inequality form of the branch-restricted labeling conclusion. -/
theorem theorem13_two_pair_routability_sparsifier_of_branchLabelings_cardLe
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (L : TwoPairBranchForwardLabeling P Q k)
    (Lrev : TwoPairBranchReverseRedLabeling P Q k)
    (hPcard : P.card ≤ k) (hQcard : Q.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  exact
    theorem13_two_pair_routability_sparsifier_of_branchChainLabelCertificate_cardLe
      S₁ T₁ S₂ T₂ P Q
      (TwoPairBranchChainLabelCertificate.ofBranchLabelings L Lrev)
      hPcard hQcard

/-- Theorem 1.3's routing sparsifier conclusion from branch-restricted
reachability covers. -/
theorem theorem13_two_pair_routability_sparsifier_of_branchReachCovers
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (Z : TwoPairBranchForwardReachCover P Q k₁)
    (Zrev : TwoPairBranchReverseRedReachCover P Q k₁)
    (hS₁ : S₁.card = k₁) (hS₂ : S₂.card ≤ k₁) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  exact
    theorem13_two_pair_routability_sparsifier_of_branchLabelings
      S₁ T₁ S₂ T₂ P Q
      Z.toBranchForwardLabeling Zrev.toBranchReverseRedLabeling hS₁ hS₂

/-- Cardinality-inequality form of the branch-restricted reach-cover
conclusion. -/
theorem theorem13_two_pair_routability_sparsifier_of_branchReachCovers_cardLe
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (Z : TwoPairBranchForwardReachCover P Q k)
    (Zrev : TwoPairBranchReverseRedReachCover P Q k)
    (hPcard : P.card ≤ k) (hQcard : Q.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  exact
    theorem13_two_pair_routability_sparsifier_of_branchLabelings_cardLe
      S₁ T₁ S₂ T₂ P Q
      Z.toBranchForwardLabeling Zrev.toBranchReverseRedLabeling
      hPcard hQcard

omit [Fintype V] in
/-- Minor-side Theorem 1.3 conclusion from branch-restricted reachability
covers in a minimal good minor. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_branchReachCovers
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (Z :
      TwoPairBranchForwardReachCover
        M.good.redRouting M.good.blueRouting k)
    (Zrev :
      TwoPairBranchReverseRedReachCover
        M.good.redRouting M.good.blueRouting k)
    (hS₁ : S₁.card = k) (hS₂ : S₂.card ≤ k) :
    TwoPairRoutingSparsifier H
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))
      k := by
  have hS₁' :
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂)).card = k := by
    rw [M.good.respecting.terminalImage_card]
    exact hS₁
  have hS₂' :
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂)).card ≤ k := by
    rw [M.good.respecting.terminalImage_card]
    exact hS₂
  exact theorem13_two_pair_routability_sparsifier_of_branchReachCovers
    _ _ _ _ M.good.redRouting M.good.blueRouting Z Zrev hS₁' hS₂'

omit [Fintype V] in
/-- Minor-side Theorem 1.3 conclusion from core-incidence facts, using only
the branch-restricted counting route. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_coreIncidence_branch
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (C : TwoPairGoodMinorCoreIncidence M.good)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hS₂ : S₂.card ≤ k) :
    TwoPairRoutingSparsifier H
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))
      k := by
  have hredCard : M.good.redRouting.card ≤ k := by
    rw [M.good.redRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₁
  have hblueCard : M.good.blueRouting.card ≤ k := by
    rw [M.good.blueRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₂
  let Z :=
    M.branchForwardReachCoverOfCoreIncidence
      C hdeg hdisj defaultState hredCard hblueCard
  let Zrev :=
    M.branchReverseRedReachCoverOfCoreIncidence
      C hdeg hdisj defaultState hredCard hblueCard
  exact theorem13_two_pair_routability_sparsifier_of_branchReachCovers_cardLe
    _ _ _ _ M.good.redRouting M.good.blueRouting Z Zrev hredCard hblueCard

omit [Fintype V] in
/-- Minor-side Theorem 1.3 conclusion for a minimal good minor, using the
branch-restricted chain construction directly from minimality. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_branchMinimality
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hS₂ : S₂.card ≤ k) :
    TwoPairRoutingSparsifier H
      (M.good.respecting.terminalImage S₁
        (subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₁
        (subset_twoPairTerminalSet_T₁ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage S₂
        (subset_twoPairTerminalSet_S₂ S₁ T₁ S₂ T₂))
      (M.good.respecting.terminalImage T₂
        (subset_twoPairTerminalSet_T₂ S₁ T₁ S₂ T₂))
      k := by
  have hredCard : M.good.redRouting.card ≤ k := by
    rw [M.good.redRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₁
  have hblueCard : M.good.blueRouting.card ≤ k := by
    rw [M.good.blueRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₂
  let Z :=
    M.branchForwardReachCoverOfMinimality
      hdeg hdisj defaultState hredCard hblueCard
  let Zrev :=
    M.branchReverseRedReachCoverOfMinimality
      hdeg hdisj defaultState hredCard hblueCard
  exact theorem13_two_pair_routability_sparsifier_of_branchReachCovers_cardLe
    _ _ _ _ M.good.redRouting M.good.blueRouting Z Zrev hredCard hblueCard

/-- Host-side Theorem 1.3 conclusion from a branch-minimal good minor and a
controlled expansion whose buckets are precisely the branch vertices of the
minor red/blue union.  This is the faithful target for the paper's local
minor-expansion paragraph. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_branchMinimality_expansion
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    [Fintype V]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (E :
      TwoPairControlledExpansion
        (W :=
          {w : W //
            w ∈ branchVertexFinset
              (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)})
        G S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hS₂ : S₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  have hredCard : M.good.redRouting.card ≤ k := by
    rw [M.good.redRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₁
  have hblueCard : M.good.blueRouting.card ≤ k := by
    rw [M.good.blueRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₂
  let Z :=
    M.branchForwardReachCoverOfMinimality
      hdeg hdisj defaultState hredCard hblueCard
  let Zrev :=
    M.branchReverseRedReachCoverOfMinimality
      hdeg hdisj defaultState hredCard hblueCard
  let C :=
    TwoPairBranchChainLabelCertificate.ofBranchLabelings
      Z.toBranchForwardLabeling Zrev.toBranchReverseRedLabeling
  have hbranchFour :
      branchVertexCount
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) ≤
          4 * k ^ 4 :=
    C.branchVertexCount_le_four_mul_pow hredCard hblueCard
  have hbucket :
      Fintype.card
        {w : W //
          w ∈ branchVertexFinset
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)} ≤
        4 * k ^ 4 + 4 * k := by
    let B :=
      branchVertexFinset
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)
    have hcard :
        Fintype.card {w : W // w ∈ B} = B.card := by
      simpa [B] using Fintype.card_subtype (fun w : W => w ∈ B)
    have hBbranch :
        B.card =
          branchVertexCount
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) := by
      simp [B]
    calc
      Fintype.card
          {w : W //
            w ∈ branchVertexFinset
              (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)}
          = B.card := by
            simpa [B] using hcard
      _ =
          branchVertexCount
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) :=
            hBbranch
      _ ≤ 4 * k ^ 4 := hbranchFour
      _ ≤ 4 * k ^ 4 + 4 * k := by omega
  exact E.toRoutingSparsifier hbucket

/-- Host-side Theorem 1.3 conclusion from a branch-minimal good minor, using
only the paper's local `≤ 2` expansion bound and the branch-restricted
`4 k^4` minor count.  This avoids the weaker route through a bound on all
vertices of the minor. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_branchMinimality_liftedLocalBound
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    [Fintype V]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hlocal : M.good.LiftedRoutingBranchSetLocalBound)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hS₂ : S₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  have hredCard : M.good.redRouting.card ≤ k := by
    rw [M.good.redRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₁
  have hblueCard : M.good.blueRouting.card ≤ k := by
    rw [M.good.blueRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₂
  let Z :=
    M.branchForwardReachCoverOfMinimality
      hdeg hdisj defaultState hredCard hblueCard
  let Zrev :=
    M.branchReverseRedReachCoverOfMinimality
      hdeg hdisj defaultState hredCard hblueCard
  let C :=
    TwoPairBranchChainLabelCertificate.ofBranchLabelings
      Z.toBranchForwardLabeling Zrev.toBranchReverseRedLabeling
  have hbranchFour :
      branchVertexCount
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) ≤
          4 * k ^ 4 :=
    C.branchVertexCount_le_four_mul_pow hredCard hblueCard
  let E :=
    M.controlledExpansionOfLiftedRoutingMinorBranchVertices
      hdeg hdisj hlocal
  have hbucket :
      Fintype.card
        {w : W //
          w ∈ branchVertexFinset
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)} ≤
        4 * k ^ 4 + 4 * k := by
    let B :=
      branchVertexFinset
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)
    have hcard :
        Fintype.card {w : W // w ∈ B} = B.card := by
      simpa [B] using Fintype.card_subtype (fun w : W => w ∈ B)
    have hBbranch :
        B.card =
          branchVertexCount
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) := by
      simp [B]
    calc
      Fintype.card
          {w : W //
            w ∈ branchVertexFinset
              (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)}
          = B.card := by
            simpa [B] using hcard
      _ =
          branchVertexCount
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) :=
            hBbranch
      _ ≤ 4 * k ^ 4 := hbranchFour
      _ ≤ 4 * k ^ 4 + 4 * k := by omega
  exact E.toRoutingSparsifier hbucket

/-- Host-side Theorem 1.3 conclusion from a branch-minimal good minor, using the
paper-expanded routings and the paper's branch-set-local `≤ 2` bound. -/
theorem theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_branchMinimality_paperLocalBound
    {W : Type w} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    [Fintype V]
    (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂)
    (hlocal : M.good.PaperRoutingBranchSetLocalBound)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂)
    (defaultState : TwoPairAltState W)
    (hS₁ : S₁.card ≤ k) (hS₂ : S₂.card ≤ k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  have hredCard : M.good.redRouting.card ≤ k := by
    rw [M.good.redRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₁
  have hblueCard : M.good.blueRouting.card ≤ k := by
    rw [M.good.blueRouting.card_eq_left_card,
      M.good.respecting.terminalImage_card]
    exact hS₂
  let Z :=
    M.branchForwardReachCoverOfMinimality
      hdeg hdisj defaultState hredCard hblueCard
  let Zrev :=
    M.branchReverseRedReachCoverOfMinimality
      hdeg hdisj defaultState hredCard hblueCard
  let C :=
    TwoPairBranchChainLabelCertificate.ofBranchLabelings
      Z.toBranchForwardLabeling Zrev.toBranchReverseRedLabeling
  have hbranchFour :
      branchVertexCount
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) ≤
          4 * k ^ 4 :=
    C.branchVertexCount_le_four_mul_pow hredCard hblueCard
  let E :=
    M.controlledExpansionOfPaperRoutingMinorBranchVertices
      hdeg hdisj hlocal
  have hbucket :
      Fintype.card
        {w : W //
          w ∈ branchVertexFinset
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)} ≤
        4 * k ^ 4 + 4 * k := by
    let B :=
      branchVertexFinset
        (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)
    have hcard :
        Fintype.card {w : W // w ∈ B} = B.card := by
      simpa [B] using Fintype.card_subtype (fun w : W => w ∈ B)
    have hBbranch :
        B.card =
          branchVertexCount
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) := by
      simp [B]
    calc
      Fintype.card
          {w : W //
            w ∈ branchVertexFinset
              (twoPackingUnionGraph M.good.redRouting M.good.blueRouting)}
          = B.card := by
            simpa [B] using hcard
      _ =
          branchVertexCount
            (twoPackingUnionGraph M.good.redRouting M.good.blueRouting) :=
            hBbranch
      _ ≤ 4 * k ^ 4 := hbranchFour
      _ ≤ 4 * k ^ 4 + 4 * k := by omega
  exact E.toRoutingSparsifier hbucket

/-- Normalized Theorem 1.3 after the finite minimal-good-minor choice has
been made internally.  This is the Section 2 reduction with equal-sized,
pairwise-disjoint degree-one terminals; the only remaining input is the
paper's local expansion theorem for the minimal good minor selected by the
finite minimization argument. -/
theorem theorem13_two_pair_routability_sparsifier_normalized_liftedLocalBound
    [Fintype V]
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (hS₁ : S₁.card = k) (hS₂ : S₂.card = k)
    (hkpos : 0 < k)
    (hR₁ : RoutableIn G S₁ T₁)
    (hR₂ : RoutableIn G S₂ T₂)
    (hlocal :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {H : _root_.SimpleGraph W}
        (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂),
          M.good.LiftedRoutingBranchSetLocalBound)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  rcases exists_minimalGoodMinor_of_routable hR₁ hR₂ with
    ⟨W, instW, instDecW, H, ⟨M⟩⟩
  letI : Fintype W := instW
  letI : DecidableEq W := instDecW
  have hS₁nonempty : S₁.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  let x : V := hS₁nonempty.choose
  have hxS₁ : x ∈ S₁ := hS₁nonempty.choose_spec
  let defaultState : TwoPairAltState W :=
    (M.good.respecting.terminalVertex x
      ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hxS₁),
      TwoPairColor.red)
  have hS₁le : S₁.card ≤ k := by omega
  have hS₂le : S₂.card ≤ k := by omega
  exact
    theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_branchMinimality_liftedLocalBound
      M (hlocal M) hdeg hdisj defaultState hS₁le hS₂le

/-- Normalized Theorem 1.3 using the concrete paper-expanded routings, after the
local branch-set bound has been proved for the selected minimal good minor. -/
theorem theorem13_two_pair_routability_sparsifier_normalized_paperLocalBound
    [Fintype V]
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (hS₁ : S₁.card = k) (hS₂ : S₂.card = k)
    (hkpos : 0 < k)
    (hR₁ : RoutableIn G S₁ T₁)
    (hR₂ : RoutableIn G S₂ T₂)
    (hlocal :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {H : _root_.SimpleGraph W}
        (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂),
          M.good.PaperRoutingBranchSetLocalBound)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  rcases exists_minimalGoodMinor_of_routable hR₁ hR₂ with
    ⟨W, instW, instDecW, H, ⟨M⟩⟩
  letI : Fintype W := instW
  letI : DecidableEq W := instDecW
  have hS₁nonempty : S₁.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  let x : V := hS₁nonempty.choose
  have hxS₁ : x ∈ S₁ := hS₁nonempty.choose_spec
  let defaultState : TwoPairAltState W :=
    (M.good.respecting.terminalVertex x
      ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hxS₁),
      TwoPairColor.red)
  have hS₁le : S₁.card ≤ k := by omega
  have hS₂le : S₂.card ≤ k := by omega
  exact
    theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_branchMinimality_paperLocalBound
      M (hlocal M) hdeg hdisj defaultState hS₁le hS₂le

/-- Closed normalized Theorem 1.3 using the concrete paper-expanded routings.
The local branch-set bound is proved internally from the paper's rerouting
argument above. -/
theorem theorem13_two_pair_routability_sparsifier_normalized_paper
    [Fintype V]
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (hS₁ : S₁.card = k) (hS₂ : S₂.card = k)
    (hkpos : 0 < k)
    (hR₁ : RoutableIn G S₁ T₁)
    (hR₂ : RoutableIn G S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  exact
    theorem13_two_pair_routability_sparsifier_normalized_paperLocalBound
      hS₁ hS₂ hkpos hR₁ hR₂
      (fun M => M.paperRoutingBranchSetLocalBound hdeg hdisj)
      hdeg hdisj

/-- Normalized Theorem 1.3 with the minimal good minor chosen internally and
the paper's expansion paragraph supplied directly as a controlled expansion
over the branch vertices of that minor. -/
theorem theorem13_two_pair_routability_sparsifier_normalized_expansion
    [Fintype V]
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k : ℕ}
    (hS₁ : S₁.card = k) (hS₂ : S₂.card = k)
    (hkpos : 0 < k)
    (hR₁ : RoutableIn G S₁ T₁)
    (hR₂ : RoutableIn G S₂ T₂)
    (hexpansion :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {H : _root_.SimpleGraph W}
        (M : TwoPairMinimalGoodMinor G H S₁ T₁ S₂ T₂),
          TwoPairControlledExpansion
            (W :=
              {w : W //
                w ∈ branchVertexFinset
                  (twoPackingUnionGraph
                    M.good.redRouting M.good.blueRouting)})
            G S₁ T₁ S₂ T₂)
    (hdeg :
      ∀ x : V, x ∈ twoPairTerminalSet S₁ T₁ S₂ T₂ →
        DegreeEquals G x 1)
    (hdisj : TwoPairTerminalSetsDisjoint S₁ T₁ S₂ T₂) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  rcases exists_minimalGoodMinor_of_routable hR₁ hR₂ with
    ⟨W, instW, instDecW, H, ⟨M⟩⟩
  letI : Fintype W := instW
  letI : DecidableEq W := instDecW
  have hS₁nonempty : S₁.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  let x : V := hS₁nonempty.choose
  have hxS₁ : x ∈ S₁ := hS₁nonempty.choose_spec
  let defaultState : TwoPairAltState W :=
    (M.good.respecting.terminalVertex x
      ((subset_twoPairTerminalSet_S₁ S₁ T₁ S₂ T₂) hxS₁),
      TwoPairColor.red)
  have hS₁le : S₁.card ≤ k := by omega
  have hS₂le : S₂.card ≤ k := by omega
  exact
    theorem13_two_pair_routability_sparsifier_of_minimalGoodMinor_branchMinimality_expansion
      M (hexpansion M) hdeg hdisj defaultState hS₁le hS₂le

/-! ## Public Theorem 1.3 augmentation data -/

/-- Vertex type for the standard reduction from Theorem 1.3 to the normalized
degree-one, disjoint-terminal case used by Theorem 2.1.

The `old` vertices are the original graph vertices.  The `dummyA`/`dummyB`
vertices are the extra blue-pair endpoints added when `k₂ < k₁`.  The
remaining constructors are fresh leaves attached to the corresponding old or
dummy terminal occurrence, so the four normalized terminal sets are disjoint
even when the original terminal sets overlap. -/
inductive Theorem13AugVertex
    (V : Type u) (S₁ T₁ S₂ T₂ : Finset V) (δ : ℕ) where
  | old : V → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
  | dummyA : Fin δ → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
  | dummyB : Fin δ → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
  | leafS₁ : {x : V // x ∈ S₁} → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
  | leafT₁ : {x : V // x ∈ T₁} → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
  | leafS₂Old : {x : V // x ∈ S₂} → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
  | leafT₂Old : {x : V // x ∈ T₂} → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
  | leafS₂Dummy : Fin δ → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
  | leafT₂Dummy : Fin δ → Theorem13AugVertex V S₁ T₁ S₂ T₂ δ
deriving DecidableEq, Fintype

namespace Theorem13AugVertex

variable {S₁ T₁ S₂ T₂ : Finset V} {δ : ℕ}

namespace GraphPath

variable {W : Type w} [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}

/-- Map a bundled path along an injective graph homomorphism. -/
def mapHomInjective (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (φ : G →g H) (hinj : Function.Injective φ) :
    Lax17Proofs.SimpleGraph.GraphPath H where
  source := φ P.source
  target := φ P.target
  walk := P.walk.map φ
  isPath := _root_.SimpleGraph.Walk.map_isPath_of_injective
    (f := φ) hinj P.isPath

@[simp] theorem mapHomInjective_source
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (φ : G →g H) (hinj : Function.Injective φ) :
    (mapHomInjective P φ hinj).source = φ P.source := rfl

@[simp] theorem mapHomInjective_target
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (φ : G →g H) (hinj : Function.Injective φ) :
    (mapHomInjective P φ hinj).target = φ P.target := rfl

@[simp] theorem mapHomInjective_vertexSet
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (φ : G →g H) (hinj : Function.Injective φ) :
    (mapHomInjective P φ hinj).vertexSet =
      P.vertexSet.image (fun x => φ x) := by
  classical
  ext y
  simp [mapHomInjective, Lax17Proofs.SimpleGraph.GraphPath.vertexSet,
    _root_.SimpleGraph.Walk.support_map]

@[simp] theorem mapHomInjective_edgeSet
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (φ : G →g H) (hinj : Function.Injective φ) :
    (mapHomInjective P φ hinj).edgeSet =
      P.edgeSet.image (fun e => Sym2.map (fun x => φ x) e) := by
  classical
  ext e
  simp [mapHomInjective, Lax17Proofs.SimpleGraph.GraphPath.edgeSet,
    _root_.SimpleGraph.Walk.edges_map]

end GraphPath

/-- The fresh leaves representing the first source set. -/
noncomputable def S₁Leaves :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  S₁.attach.image
    (Theorem13AugVertex.leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The fresh leaves representing the first target set. -/
noncomputable def T₁Leaves :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  T₁.attach.image
    (Theorem13AugVertex.leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The fresh leaves representing the second source set, including the dummy
blue endpoints added to equalize the two pair sizes. -/
noncomputable def S₂Leaves :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  S₂.attach.image
      (Theorem13AugVertex.leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
    (Finset.univ : Finset (Fin δ)).image
      (Theorem13AugVertex.leafS₂Dummy (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The fresh leaves representing the second target set, including the dummy
blue endpoints added to equalize the two pair sizes. -/
noncomputable def T₂Leaves :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  T₂.attach.image
      (Theorem13AugVertex.leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
    (Finset.univ : Finset (Fin δ)).image
      (Theorem13AugVertex.leafT₂Dummy (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The old-vertex second-source leaves, before adding dummy terminals. -/
noncomputable def S₂OldLeaves :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  S₂.attach.image
    (Theorem13AugVertex.leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The dummy second-source leaves used only to equalize pair sizes. -/
noncomputable def S₂DummyLeaves :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  (Finset.univ : Finset (Fin δ)).image
    (Theorem13AugVertex.leafS₂Dummy (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The old-vertex second-target leaves, before adding dummy terminals. -/
noncomputable def T₂OldLeaves :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  T₂.attach.image
    (Theorem13AugVertex.leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The dummy second-target leaves used only to equalize pair sizes. -/
noncomputable def T₂DummyLeaves :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  (Finset.univ : Finset (Fin δ)).image
    (Theorem13AugVertex.leafT₂Dummy (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

@[simp] theorem S₂Leaves_eq_old_union_dummy :
    S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) =
      S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) ∪
      S₂DummyLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := rfl

@[simp] theorem T₂Leaves_eq_old_union_dummy :
    T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) =
      T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) ∪
      T₂DummyLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := rfl

@[simp] theorem S₁Leaves_card :
    (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)).card = S₁.card := by
  classical
  rw [S₁Leaves, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    cases hxy
    rfl

@[simp] theorem T₁Leaves_card :
    (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)).card = T₁.card := by
  classical
  rw [T₁Leaves, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    cases hxy
    rfl

@[simp] theorem S₂Leaves_card :
    (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)).card = S₂.card + δ := by
  classical
  rw [S₂Leaves]
  have hdisj :
      Disjoint
        (S₂.attach.image
          (Theorem13AugVertex.leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)))
        ((Finset.univ : Finset (Fin δ)).image
          (Theorem13AugVertex.leafS₂Dummy (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ))) := by
    rw [Finset.disjoint_left]
    intro z hzOld hzDummy
    rcases Finset.mem_image.mp hzOld with ⟨x, _hx, rfl⟩
    rcases Finset.mem_image.mp hzDummy with ⟨i, _hi, h⟩
    cases h
  rw [Finset.card_union_of_disjoint hdisj]
  rw [Finset.card_image_of_injective, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    cases hxy
    rfl
  · intro x y hxy
    cases hxy
    rfl

@[simp] theorem T₂Leaves_card :
    (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)).card = T₂.card + δ := by
  classical
  rw [T₂Leaves]
  have hdisj :
      Disjoint
        (T₂.attach.image
          (Theorem13AugVertex.leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)))
        ((Finset.univ : Finset (Fin δ)).image
          (Theorem13AugVertex.leafT₂Dummy (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ))) := by
    rw [Finset.disjoint_left]
    intro z hzOld hzDummy
    rcases Finset.mem_image.mp hzOld with ⟨x, _hx, rfl⟩
    rcases Finset.mem_image.mp hzDummy with ⟨i, _hi, h⟩
    cases h
  rw [Finset.card_union_of_disjoint hdisj]
  rw [Finset.card_image_of_injective, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    cases hxy
    rfl
  · intro x y hxy
    cases hxy
    rfl

theorem exists_leafS₁Value
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    ∃ x : {x : V // x ∈ S₁},
      z = leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
  classical
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hxz⟩
  exact ⟨x, hxz.symm⟩

noncomputable def leafS₁Value
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    {x : V // x ∈ S₁} :=
  Classical.choose (exists_leafS₁Value (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) hz)

theorem leafS₁Value_spec
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    z = leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (leafS₁Value (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) hz) :=
  Classical.choose_spec (exists_leafS₁Value (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) hz)

theorem exists_leafT₁Value
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    ∃ x : {x : V // x ∈ T₁},
      z = leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
  classical
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hxz⟩
  exact ⟨x, hxz.symm⟩

noncomputable def leafT₁Value
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    {x : V // x ∈ T₁} :=
  Classical.choose (exists_leafT₁Value (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) hz)

theorem leafT₁Value_spec
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    z = leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (leafT₁Value (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) hz) :=
  Classical.choose_spec (exists_leafT₁Value (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) hz)

theorem exists_leafS₂OldValue
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    ∃ x : {x : V // x ∈ S₂},
      z = leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
  classical
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hxz⟩
  exact ⟨x, hxz.symm⟩

noncomputable def leafS₂OldValue
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    {x : V // x ∈ S₂} :=
  Classical.choose (exists_leafS₂OldValue (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) hz)

theorem leafS₂OldValue_spec
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    z = leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (leafS₂OldValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) hz) :=
  Classical.choose_spec (exists_leafS₂OldValue
    (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) hz)

theorem exists_leafT₂OldValue
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    ∃ x : {x : V // x ∈ T₂},
      z = leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
  classical
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hxz⟩
  exact ⟨x, hxz.symm⟩

noncomputable def leafT₂OldValue
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    {x : V // x ∈ T₂} :=
  Classical.choose (exists_leafT₂OldValue (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) hz)

theorem leafT₂OldValue_spec
    {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz :
      z ∈ T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    z = leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (leafT₂OldValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) hz) :=
  Classical.choose_spec (exists_leafT₂OldValue
    (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) hz)

/-- The four normalized leaf terminal sets are pairwise disjoint by
construction, independently of overlaps among the original terminal sets. -/
theorem terminalSetsDisjoint :
    TwoPairTerminalSetsDisjoint
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
  classical
  simp [TwoPairTerminalSetsDisjoint, S₁Leaves, T₁Leaves, S₂Leaves, T₂Leaves,
    Finset.disjoint_left] <;> aesop

/-- The directed edge relation used to build the normalized auxiliary graph.
It is symmetrized by `SimpleGraph.fromRel`. -/
def rel (G : _root_.SimpleGraph V) :
    Theorem13AugVertex V S₁ T₁ S₂ T₂ δ →
      Theorem13AugVertex V S₁ T₁ S₂ T₂ δ → Prop
  | old x, old y => G.Adj x y
  | leafS₁ x, old y => x.1 = y
  | leafT₁ x, old y => x.1 = y
  | leafS₂Old x, old y => x.1 = y
  | leafT₂Old x, old y => x.1 = y
  | dummyA i, dummyB j => i = j
  | leafS₂Dummy i, dummyA j => i = j
  | leafT₂Dummy i, dummyB j => i = j
  | _, _ => False

/-- The auxiliary graph used by the public Theorem 1.3 reduction. -/
def graph (G : _root_.SimpleGraph V) :
    _root_.SimpleGraph (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  _root_.SimpleGraph.fromRel
    (rel (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) (δ := δ) G)

/-- Image of an original terminal set in the old-vertex copy. -/
noncomputable def oldImage (A : Finset V) :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  A.image
    (Theorem13AugVertex.old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The dummy `A` vertices used as extra blue sources. -/
noncomputable def dummyAImage :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  (Finset.univ : Finset (Fin δ)).image
    (Theorem13AugVertex.dummyA (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

/-- The dummy `B` vertices used as extra blue targets. -/
noncomputable def dummyBImage :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  (Finset.univ : Finset (Fin δ)).image
    (Theorem13AugVertex.dummyB (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

@[simp] theorem oldImage_card (A : Finset V) :
    (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) A).card = A.card := by
  classical
  rw [oldImage, Finset.card_image_of_injective]
  intro x y hxy
  cases hxy
  rfl

@[simp] theorem dummyAImage_card :
    (dummyAImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)).card = δ := by
  classical
  rw [dummyAImage, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    cases hxy
    rfl

@[simp] theorem dummyBImage_card :
    (dummyBImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)).card = δ := by
  classical
  rw [dummyBImage, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    cases hxy
    rfl

theorem mem_oldImage {A : Finset V} {x : V} :
    old x ∈ oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) A ↔ x ∈ A := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    cases hxy
    exact hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

@[simp] theorem graph_adj
    {G : _root_.SimpleGraph V}
    {x y : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ} :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj
        x y ↔ x ≠ y ∧
          (rel (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) (δ := δ) G x y ∨
            rel (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) (δ := δ) G y x) :=
  Iff.rfl

theorem adj_old_old {G : _root_.SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (old x) (old y) := by
  rw [graph_adj]
  constructor
  · intro h
    exact hxy.ne (by cases h; rfl)
  · exact Or.inl hxy

theorem old_injective :
    Function.Injective
      (Theorem13AugVertex.old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
  intro x y hxy
  cases hxy
  rfl

/-- The original graph embeds homomorphically into the old-vertex part of the
auxiliary graph. -/
def oldHom (G : _root_.SimpleGraph V) :
    G →g graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G where
  toFun :=
    Theorem13AugVertex.old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
  map_rel' := by
    intro x y hxy
    exact adj_old_old (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) hxy

/-- Map an original perfect routing to the old-vertex copy in the auxiliary
graph. -/
noncomputable def oldPerfectPathPacking [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B) :
    PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) A)
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) B) where
  toPathPacking := {
    Index := P.Index
    path := fun i =>
      GraphPath.mapHomInjective (P.path i)
        (oldHom (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
        (old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
    connects := by
      intro i
      exact Or.inl
        ⟨by
          exact Finset.mem_image.mpr ⟨(P.path i).source, P.source_mem i, rfl⟩,
         by
          exact Finset.mem_image.mpr ⟨(P.path i).target, P.target_mem i, rfl⟩⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro z hzi hzj
      rw [GraphPath.mapHomInjective_vertexSet] at hzi hzj
      rcases Finset.mem_image.mp hzi with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hzj with ⟨y, hy, hyx⟩
      have hxy : x = y :=
        old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) hyx.symm
      exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij)
        hx (by simpa [hxy] using hy)
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨(P.path i).source, P.source_mem i, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨(P.path i).target, P.target_mem i, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      apply P.source_bijective.1
      apply Subtype.ext
      have hsrc :
          old (P.path i).source = old (P.path j).source :=
        congrArg Subtype.val hij
      exact old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) hsrc
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      rcases P.source_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have hsrc : (P.path i).source = v := congrArg Subtype.val hi
      calc
        old (P.path i).source = old v := by simpa [hsrc]
        _ = x.1 := hvx
  target_bijective := by
    classical
    constructor
    · intro i j hij
      apply P.target_bijective.1
      apply Subtype.ext
      have htgt :
          old (P.path i).target = old (P.path j).target :=
        congrArg Subtype.val hij
      exact old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) htgt
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      rcases P.target_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have htgt : (P.path i).target = v := congrArg Subtype.val hi
      calc
        old (P.path i).target = old v := by simpa [htgt]
        _ = x.1 := hvx

theorem adj_leafS₁_old {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ S₁}) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafS₁ x) (old x.1) := by
  rw [graph_adj]
  constructor
  · intro h
    cases h
  · exact Or.inl rfl

theorem adj_leafT₁_old {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ T₁}) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafT₁ x) (old x.1) := by
  rw [graph_adj]
  constructor
  · intro h
    cases h
  · exact Or.inl rfl

theorem adj_leafS₁_iff {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ S₁})
    {y : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ} :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafS₁ x) y ↔
      y = old x.1 := by
  constructor
  · intro hy
    rw [graph_adj] at hy
    rcases hy with ⟨_hne, hrel | hrel⟩
    · cases y <;> simp [rel] at hrel
      simpa using congrArg
        (old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) hrel.symm
    · cases y <;> simp [rel] at hrel
  · intro hy
    rw [hy]
    exact adj_leafS₁_old (G := G) x

theorem adj_leafT₁_iff {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ T₁})
    {y : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ} :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafT₁ x) y ↔
      y = old x.1 := by
  constructor
  · intro hy
    rw [graph_adj] at hy
    rcases hy with ⟨_hne, hrel | hrel⟩
    · cases y <;> simp [rel] at hrel
      simpa using congrArg
        (old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) hrel.symm
    · cases y <;> simp [rel] at hrel
  · intro hy
    rw [hy]
    exact adj_leafT₁_old (G := G) x

/-- The pendant edges from the fresh first-source leaves to the corresponding
old source vertices. -/
noncomputable def leafS₁ToOldPacking [DecidableEq V] {G : _root_.SimpleGraph V} :
    PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) S₁) where
  toPathPacking := {
    Index := Fin S₁.card
    path := fun i =>
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
        (adj_leafS₁_old (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
          (S₁.equivFin.symm i))
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr
            ⟨S₁.equivFin.symm i, by simp, rfl⟩,
          Finset.mem_image.mpr
            ⟨(S₁.equivFin.symm i).1, (S₁.equivFin.symm i).2, rfl⟩⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro z hzi hzj
      have hziPair :
          z = leafS₁ (S₁.equivFin.symm i) ∨
            z = old (S₁.equivFin.symm i).1 := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            (adj_leafS₁_old (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
              (S₁.equivFin.symm i)) hzi
        simpa using hsub
      have hzjPair :
          z = leafS₁ (S₁.equivFin.symm j) ∨
            z = old (S₁.equivFin.symm j).1 := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            (adj_leafS₁_old (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
              (S₁.equivFin.symm j)) hzj
        simpa using hsub
      rcases hziPair with rfl | rfl <;> rcases hzjPair with h | h
      · have hx :
            S₁.equivFin.symm i = S₁.equivFin.symm j := by
          simpa using h
        exact hij (S₁.equivFin.symm.injective hx)
      · cases h
      · cases h
      · have hval :
            (S₁.equivFin.symm i).1 = (S₁.equivFin.symm j).1 :=
          old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) h
        have hx :
            S₁.equivFin.symm i = S₁.equivFin.symm j :=
          Subtype.ext hval
        exact hij (S₁.equivFin.symm.injective hx)
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨S₁.equivFin.symm i, by simp, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨(S₁.equivFin.symm i).1, (S₁.equivFin.symm i).2, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      have hleaf :
          leafS₁ (S₁.equivFin.symm i) =
            leafS₁ (S₁.equivFin.symm j) :=
        congrArg Subtype.val hij
      have hx :
          S₁.equivFin.symm i = S₁.equivFin.symm j := by
        simpa using hleaf
      exact S₁.equivFin.symm.injective hx
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, _hv, hvx⟩
      refine ⟨S₁.equivFin v, ?_⟩
      apply Subtype.ext
      simpa using hvx
  target_bijective := by
    classical
    constructor
    · intro i j hij
      have hold :
          old (S₁.equivFin.symm i).1 =
            old (S₁.equivFin.symm j).1 :=
        congrArg Subtype.val hij
      have hval :
          (S₁.equivFin.symm i).1 = (S₁.equivFin.symm j).1 :=
        old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          hold
      exact S₁.equivFin.symm.injective (Subtype.ext hval)
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      refine ⟨S₁.equivFin ⟨v, hv⟩, ?_⟩
      apply Subtype.ext
      simpa using hvx

/-- The pendant edges from old first-target vertices to their fresh target
leaves. -/
noncomputable def oldToLeafT₁Packing [DecidableEq V] {G : _root_.SimpleGraph V} :
    PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) T₁)
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) where
  toPathPacking := {
    Index := Fin T₁.card
    path := fun i =>
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
        ((adj_leafT₁_old (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
          (T₁.equivFin.symm i)).symm)
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr
            ⟨(T₁.equivFin.symm i).1, (T₁.equivFin.symm i).2, rfl⟩,
          Finset.mem_image.mpr
            ⟨T₁.equivFin.symm i, by simp, rfl⟩⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro z hzi hzj
      have hziPair :
          z = old (T₁.equivFin.symm i).1 ∨
            z = leafT₁ (T₁.equivFin.symm i) := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            ((adj_leafT₁_old (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
              (T₁.equivFin.symm i)).symm) hzi
        simpa using hsub
      have hzjPair :
          z = old (T₁.equivFin.symm j).1 ∨
            z = leafT₁ (T₁.equivFin.symm j) := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            ((adj_leafT₁_old (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
              (T₁.equivFin.symm j)).symm) hzj
        simpa using hsub
      rcases hziPair with rfl | rfl <;> rcases hzjPair with h | h
      · have hval :
            (T₁.equivFin.symm i).1 = (T₁.equivFin.symm j).1 :=
          old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) h
        have hx :
            T₁.equivFin.symm i = T₁.equivFin.symm j :=
          Subtype.ext hval
        exact hij (T₁.equivFin.symm.injective hx)
      · cases h
      · cases h
      · have hx :
            T₁.equivFin.symm i = T₁.equivFin.symm j := by
          simpa using h
        exact hij (T₁.equivFin.symm.injective hx)
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨(T₁.equivFin.symm i).1, (T₁.equivFin.symm i).2, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨T₁.equivFin.symm i, by simp, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      have hold :
          old (T₁.equivFin.symm i).1 =
            old (T₁.equivFin.symm j).1 :=
        congrArg Subtype.val hij
      have hval :
          (T₁.equivFin.symm i).1 = (T₁.equivFin.symm j).1 :=
        old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        hold
      exact T₁.equivFin.symm.injective (Subtype.ext hval)
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      refine ⟨T₁.equivFin ⟨v, hv⟩, ?_⟩
      apply Subtype.ext
      simpa using hvx
  target_bijective := by
    classical
    constructor
    · intro i j hij
      have hleaf :
          leafT₁ (T₁.equivFin.symm i) =
            leafT₁ (T₁.equivFin.symm j) :=
        congrArg Subtype.val hij
      have hx :
          T₁.equivFin.symm i = T₁.equivFin.symm j := by
        simpa using hleaf
      exact T₁.equivFin.symm.injective hx
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, _hv, hvx⟩
      refine ⟨T₁.equivFin v, ?_⟩
      apply Subtype.ext
      simpa using hvx

theorem S₁Leaves_disjoint_oldImage [DecidableEq V] (A : Finset V) :
    Disjoint
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) A) := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hOld
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hzx⟩
  rcases Finset.mem_image.mp hOld with ⟨y, _hy, hzy⟩
  rw [← hzx] at hzy
  cases hzy

theorem T₁Leaves_disjoint_oldImage [DecidableEq V] (A : Finset V) :
    Disjoint
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) A) := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hOld
  rcases Finset.mem_image.mp hz with ⟨x, _hx, hzx⟩
  rcases Finset.mem_image.mp hOld with ⟨y, _hy, hzy⟩
  rw [← hzx] at hzy
  cases hzy

theorem T₁Leaves_disjoint_S₁Leaves [DecidableEq V] :
    Disjoint
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzT hzS
  rcases Finset.mem_image.mp hzT with ⟨x, _hx, hzx⟩
  rcases Finset.mem_image.mp hzS with ⟨y, _hy, hzy⟩
  rw [← hzx] at hzy
  cases hzy

theorem T₁Leaves_disjoint_redPrefixRegion [DecidableEq V] :
    Disjoint
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      ((S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
        (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))) := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hregion
  rcases Finset.mem_union.mp hregion with hzS | hzOld
  · exact Finset.disjoint_left.mp
      (T₁Leaves_disjoint_S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) hz hzS
  · exact Finset.disjoint_left.mp
      (T₁Leaves_disjoint_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)) hz hzOld

theorem oldPerfectPathPacking_staysIn_oldImage_univ [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (P : PerfectPathPacking G A B) :
    (oldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P).toPathPacking.StaysIn
        (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)) := by
  classical
  intro i z hz
  change z ∈
      (GraphPath.mapHomInjective (P.path i)
        (oldHom (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
        (old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))).vertexSet at hz
  rw [GraphPath.mapHomInjective_vertexSet] at hz
  rcases Finset.mem_image.mp hz with ⟨x, _hx, rfl⟩
  exact (mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ)
    (A := (Finset.univ : Finset V))).2 (by simp)

theorem leafS₁ToOldPacking_internallyDisjoint_oldImage_univ [DecidableEq V]
    {G : _root_.SimpleGraph V} :
    (leafS₁ToOldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.InternallyDisjointFromSet
          (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)) := by
  intro i
  exact Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_internallyDisjointFromSet
    (adj_leafS₁_old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
      (S₁.equivFin.symm i))
    (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))

theorem oldToLeafT₁Packing_internallyDisjoint_redPrefixRegion [DecidableEq V]
    {G : _root_.SimpleGraph V} :
    (oldToLeafT₁Packing (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.InternallyDisjointFromSet
          ((S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
            (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))) := by
  intro i
  exact Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_internallyDisjointFromSet
    ((adj_leafT₁_old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
      (T₁.equivFin.symm i)).symm)
    ((S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)))

theorem leafS₁ToOldPacking_staysIn [DecidableEq V] {G : _root_.SimpleGraph V} :
    (leafS₁ToOldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.StaysIn
        ((S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
          (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))) := by
  classical
  intro i z hz
  have hpair :
      z = leafS₁ (S₁.equivFin.symm i) ∨
        z = old (S₁.equivFin.symm i).1 := by
    have hsub :=
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
        (adj_leafS₁_old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
          (S₁.equivFin.symm i)) hz
    simpa using hsub
  rcases hpair with rfl | rfl
  · exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨S₁.equivFin.symm i, by simp, rfl⟩)
  · exact Finset.mem_union_right _
      ((mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        (A := (Finset.univ : Finset V))).2 (by simp))

theorem oldToLeafT₁Packing_staysIn [DecidableEq V] {G : _root_.SimpleGraph V} :
    (oldToLeafT₁Packing (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.StaysIn
        ((oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)) ∪
          (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ))) := by
  classical
  intro i z hz
  have hpair :
      z = old (T₁.equivFin.symm i).1 ∨
        z = leafT₁ (T₁.equivFin.symm i) := by
    have hsub :=
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
        ((adj_leafT₁_old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
          (T₁.equivFin.symm i)).symm) hz
    simpa using hsub
  rcases hpair with rfl | rfl
  · exact Finset.mem_union_left _
      ((mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        (A := (Finset.univ : Finset V))).2 (by simp))
  · exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨T₁.equivFin.symm i, by simp, rfl⟩)

/-- Add the fresh first-source leaves to an original red routing and stop at
the old-copy first targets. -/
noncomputable def redPrefixAugmentedPacking [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking G S₁ T₁) :
    PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) T₁) :=
  PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn
    (leafS₁ToOldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    (oldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
    (leafS₁ToOldPacking_internallyDisjoint_oldImage_univ
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    (oldPerfectPathPacking_staysIn_oldImage_univ
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
    (S₁Leaves_disjoint_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))

theorem redPrefixAugmentedPacking_staysIn [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking G S₁ T₁) :
    (redPrefixAugmentedPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P).toPathPacking.StaysIn
        ((S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
          (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))) := by
  classical
  let R₀ :=
    leafS₁ToOldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
  let R₁ :=
    oldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P
  let Aold :=
    oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)
  let Bprefix :=
    (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪ Aold
  have hR₀int : R₀.toPathPacking.InternallyDisjointFromSet Aold := by
    simpa [R₀, Aold] using
      (leafS₁ToOldPacking_internallyDisjoint_oldImage_univ
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
  have hR₁stay : R₁.toPathPacking.StaysIn Aold := by
    simpa [R₁, Aold] using
      (oldPerfectPathPacking_staysIn_oldImage_univ
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
  have hSdisj :
      Disjoint
        (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) Aold := by
    simpa [Aold] using
      (S₁Leaves_disjoint_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))
  have hR₀stay : R₀.toPathPacking.StaysIn Bprefix := by
    simpa [R₀, Bprefix, Aold] using
      (leafS₁ToOldPacking_staysIn (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
  have hwide :
      (R₀.concatOfFirstInternallyDisjointSecondStaysIn
        R₁ hR₀int hR₁stay hSdisj).toPathPacking.StaysIn (Bprefix ∪ Aold) :=
    PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
      R₀ R₁ hR₀int hR₁stay hSdisj hR₀stay
  have htarget :
      (R₀.concatOfFirstInternallyDisjointSecondStaysIn
        R₁ hR₀int hR₁stay hSdisj).toPathPacking.StaysIn Bprefix := by
    intro i z hz
    have hzwide := hwide i hz
    rcases Finset.mem_union.mp hzwide with hzB | hzOld
    · exact hzB
    · exact Finset.mem_union_right _ hzOld
  simpa [redPrefixAugmentedPacking, R₀, R₁, Aold, Bprefix] using htarget

/-- The original red routing, with fresh first-pair leaves attached at both
ends, as a normalized routing in the auxiliary graph. -/
noncomputable def redAugmentedPerfectPathPacking [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking G S₁ T₁) :
    PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :=
  PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint
    (redPrefixAugmentedPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
    (oldToLeafT₁Packing (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    (redPrefixAugmentedPacking_staysIn (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
    (oldToLeafT₁Packing_internallyDisjoint_redPrefixRegion
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    (T₁Leaves_disjoint_redPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))

theorem redAugmented_routable [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (hR : RoutableIn G S₁ T₁) :
    RoutableIn
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
  rcases hR with ⟨P⟩
  exact ⟨redAugmentedPerfectPathPacking
    (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) P⟩

theorem adj_leafS₂Old_old {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ S₂}) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafS₂Old x) (old x.1) := by
  rw [graph_adj]
  constructor
  · intro h
    cases h
  · exact Or.inl rfl

theorem adj_leafT₂Old_old {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ T₂}) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafT₂Old x) (old x.1) := by
  rw [graph_adj]
  constructor
  · intro h
    cases h
  · exact Or.inl rfl

theorem adj_leafS₂Old_iff {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ S₂})
    {y : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ} :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafS₂Old x) y ↔
      y = old x.1 := by
  constructor
  · intro hy
    rw [graph_adj] at hy
    rcases hy with ⟨_hne, hrel | hrel⟩
    · cases y <;> simp [rel] at hrel
      simpa using congrArg
        (old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) hrel.symm
    · cases y <;> simp [rel] at hrel
  · intro hy
    rw [hy]
    exact adj_leafS₂Old_old (G := G) x

theorem adj_leafT₂Old_iff {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ T₂})
    {y : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ} :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafT₂Old x) y ↔
      y = old x.1 := by
  constructor
  · intro hy
    rw [graph_adj] at hy
    rcases hy with ⟨_hne, hrel | hrel⟩
    · cases y <;> simp [rel] at hrel
      simpa using congrArg
        (old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) hrel.symm
    · cases y <;> simp [rel] at hrel
  · intro hy
    rw [hy]
    exact adj_leafT₂Old_old (G := G) x

/-- The pendant edges from the old second-source leaves to the corresponding
old source vertices. -/
noncomputable def leafS₂OldToOldPacking [DecidableEq V] {G : _root_.SimpleGraph V} :
    PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) S₂) where
  toPathPacking := {
    Index := Fin S₂.card
    path := fun i =>
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
        (adj_leafS₂Old_old (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
          (S₂.equivFin.symm i))
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr
            ⟨S₂.equivFin.symm i, by simp, rfl⟩,
          Finset.mem_image.mpr
            ⟨(S₂.equivFin.symm i).1, (S₂.equivFin.symm i).2, rfl⟩⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro z hzi hzj
      have hziPair :
          z = leafS₂Old (S₂.equivFin.symm i) ∨
            z = old (S₂.equivFin.symm i).1 := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            (adj_leafS₂Old_old (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
              (S₂.equivFin.symm i)) hzi
        simpa using hsub
      have hzjPair :
          z = leafS₂Old (S₂.equivFin.symm j) ∨
            z = old (S₂.equivFin.symm j).1 := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            (adj_leafS₂Old_old (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
              (S₂.equivFin.symm j)) hzj
        simpa using hsub
      rcases hziPair with rfl | rfl <;> rcases hzjPair with h | h
      · have hx :
            S₂.equivFin.symm i = S₂.equivFin.symm j := by
          simpa using h
        exact hij (S₂.equivFin.symm.injective hx)
      · cases h
      · cases h
      · have hval :
            (S₂.equivFin.symm i).1 = (S₂.equivFin.symm j).1 :=
          old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) h
        exact hij (S₂.equivFin.symm.injective (Subtype.ext hval))
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨S₂.equivFin.symm i, by simp, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨(S₂.equivFin.symm i).1, (S₂.equivFin.symm i).2, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      have hleaf :
          leafS₂Old (S₂.equivFin.symm i) =
            leafS₂Old (S₂.equivFin.symm j) :=
        congrArg Subtype.val hij
      have hx :
          S₂.equivFin.symm i = S₂.equivFin.symm j := by
        simpa using hleaf
      exact S₂.equivFin.symm.injective hx
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, _hv, hvx⟩
      refine ⟨S₂.equivFin v, ?_⟩
      apply Subtype.ext
      simpa using hvx
  target_bijective := by
    classical
    constructor
    · intro i j hij
      have hold :
          old (S₂.equivFin.symm i).1 =
            old (S₂.equivFin.symm j).1 :=
        congrArg Subtype.val hij
      have hval :
          (S₂.equivFin.symm i).1 = (S₂.equivFin.symm j).1 :=
        old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) hold
      exact S₂.equivFin.symm.injective (Subtype.ext hval)
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      refine ⟨S₂.equivFin ⟨v, hv⟩, ?_⟩
      apply Subtype.ext
      simpa using hvx

/-- The pendant edges from old second-target vertices to their old target
leaves. -/
noncomputable def oldToLeafT₂OldPacking [DecidableEq V] {G : _root_.SimpleGraph V} :
    PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) T₂)
      (T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) where
  toPathPacking := {
    Index := Fin T₂.card
    path := fun i =>
      Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
        ((adj_leafT₂Old_old (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
          (T₂.equivFin.symm i)).symm)
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr
            ⟨(T₂.equivFin.symm i).1, (T₂.equivFin.symm i).2, rfl⟩,
          Finset.mem_image.mpr
            ⟨T₂.equivFin.symm i, by simp, rfl⟩⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro z hzi hzj
      have hziPair :
          z = old (T₂.equivFin.symm i).1 ∨
            z = leafT₂Old (T₂.equivFin.symm i) := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            ((adj_leafT₂Old_old (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
              (T₂.equivFin.symm i)).symm) hzi
        simpa using hsub
      have hzjPair :
          z = old (T₂.equivFin.symm j).1 ∨
            z = leafT₂Old (T₂.equivFin.symm j) := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            ((adj_leafT₂Old_old (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
              (T₂.equivFin.symm j)).symm) hzj
        simpa using hsub
      rcases hziPair with rfl | rfl <;> rcases hzjPair with h | h
      · have hval :
            (T₂.equivFin.symm i).1 = (T₂.equivFin.symm j).1 :=
          old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) h
        exact hij (T₂.equivFin.symm.injective (Subtype.ext hval))
      · cases h
      · cases h
      · have hx :
            T₂.equivFin.symm i = T₂.equivFin.symm j := by
          simpa using h
        exact hij (T₂.equivFin.symm.injective hx)
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨(T₂.equivFin.symm i).1, (T₂.equivFin.symm i).2, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr
      ⟨T₂.equivFin.symm i, by simp, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      have hold :
          old (T₂.equivFin.symm i).1 =
            old (T₂.equivFin.symm j).1 :=
        congrArg Subtype.val hij
      have hval :
          (T₂.equivFin.symm i).1 = (T₂.equivFin.symm j).1 :=
        old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) hold
      exact T₂.equivFin.symm.injective (Subtype.ext hval)
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, hv, hvx⟩
      refine ⟨T₂.equivFin ⟨v, hv⟩, ?_⟩
      apply Subtype.ext
      simpa using hvx
  target_bijective := by
    classical
    constructor
    · intro i j hij
      have hleaf :
          leafT₂Old (T₂.equivFin.symm i) =
            leafT₂Old (T₂.equivFin.symm j) :=
        congrArg Subtype.val hij
      have hx :
          T₂.equivFin.symm i = T₂.equivFin.symm j := by
        simpa using hleaf
      exact T₂.equivFin.symm.injective hx
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨v, _hv, hvx⟩
      refine ⟨T₂.equivFin v, ?_⟩
      apply Subtype.ext
      simpa using hvx

theorem adj_dummyA_dummyB {G : _root_.SimpleGraph V} (i : Fin δ) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (dummyA i) (dummyB i) := by
  rw [graph_adj]
  constructor
  · intro h
    cases h
  · exact Or.inl rfl

theorem adj_leafS₂Dummy_dummyA {G : _root_.SimpleGraph V} (i : Fin δ) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafS₂Dummy i) (dummyA i) := by
  rw [graph_adj]
  constructor
  · intro h
    cases h
  · exact Or.inl rfl

theorem adj_leafT₂Dummy_dummyB {G : _root_.SimpleGraph V} (i : Fin δ) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafT₂Dummy i) (dummyB i) := by
  rw [graph_adj]
  constructor
  · intro h
    cases h
  · exact Or.inl rfl

/-- The three-edge dummy blue path added for one artificial second-pair
terminal. -/
noncomputable def dummyBluePath {G : _root_.SimpleGraph V} (i : Fin δ) :
    Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G) :=
  let P :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
      (adj_leafS₂Dummy_dummyA (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i)
  let Q :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
      (adj_dummyA_dummyB (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i)
  let R :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
      ((adj_leafT₂Dummy_dummyB (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i).symm)
  P.append3WithEqToPath Q R (by simp [P, Q]) (by simp [Q, R])

@[simp] theorem dummyBluePath_source {G : _root_.SimpleGraph V} (i : Fin δ) :
    (dummyBluePath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i).source =
      leafS₂Dummy i := by
  simp [dummyBluePath]

@[simp] theorem dummyBluePath_target {G : _root_.SimpleGraph V} (i : Fin δ) :
    (dummyBluePath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i).target =
      leafT₂Dummy i := by
  simp [dummyBluePath]

theorem dummyBluePath_vertexSet_subset_index [DecidableEq V]
    {G : _root_.SimpleGraph V} (i : Fin δ) {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hz : z ∈ (dummyBluePath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i).vertexSet) :
    z = leafS₂Dummy i ∨ z = dummyA i ∨ z = dummyB i ∨ z = leafT₂Dummy i := by
  classical
  let P :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
      (adj_leafS₂Dummy_dummyA (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i)
  let Q :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
      (adj_dummyA_dummyB (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i)
  let R :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj
      ((adj_leafT₂Dummy_dummyB (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i).symm)
  have hsubset :
      z ∈ P.vertexSet ∪ Q.vertexSet ∪ R.vertexSet := by
    have h :=
      Lax17Proofs.SimpleGraph.GraphPath.append3WithEqToPath_vertexSet_subset
        P Q R (by simp [P, Q]) (by simp [Q, R])
        (by simpa [dummyBluePath, P, Q, R] using hz)
    exact h
  rcases Finset.mem_union.mp hsubset with hPQ | hR
  · rcases Finset.mem_union.mp hPQ with hP | hQ
    · have hp :
          z = leafS₂Dummy i ∨ z = dummyA i := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            (adj_leafS₂Dummy_dummyA (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i) hP
        simpa using hsub
      rcases hp with hLeaf | hA
      · exact Or.inl hLeaf
      · exact Or.inr (Or.inl hA)
    · have hq :
          z = dummyA i ∨ z = dummyB i := by
        have hsub :=
          Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
            (adj_dummyA_dummyB (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i) hQ
        simpa using hsub
      rcases hq with hA | hB
      · exact Or.inr (Or.inl hA)
      · exact Or.inr (Or.inr (Or.inl hB))
  · have hr :
        z = dummyB i ∨ z = leafT₂Dummy i := by
      have hsub :=
        Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
          ((adj_leafT₂Dummy_dummyB (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i).symm) hR
      simpa using hsub
    rcases hr with hB | hLeaf
    · exact Or.inr (Or.inr (Or.inl hB))
    · exact Or.inr (Or.inr (Or.inr hLeaf))

/-- The dummy blue paths connecting artificial second-source leaves to
artificial second-target leaves. -/
noncomputable def dummyBluePacking [DecidableEq V] {G : _root_.SimpleGraph V} :
    PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂DummyLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂DummyLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) where
  toPathPacking := {
    Index := Fin δ
    path := fun i =>
      dummyBluePath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i
    connects := by
      intro i
      exact Or.inl
        ⟨by
          simp [S₂DummyLeaves],
         by
          simp [T₂DummyLeaves]⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro z hzi hzj
      have hziSet :=
        dummyBluePath_vertexSet_subset_index
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i hzi
      have hzjSet :=
        dummyBluePath_vertexSet_subset_index
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) j hzj
      rcases hziSet with rfl | rfl | rfl | rfl <;>
        rcases hzjSet with h | h | h | h <;>
        cases h <;> exact hij rfl
  }
  source_mem := by
    intro i
    simp [S₂DummyLeaves]
  target_mem := by
    intro i
    simp [T₂DummyLeaves]
  source_bijective := by
    classical
    constructor
    · intro i j hij
      have hleaf : leafS₂Dummy i = leafS₂Dummy j :=
        congrArg Subtype.val hij
      cases hleaf
      rfl
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨i, _hi, hix⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      simpa using hix
  target_bijective := by
    classical
    constructor
    · intro i j hij
      have hleaf : leafT₂Dummy i = leafT₂Dummy j :=
        congrArg Subtype.val hij
      cases hleaf
      rfl
    · intro x
      rcases Finset.mem_image.mp x.2 with ⟨i, _hi, hix⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      simpa using hix

  /-- The region used by the old second-pair paths after the source leaves have
  been attached and before the target leaves have been attached. -/
  noncomputable def blueOldPrefixRegion :
      Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
    S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) ∪
      oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)

  /-- The full region used by the old second-pair paths in the augmented
  graph. -/
  noncomputable def blueOldRegion :
      Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
    blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) ∪
      T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)

  /-- The full region used by the dummy second-pair paths in the augmented
  graph. -/
  noncomputable def dummyBlueRegion :
      Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
    ((S₂DummyLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) ∪
        dummyAImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
      dummyBImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
      T₂DummyLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)

  theorem S₂OldLeaves_disjoint_oldImage [DecidableEq V] (A : Finset V) :
      Disjoint
        (S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) A) := by
    classical
    rw [Finset.disjoint_left]
    intro z hz hOld
    rcases Finset.mem_image.mp hz with ⟨x, _hx, hzx⟩
    rcases Finset.mem_image.mp hOld with ⟨y, _hy, hzy⟩
    rw [← hzx] at hzy
    cases hzy

  theorem T₂OldLeaves_disjoint_oldImage [DecidableEq V] (A : Finset V) :
      Disjoint
        (T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) A) := by
    classical
    rw [Finset.disjoint_left]
    intro z hz hOld
    rcases Finset.mem_image.mp hz with ⟨x, _hx, hzx⟩
    rcases Finset.mem_image.mp hOld with ⟨y, _hy, hzy⟩
    rw [← hzx] at hzy
    cases hzy

  theorem T₂OldLeaves_disjoint_S₂OldLeaves [DecidableEq V] :
      Disjoint
        (T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    classical
    rw [Finset.disjoint_left]
    intro z hzT hzS
    rcases Finset.mem_image.mp hzT with ⟨x, _hx, hzx⟩
    rcases Finset.mem_image.mp hzS with ⟨y, _hy, hzy⟩
    rw [← hzx] at hzy
    cases hzy

  theorem T₂OldLeaves_disjoint_blueOldPrefixRegion [DecidableEq V] :
      Disjoint
        (T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    classical
    rw [Finset.disjoint_left]
    intro z hz hregion
    rcases Finset.mem_union.mp hregion with hzS | hzOld
    · exact Finset.disjoint_left.mp
        (T₂OldLeaves_disjoint_S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) hz hzS
    · exact Finset.disjoint_left.mp
        (T₂OldLeaves_disjoint_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)) hz hzOld

  theorem leafS₂OldToOldPacking_internallyDisjoint_oldImage_univ [DecidableEq V]
      {G : _root_.SimpleGraph V} :
      (leafS₂OldToOldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.InternallyDisjointFromSet
            (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)) := by
    intro i
    exact Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_internallyDisjointFromSet
      (adj_leafS₂Old_old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
        (S₂.equivFin.symm i))
      (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))

  theorem oldToLeafT₂OldPacking_internallyDisjoint_blueOldPrefixRegion [DecidableEq V]
      {G : _root_.SimpleGraph V} :
      (oldToLeafT₂OldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.InternallyDisjointFromSet
            (blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    intro i
    exact Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_internallyDisjointFromSet
      ((adj_leafT₂Old_old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
        (T₂.equivFin.symm i)).symm)
      (blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))

  theorem leafS₂OldToOldPacking_staysIn [DecidableEq V] {G : _root_.SimpleGraph V} :
      (leafS₂OldToOldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.StaysIn
          (blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    classical
    intro i z hz
    have hpair :
        z = leafS₂Old (S₂.equivFin.symm i) ∨
          z = old (S₂.equivFin.symm i).1 := by
      have hsub :=
        Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
          (adj_leafS₂Old_old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
            (S₂.equivFin.symm i)) hz
      simpa using hsub
    rcases hpair with rfl | rfl
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨S₂.equivFin.symm i, by simp, rfl⟩)
    · exact Finset.mem_union_right _
        ((mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          (A := (Finset.univ : Finset V))).2 (by simp))

  theorem oldToLeafT₂OldPacking_staysIn [DecidableEq V] {G : _root_.SimpleGraph V} :
      (oldToLeafT₂OldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.StaysIn
          ((oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)) ∪
            (T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ))) := by
    classical
    intro i z hz
    have hpair :
        z = old (T₂.equivFin.symm i).1 ∨
          z = leafT₂Old (T₂.equivFin.symm i) := by
      have hsub :=
        Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair
          ((adj_leafT₂Old_old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
            (T₂.equivFin.symm i)).symm) hz
      simpa using hsub
    rcases hpair with rfl | rfl
    · exact Finset.mem_union_left _
        ((mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          (A := (Finset.univ : Finset V))).2 (by simp))
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨T₂.equivFin.symm i, by simp, rfl⟩)

  /-- Add the old second-source leaves to an original blue routing and stop at
  the old-copy second targets. -/
  noncomputable def blueOldPrefixAugmentedPacking [DecidableEq V]
      {G : _root_.SimpleGraph V}
      (P : PerfectPathPacking G S₂ T₂) :
      PerfectPathPacking
        (graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
        (S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) T₂) :=
    PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn
      (leafS₂OldToOldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
      (oldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
      (leafS₂OldToOldPacking_internallyDisjoint_oldImage_univ
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
      (oldPerfectPathPacking_staysIn_oldImage_univ
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
      (S₂OldLeaves_disjoint_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))

  theorem blueOldPrefixAugmentedPacking_staysIn [DecidableEq V]
      {G : _root_.SimpleGraph V}
      (P : PerfectPathPacking G S₂ T₂) :
      (blueOldPrefixAugmentedPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P).toPathPacking.StaysIn
          (blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    classical
    let R₀ :=
      leafS₂OldToOldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
    let R₁ :=
      oldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P
    let Aold :=
      oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)
    let Bprefix :=
      blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
    have hR₀int : R₀.toPathPacking.InternallyDisjointFromSet Aold := by
      simpa [R₀, Aold] using
        (leafS₂OldToOldPacking_internallyDisjoint_oldImage_univ
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    have hR₁stay : R₁.toPathPacking.StaysIn Aold := by
      simpa [R₁, Aold] using
        (oldPerfectPathPacking_staysIn_oldImage_univ
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
    have hSdisj :
        Disjoint
          (S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)) Aold := by
      simpa [Aold] using
        (S₂OldLeaves_disjoint_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V))
    have hR₀stay : R₀.toPathPacking.StaysIn Bprefix := by
      simpa [R₀, Bprefix] using
        (leafS₂OldToOldPacking_staysIn (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    have hwide :
        (R₀.concatOfFirstInternallyDisjointSecondStaysIn
          R₁ hR₀int hR₁stay hSdisj).toPathPacking.StaysIn (Bprefix ∪ Aold) :=
      PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        R₀ R₁ hR₀int hR₁stay hSdisj hR₀stay
    have htarget :
        (R₀.concatOfFirstInternallyDisjointSecondStaysIn
          R₁ hR₀int hR₁stay hSdisj).toPathPacking.StaysIn Bprefix := by
      intro i z hz
      have hzwide := hwide i hz
      rcases Finset.mem_union.mp hzwide with hzB | hzOld
      · exact hzB
      · exact Finset.mem_union_right _ hzOld
    simpa [blueOldPrefixAugmentedPacking, R₀, R₁, Aold, Bprefix] using htarget

  /-- The original blue routing on the old second terminals, with fresh old
  second-pair leaves attached at both ends. -/
  noncomputable def blueOldAugmentedPerfectPathPacking [DecidableEq V]
      {G : _root_.SimpleGraph V}
      (P : PerfectPathPacking G S₂ T₂) :
      PerfectPathPacking
        (graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
        (S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) :=
    PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint
      (blueOldPrefixAugmentedPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
      (oldToLeafT₂OldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
      (blueOldPrefixAugmentedPacking_staysIn (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
      (oldToLeafT₂OldPacking_internallyDisjoint_blueOldPrefixRegion
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
      (T₂OldLeaves_disjoint_blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))

  theorem blueOldAugmentedPacking_staysIn [DecidableEq V]
      {G : _root_.SimpleGraph V}
      (P : PerfectPathPacking G S₂ T₂) :
      (blueOldAugmentedPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P).toPathPacking.StaysIn
          (blueOldRegion (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    classical
    let R₀ :=
      blueOldPrefixAugmentedPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P
    let R₁ :=
      oldToLeafT₂OldPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
    let Bprefix :=
      blueOldPrefixRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
    let Aold :=
      oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)
    let Told :=
      T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
    have hR₀stay : R₀.toPathPacking.StaysIn Bprefix := by
      simpa [R₀, Bprefix] using
        (blueOldPrefixAugmentedPacking_staysIn
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
    have hR₁int : R₁.toPathPacking.InternallyDisjointFromSet Bprefix := by
      simpa [R₁, Bprefix] using
        (oldToLeafT₂OldPacking_internallyDisjoint_blueOldPrefixRegion
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    have hTdisj : Disjoint Told Bprefix := by
      simpa [Told, Bprefix] using
        (T₂OldLeaves_disjoint_blueOldPrefixRegion
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
    have hR₁stay : R₁.toPathPacking.StaysIn (Aold ∪ Told) := by
      simpa [R₁, Aold, Told] using
        (oldToLeafT₂OldPacking_staysIn (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    have hwide :
        (R₀.concatOfFirstStaysInSecondInternallyDisjoint
          R₁ hR₀stay hR₁int hTdisj).toPathPacking.StaysIn
            (Bprefix ∪ (Aold ∪ Told)) :=
      PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        R₀ R₁ hR₀stay hR₁int hTdisj hR₁stay
    have htarget :
        (R₀.concatOfFirstStaysInSecondInternallyDisjoint
          R₁ hR₀stay hR₁int hTdisj).toPathPacking.StaysIn
            (Bprefix ∪ Told) := by
      intro i z hz
      have hzwide := hwide i hz
      rcases Finset.mem_union.mp hzwide with hzPrefix | hzTail
      · exact Finset.mem_union_left _ hzPrefix
      · rcases Finset.mem_union.mp hzTail with hzOld | hzT
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hzOld)
        · exact Finset.mem_union_right _ hzT
    simpa [blueOldAugmentedPerfectPathPacking, blueOldRegion, R₀, R₁, Bprefix, Told] using htarget

  theorem dummyBluePacking_staysIn [DecidableEq V] {G : _root_.SimpleGraph V} :
      (dummyBluePacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)).toPathPacking.StaysIn
          (dummyBlueRegion (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    classical
    intro i z hz
    have hcases :=
      dummyBluePath_vertexSet_subset_index
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) i hz
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)))
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)

  theorem blueOldRegion_disjoint_dummyBlueRegion [DecidableEq V] :
      Disjoint
        (blueOldRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (dummyBlueRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    classical
    rw [Finset.disjoint_left]
    intro z hzOld hzDummy
    simp [blueOldRegion, blueOldPrefixRegion, dummyBlueRegion,
      S₂OldLeaves, T₂OldLeaves, oldImage,
      S₂DummyLeaves, dummyAImage, dummyBImage, T₂DummyLeaves] at hzOld hzDummy
    aesop

  /-- The augmented blue routing, including the old second-pair routing and the
  dummy paths that equalize the two pair sizes. -/
  noncomputable def blueAugmentedPerfectPathPacking [DecidableEq V]
      {G : _root_.SimpleGraph V}
      (P : PerfectPathPacking G S₂ T₂) :
      PerfectPathPacking
        (graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
        (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    classical
    let Old :=
      blueOldAugmentedPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P
    let Dummy :=
      dummyBluePacking (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G)
    let Rold :=
      blueOldRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
    let Rdummy :=
      dummyBlueRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
    have hOldStay : Old.toPathPacking.StaysIn Rold := by
      simpa [Old, Rold] using
        (blueOldAugmentedPacking_staysIn
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
    have hDummyStay : Dummy.toPathPacking.StaysIn Rdummy := by
      simpa [Dummy, Rdummy] using
        (dummyBluePacking_staysIn
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G))
    have hRegionDisj : Disjoint Rold Rdummy := by
      simpa [Rold, Rdummy] using
        (blueOldRegion_disjoint_dummyBlueRegion
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
    have hOldSourceRegion : ∀ i : Old.Index, (Old.path i).source ∈ Rold := by
      intro i
      exact hOldStay i (Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet (Old.path i))
    have hOldTargetRegion : ∀ i : Old.Index, (Old.path i).target ∈ Rold := by
      intro i
      exact hOldStay i (Lax17Proofs.SimpleGraph.GraphPath.target_mem_vertexSet (Old.path i))
    have hDummySourceRegion : ∀ i : Dummy.Index, (Dummy.path i).source ∈ Rdummy := by
      intro i
      exact hDummyStay i (Lax17Proofs.SimpleGraph.GraphPath.source_mem_vertexSet (Dummy.path i))
    have hDummyTargetRegion : ∀ i : Dummy.Index, (Dummy.path i).target ∈ Rdummy := by
      intro i
      exact hDummyStay i (Lax17Proofs.SimpleGraph.GraphPath.target_mem_vertexSet (Dummy.path i))
    refine
      { toPathPacking := {
          Index := Old.Index ⊕ Dummy.Index
          path := fun i =>
            match i with
            | Sum.inl j => Old.path j
            | Sum.inr j => Dummy.path j
          connects := ?_
          node_disjoint := ?_ }
        source_mem := ?_
        target_mem := ?_
        source_bijective := ?_
        target_bijective := ?_ }
    · intro i
      cases i with
      | inl j =>
          exact Or.inl
            ⟨Finset.mem_union_left _ (Old.source_mem j),
              Finset.mem_union_left _ (Old.target_mem j)⟩
      | inr j =>
          exact Or.inl
            ⟨Finset.mem_union_right _ (Dummy.source_mem j),
              Finset.mem_union_right _ (Dummy.target_mem j)⟩
    · intro i j hij
      cases i with
      | inl iOld =>
          cases j with
          | inl jOld =>
              have hne : iOld ≠ jOld := by
                intro h
                exact hij (by cases h; rfl)
              simpa using Old.toPathPacking.node_disjoint hne
          | inr jDummy =>
              rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
              intro z hzOld hzDummy
              exact Finset.disjoint_left.mp hRegionDisj (hOldStay iOld hzOld)
                (hDummyStay jDummy hzDummy)
      | inr iDummy =>
          cases j with
          | inl jOld =>
              rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint, Finset.disjoint_left]
              intro z hzDummy hzOld
              exact Finset.disjoint_left.mp hRegionDisj (hOldStay jOld hzOld)
                (hDummyStay iDummy hzDummy)
          | inr jDummy =>
              have hne : iDummy ≠ jDummy := by
                intro h
                exact hij (by cases h; rfl)
              simpa using Dummy.toPathPacking.node_disjoint hne
    · intro i
      cases i with
      | inl j => exact Finset.mem_union_left _ (Old.source_mem j)
      | inr j => exact Finset.mem_union_right _ (Dummy.source_mem j)
    · intro i
      cases i with
      | inl j => exact Finset.mem_union_left _ (Old.target_mem j)
      | inr j => exact Finset.mem_union_right _ (Dummy.target_mem j)
    · constructor
      · intro i j hij
        rcases i with iOld | iDummy
        · rcases j with jOld | jDummy
          · apply congrArg Sum.inl
            have hval : (Old.path iOld).source = (Old.path jOld).source := by
              simpa using congrArg Subtype.val hij
            apply Old.source_bijective.1
            exact Subtype.ext hval
          · exfalso
            have hval : (Old.path iOld).source = (Dummy.path jDummy).source := by
              simpa using congrArg Subtype.val hij
            exact Finset.disjoint_left.mp hRegionDisj (hOldSourceRegion iOld) (by
              rw [hval]
              exact hDummySourceRegion jDummy)
        · rcases j with jOld | jDummy
          · exfalso
            have hval : (Dummy.path iDummy).source = (Old.path jOld).source := by
              simpa using congrArg Subtype.val hij
            exact Finset.disjoint_left.mp hRegionDisj (hOldSourceRegion jOld) (by
              rw [← hval]
              exact hDummySourceRegion iDummy)
          · apply congrArg Sum.inr
            have hval : (Dummy.path iDummy).source = (Dummy.path jDummy).source := by
              simpa using congrArg Subtype.val hij
            apply Dummy.source_bijective.1
            exact Subtype.ext hval
      · intro x
        have hx :
            x.1 ∈
              (S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
              (S₂DummyLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
          simpa using x.2
        rcases Finset.mem_union.mp hx with hxOld | hxDummy
        · rcases Old.source_bijective.2 ⟨x.1, hxOld⟩ with ⟨i, hi⟩
          refine ⟨Sum.inl i, ?_⟩
          apply Subtype.ext
          simpa using congrArg Subtype.val hi
        · rcases Dummy.source_bijective.2 ⟨x.1, hxDummy⟩ with ⟨i, hi⟩
          refine ⟨Sum.inr i, ?_⟩
          apply Subtype.ext
          simpa using congrArg Subtype.val hi
    · constructor
      · intro i j hij
        rcases i with iOld | iDummy
        · rcases j with jOld | jDummy
          · apply congrArg Sum.inl
            have hval : (Old.path iOld).target = (Old.path jOld).target := by
              simpa using congrArg Subtype.val hij
            apply Old.target_bijective.1
            exact Subtype.ext hval
          · exfalso
            have hval : (Old.path iOld).target = (Dummy.path jDummy).target := by
              simpa using congrArg Subtype.val hij
            exact Finset.disjoint_left.mp hRegionDisj (hOldTargetRegion iOld) (by
              rw [hval]
              exact hDummyTargetRegion jDummy)
        · rcases j with jOld | jDummy
          · exfalso
            have hval : (Dummy.path iDummy).target = (Old.path jOld).target := by
              simpa using congrArg Subtype.val hij
            exact Finset.disjoint_left.mp hRegionDisj (hOldTargetRegion jOld) (by
              rw [← hval]
              exact hDummyTargetRegion iDummy)
          · apply congrArg Sum.inr
            have hval : (Dummy.path iDummy).target = (Dummy.path jDummy).target := by
              simpa using congrArg Subtype.val hij
            apply Dummy.target_bijective.1
            exact Subtype.ext hval
      · intro x
        have hx :
            x.1 ∈
              (T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
              (T₂DummyLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
          simpa using x.2
        rcases Finset.mem_union.mp hx with hxOld | hxDummy
        · rcases Old.target_bijective.2 ⟨x.1, hxOld⟩ with ⟨i, hi⟩
          refine ⟨Sum.inl i, ?_⟩
          apply Subtype.ext
          simpa using congrArg Subtype.val hi
        · rcases Dummy.target_bijective.2 ⟨x.1, hxDummy⟩ with ⟨i, hi⟩
          refine ⟨Sum.inr i, ?_⟩
          apply Subtype.ext
          simpa using congrArg Subtype.val hi

  theorem blueAugmented_routable [DecidableEq V]
      {G : _root_.SimpleGraph V}
      (hR : RoutableIn G S₂ T₂) :
      RoutableIn
        (graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
        (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) := by
    rcases hR with ⟨P⟩
    exact ⟨blueAugmentedPerfectPathPacking
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P⟩

  theorem leafS₁_degree_one [DecidableEq V] {G : _root_.SimpleGraph V}
      (x : {x : V // x ∈ S₁}) :
      DegreeEquals
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (leafS₁ x) 1 := by
  classical
  refine degreeEquals_one_of_unique_neighbor (adj_leafS₁_old (G := G) x) ?_
  intro y hy
  rw [graph_adj] at hy
  rcases hy with ⟨hne, hrel | hrel⟩
  · cases y <;> simp [rel] at hrel
    · cases hrel
      rfl
  · cases y <;> simp [rel] at hrel

theorem leafT₁_degree_one [DecidableEq V] {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ T₁}) :
    DegreeEquals
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (leafT₁ x) 1 := by
  classical
  refine degreeEquals_one_of_unique_neighbor (adj_leafT₁_old (G := G) x) ?_
  intro y hy
  rw [graph_adj] at hy
  rcases hy with ⟨hne, hrel | hrel⟩
  · cases y <;> simp [rel] at hrel
    · cases hrel
      rfl
  · cases y <;> simp [rel] at hrel

theorem leafS₂Old_degree_one [DecidableEq V] {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ S₂}) :
    DegreeEquals
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (leafS₂Old x) 1 := by
  classical
  refine degreeEquals_one_of_unique_neighbor (adj_leafS₂Old_old (G := G) x) ?_
  intro y hy
  rw [graph_adj] at hy
  rcases hy with ⟨hne, hrel | hrel⟩
  · cases y <;> simp [rel] at hrel
    · cases hrel
      rfl
  · cases y <;> simp [rel] at hrel

theorem leafT₂Old_degree_one [DecidableEq V] {G : _root_.SimpleGraph V}
    (x : {x : V // x ∈ T₂}) :
    DegreeEquals
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (leafT₂Old x) 1 := by
  classical
  refine degreeEquals_one_of_unique_neighbor (adj_leafT₂Old_old (G := G) x) ?_
  intro y hy
  rw [graph_adj] at hy
  rcases hy with ⟨hne, hrel | hrel⟩
  · cases y <;> simp [rel] at hrel
    · cases hrel
      rfl
  · cases y <;> simp [rel] at hrel

theorem leafS₂Dummy_degree_one [DecidableEq V] {G : _root_.SimpleGraph V}
    (i : Fin δ) :
    DegreeEquals
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (leafS₂Dummy i) 1 := by
  classical
  refine degreeEquals_one_of_unique_neighbor (adj_leafS₂Dummy_dummyA (G := G) i) ?_
  intro y hy
  rw [graph_adj] at hy
  rcases hy with ⟨hne, hrel | hrel⟩
  · cases y <;> simp [rel] at hrel
    · cases hrel
      rfl
  · cases y <;> simp [rel] at hrel

theorem leafT₂Dummy_degree_one [DecidableEq V] {G : _root_.SimpleGraph V}
    (i : Fin δ) :
    DegreeEquals
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (leafT₂Dummy i) 1 := by
  classical
  refine degreeEquals_one_of_unique_neighbor (adj_leafT₂Dummy_dummyB (G := G) i) ?_
  intro y hy
  rw [graph_adj] at hy
  rcases hy with ⟨hne, hrel | hrel⟩
  · cases y <;> simp [rel] at hrel
    · cases hrel
      rfl
  · cases y <;> simp [rel] at hrel

theorem terminal_degree_one [DecidableEq V] {G : _root_.SimpleGraph V}
    {x : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hx : x ∈
      twoPairTerminalSet
        (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))) :
    DegreeEquals
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      x 1 := by
  classical
  simp only [twoPairTerminalSet, Finset.mem_union] at hx
  rcases hx with (((hx | hx) | hx) | hx)
  · rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
    exact leafS₁_degree_one (G := G) a
  · rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
    exact leafT₁_degree_one (G := G) a
  · rw [S₂Leaves, Finset.mem_union] at hx
    rcases hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
      exact leafS₂Old_degree_one (G := G) a
    · rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
      exact leafS₂Dummy_degree_one (G := G) i
  · rw [T₂Leaves, Finset.mem_union] at hx
    rcases hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
      exact leafT₂Old_degree_one (G := G) a
    · rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
      exact leafT₂Dummy_degree_one (G := G) i

/-- The component of the augmented graph containing the original graph and all
old-terminal leaves.  It deliberately excludes the dummy blue component. -/
noncomputable def oldComponentRegion :
    Finset (Theorem13AugVertex V S₁ T₁ S₂ T₂ δ) :=
  ((((oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)) ∪
      S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
    T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
    S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) ∪
    T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)

theorem old_mem_oldComponentRegion [DecidableEq V] (x : V) :
    old x ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, oldImage, Finset.mem_union]

theorem leafS₁_mem_oldComponentRegion [DecidableEq V] (x : {x : V // x ∈ S₁}) :
    leafS₁ x ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, S₁Leaves, Finset.mem_union]

theorem leafT₁_mem_oldComponentRegion [DecidableEq V] (x : {x : V // x ∈ T₁}) :
    leafT₁ x ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, T₁Leaves, Finset.mem_union]

theorem leafS₂Old_mem_oldComponentRegion [DecidableEq V] (x : {x : V // x ∈ S₂}) :
    leafS₂Old x ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, S₂OldLeaves, Finset.mem_union]

theorem leafT₂Old_mem_oldComponentRegion [DecidableEq V] (x : {x : V // x ∈ T₂}) :
    leafT₂Old x ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, T₂OldLeaves, Finset.mem_union]

theorem dummyA_not_mem_oldComponentRegion [DecidableEq V] (i : Fin δ) :
    dummyA (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) i ∉
      oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, oldImage, S₁Leaves, T₁Leaves, S₂OldLeaves, T₂OldLeaves]

theorem dummyB_not_mem_oldComponentRegion [DecidableEq V] (i : Fin δ) :
    dummyB (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) i ∉
      oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, oldImage, S₁Leaves, T₁Leaves, S₂OldLeaves, T₂OldLeaves]

theorem leafS₂Dummy_not_mem_oldComponentRegion [DecidableEq V] (i : Fin δ) :
    leafS₂Dummy (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) i ∉
      oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, oldImage, S₁Leaves, T₁Leaves, S₂OldLeaves, T₂OldLeaves]

theorem leafT₂Dummy_not_mem_oldComponentRegion [DecidableEq V] (i : Fin δ) :
    leafT₂Dummy (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) i ∉
      oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [oldComponentRegion, oldImage, S₁Leaves, T₁Leaves, S₂OldLeaves, T₂OldLeaves]

theorem rel_oldComponentRegion_closed [DecidableEq V] {G : _root_.SimpleGraph V}
    {x y : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hx : x ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (hrel :
      rel (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G x y) :
      y ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  cases x <;> try
    first
    | exact False.elim (dummyA_not_mem_oldComponentRegion
        (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) _ hx)
    | exact False.elim (dummyB_not_mem_oldComponentRegion
        (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) _ hx)
    | exact False.elim (leafS₂Dummy_not_mem_oldComponentRegion
        (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) _ hx)
    | exact False.elim (leafT₂Dummy_not_mem_oldComponentRegion
        (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) _ hx)
  · cases y <;> simp [rel] at hrel
    · exact old_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · cases y <;> simp [rel] at hrel
    · exact old_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · cases y <;> simp [rel] at hrel
    · exact old_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · cases y <;> simp [rel] at hrel
    · exact old_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · cases y <;> simp [rel] at hrel
    · exact old_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) _

theorem rel_oldComponentRegion_closed_left [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {x y : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hx : x ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (hrel :
      rel (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G y x) :
      y ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  cases y
  · exact old_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · cases x <;> simp [rel] at hrel
    exact False.elim (dummyB_not_mem_oldComponentRegion
      (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) _ hx)
  · cases x <;> simp [rel] at hrel
  · exact leafS₁_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · exact leafT₁_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · exact leafS₂Old_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · exact leafT₂Old_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) _
  · cases x <;> simp [rel] at hrel
    exact False.elim (dummyA_not_mem_oldComponentRegion
      (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) _ hx)
  · cases x <;> simp [rel] at hrel
    exact False.elim (dummyB_not_mem_oldComponentRegion
      (V := V) (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) _ hx)

theorem oldComponentRegion_adj_closed [DecidableEq V] {G : _root_.SimpleGraph V}
    {x y : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ}
    (hx : x ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj x y →
      y ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  intro hxy
  rw [Theorem13AugVertex.graph_adj] at hxy
  rcases hxy with ⟨_hne, hrel | hrel⟩
  · exact rel_oldComponentRegion_closed
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) hx hrel
  · exact rel_oldComponentRegion_closed_left
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) hx hrel

theorem vertexSet_subset_oldComponentRegion_of_source_mem [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    (hsource : P.source ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
  GraphPath.vertexSet_subset_of_source_mem_of_adj_closed P
      (oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      hsource
      (by
        intro x y hx hxy
        exact oldComponentRegion_adj_closed
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) hx hxy)

/-- A vertex in the old-image subtype has an original value. -/
theorem exists_oldValue [DecidableEq V]
    (z :
      {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ //
        z ∈ oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)}) :
    ∃ x : V, z.1 = old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
  classical
  rcases Finset.mem_image.mp z.2 with ⟨x, _hx, hxz⟩
  exact ⟨x, hxz.symm⟩

/-- Project a vertex of the old-copy subtype back to the original vertex. -/
noncomputable def oldValue [DecidableEq V]
    (z :
      {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ //
        z ∈ oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)}) : V :=
  Classical.choose (exists_oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) z)

theorem oldValue_spec [DecidableEq V]
    (z :
      {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ //
        z ∈ oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)}) :
    z.1 = old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) z) :=
  Classical.choose_spec (exists_oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) z)

@[simp] theorem oldValue_old [DecidableEq V] (x : V) :
    oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        ⟨old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
          (mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)
            (A := (Finset.univ : Finset V))).2 (by simp)⟩ = x := by
  classical
  have h :=
    oldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      ⟨old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
        (mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          (A := (Finset.univ : Finset V))).2 (by simp)⟩
  have hx :
      x =
        oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          ⟨old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
            (mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ)
              (A := (Finset.univ : Finset V))).2 (by simp)⟩ :=
    old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) h
  exact hx.symm

/-- The old-copy induced subgraph projects homomorphically back to the
original graph. -/
noncomputable def oldProjectionHom [DecidableEq V] (G : _root_.SimpleGraph V) :
    (graph (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G).induce
        {z : Theorem13AugVertex V S₁ T₁ S₂ T₂ δ |
          z ∈ oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)} →g G where
  toFun := fun z =>
    oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) z
  map_rel' := by
    intro a b hab
    have hAdj :
        (graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj a.1 b.1 := by
      simpa using hab
    have ha :=
      oldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) a
    have hb :=
      oldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) b
    rw [ha, hb, Theorem13AugVertex.graph_adj] at hAdj
    rcases hAdj with ⟨_hne, hrel | hrel⟩
    · simpa [rel] using hrel
    · have hba :
          G.Adj
            (oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) b)
            (oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) a) := by
          simpa [rel] using hrel
      exact hba.symm

theorem oldProjectionHom_injective [DecidableEq V] (G : _root_.SimpleGraph V) :
    Function.Injective
      (oldProjectionHom (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G) := by
  classical
  intro a b h
  apply Subtype.ext
  have ha :=
    oldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) a
  have hb :=
    oldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) b
  rw [ha, hb]
  exact congrArg
    (old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)) h

theorem segmentBetween_old_old_vertexSet_subset_oldImage_univ [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    {a b : V}
    (ha : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) a ∈ P.vertexSet)
    (hb : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) b ∈ P.vertexSet)
    (hregion :
      P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (hsource_not_old :
      ∀ x : V, P.source ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
    (htarget_not_old :
      ∀ x : V, P.target ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x) :
    (Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween P ha hb).vertexSet ⊆
      oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V) := by
  classical
  intro z hzseg
  have hzP : z ∈ P.vertexSet :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween_vertexSet_subset
      P ha hb hzseg
  have hzRegion :
      z ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    hregion hzP
  have hnotSource :
      P.source ∉
        (Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween P ha hb).vertexSet :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.source_not_mem_segmentBetween_of_ne P ha hb
      (hsource_not_old a) (hsource_not_old b)
  have hnotTarget :
      P.target ∉
        (Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween P ha hb).vertexSet :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.target_not_mem_segmentBetween_of_ne P ha hb
      ((htarget_not_old a).symm) ((htarget_not_old b).symm)
  cases z with
  | old x =>
      exact (mem_oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        (A := (Finset.univ : Finset V))).2 (by simp)
  | dummyA i =>
      exact False.elim
        (dummyA_not_mem_oldComponentRegion
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) i hzRegion)
  | dummyB i =>
      exact False.elim
        (dummyB_not_mem_oldComponentRegion
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) i hzRegion)
  | leafS₁ x =>
      have hend :
          P.IsEndpoint
            (leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x) :=
        Lax17Proofs.SimpleGraph.GraphPath.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          P
          (leafS₁_degree_one (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) x)
          hzP
      rcases hend with hsrc | htgt
      · exact False.elim (hnotSource (by simpa [hsrc] using hzseg))
      · exact False.elim (hnotTarget (by simpa [htgt] using hzseg))
  | leafT₁ x =>
      have hend :
          P.IsEndpoint
            (leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x) :=
        Lax17Proofs.SimpleGraph.GraphPath.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          P
          (leafT₁_degree_one (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) x)
          hzP
      rcases hend with hsrc | htgt
      · exact False.elim (hnotSource (by simpa [hsrc] using hzseg))
      · exact False.elim (hnotTarget (by simpa [htgt] using hzseg))
  | leafS₂Old x =>
      have hend :
          P.IsEndpoint
            (leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x) :=
        Lax17Proofs.SimpleGraph.GraphPath.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          P
          (leafS₂Old_degree_one (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) x)
          hzP
      rcases hend with hsrc | htgt
      · exact False.elim (hnotSource (by simpa [hsrc] using hzseg))
      · exact False.elim (hnotTarget (by simpa [htgt] using hzseg))
  | leafT₂Old x =>
      have hend :
          P.IsEndpoint
            (leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x) :=
        Lax17Proofs.SimpleGraph.GraphPath.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
          P
          (leafT₂Old_degree_one (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) x)
          hzP
      rcases hend with hsrc | htgt
      · exact False.elim (hnotSource (by simpa [hsrc] using hzseg))
      · exact False.elim (hnotTarget (by simpa [htgt] using hzseg))
  | leafS₂Dummy i =>
      exact False.elim
        (leafS₂Dummy_not_mem_oldComponentRegion
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) i hzRegion)
  | leafT₂Dummy i =>
      exact False.elim
        (leafT₂Dummy_not_mem_oldComponentRegion
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) i hzRegion)

noncomputable def oldSegmentProjectedPath [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    {a b : V}
    (ha : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) a ∈ P.vertexSet)
    (hb : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) b ∈ P.vertexSet)
    (hregion :
      P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (hsource_not_old :
      ∀ x : V, P.source ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
    (htarget_not_old :
      ∀ x : V, P.target ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x) :
    Lax17Proofs.SimpleGraph.GraphPath G :=
  let U :=
    oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)
  let R :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween P ha hb
  let hR : R.vertexSet ⊆ U :=
    segmentBetween_old_old_vertexSet_subset_oldImage_univ
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      P ha hb hregion hsource_not_old htarget_not_old
  Lax17Proofs.SimpleGraph.TreewidthSparsifier.Theorem13AugVertex.GraphPath.mapHomInjective
    (R.induce U hR)
    (oldProjectionHom (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
    (oldProjectionHom_injective (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) G)

theorem oldSegmentProjectedPath_source [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    {a b : V}
    (ha : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) a ∈ P.vertexSet)
    (hb : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) b ∈ P.vertexSet)
    (hregion :
      P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (hsource_not_old :
      ∀ x : V, P.source ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
    (htarget_not_old :
      ∀ x : V, P.target ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x) :
    (oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      P ha hb hregion hsource_not_old htarget_not_old).source = a := by
  classical
  simp [oldSegmentProjectedPath, oldProjectionHom]

theorem oldSegmentProjectedPath_target [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    {a b : V}
    (ha : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) a ∈ P.vertexSet)
    (hb : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) b ∈ P.vertexSet)
    (hregion :
      P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (hsource_not_old :
      ∀ x : V, P.source ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
    (htarget_not_old :
      ∀ x : V, P.target ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x) :
    (oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      P ha hb hregion hsource_not_old htarget_not_old).target = b := by
  classical
  simp [oldSegmentProjectedPath, oldProjectionHom]

theorem old_mem_of_mem_oldSegmentProjectedPath_vertexSet [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    {a b x : V}
    (ha : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) a ∈ P.vertexSet)
    (hb : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) b ∈ P.vertexSet)
    (hregion :
      P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (hsource_not_old :
      ∀ x : V, P.source ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
    (htarget_not_old :
      ∀ x : V, P.target ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
    (hx :
      x ∈ (oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        P ha hb hregion hsource_not_old htarget_not_old).vertexSet) :
    old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈ P.vertexSet := by
  classical
  let U :=
    oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)
  let R :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween P ha hb
  let hR : R.vertexSet ⊆ U :=
    segmentBetween_old_old_vertexSet_subset_oldImage_univ
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      P ha hb hregion hsource_not_old htarget_not_old
  have hxImage :
      x ∈
        (Lax17Proofs.SimpleGraph.GraphPath.induce R U hR).vertexSet.image
          (fun z =>
            oldProjectionHom (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) G z) := by
    simpa [oldSegmentProjectedPath, R, U, hR] using hx
  rcases Finset.mem_image.mp hxImage with ⟨z, hz, hzx⟩
  have hzR : z.1 ∈ R.vertexSet := by
    exact (Lax17Proofs.SimpleGraph.GraphPath.mem_induce_vertexSet R U hR z).1 hz
  have hval :
      z.1 = old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
    have hOldValue :
        oldValue (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) z = x := by
      simpa [oldProjectionHom] using hzx
    have hspec :=
      oldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) z
    simpa [hOldValue] using hspec
  have hOldR :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈ R.vertexSet := by
    simpa [hval] using hzR
  exact
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween_vertexSet_subset
      P ha hb hOldR

theorem old_edge_mem_of_mem_oldSegmentProjectedPath_edgeSet [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    {a b x y : V}
    (ha : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) a ∈ P.vertexSet)
    (hb : old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) b ∈ P.vertexSet)
    (hregion :
      P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (hsource_not_old :
      ∀ x : V, P.source ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
    (htarget_not_old :
      ∀ x : V, P.target ≠ old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
    (hxy :
      s(x, y) ∈ (oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        P ha hb hregion hsource_not_old htarget_not_old).edgeSet) :
    s(old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) y) ∈ P.edgeSet := by
  classical
  let U :=
    oldImage (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (Finset.univ : Finset V)
  let R :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween P ha hb
  let hR : R.vertexSet ⊆ U :=
    segmentBetween_old_old_vertexSet_subset_oldImage_univ
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      P ha hb hregion hsource_not_old htarget_not_old
  have hxyImage :
      s(x, y) ∈
        (Lax17Proofs.SimpleGraph.GraphPath.induce R U hR).edgeSet.image
          (fun e =>
            Sym2.map
              (fun z =>
                oldProjectionHom (V := V) (S₁ := S₁) (T₁ := T₁)
                  (S₂ := S₂) (T₂ := T₂) (δ := δ) G z)
              e) := by
    simpa [oldSegmentProjectedPath, R, U, hR] using hxy
  rcases Finset.mem_image.mp hxyImage with ⟨e, he, hemap⟩
  have heR :
      Sym2.map Subtype.val e ∈ R.edgeSet :=
    (Lax17Proofs.SimpleGraph.GraphPath.mem_induce_edgeSet R U hR e).1 he
  have heOld :
      Sym2.map Subtype.val e =
        s(old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) y) := by
    induction e using Sym2.ind with
    | h p q =>
        have hcongr :=
          congrArg
            (fun e : Sym2 V =>
              Sym2.map
                (old (V := V) (S₁ := S₁) (T₁ := T₁)
                  (S₂ := S₂) (T₂ := T₂) (δ := δ))
                e) hemap
        simpa [oldProjectionHom,
          oldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) p,
          oldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) q] using hcongr
  have hOldR :
      s(old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) y) ∈ R.edgeSet := by
    simpa [heOld] using heR
  exact
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.segmentBetween_edgeSet_subset
      P ha hb hOldR

theorem old_mem_of_source_leafS₁ [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    (x : {x : V // x ∈ S₁})
    (hsource : P.source = leafS₁ x)
    (htarget : P.target ≠ leafS₁ x) :
    old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x.1 ∈ P.vertexSet := by
  classical
  have hsource_ne_target : P.source ≠ P.target := by
    intro h
    exact htarget (by
      calc
        P.target = P.source := h.symm
        _ = leafS₁ x := hsource)
  rcases GraphPath.exists_forward_edge_of_mem_not_target P
      (by simpa [hsource] using GraphPath.source_mem_vertexSet P)
      hsource_ne_target with
    ⟨y, he, _hbefore, _hne⟩
  have hyMem : y ∈ P.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet P he).2
  have hAdj :
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafS₁ x) y := by
    simpa [hsource] using GraphPath.edgeSet_subset_edgeSet P he
  have hy : y = old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x.1 :=
    (adj_leafS₁_iff (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) x).1 hAdj
  simpa [hy] using hyMem

theorem old_mem_of_target_leafT₁ [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    (x : {x : V // x ∈ T₁})
    (htarget : P.target = leafT₁ x)
    (hsource : P.source ≠ leafT₁ x) :
    old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x.1 ∈ P.vertexSet := by
  classical
  have htarget_ne_source : P.target ≠ P.source := by
    intro h
    exact hsource (by
      calc
        P.source = P.target := h.symm
        _ = leafT₁ x := htarget)
  rcases GraphPath.exists_backward_edge_of_mem_not_source P
      (by simpa [htarget] using GraphPath.target_mem_vertexSet P)
      htarget_ne_source with
    ⟨y, he, _hbefore, _hne⟩
  have hyMem : y ∈ P.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet P he).1
  have hAdj :
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafT₁ x) y := by
    have hyAdj :
        (graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj y (leafT₁ x) := by
      simpa [htarget] using GraphPath.edgeSet_subset_edgeSet P he
    exact hyAdj.symm
  have hy : y = old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x.1 :=
    (adj_leafT₁_iff (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) x).1 hAdj
  simpa [hy] using hyMem

theorem old_mem_of_source_leafS₂Old [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    (x : {x : V // x ∈ S₂})
    (hsource : P.source = leafS₂Old x)
    (htarget : P.target ≠ leafS₂Old x) :
    old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x.1 ∈ P.vertexSet := by
  classical
  have hsource_ne_target : P.source ≠ P.target := by
    intro h
    exact htarget (by
      calc
        P.target = P.source := h.symm
        _ = leafS₂Old x := hsource)
  rcases GraphPath.exists_forward_edge_of_mem_not_target P
      (by simpa [hsource] using GraphPath.source_mem_vertexSet P)
      hsource_ne_target with
    ⟨y, he, _hbefore, _hne⟩
  have hyMem : y ∈ P.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet P he).2
  have hAdj :
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafS₂Old x) y := by
    simpa [hsource] using GraphPath.edgeSet_subset_edgeSet P he
  have hy : y = old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x.1 :=
    (adj_leafS₂Old_iff (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) x).1 hAdj
  simpa [hy] using hyMem

theorem old_mem_of_target_leafT₂Old [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    (x : {x : V // x ∈ T₂})
    (htarget : P.target = leafT₂Old x)
    (hsource : P.source ≠ leafT₂Old x) :
    old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x.1 ∈ P.vertexSet := by
  classical
  have htarget_ne_source : P.target ≠ P.source := by
    intro h
    exact hsource (by
      calc
        P.source = P.target := h.symm
        _ = leafT₂Old x := htarget)
  rcases GraphPath.exists_backward_edge_of_mem_not_source P
      (by simpa [htarget] using GraphPath.target_mem_vertexSet P)
      htarget_ne_source with
    ⟨y, he, _hbefore, _hne⟩
  have hyMem : y ∈ P.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet P he).1
  have hAdj :
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj (leafT₂Old x) y := by
    have hyAdj :
        (graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G).Adj y (leafT₂Old x) := by
      simpa [htarget] using GraphPath.edgeSet_subset_edgeSet P he
    exact hyAdj.symm
  have hy : y = old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x.1 :=
    (adj_leafT₂Old_iff (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) (G := G) x).1 hAdj
  simpa [hy] using hyMem

noncomputable def redSourceValue [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) : {x : V // x ∈ S₁} :=
  leafS₁Value (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) (P.source_mem i)

noncomputable def redTargetValue [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) : {x : V // x ∈ T₁} :=
  leafT₁Value (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) (P.target_mem i)

theorem redSourceValue_spec [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) :
    (P.path i).source =
      leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        (redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i) :=
  leafS₁Value_spec (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) (P.source_mem i)

theorem redTargetValue_spec [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) :
    (P.path i).target =
      leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        (redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i) :=
  leafT₁Value_spec (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ) (P.target_mem i)

noncomputable def strippedRedPath [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) :
    Lax17Proofs.SimpleGraph.GraphPath G := by
  classical
  let s :=
    redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  let t :=
    redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have hsource :
      (P.path i).source =
        leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s := by
    simpa [s] using
      redSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget :
      (P.path i).target =
        leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t := by
    simpa [t] using
      redTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget_ne_sourceLeaf :
      (P.path i).target ≠
        leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s := by
    intro h
    rw [htarget] at h
    cases h
  have hsource_ne_targetLeaf :
      (P.path i).source ≠
        leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t := by
    intro h
    rw [hsource] at h
    cases h
  have ha :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) s.1 ∈
        (P.path i).vertexSet :=
    old_mem_of_source_leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) s hsource htarget_ne_sourceLeaf
  have hb :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) t.1 ∈
        (P.path i).vertexSet :=
    old_mem_of_target_leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) t htarget hsource_ne_targetLeaf
  have hsourceRegion :
      (P.path i).source ∈
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
    rw [hsource]
    exact leafS₁_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) s
  have hregion :
      (P.path i).vertexSet ⊆
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_source_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) hsourceRegion
  have hsource_not_old :
      ∀ x : V, (P.path i).source ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
    intro x h
    rw [hsource] at h
    cases h
  have htarget_not_old :
      ∀ x : V, (P.path i).target ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
    intro x h
    rw [htarget] at h
    cases h
  exact oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ)
    (P.path i) ha hb hregion hsource_not_old htarget_not_old

theorem strippedRedPath_source [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) :
    (strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).source =
      (redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).1 := by
  classical
  simp [strippedRedPath, oldSegmentProjectedPath_source]

theorem strippedRedPath_target [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) :
    (strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).target =
      (redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).1 := by
  classical
  simp [strippedRedPath, oldSegmentProjectedPath_target]

theorem old_mem_of_mem_strippedRedPath_vertexSet [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) {x : V}
    (hx :
      x ∈ (strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).vertexSet) :
    old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈ (P.path i).vertexSet := by
  classical
  let s :=
    redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  let t :=
    redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have hsource :
      (P.path i).source =
        leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s := by
    simpa [s] using
      redSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget :
      (P.path i).target =
        leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t := by
    simpa [t] using
      redTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget_ne_sourceLeaf :
      (P.path i).target ≠
        leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s := by
    intro h
    rw [htarget] at h
    cases h
  have hsource_ne_targetLeaf :
      (P.path i).source ≠
        leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t := by
    intro h
    rw [hsource] at h
    cases h
  have ha :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) s.1 ∈
        (P.path i).vertexSet :=
    old_mem_of_source_leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) s hsource htarget_ne_sourceLeaf
  have hb :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) t.1 ∈
        (P.path i).vertexSet :=
    old_mem_of_target_leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) t htarget hsource_ne_targetLeaf
  have hsourceRegion :
      (P.path i).source ∈
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
    rw [hsource]
    exact leafS₁_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) s
  have hregion :
      (P.path i).vertexSet ⊆
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_source_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) hsourceRegion
  have hsource_not_old :
      ∀ y : V, (P.path i).source ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) y := by
    intro y h
    rw [hsource] at h
    cases h
  have htarget_not_old :
      ∀ y : V, (P.path i).target ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) y := by
    intro y h
    rw [htarget] at h
    cases h
  have hx' :
      x ∈
        (oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          (P.path i) ha hb hregion hsource_not_old htarget_not_old).vertexSet := by
    simpa [strippedRedPath] using hx
  exact
    old_mem_of_mem_oldSegmentProjectedPath_vertexSet
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) ha hb hregion hsource_not_old htarget_not_old hx'

theorem old_edge_mem_of_mem_strippedRedPath_edgeSet [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) {x y : V}
    (hxy :
      s(x, y) ∈ (strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).edgeSet) :
    s(old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) y) ∈ (P.path i).edgeSet := by
  classical
  let s₀ :=
    redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  let t₀ :=
    redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have hsource :
      (P.path i).source =
        leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s₀ := by
    simpa [s₀] using
      redSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget :
      (P.path i).target =
        leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t₀ := by
    simpa [t₀] using
      redTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget_ne_sourceLeaf :
      (P.path i).target ≠
        leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s₀ := by
    intro h
    rw [htarget] at h
    cases h
  have hsource_ne_targetLeaf :
      (P.path i).source ≠
        leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t₀ := by
    intro h
    rw [hsource] at h
    cases h
  have ha :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) s₀.1 ∈
        (P.path i).vertexSet :=
    old_mem_of_source_leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) s₀ hsource htarget_ne_sourceLeaf
  have hb :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) t₀.1 ∈
        (P.path i).vertexSet :=
    old_mem_of_target_leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) t₀ htarget hsource_ne_targetLeaf
  have hsourceRegion :
      (P.path i).source ∈
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
    rw [hsource]
    exact leafS₁_mem_oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) s₀
  have hregion :
      (P.path i).vertexSet ⊆
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_source_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) hsourceRegion
  have hsource_not_old :
      ∀ z : V, (P.path i).source ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) z := by
    intro z h
    rw [hsource] at h
    cases h
  have htarget_not_old :
      ∀ z : V, (P.path i).target ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) z := by
    intro z h
    rw [htarget] at h
    cases h
  have hxy' :
      s(x, y) ∈
        (oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          (P.path i) ha hb hregion hsource_not_old htarget_not_old).edgeSet := by
    simpa [strippedRedPath] using hxy
  exact
    old_edge_mem_of_mem_oldSegmentProjectedPath_edgeSet
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i) ha hb hregion hsource_not_old htarget_not_old hxy'

noncomputable def strippedRedPerfectPathPacking [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))) :
    PerfectPathPacking G S₁ T₁ where
  toPathPacking := {
    Index := P.Index
    path := fun i =>
      strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
    connects := by
      intro i
      exact Or.inl
        ⟨by
          simpa [strippedRedPath_source] using
            (redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2,
         by
          simpa [strippedRedPath_target] using
            (redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint,
        Finset.disjoint_left]
      intro x hxi hxj
      have hOldi :
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈
            (P.path i).vertexSet :=
        old_mem_of_mem_strippedRedPath_vertexSet
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i hxi
      have hOldj :
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈
            (P.path j).vertexSet :=
        old_mem_of_mem_strippedRedPath_vertexSet
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P j hxj
      exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij)
        hOldi hOldj
  }
  source_mem := by
    intro i
    simpa [strippedRedPath_source] using
      (redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2
  target_mem := by
    intro i
    simpa [strippedRedPath_target] using
      (redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2
  source_bijective := by
    classical
    constructor
    · intro i j hij
      apply P.source_bijective.1
      apply Subtype.ext
      have hsrc :
          (strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).source =
          (strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P j).source :=
        congrArg (fun x : {v // v ∈ S₁} => x.1) hij
      have hval :
          (redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).1 =
          (redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P j).1 := by
        simpa [strippedRedPath_source] using hsrc
      have hsource_eq :
          (P.path i).source = (P.path j).source := by
        rw [redSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i,
          redSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P j]
        exact congrArg
          (leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ))
          (Subtype.ext hval)
      exact hsource_eq
    · intro x
      have hxLeaf :
          leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈
            S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
        exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
      rcases P.source_bijective.2 ⟨_, hxLeaf⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have hsourceLeaf :
          (P.path i).source =
            leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x :=
        congrArg (fun y : {v // v ∈ S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)} => y.1) hi
      have hvalue :
          (redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i) = x := by
        have hleaf :
            leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ)
              (redSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ) P i) =
            leafS₁ (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
          exact
            (redSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).symm.trans hsourceLeaf
        cases hleaf
        rfl
      simpa [strippedRedPath_source, hvalue]
  target_bijective := by
    classical
    constructor
    · intro i j hij
      apply P.target_bijective.1
      apply Subtype.ext
      have htgt :
          (strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).target =
          (strippedRedPath (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P j).target :=
        congrArg (fun x : {v // v ∈ T₁} => x.1) hij
      have hval :
          (redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).1 =
          (redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P j).1 := by
        simpa [strippedRedPath_target] using htgt
      have htarget_eq :
          (P.path i).target = (P.path j).target := by
        rw [redTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i,
          redTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P j]
        exact congrArg
          (leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ))
          (Subtype.ext hval)
      exact htarget_eq
    · intro x
      have hxLeaf :
          leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈
            T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
        exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
      rcases P.target_bijective.2 ⟨_, hxLeaf⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have htargetLeaf :
          (P.path i).target =
            leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x :=
        congrArg (fun y : {v // v ∈ T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)} => y.1) hi
      have hvalue :
          (redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i) = x := by
        have hleaf :
            leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ)
              (redTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ) P i) =
            leafT₁ (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
          exact
            (redTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).symm.trans htargetLeaf
        cases hleaf
        rfl
      simpa [strippedRedPath_target, hvalue]

theorem vertexSet_subset_oldComponentRegion_of_target_mem [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    (htarget : P.target ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  have hrev :
      P.reverse.vertexSet ⊆ oldComponentRegion
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_source_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      P.reverse (by simpa using htarget)
  intro z hz
  exact hrev (by simpa using hz)

theorem target_mem_T₂OldLeaves_of_source_mem_S₂OldLeaves [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    (hsource :
      P.source ∈ S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (htarget :
      P.target ∈ T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    P.target ∈ T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  have hsourceRegion :
      P.source ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
    rcases Finset.mem_image.mp hsource with ⟨x, _hx, hx⟩
    rw [← hx]
    exact leafS₂Old_mem_oldComponentRegion
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x
  have hregion :
      P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_source_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P hsourceRegion
  have htargetRegion :
      P.target ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    hregion (GraphPath.target_mem_vertexSet P)
  rw [T₂Leaves_eq_old_union_dummy] at htarget
  rcases Finset.mem_union.mp htarget with hOld | hDummy
  · exact hOld
  · rcases Finset.mem_image.mp hDummy with ⟨i, _hi, hi⟩
    rw [← hi] at htargetRegion
    exact False.elim
      (leafT₂Dummy_not_mem_oldComponentRegion
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) i htargetRegion)

theorem source_mem_S₂OldLeaves_of_target_mem_T₂OldLeaves [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : Lax17Proofs.SimpleGraph.GraphPath
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G))
    (hsource :
      P.source ∈ S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
    (htarget :
      P.target ∈ T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)) :
    P.source ∈ S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  have htargetRegion :
      P.target ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
    rcases Finset.mem_image.mp htarget with ⟨x, _hx, hx⟩
    rw [← hx]
    exact leafT₂Old_mem_oldComponentRegion
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x
  have hregion :
      P.vertexSet ⊆ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_target_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P htargetRegion
  have hsourceRegion :
      P.source ∈ oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    hregion (GraphPath.source_mem_vertexSet P)
  rw [S₂Leaves_eq_old_union_dummy] at hsource
  rcases Finset.mem_union.mp hsource with hOld | hDummy
  · exact hOld
  · rcases Finset.mem_image.mp hDummy with ⟨i, _hi, hi⟩
    rw [← hi] at hsourceRegion
    exact False.elim
      (leafS₂Dummy_not_mem_oldComponentRegion
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) i hsourceRegion)

noncomputable def blueOldIndexSet [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))) :
    Finset P.Index :=
  Finset.univ.filter fun i =>
    (P.path i).source ∈
      S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)

theorem mem_blueOldIndexSet_iff [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : P.Index) :
    i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P ↔
    (P.path i).source ∈
      S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
  classical
  simp [blueOldIndexSet]

noncomputable def blueOldSourceValue [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P}) : {x : V // x ∈ S₂} :=
  leafS₂OldValue (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ)
    ((mem_blueOldIndexSet_iff (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i.1).1 i.2)

theorem blueOldSourceValue_spec [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P}) :
    (P.path i.1).source =
      leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        (blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i) :=
  leafS₂OldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ)
    ((mem_blueOldIndexSet_iff (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i.1).1 i.2)

noncomputable def blueOldTargetValue [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P}) : {x : V // x ∈ T₂} :=
  leafT₂OldValue (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ)
    (target_mem_T₂OldLeaves_of_source_mem_S₂OldLeaves
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1)
      ((mem_blueOldIndexSet_iff (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i.1).1 i.2)
      (P.target_mem i.1))

theorem blueOldTargetValue_spec [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P}) :
    (P.path i.1).target =
      leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)
        (blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i) :=
  leafT₂OldValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ)
    (target_mem_T₂OldLeaves_of_source_mem_S₂OldLeaves
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1)
      ((mem_blueOldIndexSet_iff (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i.1).1 i.2)
      (P.target_mem i.1))

noncomputable def strippedBlueOldPath [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P}) :
    Lax17Proofs.SimpleGraph.GraphPath G := by
  classical
  let s :=
    blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  let t :=
    blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have hsource :
      (P.path i.1).source =
        leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s := by
    simpa [s] using
      blueOldSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget :
      (P.path i.1).target =
        leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t := by
    simpa [t] using
      blueOldTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget_ne_sourceLeaf :
      (P.path i.1).target ≠
        leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s := by
    intro h
    rw [htarget] at h
    cases h
  have hsource_ne_targetLeaf :
      (P.path i.1).source ≠
        leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t := by
    intro h
    rw [hsource] at h
    cases h
  have ha :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) s.1 ∈
        (P.path i.1).vertexSet :=
    old_mem_of_source_leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) s hsource htarget_ne_sourceLeaf
  have hb :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) t.1 ∈
        (P.path i.1).vertexSet :=
    old_mem_of_target_leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) t htarget hsource_ne_targetLeaf
  have hsourceRegion :
      (P.path i.1).source ∈
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
    rw [hsource]
    exact leafS₂Old_mem_oldComponentRegion
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) s
  have hregion :
      (P.path i.1).vertexSet ⊆
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_source_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) hsourceRegion
  have hsource_not_old :
      ∀ x : V, (P.path i.1).source ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
    intro x h
    rw [hsource] at h
    cases h
  have htarget_not_old :
      ∀ x : V, (P.path i.1).target ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
    intro x h
    rw [htarget] at h
    cases h
  exact oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
    (S₂ := S₂) (T₂ := T₂) (δ := δ)
    (P.path i.1) ha hb hregion hsource_not_old htarget_not_old

theorem strippedBlueOldPath_source [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P}) :
    (strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).source =
      (blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).1 := by
  classical
  simp [strippedBlueOldPath, oldSegmentProjectedPath_source]

theorem strippedBlueOldPath_target [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P}) :
    (strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).target =
      (blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).1 := by
  classical
  simp [strippedBlueOldPath, oldSegmentProjectedPath_target]

theorem old_mem_of_mem_strippedBlueOldPath_vertexSet [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P})
    {x : V}
    (hx :
      x ∈ (strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).vertexSet) :
    old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈ (P.path i.1).vertexSet := by
  classical
  let s :=
    blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  let t :=
    blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have hsource :
      (P.path i.1).source =
        leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s := by
    simpa [s] using
      blueOldSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget :
      (P.path i.1).target =
        leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t := by
    simpa [t] using
      blueOldTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget_ne_sourceLeaf :
      (P.path i.1).target ≠
        leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s := by
    intro h
    rw [htarget] at h
    cases h
  have hsource_ne_targetLeaf :
      (P.path i.1).source ≠
        leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t := by
    intro h
    rw [hsource] at h
    cases h
  have ha :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) s.1 ∈
        (P.path i.1).vertexSet :=
    old_mem_of_source_leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) s hsource htarget_ne_sourceLeaf
  have hb :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) t.1 ∈
        (P.path i.1).vertexSet :=
    old_mem_of_target_leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) t htarget hsource_ne_targetLeaf
  have hsourceRegion :
      (P.path i.1).source ∈
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
    rw [hsource]
    exact leafS₂Old_mem_oldComponentRegion
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) s
  have hregion :
      (P.path i.1).vertexSet ⊆
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_source_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) hsourceRegion
  have hsource_not_old :
      ∀ y : V, (P.path i.1).source ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) y := by
    intro y h
    rw [hsource] at h
    cases h
  have htarget_not_old :
      ∀ y : V, (P.path i.1).target ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) y := by
    intro y h
    rw [htarget] at h
    cases h
  have hx' :
      x ∈
        (oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          (P.path i.1) ha hb hregion hsource_not_old htarget_not_old).vertexSet := by
    simpa [strippedBlueOldPath] using hx
  exact
    old_mem_of_mem_oldSegmentProjectedPath_vertexSet
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) ha hb hregion hsource_not_old htarget_not_old hx'

theorem old_edge_mem_of_mem_strippedBlueOldPath_edgeSet [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (i : {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P})
    {x y : V}
    (hxy :
      s(x, y) ∈ (strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).edgeSet) :
    s(old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) y) ∈ (P.path i.1).edgeSet := by
  classical
  let s₀ :=
    blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  let t₀ :=
    blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have hsource :
      (P.path i.1).source =
        leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s₀ := by
    simpa [s₀] using
      blueOldSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget :
      (P.path i.1).target =
        leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t₀ := by
    simpa [t₀] using
      blueOldTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
  have htarget_ne_sourceLeaf :
      (P.path i.1).target ≠
        leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) s₀ := by
    intro h
    rw [htarget] at h
    cases h
  have hsource_ne_targetLeaf :
      (P.path i.1).source ≠
        leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) t₀ := by
    intro h
    rw [hsource] at h
    cases h
  have ha :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) s₀.1 ∈
        (P.path i.1).vertexSet :=
    old_mem_of_source_leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) s₀ hsource htarget_ne_sourceLeaf
  have hb :
      old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) t₀.1 ∈
        (P.path i.1).vertexSet :=
    old_mem_of_target_leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) t₀ htarget hsource_ne_targetLeaf
  have hsourceRegion :
      (P.path i.1).source ∈
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
    rw [hsource]
    exact leafS₂Old_mem_oldComponentRegion
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) s₀
  have hregion :
      (P.path i.1).vertexSet ⊆
        oldComponentRegion (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
    vertexSet_subset_oldComponentRegion_of_source_mem
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) hsourceRegion
  have hsource_not_old :
      ∀ z : V, (P.path i.1).source ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) z := by
    intro z h
    rw [hsource] at h
    cases h
  have htarget_not_old :
      ∀ z : V, (P.path i.1).target ≠
        old (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) z := by
    intro z h
    rw [htarget] at h
    cases h
  have hxy' :
      s(x, y) ∈
        (oldSegmentProjectedPath (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          (P.path i.1) ha hb hregion hsource_not_old htarget_not_old).edgeSet := by
    simpa [strippedBlueOldPath] using hxy
  exact
    old_edge_mem_of_mem_oldSegmentProjectedPath_edgeSet
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
      (P.path i.1) ha hb hregion hsource_not_old htarget_not_old hxy'

noncomputable def strippedBlueOldPerfectPathPacking [DecidableEq V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))) :
    PerfectPathPacking G S₂ T₂ where
  toPathPacking := {
    Index := {i : P.Index //
      i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P}
    path := fun i =>
      strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
    connects := by
      intro i
      exact Or.inl
        ⟨by
          simpa [strippedBlueOldPath_source] using
            (blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2,
         by
          simpa [strippedBlueOldPath_target] using
            (blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2⟩
    node_disjoint := by
      classical
      intro i j hij
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint,
        Finset.disjoint_left]
      intro x hxi hxj
      have hOldi :
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈
            (P.path i.1).vertexSet :=
        old_mem_of_mem_strippedBlueOldPath_vertexSet
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i hxi
      have hOldj :
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈
            (P.path j.1).vertexSet :=
        old_mem_of_mem_strippedBlueOldPath_vertexSet
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P j hxj
      have hidx : i.1 ≠ j.1 := by
        intro h
        exact hij (Subtype.ext h)
      exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hidx)
        hOldi hOldj
  }
  source_mem := by
    intro i
    simpa [strippedBlueOldPath_source] using
      (blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2
  target_mem := by
    intro i
    simpa [strippedBlueOldPath_target] using
      (blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2
  source_bijective := by
    classical
    constructor
    · intro i j hij
      apply Subtype.ext
      apply P.source_bijective.1
      apply Subtype.ext
      have hsrc :
          (strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).source =
          (strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P j).source :=
        congrArg (fun x : {v // v ∈ S₂} => x.1) hij
      have hval :
          (blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).1 =
          (blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P j).1 := by
        simpa [strippedBlueOldPath_source] using hsrc
      have hsource_eq :
          (P.path i.1).source = (P.path j.1).source := by
        rw [blueOldSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i,
          blueOldSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P j]
        exact congrArg
          (leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ))
          (Subtype.ext hval)
      exact hsource_eq
    · intro x
      have hxLeaf :
          leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈
            S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
        rw [S₂Leaves_eq_old_union_dummy]
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨x, by simp, rfl⟩)
      rcases P.source_bijective.2 ⟨_, hxLeaf⟩ with ⟨i, hi⟩
      have hiOld :
          i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P := by
        rw [mem_blueOldIndexSet_iff (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i]
        have hsourceLeaf :
            (P.path i).source =
              leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ) x :=
          congrArg (fun y : {v // v ∈ S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ)} => y.1) hi
        rw [hsourceLeaf]
        exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
      refine ⟨⟨i, hiOld⟩, ?_⟩
      apply Subtype.ext
      have hsourceLeaf :
          (P.path i).source =
            leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x :=
        congrArg (fun y : {v // v ∈ S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)} => y.1) hi
      have hvalue :
          (blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P ⟨i, hiOld⟩) = x := by
        have hleaf :
            leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ)
              (blueOldSourceValue (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ) P ⟨i, hiOld⟩) =
            leafS₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
          exact
            (blueOldSourceValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) P ⟨i, hiOld⟩).symm.trans
              hsourceLeaf
        cases hleaf
        rfl
      simpa [strippedBlueOldPath_source, hvalue]
  target_bijective := by
    classical
    constructor
    · intro i j hij
      apply Subtype.ext
      apply P.target_bijective.1
      apply Subtype.ext
      have htgt :
          (strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).target =
          (strippedBlueOldPath (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P j).target :=
        congrArg (fun x : {v // v ∈ T₂} => x.1) hij
      have hval :
          (blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).1 =
          (blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P j).1 := by
        simpa [strippedBlueOldPath_target] using htgt
      have htarget_eq :
          (P.path i.1).target = (P.path j.1).target := by
        rw [blueOldTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i,
          blueOldTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P j]
        exact congrArg
          (leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ))
          (Subtype.ext hval)
      exact htarget_eq
    · intro x
      have hxLeaf :
          leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ∈
            T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
        rw [T₂Leaves_eq_old_union_dummy]
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨x, by simp, rfl⟩)
      rcases P.target_bijective.2 ⟨_, hxLeaf⟩ with ⟨i, hi⟩
      have htargetLeaf :
          (P.path i).target =
            leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x :=
        congrArg (fun y : {v // v ∈ T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)} => y.1) hi
      have hiTargetOld :
          (P.path i).target ∈
            T₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) := by
        rw [htargetLeaf]
        exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
      have hiSourceOld :
          (P.path i).source ∈
            S₂OldLeaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) :=
        source_mem_S₂OldLeaves_of_target_mem_T₂OldLeaves
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)
          (P.path i) (P.source_mem i) hiTargetOld
      have hiOld :
          i ∈ blueOldIndexSet (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P := by
        exact (mem_blueOldIndexSet_iff (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i).2 hiSourceOld
      refine ⟨⟨i, hiOld⟩, ?_⟩
      apply Subtype.ext
      have hvalue :
          (blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P ⟨i, hiOld⟩) = x := by
        have hleaf :
            leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ)
              (blueOldTargetValue (V := V) (S₁ := S₁) (T₁ := T₁)
                (S₂ := S₂) (T₂ := T₂) (δ := δ) P ⟨i, hiOld⟩) =
            leafT₂Old (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) x := by
          exact
            (blueOldTargetValue_spec (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := δ) P ⟨i, hiOld⟩).symm.trans
              htargetLeaf
        cases hleaf
        rfl
      simpa [strippedBlueOldPath_target, hvalue]

/-- Edges in the stripped red/old-blue routings lift to edges in the
augmented red/blue union by the old-vertex embedding. -/
theorem strippedUnion_adj_old [Fintype V] {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (Q : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    {x y : V}
    (hxy :
      (twoPackingUnionGraph
        (strippedRedPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
        (strippedBlueOldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) Q)).Adj x y) :
    (twoPackingUnionGraph P Q).Adj
      (old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
      (old (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) y) := by
  classical
  let Pred :=
    strippedRedPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P
  let Qold :=
    strippedBlueOldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) Q
  rcases (show
      Pred.toPathPacking.spanningGraph.Adj x y ∨
        Qold.toPathPacking.spanningGraph.Adj x y by
      simpa [Pred, Qold, twoPackingUnionGraph] using hxy) with hred | hblue
  · rcases (Pred.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1 hred with
      ⟨⟨i, he⟩, hne⟩
    have heOld :
        s(old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) y) ∈
          (P.path i).edgeSet := by
      simpa [Pred, strippedRedPerfectPathPacking] using
        old_edge_mem_of_mem_strippedRedPath_edgeSet
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P i
          (x := x) (y := y) he
    have hneOld :
        old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ≠
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) y := by
      intro h
      exact hne
        (old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) h)
    have hredAdj :
        P.toPathPacking.spanningGraph.Adj
          (old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
          (old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) y) :=
      (P.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
        ⟨⟨i, heOld⟩, hneOld⟩
    simpa [twoPackingUnionGraph] using Or.inl hredAdj
  · rcases (Qold.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1 hblue with
      ⟨⟨i, he⟩, hne⟩
    have heOld :
        s(old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x,
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) y) ∈
          (Q.path i.1).edgeSet := by
      simpa [Qold, strippedBlueOldPerfectPathPacking] using
        old_edge_mem_of_mem_strippedBlueOldPath_edgeSet
          (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) Q i
          (x := x) (y := y) he
    have hneOld :
        old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x ≠
          old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) y := by
      intro h
      exact hne
        (old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) h)
    have hblueAdj :
        Q.toPathPacking.spanningGraph.Adj
          (old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) x)
          (old (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) y) :=
      (Q.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
        ⟨⟨i.1, heOld⟩, hneOld⟩
    simpa [twoPackingUnionGraph] using Or.inr hblueAdj

/-- Stripping the normalized red routing and the old-blue part cannot create
more branch vertices than the original normalized red/blue union. -/
theorem strippedPair_branchVertexCount_le_augmented [Fintype V]
    {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ)))
    (Q : PerfectPathPacking
      (graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
      (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))
      (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := δ))) :
    branchVertexCount
        (twoPackingUnionGraph
          (strippedRedPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
          (strippedBlueOldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := δ) Q)) ≤
      branchVertexCount (twoPackingUnionGraph P Q) := by
  classical
  refine branchVertexCount_le_of_injective_adj
    (G :=
      twoPackingUnionGraph
        (strippedRedPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) P)
        (strippedBlueOldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) Q))
    (H := twoPackingUnionGraph P Q)
    (old (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)) ?hf ?hadj
  · exact old_injective (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ)
  · intro x y hxy
    exact strippedUnion_adj_old
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P Q hxy

/-- Any sparsifier for the normalized augmented instance projects to a
sparsifier for the original two-pair instance by stripping the fresh leaves
and discarding dummy blue paths. -/
theorem routingSparsifier_of_augmentedRoutingSparsifier [Fintype V]
    {G : _root_.SimpleGraph V} {k : ℕ}
    (h :
      TwoPairRoutingSparsifier
        (graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ) G)
        (S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ))
        (T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := δ)) k) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k := by
  classical
  rcases h with ⟨P, Q, hbranch⟩
  refine ⟨
    strippedRedPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P,
    strippedBlueOldPerfectPathPacking (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) Q,
    ?_⟩
  exact
    (strippedPair_branchVertexCount_le_augmented
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := δ) P Q).trans hbranch

end Theorem13AugVertex

/-- Public Theorem 1.3 reduced to the normalized augmented instance.

The proof adds fresh degree-one leaves and enough dummy blue terminals to make
both terminal pairs have size `k₁`, applies the normalized theorem, and then
strips the fresh vertices back out.  The degenerate `k₁ = 0` and `k₂ = 0`
cases use the already stronger empty-routing lemmas. -/
theorem theorem13_two_pair_routability_sparsifier_of_normalized_expansion
    [Fintype V] {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ k₂ : ℕ}
    (hS₁ : S₁.card = k₁) (hT₁ : T₁.card = k₁)
    (hS₂ : S₂.card = k₂) (hT₂ : T₂.card = k₂)
    (hk₂ : k₂ ≤ k₁)
    (hR₁ : RoutableIn G S₁ T₁)
    (hR₂ : RoutableIn G S₂ T₂)
    (hexpansion :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {H : _root_.SimpleGraph W}
        (M : TwoPairMinimalGoodMinor
          (Theorem13AugVertex.graph (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) G)
          H
          (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
          (Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
          (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
          (Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
            (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))),
          TwoPairControlledExpansion
            (W :=
              {w : W //
                w ∈ branchVertexFinset
                  (twoPackingUnionGraph
                    M.good.redRouting M.good.blueRouting)})
            (Theorem13AugVertex.graph (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) G)
            (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  classical
  by_cases hk₁zero : k₁ = 0
  · have hS₁zero : S₁.card = 0 := by
      simpa [hk₁zero] using hS₁
    have hT₁zero : T₁.card = 0 := by
      simpa [hk₁zero] using hT₁
    have hk₂le0 : k₂ ≤ 0 := by
      simpa [hk₁zero] using hk₂
    have hzero :
        TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ 0 :=
      theorem13_two_pair_routability_sparsifier_zero
        S₁ T₁ S₂ T₂ hS₁zero hT₁zero hS₂ hT₂ hk₂le0 hR₁ hR₂
    simpa [hk₁zero] using hzero
  by_cases hk₂zero : k₂ = 0
  · have hS₂zero : S₂.card = 0 := by
      simpa [hk₂zero] using hS₂
    have hT₂zero : T₂.card = 0 := by
      simpa [hk₂zero] using hT₂
    exact
      theorem13_two_pair_routability_sparsifier_blue_empty
        S₁ T₁ S₂ T₂ hS₁ hT₁ hS₂zero hT₂zero
        (Nat.zero_le k₁) hR₁ hR₂
  have hk₁pos : 0 < k₁ := Nat.pos_of_ne_zero hk₁zero
  have hS₁Aug :
      (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)).card = k₁ := by
    rw [Theorem13AugVertex.S₁Leaves_card, hS₁]
  have hS₂Aug :
      (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)).card = k₁ := by
    rw [Theorem13AugVertex.S₂Leaves_card, hS₂]
    omega
  have hR₁Aug :
      RoutableIn
        (Theorem13AugVertex.graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) G)
        (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)) :=
    Theorem13AugVertex.redAugmented_routable
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) hR₁
  have hR₂Aug :
      RoutableIn
        (Theorem13AugVertex.graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) G)
        (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)) :=
    Theorem13AugVertex.blueAugmented_routable
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) hR₂
  have hdegAug :
      ∀ x : Theorem13AugVertex V S₁ T₁ S₂ T₂ (k₁ - k₂),
        x ∈
          twoPairTerminalSet
            (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)) →
          DegreeEquals
            (Theorem13AugVertex.graph (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) G) x 1 := by
    intro x hx
    exact
      Theorem13AugVertex.terminal_degree_one
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)
        (G := G) hx
  have hdisjAug :
      TwoPairTerminalSetsDisjoint
        (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)) :=
    Theorem13AugVertex.terminalSetsDisjoint
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)
  have hAug :
      TwoPairRoutingSparsifier
        (Theorem13AugVertex.graph (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) G)
        (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)) k₁ :=
    theorem13_two_pair_routability_sparsifier_normalized_expansion
      (V := Theorem13AugVertex V S₁ T₁ S₂ T₂ (k₁ - k₂))
      (G := Theorem13AugVertex.graph (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) G)
      (S₁ := Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
      (T₁ := Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
      (S₂ := Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
      (T₂ := Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
      hS₁Aug hS₂Aug hk₁pos hR₁Aug hR₂Aug hexpansion hdegAug hdisjAug
  exact
    Theorem13AugVertex.routingSparsifier_of_augmentedRoutingSparsifier
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) hAug

/-- Theorem 1.3 of `treewidth-sparsifier.pdf`, without the algorithmic claim.

This is the closed Section 2 proof: first normalize by adding fresh
degree-one leaves and dummy blue terminals, then apply the internally proved
paper-routing expansion bound for a minimal good minor, and finally strip the
fresh vertices back to the original graph. -/
theorem theorem13_two_pair_routability_sparsifier
    [Fintype V]
    (G : _root_.SimpleGraph V)
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ k₂ : ℕ}
    (hS₁ : S₁.card = k₁)
    (hT₁ : T₁.card = k₁)
    (hS₂ : S₂.card = k₂)
    (hT₂ : T₂.card = k₂)
    (hk₂ : k₂ ≤ k₁)
    (hR₁ : RoutableIn G S₁ T₁)
    (hR₂ : RoutableIn G S₂ T₂) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  classical
  refine
    theorem13_two_pair_routability_sparsifier_of_normalized_expansion
      (G := G) S₁ T₁ S₂ T₂ hS₁ hT₁ hS₂ hT₂ hk₂ hR₁ hR₂ ?_
  intro W instW instDecW H M
  letI : Fintype W := instW
  letI : DecidableEq W := instDecW
  let hdegAug :
      ∀ x : Theorem13AugVertex V S₁ T₁ S₂ T₂ (k₁ - k₂),
        x ∈
          twoPairTerminalSet
            (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
            (Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)) →
          DegreeEquals
            (Theorem13AugVertex.graph (V := V) (S₁ := S₁) (T₁ := T₁)
              (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂) G) x 1 :=
    fun x hx =>
      Theorem13AugVertex.terminal_degree_one
        (V := V) (S₁ := S₁) (T₁ := T₁)
        (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)
        (G := G) hx
  let hdisjAug :
      TwoPairTerminalSetsDisjoint
        (Theorem13AugVertex.S₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.T₁Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.S₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂))
        (Theorem13AugVertex.T₂Leaves (V := V) (S₁ := S₁) (T₁ := T₁)
          (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)) :=
    Theorem13AugVertex.terminalSetsDisjoint
      (V := V) (S₁ := S₁) (T₁ := T₁)
      (S₂ := S₂) (T₂ := T₂) (δ := k₁ - k₂)
  exact
    M.controlledExpansionOfPaperRoutingMinorBranchVertices
      hdegAug hdisjAug
      (M.paperRoutingBranchSetLocalBound hdegAug hdisjAug)

/-- Theorem 1.3 from the Section 2 chain-label certificate for the chosen
routings.

This is the closed formal part after the paper's minimal-minor and chain
construction have supplied the two routings and their label certificate. -/
theorem theorem13_two_pair_routability_sparsifier_of_chainLabelCertificate
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (C : TwoPairChainLabelCertificate P Q k₁)
    (hS₁ : S₁.card = k₁) (hS₂ : S₂.card ≤ k₁) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  refine ⟨P, Q, ?_⟩
  have hPcard : P.card ≤ k₁ := by
    rw [P.card_eq_left_card, hS₁]
  have hQcard : Q.card ≤ k₁ := by
    rw [Q.card_eq_left_card]
    exact hS₂
  exact C.branchVertexCount_le_theorem13_bound hPcard hQcard

/-- Theorem 1.3's routing sparsifier conclusion from the split Section 2
ingredients. -/
theorem theorem13_two_pair_routability_sparsifier_of_labelings
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (L : TwoPairForwardLabeling P Q k₁)
    (Lrev : TwoPairReverseRedLabeling P Q k₁)
    (hS₁ : S₁.card = k₁) (hS₂ : S₂.card ≤ k₁) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  exact theorem13_two_pair_routability_sparsifier_of_chainLabelCertificate
    S₁ T₁ S₂ T₂ P Q
    (TwoPairChainLabelCertificate.ofLabelingsAndPackings L Lrev)
    hS₁ hS₂

/-- Theorem 1.3's routing sparsifier conclusion from the reachability-cover
form of the Section 2 proof. -/
theorem theorem13_two_pair_routability_sparsifier_of_reachCovers
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (Z : TwoPairForwardReachCover P Q k₁)
    (Zrev : TwoPairReverseRedReachCover P Q k₁)
    (hS₁ : S₁.card = k₁) (hS₂ : S₂.card ≤ k₁) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  exact theorem13_two_pair_routability_sparsifier_of_labelings
    S₁ T₁ S₂ T₂ P Q
    Z.toForwardLabeling Zrev.toReverseRedLabeling hS₁ hS₂

/-- Theorem 1.3's routing sparsifier conclusion from the chain-cover form of
the Section 2 proof. -/
theorem theorem13_two_pair_routability_sparsifier_of_chainCovers
    {G : _root_.SimpleGraph V}
    (S₁ T₁ S₂ T₂ : Finset V) {k₁ : ℕ}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (Z : TwoPairForwardChainCover P Q k₁)
    (Zrev : TwoPairReverseRedChainCover P Q k₁)
    (hS₁ : S₁.card = k₁) (hS₂ : S₂.card ≤ k₁) :
    TwoPairRoutingSparsifier G S₁ T₁ S₂ T₂ k₁ := by
  exact theorem13_two_pair_routability_sparsifier_of_labelings
    S₁ T₁ S₂ T₂ P Q
    Z.toForwardLabeling Zrev.toReverseRedLabeling hS₁ hS₂

end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
