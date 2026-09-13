import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.PseudoGridSlicingDefs

namespace Lax17Proofs

universe u v w

/-!
# Pseudo-grid slicing

This file starts the formalization of Section 4.2 of Chuzhoy--Tan.  It
contains the self-contained counting step that discards the row-bad `Q'`
segments and leaves a subfamily `Q''` intersecting every pseudo-grid row.

It also records the paper's next objects: the row linkage `R`, the retained
subpaths `Q''`, unique linkages, and `M`-slicings of a linkage.  These
definitions are intentionally stated in graph-theoretic terms, so later files
can formalize Observations 4.3--4.4 and Theorem 4.6 without changing the
Section 4.1 pseudo-grid interface.
-/

namespace SimpleGraph


namespace GraphPath

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- If all edges of a path have both endpoints in `U`, and the target endpoint
lies in `U`, then every vertex of the path lies in `U`.

This support-control lemma is useful for paths in graphs defined only by an
edge set: a length-zero path is handled by the target hypothesis, while every
other support vertex is incident with one of the path edges. -/
theorem vertexSet_subset_of_edgeSet_vertices
    (P : GraphPath G) (U : Finset V)
    (htarget : P.target ∈ U)
    (hedge : ∀ e, e ∈ P.edgeSet → ∀ v, v ∈ e → v ∈ U) :
    P.vertexSet ⊆ U := by
  intro v hv
  have hvSupport : v ∈ P.walk.support := by
    simpa [GraphPath.vertexSet] using hv
  rcases (_root_.SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mp hvSupport)
      with hvTarget | hEdge
  · simpa [hvTarget] using htarget
  · rcases hEdge with ⟨e, heWalk, hve⟩
    exact hedge e (by simpa [GraphPath.edgeSet] using heWalk) v hve

/-- Vertex-disjoint paths are edge-disjoint. -/
theorem edgeDisjoint_of_nodeDisjoint {P Q : GraphPath G}
    (h : P.NodeDisjoint Q) : P.EdgeDisjoint Q := by
  classical
  rw [GraphPath.EdgeDisjoint, Finset.disjoint_left]
  intro e heP heQ
  induction e using Sym2.ind with
  | h u v =>
      have hePwalk : s(u, v) ∈ P.walk.edges := by
        simpa [GraphPath.edgeSet] using heP
      have heQwalk : s(u, v) ∈ Q.walk.edges := by
        simpa [GraphPath.edgeSet] using heQ
      have huP : u ∈ P.vertexSet := by
        have huSupport : u ∈ P.walk.support :=
          P.walk.fst_mem_support_of_mem_edges hePwalk
        simpa [GraphPath.vertexSet] using huSupport
      have huQ : u ∈ Q.vertexSet := by
        have huSupport : u ∈ Q.walk.support :=
          Q.walk.fst_mem_support_of_mem_edges heQwalk
        simpa [GraphPath.vertexSet] using huSupport
      exact Finset.disjoint_left.mp h huP huQ

end GraphPath

namespace PathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- A node-disjoint path packing cannot use more paths than left terminals. -/
theorem card_le_left_card (P : PathPacking G S T) :
    P.card ≤ S.card := by
  simpa using Finset.card_le_card P.sourceSet_subset_left

/-- A node-disjoint path packing cannot use more paths than right terminals. -/
theorem card_le_right_card (P : PathPacking G S T) :
    P.card ≤ T.card := by
  simpa using Finset.card_le_card P.targetSet_subset_right

/-- Membership in a hit set is equivalently witnessed by a vertex of the path
lying in the finite set. -/
theorem mem_hitSet_iff_exists (P : PathPacking G S T) (U : Finset V)
    (i : P.Index) :
    i ∈ P.hitSet U ↔ ∃ v, v ∈ (P.path i).vertexSet ∧ v ∈ U := by
  classical
  rw [P.mem_hitSet U i, Finset.not_disjoint_iff]

/-- If `U ⊆ W`, every path hitting `U` also hits `W`. -/
theorem hitSet_subset_of_subset (P : PathPacking G S T) {U W : Finset V}
    (hUW : U ⊆ W) :
    P.hitSet U ⊆ P.hitSet W := by
  classical
  intro i hi
  rcases (P.mem_hitSet_iff_exists U i).1 hi with ⟨v, hvPath, hvU⟩
  exact (P.mem_hitSet_iff_exists W i).2 ⟨v, hvPath, hUW hvU⟩

/-- A node-disjoint path packing has at most `|U|` paths meeting `U`.

This is the counting estimate used in Section 4.2 when bounding the number of
auxiliary paths that hit a separator, the first endpoints, or the last
endpoints of the unique linkage. -/
theorem hitSet_card_le (P : PathPacking G S T) (U : Finset V) :
    (P.hitSet U).card ≤ U.card := by
  classical
  let witnessExists :
      ∀ i : P.hitSet U,
        ∃ v, v ∈ (P.path i.1).vertexSet ∧ v ∈ U := fun i =>
    Finset.not_disjoint_iff.1 ((P.mem_hitSet U i.1).1 i.2)
  let hitVertex : P.hitSet U → V := fun i =>
    Classical.choose (witnessExists i)
  have hitVertex_mem_path :
      ∀ i : P.hitSet U, hitVertex i ∈ (P.path i.1).vertexSet := by
    intro i
    exact (Classical.choose_spec (witnessExists i)).1
  have hitVertex_mem_U :
      ∀ i : P.hitSet U, hitVertex i ∈ U := by
    intro i
    exact (Classical.choose_spec (witnessExists i)).2
  let f : P.hitSet U → {v // v ∈ U} := fun i => ⟨hitVertex i, hitVertex_mem_U i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hindex
    have hv_eq : hitVertex i = hitVertex j := congrArg Subtype.val hij
    have hvj_on_i : hitVertex j ∈ (P.path i.1).vertexSet := by
      simpa [hv_eq] using hitVertex_mem_path i
    exact Finset.disjoint_left.mp (P.node_disjoint hindex)
      hvj_on_i (hitVertex_mem_path j)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_coe] using hcard

/-- Removing all paths that hit `U` leaves at least `P.card - U.card` paths. -/
theorem card_sdiff_hitSet_ge (P : PathPacking G S T) (U : Finset V) :
    P.card - U.card ≤
      ((Finset.univ : Finset P.Index) \ P.hitSet U).card := by
  classical
  have hsub : P.hitSet U ⊆ (Finset.univ : Finset P.Index) := by
    intro i _hi
    simp
  rw [Finset.card_sdiff_of_subset hsub]
  have hhit := P.hitSet_card_le U
  simp [PathPacking.card]
  omega

/-- Transfer a path packing to the graph obtained by deleting an edge that none
of its paths uses. -/
noncomputable def deleteEdgeOfNotMemEdgeSet
    (P : PathPacking G S T) (e : Sym2 V) (he : e ∉ P.edgeSet) :
    PathPacking (G.deleteEdges ({e} : Set (Sym2 V))) S T :=
  P.transfer (G.deleteEdges ({e} : Set (Sym2 V))) (by
    intro i e' he'
    rw [_root_.SimpleGraph.edgeSet_deleteEdges]
    constructor
    · exact (P.path i).walk.edges_subset_edgeSet he'
    · intro heSingleton
      have heq : e' = e := by
        simpa using heSingleton
      apply he
      rw [← heq]
      exact (P.mem_edgeSet).2
        ⟨i, by simpa [GraphPath.edgeSet] using he'⟩)

@[simp] theorem deleteEdgeOfNotMemEdgeSet_card
    (P : PathPacking G S T) (e : Sym2 V) (he : e ∉ P.edgeSet) :
    (P.deleteEdgeOfNotMemEdgeSet e he).card = P.card :=
  rfl

/-- A vertex incident with an edge of a packing's spanning graph belongs to
the vertex set of the packing. -/
theorem mem_vertexSet_of_mem_spanningGraph_edge
    (P : PathPacking G S T) {e : Sym2 V}
    (he : e ∈ P.spanningGraph.edgeSet) {v : V} (hv : v ∈ e) :
    v ∈ P.vertexSet := by
  classical
  have he' :
      e ∈ (↑P.edgeSet : Set (Sym2 V)) \ Sym2.diagSet := by
    simpa [PathPacking.spanningGraph] using he
  have heP : e ∈ P.edgeSet := by
    simpa using he'.1
  rcases (P.mem_edgeSet).1 heP with ⟨i, hei⟩
  have heWalk : e ∈ (P.path i).walk.edges := by
    simpa [GraphPath.edgeSet] using hei
  have hvPath : v ∈ (P.path i).vertexSet := by
    have hvSupport : v ∈ (P.path i).walk.support :=
      (P.path i).walk.mem_support_of_mem_edges heWalk hv
    simpa [GraphPath.vertexSet] using hvSupport
  exact P.path_vertexSet_subset_vertexSet i hvPath

/-- Symmetric form of
`mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet`. -/
theorem mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet_right
    (P : PathPacking G S T) {r : P.Index} {u v : V}
    (hv : v ∈ (P.path r).vertexSet) (huv : P.spanningGraph.Adj u v) :
    u ∈ (P.path r).vertexSet := by
  exact P.mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet hv huv.symm

/-- A vertex incident with an edge of the union of two packing-spanning graphs
belongs to one of the two packing vertex sets. -/
theorem mem_vertexSet_union_of_mem_sup_spanningGraph_edge
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PathPacking G S₁ T₁) (P₂ : PathPacking G S₂ T₂)
    {e : Sym2 V}
    (he : e ∈ (P₁.spanningGraph ⊔ P₂.spanningGraph).edgeSet)
    {v : V} (hv : v ∈ e) :
    v ∈ P₁.vertexSet ∪ P₂.vertexSet := by
  classical
  rw [_root_.SimpleGraph.edgeSet_sup] at he
  rcases he with he₁ | he₂
  · exact Finset.mem_union_left _ (P₁.mem_vertexSet_of_mem_spanningGraph_edge he₁ hv)
  · exact Finset.mem_union_right _ (P₂.mem_vertexSet_of_mem_spanningGraph_edge he₂ hv)

end PathPacking

namespace PathSlicing

variable {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B S T : Finset V}

namespace LinkageOrdering

variable {R : PerfectPathPacking G A B}

/-- The selected row vertex belongs to the finite separator set `S_t`. -/
theorem separatorVertex_mem_separatorSet
    (theta : LinkageOrdering R) (t : ℕ) (r : R.Index) :
    theta.separatorVertex t r ∈ theta.separatorSet t := by
  classical
  rw [theta.separatorSet_eq t]
  exact Finset.mem_image.2 ⟨r, by simp, rfl⟩

/-- The set of vertices with exactly rank `t` in a Robertson--Seymour
ordering. -/
noncomputable def rankLevel (theta : LinkageOrdering R) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v : V => theta.rank v = t

@[simp] theorem mem_rankLevel
    (theta : LinkageOrdering R) (t : ℕ) (v : V) :
    v ∈ theta.rankLevel t ↔ theta.rank v = t := by
  classical
  simp [rankLevel]

/-- Since the ranking is injective, every rank level contains at most one
vertex. -/
theorem rankLevel_card_le_one (theta : LinkageOrdering R) (t : ℕ) :
    (theta.rankLevel t).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haRank : theta.rank a = t := (theta.mem_rankLevel t a).1 ha
  have hbRank : theta.rank b = t := (theta.mem_rankLevel t b).1 hb
  exact theta.rank_injective (haRank.trans hbRank.symm)

end LinkageOrdering

omit [Fintype V] in
/-- Appendix B, Observation B.1.  If `x` appears strictly before `y` on a row
and the dependency digraph has an edge `y -> z`, then it also has the edge
`x -> z`. -/
theorem linkageDependency_of_before_of_linkageDependency
    {R : PerfectPathPacking G A B} {x y z : V} {r : R.Index}
    (hxy : (R.path r).Before x y) (hxy_ne : x ≠ y)
    (hyz : LinkageDependency R y z) :
    LinkageDependency R x z := by
  classical
  have hxyData := ((R.path r).before_iff_vertexIndex_le).1 hxy
  have hx : x ∈ (R.path r).vertexSet := hxyData.1
  have hy : y ∈ (R.path r).vertexSet := hxyData.2.1
  rcases hyz with hyzType1 | hyzType2
  · rcases hyzType1 with ⟨r', hyr', hzr', hyzBefore, hyz_ne⟩
    have hrr' : r' = r := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
        hyr' hy
    subst r'
    refine Or.inl ⟨r, hx, hzr', (R.path r).before_trans hxy hyzBefore, ?_⟩
    intro hxz
    have hyx : (R.path r).Before y x := by
      simpa [hxz] using hyzBefore
    exact hxy_ne ((R.path r).before_antisymm hxy hyx)
  · rcases hyzType2 with
      ⟨r', r'', hr_ne, hyr', hzr'', w, hwr', hywBefore, hyw_ne, hwz⟩
    have hrr' : r' = r := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
        hyr' hy
    subst r'
    refine Or.inr
      ⟨r, r'', hr_ne, hx, hzr'', w, hwr',
        (R.path r).before_trans hxy hywBefore, ?_, hwz⟩
    intro hxw
    have hwy : (R.path r).Before w y := by
      simpa [hxw] using hxy
    exact hyw_ne ((R.path r).before_antisymm hywBefore hwy)

/-- The sorted list used to turn an injective ordered key on a finite type into
a zero-based ranking. -/
noncomputable def sortedByKey {α β : Type*} [Fintype α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) : List α := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  exact (Finset.univ : Finset α).sort (· ≤ ·)

/-- The zero-based rank of an element in the finite list sorted by `key`. -/
noncomputable def rankByKey {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) (hkey : Function.Injective key) (a : α) : ℕ :=
  (sortedByKey key hkey).idxOf a

theorem mem_sortedByKey {α β : Type*} [Fintype α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) (a : α) :
    a ∈ sortedByKey key hkey := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  simp [sortedByKey]

theorem sortedByKey_nodup {α β : Type*} [Fintype α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) :
    (sortedByKey key hkey).Nodup := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  simp [sortedByKey]

theorem sortedByKey_length {α β : Type*} [Fintype α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) :
    (sortedByKey key hkey).length = Fintype.card α := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  simp [sortedByKey]

theorem rankByKey_lt_card {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) (hkey : Function.Injective key) (a : α) :
    rankByKey key hkey a < Fintype.card α := by
  classical
  have hmem : a ∈ sortedByKey key hkey := mem_sortedByKey key hkey a
  simpa [rankByKey, sortedByKey_length key hkey] using
    (List.idxOf_lt_length_iff.2 hmem)

theorem rankByKey_injective {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) (hkey : Function.Injective key) :
    Function.Injective (rankByKey key hkey) := by
  classical
  intro a b h
  have ha : a ∈ sortedByKey key hkey := mem_sortedByKey key hkey a
  exact (List.idxOf_inj ha).1 (by simpa [rankByKey] using h)

theorem key_le_of_rankByKey_le {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) {a b : α}
    (hkey : Function.Injective key)
    (h : rankByKey key hkey a ≤ rankByKey key hkey b) :
    key a ≤ key b := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  let l := sortedByKey key hkey
  have haMem : a ∈ l := by simpa [l] using mem_sortedByKey key hkey a
  have hbMem : b ∈ l := by simpa [l] using mem_sortedByKey key hkey b
  have haLt : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 haMem
  have hbLt : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hbMem
  let ia : Fin l.length := ⟨l.idxOf a, haLt⟩
  let ib : Fin l.length := ⟨l.idxOf b, hbLt⟩
  have hPair : l.Pairwise (fun x y : α => x ≤ y) := by
    change ((Finset.univ : Finset α).sort (· ≤ ·)).Pairwise
      (fun x y : α => x ≤ y)
    exact Finset.pairwise_sort (s := (Finset.univ : Finset α))
      (r := (· ≤ ·))
  have hiaib : ia ≤ ib := by
    exact h
  have hleAlpha : l.get ia ≤ l.get ib :=
    hPair.rel_get_of_le hiaib
  have hle : key (l.get ia) ≤ key (l.get ib) := by
    exact hleAlpha
  have hgeta : l.get ia = a := by
    exact List.idxOf_get (a := a) (l := l) haLt
  have hgetb : l.get ib = b := by
    exact List.idxOf_get (a := b) (l := l) hbLt
  calc
    key a = key (l.get ia) := by rw [hgeta]
    _ ≤ key (l.get ib) := hle
    _ = key b := by rw [hgetb]

theorem rankByKey_lt_of_key_lt {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) (hkey : Function.Injective key)
    {a b : α} (hltKey : key a < key b) :
    rankByKey key hkey a < rankByKey key hkey b := by
  classical
  by_contra hnot
  have hleRank : rankByKey key hkey b ≤ rankByKey key hkey a :=
    Nat.le_of_not_gt hnot
  have hleKey : key b ≤ key a := key_le_of_rankByKey_le key hkey hleRank
  exact (not_le_of_gt hltKey) hleKey

namespace ThresholdSequence

variable {R : PerfectPathPacking G A B} {M : ℕ}

/-- A monotone sequence of thresholds gives the corresponding concrete
`M`-slicing by taking, on every row, the separator vertex for each threshold.
-/
noncomputable def toPathSlicing
    (theta : LinkageOrdering R) (tau : ThresholdSequence R theta M) :
    PathSlicing R M where
  cut := fun r i => theta.separatorVertex (tau.threshold i) r
  cut_mem := fun r i => theta.separatorVertex_mem (tau.threshold i) r
  cut_zero := by
    intro r
    rw [tau.threshold_zero, theta.separatorVertex_zero]
  cut_last := by
    intro r
    rw [tau.threshold_last, theta.separatorVertex_card]
  cut_monotone := by
    intro r s t hst
    exact theta.separatorVertex_monotone r (tau.threshold_monotone hst)

@[simp] theorem toPathSlicing_cut
    (theta : LinkageOrdering R) (tau : ThresholdSequence R theta M)
    (r : R.Index) (i : Fin (M + 1)) :
    (tau.toPathSlicing theta).cut r i =
      theta.separatorVertex (tau.threshold i) r := rfl

/-- The two-slice threshold sequence `(0,t,|V|)`. -/
noncomputable def two
    (theta : LinkageOrdering R) (t : ℕ) (ht : t ≤ Fintype.card V) :
    ThresholdSequence R theta 2 where
  threshold := fun i =>
    if i.val = 0 then 0 else if i.val = 1 then t else Fintype.card V
  threshold_zero := by
    simp
  threshold_last := by
    simp
  threshold_monotone := by
    intro s u hsu
    have hsleu : s.val ≤ u.val := hsu
    have hslt : s.val < 3 := s.isLt
    have hult : u.val < 3 := u.isLt
    by_cases hs0 : s.val = 0
    · simp [hs0]
    · by_cases hs1 : s.val = 1
      · have hu_ne0 : u.val ≠ 0 := by omega
        by_cases hu1 : u.val = 1
        · simp [hs1, hu1]
        · have hu2 : u.val = 2 := by omega
          simp [hs1, hu2, ht]
      · have hs2 : s.val = 2 := by omega
        have hu2 : u.val = 2 := by omega
        simp [hs2, hu2]

@[simp] theorem two_threshold_zero
    (theta : LinkageOrdering R) (t : ℕ) (ht : t ≤ Fintype.card V) :
    (two theta t ht).threshold 0 = 0 := by
  simp [two]

@[simp] theorem two_threshold_one
    (theta : LinkageOrdering R) (t : ℕ) (ht : t ≤ Fintype.card V) :
    (two theta t ht).threshold 1 = t := by
  simp [two]

@[simp] theorem two_threshold_last
    (theta : LinkageOrdering R) (t : ℕ) (ht : t ≤ Fintype.card V) :
    (two theta t ht).threshold (Fin.last 2) = Fintype.card V := by
  simp [two]

end ThresholdSequence

/-- If the cardinalities of a finite sequence of finite sets start at zero,
end above `target`, and grow by at most one at each step, then one of them has
cardinality exactly `target`.

This is the finite intermediate-value step used in the slicing algorithm after
Observation 4.7. -/
theorem exists_index_card_eq_of_step_le_one {α : Type u}
    (F : ℕ → Finset α) {n target : ℕ}
    (h0 : (F 0).card = 0)
    (hend : target ≤ (F n).card)
    (hstep : ∀ i, i < n → (F (i + 1)).card ≤ (F i).card + 1) :
    ∃ i ≤ n, (F i).card = target := by
  classical
  let Good : ℕ → Prop := fun i => i ≤ n ∧ target ≤ (F i).card
  have hex : ∃ i : ℕ, Good i := ⟨n, le_rfl, hend⟩
  let i := Nat.find hex
  have hi : Good i := Nat.find_spec hex
  by_cases hzero : i = 0
  · have hle0 : target ≤ 0 := by
      have hi2 : target ≤ (F 0).card := by
        simpa [i, hzero] using hi.2
      simpa [h0] using hi2
    have htarget_zero : target = 0 := Nat.eq_zero_of_le_zero hle0
    exact ⟨0, Nat.zero_le n, by simp [h0, htarget_zero]⟩
  · have hipos : 0 < i := Nat.pos_of_ne_zero hzero
    let j := i - 1
    have hsucc : j + 1 = i := by
      simpa [j] using (Nat.succ_pred_eq_of_pos hipos)
    have hjlt : j < i := by omega
    have hjnot : ¬ Good j := Nat.find_min hex hjlt
    have hjle : j ≤ n := le_trans (Nat.pred_le i) hi.1
    have hjcard_lt : (F j).card < target := by
      have hnot : ¬ target ≤ (F j).card := by
        intro hle
        exact hjnot ⟨hjle, hle⟩
      exact Nat.lt_of_not_ge hnot
    have hstepj : (F i).card ≤ (F j).card + 1 := by
      have hjlt_n : j < n := by omega
      simpa [hsucc] using hstep j hjlt_n
    have hle_target : (F i).card ≤ target := by omega
    exact ⟨i, hi.1, le_antisymm hle_target hi.2⟩

/-- Any auxiliary path crossing a Robertson--Seymour threshold must hit the
corresponding threshold separator. -/
theorem pathsCrossingThreshold_subset_hitSet_separator
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) :
    pathsCrossingThreshold theta.rank Qpack t ⊆
      Qpack.hitSet (theta.separatorSet t) := by
  classical
  intro q hq
  have hcross :
      GraphPathCrossesRankThreshold theta.rank t (Qpack.path q) :=
    (mem_pathsCrossingThreshold theta.rank Qpack t q).1 hq
  rcases theta.separator_blocks t (Qpack.path q) hcross with
    ⟨v, hvPath, hvSep⟩
  exact (Qpack.mem_hitSet (theta.separatorSet t) q).2
    (Finset.not_disjoint_iff.2 ⟨v, hvPath, hvSep⟩)

/-- Counting consequence of Lemma 4.5: at most `|R|` node-disjoint auxiliary
paths cross any fixed threshold. -/
theorem pathsCrossingThreshold_card_le
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) :
    (pathsCrossingThreshold theta.rank Qpack t).card ≤ R.card := by
  classical
  calc
    (pathsCrossingThreshold theta.rank Qpack t).card
        ≤ (Qpack.hitSet (theta.separatorSet t)).card :=
          Finset.card_le_card
            (pathsCrossingThreshold_subset_hitSet_separator theta Qpack t)
    _ ≤ (theta.separatorSet t).card := Qpack.hitSet_card_le (theta.separatorSet t)
    _ ≤ R.card := theta.separator_card_le t

/-- The paper's estimate `|Q0(S_t)| ≤ |R|`: at most one node-disjoint
auxiliary path can be charged to each separator vertex. -/
theorem qZero_card_le
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) :
    (theta.qZero Qpack t).card ≤ R.card := by
  classical
  calc
    (theta.qZero Qpack t).card
        = (Qpack.hitSet (theta.separatorSet t)).card := rfl
    _ ≤ (theta.separatorSet t).card :=
        Qpack.hitSet_card_le (theta.separatorSet t)
    _ ≤ R.card := theta.separator_card_le t

/-- No path can hit the lower side of threshold `0`; this is
`Q1(S_0) = ∅` from Observation 4.7. -/
theorem qOne_zero_eq_empty
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) :
    theta.qOne Qpack 0 = ∅ := by
  classical
  ext q
  simp [LinkageOrdering.qOne, LinkageOrdering.belowSet,
    PathPacking.hitSet]

@[simp] theorem qOne_zero_card
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) :
    (theta.qOne Qpack 0).card = 0 := by
  rw [qOne_zero_eq_empty theta Qpack]
  simp

/-- Every auxiliary path hits the lower side of the final threshold
`|V|`. -/
theorem hitSet_belowSet_card_eq_univ
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) :
    Qpack.hitSet (theta.belowSet (Fintype.card V)) =
      (Finset.univ : Finset Qpack.Index) := by
  classical
  ext q
  constructor
  · intro _hq
    simp
  · intro _hq
    apply (Qpack.mem_hitSet_iff_exists
      (theta.belowSet (Fintype.card V)) q).2
    exact ⟨(Qpack.path q).source, GraphPath.source_mem_vertexSet (Qpack.path q),
      by
        simp [LinkageOrdering.belowSet, theta.rank_lt_card (Qpack.path q).source]⟩

/-- At the final threshold, `Q1` contains all paths except those that hit the
final separator, so it contains all but at most `|R|` paths. -/
theorem qOne_card_final_lower_bound
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) :
    Qpack.card - R.card ≤
      (theta.qOne Qpack (Fintype.card V)).card := by
  classical
  have hqOne_eq :
      theta.qOne Qpack (Fintype.card V) =
        (Finset.univ : Finset Qpack.Index) \
          theta.qZero Qpack (Fintype.card V) := by
    simp [LinkageOrdering.qOne, hitSet_belowSet_card_eq_univ theta Qpack]
  rw [hqOne_eq]
  have hsdiff :
      (Finset.univ : Finset Qpack.Index).card -
          (theta.qZero Qpack (Fintype.card V)).card ≤
        ((Finset.univ : Finset Qpack.Index) \
          theta.qZero Qpack (Fintype.card V)).card :=
    Finset.le_card_sdiff
      (theta.qZero Qpack (Fintype.card V))
      (Finset.univ : Finset Qpack.Index)
  have hq0 := qZero_card_le theta Qpack (Fintype.card V)
  have huniv : (Finset.univ : Finset Qpack.Index).card = Qpack.card := by
    simp [PathPacking.card]
  omega

theorem mem_qOne_iff
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) (q : Qpack.Index) :
    q ∈ theta.qOne Qpack t ↔
      q ∈ Qpack.hitSet (theta.belowSet t) ∧
        q ∉ theta.qZero Qpack t := by
  classical
  simp [LinkageOrdering.qOne]

theorem mem_qTwo_iff
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) (q : Qpack.Index) :
    q ∈ theta.qTwo Qpack t ↔
      q ∈ Qpack.hitSet (theta.aboveSet t) ∧
        q ∉ theta.qZero Qpack t := by
  classical
  simp [LinkageOrdering.qTwo]

theorem disjoint_qOne_qZero
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) :
    Disjoint (theta.qOne Qpack t) (theta.qZero Qpack t) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqOne hqZero
  exact ((mem_qOne_iff theta Qpack t q).1 hqOne).2 hqZero

theorem disjoint_qTwo_qZero
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) :
    Disjoint (theta.qTwo Qpack t) (theta.qZero Qpack t) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqTwo hqZero
  exact ((mem_qTwo_iff theta Qpack t q).1 hqTwo).2 hqZero

/-- A path disjoint from the threshold separator cannot hit both sides of the
threshold.  This is the formal `Q1(S_t) ∩ Q2(S_t) = ∅` argument in the proof
of Theorem 4.6. -/
theorem disjoint_qOne_qTwo
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) :
    Disjoint (theta.qOne Qpack t) (theta.qTwo Qpack t) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqOne hqTwo
  have hbelow_hit : q ∈ Qpack.hitSet (theta.belowSet t) :=
    ((mem_qOne_iff theta Qpack t q).1 hqOne).1
  have habove_hit : q ∈ Qpack.hitSet (theta.aboveSet t) :=
    ((mem_qTwo_iff theta Qpack t q).1 hqTwo).1
  have hnotZero : q ∉ theta.qZero Qpack t :=
    ((mem_qOne_iff theta Qpack t q).1 hqOne).2
  rcases (Qpack.mem_hitSet_iff_exists (theta.belowSet t) q).1 hbelow_hit with
    ⟨y, hyPath, hyBelow⟩
  rcases (Qpack.mem_hitSet_iff_exists (theta.aboveSet t) q).1 habove_hit with
    ⟨z, hzPath, hzAbove⟩
  have hyRank : theta.rank y < t := by
    simpa [LinkageOrdering.belowSet] using hyBelow
  have hzRank : t ≤ theta.rank z := by
    simpa [LinkageOrdering.aboveSet] using hzAbove
  have hcross :
      GraphPathCrossesRankThreshold theta.rank t (Qpack.path q) :=
    ⟨y, hyPath, z, hzPath, hyRank, hzRank⟩
  rcases theta.separator_blocks t (Qpack.path q) hcross with
    ⟨v, hvPath, hvSep⟩
  exact hnotZero ((Qpack.mem_hitSet_iff_exists (theta.separatorSet t) q).2
    ⟨v, hvPath, hvSep⟩)

/-- A `Q1(S_t)` path is disjoint from the upper side `Z_t`. -/
theorem qOne_path_disjoint_aboveSet
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) {q : Qpack.Index}
    (hq : q ∈ theta.qOne Qpack t) :
    Disjoint (Qpack.path q).vertexSet (theta.aboveSet t) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvPath hvAbove
  have hhit : q ∈ Qpack.hitSet (theta.aboveSet t) :=
    (Qpack.mem_hitSet_iff_exists (theta.aboveSet t) q).2
      ⟨v, hvPath, hvAbove⟩
  have hnotZero : q ∉ theta.qZero Qpack t :=
    ((mem_qOne_iff theta Qpack t q).1 hq).2
  have hqTwo : q ∈ theta.qTwo Qpack t :=
    (mem_qTwo_iff theta Qpack t q).2 ⟨hhit, hnotZero⟩
  exact Finset.disjoint_left.mp (disjoint_qOne_qTwo theta Qpack t) hq hqTwo

/-- Observation 4.7 monotonicity: the families `Q1(S_t)` are monotone in the
threshold. -/
theorem qOne_mono
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {s t : ℕ} (hst : s ≤ t) :
    theta.qOne Qpack s ⊆ theta.qOne Qpack t := by
  classical
  intro q hq
  have hqData := (mem_qOne_iff theta Qpack s q).1 hq
  have hhit_t : q ∈ Qpack.hitSet (theta.belowSet t) := by
    apply Qpack.hitSet_subset_of_subset (U := theta.belowSet s)
      (W := theta.belowSet t) ?_ hqData.1
    intro v hv
    have hvRank : theta.rank v < s := by
      simpa [LinkageOrdering.belowSet] using hv
    have : theta.rank v < t := by omega
    simpa [LinkageOrdering.belowSet] using this
  have hnot_t : q ∉ theta.qZero Qpack t := by
    intro hqt
    rcases (Qpack.mem_hitSet_iff_exists (theta.separatorSet t) q).1 hqt with
      ⟨v, hvQ, hvSepT⟩
    have hvUnion :=
      theta.separatorSet_subset_separator_union_above hst hvSepT
    rcases Finset.mem_union.1 hvUnion with hvSepS | hvAboveS
    · exact hqData.2
        ((Qpack.mem_hitSet_iff_exists (theta.separatorSet s) q).2
          ⟨v, hvQ, hvSepS⟩)
    · exact Finset.disjoint_left.mp
        (qOne_path_disjoint_aboveSet theta Qpack s hq)
        hvQ (by simpa [LinkageOrdering.aboveSet] using hvAboveS)
  exact (mem_qOne_iff theta Qpack t q).2 ⟨hhit_t, hnot_t⟩

/-- The new paths that enter `Q1` when the threshold advances from `t` to
`t + 1` must hit the unique possible rank-`t` vertex.  This is the formal
content of the type-1/type-2 discussion in Observation 4.7. -/
theorem qOne_succ_sdiff_subset_hitSet_rankLevel
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {t : ℕ} (ht : t < Fintype.card V) :
    theta.qOne Qpack (t + 1) \ theta.qOne Qpack t ⊆
      Qpack.hitSet (theta.rankLevel t) := by
  classical
  intro q hqnew
  rcases Finset.mem_sdiff.1 hqnew with ⟨hqSucc, hnotOld⟩
  have hsuccData := (mem_qOne_iff theta Qpack (t + 1) q).1 hqSucc
  by_cases hhitBelowT : q ∈ Qpack.hitSet (theta.belowSet t)
  · have hqZeroT : q ∈ theta.qZero Qpack t := by
      by_contra hnotZeroT
      exact hnotOld ((mem_qOne_iff theta Qpack t q).2
        ⟨hhitBelowT, hnotZeroT⟩)
    rcases (Qpack.mem_hitSet_iff_exists (theta.separatorSet t) q).1
        hqZeroT with ⟨v, hvQ, hvSepT⟩
    have hvNotSepSucc : v ∉ theta.separatorSet (t + 1) := by
      intro hvSepSucc
      exact hsuccData.2
        ((Qpack.mem_hitSet_iff_exists (theta.separatorSet (t + 1)) q).2
          ⟨v, hvQ, hvSepSucc⟩)
    have hvDiff : v ∈ theta.separatorSet t \ theta.separatorSet (t + 1) :=
      Finset.mem_sdiff.2 ⟨hvSepT, hvNotSepSucc⟩
    have hvRankLevel :
        v ∈ theta.rankLevel t := by
      simpa [LinkageOrdering.rankLevel] using
        theta.separatorSet_sdiff_succ_subset_rankLevel ht hvDiff
    exact (Qpack.mem_hitSet_iff_exists (theta.rankLevel t) q).2
      ⟨v, hvQ, hvRankLevel⟩
  · rcases (Qpack.mem_hitSet_iff_exists (theta.belowSet (t + 1)) q).1
        hsuccData.1 with ⟨v, hvQ, hvBelowSucc⟩
    have hvLtSucc : theta.rank v < t + 1 := by
      simpa [LinkageOrdering.belowSet] using hvBelowSucc
    have hvNotLtT : ¬ theta.rank v < t := by
      intro hvLtT
      exact hhitBelowT
        ((Qpack.mem_hitSet_iff_exists (theta.belowSet t) q).2
          ⟨v, hvQ, by simpa [LinkageOrdering.belowSet] using hvLtT⟩)
    have hvRank : theta.rank v = t := by omega
    exact (Qpack.mem_hitSet_iff_exists (theta.rankLevel t) q).2
      ⟨v, hvQ, by simpa [PathSlicing.LinkageOrdering.rankLevel] using hvRank⟩

/-- Observation 4.7 one-step growth: `Q1(S_t)` gains at most one path when
the threshold advances by one. -/
theorem qOne_succ_card_le
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {t : ℕ} (ht : t < Fintype.card V) :
    (theta.qOne Qpack (t + 1)).card ≤
      (theta.qOne Qpack t).card + 1 := by
  classical
  let A : Finset Qpack.Index := theta.qOne Qpack t
  let B : Finset Qpack.Index := theta.qOne Qpack (t + 1)
  have hAB : A ⊆ B := qOne_mono theta Qpack (Nat.le_succ t)
  have hdiff_le_one : (B \ A).card ≤ 1 := by
    calc
      (B \ A).card
          ≤ (Qpack.hitSet (theta.rankLevel t)).card :=
            Finset.card_le_card
              (by
                intro q hq
                exact qOne_succ_sdiff_subset_hitSet_rankLevel
                  theta Qpack ht (by simpa [A, B] using hq))
      _ ≤ (theta.rankLevel t).card := Qpack.hitSet_card_le (theta.rankLevel t)
      _ ≤ 1 := theta.rankLevel_card_le_one t
  have hcard : (B \ A).card + A.card = B.card :=
    Finset.card_sdiff_add_card_eq_card hAB
  calc
    B.card = (B \ A).card + A.card := hcard.symm
    _ ≤ 1 + A.card := Nat.add_le_add_right hdiff_le_one A.card
    _ = A.card + 1 := by omega

/-- Every vertex of a `Q1(S_t)` path has rank below `t`. -/
theorem rank_lt_of_qOne_path_mem
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) {q : Qpack.Index}
    (hq : q ∈ theta.qOne Qpack t) {v : V}
    (hv : v ∈ (Qpack.path q).vertexSet) :
    theta.rank v < t := by
  classical
  by_contra hnot
  have hvAbove : v ∈ theta.aboveSet t := by
    simp [LinkageOrdering.aboveSet, le_of_not_gt hnot]
  exact Finset.disjoint_left.mp
    (qOne_path_disjoint_aboveSet theta Qpack t hq) hv hvAbove

/-- A `Q2(S_t)` path is disjoint from the lower side `Y_t`. -/
theorem qTwo_path_disjoint_belowSet
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) {q : Qpack.Index}
    (hq : q ∈ theta.qTwo Qpack t) :
    Disjoint (Qpack.path q).vertexSet (theta.belowSet t) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvPath hvBelow
  have hhit : q ∈ Qpack.hitSet (theta.belowSet t) :=
    (Qpack.mem_hitSet_iff_exists (theta.belowSet t) q).2
      ⟨v, hvPath, hvBelow⟩
  have hnotZero : q ∉ theta.qZero Qpack t :=
    ((mem_qTwo_iff theta Qpack t q).1 hq).2
  have hqOne : q ∈ theta.qOne Qpack t :=
    (mem_qOne_iff theta Qpack t q).2 ⟨hhit, hnotZero⟩
  exact Finset.disjoint_left.mp (disjoint_qOne_qTwo theta Qpack t).symm hq hqOne

/-- Every vertex of a `Q2(S_t)` path has rank at least `t`. -/
theorem le_rank_of_qTwo_path_mem
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) {q : Qpack.Index}
    (hq : q ∈ theta.qTwo Qpack t) {v : V}
    (hv : v ∈ (Qpack.path q).vertexSet) :
    t ≤ theta.rank v := by
  classical
  by_contra hnot
  have hvBelow : v ∈ theta.belowSet t := by
    simp [LinkageOrdering.belowSet, Nat.lt_of_not_ge hnot]
  exact Finset.disjoint_left.mp
    (qTwo_path_disjoint_belowSet theta Qpack t hq) hv hvBelow

/-- A row-linkage intersection of a `Q1(S_t)` path lies before the selected
threshold vertex on that row. -/
theorem qOne_intersection_before_separator
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) {q : Qpack.Index}
    (hq : q ∈ theta.qOne Qpack t) {r : R.Index} {v : V}
    (hvQ : v ∈ (Qpack.path q).vertexSet)
    (hvR : v ∈ (R.path r).vertexSet) :
    (R.path r).Before v (theta.separatorVertex t r) :=
  theta.below_before_separator t r hvR
    (rank_lt_of_qOne_path_mem theta Qpack t hq hvQ)

/-- A row-linkage intersection of a `Q2(S_t)` path lies after the selected
threshold vertex on that row. -/
theorem separator_before_qTwo_intersection
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) {q : Qpack.Index}
    (hq : q ∈ theta.qTwo Qpack t) {r : R.Index} {v : V}
    (hvQ : v ∈ (Qpack.path q).vertexSet)
    (hvR : v ∈ (R.path r).vertexSet) :
    (R.path r).Before (theta.separatorVertex t r) v :=
  theta.separator_before_above t r hvR
    (le_rank_of_qTwo_path_mem theta Qpack t hq hvQ)

/-- A `Q1(S_t)` path cannot contain the selected threshold vertex of any row. -/
theorem qOne_ne_separatorVertex_of_mem
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) {q : Qpack.Index}
    (hq : q ∈ theta.qOne Qpack t) {r : R.Index} {v : V}
    (hvQ : v ∈ (Qpack.path q).vertexSet) :
    v ≠ theta.separatorVertex t r := by
  intro hv
  have hnotZero : q ∉ theta.qZero Qpack t :=
    ((mem_qOne_iff theta Qpack t q).1 hq).2
  exact hnotZero ((Qpack.mem_hitSet_iff_exists (theta.separatorSet t) q).2
    ⟨v, hvQ, by
      rw [hv]
      exact theta.separatorVertex_mem_separatorSet t r⟩)

/-- A `Q2(S_t)` path cannot contain the selected threshold vertex of any row. -/
theorem qTwo_ne_separatorVertex_of_mem
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) {q : Qpack.Index}
    (hq : q ∈ theta.qTwo Qpack t) {r : R.Index} {v : V}
    (hvQ : v ∈ (Qpack.path q).vertexSet) :
    v ≠ theta.separatorVertex t r := by
  intro hv
  have hnotZero : q ∉ theta.qZero Qpack t :=
    ((mem_qTwo_iff theta Qpack t q).1 hq).2
  exact hnotZero ((Qpack.mem_hitSet_iff_exists (theta.separatorSet t) q).2
    ⟨v, hvQ, by
      rw [hv]
      exact theta.separatorVertex_mem_separatorSet t r⟩)

/-- Any auxiliary path avoiding the first threshold separator belongs to
`Q2(S_0)`: every vertex has rank at least zero, and every graph path has at
least one vertex. -/
theorem mem_qTwo_zero_of_not_mem_qZero_zero
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {q : Qpack.Index}
    (hnot : q ∉ theta.qZero Qpack 0) :
    q ∈ theta.qTwo Qpack 0 := by
  classical
  apply (mem_qTwo_iff theta Qpack 0 q).2
  constructor
  · apply (Qpack.mem_hitSet_iff_exists (theta.aboveSet 0) q).2
    exact ⟨(Qpack.path q).source, GraphPath.source_mem_vertexSet (Qpack.path q),
      by simp [LinkageOrdering.aboveSet]⟩
  · exact hnot

/-- Any auxiliary path avoiding the final threshold separator belongs to
`Q1(S_|V|)`: all ranks are strictly below `|V|`. -/
theorem mem_qOne_card_of_not_mem_qZero_card
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {q : Qpack.Index}
    (hnot : q ∉ theta.qZero Qpack (Fintype.card V)) :
    q ∈ theta.qOne Qpack (Fintype.card V) := by
  classical
  apply (mem_qOne_iff theta Qpack (Fintype.card V) q).2
  constructor
  · apply (Qpack.mem_hitSet_iff_exists
        (theta.belowSet (Fintype.card V)) q).2
    exact ⟨(Qpack.path q).source, GraphPath.source_mem_vertexSet (Qpack.path q),
      by
        simp [LinkageOrdering.belowSet, theta.rank_lt_card (Qpack.path q).source]⟩
  · exact hnot

/-- If every auxiliary path intersects the linkage, then every auxiliary path
belongs to `Q0(S_t)`, `Q1(S_t)`, or `Q2(S_t)`. -/
theorem mem_qZero_or_qOne_or_qTwo_of_intersectsLinkage
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ)
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (q : Qpack.Index) :
    q ∈ theta.qZero Qpack t ∨
      q ∈ theta.qOne Qpack t ∨
        q ∈ theta.qTwo Qpack t := by
  classical
  by_cases hzero : q ∈ theta.qZero Qpack t
  · exact Or.inl hzero
  · rcases hintersects q with ⟨r, hmeet⟩
    rcases Finset.not_disjoint_iff.1 hmeet with ⟨v, hvQ, hvR⟩
    by_cases hvBelow : theta.rank v < t
    · right
      left
      apply (mem_qOne_iff theta Qpack t q).2
      constructor
      · apply (Qpack.mem_hitSet (theta.belowSet t) q).2
        exact Finset.not_disjoint_iff.2
          ⟨v, hvQ, by simp [LinkageOrdering.belowSet, hvBelow]⟩
      · exact hzero
    · right
      right
      apply (mem_qTwo_iff theta Qpack t q).2
      constructor
      · apply (Qpack.mem_hitSet (theta.aboveSet t) q).2
        have hvAbove : t ≤ theta.rank v := le_of_not_gt hvBelow
        exact Finset.not_disjoint_iff.2
          ⟨v, hvQ, by simp [LinkageOrdering.aboveSet, hvAbove]⟩
      · exact hzero

/-- If an auxiliary path intersects the linkage and is neither in `Q0(S_t)`
nor in `Q1(S_t)`, then it is in `Q2(S_t)`. -/
theorem mem_qTwo_of_intersects_not_qZero_not_qOne
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ)
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    {q : Qpack.Index}
    (hnotZero : q ∉ theta.qZero Qpack t)
    (hnotOne : q ∉ theta.qOne Qpack t) :
    q ∈ theta.qTwo Qpack t := by
  rcases mem_qZero_or_qOne_or_qTwo_of_intersectsLinkage
      theta Qpack t hintersects q with h0 | h12
  · exact False.elim (hnotZero h0)
  · rcases h12 with h1 | h2
    · exact False.elim (hnotOne h1)
    · exact h2

/-- The threshold families `Q0`, `Q1`, and `Q2` cover the whole auxiliary
packing when every auxiliary path intersects the linkage. -/
theorem qZero_union_qOne_union_qTwo_eq_univ_of_intersectsLinkage
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ)
    (hintersects : PathPackingIntersectsLinkage R Qpack) :
    theta.qZero Qpack t ∪ (theta.qOne Qpack t ∪ theta.qTwo Qpack t) =
      (Finset.univ : Finset Qpack.Index) := by
  classical
  ext q
  constructor
  · intro _hq
    simp
  · intro _hq
    rcases mem_qZero_or_qOne_or_qTwo_of_intersectsLinkage
        theta Qpack t hintersects q with h0 | h12
    · exact Finset.mem_union_left _ h0
    · rcases h12 with h1 | h2
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ h1)
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _ h2)

/-- The three threshold families are pairwise disjoint in the cardinal sense
used by the paper's partition count. -/
theorem card_qZero_union_qOne_union_qTwo
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ) :
    (theta.qZero Qpack t ∪ (theta.qOne Qpack t ∪ theta.qTwo Qpack t)).card =
      (theta.qZero Qpack t).card +
        (theta.qOne Qpack t).card + (theta.qTwo Qpack t).card := by
  classical
  have h0_12 :
      Disjoint (theta.qZero Qpack t)
        (theta.qOne Qpack t ∪ theta.qTwo Qpack t) := by
    rw [Finset.disjoint_left]
    intro q hq0 hq12
    rcases Finset.mem_union.1 hq12 with hq1 | hq2
    · exact Finset.disjoint_left.mp (disjoint_qOne_qZero theta Qpack t).symm
        hq0 hq1
    · exact Finset.disjoint_left.mp (disjoint_qTwo_qZero theta Qpack t).symm
        hq0 hq2
  rw [Finset.card_union_of_disjoint h0_12,
    Finset.card_union_of_disjoint (disjoint_qOne_qTwo theta Qpack t)]
  omega

/-- Exact cardinal form of the `Q0/Q1/Q2` partition. -/
theorem card_eq_qZero_add_qOne_add_qTwo_of_intersectsLinkage
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ)
    (hintersects : PathPackingIntersectsLinkage R Qpack) :
    Qpack.card =
      (theta.qZero Qpack t).card +
        (theta.qOne Qpack t).card + (theta.qTwo Qpack t).card := by
  classical
  have hcover :=
    qZero_union_qOne_union_qTwo_eq_univ_of_intersectsLinkage
      theta Qpack t hintersects
  calc
    Qpack.card = (Finset.univ : Finset Qpack.Index).card := by
      simp [PathPacking.card]
    _ = (theta.qZero Qpack t ∪
          (theta.qOne Qpack t ∪ theta.qTwo Qpack t)).card := by
      rw [hcover]
    _ = (theta.qZero Qpack t).card +
          (theta.qOne Qpack t).card + (theta.qTwo Qpack t).card :=
      card_qZero_union_qOne_union_qTwo theta Qpack t

/-- Cardinal form of the `Q0/Q1/Q2` cover. -/
theorem card_le_qZero_add_qOne_add_qTwo_of_intersectsLinkage
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t : ℕ)
    (hintersects : PathPackingIntersectsLinkage R Qpack) :
    Qpack.card ≤
      (theta.qZero Qpack t).card +
        (theta.qOne Qpack t).card + (theta.qTwo Qpack t).card := by
  classical
  have hcover :=
    qZero_union_qOne_union_qTwo_eq_univ_of_intersectsLinkage
      theta Qpack t hintersects
  calc
    Qpack.card = (Finset.univ : Finset Qpack.Index).card := by
      simp [PathPacking.card]
    _ = (theta.qZero Qpack t ∪
          (theta.qOne Qpack t ∪ theta.qTwo Qpack t)).card := by
      rw [hcover]
    _ ≤ (theta.qZero Qpack t).card +
          (theta.qOne Qpack t ∪ theta.qTwo Qpack t).card :=
      Finset.card_union_le _ _
    _ ≤ (theta.qZero Qpack t).card +
          ((theta.qOne Qpack t).card + (theta.qTwo Qpack t).card) := by
      exact Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ = (theta.qZero Qpack t).card +
          (theta.qOne Qpack t).card + (theta.qTwo Qpack t).card := by
      omega

/-- If the auxiliary family is larger than the separator cost plus two target
quotas, then either `Q1(S_t)` meets the first quota or `Q2(S_t)` meets the
second. -/
theorem qOne_or_qTwo_large_of_card_ge
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (t a b : ℕ)
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (hcard : R.card + a + b ≤ Qpack.card) :
    a ≤ (theta.qOne Qpack t).card ∨
      b ≤ (theta.qTwo Qpack t).card := by
  classical
  by_contra h
  rw [not_or] at h
  have hqOne : (theta.qOne Qpack t).card < a := Nat.lt_of_not_ge h.1
  have hqTwo : (theta.qTwo Qpack t).card < b := Nat.lt_of_not_ge h.2
  have hcover :=
    card_le_qZero_add_qOne_add_qTwo_of_intersectsLinkage
      theta Qpack t hintersects
  have hqZero := qZero_card_le theta Qpack t
  omega

/-- Observation 4.7 packaged as the exact threshold-selection step used in
the first iteration: a monotone-by-one sequence of `Q1` cardinalities that
starts at zero and eventually reaches `target` contains a threshold with
cardinality exactly `target`. -/
theorem exists_threshold_qOne_card_eq
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {target : ℕ}
    (hzero : (theta.qOne Qpack 0).card = 0)
    (hfinal : target ≤
      (theta.qOne Qpack (Fintype.card V)).card)
    (hstep :
      ∀ t, t < Fintype.card V →
        (theta.qOne Qpack (t + 1)).card ≤
          (theta.qOne Qpack t).card + 1) :
    ∃ t ≤ Fintype.card V, (theta.qOne Qpack t).card = target := by
  exact exists_index_card_eq_of_step_le_one
    (fun t => theta.qOne Qpack t) hzero hfinal hstep

/-- The first threshold at which `|Q1(S_t)|` reaches a prescribed target.
The final-threshold lower bound is supplied as an argument so this construction
can be used with several target sizes in the slicing algorithm. -/
noncomputable def firstQOneThreshold
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (target : ℕ)
    (hfinal :
      target ≤ (theta.qOne Qpack (Fintype.card V)).card) : ℕ :=
  Nat.find (show ∃ t : ℕ, target ≤ (theta.qOne Qpack t).card from
    ⟨Fintype.card V, hfinal⟩)

theorem firstQOneThreshold_spec
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (target : ℕ)
    (hfinal :
      target ≤ (theta.qOne Qpack (Fintype.card V)).card) :
    target ≤
      (theta.qOne Qpack
        (firstQOneThreshold theta Qpack target hfinal)).card := by
  classical
  simpa [firstQOneThreshold] using
    (Nat.find_spec
      (show ∃ t : ℕ, target ≤ (theta.qOne Qpack t).card from
        ⟨Fintype.card V, hfinal⟩))

theorem firstQOneThreshold_le_card
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (target : ℕ)
    (hfinal :
      target ≤ (theta.qOne Qpack (Fintype.card V)).card) :
    firstQOneThreshold theta Qpack target hfinal ≤ Fintype.card V := by
  classical
  exact Nat.find_min'
    (show ∃ t : ℕ, target ≤ (theta.qOne Qpack t).card from
      ⟨Fintype.card V, hfinal⟩)
    hfinal

theorem firstQOneThreshold_mono
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {target₁ target₂ : ℕ}
    (htarget : target₁ ≤ target₂)
    (hfinal₁ :
      target₁ ≤ (theta.qOne Qpack (Fintype.card V)).card)
    (hfinal₂ :
      target₂ ≤ (theta.qOne Qpack (Fintype.card V)).card) :
    firstQOneThreshold theta Qpack target₁ hfinal₁ ≤
      firstQOneThreshold theta Qpack target₂ hfinal₂ := by
  classical
  apply Nat.find_min'
    (show ∃ t : ℕ, target₁ ≤ (theta.qOne Qpack t).card from
      ⟨Fintype.card V, hfinal₁⟩)
  exact htarget.trans
    (firstQOneThreshold_spec theta Qpack target₂ hfinal₂)

/-- With the Observation 4.7 one-step growth bound, the first threshold
reaching a target has exactly that target cardinality. -/
theorem firstQOneThreshold_card_eq_of_step
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {target : ℕ}
    (hfinal :
      target ≤ (theta.qOne Qpack (Fintype.card V)).card)
    (hstep :
      ∀ t, t < Fintype.card V →
        (theta.qOne Qpack (t + 1)).card ≤
          (theta.qOne Qpack t).card + 1) :
    (theta.qOne Qpack
      (firstQOneThreshold theta Qpack target hfinal)).card = target := by
  classical
  let H : ∃ t : ℕ, target ≤ (theta.qOne Qpack t).card :=
    ⟨Fintype.card V, hfinal⟩
  let τ := firstQOneThreshold theta Qpack target hfinal
  change (theta.qOne Qpack τ).card = target
  have hτspec : target ≤ (theta.qOne Qpack τ).card := by
    simpa [τ, firstQOneThreshold, H] using Nat.find_spec H
  have hτle : τ ≤ Fintype.card V := by
    simpa [τ, firstQOneThreshold, H] using Nat.find_min' H hfinal
  by_cases hzeroτ : τ = 0
  · have htarget0 : target = 0 := by
      have hle0 : target ≤ 0 := by
        simpa [τ, hzeroτ, qOne_zero_card theta Qpack] using hτspec
      exact Nat.eq_zero_of_le_zero hle0
    rw [hzeroτ, htarget0]
    exact qOne_zero_card theta Qpack
  · have hτpos : 0 < τ := Nat.pos_of_ne_zero hzeroτ
    let j := τ - 1
    have hsucc : j + 1 = τ := by
      simpa [j] using Nat.succ_pred_eq_of_pos hτpos
    have hjltτ : j < τ := by omega
    have hjnot : ¬ target ≤ (theta.qOne Qpack j).card := by
      simpa [τ, firstQOneThreshold, H] using Nat.find_min H hjltτ
    have hjcard_lt : (theta.qOne Qpack j).card < target :=
      Nat.lt_of_not_ge hjnot
    have hjltCard : j < Fintype.card V := by omega
    have hstepj :
        (theta.qOne Qpack τ).card ≤
          (theta.qOne Qpack j).card + 1 := by
      simpa [hsucc] using hstep j hjltCard
    omega

/-- Threshold membership criterion for the paths captured by a concrete slice.

If a path is on the upper side of the lower threshold and on the lower side of
the upper threshold, while avoiding both threshold separators as encoded by
`Q2` and `Q1`, then every intersection with the row linkage lies strictly
between the two corresponding cut vertices. -/
theorem ThresholdSequence.pathInSlice_of_mem_qTwo_qOne
    {R : PerfectPathPacking G A B} {M : ℕ}
    (theta : LinkageOrdering R) (tau : ThresholdSequence R theta M)
    (Qpack : PathPacking G S T) (i : Fin M) {q : Qpack.Index}
    (hlo : q ∈ theta.qTwo Qpack (tau.threshold i.castSucc))
    (hhi : q ∈ theta.qOne Qpack (tau.threshold i.succ)) :
    (tau.toPathSlicing theta).PathInSlice Qpack i q := by
  classical
  intro r v hvQ hvR
  refine ⟨hvR, ?_, ?_, ?_, ?_⟩
  · simpa [ThresholdSequence.toPathSlicing] using
      separator_before_qTwo_intersection theta Qpack
        (tau.threshold i.castSucc) hlo hvQ hvR
  · simpa [ThresholdSequence.toPathSlicing] using
      qOne_intersection_before_separator theta Qpack
        (tau.threshold i.succ) hhi hvQ hvR
  · simpa [ThresholdSequence.toPathSlicing] using
      qTwo_ne_separatorVertex_of_mem theta Qpack
        (tau.threshold i.castSucc) hlo hvQ
  · simpa [ThresholdSequence.toPathSlicing] using
      qOne_ne_separatorVertex_of_mem theta Qpack
        (tau.threshold i.succ) hhi hvQ

/-- Cardinal version of the threshold membership criterion: any finite set of
auxiliary paths contained in the relevant `Q2(lower) ∩ Q1(upper)` contributes
to the corresponding slice of the threshold slicing. -/
theorem ThresholdSequence.card_pathsInSlice_ge_of_subset_qTwo_inter_qOne
    {R : PerfectPathPacking G A B} {M : ℕ}
    (theta : LinkageOrdering R) (tau : ThresholdSequence R theta M)
    (Qpack : PathPacking G S T) (i : Fin M) (I : Finset Qpack.Index)
    (hI :
      I ⊆ theta.qTwo Qpack (tau.threshold i.castSucc) ∩
        theta.qOne Qpack (tau.threshold i.succ)) :
    I.card ≤ ((tau.toPathSlicing theta).pathsInSlice Qpack i).card := by
  classical
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_inter.1 (hI hq) with ⟨hlo, hhi⟩
  exact ((tau.toPathSlicing theta).mem_pathsInSlice Qpack i q).2
    (tau.pathInSlice_of_mem_qTwo_qOne theta Qpack i hlo hhi)

/-- General slice-counting lemma.  If the `Q1` family grows by at least
`w + |R|` between the lower and upper threshold of a slice, then after
discarding the at-most-`|R|` paths hitting the lower separator, at least `w`
paths lie in that slice. -/
theorem ThresholdSequence.slice_card_ge_of_qOne_gap
    {R : PerfectPathPacking G A B} {M : ℕ}
    (theta : LinkageOrdering R) (tau : ThresholdSequence R theta M)
    (Qpack : PathPacking G S T) (i : Fin M) {w : ℕ}
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (hgap :
      w + R.card ≤
        (theta.qOne Qpack (tau.threshold i.succ)).card -
          (theta.qOne Qpack (tau.threshold i.castSucc)).card) :
    w ≤ ((tau.toPathSlicing theta).pathsInSlice Qpack i).card := by
  classical
  let lower := tau.threshold i.castSucc
  let upper := tau.threshold i.succ
  let Q1lo : Finset Qpack.Index := theta.qOne Qpack lower
  let Q1hi : Finset Qpack.Index := theta.qOne Qpack upper
  let D : Finset Qpack.Index := Q1hi \ Q1lo
  let I : Finset Qpack.Index := D \ theta.qZero Qpack lower
  have hleThreshold : lower ≤ upper := tau.threshold_monotone (by
    exact Fin.castSucc_le_succ i)
  have hQ1sub : Q1lo ⊆ Q1hi := qOne_mono theta Qpack hleThreshold
  have hDcard : D.card = Q1hi.card - Q1lo.card := by
    simpa [D] using Finset.card_sdiff_of_subset hQ1sub
  have hIcard : w ≤ I.card := by
    have hq0 := qZero_card_le theta Qpack lower
    have hwsub : w ≤ D.card - (theta.qZero Qpack lower).card := by
      rw [hDcard]
      have hgap' :
          w + R.card ≤ Q1hi.card - Q1lo.card := by
        simpa [lower, upper, Q1lo, Q1hi] using hgap
      omega
    exact hwsub.trans
      (Finset.le_card_sdiff (theta.qZero Qpack lower) D)
  have hI_subset :
      I ⊆ theta.qTwo Qpack lower ∩ theta.qOne Qpack upper := by
    intro q hq
    rcases Finset.mem_sdiff.1 hq with ⟨hqD, hnotZero⟩
    rcases Finset.mem_sdiff.1 hqD with ⟨hqHi, hnotLo⟩
    exact Finset.mem_inter.2
      ⟨mem_qTwo_of_intersects_not_qZero_not_qOne
          theta Qpack lower hintersects hnotZero hnotLo,
        hqHi⟩
  exact hIcard.trans
    (tau.card_pathsInSlice_ge_of_subset_qTwo_inter_qOne
      theta Qpack i I (by simpa [lower, upper, I] using hI_subset))

/-- Final-slice counting lemma.  If `Q2` at the lower threshold has
`w + |R|` paths, then after discarding the at-most-`|R|` paths hitting the
final separator, at least `w` paths lie in the slice ending at the final cut.
-/
theorem ThresholdSequence.last_slice_card_ge_of_qTwo_gap
    {R : PerfectPathPacking G A B} {M : ℕ}
    (theta : LinkageOrdering R) (tau : ThresholdSequence R theta M)
    (Qpack : PathPacking G S T) (i : Fin M) {w : ℕ}
    (hupper : tau.threshold i.succ = Fintype.card V)
    (hgap : w + R.card ≤
      (theta.qTwo Qpack (tau.threshold i.castSucc)).card) :
    w ≤ ((tau.toPathSlicing theta).pathsInSlice Qpack i).card := by
  classical
  let lower := tau.threshold i.castSucc
  let I : Finset Qpack.Index :=
    theta.qTwo Qpack lower \ theta.qZero Qpack (Fintype.card V)
  have hI_subset :
      I ⊆ theta.qTwo Qpack lower ∩ theta.qOne Qpack (tau.threshold i.succ) := by
    intro q hq
    rcases Finset.mem_sdiff.1 hq with ⟨hqTwo, hnotFinal⟩
    exact Finset.mem_inter.2
      ⟨hqTwo, by
        rw [hupper]
        exact mem_qOne_card_of_not_mem_qZero_card theta Qpack hnotFinal⟩
  have hIcard : w ≤ I.card := by
    have hq0 := qZero_card_le theta Qpack (Fintype.card V)
    have hgapLower :
        w + R.card ≤ (theta.qTwo Qpack lower).card := by
      simpa [lower] using hgap
    have hwq0 :
        w + (theta.qZero Qpack (Fintype.card V)).card ≤
          (theta.qTwo Qpack lower).card := by
      omega
    have hwsub :
        w ≤ (theta.qTwo Qpack lower).card -
          (theta.qZero Qpack (Fintype.card V)).card := by
      exact Nat.le_sub_of_add_le hwq0
    exact hwsub.trans
      (Finset.le_card_sdiff
        (theta.qZero Qpack (Fintype.card V)) (theta.qTwo Qpack lower))
  exact hIcard.trans
    (tau.card_pathsInSlice_ge_of_subset_qTwo_inter_qOne
      theta Qpack i I (by simpa [lower, I] using hI_subset))

/-- The canonical threshold sequence used in the proof of Theorem 4.6.  The
internal cut `i` is the first threshold where `|Q1|` reaches
`i * (w + |R|)`, while the first and last cuts are forced to be `0` and
`|V|`. -/
noncomputable def ThresholdSequence.ofQOneTargets
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (M w : ℕ) (hM : 0 < M)
    (hfinal :
      M * (w + R.card) ≤
        (theta.qOne Qpack (Fintype.card V)).card) :
    ThresholdSequence R theta M := by
  classical
  let N : ℕ := w + R.card
  let target : Fin (M + 1) → ℕ := fun i => i.val * N
  have targetLeFinal :
      ∀ i : Fin (M + 1),
        target i ≤ (theta.qOne Qpack (Fintype.card V)).card := by
    intro i
    have hile : i.val ≤ M := Nat.le_of_lt_succ i.isLt
    exact (Nat.mul_le_mul_right N hile).trans hfinal
  let thresholdFun : Fin (M + 1) → ℕ := fun i =>
    if h0 : i = 0 then 0
    else if hlast : i = Fin.last M then Fintype.card V
    else firstQOneThreshold theta Qpack (target i) (targetLeFinal i)
  have thresholdFun_zero : thresholdFun 0 = 0 := by
    simp [thresholdFun]
  have thresholdFun_last : thresholdFun (Fin.last M) = Fintype.card V := by
    have hlast_ne_zero : (Fin.last M) ≠ (0 : Fin (M + 1)) := by
      intro h
      have hval : M = 0 := by
        simpa using congrArg Fin.val h
      omega
    simp [thresholdFun, hlast_ne_zero]
  have thresholdFun_le_card : ∀ i : Fin (M + 1),
      thresholdFun i ≤ Fintype.card V := by
    intro i
    by_cases hi0 : i = 0
    · simp [thresholdFun, hi0]
    · by_cases hiLast : i = Fin.last M
      · have hMne : M ≠ 0 := Nat.ne_of_gt hM
        simp [thresholdFun, hiLast, hMne]
      · simpa [thresholdFun, hi0, hiLast] using
          firstQOneThreshold_le_card theta Qpack (target i) (targetLeFinal i)
  have thresholdFun_mono :
      ∀ ⦃s t : Fin (M + 1)⦄, s ≤ t →
        thresholdFun s ≤ thresholdFun t := by
    intro s t hst
    have hval : s.val ≤ t.val := hst
    by_cases hs0 : s = 0
    · simp [thresholdFun, hs0]
    · by_cases htLast : t = Fin.last M
      · have ht0 : t ≠ (0 : Fin (M + 1)) := by
          intro ht0
          exact hs0 (le_antisymm (by simpa [ht0] using hst) (by simp))
        have htEq : thresholdFun t = Fintype.card V := by
          have hMne : M ≠ 0 := Nat.ne_of_gt hM
          simp [thresholdFun, htLast, hMne]
        rw [htEq]
        exact thresholdFun_le_card s
      · have ht0 : t ≠ (0 : Fin (M + 1)) := by
          intro ht0
          have hsval0 : s.val = 0 := by
            have htval0 : t.val = 0 := by simpa using congrArg Fin.val ht0
            omega
          exact hs0 (Fin.ext hsval0)
        have hsLast : s ≠ Fin.last M := by
          intro hsLast
          have htleM : t.val ≤ M := Nat.le_of_lt_succ t.isLt
          have hsvalM : s.val = M := by
            simpa using congrArg Fin.val hsLast
          have htvalM : t.val = M := by omega
          exact htLast (Fin.ext htvalM)
        have htarget : target s ≤ target t :=
          Nat.mul_le_mul_right N hval
        simpa [thresholdFun, hs0, hsLast, ht0, htLast] using
          firstQOneThreshold_mono theta Qpack htarget
            (targetLeFinal s) (targetLeFinal t)
  exact
    { threshold := thresholdFun
      threshold_zero := thresholdFun_zero
      threshold_last := thresholdFun_last
      threshold_monotone := thresholdFun_mono }

/-- Cardinality of `Q1` at an internal cut of
`ThresholdSequence.ofQOneTargets`. -/
theorem ThresholdSequence.ofQOneTargets_qOne_card
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (M w : ℕ) (hM : 0 < M)
    (hfinal :
      M * (w + R.card) ≤
        (theta.qOne Qpack (Fintype.card V)).card)
    (hstep :
      ∀ t, t < Fintype.card V →
        (theta.qOne Qpack (t + 1)).card ≤
          (theta.qOne Qpack t).card + 1)
    (i : Fin (M + 1)) (hi0 : i.val ≠ 0) (hiM : i.val ≠ M) :
    (theta.qOne Qpack
      ((ThresholdSequence.ofQOneTargets theta Qpack M w hM hfinal).threshold i)).card =
        i.val * (w + R.card) := by
  classical
  let N : ℕ := w + R.card
  let target : Fin (M + 1) → ℕ := fun i => i.val * N
  have targetLeFinal :
      ∀ i : Fin (M + 1),
        target i ≤ (theta.qOne Qpack (Fintype.card V)).card := by
    intro i
    have hile : i.val ≤ M := Nat.le_of_lt_succ i.isLt
    exact (Nat.mul_le_mul_right N hile).trans hfinal
  have hi0' : i ≠ (0 : Fin (M + 1)) := by
    intro h
    exact hi0 (by simpa using congrArg Fin.val h)
  have hiLast' : i ≠ Fin.last M := by
    intro h
    exact hiM (by simpa using congrArg Fin.val h)
  simpa [ThresholdSequence.ofQOneTargets, N, target, hi0', hiLast'] using
    firstQOneThreshold_card_eq_of_step
      theta Qpack (targetLeFinal i) hstep

/-- Cardinality of `Q1` at any non-final cut of
`ThresholdSequence.ofQOneTargets`; this includes the first cut, where both
sides are zero. -/
theorem ThresholdSequence.ofQOneTargets_qOne_card_of_ne_last
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (M w : ℕ) (hM : 0 < M)
    (hfinal :
      M * (w + R.card) ≤
        (theta.qOne Qpack (Fintype.card V)).card)
    (hstep :
      ∀ t, t < Fintype.card V →
        (theta.qOne Qpack (t + 1)).card ≤
          (theta.qOne Qpack t).card + 1)
    (i : Fin (M + 1)) (hiLast : i ≠ Fin.last M) :
    (theta.qOne Qpack
      ((ThresholdSequence.ofQOneTargets theta Qpack M w hM hfinal).threshold i)).card =
        i.val * (w + R.card) := by
  classical
  by_cases hi0 : i = (0 : Fin (M + 1))
  · simp [hi0, ThresholdSequence.ofQOneTargets,
      qOne_zero_card theta Qpack]
  · have hi0val : i.val ≠ 0 := by
      intro h
      exact hi0 (Fin.ext h)
    have hiMval : i.val ≠ M := by
      intro h
      exact hiLast (Fin.ext h)
    exact ThresholdSequence.ofQOneTargets_qOne_card
      theta Qpack M w hM hfinal hstep i hi0val hiMval

/-- The self-contained slicing theorem once a Robertson--Seymour ordering has
been supplied.  This is Theorem 4.6 minus Lemma 4.5's construction of the
ordering from uniqueness. -/
theorem exists_slicing_of_linkageOrdering
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) (M w : ℕ)
    (hM : 0 < M)
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (hcard : M * w + (M + 1) * R.card ≤ Qpack.card) :
    ∃ sigma : PathSlicing R M, sigma.WidthAtLeast Qpack w := by
  classical
  have hfinal :
      M * (w + R.card) ≤
        (theta.qOne Qpack (Fintype.card V)).card := by
    have hfinalLower := qOne_card_final_lower_bound theta Qpack
    have htarget :
        M * (w + R.card) ≤ Qpack.card - R.card := by
      apply Nat.le_sub_of_add_le
      calc
        M * (w + R.card) + R.card
            = M * w + (M + 1) * R.card := by
              rw [Nat.mul_add, Nat.add_mul, Nat.one_mul]
              omega
        _ ≤ Qpack.card := hcard
    exact htarget.trans hfinalLower
  let tau := ThresholdSequence.ofQOneTargets theta Qpack M w hM hfinal
  have hstep :
      ∀ t, t < Fintype.card V →
        (theta.qOne Qpack (t + 1)).card ≤
          (theta.qOne Qpack t).card + 1 :=
    fun t ht => qOne_succ_card_le theta Qpack ht
  refine ⟨tau.toPathSlicing theta, ?_⟩
  intro i
  have hlo_ne_last : i.castSucc ≠ (Fin.last M : Fin (M + 1)) := by
    intro h
    have hval : i.val = M := by
      simpa using congrArg Fin.val h
    exact (Nat.ne_of_lt i.isLt) hval
  by_cases hiLast : i.succ = (Fin.last M : Fin (M + 1))
  · have hupper :
        tau.threshold i.succ = Fintype.card V := by
      simpa [tau, hiLast] using tau.threshold_last
    have hloCard :
        (theta.qOne Qpack (tau.threshold i.castSucc)).card =
          i.val * (w + R.card) := by
      simpa [tau] using
        ThresholdSequence.ofQOneTargets_qOne_card_of_ne_last
          theta Qpack M w hM hfinal hstep i.castSucc hlo_ne_last
    have hiM : i.val + 1 = M := by
      simpa using congrArg Fin.val hiLast
    have hpartition :=
      card_eq_qZero_add_qOne_add_qTwo_of_intersectsLinkage
        theta Qpack (tau.threshold i.castSucc) hintersects
    have hq0 := qZero_card_le theta Qpack (tau.threshold i.castSucc)
    have hgap : w + R.card ≤
        (theta.qTwo Qpack (tau.threshold i.castSucc)).card := by
      rw [hloCard] at hpartition
      have hcard_i :
          (i.val + 1) * w + ((i.val + 1) + 1) * R.card ≤ Qpack.card := by
        simpa [hiM] using hcard
      have hneeded :
          i.val * (w + R.card) + (w + R.card) + R.card ≤ Qpack.card := by
        calc
          i.val * (w + R.card) + (w + R.card) + R.card
              = (i.val + 1) * w + ((i.val + 1) + 1) * R.card := by
                ring_nf
          _ ≤ Qpack.card := hcard_i
      omega
    exact ThresholdSequence.last_slice_card_ge_of_qTwo_gap
      theta tau Qpack i hupper hgap
  · have hupperCard :
        (theta.qOne Qpack (tau.threshold i.succ)).card =
          (i.val + 1) * (w + R.card) := by
      have hsuccVal : (i.succ : Fin (M + 1)).val = i.val + 1 := rfl
      simpa [tau, hsuccVal] using
        ThresholdSequence.ofQOneTargets_qOne_card_of_ne_last
          theta Qpack M w hM hfinal hstep i.succ hiLast
    have hlowerCard :
        (theta.qOne Qpack (tau.threshold i.castSucc)).card =
          i.val * (w + R.card) := by
      simpa [tau] using
        ThresholdSequence.ofQOneTargets_qOne_card_of_ne_last
          theta Qpack M w hM hfinal hstep i.castSucc hlo_ne_last
    have hgap :
        w + R.card ≤
          (theta.qOne Qpack (tau.threshold i.succ)).card -
            (theta.qOne Qpack (tau.threshold i.castSucc)).card := by
      rw [hupperCard, hlowerCard]
      apply Nat.le_sub_of_add_le
      rw [Nat.succ_mul]
      omega
    exact ThresholdSequence.slice_card_ge_of_qOne_gap
      theta tau Qpack i hintersects hgap

/-- First-slice counting in the initial two-slice construction from the proof
of Theorem 4.6.  If `Q1(S_t)` has `w` paths after paying for the at-most-`|R|`
paths hitting the first separator, then the first slice of `(0,t,|V|)` has
width at least `w`. -/
theorem ThresholdSequence.two_first_slice_card_ge
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {t w : ℕ}
    (ht : t ≤ Fintype.card V)
    (hcard : w + R.card ≤ (theta.qOne Qpack t).card) :
    w ≤ (((ThresholdSequence.two theta t ht).toPathSlicing theta).pathsInSlice
      Qpack (0 : Fin 2)).card := by
  classical
  let tau := ThresholdSequence.two theta t ht
  let I : Finset Qpack.Index := theta.qOne Qpack t \ theta.qZero Qpack 0
  have hI_subset :
      I ⊆ theta.qTwo Qpack (tau.threshold (0 : Fin 2).castSucc) ∩
        theta.qOne Qpack (tau.threshold (0 : Fin 2).succ) := by
    intro q hq
    have hqOne : q ∈ theta.qOne Qpack t := (Finset.mem_sdiff.1 hq).1
    have hnotZero : q ∉ theta.qZero Qpack 0 := (Finset.mem_sdiff.1 hq).2
    exact Finset.mem_inter.2 ⟨by
      simpa [tau] using mem_qTwo_zero_of_not_mem_qZero_zero
        theta Qpack hnotZero
    , by
      simpa [tau] using hqOne⟩
  have hIcard : w ≤ I.card := by
    have hq0 := qZero_card_le theta Qpack 0
    have hwq0 : w + (theta.qZero Qpack 0).card ≤
        (theta.qOne Qpack t).card := by
      omega
    have hdiff : w ≤
        (theta.qOne Qpack t).card - (theta.qZero Qpack 0).card :=
      Nat.le_sub_of_add_le hwq0
    exact hdiff.trans
      (Finset.le_card_sdiff (theta.qZero Qpack 0) (theta.qOne Qpack t))
  exact hIcard.trans
    (tau.card_pathsInSlice_ge_of_subset_qTwo_inter_qOne theta Qpack
      (0 : Fin 2) I hI_subset)

/-- Last-slice counting in the initial two-slice construction from the proof
of Theorem 4.6.  If `Q2(S_t)` has `w` paths after paying for the at-most-`|R|`
paths hitting the final separator, then the second slice of `(0,t,|V|)` has
width at least `w`. -/
theorem ThresholdSequence.two_second_slice_card_ge
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {t w : ℕ}
    (ht : t ≤ Fintype.card V)
    (hcard : w + R.card ≤ (theta.qTwo Qpack t).card) :
    w ≤ (((ThresholdSequence.two theta t ht).toPathSlicing theta).pathsInSlice
      Qpack (1 : Fin 2)).card := by
  classical
  let tau := ThresholdSequence.two theta t ht
  let I : Finset Qpack.Index :=
    theta.qTwo Qpack t \ theta.qZero Qpack (Fintype.card V)
  have hI_subset :
      I ⊆ theta.qTwo Qpack (tau.threshold (1 : Fin 2).castSucc) ∩
        theta.qOne Qpack (tau.threshold (1 : Fin 2).succ) := by
    intro q hq
    have hqTwo : q ∈ theta.qTwo Qpack t := (Finset.mem_sdiff.1 hq).1
    have hnotZero : q ∉ theta.qZero Qpack (Fintype.card V) :=
      (Finset.mem_sdiff.1 hq).2
    exact Finset.mem_inter.2 ⟨by
      simpa [tau] using hqTwo
    , by
      simpa [tau] using mem_qOne_card_of_not_mem_qZero_card
        theta Qpack hnotZero⟩
  have hIcard : w ≤ I.card := by
    have hq0 := qZero_card_le theta Qpack (Fintype.card V)
    have hwq0 : w + (theta.qZero Qpack (Fintype.card V)).card ≤
        (theta.qTwo Qpack t).card := by
      omega
    have hdiff : w ≤
        (theta.qTwo Qpack t).card -
          (theta.qZero Qpack (Fintype.card V)).card :=
      Nat.le_sub_of_add_le hwq0
    exact hdiff.trans
      (Finset.le_card_sdiff
        (theta.qZero Qpack (Fintype.card V)) (theta.qTwo Qpack t))
  exact hIcard.trans
    (tau.card_pathsInSlice_ge_of_subset_qTwo_inter_qOne theta Qpack
      (1 : Fin 2) I hI_subset)

/-- The initial two-slice construction from the proof of Theorem 4.6, packaged
as a width statement. -/
theorem ThresholdSequence.two_widthAtLeast
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {t w : ℕ}
    (ht : t ≤ Fintype.card V)
    (hfirst : w + R.card ≤ (theta.qOne Qpack t).card)
    (hsecond : w + R.card ≤ (theta.qTwo Qpack t).card) :
    ((ThresholdSequence.two theta t ht).toPathSlicing theta).WidthAtLeast
      Qpack w := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hlt : i.val < 2 := i.isLt
    omega
  rcases hi with hi | hi
  · have hifin : i = (0 : Fin 2) := Fin.ext hi
    simpa [hifin] using
      ThresholdSequence.two_first_slice_card_ge theta Qpack ht hfirst
  · have hifin : i = (1 : Fin 2) := Fin.ext hi
    simpa [hifin] using
      ThresholdSequence.two_second_slice_card_ge theta Qpack ht hsecond

/-- First algorithmic step of Theorem 4.6.

Once Observation 4.7 supplies a threshold `t` with
`|Q1(S_t)| = w + |R|`, the global budget `|Q| ≥ 2w + 3|R|` implies that both
halves of the two-slice threshold sequence `(0,t,|V|)` have width at least
`w`. -/
theorem ThresholdSequence.two_widthAtLeast_of_qOne_card_eq
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {t w : ℕ}
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (ht : t ≤ Fintype.card V)
    (hqOne : (theta.qOne Qpack t).card = w + R.card)
    (hcard : 2 * w + 3 * R.card ≤ Qpack.card) :
    ((ThresholdSequence.two theta t ht).toPathSlicing theta).WidthAtLeast
      Qpack w := by
  classical
  have hfirst : w + R.card ≤ (theta.qOne Qpack t).card := by
    omega
  have hpartition :=
    card_eq_qZero_add_qOne_add_qTwo_of_intersectsLinkage
      theta Qpack t hintersects
  have hq0 := qZero_card_le theta Qpack t
  have hsecond : w + R.card ≤ (theta.qTwo Qpack t).card := by
    omega
  exact ThresholdSequence.two_widthAtLeast theta Qpack ht hfirst hsecond

/-- Two-slice existence from the Observation 4.7 hypotheses.  This is the
base case of the slicing algorithm in Theorem 4.6, separated from the later
inductive refinement. -/
theorem ThresholdSequence.exists_two_slicing_of_observation47
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {w : ℕ}
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (hzero : (theta.qOne Qpack 0).card = 0)
    (hfinal :
      w + R.card ≤ (theta.qOne Qpack (Fintype.card V)).card)
    (hstep :
      ∀ t, t < Fintype.card V →
        (theta.qOne Qpack (t + 1)).card ≤
          (theta.qOne Qpack t).card + 1)
    (hcard : 2 * w + 3 * R.card ≤ Qpack.card) :
    ∃ sigma : PathSlicing R 2, sigma.WidthAtLeast Qpack w := by
  classical
  rcases exists_threshold_qOne_card_eq theta Qpack hzero hfinal hstep with
    ⟨t, ht, htcard⟩
  exact ⟨(ThresholdSequence.two theta t ht).toPathSlicing theta,
    ThresholdSequence.two_widthAtLeast_of_qOne_card_eq
      theta Qpack hintersects ht htcard hcard⟩

/-- Two-slice existence from the remaining one-step growth clause of
Observation 4.7.  The endpoint clauses of Observation 4.7 are proved above, so
this theorem isolates the only still-unproved base-case input: `Q1` grows by
at most one path per threshold step. -/
theorem ThresholdSequence.exists_two_slicing_of_qOne_step
    {R : PerfectPathPacking G A B} (theta : LinkageOrdering R)
    (Qpack : PathPacking G S T) {w : ℕ}
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (hstep :
      ∀ t, t < Fintype.card V →
        (theta.qOne Qpack (t + 1)).card ≤
          (theta.qOne Qpack t).card + 1)
    (hcard : 2 * w + 3 * R.card ≤ Qpack.card) :
    ∃ sigma : PathSlicing R 2, sigma.WidthAtLeast Qpack w := by
  classical
  apply ThresholdSequence.exists_two_slicing_of_observation47
    theta Qpack hintersects (qOne_zero_card theta Qpack) ?_ hstep hcard
  have hfinal := qOne_card_final_lower_bound theta Qpack
  omega

end PathSlicing

namespace PerfectPathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B X : Finset V}

/-- Sources of disjoint index sets are disjoint. -/
theorem sourceSet_disjoint_of_disjoint
    {S T : Finset V} (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : Disjoint I J) :
    Disjoint (P.sourceSet I) (P.sourceSet J) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvI hvJ
  rcases Finset.mem_image.mp hvI with ⟨i, hi, hvi⟩
  rcases Finset.mem_image.mp hvJ with ⟨j, hj, hvj⟩
  have hij : i = j := by
    apply P.source_bijective.1
    exact Subtype.ext (hvi.trans hvj.symm)
  exact Finset.disjoint_left.mp hIJ hi (by simpa [hij] using hj)

/-- Targets of disjoint index sets are disjoint. -/
theorem targetSet_disjoint_of_disjoint
    {S T : Finset V} (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : Disjoint I J) :
    Disjoint (P.targetSet I) (P.targetSet J) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvI hvJ
  rcases Finset.mem_image.mp hvI with ⟨i, hi, hvi⟩
  rcases Finset.mem_image.mp hvJ with ⟨j, hj, hvj⟩
  have hij : i = j := by
    apply P.target_bijective.1
    exact Subtype.ext (hvi.trans hvj.symm)
  exact Finset.disjoint_left.mp hIJ hi (by simpa [hij] using hj)

/-- The sources of an index set and its complement partition the left terminal
set. -/
theorem sourceSet_union_sdiff_eq_left
    {S T : Finset V} (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    P.sourceSet I ∪ P.sourceSet ((Finset.univ : Finset P.Index) \ I) = S := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hvI | hvI
    · exact P.sourceSet_subset_left I hvI
    · exact P.sourceSet_subset_left ((Finset.univ : Finset P.Index) \ I) hvI
  · intro hvS
    rcases P.source_bijective.2 ⟨v, hvS⟩ with ⟨i, hi⟩
    have hsrc : (P.path i).source = v :=
      congrArg (fun x : {v // v ∈ S} => x.1) hi
    by_cases hiI : i ∈ I
    · exact Finset.mem_union_left _
        (Finset.mem_image.2 ⟨i, hiI, hsrc⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.2
          ⟨i, Finset.mem_sdiff.2 ⟨by simp, hiI⟩, hsrc⟩)

/-- The targets of an index set and its complement partition the right terminal
set. -/
theorem targetSet_union_sdiff_eq_right
    {S T : Finset V} (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    P.targetSet I ∪ P.targetSet ((Finset.univ : Finset P.Index) \ I) = T := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hvI | hvI
    · exact P.targetSet_subset_right I hvI
    · exact P.targetSet_subset_right ((Finset.univ : Finset P.Index) \ I) hvI
  · intro hvT
    rcases P.target_bijective.2 ⟨v, hvT⟩ with ⟨i, hi⟩
    have htgt : (P.path i).target = v :=
      congrArg (fun x : {v // v ∈ T} => x.1) hi
    by_cases hiI : i ∈ I
    · exact Finset.mem_union_left _
        (Finset.mem_image.2 ⟨i, hiI, htgt⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.2
          ⟨i, Finset.mem_sdiff.2 ⟨by simp, hiI⟩, htgt⟩)

/-- The sources of an index set are disjoint from the sources of its
complement. -/
theorem sourceSet_disjoint_sdiff
    {S T : Finset V} (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    Disjoint (P.sourceSet I)
      (P.sourceSet ((Finset.univ : Finset P.Index) \ I)) :=
  P.sourceSet_disjoint_of_disjoint (Finset.disjoint_sdiff)

/-- The targets of an index set are disjoint from the targets of its
complement. -/
theorem targetSet_disjoint_sdiff
    {S T : Finset V} (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    Disjoint (P.targetSet I)
      (P.targetSet ((Finset.univ : Finset P.Index) \ I)) :=
  P.targetSet_disjoint_of_disjoint (Finset.disjoint_sdiff)

/-- A minimum Theorem 4.1 pair admits no replacement pair with smaller
edge-union count. -/
theorem not_pairUnionEdgeCount_lt_of_minimum
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X)
    (hmin : P.IsMinimumTheorem41Pair Q)
    (P' : PerfectPathPacking G A B) (Q' : PerfectPathPacking G A X) :
    ¬ P'.pairUnionEdgeCount Q' < P.pairUnionEdgeCount Q := by
  intro hlt
  exact Nat.not_lt_of_ge (hmin P' Q') hlt

/-- The uniqueness argument used in Observation 4.4.

The hypotheses isolate the two graph-theoretic facts supplied by the
contraction procedure and Observation 4.3: every different linkage omits some
edge of `R`, and deleting any edge of `R` leaves no full-size linkage. -/
theorem isUniqueLinkage_of_edge_deletion_bound
    {A B : Finset V} (R : PerfectPathPacking G A B)
    (hspan : R.SpansVertices)
    (hcard_pos : 0 < R.card)
    (hmissing :
      ∀ R' : PerfectPathPacking G A B,
        R'.toPathPacking.edgeSet ≠ R.toPathPacking.edgeSet →
          ∃ e ∈ R.toPathPacking.edgeSet, e ∉ R'.toPathPacking.edgeSet)
    (hdelete :
      ∀ e ∈ R.toPathPacking.edgeSet,
        ∀ L : PathPacking (G.deleteEdges ({e} : Set (Sym2 V))) A B,
          L.card ≤ R.card - 1) :
    R.IsUniqueLinkage := by
  constructor
  · exact hspan
  · intro R'
    by_contra hne
    rcases hmissing R' hne with ⟨e, heR, heR'⟩
    let L : PathPacking (G.deleteEdges ({e} : Set (Sym2 V))) A B :=
      R'.toPathPacking.deleteEdgeOfNotMemEdgeSet e heR'
    have hbound : L.card ≤ R.card - 1 := hdelete e heR L
    have hLcard : L.card = R.card := by
      calc
        L.card = R'.toPathPacking.card := by simp [L]
        _ = R'.card := rfl
        _ = A.card := R'.card_eq_left_card
        _ = R.card := R.card_eq_left_card.symm
    omega

end PerfectPathPacking

namespace PseudoGrid

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

/-- A fixed witness for the at-most-`2g^2` set of `Q'` segments that miss row
`i`. -/
noncomputable def rowMissSet
    (Gamma : PseudoGrid G A B X g D P Q) (i : Fin D) :
    Finset Gamma.QIndex :=
  Classical.choose (Gamma.few_qPath_miss_reserved i)

/-- The row-miss witness has the cardinality guaranteed by pseudo-grid
property P2. -/
theorem rowMissSet_card_le
    (Gamma : PseudoGrid G A B X g D P Q) (i : Fin D) :
    (Gamma.rowMissSet i).card ≤ 2 * g ^ 2 :=
  (Classical.choose_spec (Gamma.few_qPath_miss_reserved i)).1

/-- Every selected `Q'` segment that misses row `i` belongs to the chosen
row-miss witness. -/
theorem mem_rowMissSet_of_not_intersects
    (Gamma : PseudoGrid G A B X g D P Q) (i : Fin D)
    (j : Gamma.QIndex)
    (hmiss : ¬ pseudoGridIntersectsRow P Gamma.reserved Gamma.qPath i j) :
    j ∈ Gamma.rowMissSet i :=
  (Classical.choose_spec (Gamma.few_qPath_miss_reserved i)).2 j hmiss

/-- The set of `Q'` segments discarded at the start of Section 4.2: the union
of all row-specific miss sets. -/
noncomputable def globalMissSet
    (Gamma : PseudoGrid G A B X g D P Q) : Finset Gamma.QIndex :=
  Finset.univ.biUnion Gamma.rowMissSet

theorem mem_globalMissSet
    (Gamma : PseudoGrid G A B X g D P Q) (j : Gamma.QIndex) :
    j ∈ Gamma.globalMissSet ↔ ∃ i : Fin D, j ∈ Gamma.rowMissSet i := by
  classical
  simp [globalMissSet]

/-- At most `D * (2g^2)` selected `Q'` segments are discarded when all row-bad
sets are unioned. -/
theorem globalMissSet_card_le
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.globalMissSet.card ≤ D * (2 * g ^ 2) := by
  classical
  simpa [globalMissSet, Nat.mul_comm] using
    (Finset.card_biUnion_le_card_mul
      (Finset.univ : Finset (Fin D)) Gamma.rowMissSet (2 * g ^ 2)
      (by
        intro i _hi
        exact Gamma.rowMissSet_card_le i))

/-- The retained subfamily `Q''` from Section 4.2. -/
noncomputable def goodQSet
    (Gamma : PseudoGrid G A B X g D P Q) : Finset Gamma.QIndex :=
  Finset.univ \ Gamma.globalMissSet

theorem mem_goodQSet_iff
    (Gamma : PseudoGrid G A B X g D P Q) (j : Gamma.QIndex) :
    j ∈ Gamma.goodQSet ↔ j ∉ Gamma.globalMissSet := by
  classical
  simp [goodQSet]

/-- Property I1 for the retained family: every path in `Q''` intersects at
least one path in every row `R_i`. -/
theorem goodQSet_intersects_row
    (Gamma : PseudoGrid G A B X g D P Q) {j : Gamma.QIndex}
    (hj : j ∈ Gamma.goodQSet) (i : Fin D) :
    pseudoGridIntersectsRow P Gamma.reserved Gamma.qPath i j := by
  classical
  by_contra hmiss
  have hjrow : j ∈ Gamma.rowMissSet i :=
    Gamma.mem_rowMissSet_of_not_intersects i j hmiss
  have hjglobal : j ∈ Gamma.globalMissSet := by
    exact (Gamma.mem_globalMissSet j).2 ⟨i, hjrow⟩
  exact (Gamma.mem_goodQSet_iff j).1 hj hjglobal

/-- A row is nonempty as soon as there is a retained `Q''` path, because every
retained path intersects the row. -/
theorem reserved_nonempty_of_mem_goodQSet
    (Gamma : PseudoGrid G A B X g D P Q) {j : Gamma.QIndex}
    (hj : j ∈ Gamma.goodQSet) (i : Fin D) :
    (Gamma.reserved i).Nonempty := by
  rcases Gamma.goodQSet_intersects_row hj i with ⟨p, hp, _hintersects⟩
  exact ⟨p, hp⟩

/-- Exact cardinality of the retained family in terms of the global discarded
set. -/
theorem goodQSet_card_eq
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.goodQSet.card =
      Fintype.card Gamma.QIndex - Gamma.globalMissSet.card := by
  classical
  have hsub : Gamma.globalMissSet ⊆ (Finset.univ : Finset Gamma.QIndex) := by
    intro j _hj
    simp
  simpa [goodQSet] using
    (Finset.card_sdiff_of_subset hsub)

/-- If after paying for the row-bad union there is room for `m` paths, then
`Q''` has at least `m` paths. -/
theorem goodQSet_card_lower_bound
    (Gamma : PseudoGrid G A B X g D P Q) {m : ℕ}
    (hcard : Gamma.globalMissSet.card + m ≤ Fintype.card Gamma.QIndex) :
    m ≤ Gamma.goodQSet.card := by
  rw [Gamma.goodQSet_card_eq]
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hcard)

/-- A convenient Section 4.2 form of the preceding bound using the explicit
`D * 2g^2` estimate for discarded paths. -/
theorem goodQSet_card_lower_bound_of_global_bound
    (Gamma : PseudoGrid G A B X g D P Q) {m : ℕ}
    (hcard : D * (2 * g ^ 2) + m ≤ Fintype.card Gamma.QIndex) :
    m ≤ Gamma.goodQSet.card :=
  Gamma.goodQSet_card_lower_bound
    ((Nat.add_le_add_right Gamma.globalMissSet_card_le m).trans hcard)

/-- The same bound with `|Q'| = |P|/4` unfolded. -/
theorem goodQSet_card_lower_bound_of_packing_bound
    (Gamma : PseudoGrid G A B X g D P Q) {m : ℕ}
    (hcard : D * (2 * g ^ 2) + m ≤ P.card / 4) :
    m ≤ Gamma.goodQSet.card := by
  apply Gamma.goodQSet_card_lower_bound_of_global_bound
  simpa [Gamma.q_card_eq] using hcard

/-- The formal first paragraph of Section 4.2: after discarding the union of
all row-bad `Q'` paths, the retained subfamily has the requested lower bound
and satisfies property I1. -/
theorem section42_discard_bad_paths
    (Gamma : PseudoGrid G A B X g D P Q) {m : ℕ}
    (hcard : D * (2 * g ^ 2) + m ≤ Fintype.card Gamma.QIndex) :
    ∃ Qgood : Finset Gamma.QIndex,
      m ≤ Qgood.card ∧
        ∀ j ∈ Qgood, ∀ i : Fin D,
          pseudoGridIntersectsRow P Gamma.reserved Gamma.qPath i j := by
  exact ⟨Gamma.goodQSet,
    Gamma.goodQSet_card_lower_bound_of_global_bound hcard,
    fun j hj i => Gamma.goodQSet_intersects_row hj i⟩

/-- The row linkage `R = ⋃ᵢ R_i` from Section 4.2, as a subpacking of the
original `A`--`B` linkage `P`. -/
noncomputable def rowPacking
    (Gamma : PseudoGrid G A B X g D P Q) : PathPacking G A B :=
  P.toPathPacking.restrictIndexSet Gamma.reservedUnion

/-- The row linkage `R = ⋃ᵢ R_i` as a perfect linkage with terminal sets
`A'` and `B'`, the sources and targets of the selected row paths. -/
noncomputable def rowPerfectPacking
    (Gamma : PseudoGrid G A B X g D P Q) :
    PerfectPathPacking G (P.sourceSet Gamma.reservedUnion)
      (P.targetSet Gamma.reservedUnion) :=
  P.restrictIndexSet Gamma.reservedUnion

@[simp] theorem rowPacking_card
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPacking.card = Gamma.reservedUnion.card := by
  classical
  simp [rowPacking]

/-- Every row-linkage edge is an original `P` edge. -/
theorem rowPacking_edgeSet_subset_P
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPacking.edgeSet ⊆ P.toPathPacking.edgeSet := by
  classical
  intro e he
  rcases (Gamma.rowPacking.mem_edgeSet).1 he with ⟨i, hei⟩
  exact (P.toPathPacking.mem_edgeSet).2
    ⟨i.1, by simpa [rowPacking] using hei⟩

/-- Edges of the unselected part of the original `P` linkage are original
`P` edges. -/
theorem remainingPerfectPacking_edgeSet_subset_P
    (Gamma : PseudoGrid G A B X g D P Q) :
    (P.restrictIndexSet Gamma.remaining).toPathPacking.edgeSet ⊆
      P.toPathPacking.edgeSet :=
  P.restrictIndexSet_edgeSet_subset Gamma.remaining

/-- A row edge cannot also be used by the complementary part of `P`. -/
theorem rowPacking_edge_not_mem_remainingPerfectPacking
    (Gamma : PseudoGrid G A B X g D P Q) {e : Sym2 V}
    (he : e ∈ Gamma.rowPacking.edgeSet) :
    e ∉ (P.restrictIndexSet Gamma.remaining).toPathPacking.edgeSet := by
  classical
  intro hrem
  rcases (Gamma.rowPacking.mem_edgeSet).1 he with ⟨r, her⟩
  rcases ((P.restrictIndexSet Gamma.remaining).toPathPacking.mem_edgeSet).1 hrem with
    ⟨p, hep⟩
  have hpnot : p.1 ∉ Gamma.reservedUnion := by
    have hp : p.1 ∈ pseudoGridRemaining Gamma.reserved := by
      exact p.2
    exact (Finset.mem_sdiff.1 hp).2
  have hne : r.1 ≠ p.1 := by
    intro h
    exact hpnot (by simpa [h] using r.2)
  have hEdgeDisj :
      Disjoint (P.path r.1).edgeSet (P.path p.1).edgeSet :=
    GraphPath.edgeDisjoint_of_nodeDisjoint
      (P.toPathPacking.node_disjoint hne)
  exact Finset.disjoint_left.mp hEdgeDisj
    (by simpa [rowPacking] using her)
    (by simpa using hep)

@[simp] theorem rowPerfectPacking_card
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPacking.card = Gamma.reservedUnion.card := by
  classical
  simp [rowPerfectPacking]

/-- The retained `Q''` subfamily, viewed as a path packing with one endpoint in
`X` and the other endpoint unconstrained.  The formal terminal set on the
unconstrained side is `univ`. -/
noncomputable def goodQPathPacking
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathPacking G Finset.univ X where
  Index := {j : Gamma.QIndex // j ∈ Gamma.goodQSet}
  path := fun j => Gamma.qPath j.1
  connects := by
    intro j
    rcases (Gamma.qPath_exactly_one_endpoint_in_X j.1).1 with hsource | htarget
    · exact Or.inr ⟨hsource, by simp⟩
    · exact Or.inl ⟨by simp, htarget⟩
  node_disjoint := by
    intro i j hij
    exact Gamma.qPath_nodeDisjoint (fun h => hij (Subtype.ext h))

@[simp] theorem goodQPathPacking_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.goodQPathPacking.card = Gamma.goodQSet.card := by
  classical
  simp [goodQPathPacking, PathPacking.card]

/-- Every retained auxiliary edge is an original `Q` edge. -/
theorem goodQPathPacking_edgeSet_subset_Q
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.goodQPathPacking.edgeSet ⊆ Q.toPathPacking.edgeSet := by
  classical
  intro e he
  rcases (Gamma.goodQPathPacking.mem_edgeSet).1 he with ⟨j, hej⟩
  have hejQ :
      e ∈ (Q.path (P.matchedSourceIndex Q (Gamma.parent j.1))).edgeSet :=
    Gamma.qPath_edgeSet_subset_matched j.1 (by
      simpa [goodQPathPacking] using hej)
  exact (Q.toPathPacking.mem_edgeSet).2
    ⟨P.matchedSourceIndex Q (Gamma.parent j.1), hejQ⟩

/-- Property I1 restated for the indexed paths of the retained packing
`Q''`. -/
theorem goodQPathPacking_intersects_row
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPacking.Index) (i : Fin D) :
    pseudoGridIntersectsRow P Gamma.reserved Gamma.qPath i j.1 :=
  Gamma.goodQSet_intersects_row j.2 i

/-- A `P`-path outside the selected rows is disjoint from the whole row
packing. -/
theorem remaining_path_disjoint_rowPacking_vertexSet
    (Gamma : PseudoGrid G A B X g D P Q)
    {p : P.Index} (hp : p ∈ Gamma.remaining) :
    Disjoint (P.path p).vertexSet Gamma.rowPacking.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvRow
  rcases (Gamma.rowPacking.mem_vertexSet).1 hvRow with ⟨r, hvR⟩
  have hpnot : p ∉ Gamma.reservedUnion := by
    change p ∈ pseudoGridRemaining Gamma.reserved at hp
    exact (Finset.mem_sdiff.1 hp).2
  have hpr : p ≠ r.1 := by
    intro h
    apply hpnot
    simp [h, r.2]
  exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hpr)
    hvP (by simpa [rowPacking] using hvR)

/-- A `P`-path outside the selected rows is disjoint from every retained
auxiliary path, hence from the retained auxiliary packing. -/
theorem remaining_path_disjoint_goodQPathPacking_vertexSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {p : P.Index} (hp : p ∈ Gamma.remaining) :
    Disjoint (P.path p).vertexSet Gamma.goodQPathPacking.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvQ
  rcases (Gamma.goodQPathPacking.mem_vertexSet).1 hvQ with ⟨j, hvj⟩
  have hp' : p ∈ pseudoGridRemaining Gamma.reserved := by
    simpa [remaining] using hp
  exact Finset.disjoint_left.mp (Gamma.remaining_disjoint_qPath p hp' j.1)
    hvP (by simpa [goodQPathPacking] using hvj)

/-- A `P`-path outside the selected rows is disjoint from the vertex union used
by `H'`. -/
theorem remaining_path_disjoint_hPrime_vertexUnion
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {p : P.Index} (hp : p ∈ Gamma.remaining) :
    Disjoint (P.path p).vertexSet
      (Gamma.rowPacking.vertexSet ∪ Gamma.goodQPathPacking.vertexSet) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvUnion
  rcases Finset.mem_union.mp hvUnion with hvRow | hvQ
  · exact Finset.disjoint_left.mp
      (Gamma.remaining_path_disjoint_rowPacking_vertexSet hp) hvP hvRow
  · exact Finset.disjoint_left.mp
      (Gamma.remaining_path_disjoint_goodQPathPacking_vertexSet hp) hvP hvQ

/-- The graph `H'` from Section 4.2: the union of the row linkage `R` and the
retained auxiliary family `Q''`. -/
noncomputable def hPrimeGraph
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) : _root_.SimpleGraph V :=
  Gamma.rowPacking.spanningGraph ⊔ Gamma.goodQPathPacking.spanningGraph

theorem hPrimeGraph_le
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.hPrimeGraph ≤ G := by
  intro u v huv
  rw [hPrimeGraph] at huv
  rcases huv with huv | huv
  · exact Gamma.rowPacking.spanningGraph_le huv
  · exact Gamma.goodQPathPacking.spanningGraph_le huv

/-- Every edge of `H'` belongs to the original edge union `E(P) ∪ E(Q)`. -/
theorem hPrimeGraph_edgeSet_subset_pairUnion
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.hPrimeGraph.edgeSet ⊆
      ↑(P.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet) := by
  classical
  intro e he
  rw [hPrimeGraph, _root_.SimpleGraph.edgeSet_sup] at he
  rcases he with heRow | heQ
  · have he' :
        e ∈ (↑Gamma.rowPacking.edgeSet : Set (Sym2 V)) \ Sym2.diagSet := by
      simpa [PathPacking.spanningGraph] using heRow
    exact by
      simp [Gamma.rowPacking_edgeSet_subset_P he'.1]
  · have he' :
        e ∈ (↑Gamma.goodQPathPacking.edgeSet : Set (Sym2 V)) \ Sym2.diagSet := by
      simpa [PathPacking.spanningGraph] using heQ
    exact by
      simp [Gamma.goodQPathPacking_edgeSet_subset_Q he'.1]

/-- Every edge used by a packing in `H' \ e` belongs to the original edge
union `E(P) ∪ E(Q)`. -/
theorem deleteEdges_packing_edgeSet_subset_pairUnion
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (e : Sym2 V)
    {S' T' : Finset V}
    (L : PathPacking (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V))) S' T') :
    L.edgeSet ⊆ P.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet := by
  classical
  intro f hf
  have hfAmbient : f ∈ (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V))).edgeSet :=
    L.edgeSet_subset_edgeSet hf
  rw [_root_.SimpleGraph.edgeSet_deleteEdges] at hfAmbient
  have hfPair := Gamma.hPrimeGraph_edgeSet_subset_pairUnion hfAmbient.1
  simpa using hfPair

/-- No path-packing edge in `H' \ e` is equal to the deleted edge. -/
theorem deleteEdges_packing_not_mem_deleted
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (e : Sym2 V)
    {S' T' : Finset V}
    (L : PathPacking (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V))) S' T') :
    e ∉ L.edgeSet := by
  classical
  intro heL
  have heAmbient : e ∈ (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V))).edgeSet :=
    L.edgeSet_subset_edgeSet heL
  rw [_root_.SimpleGraph.edgeSet_deleteEdges] at heAmbient
  exact heAmbient.2 (by simp)

/-- Sources of selected row paths are vertices of the row packing. -/
theorem sourceSet_subset_rowPacking_vertexSet
    (Gamma : PseudoGrid G A B X g D P Q) :
    P.sourceSet Gamma.reservedUnion ⊆ Gamma.rowPacking.vertexSet := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
  exact (Gamma.rowPacking.mem_vertexSet).2
    ⟨⟨i, hi⟩, GraphPath.source_mem_vertexSet (P.path i)⟩

/-- Targets of selected row paths are vertices of the row packing. -/
theorem targetSet_subset_rowPacking_vertexSet
    (Gamma : PseudoGrid G A B X g D P Q) :
    P.targetSet Gamma.reservedUnion ⊆ Gamma.rowPacking.vertexSet := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
  exact (Gamma.rowPacking.mem_vertexSet).2
    ⟨⟨i, hi⟩, GraphPath.target_mem_vertexSet (P.path i)⟩

/-- A path in `H'` whose target is already in the row/auxiliary vertex union
stays inside that union.  This is the support-control fact behind
Observation 4.3. -/
theorem hPrimeGraph_path_vertexSet_subset
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R : GraphPath Gamma.hPrimeGraph)
    (htarget :
      R.target ∈ Gamma.rowPacking.vertexSet ∪ Gamma.goodQPathPacking.vertexSet) :
    R.vertexSet ⊆ Gamma.rowPacking.vertexSet ∪ Gamma.goodQPathPacking.vertexSet := by
  classical
  refine R.vertexSet_subset_of_edgeSet_vertices
    (Gamma.rowPacking.vertexSet ∪ Gamma.goodQPathPacking.vertexSet) htarget ?_
  intro e he v hv
  have heAmbient : e ∈ Gamma.hPrimeGraph.edgeSet :=
    GraphPath.edgeSet_subset_edgeSet R he
  exact PathPacking.mem_vertexSet_union_of_mem_sup_spanningGraph_edge
    Gamma.rowPacking Gamma.goodQPathPacking
    (by simpa [hPrimeGraph] using heAmbient) hv

/-- A path in `H' \ e` with a row terminal as target stays inside the union of
row vertices and retained auxiliary vertices. -/
theorem hPrimeGraph_deleteEdges_path_vertexSet_subset
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (e : Sym2 V)
    (R : GraphPath (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V))))
    (htarget :
      R.target ∈ P.sourceSet Gamma.reservedUnion ∪
        P.targetSet Gamma.reservedUnion) :
    R.vertexSet ⊆ Gamma.rowPacking.vertexSet ∪ Gamma.goodQPathPacking.vertexSet := by
  classical
  let R' : GraphPath Gamma.hPrimeGraph :=
    R.mapLe (_root_.SimpleGraph.deleteEdges_le ({e} : Set (Sym2 V)))
  have htarget' :
      R'.target ∈ Gamma.rowPacking.vertexSet ∪ Gamma.goodQPathPacking.vertexSet := by
    rcases Finset.mem_union.mp htarget with hsource | htarget
    · exact Finset.mem_union_left _ (Gamma.sourceSet_subset_rowPacking_vertexSet hsource)
    · exact Finset.mem_union_left _ (Gamma.targetSet_subset_rowPacking_vertexSet htarget)
  have hsub := Gamma.hPrimeGraph_path_vertexSet_subset R' htarget'
  simpa [R'] using hsub

/-- A path in `H' \ e` with a row terminal as target is disjoint from every
unselected `P`-path. -/
theorem hPrimeGraph_deleteEdges_path_disjoint_remaining
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (e : Sym2 V)
    (R : GraphPath (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V))))
    (htarget :
      R.target ∈ P.sourceSet Gamma.reservedUnion ∪
        P.targetSet Gamma.reservedUnion)
    {p : P.Index} (hp : p ∈ Gamma.remaining) :
    Disjoint R.vertexSet (P.path p).vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvR hvP
  have hvUnion :=
    Gamma.hPrimeGraph_deleteEdges_path_vertexSet_subset e R htarget hvR
  exact Finset.disjoint_left.mp
    (Gamma.remaining_path_disjoint_hPrime_vertexUnion hp) hvP hvUnion

/-- Each path of an `A'`--`B'` packing in `H' \ e` is disjoint from every
unselected `P`-path. -/
theorem hPrimeGraph_deleteEdges_packing_path_disjoint_remaining
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (e : Sym2 V)
    (L : PathPacking
        (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V)))
        (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion))
    (i : L.Index) {p : P.Index} (hp : p ∈ Gamma.remaining) :
    Disjoint (L.path i).vertexSet (P.path p).vertexSet := by
  classical
  have htarget :
      (L.path i).target ∈ P.sourceSet Gamma.reservedUnion ∪
        P.targetSet Gamma.reservedUnion := by
    rcases L.connects i with h | h
    · exact Finset.mem_union_right _ h.2
    · exact Finset.mem_union_left _ h.2
  exact Gamma.hPrimeGraph_deleteEdges_path_disjoint_remaining e (L.path i)
    htarget hp

/-- The graph `H'` is a subgraph, hence a minor, of the original graph. -/
theorem hPrimeGraph_isMinor
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    IsMinor Gamma.hPrimeGraph G :=
  (IsMinor.refl Gamma.hPrimeGraph).mono Gamma.hPrimeGraph_le

theorem rowPacking_spanningGraph_le_hPrimeGraph
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPacking.spanningGraph ≤ Gamma.hPrimeGraph := by
  simp [hPrimeGraph]

theorem goodQPathPacking_spanningGraph_le_hPrimeGraph
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.goodQPathPacking.spanningGraph ≤ Gamma.hPrimeGraph := by
  simp [hPrimeGraph]

theorem rowPerfectPacking_spanningGraph_le_hPrimeGraph
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPacking.toPathPacking.spanningGraph ≤ Gamma.hPrimeGraph := by
  intro u v huv
  apply Gamma.rowPacking_spanningGraph_le_hPrimeGraph
  simpa [rowPerfectPacking, rowPacking] using huv

/-- The row linkage viewed inside `H'`. -/
noncomputable def rowPackingInHPrime
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathPacking Gamma.hPrimeGraph A B :=
  Gamma.rowPacking.inSpanningGraph.mapLe
    Gamma.rowPacking_spanningGraph_le_hPrimeGraph

@[simp] theorem rowPackingInHPrime_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPackingInHPrime.card = Gamma.rowPacking.card := by
  simp [rowPackingInHPrime]

/-- The row linkage viewed as a perfect linkage inside `H'`, with terminal
sets `A'` and `B'`. -/
noncomputable def rowPerfectPackingInHPrime
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PerfectPathPacking Gamma.hPrimeGraph
      (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion) :=
  Gamma.rowPerfectPacking.inSpanningGraph.mapLe
    Gamma.rowPerfectPacking_spanningGraph_le_hPrimeGraph

@[simp] theorem rowPerfectPackingInHPrime_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPackingInHPrime.card = Gamma.rowPerfectPacking.card := by
  simp [rowPerfectPackingInHPrime]

/-- The graph induced by the vertices of the row linkage inside the row
spanning graph.  This is the vertex-exact support graph needed for the
perfect-linkage property: every ambient vertex lies on a row path. -/
noncomputable def rowSupportGraph
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    _root_.SimpleGraph {v : V // v ∈ Gamma.rowPacking.vertexSet} :=
  Gamma.rowPacking.spanningGraph.induce
    {v : V | v ∈ Gamma.rowPacking.vertexSet}

/-- The row perfect packing's spanning graph is the same row-edge graph as the
row packing's spanning graph, up to the coercion through the perfect-packing
wrapper. -/
theorem rowPerfectPacking_spanningGraph_le_rowPacking_spanningGraph
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPacking.toPathPacking.spanningGraph ≤
      Gamma.rowPacking.spanningGraph := by
  intro u v huv
  simpa [rowPerfectPacking, rowPacking] using huv

/-- The row perfect packing, first viewed in the spanning graph of the selected
row paths.  This named intermediate avoids repeating the same `mapLe`
coercion in the induced row-support graph. -/
noncomputable def rowPerfectPackingInRowSpanningGraph
    (Gamma : PseudoGrid G A B X g D P Q) :
    PerfectPathPacking Gamma.rowPacking.spanningGraph
      (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion) :=
  Gamma.rowPerfectPacking.inSpanningGraph.mapLe
    Gamma.rowPerfectPacking_spanningGraph_le_rowPacking_spanningGraph

@[simp] theorem rowPerfectPackingInRowSpanningGraph_card
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPackingInRowSpanningGraph.card =
      Gamma.rowPerfectPacking.card := by
  simp [rowPerfectPackingInRowSpanningGraph]

/-- Every row path of the row-spanning linkage stays inside the row-packing
vertex set. -/
theorem rowPerfectPackingInRowSpanningGraph_staysIn
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPackingInRowSpanningGraph.toPathPacking.StaysIn
      Gamma.rowPacking.vertexSet := by
  intro r v hv
  exact (Gamma.rowPacking.mem_vertexSet).2
    ⟨r, by
      simpa [rowPerfectPackingInRowSpanningGraph, rowPerfectPacking, rowPacking,
        PerfectPathPacking.mapLe, PerfectPathPacking.inSpanningGraph,
        PathPacking.mapLe, PathPacking.inSpanningGraph, PathPacking.transfer]
        using hv⟩

/-- The source terminal set of the row linkage in the row-support vertex type. -/
noncomputable abbrev rowSupportSourceSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Finset {v : V // v ∈ Gamma.rowPacking.vertexSet} :=
  PathPacking.subtypeFinset (P.sourceSet Gamma.reservedUnion)
    Gamma.rowPacking.vertexSet Gamma.sourceSet_subset_rowPacking_vertexSet

/-- The target terminal set of the row linkage in the row-support vertex type. -/
noncomputable abbrev rowSupportTargetSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Finset {v : V // v ∈ Gamma.rowPacking.vertexSet} :=
  PathPacking.subtypeFinset (P.targetSet Gamma.reservedUnion)
    Gamma.rowPacking.vertexSet Gamma.targetSet_subset_rowPacking_vertexSet

/-- The row linkage viewed in its vertex-exact support graph. -/
noncomputable def rowPerfectPackingInRowSupport
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet := by
  classical
  exact Gamma.rowPerfectPackingInRowSpanningGraph.induce
    Gamma.rowPacking.vertexSet
    Gamma.rowPerfectPackingInRowSpanningGraph_staysIn
    Gamma.sourceSet_subset_rowPacking_vertexSet
    Gamma.targetSet_subset_rowPacking_vertexSet

@[simp] theorem rowPerfectPackingInRowSupport_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPackingInRowSupport.card = Gamma.rowPerfectPacking.card := by
  calc
    Gamma.rowPerfectPackingInRowSupport.card =
        Gamma.rowPerfectPackingInRowSpanningGraph.card := rfl
    _ = Gamma.rowPerfectPacking.card :=
        Gamma.rowPerfectPackingInRowSpanningGraph_card

@[simp] theorem rowPerfectPackingInRowSupport_path_vertexSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    (v : {x : V // x ∈ Gamma.rowPacking.vertexSet}) :
    v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet ↔
      v.1 ∈ (Gamma.rowPacking.path r).vertexSet := by
  classical
  change v ∈
      ((Gamma.rowPerfectPackingInRowSpanningGraph.path r).induce
        Gamma.rowPacking.vertexSet
        (Gamma.rowPerfectPackingInRowSpanningGraph_staysIn r)).vertexSet ↔
      v.1 ∈ (Gamma.rowPacking.path r).vertexSet
  rw [GraphPath.mem_induce_vertexSet]
  simp [rowPerfectPackingInRowSpanningGraph, rowPerfectPacking, rowPacking,
    PerfectPathPacking.mapLe, PerfectPathPacking.inSpanningGraph,
    PathPacking.mapLe, PathPacking.inSpanningGraph, PathPacking.transfer]

/-- The row-support graph is a minor of the original graph: first embed the
induced row-support graph into the row spanning subgraph, then use monotonicity
of minors under adding host edges. -/
theorem rowSupportGraph_isMinor
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    IsMinor Gamma.rowSupportGraph G :=
  (IsMinor.of_embedding
    (_root_.SimpleGraph.Embedding.induce
      ({v : V | v ∈ Gamma.rowPacking.vertexSet}))).mono
    Gamma.rowPacking.spanningGraph_le

/-- In the row-support graph every vertex lies on the row linkage. -/
theorem rowPerfectPackingInRowSupport_spans
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPackingInRowSupport.SpansVertices := by
  classical
  intro v
  rcases (Gamma.rowPacking.mem_vertexSet).1 v.2 with ⟨r, hvr⟩
  exact (Gamma.rowPerfectPackingInRowSupport.toPathPacking.mem_vertexSet).2
    ⟨r, by
      exact (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r v).2 hvr⟩

/-- The selected row containing a vertex of the row-support graph.  The row
linkage paths are vertex-disjoint, so this choice is unique; the uniqueness
lemma below records the usable form. -/
noncomputable def rowSupportVertexRow
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (v : {x : V // x ∈ Gamma.rowPacking.vertexSet}) :
    Gamma.rowPerfectPackingInRowSupport.Index :=
  Classical.choose ((Gamma.rowPacking.mem_vertexSet).1 v.2)

theorem rowSupportVertexRow_mem
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (v : {x : V // x ∈ Gamma.rowPacking.vertexSet}) :
    v ∈
      (Gamma.rowPerfectPackingInRowSupport.path
        (Gamma.rowSupportVertexRow v)).vertexSet := by
  classical
  have hv :
      v.1 ∈
        (Gamma.rowPacking.path (Gamma.rowSupportVertexRow v)).vertexSet :=
    Classical.choose_spec ((Gamma.rowPacking.mem_vertexSet).1 v.2)
  exact (Gamma.rowPerfectPackingInRowSupport_path_vertexSet
    (Gamma.rowSupportVertexRow v) v).2 hv

theorem rowSupportVertexRow_eq_of_mem
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {v : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    {r : Gamma.rowPerfectPackingInRowSupport.Index}
    (hv : v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet) :
    Gamma.rowSupportVertexRow v = r := by
  classical
  by_contra hne
  exact Finset.disjoint_left.mp
    (Gamma.rowPerfectPackingInRowSupport.toPathPacking.node_disjoint hne)
    (Gamma.rowSupportVertexRow_mem v) hv

/-- The concrete key used for the row-support ordering: first an arbitrary
finite row number, then the vertex position on that row path. -/
noncomputable def rowSupportVertexKey
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (v : {x : V // x ∈ Gamma.rowPacking.vertexSet}) : Nat ×ₗ Nat :=
  toLex
    (((Fintype.equivFin Gamma.rowPerfectPackingInRowSupport.Index)
        (Gamma.rowSupportVertexRow v)).val,
      (Gamma.rowPerfectPackingInRowSupport.path
        (Gamma.rowSupportVertexRow v)).vertexIndex v)

theorem rowSupportVertexKey_injective
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Function.Injective Gamma.rowSupportVertexKey := by
  classical
  intro u v hkey
  have hpair :
      (((Fintype.equivFin Gamma.rowPerfectPackingInRowSupport.Index)
          (Gamma.rowSupportVertexRow u)).val,
        (Gamma.rowPerfectPackingInRowSupport.path
          (Gamma.rowSupportVertexRow u)).vertexIndex u) =
      (((Fintype.equivFin Gamma.rowPerfectPackingInRowSupport.Index)
          (Gamma.rowSupportVertexRow v)).val,
        (Gamma.rowPerfectPackingInRowSupport.path
          (Gamma.rowSupportVertexRow v)).vertexIndex v) := by
    simpa [rowSupportVertexKey] using congrArg ofLex hkey
  have hrow :
      Gamma.rowSupportVertexRow u = Gamma.rowSupportVertexRow v := by
    apply (Fintype.equivFin Gamma.rowPerfectPackingInRowSupport.Index).injective
    apply Fin.ext
    exact congrArg Prod.fst hpair
  have hidx :
      (Gamma.rowPerfectPackingInRowSupport.path
        (Gamma.rowSupportVertexRow u)).vertexIndex u =
      (Gamma.rowPerfectPackingInRowSupport.path
        (Gamma.rowSupportVertexRow u)).vertexIndex v := by
    have hidxRaw := congrArg Prod.snd hpair
    simpa [hrow] using hidxRaw
  let Rrow :=
    Gamma.rowPerfectPackingInRowSupport.path (Gamma.rowSupportVertexRow u)
  have hu : u ∈ Rrow.vertexSet := by
    simpa [Rrow] using Gamma.rowSupportVertexRow_mem u
  have hv : v ∈ Rrow.vertexSet := by
    simpa [Rrow, hrow] using Gamma.rowSupportVertexRow_mem v
  have huv : Rrow.Before u v :=
    (Rrow.before_iff_vertexIndex_le).2 ⟨hu, hv, by simpa [Rrow] using hidx.le⟩
  have hvu : Rrow.Before v u :=
    (Rrow.before_iff_vertexIndex_le).2 ⟨hv, hu, by simpa [Rrow] using hidx.ge⟩
  exact Rrow.before_antisymm huv hvu

theorem rowSupportVertexKey_lt_of_before
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {r : Gamma.rowPerfectPackingInRowSupport.Index}
    {u v : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (hu : u ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    (hv : v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    (huv : (Gamma.rowPerfectPackingInRowSupport.path r).Before u v)
    (hne : u ≠ v) :
    Gamma.rowSupportVertexKey u < Gamma.rowSupportVertexKey v := by
  classical
  let Rrow := Gamma.rowPerfectPackingInRowSupport.path r
  have hrowu : Gamma.rowSupportVertexRow u = r :=
    Gamma.rowSupportVertexRow_eq_of_mem hu
  have hrowv : Gamma.rowSupportVertexRow v = r :=
    Gamma.rowSupportVertexRow_eq_of_mem hv
  have hidxle : Rrow.vertexIndex u ≤ Rrow.vertexIndex v :=
    ((Rrow.before_iff_vertexIndex_le).1 (by simpa [Rrow] using huv)).2.2
  have hidxne : Rrow.vertexIndex u ≠ Rrow.vertexIndex v := by
    intro hidx
    have hvu : Rrow.Before v u :=
      (Rrow.before_iff_vertexIndex_le).2
        ⟨by simpa [Rrow] using hv, by simpa [Rrow] using hu, hidx.ge⟩
    exact hne (Rrow.before_antisymm (by simpa [Rrow] using huv) hvu)
  have hidxlt : Rrow.vertexIndex u < Rrow.vertexIndex v :=
    lt_of_le_of_ne hidxle hidxne
  rw [rowSupportVertexKey, rowSupportVertexKey, hrowu, hrowv]
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, hidxlt⟩

/-- The zero-based rank used by the concrete row-support ordering. -/
noncomputable def rowSupportRank
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (v : {x : V // x ∈ Gamma.rowPacking.vertexSet}) : ℕ :=
  PathSlicing.rankByKey Gamma.rowSupportVertexKey Gamma.rowSupportVertexKey_injective v

theorem rowSupportRank_injective
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Function.Injective Gamma.rowSupportRank :=
  PathSlicing.rankByKey_injective
    Gamma.rowSupportVertexKey Gamma.rowSupportVertexKey_injective

theorem rowSupportRank_lt_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (v : {x : V // x ∈ Gamma.rowPacking.vertexSet}) :
    Gamma.rowSupportRank v <
      Fintype.card {x : V // x ∈ Gamma.rowPacking.vertexSet} :=
  PathSlicing.rankByKey_lt_card
    Gamma.rowSupportVertexKey Gamma.rowSupportVertexKey_injective v

theorem rowSupportRank_lt_of_before
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {r : Gamma.rowPerfectPackingInRowSupport.Index}
    {u v : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (hu : u ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    (hv : v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    (huv : (Gamma.rowPerfectPackingInRowSupport.path r).Before u v)
    (hne : u ≠ v) :
    Gamma.rowSupportRank u < Gamma.rowSupportRank v :=
  PathSlicing.rankByKey_lt_of_key_lt
    Gamma.rowSupportVertexKey Gamma.rowSupportVertexKey_injective
    (Gamma.rowSupportVertexKey_lt_of_before hu hv huv hne)

/-- Vertices whose row-support rank is at or above a threshold. -/
noncomputable def rowSupportAboveSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (t : ℕ) :
    Finset {x : V // x ∈ Gamma.rowPacking.vertexSet} := by
  classical
  exact Finset.univ.filter fun v => t ≤ Gamma.rowSupportRank v

@[simp] theorem mem_rowSupportAboveSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (t : ℕ)
    (v : {x : V // x ∈ Gamma.rowPacking.vertexSet}) :
    v ∈ Gamma.rowSupportAboveSet t ↔ t ≤ Gamma.rowSupportRank v := by
  classical
  simp [rowSupportAboveSet]

/-- On a row of the row-support linkage, the threshold vertex is the first
vertex whose global rank is at least `t`, or the target if the row has no such
vertex. -/
noncomputable def rowSupportSeparatorVertex
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (t : ℕ) (r : Gamma.rowPerfectPackingInRowSupport.Index) :
    {x : V // x ∈ Gamma.rowPacking.vertexSet} := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let U := Gamma.rowSupportAboveSet t
  exact
    if hne : (Prow.vertexSet ∩ U).Nonempty then
      Prow.firstHitVertex U hne
    else
      Prow.target

theorem rowSupportSeparatorVertex_mem
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (t : ℕ) (r : Gamma.rowPerfectPackingInRowSupport.Index) :
    Gamma.rowSupportSeparatorVertex t r ∈
      (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let U := Gamma.rowSupportAboveSet t
  by_cases hne : (Prow.vertexSet ∩ U).Nonempty
  · simp [rowSupportSeparatorVertex, Prow, U, hne,
      GraphPath.firstHitVertex_mem_vertexSet]
  · simp [rowSupportSeparatorVertex, Prow, U, hne]

theorem rowSupportSeparatorVertex_above_of_exists
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {t : ℕ} {r : Gamma.rowPerfectPackingInRowSupport.Index}
    (hne :
      ((Gamma.rowPerfectPackingInRowSupport.path r).vertexSet ∩
        Gamma.rowSupportAboveSet t).Nonempty) :
    t ≤ Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex t r) := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let U := Gamma.rowSupportAboveSet t
  have hmem :
      Prow.firstHitVertex U (by simpa [Prow, U] using hne) ∈ U :=
    Prow.firstHitVertex_mem_set U (by simpa [Prow, U] using hne)
  simpa [rowSupportSeparatorVertex, Prow, U, hne] using hmem

theorem rowSupportSeparatorVertex_zero
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index) :
    Gamma.rowSupportSeparatorVertex 0 r =
      (Gamma.rowPerfectPackingInRowSupport.path r).source := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let U := Gamma.rowSupportAboveSet 0
  have hne : (Prow.vertexSet ∩ U).Nonempty := by
    exact ⟨Prow.source, by simp [Prow, U]⟩
  have hfirst_le_source :
      Prow.vertexIndex (Prow.firstHitVertex U hne) ≤
        Prow.vertexIndex Prow.source :=
    (Prow.firstHitVertex_spec U hne).2 Prow.source (by simp [Prow, U])
  have hidx0 :
      Prow.vertexIndex (Prow.firstHitVertex U hne) = 0 := by
    simpa [GraphPath.source_vertexIndex] using hfirst_le_source
  have hfirst_mem : Prow.firstHitVertex U hne ∈ Prow.vertexSet :=
    Prow.firstHitVertex_mem_vertexSet U hne
  have hbefore_source :
      Prow.Before (Prow.firstHitVertex U hne) Prow.source :=
    (Prow.before_iff_vertexIndex_le).2
      ⟨hfirst_mem, GraphPath.source_mem_vertexSet Prow, by simp [hidx0]⟩
  have hsource_before :
      Prow.Before Prow.source (Prow.firstHitVertex U hne) :=
    Prow.source_before_of_mem hfirst_mem
  have hfirst_eq :
      Prow.firstHitVertex U hne = Prow.source :=
    Prow.before_antisymm hbefore_source hsource_before
  simpa [rowSupportSeparatorVertex, Prow, U, hne] using hfirst_eq

theorem rowSupportSeparatorVertex_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index) :
    Gamma.rowSupportSeparatorVertex
        (Fintype.card {x : V // x ∈ Gamma.rowPacking.vertexSet}) r =
      (Gamma.rowPerfectPackingInRowSupport.path r).target := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let U :=
    Gamma.rowSupportAboveSet
      (Fintype.card {x : V // x ∈ Gamma.rowPacking.vertexSet})
  have hne :
      ¬ (Prow.vertexSet ∩ U).Nonempty := by
    rintro ⟨v, hv⟩
    have hvU :
        Fintype.card {x : V // x ∈ Gamma.rowPacking.vertexSet} ≤
          Gamma.rowSupportRank v := by
      simpa [U] using (Finset.mem_inter.1 hv).2
    have hvRank := Gamma.rowSupportRank_lt_card v
    omega
  change (if h : (Prow.vertexSet ∩ U).Nonempty then
      Prow.firstHitVertex U h
    else
      Prow.target) = Prow.target
  rw [dif_neg hne]

theorem rowSupport_below_before_separator
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (t : ℕ) (r : Gamma.rowPerfectPackingInRowSupport.Index)
    {v : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (hv : v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    (hbelow : Gamma.rowSupportRank v < t) :
    (Gamma.rowPerfectPackingInRowSupport.path r).Before v
      (Gamma.rowSupportSeparatorVertex t r) := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let U := Gamma.rowSupportAboveSet t
  by_cases hne : (Prow.vertexSet ∩ U).Nonempty
  · let s := Prow.firstHitVertex U hne
    have hs_mem : s ∈ Prow.vertexSet := Prow.firstHitVertex_mem_vertexSet U hne
    have hs_above : t ≤ Gamma.rowSupportRank s := by
      have hsU : s ∈ U := Prow.firstHitVertex_mem_set U hne
      simpa [U] using hsU
    have hidx_not : ¬ Prow.vertexIndex s < Prow.vertexIndex v := by
      intro hlt
      have hsv : Prow.Before s v :=
        (Prow.before_iff_vertexIndex_le).2 ⟨hs_mem, hv, hlt.le⟩
      have hs_ne_v : s ≠ v := by
        intro hsv_eq
        have hs_rank_eq :
            Gamma.rowSupportRank s = Gamma.rowSupportRank v :=
          congrArg Gamma.rowSupportRank hsv_eq
        omega
      have hrank_lt :
          Gamma.rowSupportRank s < Gamma.rowSupportRank v :=
        Gamma.rowSupportRank_lt_of_before hs_mem hv hsv hs_ne_v
      omega
    have hbefore : Prow.Before v s :=
      (Prow.before_iff_vertexIndex_le).2
        ⟨hv, hs_mem, Nat.le_of_not_gt hidx_not⟩
    simpa [rowSupportSeparatorVertex, Prow, U, hne, s] using hbefore
  · have hbefore_target : Prow.Before v Prow.target :=
      ⟨hv, by
        simpa [GraphPath.dropUntil_target] using
          GraphPath.target_mem_vertexSet (Prow.dropUntil hv)⟩
    simpa [rowSupportSeparatorVertex, Prow, U, hne] using hbefore_target

theorem rowSupport_separator_before_above
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (t : ℕ) (r : Gamma.rowPerfectPackingInRowSupport.Index)
    {v : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (hv : v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    (habove : t ≤ Gamma.rowSupportRank v) :
    (Gamma.rowPerfectPackingInRowSupport.path r).Before
      (Gamma.rowSupportSeparatorVertex t r) v := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let U := Gamma.rowSupportAboveSet t
  have hne : (Prow.vertexSet ∩ U).Nonempty := by
    exact ⟨v, Finset.mem_inter.2 ⟨hv, by simpa [U] using habove⟩⟩
  have hbefore :
      Prow.Before (Prow.firstHitVertex U hne) v :=
    Prow.firstHitVertex_before_of_mem_set U hne hv (by simpa [U] using habove)
  simpa [rowSupportSeparatorVertex, Prow, U, hne] using hbefore

theorem rowSupportSeparatorVertex_monotone
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    {s t : ℕ} (hst : s ≤ t) :
    (Gamma.rowPerfectPackingInRowSupport.path r).Before
      (Gamma.rowSupportSeparatorVertex s r)
      (Gamma.rowSupportSeparatorVertex t r) := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let Ut := Gamma.rowSupportAboveSet t
  by_cases htne : (Prow.vertexSet ∩ Ut).Nonempty
  · have ht_above :
        t ≤ Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex t r) :=
      Gamma.rowSupportSeparatorVertex_above_of_exists (by simpa [Prow, Ut] using htne)
    exact Gamma.rowSupport_separator_before_above s r
      (Gamma.rowSupportSeparatorVertex_mem t r) (hst.trans ht_above)
  · have htarget :
        Gamma.rowSupportSeparatorVertex t r = Prow.target := by
      simp [rowSupportSeparatorVertex, Prow, Ut, htne]
    rw [htarget]
    exact
      ⟨Gamma.rowSupportSeparatorVertex_mem s r, by
        simpa [GraphPath.dropUntil_target] using
          GraphPath.target_mem_vertexSet
            (Prow.dropUntil (Gamma.rowSupportSeparatorVertex_mem s r))⟩

/-- The finite threshold separator in the row-support ordering. -/
noncomputable def rowSupportSeparatorSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (t : ℕ) :
    Finset {x : V // x ∈ Gamma.rowPacking.vertexSet} := by
  classical
  exact Finset.univ.image fun r : Gamma.rowPerfectPackingInRowSupport.Index =>
    Gamma.rowSupportSeparatorVertex t r

theorem rowSupportSeparatorSet_eq
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (t : ℕ) :
    Gamma.rowSupportSeparatorSet t =
      Finset.univ.image fun r : Gamma.rowPerfectPackingInRowSupport.Index =>
        Gamma.rowSupportSeparatorVertex t r := rfl

theorem rowSupportSeparatorVertex_mem_separatorSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (t : ℕ) (r : Gamma.rowPerfectPackingInRowSupport.Index) :
    Gamma.rowSupportSeparatorVertex t r ∈
      Gamma.rowSupportSeparatorSet t := by
  classical
  rw [Gamma.rowSupportSeparatorSet_eq t]
  exact Finset.mem_image.2 ⟨r, by simp, rfl⟩

theorem rowSupportSeparatorSet_card_le
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (t : ℕ) :
    (Gamma.rowSupportSeparatorSet t).card ≤
      Gamma.rowPerfectPackingInRowSupport.card := by
  classical
  rw [Gamma.rowSupportSeparatorSet_eq t]
  calc
    (Finset.univ.image fun r : Gamma.rowPerfectPackingInRowSupport.Index =>
        Gamma.rowSupportSeparatorVertex t r).card
        ≤ (Finset.univ : Finset Gamma.rowPerfectPackingInRowSupport.Index).card :=
          Finset.card_image_le
    _ = Gamma.rowPerfectPackingInRowSupport.card := rfl

theorem rowSupportSeparatorVertex_rank_ge_or_eq
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {s t : ℕ} (hst : s ≤ t)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    (hne :
      Gamma.rowSupportSeparatorVertex t r ≠
        Gamma.rowSupportSeparatorVertex s r) :
    s ≤ Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex t r) := by
  classical
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let Us := Gamma.rowSupportAboveSet s
  by_cases hsne : (Prow.vertexSet ∩ Us).Nonempty
  · have hs_above :
        s ≤ Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex s r) :=
      Gamma.rowSupportSeparatorVertex_above_of_exists (by simpa [Prow, Us] using hsne)
    have hbefore :=
      Gamma.rowSupportSeparatorVertex_monotone r hst
    have hlt :
        Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex s r) <
          Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex t r) :=
      Gamma.rowSupportRank_lt_of_before
        (Gamma.rowSupportSeparatorVertex_mem s r)
        (Gamma.rowSupportSeparatorVertex_mem t r)
        hbefore hne.symm
    exact hs_above.trans hlt.le
  · have hsep_s :
        Gamma.rowSupportSeparatorVertex s r = Prow.target := by
      simp [rowSupportSeparatorVertex, Prow, Us, hsne]
    have ht_no :
        ¬ (Prow.vertexSet ∩ Gamma.rowSupportAboveSet t).Nonempty := by
      intro htne
      apply hsne
      rcases htne with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      rcases Finset.mem_inter.1 hv with ⟨hvP, hvU⟩
      exact Finset.mem_inter.2
        ⟨hvP, by
          have htv : t ≤ Gamma.rowSupportRank v := by simpa using hvU
          simpa [Us] using hst.trans htv⟩
    have hsep_t :
        Gamma.rowSupportSeparatorVertex t r = Prow.target := by
      simp [rowSupportSeparatorVertex, Prow, ht_no]
    exact False.elim (hne (hsep_t.trans hsep_s.symm))

theorem rowSupportSeparatorSet_subset_separator_union_above
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {s t : ℕ} (hst : s ≤ t) :
    Gamma.rowSupportSeparatorSet t ⊆
      Gamma.rowSupportSeparatorSet s ∪
        (Finset.univ.filter fun v :
          {x : V // x ∈ Gamma.rowPacking.vertexSet} =>
            s ≤ Gamma.rowSupportRank v) := by
  classical
  intro v hv
  rw [Gamma.rowSupportSeparatorSet_eq t] at hv
  rcases Finset.mem_image.1 hv with ⟨r, _hr, rfl⟩
  by_cases hsame :
      Gamma.rowSupportSeparatorVertex t r =
        Gamma.rowSupportSeparatorVertex s r
  · exact Finset.mem_union_left _
      (by
        rw [hsame]
        exact Gamma.rowSupportSeparatorVertex_mem_separatorSet s r)
  · exact Finset.mem_union_right _
      (by
        simp [Gamma.rowSupportSeparatorVertex_rank_ge_or_eq hst r hsame])

theorem rowSupportSeparatorSet_sdiff_succ_subset_rankLevel
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {t : ℕ}
    (_ht : t < Fintype.card {x : V // x ∈ Gamma.rowPacking.vertexSet}) :
    Gamma.rowSupportSeparatorSet t \ Gamma.rowSupportSeparatorSet (t + 1) ⊆
      (Finset.univ.filter fun v :
        {x : V // x ∈ Gamma.rowPacking.vertexSet} =>
          Gamma.rowSupportRank v = t) := by
  classical
  intro v hv
  rcases Finset.mem_sdiff.1 hv with ⟨hvSep, hvNotSucc⟩
  rw [Gamma.rowSupportSeparatorSet_eq t] at hvSep
  rcases Finset.mem_image.1 hvSep with ⟨r, _hr, rfl⟩
  have hge : t ≤ Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex t r) := by
    by_contra hnot
    have hno :
        ¬ ((Gamma.rowPerfectPackingInRowSupport.path r).vertexSet ∩
          Gamma.rowSupportAboveSet t).Nonempty := by
      intro hne
      exact hnot (Gamma.rowSupportSeparatorVertex_above_of_exists hne)
    have hsep_t :
        Gamma.rowSupportSeparatorVertex t r =
          (Gamma.rowPerfectPackingInRowSupport.path r).target := by
      simp [rowSupportSeparatorVertex, hno]
    have hnoSucc :
        ¬ ((Gamma.rowPerfectPackingInRowSupport.path r).vertexSet ∩
          Gamma.rowSupportAboveSet (t + 1)).Nonempty := by
      rintro ⟨x, hx⟩
      have hxAboveSucc : t + 1 ≤ Gamma.rowSupportRank x := by
        simpa using (Finset.mem_inter.1 hx).2
      apply hno
      exact ⟨x, Finset.mem_inter.2
        ⟨(Finset.mem_inter.1 hx).1,
          by
            have hxAbove : t ≤ Gamma.rowSupportRank x :=
              (Nat.le_succ t).trans hxAboveSucc
            simpa using hxAbove⟩⟩
    have hsep_succ :
        Gamma.rowSupportSeparatorVertex (t + 1) r =
          (Gamma.rowPerfectPackingInRowSupport.path r).target := by
      simp [rowSupportSeparatorVertex, hnoSucc]
    have hmemSucc :=
      Gamma.rowSupportSeparatorVertex_mem_separatorSet (t + 1) r
    rw [hsep_succ, ← hsep_t] at hmemSucc
    exact hvNotSucc hmemSucc
  have hle : Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex t r) ≤ t := by
    by_contra hnot
    have hsucc :
        t + 1 ≤ Gamma.rowSupportRank (Gamma.rowSupportSeparatorVertex t r) := by
      omega
    have hbefore1 :=
      Gamma.rowSupportSeparatorVertex_monotone r (Nat.le_succ t)
    have hbefore2 :
        (Gamma.rowPerfectPackingInRowSupport.path r).Before
          (Gamma.rowSupportSeparatorVertex (t + 1) r)
          (Gamma.rowSupportSeparatorVertex t r) :=
      Gamma.rowSupport_separator_before_above (t + 1) r
        (Gamma.rowSupportSeparatorVertex_mem t r) hsucc
    have heq :
        Gamma.rowSupportSeparatorVertex t r =
          Gamma.rowSupportSeparatorVertex (t + 1) r :=
      (Gamma.rowPerfectPackingInRowSupport.path r).before_antisymm
        hbefore1 hbefore2
    have hmemSucc :=
      Gamma.rowSupportSeparatorVertex_mem_separatorSet (t + 1) r
    rw [← heq] at hmemSucc
    exact hvNotSucc hmemSucc
  simp [le_antisymm hle hge]

/-- A walk in the row-support graph that starts on one selected row path stays
on that row path.  The row-support graph has only the row-linkage edges, and
the selected row paths are vertex-disjoint. -/
theorem rowSupportGraph_walk_support_subset_row
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (r : Gamma.rowPacking.Index)
    {s t : {v : V // v ∈ Gamma.rowPacking.vertexSet}}
    (W : Gamma.rowSupportGraph.Walk s t)
    (hs : s.1 ∈ (Gamma.rowPacking.path r).vertexSet) :
    ∀ v ∈ W.support, v.1 ∈ (Gamma.rowPacking.path r).vertexSet := by
  induction W with
  | nil =>
      intro v hv
      have hv_eq := by
        simpa using hv
      simpa [hv_eq] using hs
  | @cons u v w h W ih =>
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact hs
      · exact ih (by
          have hadj : Gamma.rowPacking.spanningGraph.Adj u.1 v.1 := by
            simpa [rowSupportGraph] using h
          exact Gamma.rowPacking.mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet
            hs hadj) x hx

/-- A path in the row-support graph that starts on one selected row path stays
on that row path. -/
theorem rowSupportGraph_path_vertexSet_subset_row
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (r : Gamma.rowPacking.Index)
    (Z : GraphPath Gamma.rowSupportGraph)
    (hs : Z.source.1 ∈ (Gamma.rowPacking.path r).vertexSet) :
    ∀ v ∈ Z.vertexSet, v.1 ∈ (Gamma.rowPacking.path r).vertexSet := by
  intro v hv
  have hvSupport : v ∈ Z.walk.support := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.vertexSet] using hv)
  exact Gamma.rowSupportGraph_walk_support_subset_row r Z.walk hs v hvSupport

/-- A path in the row-support graph that starts on one row of the induced
row linkage stays on that row, stated directly for the induced linkage paths.
-/
theorem rowSupportGraph_path_vertexSet_subset_rowSupport
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    (Z : GraphPath Gamma.rowSupportGraph)
    (hs : Z.source ∈
      (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet) :
    ∀ v ∈ Z.vertexSet,
      v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet := by
  intro v hv
  have hsBase :
      Z.source.1 ∈ (Gamma.rowPacking.path r).vertexSet :=
    (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r Z.source).1 hs
  exact (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r v).2
    (Gamma.rowSupportGraph_path_vertexSet_subset_row r Z hsBase v hv)

/-- Adjacency in the row-support graph is exactly adjacency along one of the
selected row paths, with endpoints coerced to the original vertex type. -/
theorem rowSupportGraph_adj_iff_exists_row_edge
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {u v : {x : V // x ∈ Gamma.rowPacking.vertexSet}} :
    Gamma.rowSupportGraph.Adj u v ↔
      (∃ r : Gamma.rowPacking.Index,
        s(u.1, v.1) ∈ (Gamma.rowPacking.path r).edgeSet) ∧ u ≠ v := by
  classical
  change Gamma.rowPacking.spanningGraph.Adj u.1 v.1 ↔
      (∃ r : Gamma.rowPacking.Index,
        s(u.1, v.1) ∈ (Gamma.rowPacking.path r).edgeSet) ∧ u ≠ v
  rw [Gamma.rowPacking.spanningGraph_adj_iff_exists_path_edge]
  constructor
  · rintro ⟨hrow, huv⟩
    exact ⟨hrow, fun h => huv (Subtype.ext_iff.mp h)⟩
  · rintro ⟨hrow, huv⟩
    exact ⟨hrow, fun h => huv (Subtype.ext h)⟩

/-- Every edge of the row-support graph is one of the edges of the induced row
linkage. -/
theorem rowSupportGraph_adj_mem_rowPerfectPackingInRowSupport_edgeSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {u v : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (huv : Gamma.rowSupportGraph.Adj u v) :
    s(u, v) ∈ Gamma.rowPerfectPackingInRowSupport.toPathPacking.edgeSet := by
  classical
  rcases (Gamma.rowSupportGraph_adj_iff_exists_row_edge).1 huv with
    ⟨⟨r, he⟩, _hne⟩
  have hePath :
      s(u, v) ∈ (Gamma.rowPerfectPackingInRowSupport.path r).edgeSet := by
    change s(u, v) ∈
      ((Gamma.rowPerfectPackingInRowSpanningGraph.path r).induce
        Gamma.rowPacking.vertexSet
        (Gamma.rowPerfectPackingInRowSpanningGraph_staysIn r)).edgeSet
    rw [GraphPath.mem_induce_edgeSet]
    simpa [Sym2.map_mk, rowPerfectPackingInRowSpanningGraph, rowPerfectPacking,
      rowPacking, PerfectPathPacking.mapLe, PerfectPathPacking.inSpanningGraph,
      PathPacking.mapLe, PathPacking.inSpanningGraph, PathPacking.transfer] using he
  exact (Gamma.rowPerfectPackingInRowSupport.toPathPacking.mem_edgeSet).2
    ⟨r, hePath⟩

/-- If a row-support edge is incident with a vertex of row `r`, then it is an
edge of the induced copy of that same row path. -/
theorem rowSupportGraph_adj_mem_rowPerfectPackingInRowSupport_path_edgeSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    {u v : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (hu : u ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    (huv : Gamma.rowSupportGraph.Adj u v) :
    s(u, v) ∈ (Gamma.rowPerfectPackingInRowSupport.path r).edgeSet := by
  classical
  have hu_row :
      u.1 ∈ (Gamma.rowPacking.path r).vertexSet :=
    (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r u).1 hu
  rcases (Gamma.rowSupportGraph_adj_iff_exists_row_edge).1 huv with
    ⟨⟨r', he'⟩, _hne⟩
  have heWalk' : s(u.1, v.1) ∈ (Gamma.rowPacking.path r').walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using he')
  have hu_row' :
      u.1 ∈ (Gamma.rowPacking.path r').vertexSet := by
    have huSupport :
        u.1 ∈ (Gamma.rowPacking.path r').walk.support :=
      (Gamma.rowPacking.path r').walk.fst_mem_support_of_mem_edges heWalk'
    simpa [GraphPath.vertexSet] using huSupport
  have hrr' : r' = r := by
    by_contra hne
    exact Finset.disjoint_left.mp (Gamma.rowPacking.node_disjoint hne)
      hu_row' hu_row
  have heRow :
      s(u.1, v.1) ∈ (Gamma.rowPacking.path r).edgeSet := by
    simpa [hrr'] using he'
  change s(u, v) ∈
    ((Gamma.rowPerfectPackingInRowSpanningGraph.path r).induce
      Gamma.rowPacking.vertexSet
      (Gamma.rowPerfectPackingInRowSpanningGraph_staysIn r)).edgeSet
  rw [GraphPath.mem_induce_edgeSet]
  simpa [Sym2.map_mk, rowPerfectPackingInRowSpanningGraph, rowPerfectPacking,
    rowPacking, PerfectPathPacking.mapLe, PerfectPathPacking.inSpanningGraph,
    PathPacking.mapLe, PathPacking.inSpanningGraph, PathPacking.transfer] using heRow

/-- Every path in the row-support graph uses only row-linkage edges. -/
theorem rowSupportGraph_path_edgeSet_subset_rowPerfectPackingInRowSupport
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (Z : GraphPath Gamma.rowSupportGraph) :
    Z.edgeSet ⊆ Gamma.rowPerfectPackingInRowSupport.toPathPacking.edgeSet := by
  classical
  intro e he
  induction e using Sym2.ind with
  | h u v =>
      have heWalk : s(u, v) ∈ Z.walk.edges := by
        have heFin : s(u, v) ∈ Z.walk.edges.toFinset := by
          simpa [GraphPath.edgeSet] using he
        exact List.mem_toFinset.1 heFin
      exact Gamma.rowSupportGraph_adj_mem_rowPerfectPackingInRowSupport_edgeSet
        (Z.walk.adj_of_mem_edges heWalk)

/-- Any path packing in the row-support graph has edge set contained in the row
linkage edge set. -/
theorem rowSupportGraph_packing_edgeSet_subset_rowPerfectPackingInRowSupport
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {S T : Finset {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (L : PathPacking Gamma.rowSupportGraph S T) :
    L.edgeSet ⊆ Gamma.rowPerfectPackingInRowSupport.toPathPacking.edgeSet := by
  classical
  intro e he
  rcases (L.mem_edgeSet).1 he with ⟨i, hei⟩
  exact Gamma.rowSupportGraph_path_edgeSet_subset_rowPerfectPackingInRowSupport
    (L.path i) hei

/-- A row-support path that starts on row `r` uses only the induced edge set of
that row. -/
theorem rowSupportGraph_path_edgeSet_subset_row
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    (Z : GraphPath Gamma.rowSupportGraph)
    (hs : Z.source ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet) :
    Z.edgeSet ⊆ (Gamma.rowPerfectPackingInRowSupport.path r).edgeSet := by
  classical
  intro e he
  induction e using Sym2.ind with
  | h u v =>
      have heWalk : s(u, v) ∈ Z.walk.edges := by
        exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using he)
      have huZ : u ∈ Z.vertexSet := by
        have huSupport : u ∈ Z.walk.support :=
          Z.walk.fst_mem_support_of_mem_edges heWalk
        simpa [GraphPath.vertexSet] using huSupport
      have huRow : u ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet := by
        have huBase :
            u.1 ∈ (Gamma.rowPacking.path r).vertexSet :=
          Gamma.rowSupportGraph_path_vertexSet_subset_row r Z
            ((Gamma.rowPerfectPackingInRowSupport_path_vertexSet r Z.source).1 hs)
            u huZ
        exact (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r u).2 huBase
      exact Gamma.rowSupportGraph_adj_mem_rowPerfectPackingInRowSupport_path_edgeSet
        r huRow (Z.walk.adj_of_mem_edges heWalk)

/-- Along any walk in the row-support graph that starts on row `r`, the
position on row `r` can increase by at most the length of the walk. -/
theorem rowSupportGraph_walk_row_vertexIndex_le
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    {s t : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (W : Gamma.rowSupportGraph.Walk s t)
    (hs : s ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet) :
    (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex t ≤
      (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex s + W.length := by
  classical
  induction W with
  | nil =>
      simp
  | @cons u v w huv W ih =>
      have he :
          s(u, v) ∈ (Gamma.rowPerfectPackingInRowSupport.path r).edgeSet :=
        Gamma.rowSupportGraph_adj_mem_rowPerfectPackingInRowSupport_path_edgeSet
          r hs huv
      have hv :
          v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet := by
        have hvWalk :
            v.1 ∈ (Gamma.rowPacking.path r).vertexSet :=
          Gamma.rowPacking.mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet
            ((Gamma.rowPerfectPackingInRowSupport_path_vertexSet r u).1 hs)
            (by simpa [rowSupportGraph] using huv)
        exact (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r v).2 hvWalk
      have hstep :
          (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex v ≤
            (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex u + 1 :=
        GraphPath.edge_vertexIndex_le_succ
          (Gamma.rowPerfectPackingInRowSupport.path r) he
      have htail :
          (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex w ≤
            (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex v + W.length :=
        ih hv
      calc
        (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex w
            ≤ (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex v +
                W.length := htail
        _ ≤ ((Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex u + 1) +
                W.length := Nat.add_le_add_right hstep W.length
        _ = (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex u +
                (SimpleGraph.Walk.cons huv W).length := by
              simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A walk in the row-support graph from a vertex at row-index at most `k` to
a vertex at row-index at least `k` visits a vertex of row-index exactly `k`.

This is the discrete intermediate-value fact for a path graph.  Each
row-support edge is an edge of the chosen row path, hence its row index can
increase by at most one in a single step. -/
theorem rowSupportGraph_walk_contains_row_vertexIndex
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    {s t : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (W : Gamma.rowSupportGraph.Walk s t)
    (hs : s ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    {k : ℕ}
    (hsk : (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex s ≤ k)
    (hkt : k ≤ (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex t) :
    ∃ v,
      v ∈ W.support ∧
        v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet ∧
          (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex v = k := by
  classical
  induction W with
  | nil =>
      have hk :
          (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex _ = k :=
        le_antisymm hsk hkt
      exact ⟨_, by simp, hs, hk⟩
  | @cons u v w huv W ih =>
      by_cases huk :
          (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex u = k
      · exact ⟨u, by simp, hs, huk⟩
      · have hu_lt :
            (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex u < k :=
          lt_of_le_of_ne hsk huk
        have he :
            s(u, v) ∈
              (Gamma.rowPerfectPackingInRowSupport.path r).edgeSet :=
          Gamma.rowSupportGraph_adj_mem_rowPerfectPackingInRowSupport_path_edgeSet
            r hs huv
        have hvRow :
            v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet := by
          have hvBase :
              v.1 ∈ (Gamma.rowPacking.path r).vertexSet :=
            Gamma.rowPacking.mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet
              ((Gamma.rowPerfectPackingInRowSupport_path_vertexSet r u).1 hs)
              (by simpa [rowSupportGraph] using huv)
          exact (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r v).2 hvBase
        have hv_le :
            (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex v ≤ k := by
          have hstep :
              (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex v ≤
                (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex u + 1 :=
            GraphPath.edge_vertexIndex_le_succ
              (Gamma.rowPerfectPackingInRowSupport.path r) he
          omega
        rcases ih hvRow hv_le hkt with ⟨x, hxW, hxRow, hxidx⟩
        exact ⟨x, by simp [hxW], hxRow, hxidx⟩

/-- Path form of `rowSupportGraph_walk_contains_row_vertexIndex`. -/
theorem rowSupportGraph_path_contains_row_vertexIndex
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    (Z : GraphPath Gamma.rowSupportGraph)
    (hs : Z.source ∈
      (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet)
    {k : ℕ}
    (hsk : (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex Z.source ≤ k)
    (hkt : k ≤ (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex Z.target) :
    ∃ v,
      v ∈ Z.vertexSet ∧
        v ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet ∧
          (Gamma.rowPerfectPackingInRowSupport.path r).vertexIndex v = k := by
  rcases Gamma.rowSupportGraph_walk_contains_row_vertexIndex r Z.walk hs hsk hkt
    with ⟨v, hvSupport, hvRow, hvidx⟩
  exact ⟨v, by simpa [GraphPath.vertexSet] using List.mem_toFinset.2 hvSupport,
    hvRow, hvidx⟩

/-- A row-support path containing one vertex below a threshold and one vertex
above it contains the selected threshold vertex of that row. -/
theorem rowSupportGraph_path_contains_separator_of_rank_crossing
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (t : ℕ)
    (Z : GraphPath Gamma.rowSupportGraph)
    {y z : {x : V // x ∈ Gamma.rowPacking.vertexSet}}
    (hyZ : y ∈ Z.vertexSet) (hzZ : z ∈ Z.vertexSet)
    (hyRank : Gamma.rowSupportRank y < t)
    (hzRank : t ≤ Gamma.rowSupportRank z) :
    ∃ v, v ∈ Z.vertexSet ∧ v ∈ Gamma.rowSupportSeparatorSet t := by
  classical
  let r := Gamma.rowSupportVertexRow y
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  let sep := Gamma.rowSupportSeparatorVertex t r
  have hyRow : y ∈ Prow.vertexSet := by
    simpa [Prow, r] using Gamma.rowSupportVertexRow_mem y
  have hsepMem : sep ∈ Prow.vertexSet := by
    simpa [sep, Prow] using Gamma.rowSupportSeparatorVertex_mem t r
  have horder : Z.Before y z ∨ Z.Before z y := by
    rcases le_total (Z.vertexIndex y) (Z.vertexIndex z) with hyz | hzy
    · exact Or.inl ((Z.before_iff_vertexIndex_le).2 ⟨hyZ, hzZ, hyz⟩)
    · exact Or.inr ((Z.before_iff_vertexIndex_le).2 ⟨hzZ, hyZ, hzy⟩)
  rcases horder with hyz | hzy
  · let YZ := Z.segmentOfBefore hyz
    have hsourceRow : YZ.source ∈ Prow.vertexSet := by
      simpa [YZ, Prow] using hyRow
    have hzRow : z ∈ Prow.vertexSet := by
      have htargetRow :=
        Gamma.rowSupportGraph_path_vertexSet_subset_rowSupport r YZ hsourceRow
          YZ.target (GraphPath.target_mem_vertexSet YZ)
      simpa [YZ, Prow] using htargetRow
    have hy_before_sep : Prow.Before y sep := by
      simpa [Prow, sep] using
        Gamma.rowSupport_below_before_separator t r hyRow hyRank
    have hsep_before_z : Prow.Before sep z := by
      simpa [Prow, sep] using
        Gamma.rowSupport_separator_before_above t r hzRow hzRank
    have hy_idx :
        Prow.vertexIndex y ≤ Prow.vertexIndex sep :=
      ((Prow.before_iff_vertexIndex_le).1 hy_before_sep).2.2
    have hz_idx :
        Prow.vertexIndex sep ≤ Prow.vertexIndex z :=
      ((Prow.before_iff_vertexIndex_le).1 hsep_before_z).2.2
    rcases Gamma.rowSupportGraph_path_contains_row_vertexIndex
        r YZ hsourceRow (k := Prow.vertexIndex sep)
        (by simpa [YZ, Prow] using hy_idx)
        (by simpa [YZ, Prow] using hz_idx) with
      ⟨v, hvYZ, hvRow, hvIdx⟩
    have hv_eq_sep : v = sep := by
      have hvIdx' : Prow.vertexIndex v = Prow.vertexIndex sep := by
        simpa [Prow] using hvIdx
      have hv_before_sep : Prow.Before v sep :=
        (Prow.before_iff_vertexIndex_le).2
          ⟨by simpa [Prow] using hvRow, hsepMem, hvIdx'.le⟩
      have hsep_before_v : Prow.Before sep v :=
        (Prow.before_iff_vertexIndex_le).2
          ⟨hsepMem, by simpa [Prow] using hvRow, hvIdx'.ge⟩
      exact Prow.before_antisymm hv_before_sep hsep_before_v
    refine ⟨v, ?_, ?_⟩
    · exact Z.segmentOfBefore_vertexSet_subset hyz hvYZ
    · rw [hv_eq_sep]
      simpa [sep] using Gamma.rowSupportSeparatorVertex_mem_separatorSet t r
  · let ZY := Z.segmentOfBefore hzy
    let YZ := ZY.reverse
    have hsourceRow : YZ.source ∈ Prow.vertexSet := by
      simpa [YZ, ZY, Prow] using hyRow
    have hzRow : z ∈ Prow.vertexSet := by
      have htargetRow :=
        Gamma.rowSupportGraph_path_vertexSet_subset_rowSupport r YZ hsourceRow
          YZ.target (GraphPath.target_mem_vertexSet YZ)
      simpa [YZ, ZY, Prow] using htargetRow
    have hy_before_sep : Prow.Before y sep := by
      simpa [Prow, sep] using
        Gamma.rowSupport_below_before_separator t r hyRow hyRank
    have hsep_before_z : Prow.Before sep z := by
      simpa [Prow, sep] using
        Gamma.rowSupport_separator_before_above t r hzRow hzRank
    have hy_idx :
        Prow.vertexIndex y ≤ Prow.vertexIndex sep :=
      ((Prow.before_iff_vertexIndex_le).1 hy_before_sep).2.2
    have hz_idx :
        Prow.vertexIndex sep ≤ Prow.vertexIndex z :=
      ((Prow.before_iff_vertexIndex_le).1 hsep_before_z).2.2
    rcases Gamma.rowSupportGraph_path_contains_row_vertexIndex
        r YZ hsourceRow (k := Prow.vertexIndex sep)
        (by simpa [YZ, ZY, Prow] using hy_idx)
        (by simpa [YZ, ZY, Prow] using hz_idx) with
      ⟨v, hvYZ, hvRow, hvIdx⟩
    have hv_eq_sep : v = sep := by
      have hvIdx' : Prow.vertexIndex v = Prow.vertexIndex sep := by
        simpa [Prow] using hvIdx
      have hv_before_sep : Prow.Before v sep :=
        (Prow.before_iff_vertexIndex_le).2
          ⟨by simpa [Prow] using hvRow, hsepMem, hvIdx'.le⟩
      have hsep_before_v : Prow.Before sep v :=
        (Prow.before_iff_vertexIndex_le).2
          ⟨hsepMem, by simpa [Prow] using hvRow, hvIdx'.ge⟩
      exact Prow.before_antisymm hv_before_sep hsep_before_v
    refine ⟨v, ?_, ?_⟩
    · have hvZY : v ∈ ZY.vertexSet := by
        simpa [YZ] using hvYZ
      exact Z.segmentOfBefore_vertexSet_subset hzy hvZY
    · rw [hv_eq_sep]
      simpa [sep] using Gamma.rowSupportSeparatorVertex_mem_separatorSet t r

/-- The concrete row-support ordering satisfies the separator-blocking
property required in the Robertson--Seymour linkage ordering. -/
theorem rowSupport_separator_blocks
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (t : ℕ) (Z : GraphPath Gamma.rowSupportGraph)
    (hcross :
      PathSlicing.GraphPathCrossesRankThreshold
        Gamma.rowSupportRank t Z) :
    ∃ v ∈ Z.vertexSet, v ∈ Gamma.rowSupportSeparatorSet t := by
  rcases hcross with ⟨y, hyZ, z, hzZ, hyRank, hzRank⟩
  exact Gamma.rowSupportGraph_path_contains_separator_of_rank_crossing
    t Z hyZ hzZ hyRank hzRank

/-- The concrete Robertson--Seymour ordering for the row-support linkage of a
pseudo-grid.

Rows are ordered by an arbitrary finite row order, and vertices within each
row are ordered by their position on the row path.  Since the row-support graph
is exactly the disjoint union of the selected row paths, the threshold
separator consisting of one selected vertex per row blocks every path crossing
the threshold. -/
noncomputable def rowSupportLinkageOrdering
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathSlicing.LinkageOrdering Gamma.rowPerfectPackingInRowSupport where
  rank := Gamma.rowSupportRank
  rank_injective := Gamma.rowSupportRank_injective
  rank_lt_card := Gamma.rowSupportRank_lt_card
  row_strict := by
    intro r u v hu hv huv hne
    exact Gamma.rowSupportRank_lt_of_before hu hv huv hne
  separatorVertex := Gamma.rowSupportSeparatorVertex
  separatorVertex_mem := Gamma.rowSupportSeparatorVertex_mem
  separatorVertex_zero := Gamma.rowSupportSeparatorVertex_zero
  separatorVertex_card := Gamma.rowSupportSeparatorVertex_card
  below_before_separator := Gamma.rowSupport_below_before_separator
  separator_before_above := Gamma.rowSupport_separator_before_above
  separatorVertex_monotone := Gamma.rowSupportSeparatorVertex_monotone
  separatorSet := Gamma.rowSupportSeparatorSet
  separatorSet_eq := Gamma.rowSupportSeparatorSet_eq
  separatorSet_subset_separator_union_above := by
    intro s t hst
    exact Gamma.rowSupportSeparatorSet_subset_separator_union_above hst
  separatorSet_sdiff_succ_subset_rankLevel := by
    intro t ht
    exact Gamma.rowSupportSeparatorSet_sdiff_succ_subset_rankLevel ht
  separator_card_le := Gamma.rowSupportSeparatorSet_card_le
  separator_blocks := Gamma.rowSupport_separator_blocks

/-- A path in the row-support graph from the source of row `r` to the target
of row `r` is at least as long as the row path itself. -/
theorem rowSupportGraph_path_length_ge_row
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (r : Gamma.rowPerfectPackingInRowSupport.Index)
    (Z : GraphPath Gamma.rowSupportGraph)
    (hsrc : Z.source = (Gamma.rowPerfectPackingInRowSupport.path r).source)
    (htgt : Z.target = (Gamma.rowPerfectPackingInRowSupport.path r).target) :
    (Gamma.rowPerfectPackingInRowSupport.path r).walk.length ≤ Z.walk.length := by
  classical
  have hsource_mem :
      Z.source ∈ (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet := by
    rw [hsrc]
    exact GraphPath.source_mem_vertexSet
      (Gamma.rowPerfectPackingInRowSupport.path r)
  have hidx :=
    Gamma.rowSupportGraph_walk_row_vertexIndex_le r Z.walk hsource_mem
  simpa only [htgt, hsrc, GraphPath.target_vertexIndex,
    GraphPath.source_vertexIndex, Nat.zero_add] using hidx

/-- For a competing perfect linkage in the row-support graph, the row determined
by the source of a path. -/
noncomputable def rowSupportSourceRow
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet)
    (i : R'.Index) : Gamma.rowPerfectPackingInRowSupport.Index :=
  Gamma.rowPerfectPackingInRowSupport.indexOfSource
    ⟨(R'.path i).source, R'.source_mem i⟩

theorem rowSupportSourceRow_source_eq
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet)
    (i : R'.Index) :
    (Gamma.rowPerfectPackingInRowSupport.path
      (Gamma.rowSupportSourceRow R' i)).source =
        (R'.path i).source := by
  have h :=
    congrArg Subtype.val
      (Gamma.rowPerfectPackingInRowSupport.source_indexOfSource
        ⟨(R'.path i).source, R'.source_mem i⟩)
  simpa [rowSupportSourceRow] using h

/-- A competing perfect-linkage path in the row-support graph stays on the row
selected by its source endpoint. -/
theorem rowSupportPerfectPath_vertexSet_subset_sourceRow
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet)
    (i : R'.Index) :
    ∀ v ∈ (R'.path i).vertexSet,
      v.1 ∈
        (Gamma.rowPacking.path (Gamma.rowSupportSourceRow R' i)).vertexSet := by
  classical
  let r := Gamma.rowSupportSourceRow R' i
  have hsrc_eq :
      (Gamma.rowPerfectPackingInRowSupport.path r).source =
        (R'.path i).source := by
    simpa [r] using Gamma.rowSupportSourceRow_source_eq R' i
  have hsrc_row :
      (R'.path i).source.1 ∈ (Gamma.rowPacking.path r).vertexSet := by
    have hRsrc :
        (Gamma.rowPerfectPackingInRowSupport.path r).source ∈
          (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet :=
      GraphPath.source_mem_vertexSet _
    have hRsrc_row :
        (Gamma.rowPerfectPackingInRowSupport.path r).source.1 ∈
          (Gamma.rowPacking.path r).vertexSet :=
      (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r
        (Gamma.rowPerfectPackingInRowSupport.path r).source).1 hRsrc
    simpa [hsrc_eq] using hRsrc_row
  exact Gamma.rowSupportGraph_path_vertexSet_subset_row r (R'.path i) hsrc_row

/-- A competing perfect-linkage path in the row-support graph ends at the target
of the same row selected by its source. -/
theorem rowSupportPerfectPath_target_eq_sourceRow_target
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet)
    (i : R'.Index) :
    (R'.path i).target =
      (Gamma.rowPerfectPackingInRowSupport.path
        (Gamma.rowSupportSourceRow R' i)).target := by
  classical
  let r := Gamma.rowSupportSourceRow R' i
  have htarget_row :
      (R'.path i).target.1 ∈ (Gamma.rowPacking.path r).vertexSet :=
    Gamma.rowSupportPerfectPath_vertexSet_subset_sourceRow R' i
      (R'.path i).target (GraphPath.target_mem_vertexSet _)
  have htarget_on_R :
      (R'.path i).target ∈
        (Gamma.rowPerfectPackingInRowSupport.path r).vertexSet :=
    (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r (R'.path i).target).2
      htarget_row
  simpa [r] using
    (Gamma.rowPerfectPackingInRowSupport.eq_target_of_mem_right_of_mem_path_vertexSet
      r (R'.target_mem i) htarget_on_R)

/-- The source-row map of a competing perfect linkage is injective. -/
theorem rowSupportSourceRow_injective
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet) :
    Function.Injective (Gamma.rowSupportSourceRow R') := by
  intro i j hij
  apply R'.source_bijective.1
  apply Subtype.ext
  calc
    (R'.path i).source =
        (Gamma.rowPerfectPackingInRowSupport.path
          (Gamma.rowSupportSourceRow R' i)).source := by
          exact (Gamma.rowSupportSourceRow_source_eq R' i).symm
    _ = (Gamma.rowPerfectPackingInRowSupport.path
          (Gamma.rowSupportSourceRow R' j)).source := by
          rw [hij]
    _ = (R'.path j).source := by
          exact Gamma.rowSupportSourceRow_source_eq R' j

/-- The source-row map of a competing perfect linkage is bijective: both
linkages use exactly the same source terminal set. -/
theorem rowSupportSourceRow_bijective
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet) :
    Function.Bijective (Gamma.rowSupportSourceRow R') := by
  classical
  refine (Fintype.bijective_iff_injective_and_card
    (Gamma.rowSupportSourceRow R')).2 ⟨
      Gamma.rowSupportSourceRow_injective R', ?_⟩
  calc
    Fintype.card R'.Index = R'.card := rfl
    _ = Gamma.rowSupportSourceSet.card := R'.card_eq_left_card
    _ = Gamma.rowPerfectPackingInRowSupport.card :=
        Gamma.rowPerfectPackingInRowSupport.card_eq_left_card.symm
    _ = Fintype.card Gamma.rowPerfectPackingInRowSupport.Index := rfl

theorem rowSupportSourceRow_surjective
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet) :
    Function.Surjective (Gamma.rowSupportSourceRow R') :=
  (Gamma.rowSupportSourceRow_bijective R').2

/-- Every row of the support linkage is represented by exactly one path of any
competing perfect linkage, with the same source and target endpoints. -/
theorem exists_rowSupportPerfectPath_for_row
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet)
    (r : Gamma.rowPerfectPackingInRowSupport.Index) :
    ∃ i : R'.Index,
      Gamma.rowSupportSourceRow R' i = r ∧
        (R'.path i).source =
          (Gamma.rowPerfectPackingInRowSupport.path r).source ∧
        (R'.path i).target =
          (Gamma.rowPerfectPackingInRowSupport.path r).target := by
  rcases Gamma.rowSupportSourceRow_surjective R' r with ⟨i, hi⟩
  refine ⟨i, hi, ?_, ?_⟩
  · simpa [hi] using (Gamma.rowSupportSourceRow_source_eq R' i).symm
  · simpa [hi] using Gamma.rowSupportPerfectPath_target_eq_sourceRow_target R' i

/-- Edge-set containment half of the row-support unique-linkage proof.  The
reverse containment is the remaining path-graph uniqueness argument. -/
theorem rowSupportPerfectPacking_edgeSet_subset_rowPerfectPackingInRowSupport
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (R' : PerfectPathPacking Gamma.rowSupportGraph
      Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet) :
    R'.toPathPacking.edgeSet ⊆
      Gamma.rowPerfectPackingInRowSupport.toPathPacking.edgeSet :=
  Gamma.rowSupportGraph_packing_edgeSet_subset_rowPerfectPackingInRowSupport
    R'.toPathPacking

/-- Row-support uniqueness reduced to the local path-graph fact.

The proved global part says that a competing perfect linkage is forced to use
one path per row, with the same row endpoints, and cannot use edges outside the
row linkage.  Therefore it suffices to know that the row path's edge set is
contained in the corresponding competing path's edge set. -/
theorem rowPerfectPackingInRowSupport_isUniqueLinkage_of_pathGraph_unique
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (hpath :
      ∀ R' : PerfectPathPacking Gamma.rowSupportGraph
          Gamma.rowSupportSourceSet Gamma.rowSupportTargetSet,
        ∀ i : R'.Index,
          (Gamma.rowPerfectPackingInRowSupport.path
            (Gamma.rowSupportSourceRow R' i)).edgeSet ⊆
              (R'.path i).edgeSet) :
    Gamma.rowPerfectPackingInRowSupport.IsUniqueLinkage := by
  classical
  constructor
  · exact Gamma.rowPerfectPackingInRowSupport_spans
  · intro R'
    apply le_antisymm
    · exact Gamma.rowSupportPerfectPacking_edgeSet_subset_rowPerfectPackingInRowSupport R'
    · intro e he
      rcases (Gamma.rowPerfectPackingInRowSupport.toPathPacking.mem_edgeSet).1 he with
        ⟨r, her⟩
      rcases Gamma.rowSupportSourceRow_surjective R' r with ⟨i, hi⟩
      have herow :
          e ∈ (Gamma.rowPerfectPackingInRowSupport.path
            (Gamma.rowSupportSourceRow R' i)).edgeSet := by
        simpa [hi] using her
      exact (R'.toPathPacking.mem_edgeSet).2 ⟨i, hpath R' i herow⟩

/-- If the row-support graph is acyclic, the row linkage is unique.  This turns
the remaining local path-graph uniqueness obligation into the standard
mathlib uniqueness of paths in an acyclic graph. -/
theorem rowPerfectPackingInRowSupport_isUniqueLinkage_of_acyclic
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (hacyc : Gamma.rowSupportGraph.IsAcyclic) :
    Gamma.rowPerfectPackingInRowSupport.IsUniqueLinkage := by
  classical
  refine Gamma.rowPerfectPackingInRowSupport_isUniqueLinkage_of_pathGraph_unique ?_
  intro R' i e he
  let r := Gamma.rowSupportSourceRow R' i
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  have hsrc : Prow.source = (R'.path i).source := by
    simpa [Prow, r] using Gamma.rowSupportSourceRow_source_eq R' i
  have htgt : Prow.target = (R'.path i).target := by
    simpa [Prow, r] using
      (Gamma.rowSupportPerfectPath_target_eq_sourceRow_target R' i).symm
  let Prow' : Gamma.rowSupportGraph.Path (R'.path i).source (R'.path i).target :=
    ⟨Prow.walk.copy hsrc htgt, by
      simpa [Prow] using Prow.isPath⟩
  let Zi : Gamma.rowSupportGraph.Path (R'.path i).source (R'.path i).target :=
    ⟨(R'.path i).walk, (R'.path i).isPath⟩
  have hwalk : Prow.walk.copy hsrc htgt = (R'.path i).walk := by
    simpa [Prow', Zi] using congrArg Subtype.val (hacyc.path_unique Prow' Zi)
  have hwalk_edges : Prow.walk.edges = (R'.path i).walk.edges := by
    have hcopy_edges : (Prow.walk.copy hsrc htgt).edges = Prow.walk.edges := by
      simp
    rw [← hcopy_edges, hwalk]
  have hmem : e ∈ Prow.edgeSet := by
    simpa [Prow] using he
  simpa [GraphPath.edgeSet, hwalk_edges] using hmem

/-- The row linkage in its vertex-exact support graph is unique.

The support graph contains exactly the row-linkage edges.  A competing perfect
linkage path is forced by its source endpoint to stay on the same row and to
end at that row's target.  Its edges are therefore a subset of the row edge
set; the row-index length bound shows it has at least the row length, so the
finite edge sets are equal. -/
theorem rowPerfectPackingInRowSupport_isUniqueLinkage
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.rowPerfectPackingInRowSupport.IsUniqueLinkage := by
  classical
  refine Gamma.rowPerfectPackingInRowSupport_isUniqueLinkage_of_pathGraph_unique ?_
  intro R' i e he
  let r := Gamma.rowSupportSourceRow R' i
  let Prow := Gamma.rowPerfectPackingInRowSupport.path r
  have hsrc : (R'.path i).source = Prow.source := by
    simpa [Prow, r] using (Gamma.rowSupportSourceRow_source_eq R' i).symm
  have htgt : (R'.path i).target = Prow.target := by
    simpa [Prow, r] using Gamma.rowSupportPerfectPath_target_eq_sourceRow_target R' i
  have hsource_mem : (R'.path i).source ∈ Prow.vertexSet := by
    rw [hsrc]
    exact GraphPath.source_mem_vertexSet Prow
  have hsub :
      (R'.path i).edgeSet ⊆ Prow.edgeSet := by
    simpa [Prow] using
      Gamma.rowSupportGraph_path_edgeSet_subset_row r (R'.path i) hsource_mem
  have hlen :
      Prow.walk.length ≤ (R'.path i).walk.length := by
    simpa [Prow] using
      Gamma.rowSupportGraph_path_length_ge_row r (R'.path i) hsrc htgt
  have hcard :
      Prow.edgeSet.card ≤ (R'.path i).edgeSet.card := by
    simpa [GraphPath.edgeSet_card] using hlen
  have hedge_eq : (R'.path i).edgeSet = Prow.edgeSet :=
    Finset.eq_of_subset_of_card_le hsub hcard
  rw [← hedge_eq] at he
  exact he

/-- The retained auxiliary family viewed inside `H'`. -/
noncomputable def goodQPathPackingInHPrime
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathPacking Gamma.hPrimeGraph Finset.univ X :=
  Gamma.goodQPathPacking.inSpanningGraph.mapLe
    Gamma.goodQPathPacking_spanningGraph_le_hPrimeGraph

@[simp] theorem goodQPathPackingInHPrime_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.goodQPathPackingInHPrime.card = Gamma.goodQPathPacking.card := by
  simp [goodQPathPackingInHPrime]

/-- The replacement-pair construction in Observation 4.3.

If a full-size `A'`--`B'` linkage exists in `H' \ e`, where `e` is a row edge
unused by the original `Q` family, then replacing the selected row paths of
`P` by that linkage and keeping the complementary `P` paths gives a new
Theorem-4.1 pair with strictly fewer edges in `P ∪ Q`. -/
theorem exists_replacement_pair_of_full_delete_linkage
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) (e : Sym2 V)
    (heR : e ∈ Gamma.rowPacking.edgeSet)
    (heQ : e ∉ Q.toPathPacking.edgeSet)
    (L : PathPacking
        (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V)))
        (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion))
    (hLcard : L.card = Gamma.rowPacking.card) :
    ∃ (P' : PerfectPathPacking G A B) (Q' : PerfectPathPacking G A X),
      P'.pairUnionEdgeCount Q' < P.pairUnionEdgeCount Q := by
  classical
  have hLS : L.card = (P.sourceSet Gamma.reservedUnion).card := by
    calc
      L.card = Gamma.rowPacking.card := hLcard
      _ = (P.sourceSet Gamma.reservedUnion).card := by
        rw [Gamma.rowPacking_card, P.sourceSet_card]
  have hLT : L.card = (P.targetSet Gamma.reservedUnion).card := by
    calc
      L.card = Gamma.rowPacking.card := hLcard
      _ = (P.targetSet Gamma.reservedUnion).card := by
        rw [Gamma.rowPacking_card, P.targetSet_card]
  let LperfectDeleted :
      PerfectPathPacking (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V)))
        (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion) :=
    L.toPerfectOfCardEq hLS hLT
  have hdelG :
      Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V)) ≤ G :=
    (_root_.SimpleGraph.deleteEdges_le ({e} : Set (Sym2 V))).trans
      Gamma.hPrimeGraph_le
  let LperfectG :
      PerfectPathPacking G
        (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion) :=
    LperfectDeleted.mapLe hdelG
  let Prem : PerfectPathPacking G (P.sourceSet Gamma.remaining)
      (P.targetSet Gamma.remaining) :=
    P.restrictIndexSet Gamma.remaining
  have hSdisj :
      Disjoint (P.sourceSet Gamma.reservedUnion) (P.sourceSet Gamma.remaining) := by
    simpa [PseudoGrid.remaining] using
      P.sourceSet_disjoint_sdiff Gamma.reservedUnion
  have hTdisj :
      Disjoint (P.targetSet Gamma.reservedUnion) (P.targetSet Gamma.remaining) := by
    simpa [PseudoGrid.remaining] using
      P.targetSet_disjoint_sdiff Gamma.reservedUnion
  have hnode : LperfectG.toPathPacking.MutuallyNodeDisjoint Prem.toPathPacking := by
    intro i j
    have hdisj :=
      Gamma.hPrimeGraph_deleteEdges_packing_path_disjoint_remaining
        e L i (p := j.1) j.2
    simpa [LperfectG, LperfectDeleted, Prem, PathPacking.toPerfectOfCardEq,
      PerfectPathPacking.mapLe, PathPacking.mapLe, PathPacking.orient,
      PerfectPathPacking.restrictIndexSet, GraphPath.NodeDisjoint] using hdisj
  let Punion :
      PerfectPathPacking G
        (P.sourceSet Gamma.reservedUnion ∪ P.sourceSet Gamma.remaining)
        (P.targetSet Gamma.reservedUnion ∪ P.targetSet Gamma.remaining) :=
    LperfectG.disjointUnion Prem hSdisj hTdisj hnode
  have hSourceUnion :
      P.sourceSet Gamma.reservedUnion ∪ P.sourceSet Gamma.remaining = A := by
    simpa [PseudoGrid.remaining] using
      P.sourceSet_union_sdiff_eq_left Gamma.reservedUnion
  have hTargetUnion :
      P.targetSet Gamma.reservedUnion ∪ P.targetSet Gamma.remaining = B := by
    simpa [PseudoGrid.remaining] using
      P.targetSet_union_sdiff_eq_right Gamma.reservedUnion
  let Pnew : PerfectPathPacking G A B :=
    Punion.copyTerminals hSourceUnion hTargetUnion
  have hPnew_subset :
      Pnew.toPathPacking.edgeSet ⊆
        P.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet := by
    intro f hf
    have hfUnion :
        f ∈ LperfectG.toPathPacking.edgeSet ∪ Prem.toPathPacking.edgeSet := by
      have hsub :=
        PerfectPathPacking.disjointUnion_edgeSet_subset_union
          LperfectG Prem hSdisj hTdisj hnode
      exact hsub (by simpa [Pnew, Punion] using hf)
    rcases Finset.mem_union.mp hfUnion with hfL | hfPrem
    · have hfL' : f ∈ L.edgeSet := by
        simpa [LperfectG, LperfectDeleted, PathPacking.toPerfectOfCardEq] using hfL
      exact Gamma.deleteEdges_packing_edgeSet_subset_pairUnion e L hfL'
    · have hfPrem' :
          f ∈ (P.restrictIndexSet Gamma.remaining).toPathPacking.edgeSet := by
        simpa [Prem] using hfPrem
      exact Finset.mem_union_left _
        (Gamma.remainingPerfectPacking_edgeSet_subset_P hfPrem')
  have heOld :
      e ∈ P.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet :=
    Finset.mem_union_left _
      (Gamma.rowPacking_edgeSet_subset_P heR)
  have hePnew_not : e ∉ Pnew.toPathPacking.edgeSet := by
    intro hnew
    have hnewUnion :
        e ∈ LperfectG.toPathPacking.edgeSet ∪ Prem.toPathPacking.edgeSet := by
      have hsub :=
        PerfectPathPacking.disjointUnion_edgeSet_subset_union
          LperfectG Prem hSdisj hTdisj hnode
      exact hsub (by simpa [Pnew, Punion] using hnew)
    rcases Finset.mem_union.mp hnewUnion with heL | hePrem
    · have heL' : e ∈ L.edgeSet := by
        simpa [LperfectG, LperfectDeleted, PathPacking.toPerfectOfCardEq] using heL
      exact Gamma.deleteEdges_packing_not_mem_deleted e L heL'
    · have hePrem' :
          e ∈ (P.restrictIndexSet Gamma.remaining).toPathPacking.edgeSet := by
        simpa [Prem] using hePrem
      exact Gamma.rowPacking_edge_not_mem_remainingPerfectPacking heR hePrem'
  have heNew_not :
      e ∉ Pnew.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet := by
    intro hnew
    rcases Finset.mem_union.mp hnew with hPnew | hQ
    · exact hePnew_not hPnew
    · exact heQ hQ
  have hUnionSubset :
      Pnew.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet ⊆
        P.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet := by
    intro f hf
    rcases Finset.mem_union.mp hf with hfPnew | hfQ
    · exact hPnew_subset hfPnew
    · exact Finset.mem_union_right _ hfQ
  have hproper :
      Pnew.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet ⊂
        P.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet := by
    refine ⟨hUnionSubset, ?_⟩
    intro hOldSubsetNew
    have heNew :
        e ∈ Pnew.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet :=
      hOldSubsetNew heOld
    exact heNew_not heNew
  refine ⟨Pnew, Q, ?_⟩
  simpa [PerfectPathPacking.pairUnionEdgeCount] using
    Finset.card_lt_card hproper

/-- Conditional core of Observation 4.3.

If every full-size `A'`--`B'` linkage in `H' \ e` gives a replacement
Theorem-4.1 pair with strictly smaller edge-union count, then no such full-size
linkage exists.  The remaining, graph-specific part of Observation 4.3 is the
construction of that replacement pair from a full-size linkage after deleting
an eligible row edge. -/
theorem observation_four_three_edge_deletion_bound_of_replacement
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q) (e : Sym2 V)
    (hreplace :
      ∀ L : PathPacking (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V)))
          (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion),
        L.card = Gamma.rowPacking.card →
          ∃ (P' : PerfectPathPacking G A B) (Q' : PerfectPathPacking G A X),
            P'.pairUnionEdgeCount Q' < P.pairUnionEdgeCount Q) :
    ∀ L : PathPacking
        (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V)))
        (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion),
      L.card ≤ Gamma.rowPacking.card - 1 := by
  classical
  intro L
  have hLle : L.card ≤ Gamma.rowPacking.card := by
    calc
      L.card ≤ (P.sourceSet Gamma.reservedUnion).card := L.card_le_left_card
      _ = Gamma.rowPacking.card := by
        rw [P.sourceSet_card, Gamma.rowPacking_card]
  by_cases hzero : Gamma.rowPacking.card = 0
  · omega
  by_contra hnot
  have hge : Gamma.rowPacking.card ≤ L.card := by
    omega
  have hLcard : L.card = Gamma.rowPacking.card :=
    le_antisymm hLle hge
  rcases hreplace L hLcard with ⟨P', Q', hlt⟩
  exact (P.not_pairUnionEdgeCount_lt_of_minimum Q hminimal P' Q') hlt

/-- Observation 4.3 of Chuzhoy--Tan Section 4.2.

For a row edge of `H'` that is not used by any original `Q` path, deleting the
edge lowers the maximum size of an `A'`--`B'` path packing below the row-linkage
size. -/
theorem observation_four_three_edge_deletion_bound
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q) (e : Sym2 V)
    (heR : e ∈ Gamma.rowPacking.edgeSet)
    (heQ : e ∉ Q.toPathPacking.edgeSet) :
    ∀ L : PathPacking
        (Gamma.hPrimeGraph.deleteEdges ({e} : Set (Sym2 V)))
        (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion),
      L.card ≤ Gamma.rowPacking.card - 1 :=
  Gamma.observation_four_three_edge_deletion_bound_of_replacement
    hminimal e
    (fun L hLcard =>
      Gamma.exists_replacement_pair_of_full_delete_linkage e heR heQ L hLcard)

/-- Property I1 as an intersection with the row linkage: every retained
`Q''` path intersects the row packing.  The stronger row-by-row I1 is
`goodQPathPacking_intersects_row`. -/
theorem goodQPathPacking_intersects_rowPacking
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPacking.Index) :
    ∃ r : Gamma.rowPacking.Index,
      ¬ Disjoint
        (Gamma.goodQPathPacking.path j).vertexSet
        (Gamma.rowPacking.path r).vertexSet := by
  classical
  let i0 : Fin D := ⟨0, Gamma.depth_pos⟩
  rcases Gamma.goodQPathPacking_intersects_row j i0 with
    ⟨p, hp, hdisj⟩
  let r : Gamma.rowPacking.Index :=
    ⟨p, by
      change p ∈ pseudoGridReservedUnion Gamma.reserved
      exact Finset.mem_biUnion.2 ⟨i0, by simp, hp⟩⟩
  refine ⟨r, ?_⟩
  intro h
  apply hdisj
  rw [Finset.disjoint_left]
  intro v hvP hvQ
  exact Finset.disjoint_left.mp h
    (by simpa [goodQPathPacking] using hvQ)
    (by simpa [rowPacking, r] using hvP)

/-- A row path intersected by a retained auxiliary path. -/
noncomputable def goodQContactRow
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPacking.Index) : Gamma.rowPacking.Index :=
  Classical.choose (Gamma.goodQPathPacking_intersects_rowPacking j)

/-- A retained auxiliary path is not disjoint from its chosen contact row. -/
theorem goodQContactRow_not_disjoint
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPacking.Index) :
    ¬ Disjoint
      (Gamma.goodQPathPacking.path j).vertexSet
      (Gamma.rowPacking.path (Gamma.goodQContactRow j)).vertexSet :=
  Classical.choose_spec (Gamma.goodQPathPacking_intersects_rowPacking j)

/-- The concrete contact vertex used when contracting a retained auxiliary path
onto the row linkage. -/
noncomputable def goodQContactVertex
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPacking.Index) : V :=
  Classical.choose
    (Finset.not_disjoint_iff.mp (Gamma.goodQContactRow_not_disjoint j))

theorem goodQContactVertex_mem_goodQPath
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPacking.Index) :
    Gamma.goodQContactVertex j ∈
      (Gamma.goodQPathPacking.path j).vertexSet :=
  (Classical.choose_spec
    (Finset.not_disjoint_iff.mp (Gamma.goodQContactRow_not_disjoint j))).1

theorem goodQContactVertex_mem_contactRow
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPacking.Index) :
    Gamma.goodQContactVertex j ∈
      (Gamma.rowPacking.path (Gamma.goodQContactRow j)).vertexSet :=
  (Classical.choose_spec
    (Finset.not_disjoint_iff.mp (Gamma.goodQContactRow_not_disjoint j))).2

theorem goodQContactVertex_mem_rowPacking_vertexSet
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPacking.Index) :
    Gamma.goodQContactVertex j ∈ Gamma.rowPacking.vertexSet :=
  (Gamma.rowPacking.mem_vertexSet).2
    ⟨Gamma.goodQContactRow j, Gamma.goodQContactVertex_mem_contactRow j⟩

/-- Distinct retained auxiliary paths have distinct row-contact vertices,
because the retained auxiliary paths are node-disjoint. -/
theorem goodQContactVertex_injective
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Function.Injective Gamma.goodQContactVertex := by
  intro i j hij
  by_contra hne
  have hdisj := Gamma.goodQPathPacking.node_disjoint hne
  exact Finset.disjoint_left.mp hdisj
    (Gamma.goodQContactVertex_mem_goodQPath i)
    (by
      simpa [hij] using Gamma.goodQContactVertex_mem_goodQPath j)

/-- The contracted retained auxiliary family: one length-zero path at the
chosen row-contact vertex of each retained `Q''` path. -/
noncomputable def goodQContactPackingInHPrime
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathPacking Gamma.hPrimeGraph Finset.univ Finset.univ where
  Index := Gamma.goodQPathPacking.Index
  path := fun j => GraphPath.refl Gamma.hPrimeGraph (Gamma.goodQContactVertex j)
  connects := by
    intro j
    exact Or.inl ⟨by simp, by simp⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, GraphPath.refl_vertexSet,
      GraphPath.refl_vertexSet, Finset.disjoint_singleton_left]
    intro hcontact
    have hcontact_eq :
        Gamma.goodQContactVertex i = Gamma.goodQContactVertex j := by
      simpa using hcontact
    exact hij (Gamma.goodQContactVertex_injective hcontact_eq)

@[simp] theorem goodQContactPackingInHPrime_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.goodQContactPackingInHPrime.card = Gamma.goodQPathPacking.card := by
  rfl

/-- Contracting retained auxiliary paths to their row contacts preserves the
intersection-with-linkage hypothesis needed by Theorem 4.6. -/
theorem goodQContactPackingInHPrime_intersects_rowPerfectPackingInHPrime
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathSlicing.PathPackingIntersectsLinkage
      Gamma.rowPerfectPackingInHPrime Gamma.goodQContactPackingInHPrime := by
  intro j
  let r : Gamma.rowPerfectPackingInHPrime.Index := Gamma.goodQContactRow j
  refine ⟨r, ?_⟩
  rw [Finset.not_disjoint_iff]
  exact ⟨Gamma.goodQContactVertex j,
    by simp [goodQContactPackingInHPrime],
    by
      simpa [rowPerfectPackingInHPrime, PerfectPathPacking.mapLe,
        PerfectPathPacking.inSpanningGraph, PathPacking.mapLe,
        PathPacking.inSpanningGraph, PathPacking.transfer, r]
        using Gamma.goodQContactVertex_mem_contactRow j⟩

/-- The contracted retained auxiliary family inside the row-support graph.  The
vertex type is already the set of row-linkage vertices, so each retained `Q''`
path becomes a length-zero path at its chosen row-contact vertex. -/
noncomputable def goodQContactPackingInRowSupport
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathPacking Gamma.rowSupportGraph Finset.univ Finset.univ where
  Index := Gamma.goodQPathPacking.Index
  path := fun j =>
    GraphPath.refl Gamma.rowSupportGraph
      ⟨Gamma.goodQContactVertex j,
        Gamma.goodQContactVertex_mem_rowPacking_vertexSet j⟩
  connects := by
    intro j
    exact Or.inl ⟨by simp, by simp⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, GraphPath.refl_vertexSet,
      GraphPath.refl_vertexSet, Finset.disjoint_singleton_left]
    intro hcontact
    have hcontact_eq :
        Gamma.goodQContactVertex i = Gamma.goodQContactVertex j := by
      have hsub :
          (⟨Gamma.goodQContactVertex i,
            Gamma.goodQContactVertex_mem_rowPacking_vertexSet i⟩ :
            {x : V // x ∈ Gamma.rowPacking.vertexSet}) =
            ⟨Gamma.goodQContactVertex j,
              Gamma.goodQContactVertex_mem_rowPacking_vertexSet j⟩ := by
        simpa using hcontact
      exact congrArg Subtype.val hsub
    exact hij (Gamma.goodQContactVertex_injective hcontact_eq)

@[simp] theorem goodQContactPackingInRowSupport_card
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    Gamma.goodQContactPackingInRowSupport.card =
      Gamma.goodQPathPacking.card := by
  rfl

/-- The contracted retained auxiliary family still intersects the induced row
linkage in the row-support graph. -/
theorem goodQContactPackingInRowSupport_intersects_rowPerfectPackingInRowSupport
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathSlicing.PathPackingIntersectsLinkage
      Gamma.rowPerfectPackingInRowSupport
      Gamma.goodQContactPackingInRowSupport := by
  intro j
  let r : Gamma.rowPerfectPackingInRowSupport.Index := Gamma.goodQContactRow j
  let c : {x : V // x ∈ Gamma.rowPacking.vertexSet} :=
    ⟨Gamma.goodQContactVertex j,
      Gamma.goodQContactVertex_mem_rowPacking_vertexSet j⟩
  refine ⟨r, ?_⟩
  rw [Finset.not_disjoint_iff]
  refine ⟨c, ?_, ?_⟩
  · simp [goodQContactPackingInRowSupport, c]
  · exact (Gamma.rowPerfectPackingInRowSupport_path_vertexSet r c).2
      (Gamma.goodQContactVertex_mem_contactRow j)

/-- All non-uniqueness conclusions of Observation 4.4 are already available
in `H'`: it is a minor of the original graph, the row packing has the right
cardinality, and the contracted retained auxiliary family still intersects the
row linkage.  The remaining mathematical work in Observation 4.4 is precisely
to prove the unique-linkage hypothesis after the edge-contraction reduction. -/
theorem observation_four_four_reduction_of_unique
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (hunique : Gamma.rowPerfectPackingInHPrime.IsUniqueLinkage) :
    ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
      ∃ (H : _root_.SimpleGraph W),
      ∃ (A' B' S T : Finset W),
        ∃ (R : PerfectPathPacking H A' B') (Qpack : PathPacking H S T),
          IsMinor H G ∧
            R.IsUniqueLinkage ∧
              R.card = Gamma.rowPacking.card ∧
                Gamma.goodQSet.card ≤ Qpack.card ∧
                  PathSlicing.PathPackingIntersectsLinkage R Qpack := by
  refine ⟨V, inferInstance, inferInstance, Gamma.hPrimeGraph,
    P.sourceSet Gamma.reservedUnion, P.targetSet Gamma.reservedUnion,
    Finset.univ, Finset.univ, Gamma.rowPerfectPackingInHPrime,
    Gamma.goodQContactPackingInHPrime, ?_, hunique, ?_, ?_, ?_⟩
  · exact Gamma.hPrimeGraph_isMinor
  · calc
      Gamma.rowPerfectPackingInHPrime.card = Gamma.rowPerfectPacking.card := by
        simp
      _ = Gamma.rowPacking.card := by
        rw [Gamma.rowPerfectPacking_card, Gamma.rowPacking_card]
  · calc
      Gamma.goodQSet.card = Gamma.goodQPathPacking.card := by
        rw [Gamma.goodQPathPacking_card]
      _ = Gamma.goodQContactPackingInHPrime.card := by
        rw [Gamma.goodQContactPackingInHPrime_card]
      _ ≤ Gamma.goodQContactPackingInHPrime.card := le_rfl
  · exact Gamma.goodQContactPackingInHPrime_intersects_rowPerfectPackingInHPrime

/-- Vertex-exact form of Observation 4.4.

The ambient graph is the induced support of the row linkage, so the spanning
condition in `IsUniqueLinkage` is built in.  This is the same minor/reduction
package as Observation 4.4 once the structural unique-linkage proof for this
support graph has been supplied. -/
theorem observation_four_four_reduction_of_rowSupport_unique
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (hunique : Gamma.rowPerfectPackingInRowSupport.IsUniqueLinkage) :
    ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
      ∃ (H : _root_.SimpleGraph W),
      ∃ (A' B' S T : Finset W),
        ∃ (R : PerfectPathPacking H A' B') (Qpack : PathPacking H S T),
          IsMinor H G ∧
            R.IsUniqueLinkage ∧
              R.card = Gamma.rowPacking.card ∧
                Gamma.goodQSet.card ≤ Qpack.card ∧
                  PathSlicing.PathPackingIntersectsLinkage R Qpack := by
  refine ⟨{v : V // v ∈ Gamma.rowPacking.vertexSet}, inferInstance, inferInstance,
    Gamma.rowSupportGraph,
    PathPacking.subtypeFinset (P.sourceSet Gamma.reservedUnion)
      Gamma.rowPacking.vertexSet Gamma.sourceSet_subset_rowPacking_vertexSet,
    PathPacking.subtypeFinset (P.targetSet Gamma.reservedUnion)
      Gamma.rowPacking.vertexSet Gamma.targetSet_subset_rowPacking_vertexSet,
    Finset.univ, Finset.univ, Gamma.rowPerfectPackingInRowSupport,
    Gamma.goodQContactPackingInRowSupport, ?_, hunique, ?_, ?_, ?_⟩
  · exact Gamma.rowSupportGraph_isMinor
  · calc
      Gamma.rowPerfectPackingInRowSupport.card = Gamma.rowPerfectPacking.card := by
        simp
      _ = Gamma.rowPacking.card := by
        rw [Gamma.rowPerfectPacking_card, Gamma.rowPacking_card]
  · calc
      Gamma.goodQSet.card = Gamma.goodQPathPacking.card := by
        rw [Gamma.goodQPathPacking_card]
      _ = Gamma.goodQContactPackingInRowSupport.card := by
        rw [Gamma.goodQContactPackingInRowSupport_card]
      _ ≤ Gamma.goodQContactPackingInRowSupport.card := le_rfl
  · exact
      Gamma.goodQContactPackingInRowSupport_intersects_rowPerfectPackingInRowSupport

/-- Observation 4.4: after passing to the row-support minor and contracting
each retained auxiliary path to a row-contact vertex, the row linkage is a
perfect unique linkage and the retained auxiliary family still intersects it.

The minimality hypothesis is part of the paper's route through edge deletion;
the vertex-exact row-support construction proves the required unique linkage
directly from the row-path support graph. -/
theorem observation_four_four_unique_linkage_reduction
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    (_hminimal : P.IsMinimumTheorem41Pair Q) :
    ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
      ∃ (H : _root_.SimpleGraph W),
      ∃ (A' B' S T : Finset W),
        ∃ (R : PerfectPathPacking H A' B') (Qpack : PathPacking H S T),
          IsMinor H G ∧
            R.IsUniqueLinkage ∧
              R.card = Gamma.rowPacking.card ∧
                Gamma.goodQSet.card ≤ Qpack.card ∧
                  PathSlicing.PathPackingIntersectsLinkage R Qpack :=
  Gamma.observation_four_four_reduction_of_rowSupport_unique
    Gamma.rowPerfectPackingInRowSupport_isUniqueLinkage

/-- Self-contained pseudo-grid branch of Section 4.2.

This is the combined Observation 4.4 plus Theorem 4.6 outcome specialized to
the row-support minor.  The generic Robertson--Seymour ordering lemma is not
used here: `rowSupportLinkageOrdering` supplies the required ordering directly
from the fact that the row-support graph is the disjoint union of row paths. -/
theorem section42_slicing_minor_of_pseudoGrid_rowSupport
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q)
    {M w : ℕ} (hM : 0 < M) (_hw : 0 < w)
    (hcard :
      M * w + (M + 1) * Gamma.rowPacking.card ≤ Gamma.goodQSet.card) :
    ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
      ∃ (H : _root_.SimpleGraph W),
      ∃ (A' B' S T : Finset W),
        ∃ (R : PerfectPathPacking H A' B') (Qpack : PathPacking H S T),
          ∃ sigma : PathSlicing R M,
            IsMinor H G ∧
              R.IsUniqueLinkage ∧
                R.card = Gamma.rowPacking.card ∧
                  sigma.WidthAtLeast Qpack w := by
  classical
  let W : Type u := {v : V // v ∈ Gamma.rowPacking.vertexSet}
  let H : _root_.SimpleGraph W := Gamma.rowSupportGraph
  let A' : Finset W := Gamma.rowSupportSourceSet
  let B' : Finset W := Gamma.rowSupportTargetSet
  let R : PerfectPathPacking H A' B' := Gamma.rowPerfectPackingInRowSupport
  let Qpack : PathPacking H Finset.univ Finset.univ :=
    Gamma.goodQContactPackingInRowSupport
  have hRcard : R.card = Gamma.rowPacking.card := by
    calc
      R.card = Gamma.rowPerfectPackingInRowSupport.card := rfl
      _ = Gamma.rowPerfectPacking.card :=
        Gamma.rowPerfectPackingInRowSupport_card
      _ = Gamma.reservedUnion.card := Gamma.rowPerfectPacking_card
      _ = Gamma.rowPacking.card := Gamma.rowPacking_card.symm
  have hQcard : Gamma.goodQSet.card ≤ Qpack.card := by
    calc
      Gamma.goodQSet.card = Gamma.goodQPathPacking.card := by
        exact Gamma.goodQPathPacking_card.symm
      _ = Gamma.goodQContactPackingInRowSupport.card := by
        exact Gamma.goodQContactPackingInRowSupport_card.symm
      _ ≤ Qpack.card := le_rfl
  have hcard' : M * w + (M + 1) * R.card ≤ Qpack.card := by
    calc
      M * w + (M + 1) * R.card
          = M * w + (M + 1) * Gamma.rowPacking.card := by rw [hRcard]
      _ ≤ Gamma.goodQSet.card := hcard
      _ ≤ Qpack.card := hQcard
  let theta : PathSlicing.LinkageOrdering R := Gamma.rowSupportLinkageOrdering
  rcases PathSlicing.exists_slicing_of_linkageOrdering
      theta Qpack M w hM
      (by
        simpa [R, Qpack] using
          Gamma.goodQContactPackingInRowSupport_intersects_rowPerfectPackingInRowSupport)
      hcard' with
    ⟨sigma, hwidth⟩
  refine ⟨W, inferInstance, inferInstance, H, A', B', Finset.univ, Finset.univ,
    R, Qpack, sigma, ?_, ?_, hRcard, hwidth⟩
  · simpa [W, H] using Gamma.rowSupportGraph_isMinor
  · simpa [R] using Gamma.rowPerfectPackingInRowSupport_isUniqueLinkage

/-- The retained `Q''` packing intersects the row perfect linkage. -/
theorem goodQPathPacking_intersects_rowPerfectPacking
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathSlicing.PathPackingIntersectsLinkage
      Gamma.rowPerfectPacking Gamma.goodQPathPacking := by
  classical
  intro j
  rcases Gamma.goodQPathPacking_intersects_rowPacking j with ⟨r, hdisj⟩
  refine ⟨r, ?_⟩
  intro h
  apply hdisj
  rw [Finset.disjoint_left]
  intro v hvQ hvR
  exact Finset.disjoint_left.mp h
    (by simpa [goodQPathPacking] using hvQ)
    (by simpa [rowPerfectPacking] using hvR)

/-- Property I1 inside `H'`, with the row family viewed as the perfect linkage
on `A'` and `B'`. -/
theorem goodQPathPackingInHPrime_intersects_rowPerfectPackingInHPrime
    [Fintype V]
    (Gamma : PseudoGrid G A B X g D P Q) :
    PathSlicing.PathPackingIntersectsLinkage
      Gamma.rowPerfectPackingInHPrime Gamma.goodQPathPackingInHPrime := by
  classical
  intro j
  rcases Gamma.goodQPathPacking_intersects_rowPerfectPacking j with
    ⟨r, hdisj⟩
  refine ⟨r, ?_⟩
  intro h
  apply hdisj
  rw [Finset.disjoint_left]
  intro v hvQ hvR
  exact Finset.disjoint_left.mp h
    (by
      simpa [goodQPathPackingInHPrime, PathPacking.mapLe,
        PathPacking.inSpanningGraph, PathPacking.transfer] using hvQ)
    (by
      simpa [rowPerfectPackingInHPrime, PerfectPathPacking.mapLe,
        PerfectPathPacking.inSpanningGraph, PathPacking.mapLe,
        PathPacking.inSpanningGraph, PathPacking.transfer] using hvR)

/-- If `Q''` is nonempty, then the row linkage has at least `D` paths.  This
is the formal counterpart of the paper's `D ≤ N` once I1 is available. -/
theorem depth_le_reservedUnion_card_of_goodQSet_nonempty
    (Gamma : PseudoGrid G A B X g D P Q)
    (hgood : Gamma.goodQSet.Nonempty) :
    D ≤ Gamma.reservedUnion.card := by
  classical
  rcases hgood with ⟨j, hj⟩
  let hrow : ∀ i : Fin D, (Gamma.reserved i).Nonempty :=
    fun i => Gamma.reserved_nonempty_of_mem_goodQSet hj i
  let pick : Fin D → P.Index := fun i => (hrow i).choose
  have pick_mem : ∀ i : Fin D, pick i ∈ Gamma.reserved i :=
    fun i => (hrow i).choose_spec
  let f : Fin D → {p : P.Index // p ∈ Gamma.reservedUnion} := fun i =>
    ⟨pick i, by
      change pick i ∈ pseudoGridReservedUnion Gamma.reserved
      exact Finset.mem_biUnion.2 ⟨i, by simp, pick_mem i⟩⟩
  have hf : Function.Injective f := by
    intro i k hik
    by_contra hne
    have hpick : pick i = pick k := congrArg Subtype.val hik
    have hki : pick i ∈ Gamma.reserved k := by
      simpa [hpick] using pick_mem k
    exact Finset.disjoint_left.mp (Gamma.reserved_disjoint hne)
      (pick_mem i) hki
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, Fintype.card_fin] using hcard

/-- The paper's `D ≤ N ≤ Dg^2` bound for the row linkage size
`N = |R|`, once `Q''` is nonempty. -/
theorem rowPacking_card_bounds_of_goodQSet_nonempty
    (Gamma : PseudoGrid G A B X g D P Q)
    (hgood : Gamma.goodQSet.Nonempty) :
    D ≤ Gamma.rowPacking.card ∧ Gamma.rowPacking.card ≤ D * g ^ 2 := by
  constructor
  · simpa using Gamma.depth_le_reservedUnion_card_of_goodQSet_nonempty hgood
  · simpa using Gamma.reservedUnion_card_le

/-- The same `D ≤ N ≤ Dg^2` bound for the row linkage in its perfect-packing
form. -/
theorem rowPerfectPacking_card_bounds_of_goodQSet_nonempty
    (Gamma : PseudoGrid G A B X g D P Q)
    (hgood : Gamma.goodQSet.Nonempty) :
    D ≤ Gamma.rowPerfectPacking.card ∧
      Gamma.rowPerfectPacking.card ≤ D * g ^ 2 := by
  constructor
  · simpa using Gamma.depth_le_reservedUnion_card_of_goodQSet_nonempty hgood
  · simpa using Gamma.reservedUnion_card_le

theorem rowPerfectPacking_card_pos_of_goodQSet_nonempty
    (Gamma : PseudoGrid G A B X g D P Q)
    (hgood : Gamma.goodQSet.Nonempty) :
    0 < Gamma.rowPerfectPacking.card := by
  have hD : D ≤ Gamma.rowPerfectPacking.card :=
    (Gamma.rowPerfectPacking_card_bounds_of_goodQSet_nonempty hgood).1
  exact lt_of_lt_of_le Gamma.depth_pos hD

/-- Observation 4.4's final uniqueness step, packaged for the row linkage of a
pseudo-grid after the contraction procedure has supplied the needed
invariants. -/
theorem rowPerfectPacking_isUniqueLinkage_of_edge_deletion_bound
    (Gamma : PseudoGrid G A B X g D P Q)
    (hspan : Gamma.rowPerfectPacking.SpansVertices)
    (hcard_pos : 0 < Gamma.rowPerfectPacking.card)
    (hmissing :
      ∀ R' : PerfectPathPacking G
          (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion),
        R'.toPathPacking.edgeSet ≠
            Gamma.rowPerfectPacking.toPathPacking.edgeSet →
          ∃ e ∈ Gamma.rowPerfectPacking.toPathPacking.edgeSet,
            e ∉ R'.toPathPacking.edgeSet)
    (hdelete :
      ∀ e ∈ Gamma.rowPerfectPacking.toPathPacking.edgeSet,
        ∀ L : PathPacking (G.deleteEdges ({e} : Set (Sym2 V)))
            (P.sourceSet Gamma.reservedUnion) (P.targetSet Gamma.reservedUnion),
          L.card ≤ Gamma.rowPerfectPacking.card - 1) :
    Gamma.rowPerfectPacking.IsUniqueLinkage :=
  Gamma.rowPerfectPacking.isUniqueLinkage_of_edge_deletion_bound
    hspan hcard_pos hmissing hdelete

end PseudoGrid

end SimpleGraph

end Lax17Proofs
