import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.Degree
import Lax17Proofs.Source.TreewidthContract
import Lax17Proofs.Source.TreewidthMinor
import Lax17Proofs.Source.TreewidthSparsifierContract
import Lax17Proofs.Source.ChekuriChuzhoyTheorem221
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Contract for the degree-three strong path-of-sets input

This file states the Appendix A.2 starting ingredient used in the proof of
Chuzhoy--Tan Theorem 2.3.

In the paper this ingredient is obtained by combining:

* Theorem A.1: a large-treewidth graph has a maximum-degree-three subgraph
  whose treewidth is still large up to a polylogarithmic loss; and
* Theorem A.2: sufficiently large treewidth forces a strong Path-of-Sets
  System of prescribed length and width.

The contracts below state those two imported theorems in threshold forms that
compose cleanly.  The arithmetic composition is also exposed as a source-driven
theorem, so later self-contained proofs of the imported theorems can be plugged
in without redoing the parameter calculation.  The file then specializes the
combined consequence to the doubled-length/scaled-width form used by the formal
Appendix A.2 assembly.
-/

namespace SimpleGraph
namespace DegreeThreeStrongPathOfSetsContract


/-- Chuzhoy--Tan Theorem A.1 in the paper's Omega form.

The constants mean that for every graph of treewidth at least `k`, there is a
maximum-degree-three subgraph `H` whose treewidth loses only the multiplicative
factor `cSparse * log(k)^cSparseLog`:

`k ≤ cSparse * treewidth(H) * log(k)^cSparseLog`.

The threshold form used by the Appendix A.2 arithmetic is proved below from
this statement. -/
def DegreeThreeTreewidthSparsifierOmega
    (cSparse cSparseLog : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {k : ℕ},
      1 < k →
        k ≤ treewidth G →
          ∃ H : _root_.SimpleGraph V,
            H ≤ G ∧
              MaxDegreeAtMost H 3 ∧
                k ≤ cSparse * treewidth H *
                  (Nat.log 2 k) ^ cSparseLog

/-- The paper-shaped Omega form of Theorem A.1 implies the threshold form used
in the formal Appendix A.2 composition. -/
theorem degreeThreeTreewidthSparsifier_of_omega
    (homega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeTreewidthSparsifierOmega.{u} cSparse cSparseLog) :
    ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {k t : ℕ},
          1 < k →
            k ≤ treewidth G →
              cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H := by
  rcases homega with
    ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, homega'⟩
  refine ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, ?_⟩
  intro V _ _ G k t hk htw hlarge
  rcases homega' G hk htw with ⟨H, hHG, hdegree, hHtw⟩
  refine ⟨H, hHG, hdegree, ?_⟩
  let L := Nat.log 2 k
  let f := cSparse * L ^ cSparseLog
  have hlt : f * t < f * treewidth H := by
    calc
      f * t = cSparse * t * L ^ cSparseLog := by
        dsimp [f]
        ring
      _ < k := by
        simpa [L] using hlarge
      _ ≤ cSparse * treewidth H * L ^ cSparseLog := by
        simpa [L] using hHtw
      _ = f * treewidth H := by
        dsimp [f]
        ring
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left hlt)

/-- A width-zero decomposition of an edgeless finite graph.

The decomposition nodes are indexed in `Type` by one more than the number of
vertices.  Each vertex gets its own singleton bag; an arbitrary spanning tree
of the complete node graph supplies the decomposition tree. -/
noncomputable def edgelessTreeDecomposition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (hG : G = ⊥) : TreeDecomposition G := by
  let n := Fintype.card V
  let e := Fintype.equivFin V
  let T : _root_.SimpleGraph (Fin (n + 1)) :=
    Classical.choose
      ((_root_.SimpleGraph.connected_top (V := Fin (n + 1))).exists_isTree_le)
  have hT : T.IsTree :=
    (Classical.choose_spec
      ((_root_.SimpleGraph.connected_top (V := Fin (n + 1))).exists_isTree_le)).2
  exact {
    Node := Fin (n + 1)
    tree := T
    isTree := hT
    bag := fun i => Finset.univ.filter fun v => (e v).val = i.val
    vertex_mem_bag := by
      intro v
      refine ⟨⟨(e v).val, (e v).isLt.trans (Nat.lt_succ_self n)⟩, ?_⟩
      simp
    edge_mem_bag := by
      intro x y hxy
      rw [hG] at hxy
      simp at hxy
    bag_indices_connected := by
      intro v
      haveI : Nonempty {i : Fin (n + 1) |
          v ∈ Finset.univ.filter fun w => (e w).val = i.val} :=
        ⟨⟨⟨(e v).val, (e v).isLt.trans (Nat.lt_succ_self n)⟩, by simp⟩⟩
      haveI : Subsingleton {i : Fin (n + 1) |
          v ∈ Finset.univ.filter fun w => (e w).val = i.val} := by
        constructor
        rintro ⟨i, hi⟩ ⟨j, hj⟩
        apply Subtype.ext
        apply Fin.ext
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        simpa using hi.symm.trans hj
      exact _root_.SimpleGraph.Connected.of_subsingleton
  }

/-- An edgeless finite graph has treewidth zero. -/
theorem treewidth_eq_zero_of_eq_bot
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (hG : G = ⊥) :
    treewidth G = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply treewidth_le_of_hasTreewidthAtMost
  refine ⟨edgelessTreeDecomposition G hG, ?_⟩
  classical
  dsimp [edgelessTreeDecomposition, TreeDecomposition.width]
  have hsup :
      (Finset.univ.sup fun i : Fin (Fintype.card V + 1) =>
        (Finset.univ.filter fun v =>
          ((Fintype.equivFin V) v).val = i.val).card) ≤ 1 := by
    apply Finset.sup_le
    intro i _hi
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    apply (Fintype.equivFin V).injective
    apply Fin.ext
    exact hx.trans hy.symm
  omega

/-- A finite graph of treewidth greater than one contains an edge. -/
theorem exists_adj_of_one_lt_treewidth
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (hG : 1 < treewidth G) :
    ∃ u v : V, G.Adj u v := by
  by_contra h
  have h' : ∀ u v : V, ¬G.Adj u v := by
    intro u v huv
    exact h ⟨u, v, huv⟩
  have hbot : G = ⊥ :=
    _root_.SimpleGraph.eq_bot_iff_forall_not_adj.mpr h'
  rw [treewidth_eq_zero_of_eq_bot hbot] at hG
  omega

/-- The presence of an edge forces positive treewidth. -/
theorem treewidth_pos_of_adj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    0 < treewidth G := by
  by_contra h
  have htw : treewidth G = 0 := Nat.eq_zero_of_not_pos h
  rcases hasTreewidthAtMost_treewidth G with ⟨D, hD⟩
  rcases D.edge_mem_bag huv with ⟨i, hui, hvi⟩
  letI : Fintype D.Node := D.nodeFintype
  letI : DecidableEq D.Node := D.nodeDecidableEq
  have hcard : 2 ≤ (D.bag i).card := by
    have hsub : ({u, v} : Finset V) ⊆ D.bag i := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hui
      · exact hvi
    have := Finset.card_le_card hsub
    simpa [huv.ne] using this
  have hsup : (D.bag i).card ≤
      Finset.univ.sup (fun j : D.Node => (D.bag j).card) :=
    Finset.le_sup (f := fun j : D.Node => (D.bag j).card) (by simp)
  have hwidth : 1 ≤ D.width := by
    dsimp [TreeDecomposition.width]
    omega
  rw [htw] at hD
  omega

/-- The endpoints selected by `Sym2.out` are adjacent when the unordered pair
belongs to a graph's edge set. -/
theorem adj_out_of_mem_edgeSet
    {V : Type u} {G : _root_.SimpleGraph V} {e : Sym2 V}
    (he : e ∈ G.edgeSet) :
    G.Adj e.out.1 e.out.2 := by
  classical
  have heout : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  rw [← heout] at he
  simpa using he

/-- A one-edge graph path has no internal vertices. -/
theorem pathInternalVertexSet_ofAdj_eq_empty
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {u v : V} (huv : G.Adj u v) :
    TreewidthSparsifier.pathInternalVertexSet
      (TreewidthSparsifier.GraphPath.ofAdj huv) = ∅ := by
  classical
  ext x
  constructor
  · intro hx
    have hxtarget := Finset.mem_erase.mp hx
    have hxsource := Finset.mem_erase.mp hxtarget.2
    have hx' :
        x ∈ (TreewidthSparsifier.GraphPath.ofAdj huv).vertexSet ∧
          x ≠ u ∧ x ≠ v :=
      ⟨hxsource.2, by simpa using hxsource.1,
        by simpa using hxtarget.1⟩
    have hxpair :=
      TreewidthSparsifier.GraphPath.ofAdj_vertexSet_subset_pair huv hx'.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
    rcases hxpair with hxu | hxv
    · exact False.elim (hx'.2.1 hxu)
    · exact False.elim (hx'.2.2 hxv)
  · intro hx
    simp at hx

/-- Same-vertex graph inclusion gives a topological-minor model whose edge
paths are the corresponding one-edge paths. -/
noncomputable def topologicalMinorModelOfLE
    {V : Type u} [DecidableEq V]
    {H G : _root_.SimpleGraph V} (hHG : H ≤ G) :
    TreewidthSparsifier.TopologicalMinorModel H G where
  branchVertex := id
  branch_injective := Function.injective_id
  edgeSource := fun e => e.1.out.1
  edgeTarget := fun e => e.1.out.2
  edge_adj := fun e => adj_out_of_mem_edgeSet e.2
  edge_eq := by
    intro e
    rw [Sym2.mk, e.1.out_eq]
  edgePath := fun e =>
    TreewidthSparsifier.GraphPath.ofAdj
      (hHG (adj_out_of_mem_edgeSet e.2))
  edgePath_source := by
    intro e
    simp [TreewidthSparsifier.GraphPath.ofAdj]
  edgePath_target := by
    intro e
    simp [TreewidthSparsifier.GraphPath.ofAdj]
  edgePath_internal_disjoint_branches := by
    intro e z _hzs _hzt
    rw [pathInternalVertexSet_ofAdj_eq_empty]
    simp
  edgePath_pairwise_internal_disjoint := by
    intro e f _hef
    rw [pathInternalVertexSet_ofAdj_eq_empty,
      pathInternalVertexSet_ofAdj_eq_empty]
    simp

/-- A same-vertex spanning subgraph is a topological minor. -/
theorem isTopologicalMinor_of_le
    {V : Type u} [DecidableEq V]
    {H G : _root_.SimpleGraph V} (hHG : H ≤ G) :
    TreewidthSparsifier.IsTopologicalMinor H G :=
  ⟨topologicalMinorModelOfLE hHG⟩

/-- A graph consisting of at most one edge has maximum degree at most three. -/
theorem edge_maxDegreeAtMost_three
    {V : Type u} [DecidableEq V] {u v : V} :
    MaxDegreeAtMost (_root_.SimpleGraph.edge u v) 3 := by
  by_cases huv : u = v
  · subst v
    intro x
    refine ⟨∅, ?_, by simp⟩
    intro y
    simp
  intro x
  by_cases hxu : x = u
  · subst x
    refine ⟨{v}, ?_, by simp⟩
    intro y
    constructor
    · intro hy
      have hyv : y = v := by simpa using hy
      subst y
      exact (_root_.SimpleGraph.edge_adj u v u v).2
        ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
    · intro h
      rw [_root_.SimpleGraph.edge_adj] at h
      rcases h.1 with h | h
      · simp [h.2]
      · exact False.elim (huv h.1)
  · by_cases hxv : x = v
    · subst x
      refine ⟨{u}, ?_, by simp⟩
      intro y
      constructor
      · intro hy
        have hyu : y = u := by simpa using hy
        subst y
        exact (_root_.SimpleGraph.edge_adj u v v u).2
          ⟨Or.inr ⟨rfl, rfl⟩, Ne.symm huv⟩
      · intro h
        rw [_root_.SimpleGraph.edge_adj] at h
        rcases h.1 with h | h
        · exact False.elim ((Ne.symm huv) h.1)
        · simp [h.2]
    · refine ⟨∅, ?_, by simp⟩
      intro y
      simp [_root_.SimpleGraph.edge_adj, hxu, hxv]

/-- A graph of treewidth greater than one has a same-vertex subgraph of
maximum degree at most three and positive treewidth. -/
theorem exists_subgraph_maxDegreeAtMost_three_treewidth_pos
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (hG : 1 < treewidth G) :
    ∃ H : _root_.SimpleGraph V,
      H ≤ G ∧ MaxDegreeAtMost H 3 ∧ 0 < treewidth H := by
  rcases exists_adj_of_one_lt_treewidth hG with ⟨u, v, huv⟩
  let H := _root_.SimpleGraph.edge u v
  have hHG : H ≤ G := by
    intro x y hxy
    rw [_root_.SimpleGraph.edge_adj] at hxy
    rcases hxy.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv
    · exact huv.symm
  refine ⟨H, hHG, edge_maxDegreeAtMost_three, ?_⟩
  apply treewidth_pos_of_adj (u := u) (v := v)
  simpa [H, _root_.SimpleGraph.edge_adj] using huv.ne

/-- The threshold topological treewidth sparsifier implies its paper-shaped
Omega form with constant `2 * cSparse` and the same logarithmic exponent.

For `k ≤ 2 * cSparse * log(k)^cSparseLog`, the one-edge subgraph above
supplies the required positive-treewidth topological minor.  Otherwise the
threshold theorem is applied at
`k / (2 * cSparse * log(k)^cSparseLog) + 1`. -/
theorem degreeThreeTopologicalTreewidthSparsifierOmega_of_threshold
    {cSparse cSparseLog : ℕ} (hcSparse : 0 < cSparse)
    (hthreshold :
      TreewidthSparsifier.DegreeThreeTopologicalTreewidthSparsifierThreshold.{u}
        cSparse cSparseLog) :
    TreewidthSparsifier.DegreeThreeTopologicalTreewidthSparsifierOmega.{u}
      (2 * cSparse) cSparseLog := by
  intro V _ _ G k hk hGtw
  let L := Nat.log 2 k
  let F := cSparse * L ^ cSparseLog
  have hLpos : 0 < L := by
    simpa [L] using
      Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hFpos : 0 < F := by
    dsimp [F]
    positivity
  by_cases hsmall : k ≤ 2 * F
  · have htwLarge : 1 < treewidth G := hk.trans_le hGtw
    rcases exists_subgraph_maxDegreeAtMost_three_treewidth_pos htwLarge with
      ⟨H, hHG, hdegree, hHtw⟩
    refine ⟨V, inferInstance, inferInstance, H,
      isTopologicalMinor_of_le hHG, hdegree, ?_⟩
    calc
      k ≤ 2 * F := hsmall
      _ ≤ 2 * F * treewidth H := by
        exact Nat.le_mul_of_pos_right (2 * F) hHtw
      _ = (2 * cSparse) * treewidth H * L ^ cSparseLog := by
        dsimp [F]
        ring
      _ = (2 * cSparse) * treewidth H *
          (Nat.log 2 k) ^ cSparseLog := by rfl
  · have hlarge : 2 * F < k := Nat.lt_of_not_ge hsmall
    let t := k / (2 * F) + 1
    have htwCondition :
        cSparse * t * (Nat.log 2 k) ^ cSparseLog < k := by
      have hquotient :
          2 * (F * (k / (2 * F))) ≤ k := by
        calc
          2 * (F * (k / (2 * F))) =
              k / (2 * F) * (2 * F) := by ring
          _ ≤ k := Nat.div_mul_le_self k (2 * F)
      have hFt : F * t < k := by
        dsimp [t]
        rw [Nat.mul_add]
        omega
      calc
        cSparse * t * (Nat.log 2 k) ^ cSparseLog = F * t := by
          dsimp [F, L]
          ring
        _ < k := hFt
    rcases hthreshold G hk hGtw htwCondition with
      ⟨W, instW, instDecW, H, hminor, hdegree, hHtw⟩
    refine ⟨W, instW, instDecW, H, hminor, hdegree, ?_⟩
    have hdenom : 0 < 2 * F := by positivity
    calc
      k ≤ 2 * F * t := by
        exact Nat.le_of_lt (by
          simpa [t] using Nat.lt_mul_div_succ k hdenom)
      _ ≤ 2 * F * treewidth H := Nat.mul_le_mul_left (2 * F) hHtw
      _ = (2 * cSparse) * treewidth H * L ^ cSparseLog := by
        dsimp [F]
        ring
      _ = (2 * cSparse) * treewidth H *
          (Nat.log 2 k) ^ cSparseLog := by rfl


/-- The formal A.1 bridge through the support graph of a topological model.

The support graph of a topological-minor model is a same-vertex subgraph of the
host.  Existing minor monotonicity gives
`treewidth H ≤ treewidth M.supportGraph`, so Theorem 1.1's treewidth bound
transfers to the support graph.  The degree step is already discharged by
`TopologicalMinorModel.supportGraph_maxDegreeAtMost_of_maxDegreeAtMost`; the
parameter below keeps this source-level bridge reusable, and the concrete
theorem later in this file supplies that proved result. -/
theorem degreeThreeTreewidthSparsifierOmega_of_treewidthSparsifierTheorem11_and_supportGraphDegree
    (hsupport :
      ∀ {V W : Type u} [Fintype V] [DecidableEq V]
        [Fintype W] [DecidableEq W]
        {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
        (M : TreewidthSparsifier.TopologicalMinorModel H G),
          MaxDegreeAtMost H 3 →
            MaxDegreeAtMost M.supportGraph 3)
    (h11 :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        TreewidthSparsifier.DegreeThreeTopologicalTreewidthSparsifierOmega.{u}
          cSparse cSparseLog) :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        DegreeThreeTreewidthSparsifierOmega.{u} cSparse cSparseLog := by
  rcases h11 with ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, htop⟩
  refine ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, ?_⟩
  intro V _ _ G k hk htw
  rcases htop G hk htw with
    ⟨W, _, _, H, hminor, hdegree, htwH⟩
  rcases hminor with ⟨M⟩
  refine ⟨M.supportGraph, M.supportGraph_le, hsupport M hdegree, ?_⟩
  have htw_le : treewidth H ≤ treewidth M.supportGraph :=
    treewidth_le_of_minor M.isMinor_supportGraph
  exact htwH.trans
    (Nat.mul_le_mul_right ((Nat.log 2 k) ^ cSparseLog)
      (Nat.mul_le_mul_left cSparse htw_le))


/-- Threshold-form A.1 bridge from the paper-facing topological-minor
sparsifier to the same-vertex subgraph sparsifier used by Appendix A.2.

As in the Omega bridge above, the returned subgraph is the support graph of the
topological-minor model.  Minor monotonicity transfers the treewidth lower
bound from the modelled degree-three graph to its support graph. -/
theorem degreeThreeTreewidthSparsifier_of_treewidthSparsifierThreshold_and_supportGraphDegree
    (hsupport :
      ∀ {V W : Type u} [Fintype V] [DecidableEq V]
        [Fintype W] [DecidableEq W]
        {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
        (M : TreewidthSparsifier.TopologicalMinorModel H G),
          MaxDegreeAtMost H 3 →
            MaxDegreeAtMost M.supportGraph 3)
    (hthreshold :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        TreewidthSparsifier.DegreeThreeTopologicalTreewidthSparsifierThreshold.{u}
          cSparse cSparseLog) :
    ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {k t : ℕ},
          1 < k →
            k ≤ treewidth G →
              cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H := by
  rcases hthreshold with ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, htop⟩
  refine ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, ?_⟩
  intro V _ _ G k t hk htw hlarge
  rcases htop G hk htw hlarge with
    ⟨W, _, _, H, hminor, hdegree, htwH⟩
  rcases hminor with ⟨M⟩
  refine ⟨M.supportGraph, M.supportGraph_le, hsupport M hdegree, ?_⟩
  exact htwH.trans (treewidth_le_of_minor M.isMinor_supportGraph)



/-- The local linked-pair predicate implies the paper's equal-sized-subset
linkedness predicate.

This direction is valid for linked pairs because the two full terminal sides
are already disjoint, so every pair of subfamilies is disjoint as well. -/
theorem paperLinkedIn_of_nodeLinkedIn
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {C A B : Finset V}
    (h : NodeLinkedIn G C A B) :
    TreewidthSparsifier.PaperLinkedIn G C A B := by
  classical
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro A' B' hA' hB' hcard
  rcases (NodeLinkedIn.mono_terminals h hA' hB').exists_perfectPathPacking_of_card_eq
      hcard with
    ⟨P, _hPcard, hPstay⟩
  exact ⟨P, hPstay⟩

/-- The paper's equal-sized-subset node-well-linkedness implies the local
maximum-packing form used by the repository.

For unequal terminal subfamilies, restrict the larger side to a subset with the
same cardinality as the smaller side, apply the paper predicate, and then view
the resulting packing as one between the original larger terminal sets. -/
theorem nodeWellLinkedIn_of_paperNodeWellLinkedIn
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {C T : Finset V}
    (h : TreewidthSparsifier.PaperNodeWellLinkedIn G C T) :
    NodeWellLinkedIn G C T := by
  classical
  refine ⟨h.1, ?_⟩
  intro A B hA hB _hdisj
  by_cases hle : A.card ≤ B.card
  · rcases Finset.exists_subset_card_eq hle with ⟨B₀, hB₀sub, hB₀card⟩
    rcases h.2 hA (subset_trans hB₀sub hB) (by simp [hB₀card]) with
      ⟨P, hPstay⟩
    refine ⟨P.toPathPacking.widenTerminals subset_rfl hB₀sub, ?_, ?_⟩
    · calc
        (P.toPathPacking.widenTerminals subset_rfl hB₀sub).card =
            P.toPathPacking.card := rfl
        _ = P.card := P.toPathPacking_card
        _ = A.card := P.card_eq_left_card
        _ = min A.card B.card := (Nat.min_eq_left hle).symm
    · intro i
      simpa [PathPacking.widenTerminals] using hPstay i
  · have hB_le_A : B.card ≤ A.card := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    rcases Finset.exists_subset_card_eq hB_le_A with ⟨A₀, hA₀sub, hA₀card⟩
    rcases h.2 (subset_trans hA₀sub hA) hB (by simp [hA₀card]) with
      ⟨P, hPstay⟩
    refine ⟨P.toPathPacking.widenTerminals hA₀sub subset_rfl, ?_, ?_⟩
    · calc
        (P.toPathPacking.widenTerminals hA₀sub subset_rfl).card =
            P.toPathPacking.card := rfl
        _ = P.card := P.toPathPacking_card
        _ = B.card := P.card_eq_right_card
        _ = min A.card B.card := (Nat.min_eq_right hB_le_A).symm
    · intro i
      simpa [PathPacking.widenTerminals] using hPstay i

/-- The paper's equal-sized-subset linkedness implies the local linkedness
predicate used by the repository. -/
theorem nodeLinkedIn_of_paperLinkedIn
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {C A B : Finset V}
    (h : TreewidthSparsifier.PaperLinkedIn G C A B) :
    NodeLinkedIn G C A B := by
  classical
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro A' B' hA' hB'
  by_cases hle : A'.card ≤ B'.card
  · rcases Finset.exists_subset_card_eq hle with ⟨B₀, hB₀sub, hB₀card⟩
    rcases h.2.2.2 hA' (subset_trans hB₀sub hB') (by simp [hB₀card]) with
      ⟨P, hPstay⟩
    refine ⟨P.toPathPacking.widenTerminals subset_rfl hB₀sub, ?_, ?_⟩
    · calc
        (P.toPathPacking.widenTerminals subset_rfl hB₀sub).card =
            P.toPathPacking.card := rfl
        _ = P.card := P.toPathPacking_card
        _ = A'.card := P.card_eq_left_card
        _ = min A'.card B'.card := (Nat.min_eq_left hle).symm
    · intro i
      simpa [PathPacking.widenTerminals] using hPstay i
  · have hB_le_A : B'.card ≤ A'.card := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    rcases Finset.exists_subset_card_eq hB_le_A with ⟨A₀, hA₀sub, hA₀card⟩
    rcases h.2.2.2 (subset_trans hA₀sub hA') hB' (by simp [hA₀card]) with
      ⟨P, hPstay⟩
    refine ⟨P.toPathPacking.widenTerminals hA₀sub subset_rfl, ?_, ?_⟩
    · calc
        (P.toPathPacking.widenTerminals hA₀sub subset_rfl).card =
            P.toPathPacking.card := rfl
        _ = P.card := P.toPathPacking_card
        _ = B'.card := P.card_eq_right_card
        _ = min A'.card B'.card := (Nat.min_eq_right hB_le_A).symm
    · intro i
      simpa [PathPacking.widenTerminals] using hPstay i

/-- Bridge from the paper-literal path-of-sets contract to the repository's
existing projected path-of-sets structure.

This is definitional: the paper version states stronger equal-sized-subset
node-linkedness conditions, and the two lemmas above convert them to the local
maximum-packing predicates consumed downstream. -/
theorem strongPathOfSetsSystem_of_paperStrongPathOfSetsSystem :
    ∀ {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ},
      Nonempty (TreewidthSparsifier.PaperStrongPathOfSetsSystem G ell w) →
        Nonempty (StrongPathOfSetsSystem G ell w) := by
  intro V _ G ell w h
  rcases h with ⟨P⟩
  exact ⟨{
    toPathOfSetsSystem := P.toPathOfSetsSystem
    left_nodeWellLinked := fun i =>
      nodeWellLinkedIn_of_paperNodeWellLinkedIn (P.left_paperNodeWellLinked i)
    right_nodeWellLinked := fun i =>
      nodeWellLinkedIn_of_paperNodeWellLinkedIn (P.right_paperNodeWellLinked i)
    left_right_nodeLinked := fun i =>
      nodeLinkedIn_of_paperLinkedIn (P.left_right_paperLinked i) }⟩


/-- Appendix A.2 starting ingredient, proved from Theorem A.1 and Theorem A.2
in paper-shaped form.

There are universal constants `cStrong` and `cStrongLog` such that the
treewidth threshold

`cStrong * w * ell^50 * (log_2 k)^cStrongLog < k`

forces a subgraph of maximum degree at most three containing a strong
Path-of-Sets System of length `ell` and width `w`.

This packages Theorem A.1 and Theorem A.2 from Appendix A.2: the polylogarithmic
loss in the degree-three sparsifier is absorbed into `cStrongLog`, and the
constant losses are absorbed into `cStrong`.
-/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_path
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hpathInput :
      ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w k : ℕ},
            1 < ell →
              1 < w →
                1 < k →
                  k ≤ treewidth G →
                    cPath * w * ell ^ 50 *
                        (Nat.log 2 k) ^ cPathLog < k →
                      Nonempty (StrongPathOfSetsSystem G ell w)) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  rcases hsparseInput with
    ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, hsparse⟩
  rcases hpathInput with
    ⟨cPath, cPathLog, hcPath, hcPathLog, hpath⟩
  refine ⟨cSparse * (cPath + 1), cPathLog + cSparseLog,
    Nat.mul_pos hcSparse (Nat.succ_pos cPath), Nat.add_pos_left hcPathLog _, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  let L := Nat.log 2 k
  let A := w * ell ^ 50 * L ^ cPathLog
  let t := cPath * A + 1
  have hlog_pos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hA_pos : 0 < A := by
    dsimp [A]
    exact Nat.mul_pos
      (Nat.mul_pos (lt_trans Nat.zero_lt_one hw)
        (Nat.pow_pos (lt_trans Nat.zero_lt_one hell)))
      (Nat.pow_pos hlog_pos)
  have hA_one : 1 ≤ A := Nat.succ_le_of_lt hA_pos
  have ht_pos : 0 < t := by
    dsimp [t]
    omega
  have ht_gt_one : 1 < t := by
    have hmul_pos : 0 < cPath * A := Nat.mul_pos hcPath hA_pos
    dsimp [t]
    omega
  have ht_le_scaledA : t ≤ (cPath + 1) * A := by
    dsimp [t]
    calc
      cPath * A + 1 ≤ cPath * A + A := Nat.add_le_add_left hA_one _
      _ = (cPath + 1) * A := by ring
  have hspar_large :
      cSparse * t * L ^ cSparseLog < k := by
    have hle :
        cSparse * t * L ^ cSparseLog ≤
          (cSparse * (cPath + 1)) * w * ell ^ 50 *
            L ^ (cPathLog + cSparseLog) := by
      calc
        cSparse * t * L ^ cSparseLog
            = cSparse * (t * L ^ cSparseLog) := by ring
        _ ≤ cSparse * (((cPath + 1) * A) * L ^ cSparseLog) := by
                exact Nat.mul_le_mul_left cSparse
                  (Nat.mul_le_mul_right (L ^ cSparseLog) ht_le_scaledA)
        _ = cSparse * ((cPath + 1) * A) * L ^ cSparseLog := by ring
        _ = (cSparse * (cPath + 1)) * w * ell ^ 50 *
              L ^ (cPathLog + cSparseLog) := by
                dsimp [A]
                rw [Nat.pow_add]
                ring
    exact lt_of_le_of_lt hle (by simpa [L] using hlarge)
  have ht_le_product : t ≤ cSparse * t * L ^ cSparseLog := by
    have hfactor_pos : 0 < cSparse * L ^ cSparseLog :=
      Nat.mul_pos hcSparse (Nat.pow_pos hlog_pos)
    have hfactor_one : 1 ≤ cSparse * L ^ cSparseLog :=
      Nat.succ_le_of_lt hfactor_pos
    calc
      t = 1 * t := by simp
      _ ≤ (cSparse * L ^ cSparseLog) * t :=
        Nat.mul_le_mul_right t hfactor_one
      _ = cSparse * t * L ^ cSparseLog := by ring
  have ht_lt_k : t < k := lt_of_le_of_lt ht_le_product hspar_large
  have ht_le_k : t ≤ k := Nat.le_of_lt ht_lt_k
  rcases hsparse G hk htw hspar_large with
    ⟨H, hHG, hdegree, ht_treewidth⟩
  have hlog_t_le : Nat.log 2 t ≤ L := by
    simpa [L] using Nat.log_mono_right ht_le_k
  have hpath_large :
      cPath * w * ell ^ 50 * (Nat.log 2 t) ^ cPathLog < t := by
    have hpow_le : (Nat.log 2 t) ^ cPathLog ≤ L ^ cPathLog :=
      Nat.pow_le_pow_left hlog_t_le cPathLog
    have hle :
        cPath * w * ell ^ 50 * (Nat.log 2 t) ^ cPathLog ≤
          cPath * A := by
      calc
        cPath * w * ell ^ 50 * (Nat.log 2 t) ^ cPathLog
            ≤ cPath * w * ell ^ 50 * L ^ cPathLog := by
                exact Nat.mul_le_mul_left (cPath * w * ell ^ 50) hpow_le
        _ = cPath * A := by
              dsimp [A]
              ring
    have hterm_lt : cPath * A < t := by
      dsimp [t]
      omega
    exact lt_of_le_of_lt hle hterm_lt
  rcases hpath H hell hw ht_gt_one ht_treewidth hpath_large with ⟨P⟩
  exact ⟨H, hHG, hdegree, ⟨P⟩⟩


/-- Appendix A.2 starting ingredient from the degree-three sparsifier and the
source-route Chekuri--Chuzhoy obligations behind Theorem A.2.

This theorem contains no new axiom use beyond the explicit hypotheses.  It is
the plug-in point for replacing `exists_strongPathOfSets_of_treewidth` by the
formalized proof route through Chekuri--Chuzhoy Theorem 2.21 and Section 4. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_sources
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcore :
      ∃ cCore cCoreLog cDeg cDegLog : ℕ,
        ChekuriChuzhoy.NodeWellLinkedCoreFromTreewidth.{u}
          cCore cCoreLog cDeg cDegLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  have htree :
      ∃ cTree cTreeLog : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsWithBufferedPathFromTreewidth.{u}
          cTree cTreeLog :=
    Lax17Proofs.SimpleGraph.ChekuriChuzhoy.strongTreeOfSetsWithBufferedPathFromTreewidth_of_core_and_route
        hcore hroute
  have hpath :
      ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w k : ℕ},
            1 < ell →
              1 < w →
                1 < k →
                  k ≤ treewidth G →
                    cPath * w * ell ^ 50 *
                        (Nat.log 2 k) ^ cPathLog < k →
                      Nonempty (StrongPathOfSetsSystem G ell w) :=
    Lax17Proofs.SimpleGraph.ChekuriChuzhoy.exists_strongPathOfSets_of_treewidth_from_strongTreeOfSets
      htree
  exact exists_degreeThreeStrongPathOfSets_of_sparsifier_and_path
    hsparseInput hpath

/-- Appendix A.2 starting ingredient from the degree-three sparsifier,
Chekuri--Chuzhoy Theorem 2.21, and the faithful direct Section 4 route to a
strong path-of-sets system. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_pathRoute
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcore :
      ∃ cCore cCoreLog cDeg cDegLog : ℕ,
        ChekuriChuzhoy.NodeWellLinkedCoreFromTreewidth.{u}
          cCore cCoreLog cDeg cDegLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  have hpath :
      ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w k : ℕ},
            1 < ell →
              1 < w →
                1 < k →
                  k ≤ treewidth G →
                    cPath * w * ell ^ 50 *
                        (Nat.log 2 k) ^ cPathLog < k →
                      Nonempty (StrongPathOfSetsSystem G ell w) :=
    Lax17Proofs.SimpleGraph.ChekuriChuzhoy.exists_strongPathOfSets_of_treewidth_from_core_and_pathRoute
      hcore hroute
  exact exists_degreeThreeStrongPathOfSets_of_sparsifier_and_path
    hsparseInput hpath

/-- Appendix A.2 starting ingredient from the degree-three sparsifier and the
lower-level Chekuri--Chuzhoy Theorem 2.21 proof boundary.

Compared with
`exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_sources`,
this theorem does not take the node-well-linked core form of Theorem 2.21 as an
input.  It derives that form from the cut-well-linked low-degree core produced
by the cut-matching/AARV part of Appendix A.4, using the self-contained
Theorem 2.14 boosting formalization. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_route
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_sources
    hsparseInput
    (Lax17Proofs.SimpleGraph.ChekuriChuzhoy.nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore
      hcut)
    hroute

/-- Appendix A.2 starting ingredient from the degree-three sparsifier, the
cut-well-linked form of the Theorem 2.21 proof, and the faithful direct
Section 4 path route. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_pathRoute
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_pathRoute
    hsparseInput
    (Lax17Proofs.SimpleGraph.ChekuriChuzhoy.nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore
      hcut)
    hroute

/-- Appendix A.2 starting ingredient from the degree-three sparsifier, the
Lemma 2.17 routable-set source, the cut-matching/AARV embedding source, and
the Section 4 tree-of-sets route.

This exposes the lower-level source split of Chekuri--Chuzhoy Theorem 2.21
instead of taking the cut-well-linked core as a black-box hypothesis. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_route
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_route
    hsparseInput
    (Lax17Proofs.SimpleGraph.ChekuriChuzhoy.cutWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
      hroutable hcutMatching)
    hroute

/-- Appendix A.2 starting ingredient from the degree-three sparsifier, the
Lemma 2.17 routable-set source, the cut-matching/AARV embedding source, and
the faithful direct Section 4 path route. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_pathRoute
    hsparseInput
    (Lax17Proofs.SimpleGraph.ChekuriChuzhoy.cutWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
      hroutable hcutMatching)
    hroute

/-- Appendix A.2 starting ingredient from the degree-three sparsifier, Lemma
2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, and Theorem 4.6 extraction. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact
    exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      hsparseInput hroutable hcutMatching
      (Lax17Proofs.SimpleGraph.ChekuriChuzhoy.strongPathOfSetsFromNodeWellLinkedCore_of_strongTreeCore_and_extraction
        hbuild hextract)

/-- Appendix A.2 starting ingredient from the degree-three sparsifier, Lemma
2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, and the split proof of Theorem 4.6. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact
    exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      hsparseInput hroutable hcutMatching hbuild
      (Lax17Proofs.SimpleGraph.ChekuriChuzhoy.strongPathOfSetsFromStrongTreeOfSets_of_metaDichotomy_and_leafExtraction
        hdichotomy hleaf)

/-- Appendix A.2 starting ingredient from the degree-three sparsifier, Lemma
2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, the proved finite-tree dichotomy, and the
DFS/many-leaves branch of Theorem 4.6. -/
theorem exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact
    exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      hsparseInput hroutable hcutMatching hbuild
      (Lax17Proofs.SimpleGraph.ChekuriChuzhoy.strongPathOfSetsFromStrongTreeOfSets_of_leafExtraction
        hleaf)

/-- Appendix A.2 starting ingredient from Theorem A.1 in its paper-shaped
Omega form, Lemma 2.17 routability, the cut-matching/AARV embedding source,
and the faithful direct Section 4 path route. -/
theorem exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact
    exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      (degreeThreeTreewidthSparsifier_of_omega hsparseOmega)
      hroutable hcutMatching hroute

/-- Appendix A.2 starting ingredient from Theorem A.1 in its paper-shaped
Omega form, Lemma 2.17 routability, the cut-matching/AARV embedding source,
the Section 4 strong-tree construction, and Theorem 4.6 extraction. -/
theorem exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact
    exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      (degreeThreeTreewidthSparsifier_of_omega hsparseOmega)
      hroutable hcutMatching hbuild hextract

/-- Appendix A.2 starting ingredient from Theorem A.1 in its paper-shaped
Omega form, Lemma 2.17 routability, the cut-matching/AARV embedding source,
the Section 4 strong-tree construction, and the split proof of Theorem 4.6. -/
theorem exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact
    exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
      (degreeThreeTreewidthSparsifier_of_omega hsparseOmega)
      hroutable hcutMatching hbuild hdichotomy hleaf

/-- Appendix A.2 starting ingredient from Theorem A.1 in its paper-shaped
Omega form, Lemma 2.17 routability, the cut-matching/AARV embedding source,
the Section 4 strong-tree construction, the proved finite-tree dichotomy, and
the DFS/many-leaves branch of Theorem 4.6. -/
theorem exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cStrong * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cStrongLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (StrongPathOfSetsSystem H ell w) := by
  exact
    exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
      (degreeThreeTreewidthSparsifier_of_omega hsparseOmega)
      hroutable hcutMatching hbuild hleaf


end DegreeThreeStrongPathOfSetsContract
end SimpleGraph

end Lax17Proofs
