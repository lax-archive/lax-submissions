import Lax17Proofs.Source.ChekuriChuzhoySection5DisjointBundleSelection
import Lax17Proofs.Source.ChekuriChuzhoySection5RouterSkeleton

namespace Lax17Proofs

universe u v w

/-!
# Simultaneous selection in the Phase 1 router skeleton

This file adapts the source-sharp, pairwise-disjoint bundle transversal to the
router-valued skeleton produced by Theorem 5.10.  The selection is global:
one path is retained from every history group, while every requested
unoriented router pair retains a prescribed number of named copies.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5RouterSkeleton


open Finset
open ChekuriChuzhoySection5DisjointBundleSelection
open ChekuriChuzhoySection5Selection

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {n q : Nat} {cluster : Fin n → Finset V}

namespace RouterPathSkeleton

/-- The finite type of history groups in a router skeleton. -/
abbrev GroupIndex (S : RouterPathSkeleton G cluster) :=
  {U : Finset S.graph.Edge // U ∈ S.groups.parts}

/-- The unique history group containing a named skeleton edge. -/
noncomputable def groupOf
    (S : RouterPathSkeleton G cluster) (e : S.graph.Edge) :
    S.GroupIndex := by
  classical
  exact ⟨S.groups.part e, S.groups.part_mem.mpr (by simp)⟩

theorem groupOf_eq_iff_mem
    (S : RouterPathSkeleton G cluster)
    (e : S.graph.Edge) (U : S.GroupIndex) :
    S.groupOf e = U ↔ e ∈ U.1 := by
  classical
  constructor
  · intro h
    rw [← h]
    exact S.groups.mem_part (by simp)
  · intro he
    apply Subtype.ext
    exact S.groups.part_eq_of_mem U.2 he

theorem filter_groupOf_eq
    (S : RouterPathSkeleton G cluster) (U : S.GroupIndex) :
    (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = U) = U.1 := by
  classical
  ext e
  simp [S.groupOf_eq_iff_mem e U]

theorem image_groupOf_univ
    (S : RouterPathSkeleton G cluster) :
    (Finset.univ.image S.groupOf) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro U
  rcases S.groups.nonempty_of_mem_parts U.2 with ⟨e, he⟩
  exact Finset.mem_image.mpr
    ⟨e, Finset.mem_univ e, (S.groupOf_eq_iff_mem e U).2 he⟩

theorem groupFiber_card_le
    (S : RouterPathSkeleton G cluster) {k : Nat}
    (hsize : S.GroupSizeAtMost k) (U : S.GroupIndex) :
    (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = U).card ≤ k := by
  rw [S.filter_groupOf_eq U]
  exact hsize U.1 U.2

theorem isGroupTransversal_of_exact
    (S : RouterPathSkeleton G cluster)
    {selected : Finset S.graph.Edge}
    (hselected :
      IsExactGroupTransversal Finset.univ S.groupOf selected) :
    S.IsGroupTransversal selected := by
  classical
  intro U hU
  let g : S.GroupIndex := ⟨U, hU⟩
  have hg : g ∈ (Finset.univ : Finset S.graph.Edge).image S.groupOf := by
    rw [S.image_groupOf_univ]
    simp
  rcases hselected.existsUnique_mem_group hg with ⟨e, he, hunique⟩
  have heU : e ∈ U := (S.groupOf_eq_iff_mem e g).1 he.2
  have hsubset : selected ∩ U ⊆ {e} := by
    intro f hf
    have hfSelected := (Finset.mem_inter.mp hf).1
    have hfU := (Finset.mem_inter.mp hf).2
    have hfg : S.groupOf f = g := (S.groupOf_eq_iff_mem f g).2 hfU
    have hfe : f = e := hunique f ⟨hfSelected, hfg⟩
    simpa [hfe]
  have heInter : e ∈ selected ∩ U :=
    Finset.mem_inter.mpr ⟨he.1, heU⟩
  exact Finset.card_eq_one.mpr
    ⟨e, Finset.Subset.antisymm hsubset (by
      intro f hf
      have hfe : f = e := Finset.mem_singleton.mp hf
      simpa [hfe] using heInter)⟩

/-- The unoriented router pair carried by one named skeleton edge. -/
def edgeKey
    (S : RouterPathSkeleton G cluster) (e : S.graph.Edge) :
    Sym2 (Fin n) :=
  s(S.graph.left e, S.graph.right e)

/-- The named copies with one prescribed unoriented router pair. -/
noncomputable def edgeBundleKey
    (S : RouterPathSkeleton G cluster) (p : Sym2 (Fin n)) :
    Finset S.graph.Edge := by
  classical
  exact Finset.univ.filter fun e => S.edgeKey e = p

@[simp] theorem mem_edgeBundleKey
    (S : RouterPathSkeleton G cluster)
    {p : Sym2 (Fin n)} {e : S.graph.Edge} :
    e ∈ S.edgeBundleKey p ↔ S.edgeKey e = p := by
  simp [edgeBundleKey]

private theorem edgeKey_eq_of_joins
    (S : RouterPathSkeleton G cluster)
    {e : S.graph.Edge} {i j : Fin n}
    (h : S.graph.Joins e i j) :
    S.edgeKey e = s(i, j) := by
  rcases h with h | h
  · simp [edgeKey, h.1, h.2]
  · simpa [edgeKey, h.1, h.2, Sym2.eq_swap]

theorem edgeBundle_eq_edgeBundleKey
    (S : RouterPathSkeleton G cluster) (i j : Fin n) :
    S.edgeBundle i j = S.edgeBundleKey s(i, j) := by
  ext e
  simp only [RouterPathSkeleton.mem_edgeBundle, mem_edgeBundleKey]
  constructor
  · exact edgeKey_eq_of_joins S
  · intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩

theorem edgeBundleKey_disjoint_of_ne
    (S : RouterPathSkeleton G cluster)
    {p q : Sym2 (Fin n)} (hne : p ≠ q) :
    Disjoint (S.edgeBundleKey p) (S.edgeBundleKey q) := by
  rw [Finset.disjoint_left]
  intro e hep heq
  exact hne ((S.mem_edgeBundleKey.mp hep).symm.trans
    (S.mem_edgeBundleKey.mp heq))

/-- Bundles requested by the edges of a simple support graph. -/
noncomputable def supportBundles
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n)) :
    Finset (Finset S.graph.Edge) := by
  classical
  exact T.edgeFinset.image S.edgeBundleKey

theorem supportBundles_pairwiseDisjoint
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n)) :
    (↑(S.supportBundles T) : Set (Finset S.graph.Edge)).PairwiseDisjoint id := by
  classical
  intro B hB C hC hBC
  rcases Finset.mem_image.mp hB with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hC with ⟨q, hq, rfl⟩
  apply S.edgeBundleKey_disjoint_of_ne
  intro hpq
  apply hBC
  simpa [hpq]

/-- A global history-group transversal retaining `q` named paths on every
edge of a requested support graph. -/
structure SupportBundleTransversal
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n)) (q : Nat) where
  selected : Finset S.graph.Edge
  groupTransversal : S.IsGroupTransversal selected
  retained :
    ∀ i j : Fin n, T.Adj i j →
      q ≤ (selected ∩ S.edgeBundle i j).card

/-- Source-sharp simultaneous path selection on all support edges. -/
theorem exists_supportBundleTransversal
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    (hn : 0 < n)
    (hgroups : S.GroupSizeAtMost n)
    (hbundle :
      ∀ p ∈ T.edgeSet, n * q ≤ (S.edgeBundleKey p).card) :
    Nonempty (SupportBundleTransversal S T q) := by
  classical
  have hbundles :
      ∀ B ∈ S.supportBundles T,
        B ⊆ (Finset.univ : Finset S.graph.Edge) := by
    intro B hB
    exact Finset.subset_univ _
  have hgroupSize :
      ∀ g ∈ (Finset.univ : Finset S.graph.Edge).image S.groupOf,
        (Finset.univ.filter fun e : S.graph.Edge =>
          S.groupOf e = g).card ≤ n := by
    intro g _hg
    exact S.groupFiber_card_le hgroups g
  have hbundleSize :
      ∀ B ∈ S.supportBundles T, n * q ≤ B.card := by
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨p, hp, rfl⟩
    apply hbundle p
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hp
  rcases
      exists_exactGroupTransversal_retaining_pairwiseDisjoint_bundles
        (Finset.univ : Finset S.graph.Edge) S.groupOf
        (S.supportBundles T) n q hn hbundles
        (S.supportBundles_pairwiseDisjoint T) hgroupSize hbundleSize with
    ⟨selected, hselected, hretained⟩
  refine ⟨{
    selected := selected
    groupTransversal := S.isGroupTransversal_of_exact hselected
    retained := ?_ }⟩
  intro i j hij
  have hpair : s(i, j) ∈ T.edgeFinset := by
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hij
  have hbundleMem :
      S.edgeBundleKey s(i, j) ∈ S.supportBundles T :=
    Finset.mem_image.mpr ⟨s(i, j), hpair, rfl⟩
  simpa [S.edgeBundle_eq_edgeBundleKey i j] using
    hretained (S.edgeBundleKey s(i, j)) hbundleMem

end RouterPathSkeleton
end ChekuriChuzhoySection5RouterSkeleton
end SimpleGraph

end Lax17Proofs
