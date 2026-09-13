import Lax17Proofs.Source.Paths
import Lax17Proofs.Source.Section44
import Mathlib.Data.List.SplitBy

namespace Lax17Proofs

universe u v w

/-!
# Maximal one-side runs of a path

Claim 5.4 of `treewidth-sparsifier.pdf` deletes the edges of a vertex cut
from two path packings and uses the resulting path components.  This module
implements that operation directly on the support list of a `GraphPath`.
The `splitBy` relation changes group exactly when membership in the chosen
side changes, so its selected groups are precisely the maximal contiguous
pieces on that side.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace PathRuns


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Adjacent vertices belong to the same run exactly when their membership
in `X` agrees. -/
def sameSide (X : Finset V) (u v : V) : Bool :=
  decide (u ∈ X ↔ v ∈ X)

/-- The maximal constant-membership runs of a path support list. -/
noncomputable def groups (Q : GraphPath G) (X : Finset V) :
    List (List V) :=
  Q.walk.support.splitBy (sameSide X)

@[simp] theorem flatten_groups (Q : GraphPath G) (X : Finset V) :
    (groups Q X).flatten = Q.walk.support := by
  classical
  exact List.flatten_splitBy _ _

/-- The run at a finite position in `groups`. -/
noncomputable def runAt (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) : List V :=
  (groups Q X).get i

theorem runAt_mem_groups (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    runAt Q X i ∈ groups Q X :=
  List.get_mem _ i

theorem runAt_ne_nil (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    runAt Q X i ≠ [] := by
  classical
  exact List.ne_nil_of_mem_splitBy (runAt_mem_groups Q X i)

/-- Each run is a contiguous sublist of the original path support. -/
theorem runAt_isInfix (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    runAt Q X i <:+: Q.walk.support := by
  classical
  rcases
      List.eq_append_cons_of_mem (runAt_mem_groups Q X i) with
    ⟨before, after, hgroups, _hnot⟩
  refine ⟨before.flatten, after.flatten, ?_⟩
  rw [← flatten_groups Q X, hgroups]
  simp only [List.flatten_append, List.flatten_cons]
  simp [List.append_assoc]

/-- A contiguous run inherits adjacency from the original walk. -/
theorem runAt_isChain_adj (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    (runAt Q X i).IsChain G.Adj := by
  classical
  exact Q.walk.isChain_adj_support.infix (runAt_isInfix Q X i)

/-- Consecutive runs meet across an actual graph edge. -/
theorem groups_isChain_adj (Q : GraphPath G) (X : Finset V) :
    (groups Q X).IsChain fun a b =>
      ∀ ha : a ≠ [], ∀ hb : b ≠ [],
        G.Adj (a.getLast ha) (b.head hb) := by
  classical
  have hnil : [] ∉ groups Q X := by
    exact List.nil_notMem_splitBy _ _
  have hchain :
      (groups Q X).flatten.IsChain G.Adj := by
    rw [flatten_groups]
    exact Q.walk.isChain_adj_support
  have h := (List.isChain_flatten hnil).mp hchain |>.2
  apply h.imp
  intro a b hab ha hb
  exact hab (a.getLast ha) (List.getLast_mem_getLast? ha)
    (b.head hb) (List.head_mem_head? hb)

/-- Membership in `X` changes between consecutive maximal runs. -/
theorem groups_isChain_changesSide (Q : GraphPath G) (X : Finset V) :
    (groups Q X).IsChain fun a b =>
      ∀ ha : a ≠ [], ∀ hb : b ≠ [],
        ¬((a.getLast ha ∈ X) ↔ (b.head hb ∈ X)) := by
  classical
  have h :=
    List.isChain_getLast_head_splitBy
      (sameSide X) Q.walk.support
  apply h.imp
  rintro a b ⟨ha, hb, hchange⟩ ha' hb'
  simpa [sameSide] using hchange

/-- The graph path represented by one maximal run. -/
noncomputable def runPath (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) : GraphPath G := by
  let r := runAt Q X i
  let hne : r ≠ [] := runAt_ne_nil Q X i
  let hchain : r.IsChain G.Adj := runAt_isChain_adj Q X i
  exact {
    source := r.head hne
    target := r.getLast hne
    walk := _root_.SimpleGraph.Walk.ofSupport r hne hchain
    isPath := by
      have hsupp :
          (_root_.SimpleGraph.Walk.ofSupport r hne hchain).support.Nodup := by
        rw [_root_.SimpleGraph.Walk.support_ofSupport]
        exact (runAt_isInfix Q X i).nodup Q.isPath.support_nodup
      exact
        ⟨⟨_root_.SimpleGraph.Walk.edges_nodup_of_support_nodup hsupp⟩,
          hsupp⟩
  }

@[simp] theorem runPath_support (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    (runPath Q X i).walk.support = runAt Q X i := by
  classical
  simp [runPath]

@[simp] theorem runPath_vertexSet (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    (runPath Q X i).vertexSet = (runAt Q X i).toFinset := by
  classical
  simp [GraphPath.vertexSet]

/-- A run path is a contiguous subwalk of its original path. -/
theorem runPath_isSubwalk (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    (runPath Q X i).walk.IsSubwalk Q.walk := by
  rw [_root_.SimpleGraph.Walk.isSubwalk_iff_support_isInfix,
    runPath_support]
  exact runAt_isInfix Q X i

/-- In particular, every run edge is an edge of the original path. -/
theorem runPath_edgeSet_subset_original
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    (runPath Q X i).edgeSet ⊆ Q.edgeSet := by
  classical
  intro e he
  have heWalk : e ∈ (runPath Q X i).walk.edges := by
    simpa [GraphPath.edgeSet] using he
  have heOriginal : e ∈ Q.walk.edges :=
    (runPath_isSubwalk Q X i).edges_subset heWalk
  simpa [GraphPath.edgeSet] using heOriginal

private theorem all_mem_of_sameSide_chain :
    ∀ (a : V) (xs : List V) (X : Finset V),
      (a :: xs).IsChain (fun u v => sameSide X u v) →
        a ∈ X →
          ∀ v ∈ a :: xs, v ∈ X
  | a, [], _X, _hchain, ha => by simpa using ha
  | a, b :: xs, X, hchain, ha => by
      have hab : a ∈ X ↔ b ∈ X := by
        have := hchain.rel
        simpa [sameSide] using this
      have hb : b ∈ X := hab.mp ha
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ha
      · exact all_mem_of_sameSide_chain b xs X hchain.of_cons hb v hv

private theorem all_not_mem_of_sameSide_chain :
    ∀ (a : V) (xs : List V) (X : Finset V),
      (a :: xs).IsChain (fun u v => sameSide X u v) →
        a ∉ X →
          ∀ v ∈ a :: xs, v ∉ X
  | a, [], _X, _hchain, ha => by simpa using ha
  | a, b :: xs, X, hchain, ha => by
      have hab : a ∈ X ↔ b ∈ X := by
        have := hchain.rel
        simpa [sameSide] using this
      have hb : b ∉ X := by
        intro hbX
        exact ha (hab.mpr hbX)
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ha
      · exact all_not_mem_of_sameSide_chain b xs X
          hchain.of_cons hb v hv

/-- A run whose first vertex lies in `X` lies wholly in `X`. -/
theorem runAt_subset_of_head_mem
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length)
    (hi : (runAt Q X i).head (runAt_ne_nil Q X i) ∈ X) :
    (runAt Q X i).toFinset ⊆ X := by
  classical
  intro v hv
  have hmem : v ∈ runAt Q X i := by simpa using hv
  cases hr : runAt Q X i with
  | nil =>
      exact False.elim ((runAt_ne_nil Q X i) hr)
  | cons a xs =>
      have hhead : a ∈ X := by simpa [hr] using hi
      have hchain : (a :: xs).IsChain (fun u v => sameSide X u v) := by
        simpa [hr] using
          (List.isChain_of_mem_splitBy (runAt_mem_groups Q X i))
      exact all_mem_of_sameSide_chain a xs X hchain hhead v
        (by simpa [hr] using hmem)

theorem runAt_eq_support_of_groups_length_eq_one
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length)
    (hone : (groups Q X).length = 1) :
    runAt Q X i = Q.walk.support := by
  classical
  have hi : i = ⟨0, by omega⟩ := by
    apply Fin.ext
    omega
  subst i
  have hgroups := List.eq_cons_of_length_one hone
  have hflat :
      [(groups Q X).get ⟨0, by omega⟩].flatten =
        Q.walk.support := by
    calc
      [(groups Q X).get ⟨0, by omega⟩].flatten =
          (groups Q X).flatten := by
        congr
        exact hgroups.symm
      _ = Q.walk.support := flatten_groups Q X
  change (groups Q X).get ⟨0, by omega⟩ = Q.walk.support
  simpa using hflat

/-- A selected inside run of a path which is not wholly inside has an
incident path edge crossing the vertex cut. -/
structure RunBoundaryWitness
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) where
  inside : V
  outside : V
  inside_mem_run : inside ∈ runAt Q X i
  inside_mem_side : inside ∈ X
  outside_not_mem_side : outside ∉ X
  adj : G.Adj inside outside

/-- Construct the cut edge charged to a non-whole inside run.  Except for
the first run, use its entering edge; for the first run, use its leaving
edge. -/
noncomputable def runBoundaryWitness
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length)
    (hi : (runAt Q X i).head (runAt_ne_nil Q X i) ∈ X)
    (hnot : ¬ Q.vertexSet ⊆ X) :
    RunBoundaryWitness Q X i := by
  classical
  let L := groups Q X
  by_cases hzero : i.1 = 0
  · have hlen : 1 < L.length := by
      have hpos : 0 < L.length := by
        change 0 < (groups Q X).length
        omega
      by_contra hnotlt
      have hone : L.length = 1 := by omega
      apply hnot
      intro v hv
      have hv' : v ∈ Q.walk.support := by
        simpa [GraphPath.vertexSet] using hv
      have hrun : runAt Q X i = Q.walk.support :=
        runAt_eq_support_of_groups_length_eq_one Q X i hone
      have hvRun : v ∈ runAt Q X i := by simpa [hrun] using hv'
      exact runAt_subset_of_head_mem Q X i hi (by simpa using hvRun)
    let next : Fin L.length := ⟨1, hlen⟩
    have hcur : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    have hrelAdj :=
      (List.isChain_iff_getElem.mp (groups_isChain_adj Q X))
        0 (by simpa [L] using hlen)
    have hrelChange :=
      (List.isChain_iff_getElem.mp (groups_isChain_changesSide Q X))
        0 (by simpa [L] using hlen)
    have hcurNe : L[0] ≠ [] := by
      exact List.ne_nil_of_mem_splitBy
        (by
          change L[0] ∈ L
          exact List.getElem_mem (by omega))
    have hnextNe : L[1] ≠ [] := by
      exact List.ne_nil_of_mem_splitBy
        (by
          change L[1] ∈ L
          exact List.getElem_mem (by omega))
    have hlastIn : L[0].getLast hcurNe ∈ X := by
      have hsub :=
        runAt_subset_of_head_mem Q X i hi
      apply hsub
      have : L[0].getLast hcurNe ∈ L[0] :=
        List.getLast_mem hcurNe
      simpa [runAt, L, hcur] using this
    have hnextOut : L[1].head hnextNe ∉ X := by
      intro hnextIn
      exact hrelChange hcurNe hnextNe
        ⟨fun _ => hnextIn, fun _ => hlastIn⟩
    exact {
      inside := L[0].getLast hcurNe
      outside := L[1].head hnextNe
      inside_mem_run := by
        have : L[0].getLast hcurNe ∈ L[0] :=
          List.getLast_mem hcurNe
        simpa [runAt, L, hcur] using this
      inside_mem_side := hlastIn
      outside_not_mem_side := hnextOut
      adj := hrelAdj hcurNe hnextNe
    }
  · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hzero
    let prev : Fin L.length := ⟨i.1 - 1, by
      dsimp [L]
      omega⟩
    have hstep : i.1 - 1 + 1 = i.1 := by omega
    have hrelAdj :=
      (List.isChain_iff_getElem.mp (groups_isChain_adj Q X))
        (i.1 - 1) (by
          rw [hstep]
          exact i.2)
    have hrelChange :=
      (List.isChain_iff_getElem.mp (groups_isChain_changesSide Q X))
        (i.1 - 1) (by
          rw [hstep]
          exact i.2)
    have hprevNe : L[i.1 - 1] ≠ [] := by
      exact List.ne_nil_of_mem_splitBy
        (by
          change L[i.1 - 1] ∈ L
          exact List.getElem_mem (by
            dsimp [L]
            omega))
    have hcurNe : L[i.1] ≠ [] := by
      exact List.ne_nil_of_mem_splitBy
        (by
          change L[i.1] ∈ L
          exact List.getElem_mem i.2)
    have hrelAdj' :
        ∀ (ha : L[i.1 - 1] ≠ []) (hb : L[i.1] ≠ []),
          G.Adj (L[i.1 - 1].getLast ha) (L[i.1].head hb) := by
      simpa only [L, hstep] using hrelAdj
    have hrelChange' :
        ∀ (ha : L[i.1 - 1] ≠ []) (hb : L[i.1] ≠ []),
          ¬(L[i.1 - 1].getLast ha ∈ X ↔
            L[i.1].head hb ∈ X) := by
      simpa only [L, hstep] using hrelChange
    have hheadIn : L[i.1].head hcurNe ∈ X := by
      simpa [runAt, L, List.get_eq_getElem] using hi
    have hprevOut : L[i.1 - 1].getLast hprevNe ∉ X := by
      intro hprevIn
      have hbad := hrelChange' hprevNe hcurNe
      exact hbad ⟨fun _ => hheadIn, fun _ => hprevIn⟩
    exact {
      inside := L[i.1].head hcurNe
      outside := L[i.1 - 1].getLast hprevNe
      inside_mem_run := by
        have : L[i.1].head hcurNe ∈ L[i.1] :=
          List.head_mem hcurNe
        simpa [runAt, L, List.get_eq_getElem] using this
      inside_mem_side := hheadIn
      outside_not_mem_side := hprevOut
      adj := by
        have h := hrelAdj' hprevNe hcurNe
        exact h.symm
    }

/-- Indices of the maximal runs lying in `X`. -/
noncomputable def insideIndices (Q : GraphPath G) (X : Finset V) :
    Finset (Fin (groups Q X).length) := by
  classical
  exact Finset.univ.filter fun i =>
    (runAt Q X i).head (runAt_ne_nil Q X i) ∈ X

@[simp] theorem mem_insideIndices
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    i ∈ insideIndices Q X ↔
      (runAt Q X i).head (runAt_ne_nil Q X i) ∈ X := by
  classical
  simp [insideIndices]

/-- The finite type of maximal path pieces contained in `X`. -/
abbrev InsideIndex (Q : GraphPath G) (X : Finset V) :=
  {i : Fin (groups Q X).length // i ∈ insideIndices Q X}

theorem inside_runPath_vertexSet_subset
    (Q : GraphPath G) (X : Finset V)
    (i : InsideIndex Q X) :
    (runPath Q X i.1).vertexSet ⊆ X := by
  rw [runPath_vertexSet]
  exact runAt_subset_of_head_mem Q X i.1
    ((mem_insideIndices Q X i.1).mp i.2)

/-- Every path vertex lying on the selected side belongs to a unique selected
run. -/
theorem exists_insideIndex_of_mem
    (Q : GraphPath G) (X : Finset V) {v : V}
    (hvQ : v ∈ Q.vertexSet) (hvX : v ∈ X) :
    ∃ i : InsideIndex Q X,
      v ∈ (runPath Q X i.1).vertexSet := by
  classical
  have hvSupport : v ∈ Q.walk.support := by
    simpa [GraphPath.vertexSet] using hvQ
  have hvFlatten : v ∈ (groups Q X).flatten := by
    simpa using hvSupport
  rcases List.mem_flatten.mp hvFlatten with ⟨r, hrGroups, hvr⟩
  rcases List.get_of_mem hrGroups with ⟨i, hi⟩
  have hvrun : v ∈ runAt Q X i := by
    rw [runAt, hi]
    exact hvr
  have hhead :
      (runAt Q X i).head (runAt_ne_nil Q X i) ∈ X := by
    by_contra hnot
    cases hr : runAt Q X i with
    | nil => exact False.elim ((runAt_ne_nil Q X i) hr)
    | cons a xs =>
        have hheadNot : a ∉ X := by
          simpa [hr] using hnot
        have hchain :
            (a :: xs).IsChain (fun u w => sameSide X u w) := by
          simpa [hr] using
            (List.isChain_of_mem_splitBy (runAt_mem_groups Q X i))
        have hvList : v ∈ a :: xs := by
          simpa [hr] using hvrun
        exact
          (all_not_mem_of_sameSide_chain a xs X hchain
            hheadNot v hvList) hvX
  let inside : InsideIndex Q X :=
    ⟨i, (mem_insideIndices Q X i).2 hhead⟩
  refine ⟨inside, ?_⟩
  rw [runPath_vertexSet]
  simpa [inside] using hvrun

/-- Different maximal runs of one simple path are vertex-disjoint. -/
theorem runPath_nodeDisjoint
    (Q : GraphPath G) (X : Finset V)
    {i j : Fin (groups Q X).length} (hij : i ≠ j) :
    GraphPath.NodeDisjoint (runPath Q X i) (runPath Q X j) := by
  classical
  rw [GraphPath.NodeDisjoint, runPath_vertexSet, runPath_vertexSet,
    Finset.disjoint_left]
  have hflatNodup : (groups Q X).flatten.Nodup := by
    rw [flatten_groups]
    exact Q.isPath.support_nodup
  have hpw : (groups Q X).Pairwise List.Disjoint :=
    (List.nodup_flatten.mp hflatNodup).2
  have hdisj :
      List.Disjoint (runAt Q X i) (runAt Q X j) := by
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hpw.rel_get_of_lt hijlt
    · exact (hpw.rel_get_of_lt hjilt).symm
  intro v hvi hvj
  exact hdisj (by simpa using hvi) (by simpa using hvj)

/-- The edge charged to a non-whole inside run. -/
noncomputable def runBoundaryEdge
    (Q : GraphPath G) (X : Finset V)
    (i : InsideIndex Q X)
    (hnot : ¬ Q.vertexSet ⊆ X) : Sym2 V :=
  let w :=
    runBoundaryWitness Q X i.1
      ((mem_insideIndices Q X i.1).mp i.2) hnot
  s(w.inside, w.outside)

theorem runBoundaryEdge_mem_edgeBoundary
    (Q : GraphPath G) (X : Finset V)
    (i : InsideIndex Q X)
    (hnot : ¬ Q.vertexSet ⊆ X) :
    runBoundaryEdge Q X i hnot ∈
      Section44.edgeBoundary G X Xᶜ := by
  classical
  let w :=
    runBoundaryWitness Q X i.1
      ((mem_insideIndices Q X i.1).mp i.2) hnot
  rw [Section44.mem_edgeBoundary]
  refine ⟨?_, w.inside, w.inside_mem_side,
    w.outside, by simpa using w.outside_not_mem_side, rfl⟩
  change s(w.inside, w.outside) ∈ G.edgeSet
  rw [_root_.SimpleGraph.mem_edgeSet]
  exact w.adj

/-- Different non-whole inside runs charge different cut edges. -/
theorem runBoundaryEdge_injective
    (Q : GraphPath G) (X : Finset V)
    (hnot : ¬ Q.vertexSet ⊆ X) :
    Function.Injective fun i : InsideIndex Q X =>
      runBoundaryEdge Q X i hnot := by
  classical
  intro i j hij
  let wi :=
    runBoundaryWitness Q X i.1
      ((mem_insideIndices Q X i.1).mp i.2) hnot
  let wj :=
    runBoundaryWitness Q X j.1
      ((mem_insideIndices Q X j.1).mp j.2) hnot
  have hedge : s(wi.inside, wi.outside) =
      s(wj.inside, wj.outside) := by
    simpa [runBoundaryEdge, wi, wj] using hij
  have hins : wi.inside = wj.inside := by
    rw [Sym2.eq_iff] at hedge
    rcases hedge with hdirect | hswap
    · exact hdirect.1
    · exact False.elim
        (wi.outside_not_mem_side (hswap.2 ▸ wj.inside_mem_side))
  apply Subtype.ext
  by_contra hindex
  have hdisj := runPath_nodeDisjoint Q X hindex
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left] at hdisj
  exact hdisj
    (by
      rw [runPath_vertexSet]
      simpa using wi.inside_mem_run)
    (by
      rw [hins, runPath_vertexSet]
      simpa using wj.inside_mem_run)

/-- A path not wholly contained in `X` has at most one inside run per
crossing edge. -/
theorem insideIndices_card_le_edgeBoundary
    (Q : GraphPath G) (X : Finset V)
    (hnot : ¬ Q.vertexSet ⊆ X) :
    (insideIndices Q X).card ≤
      (Section44.edgeBoundary G X Xᶜ).card := by
  classical
  let f :
      InsideIndex Q X →
        {e : Sym2 V // e ∈ Section44.edgeBoundary G X Xᶜ} :=
    fun i => ⟨runBoundaryEdge Q X i hnot,
      runBoundaryEdge_mem_edgeBoundary Q X i hnot⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply runBoundaryEdge_injective Q X hnot
    exact congrArg Subtype.val hij
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- A path wholly contained in `X` consists of exactly one inside run. -/
theorem groups_length_eq_one_of_vertexSet_subset
    (Q : GraphPath G) (X : Finset V)
    (hsub : Q.vertexSet ⊆ X) :
    (groups Q X).length = 1 := by
  classical
  have hall : ∀ v ∈ Q.walk.support, v ∈ X := by
    intro v hv
    exact hsub (by simpa [GraphPath.vertexSet] using hv)
  have hchain :
      Q.walk.support.IsChain fun u v => sameSide X u v := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [sameSide, decide_eq_true_eq]
    exact ⟨fun _ => hall _ (List.getElem_mem (by omega)),
      fun _ => hall _ (List.getElem_mem (by omega))⟩
  rw [groups, List.splitBy_of_isChain Q.walk.support_ne_nil hchain]
  simp

theorem insideIndex_eq_of_vertexSet_subset
    (Q : GraphPath G) (X : Finset V)
    (hsub : Q.vertexSet ⊆ X)
    (i j : InsideIndex Q X) :
    i = j := by
  apply Subtype.ext
  apply Fin.ext
  have hone := groups_length_eq_one_of_vertexSet_subset Q X hsub
  omega

/-- The selected inside runs of one path, viewed as a path packing. -/
noncomputable def insidePacking (Q : GraphPath G) (X : Finset V) :
    PathPacking G Finset.univ Finset.univ where
  Index := InsideIndex Q X
  path := fun i => runPath Q X i.1
  connects := by
    intro i
    exact Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  node_disjoint := by
    intro i j hij
    exact runPath_nodeDisjoint Q X
      (fun h => hij (Subtype.ext h))

/-- The maximal inside pieces of one path form a perfect routing between
their own oriented endpoint sets. -/
noncomputable def insidePerfectPacking
    (Q : GraphPath G) (X : Finset V) :
    PerfectPathPacking G
      (insidePacking Q X).sourceSet
      (insidePacking Q X).targetSet :=
  (insidePacking Q X).toPerfectUsedTerminals

@[simp] theorem insidePerfectPacking_card
    (Q : GraphPath G) (X : Finset V) :
    (insidePerfectPacking Q X).card =
      (insideIndices Q X).card := by
  classical
  change Fintype.card (InsideIndex Q X) = (insideIndices Q X).card
  rw [Fintype.card_coe]

/-! ## Restricting an entire packing -/

/-- A run stays inside the vertex set of its original packed path. -/
theorem runPath_vertexSet_subset_original
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    (runPath Q X i).vertexSet ⊆ Q.vertexSet := by
  classical
  rw [runPath_vertexSet]
  intro v hv
  have hvList : v ∈ runAt Q X i := by simpa using hv
  have hvSupport : v ∈ Q.walk.support :=
    (runAt_isInfix Q X i).mem hvList
  simpa [GraphPath.vertexSet] using hvSupport

/-- An inside run is named by its original packed path and its run index. -/
abbrev PackingInsideIndex
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :=
  Σ r : P.Index, InsideIndex (P.path r) X

/-- Original paths which actually meet the selected side. -/
noncomputable def meetingIndices
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    Finset P.Index := by
  classical
  exact Finset.univ.filter fun r =>
    ((P.path r).vertexSet ∩ X).Nonempty

abbrev MeetingIndex
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :=
  {r : P.Index // r ∈ meetingIndices P X}

@[simp] theorem mem_meetingIndices
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V)
    (r : P.Index) :
    r ∈ meetingIndices P X ↔
      ((P.path r).vertexSet ∩ X).Nonempty := by
  classical
  simp [meetingIndices]

/-- Original paths lying wholly on the selected side. -/
noncomputable def wholeIndices
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    Finset P.Index := by
  classical
  exact Finset.univ.filter fun r => (P.path r).vertexSet ⊆ X

abbrev WholeIndex
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :=
  {r : P.Index // r ∈ wholeIndices P X}

@[simp] theorem mem_wholeIndices
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V)
    (r : P.Index) :
    r ∈ wholeIndices P X ↔ (P.path r).vertexSet ⊆ X := by
  classical
  simp [wholeIndices]

/-- Charge a whole path to its path index and every run of a non-whole path
to its selected cut edge. -/
noncomputable def packingRunCharge
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    PackingInsideIndex P X →
      WholeIndex P X ⊕
        {e : Sym2 V // e ∈ Section44.edgeBoundary G X Xᶜ} :=
  fun q =>
    if hwhole : (P.path q.1).vertexSet ⊆ X then
      Sum.inl ⟨q.1, (mem_wholeIndices P X q.1).2 hwhole⟩
    else
      Sum.inr
        ⟨runBoundaryEdge (P.path q.1) X q.2 hwhole,
          runBoundaryEdge_mem_edgeBoundary
            (P.path q.1) X q.2 hwhole⟩

theorem packingRunCharge_injective
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    Function.Injective (packingRunCharge P X) := by
  classical
  intro q r hqr
  by_cases hqWhole : (P.path q.1).vertexSet ⊆ X
  · by_cases hrWhole : (P.path r.1).vertexSet ⊆ X
    · have hbase : q.1 = r.1 := by
        have h := congrArg
          (fun z :
                WholeIndex P X ⊕
                  {e : Sym2 V //
                    e ∈ Section44.edgeBoundary G X Xᶜ} =>
              z.elim Subtype.val (fun _ => q.1))
            hqr
        simpa [packingRunCharge, hqWhole, hrWhole] using h
      cases q with
      | mk qi qs =>
          cases r with
          | mk ri rs =>
              dsimp only at hbase ⊢
              subst ri
              have hrs :
                  (P.path qi).vertexSet ⊆ X := hrWhole
              have hrun :
                  qs = rs :=
                insideIndex_eq_of_vertexSet_subset
                  (P.path qi) X hrs qs rs
              subst rs
              rfl
    · simp [packingRunCharge, hqWhole, hrWhole] at hqr
  · by_cases hrWhole : (P.path r.1).vertexSet ⊆ X
    · simp [packingRunCharge, hqWhole, hrWhole] at hqr
    · have hedge :
          runBoundaryEdge (P.path q.1) X q.2 hqWhole =
            runBoundaryEdge (P.path r.1) X r.2 hrWhole := by
        have hsum :
            (Sum.inr
                ⟨runBoundaryEdge (P.path q.1) X q.2 hqWhole,
                  runBoundaryEdge_mem_edgeBoundary
                    (P.path q.1) X q.2 hqWhole⟩ :
              WholeIndex P X ⊕
                {e : Sym2 V //
                  e ∈ Section44.edgeBoundary G X Xᶜ}) =
              (Sum.inr
                ⟨runBoundaryEdge (P.path r.1) X r.2 hrWhole,
                  runBoundaryEdge_mem_edgeBoundary
                    (P.path r.1) X r.2 hrWhole⟩ :
              WholeIndex P X ⊕
                {e : Sym2 V //
                  e ∈ Section44.edgeBoundary G X Xᶜ}) := by
          simpa [packingRunCharge, hqWhole, hrWhole] using hqr
        exact congrArg Subtype.val (Sum.inr_injective hsum)
      by_cases hbase : q.1 = r.1
      · cases q with
        | mk qi qs =>
            cases r with
            | mk ri rs =>
                dsimp only at hbase ⊢
                subst ri
                have hedge' :
                    runBoundaryEdge (P.path qi) X qs hqWhole =
                      runBoundaryEdge (P.path qi) X rs hrWhole :=
                  hedge
                have hrun :
                    qs = rs := by
                  apply runBoundaryEdge_injective
                    (P.path qi) X hqWhole
                  exact hedge'
                subst rs
                rfl
      · let wq :=
          runBoundaryWitness (P.path q.1) X q.2.1
            ((mem_insideIndices (P.path q.1) X q.2.1).mp q.2.2)
            hqWhole
        let wr :=
          runBoundaryWitness (P.path r.1) X r.2.1
            ((mem_insideIndices (P.path r.1) X r.2.1).mp r.2.2)
            hrWhole
        have hedge' :
            s(wq.inside, wq.outside) =
              s(wr.inside, wr.outside) := by
          simpa [runBoundaryEdge, wq, wr] using hedge
        have hins : wq.inside = wr.inside := by
          rw [Sym2.eq_iff] at hedge'
          rcases hedge' with hdirect | hswap
          · exact hdirect.1
          · exact False.elim
              (wq.outside_not_mem_side
                (hswap.2 ▸ wr.inside_mem_side))
        have hqMem :
            wq.inside ∈ (P.path q.1).vertexSet := by
          have :
              wq.inside ∈
                (runPath (P.path q.1) X q.2.1).vertexSet := by
            rw [runPath_vertexSet]
            simpa using wq.inside_mem_run
          exact
            runPath_vertexSet_subset_original
              (P.path q.1) X q.2.1 this
        have hrMem :
            wq.inside ∈ (P.path r.1).vertexSet := by
          rw [hins]
          have :
              wr.inside ∈
                (runPath (P.path r.1) X r.2.1).vertexSet := by
            rw [runPath_vertexSet]
            simpa using wr.inside_mem_run
          exact
            runPath_vertexSet_subset_original
              (P.path r.1) X r.2.1 this
        exact False.elim
          (Finset.disjoint_left.mp (P.node_disjoint hbase)
            hqMem hrMem)

/-- All maximal pieces of all paths of `P` which lie in `X`.

The endpoints are temporarily declared to lie in `univ`; the canonical
`toPerfectUsedTerminals` operation below replaces these by the exact endpoint
sets. -/
noncomputable def packingInside
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    PathPacking G Finset.univ Finset.univ where
  Index := PackingInsideIndex P X
  path := fun q => runPath (P.path q.1) X q.2.1
  connects := by
    intro q
    exact Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  node_disjoint := by
    intro q r hqr
    classical
    by_cases hbase : q.1 = r.1
    · cases q with
      | mk qi qs =>
          cases r with
          | mk ri rs =>
              dsimp only at hbase ⊢
              subst ri
              exact runPath_nodeDisjoint (P.path qi) X
                (fun hrun =>
                  hqr (Sigma.ext rfl (heq_of_eq (Subtype.ext hrun))))
    · rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro v hvq hvr
      have hvq' : v ∈ (P.path q.1).vertexSet :=
        runPath_vertexSet_subset_original
          (P.path q.1) X q.2.1 hvq
      have hvr' : v ∈ (P.path r.1).vertexSet :=
        runPath_vertexSet_subset_original
          (P.path r.1) X r.2.1 hvr
      exact Finset.disjoint_left.mp (P.node_disjoint hbase) hvq' hvr'

/-- Across a node-disjoint packing, the number of inside pieces is at most
the number of original paths plus the size of the ambient cut. -/
theorem packingInside_card_le
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    (packingInside P X).card ≤
      (wholeIndices P X).card +
        (Section44.edgeBoundary G X Xᶜ).card := by
  classical
  have hcard :=
    Fintype.card_le_of_injective
      (packingRunCharge P X)
      (packingRunCharge_injective P X)
  change Fintype.card (PackingInsideIndex P X) ≤
    (wholeIndices P X).card +
      (Section44.edgeBoundary G X Xᶜ).card
  simpa only [Fintype.card_coe, Fintype.card_sum] using hcard

/-- The exact endpoint routing formed by all inside runs of a packing. -/
noncomputable def packingInsidePerfect
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    PerfectPathPacking G
      (packingInside P X).sourceSet
      (packingInside P X).targetSet :=
  (packingInside P X).toPerfectUsedTerminals

@[simp] theorem packingInsidePerfect_card
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    (packingInsidePerfect P X).card =
      ∑ r : P.Index, (insideIndices (P.path r) X).card := by
  classical
  change Fintype.card (PackingInsideIndex P X) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Fintype.card_coe]

/-- Every path in the restricted routing stays on the selected side. -/
theorem packingInside_staysIn
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    (packingInside P X).StaysIn X := by
  intro q
  exact inside_runPath_vertexSet_subset (P.path q.1) X q.2

/-- The exact endpoint routing of the inside runs stays on the selected
side as well. -/
theorem packingInsidePerfect_staysIn
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    (packingInsidePerfect P X).toPathPacking.StaysIn X := by
  exact
    (packingInside P X).toPerfectUsedTerminals_staysIn
      (packingInside_staysIn P X)

end PathRuns
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
