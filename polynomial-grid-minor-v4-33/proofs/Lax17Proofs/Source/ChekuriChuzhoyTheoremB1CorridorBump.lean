import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorState

namespace Lax17Proofs

universe u v w

/-!
# Bump rerouting in an arbitrary Appendix B.1 corridor

This file proves the bump half of the finite row descent in the corridor
lemma used for Chekuri--Chuzhoy Theorem B.1.  Unlike the older type-one
development in `ChekuriChuzhoyTheoremB1`, every definition below is stated for
the common `CorridorRowState`; the type-one and type-two branches therefore
use exactly the same operation.

A bump is a non-row-contained subpath of one of the fixed full columns whose
two endpoints occur in order on one active row and whose interior avoids the
whole current linkage.  The row interval between those endpoints is replaced
by the oriented column segment.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


open IndexedAuxiliaryPrefix

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {original : PerfectPathPacking G A B}
variable {activeCount : ℕ} {ι : Type w}
variable {fixedColumn : ι → GraphPath G}

/-- Orient an unoriented corridor segment between its two named endpoints. -/
noncomputable def corridorOrientBetween
    (P : GraphPath G) {s t : V} (h : P.Connects {s} {t}) :
    GraphPath G :=
  P.orient h

namespace corridorOrientBetween

variable {P : GraphPath G} {s t : V} {h : P.Connects {s} {t}}

@[simp] theorem vertexSet :
    (corridorOrientBetween (G := G) P h).vertexSet = P.vertexSet := by
  simp [corridorOrientBetween]

@[simp] theorem edgeSet :
    (corridorOrientBetween (G := G) P h).edgeSet = P.edgeSet := by
  simp [corridorOrientBetween]

theorem source :
    (corridorOrientBetween (G := G) P h).source = s := by
  have hs := GraphPath.orient_source_mem P h
  simpa [corridorOrientBetween] using hs

theorem target :
    (corridorOrientBetween (G := G) P h).target = t := by
  have ht := GraphPath.orient_target_mem P h
  simpa [corridorOrientBetween] using ht

end corridorOrientBetween

/-- Vertex support of the path concatenation primitive. -/
theorem corridorAppend_vertexSet_subset
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).vertexSet ⊆
      P.vertexSet ∪ Q.vertexSet := by
  exact P.appendWithEq_vertexSet_subset Q h
    (P.appendWithEq_isPath_of_inter_subset_target Q h hinter)

/-- Edge support of the path concatenation primitive. -/
theorem corridorAppend_edgeSet_subset
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).edgeSet ⊆
      P.edgeSet ∪ Q.edgeSet := by
  exact P.appendWithEq_edgeSet_subset Q h
    (P.appendWithEq_isPath_of_inter_subset_target Q h hinter)

/-- Reverse an auxiliary bridge. -/
noncomputable def reverseCorridorBridge
    {P : PathPacking G A B} {i j : P.Index}
    (β : P.BridgeBetween i j) : P.BridgeBetween j i where
  path := β.path.reverse
  connects := by
    rcases β.connects with h | h
    · exact Or.inl ⟨by simpa using h.2, by simpa using h.1⟩
    · exact Or.inr ⟨by simpa using h.2, by simpa using h.1⟩
  internallyDisjoint := by
    exact (β.path.reverse_internallyDisjointFromSet P.vertexSet).2
      β.internallyDisjoint

/-- Replace one path of a perfect linkage, preserving its ordered endpoints
and its shared index type. -/
noncomputable def replaceCorridorPathSameEndpoints
    (P : PerfectPathPacking G A B) (j : P.Index) (Pj : GraphPath G)
    (hsource : Pj.source = (P.path j).source)
    (htarget : Pj.target = (P.path j).target)
    (hdisj : ∀ i : P.Index, i ≠ j → Pj.NodeDisjoint (P.path i)) :
    PerfectPathPacking G A B := by
  classical
  let path' : P.Index → GraphPath G :=
    fun i => if i = j then Pj else P.path i
  have hpath_source :
      ∀ i : P.Index, (path' i).source = (P.path i).source := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [path', hsource]
    · simp [path', hij]
  have hpath_target :
      ∀ i : P.Index, (path' i).target = (P.path i).target := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [path', htarget]
    · simp [path', hij]
  refine
    { toPathPacking :=
        { Index := P.Index
          path := path'
          connects := by
            intro i
            exact Or.inl
              ⟨by
                  rw [hpath_source i]
                  exact P.source_mem i,
                by
                  rw [hpath_target i]
                  exact P.target_mem i⟩
          node_disjoint := by
            intro i k hik
            by_cases hij : i = j
            · by_cases hkj : k = j
              · exact False.elim (hik (hij.trans hkj.symm))
              · simpa [path', hij, hkj] using hdisj k hkj
            · by_cases hkj : k = j
              · simpa [path', hij, hkj] using (hdisj i hij).symm
              · simpa [path', hij, hkj] using P.node_disjoint hik }
      source_mem := by
        intro i
        rw [hpath_source i]
        exact P.source_mem i
      target_mem := by
        intro i
        rw [hpath_target i]
        exact P.target_mem i
      source_bijective := ?_
      target_bijective := ?_ }
  · have hsrc :
        (fun i : P.Index =>
          (⟨(path' i).source, by
            rw [hpath_source i]
            exact P.source_mem i⟩ : {v // v ∈ A})) =
        (fun i : P.Index =>
          (⟨(P.path i).source, P.source_mem i⟩ : {v // v ∈ A})) := by
      funext i
      apply Subtype.ext
      exact hpath_source i
    simpa [hsrc] using P.source_bijective
  · have htgt :
        (fun i : P.Index =>
          (⟨(path' i).target, by
            rw [hpath_target i]
            exact P.target_mem i⟩ : {v // v ∈ B})) =
        (fun i : P.Index =>
          (⟨(P.path i).target, P.target_mem i⟩ : {v // v ∈ B})) := by
      funext i
      apply Subtype.ext
      exact hpath_target i
    simpa [htgt] using P.target_bijective

@[simp] theorem replaceCorridorPathSameEndpoints_path_self
    (P : PerfectPathPacking G A B) (j : P.Index) (Pj : GraphPath G)
    (hsource : Pj.source = (P.path j).source)
    (htarget : Pj.target = (P.path j).target)
    (hdisj : ∀ i : P.Index, i ≠ j → Pj.NodeDisjoint (P.path i)) :
    (replaceCorridorPathSameEndpoints
      P j Pj hsource htarget hdisj).path j = Pj := by
  simp [replaceCorridorPathSameEndpoints]

@[simp] theorem replaceCorridorPathSameEndpoints_path_of_ne
    (P : PerfectPathPacking G A B) (j i : P.Index) (Pj : GraphPath G)
    (hsource : Pj.source = (P.path j).source)
    (htarget : Pj.target = (P.path j).target)
    (hdisj : ∀ i : P.Index, i ≠ j → Pj.NodeDisjoint (P.path i))
    (hij : i ≠ j) :
    (replaceCorridorPathSameEndpoints
      P j Pj hsource htarget hdisj).path i = P.path i := by
  simp [replaceCorridorPathSameEndpoints, hij]

/-- A connected path cannot switch owners while using only edges of a
pairwise vertex-disjoint finite path family. -/
theorem graphPath_edgeSet_subset_member_of_pairwiseUnion
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (paths : κ → GraphPath G)
    (hpairwise :
      Pairwise fun i j : κ => (paths i).NodeDisjoint (paths j))
    (base : κ) (P : GraphPath G)
    (hsource : P.source ∈ (paths base).vertexSet)
    (hedges :
      P.edgeSet ⊆
        Finset.univ.biUnion fun i : κ => (paths i).edgeSet) :
    P.edgeSet ⊆ (paths base).edgeSet := by
  classical
  have aux :
      ∀ {x y : V} (W : G.Walk x y) (base : κ),
        x ∈ (paths base).vertexSet →
        (∀ e : Sym2 V, e ∈ W.edges.toFinset →
          e ∈ Finset.univ.biUnion fun i : κ => (paths i).edgeSet) →
        ∀ e : Sym2 V, e ∈ W.edges.toFinset →
          e ∈ (paths base).edgeSet := by
    intro x y W
    induction W with
    | nil =>
        intro base hx hall e he
        simp at he
    | @cons x y z hxy W ih =>
        intro base hx hall e he
        have hfirstUnion :
            s(x, y) ∈
              Finset.univ.biUnion fun i : κ => (paths i).edgeSet :=
          hall s(x, y) (by simp)
        rcases Finset.mem_biUnion.1 hfirstUnion with
          ⟨owner, _howner, hfirstOwner⟩
        have hends :
            x ∈ (paths owner).vertexSet ∧
              y ∈ (paths owner).vertexSet :=
          (paths owner).endpoints_mem_vertexSet_of_edgeSet hfirstOwner
        have howner : owner = base := by
          by_contra hne
          exact Finset.disjoint_left.mp (hpairwise hne) hends.1 hx
        have hy : y ∈ (paths base).vertexSet := by
          simpa [howner] using hends.2
        have htail :
            ∀ f : Sym2 V, f ∈ W.edges.toFinset →
              f ∈ Finset.univ.biUnion fun i : κ => (paths i).edgeSet := by
          intro f hf
          exact hall f (by
            have hfList : f ∈ W.edges := List.mem_toFinset.mp hf
            exact List.mem_toFinset.mpr (by
              simpa using List.mem_cons_of_mem s(x, y) hfList))
        have he_cases : e = s(x, y) ∨ e ∈ W.edges.toFinset := by
          have heList : e ∈ s(x, y) :: W.edges := by
            simpa using List.mem_toFinset.mp he
          rcases List.mem_cons.1 heList with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_toFinset.mpr h)
        rcases he_cases with rfl | heTail
        · simpa [howner] using hfirstOwner
        · exact ih base hy htail e heTail
  intro e he
  exact aux P.walk base hsource
    (by
      intro f hf
      exact hedges (by simpa [GraphPath.edgeSet] using hf))
    e (by simpa [GraphPath.edgeSet] using he)

/-- A source-faithful bump in one current active row.

The segment is stored unoriented, since the owning full column can traverse it
in either direction.  `segment_clean_linkage` is the formal version of
"the interior avoids all current rows": outside-corridor avoidance of a full
column upgrades that condition to the entire current linkage. -/
structure CorridorBumpWitness
    (S : CorridorRowState original activeCount ι fixedColumn) where
  row : Fin activeCount
  column : ι
  left : V
  right : V
  left_mem_row :
    left ∈
      (AuxiliaryCorridor.activePath S.corridor row).vertexSet
  right_mem_row :
    right ∈
      (AuxiliaryCorridor.activePath S.corridor row).vertexSet
  left_before_right :
    (AuxiliaryCorridor.activePath S.corridor row).Before left right
  left_ne_right : left ≠ right
  segment : GraphPath G
  segment_connects : segment.Connects {left} {right}
  segment_vertexSet_subset_column :
    segment.vertexSet ⊆ (fixedColumn column).vertexSet
  segment_edgeSet_subset_column :
    segment.edgeSet ⊆ (fixedColumn column).edgeSet
  segment_clean_linkage :
    segment.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet
  not_row_contained :
    (∃ v : V, v ∈ segment.vertexSet ∧
      v ∉
        (AuxiliaryCorridor.activePath S.corridor row).vertexSet) ∨
      ¬ segment.edgeSet ⊆
        (AuxiliaryCorridor.activePath S.corridor row).edgeSet

namespace CorridorBumpWitness

variable {S : CorridorRowState original activeCount ι fixedColumn}
variable (bump : CorridorBumpWitness S)

/-- The linkage index of the row changed by the bump. -/
def middleIndex : S.linkage.Index :=
  S.corridor.index (S.corridor.activePosition bump.row)

/-- The current row changed by the bump. -/
def rowPath : GraphPath G :=
  S.corridor.activePath bump.row

@[simp] theorem rowPath_eq_linkage_path :
    bump.rowPath = S.linkage.path bump.middleIndex :=
  rfl

/-- The column segment oriented from the earlier to the later row endpoint. -/
noncomputable def orientedSegment : GraphPath G :=
  corridorOrientBetween bump.segment bump.segment_connects

@[simp] theorem orientedSegment_vertexSet :
    bump.orientedSegment.vertexSet = bump.segment.vertexSet := by
  simp [orientedSegment]

@[simp] theorem orientedSegment_edgeSet :
    bump.orientedSegment.edgeSet = bump.segment.edgeSet := by
  simp [orientedSegment]

@[simp] theorem orientedSegment_source :
    bump.orientedSegment.source = bump.left :=
  corridorOrientBetween.source

@[simp] theorem orientedSegment_target :
    bump.orientedSegment.target = bump.right :=
  corridorOrientBetween.target

/-- The old row interval deleted by the switch. -/
noncomputable def deletedRowSegment : GraphPath G :=
  bump.rowPath.segmentOfBefore bump.left_before_right

@[simp] theorem deletedRowSegment_source :
    bump.deletedRowSegment.source = bump.left :=
  rfl

@[simp] theorem deletedRowSegment_target :
    bump.deletedRowSegment.target = bump.right :=
  rfl

theorem deletedRowSegment_edgeSet_subset_row :
    bump.deletedRowSegment.edgeSet ⊆ bump.rowPath.edgeSet :=
  bump.rowPath.segmentOfBefore_edgeSet_subset bump.left_before_right

theorem left_mem_segment :
    bump.left ∈ bump.segment.vertexSet := by
  have hs :
      bump.orientedSegment.source ∈ bump.orientedSegment.vertexSet :=
    GraphPath.source_mem_vertexSet bump.orientedSegment
  simpa using hs

theorem right_mem_segment :
    bump.right ∈ bump.segment.vertexSet := by
  have ht :
      bump.orientedSegment.target ∈ bump.orientedSegment.vertexSet :=
    GraphPath.target_mem_vertexSet bump.orientedSegment
  simpa using ht

theorem left_mem_column :
    bump.left ∈ (fixedColumn bump.column).vertexSet :=
  bump.segment_vertexSet_subset_column bump.left_mem_segment

theorem right_mem_column :
    bump.right ∈ (fixedColumn bump.column).vertexSet :=
  bump.segment_vertexSet_subset_column bump.right_mem_segment

/-- Whole-linkage cleanliness is invariant under orienting the segment. -/
theorem orientedSegment_clean_linkage :
    bump.orientedSegment.InternallyDisjointFromSet
      S.linkage.toPathPacking.vertexSet := by
  intro v hv hlink
  have hv' : v ∈ bump.segment.vertexSet := by simpa using hv
  have hend := bump.segment_clean_linkage hv' hlink
  change (bump.segment.orient bump.segment_connects).IsEndpoint v
  exact
    (GraphPath.orient_isEndpoint bump.segment bump.segment_connects).2 hend

/-- In particular, the oriented segment meets its own current row only at its
two endpoints. -/
theorem orientedSegment_clean_row :
    bump.orientedSegment.InternallyDisjointFromSet bump.rowPath.vertexSet := by
  intro v hv hvrow
  have hvlink :
      v ∈ S.linkage.toPathPacking.vertexSet :=
    (S.linkage.toPathPacking.mem_vertexSet).2
      ⟨bump.middleIndex, by simpa using hvrow⟩
  exact bump.orientedSegment_clean_linkage hv hvlink

theorem orientedSegment_vertexSet_subset_column :
    bump.orientedSegment.vertexSet ⊆
      (fixedColumn bump.column).vertexSet := by
  simpa using bump.segment_vertexSet_subset_column

theorem orientedSegment_edgeSet_subset_column :
    bump.orientedSegment.edgeSet ⊆
      (fixedColumn bump.column).edgeSet := by
  simpa using bump.segment_edgeSet_subset_column

/-- Since `right` is strictly after `left`, it is absent from the retained
prefix. -/
theorem right_not_mem_prefix :
    bump.right ∉
      (bump.rowPath.takeUntil bump.left_mem_row).vertexSet := by
  intro hright
  have hright_before_left :
      bump.rowPath.Before bump.right bump.left :=
    bump.rowPath.before_of_mem_takeUntil bump.left_mem_row hright
  have heq : bump.right = bump.left :=
    bump.rowPath.before_antisymm
      hright_before_left bump.left_before_right
  exact bump.left_ne_right heq.symm

/-- Since `left` is strictly before `right`, it is absent from the retained
suffix. -/
theorem left_not_mem_suffix :
    bump.left ∉
      (bump.rowPath.dropUntil bump.right_mem_row).vertexSet := by
  intro hleft
  have hright_before_left :
      bump.rowPath.Before bump.right bump.left :=
    ⟨bump.right_mem_row, hleft⟩
  have heq : bump.left = bump.right :=
    bump.rowPath.before_antisymm
      bump.left_before_right hright_before_left
  exact bump.left_ne_right heq

/-- The retained prefix meets the inserted segment only at `left`. -/
theorem prefix_inter_orientedSegment_subset_left :
    ∀ ⦃v : V⦄,
      v ∈ (bump.rowPath.takeUntil bump.left_mem_row).vertexSet →
      v ∈ bump.orientedSegment.vertexSet →
      v = (bump.rowPath.takeUntil bump.left_mem_row).target := by
  intro v hvpre hvmid
  have hvrow : v ∈ bump.rowPath.vertexSet :=
    bump.rowPath.takeUntil_vertexSet_subset bump.left_mem_row hvpre
  have hend := bump.orientedSegment_clean_row hvmid hvrow
  rcases hend with hleft | hright
  · simpa using hleft
  · exfalso
    exact bump.right_not_mem_prefix (by simpa [hright] using hvpre)

/-- The retained old-row prefix and suffix are disjoint. -/
theorem prefix_disjoint_suffix :
    Disjoint
      (bump.rowPath.takeUntil bump.left_mem_row).vertexSet
      (bump.rowPath.dropUntil bump.right_mem_row).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvpre hvsuf
  have hv_before_left : bump.rowPath.Before v bump.left :=
    bump.rowPath.before_of_mem_takeUntil bump.left_mem_row hvpre
  have hright_before_v : bump.rowPath.Before bump.right v :=
    ⟨bump.right_mem_row, hvsuf⟩
  have hright_before_left : bump.rowPath.Before bump.right bump.left :=
    bump.rowPath.before_trans hright_before_v hv_before_left
  have heq : bump.right = bump.left :=
    bump.rowPath.before_antisymm
      hright_before_left bump.left_before_right
  exact bump.left_ne_right heq.symm

end CorridorBumpWitness

/-- Exact support information for the concrete replacement row. -/
structure CorridorBumpReplacementPath
    {S : CorridorRowState original activeCount ι fixedColumn}
    (bump : CorridorBumpWitness S) where
  path : GraphPath G
  source_eq : path.source = bump.rowPath.source
  target_eq : path.target = bump.rowPath.target
  vertexSet_subset_parts :
    path.vertexSet ⊆
      ((bump.rowPath.takeUntil bump.left_mem_row).vertexSet ∪
          bump.orientedSegment.vertexSet) ∪
        (bump.rowPath.dropUntil bump.right_mem_row).vertexSet
  prefix_subset_path :
    (bump.rowPath.takeUntil bump.left_mem_row).vertexSet ⊆ path.vertexSet
  segment_subset_path :
    bump.orientedSegment.vertexSet ⊆ path.vertexSet
  suffix_subset_path :
    (bump.rowPath.dropUntil bump.right_mem_row).vertexSet ⊆ path.vertexSet
  vertexSet_subset :
    path.vertexSet ⊆ bump.rowPath.vertexSet ∪ bump.segment.vertexSet
  edgeSet_subset_parts :
    path.edgeSet ⊆
      ((bump.rowPath.takeUntil bump.left_mem_row).edgeSet ∪
          bump.orientedSegment.edgeSet) ∪
        (bump.rowPath.dropUntil bump.right_mem_row).edgeSet
  edgeSet_subset :
    path.edgeSet ⊆ bump.rowPath.edgeSet ∪ bump.segment.edgeSet

namespace CorridorBumpWitness

variable {S : CorridorRowState original activeCount ι fixedColumn}
variable (bump : CorridorBumpWitness S)

/-- The concrete switch
`row[source,left] · segment[left,right] · row[right,target]`. -/
noncomputable def replacementPath : CorridorBumpReplacementPath bump := by
  classical
  let row : GraphPath G := bump.rowPath
  let pre : GraphPath G := row.takeUntil bump.left_mem_row
  let mid : GraphPath G := bump.orientedSegment
  let suf : GraphPath G := row.dropUntil bump.right_mem_row
  have hpre_mid_glue : pre.target = mid.source := by
    simp [pre, mid, row]
  have hpre_mid_inter :
      ∀ ⦃v : V⦄, v ∈ pre.vertexSet → v ∈ mid.vertexSet →
        v = pre.target := by
    intro v hvpre hvmid
    simpa [pre, mid, row] using
      bump.prefix_inter_orientedSegment_subset_left
        (v := v) (by simpa [pre, row] using hvpre)
        (by simpa [mid] using hvmid)
  let preMid : GraphPath G :=
    pre.appendWithEqOfInterSubsetTarget mid hpre_mid_glue hpre_mid_inter
  have hpreMid_suf_glue : preMid.target = suf.source := by
    simp [preMid, pre, mid, suf, row]
  have hpreMid_suf_inter :
      ∀ ⦃v : V⦄, v ∈ preMid.vertexSet → v ∈ suf.vertexSet →
        v = preMid.target := by
    intro v hvpm hvsuf
    have hvpm_union : v ∈ pre.vertexSet ∪ mid.vertexSet :=
      corridorAppend_vertexSet_subset
        pre mid hpre_mid_glue hpre_mid_inter hvpm
    rcases Finset.mem_union.1 hvpm_union with hvpre | hvmid
    · exact False.elim
        (Finset.disjoint_left.mp bump.prefix_disjoint_suffix
          (by simpa [pre, row] using hvpre)
          (by simpa [suf, row] using hvsuf))
    · have hvrow : v ∈ bump.rowPath.vertexSet :=
        bump.rowPath.dropUntil_vertexSet_subset
          bump.right_mem_row (by simpa [suf, row] using hvsuf)
      have hend :=
        bump.orientedSegment_clean_row
          (by simpa [mid] using hvmid) hvrow
      rcases hend with hleft | hright
      · exact False.elim
          (bump.left_not_mem_suffix (by
            simpa [suf, row, hleft] using hvsuf))
      · simpa [preMid, mid] using hright
  let whole : GraphPath G :=
    preMid.appendWithEqOfInterSubsetTarget suf
      hpreMid_suf_glue hpreMid_suf_inter
  refine
    { path := whole
      source_eq := ?_
      target_eq := ?_
      vertexSet_subset_parts := ?_
      prefix_subset_path := ?_
      segment_subset_path := ?_
      suffix_subset_path := ?_
      vertexSet_subset := ?_
      edgeSet_subset_parts := ?_
      edgeSet_subset := ?_ }
  · simp [whole, preMid, pre, row]
  · simp [whole, preMid, suf, row]
  · intro v hv
    have hv_union : v ∈ preMid.vertexSet ∪ suf.vertexSet :=
      corridorAppend_vertexSet_subset
        preMid suf hpreMid_suf_glue hpreMid_suf_inter hv
    rcases Finset.mem_union.1 hv_union with hvpm | hvsuf
    · have hvpm_union : v ∈ pre.vertexSet ∪ mid.vertexSet :=
        corridorAppend_vertexSet_subset
          pre mid hpre_mid_glue hpre_mid_inter hvpm
      rcases Finset.mem_union.1 hvpm_union with hvpre | hvmid
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inl <|
            by simpa [pre, row] using hvpre
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inr <|
            by simpa [mid] using hvmid
    · exact Finset.mem_union.2 <| Or.inr <|
        by simpa [suf, row] using hvsuf
  · intro v hvpre
    have hvpm : v ∈ preMid.vertexSet :=
      pre.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        mid hpre_mid_glue hpre_mid_inter hvpre
    have hvwhole : v ∈ whole.vertexSet :=
      preMid.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        suf hpreMid_suf_glue hpreMid_suf_inter hvpm
    simpa [whole, preMid, pre, row] using hvwhole
  · intro v hvmid
    have hvpm : v ∈ preMid.vertexSet :=
      pre.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
        mid hpre_mid_glue hpre_mid_inter hvmid
    have hvwhole : v ∈ whole.vertexSet :=
      preMid.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        suf hpreMid_suf_glue hpreMid_suf_inter hvpm
    simpa [whole, preMid, mid] using hvwhole
  · intro v hvsuf
    have hvwhole : v ∈ whole.vertexSet :=
      preMid.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
        suf hpreMid_suf_glue hpreMid_suf_inter hvsuf
    simpa [whole, preMid, suf, row] using hvwhole
  · intro v hv
    have hv_union : v ∈ preMid.vertexSet ∪ suf.vertexSet :=
      corridorAppend_vertexSet_subset
        preMid suf hpreMid_suf_glue hpreMid_suf_inter hv
    rcases Finset.mem_union.1 hv_union with hvpm | hvsuf
    · have hvpm_union : v ∈ pre.vertexSet ∪ mid.vertexSet :=
        corridorAppend_vertexSet_subset
          pre mid hpre_mid_glue hpre_mid_inter hvpm
      rcases Finset.mem_union.1 hvpm_union with hvpre | hvmid
      · exact Finset.mem_union.2 <| Or.inl <|
          bump.rowPath.takeUntil_vertexSet_subset
            bump.left_mem_row (by simpa [pre, row] using hvpre)
      · exact Finset.mem_union.2 <| Or.inr <|
          by simpa [mid] using hvmid
    · exact Finset.mem_union.2 <| Or.inl <|
        bump.rowPath.dropUntil_vertexSet_subset
          bump.right_mem_row (by simpa [suf, row] using hvsuf)
  · intro e he
    have he_union : e ∈ preMid.edgeSet ∪ suf.edgeSet :=
      corridorAppend_edgeSet_subset
        preMid suf hpreMid_suf_glue hpreMid_suf_inter he
    rcases Finset.mem_union.1 he_union with hepm | hesuf
    · have hepm_union : e ∈ pre.edgeSet ∪ mid.edgeSet :=
        corridorAppend_edgeSet_subset
          pre mid hpre_mid_glue hpre_mid_inter hepm
      rcases Finset.mem_union.1 hepm_union with hepre | hemid
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inl <|
            by simpa [pre, row] using hepre
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inr <|
            by simpa [mid] using hemid
    · exact Finset.mem_union.2 <| Or.inr <|
        by simpa [suf, row] using hesuf
  · intro e he
    have he_union : e ∈ preMid.edgeSet ∪ suf.edgeSet :=
      corridorAppend_edgeSet_subset
        preMid suf hpreMid_suf_glue hpreMid_suf_inter he
    rcases Finset.mem_union.1 he_union with hepm | hesuf
    · have hepm_union : e ∈ pre.edgeSet ∪ mid.edgeSet :=
        corridorAppend_edgeSet_subset
          pre mid hpre_mid_glue hpre_mid_inter hepm
      rcases Finset.mem_union.1 hepm_union with hepre | hemid
      · exact Finset.mem_union.2 <| Or.inl <|
          bump.rowPath.takeUntil_edgeSet_subset
            bump.left_mem_row (by simpa [pre, row] using hepre)
      · exact Finset.mem_union.2 <| Or.inr <|
          by simpa [mid] using hemid
    · exact Finset.mem_union.2 <| Or.inl <|
        bump.rowPath.dropUntil_edgeSet_subset
          bump.right_mem_row (by simpa [suf, row] using hesuf)

@[simp] theorem replacementPath_source :
    bump.replacementPath.path.source = bump.rowPath.source :=
  bump.replacementPath.source_eq

@[simp] theorem replacementPath_target :
    bump.replacementPath.path.target = bump.rowPath.target :=
  bump.replacementPath.target_eq

/-- The old bumped row is disjoint from every unchanged linkage path. -/
theorem row_nodeDisjoint_unchanged
    {i : S.linkage.Index} (hi : i ≠ bump.middleIndex) :
    bump.rowPath.NodeDisjoint (S.linkage.path i) := by
  simpa [bump.rowPath_eq_linkage_path] using
    S.linkage.toPathPacking.node_disjoint (fun h => hi h.symm)

/-- The clean inserted segment is disjoint from every unchanged linkage
path, including at its two endpoints. -/
theorem orientedSegment_nodeDisjoint_unchanged
    {i : S.linkage.Index} (hi : i ≠ bump.middleIndex) :
    bump.orientedSegment.NodeDisjoint (S.linkage.path i) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvseg hvi
  have hpack : v ∈ S.linkage.toPathPacking.vertexSet :=
    (S.linkage.toPathPacking.mem_vertexSet).2 ⟨i, hvi⟩
  have hend := bump.orientedSegment_clean_linkage hvseg hpack
  rcases hend with hleft | hright
  · have hleft_i : bump.left ∈ (S.linkage.path i).vertexSet := by
      simpa [hleft] using hvi
    have hleft_row :
        bump.left ∈ (S.linkage.path bump.middleIndex).vertexSet := by
      simpa using bump.left_mem_row
    exact Finset.disjoint_left.mp
      (S.linkage.toPathPacking.node_disjoint (fun h => hi h.symm))
      hleft_row hleft_i
  · have hright_i : bump.right ∈ (S.linkage.path i).vertexSet := by
      simpa [hright] using hvi
    have hright_row :
        bump.right ∈ (S.linkage.path bump.middleIndex).vertexSet := by
      simpa using bump.right_mem_row
    exact Finset.disjoint_left.mp
      (S.linkage.toPathPacking.node_disjoint (fun h => hi h.symm))
      hright_row hright_i

/-- The concrete replacement row remains disjoint from all unchanged linkage
paths. -/
theorem replacementPath_nodeDisjoint_unchanged
    {i : S.linkage.Index} (hi : i ≠ bump.middleIndex) :
    bump.replacementPath.path.NodeDisjoint (S.linkage.path i) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvrep hvi
  have hparts := bump.replacementPath.vertexSet_subset_parts hvrep
  rcases Finset.mem_union.1 hparts with hpre_or_mid | hsuf
  · rcases Finset.mem_union.1 hpre_or_mid with hpre | hmid
    · have hvrow : v ∈ bump.rowPath.vertexSet :=
        bump.rowPath.takeUntil_vertexSet_subset bump.left_mem_row hpre
      exact Finset.disjoint_left.mp
        (bump.row_nodeDisjoint_unchanged hi) hvrow hvi
    · exact Finset.disjoint_left.mp
        (bump.orientedSegment_nodeDisjoint_unchanged hi) hmid hvi
  · have hvrow : v ∈ bump.rowPath.vertexSet :=
      bump.rowPath.dropUntil_vertexSet_subset bump.right_mem_row hsuf
    exact Finset.disjoint_left.mp
      (bump.row_nodeDisjoint_unchanged hi) hvrow hvi

/-- The new perfect linkage obtained by replacing just the bumped row. -/
noncomputable def replacementLinkage : PerfectPathPacking G A B :=
  replaceCorridorPathSameEndpoints S.linkage bump.middleIndex
    bump.replacementPath.path
    (by simpa using bump.replacementPath_source)
    (by simpa using bump.replacementPath_target)
    (fun _ hi => bump.replacementPath_nodeDisjoint_unchanged hi)

@[simp] theorem replacementLinkage_path_middle :
    bump.replacementLinkage.path bump.middleIndex =
      bump.replacementPath.path := by
  simp [replacementLinkage]

@[simp] theorem replacementLinkage_path_of_ne
    {i : S.linkage.Index} (hi : i ≠ bump.middleIndex) :
    bump.replacementLinkage.path i = S.linkage.path i := by
  simp [replacementLinkage, hi]

/-- The fixed paths remain a pairwise vertex-disjoint family when viewed
outside the dependent column structure. -/
theorem fixedColumn_pairwise_nodeDisjoint
    (S : CorridorRowState original activeCount ι fixedColumn) :
    Pairwise fun i j : ι =>
      (fixedColumn i).NodeDisjoint (fixedColumn j) :=
by
  intro i j hij
  rw [← CorridorRowState.column_eq_fixed S i,
    ← CorridorRowState.column_eq_fixed S j]
  exact S.columns.pairwise_nodeDisjoint hij

section Measure

variable [Fintype ι] [DecidableEq ι]

/-- The replacement row uses only old-row edges and fixed-column edges. -/
theorem replacementPath_edgeSet_subset_row_union_fixed :
    bump.replacementPath.path.edgeSet ⊆
      bump.rowPath.edgeSet ∪ S.fixedColumnEdgeSet := by
  classical
  intro e he
  rcases Finset.mem_union.1 (bump.replacementPath.edgeSet_subset he) with
    herow | heseg
  · exact Finset.mem_union.2 (Or.inl herow)
  · exact Finset.mem_union.2 (Or.inr <|
      Finset.mem_biUnion.2
        ⟨bump.column, Finset.mem_univ _,
          bump.segment_edgeSet_subset_column heseg⟩)

/-- The deleted interval is nontrivial. -/
theorem deletedRowSegment_edgeSet_nonempty :
    bump.deletedRowSegment.edgeSet.Nonempty := by
  have hne :
      bump.deletedRowSegment.source ≠ bump.deletedRowSegment.target := by
    intro h
    exact bump.left_ne_right (by simpa using h)
  exact bump.deletedRowSegment.edgeSet_nonempty_of_source_ne_target hne

/-- Hypothetical containment in the fixed-column union forces every deleted
interval edge to belong to the same column as the bump segment. -/
theorem deletedRowSegment_edgeSet_subset_column_of_subset_fixed
    (hsub :
      bump.deletedRowSegment.edgeSet ⊆ S.fixedColumnEdgeSet) :
    bump.deletedRowSegment.edgeSet ⊆
      (fixedColumn bump.column).edgeSet := by
  apply graphPath_edgeSet_subset_member_of_pairwiseUnion
    fixedColumn (fixedColumn_pairwise_nodeDisjoint S) bump.column
      bump.deletedRowSegment
  · simpa using bump.left_mem_column
  · simpa [CorridorRowState.fixedColumnEdgeSet] using hsub

/-- Vertex form of fixed-column ownership. -/
theorem deletedRowSegment_vertexSet_subset_column_of_subset_fixed
    (hsub :
      bump.deletedRowSegment.edgeSet ⊆ S.fixedColumnEdgeSet) :
    bump.deletedRowSegment.vertexSet ⊆
      (fixedColumn bump.column).vertexSet :=
  graphPath_vertexSet_subset_of_edgeSet_subset_of_source_mem
    (P := fixedColumn bump.column) (Q := bump.deletedRowSegment)
    (by simpa using bump.left_mem_column)
    (bump.deletedRowSegment_edgeSet_subset_column_of_subset_fixed hsub)

/-- If the deleted interval lay in the column union, the inserted segment
would lie in the deleted interval by uniqueness of subpaths of a simple
column. -/
theorem segment_vertexSet_subset_deleted_of_subset_fixed
    (hsub :
      bump.deletedRowSegment.edgeSet ⊆ S.fixedColumnEdgeSet) :
    bump.segment.vertexSet ⊆ bump.deletedRowSegment.vertexSet := by
  have hsubset :
      bump.orientedSegment.vertexSet ⊆
        bump.deletedRowSegment.vertexSet :=
    GraphPath.vertexSet_subset_of_edgeSet_subset_same_endpoints
      (fixedColumn bump.column)
      bump.orientedSegment bump.deletedRowSegment
      bump.orientedSegment_vertexSet_subset_column
      bump.orientedSegment_edgeSet_subset_column
      (bump.deletedRowSegment_vertexSet_subset_column_of_subset_fixed hsub)
      (bump.deletedRowSegment_edgeSet_subset_column_of_subset_fixed hsub)
      (by simp) (by simp)
  simpa using hsubset

/-- Converse containment under the same hypothetical ownership. -/
theorem deletedRowSegment_vertexSet_subset_segment_of_subset_fixed
    (hsub :
      bump.deletedRowSegment.edgeSet ⊆ S.fixedColumnEdgeSet) :
    bump.deletedRowSegment.vertexSet ⊆ bump.segment.vertexSet := by
  have hsubset :
      bump.deletedRowSegment.vertexSet ⊆
        bump.orientedSegment.vertexSet :=
    GraphPath.vertexSet_subset_of_edgeSet_subset_same_endpoints
      (fixedColumn bump.column)
      bump.deletedRowSegment bump.orientedSegment
      (bump.deletedRowSegment_vertexSet_subset_column_of_subset_fixed hsub)
      (bump.deletedRowSegment_edgeSet_subset_column_of_subset_fixed hsub)
      bump.orientedSegment_vertexSet_subset_column
      bump.orientedSegment_edgeSet_subset_column
      (by simp) (by simp)
  simpa using hsubset

/-- If there is no off-row vertex, linkage cleanliness says that the segment
has only its two row endpoints as vertices. -/
theorem segment_vertexSet_subset_endpoints_of_no_off_row
    (hno :
      ¬ ∃ v : V, v ∈ bump.segment.vertexSet ∧
        v ∉ bump.rowPath.vertexSet) :
    bump.segment.vertexSet ⊆ ({bump.left, bump.right} : Finset V) := by
  have hsource :
      bump.segment.source = bump.left ∨
        bump.segment.source = bump.right := by
    rcases bump.segment_connects with h | h
    · exact Or.inl (by simpa using h.1)
    · exact Or.inr (by simpa using h.1)
  have htarget :
      bump.segment.target = bump.left ∨
        bump.segment.target = bump.right := by
    rcases bump.segment_connects with h | h
    · exact Or.inr (by simpa using h.2)
    · exact Or.inl (by simpa using h.2)
  intro v hv
  have hvrow : v ∈ bump.rowPath.vertexSet := by
    by_contra hvnot
    exact hno ⟨v, hv, hvnot⟩
  have hvlink : v ∈ S.linkage.toPathPacking.vertexSet :=
    (S.linkage.toPathPacking.mem_vertexSet).2
      ⟨bump.middleIndex, by simpa using hvrow⟩
  have hend := bump.segment_clean_linkage hv hvlink
  rcases hend with hs | ht
  · simpa [hs] using hsource
  · simpa [ht] using htarget

/-- Every edge of a path supported on the two distinct bump endpoints is the
unordered edge between those endpoints. -/
theorem edge_eq_left_right_of_endpoint_vertex_support
    {P : GraphPath G} {e : Sym2 V}
    (hverts :
      P.vertexSet ⊆ ({bump.left, bump.right} : Finset V))
    (he : e ∈ P.edgeSet) :
    e = s(bump.left, bump.right) := by
  classical
  have hfst_mem : e.out.1 ∈ P.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet he (Sym2.out_fst_mem e)
  have hsnd_mem : e.out.2 ∈ P.vertexSet :=
    graphPath_mem_vertexSet_of_mem_edgeSet he (Sym2.out_snd_mem e)
  have hfst :
      e.out.1 = bump.left ∨ e.out.1 = bump.right := by
    simpa using hverts hfst_mem
  have hsnd :
      e.out.2 = bump.left ∨ e.out.2 = bump.right := by
    simpa using hverts hsnd_mem
  have heG : e ∈ G.edgeSet := P.edgeSet_subset_edgeSet he
  have hadj : G.Adj e.out.1 e.out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, e.out_eq] using heG
  have hne : e.out.1 ≠ e.out.2 := hadj.ne
  rcases hfst with hfl | hfr <;> rcases hsnd with hsl | hsr
  · exact False.elim (hne (hfl.trans hsl.symm))
  · exact (Sym2.mem_and_mem_iff bump.left_ne_right).1
      ⟨by simpa [hfl] using Sym2.out_fst_mem e,
        by simpa [hsr] using Sym2.out_snd_mem e⟩
  · exact (Sym2.mem_and_mem_iff bump.left_ne_right).1
      ⟨by simpa [hsl] using Sym2.out_snd_mem e,
        by simpa [hfr] using Sym2.out_fst_mem e⟩
  · exact False.elim (hne (hfr.trans hsr.symm))

/-- In the no-off-row case, hypothetical fixed-column containment forces all
inserted edges to be old row edges. -/
theorem segment_edgeSet_subset_row_of_subset_fixed_of_no_off_row
    (hsub :
      bump.deletedRowSegment.edgeSet ⊆ S.fixedColumnEdgeSet)
    (hno :
      ¬ ∃ v : V, v ∈ bump.segment.vertexSet ∧
        v ∉ bump.rowPath.vertexSet) :
    bump.segment.edgeSet ⊆ bump.rowPath.edgeSet := by
  classical
  have hseg :
      bump.segment.vertexSet ⊆
        ({bump.left, bump.right} : Finset V) :=
    bump.segment_vertexSet_subset_endpoints_of_no_off_row hno
  have hdel :
      bump.deletedRowSegment.vertexSet ⊆
        ({bump.left, bump.right} : Finset V) := by
    intro v hv
    exact hseg
      (bump.deletedRowSegment_vertexSet_subset_segment_of_subset_fixed
        hsub hv)
  rcases bump.deletedRowSegment_edgeSet_nonempty with ⟨erow, herow⟩
  have herow_eq : erow = s(bump.left, bump.right) :=
    bump.edge_eq_left_right_of_endpoint_vertex_support hdel herow
  have hedge_row :
      s(bump.left, bump.right) ∈ bump.rowPath.edgeSet := by
    simpa [herow_eq] using
      bump.deletedRowSegment_edgeSet_subset_row herow
  intro e he
  have heq : e = s(bump.left, bump.right) :=
    bump.edge_eq_left_right_of_endpoint_vertex_support hseg he
  simpa [heq] using hedge_row

/-- The deleted row interval cannot be fully covered by the fixed columns.
This is Lemma 2.1(1) of the supplied proof, derived from pairwise column
disjointness and simple-path uniqueness. -/
theorem deletedRowSegment_edgeSet_not_subset_fixed :
    ¬ bump.deletedRowSegment.edgeSet ⊆ S.fixedColumnEdgeSet := by
  classical
  intro hsub
  by_cases hoff :
      ∃ v : V, v ∈ bump.segment.vertexSet ∧
        v ∉ bump.rowPath.vertexSet
  · rcases hoff with ⟨v, hvseg, hvnot⟩
    have hvdel :
        v ∈ bump.deletedRowSegment.vertexSet :=
      bump.segment_vertexSet_subset_deleted_of_subset_fixed hsub hvseg
    exact hvnot
      (bump.rowPath.segmentOfBefore_vertexSet_subset
        bump.left_before_right hvdel)
  · have hsegrow :
        bump.segment.edgeSet ⊆ bump.rowPath.edgeSet :=
      bump.segment_edgeSet_subset_row_of_subset_fixed_of_no_off_row
        hsub hoff
    rcases bump.not_row_contained with hoff' | hedge
    · exact hoff hoff'
    · exact hedge hsegrow

/-- A concrete old row edge outside every fixed column. -/
theorem exists_deleted_edge_not_fixed :
    ∃ e : Sym2 V,
      e ∈ bump.deletedRowSegment.edgeSet ∧
        e ∉ S.fixedColumnEdgeSet := by
  classical
  exact Finset.not_subset.mp
    bump.deletedRowSegment_edgeSet_not_subset_fixed

/-- A deleted interval edge outside the fixed columns is absent from the
replacement row. -/
theorem deleted_edge_not_mem_replacementPath
    {e : Sym2 V}
    (he : e ∈ bump.deletedRowSegment.edgeSet)
    (hfixed : e ∉ S.fixedColumnEdgeSet) :
    e ∉ bump.replacementPath.path.edgeSet := by
  classical
  intro hrep
  rcases Finset.mem_union.1
      (bump.replacementPath.edgeSet_subset_parts hrep) with
    hpre_or_mid | hsuf
  · rcases Finset.mem_union.1 hpre_or_mid with hpre | hmid
    · exact Finset.disjoint_left.mp
        (graphPath_edgeDisjoint_of_vertex_inter_subset_singleton
          (x := bump.left) (by
            intro v hvdel hvpre
            have hv_before_left :=
              bump.rowPath.before_of_mem_takeUntil
                bump.left_mem_row hvpre
            have hleft_before_v :=
              bump.rowPath.before_of_mem_segmentOfBefore_left
                bump.left_before_right hvdel
            exact bump.rowPath.before_antisymm
              hv_before_left hleft_before_v))
        he hpre
    · apply hfixed
      exact Finset.mem_biUnion.2
        ⟨bump.column, Finset.mem_univ _,
          bump.orientedSegment_edgeSet_subset_column hmid⟩
  · exact Finset.disjoint_left.mp
      (graphPath_edgeDisjoint_of_vertex_inter_subset_singleton
        (x := bump.right) (by
          intro v hvdel hvsuf
          have hv_before_right :=
            bump.rowPath.before_of_mem_segmentOfBefore_right
              bump.left_before_right hvdel
          have hright_before_v :
              bump.rowPath.Before bump.right v :=
            ⟨bump.right_mem_row, hvsuf⟩
          exact bump.rowPath.before_antisymm
            hv_before_right hright_before_v))
      he hsuf

end Measure

/-! ## Auxiliary-graph locality -/

/-- The deleted row interval is internally clean for the new linkage. -/
theorem deletedRowSegment_clean_replacementLinkage :
    bump.deletedRowSegment.InternallyDisjointFromSet
      bump.replacementLinkage.toPathPacking.vertexSet := by
  classical
  intro v hvdel hvnew
  rcases (bump.replacementLinkage.toPathPacking.mem_vertexSet).1 hvnew with
    ⟨i, hvi⟩
  by_cases himid : i = bump.middleIndex
  · subst i
    have hvrep : v ∈ bump.replacementPath.path.vertexSet := by
      simpa using hvi
    rcases Finset.mem_union.1
        (bump.replacementPath.vertexSet_subset_parts hvrep) with
      hpre_or_seg | hsuf
    · rcases Finset.mem_union.1 hpre_or_seg with hpre | hseg
      · exact Or.inl (by
          have hv_before_left :=
            bump.rowPath.before_of_mem_takeUntil bump.left_mem_row hpre
          have hleft_before_v :=
            bump.rowPath.before_of_mem_segmentOfBefore_left
              bump.left_before_right hvdel
          simpa using bump.rowPath.before_antisymm
            hv_before_left hleft_before_v)
      · have hvrow : v ∈ bump.rowPath.vertexSet :=
          bump.rowPath.segmentOfBefore_vertexSet_subset
            bump.left_before_right hvdel
        rcases bump.orientedSegment_clean_row hseg hvrow with hleft | hright
        · exact Or.inl (by simpa using hleft)
        · exact Or.inr (by simpa using hright)
    · exact Or.inr (by
        have hv_before_right :=
          bump.rowPath.before_of_mem_segmentOfBefore_right
            bump.left_before_right hvdel
        have hright_before_v : bump.rowPath.Before bump.right v :=
          ⟨bump.right_mem_row, hsuf⟩
        simpa using bump.rowPath.before_antisymm
          hv_before_right hright_before_v)
  · have hvrow : v ∈ bump.rowPath.vertexSet :=
      bump.rowPath.segmentOfBefore_vertexSet_subset
        bump.left_before_right hvdel
    have hvrow_old :
        v ∈ (S.linkage.path bump.middleIndex).vertexSet := by
      simpa using hvrow
    have hvi_old : v ∈ (S.linkage.path i).vertexSet := by
      simpa [bump.replacementLinkage_path_of_ne himid] using hvi
    exact False.elim <|
      Finset.disjoint_left.mp
        (S.linkage.toPathPacking.node_disjoint
          (fun h => himid h.symm))
        hvrow_old hvi_old

/-- Vertex support removed from the old linkage. -/
noncomputable def deletedMiddleVertexSet : Finset V :=
  bump.deletedRowSegment.vertexSet

/-- Vertex support newly inserted into the linkage. -/
noncomputable def insertedSegmentVertexSet : Finset V :=
  bump.orientedSegment.vertexSet

/-- Every old row vertex lies in the retained prefix, deleted interval, or
retained suffix. -/
theorem row_vertex_mem_prefix_or_deleted_or_suffix
    {v : V} (hv : v ∈ bump.rowPath.vertexSet) :
    v ∈ (bump.rowPath.takeUntil bump.left_mem_row).vertexSet ∨
      v ∈ bump.deletedRowSegment.vertexSet ∨
        v ∈ (bump.rowPath.dropUntil bump.right_mem_row).vertexSet := by
  classical
  by_cases hv_before_left : bump.rowPath.Before v bump.left
  · exact Or.inl
      (bump.rowPath.mem_takeUntil_of_before
        bump.left_mem_row hv_before_left)
  · by_cases hright_before_v : bump.rowPath.Before bump.right v
    · rcases hright_before_v with ⟨_, hvdrop⟩
      exact Or.inr <| Or.inr (by simpa using hvdrop)
    · have hleft_before_v : bump.rowPath.Before bump.left v := by
        rcases le_total
            (bump.rowPath.vertexIndex bump.left)
            (bump.rowPath.vertexIndex v) with hle | hle
        · exact (bump.rowPath.before_iff_vertexIndex_le).2
            ⟨bump.left_mem_row, hv, hle⟩
        · exact False.elim (hv_before_left
            ((bump.rowPath.before_iff_vertexIndex_le).2
              ⟨hv, bump.left_mem_row, hle⟩))
      have hv_before_right : bump.rowPath.Before v bump.right := by
        rcases le_total
            (bump.rowPath.vertexIndex v)
            (bump.rowPath.vertexIndex bump.right) with hle | hle
        · exact (bump.rowPath.before_iff_vertexIndex_le).2
            ⟨hv, bump.right_mem_row, hle⟩
        · exact False.elim (hright_before_v
            ((bump.rowPath.before_iff_vertexIndex_le).2
              ⟨bump.right_mem_row, hv, hle⟩))
      exact Or.inr <| Or.inl <|
        bump.rowPath.mem_segmentOfBefore_of_before_of_before
          bump.left_before_right hleft_before_v hv_before_right

/-- Any old linkage vertex absent from the new linkage lies in the deleted
interval. -/
theorem old_link_vertex_not_new_mem_deletedMiddle
    {v : V} (hold : v ∈ S.linkage.toPathPacking.vertexSet)
    (hnew : v ∉ bump.replacementLinkage.toPathPacking.vertexSet) :
    v ∈ bump.deletedMiddleVertexSet := by
  classical
  rcases (S.linkage.toPathPacking.mem_vertexSet).1 hold with ⟨i, hvi⟩
  by_cases himid : i = bump.middleIndex
  · subst i
    have hvrow : v ∈ bump.rowPath.vertexSet := by simpa using hvi
    rcases bump.row_vertex_mem_prefix_or_deleted_or_suffix hvrow with
      hpre | hmid | hsuf
    · have hvrep : v ∈ bump.replacementPath.path.vertexSet :=
        bump.replacementPath.prefix_subset_path hpre
      exact False.elim (hnew <|
        (bump.replacementLinkage.toPathPacking.mem_vertexSet).2
          ⟨bump.middleIndex, by simpa using hvrep⟩)
    · simpa [deletedMiddleVertexSet] using hmid
    · have hvrep : v ∈ bump.replacementPath.path.vertexSet :=
        bump.replacementPath.suffix_subset_path hsuf
      exact False.elim (hnew <|
        (bump.replacementLinkage.toPathPacking.mem_vertexSet).2
          ⟨bump.middleIndex, by simpa using hvrep⟩)
  · have hvnew_path :
        v ∈ (bump.replacementLinkage.path i).vertexSet := by
      simpa [bump.replacementLinkage_path_of_ne himid] using hvi
    exact False.elim (hnew <|
      (bump.replacementLinkage.toPathPacking.mem_vertexSet).2
        ⟨i, hvnew_path⟩)

/-- Any genuinely new linkage vertex lies on the inserted segment. -/
theorem new_link_vertex_not_old_mem_insertedSegment
    {v : V}
    (hnew : v ∈ bump.replacementLinkage.toPathPacking.vertexSet)
    (hold : v ∉ S.linkage.toPathPacking.vertexSet) :
    v ∈ bump.insertedSegmentVertexSet := by
  classical
  rcases (bump.replacementLinkage.toPathPacking.mem_vertexSet).1 hnew with
    ⟨i, hvi⟩
  by_cases himid : i = bump.middleIndex
  · subst i
    have hvrep : v ∈ bump.replacementPath.path.vertexSet := by
      simpa using hvi
    rcases Finset.mem_union.1
        (bump.replacementPath.vertexSet_subset_parts hvrep) with
      hpre_or_mid | hsuf
    · rcases Finset.mem_union.1 hpre_or_mid with hpre | hmid
      · have hvrow : v ∈ bump.rowPath.vertexSet :=
          bump.rowPath.takeUntil_vertexSet_subset bump.left_mem_row hpre
        exact False.elim (hold <|
          (S.linkage.toPathPacking.mem_vertexSet).2
            ⟨bump.middleIndex, by simpa using hvrow⟩)
      · exact hmid
    · have hvrow : v ∈ bump.rowPath.vertexSet :=
        bump.rowPath.dropUntil_vertexSet_subset bump.right_mem_row hsuf
      exact False.elim (hold <|
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨bump.middleIndex, by simpa using hvrow⟩)
  · have hvold_path : v ∈ (S.linkage.path i).vertexSet := by
      simpa [bump.replacementLinkage_path_of_ne himid] using hvi
    exact False.elim (hold <|
      (S.linkage.toPathPacking.mem_vertexSet).2 ⟨i, hvold_path⟩)

/-- A new-clean path missing the deleted interval is old-clean. -/
theorem internallyDisjoint_old_of_new_clean_disjoint_deleted
    (P : GraphPath G)
    (hclean :
      P.InternallyDisjointFromSet
        bump.replacementLinkage.toPathPacking.vertexSet)
    (hmiss : Disjoint P.vertexSet bump.deletedMiddleVertexSet) :
    P.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet := by
  intro v hvP hvold
  by_cases hvnew :
      v ∈ bump.replacementLinkage.toPathPacking.vertexSet
  · exact hclean hvP hvnew
  · exact False.elim (Finset.disjoint_left.mp hmiss hvP <|
      bump.old_link_vertex_not_new_mem_deletedMiddle hvold hvnew)

/-- An old-clean path missing the inserted segment is new-clean. -/
theorem internallyDisjoint_new_of_old_clean_disjoint_inserted
    (P : GraphPath G)
    (hclean :
      P.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet)
    (hmiss : Disjoint P.vertexSet bump.insertedSegmentVertexSet) :
    P.InternallyDisjointFromSet
      bump.replacementLinkage.toPathPacking.vertexSet := by
  intro v hvP hvnew
  by_cases hvold : v ∈ S.linkage.toPathPacking.vertexSet
  · exact hclean hvP hvold
  · exact False.elim (Finset.disjoint_left.mp hmiss hvP <|
      bump.new_link_vertex_not_old_mem_insertedSegment hvnew hvold)

/-- A new bridge between unchanged paths is an old bridge when it misses the
deleted interval. -/
theorem old_aux_adj_of_new_bridge_unchanged_miss_deleted
    {i j : S.linkage.Index} (hij : i ≠ j)
    (himid : i ≠ bump.middleIndex)
    (hjmid : j ≠ bump.middleIndex)
    (β : bump.replacementLinkage.toPathPacking.BridgeBetween i j)
    (hmiss :
      Disjoint β.orientedPath.vertexSet bump.deletedMiddleVertexSet) :
    (linkageAuxGraph S.linkage).Adj i j := by
  refine ⟨hij, Or.inl ?_⟩
  refine ⟨PathPacking.BridgeBetween.of_orientedPath
    S.linkage.toPathPacking β.orientedPath ?_ ?_ ?_⟩
  · simpa [bump.replacementLinkage_path_of_ne himid] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
  · simpa [bump.replacementLinkage_path_of_ne hjmid] using
      PathPacking.BridgeBetween.orientedPath_target_mem_right β
  · exact bump.internallyDisjoint_old_of_new_clean_disjoint_deleted
      β.orientedPath β.orientedPath_internallyDisjoint hmiss

/-- An old bridge between unchanged paths is a new bridge when it misses the
inserted segment. -/
theorem new_aux_adj_of_old_bridge_unchanged_miss_inserted
    {i j : S.linkage.Index} (hij : i ≠ j)
    (himid : i ≠ bump.middleIndex)
    (hjmid : j ≠ bump.middleIndex)
    (β : S.linkage.toPathPacking.BridgeBetween i j)
    (hmiss :
      Disjoint β.orientedPath.vertexSet bump.insertedSegmentVertexSet) :
    (linkageAuxGraph bump.replacementLinkage).Adj i j := by
  refine ⟨hij, Or.inl ?_⟩
  refine ⟨PathPacking.BridgeBetween.of_orientedPath
    bump.replacementLinkage.toPathPacking β.orientedPath ?_ ?_ ?_⟩
  · simpa [bump.replacementLinkage_path_of_ne himid] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
  · simpa [bump.replacementLinkage_path_of_ne hjmid] using
      PathPacking.BridgeBetween.orientedPath_target_mem_right β
  · exact bump.internallyDisjoint_new_of_old_clean_disjoint_inserted
      β.orientedPath β.orientedPath_internallyDisjoint hmiss

/-- Stopping a new-clean path at its first deleted-interval contact produces
an old-clean prefix. -/
theorem cleanPrefixToDeleted_internallyDisjoint_old
    (P : GraphPath G)
    (hclean :
      P.InternallyDisjointFromSet
        bump.replacementLinkage.toPathPacking.vertexSet)
    (hne : (P.vertexSet ∩ bump.deletedMiddleVertexSet).Nonempty) :
    (P.cleanPrefixToSet bump.deletedMiddleVertexSet hne
      ).InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet := by
  intro v hvPrefix hvold
  have hcleanNew :
      (P.cleanPrefixToSet bump.deletedMiddleVertexSet hne
        ).InternallyDisjointFromSet
          bump.replacementLinkage.toPathPacking.vertexSet := by
    simpa [GraphPath.cleanPrefixToSet] using
      P.takeUntil_internallyDisjointFromSet
        (P.firstHitVertex_mem_vertexSet bump.deletedMiddleVertexSet hne)
        hclean
  by_cases hvnew :
      v ∈ bump.replacementLinkage.toPathPacking.vertexSet
  · exact hcleanNew hvPrefix hvnew
  · have hvdel :=
      bump.old_link_vertex_not_new_mem_deletedMiddle hvold hvnew
    have hv_eq :
        v = P.firstHitVertex bump.deletedMiddleVertexSet hne :=
      P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set
        bump.deletedMiddleVertexSet hne
        (by simpa [GraphPath.cleanPrefixToSet] using hvPrefix) hvdel
    exact Or.inr (by simp [GraphPath.cleanPrefixToSet, hv_eq])

/-- A new bridge from an unchanged path that hits the deleted interval
localizes its first endpoint to an old neighbor of the bumped row. -/
theorem old_aux_adj_to_middle_of_new_bridge_hits_deleted
    {i j : S.linkage.Index}
    (himid : i ≠ bump.middleIndex)
    (β : bump.replacementLinkage.toPathPacking.BridgeBetween i j)
    (hne :
      (β.orientedPath.vertexSet ∩
        bump.deletedMiddleVertexSet).Nonempty) :
    (linkageAuxGraph S.linkage).Adj i bump.middleIndex := by
  classical
  let P : GraphPath G := β.orientedPath
  let Prefix : GraphPath G :=
    P.cleanPrefixToSet bump.deletedMiddleVertexSet hne
  have hsrc_old :
      Prefix.source ∈ (S.linkage.path i).vertexSet := by
    have hsrc_new :=
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
    simpa [Prefix, P, bump.replacementLinkage_path_of_ne himid]
      using hsrc_new
  have hclean_old :
      Prefix.InternallyDisjointFromSet
        S.linkage.toPathPacking.vertexSet := by
    simpa [Prefix, P] using
      bump.cleanPrefixToDeleted_internallyDisjoint_old
        P β.orientedPath_internallyDisjoint hne
  have htgt_del :
      Prefix.target ∈ bump.deletedMiddleVertexSet := by
    simpa [Prefix, P] using
      P.cleanPrefixToSet_target_mem bump.deletedMiddleVertexSet hne
  have htgt_old :
      Prefix.target ∈ (S.linkage.path bump.middleIndex).vertexSet := by
    have htgt_row : Prefix.target ∈ bump.rowPath.vertexSet :=
      bump.rowPath.segmentOfBefore_vertexSet_subset
        bump.left_before_right htgt_del
    simpa using htgt_row
  exact ⟨himid, Or.inl
    ⟨PathPacking.BridgeBetween.of_orientedPath
      S.linkage.toPathPacking Prefix hsrc_old htgt_old hclean_old⟩⟩

/-- The predecessor corridor index of the bumped active row. -/
def prevIndex : S.linkage.Index :=
  S.corridor.index ⟨bump.row.1, by omega⟩

/-- The successor corridor index of the bumped active row. -/
def nextIndex : S.linkage.Index :=
  S.corridor.index ⟨bump.row.1 + 2, by omega⟩

theorem prev_adj_middle :
    (linkageAuxGraph S.linkage).Adj bump.prevIndex bump.middleIndex := by
  exact S.corridor.adj_of_consecutive (Or.inl rfl)

theorem middle_adj_next :
    (linkageAuxGraph S.linkage).Adj bump.middleIndex bump.nextIndex := by
  exact S.corridor.adj_of_consecutive (Or.inl rfl)

theorem prev_ne_next : bump.prevIndex ≠ bump.nextIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  dsimp [prevIndex, nextIndex] at hval
  omega

theorem prev_ne_middle : bump.prevIndex ≠ bump.middleIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  dsimp [prevIndex, middleIndex, AuxiliaryCorridor.activePosition] at hval
  omega

theorem middle_ne_next : bump.middleIndex ≠ bump.nextIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  dsimp [middleIndex, nextIndex, AuxiliaryCorridor.activePosition] at hval
  omega

theorem prev_degree_two :
    DegreeEquals (linkageAuxGraph S.linkage) bump.prevIndex 2 :=
  S.corridor.degree_two _

theorem middle_degree_two :
    DegreeEquals (linkageAuxGraph S.linkage) bump.middleIndex 2 :=
  S.corridor.degree_two _

theorem next_degree_two :
    DegreeEquals (linkageAuxGraph S.linkage) bump.nextIndex 2 :=
  S.corridor.degree_two _

/-- The local auxiliary triple affected by the bump. -/
noncomputable def localIndexSet : Finset S.linkage.Index :=
  {bump.prevIndex, bump.middleIndex, bump.nextIndex}

/-- Old degree saturation identifies every old neighbor of the middle row
with one of its two corridor neighbors. -/
theorem mem_localIndexSet_of_old_adj_middle
    {i : S.linkage.Index}
    (hadj : (linkageAuxGraph S.linkage).Adj i bump.middleIndex) :
    i ∈ bump.localIndexSet := by
  classical
  have hi : i = bump.prevIndex ∨ i = bump.nextIndex := by
    rcases DegreeEquals.two_adj_eq_or_eq
        bump.middle_degree_two
        ((linkageAuxGraph S.linkage).symm bump.prev_adj_middle)
        bump.middle_adj_next bump.prev_ne_next
        ((linkageAuxGraph S.linkage).symm hadj) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hi with rfl | rfl <;> simp [localIndexSet]

/-- If an old bridge first encounters the inserted segment, its prefix,
possibly continued along that segment, witnesses an old edge to the middle
row. -/
theorem old_aux_adj_to_middle_of_old_bridge_hits_inserted
    {i j : S.linkage.Index}
    (himid : i ≠ bump.middleIndex)
    (β : S.linkage.toPathPacking.BridgeBetween i j)
    (hne :
      (β.orientedPath.vertexSet ∩
        bump.insertedSegmentVertexSet).Nonempty) :
    (linkageAuxGraph S.linkage).Adj i bump.middleIndex := by
  classical
  let P : GraphPath G := β.orientedPath
  let Prefix : GraphPath G :=
    P.cleanPrefixToSet bump.insertedSegmentVertexSet hne
  have hsrc_old :
      Prefix.source ∈ (S.linkage.path i).vertexSet := by
    simpa [Prefix, P] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
  have hprefix_clean :
      Prefix.InternallyDisjointFromSet
        S.linkage.toPathPacking.vertexSet := by
    simpa [Prefix, P, GraphPath.cleanPrefixToSet] using
      P.takeUntil_internallyDisjointFromSet
        (P.firstHitVertex_mem_vertexSet
          bump.insertedSegmentVertexSet hne)
        β.orientedPath_internallyDisjoint
  have hxseg : Prefix.target ∈ bump.orientedSegment.vertexSet := by
    simpa [Prefix, P, insertedSegmentVertexSet] using
      P.cleanPrefixToSet_target_mem bump.insertedSegmentVertexSet hne
  by_cases hxold :
      Prefix.target ∈ S.linkage.toPathPacking.vertexSet
  · rcases bump.orientedSegment_clean_linkage hxseg hxold with
      hleft | hright
    · have htgt_old :
          Prefix.target ∈
            (S.linkage.path bump.middleIndex).vertexSet := by
        have hrow : Prefix.target ∈ bump.rowPath.vertexSet := by
          rw [hleft, bump.orientedSegment_source]
          exact bump.left_mem_row
        simpa using hrow
      exact ⟨himid, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking Prefix hsrc_old htgt_old
          hprefix_clean⟩⟩
    · have htgt_old :
          Prefix.target ∈
            (S.linkage.path bump.middleIndex).vertexSet := by
        have hrow : Prefix.target ∈ bump.rowPath.vertexSet := by
          rw [hright, bump.orientedSegment_target]
          exact bump.right_mem_row
        simpa using hrow
      exact ⟨himid, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking Prefix hsrc_old htgt_old
          hprefix_clean⟩⟩
  · let Tail : GraphPath G := bump.orientedSegment.dropUntil hxseg
    have hglue : Prefix.target = Tail.source := by
      simp [Tail, Prefix, P]
    have hinter :
        ∀ ⦃v : V⦄, v ∈ Prefix.vertexSet → v ∈ Tail.vertexSet →
          v = Prefix.target := by
      intro v hvpre hvtail
      have hvtail_seg : v ∈ bump.orientedSegment.vertexSet :=
        bump.orientedSegment.dropUntil_vertexSet_subset hxseg
          (by simpa [Tail] using hvtail)
      have hvins : v ∈ bump.insertedSegmentVertexSet := hvtail_seg
      have hv_eq :
          v = P.firstHitVertex bump.insertedSegmentVertexSet hne :=
        P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set
          bump.insertedSegmentVertexSet hne
          (by simpa [Prefix, GraphPath.cleanPrefixToSet] using hvpre)
          hvins
      simpa [Prefix, P, GraphPath.cleanPrefixToSet] using hv_eq
    let Joined : GraphPath G :=
      Prefix.appendWithEqOfInterSubsetTarget Tail hglue hinter
    have htail_clean :
        Tail.InternallyDisjointFromSet
          S.linkage.toPathPacking.vertexSet := by
      simpa [Tail] using
        bump.orientedSegment.dropUntil_internallyDisjointFromSet
          hxseg bump.orientedSegment_clean_linkage
    have hjoined_clean :
        Joined.InternallyDisjointFromSet
          S.linkage.toPathPacking.vertexSet := by
      simpa [Joined] using
        Prefix.appendWithEqOfInterSubsetTarget_internallyDisjointFromSet
          Tail hglue hinter hprefix_clean htail_clean hxold
    have hjoined_src :
        Joined.source ∈ (S.linkage.path i).vertexSet := by
      simpa [Joined] using hsrc_old
    have hjoined_tgt :
        Joined.target ∈
          (S.linkage.path bump.middleIndex).vertexSet := by
      have htgt : Joined.target = bump.right := by simp [Joined, Tail]
      have hrow : Joined.target ∈ bump.rowPath.vertexSet := by
        simpa [htgt] using bump.right_mem_row
      simpa using hrow
    exact ⟨himid, Or.inl
      ⟨PathPacking.BridgeBetween.of_orientedPath
        S.linkage.toPathPacking Joined hjoined_src hjoined_tgt
        hjoined_clean⟩⟩

/-- A new bridge ending on the replacement row always localizes to an old
edge ending on the original middle row. -/
theorem old_aux_adj_to_middle_of_new_bridge_to_replacement
    {i : S.linkage.Index}
    (himid : i ≠ bump.middleIndex)
    (β :
      bump.replacementLinkage.toPathPacking.BridgeBetween
        i bump.middleIndex) :
    (linkageAuxGraph S.linkage).Adj i bump.middleIndex := by
  classical
  by_cases hhit :
      (β.orientedPath.vertexSet ∩ bump.deletedMiddleVertexSet).Nonempty
  · exact bump.old_aux_adj_to_middle_of_new_bridge_hits_deleted
      himid β hhit
  · have hmiss :
        Disjoint β.orientedPath.vertexSet bump.deletedMiddleVertexSet := by
      rw [Finset.disjoint_left]
      intro v hvP hvDel
      exact hhit ⟨v, Finset.mem_inter.2 ⟨hvP, hvDel⟩⟩
    let P : GraphPath G := β.orientedPath
    have hsrc_old : P.source ∈ (S.linkage.path i).vertexSet := by
      simpa [P, bump.replacementLinkage_path_of_ne himid] using
        PathPacking.BridgeBetween.orientedPath_source_mem_left β
    have hclean_old :
        P.InternallyDisjointFromSet
          S.linkage.toPathPacking.vertexSet :=
      bump.internallyDisjoint_old_of_new_clean_disjoint_deleted
        P β.orientedPath_internallyDisjoint hmiss
    have htgt_rep :
        P.target ∈ bump.replacementPath.path.vertexSet := by
      simpa [P] using
        PathPacking.BridgeBetween.orientedPath_target_mem_right β
    rcases Finset.mem_union.1
        (bump.replacementPath.vertexSet_subset_parts htgt_rep) with
      hpre_or_seg | hsuf
    · rcases Finset.mem_union.1 hpre_or_seg with hpre | hseg
      · have htgt_old :
            P.target ∈
              (S.linkage.path bump.middleIndex).vertexSet := by
          have hrow : P.target ∈ bump.rowPath.vertexSet :=
            bump.rowPath.takeUntil_vertexSet_subset bump.left_mem_row hpre
          simpa using hrow
        exact ⟨himid, Or.inl
          ⟨PathPacking.BridgeBetween.of_orientedPath
            S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
      · by_cases hxold :
          P.target ∈ S.linkage.toPathPacking.vertexSet
        · rcases bump.orientedSegment_clean_linkage hseg hxold with
            hleft | hright
          · have htgt_old :
                P.target ∈
                  (S.linkage.path bump.middleIndex).vertexSet := by
              have hrow : P.target ∈ bump.rowPath.vertexSet := by
                rw [hleft, bump.orientedSegment_source]
                exact bump.left_mem_row
              simpa using hrow
            exact ⟨himid, Or.inl
              ⟨PathPacking.BridgeBetween.of_orientedPath
                S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
          · have htgt_old :
                P.target ∈
                  (S.linkage.path bump.middleIndex).vertexSet := by
              have hrow : P.target ∈ bump.rowPath.vertexSet := by
                rw [hright, bump.orientedSegment_target]
                exact bump.right_mem_row
              simpa using hrow
            exact ⟨himid, Or.inl
              ⟨PathPacking.BridgeBetween.of_orientedPath
                S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
        · let Tail : GraphPath G :=
            bump.orientedSegment.dropUntil hseg
          have hglue : P.target = Tail.source := by simp [Tail, P]
          have hinter :
              ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Tail.vertexSet →
                v = P.target := by
            intro v hvP hvtail
            have hvtail_seg : v ∈ bump.orientedSegment.vertexSet :=
              bump.orientedSegment.dropUntil_vertexSet_subset hseg
                (by simpa [Tail] using hvtail)
            have hvrep : v ∈ bump.replacementPath.path.vertexSet :=
              bump.replacementPath.segment_subset_path hvtail_seg
            have hvnew :
                v ∈ bump.replacementLinkage.toPathPacking.vertexSet :=
              (bump.replacementLinkage.toPathPacking.mem_vertexSet).2
                ⟨bump.middleIndex, by simpa using hvrep⟩
            rcases β.orientedPath_internallyDisjoint
                (by simpa [P] using hvP) hvnew with hsrc | htgt
            · have hsrc_i : P.source ∈ (S.linkage.path i).vertexSet :=
                hsrc_old
              exact False.elim <|
                Finset.disjoint_left.mp
                  (bump.replacementPath_nodeDisjoint_unchanged himid)
                  hvrep (by simpa [P, hsrc] using hsrc_i)
            · simpa [P] using htgt
          let Joined : GraphPath G :=
            P.appendWithEqOfInterSubsetTarget Tail hglue hinter
          have htail_clean :
              Tail.InternallyDisjointFromSet
                S.linkage.toPathPacking.vertexSet := by
            simpa [Tail] using
              bump.orientedSegment.dropUntil_internallyDisjointFromSet
                hseg bump.orientedSegment_clean_linkage
          have hjoined_clean :
              Joined.InternallyDisjointFromSet
                S.linkage.toPathPacking.vertexSet := by
            simpa [Joined] using
              P.appendWithEqOfInterSubsetTarget_internallyDisjointFromSet
                Tail hglue hinter hclean_old htail_clean hxold
          have hjoined_src :
              Joined.source ∈ (S.linkage.path i).vertexSet := by
            simpa [Joined] using hsrc_old
          have hjoined_tgt :
              Joined.target ∈
                (S.linkage.path bump.middleIndex).vertexSet := by
            have htgt : Joined.target = bump.right := by
              simp [Joined, Tail]
            have hrow : Joined.target ∈ bump.rowPath.vertexSet := by
              simpa [htgt] using bump.right_mem_row
            simpa using hrow
          exact ⟨himid, Or.inl
            ⟨PathPacking.BridgeBetween.of_orientedPath
              S.linkage.toPathPacking Joined hjoined_src hjoined_tgt
              hjoined_clean⟩⟩
    · have htgt_old :
          P.target ∈ (S.linkage.path bump.middleIndex).vertexSet := by
        have hrow : P.target ∈ bump.rowPath.vertexSet :=
          bump.rowPath.dropUntil_vertexSet_subset bump.right_mem_row hsuf
        simpa using hrow
      exact ⟨himid, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩

/-- If an old bridge between unchanged paths disappears, its first endpoint
is in the local triple. -/
theorem mem_local_of_old_bridge_not_new_unchanged
    {i j : S.linkage.Index} (hij : i ≠ j)
    (himid : i ≠ bump.middleIndex)
    (hjmid : j ≠ bump.middleIndex)
    (β : S.linkage.toPathPacking.BridgeBetween i j)
    (hnotnew :
      ¬ (linkageAuxGraph bump.replacementLinkage).Adj i j) :
    i ∈ bump.localIndexSet := by
  classical
  by_cases hhit :
      (β.orientedPath.vertexSet ∩
        bump.insertedSegmentVertexSet).Nonempty
  · exact bump.mem_localIndexSet_of_old_adj_middle <|
      bump.old_aux_adj_to_middle_of_old_bridge_hits_inserted
        himid β hhit
  · have hmiss :
        Disjoint β.orientedPath.vertexSet
          bump.insertedSegmentVertexSet := by
      rw [Finset.disjoint_left]
      intro v hvP hvIns
      exact hhit ⟨v, Finset.mem_inter.2 ⟨hvP, hvIns⟩⟩
    exact False.elim (hnotnew <|
      bump.new_aux_adj_of_old_bridge_unchanged_miss_inserted
        hij himid hjmid β hmiss)

/-- If a new bridge between unchanged paths did not exist before, its first
endpoint is in the local triple. -/
theorem mem_local_of_new_bridge_not_old_unchanged
    {i j : S.linkage.Index} (hij : i ≠ j)
    (himid : i ≠ bump.middleIndex)
    (hjmid : j ≠ bump.middleIndex)
    (β : bump.replacementLinkage.toPathPacking.BridgeBetween i j)
    (hnotold : ¬ (linkageAuxGraph S.linkage).Adj i j) :
    i ∈ bump.localIndexSet := by
  classical
  by_cases hhit :
      (β.orientedPath.vertexSet ∩
        bump.deletedMiddleVertexSet).Nonempty
  · exact bump.mem_localIndexSet_of_old_adj_middle <|
      bump.old_aux_adj_to_middle_of_new_bridge_hits_deleted
        himid β hhit
  · have hmiss :
        Disjoint β.orientedPath.vertexSet
          bump.deletedMiddleVertexSet := by
      rw [Finset.disjoint_left]
      intro v hvP hvDel
      exact hhit ⟨v, Finset.mem_inter.2 ⟨hvP, hvDel⟩⟩
    exact False.elim (hnotold <|
      bump.old_aux_adj_of_new_bridge_unchanged_miss_deleted
        hij himid hjmid β hmiss)

/-- Left-endpoint localization for a disappearing old auxiliary edge. -/
theorem mem_local_of_old_adj_not_new_left
    {i j : S.linkage.Index}
    (himid : i ≠ bump.middleIndex)
    (hold : (linkageAuxGraph S.linkage).Adj i j)
    (hnotnew :
      ¬ (linkageAuxGraph bump.replacementLinkage).Adj i j) :
    i ∈ bump.localIndexSet := by
  classical
  by_cases hj : j = bump.middleIndex
  · exact bump.mem_localIndexSet_of_old_adj_middle (by simpa [hj] using hold)
  · rcases hold with ⟨hij, hbridge⟩
    rcases hbridge with hβ | hβ
    · rcases hβ with ⟨β⟩
      exact bump.mem_local_of_old_bridge_not_new_unchanged
        hij himid hj β hnotnew
    · rcases hβ with ⟨β⟩
      exact bump.mem_local_of_old_bridge_not_new_unchanged
        hij himid hj (reverseCorridorBridge β) hnotnew

/-- Right-endpoint localization for a disappearing old auxiliary edge. -/
theorem mem_local_of_old_adj_not_new_right
    {i j : S.linkage.Index}
    (hjmid : j ≠ bump.middleIndex)
    (hold : (linkageAuxGraph S.linkage).Adj i j)
    (hnotnew :
      ¬ (linkageAuxGraph bump.replacementLinkage).Adj i j) :
    j ∈ bump.localIndexSet := by
  exact bump.mem_local_of_old_adj_not_new_left hjmid
    ((linkageAuxGraph S.linkage).symm hold)
    (fun h => hnotnew
      ((linkageAuxGraph bump.replacementLinkage).symm h))

/-- Left-endpoint localization for a genuinely new auxiliary edge. -/
theorem mem_local_of_new_adj_not_old_left
    {i j : S.linkage.Index}
    (himid : i ≠ bump.middleIndex)
    (hnew : (linkageAuxGraph bump.replacementLinkage).Adj i j)
    (hnotold : ¬ (linkageAuxGraph S.linkage).Adj i j) :
    i ∈ bump.localIndexSet := by
  classical
  by_cases hj : j = bump.middleIndex
  · rcases hnew with ⟨_hij, hbridge⟩
    have hadj :
        (linkageAuxGraph S.linkage).Adj i bump.middleIndex := by
      rcases hbridge with hβ | hβ
      · rcases hβ with ⟨β⟩
        exact bump.old_aux_adj_to_middle_of_new_bridge_to_replacement
          himid (by simpa [hj] using β)
      · rcases hβ with ⟨β⟩
        exact bump.old_aux_adj_to_middle_of_new_bridge_to_replacement
          himid (by simpa [hj] using reverseCorridorBridge β)
    exact bump.mem_localIndexSet_of_old_adj_middle hadj
  · rcases hnew with ⟨hij, hbridge⟩
    rcases hbridge with hβ | hβ
    · rcases hβ with ⟨β⟩
      exact bump.mem_local_of_new_bridge_not_old_unchanged
        hij himid hj β hnotold
    · rcases hβ with ⟨β⟩
      exact bump.mem_local_of_new_bridge_not_old_unchanged
        hij himid hj (reverseCorridorBridge β) hnotold

/-- Right-endpoint localization for a genuinely new auxiliary edge. -/
theorem mem_local_of_new_adj_not_old_right
    {i j : S.linkage.Index}
    (hjmid : j ≠ bump.middleIndex)
    (hnew : (linkageAuxGraph bump.replacementLinkage).Adj i j)
    (hnotold : ¬ (linkageAuxGraph S.linkage).Adj i j) :
    j ∈ bump.localIndexSet := by
  exact bump.mem_local_of_new_adj_not_old_left hjmid
    ((linkageAuxGraph bump.replacementLinkage).symm hnew)
    (fun h => hnotold ((linkageAuxGraph S.linkage).symm h))

/-- Every changed auxiliary edge has both endpoints in the predecessor,
middle, successor triple. -/
theorem auxiliary_change_supported_local :
    AdjChangeSupportedIn
      (linkageAuxGraph S.linkage)
      (linkageAuxGraph bump.replacementLinkage)
      bump.localIndexSet := by
  classical
  intro i j houtside
  constructor
  · intro hnew
    by_contra hnotold
    rcases houtside with hi | hj
    · have himid : i ≠ bump.middleIndex := by
        intro h
        exact hi (by simp [localIndexSet, h])
      exact hi (bump.mem_local_of_new_adj_not_old_left
        himid hnew hnotold)
    · have hjmid : j ≠ bump.middleIndex := by
        intro h
        exact hj (by simp [localIndexSet, h])
      exact hj (bump.mem_local_of_new_adj_not_old_right
        hjmid hnew hnotold)
  · intro hold
    by_contra hnotnew
    rcases houtside with hi | hj
    · have himid : i ≠ bump.middleIndex := by
        intro h
        exact hi (by simp [localIndexSet, h])
      exact hi (bump.mem_local_of_old_adj_not_new_left
        himid hold hnotnew)
    · have hjmid : j ≠ bump.middleIndex := by
        intro h
        exact hj (by simp [localIndexSet, h])
      exact hj (bump.mem_local_of_old_adj_not_new_right
        hjmid hold hnotnew)

/-- If the new middle auxiliary vertex still has degree two, locality forces
its two neighbors to remain the predecessor and successor. -/
theorem new_adjacent_to_prev_and_next_of_middle_degree_two
    (hnew :
      DegreeEquals
        (linkageAuxGraph bump.replacementLinkage)
        bump.middleIndex 2) :
    (linkageAuxGraph bump.replacementLinkage).Adj
        bump.middleIndex bump.prevIndex ∧
      (linkageAuxGraph bump.replacementLinkage).Adj
        bump.middleIndex bump.nextIndex := by
  classical
  let H := linkageAuxGraph S.linkage
  let H' := linkageAuxGraph bump.replacementLinkage
  rcases hnew with ⟨N, hN, hcard⟩
  have hsub :
      N ⊆ ({bump.prevIndex, bump.nextIndex} :
        Finset S.linkage.Index) := by
    intro x hx
    have hmx : H'.Adj bump.middleIndex x := (hN x).1 hx
    by_cases hlocal : x ∈ bump.localIndexSet
    · have hcases :
          x = bump.prevIndex ∨
            x = bump.middleIndex ∨ x = bump.nextIndex := by
        rw [localIndexSet] at hlocal
        rcases Finset.mem_insert.mp hlocal with hp | hrest
        · exact Or.inl hp
        · rcases Finset.mem_insert.mp hrest with hm | hn
          · exact Or.inr (Or.inl hm)
          · exact Or.inr (Or.inr (Finset.mem_singleton.mp hn))
      rcases hcases with hp | hm | hn
      · subst x
        exact Finset.mem_insert_self _ _
      · subst x
        exact False.elim (H'.loopless.irrefl bump.middleIndex hmx)
      · subst x
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr rfl))
    · have hmold : H.Adj bump.middleIndex x := by
        exact (bump.auxiliary_change_supported_local
          (u := bump.middleIndex) (v := x) (Or.inr hlocal)).1 hmx
      rcases DegreeEquals.two_adj_eq_or_eq
          bump.middle_degree_two
          ((linkageAuxGraph S.linkage).symm bump.prev_adj_middle)
          bump.middle_adj_next bump.prev_ne_next hmold with hp | hn
      · subst x
        exact Finset.mem_insert_self _ _
      · subst x
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr rfl))
  have hNpair :
      N = ({bump.prevIndex, bump.nextIndex} :
        Finset S.linkage.Index) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
    exact (Finset.card_pair bump.prev_ne_next).le
  constructor
  · exact (hN bump.prevIndex).1 (by
      rw [hNpair]
      exact Finset.mem_insert_self _ _)
  · exact (hN bump.nextIndex).1 (by
      rw [hNpair]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr rfl)))

/-- Choose the second old neighbor of the predecessor; it supplies the fixed
outside edge required by the three-vertex degree-saturation argument. -/
noncomputable def prevOuterIndex : S.linkage.Index :=
  Classical.choose
    (bump.prev_degree_two.two_exists_adj_ne bump.prev_adj_middle)

theorem prev_adj_prevOuter :
    (linkageAuxGraph S.linkage).Adj
      bump.prevIndex bump.prevOuterIndex :=
  (Classical.choose_spec
    (bump.prev_degree_two.two_exists_adj_ne bump.prev_adj_middle)).1

theorem prevOuter_ne_middle :
    bump.prevOuterIndex ≠ bump.middleIndex :=
  (Classical.choose_spec
    (bump.prev_degree_two.two_exists_adj_ne bump.prev_adj_middle)).2

theorem prevOuter_ne_prev :
    bump.prevOuterIndex ≠ bump.prevIndex := by
  exact bump.prev_adj_prevOuter.ne.symm

theorem prev_not_adj_next :
    ¬ (linkageAuxGraph S.linkage).Adj
      bump.prevIndex bump.nextIndex := by
  intro hadj
  have hcon := S.corridor.adj_iff_consecutive.mp hadj
  rcases hcon with h | h
  · dsimp [prevIndex, nextIndex] at h
    omega
  · dsimp [prevIndex, nextIndex] at h
    omega

theorem prevOuter_ne_next :
    bump.prevOuterIndex ≠ bump.nextIndex := by
  intro h
  apply bump.prev_not_adj_next
  simpa [h] using bump.prev_adj_prevOuter

/-- Locality yields the paper's bump dichotomy: either the number of
degree-two auxiliary vertices drops, or the entire auxiliary graph is
unchanged on the shared index type. -/
theorem degree_drop_or_auxiliary_equivalent :
    linkageAuxDegreeTwoCount bump.replacementLinkage <
        linkageAuxDegreeTwoCount S.linkage ∨
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j := by
  classical
  let H := linkageAuxGraph S.linkage
  let H' := linkageAuxGraph bump.replacementLinkage
  by_cases hMnew :
      DegreeEquals H' bump.middleIndex 2
  · have hnew :=
      bump.new_adjacent_to_prev_and_next_of_middle_degree_two hMnew
    have hresult :=
      bump_supported_degree_drop_or_aux_adj_iff
        H H' bump.prevOuterIndex bump.prevIndex
          bump.middleIndex bump.nextIndex
        (by
          simpa [H, H', localIndexSet] using
            bump.auxiliary_change_supported_local)
        (by simpa [H] using bump.prev_adj_prevOuter)
        (by simpa [H] using bump.prev_adj_middle)
        (by simpa [H] using bump.middle_adj_next)
        (by simpa [H'] using hnew.1.symm)
        (by simpa [H'] using hnew.2)
        (by simpa [H] using bump.prev_degree_two)
        (by simpa [H] using bump.middle_degree_two)
        (by simpa [H] using bump.next_degree_two)
        bump.prevOuter_ne_prev bump.prevOuter_ne_middle
        bump.prevOuter_ne_next bump.prev_ne_middle
        bump.prev_ne_next bump.middle_ne_next
    simpa [linkageAuxDegreeTwoCount, H, H'] using hresult
  · left
    have hlocalOld :
        ∀ x : S.linkage.Index, x ∈ bump.localIndexSet →
          DegreeEquals H x 2 := by
      intro x hx
      rw [localIndexSet] at hx
      rcases Finset.mem_insert.mp hx with hp | hrest
      · subst x
        simpa [H] using bump.prev_degree_two
      · rcases Finset.mem_insert.mp hrest with hm | hn
        · subst x
          simpa [H] using bump.middle_degree_two
        · have hn' := Finset.mem_singleton.mp hn
          subst x
          simpa [H] using bump.next_degree_two
    have hlt :=
      degreeTwoVertexCount_lt_of_supported_local_drop
        H H' bump.localIndexSet
        (by
          simpa [H, H'] using bump.auxiliary_change_supported_local)
        hlocalOld
        ⟨bump.middleIndex, by
          rw [localIndexSet]
          exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert_self _ _)),
          by simpa [H'] using hMnew⟩
    simpa [linkageAuxDegreeTwoCount, H, H'] using hlt

/-! ## Transported successor state -/

/-- The lower boundary is not the bumped active row. -/
theorem lowerIndex_ne_middle :
    S.corridor.index ⟨0, by omega⟩ ≠ bump.middleIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  simp [middleIndex, AuxiliaryCorridor.activePosition] at hval

/-- The upper boundary is not the bumped active row. -/
theorem upperIndex_ne_middle :
    S.corridor.index ⟨activeCount + 1, by omega⟩ ≠
      bump.middleIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  simp [middleIndex, AuxiliaryCorridor.activePosition] at hval
  omega

/-- A linkage index outside the corridor is not the bumped row index. -/
theorem outsideIndex_ne_middle
    {j : S.linkage.Index}
    (hj : j ∉ Set.range S.corridor.index) :
    j ≠ bump.middleIndex := by
  intro h
  apply hj
  refine ⟨S.corridor.activePosition bump.row, ?_⟩
  simpa [middleIndex] using h.symm

/-- In the non-drop branch, transport the entire corridor state across the
identity equivalence on linkage indices.  The replacement changes only the
bumped active row, so both boundaries and every path outside the corridor are
literally unchanged. -/
noncomputable def successorState
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    CorridorRowState original activeCount ι fixedColumn :=
  CorridorRowState.successorOfAuxEquiv S
    (linkage' := bump.replacementLinkage)
    (Equiv.refl S.linkage.Index)
    (fun i j => (hadj i j).symm)
    (by
      simpa using
        bump.replacementLinkage_path_of_ne bump.lowerIndex_ne_middle)
    (by
      simpa using
        bump.replacementLinkage_path_of_ne bump.upperIndex_ne_middle)
    (by
      intro j hj
      simpa using bump.replacementLinkage_path_of_ne
        (bump.outsideIndex_ne_middle hj))

@[simp] theorem successorState_linkage
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (bump.successorState hadj).linkage =
      bump.replacementLinkage :=
  rfl

@[simp] theorem successorState_corridor_index
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j)
    (q : Fin (activeCount + 2)) :
    (bump.successorState hadj).corridor.index q =
      S.corridor.index q :=
  rfl

@[simp] theorem successorState_activePath_bumped
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (bump.successorState hadj).corridor.activePath bump.row =
      bump.replacementPath.path := by
  change bump.replacementLinkage.path bump.middleIndex =
    bump.replacementPath.path
  exact bump.replacementLinkage_path_middle

/-- Every other active row is literally unchanged in the transported state. -/
theorem successorState_activePath_of_ne
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j)
    {r : Fin activeCount} (hr : r ≠ bump.row) :
    (bump.successorState hadj).corridor.activePath r =
      S.corridor.activePath r := by
  apply bump.replacementLinkage_path_of_ne
  intro hindex
  have hposition := S.corridor.index_injective hindex
  apply hr
  apply Fin.ext
  have hval := congrArg Fin.val hposition
  simpa [AuxiliaryCorridor.activePosition] using hval

section SuccessorMeasure

variable [Fintype ι] [DecidableEq ι]

/-- The new active-row union uses only edges from the old active rows or the
fixed columns. -/
theorem successorState_activeEdgeSet_subset_union_fixed
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (bump.successorState hadj).corridor.activeEdgeSet ⊆
      S.corridor.activeEdgeSet ∪ S.fixedColumnEdgeSet := by
  classical
  intro e he
  rw [AuxiliaryCorridor.activeEdgeSet] at he
  rcases Finset.mem_biUnion.mp he with ⟨r, _hruniv, her⟩
  by_cases hr : r = bump.row
  · subst r
    rw [bump.successorState_activePath_bumped hadj] at her
    rcases Finset.mem_union.mp
        (bump.replacementPath_edgeSet_subset_row_union_fixed her) with
      herow | hefixed
    · exact Finset.mem_union.mpr (Or.inl <|
        Finset.mem_biUnion.mpr
          ⟨bump.row, Finset.mem_univ _, by simpa [rowPath] using herow⟩)
    · exact Finset.mem_union.mpr (Or.inr hefixed)
  · rw [bump.successorState_activePath_of_ne hadj hr] at her
    exact Finset.mem_union.mpr (Or.inl <|
      Finset.mem_biUnion.mpr
        ⟨r, Finset.mem_univ _, her⟩)

/-- Distinct current active rows are edge-disjoint. -/
theorem rowPath_edgeDisjoint_activePath_of_ne
    {r : Fin activeCount} (hr : r ≠ bump.row) :
    bump.rowPath.EdgeDisjoint (S.corridor.activePath r) := by
  apply graphPath_edgeDisjoint_of_nodeDisjoint
  change
    (S.corridor.path (S.corridor.activePosition bump.row)).NodeDisjoint
      (S.corridor.path (S.corridor.activePosition r))
  apply S.corridor.path_nodeDisjoint
  intro hposition
  apply hr
  apply Fin.ext
  have hval := congrArg Fin.val hposition
  simpa [AuxiliaryCorridor.activePosition] using hval.symm

/-- A non-fixed edge of the deleted row interval is absent from the complete
new active-row union, not just from the replacement row. -/
theorem deleted_edge_not_mem_successor_activeEdgeSet
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j)
    {e : Sym2 V}
    (he : e ∈ bump.deletedRowSegment.edgeSet)
    (hfixed : e ∉ S.fixedColumnEdgeSet) :
    e ∉ (bump.successorState hadj).corridor.activeEdgeSet := by
  classical
  intro hnew
  rw [AuxiliaryCorridor.activeEdgeSet] at hnew
  rcases Finset.mem_biUnion.mp hnew with ⟨r, _hruniv, her⟩
  by_cases hr : r = bump.row
  · subst r
    rw [bump.successorState_activePath_bumped hadj] at her
    exact bump.deleted_edge_not_mem_replacementPath he hfixed her
  · rw [bump.successorState_activePath_of_ne hadj hr] at her
    exact Finset.disjoint_left.mp
      (bump.rowPath_edgeDisjoint_activePath_of_ne hr)
      (bump.deletedRowSegment_edgeSet_subset_row he) her

/-- In the auxiliary-isomorphism branch, the paper's explicit row measure
strictly decreases. -/
theorem successorState_rowMeasure_lt
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph bump.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (bump.successorState hadj).rowMeasure < S.rowMeasure := by
  classical
  rcases bump.exists_deleted_edge_not_fixed with
    ⟨e, hedeleted, henotfixed⟩
  have heold : e ∈ S.corridor.activeEdgeSet := by
    rw [AuxiliaryCorridor.activeEdgeSet]
    exact Finset.mem_biUnion.mpr
      ⟨bump.row, Finset.mem_univ _,
        bump.deletedRowSegment_edgeSet_subset_row hedeleted⟩
  have hlt :=
    outsideFixedMeasure_lt
      (bump.successorState_activeEdgeSet_subset_union_fixed hadj)
      heold henotfixed
      (bump.deleted_edge_not_mem_successor_activeEdgeSet
        hadj hedeleted henotfixed)
  simpa [CorridorRowState.rowMeasure,
    CorridorRowState.fixedColumnEdgeSet] using hlt

end SuccessorMeasure

/-- One source-faithful bump step either produces the required strict
degree-two drop, or returns a canonical corridor state with strictly smaller
row measure. -/
theorem step_degree_drop_or_smaller_state
    [Fintype V] [Fintype ι] [DecidableEq ι] :
    linkageAuxDegreeTwoCount bump.replacementLinkage <
        linkageAuxDegreeTwoCount S.linkage ∨
      ∃ S' : CorridorRowState original activeCount ι fixedColumn,
        S'.rowMeasure < S.rowMeasure := by
  rcases bump.degree_drop_or_auxiliary_equivalent with hdrop | hadj
  · exact Or.inl hdrop
  · exact Or.inr
      ⟨bump.successorState hadj,
        bump.successorState_rowMeasure_lt hadj⟩

end CorridorBumpWitness

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
