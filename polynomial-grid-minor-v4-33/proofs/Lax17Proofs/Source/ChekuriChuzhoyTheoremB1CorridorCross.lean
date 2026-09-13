import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorBump

namespace Lax17Proofs

universe u v w

/-!
# Cross rerouting in a generic Appendix B.1 corridor

This module starts the type-independent Figure 8 argument.  Unlike the older
type-one-specific witness, the two bridge segments are allowed to belong to
the same full column, as in the paper and in the supplied formal proof.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {original : PerfectPathPacking G A B}
variable {activeCount : ℕ} {ι : Type w}
variable {fixedColumn : ι → GraphPath G}

/-- A Figure-8 cross between two consecutive active rows of a common
corridor. -/
structure CorridorCross
    (S : CorridorRowState original activeCount ι fixedColumn) where
  lowerRow : Fin activeCount
  upperRow : Fin activeCount
  consecutive : lowerRow.1 + 1 = upperRow.1
  column₁ : ι
  column₂ : ι
  s₁ : V
  s₂ : V
  t₁ : V
  t₂ : V
  s₁_mem_lower : s₁ ∈ (S.corridor.activePath lowerRow).vertexSet
  s₂_mem_lower : s₂ ∈ (S.corridor.activePath lowerRow).vertexSet
  t₁_mem_upper : t₁ ∈ (S.corridor.activePath upperRow).vertexSet
  t₂_mem_upper : t₂ ∈ (S.corridor.activePath upperRow).vertexSet
  s₁_before_s₂ :
    (S.corridor.activePath lowerRow).Before s₁ s₂
  t₂_before_t₁ :
    (S.corridor.activePath upperRow).Before t₂ t₁
  s₁_ne_s₂ : s₁ ≠ s₂
  t₂_ne_t₁ : t₂ ≠ t₁
  segment₁ : GraphPath G
  segment₂ : GraphPath G
  segment₁_connects : segment₁.Connects {s₁} {t₁}
  segment₂_connects : segment₂.Connects {s₂} {t₂}
  segment₁_subset_column :
    segment₁.vertexSet ⊆ (fixedColumn column₁).vertexSet
  segment₂_subset_column :
    segment₂.vertexSet ⊆ (fixedColumn column₂).vertexSet
  segment₁_edges_subset_column :
    segment₁.edgeSet ⊆ (fixedColumn column₁).edgeSet
  segment₂_edges_subset_column :
    segment₂.edgeSet ⊆ (fixedColumn column₂).edgeSet
  segment₁_clean_linkage :
    segment₁.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet
  segment₂_clean_linkage :
    segment₂.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet
  segments_nodeDisjoint : segment₁.NodeDisjoint segment₂

namespace CorridorCross

variable {S : CorridorRowState original activeCount ι fixedColumn}

/-- The two active rows used by a cross are distinct. -/
theorem lowerRow_ne_upperRow (X : CorridorCross S) :
    X.lowerRow ≠ X.upperRow := by
  intro h
  have hval : X.lowerRow.1 = X.upperRow.1 := congrArg Fin.val h
  have hconsecutive := X.consecutive
  omega

/-- The two active row paths are vertex-disjoint linkage paths. -/
theorem rows_nodeDisjoint (X : CorridorCross S) :
    (S.corridor.activePath X.lowerRow).NodeDisjoint
      (S.corridor.activePath X.upperRow) := by
  apply S.corridor.path_nodeDisjoint
  intro h
  apply X.lowerRow_ne_upperRow
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [AuxiliaryCorridor.activePosition] at hval
  omega

/-- The first bridge oriented from the lower row to the upper row. -/
noncomputable def orientedSegment₁ (X : CorridorCross S) : GraphPath G :=
  X.segment₁.orient X.segment₁_connects

/-- The second bridge can be oriented from `t₂` back to `s₂`. -/
theorem segment₂_connects_reverse (X : CorridorCross S) :
    X.segment₂.Connects {X.t₂} {X.s₂} := by
  rcases X.segment₂_connects with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The second bridge in the direction used by the switched upper-to-lower
piece. -/
noncomputable def orientedSegment₂ (X : CorridorCross S) : GraphPath G :=
  X.segment₂.orient X.segment₂_connects_reverse

@[simp] theorem orientedSegment₁_source (X : CorridorCross S) :
    X.orientedSegment₁.source = X.s₁ := by
  simpa [orientedSegment₁] using
    GraphPath.orient_source_mem X.segment₁ X.segment₁_connects

@[simp] theorem orientedSegment₁_target (X : CorridorCross S) :
    X.orientedSegment₁.target = X.t₁ := by
  simpa [orientedSegment₁] using
    GraphPath.orient_target_mem X.segment₁ X.segment₁_connects

@[simp] theorem orientedSegment₂_source (X : CorridorCross S) :
    X.orientedSegment₂.source = X.t₂ := by
  simpa [orientedSegment₂] using
    GraphPath.orient_source_mem X.segment₂ X.segment₂_connects_reverse

@[simp] theorem orientedSegment₂_target (X : CorridorCross S) :
    X.orientedSegment₂.target = X.s₂ := by
  simpa [orientedSegment₂] using
    GraphPath.orient_target_mem X.segment₂ X.segment₂_connects_reverse

@[simp] theorem orientedSegment₁_vertexSet (X : CorridorCross S) :
    X.orientedSegment₁.vertexSet = X.segment₁.vertexSet := by
  simp [orientedSegment₁]

@[simp] theorem orientedSegment₂_vertexSet (X : CorridorCross S) :
    X.orientedSegment₂.vertexSet = X.segment₂.vertexSet := by
  simp [orientedSegment₂]

@[simp] theorem orientedSegment₁_edgeSet (X : CorridorCross S) :
    X.orientedSegment₁.edgeSet = X.segment₁.edgeSet := by
  simp [orientedSegment₁]

@[simp] theorem orientedSegment₂_edgeSet (X : CorridorCross S) :
    X.orientedSegment₂.edgeSet = X.segment₂.edgeSet := by
  simp [orientedSegment₂]

/-- The lower-row interval deleted by a cross. -/
noncomputable def deletedLowerInterval (X : CorridorCross S) : GraphPath G :=
  (S.corridor.activePath X.lowerRow).segmentOfBefore X.s₁_before_s₂

/-- The upper-row interval deleted by a cross. -/
noncomputable def deletedUpperInterval (X : CorridorCross S) : GraphPath G :=
  (S.corridor.activePath X.upperRow).segmentOfBefore X.t₂_before_t₁

/-- Reorientation preserves linkage cleanliness for the first bridge. -/
theorem orientedSegment₁_clean_linkage (X : CorridorCross S) :
    X.orientedSegment₁.InternallyDisjointFromSet
      S.linkage.toPathPacking.vertexSet := by
  intro v hv hlink
  have hv' : v ∈ X.segment₁.vertexSet := by simpa using hv
  exact (GraphPath.orient_isEndpoint X.segment₁ X.segment₁_connects).2
    (X.segment₁_clean_linkage hv' hlink)

/-- Reorientation preserves linkage cleanliness for the second bridge. -/
theorem orientedSegment₂_clean_linkage (X : CorridorCross S) :
    X.orientedSegment₂.InternallyDisjointFromSet
      S.linkage.toPathPacking.vertexSet := by
  intro v hv hlink
  have hv' : v ∈ X.segment₂.vertexSet := by simpa using hv
  exact
    (GraphPath.orient_isEndpoint X.segment₂
      X.segment₂_connects_reverse).2
      (X.segment₂_clean_linkage hv' hlink)

/-- The two oriented bridge paths remain vertex-disjoint. -/
theorem orientedSegments_nodeDisjoint (X : CorridorCross S) :
    X.orientedSegment₁.NodeDisjoint X.orientedSegment₂ := by
  simpa [GraphPath.NodeDisjoint] using X.segments_nodeDisjoint

/-! ## The two replacement paths -/

/-- The linkage index occupied by the lower crossed row. -/
def lowerIndex (X : CorridorCross S) : S.linkage.Index :=
  S.corridor.index (S.corridor.activePosition X.lowerRow)

/-- The linkage index occupied by the upper crossed row. -/
def upperIndex (X : CorridorCross S) : S.linkage.Index :=
  S.corridor.index (S.corridor.activePosition X.upperRow)

/-- The lower current row path. -/
def lowerPath (X : CorridorCross S) : GraphPath G :=
  S.corridor.activePath X.lowerRow

/-- The upper current row path. -/
def upperPath (X : CorridorCross S) : GraphPath G :=
  S.corridor.activePath X.upperRow

@[simp] theorem lowerPath_eq_linkage_path (X : CorridorCross S) :
    X.lowerPath = S.linkage.path X.lowerIndex :=
  rfl

@[simp] theorem upperPath_eq_linkage_path (X : CorridorCross S) :
    X.upperPath = S.linkage.path X.upperIndex :=
  rfl

theorem lowerIndex_ne_upperIndex (X : CorridorCross S) :
    X.lowerIndex ≠ X.upperIndex := by
  intro h
  apply X.lowerRow_ne_upperRow
  apply Fin.ext
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  simp [AuxiliaryCorridor.activePosition] at hval
  omega

/-- A reoriented bridge is disjoint from any linkage path other than its two
endpoint rows. -/
theorem orientedSegment₁_nodeDisjoint_unchanged
    (X : CorridorCross S) {i : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex) :
    X.orientedSegment₁.NodeDisjoint (S.linkage.path i) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvseg hvi
  have hpack : v ∈ S.linkage.toPathPacking.vertexSet :=
    (S.linkage.toPathPacking.mem_vertexSet).2 ⟨i, hvi⟩
  rcases X.orientedSegment₁_clean_linkage hvseg hpack with hs | ht
  · have hsrow :
        X.s₁ ∈ (S.linkage.path X.lowerIndex).vertexSet := by
      simpa using X.s₁_mem_lower
    have hsi : X.s₁ ∈ (S.linkage.path i).vertexSet := by
      simpa [hs] using hvi
    exact Finset.disjoint_left.mp
      (S.linkage.toPathPacking.node_disjoint
        (fun h => hilower h.symm)) hsrow hsi
  · have htrow :
        X.t₁ ∈ (S.linkage.path X.upperIndex).vertexSet := by
      simpa using X.t₁_mem_upper
    have hti : X.t₁ ∈ (S.linkage.path i).vertexSet := by
      simpa [ht] using hvi
    exact Finset.disjoint_left.mp
      (S.linkage.toPathPacking.node_disjoint
        (fun h => hiupper h.symm)) htrow hti

theorem orientedSegment₂_nodeDisjoint_unchanged
    (X : CorridorCross S) {i : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex) :
    X.orientedSegment₂.NodeDisjoint (S.linkage.path i) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvseg hvi
  have hpack : v ∈ S.linkage.toPathPacking.vertexSet :=
    (S.linkage.toPathPacking.mem_vertexSet).2 ⟨i, hvi⟩
  rcases X.orientedSegment₂_clean_linkage hvseg hpack with ht | hs
  · have htrow :
        X.t₂ ∈ (S.linkage.path X.upperIndex).vertexSet := by
      simpa using X.t₂_mem_upper
    have hti : X.t₂ ∈ (S.linkage.path i).vertexSet := by
      simpa [ht] using hvi
    exact Finset.disjoint_left.mp
      (S.linkage.toPathPacking.node_disjoint
        (fun h => hiupper h.symm)) htrow hti
  · have hsrow :
        X.s₂ ∈ (S.linkage.path X.lowerIndex).vertexSet := by
      simpa using X.s₂_mem_lower
    have hsi : X.s₂ ∈ (S.linkage.path i).vertexSet := by
      simpa [hs] using hvi
    exact Finset.disjoint_left.mp
      (S.linkage.toPathPacking.node_disjoint
        (fun h => hilower h.symm)) hsrow hsi

theorem s₂_not_mem_lower_prefix (X : CorridorCross S) :
    X.s₂ ∉ (X.lowerPath.takeUntil X.s₁_mem_lower).vertexSet := by
  intro hs₂
  have h₂₁ : X.lowerPath.Before X.s₂ X.s₁ :=
    X.lowerPath.before_of_mem_takeUntil X.s₁_mem_lower hs₂
  have heq := X.lowerPath.before_antisymm h₂₁ X.s₁_before_s₂
  exact X.s₁_ne_s₂ heq.symm

theorem s₁_not_mem_lower_suffix (X : CorridorCross S) :
    X.s₁ ∉ (X.lowerPath.dropUntil X.s₂_mem_lower).vertexSet := by
  intro hs₁
  have h₂₁ : X.lowerPath.Before X.s₂ X.s₁ :=
    ⟨X.s₂_mem_lower, hs₁⟩
  exact X.s₁_ne_s₂
    (X.lowerPath.before_antisymm X.s₁_before_s₂ h₂₁)

theorem t₁_not_mem_upper_prefix (X : CorridorCross S) :
    X.t₁ ∉ (X.upperPath.takeUntil X.t₂_mem_upper).vertexSet := by
  intro ht₁
  have h₁₂ : X.upperPath.Before X.t₁ X.t₂ :=
    X.upperPath.before_of_mem_takeUntil X.t₂_mem_upper ht₁
  have heq := X.upperPath.before_antisymm h₁₂ X.t₂_before_t₁
  exact X.t₂_ne_t₁ heq.symm

theorem t₂_not_mem_upper_suffix (X : CorridorCross S) :
    X.t₂ ∉ (X.upperPath.dropUntil X.t₁_mem_upper).vertexSet := by
  intro ht₂
  have h₁₂ : X.upperPath.Before X.t₁ X.t₂ :=
    ⟨X.t₁_mem_upper, ht₂⟩
  exact X.t₂_ne_t₁
    (X.upperPath.before_antisymm X.t₂_before_t₁ h₁₂)

theorem lower_prefix_disjoint_suffix (X : CorridorCross S) :
    Disjoint
      (X.lowerPath.takeUntil X.s₁_mem_lower).vertexSet
      (X.lowerPath.dropUntil X.s₂_mem_lower).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvpre hvsuf
  have hv₁ : X.lowerPath.Before v X.s₁ :=
    X.lowerPath.before_of_mem_takeUntil X.s₁_mem_lower hvpre
  have h₂v : X.lowerPath.Before X.s₂ v := ⟨X.s₂_mem_lower, hvsuf⟩
  have h₂₁ := X.lowerPath.before_trans h₂v hv₁
  exact X.s₁_ne_s₂
    (X.lowerPath.before_antisymm h₂₁ X.s₁_before_s₂).symm

theorem upper_prefix_disjoint_suffix (X : CorridorCross S) :
    Disjoint
      (X.upperPath.takeUntil X.t₂_mem_upper).vertexSet
      (X.upperPath.dropUntil X.t₁_mem_upper).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvpre hvsuf
  have hv₂ : X.upperPath.Before v X.t₂ :=
    X.upperPath.before_of_mem_takeUntil X.t₂_mem_upper hvpre
  have h₁v : X.upperPath.Before X.t₁ v := ⟨X.t₁_mem_upper, hvsuf⟩
  have h₁₂ := X.upperPath.before_trans h₁v hv₂
  exact X.t₂_ne_t₁
    (X.upperPath.before_antisymm h₁₂ X.t₂_before_t₁).symm

theorem lower_upper_disjoint_at
    (X : CorridorCross S) {v : V}
    (hlower : v ∈ X.lowerPath.vertexSet)
    (hupper : v ∈ X.upperPath.vertexSet) : False :=
  Finset.disjoint_left.mp X.rows_nodeDisjoint hlower hupper

theorem t₁_not_mem_lower (X : CorridorCross S) :
    X.t₁ ∉ X.lowerPath.vertexSet :=
  fun h => X.lower_upper_disjoint_at h X.t₁_mem_upper

theorem t₂_not_mem_lower (X : CorridorCross S) :
    X.t₂ ∉ X.lowerPath.vertexSet :=
  fun h => X.lower_upper_disjoint_at h X.t₂_mem_upper

theorem s₁_not_mem_upper (X : CorridorCross S) :
    X.s₁ ∉ X.upperPath.vertexSet :=
  fun h => X.lower_upper_disjoint_at X.s₁_mem_lower h

theorem s₂_not_mem_upper (X : CorridorCross S) :
    X.s₂ ∉ X.upperPath.vertexSet :=
  fun h => X.lower_upper_disjoint_at X.s₂_mem_lower h

theorem lower_prefix_inter_segment₁_subset_s₁ (X : CorridorCross S) :
    ∀ ⦃v : V⦄,
      v ∈ (X.lowerPath.takeUntil X.s₁_mem_lower).vertexSet →
      v ∈ X.orientedSegment₁.vertexSet →
      v = (X.lowerPath.takeUntil X.s₁_mem_lower).target := by
  intro v hvpre hvseg
  have hvrow : v ∈ X.lowerPath.vertexSet :=
    X.lowerPath.takeUntil_vertexSet_subset X.s₁_mem_lower hvpre
  have hvlink : v ∈ S.linkage.toPathPacking.vertexSet :=
    (S.linkage.toPathPacking.mem_vertexSet).2
      ⟨X.lowerIndex, by simpa using hvrow⟩
  rcases X.orientedSegment₁_clean_linkage hvseg hvlink with hs | ht
  · simpa using hs
  · exact False.elim (X.t₁_not_mem_lower (by simpa [ht] using hvrow))

theorem upper_prefix_inter_segment₂_subset_t₂ (X : CorridorCross S) :
    ∀ ⦃v : V⦄,
      v ∈ (X.upperPath.takeUntil X.t₂_mem_upper).vertexSet →
      v ∈ X.orientedSegment₂.vertexSet →
      v = (X.upperPath.takeUntil X.t₂_mem_upper).target := by
  intro v hvpre hvseg
  have hvrow : v ∈ X.upperPath.vertexSet :=
    X.upperPath.takeUntil_vertexSet_subset X.t₂_mem_upper hvpre
  have hvlink : v ∈ S.linkage.toPathPacking.vertexSet :=
    (S.linkage.toPathPacking.mem_vertexSet).2
      ⟨X.upperIndex, by simpa using hvrow⟩
  rcases X.orientedSegment₂_clean_linkage hvseg hvlink with ht | hs
  · simpa using ht
  · exact False.elim (X.s₂_not_mem_upper (by simpa [hs] using hvrow))

end CorridorCross

/-- Exact support information for the two concrete paths produced by a cross
switch. -/
structure CorridorCrossReplacementPaths
    {S : CorridorRowState original activeCount ι fixedColumn}
    (X : CorridorCross S) where
  lowerReplacement : GraphPath G
  upperReplacement : GraphPath G
  lower_source_eq : lowerReplacement.source = X.lowerPath.source
  lower_target_eq : lowerReplacement.target = X.upperPath.target
  upper_source_eq : upperReplacement.source = X.upperPath.source
  upper_target_eq : upperReplacement.target = X.lowerPath.target
  s₁_mem_lowerReplacement : X.s₁ ∈ lowerReplacement.vertexSet
  t₁_mem_lowerReplacement : X.t₁ ∈ lowerReplacement.vertexSet
  t₂_mem_upperReplacement : X.t₂ ∈ upperReplacement.vertexSet
  s₂_mem_upperReplacement : X.s₂ ∈ upperReplacement.vertexSet
  lower_prefix_subset :
    (X.lowerPath.takeUntil X.s₁_mem_lower).vertexSet ⊆
      lowerReplacement.vertexSet
  segment₁_subset :
    X.orientedSegment₁.vertexSet ⊆ lowerReplacement.vertexSet
  upper_suffix_subset :
    (X.upperPath.dropUntil X.t₁_mem_upper).vertexSet ⊆
      lowerReplacement.vertexSet
  upper_prefix_subset :
    (X.upperPath.takeUntil X.t₂_mem_upper).vertexSet ⊆
      upperReplacement.vertexSet
  segment₂_subset :
    X.orientedSegment₂.vertexSet ⊆ upperReplacement.vertexSet
  lower_suffix_subset :
    (X.lowerPath.dropUntil X.s₂_mem_lower).vertexSet ⊆
      upperReplacement.vertexSet
  lower_vertexSet_subset_parts :
    lowerReplacement.vertexSet ⊆
      ((X.lowerPath.takeUntil X.s₁_mem_lower).vertexSet ∪
          X.orientedSegment₁.vertexSet) ∪
        (X.upperPath.dropUntil X.t₁_mem_upper).vertexSet
  upper_vertexSet_subset_parts :
    upperReplacement.vertexSet ⊆
      ((X.upperPath.takeUntil X.t₂_mem_upper).vertexSet ∪
          X.orientedSegment₂.vertexSet) ∪
        (X.lowerPath.dropUntil X.s₂_mem_lower).vertexSet
  lower_edgeSet_subset :
    lowerReplacement.edgeSet ⊆
      (X.lowerPath.edgeSet ∪ X.orientedSegment₁.edgeSet) ∪
        X.upperPath.edgeSet
  upper_edgeSet_subset :
    upperReplacement.edgeSet ⊆
      (X.upperPath.edgeSet ∪ X.orientedSegment₂.edgeSet) ∪
        X.lowerPath.edgeSet

namespace CorridorCross

variable {S : CorridorRowState original activeCount ι fixedColumn}

/-- The two simple paths obtained by switching the crossed row tails. -/
noncomputable def replacementPaths
    (X : CorridorCross S) : CorridorCrossReplacementPaths X := by
  classical
  let lowerPre := X.lowerPath.takeUntil X.s₁_mem_lower
  let bridge₁ := X.orientedSegment₁
  let upperSuf := X.upperPath.dropUntil X.t₁_mem_upper
  have hpre_bridge : lowerPre.target = bridge₁.source := by
    simp [lowerPre, bridge₁]
  have hpre_bridge_inter :
      ∀ ⦃v : V⦄, v ∈ lowerPre.vertexSet → v ∈ bridge₁.vertexSet →
        v = lowerPre.target := by
    intro v hvpre hvbridge
    simpa [lowerPre, bridge₁] using
      X.lower_prefix_inter_segment₁_subset_s₁
        (v := v) (by simpa [lowerPre] using hvpre)
        (by simpa [bridge₁] using hvbridge)
  let lowerPreBridge :=
    lowerPre.appendWithEqOfInterSubsetTarget bridge₁
      hpre_bridge hpre_bridge_inter
  have hpreBridge_suf : lowerPreBridge.target = upperSuf.source := by
    simp [lowerPreBridge, lowerPre, bridge₁, upperSuf]
  have hpreBridge_suf_inter :
      ∀ ⦃v : V⦄,
        v ∈ lowerPreBridge.vertexSet → v ∈ upperSuf.vertexSet →
          v = lowerPreBridge.target := by
    intro v hvleft hvsuf
    have hvparts : v ∈ lowerPre.vertexSet ∪ bridge₁.vertexSet :=
      IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_vertexSet_subset
        lowerPre bridge₁ hpre_bridge hpre_bridge_inter hvleft
    have hvupper : v ∈ X.upperPath.vertexSet :=
      X.upperPath.dropUntil_vertexSet_subset X.t₁_mem_upper
        (by simpa [upperSuf] using hvsuf)
    rcases Finset.mem_union.1 hvparts with hvpre | hvbridge
    · have hvlower : v ∈ X.lowerPath.vertexSet :=
        X.lowerPath.takeUntil_vertexSet_subset X.s₁_mem_lower
          (by simpa [lowerPre] using hvpre)
      exact False.elim (X.lower_upper_disjoint_at hvlower hvupper)
    · have hvlink : v ∈ S.linkage.toPathPacking.vertexSet :=
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨X.upperIndex, by simpa using hvupper⟩
      rcases X.orientedSegment₁_clean_linkage
          (by simpa [bridge₁] using hvbridge) hvlink with hs | ht
      · exact False.elim (X.s₁_not_mem_upper (by simpa [hs] using hvupper))
      · simpa [lowerPreBridge, bridge₁] using ht
  let lowerWhole :=
    lowerPreBridge.appendWithEqOfInterSubsetTarget upperSuf
      hpreBridge_suf hpreBridge_suf_inter

  let upperPre := X.upperPath.takeUntil X.t₂_mem_upper
  let bridge₂ := X.orientedSegment₂
  let lowerSuf := X.lowerPath.dropUntil X.s₂_mem_lower
  have hpre_bridge₂ : upperPre.target = bridge₂.source := by
    simp [upperPre, bridge₂]
  have hpre_bridge₂_inter :
      ∀ ⦃v : V⦄, v ∈ upperPre.vertexSet → v ∈ bridge₂.vertexSet →
        v = upperPre.target := by
    intro v hvpre hvbridge
    simpa [upperPre, bridge₂] using
      X.upper_prefix_inter_segment₂_subset_t₂
        (v := v) (by simpa [upperPre] using hvpre)
        (by simpa [bridge₂] using hvbridge)
  let upperPreBridge :=
    upperPre.appendWithEqOfInterSubsetTarget bridge₂
      hpre_bridge₂ hpre_bridge₂_inter
  have hpreBridge_suf₂ : upperPreBridge.target = lowerSuf.source := by
    simp [upperPreBridge, upperPre, bridge₂, lowerSuf]
  have hpreBridge_suf₂_inter :
      ∀ ⦃v : V⦄,
        v ∈ upperPreBridge.vertexSet → v ∈ lowerSuf.vertexSet →
          v = upperPreBridge.target := by
    intro v hvleft hvsuf
    have hvparts : v ∈ upperPre.vertexSet ∪ bridge₂.vertexSet :=
      IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_vertexSet_subset
        upperPre bridge₂ hpre_bridge₂ hpre_bridge₂_inter hvleft
    have hvlower : v ∈ X.lowerPath.vertexSet :=
      X.lowerPath.dropUntil_vertexSet_subset X.s₂_mem_lower
        (by simpa [lowerSuf] using hvsuf)
    rcases Finset.mem_union.1 hvparts with hvpre | hvbridge
    · have hvupper : v ∈ X.upperPath.vertexSet :=
        X.upperPath.takeUntil_vertexSet_subset X.t₂_mem_upper
          (by simpa [upperPre] using hvpre)
      exact False.elim (X.lower_upper_disjoint_at hvlower hvupper)
    · have hvlink : v ∈ S.linkage.toPathPacking.vertexSet :=
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨X.lowerIndex, by simpa using hvlower⟩
      rcases X.orientedSegment₂_clean_linkage
          (by simpa [bridge₂] using hvbridge) hvlink with ht | hs
      · exact False.elim (X.t₂_not_mem_lower (by simpa [ht] using hvlower))
      · simpa [upperPreBridge, bridge₂] using hs
  let upperWhole :=
    upperPreBridge.appendWithEqOfInterSubsetTarget lowerSuf
      hpreBridge_suf₂ hpreBridge_suf₂_inter
  refine
    { lowerReplacement := lowerWhole
      upperReplacement := upperWhole
      lower_source_eq := ?_
      lower_target_eq := ?_
      upper_source_eq := ?_
      upper_target_eq := ?_
      s₁_mem_lowerReplacement := ?_
      t₁_mem_lowerReplacement := ?_
      t₂_mem_upperReplacement := ?_
      s₂_mem_upperReplacement := ?_
      lower_prefix_subset := ?_
      segment₁_subset := ?_
      upper_suffix_subset := ?_
      upper_prefix_subset := ?_
      segment₂_subset := ?_
      lower_suffix_subset := ?_
      lower_vertexSet_subset_parts := ?_
      upper_vertexSet_subset_parts := ?_
      lower_edgeSet_subset := ?_
      upper_edgeSet_subset := ?_ }
  · simp [lowerWhole, lowerPreBridge, lowerPre]
  · simp [lowerWhole, lowerPreBridge, upperSuf]
  · simp [upperWhole, upperPreBridge, upperPre]
  · simp [upperWhole, upperPreBridge, lowerSuf]
  · exact
      GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        lowerPreBridge upperSuf hpreBridge_suf hpreBridge_suf_inter
        (GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
          lowerPre bridge₁ hpre_bridge hpre_bridge_inter
          (by simpa [lowerPre] using
            GraphPath.target_mem_vertexSet lowerPre))
  · exact
      GraphPath.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
        lowerPreBridge upperSuf hpreBridge_suf hpreBridge_suf_inter
        (by simpa [upperSuf] using
          GraphPath.source_mem_vertexSet upperSuf)
  · exact
      GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        upperPreBridge lowerSuf hpreBridge_suf₂ hpreBridge_suf₂_inter
        (GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
          upperPre bridge₂ hpre_bridge₂ hpre_bridge₂_inter
          (by simpa [upperPre] using
            GraphPath.target_mem_vertexSet upperPre))
  · exact
      GraphPath.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
        upperPreBridge lowerSuf hpreBridge_suf₂ hpreBridge_suf₂_inter
        (by simpa [lowerSuf] using
          GraphPath.source_mem_vertexSet lowerSuf)
  · intro v hv
    exact
      GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        lowerPreBridge upperSuf hpreBridge_suf hpreBridge_suf_inter
        (GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
          lowerPre bridge₁ hpre_bridge hpre_bridge_inter
          (by simpa [lowerPre] using hv))
  · intro v hv
    exact
      GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        lowerPreBridge upperSuf hpreBridge_suf hpreBridge_suf_inter
        (GraphPath.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
          lowerPre bridge₁ hpre_bridge hpre_bridge_inter
          (by simpa [bridge₁] using hv))
  · intro v hv
    exact
      GraphPath.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
        lowerPreBridge upperSuf hpreBridge_suf hpreBridge_suf_inter
        (by simpa [upperSuf] using hv)
  · intro v hv
    exact
      GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        upperPreBridge lowerSuf hpreBridge_suf₂ hpreBridge_suf₂_inter
        (GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
          upperPre bridge₂ hpre_bridge₂ hpre_bridge₂_inter
          (by simpa [upperPre] using hv))
  · intro v hv
    exact
      GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        upperPreBridge lowerSuf hpreBridge_suf₂ hpreBridge_suf₂_inter
        (GraphPath.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
          upperPre bridge₂ hpre_bridge₂ hpre_bridge₂_inter
          (by simpa [bridge₂] using hv))
  · intro v hv
    exact
      GraphPath.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
        upperPreBridge lowerSuf hpreBridge_suf₂ hpreBridge_suf₂_inter
        (by simpa [lowerSuf] using hv)
  · intro v hv
    have hv' :=
      IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_vertexSet_subset
      lowerPreBridge upperSuf hpreBridge_suf hpreBridge_suf_inter hv
    rcases Finset.mem_union.1 hv' with hvpm | hvsuf
    · have hvpm' :=
        IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_vertexSet_subset
        lowerPre bridge₁ hpre_bridge hpre_bridge_inter hvpm
      rcases Finset.mem_union.1 hvpm' with hvpre | hvbridge
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inl <| by simpa [lowerPre] using hvpre
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inr <| by simpa [bridge₁] using hvbridge
    · exact Finset.mem_union.2 <| Or.inr <| by simpa [upperSuf] using hvsuf
  · intro v hv
    have hv' :=
      IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_vertexSet_subset
      upperPreBridge lowerSuf hpreBridge_suf₂ hpreBridge_suf₂_inter hv
    rcases Finset.mem_union.1 hv' with hvpm | hvsuf
    · have hvpm' :=
        IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_vertexSet_subset
        upperPre bridge₂ hpre_bridge₂ hpre_bridge₂_inter hvpm
      rcases Finset.mem_union.1 hvpm' with hvpre | hvbridge
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inl <| by simpa [upperPre] using hvpre
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inr <| by simpa [bridge₂] using hvbridge
    · exact Finset.mem_union.2 <| Or.inr <| by simpa [lowerSuf] using hvsuf
  · intro e he
    have he' :=
      IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_edgeSet_subset
      lowerPreBridge upperSuf hpreBridge_suf hpreBridge_suf_inter he
    rcases Finset.mem_union.1 he' with hepm | hesuf
    · have hepm' :=
        IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_edgeSet_subset
        lowerPre bridge₁ hpre_bridge hpre_bridge_inter hepm
      rcases Finset.mem_union.1 hepm' with hepre | hebridge
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inl <|
            X.lowerPath.takeUntil_edgeSet_subset X.s₁_mem_lower
              (by simpa [lowerPre] using hepre)
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inr <| by simpa [bridge₁] using hebridge
    · exact Finset.mem_union.2 <| Or.inr <|
        X.upperPath.dropUntil_edgeSet_subset X.t₁_mem_upper
          (by simpa [upperSuf] using hesuf)
  · intro e he
    have he' :=
      IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_edgeSet_subset
      upperPreBridge lowerSuf hpreBridge_suf₂ hpreBridge_suf₂_inter he
    rcases Finset.mem_union.1 he' with hepm | hesuf
    · have hepm' :=
        IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_edgeSet_subset
        upperPre bridge₂ hpre_bridge₂ hpre_bridge₂_inter hepm
      rcases Finset.mem_union.1 hepm' with hepre | hebridge
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inl <|
            X.upperPath.takeUntil_edgeSet_subset X.t₂_mem_upper
              (by simpa [upperPre] using hepre)
      · exact Finset.mem_union.2 <| Or.inl <|
          Finset.mem_union.2 <| Or.inr <| by simpa [bridge₂] using hebridge
    · exact Finset.mem_union.2 <| Or.inr <|
        X.lowerPath.dropUntil_edgeSet_subset X.s₂_mem_lower
          (by simpa [lowerSuf] using hesuf)

/-- A bridge clean with respect to the linkage is clean with respect to either
crossed row. -/
theorem orientedSegment₁_clean_lower (X : CorridorCross S) :
    X.orientedSegment₁.InternallyDisjointFromSet X.lowerPath.vertexSet := by
  intro v hvseg hvrow
  exact X.orientedSegment₁_clean_linkage hvseg
    ((S.linkage.toPathPacking.mem_vertexSet).2
      ⟨X.lowerIndex, by simpa using hvrow⟩)

theorem orientedSegment₁_clean_upper (X : CorridorCross S) :
    X.orientedSegment₁.InternallyDisjointFromSet X.upperPath.vertexSet := by
  intro v hvseg hvrow
  exact X.orientedSegment₁_clean_linkage hvseg
    ((S.linkage.toPathPacking.mem_vertexSet).2
      ⟨X.upperIndex, by simpa using hvrow⟩)

theorem orientedSegment₂_clean_lower (X : CorridorCross S) :
    X.orientedSegment₂.InternallyDisjointFromSet X.lowerPath.vertexSet := by
  intro v hvseg hvrow
  exact X.orientedSegment₂_clean_linkage hvseg
    ((S.linkage.toPathPacking.mem_vertexSet).2
      ⟨X.lowerIndex, by simpa using hvrow⟩)

theorem orientedSegment₂_clean_upper (X : CorridorCross S) :
    X.orientedSegment₂.InternallyDisjointFromSet X.upperPath.vertexSet := by
  intro v hvseg hvrow
  exact X.orientedSegment₂_clean_linkage hvseg
    ((S.linkage.toPathPacking.mem_vertexSet).2
      ⟨X.upperIndex, by simpa using hvrow⟩)

/-- The two switched paths are vertex-disjoint. -/
theorem replacementPaths_nodeDisjoint (X : CorridorCross S) :
    X.replacementPaths.lowerReplacement.NodeDisjoint
      X.replacementPaths.upperReplacement := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvlower hvupper
  have hlparts :=
    X.replacementPaths.lower_vertexSet_subset_parts hvlower
  have hupart :=
    X.replacementPaths.upper_vertexSet_subset_parts hvupper
  rcases Finset.mem_union.1 hlparts with hlpre_or_seg | husuf
  · rcases Finset.mem_union.1 hlpre_or_seg with hlpre | hseg₁
    · rcases Finset.mem_union.1 hupart with hupre_or_seg | hlsuf
      · rcases Finset.mem_union.1 hupre_or_seg with hupre | hseg₂
        · have hlrow : v ∈ X.lowerPath.vertexSet :=
            X.lowerPath.takeUntil_vertexSet_subset X.s₁_mem_lower hlpre
          have hurow : v ∈ X.upperPath.vertexSet :=
            X.upperPath.takeUntil_vertexSet_subset X.t₂_mem_upper hupre
          exact X.lower_upper_disjoint_at hlrow hurow
        · have hlrow : v ∈ X.lowerPath.vertexSet :=
            X.lowerPath.takeUntil_vertexSet_subset X.s₁_mem_lower hlpre
          rcases X.orientedSegment₂_clean_lower hseg₂ hlrow with ht | hs
          · exact X.t₂_not_mem_lower (by simpa [ht] using hlrow)
          · exact X.s₂_not_mem_lower_prefix (by simpa [hs] using hlpre)
      · exact Finset.disjoint_left.mp X.lower_prefix_disjoint_suffix
          hlpre hlsuf
    · rcases Finset.mem_union.1 hupart with hupre_or_seg | hlsuf
      · rcases Finset.mem_union.1 hupre_or_seg with hupre | hseg₂
        · have hurow : v ∈ X.upperPath.vertexSet :=
            X.upperPath.takeUntil_vertexSet_subset X.t₂_mem_upper hupre
          rcases X.orientedSegment₁_clean_upper hseg₁ hurow with hs | ht
          · exact X.s₁_not_mem_upper (by simpa [hs] using hurow)
          · exact X.t₁_not_mem_upper_prefix (by simpa [ht] using hupre)
        · exact Finset.disjoint_left.mp X.orientedSegments_nodeDisjoint
            hseg₁ hseg₂
      · have hlrow : v ∈ X.lowerPath.vertexSet :=
          X.lowerPath.dropUntil_vertexSet_subset X.s₂_mem_lower hlsuf
        rcases X.orientedSegment₁_clean_lower hseg₁ hlrow with hs | ht
        · exact X.s₁_not_mem_lower_suffix (by simpa [hs] using hlsuf)
        · exact X.t₁_not_mem_lower (by simpa [ht] using hlrow)
  · rcases Finset.mem_union.1 hupart with hupre_or_seg | hlsuf
    · rcases Finset.mem_union.1 hupre_or_seg with hupre | hseg₂
      · exact Finset.disjoint_left.mp X.upper_prefix_disjoint_suffix
          hupre husuf
      · have hurow : v ∈ X.upperPath.vertexSet :=
          X.upperPath.dropUntil_vertexSet_subset X.t₁_mem_upper husuf
        rcases X.orientedSegment₂_clean_upper hseg₂ hurow with ht | hs
        · exact X.t₂_not_mem_upper_suffix (by simpa [ht] using husuf)
        · exact X.s₂_not_mem_upper (by simpa [hs] using hurow)
    · have hurow : v ∈ X.upperPath.vertexSet :=
        X.upperPath.dropUntil_vertexSet_subset X.t₁_mem_upper husuf
      have hlrow : v ∈ X.lowerPath.vertexSet :=
        X.lowerPath.dropUntil_vertexSet_subset X.s₂_mem_lower hlsuf
      exact X.lower_upper_disjoint_at hlrow hurow

theorem lowerPath_nodeDisjoint_unchanged
    (X : CorridorCross S) {i : S.linkage.Index}
    (hi : i ≠ X.lowerIndex) :
    X.lowerPath.NodeDisjoint (S.linkage.path i) := by
  simpa using S.linkage.toPathPacking.node_disjoint
    (fun h => hi h.symm)

theorem upperPath_nodeDisjoint_unchanged
    (X : CorridorCross S) {i : S.linkage.Index}
    (hi : i ≠ X.upperIndex) :
    X.upperPath.NodeDisjoint (S.linkage.path i) := by
  simpa using S.linkage.toPathPacking.node_disjoint
    (fun h => hi h.symm)

theorem lowerReplacement_nodeDisjoint_unchanged
    (X : CorridorCross S) {i : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex) :
    X.replacementPaths.lowerReplacement.NodeDisjoint
      (S.linkage.path i) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvrep hvi
  have hparts := X.replacementPaths.lower_vertexSet_subset_parts hvrep
  rcases Finset.mem_union.1 hparts with hpre_or_seg | hsuf
  · rcases Finset.mem_union.1 hpre_or_seg with hpre | hseg
    · exact Finset.disjoint_left.mp
        (X.lowerPath_nodeDisjoint_unchanged hilower)
        (X.lowerPath.takeUntil_vertexSet_subset X.s₁_mem_lower hpre) hvi
    · exact Finset.disjoint_left.mp
        (X.orientedSegment₁_nodeDisjoint_unchanged hilower hiupper)
        hseg hvi
  · exact Finset.disjoint_left.mp
      (X.upperPath_nodeDisjoint_unchanged hiupper)
      (X.upperPath.dropUntil_vertexSet_subset X.t₁_mem_upper hsuf) hvi

theorem upperReplacement_nodeDisjoint_unchanged
    (X : CorridorCross S) {i : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex) :
    X.replacementPaths.upperReplacement.NodeDisjoint
      (S.linkage.path i) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvrep hvi
  have hparts := X.replacementPaths.upper_vertexSet_subset_parts hvrep
  rcases Finset.mem_union.1 hparts with hpre_or_seg | hsuf
  · rcases Finset.mem_union.1 hpre_or_seg with hpre | hseg
    · exact Finset.disjoint_left.mp
        (X.upperPath_nodeDisjoint_unchanged hiupper)
        (X.upperPath.takeUntil_vertexSet_subset X.t₂_mem_upper hpre) hvi
    · exact Finset.disjoint_left.mp
        (X.orientedSegment₂_nodeDisjoint_unchanged hilower hiupper)
        hseg hvi
  · exact Finset.disjoint_left.mp
      (X.lowerPath_nodeDisjoint_unchanged hilower)
      (X.lowerPath.dropUntil_vertexSet_subset X.s₂_mem_lower hsuf) hvi

/-- The new perfect linkage obtained by the cross switch. -/
noncomputable def replacementLinkage
    (X : CorridorCross S) : PerfectPathPacking G A B :=
  IndexedAuxiliaryPrefix.PerfectPathPacking.replaceTwoPathsSwapTargets
    S.linkage X.lowerIndex X.upperIndex X.lowerIndex_ne_upperIndex
    X.replacementPaths.lowerReplacement
    X.replacementPaths.upperReplacement
    (by simpa using X.replacementPaths.lower_source_eq)
    (by simpa using X.replacementPaths.lower_target_eq)
    (by simpa using X.replacementPaths.upper_source_eq)
    (by simpa using X.replacementPaths.upper_target_eq)
    X.replacementPaths_nodeDisjoint
    (fun _ hilower hiupper =>
      X.lowerReplacement_nodeDisjoint_unchanged hilower hiupper)
    (fun _ hilower hiupper =>
      X.upperReplacement_nodeDisjoint_unchanged hilower hiupper)

@[simp] theorem replacementLinkage_path_lower (X : CorridorCross S) :
    X.replacementLinkage.path X.lowerIndex =
      X.replacementPaths.lowerReplacement := by
  simp [replacementLinkage]

@[simp] theorem replacementLinkage_path_upper (X : CorridorCross S) :
    X.replacementLinkage.path X.upperIndex =
      X.replacementPaths.upperReplacement := by
  simp [replacementLinkage]

@[simp] theorem replacementLinkage_path_of_ne
    (X : CorridorCross S) {i : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex) :
    X.replacementLinkage.path i = S.linkage.path i := by
  simp [replacementLinkage, hilower, hiupper]

/-! ## Vertex support of the switch -/

noncomputable def deletedMiddleVertexSet (X : CorridorCross S) : Finset V :=
  X.deletedLowerInterval.vertexSet ∪ X.deletedUpperInterval.vertexSet

noncomputable def insertedSegmentVertexSet (X : CorridorCross S) : Finset V :=
  X.orientedSegment₁.vertexSet ∪ X.orientedSegment₂.vertexSet

theorem lower_vertex_mem_prefix_or_deleted_or_suffix
    (X : CorridorCross S) {v : V} (hv : v ∈ X.lowerPath.vertexSet) :
    v ∈ (X.lowerPath.takeUntil X.s₁_mem_lower).vertexSet ∨
      v ∈ X.deletedLowerInterval.vertexSet ∨
        v ∈ (X.lowerPath.dropUntil X.s₂_mem_lower).vertexSet := by
  classical
  by_cases hv_before : X.lowerPath.Before v X.s₁
  · exact Or.inl
      (X.lowerPath.mem_takeUntil_of_before X.s₁_mem_lower hv_before)
  · by_cases hafter : X.lowerPath.Before X.s₂ v
    · exact Or.inr <| Or.inr (by simpa using hafter.2)
    · have hs₁v : X.lowerPath.Before X.s₁ v := by
        rcases le_total (X.lowerPath.vertexIndex X.s₁)
            (X.lowerPath.vertexIndex v) with hle | hle
        · exact X.lowerPath.before_iff_vertexIndex_le.2
            ⟨X.s₁_mem_lower, hv, hle⟩
        · exact False.elim (hv_before
            (X.lowerPath.before_iff_vertexIndex_le.2
              ⟨hv, X.s₁_mem_lower, hle⟩))
      have hvs₂ : X.lowerPath.Before v X.s₂ := by
        rcases le_total (X.lowerPath.vertexIndex v)
            (X.lowerPath.vertexIndex X.s₂) with hle | hle
        · exact X.lowerPath.before_iff_vertexIndex_le.2
            ⟨hv, X.s₂_mem_lower, hle⟩
        · exact False.elim (hafter
            (X.lowerPath.before_iff_vertexIndex_le.2
              ⟨X.s₂_mem_lower, hv, hle⟩))
      exact Or.inr <| Or.inl <|
        X.lowerPath.mem_segmentOfBefore_of_before_of_before
          X.s₁_before_s₂ hs₁v hvs₂

theorem upper_vertex_mem_prefix_or_deleted_or_suffix
    (X : CorridorCross S) {v : V} (hv : v ∈ X.upperPath.vertexSet) :
    v ∈ (X.upperPath.takeUntil X.t₂_mem_upper).vertexSet ∨
      v ∈ X.deletedUpperInterval.vertexSet ∨
        v ∈ (X.upperPath.dropUntil X.t₁_mem_upper).vertexSet := by
  classical
  by_cases hv_before : X.upperPath.Before v X.t₂
  · exact Or.inl
      (X.upperPath.mem_takeUntil_of_before X.t₂_mem_upper hv_before)
  · by_cases hafter : X.upperPath.Before X.t₁ v
    · exact Or.inr <| Or.inr (by simpa using hafter.2)
    · have ht₂v : X.upperPath.Before X.t₂ v := by
        rcases le_total (X.upperPath.vertexIndex X.t₂)
            (X.upperPath.vertexIndex v) with hle | hle
        · exact X.upperPath.before_iff_vertexIndex_le.2
            ⟨X.t₂_mem_upper, hv, hle⟩
        · exact False.elim (hv_before
            (X.upperPath.before_iff_vertexIndex_le.2
              ⟨hv, X.t₂_mem_upper, hle⟩))
      have hvt₁ : X.upperPath.Before v X.t₁ := by
        rcases le_total (X.upperPath.vertexIndex v)
            (X.upperPath.vertexIndex X.t₁) with hle | hle
        · exact X.upperPath.before_iff_vertexIndex_le.2
            ⟨hv, X.t₁_mem_upper, hle⟩
        · exact False.elim (hafter
            (X.upperPath.before_iff_vertexIndex_le.2
              ⟨X.t₁_mem_upper, hv, hle⟩))
      exact Or.inr <| Or.inl <|
        X.upperPath.mem_segmentOfBefore_of_before_of_before
          X.t₂_before_t₁ ht₂v hvt₁

/-- Every old-only linkage vertex lies on a deleted middle interval. -/
theorem old_link_vertex_not_new_mem_deletedMiddle
    (X : CorridorCross S) {v : V}
    (hold : v ∈ S.linkage.toPathPacking.vertexSet)
    (hnew : v ∉ X.replacementLinkage.toPathPacking.vertexSet) :
    v ∈ X.deletedMiddleVertexSet := by
  classical
  rcases (S.linkage.toPathPacking.mem_vertexSet).1 hold with ⟨i, hvi⟩
  by_cases hilower : i = X.lowerIndex
  · subst i
    have hvrow : v ∈ X.lowerPath.vertexSet := by simpa using hvi
    rcases X.lower_vertex_mem_prefix_or_deleted_or_suffix hvrow with
      hpre | hdel | hsuf
    · exact False.elim <| hnew <|
        (X.replacementLinkage.toPathPacking.mem_vertexSet).2
          ⟨X.lowerIndex, by
            simpa using X.replacementPaths.lower_prefix_subset hpre⟩
    · exact Finset.mem_union.2 (Or.inl hdel)
    · exact False.elim <| hnew <|
        (X.replacementLinkage.toPathPacking.mem_vertexSet).2
          ⟨X.upperIndex, by
            simpa using X.replacementPaths.lower_suffix_subset hsuf⟩
  · by_cases hiupper : i = X.upperIndex
    · subst i
      have hvrow : v ∈ X.upperPath.vertexSet := by simpa using hvi
      rcases X.upper_vertex_mem_prefix_or_deleted_or_suffix hvrow with
        hpre | hdel | hsuf
      · exact False.elim <| hnew <|
          (X.replacementLinkage.toPathPacking.mem_vertexSet).2
            ⟨X.upperIndex, by
              simpa using X.replacementPaths.upper_prefix_subset hpre⟩
      · exact Finset.mem_union.2 (Or.inr hdel)
      · exact False.elim <| hnew <|
          (X.replacementLinkage.toPathPacking.mem_vertexSet).2
            ⟨X.lowerIndex, by
              simpa using X.replacementPaths.upper_suffix_subset hsuf⟩
    · exact False.elim <| hnew <|
        (X.replacementLinkage.toPathPacking.mem_vertexSet).2
          ⟨i, by simpa [X.replacementLinkage_path_of_ne hilower hiupper]
            using hvi⟩

/-- Every new-only linkage vertex lies on an inserted bridge. -/
theorem new_link_vertex_not_old_mem_insertedSegment
    (X : CorridorCross S) {v : V}
    (hnew : v ∈ X.replacementLinkage.toPathPacking.vertexSet)
    (hold : v ∉ S.linkage.toPathPacking.vertexSet) :
    v ∈ X.insertedSegmentVertexSet := by
  classical
  rcases (X.replacementLinkage.toPathPacking.mem_vertexSet).1 hnew with
    ⟨i, hvi⟩
  by_cases hilower : i = X.lowerIndex
  · subst i
    have hvrep : v ∈ X.replacementPaths.lowerReplacement.vertexSet := by
      simpa using hvi
    have hparts := X.replacementPaths.lower_vertexSet_subset_parts hvrep
    rcases Finset.mem_union.1 hparts with hpre_or_seg | hsuf
    · rcases Finset.mem_union.1 hpre_or_seg with hpre | hseg
      · exact False.elim <| hold <|
          (S.linkage.toPathPacking.mem_vertexSet).2
            ⟨X.lowerIndex, by
              simpa using
                X.lowerPath.takeUntil_vertexSet_subset X.s₁_mem_lower hpre⟩
      · exact Finset.mem_union.2 (Or.inl hseg)
    · exact False.elim <| hold <|
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨X.upperIndex, by
            simpa using
              X.upperPath.dropUntil_vertexSet_subset X.t₁_mem_upper hsuf⟩
  · by_cases hiupper : i = X.upperIndex
    · subst i
      have hvrep : v ∈ X.replacementPaths.upperReplacement.vertexSet := by
        simpa using hvi
      have hparts := X.replacementPaths.upper_vertexSet_subset_parts hvrep
      rcases Finset.mem_union.1 hparts with hpre_or_seg | hsuf
      · rcases Finset.mem_union.1 hpre_or_seg with hpre | hseg
        · exact False.elim <| hold <|
            (S.linkage.toPathPacking.mem_vertexSet).2
              ⟨X.upperIndex, by
                simpa using
                  X.upperPath.takeUntil_vertexSet_subset X.t₂_mem_upper hpre⟩
        · exact Finset.mem_union.2 (Or.inr hseg)
      · exact False.elim <| hold <|
          (S.linkage.toPathPacking.mem_vertexSet).2
            ⟨X.lowerIndex, by
              simpa using
                X.lowerPath.dropUntil_vertexSet_subset X.s₂_mem_lower hsuf⟩
    · exact False.elim <| hold <|
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨i, by
            simpa [X.replacementLinkage_path_of_ne hilower hiupper]
              using hvi⟩

theorem internallyDisjoint_old_of_new_clean_disjoint_deleted
    (X : CorridorCross S) (P : GraphPath G)
    (hclean :
      P.InternallyDisjointFromSet
        X.replacementLinkage.toPathPacking.vertexSet)
    (hmiss : Disjoint P.vertexSet X.deletedMiddleVertexSet) :
    P.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet := by
  intro v hvP hvold
  by_cases hvnew : v ∈ X.replacementLinkage.toPathPacking.vertexSet
  · exact hclean hvP hvnew
  · exact False.elim <| Finset.disjoint_left.mp hmiss hvP <|
      X.old_link_vertex_not_new_mem_deletedMiddle hvold hvnew

theorem internallyDisjoint_new_of_old_clean_disjoint_inserted
    (X : CorridorCross S) (P : GraphPath G)
    (hclean :
      P.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet)
    (hmiss : Disjoint P.vertexSet X.insertedSegmentVertexSet) :
    P.InternallyDisjointFromSet
      X.replacementLinkage.toPathPacking.vertexSet := by
  intro v hvP hvnew
  by_cases hvold : v ∈ S.linkage.toPathPacking.vertexSet
  · exact hclean hvP hvold
  · exact False.elim <| Finset.disjoint_left.mp hmiss hvP <|
      X.new_link_vertex_not_old_mem_insertedSegment hvnew hvold

/-- Reverse a bridge between two packing paths. -/
noncomputable def reverseBridge
    (X : CorridorCross S)
    {P : PathPacking G A B} {i j : P.Index}
    (β : P.BridgeBetween i j) : P.BridgeBetween j i where
  path := β.path.reverse
  connects := by
    rcases β.connects with h | h
    · exact Or.inl ⟨by simpa using h.2, by simpa using h.1⟩
    · exact Or.inr ⟨by simpa using h.2, by simpa using h.1⟩
  internallyDisjoint :=
    (β.path.reverse_internallyDisjointFromSet P.vertexSet).2
      β.internallyDisjoint

theorem old_aux_adj_of_new_bridge_unchanged_miss_deleted
    (X : CorridorCross S) {i j : S.linkage.Index} (hij : i ≠ j)
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (hjlower : j ≠ X.lowerIndex) (hjupper : j ≠ X.upperIndex)
    (β : X.replacementLinkage.toPathPacking.BridgeBetween i j)
    (hmiss : Disjoint β.orientedPath.vertexSet X.deletedMiddleVertexSet) :
    (linkageAuxGraph S.linkage).Adj i j := by
  refine ⟨hij, Or.inl ?_⟩
  refine ⟨PathPacking.BridgeBetween.of_orientedPath
    S.linkage.toPathPacking β.orientedPath ?_ ?_ ?_⟩
  · simpa [X.replacementLinkage_path_of_ne hilower hiupper] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
  · simpa [X.replacementLinkage_path_of_ne hjlower hjupper] using
      PathPacking.BridgeBetween.orientedPath_target_mem_right β
  · exact X.internallyDisjoint_old_of_new_clean_disjoint_deleted
      β.orientedPath β.orientedPath_internallyDisjoint hmiss

theorem new_aux_adj_of_old_bridge_unchanged_miss_inserted
    (X : CorridorCross S) {i j : S.linkage.Index} (hij : i ≠ j)
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (hjlower : j ≠ X.lowerIndex) (hjupper : j ≠ X.upperIndex)
    (β : S.linkage.toPathPacking.BridgeBetween i j)
    (hmiss : Disjoint β.orientedPath.vertexSet X.insertedSegmentVertexSet) :
    (linkageAuxGraph X.replacementLinkage).Adj i j := by
  refine ⟨hij, Or.inl ?_⟩
  refine ⟨PathPacking.BridgeBetween.of_orientedPath
    X.replacementLinkage.toPathPacking β.orientedPath ?_ ?_ ?_⟩
  · simpa [X.replacementLinkage_path_of_ne hilower hiupper] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
  · simpa [X.replacementLinkage_path_of_ne hjlower hjupper] using
      PathPacking.BridgeBetween.orientedPath_target_mem_right β
  · exact X.internallyDisjoint_new_of_old_clean_disjoint_inserted
      β.orientedPath β.orientedPath_internallyDisjoint hmiss

theorem cleanPrefixToDeleted_internallyDisjoint_old_of_new_clean
    (X : CorridorCross S) (P : GraphPath G)
    (hclean :
      P.InternallyDisjointFromSet
        X.replacementLinkage.toPathPacking.vertexSet)
    (hne : (P.vertexSet ∩ X.deletedMiddleVertexSet).Nonempty) :
    (P.cleanPrefixToSet X.deletedMiddleVertexSet hne).InternallyDisjointFromSet
      S.linkage.toPathPacking.vertexSet := by
  intro v hvPrefix hvold
  have hcleanNew :
      (P.cleanPrefixToSet X.deletedMiddleVertexSet hne).InternallyDisjointFromSet
        X.replacementLinkage.toPathPacking.vertexSet := by
    simpa [GraphPath.cleanPrefixToSet] using
      P.takeUntil_internallyDisjointFromSet
        (P.firstHitVertex_mem_vertexSet X.deletedMiddleVertexSet hne)
        hclean
  by_cases hvnew : v ∈ X.replacementLinkage.toPathPacking.vertexSet
  · exact hcleanNew hvPrefix hvnew
  · have hvdel := X.old_link_vertex_not_new_mem_deletedMiddle hvold hvnew
    have hv_eq : v = P.firstHitVertex X.deletedMiddleVertexSet hne :=
      P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set
        X.deletedMiddleVertexSet hne
        (by simpa [GraphPath.cleanPrefixToSet] using hvPrefix) hvdel
    exact Or.inr (by simp [GraphPath.cleanPrefixToSet, hv_eq])

theorem old_aux_adj_to_crossed_row_of_new_bridge_hits_deleted
    (X : CorridorCross S) {i j : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (β : X.replacementLinkage.toPathPacking.BridgeBetween i j)
    (hne :
      (β.orientedPath.vertexSet ∩ X.deletedMiddleVertexSet).Nonempty) :
    (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
      (linkageAuxGraph S.linkage).Adj i X.upperIndex := by
  classical
  let P := β.orientedPath
  let Prefix := P.cleanPrefixToSet X.deletedMiddleVertexSet hne
  have hsrcOld : Prefix.source ∈ (S.linkage.path i).vertexSet := by
    simpa [Prefix, P,
      X.replacementLinkage_path_of_ne hilower hiupper] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
  have hcleanOld :
      Prefix.InternallyDisjointFromSet
        S.linkage.toPathPacking.vertexSet := by
    simpa [Prefix, P] using
      X.cleanPrefixToDeleted_internallyDisjoint_old_of_new_clean
        P β.orientedPath_internallyDisjoint hne
  have htgt :
      Prefix.target ∈ X.deletedMiddleVertexSet := by
    simpa [Prefix, P] using
      P.cleanPrefixToSet_target_mem X.deletedMiddleVertexSet hne
  rcases Finset.mem_union.1 htgt with hlower | hupper
  · have htgtOld :
        Prefix.target ∈ (S.linkage.path X.lowerIndex).vertexSet := by
      simpa using X.lowerPath.segmentOfBefore_vertexSet_subset
        X.s₁_before_s₂ hlower
    exact Or.inl ⟨hilower, Or.inl
      ⟨PathPacking.BridgeBetween.of_orientedPath
        S.linkage.toPathPacking Prefix hsrcOld htgtOld hcleanOld⟩⟩
  · have htgtOld :
        Prefix.target ∈ (S.linkage.path X.upperIndex).vertexSet := by
      simpa using X.upperPath.segmentOfBefore_vertexSet_subset
        X.t₂_before_t₁ hupper
    exact Or.inr ⟨hiupper, Or.inl
      ⟨PathPacking.BridgeBetween.of_orientedPath
        S.linkage.toPathPacking Prefix hsrcOld htgtOld hcleanOld⟩⟩

/-- In the old degree-two corridor, any vertex adjacent to either crossed row
is one of the four local corridor vertices. -/
theorem mem_local_quad_of_old_adj_to_crossed_row
    (X : CorridorCross S) {i auxA auxD : S.linkage.Index}
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD)
    (hadj :
      (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
        (linkageAuxGraph S.linkage).Adj i X.upperIndex) :
    i ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
      Finset S.linkage.Index) := by
  classical
  rcases hadj with hlower | hupper
  · rcases DegreeEquals.two_adj_eq_or_eq hU
      ((linkageAuxGraph S.linkage).symm hAU) hUV hA_ne_V
      ((linkageAuxGraph S.linkage).symm hlower) with h | h
    · simpa [h]
    · simpa [h]
  · rcases DegreeEquals.two_adj_eq_or_eq hV
      ((linkageAuxGraph S.linkage).symm hUV) hVD hU_ne_D
      ((linkageAuxGraph S.linkage).symm hupper) with h | h
    · simpa [h]
    · simpa [h]

theorem old_aux_adj_to_crossed_row_of_old_bridge_first_inserted_in_segment₁
    (X : CorridorCross S) {i j : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (β : S.linkage.toPathPacking.BridgeBetween i j)
    (hne :
      (β.orientedPath.vertexSet ∩ X.insertedSegmentVertexSet).Nonempty)
    (hxseg :
      (β.orientedPath.cleanPrefixToSet
        X.insertedSegmentVertexSet hne).target ∈
          X.orientedSegment₁.vertexSet) :
    (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
      (linkageAuxGraph S.linkage).Adj i X.upperIndex := by
  classical
  let P := β.orientedPath
  let Prefix := P.cleanPrefixToSet X.insertedSegmentVertexSet hne
  have hsrc : Prefix.source ∈ (S.linkage.path i).vertexSet := by
    simpa [Prefix, P] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
  have hprefixClean :
      Prefix.InternallyDisjointFromSet
        S.linkage.toPathPacking.vertexSet := by
    simpa [Prefix, P, GraphPath.cleanPrefixToSet] using
      P.takeUntil_internallyDisjointFromSet
        (P.firstHitVertex_mem_vertexSet X.insertedSegmentVertexSet hne)
        β.orientedPath_internallyDisjoint
  by_cases hxold : Prefix.target ∈ S.linkage.toPathPacking.vertexSet
  · rcases X.orientedSegment₁_clean_linkage hxseg hxold with hs | ht
    · have htgt :
          Prefix.target ∈ (S.linkage.path X.lowerIndex).vertexSet := by
        have hrow : Prefix.target ∈ X.lowerPath.vertexSet := by
          rw [hs, X.orientedSegment₁_source]
          exact X.s₁_mem_lower
        simpa using hrow
      exact Or.inl ⟨hilower, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking Prefix hsrc htgt hprefixClean⟩⟩
    · have htgt :
          Prefix.target ∈ (S.linkage.path X.upperIndex).vertexSet := by
        have hrow : Prefix.target ∈ X.upperPath.vertexSet := by
          rw [ht, X.orientedSegment₁_target]
          exact X.t₁_mem_upper
        simpa using hrow
      exact Or.inr ⟨hiupper, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking Prefix hsrc htgt hprefixClean⟩⟩
  · let Tail := X.orientedSegment₁.dropUntil hxseg
    have hglue : Prefix.target = Tail.source := by
      simp [Tail, Prefix, P]
    have hinter :
        ∀ ⦃v : V⦄, v ∈ Prefix.vertexSet → v ∈ Tail.vertexSet →
          v = Prefix.target := by
      intro v hvpre hvtail
      have hvseg : v ∈ X.orientedSegment₁.vertexSet :=
        X.orientedSegment₁.dropUntil_vertexSet_subset hxseg
          (by simpa [Tail] using hvtail)
      have hvins : v ∈ X.insertedSegmentVertexSet :=
        Finset.mem_union.2 (Or.inl hvseg)
      have hv_eq : v = P.firstHitVertex X.insertedSegmentVertexSet hne :=
        P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set
          X.insertedSegmentVertexSet hne
          (by simpa [Prefix, GraphPath.cleanPrefixToSet] using hvpre) hvins
      simpa [Prefix, P, GraphPath.cleanPrefixToSet] using hv_eq
    let Joined :=
      Prefix.appendWithEqOfInterSubsetTarget Tail hglue hinter
    have htailClean :
        Tail.InternallyDisjointFromSet
          S.linkage.toPathPacking.vertexSet := by
      simpa [Tail] using
        X.orientedSegment₁.dropUntil_internallyDisjointFromSet
          hxseg X.orientedSegment₁_clean_linkage
    have hjoinedClean :
        Joined.InternallyDisjointFromSet
          S.linkage.toPathPacking.vertexSet := by
      simpa [Joined] using
        Prefix.appendWithEqOfInterSubsetTarget_internallyDisjointFromSet
          Tail hglue hinter hprefixClean htailClean hxold
    have hjoinedSrc : Joined.source ∈ (S.linkage.path i).vertexSet := by
      simpa [Joined] using hsrc
    have hjoinedTgt :
        Joined.target ∈ (S.linkage.path X.upperIndex).vertexSet := by
      have htgt : Joined.target = X.t₁ := by simp [Joined, Tail]
      simpa [htgt] using X.t₁_mem_upper
    exact Or.inr ⟨hiupper, Or.inl
      ⟨PathPacking.BridgeBetween.of_orientedPath
        S.linkage.toPathPacking Joined hjoinedSrc hjoinedTgt
          hjoinedClean⟩⟩

theorem old_aux_adj_to_crossed_row_of_old_bridge_first_inserted_in_segment₂
    (X : CorridorCross S) {i j : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (β : S.linkage.toPathPacking.BridgeBetween i j)
    (hne :
      (β.orientedPath.vertexSet ∩ X.insertedSegmentVertexSet).Nonempty)
    (hxseg :
      (β.orientedPath.cleanPrefixToSet
        X.insertedSegmentVertexSet hne).target ∈
          X.orientedSegment₂.vertexSet) :
    (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
      (linkageAuxGraph S.linkage).Adj i X.upperIndex := by
  classical
  let P := β.orientedPath
  let Prefix := P.cleanPrefixToSet X.insertedSegmentVertexSet hne
  have hsrc : Prefix.source ∈ (S.linkage.path i).vertexSet := by
    simpa [Prefix, P] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left β
  have hprefixClean :
      Prefix.InternallyDisjointFromSet
        S.linkage.toPathPacking.vertexSet := by
    simpa [Prefix, P, GraphPath.cleanPrefixToSet] using
      P.takeUntil_internallyDisjointFromSet
        (P.firstHitVertex_mem_vertexSet X.insertedSegmentVertexSet hne)
        β.orientedPath_internallyDisjoint
  by_cases hxold : Prefix.target ∈ S.linkage.toPathPacking.vertexSet
  · rcases X.orientedSegment₂_clean_linkage hxseg hxold with ht | hs
    · have htgt :
          Prefix.target ∈ (S.linkage.path X.upperIndex).vertexSet := by
        have hrow : Prefix.target ∈ X.upperPath.vertexSet := by
          rw [ht, X.orientedSegment₂_source]
          exact X.t₂_mem_upper
        simpa using hrow
      exact Or.inr ⟨hiupper, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking Prefix hsrc htgt hprefixClean⟩⟩
    · have htgt :
          Prefix.target ∈ (S.linkage.path X.lowerIndex).vertexSet := by
        have hrow : Prefix.target ∈ X.lowerPath.vertexSet := by
          rw [hs, X.orientedSegment₂_target]
          exact X.s₂_mem_lower
        simpa using hrow
      exact Or.inl ⟨hilower, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking Prefix hsrc htgt hprefixClean⟩⟩
  · let Tail := X.orientedSegment₂.dropUntil hxseg
    have hglue : Prefix.target = Tail.source := by
      simp [Tail, Prefix, P]
    have hinter :
        ∀ ⦃v : V⦄, v ∈ Prefix.vertexSet → v ∈ Tail.vertexSet →
          v = Prefix.target := by
      intro v hvpre hvtail
      have hvseg : v ∈ X.orientedSegment₂.vertexSet :=
        X.orientedSegment₂.dropUntil_vertexSet_subset hxseg
          (by simpa [Tail] using hvtail)
      have hvins : v ∈ X.insertedSegmentVertexSet :=
        Finset.mem_union.2 (Or.inr hvseg)
      have hv_eq : v = P.firstHitVertex X.insertedSegmentVertexSet hne :=
        P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set
          X.insertedSegmentVertexSet hne
          (by simpa [Prefix, GraphPath.cleanPrefixToSet] using hvpre) hvins
      simpa [Prefix, P, GraphPath.cleanPrefixToSet] using hv_eq
    let Joined :=
      Prefix.appendWithEqOfInterSubsetTarget Tail hglue hinter
    have htailClean :
        Tail.InternallyDisjointFromSet
          S.linkage.toPathPacking.vertexSet := by
      simpa [Tail] using
        X.orientedSegment₂.dropUntil_internallyDisjointFromSet
          hxseg X.orientedSegment₂_clean_linkage
    have hjoinedClean :
        Joined.InternallyDisjointFromSet
          S.linkage.toPathPacking.vertexSet := by
      simpa [Joined] using
        Prefix.appendWithEqOfInterSubsetTarget_internallyDisjointFromSet
          Tail hglue hinter hprefixClean htailClean hxold
    have hjoinedSrc : Joined.source ∈ (S.linkage.path i).vertexSet := by
      simpa [Joined] using hsrc
    have hjoinedTgt :
        Joined.target ∈ (S.linkage.path X.lowerIndex).vertexSet := by
      have htgt : Joined.target = X.s₂ := by simp [Joined, Tail]
      simpa [htgt] using X.s₂_mem_lower
    exact Or.inl ⟨hilower, Or.inl
      ⟨PathPacking.BridgeBetween.of_orientedPath
        S.linkage.toPathPacking Joined hjoinedSrc hjoinedTgt
          hjoinedClean⟩⟩

theorem old_aux_adj_to_crossed_row_of_old_bridge_hits_inserted
    (X : CorridorCross S) {i j : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (β : S.linkage.toPathPacking.BridgeBetween i j)
    (hne :
      (β.orientedPath.vertexSet ∩ X.insertedSegmentVertexSet).Nonempty) :
    (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
      (linkageAuxGraph S.linkage).Adj i X.upperIndex := by
  have hx :
      (β.orientedPath.cleanPrefixToSet
        X.insertedSegmentVertexSet hne).target ∈
          X.insertedSegmentVertexSet :=
    β.orientedPath.cleanPrefixToSet_target_mem
      X.insertedSegmentVertexSet hne
  rcases Finset.mem_union.1 hx with hx₁ | hx₂
  · exact
      X.old_aux_adj_to_crossed_row_of_old_bridge_first_inserted_in_segment₁
        hilower hiupper β hne hx₁
  · exact
      X.old_aux_adj_to_crossed_row_of_old_bridge_first_inserted_in_segment₂
        hilower hiupper β hne hx₂

theorem mem_local_quad_of_old_bridge_not_new_unchanged
    (X : CorridorCross S) {i j auxA auxD : S.linkage.Index}
    (hij : i ≠ j)
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (hjlower : j ≠ X.lowerIndex) (hjupper : j ≠ X.upperIndex)
    (β : S.linkage.toPathPacking.BridgeBetween i j)
    (hnotnew : ¬ (linkageAuxGraph X.replacementLinkage).Adj i j)
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    i ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
      Finset S.linkage.Index) := by
  classical
  by_cases hhit :
      (β.orientedPath.vertexSet ∩ X.insertedSegmentVertexSet).Nonempty
  · exact X.mem_local_quad_of_old_adj_to_crossed_row
      hAU hUV hVD hU hV hA_ne_V hU_ne_D
      (X.old_aux_adj_to_crossed_row_of_old_bridge_hits_inserted
        hilower hiupper β hhit)
  · have hmiss :
        Disjoint β.orientedPath.vertexSet X.insertedSegmentVertexSet := by
      rw [Finset.disjoint_left]
      intro v hvP hvIns
      exact hhit ⟨v, Finset.mem_inter.2 ⟨hvP, hvIns⟩⟩
    exact False.elim <| hnotnew <|
      X.new_aux_adj_of_old_bridge_unchanged_miss_inserted
        hij hilower hiupper hjlower hjupper β hmiss

/-- Endpoint-localizing form for an old auxiliary edge that disappears after
the cross. -/
theorem mem_local_quad_of_old_adj_not_new_at_left_endpoint
    (X : CorridorCross S) {i j auxA auxD : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex)
    (hiupper : i ≠ X.upperIndex)
    (hadj : (linkageAuxGraph S.linkage).Adj i j)
    (hnotnew :
      ¬ (linkageAuxGraph X.replacementLinkage).Adj i j)
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    i ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
      Finset S.linkage.Index) := by
  classical
  by_cases hjlower : j = X.lowerIndex
  · exact X.mem_local_quad_of_old_adj_to_crossed_row
      hAU hUV hVD hU hV hA_ne_V hU_ne_D
      (Or.inl (by simpa [hjlower] using hadj))
  · by_cases hjupper : j = X.upperIndex
    · exact X.mem_local_quad_of_old_adj_to_crossed_row
        hAU hUV hVD hU hV hA_ne_V hU_ne_D
        (Or.inr (by simpa [hjupper] using hadj))
    · rcases hadj with ⟨hij, hbridge⟩
      rcases hbridge with hβ | hβ
      · rcases hβ with ⟨β⟩
        exact X.mem_local_quad_of_old_bridge_not_new_unchanged
          hij hilower hiupper hjlower hjupper β hnotnew
          hAU hUV hVD hU hV hA_ne_V hU_ne_D
      · rcases hβ with ⟨β⟩
        exact X.mem_local_quad_of_old_bridge_not_new_unchanged
          hij hilower hiupper hjlower hjupper
          (X.reverseBridge β) hnotnew
          hAU hUV hVD hU hV hA_ne_V hU_ne_D

/-- Symmetric endpoint-localizing form for an old auxiliary edge that
disappears after the cross. -/
theorem mem_local_quad_of_old_adj_not_new_at_right_endpoint
    (X : CorridorCross S) {i j auxA auxD : S.linkage.Index}
    (hjlower : j ≠ X.lowerIndex)
    (hjupper : j ≠ X.upperIndex)
    (hadj : (linkageAuxGraph S.linkage).Adj i j)
    (hnotnew :
      ¬ (linkageAuxGraph X.replacementLinkage).Adj i j)
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    j ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
      Finset S.linkage.Index) := by
  exact X.mem_local_quad_of_old_adj_not_new_at_left_endpoint
    hjlower hjupper ((linkageAuxGraph S.linkage).symm hadj)
    (fun hnew => hnotnew ((linkageAuxGraph X.replacementLinkage).symm hnew))
    hAU hUV hVD hU hV hA_ne_V hU_ne_D

/-- A genuinely new bridge between unchanged paths has a local endpoint. -/
theorem mem_local_quad_of_new_bridge_not_old_unchanged
    (X : CorridorCross S) {i j auxA auxD : S.linkage.Index}
    (hij : i ≠ j)
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (hjlower : j ≠ X.lowerIndex) (hjupper : j ≠ X.upperIndex)
    (β : X.replacementLinkage.toPathPacking.BridgeBetween i j)
    (hnotold : ¬ (linkageAuxGraph S.linkage).Adj i j)
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    i ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
      Finset S.linkage.Index) := by
  classical
  by_cases hhit :
      (β.orientedPath.vertexSet ∩ X.deletedMiddleVertexSet).Nonempty
  · exact X.mem_local_quad_of_old_adj_to_crossed_row
      hAU hUV hVD hU hV hA_ne_V hU_ne_D
      (X.old_aux_adj_to_crossed_row_of_new_bridge_hits_deleted
        hilower hiupper β hhit)
  · have hmiss :
        Disjoint β.orientedPath.vertexSet X.deletedMiddleVertexSet := by
      rw [Finset.disjoint_left]
      intro v hvP hvDel
      exact hhit ⟨v, Finset.mem_inter.2 ⟨hvP, hvDel⟩⟩
    have hold : (linkageAuxGraph S.linkage).Adj i j :=
      X.old_aux_adj_of_new_bridge_unchanged_miss_deleted
        hij hilower hiupper hjlower hjupper β hmiss
    exact False.elim (hnotold hold)

/-- Symmetric endpoint version of
`mem_local_quad_of_new_bridge_not_old_unchanged`. -/
theorem mem_local_quad_of_new_bridge_not_old_unchanged_right_endpoint
    (X : CorridorCross S) {i j auxA auxD : S.linkage.Index}
    (hij : i ≠ j)
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (hjlower : j ≠ X.lowerIndex) (hjupper : j ≠ X.upperIndex)
    (β : X.replacementLinkage.toPathPacking.BridgeBetween i j)
    (hnotold : ¬ (linkageAuxGraph S.linkage).Adj i j)
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    j ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
      Finset S.linkage.Index) := by
  exact X.mem_local_quad_of_new_bridge_not_old_unchanged
    hij.symm hjlower hjupper hilower hiupper (X.reverseBridge β)
    (fun hold => hnotold ((linkageAuxGraph S.linkage).symm hold))
    hAU hUV hVD hU hV hA_ne_V hU_ne_D

/-- Auxiliary adjacencies between two vertices outside the cross-local
quadruple are unchanged. -/
theorem aux_adj_iff_of_both_not_mem_cross_local_quad
    (X : CorridorCross S) {u v auxA auxD : S.linkage.Index}
    (hu_not :
      u ∉ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
        Finset S.linkage.Index))
    (hv_not :
      v ∉ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
        Finset S.linkage.Index))
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    (linkageAuxGraph X.replacementLinkage).Adj u v ↔
      (linkageAuxGraph S.linkage).Adj u v := by
  classical
  have hulower : u ≠ X.lowerIndex := by
    intro h
    exact hu_not (by simp [h])
  have huupper : u ≠ X.upperIndex := by
    intro h
    exact hu_not (by simp [h])
  have hvlower : v ≠ X.lowerIndex := by
    intro h
    exact hv_not (by simp [h])
  have hvupper : v ≠ X.upperIndex := by
    intro h
    exact hv_not (by simp [h])
  constructor
  · intro hnew
    by_contra hnotold
    rcases hnew with ⟨hij, hbridge⟩
    have hulocal :
        u ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
          Finset S.linkage.Index) := by
      rcases hbridge with hβ | hβ
      · rcases hβ with ⟨β⟩
        exact X.mem_local_quad_of_new_bridge_not_old_unchanged
          hij hulower huupper hvlower hvupper β hnotold
          hAU hUV hVD hU hV hA_ne_V hU_ne_D
      · rcases hβ with ⟨β⟩
        exact X.mem_local_quad_of_new_bridge_not_old_unchanged
          hij hulower huupper hvlower hvupper (X.reverseBridge β) hnotold
          hAU hUV hVD hU hV hA_ne_V hU_ne_D
    exact hu_not hulocal
  · intro hold
    by_contra hnotnew
    exact hu_not <| X.mem_local_quad_of_old_adj_not_new_at_left_endpoint
      hulower huupper hold hnotnew
      hAU hUV hVD hU hV hA_ne_V hU_ne_D

/-- A successor bridge from an unchanged path to the lower replacement path
gives an old auxiliary edge to one of the two crossed rows. -/
theorem old_aux_adj_to_crossed_row_of_new_bridge_to_lower_replacement
    (X : CorridorCross S) {i : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (β :
      X.replacementLinkage.toPathPacking.BridgeBetween
        i X.lowerIndex) :
    (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
      (linkageAuxGraph S.linkage).Adj i X.upperIndex := by
  classical
  by_cases hhit :
      (β.orientedPath.vertexSet ∩ X.deletedMiddleVertexSet).Nonempty
  · exact X.old_aux_adj_to_crossed_row_of_new_bridge_hits_deleted
      hilower hiupper β hhit
  · have hmiss :
        Disjoint β.orientedPath.vertexSet X.deletedMiddleVertexSet := by
      rw [Finset.disjoint_left]
      intro v hvP hvDel
      exact hhit ⟨v, Finset.mem_inter.2 ⟨hvP, hvDel⟩⟩
    let P : GraphPath G := β.orientedPath
    have hsrc_old : P.source ∈ (S.linkage.path i).vertexSet := by
      have hsrc_new :=
        PathPacking.BridgeBetween.orientedPath_source_mem_left β
      simpa [P, X.replacementLinkage_path_of_ne hilower hiupper]
        using hsrc_new
    have hclean_old :
        P.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet :=
      X.internallyDisjoint_old_of_new_clean_disjoint_deleted
        P β.orientedPath_internallyDisjoint hmiss
    have htgt_lower :
        P.target ∈ X.replacementPaths.lowerReplacement.vertexSet := by
      have htgt_new :=
        PathPacking.BridgeBetween.orientedPath_target_mem_right β
      simpa [P, X.replacementLinkage_path_lower] using htgt_new
    have hparts :=
      X.replacementPaths.lower_vertexSet_subset_parts htgt_lower
    rcases Finset.mem_union.1 hparts with hpre_or_seg | hupperSuf
    · rcases Finset.mem_union.1 hpre_or_seg with hlowerPre | hseg
      · have htgt_old :
            P.target ∈ (S.linkage.path X.lowerIndex).vertexSet := by
          have hrow : P.target ∈ X.lowerPath.vertexSet :=
            X.lowerPath.takeUntil_vertexSet_subset
              X.s₁_mem_lower hlowerPre
          simpa using hrow
        exact Or.inl ⟨hilower, Or.inl
          ⟨PathPacking.BridgeBetween.of_orientedPath
            S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
      · have hxseg : P.target ∈ X.orientedSegment₁.vertexSet := hseg
        by_cases hxold :
            P.target ∈ S.linkage.toPathPacking.vertexSet
        · rcases X.orientedSegment₁_clean_linkage hxseg hxold with hs | ht
          · have htgt_old :
                P.target ∈ (S.linkage.path X.lowerIndex).vertexSet := by
              have hrow : P.target ∈ X.lowerPath.vertexSet := by
                rw [hs, X.orientedSegment₁_source]
                exact X.s₁_mem_lower
              simpa using hrow
            exact Or.inl ⟨hilower, Or.inl
              ⟨PathPacking.BridgeBetween.of_orientedPath
                S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
          · have htgt_old :
                P.target ∈ (S.linkage.path X.upperIndex).vertexSet := by
              have hrow : P.target ∈ X.upperPath.vertexSet := by
                rw [ht, X.orientedSegment₁_target]
                exact X.t₁_mem_upper
              simpa using hrow
            exact Or.inr ⟨hiupper, Or.inl
              ⟨PathPacking.BridgeBetween.of_orientedPath
                S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
        · let Tail : GraphPath G := X.orientedSegment₁.dropUntil hxseg
          have hglue : P.target = Tail.source := by
            simp [Tail, P]
          have hinter :
              ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Tail.vertexSet →
                v = P.target := by
            intro v hvP hvtail
            have hvtail_seg : v ∈ X.orientedSegment₁.vertexSet :=
              X.orientedSegment₁.dropUntil_vertexSet_subset hxseg
                (by simpa [Tail] using hvtail)
            have hvlower :
                v ∈ X.replacementPaths.lowerReplacement.vertexSet :=
              X.replacementPaths.segment₁_subset hvtail_seg
            have hvnew :
                v ∈ X.replacementLinkage.toPathPacking.vertexSet :=
              (X.replacementLinkage.toPathPacking.mem_vertexSet).2
                ⟨X.lowerIndex, by
                  simpa [X.replacementLinkage_path_lower] using hvlower⟩
            rcases β.orientedPath_internallyDisjoint
                (by simpa [P] using hvP) hvnew with hsrc | htgt
            · have hsrc_new :
                  P.source ∈
                    (X.replacementLinkage.path i).vertexSet :=
                PathPacking.BridgeBetween.orientedPath_source_mem_left β
              have hsrc_i :
                  P.source ∈ (S.linkage.path i).vertexSet := by
                simpa [P, X.replacementLinkage_path_of_ne
                  hilower hiupper] using hsrc_new
              have hsrc_lower :
                  P.source ∈
                    X.replacementPaths.lowerReplacement.vertexSet := by
                simpa [P, hsrc] using hvlower
              exact False.elim <|
                Finset.disjoint_left.mp
                  (X.lowerReplacement_nodeDisjoint_unchanged
                    hilower hiupper) hsrc_lower hsrc_i
            · simpa [P] using htgt
          let Joined : GraphPath G :=
            P.appendWithEqOfInterSubsetTarget Tail hglue hinter
          have htail_clean :
              Tail.InternallyDisjointFromSet
                S.linkage.toPathPacking.vertexSet := by
            simpa [Tail] using
              X.orientedSegment₁.dropUntil_internallyDisjointFromSet
                hxseg X.orientedSegment₁_clean_linkage
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
                (S.linkage.path X.upperIndex).vertexSet := by
            have htgt : Joined.target = X.t₁ := by
              simp [Joined, Tail]
            have hrow : Joined.target ∈ X.upperPath.vertexSet := by
              simpa [htgt] using X.t₁_mem_upper
            simpa using hrow
          exact Or.inr ⟨hiupper, Or.inl
            ⟨PathPacking.BridgeBetween.of_orientedPath
              S.linkage.toPathPacking Joined hjoined_src hjoined_tgt
                hjoined_clean⟩⟩
    · have htgt_old :
          P.target ∈ (S.linkage.path X.upperIndex).vertexSet := by
        have hrow : P.target ∈ X.upperPath.vertexSet :=
          X.upperPath.dropUntil_vertexSet_subset
            X.t₁_mem_upper hupperSuf
        simpa using hrow
      exact Or.inr ⟨hiupper, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩

/-- The corresponding assertion for the upper replacement path. -/
theorem old_aux_adj_to_crossed_row_of_new_bridge_to_upper_replacement
    (X : CorridorCross S) {i : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (β :
      X.replacementLinkage.toPathPacking.BridgeBetween
        i X.upperIndex) :
    (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
      (linkageAuxGraph S.linkage).Adj i X.upperIndex := by
  classical
  by_cases hhit :
      (β.orientedPath.vertexSet ∩ X.deletedMiddleVertexSet).Nonempty
  · exact X.old_aux_adj_to_crossed_row_of_new_bridge_hits_deleted
      hilower hiupper β hhit
  · have hmiss :
        Disjoint β.orientedPath.vertexSet X.deletedMiddleVertexSet := by
      rw [Finset.disjoint_left]
      intro v hvP hvDel
      exact hhit ⟨v, Finset.mem_inter.2 ⟨hvP, hvDel⟩⟩
    let P : GraphPath G := β.orientedPath
    have hsrc_old : P.source ∈ (S.linkage.path i).vertexSet := by
      have hsrc_new :=
        PathPacking.BridgeBetween.orientedPath_source_mem_left β
      simpa [P, X.replacementLinkage_path_of_ne hilower hiupper]
        using hsrc_new
    have hclean_old :
        P.InternallyDisjointFromSet S.linkage.toPathPacking.vertexSet :=
      X.internallyDisjoint_old_of_new_clean_disjoint_deleted
        P β.orientedPath_internallyDisjoint hmiss
    have htgt_upper :
        P.target ∈ X.replacementPaths.upperReplacement.vertexSet := by
      have htgt_new :=
        PathPacking.BridgeBetween.orientedPath_target_mem_right β
      simpa [P, X.replacementLinkage_path_upper] using htgt_new
    have hparts :=
      X.replacementPaths.upper_vertexSet_subset_parts htgt_upper
    rcases Finset.mem_union.1 hparts with hpre_or_seg | hlowerSuf
    · rcases Finset.mem_union.1 hpre_or_seg with hupperPre | hseg
      · have htgt_old :
            P.target ∈ (S.linkage.path X.upperIndex).vertexSet := by
          have hrow : P.target ∈ X.upperPath.vertexSet :=
            X.upperPath.takeUntil_vertexSet_subset
              X.t₂_mem_upper hupperPre
          simpa using hrow
        exact Or.inr ⟨hiupper, Or.inl
          ⟨PathPacking.BridgeBetween.of_orientedPath
            S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
      · have hxseg : P.target ∈ X.orientedSegment₂.vertexSet := hseg
        by_cases hxold :
            P.target ∈ S.linkage.toPathPacking.vertexSet
        · rcases X.orientedSegment₂_clean_linkage hxseg hxold with ht | hs
          · have htgt_old :
                P.target ∈ (S.linkage.path X.upperIndex).vertexSet := by
              have hrow : P.target ∈ X.upperPath.vertexSet := by
                rw [ht, X.orientedSegment₂_source]
                exact X.t₂_mem_upper
              simpa using hrow
            exact Or.inr ⟨hiupper, Or.inl
              ⟨PathPacking.BridgeBetween.of_orientedPath
                S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
          · have htgt_old :
                P.target ∈ (S.linkage.path X.lowerIndex).vertexSet := by
              have hrow : P.target ∈ X.lowerPath.vertexSet := by
                rw [hs, X.orientedSegment₂_target]
                exact X.s₂_mem_lower
              simpa using hrow
            exact Or.inl ⟨hilower, Or.inl
              ⟨PathPacking.BridgeBetween.of_orientedPath
                S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩
        · let Tail : GraphPath G := X.orientedSegment₂.dropUntil hxseg
          have hglue : P.target = Tail.source := by
            simp [Tail, P]
          have hinter :
              ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Tail.vertexSet →
                v = P.target := by
            intro v hvP hvtail
            have hvtail_seg : v ∈ X.orientedSegment₂.vertexSet :=
              X.orientedSegment₂.dropUntil_vertexSet_subset hxseg
                (by simpa [Tail] using hvtail)
            have hvupper :
                v ∈ X.replacementPaths.upperReplacement.vertexSet :=
              X.replacementPaths.segment₂_subset hvtail_seg
            have hvnew :
                v ∈ X.replacementLinkage.toPathPacking.vertexSet :=
              (X.replacementLinkage.toPathPacking.mem_vertexSet).2
                ⟨X.upperIndex, by
                  simpa [X.replacementLinkage_path_upper] using hvupper⟩
            rcases β.orientedPath_internallyDisjoint
                (by simpa [P] using hvP) hvnew with hsrc | htgt
            · have hsrc_new :
                  P.source ∈
                    (X.replacementLinkage.path i).vertexSet :=
                PathPacking.BridgeBetween.orientedPath_source_mem_left β
              have hsrc_i :
                  P.source ∈ (S.linkage.path i).vertexSet := by
                simpa [P, X.replacementLinkage_path_of_ne
                  hilower hiupper] using hsrc_new
              have hsrc_upper :
                  P.source ∈
                    X.replacementPaths.upperReplacement.vertexSet := by
                simpa [P, hsrc] using hvupper
              exact False.elim <|
                Finset.disjoint_left.mp
                  (X.upperReplacement_nodeDisjoint_unchanged
                    hilower hiupper) hsrc_upper hsrc_i
            · simpa [P] using htgt
          let Joined : GraphPath G :=
            P.appendWithEqOfInterSubsetTarget Tail hglue hinter
          have htail_clean :
              Tail.InternallyDisjointFromSet
                S.linkage.toPathPacking.vertexSet := by
            simpa [Tail] using
              X.orientedSegment₂.dropUntil_internallyDisjointFromSet
                hxseg X.orientedSegment₂_clean_linkage
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
                (S.linkage.path X.lowerIndex).vertexSet := by
            have htgt : Joined.target = X.s₂ := by
              simp [Joined, Tail]
            have hrow : Joined.target ∈ X.lowerPath.vertexSet := by
              simpa [htgt] using X.s₂_mem_lower
            simpa using hrow
          exact Or.inl ⟨hilower, Or.inl
            ⟨PathPacking.BridgeBetween.of_orientedPath
              S.linkage.toPathPacking Joined hjoined_src hjoined_tgt
                hjoined_clean⟩⟩
    · have htgt_old :
          P.target ∈ (S.linkage.path X.lowerIndex).vertexSet := by
        have hrow : P.target ∈ X.lowerPath.vertexSet :=
          X.lowerPath.dropUntil_vertexSet_subset
            X.s₂_mem_lower hlowerSuf
        simpa using hrow
      exact Or.inl ⟨hilower, Or.inl
        ⟨PathPacking.BridgeBetween.of_orientedPath
          S.linkage.toPathPacking P hsrc_old htgt_old hclean_old⟩⟩

/-- A genuinely new auxiliary edge with one unchanged endpoint has that
endpoint in the local quadruple. -/
theorem mem_local_quad_of_new_adj_not_old_at_left_endpoint
    (X : CorridorCross S) {i j auxA auxD : S.linkage.Index}
    (hilower : i ≠ X.lowerIndex) (hiupper : i ≠ X.upperIndex)
    (hnew : (linkageAuxGraph X.replacementLinkage).Adj i j)
    (hnotold : ¬ (linkageAuxGraph S.linkage).Adj i j)
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    i ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
      Finset S.linkage.Index) := by
  classical
  by_cases hjlower : j = X.lowerIndex
  · rcases hnew with ⟨_hij, hbridge⟩
    have hadjCross :
        (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
          (linkageAuxGraph S.linkage).Adj i X.upperIndex := by
      rcases hbridge with hβ | hβ
      · rcases hβ with ⟨β⟩
        exact X.old_aux_adj_to_crossed_row_of_new_bridge_to_lower_replacement
          hilower hiupper (by simpa [hjlower] using β)
      · rcases hβ with ⟨β⟩
        exact X.old_aux_adj_to_crossed_row_of_new_bridge_to_lower_replacement
          hilower hiupper
          (by simpa [hjlower] using X.reverseBridge β)
    exact X.mem_local_quad_of_old_adj_to_crossed_row
      hAU hUV hVD hU hV hA_ne_V hU_ne_D hadjCross
  · by_cases hjupper : j = X.upperIndex
    · rcases hnew with ⟨_hij, hbridge⟩
      have hadjCross :
          (linkageAuxGraph S.linkage).Adj i X.lowerIndex ∨
            (linkageAuxGraph S.linkage).Adj i X.upperIndex := by
        rcases hbridge with hβ | hβ
        · rcases hβ with ⟨β⟩
          exact X.old_aux_adj_to_crossed_row_of_new_bridge_to_upper_replacement
            hilower hiupper (by simpa [hjupper] using β)
        · rcases hβ with ⟨β⟩
          exact X.old_aux_adj_to_crossed_row_of_new_bridge_to_upper_replacement
            hilower hiupper
            (by simpa [hjupper] using X.reverseBridge β)
      exact X.mem_local_quad_of_old_adj_to_crossed_row
        hAU hUV hVD hU hV hA_ne_V hU_ne_D hadjCross
    · rcases hnew with ⟨hij, hbridge⟩
      rcases hbridge with hβ | hβ
      · rcases hβ with ⟨β⟩
        exact X.mem_local_quad_of_new_bridge_not_old_unchanged
          hij hilower hiupper hjlower hjupper β hnotold
          hAU hUV hVD hU hV hA_ne_V hU_ne_D
      · rcases hβ with ⟨β⟩
        exact X.mem_local_quad_of_new_bridge_not_old_unchanged
          hij hilower hiupper hjlower hjupper
          (X.reverseBridge β) hnotold
          hAU hUV hVD hU hV hA_ne_V hU_ne_D

/-- Symmetric endpoint-localizing form for a genuinely new auxiliary edge. -/
theorem mem_local_quad_of_new_adj_not_old_at_right_endpoint
    (X : CorridorCross S) {i j auxA auxD : S.linkage.Index}
    (hjlower : j ≠ X.lowerIndex) (hjupper : j ≠ X.upperIndex)
    (hnew : (linkageAuxGraph X.replacementLinkage).Adj i j)
    (hnotold : ¬ (linkageAuxGraph S.linkage).Adj i j)
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    j ∈ ({auxA, X.lowerIndex, X.upperIndex, auxD} :
      Finset S.linkage.Index) := by
  exact X.mem_local_quad_of_new_adj_not_old_at_left_endpoint
    hjlower hjupper ((linkageAuxGraph X.replacementLinkage).symm hnew)
    (fun hold => hnotold ((linkageAuxGraph S.linkage).symm hold))
    hAU hUV hVD hU hV hA_ne_V hU_ne_D

/-- Every auxiliary edge whose status changes under the cross switch has both
endpoints in the predecessor/crossed-pair/successor quadruple. -/
theorem cross_adjChangeSupportedIn
    (X : CorridorCross S) (auxA auxD : S.linkage.Index)
    (hAU : (linkageAuxGraph S.linkage).Adj auxA X.lowerIndex)
    (hUV : (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex)
    (hVD : (linkageAuxGraph S.linkage).Adj X.upperIndex auxD)
    (hU : DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2)
    (hV : DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2)
    (hA_ne_V : auxA ≠ X.upperIndex)
    (hU_ne_D : X.lowerIndex ≠ auxD) :
    IndexedAuxiliaryPrefix.AdjChangeSupportedIn
      (linkageAuxGraph S.linkage)
      (linkageAuxGraph X.replacementLinkage)
      ({auxA, X.lowerIndex, X.upperIndex, auxD} :
        Finset S.linkage.Index) := by
  classical
  intro u v hnonlocal
  constructor
  · intro hnew
    by_contra hnotold
    rcases hnonlocal with hu | hv
    · have hulower : u ≠ X.lowerIndex := by
        intro h
        exact hu (by simp [h])
      have huupper : u ≠ X.upperIndex := by
        intro h
        exact hu (by simp [h])
      exact hu <| X.mem_local_quad_of_new_adj_not_old_at_left_endpoint
        hulower huupper hnew hnotold
        hAU hUV hVD hU hV hA_ne_V hU_ne_D
    · have hvlower : v ≠ X.lowerIndex := by
        intro h
        exact hv (by simp [h])
      have hvupper : v ≠ X.upperIndex := by
        intro h
        exact hv (by simp [h])
      exact hv <| X.mem_local_quad_of_new_adj_not_old_at_right_endpoint
        hvlower hvupper hnew hnotold
        hAU hUV hVD hU hV hA_ne_V hU_ne_D
  · intro hold
    by_contra hnotnew
    rcases hnonlocal with hu | hv
    · have hulower : u ≠ X.lowerIndex := by
        intro h
        exact hu (by simp [h])
      have huupper : u ≠ X.upperIndex := by
        intro h
        exact hu (by simp [h])
      exact hu <| X.mem_local_quad_of_old_adj_not_new_at_left_endpoint
        hulower huupper hold hnotnew
        hAU hUV hVD hU hV hA_ne_V hU_ne_D
    · have hvlower : v ≠ X.lowerIndex := by
        intro h
        exact hv (by simp [h])
      have hvupper : v ≠ X.upperIndex := by
        intro h
        exact hv (by simp [h])
      exact hv <| X.mem_local_quad_of_old_adj_not_new_at_right_endpoint
        hvlower hvupper hold hnotnew
        hAU hUV hVD hU hV hA_ne_V hU_ne_D

/-! ## The surviving cross edge -/

theorem deletedLowerInterval_inter_lowerReplacement_endpoint
    (X : CorridorCross S) {v : V}
    (hvdel : v ∈ X.deletedLowerInterval.vertexSet)
    (hvrep : v ∈ X.replacementPaths.lowerReplacement.vertexSet) :
    X.deletedLowerInterval.IsEndpoint v := by
  have hvlower : v ∈ X.lowerPath.vertexSet :=
    X.lowerPath.segmentOfBefore_vertexSet_subset
      X.s₁_before_s₂ hvdel
  have hparts :=
    X.replacementPaths.lower_vertexSet_subset_parts hvrep
  rcases Finset.mem_union.1 hparts with hpre_or_seg | hupperSuf
  · rcases Finset.mem_union.1 hpre_or_seg with hlowerPre | hseg
    · have hvBefore :
          X.lowerPath.Before v X.s₁ :=
        X.lowerPath.before_of_mem_takeUntil
          X.s₁_mem_lower hlowerPre
      have hsBefore :
          X.lowerPath.Before X.s₁ v :=
        X.lowerPath.before_of_mem_segmentOfBefore_left
          X.s₁_before_s₂ hvdel
      have hv_eq : v = X.s₁ :=
        X.lowerPath.before_antisymm hvBefore hsBefore
      exact Or.inl (by simpa [deletedLowerInterval] using hv_eq)
    · have hvlink :
          v ∈ S.linkage.toPathPacking.vertexSet :=
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨X.lowerIndex, by simpa using hvlower⟩
      rcases X.orientedSegment₁_clean_linkage hseg hvlink with hs | ht
      · exact Or.inl (by simpa [deletedLowerInterval] using hs)
      · exact False.elim
          (X.t₁_not_mem_lower (by simpa [ht] using hvlower))
  · have hvupper : v ∈ X.upperPath.vertexSet :=
      X.upperPath.dropUntil_vertexSet_subset
        X.t₁_mem_upper hupperSuf
    exact False.elim (X.lower_upper_disjoint_at hvlower hvupper)

theorem deletedLowerInterval_inter_upperReplacement_endpoint
    (X : CorridorCross S) {v : V}
    (hvdel : v ∈ X.deletedLowerInterval.vertexSet)
    (hvrep : v ∈ X.replacementPaths.upperReplacement.vertexSet) :
    X.deletedLowerInterval.IsEndpoint v := by
  have hvlower : v ∈ X.lowerPath.vertexSet :=
    X.lowerPath.segmentOfBefore_vertexSet_subset
      X.s₁_before_s₂ hvdel
  have hparts :=
    X.replacementPaths.upper_vertexSet_subset_parts hvrep
  rcases Finset.mem_union.1 hparts with hpre_or_seg | hlowerSuf
  · rcases Finset.mem_union.1 hpre_or_seg with hupperPre | hseg
    · have hvupper : v ∈ X.upperPath.vertexSet :=
        X.upperPath.takeUntil_vertexSet_subset
          X.t₂_mem_upper hupperPre
      exact False.elim (X.lower_upper_disjoint_at hvlower hvupper)
    · have hvlink :
          v ∈ S.linkage.toPathPacking.vertexSet :=
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨X.lowerIndex, by simpa using hvlower⟩
      rcases X.orientedSegment₂_clean_linkage hseg hvlink with ht | hs
      · exact False.elim
          (X.t₂_not_mem_lower (by simpa [ht] using hvlower))
      · exact Or.inr (by simpa [deletedLowerInterval] using hs)
  · have hsBefore : X.lowerPath.Before X.s₂ v :=
      ⟨X.s₂_mem_lower, hlowerSuf⟩
    have hvBefore : X.lowerPath.Before v X.s₂ :=
      X.lowerPath.before_of_mem_segmentOfBefore_right
        X.s₁_before_s₂ hvdel
    have hv_eq : v = X.s₂ :=
      X.lowerPath.before_antisymm hvBefore hsBefore
    exact Or.inr (by simpa [deletedLowerInterval] using hv_eq)

theorem deletedUpperInterval_inter_lowerReplacement_endpoint
    (X : CorridorCross S) {v : V}
    (hvdel : v ∈ X.deletedUpperInterval.vertexSet)
    (hvrep : v ∈ X.replacementPaths.lowerReplacement.vertexSet) :
    X.deletedUpperInterval.IsEndpoint v := by
  have hvupper : v ∈ X.upperPath.vertexSet :=
    X.upperPath.segmentOfBefore_vertexSet_subset
      X.t₂_before_t₁ hvdel
  have hparts :=
    X.replacementPaths.lower_vertexSet_subset_parts hvrep
  rcases Finset.mem_union.1 hparts with hpre_or_seg | hupperSuf
  · rcases Finset.mem_union.1 hpre_or_seg with hlowerPre | hseg
    · have hvlower : v ∈ X.lowerPath.vertexSet :=
        X.lowerPath.takeUntil_vertexSet_subset
          X.s₁_mem_lower hlowerPre
      exact False.elim (X.lower_upper_disjoint_at hvlower hvupper)
    · have hvlink :
          v ∈ S.linkage.toPathPacking.vertexSet :=
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨X.upperIndex, by simpa using hvupper⟩
      rcases X.orientedSegment₁_clean_linkage hseg hvlink with hs | ht
      · exact False.elim
          (X.s₁_not_mem_upper (by simpa [hs] using hvupper))
      · exact Or.inr (by simpa [deletedUpperInterval] using ht)
  · have htBefore : X.upperPath.Before X.t₁ v :=
      ⟨X.t₁_mem_upper, hupperSuf⟩
    have hvBefore : X.upperPath.Before v X.t₁ :=
      X.upperPath.before_of_mem_segmentOfBefore_right
        X.t₂_before_t₁ hvdel
    have hv_eq : v = X.t₁ :=
      X.upperPath.before_antisymm hvBefore htBefore
    exact Or.inr (by simpa [deletedUpperInterval] using hv_eq)

theorem deletedUpperInterval_inter_upperReplacement_endpoint
    (X : CorridorCross S) {v : V}
    (hvdel : v ∈ X.deletedUpperInterval.vertexSet)
    (hvrep : v ∈ X.replacementPaths.upperReplacement.vertexSet) :
    X.deletedUpperInterval.IsEndpoint v := by
  have hvupper : v ∈ X.upperPath.vertexSet :=
    X.upperPath.segmentOfBefore_vertexSet_subset
      X.t₂_before_t₁ hvdel
  have hparts :=
    X.replacementPaths.upper_vertexSet_subset_parts hvrep
  rcases Finset.mem_union.1 hparts with hpre_or_seg | hlowerSuf
  · rcases Finset.mem_union.1 hpre_or_seg with hupperPre | hseg
    · have hvBefore : X.upperPath.Before v X.t₂ :=
        X.upperPath.before_of_mem_takeUntil
          X.t₂_mem_upper hupperPre
      have htBefore : X.upperPath.Before X.t₂ v :=
        X.upperPath.before_of_mem_segmentOfBefore_left
          X.t₂_before_t₁ hvdel
      have hv_eq : v = X.t₂ :=
        X.upperPath.before_antisymm hvBefore htBefore
      exact Or.inl (by simpa [deletedUpperInterval] using hv_eq)
    · have hvlink :
          v ∈ S.linkage.toPathPacking.vertexSet :=
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨X.upperIndex, by simpa using hvupper⟩
      rcases X.orientedSegment₂_clean_linkage hseg hvlink with ht | hs
      · exact Or.inl (by simpa [deletedUpperInterval] using ht)
      · exact False.elim
          (X.s₂_not_mem_upper (by simpa [hs] using hvupper))
  · have hvlower : v ∈ X.lowerPath.vertexSet :=
      X.lowerPath.dropUntil_vertexSet_subset
        X.s₂_mem_lower hlowerSuf
    exact False.elim (X.lower_upper_disjoint_at hvlower hvupper)

/-- The deleted lower middle segment is clean for the new linkage. -/
theorem deletedLowerInterval_clean_replacementLinkage
    (X : CorridorCross S) :
    X.deletedLowerInterval.InternallyDisjointFromSet
      X.replacementLinkage.toPathPacking.vertexSet := by
  intro v hvdel hvnew
  rcases (X.replacementLinkage.toPathPacking.mem_vertexSet).1 hvnew with
    ⟨i, hvi⟩
  by_cases hilower : i = X.lowerIndex
  · subst i
    exact X.deletedLowerInterval_inter_lowerReplacement_endpoint
      hvdel (by simpa using hvi)
  · by_cases hiupper : i = X.upperIndex
    · subst i
      exact X.deletedLowerInterval_inter_upperReplacement_endpoint
        hvdel (by simpa using hvi)
    · have hvrow :
          v ∈ (S.linkage.path X.lowerIndex).vertexSet := by
        simpa using X.lowerPath.segmentOfBefore_vertexSet_subset
          X.s₁_before_s₂ hvdel
      have hviOld : v ∈ (S.linkage.path i).vertexSet := by
        simpa [X.replacementLinkage_path_of_ne hilower hiupper] using hvi
      exact False.elim <| Finset.disjoint_left.mp
        (S.linkage.toPathPacking.node_disjoint
          (fun h => hilower h.symm)) hvrow hviOld

/-- The deleted upper middle segment is clean for the new linkage. -/
theorem deletedUpperInterval_clean_replacementLinkage
    (X : CorridorCross S) :
    X.deletedUpperInterval.InternallyDisjointFromSet
      X.replacementLinkage.toPathPacking.vertexSet := by
  intro v hvdel hvnew
  rcases (X.replacementLinkage.toPathPacking.mem_vertexSet).1 hvnew with
    ⟨i, hvi⟩
  by_cases hilower : i = X.lowerIndex
  · subst i
    exact X.deletedUpperInterval_inter_lowerReplacement_endpoint
      hvdel (by simpa using hvi)
  · by_cases hiupper : i = X.upperIndex
    · subst i
      exact X.deletedUpperInterval_inter_upperReplacement_endpoint
        hvdel (by simpa using hvi)
    · have hvrow :
          v ∈ (S.linkage.path X.upperIndex).vertexSet := by
        simpa using X.upperPath.segmentOfBefore_vertexSet_subset
          X.t₂_before_t₁ hvdel
      have hviOld : v ∈ (S.linkage.path i).vertexSet := by
        simpa [X.replacementLinkage_path_of_ne hilower hiupper] using hvi
      exact False.elim <| Finset.disjoint_left.mp
        (S.linkage.toPathPacking.node_disjoint
          (fun h => hiupper h.symm)) hvrow hviOld

/-- The freed lower-row interval witnesses adjacency of the switched rows. -/
theorem replacementLinkage_adj_lower_upper
    (X : CorridorCross S) :
    (linkageAuxGraph X.replacementLinkage).Adj
      X.lowerIndex X.upperIndex := by
  refine ⟨X.lowerIndex_ne_upperIndex, Or.inl ?_⟩
  refine ⟨PathPacking.BridgeBetween.of_orientedPath
    X.replacementLinkage.toPathPacking
    X.deletedLowerInterval ?_ ?_
    X.deletedLowerInterval_clean_replacementLinkage⟩
  · simpa [deletedLowerInterval] using
      X.replacementPaths.s₁_mem_lowerReplacement
  · simpa [deletedLowerInterval] using
      X.replacementPaths.s₂_mem_upperReplacement

/-! ## The four corridor indices around a cross -/

def prevPosition (X : CorridorCross S) : Fin (activeCount + 2) :=
  ⟨X.lowerRow.1, by omega⟩

def lowerPosition (X : CorridorCross S) : Fin (activeCount + 2) :=
  S.corridor.activePosition X.lowerRow

def upperPosition (X : CorridorCross S) : Fin (activeCount + 2) :=
  S.corridor.activePosition X.upperRow

def nextPosition (X : CorridorCross S) : Fin (activeCount + 2) :=
  ⟨X.upperRow.1 + 2, by
    have := X.upperRow.2
    omega⟩

def prevIndex (X : CorridorCross S) : S.linkage.Index :=
  S.corridor.index X.prevPosition

def nextIndex (X : CorridorCross S) : S.linkage.Index :=
  S.corridor.index X.nextPosition

@[simp] theorem lowerPosition_index (X : CorridorCross S) :
    S.corridor.index X.lowerPosition = X.lowerIndex :=
  rfl

@[simp] theorem upperPosition_index (X : CorridorCross S) :
    S.corridor.index X.upperPosition = X.upperIndex :=
  rfl

theorem prev_ne_lower (X : CorridorCross S) :
    X.prevIndex ≠ X.lowerIndex := by
  intro h
  have hp : X.prevPosition = X.lowerPosition :=
    S.corridor.index_injective h
  have hv := congrArg Fin.val hp
  change X.lowerRow.1 = X.lowerRow.1 + 1 at hv
  omega

theorem prev_ne_upper (X : CorridorCross S) :
    X.prevIndex ≠ X.upperIndex := by
  intro h
  have hp : X.prevPosition = X.upperPosition :=
    S.corridor.index_injective h
  have hv := congrArg Fin.val hp
  change X.lowerRow.1 = X.upperRow.1 + 1 at hv
  have hcon := X.consecutive
  omega

theorem prev_ne_next (X : CorridorCross S) :
    X.prevIndex ≠ X.nextIndex := by
  intro h
  have hp : X.prevPosition = X.nextPosition :=
    S.corridor.index_injective h
  have hv := congrArg Fin.val hp
  change X.lowerRow.1 = X.upperRow.1 + 2 at hv
  have hcon := X.consecutive
  omega

theorem lower_ne_next (X : CorridorCross S) :
    X.lowerIndex ≠ X.nextIndex := by
  intro h
  have hp : X.lowerPosition = X.nextPosition :=
    S.corridor.index_injective h
  have hv := congrArg Fin.val hp
  change X.lowerRow.1 + 1 = X.upperRow.1 + 2 at hv
  have hcon := X.consecutive
  omega

theorem upper_ne_next (X : CorridorCross S) :
    X.upperIndex ≠ X.nextIndex := by
  intro h
  have hp : X.upperPosition = X.nextPosition :=
    S.corridor.index_injective h
  have hv := congrArg Fin.val hp
  change X.upperRow.1 + 1 = X.upperRow.1 + 2 at hv
  omega

theorem prev_adj_lower (X : CorridorCross S) :
    (linkageAuxGraph S.linkage).Adj X.prevIndex X.lowerIndex := by
  exact S.corridor.adj_of_consecutive (Or.inl rfl)

theorem lower_adj_upper (X : CorridorCross S) :
    (linkageAuxGraph S.linkage).Adj X.lowerIndex X.upperIndex := by
  apply S.corridor.adj_of_consecutive
  left
  change X.lowerRow.1 + 1 + 1 = X.upperRow.1 + 1
  have hcon := X.consecutive
  omega

theorem upper_adj_next (X : CorridorCross S) :
    (linkageAuxGraph S.linkage).Adj X.upperIndex X.nextIndex := by
  exact S.corridor.adj_of_consecutive (Or.inl rfl)

theorem prev_degree_two (X : CorridorCross S) :
    DegreeEquals (linkageAuxGraph S.linkage) X.prevIndex 2 :=
  S.corridor.degree_two X.prevPosition

theorem lower_degree_two (X : CorridorCross S) :
    DegreeEquals (linkageAuxGraph S.linkage) X.lowerIndex 2 :=
  S.corridor.degree_two X.lowerPosition

theorem upper_degree_two (X : CorridorCross S) :
    DegreeEquals (linkageAuxGraph S.linkage) X.upperIndex 2 :=
  S.corridor.degree_two X.upperPosition

theorem next_degree_two (X : CorridorCross S) :
    DegreeEquals (linkageAuxGraph S.linkage) X.nextIndex 2 :=
  S.corridor.degree_two X.nextPosition

noncomputable def prevOuterIndex (X : CorridorCross S) :
    S.linkage.Index :=
  Classical.choose
    (X.prev_degree_two.two_exists_adj_ne X.prev_adj_lower)

theorem prev_adj_prevOuter (X : CorridorCross S) :
    (linkageAuxGraph S.linkage).Adj X.prevIndex X.prevOuterIndex :=
  (Classical.choose_spec
    (X.prev_degree_two.two_exists_adj_ne X.prev_adj_lower)).1

theorem prevOuter_ne_lower (X : CorridorCross S) :
    X.prevOuterIndex ≠ X.lowerIndex :=
  (Classical.choose_spec
    (X.prev_degree_two.two_exists_adj_ne X.prev_adj_lower)).2

noncomputable def nextOuterIndex (X : CorridorCross S) :
    S.linkage.Index :=
  Classical.choose
    (X.next_degree_two.two_exists_adj_ne X.upper_adj_next.symm)

theorem next_adj_nextOuter (X : CorridorCross S) :
    (linkageAuxGraph S.linkage).Adj X.nextIndex X.nextOuterIndex :=
  (Classical.choose_spec
    (X.next_degree_two.two_exists_adj_ne X.upper_adj_next.symm)).1

theorem nextOuter_ne_upper (X : CorridorCross S) :
    X.nextOuterIndex ≠ X.upperIndex :=
  (Classical.choose_spec
    (X.next_degree_two.two_exists_adj_ne X.upper_adj_next.symm)).2

theorem prevOuter_ne_prev (X : CorridorCross S) :
    X.prevOuterIndex ≠ X.prevIndex :=
  X.prev_adj_prevOuter.ne.symm

theorem nextOuter_ne_next (X : CorridorCross S) :
    X.nextOuterIndex ≠ X.nextIndex :=
  X.next_adj_nextOuter.ne.symm

theorem prev_not_adj_upper (X : CorridorCross S) :
    ¬ (linkageAuxGraph S.linkage).Adj X.prevIndex X.upperIndex := by
  intro h
  have hc := S.corridor.adj_iff_consecutive.mp h
  have hcon := X.consecutive
  rcases hc with hc | hc
  · change X.lowerRow.1 + 1 = X.upperRow.1 + 1 at hc
    omega
  · change X.upperRow.1 + 1 + 1 = X.lowerRow.1 at hc
    omega

theorem prev_not_adj_next (X : CorridorCross S) :
    ¬ (linkageAuxGraph S.linkage).Adj X.prevIndex X.nextIndex := by
  intro h
  have hc := S.corridor.adj_iff_consecutive.mp h
  have hcon := X.consecutive
  rcases hc with hc | hc
  · change X.lowerRow.1 + 1 = X.upperRow.1 + 2 at hc
    omega
  · change X.upperRow.1 + 2 + 1 = X.lowerRow.1 at hc
    omega

theorem lower_not_adj_next (X : CorridorCross S) :
    ¬ (linkageAuxGraph S.linkage).Adj X.lowerIndex X.nextIndex := by
  intro h
  have hc := S.corridor.adj_iff_consecutive.mp h
  have hcon := X.consecutive
  rcases hc with hc | hc
  · change X.lowerRow.1 + 1 + 1 = X.upperRow.1 + 2 at hc
    omega
  · change X.upperRow.1 + 2 + 1 = X.lowerRow.1 + 1 at hc
    omega

theorem prevOuter_ne_upper (X : CorridorCross S) :
    X.prevOuterIndex ≠ X.upperIndex := by
  intro h
  exact X.prev_not_adj_upper (by simpa [h] using X.prev_adj_prevOuter)

theorem prevOuter_ne_next (X : CorridorCross S) :
    X.prevOuterIndex ≠ X.nextIndex := by
  intro h
  exact X.prev_not_adj_next (by simpa [h] using X.prev_adj_prevOuter)

theorem nextOuter_ne_prev (X : CorridorCross S) :
    X.nextOuterIndex ≠ X.prevIndex := by
  intro h
  exact X.prev_not_adj_next <|
    (by simpa [h] using X.next_adj_nextOuter.symm)

theorem nextOuter_ne_lower (X : CorridorCross S) :
    X.nextOuterIndex ≠ X.lowerIndex := by
  intro h
  exact X.lower_not_adj_next <|
    (by simpa [h] using X.next_adj_nextOuter.symm)

theorem prevOuter_not_mem_local (X : CorridorCross S) :
    X.prevOuterIndex ∉
      ({X.prevIndex, X.lowerIndex, X.upperIndex, X.nextIndex} :
        Finset S.linkage.Index) := by
  simp [X.prevOuter_ne_prev, X.prevOuter_ne_lower,
    X.prevOuter_ne_upper, X.prevOuter_ne_next]

theorem nextOuter_not_mem_local (X : CorridorCross S) :
    X.nextOuterIndex ∉
      ({X.prevIndex, X.lowerIndex, X.upperIndex, X.nextIndex} :
        Finset S.linkage.Index) := by
  simp [X.nextOuter_ne_prev, X.nextOuter_ne_lower,
    X.nextOuter_ne_upper, X.nextOuter_ne_next]

/-- If all four local vertices remain degree two, their new order is one of
the two possible orders of the switched pair.  This is a purely finite-graph
consequence of support locality and the surviving lower--upper edge. -/
theorem replacement_attachment_order_of_all_degree_two
    (X : CorridorCross S)
    (hPrevNew :
      DegreeEquals (linkageAuxGraph X.replacementLinkage)
        X.prevIndex 2)
    (hLowerNew :
      DegreeEquals (linkageAuxGraph X.replacementLinkage)
        X.lowerIndex 2)
    (hUpperNew :
      DegreeEquals (linkageAuxGraph X.replacementLinkage)
        X.upperIndex 2)
    (hNextNew :
      DegreeEquals (linkageAuxGraph X.replacementLinkage)
        X.nextIndex 2) :
    ((linkageAuxGraph X.replacementLinkage).Adj
        X.prevIndex X.lowerIndex ∧
      (linkageAuxGraph X.replacementLinkage).Adj
        X.upperIndex X.nextIndex) ∨
    ((linkageAuxGraph X.replacementLinkage).Adj
        X.prevIndex X.upperIndex ∧
      (linkageAuxGraph X.replacementLinkage).Adj
        X.lowerIndex X.nextIndex) := by
  classical
  let H := linkageAuxGraph S.linkage
  let H' := linkageAuxGraph X.replacementLinkage
  let localSet : Finset S.linkage.Index :=
    {X.prevIndex, X.lowerIndex, X.upperIndex, X.nextIndex}
  have hsupport :
      IndexedAuxiliaryPrefix.AdjChangeSupportedIn H H' localSet := by
    simpa [H, H', localSet] using
      X.cross_adjChangeSupportedIn X.prevIndex X.nextIndex
        X.prev_adj_lower X.lower_adj_upper X.upper_adj_next
        X.lower_degree_two X.upper_degree_two
        X.prev_ne_upper X.lower_ne_next
  have hPrevOuterNew :
      H'.Adj X.prevIndex X.prevOuterIndex :=
    (hsupport (u := X.prevIndex) (v := X.prevOuterIndex)
      (Or.inr (by simpa [localSet] using X.prevOuter_not_mem_local))).2
      (by simpa [H] using X.prev_adj_prevOuter)
  have hNextOuterNew :
      H'.Adj X.nextIndex X.nextOuterIndex :=
    (hsupport (u := X.nextIndex) (v := X.nextOuterIndex)
      (Or.inr (by simpa [localSet] using X.nextOuter_not_mem_local))).2
      (by simpa [H] using X.next_adj_nextOuter)
  obtain ⟨x, hLowerX, hxUpper⟩ :=
    hLowerNew.two_exists_adj_ne
      (by simpa [H'] using X.replacementLinkage_adj_lower_upper)
  have hx :
      x = X.prevIndex ∨ x = X.nextIndex := by
    by_cases hxlocal : x ∈ localSet
    · change x ∈
        ({X.prevIndex, X.lowerIndex, X.upperIndex, X.nextIndex} :
          Finset S.linkage.Index) at hxlocal
      rcases Finset.mem_insert.mp hxlocal with hp | hrest
      · exact Or.inl hp
      · rcases Finset.mem_insert.mp hrest with hl | hrest
        · subst x
          exact False.elim (H'.loopless.irrefl _ hLowerX)
        · rcases Finset.mem_insert.mp hrest with hu | hn
          · exact False.elim (hxUpper hu)
          · exact Or.inr (Finset.mem_singleton.mp hn)
    · have hold : H.Adj X.lowerIndex x :=
        (hsupport (u := X.lowerIndex) (v := x)
          (Or.inr hxlocal)).1 hLowerX
      rcases DegreeEquals.two_adj_eq_or_eq X.lower_degree_two
          X.prev_adj_lower.symm X.lower_adj_upper X.prev_ne_upper
          (by simpa [H] using hold) with hp | hu
      · exact Or.inl hp
      · exact False.elim (hxUpper hu)
  obtain ⟨y, hUpperY, hyLower⟩ :=
    hUpperNew.two_exists_adj_ne
      (by simpa [H'] using X.replacementLinkage_adj_lower_upper.symm)
  have hy :
      y = X.prevIndex ∨ y = X.nextIndex := by
    by_cases hylocal : y ∈ localSet
    · change y ∈
        ({X.prevIndex, X.lowerIndex, X.upperIndex, X.nextIndex} :
          Finset S.linkage.Index) at hylocal
      rcases Finset.mem_insert.mp hylocal with hp | hrest
      · exact Or.inl hp
      · rcases Finset.mem_insert.mp hrest with hl | hrest
        · exact False.elim (hyLower hl)
        · rcases Finset.mem_insert.mp hrest with hu | hn
          · subst y
            exact False.elim (H'.loopless.irrefl _ hUpperY)
          · exact Or.inr (Finset.mem_singleton.mp hn)
    · have hold : H.Adj X.upperIndex y :=
        (hsupport (u := X.upperIndex) (v := y)
          (Or.inr hylocal)).1 hUpperY
      rcases DegreeEquals.two_adj_eq_or_eq X.upper_degree_two
          X.lower_adj_upper.symm X.upper_adj_next X.lower_ne_next
          (by simpa [H] using hold) with hl | hn
      · exact False.elim (hyLower hl)
      · exact Or.inr hn
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · have houter :
          X.prevOuterIndex = X.lowerIndex ∨
            X.prevOuterIndex = X.upperIndex :=
        DegreeEquals.two_adj_eq_or_eq hPrevNew
          hLowerX.symm hUpperY.symm X.lowerIndex_ne_upperIndex
          hPrevOuterNew
      rcases houter with h | h
      · exact False.elim (X.prevOuter_ne_lower h)
      · exact False.elim (X.prevOuter_ne_upper h)
    · exact Or.inl ⟨hLowerX.symm, hUpperY⟩
  · rcases hy with rfl | rfl
    · exact Or.inr ⟨hUpperY.symm, hLowerX⟩
    · have houter :
          X.nextOuterIndex = X.lowerIndex ∨
            X.nextOuterIndex = X.upperIndex :=
        DegreeEquals.two_adj_eq_or_eq hNextNew
          hLowerX.symm hUpperY.symm X.lowerIndex_ne_upperIndex
          hNextOuterNew
      rcases houter with h | h
      · exact False.elim (X.nextOuter_ne_lower h)
      · exact False.elim (X.nextOuter_ne_upper h)

/-- The four linkage indices whose auxiliary adjacencies can change in a
cross switch. -/
def localIndexSet (X : CorridorCross S) : Finset S.linkage.Index :=
  {X.prevIndex, X.lowerIndex, X.upperIndex, X.nextIndex}

/-- The source-faithful auxiliary dichotomy for a cross switch.  If one of
the four local vertices ceases to have degree two, the global degree-two
count drops.  Otherwise the auxiliary graph is either unchanged on the
shared index type, or unchanged after swapping the two crossed-row indices.
-/
theorem degree_drop_or_auxiliary_equivalent
    (X : CorridorCross S) :
    linkageAuxDegreeTwoCount X.replacementLinkage <
        linkageAuxDegreeTwoCount S.linkage ∨
      (∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) ∨
      (∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j)) := by
  classical
  let H := linkageAuxGraph S.linkage
  let H' := linkageAuxGraph X.replacementLinkage
  have hsupport :
      IndexedAuxiliaryPrefix.AdjChangeSupportedIn
        H H' X.localIndexSet := by
    simpa [H, H', localIndexSet] using
      X.cross_adjChangeSupportedIn X.prevIndex X.nextIndex
        X.prev_adj_lower X.lower_adj_upper X.upper_adj_next
        X.lower_degree_two X.upper_degree_two
        X.prev_ne_upper X.lower_ne_next
  have hlocalOld :
      ∀ x : S.linkage.Index, x ∈ X.localIndexSet →
        DegreeEquals H x 2 := by
    intro x hx
    simp [localIndexSet] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa [H] using X.prev_degree_two
    · simpa [H] using X.lower_degree_two
    · simpa [H] using X.upper_degree_two
    · simpa [H] using X.next_degree_two
  have degreeDropOf
      {x : S.linkage.Index}
      (hx : x ∈ X.localIndexSet)
      (hnot : ¬ DegreeEquals H' x 2) :
      linkageAuxDegreeTwoCount X.replacementLinkage <
        linkageAuxDegreeTwoCount S.linkage := by
    have hlt :=
      IndexedAuxiliaryPrefix.degreeTwoVertexCount_lt_of_supported_local_drop
        H H' X.localIndexSet hsupport hlocalOld ⟨x, hx, hnot⟩
    simpa [linkageAuxDegreeTwoCount, H, H'] using hlt
  by_cases hPrevNew : DegreeEquals H' X.prevIndex 2
  · by_cases hLowerNew : DegreeEquals H' X.lowerIndex 2
    · by_cases hUpperNew : DegreeEquals H' X.upperIndex 2
      · by_cases hNextNew : DegreeEquals H' X.nextIndex 2
        · rcases X.replacement_attachment_order_of_all_degree_two
              (by simpa [H'] using hPrevNew)
              (by simpa [H'] using hLowerNew)
              (by simpa [H'] using hUpperNew)
              (by simpa [H'] using hNextNew) with hsame | hswap
          · exact Or.inr (Or.inl <|
              IndexedAuxiliaryPrefix.cross_local_adj_iff_of_supported_degree_two
                (H := H) (H' := H')
                (L := X.prevOuterIndex) (A := X.prevIndex)
                (U := X.lowerIndex) (V := X.upperIndex)
                (D := X.nextIndex) (R := X.nextOuterIndex)
                hsupport
                (by simpa [H] using X.prev_adj_prevOuter)
                (by simpa [H] using X.prev_adj_lower)
                (by simpa [H] using X.lower_adj_upper)
                (by simpa [H] using X.upper_adj_next)
                (by simpa [H] using X.next_adj_nextOuter)
                (by simpa [H'] using hsame.1)
                (by simpa [H'] using
                  X.replacementLinkage_adj_lower_upper)
                (by simpa [H'] using hsame.2)
                (by simpa [H] using X.prev_degree_two)
                (by simpa [H] using X.lower_degree_two)
                (by simpa [H] using X.upper_degree_two)
                (by simpa [H] using X.next_degree_two)
                hPrevNew hLowerNew hUpperNew hNextNew
                X.prevOuter_not_mem_local X.nextOuter_not_mem_local
                X.prevOuter_ne_lower X.nextOuter_ne_upper
                X.prev_ne_lower X.prev_ne_next X.lower_ne_next
                X.prev_ne_upper X.upper_ne_next.symm
                X.prevOuter_ne_next)
          · exact Or.inr (Or.inr <|
              IndexedAuxiliaryPrefix.cross_local_adj_swap_iff_of_supported_degree_two
                (H := H) (H' := H')
                (L := X.prevOuterIndex) (A := X.prevIndex)
                (U := X.lowerIndex) (V := X.upperIndex)
                (D := X.nextIndex) (R := X.nextOuterIndex)
                hsupport
                (by simpa [H] using X.prev_adj_prevOuter)
                (by simpa [H] using X.prev_adj_lower)
                (by simpa [H] using X.lower_adj_upper)
                (by simpa [H] using X.upper_adj_next)
                (by simpa [H] using X.next_adj_nextOuter)
                (by simpa [H'] using hswap.1)
                (by simpa [H'] using
                  X.replacementLinkage_adj_lower_upper.symm)
                (by simpa [H'] using hswap.2)
                (by simpa [H] using X.prev_degree_two)
                (by simpa [H] using X.lower_degree_two)
                (by simpa [H] using X.upper_degree_two)
                (by simpa [H] using X.next_degree_two)
                hPrevNew hLowerNew hUpperNew hNextNew
                X.prevOuter_not_mem_local X.nextOuter_not_mem_local
                X.prevOuter_ne_lower X.nextOuter_ne_upper
                X.prev_ne_lower X.prev_ne_next X.lower_ne_next
                X.prev_ne_upper X.upper_ne_next.symm
                X.prevOuter_ne_next)
        · exact Or.inl <| degreeDropOf (by simp [localIndexSet]) hNextNew
      · exact Or.inl <| degreeDropOf (by simp [localIndexSet]) hUpperNew
    · exact Or.inl <| degreeDropOf (by simp [localIndexSet]) hLowerNew
  · exact Or.inl <| degreeDropOf (by simp [localIndexSet]) hPrevNew

/-! ## Transported successor states -/

theorem lowerBoundaryIndex_ne_lower (X : CorridorCross S) :
    S.corridor.index ⟨0, by omega⟩ ≠ X.lowerIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  simp [lowerIndex, AuxiliaryCorridor.activePosition] at hval

theorem lowerBoundaryIndex_ne_upper (X : CorridorCross S) :
    S.corridor.index ⟨0, by omega⟩ ≠ X.upperIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  simp [upperIndex, AuxiliaryCorridor.activePosition] at hval

theorem upperBoundaryIndex_ne_lower (X : CorridorCross S) :
    S.corridor.index ⟨activeCount + 1, by omega⟩ ≠
      X.lowerIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  simp [lowerIndex, AuxiliaryCorridor.activePosition] at hval
  omega

theorem upperBoundaryIndex_ne_upper (X : CorridorCross S) :
    S.corridor.index ⟨activeCount + 1, by omega⟩ ≠
      X.upperIndex := by
  intro h
  have hpos := S.corridor.index_injective h
  have hval := congrArg Fin.val hpos
  simp [upperIndex, AuxiliaryCorridor.activePosition] at hval
  omega

theorem outsideIndex_ne_lower
    (X : CorridorCross S) {j : S.linkage.Index}
    (hj : j ∉ Set.range S.corridor.index) :
    j ≠ X.lowerIndex := by
  intro h
  apply hj
  refine ⟨S.corridor.activePosition X.lowerRow, ?_⟩
  simpa [lowerIndex] using h.symm

theorem outsideIndex_ne_upper
    (X : CorridorCross S) {j : S.linkage.Index}
    (hj : j ∉ Set.range S.corridor.index) :
    j ≠ X.upperIndex := by
  intro h
  apply hj
  refine ⟨S.corridor.activePosition X.upperRow, ?_⟩
  simpa [upperIndex] using h.symm

/-- The successor state when the replacement rows retain their old
auxiliary order. -/
noncomputable def successorStateSame
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    CorridorRowState original activeCount ι fixedColumn :=
  CorridorRowState.successorOfAuxEquiv S
    (linkage' := X.replacementLinkage)
    (Equiv.refl S.linkage.Index)
    (fun i j => (hadj i j).symm)
    (by
      simpa using X.replacementLinkage_path_of_ne
        X.lowerBoundaryIndex_ne_lower X.lowerBoundaryIndex_ne_upper)
    (by
      simpa using X.replacementLinkage_path_of_ne
        X.upperBoundaryIndex_ne_lower X.upperBoundaryIndex_ne_upper)
    (by
      intro j hj
      simpa using X.replacementLinkage_path_of_ne
        (X.outsideIndex_ne_lower hj) (X.outsideIndex_ne_upper hj))

/-- The successor state when the two replacement rows occur in the swapped
auxiliary order. -/
noncomputable def successorStateSwap
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j)) :
    CorridorRowState original activeCount ι fixedColumn :=
  CorridorRowState.successorOfAuxEquiv S
    (linkage' := X.replacementLinkage)
    (Equiv.swap X.lowerIndex X.upperIndex)
    (by
      intro i j
      have h :=
        hadj ((Equiv.swap X.lowerIndex X.upperIndex) i)
          ((Equiv.swap X.lowerIndex X.upperIndex) j)
      simpa using h.symm)
    (by
      have hfix :
          (Equiv.swap X.lowerIndex X.upperIndex)
              (S.corridor.index ⟨0, by omega⟩) =
            S.corridor.index ⟨0, by omega⟩ :=
        Equiv.swap_apply_of_ne_of_ne
          X.lowerBoundaryIndex_ne_lower X.lowerBoundaryIndex_ne_upper
      calc
        X.replacementLinkage.path
              ((Equiv.swap X.lowerIndex X.upperIndex)
                (S.corridor.index ⟨0, by omega⟩)) =
            X.replacementLinkage.path
              (S.corridor.index ⟨0, by omega⟩) :=
          congrArg X.replacementLinkage.path hfix
        _ = S.linkage.path (S.corridor.index ⟨0, by omega⟩) :=
          X.replacementLinkage_path_of_ne
            X.lowerBoundaryIndex_ne_lower X.lowerBoundaryIndex_ne_upper)
    (by
      have hfix :
          (Equiv.swap X.lowerIndex X.upperIndex)
              (S.corridor.index ⟨activeCount + 1, by omega⟩) =
            S.corridor.index ⟨activeCount + 1, by omega⟩ :=
        Equiv.swap_apply_of_ne_of_ne
          X.upperBoundaryIndex_ne_lower X.upperBoundaryIndex_ne_upper
      calc
        X.replacementLinkage.path
              ((Equiv.swap X.lowerIndex X.upperIndex)
                (S.corridor.index ⟨activeCount + 1, by omega⟩)) =
            X.replacementLinkage.path
              (S.corridor.index ⟨activeCount + 1, by omega⟩) :=
          congrArg X.replacementLinkage.path hfix
        _ =
            S.linkage.path
              (S.corridor.index ⟨activeCount + 1, by omega⟩) :=
          X.replacementLinkage_path_of_ne
            X.upperBoundaryIndex_ne_lower X.upperBoundaryIndex_ne_upper)
    (by
      intro j hj
      have hjlower := X.outsideIndex_ne_lower hj
      have hjupper := X.outsideIndex_ne_upper hj
      have hfix :
          (Equiv.swap X.lowerIndex X.upperIndex) j = j :=
        Equiv.swap_apply_of_ne_of_ne hjlower hjupper
      exact (congrArg X.replacementLinkage.path hfix).trans
        (X.replacementLinkage_path_of_ne hjlower hjupper))

@[simp] theorem successorStateSame_linkage
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (X.successorStateSame hadj).linkage = X.replacementLinkage :=
  rfl

@[simp] theorem successorStateSwap_linkage
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j)) :
    (X.successorStateSwap hadj).linkage = X.replacementLinkage :=
  rfl

theorem activeIndex_ne_lower_of_row_ne
    (X : CorridorCross S) {r : Fin activeCount}
    (hr : r ≠ X.lowerRow) :
    S.corridor.index (S.corridor.activePosition r) ≠ X.lowerIndex := by
  intro hindex
  have hposition := S.corridor.index_injective hindex
  apply hr
  apply Fin.ext
  have hval := congrArg Fin.val hposition
  simpa [AuxiliaryCorridor.activePosition] using hval

theorem activeIndex_ne_upper_of_row_ne
    (X : CorridorCross S) {r : Fin activeCount}
    (hr : r ≠ X.upperRow) :
    S.corridor.index (S.corridor.activePosition r) ≠ X.upperIndex := by
  intro hindex
  have hposition := S.corridor.index_injective hindex
  apply hr
  apply Fin.ext
  have hval := congrArg Fin.val hposition
  simpa [AuxiliaryCorridor.activePosition] using hval

@[simp] theorem successorStateSame_activePath_lower
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (X.successorStateSame hadj).corridor.activePath X.lowerRow =
      X.replacementPaths.lowerReplacement := by
  change X.replacementLinkage.path X.lowerIndex =
    X.replacementPaths.lowerReplacement
  exact X.replacementLinkage_path_lower

@[simp] theorem successorStateSame_activePath_upper
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (X.successorStateSame hadj).corridor.activePath X.upperRow =
      X.replacementPaths.upperReplacement := by
  change X.replacementLinkage.path X.upperIndex =
    X.replacementPaths.upperReplacement
  exact X.replacementLinkage_path_upper

theorem successorStateSame_activePath_of_ne
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j)
    {r : Fin activeCount}
    (hlower : r ≠ X.lowerRow) (hupper : r ≠ X.upperRow) :
    (X.successorStateSame hadj).corridor.activePath r =
      S.corridor.activePath r := by
  apply X.replacementLinkage_path_of_ne
  · exact X.activeIndex_ne_lower_of_row_ne hlower
  · exact X.activeIndex_ne_upper_of_row_ne hupper

@[simp] theorem successorStateSwap_activePath_lower
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j)) :
    (X.successorStateSwap hadj).corridor.activePath X.lowerRow =
      X.replacementPaths.upperReplacement := by
  change
    X.replacementLinkage.path
        ((Equiv.swap X.lowerIndex X.upperIndex) X.lowerIndex) =
      X.replacementPaths.upperReplacement
  rw [Equiv.swap_apply_left]
  exact X.replacementLinkage_path_upper

@[simp] theorem successorStateSwap_activePath_upper
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j)) :
    (X.successorStateSwap hadj).corridor.activePath X.upperRow =
      X.replacementPaths.lowerReplacement := by
  change
    X.replacementLinkage.path
        ((Equiv.swap X.lowerIndex X.upperIndex) X.upperIndex) =
      X.replacementPaths.lowerReplacement
  rw [Equiv.swap_apply_right]
  exact X.replacementLinkage_path_lower

theorem successorStateSwap_activePath_of_ne
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j))
    {r : Fin activeCount}
    (hlower : r ≠ X.lowerRow) (hupper : r ≠ X.upperRow) :
    (X.successorStateSwap hadj).corridor.activePath r =
      S.corridor.activePath r := by
  let i := S.corridor.index (S.corridor.activePosition r)
  have hilower : i ≠ X.lowerIndex :=
    X.activeIndex_ne_lower_of_row_ne hlower
  have hiupper : i ≠ X.upperIndex :=
    X.activeIndex_ne_upper_of_row_ne hupper
  have hfix :
      (Equiv.swap X.lowerIndex X.upperIndex) i = i :=
    Equiv.swap_apply_of_ne_of_ne hilower hiupper
  change
    X.replacementLinkage.path
        ((Equiv.swap X.lowerIndex X.upperIndex) i) =
      S.linkage.path i
  exact (congrArg X.replacementLinkage.path hfix).trans
    (X.replacementLinkage_path_of_ne hilower hiupper)

section SuccessorMeasure

variable [Fintype ι] [DecidableEq ι]

theorem lowerReplacement_edgeSet_subset_active_union_fixed
    (X : CorridorCross S) :
    X.replacementPaths.lowerReplacement.edgeSet ⊆
      S.corridor.activeEdgeSet ∪ S.fixedColumnEdgeSet := by
  classical
  intro e he
  rcases Finset.mem_union.mp
      (X.replacementPaths.lower_edgeSet_subset he) with
    hlower_or_segment | hupper
  · rcases Finset.mem_union.mp hlower_or_segment with hlower | hsegment
    · exact Finset.mem_union.mpr (Or.inl <|
        Finset.mem_biUnion.mpr
          ⟨X.lowerRow, Finset.mem_univ _, by simpa [lowerPath] using hlower⟩)
    · exact Finset.mem_union.mpr (Or.inr <|
        Finset.mem_biUnion.mpr
          ⟨X.column₁, Finset.mem_univ _,
            X.segment₁_edges_subset_column (by simpa using hsegment)⟩)
  · exact Finset.mem_union.mpr (Or.inl <|
      Finset.mem_biUnion.mpr
        ⟨X.upperRow, Finset.mem_univ _, by simpa [upperPath] using hupper⟩)

theorem upperReplacement_edgeSet_subset_active_union_fixed
    (X : CorridorCross S) :
    X.replacementPaths.upperReplacement.edgeSet ⊆
      S.corridor.activeEdgeSet ∪ S.fixedColumnEdgeSet := by
  classical
  intro e he
  rcases Finset.mem_union.mp
      (X.replacementPaths.upper_edgeSet_subset he) with
    hupper_or_segment | hlower
  · rcases Finset.mem_union.mp hupper_or_segment with hupper | hsegment
    · exact Finset.mem_union.mpr (Or.inl <|
        Finset.mem_biUnion.mpr
          ⟨X.upperRow, Finset.mem_univ _, by simpa [upperPath] using hupper⟩)
    · exact Finset.mem_union.mpr (Or.inr <|
        Finset.mem_biUnion.mpr
          ⟨X.column₂, Finset.mem_univ _,
            X.segment₂_edges_subset_column (by simpa using hsegment)⟩)
  · exact Finset.mem_union.mpr (Or.inl <|
      Finset.mem_biUnion.mpr
        ⟨X.lowerRow, Finset.mem_univ _, by simpa [lowerPath] using hlower⟩)

theorem successorStateSame_activeEdgeSet_subset_union_fixed
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (X.successorStateSame hadj).corridor.activeEdgeSet ⊆
      S.corridor.activeEdgeSet ∪ S.fixedColumnEdgeSet := by
  classical
  intro e he
  rw [AuxiliaryCorridor.activeEdgeSet] at he
  rcases Finset.mem_biUnion.mp he with ⟨r, _hr, her⟩
  by_cases hlower : r = X.lowerRow
  · subst r
    rw [X.successorStateSame_activePath_lower hadj] at her
    exact X.lowerReplacement_edgeSet_subset_active_union_fixed her
  · by_cases hupper : r = X.upperRow
    · subst r
      rw [X.successorStateSame_activePath_upper hadj] at her
      exact X.upperReplacement_edgeSet_subset_active_union_fixed her
    · rw [X.successorStateSame_activePath_of_ne
        hadj hlower hupper] at her
      exact Finset.mem_union.mpr (Or.inl <|
        Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, her⟩)

theorem successorStateSwap_activeEdgeSet_subset_union_fixed
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j)) :
    (X.successorStateSwap hadj).corridor.activeEdgeSet ⊆
      S.corridor.activeEdgeSet ∪ S.fixedColumnEdgeSet := by
  classical
  intro e he
  rw [AuxiliaryCorridor.activeEdgeSet] at he
  rcases Finset.mem_biUnion.mp he with ⟨r, _hr, her⟩
  by_cases hlower : r = X.lowerRow
  · subst r
    rw [X.successorStateSwap_activePath_lower hadj] at her
    exact X.upperReplacement_edgeSet_subset_active_union_fixed her
  · by_cases hupper : r = X.upperRow
    · subst r
      rw [X.successorStateSwap_activePath_upper hadj] at her
      exact X.lowerReplacement_edgeSet_subset_active_union_fixed her
    · rw [X.successorStateSwap_activePath_of_ne
        hadj hlower hupper] at her
      exact Finset.mem_union.mpr (Or.inl <|
        Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, her⟩)

theorem s₂_not_mem_lowerReplacement (X : CorridorCross S) :
    X.s₂ ∉ X.replacementPaths.lowerReplacement.vertexSet := by
  intro hs
  exact Finset.disjoint_left.mp X.replacementPaths_nodeDisjoint
    hs X.replacementPaths.s₂_mem_upperReplacement

theorem s₁_not_mem_upperReplacement (X : CorridorCross S) :
    X.s₁ ∉ X.replacementPaths.upperReplacement.vertexSet := by
  intro hs
  exact Finset.disjoint_left.mp X.replacementPaths_nodeDisjoint
    X.replacementPaths.s₁_mem_lowerReplacement hs

theorem t₂_not_mem_lowerReplacement (X : CorridorCross S) :
    X.t₂ ∉ X.replacementPaths.lowerReplacement.vertexSet := by
  intro ht
  exact Finset.disjoint_left.mp X.replacementPaths_nodeDisjoint
    ht X.replacementPaths.t₂_mem_upperReplacement

theorem t₁_not_mem_upperReplacement (X : CorridorCross S) :
    X.t₁ ∉ X.replacementPaths.upperReplacement.vertexSet := by
  intro ht
  exact Finset.disjoint_left.mp X.replacementPaths_nodeDisjoint
    X.replacementPaths.t₁_mem_lowerReplacement ht

theorem deletedLower_edgeDisjoint_lowerReplacement
    (X : CorridorCross S) :
    X.deletedLowerInterval.EdgeDisjoint
      X.replacementPaths.lowerReplacement :=
  IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_vertex_inter_subset_singleton
    (x := X.s₁) (by
      intro v hvdel hvrep
      rcases X.deletedLowerInterval_inter_lowerReplacement_endpoint
          hvdel hvrep with hs₁ | hs₂
      · simpa [deletedLowerInterval] using hs₁
      · exact False.elim <| X.s₂_not_mem_lowerReplacement
          (by simpa [deletedLowerInterval, hs₂] using hvrep))

theorem deletedLower_edgeDisjoint_upperReplacement
    (X : CorridorCross S) :
    X.deletedLowerInterval.EdgeDisjoint
      X.replacementPaths.upperReplacement :=
  IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_vertex_inter_subset_singleton
    (x := X.s₂) (by
      intro v hvdel hvrep
      rcases X.deletedLowerInterval_inter_upperReplacement_endpoint
          hvdel hvrep with hs₁ | hs₂
      · exact False.elim <| X.s₁_not_mem_upperReplacement
          (by simpa [deletedLowerInterval, hs₁] using hvrep)
      · simpa [deletedLowerInterval] using hs₂)

theorem deletedUpper_edgeDisjoint_lowerReplacement
    (X : CorridorCross S) :
    X.deletedUpperInterval.EdgeDisjoint
      X.replacementPaths.lowerReplacement :=
  IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_vertex_inter_subset_singleton
    (x := X.t₁) (by
      intro v hvdel hvrep
      rcases X.deletedUpperInterval_inter_lowerReplacement_endpoint
          hvdel hvrep with ht₂ | ht₁
      · exact False.elim <| X.t₂_not_mem_lowerReplacement
          (by simpa [deletedUpperInterval, ht₂] using hvrep)
      · simpa [deletedUpperInterval] using ht₁)

theorem deletedUpper_edgeDisjoint_upperReplacement
    (X : CorridorCross S) :
    X.deletedUpperInterval.EdgeDisjoint
      X.replacementPaths.upperReplacement :=
  IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_vertex_inter_subset_singleton
    (x := X.t₂) (by
      intro v hvdel hvrep
      rcases X.deletedUpperInterval_inter_upperReplacement_endpoint
          hvdel hvrep with ht₂ | ht₁
      · simpa [deletedUpperInterval] using ht₂
      · exact False.elim <| X.t₁_not_mem_upperReplacement
          (by simpa [deletedUpperInterval, ht₁] using hvrep))

theorem s₁_mem_column₁ (X : CorridorCross S) :
    X.s₁ ∈ (fixedColumn X.column₁).vertexSet := by
  apply X.segment₁_subset_column
  rw [← X.orientedSegment₁_vertexSet]
  simpa using GraphPath.source_mem_vertexSet X.orientedSegment₁

theorem t₁_mem_column₁ (X : CorridorCross S) :
    X.t₁ ∈ (fixedColumn X.column₁).vertexSet := by
  apply X.segment₁_subset_column
  rw [← X.orientedSegment₁_vertexSet]
  simpa using GraphPath.target_mem_vertexSet X.orientedSegment₁

theorem s₂_mem_column₂ (X : CorridorCross S) :
    X.s₂ ∈ (fixedColumn X.column₂).vertexSet := by
  apply X.segment₂_subset_column
  rw [← X.orientedSegment₂_vertexSet]
  simpa using GraphPath.target_mem_vertexSet X.orientedSegment₂

theorem t₂_mem_column₂ (X : CorridorCross S) :
    X.t₂ ∈ (fixedColumn X.column₂).vertexSet := by
  apply X.segment₂_subset_column
  rw [← X.orientedSegment₂_vertexSet]
  simpa using GraphPath.source_mem_vertexSet X.orientedSegment₂

theorem deletedLower_edgeSet_subset_column₁_of_subset_fixed
    (X : CorridorCross S)
    (hsub :
      X.deletedLowerInterval.edgeSet ⊆ S.fixedColumnEdgeSet) :
    X.deletedLowerInterval.edgeSet ⊆
      (fixedColumn X.column₁).edgeSet := by
  apply graphPath_edgeSet_subset_member_of_pairwiseUnion
    fixedColumn
    (CorridorBumpWitness.fixedColumn_pairwise_nodeDisjoint S)
    X.column₁ X.deletedLowerInterval
  · simpa [deletedLowerInterval] using X.s₁_mem_column₁
  · simpa [CorridorRowState.fixedColumnEdgeSet] using hsub

theorem deletedLower_vertexSet_subset_column₁_of_subset_fixed
    (X : CorridorCross S)
    (hsub :
      X.deletedLowerInterval.edgeSet ⊆ S.fixedColumnEdgeSet) :
    X.deletedLowerInterval.vertexSet ⊆
      (fixedColumn X.column₁).vertexSet :=
  IndexedAuxiliaryPrefix.graphPath_vertexSet_subset_of_edgeSet_subset_of_source_mem
    (P := fixedColumn X.column₁) (Q := X.deletedLowerInterval)
    (by simpa [deletedLowerInterval] using X.s₁_mem_column₁)
    (X.deletedLower_edgeSet_subset_column₁_of_subset_fixed hsub)

theorem deletedUpper_edgeSet_subset_column₂_of_subset_fixed
    (X : CorridorCross S)
    (hsub :
      X.deletedUpperInterval.edgeSet ⊆ S.fixedColumnEdgeSet) :
    X.deletedUpperInterval.edgeSet ⊆
      (fixedColumn X.column₂).edgeSet := by
  apply graphPath_edgeSet_subset_member_of_pairwiseUnion
    fixedColumn
    (CorridorBumpWitness.fixedColumn_pairwise_nodeDisjoint S)
    X.column₂ X.deletedUpperInterval
  · simpa [deletedUpperInterval] using X.t₂_mem_column₂
  · simpa [CorridorRowState.fixedColumnEdgeSet] using hsub

theorem deletedUpper_vertexSet_subset_column₂_of_subset_fixed
    (X : CorridorCross S)
    (hsub :
      X.deletedUpperInterval.edgeSet ⊆ S.fixedColumnEdgeSet) :
    X.deletedUpperInterval.vertexSet ⊆
      (fixedColumn X.column₂).vertexSet :=
  IndexedAuxiliaryPrefix.graphPath_vertexSet_subset_of_edgeSet_subset_of_source_mem
    (P := fixedColumn X.column₂) (Q := X.deletedUpperInterval)
    (by simpa [deletedUpperInterval] using X.t₂_mem_column₂)
    (X.deletedUpper_edgeSet_subset_column₂_of_subset_fixed hsub)

/-- Lemma 2.1(2): if the cross bridges have distinct owning columns, the
lower deleted row interval cannot be covered by the fixed column family. -/
theorem deletedLower_edgeSet_not_subset_fixed_of_columns_ne
    (X : CorridorCross S) (hne : X.column₁ ≠ X.column₂) :
    ¬ X.deletedLowerInterval.edgeSet ⊆ S.fixedColumnEdgeSet := by
  intro hsub
  have hs₂col₁ :
      X.s₂ ∈ (fixedColumn X.column₁).vertexSet :=
    X.deletedLower_vertexSet_subset_column₁_of_subset_fixed hsub
      (by simpa [deletedLowerInterval] using
        GraphPath.target_mem_vertexSet X.deletedLowerInterval)
  exact Finset.disjoint_left.mp
    (CorridorBumpWitness.fixedColumn_pairwise_nodeDisjoint S hne)
    hs₂col₁ X.s₂_mem_column₂

/-- In the same-column case, the two row intervals together with the two
cross bridges would give two different simple subpaths of one column between
`s₁` and `t₁`. -/
theorem deletedIntervals_union_not_subset_fixed_same_column
    (X : CorridorCross S) (hsame : X.column₁ = X.column₂) :
    ¬ (X.deletedLowerInterval.edgeSet ∪
        X.deletedUpperInterval.edgeSet) ⊆ S.fixedColumnEdgeSet := by
  classical
  intro hall
  have hlower :
      X.deletedLowerInterval.edgeSet ⊆ S.fixedColumnEdgeSet :=
    fun e he => hall (Finset.mem_union.mpr (Or.inl he))
  have hupper :
      X.deletedUpperInterval.edgeSet ⊆ S.fixedColumnEdgeSet :=
    fun e he => hall (Finset.mem_union.mpr (Or.inr he))
  let bridgeRev := X.orientedSegment₂.reverse
  have hjoin₁ :
      X.deletedLowerInterval.target = bridgeRev.source := by
    simp [deletedLowerInterval, bridgeRev]
  have hinter₁ :
      ∀ ⦃v : V⦄,
        v ∈ X.deletedLowerInterval.vertexSet →
          v ∈ bridgeRev.vertexSet →
            v = X.deletedLowerInterval.target := by
    intro v hvdel hvbridge
    have hvlower : v ∈ X.lowerPath.vertexSet :=
      X.lowerPath.segmentOfBefore_vertexSet_subset
        X.s₁_before_s₂ hvdel
    have hvlink : v ∈ S.linkage.toPathPacking.vertexSet :=
      (S.linkage.toPathPacking.mem_vertexSet).2
        ⟨X.lowerIndex, by simpa using hvlower⟩
    have hvseg : v ∈ X.orientedSegment₂.vertexSet := by
      simpa [bridgeRev] using hvbridge
    rcases X.orientedSegment₂_clean_linkage hvseg hvlink with ht₂ | hs₂
    · exact False.elim <| X.t₂_not_mem_lower
        (by simpa [ht₂] using hvlower)
    · simpa [deletedLowerInterval] using hs₂
  let joined :=
    X.deletedLowerInterval.appendWithEqOfInterSubsetTarget
      bridgeRev hjoin₁ hinter₁
  have hjoin₂ : joined.target = X.deletedUpperInterval.source := by
    simp [joined, bridgeRev, deletedUpperInterval]
  have hinter₂ :
      ∀ ⦃v : V⦄,
        v ∈ joined.vertexSet →
          v ∈ X.deletedUpperInterval.vertexSet →
            v = joined.target := by
    intro v hvjoined hvupperDel
    have hvparts :
        v ∈ X.deletedLowerInterval.vertexSet ∪ bridgeRev.vertexSet :=
      IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_vertexSet_subset
        X.deletedLowerInterval bridgeRev hjoin₁ hinter₁ hvjoined
    have hvupper : v ∈ X.upperPath.vertexSet :=
      X.upperPath.segmentOfBefore_vertexSet_subset
        X.t₂_before_t₁ hvupperDel
    rcases Finset.mem_union.mp hvparts with hvlowerDel | hvbridge
    · have hvlower : v ∈ X.lowerPath.vertexSet :=
        X.lowerPath.segmentOfBefore_vertexSet_subset
          X.s₁_before_s₂ hvlowerDel
      exact False.elim (X.lower_upper_disjoint_at hvlower hvupper)
    · have hvlink : v ∈ S.linkage.toPathPacking.vertexSet :=
        (S.linkage.toPathPacking.mem_vertexSet).2
          ⟨X.upperIndex, by simpa using hvupper⟩
      have hvseg : v ∈ X.orientedSegment₂.vertexSet := by
        simpa [bridgeRev] using hvbridge
      rcases X.orientedSegment₂_clean_linkage hvseg hvlink with ht₂ | hs₂
      · simpa [joined, bridgeRev] using ht₂
      · exact False.elim <| X.s₂_not_mem_upper
          (by simpa [hs₂] using hvupper)
  let alternate :=
    joined.appendWithEqOfInterSubsetTarget X.deletedUpperInterval
      hjoin₂ hinter₂
  have hdelLowerColumn :
      X.deletedLowerInterval.edgeSet ⊆
        (fixedColumn X.column₁).edgeSet :=
    X.deletedLower_edgeSet_subset_column₁_of_subset_fixed hlower
  have hdelUpperColumn :
      X.deletedUpperInterval.edgeSet ⊆
        (fixedColumn X.column₁).edgeSet := by
    intro e he
    have he₂ :=
      X.deletedUpper_edgeSet_subset_column₂_of_subset_fixed hupper he
    simpa [hsame] using he₂
  have hbridgeColumn :
      bridgeRev.edgeSet ⊆ (fixedColumn X.column₁).edgeSet := by
    intro e he
    have he₂ : e ∈ X.segment₂.edgeSet := by
      simpa [bridgeRev] using he
    have hcol₂ := X.segment₂_edges_subset_column he₂
    simpa [hsame] using hcol₂
  have haltEdge :
      alternate.edgeSet ⊆ (fixedColumn X.column₁).edgeSet := by
    intro e he
    have heparts :
        e ∈ joined.edgeSet ∪ X.deletedUpperInterval.edgeSet :=
      IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_edgeSet_subset
        joined X.deletedUpperInterval hjoin₂ hinter₂ he
    rcases Finset.mem_union.mp heparts with hejoined | heupper
    · have heparts₁ :
          e ∈ X.deletedLowerInterval.edgeSet ∪ bridgeRev.edgeSet :=
        IndexedAuxiliaryPrefix.appendWithEqOfInterSubsetTarget_edgeSet_subset
          X.deletedLowerInterval bridgeRev hjoin₁ hinter₁ hejoined
      rcases Finset.mem_union.mp heparts₁ with helower | hebridge
      · exact hdelLowerColumn helower
      · exact hbridgeColumn hebridge
    · exact hdelUpperColumn heupper
  have haltVertex :
      alternate.vertexSet ⊆ (fixedColumn X.column₁).vertexSet :=
    IndexedAuxiliaryPrefix.graphPath_vertexSet_subset_of_edgeSet_subset_of_source_mem
      (P := fixedColumn X.column₁) (Q := alternate)
      (by simpa [alternate, joined, deletedLowerInterval] using
        X.s₁_mem_column₁)
      haltEdge
  have hsegment₁Vertex :
      X.orientedSegment₁.vertexSet ⊆
        (fixedColumn X.column₁).vertexSet := by
    simpa using X.segment₁_subset_column
  have hsegment₁Edge :
      X.orientedSegment₁.edgeSet ⊆
        (fixedColumn X.column₁).edgeSet := by
    simpa using X.segment₁_edges_subset_column
  have haltSubsetSegment₁ :
      alternate.vertexSet ⊆ X.orientedSegment₁.vertexSet :=
    GraphPath.vertexSet_subset_of_edgeSet_subset_same_endpoints
      (fixedColumn X.column₁) alternate X.orientedSegment₁
      haltVertex haltEdge hsegment₁Vertex hsegment₁Edge
      (by simp [alternate, joined, bridgeRev, deletedLowerInterval])
      (by simp [alternate, joined, bridgeRev, deletedUpperInterval])
  have hs₂Alternate : X.s₂ ∈ alternate.vertexSet := by
    apply
      GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        joined X.deletedUpperInterval hjoin₂ hinter₂
    apply
      GraphPath.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
        X.deletedLowerInterval bridgeRev hjoin₁ hinter₁
    simpa [deletedLowerInterval] using
      GraphPath.target_mem_vertexSet X.deletedLowerInterval
  have hs₂Segment₁ : X.s₂ ∈ X.orientedSegment₁.vertexSet :=
    haltSubsetSegment₁ hs₂Alternate
  have hs₂Segment₂ : X.s₂ ∈ X.orientedSegment₂.vertexSet := by
    simpa using GraphPath.target_mem_vertexSet X.orientedSegment₂
  exact Finset.disjoint_left.mp X.orientedSegments_nodeDisjoint
    hs₂Segment₁ hs₂Segment₂

/-- Lemma 2.1 in the exact form needed by the cross measure: at least one
of the two deleted row intervals contains an edge outside all fixed columns,
including when both bridges belong to the same column. -/
theorem deletedIntervals_union_not_subset_fixed
    (X : CorridorCross S) :
    ¬ (X.deletedLowerInterval.edgeSet ∪
        X.deletedUpperInterval.edgeSet) ⊆ S.fixedColumnEdgeSet := by
  by_cases hsame : X.column₁ = X.column₂
  · exact X.deletedIntervals_union_not_subset_fixed_same_column hsame
  · intro hall
    exact X.deletedLower_edgeSet_not_subset_fixed_of_columns_ne hsame
      (fun e he => hall (Finset.mem_union.mpr (Or.inl he)))

theorem exists_deleted_edge_not_fixed
    (X : CorridorCross S) :
    ∃ e : Sym2 V,
      e ∈ X.deletedLowerInterval.edgeSet ∪
          X.deletedUpperInterval.edgeSet ∧
        e ∉ S.fixedColumnEdgeSet :=
  Finset.not_subset.mp X.deletedIntervals_union_not_subset_fixed

theorem deletedLowerInterval_edgeSet_subset_lowerPath
    (X : CorridorCross S) :
    X.deletedLowerInterval.edgeSet ⊆ X.lowerPath.edgeSet :=
  X.lowerPath.segmentOfBefore_edgeSet_subset X.s₁_before_s₂

theorem deletedUpperInterval_edgeSet_subset_upperPath
    (X : CorridorCross S) :
    X.deletedUpperInterval.edgeSet ⊆ X.upperPath.edgeSet :=
  X.upperPath.segmentOfBefore_edgeSet_subset X.t₂_before_t₁

theorem deletedLower_edgeDisjoint_activePath_of_ne
    (X : CorridorCross S) {r : Fin activeCount}
    (hr : r ≠ X.lowerRow) :
    X.deletedLowerInterval.EdgeDisjoint
      (S.corridor.activePath r) := by
  apply IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_nodeDisjoint
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvdel hvr
  have hvlower : v ∈ X.lowerPath.vertexSet :=
    X.lowerPath.segmentOfBefore_vertexSet_subset X.s₁_before_s₂ hvdel
  exact Finset.disjoint_left.mp
    (S.corridor.path_nodeDisjoint (by
      intro hposition
      apply hr
      apply Fin.ext
      have hval := congrArg Fin.val hposition
      simpa [AuxiliaryCorridor.activePosition] using hval.symm))
    hvlower hvr

theorem deletedUpper_edgeDisjoint_activePath_of_ne
    (X : CorridorCross S) {r : Fin activeCount}
    (hr : r ≠ X.upperRow) :
    X.deletedUpperInterval.EdgeDisjoint
      (S.corridor.activePath r) := by
  apply IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_nodeDisjoint
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvdel hvr
  have hvupper : v ∈ X.upperPath.vertexSet :=
    X.upperPath.segmentOfBefore_vertexSet_subset X.t₂_before_t₁ hvdel
  exact Finset.disjoint_left.mp
    (S.corridor.path_nodeDisjoint (by
      intro hposition
      apply hr
      apply Fin.ext
      have hval := congrArg Fin.val hposition
      simpa [AuxiliaryCorridor.activePosition] using hval.symm))
    hvupper hvr

theorem deleted_edge_not_mem_successorStateSame_activeEdgeSet
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j)
    {e : Sym2 V}
    (he :
      e ∈ X.deletedLowerInterval.edgeSet ∪
        X.deletedUpperInterval.edgeSet) :
    e ∉ (X.successorStateSame hadj).corridor.activeEdgeSet := by
  classical
  intro hnew
  rw [AuxiliaryCorridor.activeEdgeSet] at hnew
  rcases Finset.mem_biUnion.mp hnew with ⟨r, _hr, her⟩
  rcases Finset.mem_union.mp he with helower | heupper
  · by_cases hlower : r = X.lowerRow
    · subst r
      rw [X.successorStateSame_activePath_lower hadj] at her
      exact Finset.disjoint_left.mp
        X.deletedLower_edgeDisjoint_lowerReplacement helower her
    · by_cases hupper : r = X.upperRow
      · subst r
        rw [X.successorStateSame_activePath_upper hadj] at her
        exact Finset.disjoint_left.mp
          X.deletedLower_edgeDisjoint_upperReplacement helower her
      · rw [X.successorStateSame_activePath_of_ne
          hadj hlower hupper] at her
        exact Finset.disjoint_left.mp
          (X.deletedLower_edgeDisjoint_activePath_of_ne hlower)
          helower her
  · by_cases hlower : r = X.lowerRow
    · subst r
      rw [X.successorStateSame_activePath_lower hadj] at her
      exact Finset.disjoint_left.mp
        X.deletedUpper_edgeDisjoint_lowerReplacement heupper her
    · by_cases hupper : r = X.upperRow
      · subst r
        rw [X.successorStateSame_activePath_upper hadj] at her
        exact Finset.disjoint_left.mp
          X.deletedUpper_edgeDisjoint_upperReplacement heupper her
      · rw [X.successorStateSame_activePath_of_ne
          hadj hlower hupper] at her
        exact Finset.disjoint_left.mp
          (X.deletedUpper_edgeDisjoint_activePath_of_ne hupper)
          heupper her

theorem deleted_edge_not_mem_successorStateSwap_activeEdgeSet
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j))
    {e : Sym2 V}
    (he :
      e ∈ X.deletedLowerInterval.edgeSet ∪
        X.deletedUpperInterval.edgeSet) :
    e ∉ (X.successorStateSwap hadj).corridor.activeEdgeSet := by
  classical
  intro hnew
  rw [AuxiliaryCorridor.activeEdgeSet] at hnew
  rcases Finset.mem_biUnion.mp hnew with ⟨r, _hr, her⟩
  rcases Finset.mem_union.mp he with helower | heupper
  · by_cases hlower : r = X.lowerRow
    · subst r
      rw [X.successorStateSwap_activePath_lower hadj] at her
      exact Finset.disjoint_left.mp
        X.deletedLower_edgeDisjoint_upperReplacement helower her
    · by_cases hupper : r = X.upperRow
      · subst r
        rw [X.successorStateSwap_activePath_upper hadj] at her
        exact Finset.disjoint_left.mp
          X.deletedLower_edgeDisjoint_lowerReplacement helower her
      · rw [X.successorStateSwap_activePath_of_ne
          hadj hlower hupper] at her
        exact Finset.disjoint_left.mp
          (X.deletedLower_edgeDisjoint_activePath_of_ne hlower)
          helower her
  · by_cases hlower : r = X.lowerRow
    · subst r
      rw [X.successorStateSwap_activePath_lower hadj] at her
      exact Finset.disjoint_left.mp
        X.deletedUpper_edgeDisjoint_upperReplacement heupper her
    · by_cases hupper : r = X.upperRow
      · subst r
        rw [X.successorStateSwap_activePath_upper hadj] at her
        exact Finset.disjoint_left.mp
          X.deletedUpper_edgeDisjoint_lowerReplacement heupper her
      · rw [X.successorStateSwap_activePath_of_ne
          hadj hlower hupper] at her
        exact Finset.disjoint_left.mp
          (X.deletedUpper_edgeDisjoint_activePath_of_ne hupper)
          heupper her

theorem deleted_edge_mem_old_activeEdgeSet
    (X : CorridorCross S) {e : Sym2 V}
    (he :
      e ∈ X.deletedLowerInterval.edgeSet ∪
        X.deletedUpperInterval.edgeSet) :
    e ∈ S.corridor.activeEdgeSet := by
  rw [AuxiliaryCorridor.activeEdgeSet]
  rcases Finset.mem_union.mp he with helower | heupper
  · exact Finset.mem_biUnion.mpr
      ⟨X.lowerRow, Finset.mem_univ _,
        X.deletedLowerInterval_edgeSet_subset_lowerPath helower⟩
  · exact Finset.mem_biUnion.mpr
      ⟨X.upperRow, Finset.mem_univ _,
        X.deletedUpperInterval_edgeSet_subset_upperPath heupper⟩

theorem successorStateSame_rowMeasure_lt
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj i j) :
    (X.successorStateSame hadj).rowMeasure < S.rowMeasure := by
  classical
  rcases X.exists_deleted_edge_not_fixed with ⟨e, he, hfixed⟩
  have hlt :=
    outsideFixedMeasure_lt
      (X.successorStateSame_activeEdgeSet_subset_union_fixed hadj)
      (X.deleted_edge_mem_old_activeEdgeSet he) hfixed
      (X.deleted_edge_not_mem_successorStateSame_activeEdgeSet hadj he)
  simpa [CorridorRowState.rowMeasure,
    CorridorRowState.fixedColumnEdgeSet] using hlt

theorem successorStateSwap_rowMeasure_lt
    (X : CorridorCross S)
    (hadj :
      ∀ i j : S.linkage.Index,
        (linkageAuxGraph X.replacementLinkage).Adj i j ↔
          (linkageAuxGraph S.linkage).Adj
            ((Equiv.swap X.lowerIndex X.upperIndex) i)
            ((Equiv.swap X.lowerIndex X.upperIndex) j)) :
    (X.successorStateSwap hadj).rowMeasure < S.rowMeasure := by
  classical
  rcases X.exists_deleted_edge_not_fixed with ⟨e, he, hfixed⟩
  have hlt :=
    outsideFixedMeasure_lt
      (X.successorStateSwap_activeEdgeSet_subset_union_fixed hadj)
      (X.deleted_edge_mem_old_activeEdgeSet he) hfixed
      (X.deleted_edge_not_mem_successorStateSwap_activeEdgeSet hadj he)
  simpa [CorridorRowState.rowMeasure,
    CorridorRowState.fixedColumnEdgeSet] using hlt

end SuccessorMeasure

/-- One complete cross step either lowers the number of degree-two auxiliary
vertices, or returns a canonical corridor state with strictly smaller row
measure.  Both possible auxiliary orders of the switched rows are handled,
and the measure proof includes the case where the two bridges belong to the
same fixed column. -/
theorem step_degree_drop_or_smaller_state
    (X : CorridorCross S)
    [Fintype V] [Fintype ι] [DecidableEq ι] :
    linkageAuxDegreeTwoCount X.replacementLinkage <
        linkageAuxDegreeTwoCount S.linkage ∨
      ∃ S' : CorridorRowState original activeCount ι fixedColumn,
        S'.rowMeasure < S.rowMeasure := by
  rcases X.degree_drop_or_auxiliary_equivalent with
    hdrop | hsame | hswap
  · exact Or.inl hdrop
  · exact Or.inr
      ⟨X.successorStateSame hsame,
        X.successorStateSame_rowMeasure_lt hsame⟩
  · exact Or.inr
      ⟨X.successorStateSwap hswap,
        X.successorStateSwap_rowMeasure_lt hswap⟩

end CorridorCross

/-- A common corridor contains a cross when a Figure-8 witness exists. -/
def HasCorridorCross
    (S : CorridorRowState original activeCount ι fixedColumn) : Prop :=
  Nonempty (CorridorCross S)

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
