import Lax17Proofs.Source.Section43
import Lax17Proofs.Source.Exponent8.LastHitSelection

namespace Lax17Proofs

/-!
# The last-hit crossbar construction

This experimental exponent-eight module isolates the construction used in the
strengthened form of Chuzhoy--Tan Claim 5.3.  The contracted graph carries the
slicing and its incidence counts; the conclusion is a crossbar in the original
graph.  `SliceLocalizationInvariant` records exactly the provenance needed to
pass between those two representations.

The proof orients every represented `Q` path toward `X`, assigns it to the
unique bad row containing its last bad-segment hit, selects distinct owner
rows, and truncates the selected paths at those last hits.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

/-- A fixed contracted slice together with enough original-graph provenance
to construct a crossbar.

`P` and `Q` are the original perfect `A`--`B` and `A`--`X` linkages.  `Rbar`
and `Qbar` are their row and auxiliary representatives after the Section 4.2
contractions.  The fields involving `uncontractedSegment` and
`uncontractedQ` make the paper's instruction to uncontract a selected `Q`
path explicit.
-/
structure SliceLocalizationInvariant
    {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (A B X : Finset V)
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G A X)
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    {M : ℕ} (sigma : PathSlicing Rbar M) (i : Fin M) where
  /-- Original main path represented by each contracted row.  The contracted
  row family may be a proper subfamily of `P`, so this map is injective rather
  than an equivalence. -/
  rowRoot : Rbar.Index → P.Index
  rowRoot_injective : Function.Injective rowRoot
  /-- Original-graph row object used by the last-hit construction.  A
  producer may use a lifted strict segment, but the rooted Observation 4.4
  producer uses the whole fixed source row; `contracted_hit_iff_uncontracted_hit`
  then supplies the exact incidence needed for localized paths. -/
  uncontractedSegment : Rbar.Index → GraphPath G
  segment_vertexSet_subset_main :
    ∀ r : Rbar.Index,
      (uncontractedSegment r).vertexSet ⊆
        (P.path (rowRoot r)).vertexSet
  /-- Original-graph realization of every represented auxiliary path. -/
  uncontractedQ : Qbar.Index → GraphPath G
  /-- Parent path in the original `A`--`X` linkage. -/
  qParent : Qbar.Index → Q.Index
  qParent_injective : Function.Injective qParent
  uncontractedQ_vertexSet_subset_parent :
    ∀ q : Qbar.Index,
      (uncontractedQ q).vertexSet ⊆ (Q.path (qParent q)).vertexSet
  uncontractedQ_edgeSet_subset_parent :
    ∀ q : Qbar.Index,
      (uncontractedQ q).edgeSet ⊆ (Q.path (qParent q)).edgeSet
  /-- Contracted paths for which this particular slice is the localization
  slice. -/
  localizedQ : Finset Qbar.Index
  localizedQ_subset_slice :
    localizedQ ⊆ sigma.pathsInSlice Qbar i
  /-- Uncontracting preserves the pseudo-grid terminal convention. -/
  uncontractedQ_exactlyOneEndpointIn_X :
    ∀ q : Qbar.Index, (uncontractedQ q).ExactlyOneEndpointIn X
  /-- Contracted slice incidence is exactly incidence with the selected
  original row object. -/
  contracted_hit_iff_uncontracted_hit :
    ∀ {r : Rbar.Index} {q : Qbar.Index}, q ∈ localizedQ →
      (sigma.SliceSegmentIntersectsPath Qbar i r q ↔
        PathPacking.PathsIntersect
          (uncontractedSegment r) (uncontractedQ q))
  /-- Every original intersection of a localized auxiliary path with a main
  path is contained in the selected original row object.  This is tautological
  when the producer selects the whole source row. -/
  main_hit_localized :
    ∀ {r : Rbar.Index} {q : Qbar.Index} {x : V},
      q ∈ localizedQ →
      x ∈ (uncontractedQ q).vertexSet →
      x ∈ (P.path (rowRoot r)).vertexSet →
      x ∈ (uncontractedSegment r).vertexSet
  /-- The terminal endpoint in `X` is outside every main path. -/
  X_disjoint_main :
    ∀ r : Rbar.Index,
      Disjoint X (P.path (rowRoot r)).vertexSet

namespace SliceLocalizationInvariant

variable
    {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {M : ℕ} {sigma : PathSlicing Rbar M} {i : Fin M}

/-- The uncontracted union of a family of bad row segments. -/
noncomputable def badVertexSet
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) : Finset V := by
  classical
  exact bad.biUnion fun r => (L.uncontractedSegment r).vertexSet

/-- Localized contracted auxiliary paths meeting one selected bad segment. -/
noncomputable def hitQAt
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (Qset : Finset Qbar.Index) (r : Rbar.Index) :
    Finset Qbar.Index := by
  classical
  exact Qset.filter fun q =>
    q ∈ L.localizedQ ∧
      sigma.SliceSegmentIntersectsPath Qbar i r q

/-- Localized contracted auxiliary paths meeting at least one bad segment. -/
noncomputable def badHitQ
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index) :
    Finset Qbar.Index := by
  classical
  exact Qset.filter fun q =>
    q ∈ L.localizedQ ∧
      ∃ r ∈ bad, sigma.SliceSegmentIntersectsPath Qbar i r q

@[simp] theorem mem_hitQAt
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (Qset : Finset Qbar.Index) (r : Rbar.Index) (q : Qbar.Index) :
    q ∈ L.hitQAt Qset r ↔
      q ∈ Qset ∧ q ∈ L.localizedQ ∧
        sigma.SliceSegmentIntersectsPath Qbar i r q := by
  classical
  simp [hitQAt]

@[simp] theorem mem_badHitQ
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index) (q : Qbar.Index) :
    q ∈ L.badHitQ bad Qset ↔
      q ∈ Qset ∧ q ∈ L.localizedQ ∧
        ∃ r ∈ bad, sigma.SliceSegmentIntersectsPath Qbar i r q := by
  classical
  simp [badHitQ]

/-- A bad represented auxiliary path, with its membership proof retained. -/
abbrev BadHitIndex
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index) :=
  {q : Qbar.Index // q ∈ L.badHitQ bad Qset}

/-- A row belonging to the selected bad-row family. -/
abbrev BadRowIndex (bad : Finset Rbar.Index) :=
  {r : Rbar.Index // r ∈ bad}

/-- An uncontracted represented path connects its own vertex set to `X`; this
is the orientation certificate used below and avoids requiring a `Fintype`
instance for the original vertex type. -/
theorem uncontractedQ_connects_vertexSet_X
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (q : Qbar.Index) :
    (L.uncontractedQ q).Connects (L.uncontractedQ q).vertexSet X := by
  rcases (L.uncontractedQ_exactlyOneEndpointIn_X q).1 with hsource | htarget
  · exact Or.inr ⟨hsource, GraphPath.target_mem_vertexSet _⟩
  · exact Or.inl ⟨GraphPath.source_mem_vertexSet _, htarget⟩

/-- Distinct represented paths are node-disjoint because they lie on distinct
parents in the original perfect `A`--`X` linkage. -/
theorem uncontractedQ_nodeDisjoint
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    {q q' : Qbar.Index} (hne : q ≠ q') :
    GraphPath.NodeDisjoint (L.uncontractedQ q) (L.uncontractedQ q') := by
  have hparentNe : L.qParent q ≠ L.qParent q' :=
    fun heq => hne (L.qParent_injective heq)
  exact
    (Q.toPathPacking.node_disjoint hparentNe).mono
      (L.uncontractedQ_vertexSet_subset_parent q)
      (L.uncontractedQ_vertexSet_subset_parent q')

/-- A represented original `Q` path oriented toward its endpoint in `X`. -/
noncomputable def orientedQ
  (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (q : Qbar.Index) : GraphPath G :=
  (L.uncontractedQ q).orient (L.uncontractedQ_connects_vertexSet_X q)

@[simp] theorem orientedQ_vertexSet
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (q : Qbar.Index) :
    (L.orientedQ q).vertexSet = (L.uncontractedQ q).vertexSet := by
  simp [orientedQ]

theorem orientedQ_target_mem_X
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (q : Qbar.Index) :
    (L.orientedQ q).target ∈ X :=
  GraphPath.orient_target_mem _ _

/-- Every path in `badHitQ` has an uncontracted intersection with the union of
the represented bad segments. -/
theorem badHitIndex_meets_badVertexSet
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    ((L.orientedQ q.1).vertexSet ∩ L.badVertexSet bad).Nonempty := by
  classical
  rcases (L.mem_badHitQ bad Qset q.1).1 q.2 with
    ⟨_hqQset, hqLocalized, r, hrBad, hrq⟩
  have hintersects :
      PathPacking.PathsIntersect
        (L.uncontractedSegment r) (L.uncontractedQ q.1) :=
    (L.contracted_hit_iff_uncontracted_hit
      (r := r) (q := q.1) hqLocalized).1 hrq
  rcases Finset.not_disjoint_iff.1 hintersects with
    ⟨x, hxSegment, hxQ⟩
  refine ⟨x, ?_⟩
  exact Finset.mem_inter.2
    ⟨by simpa [L.orientedQ_vertexSet q.1] using hxQ,
      Finset.mem_biUnion.2 ⟨r, hrBad, hxSegment⟩⟩

/-- The unique last vertex, in the orientation toward `X`, at which a bad
represented path meets the union of bad row segments. -/
noncomputable def lastBadVertex
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) : V :=
  (L.orientedQ q.1).lastHitVertex
    (L.badVertexSet bad) (L.badHitIndex_meets_badVertexSet bad Qset q)

theorem lastBadVertex_mem_orientedQ
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    L.lastBadVertex bad Qset q ∈ (L.orientedQ q.1).vertexSet :=
  GraphPath.lastHitVertex_mem_vertexSet _ _ _

theorem lastBadVertex_mem_badVertexSet
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    L.lastBadVertex bad Qset q ∈ L.badVertexSet bad :=
  GraphPath.lastHitVertex_mem_set _ _ _

/-- A bad row containing the last bad-segment hit exists. -/
theorem exists_badRow_lastBadVertex_mem_segment
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    ∃ r : BadRowIndex bad,
      L.lastBadVertex bad Qset q ∈
        (L.uncontractedSegment r.1).vertexSet := by
  classical
  rcases Finset.mem_biUnion.1 (L.lastBadVertex_mem_badVertexSet bad Qset q) with
    ⟨r, hrBad, hr⟩
  exact ⟨⟨r, hrBad⟩, hr⟩

/-- The bad row containing the last hit of one represented auxiliary path. -/
noncomputable def lastBadRow
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    BadRowIndex bad :=
  Classical.choose (L.exists_badRow_lastBadVertex_mem_segment bad Qset q)

theorem lastBadVertex_mem_lastBadRow_segment
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    L.lastBadVertex bad Qset q ∈
      (L.uncontractedSegment (L.lastBadRow bad Qset q).1).vertexSet :=
  Classical.choose_spec
    (L.exists_badRow_lastBadVertex_mem_segment bad Qset q)

/-- Node-disjointness of the original main paths makes the bad row containing
the last hit unique. -/
theorem eq_lastBadRow_of_lastBadVertex_mem_segment
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) (r : BadRowIndex bad)
    (hr :
      L.lastBadVertex bad Qset q ∈
        (L.uncontractedSegment r.1).vertexSet) :
    r = L.lastBadRow bad Qset q := by
  apply Subtype.ext
  by_contra hne
  have hrowNe :
      L.rowRoot r.1 ≠
        L.rowRoot (L.lastBadRow bad Qset q).1 := by
    intro heq
    exact hne (L.rowRoot_injective heq)
  have hdisjoint :=
    P.toPathPacking.node_disjoint hrowNe
  exact Finset.disjoint_left.1 hdisjoint
    (L.segment_vertexSet_subset_main r.1 hr)
    (L.segment_vertexSet_subset_main
      (L.lastBadRow bad Qset q).1
      (L.lastBadVertex_mem_lastBadRow_segment bad Qset q))

/-- The owner row is genuinely hit in the contracted slice representation. -/
theorem lastBadRow_mem_hitQAt
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    q.1 ∈ L.hitQAt Qset (L.lastBadRow bad Qset q).1 := by
  classical
  rcases (L.mem_badHitQ bad Qset q.1).1 q.2 with
    ⟨hqQset, hqLocalized, _r, _hrBad, _hrq⟩
  apply (L.mem_hitQAt Qset (L.lastBadRow bad Qset q).1 q.1).2
  refine ⟨hqQset, hqLocalized, ?_⟩
  apply
    (L.contracted_hit_iff_uncontracted_hit
      (r := (L.lastBadRow bad Qset q).1) (q := q.1)
      hqLocalized).2
  rw [PathPacking.PathsIntersect, Finset.not_disjoint_iff]
  exact
    ⟨L.lastBadVertex bad Qset q,
      L.lastBadVertex_mem_lastBadRow_segment bad Qset q,
      by simpa [L.orientedQ_vertexSet q.1] using
        L.lastBadVertex_mem_orientedQ bad Qset q⟩

/-- Truncate an auxiliary path after its last contact with any bad segment. -/
noncomputable def badSuffix
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) : GraphPath G :=
  (L.orientedQ q.1).cleanSuffixFromSet
    (L.badVertexSet bad) (L.badHitIndex_meets_badVertexSet bad Qset q)

@[simp] theorem badSuffix_source
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    (L.badSuffix bad Qset q).source = L.lastBadVertex bad Qset q :=
  rfl

theorem badSuffix_target_mem_X
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    (L.badSuffix bad Qset q).target ∈ X := by
  simpa [badSuffix] using L.orientedQ_target_mem_X q.1

theorem badSuffix_vertexSet_subset_uncontractedQ
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    (L.badSuffix bad Qset q).vertexSet ⊆
      (L.uncontractedQ q.1).vertexSet := by
  intro x hx
  have hxOrient :
      x ∈ (L.orientedQ q.1).vertexSet :=
    GraphPath.cleanSuffixFromSet_vertexSet_subset _ _ _ hx
  simpa [L.orientedQ_vertexSet q.1] using hxOrient

/-- The truncated suffix meets the whole union of bad segments exactly at its
source. -/
theorem badVertexSet_inter_badSuffix_eq_singleton_source
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    L.badVertexSet bad ∩ (L.badSuffix bad Qset q).vertexSet =
      {(L.badSuffix bad Qset q).source} := by
  exact GraphPath.cleanSuffixFromSet_inter_eq_singleton_source _ _ _

/-- The bounded-incidence hypotheses select `r` distinct bad owner rows and
one distinct represented path for each row. -/
theorem exists_lastHitSelection_of_bounds
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (d r : ℕ) (hd : 0 < d)
    (hcap : ∀ b ∈ bad, (L.hitQAt Qset b).card ≤ d)
    (hmany : d * r ≤ (L.badHitQ bad Qset).card) :
    Nonempty
      (LastHitSelection
        (Finset.univ : Finset (L.BadHitIndex bad Qset))
        (L.lastBadRow bad Qset) r) := by
  classical
  apply exists_lastHitSelection
      (Finset.univ : Finset (L.BadHitIndex bad Qset))
      (L.lastBadRow bad Qset) d r hd
  · intro row _hrowImage
    let fiber :=
      (Finset.univ : Finset (L.BadHitIndex bad Qset)).filter
        fun q => L.lastBadRow bad Qset q = row
    have himage :
        fiber.image Subtype.val ⊆ L.hitQAt Qset row.1 := by
      intro q hq
      rcases Finset.mem_image.1 hq with ⟨q', hq'Fiber, rfl⟩
      have howner :
          L.lastBadRow bad Qset q' = row :=
        (Finset.mem_filter.1 hq'Fiber).2
      simpa [howner] using L.lastBadRow_mem_hitQAt bad Qset q'
    calc
      ((Finset.univ : Finset (L.BadHitIndex bad Qset)).filter
          fun q => L.lastBadRow bad Qset q = row).card =
          (fiber.image Subtype.val).card := by
            rw [Finset.card_image_of_injective _ Subtype.val_injective]
      _ ≤ (L.hitQAt Qset row.1).card :=
        Finset.card_le_card himage
      _ ≤ d := hcap row.1 row.2
  · simpa only [Finset.card_univ, Fintype.card_coe] using hmany

/-- The suffix meets its owner main path exactly at the last bad hit. -/
theorem ownerMain_meets_badSuffix_exactlyAt
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    (P.path (L.rowRoot (L.lastBadRow bad Qset q).1)).MeetsExactlyAt
      (L.badSuffix bad Qset q) (L.lastBadVertex bad Qset q) := by
  classical
  rw [GraphPath.MeetsExactlyAt]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.1 hx with ⟨hxMain, hxSuffix⟩
    have hqLocalized :
        q.1 ∈ L.localizedQ :=
      ((L.mem_badHitQ bad Qset q.1).1 q.2).2.1
    have hxSegment :
        x ∈
          (L.uncontractedSegment
            (L.lastBadRow bad Qset q).1).vertexSet :=
      L.main_hit_localized hqLocalized
        (L.badSuffix_vertexSet_subset_uncontractedQ bad Qset q hxSuffix)
        hxMain
    have hxBad : x ∈ L.badVertexSet bad :=
      Finset.mem_biUnion.2
        ⟨(L.lastBadRow bad Qset q).1,
          (L.lastBadRow bad Qset q).2, hxSegment⟩
    have hxInter :
        x ∈ L.badVertexSet bad ∩
          (L.badSuffix bad Qset q).vertexSet :=
      Finset.mem_inter.2 ⟨hxBad, hxSuffix⟩
    rw [L.badVertexSet_inter_badSuffix_eq_singleton_source bad Qset q] at hxInter
    simpa using hxInter
  · intro hx
    have hxEq :
        x = L.lastBadVertex bad Qset q := by
      simpa using hx
    subst x
    apply Finset.mem_inter.2
    constructor
    · exact
        L.segment_vertexSet_subset_main
          (L.lastBadRow bad Qset q).1
          (L.lastBadVertex_mem_lastBadRow_segment bad Qset q)
    · simpa using GraphPath.source_mem_vertexSet (L.badSuffix bad Qset q)

/-- A last-hit suffix is disjoint from every other bad main path. -/
theorem badSuffix_nodeDisjoint_other_badMain
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) (r : BadRowIndex bad)
    (hne : r ≠ L.lastBadRow bad Qset q) :
      GraphPath.NodeDisjoint
      (P.path (L.rowRoot r.1)) (L.badSuffix bad Qset q) := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro x hxMain hxSuffix
  have hqLocalized :
      q.1 ∈ L.localizedQ :=
    ((L.mem_badHitQ bad Qset q.1).1 q.2).2.1
  have hxSegment :
      x ∈ (L.uncontractedSegment r.1).vertexSet :=
    L.main_hit_localized hqLocalized
      (L.badSuffix_vertexSet_subset_uncontractedQ bad Qset q hxSuffix)
      hxMain
  have hxBad : x ∈ L.badVertexSet bad :=
    Finset.mem_biUnion.2 ⟨r.1, r.2, hxSegment⟩
  have hxInter :
      x ∈ L.badVertexSet bad ∩
        (L.badSuffix bad Qset q).vertexSet :=
    Finset.mem_inter.2 ⟨hxBad, hxSuffix⟩
  rw [L.badVertexSet_inter_badSuffix_eq_singleton_source bad Qset q] at hxInter
  have hxLast : x = L.lastBadVertex bad Qset q := by
    simpa using hxInter
  have hxOwnerMain :
      x ∈
        (P.path (L.rowRoot (L.lastBadRow bad Qset q).1)).vertexSet := by
    rw [hxLast]
    exact
      L.segment_vertexSet_subset_main
        (L.lastBadRow bad Qset q).1
        (L.lastBadVertex_mem_lastBadRow_segment bad Qset q)
  have hrowNe :
      L.rowRoot r.1 ≠
        L.rowRoot (L.lastBadRow bad Qset q).1 := by
    intro heq
    exact hne (Subtype.ext (L.rowRoot_injective heq))
  exact Finset.disjoint_left.1
    (P.toPathPacking.node_disjoint hrowNe) hxMain hxOwnerMain

/-- Truncating distinct represented `Q` paths preserves node-disjointness. -/
theorem badSuffix_nodeDisjoint
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    {q q' : L.BadHitIndex bad Qset} (hne : q ≠ q') :
    GraphPath.NodeDisjoint
      (L.badSuffix bad Qset q) (L.badSuffix bad Qset q') := by
  have hvalNe : q.1 ≠ q'.1 := by
    intro heq
    exact hne (Subtype.ext heq)
  exact
    (L.uncontractedQ_nodeDisjoint hvalNe).mono
      (L.badSuffix_vertexSet_subset_uncontractedQ bad Qset q)
      (L.badSuffix_vertexSet_subset_uncontractedQ bad Qset q')

/-- Relative to its last bad hit, the other endpoint of the suffix is its
terminal endpoint in `X`. -/
@[simp] theorem badSuffix_otherEndpoint_lastBadVertex
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (q : L.BadHitIndex bad Qset) :
    (L.badSuffix bad Qset q).otherEndpoint
        (L.lastBadVertex bad Qset q) =
      (L.badSuffix bad Qset q).target := by
  simp [GraphPath.otherEndpoint]

/-- The last-hit construction, stated directly with its slice data.

The represented paths are first assigned to the unique bad row containing
their last hit.  The bounded-fibre selection then chooses `r` distinct owner
rows and distinct represented paths.  Uncontracting and truncating those paths
at their last bad hits supplies the spokes of the crossbar. -/
theorem lastHitCrossbar_direct
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (d r : ℕ)
    (hd : 0 < d)
    (hQset : Qset ⊆ L.localizedQ)
    (hcap : ∀ b ∈ bad, (L.hitQAt Qset b).card ≤ d)
    (hmany : d * r ≤ (L.badHitQ bad Qset).card) :
    Nonempty (Crossbar G A B X r) := by
  classical
  -- Membership in `badHitQ` already records localization.  Keeping this
  -- explicit hypothesis in the theorem makes the intended slice invariant
  -- visible at the call site.
  have _hlocalized :
      L.badHitQ bad Qset ⊆ L.localizedQ := by
    intro q hq
    exact ((L.mem_badHitQ bad Qset q).1 hq).2.1
  have _hQset := hQset
  rcases
      L.exists_lastHitSelection_of_bounds bad Qset d r hd hcap hmany with
    ⟨selection⟩
  let mainPath : Fin r → GraphPath G :=
    fun k => P.path (L.rowRoot (selection.row k).1)
  let spokePath : Fin r → GraphPath G :=
    fun k => L.badSuffix bad Qset (selection.preimage k)
  refine
    ⟨{
      Index := Fin r
      card_index := by simp
      mainPath := mainPath
      main_connects := ?_
      main_nodeDisjoint := ?_
      spokePath := spokePath
      spoke_connects := ?_
      spoke_nodeDisjoint := ?_
      spoke_meets_own_main := ?_
      spoke_exits_own_main := ?_
      spoke_disjoint_other_main := ?_
    }⟩
  · intro k
    exact P.toPathPacking.connects (L.rowRoot (selection.row k).1)
  · intro k l hkl
    apply P.toPathPacking.node_disjoint
    intro heq
    have hrow :
        (selection.row k).1 = (selection.row l).1 :=
      L.rowRoot_injective heq
    exact hkl (selection.row_injective (Subtype.ext hrow))
  · intro k
    apply Or.inl
    constructor
    · change
        L.lastBadVertex bad Qset (selection.preimage k) ∈
          (P.path (L.rowRoot (selection.row k).1)).vertexSet
      have hsegment :=
        L.lastBadVertex_mem_lastBadRow_segment
          bad Qset (selection.preimage k)
      rw [selection.maps_to k] at hsegment
      exact L.segment_vertexSet_subset_main (selection.row k).1 hsegment
    · exact L.badSuffix_target_mem_X bad Qset (selection.preimage k)
  · intro k l hkl
    apply L.badSuffix_nodeDisjoint bad Qset
    exact selection.preimage_injective.ne hkl
  · intro k
    let q := selection.preimage k
    refine ⟨L.lastBadVertex bad Qset q, ?_, ?_⟩
    · exact Or.inl rfl
    · have hmeet := L.ownerMain_meets_badSuffix_exactlyAt bad Qset q
      simpa [mainPath, spokePath, q, selection.maps_to k] using hmeet
  · intro k
    let q := selection.preimage k
    refine
      ⟨L.lastBadVertex bad Qset q, Or.inl rfl, ?_, ?_, ?_⟩
    · have hmeet := L.ownerMain_meets_badSuffix_exactlyAt bad Qset q
      simpa [mainPath, spokePath, q, selection.maps_to k] using hmeet
    · simpa [spokePath, q] using L.badSuffix_target_mem_X bad Qset q
    · have htargetX :
          (L.badSuffix bad Qset q).target ∈ X :=
        L.badSuffix_target_mem_X bad Qset q
      have hdisjoint :=
        L.X_disjoint_main (selection.row k).1
      have htargetNot :
          (L.badSuffix bad Qset q).target ∉
            (P.path (L.rowRoot (selection.row k).1)).vertexSet :=
        Finset.disjoint_left.1 hdisjoint htargetX
      simpa [mainPath, spokePath, q] using htargetNot
  · intro k l hkl
    apply
      L.badSuffix_nodeDisjoint_other_badMain
        bad Qset (selection.preimage l) (selection.row k)
    intro heq
    have hrows :
        selection.row k = selection.row l := by
      rw [← selection.maps_to l]
      exact heq
    exact hkl (selection.row_injective hrows)

/-- The exact LastHitCrossbar proposition.  Its proof appears below after the
finite owner-selection helper. -/
def LastHitCrossbar : Prop :=
  ∀
    {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {M : ℕ} {sigma : PathSlicing Rbar M} {i : Fin M}
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (d r : ℕ),
      0 < d →
      Qset ⊆ L.localizedQ →
      (∀ b ∈ bad, (L.hitQAt Qset b).card ≤ d) →
      d * r ≤ (L.badHitQ bad Qset).card →
      Nonempty (Crossbar G A B X r)

/-- The packaged last-hit crossbar statement used by the recursive Section 5
development. -/
theorem lastHitCrossbar : LastHitCrossbar.{u, v} := by
  intro V W instV instW G H A B X P Q
    Abar Bbar Sbar Tbar Rbar Qbar M sigma i
    L bad Qset d r hd hQset hcap hmany
  exact
    L.lastHitCrossbar_direct bad Qset d r
      hd hQset hcap hmany

end SliceLocalizationInvariant
end Exponent8
end SimpleGraph

end Lax17Proofs
