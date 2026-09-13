import Lax17Proofs.Source.MaderCoreRemoval
import Lax17Proofs.Source.MaderDangerBalance

namespace Lax17Proofs

universe u v w

/-!
# The minimal dangerous cover in the irreducible Mader case

This module formalizes Sections 4.3 and the initial counting part of 4.4 in
Frank's proof.  Neighbors are vertex endpoints, while all inequalities at the
center count named edge copies, so parallel copies retain their multiplicity.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A minimum-cardinality subfamily of `ambient` covering `ground`. -/
def FinsetFamilyIsMinimumCover {α : Type*} [DecidableEq α]
    (family ambient : Finset (Finset α)) (ground : Finset α) : Prop :=
  family ⊆ ambient ∧ FinsetFamilyCovers family ground ∧
    ∀ other ⊆ ambient, FinsetFamilyCovers other ground →
      family.card ≤ other.card

/-- A finite cover has a minimum-cardinality subcover, with the minimum
property retained for later replacement arguments. -/
theorem exists_minimum_finsetFamilyCover
    {α : Type*} [DecidableEq α]
    {ambient : Finset (Finset α)} {ground : Finset α}
    (hcover : FinsetFamilyCovers ambient ground) :
    ∃ family, FinsetFamilyIsMinimumCover family ambient ground := by
  classical
  let candidates := ambient.powerset.filter fun family =>
    FinsetFamilyCovers family ground
  have hnonempty : candidates.Nonempty := by
    refine ⟨ambient, ?_⟩
    simp [candidates, hcover]
  rcases Finset.exists_min_image candidates Finset.card hnonempty with
    ⟨family, hfamily, hminimum⟩
  have hdata : family ⊆ ambient ∧ FinsetFamilyCovers family ground := by
    simpa [candidates] using hfamily
  refine ⟨family, hdata.1, hdata.2, ?_⟩
  intro other hsub hother
  exact hminimum other (by simp [candidates, hsub, hother])

theorem FinsetFamilyIsMinimumCover.isMinimalCover
    {α : Type*} [DecidableEq α]
    {family ambient : Finset (Finset α)} {ground : Finset α}
    (h : FinsetFamilyIsMinimumCover family ambient ground) :
    FinsetFamilyIsMinimalCover family ground := by
  refine ⟨h.2.1, ?_⟩
  intro member hmember herase
  have hsub : family.erase member ⊆ ambient :=
    (Finset.erase_subset member family).trans h.1
  have hle := h.2.2 (family.erase member) hsub herase
  have hlt := Finset.card_erase_lt_of_mem hmember
  omega

/-- Two distinct members of a minimum cover cannot be replaced by their union
when that union is also an allowed ambient member. -/
theorem FinsetFamilyIsMinimumCover.union_not_mem_ambient
    {α : Type*} [DecidableEq α]
    {family ambient : Finset (Finset α)} {ground X Y : Finset α}
    (h : FinsetFamilyIsMinimumCover family ambient ground)
    (hX : X ∈ family) (hY : Y ∈ family) (hXY : X ≠ Y) :
    X ∪ Y ∉ ambient := by
  classical
  intro hUnion
  let replacement := insert (X ∪ Y) ((family.erase X).erase Y)
  have hreplacementSub : replacement ⊆ ambient := by
    intro Z hZ
    simp only [replacement, Finset.mem_insert] at hZ
    rcases hZ with rfl | hZ
    · exact hUnion
    · exact h.1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hZ))
  have hreplacementCover : FinsetFamilyCovers replacement ground := by
    intro a ha
    rcases Finset.mem_biUnion.mp (h.2.1 ha) with ⟨Z, hZ, haZ⟩
    by_cases hZX : Z = X
    · subst Z
      exact Finset.mem_biUnion.mpr ⟨X ∪ Y, by simp [replacement],
        Finset.mem_union_left Y haZ⟩
    by_cases hZY : Z = Y
    · subst Z
      exact Finset.mem_biUnion.mpr ⟨X ∪ Y, by simp [replacement],
        Finset.mem_union_right X haZ⟩
    exact Finset.mem_biUnion.mpr
      ⟨Z, by simp [replacement, hZX, hZY, hZ], haZ⟩
  have hYerase : Y ∈ family.erase X := Finset.mem_erase.mpr ⟨hXY.symm, hY⟩
  have hcardEraseX : (family.erase X).card = family.card - 1 := by
    rw [Finset.card_erase_of_mem hX]
  have hcardEraseY : ((family.erase X).erase Y).card = family.card - 2 := by
    rw [Finset.card_erase_of_mem hYerase, hcardEraseX]
    omega
  have hfamilyTwo : 2 ≤ family.card := by
    have : 1 < family.card := Finset.one_lt_card.mpr ⟨X, hX, Y, hY, hXY⟩
    omega
  have hreplacementCard : replacement.card ≤ family.card - 1 := by
    have hinsert := Finset.card_insert_le (X ∪ Y) ((family.erase X).erase Y)
    calc
      replacement.card ≤ ((family.erase X).erase Y).card + 1 := by
        simpa [replacement] using hinsert
      _ = family.card - 1 := by rw [hcardEraseY]; omega
  have hminimum := h.2.2 replacement hreplacementSub hreplacementCover
  omega

/-- The set of other endpoints of named edge copies incident with `s`. -/
noncomputable def centerNeighbors (H : FiniteEdgeIndexedGraph W) (s : W) :
    Finset W := by
  classical
  exact (H.incidentEdges s).image (H.otherEndpointAt s)

@[simp] theorem mem_centerNeighbors (H : FiniteEdgeIndexedGraph W)
    {s u : W} :
    u ∈ H.centerNeighbors s ↔
      ∃ e ∈ H.incidentEdges s, H.otherEndpointAt s e = u := by
  classical
  simp [centerNeighbors]

theorem centerNeighbors_subset_ground (H : FiniteEdgeIndexedGraph W) (s : W) :
    H.centerNeighbors s ⊆ Finset.univ.erase s := by
  intro u hu
  rcases H.mem_centerNeighbors.mp hu with ⟨e, he, rfl⟩
  exact Finset.mem_erase.mpr ⟨H.otherEndpointAt_ne_center he, Finset.mem_univ _⟩

/-- All dangerous sets which contain a fixed anchor neighbor. -/
noncomputable def dangerousAnchorFamily (H : FiniteEdgeIndexedGraph W)
    (s t : W) : Finset (Finset W) := by
  classical
  exact Finset.univ.filter fun X => H.MaderDangerous s X ∧ t ∈ X

@[simp] theorem mem_dangerousAnchorFamily
    (H : FiniteEdgeIndexedGraph W) {s t : W} {X : Finset W} :
    X ∈ H.dangerousAnchorFamily s t ↔ H.MaderDangerous s X ∧ t ∈ X := by
  classical
  simp [dangerousAnchorFamily]

/-- In a counterexample, dangerous sets through the endpoint of any fixed
center edge cover every center neighbor. -/
theorem dangerousAnchorFamily_covers_centerNeighbors
    (H : FiniteEdgeIndexedGraph W) {s : W}
    (hdegree : 2 ≤ H.degree s)
    (hcounter : ∀ p : H.MaderSplitPair s, ¬ H.MaderAdmissible p)
    (e0 : H.Edge) (he0 : e0 ∈ H.incidentEdges s) :
    FinsetFamilyCovers (H.dangerousAnchorFamily s (H.otherEndpointAt s e0))
      (H.centerNeighbors s) := by
  classical
  have hcard : 1 < (H.incidentEdges s).card := by simpa [degree] using hdegree
  rcases Finset.one_lt_card.mp hcard with ⟨a, ha, b, hb, hab⟩
  have hexistsOther : ∃ f ∈ H.incidentEdges s, f ≠ e0 := by
    by_cases hae : a = e0
    · exact ⟨b, hb, fun hbe => hab (hae.trans hbe.symm)⟩
    · exact ⟨a, ha, hae⟩
  rcases hexistsOther with ⟨f0, hf0, hf0ne⟩
  intro u hu
  rcases H.mem_centerNeighbors.mp hu with ⟨e, he, rfl⟩
  by_cases heq : e = e0
  · let p := H.maderSplitPairOfIncidentCopies he0 hf0 hf0ne.symm
    rcases (H.not_maderAdmissible_iff_exists_dangerous p).mp (hcounter p) with
      ⟨X, hX, hfirst, hsecond⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨X, H.mem_dangerousAnchorFamily.mpr ⟨hX, ?_⟩, ?_⟩
    · simpa [p] using hfirst
    · simpa [heq, p] using hfirst
  · let p := H.maderSplitPairOfIncidentCopies he0 he (fun h => heq h.symm)
    rcases (H.not_maderAdmissible_iff_exists_dangerous p).mp (hcounter p) with
      ⟨X, hX, hfirst, hsecond⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨X, H.mem_dangerousAnchorFamily.mpr ⟨hX, by simpa [p] using hfirst⟩,
      by simpa [p] using hsecond⟩

private theorem edgesBetween_center_eq_incidentEdges_of_neighbors_subset
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hN : H.centerNeighbors s ⊆ X) :
    H.edgesBetween {s} X = H.incidentEdges s := by
  ext e
  rw [H.mem_edgesBetween, H.mem_incidentEdges]
  constructor
  · rintro (h | h)
    · exact Or.inl (by simpa using h.1)
    · exact Or.inr (by simpa using h.1)
  · intro he
    have heInc : e ∈ H.incidentEdges s := by simpa [H.mem_incidentEdges] using he
    have hotherN : H.otherEndpointAt s e ∈ H.centerNeighbors s :=
      H.mem_centerNeighbors.mpr ⟨e, heInc, rfl⟩
    have hotherX := hN hotherN
    rcases H.otherEndpointAt_ends heInc with h | h
    · exact Or.inl ⟨by simpa using h.1, by simpa [h.2] using hotherX⟩
    · exact Or.inr ⟨by simpa using h.1, by simpa [h.2] using hotherX⟩

theorem centerIncidentCount_eq_degree_of_neighbors_subset
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hN : H.centerNeighbors s ⊆ X) :
    H.centerIncidentCount s X = H.degree s := by
  rw [centerIncidentCount, degree,
    edgesBetween_center_eq_incidentEdges_of_neighbors_subset H hN]

/-- A dangerous set cannot contain every center neighbor when the center has
positive even degree. -/
theorem MaderDangerous.not_centerNeighbors_subset
    {H : FiniteEdgeIndexedGraph W} {s : W} {X : Finset W}
    (heven : Even (H.degree s)) (hdegree : 2 ≤ H.degree s)
    (hX : H.MaderDangerous s X) :
    ¬ H.centerNeighbors s ⊆ X := by
  intro hN
  have hcount := H.centerIncidentCount_eq_degree_of_neighbors_subset hN
  have hpartition := H.centerIncidentCount_add_compl s X
  have hhalf := H.dangerous_incident_count_le_compl heven hX
  omega

private theorem edgesBetween_compl_subset_of_pair_cover
    (H : FiniteEdgeIndexedGraph W) {s : W} {X Y : Finset W}
    (hcover : FinsetFamilyCovers ({X, Y} : Finset (Finset W))
      (H.centerNeighbors s)) :
    H.edgesBetween {s} ((Finset.univ.erase s) \ X) ⊆
      H.edgesBetween {s} Y := by
  intro e he
  rw [H.mem_edgesBetween] at he ⊢
  rcases he with he | he
  · have heInc : e ∈ H.incidentEdges s := by
      rw [H.mem_incidentEdges]
      exact Or.inl (by simpa using he.1)
    have hends := H.otherEndpointAt_ends heInc
    have hother : H.otherEndpointAt s e ∈ (Finset.univ.erase s) \ X := by
      rcases hends with h | h
      · simpa [h.2] using he.2
      · have := H.end_ne e
        simp_all
    have hneighbor : H.otherEndpointAt s e ∈ H.centerNeighbors s :=
      H.mem_centerNeighbors.mpr ⟨e, heInc, rfl⟩
    have hcovered := hcover hneighbor
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hcovered
    rcases hcovered with ⟨Z, hZ, hmem⟩
    have hY : H.otherEndpointAt s e ∈ Y := by
      rcases hZ with rfl | hZ
      · exact ((Finset.mem_sdiff.mp hother).2 hmem).elim
      · simpa [hZ] using hmem
    rcases hends with h | h
    · exact Or.inl ⟨by simpa using h.1, by simpa [h.2] using hY⟩
    · exact Or.inr ⟨by simpa using h.1, by simpa [h.2] using hY⟩
  · have heInc : e ∈ H.incidentEdges s := by
      rw [H.mem_incidentEdges]
      exact Or.inr (by simpa using he.1)
    have hends := H.otherEndpointAt_ends heInc
    have hother : H.otherEndpointAt s e ∈ (Finset.univ.erase s) \ X := by
      rcases hends with h | h
      · have := H.end_ne e
        simp_all
      · simpa [h.2] using he.2
    have hneighbor : H.otherEndpointAt s e ∈ H.centerNeighbors s :=
      H.mem_centerNeighbors.mpr ⟨e, heInc, rfl⟩
    have hcovered := hcover hneighbor
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hcovered
    rcases hcovered with ⟨Z, hZ, hmem⟩
    have hY : H.otherEndpointAt s e ∈ Y := by
      rcases hZ with rfl | hZ
      · exact ((Finset.mem_sdiff.mp hother).2 hmem).elim
      · simpa [hZ] using hmem
    rcases hends with h | h
    · exact Or.inl ⟨by simpa using h.1, by simpa [h.2] using hY⟩
    · exact Or.inr ⟨by simpa using h.1, by simpa [h.2] using hY⟩

/-- For a two-set cover through the anchor, the complement incidence count of
one member is strictly smaller than the incidence count of the other. -/
theorem centerIncidentCount_compl_lt_of_pair_cover
    (H : FiniteEdgeIndexedGraph W) {s : W} {X Y : Finset W}
    (hcover : FinsetFamilyCovers ({X, Y} : Finset (Finset W))
      (H.centerNeighbors s))
    (e0 : H.Edge) (he0 : e0 ∈ H.incidentEdges s)
    (heX : H.otherEndpointAt s e0 ∈ X)
    (heY : H.otherEndpointAt s e0 ∈ Y) :
    H.centerIncidentCount s ((Finset.univ.erase s) \ X) <
      H.centerIncidentCount s Y := by
  rw [centerIncidentCount, centerIncidentCount]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨edgesBetween_compl_subset_of_pair_cover H hcover, ?_⟩
  intro heq
  have hends := H.otherEndpointAt_ends he0
  have heRight : e0 ∈ H.edgesBetween {s} Y := by
    rw [H.mem_edgesBetween]
    rcases hends with h | h
    · exact Or.inl ⟨by simpa using h.1, by simpa [h.2] using heY⟩
    · exact Or.inr ⟨by simpa using h.1, by simpa [h.2] using heY⟩
  have heLeft : e0 ∈ H.edgesBetween {s} ((Finset.univ.erase s) \ X) :=
    heq ▸ heRight
  rw [H.mem_edgesBetween] at heLeft
  rcases heLeft with h | h <;> rcases h with ⟨_, hother⟩
  · have hends' := hends
    rcases hends' with h | h
    · exact (Finset.mem_sdiff.mp hother).2 (by simpa [h.2] using heX)
    · have := H.end_ne e0
      simp_all
  · have hends' := hends
    rcases hends' with h | h
    · have := H.end_ne e0
      simp_all
    · exact (Finset.mem_sdiff.mp hother).2 (by simpa [h.2] using heX)

/-- A minimal dangerous cover through an anchor has at least three members. -/
theorem minimal_dangerousAnchorCover_three_le_card
    (H : FiniteEdgeIndexedGraph W) {s : W}
    (heven : Even (H.degree s)) (hdegree : 2 ≤ H.degree s)
    {t : W} {family : Finset (Finset W)}
    (htNeighbor : t ∈ H.centerNeighbors s)
    (hsub : family ⊆ H.dangerousAnchorFamily s t)
    (hminimal : FinsetFamilyIsMinimalCover family (H.centerNeighbors s)) :
    3 ≤ family.card := by
  by_contra hnot
  have hle : family.card ≤ 2 := by omega
  interval_cases hcard : family.card
  · have hgroundEmpty : H.centerNeighbors s = ∅ := by
      have hfamilyEmpty : family = ∅ := Finset.card_eq_zero.mp hcard
      ext u
      constructor
      · intro hu
        have := hminimal.1 hu
        simpa [FinsetFamilyCovers, hfamilyEmpty] using this
      · simp
    have hincEmpty : H.incidentEdges s = ∅ := by
      ext e
      constructor
      · intro he
        have hneighbor := H.mem_centerNeighbors.mpr ⟨e, he, rfl⟩
        simpa [hgroundEmpty] using hneighbor
      · simp
    have : H.degree s = 0 := by simp [degree, hincEmpty]
    omega
  · rcases Finset.card_eq_one.mp hcard with ⟨X, rfl⟩
    have hXmem : X ∈ H.dangerousAnchorFamily s t := hsub (by simp)
    have hN : H.centerNeighbors s ⊆ X := by
      intro u hu
      have := hminimal.1 hu
      simpa [FinsetFamilyCovers] using this
    exact (H.mem_dangerousAnchorFamily.mp hXmem).1.not_centerNeighbors_subset
      heven hdegree hN
  · rcases Finset.card_eq_two.mp hcard with ⟨X, Y, hXY, rfl⟩
    have hXfamily : X ∈ H.dangerousAnchorFamily s t :=
      hsub (Finset.mem_insert_self X {Y})
    have hYfamily : Y ∈ H.dangerousAnchorFamily s t :=
      hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self Y))
    have hXdata := H.mem_dangerousAnchorFamily.mp hXfamily
    have hYdata := H.mem_dangerousAnchorFamily.mp
      hYfamily
    have hcover := hminimal.1
    rcases H.mem_centerNeighbors.mp htNeighbor with ⟨e0, he0, heOther⟩
    have hltXY := H.centerIncidentCount_compl_lt_of_pair_cover hcover e0 he0
      (by simpa [heOther] using hXdata.2) (by simpa [heOther] using hYdata.2)
    have hltYX := H.centerIncidentCount_compl_lt_of_pair_cover
      (X := Y) (Y := X) (by simpa [Finset.pair_comm] using hcover) e0 he0
      (by simpa [heOther] using hYdata.2) (by simpa [heOther] using hXdata.2)
    have hhalfX := H.dangerous_incident_count_le_compl heven hXdata.1
    have hhalfY := H.dangerous_incident_count_le_compl heven hYdata.1
    omega

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
