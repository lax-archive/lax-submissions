import Lax17Proofs.Source.MaderSurplus

namespace Lax17Proofs

universe u v w

/-!
# The even-degree core of Mader's splitting theorem

This file isolates the part of Frank's proof used after contracting every
nontrivial tight set.  The contraction invariant is exposed as the explicit
hypothesis `MaderTightSingletons`: every proper tight subset of the
center-deleted ground set is a singleton.

All incidence sets below are finsets of named edge copies.  In particular,
parallel copies with the same other endpoint are counted separately.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The explicit invariant obtained after contracting nontrivial tight sets. -/
def MaderTightSingletons (H : FiniteEdgeIndexedGraph W) (s : W) : Prop :=
  ∀ X : Finset W, H.MaderTight s X →
    X ⊂ Finset.univ.erase s → X.card = 1

/-- Under the tight-singleton invariant, every noncenter local connectivity is
the smaller of the two singleton-cut degrees. -/
theorem localEdgeConnectivity_eq_min_degree_of_tightSingletons
    (H : FiniteEdgeIndexedGraph W) {s x y : W}
    (htight : H.MaderTightSingletons s)
    (hxs : x ≠ s) (hys : y ≠ s) (hxy : x ≠ y) :
    H.localEdgeConnectivity x y = min (H.degree x) (H.degree y) := by
  classical
  rcases H.exists_minimum_separatingCut hxy with ⟨X, hx, hy, hcut⟩
  have hleX : H.localEdgeConnectivity x y ≤ H.degree x := by
    simpa [degree, H.boundary_singleton x] using
      (H.localEdgeConnectivity_le_boundary
        (X := ({x} : Finset W)) (by simp) (by simpa using hxy.symm))
  have hleY : H.localEdgeConnectivity x y ≤ H.degree y := by
    rw [H.localEdgeConnectivity_comm x y]
    simpa [degree, H.boundary_singleton y] using
      (H.localEdgeConnectivity_le_boundary
        (X := ({y} : Finset W)) (by simp) (by simpa using hxy))
  by_cases hsX : s ∈ X
  · let Y : Finset W := Xᶜ
    have hyY : y ∈ Y := by simpa [Y] using hy
    have hxY : x ∉ Y := by simpa [Y] using hx
    have hsY : s ∉ Y := by simp [Y, hsX]
    have hYground : Y ⊆ Finset.univ.erase s := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨by
        intro hzs
        subst z
        exact hsY hz, Finset.mem_univ z⟩
    have hYproper : Y ⊂ Finset.univ.erase s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hYground, ?_⟩
      intro heq
      exact hxY (heq ▸ Finset.mem_erase.mpr ⟨hxs, Finset.mem_univ x⟩)
    have hreqLower : H.localEdgeConnectivity x y ≤
        H.centerAvoidingRequirement s Y := by
      rw [H.localEdgeConnectivity_comm x y]
      exact H.localEdgeConnectivity_le_centerAvoidingRequirement hyY hxY hxs
    have hYtight : H.MaderTight s Y := by
      refine ⟨⟨y, hyY⟩, hYground, ?_⟩
      have hreqUpper := H.centerAvoidingRequirement_le_boundary s Y
      have hboundary : (H.boundary Y).card =
          H.localEdgeConnectivity x y := by
        simpa [Y] using hcut
      omega
    have hYcard := htight Y hYtight hYproper
    have hYsingleton : Y = {y} := by
      rcases Finset.card_eq_one.mp hYcard with ⟨z, hz⟩
      have hyz : y = z := by simpa [hz] using hyY
      simpa [hyz] using hz
    have heqDegree : H.localEdgeConnectivity x y = H.degree y := by
      calc
        H.localEdgeConnectivity x y = (H.boundary Y).card := by
          simpa [Y] using hcut.symm
        _ = H.degree y := by simp [hYsingleton, degree, H.boundary_singleton y]
    omega
  · have hXground : X ⊆ Finset.univ.erase s := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨by
        intro hzs
        subst z
        exact hsX hz, Finset.mem_univ z⟩
    have hXproper : X ⊂ Finset.univ.erase s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hXground, ?_⟩
      intro heq
      exact hy (heq ▸ Finset.mem_erase.mpr ⟨hys, Finset.mem_univ y⟩)
    have hreqLower : H.localEdgeConnectivity x y ≤
        H.centerAvoidingRequirement s X :=
      H.localEdgeConnectivity_le_centerAvoidingRequirement hx hy hys
    have hXtight : H.MaderTight s X := by
      refine ⟨⟨x, hx⟩, hXground, ?_⟩
      have hreqUpper := H.centerAvoidingRequirement_le_boundary s X
      omega
    have hXcard := htight X hXtight hXproper
    have hXsingleton : X = {x} := by
      rcases Finset.card_eq_one.mp hXcard with ⟨z, hz⟩
      have hxz : x = z := by simpa [hz] using hx
      simpa [hxz] using hz
    have heqDegree : H.localEdgeConnectivity x y = H.degree x := by
      calc
        H.localEdgeConnectivity x y = (H.boundary X).card := hcut.symm
        _ = H.degree x := by simp [hXsingleton, degree, H.boundary_singleton x]
    omega

/-- The other endpoint of a named edge, when viewed from `s`.  Its value away
from edges incident with `s` is harmless; all uses below carry incidence. -/
def otherEndpointAt (H : FiniteEdgeIndexedGraph W) (s : W) (e : H.Edge) : W :=
  if H.left e = s then H.right e else H.left e

theorem otherEndpointAt_ends (H : FiniteEdgeIndexedGraph W) {s : W} {e : H.Edge}
    (he : e ∈ H.incidentEdges s) :
    (H.left e = s ∧ H.right e = H.otherEndpointAt s e) ∨
      (H.right e = s ∧ H.left e = H.otherEndpointAt s e) := by
  rw [H.mem_incidentEdges] at he
  rcases he with hleft | hright
  · exact Or.inl ⟨hleft, by simp [otherEndpointAt, hleft]⟩
  · by_cases hleft : H.left e = s
    · exact Or.inl ⟨hleft, by simp [otherEndpointAt, hleft]⟩
    · exact Or.inr ⟨hright, by simp [otherEndpointAt, hleft]⟩

theorem otherEndpointAt_ne_center
    (H : FiniteEdgeIndexedGraph W) {s : W} {e : H.Edge}
    (he : e ∈ H.incidentEdges s) : H.otherEndpointAt s e ≠ s := by
  rcases H.otherEndpointAt_ends he with h | h
  · intro hs
    exact H.end_ne e (h.1.trans (h.2.trans hs).symm)
  · intro hs
    exact H.end_ne e ((h.2.trans hs).trans h.1.symm)

/-- Named center-incident copies whose other endpoint lies in `X`. -/
noncomputable def incidentCopiesInto (H : FiniteEdgeIndexedGraph W)
    (s : W) (X : Finset W) : Finset H.Edge := by
  classical
  exact (H.incidentEdges s).filter fun e => H.otherEndpointAt s e ∈ X

@[simp] theorem mem_incidentCopiesInto
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W} {e : H.Edge} :
    e ∈ H.incidentCopiesInto s X ↔
      e ∈ H.incidentEdges s ∧ H.otherEndpointAt s e ∈ X := by
  classical
  simp [incidentCopiesInto]

theorem incidentCopiesInto_subset_incidentEdges
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset W) :
    H.incidentCopiesInto s X ⊆ H.incidentEdges s := by
  intro e he
  exact (H.mem_incidentCopiesInto.mp he).1

/-- The two named copies selected here may have the same other endpoint. -/
def maderSplitPairOfIncidentCopies
    (H : FiniteEdgeIndexedGraph W) {s : W} {e f : H.Edge}
    (he : e ∈ H.incidentEdges s) (hf : f ∈ H.incidentEdges s)
    (hef : e ≠ f) : H.MaderSplitPair s where
  first := e
  second := f
  edge_ne := hef
  firstOther := H.otherEndpointAt s e
  secondOther := H.otherEndpointAt s f
  first_ends := H.otherEndpointAt_ends he
  second_ends := H.otherEndpointAt_ends hf

/-! ## Finite minimal covers -/

/-- A finite family covers a finite ground set. -/
def FinsetFamilyCovers {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  ground ⊆ family.biUnion id

/-- No member can be erased while retaining the cover. -/
def FinsetFamilyIsMinimalCover {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  FinsetFamilyCovers family ground ∧
    ∀ member ∈ family,
      ¬ FinsetFamilyCovers (family.erase member) ground

/-- Every finite cover contains an inclusion-minimal subcover. -/
theorem exists_minimal_finsetFamilyCover
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α}
    (hcover : FinsetFamilyCovers family ground) :
    ∃ minimal ⊆ family, FinsetFamilyIsMinimalCover minimal ground := by
  classical
  let candidates := family.powerset.filter fun subfamily =>
    FinsetFamilyCovers subfamily ground
  have hcandidates : candidates.Nonempty := by
    refine ⟨family, ?_⟩
    simp [candidates, hcover]
  rcases Finset.exists_min_image candidates Finset.card hcandidates with
    ⟨minimal, hminimal, hcard⟩
  have hminimalData : minimal ⊆ family ∧
      FinsetFamilyCovers minimal ground := by
    simpa [candidates] using hminimal
  refine ⟨minimal, hminimalData.1, hminimalData.2, ?_⟩
  intro member hmember heraseCover
  have heraseCandidate : minimal.erase member ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(Finset.erase_subset _ _).trans hminimalData.1, heraseCover⟩
  have hle := hcard (minimal.erase member) heraseCandidate
  have hlt := Finset.card_erase_lt_of_mem hmember
  omega

/-- A member of an inclusion-minimal finite cover has a private ground
element.  Applied to incident-copy sets, this is a private named edge copy,
even when several copies have the same other endpoint. -/
theorem FinsetFamilyIsMinimalCover.exists_private
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground member : Finset α}
    (hminimal : FinsetFamilyIsMinimalCover family ground)
    (hmember : member ∈ family) :
    ∃ a ∈ ground, a ∈ member ∧
      ∀ other ∈ family, other ≠ member → a ∉ other := by
  classical
  have hnotCover := hminimal.2 member hmember
  simp only [FinsetFamilyCovers, Finset.not_subset] at hnotCover
  rcases hnotCover with ⟨a, haGround, haErase⟩
  have haUnion := hminimal.1 haGround
  rcases Finset.mem_biUnion.mp haUnion with ⟨owner, howner, haOwner⟩
  have hownerEq : owner = member := by
    by_contra hne
    exact haErase (Finset.mem_biUnion.mpr
      ⟨owner, Finset.mem_erase.mpr ⟨hne, howner⟩, haOwner⟩)
  subst owner
  refine ⟨a, haGround, haOwner, ?_⟩
  intro other hother hne haOther
  exact haErase (Finset.mem_biUnion.mpr
    ⟨other, Finset.mem_erase.mpr ⟨hne, hother⟩, haOther⟩)

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
