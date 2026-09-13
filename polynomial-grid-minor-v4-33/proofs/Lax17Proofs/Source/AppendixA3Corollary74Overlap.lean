import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Lemma72
import Lax17Proofs.Source.AppendixA3Corollary74

namespace Lax17Proofs

universe u v w

/-!
# Corollary 7.4 with terminal overlap

Chuzhoy applies Corollary 7.4 to the augmented boundary
`Gamma'(S) = Gamma(S) ∪ (T ∩ S)`, which need not be disjoint from `T`.
The disjoint form of Lemma 7.2 is applied here to `Gamma'(S) \ T`; the
overlap contributes at most `|T|` additional vertices.
-/

namespace SimpleGraph
namespace AppendixA3Corollary74


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A cut-well-linked set inside a region remains cut-well-linked when the
region is enlarged to the whole same-vertex graph.  The new partition may
only add crossing edges. -/
theorem scaledEdgeWellLinkedIn_univ_of_region
    {C Gamma : Finset V} {alphaNum alphaDen : ℕ}
    (hGamma :
      Section46.ScaledEdgeWellLinkedIn G C Gamma alphaNum alphaDen) :
    Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V)
      Gamma alphaNum alphaDen := by
  classical
  refine ⟨hGamma.1, hGamma.2.1, by simp, ?_⟩
  intro X Y _hX _hY hcover hdisj
  let XC := X ∩ C
  let YC := Y ∩ C
  have hXC : XC ⊆ C := Finset.inter_subset_right
  have hYC : YC ⊆ C := Finset.inter_subset_right
  have hcoverC : XC ∪ YC = C := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2
    · intro hvC
      have hvXY : v ∈ X ∪ Y := by
        rw [hcover]
        exact Finset.mem_univ v
      rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hvX, hvC⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hvY, hvC⟩)
  have hdisjC : Disjoint XC YC :=
    hdisj.mono Finset.inter_subset_left Finset.inter_subset_left
  have hXGamma : XC ∩ Gamma = X ∩ Gamma := by
    ext v
    simp only [XC, Finset.mem_inter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, hGamma.2.2.1 h.2⟩, h.2⟩
  have hYGamma : YC ∩ Gamma = Y ∩ Gamma := by
    ext v
    simp only [YC, Finset.mem_inter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, hGamma.2.2.1 h.2⟩, h.2⟩
  have hlocal :=
    hGamma.2.2.2 XC YC hXC hYC hcoverC hdisjC
  rw [hXGamma, hYGamma] at hlocal
  have hboundarySubset :
      Section44.edgeBoundary G XC YC ⊆
        Section44.edgeBoundary G X Y := by
    intro e he
    rcases ((Section44.mem_edgeBoundary (G := G) XC YC e).1 he) with
      ⟨heG, x, hx, y, hy, hxy⟩
    exact (Section44.mem_edgeBoundary (G := G) X Y e).2
      ⟨heG, x, (Finset.mem_inter.mp hx).1,
        y, (Finset.mem_inter.mp hy).1, hxy⟩
  exact hlocal.trans
    (Nat.mul_le_mul_left alphaDen
      (Finset.card_le_card hboundarySubset))

/-- Corollary 7.4 in the form actually used by Lemma 7.5.

The augmented boundary may meet `T`.  Removing the overlap gives the disjoint
set to which Lemma 7.2 applies; adding back at most `|T| = 2*kappa` vertices
gives the displayed bound. -/
theorem corollary_7_4_boundary_bound_with_terminal_overlap
    {C T Gamma : Finset V}
    {kappa d terminalNum terminalDen alphaDen : ℕ}
    (hkappa : 0 < kappa) (hd : 0 < d) (halphaDen : 0 < alphaDen)
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V)
        T terminalNum terminalDen)
    (hminimal :
      ∀ ⦃a b : V⦄, G.Adj a b →
        ¬ Section46.ScaledEdgeWellLinkedIn
          (G.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (Finset.univ : Finset V) T terminalNum terminalDen)
    (hGamma :
      Section46.ScaledEdgeWellLinkedIn G C Gamma 1 alphaDen)
    (hdegree : MaxDegreeAtMost G d) :
    Gamma.card ≤ 12 * kappa * d * alphaDen + 2 * kappa := by
  classical
  let Gamma0 := Gamma \ T
  have hGamma0Local :
      Section46.ScaledEdgeWellLinkedIn G C Gamma0 1 alphaDen :=
    hGamma.mono_terminals Finset.sdiff_subset
  have hGamma0 :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V)
        Gamma0 1 alphaDen :=
    scaledEdgeWellLinkedIn_univ_of_region hGamma0Local
  have hdisjoint : Disjoint T Gamma0 := by
    rw [Finset.disjoint_left]
    intro v hvT hvGamma0
    exact (Finset.mem_sdiff.mp hvGamma0).2 hvT
  obtain ⟨P, hPcard, hPstay⟩ :=
    AppendixA3Lemma72.lemma_7_2_edgePathPacking
      hTwell hminimal hGamma0 hdisjoint
  have hGamma0Bound :
      Gamma0.card ≤ 12 * kappa * d * alphaDen := by
    have hscaled :=
      corollary_7_4_scaled_boundary_bound_of_edgePathPacking
        (C := (Finset.univ : Finset V)) (T := T) (Gamma := Gamma0)
        (kappa := kappa) (d := d) (alphaNum := 1)
        (alphaDen := alphaDen)
        hkappa hd (by norm_num) halphaDen hTcard
        (by simp) (by simp) hdisjoint hdegree P hPstay (by
          rw [hPcard])
    simpa using hscaled
  have hcover : Gamma ⊆ Gamma0 ∪ T := by
    intro v hv
    by_cases hvT : v ∈ T
    · exact Finset.mem_union_right _ hvT
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hv, hvT⟩)
  calc
    Gamma.card ≤ (Gamma0 ∪ T).card := Finset.card_le_card hcover
    _ ≤ Gamma0.card + T.card := Finset.card_union_le _ _
    _ ≤ 12 * kappa * d * alphaDen + 2 * kappa := by
      rw [hTcard]
      omega

end AppendixA3Corollary74
end SimpleGraph

end Lax17Proofs
