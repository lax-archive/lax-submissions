import Lax17Proofs.Source.TreewidthSparsifierTheorem51Quotient
import Lax17Proofs.Source.TreewidthSparsifierThinningConcentration
import Mathlib.Order.Preorder.Finite

namespace Lax17Proofs

universe u v w

/-!
# Boundary matchings for the degree-three thinning

This file supplies the bounded-dependency reduction in Step 2 of Theorem 5.1.
In a graph of maximum degree four, every finite edge set contains a
vertex-disjoint subfamily of size at least one eighth of the original set.
The constant eight is a harmless relaxation of the source's constant.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51


variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite edge family is vertex-disjoint when distinct edges have disjoint
two-element endpoint sets. -/
def EdgeFamilyVertexDisjoint (M : Finset (Sym2 V)) : Prop :=
  (↑M : Set (Sym2 V)).Pairwise fun e f => Disjoint e.toFinset f.toFinset

theorem edgeFamilyVertexDisjoint_mono
    {M N : Finset (Sym2 V)}
    (hN : EdgeFamilyVertexDisjoint N) (hMN : M ⊆ N) :
    EdgeFamilyVertexDisjoint M := by
  intro e he f hf hef
  exact hN (hMN he) (hMN hf) hef

theorem edgeFamilyVertexDisjoint_insert
    {M : Finset (Sym2 V)} {e : Sym2 V}
    (hM : EdgeFamilyVertexDisjoint M)
    (he : ∀ f ∈ M, f ≠ e → Disjoint e.toFinset f.toFinset) :
    EdgeFamilyVertexDisjoint (insert e M) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact (hab rfl).elim
  · exact he b hb hab.symm
  · exact (he a ha hab).symm
  · exact hM ha hb hab

/-- Candidate vertex-disjoint subfamilies of `B`. -/
noncomputable def edgeDisjointCandidates
    (B : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) := by
  classical
  exact B.powerset.filter EdgeFamilyVertexDisjoint

@[simp] theorem mem_edgeDisjointCandidates
    (B M : Finset (Sym2 V)) :
    M ∈ edgeDisjointCandidates B ↔
      M ⊆ B ∧ EdgeFamilyVertexDisjoint M := by
  classical
  simp [edgeDisjointCandidates]

/-- A maximum-cardinality vertex-disjoint subfamily. -/
noncomputable def maximumEdgeDisjointSubfamily
    (B : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  have hne : (edgeDisjointCandidates B).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [edgeDisjointCandidates, EdgeFamilyVertexDisjoint]
  exact Classical.choose
    ((edgeDisjointCandidates B).exists_maximalFor
      Finset.card hne)

theorem maximumEdgeDisjointSubfamily_spec
    (B : Finset (Sym2 V)) :
    maximumEdgeDisjointSubfamily B ⊆ B ∧
      EdgeFamilyVertexDisjoint
        (maximumEdgeDisjointSubfamily B) ∧
      ∀ N ⊆ B, EdgeFamilyVertexDisjoint N →
        N.card ≤ (maximumEdgeDisjointSubfamily B).card := by
  classical
  have hne : (edgeDisjointCandidates B).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [edgeDisjointCandidates, EdgeFamilyVertexDisjoint]
  have hmax :
      MaximalFor
        (· ∈ edgeDisjointCandidates B)
        Finset.card
        (maximumEdgeDisjointSubfamily B) := by
    unfold maximumEdgeDisjointSubfamily
    exact Classical.choose_spec
      ((edgeDisjointCandidates B).exists_maximalFor
        Finset.card hne)
  have hmem :
      maximumEdgeDisjointSubfamily B ∈
        edgeDisjointCandidates B := by
    exact hmax.1
  have hspec :=
    (mem_edgeDisjointCandidates B
      (maximumEdgeDisjointSubfamily B)).mp hmem
  refine ⟨hspec.1, hspec.2, ?_⟩
  intro N hNB hN
  have hNC : N ∈ edgeDisjointCandidates B := by
    exact (mem_edgeDisjointCandidates B N).mpr ⟨hNB, hN⟩
  by_contra hnot
  have hle :
      (maximumEdgeDisjointSubfamily B).card ≤ N.card := by
    omega
  have hreverse := hmax.2 hNC hle
  exact hnot hreverse

/-- Every edge of `B` meets the endpoint set of a maximum disjoint
subfamily. -/
theorem exists_endpoint_overlap_maximum
    (B : Finset (Sym2 V)) {e : Sym2 V} (heB : e ∈ B) :
    ∃ f ∈ maximumEdgeDisjointSubfamily B,
      ¬ Disjoint e.toFinset f.toFinset := by
  classical
  let M := maximumEdgeDisjointSubfamily B
  by_contra hnone
  push_neg at hnone
  have heM : e ∉ M := by
    intro heM
    have := hnone e heM
    have hempty : e.toFinset = ∅ :=
      disjoint_self.mp this
    exact Sym2.toFinset_ne_empty e hempty
  have hinsertSubset : insert e M ⊆ B := by
    intro f hf
    simp only [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact heB
    · exact (maximumEdgeDisjointSubfamily_spec B).1 hf
  have hinsertDisjoint :
      EdgeFamilyVertexDisjoint (insert e M) := by
    apply edgeFamilyVertexDisjoint_insert
    · exact (maximumEdgeDisjointSubfamily_spec B).2.1
    · intro f hf hfe
      exact hnone f hf
  have hcard :=
    (maximumEdgeDisjointSubfamily_spec B).2.2
      (insert e M) hinsertSubset hinsertDisjoint
  rw [Finset.card_insert_of_notMem heM] at hcard
  dsimp [M] at hcard
  omega

/-- The endpoints used by an edge family. -/
noncomputable def edgeFamilyVertices
    (M : Finset (Sym2 V)) : Finset V := by
  classical
  exact M.biUnion Sym2.toFinset

theorem edgeFamilyVertices_card_le_two_mul
    (M : Finset (Sym2 V)) :
    (edgeFamilyVertices M).card ≤ 2 * M.card := by
  classical
  calc
    (edgeFamilyVertices M).card ≤
        ∑ e ∈ M, e.toFinset.card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ M, 2 := by
      exact Finset.sum_le_sum fun e _he => by
        rw [Sym2.card_toFinset]
        split <;> omega
    _ = 2 * M.card := by simp [Nat.mul_comm]

/-- In a graph of maximum degree four, every edge set contains a
vertex-disjoint subfamily of at least one eighth its size. -/
theorem card_le_eight_mul_maximumEdgeDisjointSubfamily_of_edgeSet
    (H : _root_.SimpleGraph V)
    (hdegree : MaxDegreeAtMost H 4)
    (B : Finset (Sym2 V))
    (hBH : ∀ e ∈ B, e ∈ H.edgeSet) :
    B.card ≤ 8 * (maximumEdgeDisjointSubfamily B).card := by
  classical
  let M := maximumEdgeDisjointSubfamily B
  let U := edgeFamilyVertices M
  let covered := U.biUnion fun v => H.incidenceFinset v
  have hBcovered : B ⊆ covered := by
    intro e heB
    rcases exists_endpoint_overlap_maximum B heB with
      ⟨f, hfM, hoverlap⟩
    rw [Finset.not_disjoint_iff] at hoverlap
    rcases hoverlap with ⟨v, hve, hvf⟩
    refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨f, hfM, hvf⟩
    · rw [H.mem_incidenceFinset]
      exact ⟨hBH e heB, Sym2.mem_toFinset.mp hve⟩
  have hcovered :
      covered.card ≤ 4 * U.card := by
    calc
      covered.card ≤ ∑ v ∈ U, (H.incidenceFinset v).card := by
        exact Finset.card_biUnion_le
      _ = ∑ v ∈ U, H.degree v := by
        simp [H.card_incidenceFinset_eq_degree]
      _ ≤ ∑ _v ∈ U, 4 := by
        exact Finset.sum_le_sum fun v _hv => by
          rcases hdegree v with ⟨N, hN, hcard⟩
          have hNeq : N = H.neighborFinset v := by
            ext w
            rw [H.mem_neighborFinset]
            exact hN w
          rw [← H.card_neighborFinset_eq_degree, ← hNeq]
          exact hcard
      _ = 4 * U.card := by simp [Nat.mul_comm]
  calc
    B.card ≤ covered.card := Finset.card_le_card hBcovered
    _ ≤ 4 * U.card := hcovered
    _ ≤ 4 * (2 * M.card) :=
      Nat.mul_le_mul_left 4 (edgeFamilyVertices_card_le_two_mul M)
    _ = 8 * M.card := by ring
    _ = 8 * (maximumEdgeDisjointSubfamily B).card := by rfl

/-- `edgeFinset` wrapper for
`card_le_eight_mul_maximumEdgeDisjointSubfamily_of_edgeSet`. -/
theorem card_le_eight_mul_maximumEdgeDisjointSubfamily
    (H : _root_.SimpleGraph V)
    (hdegree : MaxDegreeAtMost H 4)
    (B : Finset (Sym2 V)) (hBH : B ⊆ H.edgeFinset) :
    B.card ≤ 8 * (maximumEdgeDisjointSubfamily B).card := by
  apply card_le_eight_mul_maximumEdgeDisjointSubfamily_of_edgeSet
    H hdegree B
  intro e he
  simpa using hBH he

/-- Choose exactly `16t` vertex-disjoint edges from a finite family known
directly to lie in the graph's edge set. -/
theorem exists_vertexDisjoint_subfamily_card_of_edgeSet
    (H : _root_.SimpleGraph V)
    (hdegree : MaxDegreeAtMost H 4)
    (B : Finset (Sym2 V))
    (hBH : ∀ e ∈ B, e ∈ H.edgeSet)
    {t : ℕ} (hlarge : 128 * t ≤ B.card) :
    ∃ M : Finset (Sym2 V),
      M ⊆ B ∧ EdgeFamilyVertexDisjoint M ∧ M.card = 16 * t := by
  classical
  let M₀ := maximumEdgeDisjointSubfamily B
  have hM₀ : 16 * t ≤ M₀.card := by
    have hbound :=
      card_le_eight_mul_maximumEdgeDisjointSubfamily_of_edgeSet
        H hdegree B hBH
    dsimp [M₀]
    omega
  obtain ⟨M, hMM₀, hMcard⟩ :=
    Finset.exists_subset_card_eq hM₀
  exact
    ⟨M,
      hMM₀.trans (maximumEdgeDisjointSubfamily_spec B).1,
      edgeFamilyVertexDisjoint_mono
        (maximumEdgeDisjointSubfamily_spec B).2.1 hMM₀,
      hMcard⟩

/-- Choose exactly `16t` vertex-disjoint edges when the boundary has at least
`128t` edges. -/
theorem exists_vertexDisjoint_subfamily_card
    (H : _root_.SimpleGraph V)
    (hdegree : MaxDegreeAtMost H 4)
    (B : Finset (Sym2 V)) (hBH : B ⊆ H.edgeFinset)
    {t : ℕ} (hlarge : 128 * t ≤ B.card) :
    ∃ M : Finset (Sym2 V),
      M ⊆ B ∧ EdgeFamilyVertexDisjoint M ∧ M.card = 16 * t := by
  classical
  let M₀ := maximumEdgeDisjointSubfamily B
  have hM₀ : 16 * t ≤ M₀.card := by
    have hbound :=
      card_le_eight_mul_maximumEdgeDisjointSubfamily
        H hdegree B hBH
    dsimp [M₀]
    omega
  obtain ⟨M, hMM₀, hMcard⟩ :=
    Finset.exists_subset_card_eq hM₀
  exact
    ⟨M,
      hMM₀.trans (maximumEdgeDisjointSubfamily_spec B).1,
      edgeFamilyVertexDisjoint_mono
        (maximumEdgeDisjointSubfamily_spec B).2.1 hMM₀,
      hMcard⟩

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
