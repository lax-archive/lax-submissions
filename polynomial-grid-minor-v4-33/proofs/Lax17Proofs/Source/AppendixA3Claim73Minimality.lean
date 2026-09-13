import Lax17Proofs.Source.AppendixA3DeletableEdge

namespace Lax17Proofs

universe u v w

/-!
# Minimum-set consequences for Chuzhoy Claim 7.3

This file isolates the use of minimum cardinality in Claim 7.3.  Once cut
submodularity gives the two parts boundary at most `gamma`, minimum cardinality
forces each proper part to contain less than half of `Gamma`.
-/

namespace SimpleGraph
namespace AppendixA3Claim73


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A proper subset of the minimum Lemma 7.2 set, still having boundary at
most `gamma`, contains strictly less than half of `Gamma`. -/
theorem minimumSet_properSubset_two_mul_inter_gamma_lt
    {T Gamma M N : Finset V} {gamma : ℕ}
    (hM :
      AppendixA3DeletableEdge.IsMinimumLemma72Set G T Gamma gamma M)
    (hNM : N ⊆ M) (hcard : N.card < M.card)
    (hboundary : (Section44.clusterBoundary G N).card ≤ gamma) :
    2 * (N ∩ Gamma).card < Gamma.card := by
  classical
  by_contra hnot
  have hhalf : Gamma.card ≤ 2 * (N ∩ Gamma).card :=
    Nat.le_of_not_gt hnot
  have hdisjoint : Disjoint N T :=
    hM.disjoint_terminals.mono_left hNM
  have hcandidate :
      AppendixA3DeletableEdge.Lemma72SetConditions G T Gamma gamma N :=
    ⟨hdisjoint, hhalf, hboundary⟩
  exact (Nat.not_le_of_lt hcard) (hM.card_minimal hcandidate)

/-- If a minimum Lemma 7.2 set is split into two nonempty disjoint parts and
both new cuts have size at most `gamma`, then neither part contains half of
`Gamma`. -/
theorem minimumSet_partition_parts_two_mul_inter_gamma_lt
    {T Gamma M Z Z' : Finset V} {gamma : ℕ}
    (hM :
      AppendixA3DeletableEdge.IsMinimumLemma72Set G T Gamma gamma M)
    (hcover : Z ∪ Z' = M) (hdisjoint : Disjoint Z Z')
    (hZnonempty : Z.Nonempty) (hZ'nonempty : Z'.Nonempty)
    (hZboundary : (Section44.clusterBoundary G Z).card ≤ gamma)
    (hZ'boundary : (Section44.clusterBoundary G Z').card ≤ gamma) :
    2 * (Z ∩ Gamma).card < Gamma.card ∧
      2 * (Z' ∩ Gamma).card < Gamma.card := by
  classical
  have hZsub : Z ⊆ M := by
    intro v hv
    rw [← hcover]
    exact Finset.mem_union_left _ hv
  have hZ'sub : Z' ⊆ M := by
    intro v hv
    rw [← hcover]
    exact Finset.mem_union_right _ hv
  have hMcard : M.card = Z.card + Z'.card := by
    rw [← hcover, Finset.card_union_of_disjoint hdisjoint]
  have hZcard : Z.card < M.card := by
    have hZ'pos := Finset.card_pos.mpr hZ'nonempty
    omega
  have hZ'card : Z'.card < M.card := by
    have hZpos := Finset.card_pos.mpr hZnonempty
    omega
  exact
    ⟨minimumSet_properSubset_two_mul_inter_gamma_lt
        hM hZsub hZcard hZboundary,
      minimumSet_properSubset_two_mul_inter_gamma_lt
        hM hZ'sub hZ'card hZ'boundary⟩

end AppendixA3Claim73
end SimpleGraph

end Lax17Proofs
