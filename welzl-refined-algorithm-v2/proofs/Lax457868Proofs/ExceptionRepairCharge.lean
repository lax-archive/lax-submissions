import Lax457868Proofs.ExceptionRepairLoop
import Lax11Proofs.CCGraph

/-! The disjoint class scans charge each CSR row at most once. -/
namespace Lax457868Proofs.ExceptionRepairCharge
open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.RepairClassScan
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
noncomputable section

lemma sum_slice_eq {start size : ℕ} {ord : ℕ → ℕ} {S : Finset ℕ}
    (h : PrefixEnumerates size (fun i => ord (start + i)) S)
    (weight : ℕ → ℕ) :
    (∑ i ∈ Finset.Ico start (start + size), weight (ord i)) =
      ∑ v ∈ S, weight v := by
  classical
  apply Finset.sum_bij (fun i _ => ord i)
  · intro i hi
    have hii := Finset.mem_Ico.mp hi
    apply (h.2 _).mp
    simp only [Stack.toList, Lax808846Proofs.Reasoning.arrOf, List.mem_map, List.mem_range]
    exact ⟨i - start, by omega, by congr 1; omega⟩
  · intro i hi j hj heq
    have hii := Finset.mem_Ico.mp hi
    have hjj := Finset.mem_Ico.mp hj
    have hsame := h.injective_on_prefix (i - start) (by omega)
      (j - start) (by omega)
      (by simpa [Nat.add_sub_of_le hii.1, Nat.add_sub_of_le hjj.1] using heq)
    omega
  · intro v hv
    have hm := (h.2 v).mpr hv
    simp only [Stack.toList, Lax808846Proofs.Reasoning.arrOf, List.mem_map, List.mem_range] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    exact ⟨start + i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
  · intro i hi
    rfl

lemma sum_class_potentials_le_csr
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (S : Finset ℕ) (hSE : S ⊆ E)
    (hseparate : ∀ u ∈ E, ∀ v ∈ E,
      trace (numericNeighborhood G) Wbase u =
        trace (numericNeighborhood G) Wbase v → u = v) :
    (∑ b ∈ S, repairClassPotential
      (classStart R.size (R.label b) + R.size (R.label b))
      (classStart R.size (R.label b)) (repairClassSlotWeight x R.ord)) ≤
      90 * (2 * edgeCount x) + 70 * n := by
  classical
  let classes := fun b => labelClass R.xs R.label (R.label b)
  let weight := fun v => 90 * (Lax11Proofs.CC.deg x v) + 70
  have hsum (b : ℕ) (hb : b ∈ S) :
      repairClassPotential
        (classStart R.size (R.label b) + R.size (R.label b))
        (classStart R.size (R.label b)) (repairClassSlotWeight x R.ord) =
      ∑ v ∈ classes b, weight v := by
    rw [repairClassPotential_eq_sum_Ico]
    exact sum_slice_eq (R.hslice _ (R.hlabel b (hSE hb))) weight
  have hpair : (S : Set ℕ).PairwiseDisjoint classes := by
    intro b hb b' hb' hne
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    have h₁ := (Finset.mem_filter.mp hv).2
    have h₂ := (Finset.mem_filter.mp hv').2
    exact hne (R.label_injective_on_exceptions hseparate b (hSE hb)
      b' (hSE hb') (h₁.symm.trans h₂))
  have hrange : S.biUnion classes ⊆ Finset.range n := by
    intro v hv
    obtain ⟨b, hb, hv⟩ := Finset.mem_biUnion.mp hv
    exact R.hxsRange (Finset.mem_filter.mp hv).1
  calc
    _ = ∑ b ∈ S, ∑ v ∈ classes b, weight v := Finset.sum_congr rfl hsum
    _ = ∑ v ∈ S.biUnion classes, weight v := (Finset.sum_biUnion hpair).symm
    _ ≤ ∑ v ∈ Finset.range n, weight v := Finset.sum_le_sum_of_subset hrange
    _ = 90 * (2 * edgeCount x) + 70 * n := by
      simp only [weight, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Lax11Proofs.CC.sum_deg R.hgraph le_rfl, R.hgraph.offset_zero,
        R.hgraph.offset_last]
      simp [Nat.mul_comm]

/-- Across all executed exceptions, the complete class-scan charge is
linear in the CSR encoding; the representative's repeated local trials
are accounted for separately by their stopped mean. -/
lemma sum_classScanCharge_le_csr
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (S : Finset ℕ) (hSE : S ⊆ E)
    (hseparate : ∀ u ∈ E, ∀ v ∈ E,
      trace (numericNeighborhood G) Wbase u =
        trace (numericNeighborhood G) Wbase v → u = v) :
    (∑ b ∈ S, classScanCharge x R.size R.label R.ord b) ≤
      156 * (2 * edgeCount x) + 117 * n := by
  have hp := sum_class_potentials_le_csr R S hSE hseparate
  have hd := Lax11Proofs.CC.sum_deg_le R.hgraph
    (fun v hv => Finset.mem_range.mp (R.hErange (hSE hv)))
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_card (hSE.trans R.hErange)
  have heq : (∑ b ∈ S, classScanCharge x R.size R.label R.ord b) =
      66 * (∑ b ∈ S, Lax11Proofs.CC.deg x b) +
      (∑ b ∈ S, repairClassPotential
        (classStart R.size (R.label b) + R.size (R.label b))
        (classStart R.size (R.label b)) (repairClassSlotWeight x R.ord)) +
      47 * S.card := by
    simp [classScanCharge, Lax11Proofs.CC.deg, Finset.sum_add_distrib,
      Finset.mul_sum]
    ring
  rw [heq]
  omega

lemma sum_classScanCharge_le_input
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (S : Finset ℕ) (hSE : S ⊆ E)
    (hseparate : ∀ u ∈ E, ∀ v ∈ E,
      trace (numericNeighborhood G) Wbase u =
        trace (numericNeighborhood G) Wbase v → u = v) :
    (∑ b ∈ S, classScanCharge x R.size R.label R.ord b) ≤
      156 * x.length := by
  have h := sum_classScanCharge_le_csr R S hSE hseparate
  have hlen := R.hgraph.length_eq
  omega

/-- Domain construction pays once for each exception row and once for its
initial representative row. Only the latter term needs averaging over the
initial random choice. -/
lemma sum_domainCharge_le
    {n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (A E : Finset ℕ) (rep : ℕ → ℕ)
    (hE : E ⊆ Finset.range n) (hrep : ∀ b ∈ E, rep b < n) :
    (∑ b ∈ E, domainCharge x G A rep b) ≤
      90 * (2 * edgeCount x) + 73 * n +
        90 * (∑ b ∈ E, Lax11Proofs.CC.deg x (rep b)) := by
  have hpoint (b : ℕ) (hb : b ∈ E) :=
    Lax457868Proofs.RepairFilterSource.repairDomainSource_cost_le
      hx A rep (Finset.mem_range.mp (hE hb)) (hrep b hb)
  have hsum := Finset.sum_le_sum (fun b hb => hpoint b hb)
  change (∑ b ∈ E, domainCharge x G A rep b) ≤
    ∑ b ∈ E, (90 * (Lax11Proofs.CC.deg x b + Lax11Proofs.CC.deg x (rep b)) + 73) at hsum
  have hd := Lax11Proofs.CC.sum_deg_le hx
    (fun v hv => Finset.mem_range.mp (hE hv))
  have hcard : E.card ≤ n := by simpa using Finset.card_le_card hE
  have heq : (∑ b ∈ E, (90 * (Lax11Proofs.CC.deg x b + Lax11Proofs.CC.deg x (rep b)) + 73)) =
      90 * (∑ b ∈ E, Lax11Proofs.CC.deg x b) +
        90 * (∑ b ∈ E, Lax11Proofs.CC.deg x (rep b)) + 73 * E.card := by
    simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  rw [heq] at hsum
  omega

end
end Lax457868Proofs.ExceptionRepairCharge
