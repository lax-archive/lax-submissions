import Lax17Proofs.Source.AppendixA3DeletableEdge
import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Linked subsets of a scaled cut-well-linked set

This file gives the scaled cut-well-linked analogue of the edge-well-linked
form of Theorem 4.21 in `Section46`.
-/

namespace SimpleGraph
namespace Section46


open Finset

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

namespace ScaledEdgeWellLinkedIn

/-- A scaled cut-well-linked set supplies an exact edge-disjoint packing once
the requested cardinality is strictly below the scaled terminal-side bound.

The strict inequality uses `r - 1`, so this is the natural-number ceiling
form of the ratio bound rather than a lossy floor form. -/
theorem exists_exact_edgePathPacking [Fintype V]
    {C Terminals S T : Finset V} {alphaNum alphaDen r : ℕ}
    (hwell : ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hdisj : Disjoint S T)
    (hratio : alphaDen * (r - 1) < alphaNum * min S.card T.card) :
    ∃ P : EdgePathPacking G S T, P.card = r ∧ P.StaysIn C := by
  classical
  apply AppendixA3DeletableEdge.exists_exact_edgePathPacking_of_cut_lower_bound
      (G := G) (C := C) (T := S) (Gamma := T)
      (subset_trans hS hwell.2.2.1) (subset_trans hT hwell.2.2.1) hdisj
  intro X Y hcover hXY hSX hTY
  have hXC : X ⊆ C := by
    intro v hv
    rw [← hcover]
    exact mem_union_left Y hv
  have hYC : Y ⊆ C := by
    intro v hv
    rw [← hcover]
    exact mem_union_right X hv
  have hS_inter : S ⊆ X ∩ Terminals := by
    intro v hv
    exact mem_inter.mpr ⟨hSX hv, hS hv⟩
  have hT_inter : T ⊆ Y ∩ Terminals := by
    intro v hv
    exact mem_inter.mpr ⟨hTY hv, hT hv⟩
  have hmin : min S.card T.card ≤
      min (X ∩ Terminals).card (Y ∩ Terminals).card := by
    exact min_le_min (card_le_card hS_inter) (card_le_card hT_inter)
  have hscaled := hwell.2.2.2 X Y hXC hYC hcover hXY
  rw [← Section44.edgeBoundary_eq_edgeMenger] at *
  by_contra hnot
  have hboundary : (Section44.edgeBoundary G X Y).card ≤ r - 1 := by
    omega
  have hratio' :
      alphaNum * min S.card T.card ≤
        alphaDen * (Section44.edgeBoundary G X Y).card :=
    (Nat.mul_le_mul_left alphaNum hmin).trans hscaled
  have := hratio'.trans (Nat.mul_le_mul_left alphaDen hboundary)
  omega

end ScaledEdgeWellLinkedIn

/-- The scaled cut-well-linked form of Theorem 4.21 without an equal-cardinality
hypothesis on the selected subsets.

If `T1 ∪ T2` is `alphaNum / alphaDen` cut-well-linked, each side is
node-well-linked, and both sides contain at least `kappa` terminals, then
the selected subsets are linked whenever
`2 * Delta * alphaDen * |T1'| ≤ alphaNum * kappa`. -/
theorem theorem421_linkedSubsets_scaledEdgeWellLinked_minCard
    [Fintype V]
    {C T1 T2 T1' T2' : Finset V}
    {Delta kappa alphaNum alphaDen : ℕ}
    (hdegree : MaxDegreeAtMost G Delta)
    (halpha_pos : 0 < alphaNum) (halpha_le : alphaNum ≤ alphaDen)
    (hdisj : Disjoint T1 T2)
    (hT1card : kappa ≤ T1.card) (hT2card : kappa ≤ T2.card)
    (hwell : ScaledEdgeWellLinkedIn G C (T1 ∪ T2) alphaNum alphaDen)
    (hT1node : NodeWellLinkedIn G C T1)
    (hT2node : NodeWellLinkedIn G C T2)
    (hT1' : T1' ⊆ T1) (hT2' : T2' ⊆ T2)
    (hsmall : 2 * Delta * alphaDen * T1'.card ≤ alphaNum * kappa) :
    NodeLinkedIn G C T1' T2' := by
  classical
  have hT1'C : T1' ⊆ C := subset_trans hT1' hT1node.1
  have hT2'C : T2' ⊆ C := subset_trans hT2' hT2node.1
  have hT1'T2' : Disjoint T1' T2' := hdisj.mono hT1' hT2'
  refine nodeLinkedIn_of_induced_separator_lower_bound
      (G := G) (C := C) (A := T1') (B := T2')
      hT1'C hT2'C hT1'T2' ?_
  intro A B X hA hB hsep
  let k := min A.card B.card
  by_contra hnot
  have hXlt : X.card < k := Nat.lt_of_not_ge hnot
  have hkA : k ≤ A.card := Nat.min_le_left A.card B.card
  have hkB : k ≤ B.card := Nat.min_le_right A.card B.card
  rcases Finset.exists_subset_card_eq hkA with ⟨A0, hA0sub, hA0card⟩
  rcases Finset.exists_subset_card_eq hkB with ⟨B0, hB0sub, hB0card⟩
  have hA0T1' : A0 ⊆ T1' := subset_trans hA0sub hA
  have hB0T2' : B0 ⊆ T2' := subset_trans hB0sub hB
  have hA0T1 : A0 ⊆ T1 := subset_trans hA0T1' hT1'
  have hB0T2 : B0 ⊆ T2 := subset_trans hB0T2' hT2'
  have hA0C : A0 ⊆ C := subset_trans hA0T1 hT1node.1
  have hB0C : B0 ⊆ C := subset_trans hB0T2 hT2node.1
  have hsep0 : STSeparator (inducedOnFinset G C) A0 B0 X := by
    intro P hP
    apply hsep P
    rcases hP with h | h
    · exact Or.inl ⟨hA0sub h.1, hB0sub h.2⟩
    · exact Or.inr ⟨hB0sub h.1, hA0sub h.2⟩
  let R1 := reachableTerminalsAfterDeleting G C X A0 T1
  let R2 := reachableTerminalsAfterDeleting G C X B0 T2
  have hR1T1 : R1 ⊆ T1 :=
    reachableTerminalsAfterDeleting.subset_terminals
      (G := G) (C := C) (X := X) (A := A0) (T := T1)
  have hR2T2 : R2 ⊆ T2 :=
    reachableTerminalsAfterDeleting.subset_terminals
      (G := G) (C := C) (X := X) (A := B0) (T := T2)
  have hR1_lower : T1.card - k ≤ R1.card := by
    exact reachableTerminalsAfterDeleting.card_ge_terminals_sub
      (G := G) (C := C) (X := X) (A := A0) (T := T1)
      hT1node hA0T1 hA0card hXlt
  have hR2_lower : T2.card - k ≤ R2.card := by
    exact reachableTerminalsAfterDeleting.card_ge_terminals_sub
      (G := G) (C := C) (X := X) (A := B0) (T := T2)
      hT2node hB0T2 hB0card hXlt
  have hA0R1 : A0 ⊆ R1 :=
    reachableTerminalsAfterDeleting.left_subset
      (G := G) (C := C) (X := X) (A := A0) (T := T1) hA0T1
  have hB0R2 : B0 ⊆ R2 :=
    reachableTerminalsAfterDeleting.left_subset
      (G := G) (C := C) (X := X) (A := B0) (T := T2) hB0T2
  have hkR1 : k ≤ R1.card := by simpa [hA0card] using card_le_card hA0R1
  have hkR2 : k ≤ R2.card := by simpa [hB0card] using card_le_card hB0R2
  have hR1_union : R1 ⊆ T1 ∪ T2 :=
    subset_trans hR1T1 (subset_union_left (s₁ := T1) (s₂ := T2))
  have hR2_union : R2 ⊆ T1 ∪ T2 :=
    subset_trans hR2T2 (subset_union_right (s₁ := T1) (s₂ := T2))
  have hRdisj : Disjoint R1 R2 := hdisj.mono hR1T1 hR2T2
  have hk_le_T1' : k ≤ T1'.card :=
    hkA.trans (card_le_card hA)
  have hsmall_k :
      2 * Delta * alphaDen * k ≤ alphaNum * kappa := by
    exact (Nat.mul_le_mul_left (2 * Delta * alphaDen) hk_le_T1').trans hsmall
  have hratio :
      alphaDen * ((Delta * X.card + 1) - 1) <
        alphaNum * min R1.card R2.card := by
    simp only [Nat.add_sub_cancel]
    by_cases hDelta : Delta = 0
    · subst Delta
      simp only [Nat.zero_mul, Nat.mul_zero]
      have hk_pos : 0 < k := Nat.zero_lt_of_lt hXlt
      exact Nat.mul_pos halpha_pos (hk_pos.trans_le (le_min hkR1 hkR2))
    · have hDelta_pos : 0 < Delta := Nat.pos_of_ne_zero hDelta
      have halphaDen_pos : 0 < alphaDen := lt_of_lt_of_le halpha_pos halpha_le
      have hcoef_pos : 0 < alphaDen * Delta := Nat.mul_pos halphaDen_pos hDelta_pos
      have hDXlt : alphaDen * Delta * X.card < alphaDen * Delta * k :=
        Nat.mul_lt_mul_of_pos_left hXlt hcoef_pos
      have halpha_le_coef : alphaNum ≤ alphaDen * Delta := by
        calc
          alphaNum ≤ alphaDen := halpha_le
          _ = alphaDen * 1 := by simp
          _ ≤ alphaDen * Delta := Nat.mul_le_mul_left alphaDen hDelta_pos
      have halphaK_le : alphaNum * k ≤ alphaDen * Delta * k :=
        Nat.mul_le_mul_right k halpha_le_coef
      have hsum :
          alphaDen * Delta * X.card + alphaNum * k < alphaNum * kappa := by
        have hadd :
            alphaDen * Delta * X.card + alphaNum * k <
              alphaDen * Delta * k + alphaDen * Delta * k :=
          Nat.add_lt_add_of_lt_of_le hDXlt halphaK_le
        have hdouble :
            alphaDen * Delta * k + alphaDen * Delta * k =
              2 * Delta * alphaDen * k := by ring
        rw [hdouble] at hadd
        exact hadd.trans_le hsmall_k
      have hkappa : k ≤ kappa := by
        by_contra hknot
        have hkap_le_k : kappa ≤ k := Nat.le_of_not_ge hknot
        have : alphaNum * kappa ≤ alphaNum * k :=
          Nat.mul_le_mul_left alphaNum hkap_le_k
        omega
      have hsub :
          alphaDen * Delta * X.card < alphaNum * (kappa - k) := by
        rw [Nat.mul_sub_left_distrib]
        omega
      have hfinal := hsub.trans_le (Nat.mul_le_mul_left alphaNum
        (le_min
          ((Nat.sub_le_sub_right hT1card k).trans hR1_lower)
          ((Nat.sub_le_sub_right hT2card k).trans hR2_lower)))
      simpa [Nat.mul_assoc] using hfinal
  rcases hwell.exists_exact_edgePathPacking
      hR1_union hR2_union hRdisj hratio with ⟨Q, hQcard, hQstay⟩
  have hQlarge : Delta * X.card < Q.card := by
    rw [hQcard]
    omega
  rcases EdgePathPacking.exists_path_vertexSet_disjoint_of_card_gt_degree_mul
      (G := G) (S := R1) (T := R2) (X := X) (Δ := Delta)
      Q hdegree hRdisj hQlarge with ⟨i, havoid⟩
  have hconn := Q.connects i
  have hstay := hQstay i
  have hreachQ := reachable_in_deleted_of_path_avoids
      (G := G) (C := C) (X := X) (Q.path i) hstay havoid
  rcases hconn with h | h
  · have hsource_notX : (Q.path i).source ∉ X := by
      intro hx
      exact Finset.disjoint_left.mp havoid
        (GraphPath.source_mem_vertexSet (Q.path i)) hx
    have htarget_notX : (Q.path i).target ∉ X := by
      intro hx
      exact Finset.disjoint_left.mp havoid
        (GraphPath.target_mem_vertexSet (Q.path i)) hx
    rcases reachableTerminalsAfterDeleting.exists_reachable_of_mem_of_not_mem_deleted
        (G := G) (C := C) (X := X) (A := A0) (T := T1)
        hA0C h.1 hsource_notX with ⟨a, haA, haCX, hreachA⟩
    rcases reachableTerminalsAfterDeleting.exists_reachable_of_mem_of_not_mem_deleted
        (G := G) (C := C) (X := X) (A := B0) (T := T2)
        hB0C h.2 htarget_notX with ⟨b, hbB, _hbCX, hreachB⟩
    have hreachAB :
        (inducedOnFinset G (C \ X)).Reachable a b :=
      (hreachA.trans hreachQ).trans hreachB.symm
    exact not_separator_of_reachable_avoiding
      (G := G) (C := C) (X := X) (A := A0) (B := B0)
      hsep0 haA hbB haCX hreachAB
  · have hsource_notX : (Q.path i).source ∉ X := by
      intro hx
      exact Finset.disjoint_left.mp havoid
        (GraphPath.source_mem_vertexSet (Q.path i)) hx
    have htarget_notX : (Q.path i).target ∉ X := by
      intro hx
      exact Finset.disjoint_left.mp havoid
        (GraphPath.target_mem_vertexSet (Q.path i)) hx
    rcases reachableTerminalsAfterDeleting.exists_reachable_of_mem_of_not_mem_deleted
        (G := G) (C := C) (X := X) (A := A0) (T := T1)
        hA0C h.2 htarget_notX with ⟨a, haA, haCX, hreachA⟩
    rcases reachableTerminalsAfterDeleting.exists_reachable_of_mem_of_not_mem_deleted
        (G := G) (C := C) (X := X) (A := B0) (T := T2)
        hB0C h.1 hsource_notX with ⟨b, hbB, _hbCX, hreachB⟩
    have hreachAB :
        (inducedOnFinset G (C \ X)).Reachable a b :=
      (hreachA.trans hreachQ.symm).trans hreachB.symm
    exact not_separator_of_reachable_avoiding
      (G := G) (C := C) (X := X) (A := A0) (B := B0)
      hsep0 haA hbB haCX hreachAB

/-- Compatibility form of the scaled Theorem 4.21 statement for equal-size
selected subsets.  The equality is unnecessary because `NodeLinkedIn` routes
the minimum cardinality of every selected pair. -/
theorem theorem421_linkedSubsets_scaledEdgeWellLinked
    [Fintype V]
    {C T1 T2 T1' T2' : Finset V}
    {Delta kappa alphaNum alphaDen : ℕ}
    (hdegree : MaxDegreeAtMost G Delta)
    (halpha_pos : 0 < alphaNum) (halpha_le : alphaNum ≤ alphaDen)
    (hdisj : Disjoint T1 T2)
    (hT1card : kappa ≤ T1.card) (hT2card : kappa ≤ T2.card)
    (hwell : ScaledEdgeWellLinkedIn G C (T1 ∪ T2) alphaNum alphaDen)
    (hT1node : NodeWellLinkedIn G C T1)
    (hT2node : NodeWellLinkedIn G C T2)
    (hT1' : T1' ⊆ T1) (hT2' : T2' ⊆ T2)
    (_hcard_eq : T1'.card = T2'.card)
    (hsmall : 2 * Delta * alphaDen * T1'.card ≤ alphaNum * kappa) :
    NodeLinkedIn G C T1' T2' :=
  theorem421_linkedSubsets_scaledEdgeWellLinked_minCard
    (G := G) (C := C) (T1 := T1) (T2 := T2)
    (T1' := T1') (T2' := T2') (Delta := Delta) (kappa := kappa)
    (alphaNum := alphaNum) (alphaDen := alphaDen)
    hdegree halpha_pos halpha_le hdisj hT1card hT2card hwell
    hT1node hT2node hT1' hT2' hsmall

end Section46
end SimpleGraph

end Lax17Proofs
