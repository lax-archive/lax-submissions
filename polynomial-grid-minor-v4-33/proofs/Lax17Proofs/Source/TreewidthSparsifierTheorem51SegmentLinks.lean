import Lax17Proofs.Source.TreewidthSparsifierTheorem51SegmentQuotient
import Lax17Proofs.Source.TreewidthSparsifierThinningBoundary

namespace Lax17Proofs

universe u v w

/-!
# Complete physical links for the segment quotient

Chekuri--Chuzhoy, *Degree-3 Treewidth Sparsifiers*, Theorem 5.1, Step 2,
suppresses every blue subpath between consecutive red intersections.  A raw
owner-changing physical edge is only the last edge of such a suppressed arc;
retaining that single edge is not enough.  This module associates the complete
carrier-clean arc to the transition.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- The oriented path segment joining the last red predecessors of the two
endpoints of a local blue edge. -/
noncomputable def predecessorArc
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v : V}
    (hu : u ∈ (E.localBluePath z.1 z.2).vertexSet)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    GraphPath (E.recordAt z.1).layer.localGraph := by
  classical
  let Q := E.localBluePath z.1 z.2
  exact GraphPath.segmentBetween Q
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z u hu)).1
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z v hv)).1

@[simp] theorem predecessorArc_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v : V}
    (hu : u ∈ (E.localBluePath z.1 z.2).vertexSet)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    (E.predecessorArc hbudget z hu hv).source =
      E.precedingRedVertex hbudget z u hu := by
  simp [predecessorArc]

@[simp] theorem predecessorArc_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v : V}
    (hu : u ∈ (E.localBluePath z.1 z.2).vertexSet)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    (E.predecessorArc hbudget z hu hv).target =
      E.precedingRedVertex hbudget z v hv := by
  simp [predecessorArc]

theorem predecessorArc_vertexSet_subset
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v : V}
    (hu : u ∈ (E.localBluePath z.1 z.2).vertexSet)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    (E.predecessorArc hbudget z hu hv).vertexSet ⊆
      (E.localBluePath z.1 z.2).vertexSet := by
  classical
  apply GraphPath.segmentBetween_vertexSet_subset
  · exact
      (Finset.mem_filter.mp
        (E.precedingRedVertex_mem hbudget z u hu)).1
  · exact
      (Finset.mem_filter.mp
        (E.precedingRedVertex_mem hbudget z v hv)).1

theorem predecessorArc_edgeSet_subset
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v : V}
    (hu : u ∈ (E.localBluePath z.1 z.2).vertexSet)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    (E.predecessorArc hbudget z hu hv).edgeSet ⊆
      (E.localBluePath z.1 z.2).edgeSet := by
  classical
  apply GraphPath.segmentBetween_edgeSet_subset
  · exact
      (Finset.mem_filter.mp
        (E.precedingRedVertex_mem hbudget z u hu)).1
  · exact
      (Finset.mem_filter.mp
        (E.precedingRedVertex_mem hbudget z v hv)).1

/-- Consecutive blue-path vertices with distinct red predecessors have no
third red-carried vertex between those predecessors. -/
theorem predecessorArc_internally_carrier_clean
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v : V}
    (he : s(u, v) ∈ (E.localBluePath z.1 z.2).edgeSet)
    (hpne :
      E.precedingRedVertex hbudget z u
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).1 ≠
        E.precedingRedVertex hbudget z v
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).2) :
    (E.predecessorArc hbudget z
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he).1
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he).2).InternallyDisjointFromSet
      (E.redCarrierVertices hbudget) := by
  classical
  let Q := E.localBluePath z.1 z.2
  let hu := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he).1
  let hv := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he).2
  let pu := E.precedingRedVertex hbudget z u hu
  let pv := E.precedingRedVertex hbudget z v hv
  have hpuData :
      pu ∈ Q.vertexSet ∧ Q.vertexIndex pu ≤ Q.vertexIndex u ∧
        ∃ x : Fin h, E.RedCarrier hbudget pu x := by
    simpa [pu, Q, precedingRedCandidates] using
      E.precedingRedVertex_mem hbudget z u hu
  have hpvData :
      pv ∈ Q.vertexSet ∧ Q.vertexIndex pv ≤ Q.vertexIndex v ∧
        ∃ x : Fin h, E.RedCarrier hbudget pv x := by
    simpa [pv, Q, precedingRedCandidates] using
      E.precedingRedVertex_mem hbudget z v hv
  have huvNe : u ≠ v := by
    intro huv
    subst v
    exact (Q.edgeSet_subset_edgeSet he).ne rfl
  intro w hwArc hwCarrier
  have hwQ :
      w ∈ Q.vertexSet :=
    E.predecessorArc_vertexSet_subset hbudget z hu hv hwArc
  obtain ⟨xw, hwRed⟩ :=
    (E.mem_redCarrierVertices hbudget w).1 hwCarrier
  have hidxEither :
      Q.vertexIndex u < Q.vertexIndex v ∨
        Q.vertexIndex v < Q.vertexIndex u := by
    rcases lt_or_gt_of_ne
      (fun hidx =>
        huvNe (GraphPath.eq_of_vertexIndex_eq Q hu hv hidx)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hidxEither with huv | hvu
  · have huvSucc :
        Q.vertexIndex v = Q.vertexIndex u + 1 := by
      have hle := Q.edge_vertexIndex_le_succ he
      omega
    have hpuCandidateV :
        pu ∈ E.precedingRedCandidates hbudget z v := by
      simp only [precedingRedCandidates, Finset.mem_filter]
      exact ⟨hpuData.1,
        hpuData.2.1.trans (Nat.le_of_lt huv), hpuData.2.2⟩
    have hpuLePv :
        Q.vertexIndex pu ≤ Q.vertexIndex pv := by
      exact E.precedingRedVertex_maximal hbudget z v hv hpuCandidateV
    have hwBounds :
        Q.vertexIndex pu ≤ Q.vertexIndex w ∧
          Q.vertexIndex w ≤ Q.vertexIndex pv := by
      have hw' :
          w ∈
            (GraphPath.segmentBetween Q hpuData.1 hpvData.1).vertexSet := by
        simpa [predecessorArc, Q, pu, pv, hu, hv] using hwArc
      simp only [GraphPath.segmentBetween, hpuLePv, ↓reduceDIte] at hw'
      exact
        ⟨((Q.before_iff_vertexIndex_le).1
            (Q.before_of_mem_segmentOfBefore_left _ hw')).2.2,
          ((Q.before_iff_vertexIndex_le).1
            (Q.before_of_mem_segmentOfBefore_right _ hw')).2.2⟩
    by_cases hwu : Q.vertexIndex w ≤ Q.vertexIndex u
    · have hwCandidate :
          w ∈ E.precedingRedCandidates hbudget z u := by
        simp only [precedingRedCandidates, Finset.mem_filter]
        exact ⟨hwQ, hwu, ⟨xw, hwRed⟩⟩
      have hwLePu :
          Q.vertexIndex w ≤ Q.vertexIndex pu :=
        E.precedingRedVertex_maximal hbudget z u hu hwCandidate
      have hwp : w = pu :=
        GraphPath.eq_of_vertexIndex_eq Q hwQ hpuData.1
          (Nat.le_antisymm hwLePu hwBounds.1)
      exact Or.inl (by
        simpa [predecessorArc, Q, pu, pv, hu, hv] using hwp)
    · have hwvIdx : Q.vertexIndex w = Q.vertexIndex v := by
        omega
      have hwv : w = v :=
        GraphPath.eq_of_vertexIndex_eq Q hwQ hv hwvIdx
      have hpvv : pv = v := by
        exact E.precedingRedVertex_eq_self_of_carrier
          hbudget z v hv (hwv ▸ hwRed)
      exact Or.inr (by
        simpa [predecessorArc, Q, pu, pv, hu, hv] using
          hwv.trans hpvv.symm)
  · have hvuSucc :
        Q.vertexIndex u = Q.vertexIndex v + 1 := by
      have he' : s(v, u) ∈ Q.edgeSet := by
        simpa [Sym2.eq_swap] using he
      have hle := Q.edge_vertexIndex_le_succ he'
      omega
    have hpvCandidateU :
        pv ∈ E.precedingRedCandidates hbudget z u := by
      simp only [precedingRedCandidates, Finset.mem_filter]
      exact ⟨hpvData.1,
        hpvData.2.1.trans (Nat.le_of_lt hvu), hpvData.2.2⟩
    have hpvLePu :
        Q.vertexIndex pv ≤ Q.vertexIndex pu := by
      exact E.precedingRedVertex_maximal hbudget z u hu hpvCandidateU
    have hwBounds :
        Q.vertexIndex pv ≤ Q.vertexIndex w ∧
          Q.vertexIndex w ≤ Q.vertexIndex pu := by
      have hw' :
          w ∈
            (GraphPath.segmentBetween Q hpuData.1 hpvData.1).vertexSet := by
        simpa [predecessorArc, Q, pu, pv, hu, hv] using hwArc
      simp only [GraphPath.segmentBetween, Nat.not_le.mpr
        (lt_of_le_of_ne hpvLePu (Ne.symm (fun h =>
          hpne (GraphPath.eq_of_vertexIndex_eq Q hpuData.1 hpvData.1 h)))) ,
        ↓reduceDIte] at hw'
      have hwRev :
          w ∈
            (Q.segmentOfBefore
              ((Q.before_iff_vertexIndex_le).2
                ⟨hpvData.1, hpuData.1, hpvLePu⟩)).vertexSet := by
        simpa using hw'
      exact
        ⟨((Q.before_iff_vertexIndex_le).1
            (Q.before_of_mem_segmentOfBefore_left _ hwRev)).2.2,
          ((Q.before_iff_vertexIndex_le).1
            (Q.before_of_mem_segmentOfBefore_right _ hwRev)).2.2⟩
    by_cases hwv : Q.vertexIndex w ≤ Q.vertexIndex v
    · have hwCandidate :
          w ∈ E.precedingRedCandidates hbudget z v := by
        simp only [precedingRedCandidates, Finset.mem_filter]
        exact ⟨hwQ, hwv, ⟨xw, hwRed⟩⟩
      have hwLePv :
          Q.vertexIndex w ≤ Q.vertexIndex pv :=
        E.precedingRedVertex_maximal hbudget z v hv hwCandidate
      have hwp : w = pv :=
        GraphPath.eq_of_vertexIndex_eq Q hwQ hpvData.1
          (Nat.le_antisymm hwLePv hwBounds.1)
      exact Or.inr (by
        simpa [predecessorArc, Q, pu, pv, hu, hv] using hwp)
    · have hwuIdx : Q.vertexIndex w = Q.vertexIndex u := by
        omega
      have hwuEq : w = u :=
        GraphPath.eq_of_vertexIndex_eq Q hwQ hu hwuIdx
      have hpuu : pu = u := by
        exact E.precedingRedVertex_eq_self_of_carrier
          hbudget z u hu (hwuEq ▸ hwRed)
      exact Or.inl (by
        simpa [predecessorArc, Q, pu, pv, hu, hv] using
          hwuEq.trans hpuu.symm)

/-- For an oriented blue edge, if its two last red predecessors differ, the
later endpoint is itself red-carried and is the later predecessor. -/
theorem precedingRedVertex_eq_later_of_edge
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v : V}
    (he : s(u, v) ∈ (E.localBluePath z.1 z.2).edgeSet)
    (huv : (E.localBluePath z.1 z.2).Before u v)
    (hpne :
      E.precedingRedVertex hbudget z u
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).1 ≠
        E.precedingRedVertex hbudget z v
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).2) :
    E.precedingRedVertex hbudget z v
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he).2 = v := by
  classical
  let Q := E.localBluePath z.1 z.2
  let hu := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he).1
  let hv := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he).2
  let pu := E.precedingRedVertex hbudget z u hu
  let pv := E.precedingRedVertex hbudget z v hv
  have huvNe : u ≠ v := by
    intro h
    subst v
    exact (Q.edgeSet_subset_edgeSet he).ne rfl
  have huvLt : Q.vertexIndex u < Q.vertexIndex v := by
    have huvLe := ((Q.before_iff_vertexIndex_le).1 huv).2.2
    exact lt_of_le_of_ne huvLe (fun h =>
      huvNe (GraphPath.eq_of_vertexIndex_eq Q hu hv h))
  have huvSucc : Q.vertexIndex v = Q.vertexIndex u + 1 := by
    have hle := Q.edge_vertexIndex_le_succ he
    omega
  have hpuData :
      pu ∈ Q.vertexSet ∧ Q.vertexIndex pu ≤ Q.vertexIndex u ∧
        ∃ x : Fin h, E.RedCarrier hbudget pu x := by
    simpa [pu, Q, precedingRedCandidates] using
      E.precedingRedVertex_mem hbudget z u hu
  have hpvData :
      pv ∈ Q.vertexSet ∧ Q.vertexIndex pv ≤ Q.vertexIndex v ∧
        ∃ x : Fin h, E.RedCarrier hbudget pv x := by
    simpa [pv, Q, precedingRedCandidates] using
      E.precedingRedVertex_mem hbudget z v hv
  have hpuCandidateV :
      pu ∈ E.precedingRedCandidates hbudget z v := by
    simp only [precedingRedCandidates, Finset.mem_filter]
    exact ⟨hpuData.1,
      hpuData.2.1.trans (Nat.le_of_lt huvLt), hpuData.2.2⟩
  have hpuLePv : Q.vertexIndex pu ≤ Q.vertexIndex pv :=
    E.precedingRedVertex_maximal hbudget z v hv hpuCandidateV
  have hnotPvLeU : ¬ Q.vertexIndex pv ≤ Q.vertexIndex u := by
    intro hpvu
    have hpvCandidateU :
        pv ∈ E.precedingRedCandidates hbudget z u := by
      simp only [precedingRedCandidates, Finset.mem_filter]
      exact ⟨hpvData.1, hpvu, hpvData.2.2⟩
    have hpvLePu : Q.vertexIndex pv ≤ Q.vertexIndex pu :=
      E.precedingRedVertex_maximal hbudget z u hu hpvCandidateU
    have hpueq :
        pu = pv :=
      GraphPath.eq_of_vertexIndex_eq Q hpuData.1 hpvData.1
        (Nat.le_antisymm hpuLePv hpvLePu)
    exact hpne (by simpa [pu, pv, hu, hv, Q] using hpueq)
  have hpvIdx : Q.vertexIndex pv = Q.vertexIndex v := by
    omega
  exact GraphPath.eq_of_vertexIndex_eq Q hpvData.1 hv hpvIdx

/-- On one local blue path, the unordered pair of consecutive red
predecessors determines the owner-changing physical edge uniquely. -/
theorem edge_eq_of_predecessor_pair_of_before_left
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v a b : V}
    (he : s(u, v) ∈ (E.localBluePath z.1 z.2).edgeSet)
    (huv : (E.localBluePath z.1 z.2).Before u v)
    (hf : s(a, b) ∈ (E.localBluePath z.1 z.2).edgeSet)
    (heNe :
      E.precedingRedVertex hbudget z u
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).1 ≠
        E.precedingRedVertex hbudget z v
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).2)
    (hfNe :
      E.precedingRedVertex hbudget z a
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) hf).1 ≠
        E.precedingRedVertex hbudget z b
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) hf).2)
    (hpairs :
      s(E.precedingRedVertex hbudget z u
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).1,
        E.precedingRedVertex hbudget z v
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).2) =
      s(E.precedingRedVertex hbudget z a
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) hf).1,
        E.precedingRedVertex hbudget z b
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) hf).2)) :
    s(u, v) = s(a, b) := by
  classical
  let Q := E.localBluePath z.1 z.2
  let hu := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he).1
  let hv := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he).2
  let ha := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q hf).1
  let hb := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q hf).2
  let pu := E.precedingRedVertex hbudget z u hu
  let pv := E.precedingRedVertex hbudget z v hv
  let pa := E.precedingRedVertex hbudget z a ha
  let pb := E.precedingRedVertex hbudget z b hb
  have hpu : pu ∈ Q.vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z u hu)).1
  have hpv : pv ∈ Q.vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z v hv)).1
  have hpa : pa ∈ Q.vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z a ha)).1
  have hpb : pb ∈ Q.vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z b hb)).1
  have habOrder := GraphPath.before_total_of_mem Q ha hb
  rcases habOrder with hab | hba
  · have hpvV : pv = v :=
      E.precedingRedVertex_eq_later_of_edge hbudget z he huv heNe
    have hpbB : pb = b :=
      E.precedingRedVertex_eq_later_of_edge hbudget z hf hab hfNe
    have hpuLtPv : Q.vertexIndex pu < Q.vertexIndex pv := by
      have hpuLe :
          Q.vertexIndex pu ≤ Q.vertexIndex pv := by
        have hcandidate :
            pu ∈ E.precedingRedCandidates hbudget z v := by
          have hpuData := Finset.mem_filter.mp
            (E.precedingRedVertex_mem hbudget z u hu)
          simp only [precedingRedCandidates, Finset.mem_filter]
          exact ⟨hpuData.1,
            hpuData.2.1.trans
              (((Q.before_iff_vertexIndex_le).1 huv).2.2),
            hpuData.2.2⟩
        exact E.precedingRedVertex_maximal hbudget z v hv hcandidate
      exact lt_of_le_of_ne hpuLe (fun h =>
        heNe (GraphPath.eq_of_vertexIndex_eq Q hpu hpv h))
    have hpaLtPb : Q.vertexIndex pa < Q.vertexIndex pb := by
      have hpaLe :
          Q.vertexIndex pa ≤ Q.vertexIndex pb := by
        have hcandidate :
            pa ∈ E.precedingRedCandidates hbudget z b := by
          have hpaData := Finset.mem_filter.mp
            (E.precedingRedVertex_mem hbudget z a ha)
          simp only [precedingRedCandidates, Finset.mem_filter]
          exact ⟨hpaData.1,
            hpaData.2.1.trans
              (((Q.before_iff_vertexIndex_le).1 hab).2.2),
            hpaData.2.2⟩
        exact E.precedingRedVertex_maximal hbudget z b hb hcandidate
      exact lt_of_le_of_ne hpaLe (fun h =>
        hfNe (GraphPath.eq_of_vertexIndex_eq Q hpa hpb h))
    rw [Sym2.eq_iff] at hpairs
    rcases hpairs with ⟨hupa, hvpb⟩ | ⟨hupb, hvpa⟩
    · change pu = pa at hupa
      change pv = pb at hvpb
      have hvb : v = b := by
        simpa [pu, pv, pa, pb, hpvV, hpbB] using hvpb
      have hf' : s(a, v) ∈ Q.edgeSet := by
        simpa [hvb] using hf
      have hab' : Q.Before a v := by
        simpa [hvb] using hab
      have huvNe : u ≠ v := (Q.edgeSet_subset_edgeSet he).ne
      have havNe : a ≠ v := (Q.edgeSet_subset_edgeSet hf').ne
      have hua : u = a :=
        GraphPath.backward_edge_unique Q
          he huv huvNe hf' hab' havNe
      simpa [hua, hvb]
    · change pu = pb at hupb
      change pv = pa at hvpa
      have hcontra :
          Q.vertexIndex pv < Q.vertexIndex pu := by
        rw [← hvpa, ← hupb] at hpaLtPb
        exact hpaLtPb
      omega
  · have hpvV : pv = v :=
      E.precedingRedVertex_eq_later_of_edge hbudget z he huv heNe
    have hpaA : pa = a := by
      have hf' : s(b, a) ∈ Q.edgeSet := by
        simpa [Sym2.eq_swap] using hf
      exact E.precedingRedVertex_eq_later_of_edge
        hbudget z hf' hba (by simpa [Sym2.eq_swap] using hfNe.symm)
    have hpuLtPv : Q.vertexIndex pu < Q.vertexIndex pv := by
      have hle :
          Q.vertexIndex pu ≤ Q.vertexIndex pv := by
        have hdata := Finset.mem_filter.mp
          (E.precedingRedVertex_mem hbudget z u hu)
        apply E.precedingRedVertex_maximal hbudget z v hv
        simp only [precedingRedCandidates, Finset.mem_filter]
        exact ⟨hdata.1,
          hdata.2.1.trans (((Q.before_iff_vertexIndex_le).1 huv).2.2),
          hdata.2.2⟩
      exact lt_of_le_of_ne hle (fun h =>
        heNe (GraphPath.eq_of_vertexIndex_eq Q hpu hpv h))
    have hpbLtPa : Q.vertexIndex pb < Q.vertexIndex pa := by
      have hf' : s(b, a) ∈ Q.edgeSet := by
        simpa [Sym2.eq_swap] using hf
      have hle :
          Q.vertexIndex pb ≤ Q.vertexIndex pa := by
        have hdata := Finset.mem_filter.mp
          (E.precedingRedVertex_mem hbudget z b hb)
        apply E.precedingRedVertex_maximal hbudget z a ha
        simp only [precedingRedCandidates, Finset.mem_filter]
        exact ⟨hdata.1,
          hdata.2.1.trans (((Q.before_iff_vertexIndex_le).1 hba).2.2),
          hdata.2.2⟩
      exact lt_of_le_of_ne hle (fun h =>
        hfNe.symm (GraphPath.eq_of_vertexIndex_eq Q hpb hpa h))
    rw [Sym2.eq_iff] at hpairs
    rcases hpairs with ⟨hupa, hvpb⟩ | ⟨hupb, hvpa⟩
    · change pu = pa at hupa
      change pv = pb at hvpb
      have hcontra :
          Q.vertexIndex pv < Q.vertexIndex pu := by
        rw [← hvpb, ← hupa] at hpbLtPa
        exact hpbLtPa
      omega
    · change pu = pb at hupb
      change pv = pa at hvpa
      have hva : v = a := by
        simpa [pu, pv, pa, pb, hpvV, hpaA] using hvpa
      have hf' : s(b, v) ∈ Q.edgeSet := by
        simpa [hva, Sym2.eq_swap] using hf
      have hba' : Q.Before b v := by
        simpa [hva] using hba
      have huvNe : u ≠ v := (Q.edgeSet_subset_edgeSet he).ne
      have hbvNe : b ≠ v := (Q.edgeSet_subset_edgeSet hf').ne
      have hub : u = b :=
        GraphPath.backward_edge_unique Q
          he huv huvNe hf' hba' hbvNe
      simpa [hub, hva, Sym2.eq_swap]

/-- The unordered pair of consecutive red predecessors determines an
owner-changing physical edge, independently of its stored orientation. -/
theorem edge_eq_of_predecessor_pair
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {u v a b : V}
    (he : s(u, v) ∈ (E.localBluePath z.1 z.2).edgeSet)
    (hf : s(a, b) ∈ (E.localBluePath z.1 z.2).edgeSet)
    (heNe :
      E.precedingRedVertex hbudget z u
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).1 ≠
        E.precedingRedVertex hbudget z v
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).2)
    (hfNe :
      E.precedingRedVertex hbudget z a
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) hf).1 ≠
        E.precedingRedVertex hbudget z b
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) hf).2)
    (hpairs :
      s(E.precedingRedVertex hbudget z u
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).1,
        E.precedingRedVertex hbudget z v
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) he).2) =
      s(E.precedingRedVertex hbudget z a
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) hf).1,
        E.precedingRedVertex hbudget z b
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath z.1 z.2) hf).2)) :
    s(u, v) = s(a, b) := by
  classical
  let Q := E.localBluePath z.1 z.2
  have hu :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he).1
  have hv :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he).2
  rcases GraphPath.before_total_of_mem Q hu hv with huv | hvu
  · exact E.edge_eq_of_predecessor_pair_of_before_left
      hbudget z he huv hf heNe hfNe hpairs
  · have he' : s(v, u) ∈ Q.edgeSet := by
      simpa [Sym2.eq_swap] using he
    have heNe' :
        E.precedingRedVertex hbudget z v
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he').1 ≠
          E.precedingRedVertex hbudget z u
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he').2 := by
      simpa only [Sym2.eq_swap] using heNe.symm
    have hpairs' :
        s(E.precedingRedVertex hbudget z v
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he').1,
          E.precedingRedVertex hbudget z u
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he').2) =
        s(E.precedingRedVertex hbudget z a
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q hf).1,
          E.precedingRedVertex hbudget z b
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q hf).2) := by
      simpa only [Sym2.eq_swap] using hpairs
    have h :=
      E.edge_eq_of_predecessor_pair_of_before_left
        hbudget z (u := v) (v := u) he' hvu hf heNe' hfNe hpairs'
    simpa [Sym2.eq_swap] using h

/-- A blue physical edge crossing two distinct segment-owner fibres. -/
abbrev BlueSegmentTransition
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :=
  {e : Sym2 V //
    e ∈ E.segmentCrossingEdges hbudget hrecords B hB fallback ∧
      e ∈ E.blueSupport.edgeSet}

/-- The unique local blue path containing a blue segment transition. -/
noncomputable def blueSegmentTransitionIndex
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    E.LocalBlueIndex :=
  Classical.choose (E.blueSupport_edge_has_localBlueIndex e.2.2)

theorem blueSegmentTransition_mem_path
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    e.1 ∈
      (E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).2).edgeSet :=
  Classical.choose_spec (E.blueSupport_edge_has_localBlueIndex e.2.2)

/-- The unordered pair of red intersections which are the endpoints of the
complete suppressed blue arc represented by a transition edge. -/
noncomputable def blueSegmentTransitionEndpoints
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    Sym2 V := by
  let z := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let he := E.blueSegmentTransition_mem_path
    hbudget hrecords B hB fallback e
  let he' : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact he
  exact
    s(E.precedingRedVertex hbudget z e.1.out.1
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he').1,
      E.precedingRedVertex hbudget z e.1.out.2
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he').2)

theorem blueSegmentTransition_predecessors_ne
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    let z := E.blueSegmentTransitionIndex
      hbudget hrecords B hB fallback e
    let he : s(e.1.out.1, e.1.out.2) ∈
        (E.localBluePath z.1 z.2).edgeSet := by
      simpa [Sym2.mk, e.1.out_eq] using
        E.blueSegmentTransition_mem_path
          hbudget hrecords B hB fallback e
    E.precedingRedVertex hbudget z e.1.out.1
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he).1 ≠
      E.precedingRedVertex hbudget z e.1.out.2
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he).2 := by
  classical
  dsimp only
  intro hp
  let z := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    simpa [Sym2.mk, e.1.out_eq] using
      E.blueSegmentTransition_mem_path
        hbudget hrecords B hB fallback e
  have howner :=
    Finset.mem_filter.mp e.2.1 |>.2
  have hleft :=
    E.segmentOwner_precedingRedVertex
      hbudget hrecords B hB fallback z e.1.out.1
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he).1
  have hright :=
    E.segmentOwner_precedingRedVertex
      hbudget hrecords B hB fallback z e.1.out.2
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.localBluePath z.1 z.2) he).2
  apply howner
  rw [← hleft, ← hright, hp]

theorem blueSegmentTransitionEndpoints_ne
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    (E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e).out.1 ≠
      (E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e).out.2 := by
  classical
  let z := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    simpa [Sym2.mk, e.1.out_eq] using
      E.blueSegmentTransition_mem_path
        hbudget hrecords B hB fallback e
  have hpne :=
    E.blueSegmentTransition_predecessors_ne
      hbudget hrecords B hB fallback e
  have hmk :
      E.blueSegmentTransitionEndpoints hbudget hrecords B hB fallback e =
        s(E.precedingRedVertex hbudget z e.1.out.1
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (E.localBluePath z.1 z.2) he).1,
          E.precedingRedVertex hbudget z e.1.out.2
            (GraphPath.endpoints_mem_vertexSet_of_edgeSet
              (E.localBluePath z.1 z.2) he).2) := by
    rfl
  have hnotdiag :
      ¬ (E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e).IsDiag := by
    rw [hmk, Sym2.mk_isDiag_iff]
    exact hpne
  intro hout
  apply hnotdiag
  rw [← (E.blueSegmentTransitionEndpoints
    hbudget hrecords B hB fallback e).out_eq,
    Sym2.mk_isDiag_iff]
  exact hout

/-- The complete carrier-clean blue arc represented by a transition edge,
viewed in the assembled support. -/
noncomputable def blueSegmentTransitionPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    GraphPath (E.assembledSupport hbudget) := by
  let z := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  exact
    (E.predecessorArc hbudget z
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        (E.localBluePath z.1 z.2) he).1
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        (E.localBluePath z.1 z.2) he).2).mapLe
      (E.recordAt_localGraph_le_assembledSupport hbudget z.1)

theorem blueSegmentTransitionPath_internally_carrier_clean
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    (E.blueSegmentTransitionPath
      hbudget hrecords B hB fallback e).InternallyDisjointFromSet
        (E.redCarrierVertices hbudget) := by
  classical
  let z := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  have hclean :=
    E.predecessorArc_internally_carrier_clean hbudget z he
      (E.blueSegmentTransition_predecessors_ne
        hbudget hrecords B hB fallback e)
  intro v hv hcarrier
  apply hclean
  · simpa [blueSegmentTransitionPath, z, he] using hv
  · exact hcarrier

theorem blueSegmentTransitionPath_endpoints
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    s((E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).source,
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).target) =
      E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e := by
  classical
  simp only [blueSegmentTransitionPath,
    blueSegmentTransitionEndpoints, GraphPath.mapLe,
    predecessorArc_source, predecessorArc_target]

theorem blueSegmentTransitionPath_source_ne_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    (E.blueSegmentTransitionPath
      hbudget hrecords B hB fallback e).source ≠
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).target := by
  intro heq
  have hnotdiag :
      ¬ (E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e).IsDiag := by
    intro hdiag
    apply E.blueSegmentTransitionEndpoints_ne
      hbudget hrecords B hB fallback e
    rw [← (E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e).out_eq,
      Sym2.mk_isDiag_iff] at hdiag
    exact hdiag
  apply hnotdiag
  rw [← E.blueSegmentTransitionPath_endpoints
    hbudget hrecords B hB fallback e,
    Sym2.mk_isDiag_iff]
  exact heq

theorem blueSegmentTransitionPath_edgeSet_subset_blue
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    ∀ f ∈ (E.blueSegmentTransitionPath
      hbudget hrecords B hB fallback e).edgeSet,
        f ∈ E.blueSupport.edgeSet := by
  classical
  let z := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  intro f hf
  have hfQ :
      f ∈ (E.localBluePath z.1 z.2).edgeSet := by
    exact E.predecessorArc_edgeSet_subset hbudget z _ _ (by
      simpa [blueSegmentTransitionPath, z, he] using hf)
  let Q := E.localBluePath z.1 z.2
  have hfOut : s(f.out.1, f.out.2) = f := by
    rw [Sym2.mk, f.out_eq]
  have hfQOut : s(f.out.1, f.out.2) ∈ Q.edgeSet := by
    simpa [Q, hfOut] using hfQ
  have hfLocal :
      f ∈ (E.recordAt z.1).layer.localGraph.edgeSet :=
    GraphPath.edgeSet_subset_edgeSet Q (by simpa [Q] using hfQ)
  have hne : f.out.1 ≠ f.out.2 := by
    have hadj :
        (E.recordAt z.1).layer.localGraph.Adj f.out.1 f.out.2 := by
      rw [← _root_.SimpleGraph.mem_edgeSet]
      simpa [hfOut] using hfLocal
    exact hadj.ne
  have hspan :
      (E.recordAt z.1).layer.blue.toPathPacking.spanningGraph.Adj
        f.out.1 f.out.2 := by
    rw [PathPacking.spanningGraph_adj_iff_exists_path_edge]
    refine ⟨?_, hne⟩
    refine ⟨(E.recordAt z.1).layer.blue.indexOfSource
      (labelledImageEquiv
        (E.recordAt z.1).label (E.recordAt z.1).cut.left z.2), ?_⟩
    simpa [Q, localBluePath] using hfQOut
  have hfBlueAdj : E.blueSupport.Adj f.out.1 f.out.2 :=
    (le_iSup
      (fun j : Fin E.finalState.records.length =>
        (E.recordAt j).layer.blue.toPathPacking.spanningGraph) z.1)
      hspan
  have hfBlue : f ∈ E.blueSupport.edgeSet := by
    rw [← _root_.SimpleGraph.mem_edgeSet] at hfBlueAdj
    simpa [hfOut] using hfBlueAdj
  exact hfBlue

/-- Distinct blue transition edges have distinct pairs of red endpoints. -/
theorem blueSegmentTransitionEndpoints_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Function.Injective
      (E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback) := by
  classical
  intro e f hef
  let ze := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let zf := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback f
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath ze.1 ze.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  let hf : s(f.1.out.1, f.1.out.2) ∈
      (E.localBluePath zf.1 zf.2).edgeSet := by
    rw [Sym2.mk, f.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback f
  let peu := E.precedingRedVertex hbudget ze e.1.out.1
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath ze.1 ze.2) he).1
  let pev := E.precedingRedVertex hbudget ze e.1.out.2
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath ze.1 ze.2) he).2
  let pfu := E.precedingRedVertex hbudget zf f.1.out.1
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath zf.1 zf.2) hf).1
  let pfv := E.precedingRedVertex hbudget zf f.1.out.2
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath zf.1 zf.2) hf).2
  have hpairs : s(peu, pev) = s(pfu, pfv) := by
    simpa [blueSegmentTransitionEndpoints, ze, zf, he, hf,
      peu, pev, pfu, pfv] using hef
  have hpeu :
      peu ∈ (E.localBluePath ze.1 ze.2).vertexSet := by
    exact (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget ze e.1.out.1 _)).1
  have hpev :
      pev ∈ (E.localBluePath ze.1 ze.2).vertexSet := by
    exact (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget ze e.1.out.2 _)).1
  have hpfu :
      pfu ∈ (E.localBluePath zf.1 zf.2).vertexSet := by
    exact (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget zf f.1.out.1 _)).1
  have hpfv :
      pfv ∈ (E.localBluePath zf.1 zf.2).vertexSet := by
    exact (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget zf f.1.out.2 _)).1
  have hz : ze = zf := by
    rw [Sym2.eq_iff] at hpairs
    rcases hpairs with hpairs | hpairs
    · exact E.localBlueIndex_unique hbudget hpeu (hpairs.1 ▸ hpfu)
    · exact E.localBlueIndex_unique hbudget hpeu (hpairs.1 ▸ hpfv)
  let hf' : s(f.1.out.1, f.1.out.2) ∈
      (E.localBluePath ze.1 ze.2).edgeSet := by
    rw [hz]
    exact hf
  have hfNe' :
      E.precedingRedVertex hbudget ze f.1.out.1
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath ze.1 ze.2) hf').1 ≠
        E.precedingRedVertex hbudget ze f.1.out.2
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath ze.1 ze.2) hf').2 := by
    simpa [ze, zf, hz, hf'] using
      E.blueSegmentTransition_predecessors_ne
        hbudget hrecords B hB fallback f
  have hpairs' :
      s(E.precedingRedVertex hbudget ze e.1.out.1
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath ze.1 ze.2) he).1,
        E.precedingRedVertex hbudget ze e.1.out.2
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath ze.1 ze.2) he).2) =
      s(E.precedingRedVertex hbudget ze f.1.out.1
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath ze.1 ze.2) hf').1,
        E.precedingRedVertex hbudget ze f.1.out.2
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (E.localBluePath ze.1 ze.2) hf').2) := by
    simpa [peu, pev, pfu, pfv, ze, zf, hz, hf'] using hpairs
  have heq :
      s(e.1.out.1, e.1.out.2) =
        s(f.1.out.1, f.1.out.2) := by
    apply E.edge_eq_of_predecessor_pair hbudget ze he hf'
    · exact E.blueSegmentTransition_predecessors_ne
        hbudget hrecords B hB fallback e
    · exact hfNe'
    · exact hpairs'
  apply Subtype.ext
  calc
    e.1 = s(e.1.out.1, e.1.out.2) := e.1.out_eq.symm
    _ = s(f.1.out.1, f.1.out.2) := heq
    _ = f.1 := f.1.out_eq

/-- Both named endpoints of a transition lie on its local blue path and are
red-carried vertices. -/
theorem mem_blueSegmentTransitionEndpoints
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    {v : V}
    (hv : v ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e) :
    v ∈
        (E.localBluePath
          (E.blueSegmentTransitionIndex
            hbudget hrecords B hB fallback e).1
          (E.blueSegmentTransitionIndex
            hbudget hrecords B hB fallback e).2).vertexSet ∧
      v ∈ E.redCarrierVertices hbudget := by
  classical
  let z := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  let p := E.precedingRedVertex hbudget z e.1.out.1
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).1
  let q := E.precedingRedVertex hbudget z e.1.out.2
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).2
  have hpQ : p ∈ (E.localBluePath z.1 z.2).vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z e.1.out.1 _)).1
  have hqQ : q ∈ (E.localBluePath z.1 z.2).vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z e.1.out.2 _)).1
  have hpC : p ∈ E.redCarrierVertices hbudget := by
    rw [E.mem_redCarrierVertices]
    exact E.precedingRedVertex_has_carrier hbudget z e.1.out.1 _
  have hqC : q ∈ E.redCarrierVertices hbudget := by
    rw [E.mem_redCarrierVertices]
    exact E.precedingRedVertex_has_carrier hbudget z e.1.out.2 _
  have hvpq : v ∈ s(p, q) := by
    simpa [blueSegmentTransitionEndpoints, z, he, p, q] using hv
  rw [Sym2.mem_iff] at hvpq
  rcases hvpq with rfl | rfl
  · exact ⟨hpQ, hpC⟩
  · exact ⟨hqQ, hqC⟩

/-- Every blue-path vertex lying between the two red endpoints of a
transition belongs to its complete suppressed arc. -/
theorem mem_blueSegmentTransitionPath_of_between
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    {x y z : V}
    (hendpoints :
      E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e = s(x, z))
    (hxy :
      (E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).2).Before x y)
    (hyz :
      (E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).2).Before y z) :
    y ∈ (E.blueSegmentTransitionPath
      hbudget hrecords B hB fallback e).vertexSet := by
  classical
  let q := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath q.1 q.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  let p₁ := E.precedingRedVertex hbudget q e.1.out.1
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath q.1 q.2) he).1
  let p₂ := E.precedingRedVertex hbudget q e.1.out.2
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath q.1 q.2) he).2
  have hp₁ :
      p₁ ∈ (E.localBluePath q.1 q.2).vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget q e.1.out.1 _)).1
  have hp₂ :
      p₂ ∈ (E.localBluePath q.1 q.2).vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget q e.1.out.2 _)).1
  have hpairs : s(p₁, p₂) = s(x, z) := by
    simpa [blueSegmentTransitionEndpoints, q, he, p₁, p₂] using
      hendpoints
  rw [Sym2.eq_iff] at hpairs
  rcases hpairs with ⟨hp₁x, hp₂z⟩ | ⟨hp₁z, hp₂x⟩
  · have hxyData :=
      ((E.localBluePath q.1 q.2).before_iff_vertexIndex_le).1 hxy
    have hyzData :=
      ((E.localBluePath q.1 q.2).before_iff_vertexIndex_le).1 hyz
    have hxz :
        (E.localBluePath q.1 q.2).Before x z :=
      ((E.localBluePath q.1 q.2).before_iff_vertexIndex_le).2
        ⟨hxyData.1, hyzData.2.1,
          hxyData.2.2.trans hyzData.2.2⟩
    have hp₁p₂ :
        (E.localBluePath q.1 q.2).Before p₁ p₂ := by
      simpa only [hp₁x, hp₂z] using hxz
    have hp₁y :
        (E.localBluePath q.1 q.2).Before p₁ y := by
      simpa only [hp₁x] using hxy
    have hyp₂ :
        (E.localBluePath q.1 q.2).Before y p₂ := by
      simpa only [hp₂z] using hyz
    have hySeg :
        y ∈ ((E.localBluePath q.1 q.2).segmentOfBefore hp₁p₂).vertexSet :=
      (E.localBluePath q.1 q.2).mem_segmentOfBefore_of_before_of_before
        hp₁p₂ hp₁y hyp₂
    have hidx :
        (E.localBluePath q.1 q.2).vertexIndex p₁ ≤
          (E.localBluePath q.1 q.2).vertexIndex p₂ := by
      exact
        ((E.localBluePath q.1 q.2).before_iff_vertexIndex_le).1
          hp₁p₂ |>.2.2
    simp only [blueSegmentTransitionPath, GraphPath.mapLe_vertexSet]
    change y ∈
      (GraphPath.segmentBetween
        (E.localBluePath q.1 q.2) hp₁ hp₂).vertexSet
    simp only [GraphPath.segmentBetween, hidx, ↓reduceDIte]
    exact hySeg
  · have hxyData :=
      ((E.localBluePath q.1 q.2).before_iff_vertexIndex_le).1 hxy
    have hyzData :=
      ((E.localBluePath q.1 q.2).before_iff_vertexIndex_le).1 hyz
    have hxz :
        (E.localBluePath q.1 q.2).Before x z :=
      ((E.localBluePath q.1 q.2).before_iff_vertexIndex_le).2
        ⟨hxyData.1, hyzData.2.1,
          hxyData.2.2.trans hyzData.2.2⟩
    have hp₂p₁ :
        (E.localBluePath q.1 q.2).Before p₂ p₁ := by
      simpa only [hp₂x, hp₁z] using hxz
    have hp₂y :
        (E.localBluePath q.1 q.2).Before p₂ y := by
      simpa only [hp₂x] using hxy
    have hyp₁ :
        (E.localBluePath q.1 q.2).Before y p₁ := by
      simpa only [hp₁z] using hyz
    have hySeg :
        y ∈ ((E.localBluePath q.1 q.2).segmentOfBefore hp₂p₁).vertexSet :=
      (E.localBluePath q.1 q.2).mem_segmentOfBefore_of_before_of_before
        hp₂p₁ hp₂y hyp₁
    have hnot :
        ¬ (E.localBluePath q.1 q.2).vertexIndex p₁ ≤
            (E.localBluePath q.1 q.2).vertexIndex p₂ := by
      have hpne :=
        E.blueSegmentTransition_predecessors_ne
          hbudget hrecords B hB fallback e
      have hp₂LtP₁ :
          (E.localBluePath q.1 q.2).vertexIndex p₂ <
            (E.localBluePath q.1 q.2).vertexIndex p₁ := by
        have hle :=
          ((E.localBluePath q.1 q.2).before_iff_vertexIndex_le).1
            hp₂p₁ |>.2.2
        exact lt_of_le_of_ne hle (fun h =>
          hpne (GraphPath.eq_of_vertexIndex_eq
            (E.localBluePath q.1 q.2) hp₁ hp₂ h.symm))
      exact Nat.not_le.mpr hp₂LtP₁
    simp only [blueSegmentTransitionPath, GraphPath.mapLe_vertexSet]
    change y ∈
      (GraphPath.segmentBetween
        (E.localBluePath q.1 q.2) hp₁ hp₂).vertexSet
    simp only [GraphPath.segmentBetween, hnot, ↓reduceDIte]
    simpa using hySeg

/-- At a fixed red intersection there is at most one transition arc leaving
in either direction along the local blue-path order. -/
theorem blueSegmentTransition_otherEndpoint_unique_of_before
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e f : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    {x y z : V}
    (he :
      E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e = s(x, y))
    (hf :
      E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback f = s(x, z))
    (hxy :
      (E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).2).Before x y)
    (hxz :
      (E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback f).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback f).2).Before x z) :
    y = z := by
  classical
  let qe := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let qf := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback f
  change (E.localBluePath qe.1 qe.2).Before x y at hxy
  change (E.localBluePath qf.1 qf.2).Before x z at hxz
  have hxEe : x ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e := by
    rw [he]
    simp
  have hxEf : x ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f := by
    rw [hf]
    simp
  have hyEe : y ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e := by
    rw [he]
    simp
  have hzEf : z ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f := by
    rw [hf]
    simp
  have hxQe :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e hxEe).1
  have hxQf :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f hxEf).1
  have hyQe :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e hyEe).1
  have hzQf :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f hzEf).1
  have hyCarrier :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e hyEe).2
  have hzCarrier :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f hzEf).2
  have hq : qe = qf :=
    E.localBlueIndex_unique hbudget hxQe hxQf
  have hyQf :
      y ∈ (E.localBluePath qf.1 qf.2).vertexSet := by
    rw [← hq]
    exact hyQe
  have hzQe :
      z ∈ (E.localBluePath qe.1 qe.2).vertexSet := by
    rw [hq]
    exact hzQf
  have hxyNe : x ≠ y := by
    intro h
    have hdiag :
        (E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e).IsDiag := by
      rw [he, Sym2.mk_isDiag_iff]
      exact h
    have hout :=
      E.blueSegmentTransitionEndpoints_ne
        hbudget hrecords B hB fallback e
    apply hout
    rw [← (E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e).out_eq,
      Sym2.mk_isDiag_iff] at hdiag
    exact hdiag
  have hxzNe : x ≠ z := by
    intro h
    have hdiag :
        (E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback f).IsDiag := by
      rw [hf, Sym2.mk_isDiag_iff]
      exact h
    have hout :=
      E.blueSegmentTransitionEndpoints_ne
        hbudget hrecords B hB fallback f
    apply hout
    rw [← (E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f).out_eq,
      Sym2.mk_isDiag_iff] at hdiag
    exact hdiag
  rcases le_total
      ((E.localBluePath qe.1 qe.2).vertexIndex y)
      ((E.localBluePath qe.1 qe.2).vertexIndex z) with hyz | hzy
  · have hyzBefore :
        (E.localBluePath qf.1 qf.2).Before y z := by
      apply (E.localBluePath qf.1 qf.2).before_iff_vertexIndex_le |>.2
      refine ⟨hyQf, hzQf, ?_⟩
      rw [← hq]
      exact hyz
    have hxyF :
        (E.localBluePath qf.1 qf.2).Before x y := by
      rw [← hq]
      exact hxy
    have hyPath :=
      E.mem_blueSegmentTransitionPath_of_between
        hbudget hrecords B hB fallback f hf hxyF hyzBefore
    have hyEndpoint :=
      E.blueSegmentTransitionPath_internally_carrier_clean
        hbudget hrecords B hB fallback f hyPath hyCarrier
    have hyNamed :
        y ∈ E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback f := by
      rw [← E.blueSegmentTransitionPath_endpoints
        hbudget hrecords B hB fallback f]
      rcases hyEndpoint with rfl | rfl <;> simp
    rw [hf, Sym2.mem_iff] at hyNamed
    exact hyNamed.resolve_left hxyNe.symm
  · have hzyBefore :
        (E.localBluePath qe.1 qe.2).Before z y := by
      exact (E.localBluePath qe.1 qe.2).before_iff_vertexIndex_le |>.2
        ⟨hzQe, hyQe, hzy⟩
    have hxzE :
        (E.localBluePath qe.1 qe.2).Before x z := by
      rw [hq]
      exact hxz
    have hzPath :=
      E.mem_blueSegmentTransitionPath_of_between
        hbudget hrecords B hB fallback e he hxzE hzyBefore
    have hzEndpoint :=
      E.blueSegmentTransitionPath_internally_carrier_clean
        hbudget hrecords B hB fallback e hzPath hzCarrier
    have hzNamed :
        z ∈ E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e := by
      rw [← E.blueSegmentTransitionPath_endpoints
        hbudget hrecords B hB fallback e]
      rcases hzEndpoint with rfl | rfl <;> simp
    rw [he, Sym2.mem_iff] at hzNamed
    exact (hzNamed.resolve_left hxzNe.symm).symm

theorem blueSegmentTransition_otherEndpoint_unique_of_after
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e f : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    {x y z : V}
    (he :
      E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e = s(x, y))
    (hf :
      E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback f = s(x, z))
    (hyx :
      (E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).2).Before y x)
    (hzx :
      (E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback f).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback f).2).Before z x) :
    y = z := by
  classical
  let qe := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback e
  let qf := E.blueSegmentTransitionIndex
    hbudget hrecords B hB fallback f
  change (E.localBluePath qe.1 qe.2).Before y x at hyx
  change (E.localBluePath qf.1 qf.2).Before z x at hzx
  have hxEe : x ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e := by rw [he]; simp
  have hxEf : x ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f := by rw [hf]; simp
  have hyEe : y ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e := by rw [he]; simp
  have hzEf : z ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f := by rw [hf]; simp
  have hxQe :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e hxEe).1
  have hxQf :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f hxEf).1
  have hyQe :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e hyEe).1
  have hzQf :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f hzEf).1
  have hyCarrier :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e hyEe).2
  have hzCarrier :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f hzEf).2
  have hq : qe = qf :=
    E.localBlueIndex_unique hbudget hxQe hxQf
  have hyQf : y ∈ (E.localBluePath qf.1 qf.2).vertexSet := by
    rw [← hq]
    exact hyQe
  have hzQe : z ∈ (E.localBluePath qe.1 qe.2).vertexSet := by
    rw [hq]
    exact hzQf
  have hxyNe : x ≠ y := by
    intro h
    have hdiag :
        (E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e).IsDiag := by
      rw [he, Sym2.mk_isDiag_iff]
      exact h
    have hout :=
      E.blueSegmentTransitionEndpoints_ne
        hbudget hrecords B hB fallback e
    apply hout
    rw [← (E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e).out_eq,
      Sym2.mk_isDiag_iff] at hdiag
    exact hdiag
  have hxzNe : x ≠ z := by
    intro h
    have hdiag :
        (E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback f).IsDiag := by
      rw [hf, Sym2.mk_isDiag_iff]
      exact h
    have hout :=
      E.blueSegmentTransitionEndpoints_ne
        hbudget hrecords B hB fallback f
    apply hout
    rw [← (E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f).out_eq,
      Sym2.mk_isDiag_iff] at hdiag
    exact hdiag
  rcases le_total
      ((E.localBluePath qe.1 qe.2).vertexIndex y)
      ((E.localBluePath qe.1 qe.2).vertexIndex z) with hyz | hzy
  · have hyzBefore :
        (E.localBluePath qe.1 qe.2).Before y z :=
      (E.localBluePath qe.1 qe.2).before_iff_vertexIndex_le |>.2
        ⟨hyQe, hzQe, hyz⟩
    have hzxE :
        (E.localBluePath qe.1 qe.2).Before z x := by
      rw [hq]
      exact hzx
    have hzPath :=
      E.mem_blueSegmentTransitionPath_of_between
        hbudget hrecords B hB fallback e
        (by simpa [Sym2.eq_swap] using he)
        hyzBefore hzxE
    have hzEndpoint :=
      E.blueSegmentTransitionPath_internally_carrier_clean
        hbudget hrecords B hB fallback e hzPath hzCarrier
    have hzNamed :
        z ∈ E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e := by
      rw [← E.blueSegmentTransitionPath_endpoints
        hbudget hrecords B hB fallback e]
      rcases hzEndpoint with rfl | rfl <;> simp
    rw [he, Sym2.mem_iff] at hzNamed
    exact (hzNamed.resolve_left hxzNe.symm).symm
  · have hzyBefore :
        (E.localBluePath qf.1 qf.2).Before z y := by
      apply (E.localBluePath qf.1 qf.2).before_iff_vertexIndex_le |>.2
      refine ⟨hzQf, hyQf, ?_⟩
      rw [← hq]
      exact hzy
    have hyxF :
        (E.localBluePath qf.1 qf.2).Before y x := by
      rw [← hq]
      exact hyx
    have hyPath :=
      E.mem_blueSegmentTransitionPath_of_between
        hbudget hrecords B hB fallback f
        (by simpa [Sym2.eq_swap] using hf)
        hzyBefore hyxF
    have hyEndpoint :=
      E.blueSegmentTransitionPath_internally_carrier_clean
        hbudget hrecords B hB fallback f hyPath hyCarrier
    have hyNamed :
        y ∈ E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback f := by
      rw [← E.blueSegmentTransitionPath_endpoints
        hbudget hrecords B hB fallback f]
      rcases hyEndpoint with rfl | rfl <;> simp
    rw [hf, Sym2.mem_iff] at hyNamed
    exact hyNamed.resolve_left hxyNe.symm

/-- The simple graph whose edges are the endpoint pairs of all complete blue
segment transitions. -/
noncomputable def blueSegmentTransitionGraph
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    _root_.SimpleGraph V :=
  _root_.SimpleGraph.fromEdgeSet
    (Set.range
      (E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback))

theorem blueSegmentTransitionGraph_adj_has_transition
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    {x y : V}
    (hxy :
      (E.blueSegmentTransitionGraph
        hbudget hrecords B hB fallback).Adj x y) :
    ∃ e : E.BlueSegmentTransition hbudget hrecords B hB fallback,
      E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e = s(x, y) := by
  rw [blueSegmentTransitionGraph,
    _root_.SimpleGraph.fromEdgeSet_adj] at hxy
  exact hxy.1

/-- The suppressed blue arcs form a vertex-disjoint union of paths: each red
intersection is incident with at most the preceding and following arc. -/
theorem blueSegmentTransitionGraph_maxDegreeAtMost_two
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    MaxDegreeAtMost
      (E.blueSegmentTransitionGraph hbudget hrecords B hB fallback) 2 := by
  classical
  intro x
  let K := E.blueSegmentTransitionGraph hbudget hrecords B hB fallback
  let N := K.neighborFinset x
  refine ⟨N, ?_, ?_⟩
  · intro y
    exact K.mem_neighborFinset x y
  · by_cases hN : N.Nonempty
    · let y₀ : {y : V // y ∈ N} := ⟨Classical.choose hN,
        Classical.choose_spec hN⟩
      have hxy₀ : K.Adj x y₀.1 := by
        exact (K.mem_neighborFinset x y₀.1).mp y₀.2
      let e₀ :=
        Classical.choose
          (E.blueSegmentTransitionGraph_adj_has_transition
            hbudget hrecords B hB fallback hxy₀)
      have he₀ :
          E.blueSegmentTransitionEndpoints
              hbudget hrecords B hB fallback e₀ =
            s(x, y₀.1) :=
        Classical.choose_spec
          (E.blueSegmentTransitionGraph_adj_has_transition
            hbudget hrecords B hB fallback hxy₀)
      let q₀ := E.blueSegmentTransitionIndex
        hbudget hrecords B hB fallback e₀
      let transition :
          {y : V // y ∈ N} →
            E.BlueSegmentTransition hbudget hrecords B hB fallback :=
        fun y =>
          Classical.choose
            (E.blueSegmentTransitionGraph_adj_has_transition
              hbudget hrecords B hB fallback
              ((K.mem_neighborFinset x y.1).mp y.2))
      have transition_spec :
          ∀ y,
            E.blueSegmentTransitionEndpoints
                hbudget hrecords B hB fallback (transition y) =
              s(x, y.1) := by
        intro y
        exact Classical.choose_spec
          (E.blueSegmentTransitionGraph_adj_has_transition
            hbudget hrecords B hB fallback
            ((K.mem_neighborFinset x y.1).mp y.2))
      have x_mem_transition :
          ∀ y : {y : V // y ∈ N}, x ∈
            (E.localBluePath
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback (transition y)).1
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback (transition y)).2).vertexSet := by
        intro y
        have hx : x ∈ E.blueSegmentTransitionEndpoints
            hbudget hrecords B hB fallback (transition y) := by
          rw [transition_spec]
          simp
        exact (E.mem_blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback (transition y) hx).1
      have y_mem_transition :
          ∀ y : {y : V // y ∈ N}, y.1 ∈
            (E.localBluePath
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback (transition y)).1
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback (transition y)).2).vertexSet := by
        intro y
        have hy : y.1 ∈ E.blueSegmentTransitionEndpoints
            hbudget hrecords B hB fallback (transition y) := by
          rw [transition_spec]
          simp
        exact (E.mem_blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback (transition y) hy).1
      have x_mem_q₀ :
          x ∈ (E.localBluePath q₀.1 q₀.2).vertexSet := by
        have hx : x ∈ E.blueSegmentTransitionEndpoints
            hbudget hrecords B hB fallback e₀ := by
          rw [he₀]
          simp
        exact (E.mem_blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e₀ hx).1
      have q_eq :
          ∀ y : {y : V // y ∈ N},
            E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback (transition y) = q₀ := by
        intro y
        exact E.localBlueIndex_unique hbudget
          (x_mem_transition y) x_mem_q₀
      have y_mem_q₀ :
          ∀ y : {y : V // y ∈ N},
            y.1 ∈ (E.localBluePath q₀.1 q₀.2).vertexSet := by
        intro y
        rw [← q_eq y]
        exact y_mem_transition y
      let side : {y : V // y ∈ N} → Fin 2 :=
        fun y =>
          if (E.localBluePath q₀.1 q₀.2).Before x y.1 then 0 else 1
      have hside : Function.Injective side := by
        intro y z hyz
        by_cases hy :
            (E.localBluePath q₀.1 q₀.2).Before x y.1
        · by_cases hz :
              (E.localBluePath q₀.1 q₀.2).Before x z.1
          · apply Subtype.ext
            apply E.blueSegmentTransition_otherEndpoint_unique_of_before
              hbudget hrecords B hB fallback
              (transition y) (transition z)
              (transition_spec y) (transition_spec z)
            · rw [q_eq y]
              exact hy
            · rw [q_eq z]
              exact hz
          · simp [side, hy, hz] at hyz
        · by_cases hz :
              (E.localBluePath q₀.1 q₀.2).Before x z.1
          · simp [side, hy, hz] at hyz
          · have hyx :
                (E.localBluePath q₀.1 q₀.2).Before y.1 x := by
              rcases GraphPath.before_total_of_mem
                  (E.localBluePath q₀.1 q₀.2)
                  (y_mem_q₀ y) x_mem_q₀ with hy' | hy'
              · exact hy'
              · exact False.elim (hy hy')
            have hzx :
                (E.localBluePath q₀.1 q₀.2).Before z.1 x := by
              rcases GraphPath.before_total_of_mem
                  (E.localBluePath q₀.1 q₀.2)
                  (y_mem_q₀ z) x_mem_q₀ with hz' | hz'
              · exact hz'
              · exact False.elim (hz hz')
            apply Subtype.ext
            apply E.blueSegmentTransition_otherEndpoint_unique_of_after
              hbudget hrecords B hB fallback
              (transition y) (transition z)
              (transition_spec y) (transition_spec z)
            · rw [q_eq y]
              exact hyx
            · rw [q_eq z]
              exact hzx
      have hcard :
          Fintype.card {y : V // y ∈ N} ≤ Fintype.card (Fin 2) :=
        Fintype.card_le_of_injective side hside
      simpa only [Fintype.card_coe, Fintype.card_fin] using hcard
    · have hEmpty : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
      simp [hEmpty]

theorem blueSegmentTransitionEndpoints_mem_graph_edgeSet
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    E.blueSegmentTransitionEndpoints hbudget hrecords B hB fallback e ∈
      (E.blueSegmentTransitionGraph
        hbudget hrecords B hB fallback).edgeSet := by
  classical
  rw [blueSegmentTransitionGraph,
    _root_.SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨⟨e, rfl⟩, ?_⟩
  intro hdiag
  have hout :=
    E.blueSegmentTransitionEndpoints_ne
      hbudget hrecords B hB fallback e
  apply hout
  rw [Sym2.mem_diagSet,
    ← (E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e).out_eq,
    Sym2.mk_isDiag_iff] at hdiag
  exact hdiag

/-- A family of transitions has disjoint complete-link endpoints when their
unordered endpoint pairs form a vertex-disjoint edge family. -/
def BlueSegmentTransitionFamilyVertexDisjoint
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (M : Finset
      (E.BlueSegmentTransition hbudget hrecords B hB fallback)) : Prop :=
  EdgeFamilyVertexDisjoint
    (M.image
      (E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback))

/-- From `128t` blue quotient transitions, select exactly `16t` complete
links with pairwise disjoint red endpoints. -/
theorem exists_blueSegmentTransition_subfamily_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (T : Finset
      (E.BlueSegmentTransition hbudget hrecords B hB fallback))
    {t : ℕ} (hlarge : 128 * t ≤ T.card) :
    ∃ M : Finset
        (E.BlueSegmentTransition hbudget hrecords B hB fallback),
      M ⊆ T ∧
        E.BlueSegmentTransitionFamilyVertexDisjoint
          hbudget hrecords B hB fallback M ∧
        M.card = 16 * t := by
  classical
  let endpoint :=
    E.blueSegmentTransitionEndpoints hbudget hrecords B hB fallback
  let K := E.blueSegmentTransitionGraph hbudget hrecords B hB fallback
  let F := T.image endpoint
  have hFcard : F.card = T.card := by
    exact Finset.card_image_of_injective T
      (E.blueSegmentTransitionEndpoints_injective
        hbudget hrecords B hB fallback)
  have hFK : ∀ f ∈ F, f ∈ K.edgeSet := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨e, _heT, rfl⟩
    exact E.blueSegmentTransitionEndpoints_mem_graph_edgeSet
      hbudget hrecords B hB fallback e
  obtain ⟨D, hDF, hDdisj, hDcard⟩ :=
    exists_vertexDisjoint_subfamily_card_of_edgeSet K
      (maxDegreeAtMost_mono
        (E.blueSegmentTransitionGraph_maxDegreeAtMost_two
          hbudget hrecords B hB fallback) (by omega))
      F hFK (by simpa [hFcard] using hlarge)
  let M := T.filter fun e => endpoint e ∈ D
  have hMsub : M ⊆ T := Finset.filter_subset _ _
  have hImage : M.image endpoint = D := by
    ext f
    constructor
    · intro hf
      rcases Finset.mem_image.mp hf with ⟨e, heM, rfl⟩
      exact (Finset.mem_filter.mp heM).2
    · intro hfD
      have hfF := hDF hfD
      rcases Finset.mem_image.mp hfF with ⟨e, heT, heEq⟩
      apply Finset.mem_image.mpr
      refine ⟨e, ?_, heEq⟩
      exact Finset.mem_filter.mpr
        ⟨heT, by simpa [heEq] using hfD⟩
  have hMcard :
      M.card = (M.image endpoint).card := by
    symm
    exact Finset.card_image_of_injective M
      (E.blueSegmentTransitionEndpoints_injective
        hbudget hrecords B hB fallback)
  refine ⟨M, hMsub, ?_, ?_⟩
  · simpa [BlueSegmentTransitionFamilyVertexDisjoint,
      endpoint, hImage] using hDdisj
  · rw [hMcard, hImage, hDcard]

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
