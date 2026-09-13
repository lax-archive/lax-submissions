import Lax17Proofs.Source.TreewidthSparsifierTheorem51SegmentWellLinked
import Lax17Proofs.Source.ChekuriChuzhoySection5DensePartition

namespace Lax17Proofs

universe u v w

/-!
# Boundaries of path segments

An internal degree-two vertex of a simple path cannot send an edge outside
the path.  Consequently the boundary degree of a path segment is controlled
by the number of ambient branch vertices on the segment, plus its two
endpoints.  This is the degree-two-suppression estimate used when expanding
the contracted segments in Theorem 5.1.
-/

namespace SimpleGraph
namespace TreewidthSparsifier

open ChekuriChuzhoySection5TerminalSkeleton


variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite named-edge presentation of a finite simple graph. -/
noncomputable def simpleEdgeIndexedGraph
    (H : _root_.SimpleGraph V) :
    FiniteEdgeIndexedGraph V := by
  classical
  let edges := H.edgeFinset
  exact {
    Edge := Fin edges.card
    left := fun e => (edges.equivFin.symm e).1.out.1
    right := fun e => (edges.equivFin.symm e).1.out.2
    end_ne := by
      intro e heq
      have heSet : (edges.equivFin.symm e).1 ∈ H.edgeSet := by
        exact _root_.SimpleGraph.mem_edgeFinset.mp
          (edges.equivFin.symm e).2
      have hdiag : (edges.equivFin.symm e).1.IsDiag := by
        rw [← (edges.equivFin.symm e).1.out_eq, Sym2.mk_isDiag_iff]
        exact heq
      exact (H.not_isDiag_of_mem_edgeSet heSet) hdiag
  }

namespace simpleEdgeIndexedGraph

variable (H : _root_.SimpleGraph V)

/-- The physical unordered edge named by an indexed edge. -/
noncomputable def edgeAt
    (e : (simpleEdgeIndexedGraph H).Edge) : Sym2 V := by
  classical
  exact (H.edgeFinset.equivFin.symm e).1

theorem edgeAt_mem_edgeSet
    (e : (simpleEdgeIndexedGraph H).Edge) :
    edgeAt H e ∈ H.edgeSet := by
  classical
  exact _root_.SimpleGraph.mem_edgeFinset.mp
    (H.edgeFinset.equivFin.symm e).2

theorem edgeAt_injective :
    Function.Injective (edgeAt H) := by
  classical
  intro e f hef
  have hsub :
      H.edgeFinset.equivFin.symm e =
        H.edgeFinset.equivFin.symm f := by
    exact Subtype.ext hef
  exact H.edgeFinset.equivFin.symm.injective hsub

@[simp] theorem left_eq_edgeAt_out_fst
    (e : (simpleEdgeIndexedGraph H).Edge) :
    (simpleEdgeIndexedGraph H).left e = (edgeAt H e).out.1 := rfl

@[simp] theorem right_eq_edgeAt_out_snd
    (e : (simpleEdgeIndexedGraph H).Edge) :
    (simpleEdgeIndexedGraph H).right e = (edgeAt H e).out.2 := rfl

theorem mem_edgeAt_iff_mem_incidentEdges
    (v : V) (e : (simpleEdgeIndexedGraph H).Edge) :
    v ∈ edgeAt H e ↔
      e ∈ (simpleEdgeIndexedGraph H).incidentEdges v := by
  classical
  rw [(simpleEdgeIndexedGraph H).mem_incidentEdges]
  constructor
  · intro hv
    rcases Sym2.mem_iff_exists.mp hv with ⟨w, hw⟩
    have hp :
      s((edgeAt H e).out.1, (edgeAt H e).out.2) =
          s(v, w) :=
      (edgeAt H e).out_eq.trans hw
    rw [Sym2.eq_iff] at hp
    rcases hp with hp | hp
    · exact Or.inl hp.1
    · exact Or.inr hp.2
  · intro he
    rcases he with he | he
    · apply Sym2.mem_iff_exists.mpr
      refine ⟨(edgeAt H e).out.2, ?_⟩
      rw [← he]
      exact (edgeAt H e).out_eq.symm
    · apply Sym2.mem_iff_exists.mpr
      refine ⟨(edgeAt H e).out.1, ?_⟩
      rw [← he, Sym2.eq_swap]
      exact (edgeAt H e).out_eq.symm

/-- The endpoint opposite `v` on an indexed simple edge incident with `v`. -/
noncomputable def other
    (v : V)
    (e : (simpleEdgeIndexedGraph H).Edge) : V :=
  if (simpleEdgeIndexedGraph H).left e = v
  then (simpleEdgeIndexedGraph H).right e
  else (simpleEdgeIndexedGraph H).left e

theorem other_adj
    (v : V)
    (e : (simpleEdgeIndexedGraph H).Edge)
    (he : e ∈ (simpleEdgeIndexedGraph H).incidentEdges v) :
    H.Adj v (other H v e) := by
  classical
  have hadj :
      H.Adj (edgeAt H e).out.1 (edgeAt H e).out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, (edgeAt H e).out_eq] using edgeAt_mem_edgeSet H e
  have hincident :=
    ((simpleEdgeIndexedGraph H).mem_incidentEdges v e).1 he
  rcases hincident with hleft | hright
  · unfold other
    rw [if_pos hleft, ← hleft]
    exact hadj
  · have hleftNe :
        (simpleEdgeIndexedGraph H).left e ≠ v := by
      intro hleft
      exact (simpleEdgeIndexedGraph H).end_ne e
        (hleft.trans hright.symm)
    unfold other
    rw [if_neg hleftNe, ← hright]
    exact hadj.symm

theorem other_injective
    (v : V) :
    Function.Injective
      (fun e :
          {e : (simpleEdgeIndexedGraph H).Edge //
            e ∈ (simpleEdgeIndexedGraph H).incidentEdges v} =>
        other H v e.1) := by
  classical
  intro e f hef
  change other H v e.1 = other H v f.1 at hef
  apply Subtype.ext
  have heInc :=
    ((simpleEdgeIndexedGraph H).mem_incidentEdges v e.1).1 e.2
  have hfInc :=
    ((simpleEdgeIndexedGraph H).mem_incidentEdges v f.1).1 f.2
  rcases heInc with heL | heR <;>
    rcases hfInc with hfL | hfR
  · have heOther :
        other H v e.1 =
          (simpleEdgeIndexedGraph H).right e.1 := by
      unfold other
      rw [if_pos heL]
    have hfOther :
        other H v f.1 =
          (simpleEdgeIndexedGraph H).right f.1 := by
      unfold other
      rw [if_pos hfL]
    rw [heOther, hfOther] at hef
    apply edgeAt_injective H
    calc
      edgeAt H e.1 =
          s((simpleEdgeIndexedGraph H).left e.1,
            (simpleEdgeIndexedGraph H).right e.1) := by
        exact (edgeAt H e.1).out_eq.symm
      _ = s(v, (simpleEdgeIndexedGraph H).right e.1) := by rw [heL]
      _ = s(v, (simpleEdgeIndexedGraph H).right f.1) := by rw [hef]
      _ = s((simpleEdgeIndexedGraph H).left f.1,
            (simpleEdgeIndexedGraph H).right f.1) := by rw [hfL]
      _ = edgeAt H f.1 := (edgeAt H f.1).out_eq
  · have heOther :
        other H v e.1 =
          (simpleEdgeIndexedGraph H).right e.1 := by
      unfold other
      rw [if_pos heL]
    have hfLeftNe :
        (simpleEdgeIndexedGraph H).left f.1 ≠ v := by
      intro hfL
      exact (simpleEdgeIndexedGraph H).end_ne f.1
        (hfL.trans hfR.symm)
    have hfOther :
        other H v f.1 =
          (simpleEdgeIndexedGraph H).left f.1 := by
      unfold other
      rw [if_neg hfLeftNe]
    rw [heOther, hfOther] at hef
    apply edgeAt_injective H
    calc
      edgeAt H e.1 =
          s((simpleEdgeIndexedGraph H).left e.1,
          (simpleEdgeIndexedGraph H).right e.1) :=
        (edgeAt H e.1).out_eq.symm
      _ = s(v, (simpleEdgeIndexedGraph H).right e.1) := by rw [heL]
      _ = s(v, (simpleEdgeIndexedGraph H).left f.1) := by rw [hef]
      _ = s((simpleEdgeIndexedGraph H).right f.1,
            (simpleEdgeIndexedGraph H).left f.1) := by rw [hfR]
      _ = s((simpleEdgeIndexedGraph H).left f.1,
            (simpleEdgeIndexedGraph H).right f.1) := Sym2.eq_swap
      _ = edgeAt H f.1 := (edgeAt H f.1).out_eq
  · have heLeftNe :
        (simpleEdgeIndexedGraph H).left e.1 ≠ v := by
      intro heL
      exact (simpleEdgeIndexedGraph H).end_ne e.1
        (heL.trans heR.symm)
    have heOther :
        other H v e.1 =
          (simpleEdgeIndexedGraph H).left e.1 := by
      unfold other
      rw [if_neg heLeftNe]
    have hfOther :
        other H v f.1 =
          (simpleEdgeIndexedGraph H).right f.1 := by
      unfold other
      rw [if_pos hfL]
    rw [heOther, hfOther] at hef
    apply edgeAt_injective H
    calc
      edgeAt H e.1 =
          s((simpleEdgeIndexedGraph H).left e.1,
          (simpleEdgeIndexedGraph H).right e.1) :=
        (edgeAt H e.1).out_eq.symm
      _ = s((simpleEdgeIndexedGraph H).left e.1, v) := by rw [heR]
      _ = s((simpleEdgeIndexedGraph H).right f.1, v) := by rw [hef]
      _ = s((simpleEdgeIndexedGraph H).right f.1,
            (simpleEdgeIndexedGraph H).left f.1) := by rw [hfL]
      _ = s((simpleEdgeIndexedGraph H).left f.1,
            (simpleEdgeIndexedGraph H).right f.1) := Sym2.eq_swap
      _ = edgeAt H f.1 := (edgeAt H f.1).out_eq
  · have heLeftNe :
        (simpleEdgeIndexedGraph H).left e.1 ≠ v := by
      intro heL
      exact (simpleEdgeIndexedGraph H).end_ne e.1
        (heL.trans heR.symm)
    have hfLeftNe :
        (simpleEdgeIndexedGraph H).left f.1 ≠ v := by
      intro hfL
      exact (simpleEdgeIndexedGraph H).end_ne f.1
        (hfL.trans hfR.symm)
    have heOther :
        other H v e.1 =
          (simpleEdgeIndexedGraph H).left e.1 := by
      unfold other
      rw [if_neg heLeftNe]
    have hfOther :
        other H v f.1 =
          (simpleEdgeIndexedGraph H).left f.1 := by
      unfold other
      rw [if_neg hfLeftNe]
    rw [heOther, hfOther] at hef
    apply edgeAt_injective H
    calc
      edgeAt H e.1 =
          s((simpleEdgeIndexedGraph H).left e.1,
          (simpleEdgeIndexedGraph H).right e.1) :=
        (edgeAt H e.1).out_eq.symm
      _ = s((simpleEdgeIndexedGraph H).left e.1, v) := by rw [heR]
      _ = s((simpleEdgeIndexedGraph H).left f.1, v) := by rw [hef]
      _ = s((simpleEdgeIndexedGraph H).left f.1,
            (simpleEdgeIndexedGraph H).right f.1) := by rw [hfR]
      _ = edgeAt H f.1 := (edgeAt H f.1).out_eq

theorem degree_le_of_maxDegreeAtMost
    {d : ℕ} (hdegree : MaxDegreeAtMost H d) (v : V) :
    (simpleEdgeIndexedGraph H).degree v ≤ d := by
  classical
  let f :
      {e : (simpleEdgeIndexedGraph H).Edge //
        e ∈ (simpleEdgeIndexedGraph H).incidentEdges v} →
        {w : V // w ∈ MaxDegreeAtMost.neighborFinset hdegree v} :=
    fun e =>
      ⟨other H v e.1,
        (MaxDegreeAtMost.mem_neighborFinset hdegree v _).2
          (other_adj H v e.1 e.2)⟩
  have hf : Function.Injective f := by
    intro e q heq
    exact other_injective H v (congrArg Subtype.val heq)
  calc
    (simpleEdgeIndexedGraph H).degree v =
        Fintype.card
          {e : (simpleEdgeIndexedGraph H).Edge //
            e ∈ (simpleEdgeIndexedGraph H).incidentEdges v} := by
      change
        ((simpleEdgeIndexedGraph H).incidentEdges v).card =
          Fintype.card
            {e : (simpleEdgeIndexedGraph H).Edge //
              e ∈ (simpleEdgeIndexedGraph H).incidentEdges v}
      rw [Fintype.card_coe]
    _ ≤ Fintype.card
          {w : V // w ∈
            MaxDegreeAtMost.neighborFinset hdegree v} :=
      Fintype.card_le_of_injective f hf
    _ = (MaxDegreeAtMost.neighborFinset hdegree v).card := by
      rw [Fintype.card_coe]
    _ ≤ d := MaxDegreeAtMost.card_neighborFinset_le hdegree v

end simpleEdgeIndexedGraph

namespace GraphPath

/-- Vertices of `P` incident with an ambient edge leaving `P`. -/
noncomputable def externalVertices
    {H : _root_.SimpleGraph V} (P : GraphPath H) :
    Finset V := by
  classical
  exact P.vertexSet.filter fun v =>
    ∃ w : V, H.Adj v w ∧ w ∉ P.vertexSet

/-- Ambient branch vertices lying on `P`. -/
noncomputable def ambientBranchVertices
    {H : _root_.SimpleGraph V} (P : GraphPath H) :
    Finset V := by
  classical
  exact P.vertexSet.filter fun v => ¬ DegreeAtMost H v 2

theorem mem_externalVertices
    {H : _root_.SimpleGraph V} (P : GraphPath H) (v : V) :
    v ∈ externalVertices P ↔
      v ∈ P.vertexSet ∧
        ∃ w : V, H.Adj v w ∧ w ∉ P.vertexSet := by
  classical
  simp [externalVertices]

/-- An external-incidence vertex is either a path endpoint or has ambient
degree at least three. -/
theorem endpoint_or_not_degreeAtMost_two_of_mem_externalVertices
    {H : _root_.SimpleGraph V} (P : GraphPath H) {v : V}
    (hv : v ∈ externalVertices P) :
    P.IsEndpoint v ∨ ¬ DegreeAtMost H v 2 := by
  classical
  rcases (mem_externalVertices P v).1 hv with
    ⟨hvP, w, hvw, hwNot⟩
  by_cases hend : P.IsEndpoint v
  · exact Or.inl hend
  right
  intro hdegree
  have hvSource : v ≠ P.source := by
    intro h
    exact hend (Or.inl h)
  have hvTarget : v ≠ P.target := by
    intro h
    exact hend (Or.inr h)
  obtain ⟨a, b, hab, hva, hvb⟩ :=
    exists_two_distinct_path_neighbors_of_internal P
      hvP hvSource hvTarget
  rcases hdegree with ⟨N, hN, hNcard⟩
  have haN : a ∈ N :=
    (hN a).2 (GraphPath.edgeSet_subset_edgeSet P hva)
  have hbN : b ∈ N :=
    (hN b).2 (GraphPath.edgeSet_subset_edgeSet P hvb)
  have hwN : w ∈ N := (hN w).2 hvw
  have haP :
      a ∈ P.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet P hva).2
  have hbP :
      b ∈ P.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet P hvb).2
  have haw : a ≠ w := fun h => hwNot (h ▸ haP)
  have hbw : b ≠ w := fun h => hwNot (h ▸ hbP)
  have hthree : ({a, b, w} : Finset V).card = 3 := by
    simp [hab, haw, hbw]
  have hsubset : ({a, b, w} : Finset V) ⊆ N := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haN
    · exact hbN
    · exact hwN
  have := Finset.card_le_card hsubset
  omega

/-- A path has at most two endpoint exceptions in addition to its ambient
branch vertices. -/
theorem externalVertices_card_le_branch_add_two
    {H : _root_.SimpleGraph V} (P : GraphPath H) :
    (externalVertices P).card ≤
      (ambientBranchVertices P).card + 2 := by
  classical
  let B := ambientBranchVertices P
  have hsubset :
      externalVertices P ⊆ B ∪ {P.source, P.target} := by
    intro v hv
    rcases endpoint_or_not_degreeAtMost_two_of_mem_externalVertices P hv with
      hend | hbranch
    · rcases hend with rfl | rfl <;> simp [B]
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr
          ⟨(mem_externalVertices P v).1 hv |>.1, hbranch⟩))
  calc
    (externalVertices P).card ≤
        (B ∪ {P.source, P.target}).card :=
      Finset.card_le_card hsubset
    _ ≤ B.card + ({P.source, P.target} : Finset V).card :=
      Finset.card_union_le _ _
    _ ≤ B.card + 2 :=
      Nat.add_le_add_left Finset.card_le_two B.card

/-- Every boundary edge of the path vertex set is incident with one of its
external-incidence vertices. -/
theorem boundary_subset_external_incident
    {H : _root_.SimpleGraph V} (P : GraphPath H) :
    (simpleEdgeIndexedGraph H).boundary P.vertexSet ⊆
      (externalVertices P).biUnion
        (simpleEdgeIndexedGraph H).incidentEdges := by
  classical
  intro e he
  have hcross :=
    ((simpleEdgeIndexedGraph H).mem_boundary P.vertexSet e).1 he
  rcases hcross with hcross | hcross
  · have hadj :
        H.Adj
          ((simpleEdgeIndexedGraph H).left e)
          ((simpleEdgeIndexedGraph H).right e) := by
      have hother :=
        simpleEdgeIndexedGraph.other_adj H
          ((simpleEdgeIndexedGraph H).left e) e
          (((simpleEdgeIndexedGraph H).mem_incidentEdges _ e).2
            (Or.inl rfl))
      simpa [simpleEdgeIndexedGraph.other] using hother
    have hleft :
        (simpleEdgeIndexedGraph H).left e ∈ externalVertices P :=
      (mem_externalVertices P _).2
        ⟨hcross.1, _, hadj, hcross.2⟩
    exact Finset.mem_biUnion.mpr
      ⟨_, hleft,
        ((simpleEdgeIndexedGraph H).mem_incidentEdges _ e).2
          (Or.inl rfl)⟩
  · have hadj :
        H.Adj
          ((simpleEdgeIndexedGraph H).right e)
          ((simpleEdgeIndexedGraph H).left e) := by
      have hother :=
        simpleEdgeIndexedGraph.other_adj H
          ((simpleEdgeIndexedGraph H).right e) e
          (((simpleEdgeIndexedGraph H).mem_incidentEdges _ e).2
            (Or.inr rfl))
      unfold simpleEdgeIndexedGraph.other at hother
      rw [if_neg ((simpleEdgeIndexedGraph H).end_ne e)] at hother
      exact hother
    have hright :
        (simpleEdgeIndexedGraph H).right e ∈ externalVertices P :=
      (mem_externalVertices P _).2
        ⟨hcross.1, _, hadj, hcross.2⟩
    exact Finset.mem_biUnion.mpr
      ⟨_, hright,
        ((simpleEdgeIndexedGraph H).mem_incidentEdges _ e).2
          (Or.inr rfl)⟩

/-- Boundary-degree estimate for a path segment in a bounded-degree graph. -/
theorem boundary_card_le_degree_mul_branch_add_two
    {H : _root_.SimpleGraph V} (P : GraphPath H)
    {d : ℕ} (hdegree : MaxDegreeAtMost H d) :
    ((simpleEdgeIndexedGraph H).boundary P.vertexSet).card ≤
      d * ((ambientBranchVertices P).card + 2) := by
  classical
  calc
    ((simpleEdgeIndexedGraph H).boundary P.vertexSet).card ≤
        ((externalVertices P).biUnion
          (simpleEdgeIndexedGraph H).incidentEdges).card :=
      Finset.card_le_card (boundary_subset_external_incident P)
    _ ≤ ∑ v ∈ externalVertices P,
          (simpleEdgeIndexedGraph H).degree v := by
      simpa using Finset.card_biUnion_le
        (s := externalVertices P)
        (t := (simpleEdgeIndexedGraph H).incidentEdges)
    _ ≤ ∑ _v ∈ externalVertices P, d := by
      apply Finset.sum_le_sum
      intro v _hv
      exact simpleEdgeIndexedGraph.degree_le_of_maxDegreeAtMost
        H hdegree v
    _ = d * (externalVertices P).card := by
      simp [Nat.mul_comm]
    _ ≤ d * ((ambientBranchVertices P).card + 2) :=
      Nat.mul_le_mul_left d
        (externalVertices_card_le_branch_add_two P)

end GraphPath

/-- Named edge indices incident with at least one vertex of `U`. -/
noncomputable def incidentEdgeIndices
    (H : _root_.SimpleGraph V) (U : Finset V) :
    Finset (simpleEdgeIndexedGraph H).Edge :=
  U.biUnion (simpleEdgeIndexedGraph H).incidentEdges

theorem incidentEdgeIndices_card_le
    (H : _root_.SimpleGraph V) (U : Finset V)
    {d : ℕ} (hdegree : MaxDegreeAtMost H d) :
    (incidentEdgeIndices H U).card ≤ d * U.card := by
  classical
  calc
    (incidentEdgeIndices H U).card ≤
        ∑ v ∈ U, (simpleEdgeIndexedGraph H).degree v := by
      simpa [incidentEdgeIndices] using
        Finset.card_biUnion_le
          (s := U)
          (t := (simpleEdgeIndexedGraph H).incidentEdges)
    _ ≤ ∑ _v ∈ U, d := by
      exact Finset.sum_le_sum fun v _ =>
        simpleEdgeIndexedGraph.degree_le_of_maxDegreeAtMost H hdegree v
    _ = d * U.card := by simp [Nat.mul_comm]

end TreewidthSparsifier

end SimpleGraph

end Lax17Proofs
