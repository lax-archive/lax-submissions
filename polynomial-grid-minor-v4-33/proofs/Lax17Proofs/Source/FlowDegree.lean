import Lax17Proofs.Source.Degree
import Lax17Proofs.Source.Flow
import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Degree estimates for finite path flows

This file contains the self-contained flow bookkeeping used in the proof of
Chekuri--Chuzhoy Theorem 2.14.  The main estimate is that, in a graph of maximum
degree `Δ`, an edge-congestion bound `η` bounds the internal vertex load by
`Δ * η`.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T : Finset V}

/-- The finite set of graph edges incident with `v`. -/
noncomputable def incidentEdgeFinset (G : _root_.SimpleGraph V) (v : V) :
    Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e : Sym2 V => e ∈ G.edgeSet ∧ v ∈ e

theorem mem_incidentEdgeFinset (G : _root_.SimpleGraph V) (v : V) (e : Sym2 V) :
    e ∈ incidentEdgeFinset G v ↔ e ∈ G.edgeSet ∧ v ∈ e := by
  classical
  simp [incidentEdgeFinset]

/-- The incident-edge finset has size at most any certified maximum-degree
bound. -/
theorem incidentEdgeFinset_card_le_maxDegree {Δ : ℕ}
    (hdegree : MaxDegreeAtMost G Δ) (v : V) :
    (incidentEdgeFinset G v).card ≤ Δ := by
  classical
  let toNeighbor :
      {e : Sym2 V // e ∈ incidentEdgeFinset G v} →
        {u : V // u ∈ MaxDegreeAtMost.neighborFinset hdegree v} :=
    fun e =>
      let hinc : e.1 ∈ G.incidenceSet v := by
        have he := (mem_incidentEdgeFinset G v e.1).1 e.2
        exact ⟨he.1, he.2⟩
      ⟨G.otherVertexOfIncident hinc, by
        rw [MaxDegreeAtMost.mem_neighborFinset]
        exact (G.incidence_other_prop hinc :
          G.otherVertexOfIncident hinc ∈ G.neighborSet v)⟩
  have hinj : Function.Injective toNeighbor := by
    intro e f hef
    apply Subtype.ext
    have he_inc : e.1 ∈ G.incidenceSet v := by
      have he := (mem_incidentEdgeFinset G v e.1).1 e.2
      exact ⟨he.1, he.2⟩
    have hf_inc : f.1 ∈ G.incidenceSet v := by
      have hf := (mem_incidentEdgeFinset G v f.1).1 f.2
      exact ⟨hf.1, hf.2⟩
    have hother :
        G.otherVertexOfIncident he_inc =
          G.otherVertexOfIncident hf_inc :=
      congrArg Subtype.val hef
    have he_eq : e.1 = s(v, G.otherVertexOfIncident he_inc) :=
      (Sym2.other_spec' he_inc.2).symm
    have hf_eq : f.1 = s(v, G.otherVertexOfIncident hf_inc) :=
      (Sym2.other_spec' hf_inc.2).symm
    calc
      e.1 = s(v, G.otherVertexOfIncident he_inc) := he_eq
      _ = s(v, G.otherVertexOfIncident hf_inc) := by rw [hother]
      _ = f.1 := hf_eq.symm
  have hle := Fintype.card_le_of_injective toNeighbor hinj
  have hle' :
      (incidentEdgeFinset G v).card ≤
        (MaxDegreeAtMost.neighborFinset hdegree v).card := by
    simpa using hle
  exact hle'.trans (MaxDegreeAtMost.card_neighborFinset_le hdegree v)

namespace OrientedPathFlow

variable (F : OrientedPathFlow G S T)

/-- Total flow on edges incident with a vertex. -/
noncomputable def incidentEdgeLoad (F : OrientedPathFlow G S T) (v : V) : ℚ :=
  ∑ e ∈ incidentEdgeFinset G v, F.edgeLoad e

omit [Fintype V] in
theorem edgeLoad_nonneg (e : Sym2 V) :
    0 ≤ F.edgeLoad e := by
  classical
  unfold edgeLoad
  refine Finset.sum_nonneg ?_
  intro i _hi
  by_cases h : e ∈ (F.path i).edgeSet
  · simpa [h] using F.weight_nonneg i
  · simp [h]

theorem incidentEdgeLoad_nonneg (v : V) :
    0 ≤ F.incidentEdgeLoad v := by
  classical
  unfold incidentEdgeLoad
  exact Finset.sum_nonneg fun e _he => F.edgeLoad_nonneg e

omit [Fintype V] in
theorem internalVertexLoad_nonneg (v : V) :
    0 ≤ F.internalVertexLoad v := by
  classical
  unfold internalVertexLoad
  refine Finset.sum_nonneg ?_
  intro i _hi
  by_cases hInternal :
      v ∈ (F.path i).vertexSet ∧
        v ≠ (F.path i).source ∧ v ≠ (F.path i).target
  · simpa [hInternal] using F.weight_nonneg i
  · simp [hInternal]

omit [Fintype V] in
/-- Vertex load is bounded by the sum of source load, target load, and internal
vertex load.  This is the bookkeeping split used when converting edge
congestion to vertex congestion. -/
theorem vertexLoad_le_sourceLoad_add_targetLoad_add_internalVertexLoad (v : V) :
    F.vertexLoad v ≤
      F.sourceLoad v + F.targetLoad v + F.internalVertexLoad v := by
  classical
  unfold vertexLoad sourceLoad targetLoad internalVertexLoad
  calc
    (∑ i : F.Index, if v ∈ (F.path i).vertexSet then F.weight i else 0)
        ≤ ∑ i : F.Index,
            ((if (F.path i).source = v then F.weight i else 0) +
              (if (F.path i).target = v then F.weight i else 0) +
                (if v ∈ (F.path i).vertexSet ∧
                    v ≠ (F.path i).source ∧ v ≠ (F.path i).target
                  then F.weight i else 0)) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      let a : ℚ := if (F.path i).source = v then F.weight i else 0
      let b : ℚ := if (F.path i).target = v then F.weight i else 0
      let c : ℚ :=
        if v ∈ (F.path i).vertexSet ∧
            v ≠ (F.path i).source ∧ v ≠ (F.path i).target
        then F.weight i else 0
      have ha : 0 ≤ a := by
        dsimp [a]
        by_cases h : (F.path i).source = v
        · simpa [h] using F.weight_nonneg i
        · simp [h]
      have hb : 0 ≤ b := by
        dsimp [b]
        by_cases h : (F.path i).target = v
        · simpa [h] using F.weight_nonneg i
        · simp [h]
      have hc : 0 ≤ c := by
        dsimp [c]
        by_cases h :
            v ∈ (F.path i).vertexSet ∧
              v ≠ (F.path i).source ∧ v ≠ (F.path i).target
        · simpa [h] using F.weight_nonneg i
        · simp [h]
      change (if v ∈ (F.path i).vertexSet then F.weight i else 0) ≤ a + b + c
      by_cases hv : v ∈ (F.path i).vertexSet
      · by_cases hend : v = (F.path i).source ∨ v = (F.path i).target
        · rcases hend with hsrc | htgt
          · have ha_eq : a = F.weight i := by
              dsimp [a]
              simp [hsrc.symm]
            have hle : F.weight i ≤ a + b + c := by
              nlinarith
            simpa [hv] using hle
          · have hb_eq : b = F.weight i := by
              dsimp [b]
              simp [htgt.symm]
            have hle : F.weight i ≤ a + b + c := by
              nlinarith
            simpa [hv] using hle
        · have hInternal :
              v ∈ (F.path i).vertexSet ∧
                v ≠ (F.path i).source ∧ v ≠ (F.path i).target := by
            refine ⟨hv, ?_, ?_⟩
            · intro h
              exact hend (Or.inl h)
            · intro h
              exact hend (Or.inr h)
          have hc_eq : c = F.weight i := by
            dsimp [c]
            simp [hInternal]
          have hle : F.weight i ≤ a + b + c := by
            nlinarith
          simpa [hv] using hle
      · have hle : (0 : ℚ) ≤ a + b + c := by
          nlinarith
        simpa [hv] using hle
    _ = (∑ i : F.Index, if (F.path i).source = v then F.weight i else 0) +
          (∑ i : F.Index, if (F.path i).target = v then F.weight i else 0) +
            (∑ i : F.Index,
              if v ∈ (F.path i).vertexSet ∧
                  v ≠ (F.path i).source ∧ v ≠ (F.path i).target
              then F.weight i else 0) := by
      simp [Finset.sum_add_distrib, add_assoc]

/-- Internal load at a vertex is at most the total load on edges incident with
that vertex. -/
theorem internalVertexLoad_le_incidentEdgeLoad (v : V) :
    F.internalVertexLoad v ≤ F.incidentEdgeLoad v := by
  classical
  unfold internalVertexLoad incidentEdgeLoad edgeLoad
  calc
    (∑ i : F.Index,
        if v ∈ (F.path i).vertexSet ∧
            v ≠ (F.path i).source ∧ v ≠ (F.path i).target
        then F.weight i else 0)
        ≤ ∑ i : F.Index, ∑ e ∈ incidentEdgeFinset G v,
            if e ∈ (F.path i).edgeSet then F.weight i else 0 := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      by_cases hInternal :
          v ∈ (F.path i).vertexSet ∧
            v ≠ (F.path i).source ∧ v ≠ (F.path i).target
      · rcases hInternal with ⟨hvPath, hvSource, hvTarget⟩
        have hInternal' :
            v ∈ (F.path i).vertexSet ∧
              v ≠ (F.path i).source ∧ v ≠ (F.path i).target :=
          ⟨hvPath, hvSource, hvTarget⟩
        have hne : (F.path i).source ≠ (F.path i).target := by
          intro hst
          have hv_eq :=
            GraphPath.eq_source_of_source_eq_target_of_mem_vertexSet
              (F.path i) hst hvPath
          exact hvSource hv_eq
        rcases GraphPath.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
            (F.path i) hne hvPath with ⟨e, hePath, hve⟩
        have heGraph : e ∈ G.edgeSet :=
          GraphPath.edgeSet_subset_edgeSet (F.path i) hePath
        have heIncident : e ∈ incidentEdgeFinset G v :=
          (mem_incidentEdgeFinset G v e).2 ⟨heGraph, hve⟩
        have hnonneg :
            ∀ x ∈ incidentEdgeFinset G v,
              0 ≤ if x ∈ (F.path i).edgeSet then F.weight i else 0 := by
          intro x _hx
          by_cases hxPath : x ∈ (F.path i).edgeSet
          · simpa [hxPath] using F.weight_nonneg i
          · simp [hxPath]
        have hsingle :=
          Finset.single_le_sum hnonneg heIncident
        have hterm :
            (if e ∈ (F.path i).edgeSet then F.weight i else 0) =
              F.weight i := by
          simp [hePath]
        simpa [hInternal', hterm] using hsingle
      · have hnonneg :
            ∀ x ∈ incidentEdgeFinset G v,
              0 ≤ if x ∈ (F.path i).edgeSet then F.weight i else 0 := by
          intro x _hx
          by_cases hxPath : x ∈ (F.path i).edgeSet
          · simpa [hxPath] using F.weight_nonneg i
          · simp [hxPath]
        have hsum_nonneg :
            0 ≤ ∑ e ∈ incidentEdgeFinset G v,
              if e ∈ (F.path i).edgeSet then F.weight i else 0 :=
          Finset.sum_nonneg hnonneg
        simpa [hInternal] using hsum_nonneg
    _ = ∑ e ∈ incidentEdgeFinset G v, ∑ i : F.Index,
          if e ∈ (F.path i).edgeSet then F.weight i else 0 := by
      rw [Finset.sum_comm]

/-- An internal use of a vertex contributes to two distinct incident path
edges, so twice the internal vertex load is bounded by incident edge load. -/
theorem two_mul_internalVertexLoad_le_incidentEdgeLoad (v : V) :
    2 * F.internalVertexLoad v ≤ F.incidentEdgeLoad v := by
  classical
  unfold internalVertexLoad incidentEdgeLoad edgeLoad
  calc
    2 * (∑ i : F.Index,
        if v ∈ (F.path i).vertexSet ∧
            v ≠ (F.path i).source ∧ v ≠ (F.path i).target
        then F.weight i else 0)
        = ∑ i : F.Index,
            2 * (if v ∈ (F.path i).vertexSet ∧
                v ≠ (F.path i).source ∧ v ≠ (F.path i).target
              then F.weight i else 0) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i : F.Index, ∑ e ∈ incidentEdgeFinset G v,
            if e ∈ (F.path i).edgeSet then F.weight i else 0 := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      by_cases hInternal :
          v ∈ (F.path i).vertexSet ∧
            v ≠ (F.path i).source ∧ v ≠ (F.path i).target
      · rcases hInternal with ⟨hvPath, hvSource, hvTarget⟩
        have hInternal' :
            v ∈ (F.path i).vertexSet ∧
              v ≠ (F.path i).source ∧ v ≠ (F.path i).target :=
          ⟨hvPath, hvSource, hvTarget⟩
        rcases GraphPath.exists_two_edgeSet_incident_of_mem_vertexSet_of_not_endpoint
            (F.path i) hvPath hvSource hvTarget with
          ⟨e₁, he₁Path, hve₁, e₂, he₂Path, hve₂, he₁e₂⟩
        have he₁Graph : e₁ ∈ G.edgeSet :=
          GraphPath.edgeSet_subset_edgeSet (F.path i) he₁Path
        have he₂Graph : e₂ ∈ G.edgeSet :=
          GraphPath.edgeSet_subset_edgeSet (F.path i) he₂Path
        have he₁Incident : e₁ ∈ incidentEdgeFinset G v :=
          (mem_incidentEdgeFinset G v e₁).2 ⟨he₁Graph, hve₁⟩
        have he₂Incident : e₂ ∈ incidentEdgeFinset G v :=
          (mem_incidentEdgeFinset G v e₂).2 ⟨he₂Graph, hve₂⟩
        let pair : Finset (Sym2 V) := {e₁, e₂}
        have hpair_subset : pair ⊆ incidentEdgeFinset G v := by
          intro e he
          simp [pair] at he
          rcases he with rfl | rfl
          · exact he₁Incident
          · exact he₂Incident
        have hnonneg :
            ∀ x ∈ incidentEdgeFinset G v, x ∉ pair →
              0 ≤ if x ∈ (F.path i).edgeSet then F.weight i else 0 := by
          intro x _hx _hxnot
          by_cases hxPath : x ∈ (F.path i).edgeSet
          · simpa [hxPath] using F.weight_nonneg i
          · simp [hxPath]
        have hpair_le :
            (∑ e ∈ pair,
              if e ∈ (F.path i).edgeSet then F.weight i else 0) ≤
              ∑ e ∈ incidentEdgeFinset G v,
                if e ∈ (F.path i).edgeSet then F.weight i else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hpair_subset hnonneg
        have hpair_sum :
            (∑ e ∈ pair,
              if e ∈ (F.path i).edgeSet then F.weight i else 0) =
                F.weight i + F.weight i := by
          have he₁_not_mem_singleton : e₁ ∉ ({e₂} : Finset (Sym2 V)) := by
            simp [he₁e₂]
          have hpair_eq : pair = insert e₁ ({e₂} : Finset (Sym2 V)) := by
            ext e
            simp [pair]
          rw [hpair_eq, Finset.sum_insert he₁_not_mem_singleton]
          simp [he₁Path, he₂Path]
        have htwo :
            2 * F.weight i ≤ ∑ e ∈ incidentEdgeFinset G v,
              if e ∈ (F.path i).edgeSet then F.weight i else 0 := by
          calc
            2 * F.weight i = F.weight i + F.weight i := by ring
            _ = ∑ e ∈ pair,
                  if e ∈ (F.path i).edgeSet then F.weight i else 0 :=
                hpair_sum.symm
            _ ≤ ∑ e ∈ incidentEdgeFinset G v,
                  if e ∈ (F.path i).edgeSet then F.weight i else 0 :=
                hpair_le
        simpa [hInternal'] using htwo
      · have hnonneg :
            ∀ x ∈ incidentEdgeFinset G v,
              0 ≤ if x ∈ (F.path i).edgeSet then F.weight i else 0 := by
          intro x _hx
          by_cases hxPath : x ∈ (F.path i).edgeSet
          · simpa [hxPath] using F.weight_nonneg i
          · simp [hxPath]
        have hsum_nonneg :
            0 ≤ ∑ e ∈ incidentEdgeFinset G v,
              if e ∈ (F.path i).edgeSet then F.weight i else 0 :=
          Finset.sum_nonneg hnonneg
        simpa [hInternal] using hsum_nonneg
    _ = ∑ e ∈ incidentEdgeFinset G v, ∑ i : F.Index,
          if e ∈ (F.path i).edgeSet then F.weight i else 0 := by
      rw [Finset.sum_comm]

/-- Edge congestion and maximum degree bound total incident edge load. -/
theorem incidentEdgeLoad_le_maxDegree_mul_of_edgeCongestion
    {Δ : ℕ} {η : ℚ} (hdegree : MaxDegreeAtMost G Δ) (hη : 0 ≤ η)
    (hcongestion : F.EdgeCongestionAtMost η) (v : V) :
    F.incidentEdgeLoad v ≤ (Δ : ℚ) * η := by
  classical
  calc
    F.incidentEdgeLoad v
        ≤ ((incidentEdgeFinset G v).card : ℚ) * η := by
      unfold incidentEdgeLoad
      calc
        (∑ e ∈ incidentEdgeFinset G v, F.edgeLoad e)
            ≤ ∑ _e ∈ incidentEdgeFinset G v, η := by
          refine Finset.sum_le_sum ?_
          intro e he
          exact hcongestion e ((mem_incidentEdgeFinset G v e).1 he).1
        _ = ((incidentEdgeFinset G v).card : ℚ) * η := by
          simp [nsmul_eq_mul]
    _ ≤ (Δ : ℚ) * η := by
      have hcardNat := incidentEdgeFinset_card_le_maxDegree
        (G := G) hdegree v
      have hcardRat :
          ((incidentEdgeFinset G v).card : ℚ) ≤ (Δ : ℚ) := by
        exact_mod_cast hcardNat
      exact mul_le_mul_of_nonneg_right hcardRat hη

/-- An edge-congestion bound and a maximum-degree bound control internal vertex
load. -/
theorem internalVertexLoad_le_maxDegree_mul_of_edgeCongestion
    {Δ : ℕ} {η : ℚ} (hdegree : MaxDegreeAtMost G Δ) (hη : 0 ≤ η)
    (hcongestion : F.EdgeCongestionAtMost η) (v : V) :
    F.internalVertexLoad v ≤ (Δ : ℚ) * η := by
  classical
  calc
    F.internalVertexLoad v ≤ F.incidentEdgeLoad v :=
      F.internalVertexLoad_le_incidentEdgeLoad v
    _ ≤ (Δ : ℚ) * η :=
      F.incidentEdgeLoad_le_maxDegree_mul_of_edgeCongestion hdegree hη hcongestion v

/-- With the two-edge accounting for internal vertices, edge congestion bounds
internal vertex load by half of `Δ * η`. -/
theorem internalVertexLoad_le_half_maxDegree_mul_of_edgeCongestion
    {Δ : ℕ} {η : ℚ} (hdegree : MaxDegreeAtMost G Δ) (hη : 0 ≤ η)
    (hcongestion : F.EdgeCongestionAtMost η) (v : V) :
    F.internalVertexLoad v ≤ ((Δ : ℚ) * η) / 2 := by
  have htwice :
      2 * F.internalVertexLoad v ≤ (Δ : ℚ) * η :=
    (F.two_mul_internalVertexLoad_le_incidentEdgeLoad v).trans
      (F.incidentEdgeLoad_le_maxDegree_mul_of_edgeCongestion hdegree hη hcongestion v)
  nlinarith

/-- If each endpoint contributes at most one unit at `v`, then edge congestion
and maximum degree bound the total vertex load at `v`. -/
theorem vertexLoad_le_two_add_maxDegree_mul_of_edgeCongestion
    {Δ : ℕ} {η : ℚ} (hdegree : MaxDegreeAtMost G Δ) (hη : 0 ≤ η)
    (hcongestion : F.EdgeCongestionAtMost η) {v : V}
    (hsource : F.sourceLoad v ≤ 1) (htarget : F.targetLoad v ≤ 1) :
    F.vertexLoad v ≤ 2 + (Δ : ℚ) * η := by
  have hsplit := F.vertexLoad_le_sourceLoad_add_targetLoad_add_internalVertexLoad v
  have hinternal :=
    F.internalVertexLoad_le_maxDegree_mul_of_edgeCongestion
      hdegree hη hcongestion v
  calc
    F.vertexLoad v
        ≤ F.sourceLoad v + F.targetLoad v + F.internalVertexLoad v := hsplit
    _ ≤ 1 + 1 + (Δ : ℚ) * η := by
      exact add_le_add (add_le_add hsource htarget) hinternal
    _ = 2 + (Δ : ℚ) * η := by ring

omit [Fintype V] in
/-- For disjoint source and target terminal sets, the endpoint contribution at
any vertex is at most one unit. -/
theorem sourceLoad_add_targetLoad_le_one_of_disjoint
    (hunit : F.IsUnitFlow) (hdisj : Disjoint S T) (v : V) :
    F.sourceLoad v + F.targetLoad v ≤ 1 := by
  classical
  by_cases hvS : v ∈ S
  · have hvT : v ∉ T := Finset.disjoint_left.mp hdisj hvS
    rw [hunit.1 v hvS, F.targetLoad_eq_zero_of_not_mem hvT]
    norm_num
  · by_cases hvT : v ∈ T
    · rw [F.sourceLoad_eq_zero_of_not_mem hvS, hunit.2 v hvT]
      norm_num
    · rw [F.sourceLoad_eq_zero_of_not_mem hvS, F.targetLoad_eq_zero_of_not_mem hvT]
      norm_num

/-- In the disjoint-terminal case, edge congestion and maximum degree bound
total vertex load by `1 + Δ * η / 2`. -/
theorem vertexLoad_le_one_add_half_maxDegree_mul_of_edgeCongestion
    {Δ : ℕ} {η : ℚ} (hdegree : MaxDegreeAtMost G Δ) (hη : 0 ≤ η)
    (hcongestion : F.EdgeCongestionAtMost η) (hunit : F.IsUnitFlow)
    (hdisj : Disjoint S T) (v : V) :
    F.vertexLoad v ≤ 1 + ((Δ : ℚ) * η) / 2 := by
  have hsplit := F.vertexLoad_le_sourceLoad_add_targetLoad_add_internalVertexLoad v
  have hendpoint := F.sourceLoad_add_targetLoad_le_one_of_disjoint hunit hdisj v
  have hinternal :=
    F.internalVertexLoad_le_half_maxDegree_mul_of_edgeCongestion
      hdegree hη hcongestion v
  calc
    F.vertexLoad v
        ≤ F.sourceLoad v + F.targetLoad v + F.internalVertexLoad v := hsplit
    _ ≤ 1 + ((Δ : ℚ) * η) / 2 := by
      linarith

end OrientedPathFlow

end SimpleGraph

end Lax17Proofs
