import Lax17Proofs.Source.FlowDefs

namespace Lax17Proofs

universe u v w

/-!
# Elementary API for finite path flows

This file proves basic algebraic facts about the concrete path-flow structure
from `FlowDefs`.  Substantive external theorems such as max-flow/min-cut and
integral-flow decomposition live in `FlowContract`.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T : Finset V}

namespace OrientedPathFlow

/-- The unit path flow obtained from a node-disjoint path packing, orienting
each path from `S` to `T`. -/
noncomputable def ofPathPacking (P : PathPacking G S T) :
    OrientedPathFlow G S T where
  Index := P.Index
  path := fun i => (P.path i).orient (P.connects i)
  source_mem := fun i => GraphPath.orient_source_mem (P.path i) (P.connects i)
  target_mem := fun i => GraphPath.orient_target_mem (P.path i) (P.connects i)
  weight := fun _ => 1
  weight_nonneg := fun _ => by norm_num

@[simp] theorem ofPathPacking_value (P : PathPacking G S T) :
    (ofPathPacking P).value = P.card := by
  classical
  simp [ofPathPacking, value, PathPacking.card]
  rfl

private theorem ofPathPacking_source_injective (P : PathPacking G S T) :
    Function.Injective fun i : P.Index =>
      ((P.path i).orient (P.connects i)).source := by
  intro i j hij
  by_contra hne
  have hdisj := P.orient.node_disjoint hne
  have hi :
      (P.orient.path i).source ∈ (P.orient.path i).vertexSet :=
    GraphPath.source_mem_vertexSet (P.orient.path i)
  have hj :
      (P.orient.path i).source ∈ (P.orient.path j).vertexSet := by
    have hj' := GraphPath.source_mem_vertexSet (P.orient.path j)
    change (P.orient.path i).source = (P.orient.path j).source at hij
    rw [← hij] at hj'
    exact hj'
  exact Finset.disjoint_left.mp hdisj hi hj

/-- A packing using every source terminal gives the corresponding unit flow
exactly one unit of load at each source. -/
theorem ofPathPacking_sourceLoadExactlyOne (P : PathPacking G S T)
    (hcard : P.card = S.card) :
    (ofPathPacking P).SourceLoadExactlyOne := by
  classical
  intro v hvS
  have hvUsed : v ∈ P.sourceSet := by
    rw [P.sourceSet_eq_left_of_card_eq hcard]
    exact hvS
  rcases P.exists_orient_source_eq_of_mem_sourceSet hvUsed with ⟨i, hi⟩
  rw [sourceLoad]
  change (∑ j : P.Index,
    if (P.orient.path j).source = v then (1 : ℚ) else 0) = 1
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _hj hji
    have hne : (P.orient.path j).source ≠ v := by
      intro hjv
      have hji' : j = i :=
        ofPathPacking_source_injective P (hjv.trans hi.symm)
      exact hji hji'
    simp [hne]
  · simp

/-- A packing using every target terminal gives the corresponding unit flow
exactly one unit of load at each target. -/
theorem ofPathPacking_targetLoadExactlyOne (P : PathPacking G S T)
    (hcard : P.card = T.card) :
    (ofPathPacking P).TargetLoadExactlyOne := by
  classical
  intro v hvT
  have hvUsed : v ∈ P.targetSet := by
    rw [P.targetSet_eq_right_of_card_eq hcard]
    exact hvT
  rcases P.exists_orient_target_eq_of_mem_targetSet hvUsed with ⟨i, hi⟩
  rw [targetLoad]
  change (∑ j : P.Index,
    if (P.orient.path j).target = v then (1 : ℚ) else 0) = 1
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _hj hji
    have hne : (P.orient.path j).target ≠ v := by
      intro hjv
      have hji' : j = i :=
        P.orient_target_injective (hjv.trans hi.symm)
      exact hji hji'
    simp [hne]
  · simp

/-- Node-disjoint paths carrying unit weight have vertex congestion at most
one, including at their endpoints. -/
theorem ofPathPacking_vertexCongestionAtMost_one (P : PathPacking G S T) :
    (ofPathPacking P).VertexCongestionAtMost 1 := by
  classical
  intro v
  by_cases hv : ∃ i : P.Index, v ∈ (P.path i).vertexSet
  · rcases hv with ⟨i, hi⟩
    rw [vertexLoad]
    simp only [ofPathPacking, GraphPath.orient_vertexSet]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _hj hji
      have hnot : v ∉ (P.path j).vertexSet := by
        intro hj
        exact Finset.disjoint_left.mp (P.node_disjoint hji) hj hi
      simp [hnot]
    · simp
  · rw [vertexLoad]
    simp only [ofPathPacking, GraphPath.orient_vertexSet]
    have hnot : ∀ j : P.Index, v ∉ (P.path j).vertexSet := by
      intro j hj
      exact hv ⟨j, hj⟩
    simp [hnot]

/-- A full node-disjoint path packing induces a unit flow with vertex
congestion at most one. -/
theorem ofPathPacking_isUnitFlow_and_vertexCongestionAtMost_one
    (P : PathPacking G S T)
    (hsource : P.card = S.card) (htarget : P.card = T.card) :
    (ofPathPacking P).IsUnitFlow ∧
      (ofPathPacking P).VertexCongestionAtMost 1 :=
  ⟨⟨ofPathPacking_sourceLoadExactlyOne P hsource,
    ofPathPacking_targetLoadExactlyOne P htarget⟩,
    ofPathPacking_vertexCongestionAtMost_one P⟩

/-- The unit path flow obtained from an edge-disjoint path packing, orienting
each path from `S` to `T`. -/
noncomputable def ofEdgePathPacking (P : EdgePathPacking G S T) :
    OrientedPathFlow G S T where
  Index := P.Index
  path := fun i => (P.path i).orient (P.connects i)
  source_mem := fun i => GraphPath.orient_source_mem (P.path i) (P.connects i)
  target_mem := fun i => GraphPath.orient_target_mem (P.path i) (P.connects i)
  weight := fun _ => 1
  weight_nonneg := fun _ => by norm_num

@[simp] theorem ofEdgePathPacking_value (P : EdgePathPacking G S T) :
    (ofEdgePathPacking P).value = P.card := by
  classical
  simp [ofEdgePathPacking, value, EdgePathPacking.card]
  rfl

/-- Re-express the value of a path flow as the sum of its source loads over the
source terminal set. -/
theorem value_eq_sum_sourceLoad (F : OrientedPathFlow G S T) :
    F.value = ∑ v ∈ S, F.sourceLoad v := by
  classical
  calc
    F.value = ∑ i : F.Index, ∑ v ∈ S,
        if (F.path i).source = v then F.weight i else 0 := by
      simp only [value]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Finset.sum_eq_single (F.path i).source]
      · simp
      · intro b hb hne
        have hne' : (F.path i).source ≠ b := fun h => hne h.symm
        simp [hne']
      · intro hnot
        exact False.elim (hnot (F.source_mem i))
    _ = ∑ v ∈ S, F.sourceLoad v := by
      rw [Finset.sum_comm]
      rfl

/-- Re-express the value of a path flow as the sum of its target loads over the
target terminal set. -/
theorem value_eq_sum_targetLoad (F : OrientedPathFlow G S T) :
    F.value = ∑ v ∈ T, F.targetLoad v := by
  classical
  calc
    F.value = ∑ i : F.Index, ∑ v ∈ T,
        if (F.path i).target = v then F.weight i else 0 := by
      simp only [value]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Finset.sum_eq_single (F.path i).target]
      · simp
      · intro b hb hne
        have hne' : (F.path i).target ≠ b := fun h => hne h.symm
        simp [hne']
      · intro hnot
        exact False.elim (hnot (F.target_mem i))
    _ = ∑ v ∈ T, F.targetLoad v := by
      rw [Finset.sum_comm]
      rfl

/-- A unit flow has value equal to the number of source terminals. -/
theorem value_eq_card_source_of_sourceLoadExactlyOne
    (F : OrientedPathFlow G S T) (h : F.SourceLoadExactlyOne) :
    F.value = S.card := by
  classical
  rw [F.value_eq_sum_sourceLoad]
  calc
    (∑ v ∈ S, F.sourceLoad v) = ∑ v ∈ S, (1 : ℚ) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simp [h v hv]
    _ = S.card := by
      simp

/-- A unit flow has value equal to the number of target terminals. -/
theorem value_eq_card_target_of_targetLoadExactlyOne
    (F : OrientedPathFlow G S T) (h : F.TargetLoadExactlyOne) :
    F.value = T.card := by
  classical
  rw [F.value_eq_sum_targetLoad]
  calc
    (∑ v ∈ T, F.targetLoad v) = ∑ v ∈ T, (1 : ℚ) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simp [h v hv]
    _ = T.card := by
      simp

/-- Vertices outside the source side have zero source load. -/
theorem sourceLoad_eq_zero_of_not_mem
    (F : OrientedPathFlow G S T) {v : V} (hv : v ∉ S) :
    F.sourceLoad v = 0 := by
  classical
  unfold sourceLoad
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hne : (F.path i).source ≠ v := by
    intro h
    exact hv (by simpa [h] using F.source_mem i)
  simp [hne]

/-- Vertices outside the target side have zero target load. -/
theorem targetLoad_eq_zero_of_not_mem
    (F : OrientedPathFlow G S T) {v : V} (hv : v ∉ T) :
    F.targetLoad v = 0 := by
  classical
  unfold targetLoad
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hne : (F.path i).target ≠ v := by
    intro h
    exact hv (by simpa [h] using F.target_mem i)
  simp [hne]

/-- A unit source-load condition bounds source load at every vertex by one. -/
theorem sourceLoad_le_one_of_sourceLoadExactlyOne
    (F : OrientedPathFlow G S T) (h : F.SourceLoadExactlyOne) (v : V) :
    F.sourceLoad v ≤ 1 := by
  classical
  by_cases hv : v ∈ S
  · simp [h v hv]
  · rw [F.sourceLoad_eq_zero_of_not_mem hv]
    norm_num

/-- A unit target-load condition bounds target load at every vertex by one. -/
theorem targetLoad_le_one_of_targetLoadExactlyOne
    (F : OrientedPathFlow G S T) (h : F.TargetLoadExactlyOne) (v : V) :
    F.targetLoad v ≤ 1 := by
  classical
  by_cases hv : v ∈ T
  · simp [h v hv]
  · rw [F.targetLoad_eq_zero_of_not_mem hv]
    norm_num

/-- View a path flow inside a same-vertex supergraph. -/
noncomputable def mapLe (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    OrientedPathFlow H S T where
  Index := F.Index
  path := fun i => (F.path i).mapLe hGH
  source_mem := F.source_mem
  target_mem := F.target_mem
  weight := F.weight
  weight_nonneg := F.weight_nonneg

omit [DecidableEq V] in
@[simp] theorem mapLe_value (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (F.mapLe hGH).value = F.value := by
  rfl

@[simp] theorem mapLe_sourceLoad (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) (v : V) :
    (F.mapLe hGH).sourceLoad v = F.sourceLoad v := by
  rfl

@[simp] theorem mapLe_targetLoad (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) (v : V) :
    (F.mapLe hGH).targetLoad v = F.targetLoad v := by
  rfl

@[simp] theorem mapLe_vertexLoad (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) (v : V) :
    (F.mapLe hGH).vertexLoad v = F.vertexLoad v := by
  classical
  unfold vertexLoad mapLe
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [GraphPath.mapLe_vertexSet]

theorem mapLe_sourceLoadExactlyOne (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H)
    (h : F.SourceLoadExactlyOne) :
    (F.mapLe hGH).SourceLoadExactlyOne := by
  intro v hv
  simpa using h v hv

theorem mapLe_targetLoadExactlyOne (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H)
    (h : F.TargetLoadExactlyOne) :
    (F.mapLe hGH).TargetLoadExactlyOne := by
  intro v hv
  simpa using h v hv

theorem mapLe_isUnitFlow (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H)
    (h : F.IsUnitFlow) :
    (F.mapLe hGH).IsUnitFlow :=
  ⟨F.mapLe_sourceLoadExactlyOne hGH h.1,
    F.mapLe_targetLoadExactlyOne hGH h.2⟩

theorem mapLe_vertexCongestionAtMost (F : OrientedPathFlow G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) {η : ℚ}
    (hη : F.VertexCongestionAtMost η) :
    (F.mapLe hGH).VertexCongestionAtMost η := by
  intro v
  simpa using hη v

/-- Scaling a finite path flow by a nonnegative rational factor. -/
noncomputable def scale (F : OrientedPathFlow G S T) (c : ℚ) (hc : 0 ≤ c) :
    OrientedPathFlow G S T where
  Index := F.Index
  path := F.path
  source_mem := F.source_mem
  target_mem := F.target_mem
  weight := fun i => c * F.weight i
  weight_nonneg := fun i => mul_nonneg hc (F.weight_nonneg i)

omit [DecidableEq V] in
@[simp] theorem scale_value (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) :
    (F.scale c hc).value = c * F.value := by
  classical
  simp only [scale, value]
  rw [Finset.mul_sum]
  rfl

@[simp] theorem scale_sourceLoad (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) (v : V) :
    (F.scale c hc).sourceLoad v = c * F.sourceLoad v := by
  classical
  simp only [scale, sourceLoad]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : (F.path i).source = v <;> simp [h]

@[simp] theorem scale_targetLoad (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) (v : V) :
    (F.scale c hc).targetLoad v = c * F.targetLoad v := by
  classical
  simp only [scale, targetLoad]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : (F.path i).target = v <;> simp [h]

@[simp] theorem scale_edgeLoad (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) (e : Sym2 V) :
    (F.scale c hc).edgeLoad e = c * F.edgeLoad e := by
  classical
  simp only [scale, edgeLoad]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : e ∈ (F.path i).edgeSet <;> simp [h]

@[simp] theorem scale_vertexLoad (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) (v : V) :
    (F.scale c hc).vertexLoad v = c * F.vertexLoad v := by
  classical
  simp only [scale, vertexLoad]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : v ∈ (F.path i).vertexSet <;> simp [h]

/-- Scaling preserves source unit constraints after the expected rescaling. -/
theorem scale_sourceLoad_eq
    (F : OrientedPathFlow G S T) (c : ℚ) (hc : 0 ≤ c)
    (h : F.SourceLoadExactlyOne) :
    ∀ v ∈ S, (F.scale c hc).sourceLoad v = c := by
  intro v hv
  simp [h v hv]

/-- Scaling an edge-congestion bound. -/
theorem scale_edgeCongestionAtMost
    (F : OrientedPathFlow G S T) {η c : ℚ} (hc : 0 ≤ c)
    (hη : F.EdgeCongestionAtMost η) :
    (F.scale c hc).EdgeCongestionAtMost (c * η) := by
  intro e he
  rw [scale_edgeLoad]
  exact mul_le_mul_of_nonneg_left (hη e he) hc

/-- Scaling a vertex-congestion bound. -/
theorem scale_vertexCongestionAtMost
    (F : OrientedPathFlow G S T) {η c : ℚ} (hc : 0 ≤ c)
    (hη : F.VertexCongestionAtMost η) :
    (F.scale c hc).VertexCongestionAtMost (c * η) := by
  intro v
  rw [scale_vertexLoad]
  exact mul_le_mul_of_nonneg_left (hη v) hc

end OrientedPathFlow

end SimpleGraph

end Lax17Proofs
