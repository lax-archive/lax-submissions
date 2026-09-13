import Lax17Proofs.Source.MengerDefs

namespace Lax17Proofs

universe u v w

/-!
# Elementary operations on endpoint-clean path packings

These are the orientation and terminal-set bookkeeping operations used in the
two applications of Chekuri--Chuzhoy Lemma 2.19 in the many-leaves proof of
Theorem 4.6.
-/

namespace SimpleGraph
namespace EndpointCleanPathPacking


open scoped Classical

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {S T S' T' : Finset V}

@[simp] theorem toPathPacking_orient_path
    (P : EndpointCleanPathPacking G S T) (i : P.Index) :
    (P.toPathPacking.orient.path i) = P.path i := by
  classical
  change
    (P.path i).orient ((P.endpoint_clean i).connects) = P.path i
  simp [GraphPath.orient, (P.endpoint_clean i).source_mem,
    (P.endpoint_clean i).target_mem]

@[simp] theorem toPathPacking_sourceSet
    (P : EndpointCleanPathPacking G S T) :
    P.toPathPacking.sourceSet = P.sourceSet := by
  classical
  simp only [PathPacking.sourceSet, sourceSet, toPathPacking_orient_path]
  rfl

@[simp] theorem toPathPacking_targetSet
    (P : EndpointCleanPathPacking G S T) :
    P.toPathPacking.targetSet = P.targetSet := by
  classical
  simp only [PathPacking.targetSet, targetSet, toPathPacking_orient_path]
  rfl

/-- Reverse every path in an endpoint-clean packing. -/
noncomputable def reverse (P : EndpointCleanPathPacking G S T) :
    EndpointCleanPathPacking G T S where
  Index := P.Index
  path := fun i => (P.path i).reverse
  endpoint_clean := by
    intro i
    refine
      { source_mem := by simpa using (P.endpoint_clean i).target_mem
        target_mem := by simpa using (P.endpoint_clean i).source_mem
        left_eq_source := ?_
        right_eq_target := ?_ }
    · intro v hv hT
      have hv' : v ∈ (P.path i).vertexSet := by simpa using hv
      have := (P.endpoint_clean i).right_eq_target hv' hT
      simpa using this
    · intro v hv hS
      have hv' : v ∈ (P.path i).vertexSet := by simpa using hv
      have := (P.endpoint_clean i).left_eq_source hv' hS
      simpa using this
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

@[simp] theorem reverse_card (P : EndpointCleanPathPacking G S T) :
    P.reverse.card = P.card := rfl

@[simp] theorem reverse_sourceSet (P : EndpointCleanPathPacking G S T) :
    P.reverse.sourceSet = P.targetSet := by
  classical
  ext v
  simp [reverse, sourceSet, targetSet]

@[simp] theorem reverse_targetSet (P : EndpointCleanPathPacking G S T) :
    P.reverse.targetSet = P.sourceSet := by
  classical
  ext v
  simp [reverse, sourceSet, targetSet]

@[simp] theorem reverse_path_vertexSet
    (P : EndpointCleanPathPacking G S T) (i : P.reverse.Index) :
    (P.reverse.path i).vertexSet = (P.path i).vertexSet := by
  simp [reverse]

/-- Reinterpret the same paths with larger or otherwise changed terminal
sets, provided endpoint cleanliness for those terminal sets is supplied
explicitly. -/
noncomputable def copyTerminals
    (P : EndpointCleanPathPacking G S T)
    (hclean : ∀ i, (P.path i).EndpointClean S' T') :
    EndpointCleanPathPacking G S' T' where
  Index := P.Index
  path := P.path
  endpoint_clean := hclean
  node_disjoint := P.node_disjoint

@[simp] theorem copyTerminals_card
    (P : EndpointCleanPathPacking G S T)
    (hclean : ∀ i, (P.path i).EndpointClean S' T') :
    (P.copyTerminals hclean).card = P.card := rfl

@[simp] theorem copyTerminals_sourceSet
    (P : EndpointCleanPathPacking G S T)
    (hclean : ∀ i, (P.path i).EndpointClean S' T') :
    (P.copyTerminals hclean).sourceSet = P.sourceSet := rfl

@[simp] theorem copyTerminals_targetSet
    (P : EndpointCleanPathPacking G S T)
    (hclean : ∀ i, (P.path i).EndpointClean S' T') :
    (P.copyTerminals hclean).targetSet = P.targetSet := rfl

/-- Reorder a union used as the ambient source terminal set. -/
noncomputable def swapSourceUnion
    {A B C : Finset V}
    (P : EndpointCleanPathPacking G (A ∪ B) C) :
    EndpointCleanPathPacking G (B ∪ A) C :=
  P.copyTerminals (by
    intro i
    simpa [Finset.union_comm] using P.endpoint_clean i)

@[simp] theorem swapSourceUnion_card
    {A B C : Finset V}
    (P : EndpointCleanPathPacking G (A ∪ B) C) :
    P.swapSourceUnion.card = P.card := rfl

@[simp] theorem swapSourceUnion_sourceSet
    {A B C : Finset V}
    (P : EndpointCleanPathPacking G (A ∪ B) C) :
    P.swapSourceUnion.sourceSet = P.sourceSet := rfl

@[simp] theorem swapSourceUnion_targetSet
    {A B C : Finset V}
    (P : EndpointCleanPathPacking G (A ∪ B) C) :
    P.swapSourceUnion.targetSet = P.targetSet := rfl

/-- Convert an oriented perfect packing to an endpoint-clean packing when the
two endpoint-cleanliness conditions have already been established. -/
noncomputable def ofPerfect
    (P : PerfectPathPacking G S T)
    (hleft :
      ∀ i v, v ∈ (P.path i).vertexSet → v ∈ S → v = (P.path i).source)
    (hright :
      ∀ i v, v ∈ (P.path i).vertexSet → v ∈ T → v = (P.path i).target) :
    EndpointCleanPathPacking G S T where
  Index := P.Index
  path := P.path
  endpoint_clean := by
    intro i
    exact
      { source_mem := P.source_mem i
        target_mem := P.target_mem i
        left_eq_source := hleft i
        right_eq_target := hright i }
  node_disjoint := P.toPathPacking.node_disjoint

@[simp] theorem ofPerfect_card
    (P : PerfectPathPacking G S T)
    (hleft :
      ∀ i v, v ∈ (P.path i).vertexSet → v ∈ S → v = (P.path i).source)
    (hright :
      ∀ i v, v ∈ (P.path i).vertexSet → v ∈ T → v = (P.path i).target) :
    (ofPerfect P hleft hright).card = P.card := rfl

@[simp] theorem ofPerfect_sourceSet
    (P : PerfectPathPacking G S T)
    (hleft :
      ∀ i v, v ∈ (P.path i).vertexSet → v ∈ S → v = (P.path i).source)
    (hright :
      ∀ i v, v ∈ (P.path i).vertexSet → v ∈ T → v = (P.path i).target) :
    (ofPerfect P hleft hright).sourceSet = S := by
  apply Finset.eq_of_subset_of_card_le
    (ofPerfect P hleft hright).sourceSet_subset_left
  simpa [P.card_eq_left_card]

@[simp] theorem ofPerfect_targetSet
    (P : PerfectPathPacking G S T)
    (hleft :
      ∀ i v, v ∈ (P.path i).vertexSet → v ∈ S → v = (P.path i).source)
    (hright :
      ∀ i v, v ∈ (P.path i).vertexSet → v ∈ T → v = (P.path i).target) :
    (ofPerfect P hleft hright).targetSet = T := by
  apply Finset.eq_of_subset_of_card_le
    (ofPerfect P hleft hright).targetSet_subset_right
  simpa [P.card_eq_right_card]

/-- Every perfect packing is endpoint-clean for its designated terminal
sets.  If a path met another path's source or target internally, it would
contradict node-disjointness; bijectivity identifies the endpoint when the
terminal belongs to the same path. -/
noncomputable def ofPerfectCanonical
    (P : PerfectPathPacking G S T) :
    EndpointCleanPathPacking G S T :=
  ofPerfect P
    (by
      intro i v hv hvS
      rcases P.source_bijective.2 ⟨v, hvS⟩ with ⟨j, hj⟩
      have hsource : (P.path j).source = v :=
        congrArg Subtype.val hj
      by_cases hij : i = j
      · subst j
        exact hsource.symm
      · exact False.elim
          (Finset.disjoint_left.mp (P.node_disjoint hij) hv
            (by simpa [hsource] using
              GraphPath.source_mem_vertexSet (P.path j))))
    (by
      intro i v hv hvT
      rcases P.target_bijective.2 ⟨v, hvT⟩ with ⟨j, hj⟩
      have htarget : (P.path j).target = v :=
        congrArg Subtype.val hj
      by_cases hij : i = j
      · subst j
        exact htarget.symm
      · exact False.elim
          (Finset.disjoint_left.mp (P.node_disjoint hij) hv
            (by simpa [htarget] using
              GraphPath.target_mem_vertexSet (P.path j))))

/-- Regard a perfect packing as endpoint-clean after adjoining source
terminals avoided by every path. -/
noncomputable def ofPerfectWithExtraSources
    {E : Finset V}
    (P : PerfectPathPacking G S T)
    (havoid : ∀ i, Disjoint (P.path i).vertexSet E) :
    EndpointCleanPathPacking G (S ∪ E) T :=
  (ofPerfectCanonical P).copyTerminals (by
    intro i
    refine
      { source_mem := Finset.mem_union_left _ (P.source_mem i)
        target_mem := P.target_mem i
        left_eq_source := ?_
        right_eq_target := ?_ }
    · intro v hv hvSE
      rcases Finset.mem_union.mp hvSE with hvS | hvE
      · exact (ofPerfectCanonical P).endpoint_clean i |>.left_eq_source hv hvS
      · exact False.elim (Finset.disjoint_left.mp (havoid i) hv hvE)
    · intro v hv hvT
      exact (ofPerfectCanonical P).endpoint_clean i |>.right_eq_target hv hvT)

@[simp] theorem ofPerfectWithExtraSources_sourceSet
    {E : Finset V}
    (P : PerfectPathPacking G S T)
    (havoid : ∀ i, Disjoint (P.path i).vertexSet E) :
    (ofPerfectWithExtraSources P havoid).sourceSet = S := by
  change (ofPerfectCanonical P).sourceSet = S
  unfold ofPerfectCanonical
  apply ofPerfect_sourceSet

@[simp] theorem ofPerfectWithExtraSources_targetSet
    {E : Finset V}
    (P : PerfectPathPacking G S T)
    (havoid : ∀ i, Disjoint (P.path i).vertexSet E) :
    (ofPerfectWithExtraSources P havoid).targetSet = T := by
  change (ofPerfectCanonical P).targetSet = T
  unfold ofPerfectCanonical
  apply ofPerfect_targetSet

/-- Endpoint-clean conversion when the target terminal set is enlarged to a
region met only at the final endpoint. -/
noncomputable def ofPerfectWithExtraSourcesAndTargetRegion
    {E C : Finset V}
    (P : PerfectPathPacking G S T)
    (havoid : ∀ i, Disjoint (P.path i).vertexSet E)
    (hTC : T ⊆ C)
    (hSC : Disjoint S C)
    (hInternal : P.toPathPacking.InternallyDisjointFromSet C) :
    EndpointCleanPathPacking G (S ∪ E) C :=
  (ofPerfectCanonical P).copyTerminals (by
    intro i
    refine
      { source_mem := Finset.mem_union_left _ (P.source_mem i)
        target_mem := hTC (P.target_mem i)
        left_eq_source := ?_
        right_eq_target := ?_ }
    · intro v hv hvSE
      rcases Finset.mem_union.mp hvSE with hvS | hvE
      · exact (ofPerfectCanonical P).endpoint_clean i |>.left_eq_source hv hvS
      · exact False.elim (Finset.disjoint_left.mp (havoid i) hv hvE)
    · intro v hv hvC
      rcases hInternal i hv hvC with hvSource | hvTarget
      · exact False.elim
          (Finset.disjoint_left.mp hSC
            (by simpa [hvSource] using P.source_mem i) hvC)
      · exact hvTarget)

@[simp] theorem ofPerfectWithExtraSourcesAndTargetRegion_card
    {E C : Finset V}
    (P : PerfectPathPacking G S T)
    (havoid : ∀ i, Disjoint (P.path i).vertexSet E)
    (hTC : T ⊆ C)
    (hSC : Disjoint S C)
    (hInternal : P.toPathPacking.InternallyDisjointFromSet C) :
    (ofPerfectWithExtraSourcesAndTargetRegion
      P havoid hTC hSC hInternal).card = P.card := rfl

@[simp] theorem ofPerfectWithExtraSourcesAndTargetRegion_sourceSet
    {E C : Finset V}
    (P : PerfectPathPacking G S T)
    (havoid : ∀ i, Disjoint (P.path i).vertexSet E)
    (hTC : T ⊆ C)
    (hSC : Disjoint S C)
    (hInternal : P.toPathPacking.InternallyDisjointFromSet C) :
    (ofPerfectWithExtraSourcesAndTargetRegion
      P havoid hTC hSC hInternal).sourceSet = S := by
  change (ofPerfectCanonical P).sourceSet = S
  unfold ofPerfectCanonical
  apply ofPerfect_sourceSet

@[simp] theorem ofPerfectWithExtraSourcesAndTargetRegion_targetSet
    {E C : Finset V}
    (P : PerfectPathPacking G S T)
    (havoid : ∀ i, Disjoint (P.path i).vertexSet E)
    (hTC : T ⊆ C)
    (hSC : Disjoint S C)
    (hInternal : P.toPathPacking.InternallyDisjointFromSet C) :
    (ofPerfectWithExtraSourcesAndTargetRegion
      P havoid hTC hSC hInternal).targetSet = T := by
  change (ofPerfectCanonical P).targetSet = T
  unfold ofPerfectCanonical
  apply ofPerfect_targetSet

@[simp] theorem ofPerfectCanonical_card
    (P : PerfectPathPacking G S T) :
    (ofPerfectCanonical P).card = P.card := rfl

@[simp] theorem ofPerfectCanonical_sourceSet
    (P : PerfectPathPacking G S T) :
    (ofPerfectCanonical P).sourceSet = S :=
  ofPerfect_sourceSet P _ _

@[simp] theorem ofPerfectCanonical_targetSet
    (P : PerfectPathPacking G S T) :
    (ofPerfectCanonical P).targetSet = T :=
  ofPerfect_targetSet P _ _

end EndpointCleanPathPacking

namespace PerfectPathPacking

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Mutually node-disjoint perfect packings have disjoint designated source
sets. -/
theorem source_disjoint_of_mutuallyNodeDisjoint
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (h : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    Disjoint S₁ S₂ := by
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  rcases P.source_bijective.2 ⟨v, hv₁⟩ with ⟨i, hi⟩
  rcases Q.source_bijective.2 ⟨v, hv₂⟩ with ⟨j, hj⟩
  have hi' : (P.path i).source = v := congrArg Subtype.val hi
  have hj' : (Q.path j).source = v := congrArg Subtype.val hj
  exact Finset.disjoint_left.mp (h i j)
    (by simpa [hi'] using GraphPath.source_mem_vertexSet (P.path i))
    (by simpa [hj'] using GraphPath.source_mem_vertexSet (Q.path j))

/-- Mutually node-disjoint perfect packings have disjoint designated target
sets. -/
theorem target_disjoint_of_mutuallyNodeDisjoint
    {S₁ T₁ S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂)
    (h : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    Disjoint T₁ T₂ := by
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  rcases P.target_bijective.2 ⟨v, hv₁⟩ with ⟨i, hi⟩
  rcases Q.target_bijective.2 ⟨v, hv₂⟩ with ⟨j, hj⟩
  have hi' : (P.path i).target = v := congrArg Subtype.val hi
  have hj' : (Q.path j).target = v := congrArg Subtype.val hj
  exact Finset.disjoint_left.mp (h i j)
    (by simpa [hi'] using GraphPath.target_mem_vertexSet (P.path i))
    (by simpa [hj'] using GraphPath.target_mem_vertexSet (Q.path j))

end PerfectPathPacking
end SimpleGraph

end Lax17Proofs
