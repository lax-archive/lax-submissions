import Lax17Proofs.Source.TreewidthSparsifierTheorem51Segments

namespace Lax17Proofs

universe u v w

/-!
# Exact concatenated red rails

The preliminary `railPath` construction only retained a cycle-erased
concatenation.  Step 2 of Theorem 5.1 needs the stronger fact that every local
red piece occurs, in order, on the global rail.  The path-of-sets separation
axioms imply that a new connector or local piece meets the preceding prefix
only at its glue endpoint.  This module performs that exact concatenation.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- An exact rail through record `n`, together with the constituent-piece
inclusions needed by the segmentation. -/
structure ExactRailPrefix
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (n : ℕ) (hn : n < E.finalState.records.length) where
  path : GraphPath (E.redSupport hbudget)
  source_eq : path.source = E.initialTerminal hrecords x
  target_eq : path.target = (E.localRedPath ⟨n, hn⟩ x).target
  vertex_mem :
    ∀ ⦃v : V⦄, v ∈ path.vertexSet →
      (∃ j : Fin E.finalState.records.length,
          j.1 ≤ n ∧ v ∈ (E.localRedPath j x).vertexSet) ∨
        (∃ k : Fin (E.finalState.records.length - 1),
          k.1 < n ∧
            v ∈ (E.connectorPath hbudget k x).vertexSet)
  local_subset :
    ∀ (j : Fin E.finalState.records.length), j.1 ≤ n →
      (E.localRedPathInRedSupport hbudget j x).vertexSet ⊆
        path.vertexSet
  connector_subset :
    ∀ (k : Fin (E.finalState.records.length - 1)), k.1 < n →
      (E.connectorPathInRedSupport hbudget k x).vertexSet ⊆
        path.vertexSet

/-- Exact concatenation of the local red pieces and connector pieces through
record `n`. -/
noncomputable def exactRailPrefix
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    (n : ℕ) → (hn : n < E.finalState.records.length) →
      ExactRailPrefix E hbudget hrecords x n hn
  | 0, hn => by
      let j : Fin E.finalState.records.length := ⟨0, hn⟩
      let localPiece := E.localRedPathInRedSupport hbudget j x
      refine {
        path := localPiece
        source_eq := ?_
        target_eq := ?_
        vertex_mem := ?_
        local_subset := ?_
        connector_subset := ?_
      }
      · rw [show localPiece.source = (E.localRedPath j x).source by
          simp [localPiece],
          E.localRedPath_source]
        apply congrArg Subtype.val
        change
          (E.recordAt j).label x =
            (E.recordAt (E.firstRecord hrecords)).label x
        congr 2
      · simp [localPiece, j]
      · intro v hv
        left
        refine ⟨j, by simp [j], ?_⟩
        simpa [localPiece] using hv
      · intro k hk v hv
        have hkj : k = j := by
          apply Fin.ext
          simp [j]
          omega
        subst k
        simpa [localPiece] using hv
      · intro k hk
        omega
  | n + 1, hn => by
      let prevIndex : Fin E.finalState.records.length :=
        ⟨n, by omega⟩
      let gapIndex : Fin (E.finalState.records.length - 1) :=
        ⟨n, by omega⟩
      let nextIndex : Fin E.finalState.records.length := ⟨n + 1, hn⟩
      let previous := E.exactRailPrefix hbudget hrecords x n (by omega)
      let connector := E.connectorPathInRedSupport hbudget gapIndex x
      let localPiece := E.localRedPathInRedSupport hbudget nextIndex x
      have hPreviousConnector :
          previous.path.target = connector.source := by
        rw [previous.target_eq]
        simp only [connector,
          E.connectorPathInRedSupport_source,
          E.connectorPath_source]
        change
          (E.localRedPath prevIndex x).target =
            (E.localRedPath (E.gapRecord gapIndex) x).target
        congr 2
      have hinterPreviousConnector :
          ∀ ⦃v : V⦄,
            v ∈ previous.path.vertexSet →
              v ∈ connector.vertexSet →
                v = previous.path.target := by
        intro v hvPrevious hvConnector
        have hvConnector' :
            v ∈ (E.connectorPath hbudget gapIndex x).vertexSet := by
          simpa [connector] using hvConnector
        rcases previous.vertex_mem hvPrevious with
          ⟨j, hjn, hvLocal⟩ | ⟨k, hkn, hvOldConnector⟩
        · rcases E.localRedPath_connectorPath_intersection
              hbudget j gapIndex x hvLocal hvConnector' with
            hleft | hright
          · have hjPrev : j = prevIndex := by
              exact hleft.1.trans (by rfl)
            subst j
            exact hleft.2.1.trans previous.target_eq.symm
          · have hjval := congrArg Fin.val hright.1
            dsimp [nextRecord, gapIndex] at hjval
            omega
        · have hkgap : k = gapIndex :=
            E.connectorPath_gap_unique hbudget
              hvOldConnector hvConnector'
          have hkval := congrArg Fin.val hkgap
          dsimp [gapIndex] at hkval
          omega
      let throughConnector :=
        previous.path.appendWithEqOfInterSubsetTarget connector
          hPreviousConnector hinterPreviousConnector
      have hConnectorLocal :
          throughConnector.target = localPiece.source := by
        change connector.target = localPiece.source
        simp only [connector, localPiece,
          E.connectorPathInRedSupport_target,
          E.localRedPathInRedSupport_source,
          E.connectorPath_target]
        rw [← E.localRedPath_source (E.nextRecord gapIndex) x]
        congr 2
      have hinterThroughLocal :
          ∀ ⦃v : V⦄,
            v ∈ throughConnector.vertexSet →
              v ∈ localPiece.vertexSet →
                v = throughConnector.target := by
        intro v hvThrough hvLocal
        have hvUnion :
            v ∈ previous.path.vertexSet ∪ connector.vertexSet := by
          exact previous.path.appendWithEq_vertexSet_subset connector
            hPreviousConnector
            (previous.path.appendWithEq_isPath_of_inter_subset_target
              connector hPreviousConnector hinterPreviousConnector)
            hvThrough
        have hvLocal' :
            v ∈ (E.localRedPath nextIndex x).vertexSet := by
          simpa [localPiece] using hvLocal
        rcases Finset.mem_union.mp hvUnion with hvPrevious | hvConnector
        · rcases previous.vertex_mem hvPrevious with
            ⟨j, hjn, hvOldLocal⟩ | ⟨k, hkn, hvOldConnector⟩
          · have hjnext :=
              E.localRedPath_record_unique hbudget hvOldLocal hvLocal'
            have hjval := congrArg Fin.val hjnext
            dsimp [nextIndex] at hjval
            omega
          · rcases E.localRedPath_connectorPath_intersection
                hbudget nextIndex k x hvLocal' hvOldConnector with
              hleft | hright
            · have hval := congrArg Fin.val hleft.1
              dsimp [nextIndex, gapRecord] at hval
              omega
            · have hval := congrArg Fin.val hright.1
              dsimp [nextIndex, nextRecord] at hval
              omega
        · have hvConnector' :
              v ∈ (E.connectorPath hbudget gapIndex x).vertexSet := by
            simpa [connector] using hvConnector
          rcases E.localRedPath_connectorPath_intersection
              hbudget nextIndex gapIndex x hvLocal' hvConnector' with
            hleft | hright
          · have hval := congrArg Fin.val hleft.1
            dsimp [nextIndex, gapIndex, gapRecord] at hval
            omega
          · change v = connector.target
            exact hright.2.2
      let completed :=
        throughConnector.appendWithEqOfInterSubsetTarget localPiece
          hConnectorLocal hinterThroughLocal
      refine {
        path := completed
        source_eq := ?_
        target_eq := ?_
        vertex_mem := ?_
        local_subset := ?_
        connector_subset := ?_
      }
      · simpa [completed, throughConnector] using previous.source_eq
      · change localPiece.target = (E.localRedPath nextIndex x).target
        simp [localPiece]
      · intro v hv
        have hvOuter :
            v ∈ throughConnector.vertexSet ∪ localPiece.vertexSet := by
          exact throughConnector.appendWithEq_vertexSet_subset localPiece
            hConnectorLocal
            (throughConnector.appendWithEq_isPath_of_inter_subset_target
              localPiece hConnectorLocal hinterThroughLocal) hv
        rcases Finset.mem_union.mp hvOuter with hvThrough | hvLocal
        · have hvInner :
              v ∈ previous.path.vertexSet ∪ connector.vertexSet := by
            exact previous.path.appendWithEq_vertexSet_subset connector
              hPreviousConnector
              (previous.path.appendWithEq_isPath_of_inter_subset_target
                connector hPreviousConnector hinterPreviousConnector)
              hvThrough
          rcases Finset.mem_union.mp hvInner with hvPrevious | hvConnector
          · rcases previous.vertex_mem hvPrevious with h | h
            · left
              rcases h with ⟨j, hj, hvj⟩
              exact ⟨j, hj.trans (by omega), hvj⟩
            · right
              rcases h with ⟨k, hk, hvk⟩
              exact ⟨k, hk.trans (by omega), hvk⟩
          · right
            refine ⟨gapIndex, by simp [gapIndex], ?_⟩
            simpa [connector] using hvConnector
        · left
          refine ⟨nextIndex, by simp [nextIndex], ?_⟩
          simpa [localPiece] using hvLocal
      · intro j hj v hv
        by_cases hold : j.1 ≤ n
        · have hvPrevious :
              v ∈ previous.path.vertexSet :=
            previous.local_subset j hold hv
          have hvThrough :
              v ∈ throughConnector.vertexSet :=
            previous.path.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
              connector hPreviousConnector hinterPreviousConnector hvPrevious
          exact
            throughConnector.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
              localPiece hConnectorLocal hinterThroughLocal hvThrough
        · have hjnext : j = nextIndex := by
            apply Fin.ext
            dsimp [nextIndex]
            omega
          subst j
          have hvLocal : v ∈ localPiece.vertexSet := by
            simpa [localPiece] using hv
          exact
            throughConnector.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
              localPiece hConnectorLocal hinterThroughLocal hvLocal
      · intro k hk v hv
        by_cases hold : k.1 < n
        · have hvPrevious :
              v ∈ previous.path.vertexSet :=
            previous.connector_subset k hold hv
          have hvThrough :
              v ∈ throughConnector.vertexSet :=
            previous.path.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
              connector hPreviousConnector hinterPreviousConnector hvPrevious
          exact
            throughConnector.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
              localPiece hConnectorLocal hinterThroughLocal hvThrough
        · have hkgap : k = gapIndex := by
            apply Fin.ext
            dsimp [gapIndex]
            omega
          subst k
          have hvConnector : v ∈ connector.vertexSet := by
            simpa [connector] using hv
          have hvThrough :
              v ∈ throughConnector.vertexSet :=
            previous.path.right_vertexSet_subset_appendWithEqOfInterSubsetTarget
              connector hPreviousConnector hinterPreviousConnector hvConnector
          exact
            throughConnector.left_vertexSet_subset_appendWithEqOfInterSubsetTarget
              localPiece hConnectorLocal hinterThroughLocal hvThrough
termination_by n _ => n

/-- The complete exact red rail. -/
noncomputable def exactRailPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    GraphPath (E.redSupport hbudget) :=
  (E.exactRailPrefix hbudget hrecords x
    (E.finalState.records.length - 1) (by omega)).path

@[simp] theorem exactRailPath_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    (E.exactRailPath hbudget hrecords x).source =
      E.initialTerminal hrecords x :=
  (E.exactRailPrefix hbudget hrecords x
    (E.finalState.records.length - 1) (by omega)).source_eq

/-- Every local red piece is literally contained in the complete exact rail. -/
theorem localRedPath_vertexSet_subset_exactRailPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (j : Fin E.finalState.records.length) (x : Fin h) :
    (E.localRedPathInRedSupport hbudget j x).vertexSet ⊆
      (E.exactRailPath hbudget hrecords x).vertexSet := by
  apply
    (E.exactRailPrefix hbudget hrecords x
      (E.finalState.records.length - 1) (by omega)).local_subset
  omega

/-- Every connector piece is literally contained in the complete exact
rail. -/
theorem connectorPath_vertexSet_subset_exactRailPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (k : Fin (E.finalState.records.length - 1)) (x : Fin h) :
    (E.connectorPathInRedSupport hbudget k x).vertexSet ⊆
      (E.exactRailPath hbudget hrecords x).vertexSet := by
  apply
    (E.exactRailPrefix hbudget hrecords x
      (E.finalState.records.length - 1) (by omega)).connector_subset
  omega

/-- Distinct exact rails are node-disjoint. -/
theorem exactRailPath_nodeDisjoint
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {x y : Fin h} (hxy : x ≠ y) :
    GraphPath.NodeDisjoint
      (E.exactRailPath hbudget hrecords x)
      (E.exactRailPath hbudget hrecords y) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvx hvy
  have hx :
      E.RedCarrier hbudget v x := by
    rcases
        (E.exactRailPrefix hbudget hrecords x
          (E.finalState.records.length - 1) (by omega)).vertex_mem hvx with
      ⟨j, _hj, hvj⟩ | ⟨k, _hk, hvk⟩
    · exact Or.inl ⟨j, hvj⟩
    · exact Or.inr ⟨k, hvk⟩
  have hy :
      E.RedCarrier hbudget v y := by
    rcases
        (E.exactRailPrefix hbudget hrecords y
          (E.finalState.records.length - 1) (by omega)).vertex_mem hvy with
      ⟨j, _hj, hvj⟩ | ⟨k, _hk, hvk⟩
    · exact Or.inl ⟨j, hvj⟩
    · exact Or.inr ⟨k, hvk⟩
  exact hxy (E.redCarrier_unique hbudget hx hy)

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
