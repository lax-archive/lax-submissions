import Lax17Proofs.Source.TreewidthSparsifierTheorem51ChunkOutcome

namespace Lax17Proofs

universe u v w

/-!
# Connectivity of the surviving red rails

The local red routings and the intervening path-of-sets connectors concatenate
label by label.  This module records the resulting reachability statement in
the red support.  Since the red support survives every thinning outcome, it
is the deterministic part used to attach each clean blue chunk to the initial
terminal carrying the same abstract label.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- A local red path, viewed inside the complete red support. -/
noncomputable def localRedPathInRedSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    GraphPath (E.redSupport hbudget) := by
  let i :=
    (E.recordAt j).layer.red.indexOfSource
      ((E.recordAt j).label x)
  let Q :=
    (E.recordAt j).layer.red.toPathPacking.inSpanningGraph.path i
  exact Q.mapLe
    ((le_iSup
      (fun k : Fin E.finalState.records.length =>
        (E.recordAt k).layer.red.toPathPacking.spanningGraph) j).trans
      le_sup_left)

@[simp] theorem localRedPathInRedSupport_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.localRedPathInRedSupport hbudget j x).source =
      (E.localRedPath j x).source := by
  simp [localRedPathInRedSupport, localRedPath,
    PathPacking.inSpanningGraph, PathPacking.transfer,
    GraphPath.mapLe, GraphPath.transfer]

@[simp] theorem localRedPathInRedSupport_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.localRedPathInRedSupport hbudget j x).target =
      (E.localRedPath j x).target := by
  simp [localRedPathInRedSupport, localRedPath,
    PathPacking.inSpanningGraph, PathPacking.transfer,
    GraphPath.mapLe, GraphPath.transfer]

@[simp] theorem localRedPathInRedSupport_vertexSet
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.localRedPathInRedSupport hbudget j x).vertexSet =
      (E.localRedPath j x).vertexSet := by
  simp [localRedPathInRedSupport, localRedPath]

/-- The source of a local red piece reaches every vertex of that piece in
the global red support. -/
theorem localRedPath_source_reachable
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (x : Fin h) {v : V}
    (hv : v ∈ (E.localRedPath j x).vertexSet) :
    (E.redSupport hbudget).Reachable
      (E.localRedPath j x).source v := by
  let Q := E.localRedPathInRedSupport hbudget j x
  have hvQ : v ∈ Q.vertexSet := by
    simpa [Q] using hv
  have hreach := (Q.takeUntil hvQ).walk.reachable
  simpa [Q] using hreach

/-- A connector path, viewed inside the complete red support. -/
noncomputable def connectorPathInRedSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) :
    GraphPath (E.redSupport hbudget) := by
  let i :=
    (E.connectorAt hbudget j).indexOfSource
      (E.connectorSource hbudget j x)
  let Q :=
    (E.connectorAt hbudget j).toPathPacking.inSpanningGraph.path i
  exact Q.mapLe
    ((le_iSup
      (fun k : Fin (E.finalState.records.length - 1) =>
        (E.connectorAt hbudget k).toPathPacking.spanningGraph) j).trans
      le_sup_right)

@[simp] theorem connectorPathInRedSupport_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) :
    (E.connectorPathInRedSupport hbudget j x).source =
      (E.connectorPath hbudget j x).source := by
  simp [connectorPathInRedSupport, connectorPath,
    PathPacking.inSpanningGraph, PathPacking.transfer,
    GraphPath.mapLe, GraphPath.transfer]

@[simp] theorem connectorPathInRedSupport_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) :
    (E.connectorPathInRedSupport hbudget j x).target =
      (E.connectorPath hbudget j x).target := by
  simp [connectorPathInRedSupport, connectorPath,
    PathPacking.inSpanningGraph, PathPacking.transfer,
    GraphPath.mapLe, GraphPath.transfer]

@[simp] theorem connectorPathInRedSupport_vertexSet
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) :
    (E.connectorPathInRedSupport hbudget j x).vertexSet =
      (E.connectorPath hbudget j x).vertexSet := by
  simp [connectorPathInRedSupport, connectorPath]

theorem connectorPath_source_reachable
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) {v : V}
    (hv : v ∈ (E.connectorPath hbudget j x).vertexSet) :
    (E.redSupport hbudget).Reachable
      (E.connectorPath hbudget j x).source v := by
  let Q := E.connectorPathInRedSupport hbudget j x
  have hvQ : v ∈ Q.vertexSet := by
    simpa [Q] using hv
  have hreach := (Q.takeUntil hvQ).walk.reachable
  simpa [Q] using hreach

/-- The initial terminal carrying abstract rail `x`. -/
noncomputable def initialTerminal
    (E : ExpanderBlocks P count)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) : V :=
  ((E.recordAt (E.firstRecord hrecords)).label x).1

theorem initialTerminal_mem
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    E.initialTerminal hrecords x ∈ P.left P.firstIndex := by
  rw [initialTerminal, ← E.firstRecord_index_eq_firstIndex hbudget hrecords]
  exact ((E.recordAt (E.firstRecord hrecords)).label x).2

theorem initialTerminal_injective
    (E : ExpanderBlocks P count)
    (hrecords : 0 < E.finalState.records.length) :
    Function.Injective (E.initialTerminal hrecords) := by
  intro x y hxy
  apply (E.recordAt (E.firstRecord hrecords)).label.injective
  exact Subtype.ext hxy

theorem image_initialTerminal_univ
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length) :
    Finset.univ.image (E.initialTerminal hrecords) =
      P.left P.firstIndex := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
    exact E.initialTerminal_mem hbudget hrecords x
  · intro v hv
    let named :
        {z : V // z ∈
          P.left (E.recordAt (E.firstRecord hrecords)).index} :=
      ⟨v, by
        rw [E.firstRecord_index_eq_firstIndex hbudget hrecords]
        exact hv⟩
    let x : Fin h :=
      (E.recordAt (E.firstRecord hrecords)).label.symm named
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val
      ((E.recordAt (E.firstRecord hrecords)).label.apply_symm_apply named)

/-- The first terminal reaches the start of every later local red piece. -/
theorem initialTerminal_reachable_localRedPath_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.redSupport hbudget).Reachable
      (E.initialTerminal hrecords x)
      (E.localRedPath j x).source := by
  have aux :
      ∀ n (hn : n < E.finalState.records.length),
        (E.redSupport hbudget).Reachable
          (E.initialTerminal hrecords x)
          (E.localRedPath ⟨n, hn⟩ x).source := by
    intro n
    induction n with
    | zero =>
        intro hn
        have heq :
            E.initialTerminal hrecords x =
              (E.localRedPath ⟨0, hn⟩ x).source := by
          rw [initialTerminal, E.localRedPath_source]
          congr 2
        rw [heq]
    | succ n ih =>
        intro hn
        let prev : Fin E.finalState.records.length :=
          ⟨n, by omega⟩
        let gap : Fin (E.finalState.records.length - 1) :=
          ⟨n, by omega⟩
        have hprev := ih (by omega)
        have hlocal :=
          E.localRedPath_source_reachable hbudget prev x
            (GraphPath.target_mem_vertexSet _)
        have hconnector :=
          E.connectorPath_source_reachable hbudget gap x
            (GraphPath.target_mem_vertexSet _)
        have hsource :
            (E.connectorPath hbudget gap x).source =
              (E.localRedPath prev x).target := by
          rw [E.connectorPath_source, E.localRedPath_target]
          congr 2
        have htarget :
            (E.connectorPath hbudget gap x).target =
              (E.localRedPath ⟨n + 1, hn⟩ x).source := by
          rw [E.connectorPath_target, E.localRedPath_source]
          congr 2
        rw [hsource] at hconnector
        rw [htarget] at hconnector
        exact hprev.trans (hlocal.trans hconnector)
  exact aux j.1 j.2

/-- Every vertex carried by rail `x` is red-reachable from the initial
terminal carrying `x`. -/
theorem initialTerminal_reachable_of_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {v : V} {x : Fin h}
    (hv : E.RedCarrier hbudget v x) :
    (E.redSupport hbudget).Reachable
      (E.initialTerminal hrecords x) v := by
  rcases hv with ⟨j, hv⟩ | ⟨j, hv⟩
  · exact
      (E.initialTerminal_reachable_localRedPath_source
        hbudget hrecords j x).trans
        (E.localRedPath_source_reachable hbudget j x hv)
  · let prev := E.gapRecord j
    have hstart :=
      E.initialTerminal_reachable_localRedPath_source
        hbudget hrecords prev x
    have hlocal :=
      E.localRedPath_source_reachable hbudget prev x
        (GraphPath.target_mem_vertexSet _)
    have hconnector :=
      E.connectorPath_source_reachable hbudget j x hv
    have hsource :
        (E.connectorPath hbudget j x).source =
          (E.localRedPath prev x).target := by
      rw [E.connectorPath_source, E.localRedPath_target]
    rw [hsource] at hconnector
    exact hstart.trans (hlocal.trans hconnector)

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
