import Lax17Proofs.Source.FlowWellLinked
import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Flow consequences used in Chuzhoy--Tan Section 4.6

This file connects the cluster-local cut-well-linkedness definition from
`Section46` with the self-contained auxiliary max-flow/min-cut routing theorem
from `FlowWellLinked`.
-/

namespace SimpleGraph
namespace Section46


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Cluster-local scaled edge-well-linkedness gives many disjoint paths between
equal-size terminal subsets in a bounded-degree graph.

The paths are produced in the same-vertex induced graph on `C` and then mapped
back to the ambient graph. -/
theorem hasDisjointSTPaths_of_scaledEdgeWellLinkedIn
    {C Terminals S T : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card)
    (hk : 10 * Δ * alphaDen * k ≤ 3 * alphaNum * S.card) :
    HasDisjointSTPaths G S T k := by
  classical
  let H := inducedOnFinset G C
  have hdegreeH : MaxDegreeAtMost H Δ :=
    maxDegreeAtMost_of_le hdegree (inducedOnFinset_le (G := G) (C := C))
  have hwellH : ScaledEdgeWellLinked H Terminals alphaNum alphaDen :=
    hwell.toScaledEdgeWellLinked_induced
  have hpathsH : HasDisjointSTPaths H S T k :=
    FlowWellLinked.hasDisjointSTPaths_of_scaledEdgeWellLinked
      (G := H) (Terminals := Terminals) (S := S) (T := T)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
      hdegreeH hDelta hwellH hS hT hcard hk
  rcases hpathsH with ⟨P, hPcard⟩
  exact ⟨P.mapLe (inducedOnFinset_le (G := G) (C := C)), by
    simpa using hPcard⟩

/-- Cluster-local scaled edge-well-linkedness gives many disjoint paths between
equal-size terminal subsets, with the additional certificate that the ambient
paths stay inside the cluster. -/
theorem exists_pathPacking_staysIn_of_scaledEdgeWellLinkedIn
    {C Terminals S T : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card)
    (hk : 10 * Δ * alphaDen * k ≤ 3 * alphaNum * S.card) :
    ∃ P : PathPacking G S T, k ≤ P.card ∧ P.StaysIn C := by
  classical
  let H := inducedOnFinset G C
  have hdegreeH : MaxDegreeAtMost H Δ :=
    maxDegreeAtMost_of_le hdegree (inducedOnFinset_le (G := G) (C := C))
  have hwellH : ScaledEdgeWellLinked H Terminals alphaNum alphaDen :=
    hwell.toScaledEdgeWellLinked_induced
  have hpathsH : HasDisjointSTPaths H S T k :=
    FlowWellLinked.hasDisjointSTPaths_of_scaledEdgeWellLinked
      (G := H) (Terminals := Terminals) (S := S) (T := T)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
      hdegreeH hDelta hwellH hS hT hcard hk
  rcases hpathsH with ⟨P, hPcard⟩
  refine ⟨P.mapLe (inducedOnFinset_le (G := G) (C := C)), by simpa using hPcard, ?_⟩
  exact InducedOnFinset.pathPacking_mapLe_staysIn
    (G := G) (C := C) (A := S) (B := T) P
    (subset_trans hS hwell.2.2.1) (subset_trans hT hwell.2.2.1)

/-- Cluster-local sharpened routing theorem for disjoint equal-size terminal
subsets. -/
theorem hasDisjointSTPaths_of_scaledEdgeWellLinkedIn_disjoint
    {C Terminals S T : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) (hdisj : Disjoint S T)
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * S.card) :
    HasDisjointSTPaths G S T k := by
  classical
  let H := inducedOnFinset G C
  have hdegreeH : MaxDegreeAtMost H Δ :=
    maxDegreeAtMost_of_le hdegree (inducedOnFinset_le (G := G) (C := C))
  have hwellH : ScaledEdgeWellLinked H Terminals alphaNum alphaDen :=
    hwell.toScaledEdgeWellLinked_induced
  have hpathsH : HasDisjointSTPaths H S T k :=
    FlowWellLinked.hasDisjointSTPaths_of_scaledEdgeWellLinked_disjoint
      (G := H) (Terminals := Terminals) (S := S) (T := T)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
      hdegreeH hDelta hwellH hS hT hcard hdisj hk
  rcases hpathsH with ⟨P, hPcard⟩
  exact ⟨P.mapLe (inducedOnFinset_le (G := G) (C := C)), by
    simpa using hPcard⟩

/-- Cluster-local sharpened routing theorem for disjoint equal-size terminal
subsets, with an explicit `StaysIn C` certificate. -/
theorem exists_pathPacking_staysIn_of_scaledEdgeWellLinkedIn_disjoint
    {C Terminals S T : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) (hdisj : Disjoint S T)
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * S.card) :
    ∃ P : PathPacking G S T, k ≤ P.card ∧ P.StaysIn C := by
  classical
  let H := inducedOnFinset G C
  have hdegreeH : MaxDegreeAtMost H Δ :=
    maxDegreeAtMost_of_le hdegree (inducedOnFinset_le (G := G) (C := C))
  have hwellH : ScaledEdgeWellLinked H Terminals alphaNum alphaDen :=
    hwell.toScaledEdgeWellLinked_induced
  have hpathsH : HasDisjointSTPaths H S T k :=
    FlowWellLinked.hasDisjointSTPaths_of_scaledEdgeWellLinked_disjoint
      (G := H) (Terminals := Terminals) (S := S) (T := T)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
      hdegreeH hDelta hwellH hS hT hcard hdisj hk
  rcases hpathsH with ⟨P, hPcard⟩
  refine ⟨P.mapLe (inducedOnFinset_le (G := G) (C := C)), by simpa using hPcard, ?_⟩
  exact InducedOnFinset.pathPacking_mapLe_staysIn
    (G := G) (C := C) (A := S) (B := T) P
    (subset_trans hS hwell.2.2.1) (subset_trans hT hwell.2.2.1)

end Section46
end SimpleGraph

end Lax17Proofs
