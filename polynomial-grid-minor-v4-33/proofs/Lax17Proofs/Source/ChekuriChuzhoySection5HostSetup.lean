import Lax17Proofs.Source.ChekuriChuzhoyPendantTerminals
import Lax17Proofs.Source.ChekuriChuzhoySection5GoodClustering
import Lax17Proofs.Source.ChekuriChuzhoySection5MinimalHost

namespace Lax17Proofs

universe u v w

/-!
# Pendant edge-minimal host setup

Chekuri--Chuzhoy Section 5 first replaces the node-well-linked set by fresh
degree-one terminals and then takes an edge-minimal spanning subgraph that
preserves their node-well-linkedness.  A terminal edge cannot disappear in
that subgraph: routing the terminal to any distinct terminal supplies a
nontrivial path and hence an incident retained edge.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5HostSetup


open ChekuriChuzhoyPendantVertex
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5GoodClustering
open ChekuriChuzhoySection5MinimalHost

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {X : Finset V}

private theorem exists_distinct_mem
    {W : Type*} [DecidableEq W] {T : Finset W}
    (hT : 2 ≤ T.card) {t : W} (ht : t ∈ T) :
    ∃ u ∈ T, u ≠ t := by
  have hcard : 0 < (T.erase t).card := by
    rw [Finset.card_erase_of_mem ht]
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hcard
  exact ⟨u, Finset.mem_of_mem_erase hu, (Finset.mem_erase.mp hu).1⟩

private theorem edgeMinimal_terminal_has_neighbor
    {W : Type*} [Fintype W] [DecidableEq W]
    {G0 : _root_.SimpleGraph W} {T : Finset W}
    (M : EdgeMinimalNodeWellLinkedHost G0 T)
    (hT : 2 ≤ T.card) {t : W} (ht : t ∈ T) :
    ∃ v, M.H.Adj t v := by
  classical
  obtain ⟨u, huT, hut⟩ := exists_distinct_mem hT ht
  have hsingleDisjoint : Disjoint ({t} : Finset W) {u} := by
    simp [hut.symm]
  obtain ⟨P, hPcard, _hPstay⟩ :=
    M.nodeWellLinked.2
      (by simpa using ht) (by simpa using huT) hsingleDisjoint
  have hPpositive : 0 < P.card := by
    have hPcard' : P.card = 1 := by simpa using hPcard
    omega
  have hindex : Nonempty P.Index := by
    rw [← Fintype.card_pos_iff]
    simpa [PathPacking.card] using hPpositive
  let i : P.Index := Classical.choice hindex
  rcases P.connects i with hconnects | hconnects
  · have hsource : (P.path i).source = t := by simpa using hconnects.1
    have htarget : (P.path i).target = u := by simpa using hconnects.2
    have hne : (P.path i).source ≠ (P.path i).target := by
      simpa [hsource, htarget] using hut.symm
    refine ⟨(P.path i).reverse.penultimate, ?_⟩
    have hrev :
        (P.path i).reverse.source ≠ (P.path i).reverse.target := by
      simpa using hne.symm
    have hadj :=
      ((P.path i).reverse.penultimate_adj_target hrev).symm
    simpa [hsource] using hadj
  · have hsource : (P.path i).source = u := by simpa using hconnects.1
    have htarget : (P.path i).target = t := by simpa using hconnects.2
    have hne : (P.path i).source ≠ (P.path i).target := by
      simpa [hsource, htarget] using hut
    refine ⟨(P.path i).penultimate, ?_⟩
    simpa [htarget] using ((P.path i).penultimate_adj_target hne).symm

/-- Every fresh terminal still has degree exactly one after edge
minimalization. -/
theorem edgeMinimal_leaf_degree_one
    (M : EdgeMinimalNodeWellLinkedHost
      (graph (X := X) G) (leaves (V := V) (X := X)))
    (hX : 2 ≤ X.card)
    (t : ChekuriChuzhoyPendantVertex V X)
    (ht : t ∈ leaves (V := V) (X := X)) :
    DegreeEquals M.H t 1 := by
  classical
  have hleaves :
      2 ≤ (leaves (V := V) (X := X)).card := by
    simpa using hX
  obtain ⟨v, htv⟩ :=
    edgeMinimal_terminal_has_neighbor M hleaves ht
  obtain ⟨x, rfl⟩ := exists_leafValue ht
  have horiginal :
      DegreeEquals (graph (X := X) G) (leaf x) 1 :=
    leaf_degree_one (G := G) x
  exact degreeEquals_one_of_unique_neighbor htv (by
    intro w htw
    exact horiginal.one_adj_eq (M.le_original htw)
      (M.le_original htv))

/-- Degree-exactness gives the singleton boundary count used by Claim 5.9. -/
theorem originalBoundary_singleton_card_eq_one_of_degreeEquals
    {W : Type*} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W} {t : W}
    (ht : DegreeEquals H t 1) :
    (originalBoundary H ({t} : Finset W)).card = 1 := by
  classical
  letI := Classical.decRel H.Adj
  rw [originalBoundary_singleton_card]
  rcases ht with ⟨N, hN, hcard⟩
  have hNfinset : N = H.neighborFinset t := by
    ext v
    simp only [H.mem_neighborFinset]
    exact hN v
  rw [← H.card_neighborFinset_eq_degree, ← hNfinset, hcard]

/-- Complete nonalgorithmic host setup for Section 5.  The selected host has
maximum degree at most `Delta + 1`, its pendant terminals remain
node-well-linked, and every terminal retains degree exactly one. -/
theorem exists_edgeMinimalPendantHost
    {Delta : Nat}
    (hdegree : MaxDegreeAtMost G Delta)
    (hXcard : 2 ≤ X.card)
    (hXwell :
      NodeWellLinkedIn G (Finset.univ : Finset V) X) :
    ∃ M : EdgeMinimalNodeWellLinkedHost
        (graph (X := X) G) (leaves (V := V) (X := X)),
      MaxDegreeAtMost M.H (Delta + 1) ∧
      (∀ t ∈ leaves (V := V) (X := X), DegreeEquals M.H t 1) ∧
      ∀ t ∈ leaves (V := V) (X := X),
        (originalBoundary M.H ({t} : Finset
          (ChekuriChuzhoyPendantVertex V X))).card = 1 := by
  have hpendantWell :
      NodeWellLinkedIn (graph (X := X) G)
        (Finset.univ : Finset (ChekuriChuzhoyPendantVertex V X))
        (leaves (V := V) (X := X)) :=
    nodeWellLinkedIn_leaves hXwell
  obtain ⟨M⟩ :=
    exists_edgeMinimalNodeWellLinkedHost hpendantWell
  have hMdegree : MaxDegreeAtMost M.H (Delta + 1) :=
    maxDegreeAtMost_of_le (maxDegreeAtMost_succ hdegree) M.le_original
  have hterminalDegree :
      ∀ t ∈ leaves (V := V) (X := X), DegreeEquals M.H t 1 :=
    fun t ht => edgeMinimal_leaf_degree_one M hXcard t ht
  exact ⟨M, hMdegree, hterminalDegree, fun t ht =>
    originalBoundary_singleton_card_eq_one_of_degreeEquals
      (hterminalDegree t ht)⟩

end ChekuriChuzhoySection5HostSetup
end SimpleGraph

end Lax17Proofs
