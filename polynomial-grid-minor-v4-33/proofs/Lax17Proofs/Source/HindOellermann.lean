import Lax17Proofs.Source.HindOellermannCombinatorics
import Lax17Proofs.Source.HindOellermannContractionCuts
import Lax17Proofs.Source.HindOellermannDeletionCuts
import Lax17Proofs.Source.HindOellermannElementMenger
import Lax17Proofs.Source.HindOellermannElementMengerTheorem
import Lax17Proofs.Source.HindOellermannPathLemma

namespace Lax17Proofs

universe u v w

open SimpleGraph.ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.ElementMengerGraph.TerminalElementConnectedAtLeast

/-!
# The Hind--Oellermann deletion--contraction theorem

This module completes the path-counting part of Hind and Oellermann's
deletion--contraction argument.  The capacity-expanded incidence graph keeps
named parallel edges distinct, gives nonterminals capacity one, and gives
terminals capacity `k`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset
open HindOellermannCombinatorics

namespace PathPacking

variable {V : Type*} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T : Finset V}

/-- Fewer vertices than paths cannot meet every path in a node-disjoint
packing. -/
theorem exists_path_disjoint_of_card_lt
    (P : PathPacking G S T) (X : Finset V) (hcard : X.card < P.card) :
    ∃ i : P.Index, Disjoint (P.path i).vertexSet X := by
  classical
  by_contra hnone
  push Not at hnone
  have hhits : ∀ i : P.Index, ((P.path i).vertexSet ∩ X).Nonempty := by
    intro i
    exact Finset.not_disjoint_iff_nonempty_inter.mp (hnone i)
  have hle := fintype_card_le_card_of_pairwiseDisjoint_of_hits
    (fun i : P.Index => (P.path i).vertexSet) X P.node_disjoint hhits
  change P.card ≤ X.card at hle
  omega

/-- If a set no larger than a packing hits one path twice, it misses another
packed path. -/
theorem exists_path_disjoint_of_card_le_of_two_hits
    (P : PathPacking G S T) (X : Finset V) (hcard : X.card ≤ P.card)
    (i : P.Index) (htwo : 2 ≤ ((P.path i).vertexSet ∩ X).card) :
    ∃ j : P.Index, Disjoint (P.path j).vertexSet X := by
  classical
  apply exists_disjoint_of_card_le_fintype_card_of_two_le_card_inter
    (fun j : P.Index => (P.path j).vertexSet) X P.node_disjoint
  · simpa [PathPacking.card] using hcard
  · exact htwo

end PathPacking

open ElementMengerGraph

/-- Hind and Oellermann's deletion--contraction alternative for terminal
element connectivity. -/
theorem hindOellermannDeletionContraction :
    HindOellermannDeletionContractionStatement := by
  intro W _instFintype _instDecidableEq H terminals k e0 hleft hright hconn
  by_cases hdelete :
      (H.deleteEdge e0).TerminalElementConnectedAtLeast terminals k
  · exact Or.inl hdelete
  right
  by_contra hcontract
  rcases exists_terminalElementCut_order_lt_of_not_connectedAtLeast hdelete with
    ⟨a, ha, b, hb, hab, D, hDsmall⟩
  rcases exists_terminalElementCut_order_lt_of_not_connectedAtLeast hcontract with
    ⟨a', ha', b', hb', _hab', C, hCsmall⟩
  rw [ContractVertex.mem_terminalImage] at ha' hb'
  rcases ha' with ⟨x, hx, hpx⟩
  rcases hb' with ⟨y, hy, hpy⟩
  let D0 : TerminalElementCut H terminals a b := D.liftDelete H e0
  let R : TerminalElementCut H terminals x y :=
    C.liftContract H e0 terminals hpx hpy
  have hDorder : D.order = k - 1 :=
    deletionCut_order_eq_sub_one hconn e0 ha hb hab D hDsmall
  have hD0order : D0.order = k := by
    rw [show D0.order = D.order + 1 from D.liftDelete_order_eq_add_one e0,
      hDorder]
    omega
  rcases hconn.deficient_contractCut_liftContract e0 hx hy hpx hpy C hCsmall with
    ⟨_hmerged, _hRorderEq, hRorder, hleftR, hrightR⟩
  have hcross_same_side : ∀ {u v : W}, u ∈ terminals -> v ∈ terminals ->
      u ∈ D0.side -> v ∉ D0.side -> (u ∈ R.side ↔ v ∈ R.side) := by
    intro u v hu hv huD hvD
    have huv : u ≠ v := by
      intro huv
      subst v
      exact hvD huD
    rcases exists_elementMengerPathPacking hconn hu hv huv with ⟨P, hPcard⟩
    let Duv : TerminalElementCut H terminals u v := D0.retarget huD hvD
    let deletedNode : ElementMengerNode H terminals k := .edge e0
    let J : Finset (ElementMengerNode H terminals k) := elementSet Duv k
    have hJcard : J.card = k := by
      rw [show J.card = Duv.order from elementSet_card Duv k,
        show Duv.order = D0.order from rfl, hD0order]
    have hdeletedJ : deletedNode ∈ J := by
      rw [show deletedNode = (.edge e0 : ElementMengerNode H terminals k) from rfl,
        show J = elementSet Duv k from rfl, edge_mem_elementSet_iff]
      simp [Duv, D0, TerminalElementCut.retarget,
        TerminalElementCut.liftDelete]
    have hJerase : (J.erase deletedNode).card < P.card := by
      have herase := Finset.card_erase_add_one hdeletedJ
      omega
    rcases PathPacking.exists_path_disjoint_of_card_lt P
        (J.erase deletedNode) hJerase with
      ⟨i, hi⟩
    have hhitJ := cut_blocks Duv k (P.path i) (P.connects i)
    rcases hhitJ with ⟨z, hzPath, hzJ⟩
    have hzNotErase : z ∉ J.erase deletedNode :=
      Finset.disjoint_left.mp hi hzPath
    have hzDeleted : z = deletedNode := by
      by_contra hne
      exact hzNotErase (Finset.mem_erase.mpr ⟨hne, hzJ⟩)
    have hdeletedPath : deletedNode ∈ (P.path i).vertexSet := by
      simpa [hzDeleted] using hzPath
    have contradict_cut : ∀ {s t : W}
        (Q : TerminalElementCut H terminals s t),
        Q.order ≤ k ->
        H.left e0 ∈ Q.removedVertices ->
        H.right e0 ∈ Q.removedVertices ->
        (∀ j : P.Index, (P.path j).Connects
          (terminalCopies (H := H) (terminals := terminals) (k := k) s)
          (terminalCopies (H := H) (terminals := terminals) (k := k) t)) ->
        False := by
      intro s t Q hQorder hleftQ hrightQ hconnects
      have hleftSet :
          (.nonterminal ⟨H.left e0, hleft⟩ : ElementMengerNode H terminals k) ∈
            elementSet Q k :=
        (nonterminal_mem_elementSet_iff Q k _).2 hleftQ
      have hrightSet :
          (.nonterminal ⟨H.right e0, hright⟩ : ElementMengerNode H terminals k) ∈
            elementSet Q k :=
        (nonterminal_mem_elementSet_iff Q k _).2 hrightQ
      have htwo := two_le_card_vertexSet_inter_elementSet_of_edge_mem
        Q (P.path i) (hconnects i) e0 hleft hright
        (by simpa [deletedNode] using hdeletedPath) hleftSet hrightSet
      have hQcard : (elementSet Q k).card ≤ P.card := by
        rw [elementSet_card, hPcard]
        exact hQorder
      rcases PathPacking.exists_path_disjoint_of_card_le_of_two_hits P
          (elementSet Q k) hQcard i htwo with ⟨j, hj⟩
      rcases cut_blocks Q k (P.path j) (hconnects j) with
        ⟨z, hzPath, hzQ⟩
      exact Finset.disjoint_left.mp hj hzPath hzQ
    by_cases huR : u ∈ R.side
    · by_cases hvR : v ∈ R.side
      · exact ⟨fun _ => hvR, fun _ => huR⟩
      · exact (contradict_cut (R.retarget huR hvR)
          (by simpa using hRorder) hleftR hrightR (fun j => P.connects j)).elim
    · by_cases hvR : v ∈ R.side
      · exact (contradict_cut (R.retarget hvR huR)
          (by simpa using hRorder) hleftR hrightR
          (fun j => (GraphPath.connects_comm (P.path j) _ _).mp (P.connects j))).elim
      · exact ⟨fun h => (huR h).elim, fun h => (hvR h).elim⟩
  by_cases hxD : x ∈ D0.side
  · by_cases hyD : y ∈ D0.side
    · have hxb := hcross_same_side hx hb hxD D0.target_not_mem
      have hyb := hcross_same_side hy hb hyD D0.target_not_mem
      have hbR : b ∈ R.side := hxb.mp R.source_mem
      exact R.target_not_mem (hyb.mpr hbR)
    · have hxyR := hcross_same_side hx hy hxD hyD
      exact R.target_not_mem (hxyR.mp R.source_mem)
  · by_cases hyD : y ∈ D0.side
    · have hyxR := hcross_same_side hy hx hyD hxD
      exact R.target_not_mem (hyxR.mpr R.source_mem)
    · have hax := hcross_same_side ha hx D0.source_mem hxD
      have hay := hcross_same_side ha hy D0.source_mem hyD
      have haR : a ∈ R.side := hax.mpr R.source_mem
      exact R.target_not_mem (hay.mp haR)

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
