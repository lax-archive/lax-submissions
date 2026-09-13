import Lax17Proofs.Source.HindOellermannElementMenger
import Lax17Proofs.Source.HindOellermannCombinatorics

namespace Lax17Proofs

universe u v w

/-!
# The local path lemma for Hind--Oellermann

An edge node whose original endpoints are both nonterminals has exactly two
neighbors in the element-Menger graph.  Consequently, a terminal-to-terminal
path containing that edge node also contains both endpoint nodes.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph
namespace ElementMengerGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}

/-- If both endpoints of a named edge are nonterminals, its edge node has
exactly the two corresponding nonterminal nodes as neighbors. -/
theorem edge_adj_iff_eq_nonterminal_endpoints (e0 : H.Edge)
    (hleft : H.left e0 ∉ terminals) (hright : H.right e0 ∉ terminals)
    (x : ElementMengerNode H terminals k) :
    (elementMengerGraph H terminals k).Adj (.edge e0) x ↔
      x = .nonterminal ⟨H.left e0, hleft⟩ ∨
      x = .nonterminal ⟨H.right e0, hright⟩ := by
  rw [edge_adj_iff_represents_endpoint]
  cases x with
  | nonterminal x =>
      simp only [ElementMengerNode.represents_nonterminal,
        ElementMengerNode.nonterminal.injEq]
      constructor
      · rintro (hx | hx)
        · exact Or.inl (Subtype.ext hx)
        · exact Or.inr (Subtype.ext hx)
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
  | terminal x i =>
      have hxleft : x.1 ≠ H.left e0 := by
        intro hx
        exact hleft (hx ▸ x.2)
      have hxright : x.1 ≠ H.right e0 := by
        intro hx
        exact hright (hx ▸ x.2)
      simp [ElementMengerNode.Represents, hxleft, hxright]
  | edge e => simp [ElementMengerNode.Represents]

/-- A terminal-copy path containing an edge node with two nonterminal
endpoints also contains both corresponding nonterminal nodes. -/
theorem nonterminal_endpoints_mem_vertexSet_of_edge_mem
    {u v : W}
    (P : GraphPath (elementMengerGraph H terminals k))
    (hconnects : P.Connects
      (terminalCopies (H := H) (terminals := terminals) (k := k) u)
      (terminalCopies (H := H) (terminals := terminals) (k := k) v))
    (e0 : H.Edge) (hleft : H.left e0 ∉ terminals)
    (hright : H.right e0 ∉ terminals)
    (he0 : (.edge e0 : ElementMengerNode H terminals k) ∈ P.vertexSet) :
    (.nonterminal ⟨H.left e0, hleft⟩ : ElementMengerNode H terminals k) ∈
        P.vertexSet ∧
      (.nonterminal ⟨H.right e0, hright⟩ : ElementMengerNode H terminals k) ∈
        P.vertexSet := by
  classical
  let edgeNode : ElementMengerNode H terminals k := .edge e0
  let leftNode : ElementMengerNode H terminals k :=
    .nonterminal ⟨H.left e0, hleft⟩
  let rightNode : ElementMengerNode H terminals k :=
    .nonterminal ⟨H.right e0, hright⟩
  have hedge_not_copy (w : W) :
      edgeNode ∉ terminalCopies (H := H) (terminals := terminals) (k := k) w := by
    simp [edgeNode]
  have hedge_source : edgeNode ≠ P.source := by
    intro heq
    rcases hconnects with hconnects | hconnects
    · exact hedge_not_copy u (heq ▸ hconnects.1)
    · exact hedge_not_copy v (heq ▸ hconnects.1)
  have hedge_target : edgeNode ≠ P.target := by
    intro heq
    rcases hconnects with hconnects | hconnects
    · exact hedge_not_copy v (heq ▸ hconnects.2)
    · exact hedge_not_copy u (heq ▸ hconnects.2)
  rcases GraphPath.exists_two_edgeSet_incident_of_mem_vertexSet_of_not_endpoint
      P he0 hedge_source hedge_target with
    ⟨e1, he1P, hedge1, e2, he2P, hedge2, he12⟩
  have incident_edge_gives_endpoint
      (e : Sym2 (ElementMengerNode H terminals k))
      (heP : e ∈ P.edgeSet) (hedge : edgeNode ∈ e) :
      ∃ y, e = s(edgeNode, y) ∧ (y = leftNode ∨ y = rightNode) ∧
        y ∈ P.vertexSet := by
    let a := e.out.1
    let b := e.out.2
    have hab : s(a, b) = e := by
      dsimp [a, b]
      rw [Sym2.mk, e.out_eq]
    have hedgeab : edgeNode ∈ s(a, b) := by
      simpa [hab] using hedge
    have habAdj : (elementMengerGraph H terminals k).Adj a b := by
      have heGraph := P.edgeSet_subset_edgeSet heP
      have heGraphAB : s(a, b) ∈ (elementMengerGraph H terminals k).edgeSet := by
        rw [hab]
        exact heGraph
      simpa using heGraphAB
    have heWalk : e ∈ P.walk.edges := by
      exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using heP)
    have heWalkAB : s(a, b) ∈ P.walk.edges := by
      rw [hab]
      exact heWalk
    rcases Sym2.mem_iff.mp hedgeab with ha | hb
    · refine ⟨b, ?_, ?_, ?_⟩
      · simpa [ha] using hab.symm
      · have hadj : (elementMengerGraph H terminals k).Adj edgeNode b := by
          simpa [ha] using habAdj
        simpa [edgeNode, leftNode, rightNode] using
          (edge_adj_iff_eq_nonterminal_endpoints e0 hleft hright b).1 hadj
      · have hbSupport : b ∈ P.walk.support := by
          exact P.walk.snd_mem_support_of_mem_edges heWalkAB
        simpa [GraphPath.vertexSet] using hbSupport
    · refine ⟨a, ?_, ?_, ?_⟩
      · simpa [hb, Sym2.eq_swap] using hab.symm
      · have hadj : (elementMengerGraph H terminals k).Adj edgeNode a := by
          simpa [hb] using (elementMengerGraph H terminals k).symm habAdj
        simpa [edgeNode, leftNode, rightNode] using
          (edge_adj_iff_eq_nonterminal_endpoints e0 hleft hright a).1 hadj
      · have haSupport : a ∈ P.walk.support := by
          exact P.walk.fst_mem_support_of_mem_edges heWalkAB
        simpa [GraphPath.vertexSet] using haSupport
  rcases incident_edge_gives_endpoint e1 he1P hedge1 with
    ⟨y1, he1, hy1, hy1P⟩
  rcases incident_edge_gives_endpoint e2 he2P hedge2 with
    ⟨y2, he2, hy2, hy2P⟩
  have hy12 : y1 ≠ y2 := by
    intro hy
    apply he12
    rw [he1, he2, hy]
  rcases hy1 with rfl | rfl <;> rcases hy2 with rfl | rfl
  · exact False.elim (hy12 rfl)
  · exact ⟨hy1P, hy2P⟩
  · exact ⟨hy2P, hy1P⟩
  · exact False.elim (hy12 rfl)

/-- If an encoded element cut contains both nonterminal endpoint nodes of an
edge node on a terminal-copy path, then it meets that path in at least two
vertices. -/
theorem two_le_card_vertexSet_inter_elementSet_of_edge_mem
    {a b u v : W} (C : TerminalElementCut H terminals a b)
    (P : GraphPath (elementMengerGraph H terminals k))
    (hconnects : P.Connects
      (terminalCopies (H := H) (terminals := terminals) (k := k) u)
      (terminalCopies (H := H) (terminals := terminals) (k := k) v))
    (e0 : H.Edge) (hleft : H.left e0 ∉ terminals)
    (hright : H.right e0 ∉ terminals)
    (he0 : (.edge e0 : ElementMengerNode H terminals k) ∈ P.vertexSet)
    (hleftSet :
      (.nonterminal ⟨H.left e0, hleft⟩ : ElementMengerNode H terminals k) ∈
        elementSet C k)
    (hrightSet :
      (.nonterminal ⟨H.right e0, hright⟩ : ElementMengerNode H terminals k) ∈
        elementSet C k) :
    2 ≤ (P.vertexSet ∩ elementSet C k).card := by
  classical
  rcases nonterminal_endpoints_mem_vertexSet_of_edge_mem
      P hconnects e0 hleft hright he0 with ⟨hleftP, hrightP⟩
  let leftNode : ElementMengerNode H terminals k :=
    .nonterminal ⟨H.left e0, hleft⟩
  let rightNode : ElementMengerNode H terminals k :=
    .nonterminal ⟨H.right e0, hright⟩
  have hnodes_ne : leftNode ≠ rightNode := by
    intro hnodes
    have hnodes' := congrArg (elementMengerNodeEquiv H terminals k) hnodes
    exact H.end_ne e0 (by simpa [leftNode, rightNode] using hnodes')
  have hpair_subset :
      ({leftNode, rightNode} : Finset (ElementMengerNode H terminals k)) ⊆
        P.vertexSet ∩ elementSet C k := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.2 ⟨hleftP, hleftSet⟩
    · exact Finset.mem_inter.2 ⟨hrightP, hrightSet⟩
  rw [← Finset.card_pair hnodes_ne]
  exact Finset.card_le_card hpair_subset

end ElementMengerGraph
end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
