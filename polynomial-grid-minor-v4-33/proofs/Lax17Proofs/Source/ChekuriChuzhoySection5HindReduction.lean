import Lax17Proofs.Source.HindOellermann

namespace Lax17Proofs

universe u v w

/-!
# The Hind--Oellermann reduction in Chekuri--Chuzhoy Section 5

This module formalizes the first phase of journal Theorem 5.10 (preprint
Theorem 5.10).  Repeated deletion or contraction of a nonterminal edge ends
with a named multigraph in which every edge has a terminal endpoint.  The
terminal labels remain injective, terminal element connectivity is preserved,
and no terminal degree increases.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The terminal set represented by an injective terminal-label map. -/
noncomputable def terminalMapImage {A Z : Type*} [Fintype A] [DecidableEq Z]
    (f : A → Z) : Finset Z :=
  Finset.univ.image f

@[simp] theorem mem_terminalMapImage {A Z : Type*} [Fintype A] [DecidableEq Z]
    {f : A → Z} {z : Z} :
    z ∈ terminalMapImage f ↔ ∃ a, f a = z := by
  simp [terminalMapImage]

/-- Output of the deletion--contraction phase.  The vertex type is allowed to
change under contraction, while `terminalMap` keeps the original terminal
labels stable. -/
structure HindReduction (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) where
  Vertex : Type u
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  graph : FiniteEdgeIndexedGraph Vertex
  terminalMap : TerminalVertex terminals → Vertex
  terminalMap_injective : Function.Injective terminalMap
  element_connected : graph.TerminalElementConnectedAtLeast
    (terminalMapImage terminalMap) k
  terminal_degree_le : ∀ t : TerminalVertex terminals,
    graph.degree (terminalMap t) ≤ H.degree t.1
  every_edge_incident_terminal : ∀ e : graph.Edge,
    graph.left e ∈ terminalMapImage terminalMap ∨
      graph.right e ∈ terminalMapImage terminalMap

namespace HindReduction

instance {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (R : H.HindReduction terminals k) : Fintype R.Vertex :=
  R.vertexFintype

instance {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (R : H.HindReduction terminals k) : DecidableEq R.Vertex :=
  R.vertexDecidableEq

end HindReduction

/-- The original terminal subtype maps to the terminal image after contracting
a nonterminal edge. -/
def contractionTerminalMap (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (e : H.Edge)
    (hleft : H.left e ∉ terminals) (hright : H.right e ∉ terminals) :
    TerminalVertex terminals →
      TerminalVertex (ContractVertex.terminalImage
        (p := H.left e) (q := H.right e) terminals) :=
  fun t => ⟨ContractVertex.projection
    (p := H.left e) (q := H.right e) t.1,
    Finset.mem_image.mpr ⟨t.1, t.2, rfl⟩⟩

theorem contractionTerminalMap_injective
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (e : H.Edge)
    (hleft : H.left e ∉ terminals) (hright : H.right e ∉ terminals) :
    Function.Injective (H.contractionTerminalMap terminals e hleft hright) := by
  intro x y hxy
  apply Subtype.ext
  apply ContractVertex.eq_of_projection_eq_of_right_not_endpoint
    (congrArg Subtype.val hxy)
  · exact fun h => hleft (h ▸ y.2)
  · exact fun h => hright (h ▸ y.2)

theorem contractionTerminalMap_surjective
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (e : H.Edge)
    (hleft : H.left e ∉ terminals) (hright : H.right e ∉ terminals) :
    Function.Surjective (H.contractionTerminalMap terminals e hleft hright) := by
  intro z
  rcases ContractVertex.mem_terminalImage.mp z.2 with ⟨t, ht, htz⟩
  refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
  exact htz

/-- The original graph is a reduction result when it already has no edge with
two nonterminal endpoints. -/
noncomputable def HindReduction.refl
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : H.TerminalElementConnectedAtLeast terminals k)
    (hreduced : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals) :
    H.HindReduction terminals k where
  Vertex := W
  graph := H
  terminalMap := fun t => t.1
  terminalMap_injective := fun x y h => Subtype.ext h
  element_connected := by
    simpa [terminalMapImage] using hconn
  terminal_degree_le := fun _ => le_rfl
  every_edge_incident_terminal := by
    intro e
    simpa [terminalMapImage] using hreduced e

/-- Repeated Hind--Oellermann deletion/contraction reaches the source normal
form without losing terminal element connectivity or increasing a terminal
degree. -/
theorem exists_hindReduction
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : H.TerminalElementConnectedAtLeast terminals k) :
    Nonempty (H.HindReduction terminals k) := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ (Z : Type u) [Fintype Z] [DecidableEq Z]
      (K : FiniteEdgeIndexedGraph Z) (T : Finset Z),
      Fintype.card K.Edge = n →
      K.TerminalElementConnectedAtLeast T k →
        Nonempty (K.HindReduction T k)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Z _ _ K T hcard hconnected
        by_cases hreduced : ∀ e : K.Edge,
            K.left e ∈ T ∨ K.right e ∈ T
        · exact ⟨HindReduction.refl K T k hconnected hreduced⟩
        · push Not at hreduced
          rcases hreduced with ⟨e, hleft, hright⟩
          rcases hindOellermannDeletionContraction K T k e hleft hright
              hconnected with hdelete | hcontract
          · have hlt : Fintype.card (K.deleteEdge e).Edge < n := by
              rw [K.deleteEdge_edgeCard e, hcard]
              have hpos : 0 < n := by
                rw [← hcard]
                exact Fintype.card_pos_iff.mpr ⟨e⟩
              omega
            rcases ih _ hlt Z (K.deleteEdge e) T rfl hdelete with ⟨R⟩
            exact ⟨{
              Vertex := R.Vertex
              graph := R.graph
              terminalMap := R.terminalMap
              terminalMap_injective := R.terminalMap_injective
              element_connected := R.element_connected
              terminal_degree_le := fun t =>
                (R.terminal_degree_le t).trans (K.deleteEdge_degree_le e t.1)
              every_edge_incident_terminal := R.every_edge_incident_terminal }⟩
          · let T' := ContractVertex.terminalImage
                (p := K.left e) (q := K.right e) T
            have hlt : Fintype.card (K.contractEdge e).Edge < n := by
              rw [← hcard]
              exact K.contractEdge_edgeCard_lt e
            rcases ih _ hlt (ContractVertex Z (K.left e) (K.right e))
                (K.contractEdge e) T' rfl hcontract with ⟨R⟩
            let project := K.contractionTerminalMap T e hleft hright
            let finalMap : TerminalVertex T → R.Vertex :=
              fun t => R.terminalMap (project t)
            have himage : terminalMapImage finalMap =
                terminalMapImage R.terminalMap := by
              ext z
              simp only [mem_terminalMapImage, finalMap]
              constructor
              · rintro ⟨t, rfl⟩
                exact ⟨project t, rfl⟩
              · rintro ⟨t', rfl⟩
                rcases K.contractionTerminalMap_surjective T e hleft hright t'
                  with ⟨t, rfl⟩
                exact ⟨t, rfl⟩
            exact ⟨{
              Vertex := R.Vertex
              graph := R.graph
              terminalMap := finalMap
              terminalMap_injective :=
                R.terminalMap_injective.comp
                  (K.contractionTerminalMap_injective T e hleft hright)
              element_connected := by
                rw [himage]
                exact R.element_connected
              terminal_degree_le := by
                intro t
                refine (R.terminal_degree_le (project t)).trans_eq ?_
                exact K.contractEdge_degree_terminal e T t.1 t.2 hleft hright
              every_edge_incident_terminal := by
                intro f
                simpa [himage] using R.every_edge_incident_terminal f }⟩
  exact hP (Fintype.card H.Edge) W H terminals rfl hconn

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
