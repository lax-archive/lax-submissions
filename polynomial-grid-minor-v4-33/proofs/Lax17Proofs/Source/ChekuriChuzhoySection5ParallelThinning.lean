import Lax17Proofs.Source.ChekuriChuzhoySection5ElementConnectivity

namespace Lax17Proofs

universe u v w

/-!
# Parallel-edge thinning at a terminal

This module formalizes the local simplification used after the
Hind--Oellermann reduction in Chekuri--Chuzhoy, journal Section 5.  If two
named parallel edges join a terminal to the same nonterminal, deleting one
copy preserves terminal element connectivity.

The proof uses canonical element cuts.  When the deleted copy would belong to
the available boundary, the surviving parallel copy pays for adding the
nonterminal endpoint to the removed-vertex set.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {H : FiniteEdgeIndexedGraph W}

omit [Fintype W] in
private theorem crosses_iff_of_joins
    {e₁ e₂ : H.Edge} {x y : W} {side : Finset W}
    (h₁ : H.Joins e₁ x y) (h₂ : H.Joins e₂ x y) :
    H.Crosses side e₁ ↔ H.Crosses side e₂ := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  all_goals simp [Crosses, h₁.1, h₁.2, h₂.1, h₂.2]
  all_goals tauto

omit [Fintype W] [DecidableEq W] in
private theorem endpoints_not_mem_of_joins
    {e : H.Edge} {x y : W} {removed : Finset W}
    (hjoin : H.Joins e x y)
    (hleft : H.left e ∉ removed) (hright : H.right e ∉ removed) :
    x ∉ removed ∧ y ∉ removed := by
  rcases hjoin with hjoin | hjoin
  · simpa [hjoin.1, hjoin.2] using And.intro hleft hright
  · simpa [hjoin.1, hjoin.2] using And.intro hright hleft

omit [Fintype W] [DecidableEq W] in
private theorem edge_endpoints_not_mem_of_joins
    {e : H.Edge} {x y : W} {removed : Finset W}
    (hjoin : H.Joins e x y) (hx : x ∉ removed) (hy : y ∉ removed) :
    H.left e ∉ removed ∧ H.right e ∉ removed := by
  rcases hjoin with hjoin | hjoin
  · simpa [hjoin.1, hjoin.2] using And.intro hx hy
  · simpa [hjoin.1, hjoin.2] using And.intro hy hx

omit [Fintype W] in
private theorem edge_ne_of_joins_of_endpoints_not_mem_insert
    {e e₀ : H.Edge} {x y : W} {removed : Finset W}
    (hjoin : H.Joins e₀ x y)
    (hleft : H.left e ∉ insert y removed)
    (hright : H.right e ∉ insert y removed) :
    e ≠ e₀ := by
  intro he
  subst e
  rcases hjoin with hjoin | hjoin
  · exact hright (by simp [hjoin.2])
  · exact hleft (by simp [hjoin.2])

omit [Fintype W] in
private theorem crosses_of_crosses_erase
    {e : H.Edge} {v : W} {side : Finset W}
    (hcross : H.Crosses (side.erase v) e)
    (hleft : H.left e ≠ v) (hright : H.right e ≠ v) :
    H.Crosses side e := by
  simp only [Crosses, mem_erase] at hcross ⊢
  tauto

/-- Deleting one of two named parallel copies joining a terminal to the same
nonterminal preserves terminal element connectivity.

This is the parallel-edge thinning step following the Hind--Oellermann
reduction in Chekuri--Chuzhoy, journal Section 5. -/
theorem TerminalElementConnectedAtLeast.deleteEdge_of_parallel_terminal_nonterminal
    {terminals : Finset W} {k : Nat}
    (hconnected : H.TerminalElementConnectedAtLeast terminals k)
    (eDrop eKeep : H.Edge) (hne : eDrop ≠ eKeep)
    {t v : W} (ht : t ∈ terminals) (hv : v ∉ terminals)
    (hDrop : H.Joins eDrop t v) (hKeep : H.Joins eKeep t v) :
    (H.deleteEdge eDrop).TerminalElementConnectedAtLeast terminals k := by
  rw [terminalElementConnectedAtLeast_iff_availableBoundary
    H terminals k] at hconnected
  rw [terminalElementConnectedAtLeast_iff_availableBoundary
    (H.deleteEdge eDrop) terminals k]
  intro a ha b hb hab removed side hremoved haSide hbSide hsideRemoved
  by_cases hDropAvailable : eDrop ∈ H.availableBoundary removed side
  · have hDropData :=
      (H.mem_availableBoundary removed side eDrop).mp hDropAvailable
    have hDropEndsNotRemoved : t ∉ removed ∧ v ∉ removed :=
      endpoints_not_mem_of_joins hDrop hDropData.2.1 hDropData.2.2
    have htNotRemoved : t ∉ removed := by
      intro htRemoved
      exact Finset.disjoint_left.mp hremoved htRemoved ht
    have htvNotRemoved : t ∉ removed ∧ v ∉ removed :=
      ⟨htNotRemoved, hDropEndsNotRemoved.2⟩
    have hKeepCrosses : H.Crosses side eKeep :=
      (crosses_iff_of_joins hDrop hKeep).mp hDropData.1
    have hKeepEndsNotRemoved :
        H.left eKeep ∉ removed ∧ H.right eKeep ∉ removed :=
      edge_endpoints_not_mem_of_joins hKeep
        htvNotRemoved.1 htvNotRemoved.2
    let keepEdge : (H.deleteEdge eDrop).Edge := ⟨eKeep, hne.symm⟩
    have hKeepAvailable :
        keepEdge ∈ (H.deleteEdge eDrop).availableBoundary removed side := by
      rw [(H.deleteEdge eDrop).mem_availableBoundary]
      change H.Crosses side eKeep ∧
        H.left eKeep ∉ removed ∧ H.right eKeep ∉ removed
      exact ⟨hKeepCrosses, hKeepEndsNotRemoved⟩
    have hremoved' : Disjoint (insert v removed) terminals := by
      rw [Finset.disjoint_left]
      intro x hx hxt
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv hxt
      · exact Finset.disjoint_left.mp hremoved hx hxt
    have haSide' : a ∈ side.erase v := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, haSide⟩
      intro hav
      subst a
      exact hv ha
    have hbSide' : b ∉ side.erase v := by
      intro hbSide'
      exact hbSide (Finset.mem_of_mem_erase hbSide')
    have hsideRemoved' : Disjoint (side.erase v) (insert v removed) := by
      rw [Finset.disjoint_left]
      intro x hxSide hxRemoved
      have hxne : x ≠ v := (Finset.mem_erase.mp hxSide).1
      rcases Finset.mem_insert.mp hxRemoved with hxv | hxRemoved
      · exact hxne hxv
      · exact Finset.disjoint_left.mp hsideRemoved
          (Finset.mem_of_mem_erase hxSide) hxRemoved
    have hsourceBound := hconnected ha hb hab
      (insert v removed) (side.erase v) hremoved'
      haSide' hbSide' hsideRemoved'
    let f :
        (H.availableBoundary (insert v removed) (side.erase v)) →
          ((H.deleteEdge eDrop).availableBoundary removed side) :=
      fun e => by
        have heData :=
          (H.mem_availableBoundary (insert v removed) (side.erase v) e.1).mp e.2
        have heNeDrop : e.1 ≠ eDrop :=
          edge_ne_of_joins_of_endpoints_not_mem_insert
            hDrop heData.2.1 heData.2.2
        let surviving : (H.deleteEdge eDrop).Edge := ⟨e.1, heNeDrop⟩
        refine ⟨surviving, ?_⟩
        rw [(H.deleteEdge eDrop).mem_availableBoundary]
        change H.Crosses side e.1 ∧
          H.left e.1 ∉ removed ∧ H.right e.1 ∉ removed
        have hleftNe : H.left e.1 ≠ v := by
          intro hleft
          exact heData.2.1 (by simp [hleft])
        have hrightNe : H.right e.1 ≠ v := by
          intro hright
          exact heData.2.2 (by simp [hright])
        exact
          ⟨crosses_of_crosses_erase heData.1 hleftNe hrightNe,
            fun hx => heData.2.1 (Finset.mem_insert_of_mem hx),
            fun hx => heData.2.2 (Finset.mem_insert_of_mem hx)⟩
    have hf : Function.Injective f := by
      intro e e' heq
      apply Subtype.ext
      exact congrArg
        (fun z : ((H.deleteEdge eDrop).availableBoundary removed side) =>
          z.1.1) heq
    have hfNotSurjective : ¬ Function.Surjective f := by
      intro hsurjective
      rcases hsurjective ⟨keepEdge, hKeepAvailable⟩ with ⟨e, he⟩
      have heData :=
        (H.mem_availableBoundary (insert v removed) (side.erase v) e.1).mp e.2
      have heNeKeep : e.1 ≠ eKeep :=
        edge_ne_of_joins_of_endpoints_not_mem_insert
          hKeep heData.2.1 heData.2.2
      apply heNeKeep
      exact congrArg
        (fun z : ((H.deleteEdge eDrop).availableBoundary removed side) =>
          z.1.1) he
    have hboundaryCard :
        (H.availableBoundary (insert v removed) (side.erase v)).card <
          ((H.deleteEdge eDrop).availableBoundary removed side).card := by
      rw [← Fintype.card_coe, ← Fintype.card_coe]
      exact Fintype.card_lt_of_injective_not_surjective f hf hfNotSurjective
    have hremovedCard : (insert v removed).card = removed.card + 1 :=
      Finset.card_insert_of_notMem htvNotRemoved.2
    exact hsourceBound.trans (by omega)
  · let f :
        (H.availableBoundary removed side) →
          ((H.deleteEdge eDrop).availableBoundary removed side) :=
      fun e => by
        have heNeDrop : e.1 ≠ eDrop := by
          intro heq
          apply hDropAvailable
          rw [← heq]
          exact e.2
        let surviving : (H.deleteEdge eDrop).Edge := ⟨e.1, heNeDrop⟩
        refine ⟨surviving, ?_⟩
        rw [(H.deleteEdge eDrop).mem_availableBoundary]
        change H.Crosses side e.1 ∧
          H.left e.1 ∉ removed ∧ H.right e.1 ∉ removed
        exact (H.mem_availableBoundary removed side e.1).mp e.2
    have hf : Function.Injective f := by
      intro e e' heq
      apply Subtype.ext
      exact congrArg
        (fun z : ((H.deleteEdge eDrop).availableBoundary removed side) =>
          z.1.1) heq
    have hboundaryCard :
        (H.availableBoundary removed side).card ≤
          ((H.deleteEdge eDrop).availableBoundary removed side).card := by
      rw [← Fintype.card_coe, ← Fintype.card_coe]
      exact Fintype.card_le_of_injective f hf
    exact (hconnected ha hb hab removed side hremoved
      haSide hbSide hsideRemoved).trans
        (Nat.add_le_add_left hboundaryCard removed.card)

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
