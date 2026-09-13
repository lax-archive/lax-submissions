import Lax17Proofs.Source.ChekuriChuzhoySection5ElementConnectivity

namespace Lax17Proofs

universe u v w

/-!
# Hind--Oellermann contraction-cut pullbacks

This module isolates the separator bookkeeping used in the contraction branch
of Hind--Oellermann's deletion/contraction argument.  A contracted cut has two
different cardinality behaviours according to whether its removed vertex set
contains the merged vertex.  If it does not, pulling the cut back preserves its
order exactly.  If it does, the two endpoints of the contracted edge replace
the merged vertex, increasing the order by exactly one.

The final Hind--Oellermann alternative is not proved here.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace ContractVertex

variable {W : Type u} [Fintype W] [DecidableEq W] {p q : W}

/-- Away from the merged vertex, projection is injective on a pulled-back
finite set. -/
theorem projection_injOn_preimageFinset_of_merged_not_mem
    (X : Finset (ContractVertex W p q))
    (hmerged : (merged : ContractVertex W p q) ∉ X) :
    Set.InjOn (projection (p := p) (q := q)) (preimageFinset X) := by
  intro x hx y hy hxy
  rcases eq_or_both_endpoints_of_projection_eq hxy with h | hends
  · exact h
  · have hxMerged : projection (p := p) (q := q) x = merged :=
      projection_eq_merged_iff.mpr hends.1
    exact (hmerged (hxMerged ▸ mem_preimageFinset.mp hx)).elim

/-- Pullback preserves cardinality when the contracted set omits the merged
vertex. -/
theorem preimageFinset_card_eq_of_merged_not_mem
    (X : Finset (ContractVertex W p q))
    (hmerged : (merged : ContractVertex W p q) ∉ X) :
    (preimageFinset X).card = X.card := by
  classical
  let Y := preimageFinset X
  have hinj : Set.InjOn (projection (p := p) (q := q)) Y :=
    projection_injOn_preimageFinset_of_merged_not_mem X hmerged
  have himageCard :
      (Y.image (projection (p := p) (q := q))).card = Y.card :=
    Finset.card_image_iff.mpr hinj
  have himage : Y.image (projection (p := p) (q := q)) = X := by
    ext z
    constructor
    · rintro hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact mem_preimageFinset.mp hw
    · intro hz
      rcases projection_surjective z with ⟨w, rfl⟩
      exact Finset.mem_image.mpr ⟨w, mem_preimageFinset.mpr hz, rfl⟩
  rw [himage] at himageCard
  exact himageCard.symm

/-- If the merged vertex is present, its pullback replaces one vertex by the
two distinct contracted endpoints. -/
theorem preimageFinset_card_eq_add_one_of_merged_mem
    (hpq : p ≠ q) (X : Finset (ContractVertex W p q))
    (hmerged : (merged : ContractVertex W p q) ∈ X) :
    (preimageFinset X).card = X.card + 1 := by
  classical
  let Y := preimageFinset X
  have hqY : q ∈ Y := by
    exact mem_preimageFinset.mpr (by simpa using hmerged)
  have hinj : Set.InjOn (projection (p := p) (q := q)) (Y.erase q) := by
    intro x hx y hy hxy
    have hxq : x ≠ q := (Finset.mem_erase.mp hx).1
    have hyq : y ≠ q := (Finset.mem_erase.mp hy).1
    rcases eq_or_both_endpoints_of_projection_eq hxy with h | ⟨hxends, hyends⟩
    · exact h
    · rcases hxends with hxp | hxq' <;> rcases hyends with hyp | hyq'
      · exact hxp.trans hyp.symm
      · exact (hyq hyq').elim
      · exact (hxq hxq').elim
      · exact (hxq hxq').elim
  have himageCard :
      ((Y.erase q).image (projection (p := p) (q := q))).card =
        (Y.erase q).card :=
    Finset.card_image_iff.mpr hinj
  have himage :
      (Y.erase q).image (projection (p := p) (q := q)) = X := by
    ext z
    constructor
    · rintro hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact mem_preimageFinset.mp (Finset.mem_of_mem_erase hw)
    · intro hz
      cases z with
      | merged =>
          exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hpq, by
            exact mem_preimageFinset.mpr (by simpa using hz)⟩, by simp⟩
      | keep w =>
          exact Finset.mem_image.mpr ⟨w.1, Finset.mem_erase.mpr ⟨w.2.2, by
            exact mem_preimageFinset.mpr (by
              simpa [projection_eq_keep w.2.1 w.2.2] using hz)⟩,
            projection_eq_keep w.2.1 w.2.2⟩
  have herase : Y.card = (Y.erase q).card + 1 :=
    (Finset.card_erase_add_one hqY).symm
  rw [himage] at himageCard
  calc
    (preimageFinset X).card = Y.card := rfl
    _ = (Y.erase q).card + 1 := herase
    _ = X.card + 1 := by rw [← himageCard]

end ContractVertex

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

namespace TerminalElementCut

variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}

/-- A contraction-cut pullback has exactly the same order if the cut does not
remove the merged vertex. -/
theorem liftContract_order_eq_of_merged_not_mem
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)} {a b : W}
    (ha : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) a = a')
    (hb : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) b = b')
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (hmerged : (ContractVertex.merged :
      ContractVertex W (H.left e0) (H.right e0)) ∉ C.removedVertices) :
    (C.liftContract H e0 terminals ha hb).order = C.order := by
  classical
  have hvertices :=
    ContractVertex.preimageFinset_card_eq_of_merged_not_mem
      C.removedVertices hmerged
  have hedges : (C.removedEdges.image Subtype.val).card = C.removedEdges.card :=
    Finset.card_image_iff.mpr fun x _ y _ hxy => Subtype.ext hxy
  simp only [TerminalElementCut.order, TerminalElementCut.liftContract]
  rw [hvertices, hedges]

/-- A contraction-cut pullback gains exactly one removed vertex if the cut
removes the merged vertex. -/
theorem liftContract_order_eq_add_one_of_merged_mem
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)} {a b : W}
    (ha : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) a = a')
    (hb : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) b = b')
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (hmerged : (ContractVertex.merged :
      ContractVertex W (H.left e0) (H.right e0)) ∈ C.removedVertices) :
    (C.liftContract H e0 terminals ha hb).order = C.order + 1 := by
  classical
  have hvertices :=
    ContractVertex.preimageFinset_card_eq_add_one_of_merged_mem
      (H.end_ne e0) C.removedVertices hmerged
  have hedges : (C.removedEdges.image Subtype.val).card = C.removedEdges.card :=
    Finset.card_image_iff.mpr fun x _ y _ hxy => Subtype.ext hxy
  simp only [TerminalElementCut.order, TerminalElementCut.liftContract]
  rw [hvertices, hedges]
  omega

/-- Upper-bound form of the merged-vertex pullback identity. -/
theorem liftContract_order_le_add_one_of_merged_mem
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)} {a b : W}
    (ha : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) a = a')
    (hb : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) b = b')
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (hmerged : (ContractVertex.merged :
      ContractVertex W (H.left e0) (H.right e0)) ∈ C.removedVertices) :
    (C.liftContract H e0 terminals ha hb).order ≤ C.order + 1 := by
  rw [C.liftContract_order_eq_add_one_of_merged_mem H e0 terminals ha hb hmerged]

omit [Fintype W] [DecidableEq W] in
/-- Endpoints of a terminal cut are necessarily distinct. -/
theorem source_ne_target
    {a b : W} (C : TerminalElementCut H terminals a b) : a ≠ b := by
  intro hab
  subst b
  exact C.target_not_mem C.source_mem

/-- A contracted terminal cut omitting the merged vertex pulls back to an
equal-order cut separating two distinct original terminals. -/
theorem exists_original_terminal_cut_of_merged_not_mem
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)}
    (ha' : a' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (hb' : b' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (hmerged : (ContractVertex.merged :
      ContractVertex W (H.left e0) (H.right e0)) ∉ C.removedVertices) :
    ∃ a ∈ terminals, ∃ b ∈ terminals, a ≠ b ∧
      ∃ D : TerminalElementCut H terminals a b, D.order = C.order := by
  rw [ContractVertex.mem_terminalImage] at ha' hb'
  rcases ha' with ⟨a, ha, hpa⟩
  rcases hb' with ⟨b, hb, hpb⟩
  have hab : a ≠ b := by
    intro hab
    subst b
    exact C.source_ne_target (hpa.symm.trans hpb)
  refine ⟨a, ha, b, hb, hab, C.liftContract H e0 terminals hpa hpb, ?_⟩
  exact C.liftContract_order_eq_of_merged_not_mem
    H e0 terminals hpa hpb hmerged

/-- A contracted terminal cut containing the merged vertex pulls back to a
cut separating two distinct original terminals with at most one extra removed
element. -/
theorem exists_original_terminal_cut_of_merged_mem
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)}
    (ha' : a' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (hb' : b' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (hmerged : (ContractVertex.merged :
      ContractVertex W (H.left e0) (H.right e0)) ∈ C.removedVertices) :
    ∃ a ∈ terminals, ∃ b ∈ terminals, a ≠ b ∧
      ∃ D : TerminalElementCut H terminals a b, D.order ≤ C.order + 1 := by
  rw [ContractVertex.mem_terminalImage] at ha' hb'
  rcases ha' with ⟨a, ha, hpa⟩
  rcases hb' with ⟨b, hb, hpb⟩
  have hab : a ≠ b := by
    intro hab
    subst b
    exact C.source_ne_target (hpa.symm.trans hpb)
  refine ⟨a, ha, b, hb, hab, C.liftContract H e0 terminals hpa hpb, ?_⟩
  exact C.liftContract_order_le_add_one_of_merged_mem
    H e0 terminals hpa hpb hmerged

end TerminalElementCut

variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}

/-- Original terminal element connectivity gives the full lower bound for a
contracted cut that omits the merged vertex. -/
theorem TerminalElementConnectedAtLeast.le_contractCut_order_of_merged_not_mem
    {k : Nat} (h : H.TerminalElementConnectedAtLeast terminals k)
    (e0 : H.Edge)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)}
    (ha' : a' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (hb' : b' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (hmerged : (ContractVertex.merged :
      ContractVertex W (H.left e0) (H.right e0)) ∉ C.removedVertices) :
    k ≤ C.order := by
  rcases C.exists_original_terminal_cut_of_merged_not_mem
      H e0 terminals ha' hb' hmerged with
    ⟨a, ha, b, hb, hab, D, horder⟩
  calc
    k ≤ D.order := h ha hb hab D
    _ = C.order := horder

/-- In the merged-vertex branch, original connectivity supplies only the
one-unit-weaker lower bound furnished by the direct pullback. -/
theorem TerminalElementConnectedAtLeast.le_contractCut_order_add_one_of_merged_mem
    {k : Nat} (h : H.TerminalElementConnectedAtLeast terminals k)
    (e0 : H.Edge)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)}
    (ha' : a' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (hb' : b' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (hmerged : (ContractVertex.merged :
      ContractVertex W (H.left e0) (H.right e0)) ∈ C.removedVertices) :
    k ≤ C.order + 1 := by
  rcases C.exists_original_terminal_cut_of_merged_mem
      H e0 terminals ha' hb' hmerged with
    ⟨a, ha, b, hb, hab, D, horder⟩
  exact (h ha hb hab D).trans horder

/-- Consequently, every contracted terminal cut below the original
connectivity value must remove the merged vertex. -/
theorem TerminalElementConnectedAtLeast.merged_mem_of_contractCut_order_lt
    {k : Nat} (h : H.TerminalElementConnectedAtLeast terminals k)
    (e0 : H.Edge)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)}
    (ha' : a' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (hb' : b' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals)
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (horder : C.order < k) :
    (ContractVertex.merged :
      ContractVertex W (H.left e0) (H.right e0)) ∈ C.removedVertices := by
  by_contra hmerged
  exact (Nat.not_lt_of_ge
    (TerminalElementConnectedAtLeast.le_contractCut_order_of_merged_not_mem
      h e0 ha' hb' C hmerged)) horder

/-- Direct integration form for a deficient contracted cut.  Once original
terminal representatives are fixed, the cut must remove the merged vertex;
its standard pullback has the sharp one-unit order increase and removes both
endpoints of the contracted edge. -/
theorem TerminalElementConnectedAtLeast.deficient_contractCut_liftContract
    {k : Nat} (h : H.TerminalElementConnectedAtLeast terminals k)
    (e0 : H.Edge)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)} {a b : W}
    (ha : a ∈ terminals) (hb : b ∈ terminals)
    (hpa : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) a = a')
    (hpb : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) b = b')
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b')
    (horder : C.order < k) :
    (ContractVertex.merged :
        ContractVertex W (H.left e0) (H.right e0)) ∈ C.removedVertices ∧
      (C.liftContract H e0 terminals hpa hpb).order = C.order + 1 ∧
      (C.liftContract H e0 terminals hpa hpb).order ≤ k ∧
      H.left e0 ∈ (C.liftContract H e0 terminals hpa hpb).removedVertices ∧
      H.right e0 ∈
        (C.liftContract H e0 terminals hpa hpb).removedVertices := by
  have ha' : a' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals :=
    Finset.mem_image.mpr ⟨a, ha, hpa⟩
  have hb' : b' ∈ ContractVertex.terminalImage
      (p := H.left e0) (q := H.right e0) terminals :=
    Finset.mem_image.mpr ⟨b, hb, hpb⟩
  have hmerged :=
    h.merged_mem_of_contractCut_order_lt e0 ha' hb' C horder
  have hliftOrder := C.liftContract_order_eq_add_one_of_merged_mem
    H e0 terminals hpa hpb hmerged
  have hliftLe : (C.liftContract H e0 terminals hpa hpb).order ≤ k := by
    rw [hliftOrder]
    omega
  have hpRemoved :
      H.left e0 ∈ (C.liftContract H e0 terminals hpa hpb).removedVertices := by
    change H.left e0 ∈ ContractVertex.preimageFinset C.removedVertices
    rw [ContractVertex.mem_preimageFinset]
    simpa using hmerged
  have hqRemoved :
      H.right e0 ∈ (C.liftContract H e0 terminals hpa hpb).removedVertices := by
    change H.right e0 ∈ ContractVertex.preimageFinset C.removedVertices
    rw [ContractVertex.mem_preimageFinset]
    simpa using hmerged
  exact ⟨hmerged, hliftOrder, hliftLe, hpRemoved, hqRemoved⟩

end FiniteEdgeIndexedGraph

end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
