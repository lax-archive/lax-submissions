import Lax17Proofs.Source.ChekuriChuzhoySection5TerminalSkeleton

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 edge contraction

This file supplies the finite bookkeeping used immediately before the
Hind--Oellermann deletion/contraction theorem in the proof of journal
Theorem 5.12 (preprint Theorem 5.10).  Contracting a named edge identifies its
endpoints and discards every named edge copy that thereby becomes a loop.
All other copies retain their original indices, so parallel edges are not
collapsed.

No connectivity alternative from Hind--Oellermann is assumed here.  The
results below are the elementary projection, incidence, boundary, and
cardinality facts needed to state and prove that alternative separately.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

/-! ## Contracted vertices -/

/-- Vertices obtained by identifying `p` and `q`.  The constructor `merged`
represents both endpoints; every other original vertex has its own `keep`
vertex. -/
inductive ContractVertex (W : Type u) (p q : W) where
  | merged : ContractVertex W p q
  | keep : {w : W // w ≠ p ∧ w ≠ q} -> ContractVertex W p q
deriving DecidableEq

namespace ContractVertex

variable {W : Type u} {p q : W}

noncomputable instance [Fintype W] : Fintype (ContractVertex W p q) := by
  classical
  exact Fintype.ofEquiv
    (Unit ⊕ {w : W // w ≠ p ∧ w ≠ q})
    { toFun := fun x =>
        match x with
        | Sum.inl _ => merged
        | Sum.inr w => keep w
      invFun := fun x =>
        match x with
        | merged => Sum.inl ()
        | keep w => Sum.inr w
      left_inv := by
        intro x
        cases x with
        | inl x => cases x; rfl
        | inr x => rfl
      right_inv := by
        intro x
        cases x <;> rfl }

/-- Project an original vertex to the contracted vertex type. -/
def projection [DecidableEq W] (w : W) : ContractVertex W p q :=
  if hw : w = p ∨ w = q then
    merged
  else
    keep ⟨w, fun h => hw (Or.inl h), fun h => hw (Or.inr h)⟩

@[simp] theorem projection_left [DecidableEq W] :
    projection (p := p) (q := q) p = merged := by
  simp [projection]

@[simp] theorem projection_right [DecidableEq W] :
    projection (p := p) (q := q) q = merged := by
  simp [projection]

theorem projection_eq_keep [DecidableEq W] {w : W} (hwp : w ≠ p) (hwq : w ≠ q) :
    projection (p := p) (q := q) w = keep ⟨w, hwp, hwq⟩ := by
  simp [projection, hwp, hwq]

@[simp] theorem projection_eq_merged_iff [DecidableEq W] {w : W} :
    projection (p := p) (q := q) w = merged ↔ w = p ∨ w = q := by
  by_cases hw : w = p ∨ w = q
  · simp [projection, hw]
  · constructor
    · intro h
      simp [projection, hw] at h
    · exact fun h => (hw h).elim

/-- Projection identifies only the two contracted endpoints. -/
theorem eq_or_both_endpoints_of_projection_eq [DecidableEq W] {x y : W}
    (h : projection (p := p) (q := q) x = projection (p := p) (q := q) y) :
    x = y ∨ (x = p ∨ x = q) ∧ (y = p ∨ y = q) := by
  by_cases hx : x = p ∨ x = q
  · right
    refine ⟨hx, ?_⟩
    rw [← projection_eq_merged_iff]
    simpa [projection, hx] using h.symm
  · by_cases hy : y = p ∨ y = q
    · have hxMerged : projection (p := p) (q := q) x = merged := by
        simpa [projection, hy] using h
      exact (hx (projection_eq_merged_iff.mp hxMerged)).elim
    · left
      have hkeep :
          keep ⟨x, fun hxp => hx (Or.inl hxp), fun hxq => hx (Or.inr hxq)⟩ =
            keep ⟨y, fun hyp => hy (Or.inl hyp), fun hyq => hy (Or.inr hyq)⟩ := by
        simpa [projection, hx, hy] using h
      injection hkeep with hsub
      exact congrArg Subtype.val hsub

theorem eq_of_projection_eq_of_right_not_endpoint [DecidableEq W] {x y : W}
    (h : projection (p := p) (q := q) x = projection (p := p) (q := q) y)
    (hyp : y ≠ p) (hyq : y ≠ q) : x = y := by
  rcases eq_or_both_endpoints_of_projection_eq h with hxy | ⟨_hx, hy⟩
  · exact hxy
  · exact (hy.elim hyp hyq).elim

theorem projection_surjective [DecidableEq W] :
    Function.Surjective (projection (W := W) (p := p) (q := q)) := by
  intro x
  cases x with
  | merged => exact ⟨p, projection_left⟩
  | keep w => exact ⟨w.1, projection_eq_keep w.2.1 w.2.2⟩

/-- The contracted vertex type has exactly one fewer vertex. -/
theorem card [Fintype W] [DecidableEq W] (hpq : p ≠ q) :
    Fintype.card (ContractVertex W p q) = Fintype.card W - 1 := by
  classical
  let e : ContractVertex W p q ≃ {w : W // w ≠ q} :=
    { toFun := fun x =>
        match x with
        | merged => ⟨p, hpq⟩
        | keep w => ⟨w.1, w.2.2⟩
      invFun := fun w =>
        if hwp : w.1 = p then merged
        else keep ⟨w.1, hwp, w.2⟩
      left_inv := by
        intro x
        cases x with
        | merged => simp
        | keep w => simp [w.2.1]
      right_inv := by
        intro w
        by_cases hwp : w.1 = p
        · apply Subtype.ext
          simp [hwp]
        · apply Subtype.ext
          simp [hwp] }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  rw [show (Finset.univ.filter fun w : W => w ≠ q) = Finset.univ.erase q by
    ext w
    simp]
  exact Finset.card_erase_of_mem (Finset.mem_univ q)

/-- The image of a terminal set under the contraction projection. -/
def terminalImage [DecidableEq W] (terminals : Finset W) :
    Finset (ContractVertex W p q) :=
  terminals.image (projection (p := p) (q := q))

@[simp] theorem mem_terminalImage [DecidableEq W] {terminals : Finset W}
    {x : ContractVertex W p q} :
    x ∈ terminalImage (p := p) (q := q) terminals ↔
      ∃ t ∈ terminals, projection (p := p) (q := q) t = x := by
  simp [terminalImage]

theorem projection_injective_on [DecidableEq W] {terminals : Finset W}
    (hp : p ∉ terminals) (hq : q ∉ terminals) :
    Set.InjOn (projection (p := p) (q := q)) terminals := by
  intro x hx y hy hxy
  exact eq_of_projection_eq_of_right_not_endpoint hxy
    (fun h => hp (h ▸ hy)) (fun h => hq (h ▸ hy))

theorem terminalImage_card [DecidableEq W] (terminals : Finset W)
    (hp : p ∉ terminals) (hq : q ∉ terminals) :
    (terminalImage (p := p) (q := q) terminals).card = terminals.card := by
  classical
  exact Finset.card_image_iff.mpr (projection_injective_on hp hq)

theorem projection_mem_terminalImage_iff [DecidableEq W]
    (terminals : Finset W) (hp : p ∉ terminals) (hq : q ∉ terminals) (w : W) :
    projection (p := p) (q := q) w ∈ terminalImage (p := p) (q := q) terminals ↔
      w ∈ terminals := by
  constructor
  · rw [mem_terminalImage]
    rintro ⟨t, ht, htw⟩
    have hwt := eq_of_projection_eq_of_right_not_endpoint htw.symm
      (fun h => hp (h ▸ ht)) (fun h => hq (h ▸ ht))
    simpa [hwt] using ht
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

theorem merged_not_mem_terminalImage [DecidableEq W]
    (terminals : Finset W) (hp : p ∉ terminals) (hq : q ∉ terminals) :
    (merged : ContractVertex W p q) ∉ terminalImage (p := p) (q := q) terminals := by
  rw [mem_terminalImage]
  rintro ⟨t, ht, hmerged⟩
  rcases projection_eq_merged_iff.mp hmerged with rfl | rfl
  · exact hp ht
  · exact hq ht

/-- Pull a contracted vertex set back along the projection. -/
def preimageFinset [Fintype W] [DecidableEq W]
    (X : Finset (ContractVertex W p q)) : Finset W :=
  Finset.univ.filter fun w => projection (p := p) (q := q) w ∈ X

@[simp] theorem mem_preimageFinset [Fintype W] [DecidableEq W]
    {X : Finset (ContractVertex W p q)} {w : W} :
    w ∈ preimageFinset X ↔ projection (p := p) (q := q) w ∈ X := by
  simp [preimageFinset]

theorem preimageFinset_nonempty [Fintype W] [DecidableEq W]
    {X : Finset (ContractVertex W p q)} (hX : X.Nonempty) :
    (preimageFinset X).Nonempty := by
  rcases hX with ⟨x, hx⟩
  rcases projection_surjective x with ⟨w, rfl⟩
  exact ⟨w, by simpa⟩

theorem preimageFinset_ne_univ [Fintype W] [DecidableEq W]
    {X : Finset (ContractVertex W p q)} (hX : X ≠ Finset.univ) :
    preimageFinset X ≠ Finset.univ := by
  intro hpre
  apply hX
  ext x
  constructor
  · exact fun _ => Finset.mem_univ x
  · intro _
    rcases projection_surjective x with ⟨w, rfl⟩
    have hw : w ∈ preimageFinset X := by simp [hpre]
    simpa using hw

end ContractVertex

/-! ## Named-edge contraction -/

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Both endpoints of an edge lie outside the designated terminal set. -/
def IsNonterminalEdge
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (e : H.Edge) : Prop :=
  H.left e ∉ terminals ∧ H.right e ∉ terminals

/-- An edge survives contraction exactly when its projected endpoints remain
distinct. -/
def SurvivesContraction (H : FiniteEdgeIndexedGraph W) (e0 e : H.Edge) : Prop :=
  ContractVertex.projection (p := H.left e0) (q := H.right e0) (H.left e) ≠
    ContractVertex.projection (p := H.left e0) (q := H.right e0) (H.right e)

/-- Contract `e0`, retaining every named edge copy whose endpoints are not
identified.  In particular, parallel surviving copies remain distinct. -/
noncomputable def contractEdge (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) :
    FiniteEdgeIndexedGraph
      (ContractVertex W (H.left e0) (H.right e0)) := by
  classical
  exact
    { Edge := {e : H.Edge // H.SurvivesContraction e0 e}
      left := fun e => ContractVertex.projection
        (p := H.left e0) (q := H.right e0) (H.left e.1)
      right := fun e => ContractVertex.projection
        (p := H.left e0) (q := H.right e0) (H.right e.1)
      end_ne := fun e => e.2 }

@[simp] theorem contractEdge_left (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (e : (H.contractEdge e0).Edge) :
    (H.contractEdge e0).left e = ContractVertex.projection
      (p := H.left e0) (q := H.right e0) (H.left e.1) := rfl

@[simp] theorem contractEdge_right (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (e : (H.contractEdge e0).Edge) :
    (H.contractEdge e0).right e = ContractVertex.projection
      (p := H.left e0) (q := H.right e0) (H.right e.1) := rfl

theorem contractedEdge_does_not_survive (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) :
    ¬ H.SurvivesContraction e0 e0 := by
  simp [SurvivesContraction]

/-- Contracting an edge strictly decreases the number of named edge copies.
Every parallel copy whose endpoints are identified is discarded as a loop. -/
theorem contractEdge_edgeCard_lt (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) :
    Fintype.card (H.contractEdge e0).Edge < Fintype.card H.Edge := by
  apply Fintype.card_lt_of_injective_not_surjective
    (fun e : (H.contractEdge e0).Edge => e.1)
  · exact Subtype.val_injective
  · intro hsurj
    rcases hsurj e0 with ⟨e, he⟩
    have : e.1 = e0 := he
    have hsurvives := e.2
    rw [this] at hsurvives
    exact contractedEdge_does_not_survive H e0 hsurvives

theorem contractEdge_edgeCard_le_sub_one (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) :
    Fintype.card (H.contractEdge e0).Edge ≤ Fintype.card H.Edge - 1 := by
  have hlt := contractEdge_edgeCard_lt H e0
  omega

theorem survivesContraction_of_incident_terminal
    (H : FiniteEdgeIndexedGraph W) (e0 e : H.Edge) {terminals : Finset W} {t : W}
    (ht : t ∈ terminals) (hp : H.left e0 ∉ terminals) (hq : H.right e0 ∉ terminals)
    (he : H.left e = t ∨ H.right e = t) : H.SurvivesContraction e0 e := by
  intro hproj
  rcases ContractVertex.eq_or_both_endpoints_of_projection_eq hproj with heq | hends
  · exact H.end_ne e heq
  · rcases he with hleft | hright
    · have htEnds : t = H.left e0 ∨ t = H.right e0 := hleft ▸ hends.1
      exact htEnds.elim (fun h => hp (h ▸ ht)) (fun h => hq (h ▸ ht))
    · have htEnds : t = H.left e0 ∨ t = H.right e0 := hright ▸ hends.2
      exact htEnds.elim (fun h => hp (h ▸ ht)) (fun h => hq (h ▸ ht))

/-- At a terminal, incidence is unchanged by contraction of a nonterminal
edge. -/
noncomputable def contractEdgeIncidentEquiv
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    (t : W) (ht : t ∈ terminals)
    (hp : H.left e0 ∉ terminals) (hq : H.right e0 ∉ terminals) :
    (H.contractEdge e0).incidentEdges
        (ContractVertex.projection
          (p := H.left e0) (q := H.right e0) t) ≃
      H.incidentEdges t where
  toFun e := ⟨e.1.1, by
    rw [H.mem_incidentEdges]
    rcases ((H.contractEdge e0).mem_incidentEdges _ e.1).mp e.2 with h | h
    · left
      exact ContractVertex.eq_of_projection_eq_of_right_not_endpoint h
        (fun hte => hp (hte ▸ ht)) (fun hte => hq (hte ▸ ht))
    · right
      exact ContractVertex.eq_of_projection_eq_of_right_not_endpoint h
        (fun hte => hp (hte ▸ ht)) (fun hte => hq (hte ▸ ht))⟩
  invFun e :=
    ⟨⟨e.1, survivesContraction_of_incident_terminal H e0 e.1 ht hp hq
      ((H.mem_incidentEdges t e.1).mp e.2)⟩, by
      rw [(H.contractEdge e0).mem_incidentEdges]
      rcases (H.mem_incidentEdges t e.1).mp e.2 with h | h
      · exact Or.inl (congrArg (ContractVertex.projection
          (p := H.left e0) (q := H.right e0)) h)
      · exact Or.inr (congrArg (ContractVertex.projection
          (p := H.left e0) (q := H.right e0)) h)⟩
  left_inv := by
    intro e
    exact Subtype.ext (Subtype.ext rfl)
  right_inv := by
    intro e
    exact Subtype.ext rfl

theorem contractEdge_degree_terminal
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    (t : W) (ht : t ∈ terminals)
    (hp : H.left e0 ∉ terminals) (hq : H.right e0 ∉ terminals) :
    (H.contractEdge e0).degree
        (ContractVertex.projection
          (p := H.left e0) (q := H.right e0) t) = H.degree t := by
  unfold degree
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (contractEdgeIncidentEquiv H e0 terminals t ht hp hq)

/-- A contracted edge crosses `X` exactly when its original copy crosses the
pullback of `X`. -/
theorem contractEdge_crosses_iff (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (X : Finset (ContractVertex W (H.left e0) (H.right e0)))
    (e : (H.contractEdge e0).Edge) :
    (H.contractEdge e0).Crosses X e ↔
      H.Crosses (ContractVertex.preimageFinset X) e.1 := by
  simp only [Crosses, contractEdge_left, contractEdge_right,
    ContractVertex.mem_preimageFinset]

/-- Boundary copies are in canonical bijection across contraction and
pullback. -/
noncomputable def contractEdgeBoundaryEquiv
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (X : Finset (ContractVertex W (H.left e0) (H.right e0))) :
    (H.contractEdge e0).boundary X ≃
      H.boundary (ContractVertex.preimageFinset X) where
  toFun e := ⟨e.1.1, by
    rw [H.mem_boundary]
    exact (contractEdge_crosses_iff H e0 X e.1).mp
      (((H.contractEdge e0).mem_boundary X e.1).mp e.2)⟩
  invFun e := by
    have hcross : H.Crosses (ContractVertex.preimageFinset X) e.1 :=
      (H.mem_boundary _ e.1).mp e.2
    have hsurvives : H.SurvivesContraction e0 e.1 := by
      intro heq
      rcases hcross with hcross | hcross
      · have hleft : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.left e.1) ∈ X := by
          simpa using hcross.1
        have hright : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.right e.1) ∉ X := by
          simpa using hcross.2
        exact hright (heq ▸ hleft)
      · have hright : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.right e.1) ∈ X := by
          simpa using hcross.1
        have hleft : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.left e.1) ∉ X := by
          simpa using hcross.2
        exact hleft (heq.symm ▸ hright)
    exact ⟨⟨e.1, hsurvives⟩,
      (H.contractEdge e0).mem_boundary X ⟨e.1, hsurvives⟩ |>.mpr
        ((contractEdge_crosses_iff H e0 X ⟨e.1, hsurvives⟩).mpr hcross)⟩
  left_inv := by
    intro e
    exact Subtype.ext (Subtype.ext rfl)
  right_inv := by
    intro e
    exact Subtype.ext rfl

theorem contractEdge_boundary_card
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (X : Finset (ContractVertex W (H.left e0) (H.right e0))) :
    ((H.contractEdge e0).boundary X).card =
      (H.boundary (ContractVertex.preimageFinset X)).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (contractEdgeBoundaryEquiv H e0 X)

/-- Ordinary edge-connectivity cannot decrease under contraction.  This is
strictly weaker than the terminal element-connectivity alternative of
Hind--Oellermann. -/
theorem IsEdgeConnected.contractEdge {H : FiniteEdgeIndexedGraph W} {k : Nat}
    (h : H.IsEdgeConnected k) (e0 : H.Edge) :
    (H.contractEdge e0).IsEdgeConnected k := by
  intro X hX hXproper
  rw [contractEdge_boundary_card]
  exact h (ContractVertex.preimageFinset X)
    (ContractVertex.preimageFinset_nonempty hX)
    (ContractVertex.preimageFinset_ne_univ hXproper)

end FiniteEdgeIndexedGraph

end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
