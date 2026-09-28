import Lax303502Proofs.OuterConnectivity
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph

/-- A connected component after deleting `T`, with another surviving vertex. -/
structure CutComponent {V : Type*} (G : SimpleGraph V) (T C : Set V) : Prop where
  connected : (G.induce C).Connected
  disjoint : Disjoint C T
  boundary : ∀ a ∈ C, ∀ b, b ∉ C → G.Adj a b → b ∈ T
  outside : (Tᶜ \ C).Nonempty

/-- Deleting at most two vertices leaves a connected graph. The cardinality
condition for three-connectivity is imposed separately at its uses. -/
def ThreeRobust {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card ≤ 2 → (G.induce (S : Set V)ᶜ).Preconnected

namespace CutComponent

variable {V : Type*} {G : SimpleGraph V} {T C D : Set V}

theorem subset_compl (h : CutComponent G T C) : C ⊆ Tᶜ :=
  fun _ hx ht => Set.disjoint_left.mp h.disjoint hx ht

theorem nonempty (h : CutComponent G T C) : C.Nonempty := by
  obtain ⟨x⟩ := h.connected.nonempty
  exact ⟨x,x.property⟩

theorem mem_of_adj (h : CutComponent G T C) {a b : V}
    (ha : a ∈ C) (hb : b ∉ T) (hab : G.Adj a b) : b ∈ C := by
  by_contra hn
  exact hb (h.boundary a ha b hn hab)

/-- A connected set avoiding the deleted vertices cannot cross a component boundary. -/
theorem contains_connected (h : CutComponent G T C)
    (hD : (G.induce D).Preconnected) (hDT : Disjoint D T)
    (hmeet : (C ∩ D).Nonempty) : D ⊆ C := by
  obtain ⟨x,hxC,hxD⟩ := hmeet
  intro y hyD
  by_contra hyC
  obtain ⟨a,haD,b,hbD,haC,hbC,hab⟩ := preconnected_boundary hD hxD hyD hxC hyC
  exact Set.disjoint_left.mp hDT hbD (h.boundary a haC b hbC hab)

/-- Every member of a minimal three-vertex separator sees every component. -/
theorem attachment [DecidableEq V] (h : CutComponent G T C)
    (hrob : ThreeRobust G) (S : Finset V) (hS : (S : Set V) = T)
    (hcard : S.card ≤ 3) {t : V} (ht : t ∈ S) : ∃ a ∈ C, G.Adj t a := by
  obtain ⟨x,hx⟩ := h.nonempty
  obtain ⟨y,hyT,hyC⟩ := h.outside
  have htcard : (S.erase t).card ≤ 2 := by
    rw [Finset.card_erase_of_mem ht]
    omega
  have hsub : (↑(S.erase t) : Set V) ⊆ T := by
    intro a ha
    rw [← hS]
    exact Finset.mem_of_mem_erase ha
  have hx' : x ∈ (↑(S.erase t) : Set V)ᶜ := fun hx' => h.subset_compl hx (hsub hx')
  have hy' : y ∈ (↑(S.erase t) : Set V)ᶜ := fun hy' => hyT (hsub hy')
  obtain ⟨a,_,b,hb',ha,hb,hab⟩ :=
    preconnected_boundary (hrob (S.erase t) htcard) hx' hy' hx hyC
  have hbS : b ∈ S := by
    change b ∈ (S : Set V)
    rw [hS]
    exact h.boundary a ha b hb hab
  have hbt : b = t := by
    by_contra hne
    exact hb' (Finset.mem_erase.mpr ⟨hne,hbS⟩)
  exact ⟨a,ha,hbt ▸ hab.symm⟩

end CutComponent

/-- A disconnected complement has a component with a nonempty remainder. -/
theorem exists_cutComponent {V : Type*} {G : SimpleGraph V} {T : Set V}
    (hn : ¬(G.induce Tᶜ).Preconnected) : ∃ C, CutComponent G T C := by
  classical
  change ¬∀ x y : ↥(Tᶜ), (G.induce Tᶜ).Reachable x y at hn
  push Not at hn
  obtain ⟨x,y,hxy⟩ := hn
  obtain ⟨C,hx,hC,hd,hb⟩ := outside_component (G:=G) T x.property
  have hy : y.val ∉ C := by
    intro hy
    let f : G.induce C →g G.induce Tᶜ :=
      ⟨fun a => ⟨a,fun ht => Set.disjoint_left.mp hd a.property ht⟩,fun h => h⟩
    obtain ⟨p⟩ := hC.preconnected ⟨x,hx⟩ ⟨y,hy⟩
    exact hxy ⟨p.map f⟩
  exact ⟨C,⟨hC,hd,hb,⟨y,y.property,hy⟩⟩⟩

/-- From the other side of one component, obtain a disjoint component. -/
theorem CutComponent.other {V : Type*} {G : SimpleGraph V} {T C : Set V}
    (h : CutComponent G T C) : ∃ D, CutComponent G T D ∧ Disjoint C D := by
  obtain ⟨y,hyT,hyC⟩ := h.outside
  obtain ⟨D,hy,hD,hd,hb⟩ := outside_component (G:=G) T hyT
  have hCD : Disjoint C D := by
    rw [Set.disjoint_left]
    intro x hxC hxD
    exact hyC (h.contains_connected hD.preconnected hd ⟨x,hxC,hxD⟩ hy)
  obtain ⟨x,hx⟩ := h.nonempty
  exact ⟨D,⟨hD,hd,hb,⟨x,h.subset_compl hx,fun hxD => Set.disjoint_left.mp hCD hx hxD⟩⟩,hCD⟩

/-- Adjacent vertices cannot occupy different components; hence one component
of a disconnected complement avoids both. -/
theorem cutComponent_avoiding_edge {V : Type*} {G : SimpleGraph V} {T : Set V}
    (hn : ¬(G.induce Tᶜ).Preconnected) {x y : V} (hxy : G.Adj x y) :
    ∃ C, CutComponent G T C ∧ x ∉ C ∧ y ∉ C := by
  classical
  obtain ⟨C,hC⟩ := exists_cutComponent hn
  by_cases hx : x ∈ C
  · obtain ⟨D,hD,hd⟩ := hC.other
    refine ⟨D,hD,fun hxD => Set.disjoint_left.mp hd hx hxD,?_⟩
    intro hyD
    have hxD := hD.mem_of_adj hyD (hC.subset_compl hx) hxy.symm
    exact Set.disjoint_left.mp hd hx hxD
  · by_cases hy : y ∈ C
    · obtain ⟨D,hD,hd⟩ := hC.other
      refine ⟨D,hD,?_,fun hyD => Set.disjoint_left.mp hd hy hyD⟩
      intro hxD
      have hyD := hD.mem_of_adj hxD (hC.subset_compl hy) hxy
      exact Set.disjoint_left.mp hd hy hyD
    · exact ⟨C,hC,hx,hy⟩

end Lax303502Proofs
