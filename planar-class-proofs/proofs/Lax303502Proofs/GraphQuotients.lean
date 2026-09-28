import Lax303502Proofs.ContractibleEdge
import Lax303502Proofs.FourFans

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.GraphMinors

/-- Map a path through a vertex identification, suppressing collapsed steps. -/
theorem reachable_map_weak {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : ∀ {x y}, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y))
    {a b : V} (h : G.Reachable a b) : H.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | @cons a b c hab p ih =>
    rcases hf hab with he | he
    · exact he ▸ ih
    · exact he.reachable.trans ih

/-- Connectivity survives a surjective vertex identification. -/
theorem preconnected_map_set {V W : Type*} {G : SimpleGraph V} (f : V → W)
    {A : Set V} {B : Set W} (hA : (G.induce A).Preconnected)
    (hf : f '' A = B) : ((G.map f).induce B).Preconnected := by
  classical
  let g : A → B := fun a => ⟨f a,hf ▸ ⟨a,a.property,rfl⟩⟩
  have hg : ∀ {a b}, (G.induce A).Adj a b →
      g a = g b ∨ ((G.map f).induce B).Adj (g a) (g b) := by
    intro a b hab
    by_cases he : f a = f b
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (G.map_adj_apply' hab he)
  intro x y
  have hxmem : x.val ∈ f '' A := by rw [hf]; exact x.property
  have hymem : y.val ∈ f '' A := by rw [hf]; exact y.property
  obtain ⟨a,ha,hax⟩ := hxmem
  obtain ⟨b,hb,hby⟩ := hymem
  have hh := reachable_map_weak g hg (hA ⟨a,ha⟩ ⟨b,hb⟩)
  have hx : g ⟨a,ha⟩ = x := Subtype.ext hax
  have hy : g ⟨b,hb⟩ = y := Subtype.ext hby
  exact hx ▸ hy ▸ hh

/-- A connected graph of nonempty connected vertex sets has connected union
when every index edge is witnessed by an edge between its two sets. -/
theorem connected_union_along {I V : Type*} {H : SimpleGraph I} {G : SimpleGraph V}
    (hH : H.Connected) (S : I → Set V) (hS : ∀ i, (G.induce (S i)).Connected)
    (he : ∀ {i j}, H.Adj i j → ∃ a ∈ S i, ∃ b ∈ S j, G.Adj a b) :
    (G.induce (⋃ i, S i)).Connected := by
  let U := ⋃ i, S i
  have hlocal (i) {x y : V} (hx : x ∈ S i) (hy : y ∈ S i) :
      (G.induce U).Reachable ⟨x,Set.mem_iUnion.mpr ⟨i,hx⟩⟩
        ⟨y,Set.mem_iUnion.mpr ⟨i,hy⟩⟩ := by
    let f : G.induce (S i) →g G.induce U :=
      ⟨fun z => ⟨z,Set.mem_iUnion.mpr ⟨i,z.property⟩⟩,fun h => h⟩
    exact ((hS i).preconnected ⟨x,hx⟩ ⟨y,hy⟩).map f
  have hroute {i j : I} (p : H.Walk i j) :
      ∀ (x y : V) (hx : x ∈ S i) (hy : y ∈ S j),
      (G.induce U).Reachable ⟨x,Set.mem_iUnion.mpr ⟨i,hx⟩⟩
        ⟨y,Set.mem_iUnion.mpr ⟨j,hy⟩⟩ := by
    induction p with
    | nil => intro x y hx hy; exact hlocal _ hx hy
    | @cons i j k hij p ih =>
      intro x y hx hy
      obtain ⟨a,ha,b,hb,hab⟩ := he hij
      have hab' : (G.induce U).Adj ⟨a,Set.mem_iUnion.mpr ⟨i,ha⟩⟩
          ⟨b,Set.mem_iUnion.mpr ⟨j,hb⟩⟩ := hab
      exact (hlocal i hx ha).trans (hab'.reachable.trans (ih b y hb hy))
  obtain ⟨i⟩ := hH.nonempty
  obtain ⟨x⟩ := (hS i).nonempty
  have : Nonempty ↥U := ⟨⟨x,Set.mem_iUnion.mpr ⟨i,x.property⟩⟩⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp x.property
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp y.property
  obtain ⟨p⟩ := hH.preconnected i j
  exact hroute p x y hi hj

/-- Composition of the exact branch-set minor models used by Lax68. -/
noncomputable def MinorModel.comp {U V W : Type*}
    {K : SimpleGraph U} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : MinorModel K H) (N : MinorModel H G) : MinorModel K G where
  branchSet a := ⋃ b : M.branchSet a, N.branchSet b
  connected a := connected_union_along (M.connected a) (fun b => N.branchSet b)
    (fun b => N.connected b) (fun h => N.adjacent h)
  disjoint := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hx hy
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
    have hij : i.val ≠ j.val := fun he =>
      Set.disjoint_left.mp (M.disjoint hab) i.property (he ▸ j.property)
    exact Set.disjoint_left.mp (N.disjoint hij) hi hj
  adjacent := by
    intro a b hab
    obtain ⟨i,hi,j,hj,hij⟩ := M.adjacent hab
    obtain ⟨x,hx,y,hy,hxy⟩ := N.adjacent hij
    exact ⟨x,Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hx⟩,
      y,Set.mem_iUnion.mpr ⟨⟨j,hj⟩,hy⟩,hxy⟩

end Lax303502Proofs
