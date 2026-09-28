import Lax303502Proofs.MinorConstructions

set_option autoImplicit false

namespace Lax303502Proofs

theorem preconnected_boundary {V : Type*} {G : SimpleGraph V} {A T : Set V}
    (hA : (G.induce A).Preconnected) {x y : V}
    (hx : x ∈ A) (hy : y ∈ A) (hxt : x ∈ T) (hyt : y ∉ T) :
    ∃ a ∈ A, ∃ b ∈ A, a ∈ T ∧ b ∉ T ∧ G.Adj a b := by
  classical
  by_contra hn
  push Not at hn
  have hc := connected_constant hA (fun v => v ∈ T) (a:=x) (b:=y) (by
    intro a ha b hb hab
    constructor
    · intro hat
      by_contra hbt
      exact hn a ha b hb hat hbt hab
    · intro hbt
      by_contra hat
      exact hn b hb a ha hbt hat hab.symm) hx hy
  exact hyt (hc.mp hxt)

/-- A component outside a specified vertex set, expressed in the original
vertex type so that it can directly serve as a minor branch set. -/
theorem outside_component {V : Type*} {G : SimpleGraph V} (C : Set V)
    {x : V} (hx : x ∉ C) : ∃ T : Set V, x ∈ T ∧ (G.induce T).Connected ∧
      Disjoint T C ∧ ∀ a ∈ T, ∀ b, b ∉ T → G.Adj a b → b ∈ C := by
  let H := G.induce Cᶜ
  let K := H.connectedComponentMk ⟨x,hx⟩
  let T : Set V := Subtype.val '' K.supp
  have hxK : (⟨x,hx⟩ : ↥(Cᶜ)) ∈ K.supp := rfl
  refine ⟨T,⟨⟨x,hx⟩,hxK,rfl⟩,?_,?_,?_⟩
  · exact connected_image (SimpleGraph.Embedding.induce Cᶜ).toHom K.connected_toSimpleGraph
  · rw [Set.disjoint_left]
    rintro y ⟨z,hz,rfl⟩ hy
    exact z.property hy
  · rintro a ⟨u,hu,rfl⟩ b hb hab
    by_contra hbc
    apply hb
    have hmem : (⟨b,hbc⟩ : ↥(Cᶜ)) ∈ K.supp := K.mem_supp_of_adj_mem_supp hu hab
    exact ⟨⟨b,hbc⟩,hmem,rfl⟩

/-- If deleting any one vertex preserves connectivity, a component outside a
nontrivial set has two distinct attachment vertices in that set. -/
theorem outside_two_attachments {V : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (hdel : ∀ v, (G.induce {v}ᶜ).Preconnected)
    (C : Set V) (hC : C.Nontrivial) {x : V} (hx : x ∉ C) :
    ∃ T : Set V, (G.induce T).Connected ∧ Disjoint T C ∧
      ∃ a ∈ C, ∃ b ∈ C, a ≠ b ∧
        (∃ u ∈ T, G.Adj a u) ∧ (∃ v ∈ T, G.Adj b v) := by
  obtain ⟨T,hxT,hT,hdis,hboundary⟩ := outside_component (G:=G) C hx
  obtain ⟨y,hy,z,hz,hyz⟩ := hC
  have hpre : (G.induce Set.univ).Preconnected := by
    intro u v
    obtain ⟨p⟩ := hG u v
    let f : G →g G.induce Set.univ := ⟨fun w => ⟨w,Set.mem_univ w⟩,fun h => h⟩
    exact ⟨p.map f⟩
  obtain ⟨u,_,a,_,hu,ha,hua⟩ := preconnected_boundary hpre (Set.mem_univ x)
    (Set.mem_univ y) hxT (fun h => Set.disjoint_left.mp hdis h hy)
  have haC := hboundary u hu a ha hua
  obtain ⟨b,hbC,hba⟩ : ∃ b ∈ C, b ≠ a := by
    by_cases he : y = a
    · exact ⟨z,hz,fun he' => hyz (he.trans he'.symm)⟩
    · exact ⟨y,hy,he⟩
  have hxne : x ≠ a := fun he => hx (he ▸ haC)
  obtain ⟨v,hva,c,hca,hv,hc,hvc⟩ := preconnected_boundary (hdel a)
    (by simpa using hxne) (by simpa using hba) hxT (fun h => Set.disjoint_left.mp hdis h hbC)
  have hcC := hboundary v hv c hc hvc
  refine ⟨T,hT,hdis,a,haC,c,hcC,?_,⟨u,hu,hua.symm⟩,⟨v,hv,hvc.symm⟩⟩
  simpa [ne_comm] using hca


/-- A path through a connected outside set, with the two attachment vertices
as its endpoints. Its interior stays in the outside set. -/
theorem outside_path {V : Type*} {G : SimpleGraph V} {T : Set V}
    (hT : (G.induce T).Connected) {a b : V} (hab : a ≠ b)
    (ha : a ∉ T) (hb : b ∉ T)
    (ea : ∃ x ∈ T, G.Adj a x) (eb : ∃ y ∈ T, G.Adj b y) :
    ∃ q : G.Walk a b, q.IsPath ∧ 2 ≤ q.length ∧
      ∀ v ∈ q.support.tail, v = b ∨ v ∈ T := by
  obtain ⟨x,hx,hax⟩ := ea
  obtain ⟨y,hy,hby⟩ := eb
  obtain ⟨p,hp⟩ := hT.exists_isPath ⟨x,hx⟩ ⟨y,hy⟩
  let f : G.induce T →g G := ⟨Subtype.val,fun h => h⟩
  let r : G.Walk x y := p.map f
  have hr : r.IsPath := hp.map Subtype.val_injective
  have hrT {v} (hv : v ∈ r.support) : v ∈ T := by
    change v ∈ (p.map f).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w,_,he⟩ := List.mem_map.mp hv
    have he : w.val = v := he
    exact he ▸ w.property
  let q : G.Walk a b := (r.concat hby.symm).cons hax
  have hq : q.IsPath := (hr.concat (fun h => hb (hrT h)) hby.symm).cons (by
    simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
    rintro (h | h)
    · exact ha (hrT h)
    · exact hab h)
  refine ⟨q,hq,?_,?_⟩
  · simp only [q, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]; omega
  · intro v hv
    change v ∈ (r.concat hby.symm).support at hv
    simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hv
    rcases hv with hv | hv
    · exact Or.inr (hrT hv)
    · exact Or.inl hv


/-- A disconnected induced graph can be split along one connected component. -/
theorem not_preconnected_partition {V : Type*} {G : SimpleGraph V} {A : Set V}
    (hA : ¬(G.induce A).Preconnected) : ∃ U : Set V, U ⊆ A ∧ U.Nonempty ∧
      (A \ U).Nonempty ∧ ∀ a ∈ U, ∀ b ∈ A, G.Adj a b → b ∈ U := by
  classical
  change ¬∀ x y : A, (G.induce A).Reachable x y at hA
  push Not at hA
  obtain ⟨x,y,hxy⟩ := hA
  let H := G.induce A
  let C := H.connectedComponentMk x
  let U : Set V := Subtype.val '' C.supp
  have hxC : x ∈ C.supp := rfl
  have hxU : x.val ∈ U := ⟨x,hxC,rfl⟩
  have hyU : y.val ∉ U := by
    rintro ⟨z,hz,he⟩
    have he : z = y := Subtype.ext he
    exact hxy (C.reachable_of_mem_supp hxC (he ▸ hz))
  refine ⟨U,?_,⟨x,hxU⟩,⟨y,y.property,hyU⟩,?_⟩
  · rintro a ⟨z,hz,rfl⟩; exact z.property
  · rintro a ⟨z,hz,rfl⟩ b hb hab
    exact ⟨⟨b,hb⟩,C.mem_supp_of_adj_mem_supp hz hab,rfl⟩

end Lax303502Proofs
