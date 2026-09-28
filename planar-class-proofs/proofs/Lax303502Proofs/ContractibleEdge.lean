import Lax303502Proofs.CutComponents

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph

/-- Diestel, Lemma 3.2.4: the minimal-component argument. There is an edge
whose ends, together with any one further vertex, do not disconnect the
remaining graph. The contraction construction below turns this into the
usual statement about a three-connected contraction. -/
theorem exists_robust_edge {V : Type*} [Finite V] {G : SimpleGraph V}
    (hrob : ThreeRobust G) (hedge : ∃ x y, G.Adj x y) :
    ∃ x y, G.Adj x y ∧ ∀ z, (G.induce ({x,y,z} : Set V)ᶜ).Preconnected := by
  classical
  by_contra hn
  push Not at hn
  let P (n : ℕ) := ∃ x y z C, G.Adj x y ∧
    CutComponent G ({x,y,z} : Set V) C ∧ C.ncard = n
  have hP : ∃ n, P n := by
    obtain ⟨x,y,hxy⟩ := hedge
    obtain ⟨z,hz⟩ := hn x y hxy
    obtain ⟨C,hC⟩ := exists_cutComponent hz
    exact ⟨C.ncard,x,y,z,C,hxy,hC,rfl⟩
  obtain ⟨x,y,z,C,hxy,hC,hCn⟩ := Nat.find_spec hP
  have hcard (a b c : V) : ({a,b,c} : Finset V).card ≤ 3 := by
    have := Finset.card_insert_le a ({b,c} : Finset V)
    have := Finset.card_insert_le b ({c} : Finset V)
    simp only [Finset.card_singleton] at *
    omega
  obtain ⟨v,hv,hzv⟩ := hC.attachment hrob {x,y,z} (by simp) (hcard x y z) (t:=z) (by simp)
  obtain ⟨w,hw⟩ := hn z v hzv
  obtain ⟨D,hD,hxD,hyD⟩ := cutComponent_avoiding_edge hw hxy
  have hzD : z ∉ D := fun hz => hD.subset_compl hz (by simp)
  have hvD : v ∉ D := fun hv => hD.subset_compl hv (by simp)
  have hDT : Disjoint D ({x,y,z} : Set V) := by
    rw [Set.disjoint_left]
    intro a ha hat
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hat
    rcases hat with rfl | rfl | rfl
    exacts [hxD ha,hyD ha,hzD ha]
  obtain ⟨u,huD,hvu⟩ := hD.attachment hrob {z,v,w} (by simp) (hcard z v w) (t:=v) (by simp)
  have huC := hC.mem_of_adj hv (fun huT => Set.disjoint_left.mp hDT huD huT) hvu
  have hDC : D ⊆ C := hC.contains_connected hD.connected.preconnected hDT ⟨u,huC,huD⟩
  have hlt : D.ncard < C.ncard := Set.ncard_lt_ncard
    (Set.ssubset_iff_subset_ne.mpr ⟨hDC,fun he => hvD (he ▸ hv)⟩) (Set.toFinite C)
  have hmin := Nat.find_min' hP (show P D.ncard from ⟨z,v,w,D,hzv,hD,rfl⟩)
  omega

end Lax303502Proofs
