import Lax303502Proofs.GraphQuotients
import Lax303502Proofs.KuratowskiObstructions

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.GraphMinors

/-- Identify `y` with `x`, keeping the other vertex labels. -/
def contractMap {V : Type*} [DecidableEq V] {x y : V} (h : x ≠ y) : V → {v : V // v ≠ y} :=
  fun v => if hv : v = y then ⟨x,h⟩ else ⟨v,hv⟩

@[simp] theorem contractMap_self {V : Type*} [DecidableEq V] {x y : V}
    (h : x ≠ y) (v : {v : V // v ≠ y}) : contractMap h v = v := by
  simp [contractMap,v.property]

@[simp] theorem contractMap_right {V : Type*} [DecidableEq V] {x y : V}
    (h : x ≠ y) : contractMap h y = ⟨x,h⟩ := by simp [contractMap]

theorem contractMap_surjective {V : Type*} [DecidableEq V] {x y : V} (h : x ≠ y) :
    Function.Surjective (contractMap h) := fun v => ⟨v,contractMap_self h v⟩

theorem contractMap_eq_iff {V : Type*} [DecidableEq V] {x y : V} (h : x ≠ y)
    (u : V) (v : {v : V // v ≠ y}) :
    contractMap h u = v ↔ u = v.val ∨ u = y ∧ v.val = x := by
  by_cases hu : u = y
  · subst u
    simp [contractMap,Subtype.ext_iff,Ne.symm v.property,eq_comm]
  · simp [contractMap,hu,Subtype.ext_iff]

/-- The simple graph obtained by contracting one edge, with loops suppressed. -/
def edgeContract {V : Type*} [DecidableEq V] (G : SimpleGraph V) {x y : V}
    (h : x ≠ y) : SimpleGraph {v : V // v ≠ y} := G.map (contractMap h)

/-- The fibers of an edge contraction are its branch sets. -/
noncomputable def edgeContract_minor {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hxy : G.Adj x y) : MinorModel (edgeContract G hxy.ne) G where
  branchSet v := {u | contractMap hxy.ne u = v}
  connected v := by
    by_cases hv : v.val = x
    · have hs : {u | contractMap hxy.ne u = v} = ({x,y} : Set V) := by
        ext u
        simp [contractMap_eq_iff,hv]
      rw [hs]
      exact induce_pair_connected_of_adj hxy
    · have hs : {u | contractMap hxy.ne u = v} = ({v.val} : Set V) := by
        ext u
        simp [contractMap_eq_iff,hv]
      rw [hs]
      simp
  disjoint := by
    intro a b hab
    rw [Set.disjoint_left]
    intro u hua hub
    exact hab (hua.symm.trans hub)
  adjacent := by
    intro a b hab
    obtain ⟨_,u,v,huv,hu,hv⟩ := hab
    exact ⟨u,hu,v,hv,huv⟩

/-- The robust-edge criterion preserves connectivity after every deletion of
at most two vertices in the contracted graph. -/
theorem threeRobust_edgeContract {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hxy : x ≠ y) (hrob : ThreeRobust G)
    (he : ∀ z, (G.induce ({x,y,z} : Set V)ᶜ).Preconnected) :
    ThreeRobust (edgeContract G hxy) := by
  classical
  let q := contractMap hxy
  let r : {v : V // v ≠ y} := ⟨x,hxy⟩
  intro S hS
  have transfer {A : Set V} (hA : (G.induce A).Preconnected)
      (hpre : q ⁻¹' (S : Set {v : V // v ≠ y})ᶜ = A) :
      ((edgeContract G hxy).induce (S : Set {v : V // v ≠ y})ᶜ).Preconnected := by
    apply preconnected_map_set q hA
    rw [← hpre]
    exact Set.image_preimage_eq _ (contractMap_surjective hxy)
  by_cases hr : r ∈ S
  · have herase : (S.erase r).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hr]
      omega
    by_cases hzero : S.erase r = ∅
    · have hEq : S = {r} := by
        rw [← Finset.insert_erase hr,hzero]
        rfl
      apply transfer (he x)
      ext u
      simp [q,hEq,contractMap_eq_iff,r,and_comm]
    · have hone : (S.erase r).card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
        omega
      obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hone
      have hEq : S = {r,z} := by
        rw [← Finset.insert_erase hr,hz]
      apply transfer (he z.val)
      ext u
      simp [q,hEq,contractMap_eq_iff,r]
      tauto
  · let S' : Finset V := S.image Subtype.val
    have hS' : S'.card ≤ 2 := (Finset.card_image_le).trans hS
    apply transfer (hrob S' hS')
    ext u
    simp only [Set.mem_preimage,Set.mem_compl_iff,Finset.mem_coe,not_iff_not]
    constructor
    · intro hu
      have huy : u ≠ y := by
        intro h
        subst u
        exact hr (by simpa [q,r] using hu)
      exact Finset.mem_image.mpr ⟨q u,hu,by simp [q,contractMap,huy]⟩
    · intro hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      simpa [q] using hv

/-- Excluding the two Kuratowski minors survives an edge contraction. -/
theorem excludedMinors_edgeContract {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hxy : G.Adj x y) (hG : Lax68.Planar.IsPlanarByExcludedMinors G) :
    Lax68.Planar.IsPlanarByExcludedMinors (edgeContract G hxy.ne) := by
  constructor
  · rintro ⟨M⟩
    exact hG.1 ⟨MinorModel.comp M (edgeContract_minor hxy)⟩
  · rintro ⟨M⟩
    exact hG.2 ⟨MinorModel.comp M (edgeContract_minor hxy)⟩

/-- The subdivision-free formulation follows from the unconditional bridge. -/
theorem kuratowskiFree_edgeContract {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hxy : G.Adj x y) (hG : Lax68.GraphTopologicalMinors.IsKuratowskiFree G) :
    Lax68.GraphTopologicalMinors.IsKuratowskiFree (edgeContract G hxy.ne) :=
  excludedMinors_iff_kuratowskiFree.mp
    (excludedMinors_edgeContract hxy (excludedMinors_iff_kuratowskiFree.mpr hG))

end Lax303502Proofs
