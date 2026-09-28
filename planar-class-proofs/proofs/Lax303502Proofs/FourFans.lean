import Lax303502Proofs.PathFans

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph

theorem connected_rooted_union {V I : Type*} [Nonempty I] {G : SimpleGraph V}
    (S : I → Set V) (c : V) (hc : ∀ i, c ∈ S i) (hs : ∀ i, (G.induce (S i)).Connected) :
    (G.induce (⋃ i, S i)).Connected := by
  classical
  have hcU : c ∈ ⋃ i, S i := Set.mem_iUnion.mpr ⟨Classical.arbitrary I,hc _⟩
  have hreach (x : ↥(⋃ i, S i)) : (G.induce (⋃ i, S i)).Reachable ⟨c,hcU⟩ x := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp x.property
    obtain ⟨p⟩ := (hs i) ⟨c,hc i⟩ ⟨x,hi⟩
    let f : G.induce (S i) →g G.induce (⋃ i, S i) :=
      ⟨fun z => ⟨z,Set.mem_iUnion.mpr ⟨i,z.property⟩⟩,fun h => h⟩
    exact ⟨p.map f⟩
  have : Nonempty ↥(⋃ i, S i) := ⟨⟨c,hcU⟩⟩
  exact ⟨fun x y => (hreach x).symm.trans (hreach y)⟩

theorem path_end_not_dropLast {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) (hne : a ≠ b) : b ∉ p.dropLast.support := by
  have hn : ¬p.Nil := Walk.not_nil_of_ne hne
  have hh := hp.support_nodup
  rw [← p.support_dropLast_concat hn,List.nodup_append'] at hh
  intro hb
  exact hh.2.2 hb (by simp)

/-- The alternative to a four-arm fan: two connected disjoint sets joined
by an edge, with two of the terminals in each set. -/
structure FourSplit {V : Type*} (G : SimpleGraph V) (t : Fin 4 → V) where
  index : Fin 3
  left : Set V
  right : Set V
  left_connected : (G.induce left).Connected
  right_connected : (G.induce right).Connected
  disjoint : Disjoint left right
  adjacent : ∃ x ∈ left, ∃ y ∈ right, G.Adj x y
  left_terminal : ∀ i : Fin 3, i ≠ index → t i.castSucc ∈ left
  right_terminal : t index.castSucc ∈ right
  last_terminal : t 3 ∈ right

/-- Diestel's four-terminal tree alternative, constructed with paths: attach
one terminal to a tripod at its first point of contact. -/
theorem connected_four_fan_or_split {V : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (t : Fin 4 → V) :
    Nonempty (PathFan G t) ∨ Nonempty (FourSplit G t) := by
  classical
  obtain ⟨F⟩ := connected_three_fan hG (fun i => t i.castSucc)
  let U : Set V := ⋃ i, {x | x ∈ (F.arm i).support}
  have hcU : F.center ∈ U := Set.mem_iUnion.mpr ⟨0,(F.arm 0).start_mem_support⟩
  obtain ⟨w,hw,q,hq,hqU⟩ := connected_path_to_set hG (t 3) ⟨F.center,hcU⟩
  by_cases hwc : w = F.center
  · subst w
    left
    let arm : ∀ i : Fin 4, G.Walk F.center (t i) := Fin.lastCases q.reverse F.arm
    refine ⟨⟨F.center,arm,?_,?_⟩⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hq.reverse
      · simpa only [arm,Fin.lastCases_castSucc] using F.isPath j
    · intro i j hij x hx hx'
      have hnew {j : Fin 3} (hx : x ∈ q.reverse.support) (hx' : x ∈ (F.arm j).support) : x = F.center := by
        simp only [Walk.support_reverse,List.mem_reverse] at hx
        exact hqU x hx (Set.mem_iUnion.mpr ⟨j,hx'⟩)
      revert hij hx hx'
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact (hij rfl).elim
      · intro _ hx hx'; apply hnew hx; simpa only [arm,Fin.lastCases_castSucc] using hx'
      · intro _ hx hx'; apply hnew hx'; simpa only [arm,Fin.lastCases_castSucc] using hx
      · intro hij hx hx'
        simp only [arm,Fin.lastCases_castSucc] at hx hx'
        exact F.meet (fun he => hij (congrArg Fin.castSucc he)) x hx hx'
  · right
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hw
    let p := (F.arm k).takeUntil w hk
    let r := (F.arm k).dropUntil w hk
    have hp : p.IsPath := (F.isPath k).takeUntil hk
    have hpn : ¬p.Nil := Walk.not_nil_of_ne (Ne.symm hwc)
    have hwP : w ∉ p.dropLast.support := path_end_not_dropLast hp (Ne.symm hwc)
    have hpSub : ∀ x ∈ p.dropLast.support, x ∈ (F.arm k).support := by
      intro x hx
      apply (F.arm k).support_takeUntil_subset_support hk
      apply List.mem_of_mem_dropLast
      simpa only [Walk.support_dropLast hpn] using hx
    have hrSub : ∀ x ∈ r.support, x ∈ (F.arm k).support :=
      (F.arm k).support_dropUntil_subset_support hk
    have hcR : F.center ∉ r.support := by
      intro hx
      have he := path_split_meet (F.isPath k) hk p.start_mem_support hx
      exact hwc he.symm
    let A : Fin 3 → Set V := fun i => if i = k then {x | x ∈ p.dropLast.support} else {x | x ∈ (F.arm i).support}
    let L : Set V := ⋃ i, A i
    let R : Set V := {x | x ∈ r.support} ∪ {x | x ∈ q.support}
    have hL : (G.induce L).Connected := by
      apply connected_rooted_union A F.center
      · intro i; by_cases hi : i = k
        · simp only [A,if_pos hi]; exact p.dropLast.start_mem_support
        · simp only [A,if_neg hi]; exact (F.arm i).start_mem_support
      · intro i; by_cases hi : i = k
        · dsimp only [A]; rw [if_pos hi]; exact p.dropLast.connected_induce_support
        · dsimp only [A]; rw [if_neg hi]; exact (F.arm i).connected_induce_support
    have hR : (G.induce R).Connected := induce_union_connected r.connected_induce_support.preconnected
      q.connected_induce_support.preconnected ⟨w,r.start_mem_support,q.end_mem_support⟩
    have hdis : Disjoint L R := by
      rw [Set.disjoint_left]
      intro x hx hx'
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      by_cases hik : i = k
      · have hxP : x ∈ p.dropLast.support := by simpa only [A,if_pos hik,Set.mem_ofPred_eq] using hi
        rcases hx' with hxR | hxQ
        · have hxpre : x ∈ p.support := by
            apply List.mem_of_mem_dropLast
            simpa only [Walk.support_dropLast hpn] using hxP
          have he := path_split_meet (F.isPath k) hk hxpre hxR
          exact hwP (he ▸ hxP)
        · have he := hqU x hxQ (Set.mem_iUnion.mpr ⟨k,hpSub x hxP⟩)
          exact hwP (he ▸ hxP)
      · have hxi : x ∈ (F.arm i).support := by simpa only [A,if_neg hik,Set.mem_ofPred_eq] using hi
        rcases hx' with hxR | hxQ
        · have he := F.meet hik x hxi (hrSub x hxR)
          exact hcR (he ▸ hxR)
        · have he := hqU x hxQ (Set.mem_iUnion.mpr ⟨i,hxi⟩)
          have he' := F.meet hik w (he ▸ hxi) hk
          exact hwc he'
    refine ⟨⟨k,L,R,hL,hR,hdis,?_,?_,Or.inl r.end_mem_support,Or.inr q.start_mem_support⟩⟩
    · refine ⟨p.penultimate,Set.mem_iUnion.mpr ⟨k,?_⟩,w,Or.inl r.start_mem_support,p.adj_penultimate hpn⟩
      simp only [A,if_pos rfl]
      exact p.dropLast.end_mem_support
    · intro i hik
      apply Set.mem_iUnion.mpr
      refine ⟨i,?_⟩
      simp only [A,if_neg hik]
      exact (F.arm i).end_mem_support

end Lax303502Proofs
