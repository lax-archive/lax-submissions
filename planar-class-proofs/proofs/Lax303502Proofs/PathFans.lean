import Lax303502Proofs.OuterConnectivity
import Lax68.GraphTopologicalMinors

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph

/-- A family of paths with a common start and no other intersections. -/
structure PathFan {V I : Type*} (G : SimpleGraph V) (terminal : I → V) where
  center : V
  arm : ∀ i, G.Walk center (terminal i)
  isPath : ∀ i, (arm i).IsPath
  meet : ∀ {i j}, i ≠ j → ∀ x, x ∈ (arm i).support → x ∈ (arm j).support → x = center

theorem path_append_of_meet {V : Type*} {G : SimpleGraph V} {a b c : V}
    {p : G.Walk a b} {q : G.Walk b c} (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ x, x ∈ p.support → x ∈ q.support → x = b) : (p.append q).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append,List.nodup_append']
  refine ⟨hp.support_nodup,hq.support_nodup.tail,?_⟩
  intro x hx hx'
  have he := hmeet x hx (List.mem_of_mem_tail hx')
  have hb : b ∉ q.support.tail := by
    have hh := hq.support_nodup
    rw [← q.cons_tail_support,List.nodup_cons] at hh
    exact hh.1
  exact hb (he ▸ hx')

theorem path_split_meet {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {a b c : V} {p : G.Walk a b} (hp : p.IsPath) (hc : c ∈ p.support)
    {x : V} (hx : x ∈ (p.takeUntil c hc).support) (hx' : x ∈ (p.dropUntil c hc).support) :
    x = c := by
  by_contra hne
  have hpath : ((p.takeUntil c hc).append (p.dropUntil c hc)).IsPath := by simpa using hp
  exact hpath.ne_of_mem_support_of_append hne hx hx' rfl

/-- Stop at the first visit to a nonempty set. A shortest path to the set
cannot visit it anywhere before its endpoint. -/
theorem connected_path_to_set {V : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (a : V) {S : Set V} (hS : S.Nonempty) :
    ∃ b ∈ S, ∃ p : G.Walk a b, p.IsPath ∧ ∀ x ∈ p.support, x ∈ S → x = b := by
  classical
  have hex : ∃ n, ∃ b ∈ S, ∃ p : G.Walk a b, p.IsPath ∧ p.length = n := by
    obtain ⟨b,hb⟩ := hS
    obtain ⟨p,hp⟩ := hG.exists_isPath a b
    exact ⟨p.length,b,hb,p,hp,rfl⟩
  obtain ⟨b,hb,p,hp,hl⟩ := Nat.find_spec hex
  refine ⟨b,hb,p,hp,?_⟩
  intro x hx hxS
  by_contra hxb
  have hmin := Nat.find_min' hex ⟨x,hxS,p.takeUntil x hx,hp.takeUntil hx,rfl⟩
  have hlt := Walk.length_takeUntil_lt_length hx hxb
  omega

/-- Three terminals of a connected graph have a tripod of paths, allowing
zero-length arms when terminals coincide with its center. -/
theorem connected_three_fan {V : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (t : Fin 3 → V) : Nonempty (PathFan G t) := by
  classical
  obtain ⟨p,hp⟩ := hG.exists_isPath (t 1) (t 2)
  obtain ⟨c,hc,q,hq,hmeet⟩ := connected_path_to_set hG (t 0)
    (S:={x | x ∈ p.support}) ⟨t 1,p.start_mem_support⟩
  let arm : ∀ i : Fin 3, G.Walk c (t i) :=
    Fin.cases q.reverse (Fin.cases (p.takeUntil c hc).reverse
      (Fin.cases (p.dropUntil c hc) (fun i => Fin.elim0 i)))
  have ha0 : arm 0 = q.reverse := rfl
  have ha1 : arm 1 = (p.takeUntil c hc).reverse := rfl
  have ha2 : arm 2 = p.dropUntil c hc := rfl
  refine ⟨⟨c,arm,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact hq.reverse
    · exact (hp.takeUntil hc).reverse
    · exact hp.dropUntil hc
  · intro i j hij x hx hx'
    have h01 (hx : x ∈ (arm 0).support) (hx' : x ∈ (arm 1).support) : x = c := by
      rw [ha0,Walk.support_reverse,List.mem_reverse] at hx
      rw [ha1,Walk.support_reverse,List.mem_reverse] at hx'
      exact hmeet x hx (p.support_takeUntil_subset_support hc hx')
    have h02 (hx : x ∈ (arm 0).support) (hx' : x ∈ (arm 2).support) : x = c := by
      rw [ha0,Walk.support_reverse,List.mem_reverse] at hx
      exact hmeet x hx (p.support_dropUntil_subset_support hc hx')
    have h12 (hx : x ∈ (arm 1).support) (hx' : x ∈ (arm 2).support) : x = c := by
      rw [ha1,Walk.support_reverse,List.mem_reverse] at hx
      exact path_split_meet hp hc hx hx'
    fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | exact h01 hx hx' | exact h01 hx' hx |
        exact h02 hx hx' | exact h02 hx' hx | exact h12 hx hx' | exact h12 hx' hx


def PathFan.reindex {V I J : Type*} {G : SimpleGraph V} {t : I → V}
    (F : PathFan G t) (e : J ↪ I) : PathFan G (t ∘ e) where
  center := F.center
  arm i := F.arm (e i)
  isPath i := F.isPath (e i)
  meet hij := F.meet (e.injective.ne hij)

theorem connected_fan_three_equiv {V I : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (e : Fin 3 ≃ I) (t : I → V) : Nonempty (PathFan G t) := by
  obtain ⟨F⟩ := connected_three_fan hG (t ∘ e)
  simpa only [Function.comp_def,Equiv.apply_symm_apply] using
    (show Nonempty (PathFan G ((t ∘ e) ∘ e.symm)) from ⟨F.reindex e.symm.toEmbedding⟩)

end Lax303502Proofs
