import Lax303502Proofs.OuterConnectivity
import Lax303502Proofs.CycleDrawing

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph

theorem cycle_index_injective {V : Type*} {G : SimpleGraph V} {a : V}
    {p : G.Walk a a} (hp : p.IsCycle) : Set.InjOn p.getVert (Set.Iio p.length) := by
  intro i hi j hj he
  exact hp.getVert_injOn' (by change i ≤ p.length-1; exact Nat.le_sub_one_of_lt hi)
    (by change j ≤ p.length-1; exact Nat.le_sub_one_of_lt hj) he

theorem cycle_index_of_mem {V : Type*} {G : SimpleGraph V} {a v : V}
    {p : G.Walk a a} (hp : p.IsCycle) (hv : v ∈ p.support) :
    ∃ i < p.length, p.getVert i = v := by
  obtain ⟨i,hi,hin⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  by_cases he : i = p.length
  · exact ⟨0,by have := hp.three_le_length; omega,by simpa [he] using hi⟩
  · exact ⟨i,by omega,hi⟩

theorem cycle_extend_edge {V : Type*} {G : SimpleGraph V} {a : V}
    {p : G.Walk a a} (hp : p.IsCycle) {T : Set V}
    (hT : (G.induce T).Connected) (hdis : Disjoint T {v | v ∈ p.support})
    (ea : ∃ x ∈ T, G.Adj a x) (eb : ∃ y ∈ T, G.Adj p.snd y) :
    ∃ q : G.Walk a a, q.IsCycle ∧ p.length < q.length := by
  have hna : a ∉ T := fun h => Set.disjoint_left.mp hdis h p.start_mem_support
  have hnb : p.snd ∉ T := fun h => Set.disjoint_left.mp hdis h (p.getVert_mem_support 1)
  obtain ⟨q,hq,hql,hqT⟩ := outside_path hT (p.adj_snd hp.not_nil).ne hna hnb ea eb
  have htail : p.snd ∉ p.tail.support.tail := by
    have hh := hp.isPath_tail.support_nodup
    rw [← p.tail.cons_tail_support, List.nodup_cons] at hh
    exact hh.1
  have hsub : ∀ v ∈ p.tail.support, v ∈ p.support := by
    intro v hv
    rw [p.support_tail_of_not_nil hp.not_nil] at hv
    exact List.mem_of_mem_tail hv
  have hc : (q.append p.tail).IsCycle := hq.isCycle_append hp.isPath_tail (by
    intro v hv hv'
    rcases hqT v hv with he | ht
    · exact htail (he ▸ hv')
    · exact Set.disjoint_left.mp hdis ht (hsub v (List.mem_of_mem_tail hv')))
    (Or.inl (by omega))
  refine ⟨q.append p.tail,hc,?_⟩
  simp only [Walk.length_append]
  have := p.length_tail_add_one hp.not_nil
  omega

theorem exists_longest_cycle {V : Type*} [Finite V] {G : SimpleGraph V}
    (hcycle : ∃ a, ∃ p : G.Walk a a, p.IsCycle) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧
      ∀ b, ∀ q : G.Walk b b, q.IsCycle → q.length ≤ p.length := by
  classical
  let := Fintype.ofFinite G.edgeSet
  let S := {n | ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = n}
  have hs : S.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    (fun n ⟨a,p,hp,he⟩ => he ▸ hp.isTrail.length_le_card_edgeFinset)
  obtain ⟨a,p,hp⟩ := hcycle
  obtain ⟨_,⟨⟨b,q,hq,_⟩,hm⟩⟩ := hs.exists_maximal ⟨p.length,a,p,hp,rfl⟩
  refine ⟨b,q,hq,fun c r hr => ?_⟩
  have := hm ⟨c,r,hr,rfl⟩
  omega


/-- In a graph without a cut vertex or a `K₂,₃` minor, every longest cycle
contains all vertices. The outside component either extends an edge of the
cycle or supplies the third branch of a forbidden minor. -/
theorem longest_cycle_spanning {V : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (hdel : ∀ v, (G.induce {v}ᶜ).Preconnected)
    (hK : ¬Lax68.GraphMinors.IsMinor Lax68.GraphMinors.K23 G)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    (hmax : ∀ b, ∀ q : G.Walk b b, q.IsCycle → q.length ≤ p.length) :
    ∀ x, x ∈ p.support := by
  classical
  intro x
  by_contra hx
  have hC : ({w | w ∈ p.support} : Set V).Nontrivial :=
    ⟨v,p.start_mem_support,p.snd,p.getVert_mem_support 1,(p.adj_snd hp.not_nil).ne⟩
  obtain ⟨T,hT,hdis,a,ha,b,hb,hab,ea,eb⟩ :=
    outside_two_attachments hG hdel {w | w ∈ p.support} hC hx
  let q := p.rotate a ha
  have hq : q.IsCycle := hp.rotate ha
  have hql : q.length = p.length := p.length_rotate a ha
  have hdisq : Disjoint T {w | w ∈ q.support} := by
    simpa only [q,Walk.mem_support_rotate_iff] using hdis
  have hbq : b ∈ q.support := by simpa only [q,Walk.mem_support_rotate_iff,Set.mem_ofPred_eq] using hb
  obtain ⟨j,hjn,hj⟩ := cycle_index_of_mem hq hbq
  have hj0 : j ≠ 0 := by
    intro he
    apply hab
    simpa [he] using hj
  by_cases hj1 : j = 1
  · have eb' : ∃ y ∈ T, G.Adj q.snd y := by
      have he : q.snd = b := by simpa only [hj1] using hj
      exact he ▸ eb
    obtain ⟨r,hr,hl⟩ := cycle_extend_edge hq hT hdisq ea eb'
    have := hmax a r hr
    omega
  by_cases hjlast : j = q.length-1
  · have he : q.reverse.snd = b := by
      rw [Walk.snd_reverse]
      change q.getVert (q.length-1) = b
      simpa only [hjlast] using hj
    have eb' : ∃ y ∈ T, G.Adj q.reverse.snd y := he ▸ eb
    have hdrev : Disjoint T {w | w ∈ q.reverse.support} := by simpa using hdisq
    obtain ⟨r,hr,hl⟩ := cycle_extend_edge hq.reverse hT hdrev ea eb'
    have := hmax a r hr
    simp only [Walk.length_reverse] at hl
    omega
  apply hK
  refine ⟨cycle_theta_minor q.getVert (n:=q.length) (j:=j) (cycle_index_injective hq)
    (fun i hi => q.adj_getVert_succ hi) (by simp) (by omega) (by omega) T hT ?_ ?_ ?_⟩
  · intro i _ hi
    exact Set.disjoint_left.mp hdisq hi (q.getVert_mem_support i)
  · simpa only [Walk.getVert_zero] using ea
  · simpa only [hj] using eb

end Lax303502Proofs
