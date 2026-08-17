import Lax3Proofs.RamCoverActiveMass
import Lax3Proofs.Refine.ElimCompactWalks

/-!
# The compact ordering, lifted to the active carrier

The compact engines order `Fin mm`, whereas the active cover consumes a
permutation of `Fin n`.  This file supplies the exact bridge.  Live vertices
occupy the first `mm` positions, in the compact order; dead vertices occupy
the remaining positions.  Consequently weak reachability in the masked
carrier is the image of weak reachability in the compact member graph.
-/

namespace Lax3Proofs.Refine.OrderActiveMath

open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked masked_adj)
open Lax3Proofs.RamCover (rk rk_fin rk_of_lt)
open Lax3Proofs.RamCoverActive (CentresBy)
open Lax3Proofs.RamDriverCluster (markSet mem_markSet)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.Refine.ElimCompact (memEmb memEmb_injective memGraph memGraph_adj)
open Lax3Proofs.Refine.ElimCompactWalks (memEmb_mem_markSet exists_memEmb_eq)

variable {n mm r d : ℕ} {G : SimpleGraph (Fin n)} {M Mem : ℕ → ℕ}

/-- The live carrier subtype. -/
abbrev Live (n : ℕ) (M : ℕ → ℕ) := {v : Fin n // M (v : ℕ) ≠ 0}

/-- The member embedding, with its liveness proof retained. -/
def memLive (hml : MemList n mm Mem (markSet n M)) (i : Fin mm) : Live n M :=
  ⟨memEmb hml i, mem_markSet.mp (memEmb_mem_markSet hml i)⟩

/-- The member list is an equivalence onto the live carrier subtype. -/
noncomputable def memEquiv (hml : MemList n mm Mem (markSet n M)) :
    Fin mm ≃ Live n M :=
  Equiv.ofBijective (memLive hml) ⟨
    fun _ _ h => memEmb_injective hml (congrArg Subtype.val h),
    fun v => by
      obtain ⟨i, hi⟩ := exists_memEmb_eq hml (mem_markSet.mpr v.property)
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp] theorem memEquiv_apply (hml : MemList n mm Mem (markSet n M)) (i : Fin mm) :
    memEquiv hml i = memLive hml i := rfl

/-- The compact graph is the masked graph induced on its live subtype. -/
noncomputable def memIso (hml : MemList n mm Mem (markSet n M)) :
    memGraph G M hml ≃g (masked G M).induce {v : Fin n | M (v : ℕ) ≠ 0} where
  toEquiv := memEquiv hml
  map_rel_iff' := by
    intro i k
    change (masked G M).Adj (memEmb hml i) (memEmb hml k) ↔ _
    exact memGraph_adj.symm

/-- The live-first extension of a compact ordering to the carrier. -/
noncomputable def activePerm (hml : MemList n mm Mem (markSet n M))
    (πm : Equiv.Perm (Fin mm)) : Equiv.Perm (Fin n) :=
  let p : Fin n → Prop := fun v => M (v : ℕ) ≠ 0
  let eLive : {v // p v} ≃ Fin mm := (memEquiv hml).symm.trans πm
  let eDead : {v // ¬ p v} ≃ Fin (Fintype.card {v // ¬ p v}) := Fintype.equivFin _
  let hLive : Fintype.card {v // p v} = mm := by
    simpa [p] using (Fintype.card_congr (memEquiv hml)).symm
  let hCard : mm + Fintype.card {v // ¬ p v} = n := by
    rw [Fintype.card_subtype_compl, hLive, Fintype.card_fin]
    exact Nat.add_sub_of_le hml.card_le
  (Equiv.sumCompl p).symm |>.trans (Equiv.sumCongr eLive eDead) |>.trans
    finSumFinEquiv |>.trans (finCongr hCard)

/-- On a live member, the extended carrier rank is exactly its compact rank. -/
theorem activePerm_mem (hml : MemList n mm Mem (markSet n M))
    (πm : Equiv.Perm (Fin mm)) (i : Fin mm) :
    (((activePerm hml πm) (memEmb hml i) : Fin n) : ℕ) = ((πm i : Fin mm) : ℕ) := by
  classical
  simp only [activePerm, Equiv.trans_apply]
  have hsum :
      (Equiv.sumCompl (fun v : Fin n => M (v : ℕ) ≠ 0)).symm (memEmb hml i) =
        Sum.inl (memLive hml i) := by
    simpa only [memLive] using
      (Equiv.sumCompl_symm_apply_of_pos
        (p := fun v : Fin n => M (v : ℕ) ≠ 0) (a := memEmb hml i)
        (mem_markSet.mp (memEmb_mem_markSet hml i)))
  rw [hsum]
  have hinv : (memEquiv hml).symm (memLive hml i) = i :=
    (memEquiv hml).symm_apply_apply i
  simp [hinv]

/-- The active centre array: the compact order, read back as arena vertices. -/
noncomputable def activeCentre (mm : ℕ) (Mem : ℕ → ℕ) (πm : Equiv.Perm (Fin mm))
    (k : ℕ) : ℕ :=
  if hk : k < mm then Mem (((πm.symm ⟨k, hk⟩ : Fin mm) : ℕ)) else 0

theorem activeCentre_of_lt (πm : Equiv.Perm (Fin mm)) {k : ℕ} (hk : k < mm) :
    activeCentre mm Mem πm k = Mem (((πm.symm ⟨k, hk⟩ : Fin mm) : ℕ)) := by
  simp [activeCentre, hk]

/-- The active centre array enumerates precisely the live vertices, in the
extended carrier ordering. -/
theorem centresBy_activeCentre (hml : MemList n mm Mem (markSet n M))
    (πm : Equiv.Perm (Fin mm)) :
    CentresBy n mm M (activePerm hml πm) (activeCentre mm Mem πm) := by
  classical
  refine
    { count_le := hml.card_le
      centre_lt := ?_
      alive := ?_
      rank_mono := ?_
      complete := ?_ }
  · intro k hk
    rw [activeCentre_of_lt πm hk]
    exact hml.lt _ (πm.symm ⟨k, hk⟩).isLt
  · intro k hk
    rw [activeCentre_of_lt πm hk]
    exact mem_markSet.mp (memEmb_mem_markSet hml (πm.symm ⟨k, hk⟩))
  · intro i k hik hk
    have hi : i < mm := by omega
    have hci : activeCentre mm Mem πm i < n := by
      rw [activeCentre_of_lt πm hi]
      exact hml.lt _ (πm.symm ⟨i, hi⟩).isLt
    have hck : activeCentre mm Mem πm k < n := by
      rw [activeCentre_of_lt πm hk]
      exact hml.lt _ (πm.symm ⟨k, hk⟩).isLt
    rw [rk_of_lt hci, rk_of_lt hck]
    have hei : (⟨activeCentre mm Mem πm i, hci⟩ : Fin n) =
        memEmb hml (πm.symm ⟨i, hi⟩) := by
      apply Fin.ext
      exact activeCentre_of_lt πm hi
    have hek : (⟨activeCentre mm Mem πm k, hck⟩ : Fin n) =
        memEmb hml (πm.symm ⟨k, hk⟩) := by
      apply Fin.ext
      exact activeCentre_of_lt πm hk
    rw [hei, hek, activePerm_mem, activePerm_mem]
    simpa using hik
  · intro v hv hMv
    let vf : Fin n := ⟨v, hv⟩
    obtain ⟨i, hi⟩ := exists_memEmb_eq hml (v := vf) (mem_markSet.mpr hMv)
    let k : ℕ := ((πm i : Fin mm) : ℕ)
    have hk : k < mm := (πm i).isLt
    refine ⟨k, hk, ?_⟩
    rw [activeCentre_of_lt πm hk]
    have hs : πm.symm ⟨k, hk⟩ = i := by
      apply πm.injective
      rw [πm.apply_symm_apply]
    rw [hs]
    exact congrArg Fin.val hi

/-! ## Weak reachability transport -/

/-- Every vertex on a masked walk from a live start is live. -/
theorem walk_support_live {v u : Fin n} (hv : M (v : ℕ) ≠ 0)
    (p : (masked G M).Walk v u) : ∀ y ∈ p.support, M (y : ℕ) ≠ 0 := by
  induction p with
  | nil => simpa using hv
  | @cons a b c hab p ih =>
      intro y hy
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact (masked_adj.mp hab).2.1
      · exact ih (masked_adj.mp hab).2.2 y hy

/-- A weakly reachable vertex from a live member lifts to a weakly reachable
compact vertex. -/
theorem mem_wreach_lift (hml : MemList n mm Mem (markSet n M))
    (πm : Equiv.Perm (Fin mm)) {i : Fin mm} {u : Fin n}
    (hu : u ∈ wreach (masked G M) (activePerm hml πm) r (memEmb hml i)) :
    ∃ k : Fin mm, memEmb hml k = u ∧ k ∈ wreach (memGraph G M hml) πm r i := by
  classical
  obtain ⟨p, hp, hmin⟩ := hu
  have hstart : M ((memEmb hml i : Fin n) : ℕ) ≠ 0 :=
    mem_markSet.mp (memEmb_mem_markSet hml i)
  have hlive := walk_support_live hstart p
  have huLive : M (u : ℕ) ≠ 0 := hlive u p.end_mem_support
  let q0 := p.induce {v : Fin n | M (v : ℕ) ≠ 0} hlive
  let q1 := q0.map (memIso (G := G) hml).symm.toHom
  have hi0 : (memIso (G := G) hml).symm ⟨memEmb hml i, hstart⟩ = i := by
    exact (memIso (G := G) hml).symm_apply_apply i
  let k : Fin mm := (memIso (G := G) hml).symm ⟨u, huLive⟩
  have hku : memEmb hml k = u := by
    have h := (memIso (G := G) hml).apply_symm_apply ⟨u, huLive⟩
    exact congrArg Subtype.val h
  let q : (memGraph G M hml).Walk i k := q1.copy hi0 (by rfl)
  refine ⟨k, hku, ⟨q, ?_, ?_⟩⟩
  · have hq0 : q0.length = p.length := by
      have hplus : q0.length + 1 = p.length + 1 := by
        calc
          q0.length + 1 = q0.support.length := q0.length_support.symm
          _ = p.support.length := by simp only [q0, SimpleGraph.Walk.support_induce,
            List.length_attachWith]
          _ = p.length + 1 := p.length_support
      omega
    simpa only [q, SimpleGraph.Walk.length_copy, q1, SimpleGraph.Walk.length_map,
      hq0] using hp
  · intro z hz
    have hzMap : memEmb hml z ∈ p.support := by
      have hz' : z ∈ q1.support := by simpa [q] using hz
      simp only [q1, SimpleGraph.Walk.support_map, List.mem_map] at hz'
      obtain ⟨y, hy, hyz⟩ := hz'
      have hyP : (y : Fin n) ∈ p.support := by
        simpa only [q0, SimpleGraph.Walk.support_induce, List.mem_attachWith] using hy
      have heq : memEmb hml z = (y : Fin n) := by
        rw [← hyz]
        exact congrArg Subtype.val ((memIso (G := G) hml).apply_symm_apply y)
      rwa [heq]
    have h := hmin (memEmb hml z) hzMap
    have hleft : (((activePerm hml πm) u : Fin n) : ℕ) = ((πm k : Fin mm) : ℕ) := by
      rw [← hku, activePerm_mem]
    have hright :
        (((activePerm hml πm) (memEmb hml z) : Fin n) : ℕ) = ((πm z : Fin mm) : ℕ) :=
      activePerm_mem hml πm z
    have hval : (((activePerm hml πm) u : Fin n) : ℕ) ≤
        (((activePerm hml πm) (memEmb hml z) : Fin n) : ℕ) := h
    rw [hleft, hright] at hval
    exact_mod_cast hval

/-- At a live start, carrier weak reachability injects into compact weak
reachability. -/
theorem wreach_ncard_le_compact (hml : MemList n mm Mem (markSet n M))
    (πm : Equiv.Perm (Fin mm)) (i : Fin mm) :
    (wreach (masked G M) (activePerm hml πm) r (memEmb hml i)).ncard ≤
      (wreach (memGraph G M hml) πm r i).ncard := by
  classical
  have hsub :
      wreach (masked G M) (activePerm hml πm) r (memEmb hml i) ⊆
        memEmb hml '' wreach (memGraph G M hml) πm r i := by
    intro u hu
    obtain ⟨k, hku, hk⟩ := mem_wreach_lift hml πm hu
    exact ⟨k, hk, hku⟩
  calc
    (wreach (masked G M) (activePerm hml πm) r (memEmb hml i)).ncard ≤
        (memEmb hml '' wreach (memGraph G M hml) πm r i).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (wreach (memGraph G M hml) πm r i).ncard :=
      Set.ncard_image_of_injective _ (memEmb_injective hml)

/-- A dead vertex is the only vertex weakly reachable from itself in the
masked graph. -/
theorem wreach_dead {π : Equiv.Perm (Fin n)} {v : Fin n} (hv : M (v : ℕ) = 0) :
    wreach (masked G M) π r v = {v} := by
  ext u
  constructor
  · rintro ⟨p, -, -⟩
    cases p with
    | nil => simp
    | @cons a b c hab p => exact False.elim ((masked_adj.mp hab).2.1 hv)
  · intro hu
    have huv : u = v := by simpa [Set.mem_singleton_iff] using hu
    subst u
    exact Lax3Proofs.RamCover.self_mem_wreach (masked G M) π r v

/-- A compact weak-reachability bound lifts to the active carrier.  The
`1 ≤ d` side is necessary only for dead vertices, whose masked component is
the singleton. -/
theorem active_degree_of_compact (hml : MemList n mm Mem (markSet n M))
    (πm : Equiv.Perm (Fin mm)) (hd : 1 ≤ d)
    (hcompact : ∀ i : Fin mm, (wreach (memGraph G M hml) πm r i).ncard ≤ d) :
    ∀ v : Fin n, (wreach (masked G M) (activePerm hml πm) r v).ncard ≤ d := by
  intro v
  by_cases hv : M (v : ℕ) = 0
  · rw [wreach_dead hv, Set.ncard_singleton]
    exact hd
  · obtain ⟨i, hi⟩ := exists_memEmb_eq hml (mem_markSet.mpr hv)
    subst v
    exact (wreach_ncard_le_compact hml πm i).trans (hcompact i)

#print axioms centresBy_activeCentre
#print axioms active_degree_of_compact

end Lax3Proofs.Refine.OrderActiveMath
