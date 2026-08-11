import Lax3Proofs.RamCoverMember
import Lax3Proofs.Refine.MassAlive

/-!
# Active-centre cover invariant

The carrier cover processes every ordering position.  A nested arena may
process only its live centres.  This file supplies the corresponding
mathematical invariant: `centre[0..q)` enumerates the live vertices in
increasing ordering rank, the mask deletes precisely the prefix already
processed, and the assignment stores an index into that active prefix.

The executable cover phase only has to realize the step hypotheses below.
No carrier-wide initialization or dead assignment cell occurs in the
contract.
-/

namespace Lax3Proofs.RamCoverActive

open Lax3.ColoredGraphs
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover
open Lax12.UniformQuasiWideness (deleteVerts)

variable {n : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ M centre Xoff Xmem asg : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)} {q r c xp : ℕ}

/-! ## The active ordering -/

/-- The live vertices, in increasing position in `π`. -/
structure CentresBy (n q : ℕ) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre : ℕ → ℕ) : Prop where
  count_le : q ≤ n
  centre_lt : ∀ k < q, centre k < n
  alive : ∀ k < q, A₀ (centre k) ≠ 0
  rank_mono : ∀ i j, i < j → j < q → rk n π (centre i) < rk n π (centre j)
  complete : ∀ v < n, A₀ v ≠ 0 → ∃ k < q, centre k = v

namespace CentresBy

/-- Active indices name distinct vertices. -/
theorem injective (h : CentresBy n q A₀ π centre) {i j : ℕ}
    (hi : i < q) (hj : j < q) (heq : centre i = centre j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have := h.rank_mono i j hij hj
    rw [heq] at this
    omega
  · exact hij
  · have := h.rank_mono j i hij hi
    rw [heq] at this
    omega

/-- Rank is monotone for non-strict active-index comparison. -/
theorem rank_le (h : CentresBy n q A₀ π centre) {i j : ℕ}
    (_hi : i < q) (hj : j < q) (hij : i ≤ j) :
    rk n π (centre i) ≤ rk n π (centre j) := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  · exact (h.rank_mono i j hij hj).le

/-- Below a live centre, the processed active prefix is exactly its ordering
predecessors.  Dead predecessors are already absent from the ambient mask. -/
theorem processed_iff_rank_lt (h : CentresBy n q A₀ π centre)
    {k u : ℕ} (hk : k < q) (hu : u < n) (halive : A₀ u ≠ 0) :
    (∃ i < k, centre i = u) ↔ rk n π u < rk n π (centre k) := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact h.rank_mono i k hi hk
  · intro hr
    obtain ⟨i, hi, hic⟩ := h.complete u hu halive
    rcases lt_trichotomy i k with hik | hik | hik
    · exact ⟨i, hik, hic⟩
    · subst i
      rw [hic] at hr
      omega
    · have hm := h.rank_mono k i hik hi
      rw [hic] at hm
      omega

end CentresBy

/-! ## The active mask seam -/

/-- At an active turn, deleting the previously processed live centres is the
same graph as deleting every ordering predecessor of the current centre. -/
theorem masked_step (hcentres : CentresBy n q A₀ π centre) (hc : c < q)
    (hmask : ∀ u < n, M u = 0 ↔ (A₀ u = 0 ∨ ∃ i < c, centre i = u)) :
    masked G M = deleteVerts (masked G A₀) (pred π ⟨centre c, hcentres.centre_lt c hc⟩) := by
  rw [RamBfs.masked_def G M, RamBfs.masked_def G A₀, deleteVerts_deleteVerts]
  refine congrArg (deleteVerts G) (Set.ext fun u => ?_)
  simp only [Set.mem_setOf_eq, Set.mem_union, mem_pred, Fin.lt_def]
  rw [hmask (u : ℕ) u.isLt, ← rk_fin u,
    ← rk_fin (⟨centre c, hcentres.centre_lt c hc⟩ : Fin n)]
  by_cases hdead : A₀ (u : ℕ) = 0
  · simp [hdead]
  · simp only [hdead, false_or]
    exact hcentres.processed_iff_rank_lt hc u.isLt hdead

/-! ## The active cover invariant -/

/-- The cover state after the first `c` live centres have been processed. -/
structure CoverInvA (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (q r c xp : ℕ)
    (Xoff Xmem asg M : ℕ → ℕ) : Prop where
  pos_le : c ≤ q
  zero : Xoff 0 = 0
  mono : ∀ k < c, Xoff k ≤ Xoff (k + 1)
  ptr : Xoff c = xp
  ptr_le : xp ≤ c * n
  mem_lt : ∀ p < xp, Xmem p < n
  block : ∀ k < c, ∀ w,
    (∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧ Xmem p = w) ↔
      InCluster (masked G A₀) π r (centre k) w
  block_inj : ∀ k < c, ∀ p p', Xoff k ≤ p → p < Xoff (k + 1) →
    Xoff k ≤ p' → p' < Xoff (k + 1) → Xmem p = Xmem p' → p = p'
  block_mono : ∀ k < c, ∀ p p', Xoff k ≤ p → p < p' →
    p' < Xoff (k + 1) → Xmem p < Xmem p'
  mask : ∀ u < n, M u = 0 ↔ (A₀ u = 0 ∨ ∃ i < c, centre i = u)
  asg_le : ∀ w < n, A₀ w ≠ 0 → asg w ≤ q
  asg_set : ∀ w < n, A₀ w ≠ 0 → asg w < q →
    asg w < c ∧ Catches (masked G A₀) π r (centre (asg w)) w ∧
      ∀ i < q, Catches (masked G A₀) π r (centre i) w → asg w ≤ i
  asg_unset : ∀ w < n, A₀ w ≠ 0 → asg w = q →
    ∀ i < q, Catches (masked G A₀) π r (centre i) w → c ≤ i

namespace CoverInvA

/-- The block offsets are monotone throughout the processed active prefix. -/
theorem mono' (hI : CoverInvA G A₀ π centre q r c xp Xoff Xmem asg M) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ c) : Xoff i ≤ Xoff j := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst this
      exact le_rfl
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (hI.mono j (by omega))
      · have : i = j + 1 := by omega
        subst this
        exact le_rfl

/-- The active pass starts with an empty arena, the ambient mask, and the
active sentinel in every live assignment cell. -/
theorem init (hA : ∀ u < n, M u = A₀ u) (hoff : Xoff 0 = 0)
    (hasg : ∀ w < n, A₀ w ≠ 0 → asg w = q) :
    CoverInvA G A₀ π centre q r 0 0 Xoff Xmem asg M where
  pos_le := Nat.zero_le _
  zero := hoff
  mono := fun _ hk => absurd hk (by omega)
  ptr := hoff
  ptr_le := by omega
  mem_lt := fun _ hp => absurd hp (by omega)
  block := fun _ hk => absurd hk (by omega)
  block_inj := fun _ hk => absurd hk (by omega)
  block_mono := fun _ hk => absurd hk (by omega)
  mask := by
    intro u hu
    rw [hA u hu]
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨i, hi, -⟩)
      · exact h
      · omega
  asg_le := fun w hw halive => (hasg w hw halive).le
  asg_set := fun w hw halive hlt => by rw [hasg w hw halive] at hlt; omega
  asg_unset := fun _ _ _ _ _ _ _ => Nat.zero_le _

/-- One active centre advances the invariant.  The hypotheses are the exact
semantic facts an executable block search and emission walk must return. -/
theorem step (hcentres : CentresBy n q A₀ π centre)
    (hI : CoverInvA G A₀ π centre q r c xp Xoff Xmem asg M) (hc : c < q)
    {D Xoff' Xmem' asg' M' : ℕ → ℕ} {xp' : ℕ}
    (hD : ∀ (w : Fin n) (k : ℕ), k ≤ 2 * r →
      (D (w : ℕ) ≤ k ↔ WithinDist (masked G M) k
        ⟨centre c, hcentres.centre_lt c hc⟩ w))
    (hoff : ∀ k ≤ c, Xoff' k = Xoff k) (hoff' : Xoff' (c + 1) = xp')
    (hkeep : ∀ p < xp, Xmem' p = Xmem p)
    (hblock : ∀ w, (∃ p, xp ≤ p ∧ p < xp' ∧ Xmem' p = w) ↔
      (w < n ∧ D w ≤ 2 * r))
    (hxp : xp ≤ xp') (hxpn : xp' ≤ xp + n)
    (hbinj : ∀ p p', xp ≤ p → p < xp' → xp ≤ p' → p' < xp' →
      Xmem' p = Xmem' p' → p = p')
    (hbmono : ∀ p p', xp ≤ p → p < p' → p' < xp' → Xmem' p < Xmem' p')
    (hasg : ∀ w < n, A₀ w ≠ 0 →
      asg' w = if asg w < q then asg w else if D w ≤ r then c else q)
    (hM : ∀ u < n, M' u = if u = centre c then 0 else M u) :
    CoverInvA G A₀ π centre q r (c + 1) xp' Xoff' Xmem' asg' M' := by
  have hv : centre c < n := hcentres.centre_lt c hc
  have hmg : masked G M =
      deleteVerts (masked G A₀) (pred π ⟨centre c, hv⟩) :=
    masked_step hcentres hc hI.mask
  have hclus : ∀ (w : ℕ) (hw : w < n),
      D w ≤ 2 * r ↔ InCluster (masked G A₀) π r (centre c) w := by
    intro w hw
    rw [hD ⟨w, hw⟩ (2 * r) le_rfl, hmg,
      ← mem_wreach_iff_withinDist_pred, inCluster_iff hv hw]
  have hcatch : ∀ (w : ℕ) (hw : w < n),
      D w ≤ r ↔ Catches (masked G A₀) π r (centre c) w := by
    intro w hw
    rw [hD ⟨w, hw⟩ r (by omega), hmg,
      ← mem_wreach_iff_withinDist_pred, catches_iff hv hw]
  have hoffc : Xoff' c = xp := by rw [hoff c le_rfl, hI.ptr]
  refine ⟨by omega, ?_, ?_, hoff', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hoff 0 (by omega)]
    exact hI.zero
  · intro k hk
    rcases Nat.lt_or_ge k c with hlt | hge
    · rw [hoff k (by omega), hoff (k + 1) (by omega)]
      exact hI.mono k hlt
    · have : k = c := by omega
      subst k
      rw [hoffc, hoff']
      exact hxp
  · have h₁ := hI.ptr_le
    have h₂ : (c + 1) * n = c * n + n := by ring
    omega
  · intro p hp
    rcases Nat.lt_or_ge p xp with hlt | hge
    · rw [hkeep p hlt]
      exact hI.mem_lt p hlt
    · exact ((hblock (Xmem' p)).mp ⟨p, hge, hp, rfl⟩).1
  · intro k hk w
    rcases Nat.lt_or_ge k c with hlt | hge
    · have hbnd : ∀ p, p < Xoff (k + 1) → p < xp := by
        intro p hp
        have hmono := hI.mono' (i := k + 1) (j := c) (by omega) le_rfl
        rw [hI.ptr] at hmono
        omega
      rw [← hI.block k hlt w, hoff k (by omega), hoff (k + 1) (by omega)]
      exact ⟨fun ⟨p, hp₁, hp₂, hp₃⟩ =>
          ⟨p, hp₁, hp₂, by rw [← hp₃, hkeep p (hbnd p hp₂)]⟩,
        fun ⟨p, hp₁, hp₂, hp₃⟩ =>
          ⟨p, hp₁, hp₂, by rw [hkeep p (hbnd p hp₂)]; exact hp₃⟩⟩
    · have : k = c := by omega
      subst k
      rw [hoffc, hoff', hblock w]
      exact ⟨fun h => (hclus w h.1).mp h.2,
        fun h => ⟨h.lt_mem, (hclus w h.lt_mem).mpr h⟩⟩
  · intro k hk p p' hp₁ hp₂ hp₁' hp₂' heq
    rcases Nat.lt_or_ge k c with hlt | hge
    · have hbnd : ∀ z, z < Xoff (k + 1) → z < xp := by
        intro z hz
        have hmono := hI.mono' (i := k + 1) (j := c) (by omega) le_rfl
        rw [hI.ptr] at hmono
        omega
      rw [hoff k (by omega)] at hp₁ hp₁'
      rw [hoff (k + 1) (by omega)] at hp₂ hp₂'
      refine hI.block_inj k hlt p p' hp₁ hp₂ hp₁' hp₂' ?_
      rw [← hkeep p (hbnd p hp₂), ← hkeep p' (hbnd p' hp₂')]
      exact heq
    · have : k = c := by omega
      subst k
      rw [hoffc] at hp₁ hp₁'
      rw [hoff'] at hp₂ hp₂'
      exact hbinj p p' hp₁ hp₂ hp₁' hp₂' heq
  · intro k hk p p' hp₁ hpp' hp₂
    rcases Nat.lt_or_ge k c with hlt | hge
    · have hbnd : ∀ z, z < Xoff (k + 1) → z < xp := by
        intro z hz
        have hmono := hI.mono' (i := k + 1) (j := c) (by omega) le_rfl
        rw [hI.ptr] at hmono
        omega
      rw [hoff k (by omega)] at hp₁
      rw [hoff (k + 1) (by omega)] at hp₂
      rw [hkeep p (hbnd p (by omega)), hkeep p' (hbnd p' hp₂)]
      exact hI.block_mono k hlt p p' hp₁ hpp' hp₂
    · have : k = c := by omega
      subst k
      rw [hoffc] at hp₁
      rw [hoff'] at hp₂
      exact hbmono p p' hp₁ hpp' hp₂
  · intro u hu
    rw [hM u hu]
    by_cases hue : u = centre c
    · rw [if_pos hue]
      exact ⟨fun _ => Or.inr ⟨c, by omega, hue.symm⟩, fun _ => rfl⟩
    · rw [if_neg hue, hI.mask u hu]
      constructor
      · rintro (hdead | ⟨i, hi, hic⟩)
        · exact Or.inl hdead
        · exact Or.inr ⟨i, by omega, hic⟩
      · rintro (hdead | ⟨i, hi, hic⟩)
        · exact Or.inl hdead
        · by_cases hil : i < c
          · exact Or.inr ⟨i, hil, hic⟩
          · have : i = c := by omega
            subst i
            exact absurd hic.symm hue
  · intro w hw halive
    rw [hasg w hw halive]
    by_cases hset : asg w < q
    · rw [if_pos hset]
      exact (hI.asg_le w hw halive)
    · rw [if_neg hset]
      split <;> omega
  · intro w hw halive hlt
    rw [hasg w hw halive] at hlt ⊢
    by_cases hset : asg w < q
    · rw [if_pos hset] at hlt ⊢
      obtain ⟨hc₀, hcat, hmin⟩ := hI.asg_set w hw halive hset
      exact ⟨by omega, hcat, hmin⟩
    · rw [if_neg hset] at hlt ⊢
      have hasgq : asg w = q := by have := hI.asg_le w hw halive; omega
      by_cases hd : D w ≤ r
      · rw [if_pos hd] at hlt ⊢
        exact ⟨by omega, (hcatch w hw).mp hd,
          fun i hi hcat => hI.asg_unset w hw halive hasgq i hi hcat⟩
      · rw [if_neg hd] at hlt
        omega
  · intro w hw halive heq i hi hcat
    rw [hasg w hw halive] at heq
    by_cases hset : asg w < q
    · rw [if_pos hset] at heq
      omega
    · rw [if_neg hset] at heq
      have hasgq : asg w = q := by have := hI.asg_le w hw halive; omega
      by_cases hd : D w ≤ r
      · rw [if_pos hd] at heq
        omega
      · rw [if_neg hd] at heq
        have hci := hI.asg_unset w hw halive hasgq i hi hcat
        have hine : i ≠ c := by
          intro hic
          subst i
          exact hd ((hcatch w hw).mpr hcat)
        omega

/-- At the end of the active prefix, the invariant is the consumer-facing
active cover. -/
theorem out (hcentres : CentresBy n q A₀ π centre)
    (hI : CoverInvA G A₀ π centre q r q xp Xoff Xmem asg M) :
    RamCover.CoverOutA G A₀ π centre r q xp Xoff Xmem asg := by
  have hlt : ∀ w < n, A₀ w ≠ 0 → asg w < q := by
    intro w hw halive
    rcases lt_or_eq_of_le (hI.asg_le w hw halive) with h | heq
    · exact h
    · obtain ⟨i, hi, hic⟩ := hcentres.complete w hw halive
      have hcat : Catches (masked G A₀) π r (centre i) w := by
        rw [hic]
        exact catches_self (masked G A₀) π r hw
      have := hI.asg_unset w hw halive heq i hi hcat
      omega
  refine
    { count_le := hcentres.count_le
      zero := hI.zero
      last := hI.ptr
      mono := hI.mono
      centre_lt := hcentres.centre_lt
      mem_lt := hI.mem_lt
      block := hI.block
      block_inj := hI.block_inj
      block_mono := hI.block_mono
      asg_lt := hlt
      asg_cover := ?_ }
  intro w hw halive
  obtain ⟨-, hcat, hmin⟩ := hI.asg_set w hw halive (hlt w hw halive)
  have hu : centre (asg w) < n := hcentres.centre_lt _ (hlt w hw halive)
  refine subset_trans (ball_subset_fibre_of_min_wreach
    ((catches_iff hu hw).mp hcat) (fun u' hu' => ?_)) (fun z hz => ?_)
  · have hu'alive : A₀ (u' : ℕ) ≠ 0 :=
      (Refine.MassAlive.alive_iff_of_wreach hu').mp halive
    obtain ⟨i, hi, hic⟩ := hcentres.complete (u' : ℕ) u'.isLt hu'alive
    have hcat' : Catches (masked G A₀) π r (centre i) w := by
      apply (catches_iff (hcentres.centre_lt i hi) hw).mpr
      simpa [hic] using hu'
    have hidx : asg w ≤ i := hmin i hi hcat'
    have hrank := hcentres.rank_le (hlt w hw halive) hi hidx
    rw [hic] at hrank
    rw [Fin.le_def, ← rk_of_lt hu, ← rk_fin u']
    exact hrank
  · exact (inCluster_iff hu z.isLt).mpr (by simpa using hz)

end CoverInvA

end Lax3Proofs.RamCoverActive
