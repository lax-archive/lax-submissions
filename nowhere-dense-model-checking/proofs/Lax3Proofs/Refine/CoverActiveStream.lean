import Lax3Proofs.Refine.CoverActiveBlock

/-!
# Streaming active-cover semantics

The original active-cover invariant retains every completed block in one
arena.  That representation is useful to a later consumer, but it forces the
executed arena pointer through as many as `n * D` words.  At the exact C0 word
length this is not a harmless logical allocation: the pointer itself no longer
fits in one machine word when the cover degree is input-dependent.

This file separates the facts that genuinely persist between centre turns
from the row that is consumed by the current cluster.  `CoverPrefixA` keeps
only the progressive mask and first-catcher assignment.  `RawStreamRowA`
then describes one duplicate-free BFS row in the reusable prefix
`xmem[0..tail)`.  No statement mentions an accumulated arena pointer or an
offset table.
-/

namespace Lax3Proofs.Refine.CoverActiveStream

open Lax3.ColoredGraphs
open Lax3Proofs.RamBfs (WD masked)
open Lax3Proofs.RamCover
open Lax3Proofs.RamCoverActive
open Lax3Proofs.Refine.BfsBlock
open Lax3Proofs.Refine.CoverActiveBlock

variable {n q r c tail : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre asg M Q QD Xmem : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)}

/-! ## Persistent prefix state -/

/-- The semantic state that must survive from one active centre to the next.
It is exactly the non-representation tail of `RawCoverInvA`: the progressive
mask and the stable first-catcher assignment. -/
structure CoverPrefixA (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (q r c : ℕ)
    (asg M : ℕ → ℕ) : Prop where
  pos_le : c ≤ q
  mask : ∀ u < n, M u = 0 ↔ (A₀ u = 0 ∨ ∃ i < c, centre i = u)
  asg_le : ∀ w < n, A₀ w ≠ 0 → asg w ≤ q
  asg_set : ∀ w < n, A₀ w ≠ 0 → asg w < q →
    asg w < c ∧ Catches (masked G A₀) π r (centre (asg w)) w ∧
      ∀ i < q, Catches (masked G A₀) π r (centre i) w → asg w ≤ i
  asg_unset : ∀ w < n, A₀ w ≠ 0 → asg w = q →
    ∀ i < q, Catches (masked G A₀) π r (centre i) w → c ≤ i

namespace CoverPrefixA

/-- Forget the accumulated rows of the historical raw invariant. -/
theorem of_raw {xp : ℕ} {Xoff Xmem : ℕ → ℕ}
    (h : RawCoverInvA G A₀ π centre q r c xp Xoff Xmem asg M) :
    CoverPrefixA G A₀ π centre q r c asg M :=
  { pos_le := h.pos_le
    mask := h.mask
    asg_le := h.asg_le
    asg_set := h.asg_set
    asg_unset := h.asg_unset }

/-- The streaming pass starts with the ambient mask and the active sentinel
in every live assignment cell. -/
theorem init (hA : ∀ u < n, M u = A₀ u)
    (hasg : ∀ w < n, A₀ w ≠ 0 → asg w = q) :
    CoverPrefixA G A₀ π centre q r 0 asg M where
  pos_le := Nat.zero_le _
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

/-- The current centre has not yet been removed from the progressive mask. -/
theorem currentCentre_alive (hcentres : CentresBy n q A₀ π centre)
    (hI : CoverPrefixA G A₀ π centre q r c asg M) (hc : c < q) :
    M (centre c) ≠ 0 := by
  intro hzero
  rcases (hI.mask (centre c) (hcentres.centre_lt c hc)).mp hzero with
    hdead | ⟨i, hi, hic⟩
  · exact hcentres.alive c hc hdead
  · have hieq := hcentres.injective (by omega) hc hic
    omega

/-- One searched centre advances the persistent state.  Notice that the
hypotheses contain no row store: the current row may be consumed and reused
without affecting this theorem. -/
theorem step (hcentres : CentresBy n q A₀ π centre)
    (hI : CoverPrefixA G A₀ π centre q r c asg M) (hc : c < q)
    {D asg' M' : ℕ → ℕ}
    (hD : ∀ (w : Fin n) (k : ℕ), k ≤ 2 * r →
      (D (w : ℕ) ≤ k ↔ WithinDist (masked G M) k
        ⟨centre c, hcentres.centre_lt c hc⟩ w))
    (hasg : ∀ w < n, A₀ w ≠ 0 →
      asg' w = if asg w < q then asg w else if D w ≤ r then c else q)
    (hM : ∀ u < n, M' u = if u = centre c then 0 else M u) :
    CoverPrefixA G A₀ π centre q r (c + 1) asg' M' := by
  have hv : centre c < n := hcentres.centre_lt c hc
  have hmg : masked G M =
      Lax12.UniformQuasiWideness.deleteVerts (masked G A₀)
        (pred π ⟨centre c, hv⟩) :=
    masked_step hcentres hc hI.mask
  have hcatch : ∀ (w : ℕ) (hw : w < n),
      D w ≤ r ↔ Catches (masked G A₀) π r (centre c) w := by
    intro w hw
    rw [hD ⟨w, hw⟩ r (by omega), hmg,
      ← mem_wreach_iff_withinDist_pred, catches_iff hv hw]
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
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
      exact hI.asg_le w hw halive
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

/-- Every assignment already made by a prefix has the full cover property.
This is the fact needed to consume row `c` immediately: later centres cannot
change a first-catcher cell whose value is already below `q`. -/
theorem assigned_cover (hcentres : CentresBy n q A₀ π centre)
    (hI : CoverPrefixA G A₀ π centre q r c asg M)
    (v : ℕ) (hv : v < n) (halive : A₀ v ≠ 0) (hset : asg v < q) :
    ball (masked G A₀) r ⟨v, hv⟩ ⊆
      {z : Fin n | InCluster (masked G A₀) π r (centre (asg v)) (z : ℕ)} := by
  obtain ⟨-, hcat, hmin⟩ := hI.asg_set v hv halive hset
  have hu : centre (asg v) < n := hcentres.centre_lt _ hset
  refine subset_trans (ball_subset_fibre_of_min_wreach
    ((catches_iff hu hv).mp hcat) (fun u' hu' => ?_)) (fun z hz => ?_)
  · have hu'alive : A₀ (u' : ℕ) ≠ 0 :=
      (Lax3Proofs.Refine.MassAlive.alive_iff_of_wreach hu').mp halive
    obtain ⟨i, hi, hic⟩ := hcentres.complete (u' : ℕ) u'.isLt hu'alive
    have hcat' : Catches (masked G A₀) π r (centre i) v := by
      apply (catches_iff (hcentres.centre_lt i hi) hv).mpr
      simpa [hic] using hu'
    have hidx : asg v ≤ i := hmin i hi hcat'
    have hrank := hcentres.rank_le hset hi hidx
    rw [hic] at hrank
    rw [Fin.le_def, ← rk_of_lt hu, ← rk_fin u']
    exact hrank
  · exact (inCluster_iff hu z.isLt).mpr (by simpa using hz)

end CoverPrefixA

/-! ## One reusable row -/

/-- The output of one streamed centre search before row sorting.  The row
occupies only `xmem[0..tail)` and carries the already-advanced persistent
state. -/
structure RawStreamRowA (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (q r c tail : ℕ)
    (Xmem asg M : ℕ → ℕ) : Prop where
  state : CoverPrefixA G A₀ π centre q r (c + 1) asg M
  tail_le : tail ≤ n
  mem_lt : ∀ p < tail, Xmem p < n
  block : ∀ w, (∃ p, p < tail ∧ Xmem p = w) ↔
    InCluster (masked G A₀) π r (centre c) w
  block_inj : ∀ p p', p < tail → p' < tail → Xmem p = Xmem p' → p = p'

/-- The streamed row after sorting. -/
structure StreamRowA (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (q r c tail : ℕ)
    (Xmem asg M : ℕ → ℕ) : Prop extends
      RawStreamRowA G A₀ π centre q r c tail Xmem asg M where
  block_mono : ∀ p p', p < p' → p' < tail → Xmem p < Xmem p'

namespace RawStreamRowA

/-- A row rearrangement that preserves membership and returns increasing
entries upgrades the raw streamed row to the consumer-facing form. -/
theorem sorted
    (h : RawStreamRowA G A₀ π centre q r c tail Xmem asg M)
    {Xmem' : ℕ → ℕ}
    (hmem : ∀ p < tail, Xmem' p < n)
    (hblock : ∀ w, (∃ p, p < tail ∧ Xmem' p = w) ↔
      (∃ p, p < tail ∧ Xmem p = w))
    (hmono : ∀ p p', p < p' → p' < tail → Xmem' p < Xmem' p') :
    StreamRowA G A₀ π centre q r c tail Xmem' asg M := by
  refine { toRawStreamRowA := ?_, block_mono := hmono }
  refine ⟨h.state, h.tail_le, hmem, ?_, ?_⟩
  · intro w
    rw [hblock w, h.block w]
  · intro p p' hp hp' heq
    rcases lt_trichotomy p p' with hpp | hpp | hpp
    · have := hmono p p' hpp hp'
      omega
    · exact hpp
    · have := hmono p' p hpp hp
      omega

/-- **The streaming block seam.**  Copying the returned BFS queue into the
reusable row prefix, updating first-catcher assignments, and killing the
current centre produces one exact row plus the next persistent prefix. -/
theorem stepQueue
    (hcentres : CentresBy n q A₀ π centre)
    (hI : CoverPrefixA G A₀ π centre q r c asg M) (hc : c < q)
    (htail : tail ≤ n)
    (hQlt : ∀ i, i < tail → Q i < n)
    (hseg : ∀ v, v < n →
      ((∃ i, i < tail ∧ Q i = v) ↔
        (M v ≠ 0 ∧ WD G M (2 * r) (centre c) v)))
    (hQinj : ∀ i, i < tail → ∀ j, j < tail → Q i = Q j → i = j)
    (hQD : ∀ i, i < tail → ∀ k, k ≤ 2 * r →
      (QD i ≤ k ↔ WD G M k (centre c) (Q i)))
    {Xmem' asg' M' : ℕ → ℕ}
    (hwrite : ∀ i < tail, Xmem' i = Q i)
    (hasg' : ∀ w < n, A₀ w ≠ 0 →
      asg' w = if asg w < q then asg w
        else if ∃ i, i < tail ∧ Q i = w ∧ QD i ≤ r then c else q)
    (hM : ∀ u < n, M' u = if u = centre c then 0 else M u) :
    RawStreamRowA G A₀ π centre q r c tail Xmem' asg' M' := by
  let D : ℕ → ℕ := queueDist (2 * r) tail Q QD
  have hsM : M (centre c) ≠ 0 := CoverPrefixA.currentCentre_alive hcentres hI hc
  have hs : centre c < n := hcentres.centre_lt c hc
  have hD : ∀ (w : Fin n) (k : ℕ), k ≤ 2 * r →
      (D (w : ℕ) ≤ k ↔ WithinDist (masked G M) k ⟨centre c, hs⟩ w) := by
    intro w k hk
    exact (queueDist_le_iff_wd w.isLt hsM hk hseg hQD).trans
      (Lax3Proofs.RamBfs.wd_iff_withinDist hs w.isLt)
  have hasgD : ∀ w < n, A₀ w ≠ 0 →
      asg' w = if asg w < q then asg w else if D w ≤ r then c else q := by
    intro w hw halive
    rw [hasg' w hw halive]
    by_cases hset : asg w < q
    · simp only [hset, if_true]
    · simp only [hset, if_false]
      have hiff := queueCatch_iff (d₀ := r) (d := 2 * r) (s := centre c) (w := w)
        hw hsM (by omega) hseg hQD
      by_cases hcatch : ∃ i, i < tail ∧ Q i = w ∧ QD i ≤ r
      · have hdist : D w ≤ r := hiff.mp hcatch
        simp only [hcatch, hdist, if_true]
      · have hdist : ¬ D w ≤ r := fun hd => hcatch (hiff.mpr hd)
        simp only [hcatch, hdist, if_false]
  have hprefix : CoverPrefixA G A₀ π centre q r (c + 1) asg' M' :=
    CoverPrefixA.step hcentres hI hc hD hasgD hM
  have hmg : masked G M =
      Lax12.UniformQuasiWideness.deleteVerts (masked G A₀)
        (pred π ⟨centre c, hs⟩) :=
    masked_step hcentres hc hI.mask
  have hclus : ∀ (w : ℕ) (hw : w < n),
      D w ≤ 2 * r ↔ InCluster (masked G A₀) π r (centre c) w := by
    intro w hw
    rw [hD ⟨w, hw⟩ (2 * r) le_rfl, hmg,
      ← mem_wreach_iff_withinDist_pred, inCluster_iff hs hw]
  refine ⟨hprefix, htail, ?_, ?_, ?_⟩
  · intro p hp
    rw [hwrite p hp]
    exact hQlt p hp
  · intro w
    constructor
    · rintro ⟨p, hp, hpw⟩
      have hQw : Q p = w := by rw [← hpw, hwrite p hp]
      have hqn := hQlt p hp
      have hwd := (hseg (Q p) hqn).mp ⟨p, hp, rfl⟩ |>.2
      exact (hclus w (hQw ▸ hqn)).mp
        ((queueDist_le_iff_wd (hQw ▸ hqn) hsM le_rfl hseg hQD).mpr
          (by simpa only [hQw] using hwd))
    · intro hcluster
      have hw : w < n := hcluster.lt_mem
      have hwd := (queueDist_le_iff_wd hw hsM le_rfl hseg hQD).mp
        ((hclus w hw).mpr hcluster)
      have hMw : M w ≠ 0 := by
        by_cases hws : w = centre c
        · simpa only [hws] using hsM
        · exact alive_of_wd hwd (Ne.symm hws)
      obtain ⟨i, hi, hQi⟩ := (hseg w hw).mpr ⟨hMw, hwd⟩
      exact ⟨i, hi, by rw [hwrite i hi, hQi]⟩
  · intro p p' hp hp' heq
    rw [hwrite p hp, hwrite p' hp'] at heq
    exact hQinj p hp p' hp' heq

end RawStreamRowA

/-! ## Axiom audit -/

#print axioms CoverPrefixA.step
#print axioms CoverPrefixA.assigned_cover
#print axioms RawStreamRowA.sorted
#print axioms RawStreamRowA.stepQueue

end Lax3Proofs.Refine.CoverActiveStream
