import Lax3Proofs.RamCoverActive
import Lax3Proofs.Refine.ReachedBridge

/-!
# Active-prefix cover emission bridge

`CoverSynth.emitRun` already has the right touched-only implementation for a
nested cover.  Its first numeric parameter, however, is the assignment
sentinel, whereas `ReachedList`'s numeric parameter is the carrier size.  They
coincide in the carrier-wide pass and differ at an active prefix (`q ≤ n`).

This file separates those two roles.  The list-level facts below run the
existing emitter with sentinel `q`, while the reached-list facts continue to
range over `n`.  The final theorem packages one such run as exactly one
`RawCoverInvA.step`; in particular, no discovery-order claim is made.
-/

namespace Lax3Proofs.Refine.CoverActiveBridge

open Lax3.ColoredGraphs
open Lax13Proofs.Reasoning
open Lax13Proofs.Refine
open Lax13Proofs.Refine.BfsQ (QPost)
open Lax3Proofs.RamCoverActive
open Lax3Proofs.Refine.CoverSynth

/-! ## List/function devices -/

/-- Read a machine list as the total function used by the cover invariant. -/
def larr (xs : List ℕ) : ℕ → ℕ := fun i => xs[i]!

@[simp] theorem larr_apply (xs : List ℕ) (i : ℕ) : larr xs i = xs[i]! := rfl

/-- A single mathematical function update. -/
def fset (f : ℕ → ℕ) (i v : ℕ) : ℕ → ℕ := fun z => if z = i then v else f z

@[simp] theorem fset_eq (f : ℕ → ℕ) (i v : ℕ) : fset f i v i = v := by
  simp [fset]

theorem fset_ne (f : ℕ → ℕ) (i v z : ℕ) (h : z ≠ i) : fset f i v z = f z := by
  simp [fset, h]

/-! ## The active-sentinel readings of the emitter -/

/-- The emitted arena segment is the reached set.  `q` is used only by the
assignment update; `n` remains the carrier of `ReachedList`. -/
theorem emitRun_blockA (reach dist : List ℕ) (n q c s tl d : ℕ) (t : ESt)
    (hk : t.1 = 0) (hlen : t.2.1 + max tl 1 ≤ t.2.2.1.length)
    (hR : ReachedList n d dist reach tl) (w : ℕ) :
    (∃ p, t.2.1 ≤ p ∧ p < t.2.1 + max tl 1 ∧
        (emitRun reach dist q c s (max tl 1) t).2.2.1[p]! = w)
      ↔ (w < n ∧ dist[w]! ≤ d) := by
  obtain ⟨hlt, -, hiff⟩ := hR
  obtain ⟨-, harena⟩ := emitRun_arena reach dist q c s (max tl 1) t hlen
  constructor
  · rintro ⟨p, hp₁, hp₂, hp₃⟩
    obtain ⟨k, rfl⟩ : ∃ k, p = t.2.1 + k := ⟨p - t.2.1, by omega⟩
    have hkk : k < max tl 1 := by omega
    rw [harena k hkk, hk, Nat.zero_add] at hp₃
    exact ⟨hp₃ ▸ hlt k hkk, (hiff w (hp₃ ▸ hlt k hkk)).2 ⟨k, hkk, hp₃⟩⟩
  · rintro ⟨hw, hd⟩
    obtain ⟨k, hkk, hkw⟩ := (hiff w hw).1 hd
    exact ⟨t.2.1 + k, by omega, by omega, by
      rw [harena k hkk, hk, Nat.zero_add]
      exact hkw⟩

/-- The reached prefix cannot contain more slots than carrier vertices. -/
theorem reachedSlots_le {n d tl : ℕ} {dist reach : List ℕ}
    (hR : ReachedList n d dist reach tl) : max tl 1 ≤ n := by
  let f : Fin (max tl 1) → Fin n := fun k => ⟨reach[(k : ℕ)]!, hR.1 k k.isLt⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hR.2.1 i i.isLt j j.isLt (congrArg Fin.val hij)
  simpa using Fintype.card_le_of_injective f hf

/-- Pointwise assignment semantics with an active sentinel.  Only a live
vertex's entering cell needs a bound; dead cells are outside the active
consumer contract. -/
theorem emitRun_hasgA (reach dist : List ℕ) (n q c r d tl : ℕ) (t : ESt)
    (hk : t.1 = 0) (hrd : r ≤ d) (hR : ReachedList n d dist reach tl)
    (w : ℕ) (hw : w < n) (hle : t.2.2.2[w]! ≤ q)
    (hlen : ∀ k < max tl 1, reach[k]! < t.2.2.2.length) :
    (emitRun reach dist q c (r + 1) (max tl 1) t).2.2.2[w]!
      = if t.2.2.2[w]! < q then t.2.2.2[w]!
        else if dist[w]! ≤ r then c else q := by
  obtain ⟨-, hinj, hiff⟩ := hR
  rw [emitRun_asg reach dist q c (r + 1) (max tl 1) t
    (by intro k hkk; rw [hk, Nat.zero_add]; exact hlen k hkk)
    (by intro k hkk k' hkk' he
        rw [hk, Nat.zero_add, Nat.zero_add] at he
        exact hinj k hkk k' hkk' he) w]
  have hmem : (∃ k < max tl 1, reach[t.1 + k]! = w) ↔ dist[w]! ≤ d := by
    rw [hk]
    simp only [Nat.zero_add]
    exact (hiff w hw).symm
  by_cases hset : t.2.2.2[w]! < q
  · rw [if_pos hset]
    by_cases hm : ∃ k < max tl 1, reach[t.1 + k]! = w
    · rw [if_pos hm, newAsg, if_pos hset]
      split <;> rfl
    · rw [if_neg hm]
  · rw [if_neg hset]
    have hq : t.2.2.2[w]! = q := le_antisymm hle (by omega)
    by_cases hm : ∃ k < max tl 1, reach[t.1 + k]! = w
    · rw [if_pos hm, newAsg, hq]
      by_cases hd : dist[w]! < r + 1
      · rw [if_pos hd, if_neg (by omega), if_pos (by omega)]
      · rw [if_neg hd, if_neg (by omega)]
    · rw [if_neg hm, hq, if_neg (by
        intro hd
        exact hm (hmem.mpr (by omega)))]

/-! ## One synthesized emission advances the raw invariant -/

variable {n q r c xp tl : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ M centre Xoff : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
variable {dist reach xmem asg : List ℕ}

/-- The exact semantic seam between the touched-only list emitter and the
active cover mathematics.  The search supplies `QPost` and `ReachedList`;
the emitter supplies the new arena and assignment arrays; the result is one
complete `RawCoverInvA` turn. -/
theorem emitRun_raw_step
    (hcentres : CentresBy n q A₀ π centre)
    (hI : RawCoverInvA G A₀ π centre q r c xp Xoff (larr xmem) (larr asg) M)
    (hc : c < q) (hxm : xmem.length = n * n) (hag : asg.length = n)
    (hpost : QPost n (2 * r) (centre c) G (arrOf n M)
      (hcentres.centre_lt c hc) dist)
    (hR : ReachedList n (2 * r) dist reach tl) :
    let e := emitRun reach dist q c (r + 1) (max tl 1) (0, xp, xmem, asg)
    RawCoverInvA G A₀ π centre q r (c + 1) e.2.1
      (fset Xoff (c + 1) e.2.1) (larr e.2.2.1) (larr e.2.2.2)
      (fset M (centre c) 0) := by
  dsimp only
  let slots := max tl 1
  let e := emitRun reach dist q c (r + 1) slots (0, xp, xmem, asg)
  have hslots : slots ≤ n := reachedSlots_le hR
  have hcq : c + 1 ≤ q := by omega
  have hcn0 : c + 1 ≤ n := le_trans hcq hcentres.count_le
  have hcn : (c + 1) * n ≤ n * n := Nat.mul_le_mul_right n hcn0
  have hmul : (c + 1) * n = c * n + n := by ring
  have heLen : xp + slots ≤ xmem.length := by
    rw [hxm]
    calc
      xp + slots ≤ c * n + n := Nat.add_le_add hI.ptr_le hslots
      _ = (c + 1) * n := hmul.symm
      _ ≤ n * n := hcn
  have hePtr : e.2.1 = xp + slots := by
    dsimp only [e]
    simpa using
      (emitRun_ptr reach dist q c (r + 1) slots (0, xp, xmem, asg))
  obtain ⟨heKeep, heWrite⟩ :=
    emitRun_arena reach dist q c (r + 1) slots (0, xp, xmem, asg) heLen
  apply RawCoverInvA.step hcentres hI hc
  · intro w k hk
    exact (hpost.2 w k hk).trans Lax3Proofs.Refine.BfsBridge.wd_iff_withinDist
  · intro k hk
    exact fset_ne Xoff (c + 1) e.2.1 k (by omega)
  · exact fset_eq Xoff (c + 1) e.2.1
  · intro p hp
    exact heKeep p hp
  · intro w
    rw [hePtr]
    exact emitRun_blockA reach dist n q c (r + 1) tl (2 * r)
      (0, xp, xmem, asg) rfl heLen hR w
  · rw [hePtr]
    exact Nat.le_add_right xp slots
  · rw [hePtr]
    exact Nat.add_le_add_left hslots xp
  · intro p p' hp₁ hp₂ hp₁' hp₂' heq
    rw [hePtr] at hp₂ hp₂'
    obtain ⟨k, rfl⟩ : ∃ k, p = xp + k := ⟨p - xp, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', p' = xp + k' := ⟨p' - xp, by omega⟩
    have hk : k < slots := by omega
    have hk' : k' < slots := by omega
    change e.2.2.1[xp + k]! = e.2.2.1[xp + k']! at heq
    rw [heWrite k hk, heWrite k' hk', Nat.zero_add, Nat.zero_add] at heq
    have hkk := hR.2.1 k hk k' hk' heq
    omega
  · intro w hw halive
    exact emitRun_hasgA reach dist n q c r (2 * r) tl
      (0, xp, xmem, asg) rfl (by omega) hR w hw
      (hI.asg_le w hw halive) (by
        intro k hk
        rw [hag]
        exact hR.1 k hk)
  · intro u hu
    rfl

/-! ## Axiom audit -/

#print axioms reachedSlots_le
#print axioms emitRun_hasgA
#print axioms emitRun_raw_step

end Lax3Proofs.Refine.CoverActiveBridge
