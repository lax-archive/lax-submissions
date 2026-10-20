import Lax457868Proofs.ExceptionRepairLoop
import Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
import Mathlib.Tactic

/-! A coarse deterministic reserve for all local-repair bits in one source
sampler call. This is a tape-length fact; it is not the expected cost bound. -/

namespace Lax457868Proofs.RefinedTapeReserve

open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ExceptionPhaseSource
open Lax808846Proofs.Reasoning.Lib
open scoped symmDiff

lemma traceBitCost_le {n cap s t e : ℕ} {G : SimpleGraph (Fin n)}
    {A : Finset ℕ} {rep : ℕ → ℕ} {steps : List ExecutedException}
    (hA : A ⊆ Finset.range n)
    (hlen : steps.length ≤ e)
    (hsteps : ∀ z ∈ steps, z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t)) :
    traceBitCost G A rep steps ≤ e * (cap * (s * t * Nat.clog 2 n)) := by
  have hsingle (z : ExecutedException) (hz : z ∈ steps) :
      z.bitCost G A rep ≤ cap * (s * t * Nat.clog 2 n) := by
    let X := (numericNeighborhood G z.vertex ∩ A) ∆
      (numericNeighborhood G (rep z.vertex) ∩ A)
    have hX : X ⊆ A := by
      intro v hv
      simp only [X, Finset.mem_symmDiff, Finset.mem_inter] at hv
      tauto
    have hcard : X.card ≤ n := by
      have hh := (Finset.card_le_card hX).trans (Finset.card_le_card hA)
      simpa using hh
    have hlog : Nat.clog 2 X.card ≤ Nat.clog 2 n :=
      Nat.clog_mono_right 2 hcard
    have huse : z.used ≤ cap * (s * t) :=
      (hsteps z hz).2.trans (Nat.mul_le_mul_right _ (hsteps z hz).1)
    dsimp [ExecutedException.bitCost]
    change z.used * Nat.clog 2 X.card ≤ _
    calc
      z.used * Nat.clog 2 X.card ≤ (cap * (s * t)) * Nat.clog 2 n :=
        Nat.mul_le_mul huse hlog
      _ = cap * (s * t * Nat.clog 2 n) := by ring
  have hsum : ∀ ys : List ExecutedException,
      (∀ z ∈ ys, z ∈ steps) →
      (ys.map (ExecutedException.bitCost G A rep)).sum ≤
        ys.length * (cap * (s * t * Nat.clog 2 n)) := by
    intro ys
    induction ys with
    | nil => simp
    | cons z zs ih =>
      intro hmem
      have hz := hsingle z (hmem z (by simp))
      have htail := ih (by
        intro w hw
        exact hmem w (by simp [hw]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  have hh := hsum steps (by intros; assumption)
  dsimp [traceBitCost]
  exact hh.trans (Nat.mul_le_mul_right _ hlen)

lemma steps_length_le {e : ℕ} {steps : List ExecutedException}
    {exceptionList : ℕ → ℕ}
    (hmap : steps.map ExecutedException.vertex =
      (Stack.toList e exceptionList).take steps.length) :
    steps.length ≤ e := by
  have h := congrArg List.length hmap
  simp at h
  omega

end Lax457868Proofs.RefinedTapeReserve
