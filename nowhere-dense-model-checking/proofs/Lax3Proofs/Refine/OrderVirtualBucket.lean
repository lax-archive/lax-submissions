import Lax3Proofs.Refine.OrderVirtualTournament
import Lax3Proofs.RamDriverOrder

/-!
# Rebuilding a carrier-linear lazy bucket arena

The landed elimination engine keeps stale bucket entries and normally gives
the arena one slot for every degree decrement.  An implicit augmented graph
cannot afford that resident address range.  The bucket representation itself
does not require the old entries, however: zeroing the heads and running the
existing verified bucket initializer reconstructs exactly one live entry per
vertex from the current degree array.

This file proves that rebuilding operation in isolation.  Later the virtual
eliminator invokes it whenever the next carrier-sized row would not fit in the
linear arena; the gap between rebuilds supplies the amortized cost.
-/

namespace Lax3Proofs.Refine.OrderVirtualBucket

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamElim (Buck BuckInv initBuck initBuck_spec)
open Lax3Proofs.RamDriver (fillUpto)

/-- Two carrier widths beyond the initial `n + 1` bucket nodes.  Thus the
physical `bv`/`bn` length used by `RamElim` is `3*n + 3`. -/
def bucketExtra (n : ℕ) : ℕ := 2 * n + 2

@[simp] theorem bucket_arena_length (n : ℕ) :
    n + bucketExtra n + 1 = 3 * n + 3 := by
  simp [bucketExtra]
  omega

/-- Clear the bucket heads and reconstruct the stacks from the current
degree array.  Old arena nodes become unreachable and are overwritten from
slot one upward. -/
def rebuildBuckets : Com :=
  .seq (fillUpto "bh" (.add (.var "n") (.lit 1)) (.lit 0)) initBuck

/-- Exact charge inherited from `fillKeep_spec` and `initBuck_spec`. -/
def rebuildBucketsCost (n : ℕ) : ℕ := 42 * n + 31

/-- Rebuilding forgets every stale node and leaves precisely one bucket node
per vertex.  The theorem deliberately retains an arbitrary physical tail:
only the carrier-linear prefix is ever addressed. -/
theorem rebuildBuckets_spec {B n W : ℕ} {D : ℕ → ℕ}
    (hnB : n + 1 < B) (hD : ∀ v < n, D v < n) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.arrs "deg" = arrOf n D ∧
        (∃ g, σ.arrs "bh" = arrOf (n + 1) g) ∧
        (∃ g, σ.arrs "bv" = arrOf (n + W + 1) g) ∧
        (∃ g, σ.arrs "bn" = arrOf (n + W + 1) g))
      rebuildBuckets
      (fun _ σ' => BuckInv n W D σ' ∧ σ'.vars "i" = n)
      (rebuildBucketsCost n) := by
  have hzero : Spec B
      (fun σ => (∃ g, σ.arrs "bh" = arrOf (n + 1) g) ∧
        (σ.vars "n" = n ∧ σ.arrs "deg" = arrOf n D ∧
          (∃ g, σ.arrs "bv" = arrOf (n + W + 1) g) ∧
          (∃ g, σ.arrs "bn" = arrOf (n + W + 1) g)))
      (fillUpto "bh" (.add (.var "n") (.lit 1)) (.lit 0))
      (fun _ σ' =>
        (∃ h, σ'.arrs "bh" = arrOf (n + 1) h ∧
          (∀ k < n + 1, h k = 0)) ∧
        σ'.vars "i" = n + 1 ∧
        (σ'.vars "n" = n ∧ σ'.arrs "deg" = arrOf n D ∧
          (∃ g, σ'.arrs "bv" = arrOf (n + W + 1) g) ∧
          (∃ g, σ'.arrs "bn" = arrOf (n + W + 1) g)))
      (13 * n + 21) := by
    refine ((Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B)
      (n + 1) (n + 1) "bh" (.add (.var "n") (.lit 1)) (.lit 0)
      (fun _ => 0)
      (fun σ => σ.vars "n" = n ∧ σ.arrs "deg" = arrOf n D ∧
        (∃ g, σ.arrs "bv" = arrOf (n + W + 1) g) ∧
        (∃ g, σ.arrs "bn" = arrOf (n + W + 1) g))
      (by omega) hnB le_rfl ?_ ?_ ?_).post ?_).mono ?_
    · intro σ σ' hQ hv ha
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hv "n" (by decide) |>.trans hQ.1
      · rw [ha "deg" (by decide), hQ.2.1]
      · obtain ⟨g, hg⟩ := hQ.2.2.1
        exact ⟨g, by rw [ha "bv" (by decide), hg]⟩
      · obtain ⟨g, hg⟩ := hQ.2.2.2
        exact ⟨g, by rw [ha "bn" (by decide), hg]⟩
    · intro σ hQ
      have hn₀ := evalB_var (B := B) (σ := σ) (x := "n")
        (by rw [hQ.1]; omega)
      have hn : (Expr.var "n").evalB B σ = some n := by
        simpa only [hQ.1] using hn₀
      exact evalB_bin hn (evalB_lit (by omega)) (by simp; omega)
    · intro _ _ _
      exact evalB_lit (by omega)
    · intro _ _ _ hpost
      obtain ⟨⟨h, hh, hz, -⟩, hi, hQ⟩ := hpost
      exact ⟨⟨h, hh, hz⟩, hi, hQ⟩
    · simp only [Expr.size]
      omega
  intro σ hσ
  obtain ⟨σ₁, r₁, hbh₁, hi₁, hn₁, hdeg₁, hbv₁, hbn₁⟩ :=
    hzero.run ⟨hσ.2.2.1, hσ.1, hσ.2.1, hσ.2.2.2.1, hσ.2.2.2.2⟩
  obtain ⟨BH, hBH, hBH0⟩ := hbh₁
  have hinit := initBuck_spec B n W D hnB hD
  obtain ⟨σ₂, r₂, hpost⟩ := hinit.run
    ⟨hn₁, hdeg₁, ⟨BH, hBH, fun j hj => hBH0 j (by omega)⟩, hbv₁, hbn₁⟩
  refine ⟨σ₂, ?_, hpost⟩
  exact (r₁.seq r₂).mono (by simp only [rebuildBucketsCost]; omega)

/-! ## The fixed linear instance -/

/-- At the fixed arena width, a fresh rebuild places the allocation pointer
at `n+1`, leaving room for an entire carrier row before index `3*n+3`. -/
theorem rebuilt_has_row_room {n : ℕ} :
    (n + 1) + n < n + bucketExtra n + 1 := by
  simp [bucketExtra]
  omega

/-! ## Axiom audit -/

#print axioms rebuildBuckets_spec
#print axioms rebuilt_has_row_room

end Lax3Proofs.Refine.OrderVirtualBucket
