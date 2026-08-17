import Lax3Proofs.Refine.OrderActiveElim
import Lax3Proofs.Refine.CompactPreps

/-!
# Relinking compact active augmentation rounds

The compact augmentation engine returns its next orientation in
`noff`/`ntg`.  Its next invocation reads `ioff`/`itg`, so the active order
phase needs one small resident-workspace relink between rounds.  Both copies
stop at the compact carrier or the live slot count; no pass scans the ambient
carrier or the physical target width.
-/

namespace Lax3Proofs.Refine.OrderActiveRound

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriver (copyUpto fillUpto)

/-- The data which the two copies must retain while their loop counter moves. -/
def RoundRelinkQ (n W mm m : ℕ) (NOg NT : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "mm" = mm ∧ σ.vars "mn" = m ∧
  σ.arrs "noff" = arrOf (n + 1) NOg ∧ σ.arrs "ntg" = arrOf W NT

private theorem roundRelinkQ_frame {n W mm m : ℕ} {NOg NT : ℕ → ℕ} {a : String}
    (hnoff : a ≠ "noff") (hntg : a ≠ "ntg") :
    ∀ σ σ' : Env, RoundRelinkQ n W mm m NOg NT σ →
      (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) →
      (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) →
      RoundRelinkQ n W mm m NOg NT σ' := by
  rintro σ σ' ⟨hmm, hmn, hNO, hNT⟩ hv ha
  exact ⟨by rw [hv "mm" (by decide), hmm], by rw [hv "mn" (by decide), hmn],
    by rw [ha "noff" (Ne.symm hnoff), hNO],
    by rw [ha "ntg" (Ne.symm hntg), hNT]⟩

/-- Copy the round output back to the compact input arrays, then make its
actual slot count the bound used by the next compact round. -/
def roundRelinkCom : Com :=
  .seq (copyUpto "noff" "ioff" (.add (.var "mm") (.lit 1)))
    (.seq (copyUpto "ntg" "itg" (.var "mn"))
      (.assign "kd" (.var "mn")))

/-- Exact cost of the two live-prefix copies and the scalar assignment. -/
def roundRelinkCost (mm m : ℕ) : ℕ := 14 * mm + 12 * m + 30

/-- The compact output CSR becomes the next round's input CSR.  The offset
copy visits `mm + 1` cells and the target copy visits exactly `m` cells.
Both physical tails are retained, all other arrays are framed, and the new
input slot scalar is `m`. -/
theorem roundRelink_spec {B n W mm m : ℕ} {NOg NO NT : ℕ → ℕ} {σ : Env}
    (hmmB : mm + 1 < B) (hmB : m < B) (hmn : mm ≤ n) (hmW : m ≤ W)
    (hmm : σ.vars "mm" = mm) (hmnvar : σ.vars "mn" = m)
    (hnoff : σ.arrs "noff" = arrOf (n + 1) NOg)
    (hNO : ∀ i, i ≤ mm → NOg i = NO i)
    (hntg : σ.arrs "ntg" = arrOf W NT)
    (hNOB : ∀ i, i ≤ mm → NO i < B) (hNTB : ∀ z, z < m → NT z < B)
    (hioff : ∃ g, σ.arrs "ioff" = arrOf (n + 1) g)
    (hitg : ∃ g, σ.arrs "itg" = arrOf W g) :
    ∃ σ', Run B roundRelinkCom σ σ' (roundRelinkCost mm m) ∧
      (∃ g, σ'.arrs "ioff" = arrOf (n + 1) g ∧ ∀ i, i ≤ mm → g i = NO i) ∧
      (∃ g, σ'.arrs "itg" = arrOf W g ∧ ∀ z, z < m → g z = NT z) ∧
      σ'.vars "kd" = m ∧ σ'.vars "mm" = mm ∧ σ'.vars "mn" = m ∧
      (∀ a, a ≠ "ioff" → a ≠ "itg" → σ'.arrs a = σ.arrs a) := by
  classical
  have hQ₀ : RoundRelinkQ n W mm m NOg NT σ := ⟨hmm, hmnvar, hnoff, hntg⟩
  have hNOgB : ∀ k < mm + 1, NOg k < B := by
    intro k hk
    rw [hNO k (by omega)]
    exact hNOB k (by omega)
  have c₁ :=
    (Lax3Proofs.RamDriverOrder.copyKeep_spec (B := B) (mm + 1) (n + 1) (n + 1)
      "noff" "ioff" (.add (.var "mm") (.lit 1)) NOg
      (RoundRelinkQ n W mm m NOg NT) (by omega) hmmB (by omega) (by omega)
      (roundRelinkQ_frame (by decide) (by decide))
      (fun _ hQ => Lax3Proofs.Refine.CompactPreps.evalB_mmAdd1 hQ.1 hmmB)
      (fun _ hQ => hQ.2.2.1) hNOgB).mono
      (show ((Expr.add (.var "mm") (.lit 1)).size + 11) * (mm + 1) +
          (Expr.add (.var "mm") (.lit 1)).size + 5 ≤ 14 * mm + 22 by
        simp only [Expr.size]
        omega)
  obtain ⟨σ₁, r₁, ⟨IO₁, hIO₁, hIO₁lo, -⟩, -, hQ₁⟩ := c₁.run ⟨hioff, hQ₀⟩
  have c₂ :=
    (Lax3Proofs.RamDriverOrder.copyKeep_spec (B := B) m W W "ntg" "itg" (.var "mn") NT
      (RoundRelinkQ n W mm m NOg NT) (by omega) hmB hmW hmW
      (roundRelinkQ_frame (by decide) (by decide))
      (fun _ hQ => Lax3Proofs.Refine.CompactPreps.evalB_scalar hQ.2.1 hmB)
      (fun _ hQ => hQ.2.2.2) hNTB).mono
      (show ((Expr.var "mn").size + 11) * m + (Expr.var "mn").size + 5 ≤
          12 * m + 6 by
        simp only [Expr.size]
        omega)
  obtain ⟨σ₂, r₂, ⟨IT₂, hIT₂, hIT₂lo, -⟩, -, hQ₂⟩ := c₂.run ⟨(by
    obtain ⟨g, hg⟩ := hitg
    exact ⟨g, by rw [r₁.frame_arr "itg" (by
      simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hg]⟩), hQ₁⟩
  have hmn₂ : σ₂.vars "mn" = m := hQ₂.2.1
  have r₃ : Run B (.assign "kd" (.var "mn")) σ₂ (σ₂.setVar "kd" m) 2 := by
    have h := Run.assign (B := B) (σ := σ₂) (x := "kd") (e := .var "mn")
      (evalB_var (by rw [hmn₂]; exact hmB))
    rw [hmn₂] at h
    simpa using h
  let σ' := σ₂.setVar "kd" m
  have rAll : Run B roundRelinkCom σ σ' (roundRelinkCost mm m) := by
    change Run B roundRelinkCom σ (σ₂.setVar "kd" m) (roundRelinkCost mm m)
    exact (r₁.seq (r₂.seq r₃)).mono (by
      simp only [roundRelinkCost]
      omega)
  refine ⟨σ', rAll, ⟨IO₁, ?_, ?_⟩, ⟨IT₂, ?_, hIT₂lo⟩, ?_, ?_, ?_, ?_⟩
  · change σ₂.arrs "ioff" = arrOf (n + 1) IO₁
    rw [r₂.frame_arr "ioff" (by simp [copyUpto, fillUpto, Fill.put, Com.warrs])]
    exact hIO₁
  · intro i hi
    rw [hIO₁lo i (by omega), hNO i hi]
  · exact hIT₂
  · simp [σ']
  · simp only [σ', vars_setVar, if_neg (by decide : ¬ ("mm" = "kd"))]
    exact hQ₂.1
  · simp only [σ', vars_setVar, if_neg (by decide : ¬ ("mn" = "kd"))]
    exact hQ₂.2.1
  · intro a haIO haIT
    exact rAll.frame_arr a (by
      simp [roundRelinkCom, copyUpto, fillUpto, Fill.put, Com.warrs, haIO, haIT])

/-! ## Axioms -/

#print axioms roundRelink_spec

end Lax3Proofs.Refine.OrderActiveRound
