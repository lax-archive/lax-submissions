import Lax185574Proofs.MainRam.ValidProg

/-!
The validation program: the checks after the shape check, run in a row.
The flag ends at `1` exactly when all checks pass.
-/

namespace Lax185574Proofs.MainRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax271696.GraphEncoding Lax185574Proofs.Compose
open Classical

theorem mat_of_arrOf {σ : Env} {arr : String} {n : ℕ} {f : ℕ → ℕ → ℕ}
    (h : σ.arrs arr = arrOf (n * n) (fun i => f (i / n) (i % n))) : Mat σ arr n f := by
  refine ⟨by rw [h]; simp, fun i hi j hj => ?_⟩
  rw [h, getElem?_arrOf _ (rowMajor_lt hi hj)]
  obtain ⟨h1, h2⟩ := div_mod_rm (N := n) (u := i) hj
  rw [h1, h2]

set_option maxHeartbeats 1000000 in
theorem restPh_run {B Λ : ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {g y : List ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = numSteps n y) (hY : σ.arrs "Y" = y)
    (hcol : (σ.arrs "col").length = n) (hc2 : (σ.arrs "c2").length = n)
    (hS : σ.arrs "S" = arrOf (n * n) (fun _ => 0)) (hS2 : (σ.arrs "S2").length = n * n)
    (hA : σ.arrs "A" = arrOf (n * n) (fun i =>
      if InBlock (fun i => (ofL g n).getD i 0) (fun j => (tgL g n).getD j 0) (i / n) (i % n)
      then 1 else 0))
    (hok : σ.vars "ok" = 1) (hshape : Shape n y)
    (hyΛ : ∀ a ∈ y, a ≤ Λ) (hlΛ : y.length ≤ Λ) (hnΛ : n * n + n ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ σ', Run B restPh σ σ' (y.length * (n * (n * 120 + 108) + 160) +
        n * (n * 400 + 100) + 100) ∧
      σ'.vars "ok" = (if Checks G g y then 1 else 0) := by
  set M := numSteps n y
  have hlen : y.length = n + 2 + 3 * M := hshape.2
  have hM : M ≤ y.length := by omega
  -- opcodes
  obtain ⟨σ1, r1, fr1, ok1⟩ := opPh_run (B := B) (Λ := Λ) hn hm hY hyΛ (by omega) hlΛ hB
  have hn1 : σ1.vars "n" = n := by rw [fr1.var (by decide), hn]
  -- colors
  obtain ⟨σ2, r2, hv2, fv2, fa2, -, -⟩ := colPh_run (B := B) (Λ := Λ) hn1 (by rw [fr1.arr, hY])
    (by rw [fr1.arr, hcol]) hyΛ (by omega) hlΛ hB
  have hn2 : σ2.vars "n" = n := by rw [fv2 _ (by decide), hn1]
  have hok2 : σ2.vars "ok" = σ1.vars "ok" := fv2 _ (by decide)
  -- injectivity
  obtain ⟨σ3, r3, fr3, ok3⟩ := injPh_run (B := B) (Λ := Λ) (c := fun v => y.getD (v + 1) 0) hn2
    hv2 (fun v _ => getD_le hyΛ _) (by nlinarith) hB
  have hn3 : σ3.vars "n" = n := by rw [fr3.var (by decide), hn2]
  have hm3 : σ3.vars "m" = M := by
    rw [fr3.var (by decide), fv2 _ (by decide), fr1.var (by decide), hm]
  -- the steps
  have hS3 : Mat σ3 "S" n (simInit y).st := by
    apply mat_of_arrOf
    rw [fr3.arr, fa2 _ (by decide), fr1.arr, hS]; rfl
  obtain ⟨σ4, r4, hc4, hS4, fv4, fa4, -, -⟩ := stepPh_run (B := B) (Λ := Λ) hn3 hm3
    (by rw [fr3.arr, fa2 _ (by decide), fr1.arr, hY]) (hv2.of_eq (by rw [fr3.arr])) hS3
    (by rw [fr3.arr, fa2 _ (by decide), fr1.arr, hc2])
    (by rw [fr3.arr, fa2 _ (by decide), fr1.arr, hS2]) hyΛ (by omega) hlΛ hnΛ hB
  have hn4 : σ4.vars "n" = n := by rw [fv4 _ (by decide), hn3]
  have hbnd := simFold_le (n := n) hyΛ M
  -- final colors
  obtain ⟨σ5, r5, fr5, ok5⟩ := finColPh_run (B := B) (Λ := Λ) hn4 hc4
    (fun v _ => hbnd.1 v) (by nlinarith) hB
  have hn5 : σ5.vars "n" = n := by rw [fr5.var (by decide), hn4]
  -- final statuses
  have hA5 : Mat σ5 "A" n (fun u v => ind (InBlock (fun i => (ofL g n).getD i 0)
      (fun j => (tgL g n).getD j 0) u v)) := by
    apply mat_of_arrOf
    rw [fr5.arr, fa4 _ (by decide), fr3.arr, fa2 _ (by decide), fr1.arr, hA]
    rfl
  obtain ⟨σ6, r6, fr6, ok6⟩ := finMatPh_run (B := B) (Λ := Λ) hn5 (hS4.of_eq (by rw [fr5.arr]))
    hA5 (fun u _ v _ => hbnd.2 u v) hnΛ hB
  refine ⟨σ6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_, ?_⟩
  · have : n * (n * 70 + 14) ≤ n * (n * 400 + 100) := Nat.mul_le_mul_left _ (by omega)
    have : n * (n * 120 + 14) ≤ n * (n * 400 + 100) := Nat.mul_le_mul_left _ (by omega)
    have : M * (n * (n * 120 + 108) + 120) ≤ y.length * (n * (n * 120 + 108) + 160) :=
      Nat.mul_le_mul hM (by omega)
    nlinarith
  · rw [ok6, ok5, fv4 "ok" (by decide), ok3, hok2, ok1, hok]
    unfold Checks
    split_ifs <;> first | rfl | (exfalso; tauto)

end Lax185574Proofs.MainRam
