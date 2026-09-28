import Lax235315Proofs.Construction.WelzlSetup
import Lax235315Proofs.Construction.RadixEight
import Lax235315.ConstructionContracts
import Mathlib.Tactic

/-! The complete deterministic setup, with canonical CSR arrays and workspace
sizes, stated in the same word bound as the public construction contracts. -/

namespace Lax235315Proofs.Construction.DriverSetup

open Lax11.GraphEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.Construction.RadixEight
open Lax235315.ConstructionContracts

/-- The fixed graph data and correctly sized workspace available after setup. -/
structure Ready (c n : ℕ) (x bits : List ℕ) (σ : Env) : Prop where
  parameter : σ.vars "c" = c
  vertices : σ.vars "n" = n
  edges : σ.vars "m" = edgeCount x
  logarithm : σ.vars "L" = Nat.clog 2 n
  radixSize : σ.vars "qpow" = 2 ^ Nat.clog 2 n
  activeCount : σ.vars "acount" = n
  success : σ.vars "good" = 1
  round : σ.vars "round" = 0
  removedCount : σ.vars "removedCount" = 0
  offsets : σ.arrs "off" = arrOf (n + 1) (offset x)
  targets : σ.arrs "tgt" = arrOf (2 * edgeCount x) (target x)
  activeA : σ.arrs "activeA" = arrOf n (fun _ => 1)
  activeB : σ.arrs "activeB" = arrOf n (fun _ => 1)
  lengths : ∀ a, (σ.arrs a).length =
    welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a
  input : σ.inp = bits
  output : σ.out = []

/-- Binary rounding needs fewer than twice n+1 radix buckets, even for n=0. -/
lemma radix_size_lt (n : ℕ) : 2 ^ Nat.clog 2 n < 2 * (n + 1) := by
  by_cases hn : n ≤ 1
  · rw [Nat.clog_of_right_le_one hn]
    simp
    omega
  · have hn' : 1 < n := by omega
    have hpos : 0 < Nat.clog 2 n :=
      (Nat.lt_clog_iff_pow_lt (by decide)).2 (by simpa using hn')
    have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by decide) hn'
    simp only [Nat.pred_eq_sub_one] at hpred
    rw [show Nat.clog 2 n = Nat.clog 2 n - 1 + 1 by omega, pow_succ]
    omega

/-- A coarse linear bound suffices for the loop counter representing log n. -/
lemma clog_le_vertices (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide)))

/-- Compose CSR reading and initialization without consuming the random suffix. -/
lemma setup_run {B c n : ℕ} {G : SimpleGraph (Fin n)} {x bits : List ℕ}
    (hx : EncodesGraph x n G) (hB : 4 * (x.length + 1) ≤ B) :
    ∃ σ, Run B setup
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) ((c :: x) ++ bits))
      σ (40 * (x.length + Nat.clog 2 n + 1)) ∧ Ready c n x bits σ := by
  have hlen := hx.length_eq
  have hpowB : 2 ^ Nat.clog 2 n < B := by
    have hq := radix_size_lt n
    omega
  have hlogB : Nat.clog 2 n + 1 < B := by
    have hL := clog_le_vertices n
    omega
  obtain ⟨m, ys, zs, hm, hsplit, hys, hzs, hO, hT⟩ := encodesGraph_split hx
  obtain ⟨σ₁, O, T, r₁, hc₁, hn₁, hm₁, hoff₁, htgt₁, hOval, hTval, hi₁, ho₁⟩ :=
    readGraph_run (B := B) (c := c) (qpow := 2 ^ Nat.clog 2 n) (bits := bits)
      hx hm hsplit hys hzs hO hT (by omega)
  have ha₁ : σ₁.arrs "activeA" = arrOf n (fun _ => 0) := by
    rw [r₁.frame_arr "activeA" (by decide)]
    simp [initEnv, welzlExt, replicate_eq_arrOf]
  have hb₁ : σ₁.arrs "activeB" = arrOf n (fun _ => 0) := by
    rw [r₁.frame_arr "activeB" (by decide)]
    simp [initEnv, welzlExt, replicate_eq_arrOf]
  obtain ⟨σ₂, A, Bside, r₂, hn₂, hL₂, hq₂, hac₂, hg₂, hr₂, hd₂,
      ha₂, hb₂, hAval, hBval, hoff₂, htgt₂, hi₂, ho₂⟩ :=
    initializeWelzl_run hn₁ ha₁ hb₁ hpowB hlogB (by omega) (by omega)
  have r : Run B setup
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) ((c :: x) ++ bits))
      σ₂ (40 * (x.length + Nat.clog 2 n + 1)) := by
    rw [hm]
    simpa [setup, seqs] using (r₁.seq r₂).mono (by rw [hm] at hlen; omega)
  refine ⟨σ₂, r, ?_⟩
  refine ⟨?_, hn₂, ?_, hL₂, hq₂, hac₂, hg₂, hr₂, hd₂,
    ?_, ?_, ?_, ?_, ?_, hi₂.trans hi₁, ho₂.trans ho₁⟩
  · exact (r₂.frame_var "c" (by decide)).trans hc₁
  · exact (r₂.frame_var "m" (by decide)).trans (hm₁.trans hm.symm)
  · rw [hoff₂, hoff₁]
    exact arrOf_congr hOval
  · rw [htgt₂, htgt₁, hm]
    exact arrOf_congr hTval
  · exact ha₂.trans (arrOf_congr hAval)
  · exact hb₂.trans (arrOf_congr hBval)
  · intro a
    rw [run_array_length_eq r a]
    simp [initEnv]

/-- The registered word-fit condition already pays for deterministic setup. -/
lemma setup_run_of_validInput {K c n w : ℕ} {G : SimpleGraph (Fin n)}
    {x bits : List ℕ} (hK : 4 ≤ K) (hvalid : ValidInput K c n w G x) :
    ∃ σ, Run (2 ^ w) setup
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) ((c :: x) ++ bits))
      σ (40 * (x.length + Nat.clog 2 n + 1)) ∧ Ready c n x bits σ := by
  apply setup_run hvalid.2.2.1
  have hfit := hvalid.2.2.2 c (by simp)
  nlinarith

end Lax235315Proofs.Construction.DriverSetup
