import Lax185574Proofs.EvalRam.Prog

/-!
The run of the evaluation program: the reading phase, the table, and the
answer.
-/

namespace Lax185574Proofs.EvalRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

theorem mem_pad {u : List ℕ} {m v : ℕ} (h : v ∈ u ++ (List.replicate m 0).drop u.length) :
    v ∈ u ∨ v = 0 := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · rw [List.drop_replicate] at h; exact Or.inr (List.eq_of_mem_replicate h)

set_option maxHeartbeats 1000000 in
/-- **The run of the evaluation program.** On the word of a type tree
followed by the code of a formula of the same arity, `prog` writes the
value of the semantic core `evalNode`. -/
theorem prog_run (k q ℓ : ℕ) (t : Node q ℓ) (φ : DistFO ℓ) :
    ∃ σ', Run (valBound 8 2 (inWord k q ℓ t φ)) prog
      (initEnv (evalExt (inWord k q ℓ t φ).length) (inWord k q ℓ t φ)) σ'
      (2000 * ((inWord k q ℓ t φ).length + 1) ^ 3) ∧
      σ'.out = [bv (evalNode t φ)] := by
  obtain ⟨σ3, hr3, hR⟩ := readPhase_run k q ℓ t φ
  set x := inWord k q ℓ t φ with hxdef
  obtain ⟨n, hn⟩ : ∃ n, x.length = n := ⟨_, rfl⟩
  have hR' := hR
  obtain ⟨hx3, hf3, hq3, hfl3, hen3, hval3, hout3, hNX, hN0, hr03, hd03, hpl3, hdl3, hfl3', hnodes⟩ := hR'
  rw [hn] at hr3 hx3 hf3 hen3 hval3 hNX hpl3 hdl3 hfl3' hnodes ⊢
  set B := valBound 8 2 x with hB
  set M := maxEntry x with hM
  have hBdef : B = 8 * (x.length + M + 1) ^ 2 := rfl
  rw [hn] at hBdef
  have hmem : ∀ v ∈ x, v < B := fun v hv => by
    have := le_maxEntry hv; rw [hBdef]; nlinarith
  have htl : (toWord t).length + (code φ).length + 3 = n := by rw [← hn, hxdef]; simp [inWord] <;> omega
  have hL1 := one_le_code_length φ
  have hBn : (n + 5) * (n + 2) + 10 < B := by rw [hBdef]; nlinarith
  have hnB : n + 10 < B := by nlinarith
  have hqB : q < B := hmem q (by simp [hxdef, inWord])
  set X := xArr t n with hX
  set F := fArr φ n with hF
  set L := (code φ).length with hL
  set N := σ3.vars "nn" with hN
  set PA := σ3.arrs "pos" with hPA
  set DA := σ3.arrs "dep" with hDA
  set FA := σ3.arrs "fc" with hFA
  have hXl : X.length = n + 1 := by simp [hX, xArr]; omega
  have hFl : F.length = n + 5 := by simp [hF, fArr]; omega
  have hXv : ∀ v ∈ X, v < B := fun v hv => by
    rcases mem_pad hv with h | h
    · exact hmem v (by simp [hxdef, inWord, h])
    · omega
  have hFv : ∀ v ∈ F, v < B := fun v hv => by
    rcases mem_pad hv with h | h
    · exact hmem v (by simp [hxdef, inWord, h])
    · omega
  have hXt : X.drop 0 = toWord t ++ (List.replicate (n + 1) 0).drop (toWord t).length := by
    simp [hX, xArr]
  set EN := List.replicate (n + 5) 0 with hEN
  set VL := List.replicate ((n + 5) * (n + 2)) 0 with hVL
  have hC : Ctx B X F PA DA FA EN VL q N L :=
    { hX := hXv, hF := hFv, hV := fun v h => by rw [List.eq_of_mem_replicate h]; omega,
      hEN := fun v h => by rw [List.eq_of_mem_replicate h]; omega, hXB := by omega,
      hFL := by omega, hFB := by omega, hENl := by simp [hEN]; omega,
      hVL := by simp [hVL]; exact Nat.mul_le_mul (by omega) (by omega),
      hVB := by simp [hVL]; omega, hPA := by omega, hDA := by omega, hFA := by omega, hqB := hqB,
      hLB := by omega, h9 := by omega }
  obtain ⟨σ4, hr4, hI4⟩ := dpCmd_spec B X F PA DA FA q N L (by omega) hnodes (by omega) σ3
    ⟨by simp [hx3], by simp [hf3], by simp [hPA], by simp [hDA], by simp [hFA], by simp [hq3],
      by simp [hN], by simp [hfl3], EN, VL, by simp [hen3], by simp [hval3], hC,
      fun p hp hpL => by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, ENf, VLf, -, hvl4, hC4, hR4⟩ := hI4
  rw [Nat.sub_self] at hR4
  have hF0 : F.drop 0 = code φ ++ (List.replicate (n + 5) 0).drop L := by rw [List.drop_zero, hF, fArr]
  obtain ⟨-, hval⟩ := hR4 0 le_rfl (by omega) ℓ φ _ hF0 (by omega)
  have h00 := hval 0 hN0
  rw [Nat.zero_mul, Nat.zero_add, show xg PA 0 = 0 from hr03, show xg DA 0 = 0 from hd03,
    Nat.sub_zero, evalW_eq X φ t 0 _ hXt] at h00
  have hVL0 : 0 < VLf.length := by have := hC4.hVL; nlinarith
  have hout4 : σ4.out = [] := by rw [hr4.out_eq dpCmd_noWrite, hout3]
  refine ⟨{ σ4 with out := σ4.out ++ [bv (evalNode t φ)] }, ?_, by simp [hout4]⟩
  unfold prog
  refine (Run.seq hr3 (Run.seq hr4 (Run.write ?_))).mono ?_
  · simp only [evalB_get_iff, evalB_lit_iff]
    refine ⟨0, ⟨rfl, by omega⟩, ?_, by have := bv_le (evalNode t φ); omega⟩
    rw [hvl4, List.getElem?_eq_getElem hVL0, ← h00]
    simp [xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hVL0]
  · simp only [Expr.size, hXl]
    have h1 : L ≤ n := by omega
    have h3 : N * (100 * (n + 1) + 208) ≤ (n + 2) * (308 * (n + 1)) :=
      Nat.mul_le_mul hNX (by omega)
    have h4 : L * ((n + 2) * (308 * (n + 1)) + 88) ≤ n * ((n + 2) * (308 * (n + 1)) + 88) :=
      Nat.mul_le_mul_right _ h1
    have h5 : L * (N * (100 * (n + 1) + 208) + 88) ≤ L * ((n + 2) * (308 * (n + 1)) + 88) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right h3 _)
    nlinarith

end Lax185574Proofs.EvalRam
