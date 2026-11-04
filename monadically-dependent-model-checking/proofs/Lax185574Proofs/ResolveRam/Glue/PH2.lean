import Lax185574Proofs.ResolveRam.Glue.PH4

/-!
The run of the tape program of the resolved graph (`hIn_run`): from the
input of the composite it writes the word of `resolveBy G s P Q` and the
word of its distance matrix, by eq:resolve-dist from the distance matrix
of `G` (`dhWord_eq`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax185574Proofs.StpRam Lax185574.PartialGraphs Lax185574.WordEncoding Lax185574Proofs.ResolveRam
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift

variable {n : ℕ}

/-- The entries of the edges after the resolve. -/
def eEd : Expr := rsE "E" "N" (.var "gs")

/-- The entries of the non-edges after the resolve. -/
def eNe : Expr := rsE "N" "E" (notX (.var "gs"))

theorem size_eEd : 6 + eEd.size ≤ 270 := by decide

theorem size_eNe : 6 + eNe.size ≤ 270 := by decide

theorem writeGraph_warrs : writeGraph.warrs = [] := by decide

/-- Fill `Rm` and write it as a graph. -/
def fillW (e : Expr) : Com := .seq (matFill "Rm" e) writeGraph

open Classical in
theorem fillW_run {B P Q g : ℕ} {M₁ M₂ : String} {sg : Expr} {col : ℕ → ℕ} {R₁ R₂ N' : ℕ → ℕ → Prop}
    {S : Prop} {σ : Env} (hM₁ : M₁ ≠ "Rm") (hM₂ : M₂ ≠ "Rm") (hsz : 6 + (rsE M₁ M₂ sg).size ≤ 270)
    (hn : σ.vars "n" = n) (h₁ : Mat σ M₁ n fun u v => ind (R₁ u v)) (h₂ : Mat σ M₂ n fun u v => ind (R₂ u v))
    (hco : σ.arrs "co" = arrOf n col) (hP : σ.vars "gp" = P) (hQ : σ.vars "gq" = Q)
    (hg : σ.vars "gs" = g) (hsg : ∀ τ : Env, τ.vars "gs" = g → sg.evalB B τ = some (ind S))
    (hRm : (σ.arrs "Rm").length = n * n) (hB : n * n + n + 3 < B) (hcol : ∀ v < n, col v < B)
    (hPB : P < B) (hQB : Q < B)
    (hN : ∀ i < n, ∀ j < n, (R₁ i j ∨ (S ∧ ¬ i = j ∧ ((col i = P ∧ col j = Q) ∨ (col j = P ∧ col i = Q)) ∧
      ¬ R₂ i j)) ↔ N' i j) :
    ∃ σ', Run B (fillW (rsE M₁ M₂ sg)) σ σ' (n * (n * 278 + 14) + 6 + 100 * (n + 1) ^ 2) ∧
      σ'.out = σ.out ++ graphWord n N' ∧ (∀ a, a ≠ "Rm" → σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ∉ (fillW (rsE M₁ M₂ sg)).wvars → σ'.vars x = σ.vars x) := by
  let C : Env → Prop := fun τ => τ.vars "n" = n ∧ τ.vars "gp" = P ∧ τ.vars "gq" = Q ∧ τ.vars "gs" = g ∧
    (∀ a, a ≠ "Rm" → τ.arrs a = σ.arrs a)
  have hC : ∀ τ x v, C τ → x ∈ ["a", "b"] → C (τ.setVar x v) := by
    intro τ x v h hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
      fun a ha => by simp [h.2.2.2.2 a ha]⟩
  obtain ⟨σ1, r1, hC1, hm1⟩ := matFill_run (B := B) (n := n) (K := 270) (arr := "Rm") (e := rsE M₁ M₂ sg) C
    (fun i j => ind (R₁ i j ∨ (S ∧ ¬ i = j ∧ ((col i = P ∧ col j = Q) ∨ (col j = P ∧ col i = Q)) ∧ ¬ R₂ i j)))
    (by omega) (fun τ h => h.1) (fun τ x h => hC τ "a" x h (by simp)) (fun τ x h => hC τ "b" x h (by simp))
    (fun τ i x h => ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
      fun a ha => by simp [ha, h.2.2.2.2 a ha]⟩)
    (fun τ i j h ha hb hi hj => rsE_evalB ha hb h.1 hi hj (h₁.of_eq (h.2.2.2.2 _ hM₁))
      (h₂.of_eq (h.2.2.2.2 _ hM₂)) (by rw [h.2.2.2.2 _ (by decide), hco]) h.2.1 h.2.2.1 (hsg τ h.2.2.2.1) hB
      hcol hPB hQB)
    hsz (σ := σ) ⟨hn, hP, hQ, hg, fun _ _ => rfl⟩ hRm
  have hgc : GraphCtx n N' σ1 := ⟨hC1.1, hm1.congr fun i hi j hj => by rw [ind_eq_iff]; exact hN i hi j hj⟩
  obtain ⟨σ2, r2, -, ho2⟩ := writeGraph_run (B := B) hgc (by omega)
  have hrun : Run B (fillW (rsE M₁ M₂ sg)) σ σ2 (n * (n * 278 + 14) + 6 + 100 * (n + 1) ^ 2) :=
    Run.seq r1 r2
  refine ⟨σ2, hrun, ?_, fun a ha => ?_, fun x hx => hrun.frame_var x hx⟩
  · rw [ho2, r1.out_eq (by simp [matFill, rowFill, forUp, Com.NoWrite])]
  · rw [r2.frame_arr a (by rw [writeGraph_warrs]; simp), hC1.2.2.2.2 a ha]

/-- The distance matrix of the resolved graph: the distances to the
classes of `P` and `Q`, whether these classes have a vertex, and the
entries. -/
def dhOut : Com :=
  .seq (dtLoop "dp" "gp") (.seq (dtLoop "dq" "gq") (.seq (flgLoop "hp" "gp") (.seq (flgLoop "hq" "gq") dhW)))

/-- **The resolved graph as a tape program.** -/
def hIn : Com :=
  .seq (.read "n") (.seq (.write (.var "n")) (.seq rdCoW (.seq (rdG "E") (.seq (rdG "N") (.seq rdD
    (.seq (.read "gp") (.seq (.read "gq") (.seq (.read "gs") (.seq (fillW eEd) (.seq (fillW eNe)
      dhOut))))))))))

theorem ind_sign (s : Bool) : (if s then 1 else 0) = ind (s = true) := by
  cases s <;> simp [ind]

theorem dtVal_le {n X : ℕ} (G : PartialGraph (Fin n)) (u : ℕ) : dtVal (colN G) (dF G) n X u ≤ n :=
  cmPre_le fun x _ => by split_ifs <;> [exact dF_le G u x; omega]

open Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix in
set_option maxHeartbeats 1600000 in
/-- **The run of the program of the resolved graph.** -/
theorem hIn_run {B k₀ q₀ P Q : ℕ} {s : Bool} (G : PartialGraph (Fin n)) {σ : Env}
    (hinp : σ.inp = xIn G k₀ q₀ P Q s) (hco : (σ.arrs "co").length = n)
    (hE : (σ.arrs "E").length = n * n) (hN : (σ.arrs "N").length = n * n)
    (hRm : (σ.arrs "Rm").length = n * n) (hdd : (σ.arrs "dd").length = 1 + n * (n + 1))
    (hdp : (σ.arrs "dp").length = n) (hdq : (σ.arrs "dq").length = n)
    (hB : ySz (xIn G k₀ q₀ P Q s) * ySz (xIn G k₀ q₀ P Q s) < B) :
    ∃ σ', Run B hIn σ σ' (3000 * ((xIn G k₀ q₀ P Q s).length + 1)) ∧
      σ'.out = σ.out ++ (toWord (resolveBy G s P Q) ++ toWord (distMatrix (resolveBy G s P Q))) := by
  set Dw := toWord (distMatrix G) with hDw
  have hDl : Dw.length = 1 + n * (n + 1) := length_toWord_distMatrix G
  have hinp' : σ.inp = n :: (List.ofFn G.color ++ (toWord G.edge ++ (toWord G.nonEdge ++
      (Dw ++ ([P, Q, if s then 1 else 0] ++ toWord (family G k₀ q₀)))))) := by
    rw [hinp, toWord_xIn, toWord_ofFn_append]; simp [Dw]
  obtain ⟨hmc, hmP, hmQ⟩ := xIn_mem (G := G) (k₀ := k₀) (q₀ := q₀) (P := P) (Q := Q) (s := s)
  have hlen : n + 1 + StpRam.offL G.edge n + StpRam.offL G.nonEdge n + (1 + n * (n + 1)) + 2 ≤
      (xIn G k₀ q₀ P Q s).length := xIn_len
  have hyS : (xIn G k₀ q₀ P Q s).length + maxEntry (xIn G k₀ q₀ P Q s) + 1 = ySz (xIn G k₀ q₀ P Q s) := rfl
  have hyy : ySz (xIn G k₀ q₀ P Q s) ≤ ySz (xIn G k₀ q₀ P Q s) * ySz (xIn G k₀ q₀ P Q s) :=
    Nat.le_mul_self _
  have hcB : ∀ v < n, colN G v < B := fun v hv => by
    have := le_maxEntry (hmc v hv); omega
  have hPB : P < B := by have := le_maxEntry hmP; omega
  have hQB : Q < B := by have := le_maxEntry hmQ; omega
  have h1 : n + 2 ≤ ySz (xIn G k₀ q₀ P Q s) := by omega
  have h2 := Nat.mul_le_mul h1 h1
  have hsq : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
  have hn3 : n * n + n + 3 < B := by omega
  have hDB : Dw.length < B := by
    have : n * (n + 1) = n * n + n := by ring
    omega
  have hnB : n + 1 < B := by omega
  have h3B : 3 * n + 3 < B := by omega
  clear h1 h2 hsq
  clear hmc hmP hmQ hyS hyy
  -- the head
  set σ1 : Env := { σ.setVar "n" n with inp := List.ofFn G.color ++ (toWord G.edge ++ (toWord G.nonEdge ++
      (Dw ++ ([P, Q, if s then 1 else 0] ++ toWord (family G k₀ q₀))))) }
  have r1 : Run B (.read "n") σ σ1 1 := Run.read hinp'
  set σ2 : Env := { σ1 with out := σ1.out ++ [n] }
  have r2 : Run B (.write (.var "n")) σ1 σ2 2 := (Run.write (by simp [σ1]; omega)).mono (by simp)
  obtain ⟨σ3, r3, hin3, hco3, hv3, ha3, ho3⟩ := rdCoW_run (B := B) G (σ := σ2) rfl (by simp [σ2, σ1])
    (by simp [σ2, σ1, hco]) (by omega) hcB
  -- the matrices
  obtain ⟨σ4, r4, hin4, hm4, ha4, hv4, ho4⟩ := rdG_run (B := B) G.edge (arr := "E") (σ := σ3) hin3
    (by rw [hv3 "n" (by decide)]; simp [σ2, σ1]) (by rw [ha3 "E" (by decide)]; simp [σ2, σ1, hE]) (by omega)
  obtain ⟨σ5, r5, hin5, hm5, ha5, hv5, ho5⟩ := rdG_run (B := B) G.nonEdge (arr := "N") (σ := σ4) hin4
    (by rw [hv4 "n" (by decide), hv3 "n" (by decide)]; simp [σ2, σ1])
    (by rw [ha4 "N" (by decide), ha3 "N" (by decide)]; simp [σ2, σ1, hN]) (by omega)
  have hn5 : σ5.vars "n" = n := by
    rw [hv5 "n" (by decide), hv4 "n" (by decide), hv3 "n" (by decide)]; simp [σ2, σ1]
  -- the distance matrix of `G`
  obtain ⟨σD, rD, hinD, hddD, hvD, haD, hoD⟩ := rdD_run (B := B) (n := n) (L := Dw)
    (rest := [P, Q, if s then 1 else 0] ++ toWord (family G k₀ q₀)) (σ := σ5) hin5 hn5 (by rw [hDl]; ring)
    (by rw [ha5 "dd" (by decide), ha4 "dd" (by decide), ha3 "dd" (by decide)]; simp [σ2, σ1, hdd, hDl])
    hDB (fun v hv => by have := toWord_distMatrix_le G v hv; omega)
  have hnD : σD.vars "n" = n := by rw [hvD "n" (by decide), hn5]
  -- the numbers
  set σ6 : Env := { σD.setVar "gp" P with inp := [Q, if s then 1 else 0] ++ toWord (family G k₀ q₀) }
  have r6 : Run B (.read "gp") σD σ6 1 := Run.read (by rw [hinD]; rfl)
  set σ7 : Env := { σ6.setVar "gq" Q with inp := [if s then 1 else 0] ++ toWord (family G k₀ q₀) }
  have r7 : Run B (.read "gq") σ6 σ7 1 := Run.read rfl
  set σ8 : Env := { σ7.setVar "gs" (if s then 1 else 0) with inp := toWord (family G k₀ q₀) }
  have r8 : Run B (.read "gs") σ7 σ8 1 := Run.read rfl
  have hE8 : Mat σ8 "E" n fun u v => ind (Conversions.Ram.gA G.edge u v) :=
    hm4.of_eq (by simp [σ8, σ7, σ6, haD "E" (by decide), ha5 "E" (by decide)])
  have hN8 : Mat σ8 "N" n fun u v => ind (Conversions.Ram.gA G.nonEdge u v) :=
    hm5.of_eq (by simp [σ8, σ7, σ6, haD "N" (by decide)])
  have hco8 : σ8.arrs "co" = arrOf n (colN G) := by
    simp [σ8, σ7, σ6, haD "co" (by decide), ha5 "co" (by decide), ha4 "co" (by decide), hco3]
  have hRm8 : (σ8.arrs "Rm").length = n * n := by
    simp [σ8, σ7, σ6, haD "Rm" (by decide), ha5 "Rm" (by decide), ha4 "Rm" (by decide),
      ha3 "Rm" (by decide), σ2, σ1, hRm]
  -- the edges
  obtain ⟨σ9, r9, ho9, ha9, hv9⟩ := fillW_run (B := B) (P := P) (Q := Q) (g := if s then 1 else 0)
    (M₁ := "E") (M₂ := "N") (sg := .var "gs") (col := colN G) (S := s = true)
    (N' := edgeR G s P Q) (σ := σ8) (by decide) (by decide) size_eEd (by simp [σ8, σ7, σ6, hnD]) hE8 hN8
    hco8 (by simp [σ8, σ7, σ6]) (by simp [σ8, σ7]) (by simp [σ8])
    (fun τ h => by rw [evalB_var_iff, h, ind_sign]; exact ⟨rfl, by unfold ind; split_ifs <;> omega⟩)
    hRm8 hn3 hcB hPB hQB
    (fun i hi j hj => by unfold edgeR btw; simp only [hi, hj, true_and]; tauto)
  -- the non-edges
  obtain ⟨σ10, r10, ho10, ha10, hv10⟩ := fillW_run (B := B) (P := P) (Q := Q) (g := if s then 1 else 0)
    (M₁ := "N") (M₂ := "E") (sg := notX (.var "gs")) (col := colN G) (S := ¬ s = true)
    (N' := nonEdgeR G s P Q) (σ := σ9) (by decide) (by decide) size_eNe
    (by rw [hv9 "n" (by decide)]; simp [σ8, σ7, σ6, hnD]) (hN8.of_eq (ha9 _ (by decide)))
    (hE8.of_eq (ha9 _ (by decide))) (by rw [ha9 _ (by decide), hco8])
    (by rw [hv9 "gp" (by decide)]; simp [σ8, σ7, σ6]) (by rw [hv9 "gq" (by decide)]; simp [σ8, σ7])
    (by rw [hv9 "gs" (by decide)]; simp [σ8])
    (fun τ h => notX_evalB (by rw [evalB_var_iff, h, ind_sign]; exact ⟨rfl, by unfold ind; split_ifs <;> omega⟩)
      (by omega))
    (by rw [run_len_eq r9]; exact hRm8) hn3 hcB hPB hQB
    (fun i hi j hj => by unfold nonEdgeR btw; simp only [hi, hj, true_and, Bool.not_eq_true]; tauto)
  -- the distances to the classes
  have hl10 : ∀ a, a ∉ ["co", "E", "N", "Rm", "dd"] → (σ10.arrs a).length = (σ.arrs a).length := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    rw [ha10 a ha.2.2.2.1, ha9 a ha.2.2.2.1]
    simp [σ8, σ7, σ6, haD a ha.2.2.2.2, ha5 a ha.2.2.1, ha4 a ha.2.1, ha3 a ha.1, σ2, σ1]
  have hC10 : DtCtx "gp" n P (colN G) Dw σ10 :=
    ⟨by rw [hv10 "n" (by decide), hv9 "n" (by decide)]; simp [σ8, σ7, σ6, hnD],
      by rw [hv10 "gp" (by decide), hv9 "gp" (by decide)]; simp [σ8, σ7, σ6],
      by rw [ha10 "co" (by decide), ha9 "co" (by decide), hco8],
      by rw [ha10 "dd" (by decide), ha9 "dd" (by decide)]; simp [σ8, σ7, σ6, hddD]⟩
  have hfB : ∀ u < n, ∀ x < n, dF G u x < B := fun u _ x _ => by have := dF_le G u x; omega
  obtain ⟨σ11, r11, hC11, hp11⟩ := dtLoop_run (B := B) (dst := "dp") (Xv := "gp") (f := dF G) (by decide)
    (by decide) hC10 (fun u hu x hx => getElem?_dF G hu hx) hfB hcB hPB hDB hnB
    (by rw [hl10 "dp" (by decide), hdp])
  have hC11' : DtCtx "gq" n Q (colN G) Dw σ11 :=
    ⟨hC11.vn, by rw [r11.frame_var "gq" (by decide), hv10 "gq" (by decide), hv9 "gq" (by decide)]; simp [σ8, σ7],
      hC11.aco, hC11.add⟩
  obtain ⟨σ12, r12, hC12, hq12⟩ := dtLoop_run (B := B) (dst := "dq") (Xv := "gq") (f := dF G) (by decide)
    (by decide) hC11' (fun u hu x hx => getElem?_dF G hu hx) hfB hcB hQB hDB hnB
    (by rw [r11.frame_arr "dq" (by decide), hl10 "dq" (by decide), hdq])
  obtain ⟨σ13, r13, hf13, hv13, ha13, ho13, -⟩ := flgLoop_run (B := B) (dst := "hp") (Xv := "gp") (by decide)
    (by decide) hC12.vn (by rw [r12.frame_var "gp" (by decide), hC11.vx]) hC12.aco hcB hPB hnB
  obtain ⟨σ14, r14, hf14, hv14, ha14, ho14, -⟩ := flgLoop_run (B := B) (dst := "hq") (Xv := "gq") (by decide)
    (by decide) (by rw [hv13 "n" (by decide), hC12.vn]) (by rw [hv13 "gq" (by decide), hC12.vx])
    (by rw [ha13, hC12.aco]) hcB hQB hnB
  have hC14 : DhCtx n (dtVal (colN G) (dF G) n P) (dtVal (colN G) (dF G) n Q) (flg G P) (flg G Q) Dw σ14 :=
    ⟨by rw [hv14 "n" (by decide), hv13 "n" (by decide), hC12.vn],
      by rw [hv14 "hp" (by decide), hf13]; rfl, by rw [hf14]; rfl,
      by rw [ha14, ha13, r12.frame_arr "dp" (by decide), hp11],
      by rw [ha14, ha13, hq12], by rw [ha14, ha13, hC12.add]⟩
  obtain ⟨σ15, r15, ho15, -⟩ := dhW_run (B := B) (f := dF G) hC14 (fun u hu x hx => getElem?_dF G hu hx)
    (fun u _ x _ => dF_le G u x) (fun v _ => dtVal_le G v) (fun v _ => dtVal_le G v) (flg_le G P)
    (flg_le G Q) hDB h3B
  refine ⟨σ15, ?_, ?_⟩
  · unfold hIn dhOut
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq rD (Run.seq r6 (Run.seq r7
      (Run.seq r8 (Run.seq r9 (Run.seq r10 (Run.seq r11 (Run.seq r12 (Run.seq r13
        (Run.seq r14 r15))))))))))))))).mono ?_
    generalize (xIn G k₀ q₀ P Q s).length = X at hlen
    rw [hDl]
    have h0 : n * n ≤ n * (n + 1) := Nat.mul_le_mul_left n (Nat.le_succ n)
    have h1 : n * n ≤ X := by omega
    have h2 : n ≤ X := by omega
    clear * - h1 h2
    ring_nf
    ring_nf at h1
    omega
  · rw [ho15, ho14, ho13, r12.out_eq (by decide), r11.out_eq (by decide), ho10, ho9, dhWord_eq G s P Q,
      toWord_resolve]
    simp only [σ8, σ7, σ6, hoD, ho5, ho4, ho3, σ2, σ1, out_setVar, List.append_assoc, List.cons_append,
      List.nil_append]

end Lax185574Proofs.ResolveRam.Glue
