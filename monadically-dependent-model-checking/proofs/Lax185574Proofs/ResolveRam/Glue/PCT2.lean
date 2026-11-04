import Lax185574Proofs.ResolveRam.Glue.PCT1
import Lax185574Proofs.ResolveRam.Glue.DistCmd
import Lax185574Proofs.ResolveRam.Glue.DistRd

/-!
Reading the graph in a tape program, and the classes of the colors.

`ctRdIn` reads the word of the partial graph `G`: the colors into `co`,
the edges and the non-edges in compressed-row form (StpRam `readCsr`),
then the word of the distance matrix into `dd` (`rdD`), and then the two
numbers `P` and `Q` (`ctRdIn_run`). `clsCmd` labels every
vertex by the first vertex of its color (Conversions `classify`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax808846Proofs.Reasoning.Lib.Csr Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax185574Proofs.StpRam Lax185574.PartialGraphs Lax185574.WordEncoding

/-! ### The number of neighbors -/

theorem offL_le_blocks {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∀ k v, v + k = n → StpRam.offL H n ≤ StpRam.offL H v + (blocksFrom H v).length
  | 0, v, h => by subst h; simp
  | k + 1, v, h => by
    have hv : v < n := by omega
    have := offL_le_blocks H k (v + 1) (by omega)
    rw [StpRam.offL_succ] at this
    rw [blocksFrom_succ H hv, List.length_append]
    have : (nbrL H v).length ≤ (vblk (nbrL H v)).length := by
      simp only [vblk, List.length_cons, List.length_flatten, List.map_map]
      have : ∀ l : List ℕ, l.length ≤ (l.map (List.length ∘ fun z => [1, z])).sum := by
        intro l; induction l with
        | nil => simp
        | cons a l ih => simp at ih ⊢; omega
      have := this (nbrL H v); omega
    omega

/-- The number of neighbors is at most the length of the word. -/
theorem offL_le_word {n : ℕ} (H : SimpleGraph (Fin n)) : StpRam.offL H n ≤ (toWord H).length := by
  have := offL_le_blocks H n 0 (by omega)
  have h0 : StpRam.offL H 0 = 0 := by simp [StpRam.offL]
  rw [toWord_graph_blocks, List.length_cons]; omega

/-! ### Reading the input -/

/-- Read the colors into `co`. -/
def rdCo : Com := forUp "v" (.var "n") (.seq (.read "cx") (.store "co" (.var "v") (.var "cx")))

/-- **Read the graph, its distance matrix and `P`, `Q`.** -/
def ctRdIn : Com :=
  .seq (.read "n") (.seq rdCo (.seq (readCsr "eo" "et") (.seq (readCsr "no" "nt")
    (.seq rdD (.seq (.read "gp") (.read "gq"))))))

theorem rdCo_run {B n : ℕ} (G : PartialGraph (Fin n)) {σ : Env} {rest : List ℕ}
    (hinp : σ.inp = List.ofFn G.color ++ rest) (hn : σ.vars "n" = n) (hco : (σ.arrs "co").length = n)
    (hnB : n < B) (hcB : ∀ v < n, colN G v < B) :
    ∃ σ', Run B rdCo σ σ' (n * 17 + 6) ∧ σ'.inp = rest ∧ σ'.arrs "co" = arrOf n (colN G) ∧
      (∀ x, x ∉ ["v", "cx"] → σ'.vars x = σ.vars x) ∧ (∀ a, a ≠ "co" → σ'.arrs a = σ.arrs a) ∧
      σ'.out = σ.out := by
  have hcol : ∀ k (hk : k < n), (List.ofFn G.color)[k]'(by simpa using hk) = colN G k := by
    intro k hk; simp [colN, hk]
  let I : ℕ → Env → Prop := fun k τ => τ.inp = (List.ofFn G.color).drop k ++ rest ∧
    (τ.arrs "co").length = n ∧ (∀ j < k, (τ.arrs "co")[j]? = some (colN G j)) ∧
    (∀ x, x ∉ ["v", "cx"] → τ.vars x = σ.vars x) ∧ (∀ a, a ≠ "co" → τ.arrs a = σ.arrs a) ∧
    τ.out = σ.out
  obtain ⟨σ', r, ⟨h1, h2, h3, h4, h5, h6⟩, -⟩ := forUp_run (B := B) (i := "v") (e := .var "n")
    (body := .seq (.read "cx") (.store "co" (.var "v") (.var "cx"))) (N := n) (K := 9) I (σ := σ) hnB
    (fun k _ τ hI _ => by rw [evalB_var_iff, hI.2.2.2.1 "n" (by decide), hn]; omega)
    ⟨by simp [hinp], by simp [hco], fun j hj => absurd hj (Nat.not_lt_zero _),
      fun x hx => by simp at hx; simp [hx.1], fun a _ => by simp, by simp⟩
    (by
      rintro k hk τ ⟨hin, hl, hg, hv, ha, ho⟩ hvk
      have hkl : k < (List.ofFn G.color).length := by simpa using hk
      have hd : (List.ofFn G.color).drop k = colN G k :: (List.ofFn G.color).drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hkl, hcol k hk]
      set τ1 : Env := { τ.setVar "cx" (colN G k) with inp := (List.ofFn G.color).drop (k + 1) ++ rest }
      have r1 : Run B (.read "cx") τ τ1 1 := Run.read (by rw [hin, hd]; rfl)
      have r2 : Run B (.store "co" (.var "v") (.var "cx")) τ1 (τ1.setArr "co" k (colN G k)) 3 :=
        (Run.store (by simp [τ1, hvk]; omega) (by simp [τ1]; exact hcB k hk) (by simp [τ1, hl, hk])).mono
          (by simp)
      refine ⟨_, (Run.seq r1 r2).mono (by omega), by simp [τ1, hvk], by simp [τ1], by simp [τ1, hl],
        fun j hj => ?_, fun x hx => ?_, fun a ha' => by simp [τ1, ha', ha a ha'], by simp [τ1, ho]⟩
      · simp only [arrs_setVar, arrs_setArr, if_true, τ1]
        rw [List.getElem?_set]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
        · simp [show k ≠ j by omega, hg j h]
        · simp [hl, hk]
      · simp at hx; simp [τ1, hx.1, hx.2, hv x (by simp [hx.1, hx.2])])
  refine ⟨σ', r.mono (by simp only [Expr.size]; omega), by rw [h1, List.drop_eq_nil_of_le (by simp)]; rfl,
    ?_, h4, h5, h6⟩
  refine List.ext_getElem (by rw [h2]; simp) fun j hj _ => ?_
  have := h3 j (by omega)
  rw [List.getElem?_eq_getElem hj] at this
  simp only [Option.some.injEq] at this
  rw [this]; simp [arrOf]

theorem toWord_ofFn_append {n : ℕ} (G : PartialGraph (Fin n)) :
    toWord G = n :: (List.ofFn G.color ++ (toWord G.edge ++ toWord G.nonEdge)) := by
  rw [toWord_pg]; simp

set_option maxHeartbeats 1000000 in
/-- **Reading the graph.** -/
theorem ctRdIn_run {B n P Q : ℕ} (G : PartialGraph (Fin n)) {σ : Env} {rest : List ℕ}
    (hinp : σ.inp = toWord G ++ toWord (Lax185574.DistanceMatrix.distMatrix G) ++ [P, Q] ++ rest)
    (hco : (σ.arrs "co").length = n)
    (heo : (σ.arrs "eo").length = n + 1) (het : (σ.arrs "et").length = StpRam.offL G.edge n)
    (hno : (σ.arrs "no").length = n + 1) (hnt : (σ.arrs "nt").length = StpRam.offL G.nonEdge n)
    (hdd : (σ.arrs "dd").length = 1 + n * (n + 1))
    (hnB : n + 1 < B) (hEB : StpRam.offL G.edge n + 1 < B) (hNB : StpRam.offL G.nonEdge n + 1 < B)
    (hDB : 1 + n * (n + 1) < B) (hcB : ∀ v < n, colN G v < B) :
    ∃ σ', Run B ctRdIn σ σ' (2 * (n * (17 * n + 18) + 12) + 17 * n + 12 +
        ((1 + n * (n + 1)) * 17 + 30)) ∧
      σ'.vars "n" = n ∧ σ'.arrs "co" = arrOf n (colN G) ∧
      σ'.arrs "dd" = toWord (Lax185574.DistanceMatrix.distMatrix G) ∧
      σ'.vars "gp" = P ∧ σ'.vars "gq" = Q ∧ σ'.inp = rest ∧
      σ'.out = σ.out ∧ (∀ a, a ∉ ["co", "eo", "et", "no", "nt", "dd"] → σ'.arrs a = σ.arrs a) := by
  set Dw := toWord (Lax185574.DistanceMatrix.distMatrix G) with hDw
  have hDl : Dw.length = 1 + n * (n + 1) := Lax185574Proofs.DistMatrix.length_toWord_distMatrix G
  rw [toWord_ofFn_append] at hinp
  set σ1 : Env := { σ.setVar "n" n with inp := List.ofFn G.color ++ (toWord G.edge ++ (toWord G.nonEdge ++
    (Dw ++ ([P, Q] ++ rest)))) }
  have r1 : Run B (.read "n") σ σ1 1 := Run.read (by rw [hinp]; simp)
  obtain ⟨σ2, r2, hin2, hco2, hv2, ha2, ho2⟩ := rdCo_run (B := B) G (σ := σ1) rfl (by simp [σ1])
    (by simp [σ1, hco]) (by omega) hcB
  obtain ⟨σ3, r3, hc3, hin3, hcn3⟩ := readCsr_run (B := B) G.edge (o := "eo") (t := "et") (by decide)
    (σ := σ2) hin2 (by rw [ha2 _ (by decide)]; simp [σ1, heo]) (by rw [ha2 _ (by decide)]; simp [σ1, het])
    hnB hEB
  have hf3 : ∀ x, x ∉ (readCsr "eo" "et").warrs → σ3.arrs x = σ2.arrs x := fun x h => r3.frame_arr x h
  obtain ⟨σ4, r4, hc4, hin4, hcn4⟩ := readCsr_run (B := B) G.nonEdge (o := "no") (t := "nt") (by decide)
    (σ := σ3) hin3 (by rw [hf3 _ (by decide), ha2 _ (by decide)]; simp [σ1, hno])
    (by rw [hf3 _ (by decide), ha2 _ (by decide)]; simp [σ1, hnt]) hnB hNB
  have hf4 : ∀ x, x ∉ (readCsr "no" "nt").warrs → σ4.arrs x = σ3.arrs x := fun x h => r4.frame_arr x h
  have hn4 : σ4.vars "n" = n := by
    rw [r4.frame_var "n" (by decide), r3.frame_var "n" (by decide), hv2 "n" (by decide)]; simp [σ1]
  obtain ⟨σD, rD, hinD, hddD, hvD, haD, hoD⟩ := rdD_run (B := B) (n := n) (L := Dw) (rest := [P, Q] ++ rest)
    (σ := σ4) hin4 hn4 (by rw [hDl]; ring) (by
      rw [hf4 _ (by decide), hf3 _ (by decide), ha2 _ (by decide)]; simp [σ1, hdd, hDl]) (by omega)
    (fun v hv => by have := Lax185574Proofs.DistMatrix.toWord_distMatrix_le G v hv; omega)
  set σ5 : Env := { σD.setVar "gp" P with inp := Q :: rest }
  have r5 : Run B (.read "gp") σD σ5 1 := Run.read (by rw [hinD]; simp)
  set σ6 : Env := { σ5.setVar "gq" Q with inp := rest }
  have r6 : Run B (.read "gq") σ5 σ6 1 := Run.read rfl
  have hrun : Run B ctRdIn σ σ6 (2 * (n * (17 * n + 18) + 12) + 17 * n + 12 +
      ((1 + n * (n + 1)) * 17 + 30)) := by
    unfold ctRdIn
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq rD (Run.seq r5 r6)))))).mono ?_
    rw [hDl]; omega
  refine ⟨σ6, hrun, ?_, ?_, ?_, by simp [σ6, σ5], by simp [σ6], by simp [σ6],
    by rw [hrun.out_eq (by decide)], fun a ha => ?_⟩
  · simp [σ6, σ5, hvD "n" (by decide), hn4]
  · simp [σ6, σ5, haD "co" (by decide), hf4 "co" (by decide), hf3 "co" (by decide), hco2]
  · simp [σ6, σ5, hddD]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    simp only [σ6, σ5, arrs_setVar]
    rw [haD a ha.2.2.2.2.2, hf4 a (by simp [readCsr, vtxRd, slotRd, forUp, Com.warrs]; tauto),
      hf3 a (by simp [readCsr, vtxRd, slotRd, forUp, Com.warrs]; tauto), ha2 a ha.1]
    simp [σ1]

/-! ### The classes of the colors -/

/-- The test of `classify`: equal colors. -/
def eqCo : Com :=
  .ite (.eq (.get "co" (.var "u")) (.get "co" (.var "v"))) (.assign "ok" (.lit 1)) (.assign "ok" (.lit 0))

/-- Label every vertex by the first vertex of its color. -/
def clsCmd : Com := classify "cl" eqCo

open Classical in
theorem clsCmd_run {B n : ℕ} {col : ℕ → ℕ} {σ : Env} (hn : σ.vars "n" = n)
    (hco : σ.arrs "co" = arrOf n col) (hcl : (σ.arrs "cl").length = n) (hnB : n + 1 < B)
    (hcB : ∀ v < n, col v < B) :
    ∃ σ', Run B clsCmd σ σ' (n * (n * 30 + 17) + 6) ∧
      σ'.arrs "cl" = arrOf n (fun v => leastBelow (fun u => col u = col v) n n) ∧
      σ'.vars "n" = n ∧ (∀ a, a ≠ "cl" → σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ∉ clsCmd.wvars → σ'.vars x = σ.vars x) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  let Ctx : Env → Prop := fun τ => τ.vars "n" = n ∧ τ.arrs "co" = arrOf n col ∧
    (∀ a, a ≠ "cl" → τ.arrs a = σ.arrs a)
  obtain ⟨σ', r, ⟨hn', hco', ha'⟩, hl', hg'⟩ := classify_run (B := B) (n := n) (Ke := 10) (arr := "cl")
    (eqc := eqCo) Ctx (fun u v => col u = col v) hnB (fun τ h => h.1)
    (fun τ x h => ⟨by simp [h.1], by simp [h.2.1], fun a ha => by simp [h.2.2 a ha]⟩)
    (fun τ x h => ⟨by simp [h.1], by simp [h.2.1], fun a ha => by simp [h.2.2 a ha]⟩)
    (fun τ i x h => ⟨by simp [h.1], by simp [h.2.1], fun a ha => by simp [ha, h.2.2 a ha]⟩)
    (by
      intro τ h hu hv
      have e1 : (Expr.get "co" (.var "u")).evalB B τ = some (col (τ.vars "u")) := by
        simp [h.2.1, hu]; exact ⟨by omega, hcB _ hu⟩
      have e2 : (Expr.get "co" (.var "v")).evalB B τ = some (col (τ.vars "v")) := by
        simp [h.2.1, hv]; exact ⟨by omega, hcB _ hv⟩
      by_cases hc : col (τ.vars "u") = col (τ.vars "v")
      · refine ⟨τ.setVar "ok" 1, (Run.ite_true ?_ (Run.assign (by simp; omega))).mono (by simp),
          ⟨by simp [h.1], by simp [h.2.1], fun a ha => by simp [h.2.2 a ha]⟩, by simp [ind, hc],
          by simp, by simp, by simp⟩
        rw [evalB_condEq e1 e2]; simp [hc]
      · refine ⟨τ.setVar "ok" 0, (Run.ite_false ?_ (Run.assign (by simp; omega))).mono (by simp),
          ⟨by simp [h.1], by simp [h.2.1], fun a ha => by simp [h.2.2 a ha]⟩, by simp [ind, hc],
          by simp, by simp, by simp⟩
        rw [evalB_condEq e1 e2]; simp [hc])
    (σ := σ) ⟨hn, hco, fun _ _ => rfl⟩ hcl
  refine ⟨σ', r, ?_, hn', ha', fun x hx => r.frame_var x hx, r.out_eq (by decide),
    r.frame_inp (by decide)⟩
  refine List.ext_getElem (by simp [hl']) fun j hj _ => ?_
  have := hg' j (by omega)
  rw [List.getElem?_eq_getElem hj] at this
  simp only [Option.some.injEq] at this
  rw [this]; simp [arrOf]

end Lax185574Proofs.ResolveRam.Glue
