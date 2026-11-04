import Lax185574Proofs.CompRam.GBuild
import Lax185574Proofs.CompRam.GChk
import Lax185574Proofs.CompRam.Assembly

/-!
The glue program of lem:compose meets its specification.

The program is `guardedProgram gLayout (glueCmd eR eS eC d)` with
`d = sQ - guardBits gLayout`. Its input entries are below
`2^(v - sI)` with `sI = guardBits gLayout + 16`, so the input has length
at most twice its largest entry plus three (`uT_len`) and fits into the
buffers. `glueCmd_run`: the command builds the output, and it leaves
`ovf` at `0` exactly when the guard of the query, the round test and
the bound on the written entries hold. From this the two clauses of
`GlueSpec` follow (`glue_spec`), and with them `GlueHyp` (`glue_hyp`).
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax185574.PartialGraphs Lax185574Proofs.Simulate

section input

variable {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ} {u₁ : Fin l1 → Fin n}
  {u₂ : Fin l2 → Fin n}

/-- The input of a reached round is at most about twice as long as its largest entry, and
holds the round counter. -/
theorem uT_len {j : ℕ} (hR : Reached G k q u₁ u₂ j) :
    (uT G k q u₁ u₂ j).length ≤ 2 * maxEntry (uT G k q u₁ u₂ j) + 3 ∧
      j ≤ maxEntry (uT G k q u₁ u₂ j) := by
  cases j with
  | zero =>
    rw [uT_zero]
    have := le_maxEntry (x := [0, (xT G k q u₁ u₂).length] ++ xT G k q u₁ u₂ ++ [0])
      (v := (xT G k q u₁ u₂).length) (by simp)
    simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
    omega
  | succ j =>
    obtain ⟨g, S, q', htr, -, -⟩ := hR j (by omega)
    rw [uT_succ_eq htr]
    set o := ansWord q' (ansOf G q')
    have h1 := le_maxEntry (x := glueIn (j + 1) (g :: S) o) (v := (stWord (j + 1) (g :: S)).length)
      (by simp [glueIn])
    have h2 := le_maxEntry (x := glueIn (j + 1) (g :: S) o) (v := o.length) (by simp [glueIn])
    have h3 := le_maxEntry (x := glueIn (j + 1) (g :: S) o) (v := j + 1) (by simp [glueIn, stWord])
    refine ⟨?_, h3⟩
    simp only [glueIn, List.length_append, List.length_cons, List.length_nil] at h1 h2 ⊢
    omega

end input

/-! ### The command -/

/-- The input layer of the glue. -/
abbrev sIg : ℕ := guardBits gLayout + 16

theorem init_arrs_lt (W : ℕ) (x : List ℕ) :
    ∀ a, ∀ v ∈ ((initEnv (fun _ => W + 1) x).setVar "W" W).arrs a, v < W + 1 := by
  intro a v hv
  simp only [Env.setVar, initEnv] at hv
  rw [List.eq_of_mem_replicate hv]; omega

theorem built_sub {j : ℕ} {r : Res} {ob : List ℕ} {σ : Env} (hB : Built j r ob σ) :
    ob.length ≤ (outW j r).length ∧ ∀ e ∈ ob, e ∈ outW j r := by
  obtain ⟨-, hsp, -, hout, -⟩ := hB
  rw [hout]
  refine ⟨by simp; omega, fun e he => ?_⟩
  rw [← List.take_append_drop (σ.vars "sp") ob] at he
  rcases List.mem_append.1 he with h | h <;> simp [h]

theorem built_q {j : ℕ} {S : List Fr} {q' : Qry} {ob : List ℕ} {σ : Env}
    (hB : Built j (.call S q') ob σ) :
    (realQ q').length ≤ ob.length ∧ ∀ e ∈ realQ q', e ∈ ob := by
  obtain ⟨-, -, -, -, hk, hle, hseg⟩ := hB
  rw [← hseg]
  exact ⟨by rw [length_seg (by omega)]; omega, fun e he => mem_seg he⟩

theorem cost_arith {K1 K2 K3 K4 A B P e : ℕ} (h1 : K1 ≤ 2000 * (A + B + 1))
    (h2 : K2 ≤ B * 30 + 60 * e + 30 * P + 300) (h3 : K3 ≤ 30 * P + 600) (h4 : K4 ≤ 30 * B + 300100) :
    1 + 5 + (K1 + (K2 + (K3 + K4))) ≤ 2200 * (A + B + 1) + 60 * e + 60 * P + 302000 := by
  omega

/-- **The command of the glue at a reached round.** -/
theorem glueCmd_run {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ} {u₁ : Fin l1 → Fin n}
    {u₂ : Fin l2 → Fin n} (hI : Inst G k q u₁ u₂) {j : ℕ} (hR : Reached G k q u₁ u₂ j) {v : ℕ}
    (hv : sIg ≤ v) (hent : ∀ e ∈ uT G k q u₁ u₂ j, e < 2 ^ (v - (113 + 16))) (eR eS eC d : ℕ) :
    ∃ σ' K, Run (guardW gLayout v + 1) (glueCmd eR eS eC d)
        ((initEnv (fun _ => guardW gLayout v + 1) (uT G k q u₁ u₂ j)).setVar "W" (guardW gLayout v))
        σ' K ∧
      (guardW gLayout v < 2 ^ 34 → σ'.vars "ovf" ≠ 0) ∧
      (2 ^ 34 ≤ guardW gLayout v → ∃ ob : List ℕ, σ'.out = aT G k q u₁ u₂ (j + 1) ∧
        ob.length ≤ (aT G k q u₁ u₂ (j + 1)).length ∧ (∀ e ∈ ob, e ∈ aT G k q u₁ u₂ (j + 1)) ∧
        (∀ e ∈ aT G k q u₁ u₂ (j + 1), e ∈ ob ∨ e ∈ dSq) ∧
        (∀ S q', trT G k q u₁ u₂ j = .call S q' → (realQ q').length ≤ ob.length ∧
          ∀ e ∈ realQ q', e ∈ ob) ∧
        (σ'.vars "ovf" = 0 ↔ GOK eR eS eC d (guardW gLayout v) (trT G k q u₁ u₂ j) ∧
          min ((1 + 2 * j + 1) ^ (3 + 1)) (guardW gLayout v) ≤
            guardW gLayout v / min (2 ^ d) (guardW gLayout v) ∧
          ∀ e ∈ ob, e < guardW gLayout v / 2 ^ 20 + 1) ∧
        K ≤ 2200 * ((uT G k q u₁ u₂ j).length + ob.length + 1) + 60 * (eR + eS + eC + 1) +
          60 * 2 ^ d + 302000) := by
  have hgb : guardBits gLayout = 113 := guardBits_gLayout
  simp only [sIg, hgb] at hv hent
  set W := guardW gLayout v with hWd
  have hW1 : W + 1 = 2 ^ (v - 113) := by rw [← hgb]; exact guardW_succ _ _
  have hW16 : 2 ^ 16 ≤ W + 1 := by rw [hW1]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set σ0 := (initEnv (fun _ => W + 1) (uT G k q u₁ u₂ j)).setVar "W" W with hσ0
  have hW0 : σ0.vars "W" = W := by simp [hσ0]
  have hsh : (Expr.shiftr (V "W") (N 34)).evalB (W + 1) σ0 = some (W / 2 ^ 34) := by
    have h34 : 34 < W + 1 := by omega
    exact evalB_bin (by rw [← hW0]; exact evalB_var (by omega)) (evalB_lit h34)
      (by simp only [Bop.apply_shiftr]; exact Nat.lt_succ_of_le (Nat.div_le_self _ _))
  by_cases hsmall : W < 2 ^ 34
  · have hc : (Cond.eq (.shiftr (V "W") (N 34)) (N 0)).evalB (W + 1) σ0 = some true := by
      rw [evalB_condEq hsh (evalB_lit (by omega))]
      simp [Nat.div_eq_of_lt hsmall]; omega
    refine ⟨σ0.setVar "ovf" 1, _, Run.ite_true hc (Run.assign (evalB_lit (by omega))),
      fun _ => by simp, fun h => absurd h (by omega)⟩
  · have hbig : 2 ^ 34 ≤ W := by omega
    have hc : (Cond.eq (.shiftr (V "W") (N 34)) (N 0)).evalB (W + 1) σ0 = some false := by
      rw [evalB_condEq hsh (evalB_lit (by omega))]
      have : W / 2 ^ 34 ≠ 0 := by
        have := (Nat.le_div_iff_mul_le (show 0 < 2 ^ 34 by positivity)).2 (show 1 * 2 ^ 34 ≤ W by omega)
        omega
      simp only [beq_iff_eq, Option.some.injEq]; simpa using this
    -- bounds of the input
    obtain ⟨hlenM, hjM⟩ := uT_len hR
    set x := uT G k q u₁ u₂ j with hx
    have hN0 : 2 ^ 16 * 2 ^ (v - (113 + 16)) = W + 1 := by
      rw [hW1, ← pow_add, show 16 + (v - (113 + 16)) = v - 113 by omega]
    have hmx : maxEntry x < 2 ^ (v - (113 + 16)) ∨ x = [] := by
      by_cases hx0 : x = []
      · exact Or.inr hx0
      · exact Or.inl (hent _ (maxEntry_mem hx0))
    have hmx' : maxEntry x + 1 ≤ 2 ^ (v - (113 + 16)) := by
      rcases hmx with h | h
      · omega
      · rw [h]; simp [maxEntry]; exact Nat.one_le_two_pow
    have hin : ∀ e ∈ x, 2 ^ 16 * (e + 1) ≤ W + 1 := fun e he => by
      have := hent e he; rw [← hN0]; exact Nat.mul_le_mul_left _ (by omega)
    have hN19 : 2 ^ 18 ≤ 2 ^ (v - (113 + 16)) := by
      have : 2 ^ 34 ≤ 2 ^ 16 * 2 ^ (v - (113 + 16)) := by rw [hN0]; exact Nat.le_succ_of_le hbig
      by_contra hc
      have h1 : 2 ^ (v - (113 + 16)) < 2 ^ 18 := by omega
      have : 2 ^ 16 * 2 ^ (v - (113 + 16)) < 2 ^ 16 * 2 ^ 18 := Nat.mul_lt_mul_of_pos_left h1 (by norm_num)
      omega
    have hlen : 2 ^ 14 * (x.length + 513) ≤ W + 1 := by
      rw [← hN0]
      have : x.length + 513 ≤ 4 * 2 ^ (v - (113 + 16)) := by omega
      calc 2 ^ 14 * (x.length + 513) ≤ 2 ^ 14 * (4 * 2 ^ (v - (113 + 16))) := Nat.mul_le_mul_left _ this
        _ = 2 ^ 16 * 2 ^ (v - (113 + 16)) := by ring
    obtain ⟨σ1, ob, K1, r1, hB, hjr1, hW1', hov1, hout1, hOB1, hob1, hK1⟩ :=
      buildCmd_run hI hR (W := W) (le_trans (by norm_num) (Nat.le_succ_of_le hbig)) hin hlen
    have hv1 : ∀ v' ∈ σ1.arrs "OB", v' ≤ W := fun v' hv' => by
      have := Run.arrs_lt r1 (init_arrs_lt W x) "OB" v' hv'; omega
    have hF1 := hB.1
    obtain ⟨σ2, r2, hov2, fv2, fa2, fo2, fi2⟩ := guardQ_run (eR := eR) (eS := eS) (eC := eC) (d := d)
      hW1' (by omega) hF1 hB.2.2.2.2 (by omega) hv1
    have hF2 : Filled "OB" "po" ob σ2 := hF1.congr (fv2 "po" (by decide)) (by rw [fa2])
    obtain ⟨σ3, r3, hov3, hF3, fv3, fa3, hOB3, hv3, fo3, fi3⟩ := roundTest_run (d := d)
      (by rw [fv2 "W" (by decide), hW1']) (by omega) hF2 (by omega) (by rw [fa2, hOB1])
      (by rw [fv2 "jr" (by decide), hjr1]; omega) (by rw [fa2]; exact hv1)
    have hsp3 : σ3.vars "sp" = σ1.vars "sp" := by
      rw [fv3 "sp" (by decide), fv2 "sp" (by decide)]
    have hdq3 : σ3.vars "dq" = σ1.vars "dq" := by
      rw [fv3 "dq" (by decide), fv2 "dq" (by decide)]
    have hobv : ∀ e ∈ ob, e ≤ W := fun e he => by
      have := hF1.get
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      have h1 := hF1.get i hi
      exact hv1 _ (List.mem_of_getElem? h1)
    obtain ⟨σ4, r4, ho4, hov4, fi4⟩ := wrOut_run (W := W) (σ := σ3) (ob := ob)
      (by rw [fv3 "W" (by decide), fv2 "W" (by decide), hW1']) (Nat.le_succ_of_le hbig) hF3
      (by rw [hsp3]; exact hB.2.1) (by rw [hdq3]; exact hB.2.2.1) (by omega) hobv
    refine ⟨σ4, _, Run.ite_false hc (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2
      (Run.seqs_cons (by simp) r3 (Run.seqs_one r4)))), fun h => absurd h (by omega), fun _ => ?_⟩
    have hjr2 : σ2.vars "jr" = j := by rw [fv2 "jr" (by decide), hjr1]
    have hout : σ4.out = aT G k q u₁ u₂ (j + 1) := by
      rw [ho4, fo3, fo2, hout1, hsp3, hdq3, aT_succ, hB.2.2.2.1]; simp
    obtain ⟨hsub1, hsub2⟩ := built_sub hB
    rw [← aT_succ] at hsub1 hsub2
    refine ⟨ob, hout, hsub1, hsub2, ?_, fun S q' htr => built_q (htr ▸ hB), ?_, ?_⟩
    · intro e he
      rw [aT_succ, hB.2.2.2.1] at he
      rcases List.mem_append.1 he with h | h
      · rcases List.mem_append.1 h with h' | h'
        · exact Or.inl (List.mem_of_mem_take h')
        · split_ifs at h' <;> simp_all
      · exact Or.inl (List.mem_of_mem_drop h)
    · rw [hov4, hov3, hov2, hjr2]
      simp only [hov1, true_and, and_assoc]
    · have hcs : (Cond.eq (.shiftr (V "W") (N 34)) (N 0)).size = 5 := rfl
      rw [hcs]
      exact cost_arith hK1 le_rfl le_rfl le_rfl

/-! ### The specification -/

theorem guardW_eq (v : ℕ) : guardW gLayout v + 1 = 2 ^ (v - 113) := by
  rw [← guardBits_gLayout]; exact guardW_succ _ _

theorem div_shift_eq {m : ℕ} (hm : 20 ≤ m) : (2 ^ m - 1) / 2 ^ 20 + 1 = 2 ^ (m - 20) := by
  have h := two_pow_sub_one_div (w := m) (r := 20) hm
  rw [h]; have : 0 < 2 ^ (m - 20) := by positivity
  omega

theorem dSq_lt' {e : ℕ} (he : e ∈ dSq) : e < 8000 := dSq_lt e he

/-- The constant of the time bound of the glue. -/
def cGl (eR eS eC d : ℕ) : ℕ :=
  2 ^ 40 * (gLayout.const + 1) * (60 * (eR + eS + eC + 1) + 60 * 2 ^ d + 400000)

theorem cGl_ge (eR eS eC d : ℕ) : 2 ^ 40 ≤ cGl eR eS eC d := by
  unfold cGl
  have : 1 ≤ (gLayout.const + 1) * (60 * (eR + eS + eC + 1) + 60 * 2 ^ d + 400000) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 2 ^ 40 = 2 ^ 40 * 1 := by ring
    _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ this

theorem time_arith {c K A B e P : ℕ} (hK : K ≤ 2200 * (A + B + 1) + 60 * e + 60 * P + 302000) :
    c * K + 5 ≤ 2 ^ 40 * (c + 1) * (60 * e + 60 * P + 400000) * (A + B + 1) ^ 2 := by
  have hY : A + B + 1 ≤ (A + B + 1) ^ 2 := by nlinarith
  have hY1 : 1 ≤ A + B + 1 := by omega
  generalize A + B + 1 = Y at hK hY hY1
  have hCY := Nat.mul_le_mul_left (60 * e + 60 * P + 302000) hY1
  have h1 : K ≤ (60 * e + 60 * P + 400000) * Y := by
    have e1 : (60 * e + 60 * P + 400000) * Y = (60 * e + 60 * P + 302000) * Y + 98000 * Y := by ring
    rw [e1]; omega
  have h2 : c * K ≤ c * ((60 * e + 60 * P + 400000) * Y) := Nat.mul_le_mul_left _ h1
  have hT : 400000 ≤ 60 * e + 60 * P + 400000 := Nat.le_add_left _ _
  generalize 60 * e + 60 * P + 400000 = T at h1 h2 hT
  have h3 : (c + 1) * (T * Y) ≤ 2 ^ 40 * (c + 1) * T * Y ^ 2 := by
    have : T * Y ≤ T * Y ^ 2 := Nat.mul_le_mul_left _ hY
    nlinarith
  have h4 : 5 ≤ T * Y := le_trans (by omega) (Nat.le_mul_of_pos_right T hY1)
  have h5 : c * (T * Y) + 5 ≤ (c + 1) * (T * Y) := by rw [Nat.add_mul, one_mul]; omega
  calc c * K + 5 ≤ c * (T * Y) + 5 := by omega
    _ ≤ (c + 1) * (T * Y) := h5
    _ ≤ _ := h3

/-- A guard with exponent `E` passes when `2 s^E` fits. -/
theorem pass_arith {s E W v sQ : ℕ} (hW1 : W + 1 = 2 ^ (v - 113)) (hsQ : 113 < sQ) (hs : 1 ≤ s)
    (h : 2 * s ^ E ≤ 2 ^ (v - sQ)) : min (s ^ E) W ≤ W / min (2 ^ (sQ - 113)) W :=
  guard_compl_arith hW1 hsQ hs h

/-- **The glue meets its specification.** -/
theorem glue_spec (eR eS eC D : ℕ) (hD : sIg + 4 ≤ D) :
    GlueSpec (guardedProgram gLayout (glueCmd eR eS eC (D + 20 - 113))) sIg (D + 20) eR eS eC
      (cGl eR eS eC (D + 20 - 113)) (eR + eS + eC + 5) := by
  have hgb : guardBits gLayout = 113 := guardBits_gLayout
  have hD' : 133 ≤ D := by simpa [sIg, hgb] using hD
  set d := D + 20 - 113 with hd
  have hok := glueCmd_ok eR eS eC d
  have hWs : "W" ∈ gLayout.scalars := by decide
  have hOs : "ovf" ∈ gLayout.scalars := by decide
  constructor
  · intro n G k q l1 l2 u₁ u₂ hI j hR v hv hent o t hrun
    obtain ⟨σ', K, r, hsmall, hbig⟩ := glueCmd_run hI hR hv hent eR eS eC d
    have hv' : 129 ≤ v := by simpa [sIg, hgb] using hv
    have hW1 := guardW_eq v
    set W := guardW gLayout v
    have hx : ∀ e ∈ uT G k q u₁ u₂ j, e ≤ guardW gLayout v := fun e he => by
      have h1 := hent e he
      have h2 : 2 ^ (v - sIg) ≤ 2 ^ (v - 113) := Nat.pow_le_pow_right (by norm_num) (by simp only [sIg, hgb]; omega)
      omega
    obtain ⟨hov0, ho⟩ := (guarded_sound hok hWs hOs (by rw [hgb]; omega) hx r).1 o t hrun
    by_cases hsm : W < 2 ^ 34
    · exact absurd hov0 (hsmall hsm)
    obtain ⟨ob, hout, -, hsub2, hcover, -, hiff, -⟩ := hbig (by omega)
    obtain ⟨hgok, hrt, heb⟩ := hiff.1 hov0
    have hW34 : 2 ^ 34 < 2 ^ (v - 113) := by omega
    have hv35 : 35 ≤ v - 113 := by
      by_contra hc
      have : 2 ^ (v - 113) ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hOb : W / 2 ^ 20 + 1 = 2 ^ (v - sIg - 4) := by
      rw [show W = 2 ^ (v - 113) - 1 by omega, div_shift_eq (by omega),
        show v - 113 - 20 = v - sIg - 4 by simp only [sIg, hgb]; omega]
    refine ⟨by rw [ho, hout], fun e he => ?_, ?_, ?_⟩
    · rw [ho, hout] at he
      rcases hcover e he with h | h
      · rw [← hOb]; exact heb e h
      · have h1 := dSq_lt' h
        have : 2 ^ 15 ≤ 2 ^ (v - sIg - 4) := Nat.pow_le_pow_right (by norm_num) (by simp [sIg, hgb]; omega)
        omega
    · have h := guard_sound_arith (s := 1 + 2 * j + 1) (E := 3 + 1) hW1 (show 113 < D + 20 by omega)
        (by omega) (by rw [hd] at hrt; exact hrt)
      calc (2 * j + 1) ^ 4 ≤ (1 + 2 * j + 1) ^ (3 + 1) := Nat.pow_le_pow_left (by omega) _
        _ ≤ _ := h
    · cases htr : trT G k q u₁ u₂ j with
      | call S q' =>
        rw [htr] at hgok
        exact guard_sound_arith hW1 (show 113 < D + 20 by omega) (by omega) (by rw [hd] at hgok; exact hgok)
      | done z => trivial
      | err => trivial
  · intro n G k q l1 l2 u₁ u₂ hI j hR v hv hent hcG
    obtain ⟨σ', K, r, hsmall, hbig⟩ := glueCmd_run hI hR hv hent eR eS eC d
    have hv' : 129 ≤ v := by simpa [sIg, hgb] using hv
    have hW1 := guardW_eq v
    set W := guardW gLayout v
    have hx : ∀ e ∈ uT G k q u₁ u₂ j, e ≤ guardW gLayout v := fun e he => by
      have h1 := hent e he
      have h2 : 2 ^ (v - sIg) ≤ 2 ^ (v - 113) := Nat.pow_le_pow_right (by norm_num) (by simp only [sIg, hgb]; omega)
      omega
    set U := uT G k q u₁ u₂ j
    set A := aT G k q u₁ u₂ (j + 1)
    set X := U.length + A.length + maxEntry (U ++ A) + 1 with hX
    set E := eR + eS + eC + 5
    have hX1 : 1 ≤ X := by omega
    have hXE : X ≤ X ^ E := Nat.le_self_pow (by omega) _
    have hsQ : 2 ^ (v - (D + 20)) ≤ W + 1 := by
      rw [hW1]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc40 := cGl_ge eR eS eC d
    have hcX : cGl eR eS eC d * X ^ E ≤ 2 ^ (v - (D + 20)) := hcG
    have hcX1 : X ^ E ≤ cGl eR eS eC d * X ^ E := Nat.le_mul_of_pos_left _ (by omega)
    have hbig' : 2 ^ 34 ≤ W := by
      have : 2 ^ 40 ≤ cGl eR eS eC d * X ^ E :=
        le_trans hc40 (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hX1))
      omega
    obtain ⟨ob, hout, hsub1, hsub2, -, hq, hiff, hK⟩ := hbig hbig'
    have hmaxA : ∀ e ∈ A, e ≤ maxEntry (U ++ A) := fun e he => le_maxEntry (List.mem_append_right _ he)
    have hjU : j ≤ maxEntry (U ++ A) := le_trans (uT_len hR).2 (maxEntry_le (fun e he =>
      le_maxEntry (List.mem_append_left _ he)))
    have hov : σ'.vars "ovf" = 0 := by
      refine hiff.2 ⟨?_, ?_, ?_⟩
      · cases htr : trT G k q u₁ u₂ j with
        | call S q' =>
          obtain ⟨hql, hqe⟩ := hq S q' htr
          show min (((realQ q').length + maxEntry (realQ q') + 1) ^ (expQ eR eS eC q' + 1)) W ≤ _
          have hs : (realQ q').length + maxEntry (realQ q') + 1 ≤ X := by
            have : maxEntry (realQ q') ≤ maxEntry (U ++ A) :=
              maxEntry_le (fun e he => hmaxA e (hsub2 e (hqe e he)))
            omega
          have he : expQ eR eS eC q' + 1 ≤ E := by cases q' <;> simp [expQ, E] <;> omega
          refine pass_arith hW1 (show 113 < D + 20 by omega) (by omega) ?_
          calc 2 * ((realQ q').length + maxEntry (realQ q') + 1) ^ (expQ eR eS eC q' + 1)
              ≤ 2 * X ^ E := Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_left hs _)
                (Nat.pow_le_pow_right hX1 he))
            _ ≤ cGl eR eS eC d * X ^ E := Nat.mul_le_mul_right _ (by omega)
            _ ≤ _ := hcX
        | done z => trivial
        | err => trivial
      · refine pass_arith hW1 (show 113 < D + 20 by omega) (by omega) ?_
        have h2 : 1 + 2 * j + 1 ≤ 2 * X := by omega
        calc 2 * (1 + 2 * j + 1) ^ (3 + 1) ≤ 2 * (2 * X) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
          _ = 32 * X ^ 4 := by ring
          _ ≤ 32 * X ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
          _ ≤ cGl eR eS eC d * X ^ E := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := hcX
      · intro e he
        have h1 : e < X := by have := hmaxA e (hsub2 e he); omega
        have h2 : 2 ^ (v - (D + 20)) ≤ 2 ^ (v - 113 - 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [show W = 2 ^ (v - 113) - 1 by omega, div_shift_eq (by
          by_contra hc
          have : 2 ^ (v - 113) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)]
        omega
    obtain ⟨t, ht, hrt⟩ := (guarded_sound hok hWs hOs (by rw [hgb]; omega) hx r).2 hov
    refine ⟨t, le_trans ht ?_, by rw [← hout]; exact hrt⟩
    have := time_arith (c := gLayout.const) hK
    unfold cGl
    calc gLayout.const * K + 5 ≤ _ := this
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (by omega) 2

/-- **The glue hypothesis of lem:compose holds.** -/
theorem glue_hyp : GlueHyp :=
  ⟨sIg, fun eR eS eC D hD => ⟨_, _, _, by omega, glue_spec eR eS eC D hD⟩⟩

end Lax185574Proofs.CompRam
