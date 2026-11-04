import Lax185574Proofs.ResolveRam.Glue.PFALoop
import Lax185574Proofs.StpRam.GlueOk

/-!
The far filter of lem:resolve-lift: the command `faCmd` and its
specification `FASpec` (`faCmd_spec`).

`faCmd` looks up the colors in the color table (`colSet`), reads the
header of the shifted tree (`treeSet`) and runs the member loop
(`memLoop`). On a tree word the far test `passSel` is the member test
`memP` (`passSel_memP`). `faCmd_ok`: the compiler accepts the command
for the layout `faLayout`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.FarRam Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- **The far filter.** -/
def faCmd : Com := .seq colSet (.seq treeSet memLoop)

/-- The scalars that `faCmd` writes. -/
def faV : List String := colV ++ treeV ++ loopV

theorem faCmd_wvars : ∀ y ∈ faCmd.wvars, y ∈ faV := by
  have h1 := colSet_wvars
  have h2 := treeSet_wvars
  have h3 : ∀ y ∈ memLoop.wvars, y ∈ loopV := by
    have := passC_wvars
    intro y hy
    by_cases hp : y ∈ passC.wvars
    · exact List.mem_append_left _ (this y hp)
    · simp only [memLoop, faBody, cpFr, cpSeg, push1, forUp, Com.wvars, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, List.append_nil, hp, false_or] at hy
      simp only [loopV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      tauto
  intro y hy
  simp only [faCmd, Com.wvars, List.mem_append] at hy
  simp only [faV, List.mem_append]
  rcases hy with h | h | h
  · exact Or.inl (Or.inl (h1 y h))
  · exact Or.inl (Or.inr (h2 y h))
  · exact Or.inr (h3 y h)

/-- The test of the far filter on the word of a tree is the member test. -/
theorem passSel_memP (Dw : DW) (σ : TypeTree) (w : List ℕ) :
    passSel Dw (toWord σ) w = memP Dw σ.ℓ (Node.atoms σ.root).words (rhoPlus σ.k σ.q) w := by
  unfold passSel passW memP
  rw [listWords_tree_root, toWord_typeTree]
  rfl

theorem room_ge {W R S : ℕ} (h : Room W R S) : 65536 * (S + 1) * (R + 1) ≤ W := by
  unfold Room at h
  have h1 : (R + 1) ≤ (R + 1) ^ 2 := by nlinarith
  have h2 : (S + 1) ≤ (S + 1) ^ 2 := by nlinarith
  calc 65536 * (S + 1) * (R + 1) ≤ 65536 * (S + 1) ^ 2 * (R + 1) ^ 2 := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h1
    _ = 2 ^ 16 * (R + 1) ^ 2 * (S + 1) ^ 2 := by ring
    _ ≤ W := h

theorem mem_toWord_of {ws : List (List ℕ)} {i : ℕ} (hi : i < ws.length) {v : ℕ} (hv : v ∈ ws[i]) :
    v ∈ toWord ws := frame_mem hi v (List.mem_cons_of_mem _ hv)

/-- The cost bound of the far filter, by powers of the base. -/
theorem fa_cost {b ℓ R L' m nL nC : ℕ} (hb : 1 ≤ b) (hℓ : ℓ ≤ b) (hR : R + 1 ≤ b) (hL : L' ≤ b)
    (hm : m ≤ b) :
    40 * nC + 100 + (20 * R + 60 + (nL * (passK ℓ L' R + 20 * m + 120) + 30)) ≤
      3000 * (nL + nC + 1) * b ^ 4 := by
  have e1 : (R + 2) * (R + 2) ≤ (2 * b) * (2 * b) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : (R + 2) * (R + 2) * (140 * L' + 500) ≤ (2 * b) * (2 * b) * (640 * b) :=
    Nat.mul_le_mul e1 (by omega)
  have e3 : ℓ * ((R + 2) * (R + 2) * (140 * L' + 500) + 30) ≤ b * ((2 * b) * (2 * b) * (640 * b) + 30) :=
    Nat.mul_le_mul hℓ (Nat.add_le_add_right e2 30)
  have hb4 : b ≤ b ^ 4 := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ 4 := Nat.pow_le_pow_right hb (by norm_num)
  have e4 : b * ((2 * b) * (2 * b) * (640 * b) + 30) = 2560 * b ^ 4 + 30 * b := by ring
  have hp : passK ℓ L' R + 20 * m + 120 ≤ 2900 * b ^ 4 := by
    unfold passK hopK; linarith
  have e5 : nL * (passK ℓ L' R + 20 * m + 120) ≤ 2900 * (nL * b ^ 4) := by
    calc _ ≤ nL * (2900 * b ^ 4) := Nat.mul_le_mul_left _ hp
      _ = 2900 * (nL * b ^ 4) := by ring
  have e6 : nC ≤ nC * b ^ 4 := Nat.le_mul_of_pos_right _ (by omega)
  have e7 : 3000 * (nL + nC + 1) * b ^ 4 = 3000 * (nL * b ^ 4) + 3000 * (nC * b ^ 4) + 3000 * b ^ 4 := by
    ring
  have e8 : 1 ≤ b ^ 4 := le_trans hb hb4
  rw [e7]
  generalize nL * (passK ℓ L' R + 20 * m + 120) = X at e5 ⊢
  generalize nL * b ^ 4 = Y at e5 ⊢
  generalize nC * b ^ 4 = Z at e6 ⊢
  generalize b ^ 4 = V at e8 hb4 ⊢
  omega

theorem maxLen_le_total' (L : List (List ℕ)) : maxLen L ≤ total L := by
  induction L with
  | nil => simp [maxLen]
  | cons a l ih =>
    simp only [maxLen, List.map_cons, List.foldr_cons, total, List.flatten_cons, List.length_append]
      at ih ⊢
    exact max_le (by omega) (by omega)

/-- **The specification of the far filter.** -/
theorem faCmd_spec : FASpec faCmd faV := by
  refine ⟨3000, 4, ?_⟩
  intro W τ ws L pre oc os yo P Q sg hoc hos hW hA hw hocv hosv hyov hPv hQv hPW hQW hsgv hsg hCT hσ'
    hL hY hF hRoom
  obtain ⟨cs, f, g, hct⟩ := hCT
  obtain ⟨σ, hσ⟩ := hσ'
  have g0 : ws[os].getD 0 0 = σ.k := by rw [hσ, toWord_typeTree]; rfl
  have g1 : ws[os].getD 1 0 = σ.q := by rw [hσ, toWord_typeTree]; rfl
  have g2 : ws[os].getD 2 0 = σ.ℓ := by rw [hσ, toWord_typeTree]; rfl
  rw [g0, g1, g2] at hRoom ⊢
  set R := rhoPlus σ.k σ.q
  set S := ySz (toWord ws) + ySz (toWord L) + yo + pre.length + σ.ℓ
  have hRS := room_ge hRoom
  have hSW : 65536 * (S + 1) ≤ W := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hRS
  have hRW : 65536 * (R + 1) ≤ W := by
    have := Nat.mul_le_mul_left 65536 (Nat.le_mul_of_pos_left (R + 1) (show 0 < S + 1 by omega))
    rw [← Nat.mul_assoc] at this; exact le_trans this hRS
  have hws : (toWord ws).length = ws.length + total ws + 1 := by
    rw [toWord_words, List.length_cons, Words.length_frames]
  have hwL : (toWord L).length = L.length + total L + 1 := by
    rw [toWord_words, List.length_cons, Words.length_frames]
  have hySw : (toWord ws).length + maxEntry (toWord ws) + 1 ≤ S := by simp only [S, ySz]; omega
  have hySL : (toWord L).length + maxEntry (toWord L) + 1 + yo + pre.length + σ.ℓ ≤ S := by
    simp only [S, ySz]; omega
  have hTB : total ws + ws.length + 4 < W + 1 := by omega
  have hent : ∀ i (hi : i < ws.length), ∀ v ∈ ws[i], v < W + 1 := fun i hi v hv => by
    have := le_maxEntry (mem_toWord_of hi hv); omega
  -- the colors
  obtain ⟨τ1, r1, cP1, cQ1, P1, Q1, f1, a1, o1, i1⟩ := colSet_run (B := W + 1) hw hoc hct hocv hPv hQv
    (by omega) (by omega) hTB (hent oc hoc)
  have hw1 : WordsAt ws τ1 := hw.of_arrs (by rw [a1]) (by rw [a1]) (by rw [a1])
  -- the shifted tree
  obtain ⟨τ2, r2, s2, L2, p2, f2, a2, o2, i2⟩ := treeSet_run (B := W + 1) hw1 hos hσ
    (by rw [f1 "os" (by decide), hosv]) hTB (hent os hos) (by omega) (by omega)
  have hd0 := drop_off hw hos
  rw [hσ] at hd0
  obtain ⟨r₁, hd₁, hl₁, hm₁⟩ := tree_atoms hd0
  set Aσ := (Node.atoms σ.root).words
  set Dw := dwOf P Q sg ws[oc]
  have hcP : Dw.cP = decide (P ∈ cs) := by simp only [Dw, dwOf, hct, inCT_flatMap]
  have hcQ : Dw.cQ = decide (Q ∈ cs) := by simp only [Dw, dwOf, hct, inCT_flatMap]
  have hP2 : PassAt (τ.arrs "a") (τ.arrs "y") (off ws os + 3) Dw σ.ℓ R τ2 :=
    ⟨by rw [a2, a1], by rw [a2, a1], p2, by rw [f2 _ (by decide), P1]; rfl, by rw [f2 _ (by decide), Q1]; rfl,
      by rw [f2 _ (by decide), cP1, hcP], by rw [f2 _ (by decide), cQ1, hcQ], L2, s2⟩
  have hoff := off_add_le hos
  have hlσ : (toWord σ).length = ws[os].length := by rw [hσ]
  have hAσ : Aσ.length < (toWord Aσ).length := by
    rw [toWord_words, List.length_cons, Words.length_frames]; omega
  have hmL : maxLen L ≤ total L := maxLen_le_total' L
  obtain ⟨τ3, r3, F3, c3, o3⟩ := memLoop_run (W := W) hP2 hd₁
    (by rw [f2 _ (by decide), f1 _ (by decide), hyov])
    (fun i h => by rw [a2, a1]; exact hY i h) hL
    (hF.congr (by rw [f2 _ (by decide), f1 _ (by decide)]) (by rw [a2, a1]))
    (by rw [a2, a1]; exact hA "OB") (by rw [a2, a1]; exact hA "y")
    (by omega) (fun v hv => hent os hos v (by rw [hσ]; exact hm₁ v hv)) (by omega)
    (fun v hv => by have := le_maxEntry hv; omega) (by simp only [Dw, dwOf]; omega)
    (by simp only [Dw, dwOf]; omega) (by omega) (by omega)
  have hfil : L.filter (passSel Dw ws[os]) = L.filter (memP Dw σ.ℓ Aσ R) := by
    rw [hσ]; exact List.filter_congr (fun w _ => passSel_memP Dw σ w)
  refine ⟨τ3, ?_, by rw [hfil]; exact F3, by rw [hfil]; exact c3, ?_⟩
  · unfold faCmd
    refine (Run.seq r1 (Run.seq r2 r3)).mono ?_
    have hb := fa_cost (b := ws[os].length + σ.ℓ + maxLen L + R + 1) (ℓ := σ.ℓ) (R := R)
      (L' := Aσ.length + maxLen L) (m := maxLen L) (nL := L.length) (nC := ws[oc].length)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    refine le_trans hb ?_
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_left
    omega
  · refine ⟨fun y hy => ?_, fun b hb => ?_, fun b => ?_, ?_, ?_⟩
    · simp only [faV, List.mem_append, not_or] at hy
      rw [o3.vars y hy.2, f2 y (fun h => hy.1.2 h), f1 y (fun h => hy.1.1 h)]
    · have : b ≠ "OB" := by intro h; subst h; simp [keepA] at hb
      rw [o3.arrs b this, a2, a1]
    · by_cases h : b = "OB"
      · subst h; rw [o3.len, a2, a1]
      · rw [o3.arrs b h, a2, a1]
    · rw [o3.out, o2, o1]
    · rw [o3.inp, i2, i1]

/-- A layout for the far filter. -/
def faLayout : Lax808846Proofs.Compile.Layout :=
  ⟨faV ++ ["W", "oc", "os", "yo", "gP", "gQ"], ["a", "st", "ln", "y", "OB"], 6⟩

theorem faCmd_ok : Lax808846Proofs.Compile.Com.Ok faLayout faCmd :=
  StpRam.comOkB_sound _ _ (by decide)

end Lax185574Proofs.ResolveRam.Glue
