import Lax185574Proofs.ResolveRam.Glue.PEx6

/-!
The expansion of an item of lem:resolve-lift: the command `exCmd` and
its specification `ExSpec` (`exCmd_spec`).

`exCmd` looks up the colors (`colSet`), reads the header of the item
(`exHdr`), finds the list of extensions of the root (`exSkip`) and runs
the three parts. The words of `exW` with the index in front are the
words of the three parts (`exW_parts`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- **The expansion.** -/
def exCmd : Com := .seq colSet (.seq exHdr (.seq exSkip (.seq part1 (.seq part2 part3))))

/-- The scalars that `exCmd` writes. -/
def exV : List String := colV ++ hdrV ++ skipV ++ p1V ++ p2V ++ p3V

/-- **The words of the expansion, part by part.** -/
theorem exW_parts (Dw : DW) (k q ℓ i : ℕ) (t : Node (q + 1) ℓ) (C : List (List ℕ)) :
    (exW Dw k q ℓ (toWord t) C).map (i :: ·) =
      (Node.exts t).words.map (oldW i k q ℓ) ++
        (Node.exts t).words.flatMap (oldG Dw (rhoPlus (k + 1) q) i k q ℓ) ++
          C.flatMap (newG Dw (rhoPlus (k + 1) q) i q ℓ) := by
  have hE : listWords (toWord t) (listEnd (toWord t) 0) = (Node.exts t).words := by
    have := (nodeSplit (x := toWord t) (p := 0) (t := t) (r := []) (by simp)).2
    rw [List.append_nil] at this
    exact listWords_eq (r := []) (by rw [this, List.append_nil])
  unfold exW
  simp only [hE, List.map_append, List.map_map, List.map_flatMap]
  congr 1
  congr 1
  funext cw
  unfold newG
  split_ifs <;> simp

theorem frames_map_oldW (i k q ℓ : ℕ) :
    ∀ E : List (List ℕ), (∀ ew ∈ E, 1 ≤ ew.length) →
      (frames (E.map (oldW i k q ℓ))).length = (frames E).length + 4 * E.length
  | [], _ => by simp [frames]
  | ew :: E, h => by
    have ih := frames_map_oldW i k q ℓ E (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have h1 := h ew (List.mem_cons_self ..)
    rw [List.map_cons, show ew :: E = [ew] ++ E from rfl, show oldW i k q ℓ ew :: E.map (oldW i k q ℓ) =
      [oldW i k q ℓ ew] ++ E.map (oldW i k q ℓ) from rfl, frames_append, frames_append, List.length_append,
      List.length_append, ih, frames_single, frames_single]
    simp [oldW, childW]
    omega

theorem exFrames_flatMap_le (ℓ : ℕ) (f : List ℕ → List (List ℕ)) :
    ∀ E : List (List ℕ), (∀ ew ∈ E, (frames (f ew)).length ≤ ℓ * (ew.length + 5)) →
      (frames (E.flatMap f)).length ≤ ℓ * ((frames E).length + 4 * E.length)
  | [], _ => by simp [frames]
  | ew :: E, h => by
    have ih := exFrames_flatMap_le ℓ f E (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have h1 := h ew (List.mem_cons_self ..)
    rw [List.flatMap_cons, frames_append, List.length_append]
    have e : (frames (ew :: E)).length = ew.length + 1 + (frames E).length := by simp [frames]; omega
    rw [e, List.length_cons]
    have : ℓ * (ew.length + 5) + ℓ * ((frames E).length + 4 * E.length) =
        ℓ * (ew.length + 1 + (frames E).length + 4 * (E.length + 1)) := by ring
    omega

theorem length_flatMap_le (ℓ : ℕ) (f : List ℕ → List (List ℕ)) :
    ∀ E : List (List ℕ), (∀ ew ∈ E, (f ew).length ≤ ℓ) → (E.flatMap f).length ≤ ℓ * E.length
  | [], _ => by simp
  | ew :: E, h => by
    have ih := length_flatMap_le ℓ f E (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have h1 := h ew (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega

theorem room_sq {W R S : ℕ} (h : Room W R S) : 65536 * ((S + 1) * (S + 1)) ≤ W := by
  unfold Room at h
  have h1 : 1 ≤ (R + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc 65536 * ((S + 1) * (S + 1)) = 2 ^ 16 * 1 * (S + 1) ^ 2 := by ring
    _ ≤ 2 ^ 16 * (R + 1) ^ 2 * (S + 1) ^ 2 := by
      apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; exact h1
    _ ≤ W := h

/-- The cost of the expansion, by powers of the base. -/
theorem ex_cost {b ℓ R L Lt nE TC cn nC : ℕ} (hb : 1 ≤ b) (hℓ : ℓ ≤ b) (hR : R + 1 ≤ b) (hL : L ≤ b)
    (hLt : Lt ≤ b) (hnE : nE ≤ b) (hTC : TC ≤ b) (hcn : cn ≤ b) :
    40 * nC + 100 + (20 * R + 120 + (20 * Lt + 40 + (nE * (20 * L + 130) + 10 +
      (nE * (ℓ * (hopK (2 * L) R + 20 * L + 100) + 50) + 10 +
        (cn * (ℓ * (hopK (2 * TC) R + 20 * TC + 100) + 120) + 10))))) ≤
      8000 * (nC + 1) * b ^ 5 := by
  have hk : ∀ x, x ≤ b → hopK (2 * x) R ≤ 3120 * b ^ 3 := fun x hx => by
    unfold hopK
    have e1 : (R + 2) * (R + 2) ≤ (2 * b) * (2 * b) := Nat.mul_le_mul (by omega) (by omega)
    have e2 : (R + 2) * (R + 2) * (140 * (2 * x) + 500) ≤ (2 * b) * (2 * b) * (780 * b) :=
      Nat.mul_le_mul e1 (by omega)
    have : (2 * b) * (2 * b) * (780 * b) = 3120 * b ^ 3 := by ring
    omega
  have hb3 : b ≤ b ^ 3 := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ 3 := Nat.pow_le_pow_right hb (by norm_num)
  have hb4 : b ^ 3 ≤ b ^ 4 := Nat.pow_le_pow_right hb (by norm_num)
  have hb5 : b ^ 4 ≤ b ^ 5 := Nat.pow_le_pow_right hb (by norm_num)
  have hp : ∀ x, x ≤ b → ℓ * (hopK (2 * x) R + 20 * x + 100) + 120 ≤ 3400 * b ^ 4 := fun x hx => by
    have h1 := hk x hx
    have h2 : hopK (2 * x) R + 20 * x + 100 ≤ 3240 * b ^ 3 := by omega
    have h3 := Nat.mul_le_mul hℓ h2
    have h4 : b * (3240 * b ^ 3) = 3240 * b ^ 4 := by ring
    omega
  have hq1 := Nat.mul_le_mul hnE (hp L hL)
  have hq2 := Nat.mul_le_mul hcn (hp TC hTC)
  have h5 : b * (3400 * b ^ 4) = 3400 * b ^ 5 := by ring
  have hq3 : nE * (20 * L + 130) ≤ 150 * b ^ 5 := by
    have := Nat.mul_le_mul hnE (show 20 * L + 130 ≤ 150 * b ^ 4 by omega)
    have h6 : b * (150 * b ^ 4) = 150 * b ^ 5 := by ring
    omega
  have h7 : nC ≤ nC * b ^ 5 := Nat.le_mul_of_pos_right _ (by omega)
  have h8 : 8000 * (nC + 1) * b ^ 5 = 8000 * (nC * b ^ 5) + 8000 * b ^ 5 := by ring
  have h9 : nE * (ℓ * (hopK (2 * L) R + 20 * L + 100) + 50) ≤ nE * (ℓ * (hopK (2 * L) R + 20 * L + 100) + 120) :=
    Nat.mul_le_mul_left _ (by omega)
  generalize ℓ * (hopK (2 * L) R + 20 * L + 100) = X1 at *
  generalize ℓ * (hopK (2 * TC) R + 20 * TC + 100) = X2 at *
  generalize nE * (X1 + 50) = Y1 at *
  generalize nE * (X1 + 120) = Y1' at *
  generalize cn * (X2 + 120) = Y2 at *
  generalize nC * b ^ 5 = Z at *
  omega

set_option maxHeartbeats 1000000 in
/-- **The specification of the expansion.** -/
theorem exCmd_spec : ExSpec exCmd exV := by
  refine ⟨8000, 5, ?_⟩
  intro W τ ws pre oc ow cl cn i P Q sg p g k q ℓ t hoc how hW hA hw hocv howv hclv hcnv hcc hiv hPv hQv
    hPW hQW hsgv hsg hCT hit hC hF hRoom
  obtain ⟨cs, fct, gct, hct⟩ := hCT
  set R := rhoPlus (k + 1) q
  set S := ySz (toWord ws) + i + pre.length + ℓ
  set C := (ws.drop cl).take cn
  have hRS := room_ge hRoom
  have hSq := room_sq hRoom
  have hSW : 65536 * (S + 1) ≤ W := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hRS
  have hRW : 65536 * (R + 1) ≤ W := by
    have := Nat.mul_le_mul_left 65536 (Nat.le_mul_of_pos_left (R + 1) (show 0 < S + 1 by omega))
    rw [← Nat.mul_assoc] at this; exact le_trans this hRS
  have hws : (toWord ws).length = ws.length + total ws + 1 := by
    rw [toWord_words, List.length_cons, Words.length_frames]
  have hySw : (toWord ws).length + maxEntry (toWord ws) + 1 + i + pre.length + ℓ ≤ S := by
    simp only [S, ySz]; omega
  have hTB : total ws + ws.length + 10 ≤ W := by omega
  have hent : ∀ n (hn : n < ws.length), ∀ u ∈ ws[n], u + 1 ≤ S := fun n hn u hu => by
    have := le_maxEntry (mem_toWord_of hn hu); omega
  have hentW : ∀ n (hn : n < ws.length), ∀ u ∈ ws[n], u ≤ W := fun n hn u hu => by
    have := hent n hn u hu; omega
  have hitw : ws[ow] = p :: g :: k :: (q + 1) :: ℓ :: toWord t := by rw [hit]; rfl
  have bk : k + 1 ≤ S := hent ow how k (by rw [hitw]; simp)
  have bq : q + 2 ≤ S := hent ow how (q + 1) (by rw [hitw]; simp)
  have bl : ℓ + 1 ≤ S := by omega
  -- the colors
  obtain ⟨τ1, r1, cP1, cQ1, P1, Q1, f1, a1, o1, i1⟩ := colSet_run (B := W + 1) hw hoc hct hocv hPv hQv
    (by omega) (by omega) (by omega) (fun u hu => by have := hentW oc hoc u hu; omega)
  have hw1 : WordsAt ws τ1 := hw.of_arrs (by rw [a1]) (by rw [a1]) (by rw [a1])
  -- the header
  obtain ⟨τ2, r2, H2, pc2, f2, a2, o2, i2⟩ := exHdr_run (W := W) hw1 how hit
    (by rw [f1 "ow" (by decide), howv]) (by omega) (fun u hu => by have := hent ow how u hu; omega) (by omega)
    (by omega)
  -- the extensions
  have hoff := off_add_le how
  set b := off ws ow
  have hd0 := drop_off hw how
  have hlt : ws[ow].length = (toWord t).length + 5 := by rw [hitw]; simp
  have hd5 : (τ.arrs "a").drop (b + 5) = toWord t ++ (τ.arrs "a").drop (b + ws[ow].length) := by
    rw [show (τ.arrs "a").drop (b + 5) = ((τ.arrs "a").drop b).drop 5 by rw [List.drop_drop], hd0,
      List.drop_append_of_le_length (by omega), show ws[ow].drop 5 = toWord t by rw [hitw]; rfl]
  have hvt : ∀ v ∈ toWord t, v < W + 1 := fun v hv => by
    have := hent ow how v (by rw [hitw]; simp [hv]); omega
  obtain ⟨τ3, r3, te3, tne3, hdE, f3, a3, o3, i3⟩ := exSkip_run (W := W) (X := τ.arrs "a") (b := b) (t := t)
    (by rw [a2, a1]) hd5 H2.b0 (by omega) hvt
  set A := (Node.atoms t).words
  set E := (Node.exts t).words
  set e := b + 5 + (toWord A).length
  set L := (toWord E).length
  have hAE : (toWord t).length = (toWord A).length + L := by rw [toWord_node_succ]; simp [A, E, L]
  have hEL : E.length < L := by simp only [L]; rw [toWord_words, List.length_cons, Words.length_frames]; omega
  have hFE : (frames E).length + 1 = L := by simp only [L]; rw [toWord_words]; simp
  have hvE : ∀ v ∈ toWord E, v < W + 1 := fun v hv => hvt v (by rw [toWord_node_succ]; exact List.mem_append_right _ hv)
  have hE2 : ∀ ew ∈ E, ∃ (g' : ℕ) (c : Node q (ℓ + 1)), ew = g' :: toWord c := by
    intro ew hew
    obtain ⟨x, -, rfl⟩ := (mem_words (S := Node.exts t)).1 hew
    exact ⟨x.1.val, x.2, toWord_ext x⟩
  have hE1 : ∀ ew ∈ E, 1 ≤ ew.length := fun ew hew => by
    obtain ⟨g', c, rfl⟩ := hE2 ew hew; simp
  -- facts at τ3
  have v3 : ∀ y, y ∉ colV → y ∉ hdrV → y ∉ skipV → τ3.vars y = τ.vars y := fun y h1 h2 h3 => by
    rw [f3 y h3, f2 y h2, f1 y h1]
  have k23 : ∀ y, y ∉ skipV → τ3.vars y = τ2.vars y := f3
  have k12 : ∀ y, y ∉ skipV → y ∉ hdrV → τ3.vars y = τ1.vars y := fun y h1 h2 => by rw [f3 y h1, f2 y h2]
  have arr3 : τ3.arrs = τ.arrs := by rw [a3, a2, a1]
  set Dw := dwOf P Q sg ws[oc]
  have hcP : Dw.cP = decide (P ∈ cs) := by simp only [Dw, dwOf, hct, inCT_flatMap]
  have hcQ : Dw.cQ = decide (Q ∈ cs) := by simp only [Dw, dwOf, hct, inCT_flatMap]
  have F3 : Filled "OB" "po" pre τ3 := hF.congr (v3 _ (by decide) (by decide) (by decide)) (by rw [arr3])
  -- part 1
  have hframes1 := frames_map_oldW i k q ℓ E hE1
  obtain ⟨τ4, r4, F4, c4, o4⟩ := part1_run (W := W) (i := i) (k := k) (q := q) (ℓ := ℓ) (c₀ := 0)
    (by rw [arr3]) hdE te3 tne3 hE1 (by rw [v3 _ (by decide) (by decide) (by decide), hiv])
    (by rw [k23 _ (by decide), H2.h0]) (by rw [k23 _ (by decide), H2.h1]) (by rw [k23 _ (by decide), H2.h2]) F3
    (by rw [k23 _ (by decide), pc2]) (by rw [arr3, hA]) (by rw [arr3, hA]) (by omega) hvE
    (by omega) ⟨by omega, by omega, by omega, by omega⟩ (by omega)
  -- part 2
  have k34 : ∀ y ∈ ["ii", "th0", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL", "tqq", "tl1", "cl",
      "cn", "te", "tne"], y ∉ p1V := by decide
  have hcap2 : (pre ++ frames (E.map (oldW i k q ℓ))).length + ℓ * (5 * L) ≤ W := by
    rw [List.length_append, hframes1]
    have h1 : ℓ * L ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
    have h2 : 65536 * ((S + 1) * (S + 1)) = 65536 * (S * S) + 131072 * S + 65536 := by ring
    have h3 : ℓ * (5 * L) = 5 * (ℓ * L) := by ring
    omega
  have g4 : ∀ y ∈ ["ii", "th0", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL", "tqq", "tl1", "cl",
      "cn", "te", "tne"], τ4.vars y = τ3.vars y := fun y hy => o4.vars y (k34 y hy)
  have hES : ℓ * (E.length + 1) ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
  have hsq : 65536 * ((S + 1) * (S + 1)) = 65536 * (S * S) + 131072 * S + 65536 := by ring
  obtain ⟨τ5, r5, F5, c5, o5⟩ := part2_run (W := W) (Dw := Dw) (R := R) (i := i) (k := k) (q := q) (ℓ := ℓ)
    (c₀ := 0 + E.length) (by rw [o4.arrs _ (by decide), arr3]) hdE
    (by rw [g4 "te" (by simp), te3]) (by rw [g4 "tne" (by simp), tne3]) hE2
    (by rw [g4 "ii" (by simp), v3 _ (by decide) (by decide) (by decide), hiv])
    (by rw [g4 "th0" (by simp), k23 _ (by decide), H2.h0]) (by rw [g4 "th1" (by simp), k23 _ (by decide), H2.h1])
    (by rw [g4 "th2" (by simp), k23 _ (by decide), H2.h2])
    (by rw [g4 "tP" (by simp), k12 _ (by decide) (by decide), P1]; rfl)
    (by rw [g4 "tQ" (by simp), k12 _ (by decide) (by decide), Q1]; rfl)
    (by rw [g4 "tcP" (by simp), k12 _ (by decide) (by decide), cP1, hcP])
    (by rw [g4 "tcQ" (by simp), k12 _ (by decide) (by decide), cQ1, hcQ])
    (by rw [g4 "ti2" (by simp), k23 _ (by decide), H2.i2]) (by rw [g4 "ts" (by simp), k23 _ (by decide), H2.s])
    (by rw [g4 "tL" (by simp), k23 _ (by decide), H2.L]) F4 c4
    (by rw [o4.len, arr3, hA]) (by rw [o4.arrs _ (by decide), arr3, hA]) (by omega) hvE hcap2
    ⟨by omega, by omega, by omega, by omega⟩ (by omega) (by simp only [Dw, dwOf]; omega)
    (by simp only [Dw, dwOf]; omega) (by omega)
  -- part 3
  have hoG : ∀ ew ∈ E, (frames (oldG Dw R i k q ℓ ew)).length ≤ ℓ * (ew.length + 5) := fun ew hew => by
    rw [oldG, length_frames_oldG]
    have h1 := length_guardW_le Dw R ℓ (listWords (childW k q ℓ ew) 3) (childW k q ℓ ew)
    have h2 : (childW k q ℓ ew).length + 3 = ew.length + 5 := by
      have := hE1 ew hew; simp [childW]; omega
    rw [h2]; exact Nat.mul_le_mul_right _ h1
  have hfr2 := exFrames_flatMap_le ℓ (oldG Dw R i k q ℓ) E hoG
  have hlen2 := length_flatMap_le ℓ (oldG Dw R i k q ℓ) E (fun ew _ => by
    rw [oldG, List.length_map]; exact length_guardW_le _ _ _ _ _)
  have g5 : ∀ y ∈ ["ii", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL", "tqq", "tl1", "cl", "cn"],
      τ5.vars y = τ3.vars y := fun y hy => by
    rw [o5.vars y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> decide), g4 y (by simp at hy ⊢; tauto)]
  have arr5 : ∀ b, b ≠ "OB" → τ5.arrs b = τ.arrs b := fun b hb => by rw [o5.arrs b hb, o4.arrs b hb, arr3]
  have hT2 : total ws * ℓ ≤ S * S := by
    have := Nat.mul_le_mul (show total ws ≤ S by omega) (show ℓ ≤ S by omega); linarith
  obtain ⟨τ6, r6, F6, c6, o6⟩ := part3_run (W := W) (Dw := Dw) (R := R) (i := i) (q := q) (ℓ := ℓ)
    (c₀ := 0 + E.length + (E.flatMap (oldG Dw R i k q ℓ)).length)
    (hw.of_arrs (arr5 _ (by decide)) (arr5 _ (by decide)) (arr5 _ (by decide)))
    (by rw [g5 "cl" (by simp), v3 _ (by decide) (by decide) (by decide), hclv])
    (by rw [g5 "cn" (by simp), v3 _ (by decide) (by decide) (by decide), hcnv]) hcc hC
    (by rw [g5 "ii" (by simp), v3 _ (by decide) (by decide) (by decide), hiv])
    (by rw [g5 "tqq" (by simp), k23 _ (by decide), H2.qq]) (by rw [g5 "tl1" (by simp), k23 _ (by decide), H2.l1])
    (by rw [g5 "th1" (by simp), k23 _ (by decide), H2.h1]) (by rw [g5 "th2" (by simp), k23 _ (by decide), H2.h2])
    (by rw [g5 "tP" (by simp), k12 _ (by decide) (by decide), P1]; rfl)
    (by rw [g5 "tQ" (by simp), k12 _ (by decide) (by decide), Q1]; rfl)
    (by rw [g5 "tcP" (by simp), k12 _ (by decide) (by decide), cP1, hcP])
    (by rw [g5 "tcQ" (by simp), k12 _ (by decide) (by decide), cQ1, hcQ])
    (by rw [g5 "ti2" (by simp), k23 _ (by decide), H2.i2]) (by rw [g5 "ts" (by simp), k23 _ (by decide), H2.s])
    (by rw [g5 "tL" (by simp), k23 _ (by decide), H2.L]) F5 c5
    (by rw [o5.len, o4.len, arr3, hA]) (by rw [arr5 _ (by decide), hA]) hTB hentW
    (by
      simp only [List.length_append]
      rw [hframes1]
      have h3 : ℓ * ((frames E).length + 4 * E.length) ≤ 5 * (S * S) := by
        have := Nat.mul_le_mul (show ℓ ≤ S by omega) (show (frames E).length + 4 * E.length ≤ 5 * S by omega)
        linarith
      have h4 : ℓ * (4 * total ws + 4 * ws.length) ≤ 8 * (S * S) := by
        have := Nat.mul_le_mul (show ℓ ≤ S by omega) (show 4 * total ws + 4 * ws.length ≤ 8 * S by omega)
        linarith
      omega)
    ⟨by omega, by omega, by omega⟩
    (by
      have : ℓ * (cn + 1) ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
      have : ℓ * E.length ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
      omega)
    (by simp only [Dw, dwOf]; omega) (by simp only [Dw, dwOf]; omega) (by omega)
  -- the result
  have hparts := exW_parts Dw k q ℓ i t C
  refine ⟨τ6, ?_, ?_, ?_, ?_⟩
  · unfold exCmd
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono ?_
    have hTC : total C ≤ total ws := total_sub ((List.take_sublist _ _).trans (List.drop_sublist _ _))
    have hLb : L ≤ ws[ow].length := by omega
    have hEb : E.length ≤ ws[ow].length := by omega
    exact ex_cost (b := ws[ow].length + ℓ + total C + cn + R + 1) (ℓ := ℓ) (R := R) (L := L)
      (Lt := (toWord t).length) (nE := E.length) (TC := total C) (cn := cn) (nC := ws[oc].length)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [hparts, frames_append, frames_append, ← List.append_assoc, ← List.append_assoc]; exact F6
  · have hl := congrArg List.length hparts
    simp only [List.length_map, List.length_append] at hl
    rw [c6, hl, Nat.zero_add]
  · have hsub : ∀ y, y ∉ exV → y ∉ colV ∧ y ∉ hdrV ∧ y ∉ skipV ∧ y ∉ p1V ∧ y ∉ p2V ∧ y ∉ p3V := by
      intro y hy; simp only [exV, List.mem_append, not_or] at hy; tauto
    refine ⟨fun y hy => ?_, fun b hb => ?_, fun b => ?_, ?_, ?_⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsub y hy
      rw [o6.vars y h6, o5.vars y h5, o4.vars y h4, v3 y h1 h2 h3]
    · have : b ≠ "OB" := by intro h; subst h; simp [keepA] at hb
      rw [o6.arrs b this, arr5 b this]
    · by_cases h : b = "OB"
      · subst h; rw [o6.len, o5.len, o4.len, arr3]
      · rw [o6.arrs b h, arr5 b h]
    · rw [o6.out, o5.out, o4.out, o3, o2, o1]
    · rw [o6.inp, o5.inp, o4.inp, i3, i2, i1]

/-- A layout for the expansion. -/
def exLayout : Lax808846Proofs.Compile.Layout :=
  ⟨exV ++ ["W", "oc", "ow", "cl", "cn", "ii", "gP", "gQ"], ["a", "st", "ln", "OB"], 6⟩

theorem exCmd_ok : Lax808846Proofs.Compile.Com.Ok exLayout exCmd :=
  StpRam.comOkB_sound _ _ (by decide)

end Lax185574Proofs.ResolveRam.Glue
