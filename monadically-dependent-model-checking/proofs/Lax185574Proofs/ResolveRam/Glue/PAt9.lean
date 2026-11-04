import Lax185574Proofs.ResolveRam.Glue.PAt8
import Lax185574Proofs.StpRam.GlueOk

/-!
The atom words of a tree in lem:resolve-lift: the command `atCmd` and
its specification `AtSpec` (`atCmd_spec`).

`atCmd` reads the header of the tree (`atHdr`) and the color table
(`atSet`), runs the six loops over the candidates in the order of
`candW_eq`, each emitting the candidates that pass `newAtomW`, and
writes the count in front of the frames (`patch`). `atCmd_ok`: the
compiler accepts the command for the layout `atLayout`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The cost bound of the atom words, by powers of the base. -/
theorem at_cost {b nC c ℓ A Rm R : ℕ} (hb : 1 ≤ b) (hℓ : ℓ ≤ b) (hA : A ≤ b) (hRm : Rm ≤ R)
    (hR : R + 1 ≤ b) (hc : c ≤ nC) :
    (40 * R + 100) + ((40 * nC + 140) + ((ℓ * (ℓ * (70 * A + 1 + 138) + 14) + 6) +
      ((ℓ * (ℓ * (70 * A + (420 * A + 400) + 138) + 14) + 6) +
      ((ℓ * (ℓ * (70 * A + (420 * A + 400) + 138) + 14) + 6) +
      ((c * (ℓ * (70 * A + 139) + 21) + 6) +
      (((Rm + 1) * (ℓ * (ℓ * (70 * A + hopK (A + A) Rm + 148) + 14) + 16) + 8) +
      (((R + 1) * (c * (ℓ * (70 * A + hopK (A + A) R + 158) + 40) + 16) + 8) + 3))))))) ≤
      40000 * (nC + 1) * b ^ 6 := by
  have h1 : hopK (A + A) Rm ≤ hopK (b + b) b := by unfold hopK; gcongr <;> omega
  have h2 : hopK (A + A) R ≤ hopK (b + b) b := by unfold hopK; gcongr <;> omega
  calc _ ≤ (40 * b + 100) + ((40 * nC + 140) + ((b * (b * (70 * b + 1 + 138) + 14) + 6) +
      ((b * (b * (70 * b + (420 * b + 400) + 138) + 14) + 6) +
      ((b * (b * (70 * b + (420 * b + 400) + 138) + 14) + 6) +
      ((nC * (b * (70 * b + 139) + 21) + 6) +
      (((b + 1) * (b * (b * (70 * b + hopK (b + b) b + 148) + 14) + 16) + 8) +
      (((b + 1) * (nC * (b * (70 * b + hopK (b + b) b + 158) + 40) + 16) + 8) + 3))))))) := by
        gcongr <;> omega
    _ ≤ 40000 * (nC + 1) * b ^ 6 := by
        unfold hopK
        have p1 : b ≤ b ^ 6 := by
          calc b = b ^ 1 := (pow_one b).symm
            _ ≤ b ^ 6 := Nat.pow_le_pow_right hb (by norm_num)
        have p2 : b ^ 2 ≤ b ^ 6 := Nat.pow_le_pow_right hb (by norm_num)
        have p3 : b ^ 3 ≤ b ^ 6 := Nat.pow_le_pow_right hb (by norm_num)
        have p4 : b ^ 4 ≤ b ^ 6 := Nat.pow_le_pow_right hb (by norm_num)
        have p5 : b ^ 5 ≤ b ^ 6 := Nat.pow_le_pow_right hb (by norm_num)
        have p0 : 1 ≤ b ^ 6 := Nat.one_le_pow _ _ hb
        have q1 : nC * b ≤ nC * b ^ 6 := Nat.mul_le_mul_left _ p1
        have q2 : nC * b ^ 2 ≤ nC * b ^ 6 := Nat.mul_le_mul_left _ p2
        have q3 : nC * b ^ 3 ≤ nC * b ^ 6 := Nat.mul_le_mul_left _ p3
        have q4 : nC * b ^ 4 ≤ nC * b ^ 6 := Nat.mul_le_mul_left _ p4
        have q5 : nC * b ^ 5 ≤ nC * b ^ 6 := Nat.mul_le_mul_left _ p5
        have q0 : nC ≤ nC * b ^ 6 := Nat.le_mul_of_pos_right _ (by omega)
        ring_nf
        ring_nf at q1 q2 q3 q4 q5
        nlinarith

theorem ct_get (cs : List ℕ) (f g : ℕ → ℕ) : ∀ m < cs.length,
    (cs.flatMap fun Y => [Y, f Y, g Y])[m * 3]? = some (cs.getD m 0) ∧
    (cs.flatMap fun Y => [Y, f Y, g Y])[m * 3 + 1]? = some (f (cs.getD m 0)) ∧
    (cs.flatMap fun Y => [Y, f Y, g Y])[m * 3 + 2]? = some (g (cs.getD m 0)) := by
  induction cs with
  | nil => intro m h; simp at h
  | cons a l ih =>
    intro m hm
    cases m with
    | zero => simp
    | succ m =>
      obtain ⟨h1, h2, h3⟩ := ih m (by simpa using hm)
      have e : ∀ j, (m + 1) * 3 + j = (m * 3 + j) + 1 + 1 + 1 := fun j => by ring
      simp only [List.flatMap_cons, List.getD_cons_succ, List.cons_append, List.nil_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [show (m + 1) * 3 = m * 3 + 1 + 1 + 1 by ring]; simpa using h1
      · rw [e 1]; simpa using h2
      · rw [e 2]; simpa using h3

theorem len_flatMap_le {α : Type*} (l : List ℕ) (F : ℕ → List α) (k : ℕ) (h : ∀ x, (F x).length ≤ k) :
    (l.flatMap F).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := h a; nlinarith

theorem frames_len_le (l : List (List ℕ)) (h : ∀ w ∈ l, w.length ≤ 4) : (frames l).length ≤ 5 * l.length := by
  induction l with
  | nil => simp [frames]
  | cons a l ih =>
    have ha := h a (by simp)
    have := ih (fun w hw => h w (by simp [hw]))
    simp only [frames, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at this ⊢
    omega

theorem candW_len (k q ℓ : ℕ) (cs : List ℕ) :
    (candW k q ℓ cs).length ≤ 3 * (ℓ * (ℓ * 1)) + cs.length * (ℓ * 1) +
      (rhoMinus k q + 1) * (ℓ * (ℓ * 1)) + (rhoPlus k q + 1) * (cs.length * (ℓ * 1)) := by
  have hp : ∀ d, (pB d ℓ).length ≤ ℓ * (ℓ * 1) := fun d => by
    unfold pB
    refine le_trans (len_flatMap_le _ _ (ℓ * 1) fun i => ?_) (by simp)
    exact le_trans (len_flatMap_le _ _ 1 fun j => by simp) (by simp)
  have hc : (cB cs ℓ).length ≤ cs.length * (ℓ * 1) := by
    unfold cB
    refine le_trans (len_flatMap_le _ _ (ℓ * 1) fun i => ?_) (by simp)
    exact le_trans (len_flatMap_le _ _ 1 fun j => by simp) (by simp)
  have hd : (dB (rhoMinus k q) ℓ).length ≤ (rhoMinus k q + 1) * (ℓ * (ℓ * 1)) := by
    unfold dB
    refine le_trans (len_flatMap_le _ _ (ℓ * (ℓ * 1)) fun s => ?_) (by simp)
    refine le_trans (len_flatMap_le _ _ (ℓ * 1) fun i => ?_) (by simp)
    exact le_trans (len_flatMap_le _ _ 1 fun j => by simp) (by simp)
  have he : (eB (rhoPlus k q) cs ℓ).length ≤ (rhoPlus k q + 1) * (cs.length * (ℓ * 1)) := by
    unfold eB
    refine le_trans (len_flatMap_le _ _ (cs.length * (ℓ * 1)) fun s => ?_) (by simp)
    refine le_trans (len_flatMap_le _ _ (ℓ * 1) fun i => ?_) (by simp)
    exact le_trans (len_flatMap_le _ _ 1 fun j => by simp) (by simp)
  rw [candW_eq]
  simp only [List.length_append]
  have := hp 0; have := hp 1; have := hp 2
  omega

theorem candW_mem_len {k q ℓ : ℕ} {cs : List ℕ} : ∀ w ∈ candW k q ℓ cs, w.length ≤ 4 := by
  intro w hw
  rw [candW_eq] at hw
  simp only [pB, cB, dB, eB, List.mem_append, List.mem_flatMap, List.mem_singleton, List.mem_range] at hw
  rcases hw with ((((⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) | ⟨_, _, _, _, rfl⟩) | ⟨_, _, _, _, rfl⟩) |
    ⟨_, _, _, _, _, _, rfl⟩) | ⟨_, _, _, _, _, _, rfl⟩ <;> simp

theorem bv_one (b : Bool) : decide (bv b = 1) = b := by cases b <;> rfl

theorem bv_zero (b : Bool) : decide (bv b = 0) = !b := by cases b <;> rfl

theorem room_frames (R S : ℕ) :
    5 * (3 * (S * (S * 1)) + S * (S * 1) + (R + 1) * (S * (S * 1)) + (R + 1) * (S * (S * 1))) + S + 1 ≤
      2 ^ 16 * (R + 1) ^ 2 * (S + 1) ^ 2 := by
  have hX : S * (S * 1) ≤ (S + 1) ^ 2 := by nlinarith
  have hX1 : S + 1 ≤ (S + 1) ^ 2 := by nlinarith
  have hY : (R + 1) * (S + 1) ^ 2 ≤ (R + 1) ^ 2 * (S + 1) ^ 2 :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have hZ : (S + 1) ^ 2 ≤ (R + 1) * (S + 1) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  calc _ ≤ 5 * (3 * (S + 1) ^ 2 + (S + 1) ^ 2 + (R + 1) * (S + 1) ^ 2 + (R + 1) * (S + 1) ^ 2) +
        (S + 1) ^ 2 := by gcongr <;> nlinarith
    _ ≤ 31 * ((R + 1) * (S + 1) ^ 2) := by linarith
    _ ≤ 2 ^ 16 * ((R + 1) ^ 2 * (S + 1) ^ 2) := by linarith
    _ = _ := by ring

theorem at_sub (a b c d e f g : List String) :
    a ++ ((b ++ (((((c ++ d) ++ d) ++ e) ++ f) ++ g)) ++ []) ⊆ a ++ b ++ c ++ d ++ e ++ f ++ g := by
  intro y hy
  simp only [List.mem_append, List.not_mem_nil, or_false] at hy ⊢
  tauto

/-- **The atom words of a tree.** -/
def atCmd : Com :=
  .seq atHdr (.seq atSet (.seq (pairLoop 0 .skip) (.seq (pairLoop 1 (crossT 2 1))
    (.seq (pairLoop 2 (crossT 1 0)) (.seq colLoop (.seq dLoop (.seq eLoop patch)))))))

/-- The scalars that `atCmd` writes. -/
def atV : List String := atHV ++ atSV ++ plV [] ++ plV crV ++ clV ++ dlV ++ elV

theorem frames_prefix {L' L : List (List ℕ)} (h : L' <+: L) : (frames L').length ≤ (frames L).length := by
  obtain ⟨t, rfl⟩ := h
  simp [frames]

/-- **The specification of the atom words.** -/
theorem atCmd_spec : AtSpec atCmd atV := by
  refine ⟨40000, 6, ?_⟩
  intro W τ ws pre oc ow P Q sg p g σ hoc how hW hA hw hocv howv hPv hQv hPW hQW hsgv hsg hCT hit hF hRoom
  obtain ⟨cs, fT, gT, hct⟩ := hCT
  set R := rhoPlus σ.k σ.q with hRdef
  set Rm := rhoMinus σ.k σ.q with hRmdef
  have hRmR : Rm ≤ R := rhoMinus_le σ.k σ.q
  set S := ySz (toWord ws) + pre.length + σ.ℓ
  have hRS := room_ge hRoom
  have hSW : 65536 * (S + 1) ≤ W := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hRS
  have hRW : 65536 * (R + 1) ≤ W := by
    have := Nat.mul_le_mul_left 65536 (Nat.le_mul_of_pos_left (R + 1) (show 0 < S + 1 by omega))
    rw [← Nat.mul_assoc] at this; exact le_trans this hRS
  have hws : (toWord ws).length = ws.length + total ws + 1 := by
    rw [toWord_words, List.length_cons, Words.length_frames]
  have hySw : (toWord ws).length + maxEntry (toWord ws) + 1 + pre.length + σ.ℓ ≤ S := by
    simp only [S, ySz]; omega
  have hTB : total ws + ws.length + 4 < W + 1 := by omega
  have hentS : ∀ i (hi : i < ws.length), ∀ v ∈ ws[i], v ≤ S := fun i hi v hv => by
    have := le_maxEntry (mem_toWord_of hi hv); omega
  have hent : ∀ i (hi : i < ws.length), ∀ v ∈ ws[i], v < W + 1 := fun i hi v hv => by
    have := hentS i hi v hv; omega
  have hit' : ws[ow] = p :: g :: toWord σ := hit
  have hlen : ws[oc].length = 3 * cs.length := by rw [hct, length_ct]
  have hoffc := off_add_le hoc
  have hoffw := off_add_le how
  -- the header
  obtain ⟨τ1, r1, Rp1, Rm1, L1, p11, p21, f1, a1, o1, i1⟩ := atHdr_run hw how hit' howv hTB (hent ow how)
    (by omega) (by omega)
  have O1 : OFr τ τ1 atHV := ⟨f1, fun b _ => by rw [a1], by rw [a1], o1, i1⟩
  have hw1 : WordsAt ws τ1 := hw.of_arrs (by rw [a1]) (by rw [a1]) (by rw [a1])
  -- the setup
  obtain ⟨τ2, r2, cP2, cQ2, P2, Q2, sg2, nc2, cb2, fp2, E2, O2⟩ := atSet_run (W := W) hw1 hoc hct
    (by rw [f1 _ (by decide), hocv]) (by rw [f1 _ (by decide), hPv]) (by rw [f1 _ (by decide), hQv])
    (by rw [f1 _ (by decide), hsgv]) hPW hQW hsg hTB (hent oc hoc)
    (hF.congr (f1 "po" (by decide)) (by rw [a1])) (by rw [a1]; exact hA "OB") (by omega)
  set Xa := τ.arrs "a"
  set p₁ := off ws ow + 5
  set Dw := dwOf P Q sg ws[oc]
  have hD2 : AtD Xa p₁ Dw σ.ℓ cs.length (off ws oc) Rm R τ2 := by
    refine ⟨by rw [O2.arrs "a" (by decide), a1], by rw [O2.vars "tp1" (by decide), p11],
      by rw [O2.vars "tp2" (by decide), p21], P2, Q2, ?_, ?_, ?_, by rw [O2.vars "tL" (by decide), L1], nc2, cb2,
      by rw [O2.vars "tRm" (by decide), Rm1], by rw [O2.vars "tRp" (by decide), Rp1]⟩
    · show τ2.vars "tcP" = bv (inCT ws[oc] P)
      rw [cP2, hct, inCT_flatMap]
    · show τ2.vars "tcQ" = bv (inCT ws[oc] Q)
      rw [cQ2, hct, inCT_flatMap]
    · show τ2.vars "tsg" = bv (sg == 1)
      rw [sg2]; interval_cases sg <;> rfl
  -- the atom list
  obtain ⟨r0, hr0⟩ : ∃ r0, Xa.drop (off ws ow) = ws[ow] ++ r0 := ⟨_, drop_off hw how⟩
  have hd0 : Xa.drop (off ws ow + 2) = toWord σ ++ r0 := by
    rw [← List.drop_drop, hr0, hit']; simp
  obtain ⟨rr, hd', hlA, hmA⟩ := tree_atoms hd0
  set A := (Node.atoms σ.root).words
  have hd : Xa.drop p₁ = toWord A ++ rr := by rw [show p₁ = off ws ow + 2 + 3 by omega]; exact hd'
  have hlw : ws[ow].length = (toWord σ).length + 2 := by rw [hit']; simp
  have hAl : A.length < (toWord A).length := by
    rw [toWord_words, List.length_cons, Words.length_frames]; omega
  have hB1 : p₁ + (toWord A).length + 6 < W + 1 := by omega
  have hv : ∀ v ∈ toWord A, v < W + 1 := fun v h => hent ow how v (by rw [hit']; simp [hmA v h])
  have hℓS : σ.ℓ ≤ S := by omega
  have hcsS : cs.length ≤ S := by omega
  have hℓW : σ.ℓ ≤ W := by omega
  have hW5 : 5 ≤ W := by omega
  -- the bound on the output
  set f := newAtomW Dw A
  set Full := (candW σ.k σ.q σ.ℓ cs).filter f
  have hFull : pre.length + 1 + (frames Full).length ≤ W := by
    have h1 := frames_len_le Full (fun w hw => candW_mem_len w (List.mem_of_mem_filter hw))
    have h2 : Full.length ≤ (candW σ.k σ.q σ.ℓ cs).length := List.length_filter_le _ _
    have h3 := candW_len σ.k σ.q σ.ℓ cs
    have h4 : 3 * (σ.ℓ * (σ.ℓ * 1)) + cs.length * (σ.ℓ * 1) + (Rm + 1) * (σ.ℓ * (σ.ℓ * 1)) +
        (R + 1) * (cs.length * (σ.ℓ * 1)) ≤ 3 * (S * (S * 1)) + S * (S * 1) + (R + 1) * (S * (S * 1)) +
        (R + 1) * (S * (S * 1)) := by gcongr
    have h5 := room_frames R S
    unfold Room at hRoom
    generalize 3 * (σ.ℓ * (σ.ℓ * 1)) + cs.length * (σ.ℓ * 1) + (Rm + 1) * (σ.ℓ * (σ.ℓ * 1)) +
        (R + 1) * (cs.length * (σ.ℓ * 1)) = U at h3 h4
    generalize 3 * (S * (S * 1)) + S * (S * 1) + (R + 1) * (S * (S * 1)) + (R + 1) * (S * (S * 1)) = V at h4 h5
    generalize 2 ^ 16 * (R + 1) ^ 2 * (S + 1) ^ 2 = Z at h5 hRoom
    omega
  have hpre : ∀ L', L' <+: Full → pre.length + 1 + (frames L').length ≤ W := fun L' h => by
    have := frames_prefix h; omega
  have hsplit : Full = (pB 0 σ.ℓ).filter f ++ (pB 1 σ.ℓ).filter f ++ (pB 2 σ.ℓ).filter f ++
      (cB cs σ.ℓ).filter f ++ (dB Rm σ.ℓ).filter f ++ (eB R cs σ.ℓ).filter f := by
    simp only [Full, candW_eq, List.filter_append]; rfl
  have hOB2 : (τ2.arrs "OB").length = W + 1 := by rw [O2.len, O1.len]; exact hA "OB"
  -- the loop over `[0, i, j]`
  obtain ⟨τ3, r3, E3, O3⟩ := pairLoop_run (W := W) (d := 0) (T := .skip) (KT := 1) (VT := [])
    (fun _ _ => false) f hD2 hd hB1 hv (by omega) hℓW hW5 E2 hOB2
    (hpre _ ⟨(pB 1 σ.ℓ).filter f ++ (pB 2 σ.ℓ).filter f ++ (cB cs σ.ℓ).filter f ++ (dB Rm σ.ℓ).filter f ++
      (eB R cs σ.ℓ).filter f, by rw [hsplit]; simp⟩)
    (fun i j => by simp [f, newAtomW]) (fun i j _ _ => skip_tspec W _) (by simp)
  have hD3 := hD2.ofr O3 (plV_aN (by simp))
  have hOB3 : (τ3.arrs "OB").length = W + 1 := by rw [O3.len, hOB2]
  -- the loop over `[1, i, j]`
  obtain ⟨τ4, r4, E4, O4⟩ := pairLoop_run (W := W) (d := 1) (T := crossT 2 1) (KT := 420 * A.length + 400)
    (VT := crV) (fun i j => Dw.sg && crossW Dw A i j && !inW A [0, i, j] && !inW A [2, i, j]) f hD3 hd hB1 hv
    (by omega) hℓW hW5 E3 hOB3
    (hpre _ ⟨(pB 2 σ.ℓ).filter f ++ (cB cs σ.ℓ).filter f ++ (dB Rm σ.ℓ).filter f ++
      (eB R cs σ.ℓ).filter f, by rw [hsplit]; simp⟩)
    (fun i j => by simp [f, newAtomW])
    (fun i j hi hj => by
      rintro ρ ⟨Dρ, h1, h2⟩ hF0
      obtain ⟨τ', r', fF, o', a'⟩ := crossT_run (W := W) (d := 2) (g := 1) Dρ.a hd Dρ.p1 Dρ.P Dρ.Q Dρ.sg h1 h2
        hF0 hPW hQW (by omega) (by omega) (by omega) (by omega) hW5 (by omega) hv
      exact ⟨τ', r', by rw [fF, bv_one], o', a'⟩)
    (by decide)
  have hD4 := hD3.ofr O4 (plV_aN (by decide))
  have hOB4 : (τ4.arrs "OB").length = W + 1 := by rw [O4.len, hOB3]
  -- the loop over `[2, i, j]`
  obtain ⟨τ5, r5, E5, O5⟩ := pairLoop_run (W := W) (d := 2) (T := crossT 1 0) (KT := 420 * A.length + 400)
    (VT := crV) (fun i j => !Dw.sg && crossW Dw A i j && !inW A [0, i, j] && !inW A [1, i, j]) f hD4 hd hB1 hv
    (by omega) hℓW hW5 E4 hOB4
    (hpre _ ⟨(cB cs σ.ℓ).filter f ++ (dB Rm σ.ℓ).filter f ++ (eB R cs σ.ℓ).filter f, by rw [hsplit]; simp⟩)
    (fun i j => by simp [f, newAtomW])
    (fun i j hi hj => by
      rintro ρ ⟨Dρ, h1, h2⟩ hF0
      obtain ⟨τ', r', fF, o', a'⟩ := crossT_run (W := W) (d := 1) (g := 0) Dρ.a hd Dρ.p1 Dρ.P Dρ.Q Dρ.sg h1 h2
        hF0 hPW hQW (by omega) (by omega) (by omega) (by omega) hW5 (by omega) hv
      exact ⟨τ', r', by rw [fF, bv_zero], o', a'⟩)
    (by decide)
  have hD5 := hD4.ofr O5 (plV_aN (by decide))
  have hOB5 : (τ5.arrs "OB").length = W + 1 := by rw [O5.len, hOB4]
  -- the table
  have hXa : ∀ j < ws[oc].length, Xa[off ws oc + j]? = ws[oc][j]? := fun j hj => by
    rw [hw.a oc hoc j hj, List.getElem?_eq_getElem hj]
  have hcol : ∀ m < cs.length, Xa[off ws oc + m * 3]? = some (cs.getD m 0) ∧
      Xa[off ws oc + m * 3 + 1]? = some (Dw.tP (cs.getD m 0)) ∧
      Xa[off ws oc + m * 3 + 2]? = some (Dw.tQ (cs.getD m 0)) := by
    intro m hm
    have hY : cs.getD m 0 ∈ cs := by rw [List.getD_eq_getElem _ _ hm]; exact List.getElem_mem hm
    have htP : Dw.tP (cs.getD m 0) = fT (cs.getD m 0) := by
      show tabLook ws[oc] 0 _ = _
      rw [hct, tabLook_flatMap, if_pos hY, if_pos rfl]
    have htQ : Dw.tQ (cs.getD m 0) = gT (cs.getD m 0) := by
      show tabLook ws[oc] 1 _ = _
      rw [hct, tabLook_flatMap, if_pos hY, if_neg (by norm_num)]
    obtain ⟨e0, e1, e2⟩ := ct_get cs fT gT m hm
    refine ⟨?_, ?_, ?_⟩
    · rw [hXa _ (by omega), hct, e0]
    · rw [Nat.add_assoc, hXa _ (by omega), hct, e1, htP]
    · rw [Nat.add_assoc, hXa _ (by omega), hct, e2, htQ]
  have htab : ∀ j Y, tabLook ws[oc] j Y ≤ W := fun j Y => by
    rw [hct, tabLook_flatMap]
    split_ifs with h1 h2
    · have := hent oc hoc (fT Y) (by rw [hct]; exact List.mem_flatMap.2 ⟨Y, h1, by simp⟩); omega
    · have := hent oc hoc (gT Y) (by rw [hct]; exact List.mem_flatMap.2 ⟨Y, h1, by simp⟩); omega
    · omega
  have hcsW : ∀ Y ∈ cs, Y ≤ W := fun Y h => by
    have := hent oc hoc Y (by rw [hct]; exact List.mem_flatMap.2 ⟨Y, h, by simp⟩); omega
  have hcsW' : ∀ m, cs.getD m 0 ≤ W ∧ Dw.tP (cs.getD m 0) ≤ W ∧ Dw.tQ (cs.getD m 0) ≤ W := fun m => by
    refine ⟨?_, htab 0 _, htab 1 _⟩
    rcases Nat.lt_or_ge m cs.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hcsW _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]; omega
  -- the loop over `[3, Y, i]`
  obtain ⟨τ6, r6, E6, O6⟩ := colLoop_run (W := W) f hD5 hd hB1 hv hℓW hW5 E5 hOB5
    (hpre _ ⟨(dB Rm σ.ℓ).filter f ++ (eB R cs σ.ℓ).filter f, by rw [hsplit]; simp⟩)
    (fun m hm => (hcol m hm).1) hcsW (by omega) (fun Y i => by simp [f, newAtomW])
  have hD6 := hD5.ofr O6 (by decide)
  have hOB6 : (τ6.arrs "OB").length = W + 1 := by rw [O6.len, hOB5]
  -- the loop over `[4, s, i, j]`
  obtain ⟨τ7, r7, E7, O7⟩ := dLoop_run (W := W) f hD6 hd hB1 hv hℓW hW5 E6 hOB6
    (hpre _ ⟨(eB R cs σ.ℓ).filter f, by rw [hsplit]; simp⟩) hPW hQW (by omega)
    (fun s i j => by simp [f, newAtomW])
  have hD7 := hD6.ofr O7 (by decide)
  have hOB7 : (τ7.arrs "OB").length = W + 1 := by rw [O7.len, hOB6]
  -- the loop over `[5, s, Y, i]`
  obtain ⟨τ8, r8, E8, O8⟩ := eLoop_run (W := W) f hD7 hd hB1 hv hℓW hW5 E7 hOB7
    (hpre _ ⟨[], by rw [hsplit]; simp⟩) hcol hcsW' (by omega) hPW hQW (by omega)
    (fun s Y i => by simp [f, newAtomW])
  have hL8 : [] ++ (pB 0 σ.ℓ).filter f ++ (pB 1 σ.ℓ).filter f ++ (pB 2 σ.ℓ).filter f ++
      (cB cs σ.ℓ).filter f ++ (dB Rm σ.ℓ).filter f ++ (eB R cs σ.ℓ).filter f = Full := by
    rw [hsplit, List.nil_append]
  rw [hL8] at E8
  -- the count
  have O38 := (((((O3.trans O4).trans O5).trans O6).trans O7).trans O8)
  obtain ⟨τ9, r9, F9, O9⟩ := patch_run (W := W) E8.1 (by rw [O38.vars "fp" (by decide), fp2]) E8.2
    (by simp only [List.length_append, List.length_singleton]; have := hFull; omega)
  have hres : Full = (candW σ.k σ.q σ.ℓ (ctCols ws[oc])).filter
      (newAtomW (dwOf P Q sg ws[oc]) (listWords (toWord σ) 3)) := by
    rw [hct, ctCols_flatMap, listWords_tree_root, ← hct]
  refine ⟨τ9, ?_, by rw [← hres]; exact F9, ?_⟩
  · unfold atCmd
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
      (Run.seq r8 r9)))))))).mono ?_
    have hAw : A.length ≤ ws[ow].length := by omega
    exact at_cost (b := ws[ow].length + σ.ℓ + R + 1) (nC := ws[oc].length) (by omega) (by omega)
      (by omega) hRmR (by omega) (by omega)
  · have Oall := (O1.trans ((O2.trans O38).trans O9)).mono (ys := atV) (at_sub _ _ _ _ _ _ _)
    refine ⟨Oall.vars, fun b hb => Oall.arrs b (by intro h; subst h; simp [keepA] at hb), fun b => ?_,
      Oall.out, Oall.inp⟩
    by_cases h : b = "OB"
    · subst h; exact Oall.len
    · rw [Oall.arrs b h]

/-- A layout for the atom words. -/
def atLayout : Lax808846Proofs.Compile.Layout :=
  ⟨atV ++ ["W", "oc", "ow", "gP", "gQ", "gS"], ["a", "st", "ln", "OB"], 6⟩

theorem atCmd_ok : Lax808846Proofs.Compile.Com.Ok atLayout atCmd :=
  StpRam.comOkB_sound _ _ (by decide)

end Lax185574Proofs.ResolveRam.Glue
