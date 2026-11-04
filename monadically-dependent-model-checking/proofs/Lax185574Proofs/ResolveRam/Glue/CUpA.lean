import Lax185574Proofs.ResolveRam.Glue.CUpS
import Lax185574Proofs.ResolveRam.Glue.CUpK
import Lax185574Proofs.ResolveRam.Glue.CComp

/-!
The case after the canonical form of the atom words of an item with
children (position `up d i 0`, `d < q₀`): the answer is stored as the atom
words of the state, and the query of the children words of the item is
written (`bUpA_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- The fixed answers in front of the answer of a canonical form. -/
noncomputable def plK : ℕ := yA0.length + yB0.length + yC0.length

/-- The fixed answers around the answer of a canonical form. -/
noncomputable def dlK : ℕ := yA0.length + yB0.length + yC0.length + yF0.length

theorem dLen_canon (ws : List (List ℕ)) : dLen (.canon ws) = dlK := by
  simp [dLen, dlK]; omega

theorem preLen_canon (ws : List (List ℕ)) : preLen (.canon ws) = plK := rfl

/-- Entry `e` of the lengths of the levels. -/
def eLL (e : Expr) : Expr := .get "a" (.add (.get "st" (.lit 3)) e)

/-- The item word, the item words of the level below and their output words. -/
def upA1 : List (String × Expr) :=
  [("ow", .add (.add (.add (.lit 4) (.var "nSG")) (.var "oL")) (.var "ii")),
    ("kl", .add (.add (.add (.lit 4) (.var "nSG")) (.var "oL")) (eLL (.var "dd"))),
    ("kn", eLL (.add (.var "dd") (.lit 1))),
    ("ol", .add (.add (.lit 4) (.var "nSG")) (.var "nLV"))]

/-- The scalars of the new head after the atom words. -/
def hdA : List (String × Expr) :=
  [("Nt", .lit 1), ("Nw", .lit 0), ("Nph", .lit 2), ("Nd", .var "dd"), ("Ni", .var "ii"), ("Nm", .lit 1),
    ("NSG", .var "nSG"), ("NFA", .lit 0), ("NCO", .lit 0), ("NLV", .var "nLV"), ("qk", .lit 3), ("po", .lit 0)]

/-- The plan `psRep2`. -/
def plR2 : List (Expr × Expr) :=
  [(.lit 0, .lit 2), (.add (.var "m0") (.lit 1), .lit 1), (.lit 3, .sub (.var "m0") (.lit 3))]

/-- The case after the atom words of an item with children. -/
noncomputable def bUpA : Com :=
  .seq (.assign "m0" (.var "m")) (.seq apE (.seq (apY plK dlK) (.seq sumLL (.seq (asgs upA1)
    (.seq (asgs hdA) (.seq (winC (.eq (.var "dd") (.lit 0))
      (.eq (.add (.var "ii") (.lit 1)) (eLL (.lit 0)))) (.seq kdT (stPlan plR2))))))))

/-- The constant of the cost of the children words. -/
noncomputable def cKd : ℕ := kdT_run.choose

/-- The exponent of the cost of the children words. -/
noncomputable def aKd : ℕ := kdT_run.choose_spec.choose

theorem kdT_spec : ∀ {W R iw i kl kn ol p g k q ℓ : ℕ} {t : Node (q + 1) ℓ} {L : List (List ℕ)}
    {b : List ℕ} {τ : Env}
    (hW : τ.vars "W" = W) (hW24 : 2 ^ 24 < W) (har : ArrW W τ) (hlt : EnvLt (W + 1) τ)
    (hL : Lib L τ) (hrR : τ.vars "rR" = min R W) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length)
    (hy : SegAt "y" 0 b τ) (hov : τ.vars "ovf" = 0) (how : τ.vars "ow" = iw) (hiw : iw < L.length)
    (hitem : L[iw] = itemW ((p, g), ⟨k, q + 1, ℓ, t⟩)) (hii : τ.vars "ii" = i) (hi : i ≤ L.length)
    (hkl : τ.vars "kl" = kl) (hkn : τ.vars "kn" = kn) (hol : τ.vars "ol" = ol) (hkl' : kl + kn ≤ L.length)
    (hol' : ol + kn ≤ L.length) (hR : 1 ≤ R),
    ∃ τ' K, Run (W + 1) kdT τ τ' K ∧
      K ≤ kKdT L b (kdQW L q ℓ i kl kn ol)
        (cKd * (kn + total ((L.drop kl).take kn) + total ((L.drop ol).take kn) + 1) * (L[iw].length + 1) ^ aKd) ∧
      (τ'.vars "ovf" = 0 → Lib (L ++ [kdQW L q ℓ i kl kn ol]) τ' ∧ τ'.vars "oe" = L.length ∧
        τ'.vars "po" = 0) ∧
      (∀ y, y ∉ kdTV → τ'.vars y = τ.vars y) ∧ τ'.arrs "y" = τ.arrs "y" ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp ∧
      (∀ Lb : List (List ℕ), (L ++ [kdQW L q ℓ i kl kn ol]).Sublist Lb →
        BigRoom W R Lb b (τ.vars "nx") (τ.vars "mw") → τ'.vars "ovf" = 0) :=
  kdT_run.choose_spec.choose_spec

/-- The cost of the case after the atom words, without the children words. -/
def kUpA (b : List ℕ) (d : ℕ) : ℕ := b.length * 18 + d * 20 + 3000

theorem planW_append_of {L M : List (List ℕ)} {ps : List (ℕ × ℕ)} (h : ∀ p ∈ ps, p.1 + p.2 ≤ L.length) :
    planW (L ++ M) ps = planW L ps := by
  unfold planW
  exact List.flatMap_congr fun p hp => rng_append_left (h p hp)

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- An item of a level above the last as a tree of positive depth. -/
theorem itm_succ (hk : 1 ≤ k₀) {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    ∃ q ℓ, ∃ t : Node (q + 1) ℓ, (itm G P Q s k₀ q₀ d i).2 = ⟨k₀ + d, q + 1, ℓ, t⟩ ∧ q + 1 = q₀ - d := by
  obtain ⟨ℓ, t, hx⟩ := lvR_shape G P Q s k₀ q₀ hk hd.le hi
  obtain ⟨q, hq⟩ : ∃ q, q₀ - d = q + 1 := ⟨q₀ - d - 1, by omega⟩
  revert t
  rw [hq]
  intro t hx
  exact ⟨q, ℓ, t, by rw [itm_eq G P Q s k₀ q₀ hi, hx], rfl⟩

theorem winOf_upA {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    winOf G P Q s k₀ q₀ (.up d i 1) =
      if d = 0 ∧ i + 1 = (lvR G P Q s k₀ q₀ 0).length then (xIn G k₀ q₀ P Q s).length else 0 := by
  have hn : ¬ (1 + 1 < nUp q₀ d) := by unfold nUp; split_ifs <;> omega
  unfold winOf
  simp only [next, if_neg hn]
  by_cases h0 : d = 0
  · subst h0
    by_cases h1 : i + 1 < (lvR G P Q s k₀ q₀ 0).length
    · have h2 : i + 1 ≠ (lvR G P Q s k₀ q₀ 0).length := by omega
      simp [h1, h2]
    · have h2 : i + 1 = (lvR G P Q s k₀ q₀ 0).length := by omega
      simp [h1, h2]
  · by_cases h1 : i + 1 < (lvR G P Q s k₀ q₀ d).length
    · simp [h1, h0]
    · simp [h1, h0]

theorem case_upA {d i : ℕ} :
    planW ((swAt G P Q s k₀ q₀ (.up d i 0)).ws ++
        [[], canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2), realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 1))])
        (psRep2 (swAt G P Q s k₀ q₀ (.up d i 0)).ws.length) =
      (swAt G P Q s k₀ q₀ (.up d i 1)).ws := by
  have h4 := length_SW_ws (swAt G P Q s k₀ q₀ (.up d i 0))
  rw [show ∀ A B C : List ℕ, ∀ L : List (List ℕ), L ++ [A, B, C] = (L ++ [A, B]) ++ [C] by simp,
    planW_append_of (by intro p hp; simp [psRep2] at hp; rcases hp with rfl | rfl | rfl <;> simp <;> omega),
    case_atoms]

set_option maxHeartbeats 3200000 in
/-- **The case after the atom words of an item with children.** -/
theorem bUpA_ok (hk : 1 ≤ k₀) {d i W : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    BodyCall bUpA W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.up d i 0))
      (swAt G P Q s k₀ q₀ (.up d i 0)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.up d i 0)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 0)))
      ((swAt G P Q s k₀ q₀ (.up d i 0)).ws ++
        [[], canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2), realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 1))])
      (psRep2 (swAt G P Q s k₀ q₀ (.up d i 0)).ws.length)
      (kindOf (callOf G P Q s k₀ q₀ (.up d i 1))) (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 1)))
      (tagOf G P Q s k₀ q₀ (.up d i 1)) (winOf G P Q s k₀ q₀ (.up d i 1)) (scW G P Q s k₀ q₀ (.up d i 1))
      (kUpA (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 0))) d +
        kKdT ((swAt G P Q s k₀ q₀ (.up d i 0)).ws ++ [[], canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2)])
          (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 0))) (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 1)))
          (cKd * ((lvR G P Q s k₀ q₀ (d + 1)).length + total (lvW G P Q s k₀ q₀ (d + 1)) +
            total (outW G P Q s k₀ q₀ (d + 1)) + 1) * ((itemW (itm G P Q s k₀ q₀ d i)).length + 1) ^ aKd)) := by
  intro τ0 P0 hov hkq
  set σ := (itm G P Q s k₀ q₀ d i).2
  have hnu : nUp q₀ d = 2 := by simp [nUp, hd]
  have hc0 : callOf G P Q s k₀ q₀ (.up d i 0) = .canon (atomQ G P Q s k₀ q₀ σ) := by
    rw [callOf_up' hi (by omega)]; simp [σ]
  have hc1 : callOf G P Q s k₀ q₀ (.up d i 1) = .canon (kidQ G P Q s k₀ q₀ d i σ) := by
    rw [callOf_up' hi (by omega)]; simp [σ]
  rw [hc0] at P0 ⊢
  obtain ⟨q, ℓ, t, hσ, hq⟩ := itm_succ G P Q s k₀ q₀ hk hd hi
  set R := rhoPlus (k₀ + 1) q₀ + 2
  have hR : 1 ≤ R := by omega
  set w0 := swAt G P Q s k₀ q₀ (.up d i 0)
  set ws := w0.ws
  set b := rY G k₀ q₀ (.canon (atomQ G P Q s k₀ q₀ σ))
  set Y := canonW (atomQ G P Q s k₀ q₀ σ)
  set KQ := realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 1))
  have hKQ : KQ = toWord (kidW q ℓ i ((lvR G P Q s k₀ q₀ (d + 1)).map (·.1)) (outW G P Q s k₀ q₀ (d + 1))) := by
    simp only [KQ, hc1, realQ_canon, σ, hσ, kidQ_words]
  have hroom : RoomOK W R τ0 ws b := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS := room_bound hroom hR
  obtain ⟨hS1, hS2, hS3, hS4⟩ := sOfV_ge (τ := τ0) (ws := ws) (b := b)
  have hq0W : q₀ + 2 ≤ W := by
    have h4 : 4 ≤ ws.length := length_SW_ws w0
    have h1 := len_le_total (L := ws) (i := 3) (by omega)
    have h3 : ws[3] = llW G P Q s k₀ q₀ q₀ := by
      rw [← LL_up G P Q s k₀ q₀ d i 0]; simp [ws, w0, SW.ws_eq]
    rw [h3, length_llW] at h1
    omega
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hl0 := P0.hlt
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.up d i 0)).getD j 0 := P0.hsc
  have hdd : τ0.vars "dd" = d := by simpa [scR, scW, curW] using hsc 10 (by omega)
  have hii : τ0.vars "ii" = i := by simpa [scR, scW, curW] using hsc 11 (by omega)
  have hSG : τ0.vars "nSG" = w0.SG.length := by simpa [scR, scW, curW] using hsc 13 (by omega)
  have hLV : τ0.vars "nLV" = w0.LV.length := by simpa [scR, scW, curW] using hsc 16 (by omega)
  have hnx : τ0.vars "nx" = (xIn G k₀ q₀ P Q s).length := by simpa [scR, scW, curW] using hsc 2 (by omega)
  have hwsl : ws.length = 4 + w0.SG.length + w0.LV.length + w0.OU.length := by
    simp only [ws, SW.ws, List.length_append, List.length_cons, List.length_nil, FA_up, CO_up, w0]; omega
  have hLVl : w0.LV.length = offL G P Q s k₀ q₀ (q₀ + 1) := by rw [LV_up, length_lvsW]
  have hoff1 : offL G P Q s k₀ q₀ (d + 1) + (lvR G P Q s k₀ q₀ (d + 1)).length ≤ w0.LV.length := by
    rw [hLVl, ← offL_succ]
    exact offL_mono G P Q s k₀ q₀ (by omega)
  have hOUl : (lvR G P Q s k₀ q₀ (d + 1)).length ≤ w0.OU.length := by
    simp [w0, swAt, hd, length_outW]
  have hoffd : offL G P Q s k₀ q₀ (d + 1) = offL G P Q s k₀ q₀ d + (lvR G P Q s k₀ q₀ d).length :=
    offL_succ G P Q s k₀ q₀ d
  -- step 1: m0
  set τ1 := τ0.setVar "m0" ws.length
  have r1 : Run (W + 1) (.assign "m0" (.var "m")) τ0 τ1 2 := Run.assign (ev_var P0.hlib.m (by omega))
  have L1 : Lib ws τ1 := P0.hlib.of (by simp [τ1]) (by simp [τ1]) rfl rfl rfl
  have ar1 : ArrW W τ1 := P0.harr
  -- step 2: the empty word
  obtain ⟨τ2, r2, L2, f2, a2, ar2, o2, i2⟩ := apE_run L1 ar1 (by omega)
  -- step 3: the answer
  have hyb : SegAt "y" 0 b τ2 := fun j hj => by rw [a2 "y" (by decide)]; exact P0.hy j hj
  have hbv : ∀ v ∈ b, v ≤ W := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have := P0.hy j hj
    have := hl0.arrs "y" _ (List.mem_of_getElem? (by simpa using this))
    omega
  obtain ⟨pre, post, hsp, hpre, hpp⟩ := rY_split G k₀ q₀ (.canon (atomQ G P Q s k₀ q₀ σ))
  have hdl : dlK ≤ b.length := by
    rw [← dLen_canon (atomQ G P Q s k₀ q₀ σ), ← hpp]; simp only [b, hsp, List.length_append]; omega
  have hpd : plK ≤ dlK := by unfold plK dlK; omega
  obtain ⟨τ3, r3, L3, f3, a3, ar3, o3, i3⟩ := apY_run (pl := plK) (dl := dlK) L2 ar2
    (by rw [f2 "bl" (by decide), show τ1.vars "bl" = τ0.vars "bl" by simp [τ1], P0.hbl]) hyb hdl hpd
    (by have : plK ≤ b.length := by omega
        simp only [total_append, total_single, List.length_append, List.length_cons, List.length_nil]; omega) hbv
  have hYw : (b.drop plK).take (b.length - dlK) = Y := by
    have := realY_seg G k₀ q₀ (.canon (atomQ G P Q s k₀ q₀ σ))
    rw [dLen_canon, preLen_canon] at this; exact this
  rw [hYw, List.append_assoc] at L3
  set L := ws ++ [[], Y]
  have fr3 : ∀ y, y ∉ apV → y ≠ "m0" → τ3.vars y = τ0.vars y := fun y h1 h2 => by
    rw [f3 y h1, f2 y h1]; simp [τ1, h2]
  have ar3' : ∀ b', b' ∉ ["a", "st", "ln"] → τ3.arrs b' = τ0.arrs b' := fun b' hb => by
    rw [a3 b' hb, a2 b' hb]; rfl
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt (Run.seq r1 (Run.seq r2 r3)) hl0
  have hLl : L.length = ws.length + 2 := by simp [L]
  have hL3 : (L[3]'(by omega)) = llW G P Q s k₀ q₀ q₀ := by
    simp only [L, ws, SW.ws]; simp [w0, LL_up]
  have hLLl : (L[3]'(by omega)).length = q₀ + 1 := by rw [hL3]; simp [llW]
  -- step 4: the offset of level d
  have hsum : ((L[3]'(by omega)).take d).sum = offL G P Q s k₀ q₀ d := by
    rw [hL3]; exact sum_llW G P Q s k₀ q₀ (by omega)
  obtain ⟨τ4, r4, s4, f4, a4, o4, i4⟩ := sumLL_run (W := W) (d := d) (L := L) L3.at_ (by omega)
    (by rw [fr3 "dd" (by decide) (by decide), hdd]) (by omega) (by rw [hsum]; omega) hl3 ar3 (by omega)
  rw [hsum] at s4
  have fr4 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → τ4.vars y = τ0.vars y := fun y h1 h2 h3 h4 => by
    rw [f4 y h3 h4, fr3 y h1 h2]
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt r4 hl3
  have ar4 : ArrW W τ4 := fun b' => by rw [a4]; exact ar3 b'
  have hw4 : WordsAt L τ4 := L3.at_.of_arrs (by rw [a4]) (by rw [a4]) (by rw [a4])
  have hv4 : ∀ y v, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → τ0.vars y = v →
      (Expr.var y).evalB (W + 1) τ4 = some v := fun y v h1 h2 h3 h4 h =>
    ev_var (by rw [fr4 y h1 h2 h3 h4, h]) (by rw [← h, ← fr4 y h1 h2 h3 h4]; exact hl4.vars _)
  -- step 5: the ranges of the piece
  set iw := 4 + w0.SG.length + offL G P Q s k₀ q₀ d + i
  set kl := 4 + w0.SG.length + offL G P Q s k₀ q₀ (d + 1)
  set kn := (lvR G P Q s k₀ q₀ (d + 1)).length
  set ol := 4 + w0.SG.length + w0.LV.length
  have eS := hv4 "nSG" _ (by decide) (by decide) (by decide) (by decide) hSG
  have eO : (Expr.var "oL").evalB (W + 1) τ4 = some (offL G P Q s k₀ q₀ d) := ev_var s4 (by omega)
  have eD := hv4 "dd" _ (by decide) (by decide) (by decide) (by decide) hdd
  have eLd : (eLL (.var "dd")).evalB (W + 1) τ4 = some (lvR G P Q s k₀ q₀ d).length := by
    rw [← llW_get G P Q s k₀ q₀ (show d ≤ q₀ by omega)]
    exact ev_LL3 hw4 (by omega) hL3 eD _ hl4 ar4 (by omega)
  have eLd1 : (eLL (.add (.var "dd") (.lit 1))).evalB (W + 1) τ4 = some kn := by
    show _ = some (lvR G P Q s k₀ q₀ (d + 1)).length
    rw [← llW_get G P Q s k₀ q₀ (show d + 1 ≤ q₀ by omega)]
    exact ev_LL3 hw4 (by omega) hL3 (ev_add eD (evalB_lit (by omega)) (by omega)) _ hl4 ar4 (by omega)
  let fA : String → ℕ := fun y => if y = "ow" then iw else if y = "kl" then kl else if y = "kn" then kn else ol
  obtain ⟨τ5, r5, s5, g5, a5, o5, i5⟩ := asgs_run (B := W + 1) (τ := τ4) (l := upA1) (f := fA)
    (by
      intro p hp
      simp only [upA1, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · rw [show fA "ow" = iw by simp [fA]]
        exact ev_add (ev_add (ev_add (evalB_lit (by omega)) eS (by omega)) eO (by omega))
          (hv4 "ii" _ (by decide) (by decide) (by decide) (by decide) hii) (by omega)
      · rw [show fA "kl" = 4 + w0.SG.length + offL G P Q s k₀ q₀ d + (lvR G P Q s k₀ q₀ d).length by
          simp only [fA, kl, offL_succ]; simp; omega]
        exact ev_add (ev_add (ev_add (evalB_lit (by omega)) eS (by omega)) eO (by omega)) eLd (by omega)
      · rw [show fA "kn" = kn by simp [fA]]; exact eLd1
      · rw [show fA "ol" = ol by simp [fA]]
        exact ev_add (ev_add (evalB_lit (by omega)) eS (by omega))
          (hv4 "nLV" _ (by decide) (by decide) (by decide) (by decide) hLV) (by omega))
    (by decide)
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt r5 hl4
  have fr5 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ∉ upA1.map Prod.fst → τ5.vars y = τ0.vars y :=
    fun y h1 h2 h3 h4 h5 => by rw [g5 y h5, fr4 y h1 h2 h3 h4]
  have L5 : Lib L τ5 := L3.of (by rw [g5 "m" (by decide), f4 "m" (by decide) (by decide)])
    (by rw [g5 "lt" (by decide), f4 "lt" (by decide) (by decide)]) (by rw [a5, a4]) (by rw [a5, a4]) (by rw [a5, a4])
  -- step 6: the head
  have hv5' : ∀ y v, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ∉ upA1.map Prod.fst →
      τ0.vars y = v → (Expr.var y).evalB (W + 1) τ5 = some v := fun y v h1 h2 h3 h4 h5 h =>
    ev_var (by rw [fr5 y h1 h2 h3 h4 h5, h]) (by rw [← h, ← fr5 y h1 h2 h3 h4 h5]; exact hl5.vars _)
  let fH : String → ℕ := fun y =>
    if y = "Nt" ∨ y = "Nm" then 1 else if y = "Nph" then 2 else if y = "Nd" then d else if y = "Ni" then i
    else if y = "NSG" then w0.SG.length else if y = "NLV" then w0.LV.length else if y = "qk" then 3 else 0
  obtain ⟨τ6, r6, s6, g6, a6, o6, i6⟩ := asgs_run (B := W + 1) (τ := τ5) (l := hdA) (f := fH)
    (by
      intro p hp
      simp only [hdA, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show fH "Nt" = 1 by simp [fH]]; exact evalB_lit (by omega)
      · rw [show fH "Nw" = 0 by simp [fH]]; exact evalB_lit (by omega)
      · rw [show fH "Nph" = 2 by simp [fH]]; exact evalB_lit (by omega)
      · rw [show fH "Nd" = d by simp [fH]]
        exact hv5' "dd" _ (by decide) (by decide) (by decide) (by decide) (by decide) hdd
      · rw [show fH "Ni" = i by simp [fH]]
        exact hv5' "ii" _ (by decide) (by decide) (by decide) (by decide) (by decide) hii
      · rw [show fH "Nm" = 1 by simp [fH]]; exact evalB_lit (by omega)
      · rw [show fH "NSG" = w0.SG.length by simp [fH]]
        exact hv5' "nSG" _ (by decide) (by decide) (by decide) (by decide) (by decide) hSG
      · rw [show fH "NFA" = 0 by simp [fH]]; exact evalB_lit (by omega)
      · rw [show fH "NCO" = 0 by simp [fH]]; exact evalB_lit (by omega)
      · rw [show fH "NLV" = w0.LV.length by simp [fH]]
        exact hv5' "nLV" _ (by decide) (by decide) (by decide) (by decide) (by decide) hLV
      · rw [show fH "qk" = 3 by simp [fH]]; exact evalB_lit (by omega)
      · rw [show fH "po" = 0 by simp [fH]]; exact evalB_lit (by omega))
    (by decide)
  have hl6 : EnvLt (W + 1) τ6 := Run.envLt r6 hl5
  have fr6 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ∉ upA1.map Prod.fst →
      y ∉ hdA.map Prod.fst → τ6.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 h6 => by
    rw [g6 y h6, fr5 y h1 h2 h3 h4 h5]
  -- step 7: the window
  have hw6 : WordsAt L τ6 := hw4.of_arrs (by rw [a6, a5]) (by rw [a6, a5]) (by rw [a6, a5])
  have ar6 : ArrW W τ6 := fun b' => by rw [a6, a5]; exact ar4 b'
  have eD6 : (Expr.var "dd").evalB (W + 1) τ6 = some d :=
    ev_var (by rw [fr6 "dd" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hdd])
      (by omega)
  have eI6 : (Expr.var "ii").evalB (W + 1) τ6 = some i :=
    ev_var (by rw [fr6 "ii" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hii])
      (by omega)
  have eL0 : (eLL (.lit 0)).evalB (W + 1) τ6 = some (lvR G P Q s k₀ q₀ 0).length := by
    rw [← llW_get G P Q s k₀ q₀ (show 0 ≤ q₀ by omega)]
    exact ev_LL3 hw6 (by omega) hL3 (evalB_lit (by omega)) _ hl6 ar6 (by omega)
  have hX6 : τ6.vars "nx" = (xIn G k₀ q₀ P Q s).length := by
    rw [fr6 "nx" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hnx]
  obtain ⟨τ7, K7, r7, hK7, n7t, n7w, f7, a7, o7, i7⟩ := winC_run (W := W) (X := (xIn G k₀ q₀ P Q s).length)
    (ev_condEq eD6 (evalB_lit (n := 0) (by omega)))
    (ev_condEq (ev_add eI6 (evalB_lit (n := 1) (by omega)) (by omega)) eL0) hX6 (by omega)
  have hl7 : EnvLt (W + 1) τ7 := Run.envLt r7 hl6
  have fr7 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ∉ upA1.map Prod.fst →
      y ∉ hdA.map Prod.fst → τ7.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 h6 => by
    rw [f7 y (fun h => h6 (by simp [hdA, h])) (fun h => h6 (by simp [hdA, h])), fr6 y h1 h2 h3 h4 h5 h6]
  have hS7 : ∀ y, y ∈ hdA.map Prod.fst → y ≠ "Nt" → y ≠ "Nw" → τ7.vars y = fH y := fun y hy h1 h2 => by
    rw [f7 y h1 h2, s6 y hy]
  have L7 : Lib L τ7 := L5.of (by rw [f7 "m" (by decide) (by decide), g6 "m" (by decide)])
    (by rw [f7 "lt" (by decide) (by decide), g6 "lt" (by decide)]) (by rw [a7, a6]) (by rw [a7, a6]) (by rw [a7, a6])
  -- step 8: the children words
  have hitem : L[iw]? = some (itemW (itm G P Q s k₀ q₀ d i)) := by
    rw [List.getElem?_append_left (by
      have := (List.getElem?_eq_some_iff.1 (ws_up_item G P Q s k₀ q₀ (e := d) (i' := i) (m := 0) hd.le hi)).1
      exact this), ws_up_item G P Q s k₀ q₀ (e := d) (i' := i) (m := 0) hd.le hi, itm_eq G P Q s k₀ q₀ hi]
  have hiw : iw < L.length := (List.getElem?_eq_some_iff.1 hitem).1
  have hLiw : L[iw] = itemW (itm G P Q s k₀ q₀ d i) := (List.getElem?_eq_some_iff.1 hitem).2
  have hLiw' : L[iw] = itemW (((itm G P Q s k₀ q₀ d i).1.1, (itm G P Q s k₀ q₀ d i).1.2),
      ⟨k₀ + d, q + 1, ℓ, t⟩) := by rw [hLiw, ← hσ]
  have hrK : rng L kl kn = lvW G P Q s k₀ q₀ (d + 1) := rng_up_lv G P Q s k₀ q₀ (by omega) [[], Y]
  have hrO : rng L ol kn = outW G P Q s k₀ q₀ (d + 1) := rng_up_out G P Q s k₀ q₀ hd [[], Y]
  have hKQ' : kdQW L q ℓ i kl kn ol = KQ := by
    rw [hKQ, kdQW]
    change toWord (kidW q ℓ i ((rng L kl kn).map _) (rng L ol kn)) = _
    rw [hrK, hrO, lvW_parents]
  have hz0 : τ0.vars "z0" = 0 := by simpa [scR, scW, curW] using hsc 0 (by omega)
  have hk7' : ∀ y ∈ ["W", "rR", "z0", "bl", "ovf", "ii", "nx", "mw"], y ∉ apV ∧ y ≠ "m0" ∧ y ≠ "oL" ∧
      y ≠ "fk" ∧ y ∉ upA1.map Prod.fst ∧ y ∉ hdA.map Prod.fst := by decide
  have hv7 : ∀ y v, y ∈ ["W", "rR", "z0", "bl", "ovf", "ii", "nx", "mw"] → τ0.vars y = v → τ7.vars y = v :=
    fun y v hy h => by
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hk7' y hy
      rw [fr7 y e1 e2 e3 e4 e5 e6, h]
  have hk7'' : ∀ y ∈ ["ow", "kl", "kn", "ol"], y ≠ "Nt" ∧ y ≠ "Nw" ∧ y ∉ hdA.map Prod.fst := by decide
  have hA7 : ∀ y ∈ ["ow", "kl", "kn", "ol"], τ7.vars y = τ5.vars y := fun y hy => by
    obtain ⟨e1, e2, e3⟩ := hk7'' y hy
    rw [f7 y e1 e2, g6 y e3]
  obtain ⟨τ8, K8, r8, hK8, hL8, f8, ya8, ar8, hl8, o8, i8, cp8⟩ :=
    kdT_spec (R := R) (iw := iw) (i := i) (kl := kl) (kn := kn) (ol := ol) (t := t) (L := L) (b := b) (τ := τ7)
      (hv7 "W" _ (by simp) P0.hW) (by omega) (fun b' => by rw [a7]; exact ar6 b') hl7 L7
      (hv7 "rR" _ (by simp) P0.hrR) (hv7 "z0" _ (by simp) hz0) (hv7 "bl" _ (by simp) P0.hbl)
      (fun j hj => by rw [a7, a6, a5, a4, ar3' "y" (by decide)]; exact P0.hy j hj) (hv7 "ovf" _ (by simp) hov)
      (by rw [hA7 "ow" (by simp), s5 "ow" (by simp [upA1])]; simp [fA]) hiw hLiw' (hv7 "ii" _ (by simp) hii) (by omega)
      (by rw [hA7 "kl" (by simp), s5 "kl" (by simp [upA1])]; simp [fA]) (by rw [hA7 "kn" (by simp), s5 "kn" (by simp [upA1])]; simp [fA])
      (by rw [hA7 "ol" (by simp), s5 "ol" (by simp [upA1])]; simp [fA])
      (by omega) (by omega) hR
  rw [hKQ'] at hK8 hL8 cp8
  have hl8' := hl8
  -- step 9: the plan
  have hkd : ∀ y ∈ hdA.map Prod.fst ++ ["m0", "nx", "mw", "W", "rR", "bl", "z0", "gX", "gn", "gP", "gQ", "gS",
      "gK", "gq"], y ∉ kdTV ∨ y = "po" := by decide
  have hm08 : τ8.vars "m0" = ws.length := by
    rw [f8 _ (by decide), f7 _ (by decide) (by decide), g6 _ (by decide), g5 _ (by decide),
      f4 _ (by decide) (by decide), f3 _ (by decide), f2 _ (by decide)]; simp [τ1]
  obtain ⟨τ9, r9, PR9, np9, f9, a9, l9, o9, i9⟩ := stPlan_run (W := W) (l := plR2) (ps := psRep2 ws.length)
    (τ := τ8) rfl (ar8 "PR") (by simp [plR2]; omega)
    (by
      intro j hj
      simp only [plR2, List.length_cons, List.length_nil] at hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact ⟨evalB_lit (by omega), evalB_lit (by omega)⟩
      · exact ⟨ev_add (ev_var hm08 (by omega)) (evalB_lit (by omega)) (by omega), evalB_lit (by omega)⟩
      · exact ⟨evalB_lit (by omega), ev_sub (ev_var hm08 (by omega)) (evalB_lit (by omega)) (by omega)⟩)
    (by decide)
  have hrun := Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
    (Run.seq r8 r9)))))))
  have hl9 : EnvLt (W + 1) τ9 := Run.envLt hrun hl0
  have ar9 : ArrW W τ9 := fun b' => by
    by_cases hb : b' = "PR"
    · subst hb; exact l9
    · rw [a9 b' hb]; exact ar8 b'
  have hov9 : τ9.vars "ovf" = τ8.vars "ovf" := f9 "ovf" (by decide)
  have fr9 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ∉ upA1.map Prod.fst →
      y ∉ hdA.map Prod.fst → y ∉ kdTV → y ≠ "np" → τ9.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [f9 y h8, f8 y h7, fr7 y h1 h2 h3 h4 h5 h6]
  have hS9 : ∀ y, y ∈ hdA.map Prod.fst → y ≠ "Nt" → y ≠ "Nw" → y ≠ "po" → τ9.vars y = fH y :=
    fun y hy h1 h2 h3 => by
      rw [f9 y (by intro h; subst h; simp [hdA] at hy), f8 y (by
        rcases hkd y (List.mem_append_left _ hy) with h | h
        · exact h
        · exact absurd h h3), hS7 y hy h1 h2]
  have hscR : ∀ y ∈ scR, y ∉ apV ∧ y ≠ "m0" ∧ y ≠ "oL" ∧ y ≠ "fk" ∧ y ∉ upA1.map Prod.fst ∧
      y ∉ hdA.map Prod.fst ∧ y ∉ kdTV ∧ y ≠ "np" := by decide
  have g : ∀ j (h : j < 9), τ9.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.up d i 0)).getD j 0 := fun j h => by
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hscR _ (List.getElem_mem _)
    rw [fr9 _ e1 e2 e3 e4 e5 e6 e7 e8]; exact hsc j (by omega)
  have hNt : τ9.vars "Nt" = τ7.vars "Nt" := by rw [f9 _ (by decide), f8 _ (by decide)]
  have hNw : τ9.vars "Nw" = τ7.vars "Nw" := by rw [f9 _ (by decide), f8 _ (by decide)]
  have hnx9 : τ9.vars "nx" = τ0.vars "nx" := fr9 "nx" (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hmw9 : τ9.vars "mw" = τ0.vars "mw" := fr9 "mw" (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hnx7 : τ7.vars "nx" = τ0.vars "nx" := hv7 "nx" _ (by simp) rfl
  have hmw7 : τ7.vars "mw" = τ0.vars "mw" := hv7 "mw" _ (by simp) rfl
  refine ⟨τ9, _, hrun, ?_, fun h0 => ?_, fun hB => ?_⟩
  · -- the cost
    have hA1 : asgK upA1 ≤ 60 := by decide
    have hA2 : asgK hdA ≤ 40 := by decide
    have hC : (Cond.eq (.var "dd") (.lit 0)).size + (Cond.eq (.add (.var "ii") (.lit 1)) (eLL (.lit 0))).size ≤ 30 := by
      decide
    have hrK' : total ((L.drop kl).take kn) = total (lvW G P Q s k₀ q₀ (d + 1)) := by
      rw [show (L.drop kl).take kn = rng L kl kn from rfl, hrK]
    have hrO' : total ((L.drop ol).take kn) = total (outW G P Q s k₀ q₀ (d + 1)) := by
      rw [show (L.drop ol).take kn = rng L ol kn from rfl, hrO]
    rw [hrK', hrO', hLiw] at hK8
    have hP : plR2.length * ((plR2.map fun p => p.1.size + p.2.size).sum + 6) + 4 ≤ 100 := by decide
    unfold kUpA
    omega
  · rw [hov9] at h0
    obtain ⟨L8, hoe8, hpo8⟩ := hL8 h0
    refine ⟨⟨?_, hkq, ar9, hl9, ?_, hR, ?_, ?_, ?_, ?_, ?_, by rw [hov9]; exact h0, ?_, ?_, PR9, np9, ?_,
      by simp [psRep2]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fr9 "W" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        P0.hW]
    · rw [fr9 "rR" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), P0.hrR]
    · have := L8.of (τ' := τ9) (f9 "m" (by decide)) (f9 "lt" (by decide)) (a9 "a" (by decide))
        (a9 "st" (by decide)) (a9 "ln" (by decide))
      simpa [L, KQ, List.append_assoc] using this
    · rw [fr9 "z0" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hz0]
    · rw [fr9 "bl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), P0.hbl]
    · intro j hj; rw [a9 "y" (by decide), ya8, a7, a6, a5, a4, ar3' "y" (by decide)]; exact P0.hy j hj
    · simpa [scR, scW, curW] using g 1 (by omega)
    · refine ⟨fun h => by simp [hc1, kindOf] at h, fun h => by simp [hc1, kindOf] at h,
        fun h => by simp [hc1, kindOf] at h, fun _ => ?_, by simp [hc1, kindOf]⟩
      refine ⟨L.length, by simp [L], by rw [f9 "oe" (by decide), hoe8], ?_⟩
      simp [L, KQ]
    · rw [hS9 "qk" (by simp [hdA]) (by decide) (by decide) (by decide)]; simp [fH, hc1, kindOf]
    · intro p hp; simp [psRep2] at hp; rcases hp with rfl | rfl | rfl <;> simp [L] <;> omega
    · rw [hNt, n7t, tagOf, winOf_upA G P Q s k₀ q₀ hd hi, s6 "Nt" (by simp [hdA])]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      split_ifs <;> simp [fH]
    · rw [hNw, n7w, winOf_upA G P Q s k₀ q₀ hd hi, s6 "Nw" (by simp [hdA])]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      split_ifs <;> simp [fH]
    · rw [hsV_of (by simp [scW]) g (hS9 "Nph" (by simp [hdA]) (by decide) (by decide) (by decide))
        (hS9 "Nd" (by simp [hdA]) (by decide) (by decide) (by decide))
        (hS9 "Ni" (by simp [hdA]) (by decide) (by decide) (by decide))
        (hS9 "Nm" (by simp [hdA]) (by decide) (by decide) (by decide))
        (hS9 "NSG" (by simp [hdA]) (by decide) (by decide) (by decide))
        (hS9 "NFA" (by simp [hdA]) (by decide) (by decide) (by decide))
        (hS9 "NCO" (by simp [hdA]) (by decide) (by decide) (by decide))
        (hS9 "NLV" (by simp [hdA]) (by decide) (by decide) (by decide)),
        scW_eq G P Q s k₀ q₀ (.up d i 0) (.up d i 1)]
      simp [fH, curW, w0, SG_up, LV_up, FA_up, CO_up]
    · rw [f9 "po" (by decide), hpo8]
    · rw [hnx9]
    · rw [hmw9]
    · rw [o9, o8, o7, o6, o5, o4, o3, o2]; simp [τ1, P0.hout]
  · rw [hov9]
    have eLb : ws ++ [[], Y, KQ] = L ++ [KQ] := by simp [L]
    have hB' : BigRoom W R (L ++ [KQ]) b (τ7.vars "nx") (τ7.vars "mw") := by
      rw [hnx7, hmw7, ← eLb]; exact hB
    exact cp8 (L ++ [KQ]) (List.Sublist.refl _) hB'

end Lax185574Proofs.ResolveRam.Glue
