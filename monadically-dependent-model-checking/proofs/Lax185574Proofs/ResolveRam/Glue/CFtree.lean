import Lax185574Proofs.ResolveRam.Glue.CComp
import Lax185574Proofs.ResolveRam.Glue.SemFt
import Lax185574Proofs.ResolveRam.Glue.PFASpec

/-!
The case of a later round after the far tree of an item on the way down
(position `dn d i 1`).

The piece FA (`faCmd`) writes the frames of the members of the answer of
the far tree that pass `passSel` against the answer of the rank shift
(word `1` of the library). After a room check the case appends the empty
word and these words `FA'` to the library. If `FA'` is not empty, the
state of `dn d i 2` is the old state with `FA'` (`psFt`, `planW_ft`) and
the next call is the composition with `FA'[0]` (`bFt_ok`). If `FA'` is
empty, the item is finished by the command `fE`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam
open Lax3.DistFO (rhoPlus)

/-- The fixed answers in front of the answer of a far tree. -/
noncomputable def plF : ℕ := yA0.length

/-- The scalars of the new head and of the first composition. -/
def hdF : List (String × Expr) :=
  [("Nt", .lit 1), ("Nw", .lit 0), ("Nph", .lit 1), ("Nd", .var "dd"), ("Ni", .var "ii"), ("Nm", .lit 2),
    ("NSG", .var "nSG"), ("NFA", .var "pc"), ("NCO", .var "nCO"), ("NLV", .var "nLV"),
    ("of", .add (.var "m0") (.lit 1)), ("qk", .lit 2), ("po", .lit 0)]

/-- The plan after the far tree, as expressions. -/
def plF2 : List (Expr × Expr) :=
  [(.lit 0, .add (.lit 4) (.var "nSG")), (.add (.var "m0") (.lit 1), .var "pc"),
    (.add (.lit 4) (.var "nSG"), .var "nLV")]

/-- The plan after the far tree. -/
def psFt (M0 nS nF nL : ℕ) : List (ℕ × ℕ) := [(0, 4 + nS), (M0 + 1, nF), (4 + nS, nL)]

/-- The case after the far tree; `fE` finishes the item if no member passes. -/
noncomputable def bFt (fE : Com) : Com :=
  .seq (asgs [("m0", .var "m"), ("oc", .lit 0), ("os", .lit 1), ("yo", .lit plF)])
  (.seq faCmd (.seq rmLs (gate
    (.seq apE (.seq (asgs [("ls", .lit 0), ("lN", .var "pc")]) (.seq (lbFr "OB")
      (.ite (.eq (.var "pc") (.lit 0)) fE (.seq (asgs hdF) (stPlan plF2)))))))))

theorem planW_ft (w : SW) (F : List (List ℕ)) (hFA : w.FA = []) (hCO : w.CO = []) (hOU : w.OU = []) :
    planW (w.ws ++ ([] :: F)) (psFt w.ws.length w.SG.length F.length w.LV.length) =
      ({ w with FA := F } : SW).ws := by
  set A := w.CT :: w.SH :: w.AT :: w.LL :: w.SG with hA
  have hws : w.ws = A ++ w.LV := by simp [SW.ws, hA, hFA, hCO, hOU]
  have hAl : A.length = 4 + w.SG.length := by simp [hA]; omega
  simp only [planW, psFt, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have r1 : rng (w.ws ++ ([] :: F)) 0 (4 + w.SG.length) = A := by
    rw [rng_append_left (by rw [hws]; simp; omega), hws, ← hAl, rng_append_left (by omega), rng_full]
  have r2 : rng (w.ws ++ ([] :: F)) (w.ws.length + 1) F.length = F := by
    rw [rng_append_right]; simp [rng]
  have r3 : rng (w.ws ++ ([] :: F)) (4 + w.SG.length) w.LV.length = w.LV := by
    rw [rng_append_left (by rw [hws]; simp; omega), hws, ← hAl]
    have := rng_append_right (L := A) (M := w.LV) (lo := 0) (N := w.LV.length)
    simp only [Nat.add_zero] at this; rw [this]; simp [rng]
  rw [r1, r2, r3]
  simp [SW.ws, hA, hFA, hCO, hOU]

theorem filled_of_po {τ : Env} (h : τ.vars "po" = 0) : Filled "OB" "po" [] τ :=
  ⟨by simp [h], fun i h => absurd h (by simp)⟩

/-- The constants of the piece FA. -/
noncomputable def cFA : ℕ := faCmd_spec.choose
noncomputable def aFA : ℕ := faCmd_spec.choose_spec.choose

theorem faSpec' : ∀ (W : ℕ) (τ : Env) (ws : List (List ℕ)) (L : List (List ℕ)) (pre : List ℕ)
    (oc os yo P Q sg : ℕ) (hoc : oc < ws.length) (hos : os < ws.length),
    τ.vars "W" = W → ArrW W τ → WordsAt ws τ → τ.vars "oc" = oc → τ.vars "os" = os →
    τ.vars "yo" = yo → τ.vars "gP" = P → τ.vars "gQ" = Q → P ≤ W → Q ≤ W → τ.vars "gS" = sg → sg ≤ 1 →
    IsCT ws[oc] → (∃ σ : TypeTree, ws[os] = toWord σ) → (∀ w ∈ L, ∃ ν : TypeTree, w = toWord ν) →
    YAt (toWord L) yo τ → Filled "OB" "po" pre τ →
    Room W (rhoPlus (ws[os].getD 0 0) (ws[os].getD 1 0))
      (ySz (toWord ws) + ySz (toWord L) + yo + pre.length + ws[os].getD 2 0) →
    ∃ τ', Run (W + 1) faCmd τ τ' (cFA * ((toWord L).length + ws[oc].length + 1) *
        (ws[os].length + ws[os].getD 2 0 + maxLen L + rhoPlus (ws[os].getD 0 0) (ws[os].getD 1 0) + 1) ^ aFA) ∧
      Filled "OB" "po" (pre ++ frames (L.filter (passSel (dwOf P Q sg ws[oc]) ws[os]))) τ' ∧
      τ'.vars "pc" = (L.filter (passSel (dwOf P Q sg ws[oc]) ws[os])).length ∧ PFr faV τ τ' :=
  faCmd_spec.choose_spec.choose_spec

/-- The cost of the case after the far tree, with the cost `KF` of the piece and `KE` of `fE`. -/
def kFt (b : List ℕ) (ws F : List (List ℕ)) (KF KE : ℕ) : ℕ :=
  KF + 30 * total ws + 30 * b.length + (18 * total F + 60 * F.length) + KE + 3000

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The cost of the piece FA on the item `(d, i)`. -/
noncomputable def kFA (d i : ℕ) : ℕ :=
  cFA * ((toWord ((faOf G (itm G P Q s k₀ q₀ d i).2).map toWord)).length + (ctW G P Q).length + 1) *
    ((toWord (shOf G (itm G P Q s k₀ q₀ d i).2)).length + (toWord (shOf G (itm G P Q s k₀ q₀ d i).2)).getD 2 0 +
      maxLen ((faOf G (itm G P Q s k₀ q₀ d i).2).map toWord) +
      rhoPlus ((toWord (shOf G (itm G P Q s k₀ q₀ d i).2)).getD 0 0)
        ((toWord (shOf G (itm G P Q s k₀ q₀ d i).2)).getD 1 0) + 1) ^ aFA

theorem dLen_ftree (τ : TypeTree) : dLen (.ftree τ) = yA0.length + yC0.length + yE0.length + yF0.length := by
  simp [dLen]; omega

set_option maxHeartbeats 3200000 in
/-- **The case after the far tree, when a member passes.** -/
theorem bFt_ok (fE : Com) {d i W : ℕ} (hk : 1 ≤ k₀) (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hF : 0 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length) :
    BodyCall (bFt fE) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.dn d i 1))
      (swAt G P Q s k₀ q₀ (.dn d i 1)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.dn d i 1)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1)))
      ((swAt G P Q s k₀ q₀ (.dn d i 1)).ws ++
        ([] :: (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord))
      (psFt (swAt G P Q s k₀ q₀ (.dn d i 1)).ws.length (swAt G P Q s k₀ q₀ (.dn d i 1)).SG.length
        (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length (swAt G P Q s k₀ q₀ (.dn d i 1)).LV.length)
      (kindOf (callOf G P Q s k₀ q₀ (.dn d i 2))) (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 2)))
      (tagOf G P Q s k₀ q₀ (.dn d i 2)) (winOf G P Q s k₀ q₀ (.dn d i 2)) (scW G P Q s k₀ q₀ (.dn d i 2))
      (kFt (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1))) (swAt G P Q s k₀ q₀ (.dn d i 1)).ws
        ((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord) (kFA G P Q s k₀ q₀ d i) 0) := by
  intro τ0 P0 hov hkq
  set t := (itm G P Q s k₀ q₀ d i).2
  set F := faP G (dataOf G P Q s k₀ q₀) t
  set Lf := (faOf G t).map toWord
  have hnd : nDn G P Q s k₀ q₀ d i = 2 + F.length := nDn_itm hi
  have hc1 : callOf G P Q s k₀ q₀ (.dn d i 1) = .ftree t := by
    rw [callOf_dn' hi (by omega)]; simp [t]
  obtain ⟨hb2, hc2⟩ := callOf_dn_comp G P Q s k₀ q₀ (m := 2) hi le_rfl (by omega)
  rw [hc1] at P0 ⊢
  rw [hc2]
  set w0 := swAt G P Q s k₀ q₀ (.dn d i 1)
  set ws := w0.ws
  set b := rY G k₀ q₀ (.ftree t)
  set R := rhoPlus (k₀ + 1) q₀ + 2
  have hR : 1 ≤ R := by omega
  have hSH : w0.SH = toWord (shOf G t) := by simp [w0, swAt, t]
  have hCT : w0.CT = ctW G P Q := by simp [w0, swAt]
  have hroom : RoomOK W R τ0 ws b := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS := room_bound hroom hR
  obtain ⟨hS1, hS2, hS3, hS4⟩ := sOfV_ge (τ := τ0) (ws := ws) (b := b)
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hl0 := P0.hlt
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.dn d i 1)).getD j 0 := P0.hsc
  have hdd : τ0.vars "dd" = d := by simpa [scR, scW_dn] using hsc 10 (by omega)
  have hii : τ0.vars "ii" = i := by simpa [scR, scW_dn] using hsc 11 (by omega)
  have hSG : τ0.vars "nSG" = w0.SG.length := by simpa [scR, scW_dn] using hsc 13 (by omega)
  have hCO : τ0.vars "nCO" = 0 := by simpa [scR, scW_dn, w0, CO_dn1] using hsc 15 (by omega)
  have hLV : τ0.vars "nLV" = w0.LV.length := by simpa [scR, scW_dn] using hsc 16 (by omega)
  have hgP : τ0.vars "gP" = P := by simpa [scR, scW_dn] using hsc 4 (by omega)
  have hgQ : τ0.vars "gQ" = Q := by simpa [scR, scW_dn] using hsc 5 (by omega)
  have hgS : τ0.vars "gS" = (if s then 1 else 0) := by simpa [scR, scW_dn] using hsc 6 (by omega)
  have hOU : w0.OU = [] := OU_dn G P Q s k₀ q₀ d i 1
  have hFA0 : w0.FA = [] := FA_dn1 G P Q s k₀ q₀
  have hCO0 : w0.CO = [] := CO_dn1 G P Q s k₀ q₀
  have hwsl : ws.length = 4 + w0.SG.length + w0.LV.length := by
    simp only [ws, SW.ws, List.length_append, List.length_cons, List.length_nil, hOU, hFA0, hCO0]; omega
  obtain ⟨pre, post, hsp, hpre, hpp⟩ := rY_split G k₀ q₀ (.ftree t)
  have hpl : plF + (realY G k₀ q₀ (.ftree t)).length ≤ b.length := by
    rw [show plF = preLen (.ftree t) from rfl, ← hpre]; simp only [b, hsp, List.length_append]; omega
  have hbW : b.length < W + 1 := by rw [← P0.hbl]; exact hl0.vars _
  -- step 1: the scalars of the piece
  let f1 : String → ℕ := fun y => if y = "m0" then ws.length else if y = "os" then 1 else if y = "yo" then plF else 0
  obtain ⟨τ1, r1, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ0)
    (l := [("m0", .var "m"), ("oc", .lit 0), ("os", .lit 1), ("yo", .lit plF)]) (f := f1)
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · rw [show f1 "m0" = ws.length by simp [f1]]; exact ev_var P0.hlib.m (by omega)
      · rw [show f1 "oc" = 0 by simp [f1]]; exact evalB_lit (by omega)
      · rw [show f1 "os" = 1 by simp [f1]]; exact evalB_lit (by omega)
      · rw [show f1 "yo" = plF by simp [f1]]
        exact evalB_lit (by omega))
    (by decide)
  have hv1 : ∀ y, y ∉ ["m0", "oc", "os", "yo"] → τ1.vars y = τ0.vars y := fun y hy => g1 y (by simpa using hy)
  have hm01 : τ1.vars "m0" = ws.length := by rw [s1 "m0" (by simp)]; simp [f1]
  -- step 2: the piece FA
  have hws0 : 0 < ws.length := by omega
  have hws1 : 1 < ws.length := by omega
  have h0 : ws[0] = ctW G P Q := by rw [← hCT]; simp [ws, SW.ws]
  have h1 : ws[1] = toWord (shOf G t) := by rw [← hSH]; simp [ws, SW.ws]
  obtain ⟨wsh, hwsh⟩ := sh_itm G P Q s k₀ q₀ hk hd hi
  have hsk : (toWord (shOf G t)).getD 0 0 = k₀ + d + 1 := by
    rw [show shOf G t = _ from hwsh, Lax185574Proofs.FarRam.toWord_typeTree]; rfl
  have hsq : (toWord (shOf G t)).getD 1 0 = q₀ - d - 1 := by
    rw [show shOf G t = _ from hwsh, Lax185574Proofs.FarRam.toWord_typeTree]; rfl
  have hyl : SegAt "y" 0 b τ1 := fun j hj => by rw [a1]; exact P0.hy j hj
  have hYAt : YAt (toWord Lf) plF τ1 := by
    intro j hj
    have hr : realY G k₀ q₀ (.ftree t) = toWord Lf := rfl
    have hj' : plF + j < b.length := by rw [← hr] at hj; omega
    have hy' := hyl (plF + j) hj'
    rw [Nat.zero_add] at hy'
    rw [hy']
    have hpre' : pre.length = plF := hpre
    have hjr : j < (realY G k₀ q₀ (.ftree t)).length := by rw [hr]; exact hj
    simp only [b, hsp]
    rw [List.getElem_append_left (by simp only [List.length_append]; omega),
      List.getElem_append_right (by omega)]
    simp only [hpre', Nat.add_sub_cancel_left, hr]
  have hPW : P ≤ W := by rw [← hgP]; have := hl0.vars "gP"; omega
  have hQW : Q ≤ W := by rw [← hgQ]; have := hl0.vars "gQ"; omega
  have hlw1 := hl0
  have hRoom : Room W (rhoPlus (ws[1].getD 0 0) (ws[1].getD 1 0))
      (ySz (toWord ws) + ySz (toWord Lf) + plF + ([] : List ℕ).length + ws[1].getD 2 0) := by
    set So := sOfV τ0 ws b
    have hr : realY G k₀ q₀ (.ftree t) = toWord Lf := rfl
    have hm1 : maxEntry (toWord ws) ≤ total ws + ws.length + maxEntry ws.flatten :=
      maxEntry_le fun v hv => mem_toWord_bound hv (by omega) (fun w hw x hx => by
        have := le_maxEntry (List.mem_flatten.2 ⟨w, hw, hx⟩); omega)
    have hl1 := length_toWord_words ws
    have hm2 : maxEntry (toWord Lf) ≤ maxEntry b :=
      maxEntry_le fun v hv => le_maxEntry (by rw [← hr] at hv; simp only [b, hsp]; simp [hv])
    have hl2 : (toWord Lf).length ≤ b.length := by rw [← hr]; omega
    have h12 : ws[1].getD 2 0 ≤ maxEntry ws.flatten := by
      rw [List.getD_eq_getElem?_getD]
      rcases h : ws[1][2]? with _ | v
      · simp
      · have := le_maxEntry (List.mem_flatten.2 ⟨ws[1], List.getElem_mem _, List.mem_of_getElem? h⟩)
        simpa using this
    have hSo : ySz (toWord ws) + ySz (toWord Lf) + plF + ([] : List ℕ).length + ws[1].getD 2 0 + 1 ≤ 5 * So := by
      simp only [ySz, List.length_nil]; omega
    have hR' : rhoPlus (ws[1].getD 0 0) (ws[1].getD 1 0) + 1 ≤ R := by
      rw [h1, hsk, hsq]; have := rho_sh (k₀ := k₀) (q₀ := q₀) hd; simp only [R]; omega
    unfold Room
    have hroom' := hroom
    unfold RoomOK at hroom'
    calc 2 ^ 16 * (rhoPlus (ws[1].getD 0 0) (ws[1].getD 1 0) + 1) ^ 2 *
          (ySz (toWord ws) + ySz (toWord Lf) + plF + ([] : List ℕ).length + ws[1].getD 2 0 + 1) ^ 2
        ≤ 2 ^ 16 * R ^ 2 * (5 * So) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR' 2)) (Nat.pow_le_pow_left hSo 2)
      _ ≤ 2 ^ 24 * R * R * R * R * So * So := by
          have : R ^ 2 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by omega)
          have := Nat.mul_le_mul_right (So * So) (Nat.mul_le_mul_left (2 ^ 16 * 25) this)
          nlinarith
      _ ≤ W := hroom'.le
  obtain ⟨τ2, r2, F2, pc2, P2⟩ := faSpec' W τ1 ws Lf [] 0 1 plF P Q (if s then 1 else 0) hws0 hws1
    (by rw [hv1 "W" (by decide), P0.hW]) (fun b' => by rw [a1]; exact P0.harr b')
    (P0.hlib.at_.of_arrs (by rw [a1]) (by rw [a1]) (by rw [a1]))
    (by rw [s1 "oc" (by simp)]; simp [f1]) (by rw [s1 "os" (by simp)]; simp [f1]) (by rw [s1 "yo" (by simp)]; simp [f1])
    (by rw [hv1 "gP" (by decide), hgP]) (by rw [hv1 "gQ" (by decide), hgQ]) hPW hQW
    (by rw [hv1 "gS" (by decide), hgS]) (by split_ifs <;> omega)
    (by rw [h0]; exact isCT_ctW G P Q) ⟨_, h1⟩ (fun w hw => by
      obtain ⟨ν, -, rfl⟩ := List.mem_map.1 hw; exact ⟨ν, rfl⟩) hYAt
    (filled_of_po (by rw [hv1 "po" (by decide), P0.hpo])) hRoom
  have hK2 : cFA * ((toWord Lf).length + ws[0].length + 1) *
      (ws[1].length + ws[1].getD 2 0 + maxLen Lf + rhoPlus (ws[1].getD 0 0) (ws[1].getD 1 0) + 1) ^ aFA =
      kFA G P Q s k₀ q₀ d i := by rw [h0, h1]; rfl
  rw [hK2] at r2
  have hFw : Lf.filter (passSel (dwOf P Q (if s then 1 else 0) ws[0]) ws[1]) = F.map toWord := by
    rw [h0, h1, faP_words (dW_ok G P Q s k₀ q₀)]; rfl
  rw [hFw] at F2 pc2
  simp only [List.nil_append] at F2
  set F' := F.map toWord
  have hv2 : ∀ y, y ∉ faV → y ∉ ["m0", "oc", "os", "yo"] → τ2.vars y = τ0.vars y := fun y h1 h2 => by
    rw [P2.vars y h1, hv1 y h2]
  have ha2 : ∀ b', b' ∈ keepA → τ2.arrs b' = τ0.arrs b' := fun b' hb => by rw [P2.arrs b' hb, a1]
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt (Run.seq r1 r2) hl0
  have ar2 : ArrW W τ2 := fun b' => by rw [P2.len, a1]; exact P0.harr b'
  have L2 : Lib ws τ2 := P0.hlib.of (by rw [hv2 "m" (by decide) (by decide)]) (by rw [hv2 "lt" (by decide) (by decide)])
    (ha2 "a" (by decide)) (ha2 "st" (by decide)) (ha2 "ln" (by decide))
  -- step 3: the room check after the piece
  obtain ⟨τ3, r3, ov3, f3, a3, u3, i3⟩ := rmLs_run (R := R) (ws := ws) (b := b) (τ := τ2)
    (by rw [hv2 "W" (by decide) (by decide), P0.hW]) (by omega)
    (by rw [hv2 "rR" (by decide) (by decide), P0.hrR]) L2
    (by rw [hv2 "z0" (by decide) (by decide)]; simpa [scR, scW_dn] using hsc 0 (by omega))
    (by rw [hv2 "bl" (by decide) (by decide), P0.hbl]) (fun j hj => by rw [ha2 "y" (by decide)]; exact P0.hy j hj)
    ar2 hl2
  rw [hv2 "ovf" (by decide) (by decide), hov] at ov3
  have hpo2 : τ2.vars "po" = (frames F').length := F2.pos
  have hbig2 : BigRoom W R (ws ++ ([] :: F')) b (τ0.vars "nx") (τ0.vars "mw") → RoomOK W R τ2 ws b := by
    intro hB
    refine roomOK_of_big (List.sublist_append_left _ _) ?_ (by
      rw [hv2 "nx" (by decide) (by decide), hv2 "mw" (by decide) (by decide)]; exact hB)
    rw [hpo2, length_frames]
    simp only [total_append, List.length_append, List.length_cons]
    have : total ([] :: F') = total F' := by simp [total]
    omega
  by_cases hr3 : RoomOK W R τ2 ws b
  swap
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ2 ws b * sOfV τ2 ws b < W from hr3)] at ov3
    have hrun : Run (W + 1) (bFt fE) τ0 τ3 (kFt b ws F' (kFA G P Q s k₀ q₀ d i) 0) := by
      refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (gate_skip (by rw [ov3]; omega)
        (by rw [ov3]; omega))))).mono ?_
      have hA : asgK [("m0", .var "m"), ("oc", .lit 0), ("os", .lit 1), ("yo", .lit plF)] = 9 := rfl
      rw [hA]; unfold kFt; clear * -; omega
    exact ⟨τ3, _, hrun, le_rfl, fun h => by rw [ov3] at h; omega, fun hB => absurd (hbig2 hB) hr3⟩
  rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ2 ws b * sOfV τ2 ws b < W from hr3)] at ov3
  have hS2 := room_bound hr3 hR
  obtain ⟨hT1, hT2, hT3, hT4⟩ := sOfV_ge (τ := τ2) (ws := ws) (b := b)
  rw [hpo2, length_frames] at hT1
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  have ar3 : ArrW W τ3 := fun b' => by rw [a3]; exact ar2 b'
  have L3 : Lib ws τ3 := L2.of (by rw [f3 "m" (by decide)]) (by rw [f3 "lt" (by decide)]) (by rw [a3])
    (by rw [a3]) (by rw [a3])
  have hv3 : ∀ y, y ∉ rmLs.wvars → y ∉ faV → y ∉ ["m0", "oc", "os", "yo"] → τ3.vars y = τ0.vars y :=
    fun y h0 h1 h2 => by rw [f3 y h0, hv2 y h1 h2]
  -- step 4: the empty word
  obtain ⟨τ4, r4, L4, f4, a4, ar4, o4, i4⟩ := apE_run L3 ar3 (by omega)
  have hpc4 : τ4.vars "pc" = F.length := by
    rw [f4 "pc" (by decide), f3 "pc" (by decide), pc2]; simp [F']
  -- step 5: the scalars of the copy
  obtain ⟨τ5, r5, s5, f5, a5, o5, i5⟩ := asgs_run (B := W + 1) (τ := τ4)
    (l := [("ls", .lit 0), ("lN", .var "pc")]) (f := fun y => if y = "ls" then 0 else F.length)
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · simp only [if_true]; exact evalB_lit (by omega)
      · simp only [show ("lN" : String) ≠ "ls" by decide, if_false]
        exact ev_var hpc4 (by rw [← hpc4]; exact (Run.envLt r4 hl3).vars _))
    (by decide)
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt r5 (Run.envLt r4 hl3)
  have L5 : Lib (ws ++ [[]]) τ5 := L4.of (by rw [f5 "m" (by decide)]) (by rw [f5 "lt" (by decide)])
    (by rw [a5]) (by rw [a5]) (by rw [a5])
  -- step 6: the filtered words
  have hOB : τ5.arrs "OB" = τ2.arrs "OB" := by rw [a5, a4 "OB" (by decide), a3]
  have hseg : SegAt "OB" 0 (frames F') τ5 := fun j hj => by
    rw [hOB, Nat.zero_add]; exact F2.get j hj
  have hFv : ∀ w ∈ F', ∀ v ∈ w, v ≤ W := by
    intro w hw v hv
    have hm : v ∈ frames F' := by
      simp only [frames, List.mem_flatten, List.mem_map]
      exact ⟨_, ⟨w, hw, rfl⟩, List.mem_cons_of_mem _ hv⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    have := hl2.arrs "OB" _ (List.mem_of_getElem? (F2.get j hj))
    omega
  have htF : total F' + F'.length = (frames F').length := (length_frames F').symm
  obtain ⟨τ6, r6, L6, ls6, f6, a6, l6, o6, i6⟩ := lbFr_run (W := W) (src := "OB") (L := F') (p := 0) L5
    (by rw [s5 "ls" (by simp)]; simp) (by rw [s5 "lN" (by simp)]; simp [F']) hseg (by decide)
    (by rw [a5, ar4 "a"]; simp only [total_append, total_single, List.length_nil]; omega)
    (by rw [a5, ar4 "st"]; simp; omega) (by rw [a5, ar4 "ln"]; simp; omega)
    (by
      have e1 : total (ws ++ [[]]) = total ws := by simp [total]
      rw [e1, List.length_append, List.length_singleton]; omega) hFv
  have hl6 : EnvLt (W + 1) τ6 := Run.envLt r6 hl5
  have ar6 : ArrW W τ6 := fun b' => by rw [l6, a5]; exact ar4 b'
  rw [List.append_assoc, List.singleton_append] at L6
  set L := ws ++ ([] :: F')
  have hLl : L.length = ws.length + 1 + F.length := by simp [L, F']; omega
  have fr6 : ∀ y, y ∉ ["fk", "ci", "lt", "m", "lL", "ls", "lN"] → y ∉ apV → y ∉ rmLs.wvars → y ∉ faV →
      y ∉ ["m0", "oc", "os", "yo"] → τ6.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
    have h1a : y ∉ ["fk", "ci", "lt", "m", "lL", "ls"] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a1, a2, a3, a4, a5, a6⟩
    have h1' : y ∉ [("ls", Expr.lit 0), ("lN", Expr.var "pc")].map Prod.fst := by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨a6, a7⟩
    rw [f6 y h1a, f5 y h1', f4 y h2, hv3 y h3 h4 h5]
  have hpc6 : τ6.vars "pc" = F.length := by
    rw [f6 "pc" (by decide), f5 "pc" (by decide)]; exact hpc4
  -- step 7: the test
  have hc7 : (Cond.eq (.var "pc") (.lit 0)).evalB (W + 1) τ6 = some false := by
    rw [evalB_condEq (ev_var hpc6 (by rw [← hpc6]; exact hl6.vars _)) (evalB_lit (by omega))]
    have : (F.length == 0) = false := by
      rcases h : F.length with _ | k
      · omega
      · rfl
    rw [this]
  -- step 8: the head scalars and the composition
  have hm06 : τ6.vars "m0" = ws.length := by
    rw [f6 _ (by decide), f5 _ (by decide), f4 _ (by decide), f3 _ (by decide), P2.vars _ (by decide)]
    exact hm01
  have hv6 : ∀ y v, y ∉ ["fk", "ci", "lt", "m", "lL", "ls", "lN"] → y ∉ apV → y ∉ rmLs.wvars → y ∉ faV →
      y ∉ ["m0", "oc", "os", "yo"] → τ0.vars y = v → (Expr.var y).evalB (W + 1) τ6 = some v :=
    fun y v h1 h2 h3 h4 h5 h => ev_var (by rw [fr6 y h1 h2 h3 h4 h5, h])
      (by rw [← h, ← fr6 y h1 h2 h3 h4 h5]; exact hl6.vars _)
  let fS : String → ℕ := fun y =>
    if y = "Nt" ∨ y = "Nph" then 1 else if y = "Nd" then d else if y = "Ni" then i
    else if y = "Nm" ∨ y = "qk" then 2 else if y = "NSG" then w0.SG.length else if y = "NFA" then F.length
    else if y = "NLV" then w0.LV.length else if y = "of" then ws.length + 1 else 0
  obtain ⟨τ7, r7, s7, f7, a7, o7, i7⟩ := asgs_run (B := W + 1) (τ := τ6) (l := hdF) (f := fS)
    (by
      intro p hp
      simp only [hdF, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show fS "Nt" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nw" = 0 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nph" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nd" = d by simp [fS]]
        exact hv6 "dd" _ (by decide) (by decide) (by decide) (by decide) (by decide) hdd
      · rw [show fS "Ni" = i by simp [fS]]
        exact hv6 "ii" _ (by decide) (by decide) (by decide) (by decide) (by decide) hii
      · rw [show fS "Nm" = 2 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "NSG" = w0.SG.length by simp [fS]]
        exact hv6 "nSG" _ (by decide) (by decide) (by decide) (by decide) (by decide) hSG
      · rw [show fS "NFA" = F.length by simp [fS]]
        exact ev_var hpc6 (by rw [← hpc6]; exact hl6.vars _)
      · rw [show fS "NCO" = 0 by simp [fS]]
        exact hv6 "nCO" _ (by decide) (by decide) (by decide) (by decide) (by decide) hCO
      · rw [show fS "NLV" = w0.LV.length by simp [fS]]
        exact hv6 "nLV" _ (by decide) (by decide) (by decide) (by decide) (by decide) hLV
      · rw [show fS "of" = ws.length + 1 by simp [fS]]
        exact ev_add (ev_var hm06 (by omega)) (evalB_lit (by omega)) (by omega)
      · rw [show fS "qk" = 2 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "po" = 0 by simp [fS]]; exact evalB_lit (by omega))
    (by decide)
  have hl7 : EnvLt (W + 1) τ7 := Run.envLt r7 hl6
  have ar7 : ArrW W τ7 := fun b' => by rw [a7]; exact ar6 b'
  have hm07 : τ7.vars "m0" = ws.length := by rw [f7 _ (by decide)]; exact hm06
  have hpc7 : τ7.vars "pc" = F.length := by rw [f7 _ (by decide)]; exact hpc6
  have hv7 : ∀ y v, y ∉ hdF.map Prod.fst → y ∉ ["fk", "ci", "lt", "m", "lL", "ls", "lN"] → y ∉ apV →
      y ∉ rmLs.wvars → y ∉ faV → y ∉ ["m0", "oc", "os", "yo"] → τ0.vars y = v →
      (Expr.var y).evalB (W + 1) τ7 = some v :=
    fun y v h0 h1 h2 h3 h4 h5 h => ev_var (by rw [f7 y h0, fr6 y h1 h2 h3 h4 h5, h])
      (by rw [← h, ← fr6 y h1 h2 h3 h4 h5, ← f7 y h0]; exact hl7.vars _)
  obtain ⟨τ8, r8, PR8, np8, f8, a8, l8, o8, i8⟩ := stPlan_run (W := W) (l := plF2)
    (ps := psFt ws.length w0.SG.length F.length w0.LV.length) (τ := τ7) rfl (ar7 "PR") (by simp [plF2]; omega)
    (by
      intro j hj
      simp only [plF2, List.length_cons, List.length_nil] at hj
      have eS := hv7 "nSG" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSG
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact ⟨evalB_lit (by omega), ev_add (evalB_lit (by omega)) eS (by omega)⟩
      · exact ⟨ev_add (ev_var hm07 (by omega)) (evalB_lit (by omega)) (by omega),
          ev_var hpc7 (by rw [← hpc7]; exact hl7.vars _)⟩
      · exact ⟨ev_add (evalB_lit (by omega)) eS (by omega),
          hv7 "nLV" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hLV⟩)
    (by decide)
  have hrunT := Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.ite_false (c := fE) hc7 (Run.seq r7 r8))))
  have hrun : Run (W + 1) (bFt fE) τ0 τ8 (kFt b ws F' (kFA G P Q s k₀ q₀ d i) 0) := by
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (gate_run (by rw [ov3]) (by omega) hrunT)))).mono ?_
    have hA : asgK [("m0", .var "m"), ("oc", .lit 0), ("os", .lit 1), ("yo", .lit plF)] = 9 := rfl
    have hB : asgK [("ls", .lit 0), ("lN", .var "pc")] = 5 := rfl
    have hC : asgK hdF = 29 := by decide
    have hD : (plF2.length * ((plF2.map fun p => p.1.size + p.2.size).sum + 6) + 4) = 58 := by decide
    rw [hA, hB, hC, hD]; simp only [Cond.size, Expr.size]; unfold kFt; omega
  have hl8 : EnvLt (W + 1) τ8 := Run.envLt hrun hl0
  have ar8 : ArrW W τ8 := fun b' => by
    by_cases hb : b' = "PR"
    · subst hb; exact l8
    · rw [a8 b' hb]; exact ar7 b'
  have ha8 : ∀ b', b' ≠ "PR" → τ8.arrs b' = τ6.arrs b' := fun b' hb => by rw [a8 b' hb, a7]
  have fr8 : ∀ y, y ≠ "np" → y ∉ hdF.map Prod.fst → y ∉ ["fk", "ci", "lt", "m", "lL", "ls", "lN"] → y ∉ apV →
      y ∉ rmLs.wvars → y ∉ faV → y ∉ ["m0", "oc", "os", "yo"] → τ8.vars y = τ0.vars y :=
    fun y h h0 h1 h2 h3 h4 h5 => by rw [f8 y h, f7 y h0, fr6 y h1 h2 h3 h4 h5]
  have hov8 : τ8.vars "ovf" = 0 := by
    rw [f8 _ (by decide), f7 _ (by decide), f6 _ (by decide), f5 _ (by decide), f4 _ (by decide), ov3]
  have hS8 : ∀ y, y ∈ hdF.map Prod.fst → τ8.vars y = fS y := fun y hy => by
    rw [f8 y (by intro h; subst h; simp [hdF] at hy)]; exact s7 y hy
  have hscR : ∀ y ∈ scR, y ≠ "np" ∧ y ∉ hdF.map Prod.fst ∧ y ∉ ["fk", "ci", "lt", "m", "lL", "ls", "lN"] ∧
      y ∉ apV ∧ y ∉ rmLs.wvars ∧ y ∉ faV ∧ y ∉ ["m0", "oc", "os", "yo"] := by decide
  have g : ∀ j (h : j < 9), τ8.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.dn d i 1)).getD j 0 := fun j h => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hscR _ (List.getElem_mem _)
    rw [fr8 _ a1 a2 a3 a4 a5 a6 a7]; exact hsc j (by omega)
  have hfr : ∀ y ∈ ["W", "rR", "bl", "gX", "nx", "mw"], y ≠ "np" ∧ y ∉ hdF.map Prod.fst ∧
      y ∉ ["fk", "ci", "lt", "m", "lL", "ls", "lN"] ∧ y ∉ apV ∧ y ∉ rmLs.wvars ∧ y ∉ faV ∧
      y ∉ ["m0", "oc", "os", "yo"] := by decide
  have fr8' : ∀ y ∈ ["W", "rR", "bl", "gX", "nx", "mw"], τ8.vars y = τ0.vars y := fun y hy => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hfr y hy; exact fr8 y a1 a2 a3 a4 a5 a6 a7
  have hos8 : τ8.vars "os" = 1 := by
    rw [f8 _ (by decide), f7 _ (by decide), f6 _ (by decide), f5 _ (by decide), f4 _ (by decide),
      f3 _ (by decide), P2.vars _ (by decide), s1 "os" (by simp)]
    simp [f1]
  have hF0 : 0 < F'.length := by simp [F']; omega
  refine ⟨τ8, _, hrun, le_rfl, fun _ => ⟨⟨?_, hkq, ar8, hl8, ?_, hR, ?_, ?_, ?_, ?_, ?_, hov8, ?_, ?_,
    PR8, np8, ?_, by simp [psFt]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => hov8⟩
  · rw [fr8' "W" (by simp), P0.hW]
  · rw [fr8' "rR" (by simp), P0.hrR]
  · refine L6.of ?_ ?_ (ha8 "a" (by decide)) (ha8 "st" (by decide)) (ha8 "ln" (by decide))
    · rw [f8 "m" (by decide), f7 _ (by decide)]
    · rw [f8 "lt" (by decide), f7 _ (by decide)]
  · simpa [scR, scW_dn] using g 0 (by omega)
  · rw [fr8' "bl" (by simp), P0.hbl]
  · intro j hj
    rw [ha8 "y" (by decide), a6 "y" (by decide), a5, a4 "y" (by decide), a3, P2.arrs "y" (by decide), a1]
    exact P0.hy j hj
  · simpa [scR, scW_dn] using g 1 (by omega)
  · -- the real query of the composition
    refine ⟨fun h => by simp [kindOf] at h, fun h => by simp [kindOf] at h, fun _ => ?_,
      fun h => by simp [kindOf] at h, by simp [kindOf]⟩
    have h1' : (L[1]'(by omega)) = toWord (shOf G t) := by
      rw [← h1]; simp only [L]; rw [List.getElem_append_left]
    have h2' : (L[ws.length + 1]'(by omega)) = toWord F[0] := by
      simp only [L]; rw [List.getElem_append_right (by omega)]; simp [F']
    refine ⟨1, ws.length + 1, by omega, by omega, hos8, ?_, ?_⟩
    · rw [hS8 "of" (by simp [hdF])]; simp [fS]
    · rw [realQ_compose, h1', h2']
  · rw [hS8 "qk" (by simp [hdF])]; simp [fS, kindOf]
  · intro p hp; simp [psFt] at hp; rcases hp with rfl | rfl | rfl <;> simp [hLl] <;> omega
  · rw [hS8 "Nt" (by simp [hdF])]; simp [fS, tagOf_dn]
  · rw [hS8 "Nw" (by simp [hdF])]; simp [fS, winOf_dn]
  · have hsw := sw_ftree (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) (d := d) (i := i)
    rw [scW_dn, hsw]
    have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
    have h3 := g 3 (by omega); have h4 := g 4 (by omega); have h5 := g 5 (by omega)
    have h6 := g 6 (by omega); have h7 := g 7 (by omega); have h8 := g 8 (by omega)
    simp only [scR, scW_dn, List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ,
      List.getD_cons_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    have hfl : (((faOf G (itm G P Q s k₀ q₀ d i).2).map toWord).filter
        (passSel (dW G P Q s) (swAt G P Q s k₀ q₀ (.dn d i 1)).SH)).length = F.length := by
      rw [show (swAt G P Q s k₀ q₀ (.dn d i 1)).SH = toWord (shOf G (itm G P Q s k₀ q₀ d i).2) by
        simp [swAt], ← faP_words (dW_ok G P Q s k₀ q₀)]; simp [F, t]
    simp only [hsV, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      hS8 "Nph" (by simp [hdF]), hS8 "Nd" (by simp [hdF]), hS8 "Ni" (by simp [hdF]), hS8 "Nm" (by simp [hdF]),
      hS8 "NSG" (by simp [hdF]), hS8 "NFA" (by simp [hdF]), hS8 "NCO" (by simp [hdF]),
      hS8 "NLV" (by simp [hdF])]
    simp [fS, w0, hfl, CO_dn1]
  · rw [hS8 "po" (by simp [hdF])]; simp [fS]
  · rw [fr8' "nx" (by simp)]
  · rw [fr8' "mw" (by simp)]
  · rw [o8, o7, o6, o5, o4, u3, P2.out, o1]; exact P0.hout

/-- **The plan after the far tree gives the state of the next position.** -/
theorem case_ft {d i : ℕ} :
    planW ((swAt G P Q s k₀ q₀ (.dn d i 1)).ws ++
        ([] :: (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord))
      (psFt (swAt G P Q s k₀ q₀ (.dn d i 1)).ws.length (swAt G P Q s k₀ q₀ (.dn d i 1)).SG.length
        (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length
        (swAt G P Q s k₀ q₀ (.dn d i 1)).LV.length) =
      (swAt G P Q s k₀ q₀ (.dn d i 2)).ws := by
  have := planW_ft (swAt G P Q s k₀ q₀ (.dn d i 1))
    ((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord)
    (FA_dn1 G P Q s k₀ q₀) (CO_dn1 G P Q s k₀ q₀) (OU_dn G P Q s k₀ q₀ d i 1)
  rw [List.length_map] at this
  have hSH : (swAt G P Q s k₀ q₀ (.dn d i 1)).SH = toWord (shOf G (itm G P Q s k₀ q₀ d i).2) := by
    simp [swAt]
  have e : ((faOf G (itm G P Q s k₀ q₀ d i).2).map toWord).filter
      (passSel (dW G P Q s) (swAt G P Q s k₀ q₀ (.dn d i 1)).SH) =
      (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord := by
    rw [hSH, ← faP_words (dW_ok G P Q s k₀ q₀)]
  rw [this, sw_ftree, e]

end Lax185574Proofs.ResolveRam.Glue
