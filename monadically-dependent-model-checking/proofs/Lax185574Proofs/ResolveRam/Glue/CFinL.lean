import Lax185574Proofs.ResolveRam.Glue.CFinF
import Lax185574Proofs.ResolveRam.Glue.CComp

/-!
The case after the last composition of an item on the way down
(position `dn d i m`, `2 ≤ m`, `m + 1 = nDn d i`): the compositions are
copied after an empty word, the answer is appended, and the item is
finished (`bLast_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax185574.ResolveLift
open Lax3.DistFO (rhoPlus)

/-- The range of the compositions. -/
def lrA : List (String × Expr) :=
  [("lo", .add (.add (.lit 4) (.var "nSG")) (.var "nFA")), ("lN", .var "nCO")]

/-- The case after the last composition of an item. -/
noncomputable def bLast (atC : Com) : Com :=
  .seq (.assign "m0" (.var "m")) (.seq apE (.seq (asgs lrA) (.seq lbRng (.seq (apY plC dlC) (fE atC)))))

/-- The cost of the case after the last composition, without the end of the item. -/
def kLast (b : List ℕ) (ws : List (List ℕ)) : ℕ := b.length * 18 + 18 * total ws + 60 * ws.length + 200

theorem rng_ws_CO (w : SW) (M : List (List ℕ)) :
    rng (w.ws ++ M) (4 + w.SG.length + w.FA.length) w.CO.length = w.CO := by
  have e : w.ws ++ M = (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA)) ++ (w.CO ++ (w.LV ++ w.OU ++ M)) := by
    rw [SW.ws_eq]; simp
  have hl : (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA)).length = 4 + w.SG.length + w.FA.length := by
    simp; omega
  have := rng_append_right (L := w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA))
    (M := w.CO ++ (w.LV ++ w.OU ++ M)) (lo := 0) (N := w.CO.length)
  simp only [Nat.add_zero] at this
  rw [hl] at this
  rw [e, this, rng_append_left (by simp), rng_full]

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

set_option maxHeartbeats 3200000 in
/-- **The case after the last composition of an item.** -/
theorem bLast_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {d i m W : ℕ} (hk : 1 ≤ k₀) (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm2 : 2 ≤ m)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i) :
    BodyCall (bLast atC) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.dn d i m))
      (swAt G P Q s k₀ q₀ (.dn d i m)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.dn d i m)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m)))
      (finL1 G P Q s k₀ q₀ d i m ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (finPs G P Q s k₀ q₀ d i m) (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (kLast (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))) (swAt G P Q s k₀ q₀ (.dn d i m)).ws +
        (kFE G P Q s k₀ q₀ d i m (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))) + 104 +
          kBr G P Q s k₀ q₀ hAt hAV d i m (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m)))
            (next G P Q s k₀ q₀ (.dn d i m)))) := by
  intro τ0 P0 hov hkq
  set t := (itm G P Q s k₀ q₀ d i).2
  set F := faP G (dataOf G P Q s k₀ q₀) t
  have hnd := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
  rw [← show F = faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2 from rfl] at hnd
  obtain ⟨hb0, hc0⟩ := callOf_dn_comp G P Q s k₀ q₀ hi hm2 (by omega)
  rw [hc0] at P0 ⊢
  set R := rhoPlus (k₀ + 1) q₀ + 2
  have hR : 1 ≤ R := by omega
  set w0 := swAt G P Q s k₀ q₀ (.dn d i m)
  set ws := w0.ws
  set b := rY G k₀ q₀ (.compose (shOf G t) F[m - 2])
  set Y := realY G k₀ q₀ (.compose (shOf G t) F[m - 2])
  have hCOw : w0.CO = (coW G P Q s k₀ q₀ t).take (m - 2) := by simp [w0, swAt, t]
  have hroom : RoomOK W R τ0 ws b := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS := room_bound hroom hR
  obtain ⟨hS1, hS2, hS3, hS4⟩ := sOfV_ge (τ := τ0) (ws := ws) (b := b)
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hl0 := P0.hlt
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.dn d i m)).getD j 0 := P0.hsc
  have hSG : τ0.vars "nSG" = w0.SG.length := by simpa [scR, scW_dn] using hsc 13 (by omega)
  have hFA : τ0.vars "nFA" = w0.FA.length := by simpa [scR, scW_dn] using hsc 14 (by omega)
  have hCO : τ0.vars "nCO" = w0.CO.length := by simpa [scR, scW_dn] using hsc 15 (by omega)
  have hwsl := length_ws_parts w0
  have hwse : ws.length = w0.ws.length := rfl
  have hb0' : m - 2 < (faP G (dataOf G P Q s k₀ q₀) t).length := hb0
  have hFt : F.length = (faP G (dataOf G P Q s k₀ q₀) t).length := rfl
  have hCOl : w0.CO.length = m - 2 := by
    rw [hCOw, List.length_take, length_coW]; omega
  -- step 1: m0
  set τ1 := τ0.setVar "m0" ws.length
  have r1 : Run (W + 1) (.assign "m0" (.var "m")) τ0 τ1 2 := Run.assign (ev_var P0.hlib.m (by omega))
  have L1 : Lib ws τ1 := P0.hlib.of (by simp [τ1]) (by simp [τ1]) rfl rfl rfl
  have ar1 : ArrW W τ1 := P0.harr
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hl0
  -- step 2: the empty word
  obtain ⟨τ2, r2, L2, f2, a2, ar2, o2, i2⟩ := apE_run L1 ar1 (by omega)
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt r2 hl1
  have fr2 : ∀ y, y ∉ apV → y ≠ "m0" → τ2.vars y = τ0.vars y := fun y h1 h2 => by
    rw [f2 y h1]; simp [τ1, h2]
  -- step 3: the range of the compositions
  let f3 : String → ℕ := fun y => if y = "lo" then 4 + w0.SG.length + w0.FA.length else w0.CO.length
  obtain ⟨τ3, r3, s3, g3, a3, o3, i3⟩ := asgs_run (B := W + 1) (τ := τ2) (l := lrA) (f := f3)
    (by
      intro p hp
      simp only [lrA, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [show f3 "lo" = 4 + w0.SG.length + w0.FA.length by simp [f3]]
        exact ev_add (ev_add (evalB_lit (by omega)) (ev_var (by rw [fr2 "nSG" (by decide) (by decide), hSG])
          (by omega)) (by omega)) (ev_var (by rw [fr2 "nFA" (by decide) (by decide), hFA]) (by omega)) (by omega)
      · rw [show f3 "lN" = w0.CO.length by simp [f3]]
        exact ev_var (by rw [fr2 "nCO" (by decide) (by decide), hCO]) (by omega))
    (by decide)
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  have L3 : Lib (ws ++ [[]]) τ3 := L2.of (by rw [g3 "m" (by decide)]) (by rw [g3 "lt" (by decide)])
    (by rw [a3]) (by rw [a3]) (by rw [a3])
  have hwt : total (ws ++ [[]]) = total ws := by simp [total]
  obtain ⟨τ4, r4, L4, f4, a4, l4, o4, i4⟩ := lbRng_run (W := W) (ws := ws ++ [[]])
    (lo := 4 + w0.SG.length + w0.FA.length) (N := w0.CO.length) L3
    (by rw [s3 "lo" (by decide)]; simp [f3]) (by rw [s3 "lN" (by decide)]; simp [f3]) (by simp; omega)
    (by rw [a3, ar2 "a", hwt]; omega) (by rw [a3, ar2 "st"]; simp; omega) (by rw [a3, ar2 "ln"]; simp; omega)
    (by rw [hwt]; simp; omega) (lib_lt L3.at_ hl3)
  rw [rng_ws_CO w0 [[]]] at L4 r4
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt r4 hl3
  have ar4 : ArrW W τ4 := fun b' => by rw [l4, a3]; exact ar2 b'
  -- step 4: the answer
  have hyb : SegAt "y" 0 b τ4 := fun j hj => by
    rw [a4 "y" (by decide), a3, a2 "y" (by decide)]; exact P0.hy j hj
  have hbv : ∀ v ∈ b, v ≤ W := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have := P0.hy j hj
    have := hl0.arrs "y" _ (List.mem_of_getElem? (by simpa using this))
    omega
  obtain ⟨pre, post, hsp, hpre, hpp⟩ := rY_split G k₀ q₀ (.compose (shOf G t) F[m - 2])
  have hdl : dlC ≤ b.length := by
    rw [← dLen_comp (shOf G t) F[m - 2], ← hpp]; simp only [b, hsp, List.length_append]; omega
  have hpd : plC ≤ dlC := by unfold plC dlC; omega
  have hCOt : total w0.CO ≤ total ws := by
    have := total_le_of_sub (rng_sub (ws ++ [[]]) (4 + w0.SG.length + w0.FA.length) w0.CO.length)
    rw [rng_ws_CO w0 [[]], hwt] at this; exact this
  obtain ⟨τ5, r5, L5, f5, a5, ar5, o5, i5⟩ := apY_run (pl := plC) (dl := dlC) L4 ar4
    (by rw [f4 "bl" (by decide), g3 "bl" (by decide), fr2 "bl" (by decide) (by decide), P0.hbl]) hyb hdl hpd
    (by
      have : plC ≤ b.length := by omega
      simp only [total_append, total_single, List.length_append, List.length_cons, List.length_nil]; omega) hbv
  have hYw : (b.drop plC).take (b.length - dlC) = Y := by
    have := realY_seg G k₀ q₀ (.compose (shOf G t) F[m - 2])
    rw [dLen_comp, preLen_comp] at this; exact this
  have hCw : w0.CO ++ [Y] = coW G P Q s k₀ q₀ t := by
    have hlen : (coW G P Q s k₀ q₀ t).length = m - 2 + 1 := by rw [length_coW]; omega
    have e1 : coW G P Q s k₀ q₀ t = (coW G P Q s k₀ q₀ t).take (m - 2 + 1) :=
      (List.take_of_length_le (by omega)).symm
    rw [hCOw]
    conv_rhs => rw [e1, List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp [Y, coW, realY, F]
  rw [hYw, List.append_assoc, List.append_assoc, hCw, List.singleton_append] at L5
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt r5 hl4
  -- step 5: the end of the item
  have fr5 : ∀ y, y ∉ apV → y ∉ ["fk", "ci", "lt", "m", "lL", "ls"] → y ∉ ["lo", "lN"] → y ≠ "m0" →
      τ5.vars y = τ0.vars y := fun y h1 h2 h3 h4 => by
    rw [f5 y h1, f4 y h2, g3 y (by simpa [lrA] using h3), fr2 y h1 h4]
  have hsR : ∀ y ∈ scR, y ∉ apV ∧ y ∉ ["fk", "ci", "lt", "m", "lL", "ls"] ∧ y ∉ ["lo", "lN"] ∧ y ≠ "m0" := by
    decide
  have M5 : FinMid W (scW G P Q s k₀ q₀ (.dn d i m)) b (ws ++ [] :: coW G P Q s k₀ q₀ t) τ0 τ5 := by
    refine ⟨?_, ar5, hl5, L5, fun j h => ?_, fun y hy => ?_, ?_, ?_, ?_⟩
    · rw [fr5 "W" (by decide) (by decide) (by decide) (by decide), P0.hW]
    · obtain ⟨e1, e2, e3, e4⟩ := hsR _ (List.getElem_mem (l := scR) (n := j) (by simp [scR]; omega))
      rw [fr5 _ e1 e2 e3 e4]; exact hsc j h
    · exact fr5 y (by revert y; decide) (by revert y; decide) (by revert y; decide) (by revert y; decide)
    · rw [a5 "y" (by decide), a4 "y" (by decide), a3, a2 "y" (by decide)]; simp [τ1]
    · rw [fr5 "ovf" (by decide) (by decide) (by decide) (by decide), hov]
    · rw [o5, o4, o3, o2]; simp [τ1, P0.hout]
  have hm05 : τ5.vars "m0" = ws.length := by
    rw [f5 _ (by decide), f4 _ (by decide), g3 _ (by decide), f2 _ (by decide)]; simp [τ1]
  obtain ⟨τ', K, r, hK, hO, hB⟩ := fE_ok G P Q s k₀ q₀ hAt hAV hk hkq hd hi hm P0 M5 hm05
  have hrun := Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r))))
  refine ⟨τ', _, hrun, ?_, hO, hB⟩
  have hA : asgK lrA ≤ 20 := by decide
  unfold kLast
  omega

end Lax185574Proofs.ResolveRam.Glue
