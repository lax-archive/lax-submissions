import Lax185574Proofs.ResolveRam.Glue.CFinS
import Lax185574Proofs.ResolveRam.Glue.CFinU

/-!
The end of a round that finishes an item on the way down, by the next
position.

After the expansion of the item (`finE`), `finT` reads the length `lvL`
of the level of the item and the length `lvN` of the level below so far,
and branches: the next item of the level (`brA`), the level itself on
the way up when the level below is empty (`brD`), the first item of the
level below (`brB`), the first item of the last level on the way up
(`brC`). The facts at the branch are `FinAt`. One lemma per branch
gives the end of the round (`fin_a` to `fin_d`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax185574.ResolveLift
open Lax3.DistFO (rhoPlus)

/-- The next item of the level. -/
def brA : Com :=
  brDn (.lit 0) (.assign "ox" (.add (.var "ow") (.lit 1))) (.lit 1) (.var "dd") (.add (.var "ii") (.lit 1))

/-- The index of the first item of the level below. -/
def ixB (x : String) : Com :=
  .ite (.eq (.var "lvN") (.lit 0)) (.assign x (.var "e0"))
    (.assign x (.add (.sub (.var "ow") (.var "ii")) (.var "lvL")))

/-- The first item of the level below. -/
def brB : Com := brDn (.lit 1) (ixB "ox") (.lit 1) (.add (.var "dd") (.lit 1)) (.lit 0)

/-- The first item of the last level, on the way up. -/
def brC (atC : Com) : Com := brUp (.lit 0) (ixB "ow") atC (.lit 2) (.add (.var "dd") (.lit 1))

/-- The first item of the level, on the way up, when the level below is empty. -/
def brD (atC : Com) : Com :=
  brUp (.sub (.sub (.var "gq") (.var "dd")) (.lit 1)) (.assign "ow" (.sub (.var "ow") (.var "ii"))) atC
    (.lit 2) (.var "dd")

/-- The scalars of the branch. -/
def finTA : List (String × Expr) :=
  [("lvL", .get "a" (.add (.get "st" (.lit 3)) (.var "dd"))),
    ("lvN", .get "a" (.add (.add (.get "st" (.lit 3)) (.var "dd")) (.lit 1))), ("ne", .var "pc")]

/-- The end of a round after the expansion of an item. -/
def finT (atC : Com) : Com :=
  .seq (asgs finTA)
    (.ite (.lt (.add (.var "ii") (.lit 1)) (.var "lvL")) brA
      (.ite (.eq (.add (.var "lvN") (.var "ne")) (.lit 0)) (brD atC)
        (.ite (.lt (.add (.var "dd") (.lit 1)) (.var "gq")) brB (brC atC))))

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The library after the expansion of item `i` of level `d`, at position `dn d i m`. -/
noncomputable def finL1 (d i m : ℕ) : List (List ℕ) :=
  (swAt G P Q s k₀ q₀ (.dn d i m)).ws ++ [] :: coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2 ++
    exE G P Q s k₀ q₀ d i

/-- The index of the item word of item `i` of level `d` at position `dn d i m`. -/
noncomputable def finIw (d i m : ℕ) : ℕ :=
  4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length + (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length +
    (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length + offL G P Q s k₀ q₀ d + i

/-- The plan after item `i` of level `d`. -/
noncomputable def finPs (d i m : ℕ) : List (ℕ × ℕ) :=
  psFin (swAt G P Q s k₀ q₀ (.dn d i m)) (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length
    (finL1 G P Q s k₀ q₀ d i m).length
    ((swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length)
    (exE G P Q s k₀ q₀ d i).length

/-- The facts at the branch after the expansion of item `i` of level `d`. -/
structure FinAt (W R : ℕ) (d i m : ℕ) (wx b : List ℕ) (τ0 τ : Env) : Prop where
  P0 : PreR W R (scW G P Q s k₀ q₀ (.dn d i m)) (swAt G P Q s k₀ q₀ (.dn d i m)).ws wx b τ0
  M : FinMid W (scW G P Q s k₀ q₀ (.dn d i m)) b (finL1 G P Q s k₀ q₀ d i m) τ0 τ
  hm0 : τ.vars "m0" = (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length
  he0 : τ.vars "e0" =
    (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length
  hne : τ.vars "ne" = (exE G P Q s k₀ q₀ d i).length
  how : τ.vars "ow" = finIw G P Q s k₀ q₀ d i m
  hlvL : τ.vars "lvL" = (lvR G P Q s k₀ q₀ d).length
  hlvN : τ.vars "lvN" = (nxW G P Q s k₀ q₀ d i).length
  hS : ∃ S, total (finL1 G P Q s k₀ q₀ d i m) + (finL1 G P Q s k₀ q₀ d i m).length + b.length + 64 ≤ S ∧
    maxEntry (swAt G P Q s k₀ q₀ (.dn d i m)).ws.flatten ≤ S ∧ 2 ^ 24 * R * R * R * R * S * S < W

section

variable {G P Q s k₀ q₀}

theorem FinAt.room {W R d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env} (h : FinAt G P Q s k₀ q₀ W R d i m wx b τ0 τ)
    (hR : 1 ≤ R) :
    2 ^ 24 * (total (finL1 G P Q s k₀ q₀ d i m) + (finL1 G P Q s k₀ q₀ d i m).length + b.length + 64) ≤ W ∧
      2 ^ 24 * maxEntry (swAt G P Q s k₀ q₀ (.dn d i m)).ws.flatten ≤ W := by
  obtain ⟨S, h1, h3, h2⟩ := h.hS
  have : 2 ^ 24 * S ≤ 2 ^ 24 * R * R * R * R * S * S := by
    have hR4 : 1 ≤ R * R * R * R := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hS1 : 1 ≤ S := by omega
    calc 2 ^ 24 * S = 2 ^ 24 * 1 * S * 1 := by ring
      _ ≤ 2 ^ 24 * (R * R * R * R) * S * S := by gcongr
      _ = 2 ^ 24 * R * R * R * R * S * S := by ring
  constructor <;> omega

end

theorem length_ws_parts (w : SW) :
    w.ws.length = 4 + w.SG.length + w.FA.length + w.CO.length + w.LV.length + w.OU.length := by
  simp [SW.ws]; omega

theorem finL1_ws (d i m : ℕ) :
    finL1 G P Q s k₀ q₀ d i m = (swAt G P Q s k₀ q₀ (.dn d i m)).ws ++
      ([] :: coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2 ++ exE G P Q s k₀ q₀ d i) := by
  simp [finL1]

theorem finL1_get {d i m j : ℕ} (hj : j < (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length) :
    (finL1 G P Q s k₀ q₀ d i m)[j]'(by rw [finL1_ws]; simp; omega) = (swAt G P Q s k₀ q₀ (.dn d i m)).ws[j] := by
  simp only [finL1_ws]; rw [List.getElem_append_left hj]

theorem ws3_dn (d i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).ws[3]'(by have := length_SW_ws (swAt G P Q s k₀ q₀ (.dn d i m)); omega) =
      (swAt G P Q s k₀ q₀ (.dn d i m)).LL := by
  simp [SW.ws]

theorem ws0_dn (d i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).ws[0]'(by have := length_SW_ws (swAt G P Q s k₀ q₀ (.dn d i m)); omega) =
      ctW G P Q := by
  simp [SW.ws, swAt]

theorem length_LL_dn (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.dn d i m)).LL.length = d + 2 := by
  rw [ll_dn, List.length_append, length_llW]; rfl

theorem LL_dn_succ (d i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).LL[d + 1]'(by rw [length_LL_dn]; omega) = (nxW G P Q s k₀ q₀ d i).length := by
  simp only [ll_dn]
  rw [List.getElem_append_right (by rw [length_llW])]
  simp [length_llW]

theorem LL_dn_d (d i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).LL[d]'(by rw [length_LL_dn]; omega) = (lvR G P Q s k₀ q₀ d).length := by
  simp only [ll_dn]
  rw [List.getElem_append_left (by rw [length_llW]; omega)]
  simp [llW]

theorem psFin_bound {d i m : ℕ} :
    ∀ p ∈ finPs G P Q s k₀ q₀ d i m, p.1 + p.2 ≤ (finL1 G P Q s k₀ q₀ d i m).length + 1 := by
  intro p hp
  have hl := length_ws_parts (swAt G P Q s k₀ q₀ (.dn d i m))
  have hL1 : (finL1 G P Q s k₀ q₀ d i m).length = (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 +
      (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length + (exE G P Q s k₀ q₀ d i).length := by
    rw [finL1_ws]; simp; omega
  simp only [finPs, psFin, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

section

variable {G P Q s k₀ q₀}

/-- The scalars at the branch. -/
theorem FinAt.vars {W R d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env} (F : FinAt G P Q s k₀ q₀ W R d i m wx b τ0 τ) :
    τ.vars "dd" = d ∧ τ.vars "ii" = i ∧ τ.vars "gq" = q₀ ∧
      τ.vars "nSG" = (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length ∧
      τ.vars "nFA" = (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length ∧
      τ.vars "nCO" = (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length ∧
      τ.vars "nLV" = (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length := by
  have g := F.M.hsc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := g 10 (by omega); rw [scW_dn] at this; exact this
  · have := g 11 (by omega); rw [scW_dn] at this; exact this
  · have := g 8 (by omega); rw [scW_dn] at this; exact this
  · have := g 13 (by omega); rw [scW_dn] at this; exact this
  · have := g 14 (by omega); rw [scW_dn] at this; exact this
  · have := g 15 (by omega); rw [scW_dn] at this; exact this
  · have := g 16 (by omega); rw [scW_dn] at this; exact this

/-- The library at the branch. -/
theorem FinAt.lib {W R d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env} (F : FinAt G P Q s k₀ q₀ W R d i m wx b τ0 τ)
    (hR : 1 ≤ R) :
    ∃ h3 : 3 < (finL1 G P Q s k₀ q₀ d i m).length,
      (finL1 G P Q s k₀ q₀ d i m)[3] = (swAt G P Q s k₀ q₀ (.dn d i m)).LL ∧
      (finL1 G P Q s k₀ q₀ d i m)[0] = ctW G P Q ∧
      (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length ≤ (finL1 G P Q s k₀ q₀ d i m).length ∧
      d + 2 ≤ total (finL1 G P Q s k₀ q₀ d i m) ∧
      (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length + (exE G P Q s k₀ q₀ d i).length ≤
        (finL1 G P Q s k₀ q₀ d i m).length ∧
      2 ^ 24 * (total (finL1 G P Q s k₀ q₀ d i m) + (finL1 G P Q s k₀ q₀ d i m).length + b.length + 64) ≤ W := by
  have hw4 := length_SW_ws (swAt G P Q s k₀ q₀ (.dn d i m))
  have hwl := length_ws_parts (swAt G P Q s k₀ q₀ (.dn d i m))
  have hLl : (finL1 G P Q s k₀ q₀ d i m).length = (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 +
      (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length + (exE G P Q s k₀ q₀ d i).length := by
    rw [finL1_ws]; simp; omega
  have h3 : 3 < (finL1 G P Q s k₀ q₀ d i m).length := by omega
  have e3 : (finL1 G P Q s k₀ q₀ d i m)[3] = (swAt G P Q s k₀ q₀ (.dn d i m)).LL := by
    rw [finL1_get G P Q s k₀ q₀ (by omega), ws3_dn]
  refine ⟨h3, e3, by rw [finL1_get G P Q s k₀ q₀ (by omega), ws0_dn], by omega, ?_, by omega, (F.room hR).1⟩
  have := len_le_total h3
  rw [e3, length_LL_dn] at this
  exact this

end

set_option maxHeartbeats 3200000 in
/-- **The next item of the level.** -/
theorem fin_a {W R d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env} (hR : 1 ≤ R) (hkq : kq0 < W)
    (hi : i + 1 < (lvR G P Q s k₀ q₀ d).length)
    (F : FinAt G P Q s k₀ q₀ W R d i m wx b τ0 τ) :
    ∃ τ' K, Run (W + 1) brA τ τ' K ∧ K ≤ 40 * d + 600 ∧
      TailIn W R (ySz (xIn G k₀ q₀ P Q s)) (finL1 G P Q s k₀ q₀ d i m ++
          [(swAt G P Q s k₀ q₀ (.dn d (i + 1) 0)).LL])
        (finPs G P Q s k₀ q₀ d i m) (kindOf (callOf G P Q s k₀ q₀ (.dn d (i + 1) 0)))
        (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d (i + 1) 0))) b τ' ∧
      τ'.vars "Nt" = tagOf G P Q s k₀ q₀ (.dn d (i + 1) 0) ∧ τ'.vars "Nw" = winOf G P Q s k₀ q₀ (.dn d (i + 1) 0) ∧
      hsV.map τ'.vars = scW G P Q s k₀ q₀ (.dn d (i + 1) 0) ∧ τ'.vars "po" = 0 ∧
      τ'.vars "nx" = τ0.vars "nx" ∧ τ'.vars "mw" = τ0.vars "mw" ∧ τ'.out = [] ∧ τ'.vars "ovf" = 0 := by
  obtain ⟨hdd, hii, -, hnS, hnF, hnC, hnL⟩ := F.vars
  obtain ⟨h3, hL3, -, hwL, hd2, hLV, hroom⟩ := F.lib hR
  have hl := F.M.hlt
  have hsl : 9 ≤ (scW G P Q s k₀ q₀ (.dn d i m)).length := by rw [scW_dn]; simp
  have hwl := length_ws_parts (swAt G P Q s k₀ q₀ (.dn d i m))
  have hLLl := length_LL_dn G P Q s k₀ q₀ d i m
  have hnx : (nxW G P Q s k₀ q₀ d i).length ≤ (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length := by
    rw [LV_dn']; simp
  have hit := ws_item_j G P Q s k₀ q₀ (i := i) (m := m) hi
  have hidx := (List.getElem?_eq_some_iff.1 hit).1
  have hiw1 : finIw G P Q s k₀ q₀ d i m + 1 < (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length := by
    unfold finIw; omega
  have hLiw : (finL1 G P Q s k₀ q₀ d i m)[finIw G P Q s k₀ q₀ d i m + 1]'(by omega) =
      itemW (itm G P Q s k₀ q₀ d (i + 1)) := by
    rw [finL1_get G P Q s k₀ q₀ hiw1, itm_eq G P Q s k₀ q₀ hi, ← (List.getElem?_eq_some_iff.1 hit).2]
    congr 1
  have h3' : (finL1 G P Q s k₀ q₀ d i m)[3][d + 1]'(by rw [hL3]; omega) = (nxW G P Q s k₀ q₀ d i).length := by
    simp only [hL3]; exact LL_dn_succ G P Q s k₀ q₀ d i m
  obtain ⟨τ', K, r, hK, TI, n1, n2, n3, n4, n5, n6, n7, n8⟩ :=
    finDn_ok (ez := .lit 0) (cx := .assign "ox" (.add (.var "ow") (.lit 1))) (eph := .lit 1) (ed := .var "dd")
      (ei := .add (.var "ii") (.lit 1)) (ox := finIw G P Q s k₀ q₀ d i m + 1) (z := 0) (a1 := 1) (a2 := d)
      (a3 := i + 1) (X := ySz (xIn G k₀ q₀ P Q s)) (d := d) (e := (exE G P Q s k₀ q₀ d i).length)
      (M0 := (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length)
      (e0 := (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length)
      F.P0 (by rw [scW_dn]; rfl) (by rw [scW_dn]; rfl) hkq hR hsl F.M h3 hdd
      (by rw [hL3]; omega) (by rw [F.hlvN, h3']) F.hne (by rw [h3']; omega) (by omega) (evalB_lit (by omega))
      (fun ρ hρ hlρ => ⟨_, Run.assign (ev_add (ev_var (by rw [hρ "ow" (by decide) (by decide), F.how]) (by omega))
        (evalB_lit (by omega)) (by omega)), le_refl _⟩)
      F.hm0 F.he0 hnS hnF hnC hnL
      (fun ρ hρ => ⟨evalB_lit (by omega), ev_var (by rw [hρ "dd" (by decide) (by decide) (by decide), hdd])
        (by omega), ev_add (ev_var (by rw [hρ "ii" (by decide) (by decide) (by decide), hii]) (by omega))
        (evalB_lit (by omega)) (by omega)⟩)
      (by decide) (by omega) (by omega) (by omega) (by rw [hLiw]; simp [itemW])
      (psFin_bound G P Q s k₀ q₀ (d := d) (i := i) (m := m))
  have hLL' : llNew ((finL1 G P Q s k₀ q₀ d i m)[3]) d (exE G P Q s k₀ q₀ d i).length 0 =
      (swAt G P Q s k₀ q₀ (.dn d (i + 1) 0)).LL := by
    rw [hL3, sw_fin_a G P Q s k₀ q₀ (m := m)]; rfl
  rw [hLL'] at TI
  refine ⟨τ', K, r, by simp [asgK, hdFn, Expr.size] at hK; omega, ?_, by rw [n1, tagOf_dn],
    by rw [n2, winOf_dn], ?_, n4, n5, n6, n7, n8⟩
  · rw [callOf_dn0 G P Q s k₀ q₀ hi]
    simp only [kindOf, realQ]
    rw [toWord_itm, ← hLiw, finPs, psFin_eq]
    exact TI
  · rw [n3]
    simp only [scW_dn, sw_fin_a G P Q s k₀ q₀ (d := d) (i := i) (m := m)]
    simp [swFin]

/-- The value of `ixB`: the index of the first item of the level below. -/
noncomputable def finIx (d i m : ℕ) : ℕ :=
  if (nxW G P Q s k₀ q₀ d i).length = 0 then
    (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length
  else finIw G P Q s k₀ q₀ d i m - i + (lvR G P Q s k₀ q₀ d).length

theorem ixB_run {W : ℕ} {ρ : Env} (x : String) (hl : EnvLt (W + 1) ρ) {a e0 ow ii lvL : ℕ}
    (ha : ρ.vars "lvN" = a) (he : ρ.vars "e0" = e0) (hw : ρ.vars "ow" = ow) (hi : ρ.vars "ii" = ii)
    (hL : ρ.vars "lvL" = lvL) (hb : ow - ii + lvL < W + 1) :
    ∃ K, Run (W + 1) (ixB x) ρ (ρ.setVar x (if a = 0 then e0 else ow - ii + lvL)) K ∧ K ≤ 20 := by
  have hc := evalB_condEq (B := W + 1) (σ := ρ) (ev_var ha (by rw [← ha]; exact hl.vars _))
    (evalB_lit (n := 0) (by omega))
  by_cases h0 : a = 0
  · rw [if_pos h0]
    exact ⟨_, Run.ite_true (by rw [hc, h0]; rfl) (Run.assign (ev_var he (by rw [← he]; exact hl.vars _))),
      by simp [Cond.size, Expr.size]⟩
  · rw [if_neg h0]
    refine ⟨_, Run.ite_false (by rw [hc]; simp [h0])
      (Run.assign (ev_add (ev_sub (ev_var hw (by rw [← hw]; exact hl.vars _))
        (ev_var hi (by rw [← hi]; exact hl.vars _)) (by have := hl.vars "ow"; omega))
        (ev_var hL (by rw [← hL]; exact hl.vars _)) hb)), ?_⟩
    simp [Cond.size, Expr.size]

/-- The first item of the level below, in the library at the branch. -/
theorem fin_item_next {d i m : ℕ} (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length)
    (h0 : 0 < (lvR G P Q s k₀ q₀ (d + 1)).length) :
    (finL1 G P Q s k₀ q₀ d i m)[finIx G P Q s k₀ q₀ d i m]? = some (itemW (itm G P Q s k₀ q₀ (d + 1) 0)) := by
  have hl0 := lvW_get G P Q s k₀ q₀ (d := d + 1) h0
  unfold finIx
  split_ifs with hn
  · rw [finL1, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_cons]
    rw [show (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length -
      ((swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + ((coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length + 1)) = 0
      by omega, exE_item_next G P Q s k₀ q₀ hi hn, hl0]
  · have h := ws_item_next G P Q s k₀ q₀ (d := d) (i := i) (m := m) (by omega) (by omega)
    rw [hl0] at h
    have hlt := (List.getElem?_eq_some_iff.1 h).1
    rw [finL1_ws, List.getElem?_append_left (by unfold finIw; omega)]
    rw [← h]; congr 1; unfold finIw; omega

theorem rho_lvl {k₀ q₀ d : ℕ} (hd : d ≤ q₀) : rhoPlus (k₀ + d) (q₀ - d) ≤ rhoPlus (k₀ + 1) q₀ := by
  unfold rhoPlus
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega))

set_option maxHeartbeats 3200000 in
/-- **The first item of the level below.** -/
theorem fin_b {W R d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env} (hR : 1 ≤ R) (hkq : kq0 < W)
    (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length) (h0 : 0 < (lvR G P Q s k₀ q₀ (d + 1)).length)
    (F : FinAt G P Q s k₀ q₀ W R d i m wx b τ0 τ) :
    ∃ τ' K, Run (W + 1) brB τ τ' K ∧ K ≤ 40 * d + 600 ∧
      TailIn W R (ySz (xIn G k₀ q₀ P Q s)) (finL1 G P Q s k₀ q₀ d i m ++
          [(swAt G P Q s k₀ q₀ (.dn (d + 1) 0 0)).LL])
        (finPs G P Q s k₀ q₀ d i m) (kindOf (callOf G P Q s k₀ q₀ (.dn (d + 1) 0 0)))
        (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn (d + 1) 0 0))) b τ' ∧
      τ'.vars "Nt" = tagOf G P Q s k₀ q₀ (.dn (d + 1) 0 0) ∧ τ'.vars "Nw" = winOf G P Q s k₀ q₀ (.dn (d + 1) 0 0) ∧
      hsV.map τ'.vars = scW G P Q s k₀ q₀ (.dn (d + 1) 0 0) ∧ τ'.vars "po" = 0 ∧
      τ'.vars "nx" = τ0.vars "nx" ∧ τ'.vars "mw" = τ0.vars "mw" ∧ τ'.out = [] ∧ τ'.vars "ovf" = 0 := by
  obtain ⟨hdd, hii, -, hnS, hnF, hnC, hnL⟩ := F.vars
  obtain ⟨h3, hL3, -, hwL, hd2, hLV, hroom⟩ := F.lib hR
  have hl := F.M.hlt
  have hsl : 9 ≤ (scW G P Q s k₀ q₀ (.dn d i m)).length := by rw [scW_dn]; simp
  have hwl := length_ws_parts (swAt G P Q s k₀ q₀ (.dn d i m))
  have hLLl := length_LL_dn G P Q s k₀ q₀ d i m
  have hnx : (nxW G P Q s k₀ q₀ d i).length ≤ (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length := by
    rw [LV_dn']; simp
  have hit := fin_item_next G P Q s k₀ q₀ (m := m) hi h0
  have hix := (List.getElem?_eq_some_iff.1 hit).1
  have hLix : (finL1 G P Q s k₀ q₀ d i m)[finIx G P Q s k₀ q₀ d i m] = itemW (itm G P Q s k₀ q₀ (d + 1) 0) :=
    (List.getElem?_eq_some_iff.1 hit).2
  have hiwi : finIw G P Q s k₀ q₀ d i m - i + (lvR G P Q s k₀ q₀ d).length < W + 1 := by
    have : finIw G P Q s k₀ q₀ d i m < (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length := by
      have := (List.getElem?_eq_some_iff.1 (ws_item_j G P Q s k₀ q₀ (d := d) (i := i) (m := m) (j := i) (by omega))).1
      unfold finIw; omega
    unfold finIw at this ⊢; omega
  have h3' : (finL1 G P Q s k₀ q₀ d i m)[3][d + 1]'(by rw [hL3]; omega) = (nxW G P Q s k₀ q₀ d i).length := by
    simp only [hL3]; exact LL_dn_succ G P Q s k₀ q₀ d i m
  obtain ⟨τ', K, r, hK, TI, n1, n2, n3, n4, n5, n6, n7, n8⟩ :=
    finDn_ok (ez := .lit 1) (cx := ixB "ox") (eph := .lit 1) (ed := .add (.var "dd") (.lit 1))
      (ei := .lit 0) (ox := finIx G P Q s k₀ q₀ d i m) (z := 1) (a1 := 1) (a2 := d + 1)
      (a3 := 0) (X := ySz (xIn G k₀ q₀ P Q s)) (d := d) (e := (exE G P Q s k₀ q₀ d i).length)
      (M0 := (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length)
      (e0 := (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length)
      F.P0 (by rw [scW_dn]; rfl) (by rw [scW_dn]; rfl) hkq hR hsl F.M h3 hdd
      (by rw [hL3]; omega) (by rw [F.hlvN, h3']) F.hne (by rw [h3']; omega) (by omega) (evalB_lit (by omega))
      (fun ρ hρ hlρ => by
        obtain ⟨K', r', hK'⟩ := ixB_run "ox" hlρ (by rw [hρ "lvN" (by decide) (by decide), F.hlvN])
          (by rw [hρ "e0" (by decide) (by decide), F.he0]) (by rw [hρ "ow" (by decide) (by decide), F.how])
          (by rw [hρ "ii" (by decide) (by decide), hii]) (by rw [hρ "lvL" (by decide) (by decide), F.hlvL]) hiwi
        exact ⟨K', r', hK'⟩)
      F.hm0 F.he0 hnS hnF hnC hnL
      (fun ρ hρ => ⟨evalB_lit (by omega), ev_add (ev_var (by rw [hρ "dd" (by decide) (by decide) (by decide), hdd])
        (by omega)) (evalB_lit (by omega)) (by omega), evalB_lit (by omega)⟩)
      (by decide) (by omega) (by omega) hix (by rw [hLix]; simp [itemW])
      (psFin_bound G P Q s k₀ q₀ (d := d) (i := i) (m := m))
  have hLL' : llNew ((finL1 G P Q s k₀ q₀ d i m)[3]) d (exE G P Q s k₀ q₀ d i).length 1 =
      (swAt G P Q s k₀ q₀ (.dn (d + 1) 0 0)).LL := by
    rw [hL3, sw_fin_b G P Q s k₀ q₀ (m := m) hi]; rfl
  rw [hLL'] at TI
  refine ⟨τ', K, r, by simp [asgK, hdFn, Expr.size] at hK; omega, ?_, by rw [n1, tagOf_dn],
    by rw [n2, winOf_dn], ?_, n4, n5, n6, n7, n8⟩
  · rw [callOf_dn0 G P Q s k₀ q₀ h0]
    simp only [kindOf, realQ]
    rw [toWord_itm, ← hLix, finPs, psFin_eq]
    exact TI
  · rw [n3]
    simp only [scW_dn, sw_fin_b G P Q s k₀ q₀ (d := d) (i := i) (m := m) hi]
    simp [swFin]

theorem q_mem_item {p g : ℕ} {σ : TypeTree} : σ.q ∈ itemW ((p, g), σ) := by
  simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree]

/-- The constants of the cost of the query of the atom words. -/
noncomputable def cUp {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) : ℕ :=
  (finUp_ok hAt hAV).choose

/-- The exponent of the cost of the query of the atom words. -/
noncomputable def aUp {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) : ℕ :=
  (finUp_ok hAt hAV).choose_spec.choose

/-- The conclusion of a branch on the way up. -/
def FinUpOut (W R X : ℕ) (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (k : ℕ) (w b : List ℕ) (Nt Nw : ℕ)
    (nsc : List ℕ) (KB : ℕ) (c : Com) (τ0 τ : Env) : Prop :=
  ∃ τ' K, Run (W + 1) c τ τ' K ∧ K ≤ KB ∧
    (τ'.vars "ovf" = 0 → TailIn W R X L ps k w b τ' ∧ τ'.vars "Nt" = Nt ∧ τ'.vars "Nw" = Nw ∧
      hsV.map τ'.vars = nsc ∧ τ'.vars "po" = 0 ∧
      τ'.vars "nx" = τ0.vars "nx" ∧ τ'.vars "mw" = τ0.vars "mw" ∧ τ'.out = []) ∧
    (BigRoom W R L b (τ0.vars "nx") (τ0.vars "mw") → τ'.vars "ovf" = 0)

/-- The cost of a branch on the way up. -/
def kUp (L : List (List ℕ)) (b w : List ℕ) (cA aA c it ℓ ρ z : ℕ) : ℕ :=
  40 * z + 700 + kAtT L b w (cA * (c + 1) * (it + ℓ + ρ + 1) ^ aA)

set_option maxHeartbeats 1600000 in
/-- **The first item of the last level, on the way up.** -/
theorem fin_c {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) :
    ∀ {W d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env}, 1 ≤ k₀ → kq0 < W → d + 1 = q₀ →
      i + 1 = (lvR G P Q s k₀ q₀ d).length → 0 < (lvR G P Q s k₀ q₀ (d + 1)).length →
      FinAt G P Q s k₀ q₀ W (rhoPlus (k₀ + 1) q₀ + 2) d i m wx b τ0 τ →
      FinUpOut W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s))
        (finL1 G P Q s k₀ q₀ d i m ++ [(swAt G P Q s k₀ q₀ (.up (d + 1) 0 0)).LL,
          realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up (d + 1) 0 0))])
        (finPs G P Q s k₀ q₀ d i m) (kindOf (callOf G P Q s k₀ q₀ (.up (d + 1) 0 0)))
        (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up (d + 1) 0 0))) b
        (tagOf G P Q s k₀ q₀ (.up (d + 1) 0 0)) (winOf G P Q s k₀ q₀ (.up (d + 1) 0 0))
        (scW G P Q s k₀ q₀ (.up (d + 1) 0 0))
        (kUp (finL1 G P Q s k₀ q₀ d i m ++ [(swAt G P Q s k₀ q₀ (.up (d + 1) 0 0)).LL]) b
          (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up (d + 1) 0 0))) (cUp hAt hAV) (aUp hAt hAV) (ctW G P Q).length
          (itemW (itm G P Q s k₀ q₀ (d + 1) 0)).length (itm G P Q s k₀ q₀ (d + 1) 0).2.ℓ
          (rhoPlus (k₀ + 1) q₀) q₀)
        (brC atC) τ0 τ := by
  unfold cUp aUp
  intro W d i m wx b τ0 τ hk hkq HD hi H0 F
  have hR : 1 ≤ rhoPlus (k₀ + 1) q₀ + 2 := by omega
  obtain ⟨hdd, hii, hgq, hnS, hnF, hnC, hnL⟩ := F.vars
  obtain ⟨h3, hL3, hL0, hwL, hd2, hLV, hroom⟩ := F.lib hR
  have hroom2 := (F.room hR).2
  have hl := F.M.hlt
  have hsl : 9 ≤ (scW G P Q s k₀ q₀ (.dn d i m)).length := by rw [scW_dn]; simp
  have hwl := length_ws_parts (swAt G P Q s k₀ q₀ (.dn d i m))
  have hLLl := length_LL_dn G P Q s k₀ q₀ d i m
  have hnx : (nxW G P Q s k₀ q₀ d i).length ≤ (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length := by
    rw [LV_dn']; simp
  have hgP : τ.vars "gP" = P := by have := F.M.hsc 4 (by omega); rw [scW_dn] at this; exact this
  have hgQ : τ.vars "gQ" = Q := by have := F.M.hsc 5 (by omega); rw [scW_dn] at this; exact this
  have hgS : τ.vars "gS" = if s then 1 else 0 := by have := F.M.hsc 6 (by omega); rw [scW_dn] at this; exact this
  have hiw0 : finIw G P Q s k₀ q₀ d i m < (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length := by
    have := (List.getElem?_eq_some_iff.1 (ws_item_j G P Q s k₀ q₀ (d := d) (i := i) (m := m) (j := i)
      (by omega))).1
    unfold finIw; omega
  have h3' : (finL1 G P Q s k₀ q₀ d i m)[3][d + 1]'(by rw [hL3]; omega) = (nxW G P Q s k₀ q₀ d i).length := by
    simp only [hL3]; exact LL_dn_succ G P Q s k₀ q₀ d i m
  have hit := fin_item_next G P Q s k₀ q₀ (m := m) hi H0
  have hix := (List.getElem?_eq_some_iff.1 hit).1
  have hLix : (finL1 G P Q s k₀ q₀ d i m)[finIx G P Q s k₀ q₀ d i m] = itemW (itm G P Q s k₀ q₀ (d + 1) 0) :=
    (List.getElem?_eq_some_iff.1 hit).2
  have hiwi : finIw G P Q s k₀ q₀ d i m - i + (lvR G P Q s k₀ q₀ d).length < W + 1 := by
    unfold finIw at hiw0 ⊢; omega
  obtain ⟨ℓ, t, hx⟩ := lvR_shape G P Q s k₀ q₀ hk (d := d + 1) (by omega) H0
  have hσ : (itm G P Q s k₀ q₀ (d + 1) 0).2 = ⟨k₀ + (d + 1), q₀ - (d + 1), ℓ, t⟩ := by
    rw [itm_eq G P Q s k₀ q₀ H0, hx]
  have hRk : rhoPlus (itm G P Q s k₀ q₀ (d + 1) 0).2.k (itm G P Q s k₀ q₀ (d + 1) 0).2.q ≤
      rhoPlus (k₀ + 1) q₀ :=
      (congrArg (fun σ : TypeTree => rhoPlus σ.k σ.q) hσ).trans_le (rho_lvl (by omega))
  have hF := @Exists.choose_spec _ _ (@Exists.choose_spec _ _ (finUp_ok hAt hAV))
  beta_reduce at hF
  obtain ⟨τ', K, r, hK, hO, hB⟩ :=
    hF (ez := .lit 0) (cw := ixB "ow") (eph := .lit 2) (ed := .add (.var "dd") (.lit 1))
      (iw := finIx G P Q s k₀ q₀ d i m) (p := (itm G P Q s k₀ q₀ (d + 1) 0).1.1)
      (g := (itm G P Q s k₀ q₀ (d + 1) 0).1.2) (σ := (itm G P Q s k₀ q₀ (d + 1) 0).2) (P := P) (Q := Q)
      (sg := if s then 1 else 0) (z := 0) (a1 := 2) (a2 := d + 1) (Kw := 20)
      (X := ySz (xIn G k₀ q₀ P Q s)) (d := d) (e := (exE G P Q s k₀ q₀ d i).length)
      (M0 := (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length)
      (e0 := (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length)
      F.P0 (by rw [scW_dn]; rfl) (by rw [scW_dn]; rfl) hkq hR hsl F.M h3 hdd
      (by rw [hL3]; omega) (by rw [F.hlvN, h3']) F.hne (by rw [h3']; omega) (by omega) (evalB_lit (by omega))
      (fun ρ hρ hlρ => ixB_run "ow" hlρ (by rw [hρ "lvN" (by decide) (by decide), F.hlvN])
          (by rw [hρ "e0" (by decide) (by decide), F.he0]) (by rw [hρ "ow" (by decide) (by decide), F.how])
          (by rw [hρ "ii" (by decide) (by decide), hii]) (by rw [hρ "lvL" (by decide) (by decide), F.hlvL]) hiwi)
      hix hLix (by rw [hL0]; exact isCT_ctW G P Q) hgP hgQ hgS (by split_ifs <;> omega) (by omega)
      F.hm0 F.he0 hnS hnF hnC hnL
      (fun ρ hρ => ⟨evalB_lit (by omega), ev_add (ev_var (by rw [hρ "dd" (by decide), hdd])
        (by omega)) (evalB_lit (by omega)) (by omega)⟩)
      (by decide) (by omega) (by omega)
      (fun p hp => (psFin_bound G P Q s k₀ q₀ (d := d) (i := i) (m := m) p hp).trans (by omega))
  have hLL' : llNew ((finL1 G P Q s k₀ q₀ d i m)[3]) d (exE G P Q s k₀ q₀ d i).length 0 =
      (swAt G P Q s k₀ q₀ (.up (d + 1) 0 0)).LL := by
    rw [hL3, sw_fin_c G P Q s k₀ q₀ (m := m) HD hi]; rfl
  have hAQ : atQW ((finL1 G P Q s k₀ q₀ d i m)[0]'(Nat.lt_trans (by decide : 0 < 3) h3)) P Q (if s then 1 else 0) (itm G P Q s k₀ q₀ (d + 1) 0).2 =
      realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up (d + 1) 0 0)) := by
    rw [hL0, atQW_eq G P Q s k₀ q₀, callOf_up0 G P Q s k₀ q₀ H0, realQ_canon]
  have hk3 : kindOf (callOf G P Q s k₀ q₀ (.up (d + 1) 0 0)) = 3 := by
    rw [callOf_up0 G P Q s k₀ q₀ H0]; rfl
  rw [hLL', hAQ] at hK hO hB
  refine ⟨τ', K, r, ?_, fun hov => ?_, hB⟩
  · rw [hL0, hLix] at hK
    have hA : asgK (hdFn (.lit 2) (.add (.var "dd") (.lit 1)) (.lit 0) 3) ≤ 100 := by
      simp [asgK, hdFn, Expr.size]
    have hpow : (finUp_ok hAt hAV).choose * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ (d + 1) 0)).length +
        (itm G P Q s k₀ q₀ (d + 1) 0).2.ℓ + rhoPlus (itm G P Q s k₀ q₀ (d + 1) 0).2.k
          (itm G P Q s k₀ q₀ (d + 1) 0).2.q + 1) ^ (finUp_ok hAt hAV).choose_spec.choose ≤
        (finUp_ok hAt hAV).choose * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ (d + 1) 0)).length +
        (itm G P Q s k₀ q₀ (d + 1) 0).2.ℓ + rhoPlus (k₀ + 1) q₀ + 1) ^ (finUp_ok hAt hAV).choose_spec.choose :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    unfold kUp kAtT at *
    simp only [Expr.size] at hK
    omega
  obtain ⟨TI, n1, n2, n3, n4, n5, n6, n7⟩ := hO hov
  refine ⟨?_, by rw [n1, tagOf_up0 G P Q s k₀ q₀ (Or.inr (by omega))],
    by rw [n2, winOf_up0 G P Q s k₀ q₀ (Or.inr (by omega))], ?_, n4, n5, n6, n7⟩
  · rw [hk3, finPs, psFin_eq]; exact TI
  · rw [n3, scW_eq G P Q s k₀ q₀ (.dn d i m) (.up (d + 1) 0 0), sw_fin_c G P Q s k₀ q₀ (m := m) HD hi]
    simp [swFin, curW]

set_option maxHeartbeats 1600000 in
/-- **The first item of the level, on the way up, when the level below is empty.** -/
theorem fin_d {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) :
    ∀ {W d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env}, 1 ≤ k₀ → kq0 < W → d < q₀ →
      i + 1 = (lvR G P Q s k₀ q₀ d).length → (lvR G P Q s k₀ q₀ (d + 1)).length = 0 →
      FinAt G P Q s k₀ q₀ W (rhoPlus (k₀ + 1) q₀ + 2) d i m wx b τ0 τ →
      FinUpOut W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s))
        (finL1 G P Q s k₀ q₀ d i m ++ [(swAt G P Q s k₀ q₀ (.up d 0 0)).LL,
          realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d 0 0))])
        (finPs G P Q s k₀ q₀ d i m) (kindOf (callOf G P Q s k₀ q₀ (.up d 0 0)))
        (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d 0 0))) b
        (tagOf G P Q s k₀ q₀ (.up d 0 0)) (winOf G P Q s k₀ q₀ (.up d 0 0))
        (scW G P Q s k₀ q₀ (.up d 0 0))
        (kUp (finL1 G P Q s k₀ q₀ d i m ++ [(swAt G P Q s k₀ q₀ (.up d 0 0)).LL]) b
          (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d 0 0))) (cUp hAt hAV) (aUp hAt hAV) (ctW G P Q).length
          (itemW (itm G P Q s k₀ q₀ d 0)).length (itm G P Q s k₀ q₀ d 0).2.ℓ
          (rhoPlus (k₀ + 1) q₀) q₀)
        (brD atC) τ0 τ := by
  unfold cUp aUp
  intro W d i m wx b τ0 τ hk hkq hd hi HD F
  have hR : 1 ≤ rhoPlus (k₀ + 1) q₀ + 2 := by omega
  obtain ⟨hdd, hii, hgq, hnS, hnF, hnC, hnL⟩ := F.vars
  obtain ⟨h3, hL3, hL0, hwL, hd2, hLV, hroom⟩ := F.lib hR
  have hroom2 := (F.room hR).2
  have hl := F.M.hlt
  have hsl : 9 ≤ (scW G P Q s k₀ q₀ (.dn d i m)).length := by rw [scW_dn]; simp
  have hwl := length_ws_parts (swAt G P Q s k₀ q₀ (.dn d i m))
  have hLLl := length_LL_dn G P Q s k₀ q₀ d i m
  have hnx : (nxW G P Q s k₀ q₀ d i).length ≤ (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length := by
    rw [LV_dn']; simp
  have hgP : τ.vars "gP" = P := by have := F.M.hsc 4 (by omega); rw [scW_dn] at this; exact this
  have hgQ : τ.vars "gQ" = Q := by have := F.M.hsc 5 (by omega); rw [scW_dn] at this; exact this
  have hgS : τ.vars "gS" = if s then 1 else 0 := by have := F.M.hsc 6 (by omega); rw [scW_dn] at this; exact this
  have hiw0 : finIw G P Q s k₀ q₀ d i m < (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length := by
    have := (List.getElem?_eq_some_iff.1 (ws_item_j G P Q s k₀ q₀ (d := d) (i := i) (m := m) (j := i)
      (by omega))).1
    unfold finIw; omega
  have h3' : (finL1 G P Q s k₀ q₀ d i m)[3][d + 1]'(by rw [hL3]; omega) = (nxW G P Q s k₀ q₀ d i).length := by
    simp only [hL3]; exact LL_dn_succ G P Q s k₀ q₀ d i m
  have H0 : 0 < (lvR G P Q s k₀ q₀ d).length := by omega
  have hit0 := ws_item_j G P Q s k₀ q₀ (d := d) (i := i) (m := m) (j := 0) H0
  have hidx0 : finIw G P Q s k₀ q₀ d i m - i = 4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length +
      (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length + (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length +
      offL G P Q s k₀ q₀ d + 0 := by unfold finIw; omega
  have hlt0 := (List.getElem?_eq_some_iff.1 hit0).1
  have hit : (finL1 G P Q s k₀ q₀ d i m)[finIw G P Q s k₀ q₀ d i m - i]? =
      some (itemW (itm G P Q s k₀ q₀ d 0)) := by
    rw [finL1_ws, List.getElem?_append_left (by omega), hidx0, hit0, itm_eq G P Q s k₀ q₀ H0]
  have hix := (List.getElem?_eq_some_iff.1 hit).1
  have hLix : (finL1 G P Q s k₀ q₀ d i m)[finIw G P Q s k₀ q₀ d i m - i] = itemW (itm G P Q s k₀ q₀ d 0) :=
    (List.getElem?_eq_some_iff.1 hit).2
  obtain ⟨ℓ, t, hx⟩ := lvR_shape G P Q s k₀ q₀ hk (d := d) hd.le H0
  have hσ : (itm G P Q s k₀ q₀ d 0).2 = ⟨k₀ + d, q₀ - d, ℓ, t⟩ := by
    rw [itm_eq G P Q s k₀ q₀ H0, hx]
  have hRk : rhoPlus (itm G P Q s k₀ q₀ d 0).2.k (itm G P Q s k₀ q₀ d 0).2.q ≤ rhoPlus (k₀ + 1) q₀ := by
    rw [hσ]; exact rho_lvl hd.le
  have hqz : q₀ - d ≤ maxEntry (swAt G P Q s k₀ q₀ (.dn d i m)).ws.flatten := by
    have hm : itemW (itm G P Q s k₀ q₀ d 0) ∈ (swAt G P Q s k₀ q₀ (.dn d i m)).ws := by
      rw [← itm_eq G P Q s k₀ q₀ H0] at hit0; exact List.mem_of_getElem? hit0
    have hq : q₀ - d ∈ itemW (itm G P Q s k₀ q₀ d 0) := by
      have h1 : (itm G P Q s k₀ q₀ d 0).2.q = q₀ - d := by rw [hσ]
      rw [← h1]
      exact q_mem_item (p := (itm G P Q s k₀ q₀ d 0).1.1) (g := (itm G P Q s k₀ q₀ d 0).1.2)
    exact le_maxEntry (List.mem_flatten.2 ⟨_, hm, hq⟩)
  have hiw0' : finIw G P Q s k₀ q₀ d i m < W + 1 := by omega
  have hF := @Exists.choose_spec _ _ (@Exists.choose_spec _ _ (finUp_ok hAt hAV))
  beta_reduce at hF
  obtain ⟨τ', K, r, hK, hO, hB⟩ :=
    hF (ez := .sub (.sub (.var "gq") (.var "dd")) (.lit 1)) (cw := .assign "ow" (.sub (.var "ow") (.var "ii")))
      (eph := .lit 2) (ed := .var "dd")
      (iw := finIw G P Q s k₀ q₀ d i m - i) (p := (itm G P Q s k₀ q₀ d 0).1.1)
      (g := (itm G P Q s k₀ q₀ d 0).1.2) (σ := (itm G P Q s k₀ q₀ d 0).2) (P := P) (Q := Q)
      (sg := if s then 1 else 0) (z := q₀ - d - 1) (a1 := 2) (a2 := d) (Kw := 4)
      (X := ySz (xIn G k₀ q₀ P Q s)) (d := d) (e := (exE G P Q s k₀ q₀ d i).length)
      (M0 := (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length)
      (e0 := (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length)
      F.P0 (by rw [scW_dn]; rfl) (by rw [scW_dn]; rfl) hkq hR hsl F.M h3 hdd
      (by rw [hL3]; omega) (by rw [F.hlvN, h3']) F.hne (by rw [h3']; omega) (by omega)
      (ev_sub (ev_sub (ev_var hgq (by have := hl.vars "gq"; omega)) (ev_var hdd (by have := hl.vars "dd"; omega))
        (by have := hl.vars "gq"; omega)) (evalB_lit (by omega)) (by have := hl.vars "gq"; omega))
      (fun ρ hρ hlρ => ⟨_, Run.assign (ev_sub (ev_var (by rw [hρ "ow" (by decide) (by decide), F.how])
          (by omega)) (ev_var (by rw [hρ "ii" (by decide) (by decide), hii]) (by omega)) (by omega)),
        by simp [Expr.size]⟩)
      hix hLix (by rw [hL0]; exact isCT_ctW G P Q) hgP hgQ hgS (by split_ifs <;> omega) (by omega)
      F.hm0 F.he0 hnS hnF hnC hnL
      (fun ρ hρ => ⟨evalB_lit (by omega), ev_var (by rw [hρ "dd" (by decide), hdd]) (by omega)⟩)
      (by decide) (by omega) (by omega)
      (fun p hp => (psFin_bound G P Q s k₀ q₀ (d := d) (i := i) (m := m) p hp).trans (by omega))
  have hLL' : llNew ((finL1 G P Q s k₀ q₀ d i m)[3]) d (exE G P Q s k₀ q₀ d i).length (q₀ - d - 1) =
      (swAt G P Q s k₀ q₀ (.up d 0 0)).LL := by
    rw [hL3, sw_fin_d G P Q s k₀ q₀ (m := m) hd hi HD]; rfl
  have hAQ : atQW ((finL1 G P Q s k₀ q₀ d i m)[0]'(Nat.lt_trans (by decide : 0 < 3) h3)) P Q (if s then 1 else 0) (itm G P Q s k₀ q₀ d 0).2 =
      realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d 0 0)) := by
    rw [hL0, atQW_eq G P Q s k₀ q₀, callOf_up0 G P Q s k₀ q₀ H0, realQ_canon]
  have hk3 : kindOf (callOf G P Q s k₀ q₀ (.up d 0 0)) = 3 := by
    rw [callOf_up0 G P Q s k₀ q₀ H0]; rfl
  rw [hLL', hAQ] at hK hO hB
  refine ⟨τ', K, r, ?_, fun hov => ?_, hB⟩
  · rw [hL0, hLix] at hK
    have hA : asgK (hdFn (.lit 2) (.var "dd") (.lit 0) 3) ≤ 100 := by
      simp [asgK, hdFn, Expr.size]
    have hpow : (finUp_ok hAt hAV).choose * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ d 0)).length +
        (itm G P Q s k₀ q₀ d 0).2.ℓ + rhoPlus (itm G P Q s k₀ q₀ d 0).2.k
          (itm G P Q s k₀ q₀ d 0).2.q + 1) ^ (finUp_ok hAt hAV).choose_spec.choose ≤
        (finUp_ok hAt hAV).choose * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ d 0)).length +
        (itm G P Q s k₀ q₀ d 0).2.ℓ + rhoPlus (k₀ + 1) q₀ + 1) ^ (finUp_ok hAt hAV).choose_spec.choose :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    unfold kUp kAtT at *
    simp only [Expr.size] at hK
    omega
  obtain ⟨TI, n1, n2, n3, n4, n5, n6, n7⟩ := hO hov
  refine ⟨?_, by rw [n1, tagOf_up0 G P Q s k₀ q₀ (Or.inl hd)],
    by rw [n2, winOf_up0 G P Q s k₀ q₀ (Or.inl hd)], ?_, n4, n5, n6, n7⟩
  · rw [hk3, finPs, psFin_eq]; exact TI
  · rw [n3, scW_eq G P Q s k₀ q₀ (.dn d i m) (.up d 0 0), sw_fin_d G P Q s k₀ q₀ (m := m) hd hi HD]
    simp [swFin, curW]

end Lax185574Proofs.ResolveRam.Glue
