import Lax185574Proofs.ResolveRam.Glue.CFinR
import Lax185574Proofs.ResolveRam.Glue.PAt9

/-!
The end of a round that finishes an item on the way down: reading the
lengths of the level and of the level below, and branching to the next
position (`finT_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax185574.ResolveLift
open Lax3.DistFO (rhoPlus)

theorem atKeep_atV : ∀ y ∈ atKeep, y ∉ atV := by decide

/-- **Reading an entry of the word with index `3` of the library.** -/
theorem ev_wd3e {W : ℕ} {L : List (List ℕ)} {τ : Env} {e : Expr} {j : ℕ} (hw : WordsAt L τ)
    (hi : 3 < L.length) (he : e.evalB (W + 1) τ = some j) (hj : j < L[3].length) (hl : EnvLt (W + 1) τ)
    (harr : ArrW W τ) (hW3 : 3 ≤ W) :
    (Expr.get "a" (.add (.get "st" (.lit 3)) e)).evalB (W + 1) τ = some L[3][j] := by
  have hst := hw.st 3 hi
  have hoff : off L 3 < W + 1 := hl.arrs "st" _ (List.mem_of_getElem? hst)
  have ha := hw.a 3 hi j hj
  have hval : L[3][j] < W + 1 := hl.arrs "a" _ (List.mem_of_getElem? ha)
  have hidx : off L 3 + j < W + 1 := by
    have := (List.getElem?_eq_some_iff.1 ha).1
    rw [harr "a"] at this; exact this
  exact evalB_get (ev_add (evalB_get (evalB_lit (by omega)) hst hoff) he hidx) ha hval

/-- The scalars of the branch, with the level below read at `dd + 1`. -/
def finTA' : List (String × Expr) :=
  [("lvL", .get "a" (.add (.get "st" (.lit 3)) (.var "dd"))),
    ("lvN", .get "a" (.add (.get "st" (.lit 3)) (.add (.var "dd") (.lit 1)))), ("ne", .var "pc")]

/-- The end of a round after the expansion of an item. -/
def finT' (atC : Com) : Com :=
  .seq (asgs finTA')
    (.ite (.lt (.add (.var "ii") (.lit 1)) (.var "lvL")) brA
      (.ite (.eq (.add (.var "lvN") (.var "ne")) (.lit 0)) (brD atC)
        (.ite (.lt (.add (.var "dd") (.lit 1)) (.var "gq")) brB (brC atC))))

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The facts after the expansion of item `i` of level `d`. -/
structure FinPre (W R : ℕ) (d i m : ℕ) (wx b : List ℕ) (τ0 τ : Env) : Prop where
  P0 : PreR W R (scW G P Q s k₀ q₀ (.dn d i m)) (swAt G P Q s k₀ q₀ (.dn d i m)).ws wx b τ0
  M : FinMid W (scW G P Q s k₀ q₀ (.dn d i m)) b (finL1 G P Q s k₀ q₀ d i m) τ0 τ
  hm0 : τ.vars "m0" = (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length
  he0 : τ.vars "e0" =
    (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length
  hpc : τ.vars "pc" = (exE G P Q s k₀ q₀ d i).length
  how : τ.vars "ow" = finIw G P Q s k₀ q₀ d i m
  hS : ∃ S, total (finL1 G P Q s k₀ q₀ d i m) + (finL1 G P Q s k₀ q₀ d i m).length + b.length + 64 ≤ S ∧
    maxEntry (swAt G P Q s k₀ q₀ (.dn d i m)).ws.flatten ≤ S ∧ 2 ^ 24 * R * R * R * R * S * S < W

theorem scR_finTA : ∀ y ∈ scR, y ∉ finTA'.map Prod.fst := by decide

theorem room_of_S {R S W : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (h : 2 ^ 24 * R * R * R * R * S * S < W) :
    2 ^ 24 * S ≤ W := by
  have hR4 : 1 ≤ R * R * R * R := Nat.one_le_iff_ne_zero.2 (by positivity)
  have : 2 ^ 24 * S ≤ 2 ^ 24 * R * R * R * R * S * S := by
    calc 2 ^ 24 * S = 2 ^ 24 * 1 * S * 1 := by ring
      _ ≤ 2 ^ 24 * (R * R * R * R) * S * S := by gcongr
      _ = 2 ^ 24 * R * R * R * R * S * S := by ring
  omega

theorem length_lvW (d : ℕ) : (lvW G P Q s k₀ q₀ d).length = (lvR G P Q s k₀ q₀ d).length := by
  simp [lvW]

set_option maxHeartbeats 1600000 in
theorem finTA_run {W R d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env} (hR : 1 ≤ R)
    (F : FinPre G P Q s k₀ q₀ W R d i m wx b τ0 τ) :
    ∃ τ1, Run (W + 1) (asgs finTA') τ τ1 (asgK finTA') ∧ FinAt G P Q s k₀ q₀ W R d i m wx b τ0 τ1 := by
  have hl := F.M.hlt
  have hdd : τ.vars "dd" = d := by have := F.M.hsc 10 (by omega); rw [scW_dn] at this; exact this
  have hw4 := length_SW_ws (swAt G P Q s k₀ q₀ (.dn d i m))
  have hwl := length_ws_parts (swAt G P Q s k₀ q₀ (.dn d i m))
  have hLl : (finL1 G P Q s k₀ q₀ d i m).length = (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 +
      (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length + (exE G P Q s k₀ q₀ d i).length := by
    rw [finL1_ws]; simp; omega
  have h3 : 3 < (finL1 G P Q s k₀ q₀ d i m).length := by omega
  have hL3 : (finL1 G P Q s k₀ q₀ d i m)[3] = (swAt G P Q s k₀ q₀ (.dn d i m)).LL := by
    rw [finL1_get G P Q s k₀ q₀ (by omega), ws3_dn]
  have hLLl := length_LL_dn G P Q s k₀ q₀ d i m
  obtain ⟨S, hS1, -, hS2⟩ := F.hS
  have hWS := room_of_S hR (by omega) hS2
  have hd2W : d + 2 ≤ W := by
    have h4 : 4 < (finL1 G P Q s k₀ q₀ d i m).length := by omega
    have hst := F.M.hlib.at_.st 4 h4
    have h1 := hl.arrs "st" _ (List.mem_of_getElem? hst)
    have hs : off (finL1 G P Q s k₀ q₀ d i m) 4 = off (finL1 G P Q s k₀ q₀ d i m) 3 +
        (finL1 G P Q s k₀ q₀ d i m)[3].length := off_succ h3
    have h2 : (finL1 G P Q s k₀ q₀ d i m)[3].length = d + 2 := by rw [hL3, hLLl]
    omega
  let f : String → ℕ := fun y => if y = "lvL" then (lvR G P Q s k₀ q₀ d).length
    else if y = "lvN" then (nxW G P Q s k₀ q₀ d i).length else (exE G P Q s k₀ q₀ d i).length
  obtain ⟨τ1, r, s1, g1, a1, o1, -⟩ := asgs_run (B := W + 1) (τ := τ) (l := finTA') (f := f)
    (by
      intro p hp
      simp only [finTA', List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rw [ev_wd3e F.M.hlib.at_ h3 (ev_var hdd (by have := hl.vars "dd"; omega)) (by rw [hL3]; omega) hl
          F.M.harr (by omega)]
        congr 1; simp only [hL3, f, if_pos rfl]; exact LL_dn_d G P Q s k₀ q₀ d i m
      · rw [ev_wd3e F.M.hlib.at_ h3 (ev_add (ev_var hdd (by have := hl.vars "dd"; omega)) (evalB_lit (by omega))
          (by omega)) (by rw [hL3]; omega) hl F.M.harr (by omega)]
        congr 1; simp only [hL3, f]; exact LL_dn_succ G P Q s k₀ q₀ d i m
      · exact ev_var F.hpc (by have := hl.vars "pc"; rw [F.hpc] at this; simpa [f] using this))
    (by decide)
  refine ⟨τ1, r, F.P0, ⟨by rw [g1 "W" (by decide)]; exact F.M.hW, fun b' => by rw [a1]; exact F.M.harr b',
    Run.envLt r hl, F.M.hlib.of (g1 "m" (by decide)) (g1 "lt" (by decide)) (by rw [a1]) (by rw [a1]) (by rw [a1]),
    fun j h => by rw [g1 _ (scR_finTA _ (List.getElem_mem _))]; exact F.M.hsc j h,
    fun y hy => by rw [g1 y (by revert y; decide)]; exact F.M.hfr y hy, by rw [a1]; exact F.M.hy,
    by rw [g1 "ovf" (by decide)]; exact F.M.hov, by rw [o1]; exact F.M.hout⟩,
    by rw [g1 "m0" (by decide)]; exact F.hm0, by rw [g1 "e0" (by decide)]; exact F.he0,
    by rw [s1 "ne" (by decide)]; simp [f], by rw [g1 "ow" (by decide)]; exact F.how,
    by rw [s1 "lvL" (by decide)]; simp [f], by rw [s1 "lvN" (by decide)]; simp [f], F.hS⟩

/-- The new words of the round after an item, by the next position. -/
noncomputable def finNew : Cur → List (List ℕ)
  | .up d i m => [(swAt G P Q s k₀ q₀ (.up d i m)).LL, realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m))]
  | c => [(swAt G P Q s k₀ q₀ c).LL]

/-- The cost of the branch to the next position. -/
noncomputable def kBr {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    (d i m : ℕ) (b : List ℕ) : Cur → ℕ
  | .up d' j m' => kUp (finL1 G P Q s k₀ q₀ d i m ++ [(swAt G P Q s k₀ q₀ (.up d' j m')).LL]) b
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d' j m'))) (cUp hAt hAV) (aUp hAt hAV) (ctW G P Q).length
      (itemW (itm G P Q s k₀ q₀ d' 0)).length (itm G P Q s k₀ q₀ d' 0).2.ℓ (rhoPlus (k₀ + 1) q₀) q₀
  | _ => 40 * q₀ + 600

set_option maxHeartbeats 6400000 in
/-- **The end of a round after the expansion of an item.** -/
theorem finT_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {W d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env} (hk : 1 ≤ k₀) (hkq : kq0 < W) (hd : d < q₀)
    (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m + 1 = nDn G P Q s k₀ q₀ d i)
    (F : FinPre G P Q s k₀ q₀ W (rhoPlus (k₀ + 1) q₀ + 2) d i m wx b τ0 τ) :
    FinUpOut W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s))
      (finL1 G P Q s k₀ q₀ d i m ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (finPs G P Q s k₀ q₀ d i m) (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))) b
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (100 + kBr G P Q s k₀ q₀ hAt hAV d i m b (next G P Q s k₀ q₀ (.dn d i m))) (finT' atC) τ0 τ := by
  have hR : 1 ≤ rhoPlus (k₀ + 1) q₀ + 2 := by omega
  obtain ⟨τ1, rA, F1⟩ := finTA_run G P Q s k₀ q₀ hR F
  obtain ⟨hdd, hii, hgq, -, -, -, -⟩ := F1.vars
  have hl := F1.M.hlt
  have hA : asgK finTA' ≤ 30 := by decide
  have hc1 := evalB_condLt (B := W + 1) (σ := τ1) (ev_add (ev_var hii (by have := hl.vars "ii"; omega))
    (evalB_lit (n := 1) (by omega)) (by have := hl.vars "lvL"; rw [F1.hlvL] at this; omega))
    (ev_var F1.hlvL (by rw [← F1.hlvL]; exact hl.vars _))
  have hsz : ∀ e : Expr, e = .add (.var "ii") (.lit 1) ∨ e = .var "lvL" → e.size ≤ 3 := by
    rintro e (rfl | rfl) <;> simp [Expr.size]
  unfold FinUpOut
  rw [next_fin G P Q s k₀ q₀ hm]
  by_cases h1 : i + 1 < (lvR G P Q s k₀ q₀ d).length
  · simp only [if_pos h1, finNew, kBr]
    obtain ⟨τ', K, r, hK, TI, n1, n2, n3, n4, n5, n6, n7, n8⟩ := fin_a G P Q s k₀ q₀ hR hkq h1 F1
    refine ⟨τ', _, Run.seq rA (Run.ite_true (by rw [hc1]; simp [h1]) r), ?_,
      fun _ => ⟨TI, n1, n2, n3, n4, n5, n6, n7⟩, fun _ => n8⟩
    simp only [Cond.size, Expr.size]; omega
  have hi' : i + 1 = (lvR G P Q s k₀ q₀ d).length := by omega
  have hc1' : (Cond.lt (.add (.var "ii") (.lit 1)) (.var "lvL")).evalB (W + 1) τ1 = some false := by
    rw [hc1]; simp [h1]
  have hsum : (nxW G P Q s k₀ q₀ d i).length + (exE G P Q s k₀ q₀ d i).length =
      (lvR G P Q s k₀ q₀ (d + 1)).length := by
    rw [← length_exE, hi', nxW_full, length_lvW]
  have hc2 := evalB_condEq (B := W + 1) (σ := τ1)
    (ev_add (ev_var F1.hlvN (by rw [← F1.hlvN]; exact hl.vars _)) (ev_var F1.hne (by rw [← F1.hne]; exact hl.vars _))
      (by
        obtain ⟨-, -, -, -, -, hLV, hroom⟩ := F1.lib hR
        have hnx : (nxW G P Q s k₀ q₀ d i).length ≤ (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length := by
          rw [LV_dn']; simp
        omega))
    (evalB_lit (n := 0) (by omega))
  by_cases h2 : (lvR G P Q s k₀ q₀ (d + 1)).length = 0
  · simp only [if_neg h1, if_pos h2, finNew, kBr]
    obtain ⟨τ', K, r, hK, hO, hB⟩ := fin_d G P Q s k₀ q₀ hAt hAV hk hkq hd hi' h2 F1
    refine ⟨τ', _, Run.seq rA (Run.ite_false hc1' (Run.ite_true (by rw [hc2]; simp only [Option.some.injEq, beq_iff_eq]; omega) r)), ?_, hO, hB⟩
    simp only [Cond.size, Expr.size]; omega
  have hc2' : (Cond.eq (.add (.var "lvN") (.var "ne")) (.lit 0)).evalB (W + 1) τ1 = some false := by
    rw [hc2]; simp only [Option.some.injEq, beq_eq_false_iff_ne, ne_eq]; omega
  have hc3 := evalB_condLt (B := W + 1) (σ := τ1) (ev_add (ev_var hdd (by have := hl.vars "dd"; omega))
    (evalB_lit (n := 1) (by omega)) (by have := hl.vars "gq"; omega))
    (ev_var hgq (by have := hl.vars "gq"; omega))
  by_cases h3 : d + 1 < q₀
  · simp only [if_neg h1, if_neg h2, if_pos h3, finNew, kBr]
    obtain ⟨τ', K, r, hK, TI, n1, n2, n3, n4, n5, n6, n7, n8⟩ := fin_b G P Q s k₀ q₀ hR hkq hi' (by omega) F1
    refine ⟨τ', _, Run.seq rA (Run.ite_false hc1' (Run.ite_false hc2' (Run.ite_true (by rw [hc3]; simp [h3]) r))),
      ?_, fun _ => ⟨TI, n1, n2, n3, n4, n5, n6, n7⟩, fun _ => n8⟩
    simp only [Cond.size, Expr.size]; omega
  · simp only [if_neg h1, if_neg h2, if_neg h3, finNew, kBr]
    obtain ⟨τ', K, r, hK, hO, hB⟩ := fin_c G P Q s k₀ q₀ hAt hAV hk hkq (by omega) hi' (by omega) F1
    refine ⟨τ', _, Run.seq rA (Run.ite_false hc1' (Run.ite_false hc2' (Run.ite_false (by rw [hc3]; simp [h3])
      r))), ?_, hO, hB⟩
    simp only [Cond.size, Expr.size]; omega

end Lax185574Proofs.ResolveRam.Glue
