import Lax185574Proofs.ResolveRam.Glue.CUpB
import Lax185574Proofs.ResolveRam.Glue.CFinL
import Lax185574Proofs.ResolveRam.Glue.CFinFt
import Lax185574Proofs.ResolveRam.Glue.CShift

/-!
The dispatcher of a later round of the glue program of lem:resolve-lift.

The dispatcher `disp atC bR1` reads the phase, the call number, the
level and the item of the current position from the head and runs the
case of the position: `bR1` after the scatter types, `bShift`, `bFt`,
`bComp` and `bLast` on the way down, `bUpA` and `bUpB` on the way up,
and the end of the phase (`Nph := 3`) after the last call.
`disp_call`: at every position that is followed by a call, the
dispatcher does what a case must do (`BodyCall`), with a plan that gives
the state of the next position. `disp_last`: at the last position, it
only sets the phase to `3`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax185574.ResolveLift
open Lax3.DistFO (rhoPlus)

/-! ### Cases behind a test, with the facts of the start -/

theorem bc_ite_t {body c2 : Com} {b : Cond} {W R X Nt Nw KB k : ℕ} {sc wx bb w nsc : List ℕ}
    {ws L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hb : ∀ τ, PreR W R sc ws wx bb τ → τ.vars "ovf" = 0 → kq0 < W → b.evalB (W + 1) τ = some true)
    (h : BodyCall body W R X sc ws wx bb L ps k w Nt Nw nsc KB) :
    BodyCall (.ite b body c2) W R X sc ws wx bb L ps k w Nt Nw nsc (1 + b.size + KB) := by
  intro τ P0 hov hkq
  obtain ⟨τ', kb, r, hkb, h1, h2⟩ := h τ P0 hov hkq
  exact ⟨τ', _, Run.ite_true (hb τ P0 hov hkq) r, by omega, h1, h2⟩

theorem bc_ite_f {body c1 : Com} {b : Cond} {W R X Nt Nw KB k : ℕ} {sc wx bb w nsc : List ℕ}
    {ws L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hb : ∀ τ, PreR W R sc ws wx bb τ → τ.vars "ovf" = 0 → kq0 < W → b.evalB (W + 1) τ = some false)
    (h : BodyCall body W R X sc ws wx bb L ps k w Nt Nw nsc KB) :
    BodyCall (.ite b c1 body) W R X sc ws wx bb L ps k w Nt Nw nsc (1 + b.size + KB) := by
  intro τ P0 hov hkq
  obtain ⟨τ', kb, r, hkb, h1, h2⟩ := h τ P0 hov hkq
  exact ⟨τ', _, Run.ite_false (hb τ P0 hov hkq) r, by omega, h1, h2⟩

theorem kq0_ge : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)

/-- A scalar of the head at the start of a round. -/
theorem ev_sc {W R : ℕ} {sc wx b : List ℕ} {ws : List (List ℕ)} {τ : Env} (P0 : PreR W R sc ws wx b τ)
    (j : ℕ) (h : j < 17) :
    (Expr.var (scR[j]'(by simp [scR]; omega))).evalB (W + 1) τ = some (sc.getD j 0) :=
  ev_var (P0.hsc j h) (by rw [← P0.hsc j h]; exact P0.hlt.vars _)

theorem tst_eq {W R : ℕ} {sc wx b : List ℕ} {ws : List (List ℕ)} {τ : Env} (P0 : PreR W R sc ws wx b τ)
    (j : ℕ) (h : j < 17) (v : ℕ) (hv : v < W + 1) :
    (Cond.eq (.var (scR[j]'(by simp [scR]; omega))) (.lit v)).evalB (W + 1) τ =
      some (decide (sc.getD j 0 = v)) :=
  ev_condEq (ev_sc P0 j h) (evalB_lit hv)

theorem ev_scs {W R : ℕ} {sc wx b : List ℕ} {ws : List (List ℕ)} {τ : Env} (P0 : PreR W R sc ws wx b τ)
    (j : ℕ) (h : j < 17) (v : ℕ) (hv : v < W + 1) :
    (Expr.sub (.var (scR[j]'(by simp [scR]; omega))) (.lit v)).evalB (W + 1) τ = some (sc.getD j 0 - v) :=
  ev_sub (ev_sc P0 j h) (evalB_lit hv) (by
    have := P0.hlt.vars (scR[j]'(by simp [scR]; omega)); rw [P0.hsc j h] at this; omega)

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- What the dispatcher must do at a position that is followed by a call. -/
def DCase (body : Com) (c : Cur) (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (KB : ℕ) : Prop :=
  ∀ W, BodyCall body W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ c)
    (swAt G P Q s k₀ q₀ c).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ c))
    (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)) L ps (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)))
    (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)))
    (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c))
    (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)) KB

/-- The facts of a case besides the run: the plan, the old state in the
library and the length of the plan. -/
def DPlan (c : Cur) (L : List (List ℕ)) (ps : List (ℕ × ℕ)) : Prop :=
  planW L ps = (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)).ws ∧ (swAt G P Q s k₀ q₀ c).ws.Sublist L ∧
    ps.length ≤ 12

theorem scW_get (c : Cur) (j : ℕ) (hj : 9 ≤ j) (hj' : j < 13) :
    (scW G P Q s k₀ q₀ c).getD j 0 = (curW c).getD (j - 9) 0 := by
  rcases (show j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 by omega) with rfl | rfl | rfl | rfl <;>
    cases c <;> simp [scW, curW]

theorem scW_get8 (c : Cur) : (scW G P Q s k₀ q₀ c).getD 8 0 = q₀ := by
  cases c <;> simp [scW, curW]

theorem scW_get14 (c : Cur) : (scW G P Q s k₀ q₀ c).getD 14 0 = (swAt G P Q s k₀ q₀ c).FA.length := by
  cases c <;> simp [scW, curW]

/-! ### The tests of the dispatcher at a position -/

section tests

variable {G P Q s k₀ q₀}
variable {W R : ℕ} {c : Cur} {wx b : List ℕ} {ws : List (List ℕ)} {τ : Env}

theorem t_ph (P0 : PreR W R (scW G P Q s k₀ q₀ c) ws wx b τ) (hkq : kq0 < W) (v : ℕ) (hv : v ≤ 3) :
    (Cond.eq (.var "ph") (.lit v)).evalB (W + 1) τ = some (decide ((curW c).getD 0 0 = v)) := by
  have h := tst_eq P0 9 (by omega) v (by have := kq0_ge; omega)
  rw [scW_get G P Q s k₀ q₀ c 9 (by omega) (by omega)] at h
  exact h

theorem t_dd (P0 : PreR W R (scW G P Q s k₀ q₀ c) ws wx b τ) (hkq : kq0 < W) :
    (Cond.eq (.var "dd") (.lit 0)).evalB (W + 1) τ = some (decide ((curW c).getD 1 0 = 0)) := by
  have h := tst_eq P0 10 (by omega) 0 (by omega)
  rw [scW_get G P Q s k₀ q₀ c 10 (by omega) (by omega)] at h
  exact h

theorem t_mm (P0 : PreR W R (scW G P Q s k₀ q₀ c) ws wx b τ) (hkq : kq0 < W) (v : ℕ) (hv : v ≤ 3) :
    (Cond.eq (.var "mm") (.lit v)).evalB (W + 1) τ = some (decide ((curW c).getD 3 0 = v)) := by
  have h := tst_eq P0 12 (by omega) v (by have := kq0_ge; omega)
  rw [scW_get G P Q s k₀ q₀ c 12 (by omega) (by omega)] at h
  exact h

theorem t_dq (P0 : PreR W R (scW G P Q s k₀ q₀ c) ws wx b τ) :
    (Cond.lt (.var "dd") (.var "gq")).evalB (W + 1) τ = some (decide ((curW c).getD 1 0 < q₀)) := by
  have h := evalB_condLt (ev_sc P0 10 (by omega)) (ev_sc P0 8 (by omega))
  rw [scW_get G P Q s k₀ q₀ c 10 (by omega) (by omega), scW_get8] at h
  exact h

theorem t_mf (P0 : PreR W R (scW G P Q s k₀ q₀ c) ws wx b τ) (hkq : kq0 < W) :
    (Cond.lt (.sub (.var "mm") (.lit 1)) (.var "nFA")).evalB (W + 1) τ =
      some (decide ((curW c).getD 3 0 - 1 < (swAt G P Q s k₀ q₀ c).FA.length)) := by
  have h := evalB_condLt (ev_scs P0 12 (by omega) 1 (by omega)) (ev_sc P0 14 (by omega))
  rw [scW_get G P Q s k₀ q₀ c 12 (by omega) (by omega), scW_get14] at h
  exact h

theorem t_ii {d i m : ℕ} (P0 : PreR W R (scW G P Q s k₀ q₀ (.up d i m)) (swAt G P Q s k₀ q₀ (.up d i m)).ws wx b τ)
    (hkq : kq0 < W) :
    (Cond.eq (.var "ii") (.sub (eLL (.lit 0)) (.lit 1))).evalB (W + 1) τ =
      some (decide (i = (lvR G P Q s k₀ q₀ 0).length - 1)) := by
  have h4 := length_SW_ws (swAt G P Q s k₀ q₀ (.up d i m))
  have h3 : (swAt G P Q s k₀ q₀ (.up d i m)).ws[3] = llW G P Q s k₀ q₀ q₀ := by
    rw [← LL_up G P Q s k₀ q₀ d i m]; simp [SW.ws_eq]
  have hl3 : 0 < (swAt G P Q s k₀ q₀ (.up d i m)).ws[3].length := by rw [h3, length_llW]; omega
  have hL := ev_LLe (W := W) P0.hlib.at_ (by omega) (evalB_lit (n := 0) (by omega)) hl3 P0.hlt P0.harr
    (by have := kq0_ge; omega)
  have hv : (swAt G P Q s k₀ q₀ (.up d i m)).ws[3][0] = (lvR G P Q s k₀ q₀ 0).length := by
    simp only [h3]; exact llW_get G P Q s k₀ q₀ (Nat.zero_le _)
  rw [hv] at hL
  have hi := ev_sc P0 11 (by omega)
  rw [scW_get G P Q s k₀ q₀ _ 11 (by omega) (by omega)] at hi
  have hs := ev_sub (B := W + 1) hL (evalB_lit (n := 1) (by omega)) (by
    have := P0.hlt.arrs "a" _ (List.mem_of_getElem? ((P0.hlib.at_).a 3 (by omega) 0 hl3)); rw [hv] at this
    omega)
  exact ev_condEq hi hs

end tests

/-! ### The cases -/

theorem next_dn1 {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hF : 0 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length) :
    next G P Q s k₀ q₀ (.dn d i 1) = .dn d i 2 := by
  have := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
  simp only [next]; rw [if_pos (by omega)]

theorem next_up0 {d i : ℕ} (hd : d < q₀) : next G P Q s k₀ q₀ (.up d i 0) = .up d i 1 := by
  have h : 0 + 1 < nUp q₀ d := by simp [nUp, hd]
  simp only [next]; rw [if_pos h]

theorem realY_compose (σ ν : TypeTree) : realY G k₀ q₀ (.compose σ ν) = toWord (coOf G σ ν) := rfl

set_option maxHeartbeats 1600000 in
theorem disp_dn0 {atC bR1 : Com} {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    DCase G P Q s k₀ q₀ (disp atC bR1) (.dn d i 0)
      ((swAt G P Q s k₀ q₀ (.dn d i 0)).ws ++ [[], toWord (shOf G (itm G P Q s k₀ q₀ d i).2)])
      (psRep1 (swAt G P Q s k₀ q₀ (.dn d i 0)).ws.length)
      (kShift (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 0))) d + 100) := by
  intro W
  rw [next_dn0 G P Q s k₀ q₀ hi]
  refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
    (bc_ite_t (fun τ P0 _ hkq => by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
      (bc_ite_t (fun τ P0 _ hkq => by rw [t_mm P0 hkq 0 (by omega)]; simp [curW])
        (bShift_ok G P Q s k₀ q₀ hi (by omega))))) ?_
  simp only [Cond.size, Expr.size]; omega

theorem plan_dn0 {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    DPlan G P Q s k₀ q₀ (.dn d i 0)
      ((swAt G P Q s k₀ q₀ (.dn d i 0)).ws ++ [[], toWord (shOf G (itm G P Q s k₀ q₀ d i).2)])
      (psRep1 (swAt G P Q s k₀ q₀ (.dn d i 0)).ws.length) := by
  refine ⟨?_, List.sublist_append_left _ _, by simp [psRep1]⟩
  rw [next_dn0 G P Q s k₀ q₀ hi]; exact case_shift (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀)

set_option maxHeartbeats 1600000 in
theorem disp_dn1 {atC bR1 : Com} {d i : ℕ} (hk : 1 ≤ k₀) (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hF : 0 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length) :
    DCase G P Q s k₀ q₀ (disp atC bR1) (.dn d i 1)
      ((swAt G P Q s k₀ q₀ (.dn d i 1)).ws ++
        ([] :: (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord))
      (psFt (swAt G P Q s k₀ q₀ (.dn d i 1)).ws.length (swAt G P Q s k₀ q₀ (.dn d i 1)).SG.length
        (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length (swAt G P Q s k₀ q₀ (.dn d i 1)).LV.length)
      (kFt (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1))) (swAt G P Q s k₀ q₀ (.dn d i 1)).ws
        ((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord) (kFA G P Q s k₀ q₀ d i) 0 + 100) := by
  intro W
  rw [next_dn1 G P Q s k₀ q₀ hi hF]
  refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
    (bc_ite_t (fun τ P0 _ hkq => by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
      (bc_ite_f (fun τ P0 _ hkq => by rw [t_mm P0 hkq 0 (by omega)]; simp [curW])
        (bc_ite_t (fun τ P0 _ hkq => by rw [t_mm P0 hkq 1 (by omega)]; simp [curW])
          (bFt_ok G P Q s k₀ q₀ (fE atC) hk hd hi hF))))) ?_
  simp only [Cond.size, Expr.size]; omega

theorem plan_dn1 {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hF : 0 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length) :
    DPlan G P Q s k₀ q₀ (.dn d i 1)
      ((swAt G P Q s k₀ q₀ (.dn d i 1)).ws ++
        ([] :: (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord))
      (psFt (swAt G P Q s k₀ q₀ (.dn d i 1)).ws.length (swAt G P Q s k₀ q₀ (.dn d i 1)).SG.length
        (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length
        (swAt G P Q s k₀ q₀ (.dn d i 1)).LV.length) := by
  refine ⟨?_, List.sublist_append_left _ _, by simp [psFt]⟩
  rw [next_dn1 G P Q s k₀ q₀ hi hF]; exact case_ft G P Q s k₀ q₀

set_option maxHeartbeats 1600000 in
theorem disp_dn1e {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {bR1 : Com} {d i : ℕ} (hk : 1 ≤ k₀) (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hF0 : (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length = 0) :
    DCase G P Q s k₀ q₀ (disp atC bR1) (.dn d i 1)
      (finL1 G P Q s k₀ q₀ d i 1 ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1)))
      (finPs G P Q s k₀ q₀ d i 1)
      (kFt (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1))) (swAt G P Q s k₀ q₀ (.dn d i 1)).ws
        ((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord) (kFA G P Q s k₀ q₀ d i)
        (kFE G P Q s k₀ q₀ d i 1 (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1))) + 104 +
          kBr G P Q s k₀ q₀ hAt hAV d i 1 (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1)))
            (next G P Q s k₀ q₀ (.dn d i 1))) + 100) := by
  intro W
  refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
    (bc_ite_t (fun τ P0 _ hkq => by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
      (bc_ite_f (fun τ P0 _ hkq => by rw [t_mm P0 hkq 0 (by omega)]; simp [curW])
        (bc_ite_t (fun τ P0 _ hkq => by rw [t_mm P0 hkq 1 (by omega)]; simp [curW])
          (bFtE_ok G P Q s k₀ q₀ hAt hAV hk hd hi hF0))))) ?_
  simp only [Cond.size, Expr.size]; omega

set_option maxHeartbeats 1600000 in
theorem disp_comp {atC bR1 : Com} {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm2 : 2 ≤ m)
    (hmn : m + 1 < nDn G P Q s k₀ q₀ d i) :
    DCase G P Q s k₀ q₀ (disp atC bR1) (.dn d i m)
      ((swAt G P Q s k₀ q₀ (.dn d i m)).ws ++ [[], realY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))])
      (psComp (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length
        (4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length + (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length +
          (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length) (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length)
      (kComp (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))) + 100) := by
  intro W
  have hnd := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
  have hFA : (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length =
      (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length := by
    simp [swAt, show 2 ≤ m from hm2]
  rw [next_comp G P Q s k₀ q₀ hmn]
  refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
    (bc_ite_t (fun τ P0 _ hkq => by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
      (bc_ite_f (fun τ P0 _ hkq => by rw [t_mm P0 hkq 0 (by omega)]; simp [curW]; omega)
        (bc_ite_f (fun τ P0 _ hkq => by rw [t_mm P0 hkq 1 (by omega)]; simp [curW]; omega)
          (bc_ite_t (fun τ P0 _ hkq => by rw [t_mf P0 hkq, hFA]; simp [curW]; omega)
            (bComp_ok G P Q s k₀ q₀ hi hm2 hmn (by omega))))))) ?_
  simp only [Cond.size, Expr.size]; omega

theorem plan_comp {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm2 : 2 ≤ m)
    (hmn : m + 1 < nDn G P Q s k₀ q₀ d i) :
    DPlan G P Q s k₀ q₀ (.dn d i m)
      ((swAt G P Q s k₀ q₀ (.dn d i m)).ws ++ [[], realY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))])
      (psComp (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length
        (4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length + (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length +
          (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length) (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length) := by
  refine ⟨?_, List.sublist_append_left _ _, by simp [psComp]⟩
  obtain ⟨hr, hc⟩ := callOf_dn_comp G P Q s k₀ q₀ hi hm2 (by omega)
  rw [next_comp G P Q s k₀ q₀ hmn, hc, realY_compose]
  exact case_comp G P Q s k₀ q₀ hm2 hr

set_option maxHeartbeats 1600000 in
theorem disp_last {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {bR1 : Com} {d i m : ℕ} (hk : 1 ≤ k₀) (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm2 : 2 ≤ m)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i) :
    DCase G P Q s k₀ q₀ (disp atC bR1) (.dn d i m)
      (finL1 G P Q s k₀ q₀ d i m ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (finPs G P Q s k₀ q₀ d i m)
      (kLast (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))) (swAt G P Q s k₀ q₀ (.dn d i m)).ws +
        (kFE G P Q s k₀ q₀ d i m (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))) + 104 +
          kBr G P Q s k₀ q₀ hAt hAV d i m (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m)))
            (next G P Q s k₀ q₀ (.dn d i m))) + 100) := by
  intro W
  have hnd := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
  have hFA : (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length =
      (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length := by
    simp [swAt, show 2 ≤ m from hm2]
  refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
    (bc_ite_t (fun τ P0 _ hkq => by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
      (bc_ite_f (fun τ P0 _ hkq => by rw [t_mm P0 hkq 0 (by omega)]; simp [curW]; omega)
        (bc_ite_f (fun τ P0 _ hkq => by rw [t_mm P0 hkq 1 (by omega)]; simp [curW]; omega)
          (bc_ite_f (fun τ P0 _ hkq => by rw [t_mf P0 hkq, hFA]; simp [curW]; omega)
            (bLast_ok G P Q s k₀ q₀ hAt hAV hk hd hi hm2 hm)))))) ?_
  simp only [Cond.size, Expr.size]; omega

set_option maxHeartbeats 1600000 in
theorem disp_upA {atC bR1 : Com} {d i : ℕ} (hk : 1 ≤ k₀) (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    DCase G P Q s k₀ q₀ (disp atC bR1) (.up d i 0)
      ((swAt G P Q s k₀ q₀ (.up d i 0)).ws ++
        [[], canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2), realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 1))])
      (psRep2 (swAt G P Q s k₀ q₀ (.up d i 0)).ws.length)
      (kUpA (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 0))) d +
        kKdT ((swAt G P Q s k₀ q₀ (.up d i 0)).ws ++ [[], canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2)])
          (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 0))) (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 1)))
          (cKd * ((lvR G P Q s k₀ q₀ (d + 1)).length + total (lvW G P Q s k₀ q₀ (d + 1)) +
            total (outW G P Q s k₀ q₀ (d + 1)) + 1) * ((itemW (itm G P Q s k₀ q₀ d i)).length + 1) ^ aKd) + 100) := by
  intro W
  rw [next_up0 G P Q s k₀ q₀ hd]
  refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
    (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
      (bc_ite_t (fun τ P0 _ hkq => by rw [t_mm P0 hkq 0 (by omega)]; simp [curW])
        (bc_ite_t (fun τ P0 _ hkq => by rw [t_dq P0]; simp [curW, hd])
          (bUpA_ok G P Q s k₀ q₀ hk hd hi))))) ?_
  simp only [Cond.size, Expr.size]; omega

theorem plan_upA {d i : ℕ} (hd : d < q₀) :
    DPlan G P Q s k₀ q₀ (.up d i 0)
      ((swAt G P Q s k₀ q₀ (.up d i 0)).ws ++
        [[], canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2), realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i 1))])
      (psRep2 (swAt G P Q s k₀ q₀ (.up d i 0)).ws.length) := by
  refine ⟨?_, List.sublist_append_left _ _, by simp [psRep2]⟩
  rw [next_up0 G P Q s k₀ q₀ hd]; exact case_upA G P Q s k₀ q₀

/-- The end of an item on the way up that is not the last item. -/
theorem dUpE_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {d i m W : ℕ} (hk : 1 ≤ k₀) (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m + 1 = nUp q₀ d)
    (hnf : next G P Q s k₀ q₀ (.up d i m) ≠ .fin) {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {KB : ℕ}
    (h : BodyCall (bUpB atC) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.up d i m))
      (swAt G P Q s k₀ q₀ (.up d i m)).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.up d i m)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m))) L ps
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))) KB) :
    BodyCall (dUpE atC) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.up d i m))
      (swAt G P Q s k₀ q₀ (.up d i m)).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.up d i m)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m))) L ps
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))) (KB + 40) := by
  have hn : ¬ (m + 1 < nUp q₀ d) := by omega
  by_cases h0 : d = 0
  · subst h0
    have hi1 : i + 1 < (lvR G P Q s k₀ q₀ 0).length := by
      by_contra hc
      apply hnf
      simp only [next, if_neg hn, if_neg hc, if_true]
    refine bodyCall_mono (bc_ite_t (fun τ P0 _ hkq => by rw [t_dd P0 hkq]; simp [curW])
      (bc_ite_f (fun τ P0 _ hkq => by rw [t_ii P0 hkq]; simp; omega) h)) ?_
    simp only [Cond.size, Expr.size, eLL]; omega
  · refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_dd P0 hkq]; simp [curW, h0]) h) ?_
    simp only [Cond.size, Expr.size]; omega

set_option maxHeartbeats 1600000 in
theorem disp_upB {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {bR1 : Com} {d i m : ℕ} (hk : 1 ≤ k₀) (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m + 1 = nUp q₀ d) (hnf : next G P Q s k₀ q₀ (.up d i m) ≠ .fin) :
    DCase G P Q s k₀ q₀ (disp atC bR1) (.up d i m)
      ((swAt G P Q s k₀ q₀ (.up d i m)).ws ++
        [[], (outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega),
          realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)))])
      (psUp (swAt G P Q s k₀ q₀ (.up d i m)) (swAt G P Q s k₀ q₀ (.up d i m)).ws.length
        ((swAt G P Q s k₀ q₀ (.up d i m)).ws.length + 1) (pUp G P Q s k₀ q₀ d i))
      (kUpB (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m))) (swAt G P Q s k₀ q₀ (.up d i m)).ws d +
        kAtT ((swAt G P Q s k₀ q₀ (.up d i m)).ws ++ [[], (outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega)])
          (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m)))
          (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))))
          (cAt hAt hAV * ((ctW G P Q).length + 1) *
            ((itemW (itm G P Q s k₀ q₀ (nxD G P Q s k₀ q₀ d i) (nxI G P Q s k₀ q₀ d i))).length +
              (itm G P Q s k₀ q₀ (nxD G P Q s k₀ q₀ d i) (nxI G P Q s k₀ q₀ d i)).2.ℓ +
              rhoPlus (k₀ + 1) q₀ + 1) ^ aAt hAt hAV) + 200) := by
  intro W
  have hB := bUpB_ok G P Q s k₀ q₀ hAt hAV hk hd hi hm hnf (W := W)
  have hE := dUpE_ok G P Q s k₀ q₀ hAt hAV hk hd hi hm hnf hB
  by_cases hm0 : m = 0
  · subst hm0
    have hdq : ¬ d < q₀ := by intro h; simp [nUp, h] at hm
    refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
      (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
        (bc_ite_t (fun τ P0 _ hkq => by rw [t_mm P0 hkq 0 (by omega)]; simp [curW])
          (bc_ite_f (fun τ P0 _ hkq => by rw [t_dq P0]; simp [curW, hdq]) hE)))) ?_
    simp only [Cond.size, Expr.size]; omega
  · refine bodyCall_mono (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
      (bc_ite_f (fun τ P0 _ hkq => by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
        (bc_ite_f (fun τ P0 _ hkq => by rw [t_mm P0 hkq 0 (by omega)]; simp [curW, hm0]) hE))) ?_
    simp only [Cond.size, Expr.size]; omega

theorem plan_upB {d i m : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m + 1 = nUp q₀ d)
    (hnf : next G P Q s k₀ q₀ (.up d i m) ≠ .fin) :
    DPlan G P Q s k₀ q₀ (.up d i m)
      ((swAt G P Q s k₀ q₀ (.up d i m)).ws ++
        [[], (outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega),
          realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)))])
      (psUp (swAt G P Q s k₀ q₀ (.up d i m)) (swAt G P Q s k₀ q₀ (.up d i m)).ws.length
        ((swAt G P Q s k₀ q₀ (.up d i m)).ws.length + 1) (pUp G P Q s k₀ q₀ d i)) :=
  ⟨case_upB G P Q s k₀ q₀ hd hi hm hnf _, List.sublist_append_left _ _, by simp [psUp]⟩


set_option maxHeartbeats 1600000 in
theorem disp_stp {atC bR1 : Com} {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {KB : ℕ}
    (h : DCase G P Q s k₀ q₀ bR1 .stp L ps KB) :
    DCase G P Q s k₀ q₀ (disp atC bR1) .stp L ps (KB + 10) := by
  intro W
  refine bodyCall_mono (bc_ite_t (fun τ P0 _ hkq => by rw [t_ph P0 hkq 0 (by omega)]; simp [curW]) (h W)) ?_
  simp only [Cond.size, Expr.size]; omega

/-- **The dispatcher at the last position.** It only sets the phase to `3`. -/
theorem disp_end {atC bR1 : Com} {i m : ℕ} (hi : i + 1 = (lvR G P Q s k₀ q₀ 0).length) (hm : m + 1 = nUp q₀ 0)
    {W R : ℕ} {wx b : List ℕ} {τ0 : Env}
    (P0 : PreR W R (scW G P Q s k₀ q₀ (.up 0 i m)) (swAt G P Q s k₀ q₀ (.up 0 i m)).ws wx b τ0)
    (hkq : kq0 < W) :
    ∃ τ K, Run (W + 1) (disp atC bR1) τ0 τ K ∧ K ≤ 100 ∧ τ.vars "Nph" = 3 ∧
      (∀ y, y ≠ "Nph" → τ.vars y = τ0.vars y) ∧ τ.arrs = τ0.arrs ∧ τ.out = τ0.out ∧ τ.inp = τ0.inp := by
  obtain ⟨τ, r, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ0) (l := [("Nph", .lit 3)])
    (f := fun _ => 3) (by intro p hp; simp at hp; subst hp; exact evalB_lit (by have := kq0_ge; omega))
    (by decide)
  have hA : asgK [("Nph", Expr.lit 3)] = 3 := by decide
  have hE : Run (W + 1) (dUpE atC) τ0 τ (1 + (Cond.eq (.var "dd") (.lit 0)).size +
      (1 + (Cond.eq (.var "ii") (.sub (eLL (.lit 0)) (.lit 1))).size + 3)) := by
    refine Run.ite_true (by rw [t_dd P0 hkq]; simp [curW]) (Run.ite_true ?_ (hA ▸ r))
    rw [t_ii P0 hkq]; simp; omega
  have hdq : (m = 0 ∧ 0 < q₀) ∨ (m = 0 ∧ q₀ = 0) ∨ m ≠ 0 := by omega
  have hrun : ∃ K, Run (W + 1) (disp atC bR1) τ0 τ K ∧ K ≤ 100 := by
    rcases hdq with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | hm0
    · simp [nUp, hq] at hm
    · refine ⟨_, Run.ite_false (by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
        (Run.ite_false (by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
          (Run.ite_true (by rw [t_mm P0 hkq 0 (by omega)]; simp [curW])
            (Run.ite_false (by rw [t_dq P0]; simp [curW, hq]) hE))), ?_⟩
      simp only [Cond.size, Expr.size, eLL]; omega
    · refine ⟨_, Run.ite_false (by rw [t_ph P0 hkq 0 (by omega)]; simp [curW])
        (Run.ite_false (by rw [t_ph P0 hkq 1 (by omega)]; simp [curW])
          (Run.ite_false (by rw [t_mm P0 hkq 0 (by omega)]; simp [curW, hm0]) hE)), ?_⟩
      simp only [Cond.size, Expr.size, eLL]; omega
  obtain ⟨K, hr, hK⟩ := hrun
  exact ⟨τ, K, hr, hK, s1 "Nph" (by simp), fun y hy => g1 y (by simp [hy]), a1, o1, i1⟩

/-! ### The plan after an item on the way down -/

theorem sw_next_fin {d i m : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i) :
    ∃ LL', swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)) =
      swFin (swAt G P Q s k₀ q₀ (.dn d i m)) LL' (exE G P Q s k₀ q₀ d i) := by
  rw [next_fin G P Q s k₀ q₀ hm]
  split_ifs with h1 h2 h3
  · exact ⟨_, sw_fin_a G P Q s k₀ q₀⟩
  · exact ⟨_, sw_fin_d G P Q s k₀ q₀ hd (by omega) h2⟩
  · exact ⟨_, sw_fin_b G P Q s k₀ q₀ (by omega)⟩
  · exact ⟨_, sw_fin_c G P Q s k₀ q₀ (by omega) (by omega)⟩

theorem finNew_head (c : Cur) : ∃ M, finNew G P Q s k₀ q₀ c = (swAt G P Q s k₀ q₀ c).LL :: M := by
  cases c <;> exact ⟨_, rfl⟩

theorem plan_fin {d i m : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i) :
    DPlan G P Q s k₀ q₀ (.dn d i m)
      (finL1 G P Q s k₀ q₀ d i m ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (finPs G P Q s k₀ q₀ d i m) := by
  obtain ⟨LL', hsw⟩ := sw_next_fin G P Q s k₀ q₀ hd hi hm
  obtain ⟨M, hM⟩ := finNew_head G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))
  set w := swAt G P Q s k₀ q₀ (.dn d i m)
  set C := coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2
  set E := exE G P Q s k₀ q₀ d i
  have hL : finL1 G P Q s k₀ q₀ d i m ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)) =
      w.ws ++ (([] :: C) ++ (E ++ ((swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))).LL :: M))) := by
    rw [hM]; simp [finL1, w, C, E, List.append_assoc]
  have hX0 : (([] :: C) ++ (E ++ ((swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))).LL :: M)))[0]? = some [] := by simp
  have hXl : (([] :: C) ++ (E ++ ((swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))).LL :: M)))[1 + C.length + E.length]? = some (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))).LL := by
    rw [List.getElem?_append_right (by simp; omega)]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_cons, show 1 + C.length + E.length - (C.length + 1) - E.length = 0 by omega,
      List.getElem?_cons_zero]
  have hE : rng (([] :: C) ++ (E ++ ((swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))).LL :: M))) (1 + C.length) E.length = E := by
    unfold rng
    rw [List.drop_append_of_le_length (by simp; omega)]
    simp [show 1 + C.length = C.length + 1 by omega]
  have hP := planW_fin w _ E (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))).LL hX0 hXl hE
  have hps : finPs G P Q s k₀ q₀ d i m =
      psFin w w.ws.length (w.ws.length + (1 + C.length + E.length)) (w.ws.length + (1 + C.length)) E.length := by
    simp only [finPs, finL1, List.length_append, List.length_cons, w, C, E]
    congr 1 <;> omega
  refine ⟨?_, ?_, by simp [finPs, psFin]⟩
  · rw [hL, hps, hP, hsw]; rfl
  · simp only [finL1, List.append_assoc]; exact (List.sublist_append_left _ _)

end Lax185574Proofs.ResolveRam.Glue
