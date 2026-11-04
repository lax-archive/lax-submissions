import Lax185574Proofs.StpRam.Tail
import Lax185574Proofs.StpRam.FinalRead

/-!
The first round of the glue program of lem:compute-stp.

The state of the glue program after `j` calls is
`0, n, k, q, j, gl`, the word of the list `F` of the family trees and the
word of the list `A` of the first `j` answers (`stState`). Here `gl` is
the length of the word of the graph plus two plus the length of the word
of the distance matrix, the length of the window of the input that the
final round reads. The first round reads the graph, `k` and `q`, skips
the distance matrix and reads the family. If `q = 0` it outputs `0, 0`, the empty
scatter type. Otherwise it writes tag `1`, the state after no calls and
the first family tree as the first query.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs

/-- The state of the glue program after `j` calls. -/
def stState (n k q j gl : ℕ) (F A : List (List ℕ)) : List ℕ :=
  [0, n, k, q, j, gl] ++ toWord F ++ toWord A

theorem length_stState (n k q j gl : ℕ) (F A : List (List ℕ)) :
    (stState n k q j gl F A).length = 6 + (toWord F).length + (toWord A).length := by
  simp [stState]; omega

/-- The first round after the tag and the length of the input, when
`q ≥ 1`. -/
def r0b : Com :=
  .seq (.assign "xp" (.lit 0)) (.seq (push (.lit 0)) (.seq (push (.var "cn")) (.seq (push (.var "kk"))
  (.seq (push (.var "qq")) (.seq (push (.lit 0)) (.seq (push (.lit 0)) (.seq cpFam
  (.seq (.assign "pa" (.var "xp")) (.seq (push (.lit 0))
  (.seq (.store "x" (.lit 5) (.sub (.add (.add (.var "sl") (.var "cn")) (.lit 6)) (.var "pa")))
  (.seq (.assign "otg" (.lit 1)) (.seq (.assign "owin" (.lit 0)) (.seq (.assign "ws0" (.lit 7))
  (.seq (.assign "wc" (.lit 0)) tail))))))))))))))

/-- Skip the word of an `n × n` matrix: read `n` and skip `n (n + 1)`
entries. -/
def skipDm : Com :=
  .seq (.read "dz") (.seq (.assign "dz" (.mul (.var "dz") (.add (.var "dz") (.lit 1)))) (skipLoop "dz"))

/-- Read the window and skip the distance matrix. -/
def readWinS : Com := .seq readWin skipDm

set_option maxHeartbeats 1000000 in
/-- **Reading the window and skipping the matrix.** -/
theorem readWinS_run {B n k q : ℕ} (G : PartialGraph (Fin n)) {Dt rest : List ℕ} {σ : Env}
    (hinp : σ.inp = (toWord G ++ [k, q]) ++ (n :: Dt) ++ rest) (hDt : Dt.length = n * (n + 1))
    (heo : (σ.arrs "eo").length = n + 1) (het : (σ.arrs "et").length = offL G.edge n)
    (hno : (σ.arrs "no").length = n + 1) (hnt : (σ.arrs "nt").length = offL G.nonEdge n)
    (hnB : n + 1 < B) (hEB : offL G.edge n + 1 < B) (hNB : offL G.nonEdge n + 1 < B)
    (hnnB : n * (n + 1) < B) :
    ∃ σ', Run B readWinS σ σ' (winCost n + 9 * (n * (n + 1)) + 20) ∧
      σ'.vars "cn" = n ∧ σ'.vars "kk" = k ∧ σ'.vars "qq" = q ∧ σ'.inp = rest ∧ σ'.out = σ.out ∧
      (∀ x, x ∉ ["eo", "et", "no", "nt"] → σ'.arrs x = σ.arrs x) ∧
      (∀ x, x ∉ readWinS.wvars → σ'.vars x = σ.vars x) := by
  obtain ⟨σ1, r1, -, -, hcn1, hk1, hq1, hin1, ho1, ha1, -⟩ := readWin_run (B := B) (k := k) (q := q)
    G (rest := (n :: Dt) ++ rest) (by rw [hinp]; simp) heo het hno hnt hnB hEB hNB
  set σ2 : Env := { σ1.setVar "dz" n with inp := Dt ++ rest } with hσ2
  have r2 : Run B (.read "dz") σ1 σ2 1 := Run.read (by rw [hin1]; simp)
  set σ3 := σ2.setVar "dz" (n * (n + 1)) with hσ3
  have r3 : Run B (.assign "dz" (.mul (.var "dz") (.add (.var "dz") (.lit 1)))) σ2 σ3 6 := by
    refine (Run.assign ?_).mono (by simp [Expr.size])
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    have : n + 1 ≤ n * (n + 1) ∨ n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact Or.inr h
      · exact Or.inl (Nat.le_mul_of_pos_left _ h)
    exact ⟨n, n + 1, ⟨by simp [hσ2], by simp [hσ2]; omega⟩,
      ⟨n, 1, ⟨by simp [hσ2], by simp [hσ2]; omega⟩, ⟨rfl, by omega⟩, by simp, by omega⟩,
      by simp, by omega⟩
  obtain ⟨σ4, r4, hin4, hv4, ha4, ho4⟩ := skipLoop_run (B := B) (c := "dz") (by decide) (by decide)
    (σ := σ3) (l := Dt) (rest := rest) (by simp [hσ3, hσ2]) (by simp [hσ3, hDt]) (by omega)
  have hrun : Run B readWinS σ σ4 (winCost n + 9 * (n * (n + 1)) + 20) := by
    unfold readWinS skipDm
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono ?_
    rw [hDt]; omega
  have hvv : ∀ x, x ≠ "dz" → x ≠ "ci2" → x ≠ "cx" → σ4.vars x = σ1.vars x := by
    intro x h1 h2 h3
    rw [hv4 x h2 h3]; simp [hσ3, hσ2, h1]
  refine ⟨σ4, hrun, by rw [hvv "cn" (by decide) (by decide) (by decide), hcn1],
    by rw [hvv "kk" (by decide) (by decide) (by decide), hk1],
    by rw [hvv "qq" (by decide) (by decide) (by decide), hq1], hin4,
    by rw [ho4]; simp [hσ3, hσ2, ho1], fun x hx => by rw [ha4]; simp [hσ3, hσ2, ha1 x hx],
    fun x hx => hrun.frame_var x hx⟩

/-- The first round after the tag and the length of the input. -/
def round0 : Com :=
  .seq readWinS (.ite (.lt (.lit 0) (.var "qq")) r0b (.seq (.write (.lit 0)) (.write (.lit 0))))

theorem length_toWord_famW {n : ℕ} (f : Fin n → TypeTree) :
    (toWord (famW f)).length = (toWord f).length + n := by
  rw [toWord_fam, length_toWord_words, length_famW]
  simp [total, famW, List.length_flatten, List.sum_ofFn]
  omega

set_option maxHeartbeats 4000000 in
/-- **The first round.** -/
theorem round0_run {B n k q L : ℕ} (G : PartialGraph (Fin n)) (f : Fin n → TypeTree) (hn : 1 ≤ n)
    {Dw Dt : List ℕ} (hDw : Dw = n :: Dt) (hDt : Dt.length = n * (n + 1))
    {σ : Env} (hL : ∀ i, (toWord (f i)).length ≤ L)
    (hinp : σ.inp = (toWord G ++ [k, q]) ++ Dw ++ toWord f ++ [0])
    (hsl : σ.vars "sl" = (toWord G).length + 2 + Dw.length + (toWord f).length)
    (heo : (σ.arrs "eo").length = n + 1) (het : (σ.arrs "et").length = offL G.edge n)
    (hno : (σ.arrs "no").length = n + 1) (hnt : (σ.arrs "nt").length = offL G.nonEdge n)
    (hxl : 8 + (toWord f).length + n ≤ (σ.arrs "x").length)
    (hnB : n + 1 < B) (hEB : offL G.edge n + 1 < B) (hNB : offL G.nonEdge n + 1 < B)
    (hB : 2 * ((toWord G).length + Dw.length + (toWord f).length) + n + 20 < B)
    (hv : ∀ v ∈ toWord f, v < B) (hk : k < B) (hq : q < B) :
    ∃ σ', Run B round0 σ σ' (winCost n + 9 * (n * (n + 1)) + n * (48 * L + 110) +
        100 * ((toWord f).length + n) + 1020) ∧
      σ'.out = σ.out ++ (if q = 0 then [0, 0] else
        [1, (stState n k q 0 ((toWord G).length + 2 + Dw.length) (famW f) []).length, 0] ++
          stState n k q 0 ((toWord G).length + 2 + Dw.length) (famW f) [] ++ toWord (f ⟨0, hn⟩)) := by
  have hDl : Dw.length = 1 + n * (n + 1) := by rw [hDw, List.length_cons, hDt]; omega
  have hnnB : n * (n + 1) < B := by omega
  obtain ⟨σ1, r1, hcn1, hk1, hq1, hin1, ho1, ha1, hv1⟩ := readWinS_run (B := B) (k := k) (q := q)
    G (Dt := Dt) (rest := toWord f ++ [0]) (by rw [hinp, hDw]; simp) hDt heo het hno hnt hnB hEB hNB
    hnnB
  have hsl1 : σ1.vars "sl" = (toWord G).length + 2 + Dw.length + (toWord f).length := by
    rw [hv1 _ (by simp [readWinS, skipDm, readWin, readCsr, vtxRd, slotRd, skipLoop, forUp,
      Com.wvars])]; exact hsl
  by_cases hq0 : q = 0
  · subst hq0
    have hrun : Run B round0 σ { { σ1 with out := σ1.out ++ [0] } with out := σ1.out ++ [0] ++ [0] }
        (winCost n + 9 * (n * (n + 1)) + n * (48 * L + 110) + 100 * ((toWord f).length + n) + 1020) := by
      unfold round0
      refine (Run.seq r1 (Run.ite_false ?_ (Run.seq (Run.write (v := 0) ?_) (Run.write (v := 0) ?_)))).mono ?_
      · simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff, hq1]
        exact ⟨0, 0, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp⟩
      · simp; omega
      · simp; omega
      · simp [Expr.size]; omega
    exact ⟨_, hrun, by simp [ho1]⟩
  -- the header of the state
  set O := σ1.arrs "x" with hO
  have hOl : 8 + (toWord f).length + n ≤ O.length := by rw [hO, ha1 _ (by decide)]; exact hxl
  set τ0 := σ1.setVar "xp" 0 with hτ0
  have r0 : Run B (.assign "xp" (.lit 0)) σ1 τ0 2 := (Run.assign (by simp; omega)).mono (by simp [Expr.size])
  have hx0 : XAt O [] τ0 := ⟨by simp [hτ0], by simp [hτ0, hO]⟩
  have hcn0 : τ0.vars "cn" = n := by simp [hτ0, hcn1]
  have hk0 : τ0.vars "kk" = k := by simp [hτ0, hk1]
  have hq0' : τ0.vars "qq" = q := by simp [hτ0, hq1]
  obtain ⟨τa, ra, hxa, hia, hoa⟩ := push_run (B := B) (O := O) (pre := []) (e := .lit 0) (v := 0) hx0
    (by simp; omega) (by simp; omega) (by simp; omega)
  obtain ⟨τb, rb, hxb, hib, hob⟩ := push_run (B := B) (O := O) (pre := [0]) (e := .var "cn") (v := n) hxa
    (by simp; omega) (by simp; omega) (by simp [ra.frame_var "cn" (by decide), hcn0]; omega)
  obtain ⟨τc, rc, hxc, hic, hoc⟩ := push_run (B := B) (O := O) (pre := [0] ++ [n]) (e := .var "kk") (v := k)
    hxb (by simp; omega) (by simp; omega)
    (by simp [rb.frame_var "kk" (by decide), ra.frame_var "kk" (by decide), hk0]; omega)
  obtain ⟨τd, rd, hxd, hid, hod⟩ := push_run (B := B) (O := O) (pre := [0] ++ [n] ++ [k]) (e := .var "qq")
    (v := q) hxc (by simp; omega) (by simp; omega)
    (by simp [rc.frame_var "qq" (by decide), rb.frame_var "qq" (by decide), ra.frame_var "qq" (by decide),
      hq0']; omega)
  obtain ⟨τe, re, hxe, hie, hoe⟩ := push_run (B := B) (O := O) (pre := [0] ++ [n] ++ [k] ++ [q]) (e := .lit 0)
    (v := 0) hxd (by simp; omega) (by simp; omega) (by simp; omega)
  obtain ⟨τf, rf, hxf, hif, hof⟩ := push_run (B := B) (O := O) (pre := [0] ++ [n] ++ [k] ++ [q] ++ [0])
    (e := .lit 0) (v := 0) hxe (by simp; omega) (by simp; omega) (by simp; omega)
  have hpre : [0] ++ [n] ++ [k] ++ [q] ++ [0] ++ [0] = [0, n, k, q, 0, 0] := by simp
  rw [hpre] at hxf
  have hhead : Run B (.seq (.assign "xp" (.lit 0)) (.seq (push (.lit 0)) (.seq (push (.var "cn"))
      (.seq (push (.var "kk")) (.seq (push (.var "qq")) (.seq (push (.lit 0)) (push (.lit 0))))))))
      σ1 τf 60 :=
    (Run.seq r0 (Run.seq ra (Run.seq rb (Run.seq rc (Run.seq rd (Run.seq re rf)))))).mono
      (by simp [Expr.size])
  have hinf : τf.inp = toWord f ++ [0] := by rw [hif, hie, hid, hic, hib, hia]; simp [hτ0, hin1]
  -- the family
  have hFl := length_toWord_famW f
  obtain ⟨τg, rg, hxg, hig, hog⟩ := cpFam_run (B := B) (L := L) f hxf hinf hL (by simp; omega)
    (by simp; omega) hv
  set S0 := stState n k q 0 ((toWord G).length + 2 + Dw.length) (famW f) [] with hS0
  have hpa : τg.vars "xp" = 6 + (toWord (famW f)).length := by rw [hxg.1]; simp; omega
  set τh := τg.setVar "pa" (6 + (toWord (famW f)).length) with hτh
  have rh : Run B (.assign "pa" (.var "xp")) τg τh 2 :=
    (Run.assign (by simp [hpa]; omega)).mono (by simp [Expr.size])
  obtain ⟨τi, ri, hxi, hii, hoi⟩ := push_run (B := B) (O := O)
    (pre := [0, n, k, q, 0, 0] ++ toWord (famW f)) (e := .lit 0) (v := 0)
    (XAt.setVar (x := "pa") hxg (by decide) (6 + (toWord (famW f)).length)) (by simp; omega) (by simp; omega) (by simp; omega)
  -- the length of the window
  have hpai : τi.vars "pa" = 6 + (toWord (famW f)).length := by
    rw [ri.frame_var "pa" (by decide)]; simp [hτh]
  have hwv : ∀ x, x ∈ ["sl", "cn"] → τi.vars x = σ1.vars x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [ri.frame_var "sl" (by decide)]; simp only [hτh, vars_setVar, show ("sl" : String) = "pa" ↔ False by decide, if_false]
      rw [rg.frame_var "sl" (by simp [cpFam, cpTree, cpNode, cpList, cpFrame, cpEntries, cpEntry, push,
        forUp, Com.wvars]), hhead.frame_var "sl" (by simp [push, Com.wvars])]
    · rw [ri.frame_var "cn" (by decide)]; simp only [hτh, vars_setVar, show ("cn" : String) = "pa" ↔ False by decide, if_false]
      rw [rg.frame_var "cn" (by simp [cpFam, cpTree, cpNode, cpList, cpFrame, cpEntries, cpEntry, push,
        forUp, Com.wvars]), hhead.frame_var "cn" (by simp [push, Com.wvars])]
  have hsli : τi.vars "sl" = (toWord G).length + 2 + Dw.length + (toWord f).length := by
    rw [hwv "sl" (by simp), hsl1]
  have hcni : τi.vars "cn" = n := by rw [hwv "cn" (by simp), hcn1]
  have hxli : (τi.arrs "x").length = O.length := by
    rw [hxi.2]; simp only [List.length_append, List.length_drop, List.length_cons, List.length_nil]
    omega
  set gl := (toWord G).length + 2 + Dw.length with hgl
  have rj : Run B (.store "x" (.lit 5) (.sub (.add (.add (.var "sl") (.var "cn")) (.lit 6)) (.var "pa")))
      τi (τi.setArr "x" 5 gl) 14 := by
    refine (Run.store (idx := 5) (by simp; omega) ?_ (by omega)).mono (by simp [Expr.size])
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, hsli, hcni, hpai]
    exact ⟨(toWord G).length + 2 + Dw.length + (toWord f).length + n + 6, 6 + (toWord (famW f)).length,
      ⟨_, 6, ⟨_, n, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by show _ + _ < B; omega⟩, ⟨rfl, by omega⟩,
        rfl, by show _ + _ < B; omega⟩, ⟨rfl, by omega⟩, by show _ = _ - _; omega,
        by omega⟩
  have hxj : XAt O S0 (τi.setArr "x" 5 gl) := by
    have h1 : [0, n, k, q, 0, 0] ++ toWord (famW f) ++ [0] = [0, n, k, q, 0] ++ 0 :: (toWord (famW f) ++ [0]) := by
      simp
    rw [h1] at hxi
    have := XAt.setBack hxi gl
    have h2 : [0, n, k, q, 0] ++ gl :: (toWord (famW f) ++ [0]) = S0 := by
      simp [hS0, stState, toWord_words ([] : List (List ℕ)), frames]
    rw [h2] at this
    exact this
  -- the output
  set τk := ((((τi.setArr "x" 5 gl).setVar "otg" 1).setVar "owin" 0).setVar "ws0" 7).setVar "wc" 0
    with hτk
  have rk1 : Run B (.assign "otg" (.lit 1)) (τi.setArr "x" 5 gl) ((τi.setArr "x" 5 gl).setVar "otg" 1) 2 :=
    (Run.assign (by simp; omega)).mono (by simp [Expr.size])
  have rk2 : Run B (.assign "owin" (.lit 0)) ((τi.setArr "x" 5 gl).setVar "otg" 1)
      (((τi.setArr "x" 5 gl).setVar "otg" 1).setVar "owin" 0) 2 :=
    (Run.assign (by simp; omega)).mono (by simp [Expr.size])
  have rk3 : Run B (.assign "ws0" (.lit 7)) (((τi.setArr "x" 5 gl).setVar "otg" 1).setVar "owin" 0)
      ((((τi.setArr "x" 5 gl).setVar "otg" 1).setVar "owin" 0).setVar "ws0" 7) 2 :=
    (Run.assign (by simp; omega)).mono (by simp [Expr.size])
  have rk4 : Run B (.assign "wc" (.lit 0))
      ((((τi.setArr "x" 5 gl).setVar "otg" 1).setVar "owin" 0).setVar "ws0" 7) τk 2 :=
    (Run.assign (by simp; omega)).mono (by simp [Expr.size])
  have hxk : XAt O S0 τk := by
    exact XAt.setVar (XAt.setVar (XAt.setVar (XAt.setVar hxj (by decide) _) (by decide) _) (by decide) _)
      (by decide) _
  have hS0l : S0.length = 7 + (toWord f).length + n := by
    rw [hS0, length_stState, hFl, length_toWord_words ([] : List (List ℕ))]
    first | omega | (simp [total]; omega) | simp [total]
  have hdrop : S0.drop 7 = frames (famW f) ++ [0] := by
    simp [hS0, stState, toWord_words (famW f), toWord_words ([] : List (List ℕ)), frames]
  have hSv : ∀ v ∈ S0, v < B := by
    intro v hv'
    simp only [hS0, stState, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with ((h | h | h | h | h | h) | h) | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [toWord_words, length_famW] at h
      rcases List.mem_cons.mp h with h | h
      · omega
      · obtain ⟨u, hu, hvu⟩ := List.mem_flatten.mp h
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
        rw [famW, List.mem_ofFn] at hw
        obtain ⟨i, rfl⟩ := hw
        rcases List.mem_cons.mp hvu with h | h
        · have hle : (toWord (f i)).length ≤ (toWord f).length := by
            rw [toWord_fam]
            have hm : toWord (f i) ∈ famW f := by rw [famW, List.mem_ofFn]; exact ⟨i, rfl⟩
            have h3 := (List.infix_of_mem_flatten hm).length_le
            simp only [List.length_cons]; omega
          rw [h]; omega
        · have hm : toWord (f i) ∈ famW f := by rw [famW, List.mem_ofFn]; exact ⟨i, rfl⟩
          have hm2 : v ∈ toWord f := by
            rw [toWord_fam]; exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_, hm, h⟩)
          exact hv v hm2
    · simp [toWord_words, frames] at h; omega
  have hj0 : 0 < (famW f).length := by rw [length_famW]; omega
  obtain ⟨τl, rl, hol⟩ := tail_run (B := B) (S := S0) (D := O.drop S0.length) (p := 7) (j := 0) (tg := 1)
    (win := 0) (ws := famW f) (r := [0]) (τ := τk) hxk.2 hxk.1 (by simp [hτk]) (by simp [hτk])
    (by simp [hτk]) (by simp [hτk]) hj0 hdrop (by omega) hSv (by omega) (by omega)
  have hw0 : (famW f)[0] = toWord (f ⟨0, hn⟩) := by simp [famW]
  have hr0b : Run B r0b σ1 τl (2 + 9 + 9 + 9 + 9 + 9 + 9 + (n * (48 * L + 110) + 30) + 2 + 9 + 14 +
      2 + 2 + 2 + 2 + (60 * S0.length + 60)) := by
    unfold r0b
    exact (Run.seq r0 (Run.seq ra (Run.seq rb (Run.seq rc (Run.seq rd (Run.seq re (Run.seq rf
      (Run.seq rg (Run.seq rh (Run.seq ri (Run.seq rj (Run.seq rk1 (Run.seq rk2 (Run.seq rk3
      (Run.seq rk4 rl))))))))))))))).mono (by simp [Expr.size]; omega)
  have hrun : Run B round0 σ τl
      (winCost n + 9 * (n * (n + 1)) + n * (48 * L + 110) + 100 * ((toWord f).length + n) + 1020) := by
    unfold round0
    refine (Run.seq r1 (Run.ite_true ?_ hr0b)).mono ?_
    · simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff, hq1]
      exact ⟨0, q, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp; omega⟩
    · simp only [Expr.size, Cond.size]; rw [hS0l]; nlinarith
  refine ⟨τl, hrun, ?_⟩
  rw [hol, if_neg hq0, hw0]
  have : τk.out = σ.out := by
    simp [hτk, hoi, hτh, hog, hof, hoe, hod, hoc, hob, hoa, hτ0, ho1]
  rw [this]; simp

end Lax185574Proofs.StpRam
