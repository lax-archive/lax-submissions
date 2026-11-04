import Lax185574Proofs.JobMap.Script
import Lax185574Proofs.JobMap.Loops
import Lax808846Proofs.Compile

/-!
The glue program of the composite that runs a program on every job.

Round `j` reads the threshold `T = W / 64` from the guard scalar `W`,
the tag and the window length, the input word into `x`, and then the
state into `f`: in the first round nothing, later the index `j - 1`, the
frames of the earlier answers and the new answer. It checks every number
it passes on to the next round against `T`, and the lengths it writes.
If `j` is the number of jobs it writes `0 :: toWord (js.map f)`,
otherwise the head of the next round and the job `js[j]` as the query.

`glue_run` is the run of the command on the input of round `j` at any
value bound `W + 1` that holds the input: the output is `gOut js f j`,
the cost is linear in the lengths of `x` and of the frames of the
answers, and `ovf` stays `0` exactly if the checks `Checks` hold.
-/

namespace Lax185574Proofs.JobMap

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574.WordEncoding Lax185574Proofs.Words

/-! ### The command -/

/-- The head: the threshold, the tag, the window length, and the input into `x`. -/
def hdCmd : Com :=
  .seq (.assign "T" (.div (.var "W") (.lit 64)))
  (.seq (.read "tg") (.seq (.read "sl")
  (.seq (.ite (.eq (.var "tg") (.lit 0)) (.assign "nx" (.var "sl"))
    (.assign "nx" (.sub (.var "tg") (.lit 1))))
  (.seq (.assign "bs" (.lit 0)) (.seq (.assign "cnt" (.var "nx")) (rdChk "x"))))))

/-- The state after the first round: the index, the frames of the
answers, and the new answer. -/
def stCmd1 : Com :=
  .seq (.read "w") (.seq (.read "jp") (.seq (.assign "jj" (.add (.var "jp") (.lit 1)))
  (.seq (.assign "bs" (.lit 0)) (.seq (.assign "cnt" (.sub (.var "sl") (.lit 1))) (.seq (rdChk "f")
  (.seq (.assign "lb" (.get "f" (.sub (.var "sl") (.lit 2))))
  (.seq (.assign "bs" (.sub (.var "sl") (.lit 1))) (.seq (.assign "cnt" (.var "lb"))
  (.seq (rdChk "f") (.assign "fl" (.add (.sub (.var "sl") (.lit 1)) (.var "lb"))))))))))))

/-- The state. -/
def stCmd : Com :=
  .ite (.eq (.var "tg") (.lit 0)) (.seq (.assign "jj" (.lit 0)) (.assign "fl" (.lit 0))) stCmd1

/-- The checks of the lengths written. -/
def ckCmd : Com := .seq (chkE (.add (.var "nx") (.lit 1))) (chkE (.add (.var "fl") (.lit 2)))

/-- Write the frames of the answers. -/
def wrF : Com := forUp "i" (.var "fl") (.write (.get "f" (.var "i")))

/-- Find the position of the frame of job `jj`. -/
def findJob : Com :=
  .seq (.assign "p" (.lit 1))
    (forUp "i" (.var "jj") (.assign "p" (.add (.add (.var "p") (.get "x" (.var "p"))) (.lit 1))))

/-- Write the job at `p`. -/
def wrJob : Com :=
  .seq (.assign "lj" (.get "x" (.var "p")))
    (forUp "i" (.var "lj") (.write (.get "x" (.add (.add (.var "p") (.lit 1)) (.var "i")))))

/-- The output: the result after the last job, otherwise the head of the
next round and the query. -/
def outCall : Com :=
  .seq (.write (.add (.var "nx") (.lit 1))) (.seq (.write (.add (.var "fl") (.lit 2)))
    (.seq (.write (.var "nx")) (.seq (.write (.lit 0)) (.seq (.write (.var "jj"))
    (.seq wrF (.seq findJob wrJob))))))

def outCmd : Com :=
  .ite (.eq (.var "jj") (.get "x" (.lit 0))) (.seq (.write (.lit 0)) (.seq (.write (.var "jj")) wrF))
    outCall

/-- The glue program. -/
def glueCmd : Com := .seq (.seq hdCmd stCmd) (.seq ckCmd outCmd)

/-- The scalars and arrays of `glueCmd`. -/
def glueLay : Layout :=
  ⟨["W", "ovf", "T", "tg", "sl", "nx", "i", "w", "cnt", "bs", "jp", "jj", "lb", "fl", "p", "lj"],
    ["x", "f"], 4⟩

theorem glueCmd_ok : Com.Ok glueLay glueCmd := by
  simp [glueCmd, hdCmd, stCmd, stCmd1, ckCmd, outCmd, outCall, wrF, findJob, wrJob, rdChk, rdBody,
    chkE, forUp, glueLay, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-- The array lengths of round `j`. -/
def gExt (js : List (List ℕ)) (f : List ℕ → List ℕ) (j : ℕ) : String → ℕ :=
  fun a => if a = "x" then (toWord js).length else (fr js f j).length

/-- The checks of round `j` at threshold `T`. -/
def Checks (js : List (List ℕ)) (f : List ℕ → List ℕ) (j T : ℕ) : Prop :=
  (toWord js).length + 1 ≤ T ∧ (fr js f j).length + 2 ≤ T ∧ (∀ y ∈ toWord js, y ≤ T) ∧
    ∀ y ∈ fr js f j, y ≤ T

/-! ### The head -/

theorem hd_run {W : ℕ} (X rest : List ℕ) (t0 l0 : ℕ) (σ : Env) (hW : 64 ≤ W)
    (hX : ∀ y ∈ X, y ≤ W) (hXW : X.length + 1 ≤ W)
    (ht : (t0 = 0 ∧ l0 = X.length) ∨ t0 = X.length + 1)
    (hinp : σ.inp = [t0, l0] ++ X ++ rest) (hx : σ.arrs "x" = List.replicate X.length 0)
    (hWv : σ.vars "W" = W) (hov : σ.vars "ovf" = 0) :
    ∃ σ', Run (W + 1) hdCmd σ σ' (20 * X.length + 40) ∧ σ'.arrs "x" = X ∧ σ'.inp = rest ∧
      σ'.vars "tg" = t0 ∧ σ'.vars "sl" = l0 ∧ σ'.vars "nx" = X.length ∧ σ'.vars "T" = W / 64 ∧
      σ'.vars "ovf" ≤ 1 ∧ (σ'.vars "ovf" = 0 ↔ ∀ y ∈ X, y ≤ W / 64) := by
  have ht0 : t0 ≤ W := by omega
  have hT : W / 64 ≤ W := Nat.div_le_self _ _
  set σ0 := σ.setVar "T" (W / 64) with hσ0
  set σ1 : Env := { σ0.setVar "tg" t0 with inp := l0 :: (X ++ rest) } with hσ1
  set σ2 : Env := { σ1.setVar "sl" l0 with inp := X ++ rest } with hσ2
  have hite : Run (W + 1) (.ite (.eq (.var "tg") (.lit 0)) (.assign "nx" (.var "sl"))
      (.assign "nx" (.sub (.var "tg") (.lit 1)))) σ2 (σ2.setVar "nx" X.length) 8 := by
    have hc : (Cond.eq (.var "tg") (.lit 0)).evalB (W + 1) σ2 = some (t0 == 0) :=
      evalB_condEq (by simp [hσ2, hσ1]; omega) (evalB_lit (by omega))
    rcases ht with ⟨h0, hl⟩ | h1
    · exact (Run.ite_true (by rw [hc, h0]; rfl)
        (Run.assign (by simp [hσ2, hl]; omega))).mono (by simp)
    · refine (Run.ite_false (by rw [hc, h1]; simp) (Run.assign ?_)).mono (by simp)
      simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      refine ⟨t0, 1, ⟨by simp [hσ2, hσ1], by simp [hσ2, hσ1]; omega⟩, ⟨rfl, by omega⟩, ?_, ?_⟩
      · simp [h1]
      · omega
  set σ3 := ((σ2.setVar "nx" X.length).setVar "bs" 0).setVar "cnt" X.length with hσ3
  obtain ⟨σ4, r4, hin4, hx4, ho41, ho4⟩ := rdChk_run (B := W + 1) "x" (u := X) (rest := rest)
    (σ := σ3) (b0 := 0) (by omega) (by simp [hσ3, hσ2]) (by simp [hσ3]) (by simp [hσ3])
    (by simp [hσ3, hσ2, hσ1, hσ0, hx]) (by omega) (fun y hy => by have := hX y hy; omega)
    (by simp [hσ3, hσ2, hσ1, hσ0]; omega) (by simp [hσ3, hσ2, hσ1, hσ0, hov])
  have hfr : ∀ y, y ∉ (rdChk "x").wvars → σ4.vars y = σ3.vars y := fun y hy => r4.frame_var y hy
  refine ⟨σ4, ?_, ?_, hin4, ?_, ?_, ?_, ?_, ho41, ?_⟩
  · unfold hdCmd
    refine (Run.seq (Run.assign (v := W / 64) ?_) (Run.seq (Run.read (by simp [hinp]))
      (Run.seq (Run.read rfl) (Run.seq hite (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq (Run.assign (by simp; omega)) r4)))))).mono ?_
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨W, 64, ⟨hWv.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by simp; omega⟩
    · simp; omega
  · rw [hx4]; simp [hσ3, hσ2, hσ1, hσ0, hx]
  · rw [hfr "tg" (by decide)]; simp [hσ3, hσ2, hσ1]
  · rw [hfr "sl" (by decide)]; simp [hσ3, hσ2]
  · rw [hfr "nx" (by decide)]; simp [hσ3]
  · rw [hfr "T" (by decide)]; simp [hσ3, hσ2, hσ1, hσ0]
  · rw [ho4]; simp [hσ3, hσ2, hσ1, hσ0, hov]

/-! ### The state -/

theorem st1_run {W : ℕ} (F b rest : List ℕ) (jm : ℕ) (σ : Env)
    (hinp : σ.inp = [0, jm] ++ F ++ (b.length :: b) ++ rest) (hsl : σ.vars "sl" = F.length + 2)
    (hf : σ.arrs "f" = List.replicate (F.length + 1 + b.length) 0)
    (hT : σ.vars "T" ≤ W) (hov : σ.vars "ovf" ≤ 1) (hFW : F.length + b.length + 3 ≤ W)
    (hjm : jm + 1 ≤ W) (hFv : ∀ y ∈ F, y ≤ W) (hbv : ∀ y ∈ b, y ≤ W) :
    ∃ σ', Run (W + 1) stCmd1 σ σ' (20 * (F.length + b.length) + 100) ∧
      σ'.arrs "f" = F ++ b.length :: b ∧ σ'.vars "jj" = jm + 1 ∧
      σ'.vars "fl" = F.length + 1 + b.length ∧ σ'.vars "ovf" ≤ 1 ∧
      (σ'.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ ∀ y ∈ F ++ b.length :: b, y ≤ σ.vars "T") := by
  set σa : Env := { σ.setVar "w" 0 with inp := jm :: (F ++ (b.length :: b) ++ rest) } with hσa
  set σb : Env := { σa.setVar "jp" jm with inp := F ++ (b.length :: b) ++ rest } with hσb
  set σc := ((σb.setVar "jj" (jm + 1)).setVar "bs" 0).setVar "cnt" (F.length + 1) with hσc
  obtain ⟨σd, rd, hind, hfd, hod1, hod⟩ := rdChk_run (B := W + 1) "f" (u := F ++ [b.length])
    (rest := b ++ rest) (σ := σc) (b0 := 0) (by omega) (by simp [hσc, hσb])
    (by simp [hσc]) (by simp [hσc]) (by simp [hσc, hσb, hσa, hf]) (by simp; omega)
    (by intro y hy; simp at hy; rcases hy with hy | hy; · have := hFv y hy; omega
        · omega)
    (by simp [hσc, hσb, hσa]; omega) (by simp [hσc, hσb, hσa]; omega)
  have hfd' : σd.arrs "f" = F ++ [b.length] ++ List.replicate b.length 0 := by
    rw [hfd]; simp [hσc, hσb, hσa, hf]
  have hvd : ∀ y, y ∉ (rdChk "f").wvars → σd.vars y = σc.vars y := fun y hy => rd.frame_var y hy
  have hsld : σd.vars "sl" = F.length + 2 := by rw [hvd "sl" (by decide)]; simp [hσc, hσb, hσa, hsl]
  have hlb : (σd.arrs "f")[F.length]? = some b.length := by
    rw [hfd', List.append_assoc, List.getElem?_append_right (by omega)]; simp
  set σe := ((σd.setVar "lb" b.length).setVar "bs" (F.length + 1)).setVar "cnt" b.length with hσe
  obtain ⟨σg, rg, hing, hfg, hog1, hog⟩ := rdChk_run (B := W + 1) "f" (u := b) (rest := rest)
    (σ := σe) (b0 := F.length + 1) (by omega) (by simp [hσe, hind])
    (by simp [hσe]) (by simp [hσe]) (by simp [hσe, hfd']; omega) (by omega)
    (fun y hy => by have := hbv y hy; omega)
    (by simp only [hσe, vars_setVar]; simp; rw [hvd "T" (by decide)]; simp [hσc, hσb, hσa]; omega)
    (by simp [hσe]; omega)
  have hvg : ∀ y, y ∉ (rdChk "f").wvars → σg.vars y = σe.vars y := fun y hy => rg.frame_var y hy
  refine ⟨σg.setVar "fl" (F.length + 1 + b.length), ?_, ?_, ?_, by simp, ?_, ?_⟩
  · unfold stCmd1
    refine Run.mono (σ := σ) (Run.seq (Run.read (v := 0) (rest := jm :: (F ++ (b.length :: b) ++ rest))
      (by simp [hinp])) (Run.seq (Run.read (v := jm) (rest := F ++ (b.length :: b) ++ rest) rfl)
      (Run.seq (Run.assign (v := jm + 1) (by simp; omega))
      (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq (Run.assign (v := F.length + 1) (by simp [hσb, hsl]; omega)) (Run.seq rd
      (Run.seq (Run.assign (v := b.length) ?_)
      (Run.seq (Run.assign (v := F.length + 1) (by simp [hsld]; omega))
      (Run.seq (Run.assign (v := b.length) (by simp; omega)) (Run.seq rg
      (Run.assign ?_))))))))))) ?_
    · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨F.length, ⟨F.length + 2, 2, ⟨hsld.symm, by omega⟩, ⟨rfl, by omega⟩, by simp, by omega⟩,
        hlb, by omega⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      refine ⟨F.length + 1, b.length, ⟨F.length + 2, 1, ⟨?_, ?_⟩, ⟨rfl, by omega⟩, by simp, by omega⟩,
        ⟨?_, ?_⟩, rfl, by omega⟩
      · rw [hvg "sl" (by decide)]; simp [hσe, hsld]
      · rw [hvg "sl" (by decide)]; simp [hσe, hsld]; omega
      · rw [hvg "lb" (by decide)]; simp [hσe]
      · rw [hvg "lb" (by decide)]; simp [hσe]; omega
    · simp; omega
  · simp only [arrs_setVar]; rw [hfg]
    have e0 : σe.arrs "f" = (F ++ [b.length]) ++ List.replicate b.length 0 := by
      simp only [hσe, arrs_setVar, hfd']
    rw [e0, List.take_left' (by simp), List.drop_eq_nil_of_le (by simp; omega)]
    simp
  · simp only [vars_setVar]; simp; rw [hvg "jj" (by decide)]; simp [hσe]
    rw [hvd "jj" (by decide)]; simp [hσc]
  · simp; omega
  · have hTe : σe.vars "T" = σ.vars "T" := by
      simp only [hσe, vars_setVar]; simp; rw [hvd "T" (by decide)]; simp [hσc, hσb, hσa]
    have hoe : σe.vars "ovf" = σd.vars "ovf" := by simp [hσe]
    have hTc : σc.vars "T" = σ.vars "T" := by simp [hσc, hσb, hσa]
    have hoc : σc.vars "ovf" = σ.vars "ovf" := by simp [hσc, hσb, hσa]
    simp only [vars_setVar, show ("ovf" = "fl") = False by decide, if_false]
    rw [hog, hoe, hTe, hod, hTc, hoc]
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun y hy => ?_⟩
      rcases hy with hy | hy | hy
      · exact h2 y (Or.inl hy)
      · exact h2 y (Or.inr hy)
      · exact h3 y hy
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun y hy => hy.elim (fun h => h2 y (Or.inl h)) (fun h => h2 y (Or.inr (Or.inl h)))⟩,
        fun y hy => h2 y (Or.inr (Or.inr hy))⟩

/-! ### The output -/

/-- A loop that writes the values `g 0, …, g (N − 1)` (as
`Words.glue_writeLoop_run'`). -/
theorem wrLoop_run {B N : ℕ} {i m : String} {e : Expr} (g : ℕ → ℕ) (P : Env → Prop)
    (hNB : N < B) (hPw : ∀ τ (o : List ℕ), P τ → P { τ with out := o })
    (hPi : ∀ τ k, P τ → P (τ.setVar i k)) (hmN : ∀ τ, P τ → τ.vars m = N)
    (he : ∀ τ, P τ → τ.vars i < N → e.evalB B τ = some (g (τ.vars i))) (σ : Env) (hσ : P σ) :
    ∃ σ', Run B (forUp i (.var m) (.write e)) σ σ' (N * (e.size + 9) + 6) ∧ P σ' ∧
      σ'.out = σ.out ++ (List.range N).map g := by
  obtain ⟨σ', hr, ⟨hP, hout⟩, -⟩ := forUp_run (B := B) (i := i) (e := .var m) (body := .write e)
    (N := N) (K := 1 + e.size) (fun k τ => P τ ∧ τ.out = σ.out ++ (List.range k).map g) hNB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨(hmN τ hI.1).symm, by rw [hmN τ hI.1]; exact hNB⟩)
    ⟨hPi σ 0 hσ, by simp⟩
    (fun k hk τ hI hik => by
      refine ⟨{ τ with out := τ.out ++ [g k] }, Run.write ?_, by simpa using hik, ?_, ?_⟩
      · rw [← hik]; exact he τ hI.1 (by omega)
      · exact hPi _ _ (hPw τ _ hI.1)
      · simp [hI.2, List.range_succ])
  exact ⟨σ', hr.mono (by simp only [Expr.size]; ring_nf; omega), hP, hout⟩

theorem map_range_getD (u : List ℕ) : (List.range u.length).map (fun k => u.getD k 0) = u := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getD_eq_getElem?_getD, show k < u.length by simpa using h1]

theorem wrF_run {W : ℕ} (F : List ℕ) (σ : Env) (hf : σ.arrs "f" = F) (hfl : σ.vars "fl" = F.length)
    (hFW : F.length ≤ W) (hFv : ∀ y ∈ F, y ≤ W) :
    ∃ σ', Run (W + 1) wrF σ σ' (12 * F.length + 6) ∧ σ'.out = σ.out ++ F := by
  obtain ⟨σ', hr, -, hout⟩ := wrLoop_run (B := W + 1) (N := F.length) (i := "i") (m := "fl")
    (e := .get "f" (.var "i")) (fun k => F.getD k 0)
    (fun τ => τ.arrs "f" = F ∧ τ.vars "fl" = F.length) (by omega)
    (fun τ o h => h) (fun τ k h => by simp [h.1, h.2]) (fun τ h => h.2)
    (fun τ h hi => by
      simp only [evalB_get_iff, evalB_var_iff]
      refine ⟨τ.vars "i", ⟨rfl, by omega⟩, ?_, ?_⟩
      · rw [h.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
      · have := hFv _ (List.getElem_mem hi)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp; omega)
    σ ⟨hf, hfl⟩
  refine ⟨σ', hr.mono (by simp; omega), ?_⟩
  rw [hout, map_range_getD]

theorem findJob_run {W : ℕ} (js : List (List ℕ)) {j : ℕ} (hj : j < js.length) (σ : Env)
    (hx : σ.arrs "x" = toWord js) (hjj : σ.vars "jj" = j) (hXW : (toWord js).length ≤ W) :
    ∃ σ', Run (W + 1) findJob σ σ' (15 * j + 10) ∧ σ'.vars "p" = pos js j := by
  have hJx := jobs_length_lt js
  obtain ⟨σ', hr, ⟨hp, -, -⟩, -⟩ := forUp_run (B := W + 1) (i := "i") (e := .var "jj")
    (body := .assign "p" (.add (.add (.var "p") (.get "x" (.var "p"))) (.lit 1))) (N := j) (K := 7)
    (fun k τ => τ.vars "p" = pos js k ∧ τ.arrs "x" = toWord js ∧ τ.vars "jj" = j)
    (σ := σ.setVar "p" 1) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.2.symm, by rw [hI.2.2]; omega⟩)
    ⟨by simp [pos, frames], by simp [hx], by simp [hjj]⟩
    (fun k hk τ ⟨hp, hxx, hjj'⟩ hik => by
      have hk' : k < js.length := by omega
      have h1 := pos_add_le hk'
      refine ⟨τ.setVar "p" (pos js (k + 1)), (Run.assign ?_).mono (by simp), by simp [hik],
        by simp [hxx, hjj'], by simp [hxx], by simp [hjj']⟩
      simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff]
      refine ⟨pos js k + js[k].length, 1, ⟨pos js k, js[k].length, ⟨hp.symm, by omega⟩,
        ⟨pos js k, ⟨hp.symm, by omega⟩, by rw [hxx]; exact getElem?_pos hk', by omega⟩, rfl,
        by omega⟩, ⟨rfl, by omega⟩, by simp [pos_succ hk']; omega, by rw [pos_succ hk']; omega⟩)
  refine ⟨σ', (Run.seq (Run.assign (evalB_lit (by omega))) hr).mono (by simp; omega), hp⟩

theorem wrJob_run {W : ℕ} (js : List (List ℕ)) {j : ℕ} (hj : j < js.length) (σ : Env)
    (hx : σ.arrs "x" = toWord js) (hp : σ.vars "p" = pos js j) (hXW : (toWord js).length ≤ W)
    (hXv : ∀ y ∈ toWord js, y ≤ W) :
    ∃ σ', Run (W + 1) wrJob σ σ' (15 * js[j].length + 20) ∧ σ'.out = σ.out ++ js[j] := by
  have h1 := pos_add_le hj
  set σ1 := σ.setVar "lj" js[j].length with hσ1
  obtain ⟨σ', hr, -, hout⟩ := wrLoop_run (B := W + 1) (N := js[j].length) (i := "i") (m := "lj")
    (e := .get "x" (.add (.add (.var "p") (.lit 1)) (.var "i"))) (fun k => js[j].getD k 0)
    (fun τ => τ.arrs "x" = toWord js ∧ τ.vars "lj" = js[j].length ∧ τ.vars "p" = pos js j)
    (by omega) (fun τ o h => h) (fun τ k h => by simp [h.1, h.2.1, h.2.2]) (fun τ h => h.2.1)
    (fun τ h hi => by
      simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      have hi' : τ.vars "i" < js[j].length := hi
      refine ⟨pos js j + 1 + τ.vars "i", ⟨pos js j + 1, τ.vars "i", ⟨pos js j, 1, ⟨h.2.2.symm, by omega⟩,
        ⟨rfl, by omega⟩, rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩, ?_, ?_⟩
      · rw [h.1, getElem?_pos_add hj hi', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
        rfl
      · have := hXv _ (mem_job hj (List.getElem_mem hi'))
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; simp; omega)
    σ1 ⟨by simp [hσ1, hx], by simp [hσ1], by simp [hσ1, hp]⟩
  refine ⟨σ', (Run.seq (Run.assign (v := js[j].length) ?_) hr).mono ?_, ?_⟩
  · simp only [evalB_get_iff, evalB_var_iff]
    refine ⟨pos js j, ⟨hp.symm, ?_⟩, by rw [hx]; exact getElem?_pos hj, ?_⟩
    · rw [hp]; omega
    · omega
  · simp; omega
  · rw [hout, map_range_getD]; simp [hσ1]

theorem out_run {W : ℕ} (js : List (List ℕ)) (f : List ℕ → List ℕ) {j : ℕ} (hj : j ≤ js.length)
    (σ : Env) (hx : σ.arrs "x" = toWord js) (hf : σ.arrs "f" = fr js f j)
    (hnx : σ.vars "nx" = (toWord js).length) (hjj : σ.vars "jj" = j)
    (hfl : σ.vars "fl" = (fr js f j).length)
    (hB : (toWord js).length + (fr js f j).length + 2 ≤ W) (hXv : ∀ y ∈ toWord js, y ≤ W)
    (hFv : ∀ y ∈ fr js f j, y ≤ W) :
    ∃ σ', Run (W + 1) outCmd σ σ' (50 * ((toWord js).length + (fr js f j).length) + 100) ∧
      σ'.out = σ.out ++ gOut js f j := by
  have hJx := jobs_length_lt js
  have h0 : (σ.arrs "x")[0]? = some js.length := by rw [hx, toWord_jobs]; rfl
  have hc : (Cond.eq (.var "jj") (.get "x" (.lit 0))).evalB (W + 1) σ = some (j == js.length) :=
    evalB_condEq (by simp [hjj]; omega) (evalB_get (evalB_lit (by omega)) h0 (by omega))
  by_cases hjJ : j = js.length
  · subst hjJ
    set σ1 : Env := { σ with out := σ.out ++ [0] } with hσ1
    set σ2 : Env := { σ1 with out := σ1.out ++ [js.length] } with hσ2
    obtain ⟨σ3, r3, ho3⟩ := wrF_run (W := W) (fr js f js.length) σ2 (by simp [hσ2, hσ1, hf])
      (by simp [hσ2, hσ1, hfl]) (by omega) hFv
    refine ⟨σ3, (Run.ite_true (by rw [hc]; simp) (Run.seq (Run.write (evalB_lit (by omega)))
      (Run.seq (Run.write (by simp [hjj]; omega)) r3))).mono (by simp; omega), ?_⟩
    rw [ho3, gOut_last, toWord_map]
    simp [hσ2, hσ1]
  · have hjl : j < js.length := by omega
    set σ1 : Env := { σ with out := σ.out ++ [(toWord js).length + 1] } with hσ1
    set σ2 : Env := { σ1 with out := σ1.out ++ [(fr js f j).length + 2] } with hσ2
    set σ3 : Env := { σ2 with out := σ2.out ++ [(toWord js).length] } with hσ3
    set σ4 : Env := { σ3 with out := σ3.out ++ [0] } with hσ4
    set σ5 : Env := { σ4 with out := σ4.out ++ [j] } with hσ5
    obtain ⟨σ6, r6, ho6⟩ := wrF_run (W := W) (fr js f j) σ5 (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, hf])
      (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, hfl]) (by omega) hFv
    have hv6 : ∀ y, y ∉ wrF.wvars → σ6.vars y = σ5.vars y := fun y hy => r6.frame_var y hy
    have ha6 : ∀ a, a ∉ wrF.warrs → σ6.arrs a = σ5.arrs a := fun a ha => r6.frame_arr a ha
    obtain ⟨σ7, r7, hp7⟩ := findJob_run (W := W) js hjl σ6
      (by rw [ha6 "x" (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1, hx])
      (by rw [hv6 "jj" (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1, hjj]) (by omega)
    obtain ⟨σ8, r8, ho8⟩ := wrJob_run (W := W) js hjl σ7
      (by rw [r7.frame_arr "x" (by decide), ha6 "x" (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1, hx])
      hp7 (by omega) hXv
    have ho7 : σ7.out = σ6.out := r7.out_eq (by simp [findJob, forUp, Com.NoWrite])
    have hjs := pos_add_le hjl
    have w1 : Run (W + 1) (.write (.add (.var "nx") (.lit 1))) σ σ1 4 :=
      (Run.write (by simp [hnx]; omega)).mono (by simp)
    have w2 : Run (W + 1) (.write (.add (.var "fl") (.lit 2))) σ1 σ2 4 :=
      (Run.write (by simp [hσ1, hfl]; omega)).mono (by simp)
    have w3 : Run (W + 1) (.write (.var "nx")) σ2 σ3 2 :=
      (Run.write (by simp [hσ2, hσ1, hnx]; omega)).mono (by simp)
    have w4 : Run (W + 1) (.write (.lit 0)) σ3 σ4 2 := (Run.write (evalB_lit (by omega))).mono (by simp)
    have w5 : Run (W + 1) (.write (.var "jj")) σ4 σ5 2 :=
      (Run.write (by simp [hσ4, hσ3, hσ2, hσ1, hjj]; omega)).mono (by simp)
    have hoc : Run (W + 1) outCall σ σ8 (4 + (4 + (2 + (2 + (2 + ((12 * (fr js f j).length + 6) +
        ((15 * j + 10) + (15 * js[j].length + 20)))))))) :=
      Run.seq w1 (Run.seq w2 (Run.seq w3 (Run.seq w4 (Run.seq w5 (Run.seq r6 (Run.seq r7 r8))))))
    refine ⟨σ8, (Run.ite_false (by rw [hc]; simp [hjJ]) hoc).mono ?_, ?_⟩
    · simp; omega
    · rw [ho8, ho7, ho6, gOut_lt hjl]
      simp [hσ5, hσ4, hσ3, hσ2, hσ1]

/-! ### One round -/

theorem hs_run (js : List (List ℕ)) (f : List ℕ → List ℕ) {j : ℕ} (hj : j ≤ js.length) {W : ℕ}
    (hW : 64 ≤ W) (hB : (toWord js).length + (fr js f j).length + 2 ≤ W)
    (hXv : ∀ y ∈ toWord js, y ≤ W) (hFv : ∀ y ∈ fr js f j, y ≤ W) :
    ∃ σS k, Run (W + 1) (.seq hdCmd stCmd) ((initEnv (gExt js f j) (gIn js f j)).setVar "W" W) σS k ∧
      k ≤ 40 * ((toWord js).length + (fr js f j).length) + 200 ∧
      σS.arrs "x" = toWord js ∧ σS.arrs "f" = fr js f j ∧ σS.vars "nx" = (toWord js).length ∧
      σS.vars "jj" = j ∧ σS.vars "fl" = (fr js f j).length ∧ σS.vars "T" = W / 64 ∧ σS.out = [] ∧
      σS.vars "ovf" ≤ 1 ∧
      (σS.vars "ovf" = 0 ↔ (∀ y ∈ toWord js, y ≤ W / 64) ∧ ∀ y ∈ fr js f j, y ≤ W / 64) := by
  set σ0 := (initEnv (gExt js f j) (gIn js f j)).setVar "W" W with hσ0
  have hx0 : σ0.arrs "x" = List.replicate (toWord js).length 0 := by simp [hσ0, initEnv, gExt]
  have hf0 : σ0.arrs "f" = List.replicate (fr js f j).length 0 := by simp [hσ0, initEnv, gExt]
  have hJx := jobs_length_lt js
  have hnw : hdCmd.NoWrite := by simp [hdCmd, rdChk, rdBody, chkE, forUp, Com.NoWrite]
  have hnw' : stCmd.NoWrite := by simp [stCmd, stCmd1, rdChk, rdBody, chkE, forUp, Com.NoWrite]
  cases j with
  | zero =>
    obtain ⟨σH, rH, hxH, -, htgH, -, hnxH, hTH, hoH1, hoH⟩ := hd_run (W := W) (toWord js) [0] 0
      (toWord js).length σ0 hW hXv (by omega) (Or.inl ⟨rfl, rfl⟩) (by simp [hσ0, initEnv, gIn])
      hx0 (by simp [hσ0]) (by simp [hσ0, initEnv])
    have hc : (Cond.eq (.var "tg") (.lit 0)).evalB (W + 1) σH = some true := by
      rw [evalB_condEq (m := 0) (n := 0) (by simp [htgH]) (evalB_lit (by omega))]; rfl
    have rS : Run (W + 1) stCmd σH ((σH.setVar "jj" 0).setVar "fl" 0) 8 :=
      (Run.ite_true hc (Run.seq (Run.assign (evalB_lit (by omega)))
        (Run.assign (evalB_lit (by omega))))).mono (by simp)
    have hoH' : σH.out = [] := by rw [rH.out_eq hnw]; simp [hσ0, initEnv]
    have hfH : σH.arrs "f" = [] := by
      rw [rH.frame_arr "f" (by decide), hf0]; simp [fr_zero]
    refine ⟨(σH.setVar "jj" 0).setVar "fl" 0, _, Run.seq rH rS, by omega, by simp [hxH],
      by simp [hfH, fr_zero], by simp [hnxH], by simp, by simp [fr_zero], by simp [hTH],
      by simp [hoH'], by simp [hoH1], ?_⟩
    simp [hoH, fr_zero]
  | succ j =>
    have hjl : j < js.length := by omega
    have hfr := fr_succ (f := f) hjl
    set F := fr js f j with hF
    set b := f js[j] with hb
    have hlen : (fr js f (j + 1)).length = F.length + 1 + b.length := by rw [hfr]; simp; omega
    obtain ⟨σH, rH, hxH, hinH, htgH, hslH, hnxH, hTH, hoH1, hoH⟩ := hd_run (W := W) (toWord js)
      ([0, j] ++ F ++ (b.length :: b)) ((toWord js).length + 1) (F.length + 2) σ0 hW hXv
      (by omega) (Or.inr rfl) (by simp [hσ0, initEnv, gIn_succ hjl, hF, hb]) hx0 (by simp [hσ0])
      (by simp [hσ0, initEnv])
    have hc : (Cond.eq (.var "tg") (.lit 0)).evalB (W + 1) σH = some false := by
      rw [evalB_condEq (m := (toWord js).length + 1) (n := 0) (by simp [htgH]; omega)
        (evalB_lit (by omega))]; simp
    have hfH : σH.arrs "f" = List.replicate (F.length + 1 + b.length) 0 := by
      rw [rH.frame_arr "f" (by decide), hf0, hlen]
    have hFv' : ∀ y ∈ F ++ b.length :: b, y ≤ W := by rw [← hfr]; exact hFv
    obtain ⟨σS, rS, hfS, hjjS, hflS, hoS1, hoS⟩ := st1_run (W := W) F b [] j σH (by simp [hinH])
      hslH hfH (by rw [hTH]; exact Nat.div_le_self _ _) hoH1 (by omega) (by omega)
      (fun y hy => hFv' y (List.mem_append_left _ hy))
      (fun y hy => hFv' y (List.mem_append_right _ (List.mem_cons_of_mem _ hy)))
    have hoH' : σH.out = [] := by rw [rH.out_eq hnw]; simp [hσ0, initEnv]
    have rS' : Run (W + 1) stCmd σH σS _ := Run.ite_false hc rS
    refine ⟨σS, _, Run.seq rH rS', by simp; omega, ?_, by rw [hfS, hfr], ?_, hjjS,
      by rw [hflS, hlen], ?_, ?_, hoS1, ?_⟩
    · rw [rS'.frame_arr "x" (by decide), hxH]
    · rw [rS'.frame_var "nx" (by decide), hnxH]
    · rw [rS'.frame_var "T" (by decide), hTH]
    · rw [rS'.out_eq hnw', hoH']
    · rw [hoS, hoH, hTH, hfr]

theorem glue_run (js : List (List ℕ)) (f : List ℕ → List ℕ) {j : ℕ} (hj : j ≤ js.length) {W : ℕ}
    (hW : 64 ≤ W) (hB : (toWord js).length + (fr js f j).length + 2 ≤ W)
    (hXv : ∀ y ∈ toWord js, y ≤ W) (hFv : ∀ y ∈ fr js f j, y ≤ W) :
    ∃ σ' k, Run (W + 1) glueCmd ((initEnv (gExt js f j) (gIn js f j)).setVar "W" W) σ' k ∧
      σ'.out = gOut js f j ∧ k ≤ 100 * ((toWord js).length + (fr js f j).length) + 400 ∧
      (σ'.vars "ovf" = 0 ↔ Checks js f j (W / 64)) := by
  obtain ⟨σS, k1, rS, hk1, hxS, hfS, hnxS, hjjS, hflS, hTS, hoS, hov1, hov⟩ :=
    hs_run js f hj hW hB hXv hFv
  have hT : W / 64 ≤ W := Nat.div_le_self _ _
  obtain ⟨σ1, r1, ho11, ho1, hv1, ha1, -, hout1⟩ := chkE_run (B := W + 1) (σ := σS)
    (e := .add (.var "nx") (.lit 1)) (v := (toWord js).length + 1) (by omega)
    (by simp [hnxS]; omega) (by rw [hTS]; omega) hov1
  obtain ⟨σ2, r2, ho21, ho2, hv2, ha2, -, hout2⟩ := chkE_run (B := W + 1) (σ := σ1)
    (e := .add (.var "fl") (.lit 2)) (v := (fr js f j).length + 2) (by omega)
    (by simp [hv1 "fl" (by decide), hflS]; omega) (by rw [hv1 "T" (by decide), hTS]; omega) ho11
  have hT2 : σ2.vars "T" = W / 64 := by rw [hv2 "T" (by decide), hv1 "T" (by decide), hTS]
  obtain ⟨σ3, r3, ho3⟩ := out_run (W := W) js f hj σ2 (by rw [ha2, ha1, hxS]) (by rw [ha2, ha1, hfS])
    (by rw [hv2 "nx" (by decide), hv1 "nx" (by decide), hnxS])
    (by rw [hv2 "jj" (by decide), hv1 "jj" (by decide), hjjS])
    (by rw [hv2 "fl" (by decide), hv1 "fl" (by decide), hflS]) hB hXv hFv
  have hnw : "ovf" ∉ outCmd.wvars := by
    simp [outCmd, outCall, wrF, findJob, wrJob, forUp, Com.wvars]
  refine ⟨σ3, _, Run.seq rS (Run.seq (Run.seq r1 r2) r3), ?_, ?_, ?_⟩
  · rw [ho3, hout2, hout1, hoS]; simp
  · simp only [Expr.size]; omega
  · rw [r3.frame_var "ovf" hnw, ho2, ho1, hov, hv1 "T" (by decide), hTS]
    unfold Checks
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h3, h4, h1, h2⟩
    · rintro ⟨h3, h4, h1, h2⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

end Lax185574Proofs.JobMap
