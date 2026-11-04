import Lax185574Proofs.MC.Brute.Pre
import Lax185574Proofs.Words.GuardedSound
import Lax185574Proofs.MC.Asm.Defs

/-!
The brute-force thread of thm:mc.

`bruteProg` reads an input word of thm:mc (the graph in compressed
sparse row form, the word of a construction script and the prefix code
of a sentence `φ`), builds the adjacency matrix, skips the script, and
runs the evaluation machine of `MC/Brute/Machine` on the code of `φ`.
It writes `1` and then the truth value of `G ⊨ φ`. It is the guarded
program of the command `bruteCmd`, whose values all stay below `W` as
soon as `(|x| + 2)² ≤ W`.

`bruteSpec` is the statement `BruteSpec` that the assembly of thm:mc
uses: at every word length admissible for `|x|` and the entries of `x`
with exponent `2`, every halting run outputs `1 :: mcAns G φ`, and some
run halts within `c · (|x| + 1) · (n + 1) ^ (rank φ + 1)` steps. No
construction sequence is assumed, only the encoding.
-/

namespace Lax185574Proofs.MC.Brute

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.MainRam Lax185574Proofs.Compose Lax271696.GraphEncoding
open Lax3.FirstOrder Lax185574.InstanceEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.ConstructionModelChecking Lax185574Proofs.MC
open Classical

/-- The initial configuration of the machine. -/
def bInit : Com :=
  .seq (.assign "bfm" (.lit 1)) (.seq (.assign "bfp" (.lit 0)) (.seq (.assign "bfb" (.lit 0))
    (.seq (.assign "bfs" (.lit 0)) (.assign "bfd" (.lit 0)))))

/-- The brute-force command. -/
def bruteCmd : Com :=
  .seq preCmd (.seq bInit (.seq bfLoop (.seq (.write (.lit 1)) (.write (.var "bfb")))))

/-- The scalars and arrays of `bruteCmd`. -/
def bLayout : Layout :=
  ⟨["W", "ovf", "n", "E", "cnt", "i", "v", "a", "j", "hi", "bfn", "bfi", "bfx", "bfy", "bfl", "bfr",
    "bfo", "bfq", "bfm", "bfp", "bfb", "bfs", "bfd", "bft", "bfv"],
    ["of", "tg", "A", "bfA", "bfc", "bfe", "bfk", "bfa", "bfw", "bfg"], 8⟩

/-- The brute-force program. -/
def bruteProg : Program := guardedProgram bLayout bruteCmd

theorem bruteCmd_ok : Com.Ok bLayout bruteCmd := by
  simp [bruteCmd, preCmd, grBody, readArr, adjPh, adjRow, adjBody, cpA, forUp, skipSeq, skipLoop, rdK,
    rdFml, rdBody, rdOp, endsCmd, endBody, bInit, bfLoop, bfCond, bfStep, evalStep, retStep, retEx,
    pushF, bLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem bruteCmd_run {n : ℕ} {G : SimpleGraph (Fin n)}
    {s : List (Lax185574.PartialGraphs.PartialGraph (Fin n))} {φ : FO 0} {g y : List ℕ}
    (hg : EncodesGraph g n G) (hy : EncodesSequence y s) {B W : ℕ}
    (hB : B = W + 1) (hxW : ∀ v ∈ g ++ y ++ code φ, v ≤ W)
    (hfit : ((g ++ y ++ code φ).length + 2) ^ 2 ≤ W) :
    ∃ σ', Run B bruteCmd ((initEnv (bExt n (edgeCount g) B) (g ++ y ++ code φ)).setVar "W" W) σ'
      (400 * (n * n + (g ++ y ++ code φ).length) + 110 * bsteps n φ + 400) ∧
      σ'.vars "ovf" = 0 ∧ σ'.out = 1 :: mcAns G φ := by
  set X := (g ++ y ++ code φ).length with hXd
  have hLX : (code φ).length ≤ X := by simp [X]
  have hX3 : 3 ≤ X := by have := hg.length_eq; simp [X]; omega
  have hXW : X + 6 ≤ W := by nlinarith
  have hnX : n ≤ X := by have := hg.length_eq; simp [X]; omega
  have hnB : n * n < B := by nlinarith
  obtain ⟨σA, rA, hP⟩ := pre_run hg hy hB hxW hfit
  have hnw : preCmd.NoWrite := by
    simp [preCmd, grBody, readArr, adjPh, adjRow, adjBody, cpA, forUp, skipSeq, skipLoop, rdK, rdFml,
      rdBody, rdOp, endsCmd, endBody, Com.NoWrite]
  have hoA : σA.out = [] := by rw [rA.out_eq hnw]; rfl
  set σB := ((((σA.setVar "bfm" 1).setVar "bfp" 0).setVar "bfb" 0).setVar "bfs" 0).setVar "bfd" 0
  have rB : Run B bInit σA σB 15 := by
    unfold bInit
    exact (Run.seq (Run.assign (by simp; omega)) (Run.seq (Run.assign (by simp; omega))
      (Run.seq (Run.assign (by simp; omega)) (Run.seq (Run.assign (by simp; omega))
        (Run.assign (by simp; omega)))))).mono (by simp)
  have hstk : ∀ a ∈ ["bfk", "bfa", "bfw", "bfg"], σB.arrs a = List.replicate B 0 := by
    intro a ha; simp only [σB, arrs_setVar]; exact hP.stk a ha
  have hrep : BRep B n ⟨true, 0, false, [], []⟩ σB :=
    ⟨by simp [σB, hP.hn], by simp [σB], by simp [σB], by simp [σB], by simp [σB], by simp [σB],
      by rw [hstk _ (by simp)]; simp, by rw [hstk _ (by simp)]; simp,
      by rw [hstk _ (by simp)]; simp, by rw [hstk _ (by simp)]; simp,
      fun i h => by simp at h, fun i h => by simp at h, fun i h => by simp at h,
      fun i => by rw [hstk _ (by simp)]; simp [replicate_getD]⟩
  have hdat : BData B σB := ⟨by simpa [σB] using hP.lc, by simpa [σB] using hP.le,
    by simpa [σB] using hP.lA,
    fun i => by
      simp only [σB, arrs_setVar]; rw [hP.cd i]
      exact code_getD_lt (fun v hv => by have := hxW v (by simp [hv]); omega) (by omega) i,
    fun i => by simpa [σB] using hP.ve i, fun i => by simpa [σB] using hP.vA i⟩
  have hcd : CodeAt (cdOf σB) 0 (code φ) := fun j _ => by
    simp only [cdOf, σB, arrs_setVar, Nat.zero_add]; exact hP.cd j
  have hfe : FeOK (cdOf σB) (feOf σB) φ 0 := by
    have h := feOK_of_good hP.good φ 0 (fun j _ => by rw [Nat.zero_add]; exact hP.cd j) (by omega)
    exact h
  have hA : ∀ u v : Fin n, adjOf σB n u v = decide (G.Adj u v) := fun u v => by
    have := hP.adj u v; simpa [adjOf, σB] using this
  obtain ⟨σC, rC, hbC⟩ := eval_run G φ (τ := σB) (by omega) hnB hrep hdat hcd hfe hA
  have hoC : σC.out = [] := by
    rw [rC.out_eq (by simp [bfLoop, bfStep, evalStep, retStep, retEx, pushF, Com.NoWrite])]
    simp [σB, hoA]
  have hovC : σC.vars "ovf" = 0 := by
    rw [rC.frame_var "ovf" (by simp [bfLoop, bfStep, evalStep, retStep, retEx, pushF, Com.wvars])]
    simp [σB, hP.hov]
  have hbB : σC.vars "bfb" < B := by rw [hbC]; split <;> omega
  refine ⟨{ { σC with out := σC.out ++ [1] } with out := σC.out ++ [1] ++ [σC.vars "bfb"] }, ?_,
    hovC, ?_⟩
  · unfold bruteCmd
    refine (Run.seq rA (Run.seq rB (Run.seq rC (Run.seq (Run.write (v := 1) (by simp; omega))
      (Run.write (v := σC.vars "bfb") (by simpa using hbB)))))).mono ?_
    simp only [size_lit, size_var]
    omega
  · simp only [hoC, List.nil_append, hbC, mcAns]
    split <;> rfl

theorem two_pow_le {r w Y : ℕ} (hY : 1 ≤ Y) (h : 2 ^ (r + 3) * Y ≤ 2 ^ w) :
    r + 3 ≤ w ∧ 8 * Y ≤ 2 ^ (w - r) := by
  have hw : r + 3 ≤ w := by
    by_contra hc
    have : 2 ^ w < 2 ^ (r + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := Nat.le_mul_of_pos_right (2 ^ (r + 3)) hY
    omega
  refine ⟨hw, ?_⟩
  have e1 : 2 ^ w = 2 ^ r * 2 ^ (w - r) := by rw [← pow_add]; congr 1; omega
  have e2 : 2 ^ (r + 3) = 2 ^ r * 8 := by rw [pow_add]; norm_num
  rw [e1, e2, mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (by positivity)

theorem time_le (n X L r : ℕ) (hn : n ≤ X) (hL : L ≤ X) :
    400 * (n * n + X) + 110 * (3 * L * (n + 1) ^ r) + 400 ≤ 1500 * ((X + 1) * (n + 1) ^ (r + 1)) := by
  have h1 : 1 ≤ (n + 1) ^ r := Nat.one_le_pow _ _ (by omega)
  have h2 : n * n ≤ X * (n + 1) := Nat.mul_le_mul hn (by omega)
  have e : (X + 1) * (n + 1) ^ (r + 1) = (X + 1) * (n + 1) * (n + 1) ^ r := by ring
  rw [e]
  have h3 : L * (n + 1) ^ r ≤ (X + 1) * (n + 1) * (n + 1) ^ r := by
    apply Nat.mul_le_mul_right; nlinarith
  have h4 : X * (n + 1) ≤ (X + 1) * (n + 1) * (n + 1) ^ r := by nlinarith
  have h5 : X + 1 ≤ (X + 1) * (n + 1) * (n + 1) ^ r := by nlinarith
  nlinarith

/-- **The brute-force thread.** `bruteProg` satisfies the interface
`BruteSpec` of the assembly of thm:mc, with exponent `2`. -/
theorem bruteSpec : BruteSpec bruteProg := by
  set r := guardBits bLayout
  refine ⟨2, fun φ => ⟨2 ^ (r + 3) * (bLayout.const * 1500 + 5), rank φ + 1, ?_⟩⟩
  intro n G s x w hx hadm
  obtain ⟨g, y, hg, hy, rfl⟩ := hx
  rw [Lax185574Proofs.Legacy.encode_eq_foCode] at hadm ⊢
  set X := (g ++ y ++ code φ).length with hXd
  have hgl := hg.length_eq
  have hne : g ++ y ++ code φ ≠ [] := by
    intro h; have := congrArg List.length h
    simp only [List.length_append, List.length_nil] at this; omega
  obtain ⟨v₀, hv₀⟩ := List.exists_mem_of_ne_nil _ hne
  have hc1 : 1 ≤ bLayout.const * 1500 + 5 := by omega
  -- the word length
  have hadm' : ∀ v ∈ g ++ y ++ code φ, 2 ^ (r + 3) * (X + v + 1) ^ 2 ≤ 2 ^ w := by
    intro v hv
    have := hadm v hv
    calc 2 ^ (r + 3) * (X + v + 1) ^ 2 ≤ 2 ^ (r + 3) * (bLayout.const * 1500 + 5) * (X + v + 1) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
      _ ≤ 2 ^ w := this
  obtain ⟨hw, hX8⟩ := two_pow_le (Nat.one_le_pow _ _ (by omega)) (hadm' v₀ hv₀)
  set W := guardW bLayout w with hWd
  have hW1 : W + 1 = 2 ^ (w - r) := guardW_succ bLayout w
  have hfit : (X + 2) ^ 2 ≤ W := by
    have : (X + 1) ^ 2 ≤ (X + v₀ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hxW : ∀ v ∈ g ++ y ++ code φ, v ≤ W := by
    intro v hv
    obtain ⟨-, h⟩ := two_pow_le (Nat.one_le_pow _ _ (by omega)) (hadm' v hv)
    have : v + 1 ≤ (X + v + 1) ^ 2 := by nlinarith
    omega
  -- the run of the command
  obtain ⟨σ', hrun, hov, hout⟩ := bruteCmd_run (B := W + 1) (W := W) hg hy rfl hxW hfit
  obtain ⟨hsound, hfwd⟩ := guarded_sound bruteCmd_ok (by simp [bLayout]) (by simp [bLayout])
    (show guardBits bLayout + 2 ≤ w by omega) hxW hrun
  refine ⟨fun z t h => by rw [(hsound z t h).2, hout], ?_⟩
  obtain ⟨t, ht, hR⟩ := hfwd hov
  refine ⟨t, ?_, by rw [← hout]; exact hR⟩
  have hb := bsteps_le n φ
  have hL : (code φ).length ≤ X := by
    show (code φ).length ≤ (g ++ y ++ code φ).length; simp; omega
  have hn : n ≤ X := by simp [X]; omega
  have := time_le n X (code φ).length (rank φ) hn hL
  have hk : 400 * (n * n + X) + 110 * bsteps n φ + 400 ≤ 1500 * ((X + 1) * (n + 1) ^ (rank φ + 1)) := by
    have : 110 * bsteps n φ ≤ 110 * (3 * (code φ).length * (n + 1) ^ rank φ) :=
      Nat.mul_le_mul_left _ hb
    omega
  have h1 : 1 ≤ (X + 1) * (n + 1) ^ (rank φ + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : 1 ≤ 2 ^ (r + 3) := Nat.one_le_two_pow
  calc t ≤ bLayout.const * (400 * (n * n + X) + 110 * bsteps n φ + 400) + 5 := ht
    _ ≤ bLayout.const * (1500 * ((X + 1) * (n + 1) ^ (rank φ + 1))) + 5 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) _
    _ ≤ (bLayout.const * 1500 + 5) * ((X + 1) * (n + 1) ^ (rank φ + 1)) := by nlinarith
    _ ≤ 2 ^ (r + 3) * (bLayout.const * 1500 + 5) * ((X + 1) * (n + 1) ^ (rank φ + 1)) := by
        rw [mul_assoc (2 ^ (r + 3))]; exact Nat.le_mul_of_pos_left _ (by positivity)
    _ = 2 ^ (r + 3) * (bLayout.const * 1500 + 5) * (X + 1) * (n + 1) ^ (rank φ + 1) := by ring

end Lax185574Proofs.MC.Brute
