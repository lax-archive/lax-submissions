import Lax185574Proofs.FarRam.Script
import Lax185574Proofs.LoopGlue


/-!
The rounds of the far-tree program, compiled: the glue program halts with
the state of the script, and every halting run has this output.
-/

namespace Lax185574Proofs.FarRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574Proofs.Simulate Lax185574Proofs.RamSim Lax185574Proofs.EvalRam Lax185574Proofs.ShiftRam
open Lax3.DistFO (rhoMinus)

def layout : Layout :=
  ⟨["sl", "vv", "ev", "xp", "e3", "z0", "n", "tg", "ye", "tw", "n0", "jr", "nw", "ow", "cl", "i", "ze",
    "ru", "s2", "zb", "zc", "zv", "rh", "rr", "s1", "zr", "zi", "e1", "e2", "r0", "hs", "hi", "hj", "hy",
    "op", "y", "m", "al", "p", "fr", "j", "v", "zj", "zf", "ef", "zt", "pb", "lb", "c", "nR", "hl", "zx",
    "zw", "zp", "zy", "zu", "zq", "zbb", "rho", "hk", "hq", "zn", "zk", "zo", "zl", "sv", "zm", "ns",
    "la", "pa", "k", "zs"], ["f", "x", "far", "eqa", "mt", "bt", "sel", "st", "ln", "a"], 6⟩

theorem glue_ok : Com.Ok layout glue := by
  simp [glue, headCmd, tailCmd, readHdr, readTree, cpList, cpFrame, cpEntries, cpEntry, tailPre,
    readWords, readWord, readEntries, readEntry, locate, skipList, skipBody, emitCall, sumLn, findFr,
    writes, wFrames, writeWord, writeEntry, wChild2, finalCmd, radPhase, powLoop, findLoop, radBody,
    canonFill, canonBody, canonTest, hitC, atScan, atBody, atMatch, atLast, badOuter, badInner, badTest,
    anyLoop, extPhase, extBody, extInner, scanSel, selBody, eqFill, eqBody, cmpStep, entA, entB, inNC,
    inNTest, andTest, cntC, cntBody, blkTest, mbTest, hdrSel, outPhase, cntSel, outBody, writeNu, forUp,
    layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-- The compiled glue program. -/
def glueProg : Program := compileProgram layout glue

def lsz : ℕ := layout.temps + 2 + layout.scalars.length + layout.arrays.length + 1

theorem lsz_eq : lsz = 91 := rfl

/-- The array lengths of a round. -/
def gExt {q ℓ : ℕ} (t : Node (q + 1) ℓ) (W : List (List ℕ)) (nS : ℕ) : String → ℕ := fun a =>
  if a = "x" then (toWord t).length else if a = "f" then 4 else
    total W + W.length + ℓ + (Node.exts t).words.length * ℓ + (Node.exts t).words.length + nS

theorem gExt_ok {q ℓ : ℕ} (t : Node (q + 1) ℓ) (W : List (List ℕ)) (nS : ℕ) :
    ExtOK t W nS (gExt t W nS) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [gExt] <;> omega

theorem gExt_X {q ℓ : ℕ} (t : Node (q + 1) ℓ) (W : List (List ℕ)) (nS : ℕ) :
    toWord t ++ (List.replicate (gExt t W nS "x") 0).drop (toWord t).length = toWord t := by
  simp [gExt]

/-- The input of a round. -/
def gIn {q ℓ : ℕ} (tg sl k : ℕ) (t : Node (q + 1) ℓ) (hdr : List ℕ) (W : List (List ℕ)) (rin : List ℕ) :
    List ℕ := [tg, sl, k, q + 1, ℓ] ++ toWord t ++ hdr ++ toWord W ++ rin

/-- The facts every bound of a round follows from. -/
structure GBnd {q ℓ : ℕ} (tg sl k : ℕ) (t : Node (q + 1) ℓ) (hdr : List ℕ) (W : List (List ℕ))
    (rin : List ℕ) (nS j B : ℕ) : Prop where
  case : (tg = 0 ∧ hdr = [] ∧ j = 0 ∧ nS = W.length) ∨ (tg = 1 ∧ hdr = [0, j, nS])
  big : ((gIn tg sl k t hdr W rin).length + maxEntry (gIn tg sl k t hdr W rin) + 10) ^ 2 ≤ B

section Bnd

variable {q ℓ : ℕ} {tg sl k : ℕ} {t : Node (q + 1) ℓ} {hdr : List ℕ} {W : List (List ℕ)}
  {rin : List ℕ} {nS j B : ℕ}

theorem GBnd.mem (h : GBnd tg sl k t hdr W rin nS j B) {y : ℕ} (hy : y ∈ gIn tg sl k t hdr W rin) :
    y + (gIn tg sl k t hdr W rin).length + 10 ≤ B := by
  have h1 := le_maxEntry hy
  have h2 := h.big
  nlinarith

theorem GBnd.len (h : GBnd tg sl k t hdr W rin nS j B) :
    (gIn tg sl k t hdr W rin).length + maxEntry (gIn tg sl k t hdr W rin) + 10 ≤ B := by
  have h2 := h.big; nlinarith

theorem GBnd.facts (h : GBnd tg sl k t hdr W rin nS j B) :
    (∀ v ∈ toWord t, v + (toWord t).length + 10 ≤ B) ∧ (toWord t).length + 10 ≤ B ∧ sl + 10 ≤ B ∧
      k + q + ℓ + 12 ≤ B ∧ j + nS + 10 ≤ B ∧ (∀ v ∈ toWord W, v + 10 ≤ B) ∧
      (toWord W).length + 10 ≤ B ∧ tg + 10 ≤ B ∧
      (toWord t).length + nS + k + q + ℓ + 10 ≤ B ∧
      (Node.exts t).words.length * ℓ + ℓ + nS + (Node.exts t).words.length + 2 < B ∧
      (Node.exts t).words.length ≤ (toWord t).length := by
  set u := gIn tg sl k t hdr W rin with hu
  have hmem : ∀ y, y ∈ u → y + u.length + 10 ≤ B := fun y hy => h.mem hy
  have hL := h.len
  have hlt : (toWord t).length + hdr.length + (toWord W).length + 5 ≤ u.length := by simp [u, gIn]; omega
  have hk := hmem k (by simp [u, gIn])
  have hq := hmem (q + 1) (by simp [u, gIn])
  have hl := hmem ℓ (by simp [u, gIn])
  have hs := hmem sl (by simp [u, gIn])
  have htg := hmem tg (by simp [u, gIn])
  have h2M : 2 * (u.length + maxEntry u) + 20 ≤ B := by have := h.big; nlinarith
  have hjn : j + nS + 10 ≤ B := by
    rcases h.case with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl⟩
    · have := length_toWord_words W; simp at hlt; omega
    · have h1 := le_maxEntry (x := u) (v := j) (by simp [u, gIn])
      have h2 := le_maxEntry (x := u) (v := nS) (by simp [u, gIn])
      omega
  have hR : (Node.exts t).words.length ≤ (toWord t).length := by
    have := length_toWord_words (Node.exts t).words
    rw [toWord_node_succ, List.length_append]; omega
  have hlM : ℓ ≤ maxEntry u := le_maxEntry (by simp [u, gIn])
  have hRl : (Node.exts t).words.length * ℓ ≤ u.length * maxEntry u :=
    Nat.mul_le_mul (by omega) hlM
  have hbig := h.big
  have h5M : 5 * (u.length + maxEntry u) + 20 ≤ B := by nlinarith
  have hkM : k ≤ maxEntry u := le_maxEntry (by simp [u, gIn])
  have hqM : q + 1 ≤ maxEntry u := le_maxEntry (by simp [u, gIn])
  have hnM : nS ≤ u.length + maxEntry u := by
    rcases h.case with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl⟩
    · have := length_toWord_words W; simp at hlt; omega
    · have := le_maxEntry (x := u) (v := nS) (by simp [u, gIn]); omega
  refine ⟨fun v hv => by have := hmem v (by simp [u, gIn, hv]); omega, by omega, by omega, by omega,
    hjn, fun v hv => by have := hmem v (by simp [u, gIn, hv]); omega, by omega, by omega, by omega,
    by nlinarith, hR⟩

end Bnd

def headCost {q ℓ : ℕ} (t : Node (q + 1) ℓ) : ℕ := 48 * (toWord t).length + 60

/-- **A call round, compiled.** -/
theorem g_call {v B : ℕ} {q ℓ : ℕ} (t : Node (q + 1) ℓ) (k : ℕ) (W : List (List ℕ)) (nS j tg sl : ℕ)
    (hdr rin : List ℕ) (h : GBnd tg sl k t hdr W rin nS j B) (hj : j < (Node.exts t).words.length)
    (hS : lsz * B ≤ 2 ^ v) :
    (∃ tm ≤ layout.const * (headCost t + preCost W (toWord t) + callCost W (toWord t) j + 10) + 1,
      RunsTo v glueProg (gIn tg sl k t hdr W rin)
        ([1, 4 + W.length + total W, (toWord t).length + 3, 0, j + 1, nS, W.length + 1] ++ frames W ++
          queryW k t j) tm) ∧
    ∀ o tm, RunsTo v glueProg (gIn tg sl k t hdr W rin) o tm →
      o = [1, 4 + W.length + total W, (toWord t).length + 3, 0, j + 1, nS, W.length + 1] ++ frames W ++
        queryW k t j := by
  obtain ⟨hv, htl, hsl, hkq, hjn, hWv, hWl, htg, hsum, -, -⟩ := h.facts
  obtain ⟨σ1, r1, hT1, ho1⟩ := head_run B (gExt t W nS) tg sl k q ℓ t hdr W nS j rin (gExt_ok t W nS) h.case
    (fun y hy => by have := hv y hy; omega) (by omega) (by omega) (by omega) (by omega)
  rw [gExt_X] at hT1
  have hWb : WordsBound B W := ⟨by have := length_toWord_words W; omega,
    fun w hw x hx => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      have := hWv x ((mem_toWord_words hi).2 x hx); omega, by omega⟩
  obtain ⟨σ2, r2, a, ha, haw, ho2⟩ := tail_call B (toWord t) t [] (by simp) k W nS j rin σ1 hT1 hj
    (fun y hy => by have := hv y hy; omega) (by omega) hWb (by omega)
    (fun y hy => by have := hWv y hy; omega) (by omega)
  have hq : [k + 1, q, ℓ + 1] ++ toWord a.2 ++ [1, ℓ] = queryW k t j := by
    have hc : childW t j = toWord a.2 := by
      rw [childW, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simp only [Option.getD_some, ← haw, toWord_ext, List.tail_cons]
    rw [queryW, hc]
  have hrun : Run B glue (initEnv (gExt t W nS) (gIn tg sl k t hdr W rin)) σ2
      (headCost t + preCost W (toWord t) + callCost W (toWord t) j + 10) :=
    (Run.seq r1 r2).mono (by simp only [headCost]; omega)
  have hout : σ2.out = [1, 4 + W.length + total W, (toWord t).length + 3, 0, j + 1, nS, W.length + 1] ++
      frames W ++ queryW k t j := by
    rw [ho2, ho1, ← hq]; simp
  obtain ⟨h1, h2⟩ := glue_runsTo glue_ok (B := B) (v := v) (hrun := hrun) (by omega) hS
    (fun y hy => by have := h.mem hy; omega)
  rw [hout] at h1 h2
  exact ⟨h1, h2⟩

/-- **The last round, compiled.** -/
theorem g_final {v B : ℕ} {q ℓ : ℕ} (t : Node (q + 1) ℓ) (k : ℕ) (W : List (List ℕ)) (nS tg sl : ℕ)
    (hdr rin : List ℕ) (h : GBnd tg sl k t hdr W rin nS (Node.exts t).words.length B)
    (hWl : W.length = nS + (Node.exts t).words.length) (h3 : ∀ j < nS, 3 ≤ (wd W j).length)
    (hD : 4 * (9 ^ (ℓ - 1) * rhoMinus (k + 1) q) + 2 * rhoMinus (k + 1) q + (k + (q + 1) + 1) * q + 20 ≤ B)
    (hS : lsz * B ≤ 2 ^ v) :
    (∃ tm ≤ layout.const * (headCost t + preCost W (toWord t) +
        finalCost (toWord t) W k q ℓ nS (Node.exts t).words.length + 10) + 1,
      RunsTo v glueProg (gIn tg sl k t hdr W rin)
        (0 :: toWord (farList (toWord t) (W.drop nS) k q ℓ (W.take nS))) tm) ∧
    ∀ o tm, RunsTo v glueProg (gIn tg sl k t hdr W rin) o tm →
      o = 0 :: toWord (farList (toWord t) (W.drop nS) k q ℓ (W.take nS)) := by
  obtain ⟨hv, htl, hsl, hkq, hjn, hWv, hWl', htg, hsum, hNB, -⟩ := h.facts
  obtain ⟨σ1, r1, hT1, ho1⟩ := head_run B (gExt t W nS) tg sl k q ℓ t hdr W nS _ rin (gExt_ok t W nS)
    h.case (fun y hy => by have := hv y hy; omega) (by omega) (by omega) (by omega) (by omega)
  rw [gExt_X] at hT1
  have hWb : WordsBound B W := ⟨by have := length_toWord_words W; omega,
    fun w hw x hx => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      have := hWv x ((mem_toWord_words hi).2 x hx); omega, by omega⟩
  obtain ⟨σ2, r2, ho2⟩ := tail_final B (toWord t) t [] (by simp) k W nS rin σ1 hT1 hWl h3 hWb
    (fun y hy => by have := hv y hy; omega) (by omega) (by omega)
    (fun y hy => by have := hWv y hy; omega) (by omega) (by omega) (by omega) (by omega) hNB
  have hrun : Run B glue (initEnv (gExt t W nS) (gIn tg sl k t hdr W rin)) σ2
      (headCost t + preCost W (toWord t) + finalCost (toWord t) W k q ℓ nS (Node.exts t).words.length + 10) :=
    (Run.seq r1 r2).mono (by simp only [headCost]; omega)
  have hout : σ2.out = 0 :: toWord (farList (toWord t) (W.drop nS) k q ℓ (W.take nS)) := by
    rw [ho2, ho1]; simp
  obtain ⟨h1, h2⟩ := glue_runsTo glue_ok (B := B) (v := v) (hrun := hrun) (by omega) hS
    (fun y hy => by have := h.mem hy; omega)
  rw [hout] at h1 h2
  exact ⟨h1, h2⟩

end Lax185574Proofs.FarRam
