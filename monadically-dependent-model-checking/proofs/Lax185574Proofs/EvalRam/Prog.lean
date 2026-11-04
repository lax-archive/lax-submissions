import Lax185574Proofs.EvalRam.Row
import Lax185574Proofs.Words.TreeMap
import Lax185574Proofs.Words.Computes

/-!
The evaluation program and its reading phase.

The program reads the tree and copies the word of its root into an
array, reads the code of the formula into a second array, and lists the
nodes of the tree in breadth-first order. It then fills a table with one
row for every position of the code and one column for every node: the
entry of a position where a subformula starts is the value of the
subformula at the node. The rows are filled from the last position to the
first, so that the subformulas of a formula are evaluated before it. The
answer is the entry of the first position at the root.
-/

namespace Lax185574Proofs.EvalRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

/-- The reading phase: the tree, the formula, and the list of nodes. -/
def readPhase : Com := .seq readTree (.seq readFml bfs)

/-- The evaluation program, in IMP+. -/
def prog : Com := .seq readPhase (.seq dpCmd (.write (.get "val" (.lit 0))))

/-- The scalars and arrays of `prog`. -/
def layout : Lax808846Proofs.Compile.Layout :=
  ⟨["hk", "hq", "hl", "xp", "e1", "e2", "e3", "vv", "ev", "fl", "pd", "w", "op", "na", "rj", "nn", "u",
    "y", "dd", "k", "p", "c", "hh", "v", "al", "m", "fr", "j", "ch", "ee"],
    ["x", "f", "pos", "dep", "fc", "en", "val"], 8⟩

theorem prog_ok : Lax808846Proofs.Compile.Com.Ok layout prog := by
  simp [prog, readPhase, readTree, cpList, cpFrame, cpEntries, cpEntry, readFml, fmlBody, rdOne, setNa, setPd,
    forUp, bfs, bfsBody, skipList, skipBody, pushList, pushBody, dpCmd, rowBody, endCmd, endSel,
    cellCmd, opCmd, atScan, atBody, atMatch, atLast, notCmd, andCmd, nextIdx, sndIdx, exCmd, exScan,
    exBody, chIdx, layout, Lax808846Proofs.Compile.Com.Ok, Lax808846Proofs.Compile.Cond.Ok,
    Lax808846Proofs.Compile.condExpr, Lax808846Proofs.Compile.Expr.Ok]

/-- The array lengths of `prog` on an input of length `n`. -/
def evalExt (n : ℕ) : String → ℕ := fun a =>
  if a = "x" then n + 1
  else if a = "f" ∨ a = "en" then n + 5
  else if a = "pos" ∨ a = "dep" ∨ a = "fc" then n + 2
  else if a = "val" then (n + 5) * (n + 2)
  else 0

theorem readFml_noWrite : readFml.NoWrite := by
  simp [readFml, fmlBody, rdOne, setNa, setPd, forUp, Com.NoWrite]

theorem dpCmd_noWrite : dpCmd.NoWrite := by
  simp [dpCmd, rowBody, endCmd, endSel, cellCmd, opCmd, atScan, atBody, atMatch, atLast, notCmd,
    andCmd, exCmd, exScan, exBody, skipList, skipBody, forUp, Com.NoWrite]

/-- The input word: the header, the root of the tree, the code of the
formula. -/
def inWord (k q ℓ : ℕ) (t : Node q ℓ) (φ : DistFO ℓ) : List ℕ := [k, q, ℓ] ++ toWord t ++ code φ

/-- The contents of `x` after reading: the root word, padded with zeros. -/
def xArr {q ℓ : ℕ} (t : Node q ℓ) (n : ℕ) : List ℕ :=
  toWord t ++ (List.replicate (n + 1) 0).drop (toWord t).length

/-- The contents of `f` after reading: the code, padded with zeros. -/
def fArr {ℓ : ℕ} (φ : DistFO ℓ) (n : ℕ) : List ℕ :=
  code φ ++ (List.replicate (n + 5) 0).drop (code φ).length

/-- What the reading phase leaves. -/
structure ReadOut (k q ℓ : ℕ) (t : Node q ℓ) (φ : DistFO ℓ) (σ : Env) : Prop where
  x_eq : σ.arrs "x" = xArr t (inWord k q ℓ t φ).length
  f_eq : σ.arrs "f" = fArr φ (inWord k q ℓ t φ).length
  hq_eq : σ.vars "hq" = q
  fl_eq : σ.vars "fl" = (code φ).length
  en_eq : σ.arrs "en" = List.replicate ((inWord k q ℓ t φ).length + 5) 0
  val_eq : σ.arrs "val" = List.replicate (((inWord k q ℓ t φ).length + 5) * ((inWord k q ℓ t φ).length + 2)) 0
  out_eq : σ.out = []
  nn_le : σ.vars "nn" ≤ (inWord k q ℓ t φ).length + 2
  nn_pos : 0 < σ.vars "nn"
  pos_zero : xg (σ.arrs "pos") 0 = 0
  dep_zero : xg (σ.arrs "dep") 0 = 0
  pos_len : (σ.arrs "pos").length = (inWord k q ℓ t φ).length + 2
  dep_len : (σ.arrs "dep").length = (inWord k q ℓ t φ).length + 2
  fc_len : (σ.arrs "fc").length = (inWord k q ℓ t φ).length + 2
  nodes : ∀ c < σ.vars "nn", NodeOK (xArr t (inWord k q ℓ t φ).length) (σ.arrs "pos") (σ.arrs "dep")
    (σ.arrs "fc") q (σ.vars "nn") c

set_option maxHeartbeats 1000000 in
/-- **The reading phase.** -/
theorem readPhase_run (k q ℓ : ℕ) (t : Node q ℓ) (φ : DistFO ℓ) :
    ∃ σ', Run (valBound 8 2 (inWord k q ℓ t φ)) readPhase
      (initEnv (evalExt (inWord k q ℓ t φ).length) (inWord k q ℓ t φ)) σ'
      (400 * ((inWord k q ℓ t φ).length + 1) ^ 2) ∧ ReadOut k q ℓ t φ σ' := by
  set x := inWord k q ℓ t φ with hxdef
  obtain ⟨n, hn⟩ : ∃ n, x.length = n := ⟨_, rfl⟩
  rw [hn]
  set B := valBound 8 2 x with hB
  set M := maxEntry x with hM
  have hBdef : B = 8 * (x.length + M + 1) ^ 2 := rfl
  rw [hn] at hBdef
  have hmem : ∀ v ∈ x, v < B := fun v hv => by
    have := le_maxEntry hv; rw [hBdef]; nlinarith
  have htl : (toWord t).length + (code φ).length + 3 = n := by rw [← hn, hxdef]; simp [inWord] <;> omega
  have hL1 := one_le_code_length φ
  have htne := List.length_pos_iff.mpr (toWord_node_ne_nil t)
  have hn4 : 5 ≤ n := by omega
  have hBn : (n + 5) * (n + 2) + 10 < B := by rw [hBdef]; nlinarith
  have hnB : n + 10 < B := by nlinarith
  have hqB : q < B := hmem q (by simp [hxdef, inWord])
  have hqB1 : q + 1 < B := by
    have := le_maxEntry (show q ∈ x by simp [hxdef, inWord]); rw [hBdef]; nlinarith
  set ext := evalExt n with hext
  set σ0 := initEnv ext x with hσ0
  -- reading the tree
  set O := List.replicate (n + 1) 0 with hO
  obtain ⟨σ1, hr1, hk1, hq1, hl1, hx1, hinp1⟩ := readTree_spec B k q ℓ t (code φ) O
    (by simp [hO]; omega) (by omega) (fun v h => hmem v (by simp [hxdef, inWord, h])) hqB σ0
    ⟨by simp [hσ0, initEnv, hxdef, inWord], by simp [hσ0, initEnv, hext, evalExt, hO]⟩
  set X := toWord t ++ O.drop (toWord t).length with hX
  have hXl : X.length = n + 1 := by simp [hX, hO]; omega
  have hXv : ∀ v ∈ X, v < B := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hmem v (by simp [hxdef, inWord, h])
    · rw [hO, List.drop_replicate] at h; rw [List.eq_of_mem_replicate h]; omega
  have hXt : X.drop 0 = toWord t ++ O.drop (toWord t).length := by simp [hX]
  -- reading the formula
  set OF := List.replicate (n + 5) 0 with hOF
  have ha1 : ∀ a, a ∉ readTree.warrs → σ1.arrs a = σ0.arrs a := fun a h => hr1.frame_arr a h
  obtain ⟨σ2, hr2, hfl2, hf2, hinp2⟩ := readFml_spec B φ OF [] (by simp [hOF]; omega)
    (fun v h => hmem v (by simp [hxdef, inWord, h])) (by omega) σ1
    ⟨by rw [hinp1]; simp, by
      rw [ha1 "f" (by decide)]
      simp [hσ0, initEnv, hext, evalExt, hOF]⟩
  set L := (code φ).length with hL
  set F := code φ ++ OF.drop L with hF
  have hFl : F.length = n + 5 := by simp [hF, hOF]; omega
  have hFv : ∀ v ∈ F, v < B := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hmem v (by simp [hxdef, inWord, h])
    · rw [hOF, List.drop_replicate] at h; rw [List.eq_of_mem_replicate h]; omega
  have hv2 : ∀ y, y ∉ readFml.wvars → σ2.vars y = σ1.vars y := fun y h => hr2.frame_var y h
  have ha2 : ∀ a, a ∉ readFml.warrs → σ2.arrs a = σ1.arrs a := fun a h => hr2.frame_arr a h
  have hinit : ∀ a, a ∉ readTree.warrs → a ∉ readFml.warrs → σ2.arrs a = List.replicate (ext a) 0 :=
    fun a h1 h2 => by rw [ha2 a h2, ha1 a h1]; rfl
  -- listing the nodes
  have hroot : NodeAt X 0 q := ⟨ℓ, t, _, hXt⟩
  have hL0 : nodeEnd X 0 q = (toWord t).length := by rw [nodeEnd_eq hXt]; simp
  obtain ⟨σ3, hr3, hI3, hun3⟩ := bfs_spec B X q (n + 2) (by omega) hXv (by omega) hroot (by rw [hL0]; omega) σ2
    ⟨by rw [ha2 "x" (by decide), hx1],
      by rw [hv2 "hq" (by decide), hq1],
      by rw [hinit "pos" (by decide) (by decide)]; simp [hext, evalExt],
      by rw [hinit "dep" (by decide) (by decide)]; simp [hext, evalExt],
      by rw [hinit "fc" (by decide) (by decide)]; simp [hext, evalExt]⟩
  obtain ⟨hx3, hq3, -, hn13, hsum3, hpl3, hdl3, hfl3, hnodes3, hscan3, hr03, hd03⟩ := hI3
  have hv3 : ∀ y, y ∉ bfs.wvars → σ3.vars y = σ2.vars y := fun y h => hr3.frame_var y h
  have ha3 : ∀ a, a ∉ bfs.warrs → σ3.arrs a = σ2.arrs a := fun a h => hr3.frame_arr a h
  set N := σ3.vars "nn" with hN
  set PA := σ3.arrs "pos" with hPA
  set DA := σ3.arrs "dep" with hDA
  set FA := σ3.arrs "fc" with hFA
  rw [hun3] at hscan3
  have hNX : N ≤ n + 2 := by rw [hL0] at hsum3; omega
  have hnodes : ∀ c < N, NodeOK X PA DA FA q N c := fun c hc =>
    ⟨(hnodes3 c hc).1, (hscan3 c hc).2.1, (hnodes3 c hc).2, (hscan3 c hc).2.2⟩
  have hfl3' : σ3.vars "fl" = L := by rw [hv3 "fl" (by decide), hfl2]
  have hXa : X = xArr t x.length := by rw [hn]; rfl
  refine ⟨σ3, ?_, ⟨?_, ?_, hq3, hfl3', ?_, ?_, ?_, by rw [← hxdef, hn]; exact hNX, by omega, hr03, hd03,
    by rw [← hxdef, hn, hpl3], by rw [← hxdef, hn, hdl3], by rw [← hxdef, hn, hfl3], ?_⟩⟩
  · unfold readPhase
    refine (Run.seq hr1 (Run.seq hr2 hr3)).mono ?_
    rw [hXl]
    nlinarith
  · rw [← hxdef, hx3, hXa]
  · rw [← hxdef, ha3 "f" (by decide), hf2, hn]; rfl
  · rw [← hxdef, ha3 "en" (by decide), hinit "en" (by decide) (by decide), hn]; simp [hext, evalExt]
  · rw [← hxdef, ha3 "val" (by decide), hinit "val" (by decide) (by decide), hn]; simp [hext, evalExt]
  · rw [hr3.out_eq bfs_noWrite, hr2.out_eq readFml_noWrite, hr1.out_eq readTree_noWrite]; rfl
  · rw [← hxdef, ← hXa]; exact hnodes

end Lax185574Proofs.EvalRam
