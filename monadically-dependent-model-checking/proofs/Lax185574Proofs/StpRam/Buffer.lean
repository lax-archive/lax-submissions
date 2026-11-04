import Lax185574Proofs.Words.TreeCopy
import Lax185574Proofs.Words.TreeWord
import Lax185574Proofs.Words.ForLoop
import Lax185574Proofs.Legacy

/-!
Copying type trees into the buffer of the glue program of
lem:compute-stp.

The glue program keeps its state in the array `x`, filled up to the
pointer `xp` (`XAt`). `push e` appends a value. `cpTree` copies the word
of a type tree from the input into `x` as a frame, its length and then
the word. `cpFam` copies the word of a family of type trees, the number
of trees and then their words one after the other, as the word of the
list of the tree words.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-- Append the value of `e` to the buffer `x`. -/
def push (e : Expr) : Com := .seq (.store "x" (.var "xp") e) (.assign "xp" (.add (.var "xp") (.lit 1)))

theorem push_run {B : ℕ} {O pre : List ℕ} {e : Expr} {v : ℕ} {τ : Env} (hx : XAt O pre τ)
    (hl : pre.length < O.length) (hB : pre.length + 1 < B) (he : e.evalB B τ = some v) :
    ∃ τ', Run B (push e) τ τ' (e.size + 8) ∧ XAt O (pre ++ [v]) τ' ∧ τ'.inp = τ.inp ∧
      τ'.out = τ.out := by
  obtain ⟨hxp, hxa⟩ := hx
  have hxl : (τ.arrs "x").length = O.length := by rw [hxa]; simp; omega
  refine ⟨(τ.setArr "x" pre.length v).setVar "xp" (pre.length + 1),
    (Run.seq (Run.store (idx := pre.length) (by simp [hxp]; omega) he (by omega))
      (Run.assign ?_)).mono ?_, ⟨by simp, ?_⟩, by simp, by simp⟩
  · simp [hxp]; omega
  · simp [Expr.size]; omega
  · simp only [arrs_setVar, arrs_setArr]
    rw [hxa, set_prefix hl]; simp

theorem XAt.setBack {O pre mid : List ℕ} {a : ℕ} {τ : Env} (h : XAt O (pre ++ a :: mid) τ) (b : ℕ) :
    XAt O (pre ++ b :: mid) (τ.setArr "x" pre.length b) := by
  obtain ⟨hxp, hxa⟩ := h
  refine ⟨by simpa using hxp, ?_⟩
  simp only [arrs_setArr, hxa]
  rw [List.append_assoc, List.set_append_right _ _ le_rfl, Nat.sub_self]
  simp

/-- Copy the word of a node, one list of words at height `0` and two
above. -/
def cpNode : Com := .seq cpList (.ite (.lt (.lit 0) (.var "hq")) cpList .skip)

theorem cpNode_run {B q ℓ : ℕ} (t : Node q ℓ) {O pre rest : List ℕ} {τ : Env} (hx : XAt O pre τ)
    (hinp : τ.inp = toWord t ++ rest) (hq : τ.vars "hq" = q)
    (hfit : pre.length + (toWord t).length ≤ O.length) (hB : pre.length + (toWord t).length < B)
    (hv : ∀ v ∈ toWord t, v < B) (hqB : q < B) :
    ∃ τ', Run B cpNode τ τ' (48 * (toWord t).length + 40) ∧ XAt O (pre ++ toWord t) τ' ∧
      τ'.inp = rest ∧ τ'.out = τ.out := by
  cases q with
  | zero =>
    have hw : toWord t = toWord (Node.atoms t).words := toWord_node_zero t
    obtain ⟨τ5, hr5, hx5, hinp5⟩ := cpList_spec B O pre rest (Node.atoms t).words
      (by rw [← hw]; exact hfit) (by rw [← hw]; exact hB) (by rw [← hw]; exact hv) τ
      ⟨hx, by rw [hinp, hw]⟩
    have hq5 : τ5.vars "hq" = 0 := by rw [hr5.frame_var "hq" (by decide), hq]
    have hrun : Run B cpNode τ τ5 (48 * (toWord t).length + 40) := by
      unfold cpNode
      refine (Run.seq hr5 (Run.ite_false ?_ Run.skip)).mono ?_
      · simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff, hq5]
        exact ⟨0, 0, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp⟩
      · rw [hw]; simp only [Cond.size, Expr.size]; omega
    exact ⟨τ5, hrun, by rw [hw]; exact hx5, hinp5, hrun.out_eq (by decide)⟩
  | succ q =>
    have hw : toWord t = toWord (Node.atoms t).words ++ toWord (Node.exts t).words :=
      toWord_node_succ t
    have hl := congrArg List.length hw
    rw [List.length_append] at hl
    obtain ⟨τ5, hr5, hx5, hinp5⟩ := cpList_spec B O pre (toWord (Node.exts t).words ++ rest)
      (Node.atoms t).words (by omega) (by omega)
      (fun v h => hv v (by rw [hw]; exact List.mem_append_left _ h)) τ
      ⟨hx, by rw [hinp, hw, List.append_assoc]⟩
    have hq5 : τ5.vars "hq" = q + 1 := by rw [hr5.frame_var "hq" (by decide), hq]
    obtain ⟨τ6, hr6, hx6, hinp6⟩ := cpList_spec B O (pre ++ toWord (Node.atoms t).words) rest
      (Node.exts t).words (by rw [List.length_append]; omega) (by rw [List.length_append]; omega)
      (fun v h => hv v (by rw [hw]; exact List.mem_append_right _ h)) τ5 ⟨hx5, hinp5⟩
    have hrun : Run B cpNode τ τ6 (48 * (toWord t).length + 40) := by
      unfold cpNode
      refine (Run.seq hr5 (Run.ite_true ?_ hr6)).mono ?_
      · simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff, hq5]
        exact ⟨0, q + 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp⟩
      · simp only [Cond.size, Expr.size]; omega
    exact ⟨τ6, hrun, by rw [hw, ← List.append_assoc]; exact hx6, hinp6, hrun.out_eq (by decide)⟩

/-- Copy the word of a type tree as a frame. -/
def cpTree : Com :=
  .seq (.assign "p0" (.var "xp")) (.seq (push (.lit 0)) (.seq (.read "hk") (.seq (push (.var "hk"))
    (.seq (.read "hq") (.seq (push (.var "hq")) (.seq (.read "hl") (.seq (push (.var "hl"))
    (.seq cpNode (.store "x" (.var "p0") (.sub (.sub (.var "xp") (.var "p0")) (.lit 1)))))))))))

theorem toWord_typeTree (T : TypeTree) : toWord T = T.k :: T.q :: T.ℓ :: toWord T.root := rfl

set_option maxHeartbeats 1000000 in
theorem cpTree_run {B : ℕ} (T : TypeTree) {O pre rest : List ℕ} {τ : Env} (hx : XAt O pre τ)
    (hinp : τ.inp = toWord T ++ rest) (hfit : pre.length + 1 + (toWord T).length ≤ O.length)
    (hB : pre.length + 1 + (toWord T).length < B) (hv : ∀ v ∈ toWord T, v < B) :
    ∃ τ', Run B cpTree τ τ' (48 * (toWord T).length + 100) ∧
      XAt O (pre ++ (toWord T).length :: toWord T) τ' ∧ τ'.inp = rest ∧ τ'.out = τ.out := by
  obtain ⟨k, q, ℓ, t⟩ := T
  have hw : toWord (⟨k, q, ℓ, t⟩ : TypeTree) = k :: q :: ℓ :: toWord t := rfl
  rw [hw] at hinp hfit hB hv ⊢
  simp only [List.length_cons] at hfit hB
  have hk : k < B := hv k (by simp)
  have hqB : q < B := hv q (by simp)
  have hℓ : ℓ < B := hv ℓ (by simp)
  have hpre : τ.vars "xp" = pre.length := hx.1
  set τ1 := τ.setVar "p0" pre.length with hτ1
  have r1 : Run B (.assign "p0" (.var "xp")) τ τ1 2 :=
    (Run.assign (by simp [hpre]; omega)).mono (by simp [Expr.size])
  have hx1 : XAt O pre τ1 := ⟨by simp [hτ1, hpre], by simp [hτ1, hx.2]⟩
  obtain ⟨τ2, r2, hx2, hi2, ho2⟩ := push_run (B := B) (O := O) (pre := pre) (e := .lit 0) (v := 0) hx1 (by omega) (by omega) (by simp; omega)
  have hi2' : τ2.inp = k :: (q :: ℓ :: (toWord t ++ rest)) := by rw [hi2]; simp [hτ1, hinp]
  set τ3 : Env := { τ2.setVar "hk" k with inp := q :: ℓ :: (toWord t ++ rest) } with hτ3
  have r3 : Run B (.read "hk") τ2 τ3 1 := Run.read hi2'
  obtain ⟨τ4, r4, hx4, hi4, ho4⟩ := push_run (B := B) (O := O) (pre := pre ++ [0]) (e := .var "hk") (v := k)
    (⟨by rw [← hx2.1]; simp [hτ3], by rw [← hx2.2]; simp [hτ3]⟩ : XAt O (pre ++ [0]) τ3)
    (by simp; omega) (by simp; omega) (by simp [hτ3]; omega)
  set τ5 : Env := { τ4.setVar "hq" q with inp := ℓ :: (toWord t ++ rest) } with hτ5
  have r5 : Run B (.read "hq") τ4 τ5 1 := Run.read (by rw [hi4])
  obtain ⟨τ6, r6, hx6, hi6, ho6⟩ := push_run (B := B) (O := O) (pre := pre ++ [0] ++ [k]) (e := .var "hq") (v := q)
    (⟨by rw [← hx4.1]; simp [hτ5], by rw [← hx4.2]; simp [hτ5]⟩ : XAt O (pre ++ [0] ++ [k]) τ5)
    (by simp; omega) (by simp; omega) (by simp [hτ5]; omega)
  set τ7 : Env := { τ6.setVar "hl" ℓ with inp := toWord t ++ rest } with hτ7
  have r7 : Run B (.read "hl") τ6 τ7 1 := Run.read (by rw [hi6])
  obtain ⟨τ8, r8, hx8, hi8, ho8⟩ := push_run (B := B) (O := O) (pre := pre ++ [0] ++ [k] ++ [q]) (e := .var "hl") (v := ℓ)
    (⟨by rw [← hx6.1]; simp [hτ7], by rw [← hx6.2]; simp [hτ7]⟩ : XAt O (pre ++ [0] ++ [k] ++ [q]) τ7)
    (by simp; omega) (by simp; omega) (by simp [hτ7]; omega)
  have hq8 : τ8.vars "hq" = q := by
    rw [r8.frame_var "hq" (by decide)]
    simp [hτ7, r6.frame_var "hq" (by decide), hτ5]
  have hp8 : τ8.vars "p0" = pre.length := by
    rw [r8.frame_var "p0" (by decide)]
    simp [hτ7, r6.frame_var "p0" (by decide), hτ5, r4.frame_var "p0" (by decide), hτ3,
      r2.frame_var "p0" (by decide), hτ1]
  have hi8' : τ8.inp = toWord t ++ rest := by rw [hi8]
  have he8 : pre ++ [0] ++ [k] ++ [q] ++ [ℓ] = pre ++ [0, k, q, ℓ] := by simp
  rw [he8] at hx8
  obtain ⟨τ9, r9, hx9, hi9, ho9⟩ := cpNode_run t hx8 hi8' hq8 (by simp; omega) (by simp; omega)
    (fun v h => hv v (by simp [h])) hqB
  have hxp9 : τ9.vars "xp" = pre.length + 4 + (toWord t).length := by rw [hx9.1]; simp; omega
  have hp9 : τ9.vars "p0" = pre.length := by rw [r9.frame_var "p0" (by decide), hp8]
  have hxl9 : (τ9.arrs "x").length = O.length := by rw [hx9.2]; simp; omega
  have r10 : Run B (.store "x" (.var "p0") (.sub (.sub (.var "xp") (.var "p0")) (.lit 1))) τ9
      (τ9.setArr "x" pre.length ((toWord t).length + 3)) 10 := by
    refine (Run.store (idx := pre.length) (by simp [hp9]; omega) ?_ (by omega)).mono (by simp [Expr.size])
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, hp9, hxp9]
    exact ⟨pre.length + 4 + (toWord t).length - pre.length, 1, ⟨_, _, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩,
      rfl, by show _ - _ < B; omega⟩, ⟨rfl, by omega⟩, by show _ = _ - _; omega, by omega⟩
  have hrun : Run B cpTree τ (τ9.setArr "x" pre.length ((toWord t).length + 3))
      (48 * (k :: q :: ℓ :: toWord t).length + 100) := by
    unfold cpTree
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
      (Run.seq r8 (Run.seq r9 r10))))))))).mono ?_
    simp [Expr.size]; omega
  refine ⟨_, hrun, ?_, by simp [hi9], hrun.out_eq (by decide)⟩
  have hx9' : XAt O (pre ++ 0 :: (k :: q :: ℓ :: toWord t)) τ9 := by
    have : pre ++ [0, k, q, ℓ] ++ toWord t = pre ++ 0 :: (k :: q :: ℓ :: toWord t) := by simp
    rw [← this]; exact hx9
  have := XAt.setBack hx9' ((toWord t).length + 3)
  simpa using this

theorem XAt.setVar {O pre : List ℕ} {τ : Env} (h : XAt O pre τ) {x : String} (hx : x ≠ "xp") (v : ℕ) :
    XAt O pre (τ.setVar x v) :=
  ⟨by simp only [vars_setVar, if_neg (Ne.symm hx)]; exact h.1, by simpa using h.2⟩

/-- The words of the trees of a family. -/
noncomputable def famW {n : ℕ} (f : Fin n → TypeTree) : List (List ℕ) := List.ofFn fun i => toWord (f i)

theorem length_famW {n : ℕ} (f : Fin n → TypeTree) : (famW f).length = n := by simp [famW]

theorem toWord_fam {n : ℕ} (f : Fin n → TypeTree) : toWord f = n :: (famW f).flatten := by
  show (List.ofFn f).length :: ((List.ofFn f).map toWord).flatten = _
  simp [famW, List.map_ofFn, Function.comp_def]

theorem frames_take_drop (ws : List (List ℕ)) (j : ℕ) :
    frames (ws.take j) ++ frames (ws.drop j) = frames ws := by
  simp only [frames, ← List.flatten_append, ← List.map_append, List.take_append_drop]

/-- Copy the word of a family of type trees as the word of the list of
the tree words. -/
def cpFam : Com := .seq (.read "fn") (.seq (push (.var "fn")) (forUp "ti" (.var "fn") cpTree))

set_option maxHeartbeats 1000000 in
theorem cpFam_run {B n L : ℕ} (f : Fin n → TypeTree) {O pre rest : List ℕ} {τ : Env}
    (hx : XAt O pre τ) (hinp : τ.inp = toWord f ++ rest) (hL : ∀ i, (toWord (f i)).length ≤ L)
    (hfit : pre.length + (toWord (famW f)).length ≤ O.length)
    (hB : pre.length + (toWord (famW f)).length < B) (hv : ∀ v ∈ toWord f, v < B) :
    ∃ τ', Run B cpFam τ τ' (n * (48 * L + 110) + 30) ∧ XAt O (pre ++ toWord (famW f)) τ' ∧
      τ'.inp = rest ∧ τ'.out = τ.out := by
  have hFl := length_famW f
  have hTW : toWord (famW f) = n :: frames (famW f) := by rw [toWord_words, hFl]
  have hTl : (toWord (famW f)).length = 1 + (frames (famW f)).length := by rw [hTW]; simp; omega
  have hnB : n < B := by
    have := length_frames (famW f); omega
  rw [toWord_fam] at hinp hv
  set τ1 : Env := { τ.setVar "fn" n with inp := (famW f).flatten ++ rest } with hτ1
  have r1 : Run B (.read "fn") τ τ1 1 := Run.read (by rw [hinp]; rfl)
  obtain ⟨τ2, r2, hx2, hi2, ho2⟩ := push_run (B := B) (O := O) (pre := pre) (e := .var "fn") (v := n)
    (⟨by rw [← hx.1]; simp [hτ1], by rw [← hx.2]; simp [hτ1]⟩ : XAt O pre τ1)
    (by have := length_frames (famW f); omega) (by have := length_frames (famW f); omega)
    (by simp [hτ1]; omega)
  have hfn2 : τ2.vars "fn" = n := by rw [r2.frame_var "fn" (by decide)]; simp [hτ1]
  let I : ℕ → Env → Prop := fun j ρ => ρ.vars "fn" = n ∧
    XAt O (pre ++ n :: frames ((famW f).take j)) ρ ∧ ρ.inp = ((famW f).drop j).flatten ++ rest ∧
    ρ.out = τ.out
  obtain ⟨τ3, r3, ⟨-, hx3, hi3, ho3⟩, -⟩ := forUp_run (B := B) (i := "ti") (e := .var "fn")
    (body := cpTree) (N := n) (K := 48 * L + 100) I (σ := τ2) hnB
    (fun j _ ρ hI _ => by
      simp only [evalB_var_iff]; exact ⟨hI.1.symm, by rw [hI.1]; exact hnB⟩)
    ⟨by simp [hfn2], XAt.setVar (by simp only [List.take_zero, frames, List.map_nil, List.flatten_nil]; exact hx2) (by decide) 0, by simp [hi2, hτ1],
      by simp [ho2, hτ1]⟩
    (by
      rintro j hj ρ ⟨hfn, hxρ, hiρ, hoρ⟩ hti
      have hjl : j < (famW f).length := by omega
      have hwj : (famW f)[j] = toWord (f ⟨j, hj⟩) := by simp [famW]
      have hd : ((famW f).drop j).flatten = toWord (f ⟨j, hj⟩) ++ ((famW f).drop (j + 1)).flatten := by
        rw [List.drop_eq_getElem_cons hjl, List.flatten_cons, hwj]
      have hft := length_frames_take_succ hjl
      have hfa : (frames ((famW f).take (j + 1))).length ≤ (frames (famW f)).length := by
        rw [← frames_take_drop (famW f) (j + 1)]; simp
      rw [hwj] at hft
      obtain ⟨ρ', r, hx', hi', ho'⟩ := cpTree_run (B := B) (f ⟨j, hj⟩) hxρ (rest := ((famW f).drop (j + 1)).flatten ++ rest)
        (by rw [hiρ, hd, List.append_assoc]) (by simp; omega) (by simp; omega)
        (fun v hv' => hv v (List.mem_cons_of_mem _ (List.mem_flatten.mpr
          ⟨_, by rw [famW, List.mem_ofFn]; exact ⟨⟨j, hj⟩, rfl⟩, hv'⟩)))
      refine ⟨ρ', r.mono (by have := hL ⟨j, hj⟩; omega), by rw [r.frame_var "ti" (by decide), hti],
        by simp [r.frame_var "fn" (by decide), hfn], XAt.setVar ?_ (by decide) _, by simp [hi'],
        by simp [ho', hoρ]⟩
      rw [frames_take_succ' hjl, hwj]; simpa using hx')
  have hrun : Run B cpFam τ τ3 (n * (48 * L + 110) + 30) := by
    unfold cpFam
    refine (Run.seq r1 (Run.seq r2 r3)).mono ?_
    simp only [Expr.size]; nlinarith
  refine ⟨τ3, hrun, ?_, by rw [hi3, List.drop_of_length_le (by omega)]; simp, ho3⟩
  rw [hTW]; rw [List.take_of_length_le (by omega)] at hx3; exact hx3

end Lax185574Proofs.StpRam
