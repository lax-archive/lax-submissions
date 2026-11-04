import Lax185574Proofs.TreeCanon
import Lax185574Proofs.TreeAlgo.MergeLift
import Lax185574.MergeLift
import Lax185574Proofs.Interface.Poly

/-!
The merge lift of a type tree, on the word RAM.

The program is the one-pass transformation `jobProg` of
`Lax185574Proofs.Words.TreeJobs`, followed by restoring canonical form
(`Lax185574Proofs.TreeCanon.treeCanon`). It reads the colors `P` and `Q` after
the tree, and maps every color entry of an atom code, entry `1` of a code
with tag `3` (`Y(x)`) and entry `2` of a code with tag `5`
(`dist(x, Y) < r`), from `Q` to `P`. All other entries and all guards are
kept. Restoring canonical form merges atoms that become equal. This is the semantic core
`Lax185574Proofs.TreeAlgo.mergeNode`.
-/

namespace Lax185574Proofs.MergeLiftRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

/-- Entry `k` of an atom code with tag `tg` is a color. -/
def IsCol (tg k : ℕ) : Prop := (tg = 3 ∧ k = 1) ∨ (tg = 5 ∧ k = 2)

instance (tg k : ℕ) : Decidable (IsCol tg k) := by unfold IsCol; infer_instance

/-- The map of the entries of atom codes. -/
def msub (P Q : ℕ) (tg k _d v : ℕ) : Option ℕ :=
  if IsCol tg k then some (mergeColor P Q v) else some v

/-- The guards are kept. -/
def mgsub (_d i : ℕ) : Option ℕ := some i

theorem atomMapAux_id (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (tag d : ℕ)
    (h : ∀ k v, sub tag k d v = some v) : ∀ (w : List ℕ) (k0 : ℕ), atomMapAux sub tag d k0 w = some w
  | [], _ => rfl
  | v :: w, k0 => by simp [atomMapAux, h, atomMapAux_id sub tag d h w (k0 + 1)]

theorem msub_id (P Q tag d : ℕ) (h3 : tag ≠ 3) (h5 : tag ≠ 5) :
    ∀ k v, msub P Q tag k d v = some v := by
  intro k v; simp [msub, IsCol, h3, h5]

theorem atomMap_code (P Q : ℕ) {m : ℕ} (d : ℕ) (φ : DistFO m) :
    atomMap (msub P Q) d (toWord φ) = some (toWord (recolorAtom (mergeColor P Q) φ)) := by
  cases φ with
  | color Y i => simp [toWord_atom, code, atomMap, atomMapAux, msub, IsCol, recolorAtom]
  | distColorLt r Y i => simp [toWord_atom, code, atomMap, atomMapAux, msub, IsCol, recolorAtom]
  | eq i j => simp [toWord_atom, code, atomMap, atomMapAux, msub, IsCol, recolorAtom]
  | edge i j => simp [toWord_atom, code, atomMap, atomMapAux, msub, IsCol, recolorAtom]
  | nonEdge i j => simp [toWord_atom, code, atomMap, atomMapAux, msub, IsCol, recolorAtom]
  | distLe r i j => simp [toWord_atom, code, atomMap, atomMapAux, msub, IsCol, recolorAtom]
  | not φ =>
    simp only [toWord_atom, code, atomMap, List.headD_cons, recolorAtom]
    exact atomMapAux_id _ 6 d (msub_id P Q 6 d (by decide) (by decide)) _ 0
  | and φ ψ =>
    simp only [toWord_atom, code, atomMap, List.headD_cons, recolorAtom]
    exact atomMapAux_id _ 7 d (msub_id P Q 7 d (by decide) (by decide)) _ 0
  | exLocal i s φ =>
    simp only [toWord_atom, code, atomMap, List.headD_cons, recolorAtom]
    exact atomMapAux_id _ 8 d (msub_id P Q 8 d (by decide) (by decide)) _ 0

theorem biUnion_some {α β : Type*} [DecidableEq β] (S : Finset α) (g : α → β) :
    (S.biUnion fun a => (some (g a)).toFinset) = S.image g := by
  ext b; simp [eq_comm]

/-- **The program computes the core.** -/
theorem treeOut_merge (P Q : ℕ) (X : List ℕ) :
    ∀ (h d m : ℕ) (t : Node h m) (p : ℕ) (r : List ℕ), X.drop p = toWord t ++ r →
      treeOut (msub P Q) mgsub h d X p = toWord (recolorNode (mergeColor P Q) t)
  | 0, d, m, t, p, r, hx => by
    rw [treeOut_zero, toWord_node_zero, atoms_recolorNode]
    rw [toWord_node_zero] at hx
    rw [sortedDistinct_atomCands hx (fun φ => some (recolorAtom (mergeColor P Q) φ))
      (fun φ _ => by rw [atomMap_code]; rfl), biUnion_some]
  | h + 1, d, m, t, p, r, hx => by
    obtain ⟨h1, h2⟩ := nodeSplit hx
    rw [treeOut_succ, toWord_node_succ, atoms_recolorNode]
    rw [sortedDistinct_atomCands h1 (fun φ => some (recolorAtom (mergeColor P Q) φ))
      (fun φ _ => by rw [atomMap_code]; rfl), biUnion_some]
    congr 1
    rw [sortedDistinct_extCands h2 some (recolorNode (mergeColor P Q))
      (fun i => rfl) (fun ε _ P' r' hP => treeOut_merge P Q X h (d + 1) (m + 1) ε.2 P' r' hP)]
    show _ = toWord (Finset.words ((Node.exts t).image fun e => (e.1, recolorNode (mergeColor P Q) e.2)))
    congr 2
    ext e; simp only [Finset.mem_biUnion, Option.map_some, Option.toFinset_some,
      Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

/-! ### The hooks -/

/-- The data: `g1 = P`, `g2 = Q`. -/
def MDat (P Q B : ℕ) (τ : Env) : Prop := τ.vars "g1" = P ∧ τ.vars "g2" = Q ∧ P < B ∧ Q < B

theorem mdat_ok (P Q B : ℕ) : DatOK (MDat P Q B) := by
  intro τ τ' h1 h2 _ _ _ ⟨d1, d2, d3, d4⟩
  exact ⟨by rw [h1, d1], by rw [h2, d2], d3, d4⟩

/-- Recolor `Q` to `P`. -/
def recol : Com := .ite (.eq (.var "ev") (.var "g2")) (.assign "nv" (.var "g1")) .skip

/-- The hook for the entries of atom codes. -/
def subCmd : Com :=
  .seq (.assign "nv" (.var "ev")) (.seq (.assign "drp" (.lit 0))
    (.ite (.eq (.var "tg") (.lit 3)) (.ite (.eq (.var "kk") (.lit 1)) recol .skip)
      (.ite (.eq (.var "tg") (.lit 5)) (.ite (.eq (.var "kk") (.lit 2)) recol .skip) .skip)))

theorem subCmd_ok (P Q B : ℕ) (hB : 5 < B) : SubOK subCmd (msub P Q) (MDat P Q B) B 40 := by
  rintro τ ⟨⟨hg1, hg2, hPB, hQB⟩, htg, hkk, hdd, hev⟩
  unfold subCmd recol
  run_vcg
  all_goals simp_all [msub, IsCol, mergeColor]

/-- The hook for the guards. -/
def grdCmd : Com := .seq (.assign "ng" (.var "gi")) (.assign "drp" (.lit 0))

theorem grdCmd_ok (P Q B : ℕ) (hB : 1 < B) : GrdOK grdCmd mgsub (MDat P Q B) B 10 := by
  rintro τ ⟨-, hgi, hdd⟩
  unfold grdCmd
  run_vcg
  all_goals simp_all [mgsub]

theorem subCmd_frame : HookFrame subCmd := by
  refine ⟨fun y hy => ?_, by simp [subCmd, recol, Com.warrs], by simp [subCmd, recol, Com.reads],
    by simp [subCmd, recol, Com.NoWrite]⟩
  simp [subCmd, recol, Com.wvars] at hy
  simp [hookVars]
  tauto

theorem grdCmd_frame : HookFrame grdCmd := by
  refine ⟨fun y hy => ?_, by simp [grdCmd, Com.warrs], by simp [grdCmd, Com.reads],
    by simp [grdCmd, Com.NoWrite]⟩
  simp [grdCmd, Com.wvars] at hy
  simp [hookVars]
  tauto

/-- Read `P` and `Q`; the arity is kept. -/
def readArgs : Com := .seq (.read "g1") (.seq (.read "g2") (.assign "ol" (.var "hl")))

theorem readArgs_frame : ArgFrame readArgs := by
  refine ⟨fun y hy => ?_, fun b hb => ?_, by simp [readArgs, Com.NoWrite]⟩
  · simp [readArgs, Com.wvars] at hy
    simp; tauto
  · simp [readArgs, Com.warrs] at hb

theorem readArgs_spec (P Q ℓ B : ℕ) (hP : P < B) (hQ : Q < B) (hℓ : ℓ < B) :
    Spec B (fun τ => τ.inp = [P, Q] ∧ τ.vars "hl" = ℓ ∧ τ.arrs "gt" = List.replicate 0 0)
      readArgs (fun _ τ' => MDat P Q B τ' ∧ τ'.vars "ol" = ℓ) 10 := by
  rintro τ ⟨hinp, hhl, -⟩
  set τ1 : Env := { τ.setVar "g1" P with inp := [Q] } with hτ1
  set τ2 : Env := { τ1.setVar "g2" Q with inp := [] } with hτ2
  refine ⟨τ2.setVar "ol" ℓ, ?_, ⟨by simp [hτ2, hτ1], by simp [hτ2, hτ1], hP, hQ⟩, by simp⟩
  unfold readArgs
  refine (Run.seq (Run.read hinp) (Run.seq (Run.read rfl) (Run.assign ?_))).mono (by simp)
  simp [hτ2, hτ1, hhl]; omega

/-! ### The program -/

/-- The one pass of the merge lift, in IMP+. It writes the jobs of the
lifted tree, with sets in arbitrary order. -/
def prog : Com := jobProg readArgs subCmd grdCmd

/-- The scalars and arrays of `prog`. -/
def layout : Lax808846Proofs.Compile.Layout :=
  ⟨["hk", "hq", "hl", "ol", "xp", "e1", "e2", "e3", "vv", "ev", "nn", "u", "y", "dd", "b0", "m", "ap",
    "lf", "tg", "dr", "kk", "nv", "ng", "drp", "s1", "s2", "s3", "cc", "gi", "cs", "cl", "ck", "bp",
    "g1", "g2", "g3", "g4", "r1", "r2", "r3", "ci", "cj", "pa", "pb", "la", "lb", "k", "c", "fnd", "s",
    "ok", "best", "hp", "prev", "cnt", "t", "ow", "s0", "l0", "wk", "fi", "i", "j", "p", "n", "v"],
    ["x", "pos", "dep", "fc", "a", "st", "ln", "ord", "b", "bs", "bl", "gt"], 8⟩

theorem prog_ok : Lax808846Proofs.Compile.Com.Ok layout prog := by
  simp [prog, jobProg, readTree, cpList, cpFrame, cpEntries, cpEntry, readArgs, bfs,
    bfsBody, skipList, skipBody, pushList, pushBody, fillRefs, forUpJ, fillBody, fillIdx, jobLoop,
    jobNode, atList, atFrame, atEntries, atEntry, subCmd, recol, exList, exFrame, exCopies, exCopy,
    grdCmd, writeAll, writeWord, writeEntry, rootRefs, rootIdx, layout,
    Lax808846Proofs.Compile.Com.Ok, Lax808846Proofs.Compile.Cond.Ok, Lax808846Proofs.Compile.condExpr,
    Lax808846Proofs.Compile.Expr.Ok]

end Lax185574Proofs.MergeLiftRam

namespace Lax185574Proofs.MergeLift

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MergeLiftRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574Proofs.TreeCanon

/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_mergeLift_old :
    ∃ (p : Lax808846.Ram.Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n) (P Q : ℕ),
        ℓ ≤ k → P ≠ Q →
        Lax185574.Computing.Computes p e c (tree G k q u, P, Q) (tree (merge G P Q) k q u)
          (fun m => c * (m + 1) ^ a) := by
  obtain ⟨p, e, hp⟩ := treeCanon readArgs subCmd grdCmd layout prog_ok
  obtain ⟨C, hC⟩ := hp 100
  refine ⟨p, e, fun k q => ⟨C, e, fun n G ℓ u P Q _ _ => ?_⟩⟩
  set t := node G k q u with ht
  have hx : toWord (tree G k q u, P, Q) = [k, q, ℓ] ++ toWord t ++ [P, Q] := rfl
  intro w hadm
  rw [hx] at hadm ⊢
  set x := [k, q, ℓ] ++ toWord t ++ [P, Q] with hxdef
  set M := maxEntry x with hM
  have hmem : ∀ v ∈ x, v ≤ M := fun v hv => le_maxEntry hv
  have hPm : P ≤ M := hmem _ (by rw [hxdef]; simp)
  have hQm : Q ≤ M := hmem _ (by rw [hxdef]; simp)
  have hℓm : ℓ ≤ M := hmem _ (by rw [hxdef]; simp)
  set B := valBound 8 2 x with hB
  have hBdef : B = 8 * (x.length + M + 1) ^ 2 := rfl
  have hMB : M + 26 < B := by
    have h1 : 4 ≤ x.length := by rw [hxdef]; simp <;> omega
    have h2 : x.length + M + 1 ≤ (x.length + M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    rw [hBdef]; omega
  have hadm' : C * (x.length + M + 1) ^ e ≤ 2 ^ w := hadm M (maxEntry_mem (by simp [hxdef]))
  obtain ⟨h1, h2⟩ := hC (msub P Q) mgsub (MDat P Q B) 40 10 10 k q ℓ t [P, Q] 0 ℓ
    subCmd_frame grdCmd_frame readArgs_frame (subCmd_ok P Q B (by omega)) (grdCmd_ok P Q B (by omega))
    (mdat_ok P Q B) (readArgs_spec P Q ℓ B (by omega) (by omega) (by omega))
    (fun dd _ tg kk v r hv hr => by
      have hvM : v ≤ M := by
        rcases hv with hv | rfl
        · exact hmem v (by rw [hxdef]; simp [hv])
        · omega
      simp only [msub, mergeColor] at hr
      show r < B
      split_ifs at hr <;> simp at hr <;> omega)
    (fun dd _ i r hi hr => by
      have hiM : i ≤ M := by
        rcases hi with hi | rfl
        · exact hmem i (by rw [hxdef]; simp [hi])
        · omega
      show r < B
      simp only [mgsub, Option.some.injEq] at hr; omega)
    (show ℓ < B by omega) (show 40 + 10 + 10 ≤ 100 * (x.length + 1) by omega) w hadm'
  have hout : [k, q, ℓ] ++ treeOut (msub P Q) mgsub q 0
      (toWord t ++ List.replicate (x.length + 1 - (toWord t).length) 0) 0 =
      toWord (tree (merge G P Q) k q u) := by
    rw [treeOut_merge P Q _ q 0 ℓ t 0 (List.replicate (x.length + 1 - (toWord t).length) 0) (by simp)]
    show _ = [k, q, ℓ] ++ toWord (node (merge G P Q) k q u)
    rw [← mergeNode_node G P Q k q u]
    rfl
  rw [hout] at h1 h2
  refine ⟨h1, fun _ y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  obtain ⟨T, hT, hr⟩ := h2
  exact ⟨T, hT, hr⟩

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.MergeLift.exists_program_mergeLift
---
The program is one pass over the tree followed by restoring canonical
form, as in the proof of the merge lift lemma. The pass reads the tree
and the colors `P` and `Q`, lists the nodes of the tree in breadth-first
order, and writes for every node, from the last to the first, its
transformed atoms and its extensions. An atom is transformed by
replacing the color `Q` by `P` in every atom `Y(x)` and `dist(x, Y) <
r`. The guards are kept, and the child of an extension is referred to by
the indices of the jobs of the child. Nothing is sorted in the pass. The
canonical form is then restored from the leaves up by the program of the
canonical form observation, called once for every set of the result
(`TreeCanon.treeCanon`), which merges atoms that become equal. This is
the semantic core `mergeNode`, whose correctness is `mergeNode_node`. No
tree grows, so the time is polynomial in the length of the input.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_mergeLift :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n) (P Q : ℕ),
        ℓ ≤ k → P ≠ Q →
          A.Computes c (tree G k q u, P, Q) (tree (merge G P Q) k q u)
            (((encode (tree G k q u)).length + 1) ^ a) := by
  obtain ⟨p, e, h⟩ := exists_program_mergeLift_old
  refine ⟨⟨p, e⟩, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := h k q
  refine ⟨c * (2 + 1) ^ a, a, fun n G ℓ u P Q hℓ hPQ => ?_⟩
  refine computes_of_old_nat (((encode (tree G k q u)).length + 1) ^ a) (by push_cast; rfl)
    (Nat.le_mul_of_pos_right _ (by positivity)) ?_ (h n G ℓ u P Q hℓ hPQ)
  show c * ((encode (tree G k q u, P, Q)).length + 1) ^ a ≤ _
  rw [length_encode_prod, length_encode_prod]
  show c * ((encode (tree G k q u)).length + 2 + 1) ^ a ≤ _
  refine le_trans ?_ (Nat.le_add_right _ _)
  rw [mul_assoc]
  exact Nat.mul_le_mul_left c (add_succ_pow_le (encode (tree G k q u)).length 2 a)

end Lax185574Proofs.MergeLift
