import Lax185574Proofs.Words.TreeNode

/-!
Reading a type tree on the word RAM.

`readTree` reads the header `k, q, ℓ` of a type tree and copies the word
of its root. `ArgFrame` describes a command that reads further arguments.
These are shared by the programs that transform type trees.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-! ### Reading the tree -/

/-- Read the header and copy the word of the root into `x`. -/
def readTree : Com :=
  .seq (.read "hk") (.seq (.read "hq") (.seq (.read "hl") (.seq (.assign "xp" (.lit 0))
    (.seq cpList (.ite (.lt (.lit 0) (.var "hq")) cpList .skip)))))

theorem readTree_spec (B : ℕ) (k q ℓ : ℕ) (t : Node q ℓ) (rest O : List ℕ)
    (hfit : (toWord t).length ≤ O.length) (hB : (toWord t).length < B)
    (hv : ∀ v ∈ toWord t, v < B) (hqB : q < B) :
    Spec B (fun τ => τ.inp = [k, q, ℓ] ++ toWord t ++ rest ∧ τ.arrs "x" = O) readTree
      (fun _ τ' => τ'.vars "hk" = k ∧ τ'.vars "hq" = q ∧ τ'.vars "hl" = ℓ ∧
        τ'.arrs "x" = toWord t ++ O.drop (toWord t).length ∧ τ'.inp = rest)
      (48 * (toWord t).length + 40) := by
  rintro τ ⟨hinp, hxa⟩
  set τ1 : Env := { τ.setVar "hk" k with inp := q :: ℓ :: (toWord t ++ rest) } with hτ1
  set τ2 : Env := { τ1.setVar "hq" q with inp := ℓ :: (toWord t ++ rest) } with hτ2
  set τ3 : Env := { τ2.setVar "hl" ℓ with inp := toWord t ++ rest } with hτ3
  set τ4 := τ3.setVar "xp" 0 with hτ4
  have hx4 : XAt O [] τ4 := ⟨by simp [hτ4], by simp [hτ4, hτ3, hτ2, hτ1, hxa]⟩
  cases q with
  | zero =>
    have hw : toWord t = toWord (Node.atoms t).words := toWord_node_zero t
    obtain ⟨τ5, hr5, hx5, hinp5⟩ := cpList_spec B O [] rest (Node.atoms t).words
      (by rw [← hw]; simpa using hfit) (by rw [← hw]; simpa using hB) (by rw [← hw]; exact hv) τ4
      ⟨hx4, by simp [hτ4, hτ3, hτ2, hτ1, hw]⟩
    have hq5 : τ5.vars "hq" = 0 := by rw [hr5.frame_var "hq" (by decide)]; simp [hτ4, hτ3, hτ2, hτ1]
    refine ⟨τ5, ?_, by rw [hr5.frame_var "hk" (by decide)]; simp [hτ4, hτ3, hτ2, hτ1], hq5,
      by rw [hr5.frame_var "hl" (by decide)]; simp [hτ4, hτ3, hτ2, hτ1], by rw [hw]; simpa using hx5.2, hinp5⟩
    unfold readTree
    refine (Run.seq (Run.read (by rw [hinp]; rfl)) (Run.seq (Run.read rfl) (Run.seq (Run.read rfl)
      (Run.seq (Run.assign (v := 0) (by simp; omega)) (Run.seq hr5 (Run.ite_false ?_ Run.skip)))))).mono ?_
    · simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff, hq5]
      exact ⟨0, 0, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp⟩
    · rw [hw]; simp only [Cond.size, Expr.size]; omega
  | succ q =>
    have hw : toWord t = toWord (Node.atoms t).words ++ toWord (Node.exts t).words := toWord_node_succ t
    have hl := congrArg List.length hw
    rw [List.length_append] at hl
    obtain ⟨τ5, hr5, hx5, hinp5⟩ := cpList_spec B O [] (toWord (Node.exts t).words ++ rest)
      (Node.atoms t).words (by rw [List.length_nil]; omega) (by rw [List.length_nil]; omega)
      (fun v h => hv v (by rw [hw]; exact List.mem_append_left _ h)) τ4
      ⟨hx4, by simp [hτ4, hτ3, hτ2, hτ1, hw]⟩
    have hq5 : τ5.vars "hq" = q + 1 := by rw [hr5.frame_var "hq" (by decide)]; simp [hτ4, hτ3, hτ2, hτ1]
    obtain ⟨τ6, hr6, hx6, hinp6⟩ := cpList_spec B O (toWord (Node.atoms t).words) rest
      (Node.exts t).words (by omega) (by omega)
      (fun v h => hv v (by rw [hw]; exact List.mem_append_right _ h)) τ5
      ⟨by simpa using hx5, hinp5⟩
    refine ⟨τ6, ?_, by rw [hr6.frame_var "hk" (by decide), hr5.frame_var "hk" (by decide)]; simp [hτ4, hτ3, hτ2, hτ1],
      by rw [hr6.frame_var "hq" (by decide), hq5],
      by rw [hr6.frame_var "hl" (by decide), hr5.frame_var "hl" (by decide)]; simp [hτ4, hτ3, hτ2, hτ1],
      by rw [hw]; exact hx6.2, hinp6⟩
    unfold readTree
    refine (Run.seq (Run.read (by rw [hinp]; rfl)) (Run.seq (Run.read rfl) (Run.seq (Run.read rfl)
      (Run.seq (Run.assign (v := 0) (by simp; omega)) (Run.seq hr5 (Run.ite_true ?_ hr6)))))).mono ?_
    · simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff, hq5]
      exact ⟨0, q + 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp⟩
    · simp only [Cond.size, Expr.size]; omega

/-! ### Frames -/

/-- The command `readArgs` writes only the data of the hooks, the new
arity `ol` and three scratch scalars, and only the array `gt`. -/
def ArgFrame (cmd : Com) : Prop :=
  (∀ y ∈ cmd.wvars, y ∈ ["g1", "g2", "g3", "g4", "ol", "r1", "r2", "r3"]) ∧
    (∀ b ∈ cmd.warrs, b = "gt") ∧ cmd.NoWrite

theorem bfs_noWrite : bfs.NoWrite := by
  simp [bfs, bfsBody, skipList, skipBody, pushList, pushBody, Com.NoWrite]

theorem readTree_noWrite : readTree.NoWrite := by
  simp [readTree, cpList, cpFrame, cpEntries, cpEntry, Com.NoWrite]

end Lax185574Proofs.Words
