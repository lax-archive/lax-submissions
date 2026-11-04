import Lax185574Proofs.CompRam.Leads

/-!
The run of the stack machine as a sequence.

The answers described by `Ans` are determined by the questions: the word
of a type tree determines the tree, so the answer of a rank shift or of a
restriction is a function of the word asked about (`Ans.func`). With the
answer `ansOf G q` chosen for every question, the machine runs along one
trajectory `traj G r j`, and a run `Leads (Ans G) r r' m` is that
trajectory (`leads_traj`). This is the script of the loop driver.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs

/-- The positions of a word of a list of positions below `l`. -/
def decodeJ (w : List ℕ) (l : ℕ) : List (Fin l) :=
  (w.drop 1).filterMap fun v => if h : v < l then some ⟨v, h⟩ else none

theorem decodeJ_toWord {l : ℕ} (J : List (Fin l)) : decodeJ (toWord J) l = J := by
  show (((J.length :: (J.map toWord).flatten)).drop 1).filterMap _ = J
  rw [List.drop_one, List.tail_cons, flatten_map_fin]
  induction J with
  | nil => rfl
  | cons a J ih => simp [ih, a.isLt]

/-- The rank shift as a function of the tree. -/
def fsh : TypeTree → List ℕ
  | ⟨k, q + 1, l, t⟩ => toWord (⟨k + 1, q, l, shiftNode t⟩ : TypeTree)
  | _ => []

/-- The restriction as a function of the tree and the word of the
positions. -/
def fre (T : TypeTree) (wJ : List ℕ) : List ℕ :=
  toWord (restrictTree T.k T.q T.ℓ T.root (decodeJ wJ T.ℓ))

variable {n : ℕ} (G : PartialGraph (Fin n))

theorem fsh_tree (kk d : ℕ) {l : ℕ} (u : Fin l → Fin n) (hl : 1 ≤ l) :
    fsh (tree G kk (d + 1) u) = toWord (tree G (kk + 1) d u) := by
  show toWord (⟨kk + 1, d, l, shiftNode (node G kk (d + 1) u)⟩ : TypeTree) = _
  rw [shiftNode_node G kk d hl u]
  rfl

theorem fre_tree (kk d : ℕ) {l : ℕ} (u : Fin l → Fin n) (J : List (Fin l)) (hJ : J.Nodup) :
    fre (tree G kk d u) (toWord J) = toWord (tree G kk d (fun i => u (J.get i))) := by
  show toWord (restrictTree kk d l (node G kk d u) (decodeJ (toWord J) l)) = _
  rw [decodeJ_toWord, restrictTree_tree G kk d u J hJ]

theorem tree_word_inj {T T' : TypeTree} {r r' : List ℕ} (h : toWord T ++ r = toWord T' ++ r') :
    T = T' ∧ r = r' := by
  haveI := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
  exact prefix_inj' h

/-- **The answers are determined by the questions.** -/
theorem Ans.func {q : Qry} {b b' : List ℕ} (h : Ans G q b) (h' : Ans G q b') : b = b' := by
  cases q with
  | sh w =>
    obtain ⟨kk, d, l, u, h1, -, hw, rfl⟩ := h
    obtain ⟨kk', d', l', u', h1', -, hw', rfl⟩ := h'
    have e := (tree_word_inj (r := []) (r' := []) (by simpa using hw.symm.trans hw')).1
    rw [← fsh_tree G kk d u h1, ← fsh_tree G kk' d' u' h1', e]
  | re w =>
    obtain ⟨kk, d, l, u, J, -, hJ, hw, rfl⟩ := h
    obtain ⟨kk', d', l', u', J', -, hJ', hw', rfl⟩ := h'
    obtain ⟨e1, e2⟩ := tree_word_inj (T := tree G kk d u) (T' := tree G kk' d' u') (r := toWord J)
      (r' := toWord J') (hw.symm.trans hw')
    rw [← fre_tree G kk d u J hJ, ← fre_tree G kk' d' u' J' hJ', e1, e2]
  | ca ws => exact h.trans h'.symm

open Classical in
/-- The answer chosen for a question. -/
noncomputable def ansOf (q : Qry) : List ℕ := if h : ∃ b, Ans G q b then h.choose else []

theorem ansOf_eq {q : Qry} {b : List ℕ} (h : Ans G q b) : ansOf G q = b := by
  have he : ∃ b, Ans G q b := ⟨b, h⟩
  simp only [ansOf, dif_pos he]
  exact Ans.func G he.choose_spec h

/-- The trajectory of the machine with the chosen answers. -/
noncomputable def traj : Res → ℕ → Res
  | r, 0 => r
  | .call S q, j + 1 => traj (round S (ansOf G q)) j
  | r, _ + 1 => r

/-- **A run is the trajectory.** Every state before its end asks a
question with an answer, and after `m` rounds the trajectory is at the
end of the run. -/
theorem leads_traj {r r' : Res} {m : ℕ} (h : Leads (Ans G) r r' m) :
    traj G r m = r' ∧ ∀ j < m, ∃ S q, traj G r j = .call S q ∧ Ans G q (ansOf G q) := by
  induction h with
  | refl r => exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | @step S q b r' m hb _ ih =>
    have ha := ansOf_eq G hb
    refine ⟨by simp only [traj, ha]; exact ih.1, fun j hj => ?_⟩
    cases j with
    | zero => exact ⟨S, q, rfl, by rw [ha]; exact hb⟩
    | succ j =>
      obtain ⟨S', q', h1, h2⟩ := ih.2 j (by omega)
      exact ⟨S', q', by simp only [traj, ha]; exact h1, h2⟩

end Lax185574Proofs.CompRam
