import Lax185574Proofs.FarRam.Glue
import Lax185574Proofs.ShiftRam.Answer
import Lax185574Proofs.ShiftRam.Rounds
import Lax185574Proofs.LoopScript


/-!
The script of the far-tree program in the loop driver: the states the
glue program writes, the queries and the answers of the restriction
program, and the inputs of the rounds.
-/

namespace Lax185574Proofs.FarRam

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574.PartialGraphs Lax185574Proofs.RestrictionRam Lax185574Proofs.Simulate
open Lax185574Proofs.EvalRam Lax185574Proofs.RamSim

variable {n : ℕ}

theorem last_answer (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (b : Fin n) :
    tree G k q (fun i => (Fin.snoc u b : Fin (ℓ + 1) → Fin n) ([Fin.last ℓ].get i)) = tree G k q ![b] := by
  congr 1; funext i; rw [Fin.fin_one_eq_zero i]; simp

/-- **The size of an answer.** -/
theorem answer_bound_last (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (b : Fin n)
    (Bz : ℕ) (hc : ∀ v ∈ toWord (node G k q (Fin.snoc u b)), v < Bz)
    (hl : (toWord (node G k q (Fin.snoc u b))).length < Bz) (hℓ : ℓ + 1 < Bz) (hk : k < Bz)
    (hq : q < Bz) :
    (toWord (tree G k q ![b])).length ≤ (toWord (node G k q (Fin.snoc u b))).length + 3 ∧
      ∀ v ∈ toWord (tree G k q ![b]), v < Bz := by
  set μ := node G k q (Fin.snoc u b) with hμ
  set J : List (Fin (ℓ + 1)) := [Fin.last ℓ]
  have hz : tree G k q ![b] = restrictTree k q (ℓ + 1) μ J := by
    rw [restrictTree_tree G k q _ _ (by simp [J]), last_answer]
  have hw : toWord (tree G k q ![b]) = [k, q, J.length] ++
      treeOut (rsub J) (rgsub J) q 0 (toWord μ) 0 := by
    rw [hz, treeOut_restrict J (toWord μ) q 0 μ 0 [] (by simp)]
    rfl
  have hJ : J.length = 1 := rfl
  rw [hw]
  refine ⟨?_, ?_⟩
  · have := length_treeOut_le (rsub J) (rgsub J) q 0 (ℓ + 1) (toWord μ) 0 μ [] (by simp)
    simp; omega
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · simp [hJ] at h; rcases h with rfl | rfl | rfl <;> omega
    · refine treeOut_lt _ _ (toWord μ) hc hl q 0 (ℓ + 1) 0 μ [] (by simp) ?_ ?_ ?_ v h
      · intro tg k' v' r hv' hr
        rcases rsub_le J (by simp [J]) hr with h' | h'
        · have := hc v' hv'; omega
        · omega
      · intro dd _ _ tg k' v' r hv' hr
        rcases rsub_le J (by simp [J]) hr with h' | h'
        · have := hc v' hv'; omega
        · omega
      · intro dd i r _ _ hi hr
        rcases gmap_le J (by simp [J]) hr with h' | h'
        · have := hc i hi; omega
        · omega

/-! ### The script -/

section Script

variable {q ℓ : ℕ} (k : ℕ) (t : Node (q + 1) ℓ)

/-- The answer to the query of extension `j`: the tree of its new vertex. -/
noncomputable def ansW (j : ℕ) : List ℕ :=
  if h : j < (Node.exts t).words.length then
    toWord (lastTree k q ℓ (Classical.choose (getElem_words h)).2)
  else []

/-- The word of the child of extension `j`. -/
def childW (j : ℕ) : List ℕ := ((Node.exts t).words.getD j []).tail

/-- The query of extension `j`. -/
def queryW (j : ℕ) : List ℕ := [k + 1, q, ℓ + 1] ++ childW t j ++ [1, ℓ]

/-- The words read in round `j`: the scatter type and the first `j` answers. -/
noncomputable def wl (S : List (List ℕ)) (j : ℕ) : List (List ℕ) :=
  S ++ (List.range j).map (ansW k t)

/-- The output of the call round `j`. -/
noncomputable def callOut (S : List (List ℕ)) (j : ℕ) : List ℕ :=
  [1, 4 + (wl k t S j).length + total (wl k t S j), (toWord t).length + 3, 0, j + 1, S.length,
    (wl k t S j).length + 1] ++ frames (wl k t S j) ++ queryW k t j

/-- The glue states of the script. -/
noncomputable def scA (x : List ℕ) (S : List (List ℕ)) : ℕ → List ℕ
  | 0 => lpA0 x
  | j + 1 => callOut k t S j

/-- The answers of the script. -/
noncomputable def scB : ℕ → List ℕ
  | 0 => []
  | j + 1 => ansW k t j

theorem wl_succ (S : List (List ℕ)) (j : ℕ) : wl k t S (j + 1) = wl k t S j ++ [ansW k t j] := by
  simp [wl, List.range_succ]

theorem lpQ_callOut (S : List (List ℕ)) (j : ℕ) : lpQ (callOut k t S j) = queryW k t j := by
  have hf := length_frames (wl k t S j)
  have h1 : (callOut k t S j).getD 1 0 = 4 + (wl k t S j).length + total (wl k t S j) := by
    simp [callOut]
  unfold lpQ
  rw [h1]
  unfold callOut
  rw [List.drop_left' (by simp; omega)]

theorem lpU_zero (x : List ℕ) (S : List (List ℕ)) (htw : x = [k, q + 1, ℓ] ++ toWord t ++ toWord S) :
    lpU x (scA k t x S 0) (scB k t 0) =
      [0, x.length, k, q + 1, ℓ] ++ toWord t ++ [] ++ toWord S ++ [0] := by
  show lpU x (lpA0 x) [] = _
  have h : lpU x (lpA0 x) [] = [0, x.length] ++ x ++ [0] := by simp [lpU, lpA0]
  rw [h]
  nth_rewrite 2 [htw]
  simp

theorem lpU_succ (x : List ℕ) (S : List (List ℕ))
    (htw : x = [k, q + 1, ℓ] ++ toWord t ++ toWord S) (j : ℕ) :
    lpU x (scA k t x S (j + 1)) (scB k t (j + 1)) =
      [1, 4 + (wl k t S j).length + total (wl k t S j), k, q + 1, ℓ] ++ toWord t ++
        [0, j + 1, S.length] ++ toWord (wl k t S (j + 1)) ++ [] := by
  have hf := length_frames (wl k t S j)
  set W := wl k t S j
  have hx : (x.drop 0).take ((toWord t).length + 3) = [k, q + 1, ℓ] ++ toWord t := by
    rw [htw, List.drop_zero, List.take_left' (by simp)]
  have hc : callOut k t S j = [1, 4 + W.length + total W, (toWord t).length + 3] ++
      ([0, j + 1, S.length, W.length + 1] ++ frames W) ++ queryW k t j := by simp [callOut, W]
  have hd : ((callOut k t S j).drop 3).take (4 + W.length + total W) =
      [0, j + 1, S.length, W.length + 1] ++ frames W := by
    rw [hc, List.append_assoc, List.drop_left' (by simp), List.take_left' (by simp; omega)]
  have hw : toWord (wl k t S (j + 1)) = (W.length + 1) :: (frames W ++ ((ansW k t j).length :: ansW k t j)) := by
    rw [toWord_words, wl_succ]; simp [W, frames_append, frames]
  have h0 : (callOut k t S j).getD 0 0 = 1 := by simp [callOut]
  have h1 : (callOut k t S j).getD 1 0 = 4 + W.length + total W := by simp [callOut, W]
  have h2 : (callOut k t S j).getD 2 0 = (toWord t).length + 3 := by simp [callOut]
  have h3 : (callOut k t S j).getD 3 0 = 0 := by simp [callOut]
  simp only [scA, scB, lpU, h0, h1, h2, h3, hd, hx, hw]
  simp

end Script

section Genuine

variable (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n)

theorem ans_query (j : ℕ) (hj : j < (Node.exts (node G k (q + 1) u)).words.length) :
    ∃ b : Fin n, queryW k (node G k (q + 1) u) j =
        toWord (tree G (k + 1) q (Fin.snoc u b), [Fin.last ℓ]) ∧
      ansW k (node G k (q + 1) u) j =
        toWord (tree G (k + 1) q (fun i => (Fin.snoc u b : Fin (ℓ + 1) → Fin n) ([Fin.last ℓ].get i))) ∧
      (toWord (node G (k + 1) q (Fin.snoc u b))).IsInfix (toWord (node G k (q + 1) u)) := by
  set t := node G k (q + 1) u
  have hs := Classical.choose_spec (getElem_words hj)
  set a := Classical.choose (getElem_words hj)
  obtain ⟨ha, haw⟩ := hs
  obtain ⟨i, b, -, hab⟩ := (mem_exts_node G k q u a).1 ha
  refine ⟨b, ?_, ?_, ?_⟩
  · have hc : childW t j = toWord (node G (k + 1) q (Fin.snoc u b)) := by
      rw [childW, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simp only [Option.getD_some, ← haw, toWord_ext, List.tail_cons, hab]
    rw [queryW, hc, toWord_tree_pair, toWord_listFin]
    simp [tree]
    rfl
  · rw [ansW, dif_pos hj, last_answer, ← lastTree_node u b]
    show toWord (lastTree k q ℓ a.2) = _
    rw [hab]
  · have hinf := Lax185574Proofs.ShiftRam.child_infix (t := t) ha
    rw [hab] at hinf
    exact hinf

theorem ansOK_genuine :
    AnsOK k q ℓ (node G k (q + 1) u) ((List.range (Node.exts (node G k (q + 1) u)).words.length).map
      (ansW k (node G k (q + 1) u))) := by
  set t := node G k (q + 1) u
  refine ⟨by simp, fun e he a haw => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]
  simp only [Option.map_some, Option.getD_some, ansW, dif_pos he]
  have hs := Classical.choose_spec (getElem_words he)
  have h2 : toWord (Classical.choose (getElem_words he)).2 = toWord a.2 := by
    have := hs.2.trans haw.symm
    rw [toWord_ext, toWord_ext] at this
    exact (List.cons.inj this).2
  have := ((Lax185574Proofs.EncodingInjectivity.prefixFree_node q (ℓ + 1)).prefix_inj _ _ [] []
    (by simpa using h2)).1
  exact congrArg (fun μ => toWord (lastTree k q ℓ μ)) this

theorem entries_three (σ : Finset ((ℕ × TypeTree) × ℕ)) : ∀ w ∈ σ.words, 3 ≤ w.length := by
  intro w hw
  obtain ⟨p, -, rfl⟩ := mem_words.mp hw
  rw [toWord_entry, toWord_typeTree]; simp

theorem exts_pos (hℓ : 1 ≤ ℓ) : 1 ≤ (Node.exts (node G k (q + 1) u)).words.length := by
  obtain ⟨a, ha, -⟩ := Lax185574Proofs.ShiftRam.exists_guard_zero G k q hℓ u
  obtain ⟨e, he, -⟩ := ext_index a ha
  omega

end Genuine

end Lax185574Proofs.FarRam
