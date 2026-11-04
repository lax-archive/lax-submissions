import Lax185574Proofs.Words.TreeCopy
import Lax185574Proofs.Words.TreeWord
import Lax185574Proofs.Words.SelectLen
import Lax185574Proofs.RamLoop

/-!
The script of the composite that runs a program on every job of a list.

The input is the word `x = toWord js` of a list of jobs, a job being a
word. Round `j` of the glue program sees the input, the state written in
round `j - 1` and the answer `f js[j-1]` of the callee. The state is
`[0, j] ++ fr j`, where `fr j` holds the frames of the answers to the
first `j` jobs, and the query of round `j` is the job `js[j]` itself.
After the last job the glue program writes `0 :: toWord (js.map f)`.

`gA` and `gB` are the arguments of the loop driver before each round,
`gIn` the input of a round and `gOut` its output. `pos js j` is the
position of the frame of job `j` in `x`.
-/

namespace Lax185574Proofs.JobMap

open Lax808846.Ram Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.RamSim

/-- The frames of the answers to the first `j` jobs. -/
def fr (js : List (List ℕ)) (f : List ℕ → List ℕ) (j : ℕ) : List ℕ := frames ((js.map f).take j)

/-- The output of round `j` of the glue program. -/
def gOut (js : List (List ℕ)) (f : List ℕ → List ℕ) (j : ℕ) : List ℕ :=
  if j = js.length then 0 :: toWord (js.map f)
  else [(toWord js).length + 1, (fr js f j).length + 2, (toWord js).length, 0, j] ++ fr js f j ++
    js.getD j []

/-- The state argument of the loop driver before round `j`. -/
def gA (js : List (List ℕ)) (f : List ℕ → List ℕ) : ℕ → List ℕ
  | 0 => lpA0 (toWord js)
  | j + 1 => gOut js f j

/-- The answer argument of the loop driver before round `j`. -/
def gB (js : List (List ℕ)) (f : List ℕ → List ℕ) : ℕ → List ℕ
  | 0 => []
  | j + 1 => f (js.getD j [])

/-- The input of round `j` of the glue program. -/
def gIn (js : List (List ℕ)) (f : List ℕ → List ℕ) (j : ℕ) : List ℕ :=
  if j = 0 then [0, (toWord js).length] ++ toWord js ++ [0]
  else [(toWord js).length + 1, (fr js f (j - 1)).length + 2] ++ toWord js ++ [0, j - 1] ++
    fr js f (j - 1) ++ ((f (js.getD (j - 1) [])).length :: f (js.getD (j - 1) []))

/-- The position of the frame of job `j` in the input. -/
def pos (js : List (List ℕ)) (j : ℕ) : ℕ := 1 + (frames (js.take j)).length

/-! ### The rounds -/

theorem lpU_zero' (x : List ℕ) : lpU x (lpA0 x) [] = [0, x.length] ++ x ++ [0] := by
  simp [lpU, lpA0]

theorem gOut_lt {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j < js.length) :
    gOut js f j = [(toWord js).length + 1, (fr js f j).length + 2, (toWord js).length, 0, j] ++
      fr js f j ++ js[j] := by
  simp [gOut, Nat.ne_of_lt hj, List.getD_eq_getElem?_getD, hj]

theorem gOut_last (js : List (List ℕ)) (f : List ℕ → List ℕ) :
    gOut js f js.length = 0 :: toWord (js.map f) := by
  simp [gOut]

theorem lpU_gA {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j ≤ js.length) :
    lpU (toWord js) (gA js f j) (gB js f j) = gIn js f j := by
  cases j with
  | zero => simp [gA, gB, gIn, lpU_zero']
  | succ j =>
    have hj' : j < js.length := by omega
    simp only [gA, gB, gIn, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, gOut_lt hj']
    simp only [lpU, List.getD_eq_getElem?_getD]
    simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, List.drop_zero, List.take_length, List.drop_succ_cons]
    have : List.take ((fr js f j).length + 2) (0 :: j :: (fr js f j ++ js[j])) =
        0 :: j :: fr js f j := by
      simp
    rw [this]
    simp [hj']

theorem lpQ_gA {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j < js.length) :
    lpQ (gA js f (j + 1)) = js[j] := by
  simp only [gA, gOut_lt hj, lpQ, List.getD_eq_getElem?_getD]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some]
  rw [show 3 + ((fr js f j).length + 2) =
    ([(toWord js).length + 1, (fr js f j).length + 2, (toWord js).length, 0, j] ++ fr js f j).length by
      simp; omega]
  simp

theorem gA_head {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j < js.length) :
    gA js f (j + 1) ≠ [] ∧ (gA js f (j + 1)).head? ≠ some 0 := by
  simp [gA, gOut_lt hj]

theorem gB_succ {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j < js.length) :
    gB js f (j + 1) = f js[j] := by
  simp [gB, List.getD_eq_getElem?_getD, hj]

theorem gIn_succ {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j < js.length) :
    gIn js f (j + 1) = [(toWord js).length + 1, (fr js f j).length + 2] ++ toWord js ++ [0, j] ++
      fr js f j ++ ((f js[j]).length :: f js[j]) := by
  simp [gIn, List.getD_eq_getElem?_getD, hj]

/-! ### The frames of the answers -/

theorem fr_zero (js : List (List ℕ)) (f : List ℕ → List ℕ) : fr js f 0 = [] := by
  simp [fr, frames]

theorem fr_succ {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j < js.length) :
    fr js f (j + 1) = fr js f j ++ ((f js[j]).length :: f js[j]) := by
  have h : j < (js.map f).length := by simpa using hj
  simp only [fr]
  rw [frames_take_succ' h]
  simp

theorem toWord_map (js : List (List ℕ)) (f : List ℕ → List ℕ) :
    toWord (js.map f) = js.length :: fr js f js.length := by
  have h2 : (js.map f).take js.length = js.map f := by simp
  rw [toWord_words, fr, h2, List.length_map]

theorem length_fr_le (js : List (List ℕ)) (f : List ℕ → List ℕ) (j : ℕ) :
    (fr js f j).length ≤ (fr js f js.length).length := by
  have := length_frames_take_le (js.map f) j
  have h2 : (js.map f).take js.length = js.map f := by simp
  simp only [fr, h2]
  exact this

theorem fr_take_mem {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} {y : ℕ}
    (hy : y ∈ fr js f j) : y ∈ fr js f js.length := by
  have h2 : (js.map f).take js.length = js.map f := by simp
  simp only [fr, h2] at hy ⊢
  rw [← List.take_append_drop j (js.map f), frames_append]
  exact List.mem_append_left _ hy

/-- An entry of the frames of the answers is a length of an answer or an
entry of an answer. -/
theorem mem_fr {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} {y : ℕ}
    (hy : y ∈ fr js f j) : ∃ u ∈ js, y = (f u).length ∨ y ∈ f u := by
  simp only [fr, frames, List.mem_flatten, List.mem_map] at hy
  obtain ⟨_, ⟨v, hv, rfl⟩, hy⟩ := hy
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv)
  rcases List.mem_cons.mp hy with h | h
  · exact ⟨u, hu, Or.inl h⟩
  · exact ⟨u, hu, Or.inr h⟩

theorem length_fr_last (js : List (List ℕ)) (f : List ℕ → List ℕ) :
    (fr js f js.length).length = js.length + ((js.map f).map List.length).sum := by
  have h2 : (js.map f).take js.length = js.map f := by simp
  simp only [fr, h2, length_frames, total, List.length_flatten, List.length_map]

/-! ### The input word -/

theorem toWord_jobs (js : List (List ℕ)) : toWord js = js.length :: frames js := toWord_words js

theorem length_toWord_jobs (js : List (List ℕ)) :
    (toWord js).length = 1 + js.length + ((js.map List.length).sum) := by
  rw [length_toWord_words, total, List.length_flatten]

theorem jobs_length_lt (js : List (List ℕ)) : js.length < (toWord js).length := by
  rw [length_toWord_jobs]; omega

theorem drop_pos (js : List (List ℕ)) (j : ℕ) : (toWord js).drop (pos js j) = frames (js.drop j) := by
  have h : frames js = frames (js.take j) ++ frames (js.drop j) := by
    rw [← frames_append, List.take_append_drop]
  rw [toWord_jobs, pos, Nat.add_comm, List.drop_succ_cons, h, List.drop_left]

theorem drop_pos_lt {js : List (List ℕ)} {j : ℕ} (hj : j < js.length) :
    (toWord js).drop (pos js j) = js[j].length :: (js[j] ++ frames (js.drop (j + 1))) := by
  rw [drop_pos, frames_drop hj]

theorem pos_succ {js : List (List ℕ)} {j : ℕ} (hj : j < js.length) :
    pos js (j + 1) = pos js j + 1 + js[j].length := by
  simp only [pos, length_frames_take_succ hj]; omega

theorem getElem?_pos {js : List (List ℕ)} {j : ℕ} (hj : j < js.length) :
    (toWord js)[pos js j]? = some js[j].length := by
  have := congrArg (fun l => l[0]?) (drop_pos_lt hj)
  simpa using this

theorem getElem?_pos_add {js : List (List ℕ)} {j i : ℕ} (hj : j < js.length) (hi : i < js[j].length) :
    (toWord js)[pos js j + 1 + i]? = some js[j][i] := by
  have := congrArg (fun l => l[1 + i]?) (drop_pos_lt hj)
  simp only [List.getElem?_drop] at this
  rw [show pos js j + 1 + i = pos js j + (1 + i) by omega, this, Nat.add_comm 1 i,
    List.getElem?_cons_succ, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem pos_add_le {js : List (List ℕ)} {j : ℕ} (hj : j < js.length) :
    pos js j + 1 + js[j].length ≤ (toWord js).length := by
  have := congrArg List.length (drop_pos_lt hj)
  simp only [List.length_drop, List.length_cons, List.length_append] at this
  omega

theorem mem_job {js : List (List ℕ)} {j : ℕ} (hj : j < js.length) {y : ℕ} (hy : y ∈ js[j]) :
    y ∈ toWord js := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have := getElem?_pos_add hj hi
  exact List.mem_of_getElem? this

theorem length_job_lt {js : List (List ℕ)} {u : List ℕ} (hu : u ∈ js) :
    u.length < (toWord js).length := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
  have := pos_add_le hj
  omega

theorem toWord_jobs_ne (js : List (List ℕ)) : toWord js ≠ [] := by simp [toWord_jobs]

end Lax185574Proofs.JobMap
