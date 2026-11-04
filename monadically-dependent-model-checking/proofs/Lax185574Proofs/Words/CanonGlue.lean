import Lax185574Proofs.Words.JobWord
import Lax185574Proofs.Words.Computes
import Lax185574Proofs.Words.TreeWord
import Lax185574Proofs.Words.Emit
import Lax185574Proofs.Words.ForLoop

/-!
The glue program of the canonical form of a list of jobs. It runs in the
loop driver (`Lax185574Proofs.Simulate.loop_sound`) with the program of
the canonical form of one set as the callee. Round `j` keeps the answers
to the jobs `0, …, j - 1` in its state, and asks for job `j`, or writes
the result once all jobs are answered.

The program reads the input into the array `x` and the answers so far
into the word arrays of `Words/Read.lean`, with the new answer appended
as the last word. If all jobs are answered it writes the entries of the
last item and the answers to its indices. Otherwise it skips job `j` to
find the position of the next job, writes the window, the state and the
answers, and then the query of job `j`, item by item.

The entry bounds `allResults_entry_le`, `jobQuery_entry_le`,
`jobsOut_entry_le` and `glueIn_entry_le` say that every value in the
words of a round is at most `maxEntry x + jobSize js fin` (plus one for
the input of a round), and `glueOut_length_le` bounds the length of the
output of a round.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574.WordEncoding

/-- The input of round `j` of the glue program, as the loop driver
builds it: the input `x`, and from the second round on the state written
in the round before and the answer to the job of that round. -/
def glueIn (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ) : List ℕ :=
  if j = 0 then [0, (toWord (js, fin)).length] ++ toWord (js, fin) ++ [0]
  else [(toWord (js, fin)).length + 1, 3 + (j - 1) + total ((allResults js).take (j - 1))] ++
    toWord (js, fin) ++ (0 :: jobPos js j :: toWord ((allResults js).take (j - 1))) ++
    (((allResults js).getD (j - 1) []).length :: (allResults js).getD (j - 1) [])

/-- The output of round `j`: the result once all jobs are answered, and
otherwise the window, the state and the query of job `j`. -/
def glueOut (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ) : List ℕ :=
  if j = js.length then 0 :: jobsOut js fin
  else [(toWord (js, fin)).length + 1, 3 + j + total ((allResults js).take j), (toWord (js, fin)).length,
      0, jobPos js (j + 1)] ++ toWord ((allResults js).take j) ++
    toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))


/-! ### The word of the jobs -/

theorem glue_toWord_jobsFin (js : List Job) (fin : List ℕ × List ℕ) :
    toWord (js, fin) = js.length :: ((js.map toWord).flatten ++ toWord fin) := rfl

theorem glue_toWord_job (jb : Job) : toWord jb = jb.1 :: jb.2.length :: frames jb.2 := by
  change [jb.1] ++ toWord jb.2 = _
  rw [toWord_words]; rfl

theorem glue_toWord_fin (fin : List ℕ × List ℕ) :
    toWord fin = fin.1.length :: (fin.1 ++ fin.2.length :: fin.2) := by
  change toWord fin.1 ++ toWord fin.2 = _
  rw [toWord_listNat, toWord_listNat]; rfl

theorem glue_jobPos_eq (js : List Job) (j : ℕ) :
    jobPos js j = 1 + ((js.take j).map toWord).flatten.length := by
  simp [jobPos, List.length_flatten, List.map_map, Function.comp_def]

theorem glue_drop_jobPos (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ) :
    (toWord (js, fin)).drop (jobPos js j) = ((js.drop j).map toWord).flatten ++ toWord fin := by
  rw [glue_toWord_jobsFin, glue_jobPos_eq, Nat.add_comm, ← List.drop_drop]
  conv_lhs => rw [← List.take_append_drop j js, List.map_append, List.flatten_append]
  simp

theorem glue_drop_jobPos_lt (js : List Job) (fin : List ℕ × List ℕ) {j : ℕ} (hj : j < js.length) :
    (toWord (js, fin)).drop (jobPos js j) = js[j].1 :: js[j].2.length ::
      (frames js[j].2 ++ (((js.drop (j + 1)).map toWord).flatten ++ toWord fin)) := by
  rw [glue_drop_jobPos, List.drop_eq_getElem_cons hj, List.map_cons, List.flatten_cons, glue_toWord_job]
  simp

theorem glue_drop_jobPos_len (js : List Job) (fin : List ℕ × List ℕ) :
    (toWord (js, fin)).drop (jobPos js js.length) =
      fin.1.length :: (fin.1 ++ fin.2.length :: fin.2) := by
  rw [glue_drop_jobPos, List.drop_length]; simp [glue_toWord_fin]

theorem glue_jobPos_succ (js : List Job) {j : ℕ} (hj : j < js.length) :
    jobPos js (j + 1) = jobPos js j + 2 + (frames js[j].2).length := by
  unfold jobPos
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.map_append, List.sum_append]
  simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, glue_toWord_job,
    List.length_cons]
  omega

theorem glue_jobPos_le (js : List Job) (fin : List ℕ × List ℕ) {j : ℕ} (hj : j ≤ js.length) :
    jobPos js j + (((js.drop j).map toWord).flatten ++ toWord fin).length =
      (toWord (js, fin)).length := by
  have := congrArg List.length (glue_drop_jobPos js fin j)
  rw [List.length_drop] at this
  have h2 : jobPos js j ≤ (toWord (js, fin)).length := by
    rw [glue_jobPos_eq, glue_toWord_jobsFin]
    conv_rhs => rw [← List.take_append_drop j js, List.map_append, List.flatten_append]
    simp; omega
  omega

/-! ### Sizes and entries -/

theorem glue_getElem?_of_drop {X u r : List ℕ} {p k : ℕ} (h : X.drop p = u ++ r) (hk : k < u.length) :
    X[p + k]? = some u[k] := by
  have := congrArg (fun l => l[k]?) h
  simp only [List.getElem?_drop] at this
  rw [this, List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

theorem glue_getElem?_of_drop_cons {X r : List ℕ} {p v : ℕ} (h : X.drop p = v :: r) : X[p]? = some v := by
  have := glue_getElem?_of_drop (u := [v]) (k := 0) (by simpa using h) (by simp)
  simpa using this

theorem glue_le_total_of_mem {ws : List (List ℕ)} {u : List ℕ} (hu : u ∈ ws) : u.length ≤ total ws := by
  rw [total, List.length_flatten]
  exact List.le_sum_of_mem (List.mem_map_of_mem hu)

theorem glue_mem_toWord_words_cases {ws : List (List ℕ)} {v : ℕ} (hv : v ∈ toWord ws) :
    v ≤ (toWord ws).length ∨ ∃ u ∈ ws, v ∈ u := by
  have hl := length_toWord_words ws
  rw [toWord_words] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · left; omega
  · simp only [frames, List.mem_flatten, List.mem_map] at hv
    obtain ⟨_, ⟨u, hu, rfl⟩, hv⟩ := hv
    rcases List.mem_cons.mp hv with rfl | hv
    · left; have := glue_le_total_of_mem hu; omega
    · right; exact ⟨u, hu, hv⟩

theorem glue_total_take_le (ws : List (List ℕ)) (j : ℕ) : total (ws.take j) ≤ total ws := by
  have := off_le_total ws j; simpa [off, total] using this

theorem glue_jobSize_ge (js : List Job) (fin : List ℕ × List ℕ) :
    (toWord (js, fin)).length + js.length + total (allResults js) ≤ jobSize js fin := by
  have := length_allResults js; unfold jobSize; omega

theorem glue_jobSize_query (js : List Job) (fin : List ℕ × List ℕ) {j : ℕ} (hj : j < js.length) :
    (toWord (jobQuery ((allResults js).take j) js[j])).length ≤ jobSize js fin := by
  have h1 : (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length ≤
      ((List.range js.length).map fun j =>
        (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem (List.mem_range.mpr hj))
  have h2 : js.getD j (0, []) = js[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [h2] at h1; unfold jobSize; omega

theorem glue_jobSize_out (js : List Job) (fin : List ℕ × List ℕ) :
    (jobsOut js fin).length ≤ jobSize js fin := by unfold jobSize; omega

theorem glue_three_le_length (js : List Job) (fin : List ℕ × List ℕ) : 3 ≤ (toWord (js, fin)).length := by
  rw [glue_toWord_jobsFin, glue_toWord_fin]; simp; omega

theorem glue_mem_item (js : List Job) (fin : List ℕ × List ℕ) {j : ℕ} (hj : j < js.length) {u : List ℕ}
    (hu : u ∈ js[j].2) {v : ℕ} (hv : v ∈ u) : v ∈ toWord (js, fin) := by
  rw [glue_toWord_jobsFin]
  refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatten.mpr
    ⟨toWord js[j], List.mem_map_of_mem (List.getElem_mem hj), ?_⟩))
  rw [glue_toWord_job]
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
  simp only [frames, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨u, hu, rfl⟩, List.mem_cons_of_mem _ hv⟩

theorem glue_mem_fin1 (js : List Job) (fin : List ℕ × List ℕ) {v : ℕ} (hv : v ∈ fin.1) :
    v ∈ toWord (js, fin) := by
  rw [glue_toWord_jobsFin, glue_toWord_fin]; simp [hv]

theorem glue_mem_fin2 (js : List Job) (fin : List ℕ × List ℕ) {v : ℕ} (hv : v ∈ fin.2) :
    v ∈ toWord (js, fin) := by
  rw [glue_toWord_jobsFin, glue_toWord_fin]; simp [hv]

theorem glue_length_getD_le (js : List Job) (fin : List ℕ × List ℕ) (r : ℕ) :
    ((allResults js).getD r []).length ≤ total (allResults js) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (allResults js)[r]? with
  | none => simp
  | some u => simpa using glue_le_total_of_mem (List.mem_of_getElem? h)

theorem glue_getD_take_mem {Rs : List (List ℕ)} {j r : ℕ} {v : ℕ} (hv : v ∈ (Rs.take j).getD r []) :
    r < j ∧ v ∈ Rs.getD r [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take] at hv
  by_cases h : r < j
  · simp only [h, if_true] at hv; exact ⟨h, by rwa [List.getD_eq_getElem?_getD]⟩
  · simp [h] at hv

/-- An entry of an expanded item is an entry of the item or of an earlier answer. -/
theorem glue_mem_expandItem {Rs : List (List ℕ)} {j f : ℕ} {u : List ℕ} {v : ℕ}
    (hv : v ∈ expandItem (Rs.take j) f u) : v ∈ u ∨ ∃ r < j, v ∈ Rs.getD r [] := by
  unfold expandItem at hv
  split_ifs at hv
  · exact Or.inl hv
  · rcases List.mem_append.mp hv with h | h
    · exact Or.inl (List.mem_of_mem_take h)
    · simp only [List.mem_flatten, List.mem_map] at h
      obtain ⟨_, ⟨r, -, rfl⟩, h⟩ := h
      obtain ⟨hr, h⟩ := glue_getD_take_mem h
      exact Or.inr ⟨r, hr, h⟩

theorem glue_query_entry_le_of (js : List Job) (fin : List ℕ × List ℕ) {j : ℕ} (hj : j < js.length)
    (ih : ∀ r < j, ∀ v ∈ (allResults js).getD r [], v ≤ maxEntry (toWord (js, fin)) + jobSize js fin)
    {w : List ℕ} (hw : w ∈ jobQuery ((allResults js).take j) js[j]) {v : ℕ} (hv : v ∈ w) :
    v ≤ maxEntry (toWord (js, fin)) + jobSize js fin := by
  simp only [jobQuery, List.mem_map] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  rcases glue_mem_expandItem hv with h | ⟨r, hr, h⟩
  · have := le_maxEntry (glue_mem_item js fin hj hu h); omega
  · exact ih r hr v h

/-- **The entries of the answers.** -/
theorem allResults_entry_le (js : List Job) (fin : List ℕ × List ℕ) :
    ∀ j (_ : j < js.length), ∀ v ∈ (allResults js).getD j [],
      v ≤ maxEntry (toWord (js, fin)) + jobSize js fin := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj v hv
    have hR := allResults_getElem? js j hj
    have hj' : j < (allResults js).length := by rw [length_allResults]; exact hj
    have hRj : (allResults js).getD j [] = (allResults js)[j] := by
      simp [List.getD_eq_getElem?_getD, hj']
    have hmem : (allResults js)[j] ∈ allResults js := List.getElem_mem hj'
    rw [List.getElem?_eq_getElem hj', Option.some.injEq] at hR
    rw [hRj] at hv
    have hlen := glue_le_total_of_mem hmem
    have hS := glue_jobSize_ge js fin
    rw [hR, jobAnswer] at hv hlen
    rcases glue_mem_toWord_words_cases hv with h | ⟨w, hw, h⟩
    · omega
    · rw [mem_sortedDistinct] at hw
      exact glue_query_entry_le_of js fin hj (fun r hr => ih r hr (by omega)) hw h

/-- **The entries of the queries.** -/
theorem jobQuery_entry_le (js : List Job) (fin : List ℕ × List ℕ) :
    ∀ j < js.length, ∀ v ∈ toWord (jobQuery ((allResults js).take j) (js.getD j (0, []))),
      v ≤ maxEntry (toWord (js, fin)) + jobSize js fin := by
  intro j hj v hv
  have h2 : js.getD j (0, []) = js[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [h2] at hv
  rcases glue_mem_toWord_words_cases hv with h | ⟨w, hw, h⟩
  · have := glue_jobSize_query js fin hj; omega
  · exact glue_query_entry_le_of js fin hj (fun r hr => allResults_entry_le js fin r (by omega)) hw h

theorem glue_getD_entry_le (js : List Job) (fin : List ℕ × List ℕ) (r : ℕ) :
    ∀ v ∈ (allResults js).getD r [], v ≤ maxEntry (toWord (js, fin)) + jobSize js fin := by
  intro v hv
  by_cases hr : r < js.length
  · exact allResults_entry_le js fin r hr v hv
  · have : (allResults js).getD r [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_allResults]; omega)]; rfl
    rw [this] at hv; simp at hv

/-- **The entries of the result.** -/
theorem jobsOut_entry_le (js : List Job) (fin : List ℕ × List ℕ) :
    ∀ v ∈ jobsOut js fin, v ≤ maxEntry (toWord (js, fin)) + jobSize js fin := by
  intro v hv
  simp only [jobsOut, finalOut, List.mem_append, List.mem_flatten, List.mem_map] at hv
  rcases hv with h | ⟨_, ⟨r, -, rfl⟩, h⟩
  · have := le_maxEntry (glue_mem_fin1 js fin h); omega
  · exact glue_getD_entry_le js fin r v h

/-- The length of an answer. -/
theorem allResults_length_le (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ) :
    ((allResults js).getD j []).length ≤ jobSize js fin := by
  have := glue_length_getD_le js fin j; have := glue_jobSize_ge js fin; omega

theorem glue_take_entry_le (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ) :
    ∀ v ∈ toWord ((allResults js).take j), v ≤ maxEntry (toWord (js, fin)) + jobSize js fin := by
  intro v hv
  rcases glue_mem_toWord_words_cases hv with h | ⟨w, hw, h⟩
  · rw [length_toWord_words] at h
    have := glue_total_take_le (allResults js) j
    have := glue_jobSize_ge js fin
    have := glue_three_le_length js fin
    have : ((allResults js).take j).length ≤ js.length := by simp [length_allResults]
    omega
  · obtain ⟨r, hr, hrw⟩ := List.getElem_of_mem (List.mem_of_mem_take hw)
    exact glue_getD_entry_le js fin r v (by simp [List.getD_eq_getElem?_getD, hr, hrw, h])

theorem glue_length_toWord_take_le (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ) :
    (toWord ((allResults js).take j)).length + 2 ≤ jobSize js fin := by
  rw [length_toWord_words]
  have := glue_total_take_le (allResults js) j
  have := glue_jobSize_ge js fin
  have := glue_three_le_length js fin
  have : ((allResults js).take j).length ≤ js.length := by simp [length_allResults]
  omega

theorem glue_jobPos_le_length (js : List Job) (fin : List ℕ × List ℕ) {j : ℕ} (hj : j ≤ js.length) :
    jobPos js j ≤ (toWord (js, fin)).length := by
  have := glue_jobPos_le js fin hj; omega

/-- **The entries of the input of a round.** -/
theorem glueIn_entry_le (js : List Job) (fin : List ℕ × List ℕ) :
    ∀ j ≤ js.length, ∀ v ∈ glueIn js fin j,
      v ≤ maxEntry (toWord (js, fin)) + jobSize js fin + 1 := by
  intro j hj v hv
  have hS := glue_jobSize_ge js fin
  have h3 := glue_three_le_length js fin
  unfold glueIn at hv
  split_ifs at hv with h0
  · simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      or_assoc] at hv
    rcases hv with h | h | h | h
    · omega
    · omega
    · have := le_maxEntry h; omega
    · omega
  · simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      or_assoc] at hv
    rcases hv with h | h | h | h | h | h | h | h
    · omega
    · have := glue_total_take_le (allResults js) (j - 1); omega
    · have := le_maxEntry h; omega
    · omega
    · have := glue_jobPos_le_length js fin hj; omega
    · have := glue_take_entry_le js fin (j - 1) v h; omega
    · have := allResults_length_le js fin (j - 1); omega
    · have := glue_getD_entry_le js fin (j - 1) v h; omega

/-- **The length of the output of a round.** -/
theorem glueOut_length_le (js : List Job) (fin : List ℕ × List ℕ) :
    ∀ j ≤ js.length, (glueOut js fin j).length ≤ 2 * jobSize js fin + 6 := by
  intro j hj
  unfold glueOut
  split_ifs with h
  · have := glue_jobSize_out js fin; simp; omega
  · have h1 := glue_length_toWord_take_le js fin j
    have h2 := glue_jobSize_query js fin (j := j) (by omega)
    have h3 : js.getD j (0, []) = js[j]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, show j < js.length by omega]
    rw [h3]; simp; omega

/-! ### Evaluation of expressions -/

theorem glue_ev_var {B : ℕ} {σ : Env} {x : String} {a : ℕ} (h : σ.vars x = a) (ha : a < B) :
    (Expr.var x).evalB B σ = some a := by
  rw [← h]; exact evalB_var (by rw [h]; exact ha)

theorem glue_ev_add {B : ℕ} {σ : Env} {e f : Expr} {a b : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (h : a + b < B) : (Expr.add e f).evalB B σ = some (a + b) :=
  evalB_bin he hf h

theorem glue_ev_sub {B : ℕ} {σ : Env} {e f : Expr} {a b : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (h : a - b < B) : (Expr.sub e f).evalB B σ = some (a - b) :=
  evalB_bin he hf h

theorem glue_ev_get {B : ℕ} {σ : Env} {arr : String} {i : Expr} {k v : ℕ} (hi : i.evalB B σ = some k)
    (hk : (σ.arrs arr)[k]? = some v) (hv : v < B) : (Expr.get arr i).evalB B σ = some v :=
  evalB_get hi hk hv

theorem glue_ev_eq {B : ℕ} {σ : Env} {e f : Expr} {a b : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) : (Cond.eq e f).evalB B σ = some (a == b) := evalB_condEq he hf

/-! ### Counting loops with varying round costs -/

theorem glue_sum_range_add (c : ℕ → ℕ) (C N : ℕ) :
    ((List.range N).map fun h => c h + C).sum = ((List.range N).map c).sum + N * C := by
  induction N with
  | zero => simp
  | succ N ih => simp only [List.range_succ, List.map_append, List.sum_append, ih]; simp; ring

/-- **The counting loop rule with round costs.** Round `k` costs at most `c k`. -/
theorem glue_forUp_sum {B : ℕ} {i : String} {e : Expr} {body : Com} {N : ℕ} (c : ℕ → ℕ)
    (I : ℕ → Env → Prop) {σ : Env} (hN : N < B)
    (he : ∀ k ≤ N, ∀ τ, I k τ → τ.vars i = k → e.evalB B τ = some N)
    (h0 : I 0 (σ.setVar i 0))
    (hstep : ∀ k < N, ∀ τ, I k τ → τ.vars i = k →
      ∃ τ', Run B body τ τ' (c k) ∧ τ'.vars i = k ∧ I (k + 1) (τ'.setVar i (k + 1))) :
    ∃ σ', Run B (forUp i e body) σ σ'
        (((List.range N).map c).sum + N * (e.size + 7) + e.size + 5) ∧ I N σ' ∧ σ'.vars i = N := by
  let J : Env → Prop := fun τ => ∃ k ≤ N, τ.vars i = k ∧ I k τ
  let Φ : Env → ℕ := fun τ => (((List.range N).drop (τ.vars i)).map fun h => c h + (e.size + 7)).sum
  obtain ⟨σ', K, hrun, ⟨k, hk, hik, hI⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var i) e)
      (c := .seq body (.assign i (.add (.var i) (.lit 1)))) J Φ
      (fun τ ⟨k, hk, hik, hI⟩ => ⟨_, evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)⟩)
      (by
        rintro τ ⟨k, hk, hik, hI⟩ hc
        have hkN : k < N := by
          rw [evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)] at hc
          simp only [Option.some.injEq, decide_eq_true_eq] at hc
          omega
        obtain ⟨τ', hr, hi', hI'⟩ := hstep k hkN τ hI hik
        refine ⟨τ'.setVar i (k + 1), c k + 4, (Run.seq hr (Run.assign ?_)).mono (by simp),
          ⟨k + 1, hkN, by simp, hI'⟩, ?_⟩
        · simp [hi']; omega
        · have hd : (List.range N).drop k = k :: (List.range N).drop (k + 1) := by
            rw [List.drop_eq_getElem_cons (by simpa using hkN)]; simp
          simp only [Φ, hik, vars_setVar, if_true, hd, List.map_cons, List.sum_cons, size_condLt,
            size_var]
          omega)
      (show J (σ.setVar i 0) from ⟨0, Nat.zero_le _, by simp, h0⟩)
  have hkN : k = N := by
    rw [evalB_condLt (evalB_var (by omega)) (he k hk σ' hI hik)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  rw [hkN] at hI hik
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono ?_, hI, hik⟩
  have h1 : Φ (σ.setVar i 0) = ((List.range N).map c).sum + N * (e.size + 7) := by
    simp only [Φ, vars_setVar, if_true, List.drop_zero, glue_sum_range_add]
  simp only [size_condLt, size_var] at hK
  simp only [size_lit]
  omega

/-! ### Reading the input into the array `x` -/

def glueReadXBody : Com := .seq (.read "w") (.store "x" (.var "i") (.var "w"))

def glueReadX : Com := forUp "i" (.var "nx") glueReadXBody

theorem glue_readX_run {B : ℕ} (u rest : List ℕ) (hu : ∀ v ∈ u, v < B) (huB : u.length < B) (σ : Env)
    (hnx : σ.vars "nx" = u.length) (hinp : σ.inp = u ++ rest)
    (hx : σ.arrs "x" = List.replicate u.length 0) :
    ∃ σ', Run B glueReadX σ σ' (u.length * 13 + 6) ∧ σ'.arrs "x" = u ∧ σ'.inp = rest := by
  obtain ⟨σ', hr, ⟨-, hin, hxa⟩, -⟩ := forUp_run (B := B) (i := "i") (e := .var "nx")
    (body := glueReadXBody) (N := u.length) (K := 4)
    (fun k τ => τ.vars "nx" = u.length ∧ τ.inp = u.drop k ++ rest ∧
      τ.arrs "x" = u.take k ++ (List.replicate u.length 0).drop k)
    (σ := σ) huB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨hI.1.symm, by rw [hI.1]; exact huB⟩)
    ⟨by simp [hnx], by simp [hinp], by simp [hx]⟩
    (fun k hk τ ⟨hn', hin, hxa⟩ hik => by
      have hin' : τ.inp = u[k] :: (u.drop (k + 1) ++ rest) := by
        rw [hin, List.drop_eq_getElem_cons hk]; rfl
      have huk : u[k] < B := hu _ (List.getElem_mem hk)
      refine ⟨({ τ.setVar "w" u[k] with inp := u.drop (k + 1) ++ rest } : Env).setArr "x" k u[k],
        (Run.seq (Run.read hin') (Run.store (idx := k) (v := u[k]) ?_ ?_ ?_)).mono (by simp),
        by simp [hik], by simp [hn'], by simp, ?_⟩
      · simp [hik]; omega
      · simp; exact huk
      · simp [hxa]; omega
      · simp only [arrs_setVar, arrs_setArr, if_true]
        change (τ.arrs "x").set k u[k] = _
        rw [hxa, set_prefix' (by simp; omega) (by simp; omega), List.take_add_one,
          List.getElem?_eq_getElem hk]
        simp)
  refine ⟨σ', hr.mono (by simp; omega), ?_, by simpa using hin⟩
  rw [hxa]; simp

/-! ### Reading the answers -/

/-- Read the list of the answers so far and the new answer, as one list. -/
def glueReadAns : Com :=
  .seq (.read "m") (.seq (.assign "m" (.add (.var "m") (.lit 1))) (.seq (.assign "i" (.lit 0))
    (.seq (.assign "p" (.lit 0)) (.while (.lt (.var "i") (.var "m")) readWord))))

theorem glue_readAns_run {B : ℕ} {ws : List (List ℕ)} {b rest : List ℕ} {σ : Env}
    (hinp : σ.inp = toWord ws ++ (b.length :: b) ++ rest)
    (hoa : total (ws ++ [b]) ≤ (σ.arrs "a").length) (host : ws.length + 1 ≤ (σ.arrs "st").length)
    (holn : ws.length + 1 ≤ (σ.arrs "ln").length)
    (hB : (toWord (ws ++ [b])).length < B) (hv : ∀ v ∈ toWord (ws ++ [b]), v < B) :
    ∃ σ', Run B glueReadAns σ σ' (21 * (toWord (ws ++ [b])).length + 20) ∧
      σ'.vars "m" = ws.length + 1 ∧ σ'.vars "p" = total (ws ++ [b]) ∧ WordsAt (ws ++ [b]) σ' := by
  set ws' := ws ++ [b] with hws'
  have hl' : ws'.length = ws.length + 1 := by simp [hws']
  have hlenB := length_toWord_words ws'
  have hinp' : σ.inp = ws.length :: (frames ws' ++ rest) := by
    rw [hinp, toWord_words, hws', frames_append]; simp [frames]
  set σ0 : Env := (((({ σ.setVar "m" ws.length with inp := frames ws' ++ rest }).setVar "m"
    (ws.length + 1)).setVar "i" 0).setVar "p" 0) with hσ0
  have hI0 : ReadInv ws' (σ.arrs "a") (σ.arrs "st") (σ.arrs "ln") rest σ0 := by
    refine ⟨0, by omega, by simp [hσ0], by simp [hσ0, hl'], by simp [hσ0, off], by simp [hσ0], ?_, ?_, ?_⟩
    · simp [hσ0, off]
    · simp [hσ0]
    · simp [hσ0]
  obtain ⟨σ', K, hrun, ⟨i, hile, hi, hm, hp, -, ha, hst, hln⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "i") (.var "m")) (c := readWord)
      (ReadInv ws' (σ.arrs "a") (σ.arrs "st") (σ.arrs "ln") rest)
      (fun τ => 21 * (ws'.length - τ.vars "i") + 16 * (total ws' - τ.vars "p"))
      (fun τ ⟨i, hile, hi, hm, _⟩ => evalB_condLt_vars (by rw [hi]; omega) (by rw [hm]; omega))
      (fun τ hI hc => readWord_step hoa (by omega) (by omega) hB hv hI hc) hI0
  have hiw : i = ws'.length := by
    have := le_of_condLt_false hfalse; rw [hi, hm] at this; omega
  subst hiw
  refine ⟨σ', (Run.seq (Run.read hinp') (Run.seq (Run.assign (v := ws.length + 1) ?_)
    (Run.seq (Run.assign (v := 0) (by simp; omega))
    (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun)))).mono ?_, by rw [hm, hl'], ?_, ?_⟩
  · simp; omega
  · have : σ0.vars "i" = 0 := by simp [hσ0]
    have : σ0.vars "p" = 0 := by simp [hσ0]
    simp only [Cond.size, Expr.size] at hK
    simp only [Expr.size]
    rw [hlenB]
    have : total ws' ≤ (toWord ws').length := by rw [hlenB]; omega
    omega
  · rw [hp, off_length]; rfl
  · rw [List.take_length] at ha hln
    rw [off_length] at ha
    exact wordsAt_of_arrs ha hst hln

/-! ### Writing a word without its length -/

/-- Write the entries of word `ow`. -/
def glueWriteRaw : Com :=
  .seq (.assign "pa" (.get "st" (.var "ow"))) (.seq (.assign "la" (.get "ln" (.var "ow")))
    (.seq (.assign "k" (.lit 0)) (.while (.lt (.var "k") (.var "la")) writeEntry)))

theorem glue_writeRaw_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) {i : ℕ} (hi : σ.vars "ow" = i) (hil : i < ws.length) :
    ∃ σ', Run B glueWriteRaw σ σ' (13 * ws[i].length + 12) ∧ σ'.out = σ.out ++ ws[i] := by
  have hoi := off_add_le hil
  have hlen := hb.len
  generalize hu : ws[i] = u at hoi
  have hea : ∀ k (h : k < u.length), (σ.arrs "a")[off ws i + k]? = some u[k] := by
    subst hu; exact hw.a i hil
  have hent : ∀ x ∈ u, x < B := by subst hu; exact hb.ent _ (List.getElem_mem hil)
  have hln : (σ.arrs "ln")[i]? = some u.length := by subst hu; exact hw.ln i hil
  set σ0 : Env := (σ.setVar "pa" (off ws i)).setVar "la" u.length with hσ0
  let I : Env → Prop := fun τ => τ.vars "pa" = off ws i ∧ τ.vars "la" = u.length ∧
    τ.vars "k" ≤ u.length ∧ τ.arrs "a" = σ.arrs "a" ∧
    τ.out = σ.out ++ u.take (τ.vars "k")
  obtain ⟨σ', hloop, ⟨hpa, hla, hkle, ha, hout⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "k") (.var "la")) (c := writeEntry) I
      (fun τ => u.length - τ.vars "k") 9
      (fun τ ⟨_, hla, hkle, _⟩ => evalB_condLt_vars (by omega) (by rw [hla]; omega))
      (by
        rintro τ ⟨hpa, hla, hkle, ha, hout⟩ hc
        have hk : τ.vars "k" < u.length := by
          have := lt_of_condLt_true hc; rwa [hla] at this
        have hget : (τ.arrs "a")[off ws i + τ.vars "k"]? = some u[τ.vars "k"] := by
          rw [ha]; exact hea _ hk
        refine ⟨_, Run.seq (Run.write (v := u[τ.vars "k"]) ?_) (Run.assign (v := τ.vars "k" + 1) ?_),
          ⟨by simp [hpa], by simp [hla], by simp; omega, by simp [ha], ?_⟩, by simp; omega⟩
        · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, hpa]
          exact ⟨_, ⟨_, _, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by simp only [Bop.apply_add]; omega⟩,
            hget, hent _ (List.getElem_mem hk)⟩
        · simp; omega
        · simp only [vars_setVar, if_true]
          rw [hout, List.take_add_one, List.getElem?_eq_getElem hk]
          simp)
      (show I (σ0.setVar "k" 0) by
        refine ⟨by simp [hσ0], by simp [hσ0], by simp, by simp [hσ0], by simp [hσ0]⟩)
  have hku : σ'.vars "k" = u.length := by
    have := le_of_condLt_false hfalse; rw [hla] at this; omega
  refine ⟨σ', ?_, by rw [hout, hku, List.take_length]⟩
  unfold glueWriteRaw
  refine (Run.seq (Run.assign (v := off ws i) ?_) (Run.seq (Run.assign (v := u.length) ?_)
    (Run.seq (Run.assign (v := 0) ?_) hloop))).mono ?_
  · simp only [evalB_get_iff, evalB_var_iff, hi]
    exact ⟨i, ⟨rfl, by omega⟩, hw.st i hil, by omega⟩
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    exact ⟨i, ⟨by simp [hi], by simp [hi]; omega⟩, hln, by omega⟩
  · simp; omega
  · simp; omega

/-! ### Writing a part of the input -/

/-- A loop that writes the values `f 0, …, f (N − 1)`. -/
theorem glue_writeLoop_run' {B N : ℕ} {i m : String} {e : Expr} (f : ℕ → ℕ) (P : Env → Prop)
    (hNB : N < B) (hm : m ≠ i)
    (hPw : ∀ τ (o : List ℕ), P τ → P { τ with out := o })
    (hPi : ∀ τ k, P τ → P (τ.setVar i k))
    (hmN : ∀ τ, P τ → τ.vars m = N)
    (he : ∀ τ, P τ → τ.vars i < N → e.evalB B τ = some (f (τ.vars i))) (σ : Env) (hσ : P σ) :
    ∃ σ', Run B (forUp i (.var m) (.write e)) σ σ' (N * (e.size + 9) + 6) ∧ P σ' ∧
      σ'.out = σ.out ++ (List.range N).map f := by
  obtain ⟨σ', hr, ⟨hP, hout⟩, -⟩ := forUp_run (B := B) (i := i) (e := .var m) (body := .write e)
    (N := N) (K := 1 + e.size) (fun k τ => P τ ∧ τ.out = σ.out ++ (List.range k).map f) hNB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨(hmN τ hI.1).symm, by rw [hmN τ hI.1]; exact hNB⟩)
    ⟨hPi σ 0 hσ, by simp⟩
    (fun k hk τ hI hik => by
      refine ⟨{ τ with out := τ.out ++ [f k] }, Run.write ?_, by simpa using hik, ?_, ?_⟩
      · rw [← hik]; exact he τ hI.1 (by omega)
      · exact hPi _ _ (hPw τ _ hI.1)
      · simp [hI.2, List.range_succ])
  exact ⟨σ', hr.mono (by simp only [Expr.size]; ring_nf; omega), hP, hout⟩

theorem glue_map_range_drop {X u r : List ℕ} {s : ℕ} (h : X.drop s = u ++ r) :
    (List.range u.length).map (fun k => X.getD (s + k) 0) = u := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, glue_getElem?_of_drop h (by simpa using h1)]
  rfl

theorem glue_sum_range_getD (l : List ℕ) (g : ℕ → ℕ) :
    ((List.range l.length).map fun h => g (l.getD h 0)).sum = (l.map g).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp at h1
  simp [List.getD_eq_getElem?_getD, h1]

theorem glue_take_succ_map_flatten {α : Type} (l : List α) (g : α → List ℕ) {k : ℕ} (hk : k < l.length) :
    ((l.take (k + 1)).map g).flatten = ((l.take k).map g).flatten ++ g l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [List.map_append, List.flatten_append, Option.toList_some, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil]

/-! ### The state between the phases -/

/-- What the first two phases leave: the input in `x`, the answers to
the first `j` jobs in the word arrays, and the position of job `j`. -/
structure glueGCtx (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ) (σ : Env) : Prop where
  x : σ.arrs "x" = toWord (js, fin)
  w : WordsAt ((allResults js).take j) σ
  m : σ.vars "m" = j
  p : σ.vars "p" = total ((allResults js).take j)
  ptr : σ.vars "ptr" = jobPos js j
  nx : σ.vars "nx" = (toWord (js, fin)).length

theorem glue_getElem?_getD' {X : List ℕ} {k : ℕ} (h : k < X.length) : X[k]? = some (X.getD k 0) := by
  simp [List.getD_eq_getElem?_getD, h]

theorem glue_getD_lt {X : List ℕ} {B : ℕ} (hX : ∀ v ∈ X, v < B) (hB : 0 < B) (k : ℕ) : X.getD k 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases h : X[k]? with
  | none => simpa using hB
  | some v => simpa using hX v (List.mem_of_getElem? h)

theorem glue_wordsBound_take {B : ℕ} (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ)
    (hBB : maxEntry (toWord (js, fin)) + jobSize js fin + 4 < B) :
    WordsBound B ((allResults js).take j) where
  len := by
    have := glue_total_take_le (allResults js) j
    have := glue_jobSize_ge js fin
    have : ((allResults js).take j).length ≤ js.length := by simp [length_allResults]
    omega
  ent u hu x hx := by
    obtain ⟨r, hr, hrw⟩ := List.getElem_of_mem (List.mem_of_mem_take hu)
    have := glue_getD_entry_le js fin r x (by simp [List.getD_eq_getElem?_getD, hr, hrw, hx])
    omega
  three := by omega

theorem glue_x_lt {B : ℕ} (js : List Job) (fin : List ℕ × List ℕ)
    (hBB : maxEntry (toWord (js, fin)) + jobSize js fin + 4 < B) : ∀ v ∈ toWord (js, fin), v < B := by
  intro v hv; have := le_maxEntry hv; omega

theorem glue_xlen_lt {B : ℕ} (js : List Job) (fin : List ℕ × List ℕ)
    (hBB : maxEntry (toWord (js, fin)) + jobSize js fin + 4 < B) : (toWord (js, fin)).length + 4 < B := by
  have := glue_jobSize_ge js fin; omega

/-! ### The last round: the result -/

/-- Write the answers to the indices of the last item. -/
def glueFinRefs : Com :=
  forUp "e" (.var "nr") (.seq (.assign "ow" (.get "x" (.add (.add (.var "r") (.lit 1)) (.var "e"))))
    glueWriteRaw)

/-- Write the result: the entries of the last item, then the answers to
its indices. -/
def glueFinalCmd : Com :=
  .seq (.write (.lit 0)) (.seq (.assign "q" (.get "x" (.var "ptr")))
    (.seq (forUp "e" (.var "q") (.write (.get "x" (.add (.add (.var "ptr") (.lit 1)) (.var "e")))))
      (.seq (.assign "r" (.add (.add (.var "ptr") (.lit 1)) (.var "q")))
        (.seq (.assign "nr" (.get "x" (.var "r"))) glueFinRefs))))

theorem glue_final_run {B : ℕ} (js : List Job) (fin : List ℕ × List ℕ) (hwf : JobsWF js fin)
    (hBB : maxEntry (toWord (js, fin)) + jobSize js fin + 4 < B) {σ : Env}
    (hc : glueGCtx js fin js.length σ) :
    ∃ σ', Run B glueFinalCmd σ σ' (60 * (jobSize js fin + 1) ^ 2) ∧ σ'.out = σ.out ++ 0 :: jobsOut js fin := by
  have hXv := glue_x_lt js fin hBB
  have hXB := glue_xlen_lt js fin hBB
  have hS := glue_jobSize_ge js fin
  have hWR : (allResults js).take js.length = allResults js :=
    List.take_of_length_le (by rw [length_allResults])
  have hw := hc.w
  rw [hWR] at hw
  have hb := glue_wordsBound_take (B := B) js fin js.length hBB
  rw [hWR] at hb
  have hRl := length_allResults js
  have hd := glue_drop_jobPos_len js fin
  have hpl := glue_jobPos_le_length js fin (le_refl js.length)
  have hx := hc.x
  have hptr := hc.ptr
  clear hc
  generalize toWord (js, fin) = X at *
  generalize jobPos js js.length = ptr at *
  generalize jobSize js fin = S at *
  obtain ⟨l, rf⟩ := fin
  simp only at hd hwf ⊢
  have hlen := congrArg List.length hd
  simp only [List.length_drop, List.length_cons, List.length_append] at hlen
  -- the entries
  have hd1 : X.drop (ptr + 1) = l ++ (rf.length :: rf) := by
    have := drop_add_of_drop (u := [l.length]) (r := l ++ rf.length :: rf) (by rw [hd]; rfl)
    simpa using this
  have hd2 : X.drop (ptr + 1 + l.length) = rf.length :: rf := drop_add_of_drop hd1
  have hd3 : X.drop (ptr + 1 + l.length + 1) = rf ++ [] := by
    have := drop_add_of_drop (u := [rf.length]) (r := rf) (by rw [hd2]; rfl)
    simpa using this
  set σ1 : Env := { σ with out := σ.out ++ [0] } with hσ1
  set σ2 := σ1.setVar "q" l.length with hσ2
  have r12 : Run B (.assign "q" (.get "x" (.var "ptr"))) σ1 σ2 3 :=
    (Run.assign (glue_ev_get (glue_ev_var (a := ptr) (by simp [hσ1, hptr]) (by omega))
      (by simp [hσ1, hx]; exact glue_getElem?_of_drop_cons hd) (by omega))).mono (by simp)
  obtain ⟨σ3, r3, ⟨hx3, hp3, hq3⟩, hout3⟩ := glue_writeLoop_run' (B := B) (N := l.length) (i := "e") (m := "q")
    (e := .get "x" (.add (.add (.var "ptr") (.lit 1)) (.var "e"))) (fun k => X.getD (ptr + 1 + k) 0)
    (fun τ => τ.arrs "x" = X ∧ τ.vars "ptr" = ptr ∧ τ.vars "q" = l.length) (by omega) (by decide)
    (fun τ o h => h) (fun τ k h => ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2⟩)
    (fun τ h => h.2.2)
    (fun τ h hi => glue_ev_get (glue_ev_add (glue_ev_add (glue_ev_var h.2.1 (by omega)) (evalB_lit (by omega)) (by omega))
      (evalB_var (by omega)) (by omega)) (by rw [h.1]; exact glue_getElem?_getD' (by omega))
      (glue_getD_lt hXv (by omega) _))
    σ2 ⟨by simp [hσ2, hσ1, hx], by simp [hσ2, hσ1, hptr], by simp [hσ2]⟩
  rw [glue_map_range_drop hd1] at hout3
  set σ4 := σ3.setVar "r" (ptr + 1 + l.length) with hσ4
  have r4 : Run B (.assign "r" (.add (.add (.var "ptr") (.lit 1)) (.var "q"))) σ3 σ4 6 :=
    (Run.assign (glue_ev_add (glue_ev_add (glue_ev_var hp3 (by omega)) (evalB_lit (by omega)) (by omega))
      (glue_ev_var hq3 (by omega)) (by omega))).mono (by simp)
  set σ5 := σ4.setVar "nr" rf.length with hσ5
  have r5 : Run B (.assign "nr" (.get "x" (.var "r"))) σ4 σ5 3 :=
    (Run.assign (glue_ev_get (glue_ev_var (a := ptr + 1 + l.length) (by simp [hσ4]) (by omega))
      (by simp [hσ4, hx3]; exact glue_getElem?_of_drop_cons hd2) (by omega))).mono (by simp)
  have hw5 : WordsAt (allResults js) σ5 := by
    refine hw.of_arrs ?_ ?_ ?_ <;>
    · simp only [hσ5, hσ4, arrs_setVar]
      rw [r3.frame_arr _ (by decide)]; simp [hσ2, hσ1]
  obtain ⟨σ6, r6, ⟨-, -, -, -, hout6⟩, -⟩ := forUp_run (B := B) (i := "e") (e := .var "nr")
    (body := .seq (.assign "ow" (.get "x" (.add (.add (.var "r") (.lit 1)) (.var "e")))) glueWriteRaw)
    (N := rf.length) (K := 13 * S + 19)
    (fun k τ => τ.arrs "x" = X ∧ WordsAt (allResults js) τ ∧ τ.vars "r" = ptr + 1 + l.length ∧
      τ.vars "nr" = rf.length ∧ τ.out = σ5.out ++ ((rf.take k).map fun r => (allResults js).getD r []).flatten)
    (σ := σ5) (by omega)
    (fun k _ τ hI _ => glue_ev_var hI.2.2.2.1 (by omega))
    ⟨by simp [hσ5, hσ4, hx3], hw5.of_arrs rfl rfl rfl, by simp [hσ5, hσ4], by simp [hσ5], by simp⟩
    (fun k hk τ ⟨hxτ, hwτ, hrτ, hnrτ, houtτ⟩ hik => by
      have hrk : rf[k] < (allResults js).length := by
        rw [hRl]; exact hwf.2 _ (List.getElem_mem hk)
      have hget0 : X[ptr + 1 + l.length + 1 + k]? = some rf[k] :=
        glue_getElem?_of_drop hd3 (by simpa using hk)
      have hget : (τ.arrs "x")[ptr + 1 + l.length + 1 + k]? = some rf[k] := by rw [hxτ]; exact hget0
      have hv : rf[k] < B := hXv _ (List.mem_of_getElem? hget0)
      obtain ⟨τ2, r2, hout2⟩ := glue_writeRaw_run (B := B) (σ := τ.setVar "ow" rf[k])
        (hwτ.of_arrs rfl rfl rfl) hb (i := rf[k]) (by simp) hrk
      have hlen2 := glue_le_total_of_mem (List.getElem_mem hrk)
      have hτ1 : τ.setVar "ow" rf[k] = τ.setVar "ow" rf[k] := rfl
      refine ⟨τ2, (Run.seq (Run.assign (glue_ev_get (glue_ev_add (glue_ev_add (glue_ev_var hrτ (by omega))
        (evalB_lit (by omega)) (by omega)) (glue_ev_var hik (by omega)) (by omega)) hget
        hv)) r2).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [size_get, size_add, size_var, size_lit]; omega
      · rw [r2.frame_var "e" (by decide)]; simp [hik]
      · simp only [arrs_setVar]; rw [r2.frame_arr "x" (by decide)]; simp [hxτ]
      · refine hwτ.of_arrs ?_ ?_ ?_ <;>
        · simp only [arrs_setVar]; rw [r2.frame_arr _ (by decide)]; simp
      · simp only [vars_setVar]; rw [r2.frame_var "r" (by decide)]; simp [hrτ]
      · simp only [vars_setVar]; rw [r2.frame_var "nr" (by decide)]; simp [hnrτ]
      · simp only [out_setVar]
        rw [hout2, out_setVar, houtτ, glue_take_succ_map_flatten _ _ hk]
        simp [List.getD_eq_getElem?_getD, hrk])
  refine ⟨σ6, ?_, ?_⟩
  · unfold glueFinalCmd glueFinRefs
    refine (Run.seq (Run.write (v := 0) (by simp; omega)) (Run.seq r12 (Run.seq r3 (Run.seq r4
      (Run.seq r5 r6))))).mono ?_
    simp only [size_lit, size_get, size_add, size_var]
    have : l.length ≤ S := by omega
    have : rf.length ≤ S := by omega
    nlinarith
  · rw [hout6, List.take_length]
    simp only [hσ5, hσ4, out_setVar, hout3, hσ2, hσ1, jobsOut, finalOut]
    simp [allResults]

/-! ### One item of the query -/

theorem glue_take_succ_map_sum {α : Type} (l : List α) (g : α → ℕ) {k : ℕ} (hk : k < l.length) :
    ((l.take (k + 1)).map g).sum = ((l.take k).map g).sum + g l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [List.map_append, List.sum_append, Option.toList_some, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

theorem glue_sum_take_map_le {α : Type} (l : List α) (g : α → ℕ) (k : ℕ) :
    ((l.take k).map g).sum ≤ (l.map g).sum := by
  conv_rhs => rw [← List.take_append_drop k l, List.map_append, List.sum_append]
  omega

theorem glue_sum_map_mul (l : List ℕ) (g : ℕ → ℕ) (c : ℕ) :
    (l.map fun x => c * g x).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_add]

theorem glue_sum_range_lin (R : List ℕ) (g : ℕ → ℕ) :
    ((List.range R.length).map fun h => 13 * g (R.getD h 0) + 19).sum =
      13 * (R.map g).sum + R.length * 19 := by
  rw [glue_sum_range_add, glue_sum_map_mul (List.range R.length) (fun h => g (R.getD h 0)) 13, glue_sum_range_getD]

theorem glue_ev_subE {B : ℕ} {σ : Env} {e f : Expr} {a b c : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (hc : a - b = c) (h : c < B) : (Expr.sub e f).evalB B σ = some c := by
  subst hc; exact evalB_bin he hf h

/-- Copy an item verbatim. -/
def glueCopyFrame : Com :=
  .seq (.write (.var "lu")) (forUp "h" (.var "lu") (.write (.get "x" (.add (.add (.var "fp") (.lit 1)) (.var "h")))))

/-- The total length of the answers to the indices of an item. -/
def glueSumLoop : Com :=
  forUp "h" (.sub (.var "lu") (.lit 1))
    (.assign "s" (.add (.var "s") (.get "ln" (.get "x" (.add (.add (.var "fp") (.lit 2)) (.var "h"))))))

/-- Write the answers to the indices of an item. -/
def glueRefLoop : Com :=
  forUp "h" (.sub (.var "lu") (.lit 1))
    (.seq (.assign "ow" (.get "x" (.add (.add (.var "fp") (.lit 2)) (.var "h")))) glueWriteRaw)

/-- Expand an item: its length, its guard, and the answers to its indices. -/
def glueExpFrame : Com :=
  .seq (.assign "s" (.lit 1)) (.seq glueSumLoop (.seq (.write (.var "s"))
    (.seq (.write (.get "x" (.add (.var "fp") (.lit 1)))) glueRefLoop)))

/-- Write the word of the item at `fp` and move `fp` to the next item. -/
def glueFrameCmd : Com :=
  .seq (.assign "lu" (.get "x" (.var "fp")))
    (.seq (.ite (.eq (.var "f") (.lit 0)) glueCopyFrame glueExpFrame)
      (.assign "fp" (.add (.add (.var "fp") (.var "lu")) (.lit 1))))

theorem glue_frameCmd_run {B : ℕ} {W : List (List ℕ)} {X u r : List ℕ} {f q : ℕ} {τ : Env}
    (hx : τ.arrs "x" = X) (hw : WordsAt W τ) (hb : WordsBound B W) (hf : τ.vars "f" = f)
    (hfp : τ.vars "fp" = q) (hd : X.drop q = u.length :: (u ++ r)) (hne : f ≠ 0 → u ≠ [])
    (href : f ≠ 0 → ∀ r' ∈ u.drop 1, r' < W.length)
    (hXv : ∀ v ∈ X, v < B) (hXB : X.length + 4 < B) (hvB : (expandItem W f u).length + 4 < B)
    (hfB : f < B) :
    ∃ τ', Run B glueFrameCmd τ τ' (50 * (u.length + (expandItem W f u).length) + 60) ∧
      τ'.vars "fp" = q + u.length + 1 ∧
      τ'.out = τ.out ++ ((expandItem W f u).length :: expandItem W f u) := by
  have hlen := congrArg List.length hd
  simp only [List.length_drop, List.length_cons, List.length_append] at hlen
  have hd1 : X.drop (q + 1) = u ++ r := by
    have := drop_add_of_drop (u := [u.length]) (r := u ++ r) (by rw [hd]; rfl)
    simpa using this
  set τ1 := τ.setVar "lu" u.length with hτ1
  have r1 : Run B (.assign "lu" (.get "x" (.var "fp"))) τ τ1 3 :=
    (Run.assign (glue_ev_get (glue_ev_var (a := q) hfp (by omega)) (by rw [hx]; exact glue_getElem?_of_drop_cons hd)
      (by omega))).mono (by simp)
  have hx1 : τ1.arrs "x" = X := by simp [hτ1, hx]
  have hfp1 : τ1.vars "fp" = q := by simp [hτ1, hfp]
  have hlu1 : τ1.vars "lu" = u.length := by simp [hτ1]
  have hw1 : WordsAt W τ1 := hw.of_arrs rfl rfl rfl
  have hc := glue_ev_eq (B := B) (σ := τ1) (e := .var "f") (f := .lit 0) (glue_ev_var (a := f) (by simp [hτ1, hf]) hfB)
    (evalB_lit (by omega))
  -- the end of the item
  have hfin : ∀ τ2 K, Run B (.ite (.eq (.var "f") (.lit 0)) glueCopyFrame glueExpFrame) τ1 τ2 K →
      ∃ τ3, Run B glueFrameCmd τ τ3 (3 + K + 6) ∧ τ3.vars "fp" = q + u.length + 1 ∧ τ3.out = τ2.out := by
    intro τ2 K r2
    have hfp2 : τ2.vars "fp" = q := by rw [r2.frame_var "fp" (by decide), hfp1]
    have hlu2 : τ2.vars "lu" = u.length := by rw [r2.frame_var "lu" (by decide), hlu1]
    refine ⟨τ2.setVar "fp" (q + u.length + 1), ?_, by simp, by simp⟩
    unfold glueFrameCmd
    exact (Run.seq r1 (Run.seq r2 (Run.assign (glue_ev_add (glue_ev_add (glue_ev_var hfp2 (by omega))
      (glue_ev_var hlu2 (by omega)) (by omega)) (evalB_lit (by omega)) (by omega))))).mono (by simp; omega)
  by_cases hf0 : f = 0
  · -- a verbatim copy
    have hv : expandItem W f u = u := by simp [expandItem, hf0]
    rw [hv] at hvB ⊢
    set τ2 : Env := { τ1 with out := τ1.out ++ [u.length] } with hτ2
    obtain ⟨τ3, r3, -, hout3⟩ := glue_writeLoop_run' (B := B) (N := u.length) (i := "h") (m := "lu")
      (e := .get "x" (.add (.add (.var "fp") (.lit 1)) (.var "h"))) (fun k => X.getD (q + 1 + k) 0)
      (fun ρ => ρ.arrs "x" = X ∧ ρ.vars "fp" = q ∧ ρ.vars "lu" = u.length) (by omega) (by decide)
      (fun ρ o h => h) (fun ρ k h => ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2⟩)
      (fun ρ h => h.2.2)
      (fun ρ h hi => glue_ev_get (glue_ev_add (glue_ev_add (glue_ev_var h.2.1 (by omega)) (evalB_lit (by omega)) (by omega))
        (evalB_var (by omega)) (by omega)) (by rw [h.1]; exact glue_getElem?_getD' (by omega))
        (glue_getD_lt hXv (by omega) _))
      τ2 ⟨by simp [hτ2, hx1], by simp [hτ2, hfp1], by simp [hτ2, hlu1]⟩
    rw [glue_map_range_drop hd1] at hout3
    have r23 : Run B glueCopyFrame τ1 τ3 (2 + (u.length * 15 + 6)) := by
      unfold glueCopyFrame
      exact Run.seq (Run.write (glue_ev_var hlu1 (by omega))) (r3.mono (by simp))
    obtain ⟨τ4, r4, hfp4, hout4⟩ := hfin τ3 _ (Run.ite_true (by rw [hc, hf0]; rfl) r23)
    refine ⟨τ4, r4.mono (by simp; omega), hfp4, ?_⟩
    rw [hout4, hout3, hτ2]; simp [hτ1]
  · -- an expanded item
    obtain ⟨a, R, rfl⟩ : ∃ a R, u = a :: R := by
      cases u with
      | nil => exact absurd rfl (hne hf0)
      | cons a R => exact ⟨a, R, rfl⟩
    have href' : ∀ r' ∈ R, r' < W.length := by simpa using href hf0
    have hqR : q + 2 + R.length ≤ X.length := by simp at hlen; omega
    set g : ℕ → ℕ := fun r' => (W.getD r' []).length with hg
    have hv : expandItem W f (a :: R) = a :: (R.map fun r' => W.getD r' []).flatten := by
      simp [expandItem, hf0]
    have hvl : (expandItem W f (a :: R)).length = 1 + (R.map g).sum := by
      rw [hv]; simp [List.length_flatten, List.map_map, hg, Function.comp_def]; omega
    have hd2 : X.drop (q + 1 + 1) = R ++ r := by
      have := drop_add_of_drop (u := [a]) (r := R ++ r) (by rw [hd1]; rfl)
      simpa using this
    have hd2' : X.drop (q + 2) = R ++ r := by simpa using hd2
    have hxR : ∀ k (hk : k < R.length), X[q + 2 + k]? = some R[k] := fun k hk => glue_getElem?_of_drop hd2' hk
    have hgk : ∀ k (hk : k < R.length), g R[k] = (W[R[k]]'(href' _ (List.getElem_mem hk))).length := by
      intro k hk; simp [hg, List.getD_eq_getElem?_getD, href' _ (List.getElem_mem hk)]
    have hRB : ∀ k (hk : k < R.length), R[k] < B := fun k hk => hXv _ (List.mem_of_getElem? (hxR k hk))
    have hlu_ev : ∀ ρ : Env, ρ.vars "lu" = (a :: R).length →
        (Expr.sub (.var "lu") (.lit 1)).evalB B ρ = some R.length := fun ρ h =>
      glue_ev_subE (glue_ev_var h (by simp; omega)) (evalB_lit (by omega)) (by simp) (by omega)
    -- the sum of the lengths
    set τ2 := τ1.setVar "s" 1 with hτ2
    obtain ⟨τ3, r3, ⟨hx3, hw3, hfp3, hlu3, hs3⟩, -⟩ := forUp_run (B := B) (i := "h")
      (e := .sub (.var "lu") (.lit 1))
      (body := .assign "s" (.add (.var "s") (.get "ln" (.get "x" (.add (.add (.var "fp") (.lit 2))
        (.var "h")))))) (N := R.length) (K := 10)
      (fun k ρ => ρ.arrs "x" = X ∧ WordsAt W ρ ∧ ρ.vars "fp" = q ∧ ρ.vars "lu" = (a :: R).length ∧
        ρ.vars "s" = 1 + ((R.take k).map g).sum)
      (σ := τ2) (by omega)
      (fun k _ ρ hI _ => hlu_ev ρ hI.2.2.2.1)
      ⟨by simp [hτ2, hx1], (hw1.of_arrs rfl rfl rfl), by simp [hτ2, hfp1], by simp [hτ2, hlu1],
        by simp [hτ2]⟩
      (fun k hk ρ ⟨hxρ, hwρ, hfpρ, hluρ, hsρ⟩ hik => by
        have hRk := href' _ (List.getElem_mem hk)
        have hsum := glue_take_succ_map_sum R g hk
        have hle := glue_sum_take_map_le R g (k + 1)
        have hgl := hgk k hk
        refine ⟨ρ.setVar "s" (ρ.vars "s" + (W[R[k]]'hRk).length), (Run.assign ?_).mono (by simp),
          by simp [hik], by simp [hxρ], hwρ.of_arrs rfl rfl rfl, by simp [hfpρ], by simp [hluρ], ?_⟩
        · refine glue_ev_add (glue_ev_var rfl (by omega)) (glue_ev_get (glue_ev_get (glue_ev_add (glue_ev_add (glue_ev_var hfpρ (by omega))
            (evalB_lit (by omega)) (by omega)) (glue_ev_var hik (by omega)) (by omega))
            (by rw [hxρ]; exact hxR k hk) (hRB k hk)) (hwρ.ln _ hRk) (by omega)) (by omega)
        · simp only [vars_setVar, if_true, show ("s" : String) = "h" ↔ False by decide, if_false]
          omega)
    rw [List.take_length, ← hvl] at hs3
    -- the length and the guard
    set τ4 : Env := { τ3 with out := τ3.out ++ [(expandItem W f (a :: R)).length] } with hτ4
    set τ5 : Env := { τ4 with out := τ4.out ++ [a] } with hτ5
    have rw4 : Run B (.write (.var "s")) τ3 τ4 2 := (Run.write (glue_ev_var hs3 (by omega))).mono (by simp)
    have rw5 : Run B (.write (.get "x" (.add (.var "fp") (.lit 1)))) τ4 τ5 5 :=
      (Run.write (glue_ev_get (glue_ev_add (glue_ev_var (a := q)
        (by simp [hτ4, hfp3]) (by omega)) (evalB_lit (by omega)) (by omega))
        (by simp [hτ4, hx3]; exact glue_getElem?_of_drop_cons (by rw [hd1]; rfl))
        (hXv _ (List.mem_of_getElem? (glue_getElem?_of_drop_cons (by rw [hd1]; rfl)))))).mono (by simp)
    -- the answers
    obtain ⟨τ6, r6, ⟨-, -, -, -, hout6⟩, -⟩ := glue_forUp_sum (B := B) (i := "h")
      (e := .sub (.var "lu") (.lit 1))
      (body := .seq (.assign "ow" (.get "x" (.add (.add (.var "fp") (.lit 2)) (.var "h")))) glueWriteRaw)
      (N := R.length) (fun h => 13 * g (R.getD h 0) + 19)
      (fun k ρ => ρ.arrs "x" = X ∧ WordsAt W ρ ∧ ρ.vars "fp" = q ∧ ρ.vars "lu" = (a :: R).length ∧
        ρ.out = τ5.out ++ ((R.take k).map fun r' => W.getD r' []).flatten)
      (σ := τ5) (by omega)
      (fun k _ ρ hI _ => hlu_ev ρ hI.2.2.2.1)
      ⟨by simp [hτ5, hτ4, hx3], (hw3.of_arrs rfl rfl rfl), by simp [hτ5, hτ4, hfp3],
        by simp [hτ5, hτ4, hlu3], by simp⟩
      (fun k hk ρ ⟨hxρ, hwρ, hfpρ, hluρ, houtρ⟩ hik => by
        have hRk := href' _ (List.getElem_mem hk)
        obtain ⟨ρ2, r2, hout2⟩ := glue_writeRaw_run (B := B) (σ := ρ.setVar "ow" R[k])
          (hwρ.of_arrs rfl rfl rfl) hb (i := R[k]) (by simp) hRk
        have hgk' : g (R.getD k 0) = (W[R[k]]'hRk).length := by
          rw [← hgk k hk]; simp [List.getD_eq_getElem?_getD, hk]
        refine ⟨ρ2, (Run.seq (Run.assign (glue_ev_get (glue_ev_add (glue_ev_add (glue_ev_var hfpρ (by omega))
          (evalB_lit (by omega)) (by omega)) (glue_ev_var hik (by omega)) (by omega))
          (by rw [hxρ]; exact hxR k hk) (hRB k hk))) r2).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [size_get, size_add, size_var, size_lit, hgk']; omega
        · rw [r2.frame_var "h" (by decide)]; simp [hik]
        · simp only [arrs_setVar]; rw [r2.frame_arr "x" (by decide)]; simp [hxρ]
        · refine hwρ.of_arrs ?_ ?_ ?_ <;>
          · simp only [arrs_setVar]; rw [r2.frame_arr _ (by decide)]; simp
        · simp only [vars_setVar]; rw [r2.frame_var "fp" (by decide)]; simp [hfpρ]
        · simp only [vars_setVar]; rw [r2.frame_var "lu" (by decide)]; simp [hluρ]
        · simp only [out_setVar]
          rw [hout2, out_setVar, houtρ, glue_take_succ_map_flatten _ _ hk]
          simp [List.getD_eq_getElem?_getD, hRk])
    rw [List.take_length] at hout6
    have r26 : Run B glueExpFrame τ1 τ6 (R.length * 30 + 30 +
        ((List.range R.length).map fun h => 13 * g (R.getD h 0) + 19).sum) := by
      unfold glueExpFrame glueSumLoop glueRefLoop
      refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r3 (Run.seq rw4 (Run.seq rw5 r6)))).mono ?_
      simp only [size_condEq, size_var, size_lit, size_sub, size_add, size_get]
      omega
    obtain ⟨τ7, r7, hfp7, hout7⟩ := hfin τ6 _ (Run.ite_false (by rw [hc]; simp [hf0]) r26)
    refine ⟨τ7, r7.mono ?_, hfp7, ?_⟩
    · simp only [size_condEq, size_var, size_lit, size_sub, size_add, size_get]
      rw [glue_sum_range_lin, hvl]; simp only [List.length_cons]; nlinarith
    · have hout3 : τ3.out = τ.out := by
        rw [r3.out_eq (by simp [forUp, Com.NoWrite])]; simp [hτ2, hτ1]
      rw [hout7, hout6, hτ5, hτ4, hv]
      simp [hout3]

/-! ### A round that asks for a job -/

/-- Skip the items of the job at `y`. -/
def glueSkipLoop : Com :=
  forUp "e" (.var "ni") (.assign "y" (.add (.add (.var "y") (.get "x" (.var "y"))) (.lit 1)))

/-- Read the flag and the number of items of the job at `ptr`, and find its end. -/
def glueSkipJob : Com :=
  .seq (.assign "f" (.get "x" (.var "ptr"))) (.seq (.assign "ni" (.get "x" (.add (.var "ptr") (.lit 1))))
    (.seq (.assign "y" (.add (.var "ptr") (.lit 2))) glueSkipLoop))

/-- Write the frames of the answers. -/
def glueWordsLoop : Com := forUp "e" (.var "m") (.seq (.assign "ow" (.var "e")) writeWord)

/-- Write the head and the state: the window, the position of the next
job and the answers so far. -/
def glueStateCmd : Com :=
  .seq (.write (.add (.var "nx") (.lit 1))) (.seq (.write (.add (.add (.lit 3) (.var "m")) (.var "p")))
    (.seq (.write (.var "nx")) (.seq (.write (.lit 0)) (.seq (.write (.var "y"))
      (.seq (.write (.var "m")) glueWordsLoop)))))

/-- Write the query: the number of items and the word of every item. -/
def glueQueryCmd : Com :=
  .seq (.write (.var "ni")) (.seq (.assign "fp" (.add (.var "ptr") (.lit 2))) (forUp "e" (.var "ni") glueFrameCmd))

/-- A round that asks for job `m`. -/
def glueJobCmd : Com := .seq glueSkipJob (.seq glueStateCmd glueQueryCmd)

theorem glue_frames_take_succ (ws : List (List ℕ)) {k : ℕ} (hk : k < ws.length) :
    frames (ws.take (k + 1)) = frames (ws.take k) ++ (ws[k].length :: ws[k]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, frames_append]; simp [frames]

theorem glue_length_le_frames (ws : List (List ℕ)) : ws.length ≤ (frames ws).length := by
  induction ws with
  | nil => simp
  | cons u ws ih =>
    simp only [frames, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at ih ⊢
    omega

theorem glue_job_cost_le (I j S : ℕ) (hI : I ≤ S) (hj : j ≤ S) :
    12 + (I * 15 + 6) + (18 + (j * (13 * S + 16 + 1 + 7) + 1 + 5) +
      (1 + 1 + (1 + (1 + 1 + 1) + (I * (100 * S + 60 + 1 + 7) + 1 + 5)))) ≤ 200 * (S + 1) ^ 2 := by
  nlinarith

set_option maxHeartbeats 4000000 in
theorem glue_job_run {B : ℕ} (js : List Job) (fin : List ℕ × List ℕ) (hwf : JobsWF js fin) {j : ℕ}
    (hj : j < js.length) (hBB : maxEntry (toWord (js, fin)) + jobSize js fin + 4 < B) {σ : Env}
    (hc : glueGCtx js fin j σ) :
    ∃ σ', Run B glueJobCmd σ σ' (200 * (jobSize js fin + 1) ^ 2) ∧
      σ'.out = σ.out ++ ([(toWord (js, fin)).length + 1, 3 + j + total ((allResults js).take j),
        (toWord (js, fin)).length, 0, jobPos js (j + 1)] ++ toWord ((allResults js).take j) ++
        toWord (jobQuery ((allResults js).take j) js[j])) := by
  have hXv := glue_x_lt js fin hBB
  have hXB := glue_xlen_lt js fin hBB
  have hS := glue_jobSize_ge js fin
  have hb := glue_wordsBound_take (B := B) js fin j hBB
  have hRl := length_allResults js
  have hWl : ((allResults js).take j).length = j := by simp [hRl]; omega
  have htW := glue_total_take_le (allResults js) j
  have hd := glue_drop_jobPos_lt js fin hj
  have hps := glue_jobPos_succ js hj
  have hpl := glue_jobPos_le_length js fin (j := j + 1) (by omega)
  have hQS := glue_jobSize_query js fin hj
  have hwf1 := hwf.1 j hj
  have hx := hc.x
  have hw := hc.w
  have hm := hc.m
  have hp := hc.p
  have hptr := hc.ptr
  have hnx := hc.nx
  clear hc
  rw [hps]
  generalize toWord (js, fin) = X at *
  generalize jobPos js j = ptr at *
  generalize jobSize js fin = S at *
  generalize (allResults js).take j = W at *
  generalize js[j] = jb at *
  obtain ⟨fl, I⟩ := jb
  simp only at hd hwf1 ⊢
  generalize ((js.drop (j + 1)).map toWord).flatten ++ toWord fin = R0 at *
  set Q := jobQuery W (fl, I) with hQ
  have hQI : Q = I.map (expandItem W fl) := rfl
  have hQl : Q.length = I.length := by simp [hQI]
  have hlen := congrArg List.length hd
  simp only [List.length_drop, List.length_cons, List.length_append] at hlen
  have hfr : X.drop (ptr + 2) = frames I ++ R0 := by
    have := drop_add_of_drop (u := [fl, I.length]) (r := frames I ++ R0) (by rw [hd]; rfl)
    simpa using this
  have hflB : fl < B := hXv fl (List.mem_of_getElem? (glue_getElem?_of_drop_cons hd))
  have hd' : X.drop (ptr + 1) = I.length :: (frames I ++ R0) := by
    have := drop_add_of_drop (u := [fl]) (r := I.length :: (frames I ++ R0)) (by rw [hd]; rfl)
    simpa using this
  have hIB : I.length < B := hXv _ (List.mem_of_getElem? (glue_getElem?_of_drop_cons hd'))
  have hIF := glue_length_le_frames I
  have hQt : total Q ≤ S := by have := length_toWord_words Q; omega
  -- skipping the job
  set σ1 := σ.setVar "f" fl with hσ1
  set σ2 := σ1.setVar "ni" I.length with hσ2
  set σ3 := σ2.setVar "y" (ptr + 2) with hσ3
  have r1 : Run B (.assign "f" (.get "x" (.var "ptr"))) σ σ1 3 :=
    (Run.assign (glue_ev_get (glue_ev_var (a := ptr) hptr (by omega)) (by rw [hx]; exact glue_getElem?_of_drop_cons hd)
      hflB)).mono (by simp)
  have r2 : Run B (.assign "ni" (.get "x" (.add (.var "ptr") (.lit 1)))) σ1 σ2 5 :=
    (Run.assign (glue_ev_get (glue_ev_add (glue_ev_var (a := ptr) (by simp [hσ1, hptr]) (by omega))
      (evalB_lit (by omega)) (by omega))
      (by simp [hσ1, hx]; exact glue_getElem?_of_drop_cons hd') hIB)).mono (by simp)
  have r3 : Run B (.assign "y" (.add (.var "ptr") (.lit 2))) σ2 σ3 4 :=
    (Run.assign (glue_ev_add (glue_ev_var (a := ptr) (by simp [hσ2, hσ1, hptr]) (by omega))
      (evalB_lit (by omega)) (by omega))).mono (by simp)
  have hsk : ∀ k ≤ I.length, skipFr X (ptr + 2) k = ptr + 2 + (frames (I.take k)).length ∧
      X.drop (skipFr X (ptr + 2) k) = frames (I.drop k) ++ R0 := fun k hk => skipFr_frames hfr hk
  have hskd : ∀ k (hk : k < I.length), X.drop (skipFr X (ptr + 2) k) =
      I[k].length :: (I[k] ++ (frames (I.drop (k + 1)) ++ R0)) := by
    intro k hk; rw [(hsk k hk.le).2, frames_drop hk]; simp
  have hsks : ∀ k (hk : k < I.length), skipFr X (ptr + 2) (k + 1) = skipFr X (ptr + 2) k + I[k].length + 1 := by
    intro k hk; rw [skipFr_succ', xg_of_drop (hskd k hk)]; omega
  have hskl : ∀ k ≤ I.length, skipFr X (ptr + 2) k ≤ ptr + 2 + (frames I).length := by
    intro k hk; rw [(hsk k hk).1]; have := length_frames_take_le I k; omega
  obtain ⟨σ4, r4, ⟨-, -, hy4⟩, -⟩ := forUp_run (B := B) (i := "e") (e := .var "ni")
    (body := .assign "y" (.add (.add (.var "y") (.get "x" (.var "y"))) (.lit 1))) (N := I.length) (K := 7)
    (fun k ρ => ρ.arrs "x" = X ∧ ρ.vars "ni" = I.length ∧ ρ.vars "y" = skipFr X (ptr + 2) k)
    (σ := σ3) hIB
    (fun k _ ρ hI _ => glue_ev_var hI.2.1 hIB)
    ⟨by simp [hσ3, hσ2, hσ1, hx], by simp [hσ3, hσ2], by simp [hσ3, skipFr]⟩
    (fun k hk ρ ⟨hxρ, hniρ, hyρ⟩ hik => by
      have h1 := hsks k hk
      have h2 := hskl (k + 1) hk
      refine ⟨ρ.setVar "y" (skipFr X (ptr + 2) k + I[k].length + 1), (Run.assign (glue_ev_add (glue_ev_add
        (glue_ev_var hyρ (by omega)) (glue_ev_get (glue_ev_var hyρ (by omega))
          (by rw [hxρ]; exact glue_getElem?_of_drop_cons (hskd k hk)) (by omega)) (by omega))
          (evalB_lit (by omega)) (by omega))).mono (by simp), by simp [hik], by simp [hxρ],
        by simp [hniρ], by simp [h1]⟩)
  rw [(hsk I.length le_rfl).1, List.take_length] at hy4
  have hv4 : ∀ z, z ∉ glueSkipLoop.wvars → σ4.vars z = σ3.vars z := fun z h => r4.frame_var z h
  have ha4 : ∀ z, z ∉ glueSkipLoop.warrs → σ4.arrs z = σ3.arrs z := fun z h => r4.frame_arr z h
  have rs : Run B glueSkipJob σ σ4 (12 + (I.length * 15 + 6)) := by
    unfold glueSkipJob
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by simp; omega)
  -- the state
  have hnx4 : σ4.vars "nx" = X.length := by rw [hv4 "nx" (by decide)]; simp [hσ3, hσ2, hσ1, hnx]
  have hm4 : σ4.vars "m" = j := by rw [hv4 "m" (by decide)]; simp [hσ3, hσ2, hσ1, hm]
  have hp4 : σ4.vars "p" = total W := by rw [hv4 "p" (by decide)]; simp [hσ3, hσ2, hσ1, hp]
  have hw4 : WordsAt W σ4 := by
    refine hw.of_arrs ?_ ?_ ?_ <;> · rw [ha4 _ (by decide)]; simp [hσ3, hσ2, hσ1]
  set O := [X.length + 1, 3 + j + total W, X.length, 0, ptr + 2 + (frames I).length, j] with hO
  set σ5 : Env := { σ4 with out := σ4.out ++ O } with hσ5
  obtain ⟨σ6, r6, ⟨-, -, hout6⟩, -⟩ := forUp_run (B := B) (i := "e") (e := .var "m")
    (body := .seq (.assign "ow" (.var "e")) writeWord) (N := j) (K := 13 * S + 16)
    (fun k ρ => WordsAt W ρ ∧ ρ.vars "m" = j ∧ ρ.out = σ5.out ++ frames (W.take k))
    (σ := σ5) (by omega)
    (fun k _ ρ hI _ => glue_ev_var hI.2.1 (by omega))
    ⟨hw4.of_arrs rfl rfl rfl, by simp [hσ5, hm4], by simp [frames]⟩
    (fun k hk ρ ⟨hwρ, hmρ, houtρ⟩ hik => by
      have hkW : k < W.length := by omega
      obtain ⟨ρ2, r2, hout2⟩ := writeWord_run (B := B) (σ := ρ.setVar "ow" k) (hwρ.of_arrs rfl rfl rfl) hb
        (i := k) (by simp) hkW
      have hlk := glue_le_total_of_mem (List.getElem_mem hkW)
      refine ⟨ρ2, (Run.seq (Run.assign (glue_ev_var hik (by omega))) r2).mono ?_, ?_, ?_, ?_, ?_⟩
      · simp only [size_var]; omega
      · rw [r2.frame_var "e" (by decide)]; simp [hik]
      · refine hwρ.of_arrs ?_ ?_ ?_ <;>
        · simp only [arrs_setVar]; rw [r2.frame_arr _ (by decide)]; simp
      · simp only [vars_setVar]; rw [r2.frame_var "m" (by decide)]; simp [hmρ]
      · simp only [out_setVar]
        rw [hout2, out_setVar, houtρ, glue_frames_take_succ W hkW]; simp)
  rw [← hWl, List.take_length] at hout6
  have rst : Run B glueStateCmd σ4 σ6 (18 + (j * (13 * S + 16 + 1 + 7) + 1 + 5)) := by
    unfold glueStateCmd glueWordsLoop
    refine (Run.seq (Run.write (glue_ev_add (glue_ev_var hnx4 (by omega)) (evalB_lit (by omega)) (by omega)))
      (Run.seq (Run.write (glue_ev_add (glue_ev_add (evalB_lit (by omega)) (glue_ev_var hm4 (by omega)) (by omega))
        (glue_ev_var hp4 (by omega)) (by omega)))
      (Run.seq (Run.write (glue_ev_var hnx4 (by omega))) (Run.seq (Run.write (evalB_lit (by omega)))
        (Run.seq (Run.write (glue_ev_var hy4 (by omega))) (Run.seq (Run.congr (Run.write (glue_ev_var hm4 (by omega)))
          ?_) r6)))))).mono (by simp; omega)
    simp [hσ5, hO]
  -- the query
  have hv6 : ∀ z, z ∉ glueStateCmd.wvars → σ6.vars z = σ4.vars z := fun z h => rst.frame_var z h
  have ha6 : ∀ z, z ∉ glueStateCmd.warrs → σ6.arrs z = σ4.arrs z := fun z h => rst.frame_arr z h
  have hni6 : σ6.vars "ni" = I.length := by
    rw [hv6 "ni" (by decide), hv4 "ni" (by decide)]; simp [hσ3, hσ2]
  have hf6 : σ6.vars "f" = fl := by
    rw [hv6 "f" (by decide), hv4 "f" (by decide)]; simp [hσ3, hσ2, hσ1]
  have hptr6 : σ6.vars "ptr" = ptr := by
    rw [hv6 "ptr" (by decide), hv4 "ptr" (by decide)]; simp [hσ3, hσ2, hσ1, hptr]
  have hx6 : σ6.arrs "x" = X := by
    rw [ha6 "x" (by decide), ha4 "x" (by decide)]; simp [hσ3, hσ2, hσ1, hx]
  have hw6 : WordsAt W σ6 := by
    refine hw4.of_arrs ?_ ?_ ?_ <;> · rw [ha6 _ (by decide)]
  set σ7 : Env := { σ6 with out := σ6.out ++ [I.length] } with hσ7
  set σ8 := σ7.setVar "fp" (ptr + 2) with hσ8
  have hlS : I.length ≤ S := by omega
  obtain ⟨σ9, r9, ⟨-, -, -, -, -, hout9⟩, -⟩ := forUp_run (B := B) (i := "e") (e := .var "ni")
    (body := glueFrameCmd) (N := I.length) (K := 100 * S + 60)
    (fun k ρ => ρ.arrs "x" = X ∧ WordsAt W ρ ∧ ρ.vars "f" = fl ∧ ρ.vars "ni" = I.length ∧
      ρ.vars "fp" = skipFr X (ptr + 2) k ∧ ρ.out = σ8.out ++ frames (Q.take k))
    (σ := σ8) hIB
    (fun k _ ρ hI _ => glue_ev_var hI.2.2.2.1 hIB)
    ⟨by simp [hσ8, hσ7, hx6], hw6.of_arrs rfl rfl rfl, by simp [hσ8, hσ7, hf6], by simp [hσ8, hσ7, hni6],
      by simp [hσ8, hσ7, skipFr], by simp [frames]⟩
    (fun k hk ρ ⟨hxρ, hwρ, hfρ, hniρ, hfpρ, houtρ⟩ hik => by
      have hkQ : k < Q.length := by omega
      have hQk : Q[k] = expandItem W fl I[k] := by simp [hQI]
      have hQkS := glue_le_total_of_mem (List.getElem_mem hkQ)
      rw [hQk] at hQkS
      have hlk := congrArg List.length (hskd k hk)
      simp only [List.length_drop, List.length_cons, List.length_append] at hlk
      obtain ⟨ρ2, r2, hfp2, hout2⟩ := glue_frameCmd_run (B := B) (τ := ρ) hxρ hwρ hb hfρ hfpρ (hskd k hk)
        (fun h => (hwf1 h I[k] (List.getElem_mem hk)).1)
        (fun h r' hr => by rw [hWl]; exact (hwf1 h _ (List.getElem_mem hk)).2 r' hr)
        hXv hXB (by omega) hflB
      refine ⟨ρ2, r2.mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [r2.frame_var "e" (by decide), hik]
      · simp only [arrs_setVar]; rw [r2.frame_arr "x" (by decide), hxρ]
      · refine hwρ.of_arrs ?_ ?_ ?_ <;>
        · simp only [arrs_setVar]; rw [r2.frame_arr _ (by decide)]
      · simp only [vars_setVar]; rw [r2.frame_var "f" (by decide)]; simp [hfρ]
      · simp only [vars_setVar]; rw [r2.frame_var "ni" (by decide)]; simp [hniρ]
      · simp only [vars_setVar]; rw [hfp2, hsks k hk]; simp
      · simp only [out_setVar]
        rw [hout2, houtρ, glue_frames_take_succ Q hkQ, hQk]; simp)
  rw [← hQl, List.take_length] at hout9
  refine ⟨σ9, ?_, ?_⟩
  · unfold glueJobCmd glueQueryCmd
    refine (Run.seq rs (Run.seq rst (Run.seq (Run.write (glue_ev_var hni6 hIB))
      (Run.seq (Run.assign (glue_ev_add (glue_ev_var (a := ptr) (by simp [hσ7, hptr6]) (by omega))
        (evalB_lit (by omega)) (by omega))) r9)))).mono ?_
    simp only [size_var, size_add, size_lit]
    have hjS : j ≤ S := by omega
    exact glue_job_cost_le I.length j S hlS hjS
  · have h4 : σ4.out = σ.out := by
      rw [rs.out_eq (by simp [glueSkipJob, glueSkipLoop, forUp, Com.NoWrite])]
    rw [hout9, hσ8, out_setVar, hσ7, hout6, hσ5, h4, toWord_words, toWord_words, hWl, hQl, hO]
    simp

/-! ### The first two phases -/

/-- Read the tag and the window length, and the input into `x`. -/
def glueHeadCmd : Com :=
  .seq (.read "tg") (.seq (.read "sl") (.seq (.ite (.eq (.var "tg") (.lit 0)) (.assign "nx" (.var "sl"))
    (.assign "nx" (.sub (.var "tg") (.lit 1)))) glueReadX))

/-- In the first round there are no answers. Later the position of the
current job and the answers are read. -/
def glueAnsCmd : Com :=
  .ite (.eq (.var "tg") (.lit 0))
    (.seq (.assign "m" (.lit 0)) (.seq (.assign "p" (.lit 0)) (.assign "ptr" (.lit 1))))
    (.seq (.read "w") (.seq (.read "ptr") glueReadAns))

theorem glue_headCmd_run {B : ℕ} (X rest : List ℕ) (t0 l0 : ℕ) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 4 < B)
    (ht : (t0 = 0 ∧ l0 = X.length) ∨ t0 = X.length + 1) (hl0 : l0 < B) (σ : Env)
    (hinp : σ.inp = [t0, l0] ++ X ++ rest) (hx : σ.arrs "x" = List.replicate X.length 0) :
    ∃ σ', Run B glueHeadCmd σ σ' (13 * X.length + 20) ∧ σ'.arrs "x" = X ∧ σ'.inp = rest ∧
      σ'.vars "tg" = t0 ∧ σ'.vars "nx" = X.length ∧ σ'.out = σ.out ∧
      ∀ a, a ≠ "x" → σ'.arrs a = σ.arrs a := by
  have ht0 : t0 < B := by omega
  set σ1 : Env := { σ.setVar "tg" t0 with inp := l0 :: (X ++ rest) } with hσ1
  set σ2 : Env := { σ1.setVar "sl" l0 with inp := X ++ rest } with hσ2
  have hite : Run B (.ite (.eq (.var "tg") (.lit 0)) (.assign "nx" (.var "sl"))
      (.assign "nx" (.sub (.var "tg") (.lit 1)))) σ2 (σ2.setVar "nx" X.length) 8 := by
    have hc := glue_ev_eq (B := B) (σ := σ2) (e := .var "tg") (f := .lit 0)
      (glue_ev_var (a := t0) (by simp [hσ2, hσ1]) ht0) (evalB_lit (by omega))
    rcases ht with ⟨h0, hl⟩ | h1
    · refine (Run.ite_true (by rw [hc, h0]; rfl) (Run.assign (glue_ev_var (by simp [hσ2, hl]) (by omega)))).mono
        (by simp)
    · refine (Run.ite_false (by rw [hc, h1]; simp)
        (Run.assign (glue_ev_subE (c := X.length) (glue_ev_var (a := t0) (by simp [hσ2, hσ1]) ht0) (evalB_lit (by omega))
          (by omega) (by omega)))).mono (by simp)
  obtain ⟨σ3, r3, hx3, hin3⟩ := glue_readX_run (B := B) X rest hX (by omega) (σ2.setVar "nx" X.length)
    (by simp) (by simp [hσ2]) (by simp [hσ2, hσ1, hx])
  refine ⟨σ3, ?_, hx3, hin3, ?_, ?_, ?_, ?_⟩
  · unfold glueHeadCmd
    exact (Run.seq (Run.read (by rw [hinp]; rfl)) (Run.seq (Run.read rfl) (Run.seq hite r3))).mono
      (by omega)
  · rw [r3.frame_var "tg" (by decide)]; simp [hσ2, hσ1]
  · rw [r3.frame_var "nx" (by decide)]; simp
  · rw [r3.out_eq (by simp [glueReadX, glueReadXBody, forUp, Com.NoWrite])]; simp [hσ2, hσ1]
  · intro a ha
    rw [r3.frame_arr a (by simp [glueReadX, glueReadXBody, forUp, Com.warrs, ha])]; simp [hσ2, hσ1]

theorem glue_take_pred_append (Rs : List (List ℕ)) {j : ℕ} (hj0 : j ≠ 0) (hj : j ≤ Rs.length) :
    Rs.take (j - 1) ++ [Rs.getD (j - 1) []] = Rs.take j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, List.take_add_one, List.getElem?_eq_getElem (by omega)]
  simp [List.getD_eq_getElem?_getD, show i < Rs.length by omega]

theorem glue_wordsAt_nil (σ : Env) : WordsAt [] σ := ⟨by simp, by simp, by simp⟩

/-- The glue program of the canonical form of a list of jobs. -/
def canonGlue : Com :=
  .seq glueHeadCmd (.seq glueAnsCmd (.ite (.eq (.var "m") (.get "x" (.lit 0))) glueFinalCmd glueJobCmd))

/-- The scalars and arrays of `canonGlue`. -/
def glueLayout : Layout :=
  ⟨["tg", "sl", "nx", "i", "w", "m", "p", "n", "j", "v", "ptr", "q", "r", "nr", "e", "ow", "pa", "la",
    "k", "f", "ni", "y", "fp", "lu", "h", "s"], ["x", "a", "st", "ln"], 4⟩

/-- The constant of the value bound. -/
def glueC : ℕ := 4
/-- The constant of the cost bound. -/
def glueK : ℕ := 300

/-- The array lengths: the input for `x`, and room for all answers in the others. -/
def glueExt (js : List Job) (fin : List ℕ × List ℕ) : String → ℕ :=
  fun a => if a = "x" then (toWord (js, fin)).length else jobSize js fin + 1

theorem canonGlue_ok : Com.Ok glueLayout canonGlue := by
  simp [canonGlue, glueHeadCmd, glueAnsCmd, glueReadX, glueReadXBody, glueReadAns, readWord, readEntries, readEntry,
    glueFinalCmd, glueFinRefs, glueWriteRaw, writeEntry, glueJobCmd, glueSkipJob, glueSkipLoop, glueStateCmd, glueWordsLoop, writeWord,
    glueQueryCmd, glueFrameCmd, glueCopyFrame, glueExpFrame, glueSumLoop, glueRefLoop, forUp, glueLayout, Com.Ok, Cond.Ok,
    condExpr, Expr.Ok]

/-- The last phase: the result or the next query. -/
theorem glue_tail_run {B : ℕ} (js : List Job) (fin : List ℕ × List ℕ) (hwf : JobsWF js fin) {j : ℕ}
    (hj : j ≤ js.length) (hBB : maxEntry (toWord (js, fin)) + jobSize js fin + 4 < B) {σ : Env}
    (hc : glueGCtx js fin j σ) (hout : σ.out = []) :
    ∃ σ', Run B (.ite (.eq (.var "m") (.get "x" (.lit 0))) glueFinalCmd glueJobCmd) σ σ'
        (5 + 200 * (jobSize js fin + 1) ^ 2) ∧ σ'.out = glueOut js fin j := by
  have hS := glue_jobSize_ge js fin
  have h0 : (σ.arrs "x")[0]? = some js.length := by rw [hc.x, glue_toWord_jobsFin]; rfl
  have hcond := glue_ev_eq (B := B) (σ := σ) (e := .var "m") (f := .get "x" (.lit 0))
    (glue_ev_var hc.m (by omega)) (glue_ev_get (evalB_lit (by omega)) h0 (by omega))
  by_cases hjl : j = js.length
  · subst hjl
    obtain ⟨σ', r, hout'⟩ := glue_final_run (B := B) js fin hwf hBB hc
    refine ⟨σ', (Run.ite_true (by rw [hcond]; simp) r).mono ?_, ?_⟩
    · simp only [size_condEq, size_var, size_get, size_lit]; nlinarith
    · rw [hout', hout, glueOut, if_pos rfl]; rfl
  · obtain ⟨σ', r, hout'⟩ := glue_job_run (B := B) js fin hwf (j := j) (by omega) hBB hc
    refine ⟨σ', (Run.ite_false (by rw [hcond]; simp [hjl]) r).mono ?_, ?_⟩
    · simp only [size_condEq, size_var, size_get, size_lit]; omega
    · rw [hout', hout, glueOut, if_neg hjl]
      have : js.getD j (0, []) = js[j]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, show j < js.length by omega]
      rw [this]; simp

/-- **One round of the glue program.** -/
theorem canonGlue_run (js : List Job) (fin : List ℕ × List ℕ) (hwf : JobsWF js fin) (j : ℕ)
    (hj : j ≤ js.length) (B : ℕ)
    (hB : glueC * (jobSize js fin + maxEntry (toWord (js, fin)) + 1) ≤ B) :
    ∃ (ext : String → ℕ) (σ' : Env),
      Run B canonGlue (initEnv ext (glueIn js fin j)) σ' (glueK * (jobSize js fin + 1) ^ 2) ∧
      σ'.out = glueOut js fin j := by
  have hS := glue_jobSize_ge js fin
  have h3 := glue_three_le_length js fin
  have hBB : maxEntry (toWord (js, fin)) + jobSize js fin + 4 < B := by unfold glueC at hB; omega
  have hXv := glue_x_lt js fin hBB
  have hXB := glue_xlen_lt js fin hBB
  have hRl := length_allResults js
  refine ⟨glueExt js fin, ?_⟩
  set σ0 := initEnv (glueExt js fin) (glueIn js fin j) with hσ0
  have hx0 : σ0.arrs "x" = List.replicate (toWord (js, fin)).length 0 := by simp [hσ0, initEnv, glueExt]
  have hext : ∀ a, a ≠ "x" → σ0.arrs a = List.replicate (jobSize js fin + 1) 0 := by
    intro a ha; simp [hσ0, initEnv, glueExt, ha]
  -- the head and the answers
  obtain ⟨σH, σA, KA, rH, rA, hKA, hcA, houtA⟩ : ∃ σH σA KA, Run B glueHeadCmd σ0 σH
      (13 * (toWord (js, fin)).length + 20) ∧ Run B glueAnsCmd σH σA KA ∧
      KA ≤ 21 * jobSize js fin + 50 ∧ glueGCtx js fin j σA ∧ σA.out = [] := by
    by_cases h0 : j = 0
    · subst h0
      obtain ⟨σH, rH, hxH, -, htgH, hnxH, houtH, haH⟩ := glue_headCmd_run (B := B) (toWord (js, fin)) [0] 0
        (toWord (js, fin)).length hXv hXB (Or.inl ⟨rfl, rfl⟩) (by omega) σ0
        (by simp [hσ0, initEnv, glueIn]) hx0
      have hc := glue_ev_eq (B := B) (σ := σH) (e := .var "tg") (f := .lit 0) (glue_ev_var htgH (by omega))
        (evalB_lit (by omega))
      refine ⟨σH, ((σH.setVar "m" 0).setVar "p" 0).setVar "ptr" 1, _, rH,
        Run.ite_true (by rw [hc]; rfl) (Run.seq (Run.assign (evalB_lit (by omega)))
          (Run.seq (Run.assign (evalB_lit (by omega))) (Run.assign (evalB_lit (by omega))))),
        by simp, ⟨by simp [hxH], by simpa using glue_wordsAt_nil _, by simp, by simp [total],
          by simp [jobPos], by simp [hnxH]⟩, by simp [houtH, hσ0, initEnv]⟩
    · have hl0 : 3 + (j - 1) + total ((allResults js).take (j - 1)) < B := by
        have := glue_total_take_le (allResults js) (j - 1); omega
      obtain ⟨σH, rH, hxH, hinH, htgH, hnxH, houtH, haH⟩ := glue_headCmd_run (B := B) (toWord (js, fin))
        ((0 :: jobPos js j :: toWord ((allResults js).take (j - 1))) ++
          (((allResults js).getD (j - 1) []).length :: (allResults js).getD (j - 1) []))
        ((toWord (js, fin)).length + 1) (3 + (j - 1) + total ((allResults js).take (j - 1))) hXv hXB
        (Or.inr rfl) hl0 σ0 (by simp [hσ0, initEnv, glueIn, h0]) hx0
      have hc := glue_ev_eq (B := B) (σ := σH) (e := .var "tg") (f := .lit 0) (glue_ev_var htgH (by omega))
        (evalB_lit (by omega))
      set ws := (allResults js).take (j - 1) with hws
      set b := (allResults js).getD (j - 1) [] with hb
      have hwsb : ws ++ [b] = (allResults js).take j := glue_take_pred_append _ h0 (by omega)
      have hwsl : ws.length = j - 1 := by simp [hws, hRl]; omega
      set σ1 : Env := { σH.setVar "w" 0 with inp := jobPos js j :: (toWord ws ++ (b.length :: b)) }
        with hσ1
      set σ2 : Env := { σ1.setVar "ptr" (jobPos js j) with inp := toWord ws ++ (b.length :: b) } with hσ2
      have harr2 : ∀ a, a ≠ "x" → σ2.arrs a = List.replicate (jobSize js fin + 1) 0 := by
        intro a ha; simp [hσ2, hσ1, haH a ha, hext a ha]
      have htw := glue_total_take_le (allResults js) j
      have hlt := glue_length_toWord_take_le js fin j
      obtain ⟨σA, rA, hmA, hpA, hwA⟩ := glue_readAns_run (B := B) (ws := ws) (b := b) (rest := []) (σ := σ2)
        (by simp [hσ2]) (by rw [harr2 "a" (by decide), hwsb]; simp; omega)
        (by rw [harr2 "st" (by decide)]; simp; omega) (by rw [harr2 "ln" (by decide)]; simp; omega)
        (by rw [hwsb]; omega)
        (by rw [hwsb]; intro v hv; have := glue_take_entry_le js fin j v hv; omega)
      rw [hwsb] at hpA hwA rA
      refine ⟨σH, σA, _, rH, Run.ite_false (by rw [hc]; simp)
        (Run.seq (Run.read (by rw [hinH]; rfl)) (Run.seq (Run.read rfl) rA)), ?_, ⟨?_, hwA, ?_, hpA, ?_, ?_⟩, ?_⟩
      · simp only [size_condEq, size_var, size_lit]; omega
      · rw [rA.frame_arr "x" (by decide)]; simp [hσ2, hσ1, hxH]
      · rw [hmA]; omega
      · rw [rA.frame_var "ptr" (by decide)]; simp [hσ2]
      · rw [rA.frame_var "nx" (by decide)]; simp [hσ2, hσ1, hnxH]
      · rw [rA.out_eq (by simp [glueReadAns, readWord, readEntries, readEntry, Com.NoWrite])]
        simp [hσ2, hσ1, houtH, hσ0, initEnv]
  obtain ⟨σ', rT, houtT⟩ := glue_tail_run (B := B) js fin hwf hj hBB hcA houtA
  refine ⟨σ', ?_, houtT⟩
  unfold canonGlue
  refine (Run.seq rH (Run.seq rA rT)).mono ?_
  unfold glueK
  nlinarith


end Lax185574Proofs.Words
