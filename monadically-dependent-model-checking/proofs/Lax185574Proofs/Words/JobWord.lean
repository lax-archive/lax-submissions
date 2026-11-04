import Lax185574Proofs.Words.Lex
import Lax185574Proofs.Words.Read

/-!
Type trees with sets in arbitrary order, as lists of jobs.

A type tree whose sets need not be sorted or duplicate-free is given by a
list of jobs. A job is a flag and a list of items. Job `j` asks for the
canonical form of the set of its items, and its answer `R j` is the word
of that set. An item of a job with flag `0` is a word as it stands. An
item of a job with flag `1` is a guard followed by indices of earlier
jobs, and stands for the guard followed by the answers to these jobs. A
last item, a list of entries and a list of indices, gives the result:
the entries followed by the answers to the indices.

A node of a type tree becomes two jobs, its atoms and its extensions,
and the child of an extension is referred to by the indices of its two
jobs. So the answers are the canonical words of the sets, from the
leaves up, and the result is the canonical word of the tree.
-/

namespace Lax185574Proofs.Words

open Lax185574.WordEncoding

/-- A job: a flag and the items. -/
abbrev Job := ℕ × List (List ℕ)

/-- The word an item stands for, given the answers `Rs` so far. -/
def expandItem (Rs : List (List ℕ)) (f : ℕ) (u : List ℕ) : List ℕ :=
  if f = 0 then u else u.take 1 ++ ((u.drop 1).map fun r => Rs.getD r []).flatten

/-- The words of the items of a job. -/
def jobQuery (Rs : List (List ℕ)) (j : Job) : List (List ℕ) := j.2.map (expandItem Rs j.1)

/-- The answer to a job: the word of the canonical form of its items. -/
def jobAnswer (Rs : List (List ℕ)) (j : Job) : List ℕ := toWord (sortedDistinct (jobQuery Rs j))

/-- The answers to the jobs, appended to `Rs`. -/
def jobResults : List Job → List (List ℕ) → List (List ℕ)
  | [], Rs => Rs
  | j :: js, Rs => jobResults js (Rs ++ [jobAnswer Rs j])

/-- The result described by the last item. -/
def finalOut (Rs : List (List ℕ)) (fin : List ℕ × List ℕ) : List ℕ :=
  fin.1 ++ (fin.2.map fun r => Rs.getD r []).flatten

/-- The result of a list of jobs and a last item. -/
def jobsOut (js : List Job) (fin : List ℕ × List ℕ) : List ℕ := finalOut (jobResults js []) fin

/-- The answers of all jobs. -/
def allResults (js : List Job) : List (List ℕ) := jobResults js []

/-- Well-formed jobs: an item of a job with flag `1` is not empty, and
refers only to earlier jobs, and the last item refers only to jobs. -/
def JobsWF (js : List Job) (fin : List ℕ × List ℕ) : Prop :=
  (∀ j (h : j < js.length), js[j].1 ≠ 0 → ∀ u ∈ js[j].2, u ≠ [] ∧ ∀ r ∈ u.drop 1, r < j) ∧
    ∀ r ∈ fin.2, r < js.length

/-- The position of job `i` in the word of `(js, fin)`. -/
def jobPos (js : List Job) (i : ℕ) : ℕ := 1 + ((js.take i).map fun j => (toWord j).length).sum

/-- The sizes that bound the work on a list of jobs: the length of the
input, the number and total length of the answers, the lengths of the
queries and of the result. -/
def jobSize (js : List Job) (fin : List ℕ × List ℕ) : ℕ :=
  (toWord (js, fin)).length + (allResults js).length + total (allResults js) +
    ((List.range js.length).map fun j =>
      (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length).sum +
    (jobsOut js fin).length

theorem jobResults_append (js : List Job) (Rs : List (List ℕ)) :
    ∃ T, jobResults js Rs = Rs ++ T ∧ T.length = js.length := by
  induction js generalizing Rs with
  | nil => exact ⟨[], by simp [jobResults], rfl⟩
  | cons j js ih =>
    obtain ⟨T, hT, hl⟩ := ih (Rs ++ [jobAnswer Rs j])
    exact ⟨jobAnswer Rs j :: T, by simp [jobResults, hT], by simp [hl]⟩

theorem length_jobResults (js : List Job) (Rs : List (List ℕ)) :
    (jobResults js Rs).length = Rs.length + js.length := by
  obtain ⟨T, hT, hl⟩ := jobResults_append js Rs
  rw [hT, List.length_append, hl]

theorem length_allResults (js : List Job) : (allResults js).length = js.length := by
  simp [allResults, length_jobResults]

/-- The answers are computed one job after the other. -/
theorem jobResults_take (js : List Job) :
    ∀ (Rs : List (List ℕ)) (j : ℕ) (hj : j < js.length),
      (jobResults js Rs)[Rs.length + j]? =
        some (jobAnswer ((jobResults js Rs).take (Rs.length + j)) js[j]) := by
  induction js with
  | nil => intro Rs j hj; simp at hj
  | cons a js ih =>
    intro Rs j hj
    obtain ⟨T, hT, hl⟩ := jobResults_append js (Rs ++ [jobAnswer Rs a])
    cases j with
    | zero =>
      simp only [jobResults, hT, Nat.add_zero, List.getElem_cons_zero]
      simp
    | succ j =>
      have := ih (Rs ++ [jobAnswer Rs a]) j (by simp at hj; omega)
      simp only [List.length_append, List.length_singleton] at this
      simp only [jobResults, List.getElem_cons_succ]
      rw [show Rs.length + (j + 1) = Rs.length + 1 + j by omega]
      exact this

theorem allResults_getElem? (js : List Job) (j : ℕ) (hj : j < js.length) :
    (allResults js)[j]? = some (jobAnswer ((allResults js).take j) js[j]) := by
  have := jobResults_take js [] j hj
  simpa [allResults] using this

end Lax185574Proofs.Words
