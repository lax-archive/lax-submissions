/-
# The tape of the simulating machine

The tape of `tmOf P N` encodes a register state `s` as a bit matrix: the cell at position
`j ≥ 1` has its `r`-th bit set exactly when `s r ≥ j`.  This file sets up that encoding
and the elementary moves of the machine along the tape ("legs" of the computation), in a
form in which they can be composed.
-/
import Lax251941Proofs.Source.Sim.Table

namespace Lax251941Proofs.PCP
namespace Sim

variable {P : Prog} {N : ℕ}

/-! ## Legs -/

lemma iter_add' {α : Type*} (f : α → α) (a b : ℕ) (x : α) : f^[a + b] x = f^[b] (f^[a] x) := by
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- `Leg P N c c'`: the machine `tmOf P N` runs from `c` to `c'` without visiting the
accept state on the way (the final configuration `c'` may be accepting). -/
def Leg (P : Prog) (N : ℕ) (c c' : Cfg) : Prop :=
  ∃ T, (dstep (tmOf P N))^[T] c = c' ∧
    ∀ t < T, ((dstep (tmOf P N))^[t] c).st ≠ stHome P.length

lemma leg_refl (c : Cfg) : Leg P N c c := ⟨0, by simp, by omega⟩

lemma leg_trans {c c' c'' : Cfg} (h1 : Leg P N c c') (h2 : Leg P N c' c'') :
    Leg P N c c'' := by
  obtain ⟨T1, e1, n1⟩ := h1
  obtain ⟨T2, e2, n2⟩ := h2
  refine ⟨T1 + T2, by rw [iter_add', e1, e2], ?_⟩
  intro t ht
  rcases Nat.lt_or_ge t T1 with h | h
  · exact n1 t h
  · obtain ⟨u, rfl⟩ : ∃ u, t = T1 + u := ⟨t - T1, by omega⟩
    rw [iter_add', e1]
    exact n2 u (by omega)

lemma leg_step {c c' : Cfg} (h : dstep (tmOf P N) c = c') (hst : c.st ≠ stHome P.length) :
    Leg P N c c' := by
  refine ⟨1, by simpa using h, fun t ht => ?_⟩
  interval_cases t
  simpa using hst

lemma leg_walk_right {q : ℕ} (hq : q ≠ stHome P.length) {L v w : List ℕ}
    (h : ∀ a ∈ v, (q, a, q, a, true) ∈ (tmOf P N).trans) :
    Leg P N ⟨L, q, v ++ w⟩ ⟨v.reverse ++ L, q, w⟩ := by
  refine ⟨v.length, ?_, fun t ht => ?_⟩
  · rw [walk_right (det_tmOf P N) q v L w h v.length le_rfl]
    simp
  · rw [walk_right (det_tmOf P N) q v L w h t (le_of_lt ht)]
    exact hq

lemma leg_walk_left {q : ℕ} (hq : q ≠ stHome P.length) {L v w : List ℕ} (hw : w ≠ [])
    (h : ∀ a ∈ w.headI :: v, (q, a, q, a, false) ∈ (tmOf P N).trans) :
    Leg P N ⟨v ++ L, q, w⟩ ⟨L, q, v.reverse ++ w⟩ := by
  refine ⟨v.length, ?_, fun t ht => ?_⟩
  · rw [walk_left (det_tmOf P N) q v L w hw h v.length le_rfl]
    simp
  · rw [walk_left (det_tmOf P N) q v L w hw h t (le_of_lt ht)]
    exact hq

/-! ## Cells on the tape -/

/-- A tape symbol which is the code of a cell. -/
def IsCell (N a : ℕ) : Prop := ∃ x : Cell N, a = cellCode x

lemma isCell_code {N : ℕ} (x : Cell N) : IsCell N (cellCode x) := ⟨x, rfl⟩

lemma isCell_zero (N : ℕ) : IsCell N 0 := ⟨blankCell N, by simp⟩

lemma list_headI_tail {α : Type*} [Inhabited α] {X : List α} (h : X ≠ []) :
    X.headI :: X.tail = X := by
  cases X with
  | nil => exact absurd rfl h
  | cons a l => rfl

lemma isCell_headI {R : List ℕ} (h : ∀ a ∈ R, IsCell N a) : IsCell N R.headI := by
  cases R with
  | nil => exact isCell_zero N
  | cons a l => exact h a (by simp)

lemma isCell_tail {R : List ℕ} (h : ∀ a ∈ R, IsCell N a) : ∀ a ∈ R.tail, IsCell N a := by
  cases R with
  | nil => simp
  | cons a l => exact fun b hb => h b (by simp only [List.tail_cons] at hb; exact List.mem_cons_of_mem _ hb)

/-- The cell at position `j` of the tape of the register state `s`. -/
def cellAt (N : ℕ) (s : Regs) (j : ℕ) : Cell N := fun i => decide (j ≤ s i)

lemma bitOf_cellAt {N : ℕ} (s : Regs) (j : ℕ) {r : ℕ} (hr : r < N) :
    bitOf (cellAt N s j) r = decide (j ≤ s r) := by
  simp [bitOf, cellAt, hr]

lemma cellAt_eq_blank {N : ℕ} {s : Regs} {j : ℕ} (h : ∀ i : Fin N, s i < j) :
    cellAt N s j = blankCell N := by
  funext i
  have := h i
  simp [cellAt, blankCell]
  omega

/-- The codes of the `m` cells at positions `a+1, …, a+m`. -/
noncomputable def cellsFrom (N : ℕ) (s : Regs) (a : ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 => cellCode (cellAt N s (a + 1)) :: cellsFrom N s (a + 1) m

@[simp] lemma cellsFrom_zero (N : ℕ) (s : Regs) (a : ℕ) : cellsFrom N s a 0 = [] := rfl

lemma cellsFrom_succ (N : ℕ) (s : Regs) (a m : ℕ) :
    cellsFrom N s a (m + 1) = cellCode (cellAt N s (a + 1)) :: cellsFrom N s (a + 1) m := rfl

@[simp] lemma length_cellsFrom (N : ℕ) (s : Regs) (a m : ℕ) :
    (cellsFrom N s a m).length = m := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih => simp [cellsFrom_succ, ih]

lemma cellsFrom_add (N : ℕ) (s : Regs) (a k l : ℕ) :
    cellsFrom N s a (k + l) = cellsFrom N s a k ++ cellsFrom N s (a + k) l := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have : a + 1 + k = a + (k + 1) := by omega
    rw [show k + 1 + l = (k + l) + 1 by omega, cellsFrom_succ, cellsFrom_succ, ih, this]
    simp

lemma cellsFrom_snoc (N : ℕ) (s : Regs) (a m : ℕ) :
    cellsFrom N s a (m + 1) = cellsFrom N s a m ++ [cellCode (cellAt N s (a + m + 1))] := by
  rw [cellsFrom_add N s a m 1, cellsFrom_succ]
  simp

lemma cellsFrom_congr {N : ℕ} {s s' : Regs} (a m : ℕ)
    (h : ∀ j, a < j → j ≤ a + m → cellAt N s j = cellAt N s' j) :
    cellsFrom N s a m = cellsFrom N s' a m := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    rw [cellsFrom_succ, cellsFrom_succ, h (a + 1) (by omega) (by omega),
      ih (a + 1) (fun j h1 h2 => h j (by omega) (by omega))]

lemma isCell_mem_cellsFrom {N : ℕ} {s : Regs} {a m : ℕ} :
    ∀ b ∈ cellsFrom N s a m, IsCell N b := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    intro b hb
    rw [cellsFrom_succ, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact isCell_code _
    · exact ih b hb

lemma headI_cellsFrom {N : ℕ} {s : Regs} {a m : ℕ} (h : ∀ i : Fin N, s i ≤ a + m) :
    (cellsFrom N s a m).headI = cellCode (cellAt N s (a + 1)) := by
  cases m with
  | zero =>
    rw [cellsFrom_zero]
    have : cellAt N s (a + 1) = blankCell N :=
      cellAt_eq_blank (fun i => by have := h i; omega)
    rw [this]
    simp
  | succ m => rw [cellsFrom_succ]; rfl

/-- Writing a new cell at position `a+1`, possibly lengthening the tape by one. -/
lemma cells_write {N : ℕ} {s s' : Regs} (a d : ℕ)
    (h : ∀ j, a + 1 < j → cellAt N s j = cellAt N s' j) :
    cellCode (cellAt N s' (a + 1)) :: (cellsFrom N s a d).tail
      = cellsFrom N s' a (max d 1) := by
  cases d with
  | zero => simp [cellsFrom_succ]
  | succ e =>
    rw [cellsFrom_succ]
    simp only [List.tail_cons]
    rw [show max (e + 1) 1 = e + 1 by omega, cellsFrom_succ]
    congr 1
    exact cellsFrom_congr (a + 1) e (fun j h1 _ => h j (by omega))

end Sim
end Lax251941Proofs.PCP
