/-
# The tape machine of a counter machine program

A counter machine program `P` using registers `< N` is turned into a tape machine whose
tape is a *bit matrix*: the cell at position `j ≥ 1` records, for each register `r < N`,
whether the value of `r` is at least `j`.  The value of a register is therefore the
length of the initial run of cells whose `r`-th bit is set, and the three instructions
are implemented by walking along the tape:

* `inc r` walks right to the first cell whose `r`-th bit is clear, sets it, and walks
  home;
* `dec r j` inspects the first cell: if its `r`-th bit is clear the register is zero and
  the machine jumps; otherwise it walks right to the last cell whose `r`-th bit is set,
  clears it, and walks home;
* `jmp j` just changes state.

Position `0` of the tape holds a marker, the *home* square, which is where each
instruction begins and ends; it also stops the leftward walks, and it is what keeps the
machine from ever falling off the left end of the tape.

Since every transition of the model moves the head, staying put is simulated by a step
right followed by a step left (the states `stBounce` and `stJmp`).

This file defines the transition table and proves that it is deterministic and that it
contains the transitions that the simulation uses.
-/
import Lax251941Proofs.Source.Sim.Walk
import Lax251941Proofs.Source.Sim.Counter

namespace Lax251941Proofs.PCP
namespace Sim

/-! ## Cells -/

/-- A tape cell: one bit per register. -/
abbrev Cell (N : ℕ) := Fin N → Bool

/-- The blank cell, with all bits clear. -/
def blankCell (N : ℕ) : Cell N := fun _ => false

/-- The bit of a cell at a register index. -/
def bitOf {N : ℕ} (x : Cell N) (r : ℕ) : Bool := if h : r < N then x ⟨r, h⟩ else false

/-- Set one bit of a cell. -/
def setBit {N : ℕ} (x : Cell N) (r : ℕ) : Cell N := fun i => if (i : ℕ) = r then true else x i

/-- Clear one bit of a cell. -/
def clrBit {N : ℕ} (x : Cell N) (r : ℕ) : Cell N := fun i => if (i : ℕ) = r then false else x i

@[simp] lemma bitOf_blank (N r : ℕ) : bitOf (blankCell N) r = false := by
  simp [bitOf, blankCell]

lemma bitOf_setBit {N : ℕ} (x : Cell N) {r : ℕ} (hr : r < N) (t : ℕ) :
    bitOf (setBit x r) t = if t = r then true else bitOf x t := by
  unfold bitOf setBit
  by_cases ht : t < N
  · by_cases h : t = r <;> simp [ht, h, hr]
  · have : t ≠ r := by omega
    simp [ht, this]

lemma bitOf_clrBit {N : ℕ} (x : Cell N) {r : ℕ} (hr : r < N) (t : ℕ) :
    bitOf (clrBit x r) t = if t = r then false else bitOf x t := by
  unfold bitOf clrBit
  by_cases ht : t < N
  · by_cases h : t = r <;> simp [ht, h, hr]
  · have : t ≠ r := by omega
    simp [ht, this]

/-- Cells are determined by their bits. -/
lemma cell_ext {N : ℕ} {x y : Cell N} (h : ∀ r, bitOf x r = bitOf y r) : x = y := by
  funext i
  have := h i
  simpa [bitOf, i.isLt] using this

/-- The code of a cell as a tape symbol.  The blank cell has code `0`, the blank tape
symbol of the model. -/
noncomputable def cellCode {N : ℕ} (x : Cell N) : ℕ :=
  if x = blankCell N then 0 else (Fintype.equivFin (Cell N) x : ℕ) + 1

@[simp] lemma cellCode_blank (N : ℕ) : cellCode (blankCell N) = 0 := by simp [cellCode]

lemma cellCode_injective (N : ℕ) : Function.Injective (cellCode (N := N)) := by
  intro x y h
  unfold cellCode at h
  by_cases hx : x = blankCell N <;> by_cases hy : y = blankCell N
  · rw [hx, hy]
  · simp [hx, hy] at h
  · simp [hx, hy] at h
  · simp only [hx, hy, if_false] at h
    exact (Fintype.equivFin (Cell N)).injective (Fin.ext (by omega))

lemma cellCode_le (N : ℕ) (x : Cell N) : cellCode x ≤ Fintype.card (Cell N) := by
  unfold cellCode
  by_cases hx : x = blankCell N
  · simp [hx]
  · simp only [hx, if_false]
    have := (Fintype.equivFin (Cell N) x).isLt
    omega

/-- The marker symbol at the left end of the tape. -/
def mark (N : ℕ) : ℕ := Fintype.card (Cell N) + 1

lemma cellCode_ne_mark {N : ℕ} (x : Cell N) : cellCode x ≠ mark N := by
  have := cellCode_le N x
  simp only [mark]
  omega

/-- Decoding a tape symbol into a cell. -/
noncomputable def cellOf (N : ℕ) (a : ℕ) : Cell N := Function.invFun (cellCode (N := N)) a

@[simp] lemma cellOf_cellCode {N : ℕ} (x : Cell N) : cellOf N (cellCode x) = x :=
  Function.leftInverse_invFun (cellCode_injective N) x

/-! ## States -/

/-- At the home square, about to execute instruction `p`. -/
def stHome (p : ℕ) : ℕ := 8 * p
/-- Walking left back to the home square. -/
def stBack (p : ℕ) : ℕ := 8 * p + 1
/-- One square right of home, about to step back onto it. -/
def stBounce (p : ℕ) : ℕ := 8 * p + 2
/-- Searching right for the cell to set, for an increment. -/
def stSinc (p : ℕ) : ℕ := 8 * p + 3
/-- Testing the first cell, for a decrement. -/
def stTdec (p : ℕ) : ℕ := 8 * p + 4
/-- Searching right for the cell to clear, for a decrement. -/
def stSdec (p : ℕ) : ℕ := 8 * p + 5
/-- Clearing the cell, for a decrement. -/
def stCdec (p : ℕ) : ℕ := 8 * p + 6
/-- One square right of home, about to step back onto it, for a jump. -/
def stJmp (p : ℕ) : ℕ := 8 * p + 7

/-! ## The transition function -/

/-- The transition of the machine in the state indexed by `(p, k)` reading the symbol
`a`. -/
noncomputable def deltaAt (P : Prog) (N : ℕ) (p k a : ℕ) : Option (ℕ × ℕ × Bool) :=
  match P[p]? with
  | none => none
  | some ins =>
    if a = mark N then
      if k = 0 then
        match ins with
        | .inc _ => some (stSinc p, mark N, true)
        | .dec _ _ => some (stTdec p, mark N, true)
        | .jmp _ => some (stJmp p, mark N, true)
      else if k = 1 then some (stBounce p, mark N, true)
      else none
    else
      if k = 1 then some (stBack p, a, false)
      else if k = 2 then some (stHome (min (p + 1) P.length), a, false)
      else
        match ins with
        | .inc r =>
            if k = 3 then
              (if bitOf (cellOf N a) r then some (stSinc p, a, true)
               else some (stBack p, cellCode (setBit (cellOf N a) r), false))
            else none
        | .dec r j =>
            if k = 4 then
              (if bitOf (cellOf N a) r then some (stSdec p, a, true)
               else some (stHome (min j P.length), a, false))
            else if k = 5 then
              (if bitOf (cellOf N a) r then some (stSdec p, a, true)
               else some (stCdec p, a, false))
            else if k = 6 then some (stBack p, cellCode (clrBit (cellOf N a) r), false)
            else none
        | .jmp j => if k = 7 then some (stHome (min j P.length), a, false) else none

/-- The transition function of the machine. -/
noncomputable def delta (P : Prog) (N : ℕ) (q a : ℕ) : Option (ℕ × ℕ × Bool) :=
  deltaAt P N (q / 8) (q % 8) a

lemma delta_eq (P : Prog) (N : ℕ) (p k a : ℕ) (hk : k < 8) :
    delta P N (8 * p + k) a = deltaAt P N p k a := by
  unfold delta
  congr 1
  · omega
  · omega

/-! ## The transition table -/

/-- All cell codes. -/
noncomputable def cellCodes (N : ℕ) : List ℕ :=
  (Finset.univ : Finset (Cell N)).toList.map cellCode

lemma mem_cellCodes {N : ℕ} (x : Cell N) : cellCode x ∈ cellCodes N :=
  List.mem_map_of_mem (by simp [Finset.mem_toList])

/-- The tape alphabet: the marker and the cell codes. -/
noncomputable def symList (N : ℕ) : List ℕ := mark N :: cellCodes N

lemma mark_mem_symList (N : ℕ) : mark N ∈ symList N := by simp [symList]

lemma cellCode_mem_symList {N : ℕ} (x : Cell N) : cellCode x ∈ symList N :=
  List.mem_cons_of_mem _ (mem_cellCodes x)

/-- The keys of the transition table. -/
noncomputable def keyList (P : Prog) (N : ℕ) : List (ℕ × ℕ) :=
  (List.range (8 * (P.length + 1))) ×ˢ symList N

lemma mem_keyList {P : Prog} {N q a : ℕ} (hq : q < 8 * (P.length + 1)) (ha : a ∈ symList N) :
    (q, a) ∈ keyList P N := by
  simp only [keyList, List.mem_product, List.mem_range]
  exact ⟨hq, ha⟩

/-- The transition table of the machine simulating `P`. -/
noncomputable def tmTrans (P : Prog) (N : ℕ) : List (ℕ × ℕ × ℕ × ℕ × Bool) :=
  (keyList P N).filterMap fun k =>
    (delta P N k.1 k.2).map fun v => (k.1, k.2, v.1, v.2.1, v.2.2)

lemma mem_tmTrans_iff {P : Prog} {N q a r b : ℕ} {d : Bool} :
    (q, a, r, b, d) ∈ tmTrans P N ↔ (q, a) ∈ keyList P N ∧ delta P N q a = some (r, b, d) := by
  simp only [tmTrans, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨q', a'⟩, hk, ⟨v, hv, heq⟩⟩
    obtain ⟨r', b', d'⟩ := v
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    exact ⟨hk, hv⟩
  · rintro ⟨hk, hv⟩
    exact ⟨(q, a), hk, ⟨(r, b, d), hv, rfl⟩⟩

/-- The tape machine simulating the program `P` on `N` registers. -/
noncomputable def tmOf (P : Prog) (N : ℕ) : TM where
  trans := tmTrans P N
  q0 := stHome 0
  qacc := stHome P.length

@[simp] lemma tmOf_trans (P : Prog) (N : ℕ) : (tmOf P N).trans = tmTrans P N := rfl
@[simp] lemma tmOf_q0 (P : Prog) (N : ℕ) : (tmOf P N).q0 = stHome 0 := rfl
@[simp] lemma tmOf_qacc (P : Prog) (N : ℕ) : (tmOf P N).qacc = stHome P.length := rfl

lemma det_tmOf (P : Prog) (N : ℕ) : Det (tmOf P N) := by
  rintro ⟨q, a, r, b, d⟩ hx ⟨q', a', r', b', d'⟩ hy h1 h2
  simp only at h1 h2
  subst h1; subst h2
  rw [tmOf_trans, mem_tmTrans_iff] at hx hy
  have := hx.2.symm.trans hy.2
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

/-! ## The transitions used by the simulation -/

variable {P : Prog} {N : ℕ}

private lemma mem_trans_of_delta {q a r b : ℕ} {d : Bool}
    (hq : q < 8 * (P.length + 1)) (ha : a ∈ symList N) (h : delta P N q a = some (r, b, d)) :
    (q, a, r, b, d) ∈ (tmOf P N).trans :=
  mem_tmTrans_iff.mpr ⟨mem_keyList hq ha, h⟩

lemma home_lt {p : ℕ} (hp : p < P.length) (k : ℕ) (hk : k < 8) :
    8 * p + k < 8 * (P.length + 1) := by omega

/-- Entering an increment. -/
lemma trans_inc_start {p r : ℕ} (hp : P[p]? = some (.inc r)) :
    (stHome p, mark N, stSinc p, mark N, true) ∈ (tmOf P N).trans := by
  have hplt : p < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hp
    exact absurd hp (by simp)
  refine mem_trans_of_delta (by simpa [stHome] using home_lt hplt 0 (by omega))
    (mark_mem_symList N) ?_
  rw [show stHome p = 8 * p + 0 by simp [stHome], delta_eq _ _ _ _ _ (by omega)]
  rw [deltaAt, hp]
  simp

/-- Entering a decrement. -/
lemma trans_dec_start {p r j : ℕ} (hp : P[p]? = some (.dec r j)) :
    (stHome p, mark N, stTdec p, mark N, true) ∈ (tmOf P N).trans := by
  have hplt : p < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hp
    exact absurd hp (by simp)
  refine mem_trans_of_delta (by simpa [stHome] using home_lt hplt 0 (by omega))
    (mark_mem_symList N) ?_
  rw [show stHome p = 8 * p + 0 by simp [stHome], delta_eq _ _ _ _ _ (by omega)]
  rw [deltaAt, hp]
  simp

/-- Entering a jump. -/
lemma trans_jmp_start {p j : ℕ} (hp : P[p]? = some (.jmp j)) :
    (stHome p, mark N, stJmp p, mark N, true) ∈ (tmOf P N).trans := by
  have hplt : p < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hp
    exact absurd hp (by simp)
  refine mem_trans_of_delta (by simpa [stHome] using home_lt hplt 0 (by omega))
    (mark_mem_symList N) ?_
  rw [show stHome p = 8 * p + 0 by simp [stHome], delta_eq _ _ _ _ _ (by omega)]
  rw [deltaAt, hp]
  simp

private lemma plt {p : ℕ} {ins : Instr} (hp : P[p]? = some ins) : p < P.length := by
  by_contra h
  rw [List.getElem?_eq_none (by omega)] at hp
  exact absurd hp (by simp)

/-- Walking left, back towards the home square. -/
lemma trans_back_cell {p : ℕ} {ins : Instr} (hp : P[p]? = some ins) (x : Cell N) :
    (stBack p, cellCode x, stBack p, cellCode x, false) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stBack] using home_lt (plt hp) 1 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stBack p = 8 * p + 1 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark, stBack]

/-- Arriving at the home square: bounce off it to the right. -/
lemma trans_back_mark {p : ℕ} {ins : Instr} (hp : P[p]? = some ins) :
    (stBack p, mark N, stBounce p, mark N, true) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stBack] using home_lt (plt hp) 1 (by omega))
    (mark_mem_symList N) ?_
  rw [show stBack p = 8 * p + 1 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp

/-- Bouncing back onto the home square, with the next instruction. -/
lemma trans_bounce {p : ℕ} {ins : Instr} (hp : P[p]? = some ins) (x : Cell N) :
    (stBounce p, cellCode x, stHome (min (p + 1) P.length), cellCode x, false)
      ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stBounce] using home_lt (plt hp) 2 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stBounce p = 8 * p + 2 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark]

/-- Searching for the cell to set: this one is already set. -/
lemma trans_sinc_move {p r : ℕ} (hp : P[p]? = some (.inc r)) {x : Cell N}
    (hx : bitOf x r = true) :
    (stSinc p, cellCode x, stSinc p, cellCode x, true) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stSinc] using home_lt (plt hp) 3 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stSinc p = 8 * p + 3 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark, hx, stSinc]

/-- Searching for the cell to set: this one is clear, so set it and go home. -/
lemma trans_sinc_set {p r : ℕ} (hp : P[p]? = some (.inc r)) {x : Cell N}
    (hx : bitOf x r = false) :
    (stSinc p, cellCode x, stBack p, cellCode (setBit x r), false) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stSinc] using home_lt (plt hp) 3 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stSinc p = 8 * p + 3 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark, hx]

/-- Testing the first cell: the register is zero, so jump. -/
lemma trans_tdec_zero {p r j : ℕ} (hp : P[p]? = some (.dec r j)) {x : Cell N}
    (hx : bitOf x r = false) :
    (stTdec p, cellCode x, stHome (min j P.length), cellCode x, false) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stTdec] using home_lt (plt hp) 4 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stTdec p = 8 * p + 4 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark, hx]

/-- Testing the first cell: the register is positive, so start searching. -/
lemma trans_tdec_pos {p r j : ℕ} (hp : P[p]? = some (.dec r j)) {x : Cell N}
    (hx : bitOf x r = true) :
    (stTdec p, cellCode x, stSdec p, cellCode x, true) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stTdec] using home_lt (plt hp) 4 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stTdec p = 8 * p + 4 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark, hx]

/-- Searching for the last set cell: this one is set, so carry on. -/
lemma trans_sdec_move {p r j : ℕ} (hp : P[p]? = some (.dec r j)) {x : Cell N}
    (hx : bitOf x r = true) :
    (stSdec p, cellCode x, stSdec p, cellCode x, true) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stSdec] using home_lt (plt hp) 5 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stSdec p = 8 * p + 5 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark, hx, stSdec]

/-- Searching for the last set cell: this one is clear, so step back onto the last one. -/
lemma trans_sdec_stop {p r j : ℕ} (hp : P[p]? = some (.dec r j)) {x : Cell N}
    (hx : bitOf x r = false) :
    (stSdec p, cellCode x, stCdec p, cellCode x, false) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stSdec] using home_lt (plt hp) 5 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stSdec p = 8 * p + 5 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark, hx]

/-- Clearing the last set cell. -/
lemma trans_cdec {p r j : ℕ} (hp : P[p]? = some (.dec r j)) (x : Cell N) :
    (stCdec p, cellCode x, stBack p, cellCode (clrBit x r), false) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stCdec] using home_lt (plt hp) 6 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stCdec p = 8 * p + 6 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark]

/-- Completing a jump. -/
lemma trans_jmp_end {p j : ℕ} (hp : P[p]? = some (.jmp j)) (x : Cell N) :
    (stJmp p, cellCode x, stHome (min j P.length), cellCode x, false) ∈ (tmOf P N).trans := by
  refine mem_trans_of_delta (by simpa [stJmp] using home_lt (plt hp) 7 (by omega))
    (cellCode_mem_symList x) ?_
  rw [show stJmp p = 8 * p + 7 from rfl, delta_eq _ _ _ _ _ (by omega), deltaAt, hp]
  simp [cellCode_ne_mark]

end Sim
end Lax251941Proofs.PCP
