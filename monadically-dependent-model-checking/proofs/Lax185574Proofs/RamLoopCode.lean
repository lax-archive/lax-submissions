import Lax185574Proofs.RamSimBack
import Lax185574Proofs.RamPipe

/-!
The loop driver (call combinator). It alternates two simulated
programs, a glue program `G` and a callee `P`, on words passed through
memory buffers.

Round `j` runs `G` on the word `lpU x a b`, built from the input `x`,
the previous output `a` of `G` and the previous output `b` of `P`.
`G` starts on `a = [0, |x|, |x|]` and `b = []`, that is, on
`0 :: |x| :: x ++ [0]`. If the output `o` of `G` starts with `0`, the
driver outputs the rest of `o` and halts. Otherwise it runs `P` on
`lpQ o = o.drop (3 + o[1])` and starts the next round with `a = o` and
`b` the output of `P`. In the next round `G` sees
`o[0] :: o[1] :: (x.drop o[3]).take o[2] ++ (o.drop 3).take o[1] ++ |b| :: b`.
So `G` saves a state of length `o[1]` in its output, may ask for the
window of the input of length `o[2]` that starts at the first entry
`o[3]` of its state, and receives the answer of `P`. The window lets
`G` read a piece of a long input without reading all that precedes it.

Every simulated run gets a fresh memory region, never reused, so no
memory has to be cleared. Region `i` belongs to batch `j = log₂ (i+1)`
and has `2 ^ (w - 3 - 2 j)` cells, so the regions of a batch take half
the room of the batch before. The outputs go to four buffers of
`2 ^ (w - 3)` cells in the upper half of memory, two for `G` and two
for `P`, used in turn. An
overflow of a buffer, an empty output of `G` and an exhausted supply of
regions end in a loop, so they never produce a halting run.

Cells: `0` to `14` as in every simulation, `15` the input length, the
segment table at `16` to `27`, evaluation cells `28` to `35`, the first
`a` in `37` to `39`, and the driver's cells: `40`, `41` base and length
of `a`, `42`, `43` base and length of `b`, `44`, `45` the buffer of the
current output of `G`, `46` the buffer of the current output of `P`,
`47` the next free region, `48` the region size, `49` and `50` the
position in the batch and the batch size, `51` the buffer size `C`,
`52` the constant four, `53` a scratch cell, and `54` to `57` the
buffer bases `4 C` to `7 C`. The regions start at `64`.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

/-! ### Words passed between the rounds -/

/-- The input of `G`:
`a[0] :: a[1] :: (x.drop a[3]).take a[2] ++ (a.drop 3).take a[1] ++ |b| :: b`. -/
def lpU (x a b : List ℕ) : List ℕ :=
  [a.getD 0 0, a.getD 1 0] ++ (x.drop (a.getD 3 0)).take (a.getD 2 0) ++
    (a.drop 3).take (a.getD 1 0) ++ (b.length :: b)

/-- The query to `P` in the output `o` of `G`. -/
def lpQ (o : List ℕ) : List ℕ := o.drop (3 + o.getD 1 0)

/-- The first `a`. -/
def lpA0 (x : List ℕ) : List ℕ := [0, x.length, x.length]

/-- The sources of `G`: the input, `a` and `b`. -/
def lpSrcsG : Fin 3 → Src := ![⟨.input, 15⟩, ⟨.mem 40, 41⟩, ⟨.mem 42, 43⟩]

/-- The sources of `P`: the output of `G`. -/
def lpSrcsP : Fin 1 → Src := ![⟨.mem 44, 45⟩]

def lpRhoG : Rewrite 3 :=
  [.expr (.entry 1 0), .expr (.entry 1 1), .slice 0 (.entry 1 3) (some (.entry 1 2)),
    .slice 1 (.lit 3) (some (.entry 1 1)), .expr (.len 2), .slice 2 (.lit 0) none]

def lpRhoP : Rewrite 1 := [.slice 0 (.add (.lit 3) (.entry 0 1)) none]

theorem lpRhoG_apply (x a b : List ℕ) : lpRhoG.apply ![x, a, b] = lpU x a b := by
  simp [lpRhoG, Rewrite.apply, Segment.apply, HExpr.eval, lpU]

theorem lpRhoP_apply (o : List ℕ) : lpRhoP.apply ![o] = lpQ o := by
  simp [lpRhoP, Rewrite.apply, Segment.apply, HExpr.eval, lpQ]

def lpKsG : List SegKind := lpRhoG.map (segKind lpSrcsG)
def lpKsP : List SegKind := lpRhoP.map (segKind lpSrcsP)

/-! ### Regions -/

/-- The allocation state before region `i`: the next free cell, the
region size, the position in the batch, the batch size and the batch. -/
structure Alloc where
  next : ℕ
  size : ℕ
  cnt : ℕ
  lim : ℕ
  bat : ℕ

def Alloc.step (A : Alloc) : Alloc :=
  if A.cnt + 1 = A.lim then ⟨A.next + A.size, A.size / 4, 0, 2 * A.lim, A.bat + 1⟩
  else ⟨A.next + A.size, A.size, A.cnt + 1, A.lim, A.bat⟩

/-- The allocation state before region `i`, for buffers of `C` cells. -/
def lpAlloc (C : ℕ) : ℕ → Alloc
  | 0 => ⟨64, C, 0, 1, 0⟩
  | i + 1 => (lpAlloc C i).step

/-- The buffer size `2 ^ (w - 3)`. -/
def lpCap (w : ℕ) : ℕ := 2 ^ (w - 3)

/-- The word length of the run in region `i`. -/
def lpV (w i : ℕ) : ℕ := w - 3 - 2 * (lpAlloc (lpCap w) i).bat

/-- The size of region `i`. -/
def lpSize (w i : ℕ) : ℕ := (lpAlloc (lpCap w) i).size

def lpBase (w i : ℕ) : ℕ := (lpAlloc (lpCap w) i).next

theorem lpAlloc_inv (C : ℕ) (i : ℕ) :
    (lpAlloc C i).cnt < (lpAlloc C i).lim ∧ (lpAlloc C i).lim = 2 ^ (lpAlloc C i).bat ∧
      (lpAlloc C i).size = C / 4 ^ (lpAlloc C i).bat ∧
      i + 1 = (lpAlloc C i).lim + (lpAlloc C i).cnt ∧
      (lpAlloc C i).next + ((lpAlloc C i).lim - (lpAlloc C i).cnt) * (lpAlloc C i).size +
        (lpAlloc C i).size * (lpAlloc C i).lim ≤ 64 + 2 * C := by
  induction i with
  | zero => simp [lpAlloc]; omega
  | succ i ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      rw [show lpAlloc C (i + 1) = (lpAlloc C i).step from rfl]
      generalize lpAlloc C i = A at *
      obtain ⟨n, s, c, l, j⟩ := A
      simp only at h1 h2 h3 h4 h5
      unfold Alloc.step
      split_ifs with h
      · simp only at h ⊢
        refine ⟨by omega, by rw [h2, pow_succ]; ring, ?_, by omega, ?_⟩
        · rw [h3, Nat.div_div_eq_div_mul, pow_succ]
        · have hl : l - c = 1 := by omega
          rw [hl] at h5
          have : s / 4 * 4 ≤ s := Nat.div_mul_le_self _ _
          simp only [Nat.sub_zero]
          nlinarith
      · simp only at h ⊢
        refine ⟨by omega, h2, h3, by omega, ?_⟩
        have : l - c = (l - (c + 1)) + 1 := by omega
        rw [this] at h5
        nlinarith

/-- Region `i` lies below `64 + 2 C`. -/
theorem lpAlloc_room (C i : ℕ) : (lpAlloc C i).next + (lpAlloc C i).size ≤ 64 + 2 * C := by
  obtain ⟨h1, -, -, -, h5⟩ := lpAlloc_inv C i
  have : (lpAlloc C i).size ≤ ((lpAlloc C i).lim - (lpAlloc C i).cnt) * (lpAlloc C i).size :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem lpAlloc_next_mono (C i : ℕ) : (lpAlloc C i).next + (lpAlloc C i).size ≤
    (lpAlloc C (i + 1)).next := by
  simp only [lpAlloc, Alloc.step]; split_ifs <;> simp

theorem lpAlloc_next_le {C i i' : ℕ} (h : i ≤ i') : (lpAlloc C i).next ≤ (lpAlloc C i').next := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (le_trans (Nat.le_add_right _ _) (lpAlloc_next_mono C _))

theorem lpAlloc_next_ge (C i : ℕ) : 64 ≤ (lpAlloc C i).next :=
  le_trans (by simp [lpAlloc]) (lpAlloc_next_le (C := C) (Nat.zero_le i))

/-- A region that is not empty has `2 ^ lpV w i` cells. -/
theorem lpSize_eq {w i : ℕ} (h : lpSize w i ≠ 0) : lpSize w i = 2 ^ lpV w i := by
  obtain ⟨-, -, h3, -, -⟩ := lpAlloc_inv (lpCap w) i
  simp only [lpSize, lpV, lpCap] at *
  rw [h3] at h ⊢
  generalize (lpAlloc (2 ^ (w - 3)) i).bat = j at *
  rw [show (4 : ℕ) ^ j = 2 ^ (2 * j) by rw [pow_mul]; norm_num] at h ⊢
  by_cases hj : 2 * j ≤ w - 3
  · rw [Nat.pow_div hj (by norm_num)]
  · exfalso; apply h
    exact Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- Region `i` has at least `2 ^ (w - 3) / (i + 1) ^ 2` cells. -/
theorem lpAlloc_bat_succ (C i : ℕ) : (lpAlloc C (i + 1)).bat ≤ (lpAlloc C i).bat + 1 := by
  show (lpAlloc C i).step.bat ≤ _
  unfold Alloc.step
  split_ifs <;> simp

/-- The word length drops by at most two from one region to the next. -/
theorem lpV_succ_ge (w i : ℕ) : lpV w i - 2 ≤ lpV w (i + 1) := by
  have := lpAlloc_bat_succ (lpCap w) i
  simp only [lpV]; omega

theorem lpSize_ge (w i : ℕ) : lpCap w / (i + 1) ^ 2 ≤ lpSize w i := by
  obtain ⟨-, h2, h3, h4, -⟩ := lpAlloc_inv (lpCap w) i
  simp only [lpSize]
  rw [h3]
  apply Nat.div_le_div_left _ (by positivity)
  rw [show (4 : ℕ) ^ (lpAlloc (lpCap w) i).bat = (2 ^ (lpAlloc (lpCap w) i).bat) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num, ← h2]
  exact Nat.pow_le_pow_left (by omega) 2

/-! ### The code -/

section code

variable (G P : Program)

/-- Constants, buffers, the first `a` (in the cells `37` to `39`), the
region allocator. -/
def lpInit : Program :=
  [.set rOne 1, .set rT 8, .not rMask rZ, .div rMask rMask rT, .add 51 rMask rOne,
    .inputLength 15, .add 38 15 rZ, .add 39 15 rZ, .set 40 37, .set 41 3,
    .add 53 51 51, .add 54 53 53, .add 55 54 51, .add 56 55 51, .add 57 56 51,
    .add 44 54 rZ, .add 46 56 rZ, .set 47 64, .add 48 51 rZ, .set 50 1, .set 52 4]

def lpLoop : ℕ := 21

/-- Take the next region, or die if none is left. -/
def lpAllocCode (die A : ℕ) : Program :=
  [.jzero 48 die, .add rBase 47 rZ, .sub rMask 48 rOne, .add 47 47 48, .add 49 49 rOne,
    .sub rU 50 49, .jzero rU (A + 8), .jump (A + 11), .set 49 0, .add 50 50 50, .div 48 48 52]

/-- Fresh cursor, empty input total, and the output buffer at the base in `obc`. -/
def lpPrelude (obc : ℕ) : Program :=
  [.set rCur 0, .set rTot 0, .add rOB obc rZ, .set rOC 0, .add rCap 51 rZ]

def lpRwG : Program := rwCode lpSrcsG 28 16 lpRhoG 0 (lpLoop + 16)
def lpHG : ℕ := lpLoop + 16 + lpRwG.length
def lpExitG : ℕ := lpHG + blockLen lpKsG * G.length
def lpStartP : ℕ := lpExitG G + 4
def lpRwP : Program := rwCode lpSrcsP 28 16 lpRhoP 0 (lpStartP G + 16)
def lpHP : ℕ := lpStartP G + 16 + (lpRwP G).length
def lpExitP : ℕ := lpHP G + blockLen lpKsP * P.length
def lpOut : ℕ := lpExitP G P + 9
def lpDie : ℕ := lpOut G P + 9

def lpCodeG : Code where
  ks := lpKsG
  tb := 16
  mode := .buffer (lpDie G P)
  tgt := fun l => if l < G.length then lpHG + blockLen lpKsG * l else lpExitG G
  exit := lpExitG G

def lpCodeP : Code where
  ks := lpKsP
  tb := 16
  mode := .buffer (lpDie G P)
  tgt := fun l => if l < P.length then lpHP G + blockLen lpKsP * l else lpExitP G P
  exit := lpExitP G P

/-- After `G`: die on an empty output, finish on a leading `0`, and
otherwise record the length of the output. -/
def lpExitGCode : Program :=
  [.jzero rOC (lpDie G P), .load rB rOB, .jzero rB (lpOut G P), .add 45 rOC rZ]

/-- After `P`: the outputs become `a` and `b`, and the other buffers
are used next. -/
def lpSwap : Program :=
  [.add 40 44 rZ, .add 41 45 rZ, .sub 53 55 44, .add 44 54 53,
    .add 42 46 rZ, .add 43 rOC rZ, .sub 53 57 46, .add 46 56 53, .jump lpLoop]

/-- Write the output of `G` from its second entry, and halt. -/
def lpOutCode : Program :=
  [.set rC 1, .sub rU rOC rC, .jzero rU (lpOut G P + 8), .add rT rOB rC, .load rB rT,
    .write rB, .add rC rC rOne, .jump (lpOut G P + 1), .halt]

def lpProg : Program :=
  lpInit ++ (lpAllocCode (lpDie G P) lpLoop ++ lpPrelude 44 ++ lpRwG) ++
    blocks (lpCodeG G P) lpHG (blockLen lpKsG) G ++
    (lpExitGCode G P ++ lpAllocCode (lpDie G P) (lpStartP G) ++ lpPrelude 46 ++ lpRwP G) ++
    blocks (lpCodeP G P) (lpHP G) (blockLen lpKsP) P ++
    (lpSwap ++ lpOutCode G P ++ [.jump (lpDie G P)])

end code

end Lax185574Proofs.RamSim
