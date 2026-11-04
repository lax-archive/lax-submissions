import Lax185574Proofs.RamPipe
import Lax185574Proofs.RamRuler

/-!
The dovetailer. Thread `i` simulates `Q` on `i :: x` at word length
`w - K - i`. Slot `j` executes one instruction of thread `ruler j`.
Thread `i` keeps its program counter, cursor, output count, a dead flag
and its output buffer in a record of `B + 5` cells at `40 + (B + 5) i`,
and its memory in a region of `2 ^ (w - K - i)` cells in the upper half
of memory. A thread that halts with output `1 :: y` makes the machine
output `y`. A thread that halts otherwise, or overflows its buffer, is
marked dead.

Cells: `0` to `15` as in every simulation, the segment table at `16`
to `19` (the entry `i` and the input), and the scheduler's cells:
`20` slot counter, `21` thread, `22` halving, `23` the power
`2 ^ (K + i)`, `24` record address, `25` saved counter, `26` the
largest word, `27` the size `2 ^ (w - K)` of thread zero, `28` the
half `2 ^ (w - 1)`, `29` two, `34` record size, `35` record base, `36`
`K`.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

/-- The segment kinds of a thread's input `i :: x`. -/
def dvKs : List SegKind := [.val, .input]

section code

variable (Q : Program) (B K : ℕ)

def dvR : ℕ := B + 5
def dvL : ℕ := blockLen dvKs

def dvL0 : ℕ := 16
def dvDisp : ℕ := dvL0 + 36
def dvH : ℕ := dvDisp + 2 * Q.length + 1
def dvStub : ℕ := dvH Q + dvL * Q.length
def dvSave : ℕ := dvStub Q + 2 * Q.length
def dvSkip : ℕ := dvSave Q + 9
def dvDead : ℕ := dvSkip Q + 2
def dvExit : ℕ := dvDead Q + 5

/-- Constants. -/
def dvInit : Program :=
  [.set rOne 1, .set 29 2, .not 26 rZ, .div 28 26 29, .add 28 28 rOne, .set 36 K,
    .shiftl 23 rOne 36, .div 27 26 23, .add 27 27 rOne, .inputLength 18, .set 16 1,
    .add rTot 18 rOne, .set rCap (B + 1), .set 34 (dvR B), .set 35 40, .set 20 1]

/-- Find the thread of the slot, check it, and load its record. -/
def dvHead : Program :=
  [.jzero 20 (dvSkip Q), .add 22 20 rZ, .set 21 0,
    -- halving loop
    .div rT 22 29, .mul rT rT 29, .sub rT 22 rT, .jzero rT (dvL0 + 8), .jump (dvL0 + 11),
    .div 22 22 29, .add 21 21 rOne, .jump (dvL0 + 3),
    -- validity, record, dead flag
    .add rT 36 21, .shiftl 23 rOne rT, .jzero 23 (dvSkip Q), .mul 24 21 34, .add 24 24 35,
    .set rT 3, .add rT rT 24, .load rU rT, .jzero rU (dvL0 + 21), .jump (dvSkip Q),
    -- load the context
    .div rMask 26 23, .add rU rMask rOne, .sub rT 27 rU, .add rT rT rT, .add rBase 28 rT,
    .set rT 1, .add rT rT 24, .load rCur rT, .set rT 2, .add rT rT 24, .load rOC rT,
    .set rT 4, .add rOB 24 rT, .add 17 21 rZ, .load rD 24]

/-- Jump to the block of the saved counter, or to the exit handler. -/
def dvDispatch : Program :=
  ((List.range Q.length).map fun l => [.jzero rD (dvH Q + dvL * l), .sub rD rD rOne]).flatten ++
    [.jump (dvExit Q)]

def dvCode : Code where
  ks := dvKs
  tb := 16
  mode := .buffer (dvDead Q)
  tgt := fun l => if l < Q.length then dvStub Q + 2 * l else dvExit Q
  exit := dvExit Q

/-- Record the counter of the next instruction. -/
def dvStubs : Program :=
  ((List.range Q.length).map fun l => [.set 25 l, .jump (dvSave Q)]).flatten

def dvSaveCode : Program :=
  [.store 24 25, .set rT 1, .add rT rT 24, .store rT rCur, .set rT 2, .add rT rT 24,
    .store rT rOC, .add 20 20 rOne, .jump dvL0]

def dvSkipCode : Program := [.add 20 20 rOne, .jump dvL0]

def dvDeadCode : Program :=
  [.set rT 3, .add rT rT 24, .store rT rOne, .add 20 20 rOne, .jump dvL0]

/-- Accept if the output starts with `1`: write the rest and halt. -/
def dvExitCode : Program :=
  [.jzero rOC (dvDead Q), .load rB rOB, .sub rU rB rOne, .jzero rU (dvExit Q + 5),
    .jump (dvDead Q), .jzero rB (dvDead Q), .set rC 1,
    .sub rU rOC rC, .jzero rU (dvExit Q + 14), .add rT rOB rC, .load rB rT, .write rB,
    .add rC rC rOne, .jump (dvExit Q + 7), .halt]

def dvProg : Program :=
  dvInit B K ++ dvHead Q ++ dvDispatch Q ++ blocks (dvCode Q) (dvH Q) dvL Q ++ dvStubs Q ++
    dvSaveCode ++ dvSkipCode ++ dvDeadCode ++ dvExitCode Q

end code

end Lax185574Proofs.RamSim
