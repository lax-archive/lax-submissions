/-
**The record-breaker decomposition is a chain of pieces.**

The mathematical half of stage 1 of the induction step of the book's snake
lemma: on every good input -- a nonempty input whose run halts and has width at
most `K` -- the record-breaker decomposition of the run supplies a chain of
pieces in the sense of `Transducers.TwoWay.Chk.ChainData`.  The blocks are cut
at the record-breaking columns (`TwoWay.snakeY`), the `2K+1` piece slots of a
pair are the `2K` halves of the `K` excursions of its record-breaking column
followed by the progress part, and the confinement of the pieces to two
neighbouring blocks is the one proved in
`RequestProject/PartC/SnakeConfine.lean`.

What this adds to `TwoWay.exists_isSnakeMarking`
(`RequestProject/PartC/SnakeData.lean`) is the *chain* structure: the entry and
the exit state of every piece, the cut at which it starts and the cut at which
it ends, and the window condition
(`Transducers.TwoWay.Chk.WinCond`) of its window -- the data that the checking
automaton of stage 1 verifies.  Every one of those is supplied, slot by slot, by
`Transducers.TwoWay.Chk.exists_slotOK`
(`RequestProject/PartC/SnakeChkSlotOK.lean`); what is left here is to check that
the slots really chain, which they do because the cut and the state at the two
ends of a piece are, by construction, the position and the state of the run at
the two times that delimit the slot.
-/
import Lax916827Proofs.Source.PartC.SnakeChkData
import Lax916827Proofs.Source.PartC.SnakeChkRel
import Lax916827Proofs.Source.PartC.SnakeChkSlotOK
import Lax916827Proofs.Source.PartC.SnakeData
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open RegPair

variable {A B Q : Type}

/-- The first record-breaking column is reached at time `0`. -/
lemma rbFirst_zero (M : TwoWay A B Q) (w : List A) : rbFirst M w 0 = 0 := by
  have hvis : (0 : ℕ) ∈ Walk.visitSet (traj M w) 0 (endT M w) (rbCol M w 0) :=
    ⟨le_refl 0, Nat.zero_le _, by rw [traj_zero, rbCol_zero]⟩
  have h : rbFirst M w 0 ≤ 0 := Walk.firstV_le hvis
  omega

/-- **Every good input carries a chain of pieces**: the record-breaker
decomposition of its run. -/
theorem nonempty_chainData_of_good [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) {w : List A} (hgood : GoodInput M K w) :
    Nonempty (ChainData M K w) := by
  classical
  obtain ⟨hw, ⟨T, hT⟩, hwidth⟩ := hgood
  choose a b p hslot using exists_slotOK hT hwidth hK
  have hKpos : 0 < K := by omega
  -- the start and the end of the last slot of the last pair coincide
  have hstN : pcStart M w K (rbN M w) (2 * K) = rbLast M w (rbN M w) := by
    rw [pcStart, if_pos rfl]
  have henN : pcEnd M w K (rbN M w) (2 * K) = rbLast M w (rbN M w) := by
    rw [pcEnd, if_pos rfl, if_neg (lt_irrefl _)]
  refine ⟨{
    N := rbN M w
    Y := snakeY M w
    a := a
    b := b
    p := p
    Y_one := ?_
    Y_mono := snakeY_mono_step hT
    Y_last := snakeY_last
    Y_lt := fun i hi => snakeY_lt_two hT hw hi
    Y_blk := ?_
    win := fun i hi r hr => ⟨(hslot i r hi hr).low, (hslot i r hi hr).le,
      (hslot i r hi hr).high⟩
    ctxL := fun i hi r hr => (hslot i r hi hr).ctxL
    ctxR := fun i hi r hr => (hslot i r hi hr).ctxR
    st := fun i hi r hr => ⟨_, _, (hslot i r hi hr).st⟩
    kind := fun i hi r hr => (hslot i r hi (by omega)).kind_cross (Or.inl hr)
    kind_mid := fun i hi =>
      (hslot i (2 * K) (le_of_lt hi) (by omega)).kind_cross (Or.inr hi)
    kind_last := (hslot (rbN M w) (2 * K) (le_refl _) (by omega)).kind_halt rfl rfl
    st_last := ?_
    cut_zero := ?_
    cut_step := ?_
    cut_last := ?_
    ent_zero := ?_
    ext_step := ?_
    ext_pair := ?_
    wcond := fun i hi r hr => (hslot i r hi hr).wcond }⟩
  · -- the `0`-th block is empty
    have h := snakeY_succ_of_le (M := M) (w := w) (m := 0) (Nat.zero_le _)
    simpa using h
  · -- the blocks in the middle are nonempty
    intro m h1 h2
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [snakeY_succ_of_le (by omega : n ≤ rbN M w),
      snakeY_succ_of_le (by omega : n + 1 ≤ rbN M w)]
    exact rbCol_lt_succ (by omega)
  · -- the last piece does not change the state
    have h := (hslot (rbN M w) (2 * K) (le_refl _) (by omega)).st
    rw [entOf_eq h, extOf_eq h, hstN, henN]
  · -- the first piece of a pair starts at the boundary between its two blocks
    intro i hi
    rw [(hslot i 0 hi (by omega)).st_cut, pcStart_zero hKpos, pos_rbFirst,
      snakeY_succ_of_le hi]
  · -- consecutive pieces of a pair meet at a common cut
    intro i hi r hr
    rw [(hslot i r hi (by omega)).en_cut (Or.inl hr),
      (hslot i (r + 1) hi (by omega)).st_cut, pcEnd_succ hT hwidth hr]
  · -- the last piece of a pair ends at the right end of the pair
    intro i hi
    rw [(hslot i (2 * K) (le_of_lt hi) (by omega)).en_cut (Or.inr hi), pcEnd, if_pos rfl,
      if_pos hi, pos_rbFirst, show i + 2 = (i + 1) + 1 from rfl,
      snakeY_succ_of_le (by omega : i + 1 ≤ rbN M w)]
  · -- the first piece starts in the initial state
    rw [entOf_eq (hslot 0 0 (Nat.zero_le _) (by omega)).st, pcStart_zero hKpos,
      rbFirst_zero, qAt_zero]
  · -- consecutive pieces of a pair meet in a common state
    intro i hi r hr
    rw [extOf_eq (hslot i r hi (by omega)).st, entOf_eq (hslot i (r + 1) hi (by omega)).st,
      pcEnd_succ hT hwidth hr]
  · -- the last piece of a pair and the first piece of the next one meet
    intro i hi
    rw [extOf_eq (hslot i (2 * K) (le_of_lt hi) (by omega)).st,
      entOf_eq (hslot (i + 1) 0 hi (by omega)).st, pcEnd_pair hKpos hi]

end Chk

end TwoWay

end Lax916827Proofs.Transducers
