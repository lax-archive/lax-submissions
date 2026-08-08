import Lax3Proofs.Refine.ScatterBlock
import Lax3Proofs.Refine.BfsBlockMask

/-!
# The scatter pass's arena, at the mask's support

`Refine/BfsBlockMask.lean` narrows the block search's distance contract
from the whole array to the mask's support. This file lifts that seam to
the arena the active-set pass carries, which is where the atom's
`fillCom "dist" (r + 1)` is actually forced.

`ScatterBlock.ArenaA`'s seventh clause is

    σ.arrs "dist" = arrOf n (fun _ => r + 1),

and it is the only reason `RamDriver.scatDeadCom` pays `11 n + 6` per
atom. `ArenaAM` is that clause replaced by `BfsBlockMask.DistClean` and
nothing else moved — same six other clauses, same names, same lengths.
`ArenaAtM` is the same at a caller-named mask array, and
`arenaAM_renEnv` is the transport, so the successor's `renCom` route
(`ScatterBlock.scatBlockComA`, the `maskSwap` rename) crosses the
narrowing unchanged: `"dist"` is `MaskFree`, so the swap fixes it and the
narrowed clause rides through untouched.

### Additions only

`ArenaA` and `ArenaAt` are **not** edited. Narrowing a precondition makes
a `Spec` stronger, so a narrowed arena still serves every landed
consumer — but each consumer's proof needs the bridge, and those proofs
live in files frozen this wave. So the narrowed forms sit beside the
landed ones and `arenaAM_of_arenaA` / `arenaAtM_of_arenaAt` are the
compiled bridges the successor points at.

### What is still open

The pass-level spec at the narrowed arena — `scatBlock_specW` /
`scatBlock_specA` with `ArenaAM` in place of `ArenaA` — needs
`ScatterBlock.step_run` re-walked at `BfsBlockMask.bfsBlockM_specW`, and
`step_run` re-derives the arena's distance clause after the mark
(`ScatterBlock.lean:304`) by framing `markBall` over the search's
clean-out. That framing is where the narrowed clause has to be carried
across `markBall`'s writes, and it is the next leaf, not this one.
`bfs_pre_of_arenaAM` below is the piece of it this file can settle: the
arena's narrowed clause *is* the engine's narrowed entry clause, the same
proposition and not a matching pair, so the boundary between pass and
engine costs nothing to cross in either direction.
-/

namespace Lax3Proofs.Refine.ScatterBlockMask

open Lax3.ColoredGraphs
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs
open Lax3Proofs.Refine.BfsBlockMask Lax3Proofs.Refine.ScatterBlock

variable {n ns nt mm r : ℕ} {O T M Mem : ℕ → ℕ}

/-! ### §1 The arena, narrowed -/

/-- **The active pass's arena, at the mask's support.**
`ScatterBlock.ArenaA` with its seventh clause narrowed and the other six
untouched. The member array keeps the carrier's physical length (rebase
F-2's length seam) and the distance array keeps it too — what narrows is
what the arena *claims* about the distance array's content, not how long
it is. -/
def ArenaAM (n nt mm r : ℕ) (O T M Mem : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "mm" = mm ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
    σ.arrs "alv" = arrOf n M ∧ σ.arrs "mem" = arrOf n Mem ∧
    DistClean n r M σ ∧
    (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g)

/-- The same at a caller-named mask array. -/
def ArenaAtM (av : String) (n nt mm r : ℕ) (O T M Mem : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "mm" = mm ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
    σ.arrs av = arrOf n M ∧ σ.arrs "mem" = arrOf n Mem ∧
    DistClean n r M σ ∧
    (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g)

/-- **The bridge.** The landed arena is an instance of the narrowed one,
so every landed caller — including the atom that still runs
`fillCom "dist" (r + 1)` — is served by the narrowed form unchanged.
This is the theorem the successor wave points `RamDriver.scatDeadCom` at
when it swaps the fill for `ScatterDeadPass.distMemCom`. -/
theorem arenaAM_of_arenaA {σ : Env} (h : ArenaA n nt mm r O T M Mem σ) :
    ArenaAM n nt mm r O T M Mem σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    distClean_of_arrOf h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- And the same at a named mask array. -/
theorem arenaAtM_of_arenaAt {av : String} {σ : Env}
    (h : ArenaAt av n nt mm r O T M Mem σ) : ArenaAtM av n nt mm r O T M Mem σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    distClean_of_arrOf h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- The named arena at the engine's own mask name is the plain one. -/
theorem arenaAtM_alv {σ : Env} : ArenaAtM "alv" n nt mm r O T M Mem σ ↔
    ArenaAM n nt mm r O T M Mem σ := Iff.rfl

/-! ### §2 The narrowed clause crosses the mask rename

`"dist"` is one of the seven names `MaskFree` holds off, so `maskSwap av`
fixes it and the narrowed clause is transported by the same one-line
`simp only` that carries the landed one. Nothing about the successor's
`renCom` route is blocked by the narrowing. -/

/-- The narrowed distance clause is invariant under the mask rename. -/
theorem distClean_renEnv {av : String} (hav : MaskFree av) {σ : Env} :
    DistClean n r M (renEnv (maskSwap av) σ) ↔
      DistClean n r M σ := by
  simp only [DistClean, renEnv_arrs,
    maskSwap_of_ne (by decide : ("dist" : String) ≠ "alv")
      (Ne.symm hav.2.2.2.1)]

/-- **The transport**, at the narrowed arena. The landed
`ScatterBlock.arenaA_renEnv` with the seventh clause swapped, and the
proof is the same `simp only`. -/
theorem arenaAM_renEnv {av : String} (hav : MaskFree av) {σ : Env} :
    ArenaAM n nt mm r O T M Mem (renEnv (maskSwap av) σ) ↔
      ArenaAtM av n nt mm r O T M Mem σ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := hav
  simp only [ArenaAM, ArenaAtM, DistClean, renEnv_vars,
    renEnv_arrs, maskSwap_alv,
    maskSwap_of_ne (by decide : ("off" : String) ≠ "alv") (Ne.symm h₁),
    maskSwap_of_ne (by decide : ("tgt" : String) ≠ "alv") (Ne.symm h₂),
    maskSwap_of_ne (by decide : ("mem" : String) ≠ "alv") (Ne.symm h₃),
    maskSwap_of_ne (by decide : ("dist" : String) ≠ "alv") (Ne.symm h₄),
    maskSwap_of_ne (by decide : ("q" : String) ≠ "alv") (Ne.symm h₅),
    maskSwap_of_ne (by decide : ("qd" : String) ≠ "alv") (Ne.symm h₆)]

/-! ### §3 The seam to the engine is an identity

The narrowed arena's distance clause and the narrowed engine's entry and
exit clauses are the **same proposition**, `DistClean n r M`. So the
pass hands its arena straight to `BfsBlockMask.bfsBlockM_specW` and takes
the clean-out straight back, with nothing to re-derive at the boundary —
which is what makes atoms chain. -/

/-- The arena supplies the engine's narrowed entry clause, on the nose. -/
theorem bfs_pre_of_arenaAM {σ : Env} (h : ArenaAM n nt mm r O T M Mem σ) :
    DistClean n r M σ := h.2.2.2.2.2.2.1

/-- And the engine's narrowed exit clause rebuilds the arena, given back
the six clauses the search does not touch. This is the shape `step_run`
will consume when the pass is re-walked: no distance re-derivation at the
boundary, only the frame. -/
theorem arenaAM_of_bfs_post {σ : Env} (hcl : DistClean n r M σ)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf nt T)
    (halv : σ.arrs "alv" = arrOf n M) (hmem : σ.arrs "mem" = arrOf n Mem)
    (hq : ∃ g, σ.arrs "q" = arrOf n g) (hqd : ∃ g, σ.arrs "qd" = arrOf n g) :
    ArenaAM n nt mm r O T M Mem σ :=
  ⟨hn, hmm, hoff, htgt, halv, hmem, hcl, hq, hqd⟩

/-! ### §4 The narrowing is strict, compiled

Two vertices are enough: one alive holding the sentinel, one dead holding
junk. The narrowed clause holds and the landed one does not, so `ArenaAM`
is genuinely weaker than `ArenaA` and the fill really is doing work no
consumer asks for. -/

/-- One alive vertex and one dead one. -/
private def m2 : ℕ → ℕ := fun z => if z = 0 then 1 else 0

/-- The sentinel at the live cell, junk at the dead one. -/
private def d2 : ℕ → ℕ := fun z => if z = 0 then 1 else 7

/-- **`ArenaAM`'s clause holds where `ArenaA`'s fails.** A member-driven
fill establishes the left conjunct and never touches the cell that
refutes the right one. -/
theorem arena_clean_not_literal :
    CleanOn 2 0 m2 d2 ∧ arrOf 2 d2 ≠ arrOf 2 (fun _ => 0 + 1) := by
  refine ⟨fun z hz hm => ?_, fun h => ?_⟩
  · have hz0 : z = 0 := by by_contra hne; simp [m2, hne] at hm
    rw [hz0]; simp [d2]
  · have e₀ := getD_arrOf d2 (show (1 : ℕ) < 2 by omega)
    have e₁ := getD_arrOf (fun _ : ℕ => 0 + 1) (show (1 : ℕ) < 2 by omega)
    rw [h, e₁] at e₀
    simp [d2] at e₀

/-- **So the narrowed arena does not imply the landed one.** Any state
whose distance array is clean on the support without being the literal
list witnesses `ArenaAM` and refutes `ArenaA`'s seventh clause; the
previous theorem exhibits such an array. Stated so that the weakening is
compiled rather than asserted. -/
theorem arenaAM_dist_not_arenaA_dist {σ : Env} {D₀ : ℕ → ℕ}
    (hσ : σ.arrs "dist" = arrOf n D₀) (hclean : CleanOn n r M D₀)
    (hne : arrOf n D₀ ≠ arrOf n (fun _ => r + 1)) :
    DistClean n r M σ ∧ σ.arrs "dist" ≠ arrOf n (fun _ => r + 1) :=
  ⟨⟨D₀, hσ, hclean⟩, by rw [hσ]; exact hne⟩

/-- **The `n = 0` control**, carried to the arena: at the empty carrier
the narrowed clause constrains no cell, and there is still no tail
conjunct anywhere in `ArenaAM`. -/
theorem arenaAM_zero_dist {σ : Env} (h : σ.arrs "dist" = arrOf 0 (fun _ => 0)) :
    DistClean 0 r M σ := distClean_zero h

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.arenaAM_of_arenaA' does not depend on any axioms -/
#guard_msgs in
#print axioms arenaAM_of_arenaA

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.arenaAtM_of_arenaAt' does not depend on any axioms -/
#guard_msgs in
#print axioms arenaAtM_of_arenaAt

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.arenaAM_renEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arenaAM_renEnv

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.distClean_renEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms distClean_renEnv

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.arena_clean_not_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arena_clean_not_literal

end Lax3Proofs.Refine.ScatterBlockMask
