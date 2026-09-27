import Lax235315Proofs.Construction.LinkedSource
import Mathlib.Tactic

/-! Bridge the log-indexed restoration arrays to the vertex-indexed linked
reconstruction relation. -/

namespace Lax235315Proofs.Construction.LinkedSource

open Lax235315Proofs.Construction.LinkedReconstruction
open Lax235315Proofs.Construction.ConcreteReconstruction

/-- The vertices stored in a contiguous interval of the removal log, in their
source order. -/
def logSlice (removed : ℕ → ℕ) (start count : ℕ) : List ℕ :=
  (List.range count).map (fun i => removed (start + i))

/-- Replaying linked writes over an appended list first replays the left
portion, then the right portion. -/
lemma writeRestored_append (representative : ℕ → ℕ) (next : ℕ → ℕ)
    (xs ys : List ℕ) :
    writeRestored representative next (xs ++ ys) =
      writeRestored representative (writeRestored representative next xs) ys := by
  induction xs generalizing next with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, writeRestored]
      exact ih (writeAfter next (representative x) x)

/-- The source prefix fold is exactly the linked pointer replay on the
corresponding ordered slice of the log. `representative` is indexed by vertex,
whereas `repAt` is indexed by log position. -/
lemma writeLogPrefix_eq_writeRestored_logSlice
    (repAt representative removed : ℕ → ℕ) (start count : ℕ)
    (next : ℕ → ℕ)
    (hrep : ∀ i < count,
      representative (removed (start + i)) = repAt (start + i)) :
    writeLogPrefix repAt removed start count next =
      writeRestored representative next (logSlice removed start count) := by
  induction count generalizing next with
  | zero => rfl
  | succ count ih =>
      rw [writeLogPrefix_succ]
      change _ = writeRestored representative next
        ((List.range (count + 1)).map (fun i => removed (start + i)))
      rw [show List.range (count + 1) = List.range count ++ [count] by
        simp [List.range_succ]]
      rw [List.map_append, writeRestored_append]
      simp only [List.map_singleton]
      rw [ih next (by
        intro i hi
        exact hrep i (by omega))]
      rw [← hrep count (by omega)]
      rfl

/-- The log-indexed pointer state after a restored slice represents exactly the
list produced by `ConcreteReconstruction.restoreAfter`. -/
lemma Represents.writeLogPrefix_restoreAfter
    {repAt representative removed : ℕ → ℕ} {start count : ℕ}
    {head : ℕ} {next : ℕ → ℕ} {current : List ℕ}
    (hcurrent : Represents head next current)
    (hremoved : (logSlice removed start count).Nodup)
    (hfresh : ∀ x ∈ logSlice removed start count, x ∉ current)
    (hreps : ∀ x ∈ logSlice removed start count, representative x ∈ current)
    (hrep : ∀ i < count,
      representative (removed (start + i)) = repAt (start + i)) :
    Represents head (writeLogPrefix repAt removed start count next)
      (restoreAfter representative current (logSlice removed start count)) := by
  rw [writeLogPrefix_eq_writeRestored_logSlice repAt representative removed
    start count next hrep]
  exact Represents.writeRestored_restoreAfter hcurrent hremoved hfresh hreps

end Lax235315Proofs.Construction.LinkedSource
