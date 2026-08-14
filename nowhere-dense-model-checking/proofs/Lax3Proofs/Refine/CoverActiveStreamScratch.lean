import Lax3Proofs.Refine.CoverActiveStreamDepth

/-!
# Reusable scratch below a streamed active level

The streamed cover uses carrier-sized arrays, but clears them only on the
row that has just been consumed.  Consequently recursion needs a genuine
resource invariant: every not-yet-entered depth starts clean, and a completed
level returns its own arrays clean before control goes back to its parent.

`StreamScratchFrom j` is the suffix of that invariant.  It deliberately does
not constrain the current level's `alv`/`gam`/colour arrays: those are the
semantic input of level `j`.  Instead its head constrains the arrays reused by
the centre loop at `j` and the semantic arrays that the loop lends to level
`j+1`.  This is exactly the split that remains true while the child is
running.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamScratch

open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- The arrays that one streamed level must receive clean and return clean.
The progressive distance array only needs the word property: the live-member
initializer establishes its semantic cleanliness without touching dead
cells, while every bounded run preserves the word property. -/
structure StreamScratchHead
    (B n cap mb j : ℕ) (σ : Env) : Prop where
  mask_zero : σ.arrs (cpsName j) = arrOf n (fun _ => 0)
  dist_words : ∀ v ∈ σ.arrs (pdsName j), v < B
  cluster_zero : σ.arrs (cluName j) = arrOf n (fun _ => 0)
  retained_zero : σ.arrs (resName j) = arrOf n (fun _ => 0)
  batch_zero : σ.arrs (batName j) = arrOf n (fun _ => 0)
  child_zero : σ.arrs (alvName (j + 1)) = arrOf n (fun _ => 0)
  game_zero : σ.arrs (gamName (j + 1)) = arrOf n (fun _ => 0)
  colours_zero : ∀ s, s < sigL cap mb (j + 1) →
    σ.arrs (colName (j + 1) s) = arrOf n (fun _ => 0)

/-- Clean reusable storage at every executable depth at or below `j` in the
recursive call tree.  The upper bound makes the base depth vacuous. -/
def StreamScratchFrom
    (B n cap mb ell j : ℕ) (σ : Env) : Prop :=
  ∀ d, j ≤ d → d < ell → StreamScratchHead B n cap mb d σ

theorem StreamScratchFrom.head
    {B n cap mb ell j : ℕ} {σ : Env}
    (h : StreamScratchFrom B n cap mb ell j σ) (hj : j < ell) :
    StreamScratchHead B n cap mb j σ :=
  h j le_rfl hj

theorem StreamScratchFrom.tail
    {B n cap mb ell j : ℕ} {σ : Env}
    (h : StreamScratchFrom B n cap mb ell j σ) :
    StreamScratchFrom B n cap mb ell (j + 1) σ :=
  fun d hd hde => h d (by omega) hde

theorem StreamScratchFrom.of_head_tail
    {B n cap mb ell j : ℕ} {σ : Env}
    (hh : StreamScratchHead B n cap mb j σ)
    (ht : StreamScratchFrom B n cap mb ell (j + 1) σ) :
    StreamScratchFrom B n cap mb ell j σ := by
  intro d hjd hdell
  rcases eq_or_lt_of_le hjd with rfl | hjd'
  · exact hh
  · exact ht d (by omega) hdell

/-- Transport one clean head across an array-extensional state change. -/
theorem StreamScratchHead.congr
    {B n cap mb j : ℕ} {σ σ' : Env}
    (h : StreamScratchHead B n cap mb j σ)
    (ha : ∀ a, σ'.arrs a = σ.arrs a) :
    StreamScratchHead B n cap mb j σ' := by
  refine {
    mask_zero := (ha _).trans h.mask_zero
    dist_words := ?_
    cluster_zero := (ha _).trans h.cluster_zero
    retained_zero := (ha _).trans h.retained_zero
    batch_zero := (ha _).trans h.batch_zero
    child_zero := (ha _).trans h.child_zero
    game_zero := (ha _).trans h.game_zero
    colours_zero := fun s hs => (ha _).trans (h.colours_zero s hs) }
  intro v hv
  exact h.dist_words v (by rwa [← ha _])

/-- Transport a clean suffix across an array-extensional state change. -/
theorem StreamScratchFrom.congr
    {B n cap mb ell j : ℕ} {σ σ' : Env}
    (h : StreamScratchFrom B n cap mb ell j σ)
    (ha : ∀ a, σ'.arrs a = σ.arrs a) :
    StreamScratchFrom B n cap mb ell j σ' :=
  fun d hjd hd => (h d hjd hd).congr ha

/-- A convenient frame principle for a clean suffix.  Exact zeros are
transported by ordinary run frames; the distance word property is stronger:
it survives even if the command writes the distance array. -/
theorem StreamScratchFrom.run
    {B n cap mb ell j K : ℕ} {cmd : Com} {σ σ' : Env}
    (h : StreamScratchFrom B n cap mb ell j σ)
    (hr : Run B cmd σ σ' K)
    (hcps : ∀ d, j ≤ d → d < ell → cpsName d ∉ cmd.warrs)
    (hclu : ∀ d, j ≤ d → d < ell → cluName d ∉ cmd.warrs)
    (hres : ∀ d, j ≤ d → d < ell → resName d ∉ cmd.warrs)
    (hbat : ∀ d, j ≤ d → d < ell → batName d ∉ cmd.warrs)
    (halv : ∀ d, j ≤ d → d < ell → alvName (d + 1) ∉ cmd.warrs)
    (hgam : ∀ d, j ≤ d → d < ell → gamName (d + 1) ∉ cmd.warrs)
    (hcol : ∀ d, j ≤ d → d < ell → ∀ s, s < sigL cap mb (d + 1) →
      colName (d + 1) s ∉ cmd.warrs) :
    StreamScratchFrom B n cap mb ell j σ' := by
  intro d hjd hdell
  have hh := h d hjd hdell
  refine {
    mask_zero := (hr.frame_arr _ (hcps d hjd hdell)).trans hh.mask_zero
    dist_words := run_mem_arrs_lt hr _ hh.dist_words
    cluster_zero := (hr.frame_arr _ (hclu d hjd hdell)).trans hh.cluster_zero
    retained_zero := (hr.frame_arr _ (hres d hjd hdell)).trans hh.retained_zero
    batch_zero := (hr.frame_arr _ (hbat d hjd hdell)).trans hh.batch_zero
    child_zero := (hr.frame_arr _ (halv d hjd hdell)).trans hh.child_zero
    game_zero := (hr.frame_arr _ (hgam d hjd hdell)).trans hh.game_zero
    colours_zero := fun s hs =>
      (hr.frame_arr _ (hcol d hjd hdell s hs)).trans (hh.colours_zero s hs) }

end Lax3Proofs.Refine.CoverActiveStreamScratch
