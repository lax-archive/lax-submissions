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
so every landed caller is served by the narrowed form unchanged. Wave
B4-walk-2m-3 no longer needs it at the *atom* — `ScatterDeadTurn`
builds `ArenaAtM` directly out of `distClean_of_cover` — and it is what
keeps every other consumer of `ArenaAt` working against the narrowed
passes. -/
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

/-! ### §5 The pass, re-walked at the narrowed arena

**This section closes the header's "What is still open".** §1–§4 settled
the arena and named the pass-level spec as the next leaf; what follows is
`ScatterBlock`'s pass carried across it — the turn (`stepM_run`), the
scan (`loopM_spec`) and the three exports. The landed walks are copied
and **exactly the distance lines move**; every other line, every cost
numeral and every `flag` clause is the landed one.

**Why so little moves.** The narrowed clause names one array, so it is a
frame wherever that array is not written, and the two walks of the pass
do not write it: `ScatterBlock.notMem_markBall_warrs` and
`notMem_clearMem_warrs` both list `"dist"`. All the distance reasoning of
a pick therefore happens inside `BfsBlockMask.bfsBlockM_specW`, whose
entry and exit clause is the arena's clause **on the nose**
(`bfs_pre_of_arenaAM`, `arenaAM_of_bfs_post`). So the re-walk carries
`DistClean` and never re-derives it.

**What is added at the exit.** The landed `scatBlock_specW` states only
the two `flag` clauses, so a caller cannot see that the distance array
comes back at all. `scatBlockM_specW` states `DistClean n r M σ'` as a
third clause — §9's `post_flag_gives_no_distClean` is the compiled reason
it has to be stated rather than recovered: the `flag` clauses constrain
no array. Without it a successor atom could not re-establish the arena
for the next atom, which is the entire point of deleting the fill. -/

open Lax3.ScatterSentences Lax3Proofs.RamScatter

variable {t : ℕ} {G : SimpleGraph (Fin n)} {X : Set (Fin n)}

/-- The narrowed clause names one array, so anything that leaves that
array alone carries it. This is the only lemma the re-walk needs beyond
what §1–§3 already compiled. -/
theorem distClean_of_arrs_eq {σ σ' : Env} (h : DistClean n r M σ)
    (he : σ'.arrs "dist" = σ.arrs "dist") : DistClean n r M σ' := by
  obtain ⟨D₀, hD, hc⟩ := h
  exact ⟨D₀, he.trans hD, hc⟩

/-- `ScatterBlock.ArenaA.of_eq` at the narrowed arena: the seventh clause
now travels by `distClean_of_arrs_eq` instead of by `rw`, and the other
eight lines are the landed ones. -/
theorem ArenaAM.of_eq {σ σ' : Env} (h : ArenaAM n nt mm r O T M Mem σ)
    (hv : σ'.vars "n" = σ.vars "n") (hv₂ : σ'.vars "mm" = σ.vars "mm")
    (h₁ : σ'.arrs "off" = σ.arrs "off") (h₂ : σ'.arrs "tgt" = σ.arrs "tgt")
    (h₃ : σ'.arrs "alv" = σ.arrs "alv") (h₄ : σ'.arrs "mem" = σ.arrs "mem")
    (h₅ : σ'.arrs "dist" = σ.arrs "dist") (h₆ : σ'.arrs "q" = σ.arrs "q")
    (h₇ : σ'.arrs "qd" = σ.arrs "qd") : ArenaAM n nt mm r O T M Mem σ' := by
  obtain ⟨e₀, e₀', e₁, e₂, e₃, e₄, e₅, ⟨g₆, e₆⟩, ⟨g₇, e₇⟩⟩ := h
  exact ⟨by rw [hv, e₀], by rw [hv₂, e₀'], by rw [h₁, e₁], by rw [h₂, e₂], by rw [h₃, e₃],
    by rw [h₄, e₄], distClean_of_arrs_eq e₅ h₅, ⟨g₆, by rw [h₆, e₆]⟩, ⟨g₇, by rw [h₇, e₇]⟩⟩

theorem ArenaAM.setVar {σ : Env} {x : String} {v : ℕ} (h : ArenaAM n nt mm r O T M Mem σ)
    (hx : x ≠ "n") (hx₂ : x ≠ "mm") : ArenaAM n nt mm r O T M Mem (σ.setVar x v) :=
  h.of_eq (by simp [Ne.symm hx]) (by simp [Ne.symm hx₂]) rfl rfl rfl rfl rfl rfl rfl

/-! ### §6 One turn of the member scan, at the narrowed arena

`ScatterBlock.step_run` verbatim except for three lines: the arena is
destructured with a `DistClean` in seventh place, the search is
`BfsBlockMask.bfsBlockM_specW` and takes that clause as its entry, and
the clause comes back across `markBall` by the frame. The control flow,
the three cases, the mathematics of the turn (`marked_iff_wd`) and the
cost disjunction `K ≤ 30` / `K ≤ pickBlockK bw nb` are untouched. -/

theorem stepM_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb)
    {σ : Env} (hA : ArenaAM n nt mm r O T M Mem σ) (hsj : σ.vars "sj" < mm)
    (hP : ProgressA G M r t X (Mem (σ.vars "sj")) σ) :
    ∃ σ' K, Run B (scatBlockStep r t) σ σ' K ∧ ArenaAM n nt mm r O T M Mem σ' ∧
      σ'.vars "sj" = σ.vars "sj" + 1 ∧
      ProgressA G M r t X (Mem (σ.vars "sj") + 1) σ' ∧
      ((σ'.vars "cnt" = σ.vars "cnt" ∧ K ≤ 30) ∨
        (σ'.vars "cnt" = σ.vars "cnt" + 1 ∧ σ.vars "cnt" < t ∧ K ≤ pickBlockK bw nb)) := by
  obtain ⟨hn, hmmv, hoff, htgt, halv, hmem, hdist, hqex, hqdex⟩ := id hA
  have hmmn : mm ≤ n := hml.card_le
  have hsn : Mem (σ.vars "sj") < n := hml.lt _ hsj
  have hsjB : σ.vars "sj" < B := by omega
  have hsB : Mem (σ.vars "sj") < B := by omega
  have hcntt : σ.vars "cnt" ≤ t := hP.cnt_le
  have hcntB : σ.vars "cnt" < B := by omega
  set s := Mem (σ.vars "sj") with hs_def
  -- the read that opens every turn
  have hread : (Expr.get "mem" (.var "sj")).evalB B σ = some s := by
    refine evalB_get (evalB_var (by rw [hmmv] at *; omega)) ?_ hsB
    -- the read is in range because the live prefix is inside the physical array
    rw [hmem, getElem?_arrOf Mem (show σ.vars "sj" < n by omega)]
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ = σ.setVar "mv" s := ⟨_, rfl⟩
  have run₀ : Run B (.assign "mv" (.get "mem" (.var "sj"))) σ τ₀ 3 := by
    rw [hτ₀]; exact (Run.assign (v := s) hread).mono (by simp [Expr.size])
  have hv₀ : ∀ y, y ≠ "mv" → τ₀.vars y = σ.vars y := by
    intro y hy; rw [hτ₀]; simp [hy]
  have ha₀ : τ₀.arrs = σ.arrs := by rw [hτ₀]; simp
  have hmv₀ : τ₀.vars "mv" = s := by rw [hτ₀]; simp
  have hA₀ : ArenaAM n nt mm r O T M Mem τ₀ := by
    rw [hτ₀]; exact hA.setVar (by decide) (by decide)
  have hP₀ : ProgressA G M r t X s τ₀ :=
    hP.of_eq (hv₀ "cnt" (by decide)) (by rw [ha₀])
  have hcnt₀ : τ₀.vars "cnt" = σ.vars "cnt" := hv₀ "cnt" (by decide)
  -- the assignment that ends every turn
  have hbump : ∀ τ : Env, τ.vars "sj" = σ.vars "sj" →
      Run B (.assign "sj" (.add (.var "sj") (.lit 1))) τ
        (τ.setVar "sj" (σ.vars "sj" + 1)) 4 := by
    intro τ hτ
    refine (Run.assign (v := σ.vars "sj" + 1) ?_).mono (by simp [Expr.size])
    rw [← hτ]
    exact evalB_bin (evalB_var (by rw [hτ]; omega)) (evalB_lit (by omega)) (by simp; omega)
  have hsj₀ : τ₀.vars "sj" = σ.vars "sj" := hv₀ "sj" (by decide)
  -- a turn that leaves the machine alone
  have hnopick : ∀ K₁, Run B (scatBlockBody r t) τ₀ τ₀ K₁ → K₁ ≤ 22 →
      ¬ GSel G M r X s →
      ∃ σ' K, Run B (scatBlockStep r t) σ σ' K ∧ ArenaAM n nt mm r O T M Mem σ' ∧
        σ'.vars "sj" = σ.vars "sj" + 1 ∧ ProgressA G M r t X (s + 1) σ' ∧
        ((σ'.vars "cnt" = σ.vars "cnt" ∧ K ≤ 30) ∨
          (σ'.vars "cnt" = σ.vars "cnt" + 1 ∧ σ.vars "cnt" < t ∧ K ≤ pickBlockK bw nb)) := by
    intro K₁ hrun hK hg
    refine ⟨τ₀.setVar "sj" (σ.vars "sj" + 1), 3 + (K₁ + 4),
      run₀.seq (hrun.seq (hbump τ₀ hsj₀)),
      hA₀.setVar (by decide) (by decide), by simp, ?_, Or.inl ⟨by simp [hcnt₀], by omega⟩⟩
    exact (progressA_succ_of_not hg hP₀).of_eq (by simp) rfl
  by_cases hlt : σ.vars "cnt" < t
  · -- there is still room, so the exclusion test is asked
    have hc₀ : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₀ = some true := by
      rw [evalB_condLt (evalB_var (by rw [hcnt₀]; omega)) (evalB_lit htB)]
      simp [hcnt₀, hlt]
    obtain ⟨-, hcnteq, E, hexc, hE1, hEiff⟩ :
        τ₀.vars "cnt" < t ∧ τ₀.vars "cnt" = (selBelow G M r X s).ncard ∧
          ∃ E, τ₀.arrs "exc" = arrOf n E ∧ (∀ w, MemOf X w → E w ≤ 1) ∧
            ∀ w, MemOf X w → (E w = 0 ↔ ∀ u < s, GSel G M r X u → ¬ WD G M r u w) := by
      rcases hP₀ with ⟨h, -⟩ | h
      · omega
      · exact h
    have hmemS : MemOf X s := hml.sound _ hsj
    have hE1s : E s ≤ 1 := hE1 _ hmemS
    have hexcv : (Expr.get "exc" (.var "mv")).evalB B τ₀ = some (E s) :=
      evalB_get (evalB_var (by rw [hmv₀]; omega))
        (by rw [hexc, hmv₀, getElem?_arrOf E hsn]) (by omega)
    by_cases hE0 : E s = 0
    · -- **the member is selected**
      have hgsel : GSel G M r X s :=
        (gsel_iff hsn).2 ⟨hmemS.2, (hEiff _ hmemS).1 hE0⟩
      have hc₁ : (Cond.eq (.get "exc" (.var "mv")) (.lit 0)).evalB B τ₀ = some true := by
        rw [evalB_condEq hexcv (evalB_lit (by omega))]; simp [hE0]
      -- count it
      obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = τ₀.setVar "cnt" (σ.vars "cnt" + 1) := ⟨_, rfl⟩
      have run₁ : Run B (.assign "cnt" (.add (.var "cnt") (.lit 1))) τ₀ τ₁ 4 := by
        rw [hτ₁, ← hcnt₀]
        exact (Run.assign (v := τ₀.vars "cnt" + 1)
          (evalB_bin (evalB_var (by rw [hcnt₀]; omega)) (evalB_lit (by omega))
            (by simp; omega))).mono (by simp [Expr.size])
      have hv₁ : ∀ y, y ≠ "cnt" → τ₁.vars y = τ₀.vars y := by
        intro y hy; rw [hτ₁]; simp [hy]
      have ha₁ : τ₁.arrs = τ₀.arrs := by rw [hτ₁]; simp
      have hcnt₁ : τ₁.vars "cnt" = σ.vars "cnt" + 1 := by rw [hτ₁]; simp
      -- name the source
      obtain ⟨τ₂, hτ₂⟩ : ∃ τ, τ = τ₁.setVar "src" s := ⟨_, rfl⟩
      have run₂ : Run B (.assign "src" (.var "mv")) τ₁ τ₂ 2 := by
        rw [hτ₂]
        refine (Run.assign (v := s) ?_).mono (by simp [Expr.size])
        rw [← hmv₀, ← hv₁ "mv" (by decide)]
        exact evalB_var (by rw [hv₁ "mv" (by decide), hmv₀]; omega)
      have hv₂ : ∀ y, y ≠ "src" → τ₂.vars y = τ₁.vars y := by
        intro y hy; rw [hτ₂]; simp [hy]
      have ha₂ : τ₂.arrs = τ₁.arrs := by rw [hτ₂]; simp
      have hsrc₂ : τ₂.vars "src" = s := by rw [hτ₂]; simp
      -- the ball this pick is charged to
      obtain ⟨Aset, hAset, hbwA, hnbA⟩ := hbud s hsn
      -- search from it, at the narrowed contract: the arena's clause **is**
      -- the engine's entry clause, so this line is a frame and not a proof
      obtain ⟨g₆, hq₂⟩ := hqex
      obtain ⟨g₇, hqd₂⟩ := hqdex
      obtain ⟨τ₃, run₃, hdist₃, Q, QD, hq₃, hqd₃, htln, htlnb, hqn, hseg, hqinj, -⟩ :=
        (bfsBlockM_specW (G := G) (M := M) (O := O) (T := T) (ns := ns) (nt := nt)
          (d := r) (s := s) hcsr hsn hnB hnsB hnt hrB hMB hAset hbwA hnbA).run (σ := τ₂)
          ⟨by rw [hv₂ "n" (by decide), hv₁ "n" (by decide), hv₀ "n" (by decide), hn],
            hsrc₂,
            by rw [ha₂, ha₁, ha₀]; exact hoff, by rw [ha₂, ha₁, ha₀]; exact htgt,
            by rw [ha₂, ha₁, ha₀]; exact halv,
            distClean_of_arrs_eq hdist (by rw [ha₂, ha₁, ha₀]),
            ⟨g₆, by rw [ha₂, ha₁, ha₀]; exact hq₂⟩, ⟨g₇, by rw [ha₂, ha₁, ha₀]; exact hqd₂⟩⟩
      -- and mark its ball
      have hn₃ : τ₃.vars "n" = n := by
        rw [run₃.frame_var "n" (notMem_bfsBlock_wvars r "n" (by simp)),
          hv₂ "n" (by decide), hv₁ "n" (by decide), hv₀ "n" (by decide), hn]
      have hsrc₃ : τ₃.vars "src" = s := by
        rw [run₃.frame_var "src" (notMem_bfsBlock_wvars r "src" (by simp)), hsrc₂]
      have hexc₃ : τ₃.arrs "exc" = arrOf n E := by
        rw [run₃.frame_arr "exc" (notMem_bfsBlock_warrs r "exc" (by simp)),
          ha₂, ha₁]; exact hexc
      obtain ⟨τ₄, K₄, run₄, hK₄, hq₄, E', hexc₄, hmark, hkeep⟩ :=
        markBall_run (n := n) (B := B) (tf := τ₃.vars "tail") (s := s) (Q := Q) (E := E)
          hnB hsn htln (fun i hi => lt_trans (hqn i hi) hnB) hn₃ hsrc₃ rfl hq₃ hexc₃
      -- what the two phases left
      have hsj₄ : τ₄.vars "sj" = σ.vars "sj" := by
        rw [run₄.frame_var "sj" (notMem_markBall_wvars "sj" (by simp)),
          run₃.frame_var "sj" (notMem_bfsBlock_wvars r "sj" (by simp)),
          hv₂ "sj" (by decide), hv₁ "sj" (by decide), hsj₀]
      have hcnt₄ : τ₄.vars "cnt" = σ.vars "cnt" + 1 := by
        rw [run₄.frame_var "cnt" (notMem_markBall_wvars "cnt" (by simp)),
          run₃.frame_var "cnt" (notMem_bfsBlock_wvars r "cnt" (by simp)),
          hv₂ "cnt" (by decide), hcnt₁]
      have harr₄ : ∀ a, a ∈ ["off", "tgt", "alv", "mem"] → τ₄.arrs a = σ.arrs a := by
        intro a ha
        rw [run₄.frame_arr a (notMem_markBall_warrs a (by fin_cases ha <;> simp)),
          run₃.frame_arr a (notMem_bfsBlock_warrs r a (by fin_cases ha <;> simp)),
          ha₂, ha₁, ha₀]
      -- **the one line the narrowing moves**: the mark does not write
      -- `"dist"`, so the search's clean-out is the arena's clause again
      have hdist₄ : DistClean n r M τ₄ :=
        distClean_of_arrs_eq hdist₃
          (run₄.frame_arr "dist" (notMem_markBall_warrs "dist" (by simp)))
      have hqd₄ : τ₄.arrs "qd" = arrOf n QD := by
        rw [run₄.frame_arr "qd" (notMem_markBall_warrs "qd" (by simp))]; exact hqd₃
      have hA₄ : ArenaAM n nt mm r O T M Mem τ₄ := by
        refine ⟨?_, ?_, by rw [harr₄ "off" (by simp)]; exact hoff,
          by rw [harr₄ "tgt" (by simp)]; exact htgt,
          by rw [harr₄ "alv" (by simp)]; exact halv,
          by rw [harr₄ "mem" (by simp)]; exact hmem, hdist₄, ⟨Q, hq₄⟩, ⟨QD, hqd₄⟩⟩
        · rw [run₄.frame_var "n" (notMem_markBall_wvars "n" (by simp)), hn₃]
        · rw [run₄.frame_var "mm" (notMem_markBall_wvars "mm" (by simp)),
            run₃.frame_var "mm" (notMem_bfsBlock_wvars r "mm" (by simp)),
            hv₂ "mm" (by decide), hv₁ "mm" (by decide), hv₀ "mm" (by decide), hmmv]
      -- **the mathematics of the turn**: the marked set is the ball
      have hE'iff : ∀ w, MemOf X w → (E' w = 0 ↔
          ∀ u < s + 1, GSel G M r X u → ¬ WD G M r u w) := by
        intro w hw
        have hwn : w < n := hw.lt
        have hmk := marked_iff_wd (G := G) (M := M) (r := r) hsn hwn hseg (w := w)
        constructor
        · intro h0 u hu hgu
          have hnotmark : ¬ ((∃ i, i < τ₃.vars "tail" ∧ Q i = w) ∨ w = s) := by
            intro hcon
            rw [hmark w hwn hcon] at h0; omega
          have hEw : E w = 0 := by rw [← hkeep w hwn hnotmark]; exact h0
          rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
          · exact (hEiff w hw).1 hEw u hu' hgu
          · exact fun hwd => hnotmark (hmk.2 hwd)
        · intro hall
          have hnotwd : ¬ WD G M r s w := fun hwd => hall s (by omega) hgsel hwd
          have hnotmark : ¬ ((∃ i, i < τ₃.vars "tail" ∧ Q i = w) ∨ w = s) :=
            fun hcon => hnotwd (hmk.1 hcon)
          rw [hkeep w hwn hnotmark]
          exact (hEiff w hw).2 (fun u hu hgu => hall u (by omega) hgu)
      have hE'1 : ∀ w, MemOf X w → E' w ≤ 1 := by
        intro w hw
        have hwn : w < n := hw.lt
        by_cases hcon : ((∃ i, i < τ₃.vars "tail" ∧ Q i = w) ∨ w = s)
        · rw [hmark w hwn hcon]
        · rw [hkeep w hwn hcon]; exact hE1 w hw
      have hncard : σ.vars "cnt" + 1 = (selBelow G M r X (s + 1)).ncard := by
        rw [ncard_selBelow_succ_of_gsel hsn hgsel, ← hcnteq, hcnt₀]
      have hlei : σ.vars "cnt" + 1 ≤ (greedySet (masked G M) r X).ncard := by
        rw [hncard]; exact ncard_selBelow_le
      refine ⟨τ₄.setVar "sj" (σ.vars "sj" + 1), _,
        run₀.seq ((Run.ite_true hc₀ (Run.ite_true hc₁
          (run₁.seq (run₂.seq (run₃.seq run₄))))).seq (hbump τ₄ hsj₄)),
        hA₄.setVar (by decide) (by decide), by simp, ?_,
        Or.inr ⟨by simp [hcnt₄], hlt, ?_⟩⟩
      · rcases Nat.lt_or_ge (σ.vars "cnt" + 1) t with hlt' | hge'
        · exact Or.inr ⟨by simp [hcnt₄]; omega, by simp [hcnt₄, ← hncard],
            E', by simp [hexc₄], hE'1, hE'iff⟩
        · exact Or.inl ⟨by simp [hcnt₄]; omega, by omega⟩
      · have hKb : K₄ ≤ markBallK nb :=
          le_trans hK₄ (by simp only [markBallK]; omega)
        simp only [pickBlockK, Cond.size, Expr.size]
        omega
    · -- an earlier pick already excluded it
      have hc₁ : (Cond.eq (.get "exc" (.var "mv")) (.lit 0)).evalB B τ₀ = some false := by
        rw [evalB_condEq hexcv (evalB_lit (by omega))]; simp [hE0]
      refine hnopick _ (Run.ite_true hc₀ (Run.ite_false hc₁ Run.skip)) (by simp [Cond.size,
        Expr.size]) fun hg => hE0 ((hEiff _ hmemS).2 ((gsel_iff hsn).1 hg).2)
  · -- the count has reached the threshold
    have hc₀ : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₀ = some false := by
      rw [evalB_condLt (evalB_var (by rw [hcnt₀]; omega)) (evalB_lit htB)]
      simp [hcnt₀, hlt]
    have hB : τ₀.vars "cnt" = t ∧ t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₀ with h | ⟨h, -⟩
      · exact h
      · omega
    refine ⟨τ₀.setVar "sj" (σ.vars "sj" + 1), _,
      run₀.seq ((Run.ite_false hc₀ Run.skip).seq (hbump τ₀ hsj₀)),
      hA₀.setVar (by decide) (by decide), by simp, ?_,
      Or.inl ⟨by simp [hcnt₀], by simp [Cond.size, Expr.size]⟩⟩
    exact Or.inl ⟨by simp [hB.1], hB.2⟩

/-! ### §7 The scan, at the narrowed arena

The loop rule, the potential and both of its readings are the landed
ones — `ScatterBlock.ScatBlockPot` is reused unchanged, because the
narrowing touches no cost. Only the invariant's arena clause moves. -/

/-- `ScatterBlock.ScatBlockInv` with `ArenaAM` in place of `ArenaA`; the
member bound and the progress clause are verbatim. -/
def ScatBlockInvM (n nt mm r t : ℕ) (G : SimpleGraph (Fin n)) (M O T Mem : ℕ → ℕ)
    (X : Set (Fin n)) (σ : Env) : Prop :=
  ArenaAM n nt mm r O T M Mem σ ∧ σ.vars "sj" ≤ mm ∧
    ProgressA G M r t X (memPos n mm Mem (σ.vars "sj")) σ

theorem loopM_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B (fun σ => ScatBlockInvM n nt mm r t G M O T Mem X (σ.setVar "sj" 0))
      (scatBlockLoop r t)
      (fun _ σ' => ArenaAM n nt mm r O T M Mem σ' ∧ ProgressA G M r t X n σ' ∧
        σ'.vars "sj" = mm)
      (pickBlockK bw nb * t + 40 * mm + 6) := by
  have hmmn : mm ≤ n := hml.card_le
  have hwhile : Spec B (ScatBlockInvM n nt mm r t G M O T Mem X)
      (.while (.lt (.var "sj") (.var "mm")) (scatBlockStep r t))
      (fun _ σ' => ScatBlockInvM n nt mm r t G M O T Mem X σ' ∧
        (Cond.lt (Expr.var "sj") (.var "mm")).evalB B σ' = some false)
      (pickBlockK bw nb * t + 40 * mm + 4) := by
    refine Spec.while_potential _ (ScatBlockPot mm bw nb t) (fun τ hτ => ?_)
      (fun τ hτ hb => ?_) (fun _ h => h) (fun τ hτ => ?_)
    · exact evalB_condLt_vars (by have := hτ.2.1; omega)
        (by rw [hτ.1.2.1]; omega)
    · have hlt : τ.vars "sj" < mm := by
        have := lt_of_condLt_true hb; rw [hτ.1.2.1] at this; exact this
      have hPm : ProgressA G M r t X (Mem (τ.vars "sj")) τ := by
        have := hτ.2.2; rwa [memPos_of_lt hlt] at this
      obtain ⟨τ', K, hrun, hA', hsj', hP', hcase⟩ :=
        stepM_run hcsr hnB hnsB hnt hrB htB hMB hml hbud hτ.1 hlt hPm
      refine ⟨τ', K, hrun, ⟨hA', by omega, ?_⟩, ?_⟩
      · rw [hsj']; exact progressA_step_gap hml hlt hP'
      · have hn1 : mm - τ.vars "sj" = (mm - (τ.vars "sj" + 1)) + 1 := by omega
        simp only [ScatBlockPot, hsj', hn1]
        rcases hcase with ⟨hc, hK⟩ | ⟨hc, hct, hK⟩
        · rw [hc]; simp only [Cond.size, Expr.size]; omega
        · have hn2 : t - τ.vars "cnt" = (t - (τ.vars "cnt" + 1)) + 1 := by omega
          rw [hc, hn2, Nat.mul_succ]
          simp only [Cond.size, Expr.size]
          omega
    · have h₁ : pickBlockK bw nb * (t - τ.vars "cnt") ≤ pickBlockK bw nb * t :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have h₂ : 40 * (mm - τ.vars "sj") ≤ 40 * mm := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      simp only [ScatBlockPot, Cond.size, Expr.size]
      omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ', hrun, hI', hfalse⟩ := hwhile.run (σ := σ.setVar "sj" 0) hσ
  have hsjmm : σ'.vars "sj" = mm := by
    have h₀ := le_of_condLt_false hfalse
    have h₁ := hI'.1.2.1
    have h₂ := hI'.2.1
    omega
  refine ⟨σ', _, Run.seq (Run.assign (v := 0) (evalB_lit (by omega))) hrun,
    by simp [Expr.size]; omega, hI'.1, ?_, hsjmm⟩
  have := hI'.2.2
  rwa [hsjmm, memPos_end hml] at this

/-! ### §8 The pass, at the narrowed arena

The three exports. Precondition `ArenaAM` / `ArenaAtM`, `flag` clauses
verbatim, charge `ScatterBlockCost.scatBlockK mm bw nb t` **unmoved** —
`pickBlockK bw nb`, `clearMemK mm`, `scanMemK mm` and every numeral are
the landed ones, because `bfsBlockM_specW` charges the landed
`bfsBlockK bw nb` and no program text moved.

The third postcondition clause is the clean-out. -/

/-- **The active-set greedy scatter pass, at the mask's support.**
`ScatterBlock.scatBlock_specW` with `ArenaAM` for `ArenaA` and the
clean-out added to the exit.

The `flag` clauses are `RamScatter.scatter_specW`'s, verbatim, and the
charge is `scatBlockK mm bw nb t`, in which **neither `n` nor `ns`
occurs**. What the caller no longer has to establish is the whole-array
fill: only the *live* cells of `dist` need hold the sentinel. -/
theorem scatBlockM_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaAM n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1 ∧ DistClean n r M σ')
      (scatBlockK mm bw nb t) := by
  have hmmn : mm ≤ n := hml.card_le
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hA, g, hexc⟩ := hσ
  obtain ⟨hn, hmmv, hoff, htgt, halv, hmem, hdist, hqex, hqdex⟩ := id hA
  -- the counter
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = σ.setVar "cnt" 0 := ⟨_, rfl⟩
  have run₁ : Run B (.assign "cnt" (.lit 0)) σ τ₁ 2 := by
    rw [hτ₁]; exact (Run.assign (v := 0) (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hv₁ : ∀ y, y ≠ "cnt" → τ₁.vars y = σ.vars y := by
    intro y hy; rw [hτ₁]; simp [hy]
  have ha₁ : τ₁.arrs = σ.arrs := by rw [hτ₁]; simp
  have hcnt₁ : τ₁.vars "cnt" = 0 := by rw [hτ₁]; simp
  have hA₁ : ArenaAM n nt mm r O T M Mem τ₁ := by
    rw [hτ₁]; exact hA.setVar (by decide) (by decide)
  -- the exclusion bits, at the members
  obtain ⟨τ₂, K₂, run₂, hK₂, hmem₂, E, hexc₂, hclear, -⟩ :=
    clearMem_run (n := n) (mm := mm) (B := B) (Mem := Mem) (X := X)
      hnB (by omega) hml (by rw [hv₁ "n" (by decide)]; exact hn)
      (by rw [hv₁ "mm" (by decide)]; exact hmmv)
      (by rw [ha₁]; exact hmem) (by rw [ha₁]; exact hexc)
  have hcnt₂ : τ₂.vars "cnt" = 0 := by
    rw [run₂.frame_var "cnt" (notMem_clearMem_wvars "cnt" (by simp)), hcnt₁]
  have harr₂ : ∀ a, a ∈ ["off", "tgt", "alv", "dist", "q", "qd"] → τ₂.arrs a = σ.arrs a := by
    intro a ha
    rw [run₂.frame_arr a (notMem_clearMem_warrs a (by fin_cases ha <;> simp)), ha₁]
  have hA₂ : ArenaAM n nt mm r O T M Mem τ₂ := by
    obtain ⟨g₆, hq⟩ := hqex
    obtain ⟨g₇, hqd⟩ := hqdex
    refine ⟨?_, ?_, by rw [harr₂ "off" (by simp)]; exact hoff,
      by rw [harr₂ "tgt" (by simp)]; exact htgt,
      by rw [harr₂ "alv" (by simp)]; exact halv, hmem₂,
      distClean_of_arrs_eq hdist (harr₂ "dist" (by simp)),
      ⟨g₆, by rw [harr₂ "q" (by simp)]; exact hq⟩,
      ⟨g₇, by rw [harr₂ "qd" (by simp)]; exact hqd⟩⟩
    · rw [run₂.frame_var "n" (notMem_clearMem_wvars "n" (by simp)),
        hv₁ "n" (by decide), hn]
    · rw [run₂.frame_var "mm" (notMem_clearMem_wvars "mm" (by simp)),
        hv₁ "mm" (by decide), hmmv]
  -- the scan starts with nothing selected and nothing excluded
  have hI₂ : ScatBlockInvM n nt mm r t G M O T Mem X (τ₂.setVar "sj" 0) := by
    refine ⟨hA₂.setVar (by decide) (by decide), by simp, ?_⟩
    refine progressA_start hml ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact Or.inl ⟨by simp [hcnt₂], by omega⟩
    · refine Or.inr ⟨by simp [hcnt₂]; omega, by simp [hcnt₂, selBelow_zero], E,
        by simp [hexc₂], fun w hw => by rw [hclear w hw]; omega,
        fun w hw => by rw [hclear w hw]; simp⟩
  obtain ⟨τ₃, run₃, hA₃, hP₃, hsj₃⟩ :=
    (loopM_spec hcsr hnB hnsB hnt hrB htB hMB hml hbud).run (σ := τ₂) hI₂
  -- the clean-out the successor needs: the arena comes back
  have hcl₃ : DistClean n r M τ₃ := bfs_pre_of_arenaAM hA₃
  -- the answer
  have hcntt : τ₃.vars "cnt" ≤ t := hP₃.cnt_le
  have hcntB : τ₃.vars "cnt" < B := by omega
  have hcv : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₃
      = some (decide (τ₃.vars "cnt" < t)) := evalB_condLt (evalB_var hcntB) (evalB_lit htB)
  by_cases hlt : τ₃.vars "cnt" < t
  · have hns : ¬ t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨h, -⟩ | ⟨-, h, -⟩
      · omega
      · rw [selBelow_all] at h; omega
    refine ⟨τ₃.setVar "flag" 0, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_true (by rw [hcv]; simp [hlt])
        (Run.assign (v := 0) (evalB_lit (by omega)))))),
      ?_, by simp [hns], by simp, distClean_of_arrs_eq hcl₃ rfl⟩
    simp only [scatBlockK, clearMemK, scanMemK, Cond.size, Expr.size]
    have : K₂ ≤ clearMemK mm := hK₂
    simp only [clearMemK] at this
    omega
  · have hyes : t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    refine ⟨τ₃.setVar "flag" 1, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_false (by rw [hcv]; simp [hlt])
        (Run.assign (v := 1) (evalB_lit (by omega)))))),
      ?_, by simp [hyes], by simp, distClean_of_arrs_eq hcl₃ rfl⟩
    simp only [scatBlockK, clearMemK, scanMemK, Cond.size, Expr.size]
    have : K₂ ≤ clearMemK mm := hK₂
    simp only [clearMemK] at this
    omega

/-- **The active-set pass at a mask array the caller names, at the mask's
support.** `ScatterBlock.scatBlock_specA`'s route, unchanged: the proof is
`renCom_spec` applied to `scatBlockM_specW`, and the narrowing rides
through because `"dist"` is `MaskFree` and `distClean_renEnv` transports
the clause in one line — both at entry (`arenaAM_renEnv`) and now at
exit. No clause of the engine is re-walked and the charge is the landed
numeral. -/
theorem scatBlockM_specA {B : ℕ} {av : String} (hav : MaskFree av)
    (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaAtM av n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockComA av r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1 ∧ DistClean n r M σ')
      (scatBlockK mm bw nb t) := by
  intro σ hσ
  obtain ⟨τ, hrun, hq⟩ :=
    renCom_spec (f := maskSwap av) (maskSwap_invol av)
      (scatBlockM_specW hcsr hnB hnsB hnt hrB htB hMB hml hbud) σ
      ⟨(arenaAM_renEnv hav).2 hσ.1, hσ.2.imp fun _ hg => (exc_renEnv hav).2 hg⟩
  exact ⟨τ, hrun, hq.1, hq.2.1, (distClean_renEnv hav).1 hq.2.2⟩

/-- **The active-set pass at the pinned target array, at the mask's
support** — the narrowed counterpart of `ScatterBlock.scatBlock_spec`,
which is the widened walk at `nt = ns`. Nothing is re-walked. -/
theorem scatBlockM_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaAM n ns mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1 ∧ DistClean n r M σ')
      (scatBlockK mm bw nb t) :=
  scatBlockM_specW hcsr hnB hnsB le_rfl hrB htB hMB hml hbud

/-! ### §8a The variant the driver actually calls

**`ScatterBlock.scatBlock_specA` has no live consumer.** The driver's
`RamDriver.scatDeadCom` runs `scatBlockComA (alvName (j + 1)) r t`, and
the theorem `ScatterDeadTurn.scatDead_spec` points at it is
`ScatterDeadEngine.scatBlockCnt_specA` — the same program and the same
charge, with the counter kept in the postcondition (`cnt ≤ t` and the
`∀ e` decision clause the dead fold consumes). So the three exports of §8
narrow the pass, but the *driver's* pass is this one, and the successor
needs it narrowed too.

It costs almost nothing on top of §7: `ScatterDeadEngine`'s proof is the
prologue of `scatBlockM_specW` verbatim followed by `loop_spec`, and the
two counter clauses are read straight off the exit `ProgressA` — which
`loopM_spec` returns unchanged. So the narrowing goes through with the
same two distance lines and nothing else.

`ScatterDeadEngine.lean` is frozen this wave, so these sit here beside
it, exactly as §8 sits beside `ScatterBlock`. -/

/-- **The active-set pass with its counter, at the mask's support.**
`ScatterDeadEngine.scatBlockCnt_specW` with `ArenaAM` for `ArenaA`, all
four landed postcondition clauses verbatim, the clean-out added, and the
charge `scatBlockK mm bw nb t` unmoved. -/
theorem scatBlockCntM_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B)
    (hMB : ∀ z < n, M z < B) (hml : MemList n mm Mem X) {bw nb : ℕ}
    (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaAM n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1 ∧ σ'.vars "cnt" ≤ t ∧
        (∀ e : ℕ, (t ≤ σ'.vars "cnt" + e ↔
          t ≤ (greedySet (masked G M) r X).ncard + e)) ∧ DistClean n r M σ')
      (scatBlockK mm bw nb t) := by
  have hmmn : mm ≤ n := hml.card_le
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hA, g, hexc⟩ := hσ
  obtain ⟨hn, hmmv, hoff, htgt, halv, hmem, hdist, hqex, hqdex⟩ := id hA
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = σ.setVar "cnt" 0 := ⟨_, rfl⟩
  have run₁ : Run B (.assign "cnt" (.lit 0)) σ τ₁ 2 := by
    rw [hτ₁]; exact (Run.assign (v := 0) (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hv₁ : ∀ y, y ≠ "cnt" → τ₁.vars y = σ.vars y := by
    intro y hy; rw [hτ₁]; simp [hy]
  have ha₁ : τ₁.arrs = σ.arrs := by rw [hτ₁]; simp
  have hcnt₁ : τ₁.vars "cnt" = 0 := by rw [hτ₁]; simp
  obtain ⟨τ₂, K₂, run₂, hK₂, hmem₂, E, hexc₂, hclear, -⟩ :=
    clearMem_run (n := n) (mm := mm) (B := B) (Mem := Mem) (X := X)
      hnB (by omega) hml (by rw [hv₁ "n" (by decide)]; exact hn)
      (by rw [hv₁ "mm" (by decide)]; exact hmmv)
      (by rw [ha₁]; exact hmem) (by rw [ha₁]; exact hexc)
  have hcnt₂ : τ₂.vars "cnt" = 0 := by
    rw [run₂.frame_var "cnt" (notMem_clearMem_wvars "cnt" (by simp)), hcnt₁]
  have harr₂ : ∀ a, a ∈ ["off", "tgt", "alv", "dist", "q", "qd"] → τ₂.arrs a = σ.arrs a := by
    intro a ha
    rw [run₂.frame_arr a (notMem_clearMem_warrs a (by fin_cases ha <;> simp)), ha₁]
  have hA₂ : ArenaAM n nt mm r O T M Mem τ₂ := by
    obtain ⟨g₆, hq⟩ := hqex
    obtain ⟨g₇, hqd⟩ := hqdex
    refine ⟨?_, ?_, by rw [harr₂ "off" (by simp)]; exact hoff,
      by rw [harr₂ "tgt" (by simp)]; exact htgt,
      by rw [harr₂ "alv" (by simp)]; exact halv, hmem₂,
      distClean_of_arrs_eq hdist (harr₂ "dist" (by simp)),
      ⟨g₆, by rw [harr₂ "q" (by simp)]; exact hq⟩,
      ⟨g₇, by rw [harr₂ "qd" (by simp)]; exact hqd⟩⟩
    · rw [run₂.frame_var "n" (notMem_clearMem_wvars "n" (by simp)),
        hv₁ "n" (by decide), hn]
    · rw [run₂.frame_var "mm" (notMem_clearMem_wvars "mm" (by simp)),
        hv₁ "mm" (by decide), hmmv]
  have hI₂ : ScatBlockInvM n nt mm r t G M O T Mem X (τ₂.setVar "sj" 0) := by
    refine ⟨hA₂.setVar (by decide) (by decide), by simp, ?_⟩
    refine progressA_start hml ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact Or.inl ⟨by simp [hcnt₂], by omega⟩
    · refine Or.inr ⟨by simp [hcnt₂]; omega, by simp [hcnt₂, selBelow_zero], E,
        by simp [hexc₂], fun w hw => by rw [hclear w hw]; omega,
        fun w hw => by rw [hclear w hw]; simp⟩
  obtain ⟨τ₃, run₃, hA₃, hP₃, hsj₃⟩ :=
    (loopM_spec hcsr hnB hnsB hnt hrB htB hMB hml hbud).run (σ := τ₂) hI₂
  have hcl₃ : DistClean n r M τ₃ := bfs_pre_of_arenaAM hA₃
  -- the counter clauses, off the exit disjunction — unchanged by the narrowing
  have hcntt : τ₃.vars "cnt" ≤ t := hP₃.cnt_le
  have hcntB : τ₃.vars "cnt" < B := by omega
  have hkey : ∀ e : ℕ, (t ≤ τ₃.vars "cnt" + e ↔
      t ≤ (greedySet (masked G M) r X).ncard + e) := by
    intro e
    rcases hP₃ with ⟨hc, hle⟩ | ⟨-, hsel, -⟩
    · exact ⟨fun _ => by omega, fun _ => by omega⟩
    · rw [selBelow_all] at hsel
      rw [hsel]
  have hcv : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₃
      = some (decide (τ₃.vars "cnt" < t)) := evalB_condLt (evalB_var hcntB) (evalB_lit htB)
  by_cases hlt : τ₃.vars "cnt" < t
  · have hns : ¬ t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨h, -⟩ | ⟨-, h, -⟩
      · omega
      · rw [selBelow_all] at h; omega
    refine ⟨τ₃.setVar "flag" 0, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_true (by rw [hcv]; simp [hlt])
        (Run.assign (v := 0) (evalB_lit (by omega)))))),
      ?_, by simp [hns], by simp, by simpa using hcntt, by simpa using hkey,
      distClean_of_arrs_eq hcl₃ rfl⟩
    simp only [scatBlockK, clearMemK, scanMemK, Cond.size, Expr.size]
    have : K₂ ≤ clearMemK mm := hK₂
    simp only [clearMemK] at this
    omega
  · have hyes : t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    refine ⟨τ₃.setVar "flag" 1, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_false (by rw [hcv]; simp [hlt])
        (Run.assign (v := 1) (evalB_lit (by omega)))))),
      ?_, by simp [hyes], by simp, by simpa using hcntt, by simpa using hkey,
      distClean_of_arrs_eq hcl₃ rfl⟩
    simp only [scatBlockK, clearMemK, scanMemK, Cond.size, Expr.size]
    have : K₂ ≤ clearMemK mm := hK₂
    simp only [clearMemK] at this
    omega

/-- **The driver's pass, narrowed** — `ScatterDeadEngine.scatBlockCnt_specA`
at `ArenaAtM`, with the clean-out. Since wave B4-walk-2m-3 this is the
theorem `ScatterDeadTurn.scatDead_spec` consumes:
`RamDriver.scatDeadCom` runs `RamDriver.distMemCom` at the sixth slot,
so what the atom can establish is `DistClean` and not the whole-array
clause. Same `renCom` route, same charge. -/
theorem scatBlockCntM_specA {B : ℕ} {av : String} (hav : MaskFree av)
    (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaAtM av n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockComA av r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1 ∧ σ'.vars "cnt" ≤ t ∧
        (∀ e : ℕ, (t ≤ σ'.vars "cnt" + e ↔
          t ≤ (greedySet (masked G M) r X).ncard + e)) ∧ DistClean n r M σ')
      (scatBlockK mm bw nb t) := by
  intro σ hσ
  obtain ⟨τ, hrun, hq⟩ :=
    renCom_spec (f := maskSwap av) (maskSwap_invol av)
      (scatBlockCntM_specW hcsr hnB hnsB hnt hrB htB hMB hml hbud) σ
      ⟨(arenaAM_renEnv hav).2 hσ.1, hσ.2.imp fun _ hg => (exc_renEnv hav).2 hg⟩
  exact ⟨τ, hrun, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
    (distClean_renEnv hav).1 hq.2.2.2.2⟩

/-! ### §8b Nothing was lost

The re-walk is only honest if the landed export comes back out of it.
It does, in one line and at the same numeral, because the narrowing
weakens the precondition (`arenaAM_of_arenaA`) and *strengthens* the
postcondition (a third clause, the two `flag` clauses verbatim). The two
theorems below are the landed statements, character for character,
derived from the narrowed ones — so a clause silently weakened during the
re-walk could not compile here. They are gates, not exports:
`ScatterBlock.scatBlock_specW` and `_specA` are untouched and remain the
names every landed consumer uses. -/

/-- **`ScatterBlock.scatBlock_specW`, recovered.** The landed statement,
verbatim, out of `scatBlockM_specW`. -/
theorem scatBlock_specW_of_M {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B)
    (hMB : ∀ z < n, M z < B) (hml : MemList n mm Mem X) {bw nb : ℕ}
    (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaA n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1)
      (scatBlockK mm bw nb t) := by
  intro σ hσ
  obtain ⟨τ, hrun, hq⟩ :=
    scatBlockM_specW hcsr hnB hnsB hnt hrB htB hMB hml hbud σ
      ⟨arenaAM_of_arenaA hσ.1, hσ.2⟩
  exact ⟨τ, hrun, hq.1, hq.2.1⟩

/-- **`ScatterDeadEngine.scatBlockCnt_specA`, recovered** — the driver's
own pass, the landed statement verbatim, out of the narrowed one. This
is the gate that matters most: it is the theorem
`ScatterDeadTurn.scatDead_spec` consumes today. -/
theorem scatBlockCnt_specA_of_M {B : ℕ} {av : String} (hav : MaskFree av)
    (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaAt av n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockComA av r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1 ∧ σ'.vars "cnt" ≤ t ∧
        ∀ e : ℕ, (t ≤ σ'.vars "cnt" + e ↔
          t ≤ (greedySet (masked G M) r X).ncard + e))
      (scatBlockK mm bw nb t) := by
  intro σ hσ
  obtain ⟨τ, hrun, hq⟩ :=
    scatBlockCntM_specA hav hcsr hnB hnsB hnt hrB htB hMB hml hbud σ
      ⟨arenaAtM_of_arenaAt hσ.1, hσ.2⟩
  exact ⟨τ, hrun, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩

/-- **`ScatterBlock.scatBlock_specA`, recovered**, at the caller-named
mask. -/
theorem scatBlock_specA_of_M {B : ℕ} {av : String} (hav : MaskFree av)
    (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaAt av n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockComA av r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1)
      (scatBlockK mm bw nb t) := by
  intro σ hσ
  obtain ⟨τ, hrun, hq⟩ :=
    scatBlockM_specA hav hcsr hnB hnsB hnt hrB htB hMB hml hbud σ
      ⟨arenaAtM_of_arenaAt hσ.1, hσ.2⟩
  exact ⟨τ, hrun, hq.1, hq.2.1⟩

/-! ### §9 The narrowing is strict at the pass, and the clean-out is not
recoverable

Two concrete environments, in the two directions the wave has to be
honest about.

* **Entry.** `arenaAM_strict` exhibits a state satisfying `ArenaAM` and
  refuting `ArenaA`: the mask kills vertex `1` and that cell holds junk.
  So the narrowed precondition is genuinely weaker and the atom's
  `fillCom "dist"` really is establishing something no consumer asks for.
* **Exit.** `post_flag_gives_no_distClean` exhibits a state satisfying
  the landed postcondition's `flag` clauses and refuting `DistClean`. So
  the third clause of `scatBlockM_specW` is an **addition** that had to be
  stated: it cannot be recovered from the landed export, and without it
  the successor cannot chain one atom to the next. -/

/-- A carrier of two vertices, `1` dead and holding junk. -/
private def envAM : Env where
  vars := fun x => if x = "n" then 2 else 0
  arrs := fun a =>
    if a = "off" then arrOf 3 (fun _ => 0)
    else if a = "tgt" then arrOf 0 (fun _ => 0)
    else if a = "alv" then arrOf 2 m2
    else if a = "dist" then arrOf 2 d2
    else arrOf 2 (fun _ => 0)
  inp := []
  out := []

/-- **The narrowed arena holds where the landed one fails.** Compiled at
a concrete state, so the strictness is exhibited and not asserted. -/
theorem arenaAM_strict :
    ArenaAM 2 0 0 0 (fun _ => 0) (fun _ => 0) m2 (fun _ => 0) envAM ∧
      ¬ ArenaA 2 0 0 0 (fun _ => 0) (fun _ => 0) m2 (fun _ => 0) envAM := by
  constructor
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨d2, rfl, ?_⟩, ⟨fun _ => 0, rfl⟩,
      ⟨fun _ => 0, rfl⟩⟩
    intro z hz hm
    have hz0 : z = 0 := by by_contra hne; simp [m2, hne] at hm
    rw [hz0]; simp [d2]
  · intro h
    have hd : envAM.arrs "dist" = arrOf 2 (fun _ => 0 + 1) := h.2.2.2.2.2.2.1
    have e₀ := getD_arrOf d2 (show (1 : ℕ) < 2 by omega)
    have e₁ := getD_arrOf (fun _ : ℕ => 0 + 1) (show (1 : ℕ) < 2 by omega)
    have : (arrOf 2 d2).getD 1 0 = (arrOf 2 (fun _ : ℕ => 0 + 1)).getD 1 0 := by
      rw [show arrOf 2 d2 = envAM.arrs "dist" from rfl, hd]
    rw [e₀, e₁] at this
    simp [d2] at this

/-- Both vertices alive — a mask strictly larger than `m2`'s support. -/
private def mAll : ℕ → ℕ := fun _ => 1

/-- **The narrowing is to the mask, not to the member list — compiled.**
The pass carries two supports and they are not the same one. `ArenaAM`
speaks of the *mask* `M`, while `MemList n mm Mem X` speaks of `X`, and
`ScatterDeadPass.atomMemCom_spec` hands the pass a **filtered** list
(`mm ≤ mm1`, the child's list cut down to `bitSet n A Tb`) over a mask
that is not cut down with it. So there are alive non-members, and the
search reads their distance cells: `RamBfs.scanSlot` tests `alv[w]` and
nothing else before relaxing `dist[w]`.

Below, `m2` plays the member support and `mAll` the mask: an array clean
on the members is *not* clean on the mask. Together with the landed
`BfsBlockMask.frontier_cap_refuted` / `frontier_sound_refuted` — which
show a dirty alive cell makes the frontier invariant **false**, not
merely unprovable — this is the reason a member-scoped arena clause would
be unsound and `DistClean n r M` is the only narrowing available. -/
theorem member_support_not_mask_support :
    (∀ z < 2, m2 z ≠ 0 → d2 z = 0 + 1) ∧ ¬ CleanOn 2 0 mAll d2 := by
  refine ⟨fun z hz hm => ?_, fun h => ?_⟩
  · have hz0 : z = 0 := by by_contra hne; simp [m2, hne] at hm
    rw [hz0]; simp [d2]
  · have hd := h 1 (by omega) (by simp [mAll])
    simp [d2] at hd

/-- The same carrier with every distance cell holding junk. -/
private def envBad : Env where
  vars := fun _ => 0
  arrs := fun a => if a = "dist" then arrOf 2 (fun _ => 5) else arrOf 2 (fun _ => 0)
  inp := []
  out := []

/-- **The landed postcondition's `flag` clauses give no clean-out.** They
constrain a scalar and no array, so a state can satisfy them with the
distance array arbitrarily dirty on the mask's support. This is why
`scatBlockM_specW` has to *state* `DistClean` at the exit rather than
recover it from `ScatterBlock.scatBlock_specW`. -/
theorem post_flag_gives_no_distClean :
    envBad.vars "flag" ≤ 1 ∧ ¬ DistClean 2 0 m2 envBad := by
  refine ⟨by simp [envBad], ?_⟩
  rintro ⟨D₀, hD, hc⟩
  have h0 : D₀ 0 = 0 + 1 := hc 0 (by omega) (by simp [m2])
  have hEq : arrOf 2 (fun _ : ℕ => 5) = arrOf 2 D₀ := hD
  have e₀ : (arrOf 2 D₀).getD 0 0 = D₀ 0 := getD_arrOf D₀ (show (0 : ℕ) < 2 by omega)
  have e₁ : (arrOf 2 (fun _ : ℕ => 5)).getD 0 0 = 5 :=
    getD_arrOf (fun _ : ℕ => 5) (show (0 : ℕ) < 2 by omega)
  rw [hEq, e₀] at e₁
  omega

/-! ### §10 The bridge the member-driven fill crosses

`RamDriver.scatDeadCom` paid `fillCom "dist" (.lit (r + 1))` —
`11 n + 6`, the last carrier-sized summand in the per-atom charge — and
wave B4-walk-2m-3 replaced it with `RamDriver.distMemCom`, a
member-driven fill. What that fill has to establish is exactly
`DistClean n r M σ`, the proposition `ArenaAM` carries and
`scatBlockM_specW` consumes; the two lemmas below are the one line that
gets it there, and `ScatterDeadTurn.scatDead_spec` is where the line is
used.

They are stated so that **the hypothesis names the hazard**. `hcov` asks
that the driving list cover the *mask's* support, and
`member_support_not_mask_support` is the compiled reason it cannot be the
pass's own member list: `ScatterDeadPass.atomMemCom_spec` filters the
child's `MemEnum n mm1 Mem1 A` down to `mm ≤ mm1` entries for
`bitSet n A Tb`, and the search reads the distance cells of the alive
non-members it drops. So the fill must be driven by the **unfiltered**
`mm1`-list, which enumerates the mask — and `hcov` is unprovable for the
filtered one, which is what makes the mistake a build failure rather than
an unsoundness.

That is how it is discharged at the one live call site:
`ScatterDeadTurn.scatDead_spec` passes `hmem1E.2.2.2`, the fourth clause
of the **child's** `RamDriver.MemEnum n mm1 Mem1 Alv'`, which
`RamDriverCluster.ClusterData` carries and `atomMemCom_spec` preserves
across the filter. The atom's own `MemList` at `"mm"` is never offered
to it. -/

/-- **A fill driven by a list covering the mask's support is clean on
it.** -/
theorem cleanOn_of_cover {mm1 : ℕ} {Mem1 D₀ : ℕ → ℕ}
    (hcov : ∀ z, z < n → M z ≠ 0 → ∃ k, k < mm1 ∧ Mem1 k = z)
    (hfill : ∀ k, k < mm1 → D₀ (Mem1 k) = r + 1) : CleanOn n r M D₀ := by
  intro z hz hm
  obtain ⟨k, hk, rfl⟩ := hcov z hz hm
  exact hfill k hk

/-- The same, packaged at the state — this is what the successor hands
`scatBlockM_specA` in place of the whole-array fill. -/
theorem distClean_of_cover {σ : Env} {mm1 : ℕ} {Mem1 D₀ : ℕ → ℕ}
    (harr : σ.arrs "dist" = arrOf n D₀)
    (hcov : ∀ z, z < n → M z ≠ 0 → ∃ k, k < mm1 ∧ Mem1 k = z)
    (hfill : ∀ k, k < mm1 → D₀ (Mem1 k) = r + 1) : DistClean n r M σ :=
  ⟨D₀, harr, cleanOn_of_cover hcov hfill⟩

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.distClean_of_cover' does not depend on any axioms -/
#guard_msgs in
#print axioms distClean_of_cover

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.stepM_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepM_run

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.loopM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loopM_spec

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.scatBlockM_specW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatBlockM_specW

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.scatBlockM_specA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatBlockM_specA

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.scatBlockM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatBlockM_spec

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.scatBlockCntM_specW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatBlockCntM_specW

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.scatBlockCntM_specA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatBlockCntM_specA

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.scatBlockCnt_specA_of_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatBlockCnt_specA_of_M

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.scatBlock_specW_of_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatBlock_specW_of_M

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.scatBlock_specA_of_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatBlock_specA_of_M

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.arenaAM_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arenaAM_strict

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.post_flag_gives_no_distClean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms post_flag_gives_no_distClean

/-- info: 'Lax3Proofs.Refine.ScatterBlockMask.member_support_not_mask_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms member_support_not_mask_support

end Lax3Proofs.Refine.ScatterBlockMask
