import Lax235315Proofs.Construction.RoundInvariant
import Lax235315Proofs.Construction.BitArrays
import Mathlib.Tactic

/-! Scratch assignments preserve the persistent state carried by the driver.
The protected names are exactly the scalar names observed by each invariant. -/
namespace Lax235315Proofs.Construction.FrontierFrames

open Lax808846Proofs.Imp
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.BitArrays
open Lax235315Proofs.Construction.MarkingMath

/-- A name outside the workspace's five persistent scalar fields. -/
def WorkspaceScratchName (name : String) : Prop :=
  name ∉ ["c", "n", "m", "L", "qpow"]

/-- A name outside every scalar inspected by the frontier invariant. -/
def FrontierScratchName (name : String) : Prop :=
  name ∉ ["c", "n", "m", "L", "qpow", "good", "acount", "removedCount", "round"]

private lemma ne_of_workspaceScratch {name : String}
    (h : WorkspaceScratchName name) :
    name ≠ "c" ∧ name ≠ "n" ∧ name ≠ "m" ∧ name ≠ "L" ∧ name ≠ "qpow" := by
  simp [WorkspaceScratchName] at h
  exact h

private lemma ne_of_frontierScratch {name : String}
    (h : FrontierScratchName name) :
    name ≠ "c" ∧ name ≠ "n" ∧ name ≠ "m" ∧ name ≠ "L" ∧
      name ≠ "qpow" ∧ name ≠ "good" ∧ name ≠ "acount" ∧
      name ≠ "removedCount" ∧ name ≠ "round" := by
  simp [FrontierScratchName] at h
  exact h

/-- Writing a bounded scratch scalar preserves the workspace invariant. -/
lemma workspace_setVar {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Workspace B c n x σ) (name : String) {v : ℕ} (hv : v < B)
    (hname : WorkspaceScratchName name) :
    Workspace B c n x (σ.setVar name v) := by
  rcases h with ⟨hb, hc, hn, hm, hL, hq, hoff, htgt, hlen, hbits, hout⟩
  rcases ne_of_workspaceScratch hname with ⟨hC, hN, hM, hLog, hQ⟩
  refine ⟨hb.setVar name hv, ?_, ?_, ?_, ?_, ?_, hoff, htgt, hlen, hbits, hout⟩
  · simpa [Env.setVar, hC.symm] using hc
  · simpa [Env.setVar, hN.symm] using hn
  · simpa [Env.setVar, hM.symm] using hm
  · simpa [Env.setVar, hLog.symm] using hL
  · simpa [Env.setVar, hQ.symm] using hq

/-- Writing a bounded scratch scalar preserves every certificate in the
successful frontier, including active counts, bit arrays, conservation, and
shrinking history. -/
lemma frontier_setVar {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Frontier B c n x σ) (name : String) {v : ℕ} (hv : v < B)
    (hname : FrontierScratchName name) :
    Frontier B c n x (σ.setVar name v) := by
  rcases h with ⟨hw, hgood, hcount, hnonemptyA, hnonemptyB,
    hactiveA, hactiveB, hnextA, hnextB, hconservation, hshrinking⟩
  rcases ne_of_frontierScratch hname with
    ⟨hC, hN, hM, hLog, hQ, hGood, hCount, hRemoved, hRound⟩
  have hws : WorkspaceScratchName name := by
    simp [WorkspaceScratchName]
    exact ⟨hC, hN, hM, hLog, hQ⟩
  have hview (a : String) : view (σ.setVar name v) a = view σ a := rfl
  refine ⟨workspace_setVar hw name hv hws,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Env.setVar, hGood.symm] using hgood
  · change (if "acount" = name then v else σ.vars "acount") =
      (activeVertices n (view (σ.setVar name v) "activeA")).card
    rw [if_neg hCount.symm, hview]
    exact hcount
  · simpa [hview] using hnonemptyA
  · simpa [hview] using hnonemptyB
  · simpa [ArrayBits, Env.setVar] using hactiveA
  · simpa [ArrayBits, Env.setVar] using hactiveB
  · simpa [ArrayBits, Env.setVar] using hnextA
  · simpa [ArrayBits, Env.setVar] using hnextB
  · simpa [Env.setVar, hRemoved.symm, hCount.symm] using hconservation
  · simpa [Env.setVar, hRound.symm, hCount.symm] using hshrinking

end Lax235315Proofs.Construction.FrontierFrames

namespace Lax235315Proofs.Construction.RoundInvariant.Workspace

/-- Method-style API for framing a workspace across a scratch assignment. -/
theorem setVar {B c n : ℕ} {x : List ℕ} {σ : Lax808846Proofs.Imp.Env}
    (h : Lax235315Proofs.Construction.RoundInvariant.Workspace B c n x σ)
    (name : String) {v : ℕ} (hv : v < B)
    (hname : Lax235315Proofs.Construction.FrontierFrames.WorkspaceScratchName name) :
    Lax235315Proofs.Construction.RoundInvariant.Workspace B c n x
      (σ.setVar name v) :=
  Lax235315Proofs.Construction.FrontierFrames.workspace_setVar h name hv hname

end Lax235315Proofs.Construction.RoundInvariant.Workspace

namespace Lax235315Proofs.Construction.RoundInvariant.Frontier

/-- Method-style API for framing a successful frontier across a scratch
assignment. -/
theorem setVar {B c n : ℕ} {x : List ℕ} {σ : Lax808846Proofs.Imp.Env}
    (h : Lax235315Proofs.Construction.RoundInvariant.Frontier B c n x σ)
    (name : String) {v : ℕ} (hv : v < B)
    (hname : Lax235315Proofs.Construction.FrontierFrames.FrontierScratchName name) :
    Lax235315Proofs.Construction.RoundInvariant.Frontier B c n x
      (σ.setVar name v) :=
  Lax235315Proofs.Construction.FrontierFrames.frontier_setVar h name hv hname

end Lax235315Proofs.Construction.RoundInvariant.Frontier
