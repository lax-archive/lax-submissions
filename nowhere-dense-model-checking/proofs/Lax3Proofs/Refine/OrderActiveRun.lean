import Lax3Proofs.Refine.OrderActiveInit

/-!
# The compact active ordering chain through all augmentation rounds

This file joins resident member-graph compaction, the initial elimination,
and the complete compact augmentation fold.  The public capacity hypothesis
is stated at the original level slot count; compaction proves its runtime
slot count is smaller before the fold consumes the bound.
-/

namespace Lax3Proofs.Refine.OrderActiveRun

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Augmentation (Orientation IsAugChain GreedyFratRound
  AugmentedDepthOneDensity LowDegreeVertices)
open Lax3Proofs.RamElim (CsrSimple)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.Refine.ElimCompact (memGraph memRowSum)
open Lax3Proofs.Refine.OrderActiveChain
open Lax3Proofs.Refine.OrderActiveInit

def compactActiveChainCom (j R : ℕ) : Com :=
  .seq (compactElimFoldInitCom j) (activeRoundsCom R)

def compactActiveChainCost (mm rs cs w R : ℕ) : ℕ :=
  compactElimFoldInitCost mm rs cs + (R * activeRoundCost mm w + 1)

/-- Starting from the resident level graph and member list, construct the
compact member graph, orient it greedily, and run all `R` augmentation
rounds in the active workspace. -/
theorem compactActiveChain_spec {B n mm ns W w j R d D₁ : ℕ}
    {G : SimpleGraph (Fin n)} {O T M Mem : ℕ → ℕ} { σ : Env }
    (hcsr : CsrSimple G ns O T)
    (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M))
    (hBns : n + ns + 1 < B) (hBW : mm + w + 1 < B)
    (hnB : n < B) (hMB : ∀ v < n, M v < B)
    (hnsW : ns ≤ W) (hwW : w ≤ W)
    (hd : LowDegreeVertices (memGraph G M hml) d)
    (hdens : ∀ (D : ℕ → Orientation mm) (i : ℕ), i ≤ R →
      IsAugChain (memGraph G M hml) D i →
      (∀ l < i, GreedyFratRound (D l) (D (l + 1))) →
      AugmentedDepthOneDensity D i D₁)
    (hcap : activeChainWidthE mm (memRowSum mm O Mem) d D₁ R ≤ w)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm)
    (hmem : σ.arrs "mem" = arrOf n Mem)
    (hoff : σ.arrs "off" = arrOf (n + 1) O)
    (htgt : σ.arrs "tgt" = arrOf W T)
    (halv : σ.arrs (Lax3Proofs.RamDriver.alvName j) = arrOf n M)
    (hsz : ActiveOrderSized n W σ) :
    ∃ σ' k cs,
      Run B (compactActiveChainCom j R) σ σ'
        (compactActiveChainCost mm (memRowSum mm O Mem) cs w R) ∧
      cs ≤ memRowSum mm O Mem ∧ cs ≤ ns ∧
      ActiveFoldInv n mm W w k (memGraph G M hml) Mem R σ' ∧
      (∀ k', LowDegreeVertices (memGraph G M hml) k' → k ≤ k') := by
  have hmn : mm ≤ n :=
    Lax3Proofs.Refine.ElimCompactWalks.card_le_of_smono
      (fun i j hij hj => hml.smono i j hij hj) (fun i hi => hml.lt i hi)
  have hrsw : memRowSum mm O Mem ≤ w := by
    simp only [activeChainWidthE] at hcap
    omega
  obtain ⟨σ₁, k, cs, r₁, hcsrs, hcsns, hI, hmin⟩ :=
    compactElimFoldInit_spec hcsr hml (by omega) hnB hMB hnsW hrsw hwW
      (by omega) hn hmm hmem hoff htgt halv hsz
  have hcapcs : activeChainWidthE mm cs d D₁ R ≤ w := by
    simp only [activeChainWidthE] at hcap ⊢
    omega
  obtain ⟨σ₂, r₂, hIR⟩ :=
    activeFold_run hml hmn hwW hBW hnB (hmin d hd) hdens hcapcs hI
  refine ⟨σ₂, k, cs, ?_, hcsrs, hcsns, hIR, hmin⟩
  simpa only [compactActiveChainCom, compactActiveChainCost] using r₁.seq r₂

/-! ## Axioms -/

#print axioms compactActiveChain_spec

end Lax3Proofs.Refine.OrderActiveRun
