import Lax3Proofs.Refine.ActiveRoot
import Lax3Proofs.Refine.G2CostProbe

/-!
# The sigma recurrence for the concrete active root

The former `G2CostProbe.g2_plug` deliberately left three implications:
carrier-wide order, carrier-wide cover, and the turn.  The concrete active
root has replaced the first two programs.  This file instantiates the same
canonical sigma recurrence directly with their actual arena-relative costs;
the turn is consequently the sole remaining execution-cost seam.
-/

namespace Lax3Proofs.Refine.ActiveCost

open Finset
open Lax3Proofs.Refine.OrderActiveBudget
open Lax3Proofs.Refine.CoverActiveBudget
open Lax3Proofs.Refine.G2CostProbe (turnCostSizeA sweepCoeffA hKbase_paid)

/-- An affine coefficient for the complete active-cover phase.  Its only
input-size dependence is the number of radix rounds, `clog 2 n`. -/
def activeCoverCostCoeff (n d : ℕ) : ℕ :=
  300 * d + 236 * Nat.clog 2 n * d + 40 * Nat.clog 2 n + 263

/-- The concrete active-cover charge is affine in the current arena weight. -/
theorem activeCoverCost_le_coeff (n d a : ℕ) :
    activeCoverCost n d a ≤ activeCoverCostCoeff n d * (a + 1) := by
  simp only [activeCoverCost, activeCoverCoreCost, activeCoverCostCoeff]
  nlinarith [Nat.zero_le a, Nat.zero_le d, Nat.zero_le (Nat.clog 2 n)]

/-- The per-level coefficient of the concrete active recurrence. -/
def activeG2A (n d D₁ R ct ksc D : ℕ) : ℕ :=
  activeOrderCostCoeff d D₁ R +
    (activeCoverCostCoeff n D + ((ct + ksc + 3) * (D + 1) + 14))

/-- The canonical sigma witness at the two concrete active phase costs.

`KscCoeff j` is a coefficient for the scatter chain at level `j`; the
execution layer still has to prove that the complete turn fits the displayed
`turnCostSizeA` budget.  No order- or cover-phase domination is assumed.
-/
theorem active_g2_exists (n ℓ D Cb d D₁ R ct kscMax : ℕ)
    (KscCoeff : ℕ → ℕ) (hKscCoeff : ∀ j < ℓ, KscCoeff j ≤ kscMax) :
    ∃ Ks Kl : ℕ → ℕ → ℕ,
      (∀ w, Cb * (w + 1) ≤ Kl ℓ w) ∧
      (∀ j, Monotone (Kl j)) ∧
      (∀ j < ℓ, ∀ s : ℕ,
        turnCostSizeA ct (KscCoeff j) s (Kl (j + 1) s) ≤ Ks j s) ∧
      (∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ range t, bs c) ≤ D * (w + 1) →
        activeOrderCost d D₁ R w +
            (activeCoverCost n D w +
              ((∑ c ∈ range t, (Ks j (bs c) + 11)) + 6)) ≤ Kl j w) ∧
      (∀ w, Kl 0 w ≤
        (ℓ * activeG2A n d D₁ R ct kscMax D + Cb) *
          (D + 1) ^ ℓ * (w + 1)) := by
  classical
  obtain ⟨Kl, Kt, hbase, hmono, hKt, hKlS, hKl0, -⟩ :=
    Lax3Proofs.CostRecurrence.exists_driverCostsSigma ℓ D Cb
      (fun _ => activeOrderCostCoeff d D₁ R)
      (fun _ => activeCoverCostCoeff n D)
      (fun j => ct + KscCoeff j + 3)
      (fun _ w => activeOrderCost d D₁ R w)
      (fun _ w => activeCoverCost n D w)
      (fun j s => (ct + KscCoeff j) * (s + 1) + 3)
      (fun j s Kin => turnCostSizeA ct (KscCoeff j) s Kin + 3)
      (fun _ _ => le_rfl)
      (fun _ w => activeCoverCost_le_coeff n D w)
      (fun _ s => by nlinarith [Nat.zero_le s])
      (fun _ _ _ => by simp only [turnCostSizeA]; omega)
  refine ⟨fun j s => turnCostSizeA ct (KscCoeff j) s (Kl (j + 1) s), Kl,
    hbase, hmono, (fun _ _ _ => le_rfl), ?_, ?_⟩
  · exact Lax3Proofs.RamDriverRoot.levelCost_of_sigma
      (fun j s => hKt j s)
      (fun j hj m t htm bs hbs => hKlS j hj m t htm bs hbs)
  · intro w
    rw [hKl0 w]
    refine Nat.mul_le_mul_right _ ?_
    have hs :
        (∑ j ∈ range ℓ,
            Lax3Proofs.CostRecurrence.driverASigma
                (fun _ => activeOrderCostCoeff d D₁ R)
                (fun _ => activeCoverCostCoeff n D)
                (fun j => ct + KscCoeff j + 3) D j * (D + 1) ^ j) +
            Cb * (D + 1) ^ ℓ =
          Lax3Proofs.CostRecurrence.solve
            (Lax3Proofs.CostRecurrence.driverASigma
              (fun _ => activeOrderCostCoeff d D₁ R)
              (fun _ => activeCoverCostCoeff n D)
              (fun j => ct + KscCoeff j + 3) D)
            (fun _ => D + 1) Cb ℓ 0 :=
      (Lax3Proofs.CostRecurrence.solve_const _ _ _ _).symm
    rw [hs]
    refine Lax3Proofs.CostRecurrence.solve_sigma_le fun j hj => ?_
    have hsc : (ct + KscCoeff j + 3) * (D + 1) ≤
        (ct + kscMax + 3) * (D + 1) :=
      Nat.mul_le_mul_right _ (by have := hKscCoeff j hj; omega)
    simp only [Lax3Proofs.CostRecurrence.driverASigma, activeG2A]
    omega

section RootPlug

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverMember
open Lax3Proofs.RamDriverDedup (dedupNs DedupMem)
open Lax3Proofs.Refine.ActiveRoot
open Lax13Proofs.Imp Lax13Proofs.Reasoning

open Classical in
/-- The replacement for the old `g2_plug`, at the executable active root.

The canonical recurrence now consumes the concrete order and cover charges
without hypotheses.  The final implication is exactly the remaining turn
engine seam: prove the landed turn is affine in its block weight, and the
whole executable root follows at the displayed geometric budget. -/
theorem active_root_g2_plug
    {n : ℕ} {B q_top cap mb ns W ℓ s R d D₁ D : ℕ}
    {N : ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {Kb : ℕ → ℕ} {Kb₀ Kdec Ksent : ℕ}
    {Ki KscR : ℕ → ℕ → ℕ}
    (ct kscMax Cb : ℕ) (KscCoeff : ℕ → ℕ)
    (hKscCoeff : ∀ j < ℓ, KscCoeff j ≤ kscMax)
    (hCb : sweepCoeffA q_top cap mb ℓ φ ≤ Cb)
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hxB : ∀ v ∈ x, v < B)
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top)
    (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n D ns cap mb) (hWB : W < B) (hnsW : ns ≤ W)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧
        2 * s + 2 ≤ Bd.ncard ∧ DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧ ∀ z,
          Lax3Proofs.Refine.ScatterDeadTurn.deadAtomKBlk
            σs.β z mb z z σs.t ≤ Kb z)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ z, Kb z * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j z)
    (hKscR : ∀ j < ℓ, ∀ z,
      Ki j z * (tablesAt q_top cap mb φ j).length + 1 ≤ KscR j z)
    (hwidthB : n + activeOrderWidth d D₁ R (n + ns) + 1 < B)
    (hwidthW : activeOrderWidth d D₁ R (n + ns) ≤ W)
    (hdeg : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M)),
      Lax3Proofs.Augmentation.LowDegreeVertices
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) d)
    (hdens : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M))
        (A : ℕ → Lax3Proofs.Augmentation.Orientation mm) (i : ℕ), i ≤ R →
      Lax3Proofs.Augmentation.IsAugChain
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) A i →
      (∀ l < i, Lax3Proofs.Augmentation.GreedyFratRound (A l) (A (l + 1))) →
      Lax3Proofs.Augmentation.AugmentedDepthOneDensity A i D₁)
    (hD : 1 ≤ D)
    (hdegree : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M))
        {A : ℕ → Lax3Proofs.Augmentation.Orientation mm}
        {d₀ k : ℕ} {pi : Equiv.Perm (Fin mm)},
      Lax3Proofs.CoverDegree.AugChainData
          (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) A pi R d₀ k →
        ∀ v : Fin mm,
          (Lax12.ColoringNumbers.wreach
            (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) pi (2 * cap) v).ncard ≤ D)
    (hKdec : Lax3Proofs.RamDriverIO.decodeCost n ns +
      Lax3Proofs.RamDriverDedup.dedupCost n ns + 4 ≤ Kdec)
    (hatoms : ∀ sa ∈
      (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      sa.r + 1 < B ∧ sa.t < B ∧
        Lax3Proofs.RamDriverIO.atomCost n (dedupNs x) sa.t ≤ Kb₀)
    (hKsent : Kb₀ *
        (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (Lax3Proofs.RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent) :
    ∃ Kl : ℕ → ℕ → ℕ,
      (∀ j, Monotone (Kl j)) ∧
      (∀ w, Kl 0 w ≤
        (ℓ * activeG2A n d D₁ R ct kscMax D + Cb) *
          (D + 1) ^ ℓ * (w + 1)) ∧
      ((∀ j < ℓ, ∀ t : ℕ,
          Lax3Proofs.RamDriverRoot.turnCostSize n (dedupNs x) cap mb q_top j φ
              (KscR j t) t (Kl (j + 1) t) ≤
            turnCostSizeA ct (KscCoeff j) t (Kl (j + 1) t)) →
        Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧
            DepthMem n cap mb σ ∧ OrderMem B n 0 W σ ∧ DedupMem n σ ∧
            TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
            σ.inp = x ∧ σ.out = [])
          (driverRootActive q_top cap mb R ℓ φ)
          (fun _ σ' => σ'.out =
            [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
          (Kdec + (Kl 0 (n + dedupNs x) + Ksent))) := by
  obtain ⟨Ks, Kl, hbase, hmono, hKsA, hKl, hclosed⟩ :=
    active_g2_exists n ℓ D Cb d D₁ R ct kscMax KscCoeff hKscCoeff
  refine ⟨Kl, hmono, hclosed, ?_⟩
  intro hturn
  have hKbase : ∀ m,
      Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ m φ ≤ Kl ℓ m := fun m =>
    le_trans (le_trans (hKbase_paid q_top cap mb ℓ m φ)
      (Nat.mul_le_mul_right _ hCb)) (hbase m)
  exact driverRootActive_decides_sentence hx hns hxB hrank hcap hmb hℓ hB hWB hnsW
    hQ hbnd hcostI hKscR hmono
    (fun j hj t => le_trans (hturn j hj t) (hKsA j hj t)) hKbase
    hwidthB hwidthW hdeg hdens hD hdegree hKl hKdec hatoms hKsent

end RootPlug

/-! ## Axiom audit -/

#print axioms activeCoverCost_le_coeff
#print axioms active_g2_exists
#print axioms active_root_g2_plug

end Lax3Proofs.Refine.ActiveCost
