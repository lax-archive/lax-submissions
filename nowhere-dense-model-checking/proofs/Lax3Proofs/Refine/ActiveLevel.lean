import Lax3Proofs.RamDriverMemberRoot
import Lax3Proofs.Refine.OrderActiveBudget
import Lax3Proofs.Refine.CoverActiveDriver

/-!
# The concrete active recursive level

The member driver is parameterized by its ordering and cover phases.  This
file first reads the write set of that recursion after instantiating those
parameters with the compact active phases.  It then plugs their semantic
contracts and the resulting frames into `RamDriverMemberRoot.levelAtA`.
-/

namespace Lax3Proofs.Refine.ActiveLevel

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverMember
open Lax3Proofs.RamDriverMemberRoot
open Lax3Proofs.Refine.OrderActiveDriver
open Lax3Proofs.Refine.OrderActiveBudget
open Lax3Proofs.Refine.CoverActiveDriver
open Lax3Proofs.Refine.CoverActiveBudget
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## The recursive write frame -/

open Classical in
/-- A concrete active level writes no array owned by a shallower level. -/
theorem belowArr_notMem_warrs_activeDriverAux
    (q_top cap mb ℓ R : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ (f d : ℕ) {a : String}, Lax3Proofs.RamDriverWrites.BelowArr d a →
      a ∉ (driverAuxA q_top cap mb ℓ φ
        (fun j => activeOrderPhase j R) (fun j => activeCoverPhase j cap) f d).warrs := by
  intro f
  induction f with
  | zero =>
      intro d a h hm
      rw [driverAuxA] at hm
      exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_baseCom
        q_top cap mb d φ h hm
  | succ f ih =>
      intro d a h hm
      rw [driverAuxA] at hm
      rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hm with hq | hq
      · exact belowArr_notMem_activeOrderPhase h hq
      rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hq with hq | hq
      · exact belowArr_notMem_activeCoverPhase h hq
      rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hq with hq | hq
      · rw [Com.warrs] at hq
        exact absurd hq List.not_mem_nil
      rw [Com.warrs] at hq
      rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hq with hq | hq
      · rw [Com.warrs] at hq
        exact absurd hq List.not_mem_nil
      rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hq with hq | hq
      · rw [clusterCom] at hq
        rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hq with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_descendCom cap d h hr
        rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_enumBatch
            (batName d) (cluName d) mb h hr
        rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_colourCom cap mb d h hr
        rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_killCom
            q_top cap mb d φ h hr
        rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_killListCom mb d h hr
        rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hr with hr | hr
        · exact ih (d + 1) (h.mono (Nat.le_succ d)) hr
        rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_scatterDeadPhase
            q_top cap mb d φ h hr
        · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_readbackCom
            q_top cap mb d φ h hr
      · rw [Com.warrs] at hq
        exact absurd hq List.not_mem_nil

open Classical in
/-- The scalar half of the concrete active recursion frame. -/
theorem belowVar_notMem_wvars_activeDriverAux
    (q_top cap mb ℓ R : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ (f d : ℕ) {y : String}, Lax3Proofs.RamDriverWrites.BelowVar d y →
      y ∉ (driverAuxA q_top cap mb ℓ φ
        (fun j => activeOrderPhase j R) (fun j => activeCoverPhase j cap) f d).wvars := by
  intro f
  induction f with
  | zero =>
      intro d y h hm
      rw [driverAuxA] at hm
      exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_baseCom
        q_top cap mb d φ h hm
  | succ f ih =>
      intro d y h hm
      rw [driverAuxA] at hm
      rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hm with hq | hq
      · exact belowVar_notMem_activeOrderPhase h hq
      rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hq with hq | hq
      · exact belowVar_notMem_activeCoverPhase h hq
      rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hq with hq | hq
      · rw [Com.wvars] at hq
        exact Lax3Proofs.RamDriverWrites.belowVar_ne h le_rfl (by tauto)
          (List.eq_of_mem_singleton hq)
      rw [Com.wvars] at hq
      rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hq with hq | hq
      · rw [Com.wvars] at hq
        exact Lax3Proofs.RamDriverWrites.belowVar_ne h le_rfl (by tauto)
          (List.eq_of_mem_singleton hq)
      rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hq with hq | hq
      · rw [clusterCom] at hq
        rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hq with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_descendCom cap d h hr
        rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_enumBatch
            (batName d) (cluName d) mb h hr
        rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_colourCom cap mb d h hr
        rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_killCom
            q_top cap mb d φ h hr
        rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_killListCom mb d h hr
        rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hr with hr | hr
        · exact ih (d + 1) (h.mono (Nat.le_succ d)) hr
        rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hr with hr | hr
        · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_scatterDeadPhase
            q_top cap mb d φ h hr
        · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_readbackCom
            q_top cap mb d φ h hr
      · rw [Com.wvars] at hq
        exact Lax3Proofs.RamDriverWrites.belowVar_ne h le_rfl (by tauto)
          (List.eq_of_mem_singleton hq)

/-- The array frame at the public active driver. -/
theorem belowArr_notMem_warrs_activeDriverAt
    {q_top cap mb ℓ R d : ℕ} {φ : Lax3.FirstOrder.FO 0} {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr d a) :
    a ∉ (driverAtA q_top cap mb ℓ φ
      (fun j => activeOrderPhase j R) (fun j => activeCoverPhase j cap) d).warrs := by
  rw [driverAtA]
  exact belowArr_notMem_warrs_activeDriverAux q_top cap mb ℓ R φ (ℓ - d) d h

/-- The scalar frame at the public active driver. -/
theorem belowVar_notMem_wvars_activeDriverAt
    {q_top cap mb ℓ R d : ℕ} {φ : Lax3.FirstOrder.FO 0} {y : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar d y) :
    y ∉ (driverAtA q_top cap mb ℓ φ
      (fun j => activeOrderPhase j R) (fun j => activeCoverPhase j cap) d).wvars := by
  rw [driverAtA]
  exact belowVar_notMem_wvars_activeDriverAux q_top cap mb ℓ R φ (ℓ - d) d h

variable {q_top cap mb ℓ R j : ℕ} {φ : Lax3.FirstOrder.FO 0}

theorem turnFrozen_notMem_warrs_activeDriverAt {a : String}
    (h : Lax3Proofs.RamDriverFrames.TurnFrozen j a) :
    a ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).warrs := by
  refine belowArr_notMem_warrs_activeDriverAt ?_
  rcases h with hm | ⟨c, rfl⟩ | ⟨b, hb, hname⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨j, Nat.lt_succ_self j, by tauto⟩
  · exact ⟨j, Nat.lt_succ_self j, by tauto⟩
  · rcases hname with rfl | rfl | rfl <;>
      exact ⟨b, by omega, by tauto⟩

theorem ctrName_notMem_wvars_activeDriverAt {a : ℕ} (h : a ≤ j) :
    ctrName a ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).wvars :=
  belowVar_notMem_wvars_activeDriverAt ⟨a, by omega, Or.inl rfl⟩

theorem xpName_notMem_wvars_activeDriverAt :
    xpName j ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).wvars :=
  belowVar_notMem_wvars_activeDriverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem curName_notMem_wvars_activeDriverAt :
    curName j ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).wvars :=
  belowVar_notMem_wvars_activeDriverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem mnumName_notMem_wvars_activeDriverAt {a : ℕ} (h : a ≤ j) :
    mnumName a ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).wvars :=
  belowVar_notMem_wvars_activeDriverAt ⟨a, by omega, by tauto⟩

theorem kkName_notMem_wvars_activeDriverAt :
    kkName j ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).wvars :=
  belowVar_notMem_wvars_activeDriverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem tabName_notMem_warrs_activeDriverAt (i : ℕ) :
    tabName j i ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).warrs :=
  belowArr_notMem_warrs_activeDriverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

/-- The complete nested-turn frame demanded by the active level induction. -/
theorem innerWriteFrames_active :
    InnerWriteFramesA j (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)) :=
  ⟨fun _ ha => turnFrozen_notMem_warrs_activeDriverAt ha,
    fun _ ha => ctrName_notMem_wvars_activeDriverAt ha,
    xpName_notMem_wvars_activeDriverAt,
    curName_notMem_wvars_activeDriverAt,
    fun _ ha => mnumName_notMem_wvars_activeDriverAt ha,
    kkName_notMem_wvars_activeDriverAt,
    tabName_notMem_warrs_activeDriverAt⟩

theorem cpsName_notMem_warrs_activeDriverAt :
    cpsName j ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).warrs :=
  belowArr_notMem_warrs_activeDriverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cnumName_notMem_wvars_activeDriverAt :
    cnumName j ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).wvars :=
  belowVar_notMem_wvars_activeDriverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cixName_notMem_wvars_activeDriverAt :
    cixName j ∉ (driverAtA q_top cap mb ℓ φ
      (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap) (j + 1)).wvars :=
  belowVar_notMem_wvars_activeDriverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

open Classical in
/-- The concrete recursive turn preserves the active centre-loop header. -/
theorem loopFrames_active :
    cpsName j ∉ (clusterCom q_top cap mb φ j
        (driverAtA q_top cap mb ℓ φ
          (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap)
          (j + 1))).warrs ∧
      cnumName j ∉ (clusterCom q_top cap mb φ j
        (driverAtA q_top cap mb ℓ φ
          (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap)
          (j + 1))).wvars ∧
      cixName j ∉ (clusterCom q_top cap mb φ j
        (driverAtA q_top cap mb ℓ φ
          (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap)
          (j + 1))).wvars :=
  ⟨Lax3Proofs.RamDriverWrites.cpsName_notMem_warrs_clusterCom q_top cap mb j φ
      cpsName_notMem_warrs_activeDriverAt,
    Lax3Proofs.RamDriverWrites.cnumName_notMem_wvars_clusterCom q_top cap mb j φ
      cnumName_notMem_wvars_activeDriverAt,
    Lax3Proofs.RamDriverWrites.cixName_notMem_wvars_clusterCom q_top cap mb j φ
      cixName_notMem_wvars_activeDriverAt⟩

/-! ## Concrete level semantics -/

section ConcreteLevel

variable {n B q_top cap mb ns W ℓ s Kmass R d D₁ : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
  {Kb : ℕ → ℕ} {Ki Ksc : ℕ → ℕ → ℕ} {Ks Kl : ℕ → ℕ → ℕ}

open Classical in
/-- The full recursive level with both carrier phases instantiated by their
compact active programs.  Its only remaining hypotheses are graph-theoretic
inputs and the scalar recurrence used by the root cost accounting. -/
theorem levelAtActive
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1))
    (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧ ∀ z,
          Lax3Proofs.Refine.ScatterDeadTurn.deadAtomKBlk
            σs.β z mb z z σs.t ≤ Kb z)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ z, Kb z * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j z)
    (hKsc : ∀ j < ℓ, ∀ z,
      Ki j z * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j z)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      Lax3Proofs.RamDriverRoot.turnCostSize n ns cap mb q_top j φ
        (Ksc j t) t (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ m φ ≤ Kl ℓ m)
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
        (D : ℕ → Lax3Proofs.Augmentation.Orientation mm) (i : ℕ), i ≤ R →
      Lax3Proofs.Augmentation.IsAugChain
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) D i →
      (∀ l < i, Lax3Proofs.Augmentation.GreedyFratRound (D l) (D (l + 1))) →
      Lax3Proofs.Augmentation.AugmentedDepthOneDensity D i D₁)
    (hKmass : 1 ≤ Kmass)
    (hdegree : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M))
        {D : ℕ → Lax3Proofs.Augmentation.Orientation mm}
        {d₀ k : ℕ} {pi : Equiv.Perm (Fin mm)},
      Lax3Proofs.CoverDegree.AugChainData
          (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) D pi R d₀ k →
        ∀ v : Fin mm,
          (Lax12.ColoringNumbers.wreach
            (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) pi (2 * cap) v).ncard ≤ Kmass)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      activeOrderCost d D₁ R m +
          (activeCoverCost n Kmass m +
            ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)) ≤ Kl j m) :
    ∀ j ≤ ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      LevelImplementsDA B q_top cap mb ℓ W ns j φ G O T M Gm C D
        (fun jd => activeOrderPhase jd R) (fun jd => activeCoverPhase jd cap)
        (Kl j (Lax3Proofs.Refine.MassWeight.arenaWeight n G M)) := by
  have hBns : n + ns + 1 < B := by
    have ha := hB.arena
    omega
  refine Lax3Proofs.RamDriverMemberRoot.levelAtA
    (Ko := fun _ a => activeOrderCost d D₁ R a)
    (Kc := fun _ a => activeCoverCost n Kmass a)
    hcap hmb hℓ hB hcsr hQ hbnd hcostI hKsc hKmono hKs hKbase ?_ ?_ ?_ ?_ ?_ hKl
  · intro jd hj M Gm C
    apply activeOrderPhase_weight_spec (R := R) (d := d) (D₁ := D₁)
      (Kmass := Kmass) hcsr hBns
    · exact lt_of_le_of_lt (Nat.add_le_add_right
        (Nat.add_le_add_left
          (activeOrderWidth_mono
            (Lax3Proofs.Refine.MassWeight.arenaWeight_le_root hcsr M)) n) 1) hwidthB
    · exact le_trans
        (activeOrderWidth_mono
          (Lax3Proofs.Refine.MassWeight.arenaWeight_le_root hcsr M)) hwidthW
    · exact hdeg M
    · exact hdens M
    · exact hKmass
    · exact hdegree M
  · intro jd hj M Gm C q π centre hord
    exact activeCoverPhase_spec hB hcsr hord
  · intro jd hj
    exact innerWriteFrames_active
  · intro jd hj
    exact loopFrames_active
  · intro jd i
    exact ⟨tabName_notMem_activeOrderPhase jd R jd i,
      tabName_notMem_activeCoverPhase jd cap jd i⟩

end ConcreteLevel

/-! ## Axiom audit -/

#print axioms belowArr_notMem_warrs_activeDriverAt
#print axioms innerWriteFrames_active
#print axioms loopFrames_active
#print axioms levelAtActive

end Lax3Proofs.Refine.ActiveLevel
