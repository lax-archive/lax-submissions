import Lax3Proofs.RamDriverRoot
import Lax3Proofs.RamDriverMemberPhases
import Lax3Proofs.RamCoverActiveMass

/-!
# Active-cover root integration

This file is the active-cover counterpart of the turn integration in
`RamDriverRoot`.  The phase walks are the same executable walks, but their
contracts only require the live centre prefix and live assignment cells.
-/

namespace Lax3Proofs.RamDriverMemberRoot

open Finset
open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamCover
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBot
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverMember
open Lax3Proofs.RamDriverClusterMember
open Lax3Proofs.Refine.MassMath (blockSize clusterAt)
open Lax3Proofs.Refine.MassWeight (arenaWeight blockWeight)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {n : ℕ}
variable {G H : SimpleGraph (Fin n)}
variable {M O T centre Xoff Xmem asg : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)}
variable {r q m k cap mm q_top mb j ns B : ℕ}
variable {φ : Lax3.FirstOrder.FO 0} {Kb : ℕ → ℕ}

/-! ## Block mathematics at an active cover -/

/-- Every offset in the active prefix lies below the arena pointer. -/
theorem off_le_arenaA
    (h : CoverOutA G M π centre r q m Xoff Xmem asg) {t : ℕ} (ht : t ≤ q) :
    Xoff t ≤ m := by
  have key : ∀ d t, t + d = q → Xoff t ≤ Xoff q := by
    intro d
    induction d with
    | zero =>
        intro t htd
        rw [show t = q by omega]
    | succ d ih =>
        intro t htd
        exact le_trans (h.mono t (by omega)) (ih (t + 1) (by omega))
  rw [← h.last]
  exact key (q - t) t (by omega)

/-- A member read from an active block is a carrier vertex. -/
theorem mem_lt_of_coverOutA
    (h : CoverOutA G M π centre r q m Xoff Xmem asg) {k p : ℕ}
    (hk : k < q) (_hp : Xoff k ≤ p) (hp' : p < Xoff (k + 1)) : Xmem p < n :=
  h.mem_lt p (lt_of_lt_of_le hp' (off_le_arenaA h (by omega)))

/-- The weight of an active cluster is at most the weight of its stored block. -/
theorem wsum_clusterAt_le_slotWeightA (f : Fin n → ℕ)
    (h : CoverOutA G M π centre r q m Xoff Xmem asg) {k : ℕ} (hk : k < q) :
    Refine.MassWeight.wsum f (clusterAt G M π centre r k) ≤
      Refine.MassWeight.slotWeight n f Xoff Xmem k := by
  classical
  have hqn := h.count_le
  have hn : 0 < n := by omega
  have hlt : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact mem_lt_of_coverOutA h hk hp.1 hp.2
  set g : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hg
  have hgval : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)),
      ((g p : Fin n) : ℕ) = Xmem p :=
    fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hsub : clusterAt G M π centre r k ⊆
      ↑((Finset.Ico (Xoff k) (Xoff (k + 1))).image g) := by
    intro z hz
    obtain ⟨p, hp₁, hp₂, hp₃⟩ := (h.block k hk (z : ℕ)).mpr hz
    have hp : p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)) :=
      Finset.mem_Ico.mpr ⟨hp₁, hp₂⟩
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨p, hp, Fin.ext (by rw [hgval p hp, hp₃])⟩)
  calc
    Refine.MassWeight.wsum f (clusterAt G M π centre r k)
        ≤ Refine.MassWeight.wsum f
            ↑((Finset.Ico (Xoff k) (Xoff (k + 1))).image g) :=
          Refine.MassWeight.wsum_mono f hsub
    _ = ∑ v ∈ (Finset.Ico (Xoff k) (Xoff (k + 1))).image g, f v :=
          Refine.MassWeight.wsum_coe_finset _ _
    _ ≤ ∑ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)), f (g p) :=
          Refine.MassWeight.sum_image_le_sum _ _ _
    _ = Refine.MassWeight.slotWeight n f Xoff Xmem k := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Refine.MassWeight.natW_val f (hlt p hp)]
          exact congrArg f (Fin.ext (hgval p hp))

/-- An active cluster has no more vertices than its stored block has slots. -/
theorem ncard_clusterAt_le_blockSizeA
    (h : CoverOutA G M π centre r q m Xoff Xmem asg) {k : ℕ} (hk : k < q) :
    (clusterAt G M π centre r k).ncard ≤ blockSize Xoff k := by
  classical
  have hqn := h.count_le
  have hn : 0 < n := by omega
  have hlt : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact mem_lt_of_coverOutA h hk hp.1 hp.2
  set f : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hf
  have hfval : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)),
      ((f p : Fin n) : ℕ) = Xmem p := fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hsub : clusterAt G M π centre r k ⊆
      f '' ↑(Finset.Ico (Xoff k) (Xoff (k + 1))) := by
    intro z hz
    obtain ⟨p, hp₁, hp₂, hp₃⟩ := (h.block k hk (z : ℕ)).mpr hz
    have hp : p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)) :=
      Finset.mem_Ico.mpr ⟨hp₁, hp₂⟩
    exact ⟨p, Finset.mem_coe.mpr hp, Fin.ext (by rw [hfval p hp, hp₃])⟩
  calc
    (clusterAt G M π centre r k).ncard
        ≤ (f '' ↑(Finset.Ico (Xoff k) (Xoff (k + 1)))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (↑(Finset.Ico (Xoff k) (Xoff (k + 1))) : Set ℕ).ncard :=
          Set.ncard_image_le (Set.toFinite _)
    _ = blockSize Xoff k := by
          rw [Set.ncard_coe_finset, Nat.card_Ico, blockSize]

/-- The active-cover form of the descent weight comparison. -/
theorem arenaWeight_le_blockWeightA (H : SimpleGraph (Fin n))
    (h : CoverOutA G M π centre r q m Xoff Xmem asg) {k : ℕ} (hk : k < q)
    {M' : ℕ → ℕ}
    (hsub : ∀ v : Fin n, M' (v : ℕ) ≠ 0 → v ∈ clusterAt G M π centre r k) :
    arenaWeight n H M' ≤ blockWeight n H Xoff Xmem k :=
  le_trans (Refine.MassWeight.wsum_mono _ hsub)
    (wsum_clusterAt_le_slotWeightA _ h hk)

/-- The readback scan of an active block fits its block-weight slot. -/
theorem rbCost_block_le_weightA
    (hout : CoverOutA G M π centre cap q mm Xoff Xmem asg) (hk : k < q) :
    RamDriverBase.rbCost q_top cap mb φ j (Xoff (k + 1) - Xoff k) ≤
      RamDriverBase.rbCost q_top cap mb φ j (blockWeight n G Xoff Xmem k) := by
  apply RamDriverBase.rbCost_mono
  change blockSize Xoff k ≤ blockWeight n G Xoff Xmem k
  exact Refine.MassWeight.blockSize_le_blockWeight G Xoff Xmem
    (fun p hp hp' => mem_lt_of_coverOutA hout hk hp hp')

/-- A ball supported inside one active cluster is paid by that block. -/
theorem ballBudget_clusterA {G : SimpleGraph (Fin n)} {ns : ℕ}
    {M O T centre Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {cap q mm k : ℕ}
    (hcsr : CsrGraph G ns O T)
    (hout : CoverOutA G M π centre cap q mm Xoff Xmem asg) (hk : k < q)
    {M' : ℕ → ℕ}
    (hsub : ∀ v : Fin n, M' (v : ℕ) ≠ 0 → v ∈ clusterAt G M π centre cap k)
    (r : ℕ) :
    Refine.ScatterBlock.BallBudget n r G M' O
      (min (Refine.MassWeight.blockRowSum O Xoff Xmem k) ns)
      (min (blockSize Xoff k) n) := by
  classical
  have hlt : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact mem_lt_of_coverOutA hout hk hp.1 hp.2
  have himg : ∀ v ∈ (Finset.Ico (Xoff k) (Xoff (k + 1))).image Xmem, v < n := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact hlt p hp
  intro s _
  refine ⟨(Finset.Ico (Xoff k) (Xoff (k + 1))).image Xmem, ?_,
    le_min ?_ ?_, le_min ?_ ?_⟩
  · intro v hv hM' _
    obtain ⟨p, hp₁, hp₂, hp₃⟩ := (hout.block k hk v).mpr (hsub ⟨v, hv⟩ hM')
    exact Finset.mem_image.mpr ⟨p, Finset.mem_Ico.mpr ⟨hp₁, hp₂⟩, hp₃⟩
  · rw [Refine.MassWeight.blockRowSum,
      ← Finset.sum_fiberwise_of_maps_to (g := Xmem)
        (fun p hp => Finset.mem_image_of_mem Xmem hp)
        (fun p => Lax13Proofs.Reasoning.Lib.Csr.rowLen O (Xmem p))]
    refine Finset.sum_le_sum fun v hv => ?_
    obtain ⟨p, hp, hgp⟩ := Finset.mem_image.mp hv
    calc
      Lax13Proofs.Reasoning.Lib.Csr.rowLen O v =
          Lax13Proofs.Reasoning.Lib.Csr.rowLen O (Xmem p) := by rw [hgp]
      _ ≤ ∑ z ∈ (Finset.Ico (Xoff k) (Xoff (k + 1))).filter
            (fun z => Xmem z = v), Lax13Proofs.Reasoning.Lib.Csr.rowLen O (Xmem z) :=
        Finset.single_le_sum (f := fun z => Lax13Proofs.Reasoning.Lib.Csr.rowLen O (Xmem z))
          (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨hp, hgp⟩)
  · exact hcsr.sum_rowLen_le himg
  · refine le_trans Finset.card_image_le ?_
    rw [Nat.card_Ico, blockSize]
  · refine le_trans (Finset.card_le_card
      (fun v hv => Finset.mem_range.mpr (himg v hv))) ?_
    rw [Finset.card_range]

/-- The active-cover form of the concrete scatter bound. -/
theorem scatterBnd_blockA (hcsr : RamElim.CsrSimple G ns O T)
    (hout : CoverOutA G M π centre cap q mm Xoff Xmem asg) (hk : k < q)
    (X : Set (Fin n))
    (hXcl : ∀ v : Fin n, v ∈ X → v ∈ clusterAt G M π centre cap k)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧ ∀ z,
          Refine.ScatterDeadTurn.deadAtomKBlk σs.β z mb z z σs.t ≤ Kb z) :
    ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          Refine.ScatterDeadTurn.deadAtomKX σs.β n X.ncard mb
              (min (Refine.MassWeight.blockRowSum O Xoff Xmem k) ns)
              (min (blockSize Xoff k) n) σs.t
            ≤ Kb (blockWeight n G Xoff Xmem k) := by
  intro β hβ σs hσs
  have hmem : ∀ p, Xoff k ≤ p → p < Xoff (k + 1) → Xmem p < n :=
    fun p hp hp' => mem_lt_of_coverOutA hout hk hp hp'
  have hXcard : X.ncard ≤ (clusterAt G M π centre cap k).ncard :=
    Set.ncard_le_ncard hXcl (Set.toFinite _)
  have hcluster : (clusterAt G M π centre cap k).ncard ≤ blockSize Xoff k :=
    ncard_clusterAt_le_blockSizeA hout hk
  have hsize := Refine.MassWeight.blockSize_le_blockWeight G Xoff Xmem hmem
  have hxb : X.ncard ≤ blockWeight n G Xoff Xmem k :=
    le_trans hXcard (le_trans hcluster hsize)
  have hrow : Refine.MassWeight.blockRowSum O Xoff Xmem k ≤
      blockWeight n G Xoff Xmem k := by
    rw [Refine.MassWeight.blockRowSum_eq_blockDegSum hcsr hmem]
    exact Refine.MassWeight.blockDegSum_le_blockWeight G Xoff Xmem hmem
  have hbw : min (Refine.MassWeight.blockRowSum O Xoff Xmem k) ns ≤
      blockWeight n G Xoff Xmem k := le_trans (Nat.min_le_left _ _) hrow
  have hnb : min (blockSize Xoff k) n ≤ blockWeight n G Xoff Xmem k :=
    le_trans (Nat.min_le_left _ _) hsize
  refine ⟨(hbnd β hβ σs hσs).1, (hbnd β hβ σs hσs).2.1, ?_⟩
  exact le_trans (Refine.ScatterDeadTurn.deadAtomKX_le_blk σs.β _ _ _ _ _ _)
    (le_trans (Refine.ScatterDeadTurn.deadAtomKBlk_mono σs.β mb σs.t hxb hbw hnb)
      ((hbnd β hβ σs hσs).2.2 _))

/-! ## Concrete active cluster turns -/

/-- The syntactic frame obligations one nested active driver owes its parent turn. -/
structure InnerWriteFramesA (j : ℕ) (inner : Com) : Prop where
  frozen : ∀ a : String, RamDriverFrames.TurnFrozen j a → a ∉ inner.warrs
  ctr : ∀ a ≤ j, ctrName a ∉ inner.wvars
  xp : xpName j ∉ inner.wvars
  cur : curName j ∉ inner.wvars
  mnum : ∀ a ≤ j, mnumName a ∉ inner.wvars
  kk : kkName j ∉ inner.wvars
  tab : ∀ i, tabName j i ∉ inner.warrs

open Classical in
/-- All seven active phase walks compose at the real block-weight cost. -/
theorem clusterStepAtA
    {B q q_top cap mb ℓ W ns Kmass j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre Xoff Xmem asg : ℕ → ℕ} {mm k : ℕ}
    {orderPhase coverPhase : ℕ → Com} {Kin : ℕ → ℕ} {Ks : ℕ}
    {Kb Ki Ksc : ℕ → ℕ}
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBoundK B n Kmass ns cap mb) (hcsr : RamElim.CsrSimple G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧ ∀ z,
          Refine.ScatterDeadTurn.deadAtomKBlk σs.β z mb z z σs.t ≤ Kb z)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ z, Kb z * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki z)
    (hKsc : ∀ z, Ki z * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc z)
    (hmono : Monotone Kin)
    (hinner : InnerWriteFramesA j
      (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)))
    (hK : RamDriverRoot.turnCostSize n ns cap mb q_top j φ
      (Ksc (blockWeight n G Xoff Xmem k)) (blockWeight n G Xoff Xmem k)
      (Kin (blockWeight n G Xoff Xmem k)) ≤ Ks) :
    ClusterStepImplementsA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
      Xoff Xmem asg mm k (arenaWeight n G)
      (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)) Kin Ks :=
  clusterStepImplementsA
    (bw := min (Refine.MassWeight.blockRowSum O Xoff Xmem k) ns)
    (nb := min (blockSize Xoff k) n) hcap hcsr.csr hB
    (RamDriverDescend.descendStepA hcsr hmb hjl le_rfl)
    (fun _ _ _ _ => RamDriverMemberPhases.enumStepA hB le_rfl)
    (fun _ _ _ _ _ => RamDriverMemberPhases.colourStepA le_rfl)
    (RamDriverFrames.wa_notMem_warrs_colourCom cap mb j)
    (fun _ _ _ _ _ _ => RamDriverMemberPhases.killStepA)
    (RamDriverRoot.wa_notMem_warrs_killCom q_top cap mb j φ)
    (fun _ _ _ _ _ _ => RamDriverMemberPhases.killListStepA)
    (fun havail _ _ _ _ _ _ => innerFramesA havail hinner.frozen hinner.ctr
      hinner.xp hinner.cur hinner.mnum hinner.kk)
    (fun X _ _ _ _ _ hk hout hXcl =>
      RamDriverMemberPhases.scatterStepA hcsr.csr hB
        (scatterBnd_blockA hcsr hout hk X hXcl hbnd)
        (fun β hβ => hcostI β hβ _) (hKsc _))
    (fun _ hk hout hsub r => ballBudget_clusterA hcsr.csr hout hk hsub r)
    (fun _ _ _ _ _ _ hk halive =>
      RamDriverMemberPhases.readbackStepA hB.one_lt hB.n_lt hk halive
        (fun hout => rbCost_block_le_weightA hout hk))
    hmono
    (fun _ hk hout hsub => arenaWeight_le_blockWeightA G hout hk hsub)
    hK

open Classical in
/-- The concrete active turn preserves the cover and every unowned table row. -/
theorem clusterFramesAtA
    {B q q_top cap mb ℓ W ns Kmass j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre Xoff Xmem asg : ℕ → ℕ} {mm k : ℕ}
    {orderPhase coverPhase : ℕ → Com} {Kin : ℕ → ℕ}
    {Kb Ki Ksc : ℕ → ℕ}
    (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBoundK B n Kmass ns cap mb) (hcsr : RamElim.CsrSimple G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧ ∀ z,
          Refine.ScatterDeadTurn.deadAtomKBlk σs.β z mb z z σs.t ≤ Kb z)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ z, Kb z * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki z)
    (hKsc : ∀ z, Ki z * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc z)
    (hmono : Monotone Kin)
    (hinner : InnerWriteFramesA j
      (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))) :
    ClusterFramesA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
      Xoff Xmem asg mm k (arenaWeight n G)
      (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)) Kin
      (RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc (n + ns))
        (blockWeight n G Xoff Xmem k) (Kin (blockWeight n G Xoff Xmem k))) :=
  clusterFramesA hcsr.csr hB
    (RamDriverDescend.descendStepA hcsr hmb hjl le_rfl)
    (fun _ _ _ _ => RamDriverMemberPhases.enumStepA hB le_rfl)
    (fun _ _ _ _ _ => RamDriverMemberPhases.colourStepA le_rfl)
    (fun _ _ _ _ _ _ => RamDriverMemberPhases.killStepA)
    (fun i => Refine.KillPass.notMem_warrs_killCom
      (fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1)
      (fun i' => RamDriverBase.tabName_ne_succ j i i')
      (fun hc => RamDriverBot.not_ext_b_tabName j i (RamDriverCompose.ext_b_of_ext_bb hc)))
    (RamDriverRoot.wa_notMem_warrs_killCom q_top cap mb j φ)
    (fun i => RamDriverWrites.notMem_warrs_killListCom
      (by simp [tabName, klName, String.ext_iff]))
    (fun _ _ _ _ _ _ => RamDriverMemberPhases.killListStepA)
    hinner.frozen hinner.ctr hinner.xp hinner.cur hinner.mnum hinner.kk
    (fun X _ _ _ _ _ =>
      RamDriverMemberPhases.scatterStepA hcsr.csr hB
        (fun β hβ σs hσs =>
          ⟨(hbnd β hβ σs hσs).1, (hbnd β hβ σs hσs).2.1,
            le_trans (Refine.ScatterDeadTurn.deadAtomKX_le_blk σs.β _ _ _ _ _ _)
              (le_trans (Refine.ScatterDeadTurn.deadAtomKBlk_mono σs.β mb σs.t
                (le_trans (RamDriverRoot.ncard_le_carrier X) (Nat.le_add_right n ns))
                (Nat.le_add_left ns n) (Nat.le_add_right n ns))
                ((hbnd β hβ σs hσs).2.2 _))⟩)
        (fun β hβ => hcostI β hβ _) (hKsc _))
    (fun i => RamDriverWrites.tabName_notMem_warrs_scatterDeadPhase j j i
      (fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1) _ 0
      (fun _ hβ => hβ))
    (Refine.ScatterDeadPass.ballBudget_carrier hcsr.csr)
    (fun _ _ _ _ _ _ hk halive =>
      RamDriverMemberPhases.readbackStepA hB.one_lt hB.n_lt hk halive
        (fun hout => rbCost_block_le_weightA hout hk))
    hinner.tab hmono
    (fun _ hk hout hsub => arenaWeight_le_blockWeightA G hout hk hsub)
    le_rfl

/-! ## The active level

The two outer phases remain parameters here because their active-set
executables are the next engine boundary.  Everything below those phases is
now concrete: the base case, all seven cluster subphases, the recursive
descent, and the weighted active-cover mass argument. -/

section Level

variable {B q_top cap mb ns W ℓ s Kmass : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
  {Kb : ℕ → ℕ} {Ki Ksc : ℕ → ℕ → ℕ}
  {Ko Kc Ks Kl : ℕ → ℕ → ℕ}
  {orderPhase coverPhase : ℕ → Com}

open Classical in
/-- Every active level, with the concrete cluster engine and active-cover
mass theorem plugged in.  The remaining semantic hypotheses are precisely
the active ordering and active cover phase contracts. -/
theorem levelAtA
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1))
    (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb)
    (hcsr : RamElim.CsrSimple G ns O T)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧ ∀ z,
          Refine.ScatterDeadTurn.deadAtomKBlk σs.β z mb z z σs.t ≤ Kb z)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ z, Kb z * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j z)
    (hKsc : ∀ j < ℓ, ∀ z,
      Ki j z * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j z)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ
        (Ksc j t) t (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, RamDriverBot.baseCost q_top cap mb ℓ m φ ≤ Kl ℓ m)
    (horder : ∀ j < ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      OrderImplementsA B n W cap mb ns j O T M Gm C
        (RamCoverActiveMass.ActiveOrderP G cap Kmass) (orderPhase j)
        (Ko j (arenaWeight n G M)))
    (hcover : ∀ j < ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (q : ℕ) (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ),
      RamCoverActiveMass.ActiveOrderP G cap Kmass M q π centre →
        CoverImplementsA B n q cap mb ns W j G O T M Gm C π centre (coverPhase j)
          (Kc j (arenaWeight n G M)))
    (hinner : ∀ j < ℓ, InnerWriteFramesA j
      (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)))
    (hloopfr : ∀ j < ℓ,
      cpsName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).warrs ∧
        cnumName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).wvars ∧
        cixName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).wvars)
    (hphfr : ∀ jd i : ℕ, tabName jd i ∉ (orderPhase jd).warrs ∧
      tabName jd i ∉ (coverPhase jd).warrs)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6))
        ≤ Kl j m) :
    ∀ j ≤ ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      LevelImplementsDA B q_top cap mb ℓ W ns j φ G O T M Gm C D
        orderPhase coverPhase (Kl j (arenaWeight n G M)) :=
  RamDriverClusterMember.levelImplementsA
    (Ksf := fun j t => RamDriverRoot.turnCostSize n ns cap mb q_top j φ
      (Ksc j (n + ns)) t (Kl (j + 1) t))
    hB.n_lt hQ hℓ
    (fun M Gm C D hbot hDdead hbit => by
      rw [driverAtA_bot]
      exact (RamDriverCompose.baseImplementsD
        (le_trans (RamDriverBot.baseCost_mono q_top cap mb ℓ φ
          (Refine.MassWeight.arenaSize_le_arenaWeight n G M)) (hKbase _))
        hB hbot hDdead hbit).pre
          (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩))
    horder hcover
    (fun j hj M Gm C q π centre Xoff Xmem asg mm k =>
      clusterStepAtA (M := M) (Gm := Gm) (C := C) (q := q) (π := π)
        (centre := centre) (Xoff := Xoff) (Xmem := Xmem) (asg := asg) (mm := mm) (k := k)
        hcap hmb hj hB hcsr (hbnd j hj) (hcostI j hj) (hKsc j hj)
        (hKmono (j + 1)) (hinner j hj) (hKs j hj _))
    (fun j hj M Gm C q π centre Xoff Xmem asg mm k =>
      clusterFramesAtA (M := M) (Gm := Gm) (C := C) (q := q) (π := π)
        (centre := centre) (Xoff := Xoff) (Xmem := Xmem) (asg := asg) (mm := mm) (k := k)
        hmb hj hB hcsr (hbnd j hj) (hcostI j hj) (hKsc j hj)
        (hKmono (j + 1)) (hinner j hj))
    hloopfr hphfr
    (fun _ _ _ _ _ _ _ _ _ _ hord hout hcomp =>
      RamCoverActiveMass.mass_of_active_order G hord hout hcomp)
    hKl

#print axioms levelAtA

end Level

end Lax3Proofs.RamDriverMemberRoot
