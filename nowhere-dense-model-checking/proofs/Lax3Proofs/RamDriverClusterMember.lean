import Lax3Proofs.RamDriverMember
import Lax3Proofs.RamDriverFrames

/-!
# The active-cover level induction

This is the level composition for `RamDriverMember.driverAtA`.  It is
separate from the landed carrier proof so that the member-driven order
and cover phases can be developed and reviewed without destabilising
that regression path.
-/

namespace Lax3Proofs.RamDriverClusterMember

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.FormulaTables Lax3Proofs.WalkDistance
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverMember
open Lax3Proofs.RamDriverFrames
open Lax3Proofs.Refine.MassMath (clusterAt)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {B n q cap mb ns W j : ℕ} {G : SimpleGraph (Fin n)}
variable {O T M Gm centre Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
variable {C : ℕ → ℕ → ℕ} {m : ℕ} {σ : Env}

/-! ## Active-cover contracts for the seven turn phases

The landed phase contracts carry `TurnPre`, whose cover is defined on
every carrier position and whose assignment is meaningful at every
vertex.  The executable walks only need the active blocks.  These
parallel contracts carry `TurnPreA`; assignment-dependent conclusions
are consequently restricted to live vertices, while dead cells are
explicitly framed.
-/

/-- The descent at an active centre. -/
def DescendStepA (B q cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n))
    (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m k K : ℕ) : Prop :=
  CsrGraph G ns O T → ∀ {d : ℕ}, WordBoundK B n d ns cap mb → k < q →
  M (centre k) ≠ 0 →
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ σ.vars (curName j) = k)
    (descendCom cap j)
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      (∃ g, σ'.arrs "wa" = arrOf mb g) ∧
      ∃ (X W : Set (Fin n)) (Alv' Gam' : ℕ → ℕ),
        (∀ v : Fin n, M (v : ℕ) ≠ 0 →
          asg (v : ℕ) = σ.vars (curName j) → ball (masked G M) cap v ⊆ X) ∧
        (W ∩ X).Nonempty ∧ W.ncard ≤ mb ∧
        (∀ v : Fin n, Alv' (v : ℕ) ≠ 0 →
          v ∈ clusterAt G M π centre cap (σ.vars (curName j))) ∧
        (∀ v : Fin n, v ∈ X →
          v ∈ clusterAt G M π centre cap (σ.vars (curName j))) ∧
        BatchData n j B G M X W Alv' Gam' σ' ∧
        PlayRec B cap G (j + 1) Alv' Gam' σ') K

/-- Padding the batch preserves an active cover. -/
def EnumStepA (B q cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n))
    (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n))
    (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ BatchData n j B G M X W Alv' Gam' σ ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ ∧ (W ∩ X).Nonempty ∧
      W.ncard ≤ mb ∧ ∃ g, σ.arrs "wa" = arrOf mb g)
    (enumBatch (batName j) (cluName j) mb)
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ PlayRec B cap G (j + 1) Alv' Gam' σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∃ w : Fin mb → Fin n, ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
        ClusterWa mb w σ') K

/-- Constructing the child colouring preserves an active cover. -/
def ColourStepA (B q cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n))
    (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n))
    (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  CsrGraph G ns O T → ∀ {d : ℕ}, WordBoundK B n d ns cap mb →
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      ClusterWa mb w σ ∧ PlayRec B cap G (j + 1) Alv' Gam' σ)
    (colourCom cap mb j)
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ' ∧ σ'.out = σ.out ∧
      σ'.vars (curName j) = σ.vars (curName j) ∧
      ∃ C' : ℕ → ℕ → ℕ,
        (∀ c < sigL cap mb (j + 1),
          σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
        (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
        colRead n C' (sigL cap mb (j + 1)) =
          stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) K

/-- Writing the killed child rows preserves an active cover. -/
def KillStepA (B q q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ)
    (C' : ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  ∀ {d : ℕ}, WordBoundK B n d ns cap mb →
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      ClusterWa mb w σ ∧
      (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
      colRead n C' (sigL cap mb (j + 1)) =
        stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ ∧ TablesSized q_top cap mb φ n σ ∧
      BaseArrs B q_top cap mb ℓ φ σ)
    (killCom q_top cap mb j φ)
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      (∀ c < sigL cap mb (j + 1),
        σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ' ∧ σ'.out = σ.out ∧
      σ'.vars (curName j) = σ.vars (curName j) ∧
      KillRowsAt q_top cap mb j φ G M Alv' X W C' σ') K

/-- Enumerating the kill set preserves an active cover. -/
def KillListStepA (B q q_top cap mb ns Ws j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ)
    (C' : ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  ∀ {d : ℕ}, WordBoundK B n d ns cap mb →
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      ClusterWa mb w σ ∧
      (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ ∧ TablesSized q_top cap mb φ n σ ∧
      KillRowsAt q_top cap mb j φ G M Alv' X W C' σ)
    (killListCom mb j)
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      (∀ c < sigL cap mb (j + 1),
        σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ' ∧ σ'.out = σ.out ∧
      σ'.vars (curName j) = σ.vars (curName j) ∧
      KillRowsAt q_top cap mb j φ G M Alv' X W C' σ' ∧
      KillListAt mb j M X W σ') K

/-- The scatter-atom fold with an active cover carried through it. -/
def ScatterStepA (B q q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ)
    (C' : ℕ → ℕ → ℕ) (bw nb K : ℕ) : Prop :=
  (∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0) →
  (∀ r : ℕ, Refine.ScatterBlock.BallBudget n r G Alv' O bw nb) →
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
      colRead n C' (sigL cap mb (j + 1)) =
        stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w ∧
      TableInvOn q_top cap mb φ G (j + 1) Alv' C' (rowDom M Alv' X W) σ ∧
      KillListAt mb j M X W σ ∧ BaseArrs B q_top cap mb ℓ φ σ)
    (foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) 0
      (tablesAt q_top cap mb φ j))
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      (∀ c < sigL cap mb (j + 1),
        σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      TableInvOn q_top cap mb φ G (j + 1) Alv' C' (rowDom M Alv' X W) σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
        ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j
            (tablesAt q_top cap mb φ j)[i])).2,
          σ'.vars (flgName j i (posOf σs (bcAtomsOf q_top
            (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≤ 1 ∧
          (σ'.vars (flgName j i (posOf σs (bcAtomsOf q_top
            (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≠ 0 ↔
            ScatVal (stepArenaP (masked G M) X w)
              (stepColoringP cap (masked G M)
                (colRead n C (sigL cap mb j)) X w) σs)) K

/-- Read back only the live vertices assigned to an active centre. -/
def ReadbackStepA (B q q_top cap mb ns Ws j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ) (m k : ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ)
    (C' : ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
      colRead n C' (sigL cap mb (j + 1)) =
        stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w ∧
      TableInvOn q_top cap mb φ G (j + 1) Alv' C' (rowDom M Alv' X W) σ ∧
      TablesSized q_top cap mb φ n σ ∧ σ.vars (curName j) = k ∧
      (∀ v : Fin n, M (v : ℕ) ≠ 0 →
        asg (v : ℕ) = σ.vars (curName j) → v ∈ X) ∧
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
        ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j
            (tablesAt q_top cap mb φ j)[i])).2,
          σ.vars (flgName j i (posOf σs (bcAtomsOf q_top
            (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≤ 1 ∧
          (σ.vars (flgName j i (posOf σs (bcAtomsOf q_top
            (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≠ 0 ↔
            ScatVal (stepArenaP (masked G M) X w)
              (stepColoringP cap (masked G M)
                (colRead n C (sigL cap mb j)) X w) σs))
    (readbackCom q_top cap mb φ j)
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ σ'.out = σ.out ∧
      σ'.vars (curName j) = σ.vars (curName j) ∧
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
        ∃ Tb Tb₀ : ℕ → ℕ, σ'.arrs (tabName j i) = arrOf n Tb ∧
          σ.arrs (tabName j i) = arrOf n Tb₀ ∧
          (∀ v : Fin n, M (v : ℕ) = 0 ∨
            asg (v : ℕ) ≠ σ.vars (curName j) → Tb (v : ℕ) = Tb₀ (v : ℕ)) ∧
          ∀ v : Fin n, M (v : ℕ) ≠ 0 →
            asg (v : ℕ) = σ.vars (curName j) →
            Tb (v : ℕ) ≤ 1 ∧
            (Tb (v : ℕ) ≠ 0 ↔
              ∃ h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧
                  DRank 1 q' (stepFml cap mb j (tablesAt q_top cap mb φ j)[i]),
                (bcOf q_top (stepFml cap mb j
                  (tablesAt q_top cap mb φ j)[i]) h).eval
                  (atomVal (stepArenaP (masked G M) X w)
                    (stepColoringP cap (masked G M)
                      (colRead n C (sigL cap mb j)) X w) v))) K

/-- The nested active driver leaves the enclosing active cover intact. -/
def InnerFramesA (B q q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ)
    (C' : ℕ → ℕ → ℕ) (inner : Com) (Kin : ℕ) : Prop :=
  Spec B (fun σ => LevelPre B n cap mb ns Ws O T (j + 1) Alv' Gam' C' σ ∧
      TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg m σ ∧
      ClusterData n mb j B G M X W w Alv' Gam' σ ∧
      TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ ∧ KillListAt mb j M X W σ ∧
      TableInvOn q_top cap mb φ G (j + 1) Alv' C' (killSet M X W) σ)
    inner
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
      (∀ c < sigL cap mb (j + 1),
        σ'.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
      σ'.vars (curName j) = σ.vars (curName j) ∧ KillListAt mb j M X W σ') Kin

/-- The syntactic frame of a nested driver, at the active-cover surface. -/
theorem innerFramesA
    {B q q_top cap mb ns Ws ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre Xoff Xmem asg : ℕ → ℕ} {mm : ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv' Gam' : ℕ → ℕ}
    {C' : ℕ → ℕ → ℕ} {wA : (ℕ → ℕ) → ℕ} {inner : Com} {Kin : ℕ → ℕ}
    (hinner : InnerAvail B q_top cap mb ns Ws ℓ j φ G O T wA inner Kin)
    (hA : ∀ a : String, TurnFrozen j a → a ∉ inner.warrs)
    (hVctr : ∀ a ≤ j, ctrName a ∉ inner.wvars)
    (hVxp : xpName j ∉ inner.wvars) (hVcur : curName j ∉ inner.wvars)
    (hVmm : ∀ a ≤ j, mnumName a ∉ inner.wvars)
    (hVkk : kkName j ∉ inner.wvars) :
    InnerFramesA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
      Xoff Xmem asg mm X W w Alv' Gam' C' inner (Kin (wA Alv')) := by
  intro σ hσ
  obtain ⟨hchild, hturn, hdata, htsz, hbarr, hplaychild, hklist, htab⟩ := hσ
  obtain ⟨σ', hrun, ⟨hlevin, -, -⟩, -⟩ :=
    (hinner Alv' Gam' C' (killSet M X W)
        (fun v hv => killSet_dead hdata.1.2.2.2.2.2.2.1 hv)
        hchild.2.2.2.2.2.2.2.2.1).run
      ⟨hchild, htsz, hbarr, hplaychild, htab⟩
  have hfa : ∀ a : String, TurnFrozen j a → σ'.arrs a = σ.arrs a :=
    fun a ha => hrun.frame_arr a (hA a ha)
  have hfv : ∀ y : String, y ∉ inner.wvars → σ'.vars y = σ.vars y :=
    fun y hy => hrun.frame_var y hy
  obtain ⟨hn', hoff', htgt', halv'', hgam'', hcol'', hAlvB', hGamB', hCB',
    hlmem', hdep', hmvar', hordmem', hpad0', hTB', Mem'', mm'', hmemA'',
    hmemV'', hmemE'', hmemBd''⟩ := hlevin
  obtain ⟨hnj, hoffj, htgtj, halvj, hgamj, hcolj, hMB, hGmB, hCB,
    hlmemj, hdepj, hmvarj, hordmemj, hpadj, hTBj, Mem, mmj, hmemA,
    hmemV, hmemE, hmemBd⟩ := hturn.level
  obtain ⟨⟨⟨Xa, hXa, hXaS, hXaB⟩, ⟨Wa, hWa, hWaS, hWaB⟩,
      ⟨Ra, hRa, hRaS, hRaB⟩, -, hAlvB, hmask, hmaskpt, -, hGamB,
      MemD, mmD, hmemAD, hmemVD, hmemED, hmemBdD⟩, hwrange⟩ := hdata
  obtain ⟨kl, kq, hklA, hkkV, hkqmb, hkllt, hklinj, hklsnd, hklcmp⟩ := hklist
  refine ⟨σ', hrun, ?_, ?_, hcol'', ?_, ?_⟩
  · refine
      { level := ?_
        play := ?_
        held := ?_ }
    · exact ⟨hn', hoff', htgt',
        (by rw [hfa _ (_root_.Or.inl (by simp))]; exact halvj),
        (by rw [hfa _ (_root_.Or.inr (_root_.Or.inr
            ⟨j, le_rfl, _root_.Or.inl rfl⟩))]; exact hgamj),
        (fun cc hcc => by
          rw [hfa _ (_root_.Or.inr (_root_.Or.inl ⟨cc, rfl⟩))]
          exact hcolj cc hcc),
        hMB, hGmB, hCB, hlmem', hdep', hmvar', hordmem', hpad0', hTB',
        Mem, mmj,
        (by rw [hfa _ (_root_.Or.inl (by simp))]; exact hmemA),
        (by rw [hfv _ (hVmm j le_rfl)]; exact hmemV), hmemE, hmemBd⟩
    · exact hturn.play.congr
        (fun a ha => hfv (ctrName a) (hVctr a (by omega)))
        (fun a ha => hfa (resName a)
          (_root_.Or.inr (_root_.Or.inr
            ⟨a, by omega, _root_.Or.inr (_root_.Or.inl rfl)⟩)))
        (fun a ha => hfa (gamName a)
          (_root_.Or.inr (_root_.Or.inr ⟨a, by omega, _root_.Or.inl rfl⟩)))
        (fun a ha => hfa (parName a)
          (_root_.Or.inr (_root_.Or.inr
            ⟨a, by omega, _root_.Or.inr (_root_.Or.inr rfl)⟩)))
    · exact
        { centre_arr := by
            rw [hfa _ (_root_.Or.inl (by simp))]
            exact hturn.held.centre_arr
          off_arr := by
            rw [hfa _ (_root_.Or.inl (by simp))]
            exact hturn.held.off_arr
          mem_arr := by
            rw [hfa _ (_root_.Or.inl (by simp))]
            exact hturn.held.mem_arr
          asg_arr := by
            rw [hfa _ (_root_.Or.inl (by simp))]
            exact hturn.held.asg_arr
          pointer := by rw [hfv _ hVxp]; exact hturn.held.pointer
          alloc := hturn.held.alloc
          pointer_lt := hturn.held.pointer_lt
          centre_lt := hturn.held.centre_lt
          cover := hturn.held.cover }
  · exact ⟨⟨⟨Xa,
        (by rw [hfa _ (_root_.Or.inl (by simp))]; exact hXa), hXaS, hXaB⟩,
      ⟨Wa, (by rw [hfa _ (_root_.Or.inl (by simp))]; exact hWa),
        hWaS, hWaB⟩,
      ⟨Ra, (by rw [hfa _ (_root_.Or.inl (by simp))]; exact hRa),
        hRaS, hRaB⟩,
      halv'', hAlvB, hmask, hmaskpt, hgam'', hGamB,
      Mem'', mm'', hmemA'', hmemV'', hmemE'', hmemBd''⟩, hwrange⟩
  · exact hfv _ hVcur
  · exact ⟨kl, kq,
      (by rw [hfa _ (_root_.Or.inl (by simp))]; exact hklA),
      (by rw [hfv _ hVkk]; exact hkkV), hkqmb, hkllt, hklinj, hklsnd, hklcmp⟩

open Classical in
/-- The seven active-cover phases compose to one active cluster turn. -/
theorem clusterStepImplementsA
    {B q q_top cap mb ns Ws ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre Xoff Xmem asg : ℕ → ℕ} {mm k : ℕ}
    {wA : (ℕ → ℕ) → ℕ} {wBk : ℕ} {inner : Com} {Kin : ℕ → ℕ}
    {bw nb Kd Ke Kc Kk Kkl Ks Kr K : ℕ}
    (hcap : cap = rhoMinus 0 q_top)
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hdes : DescendStepA B q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg mm k Kd)
    (henum : ∀ X W Alv' Gam',
      EnumStepA B q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg mm
        X W Alv' Gam' Ke)
    (hcol : ∀ X W w Alv' Gam',
      ColourStepA B q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg mm
        X W w Alv' Gam' Kc)
    (hwafr : "wa" ∉ (colourCom cap mb j).warrs)
    (hkill : ∀ X W w Alv' Gam' C',
      KillStepA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
        Xoff Xmem asg mm X W w Alv' Gam' C' Kk)
    (hwakfr : "wa" ∉ (killCom q_top cap mb j φ).warrs)
    (hklist : ∀ X W w Alv' Gam' C',
      KillListStepA B q q_top cap mb ns Ws j φ G O T M Gm C π centre
        Xoff Xmem asg mm X W w Alv' Gam' C' Kkl)
    (hfr : InnerAvail B q_top cap mb ns Ws ℓ j φ G O T wA inner Kin →
      ∀ X W w Alv' Gam' C',
        InnerFramesA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
          Xoff Xmem asg mm X W w Alv' Gam' C' inner (Kin (wA Alv')))
    (hscat : ∀ X W w Alv' Gam' C', k < q →
      RamCover.CoverOutA G M π centre cap q mm Xoff Xmem asg →
      (∀ v : Fin n, v ∈ X → v ∈ clusterAt G M π centre cap k) →
      ScatterStepA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
        Xoff Xmem asg mm X W w Alv' Gam' C' bw nb Ks)
    (hbud : ∀ M' : ℕ → ℕ, k < q →
      RamCover.CoverOutA G M π centre cap q mm Xoff Xmem asg →
      (∀ v : Fin n, M' (v : ℕ) ≠ 0 → v ∈ clusterAt G M π centre cap k) →
      ∀ r : ℕ, Refine.ScatterBlock.BallBudget n r G M' O bw nb)
    (hread : ∀ X W w Alv' Gam' C', k < q → M (centre k) ≠ 0 →
      ReadbackStepA B q q_top cap mb ns Ws j φ G O T M Gm C π centre
        Xoff Xmem asg mm k X W w Alv' Gam' C' Kr)
    (hmono : Monotone Kin)
    (hwAB : ∀ Alv' : ℕ → ℕ, k < q →
      RamCover.CoverOutA G M π centre cap q mm Xoff Xmem asg →
      (∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ clusterAt G M π centre cap k) →
      wA Alv' ≤ wBk)
    (hK : Kd + (Ke + (Kc + (Kk + (Kkl + (Kin wBk + (Ks + Kr)))))) ≤ K) :
    ClusterStepImplementsA B q_top cap mb ns Ws ℓ j φ G O T M Gm C q π centre
      Xoff Xmem asg mm k wA inner Kin K := by
  classical
  intro hkn halive _ hinner
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, htsz, hbarr, hplay, hheld, hcn⟩ := hσ
  have hturn : TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg mm σ := ⟨hlev, hplay, hheld⟩
  obtain ⟨σ₁, hr₁, hturn₁, hout₁, hc₁, hwa₁, X, W, Alv', Gam', hball,
      hWne, hWcard, hsub₁, hXcl₁, hbat₁, hplay₁⟩ :=
    (hdes hcsr hB hkn halive).run ⟨hturn, hcn⟩
  rw [hcn] at hsub₁ hXcl₁
  have hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0 :=
    fun v hv => Refine.MassAlive.clusterAt_subset_alive halive (hXcl₁ v hv)
  have hinsize : Kin (wA Alv') ≤ Kin wBk :=
    hmono (hwAB Alv' hkn hheld.cover hsub₁)
  obtain ⟨σ₂, hr₂, hturn₂, hplay₂, hout₂, hc₂, w, hdat₂, hwa₂⟩ :=
    (henum X W Alv' Gam').run ⟨hturn₁, hbat₁, hplay₁, hWne, hWcard, hwa₁⟩
  obtain ⟨σ₃, hr₃, hturn₃, hdat₃, hplay₃, hout₃, hc₃, C', hcolarr₃,
      hcolbit₃, hcolread₃⟩ :=
    (hcol X W w Alv' Gam' hcsr hB).run ⟨hturn₂, hdat₂, hwa₂, hplay₂⟩
  have htsz₃ : TablesSized q_top cap mb φ n σ₃ := (htsz.run hr₁).run hr₂ |>.run hr₃
  have hbarr₃ : BaseArrs B q_top cap mb ℓ φ σ₃ := ((hbarr.run hr₁).run hr₂).run hr₃
  have hwa₃ : ClusterWa mb w σ₃ := by
    show σ₃.arrs "wa" = _
    rw [hr₃.frame_arr "wa" hwafr]
    exact hwa₂
  obtain ⟨σₖ, hrₖ, hturnₖ, hdatₖ, hcolarrₖ, hplayₖ, houtₖ, hcₖ, hkillₖ⟩ :=
    (hkill X W w Alv' Gam' C' hB).run (σ := σ₃)
      ⟨hturn₃, hdat₃, hwa₃, hcolarr₃, hcolbit₃, hcolread₃, hplay₃, htsz₃, hbarr₃⟩
  have htszₖ : TablesSized q_top cap mb φ n σₖ := htsz₃.run hrₖ
  have hbarrₖ : BaseArrs B q_top cap mb ℓ φ σₖ := hbarr₃.run hrₖ
  have hwaₖ : ClusterWa mb w σₖ := by
    show σₖ.arrs "wa" = _
    rw [hrₖ.frame_arr "wa" hwakfr]
    exact hwa₃
  obtain ⟨σₗ, hrₗ, hturnₗ, hdatₗ, hcolarrₗ, hplayₗ, houtₗ, hcₗ, hkillₗ,
      hkllistₗ⟩ :=
    (hklist X W w Alv' Gam' C' hB).run (σ := σₖ)
      ⟨hturnₖ, hdatₖ, hwaₖ, hcolarrₖ, hplayₖ, htszₖ, hkillₖ⟩
  have hlevin : LevelPre B n cap mb ns Ws O T (j + 1) Alv' Gam' C' σₗ := by
    obtain ⟨hn₃, hoff₃, htgt₃, -, -, -, -, -, -, hmem₃, hdep₃, hm₃, hom₃,
      hpad₃, hwrd₃, -⟩ := hturnₗ.level
    obtain ⟨-, -, -, halv₃, hAlvB, -, -, hgam₃, hGamB, hmemin₃⟩ := hdatₗ.1
    exact ⟨hn₃, hoff₃, htgt₃, halv₃, hgam₃, hcolarrₗ,
      fun z hz => hAlvB z hz, fun z hz => hGamB z hz, hcolbit₃,
      hmem₃, hdep₃, hm₃, hom₃, hpad₃, hwrd₃, hmemin₃⟩
  have htszₗ : TablesSized q_top cap mb φ n σₗ := htszₖ.run hrₗ
  have hbarrₗ : BaseArrs B q_top cap mb ℓ φ σₗ := hbarrₖ.run hrₗ
  have hDdead : ∀ v : Fin n, v ∈ killSet M X W → Alv' (v : ℕ) = 0 :=
    fun v hv => killSet_dead hdatₗ.1.2.2.2.2.2.2.1 hv
  obtain ⟨σ₄, hr₄, ⟨⟨-, -, htab₄⟩, hout₄⟩, hturn₄, hdat₄, hcolarr₄,
      hc₄, hkllist₄⟩ :=
    (spec_conj ((hinner Alv' Gam' C' (killSet M X W) hDdead hcolbit₃).pre
        (fun _ h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2⟩))
      (hfr hinner X W w Alv' Gam' C')).run (σ := σₗ)
      ⟨hlevin, hturnₗ, hdatₗ, htszₗ, hbarrₗ, hplayₗ, hkllistₗ,
        hkillₗ.tableInvOn htszₗ⟩
  have htsz₄ : TablesSized q_top cap mb φ n σ₄ := htszₗ.run hr₄
  have hbarr₄ : BaseArrs B q_top cap mb ℓ φ σ₄ := hbarrₗ.run hr₄
  obtain ⟨σ₅, hr₅, hturn₅, hdat₅, hcolarr₅, htab₅, hout₅, hc₅, hflag₅⟩ :=
    (hscat X W w Alv' Gam' C' hkn hheld.cover hXcl₁ hXalive
      (hbud Alv' hkn hheld.cover hsub₁)).run (σ := σ₄)
      ⟨hturn₄, hdat₄, hcolarr₄, hcolbit₃, hcolread₃, htab₄, hkllist₄, hbarr₄⟩
  have htsz₅ : TablesSized q_top cap mb φ n σ₅ := htsz₄.run hr₅
  have hc₅₀ : σ₅.vars (curName j) = σ.vars (curName j) := by
    rw [hc₅, hc₄, hcₗ, hcₖ, hc₃, hc₂, hc₁]
  have hvis : ∀ v : Fin n, M (v : ℕ) ≠ 0 →
      asg (v : ℕ) = σ₅.vars (curName j) → v ∈ X := by
    intro v hal hv
    exact hball v hal (by rw [hv]; exact hc₅₀) (mem_ball_self _ _ _)
  obtain ⟨σ₆, hr₆, hturn₆, hout₆, hc₆, hrb₆⟩ :=
    (hread X W w Alv' Gam' C' hkn halive).run (σ := σ₅)
      ⟨hturn₅, hdat₅, hcolarr₅, hcolbit₃, hcolread₃, htab₅, htsz₅,
        hc₅₀.trans hcn, hvis, hflag₅⟩
  have hrun := hr₁.seq (hr₂.seq (hr₃.seq (hrₖ.seq (hrₗ.seq (hr₄.seq (hr₅.seq hr₆))))))
  refine ⟨σ₆, _, hrun, by omega, hturn₆.level, htsz₅.run hr₆,
    hbarrₗ.run (hr₄.seq (hr₅.seq hr₆)), hturn₆.play,
    by rw [hout₆, hout₅, hout₄, houtₗ, houtₖ, hout₃, hout₂, hout₁],
    by rw [hc₆, hc₅, hc₄, hcₗ, hcₖ, hc₃, hc₂, hc₁], fun i hi => ?_⟩
  obtain ⟨Tb, Tb₀, harr, -, -, hval⟩ := hrb₆ i hi
  refine ⟨Tb, harr, fun v hal hasgv => ?_⟩
  have hasg₅ : asg (v : ℕ) = σ₅.vars (curName j) := by
    rw [hc₅₀]
    exact hasgv
  obtain ⟨hbit, hval'⟩ := hval v hal hasg₅
  refine ⟨hbit, ?_⟩
  rw [hval']
  have hβ : TableRank q_top (tablesAt q_top cap mb φ j)[i] :=
    tableRank_of_mem_tablesAt j _ (List.getElem_mem hi)
  have hballv : ball (masked G M) cap v ⊆ X := hball v hal (by
    rw [hasg₅]
    exact hc₅₀)
  have hglue := sat_iff_eval_step (mb := mb) (j := j) hcap (A := masked G M)
    (col := colRead n C (sigL cap mb j)) w v hβ hballv
  exact ⟨fun h => hglue.mpr h.2, fun hs => ⟨hasRank_stepFml hβ, hglue.mp hs⟩⟩

open Classical in
/-- The same active turn preserves the cover and every dead or
other-turn table cell. -/
theorem clusterFramesA
    {B q q_top cap mb ns Ws ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre Xoff Xmem asg : ℕ → ℕ} {mm k : ℕ}
    {wA : (ℕ → ℕ) → ℕ} {wBk : ℕ} {inner : Com} {Kin : ℕ → ℕ}
    {bw nb Kd Ke Kc Kk Kkl Ks Kr K : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hdes : DescendStepA B q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg mm k Kd)
    (henum : ∀ X W Alv' Gam',
      EnumStepA B q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg mm
        X W Alv' Gam' Ke)
    (hcol : ∀ X W w Alv' Gam',
      ColourStepA B q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg mm
        X W w Alv' Gam' Kc)
    (hkill : ∀ X W w Alv' Gam' C',
      KillStepA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
        Xoff Xmem asg mm X W w Alv' Gam' C' Kk)
    (hkilltab : ∀ i, tabName j i ∉ (killCom q_top cap mb j φ).warrs)
    (hwakfr : "wa" ∉ (killCom q_top cap mb j φ).warrs)
    (hklisttab : ∀ i, tabName j i ∉ (killListCom mb j).warrs)
    (hklist : ∀ X W w Alv' Gam' C',
      KillListStepA B q q_top cap mb ns Ws j φ G O T M Gm C π centre
        Xoff Xmem asg mm X W w Alv' Gam' C' Kkl)
    (hA : ∀ a : String, TurnFrozen j a → a ∉ inner.warrs)
    (hVctr : ∀ a ≤ j, ctrName a ∉ inner.wvars)
    (hVxp : xpName j ∉ inner.wvars) (hVcur : curName j ∉ inner.wvars)
    (hVmm : ∀ a ≤ j, mnumName a ∉ inner.wvars)
    (hVkk : kkName j ∉ inner.wvars)
    (hscat : ∀ X W w Alv' Gam' C',
      ScatterStepA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
        Xoff Xmem asg mm X W w Alv' Gam' C' bw nb Ks)
    (hscattab : ∀ i, tabName j i ∉
      (foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) 0
        (tablesAt q_top cap mb φ j)).warrs)
    (hbud : ∀ (M' : ℕ → ℕ) (r : ℕ),
      Refine.ScatterBlock.BallBudget n r G M' O bw nb)
    (hread : ∀ X W w Alv' Gam' C', k < q → M (centre k) ≠ 0 →
      ReadbackStepA B q q_top cap mb ns Ws j φ G O T M Gm C π centre
        Xoff Xmem asg mm k X W w Alv' Gam' C' Kr)
    (hinnerTab : ∀ i, tabName j i ∉ inner.warrs)
    (hmono : Monotone Kin)
    (hwAB : ∀ Alv' : ℕ → ℕ, k < q →
      RamCover.CoverOutA G M π centre cap q mm Xoff Xmem asg →
      (∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ clusterAt G M π centre cap k) →
      wA Alv' ≤ wBk)
    (hK : Kd + (Ke + (Kc + (Kk + (Kkl + (Kin wBk + (Ks + Kr)))))) ≤ K) :
    ClusterFramesA B q_top cap mb ns Ws ℓ j φ G O T M Gm C q π centre
      Xoff Xmem asg mm k wA inner Kin K := by
  classical
  intro hkn halive hinner
  have hfr : ∀ X W w Alv' Gam' C',
      InnerFramesA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
        Xoff Xmem asg mm X W w Alv' Gam' C' inner (Kin (wA Alv')) :=
    fun _ _ _ _ _ _ => innerFramesA hinner hA hVctr hVxp hVcur hVmm hVkk
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, htsz, hbarr, hplay, hheld, hcn⟩ := hσ
  have hturn : TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg mm σ := ⟨hlev, hplay, hheld⟩
  obtain ⟨σ₁, hr₁, hturn₁, hout₁, hc₁, hwa₁, X, W, Alv', Gam', hball,
      hWne, hWcard, hsub₁, hXcl₁, hbat₁, hplay₁⟩ :=
    (hdes hcsr hB hkn halive).run ⟨hturn, hcn⟩
  rw [hcn] at hsub₁ hXcl₁
  have hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0 :=
    fun v hv => Refine.MassAlive.clusterAt_subset_alive halive (hXcl₁ v hv)
  have hinsize : Kin (wA Alv') ≤ Kin wBk :=
    hmono (hwAB Alv' hkn hheld.cover hsub₁)
  obtain ⟨σ₂, hr₂, hturn₂, hplay₂, hout₂, hc₂, w, hdat₂, hwa₂⟩ :=
    (henum X W Alv' Gam').run ⟨hturn₁, hbat₁, hplay₁, hWne, hWcard, hwa₁⟩
  obtain ⟨σ₃, hr₃, hturn₃, hdat₃, hplay₃, hout₃, hc₃, C', hcolarr₃,
      hcolbit₃, hcolread₃⟩ :=
    (hcol X W w Alv' Gam' hcsr hB).run ⟨hturn₂, hdat₂, hwa₂, hplay₂⟩
  have htsz₃ : TablesSized q_top cap mb φ n σ₃ := (htsz.run hr₁).run hr₂ |>.run hr₃
  have hbarr₃ : BaseArrs B q_top cap mb ℓ φ σ₃ := ((hbarr.run hr₁).run hr₂).run hr₃
  have hwa₃ : ClusterWa mb w σ₃ := by
    show σ₃.arrs "wa" = _
    rw [hr₃.frame_arr "wa" (wa_notMem_warrs_colourCom cap mb j)]
    exact hwa₂
  obtain ⟨σₖ, hrₖ, hturnₖ, hdatₖ, hcolarrₖ, hplayₖ, houtₖ, hcₖ, hkillₖ⟩ :=
    (hkill X W w Alv' Gam' C' hB).run (σ := σ₃)
      ⟨hturn₃, hdat₃, hwa₃, hcolarr₃, hcolbit₃, hcolread₃, hplay₃, htsz₃, hbarr₃⟩
  have htszₖ : TablesSized q_top cap mb φ n σₖ := htsz₃.run hrₖ
  have hbarrₖ : BaseArrs B q_top cap mb ℓ φ σₖ := hbarr₃.run hrₖ
  have hwaₖ : ClusterWa mb w σₖ := by
    show σₖ.arrs "wa" = _
    rw [hrₖ.frame_arr "wa" hwakfr]
    exact hwa₃
  obtain ⟨σₗ, hrₗ, hturnₗ, hdatₗ, hcolarrₗ, hplayₗ, houtₗ, hcₗ, hkillₗ,
      hkllistₗ⟩ :=
    (hklist X W w Alv' Gam' C' hB).run (σ := σₖ)
      ⟨hturnₖ, hdatₖ, hwaₖ, hcolarrₖ, hplayₖ, htszₖ, hkillₖ⟩
  have hlevin : LevelPre B n cap mb ns Ws O T (j + 1) Alv' Gam' C' σₗ := by
    obtain ⟨hn₃, hoff₃, htgt₃, -, -, -, -, -, -, hmem₃, hdep₃, hm₃, hom₃,
      hpad₃, hwrd₃, -⟩ := hturnₗ.level
    obtain ⟨-, -, -, halv₃, hAlvB, -, -, hgam₃, hGamB, hmemin₃⟩ := hdatₗ.1
    exact ⟨hn₃, hoff₃, htgt₃, halv₃, hgam₃, hcolarrₗ, hAlvB, hGamB, hcolbit₃,
      hmem₃, hdep₃, hm₃, hom₃, hpad₃, hwrd₃, hmemin₃⟩
  have htszₗ : TablesSized q_top cap mb φ n σₗ := htszₖ.run hrₗ
  have hbarrₗ : BaseArrs B q_top cap mb ℓ φ σₗ := hbarrₖ.run hrₗ
  obtain ⟨σ₄, hr₄, ⟨⟨-, -, htab₄⟩, hout₄⟩, hturn₄, hdat₄, hcolarr₄,
      hc₄, hkllist₄⟩ :=
    (spec_conj ((hinner Alv' Gam' C' (killSet M X W)
          (fun v hv => killSet_dead hdatₗ.1.2.2.2.2.2.2.1 hv) hcolbit₃).pre
        (fun _ h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2⟩))
      (hfr X W w Alv' Gam' C')).run (σ := σₗ)
      ⟨hlevin, hturnₗ, hdatₗ, htszₗ, hbarrₗ, hplayₗ, hkllistₗ,
        hkillₗ.tableInvOn htszₗ⟩
  have htsz₄ : TablesSized q_top cap mb φ n σ₄ := htszₗ.run hr₄
  have hbarr₄ : BaseArrs B q_top cap mb ℓ φ σ₄ := hbarrₗ.run hr₄
  obtain ⟨σ₅, hr₅, hturn₅, hdat₅, hcolarr₅, htab₅, hout₅, hc₅, hflag₅⟩ :=
    (hscat X W w Alv' Gam' C' hXalive (hbud Alv')).run (σ := σ₄)
      ⟨hturn₄, hdat₄, hcolarr₄, hcolbit₃, hcolread₃, htab₄, hkllist₄, hbarr₄⟩
  have htsz₅ : TablesSized q_top cap mb φ n σ₅ := htsz₄.run hr₅
  have hc₅₀ : σ₅.vars (curName j) = σ.vars (curName j) := by
    rw [hc₅, hc₄, hcₗ, hcₖ, hc₃, hc₂, hc₁]
  have hvis : ∀ v : Fin n, M (v : ℕ) ≠ 0 →
      asg (v : ℕ) = σ₅.vars (curName j) → v ∈ X := by
    intro v hal hv
    exact hball v hal (by rw [hv]; exact hc₅₀) (mem_ball_self _ _ _)
  obtain ⟨σ₆, hr₆, hturn₆, hout₆, hc₆, hrb₆⟩ :=
    (hread X W w Alv' Gam' C' hkn halive).run (σ := σ₅)
      ⟨hturn₅, hdat₅, hcolarr₅, hcolbit₃, hcolread₃, htab₅, htsz₅,
        hc₅₀.trans hcn, hvis, hflag₅⟩
  refine ⟨σ₆, _,
    hr₁.seq (hr₂.seq (hr₃.seq (hrₖ.seq (hrₗ.seq (hr₄.seq (hr₅.seq hr₆)))))),
    by omega, hturn₆.held, fun i hi Tb Tb₀ harr harr₀ v hv => ?_⟩
  obtain ⟨hfd, hfe, hfc⟩ := tabName_notMem_warrs_turn cap mb j j i
  have hframe : σ₅.arrs (tabName j i) = σ.arrs (tabName j i) := by
    rw [hr₅.frame_arr _ (hscattab i), hr₄.frame_arr _ (hinnerTab i),
      hrₗ.frame_arr _ (hklisttab i), hrₖ.frame_arr _ (hkilltab i),
      hr₃.frame_arr _ hfc, hr₂.frame_arr _ hfe, hr₁.frame_arr _ hfd]
  obtain ⟨Tb', Tb₀', harr', harr₀', hunch, -⟩ := hrb₆ i hi
  have h₁ : Tb (v : ℕ) = Tb' (v : ℕ) :=
    eq_of_arrOf_eq (harr.symm.trans harr') v.isLt
  have h₂ : Tb₀' (v : ℕ) = Tb₀ (v : ℕ) :=
    eq_of_arrOf_eq ((harr₀'.symm.trans hframe).trans harr₀) v.isLt
  rw [h₁, hunch v (by rw [hc₅₀]; exact hv), h₂]

/-- Updating an unrelated scalar preserves the active cover. -/
theorem coverHeld_setVar
    (h : CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ)
    (x : String) (hx : x ≠ xpName j) (k : ℕ) :
    CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m (σ.setVar x k) :=
  { centre_arr := by simpa using h.centre_arr
    off_arr := by simpa using h.off_arr
    mem_arr := by simpa using h.mem_arr
    asg_arr := by simpa using h.asg_arr
    pointer := by rw [vars_setVar, if_neg (Ne.symm hx)]; exact h.pointer
    alloc := h.alloc
    pointer_lt := h.pointer_lt
    centre_lt := h.centre_lt
    cover := h.cover }

theorem coverHeld_setVar_c
    (h : CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ) (k : ℕ) :
    CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m
      (σ.setVar (curName j) k) :=
  coverHeld_setVar h _ (curName_ne_xpName j j) k

theorem coverHeld_setVar_ci
    (h : CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ) (k : ℕ) :
    CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m
      (σ.setVar (cixName j) k) :=
  coverHeld_setVar h _ (cixName_ne_xpName j j) k

open Classical in
/-- One active-cover level, discharged from its two phase contracts and
its cluster-turn contracts. -/
theorem levelImplementsA
    {B q_top cap mb ℓ W ns : ℕ} {N : ℕ → ℕ} {s : ℕ}
    {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    {orderPhase coverPhase : ℕ → Com}
    {P : ℕ → Equiv.Perm (Fin n) → (ℕ → ℕ) → Prop}
    {wA : (ℕ → ℕ) → ℕ} {wB : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ}
    {Ko Kc Ks Ksf Kl : ℕ → ℕ → ℕ} {Kmass : ℕ}
    (hnB : n < B)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hℓ : ℓ = N (2 * s + 2))
    (hbase : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      masked G M = ⊥ →
      LevelImplementsDA B q_top cap mb ℓ W ns ℓ φ G O T M Gm C D
        orderPhase coverPhase (Kl ℓ (wA M)))
    (horder : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      OrderImplementsA B n W cap mb ns j O T M Gm C P (orderPhase j) (Ko j (wA M)))
    (hcover : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (q : ℕ) (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ),
      CoverImplementsA B n q cap mb ns W j G O T M Gm C π centre (coverPhase j)
        (Kc j (wA M)))
    (hstep : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (q : ℕ) (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ)
        (mm k : ℕ),
      ClusterStepImplementsA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
        Xoff Xmem asg mm k wA
        (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)) (Kl (j + 1))
        (Ks j (wB Xoff Xmem k)))
    (hframe : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (q : ℕ) (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ)
        (mm k : ℕ),
      ClusterFramesA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
        Xoff Xmem asg mm k wA
        (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)) (Kl (j + 1))
        (Ksf j (wB Xoff Xmem k)))
    (hloopfr : ∀ (j : ℕ), j < ℓ →
      cpsName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).warrs ∧
        cnumName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).wvars ∧
        cixName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).wvars)
    (hphfr : ∀ (jd i : ℕ), tabName jd i ∉ (orderPhase jd).warrs ∧
      tabName jd i ∉ (coverPhase jd).warrs)
    (hmass : ∀ (M : ℕ → ℕ) (q : ℕ) (π : Equiv.Perm (Fin n))
        (centre Xoff Xmem asg cps : ℕ → ℕ) (mm cnum : ℕ),
      P q π centre → RamCover.CoverOutA G M π centre cap q mm Xoff Xmem asg →
      Compacted q cnum mm M centre Xoff cps →
      cnum ≤ wA M ∧
        (∑ k ∈ Finset.range cnum, wB Xoff Xmem (cps k)) ≤ Kmass * (wA M + 1))
    (hK : ∀ (j : ℕ), j < ℓ → ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6))
        ≤ Kl j m) :
    ∀ (j : ℕ), j ≤ ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      LevelImplementsDA B q_top cap mb ℓ W ns j φ G O T M Gm C D
        orderPhase coverPhase (Kl j (wA M)) := by
  classical
  have key : ∀ (f j : ℕ), ℓ - j = f → j ≤ ℓ →
      ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      LevelImplementsDA B q_top cap mb ℓ W ns j φ G O T M Gm C D
        orderPhase coverPhase (Kl j (wA M)) := by
    intro f
    induction f with
    | zero =>
      intro j hf hj M Gm C D hDdead hbit
      have hje : j = ℓ := by omega
      subst hje
      intro σ hσ
      have hbot : masked G M = ⊥ :=
        eq_bot_of_playOk_full hQ
          (by rw [← hℓ]; exact playOk_of_playRec hσ.2.2.2.1)
      exact hbase M Gm C D hbot hDdead hbit σ hσ
    | succ f ih =>
      intro j hf hj M Gm C D hDdead hbit
      have hjl : j < ℓ := by omega
      have hinner : ∀ (M' Gm' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (D' : Set (Fin n)),
          (∀ v : Fin n, v ∈ D' → M' (v : ℕ) = 0) →
          (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) →
          Spec B (fun σ => LevelPre B n cap mb ns W O T (j + 1) M' Gm' C' σ ∧
              TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
              PlayRec B cap G (j + 1) M' Gm' σ ∧
              TableInvOn q_top cap mb φ G (j + 1) M' C' D' σ)
            (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))
            (fun σ σ' => LevelPostD B q_top cap mb φ G ns W O T (j + 1) M' Gm' C' D'
                σ σ' ∧ σ'.out = σ.out)
            (Kl (j + 1) (wA M')) :=
        fun M' Gm' C' D' hD' hb' => ih (j + 1) (by omega) (by omega)
          M' Gm' C' D' hD' hb'
      refine Spec.of_exists fun σ hσ => ?_
      rw [driverAtA_succ q_top cap mb ℓ φ orderPhase coverPhase hjl]
      obtain ⟨σ₁, hr₁, hlev₁, hout₁, hctr₁, hres₁, hgam₁, hpar₁, q, π, centre,
          hqn, hcentre₁, hcentrelt, hP⟩ := (horder j hjl M Gm C).run hσ.1
      have htsz₁ : TablesSized q_top cap mb φ n σ₁ := hσ.2.1.run hr₁
      have hbarr₁ : BaseArrs B q_top cap mb ℓ φ σ₁ := hσ.2.2.1.run hr₁
      have hplay₁ : PlayRec B cap G j M Gm σ₁ :=
        hσ.2.2.2.1.congr (fun a _ => hctr₁ a)
          (fun a _ => hres₁ a)
          (fun a _ => hgam₁ a)
          (fun a _ => hpar₁ a)
      obtain ⟨σ₂, hr₂, hlev₂, hout₂, hctr₂, hres₂, hgam₂, hpar₂,
          Xoff, Xmem, asg, cps, mm, cnum,
          hheld₂, hcps₂, hcnum₂, hcomp₂⟩ :=
        (hcover j hjl M Gm C q π centre).run ⟨hlev₁, hcentre₁, hcentrelt⟩
      have htsz₂ : TablesSized q_top cap mb φ n σ₂ := htsz₁.run hr₂
      have hbarr₂ : BaseArrs B q_top cap mb ℓ φ σ₂ := hbarr₁.run hr₂
      have hplay₂ : PlayRec B cap G j M Gm σ₂ :=
        hplay₁.congr (fun a _ => hctr₂ a)
          (fun a _ => hres₂ a)
          (fun a _ => hgam₂ a)
          (fun a _ => hpar₂ a)
      have hcnB : cnum < B :=
        lt_of_le_of_lt (hcomp₂.le_carrier.trans hheld₂.cover.count_le) hnB
      have hdead₂ : ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length)
          (Tb : ℕ → ℕ), σ₂.arrs (tabName j i) = arrOf n Tb →
          ∀ v : Fin n, v ∈ D →
            Tb (v : ℕ) ≤ 1 ∧
            (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G M) (colRead n C (sigL cap mb j))
              (fun _ => v) (tablesAt q_top cap mb φ j)[i]) := by
        intro i hi Tb harr v hv
        obtain ⟨Tb₀, harr₀, hbit₀, hval₀⟩ := hσ.2.2.2.2 i hi
        have hfr : σ₂.arrs (tabName j i) = σ.arrs (tabName j i) := by
          rw [hr₂.frame_arr _ (hphfr j i).2, hr₁.frame_arr _ (hphfr j i).1]
        have heq := eq_of_arrOf_eq ((harr.symm.trans hfr).trans harr₀) v.isLt
        rw [heq]
        exact ⟨hbit₀ v hv, hval₀ v hv⟩
      have hasgcps : ∀ v < n, M v ≠ 0 → ∃ k < cnum, asg v = cps k := by
        intro v hv hal
        have hlt : asg v < q := hheld₂.cover.asg_lt v hv hal
        have hself : RamCover.InCluster (masked G M) π cap (centre (asg v)) v :=
          hheld₂.cover.asg_cover v hv hal (mem_ball_self _ _ _)
        obtain ⟨p, hp₁, hp₂, -⟩ := (hheld₂.cover.block (asg v) hlt v).mpr hself
        obtain ⟨k, hk, hkc⟩ := hcomp₂.covers (asg v) hlt (by omega)
          ((Refine.MassAlive.inCluster_alive_iff hself).mp hal)
        exact ⟨k, hk, hkc.symm⟩
      obtain ⟨hfrA, hfrQ, hfrI⟩ := hloopfr j hjl
      have hbody : ∀ kk : ℕ, kk < cnum → Spec B
          (fun τ => LevelInvA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
              Xoff Xmem asg cps mm cnum D σ₂.out τ ∧ τ.vars (cixName j) = kk)
          (.seq (.assign (curName j) (.get (cpsName j) (.var (cixName j))))
            (.seq (clusterCom q_top cap mb φ j
                (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)))
              (.assign (cixName j) (.add (.var (cixName j)) (.lit 1)))))
          (fun _ τ' => LevelInvA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
              Xoff Xmem asg cps mm cnum D σ₂.out τ' ∧
            τ'.vars (cixName j) = kk + 1)
          (Ks j (wB Xoff Xmem (cps kk)) + 7) := by
        intro kk hkk
        have hpos : cps kk < q := hcomp₂.lt _ hkk
        have hcl : Spec B (fun τ => LevelPre B n cap mb ns W O T j M Gm C τ ∧
              TablesSized q_top cap mb φ n τ ∧ BaseArrs B q_top cap mb ℓ φ τ ∧
              PlayRec B cap G j M Gm τ ∧
              CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg mm τ ∧
              τ.vars (curName j) = cps kk)
            (clusterCom q_top cap mb φ j
              (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))) _
            (Ks j (wB Xoff Xmem (cps kk))) :=
          spec_conj
            (hstep j hjl M Gm C q π centre Xoff Xmem asg mm (cps kk) hpos
              (hcomp₂.alive kk hkk) hbit hinner)
            (hframe j hjl M Gm C q π centre Xoff Xmem asg mm (cps kk) hpos
              (hcomp₂.alive kk hkk) hinner)
        refine Spec.of_exists fun τ hτ => ?_
        obtain ⟨⟨hlevτ, htszτ, hbarrτ, hplayτ, hheldτ, hcpsτ, hcnumτ, houtτ, -, htabτ⟩,
          hcix⟩ := hτ
        have hcixlt : τ.vars (cixName j) < cnum := by rw [hcix]; exact hkk
        have hcixB : τ.vars (cixName j) < B := by omega
        have hposτ : cps (τ.vars (cixName j)) < q := by rw [hcix]; exact hpos
        have hread : Run B (.assign (curName j) (.get (cpsName j) (.var (cixName j)))) τ
            (τ.setVar (curName j) (cps (τ.vars (cixName j)))) 3 := by
          have h := Run.assign (B := B) (σ := τ) (x := curName j)
            (e := .get (cpsName j) (.var (cixName j)))
            (evalB_get (evalB_var hcixB)
              (by
                rw [hcpsτ]
                exact getElem?_arrOf cps
                  (lt_of_lt_of_le hcixlt (hcomp₂.le_carrier.trans hqn)))
              (lt_trans hposτ (lt_of_le_of_lt hqn hnB)))
          simpa using h
        set τ₁ := τ.setVar (curName j) (cps (τ.vars (cixName j))) with hτ₁
        have hcur₁ : τ₁.vars (curName j) = cps (τ.vars (cixName j)) := by
          rw [hτ₁, vars_setVar, if_pos rfl]
        obtain ⟨τ₂, hr, ⟨⟨hlev', htsz', hbarr', hplay', hout', hc', htab'⟩,
            hheld', hfr'⟩, hfv, hfa, -, -⟩ :=
          (hcl.frame).run (σ := τ₁)
            ⟨levelPre_setVar_c hlevτ _, tablesSized_setVar_c htszτ _ _,
              baseArrs_setVar_c hbarrτ _ _, playRec_setVar_c hplayτ _,
              coverHeld_setVar_c hheldτ _, by rw [hcur₁, hcix]⟩
        have hcix₂ : τ₂.vars (cixName j) = τ.vars (cixName j) := by
          rw [hfv _ hfrI, hτ₁, vars_setVar, if_neg (cixName_ne_curName j j)]
        have hbump : Run B (.assign (cixName j) (.add (.var (cixName j)) (.lit 1))) τ₂
            (τ₂.setVar (cixName j) (τ.vars (cixName j) + 1)) 4 := by
          have h := Run.assign (B := B) (σ := τ₂) (x := cixName j)
            (e := .add (.var (cixName j)) (.lit 1))
            (evalB_bin (evalB_var (by rw [hcix₂]; exact hcixB)) (evalB_lit (by omega))
              (by simp only [Bop.apply_add, hcix₂]; omega))
          rw [Bop.apply_add, hcix₂] at h
          simpa using h
        refine ⟨τ₂.setVar (cixName j) (τ.vars (cixName j) + 1), _,
          hread.seq (hr.seq hbump), by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · exact levelPre_setVar_ci hlev' _
        · exact tablesSized_setVar_c htsz' _ _
        · exact baseArrs_setVar_c hbarr' _ _
        · exact playRec_setVar_ci hplay' _
        · exact coverHeld_setVar_ci hheld' _
        · rw [arrs_setVar, hfa _ hfrA, hτ₁, arrs_setVar]; exact hcpsτ
        · rw [vars_setVar, if_neg (Ne.symm (cixName_ne_cnumName j j)), hfv _ hfrQ, hτ₁,
            vars_setVar, if_neg (cnumName_ne_curName j j)]
          exact hcnumτ
        · rw [out_setVar, hout', hτ₁, out_setVar]; exact houtτ
        · rw [vars_setVar, if_pos rfl]; omega
        · intro i hi Tb harr v hv
          rw [vars_setVar, if_pos rfl] at hv
          rw [arrs_setVar] at harr
          obtain ⟨Tb', harr', hcorr'⟩ := htab' i hi
          have hTb : Tb (v : ℕ) = Tb' (v : ℕ) :=
            eq_of_arrOf_eq (harr.symm.trans harr') v.isLt
          rcases hv with hdv | ⟨hal, k, hk, hkv⟩
          · obtain ⟨Tb₀, harr₀⟩ := htszτ.get j hi
            have hdead : M (v : ℕ) = 0 := hDdead v hdv
            have hsame := hfr' i hi Tb' Tb₀ harr'
              (by rw [hτ₁, arrs_setVar]; exact harr₀) v (Or.inl hdead)
            rw [hTb, hsame]
            exact htabτ i hi Tb₀ harr₀ v (Or.inl hdv)
          · rcases Nat.lt_or_ge k (τ.vars (cixName j)) with hlt | hge
            · obtain ⟨Tb₀, harr₀⟩ := htszτ.get j hi
              have hne : asg (v : ℕ) ≠ τ₁.vars (curName j) := by
                rw [hcur₁, hkv]
                exact fun he => absurd (hcomp₂.inj (by omega) hcixlt he) (by omega)
              have hsame := hfr' i hi Tb' Tb₀ harr'
                (by rw [hτ₁, arrs_setVar]; exact harr₀) v (Or.inr hne)
              rw [hTb, hsame]
              exact htabτ i hi Tb₀ harr₀ v (Or.inr ⟨hal, k, hlt, hkv⟩)
            · have hkeq : k = τ.vars (cixName j) := by omega
              rw [hTb]
              exact hcorr' v hal (by rw [hcur₁, hkv, hkeq])
        · rw [vars_setVar, if_pos rfl]; omega
      obtain ⟨σ₄, hr₄, hI₄, hcn₄⟩ :=
        (Refine.SigmaLoop.forRangeZeroSum (cixName j) (cnumName j)
          (LevelInvA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre Xoff Xmem
            asg cps mm cnum D σ₂.out) cnum
          (fun kk => Ks j (wB Xoff Xmem (cps kk)) + 7) hcnB
          (fun _ hτ => hτ.2.2.2.2.2.2.2.2.1) (fun _ hτ => hτ.2.2.2.2.2.2.1)
          hbody).run (σ := σ₂)
          ⟨levelPre_setVar_ci hlev₂ 0, tablesSized_setVar_c htsz₂ _ 0,
            baseArrs_setVar_c hbarr₂ _ 0, playRec_setVar_ci hplay₂ 0,
            coverHeld_setVar_ci hheld₂ 0, by simpa using hcps₂,
            by rw [vars_setVar, if_neg (Ne.symm (cixName_ne_cnumName j j))]; exact hcnum₂,
            by simp, by simp, by
              intro i hi Tb harr v hv
              rw [arrs_setVar] at harr
              rcases hv with hdv | ⟨-, k, hk, -⟩
              · exact hdead₂ i hi Tb harr v hdv
              · rw [vars_setVar, if_pos rfl] at hk; omega⟩
      have htabinv : TableInvOn q_top cap mb φ G j M C
          ({v : Fin n | M (v : ℕ) ≠ 0} ∪ D) σ₄ := by
        intro i hi
        obtain ⟨Tb, harr⟩ := hI₄.2.1.get j hi
        have hrow : ∀ v : Fin n, v ∈ ({v : Fin n | M (v : ℕ) ≠ 0} ∪ D) →
            Tb (v : ℕ) ≤ 1 ∧
            (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G M) (colRead n C (sigL cap mb j))
              (fun _ => v) (tablesAt q_top cap mb φ j)[i]) := by
          rintro v (hal | hdv)
          · obtain ⟨k, hk, hkv⟩ := hasgcps (v : ℕ) v.isLt hal
            exact hI₄.2.2.2.2.2.2.2.2.2 i hi Tb harr v
              (Or.inr ⟨hal, k, by rw [hcn₄]; exact hk, hkv⟩)
          · exact hI₄.2.2.2.2.2.2.2.2.2 i hi Tb harr v (Or.inl hdv)
        exact ⟨Tb, harr, fun v hv => (hrow v hv).1, fun v hv => (hrow v hv).2⟩
      obtain ⟨hturns, hbs⟩ := hmass M q π centre Xoff Xmem asg cps mm cnum
        hP hheld₂.cover hcomp₂
      have hsum : (∑ kk ∈ Finset.range cnum,
          (Ks j (wB Xoff Xmem (cps kk)) + 7 + 4)) =
          ∑ kk ∈ Finset.range cnum, (Ks j (wB Xoff Xmem (cps kk)) + 11) :=
        Finset.sum_congr rfl fun _ _ => by omega
      have hcost : Ko j (wA M) + (Kc j (wA M) +
            ((∑ kk ∈ Finset.range cnum, (Ks j (wB Xoff Xmem (cps kk)) + 11)) + 6))
          ≤ Kl j (wA M) :=
        hK j hjl (wA M) cnum hturns (fun c => wB Xoff Xmem (cps c)) hbs
      refine ⟨σ₄, _, hr₁.seq (hr₂.seq hr₄), ?_,
        ⟨hI₄.1, hI₄.2.1, htabinv⟩,
        by rw [hI₄.2.2.2.2.2.2.2.1, hout₂, hout₁]⟩
      rw [hsum]
      omega
  exact fun j hj => key (ℓ - j) j rfl hj

end Lax3Proofs.RamDriverClusterMember
