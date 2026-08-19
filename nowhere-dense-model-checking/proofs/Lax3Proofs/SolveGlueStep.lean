import Lax3Proofs.SolveFrameBridge

/-!
# F6c8 (part 1) — the frame step's skeleton: guard, leaf branch, and the
cover seam, discharged

`SolveFrameBridge.solveSpec_closed` consumes `FrameStepAll` — residual 1,
the frame body. This file discharges everything *structural* about that
residual and leaves the genuinely per-centre remainder as two precisely
named propositions, so the continuation map narrows:

* **`guardBody`** — the canonical frame body's shape: the machine leaf
  test `nS = 0` (which *is* edgelessness, `ArenaStW.ns_zero_iff_bot`)
  guarding the canonical bottom block (`canonBotB`) against the else
  branch. `frameStep_of_else` discharges the whole guard mechanism —
  the leaf branch through the landed `blockSpec_leaf_guard`, the name
  side conditions through `SolveFrameBridge` §1, the ownership of the
  conditional, the off-diagonal vacuity, and the budget `max`
  bookkeeping — reducing `FrameStep` to **`FrameElse`**: the else
  branch's contract on *edged* arenas of the diagonal only.

* **`coverElse`** — the else branch's shape: the cover stage in front
  of the centre loop. `frameElse_of_cover_loop` discharges the seam —
  the landed `CoverStageSpec` (its `Spec` consumed verbatim), the
  scratch-descriptor plumbing (`Scr` is length-only, so it crosses the
  cover by `specArrsLength` alone), the table-allocation survival, and
  the write discipline of the composition — reducing `FrameElse` to
  **`CentreLoop`**: from the cover's outputs (`CtrArr` at
  `Driver.centre`, `ClusterCsr` at `Driver.cluster`) to the level's
  `BlockPost`, the per-centre pipeline.

* **`frameStepAll_of_cover_loop`** — the headline: `FrameStepAll`
  (verbatim `SolveFrameBridge`'s residual 1, for the canonical body
  `guardBody (coverElse covC loopB)`) from the two named residuals
  quantified per admissible input (`CoverAllIn`, `CentreLoopAll`) plus
  hypotheses only of the kinds `solveSpec_closed` itself takes: the
  per-level word bounds at `mcB` (now needed at every non-bottom level,
  since every level's leaf branch runs the bottom block), the per-level
  scratch descriptor, the budget fits, and the name pools.

The remaining content of residual 1 is therefore exactly:

1. **`CoverAllIn`** — `CoverStageSpec` per admissible level arena: the
   GKS sweep (`SolveChainCover`'s named obligation, unchanged in shape,
   here pinned to the canonical names and the diagonal's arenas).
2. **`CentreLoopAll`** — the centre loop: restrict → BFS → supports →
   profilesMS → isolate → the inner block (through the windowed
   contract) → scatter → readback, per centre, from the cover's two
   output regions. All stage lifts are landed
   (`SolveChainBot`/`SolveChainRestrict`/`SolveFrameStages`); what this
   proposition still hides is the per-centre glue and the loop
   invariant (the partially written level table).

Everything here is proved; the two named residuals are strictly
narrower than `FrameStepAll` and carry all of its remaining content.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 Ownership plumbing -/

/-- The write discipline of a conditional, from its branches': the
guard tests, never writes. -/
theorem OwnedFrom.ite {LS LA : ℕ → List String} {j : ℕ} {b : Cond}
    {c d : Com} (hc : OwnedFrom LS LA j c) (hd : OwnedFrom LS LA j d) :
    OwnedFrom LS LA j (.ite b c d) := by
  constructor
  · intro y hy
    simp only [Com.wvars, List.mem_append] at hy
    rcases hy with h | h
    · exact hc.1 y h
    · exact hd.1 y h
  · intro a ha
    simp only [Com.warrs, List.mem_append] at ha
    rcases ha with h | h
    · exact hc.2 a h
    · exact hd.2 a h

/-- The write discipline of a sequence, from its halves'. -/
theorem OwnedFrom.seq {LS LA : ℕ → List String} {j : ℕ} {c d : Com}
    (hc : OwnedFrom LS LA j c) (hd : OwnedFrom LS LA j d) :
    OwnedFrom LS LA j (.seq c d) := by
  constructor
  · intro y hy
    simp only [Com.wvars, List.mem_append] at hy
    rcases hy with h | h
    · exact hc.1 y h
    · exact hd.1 y h
  · intro a ha
    simp only [Com.warrs, List.mem_append] at ha
    rcases ha with h | h
    · exact hc.2 a h
    · exact hd.2 a h

/-! ## §2 The canonical frame body's shape, and the else residual -/

/-- **The canonical frame body**: the machine leaf test `nS = 0`
guarding the canonical bottom block against the else branch — the shape
`blockSpec_leaf_guard` discharges. The else branch is a parameter: the
frame chain wires the inner block into it (`elseB j nxCom`). -/
noncomputable def guardBody (S : Setup L) (Kq : ℕ) (elseB : ℕ → Com → Com)
    (j : ℕ) (nxCom : Com) : Com :=
  .ite (.eq (.var (arenaNames j).nS) (.lit 0))
    (canonBotB S Kq j) (elseB j nxCom)

/-- **The else residual**: what remains of `FrameStep` once the guard
mechanism is discharged — given the inner block's contract and write
discipline, the else branch satisfies the level's contract **on edged
arenas of the diagonal**, and obeys the write discipline. Everything
`FrameStep` says beyond this (the leaf branch, the guard's cost and
evaluation, the off-diagonal vacuity) is proved below. -/
def FrameElse (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (elseB : ℕ → Com → Com)
    (KE : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpec B S ord ℓp htabF hbf arenaNames Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    (∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ →
      Spec B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (arenaNames j))
        (elseB j nxCom)
        (fun _ σ' => BlockPost S ord (k + 1) j (hbf j) A (htabF j A)
          (arenaNames j) σ')
        (KE k j A)) ∧
    OwnedFrom LS LA j (elseB j nxCom)

open Classical in
/-- **The frame step, from the else residual** — the guard mechanism
discharged: the leaf branch runs the canonical bottom block through the
landed `blockSpec_leaf_guard` (name side conditions from
`SolveFrameBridge` §1, at every level at once), the else branch is the
residual's, the conditional's write discipline is the branches', and
off the diagonal the contract is vacuous. The word bounds and scratch
descriptors are needed at every **non-bottom** level `j < S.depth` —
each level's leaf branch runs the bottom block at that level's own
dimensions. -/
theorem frameStep_of_else (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (elseB : ℕ → Com → Com)
    (KE : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Kq : ℕ)
    -- the schedule-rank bound at every non-bottom level
    (hKq : ∀ j, j < S.depth → ∀ β ∈ levelFml S j, qdepth β ≤ Kq)
    -- the word bounds: the carrier once, the level figures per level
    (hn0B : n₀ < B) (hn0B2 : n₀ * n₀ < B)
    (hNLB : ∀ j, j < S.depth → n₀ * S.pal j < B)
    (h2LB : ∀ j, j < S.depth → 2 ^ S.pal j * (Kq + 1) < B)
    (hTB : ∀ j, j < S.depth → n₀ * (levelFml S j).length < B)
    -- the per-level scratch descriptor, at the leaf's four regions
    (hscr : ∀ j, j < S.depth → ∀ σ, Scr j σ →
      (σ.arrs (botNa j)).length = 2 ^ S.pal j ∧
      (σ.arrs (botFa j)).length = 2 ^ S.pal j * (Kq + 1) ∧
      (σ.arrs (botEa j)).length = Kq + 1 ∧
      (σ.arrs (botXa j)).length = Kq + 1)
    -- the budget fit: the guard plus the larger branch
    (hKB : ∀ k j, j < S.depth → ∀ A : Arena (S.pal j) n₀,
      4 + max (botComK A.N (S.pal j) Kq (levelFml S j)) (KE k j A)
        ≤ KB (k + 1) j A)
    -- the name pools carry the leaf's names
    (hLS : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ j, ∀ a ∈ ([botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String), a ∈ LA j)
    -- the residual
    (helse : FrameElse B S ord ℓp htabF hbf Adm KB Scr LS LA elseB KE) :
    FrameStep B S ord ℓp htabF hbf arenaNames Adm KB Scr LS LA
      (guardBody S Kq elseB) := by
  intro k j nxCom hnx hown
  obtain ⟨helseSpec, helseOwn⟩ := helse k j nxCom hnx hown
  have hbotOwn : OwnedFrom LS LA j (canonBotB S Kq j) :=
    botBlock_owned LS LA arenaNames j Kq S (hLS j) (hLA j)
  refine ⟨?_, OwnedFrom.ite hbotOwn helseOwn⟩
  by_cases hdiag : j + (k + 1) = S.depth
  · have hj : j < S.depth := by omega
    exact blockSpec_leaf_guard B S ord ℓp htabF hbf arenaNames Adm KB Scr j Kq
      (hKq j hj) hn0B (hNLB j hj) (h2LB j hj) (hTB j hj)
      (canon_nd j) (canon_off j) (canon_tgt j) (canon_up j) (canon_hist j)
      (canon_nN j) (canon_nS j) (canon_nd5 j) (hscr j hj)
      k hn0B2 (elseB j nxCom) (KE k j)
      (fun A hd hAdm hbot => helseSpec A hd hAdm hbot)
      (fun A => hKB k j hj A)
  · intro A hd _ _
    exact absurd hd hdiag

/-! ## §3 The else branch's shape: cover, then the centre loop -/

/-- **The else branch's shape**: the level's cover stage in front of
the centre loop — the loop consumes the cover's two output regions. -/
def coverElse (covC : ℕ → Com) (loopB : ℕ → Com → Com) (j : ℕ)
    (nxCom : Com) : Com :=
  .seq (covC j) (loopB j nxCom)

/-- **Named residual (a): the cover stage per level arena** — the
landed `CoverStageSpec` shape (`SolveChainCover`), pinned to the
canonical names and quantified exactly where the frame step consumes
it: the non-bottom levels' admissible edged arenas. `ca`/`co`/`cm` are
the per-level output regions, `Scv` the stage's own scratch descriptor
(both the discharger's choice, threaded to the loop residual). -/
def CoverAll (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (ca co cm : ℕ → String) (Scv : ℕ → Env → Prop) (covC : ℕ → Com)
    (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ) : Prop :=
  ∀ j, j < S.depth → ∀ A : Arena (S.pal j) n₀, Adm j A → ¬ A.G = ⊥ →
    CoverStageSpec B S ord (hbf j) (arenaNames j) A (htabF j A)
      (ca j) (co j) (cm j) (Scv j) (covC j) (Kcov j A)

/-- **Named residual (b): the centre loop** — from the level's
`BlockPre` *plus the cover's two delivered regions* (`CtrArr` at
`Driver.centre`, `ClusterCsr` at `Driver.cluster`, both at the ordering
the routine returns for this arena), the loop leaves the level's
`BlockPost`, given the inner block's contract and write discipline.
This is the per-centre pipeline — restrict → BFS → supports →
profilesMS → isolate → the inner block → scatter → readback, per centre
of the schedule — whose stage lifts are all landed; the loop invariant
(the partially written level table) and the per-centre glue live in its
discharge. -/
def CentreLoop (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (loopB : ℕ → Com → Com)
    (KL : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpec B S ord ℓp htabF hbf arenaNames Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    (∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ →
      Spec B
        (fun σ =>
          BlockPre S j (hbf j) A (htabF j A) (Scr j) (arenaNames j) σ ∧
          CtrArr (ca j) (centre S A ((ord A.N A.G).order)) σ ∧
          ClusterCsr (co j) (cm j) (cluster S A ((ord A.N A.G).order)) σ)
        (loopB j nxCom)
        (fun _ σ' => BlockPost S ord (k + 1) j (hbf j) A (htabF j A)
          (arenaNames j) σ')
        (KL k j A)) ∧
    OwnedFrom LS LA j (loopB j nxCom)

open Classical in
/-- **The else residual, from the cover and the loop** — the seam
discharged: the cover's `Spec` runs first (its precondition drawn from
the level's scratch descriptor — the two output allocations are `Scr`'s,
at the per-depth maximum), lengths survive it for free
(`specArrsLength`), so the level's table allocation and the
length-only scratch descriptor cross to the loop, whose precondition is
exactly the cover's postcondition. The write discipline of the
composition is the parts'. -/
theorem frameElse_of_cover_loop (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (Scv : ℕ → Env → Prop) (covC : ℕ → Com) (loopB : ℕ → Com → Com)
    (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
    (KL : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ)
    -- the level's scratch descriptor carries the cover's needs …
    (hscrCov : ∀ j σ, Scr j σ →
      n₀ ≤ (σ.arrs (ca j)).length ∧ n₀ + 1 ≤ (σ.arrs (co j)).length ∧
      Scv j σ)
    -- … and is length-only, so it survives any run that keeps lengths
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    -- the cover obeys the write discipline (its discharger's, syntactic)
    (hcovOwn : ∀ j, OwnedFrom LS LA j (covC j))
    -- the two residuals
    (hcov : CoverAll B S ord ℓp htabF hbf Adm ca co cm Scv covC Kcov)
    (hloop : CentreLoop B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      loopB KL) :
    FrameElse B S ord ℓp htabF hbf Adm KB Scr LS LA (coverElse covC loopB)
      (fun k j A => Kcov j A + KL k j A) := by
  intro k j nxCom hnx hown
  obtain ⟨hloopSpec, hloopOwn⟩ := hloop k j nxCom hnx hown
  refine ⟨?_, OwnedFrom.seq (hcovOwn j) hloopOwn⟩
  intro A hdiag hAdm hbot
  have hj : j < S.depth := by omega
  have hcv := specArrsLength (hcov j hj A hAdm hbot)
  refine Spec.seq (hcv.pre ?_) (hloopSpec A hdiag hAdm hbot) ?_
    (fun _ _ _ _ _ h => h)
  · -- the block precondition lands in the cover's
    rintro σ ⟨hA, htab, hscrσ⟩
    obtain ⟨h1, h2, h3⟩ := hscrCov j σ hscrσ
    have hle : A.N ≤ n₀ := arenaN_le A
    exact ⟨hA, le_trans hle h1, le_trans (by omega) h2, h3⟩
  · -- the cover's postcondition lands in the loop's precondition
    rintro σ σ' ⟨hA, htab, hscrσ⟩ ⟨⟨hA', hctr, hcsr⟩, hlen⟩
    refine ⟨⟨hA', ?_, hscrLen j σ σ' hscrσ hlen⟩, hctr, hcsr⟩
    rw [hlen ((arenaNames j).tab)]
    exact htab

/-! ## §4 The headline: `FrameStepAll` from the two named residuals -/

/-- Residual (a), quantified per admissible input — the cover stage at
the word bound of every admissible input. -/
def CoverAllIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (Scv : ℕ → Env → Prop) (covC : ℕ → Com)
    (Kcov : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    CoverAll (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf Adm
      ca co cm Scv covC Kcov

/-- Residual (b), quantified per admissible input — the centre loop at
the word bound of every admissible input. -/
def CentreLoopAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (ca co cm : ℕ → String) (loopB : ℕ → Com → Com)
    (KL : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    CentreLoop (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      Adm KB Scr LS LA ca co cm loopB KL

open Classical in
/-- **Residual 1 of `solveSpec_closed`, discharged down to the cover
and the loop**: `FrameStepAll` holds — verbatim, at the canonical frame
body `guardBody (coverElse covC loopB)` — from the two named residuals
(`CoverAllIn`, `CentreLoopAll`) and hypotheses only of the kinds
`solveSpec_closed` itself takes: per-level word bounds at `mcB` (every
non-bottom level's leaf branch runs the bottom block at that level's
own dimensions), the per-level scratch descriptor (the leaf's four
regions and the cover's two output allocations; length-only), the
budget fits, and the name pools. -/
theorem frameStepAll_of_cover_loop (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (ca co cm : ℕ → String) (Scv : ℕ → Env → Prop)
    (covC : ℕ → Com) (loopB : ℕ → Com → Com)
    (Kcov : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (KL : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Kq : ℕ)
    -- the schedule-rank bound at every non-bottom level
    (hKq : ∀ j, j < (Headline.headlineSetup C hC φ).depth →
      ∀ β ∈ levelFml (Headline.headlineSetup C hC φ) j, qdepth β ≤ Kq)
    -- the word bounds, per admissible input
    (hB : ∀ x ∈ mcD n G c w, n < mcB q x ∧ n * n < mcB q x)
    (hBlev : ∀ x ∈ mcD n G c w,
      ∀ j, j < (Headline.headlineSetup C hC φ).depth →
      n * (Headline.headlineSetup C hC φ).pal j < mcB q x ∧
      2 ^ (Headline.headlineSetup C hC φ).pal j * (Kq + 1) < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ) j).length < mcB q x)
    -- the per-level scratch descriptor: the leaf's four regions …
    (hscr : ∀ j, j < (Headline.headlineSetup C hC φ).depth → ∀ σ, Scr j σ →
      (σ.arrs (botNa j)).length
        = 2 ^ (Headline.headlineSetup C hC φ).pal j ∧
      (σ.arrs (botFa j)).length
        = 2 ^ (Headline.headlineSetup C hC φ).pal j * (Kq + 1) ∧
      (σ.arrs (botEa j)).length = Kq + 1 ∧
      (σ.arrs (botXa j)).length = Kq + 1)
    -- … the cover's two output allocations and its scratch …
    (hscrCov : ∀ j σ, Scr j σ →
      n ≤ (σ.arrs (ca j)).length ∧ n + 1 ≤ (σ.arrs (co j)).length ∧
      Scv j σ)
    -- … and length-only transport
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    -- the budget fit: the guard plus the larger branch, the branch the
    -- cover plus the loop
    (hKB : ∀ k j, j < (Headline.headlineSetup C hC φ).depth →
      ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      4 + max (botComK A.N ((Headline.headlineSetup C hC φ).pal j) Kq
          (levelFml (Headline.headlineSetup C hC φ) j))
        (Kcov j A + KL k j A) ≤ KB (k + 1) j A)
    -- the name pools carry the leaf's names and the cover's writes
    (hLS : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ j, ∀ a ∈ ([botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String), a ∈ LA j)
    (hcovOwn : ∀ j, OwnedFrom LS LA j (covC j))
    -- the two named residuals
    (hcov : CoverAllIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm Scv
      covC Kcov)
    (hloop : CentreLoopAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      ca co cm loopB KL) :
    FrameStepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      (guardBody (Headline.headlineSetup C hC φ) Kq
        (coverElse covC loopB)) := by
  intro x hx
  obtain ⟨h1, h2⟩ := hB x hx
  refine frameStep_of_else (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp
    htabF hbf Adm KB Scr LS LA (coverElse covC loopB)
    (fun k j A => Kcov j A + KL k j A) Kq hKq h1 h2
    (fun j hj => (hBlev x hx j hj).1)
    (fun j hj => (hBlev x hx j hj).2.1)
    (fun j hj => (hBlev x hx j hj).2.2)
    hscr hKB hLS hLA ?_
  exact frameElse_of_cover_loop (mcB q x) (Headline.headlineSetup C hC φ)
    ord ℓp htabF hbf Adm KB Scr LS LA ca co cm Scv covC loopB Kcov KL
    hscrCov hscrLen hcovOwn (hcov x hx) (hloop x hx)

end Lax3Proofs.Prog
