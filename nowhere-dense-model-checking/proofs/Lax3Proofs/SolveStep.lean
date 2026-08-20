import Lax3Proofs.SolveGlueLoop

/-!
# F6c9a — the per-centre step's skeleton: the recursion window, discharged

`SolveGlueLoop` reduced `FrameStepAll` to **`CentreStepAll`** — one
straight-line pass over centre `u` re-establishing the loop invariant
`CLInv u → CLInv (u+1)` without touching the counter. This file
discharges everything *structural* about that residual — the one place
in the whole pipeline where the recursion enters: the inner block's
window. The per-centre body is pinned to the canonical three-segment
shape

`prepC j ; nxCom ; readC j`

(`centreBody`), and `CentreStep` is proved from two named residuals
that no longer mention `nxCom`, `BlockSpec`, `KB`, or the write
discipline at all:

* **`CentrePrep`** — the child construction: cluster-row read
  (`ClusterCsr.read_row`), restrict → BFS at `2R` → supports →
  profilesMS (at the PRE-isolation child `preG`) → isolate, and the
  load of the child arena into the level-`(j+1)` regions — from
  `CLInv u` (with the counter at `u`) to `CLInv u` *plus the inner
  block's own precondition* `BlockPre` at
  `childArena S A ((ord A.N A.G).order) u`, the counter untouched.
  This seam is exactly `BlockSpec (j+1)`'s precondition, so the inner
  block consumes it verbatim.
* **`CentreRead`** — the return path: the per-atom scatters on the
  (isolated) child graph read off the child's regions, and the
  readback of the rows `{v | centre v = u}` via the compiled
  combination (`bcExpr` per schedule row) into the level table — from
  `CLInv u` plus the inner block's postcondition `BlockPost` (the
  child's table at `Unroll.unrollAux k (j+1)`) to `CLInv (u+1)`, the
  counter untouched. The seam is semantically complete for
  `unrollAux (k+1)`'s recursive clause: on a non-edgeless arena,
  `frameEval` computes the row of `v` with `centre v = u` from exactly
  the child's tables (`next B vc`) and the scatter counts on `B.G` —
  both readable from `BlockPost` — through the cluster row's
  `v ↔ vc` correspondence carried by `CLInv`'s `ClusterCsr`
  (`childEquiv` is `setEquiv`, the ascending enumeration
  `Impl.restrictEmb` reads back).

What this file itself discharges (the structural remainder of
`CentreStep`):

* **the recursion window** — `BlockSpec (j+1) nxCom` instantiated at
  the child arena: the diagonal arithmetic
  (`j + (k+1) = ℓ → (j+1) + k = ℓ`), the child's admissibility and the
  fuel-`0` edgeless guard, both taken as `Adm`-side hypotheses of the
  kinds F7's run-tree facts supply (`Unroll.mkSetup_inv_of_memTree` /
  `mkSetup_memLeaf_eq_bot` through the concrete `Adm`);
* **the frame across the inner block** — the parent's whole invariant
  (`ArenaStW`, the table allocation, the two cover regions, the
  partial table, the counter cell) crosses `nxCom` by `Spec.frame`
  alone: `OwnedFrom (j+1)` says the block writes only names of pools
  `≥ j+1`, and the level-`j` names are fresh against those pools
  (`hfreshS`/`hfreshA`, the `lv` mechanism's facts, taken as
  name-pool hypotheses); `Scr` crosses by its length-only transport;
* **the budget's shape** — `centreKC = KP + (KB k (j+1) child + KR)`,
  the inner block priced by the chain's own `KB` at the child's
  dimensions, so the node-aggregate sum over `u` is exactly the
  ledger's per-centre-sum shape;
* **the write discipline of the composition** (`OwnedFrom.seq`, the
  inner block's discipline weakened one level, `OwnedFrom.mono_level`).

`centreStepAll_of_prep_read` is the headline: **verbatim
`CentreStepAll`** at the canonical body `centreBody prepC readC` and
budget `centreKC`, from `CentrePrepAll` + `CentreReadAll` plus
hypotheses only of F7-suppliable kinds. `frameStepAll_of_cover_prep_read`
wires it end to end: `FrameStepAll` at the fully concrete frame body
`guardBody (coverElse covC (centreLoopB (centreBody prepC readC)))`
from the three straight-line residuals (`CoverAllIn`, `CentrePrepAll`,
`CentreReadAll`).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 Transports: the loop invariant along agreement -/

/-- The assignment region reads one array; it transports along
agreement. -/
theorem ctrArr_of_eq {a : String} {N : ℕ} {f : Fin N → Fin N} {σ σ' : Env}
    (h : CtrArr a f σ) (ha : σ'.arrs a = σ.arrs a) : CtrArr a f σ' :=
  ⟨by rw [ha]; exact h.1, fun v => by rw [ha]; exact h.2 v⟩

/-- The cluster CSR reads two arrays; it transports along agreement. -/
theorem clusterCsr_of_eq {co cm : String} {N : ℕ}
    {Xf : Fin N → Set (Fin N)} {σ σ' : Env} (h : ClusterCsr co cm Xf σ)
    (hco : σ'.arrs co = σ.arrs co) (hcm : σ'.arrs cm = σ.arrs cm) :
    ClusterCsr co cm Xf σ' := by
  obtain ⟨offC, h0, hcoL, hcoV, hstep, hcmL, hcmV⟩ := h
  exact ⟨offC, h0, by rw [hco]; exact hcoL,
    fun i hi => by rw [hco]; exact hcoV i hi, hstep,
    by rw [hcm]; exact hcmL, fun u t ht => by rw [hcm]; exact hcmV u t ht⟩

/-- The partial table reads one array; it transports along agreement. -/
theorem tablePartial_of_eq {a : String} {N Λ : ℕ} {Fl : List (DistFO Λ 1)}
    {T : Fin N → DistFO Λ 1 → Prop} {P : Fin N → Prop} {σ σ' : Env}
    (h : TablePartial a Fl T P σ) (ha : σ'.arrs a = σ.arrs a) :
    TablePartial a Fl T P σ' := by
  intro v hv i hi
  rw [ha]
  exact h v hv i hi

/-- **The loop invariant transports along agreement on the level's own
names**: the two arena cells, the level's nine arrays (the arena's
five, the table, the cover's three), and all lengths (`Scr` is
length-only). This is what carries `CLInv` across the inner block by
its frame data alone. -/
theorem clInv_frame {S : Setup L} {ord : CoverSpec.OrderingRoutine}
    {ℓp : ℕ → ℕ}
    {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {hbf : ℕ → ℕ} {Scr : ℕ → Env → Prop} {ca co cm : ℕ → String}
    {k j : ℕ} {A : Arena (S.pal j) n₀} {m : ℕ} {σ σ' : Env}
    (hscrLen : ∀ σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (h : CLInv S ord ℓp htabF hbf Scr ca co cm k j A m σ)
    (hvN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN)
    (hvS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS)
    (harrs : ∀ a ∈ ca j :: co j :: cm j :: levelArrays j,
      σ'.arrs a = σ.arrs a)
    (hlen : ∀ b, (σ'.arrs b).length = (σ.arrs b).length) :
    CLInv S ord ℓp htabF hbf Scr ca co cm k j A m σ' := by
  obtain ⟨⟨hA, htab, hscr⟩, hctr, hcsr, hpart⟩ := h
  have hca : σ'.arrs (ca j) = σ.arrs (ca j) := harrs _ (by simp)
  have hco : σ'.arrs (co j) = σ.arrs (co j) := harrs _ (by simp)
  have hcm : σ'.arrs (cm j) = σ.arrs (cm j) := harrs _ (by simp)
  have hoff := harrs ((arenaNames j).off) (by simp [levelArrays])
  have htgt := harrs ((arenaNames j).tgt) (by simp [levelArrays])
  have hcol := harrs ((arenaNames j).col) (by simp [levelArrays])
  have hup := harrs ((arenaNames j).up) (by simp [levelArrays])
  have hhist := harrs ((arenaNames j).hist) (by simp [levelArrays])
  have htabeq := harrs ((arenaNames j).tab) (by simp [levelArrays])
  refine ⟨⟨arenaStW_of_eq hA hvN hvS hoff htgt hcol hup hhist, ?_,
    hscrLen σ σ' hscr hlen⟩, ctrArr_of_eq hctr hca,
    clusterCsr_of_eq hcsr hco hcm, tablePartial_of_eq hpart htabeq⟩
  rw [htabeq]
  exact htab

/-! ## §2 Ownership plumbing -/

/-- The write discipline weakens down the levels: a block owned from
`j'` is owned from any `j ≤ j'` — how the inner block's discipline
enters the parent's. -/
theorem OwnedFrom.mono_level {LS LA : ℕ → List String} {j j' : ℕ}
    {c : Com} (hj : j ≤ j') (h : OwnedFrom LS LA j' c) :
    OwnedFrom LS LA j c := by
  constructor
  · intro y hy
    obtain ⟨i, hi, h2⟩ := h.1 y hy
    exact ⟨i, by omega, h2⟩
  · intro a ha
    obtain ⟨i, hi, h2⟩ := h.2 a ha
    exact ⟨i, by omega, h2⟩

/-! ## §3 The per-centre body's shape, and the two residuals -/

/-- **The canonical per-centre body**: the child construction, the one
static copy of the inner block, the return path. The recursion enters
in the middle and nowhere else. -/
def centreBody (prepC readC : ℕ → Com) (j : ℕ) (nxCom : Com) : Com :=
  .seq (prepC j) (.seq nxCom (readC j))

/-- **Named residual (a): the child construction** — from the loop
invariant at centre `u` with the counter holding `u`, build the child
arena of centre `u` in the level-`(j+1)` regions: the cluster-row read
(`ClusterCsr.read_row`), restrict (`MArena.restrict`), BFS at radius
`2R`, supports (the round's `descendCol` on the channel column),
profilesMS at the **pre-isolation** child `preG`, isolate
(`deleteVerts` isolates, never removes), and the region load — leaving
the invariant at `u` intact, the counter untouched, and **exactly the
inner block's precondition** `BlockPre` at
`childArena S A ((ord A.N A.G).order) u` (with the chain's own channel
table `htabF (j+1)` and scratch descriptor `Scr (j+1)`). -/
def CentrePrep (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + (k + 1) = S.depth →
    Adm j A → ¬ A.G = ⊥ → ∀ u : Fin A.N,
    Spec B
      (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
        σ.vars (ctrName j) = (u : ℕ))
      (prepC j)
      (fun σ σ' => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ' ∧
        σ'.vars (ctrName j) = σ.vars (ctrName j) ∧
        BlockPre S (j + 1) (hbf (j + 1))
          (childArena S A ((ord A.N A.G).order) u)
          (htabF (j + 1) (childArena S A ((ord A.N A.G).order) u))
          (Scr (j + 1)) (arenaNames (j + 1)) σ')
      (KP k j A (u : ℕ))

/-- **Named residual (b): the return path** — from the loop invariant
at `u` (the counter holding `u`) *plus the inner block's postcondition*
(the child regions intact, the child table at
`Unroll.unrollAux k (j+1)` over `levelFml S (j+1)`), run the per-atom
scatters on the (isolated) child graph — batches padded to exactly
`width` through the windowed `FinBitsW`, a duplicate costing another
call — and read the rows `{v | centre v = u}` back into the level
table via the compiled combination per schedule row, matching
`frameEval`'s recursive clause on the nose (`levelFml_rank` puts every
row in the decomposition's guard); re-establish the invariant at
`u + 1`, the counter untouched. -/
def CentreRead (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (readC : ℕ → Com)
    (KR : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + (k + 1) = S.depth →
    Adm j A → ¬ A.G = ⊥ → ∀ u : Fin A.N,
    Spec B
      (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
        σ.vars (ctrName j) = (u : ℕ) ∧
        BlockPost S ord k (j + 1) (hbf (j + 1))
          (childArena S A ((ord A.N A.G).order) u)
          (htabF (j + 1) (childArena S A ((ord A.N A.G).order) u))
          (arenaNames (j + 1)) σ)
      (readC j)
      (fun σ σ' =>
        CLInv S ord ℓp htabF hbf Scr ca co cm k j A ((u : ℕ) + 1) σ' ∧
        σ'.vars (ctrName j) = σ.vars (ctrName j))
      (KR k j A (u : ℕ))

/-- **The per-centre budget**: the child construction, the inner block
at the chain's own price for the child's dimensions, the return path.
Summed over `u` by the loop, this is the ledger's per-centre-sum shape
(`centreK`'s `nxK` slot holds `KB` at the child). -/
noncomputable def centreKC (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ)
    (KP KR : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (k j : ℕ) (A : Arena (S.pal j) n₀) (u : ℕ) : ℕ :=
  KP k j A u +
    ((if h : u < A.N then
        KB k (j + 1) (childArena S A ((ord A.N A.G).order) ⟨u, h⟩)
      else 0) + KR k j A u)

/-! ## §4 The per-centre step, from the two residuals -/

open Classical in
/-- **The per-centre step, from the child construction and the return
path** — the recursion window discharged: the inner block's contract is
consumed verbatim at the child arena (the diagonal moves one level
down; admissibility and the fuel-`0` edgeless guard are the run tree's,
taken as `Adm`-side hypotheses), the parent's entire invariant crosses
the inner block by `Spec.frame` alone (the block writes only pools
`≥ j+1`, and the level's own names are fresh against them — the `lv`
mechanism's facts, taken as name-pool hypotheses; `Scr` crosses by its
length-only transport), the counter survives all three segments, and
the budget is the three-segment sum with the inner block at `KB`. -/
theorem centreStep_of_prep_read (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (prepC readC : ℕ → Com)
    (KP KR : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    -- the length-only scratch transport
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    -- the level's own names are fresh against the deeper pools
    (hfreshS : ∀ j i, j < i → ∀ y ∈ ctrName j :: levelScalars j, y ∉ LS i)
    (hfreshA : ∀ j i, j < i →
      ∀ a ∈ ca j :: co j :: cm j :: levelArrays j, a ∉ LA i)
    -- the run tree's two facts at the child, through `Adm`
    (hAdmChild : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), Adm j A →
      ¬ A.G = ⊥ → ∀ u : Fin A.N,
      Adm (j + 1) (childArena S A ((ord A.N A.G).order) u))
    (hleafChild : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), Adm j A →
      ¬ A.G = ⊥ → j + 1 = S.depth → ∀ u : Fin A.N,
      (childArena S A ((ord A.N A.G).order) u).G = ⊥)
    -- the two segments obey the write discipline (their dischargers')
    (hprepOwn : ∀ j, OwnedFrom LS LA j (prepC j))
    (hreadOwn : ∀ j, OwnedFrom LS LA j (readC j))
    -- the two residuals
    (hprep : CentrePrep B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP)
    (hread : CentreRead B S ord ℓp htabF hbf Adm Scr ca co cm readC KR) :
    CentreStep B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      (centreBody prepC readC) (centreKC S ord KB KP KR) := by
  intro k j nxCom hnx hnxOwn
  constructor
  · intro A hdiag hAdm hbot u
    -- the level's own names are never written by the inner block
    have hvarF : ∀ y ∈ ctrName j :: levelScalars j, y ∉ nxCom.wvars := by
      intro y hy hmem
      obtain ⟨i, hi, hyi⟩ := hnxOwn.1 y hmem
      exact hfreshS j i (by omega) y hy hyi
    have harrF : ∀ a ∈ ca j :: co j :: cm j :: levelArrays j,
        a ∉ nxCom.warrs := by
      intro a ha hmem
      obtain ⟨i, hi, hai⟩ := hnxOwn.2 a hmem
      exact hfreshA j i (by omega) a ha hai
    -- the inner block, at the child arena of centre `u`
    have hnxS := hnx (childArena S A ((ord A.N A.G).order) u) (by omega)
      (hAdmChild j A hAdm hbot u)
      (fun hk0 => hleafChild j A hAdm hbot (by omega) u)
    have hnxF := specArrsLength (Spec.frame hnxS)
    -- inner block ; return path — the invariant rides the frame
    have hinner : Spec B
        (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
          σ.vars (ctrName j) = (u : ℕ) ∧
          BlockPre S (j + 1) (hbf (j + 1))
            (childArena S A ((ord A.N A.G).order) u)
            (htabF (j + 1) (childArena S A ((ord A.N A.G).order) u))
            (Scr (j + 1)) (arenaNames (j + 1)) σ)
        (.seq nxCom (readC j))
        (fun σ σ' =>
          CLInv S ord ℓp htabF hbf Scr ca co cm k j A ((u : ℕ) + 1) σ' ∧
          σ'.vars (ctrName j) = σ.vars (ctrName j))
        (KB k (j + 1) (childArena S A ((ord A.N A.G).order) u)
          + KR k j A (u : ℕ)) := by
      refine Spec.seq (hnxF.pre (fun σ h => h.2.2))
        (hread k j A hdiag hAdm hbot u) ?_ ?_
      · -- the block's exit satisfies the return path's precondition
        rintro σ σ' ⟨hCL, hctr, -⟩ ⟨⟨hpost, hvars, harrs, -, -⟩, hlen⟩
        refine ⟨clInv_frame (hscrLen j) hCL
          (hvars _ (hvarF _ (by simp [levelScalars])))
          (hvars _ (hvarF _ (by simp [levelScalars])))
          (fun a ha => harrs a (harrF a ha)) hlen, ?_, hpost⟩
        rw [hvars _ (hvarF _ (by simp))]
        exact hctr
      · -- the counter survives both halves
        rintro σ σ' σ'' - ⟨⟨-, hvars, -, -, -⟩, -⟩ ⟨hCL'', hctr''⟩
        refine ⟨hCL'', ?_⟩
        rw [hctr'', hvars _ (hvarF _ (by simp))]
    -- the budget, at this centre
    have hKC : centreKC S ord KB KP KR k j A (u : ℕ)
        = KP k j A (u : ℕ)
          + (KB k (j + 1) (childArena S A ((ord A.N A.G).order) u)
            + KR k j A (u : ℕ)) := by
      simp [centreKC, u.isLt]
    rw [hKC]
    -- the child construction in front
    refine Spec.seq (hprep k j A hdiag hAdm hbot u) hinner ?_ ?_
    · -- prep's exit is the window's entry
      rintro σ σ' ⟨-, hctr0⟩ ⟨hCL, hctr, hpre⟩
      exact ⟨hCL, by rw [hctr, hctr0], hpre⟩
    · -- the counter's value composes
      rintro σ σ' σ'' - ⟨-, hctr, -⟩ ⟨hCL'', hctr''⟩
      exact ⟨hCL'', by rw [hctr'', hctr]⟩
  · -- the write discipline: the segments' own, the block's weakened
    show OwnedFrom LS LA j (.seq (prepC j) (.seq nxCom (readC j)))
    exact OwnedFrom.seq (hprepOwn j)
      (OwnedFrom.seq (OwnedFrom.mono_level (Nat.le_succ j) hnxOwn)
        (hreadOwn j))

/-! ## §5 The headline: `CentreStepAll` from the two residuals -/

/-- Residual (a), quantified per admissible input — the child
construction at the word bound of every admissible input. -/
def CentrePrepAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    CentrePrep (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      Adm Scr ca co cm prepC KP

/-- Residual (b), quantified per admissible input — the return path at
the word bound of every admissible input. -/
def CentreReadAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (readC : ℕ → Com)
    (KR : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    CentreRead (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      Adm Scr ca co cm readC KR

open Classical in
/-- **The residual of `SolveGlueLoop`, discharged down to the two
straight-line segments**: `CentreStepAll` holds — verbatim, at the
canonical body `centreBody prepC readC` and the budget `centreKC` —
from `CentrePrepAll` and `CentreReadAll` plus the length-only `Scr`
transport, the level names' freshness against the deeper pools, the
run tree's two facts at the child, and the segments' write
discipline. -/
theorem centreStepAll_of_prep_read (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (ca co cm : ℕ → String) (prepC readC : ℕ → Com)
    (KP KR : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hfreshS : ∀ j i, j < i → ∀ y ∈ ctrName j :: levelScalars j, y ∉ LS i)
    (hfreshA : ∀ j i, j < i →
      ∀ a ∈ ca j :: co j :: cm j :: levelArrays j, a ∉ LA i)
    (hAdmChild : ∀ (j : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ¬ A.G = ⊥ → ∀ u : Fin A.N,
      Adm (j + 1) (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u))
    (hleafChild : ∀ (j : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ¬ A.G = ⊥ → j + 1 = (Headline.headlineSetup C hC φ).depth →
      ∀ u : Fin A.N,
      (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u).G = ⊥)
    (hprepOwn : ∀ j, OwnedFrom LS LA j (prepC j))
    (hreadOwn : ∀ j, OwnedFrom LS LA j (readC j))
    (hprep : CentrePrepAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC KP)
    (hread : CentreReadAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm readC KR) :
    CentreStepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      ca co cm (centreBody prepC readC)
      (centreKC (Headline.headlineSetup C hC φ) ord KB KP KR) := by
  intro x hx
  exact centreStep_of_prep_read (mcB q x) (Headline.headlineSetup C hC φ)
    ord ℓp htabF hbf Adm KB Scr LS LA ca co cm prepC readC KP KR hscrLen
    hfreshS hfreshA hAdmChild hleafChild hprepOwn hreadOwn (hprep x hx)
    (hread x hx)

/-! ## §6 End to end: residual 1 from the three straight-line residuals -/

open Classical in
/-- **`FrameStepAll` — residual 1 of `solveSpec_closed` — from the
three straight-line residuals**, wired end to end: the canonical frame
body is now fully concrete in its shape,

`guardBody (coverElse covC (centreLoopB (centreBody prepC readC)))`,

and its contract follows from `CoverAllIn` (the GKS sweep),
`CentrePrepAll` (the child construction) and `CentreReadAll` (the
return path), with hypotheses only of the kinds `solveSpec_closed`
itself takes plus the freshness, `Adm`-side and ownership facts
above. -/
theorem frameStepAll_of_cover_prep_read (C : GraphClass)
    (hC : NowhereDense C) (φ : FO 0) (ord : CoverSpec.OrderingRoutine)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (ca co cm : ℕ → String) (Scv : ℕ → Env → Prop) (covC : ℕ → Com)
    (prepC readC : ℕ → Com)
    (Kcov : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (KP KR : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (Kq : ℕ)
    (hKq : ∀ j, j < (Headline.headlineSetup C hC φ).depth →
      ∀ β ∈ levelFml (Headline.headlineSetup C hC φ) j, qdepth β ≤ Kq)
    (hB : ∀ x ∈ mcD n G c w, n < mcB q x ∧ n * n < mcB q x)
    (hBlev : ∀ x ∈ mcD n G c w,
      ∀ j, j < (Headline.headlineSetup C hC φ).depth →
      n * (Headline.headlineSetup C hC φ).pal j < mcB q x ∧
      2 ^ (Headline.headlineSetup C hC φ).pal j * (Kq + 1) < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ) j).length < mcB q x)
    (hscr : ∀ j, j < (Headline.headlineSetup C hC φ).depth → ∀ σ, Scr j σ →
      (σ.arrs (botNa j)).length
        = 2 ^ (Headline.headlineSetup C hC φ).pal j ∧
      (σ.arrs (botFa j)).length
        = 2 ^ (Headline.headlineSetup C hC φ).pal j * (Kq + 1) ∧
      (σ.arrs (botEa j)).length = Kq + 1 ∧
      (σ.arrs (botXa j)).length = Kq + 1)
    (hscrCov : ∀ j σ, Scr j σ →
      n ≤ (σ.arrs (ca j)).length ∧ n + 1 ≤ (σ.arrs (co j)).length ∧
      Scv j σ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hKB : ∀ k j, j < (Headline.headlineSetup C hC φ).depth →
      ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      4 + max (botComK A.N ((Headline.headlineSetup C hC φ).pal j) Kq
          (levelFml (Headline.headlineSetup C hC φ) j))
        (Kcov j A + ((∑ i ∈ Finset.range A.N,
          (centreKC (Headline.headlineSetup C hC φ) ord KB KP KR k j A i
            + 8)) + 6))
        ≤ KB (k + 1) j A)
    (hLS : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ j, ∀ a ∈ ([botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String), a ∈ LA j)
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hfreshS : ∀ j i, j < i → ∀ y ∈ ctrName j :: levelScalars j, y ∉ LS i)
    (hfreshA : ∀ j i, j < i →
      ∀ a ∈ ca j :: co j :: cm j :: levelArrays j, a ∉ LA i)
    (hAdmChild : ∀ (j : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ¬ A.G = ⊥ → ∀ u : Fin A.N,
      Adm (j + 1) (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u))
    (hleafChild : ∀ (j : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ¬ A.G = ⊥ → j + 1 = (Headline.headlineSetup C hC φ).depth →
      ∀ u : Fin A.N,
      (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u).G = ⊥)
    (hcovOwn : ∀ j, OwnedFrom LS LA j (covC j))
    (hprepOwn : ∀ j, OwnedFrom LS LA j (prepC j))
    (hreadOwn : ∀ j, OwnedFrom LS LA j (readC j))
    (hcov : CoverAllIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm Scv
      covC Kcov)
    (hprep : CentrePrepAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC KP)
    (hread : CentreReadAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm readC KR) :
    FrameStepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      (guardBody (Headline.headlineSetup C hC φ) Kq
        (coverElse covC (centreLoopB (centreBody prepC readC)))) :=
  frameStepAll_of_cover_step C hC φ ord G c w q ℓp htabF hbf Adm KB Scr
    LS LA ca co cm Scv covC (centreBody prepC readC) Kcov
    (centreKC (Headline.headlineSetup C hC φ) ord KB KP KR) Kq
    hKq hB hBlev hscr hscrCov hscrLen hKB hLS hLA hLSc hcovOwn hcov
    (centreStepAll_of_prep_read C hC φ ord G c w q ℓp htabF hbf Adm KB Scr
      LS LA ca co cm prepC readC KP KR hscrLen hfreshS hfreshA hAdmChild
      hleafChild hprepOwn hreadOwn hprep hread)

end Lax3Proofs.Prog
