import Lax3Proofs.SolveGlueStep

/-!
# F6c8 (part 3) — the centre loop's skeleton: iteration, invariant, and
the per-centre budget, discharged

`SolveGlueStep` reduced `FrameStepAll` to the cover residual and
**`CentreLoop`** — the per-centre pipeline over the schedule's centres.
This file discharges the *loop* half of that residual: the iteration
over the centres as a concrete `Com` (`centreLoopB` — a counted scan on
the level's own counter cell), the loop invariant (the level table,
**partially written by centre**: rows of every vertex whose centre is
already processed hold their final `unrollAux` values —
`TablePartial`), the per-centre budget summed at the ledger's shape
(`Σ_u (KC u + 8)`, not `N · max` — the per-centre costs are genuinely
non-uniform, `restrictK` at the cluster's own degree sum, so the loop
is priced by `Spec.while_potential` with the tail-sum potential), and
the write discipline of the loop.

What remains is **`CentreStep`** — the straight-line per-centre body:
from the loop invariant at centre `u` (the level's `BlockPre`, the
cover's two regions, the table partial below `u`), re-establish it at
`u + 1` — i.e. process one centre: the cluster-row read
(`ClusterCsr.read_row`), restrict → BFS → supports (at radius `2R`) →
profilesMS → isolate, the inner block through the windowed contract,
the per-atom scatters, and the readback of rows `{v | centre v = u}`
via the compiled combination. Every stage lift it needs is landed
(`SolveChainBot`/`SolveChainRestrict`/`SolveFrameStages`); the loop
mechanics it would otherwise owe live here.

`centreLoopAll_of_stepAll` is the headline: `CentreLoopAll` — verbatim
`SolveGlueStep`'s residual (b), at the canonical loop `centreLoopB
bodyB` — from `CentreStepAll` plus the word bound, the length-only
`Scr` transport, and the counter's membership in the level's name pool.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The partially written table, and the loop invariant -/

open Classical in
/-- **The level table, partially written**: the rows of every vertex
satisfying `P` already hold the target table's bits — `TableBitsW`'s
value clause restricted to `P` (the region's length rides in
`BlockPre`, so it is not restated). The loop instantiates `P` with
"the vertex's centre is below the counter". -/
def TablePartial (a : String) {N Λ : ℕ} (Fl : List (DistFO Λ 1))
    (T : Fin N → DistFO Λ 1 → Prop) (P : Fin N → Prop) (σ : Env) : Prop :=
  ∀ v : Fin N, P v → ∀ (i : ℕ), ∀ hi : i < Fl.length,
    (σ.arrs a).getD ((v : ℕ) * Fl.length + i) 0 = if T v Fl[i] then 1 else 0

/-- The level's loop counter cell — per level, by the `lv` mechanism
(blocks nest, so an inner block's loop must not clobber the outer's
counter). -/
def ctrName (j : ℕ) : String := lv "sl.u" j

/-- **The loop invariant at counter value `m`**: the level's `BlockPre`
(the windowed arena, the table allocation, the scratch descriptor), the
cover's two delivered regions, and the table partially written for
every vertex whose centre is below `m` — at the target
`unrollAux (k+1)`, the block's own postcondition table. -/
def CLInv (S : Setup L) (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String)
    (k j : ℕ) (A : Arena (S.pal j) n₀) (m : ℕ) (σ : Env) : Prop :=
  BlockPre S j (hbf j) A (htabF j A) (Scr j) (arenaNames j) σ ∧
  CtrArr (ca j) (centre S A ((ord A.N A.G).order)) σ ∧
  ClusterCsr (co j) (cm j) (cluster S A ((ord A.N A.G).order)) σ ∧
  TablePartial (arenaNames j).tab (levelFml S j)
    (Unroll.unrollAux S ord (k + 1) j A)
    (fun v => (centre S A ((ord A.N A.G).order) v : ℕ) < m) σ

/-- The counter cell is fresh against the level's two arena cells —
the `lv` mechanism's, no hypothesis owed. -/
theorem ctrName_ne_nN (j : ℕ) : ctrName j ≠ (arenaNames j).nN :=
  lv_ne_of_base_ne (by rfl) (by decide) j j

theorem ctrName_ne_nS (j : ℕ) : ctrName j ≠ (arenaNames j).nS :=
  lv_ne_of_base_ne (by rfl) (by decide) j j

/-- **The invariant is insensitive to the counter cell**: every
component reads arrays and the two (distinct) arena cells only — the
increment and the initialisation carry it for free. `Scr` crosses by
its length-only transport — which is why
`clInv_setVar_ctr_scr` below exists: that transport is inconsistent
with a content-carrying descriptor
(`SolveMachPrepSeam.rankScr_not_length_only`), and the counter bump
never needed it. -/
theorem clInv_setVar_ctr {S : Setup L} {ord : CoverSpec.OrderingRoutine}
    {ℓp : ℕ → ℕ}
    {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {hbf : ℕ → ℕ} {Scr : ℕ → Env → Prop} {ca co cm : ℕ → String}
    {k j : ℕ} {A : Arena (S.pal j) n₀} {m : ℕ} {σ : Env}
    (hscrLen : ∀ σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (h : CLInv S ord ℓp htabF hbf Scr ca co cm k j A m σ) (v : ℕ) :
    CLInv S ord ℓp htabF hbf Scr ca co cm k j A m
      (σ.setVar (ctrName j) v) := by
  obtain ⟨⟨hA, htab, hscr⟩, hctr, hcsr, hpart⟩ := h
  have hv : ∀ y, y ≠ ctrName j →
      (σ.setVar (ctrName j) v).vars y = σ.vars y := by
    intro y hy
    simp [hy]
  refine ⟨⟨?_, htab, hscrLen σ _ hscr (fun _ => rfl)⟩, hctr, hcsr, hpart⟩
  exact arenaStW_of_eq hA (hv _ (Ne.symm (ctrName_ne_nN j)))
    (hv _ (Ne.symm (ctrName_ne_nS j))) rfl rfl rfl rfl rfl

/-- **The invariant is insensitive to the counter cell** — the same
fact with the descriptor crossing by its frame law instead of a
length-only transport. The counter bump changes no array at all and
moves exactly one cell, so all `ScrFrame` asks for is that the counter
is not a cell any descriptor of level `≥ j` reads — which the `lv`
mechanism gives, and which the caller states as `hctrLV`. -/
theorem clInv_setVar_ctr_scr {S : Setup L} {ord : CoverSpec.OrderingRoutine}
    {ℓp : ℕ → ℕ}
    {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {hbf : ℕ → ℕ} {Scr : ℕ → Env → Prop} {LV LR : ℕ → List String}
    {ca co cm : ℕ → String}
    {k j : ℕ} {A : Arena (S.pal j) n₀} {m : ℕ} {σ : Env}
    (hfr : ScrFrame Scr LV LR) (hctrLV : ∀ i, j ≤ i → ctrName j ∉ LV i)
    (h : CLInv S ord ℓp htabF hbf Scr ca co cm k j A m σ) (v : ℕ) :
    CLInv S ord ℓp htabF hbf Scr ca co cm k j A m
      (σ.setVar (ctrName j) v) := by
  obtain ⟨⟨hA, htab, hscr⟩, hctr, hcsr, hpart⟩ := h
  have hv : ∀ y, y ≠ ctrName j →
      (σ.setVar (ctrName j) v).vars y = σ.vars y := by
    intro y hy
    simp [hy]
  refine ⟨⟨?_, htab,
    hfr j σ _ hscr (ScrAgree.setVar hctrLV) (fun _ => rfl)⟩,
    hctr, hcsr, hpart⟩
  exact arenaStW_of_eq hA (hv _ (Ne.symm (ctrName_ne_nN j)))
    (hv _ (Ne.symm (ctrName_ne_nS j))) rfl rfl rfl rfl rfl

/-! ## §2 The loop's shape, and the per-centre residual -/

/-- **The centre loop's shape**: zero the level's counter, then scan
the carrier — one per-centre body and the increment per turn. The body
is a parameter: the per-centre pipeline (`CentreStep`'s discharger's),
wired to the inner block. -/
def centreLoopB (bodyB : ℕ → Com → Com) (j : ℕ) (nxCom : Com) : Com :=
  .seq (.assign (ctrName j) (.lit 0))
    (.while (.lt (.var (ctrName j)) (.var (arenaNames j).nN))
      (.seq (bodyB j nxCom)
        (.assign (ctrName j) (.add (.var (ctrName j)) (.lit 1)))))

/-- **The per-centre residual**: one straight-line pass over centre
`u` — from the loop invariant at `u` (with the counter cell holding
`u`), re-establish it at `u + 1` without touching the counter, within
`KC u`. This is the per-centre pipeline: cluster-row read, restrict →
BFS → supports (radius `2R`) → profilesMS → isolate, the inner block
(consumed through its `BlockSpec`, exactly as given), the per-atom
scatters, and the readback of the rows `{v | centre v = u}`. -/
def CentreStep (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpec B S ord ℓp htabF hbf arenaNames Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    (∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ → ∀ u : Fin A.N,
      Spec B
        (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
          σ.vars (ctrName j) = (u : ℕ))
        (bodyB j nxCom)
        (fun σ σ' =>
          CLInv S ord ℓp htabF hbf Scr ca co cm k j A ((u : ℕ) + 1) σ' ∧
          σ'.vars (ctrName j) = σ.vars (ctrName j))
        (KC k j A (u : ℕ))) ∧
    OwnedFrom LS LA j (bodyB j nxCom)

/-- **The per-centre residual, at the strengthened recursion window** —
verbatim `CentreStep` with the inner block consumed at `BlockSpecScr`
instead of `BlockSpec`. The per-centre conclusion is untouched: the
loop invariant `CLInv` already contains `BlockPre`, and hence the
level's descriptor, at every centre. What the strengthened window buys
the discharger is `Scr (j+1)` at the block's exit, which is what
carries the *parent's* descriptor across the recursion by `ScrStep` —
no frame reaches it, since the block rewrites the deeper scratch. -/
def CentreStepScr (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpecScr B S ord ℓp htabF hbf arenaNames Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    (∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ → ∀ u : Fin A.N,
      Spec B
        (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
          σ.vars (ctrName j) = (u : ℕ))
        (bodyB j nxCom)
        (fun σ σ' =>
          CLInv S ord ℓp htabF hbf Scr ca co cm k j A ((u : ℕ) + 1) σ' ∧
          σ'.vars (ctrName j) = σ.vars (ctrName j))
        (KC k j A (u : ℕ))) ∧
    OwnedFrom LS LA j (bodyB j nxCom)

/-- The strengthened window is a **weaker** obligation on the per-centre
discharger: it may assume more about the inner block and must conclude
the same. So nothing that discharges `CentreStep` is deprived, and the
descriptor's new transport costs the per-centre pipeline nothing. -/
theorem centreStepScr_of_centreStep (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {hbf : ℕ → ℕ} {Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop}
    {KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ} {Scr : ℕ → Env → Prop}
    {LS LA : ℕ → List String} {ca co cm : ℕ → String}
    {bodyB : ℕ → Com → Com}
    {KC : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ}
    (h : CentreStep B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm bodyB KC) :
    CentreStepScr B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm bodyB KC :=
  fun k j nxCom hnx hown =>
    h k j nxCom (blockSpec_of_blockSpecScr B S ord ℓp hnx) hown

/-! ## §3 The loop, discharged from the per-centre residual -/

open Classical in
/-- **The centre loop, from the per-centre step** — the iteration
discharged: the counted scan runs the body once per centre, the
invariant's partial table closes to `BlockPost`'s full table at
`counter = N` (every vertex's centre is a centre), and the budget is
the *sum* of the per-centre costs plus the loop overhead —
`Σ_u (KC u + 8) + 6`, priced by the tail-sum potential. -/
theorem centreLoop_of_step (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (hn0B : n₀ < B)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hstep : CentreStep B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      bodyB KC) :
    CentreLoop B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      (centreLoopB bodyB)
      (fun k j A => (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6) := by
  intro k j nxCom hnx hown
  obtain ⟨hbody, hbodyOwn⟩ := hstep k j nxCom hnx hown
  constructor
  · -- the loop's specification
    intro A hdiag hAdm hbot
    have hNle : A.N ≤ n₀ := arenaN_le A
    have hNB : A.N < B := lt_of_le_of_lt hNle hn0B
    -- the invariant, as a state predicate over the counter cell
    set I : Env → Prop := fun σ =>
      CLInv S ord ℓp htabF hbf Scr ca co cm k j A (σ.vars (ctrName j)) σ ∧
      σ.vars (ctrName j) ≤ A.N with hI_def
    have hn_eq : ∀ σ, I σ → σ.vars (arenaNames j).nN = A.N :=
      fun σ hσ => hσ.1.1.1.n_eq
    -- the guard evaluates on the invariant
    have hdef : ∀ σ, I σ → ∃ v,
        (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).evalB B σ
          = some v := by
      intro σ hσ
      exact evalB_condLt_vars (by have := hσ.2; omega)
        (by rw [hn_eq σ hσ]; exact hNB)
    -- one turn: the body at the counter's centre, then the increment
    have hturn : ∀ σ, I σ →
        (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).evalB B σ
          = some true →
        ∃ σ' K, Run B (.seq (bodyB j nxCom)
            (.assign (ctrName j) (.add (.var (ctrName j)) (.lit 1)))) σ σ' K ∧
          I σ' ∧
          1 + (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).size + K +
            (∑ i ∈ Finset.Ico (σ'.vars (ctrName j)) A.N, (KC k j A i + 8))
            ≤ ∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8) := by
      intro σ hσ htrue
      obtain ⟨hInv, hle⟩ := hσ
      have hlt : σ.vars (ctrName j) < A.N := by
        have := lt_of_condLt_true htrue
        rwa [hn_eq σ ⟨hInv, hle⟩] at this
      -- the body, at the counter's centre
      obtain ⟨σ', hrun1, hpost, hctr'⟩ :=
        hbody A hdiag hAdm hbot ⟨σ.vars (ctrName j), hlt⟩ σ ⟨hInv, rfl⟩
      -- the increment
      have hctrB : σ'.vars (ctrName j) < B := by
        rw [hctr']
        omega
      have hev : (Expr.add (.var (ctrName j)) (.lit 1)).evalB B σ'
          = some (σ'.vars (ctrName j) + 1) := by
        have := evalB_bin (op := .add) (e := Expr.var (ctrName j))
          (f := Expr.lit 1) (evalB_var hctrB)
          (evalB_lit (by omega))
          (by simp only [Bop.apply_add]; rw [hctr']; omega)
        simpa using this
      have hrun2 : Run B (.assign (ctrName j)
            (.add (.var (ctrName j)) (.lit 1))) σ'
          (σ'.setVar (ctrName j) (σ'.vars (ctrName j) + 1)) 4 := by
        have := Run.assign (B := B) (x := ctrName j)
          (e := .add (.var (ctrName j)) (.lit 1)) hev
        exact this.mono (by simp [Expr.size])
      refine ⟨σ'.setVar (ctrName j) (σ'.vars (ctrName j) + 1),
        KC k j A (σ.vars (ctrName j)) + 4, hrun1.seq hrun2, ?_, ?_⟩
      · -- the invariant, at the advanced counter
        constructor
        · have hcv : (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j)
              = σ.vars (ctrName j) + 1 := by
            rw [← hctr']
            simp
          rw [hcv]
          exact clInv_setVar_ctr (hscrLen j) hpost _
        · show (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j) ≤ A.N
          rw [show (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j)
              = σ'.vars (ctrName j) + 1 by simp, hctr']
          omega
      · -- the tail-sum potential pays for the turn
        have hcv : (σ'.setVar (ctrName j)
            (σ'.vars (ctrName j) + 1)).vars (ctrName j)
            = σ.vars (ctrName j) + 1 := by
          rw [← hctr']
          simp
        rw [hcv, Finset.sum_eq_sum_Ico_succ_bot hlt
          (f := fun i => KC k j A i + 8)]
        simp only [Cond.size, Expr.size]
        omega
    -- the loop, priced by the tail-sum potential
    have hloop := Spec.while_potential
      (B := B) (c := .seq (bodyB j nxCom)
        (.assign (ctrName j) (.add (.var (ctrName j)) (.lit 1))))
      (b := .lt (.var (ctrName j)) (.var (arenaNames j).nN))
      (P := fun σ => I σ ∧ σ.vars (ctrName j) = 0)
      I (fun σ => ∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8))
      hdef hturn (fun σ hσ => hσ.1)
      (K := (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4)
      (fun σ hσ => by
        show (∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8))
            + 1 + (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).size
          ≤ (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4
        rw [hσ.2, Finset.range_eq_Ico]
        simp only [Cond.size, Expr.size]
        omega)
    -- the initialisation in front
    have hinit : Spec B
        (fun σ => BlockPre S j (hbf j) A (htabF j A) (Scr j)
            (arenaNames j) σ ∧
          CtrArr (ca j) (centre S A ((ord A.N A.G).order)) σ ∧
          ClusterCsr (co j) (cm j) (cluster S A ((ord A.N A.G).order)) σ)
        (.assign (ctrName j) (.lit 0))
        (fun σ σ' => σ' = σ.setVar (ctrName j) 0) 2 := by
      refine (Spec.assign (f := fun _ => 0) ?_).mono (by simp [Expr.size])
      intro σ _
      exact evalB_lit (by omega)
    refine (Spec.seq hinit hloop ?_ ?_).mono
      (show 2 + ((∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4)
          ≤ (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6 by omega)
    · -- the zeroed counter establishes the invariant: nothing is
      -- written yet, and no centre is below `0`
      rintro σ σ' ⟨hpre, hctr, hcsr⟩ rfl
      have hinv0 : CLInv S ord ℓp htabF hbf Scr ca co cm k j A 0 σ :=
        ⟨hpre, hctr, hcsr, fun v hv => absurd hv (by omega)⟩
      refine ⟨⟨?_, by simp⟩, by simp⟩
      have := clInv_setVar_ctr (hscrLen j) hinv0 0
      rwa [show (σ.setVar (ctrName j) 0).vars (ctrName j) = 0 by simp]
    · -- at `counter = N` the partial table is the whole table
      rintro σ σ' σ'' - - ⟨⟨⟨⟨hA, htab, -⟩, -, -, hpart⟩, hle⟩, hfalse⟩
      have hn_eq'' : σ''.vars (arenaNames j).nN = A.N := hA.n_eq
      have hge : σ''.vars (ctrName j) = A.N := by
        have := le_of_condLt_false hfalse
        rw [hn_eq''] at this
        omega
      refine ⟨hA, htab, ?_⟩
      intro v i hi
      refine hpart v ?_ i hi
      rw [hge]
      exact (centre S A ((ord A.N A.G).order) v).isLt
  · -- the write discipline: the counter is the level's, the body its
    -- discharger's
    constructor
    · intro y hy
      simp only [centreLoopB, Com.wvars, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | hy | rfl
      · exact ⟨j, le_rfl, hLSc j⟩
      · exact hbodyOwn.1 y hy
      · exact ⟨j, le_rfl, hLSc j⟩
    · intro a ha
      simp only [centreLoopB, Com.warrs, List.mem_append,
        List.not_mem_nil, or_false, false_or] at ha
      exact hbodyOwn.2 a ha

open Classical in
/-- **The centre loop, without the length-only transport** — verbatim
`centreLoop_of_step` at the strengthened contract. Two things change
and nothing else:

* `hscrLen` becomes the descriptor's frame law `hfr` plus `hctrLV` —
  the counter cell is not a cell any descriptor of level `≥ j` reads.
  That is all the counter bump ever needed: it changes no array, and
  moves one scalar.
* the exit produces `BlockPostScr`, i.e. the level's descriptor as
  well as its table. That is **free**: at `counter = N` the loop
  invariant still holds, and `CLInv` contains `BlockPre`, which
  contains `Scr j`. The landed proof simply discarded it.

The budget is untouched — `Σ_u (KC u + 8) + 6`, the same tail-sum
potential, no new term. -/
theorem centreLoop_of_stepScr (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA LV LR : ℕ → List String) (ca co cm : ℕ → String)
    (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (hn0B : n₀ < B)
    (hfr : ScrFrame Scr LV LR)
    (hctrLV : ∀ j i, j ≤ i → ctrName j ∉ LV i)
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hstep : CentreStepScr B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      bodyB KC) :
    CentreLoopScr B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      (centreLoopB bodyB)
      (fun k j A => (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6) := by
  intro k j nxCom hnx hown
  obtain ⟨hbody, hbodyOwn⟩ := hstep k j nxCom hnx hown
  constructor
  · -- the loop's specification
    intro A hdiag hAdm hbot
    have hNle : A.N ≤ n₀ := arenaN_le A
    have hNB : A.N < B := lt_of_le_of_lt hNle hn0B
    set I : Env → Prop := fun σ =>
      CLInv S ord ℓp htabF hbf Scr ca co cm k j A (σ.vars (ctrName j)) σ ∧
      σ.vars (ctrName j) ≤ A.N with hI_def
    have hn_eq : ∀ σ, I σ → σ.vars (arenaNames j).nN = A.N :=
      fun σ hσ => hσ.1.1.1.n_eq
    have hdef : ∀ σ, I σ → ∃ v,
        (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).evalB B σ
          = some v := by
      intro σ hσ
      exact evalB_condLt_vars (by have := hσ.2; omega)
        (by rw [hn_eq σ hσ]; exact hNB)
    have hturn : ∀ σ, I σ →
        (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).evalB B σ
          = some true →
        ∃ σ' K, Run B (.seq (bodyB j nxCom)
            (.assign (ctrName j) (.add (.var (ctrName j)) (.lit 1)))) σ σ' K ∧
          I σ' ∧
          1 + (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).size + K +
            (∑ i ∈ Finset.Ico (σ'.vars (ctrName j)) A.N, (KC k j A i + 8))
            ≤ ∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8) := by
      intro σ hσ htrue
      obtain ⟨hInv, hle⟩ := hσ
      have hlt : σ.vars (ctrName j) < A.N := by
        have := lt_of_condLt_true htrue
        rwa [hn_eq σ ⟨hInv, hle⟩] at this
      obtain ⟨σ', hrun1, hpost, hctr'⟩ :=
        hbody A hdiag hAdm hbot ⟨σ.vars (ctrName j), hlt⟩ σ ⟨hInv, rfl⟩
      have hctrB : σ'.vars (ctrName j) < B := by
        rw [hctr']
        omega
      have hev : (Expr.add (.var (ctrName j)) (.lit 1)).evalB B σ'
          = some (σ'.vars (ctrName j) + 1) := by
        have := evalB_bin (op := .add) (e := Expr.var (ctrName j))
          (f := Expr.lit 1) (evalB_var hctrB)
          (evalB_lit (by omega))
          (by simp only [Bop.apply_add]; rw [hctr']; omega)
        simpa using this
      have hrun2 : Run B (.assign (ctrName j)
            (.add (.var (ctrName j)) (.lit 1))) σ'
          (σ'.setVar (ctrName j) (σ'.vars (ctrName j) + 1)) 4 := by
        have := Run.assign (B := B) (x := ctrName j)
          (e := .add (.var (ctrName j)) (.lit 1)) hev
        exact this.mono (by simp [Expr.size])
      refine ⟨σ'.setVar (ctrName j) (σ'.vars (ctrName j) + 1),
        KC k j A (σ.vars (ctrName j)) + 4, hrun1.seq hrun2, ?_, ?_⟩
      · constructor
        · have hcv : (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j)
              = σ.vars (ctrName j) + 1 := by
            rw [← hctr']
            simp
          rw [hcv]
          exact clInv_setVar_ctr_scr hfr (hctrLV j) hpost _
        · show (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j) ≤ A.N
          rw [show (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j)
              = σ'.vars (ctrName j) + 1 by simp, hctr']
          omega
      · have hcv : (σ'.setVar (ctrName j)
            (σ'.vars (ctrName j) + 1)).vars (ctrName j)
            = σ.vars (ctrName j) + 1 := by
          rw [← hctr']
          simp
        rw [hcv, Finset.sum_eq_sum_Ico_succ_bot hlt
          (f := fun i => KC k j A i + 8)]
        simp only [Cond.size, Expr.size]
        omega
    have hloop := Spec.while_potential
      (B := B) (c := .seq (bodyB j nxCom)
        (.assign (ctrName j) (.add (.var (ctrName j)) (.lit 1))))
      (b := .lt (.var (ctrName j)) (.var (arenaNames j).nN))
      (P := fun σ => I σ ∧ σ.vars (ctrName j) = 0)
      I (fun σ => ∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8))
      hdef hturn (fun σ hσ => hσ.1)
      (K := (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4)
      (fun σ hσ => by
        show (∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8))
            + 1 + (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).size
          ≤ (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4
        rw [hσ.2, Finset.range_eq_Ico]
        simp only [Cond.size, Expr.size]
        omega)
    have hinit : Spec B
        (fun σ => BlockPre S j (hbf j) A (htabF j A) (Scr j)
            (arenaNames j) σ ∧
          CtrArr (ca j) (centre S A ((ord A.N A.G).order)) σ ∧
          ClusterCsr (co j) (cm j) (cluster S A ((ord A.N A.G).order)) σ)
        (.assign (ctrName j) (.lit 0))
        (fun σ σ' => σ' = σ.setVar (ctrName j) 0) 2 := by
      refine (Spec.assign (f := fun _ => 0) ?_).mono (by simp [Expr.size])
      intro σ _
      exact evalB_lit (by omega)
    refine (Spec.seq hinit hloop ?_ ?_).mono
      (show 2 + ((∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4)
          ≤ (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6 by omega)
    · rintro σ σ' ⟨hpre, hctr, hcsr⟩ rfl
      have hinv0 : CLInv S ord ℓp htabF hbf Scr ca co cm k j A 0 σ :=
        ⟨hpre, hctr, hcsr, fun v hv => absurd hv (by omega)⟩
      refine ⟨⟨?_, by simp⟩, by simp⟩
      have := clInv_setVar_ctr_scr hfr (hctrLV j) hinv0 0
      rwa [show (σ.setVar (ctrName j) 0).vars (ctrName j) = 0 by simp]
    · -- at `counter = N` the partial table is the whole table, and the
      -- level's descriptor is the invariant's own
      rintro σ σ' σ'' - - ⟨⟨⟨⟨hA, htab, hscr''⟩, -, -, hpart⟩, hle⟩, hfalse⟩
      have hn_eq'' : σ''.vars (arenaNames j).nN = A.N := hA.n_eq
      have hge : σ''.vars (ctrName j) = A.N := by
        have := le_of_condLt_false hfalse
        rw [hn_eq''] at this
        omega
      refine ⟨⟨hA, htab, ?_⟩, hscr''⟩
      intro v i hi
      refine hpart v ?_ i hi
      rw [hge]
      exact (centre S A ((ord A.N A.G).order) v).isLt
  · -- the write discipline: the counter is the level's, the body its
    -- discharger's
    constructor
    · intro y hy
      simp only [centreLoopB, Com.wvars, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | hy | rfl
      · exact ⟨j, le_rfl, hLSc j⟩
      · exact hbodyOwn.1 y hy
      · exact ⟨j, le_rfl, hLSc j⟩
    · intro a ha
      simp only [centreLoopB, Com.warrs, List.mem_append,
        List.not_mem_nil, or_false, false_or] at ha
      exact hbodyOwn.2 a ha

/-! ## §4 The headline: residual (b) from the per-centre step -/

/-- The per-centre residual, quantified per admissible input. -/
def CentreStepAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (ca co cm : ℕ → String) (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    CentreStep (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      Adm KB Scr LS LA ca co cm bodyB KC

open Classical in
/-- **Residual (b) of `SolveGlueStep`, discharged down to the
per-centre step**: `CentreLoopAll` holds — verbatim, at the canonical
loop `centreLoopB bodyB` — from `CentreStepAll` plus the word bound,
the length-only `Scr` transport, and the counter's membership in the
level's scalar pool. -/
theorem centreLoopAll_of_stepAll (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (ca co cm : ℕ → String) (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hnB : ∀ x ∈ mcD n G c w, n < mcB q x)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hstep : CentreStepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      ca co cm bodyB KC) :
    CentreLoopAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA ca co cm
      (centreLoopB bodyB)
      (fun k j A => (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6) := by
  intro x hx
  exact centreLoop_of_step (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp
    htabF hbf Adm KB Scr LS LA ca co cm bodyB KC (hnB x hx) hscrLen hLSc
    (hstep x hx)

/-- The per-centre residual at the strengthened window, quantified per
admissible input. -/
def CentreStepAllScr (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (ca co cm : ℕ → String) (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    CentreStepScr (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      Adm KB Scr LS LA ca co cm bodyB KC

open Classical in
/-- **Residual (b) at the strengthened contract, from the per-centre
step** — verbatim `centreLoopAll_of_stepAll` with `hscrLen` replaced by
the descriptor's frame law and the counter's freshness against the
descriptor's cells. Same loop, same budget. -/
theorem centreLoopAll_of_stepAllScr (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA LV LR : ℕ → List String)
    (ca co cm : ℕ → String) (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hnB : ∀ x ∈ mcD n G c w, n < mcB q x)
    (hfr : ScrFrame Scr LV LR)
    (hctrLV : ∀ j i, j ≤ i → ctrName j ∉ LV i)
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hstep : CentreStepAllScr C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      ca co cm bodyB KC) :
    CentreLoopAllScr C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA ca co cm
      (centreLoopB bodyB)
      (fun k j A => (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6) := by
  intro x hx
  exact centreLoop_of_stepScr (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp
    htabF hbf Adm KB Scr LS LA LV LR ca co cm bodyB KC (hnB x hx) hfr hctrLV
    hLSc (hstep x hx)

/-! ## §5 End to end: residual 1 from the cover and the per-centre step -/

open Classical in
/-- **`FrameStepAll` — residual 1 of `solveSpec_closed` — from the two
remaining residuals**, wired end to end: the canonical frame body is
`guardBody (coverElse covC (centreLoopB bodyB))` — the leaf guard
around the cover stage followed by the centre loop — and its contract
follows from `CoverAllIn` (the GKS sweep per level arena) and
`CentreStepAll` (the straight-line per-centre pass), with hypotheses
only of the kinds `solveSpec_closed` itself takes. -/
theorem frameStepAll_of_cover_step (C : GraphClass) (hC : NowhereDense C)
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
    (covC : ℕ → Com) (bodyB : ℕ → Com → Com)
    (Kcov : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (KC : (k j : ℕ) →
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
        (Kcov j A + ((∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6))
        ≤ KB (k + 1) j A)
    (hLS : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ j, ∀ a ∈ ([botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String), a ∈ LA j)
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hcovOwn : ∀ j, OwnedFrom LS LA j (covC j))
    (hcov : CoverAllIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm Scv
      covC Kcov)
    (hstep : CentreStepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      ca co cm bodyB KC) :
    FrameStepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      (guardBody (Headline.headlineSetup C hC φ) Kq
        (coverElse covC (centreLoopB bodyB))) :=
  frameStepAll_of_cover_loop C hC φ ord G c w q ℓp htabF hbf Adm KB Scr
    LS LA ca co cm Scv covC (centreLoopB bodyB) Kcov
    (fun k j A => (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6) Kq
    hKq hB hBlev hscr hscrCov hscrLen hKB hLS hLA hcovOwn hcov
    (centreLoopAll_of_stepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr
      LS LA ca co cm bodyB KC (fun x hx => (hB x hx).1) hscrLen hLSc hstep)

open Classical in
/-- **`FrameStepAllScr` from the cover and the per-centre step**, wired
end to end — verbatim `frameStepAll_of_cover_step` at the strengthened
contract, with `hscrLen` gone at both seams it crossed. In its place:
the descriptor's frame law `hfr`, the counter's freshness against the
descriptor's cells, and the two syntactic disjointness facts saying the
cover stage and the leaf block write no name the descriptor reads.
Body, budget and conclusion are unchanged. -/
theorem frameStepAll_of_cover_stepScr (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA LV LR : ℕ → List String)
    (ca co cm : ℕ → String) (Scv : ℕ → Env → Prop)
    (covC : ℕ → Com) (bodyB : ℕ → Com → Com)
    (Kcov : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (KC : (k j : ℕ) →
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
    (hfr : ScrFrame Scr LV LR)
    (hctrLV : ∀ j i, j ≤ i → ctrName j ∉ LV i)
    (hLVbt : ∀ i, ∀ y ∈ LV i, y ∉ btScalars)
    (hLRbot : ∀ j i, j ≤ i → ∀ a ∈ LR i,
      a ∉ ([botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab] :
        List String))
    (hcovFree : ∀ j, ScrFree LV LR j (covC j))
    (hKB : ∀ k j, j < (Headline.headlineSetup C hC φ).depth →
      ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      4 + max (botComK A.N ((Headline.headlineSetup C hC φ).pal j) Kq
          (levelFml (Headline.headlineSetup C hC φ) j))
        (Kcov j A + ((∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6))
        ≤ KB (k + 1) j A)
    (hLS : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ j, ∀ a ∈ ([botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String), a ∈ LA j)
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hcovOwn : ∀ j, OwnedFrom LS LA j (covC j))
    (hcov : CoverAllIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm Scv
      covC Kcov)
    (hstep : CentreStepAllScr C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      ca co cm bodyB KC) :
    FrameStepAllScr C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      (guardBody (Headline.headlineSetup C hC φ) Kq
        (coverElse covC (centreLoopB bodyB))) :=
  frameStepAll_of_cover_loopScr C hC φ ord G c w q ℓp htabF hbf Adm KB Scr
    LS LA LV LR ca co cm Scv covC (centreLoopB bodyB) Kcov
    (fun k j A => (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6) Kq
    hKq hB hBlev hscr hscrCov hfr hLVbt hLRbot hcovFree hKB hLS hLA hcovOwn
    hcov
    (centreLoopAll_of_stepAllScr C hC φ ord G c w q ℓp htabF hbf Adm KB Scr
      LS LA LV LR ca co cm bodyB KC (fun x hx => (hB x hx).1) hfr hctrLV hLSc
      hstep)

end Lax3Proofs.Prog
