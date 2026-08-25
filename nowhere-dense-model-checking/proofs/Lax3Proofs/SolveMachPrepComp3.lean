import Lax3Proofs.SolveMachPrepComp2

/-!
# F6c12 (residual 1) — the child-building pass: the nine stages at the
# pass's own names

`SolveMachPrepComp` fixed the pass's name pool, its command `prepC`, its
budget and the level's scratch descriptor `prepScr`; `SolveMachPrepComp2`
discharged the three families of side condition the stage contracts bind
their caller to (the allocations, the names, the word bounds) and wrapped
**two** of the nine stages at the pass's own names (`prep_restrictStage`,
`prep_mkBatchStage`). This file wraps the remaining **seven**, so that
the composition of `ChildLoadPartsScrAll` has, for every one of the
fourteen `Spec.seq` steps that is a stage, a `Spec` already stated at
`prepC`'s own arrays, cells and dimensions, with every side condition
gone.

## The one hypothesis the pass owes beyond `PrepWB`

`ChildLoadPartsScr` quantifies over the cover's three array names
`ca`, `co`, `cm` as *parameters* and relates them to nothing. But the
pass stores into fifteen arrays and three ℕ-indexed families, and the
residual's own postcondition demands
`∀ a ∈ ca j :: co j :: cm j :: levelArrays j, σ'.arrs a = σ.arrs a`.
The `levelArrays j` half is a base or level clash at the `lv` pool and
is discharged here; the `ca/co/cm` half **cannot be**, because nothing
in the residual says those three are not the pass's own regions. Worse,
`clusterRowCom_spec` asks for `la ≠ cm` outright, so even the *first*
stage is unreachable without it.

`PrepCoverNames` (§1) is that hypothesis, in the campaign's established
shape (`FrNames`, `OrNames`, `TrNames`, …): a named `Prop` bundle,
carried explicitly, with `prepCoverNames_exists` showing it satisfiable
rather than vacuous. It is the **fourth** invisible binding requirement
of this pass, after the allocations, the exact batch width, and the
cover-offset word bound.

## Hazards honoured

No program, stage, radius or budget is defined or moved, and no landed
statement is restated: every theorem below is a landed contract with its
side conditions discharged, at `prepC`'s own arguments. In particular
the BFS and the supports pass are instantiated at radius `2 * S.R`,
never `S.R`, and the profiles stage at the **pre-isolation** child
(`prepMid j`'s CSR pair, the parent palette), never the isolated one.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

/-! ## §1 The cover's three arrays, and the pass's own

The clause list is exactly `prepC`'s array write set: `warrs_prepC`
would read it off the syntax, and every entry below is one of its
members. Nothing else about `ca`, `co`, `cm` is assumed — in particular
they are *not* assumed distinct from each other, since the pass never
needs that. -/

section CoverNames

/-- **The pass's own array regions**, at level `j`: the fifteen fixed
names. The three ℕ-indexed profile families are separate clauses of
`PrepCoverNames` because they are not a finite list. -/
def prepArrays (j : ℕ) : List String :=
  [pcLa, pcRa j, pcOi, pcTi, pcBb, pcBi, pcDa, pcPa, pcXb, pcVo,
    (arenaNames (j + 1)).off, (arenaNames (j + 1)).tgt,
    (arenaNames (j + 1)).col, (arenaNames (j + 1)).up,
    (arenaNames (j + 1)).hist]

/-- **The fourth invisible binding requirement.** The cover stage's
three arrays are none of the pass's own regions — so the pass's writes
never touch them, which is what `ChildLoadPartsScr`'s array frame
clause demands and what `clusterRowCom_spec`'s `hla_cm` asks for
outright. -/
structure PrepCoverNames (ca co cm : ℕ → String) (j : ℕ) : Prop where
  /-- Outside the fifteen fixed regions. -/
  fixed : ∀ x ∈ ([ca j, co j, cm j] : List String), x ∉ prepArrays j
  /-- Outside the batch-profile family. -/
  pd : ∀ x ∈ ([ca j, co j, cm j] : List String), ∀ t : ℕ, x ≠ pcPd t
  /-- Outside the virtual-source family. -/
  vt : ∀ x ∈ ([ca j, co j, cm j] : List String), ∀ c : ℕ, x ≠ pcVt c
  /-- Outside the per-class family. -/
  pu : ∀ x ∈ ([ca j, co j, cm j] : List String), ∀ c : ℕ, x ≠ pcPu c

/-- `clusterRowCom_spec`'s `hla_cm`, off the bundle. -/
theorem prepCoverNames_la_cm {ca co cm : ℕ → String} {j : ℕ}
    (h : PrepCoverNames ca co cm j) : pcLa ≠ cm j := by
  have hx := h.fixed (cm j) (by simp)
  intro hEq
  exact hx (by rw [← hEq]; simp [prepArrays])

/-- **The bundle is satisfiable**, so no theorem carrying it is vacuous:
at any level-tagged family whose base misses the pass's four base
groups the whole bundle is a base clash. (`"cv.a"`, `"cv.o"`, `"cv.m"`
are four characters, as `lv_inj` requires, and clash with every one of
`sa.·`, `sv.·`, `pc.·`, `pf.·`.) -/
theorem prepCoverNames_exists (j : ℕ) :
    PrepCoverNames (lv "cv.a") (lv "cv.o") (lv "cv.m") j := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [prepArrays, pcLa, pcRa, pcOi, pcTi, pcBb, pcBi, pcDa, pcPa,
      pcXb, pcVo, arenaNames, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    rcases hx with rfl | rfl | rfl <;>
      exact ⟨lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _⟩
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    intro t
    simp only [pcPd, pcVt, pcPu]
    rcases hx with rfl | rfl | rfl <;>
      exact lv_ne_of_base_ne (by decide) (by decide) _ _

end CoverNames

/-! ## §2 The word bounds at the **child's** dimensions

`SolveMachPrepComp2` §5 states `PrepWB`'s consequences at an
`Arena Λ n₀`. Six of the nine stages run at the *child*, whose carrier
is `childN` and which is an `Impl.MArena`, not an `Arena`; these are the
same four clauses read at `childN ≤ n₀`. -/

section ChildWordSize

variable {L n₀ B : ℕ} {S : Setup L} {ℓp hbf : ℕ → ℕ}

/-- The child's carrier is below the bound. -/
theorem prepWB_childN (h : PrepWB S ℓp hbf n₀ B) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : childN S A π u + 2 < B := by
  have h1 := prepWB_root h
  have h2 := prep_childN_le_root S A π u
  omega

/-- …and so is its square — `bfsCom_specW`'s and `isolateCom_specW`'s
`hNNB` at the pre-isolation child. -/
theorem prepWB_childNN (h : PrepWB S ℓp hbf n₀ B) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    childN S A π u * childN S A π u < B := by
  have h1 := h.carrier
  have h2 := prep_childN_le_root S A π u
  have : childN S A π u * childN S A π u ≤ n₀ * n₀ := Nat.mul_le_mul h2 h2
  omega

/-- `profilesCom_specW`'s `hΛB` at the child and the **parent's**
palette — the palette the pre-isolation child's colour rows are at. -/
theorem prepWB_childPal (h : PrepWB S ℓp hbf n₀ B) {j : ℕ} (hj : j ≤ S.depth)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    childN S A π u * S.pal j < B := by
  refine lt_of_le_of_lt ?_ (h.palette j hj)
  exact Nat.mul_le_mul (prep_childN_le_root S A π u) (prep_pal_le_succ S j)

/-- **The column the supports pass writes is a legal column**, at the
level's own count: the round-count pin makes `A.hist.length` the numeral
`j`, the room pin puts it inside the *child's* region, and the column
pin makes the two counts equal. This is what turns `prepSupCells`'
`.lit j` into `supportsCom_specW`'s `e : Fin (ℓp j)`. -/
theorem prep_col_lt {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop}
    (hp : PrepPins S ℓp htabF hbf Adm) (j : ℕ) (hjd : j < S.depth)
    {A : Arena (S.pal j) n₀} (hAdm : Adm j A) : j < ℓp j := by
  have hr := hp.round j A hAdm
  have hm := hp.room j A hjd hAdm
  have hc := hp.col j
  omega

end ChildWordSize

/-! ## §3 The cover-facing stages

The two loads that turn the cover's CSR row into `restrictCom_specW`'s
`ClusterList` and the connector's own child name. Both are the pass's
own glue, both charge against the restrict stage's column
(`clusterRowK_le_restrictK`, `centreIdxK_le_restrictK`), and both are
the only stages that read an array the pass does not own — which is why
`PrepCoverNames` exists. -/

section CoverStages

variable {L n₀ B : ℕ}

/-- **The cluster-row copy, at the pass's names.** `clusterRowCom_spec`
with its four disequalities (`SolveMachPrepComp2` §4), its cluster-region
allocation (§3), its cover-offset word bound (§6) and the one cover-name
clause `PrepCoverNames` supplies. -/
theorem prep_clusterRowStage {S : Setup L} {ℓp hbf : ℕ → ℕ}
    {ca co cm : ℕ → String} (hwb : PrepWB S ℓp hbf n₀ B) (j : ℕ)
    (hcn : PrepCoverNames ca co cm j)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    Spec B
      (fun σ => ClusterCsr (co j) (cm j) (cluster S A π) σ ∧
        σ.vars (ctrName j) = (u : ℕ) ∧
        prepScr S ℓp hbf n₀ j σ)
      (clusterRowCom (co j) (cm j) pcLa (ctrName j) pcCb "rs.k" pcCt)
      (fun σ σ' => ClusterList pcLa (cluster S A π u) σ' ∧
        σ'.vars "rs.k" = (cluster S A π u).ncard ∧
        (∀ y, y ≠ pcCb → y ≠ "rs.k" → y ≠ pcCt → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ pcLa → σ'.arrs a = σ.arrs a) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (clusterRowK (cluster S A π u).ncard) :=
  (clusterRowCom_spec (B := B) (Xf := cluster S A π) u
      (by have := prepWB_N hwb A; omega)
      (prepCoverNames_la_cm hcn) prep_ct_ne_rsk prep_ct_ne_cb prep_cb_ne_rsk
      (prep_ctr_ne_cb j)).pre
    (fun σ hσ =>
      ⟨hσ.1, hσ.2.1, prepScr_la_len S ℓp hbf j π u hσ.2.2,
        prep_clusterCsr_offset_lt hwb hσ.1⟩)

/-- **The connector scan, at the pass's names.**
`centreIdxCom_centreChild` with its five disequalities discharged; the
carrier cell it reads is `"rs.k"`, which the copy above just wrote. -/
theorem prep_centreIdxStage {S : Setup L} (j : ℕ)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (hNB : A.N < B) :
    Spec B
      (fun σ => ClusterList pcLa (cluster S A π u) σ ∧
        σ.vars (ctrName j) = (u : ℕ) ∧
        σ.vars "rs.k" = childN S A π u)
      (centreIdxCom pcLa (ctrName j) "rs.k" pcCc pcCt)
      (fun σ σ' =>
        σ'.vars pcCc = ((centreChild S A π u : Fin (childN S A π u)) : ℕ) ∧
        (∀ z, z ≠ pcCc → z ≠ pcCt → σ'.vars z = σ.vars z) ∧
        (∀ a, σ'.arrs a = σ.arrs a))
      (centreIdxK (childN S A π u)) :=
  centreIdxCom_centreChild S A π u hNB prep_ct_ne_rsk (prep_ct_ne_ctr j)
    prep_ct_ne_cc prep_cc_ne_rsk (prep_cc_ne_ctr j)

end CoverStages

/-! ## §4 The child-side stages

All five run on the **pre-isolation** child
`(Impl.ofArena A (chanTab S ℓp j A)).restrict (cluster S A π u)`, whose
carrier is `childN S A π u` and whose graph is `preG S A π u` — both
definitionally (`Impl.restrict_N_eq_childN`, `Impl.restrict_G_eq_preG`),
so every dimension below may be written at the driver's own names. The
name family is `prepMid j`, whose CSR pair is the pass's own scratch
`pcOi`/`pcTi`: that is what routes the isolation's output into the
level's own regions and leaves only the slot-count cell to move. -/

section ChildStages

variable {L n₀ B : ℕ}

open Classical in
/-- **The BFS, at the pass's names.** `bfsCom_specW` at the
pre-isolation child, source the connector's own child name, radius
`2 * S.R` — never `S.R` (hazard 2). Its three word bounds are §5's at
the child (§2 here), its five name clauses `SolveMachPrepComp2` §4's,
and its one allocation `prepScr_da_len`. -/
theorem prep_bfsStage {S : Setup L} {ℓp hbf : ℕ → ℕ}
    (hwb : PrepWB S ℓp hbf n₀ B) (j : ℕ)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            ((Impl.ofArena A (chanTab S ℓp j A)).restrict
              (cluster S A π u)) σ ∧
          σ.vars "bf.n" = childN S A π u ∧
          σ.vars "bf.m" = σ.vars (arenaNames (j + 1)).nS ∧
          σ.vars "bf.r" = 2 * S.R ∧
          σ.vars "bf.v"
            = ((centreChild S A π u : Fin (childN S A π u)) : ℕ) ∧
          prepScr S ℓp hbf n₀ j σ)
      (bfsCom pcOi pcTi pcDa)
      (fun σ σ' => ArenaStW (prepMid j) (hbf j)
          ((Impl.ofArena A (chanTab S ℓp j A)).restrict
            (cluster S A π u)) σ' ∧
        σ'.vars (arenaNames (j + 1)).nS = σ.vars (arenaNames (j + 1)).nS ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ v : Fin (childN S A π u),
          (σ'.arrs pcDa).getD (v : ℕ) 0 ≤ 2 * S.R + 1) ∧
        Lax3Proofs.Impl.BallTable (preG S A π u) (centreChild S A π u)
          (2 * S.R) (fun v => (σ'.arrs pcDa).getD (v : ℕ) 0))
      (bfsK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
        (2 * S.R)) :=
  (bfsCom_specW (B := B)
      (A := (Impl.ofArena A (chanTab S ℓp j A)).restrict (cluster S A π u))
      (nm := prepMid j) (da := pcDa) (centreChild S A π u)
      (by have := prepWB_childN hwb A π u; show childN S A π u < B; omega)
      (prepWB_childNN hwb A π u)
      (by have := prepWB_twoR hwb; omega)
      prep_ti_ne_oi (prep_da_notMem5 j)
      (prep_nN_notMem_bf (j + 1)) (prep_nS_notMem_bf (j + 1))).pre
    (fun σ hσ =>
      ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1,
        prepScr_da_len S ℓp hbf j π u hσ.2.2.2.2.2⟩)

open Classical in
/-- **The supports pass, at the pass's names.** `supportsCom_specW` at
the pre-isolation child, again at radius `2 * S.R`, writing the column
`A.hist.length` — which the round-count pin makes the numeral `j`, the
one `prepSupCells` loads. The column's legality (`j < ℓp j`) is the
`RoomPin`/`ColPin` pair; the row bound `2 * S.R + 1 ≤ hbf j` is not a
landed pin and is carried here as `hrow`. -/
theorem prep_supportsStage {S : Setup L} {ℓp hbf : ℕ → ℕ}
    {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop}
    (hwb : PrepWB S ℓp hbf n₀ B) (hp : PrepPins S ℓp htabF hbf Adm)
    (j : ℕ) (hj : j ≤ S.depth) (hjd : j < S.depth)
    (A : Arena (S.pal j) n₀) (hAdm : Adm j A)
    (hrow : 2 * S.R + 1 ≤ hbf j)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {D : Fin (childN S A π u) → ℕ}
    (hD : Lax3Proofs.Impl.BallTable (preG S A π u) (centreChild S A π u)
      (2 * S.R) D)
    (hDd : ∀ v : Fin (childN S A π u), D v ≤ 2 * S.R + 1) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            ((Impl.ofArena A (chanTab S ℓp j A)).restrict
              (cluster S A π u)) σ ∧
          σ.vars "sp.n" = childN S A π u ∧
          σ.vars "sp.m" = σ.vars (arenaNames (j + 1)).nS ∧
          σ.vars "sp.r" = 2 * S.R ∧ σ.vars "sp.l" = ℓp j ∧
          σ.vars "sp.h" = hbf j ∧ σ.vars "sp.p" = j ∧
          (∀ v : Fin (childN S A π u), (σ.arrs pcDa).getD (v : ℕ) 0 = D v) ∧
          prepScr S ℓp hbf n₀ j σ)
      (supportsCom pcOi pcTi pcDa pcPa (arenaNames (j + 1)).hist)
      (fun σ σ' => ArenaStW (prepMid j) (hbf j)
          { (Impl.ofArena A (chanTab S ℓp j A)).restrict (cluster S A π u)
              with hist := fun v p =>
                if p = (⟨j, prep_col_lt hp j hjd hAdm⟩ : Fin (ℓp j)) then
                  descendCol (preG S A π u) D (2 * S.R) v
                else ((Impl.ofArena A (chanTab S ℓp j A)).restrict
                  (cluster S A π u)).hist v p } σ' ∧
        σ'.vars (arenaNames (j + 1)).nS = σ.vars (arenaNames (j + 1)).nS ∧
        (∀ v : Fin (childN S A π u), (σ'.arrs pcDa).getD (v : ℕ) 0 = D v) ∧
        (∀ v : Fin (childN S A π u), (σ'.arrs pcPa).getD (v : ℕ) 0
          = leastParent (preG S A π u) D v) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (supportsK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)) :=
  (supportsCom_specW (B := B)
      (A := (Impl.ofArena A (chanTab S ℓp j A)).restrict (cluster S A π u))
      (nm := prepMid j) (pa := pcPa) (da := pcDa) (D := D)
      (s := centreChild S A π u)
      ⟨j, prep_col_lt hp j hjd hAdm⟩ hD hDd hrow
      (by have := prepWB_childN hwb A π u; show childN S A π u < B; omega)
      (prepWB_childNN hwb A π u)
      (by have := prepWB_twoR hwb; omega)
      (prepWB_lp hwb hj)
      (by have := prepWB_hb hwb hj; omega)
      (prepWB_chanChild hwb hj A π u)
      (prepMid_nodup5 j) (prep_da_notMem5 j) (prep_pa_notMem5 j)
      prep_da_ne_pa
      (prep_nN_notMem_sp (j + 1)) (prep_nS_notMem_sp (j + 1))).pre
    (fun σ hσ =>
      ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1, hσ.2.2.2.2.2.1,
        hσ.2.2.2.2.2.2.1,
        prepScr_pa_len S ℓp hbf j π u hσ.2.2.2.2.2.2.2.2,
        prepScr_da_len S ℓp hbf j π u hσ.2.2.2.2.2.2.2.2,
        hσ.2.2.2.2.2.2.2.1⟩)

open Classical in
/-- **The profiles stage, at the pass's names.** `profilesCom_specW` at
the pre-isolation child, the padded batch region `pcBi`, the parent's
palette `S.pal j` — never the child's — and the twenty-one-clause name
bundle `prep_profNames_ok`. Its five word bounds are §5's and §2's, and
its eight allocation clauses §3's, the batch region's **equality**
(`prepScr_batchWidth`) included. -/
theorem prep_profilesStage {S : Setup L} {ℓp hbf : ℕ → ℕ}
    (hwb : PrepWB S ℓp hbf n₀ B) (j : ℕ) (hj : j ≤ S.depth)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            ((Impl.ofArena A (chanTab S ℓp j A)).restrict
              (cluster S A π u)) σ ∧
          (∀ i : Fin S.width, (σ.arrs pcBi).getD (i : ℕ) 0
            = ((batchFn S A π u i : Fin (childN S A π u)) : ℕ)) ∧
          prepScr S ℓp hbf n₀ j σ)
      (profilesCom (prepProfNames j) S.width (S.pal j) S.R)
      (fun σ σ' => ArenaStW (prepMid j) (hbf j)
          ((Impl.ofArena A (chanTab S ℓp j A)).restrict
            (cluster S A π u)) σ' ∧
        σ'.vars (arenaNames (j + 1)).nS = σ.vars (arenaNames (j + 1)).nS ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ i : Fin S.width, ∀ v : Fin (childN S A π u),
          (σ'.arrs (pcPd (i : ℕ))).getD (v : ℕ) 0 ≤ S.R + 1) ∧
        (∀ c : Fin (S.pal j + 1), ∀ v : Fin (childN S A π u + 1),
          (σ'.arrs (pcPu (c : ℕ))).getD (v : ℕ) 0 ≤ S.R + 2) ∧
        Impl.ProfileTablesMS (preG S A π u) (batchFn S A π u)
          (childColR S A π u) S.R
          (fun i v => (σ'.arrs (pcPd (i : ℕ))).getD (v : ℕ) 0)
          (fun c v => (σ'.arrs (pcPu (c : ℕ))).getD (v : ℕ) 0))
      (profilesK S.width (S.pal j + 1) (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) S.R) :=
  (profilesCom_specW (B := B)
      (A := (Impl.ofArena A (chanTab S ℓp j A)).restrict (cluster S A π u))
      (nm := prepMid j) (ba := pcBi) (xb := pcXb) (vo := pcVo)
      (pdF := pcPd) (vtF := pcVt) (puF := pcPu) (batchFn S A π u)
      (prep_profNames_ok j S.width (S.pal j + 1))
      (prepWB_childN hwb A π u) (prepWB_profNs hwb A π u)
      (prepWB_R hwb) (prepWB_width hwb) (prepWB_childPal hwb hj A π u)
      (prepMid_nodup5 j) (prep_bi_notMem3 j) (prep_xb_notMemP j)
      (prep_vo_notMemP j) (fun t _ => prep_pd_notMemP j t)
      (fun c _ => prep_vt_notMemP j c)
      (fun c _ => prep_pu_notMemP j c)).pre
    (fun _ hσ =>
      ⟨hσ.1, prepScr_batchWidth hσ.2.2, hσ.2.1,
        prepScr_xb_len S ℓp hbf j π u hσ.2.2,
        prepScr_vo_len S ℓp hbf j π u hσ.2.2,
        fun t ht => prepScr_pd_len S ℓp hbf j π u hσ.2.2 t ht,
        fun c => prepScr_vt_len S ℓp hbf j π u hσ.2.2 c,
        fun c hc => prepScr_pu_len S ℓp hbf j π u hσ.2.2 c hc⟩)

open Classical in
/-- **The colour writer, at the pass's names.** `colWriteCom_machChild`
at the child's colour region, the isolation palette's row stride, and
the two table families the profiles stage just left. The colour region
allocation is the *larger* of the two demands on it
(`prepScr_col_len_write`), which is why `PrepAlloc` is sized at the
child's palette. -/
theorem prep_colWriteStage {S : Setup L} {ℓp hbf : ℕ → ℕ}
    (hwb : PrepWB S ℓp hbf n₀ B) (j : ℕ) (hj : j ≤ S.depth)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {Dp : Fin S.width → Fin (childN S A π u) → ℕ}
    {Dc : Fin (relPal (S.pal j)) → Fin (childN S A π u + 1) → ℕ}
    (hprof : Impl.ProfileTablesMS (preG S A π u) (batchFn S A π u)
      (childColR S A π u) S.R Dp Dc)
    (hpdle : ∀ (i : Fin S.width) (x : Fin (childN S A π u)), Dp i x ≤ S.R + 1)
    (hpule : ∀ (c : Fin (relPal (S.pal j))) (x : Fin (childN S A π u + 1)),
      Dc c x ≤ S.R + 2)
    {ℓc : ℕ} (chan : Fin (childN S A π u) → Fin ℓc →
      List (Fin (childN S A π u))) :
    Spec B
      (fun σ => σ.vars (arenaNames (j + 1)).nN = childN S A π u ∧
        (∀ i : Fin S.width, ∀ x : Fin (childN S A π u),
          (σ.arrs (pcPd (i : ℕ))).getD (x : ℕ) 0 = Dp i x) ∧
        (∀ c : Fin (relPal (S.pal j)), ∀ x : Fin (childN S A π u),
          (σ.arrs (pcPu (c : ℕ))).getD (x : ℕ) 0 = Dc c x.castSucc) ∧
        prepScr S ℓp hbf n₀ j σ)
      (colWriteCom (arenaNames (j + 1)).col (arenaNames (j + 1)).nN
        pcPd pcPu pcW pcDd pcVv (relPal (S.pal j)) S.width S.R)
      (fun σ σ' =>
        (∀ (x : Fin (machChild S A π u Dp Dc chan).N)
           (c' : Fin (Driver.isoPal (relPal (S.pal j)) S.width S.R)),
          (σ'.arrs (arenaNames (j + 1)).col).getD
              ((x : ℕ) * Driver.isoPal (relPal (S.pal j)) S.width S.R
                + (c' : ℕ)) 0
            = if x ∈ (machChild S A π u Dp Dc chan).col c' then 1 else 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ b, b ≠ (arenaNames (j + 1)).col → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ pcVv → y ≠ pcW → y ≠ pcDd → σ'.vars y = σ.vars y))
      (colWriteK (childN S A π u) (relPal (S.pal j)) S.width S.R) :=
  (colWriteCom_machChild (B := B) S A π u hprof hpdle hpule (prepWB_one hwb)
      prep_dd_ne_w prep_dd_ne_vv prep_w_ne_vv (prep_vv_ne_nN j)
      (prep_w_ne_nN j) (prep_dd_ne_nN j) (prepWB_R hwb)
      (by have := prepWB_childN hwb A π u; show childN S A π u < B; omega)
      (prepWB_isoRow hwb hj A π u) chan).pre
    (fun σ hσ =>
      ⟨hσ.1, prepScr_col_len_write S ℓp hbf j π u hσ.2.2.2,
        fun i => ⟨prep_pd_ne_col j (i : ℕ),
          prepScr_pd_len S ℓp hbf j π u hσ.2.2.2 (i : ℕ) i.2, hσ.2.1 i⟩,
        fun c => ⟨prep_pu_ne_col j (c : ℕ),
          le_trans (Nat.le_succ _)
            (prepScr_pu_len S ℓp hbf j π u hσ.2.2.2 (c : ℕ)
              (by have := c.2; unfold relPal at this; omega)),
          hσ.2.2.1 c⟩⟩)

open Lax12.UniformQuasiWideness (deleteVerts) in
open Classical in
/-- **The isolation, at the pass's names.** `isolateCom_specW` at the
pre-isolation child and the batch bits, writing the level's *own* CSR
pair and leaving the slot count in the pass's own cell `pcNo` — the one
cell `arenaStW_setVar_nS` then moves, because the contract forbids
`nsO = nmI.nS`. -/
theorem prep_isolateStage {S : Setup L} {ℓp hbf : ℕ → ℕ}
    (hwb : PrepWB S ℓp hbf n₀ B) (j : ℕ)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            ((Impl.ofArena A (chanTab S ℓp j A)).restrict
              (cluster S A π u)) σ ∧
          FinBitsW pcBb (Set.range (batchFn S A π u)) σ ∧
          prepScr S ℓp hbf n₀ j σ)
      (isolateCom (prepMid j) (arenaNames (j + 1)).off
        (arenaNames (j + 1)).tgt pcNo pcBb)
      (fun σ σ' =>
        ArenaStW (prepOut j) (hbf j)
          (((Impl.ofArena A (chanTab S ℓp j A)).restrict
            (cluster S A π u)).isolate (Set.range (batchFn S A π u))) σ' ∧
        σ'.vars pcNo = ∑ v : Fin (childN S A π u),
          (deleteVerts (preG S A π u) (Set.range (batchFn S A π u))).degree v ∧
        ArenaStW (prepMid j) (hbf j)
          ((Impl.ofArena A (chanTab S ℓp j A)).restrict
            (cluster S A π u)) σ' ∧
        σ'.vars (arenaNames (j + 1)).nS = σ.vars (arenaNames (j + 1)).nS ∧
        FinBitsW pcBb (Set.range (batchFn S A π u)) σ' ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (isolateK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v)) :=
  (isolateCom_specW (B := B)
      (Bar := (Impl.ofArena A (chanTab S ℓp j A)).restrict
        (cluster S A π u))
      (W := Set.range (batchFn S A π u)) (nmI := prepMid j)
      (oaO := (arenaNames (j + 1)).off) (taO := (arenaNames (j + 1)).tgt)
      (nsO := pcNo) (ba := pcBb)
      (by have := prepWB_childN hwb A π u; show childN S A π u < B; omega)
      (prepWB_childNN hwb A π u)
      (prepMid_nodup5 j) (prep_bb_notMem5 j) (prep_oaO_notMem5 j)
      (prep_taO_notMem5 j) (prep_isoOff_ne_bb j)
      (prep_isoTgt_ne_bb j) (prep_isoTgt_ne_isoOff j)
      prep_no_notMem_rs (prep_no_ne_nN j) (prep_no_ne_nS j)
      (prep_nN_notMem_rs (j + 1)) (prep_nS_notMem_rs (j + 1))).pre
    (fun σ hσ =>
      ⟨hσ.1, hσ.2.1, prepScr_bb_len S ℓp hbf j π u hσ.2.2,
        prepScr_isoOff_len S ℓp hbf j π u hσ.2.2,
        prepScr_isoTgt_len S ℓp hbf j π u hσ.2.2⟩)

end ChildStages

/-! ## §5 `prepC`'s write set, in closed form

The three write-set lemmas this campaign was missing
(`warrs_clusterRowCom`, `warrs_centreIdxCom`, `warrs_mkBatchCom`) exist
so that this can be read off the *syntax* of `prepC` rather than
threaded through fourteen postconditions. What it buys is exactly the
two frame clauses `ChildLoadPartsScr` demands and `prepScr_out`'s
`hdeep`: the pass writes the fifteen regions of `prepArrays j` and the
three profile families, and **nothing else** — no cover array, no
level-`j` region, and no deeper level's rank scratch. -/

section WriteSet

variable {L n₀ : ℕ}

/-- **Every array `prepC` stores into** is one of the pass's own fifteen
regions or a member of one of its three profile families, at the
family's own bound. -/
theorem warrs_prepC (S : Setup L) (ℓp hbf : ℕ → ℕ) (co cm : ℕ → String)
    (j : ℕ) :
    ∀ a ∈ (prepC S ℓp hbf co cm j).warrs,
      a ∈ prepArrays j ∨ (∃ t < S.width, a = pcPd t)
        ∨ (∃ c < S.pal j, a = pcVt c) ∨ ∃ c < S.pal j + 1, a = pcPu c := by
  intro a ha
  have he : (prepC S ℓp hbf co cm j).warrs
      = [pcLa] ++ ([] ++ ([] ++
        ([pcRa j, pcOi, pcTi, pcOi, (arenaNames (j + 1)).col,
          (arenaNames (j + 1)).up, (arenaNames (j + 1)).hist,
          (arenaNames (j + 1)).hist, pcRa j] ++ ([] ++
        ([pcBb, pcBb, pcBb, pcBi, pcBi] ++ ([] ++
        ([pcDa, pcDa, pcDa] ++ ([] ++
        ([pcPa, pcPa, (arenaNames (j + 1)).hist, (arenaNames (j + 1)).hist,
          (arenaNames (j + 1)).hist, (arenaNames (j + 1)).hist] ++
        ((profilesCom (prepProfNames j) S.width (S.pal j) S.R).warrs ++
        ((colWriteCom (arenaNames (j + 1)).col (arenaNames (j + 1)).nN
            pcPd pcPu pcW pcDd pcVv (relPal (S.pal j)) S.width S.R).warrs ++
        ([(arenaNames (j + 1)).off, (arenaNames (j + 1)).tgt,
          (arenaNames (j + 1)).off] ++ [])))))))))))) := rfl
  rw [he] at ha
  simp only [List.nil_append, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  by_cases hp : a ∈ (profilesCom (prepProfNames j) S.width (S.pal j) S.R).warrs
  · rcases warrs_profilesCom_subset (prepProfNames j) S.width (S.pal j) S.R a hp
      with h1 | h1 | ⟨t, ht, h1⟩ | ⟨c, hc, h1⟩ | ⟨c, hc, h1⟩
    · exact Or.inl (by rw [h1]; simp [prepArrays, prepProfNames])
    · exact Or.inl (by rw [h1]; simp [prepArrays, prepProfNames])
    · exact Or.inr (Or.inl ⟨t, ht, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨c, hc, h1⟩))
  by_cases hc : a ∈ (colWriteCom (arenaNames (j + 1)).col
      (arenaNames (j + 1)).nN pcPd pcPu pcW pcDd pcVv
      (relPal (S.pal j)) S.width S.R).warrs
  · exact Or.inl (by
      rw [warrs_colWriteCom _ _ _ _ _ _ _ _ _ _ a hc]; simp [prepArrays])
  refine Or.inl ?_
  simp only [prepArrays, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- **The pass never touches an array outside its own pool** — the
membership side condition `Spec.frameA` and `Run.frame_arr` are consumed
with, and the closed form `ChildLoadPartsScr`'s array frame clause
wants. -/
theorem prepC_notMem_warrs (S : Setup L) (ℓp hbf : ℕ → ℕ)
    (co cm : ℕ → String) (j : ℕ) {b : String} (h1 : b ∉ prepArrays j)
    (h2 : ∀ t, b ≠ pcPd t) (h3 : ∀ c, b ≠ pcVt c) (h4 : ∀ c, b ≠ pcPu c) :
    b ∉ (prepC S ℓp hbf co cm j).warrs := by
  intro hb
  rcases warrs_prepC S ℓp hbf co cm j b hb with h | ⟨t, -, h⟩ | ⟨c, -, h⟩
    | ⟨c, -, h⟩
  · exact h1 h
  · exact h2 t h
  · exact h3 c h
  · exact h4 c h

/-- **`prepScr_out`'s `hdeep`, discharged from the syntax.** A rank
scratch of a level *strictly below* `j` is outside the write set, so its
clean window rides the pass's own frame — which is the whole reason the
rank scratch is level-indexed. -/
theorem prepC_frame_deep (S : Setup L) (ℓp hbf : ℕ → ℕ)
    (co cm : ℕ → String) (j i : ℕ) (hij : j < i) :
    pcRa i ∉ (prepC S ℓp hbf co cm j).warrs := by
  refine prepC_notMem_warrs S ℓp hbf co cm j ?_ ?_ ?_ ?_
  · simp only [prepArrays, pcLa, pcRa, pcOi, pcTi, pcBb, pcBi, pcDa, pcPa,
      pcXb, pcVo, arenaNames, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    exact ⟨lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_level_ne (by decide) (by omega),
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _,
      lv_ne_of_base_ne (by decide) (by decide) _ _⟩
  all_goals
    intro t
    simp only [pcRa, pcPd, pcVt, pcPu]
    exact lv_ne_of_base_ne (by decide) (by decide) _ _

/-- **The level-`j` regions are outside the write set too** — the
`levelArrays j` half of `ChildLoadPartsScr`'s array frame clause. Every
clash is a base clash with the pass's `pc.·`/`pf.·` pool or a level
clash between `j` and `j + 1`. -/
theorem prepC_frame_level (S : Setup L) (ℓp hbf : ℕ → ℕ)
    (co cm : ℕ → String) (j : ℕ) {b : String} (hb : b ∈ levelArrays j) :
    b ∉ (prepC S ℓp hbf co cm j).warrs := by
  simp only [levelArrays, List.mem_cons, List.not_mem_nil, or_false] at hb
  refine prepC_notMem_warrs S ℓp hbf co cm j ?_ ?_ ?_ ?_
  · simp only [prepArrays, pcLa, pcRa, pcOi, pcTi, pcBb, pcBi, pcDa, pcPa,
      pcXb, pcVo, arenaNames, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_level_ne (by decide) (by omega),
        lv_ne_of_level_ne (by decide) (by omega),
        lv_ne_of_level_ne (by decide) (by omega),
        lv_ne_of_level_ne (by decide) (by omega),
        lv_ne_of_level_ne (by decide) (by omega)⟩
  all_goals
    intro t
    simp only [pcPd, pcVt, pcPu]
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact lv_ne_of_base_ne (by decide) (by decide) _ _

/-- **The cover's three arrays are outside the write set** — the
`ca/co/cm` half of the same clause, off `PrepCoverNames`. -/
theorem prepC_frame_cover {ca co cm : ℕ → String} (S : Setup L)
    (ℓp hbf : ℕ → ℕ) (j : ℕ) (hcn : PrepCoverNames ca co cm j)
    {b : String} (hb : b ∈ ([ca j, co j, cm j] : List String)) :
    b ∉ (prepC S ℓp hbf co cm j).warrs :=
  prepC_notMem_warrs S ℓp hbf co cm j (hcn.fixed b hb) (hcn.pd b hb)
    (hcn.vt b hb) (hcn.pu b hb)

end WriteSet

/-! ## §6 The axiom profile

Nothing here quotes `headlineSetup`, so the expected profile is the
ambient three. -/

#print axioms prepCoverNames_exists
#print axioms prepCoverNames_la_cm
#print axioms prepWB_childN
#print axioms prepWB_childNN
#print axioms prepWB_childPal
#print axioms prep_col_lt
#print axioms prep_clusterRowStage
#print axioms prep_centreIdxStage
#print axioms prep_bfsStage
#print axioms prep_supportsStage
#print axioms prep_profilesStage
#print axioms prep_colWriteStage
#print axioms prep_isolateStage
#print axioms warrs_prepC
#print axioms prepC_notMem_warrs
#print axioms prepC_frame_deep
#print axioms prepC_frame_level
#print axioms prepC_frame_cover

end Lax3Proofs.Prog
