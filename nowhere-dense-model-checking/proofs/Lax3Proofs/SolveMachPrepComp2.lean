import Lax3Proofs.SolveMachPrepComp

/-!
# F6c12 (residual 1) — the child-building pass: the composition's
# binding side conditions

`SolveMachPrepComp` fixed the pass's name pool, its command `prepC`, its
budget, the level's concrete scratch descriptor `prepScr`, and the two
inter-stage seams no landed object provides. What stands between those
and **`ChildLoadPartsScrAll`** is the fourteen-step `Spec.seq` chain
itself; this file supplies the part of that chain which is *not* state
threading — the side conditions each stage's contract binds its caller
to, discharged once, in the exact shapes the contracts ask for.

Three families, and they are exactly the three that have cost this
campaign a wave each:

* **§2–§3 the allocations.** An allocation clause in a precondition is a
  binding requirement on whoever establishes it and is invisible in the
  contract text; IMP+ `store` is `List.set`, so no run repairs one. §3
  derives *every* allocation clause of *every* stage from
  `prepScr S ℓp hbf n₀ j σ` alone — the audit that says `PrepAlloc` is
  complete rather than merely plausible.
* **§4 the names.** The nine contracts between them ask for a
  `ProfNames.Ok`, eight `∉ <stage scalar pool>` clauses, six
  passive-region freshness lists and some sixty pairwise disequalities.
  At the pool of `SolveMachPrepComp` §1 every one is a base clash or a
  level clash, so all of them are `decide`-able — but they still have to
  be *stated* at the right names, which is what §4 does.
* **§5 the word size.** `ChildLoadPartsScr` relates `B` to nothing.
  Every one of the nine contracts asks for word bounds (`A.N < B`,
  `A.N * A.N < B`, `A.N * Λc < B`, …), and the residual's own statement
  offers none — the same shape as the campaign's `AdjDeleteIn` finding,
  where the landed residual was *false* for want of a `B` relation and
  was repaired by one added hypothesis. `PrepWB` is that hypothesis
  bundle for this pass, `prepWB_*` are the per-stage bounds it yields,
  and `prepWB_exists` shows it is satisfiable rather than vacuous.

## What this file does **not** do

It does not discharge `ChildLoadPartsScr`. What is left after §2–§5 is
the state threading: fourteen `Spec.seq` steps whose `hmid` obligations
carry each stage's deliverable forward through the next stage's frame.
Nothing here presumes a particular order for that chain — every clause
below is read off one contract in isolation.

## Hazards honoured

No program, stage, radius or budget is defined or moved. In particular
no term of any shape enters `prepPassK`, so the `Θ(A.N²)` scratch trap
that `restrictK`'s missing `A.N` term exists to avoid is untouched.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver


/-! ## §2 The pass's dimensions, bounded at the root

Every allocation clause `PrepAlloc` carries is stated at the **root's**
`n₀`; every allocation clause a stage's precondition asks for is stated
at that stage's own, data-dependent dimension. This section is the
bridge — four monotonicity facts and nothing else — and it is what makes
§8's adequacy audit mechanical. -/

section Dimensions

variable {L : ℕ}

/-- The palette grows down the recursion: `isoPal` appends the marker
slot and the two profile blocks to the parent's. Needed because
`restrictCom_specW` fills the *child's* colour region at the **parent's**
palette while `PrepAlloc` sizes it at the child's. -/
theorem prep_pal_le_succ (S : Setup L) (j : ℕ) : S.pal j ≤ S.pal (j + 1) := by
  rw [Setup.pal_succ]
  unfold isoPal relPal
  omega

/-- A cluster is a subset of the carrier, so the child's carrier never
exceeds the parent's. -/
theorem prep_childN_le {n₀ : ℕ} (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : childN S A π u ≤ A.N := by
  have h := Set.ncard_le_ncard (Set.subset_univ (cluster S A π u))
    Set.finite_univ
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h

/-- …and therefore never exceeds the root's. -/
theorem prep_childN_le_root {n₀ : ℕ} (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : childN S A π u ≤ n₀ :=
  le_trans (prep_childN_le S A π u) (arenaN_le A)

open Classical in
/-- **A degree sum never exceeds the square of its carrier.**
`ArenaStW.ns_le_sq` says this about the *cell*; the stages' allocation
clauses ask about the number itself, at arenas no state names
(`A.restrict S`, `deleteVerts …`), so it is needed free-standing. This
is the only fact that turns `PrepAlloc`'s `n₀ * n₀` into every CSR
target allocation the pass asks for. -/
theorem prep_sum_degree_le_sq {N : ℕ} (G : SimpleGraph (Fin N)) :
    ∑ v : Fin N, G.degree v ≤ N * N := by
  calc ∑ v : Fin N, G.degree v
      ≤ ∑ _v : Fin N, N := by
        refine Finset.sum_le_sum fun v _ => ?_
        have := G.degree_lt_card_verts v
        simp only [Fintype.card_fin] at this
        omega
    _ = N * N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- A colour class is a subset of the carrier. -/
theorem prep_col_ncard_le {N Λ : ℕ} (col : Coloring N Λ) (c : Fin Λ) :
    (col c).ncard ≤ N := by
  have h := Set.ncard_le_ncard (Set.subset_univ (col c)) Set.finite_univ
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h

end Dimensions

/-! ## §3 The allocation audit — every stage's clause, from the descriptor

**The trap, audited stage by stage.** An allocation clause in a stage's
precondition is a binding requirement on whoever establishes it, and
IMP+ `store` is `List.set`, so no run can repair one: `PrepAlloc` is
the complete list, and this section is the proof that it *is* complete
— each of the nine stages' allocation clauses derived from
`prepScr S ℓp hbf n₀ j σ` alone, at the stage's own data-dependent
dimensions.

Nothing here is about the composition order: every clause below is read
off the stage's precondition and discharged against the descriptor, so
the audit is valid whatever order the chain ends up in. Two of them are
the ones that would have been missed:

* the child's colour region must hold `X.ncard · S.pal j` for
  `restrictCom_specW` *and* `childN · S.pal (j+1)` for
  `colWriteCom_machChild` — the second is the larger, and
  `prep_pal_le_succ` is why one allocation serves both;
* the batch index region's clause is an **equality**
  (`prepScr_batchWidth`), not a bound, and is therefore the one clause
  a longer allocation would *break*. -/

section Adequacy

variable {L n₀ : ℕ}

variable (S : Setup L) (ℓp hbf : ℕ → ℕ) (j : ℕ) {A : Arena (S.pal j) n₀}
  (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {σ : Env}

/-- `restrictCom_specW`'s scratch allocation. -/
theorem prepScr_ra_len (h : prepScr S ℓp hbf n₀ j σ) :
    A.N ≤ (σ.arrs (pcRa j)).length :=
  le_trans (arenaN_le A) (prepScr_alloc h).2.2.2.2.2.2.2.2.2.1

/-- `clusterRowCom_spec`'s cluster-region allocation. -/
theorem prepScr_la_len (h : prepScr S ℓp hbf n₀ j σ) :
    (cluster S A π u).ncard ≤ (σ.arrs pcLa).length :=
  le_trans (prep_childN_le_root S A π u) (prepScr_alloc h).2.2.2.2.2.2.2.2.1

/-- `restrictCom_specW`'s child-offset allocation. -/
theorem prepScr_oi_len (h : prepScr S ℓp hbf n₀ j σ) :
    (cluster S A π u).ncard + 1 ≤ (σ.arrs pcOi).length := by
  have h1 := (prepScr_alloc h).2.2.2.2.2.2.1
  have h2 := prep_childN_le_root S A π u
  show childN S A π u + 1 ≤ _
  omega

open Classical in
/-- `restrictCom_specW`'s child-target allocation, at the pre-isolation
child's own degree sum. -/
theorem prepScr_ti_len (h : prepScr S ℓp hbf n₀ j σ) :
    (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
      ≤ (σ.arrs pcTi).length := by
  refine le_trans (le_trans (prep_sum_degree_le_sq (preG S A π u)) ?_)
    (prepScr_alloc h).2.2.2.2.2.2.2.1
  exact Nat.mul_le_mul (prep_childN_le_root S A π u)
    (prep_childN_le_root S A π u)

/-- `restrictCom_specW`'s child-colour allocation, at the **parent's**
palette — the smaller of the two demands on this region. -/
theorem prepScr_col_len_restrict (h : prepScr S ℓp hbf n₀ j σ) :
    (cluster S A π u).ncard * S.pal j
      ≤ (σ.arrs (arenaNames (j + 1)).col).length := by
  refine le_trans (Nat.mul_le_mul (prep_childN_le_root S A π u)
    (prep_pal_le_succ S j)) (prepScr_alloc h).2.2.1

/-- `colWriteCom_machChild`'s colour allocation, at the **isolation**
palette — the larger demand, and the one `PrepAlloc` is sized by:
`isoPal (relPal (S.pal j)) S.width S.R` *is* `S.pal (j+1)`. -/
theorem prepScr_col_len_write (h : prepScr S ℓp hbf n₀ j σ) :
    childN S A π u * isoPal (relPal (S.pal j)) S.width S.R
      ≤ (σ.arrs (arenaNames (j + 1)).col).length := by
  rw [← Setup.pal_succ]
  exact le_trans (Nat.mul_le_mul_right _ (prep_childN_le_root S A π u))
    (prepScr_alloc h).2.2.1

/-- `restrictCom_specW`'s child-renaming allocation. -/
theorem prepScr_up_len (h : prepScr S ℓp hbf n₀ j σ) :
    (cluster S A π u).ncard ≤ (σ.arrs (arenaNames (j + 1)).up).length :=
  le_trans (prep_childN_le_root S A π u) (prepScr_alloc h).2.2.2.1

/-- `restrictCom_specW`'s child-channel allocation. -/
theorem prepScr_hist_len (h : prepScr S ℓp hbf n₀ j σ) :
    (cluster S A π u).ncard * ℓp j * (hbf j + 1)
      ≤ (σ.arrs (arenaNames (j + 1)).hist).length :=
  le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (prep_childN_le_root S A π u))) (prepScr_alloc h).2.2.2.2.1

/-- `mkBatchCom_batch`'s and `isolateCom_specW`'s bit-region
allocation. -/
theorem prepScr_bb_len (h : prepScr S ℓp hbf n₀ j σ) :
    childN S A π u ≤ (σ.arrs pcBb).length :=
  le_trans (prep_childN_le_root S A π u)
    (prepScr_alloc h).2.2.2.2.2.2.2.2.2.2.1

/-- `bfsCom_specW`'s distance allocation. -/
theorem prepScr_da_len (h : prepScr S ℓp hbf n₀ j σ) :
    childN S A π u ≤ (σ.arrs pcDa).length :=
  le_trans (prep_childN_le_root S A π u)
    (prepScr_alloc h).2.2.2.2.2.2.2.2.2.2.2.1

/-- `supportsCom_specW`'s least-parent allocation. -/
theorem prepScr_pa_len (h : prepScr S ℓp hbf n₀ j σ) :
    childN S A π u ≤ (σ.arrs pcPa).length :=
  le_trans (prep_childN_le_root S A π u)
    (prepScr_alloc h).2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `profilesCom_specW`'s class-bit allocation. -/
theorem prepScr_xb_len (h : prepScr S ℓp hbf n₀ j σ) :
    childN S A π u ≤ (σ.arrs pcXb).length :=
  le_trans (prep_childN_le_root S A π u)
    (prepScr_alloc h).2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `profilesCom_specW`'s `vsrc`-offset allocation. -/
theorem prepScr_vo_len (h : prepScr S ℓp hbf n₀ j σ) :
    childN S A π u + 2 ≤ (σ.arrs pcVo).length := by
  have h1 := (prepScr_alloc h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 := prep_childN_le_root S A π u
  omega

/-- `profilesCom_specW`'s batch-table allocations. -/
theorem prepScr_pd_len (h : prepScr S ℓp hbf n₀ j σ) :
    ∀ t < S.width, childN S A π u ≤ (σ.arrs (pcPd t)).length :=
  fun t ht => le_trans (prep_childN_le_root S A π u)
    ((prepScr_alloc h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht)

open Classical in
/-- `profilesCom_specW`'s per-class `vsrc` allocations — the only
data-dependent windows the stage has (`ns + 2·|col c|`). -/
theorem prepScr_vt_len (h : prepScr S ℓp hbf n₀ j σ) :
    ∀ c : Fin (S.pal j),
      (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
          + 2 * (childCol0 S A π u c).ncard
        ≤ (σ.arrs (pcVt (c : ℕ))).length := by
  intro c
  have hbase := (prepScr_alloc h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (c : ℕ) c.2
  have hN := prep_childN_le_root S A π u
  have hsum : (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
      ≤ n₀ * n₀ :=
    le_trans (prep_sum_degree_le_sq (preG S A π u)) (Nat.mul_le_mul hN hN)
  have hcol : (childCol0 S A π u c).ncard ≤ n₀ :=
    le_trans (prep_col_ncard_le (childCol0 S A π u) c) hN
  omega

/-- `profilesCom_specW`'s virtual-source table allocations — one per
relativised class, the marker's included. -/
theorem prepScr_pu_len (h : prepScr S ℓp hbf n₀ j σ) :
    ∀ c < S.pal j + 1, childN S A π u + 1 ≤ (σ.arrs (pcPu c)).length := by
  intro c hc
  have h1 := (prepScr_alloc h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 c hc
  have h2 := prep_childN_le_root S A π u
  omega

/-- `isolateCom_specW`'s output-offset allocation: the isolation keeps
the carrier, so this is the child's own `N + 1`. -/
theorem prepScr_isoOff_len (h : prepScr S ℓp hbf n₀ j σ) :
    childN S A π u + 1 ≤ (σ.arrs (arenaNames (j + 1)).off).length := by
  have h1 := (prepScr_alloc h).1
  have h2 := prep_childN_le_root S A π u
  omega

open Lax12.UniformQuasiWideness (deleteVerts) in
open Classical in
/-- `isolateCom_specW`'s output-target allocation, at the isolated
degree sum. -/
theorem prepScr_isoTgt_len (h : prepScr S ℓp hbf n₀ j σ) :
    (∑ v : Fin (childN S A π u),
        (deleteVerts (preG S A π u) (Set.range (batchFn S A π u))).degree v)
      ≤ (σ.arrs (arenaNames (j + 1)).tgt).length := by
  refine le_trans (le_trans (prep_sum_degree_le_sq _) ?_)
    (prepScr_alloc h).2.1
  exact Nat.mul_le_mul (prep_childN_le_root S A π u)
    (prep_childN_le_root S A π u)

end Adequacy

/-! ## §4 The name discipline, in the shapes the contracts ask for

`SolveMachPrepComp` §6 discharged the five `Nodup`/`Pairwise` bundles
and the six `∉ <five regions>` lists. What the remaining contracts ask
for beyond those is: eight `∉ <stage scalar pool>` clauses, the
profiles stage's `ProfNames.Ok` and its six passive-region freshness
lists, and the pairwise cell disequalities of four stages. All of them
are here, at the pass's own names.

The one stage whose name burden is not worth restating clause by clause
is the batch builder — thirty-two disequalities — so it appears instead
as `prep_mkBatchStage`, the contract already instantiated at the pass's
names. -/

section StageNames

/-- Freshness against a two-name list. -/
theorem prep_notMem2 {x a b : String} (ha : x ≠ a) (hb : x ≠ b) :
    x ∉ ([a, b] : List String) := by simp [ha, hb]

/-- Freshness against a three-name list. -/
theorem prep_notMem3 {x a b c : String} (ha : x ≠ a) (hb : x ≠ b)
    (hc : x ≠ c) : x ∉ ([a, b, c] : List String) := by simp [ha, hb, hc]

/-- Freshness against a four-name list. -/
theorem prep_notMem4 {x a b c d : String} (ha : x ≠ a) (hb : x ≠ b)
    (hc : x ≠ c) (hd : x ≠ d) : x ∉ ([a, b, c, d] : List String) := by
  simp [ha, hb, hc, hd]

/-! ### The four stage scalar pools

Each stage forbids its own scratch cells to the arena cells it is
handed. Every pool is a concrete list of four-character untagged
literals, so `lv_notMem` turns the clause into `decide`. -/

theorem prep_nN_notMem_rs (k : ℕ) : (arenaNames k).nN ∉ rsScalars :=
  lv_notMem (s := "sv.n") (by decide) k

theorem prep_nS_notMem_rs (k : ℕ) : (arenaNames k).nS ∉ rsScalars :=
  lv_notMem (s := "sv.m") (by decide) k

theorem prep_nN_notMem_bf (k : ℕ) : (arenaNames k).nN ∉ bfScalars :=
  lv_notMem (s := "sv.n") (by decide) k

theorem prep_nS_notMem_bf (k : ℕ) : (arenaNames k).nS ∉ bfScalars :=
  lv_notMem (s := "sv.m") (by decide) k

theorem prep_nN_notMem_sp (k : ℕ) : (arenaNames k).nN ∉ spScalars :=
  lv_notMem (s := "sv.n") (by decide) k

theorem prep_nS_notMem_sp (k : ℕ) : (arenaNames k).nS ∉ spScalars :=
  lv_notMem (s := "sv.m") (by decide) k

theorem prep_nN_notMem_prof (k : ℕ) : (arenaNames k).nN ∉ profScalars :=
  lv_notMem (s := "sv.n") (by decide) k

theorem prep_nS_notMem_prof (k : ℕ) : (arenaNames k).nS ∉ profScalars :=
  lv_notMem (s := "sv.m") (by decide) k

/-- `isolateCom_specW`'s output cell misses the restrict pool — the
stage's `hs1`. -/
theorem prep_no_notMem_rs : pcNo ∉ rsScalars := lv_notMem (by decide) 0

/-! ### The arena cells, pairwise -/

/-- The level's own two cells differ — `restrictCom_specW`'s `hCns`,
and `arenaStW_setVar_nS`'s `hnn`. -/
theorem prep_nN_ne_nS (k : ℕ) : (arenaNames k).nN ≠ (arenaNames k).nS :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `restrictCom_specW`'s `hPn1`: the two levels' carrier cells differ
by their level tag. -/
theorem prep_pnN_ne_cnN (j : ℕ) :
    (arenaNames j).nN ≠ (arenaNames (j + 1)).nN :=
  lv_ne_of_level_ne (by decide) (by omega)

/-- `restrictCom_specW`'s `hPn2`. -/
theorem prep_pnN_ne_cnS (j : ℕ) :
    (arenaNames j).nN ≠ (arenaNames (j + 1)).nS :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `restrictCom_specW`'s `hPs1`. -/
theorem prep_pnS_ne_cnN (j : ℕ) :
    (arenaNames j).nS ≠ (arenaNames (j + 1)).nN :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `restrictCom_specW`'s `hPs2`. -/
theorem prep_pnS_ne_cnS (j : ℕ) :
    (arenaNames j).nS ≠ (arenaNames (j + 1)).nS :=
  lv_ne_of_level_ne (by decide) (by omega)

/-- `isolateCom_specW`'s `hs2`. -/
theorem prep_no_ne_nN (j : ℕ) : pcNo ≠ (arenaNames (j + 1)).nN :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `isolateCom_specW`'s `hs3`. -/
theorem prep_no_ne_nS (j : ℕ) : pcNo ≠ (arenaNames (j + 1)).nS :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-! ### The cluster-row copy and the connector scan -/

/-- `clusterRowCom_spec`'s `hct_ck` and `centreIdxCom_centreChild`'s. -/
theorem prep_ct_ne_rsk : pcCt ≠ "rs.k" := lv_ne_lit (by decide) (by decide) 0

/-- `clusterRowCom_spec`'s `hct_cb`. -/
theorem prep_ct_ne_cb : pcCt ≠ pcCb := lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `clusterRowCom_spec`'s `hcb_ck`. -/
theorem prep_cb_ne_rsk : pcCb ≠ "rs.k" := lv_ne_lit (by decide) (by decide) 0

/-- `clusterRowCom_spec`'s `hcu_cb`. -/
theorem prep_ctr_ne_cb (j : ℕ) : ctrName j ≠ pcCb :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `centreIdxCom_centreChild`'s `hct_cu`. -/
theorem prep_ct_ne_ctr (j : ℕ) : pcCt ≠ ctrName j :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `centreIdxCom_centreChild`'s `hct_cc`. -/
theorem prep_ct_ne_cc : pcCt ≠ pcCc := lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `centreIdxCom_centreChild`'s `hcc_ck`. -/
theorem prep_cc_ne_rsk : pcCc ≠ "rs.k" := lv_ne_lit (by decide) (by decide) 0

/-- `centreIdxCom_centreChild`'s `hcc_cu`. -/
theorem prep_cc_ne_ctr (j : ℕ) : pcCc ≠ ctrName j :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-! ### The BFS, the supports pass and the isolation -/

/-- `bfsCom_specW`'s `hot`, at the pre-isolation family. -/
theorem prep_ti_ne_oi : pcTi ≠ pcOi := lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `supportsCom_specW`'s `hda_pa`. -/
theorem prep_da_ne_pa : pcDa ≠ pcPa := lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `isolateCom_specW`'s `hoaO_ba`. -/
theorem prep_isoOff_ne_bb (j : ℕ) : (arenaNames (j + 1)).off ≠ pcBb :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `isolateCom_specW`'s `htaO_ba`. -/
theorem prep_isoTgt_ne_bb (j : ℕ) : (arenaNames (j + 1)).tgt ≠ pcBb :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- `isolateCom_specW`'s `htaO_oaO`. -/
theorem prep_isoTgt_ne_isoOff (j : ℕ) :
    (arenaNames (j + 1)).tgt ≠ (arenaNames (j + 1)).off :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-! ### The colour writer's three cursors -/

theorem prep_dd_ne_w : pcDd ≠ pcW := lv_ne_of_base_ne (by decide) (by decide) _ _
theorem prep_dd_ne_vv : pcDd ≠ pcVv := lv_ne_of_base_ne (by decide) (by decide) _ _
theorem prep_w_ne_vv : pcW ≠ pcVv := lv_ne_of_base_ne (by decide) (by decide) _ _

theorem prep_vv_ne_nN (j : ℕ) : pcVv ≠ (arenaNames (j + 1)).nN :=
  lv_ne_of_base_ne (by decide) (by decide) _ _
theorem prep_w_ne_nN (j : ℕ) : pcW ≠ (arenaNames (j + 1)).nN :=
  lv_ne_of_base_ne (by decide) (by decide) _ _
theorem prep_dd_ne_nN (j : ℕ) : pcDd ≠ (arenaNames (j + 1)).nN :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-- The two table families miss the colour region — `colWriteCom`'s
per-table freshness, and the half of `colWrite_tables_of_profiles` that
is not `rfl`. -/
theorem prep_pd_ne_col (j : ℕ) (t : ℕ) :
    pcPd t ≠ (arenaNames (j + 1)).col :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

theorem prep_pu_ne_col (j : ℕ) (c : ℕ) :
    pcPu c ≠ (arenaNames (j + 1)).col :=
  lv_ne_of_base_ne (by decide) (by decide) _ _

/-! ### The profiles stage -/

/-- `profilesCom_specW`'s `hba3`: the batch index region misses the
three read-only regions it is handed beside. -/
theorem prep_bi_notMem3 (j : ℕ) :
    pcBi ∉ ([pcOi, pcTi, (arenaNames (j + 1)).col] : List String) :=
  prep_notMem3 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)

/-- `profilesCom_specW`'s `hxbP`: the two regions the stage never reads
are the ones the *pass* still needs intact. -/
theorem prep_xb_notMemP (j : ℕ) :
    pcXb ∉ ([(arenaNames (j + 1)).up, (arenaNames (j + 1)).hist] :
      List String) :=
  prep_notMem2 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)

/-- `profilesCom_specW`'s `hvoP`. -/
theorem prep_vo_notMemP (j : ℕ) :
    pcVo ∉ ([(arenaNames (j + 1)).up, (arenaNames (j + 1)).hist] :
      List String) :=
  prep_notMem2 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)

/-- `profilesCom_specW`'s `hpdP`. -/
theorem prep_pd_notMemP (j t : ℕ) :
    pcPd t ∉ ([(arenaNames (j + 1)).up, (arenaNames (j + 1)).hist] :
      List String) :=
  prep_notMem2 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)

/-- `profilesCom_specW`'s `hvtP`. -/
theorem prep_vt_notMemP (j c : ℕ) :
    pcVt c ∉ ([(arenaNames (j + 1)).up, (arenaNames (j + 1)).hist] :
      List String) :=
  prep_notMem2 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)

/-- `profilesCom_specW`'s `hpuP`. -/
theorem prep_pu_notMemP (j c : ℕ) :
    pcPu c ∉ ([(arenaNames (j + 1)).up, (arenaNames (j + 1)).hist] :
      List String) :=
  prep_notMem2 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)

/-- **`profilesCom_specW`'s whole name bundle**, at the pass's family —
twenty-one clauses, every one a base clash or an `lv` injectivity, and
uniform in the batch width and class count. This is the single largest
side condition the composition owes. -/
theorem prep_profNames_ok (j mb Lp : ℕ) : ProfNames.Ok (prepProfNames j) mb Lp
    where
  xb_ro := prep_notMem4 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
  vo_ro := prep_notMem4 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
  pd_ro := fun _ _ => prep_notMem4 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
  vt_ro := fun _ _ => prep_notMem4 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
  pu_ro := fun _ _ => prep_notMem4 (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
    (lv_ne_of_base_ne (by decide) (by decide) _ _)
  xb_vo := lv_ne_of_base_ne (by decide) (by decide) _ _
  pd_xb := fun _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  pd_vo := fun _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  vt_xb := fun _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  vt_vo := fun _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  pu_xb := fun _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  pu_vo := fun _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  pd_inj := fun _ _ _ _ h => (lv_inj (by rfl) h).2
  pu_inj := fun _ _ _ _ h => (lv_inj (by rfl) h).2
  vt_inj := fun _ _ _ _ h => (lv_inj (by rfl) h).2
  vt_pu := fun _ _ _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  pd_pu := fun _ _ _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  pd_vt := fun _ _ _ _ => lv_ne_of_base_ne (by decide) (by decide) _ _
  nN_scr := prep_nN_notMem_prof (j + 1)
  nS_scr := prep_nS_notMem_prof (j + 1)

end StageNames

/-! ## §5 The word size — the relation the residual does not state

**A finding, in the campaign's established shape.** `ChildLoadPartsScr`
(and the landed `ChildLoadParts` it strengthens) quantifies over every
level `j`, every admissible arena `A` and every centre `u`, and relates
none of them to the word bound `B`. Every one of the nine stage
contracts, on the other hand, asks for word bounds: `restrictCom_specW`
for five (`A.N < B`, `A.N * A.N < B`, `n₀ < B`, `A.N * Λc < B`,
`A.N * ℓp * (hb+1) < B`), `profilesCom_specW` for five more, and so on
down the chain. No proof routed through those contracts can avoid the
relation, so a discharger must carry it as a hypothesis — and at a
descriptor that is genuinely inhabited (`prepScr` is one) the residual
as literally stated is out of reach, since `ChildLoadPartsScrAll`
quantifies over every `q`, at `q = 0` the bound `mcB 0 x` is `0`, and
`Run 0` derives nothing at all. Whether it is outright **false** there
is a statement about the *instantiation*, not about the definition —
the parametric `Scr := fun _ _ => False` makes the residual vacuously
true — and this file does not settle it; it supplies the hypothesis
instead.

This is exactly the `AdjDeleteIn` shape (`plans/…/execution-ledger.md`,
F6c12 residual 6): a landed residual that "quantifies over every `N` …
and relates none to `B`", found **false**, and repaired by one added
hypothesis (`AdjDeleteInW`, `N + N² < B`) discharged at `mcB` by the
composition layer. `PrepWB` is that hypothesis for this pass.

Two things make it an honest hypothesis rather than a hole:

* `prepWB_exists` — it is satisfiable, so no theorem carrying it is
  vacuous;
* it is stated at the **root** carrier `n₀` and the schedule alone, so
  it is uniform in `j`, `A` and `u` — which is what
  `ChildLoadPartsScr`'s internal quantifiers require — while
  `mcB q x = q(|x|+1)²` is quadratic in the input length, so at F7's
  instantiation it becomes a lower bound on the schedule constant `q`,
  the same shape `sq_lt_mcB'` already discharges elsewhere.
-/

section WordSize

variable {L : ℕ}

/-- **The word-size bundle the composition owes.** Four clauses at the
root's dimensions and the schedule's; §5's derived lemmas turn them into
every `< B` side condition the nine stage contracts ask for.

`carrier` is sized for the largest single quantity any stage stores —
a slot count `≤ n₀²` plus the profiles stage's `2·N + 1` offset pad;
`palette` for the isolation palette's row stride; `channel` for the
channel region's; `sched` for the constants (`ℓp`, `hb`, the batch
width, the radius `2R`, and the level numeral the round-count pin makes
a compile-time constant). -/
structure PrepWB (S : Setup L) (ℓp hbf : ℕ → ℕ) (n₀ B : ℕ) : Prop where
  /-- Everything quadratic in the root carrier, with the offset pad. -/
  carrier : n₀ * n₀ + 2 * n₀ + 3 < B
  /-- The isolation palette's row stride, at the root carrier. -/
  palette : ∀ i, i ≤ S.depth → n₀ * S.pal (i + 1) < B
  /-- The channel region's, at the root carrier. -/
  channel : ∀ i, i ≤ S.depth → n₀ * ℓp i * (hbf i + 1) < B
  /-- The schedule's own constants, and the level numeral. -/
  sched : ∀ i, i ≤ S.depth → ℓp i + hbf i + S.width + 2 * S.R + i + 4 < B

variable {S : Setup L} {ℓp hbf : ℕ → ℕ} {n₀ B : ℕ}

/-- `1 < B` — `colWriteCom_machChild`'s `hone`, and what every `.lit`
load needs. -/
theorem prepWB_one (h : PrepWB S ℓp hbf n₀ B) : 1 < B := by
  have := h.carrier; omega

/-- `n₀ < B` — `restrictCom_specW`'s `hn0B`. -/
theorem prepWB_root (h : PrepWB S ℓp hbf n₀ B) : n₀ + 2 < B := by
  have := h.carrier
  have : n₀ ≤ n₀ * n₀ + 2 * n₀ := by omega
  omega

/-- Every arena's carrier is below the bound. -/
theorem prepWB_N (h : PrepWB S ℓp hbf n₀ B) {Λ : ℕ} (A : Arena Λ n₀) :
    A.N + 2 < B := by
  have h1 := prepWB_root h
  have h2 := arenaN_le A
  omega

/-- …and so is its square — `restrictCom_specW`'s `hNNB`. -/
theorem prepWB_NN (h : PrepWB S ℓp hbf n₀ B) {Λ : ℕ} (A : Arena Λ n₀) :
    A.N * A.N < B := by
  have h1 := h.carrier
  have h2 := arenaN_le A
  have : A.N * A.N ≤ n₀ * n₀ := Nat.mul_le_mul h2 h2
  omega

/-- `restrictCom_specW`'s `hLB`, at the **parent's** palette: the
allocation is sized at the child's, and `prep_pal_le_succ` is the step
between. -/
theorem prepWB_pal (h : PrepWB S ℓp hbf n₀ B) {j : ℕ} (hj : j ≤ S.depth)
    {Λ : ℕ} (A : Arena Λ n₀) : A.N * S.pal j < B := by
  refine lt_of_le_of_lt ?_ (h.palette j hj)
  exact Nat.mul_le_mul (arenaN_le A) (prep_pal_le_succ S j)

/-- `colWriteCom_machChild`'s `hrowB`: the isolation palette's row
stride at the child's carrier. `isoPal (relPal (S.pal j)) S.width S.R`
*is* `S.pal (j+1)`. -/
theorem prepWB_isoRow (h : PrepWB S ℓp hbf n₀ B) {j : ℕ} (hj : j ≤ S.depth)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N))
    (u : Fin A.N) :
    childN S A π u * isoPal (relPal (S.pal j)) S.width S.R < B := by
  rw [← Setup.pal_succ]
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (prep_childN_le_root S A π u)) (h.palette j hj)

/-- `restrictCom_specW`'s `hHB` and `supportsCom_specW`'s `hLB`. -/
theorem prepWB_chan (h : PrepWB S ℓp hbf n₀ B) {j : ℕ} (hj : j ≤ S.depth)
    {Λ : ℕ} (A : Arena Λ n₀) : A.N * ℓp j * (hbf j + 1) < B :=
  lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (arenaN_le A)))
    (h.channel j hj)

/-- The same at the child — `mkBatchCom_batch`'s `hRB`. -/
theorem prepWB_chanChild (h : PrepWB S ℓp hbf n₀ B) {j : ℕ}
    (hj : j ≤ S.depth) {Λ : ℕ} (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N))
    (u : Fin A.N) : childN S A π u * ℓp j * (hbf j + 1) < B :=
  lt_of_le_of_lt
    (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (prep_childN_le_root S A π u)))
    (h.channel j hj)

/-- `supportsCom_specW`'s `hlB`. -/
theorem prepWB_lp (h : PrepWB S ℓp hbf n₀ B) {j : ℕ} (hj : j ≤ S.depth) :
    ℓp j < B := by have := h.sched j hj; omega

/-- `supportsCom_specW`'s `hhB`. -/
theorem prepWB_hb (h : PrepWB S ℓp hbf n₀ B) {j : ℕ} (hj : j ≤ S.depth) :
    hbf j + 1 < B := by have := h.sched j hj; omega

/-- `mkBatchCom_batch`'s `hmbB` and `profilesCom_specW`'s. -/
theorem prepWB_width (h : PrepWB S ℓp hbf n₀ B) : S.width < B := by
  have := h.sched 0 (Nat.zero_le _); omega

/-- `profilesCom_specW`'s `hRB`. -/
theorem prepWB_R (h : PrepWB S ℓp hbf n₀ B) : S.R + 3 < B := by
  have := h.sched 0 (Nat.zero_le _); omega

/-- `bfsCom_specW`'s and `supportsCom_specW`'s `hdB` **at the radius the
pass runs**, `2R` — never `R`. -/
theorem prepWB_twoR (h : PrepWB S ℓp hbf n₀ B) : 2 * S.R + 2 < B := by
  have := h.sched 0 (Nat.zero_le _); omega

/-- The level numeral the batch builder loads (`pcJr := j`). -/
theorem prepWB_level (h : PrepWB S ℓp hbf n₀ B) {j : ℕ} (hj : j ≤ S.depth) :
    j < B := by have := h.sched j hj; omega

open Classical in
/-- `profilesCom_specW`'s `hnsB`, at the pre-isolation child: the degree
sum plus the `vsrc` offset pad. -/
theorem prepWB_profNs (h : PrepWB S ℓp hbf n₀ B)
    {Λ : ℕ} (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
        + 2 * childN S A π u + 1 < B := by
  have h1 := h.carrier
  have hN := prep_childN_le_root S A π u
  have hsum : (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
      ≤ n₀ * n₀ :=
    le_trans (prep_sum_degree_le_sq (preG S A π u)) (Nat.mul_le_mul hN hN)
  omega

/-- **The bundle is satisfiable.** Nothing in `PrepWB` constrains the
schedule against itself: for any root carrier and any column/row
schedule there is a word bound that meets all four clauses at once, so a
theorem carrying `PrepWB` is not vacuous. (At F7's own instantiation
`B = mcB q x` the clauses become a lower bound on `q`, not a new
obligation on the input.) -/
theorem prepWB_exists (S : Setup L) (ℓp hbf : ℕ → ℕ) (n₀ : ℕ) :
    ∃ B, PrepWB S ℓp hbf n₀ B := by
  classical
  refine ⟨n₀ * n₀ + 2 * n₀ + 4
      + (Finset.range (S.depth + 1)).sup (fun i =>
          n₀ * S.pal (i + 1) + n₀ * ℓp i * (hbf i + 1)
            + (ℓp i + hbf i + S.width + 2 * S.R + i + 4)), ?_⟩
  refine ⟨by omega, ?_, ?_, ?_⟩ <;>
  · intro i hi
    have hmem : i ∈ Finset.range (S.depth + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    have hle : n₀ * S.pal (i + 1) + n₀ * ℓp i * (hbf i + 1)
        + (ℓp i + hbf i + S.width + 2 * S.R + i + 4)
        ≤ (Finset.range (S.depth + 1)).sup (fun i =>
            n₀ * S.pal (i + 1) + n₀ * ℓp i * (hbf i + 1)
              + (ℓp i + hbf i + S.width + 2 * S.R + i + 4)) :=
      Finset.le_sup (f := fun i => n₀ * S.pal (i + 1) + n₀ * ℓp i * (hbf i + 1)
        + (ℓp i + hbf i + S.width + 2 * S.R + i + 4)) hmem
    omega

end WordSize

/-! ## §6 The cover output's own word bound

`clusterRowCom_spec` asks for one clause that is neither an allocation
nor a name: `∀ i ≤ N, (σ.arrs co).getD i 0 < B` — every offset the row
copy reads fits a word. It is not a hypothesis anybody upstream states,
and it is not implied by `ClusterCsr` alone; what makes it true is that
the offsets are the partial sums of the cluster sizes, so they are
bounded by `N²`, which `PrepWB.carrier` covers.

This is the third invisible binding requirement of the pass, after the
allocations and the exact batch width. -/

section CoverOffsets

/-- **The cover CSR's offsets are bounded by `N²`.** The offset array is
the partial-sum sequence of the cluster sizes, and every cluster is a
subset of the carrier. -/
theorem prep_clusterCsr_offset_le {co cm : String} {N : ℕ}
    {Xf : Fin N → Set (Fin N)} {σ : Env} (h : ClusterCsr co cm Xf σ)
    (hX : ∀ v : Fin N, (Xf v).ncard ≤ N) :
    ∀ i, i ≤ N → (σ.arrs co).getD i 0 ≤ N * N := by
  obtain ⟨offC, h0, hcoL, hco, hstep, hcmL, hcm⟩ := h
  have key : ∀ i, i ≤ N → offC i ≤ i * N := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; omega
    | succ i ih =>
      intro hi
      have hiN : i < N := by omega
      have hih := ih (by omega)
      have hXi := hX ⟨i, hiN⟩
      calc offC (i + 1) = offC i + (Xf ⟨i, hiN⟩).ncard := hstep ⟨i, hiN⟩
        _ ≤ i * N + N := Nat.add_le_add hih hXi
        _ = (i + 1) * N := (Nat.succ_mul i N).symm
  intro i hi
  rw [hco i hi]
  exact le_trans (key i hi) (Nat.mul_le_mul_right _ hi)

/-- **`clusterRowCom_spec`'s word clause, discharged** at the cover
stage's own output and the pass's word bundle. -/
theorem prep_clusterCsr_offset_lt {L n₀ : ℕ} {S : Setup L} {ℓp hbf : ℕ → ℕ}
    {B : ℕ} (hwb : PrepWB S ℓp hbf n₀ B) {co cm : String} {Λ : ℕ}
    {A : Arena Λ n₀} {π : Equiv.Perm (Fin A.N)} {σ : Env}
    (h : ClusterCsr co cm (cluster S A π) σ) :
    ∀ i, i ≤ A.N → (σ.arrs co).getD i 0 < B := by
  intro i hi
  have h1 := prep_clusterCsr_offset_le h (fun v => prep_childN_le S A π v) i hi
  have h2 := prepWB_NN hwb A
  omega

end CoverOffsets

/-! ## §7 Two stages, instantiated at the pass's own names

The two contracts whose side conditions dominate the composition:
`restrictCom_specW` (thirteen name clauses, five word bounds and seven
allocations) and `mkBatchCom_batch` (thirty-two disequalities). Both are
restated here at `prepC`'s own names, with **every** side condition
discharged from `prepScr` and `PrepWB` — so what a chain still owes at
these two steps is only that the state arriving satisfies the arena and
cell clauses.

Nothing is weakened: each conclusion is the landed contract's, at the
pass's instantiation. -/

section Stages

variable {L n₀ B : ℕ}

open Classical in
/-- **The restrict stage, at the pass's names.** `restrictCom_specW`
with its name discipline (`SolveMachPrepComp` §6 and §4 here), its five
word bounds (§5) and its seven allocation clauses (§3) discharged. The
clean rank scratch enters through `prepScr_rank` and `rankScr_take` —
the descriptor's one *content* clause, at the level's own carrier
window. -/
theorem prep_restrictStage {S : Setup L} {ℓp hbf : ℕ → ℕ}
    (hwb : PrepWB S ℓp hbf n₀ B) (j : ℕ) (hj : j ≤ S.depth)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    Spec B
      (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (chanTab S ℓp j A)) σ ∧
          ClusterList pcLa (cluster S A π u) σ ∧
          σ.vars "rs.k" = (cluster S A π u).ncard ∧
          σ.vars "rs.l" = S.pal j ∧ σ.vars "rs.p" = ℓp j ∧
          σ.vars "rs.h" = hbf j ∧
          prepScr S ℓp hbf n₀ j σ)
      (restrictCom (arenaNames j) (prepMid j) pcLa (pcRa j))
      (fun σ σ' =>
        ArenaStW (prepMid j) (hbf j)
            ((Impl.ofArena A (chanTab S ℓp j A)).restrict
              (cluster S A π u)) σ' ∧
        σ'.vars (prepMid j).nS
          = ∑ v : Fin (childN S A π u), (preG S A π u).degree v ∧
        ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (chanTab S ℓp j A)) σ' ∧
        σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS ∧
        ClusterList pcLa (cluster S A π u) σ' ∧
        σ'.vars "rs.k" = (cluster S A π u).ncard ∧
        A.N ≤ (σ'.arrs (pcRa j)).length ∧
        (σ'.arrs (pcRa j)).take A.N = arrOf A.N (fun _ => 0))
      (restrictK (Impl.degSum A.G (cluster S A π u)) (cluster S A π u).ncard
        (S.pal j) (ℓp j) (hbf j)) :=
  (restrictCom_specW (B := B)
      (A := Impl.ofArena A (chanTab S ℓp j A)) (S := cluster S A π u)
      (nmP := arenaNames j) (nmC := prepMid j) (la := pcLa) (ra := pcRa j)
      (by have h := prepWB_N hwb A; show A.N < B; omega) (prepWB_NN hwb A)
      (by have := prepWB_root hwb; omega) (prepWB_pal hwb hj A)
      (prepWB_chan hwb hj A)
      (prep_restrict_disj j) (prep_restrict_pairwise j)
      (prep_nN_notMem_rs (j + 1)) (prep_nS_notMem_rs (j + 1))
      (prep_nN_ne_nS (j + 1))
      (prep_nN_notMem_rs j) (prep_nS_notMem_rs j)
      (prep_pnN_ne_cnN j) (prep_pnN_ne_cnS j)
      (prep_pnS_ne_cnN j) (prep_pnS_ne_cnS j)
      (arenaNames_nodup5 j) (prep_la_notMem5 j)).pre
    (fun σ hσ =>
      ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1, hσ.2.2.2.2.2.1,
        prepScr_ra_len S ℓp hbf j hσ.2.2.2.2.2.2,
        rankScr_take hσ.1 (prepScr_rank hσ.2.2.2.2.2.2),
        prepScr_oi_len S ℓp hbf j π u hσ.2.2.2.2.2.2,
        prepScr_ti_len S ℓp hbf j π u hσ.2.2.2.2.2.2,
        prepScr_col_len_restrict S ℓp hbf j π u hσ.2.2.2.2.2.2,
        prepScr_up_len S ℓp hbf j π u hσ.2.2.2.2.2.2,
        prepScr_hist_len S ℓp hbf j π u hσ.2.2.2.2.2.2⟩)

open Classical in
/-- **The batch builder, at the pass's names.** `mkBatchCom_batch` with
its thirty-two disequalities discharged, its bit-region allocation read
off `prepScr`, and its index-region **equality** read off
`prepScr_batchWidth` — the clause that no run can establish, because
IMP+ `store` is `List.set`. -/
theorem prep_mkBatchStage {S : Setup L} {ℓp : ℕ → ℕ}
    {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {hbf : ℕ → ℕ} {Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop}
    (hwb : PrepWB S ℓp hbf n₀ B)
    (hp : PrepPins S ℓp htabF hbf Adm) (hw : WidthPin S)
    (j : ℕ) (A : Arena (S.pal j) n₀) (hj : j < S.depth) (hAdm : Adm j A)
    (hrow : ∀ (v : Fin A.N) (e : ℕ), (A.chan v e).length ≤ 2 * S.R + 1)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    Spec B
      (fun σ =>
        HistArrW (arenaNames (j + 1)).hist (ℓp j) (hbf j)
            (childHistTab S A π u (htabF j A)) σ ∧
        σ.vars (arenaNames (j + 1)).nN = childN S A π u ∧
        σ.vars pcCc = ((centreChild S A π u : Fin (childN S A π u)) : ℕ) ∧
        σ.vars pcJr = j ∧ σ.vars pcMw = S.width ∧
        prepScr S ℓp hbf n₀ j σ)
      (mkBatchCom (arenaNames (j + 1)).hist pcBb pcBi pcCc
        (arenaNames (j + 1)).nN pcJr pcMw pcEc pcIc pcLn pcBs pcAv pcSc
        (ℓp j) (hbf j))
      (fun σ σ' => FinBitsW pcBb (Set.range (batchFn S A π u)) σ' ∧
        BatchWidthScr pcBi S.width σ' ∧
        (∀ i : Fin S.width, (σ'.arrs pcBi).getD (i : ℕ) 0
          = ((batchFn S A π u i : Fin (childN S A π u)) : ℕ)) ∧
        (∀ y, y ≠ pcAv → y ≠ pcSc → y ≠ pcEc → y ≠ pcIc → y ≠ pcLn →
          y ≠ pcBs → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ pcBb → b ≠ pcBi → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (mkBatchK (childN S A π u) (ℓp j) (hbf j) S.width) :=
  (mkBatchCom_batch (B := B) S ℓp htabF hbf Adm hp hw j A hj hAdm hrow π u
      (by have := prepWB_N hwb A
          have := prep_childN_le S A π u
          omega)
      (prepWB_width hwb) (prepWB_chanChild hwb (le_of_lt hj) A π u)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)).pre
    (fun σ hσ =>
      ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1,
        prepScr_bb_len S ℓp hbf j π u hσ.2.2.2.2.2,
        prepScr_batchWidth hσ.2.2.2.2.2⟩)

end Stages

/-! ## §8 The axiom profile

Nothing here quotes `headlineSetup`, so the expected profile is the
ambient three. -/

#print axioms prep_sum_degree_le_sq
#print axioms prepScr_ti_len
#print axioms prepScr_vt_len
#print axioms prep_profNames_ok
#print axioms prepWB_exists
#print axioms prep_clusterCsr_offset_lt
#print axioms prep_restrictStage
#print axioms prep_mkBatchStage

end Lax3Proofs.Prog
