import Lax3Proofs.SolveMachPrepCol

/-!
# F6c12 (residual 1) — the child-building pass: the composition seams

`SolveMachPrep` states **`ChildLoadParts`/`ChildLoadPartsAll`**
(`:230`/`:299`) — the child-building pass at the shape the composed
stage lifts hand over — and `SolveMachPrepPins` §7 reduces the whole
prep segment to it (`centrePrepAll_of_parts_chanTab`: the seam
hypothesis is `rfl` at the canonical witness). The three glue programs
are landed (`clusterRowCom_spec`, `mkBatchCom_batch`,
`colWriteCom_machChild`) and so are the five stage lifts
(`restrictCom_specW`, `bfsCom_specW`, `supportsCom_specW`,
`profilesCom_specW`, `isolateCom_specW`).

**The composition order** the pass runs, per centre `u`, is

```
  clusterRowCom            -- row u of the cover CSR → ClusterList
  centreIdxCom             -- the connector's own child name  (§1 here)
  restrictCom     (nmP=level j, nmC=level j+1 regions, scratch off/tgt)
  mkBatchCom               -- ONE bit vector + the index region
  bfsCom          (source centreChild, radius 2R)
  supportsCom     (radius 2R, column A.hist.length)   -- ONE call
  profilesCom     (at preG, BEFORE isolation)
  colWriteCom              -- the isoPal colour region
  isolateCom      (W = range batchFn = the scan's own bit vector)
```

with `profilesCom` **before** and `colWriteCom`/`isolateCom` **after**
it, because `profilesCom_specW` reads the arena at the *parent's*
palette while the deliverable is at `isoPal (relPal Λ) S.width S.R`.

This file supplies the four seams that composition needs and that no
landed statement provides. It does **not** discharge
`ChildLoadPartsAll`; §5 records exactly what still blocks that, at the
pair of contracts it blocks it between.

## §1 The connector's own child name, as a numeral

`bfsCom_specW` asks for the BFS source in the `bf.v` cell and
`mkBatchCom_batch` for the connector in `cc`, both as
`(centreChild S A π u : ℕ)`. **Nothing landed computes it**:
`restrictCom_specW` returns the child's two cells and the cluster list,
never the connector's local index, and `mkBatchCom_batch` asks for the
numeral in `cc` as a hypothesis (`SolveMachPrepBatch:1307`).
`centreIdxCom` is that program — a single scan of the cluster list
counting the members below the connector, correct *because*
`Driver.setEquiv` is the sorted enumeration (`setEquiv_strictMono`, the
same fact the batch builder's carrier scan rides). Budget
`centreIdxK k = 17·k + 8`, absorbed by `restrictK`'s per-member charge
exactly as `clusterRowK` is: **no new term in `prepStageK`, and no
`A.N` term.**

## §2 The supports patch **is** `Driver.childChan`

`supportsCom_specW` leaves the arena
`{A with hist := fun v p => if p = e then descendCol A.G D d v else A.hist v p}`.
`supportsPatch_eq_childChan` proves that at `A := (ofArena A htab).restrict
(cluster …)`, `d := 2 * S.R`, `e` the column with `↑e = A.hist.length`
and `D` any table `bfsCom_specW` can leave, this *is*
`fun a p => childChan S A π u a ↑p` — `chanTabChild`, the `chanF` of
`SolveMachPrepPins`, at the **parent's** column count `ℓp j`; the move
to `ℓp (j+1)` is the landed `arenaStW_machChild_chanTabChild`, which the
column pin makes definitionally free. The new column is
`childChan_new` under
`ballTable_eq_ballDist` (the table is canonical, so which run produced
it does not matter); every older column is `childChan_old` on the nose,
because `restrict`'s `filterMap (toLocal …)` and `childChan`'s
inherited branch are the same term. **Inherit-and-patch, one BFS** —
hazard 3.

## §3 The palette move, and the assembled child

`SolveMachPrepCol` §8 leaves the colour region satisfying `ColBits`'s
clause at `machChild.col` but explicitly does **not** lift it through
`ArenaStW`: the input arena is at `Λc`, the output at
`isoPal Λc mb R`, so the `col` window moves while the other four stay.
`arenaStW_recol` is that lift, and `isolate_recol_eq_machChild` is the
identity that turns `isolateCom_specW`'s output into `machChild` —
`rfl`, since `childArena.G = deleteVerts preG (range batchFn)` and
`restrict`'s carrier/renaming are `childArena`'s.
`relColoring_restrict_col` pins the remaining half of
`machChild_eq_ofArena`'s hypothesis: `profilesCom_specW`'s
`relColoring A.col Set.univ` at the restricted child **is**
`childColR`, also `rfl`.

## §4 The pass's whole budget, glue included

The landed absorption lemmas price each glue program against
`prepStageK` *separately*; the pass runs all four, so what it has to fit
is their sum. `prepPassK` is that sum and `prepPassK_le` closes it in
`prepStageK_le`'s own shape — `restrictK` plus a **schedule constant**
times the child's weight `‖B₀‖ + 1`. **No `A.N` term**: the cluster-row
copy and the connector scan *share* `restrictK`'s per-member charge
(`clusterRowK_add_centreIdxK_le_restrictK`: `31` per member against the
`132` already charged), and every other glue figure is the child's.

## §5 The frame data the lifts do not state

`restrictCom_specW` states no frame clause and no length clause, while
`ChildLoadParts` demands both (`∀ a ∈ ca j :: co j :: cm j ::
levelArrays j, σ'.arrs a = σ.arrs a` and
`∀ b, (σ'.arrs b).length = (σ.arrs b).length`). `Spec.frameA` recovers
both from `Run` for *any* stage, and `restrictCom_notMem_warrs` /
`isolateCom_notMem_warrs` are the two membership side conditions the
composition discharges them with.

## §6 What still blocks `ChildLoadPartsAll`, precisely

Two seams do **not** meet, and neither is repaired by adding a
hypothesis:

1. **`restrictCom_specW`'s clean rank scratch has no home in `CLInv`.**
   The lift's precondition contains `(σ.arrs ra).take A.N =
   arrOf A.N (fun _ => 0)` — a *content* clause on an array outside the
   level's six regions. `CLInv` (`SolveGlueLoop`) offers exactly one
   slot for such a clause, the scratch descriptor `Scr j` inside
   `BlockPre`; but `centrePrep_of_childLoad` and
   `centrePrepAll_of_parts_chanTab` both take `hscrLen : ∀ j σ σ',
   Scr j σ → (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ'`,
   which a content clause cannot satisfy. The pass *does* restore the
   scratch (`restrictCom_specW` returns it clean), so the loop
   preserves it — but the landed transport cannot see that. The two
   escapes both cost: carrying it in `Scr` forfeits the
   `CentrePrepAll` corollary, and wiping it inside `prepC` costs
   `Θ(A.N)` per centre, i.e. §6.1's `Θ(A.N²)` scratch trap that
   `restrictK`'s missing `A.N` term exists to avoid.

2. **`profilesCom_specW`'s index-region length is an equality.** It
   asks `(σ.arrs ba).length = mb` while `ChildLoadParts`' frame forbids
   reallocation, so the equality must arrive with the state.
   `BatchWidthScr` (Pins §9) is that clause and it *is* length-only, so
   this one is discharged the moment `Scr` is instantiated — recorded
   here only because it constrains the instantiation.

Everything else meets on the nose; §1–§4 are the pieces that were
missing, not mismatched.

## Hazards honoured

* **Profiles are measured in `preG`, before isolation** — §3's
  identity isolates *after* the recolour, and the `ProfileTablesMS`
  witness `relColoring_restrict_col` transports is the one stated at
  the restricted child.
* **Supports runs at radius `2R`** — §2 is stated at `2 * S.R`, never
  `S.R`.
* **Inherit-and-patch, one BFS** — §2 proves the patch *is*
  `childChan`, one written column and the rest inherited.
* **`deleteVerts` isolates, it does not remove** — `isolate_recol_eq_
  machChild` keeps the carrier; the recolour moves only `col`.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3.ColoredGraphs
open Lax3Proofs.Driver

/-! ## §0 Two small facts -/

private theorem ncard_le_card {n : ℕ} (X : Set (Fin n)) : X.ncard ≤ n := by
  classical
  have h := Set.ncard_le_ncard (Set.subset_univ X) Set.finite_univ
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h

private theorem getElem?_of_lt (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-! ## §1 The connector's own child name -/

/-- The body of the connector scan: one comparison, one conditional
bump, one step. -/
def centreIdxBody (la cu cc ct : String) : Com :=
  .seq (.ite (.lt (.get la (.var ct)) (.var cu))
      (.assign cc (.add (.var cc) (.lit 1))) .skip)
    (.assign ct (.add (.var ct) (.lit 1)))

/-- **The connector's own child name**, as a program: scan the cluster
list and count the members below the connector. Because
`Driver.setEquiv` is the *sorted* enumeration, that count is the
connector's local index — the numeral `bfsCom_specW` wants in `bf.v`
and `mkBatchCom_batch` in `cc`. -/
def centreIdxCom (la cu ck cc ct : String) : Com :=
  .seq (.assign cc (.lit 0))
    (.seq (.assign ct (.lit 0))
      (.while (.lt (.var ct) (.var ck)) (centreIdxBody la cu cc ct)))

/-- The scan's budget: thirteen words per member — a two-level read, a
comparison, a guarded bump and a step — plus the loop's four per turn
and the two initialisations. -/
def centreIdxK (k : ℕ) : ℕ := 17 * k + 8

/-- **The scan's budget is absorbed by the restrict stage's own
column**, exactly as the cluster-row copy's is
(`clusterRowK_le_restrictK`): `restrictK` already charges `132` per
cluster member. So the glue introduces **no new term** into
`prepStageK`, and in particular no `A.N` term. -/
theorem centreIdxK_le_restrictK (dS k Λc ℓp hb : ℕ) :
    centreIdxK k ≤ restrictK dS k Λc ℓp hb := by
  have h : 17 * k ≤ k * (20 * Λc + (36 * hb + 42) * ℓp + 132) := by
    have h' : k * 17 ≤ k * (20 * Λc + (36 * hb + 42) * ℓp + 132) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  unfold centreIdxK restrictK
  omega

theorem centreIdxK_le_prepStageK (cN cns dS k Λc ℓp hb mb R : ℕ) :
    centreIdxK k ≤ prepStageK cN cns dS k Λc ℓp hb mb R := by
  have h := centreIdxK_le_restrictK dS k Λc ℓp hb
  unfold prepStageK
  omega

open Classical in
/-- **The connector scan, specified.** From the cluster's enumeration
region and the connector's parent name in `cu`, the scan leaves the
connector's *local* name in `cc`: the count of members below it, which
is its index in the ascending enumeration `Driver.setEquiv`. Two
scalars written, no array touched at all. -/
theorem centreIdxCom_spec {B n : ℕ} {X : Set (Fin n)} {la cu ck cc ct : String}
    {y : Fin n} (hy : y ∈ X) (hNB : n < B)
    (hct_ck : ct ≠ ck) (hct_cu : ct ≠ cu) (hct_cc : ct ≠ cc)
    (hcc_ck : cc ≠ ck) (hcc_cu : cc ≠ cu) :
    Spec B
      (fun σ => ClusterList la X σ ∧ σ.vars cu = (y : ℕ) ∧ σ.vars ck = X.ncard)
      (centreIdxCom la cu ck cc ct)
      (fun σ σ' =>
        σ'.vars cc = (((Driver.setEquiv X).symm ⟨y, hy⟩ : Fin X.ncard) : ℕ) ∧
        (∀ z, z ≠ cc → z ≠ ct → σ'.vars z = σ.vars z) ∧
        (∀ a, σ'.arrs a = σ.arrs a))
      (centreIdxK X.ncard) := by
  intro σ hσ
  obtain ⟨hcl, hcu, hck⟩ := hσ
  set k : ℕ := X.ncard with hk_def
  set i₀ : Fin X.ncard := (Driver.setEquiv X).symm ⟨y, hy⟩ with hi₀_def
  set c₀ : ℕ := (i₀ : ℕ) with hc₀_def
  have hkn : k ≤ n := ncard_le_card X
  have hkB : k < B := lt_of_le_of_lt hkn hNB
  have hyB : (y : ℕ) < B := lt_trans y.2 hNB
  have hB1 : 1 < B := by omega
  have hc₀k : c₀ < k := i₀.2
  -- the enumeration at the connector
  have hi₀y : ((Driver.setEquiv X i₀ : ↥X) : Fin n) = y := by
    rw [hi₀_def, Equiv.apply_symm_apply]
  -- the comparison, resolved by the enumeration's monotonicity
  have hemb : ∀ (t : ℕ) (ht : t < k),
      ((Impl.restrictEmb X ⟨t, ht⟩ : Fin n) : ℕ) < (y : ℕ) ↔ t < c₀ := by
    intro t ht
    rw [Impl.restrictEmb_apply]
    constructor
    · intro hlt
      by_contra hge
      rw [not_lt] at hge
      rcases Nat.eq_or_lt_of_le hge with h | h
      · have : (⟨t, ht⟩ : Fin k) = i₀ := Fin.ext h.symm
        rw [this, hi₀y] at hlt
        exact absurd hlt (lt_irrefl _)
      · have hmono : ((Driver.setEquiv X i₀ : ↥X) : Fin n).val
            < ((Driver.setEquiv X ⟨t, ht⟩ : ↥X) : Fin n).val :=
          setEquiv_strictMono X (show i₀ < (⟨t, ht⟩ : Fin k) from h)
        rw [hi₀y] at hmono
        omega
    · intro hlt
      have hmono : ((Driver.setEquiv X ⟨t, ht⟩ : ↥X) : Fin n).val
          < ((Driver.setEquiv X i₀ : ↥X) : Fin n).val :=
        setEquiv_strictMono X (show (⟨t, ht⟩ : Fin k) < i₀ from hlt)
      rw [hi₀y] at hmono
      exact hmono
  -- the loop invariant: the running count is the connector's index, capped
  set I : Env → Prop := fun τ =>
    ClusterList la X τ ∧ τ.vars ck = k ∧ τ.vars cu = (y : ℕ) ∧
      τ.vars ct ≤ k ∧ τ.vars cc = min (τ.vars ct) c₀ with hI_def
  have hbody : Spec B (fun τ => I τ ∧ τ.vars ct < k) (centreIdxBody la cu cc ct)
      (fun τ τ' => I τ' ∧ τ'.vars ct = τ.vars ct + 1) 13 := by
    rintro τ ⟨⟨hclτ, hckτ, hcuτ, hleτ, hccτ⟩, hltτ⟩
    set t : ℕ := τ.vars ct with ht_def
    have hlaLen : t < (τ.arrs la).length := lt_of_lt_of_le hltτ hclτ.1
    have hval : (τ.arrs la).getD t 0
        = ((Impl.restrictEmb X ⟨t, hltτ⟩ : Fin n) : ℕ) := hclτ.2 t hltτ
    have hvalB : (τ.arrs la).getD t 0 < B := by
      rw [hval]
      exact lt_trans (Impl.restrictEmb X ⟨t, hltτ⟩).2 hNB
    have hccB : τ.vars cc < B := by rw [hccτ]; omega
    have hcond : (Cond.lt (Expr.get la (Expr.var ct)) (Expr.var cu)).evalB B τ
        = some (decide ((τ.arrs la).getD t 0 < (y : ℕ))) := by
      have h1 : (Expr.get la (Expr.var ct)).evalB B τ
          = some ((τ.arrs la).getD t 0) :=
        evalB_get (evalB_var (by omega)) (getElem?_of_lt _ _ hlaLen) hvalB
      have h2 : (Expr.var cu).evalB B τ = some (y : ℕ) := by
        have h := evalB_var (B := B) (x := cu) (σ := τ) (by rw [hcuτ]; omega)
        rw [hcuτ] at h
        exact h
      exact evalB_condLt h1 h2
    -- the step and the invariant, from whichever state the branch leaves
    have hgen : ∀ ρ : Env, ρ.vars ct = t → ρ.vars cc = min (t + 1) c₀ →
        ρ.vars ck = k → ρ.vars cu = (y : ℕ) → (∀ a, ρ.arrs a = τ.arrs a) →
        ∃ ρ', Run B (.assign ct (.add (.var ct) (.lit 1))) ρ ρ' 4 ∧
          I ρ' ∧ ρ'.vars ct = τ.vars ct + 1 := by
      intro ρ hct hcc hck' hcu' harr
      have hb : (Expr.bin .add (.var ct) (.lit 1)).evalB B ρ
          = some (t + 1) := by
        refine evalB_bin ?_ (evalB_lit hB1) ?_
        · have h := evalB_var (B := B) (x := ct) (σ := ρ) (by rw [hct]; omega)
          rw [hct] at h
          exact h
        · simpa using (show t + 1 < B by omega)
      refine ⟨ρ.setVar ct (t + 1), ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa using Run.assign (x := ct) hb
      · exact clusterList_of_eq hclτ (by rw [arrs_setVar]; exact harr la)
      · rw [vars_setVar, if_neg (Ne.symm hct_ck)]; exact hck'
      · rw [vars_setVar, if_neg (Ne.symm hct_cu)]; exact hcu'
      · rw [vars_setVar, if_pos rfl]; omega
      · rw [vars_setVar, if_neg (Ne.symm hct_cc), vars_setVar, if_pos rfl]
        exact hcc
      · rw [vars_setVar, if_pos rfl]
    by_cases hlt : t < c₀
    · have htrue : (Cond.lt (Expr.get la (Expr.var ct)) (Expr.var cu)).evalB B τ
          = some true := by
        rw [hcond, hval, decide_eq_true ((hemb t hltτ).mpr hlt)]
      have hb : (Expr.bin .add (.var cc) (.lit 1)).evalB B τ
          = some (τ.vars cc + 1) := by
        refine evalB_bin (evalB_var hccB) (evalB_lit hB1) ?_
        simpa using (show τ.vars cc + 1 < B by rw [hccτ]; omega)
      have hbump : Run B
          (.ite (.lt (.get la (.var ct)) (.var cu))
            (.assign cc (.add (.var cc) (.lit 1))) .skip) τ
          (τ.setVar cc (τ.vars cc + 1))
          (1 + (Cond.lt (Expr.get la (Expr.var ct)) (Expr.var cu)).size + 4) :=
        Run.ite_true htrue (by simpa using Run.assign (x := cc) hb)
      obtain ⟨ρ', hrun', hI', hct'⟩ := hgen (τ.setVar cc (τ.vars cc + 1))
        (by rw [vars_setVar, if_neg hct_cc])
        (by rw [vars_setVar, if_pos rfl, hccτ]; omega)
        (by rw [vars_setVar, if_neg (Ne.symm hcc_ck)]; exact hckτ)
        (by rw [vars_setVar, if_neg (Ne.symm hcc_cu)]; exact hcuτ)
        (fun a => by rw [arrs_setVar])
      exact ⟨ρ', (hbump.seq hrun').mono (by simp [Cond.size, Expr.size]),
        hI', hct'⟩
    · have hfalse : (Cond.lt (Expr.get la (Expr.var ct)) (Expr.var cu)).evalB B τ
          = some false := by
        rw [hcond, hval, decide_eq_false (fun h => hlt ((hemb t hltτ).mp h))]
      have hkeep : Run B
          (.ite (.lt (.get la (.var ct)) (.var cu))
            (.assign cc (.add (.var cc) (.lit 1))) .skip) τ τ
          (1 + (Cond.lt (Expr.get la (Expr.var ct)) (Expr.var cu)).size + 1) :=
        Run.ite_false hfalse Run.skip
      obtain ⟨ρ', hrun', hI', hct'⟩ := hgen τ rfl
        (by rw [hccτ]; omega) hckτ hcuτ (fun _ => rfl)
      exact ⟨ρ', (hkeep.seq hrun').mono (by simp [Cond.size, Expr.size]),
        hI', hct'⟩
  -- the loop
  have hloop := Spec.forRangeZero (B := B) ct ck I k 13 hkB
    (fun _ hτ => hτ.2.2.2.1) (fun _ hτ => hτ.2.1) hbody
  -- the prologue: `cc := 0`
  have hrunA : Run B (.assign cc (.lit 0)) σ (σ.setVar cc 0) 2 := by
    simpa using
      Run.assign (x := cc) (evalB_lit (σ := σ) (show (0 : ℕ) < B by omega))
  have hInit : I (((σ.setVar cc 0)).setVar ct 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact clusterList_of_eq hcl (by rw [arrs_setVar, arrs_setVar])
    · rw [vars_setVar, if_neg (Ne.symm hct_ck), vars_setVar,
        if_neg (Ne.symm hcc_ck)]
      exact hck
    · rw [vars_setVar, if_neg (Ne.symm hct_cu), vars_setVar,
        if_neg (Ne.symm hcc_cu)]
      exact hcu
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_neg (Ne.symm hct_cc), vars_setVar, if_pos rfl,
        vars_setVar, if_pos rfl]
      omega
  obtain ⟨σ', hrunL, hIfin, hctfin⟩ := hloop.run hInit
  refine ⟨σ', ((hrunA.seq hrunL).mono ?_), ?_, ?_, ?_⟩
  · unfold centreIdxK; omega
  · have hcc' := hIfin.2.2.2.2
    rw [hcc', hctfin]
    omega
  · intro z h1 h2
    refine (hrunA.seq hrunL).frame_var z ?_
    simp only [centreIdxBody, Com.wvars, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    tauto
  · intro a
    refine (hrunA.seq hrunL).frame_arr a ?_
    simp only [centreIdxBody, Com.warrs, List.append_nil, List.not_mem_nil,
      not_false_eq_true]

section CentreIdxDriver

variable {L n₀ : ℕ}

open Classical in
/-- **The connector scan at the driver's objects**: from the cluster
list `restrictCom_specW` consumes and the centre's parent name in the
level's counter cell, the scan leaves `centreChild S A π u` — the BFS
source and the batch builder's connector, both of which are asked for
as numerals. -/
theorem centreIdxCom_centreChild {B : ℕ} (S : Setup L) {Λ : ℕ}
    (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {la cu ck cc ct : String} (hNB : A.N < B)
    (hct_ck : ct ≠ ck) (hct_cu : ct ≠ cu) (hct_cc : ct ≠ cc)
    (hcc_ck : cc ≠ ck) (hcc_cu : cc ≠ cu) :
    Spec B
      (fun σ => ClusterList la (cluster S A π u) σ ∧ σ.vars cu = (u : ℕ) ∧
        σ.vars ck = childN S A π u)
      (centreIdxCom la cu ck cc ct)
      (fun σ σ' =>
        σ'.vars cc = ((centreChild S A π u : Fin (childN S A π u)) : ℕ) ∧
        (∀ z, z ≠ cc → z ≠ ct → σ'.vars z = σ.vars z) ∧
        (∀ a, σ'.arrs a = σ.arrs a))
      (centreIdxK (childN S A π u)) :=
  centreIdxCom_spec (X := cluster S A π u) (self_mem_cluster S A π u) hNB
    hct_ck hct_cu hct_cc hcc_ck hcc_cu

end CentreIdxDriver

/-! ## §2 The supports patch is `Driver.childChan` -/

section Patch

variable {L n₀ : ℕ}

open Classical in
/-- **The supports patch IS the driver's inherit-and-patch channel.**
`supportsCom_specW`'s postcondition is the arena with `hist` overwritten
at one column `e` by `descendCol A.G D d`. At the restricted child, with
`d = 2 * S.R` (never `S.R` — hazard 2), `↑e = A.hist.length` (the round
the pass writes) and any table `D` a `bfsCom_specW` run can leave, that
family is exactly `chanTabChild`'s: `fun a p => childChan S A π u a ↑p`.

The written column is `childChan_new` once `D` is identified with the
canonical `childDist` (`ballTable_eq_ballDist` — the table is canonical,
so which run produced it is irrelevant); every other column is
`childChan_old` on the nose, because `MArena.restrict`'s
`filterMap (toLocal …)` and `childChan`'s inherited branch are the same
term. **One BFS, one written column** — hazard 3. -/
theorem supportsPatch_eq_childChan (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {ℓpj : ℕ}
    (htab : Fin A.N → Fin ℓpj → List (Fin A.N))
    (hchan : ∀ (v : Fin A.N) (p : Fin ℓpj), htab v p = A.chan v (p : ℕ))
    (e : Fin ℓpj) (he : (e : ℕ) = A.hist.length)
    {D : Fin (childN S A π u) → ℕ}
    (hD : Impl.BallTable (preG S A π u) (centreChild S A π u) (2 * S.R) D)
    (hDle : ∀ v : Fin (childN S A π u), D v ≤ 2 * S.R + 1) :
    (fun (a : Fin (childN S A π u)) (p : Fin ℓpj) =>
        if p = e then descendCol (preG S A π u) D (2 * S.R) a
        else ((Impl.ofArena A htab).restrict (cluster S A π u)).hist a p)
      = fun (a : Fin (childN S A π u)) (p : Fin ℓpj) =>
          childChan S A π u a (p : ℕ) := by
  have hDeq : D = childDist S A π u := ballTable_eq_ballDist hD hDle
  funext a p
  by_cases hp : p = e
  · subst hp
    rw [if_pos rfl, he, childChan_new, hDeq]
  · rw [if_neg hp]
    have hpv : (p : ℕ) ≠ A.hist.length := by
      rw [← he]
      exact fun h => hp (Fin.ext h)
    rw [childChan_old S A π u hpv]
    show (htab (Impl.restrictEmb (cluster S A π u) a) p).filterMap
        (Impl.toLocal (cluster S A π u)) = _
    rw [hchan]
    rfl

open Classical in
/-- The same at the canonical channel witness `chanTab` — the
hypothesis `hchan` holds by `rfl`. This is the family stated at the
**parent's** column count `ℓp j`, which is what `supportsCom_specW`
returns; `arenaStW_machChild_chanTabChild` (Pins §5) is the one step
that moves it to `chanTabChild` at `ℓp (j+1)`, and the move is
definitionally free because `chanTab` reads its column through `.val`
only. -/
theorem supportsPatch_eq_childChan_chanTab (S : Setup L) (ℓp : ℕ → ℕ) (j : ℕ)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (e : Fin (ℓp j)) (he : (e : ℕ) = A.hist.length)
    {D : Fin (childN S A π u) → ℕ}
    (hD : Impl.BallTable (preG S A π u) (centreChild S A π u) (2 * S.R) D)
    (hDle : ∀ v : Fin (childN S A π u), D v ≤ 2 * S.R + 1) :
    (fun (a : Fin (childN S A π u)) (p : Fin (ℓp j)) =>
        if p = e then descendCol (preG S A π u) D (2 * S.R) a
        else ((Impl.ofArena A (chanTab S ℓp j A)).restrict
          (cluster S A π u)).hist a p)
      = fun (a : Fin (childN S A π u)) (p : Fin (ℓp j)) =>
          childChan S A π u a (p : ℕ) :=
  supportsPatch_eq_childChan S A π u (chanTab S ℓp j A)
    (fun _ _ => rfl) e he hD hDle

end Patch

/-! ## §3 The palette move, and the assembled child -/

section Recolour

variable {Λ Λ' n₀ ℓp hb : ℕ}

/-- The arena with its colour rows replaced — the only field the colour
writer changes, and the only one whose window moves when the palette
does. -/
def recol (A : Impl.MArena Λ n₀ ℓp) (col' : Coloring A.N Λ') :
    Impl.MArena Λ' n₀ ℓp :=
  ⟨A.N, A.G, col', A.up, A.hist⟩

@[simp] theorem recol_N (A : Impl.MArena Λ n₀ ℓp) (col' : Coloring A.N Λ') :
    (recol (Λ' := Λ') A col').N = A.N := rfl

@[simp] theorem recol_G (A : Impl.MArena Λ n₀ ℓp) (col' : Coloring A.N Λ') :
    (recol (Λ' := Λ') A col').G = A.G := rfl

@[simp] theorem recol_col (A : Impl.MArena Λ n₀ ℓp) (col' : Coloring A.N Λ') :
    (recol (Λ' := Λ') A col').col = col' := rfl

open Classical in
/-- **The colour region's palette move, lifted to `ArenaStW`** — the
step `SolveMachPrepCol` §8 leaves to the discharger. The input arena is
at palette `Λ`, the colour writer's output at `Λ'`; the `col` window
moves from `N·Λ` to `N·Λ'` and the other four regions stay exactly
where they were, so the whole windowed contract transports on the
writer's cell claim plus the one new allocation bound. -/
theorem arenaStW_recol {nm : ArenaNames} {A : Impl.MArena Λ n₀ ℓp}
    {col' : Coloring A.N Λ'} {σ : Env} (h : ArenaStW nm hb A σ)
    (hnd5 : ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String).Nodup)
    (hlen : A.N * Λ' ≤ (σ.arrs nm.col).length)
    (hcells : ∀ (v : Fin A.N) (c : Fin Λ'),
      (σ.arrs nm.col).getD ((v : ℕ) * Λ' + (c : ℕ)) 0
        = if v ∈ col' c then 1 else 0) :
    ArenaStW nm hb (recol (Λ' := Λ') A col') σ := by
  have hnd5C := hnd5
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hnd5C
  obtain ⟨⟨hot', hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd5C
  have hoff : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.off
      = arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) nm.off := by
    rw [arenaWs_off, arenaWs_off]
  have htgt : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.tgt
      = arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) nm.tgt := by
    rw [arenaWs_tgt (Ne.symm hot'), arenaWs_tgt (Ne.symm hot')]
  have hup : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.up
      = arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) nm.up := by
    rw [arenaWs_up (Ne.symm hou) (Ne.symm htu) (Ne.symm hcu),
      arenaWs_up (Ne.symm hou) (Ne.symm htu) (Ne.symm hcu)]
  have hhist : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.hist
      = arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) nm.hist := by
    rw [arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh),
      arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh)]
  have hcolw : arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS) nm.col
      = some (A.N * Λ') := arenaWs_col (Ne.symm hoc) (Ne.symm htc)
  constructor
  · show FitsW (arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS)) σ
    intro b m hbm
    rcases arenaWs_some_elim hbm with rfl | rfl | rfl | rfl | rfl
    · exact h.fits _ m (by rw [← hoff]; exact hbm)
    · exact h.fits _ m (by rw [← htgt]; exact hbm)
    · rw [hcolw] at hbm
      cases hbm
      exact hlen
    · exact h.fits _ m (by rw [← hup]; exact hbm)
    · exact h.fits _ m (by rw [← hhist]; exact hbm)
  · show ArenaSt nm hb (recol (Λ' := Λ') A col')
      (winA (arenaWs nm Λ' ℓp hb A.N (σ.vars nm.nS)) σ)
    refine ⟨h.st.n_eq, ?_, ?_, ?_, ?_⟩
    · exact graphCsr_of_eq h.st.csr (arrs_winA_congr hoff σ)
        (arrs_winA_congr htgt σ)
    · refine ⟨length_arrs_winA hcolw hlen, fun v c => ?_⟩
      have hidx : (v : ℕ) * Λ' + (c : ℕ) < A.N * Λ' := by
        have h1 : (v : ℕ) + 1 ≤ A.N := v.2
        have h2 : (c : ℕ) + 1 ≤ Λ' := c.2
        calc (v : ℕ) * Λ' + (c : ℕ) < (v : ℕ) * Λ' + Λ' := by omega
          _ = ((v : ℕ) + 1) * Λ' := by ring
          _ ≤ A.N * Λ' := Nat.mul_le_mul_right _ h1
      rw [arrs_winA_some hcolw, getD_take_of_lt hidx]
      exact hcells v c
    · exact ⟨by rw [arrs_winA_congr hup σ]; exact h.st.up.1,
        fun v => by rw [arrs_winA_congr hup σ]; exact h.st.up.2 v⟩
    · exact histArr_congr_arrs h.st.hist (arrs_winA_congr hhist σ)

end Recolour

section Assembled

variable {L n₀ : ℕ}

open Classical in
/-- **The assembled child**: isolating the recoloured pre-isolation
child at the padded batch *is* `machChild` — `rfl`, because
`childArena.G = deleteVerts preG (range batchFn)` and `restrict`'s
carrier and renaming are `childArena`'s. This is the identity
`isolateCom_specW`'s output is read through. -/
theorem isolate_recol_eq_machChild (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {ℓc : ℕ}
    (Dp : Fin S.width → Fin (childN S A π u) → ℕ)
    (Dc : Fin (relPal Λ) → Fin (childN S A π u + 1) → ℕ)
    (chan : Fin (childN S A π u) → Fin ℓc → List (Fin (childN S A π u))) :
    Impl.MArena.isolate
        (⟨childN S A π u, preG S A π u,
          Impl.recordProfilesMS S.R (childColR S A π u) Dp Dc,
          (childArena S A π u).up, chan⟩ :
            Impl.MArena (isoPal (relPal Λ) S.width S.R) n₀ ℓc)
        (Set.range (batchFn S A π u))
      = machChild S A π u Dp Dc chan := rfl

open Classical in
/-- **`profilesCom_specW`'s colouring is `childColR`** — the second
half of `machChild_eq_ofArena`'s hypothesis, `rfl`: the stage returns
`Impl.ProfileTablesMS A.G w (relColoring A.col Set.univ) R Dp Dc`, and
at the restricted child `A.col` is `childCol0`, whose marker extension
is `childColR`. -/
theorem relColoring_restrict_col (S : Setup L) {Λ ℓpj : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (htab : Fin A.N → Fin ℓpj → List (Fin A.N)) :
    Driver.relColoring
        (((Impl.ofArena A htab).restrict (cluster S A π u)).col) Set.univ
      = childColR S A π u := rfl

end Assembled

/-! ## §4 The pass's whole budget, glue included -/

/-- **The pass's budget**: the five landed stage budgets (`prepStageK`)
plus the four glue programs that run between them — the cluster-row
copy, the connector scan, the batch builder and the colour writer. The
landed absorption lemmas price each glue program against `prepStageK`
*separately*; what the pass has to fit is their sum, which is this.

The constant-many scalar loads that set each stage's input cells are
**not** counted here: they are `O(1)` per stage, independent of every
dimension, and ride the same slack `prepPassK_le` leaves. -/
def prepPassK (cN cns dS Λc ℓp hb mb R : ℕ) : ℕ :=
  clusterRowK cN + centreIdxK cN + mkBatchK cN ℓp hb mb
    + colWriteK cN Λc mb R + prepStageK cN cns dS cN Λc ℓp hb mb R

/-- The cluster-row copy and the connector scan **share** `restrictK`'s
per-member charge: together they cost `31` per cluster member against
the `132` already charged. -/
theorem clusterRowK_add_centreIdxK_le_restrictK (dS k Λc ℓp hb : ℕ) :
    clusterRowK k + centreIdxK k ≤ restrictK dS k Λc ℓp hb := by
  have h : 31 * k ≤ k * (20 * Λc + (36 * hb + 42) * ℓp + 132) := by
    have h' : k * 31 ≤ k * (20 * Λc + (36 * hb + 42) * ℓp + 132) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  unfold clusterRowK centreIdxK restrictK
  omega

/-- The glue costs no more than the stages do: the whole pass is
`prepStageK` up to a schedule *factor*, never a new term. -/
theorem prepPassK_le_prepStageK (cN cns dS Λc ℓp hb mb R : ℕ) (hcN : 1 ≤ cN) :
    prepPassK cN cns dS Λc ℓp hb mb R
      ≤ 4 * prepStageK cN cns dS cN Λc ℓp hb mb R := by
  have h1 := clusterRowK_add_centreIdxK_le_restrictK dS cN Λc ℓp hb
  have h2 : restrictK dS cN Λc ℓp hb
      ≤ prepStageK cN cns dS cN Λc ℓp hb mb R := by
    unfold prepStageK; omega
  have h3 := mkBatchK_le_prepStageK cN cns dS Λc ℓp hb mb R hcN
  have h4 := colWriteK_le_prepStageK cN cns dS cN Λc ℓp hb mb R
  unfold prepPassK
  omega

/-- **The pass's budget fits §7's envelope, glue included** — the shape
`prepStageK_le` gives the stages, kept by the whole pass: `restrictK`
(§6.1's own column, which §7 absorbs into the leading coefficient) plus
a **schedule constant** times the child's weight `‖B₀‖ + 1`, a term of
§7's children column `c·Σ_u N_u`. **No `A.N` term is introduced** — the
`Θ(A.N²)` trap of §6.1's scratch paragraph survives the glue, because
every glue program is priced at the *child's* dimensions. -/
theorem prepPassK_le (cN cns dS Λc ℓp hb mb R : ℕ) (hcN : 1 ≤ cN) :
    prepPassK cN cns dS Λc ℓp hb mb R
      ≤ 4 * restrictK dS cN Λc ℓp hb
        + 4 * (800 * (R + 1) * (mb + Λc + 2) * (cN + cns + 1)) := by
  have h1 := prepPassK_le_prepStageK cN cns dS Λc ℓp hb mb R hcN
  have h2 := prepStageK_le cN cns dS cN Λc ℓp hb mb R
  omega

/-! ## §5 The frame data the lifts do not state -/

/-- **The frame and no-reallocation clauses, for any stage.** A `Spec`
carries a `Run`, and `Run` knows both that a command writes only the
arrays and scalars its syntax names and that no command changes an
array's *length*. `restrictCom_specW` states neither, while
`ChildLoadParts` demands both; this is the one step that supplies them
at every stage at once. -/
theorem Spec.frameA {B : ℕ} {P : Env → Prop} {c : Com}
    {Q : Env → Env → Prop} {K : ℕ} (h : Spec B P c Q K) :
    Spec B P c
      (fun σ σ' => Q σ σ' ∧
        (∀ b, b ∉ c.warrs → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length)) K := by
  intro σ hσ
  obtain ⟨σ', hrun, hq⟩ := h σ hσ
  exact ⟨σ', hrun, hq, fun b hb => hrun.frame_arr b hb,
    fun y hy => hrun.frame_var y hy, run_arrs_length_eq hrun⟩

/-- The restrict stage writes only the rank scratch and the child's
five regions — the membership side condition `Spec.frameA` is consumed
with. -/
theorem restrictCom_notMem_warrs {nmP nmC : ArenaNames} {la ra b : String}
    (h1 : b ≠ ra) (h2 : b ≠ nmC.off) (h3 : b ≠ nmC.tgt) (h4 : b ≠ nmC.col)
    (h5 : b ≠ nmC.up) (h6 : b ≠ nmC.hist) :
    b ∉ (restrictCom nmP nmC la ra).warrs := by
  rw [warrs_restrictCom]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1, h2, h3, h2, h4, h5, h6, h6, h1⟩

/-- The isolate stage writes only the two fresh output regions. -/
theorem isolateCom_notMem_warrs (nmI : ArenaNames) (oaO taO nsO ba : String)
    {b : String} (h1 : b ≠ oaO) (h2 : b ≠ taO) :
    b ∉ (isolateCom nmI oaO taO nsO ba).warrs := by
  rw [warrs_isolateCom]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1, h2, h1⟩

end Lax3Proofs.Prog
