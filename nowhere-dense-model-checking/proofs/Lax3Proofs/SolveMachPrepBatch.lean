import Lax3Proofs.SolveMachPrepPins

/-!
# F6c12-1b — the batch builder (item 1 of the leaf; item 2 not written)

`SolveMachPrepPins` §9 named the facts the batch builder closes against
and left the loop text unwritten. This file writes it.

**Item 1, the batch builder — done.** `mkBatchCom` is the program:

* a **wipe** of the bit region over the child's carrier;
* the **connector's mark** — one store, at `x₀`;
* a **channel-row marking scan**: the columns `e < rounds` of row `x₀`
  of the channel region, each read through `HistArr`'s stride-`hb+1`
  layout (length cell first, then the stored names), every stored name
  marked;
* a **carrier scan** whose invariant carries the running count
  `{y ∈ X ∧ y < a}.ncard` — *the running count is the slot*
  (`SolveMachPrepRun.ncard_lt_setEquiv`, off `Driver.setEquiv`'s being
  the **sorted** enumeration `Finset.orderIsoOfFin`) — writing the
  member with `c` members below it into index slot `c`;
* a **pad loop** filling the remaining slots with `x₀`.

**One bit vector, not two.** `range_batchFn_eq_batchSet` (Pins §9) says
`isolateCom_specW`'s `W = Set.range batchFn` and the scan's own
`batchSet` are the *same set*, so the marking scan's output serves the
isolation directly; `mkBatchCom_batch` states exactly that, at
`Set.range (batchFn …)`, alongside the index region.

**The index region is at length exactly `S.width`.**
`profilesCom_specW` asks for `(σ.arrs ba).length = mb` — an equality —
and the frame clause forbids reallocation, so the length arrives with
the state as `BatchWidthScr` and leaves with it: the program never
allocates, and `mkBatchCom_spec`'s postcondition carries the equality
forward verbatim.

## The budget

`mkBatchK cN ℓp hb mb = 31·cN + (16·hb + 25)·ℓp + 11·mb + 27`, and
`mkBatchK_le_prepStageK` shows it is **absorbed** — no new term in
`prepStageK`, and in particular **no `A.N` term** (§6.1's `Θ(A.N²)`
scratch trap):

* the three carrier passes ride `restrictK`'s per-member charge `132·k`
  at `k = cN` (the cluster's size *is* the child's carrier, `childN`);
* the channel-row scan rides the *same* per-member charge's channel
  column `k·(36·hb + 42)·ℓp` — the builder reads **one** row where
  `restrictCom` copies `k` of them;
* the pad's `11·mb` rides `profilesK`'s own `mb·batchK cN cns R`
  (`batchK ≥ 24`).

This is the cluster-row copy's precedent (`clusterRowK_le_restrictK`)
at the second of the three glue programs.

## Hazards honoured

* **Profiles are measured in `preG`, before isolation.** Nothing here
  moves the batch past `restrict`: the driver corollary reads the
  *restricted* child's channel row, `mem_batchSet_iff_chanRow_level`'s
  own object, and hands the bit region to the isolation unchanged.
* **`deleteVerts` isolates, it does not remove** — the carrier the
  scans run over is the child's whole carrier, before and after.
* **The pad is the connector, and duplicates are intended.** The pad
  loop writes `x₀` into every slot from `X.ncard` up, and
  `pad_eq_of_le_ncard` is what it proves; nothing dedupes.
* **`Driver.setEquiv` is the sorted enumeration.** The carrier scan
  runs left to right and the count-is-the-slot invariant is
  `ncard_lt_setEquiv`, which holds *because* `setEquiv` is
  `Finset.orderIsoOfFin`. An arbitrary bijection would break it.
* **IMP+ reads no array length** (`Imp.lean:158`): `cN`, `rounds` and
  `mb` all arrive in named scalar cells (`cn`, `jr`, `mw`), and each
  channel row's length is read out of its own length cell.

## What is here, and what is not

§1 the windowed channel region (`HistArrW`) and its two bridges —
`histArrW_of_win`, and `histArrW_of_arenaStW`, which is how the level's
own `ArenaStW` reaches the builder. §2 the four loops and the budget.
§3 the running count and its recurrence. §4 the four phase contracts.
§5 `mkBatchCom_spec`, the builder. §6 `mkBatchCom_batch`, the builder at
the driver's objects — `FinBitsW bb (Set.range (batchFn …))` and the
index region at `batchFn`, which are the two next stages' preconditions
verbatim.

**Item 2, the colour-region writer (`machChild.col` over the `isoPal`
layout), is NOT written here.** §7 supplies only the one thing it was
blocked on that nothing landed states: where `isoPal`'s three slot
families live as numerals (`isoOld_val`, `isoPd_val`, `isoPu_val`, all
`rfl`) and that every slot is exactly one of them (`isoPal_cases`).
The writer itself — a family-unrolled emitter over `mb` pd arrays and
`Λ+1` pu arrays, in `profilesCom`'s `batchSeq`/`classSeq` shape — is a
leaf of its own.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Driver

/-! ## §1 The channel region, windowed

`HistArr` pins the channel region at its exact length; the chain's
allocations are windowed (`ArenaStW`), so the builder — which reads the
region through the *allocation*, not the truncation — needs the `≤`
form, exactly as `FinBitsW` is the `≤` form of `FinBits`. -/

/-- **The windowed channel region**: `HistArr` with the exact length
relaxed to a fit. Same stride-`hb+1` layout: the `(v, p)` slot starts
at `(v·ℓp + p)·(hb+1)`, its first cell is the stored list's length, the
next cells its names in order. -/
def HistArrW (a : String) {N : ℕ} (ℓp hb : ℕ)
    (hist : Fin N → Fin ℓp → List (Fin N)) (σ : Env) : Prop :=
  N * ℓp * (hb + 1) ≤ (σ.arrs a).length ∧
    ∀ (v : Fin N) (p : Fin ℓp),
      (hist v p).length ≤ hb ∧
      (σ.arrs a).getD (((v : ℕ) * ℓp + p) * (hb + 1)) 0 = (hist v p).length ∧
      ∀ i : ℕ, ∀ hi : i < (hist v p).length,
        (σ.arrs a).getD (((v : ℕ) * ℓp + p) * (hb + 1) + 1 + i) 0
          = ((hist v p)[i] : ℕ)

/-- The last cell a row occupies is inside the region — the index bound
every read of the channel region rides. -/
theorem histIdx_lt {N ℓp hb : ℕ} (v : Fin N) (p : Fin ℓp) {i : ℕ}
    (hi : i ≤ hb) :
    ((v : ℕ) * ℓp + p) * (hb + 1) + i < N * ℓp * (hb + 1) := by
  have hvp : (v : ℕ) * ℓp + p + 1 ≤ N * ℓp := by
    have h1 : (v : ℕ) + 1 ≤ N := v.2
    have h2 : (p : ℕ) + 1 ≤ ℓp := p.2
    calc (v : ℕ) * ℓp + p + 1 ≤ (v : ℕ) * ℓp + ℓp := by omega
      _ = ((v : ℕ) + 1) * ℓp := by ring
      _ ≤ N * ℓp := Nat.mul_le_mul_right _ h1
  calc ((v : ℕ) * ℓp + p) * (hb + 1) + i
      < ((v : ℕ) * ℓp + p) * (hb + 1) + (hb + 1) := by omega
    _ = ((v : ℕ) * ℓp + p + 1) * (hb + 1) := by ring
    _ ≤ (N * ℓp) * (hb + 1) := Nat.mul_le_mul_right _ hvp

/-- **Bridge**: the exact region of a truncation, at the window of
exactly the region's size, is a windowed region of the allocation —
how `ArenaStW`'s own `HistArr` reaches the builder. -/
theorem histArrW_of_win {ws : String → Option ℕ} {a : String} {N ℓp hb : ℕ}
    {hist : Fin N → Fin ℓp → List (Fin N)} {σ : Env}
    (hws : ws a = some (N * ℓp * (hb + 1))) (hfit : FitsW ws σ)
    (h : HistArr a ℓp hb hist (winA ws σ)) : HistArrW a ℓp hb hist σ := by
  refine ⟨hfit a _ hws, fun v p => ?_⟩
  obtain ⟨hlen, hcell, hcells⟩ := h.2 v p
  refine ⟨hlen, ?_, fun i hi => ?_⟩
  · rw [arrs_winA_some hws] at hcell
    rwa [getD_take_of_lt
      (show ((v : ℕ) * ℓp + p) * (hb + 1) < N * ℓp * (hb + 1) by
        have := histIdx_lt (hb := hb) v p (Nat.zero_le hb); omega)] at hcell
  · have hce := hcells i hi
    rw [arrs_winA_some hws,
      getD_take_of_lt (by
        have := histIdx_lt (hb := hb) v p (show 1 + i ≤ hb by omega)
        omega)] at hce
    exact hce

/-- The windowed region reads one array: it transports along
agreement on it. -/
theorem histArrW_of_eq {a : String} {N ℓp hb : ℕ}
    {hist : Fin N → Fin ℓp → List (Fin N)} {σ σ' : Env}
    (h : HistArrW a ℓp hb hist σ) (ha : σ'.arrs a = σ.arrs a) :
    HistArrW a ℓp hb hist σ' := by
  refine ⟨by rw [ha]; exact h.1, fun v p => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 v p
  exact ⟨h1, by rw [ha]; exact h2, fun i hi => by rw [ha]; exact h3 i hi⟩

/-- **The bridge the chain uses**: the level's own channel region, read
off the windowed arena contract. `ArenaStW` holds `HistArr` of the
truncation at exactly the region's size, which is `histArrW_of_win`'s
hypothesis. -/
theorem histArrW_of_arenaStW {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env} (h : ArenaStW nm hb A σ)
    (hho : nm.hist ≠ nm.off) (hht : nm.hist ≠ nm.tgt)
    (hhc : nm.hist ≠ nm.col) (hhu : nm.hist ≠ nm.up) :
    HistArrW nm.hist ℓp hb A.hist σ :=
  histArrW_of_win (arenaWs_hist hho hht hhc hhu) h.fits h.st.hist

/-! ## §2 The programs, and the budget -/

/-- The counted scan from zero, in `Spec.forRangeZero`'s own shape:
`x := 0; while x < m do body`. Every loop below is one of these. -/
def forZero (x m : String) (body : Com) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) body)

/-- **The wipe**: the bit region cleared over the child's carrier
(`cn` cells — the child's dimension, never the parent's). -/
def wipeBitsCom (bb cn av : String) : Com :=
  forZero av cn
    (.seq (.store bb (.var av) (.lit 0))
      (.assign av (.add (.var av) (.lit 1))))

/-- **The channel-row marking scan**: the columns `e < jr` of row `cc`
of the channel region. `HistArr`'s layout is read literally — the
`(v, p)` slot starts at `(v·ℓp + p)·(hb+1)`, its first cell is the row's
length, the next cells its stored names — so the base is computed from
the two scalars and the two compile-time constants, the length is read
out of its own cell (IMP+ reads no array length), and each stored name
is marked. -/
def markRowCom (ha bb cc jr ec ic ln bs : String) (ℓp hb : ℕ) : Com :=
  forZero ec jr
    (.seq (.assign bs
        (.mul (.add (.mul (.var cc) (.lit ℓp)) (.var ec)) (.lit (hb + 1))))
      (.seq (.assign ln (.get ha (.var bs)))
        (.seq
          (forZero ic ln
            (.seq
              (.store bb (.get ha (.add (.var bs) (.add (.lit 1) (.var ic))))
                (.lit 1))
              (.assign ic (.add (.var ic) (.lit 1)))))
          (.assign ec (.add (.var ec) (.lit 1))))))

/-- **The carrier scan**: left to right over the child's carrier,
emitting each marked name into the next index slot. The counter `sc`
is the running count of members already emitted — which, because
`Driver.setEquiv` is the *sorted* enumeration, is exactly the slot the
next member belongs in. -/
def emitSlotsCom (bb bi cn av sc : String) : Com :=
  .seq (.assign sc (.lit 0))
    (forZero av cn
      (.seq
        (.ite (.eq (.get bb (.var av)) (.lit 1))
          (.seq (.store bi (.var sc) (.var av))
            (.assign sc (.add (.var sc) (.lit 1))))
          .skip)
        (.assign av (.add (.var av) (.lit 1)))))

/-- **The pad loop**: every remaining slot takes the connector's own
name. The duplicates are intended — `pad`'s width is exactly `mb`. -/
def padSlotsCom (bi cc sc mw : String) : Com :=
  .while (.lt (.var sc) (.var mw))
    (.seq (.store bi (.var sc) (.var cc))
      (.assign sc (.add (.var sc) (.lit 1))))

/-- **The batch builder**: wipe, mark the connector, scan the channel
row, emit the members in order, pad. One bit region and one index
region out. -/
def mkBatchCom (ha bb bi cc cn jr mw ec ic ln bs av sc : String)
    (ℓp hb : ℕ) : Com :=
  .seq (wipeBitsCom bb cn av)
    (.seq (.store bb (.var cc) (.lit 1))
      (.seq (markRowCom ha bb cc jr ec ic ln bs ℓp hb)
        (.seq (emitSlotsCom bb bi cn av sc) (padSlotsCom bi cc sc mw))))

/-- **The builder's budget**: three carrier passes (`11 + 20` per cell),
one channel row (`16·hb + 25` per column), one pad (`11` per slot), and
the loops' own prologues. -/
def mkBatchK (cN ℓp hb mb : ℕ) : ℕ :=
  31 * cN + (16 * hb + 25) * ℓp + 11 * mb + 27

/-- **The builder's budget is absorbed.** `restrictK` already charges
`132` per cluster member and `(36·hb + 42)·ℓp` per member for the
channel copy; the builder's three carrier passes cost `31` per member
and its channel scan reads **one** row, so both ride that column.
`profilesK`'s own `mb · batchK` (per padded slot, `≥ 24`) covers the
pad. So the glue adds **no new term** to `prepStageK` — in particular
no `A.N` term, §6.1's `Θ(A.N²)` scratch trap, since every figure here
is the child's.

`k := cN` is not a weakening: the cluster's size *is* the child's
carrier (`childN = (cluster …).ncard`). -/
theorem mkBatchK_le_prepStageK (cN cns dS Λc ℓp hb mb R : ℕ) (hcN : 1 ≤ cN) :
    mkBatchK cN ℓp hb mb ≤ prepStageK cN cns dS cN Λc ℓp hb mb R := by
  have hA : (16 * hb + 25) * ℓp ≤ cN * ((36 * hb + 42) * ℓp) :=
    calc (16 * hb + 25) * ℓp ≤ (36 * hb + 42) * ℓp :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 1 * ((36 * hb + 42) * ℓp) := (Nat.one_mul _).symm
      _ ≤ cN * ((36 * hb + 42) * ℓp) := Nat.mul_le_mul_right _ hcN
  have hB : cN * (20 * Λc + (36 * hb + 42) * ℓp + 132)
      = cN * (20 * Λc) + cN * ((36 * hb + 42) * ℓp) + 132 * cN := by ring
  have h1 : (16 * hb + 25) * ℓp + 31 * cN + 27 ≤ restrictK dS cN Λc ℓp hb := by
    unfold restrictK
    rw [hB]
    omega
  have hbk : 11 ≤ batchK cN cns R := by
    unfold batchK bfsK
    omega
  have h2 : 11 * mb ≤ profilesK mb (Λc + 1) cN cns R := by
    unfold profilesK
    have h := Nat.mul_le_mul_left mb hbk
    omega
  unfold mkBatchK prepStageK
  omega

/-! ## §3 The running count is the slot

`SolveMachPrepRun.ncard_lt_setEquiv` says the member with `c` members
below it is padded slot `c`. The carrier scan carries that count as a
scalar, so what it needs is the count's *recurrence*: one more member
crossed, one more slot. -/

section Count

variable {cN : ℕ} (X : Set (Fin cN))

/-- **The running count**: the members of `X` whose name is below the
scan's cursor. -/
noncomputable def belowCnt (t : ℕ) : ℕ := {y : Fin cN | y ∈ X ∧ (y : ℕ) < t}.ncard

@[simp] theorem belowCnt_zero : belowCnt X 0 = 0 := by
  have : {y : Fin cN | y ∈ X ∧ (y : ℕ) < 0} = ∅ := by
    ext y; simp
  rw [belowCnt, this, Set.ncard_empty]

/-- At a carrier name the count is `pad`'s own figure. -/
theorem belowCnt_eq (a : Fin cN) :
    belowCnt X (a : ℕ) = {y | y ∈ X ∧ y < a}.ncard := by
  have : {y : Fin cN | y ∈ X ∧ (y : ℕ) < (a : ℕ)} = {y | y ∈ X ∧ y < a} := by
    ext y; exact Iff.rfl
  rw [belowCnt, this]

/-- Crossing a member bumps the count. -/
theorem belowCnt_succ_of_mem {a : Fin cN} (ha : a ∈ X) :
    belowCnt X ((a : ℕ) + 1) = belowCnt X (a : ℕ) + 1 := by
  have hset : {y : Fin cN | y ∈ X ∧ (y : ℕ) < (a : ℕ) + 1}
      = insert a {y : Fin cN | y ∈ X ∧ (y : ℕ) < (a : ℕ)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hy, hlt⟩
      rcases Nat.lt_or_ge (y : ℕ) (a : ℕ) with h | h
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl (Fin.ext (by omega))
    · rintro (rfl | ⟨hy, hlt⟩)
      · exact ⟨ha, by omega⟩
      · exact ⟨hy, by omega⟩
  have hnot : a ∉ {y : Fin cN | y ∈ X ∧ (y : ℕ) < (a : ℕ)} := by
    simp only [Set.mem_setOf_eq]
    rintro ⟨-, h⟩
    omega
  rw [belowCnt, belowCnt, hset, Set.ncard_insert_of_notMem hnot (Set.toFinite _)]

/-- Crossing a non-member does not. -/
theorem belowCnt_succ_of_not_mem {a : Fin cN} (ha : a ∉ X) :
    belowCnt X ((a : ℕ) + 1) = belowCnt X (a : ℕ) := by
  have hset : {y : Fin cN | y ∈ X ∧ (y : ℕ) < (a : ℕ) + 1}
      = {y : Fin cN | y ∈ X ∧ (y : ℕ) < (a : ℕ)} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hy, hlt⟩
      refine ⟨hy, ?_⟩
      rcases Nat.lt_or_ge (y : ℕ) (a : ℕ) with h | h
      · exact h
      · exact absurd (show a ∈ X from (Fin.ext (show (a : ℕ) = (y : ℕ) by omega)) ▸ hy) ha
    · rintro ⟨hy, hlt⟩
      exact ⟨hy, by omega⟩
  rw [belowCnt, belowCnt, hset]

/-- At the end of the carrier the count is the whole membership. -/
theorem belowCnt_carrier : belowCnt X cN = X.ncard := by
  have : {y : Fin cN | y ∈ X ∧ (y : ℕ) < cN} = X := by
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  rw [belowCnt, this]

/-- The count never exceeds the total. -/
theorem belowCnt_le_ncard (t : ℕ) : belowCnt X t ≤ X.ncard :=
  Set.ncard_le_ncard (fun _ hy => hy.1) (Set.toFinite _)

/-- A member's own count is strictly below the total — the bound that
makes the slot the scan writes a legal one. -/
theorem belowCnt_lt_ncard {a : Fin cN} (ha : a ∈ X) :
    belowCnt X (a : ℕ) < X.ncard := by
  refine Set.ncard_lt_ncard ⟨fun y hy => hy.1, ?_⟩ (Set.toFinite _)
  intro hsub
  exact absurd (hsub ha).2 (by omega)

end Count

/-! ## §4 The phases -/

section Phases

variable {B : ℕ}

private theorem getD_set_self {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem getD_set_of_ne {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c).getD q 0 = l.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
    List.getD_eq_getElem?_getD]

private theorem getElem?_of_lt (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- **The wipe, specified**: the bit region reads back zero on the whole
child carrier; one scalar and one array written, no reallocation. -/
theorem wipeBitsCom_spec {cN : ℕ} {bb cn av : String} (hNB : cN < B)
    (hav_cn : av ≠ cn) :
    Spec B
      (fun σ => σ.vars cn = cN ∧ cN ≤ (σ.arrs bb).length)
      (wipeBitsCom bb cn av)
      (fun σ σ' => (∀ a : Fin cN, (σ'.arrs bb).getD (a : ℕ) 0 = 0) ∧
        (∀ y, y ≠ av → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ bb → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (11 * cN + 6) := by
  intro σ hσ
  obtain ⟨hcn, hlen⟩ := hσ
  set I : Env → Prop := fun τ =>
    τ.vars cn = cN ∧ τ.vars av ≤ cN ∧ cN ≤ (τ.arrs bb).length ∧
      ∀ t, t < τ.vars av → (τ.arrs bb).getD t 0 = 0 with hI_def
  have hbody : Spec B (fun τ => I τ ∧ τ.vars av < cN)
      (.seq (.store bb (.var av) (.lit 0))
        (.assign av (.add (.var av) (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars av = τ.vars av + 1) 7 := by
    rintro τ ⟨⟨hcnτ, hle, hlenτ, hcells⟩, hlt⟩
    set t : ℕ := τ.vars av with ht_def
    have hB1 : 1 < B := by omega
    have hrun1 : Run B (.store bb (.var av) (.lit 0)) τ (τ.setArr bb t 0) 3 :=
      Run.store (evalB_var (by omega)) (evalB_lit (by omega)) (by omega)
    have hrun2 : Run B (.assign av (.add (.var av) (.lit 1)))
        (τ.setArr bb t 0) ((τ.setArr bb t 0).setVar av (t + 1)) 4 := by
      have hb : (Expr.bin .add (.var av) (.lit 1)).evalB B (τ.setArr bb t 0)
          = some (t + 1) := by
        refine evalB_bin (evalB_var ?_) (evalB_lit hB1)
          (by simpa using (by omega : t + 1 < B))
        rw [vars_setArr]; omega
      simpa using Run.assign (x := av) hb
    refine ⟨_, (hrun1.seq hrun2).mono (by omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hav_cn), vars_setArr]
      exact hcnτ
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, List.length_set]; exact hlenτ
    · intro t' ht'
      rw [vars_setVar, if_pos rfl] at ht'
      rw [arrs_setVar, arrs_setArr, if_pos rfl]
      rcases Nat.lt_or_ge t' t with hlt' | hge'
      · rw [getD_set_of_ne (by omega)]; exact hcells t' (by omega)
      · obtain rfl : t' = t := by omega
        rw [getD_set_self (by omega)]
    · rw [vars_setVar, if_pos rfl]
  have hloop := Spec.forRangeZero (B := B) av cn I cN 7 hNB
    (fun _ hτ => hτ.2.1) (fun _ hτ => hτ.1) hbody
  have hIinit : I (σ.setVar av 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hav_cn)]; exact hcn
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [arrs_setVar]; exact hlen
    · intro t ht
      rw [vars_setVar, if_pos rfl] at ht
      omega
  obtain ⟨σ', hrun, hIfin, hfin⟩ := hloop.run hIinit
  refine ⟨σ', hrun, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hIfin.2.2.2 (a : ℕ) (by rw [hfin]; exact a.2)
  · intro y hy
    refine hrun.frame_var y ?_
    simp only [Com.wvars, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    tauto
  · intro b hb
    refine hrun.frame_arr b ?_
    simp only [Com.warrs, List.nil_append, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · exact run_arrs_length_eq hrun

open Classical in
/-- **The channel-row marking scan, specified**: every name stored in
row `cc` of the channel region, at a column that carries a round, is
marked in the bit region; the marks already there are kept. Four
scalars and one array written, no reallocation.

This is §5 line 19's `⋃_{e < rounds} B₀.hist[cc][e]`, read off the
region the machine actually holds. -/
theorem markRowCom_spec {cN ℓp hb rounds : ℕ}
    {hist : Fin cN → Fin ℓp → List (Fin cN)} {x₀ : Fin cN}
    {Base : Set (Fin cN)} {ha bb cc jr ec ic ln bs : String}
    (hround : rounds ≤ ℓp) (hNB : cN < B) (hRB : cN * ℓp * (hb + 1) < B)
    (hha_bb : ha ≠ bb)
    (hec_jr : ec ≠ jr) (hec_cc : ec ≠ cc)
    (hic_jr : ic ≠ jr) (hic_cc : ic ≠ cc) (hic_ln : ic ≠ ln)
    (hic_bs : ic ≠ bs) (hic_ec : ic ≠ ec)
    (hln_jr : ln ≠ jr) (hln_cc : ln ≠ cc) (hln_ec : ln ≠ ec)
    (hbs_jr : bs ≠ jr) (hbs_cc : bs ≠ cc) (hbs_ec : bs ≠ ec)
    (hbs_ln : bs ≠ ln) :
    Spec B
      (fun σ => HistArrW ha ℓp hb hist σ ∧
        σ.vars cc = (x₀ : ℕ) ∧ σ.vars jr = rounds ∧
        cN ≤ (σ.arrs bb).length ∧
        ∀ a : Fin cN, (σ.arrs bb).getD (a : ℕ) 0 = if a ∈ Base then 1 else 0)
      (markRowCom ha bb cc jr ec ic ln bs ℓp hb)
      (fun σ σ' =>
        (∀ a : Fin cN, (σ'.arrs bb).getD (a : ℕ) 0 =
          if (a ∈ Base ∨ ∃ e : Fin ℓp, (e : ℕ) < rounds ∧ a ∈ hist x₀ e)
            then 1 else 0) ∧
        (∀ y, y ≠ ec → y ≠ ic → y ≠ ln → y ≠ bs → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ bb → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      ((16 * hb + 25) * ℓp + 6) := by
  intro σ hσ
  obtain ⟨hha, hcc, hjr, hbbL, hcells0⟩ := hσ
  obtain ⟨hhaLen, hhaRow⟩ := hha
  have hcNpos : 0 < cN := lt_of_le_of_lt (Nat.zero_le _) x₀.2
  have hB1 : 1 < B := by omega
  have hℓpB : ℓp < B := by
    rcases Nat.eq_zero_or_pos ℓp with h | h
    · omega
    · have h1 : ℓp ≤ cN * ℓp * (hb + 1) := by
        calc ℓp = 1 * ℓp * 1 := by ring
          _ ≤ cN * ℓp * (hb + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hcNpos) (by omega)
      omega
  set I : Env → Prop := fun τ =>
    τ.vars jr = rounds ∧ τ.vars cc = (x₀ : ℕ) ∧ τ.vars ec ≤ rounds ∧
      cN ≤ (τ.arrs bb).length ∧ τ.arrs ha = σ.arrs ha ∧
      ∀ a : Fin cN, (τ.arrs bb).getD (a : ℕ) 0 =
        if (a ∈ Base ∨ ∃ e : Fin ℓp, (e : ℕ) < τ.vars ec ∧ a ∈ hist x₀ e)
          then 1 else 0 with hI_def
  have hbody : Spec B (fun τ => I τ ∧ τ.vars ec < rounds)
      (.seq (.assign bs
          (.mul (.add (.mul (.var cc) (.lit ℓp)) (.var ec)) (.lit (hb + 1))))
        (.seq (.assign ln (.get ha (.var bs)))
          (.seq
            (forZero ic ln
              (.seq
                (.store bb (.get ha (.add (.var bs) (.add (.lit 1) (.var ic))))
                  (.lit 1))
                (.assign ic (.add (.var ic) (.lit 1)))))
            (.assign ec (.add (.var ec) (.lit 1))))))
      (fun τ τ' => I τ' ∧ τ'.vars ec = τ.vars ec + 1) (16 * hb + 21) := by
    rintro τ ⟨⟨hjrτ, hccτ, hleτ, hbbLτ, hhaτ, hcellsτ⟩, hlt⟩
    have he₀ : τ.vars ec < ℓp := lt_of_lt_of_le hlt hround
    obtain ⟨e, hev⟩ : ∃ e : Fin ℓp, (e : ℕ) = τ.vars ec := ⟨⟨τ.vars ec, he₀⟩, rfl⟩
    obtain ⟨hLhb, hbaseCell, hentries⟩ := hhaRow x₀ e
    set base : ℕ := ((x₀ : ℕ) * ℓp + (e : ℕ)) * (hb + 1) with hbase_def
    have hbaseLt : base < cN * ℓp * (hb + 1) := by
      have h := histIdx_lt (hb := hb) x₀ e (Nat.zero_le hb)
      rw [hbase_def]
      omega
    have hbaseB : base < B := by omega
    have hhbB : hb + 1 < B := by
      have h1 : hb + 1 ≤ cN * ℓp * (hb + 1) := by
        calc hb + 1 = 1 * 1 * (hb + 1) := by ring
          _ ≤ cN * ℓp * (hb + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hcNpos (by omega))
      omega
    have hsumB : (x₀ : ℕ) * ℓp + (e : ℕ) < B := by
      have h : ((x₀ : ℕ) * ℓp + (e : ℕ)) * 1 ≤ base :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_one] at h
      omega
    -- the base of this column's row
    have hrun1 : Run B (.assign bs
        (.mul (.add (.mul (.var cc) (.lit ℓp)) (.var ec)) (.lit (hb + 1))))
        τ (τ.setVar bs base) 8 := by
      have h1 : (Expr.mul (.var cc) (.lit ℓp)).evalB B τ
          = some ((x₀ : ℕ) * ℓp) := by
        have h := evalB_bin (op := .mul)
          (evalB_var (x := cc) (σ := τ) (by rw [hccτ]; omega))
          (evalB_lit (σ := τ) hℓpB)
          (show τ.vars cc * ℓp < B by rw [hccτ]; omega)
        rw [hccτ] at h
        exact h
      have h2 : (Expr.add (.mul (.var cc) (.lit ℓp)) (.var ec)).evalB B τ
          = some ((x₀ : ℕ) * ℓp + (e : ℕ)) := by
        have h := evalB_bin (op := .add) h1
          (evalB_var (x := ec) (σ := τ) (by omega))
          (show (x₀ : ℕ) * ℓp + τ.vars ec < B by omega)
        rw [← hev] at h
        exact h
      have h3 : (Expr.mul (.add (.mul (.var cc) (.lit ℓp)) (.var ec))
          (.lit (hb + 1))).evalB B τ = some base :=
        evalB_bin (op := .mul) h2 (evalB_lit (σ := τ) hhbB)
          (show ((x₀ : ℕ) * ℓp + (e : ℕ)) * (hb + 1) < B by omega)
      simpa using Run.assign (x := bs) h3
    set τ1 : Env := τ.setVar bs base with hτ1_def
    have hτ1ha : τ1.arrs ha = σ.arrs ha := by
      rw [hτ1_def, arrs_setVar]; exact hhaτ
    have hτ1bs : τ1.vars bs = base := by rw [hτ1_def, vars_setVar, if_pos rfl]
    -- the row's stored length
    have hbaseLen : base < (σ.arrs ha).length := by omega
    have hrun2 : Run B (.assign ln (.get ha (.var bs))) τ1
        (τ1.setVar ln (hist x₀ e).length) 3 := by
      have h : (Expr.get ha (.var bs)).evalB B τ1
          = some (hist x₀ e).length := by
        refine evalB_get (evalB_var (by rw [hτ1bs]; omega)) ?_ (by omega)
        rw [hτ1bs, hτ1ha, ← hbaseCell]
        exact getElem?_of_lt _ _ hbaseLen
      simpa using Run.assign (x := ln) h
    set τ2 : Env := τ1.setVar ln (hist x₀ e).length with hτ2_def
    -- the inner scan over the row's entries
    set J : Env → Prop := fun ρ =>
      ρ.vars ln = (hist x₀ e).length ∧ ρ.vars bs = base ∧
        ρ.vars ic ≤ (hist x₀ e).length ∧
        cN ≤ (ρ.arrs bb).length ∧ ρ.arrs ha = σ.arrs ha ∧
        ∀ a : Fin cN, (ρ.arrs bb).getD (a : ℕ) 0 =
          if (a ∈ Base ∨ (∃ e' : Fin ℓp, (e' : ℕ) < (e : ℕ) ∧ a ∈ hist x₀ e') ∨
              a ∈ (hist x₀ e).take (ρ.vars ic))
            then 1 else 0 with hJ_def
    have hbody2 : Spec B (fun ρ => J ρ ∧ ρ.vars ic < (hist x₀ e).length)
        (.seq
          (.store bb (.get ha (.add (.var bs) (.add (.lit 1) (.var ic))))
            (.lit 1))
          (.assign ic (.add (.var ic) (.lit 1))))
        (fun ρ ρ' => J ρ' ∧ ρ'.vars ic = ρ.vars ic + 1) 12 := by
      rintro ρ ⟨⟨hlnρ, hbsρ, hleρ, hbbρ, hhaρ, hcellsρ⟩, hltρ⟩
      set i : ℕ := ρ.vars ic with hi_def
      set z : Fin cN := (hist x₀ e)[i]'hltρ with hz_def
      have htake : ∀ b : Fin cN,
          b ∈ (hist x₀ e).take (i + 1) ↔ b ∈ (hist x₀ e).take i ∨ b = z := by
        intro b
        have hsome : (hist x₀ e)[i]? = some z := by
          rw [List.getElem?_eq_getElem hltρ]
        rw [List.take_add_one, List.mem_append, hsome]
        simp
      have hidxLt : base + 1 + i < cN * ℓp * (hb + 1) := by
        have h := histIdx_lt (hb := hb) x₀ e (show 1 + i ≤ hb by omega)
        rw [hbase_def]
        omega
      have hentry : (σ.arrs ha).getD (base + 1 + i) 0 = (z : ℕ) :=
        hentries i hltρ
      have hidxE : (Expr.add (.var bs) (.add (.lit 1) (.var ic))).evalB B ρ
          = some (base + 1 + i) := by
        have h1 : (Expr.add (.lit 1) (.var ic)).evalB B ρ = some (1 + i) :=
          evalB_bin (op := .add) (evalB_lit (σ := ρ) hB1)
            (evalB_var (x := ic) (σ := ρ) (by omega))
            (show 1 + ρ.vars ic < B by omega)
        have h2 := evalB_bin (op := .add)
          (evalB_var (x := bs) (σ := ρ) (by rw [hbsρ]; omega)) h1
          (show ρ.vars bs + (1 + i) < B by rw [hbsρ]; omega)
        rw [hbsρ] at h2
        rw [show Bop.add.apply base (1 + i) = base + 1 + i from by
          show base + (1 + i) = base + 1 + i
          omega] at h2
        exact h2
      have hgetE :
          (Expr.get ha (.add (.var bs) (.add (.lit 1) (.var ic)))).evalB B ρ
            = some (z : ℕ) := by
        refine evalB_get hidxE ?_ (by have := z.2; omega)
        rw [hhaρ, ← hentry]
        exact getElem?_of_lt _ _ (by omega)
      have hrunA : Run B
          (.store bb (.get ha (.add (.var bs) (.add (.lit 1) (.var ic))))
            (.lit 1))
          ρ (ρ.setArr bb (z : ℕ) 1) 8 := by
        have h := Run.store (a := bb) hgetE (evalB_lit (σ := ρ) hB1)
          (show (z : ℕ) < (ρ.arrs bb).length by have := z.2; omega)
        simpa using h
      have hrunB : Run B (.assign ic (.add (.var ic) (.lit 1)))
          (ρ.setArr bb (z : ℕ) 1)
          ((ρ.setArr bb (z : ℕ) 1).setVar ic (i + 1)) 4 := by
        have hb : (Expr.bin .add (.var ic) (.lit 1)).evalB B
            (ρ.setArr bb (z : ℕ) 1) = some (i + 1) := by
          refine evalB_bin (evalB_var ?_) (evalB_lit hB1) ?_
          · rw [vars_setArr]; omega
          · show (ρ.setArr bb (z : ℕ) 1).vars ic + 1 < B
            rw [vars_setArr]; omega
        simpa using Run.assign (x := ic) hb
      refine ⟨_, (hrunA.seq hrunB).mono (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [vars_setVar, if_neg (Ne.symm hic_ln), vars_setArr]; exact hlnρ
      · rw [vars_setVar, if_neg (Ne.symm hic_bs), vars_setArr]; exact hbsρ
      · rw [vars_setVar, if_pos rfl]; omega
      · rw [arrs_setVar, arrs_setArr, if_pos rfl, List.length_set]; exact hbbρ
      · rw [arrs_setVar, arrs_setArr, if_neg hha_bb]; exact hhaρ
      · intro a
        rw [arrs_setVar, arrs_setArr, if_pos rfl, vars_setVar, if_pos rfl]
        by_cases hza : (a : ℕ) = (z : ℕ)
        · have haz : a = z := Fin.ext hza
          rw [hza, getD_set_self (by have := z.2; omega), if_pos]
          exact Or.inr (Or.inr ((htake a).mpr (Or.inr haz)))
        · rw [getD_set_of_ne (fun h => hza h.symm), hcellsρ a]
          refine if_congr ⟨?_, ?_⟩ rfl rfl
          · rintro (h | h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ((htake a).mpr (Or.inl h)))
          · rintro (h | h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · rcases (htake a).mp h with h' | h'
              · exact Or.inr (Or.inr h')
              · exact absurd (congrArg (fun w : Fin cN => (w : ℕ)) h') hza
      · rw [vars_setVar, if_pos rfl]
    have hLB : (hist x₀ e).length < B := by omega
    have hloop2 := Spec.forRangeZero (B := B) ic ln J (hist x₀ e).length 12 hLB
      (fun _ hρ => hρ.2.2.1) (fun _ hρ => hρ.1) hbody2
    have hJinit : J (τ2.setVar ic 0) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [vars_setVar, if_neg (Ne.symm hic_ln), hτ2_def, vars_setVar,
          if_pos rfl]
      · rw [vars_setVar, if_neg (Ne.symm hic_bs), hτ2_def, vars_setVar,
          if_neg hbs_ln, hτ1_def, vars_setVar, if_pos rfl]
      · rw [vars_setVar, if_pos rfl]; omega
      · rw [arrs_setVar, hτ2_def, arrs_setVar, hτ1_def, arrs_setVar]
        exact hbbLτ
      · rw [arrs_setVar, hτ2_def, arrs_setVar]; exact hτ1ha
      · intro a
        rw [arrs_setVar, hτ2_def, arrs_setVar, hτ1_def, arrs_setVar,
          vars_setVar, if_pos rfl, hcellsτ a, List.take_zero]
        refine if_congr ⟨?_, ?_⟩ rfl rfl
        · rintro (h | ⟨e', he', hz⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨e', by omega, hz⟩)
        · rintro (h | ⟨e', he', hz⟩ | h)
          · exact Or.inl h
          · exact Or.inr ⟨e', by omega, hz⟩
          · exact absurd h (List.not_mem_nil)
    obtain ⟨τ3, hrun3, hJfin, hicfin⟩ := hloop2.run hJinit
    obtain ⟨hlnfin, hbsfin, hlefin, hbbfin, hhafin, hcellsfin⟩ := hJfin
    have hframe3 : ∀ y, y ≠ ic → τ3.vars y = τ2.vars y := by
      intro y hy
      refine hrun3.frame_var y ?_
      simp only [Com.wvars, List.nil_append, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      tauto
    have hjr3 : τ3.vars jr = rounds := by
      rw [hframe3 jr (Ne.symm hic_jr), hτ2_def, vars_setVar,
        if_neg (Ne.symm hln_jr), hτ1_def, vars_setVar, if_neg (Ne.symm hbs_jr)]
      exact hjrτ
    have hcc3 : τ3.vars cc = (x₀ : ℕ) := by
      rw [hframe3 cc (Ne.symm hic_cc), hτ2_def, vars_setVar,
        if_neg (Ne.symm hln_cc), hτ1_def, vars_setVar, if_neg (Ne.symm hbs_cc)]
      exact hccτ
    have hec3 : τ3.vars ec = τ.vars ec := by
      rw [hframe3 ec (Ne.symm hic_ec), hτ2_def, vars_setVar,
        if_neg (Ne.symm hln_ec), hτ1_def, vars_setVar, if_neg (Ne.symm hbs_ec)]
    -- the column's bump
    have hrun4 : Run B (.assign ec (.add (.var ec) (.lit 1))) τ3
        (τ3.setVar ec (τ.vars ec + 1)) 4 := by
      have hb : (Expr.bin .add (.var ec) (.lit 1)).evalB B τ3
          = some (τ.vars ec + 1) := by
        have h := evalB_bin (op := .add)
          (evalB_var (x := ec) (σ := τ3) (by rw [hec3]; omega))
          (evalB_lit (σ := τ3) hB1)
          (show τ3.vars ec + 1 < B by rw [hec3]; omega)
        rw [hec3] at h
        exact h
      simpa using Run.assign (x := ec) hb
    refine ⟨_, ((hrun1.seq (hrun2.seq (hrun3.seq hrun4))).mono (by omega)),
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hec_jr)]; exact hjr3
    · rw [vars_setVar, if_neg (Ne.symm hec_cc)]; exact hcc3
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [arrs_setVar]; exact hbbfin
    · rw [arrs_setVar]; exact hhafin
    · intro a
      rw [arrs_setVar, vars_setVar, if_pos rfl, hcellsfin a, hicfin,
        List.take_length]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro (h | ⟨e', he', hz⟩ | h)
        · exact Or.inl h
        · exact Or.inr ⟨e', by omega, hz⟩
        · exact Or.inr ⟨e, by omega, h⟩
      · rintro (h | ⟨e', he', hz⟩)
        · exact Or.inl h
        · rcases Nat.lt_or_ge (e' : ℕ) (e : ℕ) with h' | h'
          · exact Or.inr (Or.inl ⟨e', h', hz⟩)
          · have hee : e' = e := Fin.ext (by omega)
            subst hee
            exact Or.inr (Or.inr hz)
    · rw [vars_setVar, if_pos rfl]
  have hloop := Spec.forRangeZero (B := B) ec jr I rounds (16 * hb + 21)
    (by omega) (fun _ hτ => hτ.2.2.1) (fun _ hτ => hτ.1) hbody
  have hIinit : I (σ.setVar ec 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hec_jr)]; exact hjr
    · rw [vars_setVar, if_neg (Ne.symm hec_cc)]; exact hcc
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [arrs_setVar]; exact hbbL
    · rw [arrs_setVar]
    · intro a
      rw [arrs_setVar, vars_setVar, if_pos rfl, hcells0 a]
      refine if_congr ⟨Or.inl, ?_⟩ rfl rfl
      rintro (h | ⟨e', he', -⟩)
      · exact h
      · omega
  obtain ⟨σ', hrun, hIfin, hfin⟩ := hloop.run hIinit
  obtain ⟨-, -, -, -, -, hcellsfin⟩ := hIfin
  refine ⟨σ', hrun.mono ?_, ?_, ?_, ?_, ?_⟩
  · have h : (16 * hb + 21 + 4) * rounds ≤ (16 * hb + 25) * ℓp :=
      Nat.mul_le_mul_left _ hround
    omega
  · intro a
    rw [hcellsfin a, hfin]
  · intro y h1 h2 h3 h4
    refine hrun.frame_var y ?_
    simp only [forZero, Com.wvars, List.nil_append, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    tauto
  · intro b hb
    refine hrun.frame_arr b ?_
    simp only [forZero, Com.warrs, List.nil_append, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · exact run_arrs_length_eq hrun


open Classical in
/-- **The carrier scan, specified**: the marked names, left to right,
into the index region's first `X.ncard` slots — slot `c` receiving the
member with exactly `c` members below it (`pad_eq_of_ncard_lt`, off the
sorted enumeration). The count leaves in the `sc` cell. Two scalars and
one array written, no reallocation. -/
theorem emitSlotsCom_spec {cN mb : ℕ} {X : Set (Fin cN)} {x₀ : Fin cN}
    {bb bi cn av sc : String}
    (hNB : cN < B) (hmbB : mb < B) (hXmb : X.ncard ≤ mb)
    (hbb_bi : bb ≠ bi) (hav_cn : av ≠ cn) (hav_sc : av ≠ sc)
    (hsc_cn : sc ≠ cn) :
    Spec B
      (fun σ => σ.vars cn = cN ∧ cN ≤ (σ.arrs bb).length ∧
        (σ.arrs bi).length = mb ∧
        ∀ a : Fin cN, (σ.arrs bb).getD (a : ℕ) 0 = if a ∈ X then 1 else 0)
      (emitSlotsCom bb bi cn av sc)
      (fun σ σ' => σ'.vars sc = X.ncard ∧ (σ'.arrs bi).length = mb ∧
        (∀ i : Fin mb, (i : ℕ) < X.ncard →
          (σ'.arrs bi).getD (i : ℕ) 0 = ((pad X x₀ i : Fin cN) : ℕ)) ∧
        (∀ y, y ≠ av → y ≠ sc → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ bi → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (20 * cN + 8) := by
  intro σ hσ
  obtain ⟨hcn, hbbL, hbiL, hbits⟩ := hσ
  set K : Env → Prop := fun ρ =>
    ρ.vars cn = cN ∧ ρ.vars av ≤ cN ∧ ρ.vars sc = belowCnt X (ρ.vars av) ∧
      cN ≤ (ρ.arrs bb).length ∧ (ρ.arrs bi).length = mb ∧
      (∀ a : Fin cN, (ρ.arrs bb).getD (a : ℕ) 0 = if a ∈ X then 1 else 0) ∧
      (∀ i : Fin mb, (i : ℕ) < ρ.vars sc →
        (ρ.arrs bi).getD (i : ℕ) 0 = ((pad X x₀ i : Fin cN) : ℕ)) with hK_def
  have hbody : Spec B (fun ρ => K ρ ∧ ρ.vars av < cN)
      (.seq
        (.ite (.eq (.get bb (.var av)) (.lit 1))
          (.seq (.store bi (.var sc) (.var av))
            (.assign sc (.add (.var sc) (.lit 1))))
          .skip)
        (.assign av (.add (.var av) (.lit 1))))
      (fun ρ ρ' => K ρ' ∧ ρ'.vars av = ρ.vars av + 1) 16 := by
    rintro ρ ⟨⟨hcnρ, hleρ, hscρ, hbbρ, hbiρ, hbitsρ, hslots⟩, hltρ⟩
    set t : ℕ := ρ.vars av with ht_def
    set a : Fin cN := ⟨t, hltρ⟩ with ha_def
    have hB1 : 1 < B := by omega
    have hscB : ρ.vars sc < B := by
      have h := belowCnt_le_ncard X t
      omega
    have hgetE : (Expr.get bb (.var av)).evalB B ρ
        = some (if a ∈ X then 1 else 0) := by
      refine evalB_get (evalB_var (by omega)) ?_ (by split <;> omega)
      have h := hbitsρ a
      rw [← h]
      exact getElem?_of_lt _ _ (by have := a.2; omega)
    -- the marked case: the member goes into the slot its count names
    have hstep : ∃ ρ₁, Run B
        (.ite (.eq (.get bb (.var av)) (.lit 1))
          (.seq (.store bi (.var sc) (.var av))
            (.assign sc (.add (.var sc) (.lit 1))))
          .skip) ρ ρ₁ 12 ∧
        ρ₁.vars sc = belowCnt X (t + 1) ∧ ρ₁.vars av = t ∧
        ρ₁.vars cn = cN ∧ ρ₁.arrs bb = ρ.arrs bb ∧
        (ρ₁.arrs bi).length = mb ∧
        (∀ i : Fin mb, (i : ℕ) < ρ₁.vars sc →
          (ρ₁.arrs bi).getD (i : ℕ) 0 = ((pad X x₀ i : Fin cN) : ℕ)) := by
      by_cases haX : a ∈ X
      · have hcond : (Cond.eq (.get bb (.var av)) (.lit 1)).evalB B ρ
            = some true := by
          have h := evalB_condEq hgetE (evalB_lit (σ := ρ) hB1)
          rw [if_pos haX] at h
          simpa using h
        have hcnt : ρ.vars sc = belowCnt X (a : ℕ) := by rw [hscρ]
        have hltm : ρ.vars sc < mb := by
          have h := belowCnt_lt_ncard X haX
          omega
        have hrunS : Run B (.store bi (.var sc) (.var av)) ρ
            (ρ.setArr bi (ρ.vars sc) t) 3 :=
          Run.store (evalB_var hscB) (evalB_var (by omega)) (by omega)
        have hrunB : Run B (.assign sc (.add (.var sc) (.lit 1)))
            (ρ.setArr bi (ρ.vars sc) t)
            ((ρ.setArr bi (ρ.vars sc) t).setVar sc (ρ.vars sc + 1)) 4 := by
          have hb : (Expr.bin .add (.var sc) (.lit 1)).evalB B
              (ρ.setArr bi (ρ.vars sc) t) = some (ρ.vars sc + 1) := by
            refine evalB_bin (evalB_var ?_) (evalB_lit hB1) ?_
            · rw [vars_setArr]; omega
            · show (ρ.setArr bi (ρ.vars sc) t).vars sc + 1 < B
              rw [vars_setArr]; omega
          simpa using Run.assign (x := sc) hb
        have hpad : (pad X x₀ (⟨ρ.vars sc, hltm⟩ : Fin mb) : Fin cN) = a :=
          pad_eq_of_ncard_lt haX (by rw [← belowCnt_eq, ← hcnt]) hltm
        refine ⟨_, (Run.ite_true hcond (hrunS.seq hrunB)).mono (by simp),
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [vars_setVar, if_pos rfl, hcnt]
          exact (belowCnt_succ_of_mem X haX).symm
        · rw [vars_setVar, if_neg hav_sc, vars_setArr]
        · rw [vars_setVar, if_neg (Ne.symm hsc_cn), vars_setArr]; exact hcnρ
        · rw [arrs_setVar, arrs_setArr, if_neg hbb_bi]
        · rw [arrs_setVar, arrs_setArr, if_pos rfl, List.length_set]; exact hbiρ
        · intro i hi
          rw [vars_setVar, if_pos rfl] at hi
          rw [arrs_setVar, arrs_setArr, if_pos rfl]
          rcases Nat.lt_or_ge (i : ℕ) (ρ.vars sc) with h' | h'
          · rw [getD_set_of_ne (by omega)]
            exact hslots i h'
          · have hieq : (i : ℕ) = ρ.vars sc := by omega
            rw [hieq, getD_set_self (by omega)]
            have : i = (⟨ρ.vars sc, hltm⟩ : Fin mb) := Fin.ext hieq
            rw [this, hpad]
      · have hcond : (Cond.eq (.get bb (.var av)) (.lit 1)).evalB B ρ
            = some false := by
          have h := evalB_condEq hgetE (evalB_lit (σ := ρ) hB1)
          rw [if_neg haX] at h
          simpa using h
        refine ⟨ρ, (Run.ite_false hcond Run.skip).mono (by simp), ?_, rfl, hcnρ,
          rfl, hbiρ, hslots⟩
        rw [hscρ]
        exact (belowCnt_succ_of_not_mem X haX).symm
    obtain ⟨ρ₁, hrun₁, hsc₁, hav₁, hcn₁, hbb₁, hbi₁, hslots₁⟩ := hstep
    have hrun₂ : Run B (.assign av (.add (.var av) (.lit 1))) ρ₁
        (ρ₁.setVar av (t + 1)) 4 := by
      have hb : (Expr.bin .add (.var av) (.lit 1)).evalB B ρ₁
          = some (t + 1) := by
        have h := evalB_bin (op := .add)
          (evalB_var (x := av) (σ := ρ₁) (by rw [hav₁]; omega))
          (evalB_lit (σ := ρ₁) hB1)
          (show ρ₁.vars av + 1 < B by rw [hav₁]; omega)
        rw [hav₁] at h
        exact h
      simpa using Run.assign (x := av) hb
    refine ⟨_, (hrun₁.seq hrun₂).mono (by omega),
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hav_cn)]; exact hcn₁
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_neg (Ne.symm hav_sc), vars_setVar, if_pos rfl]
      exact hsc₁
    · rw [arrs_setVar, hbb₁]; exact hbbρ
    · rw [arrs_setVar]; exact hbi₁
    · intro c
      rw [arrs_setVar, hbb₁]
      exact hbitsρ c
    · intro i hi
      rw [vars_setVar, if_neg (Ne.symm hav_sc)] at hi
      rw [arrs_setVar]
      exact hslots₁ i hi
    · rw [vars_setVar, if_pos rfl]
  have hloop := Spec.forRangeZero (B := B) av cn K cN 16 hNB
    (fun _ hρ => hρ.2.1) (fun _ hρ => hρ.1) hbody
  -- the counter's initialisation
  have hrun0 : Run B (.assign sc (.lit 0)) σ (σ.setVar sc 0) 2 := by
    simpa using Run.assign (x := sc) (evalB_lit (σ := σ) (show 0 < B by omega))
  have hKinit : K ((σ.setVar sc 0).setVar av 0) := by
    have h1 : ((σ.setVar sc 0).setVar av 0).vars sc = 0 := by
      rw [vars_setVar, if_neg (Ne.symm hav_sc), vars_setVar, if_pos rfl]
    have h2 : ((σ.setVar sc 0).setVar av 0).vars av = 0 := by
      rw [vars_setVar, if_pos rfl]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hav_cn), vars_setVar,
        if_neg (Ne.symm hsc_cn)]
      exact hcn
    · rw [h2]; omega
    · rw [h1, h2, belowCnt_zero]
    · rw [arrs_setVar, arrs_setVar]; exact hbbL
    · rw [arrs_setVar, arrs_setVar]; exact hbiL
    · intro c
      rw [arrs_setVar, arrs_setVar]
      exact hbits c
    · intro i hi
      rw [h1] at hi
      omega
  obtain ⟨σ', hrunL, hKfin, hfin⟩ := hloop.run hKinit
  obtain ⟨-, -, hscfin, -, hbifin, -, hslotsfin⟩ := hKfin
  have hscX : σ'.vars sc = X.ncard := by
    rw [hscfin, hfin, belowCnt_carrier]
  refine ⟨σ', (hrun0.seq hrunL).mono (by omega), hscX, hbifin, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hslotsfin i (by rw [hscX]; exact hi)
  · intro y h1 h2
    refine (hrun0.seq hrunL).frame_var y ?_
    simp only [Com.wvars, List.nil_append, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    tauto
  · intro b hb
    refine (hrun0.seq hrunL).frame_arr b ?_
    simp only [Com.warrs, List.nil_append, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · exact run_arrs_length_eq (hrun0.seq hrunL)

open Classical in
/-- **The pad loop, specified**: every remaining slot of the index
region takes the connector — `pad_eq_of_le_ncard`, the half the scan's
own step does not cover. Together the two pin all `mb` slots. -/
theorem padSlotsCom_spec {cN mb : ℕ} {X : Set (Fin cN)} {x₀ : Fin cN}
    {bi cc sc mw : String} (hmbB : mb < B) (hNB : cN < B)
    (hsc_cc : sc ≠ cc) (hsc_mw : sc ≠ mw) :
    Spec B
      (fun σ => σ.vars mw = mb ∧ σ.vars cc = (x₀ : ℕ) ∧
        σ.vars sc = X.ncard ∧ X.ncard ≤ mb ∧ (σ.arrs bi).length = mb ∧
        ∀ i : Fin mb, (i : ℕ) < X.ncard →
          (σ.arrs bi).getD (i : ℕ) 0 = ((pad X x₀ i : Fin cN) : ℕ))
      (padSlotsCom bi cc sc mw)
      (fun σ σ' =>
        (∀ i : Fin mb, (σ'.arrs bi).getD (i : ℕ) 0
          = ((pad X x₀ i : Fin cN) : ℕ)) ∧
        (σ'.arrs bi).length = mb ∧
        (∀ y, y ≠ sc → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ bi → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (11 * mb + 4) := by
  intro σ hσ
  obtain ⟨hmw, hcc, hsc, hXmb, hbiL, hslots⟩ := hσ
  have hB1 : 1 < B := by omega
  set M : Env → Prop := fun ρ =>
    ρ.vars mw = mb ∧ ρ.vars cc = (x₀ : ℕ) ∧ ρ.vars sc ≤ mb ∧
      X.ncard ≤ ρ.vars sc ∧ (ρ.arrs bi).length = mb ∧
      ∀ i : Fin mb, (i : ℕ) < ρ.vars sc →
        (ρ.arrs bi).getD (i : ℕ) 0 = ((pad X x₀ i : Fin cN) : ℕ) with hM_def
  have hbody : Spec B (fun ρ => M ρ ∧ ρ.vars sc < mb)
      (.seq (.store bi (.var sc) (.var cc))
        (.assign sc (.add (.var sc) (.lit 1))))
      (fun ρ ρ' => M ρ' ∧ ρ'.vars sc = ρ.vars sc + 1) 7 := by
    rintro ρ ⟨⟨hmwρ, hccρ, hleρ, hgeρ, hbiρ, hslotsρ⟩, hltρ⟩
    set s : ℕ := ρ.vars sc with hs_def
    have hpad : (pad X x₀ (⟨s, hltρ⟩ : Fin mb) : Fin cN) = x₀ :=
      pad_eq_of_le_ncard _ (by omega)
    have hrunS : Run B (.store bi (.var sc) (.var cc)) ρ
        (ρ.setArr bi s ((x₀ : ℕ))) 3 := by
      have hidx : (Expr.var sc).evalB B ρ = some s :=
        evalB_var (show ρ.vars sc < B by omega)
      have hval : (Expr.var cc).evalB B ρ = some ((x₀ : ℕ)) := by
        have h := evalB_var (B := B) (x := cc) (σ := ρ)
          (show ρ.vars cc < B by rw [hccρ]; have := x₀.2; omega)
        rw [hccρ] at h
        exact h
      simpa using
        Run.store (a := bi) hidx hval (show s < (ρ.arrs bi).length by omega)
    have hrunB : Run B (.assign sc (.add (.var sc) (.lit 1)))
        (ρ.setArr bi s ((x₀ : ℕ)))
        ((ρ.setArr bi s ((x₀ : ℕ))).setVar sc (s + 1)) 4 := by
      have hb : (Expr.bin .add (.var sc) (.lit 1)).evalB B
          (ρ.setArr bi s ((x₀ : ℕ))) = some (s + 1) := by
        refine evalB_bin (evalB_var ?_) (evalB_lit hB1) ?_
        · rw [vars_setArr]; omega
        · show (ρ.setArr bi s ((x₀ : ℕ))).vars sc + 1 < B
          rw [vars_setArr]; omega
      simpa using Run.assign (x := sc) hb
    refine ⟨_, (hrunS.seq hrunB).mono (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hsc_mw), vars_setArr]; exact hmwρ
    · rw [vars_setVar, if_neg (Ne.symm hsc_cc), vars_setArr]; exact hccρ
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, List.length_set]; exact hbiρ
    · intro i hi
      rw [vars_setVar, if_pos rfl] at hi
      rw [arrs_setVar, arrs_setArr, if_pos rfl]
      rcases Nat.lt_or_ge (i : ℕ) s with h' | h'
      · rw [getD_set_of_ne (by omega)]
        exact hslotsρ i h'
      · have hieq : (i : ℕ) = s := by omega
        rw [hieq, getD_set_self (by omega)]
        have hii : i = (⟨s, hltρ⟩ : Fin mb) := Fin.ext hieq
        rw [hii, hpad]
    · rw [vars_setVar, if_pos rfl]
  have hloop := Spec.forRange (B := B) sc mw M mb 7 (11 * mb + 4)
    (fun _ hρ => by have := hρ.2.2.1; omega)
    (fun _ hρ => by have := hρ.1; omega)
    (fun _ hρ => hρ.1) (fun _ hρ => hρ.2.2.1) hbody (fun _ h => h)
    (fun _ _ => by omega)
  have hMinit : M σ := ⟨hmw, hcc, by omega, by omega, hbiL, by
    intro i hi; exact hslots i (by omega)⟩
  obtain ⟨σ', hrun, hMfin, hfin⟩ := hloop.run hMinit
  obtain ⟨-, -, -, -, hbifin, hslotsfin⟩ := hMfin
  refine ⟨σ', hrun, ?_, hbifin, ?_, ?_, ?_⟩
  · intro i
    exact hslotsfin i (by rw [hfin]; exact i.2)
  · intro y hy
    refine hrun.frame_var y ?_
    simp only [padSlotsCom, Com.wvars, List.nil_append, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    tauto
  · intro b hb
    refine hrun.frame_arr b ?_
    simp only [padSlotsCom, Com.warrs, List.nil_append, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    tauto
  · exact run_arrs_length_eq hrun

/-! ## §5 The builder, composed -/

open Classical in
/-- **The batch builder, specified.** From the channel region, the four
figure cells and two scratch allocations, `mkBatchCom` leaves

* the **bit region** holding `X` — `isolateCom_specW`'s `FinBitsW`
  verbatim, and (§6) `X` is `Set.range batchFn`, so **one** bit vector
  serves the isolation as well as the scan;
* the **index region** at length exactly `mb`, holding `pad X x₀` —
  `profilesCom_specW`'s two batch clauses verbatim;

six scalars and two arrays written, no reallocation.

The set is given by the hypothesis `hX`, which is exactly §5 line 19 as
`mem_batchSet_iff_chanRow_level` states it: the connector, plus every
name the channel stores in the connector's row at a round column.

Budget `mkBatchK`, absorbed by `prepStageK` (`mkBatchK_le_prepStageK`). -/
theorem mkBatchCom_spec {cN ℓp hb rounds mb : ℕ}
    {hist : Fin cN → Fin ℓp → List (Fin cN)} {x₀ : Fin cN} {X : Set (Fin cN)}
    {ha bb bi cc cn jr mw ec ic ln bs av sc : String}
    (hNB : cN < B) (hmbB : mb < B) (hRB : cN * ℓp * (hb + 1) < B)
    (hround : rounds ≤ ℓp) (hXmb : X.ncard ≤ mb)
    (hX : ∀ a : Fin cN, a ∈ X ↔
      (a = x₀ ∨ ∃ e : Fin ℓp, (e : ℕ) < rounds ∧ a ∈ hist x₀ e))
    (hha_bb : ha ≠ bb) (hbb_bi : bb ≠ bi)
    (hav_cn : av ≠ cn) (hav_cc : av ≠ cc) (hav_jr : av ≠ jr) (hav_mw : av ≠ mw)
    (hav_sc : av ≠ sc)
    (hsc_cn : sc ≠ cn) (hsc_cc : sc ≠ cc) (hsc_mw : sc ≠ mw)
    (hec_cn : ec ≠ cn) (hec_cc : ec ≠ cc) (hec_jr : ec ≠ jr) (hec_mw : ec ≠ mw)
    (hic_cn : ic ≠ cn) (hic_cc : ic ≠ cc) (hic_jr : ic ≠ jr) (hic_mw : ic ≠ mw)
    (hln_cn : ln ≠ cn) (hln_cc : ln ≠ cc) (hln_jr : ln ≠ jr) (hln_mw : ln ≠ mw)
    (hbs_cn : bs ≠ cn) (hbs_cc : bs ≠ cc) (hbs_jr : bs ≠ jr) (hbs_mw : bs ≠ mw)
    (hic_ln : ic ≠ ln) (hic_bs : ic ≠ bs) (hic_ec : ic ≠ ec)
    (hln_ec : ln ≠ ec) (hbs_ec : bs ≠ ec) (hbs_ln : bs ≠ ln) :
    Spec B
      (fun σ => HistArrW ha ℓp hb hist σ ∧
        σ.vars cn = cN ∧ σ.vars cc = (x₀ : ℕ) ∧ σ.vars jr = rounds ∧
        σ.vars mw = mb ∧
        cN ≤ (σ.arrs bb).length ∧ (σ.arrs bi).length = mb)
      (mkBatchCom ha bb bi cc cn jr mw ec ic ln bs av sc ℓp hb)
      (fun σ σ' => FinBitsW bb X σ' ∧ (σ'.arrs bi).length = mb ∧
        (∀ i : Fin mb, (σ'.arrs bi).getD (i : ℕ) 0
          = ((pad X x₀ i : Fin cN) : ℕ)) ∧
        (∀ y, y ≠ av → y ≠ sc → y ≠ ec → y ≠ ic → y ≠ ln → y ≠ bs →
          σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ bb → b ≠ bi → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (mkBatchK cN ℓp hb mb) := by
  intro σ hσ
  obtain ⟨hha, hcn, hcc, hjr, hmw, hbbL, hbiL⟩ := hσ
  have hx₀ : (x₀ : ℕ) < cN := x₀.2
  have hB1 : 1 < B := by omega
  -- phase 1: the wipe
  obtain ⟨σ1, hrun1, hzero, hfv1, hfa1, hlen1⟩ :=
    (wipeBitsCom_spec (B := B) (cN := cN) (bb := bb) (cn := cn) (av := av)
      hNB hav_cn) σ ⟨hcn, hbbL⟩
  have hbbL1 : cN ≤ (σ1.arrs bb).length := by rw [hlen1 bb]; exact hbbL
  -- phase 2: the connector's own mark
  have hcc1 : σ1.vars cc = (x₀ : ℕ) := by
    rw [hfv1 cc (Ne.symm hav_cc)]; exact hcc
  have hrun2 : Run B (.store bb (.var cc) (.lit 1)) σ1
      (σ1.setArr bb ((x₀ : ℕ)) 1) 3 := by
    have hidx : (Expr.var cc).evalB B σ1 = some ((x₀ : ℕ)) := by
      have h := evalB_var (B := B) (x := cc) (σ := σ1)
        (show σ1.vars cc < B by rw [hcc1]; omega)
      rw [hcc1] at h
      exact h
    simpa using Run.store (a := bb) hidx (evalB_lit (σ := σ1) hB1)
      (show (x₀ : ℕ) < (σ1.arrs bb).length by omega)
  set σ2 : Env := σ1.setArr bb ((x₀ : ℕ)) 1 with hσ2_def
  obtain ⟨Base, hBase⟩ : ∃ S : Set (Fin cN), ∀ a : Fin cN, a ∈ S ↔ a = x₀ :=
    ⟨{b : Fin cN | b = x₀}, fun _ => Iff.rfl⟩
  have hbits2 : ∀ a : Fin cN, (σ2.arrs bb).getD (a : ℕ) 0
      = if a ∈ Base then 1 else 0 := by
    intro a
    rw [hσ2_def, arrs_setArr, if_pos rfl]
    by_cases hax : a = x₀
    · rw [hax, getD_set_self (by omega), if_pos ((hBase x₀).mpr rfl)]
    · rw [getD_set_of_ne (fun h => hax (Fin.ext h.symm)),
        if_neg (fun h => hax ((hBase a).mp h))]
      exact hzero a
  have hlen2 : ∀ b, (σ2.arrs b).length = (σ1.arrs b).length := by
    intro b
    rw [hσ2_def, arrs_setArr]
    by_cases h : b = bb
    · rw [if_pos h, h, List.length_set]
    · rw [if_neg h]
  have hfa2 : ∀ b, b ≠ bb → σ2.arrs b = σ1.arrs b := by
    intro b hb
    rw [hσ2_def, arrs_setArr, if_neg hb]
  have hfv2 : ∀ y, σ2.vars y = σ1.vars y := fun y => by rw [hσ2_def, vars_setArr]
  -- phase 3: the channel-row marking scan
  have hha2 : HistArrW ha ℓp hb hist σ2 :=
    histArrW_of_eq hha (by rw [hfa2 ha hha_bb, hfa1 ha hha_bb])
  obtain ⟨σ3, hrun3, hbits3, hfv3, hfa3, hlen3⟩ :=
    (markRowCom_spec (B := B) (hist := hist) (x₀ := x₀)
      (Base := Base) (ha := ha) (bb := bb) (cc := cc)
      (jr := jr) (ec := ec) (ic := ic) (ln := ln) (bs := bs)
      hround hNB hRB hha_bb hec_jr hec_cc hic_jr hic_cc hic_ln hic_bs hic_ec
      hln_jr hln_cc hln_ec hbs_jr hbs_cc hbs_ec hbs_ln) σ2
      ⟨hha2, by rw [hfv2 cc]; exact hcc1,
        by rw [hfv2 jr, hfv1 jr (Ne.symm hav_jr)]; exact hjr,
        by rw [hlen2 bb]; exact hbbL1, hbits2⟩
  -- the marks are exactly `X`
  have hbitsX : ∀ a : Fin cN, (σ3.arrs bb).getD (a : ℕ) 0
      = if a ∈ X then 1 else 0 := by
    intro a
    rw [hbits3 a]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro (h | h)
      · exact (hX a).mpr (Or.inl ((hBase a).mp h))
      · exact (hX a).mpr (Or.inr h)
    · intro h
      rcases (hX a).mp h with h' | h'
      · exact Or.inl ((hBase a).mpr h')
      · exact Or.inr h'
  -- phase 4: the carrier scan
  obtain ⟨σ4, hrun4, hsc4, hbiL4, hslots4, hfv4, hfa4, hlen4⟩ :=
    (emitSlotsCom_spec (B := B) (X := X) (x₀ := x₀) (bb := bb) (bi := bi)
      (cn := cn) (av := av) (sc := sc) hNB hmbB hXmb hbb_bi hav_cn hav_sc
      hsc_cn) σ3
      ⟨by rw [hfv3 cn (Ne.symm hec_cn) (Ne.symm hic_cn) (Ne.symm hln_cn)
            (Ne.symm hbs_cn), hfv2 cn, hfv1 cn (Ne.symm hav_cn)]
          exact hcn,
        by rw [hlen3 bb, hlen2 bb]; exact hbbL1,
        by rw [hlen3 bi, hlen2 bi, hlen1 bi]; exact hbiL, hbitsX⟩
  -- phase 5: the pad
  have hcc4 : σ4.vars cc = (x₀ : ℕ) := by
    rw [hfv4 cc (Ne.symm hav_cc) (Ne.symm hsc_cc),
      hfv3 cc (Ne.symm hec_cc) (Ne.symm hic_cc) (Ne.symm hln_cc)
        (Ne.symm hbs_cc), hfv2 cc]
    exact hcc1
  have hmw4 : σ4.vars mw = mb := by
    rw [hfv4 mw (Ne.symm hav_mw) (Ne.symm hsc_mw),
      hfv3 mw (Ne.symm hec_mw) (Ne.symm hic_mw) (Ne.symm hln_mw)
        (Ne.symm hbs_mw), hfv2 mw, hfv1 mw (Ne.symm hav_mw)]
    exact hmw
  obtain ⟨σ5, hrun5, hslots5, hbiL5, hfv5, hfa5, hlen5⟩ :=
    (padSlotsCom_spec (B := B) (X := X) (x₀ := x₀) (bi := bi) (cc := cc)
      (sc := sc) (mw := mw) hmbB hNB hsc_cc hsc_mw) σ4
      ⟨hmw4, hcc4, hsc4, hXmb, hbiL4, hslots4⟩
  -- assemble
  refine ⟨σ5, ((hrun1.seq (hrun2.seq (hrun3.seq (hrun4.seq hrun5)))).mono
    (by unfold mkBatchK; omega)), ⟨?_, ?_⟩, hbiL5, hslots5, ?_, ?_, ?_⟩
  · rw [hlen5 bb, hlen4 bb, hlen3 bb, hlen2 bb]; exact hbbL1
  · intro a
    rw [hfa5 bb hbb_bi, hfa4 bb hbb_bi]
    exact hbitsX a
  · intro y h1 h2 h3 h4 h5 h6
    rw [hfv5 y h2, hfv4 y h1 h2, hfv3 y h3 h4 h5 h6, hfv2 y, hfv1 y h1]
  · intro b hb1 hb2
    rw [hfa5 b hb2, hfa4 b hb2, hfa3 b hb1, hfa2 b hb1, hfa1 b hb1]
  · intro b
    rw [hlen5 b, hlen4 b, hlen3 b, hlen2 b, hlen1 b]

/-! ### The builder's write set, in closed form

`mkBatchCom_spec` above carries the frame in its postcondition, which
threads through a chain but cannot be read off a composite command.
These give the write set itself, in the shapes `Spec.frameA` and
`Spec.frameV` consume — the shape `warrs_restrictCom` and
`warrs_colWriteCom` already take for the other stages. -/

/-- **The builder's array surface**: the bit region and the index
region. The channel region `ha` is read, never written — which is why
the builder may run before the supports pass patches a column of it. -/
theorem warrs_mkBatchCom (ha bb bi cc cn jr mw ec ic ln bs av sc : String)
    (ℓp hb : ℕ) :
    (mkBatchCom ha bb bi cc cn jr mw ec ic ln bs av sc ℓp hb).warrs
      = [bb, bb, bb, bi, bi] := rfl

/-- The membership side condition `Spec.frameA` is consumed with. -/
theorem mkBatchCom_notMem_warrs {ha bb bi cc cn jr mw ec ic ln bs av sc
    b : String} {ℓp hb : ℕ} (h1 : b ≠ bb) (h2 : b ≠ bi) :
    b ∉ (mkBatchCom ha bb bi cc cn jr mw ec ic ln bs av sc ℓp hb).warrs := by
  rw [warrs_mkBatchCom]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1, h1, h1, h2, h2⟩

/-- **The builder's scalar surface**: its own six scratch cells. The
connector `cc`, the carrier cell `cn`, the round count `jr` and the
width `mw` are read, never written. -/
theorem wvars_mkBatchCom (ha bb bi cc cn jr mw ec ic ln bs av sc : String)
    (ℓp hb : ℕ) :
    (mkBatchCom ha bb bi cc cn jr mw ec ic ln bs av sc ℓp hb).wvars
      = [av, av, ec, bs, ln, ic, ic, ec, sc, av, sc, av, sc] := rfl

/-- The membership side condition `Spec.frameV` is consumed with. -/
theorem mkBatchCom_notMem_wvars {ha bb bi cc cn jr mw ec ic ln bs av sc
    y : String} {ℓp hb : ℕ} (h1 : y ≠ av) (h2 : y ≠ ec) (h3 : y ≠ bs)
    (h4 : y ≠ ln) (h5 : y ≠ ic) (h6 : y ≠ sc) :
    y ∉ (mkBatchCom ha bb bi cc cn jr mw ec ic ln bs av sc ℓp hb).wvars := by
  rw [wvars_mkBatchCom]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1, h1, h2, h3, h4, h5, h5, h2, h6, h1, h6, h1, h6⟩

end Phases


/-! ## §6 The builder at the driver's own objects

`restrictCom_specW` leaves the child's regions at
`(Impl.ofArena A (htabF j A)).restrict (cluster S A π u)` — whose
channel is the row §5 line 19 reads. Instantiating §5 there turns the
generic statement into the two things the next two stages ask for, and
turns the scan's own `batchSet` into `isolateCom_specW`'s
`Set.range batchFn` (`range_batchFn_eq_batchSet`: **one** bit vector). -/

section Driver

variable {L n₀ : ℕ}

open Classical in
/-- **The child's channel region**, as `restrictCom_specW` leaves it:
the parent's table filtered onto the cluster and renumbered. The
carrier equation `(restrict …).N = childN` is definitional
(`Impl.restrict_N_eq_childN`). -/
noncomputable def childHistTab (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {ℓpj : ℕ}
    (htab : Fin A.N → Fin ℓpj → List (Fin A.N)) :
    Fin (childN S A π u) → Fin ℓpj → List (Fin (childN S A π u)) :=
  ((Impl.ofArena A htab).restrict (cluster S A π u)).hist

open Classical in
/-- **The batch builder at the campaign's objects.** Under the pins and
the width pin, `mkBatchCom` run on the restricted child's regions
leaves

* `FinBitsW bb (Set.range (batchFn S A π u))` — *verbatim*
  `isolateCom_specW`'s bit-region precondition, and the same bit vector
  the scan itself computed (`range_batchFn_eq_batchSet`);
* `BatchWidthScr bi S.width` and `bi[i] = batchFn S A π u i` for every
  slot — *verbatim* `profilesCom_specW`'s two batch preconditions, the
  length as an **equality**, the pad included.

Hazard 1 is honoured by construction: the channel row read is
`restrict`'s — the **pre-isolation** child `B₀`'s — so nothing here
moves the batch past `restrict`. -/
theorem mkBatchCom_batch {B : ℕ} (S : Setup L) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (hp : PrepPins S ℓp htabF hbf Adm) (hw : WidthPin S)
    (j : ℕ) (A : Arena (S.pal j) n₀) (hj : j < S.depth) (hAdm : Adm j A)
    (hrow : ∀ (v : Fin A.N) (e : ℕ), (A.chan v e).length ≤ 2 * S.R + 1)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {ha bb bi cc cn jr mw ec ic ln bs av sc : String}
    (hNB : childN S A π u < B) (hmbB : S.width < B)
    (hRB : childN S A π u * ℓp j * (hbf j + 1) < B)
    (hha_bb : ha ≠ bb) (hbb_bi : bb ≠ bi)
    (hav_cn : av ≠ cn) (hav_cc : av ≠ cc) (hav_jr : av ≠ jr) (hav_mw : av ≠ mw)
    (hav_sc : av ≠ sc)
    (hsc_cn : sc ≠ cn) (hsc_cc : sc ≠ cc) (hsc_mw : sc ≠ mw)
    (hec_cn : ec ≠ cn) (hec_cc : ec ≠ cc) (hec_jr : ec ≠ jr) (hec_mw : ec ≠ mw)
    (hic_cn : ic ≠ cn) (hic_cc : ic ≠ cc) (hic_jr : ic ≠ jr) (hic_mw : ic ≠ mw)
    (hln_cn : ln ≠ cn) (hln_cc : ln ≠ cc) (hln_jr : ln ≠ jr) (hln_mw : ln ≠ mw)
    (hbs_cn : bs ≠ cn) (hbs_cc : bs ≠ cc) (hbs_jr : bs ≠ jr) (hbs_mw : bs ≠ mw)
    (hic_ln : ic ≠ ln) (hic_bs : ic ≠ bs) (hic_ec : ic ≠ ec)
    (hln_ec : ln ≠ ec) (hbs_ec : bs ≠ ec) (hbs_ln : bs ≠ ln) :
    Spec B
      (fun σ =>
        HistArrW ha (ℓp j) (hbf j) (childHistTab S A π u (htabF j A)) σ ∧
        σ.vars cn = childN S A π u ∧
        σ.vars cc = ((centreChild S A π u : Fin (childN S A π u)) : ℕ) ∧
        σ.vars jr = j ∧ σ.vars mw = S.width ∧
        childN S A π u ≤ (σ.arrs bb).length ∧
        BatchWidthScr bi S.width σ)
      (mkBatchCom ha bb bi cc cn jr mw ec ic ln bs av sc (ℓp j) (hbf j))
      (fun σ σ' => FinBitsW bb (Set.range (batchFn S A π u)) σ' ∧
        BatchWidthScr bi S.width σ' ∧
        (∀ i : Fin S.width, (σ'.arrs bi).getD (i : ℕ) 0
          = ((batchFn S A π u i : Fin (childN S A π u)) : ℕ)) ∧
        (∀ y, y ≠ av → y ≠ sc → y ≠ ec → y ≠ ic → y ≠ ln → y ≠ bs →
          σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ bb → b ≠ bi → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (mkBatchK (childN S A π u) (ℓp j) (hbf j) S.width) := by
  have hAdmR : A.hist.length = j ∧
      ∀ (v : Fin A.N) (e : ℕ), (A.chan v e).length ≤ 2 * S.R + 1 :=
    ⟨hp.round j A hAdm, hrow⟩
  have hround : j ≤ ℓp j := by
    have h := hp.fit j A (le_of_lt hj) hAdm
    rw [hAdmR.1] at h
    exact h
  have hXmb : (batchSet S A π u).ncard ≤ S.width :=
    batchSet_ncard_le_width S A π u hw hAdmR hj
  have hrange : Set.range (batchFn S A π u) = batchSet S A π u :=
    range_batchFn_eq_batchSet S A π u hw hAdmR hj
  have hX : ∀ a : Fin (childN S A π u), a ∈ batchSet S A π u ↔
      (a = centreChild S A π u ∨ ∃ e : Fin (ℓp j), (e : ℕ) < j ∧
        a ∈ childHistTab S A π u (htabF j A) (centreChild S A π u) e) :=
    fun a => mem_batchSet_iff_chanRow_level S ℓp htabF hbf Adm hp j A
      (le_of_lt hj) hAdm π u a
  refine ((mkBatchCom_spec (B := B) (cN := childN S A π u) (ℓp := ℓp j)
    (hb := hbf j) (rounds := j) (mb := S.width)
    (hist := childHistTab S A π u (htabF j A))
    (x₀ := centreChild S A π u) (X := batchSet S A π u)
    (ha := ha) (bb := bb) (bi := bi) (cc := cc) (cn := cn) (jr := jr)
    (mw := mw) (ec := ec) (ic := ic) (ln := ln) (bs := bs) (av := av)
    (sc := sc)
    hNB hmbB hRB hround hXmb hX hha_bb hbb_bi hav_cn hav_cc hav_jr hav_mw
    hav_sc hsc_cn hsc_cc hsc_mw hec_cn hec_cc hec_jr hec_mw hic_cn hic_cc
    hic_jr hic_mw hln_cn hln_cc hln_jr hln_mw hbs_cn hbs_cc hbs_jr hbs_mw
    hic_ln hic_bs hic_ec hln_ec hbs_ec hbs_ln).post ?_)
  rintro σ σ' - ⟨hbits, hbiL, hslots, hfv, hfa, hlen⟩
  exact ⟨by rw [hrange]; exact hbits, hbiL, hslots, hfv, hfa, hlen⟩

/-- The child's carrier is never empty — the connector is in it. This
is the `1 ≤ cN` the budget comparison rides. -/
theorem childN_pos (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : 0 < childN S A π u :=
  lt_of_le_of_lt (Nat.zero_le _) (centreChild S A π u).2

/-- **The budget at the driver's own dimensions**: the cluster's size
*is* the child's carrier, so `restrictK`'s per-member charge and the
builder's per-member cost are charged against the same `k`. Nothing new
enters `prepStageK`. -/
theorem mkBatchK_child_le_prepStageK (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (cns dS Λc ℓpj hbj R : ℕ) :
    mkBatchK (childN S A π u) ℓpj hbj S.width
      ≤ prepStageK (childN S A π u) cns dS (childN S A π u) Λc ℓpj hbj
          S.width R :=
  mkBatchK_le_prepStageK _ _ _ _ _ _ _ _ (childN_pos S A π u)

end Driver


/-! ## §7 The isolation palette, as the machine addresses it

Item 2 — the colour-region writer — is **not** written here. What is
written here is the one arithmetic fact it is blocked on and that
nothing landed states: where each of `isoPal`'s three slot families
lives as a *number*, since `ColBits` addresses the colour region
row-major at `v · Λ + c` and a program can only emit numerals.

All three are `rfl`: `isoEnc` is built from `finProdFinEquiv` and
`finSumFinEquiv`, whose values are definitional. -/

section Palette

variable {Λ mb cap : ℕ}

/-- An old colour keeps its own slot number. -/
theorem isoOld_val (c : Fin Λ) :
    ((Driver.isoOld (mb := mb) (cap := cap) c : Fin (Driver.isoPal Λ mb cap)) : ℕ)
      = (c : ℕ) := rfl

/-- The batch-distance slot `(j, a)`: past the old colours, then
`(cap+1)` slots per batch member, radius fastest. -/
theorem isoPd_val (j : Fin mb) (a : Fin (cap + 1)) :
    ((Driver.isoPd (Λ := Λ) j a : Fin (Driver.isoPal Λ mb cap)) : ℕ)
      = Λ + ((a : ℕ) + (cap + 1) * (j : ℕ)) := rfl

/-- The colour-distance slot `(c, b)`: past the old colours and the
whole batch block, then `(cap+1)` slots per class. -/
theorem isoPu_val (c : Fin Λ) (b : Fin (cap + 1)) :
    ((Driver.isoPu (mb := mb) c b : Fin (Driver.isoPal Λ mb cap)) : ℕ)
      = Λ + (mb * (cap + 1) + ((b : ℕ) + (cap + 1) * (c : ℕ))) := rfl

/-- **Every slot is exactly one of the three** — the case split a
`ColBits` proof over `recordProfilesMS` runs, and the reason the writer
is three loops and not one. -/
theorem isoPal_cases (c' : Fin (Driver.isoPal Λ mb cap)) :
    (∃ c : Fin Λ, c' = Driver.isoOld c) ∨
      (∃ (j : Fin mb) (a : Fin (cap + 1)), c' = Driver.isoPd j a) ∨
      ∃ (c : Fin Λ) (b : Fin (cap + 1)), c' = Driver.isoPu c b := by
  have hc' : Driver.isoEnc Λ mb cap ((Driver.isoEnc Λ mb cap).symm c') = c' :=
    Equiv.apply_symm_apply _ _
  rcases hs : (Driver.isoEnc Λ mb cap).symm c' with c | (p | p)
  · exact Or.inl ⟨c, by rw [← hc', hs]; rfl⟩
  · exact Or.inr (Or.inl ⟨p.1, p.2, by rw [← hc', hs]; rfl⟩)
  · exact Or.inr (Or.inr ⟨p.1, p.2, by rw [← hc', hs]; rfl⟩)

end Palette

end Lax3Proofs.Prog
