import Lax3Proofs.SolveSweepSelPeel

/-!
# F6c13c — the static-adjacency peel: the sorted region, the bucket
replay, and the selection they name

Wave 24 (`SolveSweepBucket`) argued — in its module docstring, in
prose, not as a theorem — that the min-degree peel at the *original*
tie-break, `minDegVert`'s least index, is `Θ(N²)` for each of the three
constant-time bucket disciplines it examined. Wave 25
(`SolveSweepSelPeel`) re-pinned the tie-break, which is free
(`selOrderingRoutine_data` gives the six-clause `AugChainData` at *any*
attaining selection), proved the amortization the linear design needs
(`staticPot`, `staticPot_erase`, `peelLoop_linear_static_cursor`), and
recorded why the obvious linear program still does not close:

* a bucket pop is a function of the machine's *history*, so the
  abstract selection has to be defined by replaying the run;
* the history includes the adjacency rows, and `DelAdjSt`
  (`SolveSweepAdj.lean:153`) **carries no order clause** — no clause of
  it mentions the order of a row's slots, only that each live prefix
  lists the current neighbours, so the rows the peel receives are not a
  function of the graph;
* one counting sort at entry repairs that at the entry *only*, because
  wave 23's `delAdjCom` is a **swap-delete**: `adjCore_unlink`
  overwrites the unlinked slot with the row's last live entry, and
  `AdjDeleteInW`'s postcondition is again just a `DelAdjSt`, which does
  not say which permutation of the row survives.

**The design this leaf builds is the one that survives all three: a
peel that never writes to the adjacency arrays.** Then one counting
sort at entry makes the rows a function of `G` for the whole run, and
the replay has only the buckets to model. The price is that a round
walks `v`'s *original* row rather than a compacted one — exactly the
charge `livePot` cannot carry and `staticPot` can, at the same linear
total since both start at `slotCount F`. `delAdjCom` is therefore not
used anywhere below: its row scrambling is the entire reason for this
design.

## What is here

* **§1 the sorted region.** `SortedAdjSt` — `DelAdjSt` at the empty
  deletion set *plus* the order clause — and `sortedAdjSt_row_eq`: two
  states satisfying it at the same graph agree on **every live slot**,
  with no relation assumed between their array names or their other
  contents. That is the precise sense in which the entry sort makes the
  rows a function of `G` alone: a row is a strictly increasing
  enumeration of `N_G(v)`, and `Finset.orderEmbOfFin_unique` says there
  is exactly one of those. And the order clause is **not derivable**:
  `delAdjSt_not_row_unique` exhibits two states of the triangle that
  satisfy `DelAdjSt` and disagree on slot `0`, whence
  `not_sortedAdjSt_of_delAdjSt`. That is the campaign's prose finding
  turned into a theorem.

* **§2 the entry sort's contract**, `AdjSortIn`, at a budget linear in
  the carrier and the slot count, with the frame clauses a composed
  pass consumes — and `adjSortIn_det`, that any two programs meeting it
  leave the same rows. The program itself is not written here.

* **§3 the abstract bucket replay, proved.** `BState`, `bInit`,
  `bStep`, `bRun`; the partition invariant `BInv` — bucket `d` holds
  exactly the live vertices of **current** degree `d`, and the cursor
  never stands above the current minimum degree; `bLevel_eq_minDeg`
  (the upward scan stops at the minimum-degree bucket, so its rise is
  `minDeg − cur`); **`bPop_spec`** (the pop is live and attains the
  minimum degree — *attainment, not least index*); `bStep_inv` (a round
  preserves the partition, each live neighbour of the peeled vertex
  moving down exactly one bucket, by `card_nbrsIn_erase`).

* **§4 the selection, and the loop rule at it.** `bucketSel`, a
  `MinDegSel` built through `MinDegSel.ofMin` so its two clauses hold
  unconditionally, with `bucketPick_bRun`: at every reachable state the
  guarded pick *is* the replay's pop. And `peelLoop_linear_bucket` —
  `peelLoop_linear_static_cursor` with every graph-side obligation
  discharged from §3, so a loop whose round advances the replay by one
  and costs `a + b·|N_F(v)| + e·(cursor rise)` runs inside
  `(a+e)·N + b·slotCount F + e·N + O(1)`. The cursor is never reset:
  `bRun_round` derives `cur σ ≤ cur σ' + 1` from
  `minDeg_le_minDeg_erase_succ`. `selRank_bPop` pins the countdown the
  round must store: the vertex popped at round `k` has rank
  `N - k - 1`.

* **§5 what remains, at the right budget.** `linearPeelBudget` and
  `covOrderIn_bucket`: `CovOrderIn` at
  `Kag + (a·A.N + b·slotCount F_aug + cst)` — **linear in the carrier and
  the slot count, with no `A.N * A.N` term** — as soon as
  `CovSelPeelIn` holds at `bucketSel` for the round program. That
  residual is named and **not discharged here**; the quadratic
  discharge already exists (`covSelPeelIn_peelCom_mdSel`) for anyone who
  wants one, and a named residual at the right budget is worth more
  than a proved theorem at the wrong one.

Conventions that are not optional. The countdown is
`selRankAux_peel_step`'s: the round's vertex gets `|S| − 1`, so the
first vertex peeled from `N` live gets `N − 1`; an off-by-one here
produces a different permutation that still typechecks against
`RankArr`. The degrees inside `BState` are **current** degrees, while
the row a round walks is the **original** row — keeping those two apart
is the crux of the design. And `deleteVerts` isolates rather than
removes, so `SortedAdjSt`'s carrier is the whole of `Fin N` and its
rows are indexed by the base degrees.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)
open Lax3Proofs.CoverRoutine (MinDegSel minDegVert minDegVert_mem)

/-! ## §1 The sorted adjacency region

`DelAdjSt` at the empty deletion set is what the augmentation pass
leaves: every vertex live, every row listing its whole neighbourhood in
the augmented graph. What it does not say is in which order — that
clause is missing from the definition, and `sortedAdjSt_row_eq` is what
adding it buys. -/

/-- **The sorted adjacency region**: the deletable region at the empty
deletion set, plus the clause `DelAdjSt` does not carry — each row is
strictly ascending on its live prefix.

The order clause is stated at *every* offset function valid for `G`
rather than at `DelAdjSt`'s own existential witness; by `offF_unique`
the two are the same requirement, and the ∀-form composes without
having to match two existentials. -/
def SortedAdjSt (ao aj dg mt : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (σ : Env) : Prop :=
  DelAdjSt ao aj dg mt G ∅ σ ∧
    ∀ offF : ℕ → ℕ, offF 0 = 0 →
      (∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) →
      ∀ (v : Fin N) (s t : ℕ), s < t → t < (σ.arrs dg).getD (v : ℕ) 0 →
        (σ.arrs aj).getD (offF (v : ℕ) + s) 0 < (σ.arrs aj).getD (offF (v : ℕ) + t) 0

/-- A sorted region is a region. -/
theorem SortedAdjSt.delAdjSt {ao aj dg mt : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {σ : Env} (h : SortedAdjSt ao aj dg mt G σ) :
    DelAdjSt ao aj dg mt G ∅ σ := h.1

/-- At the empty deletion set every row is live and its length is the
vertex's degree in `G`: `deleteVerts` isolates rather than removes, and
isolating nothing is the identity (`deleteVerts_empty`). -/
theorem delAdjSt_empty_dg {ao aj dg mt : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {σ : Env} (h : DelAdjSt ao aj dg mt G ∅ σ)
    (v : Fin N) : (σ.arrs dg).getD (v : ℕ) 0 = (G.neighborSet v).ncard := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hdeg, -, -⟩ := h
  rw [hdeg v (by simp), deleteVerts_empty]

/-- **The sorted region's rows are a function of the graph alone.** Two
states satisfying `SortedAdjSt` at the same `G` — with no relation
assumed between their array names or anything else they hold — agree on
every live slot of every row.

This is what the entry sort buys and what the static-adjacency design
rests on: a row is a strictly increasing enumeration of `N_G(v)`, and
`Finset.orderEmbOfFin_unique` says there is exactly one of those. Since
the peel never writes to `aj`, the rows stay a function of `G` for the
whole run, and the replay of §3 has only the buckets to model. -/
theorem sortedAdjSt_row_eq {ao aj dg mt ao' aj' dg' mt' : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {σ σ' : Env}
    (h : SortedAdjSt ao aj dg mt G σ) (h' : SortedAdjSt ao' aj' dg' mt' G σ')
    {offF : ℕ → ℕ} (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    (v : Fin N) {t : ℕ} (ht : t < (G.neighborSet v).ncard) :
    (σ.arrs aj).getD (offF (v : ℕ) + t) 0
      = (σ'.arrs aj').getD (offF (v : ℕ) + t) 0 := by
  classical
  set s : Finset ℕ := (nbrsIn G Finset.univ v).image Fin.val with hs
  have hcard : s.card = (G.neighborSet v).ncard := by
    rw [hs, Finset.card_image_of_injective _ Fin.val_injective, card_nbrsIn_univ]
  have key : ∀ {ajX dgX : String} {σX : Env} {aoX mtX : String},
      SortedAdjSt aoX ajX dgX mtX G σX →
      (∀ i : Fin ((G.neighborSet v).ncard),
          (σX.arrs ajX).getD (offF (v : ℕ) + (i : ℕ)) 0 ∈ s) ∧
        StrictMono (fun i : Fin ((G.neighborSet v).ncard) =>
          (σX.arrs ajX).getD (offF (v : ℕ) + (i : ℕ)) 0) := by
    intro ajX dgX σX aoX mtX hX
    have hdgX := delAdjSt_empty_dg hX.1 v
    obtain ⟨hdel, hord⟩ := hX
    obtain ⟨offG, hg0, hgstep, -, -, -, -, -, -, -, hsound, -⟩ := hdel
    have hoff : offG (v : ℕ) = offF (v : ℕ) :=
      offF_unique hg0 h0 hgstep hstep (v : ℕ) (le_of_lt v.isLt)
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · have hi : (i : ℕ) < (σX.arrs dgX).getD (v : ℕ) 0 := by rw [hdgX]; exact i.isLt
      obtain ⟨w, hadj, hval, -⟩ := hsound v (by simp) (i : ℕ) hi
      rw [hoff] at hval
      rw [hval, hs]
      refine Finset.mem_image.mpr ⟨w, ?_, rfl⟩
      rw [deleteVerts_empty] at hadj
      exact mem_nbrsIn.mpr ⟨Finset.mem_univ w, hadj.symm⟩
    · exact hord offF h0 hstep v (i : ℕ) (j : ℕ) hij (by rw [hdgX]; exact j.isLt)
  obtain ⟨hmem1, hmono1⟩ := key h
  obtain ⟨hmem2, hmono2⟩ := key h'
  have e1 := Finset.orderEmbOfFin_unique hcard hmem1 hmono1
  have e2 := Finset.orderEmbOfFin_unique hcard hmem2 hmono2
  exact congrFun (e1.trans e2.symm) ⟨t, ht⟩


/-! ### The finding: `DelAdjSt` does not pin a row's order

`SortedAdjSt`'s extra clause is a real strengthening, not bookkeeping.
Two states of the triangle — differing by the transposition of row `0`,
with the two mate pointers that follow it — both satisfy `DelAdjSt` and
disagree on slot `0`. So no consequence of `DelAdjSt` determines a
row's order; the entry sort's postcondition has to be stated
separately; and a peel whose pop depends on the row order is not a
function of the graph until the sort has run. This is wave 25's prose
finding, as a theorem. -/

/-- The witness graph: the triangle. Every degree is `2`, so the
offsets are `2·v` and every row has room for a transposition. -/
abbrev triG : SimpleGraph (Fin 3) := ⊤

theorem triG_ncard (v : Fin 3) : (triG.neighborSet v).ncard = 2 := by
  classical
  have h : triG.neighborSet v = ↑((Finset.univ : Finset (Fin 3)).filter (fun u => v ≠ u)) := by
    ext u
    simp [SimpleGraph.mem_neighborSet]
  rw [h, Set.ncard_coe_finset]
  fin_cases v <;> decide

/-- The witness states: the same offsets and the same degrees, with the
adjacency and mate arrays given explicitly. -/
def triEnv (r m : List ℕ) : Env where
  vars := fun _ => 0
  arrs := fun cn =>
    if cn = "ao" then [0, 2, 4, 6]
    else if cn = "aj" then r
    else if cn = "dg" then [2, 2, 2]
    else if cn = "mt" then m
    else []
  inp := []
  out := []

theorem triEnv_ao (r m : List ℕ) : (triEnv r m).arrs "ao" = [0, 2, 4, 6] := by
  simp [triEnv]

theorem triEnv_aj (r m : List ℕ) : (triEnv r m).arrs "aj" = r := by
  simp [triEnv]

theorem triEnv_dg (r m : List ℕ) : (triEnv r m).arrs "dg" = [2, 2, 2] := by
  simp [triEnv]

theorem triEnv_mt (r m : List ℕ) : (triEnv r m).arrs "mt" = m := by
  simp [triEnv]

theorem triDg (w : Fin 3) : ([2, 2, 2] : List ℕ).getD (w : ℕ) 0 = 2 := by
  fin_cases w <;> rfl

/-- The region at explicit rows: every clause but soundness and
completeness is arithmetic on literals, and those two are the finite
checks the caller supplies. -/
theorem delAdjSt_triEnv (r m : List ℕ) (hr : r.length = 6) (hm : m.length = 6)
    (hsound : ∀ (v : Fin 3) (t : Fin 2), ∃ w : Fin 3, v ≠ w ∧
      r.getD (2 * (v : ℕ) + (t : ℕ)) 0 = (w : ℕ) ∧
      ∃ s : Fin 2, m.getD (2 * (v : ℕ) + (t : ℕ)) 0 = 2 * (w : ℕ) + (s : ℕ) ∧
        r.getD (2 * (w : ℕ) + (s : ℕ)) 0 = (v : ℕ) ∧
        m.getD (2 * (w : ℕ) + (s : ℕ)) 0 = 2 * (v : ℕ) + (t : ℕ))
    (hcomp : ∀ v w : Fin 3, v ≠ w →
      ∃ t : Fin 2, r.getD (2 * (v : ℕ) + (t : ℕ)) 0 = (w : ℕ)) :
    DelAdjSt "ao" "aj" "dg" "mt" triG ∅ (triEnv r m) := by
  refine ⟨fun i => 2 * i, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; rw [triG_ncard]; ring
  · rw [triEnv_ao]; decide
  · intro i hi
    rw [triEnv_ao]
    interval_cases i <;> rfl
  · rw [triEnv_aj, hr]
  · rw [triEnv_mt, hm]
  · rw [triEnv_dg]; decide
  · intro v hv; exact absurd hv (by simp)
  · intro v _
    rw [triEnv_dg, deleteVerts_empty, triG_ncard, triDg]
  · intro v _ t ht
    rw [triEnv_dg, triDg] at ht
    obtain ⟨w, hvw, h1, s, h2, h3, h4⟩ := hsound v ⟨t, ht⟩
    refine ⟨w, ?_, ?_, (s : ℕ), ?_, ?_, ?_, ?_⟩
    · rw [deleteVerts_empty]; exact (SimpleGraph.top_adj _ _).mpr hvw
    · rw [triEnv_aj]; exact h1
    · rw [triEnv_dg, triDg]; exact s.isLt
    · rw [triEnv_mt]; exact h2
    · rw [triEnv_aj]; exact h3
    · rw [triEnv_mt]; exact h4
  · intro v _ w hadj
    rw [deleteVerts_empty] at hadj
    obtain ⟨t, ht⟩ := hcomp v w ((SimpleGraph.top_adj _ _).mp hadj)
    exact ⟨(t : ℕ), by rw [triEnv_dg, triDg]; exact t.isLt, by rw [triEnv_aj]; exact ht⟩

/-- Row `0` as `1, 2`. -/
theorem delAdjSt_tri₁ :
    DelAdjSt "ao" "aj" "dg" "mt" triG ∅ (triEnv [1, 2, 0, 2, 0, 1] [2, 4, 0, 5, 1, 3]) :=
  delAdjSt_triEnv _ _ rfl rfl (by decide) (by decide)

/-- Row `0` as `2, 1` — the same region, transposed, with the two mate
pointers that follow. -/
theorem delAdjSt_tri₂ :
    DelAdjSt "ao" "aj" "dg" "mt" triG ∅ (triEnv [2, 1, 0, 2, 0, 1] [4, 2, 1, 5, 0, 3]) :=
  delAdjSt_triEnv _ _ rfl rfl (by decide) (by decide)

/-- **`DelAdjSt` does not determine a row's order.** Two states of the
same graph satisfy it and disagree on slot `0` — so the rows a peel
receives from `CovAugAdjIn` (whose postcondition is exactly a
`DelAdjSt`) are not a function of the graph, and a pop that reads them
is not either. -/
theorem delAdjSt_not_row_unique :
    ∃ σ σ' : Env,
      DelAdjSt "ao" "aj" "dg" "mt" triG ∅ σ ∧
      DelAdjSt "ao" "aj" "dg" "mt" triG ∅ σ' ∧
      (σ.arrs "aj").getD 0 0 ≠ (σ'.arrs "aj").getD 0 0 :=
  ⟨_, _, delAdjSt_tri₁, delAdjSt_tri₂, by rw [triEnv_aj, triEnv_aj]; decide⟩

/-- **So the order clause is not derivable**: `SortedAdjSt` is strictly
stronger than `DelAdjSt` at the empty deletion set. If it were not,
both witnesses above would be sorted and `sortedAdjSt_row_eq` would
make them agree on slot `0`, which they do not. -/
theorem not_sortedAdjSt_of_delAdjSt :
    ¬ ∀ σ : Env, DelAdjSt "ao" "aj" "dg" "mt" triG ∅ σ →
        SortedAdjSt "ao" "aj" "dg" "mt" triG σ := by
  intro h
  obtain ⟨σ, σ', h1, h2, hne⟩ := delAdjSt_not_row_unique
  refine hne ?_
  have hstep : ∀ v : Fin 3,
      (fun i => 2 * i) ((v : ℕ) + 1) = (fun i => 2 * i) (v : ℕ) + (triG.neighborSet v).ncard := by
    intro v; rw [triG_ncard]; ring
  have key := sortedAdjSt_row_eq (h σ h1) (h σ' h2) (offF := fun i => 2 * i) rfl hstep 0
    (t := 0) (by rw [triG_ncard]; omega)
  simpa using key

/-! ## §2 The entry sort -/

/-- **Named residual (F6c13c-i): the entry sort.** From the
augmentation pass's output — the deletable region at the empty deletion
set — leave the *same* region with every row ascending, touching only
`aj` and `mt` and changing no allocation's length.

Counting-sort by target index does this in `O(N + m)` and needs no new
offsets, the row extents being the base degrees already in `ao`: one
pass over the carrier in increasing order, appending `u` to a running
cursor in the row of each of `u`'s neighbours, leaves every row
ascending; a second pass in the same order re-links the mates, because
after the first pass the neighbours of `u` below `u` are exactly an
ascending prefix of `u`'s row. The program is not written here. -/
def AdjSortIn (B : ℕ) (ao aj dg mt : String) (srtC : Com) {N : ℕ}
    (G : SimpleGraph (Fin N)) (K : ℕ) : Prop :=
  Spec B (fun σ => DelAdjSt ao aj dg mt G ∅ σ) srtC
    (fun σ σ' => SortedAdjSt ao aj dg mt G σ' ∧
      (∀ b : String, b ≠ aj → b ≠ mt → σ'.arrs b = σ.arrs b) ∧
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length)) K

/-- **The contract determines its output.** Any two programs meeting
`AdjSortIn` — at any word bounds, any array names, any budgets — leave
the same value in every live slot. So the peel that follows is a
function of `G`, which is what the replay of §3 needs and what
`DelAdjSt` alone does not give. -/
theorem adjSortIn_det {B B' : ℕ} {ao aj dg mt ao' aj' dg' mt' : String}
    {srtC srtC' : Com} {N : ℕ} {G : SimpleGraph (Fin N)} {K K' : ℕ}
    (h : AdjSortIn B ao aj dg mt srtC G K)
    (h' : AdjSortIn B' ao' aj' dg' mt' srtC' G K')
    {σ σ' : Env} (hpre : DelAdjSt ao aj dg mt G ∅ σ)
    (hpre' : DelAdjSt ao' aj' dg' mt' G ∅ σ')
    {offF : ℕ → ℕ} (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    ∃ τ τ' : Env, Run B srtC σ τ K ∧ Run B' srtC' σ' τ' K' ∧
      ∀ (v : Fin N) (t : ℕ), t < (G.neighborSet v).ncard →
        (τ.arrs aj).getD (offF (v : ℕ) + t) 0
          = (τ'.arrs aj').getD (offF (v : ℕ) + t) 0 := by
  obtain ⟨τ, hrun, hpost⟩ := h σ hpre
  obtain ⟨τ', hrun', hpost'⟩ := h' σ' hpre'
  exact ⟨τ, τ', hrun, hrun', fun v t ht =>
    sortedAdjSt_row_eq hpost.1 hpost'.1 h0 hstep v ht⟩

/-! ## §3 The abstract bucket replay -/

/-- A live degree is smaller than the live count: `v`'s live
neighbourhood avoids `v` itself. -/
theorem card_nbrsIn_lt {N : ℕ} (F : SimpleGraph (Fin N)) {S : Finset (Fin N)}
    {u : Fin N} (hu : u ∈ S) : (nbrsIn F S u).card < S.card :=
  lt_of_le_of_lt (Finset.card_le_card (nbrsIn_subset_erase F S u))
    (by rw [Finset.card_erase_of_mem hu]
        exact Nat.sub_lt (Finset.card_pos.mpr ⟨u, hu⟩) one_pos)

/-- The live minimum degree is below the live count. -/
theorem minDeg_lt_card {N : ℕ} (F : SimpleGraph (Fin N)) {S : Finset (Fin N)}
    (hS : S.Nonempty) : minDeg F S hS < S.card := by
  obtain ⟨u, hu⟩ := hS
  exact lt_of_le_of_lt (minDeg_le F _ hu) (card_nbrsIn_lt F hu)

/-- **The abstract bucket structure**: the live set, one list per
current degree, and the cursor. -/
structure BState (N : ℕ) where
  /-- The vertices not yet peeled. -/
  live : Finset (Fin N)
  /-- `bkt d` is the list of live vertices of current degree `d`. -/
  bkt : ℕ → List (Fin N)
  /-- A lower bound on the current minimum degree. It is never reset. -/
  cur : ℕ

/-- The structure at entry: every vertex live, bucketed by its degree
in `F`, cursor at `0`. Each bucket is ascending — what a build loop
running the carrier downward and pushing at the head produces. -/
noncomputable def bInit {N : ℕ} (F : SimpleGraph (Fin N)) : BState N where
  live := Finset.univ
  bkt := fun d =>
    (List.finRange N).filter (fun u => decide ((nbrsIn F Finset.univ u).card = d))
  cur := 0

/-- **One round on the structure**: peel `v`, move each live neighbour
of `v` down one bucket, drop the cursor to `v`'s degree minus one.

The moved vertices are prepended in ascending order — what a round
walking `v`'s row *downward* and pushing at the head produces, the row
being ascending after the entry sort — and the survivors of a bucket
keep their relative order, since a doubly-linked unlink does not
disturb them. The degrees here are *current* degrees; the row walked is
`v`'s *original* row, whose live entries are `nbrsIn F st.live v`. -/
noncomputable def bStep {N : ℕ} (F : SimpleGraph (Fin N)) (st : BState N)
    (v : Fin N) : BState N where
  live := st.live.erase v
  bkt := fun d =>
    (List.finRange N).filter
        (fun u => decide (u ∈ nbrsIn F st.live v ∧
          (nbrsIn F st.live u).card = d + 1))
      ++ (st.bkt d).filter
        (fun u => decide (u ≠ v ∧ u ∉ nbrsIn F st.live v))
  cur := (nbrsIn F st.live v).card - 1

@[simp] theorem bInit_live {N : ℕ} (F : SimpleGraph (Fin N)) :
    (bInit F).live = (Finset.univ : Finset (Fin N)) := rfl

@[simp] theorem bInit_cur {N : ℕ} (F : SimpleGraph (Fin N)) : (bInit F).cur = 0 := rfl

theorem bInit_bkt {N : ℕ} (F : SimpleGraph (Fin N)) (d : ℕ) :
    (bInit F).bkt d =
      (List.finRange N).filter (fun u => decide ((nbrsIn F Finset.univ u).card = d)) :=
  rfl

@[simp] theorem bStep_live {N : ℕ} (F : SimpleGraph (Fin N)) (st : BState N)
    (v : Fin N) : (bStep F st v).live = st.live.erase v := rfl

@[simp] theorem bStep_cur {N : ℕ} (F : SimpleGraph (Fin N)) (st : BState N)
    (v : Fin N) : (bStep F st v).cur = (nbrsIn F st.live v).card - 1 := rfl

theorem bStep_bkt {N : ℕ} (F : SimpleGraph (Fin N)) (st : BState N) (v : Fin N)
    (d : ℕ) :
    (bStep F st v).bkt d =
      (List.finRange N).filter
          (fun u => decide (u ∈ nbrsIn F st.live v ∧
            (nbrsIn F st.live u).card = d + 1))
        ++ (st.bkt d).filter
          (fun u => decide (u ≠ v ∧ u ∉ nbrsIn F st.live v)) := rfl

/-- The upward scan for the first nonempty bucket, with an explicit
fuel — the machine's `while bkt[c] is empty do c := c + 1`. -/
def firstNE {N : ℕ} (st : BState N) : ℕ → ℕ → ℕ
  | 0, d => d
  | fuel + 1, d => if st.bkt d = [] then firstNE st fuel (d + 1) else d

theorem firstNE_succ {N : ℕ} (st : BState N) (fuel d : ℕ) :
    firstNE st (fuel + 1) d =
      if st.bkt d = [] then firstNE st fuel (d + 1) else d := rfl

/-- **The scan lands on the first nonempty bucket at or above its
start** — provided the fuel covers the gap. -/
theorem firstNE_eq {N : ℕ} (st : BState N) :
    ∀ (fuel d m : ℕ), d ≤ m → (∀ e, d ≤ e → e < m → st.bkt e = []) →
      st.bkt m ≠ [] → m - d < fuel → firstNE st fuel d = m := by
  intro fuel
  induction fuel with
  | zero => intro d m _ _ _ hf; omega
  | succ f ih =>
      intro d m hdm hemp hne hf
      rw [firstNE_succ]
      rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
      · rw [if_neg hne]
      · rw [if_pos (hemp d le_rfl hlt)]
        exact ih (d + 1) m hlt (fun e he hem => hemp e (by omega) hem) hne (by omega)

/-- The bucket the cursor's scan stands at. -/
def bLevel {N : ℕ} (st : BState N) : ℕ := firstNE st (N + 1) st.cur

/-- **The pop**: the head of the first nonempty bucket at or above the
cursor. -/
def bPop {N : ℕ} (st : BState N) : Option (Fin N) := (st.bkt (bLevel st)).head?

/-- **The bucket invariant**: bucket `d` holds exactly the live
vertices of current degree `d`, and the cursor never stands above the
current minimum degree. -/
def BInv {N : ℕ} (F : SimpleGraph (Fin N)) (st : BState N) : Prop :=
  (∀ (d : ℕ) (u : Fin N), u ∈ st.bkt d ↔ u ∈ st.live ∧ (nbrsIn F st.live u).card = d) ∧
  (∀ hS : st.live.Nonempty, st.cur ≤ minDeg F st.live hS)

theorem bInit_inv {N : ℕ} (F : SimpleGraph (Fin N)) : BInv F (bInit F) := by
  refine ⟨fun d u => ?_, fun _ => Nat.zero_le _⟩
  rw [bInit_bkt, bInit_live, List.mem_filter]
  simp

/-- Under the invariant a bucket is nonempty exactly when some live
vertex has that current degree. -/
theorem bkt_ne_nil {N : ℕ} {F : SimpleGraph (Fin N)} {st : BState N}
    (h : BInv F st) {d : ℕ} {u : Fin N} (hu : u ∈ st.live)
    (hud : (nbrsIn F st.live u).card = d) : st.bkt d ≠ [] := by
  intro hc
  have hmem : u ∈ st.bkt d := (h.1 d u).mpr ⟨hu, hud⟩
  rw [hc] at hmem
  simp at hmem

/-- **The scan finds the minimum-degree bucket.** Under the invariant
every bucket strictly below the minimum degree is empty and the one at
it is not, so the cursor's upward scan stops exactly there — and the
rise it pays for is `minDeg - cur`. -/
theorem bLevel_eq_minDeg {N : ℕ} {F : SimpleGraph (Fin N)} {st : BState N}
    (h : BInv F st) (hS : st.live.Nonempty) :
    bLevel st = minDeg F st.live hS := by
  obtain ⟨hmem, hcur⟩ := h
  obtain ⟨w, hwS, hweq⟩ :=
    Finset.exists_mem_eq_inf' hS fun u => (nbrsIn F st.live u).card
  have hne : st.bkt (minDeg F st.live hS) ≠ [] :=
    bkt_ne_nil ⟨hmem, hcur⟩ hwS hweq.symm
  have hemp : ∀ e, st.cur ≤ e → e < minDeg F st.live hS → st.bkt e = [] := by
    intro e _ he
    by_contra hc
    obtain ⟨a, l, hal⟩ : ∃ a l, st.bkt e = a :: l := by
      cases hb : st.bkt e with
      | nil => exact absurd hb hc
      | cons a l => exact ⟨a, l, rfl⟩
    have ha : a ∈ st.bkt e := by rw [hal]; simp
    obtain ⟨haS, hadeg⟩ := (hmem e a).mp ha
    have := minDeg_le F hS haS
    omega
  have hlt : minDeg F st.live hS < N := by
    refine lt_of_lt_of_le (minDeg_lt_card F hS) ?_
    simpa using Finset.card_le_card (Finset.subset_univ st.live)
  exact firstNE_eq st (N + 1) st.cur (minDeg F st.live hS) (hcur hS) hemp hne
    (by omega)

/-- **The pop attains the minimum degree.** This is exactly the
obligation `MinDegSel.ofMin` asks for — membership and minimality —
and *not* the least-index clause `eq_minDegVert_of_bucket` needs, which
is what made the pinned tie-break quadratic. -/
theorem bPop_spec {N : ℕ} {F : SimpleGraph (Fin N)} {st : BState N}
    (h : BInv F st) (hS : st.live.Nonempty) :
    ∃ v : Fin N, bPop st = some v ∧ v ∈ st.live ∧
      (nbrsIn F st.live v).card = minDeg F st.live hS := by
  have hlev := bLevel_eq_minDeg h hS
  obtain ⟨w, hwS, hweq⟩ :=
    Finset.exists_mem_eq_inf' hS fun u => (nbrsIn F st.live u).card
  have hne : st.bkt (bLevel st) ≠ [] := by
    rw [hlev]; exact bkt_ne_nil h hwS hweq.symm
  obtain ⟨a, l, hal⟩ : ∃ a l, st.bkt (bLevel st) = a :: l := by
    cases hb : st.bkt (bLevel st) with
    | nil => exact absurd hb hne
    | cons a l => exact ⟨a, l, rfl⟩
  have ha : a ∈ st.bkt (bLevel st) := by rw [hal]; simp
  obtain ⟨haS, hadeg⟩ := (h.1 _ a).mp ha
  exact ⟨a, by rw [bPop, hal]; rfl, haS, by rw [← hlev]; exact hadeg⟩

/-- **One round preserves the invariant.** Bucket membership is
recomputed from `card_nbrsIn_erase` — a live vertex loses exactly one
from its current degree iff it is a neighbour of the peeled vertex —
and the cursor's new value is licensed by
`minDeg_le_minDeg_erase_succ`, which is why it need not be reset. -/
theorem bStep_inv {N : ℕ} {F : SimpleGraph (Fin N)} {st : BState N} {v : Fin N}
    (h : BInv F st) (hv : v ∈ st.live) (hS : st.live.Nonempty)
    (hattain : (nbrsIn F st.live v).card = minDeg F st.live hS) :
    BInv F (bStep F st v) := by
  obtain ⟨hmem, -⟩ := h
  constructor
  · intro d u
    simp only [bStep_bkt, bStep_live, List.mem_append, List.mem_filter,
      List.mem_finRange, true_and, decide_eq_true_eq, hmem]
    constructor
    · rintro (⟨hun, hud⟩ | ⟨⟨huS, hud⟩, huv, hun⟩)
      · have huE : u ∈ st.live.erase v := nbrsIn_subset_erase F st.live v hun
        have huS : u ∈ st.live := Finset.mem_of_mem_erase huE
        have hstep := card_nbrsIn_erase F st.live hv huS
        rw [if_pos hun] at hstep
        exact ⟨huE, by omega⟩
      · have huE : u ∈ st.live.erase v := Finset.mem_erase.mpr ⟨huv, huS⟩
        have hstep := card_nbrsIn_erase F st.live hv huS
        rw [if_neg hun] at hstep
        exact ⟨huE, by omega⟩
    · rintro ⟨huE, hud⟩
      have huv : u ≠ v := Finset.ne_of_mem_erase huE
      have huS : u ∈ st.live := Finset.mem_of_mem_erase huE
      have hstep := card_nbrsIn_erase F st.live hv huS
      by_cases hun : u ∈ nbrsIn F st.live v
      · rw [if_pos hun] at hstep
        exact Or.inl ⟨hun, by omega⟩
      · rw [if_neg hun] at hstep
        exact Or.inr ⟨⟨huS, by omega⟩, huv, hun⟩
  · intro hS'
    show (nbrsIn F st.live v).card - 1 ≤ minDeg F (st.live.erase v) hS'
    have := minDeg_le_minDeg_erase_succ F hS hv hS'
    omega

/-! ### The replay -/

/-- **The peel replayed on the structure alone.** A function of `F`
only: `bRun F k` is the state after `k` rounds. This is legitimate as
the abstract side of `MinDegSel` because the peel is deterministic once
the adjacency rows are — which is what the entry sort buys, and what
`delAdjCom`'s swap-delete would destroy. -/
noncomputable def bRun {N : ℕ} (F : SimpleGraph (Fin N)) : ℕ → BState N
  | 0 => bInit F
  | k + 1 =>
      match bPop (bRun F k) with
      | some v => bStep F (bRun F k) v
      | none => bRun F k

theorem bRun_zero {N : ℕ} (F : SimpleGraph (Fin N)) : bRun F 0 = bInit F := rfl

theorem bRun_succ {N : ℕ} (F : SimpleGraph (Fin N)) (k : ℕ) :
    bRun F (k + 1) =
      match bPop (bRun F k) with
      | some v => bStep F (bRun F k) v
      | none => bRun F k := rfl

/-- The replay keeps the invariant at every round. -/
theorem bRun_inv {N : ℕ} (F : SimpleGraph (Fin N)) (k : ℕ) : BInv F (bRun F k) := by
  induction k with
  | zero => exact bInit_inv F
  | succ k ih =>
      rw [bRun_succ]
      rcases (bRun F k).live.eq_empty_or_nonempty with hemp | hne
      · have hnone : bPop (bRun F k) = none := by
          rw [bPop]
          cases hb : (bRun F k).bkt (bLevel (bRun F k)) with
          | nil => rfl
          | cons a l =>
              exfalso
              have ha : a ∈ (bRun F k).bkt (bLevel (bRun F k)) := by rw [hb]; simp
              have := ((ih.1 _ a).mp ha).1
              rw [hemp] at this
              exact absurd this (Finset.notMem_empty a)
        rw [hnone]; exact ih
      · obtain ⟨v, hpop, hvS, hattain⟩ := bPop_spec ih hne
        rw [hpop]
        exact bStep_inv ih hvS hne hattain

/-- The live count counts down by one a round, so the round index is
recovered from the live set: `k = N - |S|`. -/
theorem bRun_live_card {N : ℕ} (F : SimpleGraph (Fin N)) :
    ∀ k : ℕ, k ≤ N → (bRun F k).live.card = N - k := by
  intro k
  induction k with
  | zero => intro _; simp [bRun_zero, bInit]
  | succ k ih =>
      intro hk
      have hcard := ih (by omega)
      have hne : (bRun F k).live.Nonempty := by
        rw [← Finset.card_pos, hcard]; omega
      obtain ⟨v, hpop, hvS, -⟩ := bPop_spec (bRun_inv F k) hne
      rw [bRun_succ, hpop]
      show ((bRun F k).live.erase v).card = N - (k + 1)
      rw [Finset.card_erase_of_mem hvS, hcard]
      omega

/-! ### The replay's round, packaged

The three facts a loop rule wants of a round, read off the replay: it
peels a vertex out of the live set, the live set is the erasure, and
the cursor falls by at most one. -/

/-- The cursor never leaves `[0, N]`. -/
theorem bRun_cur_le {N : ℕ} (F : SimpleGraph (Fin N)) (k : ℕ) :
    (bRun F k).cur ≤ N := by
  induction k with
  | zero => simp [bRun_zero, bInit]
  | succ k ih =>
      rw [bRun_succ]
      cases hp : bPop (bRun F k) with
      | none => exact ih
      | some v =>
          show (nbrsIn F (bRun F k).live v).card - 1 ≤ N
          have := Finset.card_le_univ (nbrsIn F (bRun F k).live v)
          simp only [Fintype.card_fin] at this
          omega

/-- Before the last round the live set is nonempty. -/
theorem bRun_live_nonempty {N : ℕ} (F : SimpleGraph (Fin N)) {k : ℕ} (hk : k < N) :
    (bRun F k).live.Nonempty := by
  rw [← Finset.card_pos, bRun_live_card F k (le_of_lt hk)]
  omega

/-- **One round of the replay**, as the loop rule consumes it: the pop
is defined, it is live, the next live set is the erasure, and the
cursor falls by at most one — the last by
`minDeg_le_minDeg_erase_succ`, which is why the cursor is never
reset. -/
theorem bRun_round {N : ℕ} (F : SimpleGraph (Fin N)) {k : ℕ} (hk : k < N) :
    ∃ v : Fin N, bPop (bRun F k) = some v ∧ v ∈ (bRun F k).live ∧
      (bRun F (k + 1)).live = ((bRun F k).live).erase v ∧
      (bRun F k).cur ≤ (bRun F (k + 1)).cur + 1 := by
  have hne := bRun_live_nonempty F hk
  obtain ⟨v, hpop, hvS, hattain⟩ := bPop_spec (bRun_inv F k) hne
  refine ⟨v, hpop, hvS, ?_, ?_⟩
  · rw [bRun_succ, hpop]; rfl
  · rw [bRun_succ, hpop]
    show (bRun F k).cur ≤ (nbrsIn F (bRun F k).live v).card - 1 + 1
    have := (bRun_inv F k).2 hne
    omega

/-! ## §4 The selection the replay names, and the loop rule at it -/

/-- The guard the selection wears: a candidate is taken only if it is
live and attains the minimum degree, and otherwise the pinned
`minDegVert` is used. It makes the two `MinDegSel` clauses hold
unconditionally; `bucketPick_bRun` shows the guard passes at every
state the replay actually reaches. -/
noncomputable def guardPick {N : ℕ} (F : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (hS : S.Nonempty) (o : Option (Fin N)) : Fin N :=
  match o with
  | some v =>
      if v ∈ S ∧ (nbrsIn F S v).card = minDeg F S hS then v else minDegVert F S hS
  | none => minDegVert F S hS

theorem guardPick_none {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty) : guardPick F S hS none = minDegVert F S hS := rfl

theorem guardPick_some {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty) (v : Fin N) :
    guardPick F S hS (some v) =
      if v ∈ S ∧ (nbrsIn F S v).card = minDeg F S hS then v else minDegVert F S hS := rfl

/-- **The bucket selection.** The pop of the replay at the round the
live set identifies (`k = N - |S|`, by `bRun_live_card`), guarded so
that the two `MinDegSel` clauses hold unconditionally: off the replay
the guard fails and the pinned `minDegVert` is used, which attains as
well. `bucketPick_bRun` says the guard passes at every reachable state,
which is all the peel program needs.

Defining the selection by replay is the route wave 25 flagged as the
open one: legitimate because the peel is deterministic and `S`
determines the round index, and available *only* because the rows are
not written — see the module docstring. -/
noncomputable def bucketPick {N : ℕ} (F : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (hS : S.Nonempty) : Fin N :=
  guardPick F S hS (bPop (bRun F (N - S.card)))

theorem bucketPick_mem {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty) : bucketPick F S hS ∈ S := by
  rw [bucketPick]
  cases h : bPop (bRun F (N - S.card)) with
  | none => rw [guardPick_none]; exact minDegVert_mem F S hS
  | some v =>
      rw [guardPick_some]
      by_cases hg : v ∈ S ∧ (nbrsIn F S v).card = minDeg F S hS
      · rw [if_pos hg]; exact hg.1
      · rw [if_neg hg]; exact minDegVert_mem F S hS

theorem bucketPick_card {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty) : (nbrsIn F S (bucketPick F S hS)).card = minDeg F S hS := by
  rw [bucketPick]
  cases h : bPop (bRun F (N - S.card)) with
  | none => rw [guardPick_none]; exact minDeg_minDegVert F S hS
  | some v =>
      rw [guardPick_some]
      by_cases hg : v ∈ S ∧ (nbrsIn F S v).card = minDeg F S hS
      · rw [if_pos hg]; exact hg.2
      · rw [if_neg hg]; exact minDeg_minDegVert F S hS

/-- **The bucket pop is an attaining selection.** Through
`MinDegSel.ofMin`: what is proved of the pop is membership and
minimality — *attainment, not least index*, which is the whole point of
wave 25's re-pin. -/
noncomputable def bucketSel (N : ℕ) : MinDegSel N :=
  MinDegSel.ofMin bucketPick bucketPick_mem
    (fun F S hS u hu => by
      rw [bucketPick_card F S hS]
      exact minDeg_le F hS hu)

@[simp] theorem bucketSel_pick {N : ℕ} (F : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (hS : S.Nonempty) :
    (bucketSel N).pick F S hS = bucketPick F S hS := rfl

/-- **At every reachable state the selection is the machine's pop.**
The guard in `bucketPick` passes along the replay, so the vertex the
round pops is exactly `(bucketSel N).pick` of the current live set.
That is what a round program needs in order to leave
`selPerm (bucketSel N) F` in the rank array; `selRank_bPop` below turns
it into the concrete number the round stores. -/
theorem bucketPick_bRun {N : ℕ} (F : SimpleGraph (Fin N)) {k : ℕ} (hk : k < N)
    (hS : (bRun F k).live.Nonempty) :
    bPop (bRun F k) = some (bucketPick F (bRun F k).live hS) := by
  have hcard : N - ((bRun F k).live).card = k := by
    rw [bRun_live_card F k (le_of_lt hk)]; omega
  obtain ⟨v, hpop, hvS, hattain⟩ := bPop_spec (bRun_inv F k) hS
  rw [bucketPick, hcard, hpop, guardPick_some, if_pos ⟨hvS, hattain⟩]

/-- **The static-adjacency peel loop, at a linear budget.**
`peelLoop_linear_static_cursor` with every graph-side obligation
discharged from §3: the machine has only to keep a round counter `kof`,
step the replay by one a round, and pay
`a + b·|N_F(v)| + e·(cursor rise)` for the round whose vertex the replay
pops. The live set and the cursor are then read off the replay, so the
loop rule's `Sof σ' = (Sof σ).erase v` and `cur σ ≤ cur σ' + 1` need no
further hypothesis.

The `b·|N_F(v)|` term is the round's walk of `v`'s **original** row —
the charge `livePot` cannot carry and `staticPot` can — and the `e`
term is the cursor's rise `minDeg - cur`, which `bLevel_eq_minDeg`
identifies. -/
theorem peelLoop_linear_bucket {B N : ℕ} {F : SimpleGraph (Fin N)}
    {bc : Cond} {body : Com} (I : Env → Prop) (kof : Env → ℕ) (a b e : ℕ)
    (hdef : ∀ σ, I σ → ∃ x, bc.evalB B σ = some x)
    (hstep : ∀ σ, I σ → bc.evalB B σ = some true →
      ∃ (v : Fin N) (σ' : Env) (K : ℕ),
        kof σ < N ∧ bPop (bRun F (kof σ)) = some v ∧
        Run B body σ σ' K ∧ I σ' ∧ kof σ' = kof σ + 1 ∧
        1 + bc.size + K ≤ a + b * (F.neighborSet v).ncard
          + e * ((bRun F (kof σ')).cur + 1 - (bRun F (kof σ)).cur)) :
    Spec B (fun σ => I σ ∧ kof σ = 0) (.while bc body)
      (fun _ σ' => I σ' ∧ bc.evalB B σ' = some false)
      ((a + e) * N + b * slotCount F + e * N + 1 + bc.size) := by
  refine (peelLoop_linear_static_cursor (F := F) I (fun σ => (bRun F (kof σ)).live)
    (fun σ => (bRun F (kof σ)).cur) a b e
    (fun σ _ => bRun_cur_le F (kof σ)) hdef ?_).pre ?_
  · intro σ hI hbc
    obtain ⟨v, σ', K, hkN, hpop, hrun, hI', hkof, hcost⟩ := hstep σ hI hbc
    obtain ⟨v', hpop', hvS, hlive, hcur⟩ := bRun_round F hkN
    have hvv : v' = v := by rw [hpop] at hpop'; exact (Option.some.inj hpop').symm
    rw [hvv] at hvS hlive
    refine ⟨v, σ', K, hvS, hrun, hI', ?_, ?_, ?_⟩
    · show (bRun F (kof σ')).live = ((bRun F (kof σ)).live).erase v
      rw [hkof]; exact hlive
    · show (bRun F (kof σ)).cur ≤ (bRun F (kof σ')).cur + 1
      rw [hkof]; exact hcur
    · show 1 + bc.size + K ≤ a + b * (F.neighborSet v).ncard
        + e * ((bRun F (kof σ')).cur + 1 - (bRun F (kof σ)).cur)
      exact hcost
  · rintro σ ⟨hI, hk⟩
    refine ⟨hI, ?_⟩
    show (bRun F (kof σ)).live = Finset.univ
    rw [hk]; rfl


/-! ### The countdown the round must write

`selRankAux_peel_step` fixes the convention; these two lemmas pin it to
the replay, so the round program has a concrete number to store and no
freedom to be off by one. -/

/-- **Every live vertex's whole-peel rank is already its rank in the
peel restricted to the live set** — wave 23's `PeelInv` clause, at the
bucket selection, proved from `selRankAux_peel_step` alone. -/
theorem selRank_eq_selRankAux_bRun {N : ℕ} (F : SimpleGraph (Fin N)) :
    ∀ k : ℕ, k ≤ N → ∀ x ∈ (bRun F k).live,
      Lax3Proofs.CoverRoutine.selRank (bucketSel N) F x =
        Lax3Proofs.CoverRoutine.selRankAux (bucketSel N) F (bRun F k).live x := by
  intro k
  induction k with
  | zero => intro _ x _; rw [bRun_zero, bInit_live]; rfl
  | succ k ih =>
      intro hk x hx
      have hk' : k < N := by omega
      obtain ⟨v, hpop, hvS, hlive, -⟩ := bRun_round F hk'
      have hS := bRun_live_nonempty F hk'
      have hpick : (bucketSel N).pick F (bRun F k).live hS = v := by
        have h := bucketPick_bRun F hk' hS
        rw [hpop] at h
        exact (Option.some.inj h).symm
      have hx' : x ∈ (bRun F k).live := by
        rw [hlive] at hx; exact Finset.mem_of_mem_erase hx
      have hxE : x ∈ (bRun F k).live.erase v := by rw [← hlive]; exact hx
      have hstep := (Lax3Proofs.CoverRoutine.selRankAux_peel_step
        (bucketSel N) F hS).2
      rw [hpick] at hstep
      rw [ih (by omega) x hx', hlive]
      exact hstep x hxE

/-- **What the round must store.** At round `k` the popped vertex's
rank is `N - k - 1`, so the *first* vertex peeled from `N` live gets
`N - 1` and the countdown falls by one a round. The convention is
`selRankAux_peel_step`'s and is not optional: an off-by-one here
silently produces a different permutation that still typechecks against
`RankArr`. -/
theorem selRank_bPop {N : ℕ} (F : SimpleGraph (Fin N)) {k : ℕ} (hk : k < N)
    {v : Fin N} (hv : bPop (bRun F k) = some v) :
    Lax3Proofs.CoverRoutine.selRank (bucketSel N) F v = N - k - 1 := by
  have hS := bRun_live_nonempty F hk
  have hpick : (bucketSel N).pick F (bRun F k).live hS = v := by
    have h := bucketPick_bRun F hk hS
    rw [hv] at h
    exact (Option.some.inj h).symm
  have hvS : v ∈ (bRun F k).live := by
    rw [← hpick]; exact (bucketSel N).mem _ _ hS
  rw [selRank_eq_selRankAux_bRun F k (le_of_lt hk) v hvS, ← hpick,
    (Lax3Proofs.CoverRoutine.selRankAux_peel_step (bucketSel N) F hS).1,
    bRun_live_card F k (le_of_lt hk)]

/-! ## §5 What the peel pass still owes, and at what budget

Everything above is graph-side and proved. What is not written here is
the round program itself: the entry sort (§2), the bucket build, and
the round that pops, writes the countdown rank, and walks `v`'s
original row. §5 records the budget that program has to meet and the
consequence of its meeting it — so the residual is named at the right
shape rather than discharged at the wrong one. -/

open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.CoverRoutine (selChain selOrderingRoutine)

/-- **The linear peel budget**: `a` per vertex of the carrier, `b` per
*slot* of the augmented graph, and a constant. It is the shape a peel
pass built on §1–§4 can meet, not a budget proved of any program here.

The carrier term has to cover the per-round overhead and the cursor's
total rise, and the slot term the row walking:
`peelLoop_linear_bucket`'s conclusion is
`(a'+e)·N + b·slotCount F + e·N + O(1)` for its own round constants
`a' b e`, which is of this shape because the cursor falls by at most
one a round (`bRun_round`, from `minDeg_le_minDeg_erase_succ`) and
because a round reading `v`'s *original* row is paid for by
`staticPot_erase` out of a potential that starts at `slotCount`
(`staticPot_univ`). The entry sort and the bucket build are single
passes and are meant to be absorbed into the same two coefficients —
`AdjSortIn`'s own `K` is a parameter, so that absorption is part of the
residual, not proved here. The slot term is the adjacency region's own
width: `offF N = slotCount` by `offF_eq_slotCount`.

The point of the shape is what is **absent**: there is no `A.N * A.N`
term. Wave 23's discharge (`covSelPeelIn_peelCom_mdSel`) is
`86·A.N² + 43·A.N + 14`, and §7 of the algorithm charges the whole
cover routine at `a·N^{1+2δ}`, which the square breaks at the root. -/
noncomputable def linearPeelBudget (R a b cst : ℕ) {Λ n₀ : ℕ}
    (A : Arena Λ n₀) : ℕ :=
  a * A.N + b * slotCount ((selChain (bucketSel A.N) A.G R).toGraph) + cst

/-- **The ordering pass at the bucket selection, linear.** As soon as
the peel program meets `CovSelPeelIn` at `bucketSel` and the linear
budget, the whole ordering pass — augmentation then peel — is
`CovOrderIn` at `Kag + (a·A.N + b·m + cst)`, with `m` the augmented
graph's slot count and **no `A.N * A.N` anywhere**.

The glue is wave 25's `covOrderIn_of_aug_selPeel` verbatim; what is new
is only that the selection is now one a machine can produce in `O(1)`
per round (`bPop_spec`, `bucketPick_bRun`) and that the budget is
stated in the shape §7 can absorb. The peel hypothesis is the leaf's
named residual and is **not** discharged here; the quadratic discharge
at the pinned selection already exists as
`covSelPeelIn_peelCom_mdSel`. -/
theorem covOrderIn_bucket (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Sag Smp Ssw : ℕ → Env → Prop) (agC mpC : ℕ → Com)
    (Kag : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (a b cst : ℕ)
    (hag : CovAugAdjSelIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm
      ca co aoO ajO dgO mtO Sag Smp Ssw agC Kag)
    (hmp : CovSelPeelIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm
      ca co ra aoO ajO dgO mtO Smp Ssw mpC
      (fun _ A => linearPeelBudget R a b cst A)) :
    CovOrderIn C hC φ (selOrderingRoutine (fun m => bucketSel m) R) G c w q ℓp
      htabF hbf Adm ca co ra (fun j σ => Sag j σ ∧ Smp j σ) Ssw
      (fun j => .seq (agC j) (mpC j))
      (fun j A => Kag j A + linearPeelBudget R a b cst A) :=
  covOrderIn_of_aug_selPeel C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf
    Adm ca co ra aoO ajO dgO mtO Sag Smp Ssw agC mpC Kag _ hag hmp

end Lax3Proofs.Prog

/-! ## §6 Axiom audit

Everything above rests on the three standard axioms alone. The single
exception is §5's `covOrderIn_bucket`, which passes through
`Headline.headlineSetup` and therefore — exactly like the landed
`covOrderIn_of_aug_selPeel` it applies — additionally carries Lax12's
endorsed `uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms Lax3Proofs.Prog.sortedAdjSt_row_eq

#print axioms Lax3Proofs.Prog.not_sortedAdjSt_of_delAdjSt

#print axioms Lax3Proofs.Prog.bPop_spec

#print axioms Lax3Proofs.Prog.bStep_inv

#print axioms Lax3Proofs.Prog.bRun_inv

#print axioms Lax3Proofs.Prog.bucketPick_bRun

#print axioms Lax3Proofs.Prog.selRank_bPop

#print axioms Lax3Proofs.Prog.peelLoop_linear_bucket

#print axioms Lax3Proofs.Prog.covOrderIn_bucket
