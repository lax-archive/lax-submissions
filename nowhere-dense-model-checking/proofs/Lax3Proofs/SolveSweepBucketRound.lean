import Lax3Proofs.SolveSweepBucketProg

/-!
# F6c13c (completion) — the round program: a static-adjacency bucket
peel, and `CovSelPeelIn` at `bucketSel` in linear time

Wave 26 (`SolveSweepBucketProg`) built the bucket machinery — the
replay `bRun`, the selection `bucketSel` it names, the loop rule
`peelLoop_linear_bucket` — and left `covOrderIn_bucket` conditional on
one hypothesis: that some IMP+ program meets `CovSelPeelIn` at
`bucketSel` and a **linear** budget. This file writes that program and
discharges the hypothesis (`covSelPeelIn_bucketPeelCom`,
`covOrderIn_bucketPeel`).

## The design, and why it is forced

**The peel never writes a row.** Wave 23's `delAdjCom` is a
swap-delete — `adjCore_unlink` moves the row's last live entry into the
hole — and `AdjDeleteInW`'s postcondition is again just a `DelAdjSt`,
which carries **no row-order clause** (`not_sortedAdjSt_of_delAdjSt`).
So a peel that compacts its rows loses the one thing the replay needs:
that the rows are a function of `G`. `delAdjCom` is therefore not used
below; `ao` and `aj` are read-only for the whole pass, and a round
walks `v`'s **original** row. The price is that the round is charged
`|N_F(v)|` rather than `v`'s current degree, which is exactly what wave
25's `staticPot` pays for — at the same linear total, since both
potentials start at `slotCount F`.

One counting sort at entry makes the row order a function of `G` for
the whole run. It is a **transpose**, not a per-row sort: scanning `u`
upward and appending `u` to the new row of each of its neighbours costs
`O(N + m)` and leaves every new row strictly ascending, because `u`
ascends (`transCom_spec`). The sorted rows go into `mt` — the mate
pointers are dead the moment `delAdjCom` is refused, and `mt` is
already exactly `offF N` wide — and `dg` is then free to hold the
*current* degrees, the row length being read as `ao[v+1] - ao[v]`.

## What is here

* **§1 the bucket stacks.** Bucket `d` is the array segment
  `sk[d·N .. d·N + tp[d])`, read top-first, so a push is a cons and a
  pop is a tail (`mLst_push`, `mLst_pop`, `mLst_frame`). The stacks are
  **lazily** cleaned: when a vertex's degree drops it is pushed into
  its new bucket and its entry in the old one is left to be skipped,
  and the peeled vertex's own cell is never removed at all. `mOK` is
  the staleness test — live *and* at the right current degree — folded
  into one comparison the way `peelKey` folds its two.

* **§2 the amortization at lazy deletion.**
  `peelLoop_linear_static_cursor_lazy` is wave 25's rule with a fourth
  potential term `f·(cells in the stacks)`, and
  `peelLoop_linear_bucket_lazy` is wave 26's `peelLoop_linear_bucket`
  at it. The fourth term is what wave 26's rule cannot carry: a round's
  stale-skipping is bounded by the *pushes of earlier rounds*, not by
  its own `|N_F(v)|`, so it needs a potential of its own. Total pushes
  are `N + slotCount F`, so the term is linear and the budget's shape
  is unchanged.

* **§3–§5 the entry phases.** `rowList` (a filter of `List.range N`, so
  ascending by construction); the transpose `transCom` at
  `27·m + 22·N + 6`; the zeroing pass and the bucket build `bkBuildCom`
  at `25·N + 6`, whose downward scan with head pushes reproduces
  `bInit`'s `(finRange N).filter` exactly (`bktV_bInit`).

* **§6 the round.** `RSt` is the refinement invariant — the stacks,
  *with their stale cells dropped*, are the replay's buckets. `scanCom`
  walks the cursor up, dropping stale heads, and stops at the
  minimum-degree bucket (`bLevel_eq_minDeg`) with the replay's pop in
  `bk.v`; `walkCom` walks `v`'s original row downward, pushing each
  live neighbour one bucket down; `round_bkts` is the one-off
  computation that the result is `bStep`'s bucket, moved group and
  survivors both. `roundCom_run` costs
  `91·|N_F(v)| + 79 + 50·(cursor rise) + 50·(cells removed)`.

* **§7 the pass.** `bucketPeelCom` and `bucketPeelCom_spec`: the peel
  leaves `RankArr (selPerm (bucketSel N) F)` at
  **`313·N + 118·m + 40`**.

* **§8 the residual, discharged.** `covSelPeelIn_bucketPeelCom` is
  `CovSelPeelIn` at `bucketSel`, every clause verbatim, at
  `linearPeelBudget R 313 118 40` — **no `A.N * A.N` term**; and
  `covOrderIn_bucketPeel` is wave 26's `covOrderIn_bucket` with its
  hypothesis gone.

## The budget, honestly

`Kmp j A = 313·A.N + 118·(slot count) + 40`. The four amortizations
that carry it are `staticPot_erase` (the row walk, through
`peelLoop_linear_static_cursor_lazy`'s `b` term),
`minDeg_le_minDeg_erase_succ` through `bRun_round` (the cursor's total
rise, the `e` term), the cell count (the stale skipping, the new `f`
term, starting at `N` because the build pushes each vertex once), and
the per-round constant. The scratch the pass asks for is the rank
region, the bucket tops (`n` cells) and the bucket cells (`n² + n`
cells: `n` blocks of width `n`, one per degree level, plus the guard
slot a push writes at). The *time* is linear; only the cell block is
quadratic in space, and it is the same shape as the adjacency region
the pass already reads (`offF_le_sq`).

## Conventions that are not optional

The countdown is `selRankAux_peel_step`'s, pinned by `selRank_bPop`:
the vertex popped at round `k` gets `N - k - 1`. The degrees in the
buckets are **current** degrees (`dg`, decremented in place); the row a
round walks is the **original** row (`mt`, at the *base* offsets `ao`).
The cursor is never reset: it falls by exactly one a round.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)
open Lax3Proofs.CoverRoutine (MinDegSel)

/-! ## §1 The bucket stacks

Bucket `d` lives in the slice `sk[d·N .. d·N + tp[d])` of one array,
the most recent push last. `mLst` reads it back as a list, head first,
so that a push is a cons and a pop is a tail — the two shapes `bStep`
is written in. -/

/-- **Bucket `d`'s stack, as a list**, most recently pushed first. -/
def mLst (tp sk : String) (N : ℕ) (σ : Env) (d : ℕ) : List ℕ :=
  ((List.range ((σ.arrs tp).getD d 0)).map
    (fun i => (σ.arrs sk).getD (d * N + i) 0)).reverse

theorem mLst_length {tp sk : String} {N : ℕ} {σ : Env} {d : ℕ} :
    (mLst tp sk N σ d).length = (σ.arrs tp).getD d 0 := by
  simp [mLst]

/-- The stack is read out of the cells below the top only, so any two
states that agree there have the same stack. -/
theorem mLst_frame {tp sk : String} {N : ℕ} {σ σ' : Env} {d : ℕ}
    (htp : (σ'.arrs tp).getD d 0 = (σ.arrs tp).getD d 0)
    (hsk : ∀ i < (σ.arrs tp).getD d 0,
      (σ'.arrs sk).getD (d * N + i) 0 = (σ.arrs sk).getD (d * N + i) 0) :
    mLst tp sk N σ' d = mLst tp sk N σ d := by
  have hmap : List.map (fun i => (σ'.arrs sk).getD (d * N + i) 0)
        (List.range ((σ.arrs tp).getD d 0))
      = List.map (fun i => (σ.arrs sk).getD (d * N + i) 0)
        (List.range ((σ.arrs tp).getD d 0)) :=
    List.map_congr_left fun i hi => hsk i (List.mem_range.mp hi)
  rw [mLst, mLst, htp, hmap]

/-- **A push is a cons.** -/
theorem mLst_push {tp sk : String} {N : ℕ} {σ σ' : Env} {d u : ℕ}
    (htp : (σ'.arrs tp).getD d 0 = (σ.arrs tp).getD d 0 + 1)
    (hsk : ∀ i < (σ.arrs tp).getD d 0,
      (σ'.arrs sk).getD (d * N + i) 0 = (σ.arrs sk).getD (d * N + i) 0)
    (htop : (σ'.arrs sk).getD (d * N + (σ.arrs tp).getD d 0) 0 = u) :
    mLst tp sk N σ' d = u :: mLst tp sk N σ d := by
  have hmap : List.map (fun i => (σ'.arrs sk).getD (d * N + i) 0)
        (List.range ((σ.arrs tp).getD d 0))
      = List.map (fun i => (σ.arrs sk).getD (d * N + i) 0)
        (List.range ((σ.arrs tp).getD d 0)) :=
    List.map_congr_left fun i hi => hsk i (List.mem_range.mp hi)
  rw [mLst, mLst, htp, List.range_succ, List.map_append, List.reverse_append, hmap]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rw [htop]

/-- **A pop is a tail.** -/
theorem mLst_pop {tp sk : String} {N : ℕ} {σ σ' : Env} {d x : ℕ} {l : List ℕ}
    (hl : mLst tp sk N σ d = x :: l)
    (htp : (σ'.arrs tp).getD d 0 + 1 = (σ.arrs tp).getD d 0)
    (hsk : ∀ i < (σ'.arrs tp).getD d 0,
      (σ'.arrs sk).getD (d * N + i) 0 = (σ.arrs sk).getD (d * N + i) 0) :
    mLst tp sk N σ' d = l := by
  have hσ : mLst tp sk N σ d = (σ.arrs sk).getD (d * N + (σ'.arrs tp).getD d 0) 0
      :: mLst tp sk N σ' d := by
    refine mLst_push (u := (σ.arrs sk).getD (d * N + (σ'.arrs tp).getD d 0) 0)
      htp.symm ?_ rfl
    intro i hi
    exact (hsk i hi).symm
  rw [hσ] at hl
  exact (List.cons.inj hl).2

/-- **The staleness test.** A cell of bucket `d` is live business
exactly when its vertex is still live — its rank cell holds the
sentinel `N` — *and* its current degree is still `d`. Both are folded
into one comparison the way `peelKey` folds its two: a ranked vertex
contributes a full `N` to the leading term, and every current degree is
below `N`. -/
def mKey (ra dg : String) (N : ℕ) (σ : Env) (x : ℕ) : ℕ :=
  (N - (σ.arrs ra).getD x 0) * N + (σ.arrs dg).getD x 0

/-- The staleness test as a `Bool`, for `List.filter`. -/
def mOK (ra dg : String) (N : ℕ) (σ : Env) (d : ℕ) (x : ℕ) : Bool :=
  decide (mKey ra dg N σ x = d)

theorem mOK_iff {ra dg : String} {N : ℕ} {σ : Env} {d x : ℕ} (hd : d < N)
    (hra : (σ.arrs ra).getD x 0 ≤ N) :
    mOK ra dg N σ d x = true ↔
      ((σ.arrs ra).getD x 0 = N ∧ (σ.arrs dg).getD x 0 = d) := by
  rw [mOK, decide_eq_true_iff, mKey]
  constructor
  · intro h
    rcases Nat.eq_or_lt_of_le hra with hx | hx
    · exact ⟨hx, by rw [hx] at h; simpa using h⟩
    · exfalso
      have h1 : 1 ≤ N - (σ.arrs ra).getD x 0 := by omega
      have h2 : N ≤ (N - (σ.arrs ra).getD x 0) * N := by
        calc N = 1 * N := (one_mul N).symm
          _ ≤ _ := Nat.mul_le_mul_right N h1
      omega
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

/-! ## §2 The amortization at lazy deletion

Wave 26's `peelLoop_linear_bucket` charges a round
`a + b·|N_F(v)| + e·(cursor rise)`. A lazily cleaned stack needs one
term more: the stale cells a round skips were pushed by *earlier*
rounds, so their number is bounded by no function of this round's
vertex. `nc` counts the cells currently in the stacks; every skip drops
it by one and every push raises it by one, and the pushes are already
paid for by the `b` term. -/

/-- **The static peel loop with a cursor and a cell count.**
`peelLoop_linear_static_cursor` with a fourth potential term: the round
may in addition pay `f` per cell it removes from a structure that
started with `nc₀` cells and gains at most one per unit of the `b`
term. Everything else — the hypotheses, the cursor licence, the
conclusion's shape — is wave 25's rule verbatim. -/
theorem peelLoop_linear_static_cursor_lazy {B N : ℕ} {F : SimpleGraph (Fin N)}
    {bc : Cond} {body : Com} (I : Env → Prop) (Sof : Env → Finset (Fin N))
    (cur nc : Env → ℕ) (a b e f nc₀ : ℕ)
    (hcurN : ∀ σ, I σ → cur σ ≤ N)
    (hdef : ∀ σ, I σ → ∃ v, bc.evalB B σ = some v)
    (hstep : ∀ σ, I σ → bc.evalB B σ = some true →
      ∃ (v : Fin N) (σ' : Env) (K : ℕ), v ∈ Sof σ ∧ Run B body σ σ' K ∧ I σ' ∧
        Sof σ' = (Sof σ).erase v ∧ cur σ ≤ cur σ' + 1 ∧
        1 + bc.size + K + f * nc σ' ≤ a + b * (F.neighborSet v).ncard
          + e * (cur σ' + 1 - cur σ) + f * nc σ) :
    Spec B (fun σ => I σ ∧ Sof σ = Finset.univ ∧ nc σ ≤ nc₀) (.while bc body)
      (fun _ σ' => I σ' ∧ bc.evalB B σ' = some false)
      ((a + e) * N + b * slotCount F + e * N + f * nc₀ + 1 + bc.size) := by
  classical
  refine Spec.while_potential I
    (fun σ => (a + e) * (Sof σ).card + b * staticPot F (Sof σ) + e * (N - cur σ)
      + f * nc σ)
    hdef ?_ (fun _ h => h.1) ?_
  · intro σ hI hv
    obtain ⟨v, σ', K, hvS, hrun, hI', hSof, hcurdrop, hcost⟩ := hstep σ hI hv
    refine ⟨σ', K, hrun, hI', ?_⟩
    show 1 + bc.size + K
        + ((a + e) * (Sof σ').card + b * staticPot F (Sof σ') + e * (N - cur σ')
            + f * nc σ')
      ≤ (a + e) * (Sof σ).card + b * staticPot F (Sof σ) + e * (N - cur σ) + f * nc σ
    obtain ⟨c, hc⟩ : ∃ c, (Sof σ).card = c + 1 := by
      have := Finset.card_pos.mpr (⟨v, hvS⟩ : (Sof σ).Nonempty)
      exact ⟨(Sof σ).card - 1, by omega⟩
    have hcard : (Sof σ').card = c := by
      rw [hSof, Finset.card_erase_of_mem hvS, hc]
      omega
    have hpot : staticPot F (Sof σ)
        = (F.neighborSet v).ncard + staticPot F (Sof σ') := by
      rw [hSof]; exact staticPot_erase F (Sof σ) hvS
    have hdist : b * staticPot F (Sof σ)
        = b * (F.neighborSet v).ncard + b * staticPot F (Sof σ') := by
      rw [hpot]; ring
    have hac : (a + e) * (c + 1) = (a + e) * c + (a + e) := by ring
    have hkey : e * (cur σ' + 1 - cur σ) + e * (N - cur σ')
        ≤ e + e * (N - cur σ) := by
      have hx := hcurN σ hI
      have hy := hcurN σ' hI'
      have h1 : (cur σ' + 1 - cur σ) + (N - cur σ') ≤ 1 + (N - cur σ) := by omega
      calc e * (cur σ' + 1 - cur σ) + e * (N - cur σ')
          = e * ((cur σ' + 1 - cur σ) + (N - cur σ')) := by ring
        _ ≤ e * (1 + (N - cur σ)) := Nat.mul_le_mul_left e h1
        _ = e + e * (N - cur σ) := by ring
    rw [hcard, hc, hdist, hac]
    omega
  · rintro σ ⟨hI, huniv, hnc⟩
    show (a + e) * (Sof σ).card + b * staticPot F (Sof σ) + e * (N - cur σ)
        + f * nc σ + 1 + bc.size
      ≤ (a + e) * N + b * slotCount F + e * N + f * nc₀ + 1 + bc.size
    have hcard : (Sof σ).card = N := by
      rw [huniv, Finset.card_univ, Fintype.card_fin]
    have hcur : e * (N - cur σ) ≤ e * N := Nat.mul_le_mul_left e (Nat.sub_le _ _)
    have hncb : f * nc σ ≤ f * nc₀ := Nat.mul_le_mul_left f hnc
    have hpot : staticPot F (Sof σ) = slotCount F := by rw [huniv, staticPot_univ]
    rw [hcard, hpot]
    omega

/-- **The static-adjacency bucket peel loop, at a linear budget, with
lazily cleaned stacks.** `peelLoop_linear_bucket` with the fourth
potential term of `peelLoop_linear_static_cursor_lazy`: the machine
keeps a round counter `kof` and a cell count `nc`, steps the replay by
one a round, and pays `a + b·|N_F(v)| + e·(cursor rise) + f·(cells
removed)` for the round whose vertex the replay pops.

The live set and the cursor are read off the replay, so the loop rule's
`Sof σ' = (Sof σ).erase v` and `cur σ ≤ cur σ' + 1` need no further
hypothesis — the second is `bRun_round`, i.e.
`minDeg_le_minDeg_erase_succ`, which is why the cursor is never
reset. -/
theorem peelLoop_linear_bucket_lazy {B N : ℕ} {F : SimpleGraph (Fin N)}
    {bc : Cond} {body : Com} (I : Env → Prop) (kof : Env → ℕ) (nc : Env → ℕ)
    (a b e f nc₀ : ℕ)
    (hdef : ∀ σ, I σ → ∃ x, bc.evalB B σ = some x)
    (hstep : ∀ σ, I σ → bc.evalB B σ = some true →
      ∃ (v : Fin N) (σ' : Env) (K : ℕ),
        kof σ < N ∧ bPop (bRun F (kof σ)) = some v ∧
        Run B body σ σ' K ∧ I σ' ∧ kof σ' = kof σ + 1 ∧
        1 + bc.size + K + f * nc σ' ≤ a + b * (F.neighborSet v).ncard
          + e * ((bRun F (kof σ')).cur + 1 - (bRun F (kof σ)).cur) + f * nc σ) :
    Spec B (fun σ => I σ ∧ kof σ = 0 ∧ nc σ ≤ nc₀) (.while bc body)
      (fun _ σ' => I σ' ∧ bc.evalB B σ' = some false)
      ((a + e) * N + b * slotCount F + e * N + f * nc₀ + 1 + bc.size) := by
  refine (peelLoop_linear_static_cursor_lazy (F := F) I
    (fun σ => (bRun F (kof σ)).live) (fun σ => (bRun F (kof σ)).cur) nc a b e f nc₀
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
    · exact hcost
  · rintro σ ⟨hI, hk, hnc⟩
    refine ⟨hI, ?_, hnc⟩
    show (bRun F (kof σ)).live = Finset.univ
    rw [hk]; rfl

/-! ## §3 The rows the entry transpose produces

A row is named by the ascending list of its neighbours' indices.
`rowList` is that list; it is a filter of `List.range N`, so it is
strictly increasing by construction and `Finset.orderEmbOfFin_unique`
is not needed — the sortedness the design rests on is the shape of the
definition. -/

/-- Adjacency to `z`, as a decidable test on a natural number. -/
noncomputable def adjB {N : ℕ} (F : SimpleGraph (Fin N)) (z : Fin N) (u : ℕ) : Bool :=
  decide (u ∈ (nbrsIn F Finset.univ z).image Fin.val)

theorem adjB_iff {N : ℕ} {F : SimpleGraph (Fin N)} {z : Fin N} {u : ℕ} :
    adjB F z u = true ↔ ∃ w : Fin N, F.Adj w z ∧ (w : ℕ) = u := by
  classical
  rw [adjB, decide_eq_true_iff, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (mem_nbrsIn.mp hw).2, rfl⟩
  · rintro ⟨w, hadj, rfl⟩
    exact ⟨w, mem_nbrsIn.mpr ⟨Finset.mem_univ w, hadj⟩, rfl⟩

theorem adjB_val {N : ℕ} {F : SimpleGraph (Fin N)} {z w : Fin N} :
    adjB F z (w : ℕ) = true ↔ F.Adj w z := by
  rw [adjB_iff]
  exact ⟨fun ⟨w', hadj, hv⟩ => by rwa [Fin.val_inj.mp hv] at hadj, fun h => ⟨w, h, rfl⟩⟩

theorem adjB_lt {N : ℕ} {F : SimpleGraph (Fin N)} {z : Fin N} {u : ℕ}
    (h : adjB F z u = true) : u < N := by
  obtain ⟨w, -, rfl⟩ := adjB_iff.mp h
  exact w.isLt

/-- **The row of `z`**: its neighbours' indices, ascending. -/
noncomputable def rowList {N : ℕ} (F : SimpleGraph (Fin N)) (z : Fin N) : List ℕ :=
  (List.range N).filter (adjB F z)

/-- The prefix of the row contributed by the vertices below `U`. -/
noncomputable def rowUpTo {N : ℕ} (F : SimpleGraph (Fin N)) (U : ℕ) (z : Fin N) :
    List ℕ :=
  (List.range U).filter (adjB F z)

@[simp] theorem rowUpTo_zero {N : ℕ} (F : SimpleGraph (Fin N)) (z : Fin N) :
    rowUpTo F 0 z = [] := by simp [rowUpTo]

theorem rowUpTo_succ {N : ℕ} (F : SimpleGraph (Fin N)) (U : ℕ) (z : Fin N) :
    rowUpTo F (U + 1) z =
      rowUpTo F U z ++ (if adjB F z U = true then [U] else []) := by
  rw [rowUpTo, rowUpTo, List.range_succ, List.filter_append]
  congr 1
  by_cases h : adjB F z U = true <;> simp [h]

theorem rowUpTo_full {N : ℕ} (F : SimpleGraph (Fin N)) (z : Fin N) :
    rowUpTo F N z = rowList F z := rfl

/-- A prefix of the row is a sublist of it. -/
theorem rowUpTo_sublist {N : ℕ} (F : SimpleGraph (Fin N)) {U : ℕ} (hU : U ≤ N)
    (z : Fin N) : (rowUpTo F U z).Sublist (rowList F z) :=
  ((List.range_sublist).mpr hU).filter _

theorem rowUpTo_length_le {N : ℕ} (F : SimpleGraph (Fin N)) {U : ℕ} (hU : U ≤ N)
    (z : Fin N) : (rowUpTo F U z).length ≤ (rowList F z).length :=
  (rowUpTo_sublist F hU z).length_le

/-- **The row has one entry per neighbour.** -/
theorem rowList_length {N : ℕ} (F : SimpleGraph (Fin N)) (z : Fin N) :
    (rowList F z).length = (F.neighborSet z).ncard := by
  classical
  have hnd : (rowList F z).Nodup := (List.nodup_range).filter _
  have htf : (rowList F z).toFinset = (nbrsIn F Finset.univ z).image Fin.val := by
    ext u
    simp only [List.mem_toFinset, rowList, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨-, h⟩
      exact (decide_eq_true_iff).mp h
    · intro h
      exact ⟨adjB_lt (by rw [adjB]; exact decide_eq_true h), by rw [adjB]; exact decide_eq_true h⟩
  rw [← List.toFinset_card_of_nodup hnd, htf,
    Finset.card_image_of_injective _ Fin.val_injective, card_nbrsIn_univ]

/-- The row is strictly increasing. -/
theorem rowList_sorted {N : ℕ} (F : SimpleGraph (Fin N)) (z : Fin N) :
    (rowList F z).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem rowList_lt_N {N : ℕ} {F : SimpleGraph (Fin N)} {z : Fin N} {u : ℕ}
    (hu : u ∈ rowList F z) : u < N :=
  List.mem_range.mp (List.mem_of_mem_filter (l := List.range N) hu)

theorem mem_rowList {N : ℕ} {F : SimpleGraph (Fin N)} {z w : Fin N} :
    (w : ℕ) ∈ rowList F z ↔ F.Adj w z := by
  rw [rowList, List.mem_filter, List.mem_range]
  exact ⟨fun h => adjB_val.mp h.2, fun h => ⟨w.isLt, adjB_val.mpr h⟩⟩

/-! ## §4 The entry transpose

Scanning `u` upward and appending `u` to the new row of each of its
neighbours costs `O(N + m)` and leaves every new row strictly
ascending, because `u` ascends. The new rows go into `mt`: the mate
pointers are dead the moment `delAdjCom` is refused, and `mt` is
already exactly `offF N` wide. -/

/-- The machine's row for `z`: the cells `mt[offF z .. offF z + tp[z])`,
in order. During the transpose `tp` is the fill cursor; afterwards it is
re-zeroed and becomes the bucket tops. -/
def mRow (mt tp : String) (offF : ℕ → ℕ) (σ : Env) (z : ℕ) : List ℕ :=
  (List.range ((σ.arrs tp).getD z 0)).map (fun s => (σ.arrs mt).getD (offF z + s) 0)

@[simp] theorem mRow_setVar (mt tp : String) (offF : ℕ → ℕ) (σ : Env) (x : String)
    (v z : ℕ) : mRow mt tp offF (σ.setVar x v) z = mRow mt tp offF σ z := rfl

theorem mRow_length {mt tp : String} {offF : ℕ → ℕ} {σ : Env} {z : ℕ} :
    (mRow mt tp offF σ z).length = (σ.arrs tp).getD z 0 := by simp [mRow]

theorem mRow_frame {mt tp : String} {offF : ℕ → ℕ} {σ σ' : Env} {z : ℕ}
    (htp : (σ'.arrs tp).getD z 0 = (σ.arrs tp).getD z 0)
    (hmt : ∀ s < (σ.arrs tp).getD z 0,
      (σ'.arrs mt).getD (offF z + s) 0 = (σ.arrs mt).getD (offF z + s) 0) :
    mRow mt tp offF σ' z = mRow mt tp offF σ z := by
  have hmap : List.map (fun s => (σ'.arrs mt).getD (offF z + s) 0)
        (List.range ((σ.arrs tp).getD z 0))
      = List.map (fun s => (σ.arrs mt).getD (offF z + s) 0)
        (List.range ((σ.arrs tp).getD z 0)) :=
    List.map_congr_left fun s hs => hmt s (List.mem_range.mp hs)
  rw [mRow, mRow, htp, hmap]

/-- Filling the next cell appends to the row. -/
theorem mRow_append {mt tp : String} {offF : ℕ → ℕ} {σ σ' : Env} {z u : ℕ}
    (htp : (σ'.arrs tp).getD z 0 = (σ.arrs tp).getD z 0 + 1)
    (hmt : ∀ s < (σ.arrs tp).getD z 0,
      (σ'.arrs mt).getD (offF z + s) 0 = (σ.arrs mt).getD (offF z + s) 0)
    (htop : (σ'.arrs mt).getD (offF z + (σ.arrs tp).getD z 0) 0 = u) :
    mRow mt tp offF σ' z = mRow mt tp offF σ z ++ [u] := by
  have hmap : List.map (fun s => (σ'.arrs mt).getD (offF z + s) 0)
        (List.range ((σ.arrs tp).getD z 0))
      = List.map (fun s => (σ.arrs mt).getD (offF z + s) 0)
        (List.range ((σ.arrs tp).getD z 0)) :=
    List.map_congr_left fun s hs => hmt s (List.mem_range.mp hs)
  rw [mRow, mRow, htp, List.range_succ, List.map_append, hmap]
  simp only [List.map_cons, List.map_nil]
  rw [htop]

/-- The contribution `u`'s row makes to `z`'s row in its first `t`
steps: one copy of `u` for each position of `z` among `u`'s first `t`
neighbours. Duplicate-freeness of a row makes it `[]` or `[u]`; the
loop does not need to know which. -/
def hitL (J0 : List ℕ) (offF : ℕ → ℕ) (U : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | t + 1, z =>
      hitL J0 offF U t z ++ (if J0.getD (offF U + t) 0 = z then [U] else [])

@[simp] theorem hitL_zero (J0 : List ℕ) (offF : ℕ → ℕ) (U z : ℕ) :
    hitL J0 offF U 0 z = [] := rfl

theorem hitL_succ (J0 : List ℕ) (offF : ℕ → ℕ) (U t z : ℕ) :
    hitL J0 offF U (t + 1) z =
      hitL J0 offF U t z ++ (if J0.getD (offF U + t) 0 = z then [U] else []) := rfl

/-- No position holds `z`: the contribution is empty. -/
theorem hitL_eq_nil {J0 : List ℕ} {offF : ℕ → ℕ} {U : ℕ} :
    ∀ (D z : ℕ), (∀ s, s < D → J0.getD (offF U + s) 0 ≠ z) →
      hitL J0 offF U D z = [] := by
  intro D
  induction D with
  | zero => intro _ _; rfl
  | succ D ih =>
      intro z h
      rw [hitL_succ, ih z (fun s hs => h s (by omega)),
        if_neg (h D (by omega))]
      rfl

/-- Exactly one position holds `z`: the contribution is one copy of
`u`. -/
theorem hitL_eq_singleton {J0 : List ℕ} {offF : ℕ → ℕ} {U : ℕ} :
    ∀ (D z t₀ : ℕ), t₀ < D →
      (∀ s, s < D → (J0.getD (offF U + s) 0 = z ↔ s = t₀)) →
      hitL J0 offF U D z = [U] := by
  intro D
  induction D with
  | zero => intro _ _ h _; omega
  | succ D ih =>
      intro z t₀ ht h
      rcases Nat.lt_or_ge t₀ D with hlt | hge
      · rw [hitL_succ, ih z t₀ hlt (fun s hs => h s (by omega)),
          if_neg (fun hc => by have := (h D (by omega)).mp hc; omega)]
        rfl
      · have ht₀ : t₀ = D := by omega
        subst ht₀
        rw [hitL_succ, hitL_eq_nil _ z
            (fun s hs hc => by have := (h s (by omega)).mp hc; omega),
          if_pos ((h t₀ (by omega)).mpr rfl)]
        rfl

/-- **What the entry region gives the transpose**, as facts about the
two arrays it reads. Every clause is `AdjFrame`/`AdjCore` at the empty
deletion set, with the state's name replaced by the array's value so
that the invariant can pin the array and the facts still apply. -/
structure TSrc {N : ℕ} (F : SimpleGraph (Fin N)) (offF : ℕ → ℕ) (A0 J0 : List ℕ) :
    Prop where
  /-- The offsets are anchored. -/
  off0 : offF 0 = 0
  /-- One row per vertex, of its degree. -/
  offs : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (F.neighborSet v).ncard
  /-- The offset region is allocated. -/
  aolen : N + 1 ≤ A0.length
  /-- The offset region holds the offsets. -/
  aoval : ∀ i, i ≤ N → A0.getD i 0 = offF i
  /-- The slot region is allocated. -/
  ajlen : offF N ≤ J0.length
  /-- Every slot holds a neighbour. -/
  sound : ∀ (u : Fin N) (t : ℕ), t < (F.neighborSet u).ncard →
    ∃ w : Fin N, F.Adj u w ∧ J0.getD (offF (u : ℕ) + t) 0 = (w : ℕ)
  /-- Every neighbour has a slot. -/
  comp : ∀ (u w : Fin N), F.Adj u w →
    ∃ t, t < (F.neighborSet u).ncard ∧ J0.getD (offF (u : ℕ) + t) 0 = (w : ℕ)
  /-- A row has no duplicates. -/
  inj : ∀ (u : Fin N) (a b : ℕ), a < (F.neighborSet u).ncard →
    b < (F.neighborSet u).ncard →
    J0.getD (offF (u : ℕ) + a) 0 = J0.getD (offF (u : ℕ) + b) 0 → a = b

namespace TSrc

variable {N : ℕ} {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ} {A0 J0 : List ℕ}

theorem offN_le_sq (h : TSrc F offF A0 J0) : offF N ≤ N * N :=
  offF_le_sq h.off0 h.offs N le_rfl

theorem slot_lt (h : TSrc F offF A0 J0) {x : Fin N} {a : ℕ}
    (ha : a < (F.neighborSet x).ncard) : offF (x : ℕ) + a < offF N :=
  offF_slot_lt h.offs ha

theorem slot_ne (h : TSrc F offF A0 J0) {x y : Fin N} (hxy : x ≠ y) {a b : ℕ}
    (ha : a < (F.neighborSet x).ncard) (hb : b < (F.neighborSet y).ncard) :
    offF (x : ℕ) + a ≠ offF (y : ℕ) + b :=
  offF_slot_ne h.offs hxy ha hb

/-- The row's slot holding `w` is the unique one, and it exists exactly
when `w` is a neighbour: the hit list of the whole row is `[u]` at a
neighbour and `[]` elsewhere. -/
theorem hitL_full (h : TSrc F offF A0 J0) (u z : Fin N) :
    hitL J0 offF (u : ℕ) ((F.neighborSet u).ncard) (z : ℕ)
      = (if adjB F z (u : ℕ) = true then [(u : ℕ)] else []) := by
  by_cases hadj : F.Adj u z
  · obtain ⟨t₀, ht₀, hval⟩ := h.comp u z hadj
    rw [if_pos (adjB_val.mpr hadj)]
    refine hitL_eq_singleton _ _ t₀ ht₀ ?_
    intro s hs
    exact ⟨fun hq => h.inj u s t₀ hs ht₀ (by rw [hq, hval]), fun hq => by rw [hq, hval]⟩
  · rw [if_neg (fun hc => hadj (adjB_val.mp hc))]
    refine hitL_eq_nil _ _ ?_
    intro s hs hc
    obtain ⟨w, hw, hval⟩ := h.sound u s hs
    rw [hval] at hc
    exact hadj (by rwa [Fin.val_inj.mp hc] at hw)

end TSrc

/-! ### The two invariants -/

/-- The transpose's outer invariant: the rows so far are the
contributions of the vertices below the counter. -/
def TOut (ao aj mt tp : String) {N : ℕ} (F : SimpleGraph (Fin N)) (offF : ℕ → ℕ)
    (A0 J0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "bk.n" = N ∧ σ.vars "bk.u" ≤ N ∧
  σ.arrs ao = A0 ∧ σ.arrs aj = J0 ∧
  offF N ≤ (σ.arrs mt).length ∧ N ≤ (σ.arrs tp).length ∧
  ∀ z : Fin N, mRow mt tp offF σ (z : ℕ) = rowUpTo F (σ.vars "bk.u") z

/-- The transpose's inner invariant, at the outer counter `U` and the
row length `D`. -/
def TIn (ao aj mt tp : String) {N : ℕ} (F : SimpleGraph (Fin N)) (offF : ℕ → ℕ)
    (A0 J0 : List ℕ) (U D : ℕ) (σ : Env) : Prop :=
  σ.vars "bk.n" = N ∧ σ.vars "bk.u" = U ∧ σ.vars "bk.m" = D ∧ σ.vars "bk.t" ≤ D ∧
  σ.arrs ao = A0 ∧ σ.arrs aj = J0 ∧
  offF N ≤ (σ.arrs mt).length ∧ N ≤ (σ.arrs tp).length ∧
  ∀ z : Fin N, mRow mt tp offF σ (z : ℕ)
    = rowUpTo F U z ++ hitL J0 offF U (σ.vars "bk.t") (z : ℕ)

/-- **The fill cursor never runs past the row it fills.** A row's hit
list has at most one entry, and if it has one then the vertex being
processed is itself a neighbour, so the row has room for it. -/
theorem TIn_tp_le {ao aj mt tp : String} {N : ℕ} {F : SimpleGraph (Fin N)}
    {offF : ℕ → ℕ} {A0 J0 : List ℕ} {U D : ℕ} {σ : Env}
    (hsrc : TSrc F offF A0 J0) (h : TIn ao aj mt tp F offF A0 J0 U D σ)
    (hU : U < N) (hD : D = (F.neighborSet ⟨U, hU⟩).ncard) (z : Fin N) :
    (σ.arrs tp).getD (z : ℕ) 0 ≤ (F.neighborSet z).ncard := by
  obtain ⟨-, -, -, htle, -, -, -, -, hrow⟩ := h
  have hlen : (σ.arrs tp).getD (z : ℕ) 0
      = (rowUpTo F U z).length + (hitL J0 offF U (σ.vars "bk.t") (z : ℕ)).length := by
    have := hrow z
    rw [← mRow_length (mt := mt) (tp := tp) (offF := offF) (σ := σ) (z := (z : ℕ)), this,
      List.length_append]
  by_cases hex : ∃ s, s < σ.vars "bk.t" ∧ J0.getD (offF U + s) 0 = (z : ℕ)
  · obtain ⟨s₀, hs₀, hval⟩ := hex
    have hsingle : hitL J0 offF U (σ.vars "bk.t") (z : ℕ) = [U] := by
      refine hitL_eq_singleton _ _ s₀ hs₀ ?_
      intro s hs
      refine ⟨fun hq => hsrc.inj ⟨U, hU⟩ s s₀ (by rw [← hD]; omega) (by rw [← hD]; omega)
        (by rw [hq, hval]), fun hq => by rw [hq, hval]⟩
    obtain ⟨w, hadj, hwv⟩ := hsrc.sound ⟨U, hU⟩ s₀ (by rw [← hD]; omega)
    rw [hval] at hwv
    have hzw : w = z := Fin.val_inj.mp hwv.symm
    subst hzw
    have hadjB : adjB F w (U : ℕ) = true := adjB_val.mpr (by simpa using hadj)
    have hstep := rowUpTo_succ F U w
    rw [if_pos hadjB] at hstep
    have hle := rowUpTo_length_le F (U := U + 1) hU w
    rw [hstep, List.length_append, rowList_length] at hle
    rw [hlen, hsingle]
    simpa using hle
  · have hex' : ∀ s, s < σ.vars "bk.t" → J0.getD (offF U + s) 0 ≠ (z : ℕ) :=
      fun s hs hc => hex ⟨s, hs, hc⟩
    rw [hlen, hitL_eq_nil _ _ hex']
    have hle := rowUpTo_length_le F (U := U) (le_of_lt hU) z
    rw [rowList_length] at hle
    simpa using hle

/-! ### The program -/

/-- One turn of the transpose's inner loop: append `u` to the new row
of its `t`-th neighbour. -/
def transBody (ao aj mt tp : String) : Com :=
  .seq (.assign "bk.z" (.get aj (.add (.get ao (.var "bk.u")) (.var "bk.t"))))
  (.seq (.store mt (.add (.get ao (.var "bk.z")) (.get tp (.var "bk.z"))) (.var "bk.u"))
  (.seq (.store tp (.var "bk.z") (.add (.get tp (.var "bk.z")) (.lit 1)))
        (.assign "bk.t" (.add (.var "bk.t") (.lit 1)))))

/-- One turn of the transpose's outer loop: walk `u`'s row. The row
length is read as `ao[u+1] - ao[u]`, which leaves `dg` free to hold the
*current* degree for the rest of the pass. -/
def transOuterBody (ao aj mt tp : String) : Com :=
  .seq (.assign "bk.m"
      (.sub (.get ao (.add (.var "bk.u") (.lit 1))) (.get ao (.var "bk.u"))))
  (.seq (.assign "bk.t" (.lit 0))
  (.seq (.while (.lt (.var "bk.t") (.var "bk.m")) (transBody ao aj mt tp))
        (.assign "bk.u" (.add (.var "bk.u") (.lit 1)))))

/-- **The entry transpose.** -/
def transCom (ao aj mt tp : String) : Com :=
  .seq (.assign "bk.u" (.lit 0))
    (.while (.lt (.var "bk.u") (.var "bk.n")) (transOuterBody ao aj mt tp))

/-! ### The inner turn -/

set_option maxHeartbeats 1000000 in
/-- **One turn of the transpose**: `u` is appended to the new row of its
`t`-th neighbour. The write lands at that row's own fill cursor, which
`TIn_tp_le` shows is still inside the row. -/
theorem transBody_spec {ao aj mt tp : String}
    (hma : mt ≠ ao) (hmj : mt ≠ aj) (hmt : mt ≠ tp) (hta : tp ≠ ao) (htj : tp ≠ aj)
    {B N : ℕ} {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ} {A0 J0 : List ℕ}
    (hsrc : TSrc F offF A0 J0) (hB : N + N * N + 1 < B)
    {U D : ℕ} (hU : U < N) (hD : D = (F.neighborSet ⟨U, hU⟩).ncard) :
    Spec B (fun σ => TIn ao aj mt tp F offF A0 J0 U D σ ∧ σ.vars "bk.t" < D)
      (transBody ao aj mt tp)
      (fun σ σ' => TIn ao aj mt tp F offF A0 J0 U D σ' ∧
        σ'.vars "bk.t" = σ.vars "bk.t" + 1) 23 := by
  classical
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hn, hu, hm, htle, hao, haj, hmtlen, htplen, hrow⟩ := hI
  have hmt' : tp ≠ mt := Ne.symm hmt
  have hom : ao ≠ mt := Ne.symm hma
  have hot : ao ≠ tp := Ne.symm hta
  have hjm : aj ≠ mt := Ne.symm hmj
  have hjt : aj ≠ tp := Ne.symm htj
  have hsq : offF N ≤ N * N := hsrc.offN_le_sq
  have haolen : N + 1 ≤ (σ.arrs ao).length := by rw [hao]; exact hsrc.aolen
  have hajlen : offF N ≤ (σ.arrs aj).length := by rw [haj]; exact hsrc.ajlen
  have haoU : (σ.arrs ao).getD U 0 = offF U := by
    rw [hao]; exact hsrc.aoval U (le_of_lt hU)
  have hltD : σ.vars "bk.t" < (F.neighborSet (⟨U, hU⟩ : Fin N)).ncard := by
    rw [← hD]; exact hlt
  obtain ⟨w, hadjw, hwval0⟩ := hsrc.sound ⟨U, hU⟩ (σ.vars "bk.t") hltD
  have hajUt : (σ.arrs aj).getD (offF U + σ.vars "bk.t") 0 = (w : ℕ) := by
    rw [haj]; exact hwval0
  have haoW : (σ.arrs ao).getD (w : ℕ) 0 = offF (w : ℕ) := by
    rw [hao]; exact hsrc.aoval (w : ℕ) (le_of_lt w.isLt)
  have hhitW : hitL J0 offF U (σ.vars "bk.t") (w : ℕ) = [] := by
    refine hitL_eq_nil _ _ ?_
    intro s hs hc
    have := hsrc.inj ⟨U, hU⟩ s (σ.vars "bk.t") (by omega) hltD (by rw [hc, hwval0])
    omega
  have htpWeq : (σ.arrs tp).getD (w : ℕ) 0 = (rowUpTo F U w).length := by
    have h := hrow w
    rw [hhitW, List.append_nil] at h
    rw [← mRow_length (mt := mt) (tp := tp) (offF := offF) (σ := σ) (z := (w : ℕ)), h]
  have htpWlt : (σ.arrs tp).getD (w : ℕ) 0 < (F.neighborSet w).ncard := by
    have hadjB : adjB F w U = true := adjB_val.mpr (by simpa using hadjw)
    have hstep := rowUpTo_succ F U w
    rw [if_pos hadjB] at hstep
    have hle := rowUpTo_length_le F (U := U + 1) hU w
    rw [hstep, List.length_append, rowList_length] at hle
    rw [htpWeq]
    simpa using hle
  have hslotW : offF (w : ℕ) + (σ.arrs tp).getD (w : ℕ) 0 < offF N := hsrc.slot_lt htpWlt
  have hslotUt : offF U + σ.vars "bk.t" < offF N := hsrc.slot_lt (x := ⟨U, hU⟩) hltD
  have hdegW : (F.neighborSet w).ncard < N := ncard_neighborSet_lt F w
  have hDN : D ≤ N := by rw [hD]; exact le_of_lt (ncard_neighborSet_lt F _)
  have hwN : (w : ℕ) < N := w.isLt
  run_vcg
  all_goals simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr,
    String.reduceEq, reduceIte, eq_self_iff_true, if_true, if_neg hmt', if_neg hmt,
    if_neg hom, if_neg hot, if_neg hjm, if_neg hjt, hu, haoU, hajUt, haoW,
    List.length_set]
  all_goals try omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [vars_setVar, vars_setArr, String.reduceEq, reduceIte]; exact hn
  · simp only [vars_setVar, vars_setArr, String.reduceEq, reduceIte]; exact hu
  · simp only [vars_setVar, vars_setArr, String.reduceEq, reduceIte]; exact hm
  · simp only [vars_setVar, vars_setArr, String.reduceEq, reduceIte,
      eq_self_iff_true, if_true]; omega
  · simp only [arrs_setVar, arrs_setArr, if_neg hot, if_neg hom]; exact hao
  · simp only [arrs_setVar, arrs_setArr, if_neg hjt, if_neg hjm]; exact haj
  · simp only [arrs_setVar, length_arrs_setArr]; exact hmtlen
  · simp only [arrs_setVar, length_arrs_setArr]; exact htplen
  · intro z
    simp only [vars_setVar, vars_setArr, arrs_setVar, String.reduceEq, reduceIte,
      eq_self_iff_true, if_true]
    by_cases hzw : z = w
    · rw [hzw]
      have hgoalR : rowUpTo F U w ++ hitL J0 offF U (σ.vars "bk.t" + 1) (w : ℕ)
          = mRow mt tp offF σ (w : ℕ) ++ [U] := by
        rw [hitL_succ, if_pos hwval0, hrow w, hhitW]
        simp
      rw [hgoalR]
      refine mRow_append ?_ ?_ ?_
      · simp only [arrs_setVar, arrs_setArr, eq_self_iff_true, if_true, if_neg hmt']
        exact getD_set_self (by omega)
      · intro s hs
        simp only [arrs_setVar, arrs_setArr, eq_self_iff_true, if_true, if_neg hmt]
        exact getD_set_of_ne (by omega)
      · simp only [arrs_setVar, arrs_setArr, eq_self_iff_true, if_true, if_neg hmt]
        exact getD_set_self (by omega)
    · have hzwv : (z : ℕ) ≠ (w : ℕ) := fun hc => hzw (Fin.val_inj.mp hc)
      have hgoalR : rowUpTo F U z ++ hitL J0 offF U (σ.vars "bk.t" + 1) (z : ℕ)
          = mRow mt tp offF σ (z : ℕ) := by
        rw [hitL_succ, if_neg (fun hc => hzwv (by rw [← hc, hwval0])), hrow z]
        simp
      rw [hgoalR]
      refine mRow_frame ?_ ?_
      · simp only [arrs_setVar, arrs_setArr, eq_self_iff_true, if_true, if_neg hmt']
        exact getD_set_of_ne hzwv
      · intro s hs
        simp only [arrs_setVar, arrs_setArr, eq_self_iff_true, if_true, if_neg hmt]
        refine getD_set_of_ne ?_
        have hsz : s < (F.neighborSet z).ncard :=
          lt_of_lt_of_le hs (TIn_tp_le hsrc hI' hU hD z)
        exact hsrc.slot_ne hzw hsz htpWlt
  · simp only [vars_setVar, vars_setArr, String.reduceEq, reduceIte,
      eq_self_iff_true, if_true]

set_option maxHeartbeats 1000000 in
/-- **One turn of the transpose's outer loop**: walk `u`'s row, at a
cost affine in its length. The cost is stated in the offsets so that
the outer loop's potential telescopes to the slot count. -/
theorem transOuterBody_run {ao aj mt tp : String}
    (hma : mt ≠ ao) (hmj : mt ≠ aj) (hmt : mt ≠ tp) (hta : tp ≠ ao) (htj : tp ≠ aj)
    {B N : ℕ} {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ} {A0 J0 : List ℕ}
    (hsrc : TSrc F offF A0 J0) (hB : N + N * N + 1 < B)
    {σ : Env} (hI : TOut ao aj mt tp F offF A0 J0 σ) (hlt : σ.vars "bk.u" < N) :
    ∃ σ' : Env, Run B (transOuterBody ao aj mt tp) σ σ'
        (27 * (offF (σ.vars "bk.u" + 1) - offF (σ.vars "bk.u")) + 18) ∧
      TOut ao aj mt tp F offF A0 J0 σ' ∧ σ'.vars "bk.u" = σ.vars "bk.u" + 1 := by
  classical
  obtain ⟨hn, hule, hao, haj, hmtlen, htplen, hrow⟩ := hI
  set U : ℕ := σ.vars "bk.u" with hU
  set D : ℕ := (F.neighborSet (⟨U, hlt⟩ : Fin N)).ncard with hD
  have hsq : offF N ≤ N * N := hsrc.offN_le_sq
  have haolen : N + 1 ≤ (σ.arrs ao).length := by rw [hao]; exact hsrc.aolen
  have haoU : (σ.arrs ao).getD U 0 = offF U := by
    rw [hao]; exact hsrc.aoval U (le_of_lt hlt)
  have haoU1 : (σ.arrs ao).getD (U + 1) 0 = offF (U + 1) := by
    rw [hao]; exact hsrc.aoval (U + 1) hlt
  have hDeq : offF (U + 1) - offF U = D := by
    have h := hsrc.offs ⟨U, hlt⟩
    simp only [Fin.val_mk] at h
    omega
  have hoffU1 : offF (U + 1) ≤ offF N := offF_mono hsrc.offs N le_rfl (U + 1) hlt
  have hoffU : offF U ≤ offF N := offF_mono hsrc.offs N le_rfl U (le_of_lt hlt)
  have hDN : D < N := ncard_neighborSet_lt F _
  have haoUB : (σ.arrs ao).getD U 0 < B := by omega
  have haoU1B : (σ.arrs ao).getD (U + 1) 0 < B := by omega
  have hsubB : (σ.arrs ao).getD (U + 1) 0 - (σ.arrs ao).getD U 0 < B := by omega
  -- the inner loop
  have hinner : Spec B (TIn ao aj mt tp F offF A0 J0 U D)
      (.while (.lt (.var "bk.t") (.var "bk.m")) (transBody ao aj mt tp))
      (fun _ τ => TIn ao aj mt tp F offF A0 J0 U D τ ∧ τ.vars "bk.t" = D)
      (27 * D + 4) := by
    refine Spec.forRange "bk.t" "bk.m" (TIn ao aj mt tp F offF A0 J0 U D) D 23
      (27 * D + 4) (fun τ hτ => ?_) (fun τ hτ => ?_) (fun τ hτ => hτ.2.2.1)
      (fun τ hτ => hτ.2.2.2.1)
      (transBody_spec hma hmj hmt hta htj hsrc hB hlt hD) (fun _ h => h)
      (fun τ hτ => ?_)
    · have := hτ.2.2.2.1; omega
    · have := hτ.2.2.1; omega
    · have := hτ.2.2.2.1
      have : (23 + 4) * (D - τ.vars "bk.t") ≤ 27 * D :=
        le_of_eq_of_le (by ring) (Nat.mul_le_mul_left 27 (Nat.sub_le _ _))
      omega
  run_vcg [hinner]
  · -- the postcondition
    rename_i hp
    obtain ⟨⟨hn', hu', hm', htle', hao', haj', hmtlen', htplen', hrow'⟩, ht'⟩ := hp
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [vars_setVar, arrs_setVar, String.reduceEq, reduceIte]; exact hn'
    · simp only [vars_setVar, eq_self_iff_true, if_true]; omega
    · simp only [arrs_setVar]; exact hao'
    · simp only [arrs_setVar]; exact haj'
    · simp only [arrs_setVar]; exact hmtlen'
    · simp only [arrs_setVar]; exact htplen'
    · intro z
      simp only [vars_setVar, eq_self_iff_true, if_true]
      rw [mRow_setVar, hrow' z, ht', hD, hsrc.hitL_full ⟨U, hlt⟩ z, ← rowUpTo_succ, hu']
    · simp only [vars_setVar, eq_self_iff_true, if_true]; omega
  · -- the inner loop's precondition
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [vars_setVar, arrs_setVar, String.reduceEq, reduceIte]; exact hn
    · simp only [vars_setVar, String.reduceEq, reduceIte, ← hU]
    · simp only [vars_setVar, String.reduceEq, reduceIte, eq_self_iff_true, if_true,
        ← hU, haoU, haoU1]
      exact hDeq
    · simp only [vars_setVar, eq_self_iff_true, if_true]
      exact Nat.zero_le _
    · simp only [arrs_setVar]; exact hao
    · simp only [arrs_setVar]; exact haj
    · simp only [arrs_setVar]; exact hmtlen
    · simp only [arrs_setVar]; exact htplen
    · intro z
      simp only [vars_setVar, eq_self_iff_true, if_true]
      rw [mRow_setVar, mRow_setVar, hrow z]
      simp
  · rename_i hp
    have h1 := hp.1.2.1
    omega
  · rename_i hp
    have h1 := hp.1.2.1
    omega
set_option maxHeartbeats 1000000 in
/-- **The entry transpose, at `27·m + 22·N + 6`.** Every row of `mt` is
then the ascending enumeration of that vertex's neighbourhood — a
function of `F` alone, which is what the replay of the buckets needs
and what `DelAdjSt` does not provide (`not_sortedAdjSt_of_delAdjSt`).
The fill cursors are left in `tp`, holding the degrees. -/
theorem transCom_spec {ao aj mt tp : String}
    (hma : mt ≠ ao) (hmj : mt ≠ aj) (hmt : mt ≠ tp) (hta : tp ≠ ao) (htj : tp ≠ aj)
    {B N : ℕ} {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ} {A0 J0 : List ℕ}
    (hsrc : TSrc F offF A0 J0) (hB : N + N * N + 1 < B) :
    Spec B
      (fun σ => σ.vars "bk.n" = N ∧ σ.arrs ao = A0 ∧ σ.arrs aj = J0 ∧
        offF N ≤ (σ.arrs mt).length ∧ N ≤ (σ.arrs tp).length ∧
        ∀ z, z < N → (σ.arrs tp).getD z 0 = 0)
      (transCom ao aj mt tp)
      (fun _ σ' => σ'.vars "bk.n" = N ∧ σ'.arrs ao = A0 ∧ σ'.arrs aj = J0 ∧
        offF N ≤ (σ'.arrs mt).length ∧ N ≤ (σ'.arrs tp).length ∧
        (∀ z : Fin N, (σ'.arrs tp).getD (z : ℕ) 0 = (F.neighborSet z).ncard) ∧
        (∀ z : Fin N, (List.range ((F.neighborSet z).ncard)).map
          (fun s => (σ'.arrs mt).getD (offF (z : ℕ) + s) 0) = rowList F z))
      (27 * slotCount F + 22 * N + 6) := by
  classical
  have hslot : offF N = slotCount F := offF_eq_slotCount hsrc.off0 hsrc.offs
  have hsq : offF N ≤ N * N := hsrc.offN_le_sq
  intro σ hσ
  obtain ⟨hn, hao, haj, hmtlen, htplen, htp0⟩ := hσ
  have hrun1 : Run B (.assign "bk.u" (.lit 0)) σ (σ.setVar "bk.u" 0) 2 :=
    (Run.assign (v := 0) (evalB_lit (by omega))).mono (by simp)
  have hcond : ∀ τ : Env, TOut ao aj mt tp F offF A0 J0 τ →
      (Cond.lt (.var "bk.u") (.var "bk.n")).evalB B τ
        = some (decide (τ.vars "bk.u" < τ.vars "bk.n")) := by
    intro τ hτ
    obtain ⟨hn', hule, -, -, -, -, -⟩ := hτ
    refine evalB_condLt (evalB_var ?_) (evalB_var ?_)
    · omega
    · omega
  have hloop : Spec B (TOut ao aj mt tp F offF A0 J0)
      (.while (.lt (.var "bk.u") (.var "bk.n")) (transOuterBody ao aj mt tp))
      (fun _ τ => TOut ao aj mt tp F offF A0 J0 τ ∧
        (Cond.lt (.var "bk.u") (.var "bk.n")).evalB B τ = some false)
      (27 * offF N + 22 * N + 4) := by
    refine Spec.while_potential (TOut ao aj mt tp F offF A0 J0)
      (fun τ => 27 * (offF N - offF (τ.vars "bk.u")) + 22 * (N - τ.vars "bk.u"))
      (fun τ hτ => ⟨_, hcond τ hτ⟩) (fun τ hτ hv => ?_) (fun _ h => h) (fun τ hτ => ?_)
    · have hlt : τ.vars "bk.u" < N := by
        rw [hcond τ hτ] at hv
        have := hτ.1
        simpa [this] using hv
      obtain ⟨τ', hrun, hI', hu'⟩ := transOuterBody_run hma hmj hmt hta htj hsrc hB hτ hlt
      refine ⟨τ', _, hrun, hI', ?_⟩
      have h1 : offF (τ.vars "bk.u") ≤ offF (τ.vars "bk.u" + 1) :=
        offF_mono hsrc.offs (τ.vars "bk.u" + 1) hlt (τ.vars "bk.u") (by omega)
      have h2 : offF (τ.vars "bk.u" + 1) ≤ offF N :=
        offF_mono hsrc.offs N le_rfl (τ.vars "bk.u" + 1) hlt
      have h3 : offF N ≤ N * N := hsq
      have hsz : (Cond.lt (Expr.var "bk.u") (Expr.var "bk.n")).size = 3 := by simp
      simp only [hsz, hu']
      omega
    · obtain ⟨-, hule, -, -, -, -, hrow⟩ := hτ
      have hsz : (Cond.lt (Expr.var "bk.u") (Expr.var "bk.n")).size = 3 := by simp
      simp only [hsz]
      have h1 : 27 * (offF N - offF (τ.vars "bk.u")) ≤ 27 * offF N :=
        Nat.mul_le_mul_left 27 (Nat.sub_le _ _)
      have h2 : 22 * (N - τ.vars "bk.u") ≤ 22 * N :=
        Nat.mul_le_mul_left 22 (Nat.sub_le _ _)
      omega
  have hinit : TOut ao aj mt tp F offF A0 J0 (σ.setVar "bk.u" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [vars_setVar, String.reduceEq, reduceIte]; exact hn
    · simp only [vars_setVar, eq_self_iff_true, if_true]; exact Nat.zero_le _
    · simp only [arrs_setVar]; exact hao
    · simp only [arrs_setVar]; exact haj
    · simp only [arrs_setVar]; exact hmtlen
    · simp only [arrs_setVar]; exact htplen
    · intro z
      simp only [vars_setVar, eq_self_iff_true, if_true]
      rw [mRow_setVar, mRow, htp0 (z : ℕ) z.isLt, rowUpTo_zero]
      simp
  obtain ⟨τ, hrun2, hI, hfalse⟩ := hloop.run hinit
  obtain ⟨hn', hule, hao', haj', hmtlen', htplen', hrow'⟩ := hI
  have huN : τ.vars "bk.u" = N := by
    rw [hcond τ ⟨hn', hule, hao', haj', hmtlen', htplen', hrow'⟩] at hfalse
    have : ¬ (τ.vars "bk.u" < τ.vars "bk.n") := by simpa using hfalse
    omega
  have hrows : ∀ z : Fin N, mRow mt tp offF τ (z : ℕ) = rowList F z := by
    intro z
    rw [hrow' z, huN, rowUpTo_full]
  refine ⟨τ, ?_, hn', hao', haj', hmtlen', htplen', ?_, ?_⟩
  · refine (hrun1.seq hrun2).mono ?_
    rw [hslot] at *
    omega
  · intro z
    have := hrows z
    rw [← mRow_length (mt := mt) (tp := tp) (offF := offF) (σ := τ) (z := (z : ℕ)),
      this, rowList_length]
  · intro z
    have hlen : (τ.arrs tp).getD (z : ℕ) 0 = (F.neighborSet z).ncard := by
      have := hrows z
      rw [← mRow_length (mt := mt) (tp := tp) (offF := offF) (σ := τ) (z := (z : ℕ)),
        this, rowList_length]
    rw [← hlen, ← mRow]
    exact hrows z

/-! ## §5 Zeroing, and the bucket build

The bucket tops start at zero, and the stacks are filled by one
downward scan of the carrier: pushing at the head with `u` descending
leaves each bucket **ascending**, which is exactly `bInit`'s
`(finRange N).filter`. -/

/-- Fill an array's first `N` cells with zero. -/
def bkZeroCom (a : String) : Com :=
  .seq (.assign "bk.i" (.lit 0))
    (.while (.lt (.var "bk.i") (.var "bk.n"))
      (.seq (.store a (.var "bk.i") (.lit 0))
        (.assign "bk.i" (.add (.var "bk.i") (.lit 1)))))

theorem bkZeroCom_spec {a : String} {B N : ℕ} (hNB : N < B) :
    Spec B (fun σ => σ.vars "bk.n" = N ∧ N ≤ (σ.arrs a).length)
      (bkZeroCom a)
      (fun _ σ' => σ'.vars "bk.n" = N ∧ N ≤ (σ'.arrs a).length ∧
        ∀ i, i < N → (σ'.arrs a).getD i 0 = 0)
      (11 * N + 6) := by
  refine (Spec.forRangeZero "bk.i" "bk.n"
    (fun σ => σ.vars "bk.n" = N ∧ N ≤ (σ.arrs a).length ∧ σ.vars "bk.i" ≤ N ∧
      ∀ i, i < σ.vars "bk.i" → (σ.arrs a).getD i 0 = 0) N 7 hNB
    (fun _ hI => hI.2.2.1) (fun _ hI => hI.1) ?_).conseq ?_ ?_ (by omega)
  · rintro σ ⟨⟨hnn, hlen, hix, hfill⟩, hlt⟩
    run_vcg
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa using hnn
    · simpa using hlen
    · simp only [vars_setVar, vars_setArr, eq_self_iff_true, if_true]; omega
    · simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr,
        eq_self_iff_true, if_true]
      intro i hi
      by_cases hie : i = σ.vars "bk.i"
      · rw [hie]; exact getD_set_self (by omega)
      · rw [getD_set_of_ne hie]; exact hfill i (by omega)
    · simp
  · rintro σ ⟨hnn, hlen⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hnn, hlen]
  · rintro σ σ' - ⟨⟨hnn, hlen, -, hfill⟩, hix⟩
    exact ⟨hnn, hlen, fun i hi => hfill i (by omega)⟩

/-- The part of the carrier from `I` up that a predicate keeps. -/
def tailFilter (q : ℕ → Bool) (I N : ℕ) : List ℕ := (List.range' I (N - I)).filter q

theorem tailFilter_self (q : ℕ → Bool) (N : ℕ) : tailFilter q N N = [] := by
  simp [tailFilter]

theorem tailFilter_zero (q : ℕ → Bool) (N : ℕ) :
    tailFilter q 0 N = (List.range N).filter q := by
  rw [tailFilter, List.range_eq_range']
  simp

theorem tailFilter_succ (q : ℕ → Bool) {I N : ℕ} (hI : I < N) :
    tailFilter q I N = (if q I = true then [I] else []) ++ tailFilter q (I + 1) N := by
  have h : N - I = (N - (I + 1)) + 1 := by omega
  rw [tailFilter, tailFilter, h, List.range'_succ, List.filter_cons]
  by_cases hq : q I = true <;> simp [hq]

theorem tailFilter_length_le (q : ℕ → Bool) (I N : ℕ) :
    (tailFilter q I N).length ≤ N - I := by
  rw [tailFilter]
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_range']

/-- Filtering commutes with a map along the predicate's factorisation. -/
theorem map_filter_comp {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.filter (fun a => p (f a))).map f = (l.map f).filter p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases h : p (f a) <;> simp [h, ih]

/-- A bucket of the replay, read as a list of indices — the shape the
machine's stack has. -/
noncomputable def bktV {N : ℕ} (st : BState N) (d : ℕ) : List ℕ := (st.bkt d).map Fin.val

/-- **The initial buckets, as index lists.** -/
theorem bktV_bInit {N : ℕ} (F : SimpleGraph (Fin N)) (q : ℕ → Bool) (d : ℕ)
    (hq : ∀ u : Fin N, q (u : ℕ) = decide ((nbrsIn F Finset.univ u).card = d)) :
    bktV (bInit F) d = (List.range N).filter q := by
  rw [bktV, bInit_bkt]
  rw [show (fun u : Fin N => decide ((nbrsIn F Finset.univ u).card = d))
      = (fun u : Fin N => q (u : ℕ)) from funext fun u => (hq u).symm]
  rw [map_filter_comp Fin.val q (List.finRange N), List.map_coe_finRange_eq_range]

/-- One turn of the bucket build: push the next vertex, downward, at the
head of its degree's stack. -/
def bkBuildBody (dg tp sk : String) : Com :=
  .seq (.assign "bk.i" (.sub (.var "bk.i") (.lit 1)))
  (.seq (.assign "bk.d" (.get dg (.var "bk.i")))
  (.seq (.store sk (.add (.mul (.var "bk.d") (.var "bk.n")) (.get tp (.var "bk.d")))
          (.var "bk.i"))
        (.store tp (.var "bk.d") (.add (.get tp (.var "bk.d")) (.lit 1)))))

/-- **The bucket build.** -/
def bkBuildCom (dg tp sk : String) : Com :=
  .seq (.assign "bk.i" (.var "bk.n"))
    (.while (.lt (.lit 0) (.var "bk.i")) (bkBuildBody dg tp sk))

/-- The build's invariant: each stack holds the vertices at or above the
counter of that degree, ascending. -/
def BInvB (dg tp sk : String) (N : ℕ) (σ : Env) : Prop :=
  σ.vars "bk.n" = N ∧ σ.vars "bk.i" ≤ N ∧
  N ≤ (σ.arrs dg).length ∧ N ≤ (σ.arrs tp).length ∧ N * N + N ≤ (σ.arrs sk).length ∧
  (∀ x, x < N → (σ.arrs dg).getD x 0 < N) ∧
  ∀ d, d < N → mLst tp sk N σ d
    = tailFilter (fun x => decide ((σ.arrs dg).getD x 0 = d)) (σ.vars "bk.i") N

/-- Two stacks never share a cell: distinct blocks of width `N`. -/
theorem block_ne {N d d' i t : ℕ} (hne : d' ≠ d) (hi : i < N) (ht : t < N) :
    d' * N + i ≠ d * N + t := by
  rcases lt_trichotomy d' d with h | h | h
  · have h1 : (d' + 1) * N ≤ d * N := Nat.mul_le_mul_right N h
    have h2 : (d' + 1) * N = d' * N + N := by ring
    omega
  · exact absurd h hne
  · have h1 : (d + 1) * N ≤ d' * N := Nat.mul_le_mul_right N h
    have h2 : (d + 1) * N = d * N + N := by ring
    omega

set_option maxHeartbeats 1000000 in
/-- **One turn of the bucket build.** -/
theorem bkBuildBody_spec {dg tp sk : String}
    (hts : tp ≠ sk) (hst : sk ≠ tp) (hdt : dg ≠ tp) (hds : dg ≠ sk)
    {B N : ℕ} (hB : N + N * N + 1 < B) :
    Spec B (fun σ => BInvB dg tp sk N σ ∧ 0 < σ.vars "bk.i")
      (bkBuildBody dg tp sk)
      (fun σ σ' => BInvB dg tp sk N σ' ∧ σ'.vars "bk.i" < σ.vars "bk.i") 21 := by
  classical
  rintro σ ⟨⟨hn, hile, hdglen, htplen, hsklen, hdgb, hbkt⟩, hipos⟩
  set I : ℕ := σ.vars "bk.i" with hI
  have hxN : I - 1 < N := by omega
  set d : ℕ := (σ.arrs dg).getD (I - 1) 0 with hd
  have hdN : d < N := hdgb _ hxN
  have htpb : ∀ e, e < N → (σ.arrs tp).getD e 0 ≤ N - I := by
    intro e he
    have h := hbkt e he
    have hlen : (σ.arrs tp).getD e 0 = (mLst tp sk N σ e).length := mLst_length.symm
    rw [hlen, h]
    exact tailFilter_length_le _ _ _
  have htpd : (σ.arrs tp).getD d 0 ≤ N - I := htpb d hdN
  have htpdN : (σ.arrs tp).getD d 0 < N := by omega
  have hidx : d * N + (σ.arrs tp).getD d 0 < N * N := by
    have h1 : (d + 1) * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
    have h2 : (d + 1) * N = d * N + N := by ring
    omega
  have hdB : d < B := by omega
  have hidxB : d * N + (σ.arrs tp).getD d 0 < B := by omega
  run_vcg
  all_goals simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr,
    String.reduceEq, reduceIte, if_neg hts, if_neg hst,
    if_neg hdt, if_neg hds, ← hI, ← hd, hn, List.length_set]
  all_goals try omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [vars_setVar, vars_setArr, String.reduceEq, reduceIte]; exact hn
  · simp only [vars_setVar, vars_setArr, String.reduceEq, reduceIte]; omega
  · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte,
      if_neg hdt, if_neg hds]
    exact hdglen
  · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte, if_neg hts,
      List.length_set]
    exact htplen
  · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte, if_neg hst,
      List.length_set]
    exact hsklen
  · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte,
      if_neg hdt, if_neg hds]
    exact hdgb
  · intro d' hd'
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr, String.reduceEq,
      reduceIte, if_neg hdt, if_neg hds]
    by_cases hdd : d' = d
    · rw [hdd]
      have hstep : mLst tp sk N
          ((((σ.setVar "bk.i" (I - 1)).setVar "bk.d" d).setArr sk
            (d * N + (σ.arrs tp).getD d 0) (I - 1)).setArr tp d
            ((σ.arrs tp).getD d 0 + 1)) d
          = (I - 1) :: mLst tp sk N σ d := by
        refine mLst_push ?_ ?_ ?_
        · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte, if_neg hts]
          exact getD_set_self (by omega)
        · intro i hi
          simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte, if_neg hst]
          exact getD_set_of_ne (by omega)
        · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte, if_neg hst]
          exact getD_set_self (by omega)
      rw [hstep, hbkt d hdN, tailFilter_succ _ (show I - 1 < N by omega),
        if_pos (by rw [← hd]; simp)]
      simp only [List.cons_append, List.nil_append]
      congr 2
      omega
    · have hstep : mLst tp sk N
          ((((σ.setVar "bk.i" (I - 1)).setVar "bk.d" d).setArr sk
            (d * N + (σ.arrs tp).getD d 0) (I - 1)).setArr tp d
            ((σ.arrs tp).getD d 0 + 1)) d'
          = mLst tp sk N σ d' := by
        refine mLst_frame ?_ ?_
        · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte, if_neg hts]
          exact getD_set_of_ne hdd
        · intro i hi
          simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte, if_neg hst]
          refine getD_set_of_ne (block_ne hdd ?_ htpdN)
          have := htpb d' hd'
          omega
      rw [hstep, hbkt d' hd', tailFilter_succ _ (show I - 1 < N by omega),
        if_neg (by rw [← hd]; simp; omega)]
      simp only [List.nil_append]
      congr 1
      omega
  · omega
set_option maxHeartbeats 1000000 in
/-- **The bucket build, at `25·N + 6`.** Pushing at the head with the
carrier scanned *downward* leaves every stack ascending — which is
`bInit`'s `(finRange N).filter` (`bktV_bInit`). -/
theorem bkBuildCom_spec {dg tp sk : String}
    (hts : tp ≠ sk) (hst : sk ≠ tp) (hdt : dg ≠ tp) (hds : dg ≠ sk)
    {B N : ℕ} (hB : N + N * N + 1 < B) :
    Spec B
      (fun σ => σ.vars "bk.n" = N ∧ N ≤ (σ.arrs dg).length ∧ N ≤ (σ.arrs tp).length ∧
        N * N + N ≤ (σ.arrs sk).length ∧ (∀ x, x < N → (σ.arrs dg).getD x 0 < N) ∧
        (∀ d, d < N → (σ.arrs tp).getD d 0 = 0))
      (bkBuildCom dg tp sk)
      (fun _ σ' => BInvB dg tp sk N σ' ∧ σ'.vars "bk.i" = 0)
      (25 * N + 6) := by
  classical
  intro σ hσ
  obtain ⟨hn, hdglen, htplen, hsklen, hdgb, htp0⟩ := hσ
  have hNB : N < B := by omega
  have hrun1 : Run B (.assign "bk.i" (.var "bk.n")) σ (σ.setVar "bk.i" N) 2 := by
    refine (Run.assign (v := N) ?_).mono (by simp)
    rw [← hn]
    exact evalB_var (by omega)
  have hcond : ∀ τ : Env, BInvB dg tp sk N τ →
      (Cond.lt (.lit 0) (.var "bk.i")).evalB B τ = some (decide (0 < τ.vars "bk.i")) := by
    intro τ hτ
    refine evalB_condLt (evalB_lit ?_) (evalB_var ?_)
    · omega
    · have := hτ.2.1; omega
  have hloop : Spec B (BInvB dg tp sk N)
      (.while (.lt (.lit 0) (.var "bk.i")) (bkBuildBody dg tp sk))
      (fun _ τ => BInvB dg tp sk N τ ∧
        (Cond.lt (.lit 0) (.var "bk.i")).evalB B τ = some false)
      (25 * N + 4) := by
    refine Spec.while_count (BInvB dg tp sk N) (fun τ => τ.vars "bk.i") 21
      (fun τ hτ => ⟨_, hcond τ hτ⟩)
      ((bkBuildBody_spec hts hst hdt hds hB).pre ?_) (fun _ h => h) (fun τ hτ => ?_)
    · rintro τ ⟨hτ, htrue⟩
      refine ⟨hτ, ?_⟩
      rw [hcond τ hτ] at htrue
      simpa using htrue
    · have hsz : (Cond.lt (Expr.lit 0) (Expr.var "bk.i")).size = 3 := by simp
      have h1 := hτ.2.1
      simp only [hsz]
      have h2 : (1 + 3 + 21) * τ.vars "bk.i" ≤ (1 + 3 + 21) * N :=
        Nat.mul_le_mul_left _ h1
      omega
  have hinit : BInvB dg tp sk N (σ.setVar "bk.i" N) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [vars_setVar, String.reduceEq, reduceIte]; exact hn
    · simp only [vars_setVar, String.reduceEq, reduceIte]; exact le_rfl
    · simp only [arrs_setVar]; exact hdglen
    · simp only [arrs_setVar]; exact htplen
    · simp only [arrs_setVar]; exact hsklen
    · simp only [arrs_setVar]; exact hdgb
    · intro d hd
      simp only [vars_setVar, String.reduceEq, reduceIte]
      rw [tailFilter_self, mLst, arrs_setVar, htp0 d hd]
      simp
  obtain ⟨τ, hrun2, hI, hfalse⟩ := hloop.run hinit
  refine ⟨τ, (hrun1.seq hrun2).mono (by omega), hI, ?_⟩
  rw [hcond τ hI] at hfalse
  have : ¬ (0 < τ.vars "bk.i") := by simpa using hfalse
  omega

/-! ## §6 The round

The machine state a round works in: the sorted rows in `mt`, the ranks
in `ra` (`N` marks a live vertex), the *current* degrees in `dg`, and
the bucket stacks in `tp`/`sk`, refining the replay `bRun F k` up to
stale cells. -/

open Lax3Proofs.CoverRoutine (selRank selPerm selChain selOrderingRoutine)

/-- **The round state.** Every clause is at the replay's `k`-th state;
the stacks refine it *after* the staleness filter, which is what lazy
deletion buys. `bk.c`, `bk.f`, `bk.v` are deliberately not pinned —
they move inside a round. -/
structure RSt (ao dg mt ra tp sk : String) {N : ℕ} (F : SimpleGraph (Fin N))
    (offF : ℕ → ℕ) (k : ℕ) (σ : Env) : Prop where
  /-- The carrier size. -/
  nn : σ.vars "bk.n" = N
  /-- The countdown: `bk.r` is the number of live vertices. -/
  rr : σ.vars "bk.r" = N - k
  /-- The offset region is allocated. -/
  aolen : N + 1 ≤ (σ.arrs ao).length
  /-- The offset region holds the offsets. -/
  aoval : ∀ i, i ≤ N → (σ.arrs ao).getD i 0 = offF i
  /-- The row region is allocated. -/
  mtlen : offF N ≤ (σ.arrs mt).length
  /-- The rank region is allocated. -/
  ralen : N ≤ (σ.arrs ra).length
  /-- The degree region is allocated. -/
  dglen : N ≤ (σ.arrs dg).length
  /-- The bucket tops are allocated. -/
  tplen : N ≤ (σ.arrs tp).length
  /-- The bucket cells are allocated. -/
  sklen : N * N + N ≤ (σ.arrs sk).length
  /-- The rows are the sorted rows of `F` — never written after the
  entry transpose, so a function of `F` for the whole run. -/
  rows : ∀ z : Fin N, (List.range ((F.neighborSet z).ncard)).map
    (fun s => (σ.arrs mt).getD (offF (z : ℕ) + s) 0) = rowList F z
  /-- A live vertex still holds the sentinel. -/
  live : ∀ x : Fin N, x ∈ (bRun F k).live → (σ.arrs ra).getD (x : ℕ) 0 = N
  /-- A peeled vertex holds its rank. -/
  dead : ∀ x : Fin N, x ∉ (bRun F k).live →
    (σ.arrs ra).getD (x : ℕ) 0 = selRank (bucketSel N) F x
  /-- `dg` holds the *current* degree of a live vertex. -/
  deg : ∀ x : Fin N, x ∈ (bRun F k).live →
    (σ.arrs dg).getD (x : ℕ) 0 = (nbrsIn F (bRun F k).live x).card
  /-- Every degree cell is below the carrier size. -/
  degb : ∀ x, x < N → (σ.arrs dg).getD x 0 < N
  /-- **The refinement**: a stack, with its stale cells dropped, is the
  replay's bucket. -/
  bkts : ∀ d, d < N → (mLst tp sk N σ d).filter (mOK ra dg N σ d) = bktV (bRun F k) d
  /-- A stack holds vertices whose degree has already reached its
  level — the clause that makes a stale cell stay stale. -/
  elts : ∀ d, d < N → ∀ x ∈ mLst tp sk N σ d, x < N ∧ (σ.arrs dg).getD x 0 ≤ d
  /-- A vertex is pushed into a given bucket at most once. -/
  nodup : ∀ d, d < N → (mLst tp sk N σ d).Nodup
  /-- The tops are inside the block. -/
  tpb : ∀ d, d < N → (σ.arrs tp).getD d 0 ≤ N

/-- The round state reads five arrays and two scalars, so assigning any
other scalar preserves it. -/
theorem RSt.setVar {ao dg mt ra tp sk : String} {N : ℕ} {F : SimpleGraph (Fin N)}
    {offF : ℕ → ℕ} {k : ℕ} {σ : Env} (h : RSt ao dg mt ra tp sk F offF k σ)
    {x : String} (h1 : x ≠ "bk.n") (h2 : x ≠ "bk.r") (v : ℕ) :
    RSt ao dg mt ra tp sk F offF k (σ.setVar x v) := by
  refine ⟨?_, ?_, h.aolen, h.aoval, h.mtlen, h.ralen, h.dglen, h.tplen, h.sklen,
    h.rows, h.live, h.dead, h.deg, h.degb, h.bkts, h.elts, h.nodup, h.tpb⟩
  · simp only [vars_setVar, if_neg (Ne.symm h1)]; exact h.nn
  · simp only [vars_setVar, if_neg (Ne.symm h2)]; exact h.rr

/-- **A stack is short.** Its entries are distinct indices, so it never
outgrows the carrier; and if some index is missing it has room for one
more — which is what a push needs. -/
theorem tp_lt_of_nodup {tp sk : String} {N : ℕ} {σ : Env} {d : ℕ}
    (hnd : (mLst tp sk N σ d).Nodup) (hlt : ∀ x ∈ mLst tp sk N σ d, x < N)
    {u : ℕ} (hu : u < N) (hnot : u ∉ mLst tp sk N σ d) :
    (σ.arrs tp).getD d 0 < N := by
  classical
  have hsub : (mLst tp sk N σ d).toFinset ⊆ (Finset.range N).erase u := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_erase.mpr ⟨fun hc => hnot (hc ▸ hx), Finset.mem_range.mpr (hlt x hx)⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_erase_of_mem
    (Finset.mem_range.mpr hu), Finset.card_range] at hcard
  have hlen : (mLst tp sk N σ d).length = (σ.arrs tp).getD d 0 := mLst_length
  omega

theorem RSt.tp_lt {ao dg mt ra tp sk : String} {N : ℕ} {F : SimpleGraph (Fin N)}
    {offF : ℕ → ℕ} {k : ℕ} {σ : Env} (h : RSt ao dg mt ra tp sk F offF k σ)
    {d : ℕ} (hd : d < N) {u : ℕ} (hu : u < N) (hnot : u ∉ mLst tp sk N σ d) :
    (σ.arrs tp).getD d 0 < N :=
  tp_lt_of_nodup (h.nodup d hd) (fun x hx => (h.elts d hd x hx).1) hu hnot

/-! ### The cell count

The fourth potential term of `peelLoop_linear_bucket_lazy` counts the
cells in the stacks. It is a function of the tops alone. -/

/-- The number of cells in the stacks. -/
def cellCount (tp : String) (N : ℕ) (σ : Env) : ℕ :=
  ∑ d ∈ Finset.range N, (σ.arrs tp).getD d 0

theorem sum_range_set_succ {N : ℕ} {l : List ℕ} {d₀ : ℕ} (hd : d₀ < N)
    (hlen : d₀ < l.length) :
    ∑ d ∈ Finset.range N, (l.set d₀ (l.getD d₀ 0 + 1)).getD d 0
      = (∑ d ∈ Finset.range N, l.getD d 0) + 1 := by
  classical
  have hmem : d₀ ∈ Finset.range N := Finset.mem_range.mpr hd
  have h1 := Finset.add_sum_erase (Finset.range N)
    (fun d => (l.set d₀ (l.getD d₀ 0 + 1)).getD d 0) hmem
  have h2 := Finset.add_sum_erase (Finset.range N) (fun d => l.getD d 0) hmem
  simp only [] at h1 h2
  have h3 : ∑ d ∈ (Finset.range N).erase d₀, (l.set d₀ (l.getD d₀ 0 + 1)).getD d 0
      = ∑ d ∈ (Finset.range N).erase d₀, l.getD d 0 :=
    Finset.sum_congr rfl fun d hd' => getD_set_of_ne (Finset.ne_of_mem_erase hd')
  rw [h3, getD_set_self hlen] at h1
  omega

theorem sum_range_set_pred {N : ℕ} {l : List ℕ} {d₀ : ℕ} (hd : d₀ < N)
    (hlen : d₀ < l.length) :
    (∑ d ∈ Finset.range N, (l.set d₀ (l.getD d₀ 0 - 1)).getD d 0) + l.getD d₀ 0
      = (∑ d ∈ Finset.range N, l.getD d 0) + (l.getD d₀ 0 - 1) := by
  classical
  have hmem : d₀ ∈ Finset.range N := Finset.mem_range.mpr hd
  have h1 := Finset.add_sum_erase (Finset.range N)
    (fun d => (l.set d₀ (l.getD d₀ 0 - 1)).getD d 0) hmem
  have h2 := Finset.add_sum_erase (Finset.range N) (fun d => l.getD d 0) hmem
  simp only [] at h1 h2
  have h3 : ∑ d ∈ (Finset.range N).erase d₀, (l.set d₀ (l.getD d₀ 0 - 1)).getD d 0
      = ∑ d ∈ (Finset.range N).erase d₀, l.getD d 0 :=
    Finset.sum_congr rfl fun d hd' => getD_set_of_ne (Finset.ne_of_mem_erase hd')
  rw [h3, getD_set_self hlen] at h1
  omega
theorem mOK_of_arrs {ra dg : String} {N : ℕ} {σ σ' : Env}
    (hra : σ'.arrs ra = σ.arrs ra) (hdg : σ'.arrs dg = σ.arrs dg) (d x : ℕ) :
    mOK ra dg N σ' d x = mOK ra dg N σ d x := by
  rw [mOK, mOK, mKey, mKey, hra, hdg]

theorem mOK_fun_eq {ra dg : String} {N : ℕ} {σ σ' : Env}
    (hra : σ'.arrs ra = σ.arrs ra) (hdg : σ'.arrs dg = σ.arrs dg) (d : ℕ) :
    mOK ra dg N σ' d = mOK ra dg N σ d := funext fun x => mOK_of_arrs hra hdg d x

/-- Reading the head of a bucket back through the index map. -/
theorem bktV_head {N : ℕ} {st : BState N} {d x : ℕ} {l : List ℕ}
    (h : bktV st d = x :: l) : ∃ v : Fin N, (v : ℕ) = x ∧ (st.bkt d).head? = some v := by
  cases hb : st.bkt d with
  | nil => rw [bktV, hb] at h; simp at h
  | cons a t =>
      rw [bktV, hb] at h
      simp only [List.map_cons, List.cons.injEq] at h
      exact ⟨a, h.1, by simp [hb]⟩

theorem bktV_eq_nil {N : ℕ} {st : BState N} {d : ℕ} (h : bktV st d = []) :
    st.bkt d = [] := by
  rwa [bktV, List.map_eq_nil_iff] at h

set_option maxHeartbeats 1000000 in
/-- **Popping a stale cell preserves the round state.** Its head fails
the staleness test, so dropping it changes no filtered stack — this is
the whole content of lazy deletion. -/
theorem RSt.pop {ao dg mt ra tp sk : String} {N : ℕ} {F : SimpleGraph (Fin N)}
    {offF : ℕ → ℕ} {k : ℕ} {σ σ' : Env} (h : RSt ao dg mt ra tp sk F offF k σ)
    (hvars : σ'.vars = σ.vars)
    (hao' : σ'.arrs ao = σ.arrs ao) (hmt' : σ'.arrs mt = σ.arrs mt)
    (hra' : σ'.arrs ra = σ.arrs ra) (hdg' : σ'.arrs dg = σ.arrs dg)
    (hsk' : σ'.arrs sk = σ.arrs sk)
    {c : ℕ} (hc : c < N)
    (htp' : σ'.arrs tp = (σ.arrs tp).set c ((σ.arrs tp).getD c 0 - 1))
    {x : ℕ} {l : List ℕ} (hlst : mLst tp sk N σ c = x :: l)
    (hstale : mOK ra dg N σ c x = false) :
    RSt ao dg mt ra tp sk F offF k σ' := by
  classical
  have hpos : 0 < (σ.arrs tp).getD c 0 := by
    have hl : (mLst tp sk N σ c).length = (σ.arrs tp).getD c 0 := mLst_length
    rw [hlst, List.length_cons] at hl
    omega
  have hclen : c < (σ.arrs tp).length := lt_of_lt_of_le hc h.tplen
  have htpc : (σ'.arrs tp).getD c 0 = (σ.arrs tp).getD c 0 - 1 := by
    rw [htp']; exact getD_set_self hclen
  have htpne : ∀ d, d ≠ c → (σ'.arrs tp).getD d 0 = (σ.arrs tp).getD d 0 := by
    intro d hd
    rw [htp']; exact getD_set_of_ne hd
  have hmc : mLst tp sk N σ' c = l := by
    refine mLst_pop hlst (by omega) ?_
    intro i _
    rw [hsk']
  have hmne : ∀ d, d ≠ c → mLst tp sk N σ' d = mLst tp sk N σ d := by
    intro d hd
    exact mLst_frame (htpne d hd) (fun i _ => by rw [hsk'])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvars]; exact h.nn
  · rw [hvars]; exact h.rr
  · rw [hao']; exact h.aolen
  · rw [hao']; exact h.aoval
  · rw [hmt']; exact h.mtlen
  · rw [hra']; exact h.ralen
  · rw [hdg']; exact h.dglen
  · rw [htp', List.length_set]; exact h.tplen
  · rw [hsk']; exact h.sklen
  · rw [hmt']; exact h.rows
  · rw [hra']; exact h.live
  · rw [hra']; exact h.dead
  · rw [hdg']; exact h.deg
  · rw [hdg']; exact h.degb
  · intro d hd
    rw [mOK_fun_eq hra' hdg' d]
    by_cases hdc : d = c
    · subst hdc
      rw [hmc, ← h.bkts d hd, hlst,
        List.filter_cons_of_neg (by rw [hstale]; exact Bool.false_ne_true)]
    · rw [hmne d hdc]; exact h.bkts d hd
  · intro d hd y hy
    rw [hdg']
    by_cases hdc : d = c
    · subst hdc
      rw [hmc] at hy
      exact h.elts d hd y (by rw [hlst]; exact List.mem_cons_of_mem _ hy)
    · rw [hmne d hdc] at hy
      exact h.elts d hd y hy
  · intro d hd
    by_cases hdc : d = c
    · subst hdc
      rw [hmc]
      have hnd := h.nodup d hd
      rw [hlst] at hnd
      exact hnd.of_cons
    · rw [hmne d hdc]; exact h.nodup d hd
  · intro d hd
    by_cases hdc : d = c
    · subst hdc; rw [htpc]; have := h.tpb d hd; omega
    · rw [htpne d hdc]; exact h.tpb d hd
/-- The head of a non-empty stack is its top cell. -/
theorem mLst_cons {tp sk : String} {N : ℕ} {σ : Env} {d : ℕ}
    (hpos : 0 < (σ.arrs tp).getD d 0) :
    ∃ l, mLst tp sk N σ d
      = (σ.arrs sk).getD (d * N + ((σ.arrs tp).getD d 0 - 1)) 0 :: l := by
  obtain ⟨m, hm⟩ : ∃ m, (σ.arrs tp).getD d 0 = m + 1 :=
    ⟨(σ.arrs tp).getD d 0 - 1, by omega⟩
  refine ⟨((List.range m).map (fun i => (σ.arrs sk).getD (d * N + i) 0)).reverse, ?_⟩
  rw [mLst, hm, List.range_succ, List.map_append, List.reverse_append]
  simp

/-- The scan's invariant: the cursor has not passed the minimum-degree
bucket, and once the flag is down it stands *at* it with the replay's
pop in `bk.v`. -/
def ScanInv (ao dg mt ra tp sk : String) {N : ℕ} (F : SimpleGraph (Fin N))
    (offF : ℕ → ℕ) (k : ℕ) (σ : Env) : Prop :=
  RSt ao dg mt ra tp sk F offF k σ ∧ σ.vars "bk.c" ≤ bLevel (bRun F k) ∧
  (σ.vars "bk.f" = 1 ∨
    (σ.vars "bk.f" = 0 ∧ σ.vars "bk.c" = bLevel (bRun F k) ∧
      ∃ v : Fin N, (v : ℕ) = σ.vars "bk.v" ∧ bPop (bRun F k) = some v))

/-- The scan's potential: the cursor's remaining rise, the cells still
in the stacks, and one last turn. -/
noncomputable def scanPot (tp : String) {N : ℕ} (F : SimpleGraph (Fin N)) (k : ℕ)
    (σ : Env) : ℕ :=
  50 * (bLevel (bRun F k) - σ.vars "bk.c") + 50 * cellCount tp N σ
    + 50 * (if σ.vars "bk.f" = 1 then 1 else 0)

/-- One turn of the cursor scan: step over an empty bucket, drop a stale
cell, or stop. -/
def scanBody (ra dg tp sk : String) : Com :=
  .ite (.eq (.get tp (.var "bk.c")) (.lit 0))
    (.assign "bk.c" (.add (.var "bk.c") (.lit 1)))
    (.seq (.assign "bk.v" (.get sk (.add (.mul (.var "bk.c") (.var "bk.n"))
            (.sub (.get tp (.var "bk.c")) (.lit 1)))))
      (.ite (.eq (.add (.mul (.sub (.var "bk.n") (.get ra (.var "bk.v"))) (.var "bk.n"))
                (.get dg (.var "bk.v")))
              (.var "bk.c"))
        (.assign "bk.f" (.lit 0))
        (.store tp (.var "bk.c") (.sub (.get tp (.var "bk.c")) (.lit 1)))))

/-- **The cursor scan.** -/
def scanCom (ra dg tp sk : String) : Com :=
  .seq (.assign "bk.f" (.lit 1))
    (.while (.eq (.var "bk.f") (.lit 1)) (scanBody ra dg tp sk))


/-- Every rank cell is at most the sentinel. -/
theorem RSt.ra_le {ao dg mt ra tp sk : String} {N : ℕ} {F : SimpleGraph (Fin N)}
    {offF : ℕ → ℕ} {k : ℕ} {σ : Env} (h : RSt ao dg mt ra tp sk F offF k σ)
    (x : Fin N) : (σ.arrs ra).getD (x : ℕ) 0 ≤ N := by
  by_cases hx : x ∈ (bRun F k).live
  · rw [h.live x hx]
  · rw [h.dead x hx]
    exact le_of_lt (Lax3Proofs.CoverRoutine.selRank_lt _ F x)

set_option maxHeartbeats 1000000 in
/-- **One turn of the cursor scan.** -/
theorem scanBody_spec {ao dg mt ra tp sk : String}
    (hta : tp ≠ ao) (htm : tp ≠ mt) (htr : tp ≠ ra) (htd : tp ≠ dg) (hts : tp ≠ sk)
    {B N : ℕ} {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ} (hB : N + N * N + 1 < B)
    {k : ℕ} (hk : k < N) :
    Spec B (fun σ => ScanInv ao dg mt ra tp sk F offF k σ ∧ σ.vars "bk.f" = 1)
      (scanBody ra dg tp sk)
      (fun σ σ' => ScanInv ao dg mt ra tp sk F offF k σ' ∧
        scanPot tp F k σ' + 44 ≤ scanPot tp F k σ) 40 := by
  classical
  rintro σ ⟨⟨hR, hcle, -⟩, hf⟩
  have hne : (bRun F k).live.Nonempty := bRun_live_nonempty F hk
  have hlev : bLevel (bRun F k) = minDeg F (bRun F k).live hne :=
    bLevel_eq_minDeg (bRun_inv F k) hne
  have hlevN : bLevel (bRun F k) < N := by
    rw [hlev]
    refine lt_of_lt_of_le (minDeg_lt_card F hne) ?_
    simpa using Finset.card_le_univ (bRun F k).live
  have hcN : σ.vars "bk.c" < N := by omega
  have hclen : σ.vars "bk.c" < (σ.arrs tp).length := lt_of_lt_of_le hcN hR.tplen
  have htpb := hR.tpb (σ.vars "bk.c") hcN
  have hnn := hR.nn
  have hcB : σ.vars "bk.c" + 1 < B := by omega
  have htpB : (σ.arrs tp).getD (σ.vars "bk.c") 0 < B := by omega
  have htpsB : (σ.arrs tp).getD (σ.vars "bk.c") 0 - 1 < B := by omega
  have hidxM : σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1) < N * N := by
    rw [hnn]
    have h1 : (σ.vars "bk.c" + 1) * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
    have h2 : (σ.vars "bk.c" + 1) * N = σ.vars "bk.c" * N + N := by ring
    omega
  have hmulB : σ.vars "bk.c" * σ.vars "bk.n" < B := by omega
  have hidxB : σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1) < B := by omega
  have hidxlen : σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1) < (σ.arrs sk).length := by have := hR.sklen; omega
  -- the bucket at the minimum level is not empty
  obtain ⟨vp, hvp, hvpS, hvpdeg⟩ := bPop_spec (bRun_inv F k) hne
  have hbktne : (bRun F k).bkt (bLevel (bRun F k)) ≠ [] := by
    intro hc
    rw [bPop, hc] at hvp
    simp at hvp
  by_cases htz : (σ.arrs tp).getD (σ.vars "bk.c") 0 = 0
  · -- the bucket is empty: step the cursor
    have hml : mLst tp sk N σ (σ.vars "bk.c") = [] := by
      rw [mLst, htz]; simp
    have hbz : (bRun F k).bkt (σ.vars "bk.c") = [] := by
      refine bktV_eq_nil ?_
      rw [← hR.bkts _ hcN, hml]
      rfl
    have hclt : σ.vars "bk.c" < bLevel (bRun F k) := by
      rcases Nat.lt_or_ge (σ.vars "bk.c") (bLevel (bRun F k)) with h | h
      · exact h
      · exact absurd (by rw [show bLevel (bRun F k) = σ.vars "bk.c" by omega]; exact hbz)
          hbktne
    run_vcg
    all_goals try (exfalso; omega)
    refine ⟨⟨hR.setVar (by decide) (by decide) _, ?_, ?_⟩, ?_⟩
    · simp only [vars_setVar, eq_self_iff_true, if_true]; omega
    · left; simp only [vars_setVar, String.reduceEq, reduceIte]; exact hf
    · have hc1 : (σ.setVar "bk.c" (σ.vars "bk.c" + 1)).vars "bk.c" = σ.vars "bk.c" + 1 := rfl
      have hf1 : (σ.setVar "bk.c" (σ.vars "bk.c" + 1)).vars "bk.f" = σ.vars "bk.f" := rfl
      have hcc : cellCount tp N (σ.setVar "bk.c" (σ.vars "bk.c" + 1)) = cellCount tp N σ := rfl
      rw [scanPot, scanPot, hc1, hf1, hcc]
      omega
  · -- the bucket is not empty: read its top
    have hm : 0 < (σ.arrs tp).getD (σ.vars "bk.c") 0 := by omega
    obtain ⟨l, hlst⟩ := mLst_cons (tp := tp) (sk := sk) (N := N) (σ := σ)
      (d := σ.vars "bk.c") hm
    have hXeq : (σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0
        = (σ.arrs sk).getD (σ.vars "bk.c" * N + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0 := by
      rw [hnn]
    have hxmem : (σ.arrs sk).getD
        (σ.vars "bk.c" * N + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0
        ∈ mLst tp sk N σ (σ.vars "bk.c") := by
      rw [hlst]; exact List.mem_cons_self ..
    obtain ⟨hxN, hxdg⟩ := hR.elts _ hcN _ hxmem
    rw [← hXeq] at hxN hxdg hxmem hlst
    have hXB : (σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0 < B := by omega
    have hXlenra : (σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0 < (σ.arrs ra).length := by have := hR.ralen; omega
    have hXlendg : (σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0 < (σ.arrs dg).length := by have := hR.dglen; omega
    have hraX : (σ.arrs ra).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0 ≤ N := hR.ra_le ⟨(σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0, hxN⟩
    have hraXB : (σ.arrs ra).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0 < B := by omega
    have hdgXB : (σ.arrs dg).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0 < B := by omega
    have hsubB : σ.vars "bk.n" - (σ.arrs ra).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0 < B := by omega
    have hmul2 : (σ.vars "bk.n" - (σ.arrs ra).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0) * σ.vars "bk.n" ≤ N * N := by
      rw [hnn]
      exact Nat.mul_le_mul_right N (by omega)
    have hmul2B : (σ.vars "bk.n" - (σ.arrs ra).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0) * σ.vars "bk.n" < B := by omega
    have haddB : (σ.vars "bk.n" - (σ.arrs ra).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0) * σ.vars "bk.n"
        + (σ.arrs dg).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0 < B := by omega
    have hkey : mKey ra dg N σ ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)
        = (σ.vars "bk.n" - (σ.arrs ra).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0) * σ.vars "bk.n"
          + (σ.arrs dg).getD ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) 0 := by rw [mKey, hnn]
    run_vcg
    all_goals try (exfalso; omega)
    all_goals try simp only [vars_setVar, vars_setArr, arrs_setVar, String.reduceEq,
      reduceIte]
    all_goals try omega
    · -- the top is live business: stop
      rename_i hkeyc
      have hok : mOK ra dg N σ (σ.vars "bk.c") ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) = true := by
        rw [mOK, decide_eq_true_iff, hkey]
        simpa using hkeyc
      have hbv : bktV (bRun F k) (σ.vars "bk.c")
          = (σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0 :: (mLst tp sk N σ (σ.vars "bk.c")).tail.filter
              (mOK ra dg N σ (σ.vars "bk.c")) := by
        rw [← hR.bkts _ hcN, hlst, List.filter_cons_of_pos hok]
        simp
      have hbne : (bRun F k).bkt (σ.vars "bk.c") ≠ [] := by
        intro hc
        rw [bktV, hc] at hbv
        simp at hbv
      have hceq : σ.vars "bk.c" = bLevel (bRun F k) := by
        obtain ⟨u, hu⟩ : ∃ u : Fin N, u ∈ (bRun F k).bkt (σ.vars "bk.c") := by
          cases hcs : (bRun F k).bkt (σ.vars "bk.c") with
          | nil => exact absurd hcs hbne
          | cons a t => exact ⟨a, by simp⟩
        obtain ⟨huS, hud⟩ := ((bRun_inv F k).1 _ u).mp hu
        have := minDeg_le F hne huS
        rw [hlev]
        omega
      obtain ⟨v, hveq, hvpop⟩ := bktV_head hbv
      refine ⟨⟨(hR.setVar (by decide) (by decide) _).setVar (by decide) (by decide) _,
        ?_, ?_⟩, ?_⟩
      · simp only [vars_setVar, String.reduceEq, reduceIte]; omega
      · right
        refine ⟨rfl, by simp only [vars_setVar, String.reduceEq, reduceIte]; exact hceq,
          v, ?_, ?_⟩
        · simp only [vars_setVar, String.reduceEq, reduceIte]; exact hveq
        · rw [bPop, ← hceq]; exact hvpop
      · have hc1 : ((σ.setVar "bk.v" ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)).setVar "bk.f" 0).vars "bk.c"
            = σ.vars "bk.c" := rfl
        have hf1 : ((σ.setVar "bk.v" ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)).setVar "bk.f" 0).vars "bk.f" = 0 := rfl
        have hcc : cellCount tp N ((σ.setVar "bk.v" ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)).setVar "bk.f" 0)
            = cellCount tp N σ := rfl
        rw [scanPot, scanPot, hc1, hf1, hcc, hf, if_neg (by decide : ¬((0 : ℕ) = 1)),
          if_pos (rfl : (1 : ℕ) = 1)]
        omega
    · -- the top is stale: drop it
      rename_i hkeyc
      have hstale : mOK ra dg N σ (σ.vars "bk.c") ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0) = false := by
        rw [mOK, decide_eq_false_iff_not, hkey]
        simpa using hkeyc
      have hpop := (hR.setVar (x := "bk.v") (by decide) (by decide) ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)).pop
        (σ' := (σ.setVar "bk.v" ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)).setArr tp (σ.vars "bk.c")
          ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1))
        (by simp only [vars_setArr]) (by simp only [arrs_setArr, if_neg (Ne.symm hta)])
        (by simp only [arrs_setArr, if_neg (Ne.symm htm)])
        (by simp only [arrs_setArr, if_neg (Ne.symm htr)])
        (by simp only [arrs_setArr, if_neg (Ne.symm htd)])
        (by simp only [arrs_setArr, if_neg (Ne.symm hts)])
        hcN (by simp only [arrs_setArr, arrs_setVar, eq_self_iff_true, if_true])
        (l := l) hlst hstale
      refine ⟨⟨hpop, ?_, ?_⟩, ?_⟩
      · simp only [vars_setArr, vars_setVar, String.reduceEq, reduceIte]; omega
      · left; simp only [vars_setArr, vars_setVar, String.reduceEq, reduceIte]; exact hf
      · have hc1 : ((σ.setVar "bk.v" ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)).setArr tp (σ.vars "bk.c")
              ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)).vars "bk.c" = σ.vars "bk.c" := rfl
        have hf1 : ((σ.setVar "bk.v" ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)).setArr tp (σ.vars "bk.c")
              ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)).vars "bk.f" = σ.vars "bk.f" := rfl
        have hcc : cellCount tp N ((σ.setVar "bk.v" ((σ.arrs sk).getD (σ.vars "bk.c" * σ.vars "bk.n" + ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) 0)).setArr tp (σ.vars "bk.c")
              ((σ.arrs tp).getD (σ.vars "bk.c") 0 - 1)) + 1 = cellCount tp N σ := by
          rw [cellCount, cellCount]
          have hsp := sum_range_set_pred (l := σ.arrs tp) (d₀ := σ.vars "bk.c") hcN hclen
          simp only [arrs_setArr, arrs_setVar, eq_self_iff_true, if_true]
          omega
        rw [scanPot, scanPot, hc1, hf1]
        omega


set_option maxHeartbeats 1000000 in
/-- **The cursor scan.** It stops at the minimum-degree bucket
(`bLevel_eq_minDeg`) with the replay's pop in `bk.v`, at a cost `50` per
step of the cursor and `50` per stale cell it drops — the two terms the
lazy loop rule charges to the cursor's total rise and to the cell
count. -/
theorem scanCom_run {ao dg mt ra tp sk : String}
    (hta : tp ≠ ao) (htm : tp ≠ mt) (htr : tp ≠ ra) (htd : tp ≠ dg) (hts : tp ≠ sk)
    {B N : ℕ} {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ} (hB : N + N * N + 1 < B)
    {k : ℕ} (hk : k < N) {σ : Env}
    (hR : RSt ao dg mt ra tp sk F offF k σ)
    (hcle : σ.vars "bk.c" ≤ bLevel (bRun F k)) :
    ∃ (σ' : Env) (K : ℕ), Run B (scanCom ra dg tp sk) σ σ' K ∧
      RSt ao dg mt ra tp sk F offF k σ' ∧
      σ'.vars "bk.c" = bLevel (bRun F k) ∧
      (∃ v : Fin N, (v : ℕ) = σ'.vars "bk.v" ∧ bPop (bRun F k) = some v) ∧
      K + 50 * cellCount tp N σ'
        ≤ 50 * (bLevel (bRun F k) - σ.vars "bk.c") + 50 * cellCount tp N σ + 56 := by
  classical
  have hcond : ∀ τ : Env, ScanInv ao dg mt ra tp sk F offF k τ →
      (Cond.eq (.var "bk.f") (.lit 1)).evalB B τ = some (τ.vars "bk.f" == 1) := by
    intro τ hτ
    refine evalB_condEq (evalB_var ?_) (evalB_lit ?_)
    · rcases hτ.2.2 with h | ⟨h, -⟩ <;> omega
    · omega
  have hrun1 : Run B (.assign "bk.f" (.lit 1)) σ (σ.setVar "bk.f" 1) 2 :=
    (Run.assign (v := 1) (evalB_lit (by omega))).mono (by simp)
  have hI1 : ScanInv ao dg mt ra tp sk F offF k (σ.setVar "bk.f" 1) := by
    refine ⟨hR.setVar (by decide) (by decide) _, ?_, Or.inl rfl⟩
    simp only [vars_setVar, String.reduceEq, reduceIte]; exact hcle
  have hstep : ∀ τ : Env, ScanInv ao dg mt ra tp sk F offF k τ →
      (Cond.eq (.var "bk.f") (.lit 1)).evalB B τ = some true →
      ∃ (τ' : Env) (K : ℕ), Run B (scanBody ra dg tp sk) τ τ' K ∧
        ScanInv ao dg mt ra tp sk F offF k τ' ∧
        1 + (Cond.eq (Expr.var "bk.f") (Expr.lit 1)).size + K + scanPot tp F k τ'
          ≤ scanPot tp F k τ := by
    intro τ hτ hv
    have hf : τ.vars "bk.f" = 1 := by
      rw [hcond τ hτ] at hv
      simpa using hv
    obtain ⟨τ', hrun, hI'', hpot⟩ := (scanBody_spec hta htm htr htd hts hB hk).run ⟨hτ, hf⟩
    have hsz : (Cond.eq (Expr.var "bk.f") (Expr.lit 1)).size = 3 := by simp
    exact ⟨τ', 40, hrun, hI'', by rw [hsz]; omega⟩
  obtain ⟨σ', K, hrun2, hI', hfalse, hpay⟩ :=
    Run.while_potential (B := B) (ScanInv ao dg mt ra tp sk F offF k)
      (scanPot tp F k) (fun τ hτ => ⟨_, hcond τ hτ⟩) hstep hI1
  · obtain ⟨hR', hcle', hdisj⟩ := hI'
    have hf0 : σ'.vars "bk.f" ≠ 1 := by
      intro hc
      rw [hcond σ' ⟨hR', hcle', hdisj⟩, hc] at hfalse
      simp at hfalse
    obtain ⟨hzero, hceq, hv⟩ : σ'.vars "bk.f" = 0 ∧ σ'.vars "bk.c" = bLevel (bRun F k) ∧
        ∃ v : Fin N, (v : ℕ) = σ'.vars "bk.v" ∧ bPop (bRun F k) = some v := by
      rcases hdisj with h | h
      · exact absurd h hf0
      · exact h
    refine ⟨σ', 2 + K, (hrun1.seq hrun2).mono le_rfl, hR', hceq, hv, ?_⟩
    have hsz : (Cond.eq (Expr.var "bk.f") (Expr.lit 1)).size = 3 := by simp
    have hp1 : scanPot tp F k σ' = 50 * cellCount tp N σ' := by
      rw [scanPot, hceq, hzero]
      simp
    have hp2 : scanPot tp F k (σ.setVar "bk.f" 1)
        = 50 * (bLevel (bRun F k) - σ.vars "bk.c") + 50 * cellCount tp N σ + 50 := by
      have hc1 : (σ.setVar "bk.f" 1).vars "bk.c" = σ.vars "bk.c" := rfl
      have hcc : cellCount tp N (σ.setVar "bk.f" 1) = cellCount tp N σ := rfl
      rw [scanPot, hc1, hcc, show (σ.setVar "bk.f" 1).vars "bk.f" = 1 from rfl,
        if_pos (rfl : (1 : ℕ) = 1)]
    rw [hsz, hp1, hp2] at hpay
    omega

/-! ### The row walk

The round walks `v`'s **original** row, downward, pushing each live
neighbour into the bucket one below its current degree. Downward with a
head push leaves the new group ascending, which is exactly `bStep`'s
`(finRange N).filter`. -/

/-- What the walk has pushed into bucket `d` by the time its counter is
`t`: the live entries of the row's tail whose degree drops to `d`. -/
def wpushed (ra dg : String) (N : ℕ) (τ : Env) (R : List ℕ) (t d : ℕ) : List ℕ :=
  (R.drop t).filter
    (fun x => decide ((τ.arrs ra).getD x 0 = N ∧ (τ.arrs dg).getD x 0 = d + 1))

theorem wpushed_full {ra dg : String} {N : ℕ} {τ : Env} {R : List ℕ} {t d : ℕ}
    (ht : R.length ≤ t) : wpushed ra dg N τ R t d = [] := by
  rw [wpushed, List.drop_eq_nil_of_le ht]
  rfl

theorem wpushed_succ {ra dg : String} {N : ℕ} {τ : Env} {R : List ℕ} {t d : ℕ}
    (ht : t < R.length) :
    wpushed ra dg N τ R t d
      = (if (τ.arrs ra).getD (R.getD t 0) 0 = N ∧
            (τ.arrs dg).getD (R.getD t 0) 0 = d + 1 then [R.getD t 0] else [])
        ++ wpushed ra dg N τ R (t + 1) d := by
  have hd : R.drop t = R.getD t 0 :: R.drop (t + 1) := by
    rw [List.drop_eq_getElem_cons ht, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem ht]
    rfl
  rw [wpushed, wpushed, hd, List.filter_cons]
  by_cases h : (τ.arrs ra).getD (R.getD t 0) 0 = N ∧
      (τ.arrs dg).getD (R.getD t 0) 0 = d + 1
  · rw [if_pos (decide_eq_true h), if_pos h]; rfl
  · rw [if_neg (by rw [decide_eq_false h]; exact Bool.false_ne_true), if_neg h]; rfl

/-- **The walk's state**, relative to the state `τ` it started in: only
`dg`, `tp` and `sk` move, `dg` drops by one at each processed live
neighbour, and each stack has grown by exactly the group pushed so
far. -/
structure WSt (ao dg mt ra tp sk : String) (N : ℕ) (R : List ℕ) (D : ℕ) (τ σ : Env) :
    Prop where
  /-- The carrier size. -/
  nn : σ.vars "bk.n" = N
  /-- The counter is inside the row. -/
  tle : σ.vars "bk.t" ≤ D
  /-- The walked vertex. -/
  vv : σ.vars "bk.v" = τ.vars "bk.v"
  /-- The countdown. -/
  rr : σ.vars "bk.r" = τ.vars "bk.r"
  /-- The offsets are untouched. -/
  aoq : σ.arrs ao = τ.arrs ao
  /-- The rows are untouched. -/
  mtq : σ.arrs mt = τ.arrs mt
  /-- The ranks are untouched. -/
  raq : σ.arrs ra = τ.arrs ra
  /-- The degree region is allocated. -/
  dglen : N ≤ (σ.arrs dg).length
  /-- The bucket tops are allocated. -/
  tplen : N ≤ (σ.arrs tp).length
  /-- The bucket cells are allocated. -/
  sklen : N * N + N ≤ (σ.arrs sk).length
  /-- Each processed live neighbour has lost one from its degree. -/
  degq : ∀ x, x < N → (σ.arrs dg).getD x 0
    = (τ.arrs dg).getD x 0
      - (if x ∈ R.drop (σ.vars "bk.t") ∧ (τ.arrs ra).getD x 0 = N then 1 else 0)
  /-- Every degree cell is below the carrier size. -/
  degb : ∀ x, x < N → (σ.arrs dg).getD x 0 < N
  /-- Each stack has grown by its share of the pushed group. -/
  stk : ∀ d, d < N → mLst tp sk N σ d
    = wpushed ra dg N τ R (σ.vars "bk.t") d ++ mLst tp sk N τ d
  /-- A stack holds vertices whose degree has reached its level. -/
  elts : ∀ d, d < N → ∀ x ∈ mLst tp sk N σ d, x < N ∧ (σ.arrs dg).getD x 0 ≤ d
  /-- A vertex is pushed into a given bucket at most once. -/
  nodup : ∀ d, d < N → (mLst tp sk N σ d).Nodup
  /-- The tops are inside the block. -/
  tpb : ∀ d, d < N → (σ.arrs tp).getD d 0 ≤ N
  /-- The walk adds at most one cell per row slot. -/
  cnt : cellCount tp N σ + σ.vars "bk.t" ≤ cellCount tp N τ + D

/-- One turn of the row walk. -/
def walkBody (ao dg mt ra tp sk : String) : Com :=
  .seq (.assign "bk.t" (.sub (.var "bk.t") (.lit 1)))
  (.seq (.assign "bk.w" (.get mt (.add (.get ao (.var "bk.v")) (.var "bk.t"))))
    (.ite (.eq (.get ra (.var "bk.w")) (.var "bk.n"))
      (.seq (.assign "bk.d" (.sub (.get dg (.var "bk.w")) (.lit 1)))
      (.seq (.store dg (.var "bk.w") (.var "bk.d"))
      (.seq (.store sk (.add (.mul (.var "bk.d") (.var "bk.n")) (.get tp (.var "bk.d")))
              (.var "bk.w"))
            (.store tp (.var "bk.d") (.add (.get tp (.var "bk.d")) (.lit 1))))))
      .skip))

/-- **The row walk.** -/
def walkCom (ao dg mt ra tp sk : String) : Com :=
  .while (.lt (.lit 0) (.var "bk.t")) (walkBody ao dg mt ra tp sk)

/-- Prepending an entry the vertex is not equal to leaves the walk's
degree correction alone. -/
theorem if_mem_cons_eq {x w : ℕ} {l : List ℕ} {P : Prop} [Decidable P] (hxw : x ≠ w) :
    (if x ∈ w :: l ∧ P then 1 else 0) = (if x ∈ l ∧ P then (1 : ℕ) else 0) := by
  by_cases h : x ∈ l ∧ P
  · rw [if_pos ⟨List.mem_cons_of_mem _ h.1, h.2⟩, if_pos h]
  · rw [if_neg h,
      if_neg (by rintro ⟨h1, h2⟩; exact h ⟨(List.mem_cons.mp h1).resolve_left hxw, h2⟩)]

set_option maxHeartbeats 1000000 in
/-- **One turn of the row walk.** -/
theorem walkBody_spec {ao dg mt ra tp sk : String}
    (hda : dg ≠ ao) (hdm : dg ≠ mt) (hdr : dg ≠ ra) (hdt : dg ≠ tp) (hds : dg ≠ sk)
    (hsa : sk ≠ ao) (hsm : sk ≠ mt) (hsr : sk ≠ ra) (hst : sk ≠ tp) (hsd : sk ≠ dg)
    (hta : tp ≠ ao) (htm : tp ≠ mt) (htr : tp ≠ ra) (hts : tp ≠ sk)
    {B N : ℕ} (hB : N + N * N + 1 < B)
    {R : List ℕ} {D : ℕ} {τ : Env} {offv : ℕ}
    (hRlen : R.length = D) (hRnd : R.Nodup) (hRlt : ∀ x ∈ R, x < N) (hDN : D < N)
    (haov : (τ.arrs ao).getD (τ.vars "bk.v") 0 = offv)
    (hvlen : τ.vars "bk.v" < (τ.arrs ao).length)
    (hmtlen : offv + D ≤ (τ.arrs mt).length) (hoffB : offv + D < B)
    (hvN : τ.vars "bk.v" < N)
    (hrow : ∀ s, s < D → (τ.arrs mt).getD (offv + s) 0 = R.getD s 0)
    (hposd : ∀ x ∈ R, (τ.arrs ra).getD x 0 = N → 0 < (τ.arrs dg).getD x 0)
    (hralen : N ≤ (τ.arrs ra).length) (hraN : ∀ x, x < N → (τ.arrs ra).getD x 0 ≤ N) :
    Spec B (fun σ => WSt ao dg mt ra tp sk N R D τ σ ∧ 0 < σ.vars "bk.t")
      (walkBody ao dg mt ra tp sk)
      (fun σ σ' => WSt ao dg mt ra tp sk N R D τ σ' ∧ σ'.vars "bk.t" < σ.vars "bk.t")
      37 := by
  classical
  rintro σ ⟨hW, htpos⟩
  have hnn := hW.nn
  have htD : σ.vars "bk.t" ≤ D := hW.tle
  have ht1 : σ.vars "bk.t" - 1 < D := by omega
  have ht1R : σ.vars "bk.t" - 1 < R.length := by omega
  -- the row entry the turn reads
  have hwmem : R.getD (σ.vars "bk.t" - 1) 0 ∈ R := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1R]
    exact List.getElem_mem ht1R
  have hwN : R.getD (σ.vars "bk.t" - 1) 0 < N := hRlt _ hwmem
  have hdrop : R.drop (σ.vars "bk.t" - 1)
      = R.getD (σ.vars "bk.t" - 1) 0 :: R.drop (σ.vars "bk.t") := by
    rw [List.drop_eq_getElem_cons ht1R, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem ht1R, show σ.vars "bk.t" - 1 + 1 = σ.vars "bk.t" by omega]
    rfl
  have hwnot : R.getD (σ.vars "bk.t" - 1) 0 ∉ R.drop (σ.vars "bk.t") := by
    have hnd : (R.drop (σ.vars "bk.t" - 1)).Nodup := hRnd.sublist (List.drop_sublist _ _)
    rw [hdrop] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hwps : ∀ d, wpushed ra dg N τ R (σ.vars "bk.t" - 1) d
      = (if (τ.arrs ra).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 = N ∧
            (τ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 = d + 1
          then [R.getD (σ.vars "bk.t" - 1) 0] else [])
        ++ wpushed ra dg N τ R (σ.vars "bk.t") d := by
    intro d
    have := wpushed_succ (ra := ra) (dg := dg) (N := N) (τ := τ) (R := R)
      (t := σ.vars "bk.t" - 1) (d := d) ht1R
    rwa [show σ.vars "bk.t" - 1 + 1 = σ.vars "bk.t" by omega] at this
  -- the machine read, in the state's own arrays
  have haoval : (σ.arrs ao).getD (σ.vars "bk.v") 0 = offv := by
    rw [hW.aoq, hW.vv]; exact haov
  have hmtread : (σ.arrs mt).getD (offv + (σ.vars "bk.t" - 1)) 0
      = R.getD (σ.vars "bk.t" - 1) 0 := by
    rw [hW.mtq]; exact hrow _ ht1
  have hdgw : (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0
      = (τ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 := by
    rw [hW.degq _ hwN, if_neg (by rintro ⟨hc, -⟩; exact hwnot hc)]
    omega
  have hraw : (σ.arrs ra).getD (R.getD (σ.vars "bk.t" - 1) 0) 0
      = (τ.arrs ra).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 := by rw [hW.raq]
  -- bounds
  have haolen : σ.vars "bk.v" < (σ.arrs ao).length := by rw [hW.aoq, hW.vv]; exact hvlen
  have hvB : σ.vars "bk.v" < B := by rw [hW.vv]; omega
  have hmtlen' : offv + (σ.vars "bk.t" - 1) < (σ.arrs mt).length := by rw [hW.mtq]; omega
  have haoB : offv < B := by omega
  have hidxB : offv + (σ.vars "bk.t" - 1) < B := by omega
  have hwB : (σ.arrs mt).getD (offv + (σ.vars "bk.t" - 1)) 0 < B := by rw [hmtread]; omega
  have hwlenra : (σ.arrs mt).getD (offv + (σ.vars "bk.t" - 1)) 0 < (σ.arrs ra).length := by
    rw [hmtread, hW.raq]; omega
  have hwlendg : (σ.arrs mt).getD (offv + (σ.vars "bk.t" - 1)) 0 < (σ.arrs dg).length := by
    rw [hmtread]; have := hW.dglen; omega
  have hraB : (σ.arrs ra).getD ((σ.arrs mt).getD (offv + (σ.vars "bk.t" - 1)) 0) 0 < B := by
    rw [hmtread, hraw]
    have := hraN _ hwN
    omega
  have hdgB : (σ.arrs dg).getD ((σ.arrs mt).getD (offv + (σ.vars "bk.t" - 1)) 0) 0 < B := by
    rw [hmtread]
    have := hW.degb _ hwN
    omega
  have hdgsB : (σ.arrs dg).getD ((σ.arrs mt).getD (offv + (σ.vars "bk.t" - 1)) 0) 0 - 1 < B := by
    omega
  have htB : σ.vars "bk.t" - 1 < B := by omega
  have hnB : σ.vars "bk.n" < B := by omega
  have hraWB : (σ.arrs ra).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 < B := by
    rw [hraw]; have := hraN _ hwN; omega
  have hdgWB : (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 < B := by
    have := hW.degb _ hwN; omega
  have hdnewN : (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1 < N := by
    have := hW.degb _ hwN; omega
  have htpd : (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 ≤ N := hW.tpb _ hdnewN
  have hidx2 : ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) * N
      + (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 ≤ N * N := by
    have h1 : ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1 + 1) * N ≤ N * N :=
      Nat.mul_le_mul_right N (by omega)
    have h2 : ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1 + 1) * N
        = ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) * N + N := by ring
    omega
  have hmulB : ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) * N < B := by omega
  have hidx2B : ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) * N
      + (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 < B := by omega
  have hidx2len : ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) * N
      + (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 < (σ.arrs sk).length := by
    have := hW.sklen; omega
  have htpdlen : (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1 < (σ.arrs tp).length := by
    have := hW.tplen; omega
  have htpdB : (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 < B := by omega
  have htpd1B : (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 + 1 < B := by omega
  have hwlendg2 : (R.getD (σ.vars "bk.t" - 1) 0) < (σ.arrs dg).length := by have := hW.dglen; omega
  run_vcg
  all_goals try simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr,
    String.reduceEq, reduceIte, hmtread, haoval, eq_self_iff_true, if_true,
      if_neg hda, if_neg hdm, if_neg hdr, if_neg hdt, if_neg hds,
      if_neg hsa, if_neg hsm, if_neg hsr, if_neg hst, if_neg hsd,
      if_neg hta, if_neg htm, if_neg htr, if_neg hts,
      if_neg (Ne.symm hda), if_neg (Ne.symm hdm), if_neg (Ne.symm hdr),
      if_neg (Ne.symm hdt), if_neg (Ne.symm hds), if_neg (Ne.symm hsa),
      if_neg (Ne.symm hsm), if_neg (Ne.symm hsr), if_neg (Ne.symm hst),
      if_neg (Ne.symm hsd), if_neg (Ne.symm hta), if_neg (Ne.symm htm),
      if_neg (Ne.symm htr), if_neg (Ne.symm hts),
    hnn, List.length_set]
  all_goals try omega
  · -- the neighbour is still live: it moves down one bucket
    rename_i hlive
    simp only [vars_setVar, arrs_setVar, String.reduceEq, reduceIte, hmtread, haoval,
      hnn] at hlive
    have hraWN : (τ.arrs ra).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 = N := by rw [← hraw]; exact hlive
    have hdgpos : 0 < (τ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 := hposd _ hwmem hraWN
    have hdgσ : (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 = (τ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 := hdgw
    have hwnotin : (R.getD (σ.vars "bk.t" - 1) 0) ∉ mLst tp sk N σ ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) := by
      intro hc
      have := (hW.elts _ hdnewN _ hc).2
      omega
    have htplt : (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 < N :=
      tp_lt_of_nodup (hW.nodup _ hdnewN) (fun x hx => (hW.elts _ hdnewN x hx).1) hwN hwnotin
    have hsame : ∀ d, d < N → d ≠ (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1 →
        ∀ i, i < (σ.arrs tp).getD d 0 → d * N + i
          ≠ ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) * N
            + (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 := by
      intro d hd hdd i hi
      have h1 := hW.tpb d hd
      exact block_ne hdd (by omega) htplt
    have hpushL : mLst tp sk N ((((σ.setVar "bk.t" (σ.vars "bk.t" - 1)).setVar "bk.w"
          (R.getD (σ.vars "bk.t" - 1) 0)).setVar "bk.d" ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1)).setArr dg (R.getD (σ.vars "bk.t" - 1) 0)
          ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) |>.setArr sk
          (((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) * N
            + (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0) (R.getD (σ.vars "bk.t" - 1) 0) |>.setArr tp
          ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1)
          ((σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 + 1))
        ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1)
        = (R.getD (σ.vars "bk.t" - 1) 0) :: mLst tp sk N σ ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) := by
      refine mLst_push ?_ ?_ ?_
      · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte,
          eq_self_iff_true, if_true, if_neg hda, if_neg hdm, if_neg hdr, if_neg hdt, if_neg hds,
          if_neg hsa, if_neg hsm, if_neg hsr, if_neg hst, if_neg hsd,
          if_neg hta, if_neg htm, if_neg htr, if_neg hts,
          if_neg (Ne.symm hda), if_neg (Ne.symm hdm), if_neg (Ne.symm hdr),
          if_neg (Ne.symm hdt), if_neg (Ne.symm hds), if_neg (Ne.symm hsa),
          if_neg (Ne.symm hsm), if_neg (Ne.symm hsr), if_neg (Ne.symm hst),
          if_neg (Ne.symm hsd), if_neg (Ne.symm hta), if_neg (Ne.symm htm),
          if_neg (Ne.symm htr), if_neg (Ne.symm hts)]
        exact getD_set_self (by have := hW.tplen; omega)
      · intro i hi
        simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte,
          eq_self_iff_true, if_true, if_neg hda, if_neg hdm, if_neg hdr, if_neg hdt, if_neg hds,
          if_neg hsa, if_neg hsm, if_neg hsr, if_neg hst, if_neg hsd,
          if_neg hta, if_neg htm, if_neg htr, if_neg hts,
          if_neg (Ne.symm hda), if_neg (Ne.symm hdm), if_neg (Ne.symm hdr),
          if_neg (Ne.symm hdt), if_neg (Ne.symm hds), if_neg (Ne.symm hsa),
          if_neg (Ne.symm hsm), if_neg (Ne.symm hsr), if_neg (Ne.symm hst),
          if_neg (Ne.symm hsd), if_neg (Ne.symm hta), if_neg (Ne.symm htm),
          if_neg (Ne.symm htr), if_neg (Ne.symm hts)]
        exact getD_set_of_ne (by omega)
      · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte,
          eq_self_iff_true, if_true, if_neg hda, if_neg hdm, if_neg hdr, if_neg hdt, if_neg hds,
          if_neg hsa, if_neg hsm, if_neg hsr, if_neg hst, if_neg hsd,
          if_neg hta, if_neg htm, if_neg htr, if_neg hts,
          if_neg (Ne.symm hda), if_neg (Ne.symm hdm), if_neg (Ne.symm hdr),
          if_neg (Ne.symm hdt), if_neg (Ne.symm hds), if_neg (Ne.symm hsa),
          if_neg (Ne.symm hsm), if_neg (Ne.symm hsr), if_neg (Ne.symm hst),
          if_neg (Ne.symm hsd), if_neg (Ne.symm hta), if_neg (Ne.symm htm),
          if_neg (Ne.symm htr), if_neg (Ne.symm hts)]
        exact getD_set_self (by have := hW.sklen; omega)
    have hframeL : ∀ d, d < N → d ≠ (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1 →
        mLst tp sk N ((((σ.setVar "bk.t" (σ.vars "bk.t" - 1)).setVar "bk.w"
          (R.getD (σ.vars "bk.t" - 1) 0)).setVar "bk.d" ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1)).setArr dg (R.getD (σ.vars "bk.t" - 1) 0)
          ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) |>.setArr sk
          (((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) * N
            + (σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0) (R.getD (σ.vars "bk.t" - 1) 0) |>.setArr tp
          ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1)
          ((σ.arrs tp).getD ((σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) 0 + 1)) d
        = mLst tp sk N σ d := by
      intro d hd hdd
      refine mLst_frame ?_ ?_
      · simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte,
          eq_self_iff_true, if_true, if_neg hda, if_neg hdm, if_neg hdr, if_neg hdt, if_neg hds,
          if_neg hsa, if_neg hsm, if_neg hsr, if_neg hst, if_neg hsd,
          if_neg hta, if_neg htm, if_neg htr, if_neg hts,
          if_neg (Ne.symm hda), if_neg (Ne.symm hdm), if_neg (Ne.symm hdr),
          if_neg (Ne.symm hdt), if_neg (Ne.symm hds), if_neg (Ne.symm hsa),
          if_neg (Ne.symm hsm), if_neg (Ne.symm hsr), if_neg (Ne.symm hst),
          if_neg (Ne.symm hsd), if_neg (Ne.symm hta), if_neg (Ne.symm htm),
          if_neg (Ne.symm htr), if_neg (Ne.symm hts)]
        exact getD_set_of_ne hdd
      · intro i hi
        simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte,
          eq_self_iff_true, if_true, if_neg hda, if_neg hdm, if_neg hdr, if_neg hdt, if_neg hds,
          if_neg hsa, if_neg hsm, if_neg hsr, if_neg hst, if_neg hsd,
          if_neg hta, if_neg htm, if_neg htr, if_neg hts,
          if_neg (Ne.symm hda), if_neg (Ne.symm hdm), if_neg (Ne.symm hdr),
          if_neg (Ne.symm hdt), if_neg (Ne.symm hds), if_neg (Ne.symm hsa),
          if_neg (Ne.symm hsm), if_neg (Ne.symm hsr), if_neg (Ne.symm hst),
          if_neg (Ne.symm hsd), if_neg (Ne.symm hta), if_neg (Ne.symm htm),
          if_neg (Ne.symm htr), if_neg (Ne.symm hts)]
        exact getD_set_of_ne (hsame d hd hdd i hi)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by omega⟩
    all_goals try simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr,
      String.reduceEq, reduceIte, eq_self_iff_true, if_true, if_neg hda, if_neg hdm, if_neg hdr, if_neg hdt, if_neg hds,
      if_neg hsa, if_neg hsm, if_neg hsr, if_neg hst, if_neg hsd,
      if_neg hta, if_neg htm, if_neg htr, if_neg hts,
      if_neg (Ne.symm hda), if_neg (Ne.symm hdm), if_neg (Ne.symm hdr),
      if_neg (Ne.symm hdt), if_neg (Ne.symm hds), if_neg (Ne.symm hsa),
      if_neg (Ne.symm hsm), if_neg (Ne.symm hsr), if_neg (Ne.symm hst),
      if_neg (Ne.symm hsd), if_neg (Ne.symm hta), if_neg (Ne.symm htm),
      if_neg (Ne.symm htr), if_neg (Ne.symm hts),
      hnn, List.length_set]
    · omega
    · exact hW.vv
    · exact hW.rr
    · exact hW.aoq
    · exact hW.mtq
    · exact hW.raq
    · exact hW.dglen
    · exact hW.tplen
    · exact hW.sklen
    · intro x hx
      rw [hdrop]
      by_cases hxw : x = R.getD (σ.vars "bk.t" - 1) 0
      · rw [hxw, getD_set_self hwlendg2, if_pos ⟨List.mem_cons_self .., hraWN⟩, ← hdgσ]
      · rw [getD_set_of_ne hxw, hW.degq x hx, if_mem_cons_eq hxw]
    · intro x hx
      by_cases hxw : x = R.getD (σ.vars "bk.t" - 1) 0
      · rw [hxw, getD_set_self hwlendg2]; omega
      · rw [getD_set_of_ne hxw]; exact hW.degb x hx
    · intro d hd
      rw [hwps d, hdgσ.symm, hraWN]
      by_cases hdd : d = (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1
      · subst hdd
        rw [if_pos ⟨rfl, by omega⟩, hpushL, hW.stk _ hd]
        simp
      · rw [if_neg (by rintro ⟨-, hc⟩; omega), hframeL d hd hdd, hW.stk d hd]
        simp
    · intro d hd x hx
      by_cases hdd : d = (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1
      · subst hdd
        rw [hpushL] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨hwN, by rw [getD_set_self hwlendg2]⟩
        · refine ⟨(hW.elts _ hd x hx').1, ?_⟩
          by_cases hxw : x = R.getD (σ.vars "bk.t" - 1) 0
          · have h2 := (hW.elts _ hd x hx').2
            rw [hxw] at h2 ⊢
            rw [getD_set_self hwlendg2]
            
          · rw [getD_set_of_ne hxw]; exact (hW.elts _ hd x hx').2
      · rw [hframeL d hd hdd] at hx
        refine ⟨(hW.elts d hd x hx).1, ?_⟩
        by_cases hxw : x = R.getD (σ.vars "bk.t" - 1) 0
        · have h2 := (hW.elts d hd x hx).2
          rw [hxw] at h2 ⊢
          rw [getD_set_self hwlendg2]
          omega
        · rw [getD_set_of_ne hxw]; exact (hW.elts d hd x hx).2
    · intro d hd
      by_cases hdd : d = (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1
      · subst hdd
        rw [hpushL]
        exact List.nodup_cons.mpr ⟨hwnotin, hW.nodup _ hd⟩
      · rw [hframeL d hd hdd]; exact hW.nodup d hd
    · intro d hd
      by_cases hdd : d = (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1
      · subst hdd
        rw [getD_set_self (by have := hW.tplen; omega)]; omega
      · rw [getD_set_of_ne hdd]; exact hW.tpb d hd
    · have hsucc := sum_range_set_succ (N := N) (l := σ.arrs tp)
        (d₀ := (σ.arrs dg).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 - 1) hdnewN (by have := hW.tplen; omega)
      have hc := hW.cnt
      simp only [cellCount] at hc ⊢
      simp only [arrs_setVar, arrs_setArr, String.reduceEq, reduceIte,
        eq_self_iff_true, if_true, if_neg hda, if_neg hdm, if_neg hdr, if_neg hdt, if_neg hds,
        if_neg hsa, if_neg hsm, if_neg hsr, if_neg hst, if_neg hsd,
        if_neg hta, if_neg htm, if_neg htr, if_neg hts,
        if_neg (Ne.symm hda), if_neg (Ne.symm hdm), if_neg (Ne.symm hdr),
        if_neg (Ne.symm hdt), if_neg (Ne.symm hds), if_neg (Ne.symm hsa),
        if_neg (Ne.symm hsm), if_neg (Ne.symm hsr), if_neg (Ne.symm hst),
        if_neg (Ne.symm hsd), if_neg (Ne.symm hta), if_neg (Ne.symm htm),
        if_neg (Ne.symm htr), if_neg (Ne.symm hts)]
      omega
  · -- the neighbour has already been peeled: nothing to do
    rename_i hdead
    simp only [vars_setVar, arrs_setVar, String.reduceEq, reduceIte, hmtread, haoval,
      hnn] at hdead
    have hraWN : (τ.arrs ra).getD (R.getD (σ.vars "bk.t" - 1) 0) 0 ≠ N := by rw [← hraw]; exact hdead
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by omega⟩
    all_goals try simp only [vars_setVar, vars_setArr, arrs_setVar, String.reduceEq,
      reduceIte, hnn]
    · omega
    · exact hW.vv
    · exact hW.rr
    · exact hW.aoq
    · exact hW.mtq
    · exact hW.raq
    · exact hW.dglen
    · exact hW.tplen
    · exact hW.sklen
    · intro x hx
      rw [hW.degq x hx, hdrop]
      by_cases hxw : x = R.getD (σ.vars "bk.t" - 1) 0
      · rw [if_neg (by rintro ⟨-, hc⟩; rw [hxw] at hc; exact hraWN hc),
          if_neg (by rintro ⟨-, hc⟩; rw [hxw] at hc; exact hraWN hc)]
      · rw [if_mem_cons_eq hxw]
    · exact hW.degb
    · intro d hd
      rw [hwps d, if_neg (by rintro ⟨hc, -⟩; exact hraWN hc)]
      simpa using hW.stk d hd
    · exact hW.elts
    · exact hW.nodup
    · exact hW.tpb
    · have hc := hW.cnt
      simp only [cellCount, arrs_setVar] at hc ⊢
      omega

set_option maxHeartbeats 1000000 in
/-- **The row walk, at `41·D + 4`** — affine in `v`'s **original**
degree, which is what `staticPot` pays for. -/
theorem walkCom_spec {ao dg mt ra tp sk : String}
    (hda : dg ≠ ao) (hdm : dg ≠ mt) (hdr : dg ≠ ra) (hdt : dg ≠ tp) (hds : dg ≠ sk)
    (hsa : sk ≠ ao) (hsm : sk ≠ mt) (hsr : sk ≠ ra) (hst : sk ≠ tp) (hsd : sk ≠ dg)
    (hta : tp ≠ ao) (htm : tp ≠ mt) (htr : tp ≠ ra) (hts : tp ≠ sk)
    {B N : ℕ} (hB : N + N * N + 1 < B)
    {R : List ℕ} {D : ℕ} {τ : Env} {offv : ℕ}
    (hRlen : R.length = D) (hRnd : R.Nodup) (hRlt : ∀ x ∈ R, x < N) (hDN : D < N)
    (haov : (τ.arrs ao).getD (τ.vars "bk.v") 0 = offv)
    (hvlen : τ.vars "bk.v" < (τ.arrs ao).length)
    (hmtlen : offv + D ≤ (τ.arrs mt).length) (hoffB : offv + D < B)
    (hvN : τ.vars "bk.v" < N)
    (hrow : ∀ s, s < D → (τ.arrs mt).getD (offv + s) 0 = R.getD s 0)
    (hposd : ∀ x ∈ R, (τ.arrs ra).getD x 0 = N → 0 < (τ.arrs dg).getD x 0)
    (hralen : N ≤ (τ.arrs ra).length) (hraN : ∀ x, x < N → (τ.arrs ra).getD x 0 ≤ N) :
    Spec B (WSt ao dg mt ra tp sk N R D τ)
      (walkCom ao dg mt ra tp sk)
      (fun _ σ' => WSt ao dg mt ra tp sk N R D τ σ' ∧ σ'.vars "bk.t" = 0)
      (41 * D + 4) := by
  have hcond : ∀ σ : Env, WSt ao dg mt ra tp sk N R D τ σ →
      (Cond.lt (.lit 0) (.var "bk.t")).evalB B σ = some (decide (0 < σ.vars "bk.t")) := by
    intro σ hσ
    refine evalB_condLt (evalB_lit ?_) (evalB_var ?_)
    · omega
    · have := hσ.tle; omega
  refine (Spec.while_count (WSt ao dg mt ra tp sk N R D τ) (fun σ => σ.vars "bk.t") 37
    (fun σ hσ => ⟨_, hcond σ hσ⟩)
    ((walkBody_spec hda hdm hdr hdt hds hsa hsm hsr hst hsd hta htm htr hts hB
      hRlen hRnd hRlt hDN haov hvlen hmtlen hoffB hvN hrow hposd hralen hraN).pre ?_)
    (fun _ h => h) (fun σ hσ => ?_)).post ?_
  · rintro σ ⟨hσ, htrue⟩
    refine ⟨hσ, ?_⟩
    rw [hcond σ hσ] at htrue
    simpa using htrue
  · have := hσ.tle
    have hmul : (1 + 3 + 37) * σ.vars "bk.t" ≤ (1 + 3 + 37) * D :=
      Nat.mul_le_mul_left _ this
    have hsz : (Cond.lt (Expr.lit 0) (Expr.var "bk.t")).size = 3 := by simp
    simp only [hsz]
    omega
  · rintro σ σ' - ⟨hσ', hfalse⟩
    refine ⟨hσ', ?_⟩
    rw [hcond σ' hσ'] at hfalse
    have : ¬ (0 < σ'.vars "bk.t") := by simpa using hfalse
    omega

/-! ### The round -/

theorem map_range_getD {D : ℕ} {f : ℕ → ℕ} {R : List ℕ} (h : (List.range D).map f = R)
    {s : ℕ} (hs : s < D) : f s = R.getD s 0 := by
  rw [← h, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hs)]
  simp

/-- **One round**: scan to the minimum-degree bucket, write the
countdown rank of the vertex it pops, walk that vertex's original row
pushing every live neighbour one bucket down, and drop the cursor by
one. The peeled vertex's own cell is *not* removed — it is stale from
the moment its rank is written, and the next scan drops it. That is the
whole of lazy deletion. -/
def roundCom (ao dg mt ra tp sk : String) : Com :=
  .seq (scanCom ra dg tp sk)
  (.seq (.seq (.assign "bk.r" (.sub (.var "bk.r") (.lit 1)))
        (.seq (.store ra (.var "bk.v") (.var "bk.r"))
              (.assign "bk.t"
                (.sub (.get ao (.add (.var "bk.v") (.lit 1))) (.get ao (.var "bk.v"))))))
  (.seq (walkCom ao dg mt ra tp sk)
        (.assign "bk.c" (.sub (.var "bk.c") (.lit 1)))))

/-- The six region names of the peel are pairwise distinct. -/
structure Distinct6 (ao mt ra dg tp sk : String) : Prop where
  /-- offsets vs rows -/
  am : ao ≠ mt
  /-- offsets vs ranks -/
  ar : ao ≠ ra
  /-- offsets vs degrees -/
  ad : ao ≠ dg
  /-- offsets vs tops -/
  at' : ao ≠ tp
  /-- offsets vs cells -/
  as : ao ≠ sk
  /-- rows vs ranks -/
  mr : mt ≠ ra
  /-- rows vs degrees -/
  md : mt ≠ dg
  /-- rows vs tops -/
  mt' : mt ≠ tp
  /-- rows vs cells -/
  ms : mt ≠ sk
  /-- ranks vs degrees -/
  rd : ra ≠ dg
  /-- ranks vs tops -/
  rt : ra ≠ tp
  /-- ranks vs cells -/
  rs : ra ≠ sk
  /-- degrees vs tops -/
  dt : dg ≠ tp
  /-- degrees vs cells -/
  ds : dg ≠ sk
  /-- tops vs cells -/
  ts : tp ≠ sk

/-- `bStep`'s moved-group predicate, as a test on an index. -/
noncomputable def movedB {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (v : Fin N) (d : ℕ) (x : ℕ) : Bool :=
  decide (∃ h : x < N, (⟨x, h⟩ : Fin N) ∈ nbrsIn F S v ∧
    (nbrsIn F S (⟨x, h⟩ : Fin N)).card = d + 1)

theorem movedB_val {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N)) (v : Fin N)
    (d : ℕ) (u : Fin N) :
    movedB F S v d (u : ℕ) = decide (u ∈ nbrsIn F S v ∧ (nbrsIn F S u).card = d + 1) := by
  rw [movedB]
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro ⟨h', hc⟩; simpa using hc
  · intro h; exact ⟨u.isLt, by simpa using h⟩

theorem map_val_movedB {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (v : Fin N) (d : ℕ) :
    ((List.finRange N).filter (fun u => decide (u ∈ nbrsIn F S v ∧
        (nbrsIn F S u).card = d + 1))).map Fin.val
      = (List.range N).filter (movedB F S v d) := by
  rw [show (fun u : Fin N => decide (u ∈ nbrsIn F S v ∧ (nbrsIn F S u).card = d + 1))
      = (fun u : Fin N => movedB F S v d (u : ℕ)) from
        funext fun u => (movedB_val F S v d u).symm,
    map_filter_comp Fin.val (movedB F S v d) (List.finRange N),
    List.map_coe_finRange_eq_range]

/-- `bStep`'s survivor predicate, as a test on an index. -/
noncomputable def survB {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (v : Fin N) (x : ℕ) : Bool :=
  decide (∃ h : x < N, (⟨x, h⟩ : Fin N) ≠ v ∧ (⟨x, h⟩ : Fin N) ∉ nbrsIn F S v)

theorem survB_val {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N)) (v : Fin N)
    (u : Fin N) : survB F S v (u : ℕ) = decide (u ≠ v ∧ u ∉ nbrsIn F S v) := by
  rw [survB]
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro ⟨h', hc⟩; simpa using hc
  · intro h; exact ⟨u.isLt, by simpa using h⟩

theorem filter_survB_map {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (v : Fin N) (l : List (Fin N)) :
    (l.map Fin.val).filter (survB F S v)
      = (l.filter (fun u => decide (u ≠ v ∧ u ∉ nbrsIn F S v))).map Fin.val := by
  rw [show (fun u : Fin N => decide (u ≠ v ∧ u ∉ nbrsIn F S v))
      = (fun u : Fin N => survB F S v (u : ℕ)) from
        funext fun u => (survB_val F S v u).symm,
    map_filter_comp Fin.val (survB F S v) l]

set_option maxHeartbeats 2000000 in
/-- **The round's refinement step, once.** After the rank write and the
row walk, each stack — with its stale cells dropped — is the replay's
bucket at `bStep`. The moved group is the walk's push list, ascending
because the row is ascending and the walk runs downward; the survivors
are the old bucket minus the peeled vertex and minus the neighbours
whose degree has just fallen, which is exactly `bStep`'s filter. -/
theorem round_bkts {ao dg mt ra tp sk : String} {N : ℕ} {F : SimpleGraph (Fin N)}
    {offF : ℕ → ℕ} {k : ℕ} {σ₁ σ₃ σ₅ : Env} {v : Fin N}
    (hR : RSt ao dg mt ra tp sk F offF k σ₁) (hk : k < N)
    (hvS : v ∈ (bRun F k).live)
    (hra₃ : σ₃.arrs ra = (σ₁.arrs ra).set (v : ℕ) (N - k - 1))
    (hdg₃ : σ₃.arrs dg = σ₁.arrs dg) (htp₃ : σ₃.arrs tp = σ₁.arrs tp)
    (hsk₃ : σ₃.arrs sk = σ₁.arrs sk)
    (hW : WSt ao dg mt ra tp sk N (rowList F v) ((F.neighborSet v).ncard) σ₃ σ₅)
    (ht₅ : σ₅.vars "bk.t" = 0) :
    ∀ d, d < N → (mLst tp sk N σ₅ d).filter (mOK ra dg N σ₅ d)
      = bktV (bStep F (bRun F k) v) d := by
  classical
  have hvlen : (v : ℕ) < (σ₁.arrs ra).length := lt_of_lt_of_le v.isLt hR.ralen
  have hra₅ : σ₅.arrs ra = σ₃.arrs ra := hW.raq
  have hraV : (σ₃.arrs ra).getD (v : ℕ) 0 = N - k - 1 := by
    rw [hra₃]; exact getD_set_self hvlen
  have hraNe : ∀ x : Fin N, x ≠ v →
      (σ₃.arrs ra).getD (x : ℕ) 0 = (σ₁.arrs ra).getD (x : ℕ) 0 := by
    intro x hx
    rw [hra₃]
    exact getD_set_of_ne (fun hc => hx (Fin.val_inj.mp hc))
  have hlive₃ : ∀ x : Fin N,
      ((σ₃.arrs ra).getD (x : ℕ) 0 = N ↔ (x ∈ (bRun F k).live ∧ x ≠ v)) := by
    intro x
    by_cases hxv : x = v
    · subst hxv
      constructor
      · intro hc; rw [hraV] at hc; omega
      · rintro ⟨-, hc⟩; exact absurd rfl hc
    · rw [hraNe x hxv]
      constructor
      · intro hc
        refine ⟨?_, hxv⟩
        by_contra hxS
        rw [hR.dead x hxS] at hc
        have := Lax3Proofs.CoverRoutine.selRank_lt (bucketSel N) F x
        omega
      · rintro ⟨hxS, -⟩; exact hR.live x hxS
  have hdg₅ : ∀ x, x < N → (σ₅.arrs dg).getD x 0
      = (σ₁.arrs dg).getD x 0
        - (if x ∈ rowList F v ∧ (σ₃.arrs ra).getD x 0 = N then 1 else 0) := by
    intro x hx
    rw [hW.degq x hx, ht₅, List.drop_zero, hdg₃]
  have hmL : ∀ d, d < N → mLst tp sk N σ₅ d
      = wpushed ra dg N σ₃ (rowList F v) 0 d ++ mLst tp sk N σ₁ d := by
    intro d hd
    rw [hW.stk d hd, ht₅]
    congr 1
    exact mLst_frame (by rw [htp₃]) (fun i _ => by rw [hsk₃])
  intro d hd
  rw [hmL d hd, List.filter_append, bktV, bStep_bkt, List.map_append]
  congr 1
  · -- the moved group
    have hself : (wpushed ra dg N σ₃ (rowList F v) 0 d).filter (mOK ra dg N σ₅ d)
        = wpushed ra dg N σ₃ (rowList F v) 0 d := by
      refine List.filter_eq_self.mpr ?_
      intro x hx
      rw [wpushed, List.drop_zero, List.mem_filter] at hx
      obtain ⟨hxR, hxq⟩ := hx
      obtain ⟨hxra, hxdg⟩ := decide_eq_true_iff.mp hxq
      have hxN : x < N := rowList_lt_N hxR
      rw [mOK, decide_eq_true_iff, mKey, hra₅, hxra, hdg₅ x hxN,
        if_pos ⟨hxR, hxra⟩, ← hdg₃, hxdg]
      simp
    rw [hself, map_val_movedB, wpushed, List.drop_zero, rowList, List.filter_filter]
    refine List.filter_congr ?_
    intro x hx
    have hxN : x < N := List.mem_range.mp hx
    have hkeyra := hlive₃ ⟨x, hxN⟩
    rw [movedB]
    by_cases hxin : (⟨x, hxN⟩ : Fin N) ∈ nbrsIn F (bRun F k).live v
    · obtain ⟨hxS, hxadj⟩ := mem_nbrsIn.mp hxin
      have hxne : (⟨x, hxN⟩ : Fin N) ≠ v := by rintro rfl; exact F.irrefl hxadj
      have hra : (σ₃.arrs ra).getD x 0 = N := hkeyra.mpr ⟨hxS, hxne⟩
      have hdgx : (σ₃.arrs dg).getD x 0 = (nbrsIn F (bRun F k).live ⟨x, hxN⟩).card := by
        rw [hdg₃]; exact hR.deg ⟨x, hxN⟩ hxS
      have hadjB : adjB F v x = true := adjB_val.mpr hxadj
      simp only [hadjB, Bool.true_and, Bool.and_true, hra, hdgx]
      refine decide_eq_decide.mpr ⟨?_, ?_⟩
      · rintro ⟨-, hc⟩; exact ⟨hxN, hxin, hc⟩
      · rintro ⟨h', -, hc⟩; exact ⟨trivial, by simpa using hc⟩
    · have hq : ¬ ∃ h : x < N, (⟨x, h⟩ : Fin N) ∈ nbrsIn F (bRun F k).live v ∧
          (nbrsIn F (bRun F k).live (⟨x, h⟩ : Fin N)).card = d + 1 := by
        rintro ⟨h', hc, -⟩; exact hxin (by simpa using hc)
      rw [decide_eq_false hq]
      by_cases hadjB : adjB F v x = true
      · have hxadj : F.Adj (⟨x, hxN⟩ : Fin N) v := adjB_val.mp hadjB
        have hxnotS : (⟨x, hxN⟩ : Fin N) ∉ (bRun F k).live :=
          fun hc => hxin (mem_nbrsIn.mpr ⟨hc, hxadj⟩)
        have hra : ¬ (σ₃.arrs ra).getD x 0 = N := fun hc => hxnotS (hkeyra.mp hc).1
        simp only [hadjB, Bool.true_and, Bool.and_true]
        exact decide_eq_false (fun hc => hra hc.1)
      · simp only [Bool.not_eq_true] at hadjB
        simp [hadjB]
  · -- the survivors
    have hpt : ∀ x ∈ mLst tp sk N σ₁ d, mOK ra dg N σ₅ d x
        = (survB F (bRun F k).live v x && mOK ra dg N σ₁ d x) := by
      intro x hx
      obtain ⟨hxN, hxdgle⟩ := hR.elts d hd x hx
      have hraN₁ : (σ₁.arrs ra).getD x 0 ≤ N := hR.ra_le ⟨x, hxN⟩
      have hxvv : ∀ h : (⟨x, hxN⟩ : Fin N) = v, x = (v : ℕ) := fun h => by rw [← h]
      have hraN₅ : (σ₅.arrs ra).getD x 0 ≤ N := by
        rw [hra₅]
        by_cases hxv : (⟨x, hxN⟩ : Fin N) = v
        · rw [hxvv hxv, hraV]; omega
        · rw [hraNe ⟨x, hxN⟩ hxv]; exact hraN₁
      rw [Bool.eq_iff_iff, mOK_iff hd hraN₅, Bool.and_eq_true, survB,
        decide_eq_true_iff, mOK_iff hd hraN₁, hra₅]
      by_cases hxv : (⟨x, hxN⟩ : Fin N) = v
      · constructor
        · rintro ⟨hc, -⟩
          rw [hxvv hxv, hraV] at hc
          omega
        · rintro ⟨⟨h', hne, -⟩, -⟩
          exact absurd (by simpa using hxv) hne
      · rw [hraNe ⟨x, hxN⟩ hxv, hdg₅ x hxN]
        by_cases hxin : (⟨x, hxN⟩ : Fin N) ∈ nbrsIn F (bRun F k).live v
        · obtain ⟨hxS, hxadj⟩ := mem_nbrsIn.mp hxin
          have hra : (σ₃.arrs ra).getD x 0 = N := (hlive₃ ⟨x, hxN⟩).mpr ⟨hxS, hxv⟩
          have hxR : x ∈ rowList F v := mem_rowList.mpr hxadj
          have hvmem : v ∈ nbrsIn F (bRun F k).live ⟨x, hxN⟩ :=
            mem_nbrsIn.mpr ⟨hvS, hxadj.symm⟩
          have hpos : 0 < (nbrsIn F (bRun F k).live (⟨x, hxN⟩ : Fin N)).card :=
            Finset.card_pos.mpr ⟨v, hvmem⟩
          have hdgx : (σ₁.arrs dg).getD x 0
              = (nbrsIn F (bRun F k).live ⟨x, hxN⟩).card := hR.deg _ hxS
          rw [if_pos ⟨hxR, hra⟩]
          constructor
          · rintro ⟨-, hc⟩; omega
          · rintro ⟨⟨h', -, hc⟩, -⟩; exact absurd (by simpa using hxin) hc
        · have hnorow : ¬ (x ∈ rowList F v ∧ (σ₃.arrs ra).getD x 0 = N) := by
            rintro ⟨h1, h2⟩
            exact hxin (mem_nbrsIn.mpr ⟨((hlive₃ ⟨x, hxN⟩).mp h2).1, mem_rowList.mp h1⟩)
          rw [if_neg hnorow]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨⟨hxN, hxv, hxin⟩, h1, by omega⟩
          · rintro ⟨-, h1, h2⟩
            exact ⟨h1, by omega⟩
    rw [List.filter_congr hpt, ← List.filter_filter, hR.bkts d hd, bktV,
      filter_survB_map]

set_option maxHeartbeats 2000000 in
/-- **One round of the peel.** The vertex it peels is the replay's pop;
the state it leaves refines the replay one step on; and it costs
`91·|N_F(v)| + 79 + 50·(cursor rise) + 50·(cells removed)` — the shape
`peelLoop_linear_bucket_lazy` charges. -/
theorem roundCom_run {ao dg mt ra tp sk : String} (hD : Distinct6 ao mt ra dg tp sk)
    {B N : ℕ} {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ} (hB : N + N * N + 1 < B)
    (hoff0 : offF 0 = 0)
    (hoffs : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (F.neighborSet v).ncard)
    {k : ℕ} (hk : k < N) {σ : Env}
    (hR : RSt ao dg mt ra tp sk F offF k σ) (hcur : σ.vars "bk.c" = (bRun F k).cur) :
    ∃ (v : Fin N) (σ' : Env) (K : ℕ),
      bPop (bRun F k) = some v ∧
      Run B (roundCom ao dg mt ra tp sk) σ σ' K ∧
      RSt ao dg mt ra tp sk F offF (k + 1) σ' ∧
      σ'.vars "bk.c" = (bRun F (k + 1)).cur ∧
      K + 50 * cellCount tp N σ'
        ≤ 91 * (F.neighborSet v).ncard + 79
          + 50 * ((bRun F (k + 1)).cur + 1 - (bRun F k).cur) + 50 * cellCount tp N σ := by
  classical
  have hne : (bRun F k).live.Nonempty := bRun_live_nonempty F hk
  have hlev : bLevel (bRun F k) = minDeg F (bRun F k).live hne :=
    bLevel_eq_minDeg (bRun_inv F k) hne
  have hlevN : bLevel (bRun F k) < N := by
    rw [hlev]
    refine lt_of_lt_of_le (minDeg_lt_card F hne) ?_
    simpa using Finset.card_le_univ (bRun F k).live
  have hcle : σ.vars "bk.c" ≤ bLevel (bRun F k) := by
    rw [hcur, hlev]; exact (bRun_inv F k).2 hne
  obtain ⟨σ₁, K₁, hrun₁, hR₁, hc₁, ⟨v, hvv, hpop⟩, hcost₁⟩ :=
    scanCom_run (Ne.symm hD.at') (Ne.symm hD.mt') (Ne.symm hD.rt) (Ne.symm hD.dt)
      hD.ts hB hk hR hcle
  obtain ⟨v', hpop', hvS0, hlive0, hcur0⟩ := bRun_round F hk
  have hvveq : v' = v := by rw [hpop] at hpop'; exact (Option.some.inj hpop').symm
  rw [hvveq] at hvS0 hlive0
  have hvS := hvS0
  have hlive' := hlive0
  have hcur' := hcur0
  have hstep : bRun F (k + 1) = bStep F (bRun F k) v := by
    rw [bRun_succ, hpop]
  have hrank : Lax3Proofs.CoverRoutine.selRank (bucketSel N) F v = N - k - 1 :=
    selRank_bPop F hk hpop
  have hvN : (v : ℕ) < N := v.isLt
  set D : ℕ := (F.neighborSet v).ncard with hDdef
  have hDN : D < N := ncard_neighborSet_lt F v
  have hsq : offF N ≤ N * N := offF_le_sq hoff0 hoffs N le_rfl
  have hoffv1 : offF ((v : ℕ) + 1) = offF (v : ℕ) + D := hoffs v
  have hoffle : offF ((v : ℕ) + 1) ≤ offF N := offF_mono hoffs N le_rfl _ hvN
  -- the prefix: countdown, rank, row length
  have hrlen : (v : ℕ) < (σ₁.arrs ra).length := lt_of_lt_of_le hvN hR₁.ralen
  have haov : (σ₁.arrs ao).getD (v : ℕ) 0 = offF (v : ℕ) := hR₁.aoval _ (le_of_lt hvN)
  have haov1 : (σ₁.arrs ao).getD ((v : ℕ) + 1) 0 = offF ((v : ℕ) + 1) :=
    hR₁.aoval _ hvN
  have haolen : (v : ℕ) + 1 < (σ₁.arrs ao).length := by have := hR₁.aolen; omega
  have hrr := hR₁.rr
  have hpre : ∃ τ : Env,
      Run B (.seq (.assign "bk.r" (.sub (.var "bk.r") (.lit 1)))
        (.seq (.store ra (.var "bk.v") (.var "bk.r"))
          (.assign "bk.t"
            (.sub (.get ao (.add (.var "bk.v") (.lit 1))) (.get ao (.var "bk.v"))))))
        σ₁ τ 15 ∧
      τ.vars "bk.n" = N ∧ τ.vars "bk.r" = N - k - 1 ∧ τ.vars "bk.v" = (v : ℕ) ∧
      τ.vars "bk.c" = σ₁.vars "bk.c" ∧ τ.vars "bk.t" = D ∧
      τ.arrs ao = σ₁.arrs ao ∧ τ.arrs mt = σ₁.arrs mt ∧ τ.arrs dg = σ₁.arrs dg ∧
      τ.arrs tp = σ₁.arrs tp ∧ τ.arrs sk = σ₁.arrs sk ∧
      τ.arrs ra = (σ₁.arrs ra).set (v : ℕ) (N - k - 1) := by
    have hnn := hR₁.nn
    have hrB : σ₁.vars "bk.r" < B := by omega
    have hvB : σ₁.vars "bk.v" < B := by rw [← hvv]; omega
    have hvlen' : σ₁.vars "bk.v" < (σ₁.arrs ra).length := by rw [← hvv]; omega
    have hao1B : (σ₁.arrs ao).getD ((v : ℕ) + 1) 0 < B := by rw [haov1]; omega
    have haovB : (σ₁.arrs ao).getD (v : ℕ) 0 < B := by rw [haov]; omega
    have hvlt : σ₁.vars "bk.v" + 1 < (σ₁.arrs ao).length := by rw [← hvv]; omega
    have hvlt2 : σ₁.vars "bk.v" < (σ₁.arrs ao).length := by rw [← hvv]; omega
    have hv1B : σ₁.vars "bk.v" + 1 < B := by rw [← hvv]; omega
    run_vcg
    all_goals try simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr,
      String.reduceEq, reduceIte, eq_self_iff_true, if_true, ← hvv, haov, haov1,
      hnn, hrr, if_neg hD.ar, if_neg hD.mr, if_neg hD.rd, if_neg hD.rt, if_neg hD.rs,
      if_neg hD.ar.symm, if_neg hD.mr.symm, if_neg hD.rd.symm, if_neg hD.rt.symm,
      if_neg hD.rs.symm]
    all_goals try omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr,
        String.reduceEq, reduceIte, eq_self_iff_true, if_true, ← hvv, haov, haov1,
        hnn, hrr, if_neg hD.ar.symm, if_neg hD.mr.symm, if_neg hD.rd.symm,
        if_neg hD.rt.symm, if_neg hD.rs.symm]) <;>
      first
        | rfl
        | omega
  obtain ⟨τ, hrunP, hτn, hτr, hτv, hτc, hτt, hτao, hτmt, hτdg, hτtp, hτsk, hτra⟩ := hpre
  obtain ⟨v'', hpop'', hv''S, hv''deg⟩ := bPop_spec (bRun_inv F k) hne
  have hv'' : v'' = v := by rw [hpop] at hpop''; exact (Option.some.inj hpop'').symm
  rw [hv''] at hv''deg
  -- the walk's hypotheses
  have hmLτ : ∀ d, mLst tp sk N τ d = mLst tp sk N σ₁ d :=
    fun d => mLst_frame (by rw [hτtp]) (fun i _ => by rw [hτsk])
  have hraVτ : (τ.arrs ra).getD (v : ℕ) 0 = N - k - 1 := by
    rw [hτra]; exact getD_set_self hrlen
  have hraNeτ : ∀ x, x < N → x ≠ (v : ℕ) →
      (τ.arrs ra).getD x 0 = (σ₁.arrs ra).getD x 0 := by
    intro x _ hx
    rw [hτra]; exact getD_set_of_ne hx
  have hτraN : ∀ x, x < N → (τ.arrs ra).getD x 0 ≤ N := by
    intro x hx
    by_cases hxv : x = (v : ℕ)
    · rw [hxv, hraVτ]; omega
    · rw [hraNeτ x hx hxv]; exact hR₁.ra_le ⟨x, hx⟩
  have hτposd : ∀ x ∈ rowList F v, (τ.arrs ra).getD x 0 = N →
      0 < (τ.arrs dg).getD x 0 := by
    intro x hx hra
    have hxN : x < N := rowList_lt_N hx
    have hxadj : F.Adj (⟨x, hxN⟩ : Fin N) v := mem_rowList.mp hx
    have hxv : x ≠ (v : ℕ) := by
      intro hc
      rw [hc, hraVτ] at hra
      omega
    rw [hraNeτ x hxN hxv] at hra
    have hxS : (⟨x, hxN⟩ : Fin N) ∈ (bRun F k).live := by
      by_contra hc
      rw [hR₁.dead _ hc] at hra
      have := Lax3Proofs.CoverRoutine.selRank_lt (bucketSel N) F ⟨x, hxN⟩
      omega
    rw [hτdg, hR₁.deg _ hxS]
    exact Finset.card_pos.mpr ⟨v, mem_nbrsIn.mpr ⟨hvS, hxadj.symm⟩⟩
  have hRlen : (rowList F v).length = D := rowList_length F v
  have hWinit : WSt ao dg mt ra tp sk N (rowList F v) D τ τ := by
    refine ⟨hτn, by omega, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [hτdg]; exact hR₁.dglen
    · rw [hτtp]; exact hR₁.tplen
    · rw [hτsk]; exact hR₁.sklen
    · intro x hx
      rw [hτt, List.drop_eq_nil_of_le (by omega)]
      simp
    · intro x hx; rw [hτdg]; exact hR₁.degb x hx
    · intro d hd
      rw [hτt, wpushed_full (by omega)]
      simp
    · intro d hd x hx
      rw [hmLτ d] at hx
      rw [hτdg]
      exact hR₁.elts d hd x hx
    · intro d hd; rw [hmLτ d]; exact hR₁.nodup d hd
    · intro d hd; rw [hτtp]; exact hR₁.tpb d hd
    · rw [hτt]
  obtain ⟨σ₅, hrun₅, hW₅, ht₅⟩ :=
    (walkCom_spec (Ne.symm hD.ad) (Ne.symm hD.md) (Ne.symm hD.rd) hD.dt hD.ds
      (Ne.symm hD.as) (Ne.symm hD.ms) (Ne.symm hD.rs) (Ne.symm hD.ts) (Ne.symm hD.ds)
      (Ne.symm hD.at') (Ne.symm hD.mt') (Ne.symm hD.rt) hD.ts hB (offv := offF (v : ℕ))
      hRlen ((List.nodup_range).filter _) (fun x hx => rowList_lt_N hx) hDN
      (by rw [hτao, hτv]; exact haov) (by rw [hτao, hτv]; omega)
      (by rw [hτmt]; have := hR₁.mtlen; omega) (by omega)
      (by rw [hτv]; exact hvN)
      (fun s hs => by rw [hτmt]; exact map_range_getD (hR₁.rows v) hs)
      hτposd (by rw [hτra, List.length_set]; exact hR₁.ralen) hτraN).run hWinit
  -- the cursor drop
  have hc₅ : σ₅.vars "bk.c" = bLevel (bRun F k) := by
    rw [hrun₅.frame_var "bk.c" (by simp [walkCom, walkBody, Com.wvars]), hτc, hc₁]
  have hcurNew : (bRun F (k + 1)).cur = bLevel (bRun F k) - 1 := by
    rw [hstep, bStep_cur, hv''deg, hlev]
  have hrun₆ : Run B (.assign "bk.c" (.sub (.var "bk.c") (.lit 1))) σ₅
      (σ₅.setVar "bk.c" (σ₅.vars "bk.c" - 1)) 4 := by
    refine (Run.assign (v := σ₅.vars "bk.c" - 1) ?_).mono (by simp)
    exact evalB_bin (evalB_var (by rw [hc₅]; omega)) (evalB_lit (by omega))
      (by show σ₅.vars "bk.c" - 1 < B; omega)
  refine ⟨v, σ₅.setVar "bk.c" (σ₅.vars "bk.c" - 1), K₁ + 41 * D + 23, hpop,
    ((hrun₁.seq (hrunP.seq (hrun₅.seq hrun₆))).mono (by omega)), ?_, ?_, ?_⟩
  · -- the round state one step on
    have hraq : σ₅.arrs ra = τ.arrs ra := hW₅.raq
    have hmtq : σ₅.arrs mt = τ.arrs mt := hW₅.mtq
    have haoq : σ₅.arrs ao = τ.arrs ao := hW₅.aoq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [vars_setVar, String.reduceEq, reduceIte]; exact hW₅.nn
    · simp only [vars_setVar, String.reduceEq, reduceIte, hW₅.rr, hτr]; omega
    · simp only [arrs_setVar, haoq, hτao]; exact hR₁.aolen
    · simp only [arrs_setVar, haoq, hτao]; exact hR₁.aoval
    · simp only [arrs_setVar, hmtq, hτmt]; exact hR₁.mtlen
    · simp only [arrs_setVar]; rw [hraq, hτra, List.length_set]; exact hR₁.ralen
    · simp only [arrs_setVar]; exact hW₅.dglen
    · simp only [arrs_setVar]; exact hW₅.tplen
    · simp only [arrs_setVar]; exact hW₅.sklen
    · simp only [arrs_setVar, hmtq, hτmt]; exact hR₁.rows
    · intro x hx
      simp only [arrs_setVar, hraq]
      rw [hstep, bStep_live, Finset.mem_erase] at hx
      rw [hraNeτ (x : ℕ) x.isLt (fun hc => hx.1 (Fin.val_inj.mp hc))]
      exact hR₁.live x hx.2
    · intro x hx
      simp only [arrs_setVar, hraq]
      rw [hstep, bStep_live, Finset.mem_erase] at hx
      by_cases hxv : x = v
      · rw [hxv, hraVτ, hrank]
      · have hxS : x ∉ (bRun F k).live := by
          intro hc; exact hx ⟨fun h => hxv h, hc⟩
        rw [hraNeτ (x : ℕ) x.isLt (fun hc => hxv (Fin.val_inj.mp hc))]
        exact hR₁.dead x hxS
    · intro x hx
      simp only [arrs_setVar]
      rw [hstep, bStep_live] at hx ⊢
      have hxE := Finset.mem_erase.mp hx
      have hxS := hxE.2
      have hxv : x ≠ v := hxE.1
      have hraX : (τ.arrs ra).getD (x : ℕ) 0 = N := by
        rw [hraNeτ (x : ℕ) x.isLt (fun hc => hxv (Fin.val_inj.mp hc))]
        exact hR₁.live x hxS
      rw [hW₅.degq (x : ℕ) x.isLt, ht₅, List.drop_zero, hτdg, hR₁.deg x hxS]
      have hc := card_nbrsIn_erase F (bRun F k).live hvS hxS
      by_cases hadj : (x : ℕ) ∈ rowList F v
      · have hxadj : F.Adj x v := mem_rowList.mp hadj
        have hin : x ∈ nbrsIn F (bRun F k).live v := mem_nbrsIn.mpr ⟨hxS, hxadj⟩
        rw [if_pos ⟨hadj, hraX⟩]
        rw [if_pos hin] at hc
        omega
      · have hnin : x ∉ nbrsIn F (bRun F k).live v := fun hc' =>
          hadj (mem_rowList.mpr (mem_nbrsIn.mp hc').2)
        rw [if_neg (by rintro ⟨hc', -⟩; exact hadj hc')]
        rw [if_neg hnin] at hc
        omega
    · intro x hx; simp only [arrs_setVar]; exact hW₅.degb x hx
    · intro d hd
      rw [show mLst tp sk N (σ₅.setVar "bk.c" (σ₅.vars "bk.c" - 1)) d
          = mLst tp sk N σ₅ d from rfl,
        show mOK ra dg N (σ₅.setVar "bk.c" (σ₅.vars "bk.c" - 1)) d
          = mOK ra dg N σ₅ d from rfl, hstep]
      exact round_bkts hR₁ hk hvS hτra hτdg hτtp hτsk hW₅ ht₅ d hd
    · intro d hd x hx; simp only [arrs_setVar]; exact hW₅.elts d hd x hx
    · intro d hd; exact hW₅.nodup d hd
    · intro d hd; simp only [arrs_setVar]; exact hW₅.tpb d hd
  · simp only [vars_setVar, eq_self_iff_true, if_true, hc₅, hcurNew]
  · have hcc₅ : cellCount tp N (σ₅.setVar "bk.c" (σ₅.vars "bk.c" - 1))
        = cellCount tp N σ₅ := rfl
    have hcnt := hW₅.cnt
    rw [ht₅] at hcnt
    have hccτ : cellCount tp N τ = cellCount tp N σ₁ := by
      rw [cellCount, cellCount, hτtp]
    have hcurle : (bRun F k).cur ≤ bLevel (bRun F k) := by rw [hlev]; exact (bRun_inv F k).2 hne
    rw [hcc₅, hcurNew, hcur] at *
    omega

/-! ## §7 The pass -/

/-- The peel's main loop. -/
def peelLoopCom (ao dg mt ra tp sk : String) : Com :=
  .while (.lt (.lit 0) (.var "bk.r")) (roundCom ao dg mt ra tp sk)

/-- The loop's invariant: the machine refines the replay at the round
the countdown names. -/
def PInv (ao dg mt ra tp sk : String) {N : ℕ} (F : SimpleGraph (Fin N))
    (offF : ℕ → ℕ) (σ : Env) : Prop :=
  RSt ao dg mt ra tp sk F offF (N - σ.vars "bk.r") σ ∧
    σ.vars "bk.c" = (bRun F (N - σ.vars "bk.r")).cur ∧ σ.vars "bk.r" ≤ N

set_option maxHeartbeats 1000000 in
/-- **The peel loop, at `233·N + 91·m + 4`.** The four terms of
`peelLoop_linear_bucket_lazy`: `83` per round, `91` per slot of the
peeled vertex's original row (paid by `staticPot_erase`), `50` per step
of the cursor (paid by `minDeg_le_minDeg_erase_succ` through
`bRun_round`), and `50` per cell removed from a stack (paid by the cell
count, which starts at `N`). There is no `N * N` term. -/
theorem peelLoopCom_spec {ao dg mt ra tp sk : String}
    (hD : Distinct6 ao mt ra dg tp sk)
    {B N : ℕ} {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ} (hB : N + N * N + 1 < B)
    (hoff0 : offF 0 = 0)
    (hoffs : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (F.neighborSet v).ncard) :
    Spec B
      (fun σ => PInv ao dg mt ra tp sk F offF σ ∧ σ.vars "bk.r" = N ∧
        cellCount tp N σ ≤ N)
      (peelLoopCom ao dg mt ra tp sk)
      (fun _ σ' => PInv ao dg mt ra tp sk F offF σ' ∧
        (Cond.lt (.lit 0) (.var "bk.r")).evalB B σ' = some false)
      (233 * N + 91 * slotCount F + 4) := by
  classical
  have hcond : ∀ σ : Env, PInv ao dg mt ra tp sk F offF σ →
      (Cond.lt (.lit 0) (.var "bk.r")).evalB B σ = some (decide (0 < σ.vars "bk.r")) := by
    intro σ hσ
    refine evalB_condLt (evalB_lit ?_) (evalB_var ?_)
    · omega
    · have := hσ.2.2; omega
  have hmain := peelLoop_linear_bucket_lazy (B := B) (N := N) (F := F)
    (bc := .lt (.lit 0) (.var "bk.r")) (body := roundCom ao dg mt ra tp sk)
    (PInv ao dg mt ra tp sk F offF) (fun σ => N - σ.vars "bk.r")
    (fun σ => cellCount tp N σ) 83 91 50 50 N
    (fun σ hσ => ⟨_, hcond σ hσ⟩) ?_
  · refine (hmain.pre ?_).mono ?_
    · rintro σ ⟨hI, hr, hnc⟩
      exact ⟨hI, by show N - σ.vars "bk.r" = 0; omega, hnc⟩
    · have hsz : (Cond.lt (Expr.lit 0) (Expr.var "bk.r")).size = 3 := by simp
      rw [hsz]
      omega
  · intro σ hσ hv
    obtain ⟨hR, hc, hrle⟩ := hσ
    have hrpos : 0 < σ.vars "bk.r" := by
      rw [hcond σ ⟨hR, hc, hrle⟩] at hv
      simpa using hv
    have hkN : N - σ.vars "bk.r" < N := by omega
    obtain ⟨v, σ', K, hpop, hrun, hR', hc', hcost⟩ :=
      roundCom_run hD hB hoff0 hoffs hkN hR hc
    have hr' : σ'.vars "bk.r" = N - (N - σ.vars "bk.r" + 1) := hR'.rr
    have hkof : N - σ'.vars "bk.r" = N - σ.vars "bk.r" + 1 := by omega
    refine ⟨v, σ', K, hkN, hpop, hrun, ⟨?_, ?_, ?_⟩, hkof, ?_⟩
    · rw [hkof]; exact hR'
    · rw [hkof]; exact hc'
    · omega
    · have hsz : (Cond.lt (Expr.lit 0) (Expr.var "bk.r")).size = 3 := by simp
      simp only [hsz, hkof]
      omega

theorem tp_le_of_nodup {tp sk : String} {N : ℕ} {σ : Env} {d : ℕ}
    (hnd : (mLst tp sk N σ d).Nodup) (hlt : ∀ x ∈ mLst tp sk N σ d, x < N) :
    (σ.arrs tp).getD d 0 ≤ N := by
  classical
  have hsub : (mLst tp sk N σ d).toFinset ⊆ Finset.range N := by
    intro x hx
    exact Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard
  have hlen : (mLst tp sk N σ d).length = (σ.arrs tp).getD d 0 := mLst_length
  omega

/-- **The static-adjacency bucket peel.** Transpose the rows once, zero
the tops, sentinel the ranks, build the buckets, then run the rounds. -/
def bucketPeelCom (ao aj dg mt ra tp sk nnSrc : String) : Com :=
  .seq (.assign "bk.n" (.var nnSrc))
  (.seq (bkZeroCom tp)
  (.seq (transCom ao aj mt tp)
  (.seq (bkZeroCom tp)
  (.seq (peelInitCom ra "bk.n" "bk.i")
  (.seq (bkBuildCom dg tp sk)
  (.seq (.assign "bk.c" (.lit 0))
  (.seq (.assign "bk.r" (.var "bk.n"))
        (peelLoopCom ao dg mt ra tp sk))))))))

set_option maxHeartbeats 2000000 in
/-- **The peel leaves the bucket elimination ranking**, at
`313·N + 118·m + 40` — linear in the carrier and the slot count, with
no `N * N` term. -/
theorem bucketPeelCom_spec {ao aj dg mt ra tp sk nnSrc : String}
    (hD : Distinct6 ao mt ra dg tp sk)
    (hja : aj ≠ ao) (hjm : aj ≠ mt) (hjr : aj ≠ ra) (hjd : aj ≠ dg)
    (hjt : aj ≠ tp) (hjs : aj ≠ sk)
    {B N : ℕ} (hB : N + N * N + 1 < B) {F : SimpleGraph (Fin N)} :
    Spec B
      (fun σ => DelAdjSt ao aj dg mt F (∅ : Set (Fin N)) σ ∧
        N ≤ (σ.arrs ra).length ∧ N ≤ (σ.arrs tp).length ∧
        N * N + N ≤ (σ.arrs sk).length ∧ σ.vars nnSrc = N)
      (bucketPeelCom ao aj dg mt ra tp sk nnSrc)
      (fun _ σ' => RankArr ra (Lax3Proofs.CoverRoutine.selPerm (bucketSel N) F) σ')
      (313 * N + 118 * slotCount F + 40) := by
  classical
  intro σ hσ
  obtain ⟨hdel, hralen, htplen, hsklen, hnsrc⟩ := hσ
  obtain ⟨offF, hframe, hcore⟩ := delAdjSt_iff.mp hdel
  rw [deleteVerts_empty] at hcore
  obtain ⟨hoff0, hoffs, haolen, haoval, hajlen, hmtlen, hdglen⟩ := hframe
  obtain ⟨hdgval, hsound, hcomp⟩ := hcore
  have hNB : N < B := by omega
  have hslot : offF N = slotCount F := offF_eq_slotCount hoff0 hoffs
  have hsq : offF N ≤ N * N := offF_le_sq hoff0 hoffs N le_rfl
  have hsrc : TSrc F offF (σ.arrs ao) (σ.arrs aj) := by
    refine ⟨hoff0, hoffs, haolen, haoval, hajlen, ?_, ?_, ?_⟩
    · intro u t ht
      obtain ⟨w, hadj, hval, -⟩ := hsound u t (by rw [hdgval u]; exact ht)
      exact ⟨w, hadj, hval⟩
    · intro u w hadj
      obtain ⟨t, ht, hval⟩ := hcomp u w hadj
      exact ⟨t, by rw [← hdgval u]; exact ht, hval⟩
    · intro u a b ha hb hab
      exact AdjCore.slot_inj ⟨hdgval, hsound, hcomp⟩ u (by rw [hdgval u]; exact ha)
        (by rw [hdgval u]; exact hb) hab
  -- 1. name the carrier size
  have hrun1 : Run B (.assign "bk.n" (.var nnSrc)) σ (σ.setVar "bk.n" N) 2 := by
    refine (Run.assign (v := N) ?_).mono (by simp)
    rw [← hnsrc]
    exact evalB_var (by omega)
  -- 2. zero the tops
  obtain ⟨σ2, hrun2, ⟨hn2, htplen2, htp2⟩, hv2, ha2, -, -⟩ :=
    (bkZeroCom_spec (a := tp) hNB).frame.run (σ := σ.setVar "bk.n" N)
      ⟨rfl, by simpa using htplen⟩
  have ha2' : ∀ a : String, a ≠ tp → σ2.arrs a = σ.arrs a := by
    intro a hane
    exact ha2 a (by simp [bkZeroCom, Com.warrs, hane])
  -- 3. the transpose
  have hmtlen2 : offF N ≤ (σ2.arrs mt).length := by
    rw [ha2' mt hD.mt']
    exact hmtlen
  obtain ⟨σ3, hrun3, ⟨hn3, hao3, haj3, hmt3, htplen3, htp3, hrows3⟩, hv3, ha3, -, -⟩ :=
    (transCom_spec (Ne.symm hD.am) (Ne.symm hjm) hD.mt' (Ne.symm hD.at')
      (Ne.symm hjt) hsrc hB).frame.run (σ := σ2)
      ⟨hn2, ha2' ao hD.at', ha2' aj hjt, hmtlen2, htplen2, htp2⟩
  have ha3' : ∀ a : String, a ≠ mt → a ≠ tp → σ3.arrs a = σ2.arrs a := by
    intro a h1 h2
    exact ha3 a (by simp [transCom, transOuterBody, transBody, Com.warrs, h1, h2])
  -- 4. zero the tops again
  obtain ⟨σ4, hrun4, ⟨hn4, htplen4, htp4⟩, hv4, ha4, -, -⟩ :=
    (bkZeroCom_spec (a := tp) hNB).frame.run (σ := σ3) ⟨hn3, htplen3⟩
  have ha4' : ∀ a : String, a ≠ tp → σ4.arrs a = σ3.arrs a := by
    intro a hane
    exact ha4 a (by simp [bkZeroCom, Com.warrs, hane])
  -- 5. the rank sentinel
  have hralen4 : N ≤ (σ4.arrs ra).length := by
    rw [ha4' ra hD.rt, ha3' ra (Ne.symm hD.mr) hD.rt, ha2' ra hD.rt]
    exact hralen
  obtain ⟨σ5, hrun5, ⟨hn5, hralen5, hra5⟩, hv5, ha5, -, -⟩ :=
    (peelInit_spec (ra := ra) (nn := "bk.n") (ux := "bk.i") (by decide) hNB).frame.run
      (σ := σ4) ⟨hn4, hralen4⟩
  have ha5' : ∀ a : String, a ≠ ra → σ5.arrs a = σ4.arrs a := by
    intro a hane
    exact ha5 a (by simp [peelInitCom, Com.warrs, hane])
  -- 6. the bucket build
  have hdgF5 : σ5.arrs dg = σ.arrs dg := by
    rw [ha5' dg (Ne.symm hD.rd), ha4' dg hD.dt, ha3' dg (Ne.symm hD.md) hD.dt,
      ha2' dg hD.dt]
  have hdgb : ∀ x, x < N → (σ.arrs dg).getD x 0 < N := by
    intro x hx
    rw [hdgval ⟨x, hx⟩]
    exact ncard_neighborSet_lt F _
  have hdglen5 : N ≤ (σ5.arrs dg).length := by rw [hdgF5]; exact hdglen
  have htplen5 : N ≤ (σ5.arrs tp).length := by
    rw [ha5' tp (Ne.symm hD.rt)]; exact htplen4
  have hsklen5 : N * N + N ≤ (σ5.arrs sk).length := by
    rw [ha5' sk (Ne.symm hD.rs), ha4' sk (Ne.symm hD.ts),
      ha3' sk (Ne.symm hD.ms) (Ne.symm hD.ts), ha2' sk (Ne.symm hD.ts)]
    exact hsklen
  have hdgb5 : ∀ x, x < N → (σ5.arrs dg).getD x 0 < N := by rw [hdgF5]; exact hdgb
  have htp5 : ∀ d, d < N → (σ5.arrs tp).getD d 0 = 0 := by
    rw [ha5' tp (Ne.symm hD.rt)]; exact htp4
  obtain ⟨σ6, hrun6, ⟨hBI6, hi6⟩, hv6, ha6, -, -⟩ :=
    (bkBuildCom_spec hD.ts (Ne.symm hD.ts) hD.dt hD.ds hB).frame.run (σ := σ5)
      ⟨hn5, hdglen5, htplen5, hsklen5, hdgb5, htp5⟩
  have ha6' : ∀ a : String, a ≠ tp → a ≠ sk → σ6.arrs a = σ5.arrs a := by
    intro a h1 h2
    exact ha6 a (by simp [bkBuildCom, bkBuildBody, Com.warrs, h1, h2])
  -- 7, 8. the cursor and the countdown
  have hn6 : σ6.vars "bk.n" = N := hBI6.1
  have hrun7 : Run B (.assign "bk.c" (.lit 0)) σ6 (σ6.setVar "bk.c" 0) 2 :=
    (Run.assign (v := 0) (evalB_lit (by omega))).mono (by simp)
  have hrun8 : Run B (.assign "bk.r" (.var "bk.n")) (σ6.setVar "bk.c" 0)
      ((σ6.setVar "bk.c" 0).setVar "bk.r" N) 2 := by
    refine (Run.assign (v := N) ?_).mono (by simp)
    rw [show N = (σ6.setVar "bk.c" 0).vars "bk.n" from by
      simp only [vars_setVar, String.reduceEq, reduceIte]; exact hn6.symm]
    exact evalB_var (by simp only [vars_setVar, String.reduceEq, reduceIte, hn6]; omega)
  -- the array chain at the loop's entry
  set σ8 : Env := (σ6.setVar "bk.c" 0).setVar "bk.r" N with hσ8def
  have haoF : σ8.arrs ao = σ.arrs ao := by
    show σ6.arrs ao = σ.arrs ao
    rw [ha6' ao hD.at' hD.as, ha5' ao hD.ar, ha4' ao hD.at',
      ha3' ao hD.am hD.at', ha2' ao hD.at']
  have hmtF : σ8.arrs mt = σ3.arrs mt := by
    show σ6.arrs mt = σ3.arrs mt
    rw [ha6' mt hD.mt' hD.ms, ha5' mt hD.mr, ha4' mt hD.mt']
  have hraF : σ8.arrs ra = σ5.arrs ra := by
    show σ6.arrs ra = σ5.arrs ra
    rw [ha6' ra hD.rt hD.rs]
  have hdgF : σ8.arrs dg = σ.arrs dg := by
    show σ6.arrs dg = σ.arrs dg
    rw [ha6' dg hD.dt hD.ds, hdgF5]
  have htpF : σ8.arrs tp = σ6.arrs tp := rfl
  have hskF : σ8.arrs sk = σ6.arrs sk := rfl
  -- the stacks at entry
  have hmL8 : ∀ d, d < N → mLst tp sk N σ8 d
      = (List.range N).filter (fun x => decide ((σ.arrs dg).getD x 0 = d)) := by
    intro d hd
    have h := hBI6.2.2.2.2.2.2 d hd
    rw [hi6, tailFilter_zero] at h
    rw [show mLst tp sk N σ8 d = mLst tp sk N σ6 d from rfl, h,
      ha6' dg hD.dt hD.ds, hdgF5]
  have hmemL8 : ∀ d, d < N → ∀ x ∈ mLst tp sk N σ8 d,
      x < N ∧ (σ.arrs dg).getD x 0 = d := by
    intro d hd x hx
    rw [hmL8 d hd, List.mem_filter, List.mem_range] at hx
    exact ⟨hx.1, decide_eq_true_iff.mp hx.2⟩
  have hndL8 : ∀ d, d < N → (mLst tp sk N σ8 d).Nodup := by
    intro d hd
    rw [hmL8 d hd]
    exact (List.nodup_range).filter _
  have hraSent : ∀ i, i < N → (σ8.arrs ra).getD i 0 = N := by
    intro i hi
    rw [hraF]; exact hra5 i hi
  -- the cell count at entry is the carrier size
  have hcell8 : cellCount tp N σ8 ≤ N := by
    have hfib : (Finset.range N).card
        = ∑ d ∈ Finset.range N,
            ((Finset.range N).filter (fun x => (σ.arrs dg).getD x 0 = d)).card :=
      Finset.card_eq_sum_card_fiberwise
        (fun x hx => Finset.mem_range.mpr (hdgb x (Finset.mem_range.mp hx)))
    have hEach : ∀ d ∈ Finset.range N, (σ8.arrs tp).getD d 0
        = ((Finset.range N).filter (fun x => (σ.arrs dg).getD x 0 = d)).card := by
      intro d hd
      have hdN := Finset.mem_range.mp hd
      have h2 : (mLst tp sk N σ8 d).length = (σ8.arrs tp).getD d 0 := mLst_length
      have htf : (mLst tp sk N σ8 d).toFinset
          = (Finset.range N).filter (fun x => (σ.arrs dg).getD x 0 = d) := by
        ext y
        rw [List.mem_toFinset, hmL8 d hdN]
        simp
      rw [← h2, ← List.toFinset_card_of_nodup (hndL8 d hdN), htf]
    rw [cellCount, Finset.sum_congr rfl hEach, ← hfib, Finset.card_range]
  -- the loop
  have hrows8 : ∀ z : Fin N, (List.range ((F.neighborSet z).ncard)).map
      (fun s => (σ8.arrs mt).getD (offF (z : ℕ) + s) 0) = rowList F z := by
    intro z; rw [hmtF]; exact hrows3 z
  have hr8 : σ8.vars "bk.r" = N := rfl
  have hRSt0 : RSt ao dg mt ra tp sk F offF 0 σ8 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ6.vars "bk.n" = N
      exact hn6
    · rw [hr8]; omega
    · rw [haoF]; exact haolen
    · rw [haoF]; exact haoval
    · rw [hmtF]; exact hmt3
    · rw [hraF]; exact hralen5
    · rw [hdgF]; exact hdglen
    · show N ≤ (σ6.arrs tp).length
      exact hBI6.2.2.2.1
    · show N * N + N ≤ (σ6.arrs sk).length
      exact hBI6.2.2.2.2.1
    · exact hrows8
    · intro x _
      exact hraSent (x : ℕ) x.isLt
    · intro x hx
      rw [bRun_zero, bInit_live] at hx
      exact absurd (Finset.mem_univ x) hx
    · intro x _
      rw [bRun_zero, bInit_live, hdgF, hdgval x, ← card_nbrsIn_univ]
    · rw [hdgF]; exact hdgb
    · intro d hd
      rw [bRun_zero]
      have hself : (mLst tp sk N σ8 d).filter (mOK ra dg N σ8 d)
          = mLst tp sk N σ8 d := by
        refine List.filter_eq_self.mpr ?_
        intro x hx
        obtain ⟨hxN, hxd⟩ := hmemL8 d hd x hx
        rw [mOK, decide_eq_true_iff, mKey, hraSent x hxN, hdgF, hxd]
        simp
      rw [hself, hmL8 d hd]
      refine (bktV_bInit F _ d ?_).symm
      intro u
      rw [hdgval u, card_nbrsIn_univ]
    · intro d hd x hx
      obtain ⟨hxN, hxd⟩ := hmemL8 d hd x hx
      exact ⟨hxN, by rw [hdgF, hxd]⟩
    · exact hndL8
    · intro d hd
      exact tp_le_of_nodup (hndL8 d hd) (fun x hx => (hmemL8 d hd x hx).1)
  have hPinit : PInv ao dg mt ra tp sk F offF σ8 := by
    have hk0 : N - σ8.vars "bk.r" = 0 := by rw [hr8]; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hk0]; exact hRSt0
    · rw [hk0, bRun_zero, bInit_cur, hσ8def]
      simp
    · rw [hr8]
  obtain ⟨σ9, hrun9, hP9, hfalse9⟩ :=
    (peelLoopCom_spec hD hB hoff0 hoffs).run ⟨hPinit, rfl, hcell8⟩
  obtain ⟨hR9, hc9, hr9le⟩ := hP9
  have hr9 : σ9.vars "bk.r" = 0 := by
    have hcond9 : (Cond.lt (.lit 0) (.var "bk.r")).evalB B σ9
        = some (decide (0 < σ9.vars "bk.r")) := by
      refine evalB_condLt (evalB_lit (by omega)) (evalB_var (by omega))
    rw [hcond9] at hfalse9
    have : ¬ (0 < σ9.vars "bk.r") := by simpa using hfalse9
    omega
  rw [hr9, Nat.sub_zero] at hR9
  have hempty : (bRun F N).live = ∅ := by
    rw [← Finset.card_eq_zero, bRun_live_card F N le_rfl]
    omega
  refine ⟨σ9, ((hrun1.seq (hrun2.seq (hrun3.seq (hrun4.seq (hrun5.seq
    (hrun6.seq (hrun7.seq (hrun8.seq hrun9))))))))).mono (by omega), hR9.ralen, ?_⟩
  intro x
  rw [hR9.dead x (by rw [hempty]; exact Finset.notMem_empty x)]
  rfl

/-! ## §8 `CovSelPeelIn` at `bucketSel`, and `covOrderIn_bucket` discharged -/

/-- The peel writes five arrays and nothing else. -/
theorem bucketPeelCom_arrs_eq {ao aj dg mt ra tp sk nnSrc : String} {B K : ℕ}
    {σ σ' : Env} (h : Run B (bucketPeelCom ao aj dg mt ra tp sk nnSrc) σ σ' K)
    (b : String) (h1 : b ≠ ra) (h2 : b ≠ mt) (h3 : b ≠ dg) (h4 : b ≠ tp)
    (h5 : b ≠ sk) : σ'.arrs b = σ.arrs b :=
  h.frame_arr b (by
    simp [bucketPeelCom, bkZeroCom, transCom, transOuterBody, transBody, peelInitCom,
      bkBuildCom, bkBuildBody, peelLoopCom, roundCom, scanCom, scanBody, walkCom,
      walkBody, Com.warrs, h1, h2, h3, h4, h5])

/-- The peel assigns to twelve scratch scalars and nothing else. -/
theorem bucketPeelCom_vars_eq {ao aj dg mt ra tp sk nnSrc : String} {B K : ℕ}
    {σ σ' : Env} (h : Run B (bucketPeelCom ao aj dg mt ra tp sk nnSrc) σ σ' K)
    (y : String) (h1 : y ≠ "bk.n") (h2 : y ≠ "bk.i") (h3 : y ≠ "bk.u")
    (h4 : y ≠ "bk.m") (h5 : y ≠ "bk.t") (h6 : y ≠ "bk.z") (h7 : y ≠ "bk.c")
    (h8 : y ≠ "bk.r") (h9 : y ≠ "bk.f") (h10 : y ≠ "bk.v") (h11 : y ≠ "bk.w")
    (h12 : y ≠ "bk.d") : σ'.vars y = σ.vars y :=
  h.frame_var y (by
    simp [bucketPeelCom, bkZeroCom, transCom, transOuterBody, transBody, peelInitCom,
      bkBuildCom, bkBuildBody, peelLoopCom, roundCom, scanCom, scanBody, walkCom,
      walkBody, Com.wvars, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12])

/-- The arena's two cells survive the peel. -/
theorem arena_vars_eq_of_bucketPeel {ao aj dg mt ra tp sk nnSrc : String} {B K : ℕ}
    {σ σ' : Env} (h : Run B (bucketPeelCom ao aj dg mt ra tp sk nnSrc) σ σ' K)
    (j : ℕ) : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN ∧
      σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS := by
  constructor <;>
    refine bucketPeelCom_vars_eq h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact lv_ne_len4 (by decide) (by decide) (by decide) j

open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

set_option maxHeartbeats 2000000 in
/-- **The peel residual at the bucket selection, discharged at a linear
budget.** `CovSelPeelIn` at `bucketSel`, every clause intact, with
`Kmp j A = 313·A.N + 118·(slot count) + 40` — **no `A.N * A.N` term**.

The scratch the pass asks for is the rank region, the bucket tops
(`n` cells) and the bucket cells (`n² + n` cells: `n` blocks of width
`n`, one per degree, plus the guard slot the push writes at). The
*time* is linear; only the cell block is quadratic in space, and it is
the same shape as the adjacency region the pass reads
(`offF_le_sq`). -/
theorem covSelPeelIn_bucketPeelCom (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO tpO skO : ℕ → String)
    (Ssw : ℕ → Env → Prop) (hq : 1 ≤ q)
    (hnd : ∀ j, Distinct6 (aoO j) (mtO j) (ra j) (dgO j) (tpO j) (skO j))
    (hnj : ∀ j, ajO j ≠ aoO j ∧ ajO j ≠ mtO j ∧ ajO j ≠ ra j ∧ ajO j ≠ dgO j ∧
      ajO j ≠ tpO j ∧ ajO j ≠ skO j)
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ ra j ∧ b ≠ mtO j ∧ b ≠ dgO j ∧ b ≠ tpO j ∧ b ≠ skO j)
    (hSsw : ∀ (j : ℕ) (σ σ' : Env),
      (∀ b : String, b ≠ ra j → b ≠ mtO j → b ≠ dgO j → b ≠ tpO j → b ≠ skO j →
        σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ≠ "bk.n" → y ≠ "bk.i" → y ≠ "bk.u" → y ≠ "bk.m" →
        y ≠ "bk.t" → y ≠ "bk.z" → y ≠ "bk.c" → y ≠ "bk.r" → y ≠ "bk.f" →
        y ≠ "bk.v" → y ≠ "bk.w" → y ≠ "bk.d" → σ'.vars y = σ.vars y) →
      Ssw j σ → Ssw j σ') :
    CovSelPeelIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm ca co ra
      aoO ajO dgO mtO
      (fun j σ => n ≤ (σ.arrs (ra j)).length ∧ n ≤ (σ.arrs (tpO j)).length ∧
        n * n + n ≤ (σ.arrs (skO j)).length)
      Ssw
      (fun j => bucketPeelCom (aoO j) (ajO j) (dgO j) (mtO j) (ra j) (tpO j) (skO j)
        (arenaNames j).nN)
      (fun _ A => linearPeelBudget R 313 118 40 A) := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hAW, hdel, hca, hco, hSmp, hSswσ⟩ := hσ
  obtain ⟨hralen, htplen, hsklen⟩ := hSmp
  obtain ⟨hja, hjm, hjr, hjd, hjt, hjs⟩ := hnj j
  have henc : EncodesGraph x n G := hx.1
  have hlen := henc.length_eq
  have hAN : A.N ≤ n := by
    have h := Fintype.card_le_of_embedding A.up
    simpa using h
  have hBnd : A.N + A.N * A.N + 1 < mcB q x := by
    have h1 : A.N * A.N ≤ n * n := Nat.mul_le_mul hAN hAN
    have h2 : (x.length + 1) * (x.length + 1) ≤ mcB q x := by
      rw [mcB, pow_two]
      exact Nat.le_mul_of_pos_left _ hq
    have h3 : n * n + n + 1 < (x.length + 1) * (x.length + 1) := by nlinarith
    omega
  have hnN : σ.vars (arenaNames j).nN = A.N := hAW.n_eq
  have hsk' : A.N * A.N + A.N ≤ (σ.arrs (skO j)).length := by
    have h1 : A.N * A.N ≤ n * n := Nat.mul_le_mul hAN hAN
    omega
  obtain ⟨σ', hrun, hrank⟩ :=
    (bucketPeelCom_spec (hnd j) hja hjm hjr hjd hjt hjs hBnd
      (F := (selChain (bucketSel A.N) A.G R).toGraph)).run
      ⟨hdel, le_trans hAN hralen, le_trans hAN htplen, hsk', hnN⟩
  have hlenEq := run_arrs_length_eq hrun
  have harrs : ∀ b : String, b ≠ ra j → b ≠ mtO j → b ≠ dgO j → b ≠ tpO j →
      b ≠ skO j → σ'.arrs b = σ.arrs b :=
    fun b h1 h2 h3 h4 h5 => bucketPeelCom_arrs_eq hrun b h1 h2 h3 h4 h5
  have hvars : ∀ y : String, y ≠ "bk.n" → y ≠ "bk.i" → y ≠ "bk.u" → y ≠ "bk.m" →
      y ≠ "bk.t" → y ≠ "bk.z" → y ≠ "bk.c" → y ≠ "bk.r" → y ≠ "bk.f" →
      y ≠ "bk.v" → y ≠ "bk.w" → y ≠ "bk.d" → σ'.vars y = σ.vars y :=
    fun y => bucketPeelCom_vars_eq hrun y
  obtain ⟨hnNeq, hnSeq⟩ := arena_vars_eq_of_bucketPeel hrun j
  refine ⟨σ', hrun, ?_, hrank, ?_, ?_, hSsw j σ σ' harrs hlenEq hvars hSswσ⟩
  · refine arenaStW_of_eq hAW hnNeq hnSeq ?_ ?_ ?_ ?_ ?_
    · obtain ⟨k1, k2, k3, k4, k5⟩ := harn j _ (Or.inl rfl)
      exact harrs _ k1 k2 k3 k4 k5
    · obtain ⟨k1, k2, k3, k4, k5⟩ := harn j _ (Or.inr (Or.inl rfl))
      exact harrs _ k1 k2 k3 k4 k5
    · obtain ⟨k1, k2, k3, k4, k5⟩ := harn j _ (Or.inr (Or.inr (Or.inl rfl)))
      exact harrs _ k1 k2 k3 k4 k5
    · obtain ⟨k1, k2, k3, k4, k5⟩ := harn j _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      exact harrs _ k1 k2 k3 k4 k5
    · obtain ⟨k1, k2, k3, k4, k5⟩ := harn j _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      exact harrs _ k1 k2 k3 k4 k5
  · rw [hlenEq (ca j)]; exact hca
  · rw [hlenEq (co j)]; exact hco

open Lax3Proofs.CoverRoutine (selOrderingRoutine)

set_option maxHeartbeats 1000000 in
/-- **`covOrderIn_bucket` with its hypothesis discharged.** The whole
ordering pass — augmentation then static-adjacency bucket peel — meets
`CovOrderIn` at `selOrderingRoutine bucketSel R` and the budget
`Kag + (313·A.N + 118·m + 40)`, linear in the carrier and the slot
count with **no `A.N * A.N` term**. Wave 26 left this conditional on a
peel program; this is that program. -/
theorem covOrderIn_bucketPeel (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO tpO skO : ℕ → String)
    (Sag Ssw : ℕ → Env → Prop) (agC : ℕ → Com)
    (Kag : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hq : 1 ≤ q)
    (hnd : ∀ j, Distinct6 (aoO j) (mtO j) (ra j) (dgO j) (tpO j) (skO j))
    (hnj : ∀ j, ajO j ≠ aoO j ∧ ajO j ≠ mtO j ∧ ajO j ≠ ra j ∧ ajO j ≠ dgO j ∧
      ajO j ≠ tpO j ∧ ajO j ≠ skO j)
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ ra j ∧ b ≠ mtO j ∧ b ≠ dgO j ∧ b ≠ tpO j ∧ b ≠ skO j)
    (hSsw : ∀ (j : ℕ) (σ σ' : Env),
      (∀ b : String, b ≠ ra j → b ≠ mtO j → b ≠ dgO j → b ≠ tpO j → b ≠ skO j →
        σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ≠ "bk.n" → y ≠ "bk.i" → y ≠ "bk.u" → y ≠ "bk.m" →
        y ≠ "bk.t" → y ≠ "bk.z" → y ≠ "bk.c" → y ≠ "bk.r" → y ≠ "bk.f" →
        y ≠ "bk.v" → y ≠ "bk.w" → y ≠ "bk.d" → σ'.vars y = σ.vars y) →
      Ssw j σ → Ssw j σ')
    (hag : CovAugAdjSelIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm
      ca co aoO ajO dgO mtO Sag
      (fun j σ => n ≤ (σ.arrs (ra j)).length ∧ n ≤ (σ.arrs (tpO j)).length ∧
        n * n + n ≤ (σ.arrs (skO j)).length) Ssw agC Kag) :
    CovOrderIn C hC φ (selOrderingRoutine (fun m => bucketSel m) R) G c w q ℓp
      htabF hbf Adm ca co ra
      (fun j σ => Sag j σ ∧ (n ≤ (σ.arrs (ra j)).length ∧
        n ≤ (σ.arrs (tpO j)).length ∧ n * n + n ≤ (σ.arrs (skO j)).length)) Ssw
      (fun j => .seq (agC j)
        (bucketPeelCom (aoO j) (ajO j) (dgO j) (mtO j) (ra j) (tpO j) (skO j)
          (arenaNames j).nN))
      (fun j A => Kag j A + linearPeelBudget R 313 118 40 A) :=
  covOrderIn_bucket C hC φ R G c w q ℓp htabF hbf Adm ca co ra aoO ajO dgO mtO
    Sag _ Ssw agC _ Kag 313 118 40 hag
    (covSelPeelIn_bucketPeelCom C hC φ R G c w q ℓp htabF hbf Adm ca co ra
      aoO ajO dgO mtO tpO skO Ssw hq hnd hnj harn hSsw)

end Lax3Proofs.Prog

/-! ## §9 Axiom audit

Everything above rests on the three standard axioms alone. The two §8
statements pass through `Headline.headlineSetup` and therefore — exactly
like the landed `covOrderIn_bucket` they apply — additionally carry
Lax12's endorsed `uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms Lax3Proofs.Prog.transCom_spec

#print axioms Lax3Proofs.Prog.bkBuildCom_spec

#print axioms Lax3Proofs.Prog.scanCom_run

#print axioms Lax3Proofs.Prog.walkCom_spec

#print axioms Lax3Proofs.Prog.round_bkts

#print axioms Lax3Proofs.Prog.roundCom_run

#print axioms Lax3Proofs.Prog.peelLoopCom_spec

#print axioms Lax3Proofs.Prog.bucketPeelCom_spec

#print axioms Lax3Proofs.Prog.covSelPeelIn_bucketPeelCom

#print axioms Lax3Proofs.Prog.covOrderIn_bucketPeel
