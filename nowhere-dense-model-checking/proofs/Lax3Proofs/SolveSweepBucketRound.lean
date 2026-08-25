import Lax3Proofs.SolveSweepBucketProg

/-!
# F6c13c (completion) — the round program: a static-adjacency bucket
peel, and `CovSelPeelIn` at `bucketSel` in linear time

Wave 26 (`SolveSweepBucketProg`) built the bucket machinery — the
replay `bRun`, the selection `bucketSel` it names, the loop rule
`peelLoop_linear_bucket` — and left `covOrderIn_bucket` conditional on
one hypothesis: that some IMP+ program meets `CovSelPeelIn` at
`bucketSel` and a *linear* budget. This file writes that program and
discharges the hypothesis.

## The design, and why it is forced

**The peel never writes the adjacency arrays.** Wave 23's `delAdjCom`
is a swap-delete — `adjCore_unlink` moves the row's last live entry
into the hole — and `AdjDeleteInW`'s postcondition is again just a
`DelAdjSt`, which carries **no row-order clause**
(`not_sortedAdjSt_of_delAdjSt`). So a peel that compacts its rows loses
the one thing the replay needs: that the rows are a function of `G`.
`delAdjCom` is therefore not used below, and a round walks `v`'s
**original** row. The price is that the round is charged `|N_F(v)|`
rather than `v`'s current degree, which is exactly what wave 25's
`staticPot` pays for — at the same linear total, since both potentials
start at `slotCount F`.

One counting sort at entry makes the rows a function of `G` for the
whole run. It is a **transpose**, not a per-row sort: scanning `u`
upward and appending `u` to the new row of each of its neighbours costs
`O(N + m)` and leaves every new row strictly ascending, because `u`
ascends. The sorted rows are written into the `mt` array — the mate
pointers are dead the moment `delAdjCom` is refused, and `mt` is
already exactly `offF N` wide.

## What is here

* **§1 the bucket stacks.** Bucket `d` is the array segment
  `sk[d·N .. d·N + tp[d])`, read head-last, so a push and a pop are one
  store and one increment (`mLst_push`, `mLst_pop`, `mLst_frame`). The
  stacks are **lazily** cleaned: when a vertex's degree drops it is
  pushed into its new bucket and its entry in the old one is left to be
  skipped. `mOK` is the staleness test — live *and* at the right
  current degree — folded into one comparison the way `peelKey` folds
  its two.

* **§2 the amortization at lazy deletion.**
  `peelLoop_linear_static_cursor_lazy` is wave 25's rule with a fourth
  potential term `f·(cells in the stacks)`, and
  `peelLoop_linear_bucket_lazy` is wave 26's `peelLoop_linear_bucket`
  at it. The fourth term is what wave 26's rule cannot carry: a round's
  stale-skipping is bounded by the *pushes of earlier rounds*, not by
  its own `|N_F(v)|`, so it has to be charged to a potential of its
  own. Total pushes are `N + slotCount F`, so the term is linear and
  the budget's shape is unchanged.

* **§3–§6 the program**, phase by phase: the zeroing pass, the
  transpose, the bucket build, and the round (scan, pop, countdown,
  row walk).

* **§7 the pass**, `bucketPeelCom`, and **§8** `CovSelPeelIn` at
  `bucketSel` and `covOrderIn_bucket` with its hypothesis discharged.

## Conventions that are not optional

The countdown is `selRankAux_peel_step`'s, pinned by `selRank_bPop`:
the vertex popped at round `k` gets `N - k - 1`. The degrees in the
buckets are **current** degrees (the `dg` array, decremented in place);
the row a round walks is the **original** row (the `mt` transpose, at
the *base* offsets `ao`, whose length is read as `ao[v+1] - ao[v]` so
that `dg` is free to hold the current degree). The cursor is never
reset: it falls by exactly one a round and is licensed by
`minDeg_le_minDeg_erase_succ` through `bRun_round`.
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

end Lax3Proofs.Prog
