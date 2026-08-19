import Lax3Proofs.SolveBlocksBot

/-!
# F6c/3 — block 0's IMP+ table fill, discharged

`SolveBlocksBot` landed §6.4's schedule abstractly: the packed row
codes (`rowCode`), the representative table (`firsts`, one `O(N·L)`
scan's worth of data, `≤ 2^L·(K+1)` cells), the table-read candidate
completion (`tableReps`, exactly `Impl.FirstRep` by
`mem_tableReps_iff`), and the table-scheduled evaluator `botEvalT`
with `botEvalT_eq_botEval`/`botEvalT_eq_sat`. This file is the machine
half: the IMP+ programs that build the table and fill block 0's
`TableBits` region with `botEvalT`'s bits, and their discharged
`Spec`s.

* **The table build** (`buildCom`): one pass over the color-bit region
  (`ColBits`, rows at stride `L`), computing each vertex's `rowCode`
  by `L` unrolled bit reads (`rowCodeCom` — the machine's
  `codeAux`), and appending the vertex to its row's `firsts` list
  while a seat is free. `buildCom_spec`: the count region `na` and
  the seat region `fa` end holding `firsts` verbatim (`FirstsSt`),
  from nothing but the lengths — the pass zeroes its own count region
  (`2^L` cells, a schedule-constant prologue).
* **The per-entry evaluator** (`evalCom`): the compile-time structural
  recursion over the formula — the same move `SolveMatTop.bcExpr`
  makes for the root combination, here over `DistFO`. Atoms are env
  reads and one row-bit read; `not`/`and` are a flip and a
  short-circuit; a quantifier is an **unrolled** candidate loop: the
  `k` environment entries, then per row code `ρ < 2^L` the first
  `K+1` seats of `firsts ρ` scanned for the first off-environment
  entry (`seatCom` — the machine's `find? (offEnv m)`), the found
  candidate tried through the env scratch cell `k`. The env scratch
  (`ea`, `K+1` cells) and the per-depth accumulator scratch (`xa`,
  `K+1` cells) are **self-cleaned**: `evalCom`'s `Spec` returns both
  regions exactly as it found them (the campaign's seam rule — the
  caller never owes a wipe). `evalCom_spec`: `"bt.r"` ends holding
  `botEvalT`'s bit, within `evalK` — a cost of `(L, K, φ)` alone,
  carrier-free. The depth budget `k + qdepth φ ≤ K + 1` is threaded
  hypothesis-to-hypothesis through the recursion: each quantifier
  case consumes one unit (`qdepth` drops by one as `k` grows by
  one), so every `mem_tableReps_iff`/`botEvalT` obligation below
  receives exactly the instance it needs.
* **The block** (`botCom`): load the carrier size, wipe the two
  scratch regions, build the table, then the fill loop over `(v, β ∈
  Fl)` writing `TableBits` — `β` runs over the level's schedule
  family as a compile-time list, so the per-vertex body is `|Fl|`
  unrolled evaluator calls. **`botCom_spec`**: from `ArenaSt` at an
  **edgeless** arena (`A.G = ⊥` is a hypothesis — the dead edged
  branch is the frame chain's guard, `mkSetup_memLeaf_eq_bot`; no
  machine-side edge scan exists here), the table region ends holding
  exactly the `Sat A.G`-values of the family — the value
  `Driver.tablesAux`'s leaf returns, through
  `Impl.tablesAux_bot_eq_botEval` + `botEvalT_eq_botEval`, landed
  here through `botEvalT_eq_sat`. The arena contract is returned
  intact.

## The budget, named (botC's `(1 + |ℱ_j|)·‖A‖` shape)

`botComK N L K Fl = buildK N L + fillK N L K Fl + 6K + 10`:

* `buildK N L = 3·2^L + (11L + 30)·N + 7` — **the one `N·L` build
  pass** (`11L + 30` per vertex: the `L` unrolled bit reads and the
  seat append) plus the `2^L` count wipe;
* `fillK N L K Fl = (|Fl|·(evalKMax + 7) + 15)·N + 6` — **a
  schedule constant per `(v, β)` entry**: `evalKMax` bounds `evalK`
  over the family, and `evalK` is defined by recursion on the formula
  from `(L, K)` alone — no occurrence of the carrier;
* the remainder is the two `K+1`-cell scratch wipes.

`botComK_le` closes the envelope at one schedule constant times
`(1 + |Fl|)·(N + 1)` — `botC`'s shape at `weight A ≥ N` (the leaf
block reads no edges, so the CSR does not enter its cost at all).

## Stored values (`mcB`, cited at the writes)

Everything this block stores is a row code (`< 2^L`, a schedule
constant — `rowCode_lt`, cited at the count writes), a seat count
(`≤ K+1`), a vertex name (`< N` — the seat and env writes), a bit
(`≤ 1` — the table writes), or an index below one of `N·L`,
`2^L·(K+1)`, `N·|Fl|`. The four explicit `< B` hypotheses
(`hNB/hNLB/h2LB/hTBB`) are exactly these classes; at `B := mcB q x`
they are the head file's stored-value arithmetic (`N ≤ n₀ ≤ |x|`,
everything else schedule-constant), discharged by F7 once.

## Division of labour

Names are parameters throughout (`na` counts, `fa` seats, `ea` env,
`xa` accumulators; the color rows and the table are the contract's
`nm.col`/`nm.tab`), with the distinctness hypotheses
`decide`-dischargeable at F7's concrete names; the fixed scratch
scalars are `btScalars`. Nothing here touches the frame blocks, the
scatter routine, or `proofs/Lax3Proofs.lean`.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (arrOf_getD getD_eq_getElem)
open Lax3.DistFO

/-! ## §1 Sequencing an unrolled pass -/

/-- A compile-time pass: one command per list element, positions
threaded — `seqIdx gen l k` is `gen k l[0]; gen (k+1) l[1]; …`. Every
unrolled loop of this file (candidate trials, seat scans, row-bit
reads, the schedule family's entries) is one of these. -/
def seqIdx {α : Type*} (gen : ℕ → α → Com) : List α → ℕ → Com
  | [], _ => .skip
  | a :: s, k => .seq (gen k a) (seqIdx gen s (k + 1))

theorem seqIdx_nil {α : Type*} (gen : ℕ → α → Com) (k : ℕ) :
    seqIdx gen [] k = .skip := rfl

theorem seqIdx_cons {α : Type*} (gen : ℕ → α → Com) (a : α) (s : List α) (k : ℕ) :
    seqIdx gen (a :: s) k = .seq (gen k a) (seqIdx gen s (k + 1)) := rfl

/-- The pass writes only scalars its steps write. -/
theorem wvars_seqIdx {α : Type*} {gen : ℕ → α → Com} {W : List String}
    (h : ∀ i a, (gen i a).wvars ⊆ W) :
    ∀ (l : List α) (k : ℕ), (seqIdx gen l k).wvars ⊆ W
  | [], _ => by simp [seqIdx]
  | a :: s, k => by
      rw [seqIdx_cons]
      show ((gen k a).wvars ++ (seqIdx gen s (k + 1)).wvars) ⊆ W
      exact List.append_subset.mpr ⟨h k a, wvars_seqIdx h s (k + 1)⟩

/-- The pass stores only into arrays its steps store into. -/
theorem warrs_seqIdx {α : Type*} {gen : ℕ → α → Com} {W : List String}
    (h : ∀ i a, (gen i a).warrs ⊆ W) :
    ∀ (l : List α) (k : ℕ), (seqIdx gen l k).warrs ⊆ W
  | [], _ => by simp [seqIdx]
  | a :: s, k => by
      rw [seqIdx_cons]
      show ((gen k a).warrs ++ (seqIdx gen s (k + 1)).warrs) ⊆ W
      exact List.append_subset.mpr ⟨h k a, warrs_seqIdx h s (k + 1)⟩

theorem noWrite_seqIdx {α : Type*} {gen : ℕ → α → Com}
    (h : ∀ i a, (gen i a).NoWrite) :
    ∀ (l : List α) (k : ℕ), (seqIdx gen l k).NoWrite
  | [], _ => by simp [seqIdx, Com.NoWrite]
  | a :: s, k => by
      rw [seqIdx_cons]
      exact ⟨h k a, noWrite_seqIdx h s (k + 1)⟩

theorem not_reads_seqIdx {α : Type*} {gen : ℕ → α → Com}
    (h : ∀ i a, ¬ (gen i a).reads) :
    ∀ (l : List α) (k : ℕ), ¬ (seqIdx gen l k).reads
  | [], _ => by simp [seqIdx]
  | a :: s, k => by
      rw [seqIdx_cons]
      show ¬ ((gen k a).reads ∨ (seqIdx gen s (k + 1)).reads)
      exact not_or.mpr ⟨h k a, not_reads_seqIdx h s (k + 1)⟩

/-- **The pass's `Spec`**, threaded through a position-indexed
invariant: if step `i` carries `Inv i` to `Inv (i + 1)` within `Kb`,
the pass carries `Inv k` to `Inv (k + l.length)` within
`l.length·Kb + 1`. -/
theorem seqIdx_spec {α : Type*} {B Kb : ℕ} {gen : ℕ → α → Com}
    (Inv : ℕ → Env → Prop) :
    ∀ (l : List α) (k : ℕ),
      (∀ i (hi : i < l.length),
        Spec B (Inv (k + i)) (gen (k + i) l[i])
          (fun _ σ' => Inv (k + i + 1) σ') Kb) →
      Spec B (Inv k) (seqIdx gen l k)
        (fun _ σ' => Inv (k + l.length) σ') (l.length * Kb + 1) := by
  intro l
  induction l with
  | nil =>
    intro k _
    rw [seqIdx_nil]
    exact Spec.skip.post (fun σ σ' hσ hq => by
      rw [hq]; simpa using hσ) |>.mono (by simp)
  | cons a s ih =>
    intro k h
    rw [seqIdx_cons]
    have h0 : Spec B (Inv k) (gen k a) (fun _ σ' => Inv (k + 1) σ') Kb := by
      have := h 0 (by simp)
      simpa using this
    have hs : Spec B (Inv (k + 1)) (seqIdx gen s (k + 1))
        (fun _ σ' => Inv (k + 1 + s.length) σ') (s.length * Kb + 1) := by
      refine ih (k + 1) (fun i hi => ?_)
      have := h (i + 1) (by simpa using Nat.succ_lt_succ hi)
      have he : k + (i + 1) = k + 1 + i := by omega
      rw [he] at this
      simpa using this
    have hseq := h0.seq hs (fun _ σ' _ hq => hq)
      (fun σ σ' σ'' _ _ hq => show Inv (k + (a :: s).length) σ'' by
        have he : k + (a :: s).length = k + 1 + s.length := by
          simp; omega
        rw [he]; exact hq)
    refine hseq.mono ?_
    have : (a :: s).length * Kb = s.length * Kb + Kb := by
      simp [Nat.succ_mul]
    omega

/-! ## §2 Small helpers -/

private theorem getElem?_eq_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem h]

/-- Two `ℕ`-lists agreeing in length and pointwise `getD` are equal. -/
private theorem eq_of_getD {l l' : List ℕ} (hlen : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i 0 = l'.getD i 0) : l = l' := by
  refine List.ext_getElem hlen (fun i h₁ h₂ => ?_)
  have := h i h₁
  rwa [getD_eq_getElem h₁, getD_eq_getElem h₂] at this

/-- The strided seat index is injective in `(ρ, s)` while the seat is
in range: the machine's `2^L × (K+1)` table is genuinely
two-dimensional. -/
private theorem seatIdx_inj {K ρ ρ' s s' : ℕ} (hs : s < K + 1) (hs' : s' < K + 1)
    (h : ρ * (K + 1) + s = ρ' * (K + 1) + s') : ρ = ρ' ∧ s = s' := by
  have key : ρ = ρ' := by
    rcases Nat.lt_trichotomy ρ ρ' with hlt | heq | hgt
    · exfalso
      have h1 : ρ * (K + 1) + (K + 1) ≤ ρ' * (K + 1) := by
        have h2 := Nat.mul_le_mul_right (K + 1) (Nat.succ_le_of_lt hlt)
        rwa [Nat.succ_mul] at h2
      omega
    · exact heq
    · exfalso
      have h1 : ρ' * (K + 1) + (K + 1) ≤ ρ * (K + 1) := by
        have h2 := Nat.mul_le_mul_right (K + 1) (Nat.succ_le_of_lt hgt)
        rwa [Nat.succ_mul] at h2
      omega
  subst key
  omega

/-- `find?` on one more element, when the prefix failed. -/
private theorem find?_take_succ_of_none {α : Type*} {p : α → Bool} {l : List α}
    {s : ℕ} (h : (l.take s).find? p = none) (hs : s < l.length) :
    (l.take (s + 1)).find? p = if p l[s] then some l[s] else none := by
  rw [List.take_add_one, List.find?_append, h]
  rw [List.getElem?_eq_getElem hs]
  cases hp : p l[s] <;> simp [List.find?, hp]

/-- `find?` is stable under extending the prefix once it has found. -/
private theorem find?_take_succ_of_some {α : Type*} {p : α → Bool} {l : List α}
    {s : ℕ} {u : α} (h : (l.take s).find? p = some u) :
    (l.take (s + 1)).find? p = some u := by
  rw [List.take_add_one, List.find?_append, h, Option.some_or]

/-! ## §3 The scratch names and regions -/

/-- The scalars the evaluator may write: result, found flag, seat
candidate, off-env flag, found candidate, seat count. -/
def evalWScalars : List String := ["bt.r", "bt.f", "bt.x", "bt.o", "bt.w", "bt.d"]

/-- All of block 0's scratch scalars: the evaluator's, the row-code
accumulator, the vertex counter, the carrier size. -/
def btScalars : List String :=
  ["bt.r", "bt.f", "bt.x", "bt.o", "bt.w", "bt.d", "bt.c", "bt.v", "bt.n"]

theorem evalWScalars_subset_btScalars : evalWScalars ⊆ btScalars := by decide

variable {N Lc : ℕ}

/-- The environment region's cell function: entries of `m` below `k`,
zero above — the self-cleaned shape the evaluator receives and
returns. -/
def envFun {k : ℕ} (m : Fin k → Fin N) : ℕ → ℕ :=
  fun i => if h : i < k then (m ⟨i, h⟩ : ℕ) else 0

theorem envFun_lt {k : ℕ} (m : Fin k → Fin N) {i : ℕ} (h : i < k) :
    envFun m i = (m ⟨i, h⟩ : ℕ) := dif_pos h

theorem envFun_ge {k : ℕ} (m : Fin k → Fin N) {i : ℕ} (h : k ≤ i) :
    envFun m i = 0 := dif_neg (by omega)

theorem envFun_lt_bound {B k : ℕ} (m : Fin k → Fin N) (i : ℕ) (hNB : N < B) :
    envFun m i < B := by
  unfold envFun
  split
  · exact lt_trans (Fin.is_lt _) hNB
  · omega

/-- Writing the candidate into the scratch cell `k` is exactly the
`Fin.snoc` extension of the environment. -/
theorem envFun_snoc {k : ℕ} (m : Fin k → Fin N) (w : Fin N) :
    upd (envFun m) k (w : ℕ) = envFun (Fin.snoc m w) := by
  funext i
  rw [upd_apply]
  rcases Nat.lt_trichotomy i k with h | rfl | h
  · rw [if_neg (by omega), envFun_lt m h, envFun_lt (Fin.snoc m w) (by omega)]
    have hc : (⟨i, by omega⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, h⟩ := rfl
    rw [hc, Fin.snoc_castSucc]
  · rw [if_pos rfl, envFun_lt (Fin.snoc m w) (by omega)]
    have hc : (⟨i, by omega⟩ : Fin (i + 1)) = Fin.last i := rfl
    rw [hc, Fin.snoc_last]
  · rw [if_neg (by omega), envFun_ge m (by omega), envFun_ge (Fin.snoc m w) (by omega)]

/-- Cleaning the scratch cell `k` returns the environment to `m`. -/
theorem envFun_unsnoc {k : ℕ} (m : Fin k → Fin N) (w : Fin N) :
    upd (envFun (Fin.snoc m w)) k 0 = envFun m := by
  funext i
  rw [upd_apply, ← envFun_snoc m w, upd_apply]
  rcases Nat.lt_trichotomy i k with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_pos rfl, envFun_ge m (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), envFun_ge m (by omega)]

/-- The color rows as the machine's bit region, at the `Bool` rows the
landed evaluator is stated over: entry `v·L + c` is the bit of
`colB v c`. (`ColBits_rowBits` bridges from the contract's `ColBits`.) -/
def RowBits (ca : String) (colB : Fin N → Fin Lc → Bool) (σ : Env) : Prop :=
  (σ.arrs ca).length = N * Lc ∧
    ∀ (v : Fin N) (c : Fin Lc),
      (σ.arrs ca).getD ((v : ℕ) * Lc + (c : ℕ)) 0 = if colB v c then 1 else 0

open Lax3.ColoredGraphs in
open Classical in
/-- The contract's color region is the machine's bit region at the
decided rows — the `colB`/`hcol` pair every landed `SolveBlocksBot`
statement consumes. -/
theorem ColBits_rowBits {ca : String} {col : Coloring N Lc} {σ : Env}
    (h : ColBits ca col σ) :
    RowBits ca (fun v c => decide (v ∈ col c)) σ := by
  refine ⟨h.1, fun v c => ?_⟩
  rw [h.2 v c]
  by_cases hm : v ∈ col c
  · rw [if_pos hm, if_pos (by simpa using hm)]
  · rw [if_neg hm, if_neg (by simpa using hm)]

/-- **The representative table's region contract**: the count region
holds each row code's `firsts` length, the seat region holds its
entries in order at stride `K+1`. This is what one build pass
establishes and every evaluator read consumes. -/
def FirstsSt (na fa : String) (colB : Fin N → Fin Lc → Bool) (K : ℕ)
    (σ : Env) : Prop :=
  (σ.arrs na).length = 2 ^ Lc ∧ (σ.arrs fa).length = 2 ^ Lc * (K + 1) ∧
    ∀ ρ, ρ < 2 ^ Lc →
      (σ.arrs na).getD ρ 0 = (firsts colB K ρ).length ∧
      ∀ s, (hs : s < (firsts colB K ρ).length) →
        (σ.arrs fa).getD (ρ * (K + 1) + s) 0 = ((firsts colB K ρ)[s] : ℕ)

/-- A row's table list is at most `K+1` long — its seat indices stay
inside the stride. -/
theorem firsts_length_le (colB : Fin N → Fin Lc → Bool) (K ρ : ℕ) :
    (firsts colB K ρ).length ≤ K + 1 := by
  rw [firsts]
  exact (List.length_take_le _ _)

/-- **The evaluator's state contract** at environment `m`: the two
table regions, the env region holding exactly `m` (zeros above), and
the accumulator region zero from depth `k` up. -/
def EvalSt (ca na fa ea xa : String) (colB : Fin N → Fin Lc → Bool) (K : ℕ)
    {k : ℕ} (m : Fin k → Fin N) (σ : Env) : Prop :=
  RowBits ca colB σ ∧ FirstsSt na fa colB K σ ∧
    σ.arrs ea = arrOf (K + 1) (envFun m) ∧
    (σ.arrs xa).length = K + 1 ∧
    ∀ i, k ≤ i → (σ.arrs xa).getD i 0 = 0

/-- The evaluator's state, mid-quantifier: the accumulator cell of the
*current* depth is live, only the deeper cells are owed as zero. This
is what one candidate trial preserves. -/
def TrialSt (ca na fa ea xa : String) (colB : Fin N → Fin Lc → Bool) (K : ℕ)
    {k : ℕ} (m : Fin k → Fin N) (σ : Env) : Prop :=
  RowBits ca colB σ ∧ FirstsSt na fa colB K σ ∧
    σ.arrs ea = arrOf (K + 1) (envFun m) ∧
    (σ.arrs xa).length = K + 1 ∧
    ∀ i, k + 1 ≤ i → (σ.arrs xa).getD i 0 = 0

theorem EvalSt.trialSt {ca na fa ea xa : String} {colB : Fin N → Fin Lc → Bool}
    {K k : ℕ} {m : Fin k → Fin N} {σ : Env}
    (h : EvalSt ca na fa ea xa colB K m σ) :
    TrialSt ca na fa ea xa colB K m σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun i hi => h.2.2.2.2 i (by omega)⟩

/-- **One candidate's footprint** (the composable postcondition): the
env region is returned verbatim, the accumulator cell `k` is forced to
`1` exactly when the candidate's bit `b` is set, every other cell and
region and every non-scratch scalar is untouched. `b₁ || b₂` composes
(`TrialPost.trans`), which is what folds the unrolled candidate loop. -/
def TrialPost (ea xa : String) (k : ℕ) (b : Bool) (σ σ' : Env) : Prop :=
  σ'.arrs ea = σ.arrs ea ∧
    (σ'.arrs xa).getD k 0 = (if b then 1 else (σ.arrs xa).getD k 0) ∧
    (∀ i, i ≠ k → (σ'.arrs xa).getD i 0 = (σ.arrs xa).getD i 0) ∧
    (σ'.arrs xa).length = (σ.arrs xa).length ∧
    (∀ a, a ≠ ea → a ≠ xa → σ'.arrs a = σ.arrs a) ∧
    (∀ y, y ∉ evalWScalars → σ'.vars y = σ.vars y)

theorem TrialPost.rfl {ea xa : String} {k : ℕ} {σ : Env} :
    TrialPost ea xa k false σ σ := by
  refine ⟨_root_.rfl, ?_, fun _ _ => _root_.rfl, _root_.rfl,
    fun _ _ _ => _root_.rfl, fun _ _ => _root_.rfl⟩
  simp

theorem TrialPost.trans {ea xa : String} {k : ℕ} {b₁ b₂ : Bool} {σ σ' σ'' : Env}
    (h₁ : TrialPost ea xa k b₁ σ σ') (h₂ : TrialPost ea xa k b₂ σ' σ'') :
    TrialPost ea xa k (b₁ || b₂) σ σ'' := by
  obtain ⟨he₁, hk₁, hi₁, hl₁, ha₁, hv₁⟩ := h₁
  obtain ⟨he₂, hk₂, hi₂, hl₂, ha₂, hv₂⟩ := h₂
  refine ⟨he₂.trans he₁, ?_, fun i hi => (hi₂ i hi).trans (hi₁ i hi),
    hl₂.trans hl₁, fun a h1 h2 => (ha₂ a h1 h2).trans (ha₁ a h1 h2),
    fun y hy => (hv₂ y hy).trans (hv₁ y hy)⟩
  rw [hk₂, hk₁]
  cases b₁ <;> cases b₂ <;> simp

/-- The mid-quantifier state survives one candidate's footprint. -/
theorem TrialSt.of_post {ca na fa ea xa : String} {colB : Fin N → Fin Lc → Bool}
    {K k : ℕ} {m : Fin k → Fin N} {b : Bool} {σ σ' : Env}
    (hca : ca ≠ ea) (hca' : ca ≠ xa) (hna : na ≠ ea) (hna' : na ≠ xa)
    (hfa : fa ≠ ea) (hfa' : fa ≠ xa)
    (h : TrialSt ca na fa ea xa colB K m σ)
    (hp : TrialPost ea xa k b σ σ') :
    TrialSt ca na fa ea xa colB K m σ' := by
  obtain ⟨hrow, hfst, henv, hxl, hxz⟩ := h
  obtain ⟨he, _, hi, hl, ha, _⟩ := hp
  refine ⟨?_, ?_, he.trans henv, hl.trans hxl, fun i hik => ?_⟩
  · rw [RowBits, ha ca hca hca']
    exact hrow
  · rw [FirstsSt, ha na hna hna', ha fa hfa hfa']
    exact hfst
  · rw [hi i (by omega)]
    exact hxz i hik

/-! ## §4 The programs -/

/-- Set `"bt.o"` to the off-environment bit of the candidate held in
`"bt.x"`: `1`, then one unrolled equality test per environment entry. -/
def offEnvCom (ea : String) (k : ℕ) : Com :=
  .seq (.assign "bt.o" (.lit 1))
    (seqIdx (fun i _ =>
        .ite (.eq (.get ea (.lit i)) (.var "bt.x"))
          (.assign "bt.o" (.lit 0)) .skip)
      (List.range k) 0)

/-- One seat of row code `ρ`'s scan (the machine's
`find? (offEnv m)`): while nothing is found and the seat is occupied
(`s < "bt.d"`, the row's count), read the seat into `"bt.x"`, test it
against the environment, and record the first success in
`"bt.f"`/`"bt.w"`. -/
def seatCom (fa ea : String) (K k ρ s : ℕ) : Com :=
  .ite (.eq (.var "bt.f") (.lit 0))
    (.ite (.lt (.lit s) (.var "bt.d"))
      (.seq (.assign "bt.x" (.get fa (.lit (ρ * (K + 1) + s))))
        (.seq (offEnvCom ea k)
          (.ite (.eq (.var "bt.o") (.lit 1))
            (.seq (.assign "bt.f" (.lit 1)) (.assign "bt.w" (.var "bt.x")))
            .skip)))
      .skip)
    .skip

/-- Try one candidate (the expression `e`): write it into the env
scratch cell `k`, run the compiled subformula `cb`, force the
accumulator cell `k` on success, clean the env cell — the self-cleanup
that lets trials chain with no caller-side wipe. -/
def trialCom (ea xa : String) (k : ℕ) (e : Expr) (cb : Com) : Com :=
  .seq (.store ea (.lit k) e)
    (.seq cb
      (.seq (.ite (.eq (.var "bt.r") (.lit 1)) (.store xa (.lit k) (.lit 1)) .skip)
        (.store ea (.lit k) (.lit 0))))

/-- One row code's turn of an unrestricted quantifier: reset the found
flag, read the row's count, scan the `K+1` seats for the first
off-environment entry, and try it if one was found. -/
def rhoCom (na fa ea xa : String) (K k ρ : ℕ) (cb : Com) : Com :=
  .seq (.assign "bt.f" (.lit 0))
    (.seq (.assign "bt.d" (.get na (.lit ρ)))
      (.seq (seqIdx (fun s _ => seatCom fa ea K k ρ s) (List.range (K + 1)) 0)
        (.ite (.eq (.var "bt.f") (.lit 1))
          (trialCom ea xa k (.var "bt.w") cb) .skip)))

/-- **The unrestricted quantifier, unrolled** (§6.4's schedule): the
`k` environment entries, then one `rhoCom` per row code — `≤ k +
2^L·(K+1)` candidates however large the arena. The accumulator cell
`k` collects the disjunction and is cleaned on the way out. -/
def exUCom (na fa ea xa : String) (Lc K k : ℕ) (cb : Com) : Com :=
  .seq (seqIdx (fun i _ => trialCom ea xa k (.get ea (.lit i)) cb) (List.range k) 0)
    (.seq (seqIdx (fun _ ρ => rhoCom na fa ea xa K k ρ cb) (List.range (2 ^ Lc)) 0)
      (.seq (.assign "bt.r" (.get xa (.lit k)))
        (.store xa (.lit k) (.lit 0))))

/-- The local quantifier: its guard set is compile-time syntax, so it
is the same unrolled trial loop over the guard's entries — no search
at all. -/
def exLCom (ea xa : String) (k : ℕ) (g : List ℕ) (cb : Com) : Com :=
  .seq (seqIdx (fun _ i => trialCom ea xa k (.get ea (.lit i)) cb) g 0)
    (.seq (.assign "bt.r" (.get xa (.lit k)))
      (.store xa (.lit k) (.lit 0)))

/-- An equality atom: one comparison of two env cells. -/
def eqCom (ea : String) (i j : ℕ) : Com :=
  .ite (.eq (.get ea (.lit i)) (.get ea (.lit j)))
    (.assign "bt.r" (.lit 1)) (.assign "bt.r" (.lit 0))

/-- A color atom: one row-bit read at stride `Lc`. -/
def colorCom (ca ea : String) (Lc c i : ℕ) : Com :=
  .assign "bt.r"
    (.get ca (.add (.mul (.get ea (.lit i)) (.lit Lc)) (.lit c)))

/-- **The compiled evaluator** — `botEvalT`, by compile-time
structural recursion over the formula (`bcExpr`'s move at `DistFO`):
atoms are env reads and row-bit reads, `not` flips, `and`
short-circuits, the quantifiers are the unrolled candidate loops. The
formula, `k`, `K` and `Lc` are schedule data; the carrier never
appears. -/
noncomputable def evalCom (ca na fa ea xa : String) (Lc K : ℕ) :
    {k : ℕ} → DistFO Lc k → Com
  | _, .adj _ _ => .assign "bt.r" (.lit 0)
  | _, .eq i j => eqCom ea i j
  | _, .color c i => colorCom ca ea Lc c i
  | _, .distLe _ i j => eqCom ea i j
  | _, .distColorLt r c i =>
      if r = 0 then .assign "bt.r" (.lit 0) else colorCom ca ea Lc c i
  | _, .not φ =>
      .seq (evalCom ca na fa ea xa Lc K φ)
        (.assign "bt.r" (.sub (.lit 1) (.var "bt.r")))
  | _, .and φ ψ =>
      .seq (evalCom ca na fa ea xa Lc K φ)
        (.ite (.eq (.var "bt.r") (.lit 1)) (evalCom ca na fa ea xa Lc K ψ) .skip)
  | k, .exU φ => exUCom na fa ea xa Lc K k (evalCom ca na fa ea xa Lc K φ)
  | k, .exL _ g φ =>
      exLCom ea xa k (g.toList.map Fin.val) (evalCom ca na fa ea xa Lc K φ)

/-! ## §5 The costs — functions of the schedule alone -/

/-- The per-entry evaluator's budget, by the same compile-time
recursion: a function of `(Lc, K, φ)` **only** — the carrier does not
occur, which is the whole content of "schedule-constant per table
entry". -/
def evalK (Lc K : ℕ) : {k : ℕ} → DistFO Lc k → ℕ
  | _, .adj _ _ => 2
  | _, .eq _ _ => 9
  | _, .color _ _ => 8
  | _, .distLe _ _ _ => 9
  | _, .distColorLt _ _ _ => 8
  | _, .not φ => evalK Lc K φ + 4
  | _, .and φ ψ => evalK Lc K φ + evalK Lc K ψ + 4
  | k, .exU φ =>
      k * (evalK Lc K φ + 14)
        + 2 ^ Lc * ((K + 1) * (7 * k + 22) + evalK Lc K φ + 24) + 8
  | _, .exL _ g φ => g.card * (evalK Lc K φ + 14) + 7

/-- The family's per-entry budget: the maximum of `evalK` over the
schedule list. -/
def evalKMax (Lc K : ℕ) (Fl : List (DistFO Lc 1)) : ℕ :=
  (Fl.map (evalK Lc K)).foldr max 0

theorem evalK_le_evalKMax {Lc K : ℕ} {Fl : List (DistFO Lc 1)}
    {β : DistFO Lc 1} (h : β ∈ Fl) : evalK Lc K β ≤ evalKMax Lc K Fl := by
  induction Fl with
  | nil => cases h
  | cons γ t ih =>
    rw [List.mem_cons] at h
    show evalK Lc K β ≤ max (evalK Lc K γ) ((t.map (evalK Lc K)).foldr max 0)
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- **The one `N·L` build pass's budget**: `11L + 30` per vertex (the
`L` unrolled row-bit reads, the seat append), plus the
schedule-constant `2^L` count wipe. -/
def buildK (N Lc : ℕ) : ℕ := 3 * 2 ^ Lc + (11 * Lc + 30) * N + 7

/-- **The fill loop's budget**: a schedule constant per `(v, β)`
entry — `botC`'s `|ℱ_j| · N` term. -/
def fillK (N Lc K : ℕ) (Fl : List (DistFO Lc 1)) : ℕ :=
  (Fl.length * (evalKMax Lc K Fl + 7) + 15) * N + 6

/-- **The whole block's budget**: the build pass, the fill loop, and
the two `K+1`-cell scratch wipes. -/
def botComK (N Lc K : ℕ) (Fl : List (DistFO Lc 1)) : ℕ :=
  buildK N Lc + fillK N Lc K Fl + 6 * K + 10

/-! ## §6 The write footprint, off the syntax -/

section Syntactic

variable (ca na fa ea xa : String) (Lc K : ℕ)

theorem wvars_offEnvCom (k : ℕ) : (offEnvCom ea k).wvars ⊆ evalWScalars := by
  rw [offEnvCom]
  show ((Com.assign "bt.o" (.lit 1)).wvars ++ _) ⊆ _
  refine List.append_subset.mpr ⟨by decide, ?_⟩
  refine wvars_seqIdx (fun i _ => ?_) _ _
  show (["bt.o"] ++ []) ⊆ evalWScalars
  decide

theorem warrs_offEnvCom (k : ℕ) {W : List String} : (offEnvCom ea k).warrs ⊆ W := by
  rw [offEnvCom]
  show ([] ++ _ : List String) ⊆ W
  rw [List.nil_append]
  refine warrs_seqIdx (fun i _ => ?_) _ _
  show (([] ++ []) : List String) ⊆ W
  simp

theorem wvars_seatCom (k ρ s : ℕ) : (seatCom fa ea K k ρ s).wvars ⊆ evalWScalars := by
  rw [seatCom]
  show ((((["bt.x"] ++ ((offEnvCom ea k).wvars ++ ((["bt.f"] ++ ["bt.w"]) ++ []))) ++ [])
      ++ []) : List String) ⊆ _
  simp only [List.append_nil]
  refine List.append_subset.mpr ⟨by decide, ?_⟩
  exact List.append_subset.mpr ⟨wvars_offEnvCom ea k, by decide⟩

theorem warrs_seatCom (k ρ s : ℕ) {W : List String} :
    (seatCom fa ea K k ρ s).warrs ⊆ W := by
  rw [seatCom]
  show (((([] ++ ((offEnvCom ea k).warrs ++ (([] ++ []) ++ []))) ++ [])
      ++ []) : List String) ⊆ W
  simp only [List.append_nil, List.nil_append]
  exact warrs_offEnvCom ea k

theorem wvars_trialCom (k : ℕ) (e : Expr) (cb : Com)
    (hcb : cb.wvars ⊆ evalWScalars) :
    (trialCom ea xa k e cb).wvars ⊆ evalWScalars := by
  rw [trialCom]
  show ([] ++ (cb.wvars ++ (([] ++ []) ++ []))) ⊆ _
  simpa using hcb

theorem warrs_trialCom (k : ℕ) (e : Expr) (cb : Com)
    (hcb : cb.warrs ⊆ [ea, xa]) :
    (trialCom ea xa k e cb).warrs ⊆ [ea, xa] := by
  rw [trialCom]
  show ([ea] ++ (cb.warrs ++ (([xa] ++ []) ++ [ea]))) ⊆ _
  refine List.append_subset.mpr ⟨by simp, ?_⟩
  refine List.append_subset.mpr ⟨hcb, by simp⟩

theorem wvars_rhoCom (k ρ : ℕ) (cb : Com) (hcb : cb.wvars ⊆ evalWScalars) :
    (rhoCom na fa ea xa K k ρ cb).wvars ⊆ evalWScalars := by
  rw [rhoCom]
  show (["bt.f"] ++ (["bt.d"] ++ (_ ++ ((trialCom ea xa k (.var "bt.w") cb).wvars ++ [])))) ⊆ _
  refine List.append_subset.mpr ⟨by decide, ?_⟩
  refine List.append_subset.mpr ⟨by decide, ?_⟩
  refine List.append_subset.mpr ⟨?_, ?_⟩
  · exact wvars_seqIdx (fun s _ => wvars_seatCom fa ea K k ρ s) _ _
  · simpa using wvars_trialCom ea xa k (.var "bt.w") cb hcb

theorem warrs_rhoCom (k ρ : ℕ) (cb : Com) (hcb : cb.warrs ⊆ [ea, xa]) :
    (rhoCom na fa ea xa K k ρ cb).warrs ⊆ [ea, xa] := by
  rw [rhoCom]
  show ([] ++ ([] ++ (_ ++ ((trialCom ea xa k (.var "bt.w") cb).warrs ++ [])))) ⊆ _
  simp only [List.nil_append]
  refine List.append_subset.mpr ⟨?_, ?_⟩
  · exact warrs_seqIdx (fun s _ => warrs_seatCom fa ea K k ρ s) _ _
  · simpa using warrs_trialCom ea xa k (.var "bt.w") cb hcb

theorem wvars_exUCom (k : ℕ) (cb : Com) (hcb : cb.wvars ⊆ evalWScalars) :
    (exUCom na fa ea xa Lc K k cb).wvars ⊆ evalWScalars := by
  rw [exUCom]
  show (_ ++ (_ ++ (["bt.r"] ++ []))) ⊆ _
  refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, by decide⟩⟩
  · exact wvars_seqIdx (fun i _ => wvars_trialCom ea xa k _ cb hcb) _ _
  · exact wvars_seqIdx (fun _ ρ => wvars_rhoCom na fa ea xa K k ρ cb hcb) _ _

theorem warrs_exUCom (k : ℕ) (cb : Com) (hcb : cb.warrs ⊆ [ea, xa]) :
    (exUCom na fa ea xa Lc K k cb).warrs ⊆ [ea, xa] := by
  rw [exUCom]
  show (_ ++ (_ ++ ([] ++ [xa]))) ⊆ _
  refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, by simp⟩⟩
  · exact warrs_seqIdx (fun i _ => warrs_trialCom ea xa k _ cb hcb) _ _
  · exact warrs_seqIdx (fun _ ρ => warrs_rhoCom na fa ea xa K k ρ cb hcb) _ _

theorem wvars_exLCom (k : ℕ) (g : List ℕ) (cb : Com)
    (hcb : cb.wvars ⊆ evalWScalars) :
    (exLCom ea xa k g cb).wvars ⊆ evalWScalars := by
  rw [exLCom]
  show (_ ++ (["bt.r"] ++ [])) ⊆ _
  refine List.append_subset.mpr ⟨?_, by decide⟩
  exact wvars_seqIdx (fun _ i => wvars_trialCom ea xa k _ cb hcb) _ _

theorem warrs_exLCom (k : ℕ) (g : List ℕ) (cb : Com)
    (hcb : cb.warrs ⊆ [ea, xa]) :
    (exLCom ea xa k g cb).warrs ⊆ [ea, xa] := by
  rw [exLCom]
  show (_ ++ ([] ++ [xa])) ⊆ _
  refine List.append_subset.mpr ⟨?_, by simp⟩
  exact warrs_seqIdx (fun _ i => warrs_trialCom ea xa k _ cb hcb) _ _

/-- The evaluator writes only its own scratch scalars. -/
theorem wvars_evalCom : ∀ {k : ℕ} (φ : DistFO Lc k),
    (evalCom ca na fa ea xa Lc K φ).wvars ⊆ evalWScalars
  | _, .adj _ _ => by
      rw [evalCom]; show ["bt.r"] ⊆ evalWScalars; decide
  | _, .eq i j => by
      rw [evalCom, eqCom]; show (["bt.r"] ++ ["bt.r"]) ⊆ evalWScalars; decide
  | _, .color c i => by
      rw [evalCom, colorCom]; show ["bt.r"] ⊆ evalWScalars; decide
  | _, .distLe _ i j => by
      rw [evalCom, eqCom]; show (["bt.r"] ++ ["bt.r"]) ⊆ evalWScalars; decide
  | _, .distColorLt r c i => by
      rw [evalCom]
      split
      · show ["bt.r"] ⊆ evalWScalars; decide
      · rw [colorCom]; show ["bt.r"] ⊆ evalWScalars; decide
  | _, .not φ => by
      rw [evalCom]
      show ((evalCom ca na fa ea xa Lc K φ).wvars ++ ["bt.r"]) ⊆ _
      exact List.append_subset.mpr ⟨wvars_evalCom φ, by decide⟩
  | _, .and φ ψ => by
      rw [evalCom]
      show ((evalCom ca na fa ea xa Lc K φ).wvars
        ++ ((evalCom ca na fa ea xa Lc K ψ).wvars ++ [])) ⊆ _
      refine List.append_subset.mpr ⟨wvars_evalCom φ, ?_⟩
      simpa using wvars_evalCom ψ
  | k, .exU φ => by
      rw [evalCom]
      exact wvars_exUCom na fa ea xa Lc K k _ (wvars_evalCom φ)
  | k, .exL r g φ => by
      rw [evalCom]
      exact wvars_exLCom ea xa k _ _ (wvars_evalCom φ)

/-- The evaluator stores only into its two scratch regions. -/
theorem warrs_evalCom : ∀ {k : ℕ} (φ : DistFO Lc k),
    (evalCom ca na fa ea xa Lc K φ).warrs ⊆ [ea, xa]
  | _, .adj _ _ => by rw [evalCom]; exact List.nil_subset _
  | _, .eq i j => by
      rw [evalCom, eqCom]
      show (([] ++ []) : List String) ⊆ _
      simp
  | _, .color c i => by rw [evalCom, colorCom]; exact List.nil_subset _
  | _, .distLe _ i j => by
      rw [evalCom, eqCom]
      show (([] ++ []) : List String) ⊆ _
      simp
  | _, .distColorLt r c i => by
      rw [evalCom]
      split
      · exact List.nil_subset _
      · rw [colorCom]; exact List.nil_subset _
  | _, .not φ => by
      rw [evalCom]
      show ((evalCom ca na fa ea xa Lc K φ).warrs ++ []) ⊆ _
      simpa using warrs_evalCom φ
  | _, .and φ ψ => by
      rw [evalCom]
      show ((evalCom ca na fa ea xa Lc K φ).warrs
        ++ ((evalCom ca na fa ea xa Lc K ψ).warrs ++ [])) ⊆ _
      refine List.append_subset.mpr ⟨warrs_evalCom φ, ?_⟩
      simpa using warrs_evalCom ψ
  | k, .exU φ => by
      rw [evalCom]
      exact warrs_exUCom na fa ea xa Lc K k _ (warrs_evalCom φ)
  | k, .exL r g φ => by
      rw [evalCom]
      exact warrs_exLCom ea xa k _ _ (warrs_evalCom φ)

end Syntactic

/-! ## §7 The evaluator, discharged -/

section EvalSpec

variable {B N Lc K : ℕ} {colB : Fin N → Fin Lc → Bool}
  {ca na fa ea xa : String}

/-- The bound is at least two as soon as the seat region fits below it. -/
private theorem one_lt_of_seats (h2LB : 2 ^ Lc * (K + 1) < B) : 1 < B := by
  have h1 : 0 < 2 ^ Lc * (K + 1) := by positivity
  omega

private theorem run_assign_lit {x : String} {v : ℕ} {σ : Env} (hv : v < B) :
    Run B (.assign x (.lit v)) σ (σ.setVar x v) 2 :=
  (Run.assign (evalB_lit hv)).mono (by simp)

private theorem evalB_get_lit {a : String} {i v : ℕ} {σ : Env}
    (hi : i < (σ.arrs a).length) (hv : (σ.arrs a).getD i 0 = v)
    (hiB : i < B) (hvB : v < B) :
    (Expr.get a (.lit i)).evalB B σ = some v := by
  refine evalB_get (evalB_lit hiB) ?_ hvB
  rw [getElem?_eq_getD hi, hv]

/-- A store into a length-pinned array, as an `upd` of its cell
function. -/
private theorem set_eq_arrOf_upd {l : List ℕ} {n : ℕ} (i v : ℕ) (hl : l.length = n) :
    l.set i v = arrOf n (upd (fun j => l.getD j 0) i v) := by
  have hpin : l = arrOf n fun j => l.getD j 0 := by
    rw [← hl]; exact (arrOf_getD l).symm
  calc l.set i v = (arrOf n fun j => l.getD j 0).set i v := by rw [← hpin]
    _ = _ := set_arrOf_eq_upd _ _ _

/-- Reading past the end of an array is the default. -/
private theorem getD_ge_len {l : List ℕ} {i : ℕ} (h : l.length ≤ i) :
    l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private theorem rowBits_of_arrs_eq {σ σ' : Env} (h : σ'.arrs ca = σ.arrs ca)
    (hr : RowBits ca colB σ) : RowBits ca colB σ' := by
  unfold RowBits at hr ⊢
  rw [h]; exact hr

private theorem firstsSt_of_arrs_eq {σ σ' : Env} (hna : σ'.arrs na = σ.arrs na)
    (hfa : σ'.arrs fa = σ.arrs fa) (hf : FirstsSt na fa colB K σ) :
    FirstsSt na fa colB K σ' := by
  unfold FirstsSt at hf ⊢
  rw [hna, hfa]; exact hf

private theorem trialSt_of_arrs_eq {k : ℕ} {m : Fin k → Fin N} {σ σ' : Env}
    (h : σ'.arrs = σ.arrs) (hst : TrialSt ca na fa ea xa colB K m σ) :
    TrialSt ca na fa ea xa colB K m σ' := by
  unfold TrialSt RowBits FirstsSt at hst ⊢
  rw [h]; exact hst

private theorem evalSt_of_arrs_eq {k : ℕ} {m : Fin k → Fin N} {σ σ' : Env}
    (h : σ'.arrs = σ.arrs) (hst : EvalSt ca na fa ea xa colB K m σ) :
    EvalSt ca na fa ea xa colB K m σ' := by
  unfold EvalSt RowBits FirstsSt at hst ⊢
  rw [h]; exact hst

/-- A state whose regions and non-scratch scalars are untouched is a
null candidate footprint. -/
private theorem trialPost_of_untouched {k : ℕ} {σ σ' : Env}
    (harr : σ'.arrs = σ.arrs)
    (hv : ∀ y, y ∉ evalWScalars → σ'.vars y = σ.vars y) :
    TrialPost ea xa k false σ σ' := by
  refine ⟨by rw [harr], by rw [harr]; simp, fun i _ => by rw [harr],
    by rw [harr], fun a _ _ => by rw [harr], hv⟩

/-- **The composable per-node postcondition**: the result bit, the two
scratch regions returned verbatim, everything else framed. -/
def EvalPost (ea xa : String) (bit : ℕ) (σ σ' : Env) : Prop :=
  σ'.vars "bt.r" = bit ∧ σ'.arrs ea = σ.arrs ea ∧ σ'.arrs xa = σ.arrs xa ∧
    (∀ a, a ≠ ea → a ≠ xa → σ'.arrs a = σ.arrs a) ∧
    (∀ y, y ∉ evalWScalars → σ'.vars y = σ.vars y)

open Classical in
/-- **The off-environment test, discharged**: from the env region at
`m` and the candidate in `"bt.x"`, the flag `"bt.o"` ends holding
`offEnv m x`'s bit; nothing else moves. -/
private theorem offEnvCom_spec (h2LB : 2 ^ Lc * (K + 1) < B) (hNB : N < B)
    {k : ℕ} (hkK : k ≤ K + 1) (m : Fin k → Fin N) (x : Fin N) :
    Spec B
      (fun σ => σ.arrs ea = arrOf (K + 1) (envFun m) ∧ σ.vars "bt.x" = (x : ℕ))
      (offEnvCom ea k)
      (fun σ σ' => σ'.vars "bt.o" = (if offEnv m x then 1 else 0) ∧
        σ'.arrs = σ.arrs ∧ σ'.vars "bt.x" = σ.vars "bt.x" ∧
        (∀ y, y ≠ "bt.o" → σ'.vars y = σ.vars y))
      (7 * k + 3) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  intro σ hσ
  obtain ⟨henv, hx⟩ := hσ
  set σ₀ := σ.setVar "bt.o" 1 with hσ₀
  have hrun₀ : Run B (.assign "bt.o" (.lit 1)) σ σ₀ 2 := run_assign_lit (by omega)
  set Inv : ℕ → Env → Prop := fun j τ =>
    τ.arrs = σ.arrs ∧ (∀ y, y ≠ "bt.o" → τ.vars y = σ.vars y) ∧
      τ.vars "bt.o" = (if ∀ i : Fin k, (i : ℕ) < j → m i ≠ x then 1 else 0)
    with hInv
  have hstep : ∀ i, i < (List.range k).length →
      Spec B (Inv (0 + i))
        (Com.ite (.eq (.get ea (.lit (0 + i))) (.var "bt.x"))
          (.assign "bt.o" (.lit 0)) .skip)
        (fun _ τ' => Inv (0 + i + 1) τ') 7 := by
    intro i hi
    rw [List.length_range] at hi
    intro τ hτ
    obtain ⟨harr, hvars, ho⟩ := hτ
    have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
    have hmiB : (m ⟨i, hi⟩ : ℕ) < B := lt_trans (Fin.is_lt _) hNB
    have hread : (Expr.get ea (.lit (0 + i))).evalB B τ = some (m ⟨i, hi⟩ : ℕ) := by
      refine evalB_get_lit ?_ ?_ (by omega) hmiB
      · rw [harr]
        rw [henv, length_arrOf]
        omega
      · rw [harr]
        rw [henv, getD_arrOf _ (by omega : 0 + i < K + 1)]
        have : 0 + i = i := by omega
        rw [this, envFun_lt m hi]
    have hxτ : τ.vars "bt.x" = (x : ℕ) := by
      rw [hvars _ (by decide)]; exact hx
    have hxev : (Expr.var "bt.x").evalB B τ = some (x : ℕ) := by
      rw [← hxτ]
      exact evalB_var (by rw [hxτ]; exact lt_trans (Fin.is_lt _) hNB)
    have hcond := evalB_condEq hread hxev
    by_cases heq : (m ⟨i, hi⟩ : ℕ) = (x : ℕ)
    · -- the candidate is this entry: clear the flag
      have hcondT : (Cond.eq (.get ea (.lit (0 + i))) (.var "bt.x")).evalB B τ
          = some true := by
        rw [hcond]
        congr 1
        simpa using heq
      refine ⟨τ.setVar "bt.o" 0,
        (Run.ite_true hcondT (run_assign_lit (by omega))).mono (by simp), ?_, ?_, ?_⟩
      · simpa using harr
      · intro y hy
        rw [vars_setVar, if_neg hy]
        exact hvars y hy
      · rw [vars_setVar, if_pos rfl]
        have hP : ¬ ∀ i' : Fin k, (i' : ℕ) < 0 + i + 1 → m i' ≠ x := by
          intro hall
          exact hall ⟨i, hi⟩ (by simp) (Fin.val_inj.mp heq)
        rw [if_neg hP]
    · -- not this entry: the flag stands
      have hcondF : (Cond.eq (.get ea (.lit (0 + i))) (.var "bt.x")).evalB B τ
          = some false := by
        rw [hcond]
        congr 1
        simpa using heq
      refine ⟨τ, (Run.ite_false hcondF Run.skip).mono (by simp), harr, hvars, ?_⟩
      rw [ho]
      refine if_congr ?_ rfl rfl
      constructor
      · intro h i' hi'
        rcases Nat.lt_or_ge (i' : ℕ) (0 + i) with h2 | h2
        · exact h i' h2
        · have hieq : i' = ⟨i, hi⟩ := by
            apply Fin.ext
            show (i' : ℕ) = i
            omega
          subst hieq
          intro hcon
          exact heq (congrArg Fin.val hcon)
      · intro h i' hi'
        exact h i' (by omega)
  -- assemble: the flag initialization, then the scan
  have hscan := seqIdx_spec (B := B) (Kb := 7)
    (gen := fun i _ => Com.ite (.eq (.get ea (.lit i)) (.var "bt.x"))
      (.assign "bt.o" (.lit 0)) .skip)
    Inv (List.range k) 0 hstep
  have hInv0 : Inv 0 σ₀ := by
    refine ⟨by rw [hσ₀]; simp, fun y hy => by rw [hσ₀, vars_setVar, if_neg hy], ?_⟩
    rw [hσ₀, vars_setVar, if_pos rfl, if_pos (fun i' h => absurd h (by omega))]
  obtain ⟨τ, hrunS, hτ⟩ := hscan σ₀ hInv0
  simp only [List.length_range, Nat.zero_add] at hτ
  obtain ⟨harr, hvars, ho⟩ := hτ
  refine ⟨τ, (hrun₀.seq hrunS).mono (by rw [List.length_range]; omega), ?_,
    harr, hvars _ (by decide), fun y hy => hvars y hy⟩
  rw [ho]
  refine if_congr ?_ rfl rfl
  rw [offEnv_eq_true_iff]
  constructor
  · rintro h ⟨i, hix⟩
    exact h i i.is_lt hix
  · intro h i' _ hcon
    exact h ⟨i', hcon⟩

variable (h2LB : 2 ^ Lc * (K + 1) < B) (hNB : N < B) (hNLB : N * Lc < B)
  (hca_ea : ca ≠ ea) (hca_xa : ca ≠ xa) (hna_ea : na ≠ ea) (hna_xa : na ≠ xa)
  (hfa_ea : fa ≠ ea) (hfa_xa : fa ≠ xa) (hea_xa : ea ≠ xa)

include h2LB hNB in
open Classical in
/-- **One row code's seat scan, discharged**: from the mid-quantifier
state with a clear flag and the row's count in `"bt.d"`, the scan ends
with `"bt.f"`/`"bt.w"` reporting exactly `find? (offEnv m)`'s verdict
on the row's table list; no array moves. -/
private theorem seatScan_spec {k : ℕ} (hkK : k ≤ K) (m : Fin k → Fin N)
    (ρ : ℕ) (hρ : ρ < 2 ^ Lc) :
    Spec B
      (fun σ => TrialSt ca na fa ea xa colB K m σ ∧
        σ.vars "bt.f" = 0 ∧ σ.vars "bt.d" = (firsts colB K ρ).length)
      (seqIdx (fun s _ => seatCom fa ea K k ρ s) (List.range (K + 1)) 0)
      (fun σ σ' => σ'.arrs = σ.arrs ∧
        (∀ y, y ∉ evalWScalars → σ'.vars y = σ.vars y) ∧
        (∀ w, (firsts colB K ρ).find? (offEnv m) = some w →
          σ'.vars "bt.f" = 1 ∧ σ'.vars "bt.w" = (w : ℕ)) ∧
        ((firsts colB K ρ).find? (offEnv m) = none → σ'.vars "bt.f" = 0))
      ((K + 1) * (7 * k + 22) + 1) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  intro σ hσ
  obtain ⟨hst, hf0, hd⟩ := hσ
  have hfl_le := firsts_length_le colB K ρ
  set Inv : ℕ → Env → Prop := fun j τ =>
    τ.arrs = σ.arrs ∧ (∀ y, y ∉ evalWScalars → τ.vars y = σ.vars y) ∧
      τ.vars "bt.d" = (firsts colB K ρ).length ∧
      (∀ w, ((firsts colB K ρ).take j).find? (offEnv m) = some w →
        τ.vars "bt.f" = 1 ∧ τ.vars "bt.w" = (w : ℕ)) ∧
      (((firsts colB K ρ).take j).find? (offEnv m) = none → τ.vars "bt.f" = 0)
    with hInv
  have hstep : ∀ s, s < (List.range (K + 1)).length →
      Spec B (Inv (0 + s)) (seatCom fa ea K k ρ (0 + s))
        (fun _ τ' => Inv (0 + s + 1) τ') (7 * k + 22) := by
    intro s hs
    rw [List.length_range] at hs
    intro τ hτ
    obtain ⟨harr, hvars, hdτ, hsome, hnone⟩ := hτ
    cases hfind : ((firsts colB K ρ).take (0 + s)).find? (offEnv m) with
    | some w =>
      -- already found: the flag blocks the seat
      obtain ⟨hf1, hw⟩ := hsome w hfind
      have hcondF : (Cond.eq (.var "bt.f") (.lit 0)).evalB B τ = some false := by
        rw [evalB_condEq (evalB_var (by rw [hf1]; omega)) (evalB_lit (by omega)), hf1]
        simp
      refine ⟨τ, (Run.ite_false hcondF Run.skip).mono
        (by simp only [size_condEq, size_var, size_lit]; omega),
        harr, hvars, hdτ, ?_, ?_⟩
      · intro w' hw'
        rw [find?_take_succ_of_some hfind] at hw'
        injection hw' with hww
        subst hww
        exact ⟨hf1, hw⟩
      · intro hcon
        rw [find?_take_succ_of_some hfind] at hcon
        simp at hcon
    | none =>
      -- nothing yet: test the seat
      have hf0τ : τ.vars "bt.f" = 0 := hnone hfind
      have hcondT : (Cond.eq (.var "bt.f") (.lit 0)).evalB B τ = some true := by
        rw [evalB_condEq (evalB_var (by rw [hf0τ]; omega)) (evalB_lit (by omega)), hf0τ]
        simp
      have hdev : (Expr.var "bt.d").evalB B τ = some (firsts colB K ρ).length := by
        rw [← hdτ]
        exact evalB_var (by rw [hdτ]; omega)
      have hcond2 := evalB_condLt (evalB_lit (show 0 + s < B by omega)) hdev
      by_cases hslt : 0 + s < (firsts colB K ρ).length
      · -- an occupied seat: read it and test off-environment
        have hcond2T : (Cond.lt (.lit (0 + s)) (.var "bt.d")).evalB B τ = some true := by
          rw [hcond2]
          congr 1
          simpa using hslt
        set w := (firsts colB K ρ)[0 + s]'hslt with hwdef
        have hidx : ρ * (K + 1) + (0 + s) < 2 ^ Lc * (K + 1) := by
          have h1 : (ρ + 1) * (K + 1) ≤ 2 ^ Lc * (K + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.succ_mul] at h1
          omega
        have hxev : (Expr.get fa (.lit (ρ * (K + 1) + (0 + s)))).evalB B τ
            = some (w : ℕ) := by
          refine evalB_get_lit ?_ ?_ (by omega) (lt_trans (Fin.is_lt _) hNB)
          · rw [harr, hst.2.1.2.1]
            exact hidx
          · rw [harr]
            exact (hst.2.1.2.2 ρ hρ).2 (0 + s) hslt
        set τ₁ := τ.setVar "bt.x" (w : ℕ) with hτ₁
        have hr₁ : Run B (.assign "bt.x" (.get fa (.lit (ρ * (K + 1) + (0 + s)))))
            τ τ₁ 3 := (Run.assign hxev).mono (by simp)
        -- the off-environment test
        obtain ⟨τ₂, hr₂, hoval, hoarr, hox, hovars⟩ :=
          (offEnvCom_spec h2LB hNB (by omega : k ≤ K + 1) m w) τ₁
            ⟨by rw [hτ₁]; simp only [arrs_setVar]; rw [harr]; exact hst.2.2.1,
              by rw [hτ₁]; simp⟩
        have hxτ₂ : τ₂.vars "bt.x" = (w : ℕ) := by rw [hox, hτ₁]; simp
        have hoB : τ₂.vars "bt.o" < B := by rw [hoval]; split <;> omega
        have hcond3 := evalB_condEq (evalB_var hoB) (evalB_lit (by omega : (1:ℕ) < B))
        by_cases hoff : offEnv m w = true
        · -- first off-environment seat: record it
          have hcond3T : (Cond.eq (.var "bt.o") (.lit 1)).evalB B τ₂ = some true := by
            rw [hcond3, hoval, hoff]
            simp
          set τ₃ := τ₂.setVar "bt.f" 1 with hτ₃
          have hr₃ : Run B (.assign "bt.f" (.lit 1)) τ₂ τ₃ 2 := run_assign_lit (by omega)
          have hwτ₃ : τ₃.vars "bt.x" = (w : ℕ) := by rw [hτ₃]; simpa using hxτ₂
          set τ₄ := τ₃.setVar "bt.w" (w : ℕ) with hτ₄
          have hr₄ : Run B (.assign "bt.w" (.var "bt.x")) τ₃ τ₄ 2 := by
            have hev : (Expr.var "bt.x").evalB B τ₃ = some (w : ℕ) := by
              rw [← hwτ₃]
              exact evalB_var (by rw [hwτ₃]; exact lt_trans (Fin.is_lt _) hNB)
            rw [hτ₄]
            exact (Run.assign hev).mono (by simp)
          have hrun : Run B (seatCom fa ea K k ρ (0 + s)) τ τ₄ (7 * k + 22) := by
            refine (Run.ite_true hcondT (Run.ite_true hcond2T
              (hr₁.seq (hr₂.seq (Run.ite_true hcond3T (hr₃.seq hr₄)))))).mono ?_
            simp only [size_condEq, size_condLt, size_var, size_lit]
            omega
          have hfindS : ((firsts colB K ρ).take (0 + s + 1)).find? (offEnv m)
              = some w := by
            rw [find?_take_succ_of_none hfind hslt, ← hwdef, if_pos hoff]
          refine ⟨τ₄, hrun, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hτ₄, hτ₃]
            simp only [arrs_setVar]
            rw [hoarr, hτ₁]
            simpa using harr
          · intro y hy
            have hyf : y ≠ "bt.f" := fun hc => hy (by rw [hc]; decide)
            have hyw : y ≠ "bt.w" := fun hc => hy (by rw [hc]; decide)
            have hyx : y ≠ "bt.x" := fun hc => hy (by rw [hc]; decide)
            have hyo : y ≠ "bt.o" := fun hc => hy (by rw [hc]; decide)
            rw [hτ₄, vars_setVar, if_neg hyw, hτ₃, vars_setVar, if_neg hyf,
              hovars y hyo, hτ₁, vars_setVar, if_neg hyx]
            exact hvars y hy
          · have hyd : ("bt.d" : String) ≠ "bt.w" := by decide
            rw [hτ₄, vars_setVar, if_neg (by decide : ("bt.d" : String) ≠ "bt.w"),
              hτ₃, vars_setVar, if_neg (by decide : ("bt.d" : String) ≠ "bt.f"),
              hovars _ (by decide), hτ₁, vars_setVar,
              if_neg (by decide : ("bt.d" : String) ≠ "bt.x")]
            exact hdτ
          · intro w' hw'
            rw [hfindS] at hw'
            injection hw' with hww
            subst hww
            constructor
            · rw [hτ₄, vars_setVar, if_neg (by decide : ("bt.f" : String) ≠ "bt.w"),
                hτ₃, vars_setVar, if_pos rfl]
            · rw [hτ₄, vars_setVar, if_pos rfl]
          · intro hcon
            rw [hfindS] at hcon
            simp at hcon
        · -- on the environment: the seat is skipped
          have hoff' : offEnv m w = false := by
            rw [Bool.not_eq_true] at hoff
            exact hoff
          have hcond3F : (Cond.eq (.var "bt.o") (.lit 1)).evalB B τ₂ = some false := by
            rw [hcond3, hoval, hoff']
            simp
          have hrun : Run B (seatCom fa ea K k ρ (0 + s)) τ τ₂ (7 * k + 22) := by
            refine (Run.ite_true hcondT (Run.ite_true hcond2T
              (hr₁.seq (hr₂.seq (Run.ite_false hcond3F Run.skip))))).mono ?_
            simp only [size_condEq, size_condLt, size_var, size_lit]
            omega
          have hfindS : ((firsts colB K ρ).take (0 + s + 1)).find? (offEnv m)
              = none := by
            rw [find?_take_succ_of_none hfind hslt, ← hwdef, if_neg (by rw [hoff']; simp)]
          have hfτ₂ : τ₂.vars "bt.f" = 0 := by
            rw [hovars _ (by decide), hτ₁, vars_setVar,
              if_neg (by decide : ("bt.f" : String) ≠ "bt.x")]
            exact hf0τ
          refine ⟨τ₂, hrun, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hoarr, hτ₁]
            simpa using harr
          · intro y hy
            have hyx : y ≠ "bt.x" := fun hc => hy (by rw [hc]; decide)
            have hyo : y ≠ "bt.o" := fun hc => hy (by rw [hc]; decide)
            rw [hovars y hyo, hτ₁, vars_setVar, if_neg hyx]
            exact hvars y hy
          · rw [hovars _ (by decide), hτ₁, vars_setVar,
              if_neg (by decide : ("bt.d" : String) ≠ "bt.x")]
            exact hdτ
          · intro w' hw'
            rw [hfindS] at hw'
            simp at hw'
          · intro _
            exact hfτ₂
      · -- an empty seat: the count blocks it
        have hcond2F : (Cond.lt (.lit (0 + s)) (.var "bt.d")).evalB B τ = some false := by
          rw [hcond2]
          congr 1
          simpa using hslt
        have htake : (firsts colB K ρ).take (0 + s) = firsts colB K ρ :=
          List.take_of_length_le (by omega)
        have htake' : (firsts colB K ρ).take (0 + s + 1) = firsts colB K ρ :=
          List.take_of_length_le (by omega)
        refine ⟨τ, (Run.ite_true hcondT (Run.ite_false hcond2F Run.skip)).mono
          (by simp only [size_condEq, size_condLt, size_var, size_lit]; omega),
          harr, hvars, hdτ, ?_, ?_⟩
        · intro w' hw'
          rw [htake'] at hw'
          rw [htake] at hfind
          rw [hfind] at hw'
          simp at hw'
        · intro _
          exact hf0τ
  -- assemble the K + 1 seats
  have hscan := seqIdx_spec (B := B) (Kb := 7 * k + 22)
    (gen := fun s _ => seatCom fa ea K k ρ s)
    Inv (List.range (K + 1)) 0 hstep
  have hInv0 : Inv 0 σ := by
    refine ⟨rfl, fun _ _ => rfl, hd, ?_, fun _ => hf0⟩
    intro w hw
    simp at hw
  obtain ⟨τ, hrunS, hτ⟩ := hscan σ hInv0
  simp only [List.length_range, Nat.zero_add] at hτ
  obtain ⟨harr, hvars, hdτ, hsome, hnone⟩ := hτ
  have htake : (firsts colB K ρ).take (K + 1) = firsts colB K ρ :=
    List.take_of_length_le hfl_le
  rw [htake] at hsome hnone
  exact ⟨τ, hrunS.mono (by rw [List.length_range]), harr, hvars, hsome, hnone⟩

include h2LB hca_ea hna_ea hfa_ea hea_xa in
open Classical in
/-- **One candidate trial, discharged**: from the mid-quantifier state
with the candidate `w` delivered by the expression `e`, the trial's
whole footprint is `TrialPost` at the candidate's `botEvalT` bit — the
env scratch cell is written, used by the compiled subformula, and
cleaned on the way out (the seam rule: no caller-side wipe, ever). The
stored values are the candidate (`< N`) and two bits. -/
private theorem trialCom_spec {k : ℕ} (hkK : k ≤ K) (m : Fin k → Fin N) (w : Fin N)
    {e : Expr} {cb : Com} {Kb : ℕ} (φ : DistFO Lc (k + 1))
    (hese : e.size ≤ 2)
    (hbody : Spec B (fun σ => EvalSt ca na fa ea xa colB K (Fin.snoc m w) σ) cb
      (EvalPost ea xa (if botEvalT colB K (Fin.snoc m w) φ then 1 else 0)) Kb) :
    Spec B
      (fun σ => TrialSt ca na fa ea xa colB K m σ ∧ e.evalB B σ = some (w : ℕ))
      (trialCom ea xa k e cb)
      (fun σ σ' => TrialPost ea xa k (botEvalT colB K (Fin.snoc m w) φ) σ σ')
      (Kb + 14) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  rintro σ ⟨hst, hev⟩
  obtain ⟨hrow, hfst, henv, hxl, hxz⟩ := hst
  -- 1. the candidate into the env scratch cell (a vertex name, `< N`)
  have hkl : k < (σ.arrs ea).length := by rw [henv, length_arrOf]; omega
  set σ₁ := σ.setArr ea k (w : ℕ) with hσ₁
  have hr₁ : Run B (.store ea (.lit k) e) σ σ₁ (2 + e.size) := by
    rw [hσ₁]
    exact (Run.store (evalB_lit (by omega)) hev hkl).mono (by simp)
  have hea₁ : σ₁.arrs ea = arrOf (K + 1) (envFun (Fin.snoc m w)) := by
    rw [hσ₁, arrs_setArr, if_pos rfl, henv, set_arrOf_eq_upd, envFun_snoc]
  have hEval₁ : EvalSt ca na fa ea xa colB K (Fin.snoc m w) σ₁ := by
    refine ⟨rowBits_of_arrs_eq ?_ hrow, firstsSt_of_arrs_eq ?_ ?_ hfst, hea₁, ?_, ?_⟩
    · rw [hσ₁, arrs_setArr, if_neg hca_ea]
    · rw [hσ₁, arrs_setArr, if_neg hna_ea]
    · rw [hσ₁, arrs_setArr, if_neg hfa_ea]
    · rw [hσ₁, arrs_setArr, if_neg (Ne.symm hea_xa)]
      exact hxl
    · intro i hi
      rw [hσ₁, arrs_setArr, if_neg (Ne.symm hea_xa)]
      exact hxz i hi
  -- 2. the compiled subformula
  obtain ⟨σ₂, hr₂, hrb, hea₂, hxa₂, harr₂, hvar₂⟩ := hbody σ₁ hEval₁
  have hxa₂σ : σ₂.arrs xa = σ.arrs xa := by
    rw [hxa₂, hσ₁, arrs_setArr, if_neg (Ne.symm hea_xa)]
  -- 3. force the accumulator cell on success
  have hrB : σ₂.vars "bt.r" < B := by rw [hrb]; split <;> omega
  have hcond := evalB_condEq (evalB_var hrB) (evalB_lit (show (1:ℕ) < B by omega))
  by_cases hb : botEvalT colB K (Fin.snoc m w) φ = true
  · -- success: `xa[k] := 1`, then clean the env cell
    have hr1 : σ₂.vars "bt.r" = 1 := by rw [hrb, hb]; simp
    have hcondT : (Cond.eq (.var "bt.r") (.lit 1)).evalB B σ₂ = some true := by
      rw [hcond, hr1]; simp
    have hkxl : k < (σ₂.arrs xa).length := by rw [hxa₂σ, hxl]; omega
    set σ₃ := σ₂.setArr xa k 1 with hσ₃
    have hr₃ : Run B (.store xa (.lit k) (.lit 1)) σ₂ σ₃ 3 := by
      rw [hσ₃]
      exact (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) hkxl).mono (by simp)
    have hkel : k < (σ₃.arrs ea).length := by
      rw [hσ₃, arrs_setArr, if_neg hea_xa, hea₂, hea₁, length_arrOf]
      omega
    set σ' := σ₃.setArr ea k 0 with hσ'
    have hr₄ : Run B (.store ea (.lit k) (.lit 0)) σ₃ σ' 3 := by
      rw [hσ']
      exact (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) hkel).mono (by simp)
    refine ⟨σ', (hr₁.seq (hr₂.seq ((Run.ite_true hcondT hr₃).seq hr₄))).mono
      (by simp only [size_condEq, size_var, size_lit]; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the env region is returned verbatim
      rw [hσ', arrs_setArr, if_pos rfl, hσ₃, arrs_setArr, if_neg hea_xa, hea₂, hea₁,
        set_arrOf_eq_upd, envFun_unsnoc, henv]
    · -- the accumulator cell holds the forced bit
      rw [hb, if_pos rfl]
      rw [hσ', arrs_setArr, if_neg (Ne.symm hea_xa), hσ₃, arrs_setArr, if_pos rfl,
        hxa₂σ, set_eq_arrOf_upd k 1 hxl, getD_arrOf _ (by omega)]
      simp [upd]
    · -- the other accumulator cells stand
      intro i hik
      rw [hσ', arrs_setArr, if_neg (Ne.symm hea_xa), hσ₃, arrs_setArr, if_pos rfl,
        hxa₂σ, set_eq_arrOf_upd k 1 hxl]
      by_cases hiK : i < K + 1
      · rw [getD_arrOf _ hiK, upd_of_ne _ hik]
      · rw [getD_ge_len (by rw [length_arrOf]; omega), getD_ge_len (by rw [hxl]; omega)]
    · rw [hσ', hσ₃]
      simp only [length_arrs_setArr]
      rw [hxa₂σ]
    · intro a ha1 ha2
      rw [hσ', arrs_setArr, if_neg ha1, hσ₃, arrs_setArr, if_neg ha2,
        harr₂ a ha1 ha2, hσ₁, arrs_setArr, if_neg ha1]
    · intro y hy
      rw [hσ', hσ₃]
      simp only [vars_setArr]
      rw [hvar₂ y hy, hσ₁]
      simp only [vars_setArr]
  · -- failure: the accumulator stands, the env cell is cleaned
    have hbf : botEvalT colB K (Fin.snoc m w) φ = false := by
      rw [Bool.not_eq_true] at hb
      exact hb
    have hr0 : σ₂.vars "bt.r" = 0 := by rw [hrb, hbf]; simp
    have hcondF : (Cond.eq (.var "bt.r") (.lit 1)).evalB B σ₂ = some false := by
      rw [hcond, hr0]; simp
    have hkel : k < (σ₂.arrs ea).length := by
      rw [hea₂, hea₁, length_arrOf]
      omega
    set σ' := σ₂.setArr ea k 0 with hσ'
    have hr₄ : Run B (.store ea (.lit k) (.lit 0)) σ₂ σ' 3 := by
      rw [hσ']
      exact (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) hkel).mono (by simp)
    refine ⟨σ', (hr₁.seq (hr₂.seq ((Run.ite_false hcondF Run.skip).seq hr₄))).mono
      (by simp only [size_condEq, size_var, size_lit]; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ', arrs_setArr, if_pos rfl, hea₂, hea₁, set_arrOf_eq_upd, envFun_unsnoc, henv]
    · rw [hbf, if_neg Bool.false_ne_true, hσ', arrs_setArr,
        if_neg (Ne.symm hea_xa), hxa₂σ]
    · intro i _
      rw [hσ', arrs_setArr, if_neg (Ne.symm hea_xa), hxa₂σ]
    · rw [hσ']
      simp only [length_arrs_setArr]
      rw [hxa₂σ]
    · intro a ha1 ha2
      rw [hσ', arrs_setArr, if_neg ha1, harr₂ a ha1 ha2, hσ₁, arrs_setArr, if_neg ha1]
    · intro y hy
      rw [hσ']
      simp only [vars_setArr]
      rw [hvar₂ y hy, hσ₁]
      simp only [vars_setArr]

include h2LB hNB hca_ea hna_ea hfa_ea hea_xa in
open Classical in
/-- **One row code's turn, discharged**: reset the flag, read the
row's count, scan the seats, try the first off-environment
representative if the row has one — the footprint is `TrialPost` at
the bit of `find? (offEnv m)`'s single candidate. -/
private theorem rhoCom_spec {k : ℕ} (hkK : k ≤ K) (m : Fin k → Fin N)
    (ρ : ℕ) (hρ : ρ < 2 ^ Lc) {cb : Com} {Kb : ℕ} (φ : DistFO Lc (k + 1))
    (hbody : ∀ w : Fin N, Spec B
      (fun σ => EvalSt ca na fa ea xa colB K (Fin.snoc m w) σ) cb
      (EvalPost ea xa (if botEvalT colB K (Fin.snoc m w) φ then 1 else 0)) Kb) :
    Spec B (fun σ => TrialSt ca na fa ea xa colB K m σ)
      (rhoCom na fa ea xa K k ρ cb)
      (fun σ σ' => TrialPost ea xa k
        ((((firsts colB K ρ).find? (offEnv m)).toList).any
          fun w => botEvalT colB K (Fin.snoc m w) φ) σ σ')
      ((K + 1) * (7 * k + 22) + Kb + 24) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hfl_le := firsts_length_le colB K ρ
  have h2L1 : 2 ^ Lc ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
  intro σ hst
  -- reset the flag, read the count
  set σ₁ := σ.setVar "bt.f" 0 with hσ₁
  have hr₁ : Run B (.assign "bt.f" (.lit 0)) σ σ₁ 2 := run_assign_lit (by omega)
  have hdev : (Expr.get na (.lit ρ)).evalB B σ₁ = some (firsts colB K ρ).length := by
    refine evalB_get_lit ?_ ?_ (by omega) (by omega)
    · rw [hσ₁]
      simp only [arrs_setVar]
      rw [hst.2.1.1]
      exact hρ
    · rw [hσ₁]
      simp only [arrs_setVar]
      exact (hst.2.1.2.2 ρ hρ).1
  set σ₂ := σ₁.setVar "bt.d" (firsts colB K ρ).length with hσ₂
  have hr₂ : Run B (.assign "bt.d" (.get na (.lit ρ))) σ₁ σ₂ 3 := by
    rw [hσ₂]
    exact (Run.assign hdev).mono (by simp)
  have harr₂ : σ₂.arrs = σ.arrs := by rw [hσ₂, hσ₁]; rfl
  have hst₂ : TrialSt ca na fa ea xa colB K m σ₂ := trialSt_of_arrs_eq harr₂ hst
  -- the seat scan
  obtain ⟨σ₃, hr₃, harr₃, hvars₃, hsome, hnone⟩ :=
    (seatScan_spec h2LB hNB hkK m ρ hρ) σ₂
      ⟨hst₂, by rw [hσ₂, vars_setVar, if_neg (by decide), hσ₁, vars_setVar, if_pos rfl],
        by rw [hσ₂, vars_setVar, if_pos rfl]⟩
  have harr₃σ : σ₃.arrs = σ.arrs := harr₃.trans harr₂
  have hvars₃σ : ∀ y, y ∉ evalWScalars → σ₃.vars y = σ.vars y := by
    intro y hy
    have hyf : y ≠ "bt.f" := fun hc => hy (by rw [hc]; decide)
    have hyd : y ≠ "bt.d" := fun hc => hy (by rw [hc]; decide)
    rw [hvars₃ y hy, hσ₂, vars_setVar, if_neg hyd, hσ₁, vars_setVar, if_neg hyf]
  have htp₀ : TrialPost ea xa k false σ σ₃ := trialPost_of_untouched harr₃σ hvars₃σ
  -- the trial, if a representative was found
  cases hfind : (firsts colB K ρ).find? (offEnv m) with
  | some w =>
    obtain ⟨hf1, hw⟩ := hsome w hfind
    have hcondT : (Cond.eq (.var "bt.f") (.lit 1)).evalB B σ₃ = some true := by
      rw [evalB_condEq (evalB_var (by rw [hf1]; omega)) (evalB_lit (by omega)), hf1]
      simp
    have hst₃ : TrialSt ca na fa ea xa colB K m σ₃ := trialSt_of_arrs_eq harr₃σ hst
    have hev : (Expr.var "bt.w").evalB B σ₃ = some (w : ℕ) := by
      rw [← hw]
      exact evalB_var (by rw [hw]; exact lt_trans (Fin.is_lt _) hNB)
    obtain ⟨σ₄, hr₄, htp₄⟩ :=
      (trialCom_spec h2LB hca_ea hna_ea hfa_ea hea_xa hkK m w (e := .var "bt.w")
        φ (by simp) (hbody w)) σ₃ ⟨hst₃, hev⟩
    have hfinal := htp₀.trans htp₄
    rw [Bool.false_or] at hfinal
    refine ⟨σ₄, ?_, ?_⟩
    · refine (hr₁.seq (hr₂.seq (hr₃.seq (Run.ite_true hcondT hr₄)))).mono ?_
      simp only [size_condEq, size_var, size_lit]
      omega
    · simpa using hfinal
  | none =>
    have hf0 := hnone hfind
    have hcondF : (Cond.eq (.var "bt.f") (.lit 1)).evalB B σ₃ = some false := by
      rw [evalB_condEq (evalB_var (by rw [hf0]; omega)) (evalB_lit (by omega)), hf0]
      simp
    refine ⟨σ₃, ?_, ?_⟩
    · refine (hr₁.seq (hr₂.seq (hr₃.seq (Run.ite_false hcondF Run.skip)))).mono ?_
      simp only [size_condEq, size_var, size_lit]
      omega
    · simpa using htp₀

include h2LB hNB hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hea_xa in
open Classical in
/-- **The unrestricted quantifier, discharged** (§6.4's schedule): the
`k` environment candidates, then one turn per row code — `botEvalT`'s
`exU` clause verbatim, `≤ k + 2^L·(K+1)` candidates however large the
arena. The accumulator cell is collected into `"bt.r"` and cleaned. -/
private theorem exUCom_spec {k : ℕ} (hkK : k ≤ K) (m : Fin k → Fin N)
    (φ : DistFO Lc (k + 1)) {cb : Com} {Kb : ℕ}
    (hbody : ∀ w : Fin N, Spec B
      (fun σ => EvalSt ca na fa ea xa colB K (Fin.snoc m w) σ) cb
      (EvalPost ea xa (if botEvalT colB K (Fin.snoc m w) φ then 1 else 0)) Kb) :
    Spec B (fun σ => EvalSt ca na fa ea xa colB K m σ)
      (exUCom na fa ea xa Lc K k cb)
      (EvalPost ea xa (if botEvalT colB K m (.exU φ) then 1 else 0))
      (k * (Kb + 14) + 2 ^ Lc * ((K + 1) * (7 * k + 22) + Kb + 24) + 8) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  intro σ hσ
  set q : Fin N → Bool := fun w => botEvalT colB K (Fin.snoc m w) φ with hq
  set frep : ℕ → List (Fin N) :=
    fun ρ => ((firsts colB K ρ).find? (offEnv m)).toList with hfrep
  -- fold 1: the environment candidates
  set Inv₁ : ℕ → Env → Prop := fun j τ =>
    TrialPost ea xa k (((List.ofFn m).take j).any q) σ τ with hInv₁
  have hstep₁ : ∀ i, i < (List.range k).length →
      Spec B (Inv₁ (0 + i)) (trialCom ea xa k (.get ea (.lit (0 + i))) cb)
        (fun _ τ' => Inv₁ (0 + i + 1) τ') (Kb + 14) := by
    intro i hi
    rw [List.length_range] at hi
    simp only [Nat.zero_add]
    intro τ htp
    have hstτ : TrialSt ca na fa ea xa colB K m τ :=
      TrialSt.of_post hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hσ.trialSt htp
    have hev : (Expr.get ea (.lit i)).evalB B τ = some (m ⟨i, hi⟩ : ℕ) := by
      refine evalB_get_lit ?_ ?_ (by omega) (lt_trans (Fin.is_lt _) hNB)
      · rw [hstτ.2.2.1, length_arrOf]
        omega
      · rw [hstτ.2.2.1, getD_arrOf _ (by omega), envFun_lt m hi]
    obtain ⟨τ', hr', htp'⟩ :=
      (trialCom_spec h2LB hca_ea hna_ea hfa_ea hea_xa hkK m (m ⟨i, hi⟩)
        (e := .get ea (.lit i)) φ (by simp) (hbody _)) τ ⟨hstτ, hev⟩
    refine ⟨τ', hr', ?_⟩
    have hfinal := htp.trans htp'
    have htake : (List.ofFn m).take (i + 1)
        = (List.ofFn m).take i ++ [m ⟨i, hi⟩] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hi),
        Option.toList_some, List.getElem_ofFn]
    show TrialPost ea xa k (((List.ofFn m).take (i + 1)).any q) σ τ'
    rw [htake, List.any_append]
    simpa using hfinal
  have hscan₁ := seqIdx_spec (B := B) (Kb := Kb + 14)
    (gen := fun i _ => trialCom ea xa k (.get ea (.lit i)) cb)
    Inv₁ (List.range k) 0 hstep₁
  have hInv₁0 : Inv₁ 0 σ := TrialPost.rfl
  obtain ⟨τ₁, hrun₁, hτ₁⟩ := hscan₁ σ hInv₁0
  simp only [List.length_range, Nat.zero_add] at hτ₁
  have htp₁ : TrialPost ea xa k ((List.ofFn m).any q) σ τ₁ := by
    have h : TrialPost ea xa k (((List.ofFn m).take k).any q) σ τ₁ := hτ₁
    rwa [List.take_of_length_le (by simp)] at h
  -- fold 2: the row codes
  set Inv₂ : ℕ → Env → Prop := fun j τ =>
    TrialPost ea xa k ((List.ofFn m ++ (List.range j).flatMap frep).any q) σ τ
    with hInv₂
  have hstep₂ : ∀ i (hi : i < (List.range (2 ^ Lc)).length),
      Spec B (Inv₂ (0 + i)) (rhoCom na fa ea xa K k ((List.range (2 ^ Lc))[i]) cb)
        (fun _ τ' => Inv₂ (0 + i + 1) τ') ((K + 1) * (7 * k + 22) + Kb + 24) := by
    intro i hi
    have hi2 : i < 2 ^ Lc := by simpa using hi
    simp only [Nat.zero_add, List.getElem_range]
    intro τ htp
    have hstτ : TrialSt ca na fa ea xa colB K m τ :=
      TrialSt.of_post hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hσ.trialSt htp
    obtain ⟨τ', hr', htp'⟩ :=
      (rhoCom_spec h2LB hNB hca_ea hna_ea hfa_ea hea_xa
        hkK m i hi2 φ hbody) τ hstτ
    refine ⟨τ', hr', ?_⟩
    show TrialPost ea xa k
      ((List.ofFn m ++ (List.range (i + 1)).flatMap frep).any q) σ τ'
    have hsplit : (List.ofFn m ++ (List.range (i + 1)).flatMap frep).any q
        = ((List.ofFn m ++ (List.range i).flatMap frep).any q || (frep i).any q) := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, ← List.append_assoc, List.any_append]
    rw [hsplit]
    exact htp.trans htp'
  have hscan₂ := seqIdx_spec (B := B) (Kb := (K + 1) * (7 * k + 22) + Kb + 24)
    (gen := fun _ ρ => rhoCom na fa ea xa K k ρ cb)
    Inv₂ (List.range (2 ^ Lc)) 0 hstep₂
  have hInv₂0 : Inv₂ 0 τ₁ := by
    show TrialPost ea xa k ((List.ofFn m ++ (List.range 0).flatMap frep).any q) σ τ₁
    rw [show (List.range 0).flatMap frep = [] from rfl, List.append_nil]
    exact htp₁
  obtain ⟨τ₂, hrun₂, hτ₂⟩ := hscan₂ τ₁ hInv₂0
  simp only [List.length_range, Nat.zero_add] at hτ₂
  have htp₂ : TrialPost ea xa k
      ((List.ofFn m ++ (List.range (2 ^ Lc)).flatMap frep).any q) σ τ₂ := hτ₂
  -- collect the accumulator into the result, then clean it
  have hbotU : botEvalT colB K m (.exU φ)
      = (List.ofFn m ++ (List.range (2 ^ Lc)).flatMap frep).any q := rfl
  have hσgd : (σ.arrs xa).getD k 0 = 0 := hσ.2.2.2.2 k (le_refl k)
  have hxl₂ : (τ₂.arrs xa).length = K + 1 := by
    rw [htp₂.2.2.2.1, hσ.2.2.2.1]
  have hgd : (τ₂.arrs xa).getD k 0
      = (if botEvalT colB K m (.exU φ) then 1 else 0) := by
    rw [htp₂.2.1, hσgd, hbotU]
  have hread : (Expr.get xa (.lit k)).evalB B τ₂
      = some (if botEvalT colB K m (.exU φ) then 1 else 0) := by
    refine evalB_get_lit (by omega) hgd (by omega) (by split <;> omega)
  set σf := τ₂.setVar "bt.r" (if botEvalT colB K m (.exU φ) then 1 else 0) with hσf
  have hrf : Run B (.assign "bt.r" (.get xa (.lit k))) τ₂ σf 3 := by
    rw [hσf]
    exact (Run.assign hread).mono (by simp)
  have hkxl : k < (σf.arrs xa).length := by
    rw [hσf]
    simp only [arrs_setVar]
    omega
  set σ' := σf.setArr xa k 0 with hσ'
  have hrc : Run B (.store xa (.lit k) (.lit 0)) σf σ' 3 := by
    rw [hσ']
    exact (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) hkxl).mono (by simp)
  refine ⟨σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hrun₁.seq (hrun₂.seq (hrf.seq hrc))).mono ?_
    simp only [List.length_range]
    omega
  · rw [hσ', hσf]
    simp
  · rw [hσ', arrs_setArr, if_neg hea_xa, hσf]
    simp only [arrs_setVar]
    exact htp₂.1
  · -- the accumulator region is returned verbatim
    have hxaf : σ'.arrs xa = (τ₂.arrs xa).set k 0 := by
      rw [hσ', arrs_setArr, if_pos rfl, hσf]
      simp only [arrs_setVar]
    rw [hxaf]
    refine eq_of_getD (by simp only [List.length_set]; rw [hxl₂, hσ.2.2.2.1]) ?_
    intro i hilen
    simp only [List.length_set] at hilen
    rw [set_eq_arrOf_upd k 0 hxl₂, getD_arrOf _ (by omega)]
    by_cases hik : i = k
    · subst hik
      rw [upd_self, hσgd]
    · rw [upd_of_ne _ hik, htp₂.2.2.1 i hik]
  · intro a ha1 ha2
    rw [hσ', arrs_setArr, if_neg ha2, hσf]
    simp only [arrs_setVar]
    exact htp₂.2.2.2.2.1 a ha1 ha2
  · intro y hy
    have hyr : y ≠ "bt.r" := fun hc => hy (by rw [hc]; decide)
    rw [hσ']
    simp only [vars_setArr]
    rw [hσf, vars_setVar, if_neg hyr]
    exact htp₂.2.2.2.2.2 y hy

include h2LB hNB hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hea_xa in
open Classical in
/-- **The local quantifier, discharged**: the guard set is
compile-time syntax, so the machine tries exactly its entries — no
search at all, `botEvalT`'s `exL` clause verbatim. -/
private theorem exLCom_spec {k : ℕ} (hkK : k ≤ K) (m : Fin k → Fin N)
    (r : ℕ) (g : Finset (Fin k)) (φ : DistFO Lc (k + 1)) {cb : Com} {Kb : ℕ}
    (hbody : ∀ w : Fin N, Spec B
      (fun σ => EvalSt ca na fa ea xa colB K (Fin.snoc m w) σ) cb
      (EvalPost ea xa (if botEvalT colB K (Fin.snoc m w) φ then 1 else 0)) Kb) :
    Spec B (fun σ => EvalSt ca na fa ea xa colB K m σ)
      (exLCom ea xa k (g.toList.map Fin.val) cb)
      (EvalPost ea xa (if botEvalT colB K m (.exL r g φ) then 1 else 0))
      (g.card * (Kb + 14) + 7) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  intro σ hσ
  set q : Fin k → Bool := fun i => botEvalT colB K (Fin.snoc m (m i)) φ with hq
  set Inv : ℕ → Env → Prop := fun j τ =>
    TrialPost ea xa k ((g.toList.take j).any q) σ τ with hInv
  have hstep : ∀ i (hi : i < (g.toList.map Fin.val).length),
      Spec B (Inv (0 + i))
        (trialCom ea xa k (.get ea (.lit ((g.toList.map Fin.val)[i]))) cb)
        (fun _ τ' => Inv (0 + i + 1) τ') (Kb + 14) := by
    intro i hi
    have hi2 : i < g.toList.length := by simpa using hi
    simp only [Nat.zero_add, List.getElem_map]
    intro τ htp
    have hstτ : TrialSt ca na fa ea xa colB K m τ :=
      TrialSt.of_post hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hσ.trialSt htp
    have hev : (Expr.get ea (.lit ((g.toList[i]'hi2 : Fin k) : ℕ))).evalB B τ
        = some ((m (g.toList[i]'hi2) : ℕ)) := by
      refine evalB_get_lit ?_ ?_ ?_ (lt_trans (Fin.is_lt _) hNB)
      · rw [hstτ.2.2.1, length_arrOf]
        have := (g.toList[i]'hi2 : Fin k).is_lt
        omega
      · rw [hstτ.2.2.1, getD_arrOf _ (by have := (g.toList[i]'hi2 : Fin k).is_lt; omega),
          envFun_lt m (g.toList[i]'hi2 : Fin k).is_lt]
      · have := (g.toList[i]'hi2 : Fin k).is_lt
        omega
    obtain ⟨τ', hr', htp'⟩ :=
      (trialCom_spec h2LB hca_ea hna_ea hfa_ea hea_xa hkK m (m (g.toList[i]'hi2))
        (e := .get ea (.lit ((g.toList[i]'hi2 : Fin k) : ℕ))) φ (by simp) (hbody _))
        τ ⟨hstτ, hev⟩
    refine ⟨τ', hr', ?_⟩
    have hfinal := htp.trans htp'
    have htake : g.toList.take (i + 1) = g.toList.take i ++ [g.toList[i]'hi2] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi2, Option.toList_some]
    show TrialPost ea xa k ((g.toList.take (i + 1)).any q) σ τ'
    rw [htake, List.any_append]
    simpa using hfinal
  have hscan := seqIdx_spec (B := B) (Kb := Kb + 14)
    (gen := fun _ i => trialCom ea xa k (.get ea (.lit i)) cb)
    Inv (g.toList.map Fin.val) 0 hstep
  have hInv0 : Inv 0 σ := TrialPost.rfl
  obtain ⟨τ, hrun, hτ⟩ := hscan σ hInv0
  simp only [List.length_map, Nat.zero_add] at hτ
  have htp : TrialPost ea xa k (g.toList.any q) σ τ := by
    have h : TrialPost ea xa k ((g.toList.take g.toList.length).any q) σ τ := hτ
    rwa [List.take_of_length_le (le_refl _)] at h
  -- the collected bit is the guard set's disjunction
  have hbit : g.toList.any q
      = decide (∃ i ∈ g, botEvalT colB K (Fin.snoc m (m i)) φ = true) := by
    by_cases hex : ∃ i ∈ g, botEvalT colB K (Fin.snoc m (m i)) φ = true
    · rw [decide_eq_true hex, List.any_eq_true]
      obtain ⟨i, hig, hqi⟩ := hex
      exact ⟨i, Finset.mem_toList.mpr hig, hqi⟩
    · rw [decide_eq_false hex]
      exact List.any_eq_false.mpr
        (fun i hig hc => hex ⟨i, Finset.mem_toList.mp hig, hc⟩)
  have hbotL : botEvalT colB K m (.exL r g φ)
      = decide (∃ i ∈ g, botEvalT colB K (Fin.snoc m (m i)) φ = true) := rfl
  -- collect and clean
  have hσgd : (σ.arrs xa).getD k 0 = 0 := hσ.2.2.2.2 k (le_refl k)
  have hxl₂ : (τ.arrs xa).length = K + 1 := by rw [htp.2.2.2.1, hσ.2.2.2.1]
  have hgd : (τ.arrs xa).getD k 0
      = (if botEvalT colB K m (.exL r g φ) then 1 else 0) := by
    rw [htp.2.1, hσgd, hbotL, ← hbit]
  have hread : (Expr.get xa (.lit k)).evalB B τ
      = some (if botEvalT colB K m (.exL r g φ) then 1 else 0) :=
    evalB_get_lit (by omega) hgd (by omega) (by split <;> omega)
  set σf := τ.setVar "bt.r" (if botEvalT colB K m (.exL r g φ) then 1 else 0) with hσf
  have hrf : Run B (.assign "bt.r" (.get xa (.lit k))) τ σf 3 := by
    rw [hσf]
    exact (Run.assign hread).mono (by simp)
  have hkxl : k < (σf.arrs xa).length := by
    rw [hσf]
    simp only [arrs_setVar]
    omega
  set σ' := σf.setArr xa k 0 with hσ'
  have hrc : Run B (.store xa (.lit k) (.lit 0)) σf σ' 3 := by
    rw [hσ']
    exact (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) hkxl).mono (by simp)
  refine ⟨σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hrun.seq (hrf.seq hrc)).mono ?_
    simp only [List.length_map, Finset.length_toList]
    omega
  · rw [hσ', hσf]
    simp
  · rw [hσ', arrs_setArr, if_neg hea_xa, hσf]
    simp only [arrs_setVar]
    exact htp.1
  · have hxaf : σ'.arrs xa = (τ.arrs xa).set k 0 := by
      rw [hσ', arrs_setArr, if_pos rfl, hσf]
      simp only [arrs_setVar]
    rw [hxaf]
    refine eq_of_getD (by simp only [List.length_set]; rw [hxl₂, hσ.2.2.2.1]) ?_
    intro i hilen
    rw [set_eq_arrOf_upd k 0 hxl₂, getD_arrOf _ (by simp only [List.length_set] at hilen; omega)]
    by_cases hik : i = k
    · subst hik
      rw [upd_self, hσgd]
    · rw [upd_of_ne _ hik, htp.2.2.1 i hik]
  · intro a ha1 ha2
    rw [hσ', arrs_setArr, if_neg ha2, hσf]
    simp only [arrs_setVar]
    exact htp.2.2.2.2.1 a ha1 ha2
  · intro y hy
    have hyr : y ≠ "bt.r" := fun hc => hy (by rw [hc]; decide)
    rw [hσ']
    simp only [vars_setArr]
    rw [hσf, vars_setVar, if_neg hyr]
    exact htp.2.2.2.2.2 y hy

/-- The result assignment's footprint. -/
private theorem evalPost_assign_r {bit v : ℕ} {σ : Env} (hv : v = bit) :
    EvalPost ea xa bit σ (σ.setVar "bt.r" v) := by
  subst hv
  refine ⟨by simp, by simp, by simp, fun a _ _ => by simp, fun y hy => ?_⟩
  rw [vars_setVar, if_neg (fun hc => hy (by rw [hc]; decide))]

/-- Footprints chain, the later bit winning. -/
private theorem evalPost_trans {b₁ b₂ : ℕ} {σ σ₁ σ₂ : Env}
    (h₁ : EvalPost ea xa b₁ σ σ₁) (h₂ : EvalPost ea xa b₂ σ₁ σ₂) :
    EvalPost ea xa b₂ σ σ₂ :=
  ⟨h₂.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun a ha1 ha2 => (h₂.2.2.2.1 a ha1 ha2).trans (h₁.2.2.2.1 a ha1 ha2),
    fun y hy => (h₂.2.2.2.2 y hy).trans (h₁.2.2.2.2 y hy)⟩

/-- Every node costs at least one unit. -/
private theorem one_le_evalK (Lc K : ℕ) :
    ∀ {k : ℕ} (φ : DistFO Lc k), 1 ≤ evalK Lc K φ
  | _, .adj _ _ => by simp [evalK]
  | _, .eq _ _ => by simp [evalK]
  | _, .color _ _ => by simp [evalK]
  | _, .distLe _ _ _ => by simp [evalK]
  | _, .distColorLt _ _ _ => by simp [evalK]
  | _, .not φ => by simp only [evalK]; omega
  | _, .and φ ψ => by simp only [evalK]; omega
  | _, .exU φ => by simp only [evalK]; omega
  | _, .exL _ g φ => by simp only [evalK]; omega

include h2LB hNB in
open Classical in
/-- An equality atom, discharged: two env reads and one test. -/
private theorem eqCom_spec {k : ℕ} (hkK : k ≤ K + 1) (m : Fin k → Fin N)
    (i j : Fin k) :
    Spec B (fun σ => EvalSt ca na fa ea xa colB K m σ)
      (eqCom ea (i : ℕ) (j : ℕ))
      (EvalPost ea xa (if decide (m i = m j) then 1 else 0)) 9 := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  intro σ hσ
  have hie : (Expr.get ea (.lit (i : ℕ))).evalB B σ = some (m i : ℕ) := by
    refine evalB_get_lit ?_ ?_ (by have := i.is_lt; omega) (lt_trans (Fin.is_lt _) hNB)
    · rw [hσ.2.2.1, length_arrOf]
      have := i.is_lt
      omega
    · rw [hσ.2.2.1, getD_arrOf _ (by have := i.is_lt; omega), envFun_lt m i.is_lt]
  have hje : (Expr.get ea (.lit (j : ℕ))).evalB B σ = some (m j : ℕ) := by
    refine evalB_get_lit ?_ ?_ (by have := j.is_lt; omega) (lt_trans (Fin.is_lt _) hNB)
    · rw [hσ.2.2.1, length_arrOf]
      have := j.is_lt
      omega
    · rw [hσ.2.2.1, getD_arrOf _ (by have := j.is_lt; omega), envFun_lt m j.is_lt]
  have hcond := evalB_condEq hie hje
  by_cases heq : (m i : ℕ) = (m j : ℕ)
  · have hcondT : (Cond.eq (.get ea (.lit (i : ℕ))) (.get ea (.lit (j : ℕ)))).evalB B σ
        = some true := by
      rw [hcond]
      congr 1
      simpa using heq
    refine ⟨σ.setVar "bt.r" 1,
      (Run.ite_true hcondT (run_assign_lit (by omega))).mono
        (by simp only [size_condEq, size_get, size_lit]; omega),
      evalPost_assign_r ?_⟩
    rw [decide_eq_true (Fin.val_inj.mp heq)]
    simp
  · have hcondF : (Cond.eq (.get ea (.lit (i : ℕ))) (.get ea (.lit (j : ℕ)))).evalB B σ
        = some false := by
      rw [hcond]
      congr 1
      simpa using heq
    refine ⟨σ.setVar "bt.r" 0,
      (Run.ite_false hcondF (run_assign_lit (by omega))).mono
        (by simp only [size_condEq, size_get, size_lit]; omega),
      evalPost_assign_r ?_⟩
    rw [decide_eq_false (fun hc => heq (congrArg Fin.val hc))]
    simp

include h2LB hNB hNLB in
open Classical in
/-- A color atom, discharged: one row-bit read at stride `Lc`. The
read index is below `N·Lc`, the value a bit. -/
private theorem colorCom_spec {k : ℕ} (hkK : k ≤ K + 1) (m : Fin k → Fin N)
    (c : Fin Lc) (i : Fin k) :
    Spec B (fun σ => EvalSt ca na fa ea xa colB K m σ)
      (colorCom ca ea Lc (c : ℕ) (i : ℕ))
      (EvalPost ea xa (if colB (m i) c then 1 else 0)) 8 := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  intro σ hσ
  have hNpos : 0 < N := (m i).pos
  have hLpos : 0 < Lc := c.pos
  have hLN : Lc ≤ N * Lc := Nat.le_mul_of_pos_left _ hNpos
  have hie : (Expr.get ea (.lit (i : ℕ))).evalB B σ = some (m i : ℕ) := by
    refine evalB_get_lit ?_ ?_ (by have := i.is_lt; omega) (lt_trans (Fin.is_lt _) hNB)
    · rw [hσ.2.2.1, length_arrOf]
      have := i.is_lt
      omega
    · rw [hσ.2.2.1, getD_arrOf _ (by have := i.is_lt; omega), envFun_lt m i.is_lt]
  have hidx : (m i : ℕ) * Lc + (c : ℕ) < N * Lc := by
    have h1 : ((m i : ℕ) + 1) * Lc ≤ N * Lc :=
      Nat.mul_le_mul_right _ (by have := (m i).is_lt; omega)
    rw [Nat.succ_mul] at h1
    have := c.is_lt
    omega
  have hmul : (Expr.mul (.get ea (.lit (i : ℕ))) (.lit Lc)).evalB B σ
      = some ((m i : ℕ) * Lc) := by
    refine evalB_bin hie (evalB_lit (by omega)) ?_
    show (m i : ℕ) * Lc < B
    omega
  have hadd : (Expr.add (.mul (.get ea (.lit (i : ℕ))) (.lit Lc)) (.lit (c : ℕ))).evalB B σ
      = some ((m i : ℕ) * Lc + (c : ℕ)) := by
    refine evalB_bin hmul (evalB_lit ?_) ?_
    · have := c.is_lt
      omega
    · show (m i : ℕ) * Lc + (c : ℕ) < B
      omega
  have hget : (Expr.get ca (.add (.mul (.get ea (.lit (i : ℕ))) (.lit Lc))
      (.lit (c : ℕ)))).evalB B σ = some (if colB (m i) c then 1 else 0) := by
    refine evalB_get hadd ?_ (by split <;> omega)
    rw [getElem?_eq_getD (by rw [hσ.1.1]; exact hidx), hσ.1.2 (m i) c]
  exact ⟨σ.setVar "bt.r" (if colB (m i) c then 1 else 0),
    (Run.assign hget).mono (by simp),
    evalPost_assign_r rfl⟩

include h2LB hNB hNLB hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hea_xa in
open Classical in
/-- **The compiled evaluator, discharged** (the per-entry half of
block 0): within the depth budget `k + qdepth φ ≤ K + 1`, the result
scalar ends holding **`botEvalT`'s bit** — the landed table-scheduled
evaluator's value, per `SolveBlocksBot` — and the two scratch regions
are returned verbatim, everything else framed. The budget is
`evalK Lc K φ`, a function of the schedule alone. The depth budget is
threaded through the structural recursion: each quantifier case hands
its body `(k + 1) + qdepth φ ≤ K + 1`, which is exactly the
hypothesis it received with one `qdepth` unit spent. -/
theorem evalCom_spec :
    ∀ {k : ℕ} (φ : DistFO Lc k) (m : Fin k → Fin N),
      k + qdepth φ ≤ K + 1 →
      Spec B (fun σ => EvalSt ca na fa ea xa colB K m σ)
        (evalCom ca na fa ea xa Lc K φ)
        (EvalPost ea xa (if botEvalT colB K m φ then 1 else 0))
        (evalK Lc K φ) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  intro k φ
  induction φ with
  | adj i j =>
    intro m _ σ hσ
    refine ⟨σ.setVar "bt.r" 0, run_assign_lit (by omega), evalPost_assign_r ?_⟩
    simp [show botEvalT colB K m (.adj i j) = false from rfl]
  | eq i j =>
    intro m hd
    simp only [qdepth] at hd
    exact eqCom_spec h2LB hNB (by omega) m i j
  | color c i =>
    intro m hd
    simp only [qdepth] at hd
    exact colorCom_spec h2LB hNB hNLB (by omega) m c i
  | distLe r i j =>
    intro m hd
    simp only [qdepth] at hd
    exact eqCom_spec h2LB hNB (by omega) m i j
  | distColorLt r c i =>
    intro m hd
    simp only [qdepth] at hd
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have hcmd : evalCom ca na fa ea xa Lc K (.distColorLt 0 c i)
          = .assign "bt.r" (.lit 0) := by
        simp [evalCom]
      have hb : botEvalT colB K m (.distColorLt 0 c i) = false := rfl
      rw [hcmd, hb]
      intro σ hσ
      refine ⟨σ.setVar "bt.r" 0,
        (run_assign_lit (by omega)).mono (by simp only [evalK]; omega),
        evalPost_assign_r (by simp)⟩
    · have hcmd : evalCom ca na fa ea xa Lc K (.distColorLt r c i)
          = colorCom ca ea Lc (c : ℕ) (i : ℕ) := by
        simp only [evalCom]
        rw [if_neg (by omega)]
      have hb : botEvalT colB K m (.distColorLt r c i) = colB (m i) c := by
        show (decide (0 < r) && colB (m i) c) = colB (m i) c
        rw [decide_eq_true hr, Bool.true_and]
      rw [hcmd, show (evalK Lc K (.distColorLt r c i) : ℕ) = 8 from rfl, hb]
      exact colorCom_spec h2LB hNB hNLB (by omega) m c i
  | not φ ih =>
    intro m hd
    simp only [qdepth] at hd
    intro σ hσ
    obtain ⟨σ₁, hr₁, hp₁⟩ := ih m (by omega) σ hσ
    have hrv : σ₁.vars "bt.r" = (if botEvalT colB K m φ then 1 else 0) := hp₁.1
    have hsub : (Expr.sub (.lit 1) (.var "bt.r")).evalB B σ₁
        = some (1 - σ₁.vars "bt.r") := by
      refine evalB_bin (evalB_lit (by omega)) (evalB_var ?_) ?_
      · rw [hrv]
        split <;> omega
      · show 1 - σ₁.vars "bt.r" < B
        omega
    refine ⟨σ₁.setVar "bt.r" (1 - σ₁.vars "bt.r"),
      (hr₁.seq (Run.assign hsub)).mono
        (by simp only [evalK, size_sub, size_lit, size_var]; omega),
      evalPost_trans hp₁ (evalPost_assign_r ?_)⟩
    rw [hrv]
    show 1 - (if botEvalT colB K m φ then 1 else 0)
        = (if (!botEvalT colB K m φ) then 1 else 0)
    cases botEvalT colB K m φ <;> simp
  | and φ ψ ih₁ ih₂ =>
    intro m hd
    simp only [qdepth] at hd
    intro σ hσ
    obtain ⟨σ₁, hr₁, hp₁⟩ := ih₁ m (by omega) σ hσ
    have hσ₁ : EvalSt ca na fa ea xa colB K m σ₁ := by
      refine ⟨rowBits_of_arrs_eq (hp₁.2.2.2.1 ca hca_ea hca_xa) hσ.1,
        firstsSt_of_arrs_eq (hp₁.2.2.2.1 na hna_ea hna_xa)
          (hp₁.2.2.2.1 fa hfa_ea hfa_xa) hσ.2.1, ?_, ?_, ?_⟩
      · rw [hp₁.2.1]
        exact hσ.2.2.1
      · rw [hp₁.2.2.1]
        exact hσ.2.2.2.1
      · intro i hi
        rw [hp₁.2.2.1]
        exact hσ.2.2.2.2 i hi
    have hrB : σ₁.vars "bt.r" < B := by rw [hp₁.1]; split <;> omega
    have hcond := evalB_condEq (evalB_var hrB) (evalB_lit (show (1:ℕ) < B by omega))
    by_cases hb : botEvalT colB K m φ = true
    · have hr1 : σ₁.vars "bt.r" = 1 := by rw [hp₁.1, hb]; simp
      have hcondT : (Cond.eq (.var "bt.r") (.lit 1)).evalB B σ₁ = some true := by
        rw [hcond, hr1]
        simp
      obtain ⟨σ₂, hr₂, hp₂⟩ := ih₂ m (by omega) σ₁ hσ₁
      refine ⟨σ₂, (hr₁.seq (Run.ite_true hcondT hr₂)).mono
        (by simp only [evalK, size_condEq, size_var, size_lit]; omega), ?_⟩
      show EvalPost ea xa
        (if (botEvalT colB K m φ && botEvalT colB K m ψ) then 1 else 0) σ σ₂
      rw [hb, Bool.true_and]
      exact evalPost_trans hp₁ hp₂
    · have hbf : botEvalT colB K m φ = false := by rwa [Bool.not_eq_true] at hb
      have hr0 : σ₁.vars "bt.r" = 0 := by rw [hp₁.1, hbf]; simp
      have hcondF : (Cond.eq (.var "bt.r") (.lit 1)).evalB B σ₁ = some false := by
        rw [hcond, hr0]
        simp
      have hψ1 := one_le_evalK Lc K ψ
      refine ⟨σ₁, (hr₁.seq (Run.ite_false hcondF Run.skip)).mono
        (by simp only [evalK, size_condEq, size_var, size_lit]; omega), ?_⟩
      show EvalPost ea xa
        (if (botEvalT colB K m φ && botEvalT colB K m ψ) then 1 else 0) σ σ₁
      rw [hbf, Bool.false_and, ← hbf]
      exact hp₁
  | exU φ ih =>
    intro m hd
    simp only [qdepth] at hd
    exact exUCom_spec h2LB hNB hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hea_xa
      (by omega) m φ (fun w => ih (Fin.snoc m w) (by omega))
  | exL r g φ ih =>
    intro m hd
    simp only [qdepth] at hd
    exact exLCom_spec h2LB hNB hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hea_xa
      (by omega) m r g φ (fun w => ih (Fin.snoc m w) (by omega))

end EvalSpec

/-! ## §8 The table build -/

/-- Wipe an array's first `n` cells — `n` unrolled stores (every use
has `n` a schedule constant: the count region, the two scratch
regions). Each call cleans its own slate; no caller owes a wipe. -/
def zeroCom (a : String) (n : ℕ) : Com :=
  seqIdx (fun i _ => .store a (.lit i) (.lit 0)) (List.range n) 0

/-- Compute the row code of the vertex in `"bt.v"` into `"bt.c"`: the
machine's `codeAux`, one unrolled bit read per color — the `L` half of
the `N·L` build pass. -/
def rowCodeCom (ca : String) (Lc : ℕ) : Com :=
  .seq (.assign "bt.c" (.lit 0))
    (seqIdx (fun cbit _ =>
        .assign "bt.c" (.add (.var "bt.c")
          (.mul (.get ca (.add (.mul (.var "bt.v") (.lit Lc)) (.lit cbit)))
            (.lit (2 ^ cbit)))))
      (List.range Lc) 0)

/-- One vertex of the build pass: compute its row code, read the row's
count, and append the vertex to its row's seats while one is free —
the stored values are the row code (`< 2^L`, `rowCode_lt`), the count
(`≤ K+1`) and the vertex name (`< N`). -/
def buildBody (ca na fa : String) (Lc K : ℕ) : Com :=
  .seq (rowCodeCom ca Lc)
    (.seq (.assign "bt.d" (.get na (.var "bt.c")))
      (.seq (.ite (.lt (.var "bt.d") (.lit (K + 1)))
        (.seq (.store fa (.add (.mul (.var "bt.c") (.lit (K + 1))) (.var "bt.d"))
            (.var "bt.v"))
          (.store na (.var "bt.c") (.add (.var "bt.d") (.lit 1))))
        .skip)
        (.assign "bt.v" (.add (.var "bt.v") (.lit 1)))))

/-- **The table build**: wipe the count region, then one pass over the
carrier — `O(N·L)`, §6.4's one scan. -/
def buildCom (ca na fa : String) (Lc K : ℕ) : Com :=
  .seq (zeroCom na (2 ^ Lc))
    (.seq (.assign "bt.v" (.lit 0))
      (.while (.lt (.var "bt.v") (.var "bt.n")) (buildBody ca na fa Lc K)))

/-- The partial representative table: `firsts`, restricted to the
vertices already scanned — the build loop's invariant data. -/
def firstsUpto {N Lc : ℕ} (colB : Fin N → Fin Lc → Bool) (K v ρ : ℕ) :
    List (Fin N) :=
  (((List.finRange N).take v).filter fun u => rowCode colB u == ρ).take (K + 1)

section BuildLemmas

variable {N Lc : ℕ} {colB : Fin N → Fin Lc → Bool} {K : ℕ}

theorem firstsUpto_zero (ρ : ℕ) : firstsUpto colB K 0 ρ = [] := rfl

/-- The full scan's table is `firsts`. -/
theorem firstsUpto_eq_firsts {v : ℕ} (h : N ≤ v) (ρ : ℕ) :
    firstsUpto colB K v ρ = firsts colB K ρ := by
  have htake : (List.finRange N).take v = List.finRange N :=
    List.take_of_length_le (by simpa using h)
  rw [firstsUpto, htake, firsts]

theorem firstsUpto_length_le (v ρ : ℕ) :
    (firstsUpto colB K v ρ).length ≤ K + 1 :=
  List.length_take_le _ _

/-- One scanned vertex extends its own row's filtered list and no
other's. -/
private theorem filter_take_succ {v : ℕ} (hv : v < N) (ρ : ℕ) :
    ((List.finRange N).take (v + 1)).filter (fun u => rowCode colB u == ρ)
      = ((List.finRange N).take v).filter (fun u => rowCode colB u == ρ)
        ++ (if rowCode colB ⟨v, hv⟩ == ρ then [(⟨v, hv⟩ : Fin N)] else []) := by
  have hlen : v < (List.finRange N).length := by simpa using hv
  have hgv : (List.finRange N)[v] = (⟨v, hv⟩ : Fin N) := by
    apply Fin.ext
    simp
  rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some, hgv,
    List.filter_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]

/-- A same-row vertex with a free seat takes the next one. -/
theorem firstsUpto_succ_pos {v : ℕ} (hv : v < N) {ρ : ℕ}
    (hρ : rowCode colB ⟨v, hv⟩ = ρ)
    (hlen : (firstsUpto colB K v ρ).length < K + 1) :
    firstsUpto colB K (v + 1) ρ = firstsUpto colB K v ρ ++ [⟨v, hv⟩] := by
  set l := ((List.finRange N).take v).filter (fun u => rowCode colB u == ρ) with hl
  have hll : l.length < K + 1 := by
    have := hlen
    rw [firstsUpto, ← hl, List.length_take] at this
    omega
  have htake : l.take (K + 1) = l := List.take_of_length_le (by omega)
  rw [firstsUpto, filter_take_succ hv ρ, if_pos (by simp [hρ]), ← hl,
    List.take_append, htake, firstsUpto, ← hl, htake]
  congr 1
  rw [List.take_of_length_le]
  simp
  omega

/-- A same-row vertex with a full row is dropped by the `take`. -/
theorem firstsUpto_succ_full {v : ℕ} (hv : v < N) {ρ : ℕ}
    (hρ : rowCode colB ⟨v, hv⟩ = ρ)
    (hlen : ¬ (firstsUpto colB K v ρ).length < K + 1) :
    firstsUpto colB K (v + 1) ρ = firstsUpto colB K v ρ := by
  set l := ((List.finRange N).take v).filter (fun u => rowCode colB u == ρ) with hl
  have hll : K + 1 ≤ l.length := by
    have := hlen
    rw [firstsUpto, ← hl, List.length_take] at this
    omega
  rw [firstsUpto, filter_take_succ hv ρ, if_pos (by simp [hρ]), ← hl,
    List.take_append, firstsUpto, ← hl]
  have : K + 1 - l.length = 0 := by omega
  rw [this]
  simp

/-- Another row's table is untouched by the scanned vertex. -/
theorem firstsUpto_succ_ne {v : ℕ} (hv : v < N) {ρ : ℕ}
    (hρ : rowCode colB ⟨v, hv⟩ ≠ ρ) :
    firstsUpto colB K (v + 1) ρ = firstsUpto colB K v ρ := by
  rw [firstsUpto, filter_take_succ hv ρ, if_neg (by simpa using hρ), List.append_nil,
    firstsUpto]

/-- The appended seat holds the appended vertex. -/
theorem firstsUpto_getElem_last {v : ℕ} (hv : v < N) {ρ s : ℕ}
    (hρ : rowCode colB ⟨v, hv⟩ = ρ)
    (hlen : (firstsUpto colB K v ρ).length < K + 1)
    (hs : s = (firstsUpto colB K v ρ).length)
    (h : s < (firstsUpto colB K (v + 1) ρ).length) :
    (firstsUpto colB K (v + 1) ρ)[s] = (⟨v, hv⟩ : Fin N) := by
  subst hs
  have hstep := firstsUpto_succ_pos hv hρ hlen
  have h1 : (firstsUpto colB K (v + 1) ρ)[(firstsUpto colB K v ρ).length]?
      = some (⟨v, hv⟩ : Fin N) := by
    rw [hstep, List.getElem?_append_right (le_refl _)]
    simp
  rw [List.getElem?_eq_getElem h] at h1
  exact Option.some.inj h1

/-- The earlier seats are untouched by the append. -/
theorem firstsUpto_getElem_lt {v : ℕ} (hv : v < N) {ρ s : ℕ}
    (hρ : rowCode colB ⟨v, hv⟩ = ρ)
    (hlen : (firstsUpto colB K v ρ).length < K + 1)
    (hs : s < (firstsUpto colB K v ρ).length)
    (h : s < (firstsUpto colB K (v + 1) ρ).length) :
    (firstsUpto colB K (v + 1) ρ)[s] = (firstsUpto colB K v ρ)[s] := by
  have hstep := firstsUpto_succ_pos hv hρ hlen
  have h1 : (firstsUpto colB K (v + 1) ρ)[s]?
      = some ((firstsUpto colB K v ρ)[s]) := by
    rw [hstep, List.getElem?_append_left hs, List.getElem?_eq_getElem hs]
  rw [List.getElem?_eq_getElem h] at h1
  exact Option.some.inj h1

end BuildLemmas

/-! ## §9 The fill loop and the block -/

/-- One table entry: evaluate the (compile-time) formula at the
current vertex, write the bit at `v·|Fl| + i`. -/
noncomputable def entryGen (ca na fa ea xa ta : String) (Lc K len : ℕ)
    (i : ℕ) (β : DistFO Lc 1) : Com :=
  .seq (evalCom ca na fa ea xa Lc K β)
    (.store ta (.add (.mul (.var "bt.v") (.lit len)) (.lit i)) (.var "bt.r"))

/-- One vertex's row of table entries: load the vertex into the env
scratch, one unrolled entry per schedule formula, clean the scratch,
advance. -/
noncomputable def fillBody (ca na fa ea xa ta : String) (Lc K : ℕ)
    (Fl : List (DistFO Lc 1)) : Com :=
  .seq (.store ea (.lit 0) (.var "bt.v"))
    (.seq (seqIdx (entryGen ca na fa ea xa ta Lc K Fl.length) Fl 0)
      (.seq (.store ea (.lit 0) (.lit 0))
        (.assign "bt.v" (.add (.var "bt.v") (.lit 1)))))

/-- **The fill loop** over the carrier. -/
noncomputable def fillCom (ca na fa ea xa ta : String) (Lc K : ℕ)
    (Fl : List (DistFO Lc 1)) : Com :=
  .seq (.assign "bt.v" (.lit 0))
    (.while (.lt (.var "bt.v") (.var "bt.n")) (fillBody ca na fa ea xa ta Lc K Fl))

/-- **Block 0, whole** (§6.4's machine schedule): load the carrier
size from the contract's cell, wipe the two evaluator scratch regions
and the count region, build the representative table in one `N·L`
pass, then fill the `N·|Fl|` table bits at a schedule constant each. -/
noncomputable def botCom (nN ca na fa ea xa ta : String) (Lc K : ℕ)
    (Fl : List (DistFO Lc 1)) : Com :=
  .seq (.assign "bt.n" (.var nN))
    (.seq (zeroCom ea (K + 1))
      (.seq (zeroCom xa (K + 1))
        (.seq (buildCom ca na fa Lc K)
          (fillCom ca na fa ea xa ta Lc K Fl))))

/-! The block's write footprint, off the syntax. -/

section BlockSyntactic

variable (ca na fa ea xa ta nN : String) (Lc K : ℕ)

theorem warrs_zeroCom (a : String) (n : ℕ) {W : List String} (ha : a ∈ W) :
    (zeroCom a n).warrs ⊆ W := by
  refine warrs_seqIdx (fun i _ => ?_) _ _
  show [a] ⊆ W
  simpa using ha

theorem wvars_zeroCom (a : String) (n : ℕ) {W : List String} :
    (zeroCom a n).wvars ⊆ W := by
  refine wvars_seqIdx (fun i _ => ?_) _ _
  show ([] : List String) ⊆ W
  simp

theorem wvars_rowCodeCom : (rowCodeCom ca Lc).wvars ⊆ btScalars := by
  rw [rowCodeCom]
  show (["bt.c"] ++ _) ⊆ btScalars
  refine List.append_subset.mpr ⟨by decide, ?_⟩
  refine wvars_seqIdx (fun i _ => ?_) _ _
  show ["bt.c"] ⊆ btScalars
  decide

theorem warrs_rowCodeCom {W : List String} : (rowCodeCom ca Lc).warrs ⊆ W := by
  rw [rowCodeCom]
  show (([] ++ _) : List String) ⊆ W
  rw [List.nil_append]
  refine warrs_seqIdx (fun i _ => ?_) _ _
  show ([] : List String) ⊆ W
  simp

theorem wvars_buildCom : (buildCom ca na fa Lc K).wvars ⊆ btScalars := by
  rw [buildCom, buildBody]
  show ((zeroCom na (2 ^ Lc)).wvars ++ (["bt.v"]
    ++ ((rowCodeCom ca Lc).wvars ++ (["bt.d"] ++ ((([] ++ []) ++ []) ++ ["bt.v"]))))) ⊆ _
  refine List.append_subset.mpr ⟨wvars_zeroCom na _, ?_⟩
  refine List.append_subset.mpr ⟨by decide, ?_⟩
  refine List.append_subset.mpr ⟨wvars_rowCodeCom ca Lc, ?_⟩
  decide

theorem warrs_buildCom : (buildCom ca na fa Lc K).warrs ⊆ [na, fa] := by
  rw [buildCom, buildBody]
  show ((zeroCom na (2 ^ Lc)).warrs ++ ([]
    ++ ((rowCodeCom ca Lc).warrs ++ ([] ++ ((([fa] ++ [na]) ++ []) ++ []))))) ⊆ _
  refine List.append_subset.mpr ⟨warrs_zeroCom na _ (by simp), ?_⟩
  rw [List.nil_append]
  refine List.append_subset.mpr ⟨warrs_rowCodeCom ca Lc, ?_⟩
  simp

theorem wvars_fillCom (Fl : List (DistFO Lc 1)) :
    (fillCom ca na fa ea xa ta Lc K Fl).wvars ⊆ btScalars := by
  rw [fillCom, fillBody]
  show (["bt.v"] ++ ([] ++ (_ ++ ([] ++ ["bt.v"])))) ⊆ _
  refine List.append_subset.mpr ⟨by decide, ?_⟩
  rw [List.nil_append]
  refine List.append_subset.mpr ⟨?_, by decide⟩
  refine wvars_seqIdx (fun i β => ?_) _ _
  rw [entryGen]
  show ((evalCom ca na fa ea xa Lc K β).wvars ++ []) ⊆ _
  rw [List.append_nil]
  exact (wvars_evalCom ca na fa ea xa Lc K β).trans evalWScalars_subset_btScalars

theorem warrs_fillCom (Fl : List (DistFO Lc 1)) :
    (fillCom ca na fa ea xa ta Lc K Fl).warrs ⊆ [ea, xa, ta] := by
  rw [fillCom, fillBody]
  show (([] ++ ([ea] ++ (_ ++ ([ea] ++ [])))) : List String) ⊆ _
  rw [List.nil_append]
  refine List.append_subset.mpr ⟨by simp, ?_⟩
  refine List.append_subset.mpr ⟨?_, by simp⟩
  refine warrs_seqIdx (fun i β => ?_) _ _
  rw [entryGen]
  show ((evalCom ca na fa ea xa Lc K β).warrs ++ [ta]) ⊆ _
  refine List.append_subset.mpr ⟨?_, by simp⟩
  refine (warrs_evalCom ca na fa ea xa Lc K β).trans ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> simp

theorem wvars_botCom (Fl : List (DistFO Lc 1)) :
    (botCom nN ca na fa ea xa ta Lc K Fl).wvars ⊆ btScalars := by
  rw [botCom]
  show (["bt.n"] ++ ((zeroCom ea (K + 1)).wvars ++ ((zeroCom xa (K + 1)).wvars
    ++ ((buildCom ca na fa Lc K).wvars
      ++ (fillCom ca na fa ea xa ta Lc K Fl).wvars)))) ⊆ _
  refine List.append_subset.mpr ⟨by decide, ?_⟩
  refine List.append_subset.mpr ⟨wvars_zeroCom ea _, ?_⟩
  refine List.append_subset.mpr ⟨wvars_zeroCom xa _, ?_⟩
  exact List.append_subset.mpr
    ⟨wvars_buildCom ca na fa Lc K, wvars_fillCom ca na fa ea xa ta Lc K Fl⟩

theorem warrs_botCom (Fl : List (DistFO Lc 1)) :
    (botCom nN ca na fa ea xa ta Lc K Fl).warrs ⊆ [na, fa, ea, xa, ta] := by
  rw [botCom]
  show (([] ++ ((zeroCom ea (K + 1)).warrs ++ ((zeroCom xa (K + 1)).warrs
    ++ ((buildCom ca na fa Lc K).warrs
      ++ (fillCom ca na fa ea xa ta Lc K Fl).warrs)))) : List String) ⊆ _
  rw [List.nil_append]
  refine List.append_subset.mpr ⟨warrs_zeroCom ea _ (by simp), ?_⟩
  refine List.append_subset.mpr ⟨warrs_zeroCom xa _ (by simp), ?_⟩
  refine List.append_subset.mpr ⟨?_, ?_⟩
  · refine (warrs_buildCom ca na fa Lc K).trans ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  · refine (warrs_fillCom ca na fa ea xa ta Lc K Fl).trans ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp

end BlockSyntactic

/-! ## §10 The build and fill passes, discharged -/

section BlockSpec

variable {B N Lc K : ℕ} {colB : Fin N → Fin Lc → Bool}
  {ca na fa ea xa ta : String}

/-- A same-row later entry sits at a strictly larger strided index. -/
private theorem rowIdx_lt {len w v i' i : ℕ} (hv : w < v) (hi' : i' < len) :
    w * len + i' < v * len + i := by
  have h1 : (w + 1) * len ≤ v * len := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at h1
  omega

variable (h2LB : 2 ^ Lc * (K + 1) < B) (hNB : N < B) (hNLB : N * Lc < B)

include h2LB in
/-- **The wipe, discharged**: the region becomes the zero array;
nothing else moves. -/
private theorem zeroCom_spec {a : String} {n : ℕ} (hnB : n < B) :
    Spec B (fun σ => (σ.arrs a).length = n) (zeroCom a n)
      (fun σ σ' => σ'.arrs a = arrOf n (fun _ => 0) ∧
        (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) ∧ σ'.vars = σ.vars)
      (3 * n + 1) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  intro σ hlen
  set Inv : ℕ → Env → Prop := fun j τ =>
    (τ.arrs a).length = n ∧ (∀ i, i < j → (τ.arrs a).getD i 0 = 0) ∧
      (∀ b, b ≠ a → τ.arrs b = σ.arrs b) ∧ τ.vars = σ.vars with hInv
  have hstep : ∀ i, i < (List.range n).length →
      Spec B (Inv (0 + i)) (Com.store a (.lit (0 + i)) (.lit 0))
        (fun _ τ' => Inv (0 + i + 1) τ') 3 := by
    intro i hi
    rw [List.length_range] at hi
    simp only [Nat.zero_add]
    intro τ hτ
    obtain ⟨hl, hz, hb, hv⟩ := hτ
    refine ⟨τ.setArr a i 0,
      (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) (by omega)).mono
        (by simp), ?_, ?_, ?_, ?_⟩
    · simpa using hl
    · intro i' hi'
      rw [arrs_setArr, if_pos rfl, set_eq_arrOf_upd i 0 hl, getD_arrOf _ (by omega)]
      by_cases he : i' = i
      · subst he
        rw [upd_self]
      · rw [upd_of_ne _ he]
        exact hz i' (by omega)
    · intro b hb'
      rw [arrs_setArr, if_neg hb']
      exact hb b hb'
    · simpa using hv
  have hscan := seqIdx_spec (B := B) (Kb := 3)
    (gen := fun i _ => Com.store a (.lit i) (.lit 0)) Inv (List.range n) 0 hstep
  obtain ⟨τ, hrun, hτ⟩ :=
    hscan σ ⟨hlen, fun i hi => absurd hi (by omega), fun _ _ => rfl, rfl⟩
  simp only [List.length_range, Nat.zero_add] at hτ
  obtain ⟨hl, hz, hb, hv⟩ := hτ
  refine ⟨τ, hrun.mono (by rw [List.length_range]; omega), ?_, hb, hv⟩
  refine eq_of_getD (by rw [hl, length_arrOf]) ?_
  intro i hi
  rw [hl] at hi
  rw [getD_arrOf _ hi]
  exact hz i hi

include h2LB hNB hNLB in
/-- **The row-code computation, discharged**: `"bt.c"` ends holding
`rowCode` of the current vertex — the machine's `codeAux`, one bit
read per color, every partial code below `2^L` (`codeAux_lt`, the
stored-value citation for this scalar). -/
private theorem rowCodeCom_spec (v : Fin N) :
    Spec B (fun σ => RowBits ca colB σ ∧ σ.vars "bt.v" = (v : ℕ))
      (rowCodeCom ca Lc)
      (fun σ σ' => σ'.vars "bt.c" = rowCode colB v ∧ σ'.arrs = σ.arrs ∧
        (∀ y, y ≠ "bt.c" → σ'.vars y = σ.vars y))
      (11 * Lc + 3) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have h2L1 : 2 ^ Lc ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
  intro σ hσ
  obtain ⟨hrow, hv⟩ := hσ
  set σ₀ := σ.setVar "bt.c" 0 with hσ₀
  have hr₀ : Run B (.assign "bt.c" (.lit 0)) σ σ₀ 2 := run_assign_lit (by omega)
  set Inv : ℕ → Env → Prop := fun j τ =>
    τ.arrs = σ.arrs ∧ (∀ y, y ≠ "bt.c" → τ.vars y = σ.vars y) ∧
      τ.vars "bt.c" = codeAux (rowBit colB v) j with hInv
  have hstep : ∀ j, j < (List.range Lc).length →
      Spec B (Inv (0 + j))
        (Com.assign "bt.c" (.add (.var "bt.c")
          (.mul (.get ca (.add (.mul (.var "bt.v") (.lit Lc)) (.lit (0 + j))))
            (.lit (2 ^ (0 + j))))))
        (fun _ τ' => Inv (0 + j + 1) τ') 11 := by
    intro j hj
    rw [List.length_range] at hj
    simp only [Nat.zero_add]
    intro τ hτ
    obtain ⟨harr, hvars, hc⟩ := hτ
    have hvτ : τ.vars "bt.v" = (v : ℕ) := by
      rw [hvars _ (by decide)]
      exact hv
    have hNpos : 0 < N := v.pos
    have hLN : Lc ≤ N * Lc := Nat.le_mul_of_pos_left _ hNpos
    have hidx : (v : ℕ) * Lc + j < N * Lc := by
      have h1 : ((v : ℕ) + 1) * Lc ≤ N * Lc :=
        Nat.mul_le_mul_right _ (by have := v.is_lt; omega)
      rw [Nat.succ_mul] at h1
      omega
    have hvev : (Expr.var "bt.v").evalB B τ = some (v : ℕ) := by
      rw [← hvτ]
      exact evalB_var (by rw [hvτ]; exact lt_trans v.is_lt hNB)
    have hmul : (Expr.mul (.var "bt.v") (.lit Lc)).evalB B τ = some ((v : ℕ) * Lc) := by
      refine evalB_bin hvev (evalB_lit (by omega)) ?_
      show (v : ℕ) * Lc < B
      omega
    have haddi : (Expr.add (.mul (.var "bt.v") (.lit Lc)) (.lit j)).evalB B τ
        = some ((v : ℕ) * Lc + j) := by
      refine evalB_bin hmul (evalB_lit (by omega)) ?_
      show (v : ℕ) * Lc + j < B
      omega
    have hget : (Expr.get ca (.add (.mul (.var "bt.v") (.lit Lc)) (.lit j))).evalB B τ
        = some (if colB v ⟨j, hj⟩ then 1 else 0) := by
      refine evalB_get haddi ?_ (by split <;> omega)
      rw [getElem?_eq_getD (by rw [harr, hrow.1]; exact hidx), harr]
      exact congrArg some (hrow.2 v ⟨j, hj⟩)
    have hpow : (2 : ℕ) ^ j < B := by
      have h1 : (2 : ℕ) ^ j ≤ 2 ^ Lc := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hmul2 : (Expr.mul (.get ca (.add (.mul (.var "bt.v") (.lit Lc)) (.lit j)))
        (.lit (2 ^ j))).evalB B τ
        = some ((if colB v ⟨j, hj⟩ then 1 else 0) * 2 ^ j) := by
      refine evalB_bin hget (evalB_lit hpow) ?_
      show (if colB v ⟨j, hj⟩ then 1 else 0) * 2 ^ j < B
      split <;> omega
    -- the bit as `codeAux`'s summand
    have hbit : (if colB v ⟨j, hj⟩ then 1 else 0) * 2 ^ j
        = (if rowBit colB v j then 2 ^ j else 0) := by
      rw [rowBit_of_lt colB v hj]
      split <;> omega
    have hcode1 := codeAux_lt (rowBit colB v) (j + 1)
    have hcodeeq : codeAux (rowBit colB v) (j + 1)
        = codeAux (rowBit colB v) j + (if rowBit colB v j then 2 ^ j else 0) := rfl
    have hpow1 : (2 : ℕ) ^ (j + 1) ≤ 2 ^ Lc := Nat.pow_le_pow_right (by omega) (by omega)
    have hcB : τ.vars "bt.c" < B := by
      rw [hc]
      have := codeAux_lt (rowBit colB v) j
      have h1 : (2 : ℕ) ^ j ≤ 2 ^ Lc := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have haddall : (Expr.add (.var "bt.c")
        (.mul (.get ca (.add (.mul (.var "bt.v") (.lit Lc)) (.lit j)))
          (.lit (2 ^ j)))).evalB B τ
        = some (codeAux (rowBit colB v) j + (if colB v ⟨j, hj⟩ then 1 else 0) * 2 ^ j) := by
      have hcv : (Expr.var "bt.c").evalB B τ = some (codeAux (rowBit colB v) j) := by
        rw [← hc]
        exact evalB_var hcB
      refine evalB_bin hcv hmul2 ?_
      show codeAux (rowBit colB v) j + (if colB v ⟨j, hj⟩ then 1 else 0) * 2 ^ j < B
      rw [hbit, ← hcodeeq]
      omega
    refine ⟨τ.setVar "bt.c" _, (Run.assign haddall).mono (by simp), ?_, ?_, ?_⟩
    · simpa using harr
    · intro y hy
      rw [vars_setVar, if_neg hy]
      exact hvars y hy
    · rw [vars_setVar, if_pos rfl, hbit, ← hcodeeq]
  have hscan := seqIdx_spec (B := B) (Kb := 11)
    (gen := fun j _ => Com.assign "bt.c" (.add (.var "bt.c")
      (.mul (.get ca (.add (.mul (.var "bt.v") (.lit Lc)) (.lit j)))
        (.lit (2 ^ j)))))
    Inv (List.range Lc) 0 hstep
  have hInv0 : Inv 0 σ₀ := by
    refine ⟨by rw [hσ₀]; simp, fun y hy => by rw [hσ₀, vars_setVar, if_neg hy], ?_⟩
    rw [hσ₀, vars_setVar, if_pos rfl]
    rfl
  obtain ⟨τ, hrunS, hτ⟩ := hscan σ₀ hInv0
  simp only [List.length_range, Nat.zero_add] at hτ
  obtain ⟨harr, hvars, hcode⟩ := hτ
  exact ⟨τ, (hr₀.seq hrunS).mono (by rw [List.length_range]; omega),
    hcode, harr, hvars⟩

open Classical in
/-- The build loop's invariant: the count and seat regions hold
exactly the partial table of the scanned prefix. -/
def BuildInv (ca na fa : String) {N Lc : ℕ} (colB : Fin N → Fin Lc → Bool)
    (K : ℕ) (σ : Env) : Prop :=
  RowBits ca colB σ ∧ σ.vars "bt.n" = N ∧ σ.vars "bt.v" ≤ N ∧
    (σ.arrs na).length = 2 ^ Lc ∧ (σ.arrs fa).length = 2 ^ Lc * (K + 1) ∧
    ∀ ρ, ρ < 2 ^ Lc →
      (σ.arrs na).getD ρ 0 = (firstsUpto colB K (σ.vars "bt.v") ρ).length ∧
      ∀ s, (hs : s < (firstsUpto colB K (σ.vars "bt.v") ρ).length) →
        (σ.arrs fa).getD (ρ * (K + 1) + s) 0
          = ((firstsUpto colB K (σ.vars "bt.v") ρ)[s] : ℕ)

include h2LB hNB hNLB in
open Classical in
/-- **One vertex of the build pass, discharged**: the appended values
are the vertex's row code (`< 2^L`, `rowCode_lt`), the bumped count
(`≤ K+1`) and the vertex name (`< N`) — the stored-value classes this
pass owns. -/
private theorem buildBody_spec (hca_na : ca ≠ na) (hca_fa : ca ≠ fa)
    (hna_fa : na ≠ fa) :
    Spec B (fun σ => BuildInv ca na fa colB K σ ∧ σ.vars "bt.v" < N)
      (buildBody ca na fa Lc K)
      (fun σ σ' => BuildInv ca na fa colB K σ' ∧
        σ'.vars "bt.v" = σ.vars "bt.v" + 1)
      (11 * Lc + 26) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  have h2L1 : 2 ^ Lc ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rintro σ ⟨hInv, hvN⟩
  obtain ⟨hrow, hn, hvle, hnal, hfal, htab⟩ := hInv
  -- 1. the row code
  obtain ⟨σ₁, hr₁, hcval, harr₁, hvars₁⟩ :=
    (rowCodeCom_spec h2LB hNB hNLB (⟨σ.vars "bt.v", hvN⟩ : Fin N)) σ ⟨hrow, rfl⟩
  set v := σ.vars "bt.v" with hvdef
  set ρ₀ := rowCode colB (⟨v, hvN⟩ : Fin N) with hρ₀
  have hρ₀lt : ρ₀ < 2 ^ Lc := rowCode_lt colB _
  have hv₁ : σ₁.vars "bt.v" = v := hvars₁ _ (by decide)
  have hn₁ : σ₁.vars "bt.n" = N := by rw [hvars₁ _ (by decide)]; exact hn
  -- 2. the count read
  set cnt := (firstsUpto colB K v ρ₀).length with hcntdef
  have hcntle : cnt ≤ K + 1 := firstsUpto_length_le v ρ₀
  have hdev : (Expr.get na (.var "bt.c")).evalB B σ₁ = some cnt := by
    have hcv : (Expr.var "bt.c").evalB B σ₁ = some ρ₀ := by
      rw [← hcval]
      exact evalB_var (by rw [hcval]; omega)
    refine evalB_get hcv ?_ (by omega)
    rw [getElem?_eq_getD (by rw [harr₁, hnal]; exact hρ₀lt), harr₁]
    exact congrArg some (htab ρ₀ hρ₀lt).1
  set σ₂ := σ₁.setVar "bt.d" cnt with hσ₂
  have hr₂ : Run B (.assign "bt.d" (.get na (.var "bt.c"))) σ₁ σ₂ 3 := by
    rw [hσ₂]
    exact (Run.assign hdev).mono (by simp)
  have harr₂ : σ₂.arrs = σ.arrs := by
    rw [hσ₂]
    simpa using harr₁
  have hd₂ : σ₂.vars "bt.d" = cnt := by rw [hσ₂, vars_setVar, if_pos rfl]
  have hc₂ : σ₂.vars "bt.c" = ρ₀ := by
    rw [hσ₂, vars_setVar, if_neg (by decide)]
    exact hcval
  have hv₂ : σ₂.vars "bt.v" = v := by
    rw [hσ₂, vars_setVar, if_neg (by decide)]
    exact hv₁
  have hn₂ : σ₂.vars "bt.n" = N := by
    rw [hσ₂, vars_setVar, if_neg (by decide)]
    exact hn₁
  -- 3. the guarded append
  have hcond : (Cond.lt (.var "bt.d") (.lit (K + 1))).evalB B σ₂
      = some (decide (cnt < K + 1)) := by
    have h1 : (Expr.var "bt.d").evalB B σ₂ = some cnt := by
      rw [← hd₂]
      exact evalB_var (by rw [hd₂]; omega)
    exact evalB_condLt h1 (evalB_lit (by omega))
  by_cases hfree : cnt < K + 1
  · -- a free seat: append the vertex and bump the count
    have hcondT : (Cond.lt (.var "bt.d") (.lit (K + 1))).evalB B σ₂ = some true := by
      rw [hcond]
      congr 1
      simpa using hfree
    have hseat : ρ₀ * (K + 1) + cnt < 2 ^ Lc * (K + 1) := by
      have h1 : (ρ₀ + 1) * (K + 1) ≤ 2 ^ Lc * (K + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at h1
      omega
    have hidxev : (Expr.add (.mul (.var "bt.c") (.lit (K + 1))) (.var "bt.d")).evalB B σ₂
        = some (ρ₀ * (K + 1) + cnt) := by
      have h1 : (Expr.mul (.var "bt.c") (.lit (K + 1))).evalB B σ₂
          = some (ρ₀ * (K + 1)) := by
        have hcv : (Expr.var "bt.c").evalB B σ₂ = some ρ₀ := by
          rw [← hc₂]
          exact evalB_var (by rw [hc₂]; omega)
        refine evalB_bin hcv (evalB_lit (by omega)) ?_
        show ρ₀ * (K + 1) < B
        omega
      have h2 : (Expr.var "bt.d").evalB B σ₂ = some cnt := by
        rw [← hd₂]
        exact evalB_var (by rw [hd₂]; omega)
      refine evalB_bin h1 h2 ?_
      show ρ₀ * (K + 1) + cnt < B
      omega
    have hvev : (Expr.var "bt.v").evalB B σ₂ = some v := by
      rw [← hv₂]
      exact evalB_var (by rw [hv₂]; omega)
    set σ₃ := σ₂.setArr fa (ρ₀ * (K + 1) + cnt) v with hσ₃
    have hr₃ : Run B (.store fa (.add (.mul (.var "bt.c") (.lit (K + 1))) (.var "bt.d"))
        (.var "bt.v")) σ₂ σ₃ 7 := by
      rw [hσ₃]
      refine (Run.store hidxev hvev ?_).mono (by simp)
      rw [harr₂, hfal]
      exact hseat
    have hcv₃ : (Expr.var "bt.c").evalB B σ₃ = some ρ₀ := by
      have h3 : σ₃.vars "bt.c" = ρ₀ := by rw [hσ₃]; simpa using hc₂
      rw [← h3]
      exact evalB_var (by rw [h3]; omega)
    have hd₃ : σ₃.vars "bt.d" = cnt := by rw [hσ₃]; simpa using hd₂
    have hdev₃ : (Expr.add (.var "bt.d") (.lit 1)).evalB B σ₃ = some (cnt + 1) := by
      have h4 : (Expr.var "bt.d").evalB B σ₃ = some cnt := by
        rw [← hd₃]
        exact evalB_var (by rw [hd₃]; omega)
      refine evalB_bin h4 (evalB_lit (by omega)) ?_
      show cnt + 1 < B
      omega
    set σ₄ := σ₃.setArr na ρ₀ (cnt + 1) with hσ₄
    have hr₄ : Run B (.store na (.var "bt.c") (.add (.var "bt.d") (.lit 1))) σ₃ σ₄ 5 := by
      rw [hσ₄]
      refine (Run.store hcv₃ hdev₃ ?_).mono (by simp)
      rw [hσ₃, arrs_setArr, if_neg hna_fa, harr₂, hnal]
      exact hρ₀lt
    have hv₄ : σ₄.vars "bt.v" = v := by rw [hσ₄, hσ₃]; simpa using hv₂
    have hincr : (Expr.add (.var "bt.v") (.lit 1)).evalB B σ₄ = some (v + 1) := by
      have h5 : (Expr.var "bt.v").evalB B σ₄ = some v := by
        rw [← hv₄]
        exact evalB_var (by rw [hv₄]; omega)
      refine evalB_bin h5 (evalB_lit (by omega)) ?_
      show v + 1 < B
      omega
    set σ₅ := σ₄.setVar "bt.v" (v + 1) with hσ₅
    have hr₅ : Run B (.assign "bt.v" (.add (.var "bt.v") (.lit 1))) σ₄ σ₅ 4 := by
      rw [hσ₅]
      exact (Run.assign hincr).mono (by simp)
    have hrun : Run B (buildBody ca na fa Lc K) σ σ₅ (11 * Lc + 26) := by
      refine (hr₁.seq (hr₂.seq ((Run.ite_true hcondT (hr₃.seq hr₄)).seq hr₅))).mono ?_
      simp only [size_condLt, size_var, size_lit]
      omega
    -- the invariant at `v + 1`
    have hfa₅ : σ₅.arrs fa = (σ.arrs fa).set (ρ₀ * (K + 1) + cnt) v := by
      rw [hσ₅]
      simp only [arrs_setVar]
      rw [hσ₄, arrs_setArr, if_neg (Ne.symm hna_fa), hσ₃, arrs_setArr, if_pos rfl,
        harr₂]
    have hna₅ : σ₅.arrs na = (σ.arrs na).set ρ₀ (cnt + 1) := by
      rw [hσ₅]
      simp only [arrs_setVar]
      rw [hσ₄, arrs_setArr, if_pos rfl, hσ₃, arrs_setArr, if_neg hna_fa, harr₂]
    have hoth₅ : ∀ b, b ≠ na → b ≠ fa → σ₅.arrs b = σ.arrs b := by
      intro b h1 h2
      rw [hσ₅]
      simp only [arrs_setVar]
      rw [hσ₄, arrs_setArr, if_neg h1, hσ₃, arrs_setArr, if_neg h2, harr₂]
    have hv₅ : σ₅.vars "bt.v" = v + 1 := by rw [hσ₅, vars_setVar, if_pos rfl]
    have hn₅ : σ₅.vars "bt.n" = N := by
      rw [hσ₅, vars_setVar, if_neg (by decide), hσ₄, hσ₃]
      simpa using hn₂
    refine ⟨σ₅, hrun, ⟨?_, hn₅, by omega, ?_, ?_, ?_⟩, by rw [hv₅]⟩
    · exact rowBits_of_arrs_eq (hoth₅ ca hca_na hca_fa) hrow
    · rw [hna₅]
      simp only [List.length_set]
      exact hnal
    · rw [hfa₅]
      simp only [List.length_set]
      exact hfal
    · -- the table, per row code
      intro ρ hρ
      rw [hv₅]
      by_cases hρeq : ρ = ρ₀
      · subst hρeq
        have hstep := firstsUpto_succ_pos hvN (hρ₀.symm) (by rw [← hcntdef]; exact hfree)
        have hlen1 : (firstsUpto colB K (v + 1) ρ₀).length = cnt + 1 := by
          rw [hstep]
          simp [← hcntdef]
        constructor
        · rw [hna₅, set_eq_arrOf_upd ρ₀ (cnt + 1) hnal, getD_arrOf _ (by omega),
            upd_self, hlen1]
        · intro s hs
          rw [hlen1] at hs
          rw [hfa₅, set_eq_arrOf_upd _ v hfal, getD_arrOf _ (by
            have h1 : (ρ₀ + 1) * (K + 1) ≤ 2 ^ Lc * (K + 1) :=
              Nat.mul_le_mul_right _ (by omega)
            rw [Nat.succ_mul] at h1
            omega)]
          by_cases hscnt : s = cnt
          · subst hscnt
            rw [upd_self,
              firstsUpto_getElem_last hvN hρ₀.symm (by rw [← hcntdef]; exact hfree)
                hcntdef (by omega)]
          · rw [upd_of_ne _ (by
              intro hcon
              exact hscnt (seatIdx_inj (by omega) (by omega) hcon).2)]
            have hslt : s < cnt := by omega
            rw [firstsUpto_getElem_lt hvN hρ₀.symm (by rw [← hcntdef]; exact hfree)
              (by rw [← hcntdef]; exact hslt) (by omega)]
            exact (htab ρ₀ hρ).2 s (by rw [← hcntdef]; exact hslt)
      · have hstep := firstsUpto_succ_ne (colB := colB) (K := K) hvN
          (by rw [← hρ₀]; exact fun hc => hρeq hc.symm)
        rw [hstep]
        constructor
        · rw [hna₅, set_eq_arrOf_upd ρ₀ (cnt + 1) hnal, getD_arrOf _ (by omega),
            upd_of_ne _ hρeq]
          exact (htab ρ hρ).1
        · intro s hs
          have hsK : s < K + 1 := lt_of_lt_of_le hs (firstsUpto_length_le v ρ)
          rw [hfa₅, set_eq_arrOf_upd _ v hfal, getD_arrOf _ (by
            have h1 : (ρ + 1) * (K + 1) ≤ 2 ^ Lc * (K + 1) :=
              Nat.mul_le_mul_right _ (by omega)
            rw [Nat.succ_mul] at h1
            omega)]
          rw [upd_of_ne _ (by
            intro hcon
            exact hρeq (seatIdx_inj hsK (by omega) hcon).1)]
          exact (htab ρ hρ).2 s hs
  · -- the row is full: nothing to append
    have hcondF : (Cond.lt (.var "bt.d") (.lit (K + 1))).evalB B σ₂ = some false := by
      rw [hcond]
      congr 1
      simpa using hfree
    have hincr : (Expr.add (.var "bt.v") (.lit 1)).evalB B σ₂ = some (v + 1) := by
      have h5 : (Expr.var "bt.v").evalB B σ₂ = some v := by
        rw [← hv₂]
        exact evalB_var (by rw [hv₂]; omega)
      refine evalB_bin h5 (evalB_lit (by omega)) ?_
      show v + 1 < B
      omega
    set σ₅ := σ₂.setVar "bt.v" (v + 1) with hσ₅
    have hr₅ : Run B (.assign "bt.v" (.add (.var "bt.v") (.lit 1))) σ₂ σ₅ 4 := by
      rw [hσ₅]
      exact (Run.assign hincr).mono (by simp)
    have hrun : Run B (buildBody ca na fa Lc K) σ σ₅ (11 * Lc + 26) := by
      refine (hr₁.seq (hr₂.seq ((Run.ite_false hcondF Run.skip).seq hr₅))).mono ?_
      simp only [size_condLt, size_var, size_lit]
      omega
    have harr₅ : σ₅.arrs = σ.arrs := by
      rw [hσ₅]
      simpa using harr₂
    have hv₅ : σ₅.vars "bt.v" = v + 1 := by rw [hσ₅, vars_setVar, if_pos rfl]
    have hn₅ : σ₅.vars "bt.n" = N := by
      rw [hσ₅, vars_setVar, if_neg (by decide)]
      exact hn₂
    refine ⟨σ₅, hrun, ⟨rowBits_of_arrs_eq (by rw [harr₅]) hrow, hn₅, by omega,
      by rw [harr₅]; exact hnal, by rw [harr₅]; exact hfal, ?_⟩, by rw [hv₅]⟩
    intro ρ hρ
    rw [hv₅]
    by_cases hρeq : ρ = ρ₀
    · subst hρeq
      have hstep := firstsUpto_succ_full hvN (hρ₀.symm) (by rw [← hcntdef]; exact hfree)
      rw [hstep, harr₅]
      exact htab ρ₀ hρ₀lt
    · have hstep := firstsUpto_succ_ne (colB := colB) (K := K) hvN
        (by rw [← hρ₀]; exact fun hc => hρeq hc.symm)
      rw [hstep, harr₅]
      exact htab ρ hρ

include h2LB hNB hNLB in
open Classical in
/-- **The table build, discharged** (§6.4's one `O(N·L)` pass): from
the color rows and the two regions' lengths, the count and seat
regions end holding `firsts` verbatim — `FirstsSt`, the region
contract every evaluator read consumes (`mem_tableReps_iff` then gives
the `Impl.FirstRep` semantics for free, per `SolveBlocksBot`). -/
theorem buildCom_spec (hca_na : ca ≠ na) (hca_fa : ca ≠ fa) (hna_fa : na ≠ fa) :
    Spec B (fun σ => RowBits ca colB σ ∧ σ.vars "bt.n" = N ∧
        (σ.arrs na).length = 2 ^ Lc ∧ (σ.arrs fa).length = 2 ^ Lc * (K + 1))
      (buildCom ca na fa Lc K)
      (fun _ σ' => FirstsSt na fa colB K σ' ∧ RowBits ca colB σ' ∧
        σ'.vars "bt.n" = N)
      (buildK N Lc) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have h2L1 : 2 ^ Lc ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rintro σ ⟨hrow, hn, hnal, hfal⟩
  -- the count wipe
  obtain ⟨σz, hrz, hzarr, hzoth, hzvars⟩ :=
    (zeroCom_spec h2LB (a := na) (n := 2 ^ Lc) (by omega)) σ hnal
  -- the pass
  have hloop := Spec.forRangeZero (B := B) "bt.v" "bt.n"
    (BuildInv ca na fa colB K) N (11 * Lc + 26) hNB
    (fun τ hτ => hτ.2.2.1) (fun τ hτ => hτ.2.1)
    (buildBody_spec h2LB hNB hNLB hca_na hca_fa hna_fa)
  have hpre : BuildInv ca na fa colB K (σz.setVar "bt.v" 0) := by
    refine ⟨?_, ?_, by simp, ?_, ?_, ?_⟩
    · refine rowBits_of_arrs_eq ?_ hrow
      simp only [arrs_setVar]
      exact hzoth ca hca_na
    · simp only [vars_setVar, if_neg (by decide : ("bt.n" : String) ≠ "bt.v")]
      rw [hzvars]
      exact hn
    · simp only [arrs_setVar]
      rw [hzarr, length_arrOf]
    · simp only [arrs_setVar]
      rw [hzoth fa (Ne.symm hna_fa)]
      exact hfal
    · intro ρ hρ
      have hv0 : (σz.setVar "bt.v" 0).vars "bt.v" = 0 := by simp
      rw [hv0]
      constructor
      · simp only [arrs_setVar]
        rw [hzarr, getD_arrOf _ hρ, firstsUpto_zero]
        rfl
      · intro s hs
        rw [firstsUpto_zero] at hs
        simp at hs
  obtain ⟨σ', hrl, hI, hvN'⟩ := hloop.run hpre
  obtain ⟨hrow', hn', hvle', hnal', hfal', htab'⟩ := hI
  refine ⟨σ', (hrz.seq hrl).mono (by
    have h1 : (11 * Lc + 26 + 4) * N = (11 * Lc + 30) * N := by ring
    simp only [buildK]
    omega), ?_, hrow', hn'⟩
  refine ⟨hnal', hfal', ?_⟩
  intro ρ hρ
  have := htab' ρ hρ
  rwa [hvN', firstsUpto_eq_firsts (le_refl N) ρ] at this

open Classical in
/-- The fill loop's invariant: the scratch regions clean between
vertices, every scanned vertex's row of table bits written. -/
def FillInv (ca na fa ea xa ta : String) {N Lc : ℕ}
    (colB : Fin N → Fin Lc → Bool) (K : ℕ) (Fl : List (DistFO Lc 1))
    (σ : Env) : Prop :=
  RowBits ca colB σ ∧ FirstsSt na fa colB K σ ∧ σ.vars "bt.n" = N ∧
    σ.vars "bt.v" ≤ N ∧
    σ.arrs ea = arrOf (K + 1) (fun _ => 0) ∧
    σ.arrs xa = arrOf (K + 1) (fun _ => 0) ∧
    (σ.arrs ta).length = N * Fl.length ∧
    ∀ w : Fin N, (w : ℕ) < σ.vars "bt.v" → ∀ i, (hi : i < Fl.length) →
      (σ.arrs ta).getD ((w : ℕ) * Fl.length + i) 0
        = (if botEvalT colB K (fun _ => w) Fl[i] then 1 else 0)

include h2LB hNB hNLB in
open Classical in
/-- **One vertex's row of table entries, discharged**: the vertex into
the env scratch, one evaluator call and one bit write per schedule
formula, the scratch cleaned. The depth budget enters here: every
`β ∈ Fl` is evaluated at one env entry, so `qdepth β ≤ K` is exactly
`botEvalT`'s `1 + qdepth β ≤ K + 1`. -/
private theorem fillBody_spec {Fl : List (DistFO Lc 1)}
    (hca_ea : ca ≠ ea) (hca_xa : ca ≠ xa) (hna_ea : na ≠ ea) (hna_xa : na ≠ xa)
    (hfa_ea : fa ≠ ea) (hfa_xa : fa ≠ xa) (hea_xa : ea ≠ xa)
    (hta_ca : ta ≠ ca) (hta_na : ta ≠ na) (hta_fa : ta ≠ fa)
    (hta_ea : ta ≠ ea) (hta_xa : ta ≠ xa)
    (hq : ∀ β ∈ Fl, qdepth β ≤ K) (hTB : N * Fl.length < B) :
    Spec B (fun σ => FillInv ca na fa ea xa ta colB K Fl σ ∧ σ.vars "bt.v" < N)
      (fillBody ca na fa ea xa ta Lc K Fl)
      (fun σ σ' => FillInv ca na fa ea xa ta colB K Fl σ' ∧
        σ'.vars "bt.v" = σ.vars "bt.v" + 1)
      (Fl.length * (evalKMax Lc K Fl + 7) + 11) := by
  have h1B : 1 < B := one_lt_of_seats h2LB
  have hK1 : K + 1 ≤ 2 ^ Lc * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  rintro σ ⟨hInv, hvN⟩
  obtain ⟨hrow, hfst, hn, hvle, hea0, hxa0, htal, hold⟩ := hInv
  set v := σ.vars "bt.v" with hvdef
  set mv : Fin 1 → Fin N := fun _ => (⟨v, hvN⟩ : Fin N) with hmv
  have hNpos : 0 < N := by omega
  -- 1. the vertex into the env scratch (a vertex name, `< N`)
  have h0l : 0 < (σ.arrs ea).length := by rw [hea0, length_arrOf]; omega
  set σ₁ := σ.setArr ea 0 v with hσ₁
  have hr₁ : Run B (.store ea (.lit 0) (.var "bt.v")) σ σ₁ 3 := by
    rw [hσ₁, hvdef]
    exact (Run.store (evalB_lit (by omega)) (evalB_var (by omega)) h0l).mono (by simp)
  have henv₁ : σ₁.arrs ea = arrOf (K + 1) (envFun mv) := by
    rw [hσ₁, arrs_setArr, if_pos rfl, hea0, set_arrOf_eq_upd]
    refine arrOf_congr fun i hi => ?_
    rw [upd_apply]
    by_cases h0 : i = 0
    · subst h0
      rw [if_pos rfl, envFun_lt mv (by omega)]
    · rw [if_neg h0, envFun_ge mv (by omega)]
  -- 2. the row of entries
  set Inv₃ : ℕ → Env → Prop := fun j τ =>
    RowBits ca colB τ ∧ FirstsSt na fa colB K τ ∧
      τ.arrs ea = arrOf (K + 1) (envFun mv) ∧
      τ.arrs xa = arrOf (K + 1) (fun _ => 0) ∧
      τ.vars "bt.v" = v ∧ τ.vars "bt.n" = N ∧
      (τ.arrs ta).length = N * Fl.length ∧
      (∀ w : Fin N, (w : ℕ) < v → ∀ i, (hi : i < Fl.length) →
        (τ.arrs ta).getD ((w : ℕ) * Fl.length + i) 0
          = (if botEvalT colB K (fun _ => w) Fl[i] then 1 else 0)) ∧
      (∀ i, (hi : i < Fl.length) → i < j →
        (τ.arrs ta).getD (v * Fl.length + i) 0
          = (if botEvalT colB K mv Fl[i] then 1 else 0)) with hInv₃
  have hstep : ∀ i (hi : i < Fl.length),
      Spec B (Inv₃ (0 + i)) (entryGen ca na fa ea xa ta Lc K Fl.length (0 + i) Fl[i])
        (fun _ τ' => Inv₃ (0 + i + 1) τ') (evalKMax Lc K Fl + 7) := by
    intro i hi
    simp only [Nat.zero_add]
    rw [entryGen]
    intro τ hτ
    obtain ⟨hrowτ, hfstτ, henvτ, hxaτ, hvτ, hnτ, htalτ, holdτ, hrowv⟩ := hτ
    have hEv : EvalSt ca na fa ea xa colB K mv τ := by
      refine ⟨hrowτ, hfstτ, henvτ, by rw [hxaτ, length_arrOf], fun i' hi' => ?_⟩
      rw [hxaτ]
      by_cases h : i' < K + 1
      · rw [getD_arrOf _ h]
      · exact getD_ge_len (by rw [length_arrOf]; omega)
    have hd : 1 + qdepth Fl[i] ≤ K + 1 := by
      have := hq Fl[i] (List.getElem_mem hi)
      omega
    obtain ⟨τ', hr', hrb, hea', hxa', harr', hvar'⟩ :=
      (evalCom_spec h2LB hNB hNLB hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hea_xa
        Fl[i] mv hd) τ hEv
    -- the bit write (index below `N·|Fl|`, value a bit)
    have hFlB : Fl.length < B := by
      have : Fl.length ≤ N * Fl.length := Nat.le_mul_of_pos_left _ hNpos
      omega
    have hidxlt : v * Fl.length + i < N * Fl.length := by
      have h1 : (v + 1) * Fl.length ≤ N * Fl.length :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at h1
      omega
    have hvτ' : τ'.vars "bt.v" = v := by
      rw [hvar' _ (by decide)]
      exact hvτ
    have hidxev : (Expr.add (.mul (.var "bt.v") (.lit Fl.length)) (.lit i)).evalB B τ'
        = some (v * Fl.length + i) := by
      have h1 : (Expr.mul (.var "bt.v") (.lit Fl.length)).evalB B τ'
          = some (v * Fl.length) := by
        have hvv : (Expr.var "bt.v").evalB B τ' = some v := by
          rw [← hvτ']
          exact evalB_var (by rw [hvτ']; omega)
        refine evalB_bin hvv (evalB_lit (by omega)) ?_
        show v * Fl.length < B
        omega
      refine evalB_bin h1 (evalB_lit (by omega)) ?_
      show v * Fl.length + i < B
      omega
    have hrev : (Expr.var "bt.r").evalB B τ'
        = some (if botEvalT colB K mv Fl[i] then 1 else 0) := by
      rw [← hrb]
      exact evalB_var (by rw [hrb]; split <;> omega)
    have hta' : τ'.arrs ta = τ.arrs ta := harr' ta hta_ea hta_xa
    set τ'' := τ'.setArr ta (v * Fl.length + i)
      (if botEvalT colB K mv Fl[i] then 1 else 0) with hτ''
    have hrst : Run B (.store ta (.add (.mul (.var "bt.v") (.lit Fl.length)) (.lit i))
        (.var "bt.r")) τ' τ'' 7 := by
      rw [hτ'']
      refine (Run.store hidxev hrev ?_).mono (by simp)
      rw [hta', htalτ]
      exact hidxlt
    have hta'' : τ''.arrs ta = (τ.arrs ta).set (v * Fl.length + i)
        (if botEvalT colB K mv Fl[i] then 1 else 0) := by
      rw [hτ'', arrs_setArr, if_pos rfl, hta']
    have hoth'' : ∀ b, b ≠ ta → τ''.arrs b = τ'.arrs b := by
      intro b hb
      rw [hτ'', arrs_setArr, if_neg hb]
    refine ⟨τ'', (hr'.seq hrst).mono (by
      have := evalK_le_evalKMax (Lc := Lc) (K := K) (List.getElem_mem hi)
      omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine rowBits_of_arrs_eq ?_ hrowτ
      rw [hoth'' ca (Ne.symm hta_ca)]
      exact harr' ca hca_ea hca_xa
    · refine firstsSt_of_arrs_eq ?_ ?_ hfstτ
      · rw [hoth'' na (Ne.symm hta_na)]
        exact harr' na hna_ea hna_xa
      · rw [hoth'' fa (Ne.symm hta_fa)]
        exact harr' fa hfa_ea hfa_xa
    · rw [hoth'' ea (Ne.symm hta_ea), hea']
      exact henvτ
    · rw [hoth'' xa (Ne.symm hta_xa), hxa']
      exact hxaτ
    · rw [hτ'']
      simp only [vars_setArr]
      exact hvτ'
    · rw [hτ'']
      simp only [vars_setArr]
      rw [hvar' _ (by decide)]
      exact hnτ
    · rw [hta'']
      simp only [List.length_set]
      exact htalτ
    · -- the finished rows stand
      intro w hw i' hi'
      rw [hta'', set_eq_arrOf_upd _ _ htalτ, getD_arrOf _ (by
        have h1 : ((w : ℕ) + 1) * Fl.length ≤ N * Fl.length :=
          Nat.mul_le_mul_right _ (by have := w.is_lt; omega)
        rw [Nat.succ_mul] at h1
        omega)]
      rw [upd_of_ne _ (Nat.ne_of_lt (rowIdx_lt hw hi'))]
      exact holdτ w hw i' hi'
    · -- this row grows by one entry
      intro i' hi' hij
      rw [hta'', set_eq_arrOf_upd _ _ htalτ, getD_arrOf _ (by
        have h1 : (v + 1) * Fl.length ≤ N * Fl.length :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at h1
        omega)]
      by_cases hii : i' = i
      · subst hii
        rw [upd_self]
      · rw [upd_of_ne _ (by omega)]
        exact hrowv i' hi' (by omega)
  have hscan := seqIdx_spec (B := B) (Kb := evalKMax Lc K Fl + 7)
    (gen := entryGen ca na fa ea xa ta Lc K Fl.length) Inv₃ Fl 0 hstep
  have hInv₃0 : Inv₃ 0 σ₁ := by
    refine ⟨rowBits_of_arrs_eq (by rw [hσ₁, arrs_setArr, if_neg hca_ea]) hrow,
      firstsSt_of_arrs_eq (by rw [hσ₁, arrs_setArr, if_neg hna_ea])
        (by rw [hσ₁, arrs_setArr, if_neg hfa_ea]) hfst,
      henv₁,
      by rw [hσ₁, arrs_setArr, if_neg (Ne.symm hea_xa)]; exact hxa0,
      by rw [hσ₁]; simpa using hvdef.symm,
      by rw [hσ₁]; simpa using hn,
      by rw [hσ₁, arrs_setArr, if_neg hta_ea]; exact htal,
      ?_, fun i hi h0 => absurd h0 (by omega)⟩
    intro w hw i hi
    rw [hσ₁, arrs_setArr, if_neg hta_ea]
    exact hold w hw i hi
  obtain ⟨τf, hrf, hτf⟩ := hscan σ₁ hInv₃0
  simp only [Nat.zero_add] at hτf
  obtain ⟨hrowf, hfstf, henvf, hxaf, hvf, hnf, htalf, holdf, hrowvf⟩ := hτf
  -- 3. clean the env scratch, advance the vertex
  have h0lf : 0 < (τf.arrs ea).length := by rw [henvf, length_arrOf]; omega
  set τg := τf.setArr ea 0 0 with hτg
  have hrg : Run B (.store ea (.lit 0) (.lit 0)) τf τg 3 := by
    rw [hτg]
    exact (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) h0lf).mono (by simp)
  have hvg : τg.vars "bt.v" = v := by rw [hτg]; simpa using hvf
  have hincr : (Expr.add (.var "bt.v") (.lit 1)).evalB B τg = some (v + 1) := by
    have h5 : (Expr.var "bt.v").evalB B τg = some v := by
      rw [← hvg]
      exact evalB_var (by rw [hvg]; omega)
    refine evalB_bin h5 (evalB_lit (by omega)) ?_
    show v + 1 < B
    omega
  set τh := τg.setVar "bt.v" (v + 1) with hτh
  have hrh : Run B (.assign "bt.v" (.add (.var "bt.v") (.lit 1))) τg τh 4 := by
    rw [hτh]
    exact (Run.assign hincr).mono (by simp)
  have hrun : Run B (fillBody ca na fa ea xa ta Lc K Fl) σ τh
      (Fl.length * (evalKMax Lc K Fl + 7) + 11) := by
    refine (hr₁.seq (hrf.seq (hrg.seq hrh))).mono ?_
    omega
  have hoth_h : ∀ b, b ≠ ea → τh.arrs b = τf.arrs b := by
    intro b hb
    rw [hτh]
    simp only [arrs_setVar]
    rw [hτg, arrs_setArr, if_neg hb]
  have hea_h : τh.arrs ea = arrOf (K + 1) (fun _ => 0) := by
    rw [hτh]
    simp only [arrs_setVar]
    rw [hτg, arrs_setArr, if_pos rfl, henvf, set_arrOf_eq_upd]
    refine arrOf_congr fun i hi => ?_
    rw [upd_apply]
    by_cases h0 : i = 0
    · subst h0
      rw [if_pos rfl]
    · rw [if_neg h0, envFun_ge mv (by omega)]
  have hvh : τh.vars "bt.v" = v + 1 := by rw [hτh, vars_setVar, if_pos rfl]
  refine ⟨τh, hrun, ⟨?_, ?_, ?_, ?_, hea_h, ?_, ?_, ?_⟩, by rw [hvh]⟩
  · exact rowBits_of_arrs_eq (hoth_h ca hca_ea) hrowf
  · exact firstsSt_of_arrs_eq (hoth_h na hna_ea) (hoth_h fa hfa_ea) hfstf
  · rw [hτh, vars_setVar, if_neg (by decide), hτg]
    simpa using hnf
  · rw [hvh]
    omega
  · rw [hoth_h xa (Ne.symm hea_xa)]
    exact hxaf
  · rw [hoth_h ta hta_ea]
    exact htalf
  · -- every scanned row, the fresh one included
    intro w hw i hi
    rw [hvh] at hw
    rw [hoth_h ta hta_ea]
    rcases Nat.lt_or_ge (w : ℕ) v with hwv | hwv
    · exact holdf w hwv i hi
    · have hweq : w = (⟨v, hvN⟩ : Fin N) := Fin.ext (by omega)
      subst hweq
      exact hrowvf i hi hi

include h2LB hNB hNLB in
open Classical in
/-- **The fill loop, discharged**: from the built table and clean
scratch, every `(v, β ∈ Fl)` table bit is written — `botEvalT`'s
value, at a schedule constant per entry. -/
theorem fillCom_spec {Fl : List (DistFO Lc 1)}
    (hca_ea : ca ≠ ea) (hca_xa : ca ≠ xa) (hna_ea : na ≠ ea) (hna_xa : na ≠ xa)
    (hfa_ea : fa ≠ ea) (hfa_xa : fa ≠ xa) (hea_xa : ea ≠ xa)
    (hta_ca : ta ≠ ca) (hta_na : ta ≠ na) (hta_fa : ta ≠ fa)
    (hta_ea : ta ≠ ea) (hta_xa : ta ≠ xa)
    (hq : ∀ β ∈ Fl, qdepth β ≤ K) (hTB : N * Fl.length < B) :
    Spec B (fun σ => RowBits ca colB σ ∧ FirstsSt na fa colB K σ ∧
        σ.vars "bt.n" = N ∧ σ.arrs ea = arrOf (K + 1) (fun _ => 0) ∧
        σ.arrs xa = arrOf (K + 1) (fun _ => 0) ∧
        (σ.arrs ta).length = N * Fl.length)
      (fillCom ca na fa ea xa ta Lc K Fl)
      (fun _ σ' => (σ'.arrs ta).length = N * Fl.length ∧
        ∀ (w : Fin N) i, (hi : i < Fl.length) →
          (σ'.arrs ta).getD ((w : ℕ) * Fl.length + i) 0
            = (if botEvalT colB K (fun _ => w) Fl[i] then 1 else 0))
      (fillK N Lc K Fl) := by
  have hloop := Spec.forRangeZero (B := B) "bt.v" "bt.n"
    (FillInv ca na fa ea xa ta colB K Fl) N
    (Fl.length * (evalKMax Lc K Fl + 7) + 11) hNB
    (fun τ hτ => hτ.2.2.2.1) (fun τ hτ => hτ.2.2.1)
    (fillBody_spec h2LB hNB hNLB hca_ea hca_xa hna_ea hna_xa hfa_ea hfa_xa hea_xa
      hta_ca hta_na hta_fa hta_ea hta_xa hq hTB)
  rintro σ ⟨hrow, hfst, hn, hea0, hxa0, htal⟩
  have hpre : FillInv ca na fa ea xa ta colB K Fl (σ.setVar "bt.v" 0) := by
    refine ⟨rowBits_of_arrs_eq (by simp) hrow,
      firstsSt_of_arrs_eq (by simp) (by simp) hfst,
      by simp only [vars_setVar, if_neg (by decide : ("bt.n" : String) ≠ "bt.v")]; exact hn,
      by simp, by simpa using hea0, by simpa using hxa0, by simpa using htal, ?_⟩
    intro w hw i hi
    have hw0 : (w : ℕ) < 0 := by simp at hw; exact hw
    exact absurd hw0 (by omega)
  obtain ⟨σ', hrl, hI, hvN'⟩ := hloop.run hpre
  obtain ⟨-, -, -, -, -, -, htal', htab'⟩ := hI
  refine ⟨σ', hrl.mono (by
    have h1 : (Fl.length * (evalKMax Lc K Fl + 7) + 11 + 4) * N
        = (Fl.length * (evalKMax Lc K Fl + 7) + 15) * N := by ring
    simp only [fillK]
    omega), htal', ?_⟩
  intro w i hi
  refine htab' w ?_ i hi
  rw [hvN']
  exact w.is_lt

end BlockSpec

end Lax3Proofs.Prog
