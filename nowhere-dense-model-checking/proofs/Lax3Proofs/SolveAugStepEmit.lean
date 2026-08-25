import Lax3Proofs.SolveAugEmitCom

/-!
# F6c12-5c-iv — `StepEmitIn`, the augmentation round's emit, as IMP+ text

The last of `SolveAugEmit`'s two residuals (its Finding 4).  **All the
mathematics is `SolveAugEmit`'s** — `emRow_eq_greedyStep` is the row
equality and `trInCsr_emit` turns any family listing each `emRow D rk v`
once into `TrInCsr o' t' (greedyStep rk D)`, all ten clauses — and **the
transpose is `SolveAugEmitCom`'s** (`transposeIn_tpCom` at
`tpK n a = 41·n + 40·a + 30`).  What is added here is loop text and the
read-back kit it needs.

## What `emCom` is

`tpCom` (the transpose), then one outer scan over the heads.  Head `v`
anchors the output offset (`o'[v] := p`), loads `v + 1` and `rk v` into
scalars, and runs **four row scans with one uniform body**

    read u ; ⟨cnd⟩ ; if c = 1 then { t'[p] := u ; p++ } ; A[u] := v+1 ; j++

differing only in the row scanned, the array `A` stamped, and the
condition block:

1. **the input row**, `A = ad`, `cnd` constantly `1` — this fuses the
   adjacency stamping with the old-arc copy, so the old arcs cost one
   pass and not two;
2. **the transpose row**, `A = ad`, `cnd` constantly `0` — the second
   half of `adjSet D v = D.inN v ∪ outNbrs D v` (`mem_adjSet`), stamped
   and not emitted;
3. **the fraternal row**, `A = sd`, `cnd` the test
   `ad[u] < v+1 ∧ sg[u] < sg[v]` — `EmFratPick`;
4. **the transitive row**, `A = dg`, `cnd` the test
   `sd[u] < v+1 ∧ ad[u] < v+1 ∧ (sg[u] < sg[v] ∨ mk[u·n+v] < 1)` —
   `EmTransPick`, whose last disjunct is the forced transitive direction
   and is the one `O(1)` matrix read (`transCsrAt_decides`).

The fourth scan stamps into `dg`, the counting sort's dead degree
region, and nothing ever reads what it writes.  That is not waste but
the point: `cnd`'s reads (`ad`, `sd`) stay disjoint from the loop's own
write, so the uniform body needs no case split on whether the stamp it
sets is the stamp it tested.

**Row stamps, and no clearing sweep.**  Head `v` stamps `v + 1` and the
carried invariant is that every cell is `≤ v` on entry; so `ad[u] = v+1`
is "stamped this round" with no per-head wipe, which would have been
`n²` over the pass and would have broken `emK`'s `300·n` term.  The
precondition's zeroed `ad`, `sd` is the base case, and `dg` needs
neither (nothing reads it).

## The read-back kit

`CsrPrefix` (`SolveGlueLoad.lean:65`) states the fraternity CSR at
`winA`, a *truncation* of the allocation, and hides its two index
functions inside `GraphCsr`'s existential.  `csrRows_of_csrPrefix`
unwraps both at once into `CsrRows`, the `TrInCsr`-shaped record the
scans actually read — offsets and targets by `getElem?` on the
allocation itself, rows duplicate-free, row membership an iff with
`Adj`.  That is the ~60 lines the leaf was minted owing; `fo ≠ ft` is
the one hypothesis it needs, and it needs it because `winA` cuts two
different windows out of the two names.

## The budget

`emCom` costs `107·n + 94·a + 39·f + 53·T + 43` at
`a = arcCount D`, `f = fratPairCount D`, `T = transPairCount D`
(`emComK`), of which the transpose is `41·n + 40·a + 30`.  So it fits
`SolveAugEmit`'s pinned `emK n a f T = 300·n + 300·a + 200·f + 240·T +
80` with room in every term (`emComK_le_emK`), and `StepEmitIn` is
discharged **at `emK` itself**.  Term by term the emit loop spends `66`
a vertex (the head's eight row-bound loads, the offset anchor, the two
scalars and the four scan tails), `27` a slot of the input row and `27`
of the transpose row, `39` a fraternal candidate and `53` a transitive
one — the last two being the two conditional blocks, `14` and `28`
against a uniform `21` of body.

## Findings

1. **The output pointer needs no separate bound.**  `emNs_le` prices
   the output inside `arcCount D + fratPairCount D + transPairCount D`,
   which is exactly the `t'` allocation the contract asks for; the loop
   carries the write pointer as `emOff E v + |what row v has emitted|`
   and a store's range obligation is then `emOff` monotonicity, not a
   separate counting argument.
2. **`CsrPrefix` needs `fo ≠ ft` and nothing else.**  Two distinct
   windows on one name would make `winA`'s truncation ambiguous;
   `GraphCsr`'s clauses are otherwise stated at the index functions and
   transport to the allocation by `List.getElem?_take_of_lt`.
3. **The stamp test is `<`, not `≠`.**  IMP+ has no disequality
   (`Imp.lean:150`), and the invariant "every cell `≤ v`" makes
   `ad[u] < v+1` and `ad[u] ≠ v+1` the same test — so the sharper
   invariant is what buys the missing primitive, not a second array.
4. **The matrix index needs no `sq_lt_mcB`.**  `n·n < B` is already a
   clause of `StepEmitIn`'s own precondition
   (`SolveAugEmit.lean:860`), and `u·n + v < n·n` at `u, v < n` is two
   lines; `sq_lt_mcB` (`SolveSweepBuild.lean:1926`) is the *different*
   statement `n·n < mcB q x`, which belongs to the composition layer
   that instantiates `B`, not to a pass stated at an abstract `B`.
5. **`nf ≤ fratPairCount D` is load-bearing exactly where
   `SolveAugEmit`'s Finding 5 said it would be** — in the cost, and
   nowhere else.  `CsrRows` gives the fraternal rows their contents and
   `fof n = nf` their total length; without the clause the `39·f` term
   would price an unbounded region.  The transitive side needs no
   counterpart: `transCsrAt_slots_le` is unconditional.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (getD_eq_getElem)
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine
open Lax3Proofs.TgtCoupling

variable {n : ℕ}

/-! ## §1 The read-back kit: a CSR of a graph, at the allocation

`CsrPrefix` is `GraphCsr` at `winA`, a truncation, with its two index
functions existentially quantified.  A scan reads the *allocation*, so
what it needs is the same ten clauses stated there.  `CsrRows` is that
record — `TrInCsr`'s shape at a `SimpleGraph` — and
`csrRows_of_csrPrefix` is the unwrapping. -/

/-- **A graph in compressed-row form, read at the allocation**:
`TrInCsr`'s shape at a `SimpleGraph`.  The two regions may be longer
than their extents, the offsets are anchored and nondecreasing, rows are
duplicate-free and row `v` lists exactly the neighbours of `v`. -/
structure CsrRows (o t : String) {n : ℕ} (G : SimpleGraph (Fin n)) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The offsets are anchored. -/
  zero : off 0 = 0
  /-- The offsets do not decrease. -/
  mono : ∀ i, i < n → off i ≤ off (i + 1)
  /-- The extent. -/
  last : off n = ns
  /-- The offset region holds at least `n + 1` cells. -/
  offLen : n + 1 ≤ (σ.arrs o).length
  /-- The target region holds at least `ns` cells. -/
  tgtLen : ns ≤ (σ.arrs t).length
  /-- Reading an offset. -/
  offGet : ∀ i, i ≤ n → (σ.arrs o)[i]? = some (off i)
  /-- Reading a target. -/
  tgtGet : ∀ p, p < ns → (σ.arrs t)[p]? = some (tgt p)
  /-- Every target is a vertex. -/
  tgtLt : ∀ p, p < ns → tgt p < n
  /-- Rows are duplicate-free. -/
  nodup : ∀ v : Fin n, (Csr.row off tgt (v : ℕ)).Nodup
  /-- Row `v` lists exactly the neighbours of `v`. -/
  mem : ∀ (v : Fin n) (u : ℕ),
    u ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hu : u < n, G.Adj v ⟨u, hu⟩

theorem CsrRows.of_eq {o t : String} {n ns : ℕ} {G : SimpleGraph (Fin n)}
    {off tgt : ℕ → ℕ} {σ : Env} (h : CsrRows o t G ns off tgt σ) {σ' : Env}
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t) :
    CsrRows o t G ns off tgt σ' :=
  { h with
    offLen := by rw [ho]; exact h.offLen
    tgtLen := by rw [ht]; exact h.tgtLen
    offGet := by rw [ho]; exact h.offGet
    tgtGet := by rw [ht]; exact h.tgtGet }

/-- Every offset is inside the extent. -/
theorem CsrRows.off_le_ns {o t : String} {n ns : ℕ} {G : SimpleGraph (Fin n)}
    {off tgt : ℕ → ℕ} {σ : Env} (h : CsrRows o t G ns off tgt σ) :
    ∀ i, i ≤ n → off i ≤ ns := by
  have hmono : ∀ b, b ≤ n → ∀ a, a ≤ b → off a ≤ off b := by
    intro b
    induction b with
    | zero => intro _ a ha; obtain rfl : a = 0 := Nat.le_zero.1 ha; exact le_rfl
    | succ b ih =>
        intro hb a ha
        rcases Nat.lt_or_ge a (b + 1) with hlt | hge
        · exact le_trans (ih (by omega) a (by omega)) (h.mono b (by omega))
        · obtain rfl : a = b + 1 := by omega
          exact le_rfl
  intro i hi
  have := hmono n le_rfl i hi
  rw [h.last] at this
  exact this

private theorem getElem?_arrOf {m i : ℕ} (f : ℕ → ℕ) (h : i < m) :
    (arrOf m f)[i]? = some (f i) := by
  rw [arrOf, List.getElem?_map, List.getElem?_range h]
  rfl

/-- **The fraternity CSR, unwrapped.**  `CsrPrefix` states `GraphCsr` at
the truncation `winA` and hides the index functions; a scan reads the
allocation, so both go.  The hypothesis `fo ≠ ft` is what makes the two
windows unambiguous (Finding 2). -/
theorem csrRows_of_csrPrefix {fo ft : String} {n : ℕ} {G : SimpleGraph (Fin n)}
    {nf : ℕ} {σ : Env} (h : CsrPrefix fo ft G nf σ) (hne : fo ≠ ft) :
    ∃ fof ftf : ℕ → ℕ, CsrRows fo ft G nf fof ftf σ := by
  obtain ⟨hoL, htL, off, tgt, hc, h0, hnd, hadj⟩ := h
  refine ⟨off, tgt, ?_⟩
  set ws : String → Option ℕ :=
    fun b => if b = fo then some (n + 1) else if b = ft then some nf else none with hws
  have hwo : ws fo = some (n + 1) := by rw [hws]; simp
  have hwt : ws ft = some nf := by rw [hws]; simp [Ne.symm hne]
  have hoA : (σ.arrs fo).take (n + 1) = arrOf (n + 1) off := by
    rw [← arrs_winA_some hwo σ]; exact hc.offArr
  have htA : (σ.arrs ft).take nf = arrOf nf tgt := by
    rw [← arrs_winA_some hwt σ]; exact hc.tgtArr
  refine
    { zero := h0
      mono := fun i hi => hc.off_le_succ hi
      last := hc.last
      offLen := hoL
      tgtLen := htL
      offGet := ?_
      tgtGet := ?_
      tgtLt := fun p hp => hc.target hp
      nodup := hnd
      mem := hadj }
  · intro i hi
    rw [← List.getElem?_take_of_lt (l := σ.arrs fo) (show i < n + 1 by omega), hoA]
    exact getElem?_arrOf off (by omega)
  · intro p hp
    rw [← List.getElem?_take_of_lt (l := σ.arrs ft) hp, htA]
    exact getElem?_arrOf tgt hp

/-! ## §2 Row prefixes

A scan reads row `v` slot by slot, so what it has seen after the flat
pointer `j` is the prefix of `Csr.row` cut at `j`.  Two facts: the
prefix grows by one entry a turn, and at the row's end it is the whole
row. -/

/-- The part of row `v` below the flat slot pointer `j`. -/
def rowPre (off tgt : ℕ → ℕ) (v j : ℕ) : List ℕ :=
  arrOf (j - off v) (fun k => tgt (off v + k))

theorem rowPre_start (off tgt : ℕ → ℕ) (v : ℕ) : rowPre off tgt v (off v) = [] := by
  simp [rowPre, arrOf]

theorem rowPre_succ (off tgt : ℕ → ℕ) {v j : ℕ} (hj : off v ≤ j) :
    rowPre off tgt v (j + 1) = rowPre off tgt v j ++ [tgt j] := by
  rw [rowPre, rowPre, show j + 1 - off v = (j - off v) + 1 by omega, arrOf, arrOf,
    List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [show off v + (j - off v) = j by omega]

theorem rowPre_end (off tgt : ℕ → ℕ) (v : ℕ) :
    rowPre off tgt v (off (v + 1)) = Csr.row off tgt v := by
  rw [rowPre, Csr.row, Csr.rowLen]

/-- A row prefix is a prefix of the row. -/
theorem rowPre_prefix (off tgt : ℕ → ℕ) {v j : ℕ} (hj : j ≤ off (v + 1)) :
    rowPre off tgt v j <+: Csr.row off tgt v := by
  rw [← rowPre_end off tgt v, rowPre, rowPre, arrOf, arrOf,
    show off (v + 1) - off v
      = (j - off v) + ((off (v + 1) - off v) - (j - off v)) by omega,
    List.range_add, List.map_append]
  exact ⟨_, rfl⟩

/-- Filtering respects prefixes: what the scan has kept so far is a
prefix of what the whole row keeps. -/
theorem filter_prefix_filter {l m : List ℕ} (h : l <+: m) (p : ℕ → Bool) :
    l.filter p <+: m.filter p := by
  obtain ⟨r, rfl⟩ := h
  rw [List.filter_append]
  exact ⟨r.filter p, rfl⟩

/-! ## §3 The four rows the pass reads, and the one it writes

Each of the four scans reads a row of one CSR; what §4's loops need of
each is the same pair of facts — the row is duplicate-free and its
membership is the intended relation.  They are read off the `inj` and
`sound`/`complete` clauses of the four landed records. -/

private theorem row_nodup_of_inj {off tgt : ℕ → ℕ} {v : ℕ}
    (h : ∀ p r, off v ≤ p → p < off (v + 1) → off v ≤ r → r < off (v + 1) →
      tgt p = tgt r → p = r) : (Csr.row off tgt v).Nodup := by
  rw [Csr.row, arrOf]
  refine List.Nodup.map_on ?_ (List.nodup_range)
  intro a ha b hb hab
  simp only [List.mem_range, Csr.rowLen] at ha hb
  have := h (off v + a) (off v + b) (by omega) (by omega) (by omega) (by omega) hab
  omega

theorem TrInCsr.row_nodup {o t : String} {ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ}
    {σ : Env} (h : TrInCsr o t D ns off tgt σ) (v : Fin n) :
    (Csr.row off tgt (v : ℕ)).Nodup :=
  row_nodup_of_inj (fun p r => h.inj v p r)

theorem TrInCsr.row_mem {o t : String} {ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ}
    {σ : Env} (h : TrInCsr o t D ns off tgt σ) (v : Fin n) (u : ℕ) :
    u ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN v := by
  rw [mem_row_iff]
  constructor
  · rintro ⟨p, hp1, hp2, rfl⟩
    have hlt : tgt p < n := h.tgtLt p (h.row_lt_ns (v := v) hp2)
    exact ⟨hlt, h.sound v p hp1 hp2 hlt⟩
  · rintro ⟨hu, hmem⟩
    obtain ⟨p, hp1, hp2, hp3⟩ := h.complete v ⟨u, hu⟩ hmem
    exact ⟨p, hp1, hp2, hp3⟩

theorem OutCsrAt.row_nodup {qo qt : String} {D : Orientation n} {otF : ℕ → ℕ}
    {σ : Env} (h : OutCsrAt qo qt D otF σ) (v : Fin n) :
    (Csr.row (outOff D) otF (v : ℕ)).Nodup :=
  row_nodup_of_inj (fun p r => h.inj v p r)

theorem OutCsrAt.row_mem {qo qt : String} {D : Orientation n} {otF : ℕ → ℕ}
    {σ : Env} (h : OutCsrAt qo qt D otF σ) (v : Fin n) (u : ℕ) :
    u ∈ Csr.row (outOff D) otF (v : ℕ) ↔ ∃ hu : u < n, (v : Fin n) ∈ D.inN ⟨u, hu⟩ := by
  rw [mem_row_iff]
  constructor
  · rintro ⟨p, hp1, hp2, rfl⟩
    have hb : p < arcCount D := by
      have := outOff_le_arcCount D (k := (v : ℕ) + 1) v.isLt
      omega
    have hlt : otF p < n := h.qtLt p hb
    exact ⟨hlt, mem_outNbrs.1 (h.sound v p hp1 hp2 hlt)⟩
  · rintro ⟨hu, hmem⟩
    obtain ⟨p, hp1, hp2, hp3⟩ := h.complete v ⟨u, hu⟩ (mem_outNbrs.2 hmem)
    exact ⟨p, hp1, hp2, hp3⟩

theorem TransCsrAt.row_nodup {ro rt mk : String} {D : Orientation n} {ttF : ℕ → ℕ}
    {σ : Env} (h : TransCsrAt ro rt mk D ttF σ) (v : Fin n) :
    (Csr.row (trOff D) ttF (v : ℕ)).Nodup :=
  row_nodup_of_inj (fun p r => h.inj v p r)

theorem TransCsrAt.row_mem {ro rt mk : String} {D : Orientation n} {ttF : ℕ → ℕ}
    {σ : Env} (h : TransCsrAt ro rt mk D ttF σ) (v : Fin n) (u : ℕ) :
    u ∈ Csr.row (trOff D) ttF (v : ℕ) ↔ ∃ hu : u < n, TransLink D ⟨u, hu⟩ v := by
  rw [mem_row_iff]
  constructor
  · rintro ⟨p, hp1, hp2, rfl⟩
    have hb : p < trOff D n := lt_of_lt_of_le hp2 (trOff_mono D v.isLt)
    have hlt : ttF p < n := h.ttLt p hb
    exact ⟨hlt, h.sound v p hp1 hp2 hlt⟩
  · rintro ⟨hu, hmem⟩
    obtain ⟨p, hp1, hp2, hp3⟩ := h.complete v ⟨u, hu⟩ hmem
    exact ⟨p, hp1, hp2, hp3⟩

/-! ### The two filters, and the emitted row

`emKeepF` and `emKeepT` are `EmFratPick` and `EmTransPick` as Boolean
tests on a plain index — the shape `List.filter` takes and the shape the
condition blocks of §4 compute.  `emE` is the row the pass writes: the
old arcs, then the two filtered candidate rows, in exactly the order
the four scans run. -/

open Classical in
/-- **The fraternal phase's test**, on a plain index: `EmFratPick`. -/
noncomputable def emKeepF (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) (u : ℕ) : Bool :=
  decide (∃ hu : u < n, ¬ D.Adjacent ⟨u, hu⟩ v ∧ rk ⟨u, hu⟩ < rk v)

open Classical in
/-- **The transitive phase's test**, on a plain index: `EmTransPick`
minus the `TransLink` the row itself already carries. -/
noncomputable def emKeepT (D : Orientation n) (rk : Fin n → ℕ) (v : Fin n) (u : ℕ) : Bool :=
  decide (∃ hu : u < n, ¬ (fratGraph D).Adj ⟨u, hu⟩ v ∧ ¬ D.Adjacent ⟨u, hu⟩ v ∧
    (rk ⟨u, hu⟩ < rk v ∨ ¬ TransLink D v ⟨u, hu⟩))

open Classical in
theorem emKeepF_iff {D : Orientation n} {rk : Fin n → ℕ} {v : Fin n} {u : ℕ} (hu : u < n) :
    emKeepF D rk v u = true ↔ (¬ D.Adjacent ⟨u, hu⟩ v ∧ rk ⟨u, hu⟩ < rk v) := by
  rw [emKeepF, decide_eq_true_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

open Classical in
theorem emKeepT_iff {D : Orientation n} {rk : Fin n → ℕ} {v : Fin n} {u : ℕ} (hu : u < n) :
    emKeepT D rk v u = true ↔
      (¬ (fratGraph D).Adj ⟨u, hu⟩ v ∧ ¬ D.Adjacent ⟨u, hu⟩ v ∧
        (rk ⟨u, hu⟩ < rk v ∨ ¬ TransLink D v ⟨u, hu⟩)) := by
  rw [emKeepT, decide_eq_true_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

open Classical in
theorem emKeepF_of_ge {D : Orientation n} {rk : Fin n → ℕ} {v : Fin n} {u : ℕ}
    (hu : ¬ u < n) : emKeepF D rk v u = false := by
  rw [emKeepF, decide_eq_false_iff_not]
  rintro ⟨h, -⟩; exact hu h

open Classical in
theorem emKeepT_of_ge {D : Orientation n} {rk : Fin n → ℕ} {v : Fin n} {u : ℕ}
    (hu : ¬ u < n) : emKeepT D rk v u = false := by
  rw [emKeepT, decide_eq_false_iff_not]
  rintro ⟨h, -⟩; exact hu h

open Classical in
/-- **Row `v` of the output**, as a list: the old arcs, the fraternal
picks, the transitive picks — the order the four scans emit in. -/
noncomputable def emE (D : Orientation n) (rk : Fin n → ℕ)
    (off tgt fof ftf ttF : ℕ → ℕ) (k : ℕ) : List ℕ :=
  if hk : k < n then
    Csr.row off tgt k ++ (Csr.row fof ftf k).filter (emKeepF D rk ⟨k, hk⟩)
      ++ (Csr.row (trOff D) ttF k).filter (emKeepT D rk ⟨k, hk⟩)
  else []

theorem emE_lt {D : Orientation n} {rk : Fin n → ℕ} {off tgt fof ftf ttF : ℕ → ℕ}
    {k : ℕ} (hk : k < n) :
    emE D rk off tgt fof ftf ttF k
      = Csr.row off tgt k ++ (Csr.row fof ftf k).filter (emKeepF D rk ⟨k, hk⟩)
        ++ (Csr.row (trOff D) ttF k).filter (emKeepT D rk ⟨k, hk⟩) :=
  dif_pos hk

/-- **Row `v` of the output lists exactly `emRow D rk v`** — the finset
`SolveAugEmit`'s `emRow_eq_greedyStep` identifies with
`(greedyStep rk D).inN v`. -/
theorem mem_emE {D : Orientation n} {rk : Fin n → ℕ} {off tgt fof ftf ttF : ℕ → ℕ}
    {v : Fin n} {u : ℕ}
    (hI : ∀ u : ℕ, u ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN v)
    (hF : ∀ u : ℕ, u ∈ Csr.row fof ftf (v : ℕ) ↔
      ∃ hu : u < n, (fratGraph D).Adj v ⟨u, hu⟩)
    (hT : ∀ u : ℕ, u ∈ Csr.row (trOff D) ttF (v : ℕ) ↔
      ∃ hu : u < n, TransLink D ⟨u, hu⟩ v) :
    u ∈ emE D rk off tgt fof ftf ttF (v : ℕ) ↔
      ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ emRow D rk v := by
  rw [emE_lt (k := (v : ℕ)) v.isLt, List.mem_append, List.mem_append,
    List.mem_filter, List.mem_filter, hI, hF, hT]
  constructor
  · rintro ((⟨hu, hmem⟩ | ⟨⟨hu, hadj⟩, hk⟩) | ⟨⟨hu, hlink⟩, hk⟩)
    · exact ⟨hu, mem_emRow.2 (Or.inl hmem)⟩
    · obtain ⟨h1, h2⟩ := (emKeepF_iff hu).1 hk
      exact ⟨hu, mem_emRow.2 (Or.inr (Or.inl ⟨hadj.symm, h1, h2⟩))⟩
    · obtain ⟨h1, h2, h3⟩ := (emKeepT_iff hu).1 hk
      exact ⟨hu, mem_emRow.2 (Or.inr (Or.inr ⟨hlink, h1, h2, h3⟩))⟩
  · rintro ⟨hu, hmem⟩
    rcases mem_emRow.1 hmem with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl (Or.inl ⟨hu, h⟩)
    · exact Or.inl (Or.inr ⟨⟨hu, h1.symm⟩, (emKeepF_iff hu).2 ⟨h2, h3⟩⟩)
    · exact Or.inr ⟨⟨hu, h1⟩, (emKeepT_iff hu).2 ⟨h2, h3, h4⟩⟩

/-- **The output row is duplicate-free.**  The three parts are, and they
do not meet: an old arc is adjacent and the two phases filter adjacency
out, and a fraternal pick is a `fratGraph`-neighbour, which the
transitive phase's seen test excludes. -/
theorem nodup_emE {D : Orientation n} {rk : Fin n → ℕ} {off tgt fof ftf ttF : ℕ → ℕ}
    {v : Fin n}
    (hI : ∀ u : ℕ, u ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN v)
    (hF : ∀ u : ℕ, u ∈ Csr.row fof ftf (v : ℕ) ↔
      ∃ hu : u < n, (fratGraph D).Adj v ⟨u, hu⟩)
    (hIn : (Csr.row off tgt (v : ℕ)).Nodup) (hFn : (Csr.row fof ftf (v : ℕ)).Nodup)
    (hTn : (Csr.row (trOff D) ttF (v : ℕ)).Nodup) :
    (emE D rk off tgt fof ftf ttF (v : ℕ)).Nodup := by
  rw [emE_lt (k := (v : ℕ)) v.isLt]
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hIn, hFn.filter _, ?_⟩,
    hTn.filter _, ?_⟩
  · rintro a ha b hb rfl
    obtain ⟨hun, hmem⟩ := (hI a).1 ha
    obtain ⟨-, hk⟩ := List.mem_filter.1 hb
    exact ((emKeepF_iff hun).1 hk).1 (Or.inl hmem)
  · rintro a ha b hb rfl
    obtain ⟨-, hk⟩ := List.mem_filter.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨hun, hmem⟩ := (hI a).1 ha
      exact ((emKeepT_iff hun).1 hk).2.1 (Or.inl hmem)
    · obtain ⟨huf, -⟩ := List.mem_filter.1 ha
      obtain ⟨hun, hadj⟩ := (hF a).1 huf
      exact ((emKeepT_iff hun).1 hk).1 hadj.symm


/-! ## §4 The uniform row scan

`emStep` is the one body all four scans run, `emRowScan` the scan that
loads a row's bounds and runs it.  Both are parameterised by the
condition block `cnd`, which is asked for exactly one thing: from a
state agreeing with the scan's entry outside `t'` and the stamp array
`A`, leave `em.c` at the truth value of `keep` on the candidate in
`em.u` and change nothing else. -/

private theorem getD_set_self {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem getD_set_of_ne {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c).getD q 0 = l.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

private theorem evB_var' {B : ℕ} {y : String} {σ : Env} {c : ℕ} (hy : σ.vars y = c)
    (hc : c < B) : (Expr.var y).evalB B σ = some c := by
  rw [← hy] at hc ⊢; exact evalB_var hc

private theorem evB_lit' {B c : ℕ} {σ : Env} (hc : c < B) :
    (Expr.lit c).evalB B σ = some c := evalB_lit hc

private theorem evB_add' {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (hab : a + b < B) :
    (Expr.add e f).evalB B σ = some (a + b) := evalB_bin he hf (by simpa using hab)

private theorem evB_mul' {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (hab : a * b < B) :
    (Expr.mul e f).evalB B σ = some (a * b) := evalB_bin he hf (by simpa using hab)

private theorem evB_get' {B : ℕ} {a : String} {i : Expr} {σ : Env} {q c : ℕ}
    (hi : i.evalB B σ = some q) (hq : (σ.arrs a)[q]? = some c) (hc : c < B) :
    (Expr.get a i).evalB B σ = some c := evalB_get hi hq hc

private theorem run_assign' {B : ℕ} {x : String} {e : Expr} {σ : Env} {c K : ℕ}
    (he : e.evalB B σ = some c) (hK : 1 + e.size ≤ K) :
    Run B (.assign x e) σ (σ.setVar x c) K := (Run.assign he).mono hK

private theorem run_store' {B : ℕ} {a : String} {i e : Expr} {σ : Env} {q c K : ℕ}
    (hi : i.evalB B σ = some q) (he : e.evalB B σ = some c)
    (hq : q < (σ.arrs a).length) (hK : 1 + i.size + e.size ≤ K) :
    Run B (.store a i e) σ (σ.setArr a q c) K := (Run.store hi he hq).mono hK

private theorem getElem?_of_lt' (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The emit pass's scalars: the head, its stamp value and its rank, the
output write pointer, the row pointer and its end, the current target
and the condition flag. -/
def emScalars : List String :=
  ["em.v", "em.v1", "em.r", "em.p", "em.j", "em.e", "em.u", "em.c"]

private theorem emScalars_ne {y : String} (h : y ∉ emScalars) :
    y ≠ "em.v" ∧ y ≠ "em.v1" ∧ y ≠ "em.r" ∧ y ≠ "em.p" ∧ y ≠ "em.j" ∧
      y ≠ "em.e" ∧ y ≠ "em.u" ∧ y ≠ "em.c" := by
  simp only [emScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- **One turn of a row scan**: read the target, decide, emit if the
decision says so, stamp, advance. -/
def emStep (st A t' : String) (cnd : Com) : Com :=
  .seq (.assign "em.u" (.get st (.var "em.j")))
    (.seq cnd
      (.seq (.ite (.eq (.var "em.c") (.lit 1))
              (.seq (.store t' (.var "em.p") (.var "em.u"))
                (.assign "em.p" (.add (.var "em.p") (.lit 1))))
              .skip)
        (.seq (.store A (.var "em.u") (.var "em.v1"))
          (.assign "em.j" (.add (.var "em.j") (.lit 1))))))

/-- **One row scan**: load the row's bounds off its offsets, then run
the turn over its slots. -/
def emRowScan (so st A t' : String) (cnd : Com) : Com :=
  .seq (.assign "em.j" (.get so (.var "em.v")))
    (.seq (.assign "em.e" (.get so (.add (.var "em.v") (.lit 1))))
      (Csr.scan "em.j" "em.e" (emStep st A t' cnd)))

/-- **What a row scan carries.**  The entry state `σ₀` is the scan's
own; only `t'` and the stamp array `A` move, the write pointer counts
what row `v` has emitted, the written cells of `t'` already agree with
the finished target array, and `A` is stamped exactly on the part of the
row already scanned. -/
private def EmScanI (nN t' A : String) (n : ℕ) (sof stf : ℕ → ℕ) (keep : ℕ → Bool)
    (E : ℕ → List ℕ) (v R : ℕ) (base : List ℕ) (σ₀ σ : Env) : Prop :=
  (∀ b, b ≠ t' → b ≠ A → σ.arrs b = σ₀.arrs b) ∧
    (σ.arrs t').length = (σ₀.arrs t').length ∧
    (σ.arrs A).length = (σ₀.arrs A).length ∧
    σ.vars nN = n ∧ σ.vars "em.v" = v ∧ σ.vars "em.v1" = v + 1 ∧
    σ.vars "em.r" = R ∧ σ.vars "em.e" = sof (v + 1) ∧
    sof v ≤ σ.vars "em.j" ∧ σ.vars "em.j" ≤ sof (v + 1) ∧
    σ.vars "em.p"
      = emOff E v + (base ++ (rowPre sof stf v (σ.vars "em.j")).filter keep).length ∧
    (∀ q, q < σ.vars "em.p" → (σ.arrs t').getD q 0 = (emPref E n).getD q 0) ∧
    (∀ q, q < n → (σ.arrs A).getD q 0
      = if q ∈ rowPre sof stf v (σ.vars "em.j") then v + 1 else (σ₀.arrs A).getD q 0)

/-- What the scan has emitted after `m` slots is a prefix of the row it
is building. -/
private theorem emit_prefix {sof stf : ℕ → ℕ} {keep : ℕ → Bool} {base : List ℕ}
    {E : ℕ → List ℕ} {v m : ℕ}
    (hbase : base ++ (Csr.row sof stf v).filter keep <+: E v)
    (hm : m ≤ sof (v + 1)) :
    base ++ (rowPre sof stf v m).filter keep <+: E v := by
  refine List.IsPrefix.trans ?_ hbase
  obtain ⟨r, hr⟩ := filter_prefix_filter (rowPre_prefix sof stf hm) keep
  exact ⟨r, by rw [List.append_assoc, hr]⟩

/-- **One turn of a row scan, discharged**, at `21` plus the condition
block's own cost.  The `if` is the only place the two cases differ, and
they differ only in the write pointer and one cell of `t'`. -/
private theorem emStep_run {B n : ℕ} {st A t' nN : String}
    {sof stf : ℕ → ℕ} {ext : ℕ} {keep : ℕ → Bool} {cnd : Com} {Kc : ℕ}
    {E : ℕ → List ℕ} {v R : ℕ} {base : List ℕ} {σ₀ σ : Env}
    (hnN : nN ∉ emScalars) (hAt : A ≠ t') (hstt : st ≠ t') (hstA : st ≠ A)
    (hnB : n < B) (hextB : ext < B) (hnsB : emNs n E < B)
    (hstGet : ∀ p, p < ext → (σ₀.arrs st)[p]? = some (stf p))
    (hstLt : ∀ p, p < ext → stf p < n)
    (hALen : n ≤ (σ₀.arrs A).length)
    (htLen : emNs n E ≤ (σ₀.arrs t').length)
    (hv : v < n) (hext : sof (v + 1) ≤ ext)
    (hbase : base ++ (Csr.row sof stf v).filter keep <+: E v)
    (hcnd : ∀ (τ : Env) (u : ℕ), u < n → τ.vars "em.u" = u → τ.vars "em.v" = v →
      τ.vars "em.v1" = v + 1 → τ.vars "em.r" = R → τ.vars nN = n →
      (∀ b, b ≠ t' → b ≠ A → τ.arrs b = σ₀.arrs b) →
      Run B cnd τ (τ.setVar "em.c" (if keep u then 1 else 0)) Kc)
    (hI : EmScanI nN t' A n sof stf keep E v R base σ₀ σ)
    (hlt : σ.vars "em.j" < sof (v + 1)) :
    ∃ σ' K', Run B (emStep st A t' cnd) σ σ' K' ∧
      EmScanI nN t' A n sof stf keep E v R base σ₀ σ' ∧
      σ'.vars "em.j" = σ.vars "em.j" + 1 ∧ K' ≤ 21 + Kc := by
  classical
  obtain ⟨hnv, hnv1, hnr, hnp, hnj, hne, hnu, hnc⟩ := emScalars_ne hnN
  obtain ⟨harr, htl, hal, hcar, hvv, hv1, hrr, hev, hj1, hj2, hpv, htv, hav⟩ := hI
  obtain ⟨j, hj⟩ : ∃ j, σ.vars "em.j" = j := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, σ.vars "em.p" = p := ⟨_, rfl⟩
  rw [hj] at hj1 hj2 hlt hpv hav
  rw [hp] at hpv htv
  have hjext : j < ext := by omega
  have hun : stf j < n := hstLt j hjext
  have hstσ : σ.arrs st = σ₀.arrs st := harr st hstt hstA
  have hget : (σ.arrs st)[j]? = some (stf j) := by rw [hstσ]; exact hstGet j hjext
  -- the row prefix grows by one entry
  have hsplit : (rowPre sof stf v (j + 1)).filter keep
      = (rowPre sof stf v j).filter keep ++ (if keep (stf j) then [stf j] else []) := by
    rw [rowPre_succ sof stf hj1, List.filter_append]
    congr 1
    by_cases hk : keep (stf j) = true
    · rw [List.filter_cons_of_pos hk, List.filter_nil, if_pos hk]
    · rw [List.filter_cons_of_neg (by simpa using hk), List.filter_nil, if_neg hk]
  have hnext : base ++ (rowPre sof stf v (j + 1)).filter keep <+: E v :=
    emit_prefix hbase (by omega)
  have hlenPre : (base ++ (rowPre sof stf v (j + 1)).filter keep).length
      = (base ++ (rowPre sof stf v j).filter keep).length
        + (if keep (stf j) then 1 else 0) := by
    rw [hsplit]
    by_cases hk : keep (stf j) = true
    · simp [hk]; omega
    · simp [hk]
  have hlenE : (base ++ (rowPre sof stf v j).filter keep).length
      + (if keep (stf j) then 1 else 0) ≤ (E v).length := by
    obtain ⟨r, hr⟩ := hnext
    rw [← hlenPre, ← hr]
    simp only [List.length_append]
    omega
  have hoffs : emOff E (v + 1) = emOff E v + (E v).length := emOff_succ E v
  have hoffn : emOff E (v + 1) ≤ emNs n E := by
    rw [emNs, emOff, emOff]
    exact length_flatPref_mono E (by omega)
  have hplen : p + (if keep (stf j) then 1 else 0) ≤ emNs n E := by
    rw [hpv]; omega
  have htlen' : (σ.arrs t').length = (σ₀.arrs t').length := htl
  -- `em.u := st[em.j]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "em.u" (stf j) := ⟨_, rfl⟩
  have r1 : Run B (.assign "em.u" (.get st (.var "em.j"))) σ σ1 3 := by
    rw [hσ1]
    exact run_assign' (evB_get' (evB_var' hj (by omega)) hget (by omega)) (by simp)
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  -- the condition block
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "em.c" (if keep (stf j) then 1 else 0) := ⟨_, rfl⟩
  have r2 : Run B cnd σ1 σ2 Kc := by
    rw [hσ2]
    refine hcnd σ1 (stf j) hun (by rw [hσ1]; simp) (by rw [hσ1]; simp [hvv])
      (by rw [hσ1]; simp [hv1]) (by rw [hσ1]; simp [hrr])
      (by rw [hσ1]; simp [hnu, hcar]) ?_
    intro b hb1 hb2
    rw [h1a]; exact harr b hb1 hb2
  have h2a : σ2.arrs = σ.arrs := by rw [hσ2, hσ1]; simp
  have h2c : σ2.vars "em.c" = (if keep (stf j) then 1 else 0) := by rw [hσ2]; simp
  have h2p : σ2.vars "em.p" = p := by rw [hσ2, hσ1]; simp [hp]
  have h2u : σ2.vars "em.u" = stf j := by rw [hσ2, hσ1]; simp
  -- the conditional emit
  obtain ⟨τ, hrun3, hτarr, hτlen, hτvars, hτp, hτtv⟩ :
      ∃ τ, Run B (.ite (.eq (.var "em.c") (.lit 1))
              (.seq (.store t' (.var "em.p") (.var "em.u"))
                (.assign "em.p" (.add (.var "em.p") (.lit 1)))) .skip) σ2 τ 11 ∧
        (∀ b, b ≠ t' → τ.arrs b = σ.arrs b) ∧
        (τ.arrs t').length = (σ.arrs t').length ∧
        (∀ y, y ≠ "em.p" → τ.vars y = σ2.vars y) ∧
        τ.vars "em.p" = p + (if keep (stf j) then 1 else 0) ∧
        (∀ q, q < τ.vars "em.p" → (τ.arrs t').getD q 0 = (emPref E n).getD q 0) := by
    by_cases hk : keep (stf j) = true
    · -- the candidate is emitted
      have hc1 : σ2.vars "em.c" = 1 := by rw [h2c, if_pos hk]
      have hpt : p < (σ2.arrs t').length := by rw [h2a]; omega
      have hstore : Run B (.store t' (.var "em.p") (.var "em.u")) σ2
          (σ2.setArr t' p (stf j)) 3 :=
        run_store' (evB_var' h2p (by omega)) (evB_var' h2u (by omega)) hpt (by simp)
      have hbump : Run B (.assign "em.p" (.add (.var "em.p") (.lit 1)))
          (σ2.setArr t' p (stf j))
          ((σ2.setArr t' p (stf j)).setVar "em.p" (p + 1)) 4 :=
        run_assign' (evB_add' (evB_var' (by simp [h2p]) (by omega))
          (evB_lit' (by omega)) (by omega)) (by simp)
      refine ⟨_, (Run.ite_true (evalB_condEq (evB_var' hc1 (by omega))
        (evB_lit' (by omega))) (hstore.seq hbump)).mono (by simp), ?_, ?_, ?_, ?_, ?_⟩
      · intro b hb; simp [hb, h2a]
      · simp [h2a]
      · intro y hy; simp [hy]
      · simp [if_pos hk]
      · intro q hq
        have hqp : q < p + 1 := by simpa using hq
        have hval : (emPref E n).getD p 0 = stf j := by
          obtain ⟨r, hr⟩ := hnext
          have hsp : base ++ (rowPre sof stf v (j + 1)).filter keep
              = (base ++ (rowPre sof stf v j).filter keep) ++ [stf j] := by
            rw [hsplit, if_pos hk, List.append_assoc]
          have hlt' : (base ++ (rowPre sof stf v j).filter keep).length < (E v).length := by
            rw [if_pos hk] at hlenE; omega
          rw [hpv, emPref, emOff, emPref, flatPref_getD E hv hlt', ← hr, hsp]
          rw [List.getD_append _ _ _ _ (by rw [List.length_append]; simp),
            List.getD_append_right _ _ _ _ (le_rfl)]
          simp
        have harrq : ((σ2.setArr t' p (stf j)).setVar "em.p" (p + 1)).arrs t'
            = (σ.arrs t').set p (stf j) := by simp [h2a]
        rw [harrq]
        rcases Nat.lt_or_ge q p with hq' | hq'
        · rw [getD_set_of_ne (by omega)]; exact htv q hq'
        · obtain rfl : q = p := by omega
          rw [getD_set_self (by omega), hval]
    · -- the candidate is skipped
      have hc0 : σ2.vars "em.c" = 0 := by rw [h2c, if_neg hk]
      refine ⟨σ2, (Run.ite_false (evalB_condEq (evB_var' hc0 (by omega))
        (evB_lit' (by omega))) Run.skip).mono (by simp), ?_, ?_, ?_, ?_, ?_⟩
      · intro b _; rw [h2a]
      · rw [h2a]
      · intro y _; rfl
      · rw [h2p, if_neg hk]; omega
      · intro q hq
        rw [h2a]
        exact htv q (by rw [h2p] at hq; exact hq)
  -- the stamp, and the advance
  have hτA : τ.arrs A = σ.arrs A := hτarr A hAt
  have hτu : τ.vars "em.u" = stf j := by rw [hτvars "em.u" (by decide), h2u]
  have hτv1 : τ.vars "em.v1" = v + 1 := by
    rw [hτvars "em.v1" (by decide), hσ2, hσ1]; simp [hv1]
  obtain ⟨σ4, hσ4⟩ : ∃ τ', τ' = τ.setArr A (stf j) (v + 1) := ⟨_, rfl⟩
  have r4 : Run B (.store A (.var "em.u") (.var "em.v1")) τ σ4 3 := by
    rw [hσ4]
    exact run_store' (evB_var' hτu (by omega)) (evB_var' hτv1 (by omega))
      (by rw [hτA]; omega) (by simp)
  have h4j : σ4.vars "em.j" = j := by
    rw [hσ4]; simp; rw [hτvars "em.j" (by decide), hσ2, hσ1]; simp [hj]
  obtain ⟨σ5, hσ5⟩ : ∃ τ', τ' = σ4.setVar "em.j" (j + 1) := ⟨_, rfl⟩
  have r5 : Run B (.assign "em.j" (.add (.var "em.j") (.lit 1))) σ4 σ5 4 := by
    rw [hσ5]
    exact run_assign' (evB_add' (evB_var' h4j (by omega)) (evB_lit' (by omega))
      (by omega)) (by simp)
  refine ⟨σ5, 21 + Kc, ((r1.seq (r2.seq (hrun3.seq (r4.seq r5)))).mono (by omega)),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, le_rfl⟩
  · intro b hb1 hb2
    rw [hσ5]; simp
    rw [hσ4]; simp [hb2]
    rw [hτarr b hb1]
    exact harr b hb1 hb2
  · rw [hσ5]; simp; rw [hσ4]; simp [Ne.symm hAt]; rw [hτlen]; exact htl
  · rw [hσ5]; simp; rw [hσ4]; simp; rw [hτA]; exact hal
  · rw [hσ5]; simp [hnj]; rw [hσ4]; simp
    rw [hτvars nN hnp, hσ2, hσ1]; simp [hnu, hnc, hcar]
  · rw [hσ5]; simp; rw [hσ4]; simp
    rw [hτvars "em.v" (by decide), hσ2, hσ1]; simp [hvv]
  · rw [hσ5]; simp; rw [hσ4]; simp; rw [hτv1]
  · rw [hσ5]; simp; rw [hσ4]; simp
    rw [hτvars "em.r" (by decide), hσ2, hσ1]; simp [hrr]
  · rw [hσ5]; simp; rw [hσ4]; simp
    rw [hτvars "em.e" (by decide), hσ2, hσ1]; simp [hev]
  · rw [hσ5]; simp; omega
  · rw [hσ5]; simp; omega
  · have hjv : σ5.vars "em.j" = j + 1 := by rw [hσ5]; simp
    have hpv5 : σ5.vars "em.p" = τ.vars "em.p" := by rw [hσ5]; simp; rw [hσ4]; simp
    rw [hjv, hpv5, hτp, hlenPre, hpv]
    omega
  · intro q hq
    have hpvv : σ5.vars "em.p" = τ.vars "em.p" := by
      rw [hσ5]; simp; rw [hσ4]; simp
    have harrq : σ5.arrs t' = τ.arrs t' := by
      rw [hσ5]; simp; rw [hσ4]; simp [Ne.symm hAt]
    rw [harrq]
    exact hτtv q (by rw [← hpvv]; exact hq)
  · intro q hq
    have hjv : σ5.vars "em.j" = j + 1 := by rw [hσ5]; simp
    have harrq : σ5.arrs A = (σ.arrs A).set (stf j) (v + 1) := by
      rw [hσ5]; simp; rw [hσ4]; simp [hτA]
    rw [hjv, harrq, rowPre_succ sof stf hj1]
    rcases eq_or_ne q (stf j) with rfl | hqu
    · rw [getD_set_self (by omega), if_pos (by simp)]
    · rw [getD_set_of_ne (Ne.symm hqu), hav q hq]
      by_cases hm : q ∈ rowPre sof stf v j
      · rw [if_pos hm, if_pos (by simp [hm])]
      · rw [if_neg hm, if_neg (by simp [hm, hqu])]
  · rw [hσ5]; simp [hj]

/-- **One row scan, discharged**: the row's bounds, then its slots, at
`25 + Kc` a slot and `12` fixed.  What it leaves is the whole row's
emissions appended to `base` and the whole row stamped into `A`. -/
private theorem emRowScan_run {B n : ℕ} {so st A t' nN : String}
    {sof stf : ℕ → ℕ} {ext : ℕ} {keep : ℕ → Bool} {cnd : Com} {Kc : ℕ}
    {E : ℕ → List ℕ} {v R : ℕ} {base : List ℕ} {σ : Env}
    (hnN : nN ∉ emScalars) (hAt : A ≠ t') (hstt : st ≠ t') (hstA : st ≠ A)
    (hnB : n < B) (hextB : ext < B) (hnsB : emNs n E < B)
    (hsoGet : ∀ i, i ≤ n → (σ.arrs so)[i]? = some (sof i))
    (hstGet : ∀ p, p < ext → (σ.arrs st)[p]? = some (stf p))
    (hstLt : ∀ p, p < ext → stf p < n)
    (hALen : n ≤ (σ.arrs A).length)
    (htLen : emNs n E ≤ (σ.arrs t').length)
    (hv : v < n) (hrow : sof v ≤ sof (v + 1)) (hext : sof (v + 1) ≤ ext)
    (hbase : base ++ (Csr.row sof stf v).filter keep <+: E v)
    (hcnd : ∀ (τ : Env) (u : ℕ), u < n → τ.vars "em.u" = u → τ.vars "em.v" = v →
      τ.vars "em.v1" = v + 1 → τ.vars "em.r" = R → τ.vars nN = n →
      (∀ b, b ≠ t' → b ≠ A → τ.arrs b = σ.arrs b) →
      Run B cnd τ (τ.setVar "em.c" (if keep u then 1 else 0)) Kc)
    (hcar : σ.vars nN = n) (hvv : σ.vars "em.v" = v) (hv1 : σ.vars "em.v1" = v + 1)
    (hrr : σ.vars "em.r" = R)
    (hpv : σ.vars "em.p" = emOff E v + base.length)
    (htv : ∀ q, q < σ.vars "em.p" → (σ.arrs t').getD q 0 = (emPref E n).getD q 0) :
    ∃ σ' K', Run B (emRowScan so st A t' cnd) σ σ' K' ∧
      K' ≤ (25 + Kc) * (sof (v + 1) - sof v) + 12 ∧
      (∀ b, b ≠ t' → b ≠ A → σ'.arrs b = σ.arrs b) ∧
      (σ'.arrs t').length = (σ.arrs t').length ∧
      (σ'.arrs A).length = (σ.arrs A).length ∧
      σ'.vars nN = n ∧ σ'.vars "em.v" = v ∧ σ'.vars "em.v1" = v + 1 ∧
      σ'.vars "em.r" = R ∧
      σ'.vars "em.p" = emOff E v + (base ++ (Csr.row sof stf v).filter keep).length ∧
      (∀ q, q < σ'.vars "em.p" → (σ'.arrs t').getD q 0 = (emPref E n).getD q 0) ∧
      (∀ q, q < n → (σ'.arrs A).getD q 0
        = if q ∈ Csr.row sof stf v then v + 1 else (σ.arrs A).getD q 0) := by
  classical
  obtain ⟨hnv, hnv1, hnr, hnp, hnj, hne, hnu, hnc⟩ := emScalars_ne hnN
  have hsofB : sof (v + 1) < B := by omega
  have hsoget : (σ.arrs so)[v]? = some (sof v) := hsoGet v (by omega)
  have hsoget1 : (σ.arrs so)[v + 1]? = some (sof (v + 1)) := hsoGet (v + 1) (by omega)
  -- `em.j := so[em.v]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "em.j" (sof v) := ⟨_, rfl⟩
  have r1 : Run B (.assign "em.j" (.get so (.var "em.v"))) σ σ1 3 := by
    rw [hσ1]
    exact run_assign' (evB_get' (evB_var' hvv (by omega)) hsoget (by omega)) (by simp)
  -- `em.e := so[em.v + 1]`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "em.e" (sof (v + 1)) := ⟨_, rfl⟩
  have r2 : Run B (.assign "em.e" (.get so (.add (.var "em.v") (.lit 1)))) σ1 σ2 5 := by
    rw [hσ2]
    have hv1' : σ1.vars "em.v" = v := by rw [hσ1]; simp [hvv]
    have ha : σ1.arrs so = σ.arrs so := by rw [hσ1]; simp
    exact run_assign' (evB_get'
      (evB_add' (evB_var' hv1' (by omega)) (evB_lit' (by omega)) (by omega))
      (by rw [ha]; exact hsoget1) (by omega)) (by simp)
  have h2a : σ2.arrs = σ.arrs := by rw [hσ2, hσ1]; simp
  have h2j : σ2.vars "em.j" = sof v := by rw [hσ2, hσ1]; simp
  have hI2 : EmScanI nN t' A n sof stf keep E v R base σ σ2 := by
    refine ⟨fun b _ _ => by rw [h2a], by rw [h2a], by rw [h2a], ?_, ?_, ?_, ?_, ?_,
      by rw [h2j], by rw [h2j]; exact hrow, ?_, ?_, ?_⟩
    · rw [hσ2, hσ1]; simp [hne, hnj, hcar]
    · rw [hσ2, hσ1]; simp [hvv]
    · rw [hσ2, hσ1]; simp [hv1]
    · rw [hσ2, hσ1]; simp [hrr]
    · rw [hσ2, hσ1]; simp
    · rw [h2j, rowPre_start]
      rw [hσ2, hσ1]; simpa using hpv
    · intro q hq
      rw [h2a]
      refine htv q ?_
      rw [hσ2, hσ1] at hq; simpa using hq
    · intro q hq
      rw [h2j, rowPre_start, h2a]
      simp
  -- the slots
  have hscan := (Csr.rowScan_spec B ((25 + Kc) * (sof (v + 1) - sof v) + 4)
    (sof (v + 1)) (21 + Kc) "em.j" "em.e" (emStep st A t' cnd)
    (P := EmScanI nN t' A n sof stf keep E v R base σ)
    (EmScanI nN t' A n sof stf keep E v R base σ) hsofB
    (fun τ hτ => ⟨hτ.2.2.2.2.2.2.2.1, hτ.2.2.2.2.2.2.2.2.2.1⟩)
    (fun τ hτ hlt => emStep_run hnN hAt hstt hstA hnB hextB hnsB hstGet hstLt hALen
      htLen hv hext hbase hcnd hτ hlt)
    (fun _ h => h)
    (fun τ hτ => by
      have hge := hτ.2.2.2.2.2.2.2.2.1
      have hsub : sof (v + 1) - τ.vars "em.j" ≤ sof (v + 1) - sof v := by omega
      have hmul : (21 + Kc + 4) * (sof (v + 1) - τ.vars "em.j")
          ≤ (25 + Kc) * (sof (v + 1) - sof v) := by
        rw [show 21 + Kc + 4 = 25 + Kc by omega]
        exact Nat.mul_le_mul_left _ hsub
      omega)).run hI2
  obtain ⟨σ3, hrun3, hI3, hj3⟩ := hscan
  obtain ⟨harr3, htl3, hal3, hcar3, hvv3, hv13, hrr3, hev3, -, -, hpv3, htv3, hav3⟩ := hI3
  rw [hj3, rowPre_end] at hpv3 hav3
  refine ⟨σ3, 3 + (5 + ((25 + Kc) * (sof (v + 1) - sof v) + 4)),
    r1.seq (r2.seq hrun3), by omega, ?_, ?_, ?_, hcar3, hvv3, hv13, hrr3, hpv3,
    htv3, ?_⟩
  · intro b hb1 hb2; rw [harr3 b hb1 hb2]
  · rw [htl3]
  · rw [hal3]
  · intro q hq; rw [hav3 q hq]

/-! ## §5 The four condition blocks

The only thing the scans differ in.  Each is a straight-line block that
sets `em.c` and nothing else — no temporary, so the index `u·n + v` of
the matrix read is inlined — and each meets the obligation `emStep_run`
states for it, at the cost its shape gives.

The stamp tests are `<`, not `≠`: IMP+ has no disequality, and the
carried invariant "every cell is `≤ v + 1` at head `v`" makes the two
the same test (Finding 3). -/

private theorem setVar_setVar_self (σ : Env) (x : String) (a b : ℕ) :
    (σ.setVar x a).setVar x b = σ.setVar x b := by
  simp only [Env.setVar]
  congr 1
  funext y
  by_cases h : y = x <;> simp [h]

/-- The input row's decision: keep the old arc. -/
def emCndIn : Com := .assign "em.c" (.lit 1)

/-- The transpose row's decision: stamp only. -/
def emCndOut : Com := .assign "em.c" (.lit 0)

/-- The fraternal row's decision: `EmFratPick`, in two nested tests. -/
def emCndFrat (ad sg : String) : Com :=
  .seq (.assign "em.c" (.lit 0))
    (.ite (.lt (.get ad (.var "em.u")) (.var "em.v1"))
      (.ite (.lt (.get sg (.var "em.u")) (.var "em.r"))
        (.assign "em.c" (.lit 1)) .skip)
      .skip)

/-- The transitive row's decision: `EmTransPick`, in four nested tests,
the innermost being the `O(1)` matrix read that decides the forced
direction. -/
def emCndTrans (nN ad sd sg mk : String) : Com :=
  .seq (.assign "em.c" (.lit 0))
    (.ite (.lt (.get sd (.var "em.u")) (.var "em.v1"))
      (.ite (.lt (.get ad (.var "em.u")) (.var "em.v1"))
        (.ite (.lt (.get sg (.var "em.u")) (.var "em.r"))
          (.assign "em.c" (.lit 1))
          (.ite (.lt (.get mk (.add (.mul (.var "em.u") (.var nN)) (.var "em.v")))
                  (.lit 1))
            (.assign "em.c" (.lit 1)) .skip))
        .skip)
      .skip)

private theorem emCndIn_run {B : ℕ} {τ : Env} (hB : 1 < B) :
    Run B emCndIn τ (τ.setVar "em.c" 1) 2 :=
  run_assign' (evB_lit' hB) (by simp)

private theorem emCndOut_run {B : ℕ} {τ : Env} (hB : 0 < B) :
    Run B emCndOut τ (τ.setVar "em.c" 0) 2 :=
  run_assign' (evB_lit' hB) (by simp)

/-- **The fraternal decision, discharged** at `14`: the adjacency stamp
and the two ranks. -/
private theorem emCndFrat_run {B n : ℕ} {ad sg : String} {D : Orientation n}
    {rk : Fin n → ℕ} {v : Fin n} {τ : Env} {u : ℕ} (hu : u < n) (hnB : n < B)
    (hrkB : ∀ w : Fin n, rk w < B)
    (hus : τ.vars "em.u" = u) (hv1 : τ.vars "em.v1" = (v : ℕ) + 1)
    (hrr : τ.vars "em.r" = rk v)
    (hadL : n ≤ (τ.arrs ad).length)
    (hadLt : ∀ q, q < n → (τ.arrs ad).getD q 0 ≤ (v : ℕ) + 1)
    (hadEq : ∀ w : Fin n, (τ.arrs ad).getD (w : ℕ) 0 = (v : ℕ) + 1 ↔ D.Adjacent w v)
    (hsgGet : ∀ w : Fin n, (τ.arrs sg)[(w : ℕ)]? = some (rk w)) :
    Run B (emCndFrat ad sg) τ
      (τ.setVar "em.c" (if emKeepF D rk v u then 1 else 0)) 14 := by
  classical
  have hvB : (v : ℕ) + 1 < B := by have := v.isLt; omega
  have h0 : Run B (.assign "em.c" (.lit 0)) τ (τ.setVar "em.c" 0) 2 :=
    run_assign' (evB_lit' (by omega)) (by simp)
  have h0a : (τ.setVar "em.c" 0).arrs = τ.arrs := by simp
  have h0u : (τ.setVar "em.c" 0).vars "em.u" = u := by simp [hus]
  have h0v1 : (τ.setVar "em.c" 0).vars "em.v1" = (v : ℕ) + 1 := by simp [hv1]
  have h0r : (τ.setVar "em.c" 0).vars "em.r" = rk v := by simp [hrr]
  have hadget : ((τ.setVar "em.c" 0).arrs ad)[u]? = some ((τ.arrs ad).getD u 0) := by
    rw [h0a]; exact getElem?_of_lt' _ _ (by omega)
  have hadB : (τ.arrs ad).getD u 0 < B := by have := hadLt u hu; omega
  have hcond : (Cond.lt (.get ad (.var "em.u")) (.var "em.v1")).evalB B
      (τ.setVar "em.c" 0) = some (decide ((τ.arrs ad).getD u 0 < (v : ℕ) + 1)) :=
    evalB_condLt (evB_get' (evB_var' h0u (by omega)) hadget hadB) (evB_var' h0v1 hvB)
  have h1 : (τ.arrs ad).getD u 0 ≤ (v : ℕ) + 1 := hadLt u hu
  have h2 : (τ.arrs ad).getD u 0 = (v : ℕ) + 1 ↔ D.Adjacent ⟨u, hu⟩ v := hadEq ⟨u, hu⟩
  have hadj : (τ.arrs ad).getD u 0 < (v : ℕ) + 1 ↔ ¬ D.Adjacent ⟨u, hu⟩ v := by
    constructor
    · intro h hc; rw [h2.2 hc] at h; omega
    · intro h
      rcases Nat.lt_or_ge ((τ.arrs ad).getD u 0) ((v : ℕ) + 1) with h' | h'
      · exact h'
      · exact absurd (h2.1 (by omega)) h
  by_cases hA : D.Adjacent ⟨u, hu⟩ v
  · have hkeep : emKeepF D rk v u = false := by
      by_contra hc
      exact ((emKeepF_iff hu).1 (by simpa using hc)).1 hA
    rw [hkeep]
    refine (h0.seq (Run.ite_false ?_ Run.skip)).mono (by simp)
    rw [hcond, decide_eq_false (fun h => (hadj.1 h) hA)]
  · have hsgget : ((τ.setVar "em.c" 0).arrs sg)[u]? = some (rk ⟨u, hu⟩) := by
      rw [h0a]; exact hsgGet ⟨u, hu⟩
    have hcond2 : (Cond.lt (.get sg (.var "em.u")) (.var "em.r")).evalB B
        (τ.setVar "em.c" 0) = some (decide (rk ⟨u, hu⟩ < rk v)) :=
      evalB_condLt (evB_get' (evB_var' h0u (by omega)) hsgget (hrkB _))
        (evB_var' h0r (hrkB v))
    have htrue : (Cond.lt (.get ad (.var "em.u")) (.var "em.v1")).evalB B
        (τ.setVar "em.c" 0) = some true := by
      rw [hcond, decide_eq_true (hadj.2 hA)]
    by_cases hlt : rk ⟨u, hu⟩ < rk v
    · have hkeep : emKeepF D rk v u = true := (emKeepF_iff hu).2 ⟨hA, hlt⟩
      rw [hkeep, if_pos rfl]
      have hset : Run B (.assign "em.c" (.lit 1)) (τ.setVar "em.c" 0)
          (τ.setVar "em.c" 1) 2 := by
        have := run_assign' (B := B) (x := "em.c") (e := .lit 1)
          (σ := τ.setVar "em.c" 0) (c := 1) (K := 2) (evB_lit' (by omega)) (by simp)
        rwa [setVar_setVar_self] at this
      exact (h0.seq (Run.ite_true htrue
        (Run.ite_true (by rw [hcond2, decide_eq_true hlt]) hset))).mono
        (by simp)
    · have hkeep : emKeepF D rk v u = false := by
        by_contra hc
        exact hlt ((emKeepF_iff hu).1 (by simpa using hc)).2
      rw [hkeep]
      exact (h0.seq (Run.ite_true htrue
        (Run.ite_false (by rw [hcond2, decide_eq_false hlt]) Run.skip))).mono
        (by simp)

open Classical in
/-- **The transitive decision, discharged** at `28`: the seen stamp, the
adjacency stamp, the two ranks, and — only when the ranks say no — the
single matrix cell `mk[u·n + v]` that decides the forced direction
(`transCsrAt_decides`). -/
private theorem emCndTrans_run {B n : ℕ} {nN ad sd sg mk : String} {D : Orientation n}
    {rk : Fin n → ℕ} {v : Fin n} {τ : Env} {u : ℕ} (hu : u < n) (hnB : n < B)
    (hnnB : n * n < B) (hrkB : ∀ w : Fin n, rk w < B)
    (hus : τ.vars "em.u" = u) (hvv : τ.vars "em.v" = (v : ℕ))
    (hv1 : τ.vars "em.v1" = (v : ℕ) + 1) (hrr : τ.vars "em.r" = rk v)
    (hcar : τ.vars nN = n) (hnc : nN ≠ "em.c")
    (hadL : n ≤ (τ.arrs ad).length)
    (hadLt : ∀ q, q < n → (τ.arrs ad).getD q 0 ≤ (v : ℕ) + 1)
    (hadEq : ∀ w : Fin n, (τ.arrs ad).getD (w : ℕ) 0 = (v : ℕ) + 1 ↔ D.Adjacent w v)
    (hsdL : n ≤ (τ.arrs sd).length)
    (hsdLt : ∀ q, q < n → (τ.arrs sd).getD q 0 ≤ (v : ℕ) + 1)
    (hsdEq : ∀ w : Fin n, (τ.arrs sd).getD (w : ℕ) 0 = (v : ℕ) + 1 ↔ (fratGraph D).Adj w v)
    (hsgGet : ∀ w : Fin n, (τ.arrs sg)[(w : ℕ)]? = some (rk w))
    (hmkL : n * n ≤ (τ.arrs mk).length)
    (hmk : ∀ w : Fin n, (τ.arrs mk).getD ((w : ℕ) * n + (v : ℕ)) 0
      = if TransLink D v w then 1 else 0) :
    Run B (emCndTrans nN ad sd sg mk) τ
      (τ.setVar "em.c" (if emKeepT D rk v u then 1 else 0)) 28 := by
  classical
  have hvB : (v : ℕ) + 1 < B := by have := v.isLt; omega
  have hidx : u * n + (v : ℕ) < n * n := by
    have h2 : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n hu
    have h3 : (u + 1) * n = u * n + n := by ring
    have := v.isLt
    omega
  have h0 : Run B (.assign "em.c" (.lit 0)) τ (τ.setVar "em.c" 0) 2 :=
    run_assign' (evB_lit' (by omega)) (by simp)
  have h0a : (τ.setVar "em.c" 0).arrs = τ.arrs := by simp
  have h0u : (τ.setVar "em.c" 0).vars "em.u" = u := by simp [hus]
  have h0v : (τ.setVar "em.c" 0).vars "em.v" = (v : ℕ) := by simp [hvv]
  have h0v1 : (τ.setVar "em.c" 0).vars "em.v1" = (v : ℕ) + 1 := by simp [hv1]
  have h0r : (τ.setVar "em.c" 0).vars "em.r" = rk v := by simp [hrr]
  have h0n : (τ.setVar "em.c" 0).vars nN = n := by simp [hnc, hcar]
  -- the two stamps
  have hstamp : ∀ (a : String), n ≤ (τ.arrs a).length →
      (∀ q, q < n → (τ.arrs a).getD q 0 ≤ (v : ℕ) + 1) →
      ((Cond.lt (.get a (.var "em.u")) (.var "em.v1")).evalB B (τ.setVar "em.c" 0)
        = some (decide ((τ.arrs a).getD u 0 < (v : ℕ) + 1))) := by
    intro a haL haLt
    refine evalB_condLt (evB_get' (evB_var' h0u (by omega)) ?_ ?_) (evB_var' h0v1 hvB)
    · rw [h0a]; exact getElem?_of_lt' _ _ (by omega)
    · have := haLt u hu; omega
  have hmeaning : ∀ (a : String) (P : Fin n → Prop),
      (∀ q, q < n → (τ.arrs a).getD q 0 ≤ (v : ℕ) + 1) →
      (∀ w : Fin n, (τ.arrs a).getD (w : ℕ) 0 = (v : ℕ) + 1 ↔ P w) →
      ((τ.arrs a).getD u 0 < (v : ℕ) + 1 ↔ ¬ P ⟨u, hu⟩) := by
    intro a P haLt haEq
    have h1 : (τ.arrs a).getD u 0 ≤ (v : ℕ) + 1 := haLt u hu
    have h2 : (τ.arrs a).getD u 0 = (v : ℕ) + 1 ↔ P ⟨u, hu⟩ := haEq ⟨u, hu⟩
    constructor
    · intro h hc; rw [h2.2 hc] at h; omega
    · intro h
      rcases Nat.lt_or_ge ((τ.arrs a).getD u 0) ((v : ℕ) + 1) with h' | h'
      · exact h'
      · exact absurd (h2.1 (by omega)) h
  have hsdc := hstamp sd hsdL hsdLt
  have hadc := hstamp ad hadL hadLt
  have hsdm := hmeaning sd (fun w => (fratGraph D).Adj w v) hsdLt hsdEq
  have hadm := hmeaning ad (fun w => D.Adjacent w v) hadLt hadEq
  by_cases hF : (fratGraph D).Adj ⟨u, hu⟩ v
  · have hkeep : emKeepT D rk v u = false := by
      by_contra hc
      exact ((emKeepT_iff hu).1 (by simpa using hc)).1 hF
    rw [hkeep]
    exact (h0.seq (Run.ite_false
      (by rw [hsdc, decide_eq_false (fun h => (hsdm.1 h) hF)]) Run.skip)).mono
      (by simp)
  · have hsdtrue : (Cond.lt (.get sd (.var "em.u")) (.var "em.v1")).evalB B
        (τ.setVar "em.c" 0) = some true := by
      rw [hsdc, decide_eq_true (hsdm.2 hF)]
    by_cases hA : D.Adjacent ⟨u, hu⟩ v
    · have hkeep : emKeepT D rk v u = false := by
        by_contra hc
        exact ((emKeepT_iff hu).1 (by simpa using hc)).2.1 hA
      rw [hkeep]
      exact (h0.seq (Run.ite_true hsdtrue (Run.ite_false
        (by rw [hadc, decide_eq_false (fun h => (hadm.1 h) hA)]) Run.skip))).mono
        (by simp)
    · have hadtrue : (Cond.lt (.get ad (.var "em.u")) (.var "em.v1")).evalB B
          (τ.setVar "em.c" 0) = some true := by
        rw [hadc, decide_eq_true (hadm.2 hA)]
      have hsgget : ((τ.setVar "em.c" 0).arrs sg)[u]? = some (rk ⟨u, hu⟩) := by
        rw [h0a]; exact hsgGet ⟨u, hu⟩
      have hcond3 : (Cond.lt (.get sg (.var "em.u")) (.var "em.r")).evalB B
          (τ.setVar "em.c" 0) = some (decide (rk ⟨u, hu⟩ < rk v)) :=
        evalB_condLt (evB_get' (evB_var' h0u (by omega)) hsgget (hrkB _))
          (evB_var' h0r (hrkB v))
      have hset : Run B (.assign "em.c" (.lit 1)) (τ.setVar "em.c" 0)
          (τ.setVar "em.c" 1) 2 := by
        have := run_assign' (B := B) (x := "em.c") (e := .lit 1)
          (σ := τ.setVar "em.c" 0) (c := 1) (K := 2) (evB_lit' (by omega)) (by simp)
        rwa [setVar_setVar_self] at this
      by_cases hlt : rk ⟨u, hu⟩ < rk v
      · have hkeep : emKeepT D rk v u = true := (emKeepT_iff hu).2 ⟨hF, hA, Or.inl hlt⟩
        rw [hkeep, if_pos rfl]
        exact (h0.seq (Run.ite_true hsdtrue (Run.ite_true hadtrue
          (Run.ite_true (by rw [hcond3, decide_eq_true hlt]) hset)))).mono
          (by simp)
      · -- the forced transitive direction: one matrix read
        have hmku : (τ.arrs mk).getD (u * n + (v : ℕ)) 0
            = if TransLink D v ⟨u, hu⟩ then 1 else 0 := hmk ⟨u, hu⟩
        have hmkget : ((τ.setVar "em.c" 0).arrs mk)[u * n + (v : ℕ)]?
            = some ((τ.arrs mk).getD (u * n + (v : ℕ)) 0) := by
          rw [h0a]; exact getElem?_of_lt' _ _ (by omega)
        have hmkB : (τ.arrs mk).getD (u * n + (v : ℕ)) 0 < B := by
          rw [hmku]; by_cases hc : TransLink D v ⟨u, hu⟩ <;> simp [hc] <;> omega
        have hcond4 : (Cond.lt (.get mk (.add (.mul (.var "em.u") (.var nN))
              (.var "em.v"))) (.lit 1)).evalB B (τ.setVar "em.c" 0)
            = some (decide ((τ.arrs mk).getD (u * n + (v : ℕ)) 0 < 1)) :=
          evalB_condLt (evB_get'
            (evB_add' (evB_mul' (evB_var' h0u (by omega)) (evB_var' h0n (by omega))
              (by omega)) (evB_var' h0v (by omega)) (by omega)) hmkget hmkB)
            (evB_lit' (by omega))
        by_cases hT : TransLink D v ⟨u, hu⟩
        · have hkeep : emKeepT D rk v u = false := by
            by_contra hc
            rcases ((emKeepT_iff hu).1 (by simpa using hc)).2.2 with h | h
            · exact hlt h
            · exact h hT
          rw [hkeep]
          refine (h0.seq (Run.ite_true hsdtrue (Run.ite_true hadtrue
            (Run.ite_false (by rw [hcond3, decide_eq_false hlt])
              (Run.ite_false ?_ Run.skip))))).mono (by simp)
          rw [hcond4, decide_eq_false (by rw [hmku, if_pos hT]; omega)]
        · have hkeep : emKeepT D rk v u = true :=
            (emKeepT_iff hu).2 ⟨hF, hA, Or.inr hT⟩
          rw [hkeep, if_pos rfl]
          refine (h0.seq (Run.ite_true hsdtrue (Run.ite_true hadtrue
            (Run.ite_false (by rw [hcond3, decide_eq_false hlt])
              (Run.ite_true ?_ hset))))).mono (by simp)
          rw [hcond4, decide_eq_true (by rw [hmku, if_neg hT]; omega)]

/-! ## §6 The head's turn

One head: anchor the output offset, load the stamp value and the rank,
run the four scans, advance.  `EmHeadSt` is what the outer loop carries
across heads — the five input regions, the four allocations, the write
pointer at `emOff E v`, the offsets written so far, and the two stamps
still below `v`. -/

theorem OutCsrAt.of_eq {qo qt : String} {n : ℕ} {D : Orientation n} {otF : ℕ → ℕ}
    {σ : Env} (h : OutCsrAt qo qt D otF σ) {σ' : Env}
    (ho : σ'.arrs qo = σ.arrs qo) (ht : σ'.arrs qt = σ.arrs qt) :
    OutCsrAt qo qt D otF σ' :=
  { h with
    qoLen := by rw [ho]; exact h.qoLen
    qtLen := by rw [ht]; exact h.qtLen
    qoGet := by rw [ho]; exact h.qoGet
    qtGet := by rw [ht]; exact h.qtGet }

theorem TransCsrAt.of_eq {ro rt mk : String} {n : ℕ} {D : Orientation n} {ttF : ℕ → ℕ}
    {σ : Env} (h : TransCsrAt ro rt mk D ttF σ) {σ' : Env}
    (ho : σ'.arrs ro = σ.arrs ro) (ht : σ'.arrs rt = σ.arrs rt)
    (hm : σ'.arrs mk = σ.arrs mk) : TransCsrAt ro rt mk D ttF σ' :=
  { h with
    toLen := by rw [ho]; exact h.toLen
    ttLen := by rw [ht]; exact h.ttLen
    markLen := by rw [hm]; exact h.markLen
    toGet := by rw [ho]; exact h.toGet
    ttGet := by rw [ht]; exact h.ttGet
    markOne := by rw [hm]; exact h.markOne
    markZero := by rw [hm]; exact h.markZero }

theorem RankAt.of_eq {sg : String} {n : ℕ} {rk : Fin n → ℕ} {σ : Env}
    (h : RankAt sg rk σ) {σ' : Env} (hs : σ'.arrs sg = σ.arrs sg) :
    RankAt sg rk σ' := by rw [RankAt, hs]; exact h

/-- The arrays the pass writes. -/
def emWr (o' t' qo qt ad sd dg : String) : List String := [o', t', qo, qt, ad, sd, dg]

/-- The arrays the pass reads. -/
def emRd (o t ro rt mk fo ft sg : String) : List String := [o, t, ro, rt, mk, fo, ft, sg]

/-- **The names the pass keeps apart**: no array it writes is one it
reads, the seven it writes are distinct, and the fraternity CSR's two
regions are distinct — the last because `CsrPrefix` cuts two different
`winA` windows out of them (Finding 2). -/
structure EmNames (o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String) : Prop where
  /-- A written region is never a read one. -/
  wrRd : ∀ a ∈ emWr o' t' qo qt ad sd dg, ∀ b ∈ emRd o t ro rt mk fo ft sg, a ≠ b
  /-- The written regions are pairwise distinct. -/
  wrNd : (emWr o' t' qo qt ad sd dg).Nodup
  /-- The fraternity CSR's offsets are not its targets. -/
  fo_ft : fo ≠ ft

private theorem emNames_wr {o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String}
    (h : EmNames o t ro rt mk fo ft sg o' t' qo qt ad sd dg) :
    o' ≠ t' ∧ o' ≠ qo ∧ o' ≠ qt ∧ o' ≠ ad ∧ o' ≠ sd ∧ o' ≠ dg ∧
      t' ≠ qo ∧ t' ≠ qt ∧ t' ≠ ad ∧ t' ≠ sd ∧ t' ≠ dg ∧
      qo ≠ qt ∧ qo ≠ ad ∧ qo ≠ sd ∧ qo ≠ dg ∧
      qt ≠ ad ∧ qt ≠ sd ∧ qt ≠ dg ∧ ad ≠ sd ∧ ad ≠ dg ∧ sd ≠ dg := by
  have hnd := h.wrNd
  simp only [emWr, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  tauto

/-- **What the outer scan carries across heads.** -/
private structure EmHeadSt (nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String)
    {n : ℕ} (D : Orientation n) (rk : Fin n → ℕ) (ns nf : ℕ)
    (off tgt otF fof ftf ttF : ℕ → ℕ) (E : ℕ → List ℕ) (k : ℕ) (σ : Env) : Prop where
  csr : TrInCsr o t D ns off tgt σ
  out : OutCsrAt qo qt D otF σ
  frat : CsrRows fo ft (fratGraph D) nf fof ftf σ
  tr : TransCsrAt ro rt mk D ttF σ
  rank : RankAt sg rk σ
  carrier : σ.vars nN = n
  oLen : n + 1 ≤ (σ.arrs o').length
  tLen : emNs n E ≤ (σ.arrs t').length
  adLen : n ≤ (σ.arrs ad).length
  sdLen : n ≤ (σ.arrs sd).length
  dgLen : n ≤ (σ.arrs dg).length
  vv : σ.vars "em.v" = k
  vle : k ≤ n
  ptr : σ.vars "em.p" = emOff E k
  offs : ∀ i, i < k → (σ.arrs o').getD i 0 = emOff E i
  tgts : ∀ q, q < σ.vars "em.p" → (σ.arrs t').getD q 0 = (emPref E n).getD q 0
  adSt : ∀ q, q < n → (σ.arrs ad).getD q 0 ≤ k
  sdSt : ∀ q, q < n → (σ.arrs sd).getD q 0 ≤ k

/-- **The head's turn**: the offset anchor, the two scalars, the four
scans and the advance. -/
def emHead (nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String) : Com :=
  .seq (.store o' (.var "em.v") (.var "em.p"))
    (.seq (.assign "em.v1" (.add (.var "em.v") (.lit 1)))
      (.seq (.assign "em.r" (.get sg (.var "em.v")))
        (.seq (emRowScan o t ad t' emCndIn)
          (.seq (emRowScan qo qt ad t' emCndOut)
            (.seq (emRowScan fo ft sd t' (emCndFrat ad sg))
              (.seq (emRowScan ro rt dg t' (emCndTrans nN ad sd sg mk))
                (.assign "em.v" (.add (.var "em.v") (.lit 1)))))))))

set_option maxHeartbeats 1600000 in
/-- **One head's turn, discharged**: `62` fixed plus `27` a slot of the
input row, `27` of the transpose row, `39` a fraternal candidate and
`53` a transitive one. -/
private theorem emHead_run {B n : ℕ}
    {nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String}
    {D : Orientation n} {rk : Fin n → ℕ} {ns nf : ℕ}
    {off tgt otF fof ftf ttF : ℕ → ℕ} {E : ℕ → List ℕ} {σ : Env} {k : ℕ}
    (hnm : EmNames o t ro rt mk fo ft sg o' t' qo qt ad sd dg)
    (hnN : nN ∉ emScalars)
    (hE : E = emE D rk off tgt fof ftf ttF)
    (hnB : n < B) (hnnB : n * n < B) (hnsB : emNs n E < B)
    (hnsB' : ns < B) (harcB : arcCount D < B) (hnfB : nf < B)
    (htrB : trOff D n < B) (hrkB : ∀ w : Fin n, rk w < B)
    (hk : k < n) (hst : EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
      D rk ns nf off tgt otF fof ftf ttF E k σ) :
    ∃ σ' K', Run B (emHead nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg) σ σ' K' ∧
      EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
        D rk ns nf off tgt otF fof ftf ttF E (k + 1) σ' ∧
      K' ≤ 62 + 27 * (off (k + 1) - off k)
        + 27 * (outOff D (k + 1) - outOff D k) + 39 * (fof (k + 1) - fof k)
        + 53 * (trOff D (k + 1) - trOff D k) := by
  classical
  obtain ⟨hnv, hnv1, hnr, hnp, hnj, hne, hnu, hnc⟩ := emScalars_ne hnN
  obtain ⟨ho't', ho'qo, ho'qt, ho'ad, ho'sd, ho'dg, ht'qo, ht'qt, ht'ad, ht'sd,
    ht'dg, hqoqt, hqoad, hqosd, hqodg, hqtad, hqtsd, hqtdg, hadsd, haddg,
    hsddg⟩ := emNames_wr hnm
  have hRd : ∀ b ∈ emRd o t ro rt mk fo ft sg, ∀ a ∈ emWr o' t' qo qt ad sd dg, b ≠ a :=
    fun b hb a ha => (hnm.wrRd a ha b hb).symm
  have mo : o ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mt : t ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mro : ro ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mrt : rt ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mmk : mk ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mfo : fo ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mft : ft ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have msg : sg ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mo' : o' ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have mt' : t' ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have mad : ad ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have msd : sd ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have mdg : dg ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  obtain ⟨hcsr, hout, hfrat, htr, hrank, hcar, hoL, htL, hadL, hsdL, hdgL,
    hvv, hvle, hptr, hoffs, htgts, hadSt, hsdSt⟩ := hst
  have hEk : E k = Csr.row off tgt k
      ++ (Csr.row fof ftf k).filter (emKeepF D rk ⟨k, hk⟩)
      ++ (Csr.row (trOff D) ttF k).filter (emKeepT D rk ⟨k, hk⟩) := by
    rw [hE]; exact emE_lt hk
  have hoffk : emOff E k ≤ emNs n E := by
    rw [emNs, emOff, emOff]; exact length_flatPref_mono E (by omega)
  have hoffsucc : emOff E (k + 1) = emOff E k + (E k).length := emOff_succ E k
  -- `o'[em.v] := em.p`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setArr o' k (emOff E k) := ⟨_, rfl⟩
  have r1 : Run B (.store o' (.var "em.v") (.var "em.p")) σ σ1 3 := by
    rw [hσ1]
    exact run_store' (evB_var' hvv (by omega)) (evB_var' hptr (by omega))
      (by omega) (by simp)
  have h1a : ∀ b, b ≠ o' → σ1.arrs b = σ.arrs b := by
    intro b hb; rw [hσ1]; simp [hb]
  have h1o' : σ1.arrs o' = (σ.arrs o').set k (emOff E k) := by rw [hσ1]; simp
  have h1v : σ1.vars = σ.vars := by rw [hσ1]; simp
  -- `em.v1 := em.v + 1`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "em.v1" (k + 1) := ⟨_, rfl⟩
  have r2 : Run B (.assign "em.v1" (.add (.var "em.v") (.lit 1))) σ1 σ2 4 := by
    rw [hσ2]
    exact run_assign' (evB_add' (evB_var' (by rw [h1v]; exact hvv) (by omega))
      (evB_lit' (by omega)) (by omega)) (by simp)
  -- `em.r := sg[em.v]`
  have hsgget : (σ2.arrs sg)[k]? = some (rk ⟨k, hk⟩) := by
    rw [hσ2]; simp; rw [h1a sg (hRd sg msg o' mo')]; exact hrank.2 ⟨k, hk⟩
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setVar "em.r" (rk ⟨k, hk⟩) := ⟨_, rfl⟩
  have r3 : Run B (.assign "em.r" (.get sg (.var "em.v"))) σ2 σ3 3 := by
    rw [hσ3]
    refine run_assign' (evB_get' (evB_var' ?_ (by omega)) hsgget (hrkB _)) (by simp)
    rw [hσ2]; simp; rw [h1v]; exact hvv
  have h3a : ∀ b, b ≠ o' → σ3.arrs b = σ.arrs b := by
    intro b hb; rw [hσ3, hσ2]; simp; exact h1a b hb
  have h3o' : σ3.arrs o' = (σ.arrs o').set k (emOff E k) := by
    rw [hσ3, hσ2]; simp; exact h1o'
  have h3v : σ3.vars "em.v" = k := by rw [hσ3, hσ2]; simp [h1v, hvv]
  have h3v1 : σ3.vars "em.v1" = k + 1 := by rw [hσ3, hσ2]; simp
  have h3r : σ3.vars "em.r" = rk ⟨k, hk⟩ := by rw [hσ3]; simp
  have h3n : σ3.vars nN = n := by rw [hσ3, hσ2]; simp [hnr, hnv1, h1v, hcar]
  have h3p : σ3.vars "em.p" = emOff E k := by rw [hσ3, hσ2]; simp [h1v, hptr]
  -- scan 1: the input row
  obtain ⟨σ4, K1, hr4, hK1, ha4, ht4l, hA4l, hn4, hv4, hv14, hr4r, hp4, ht4, had4⟩ :=
    emRowScan_run (so := o) (st := t) (A := ad) (t' := t') (nN := nN)
      (sof := off) (stf := tgt) (ext := ns) (keep := fun _ => true) (cnd := emCndIn)
      (Kc := 2) (E := E) (v := k) (R := rk ⟨k, hk⟩) (base := []) (σ := σ3)
      hnN (Ne.symm ht'ad) (hRd t mt t' mt') (hRd t mt ad mad) hnB hnsB' hnsB
      (fun i hi => by rw [h3a o (hRd o mo o' mo')]; exact hcsr.offGet i hi)
      (fun q hq => by rw [h3a t (hRd t mt o' mo')]; exact hcsr.tgtGet q hq)
      (fun q hq => hcsr.tgtLt q hq)
      (by rw [h3a ad (Ne.symm ho'ad)]; exact hadL)
      (by rw [h3a t' (Ne.symm ho't')]; exact htL)
      hk (by
        have hs : off (k + 1) = off k + (D.inN (⟨k, hk⟩ : Fin n)).card :=
          hcsr.step ⟨k, hk⟩
        omega)
      (hcsr.off_le_ns (show k + 1 ≤ n by omega))
      (by
        simp only [List.nil_append, List.filter_true]
        rw [hEk]
        exact ⟨_, (List.append_assoc _ _ _).symm⟩)
      (fun τ u _ _ _ _ _ _ _ => by simpa using emCndIn_run (B := B) (τ := τ) (by omega))
      h3n h3v h3v1 h3r (by rw [h3p]; simp)
      (fun q hq => by
        rw [h3a t' (Ne.symm ho't')]
        exact htgts q (by rw [hptr]; rw [h3p] at hq; exact hq))
  have hp4' : σ4.vars "em.p" = emOff E k + (Csr.row off tgt k).length := by simpa using hp4
  -- scan 2: the transpose row
  obtain ⟨σ5, K2, hr5, hK2, ha5, ht5l, hA5l, hn5, hv5, hv15, hr5r, hp5, ht5, had5⟩ :=
    emRowScan_run (so := qo) (st := qt) (A := ad) (t' := t') (nN := nN)
      (sof := outOff D) (stf := otF) (ext := arcCount D) (keep := fun _ => false)
      (cnd := emCndOut) (Kc := 2) (E := E) (v := k) (R := rk ⟨k, hk⟩)
      (base := Csr.row off tgt k) (σ := σ4)
      hnN (Ne.symm ht'ad) (Ne.symm ht'qt) hqtad hnB harcB hnsB
      (fun i hi => by
        rw [ha4 qo (Ne.symm ht'qo) hqoad, h3a qo (Ne.symm ho'qo)]
        exact hout.qoGet i hi)
      (fun q hq => by
        rw [ha4 qt (Ne.symm ht'qt) hqtad, h3a qt (Ne.symm ho'qt)]
        exact hout.qtGet q hq)
      (fun q hq => hout.qtLt q hq)
      (by rw [hA4l, h3a ad (Ne.symm ho'ad)]; exact hadL)
      (by rw [ht4l, h3a t' (Ne.symm ho't')]; exact htL)
      hk (outOff_le_succ D k) (outOff_le_arcCount D (by omega))
      (by
        simp only [List.filter_false, List.append_nil]
        rw [hEk]
        exact ⟨_, (List.append_assoc _ _ _).symm⟩)
      (fun τ u _ _ _ _ _ _ _ => by simpa using emCndOut_run (B := B) (τ := τ) (by omega))
      hn4 hv4 hv14 hr4r hp4' ht4
  have hp5' : σ5.vars "em.p" = emOff E k + (Csr.row off tgt k).length := by simpa using hp5
  -- what the two stamping scans left in `ad`
  have hadC : ∀ q, q < n → (σ5.arrs ad).getD q 0
      = if q ∈ Csr.row (outOff D) otF k ∨ q ∈ Csr.row off tgt k then k + 1
        else (σ.arrs ad).getD q 0 := by
    intro q hq
    rw [had5 q hq, had4 q hq, h3a ad (Ne.symm ho'ad)]
    by_cases h1 : q ∈ Csr.row (outOff D) otF k
    · rw [if_pos h1, if_pos (Or.inl h1)]
    · rw [if_neg h1]
      by_cases h2 : q ∈ Csr.row off tgt k
      · rw [if_pos h2, if_pos (Or.inr h2)]
      · rw [if_neg h2, if_neg (by tauto)]
  have hadLt5 : ∀ q, q < n → (σ5.arrs ad).getD q 0 ≤ k + 1 := by
    intro q hq
    rw [hadC q hq]
    by_cases h : q ∈ Csr.row (outOff D) otF k ∨ q ∈ Csr.row off tgt k
    · rw [if_pos h]
    · rw [if_neg h]; have := hadSt q hq; omega
  have hadEq5 : ∀ w : Fin n, (σ5.arrs ad).getD (w : ℕ) 0 = k + 1
      ↔ D.Adjacent w ⟨k, hk⟩ := by
    intro w
    rw [hadC (w : ℕ) w.isLt]
    have hI := hcsr.row_mem ⟨k, hk⟩ (w : ℕ)
    have hO := hout.row_mem ⟨k, hk⟩ (w : ℕ)
    have hIw : (w : ℕ) ∈ Csr.row off tgt k ↔ w ∈ D.inN ⟨k, hk⟩ := by
      rw [hI]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨w.isLt, h⟩⟩
    have hOw : (w : ℕ) ∈ Csr.row (outOff D) otF k ↔ (⟨k, hk⟩ : Fin n) ∈ D.inN w := by
      rw [hO]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨w.isLt, h⟩⟩
    by_cases h : (w : ℕ) ∈ Csr.row (outOff D) otF k ∨ (w : ℕ) ∈ Csr.row off tgt k
    · rw [if_pos h]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      rcases h with h | h
      · exact Or.inr (hOw.1 h)
      · exact Or.inl (hIw.1 h)
    · rw [if_neg h]
      have hle := hadSt (w : ℕ) w.isLt
      refine ⟨fun hc => absurd hc (by omega), fun hc => ?_⟩
      refine absurd ?_ h
      rcases hc with hc | hc
      · exact Or.inr (hIw.2 hc)
      · exact Or.inl (hOw.2 hc)
  -- scan 3: the fraternal row
  have hsd5 : σ5.arrs sd = σ.arrs sd := by
    rw [ha5 sd (Ne.symm ht'sd) (Ne.symm hadsd), ha4 sd (Ne.symm ht'sd) (Ne.symm hadsd),
      h3a sd (Ne.symm ho'sd)]
  obtain ⟨σ6, K3, hr6, hK3, ha6, ht6l, hA6l, hn6, hv6, hv16, hr6r, hp6, ht6, hsd6⟩ :=
    emRowScan_run (so := fo) (st := ft) (A := sd) (t' := t') (nN := nN)
      (sof := fof) (stf := ftf) (ext := nf) (keep := emKeepF D rk ⟨k, hk⟩)
      (cnd := emCndFrat ad sg) (Kc := 14) (E := E) (v := k) (R := rk ⟨k, hk⟩)
      (base := Csr.row off tgt k) (σ := σ5)
      hnN (Ne.symm ht'sd) (hRd ft mft t' mt') (hRd ft mft sd msd) hnB hnfB hnsB
      (fun i hi => by
        rw [ha5 fo (hRd fo mfo t' mt') (hRd fo mfo ad mad),
          ha4 fo (hRd fo mfo t' mt') (hRd fo mfo ad mad),
          h3a fo (hRd fo mfo o' mo')]
        exact hfrat.offGet i hi)
      (fun q hq => by
        rw [ha5 ft (hRd ft mft t' mt') (hRd ft mft ad mad),
          ha4 ft (hRd ft mft t' mt') (hRd ft mft ad mad),
          h3a ft (hRd ft mft o' mo')]
        exact hfrat.tgtGet q hq)
      (fun q hq => hfrat.tgtLt q hq)
      (by rw [hsd5]; exact hsdL)
      (by rw [ht5l, ht4l, h3a t' (Ne.symm ho't')]; exact htL)
      hk (hfrat.mono k hk) (hfrat.off_le_ns (k + 1) (by omega))
      (by rw [hEk]; exact ⟨_, rfl⟩)
      (fun τ u hu hus hvτ hv1τ hrτ hnτ hagree => by
        refine emCndFrat_run (D := D) (rk := rk) (v := ⟨k, hk⟩) hu hnB hrkB hus hv1τ
          hrτ ?_ ?_ ?_ ?_
        · rw [hagree ad (Ne.symm ht'ad) hadsd, hA5l, hA4l, h3a ad (Ne.symm ho'ad)]
          exact hadL
        · rw [hagree ad (Ne.symm ht'ad) hadsd]; exact hadLt5
        · rw [hagree ad (Ne.symm ht'ad) hadsd]; exact hadEq5
        · rw [hagree sg (hRd sg msg t' mt') (hRd sg msg sd msd),
            ha5 sg (hRd sg msg t' mt') (hRd sg msg ad mad),
            ha4 sg (hRd sg msg t' mt') (hRd sg msg ad mad),
            h3a sg (hRd sg msg o' mo')]
          exact hrank.2)
      hn5 hv5 hv15 hr5r hp5' ht5
  -- scan 4: the transitive row
  have had6 : σ6.arrs ad = σ5.arrs ad := ha6 ad (Ne.symm ht'ad) hadsd
  have hsdC : ∀ q, q < n → (σ6.arrs sd).getD q 0
      = if q ∈ Csr.row fof ftf k then k + 1 else (σ.arrs sd).getD q 0 := by
    intro q hq; rw [hsd6 q hq, hsd5]
  have hsdLt6 : ∀ q, q < n → (σ6.arrs sd).getD q 0 ≤ k + 1 := by
    intro q hq
    rw [hsdC q hq]
    by_cases h : q ∈ Csr.row fof ftf k
    · rw [if_pos h]
    · rw [if_neg h]; have := hsdSt q hq; omega
  have hsdEq6 : ∀ w : Fin n, (σ6.arrs sd).getD (w : ℕ) 0 = k + 1
      ↔ (fratGraph D).Adj w ⟨k, hk⟩ := by
    intro w
    rw [hsdC (w : ℕ) w.isLt]
    have hFw : (w : ℕ) ∈ Csr.row fof ftf k ↔ (fratGraph D).Adj w ⟨k, hk⟩ := by
      rw [hfrat.mem ⟨k, hk⟩ (w : ℕ)]
      exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨w.isLt, h.symm⟩⟩
    by_cases h : (w : ℕ) ∈ Csr.row fof ftf k
    · rw [if_pos h]; exact ⟨fun _ => hFw.1 h, fun _ => rfl⟩
    · rw [if_neg h]
      have := hsdSt (w : ℕ) w.isLt
      exact ⟨fun hc => absurd hc (by omega), fun hc => absurd (hFw.2 hc) h⟩
  obtain ⟨σ7, K4, hr7, hK4, ha7, ht7l, hA7l, hn7, hv7, hv17, hr7r, hp7, ht7, -⟩ :=
    emRowScan_run (so := ro) (st := rt) (A := dg) (t' := t') (nN := nN)
      (sof := trOff D) (stf := ttF) (ext := trOff D n)
      (keep := emKeepT D rk ⟨k, hk⟩) (cnd := emCndTrans nN ad sd sg mk) (Kc := 28)
      (E := E) (v := k) (R := rk ⟨k, hk⟩)
      (base := Csr.row off tgt k ++ (Csr.row fof ftf k).filter (emKeepF D rk ⟨k, hk⟩))
      (σ := σ6)
      hnN (Ne.symm ht'dg) (hRd rt mrt t' mt') (hRd rt mrt dg mdg) hnB htrB hnsB
      (fun i hi => by
        rw [ha6 ro (hRd ro mro t' mt') (hRd ro mro sd msd),
          ha5 ro (hRd ro mro t' mt') (hRd ro mro ad mad),
          ha4 ro (hRd ro mro t' mt') (hRd ro mro ad mad),
          h3a ro (hRd ro mro o' mo')]
        exact htr.toGet i hi)
      (fun q hq => by
        rw [ha6 rt (hRd rt mrt t' mt') (hRd rt mrt sd msd),
          ha5 rt (hRd rt mrt t' mt') (hRd rt mrt ad mad),
          ha4 rt (hRd rt mrt t' mt') (hRd rt mrt ad mad),
          h3a rt (hRd rt mrt o' mo')]
        exact htr.ttGet q hq)
      (fun q hq => htr.ttLt q hq)
      (by
        rw [ha6 dg (Ne.symm ht'dg) (Ne.symm hsddg), ha5 dg (Ne.symm ht'dg) (Ne.symm haddg),
          ha4 dg (Ne.symm ht'dg) (Ne.symm haddg), h3a dg (Ne.symm ho'dg)]
        exact hdgL)
      (by rw [ht6l, ht5l, ht4l, h3a t' (Ne.symm ho't')]; exact htL)
      hk (trOff_mono D (by omega)) (trOff_mono D (by omega))
      (by rw [hEk])
      (fun τ u hu hus hvτ hv1τ hrτ hnτ hagree => by
        refine emCndTrans_run (D := D) (rk := rk) (v := ⟨k, hk⟩) hu hnB hnnB hrkB hus
          hvτ hv1τ hrτ hnτ hnc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hagree ad (Ne.symm ht'ad) haddg, had6, hA5l, hA4l,
            h3a ad (Ne.symm ho'ad)]
          exact hadL
        · rw [hagree ad (Ne.symm ht'ad) haddg, had6]; exact hadLt5
        · rw [hagree ad (Ne.symm ht'ad) haddg, had6]; exact hadEq5
        · rw [hagree sd (Ne.symm ht'sd) hsddg, hA6l, hsd5]; exact hsdL
        · rw [hagree sd (Ne.symm ht'sd) hsddg]; exact hsdLt6
        · rw [hagree sd (Ne.symm ht'sd) hsddg]; exact hsdEq6
        · rw [hagree sg (hRd sg msg t' mt') (hRd sg msg dg mdg),
            ha6 sg (hRd sg msg t' mt') (hRd sg msg sd msd),
            ha5 sg (hRd sg msg t' mt') (hRd sg msg ad mad),
            ha4 sg (hRd sg msg t' mt') (hRd sg msg ad mad),
            h3a sg (hRd sg msg o' mo')]
          exact hrank.2
        · rw [hagree mk (hRd mk mmk t' mt') (hRd mk mmk dg mdg),
            ha6 mk (hRd mk mmk t' mt') (hRd mk mmk sd msd),
            ha5 mk (hRd mk mmk t' mt') (hRd mk mmk ad mad),
            ha4 mk (hRd mk mmk t' mt') (hRd mk mmk ad mad),
            h3a mk (hRd mk mmk o' mo')]
          exact htr.markLen
        · intro w
          rw [hagree mk (hRd mk mmk t' mt') (hRd mk mmk dg mdg),
            ha6 mk (hRd mk mmk t' mt') (hRd mk mmk sd msd),
            ha5 mk (hRd mk mmk t' mt') (hRd mk mmk ad mad),
            ha4 mk (hRd mk mmk t' mt') (hRd mk mmk ad mad),
            h3a mk (hRd mk mmk o' mo')]
          by_cases hc : TransLink D ⟨k, hk⟩ w
          · rw [if_pos hc]; exact htr.markOne w ⟨k, hk⟩ hc
          · rw [if_neg hc]; exact htr.markZero w ⟨k, hk⟩ hc)
      hn6 hv6 hv16 hr6r hp6 ht6
  -- `em.v := em.v + 1`
  obtain ⟨σ8, hσ8⟩ : ∃ τ, τ = σ7.setVar "em.v" (k + 1) := ⟨_, rfl⟩
  have r8 : Run B (.assign "em.v" (.add (.var "em.v") (.lit 1))) σ7 σ8 4 := by
    rw [hσ8]
    exact run_assign' (evB_add' (evB_var' hv7 (by omega)) (evB_lit' (by omega))
      (by omega)) (by simp)
  -- the final state, region by region
  have h8a : ∀ b, b ≠ o' → b ≠ t' → b ≠ ad → b ≠ sd → b ≠ dg → σ8.arrs b = σ.arrs b := by
    intro b h1 h2 h3 h4 h5
    rw [hσ8]; simp
    rw [ha7 b h2 h5, ha6 b h2 h4, ha5 b h2 h3, ha4 b h2 h3, h3a b h1]
  have h8o' : σ8.arrs o' = (σ.arrs o').set k (emOff E k) := by
    rw [hσ8]; simp
    rw [ha7 o' ho't' ho'dg, ha6 o' ho't' ho'sd, ha5 o' ho't' ho'ad,
      ha4 o' ho't' ho'ad]
    exact h3o'
  have h8arr : σ8.arrs = σ7.arrs := by rw [hσ8]; simp
  have had8 : σ8.arrs ad = σ5.arrs ad := by
    rw [h8arr, ha7 ad (Ne.symm ht'ad) haddg, ha6 ad (Ne.symm ht'ad) hadsd]
  have hsd8 : σ8.arrs sd = σ6.arrs sd := by
    rw [h8arr, ha7 sd (Ne.symm ht'sd) hsddg]
  have hpsucc : emOff E k
      + ((Csr.row off tgt k ++ (Csr.row fof ftf k).filter (emKeepF D rk ⟨k, hk⟩))
        ++ (Csr.row (trOff D) ttF k).filter (emKeepT D rk ⟨k, hk⟩)).length
      = emOff E (k + 1) := by
    rw [hoffsucc, hEk]
  refine ⟨σ8, 3 + (4 + (3 + (K1 + (K2 + (K3 + (K4 + 4)))))),
    r1.seq (r2.seq (r3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq r8)))))), ?_, ?_⟩
  · refine
      { csr := hcsr.of_eq (h8a o (hRd o mo o' mo') (hRd o mo t' mt') (hRd o mo ad mad)
            (hRd o mo sd msd) (hRd o mo dg mdg))
          (h8a t (hRd t mt o' mo') (hRd t mt t' mt') (hRd t mt ad mad)
            (hRd t mt sd msd) (hRd t mt dg mdg))
        out := hout.of_eq
          (h8a qo (Ne.symm ho'qo) (Ne.symm ht'qo) hqoad hqosd hqodg)
          (h8a qt (Ne.symm ho'qt) (Ne.symm ht'qt) hqtad hqtsd hqtdg)
        frat := hfrat.of_eq
          (h8a fo (hRd fo mfo o' mo') (hRd fo mfo t' mt') (hRd fo mfo ad mad)
            (hRd fo mfo sd msd) (hRd fo mfo dg mdg))
          (h8a ft (hRd ft mft o' mo') (hRd ft mft t' mt') (hRd ft mft ad mad)
            (hRd ft mft sd msd) (hRd ft mft dg mdg))
        tr := htr.of_eq
          (h8a ro (hRd ro mro o' mo') (hRd ro mro t' mt') (hRd ro mro ad mad)
            (hRd ro mro sd msd) (hRd ro mro dg mdg))
          (h8a rt (hRd rt mrt o' mo') (hRd rt mrt t' mt') (hRd rt mrt ad mad)
            (hRd rt mrt sd msd) (hRd rt mrt dg mdg))
          (h8a mk (hRd mk mmk o' mo') (hRd mk mmk t' mt') (hRd mk mmk ad mad)
            (hRd mk mmk sd msd) (hRd mk mmk dg mdg))
        rank := hrank.of_eq
          (h8a sg (hRd sg msg o' mo') (hRd sg msg t' mt') (hRd sg msg ad mad)
            (hRd sg msg sd msd) (hRd sg msg dg mdg))
        carrier := by rw [hσ8]; simp [hnv, hn7]
        oLen := by rw [h8o', List.length_set]; exact hoL
        tLen := ?_
        adLen := ?_
        sdLen := ?_
        dgLen := ?_
        vv := by rw [hσ8]; simp
        vle := hk
        ptr := ?_
        offs := ?_
        tgts := ?_
        adSt := ?_
        sdSt := ?_ }
    · rw [h8arr, ht7l, ht6l, ht5l, ht4l, h3a t' (Ne.symm ho't')]; exact htL
    · rw [had8, hA5l, hA4l, h3a ad (Ne.symm ho'ad)]; exact hadL
    · rw [hsd8, hA6l, hsd5]; exact hsdL
    · rw [h8arr, hA7l, ha6 dg (Ne.symm ht'dg) (Ne.symm hsddg),
        ha5 dg (Ne.symm ht'dg) (Ne.symm haddg), ha4 dg (Ne.symm ht'dg) (Ne.symm haddg),
        h3a dg (Ne.symm ho'dg)]
      exact hdgL
    · have h8p : σ8.vars "em.p" = σ7.vars "em.p" := by rw [hσ8]; simp
      rw [h8p, hp7, hpsucc]
    · intro i hi
      rw [h8o']
      rcases Nat.lt_or_ge i k with h | h
      · rw [getD_set_of_ne (by omega)]; exact hoffs i h
      · obtain rfl : i = k := by omega
        exact getD_set_self (by omega)
    · intro q hq
      have h8p : σ8.vars "em.p" = σ7.vars "em.p" := by rw [hσ8]; simp
      rw [h8arr]
      exact ht7 q (by rw [← h8p]; exact hq)
    · intro q hq; rw [had8]; exact hadLt5 q hq
    · intro q hq; rw [hsd8]; exact hsdLt6 q hq
  · omega

/-! ## §7 The loop, the pass, and `StepEmitIn`

The heads in increasing order, then the last offset and the slot count.
The loop's cost is amortized against the four figures at once — one
potential with a term per region — because a head's turn is long exactly
where its four rows are. -/

/-- **The emit loop**: zero the write pointer, run the heads, close the
offsets, publish the slot count. -/
def emLoopCom (nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String) : Com :=
  .seq (.assign "em.p" (.lit 0))
    (.seq
      (.seq (.assign "em.v" (.lit 0))
        (Csr.scan "em.v" nN (emHead nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg)))
      (.seq (.store o' (.var nN) (.var "em.p")) (.assign nO (.var "em.p"))))

/-- **The whole pass**: the transpose (`SolveAugEmitCom`'s `tpCom`),
then the emit loop. -/
def emCom (nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String) : Com :=
  .seq (tpCom nN o t qo qt dg)
    (emLoopCom nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg)

/-- **The pass's cost**: `41·n + 40·a` of transpose, `66` a vertex of
loop header, `27` a slot of each of the two arc-length rows, `39` a
fraternal candidate and `53` a transitive one, plus `43` fixed. -/
def emComK (n a f T : ℕ) : ℕ := 107 * n + 94 * a + 39 * f + 53 * T + 43

/-- **The pass fits `SolveAugEmit`'s pinned budget**, with room in every
term: the transpose was priced at `41·n + 40·a` of `emK`, and the loop
spends `66·n + 54·a + 39·f + 53·T + 13` of the `259·n + 260·a + 200·f +
240·T + 50` it left. -/
theorem emComK_le_emK (n a f T : ℕ) : emComK n a f T ≤ emK n a f T := by
  simp only [emComK, emK]; omega

private theorem mem_warrs_tpCom {nN o t qo qt dg b : String}
    (h : b ∈ (tpCom nN o t qo qt dg).warrs) : b = qo ∨ b = qt ∨ b = dg := by
  simp only [tpCom, tpCntCom, tpOffCom, tpScatCom, tpScatOut, tpScatIn, Csr.scan,
    Com.warrs, List.append_assoc, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.nil_append] at h
  tauto

private theorem mem_wvars_tpCom {nN o t qo qt dg y : String}
    (h : y ∈ (tpCom nN o t qo qt dg).wvars) : y ∈ tpScalars := by
  simp only [tpCom, tpCntCom, tpOffCom, tpScatCom, tpScatOut, tpScatIn, Csr.scan,
    Com.wvars, List.append_assoc, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.nil_append] at h
  simp only [tpScalars, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem mem_warrs_emCom
    {nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg b : String}
    (h : b ∈ (emCom nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg).warrs) :
    b = o' ∨ b = t' ∨ b = qo ∨ b = qt ∨ b = ad ∨ b = sd ∨ b = dg := by
  simp only [emCom, emLoopCom, emHead, emRowScan, emStep, emCndIn, emCndOut,
    emCndFrat, emCndTrans, Csr.scan, Com.warrs, List.append_assoc, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.nil_append] at h
  rcases h with h | h
  · rcases mem_warrs_tpCom h with h | h | h <;> tauto
  · tauto

set_option maxHeartbeats 800000 in
/-- **The heads, in increasing order**: one potential with a term per
region, so a long head is paid for by the rows that made it long. -/
private theorem emHeads_run {B n : ℕ}
    {nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String}
    {D : Orientation n} {rk : Fin n → ℕ} {ns nf : ℕ}
    {off tgt otF fof ftf ttF : ℕ → ℕ} {E : ℕ → List ℕ} {σ : Env}
    (hnm : EmNames o t ro rt mk fo ft sg o' t' qo qt ad sd dg)
    (hnN : nN ∉ emScalars)
    (hE : E = emE D rk off tgt fof ftf ttF)
    (hnB : n < B) (hnnB : n * n < B) (hnsB : emNs n E < B)
    (hnsB' : ns < B) (harcB : arcCount D < B) (hnfB : nf < B)
    (htrB : trOff D n < B) (hrkB : ∀ w : Fin n, rk w < B)
    (hst : EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
      D rk ns nf off tgt otF fof ftf ttF E 0 σ) :
    ∃ σ' K', Run B (Csr.scan "em.v" nN
        (emHead nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg)) σ σ' K' ∧
      EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
        D rk ns nf off tgt otF fof ftf ttF E n σ' ∧
      K' ≤ 66 * n + 27 * ns + 27 * arcCount D + 39 * nf + 53 * trOff D n + 4 := by
  classical
  have hloop := Spec.while_potential (B := B) (b := .lt (.var "em.v") (.var nN))
    (c := emHead nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg)
    (P := fun τ => EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
      D rk ns nf off tgt otF fof ftf ttF E 0 τ)
    (K := 66 * n + 27 * ns + 27 * arcCount D + 39 * nf + 53 * trOff D n + 4)
    (fun τ => EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
      D rk ns nf off tgt otF fof ftf ttF E (τ.vars "em.v") τ)
    (fun τ => 66 * (n - τ.vars "em.v") + 27 * (ns - off (τ.vars "em.v"))
      + 27 * (arcCount D - outOff D (τ.vars "em.v")) + 39 * (nf - fof (τ.vars "em.v"))
      + 53 * (trOff D n - trOff D (τ.vars "em.v")))
    (fun τ hτ => evalB_condLt_vars (by have := hτ.vle; omega)
      (by have := hτ.carrier; omega))
    ?hstep ?hPI ?hK
  · obtain ⟨σ', hrun, hI', hfalse⟩ := hloop.run hst
    have hI'' : EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
        D rk ns nf off tgt otF fof ftf ttF E (σ'.vars "em.v") σ' := hI'
    have hle := le_of_condLt_false hfalse
    have hcar := hI''.carrier
    have hvle := hI''.vle
    have hend : σ'.vars "em.v" = n := by omega
    rw [hend] at hI''
    exact ⟨σ', _, hrun, hI'', le_rfl⟩
  · intro τ hτ hc
    have hk : τ.vars "em.v" < n := by
      have h1 := lt_of_condLt_true hc
      have h2 := hτ.carrier
      omega
    have hτ' : EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
        D rk ns nf off tgt otF fof ftf ttF E (τ.vars "em.v") τ := hτ
    obtain ⟨τ', K', hrun, hst', hK'⟩ :=
      emHead_run hnm hnN hE hnB hnnB hnsB hnsB' harcB hnfB htrB hrkB hk hτ'
    refine ⟨τ', K', hrun,
      show EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
        D rk ns nf off tgt otF fof ftf ttF E (τ'.vars "em.v") τ' by
        rw [hst'.vv]; exact hst', ?_⟩
    have hcsr := hτ'.csr
    have hout := hτ'.out
    have hfrat := hτ'.frat
    have hoff1 : off (τ.vars "em.v") ≤ off (τ.vars "em.v" + 1) := by
      have hs : off (τ.vars "em.v" + 1)
          = off (τ.vars "em.v") + (D.inN (⟨τ.vars "em.v", hk⟩ : Fin n)).card :=
        hcsr.step ⟨τ.vars "em.v", hk⟩
      omega
    have hoff2 : off (τ.vars "em.v" + 1) ≤ ns := hcsr.off_le_ns (show _ ≤ n by omega)
    have hout1 : outOff D (τ.vars "em.v") ≤ outOff D (τ.vars "em.v" + 1) :=
      outOff_le_succ D _
    have hout2 : outOff D (τ.vars "em.v" + 1) ≤ arcCount D :=
      outOff_le_arcCount D (by omega)
    have hfof1 : fof (τ.vars "em.v") ≤ fof (τ.vars "em.v" + 1) := hfrat.mono _ hk
    have hfof2 : fof (τ.vars "em.v" + 1) ≤ nf :=
      hfrat.off_le_ns _ (show _ ≤ n by omega)
    have htr1 : trOff D (τ.vars "em.v") ≤ trOff D (τ.vars "em.v" + 1) :=
      trOff_mono D (by omega)
    have htr2 : trOff D (τ.vars "em.v" + 1) ≤ trOff D n := trOff_mono D (by omega)
    simp only [size_condLt, size_var]
    rw [hst'.vv]
    omega
  · intro τ hτ
    show EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
      D rk ns nf off tgt otF fof ftf ttF E (τ.vars "em.v") τ
    rw [hτ.vv]
    exact hτ
  · intro τ hτ
    have h1 : off 0 = 0 := hτ.csr.zero
    have h2 : outOff D 0 = 0 := outOff_zero D
    have h3 : fof 0 = 0 := hτ.frat.zero
    have h4 : trOff D 0 = 0 := trOff_zero D
    simp only [size_condLt, size_var]
    rw [hτ.vv, h1, h2, h3, h4]
    omega

/-- **The fraternity CSR's contract transports along its own two
regions**: `CsrPrefix` mentions no other name, `winA` included. -/
theorem csrPrefix_of_eq {fo ft : String} {N : ℕ} {G : SimpleGraph (Fin N)}
    {nf : ℕ} {σ σ' : Env} (h : CsrPrefix fo ft G nf σ) (hne : fo ≠ ft)
    (hfo : σ'.arrs fo = σ.arrs fo) (hft : σ'.arrs ft = σ.arrs ft) :
    CsrPrefix fo ft G nf σ' := by
  obtain ⟨h1, h2, of', tg', hc, hz, hnd, hmem⟩ := h
  refine ⟨by rw [hfo]; exact h1, by rw [hft]; exact h2, of', tg', ⟨?_, ?_, hc.2.2⟩,
    hz, hnd, hmem⟩
  · rw [arrs_winA_some (ws := fun b => if b = fo then some (N + 1)
        else if b = ft then some nf else none) (b := fo) (m := N + 1) (by simp) σ',
      hfo, ← arrs_winA_some (ws := fun b => if b = fo then some (N + 1)
        else if b = ft then some nf else none) (b := fo) (m := N + 1) (by simp) σ]
    exact hc.1
  · rw [arrs_winA_some (ws := fun b => if b = fo then some (N + 1)
        else if b = ft then some nf else none) (b := ft) (m := nf)
        (by simp [Ne.symm hne]) σ', hft,
      ← arrs_winA_some (ws := fun b => if b = fo then some (N + 1)
        else if b = ft then some nf else none) (b := ft) (m := nf)
        (by simp [Ne.symm hne]) σ]
    exact hc.2.1

set_option maxHeartbeats 1600000 in
/-- **`StepEmitIn`, discharged** by `emCom` at its own cost `emComK`:
the transpose of `SolveAugEmitCom`, then the four-scan emit loop,
leaving in `(o', t')` an in-neighbour CSR of `greedyStep rk D` — the
finset equality `emRow_eq_greedyStep`, read back through
`trInCsr_emit`. -/
theorem stepEmitIn_emCom {B : ℕ}
    {nN nF nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String}
    (hnm : EmNames o t ro rt mk fo ft sg o' t' qo qt ad sd dg)
    (hnN : nN ∉ emScalars) (hnNtp : nN ∉ tpScalars) :
    StepEmitIn B nN nF nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg
      (emCom nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg) emComK := by
  classical
  intro n D rk ns nf off tgt ttF
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcsr, htr, hfratP, hrank, hcarN, -, hnfle, hBig, hrkB, hoL, htL,
    hqoL, hqtL, hadL, hsdL, hdgL, had0, hsd0, hdg0⟩ := hσ
  obtain ⟨ho't', ho'qo, ho'qt, ho'ad, ho'sd, ho'dg, ht'qo, ht'qt, ht'ad, ht'sd,
    ht'dg, hqoqt, hqoad, hqosd, hqodg, hqtad, hqtsd, hqtdg, hadsd, haddg,
    hsddg⟩ := emNames_wr hnm
  obtain ⟨hnv, hnv1, hnr, hnp, hnj, hne, hnu, hnc⟩ := emScalars_ne hnN
  have hRd : ∀ b ∈ emRd o t ro rt mk fo ft sg, ∀ a ∈ emWr o' t' qo qt ad sd dg, b ≠ a :=
    fun b hb a ha => (hnm.wrRd a ha b hb).symm
  have mo : o ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mt : t ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mro : ro ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mrt : rt ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mmk : mk ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mfo : fo ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mft : ft ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have msg : sg ∈ emRd o t ro rt mk fo ft sg := by simp [emRd]
  have mo' : o' ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have mt' : t' ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have mqo : qo ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have mqt : qt ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have mad : ad ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have msd : sd ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  have mdg : dg ∈ emWr o' t' qo qt ad sd dg := by simp [emWr]
  -- the figures
  have hnsarc : ns = arcCount D := hcsr.ns_eq_arcCount
  have htrle : trOff D n ≤ transPairCount D := transCsrAt_slots_le D
  have hnB : n < B := by omega
  have hnnB : n * n < B := by omega
  have harcB : arcCount D < B := by omega
  have hnfB : nf < B := by omega
  have htrB : trOff D n < B := by omega
  -- the fraternity CSR, unwrapped, and the output rows
  obtain ⟨fof, ftf, hfrat⟩ := csrRows_of_csrPrefix hfratP hnm.fo_ft
  set E := emE D rk off tgt fof ftf ttF with hEdef
  have hnd : ∀ v : Fin n, (E (v : ℕ)).Nodup := fun v =>
    nodup_emE (hcsr.row_mem v) (hfrat.mem v) (hcsr.row_nodup v) (hfrat.nodup v)
      (htr.row_nodup v)
  have hEmem : ∀ (v : Fin n) (u : ℕ), u ∈ E (v : ℕ) ↔
      ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ emRow D rk v := fun v u =>
    mem_emE (hcsr.row_mem v) (hfrat.mem v) (htr.row_mem v)
  have hemNs : emNs n E = arcCount (greedyStep rk D) := emNs_eq hnd hEmem
  have hemNsle : emNs n E ≤ arcCount D + fratPairCount D + transPairCount D :=
    emNs_le hnd hEmem
  have hnsB : emNs n E < B := by omega
  -- the transpose
  have htpn : TpNames o t qo qt dg :=
    { dg_o := hnm.wrRd dg mdg o mo, dg_t := hnm.wrRd dg mdg t mt,
      qo_o := hnm.wrRd qo mqo o mo, qo_t := hnm.wrRd qo mqo t mt, qo_dg := hqodg,
      qt_o := hnm.wrRd qt mqt o mo, qt_t := hnm.wrRd qt mqt t mt, qt_dg := hqtdg,
      qt_qo := Ne.symm hqoqt }
  obtain ⟨σa, hrunA, hcsrA, otF, houtA⟩ :=
    (transposeIn_tpCom (B := B) htpn hnNtp D ns off tgt).run
      ⟨hcsr, hcarN, by omega, hqoL, hqtL, hdgL, hdg0⟩
  have haA : ∀ b, b ≠ qo → b ≠ qt → b ≠ dg → σa.arrs b = σ.arrs b := by
    intro b h1 h2 h3
    refine hrunA.frame_arr b (fun hc => ?_)
    rcases mem_warrs_tpCom hc with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  have hvA : σa.vars nN = n := by
    rw [hrunA.frame_var nN (fun hc => hnNtp (mem_wvars_tpCom hc))]; exact hcarN
  have hlenA := run_arrs_length_eq hrunA
  -- the emit loop's entry state
  obtain ⟨σp, hσp⟩ : ∃ τ, τ = σa.setVar "em.p" 0 := ⟨_, rfl⟩
  have rp : Run B (.assign "em.p" (.lit 0)) σa σp 2 := by
    rw [hσp]; exact run_assign' (evB_lit' (by omega)) (by simp)
  obtain ⟨σb, hσb⟩ : ∃ τ, τ = σp.setVar "em.v" 0 := ⟨_, rfl⟩
  have rv : Run B (.assign "em.v" (.lit 0)) σp σb 2 := by
    rw [hσb]; exact run_assign' (evB_lit' (by omega)) (by simp)
  have hba : σb.arrs = σa.arrs := by rw [hσb, hσp]; simp
  have hstart : EmHeadSt nN o t ro rt mk fo ft sg o' t' qo qt ad sd dg
      D rk ns nf off tgt otF fof ftf ttF E 0 σb := by
    refine
      { csr := hcsrA.of_eq (by rw [hba]) (by rw [hba])
        out := houtA.of_eq (by rw [hba]) (by rw [hba])
        frat := hfrat.of_eq
          (by rw [hba, haA fo (hRd fo mfo qo mqo) (hRd fo mfo qt mqt)
            (hRd fo mfo dg mdg)])
          (by rw [hba, haA ft (hRd ft mft qo mqo) (hRd ft mft qt mqt)
            (hRd ft mft dg mdg)])
        tr := htr.of_eq
          (by rw [hba, haA ro (hRd ro mro qo mqo) (hRd ro mro qt mqt)
            (hRd ro mro dg mdg)])
          (by rw [hba, haA rt (hRd rt mrt qo mqo) (hRd rt mrt qt mqt)
            (hRd rt mrt dg mdg)])
          (by rw [hba, haA mk (hRd mk mmk qo mqo) (hRd mk mmk qt mqt)
            (hRd mk mmk dg mdg)])
        rank := hrank.of_eq
          (by rw [hba, haA sg (hRd sg msg qo mqo) (hRd sg msg qt mqt)
            (hRd sg msg dg mdg)])
        carrier := by rw [hσb, hσp]; simp [hnv, hnp, hvA]
        oLen := by
          rw [hba, haA o' ho'qo ho'qt ho'dg]; exact hoL
        tLen := by
          rw [hba, haA t' ht'qo ht'qt ht'dg]; omega
        adLen := by
          rw [hba, haA ad hqoad.symm hqtad.symm haddg]; exact hadL
        sdLen := by
          rw [hba, haA sd hqosd.symm hqtsd.symm hsddg]; exact hsdL
        dgLen := by rw [hba, hlenA dg]; exact hdgL
        vv := by rw [hσb]; simp
        vle := Nat.zero_le n
        ptr := by rw [hσb, hσp]; simp [emOff_zero]
        offs := by intro i hi; omega
        tgts := ?_
        adSt := ?_
        sdSt := ?_ }
    · intro q hq
      rw [hσb, hσp] at hq; simp at hq
    · intro q hq
      rw [hba, haA ad hqoad.symm hqtad.symm haddg, had0 q hq]
    · intro q hq
      rw [hba, haA sd hqosd.symm hqtsd.symm hsddg, hsd0 q hq]
  -- the heads
  obtain ⟨σc, Kl, hrunC, hstC, hKl⟩ := emHeads_run hnm hnN hEdef hnB hnnB hnsB
    (by omega) harcB hnfB htrB hrkB hstart
  -- the last offset and the slot count
  obtain ⟨σd, hσd⟩ : ∃ τ, τ = σc.setArr o' n (emNs n E) := ⟨_, rfl⟩
  have hcp : σc.vars "em.p" = emNs n E := hstC.ptr
  have rd : Run B (.store o' (.var nN) (.var "em.p")) σc σd 3 := by
    rw [hσd]
    exact run_store' (evB_var' hstC.carrier (by omega)) (evB_var' hcp (by omega))
      (by have := hstC.oLen; omega) (by simp)
  obtain ⟨σe, hσe⟩ : ∃ τ, τ = σd.setVar nO (emNs n E) := ⟨_, rfl⟩
  have re : Run B (.assign nO (.var "em.p")) σd σe 2 := by
    rw [hσe]
    exact run_assign' (evB_var' (by rw [hσd]; simpa using hcp) (by omega)) (by simp)
  have hea : ∀ b, b ≠ o' → σe.arrs b = σc.arrs b := by
    intro b hb; rw [hσe, hσd]; simp [hb]
  have heo' : σe.arrs o' = (σc.arrs o').set n (emNs n E) := by rw [hσe, hσd]; simp
  have hrun : Run B (emCom nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg) σ σe
      (tpK n (arcCount D) + (2 + ((2 + Kl) + (3 + 2)))) :=
    hrunA.seq (rp.seq ((rv.seq hrunC).seq (rd.seq re)))
  have hframe : ∀ b, b ≠ o' → b ≠ t' → b ≠ qo → b ≠ qt → b ≠ ad → b ≠ sd → b ≠ dg →
      σe.arrs b = σ.arrs b := by
    intro b h1 h2 h3 h4 h5 h6 h7
    refine hrun.frame_arr b (fun hc => ?_)
    rcases mem_warrs_emCom hc with h | h | h | h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
    · exact h5 h
    · exact h6 h
    · exact h7 h
  refine ⟨σe, _, hrun, ?_, ?_, ?_, ?_, ?_, hframe, ?_⟩
  · have htp : tpK n (arcCount D) = 41 * n + 40 * arcCount D + 30 := rfl
    simp only [emComK]
    omega
  · exact hcsr.of_eq
      (hframe o (hRd o mo o' mo') (hRd o mo t' mt') (hRd o mo qo mqo)
        (hRd o mo qt mqt) (hRd o mo ad mad) (hRd o mo sd msd) (hRd o mo dg mdg))
      (hframe t (hRd t mt o' mo') (hRd t mt t' mt') (hRd t mt qo mqo)
        (hRd t mt qt mqt) (hRd t mt ad mad) (hRd t mt sd msd) (hRd t mt dg mdg))
  · exact htr.of_eq
      (hframe ro (hRd ro mro o' mo') (hRd ro mro t' mt') (hRd ro mro qo mqo)
        (hRd ro mro qt mqt) (hRd ro mro ad mad) (hRd ro mro sd msd)
        (hRd ro mro dg mdg))
      (hframe rt (hRd rt mrt o' mo') (hRd rt mrt t' mt') (hRd rt mrt qo mqo)
        (hRd rt mrt qt mqt) (hRd rt mrt ad mad) (hRd rt mrt sd msd)
        (hRd rt mrt dg mdg))
      (hframe mk (hRd mk mmk o' mo') (hRd mk mmk t' mt') (hRd mk mmk qo mqo)
        (hRd mk mmk qt mqt) (hRd mk mmk ad mad) (hRd mk mmk sd msd)
        (hRd mk mmk dg mdg))
  · exact csrPrefix_of_eq hfratP hnm.fo_ft
      (hframe fo (hRd fo mfo o' mo') (hRd fo mfo t' mt') (hRd fo mfo qo mqo)
        (hRd fo mfo qt mqt) (hRd fo mfo ad mad) (hRd fo mfo sd msd)
        (hRd fo mfo dg mdg))
      (hframe ft (hRd ft mft o' mo') (hRd ft mft t' mt') (hRd ft mft qo mqo)
        (hRd ft mft qt mqt) (hRd ft mft ad mad) (hRd ft mft sd msd)
        (hRd ft mft dg mdg))
  · exact hrank.of_eq
      (hframe sg (hRd sg msg o' mo') (hRd sg msg t' mt') (hRd sg msg qo mqo)
        (hRd sg msg qt mqt) (hRd sg msg ad mad) (hRd sg msg sd msd)
        (hRd sg msg dg mdg))
  · refine ⟨emOff E, fun p => (emPref E n).getD p 0, ?_, ?_⟩
    · have hT := trInCsr_emit (o' := o') (t' := t') (D := D) (rk := rk) (E := E)
        (σ := σe) hnd hEmem
        (by rw [heo', List.length_set]; exact hstC.oLen)
        (by rw [hea t' (Ne.symm ho't')]; exact hstC.tLen)
        (fun i hi => by
          rw [heo']
          have hlen' : i < ((σc.arrs o').set n (emNs n E)).length := by
            rw [List.length_set]; have := hstC.oLen; omega
          rw [getElem?_of_lt' _ _ hlen']
          rcases Nat.lt_or_ge i n with h | h
          · rw [getD_set_of_ne (by omega), hstC.offs i h]
          · obtain rfl : i = n := by omega
            rw [getD_set_self (by have := hstC.oLen; omega)]
            rfl)
        (fun q hq => by
          rw [hea t' (Ne.symm ho't')]
          have hlt : q < (σc.arrs t').length := by have := hstC.tLen; omega
          rw [getElem?_of_lt' _ _ hlt, hstC.tgts q (by rw [hcp]; exact hq)])
      rw [hemNs] at hT
      exact hT
    · rw [hσe]; simp [hemNs]

/-- **`StepEmitIn` at `SolveAugEmit`'s pinned budget.**  `emK n a f T =
300·n + 300·a + 200·f + 240·T + 80` was fixed before any command text
existed; `emCom` meets it with room in every term. -/
theorem stepEmitIn_emCom_emK {B : ℕ}
    {nN nF nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String}
    (hnm : EmNames o t ro rt mk fo ft sg o' t' qo qt ad sd dg)
    (hnN : nN ∉ emScalars) (hnNtp : nN ∉ tpScalars) :
    StepEmitIn B nN nF nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg
      (emCom nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg) emK :=
  fun D rk ns nf off tgt ttF =>
    (stepEmitIn_emCom hnm hnN hnNtp D rk ns nf off tgt ttF).mono
      (emComK_le_emK _ _ _ _)

/-- **The hypotheses are satisfiable**, so the discharge is not vacuous:
fifteen distinct region names and a carrier cell outside both scalar
pools meet all three. -/
example :
    EmNames "ao" "at" "ro" "rt" "mk" "fo" "ft" "sg" "oo" "ot" "qo" "qt" "ad" "sd" "dg" ∧
      ("nn" : String) ∉ emScalars ∧ ("nn" : String) ∉ tpScalars :=
  ⟨{ wrRd := by decide, wrNd := by decide, fo_ft := by decide }, by decide, by decide⟩

/-! ## §8 The axiom surface -/

#print axioms csrRows_of_csrPrefix
#print axioms csrPrefix_of_eq
#print axioms mem_emE
#print axioms nodup_emE
#print axioms emComK_le_emK
#print axioms stepEmitIn_emCom
#print axioms stepEmitIn_emCom_emK

end Lax3Proofs.Prog
