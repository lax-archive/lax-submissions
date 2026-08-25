import Lax13Proofs.Lib.Csr
import Lax3Proofs.ProgCoverCharge

/-!
# F6c12-5c-i — `TransCsrIn`, the transitive candidate region

One of the two genuinely new passes of `CovAugAdjIn`'s split.  From an
**in-neighbour CSR of the current orientation `D`** (`TrInCsr`) it builds
an exact region for `TransLink D` (`Augmentation.lean:165`), answering
`TransLink D u v` *and* `TransLink D v u` in `O(1)` each — which is
what the consumer needs, because `greedyStep` (`CoverRoutine.lean:212`)
tests both directions of every candidate pair inside one `pick` filter.

## The enumeration

Verbatim NOdM II's own pseudocode (`references/nodm05/BEII.tex:600-611`):
for each `v`, for each `(u,e) ∈ D[v]`, for each `(x,f) ∈ D[u]`, append
`x` to `D'[v]`.  Read off a CSR that is: for each `v`, for each slot
`s` of row `v`, for each slot `r` of row `tgt s`, emit `tgt r`
(`TrEmDone`, `TrEmPart`, and their bridge `TrInCsr.trEmD_row_end`).

## The region: a head-major matrix, with the CSR beside it

`TransLink` is **directed and not symmetric**: `TransLink D u v` and
`TransLink D v u` are different facts.  A row-per-head CSR alone
answers a membership query in the length of the row, not in `O(1)`, and
its transpose would be a second structure to build and keep in step.
What the pass leaves instead (`TransCsrAt`) is

* an `n × n` **mark matrix, head-major**: `mk[v·n + u] = 1` iff
  `TransLink D u v`.  Then `TransLink D u v` is the single cell
  `v·n + u` and `TransLink D v u` is the single cell `u·n + v`, so
  *both* directions are one array read of the *same* region — the
  transpose is free and there is no second structure to fall out of
  step (`transCsrAt_decides`);
* the **CSR** `(ro, rt)` of the same relation, for a consumer that
  enumerates one head's candidates rather than testing a pair
  (`transCsrAt_row`).

Array lengths are free (`Imp.lean:20-44`), so the `n²` window costs
nothing to have; the pass touches only the cells it sets, and asks the
window to be clear on entry — which is the machine's own initial state,
not work anyone pays for.

The matrix doubles as the **dedup mark**: distinct heads own disjoint
slices of it, so nothing is re-zeroed between rows and no row stamp is
needed.  That is the one structural difference from the landed exemplar
`rootCsrLoadAll_csrLoadCom` (`SolveCovLoad.lean:1290`), whose `n`-cell
mark array is re-used per row and therefore *is* row-stamped; here the
marks survive as the output.

## The budget

`trK n a T = 27·n + 23·a + 30·T + 13`, at `a = arcCount D` and
`T = transPairCount D` (`transCsrIn_trCom`).  Term by term:

* `27` a **head**: the outer turn's fixed block — anchor the head's
  offset, set its matrix row base, read its two row bounds, advance —
  and the loop headers.  One turn per vertex of the carrier, isolated
  vertices included.
* `23` an **arc** of `D`: one middle turn, which loads a mid vertex `w`
  and `w`'s two row bounds.  `arcCount D = Σ_v |inN v|`
  (`ProgCoverCharge.lean:129`) is exactly the input CSR's slot count —
  `TrInCsr.ns_eq_arcCount`.
* `30` a **transitive candidate**: one inner turn — the read, the
  matrix test, and, when it fires, the two stores and the write-pointer
  bump.  `transPairCount D = Σ_v Σ_{w ∈ inN v} |inN w|`
  (`ProgCoverCharge.lean:140`) is exactly the size of the enumeration —
  `TrInCsr.trPref_eq` — and it is the count `levelCharge`
  (`ProgCoverCharge.lean:150`) already charges the transitive stage at,
  where `exists_chainCharge_le` (`:381`) closes the chain inside §7's
  envelope.

So the pass is `O(n + arcCount D + transPairCount D)` and nothing else:
no carrier scan inside a head's turn, no comparison sort, no `n²` term.
The output never outgrows the enumeration —
`trOff D n ≤ transPairCount D` (`transCsrAt_slots_le`) — so
`transPairCount D` cells of target space are enough, which is what the
precondition asks for.

## Findings

1. **`TransLink D v v` is vacuous, not excluded.**  `TransLink` as
   stated permits `u = v`: it reads `∃ w, v ∈ inN w ∧ w ∈ inN v`.  That
   is exactly the two-cycle `Orientation.asymm` forbids, so
   `not_transLink_self` *proves* the case away rather than assuming it,
   and `TransCsrAt.mark_diag` reads off that the diagonal of the matrix
   is never written — a consumer owes no `u ≠ v` side condition.  The
   paper's directed graphs do permit two-cycles, so BEII's own
   enumeration can emit `(v, v)`; the Lean object cannot, and nothing
   here imports the paper's licence.
2. **BEII's enumeration is a multiset; this region is a set.**  The
   paper says outright that "missing arcs may appear more than once in
   the list" (`BEII.tex:617-620`) and never dedupes.  `greedyStep`'s
   `pick` filter is a *set* equality, so a multiset would not do: the
   rows here are `sound`, `complete` and repetition-free (`inj`), and
   the matrix is pinned cell by cell in both directions
   (`markOne`/`markZero`).  The dedup is free — it is the matrix test
   the pass performs anyway.
3. **Isolated vertices are in the carrier.**  A vertex in no `inN w`
   still gets a row: offsets are anchored per head at the start of its
   turn (`trOuter`'s first store), so an empty row is an empty
   half-open interval `[trOff D v, trOff D (v+1))` and not a missing
   one.  `trOff_owner` reads the partition back.
4. **`AdjBuildIn` (`SolveSweepAdj.lean:308`) is unmeetable as landed,
   and this file does not repeat its shape.**  It names no cell holding
   the carrier size, and IMP+ has no array-length primitive
   (`Imp.lean:158`), so a fixed command cannot find where a carrier
   ends.  `TransCsrIn` takes `n` from the named scalar `nN`, exactly as
   `AdjBuildAt` (`SolveSweepBuild.lean:1864`) does; `ns` is *not* taken
   from a cell because the program never needs it — every bound the
   three loops use is an offset read out of the input CSR.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation

/-! ## §1 The input CSR of an orientation -/

/-- **The in-neighbour CSR of an orientation, as this pass reads it.**
`SolveSweepBuild.SrcCsr`'s shape at a *directed* relation: row `v`
lists `D.inN v`, the offsets are the in-degree prefix sums, and the two
regions may be longer than their extents (the windowed convention). -/
structure TrInCsr (o t : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The offsets are anchored. -/
  zero : off 0 = 0
  /-- One row per vertex, of exactly its in-degree. -/
  step : ∀ v : Fin n, off ((v : ℕ) + 1) = off (v : ℕ) + (D.inN v).card
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
  /-- Every slot of row `v` holds an in-neighbour of `v`. -/
  sound : ∀ (v : Fin n) (p : ℕ), off (v : ℕ) ≤ p → p < off ((v : ℕ) + 1) →
    ∀ h : tgt p < n, (⟨tgt p, h⟩ : Fin n) ∈ D.inN v
  /-- Every in-neighbour of `v` sits in a slot of row `v`. -/
  complete : ∀ (v u : Fin n), u ∈ D.inN v →
    ∃ p, off (v : ℕ) ≤ p ∧ p < off ((v : ℕ) + 1) ∧ tgt p = (u : ℕ)
  /-- No two slots of one row hold the same target. -/
  inj : ∀ (v : Fin n) (p r : ℕ), off (v : ℕ) ≤ p → p < off ((v : ℕ) + 1) →
    off (v : ℕ) ≤ r → r < off ((v : ℕ) + 1) → tgt p = tgt r → p = r

namespace TrInCsr

variable {o t : String} {n ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ} {σ : Env}

/-- The offsets are monotone below `n`. -/
theorem mono (h : TrInCsr o t D ns off tgt σ) : ∀ b, b ≤ n → ∀ a, a ≤ b → off a ≤ off b := by
  intro b
  induction b with
  | zero => intro _ a ha; obtain rfl : a = 0 := Nat.le_zero.1 ha; exact le_rfl
  | succ b ih =>
      intro hb a ha
      have hstep : off (b + 1) = off b + (D.inN ⟨b, by omega⟩).card := h.step ⟨b, by omega⟩
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · have := ih (by omega) a (by omega)
        omega
      · obtain rfl : a = b + 1 := by omega
        exact le_rfl

/-- Every offset is at most the extent. -/
theorem off_le_ns (h : TrInCsr o t D ns off tgt σ) {i : ℕ} (hi : i ≤ n) : off i ≤ ns := by
  have := h.mono n le_rfl i hi
  rw [h.last] at this
  exact this

/-- A slot of a row is a slot of the structure. -/
theorem row_lt_ns (h : TrInCsr o t D ns off tgt σ) {v : Fin n} {p : ℕ}
    (hp : p < off ((v : ℕ) + 1)) : p < ns :=
  lt_of_lt_of_le hp (h.off_le_ns v.isLt)

/-- Reading an offset, as a `getD`. -/
theorem offGetD (h : TrInCsr o t D ns off tgt σ) {i : ℕ} (hi : i ≤ n) :
    (σ.arrs o).getD i 0 = off i := by
  have := h.offGet i hi
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- Reading a target, as a `getD`. -/
theorem tgtGetD (h : TrInCsr o t D ns off tgt σ) {p : ℕ} (hp : p < ns) :
    (σ.arrs t).getD p 0 = tgt p := by
  have := h.tgtGet p hp
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- The row of `v` is as long as `v`'s in-degree. -/
theorem rowLen_eq (h : TrInCsr o t D ns off tgt σ) (v : Fin n) :
    off ((v : ℕ) + 1) - off (v : ℕ) = (D.inN v).card := by
  rw [h.step v]; omega

/-- The pass never writes the two input regions, so the package
transports along agreement on them. -/
theorem of_eq (h : TrInCsr o t D ns off tgt σ) {σ' : Env}
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t) :
    TrInCsr o t D ns off tgt σ' :=
  { h with
    offLen := by rw [ho]; exact h.offLen
    tgtLen := by rw [ht]; exact h.tgtLen
    offGet := by rw [ho]; exact h.offGet
    tgtGet := by rw [ht]; exact h.tgtGet }

end TrInCsr

/-! ## §2 The enumeration, abstractly

`for each v, for each w ∈ inN v, for each u ∈ inN w, emit (u, v)` reads
off the CSR as: for each `v`, for each slot `s` of row `v`, for each
slot `r` of row `tgt s`, emit `tgt r`.  `TrEmDone` is what the completed
slots of row `v` below `j` have emitted, `TrEmPart` what the prefix
`[off w, k)` of row `w` has. -/

/-- The candidates at head `v` emitted by the slots of row `v` below
`j`, each slot's whole row. -/
def TrEmDone (off tgt : ℕ → ℕ) (v j z : ℕ) : Prop :=
  ∃ s, off v ≤ s ∧ s < j ∧ ∃ r, off (tgt s) ≤ r ∧ r < off (tgt s + 1) ∧ tgt r = z

/-- The candidates emitted by the prefix `[off w, k)` of row `w`. -/
def TrEmPart (off tgt : ℕ → ℕ) (w k z : ℕ) : Prop :=
  ∃ r, off w ≤ r ∧ r < k ∧ tgt r = z

variable {off tgt : ℕ → ℕ}

theorem trEmDone_start {v z : ℕ} : ¬ TrEmDone off tgt v (off v) z := by
  rintro ⟨s, h1, h2, -⟩; omega

theorem trEmPart_start {w z : ℕ} : ¬ TrEmPart off tgt w (off w) z := by
  rintro ⟨r, h1, h2, -⟩; omega

theorem trEmPart_succ {w k z : ℕ} :
    TrEmPart off tgt w (k + 1) z ↔ TrEmPart off tgt w k z ∨ (off w ≤ k ∧ tgt k = z) := by
  constructor
  · rintro ⟨r, h1, h2, h3⟩
    rcases Nat.lt_or_ge r k with h | h
    · exact Or.inl ⟨r, h1, h, h3⟩
    · obtain rfl : r = k := by omega
      exact Or.inr ⟨h1, h3⟩
  · rintro (⟨r, h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact ⟨r, h1, by omega, h3⟩
    · exact ⟨k, h1, by omega, h2⟩

theorem trEmDone_succ {v j z : ℕ} (hj : off v ≤ j) :
    TrEmDone off tgt v (j + 1) z ↔
      TrEmDone off tgt v j z ∨ TrEmPart off tgt (tgt j) (off (tgt j + 1)) z := by
  constructor
  · rintro ⟨s, h1, h2, r, h3, h4, h5⟩
    rcases Nat.lt_or_ge s j with h | h
    · exact Or.inl ⟨s, h1, h, r, h3, h4, h5⟩
    · obtain rfl : s = j := by omega
      exact Or.inr ⟨r, h3, h4, h5⟩
  · rintro (⟨s, h1, h2, hr⟩ | ⟨r, h3, h4, h5⟩)
    · exact ⟨s, h1, by omega, hr⟩
    · exact ⟨j, hj, by omega, r, h3, h4, h5⟩

/-! ### The emitted sets -/

/-- The set emitted at head `v` by the completed slots below `j`. -/
noncomputable def trEmD (n : ℕ) (off tgt : ℕ → ℕ) (v j : ℕ) : Finset (Fin n) :=
  pick (fun u : Fin n => TrEmDone off tgt v j (u : ℕ))

/-- The set emitted at head `v` by the completed slots below `j`
together with the prefix `[off (tgt j), k)` of the current slot's
row. -/
noncomputable def trEmK (n : ℕ) (off tgt : ℕ → ℕ) (v j k : ℕ) : Finset (Fin n) :=
  pick (fun u : Fin n => TrEmDone off tgt v j (u : ℕ) ∨ TrEmPart off tgt (tgt j) k (u : ℕ))

variable {n : ℕ}

theorem mem_trEmD {v j : ℕ} {u : Fin n} :
    u ∈ trEmD n off tgt v j ↔ TrEmDone off tgt v j (u : ℕ) := mem_pick

theorem mem_trEmK {v j k : ℕ} {u : Fin n} :
    u ∈ trEmK n off tgt v j k ↔
      TrEmDone off tgt v j (u : ℕ) ∨ TrEmPart off tgt (tgt j) k (u : ℕ) := mem_pick

/-- At the start of a slot's row nothing of it has been emitted yet. -/
theorem trEmK_start (v j : ℕ) : trEmK n off tgt v j (off (tgt j)) = trEmD n off tgt v j := by
  ext u
  rw [mem_trEmK, mem_trEmD]
  exact ⟨fun h => h.resolve_right trEmPart_start, Or.inl⟩

/-- A head starts with nothing emitted. -/
theorem trEmD_empty (v : ℕ) : trEmD n off tgt v (off v) = (∅ : Finset (Fin n)) := by
  ext u
  constructor
  · intro hu; exact absurd (mem_trEmD.1 hu) trEmDone_start
  · intro hu; exact absurd hu (by simp)

/-- At the end of a slot's row the slot is complete. -/
theorem trEmK_end {v j : ℕ} (hj : off v ≤ j) :
    trEmK n off tgt v j (off (tgt j + 1)) = trEmD n off tgt v (j + 1) := by
  ext u
  rw [mem_trEmK, mem_trEmD, trEmDone_succ hj]

/-- One inner turn that emits: the candidate joins the set. -/
theorem trEmK_succ_emit {v j k : ℕ} (hk : off (tgt j) ≤ k) (h : tgt k < n) :
    trEmK n off tgt v j (k + 1) = insert (⟨tgt k, h⟩ : Fin n) (trEmK n off tgt v j k) := by
  ext u
  rw [mem_trEmK, trEmPart_succ, Finset.mem_insert, mem_trEmK]
  constructor
  · rintro (hd | hp | ⟨-, he⟩)
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr hp)
    · exact Or.inl (by ext; exact he.symm)
  · rintro (rfl | hd | hp)
    · exact Or.inr (Or.inr ⟨hk, rfl⟩)
    · exact Or.inl hd
    · exact Or.inr (Or.inl hp)

/-- One inner turn that does not emit: the set is unchanged. -/
theorem trEmK_succ_skip {v j k : ℕ} (hk : off (tgt j) ≤ k) (h : tgt k < n)
    (hmem : (⟨tgt k, h⟩ : Fin n) ∈ trEmK n off tgt v j k) :
    trEmK n off tgt v j (k + 1) = trEmK n off tgt v j k := by
  rw [trEmK_succ_emit hk h, Finset.insert_eq_self.2 hmem]

/-! ## §3 The relation, its row sizes and the two counts -/

/-- The transitive in-neighbours of `v`: the exact row the pass emits
at head `v`. -/
noncomputable def trIn (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  pick (fun u => TransLink D u v)

theorem mem_trIn {D : Orientation n} {v u : Fin n} : u ∈ trIn D v ↔ TransLink D u v := mem_pick

/-- **`TransLink` never holds of a vertex and itself.**  `TransLink`
as stated permits `u = v` — it is `∃ w, v ∈ inN w ∧ w ∈ inN v` — but
that is exactly the two-cycle `Orientation.asymm` forbids, so the case
is vacuous rather than excluded by hypothesis.  The diagonal of the
mark matrix is therefore never written. -/
theorem not_transLink_self (D : Orientation n) (v : Fin n) : ¬ TransLink D v v := by
  rintro ⟨w, hvw, hwv⟩
  exact D.asymm w v hwv hvw

theorem self_not_mem_trIn (D : Orientation n) (v : Fin n) : v ∉ trIn D v :=
  fun h => not_transLink_self D v (mem_trIn.1 h)

/-- The row size of the output at head `v`, and `0` off the carrier. -/
noncomputable def trDeg (D : Orientation n) (v : ℕ) : ℕ :=
  if h : v < n then (trIn D ⟨v, h⟩).card else 0

/-- The output's offsets: the prefix sums of `trDeg`. -/
noncomputable def trOff (D : Orientation n) (v : ℕ) : ℕ := ∑ a ∈ Finset.range v, trDeg D a

theorem trOff_zero (D : Orientation n) : trOff D 0 = 0 := by simp [trOff]

theorem trOff_succ (D : Orientation n) (v : ℕ) :
    trOff D (v + 1) = trOff D v + trDeg D v := Finset.sum_range_succ _ _

theorem trOff_mono (D : Orientation n) {a b : ℕ} (hab : a ≤ b) : trOff D a ≤ trOff D b :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hab)

theorem trDeg_coe (D : Orientation n) (v : Fin n) : trDeg D (v : ℕ) = (trIn D v).card := by
  rw [trDeg, dif_pos v.isLt]

/-- The in-degree of `v` as a function of a plain index. -/
noncomputable def trInDegAt (D : Orientation n) (v : ℕ) : ℕ :=
  if h : v < n then (D.inN ⟨v, h⟩).card else 0

/-! ### The two cost quantities of the enumeration -/

/-- The transitive candidates still to be enumerated at head `v` from
slot `j` on: one per slot of each remaining `w`'s row. -/
def trRest (off tgt : ℕ → ℕ) (v j : ℕ) : ℕ :=
  ∑ s ∈ Finset.Ico j (off (v + 1)), (off (tgt s + 1) - off (tgt s))

/-- The transitive candidates at head `v`. -/
def trRow (off tgt : ℕ → ℕ) (v : ℕ) : ℕ := trRest off tgt v (off v)

/-- The transitive candidates at heads below `v`. -/
def trPref (off tgt : ℕ → ℕ) (v : ℕ) : ℕ := ∑ a ∈ Finset.range v, trRow off tgt a

theorem trRest_succ {v j : ℕ} (hj : j < off (v + 1)) :
    trRest off tgt v j = (off (tgt j + 1) - off (tgt j)) + trRest off tgt v (j + 1) :=
  Finset.sum_eq_sum_Ico_succ_bot hj _

theorem trPref_succ (v : ℕ) :
    trPref off tgt (v + 1) = trPref off tgt v + trRow off tgt v := Finset.sum_range_succ _ _

theorem trPref_mono {a b : ℕ} (hab : a ≤ b) : trPref off tgt a ≤ trPref off tgt b :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hab)

/-! ### The bridges to the landed counts -/

variable {o t : String} {ns : ℕ} {D : Orientation n} {σ : Env}

/-- The offsets are the in-degree prefix sums. -/
theorem TrInCsr.off_eq_sum (h : TrInCsr o t D ns off tgt σ) :
    ∀ k, k ≤ n → off k = ∑ v ∈ Finset.range k, trInDegAt D v := by
  intro k
  induction k with
  | zero => intro _; rw [h.zero]; simp
  | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, ← ih (by omega)]
      have := h.step ⟨k, by omega⟩
      rw [trInDegAt, dif_pos (show k < n by omega)]
      exact this

/-- **The slot count of the input CSR is the arc count**: `ns =
arcCount D`, so the pass's `ns`-term budget is an `arcCount` term. -/
theorem TrInCsr.ns_eq_arcCount (h : TrInCsr o t D ns off tgt σ) : ns = arcCount D := by
  rw [← h.last, h.off_eq_sum n le_rfl, arcCount]
  rw [← Fin.sum_univ_eq_sum_range (fun v => trInDegAt D v) n]
  exact Finset.sum_congr rfl fun v _ => by rw [trInDegAt, dif_pos v.isLt]

/-- One head's candidate count is the source algorithm's inner sum. -/
theorem TrInCsr.trRow_eq (h : TrInCsr o t D ns off tgt σ) (v : Fin n) :
    trRow off tgt (v : ℕ) = ∑ w ∈ D.inN v, (D.inN w).card := by
  rw [trRow, trRest]
  refine Finset.sum_bij (fun s hs => (⟨tgt s, ?_⟩ : Fin n)) ?_ ?_ ?_ ?_
  · rw [Finset.mem_Ico] at hs
    exact h.tgtLt _ (h.row_lt_ns (v := v) hs.2)
  · intro s hs
    rw [Finset.mem_Ico] at hs
    exact h.sound v s hs.1 hs.2 _
  · intro a ha b hb hab
    rw [Finset.mem_Ico] at ha hb
    exact h.inj v a b ha.1 ha.2 hb.1 hb.2 (by simpa using congrArg Fin.val hab)
  · intro w hw
    obtain ⟨s, h1, h2, h3⟩ := h.complete v w hw
    exact ⟨s, Finset.mem_Ico.2 ⟨h1, h2⟩, by ext; simpa using h3⟩
  · intro s hs
    rw [Finset.mem_Ico] at hs
    exact h.rowLen_eq ⟨tgt s, h.tgtLt _ (h.row_lt_ns (v := v) hs.2)⟩

/-- **The enumeration's size is `transPairCount D`** — the very count
`ProgCoverCharge.levelCharge` charges the transitive stage at. -/
theorem TrInCsr.trPref_eq (h : TrInCsr o t D ns off tgt σ) :
    trPref off tgt n = transPairCount D := by
  rw [trPref, transPairCount, ← Fin.sum_univ_eq_sum_range (fun v => trRow off tgt v) n]
  exact Finset.sum_congr rfl fun v _ => h.trRow_eq v

/-- Each output row fits inside its head's candidate list. -/
theorem trIn_card_le (D : Orientation n) (v : Fin n) :
    (trIn D v).card ≤ ∑ w ∈ D.inN v, (D.inN w).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_biUnion_le)
  intro u hu
  obtain ⟨w, hw1, hw2⟩ := mem_trIn.1 hu
  exact Finset.mem_biUnion.2 ⟨w, hw2, hw1⟩

/-- **The output never outgrows the enumeration**: `transPairCount D`
cells of target space are enough. -/
theorem trOff_le_transPairCount (D : Orientation n) : trOff D n ≤ transPairCount D := by
  rw [trOff, transPairCount, ← Fin.sum_univ_eq_sum_range (fun v => trDeg D v) n]
  exact Finset.sum_le_sum fun v _ => by rw [trDeg_coe]; exact trIn_card_le D v

/-! ### The enumeration, read at a row's end -/

/-- **Exactness of one head's enumeration**: what the completed row of
`v` has emitted is exactly `v`'s transitive in-neighbourhood. -/
theorem TrInCsr.trEmD_row_end (h : TrInCsr o t D ns off tgt σ) (v : Fin n) :
    trEmD n off tgt (v : ℕ) (off ((v : ℕ) + 1)) = trIn D v := by
  ext u
  rw [mem_trEmD, mem_trIn]
  constructor
  · rintro ⟨s, hs1, hs2, r, hr1, hr2, hr3⟩
    have hsn : tgt s < n := h.tgtLt _ (h.row_lt_ns (v := v) hs2)
    have hw : (⟨tgt s, hsn⟩ : Fin n) ∈ D.inN v := h.sound v s hs1 hs2 hsn
    have hrn : r < ns := h.row_lt_ns (v := ⟨tgt s, hsn⟩) hr2
    have hun : tgt r < n := h.tgtLt _ hrn
    have hu : (⟨tgt r, hun⟩ : Fin n) ∈ D.inN ⟨tgt s, hsn⟩ := h.sound ⟨tgt s, hsn⟩ r hr1 hr2 hun
    refine ⟨⟨tgt s, hsn⟩, ?_, hw⟩
    have : (⟨tgt r, hun⟩ : Fin n) = u := by ext; exact hr3
    rwa [this] at hu
  · rintro ⟨w, hw1, hw2⟩
    obtain ⟨s, hs1, hs2, hs3⟩ := h.complete v w hw2
    obtain ⟨r, hr1, hr2, hr3⟩ := h.complete w u hw1
    exact ⟨s, hs1, hs2, r, by rw [hs3]; exact hr1, by rw [hs3]; exact hr2, hr3⟩

/-! ## §4 The region the pass leaves

**The shape, and why.**  `TransLink` is *directed*: `TransLink D u v`
and `TransLink D v u` are different facts, and `greedyStep`
(`CoverRoutine.lean:212`) tests both.  A row-per-head CSR alone answers
a membership query in the length of the row, not in `O(1)`, and its
transpose would be a second structure to build and keep consistent.
The region here is therefore a **`n × n` mark matrix, head-major**
(`mk[v·n + u] = 1` iff `TransLink D u v`) **together with the CSR of
the same relation**.  The matrix answers *both* directions in one array
read each — `TransLink D u v` at `v·n + u` and `TransLink D v u` at
`u·n + v` — so the transpose is free and no second structure exists to
fall out of step; the CSR is what an enumeration over the candidates of
one head reads.  Array lengths are free (`Imp.lean:20-44`), so the `n²`
region costs nothing to have; the pass touches only the cells it
sets.

`SolveBlocks.GraphCsr` is the same CSR shape for a `SimpleGraph`, whose
`Adj` is symmetric and whose rows therefore need no direction; it also
pins exact array lengths through `Lib.Csr`.  This one is stated at
`≤ length` allocations (the windowed convention) and at a directed
relation, and carries the matrix clause `GraphCsr` has no counterpart
for. -/

/-- **The transitive candidate region.**  Offsets `trOff D`, targets
`ttF`, and the head-major mark matrix, all read at allocations of at
least their extents. -/
structure TransCsrAt (ro rt mk : String) {n : ℕ} (D : Orientation n) (ttF : ℕ → ℕ)
    (σ : Env) : Prop where
  /-- The offset region holds at least `n + 1` cells. -/
  toLen : n + 1 ≤ (σ.arrs ro).length
  /-- The target region holds at least the slot count. -/
  ttLen : trOff D n ≤ (σ.arrs rt).length
  /-- The matrix region holds at least `n²` cells. -/
  markLen : n * n ≤ (σ.arrs mk).length
  /-- Reading an offset. -/
  toGet : ∀ i, i ≤ n → (σ.arrs ro)[i]? = some (trOff D i)
  /-- Reading a target. -/
  ttGet : ∀ p, p < trOff D n → (σ.arrs rt)[p]? = some (ttF p)
  /-- Every target is a vertex. -/
  ttLt : ∀ p, p < trOff D n → ttF p < n
  /-- Every slot of row `v` holds a transitive in-neighbour of `v`. -/
  sound : ∀ (v : Fin n) (p : ℕ), trOff D (v : ℕ) ≤ p → p < trOff D ((v : ℕ) + 1) →
    ∀ h : ttF p < n, TransLink D ⟨ttF p, h⟩ v
  /-- Every transitive in-neighbour of `v` sits in a slot of row `v`. -/
  complete : ∀ (v u : Fin n), TransLink D u v →
    ∃ p, trOff D (v : ℕ) ≤ p ∧ p < trOff D ((v : ℕ) + 1) ∧ ttF p = (u : ℕ)
  /-- No two slots of one row hold the same target. -/
  inj : ∀ (v : Fin n) (p r : ℕ), trOff D (v : ℕ) ≤ p → p < trOff D ((v : ℕ) + 1) →
    trOff D (v : ℕ) ≤ r → r < trOff D ((v : ℕ) + 1) → ttF p = ttF r → p = r
  /-- **The matrix, where the relation holds**: cell `v·n + u` is set. -/
  markOne : ∀ v u : Fin n, TransLink D u v →
    (σ.arrs mk).getD ((v : ℕ) * n + (u : ℕ)) 0 = 1
  /-- **The matrix, where it does not**: cell `v·n + u` is clear. -/
  markZero : ∀ v u : Fin n, ¬ TransLink D u v →
    (σ.arrs mk).getD ((v : ℕ) * n + (u : ℕ)) 0 = 0

namespace TransCsrAt

variable {ro rt mk : String} {ttF : ℕ → ℕ}

/-- **The `O(1)` membership test**, one array read.  `TransLink D u v`
is the cell `v·n + u` and `TransLink D v u` is the cell `u·n + v`, so
the consumer's two-direction decision is two reads of the *same*
region and no transpose is built. -/
theorem mark_eq_one (h : TransCsrAt ro rt mk D ttF σ) (v u : Fin n) :
    (σ.arrs mk).getD ((v : ℕ) * n + (u : ℕ)) 0 = 1 ↔ TransLink D u v := by
  refine ⟨fun h1 => ?_, h.markOne v u⟩
  by_contra hc
  rw [h.markZero v u hc] at h1
  exact absurd h1 (by omega)

/-- The two directions the consumer needs, side by side. -/
theorem mark_both (h : TransCsrAt ro rt mk D ttF σ) (u v : Fin n) :
    ((σ.arrs mk).getD ((v : ℕ) * n + (u : ℕ)) 0 = 1 ↔ TransLink D u v) ∧
      ((σ.arrs mk).getD ((u : ℕ) * n + (v : ℕ)) 0 = 1 ↔ TransLink D v u) :=
  ⟨h.mark_eq_one v u, h.mark_eq_one u v⟩

/-- **The diagonal is clear.**  `TransLink D v v` would be a two-cycle
(`not_transLink_self`), so the pass never writes cell `v·n + v` and the
consumer never has to exclude `u = v` by hand. -/
theorem mark_diag (h : TransCsrAt ro rt mk D ttF σ) (v : Fin n) :
    (σ.arrs mk).getD ((v : ℕ) * n + (v : ℕ)) 0 = 0 :=
  h.markZero v v (not_transLink_self D v)

end TransCsrAt

/-! ## §5 The program

Three nested loops and nothing else: the head `v`, the mid vertex `w`
running over row `v` of the input, and the candidate `u` running over
row `w`.  The dedup is the matrix itself — cell `v·n + u` is both the
answer the consumer will read and the "already emitted in this row"
mark — so no mark array is re-zeroed between rows and no row stamp is
needed: distinct heads own disjoint slices of the matrix.  That is the
one structural difference from `rootCsrLoadAll`'s row-stamped `n`-cell
mark (`SolveCovLoad.lean:1290`), and it is what makes the marks
survive as the output. -/

/-- The pass's scratch scalars: the head, its slot pointer and row end,
the mid vertex, its slot pointer and row end, the candidate, the write
pointer and the matrix row base. -/
def trScalars : List String :=
  ["tr.v", "tr.j", "tr.e", "tr.w", "tr.k", "tr.f", "tr.z", "tr.p", "tr.b"]

/-- One turn of the innermost loop: read the candidate, and if its
matrix cell is still clear, set it and append the candidate. -/
def trInner (t rt mk : String) : Com :=
  .seq (.assign "tr.z" (.get t (.var "tr.k")))
    (.seq
      (.ite (.eq (.get mk (.add (.var "tr.b") (.var "tr.z"))) (.lit 0))
        (.seq (.store mk (.add (.var "tr.b") (.var "tr.z")) (.lit 1))
          (.seq (.store rt (.var "tr.p") (.var "tr.z"))
            (.assign "tr.p" (.add (.var "tr.p") (.lit 1)))))
        .skip)
      (.assign "tr.k" (.add (.var "tr.k") (.lit 1))))

/-- One turn of the middle loop: load the mid vertex and its row, and
scan it. -/
def trMid (o t rt mk : String) : Com :=
  .seq (.assign "tr.w" (.get t (.var "tr.j")))
    (.seq (.assign "tr.k" (.get o (.var "tr.w")))
      (.seq (.assign "tr.f" (.get o (.add (.var "tr.w") (.lit 1))))
        (.seq (Csr.scan "tr.k" "tr.f" (trInner t rt mk))
          (.assign "tr.j" (.add (.var "tr.j") (.lit 1))))))

/-- One turn of the outer loop: anchor the head's offset, set its
matrix row base, load its row and scan it. -/
def trOuter (nN o t ro rt mk : String) : Com :=
  .seq (.store ro (.var "tr.v") (.var "tr.p"))
    (.seq (.assign "tr.b" (.mul (.var "tr.v") (.var nN)))
      (.seq (.assign "tr.j" (.get o (.var "tr.v")))
        (.seq (.assign "tr.e" (.get o (.add (.var "tr.v") (.lit 1))))
          (.seq (Csr.scan "tr.j" "tr.e" (trMid o t rt mk))
            (.assign "tr.v" (.add (.var "tr.v") (.lit 1)))))))

/-- **The pass**: zero the write pointer, run the three loops, close
the last offset and publish the slot count. -/
def trCom (nN nT o t ro rt mk : String) : Com :=
  .seq (.assign "tr.p" (.lit 0))
    (.seq (.assign "tr.v" (.lit 0))
      (.seq (Csr.scan "tr.v" nN (trOuter nN o t ro rt mk))
        (.seq (.store ro (.var nN) (.var "tr.p"))
          (.assign nT (.var "tr.p")))))

/-- **The pass's budget** at `(n, a, T)`, with `a = arcCount D` the
input's slot count and `T = transPairCount D` the size of the
enumeration.  `27` a head (the outer turn's fixed block and the loop
headers), `23` an arc (one middle turn, which loads a mid vertex and
its row bounds), `30` a transitive candidate (one inner turn: the read,
the matrix test and, when it fires, the two stores and the bump).
Linear in `n + arcCount D + transPairCount D`, and in nothing else —
no carrier scan per head and no sort. -/
def trK (n a T : ℕ) : ℕ := 27 * n + 23 * a + 30 * T + 13

/-! ## §6 The carried state

Three loops, three invariants, and the two halves both of the inner
ones carry: `TrDone`, the heads already finished (frozen for the whole
of a head's turn), and `TrCur`, the head under construction — its
emitted set, its slots of the target region and its row of the
matrix. -/

/-- What the pass has finished: the heads below `v`. -/
structure TrDone (ro rt mk : String) {n : ℕ} (D : Orientation n) (v w : ℕ)
    (σ : Env) : Prop where
  /-- Every offset below `w` is in place: the heads below `v`, and the
  head under construction as soon as its turn has anchored it. -/
  roGet : ∀ i, i < w → (σ.arrs ro)[i]? = some (trOff D i)
  /-- Every slot of a finished row holds a transitive in-neighbour. -/
  rtSound : ∀ a : Fin n, (a : ℕ) < v → ∀ q, trOff D (a : ℕ) ≤ q → q < trOff D ((a : ℕ) + 1) →
    ∃ h : (σ.arrs rt).getD q 0 < n, TransLink D ⟨(σ.arrs rt).getD q 0, h⟩ a
  /-- Every transitive in-neighbour of a finished head is in a slot. -/
  rtComplete : ∀ a : Fin n, (a : ℕ) < v → ∀ u : Fin n, TransLink D u a →
    ∃ q, trOff D (a : ℕ) ≤ q ∧ q < trOff D ((a : ℕ) + 1) ∧ (σ.arrs rt).getD q 0 = (u : ℕ)
  /-- No finished row repeats a target. -/
  rtInj : ∀ a : Fin n, (a : ℕ) < v → ∀ q r, trOff D (a : ℕ) ≤ q → q < trOff D ((a : ℕ) + 1) →
    trOff D (a : ℕ) ≤ r → r < trOff D ((a : ℕ) + 1) →
    (σ.arrs rt).getD q 0 = (σ.arrs rt).getD r 0 → q = r
  /-- A finished head's matrix row is the relation at that head. -/
  mkDone : ∀ a : Fin n, (a : ℕ) < v → ∀ u : Fin n,
    (σ.arrs mk).getD ((a : ℕ) * n + (u : ℕ)) 0 = if u ∈ trIn D a then 1 else 0
  /-- Every matrix row from `w` on is still clear. -/
  mkZero : ∀ a : Fin n, w ≤ (a : ℕ) → ∀ u : Fin n,
    (σ.arrs mk).getD ((a : ℕ) * n + (u : ℕ)) 0 = 0

/-- The head under construction: its emitted set `E`, the slots
`[trOff D v, p)` of the target region and its row of the matrix. -/
structure TrCur (rt mk : String) {n : ℕ} (D : Orientation n) (v : ℕ)
    (E : Finset (Fin n)) (p : ℕ) (σ : Env) : Prop where
  /-- One slot per emitted candidate. -/
  card : p = trOff D v + E.card
  /-- Every slot written holds an emitted candidate. -/
  sound : ∀ q, trOff D v ≤ q → q < p →
    ∃ h : (σ.arrs rt).getD q 0 < n, (⟨(σ.arrs rt).getD q 0, h⟩ : Fin n) ∈ E
  /-- Every emitted candidate has a slot. -/
  complete : ∀ u ∈ E, ∃ q, trOff D v ≤ q ∧ q < p ∧ (σ.arrs rt).getD q 0 = (u : ℕ)
  /-- No slot is written twice. -/
  inj : ∀ q r, trOff D v ≤ q → q < p → trOff D v ≤ r → r < p →
    (σ.arrs rt).getD q 0 = (σ.arrs rt).getD r 0 → q = r
  /-- The head's matrix row is the emitted set. -/
  mark : ∀ u : Fin n, (σ.arrs mk).getD (v * n + (u : ℕ)) 0 = if u ∈ E then 1 else 0

/-- What every state of the pass satisfies: the input CSR, the carrier
cell, and the three allocations. -/
structure TrFrame (nN o t ro rt mk : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The input CSR, untouched. -/
  csr : TrInCsr o t D ns off tgt σ
  /-- The carrier size is in its cell. -/
  carrier : σ.vars nN = n
  /-- The offset region. -/
  roLen : n + 1 ≤ (σ.arrs ro).length
  /-- The target region, sized by the enumeration. -/
  rtLen : transPairCount D ≤ (σ.arrs rt).length
  /-- The matrix region. -/
  mkLen : n * n ≤ (σ.arrs mk).length

/-! ### The emitted sets sit inside the head's row -/

theorem trEmDone_mono {v j j' z : ℕ} (h : TrEmDone off tgt v j z) (hj : j ≤ j') :
    TrEmDone off tgt v j' z := by
  obtain ⟨s, h1, h2, hr⟩ := h; exact ⟨s, h1, by omega, hr⟩

variable {o t : String} {ns : ℕ} {D : Orientation n} {σ : Env}

/-- `trEmD_row_end` at a plain index, which is how the loops carry it. -/
theorem TrInCsr.trEmD_row_end' (h : TrInCsr o t D ns off tgt σ) {v : ℕ} (hv : v < n) :
    trEmD n off tgt v (off (v + 1)) = trIn D ⟨v, hv⟩ := h.trEmD_row_end ⟨v, hv⟩

theorem trEmK_subset (h : TrInCsr o t D ns off tgt σ) {v j k : ℕ} (hv : v < n)
    (hj1 : off v ≤ j) (hj2 : j < off (v + 1)) (hk : k ≤ off (tgt j + 1)) :
    trEmK n off tgt v j k ⊆ trIn D ⟨v, hv⟩ := by
  intro u hu
  rw [← h.trEmD_row_end' hv]
  rcases mem_trEmK.1 hu with hd | hp
  · exact mem_trEmD.2 (trEmDone_mono hd (by omega))
  · obtain ⟨r, hr1, hr2, hr3⟩ := hp
    have hd' : TrEmDone off tgt v (j + 1) (u : ℕ) :=
      (trEmDone_succ hj1).2 (Or.inr ⟨r, hr1, by omega, hr3⟩)
    exact mem_trEmD.2 (trEmDone_mono hd' (by omega))

/-! ### The names the pass keeps apart -/

/-- The two input regions and the three output regions are five
distinct arrays. -/
structure TrNames (o t ro rt mk : String) : Prop where
  /-- The input offsets are not an output region. -/
  o_ro : o ≠ ro
  /-- … -/
  o_rt : o ≠ rt
  /-- … -/
  o_mk : o ≠ mk
  /-- The input targets are not an output region. -/
  t_ro : t ≠ ro
  /-- … -/
  t_rt : t ≠ rt
  /-- … -/
  t_mk : t ≠ mk
  /-- The three output regions are distinct. -/
  ro_rt : ro ≠ rt
  /-- … -/
  ro_mk : ro ≠ mk
  /-- … -/
  rt_mk : rt ≠ mk

/-! ### The three invariants -/

/-- The innermost loop's carried state, at head `v` and slot `j` of
`v`'s row. -/
structure TrIInv (nN o t ro rt mk : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (v j : ℕ) (σ : Env) : Prop where
  /-- The ambient reading. -/
  frame : TrFrame nN o t ro rt mk D ns off tgt σ
  /-- The heads below `v`; the matrix is clear above `v`. -/
  done : TrDone ro rt mk D v (v + 1) σ
  /-- The head is a vertex. -/
  vlt : v < n
  /-- The head is in its cell. -/
  vval : σ.vars "tr.v" = v
  /-- The matrix row base. -/
  bval : σ.vars "tr.b" = v * n
  /-- The head's row end. -/
  endv : σ.vars "tr.e" = off (v + 1)
  /-- The slot pointer of the head's row. -/
  jval : σ.vars "tr.j" = j
  /-- … inside the head's row. -/
  jlo : off v ≤ j
  /-- … -/
  jhi : j < off (v + 1)
  /-- The mid vertex. -/
  wval : σ.vars "tr.w" = tgt j
  /-- The mid vertex's row end. -/
  fval : σ.vars "tr.f" = off (tgt j + 1)
  /-- The slot pointer inside the mid vertex's row. -/
  klo : off (tgt j) ≤ σ.vars "tr.k"
  /-- … -/
  khi : σ.vars "tr.k" ≤ off (tgt j + 1)
  /-- The head under construction. -/
  cur : TrCur rt mk D v (trEmK n off tgt v j (σ.vars "tr.k")) (σ.vars "tr.p") σ

/-- The middle loop's carried state, at head `v`. -/
structure TrMInv (nN o t ro rt mk : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (v : ℕ) (σ : Env) : Prop where
  /-- The ambient reading. -/
  frame : TrFrame nN o t ro rt mk D ns off tgt σ
  /-- The heads below `v`; the matrix is clear above `v`. -/
  done : TrDone ro rt mk D v (v + 1) σ
  /-- The head is a vertex. -/
  vlt : v < n
  /-- The head is in its cell. -/
  vval : σ.vars "tr.v" = v
  /-- The matrix row base. -/
  bval : σ.vars "tr.b" = v * n
  /-- The head's row end. -/
  endv : σ.vars "tr.e" = off (v + 1)
  /-- The slot pointer stays in the head's row. -/
  jlo : off v ≤ σ.vars "tr.j"
  /-- … -/
  jhi : σ.vars "tr.j" ≤ off (v + 1)
  /-- The head under construction. -/
  cur : TrCur rt mk D v (trEmD n off tgt v (σ.vars "tr.j")) (σ.vars "tr.p") σ

/-- The outer loop's carried state. -/
structure TrOInv (nN o t ro rt mk : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The ambient reading. -/
  frame : TrFrame nN o t ro rt mk D ns off tgt σ
  /-- Every head below the counter is finished, and the matrix is
  clear from the counter on. -/
  done : TrDone ro rt mk D (σ.vars "tr.v") (σ.vars "tr.v") σ
  /-- The counter stays on the carrier. -/
  vle : σ.vars "tr.v" ≤ n
  /-- The write pointer is the counter's offset. -/
  pval : σ.vars "tr.p" = trOff D (σ.vars "tr.v")

/-! ### Small array and run helpers -/

private theorem getD_set_self {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem getD_set_of_ne {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c).getD q 0 = l.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

private theorem getElem?_of_lt (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem evB_var {B : ℕ} {y : String} {σ : Env} {c : ℕ} (hy : σ.vars y = c)
    (hc : c < B) : (Expr.var y).evalB B σ = some c := by
  subst hy; exact evalB_var hc

private theorem evB_add {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (h : a + b < B) :
    (Expr.add e f).evalB B σ = some (a + b) := evalB_bin he hf (by simpa using h)

private theorem evB_mul {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (h : a * b < B) :
    (Expr.mul e f).evalB B σ = some (a * b) := evalB_bin he hf (by simpa using h)

private theorem evB_get' {B : ℕ} {a : String} {i : Expr} {σ : Env} {q c : ℕ}
    (hi : i.evalB B σ = some q) (hq : q < (σ.arrs a).length)
    (hc : (σ.arrs a).getD q 0 = c) (hcB : c < B) :
    (Expr.get a i).evalB B σ = some c :=
  evalB_get hi (by rw [getElem?_of_lt _ _ hq, hc]) hcB

private theorem run_assign' {B : ℕ} {x : String} {e : Expr} {σ : Env} {c K : ℕ}
    (h : e.evalB B σ = some c) (hK : 1 + e.size ≤ K) :
    Run B (.assign x e) σ (σ.setVar x c) K := (Run.assign h).mono hK

private theorem run_store' {B : ℕ} {a : String} {i e : Expr} {σ : Env} {q c K : ℕ}
    (hi : i.evalB B σ = some q) (he : e.evalB B σ = some c)
    (hq : q < (σ.arrs a).length) (hK : 1 + i.size + e.size ≤ K) :
    Run B (.store a i e) σ (σ.setArr a q c) K := (Run.store hi he hq).mono hK

/-- The nine scratch names, as nine disequalities. -/
private theorem trScalars_ne {y : String} (h : y ∉ trScalars) :
    y ≠ "tr.v" ∧ y ≠ "tr.j" ∧ y ≠ "tr.e" ∧ y ≠ "tr.w" ∧ y ≠ "tr.k" ∧
      y ≠ "tr.f" ∧ y ≠ "tr.z" ∧ y ≠ "tr.p" ∧ y ≠ "tr.b" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro hc
      rw [hc] at h
      exact h (by simp [trScalars])

/-! ### The transport lemmas of the two halves -/

theorem TrDone.of_eq {ro rt mk : String} {n : ℕ} {D : Orientation n} {v w : ℕ}
    {σ σ' : Env} (h : TrDone ro rt mk D v w σ)
    (hro : σ'.arrs ro = σ.arrs ro) (hrt : σ'.arrs rt = σ.arrs rt)
    (hmk : σ'.arrs mk = σ.arrs mk) : TrDone ro rt mk D v w σ' where
  roGet := by rw [hro]; exact h.roGet
  rtSound := by rw [hrt]; exact h.rtSound
  rtComplete := by rw [hrt]; exact h.rtComplete
  rtInj := by rw [hrt]; exact h.rtInj
  mkDone := by rw [hmk]; exact h.mkDone
  mkZero := by rw [hmk]; exact h.mkZero

theorem TrCur.of_eq {rt mk : String} {n : ℕ} {D : Orientation n} {v : ℕ}
    {E : Finset (Fin n)} {p : ℕ} {σ σ' : Env} (h : TrCur rt mk D v E p σ)
    (hrt : σ'.arrs rt = σ.arrs rt) (hmk : σ'.arrs mk = σ.arrs mk) :
    TrCur rt mk D v E p σ' where
  card := h.card
  sound := by rw [hrt]; exact h.sound
  complete := by rw [hrt]; exact h.complete
  inj := by rw [hrt]; exact h.inj
  mark := by rw [hmk]; exact h.mark

theorem TrFrame.of_eq {nN o t ro rt mk : String} {n ns : ℕ} {D : Orientation n}
    {off tgt : ℕ → ℕ} {σ σ' : Env} (h : TrFrame nN o t ro rt mk D ns off tgt σ)
    (hnN : σ'.vars nN = σ.vars nN) (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t)
    (hro : σ'.arrs ro = σ.arrs ro) (hrt : (σ'.arrs rt).length = (σ.arrs rt).length)
    (hmk : (σ'.arrs mk).length = (σ.arrs mk).length) :
    TrFrame nN o t ro rt mk D ns off tgt σ' where
  csr := h.csr.of_eq ho ht
  carrier := by rw [hnN]; exact h.carrier
  roLen := by rw [hro]; exact h.roLen
  rtLen := by rw [hrt]; exact h.rtLen
  mkLen := by rw [hmk]; exact h.mkLen

/-- Two distinct matrix rows never share a cell. -/
theorem trRow_ne {n a b x y : ℕ} (_hb : b < n) (hx : x < n) (hy : y < n) (hab : a ≠ b) :
    a * n + x ≠ b * n + y := by
  rcases Nat.lt_or_ge a b with h | h
  · have h1 : (a + 1) * n ≤ b * n := Nat.mul_le_mul h (le_refl n)
    have h2 : (a + 1) * n = a * n + n := by ring
    omega
  · have hba : b < a := by omega
    have h1 : (b + 1) * n ≤ a * n := Nat.mul_le_mul hba (le_refl n)
    have h2 : (b + 1) * n = b * n + n := by ring
    omega

/-! ## §7 One turn of the innermost loop -/

/-- **One inner turn**, at `26`: read the candidate; if its matrix cell
is clear, set it and append the candidate; advance the slot pointer.
The matrix cell is both the dedup mark and the output, so the row comes
out deduplicated with nothing re-zeroed anywhere. -/
theorem trInner_step {B : ℕ} {nN o t ro rt mk : String}
    (hnm : TrNames o t ro rt mk) (hnN : nN ∉ trScalars)
    {n ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ} {v j : ℕ} {σ : Env}
    (hB : n + n * n + arcCount D + transPairCount D < B)
    (hI : TrIInv nN o t ro rt mk D ns off tgt v j σ)
    (hkk : σ.vars "tr.k" < off (tgt j + 1)) :
    ∃ σ' K', Run B (trInner t rt mk) σ σ' K' ∧
      TrIInv nN o t ro rt mk D ns off tgt v j σ' ∧
      σ'.vars "tr.k" = σ.vars "tr.k" + 1 ∧ K' ≤ 26 := by
  classical
  obtain ⟨-, -, -, -, hnk, -, hnz, hnp, -⟩ := trScalars_ne hnN
  have hcsr := hI.frame.csr
  have hvlt : v < n := hI.vlt
  have hnsarc : ns = arcCount D := hcsr.ns_eq_arcCount
  have hnsB : ns < B := by omega
  have hnB : n < B := by omega
  have hnnB : n * n < B := by omega
  obtain ⟨k, hk⟩ : ∃ k, σ.vars "tr.k" = k := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, σ.vars "tr.p" = p := ⟨_, rfl⟩
  have hklo : off (tgt j) ≤ k := by rw [← hk]; exact hI.klo
  have hkhi : k < off (tgt j + 1) := by rw [← hk]; exact hkk
  have hcur : TrCur rt mk D v (trEmK n off tgt v j k) p σ := by
    have h := hI.cur; rw [hk, hp] at h; exact h
  have hjns : j < ns := hcsr.row_lt_ns (v := ⟨v, hI.vlt⟩) hI.jhi
  have hwn : tgt j < n := hcsr.tgtLt j hjns
  have hkns : k < ns := hcsr.row_lt_ns (v := ⟨tgt j, hwn⟩) hkhi
  have hzn : tgt k < n := hcsr.tgtLt k hkns
  have htk : (σ.arrs t).getD k 0 = tgt k := hcsr.tgtGetD hkns
  have htLen : k < (σ.arrs t).length := lt_of_lt_of_le hkns hcsr.tgtLen
  have hidx : v * n + tgt k < n * n := by
    have h3 : (v + 1) * n ≤ n * n := Nat.mul_le_mul hI.vlt (le_refl n)
    have h2 : (v + 1) * n = v * n + n := by ring
    omega
  have hmkLen := hI.frame.mkLen
  have hidxLen : v * n + tgt k < (σ.arrs mk).length := by omega
  have hcell : (σ.arrs mk).getD (v * n + tgt k) 0
      = if (⟨tgt k, hzn⟩ : Fin n) ∈ trEmK n off tgt v j k then 1 else 0 :=
    hcur.mark ⟨tgt k, hzn⟩
  have hbB : v * n < B := by omega
  have hzB : tgt k < B := by omega
  have hkB : k < B := by omega
  have h1B : (1 : ℕ) < B := by omega
  have hv1 : ∀ y : String, y ≠ "tr.z" → (σ.setVar "tr.z" (tgt k)).vars y = σ.vars y := by
    intro y hy; simp [hy]
  have ha1 : (σ.setVar "tr.z" (tgt k)).arrs = σ.arrs := by simp
  have r1 : Run B (.assign "tr.z" (.get t (.var "tr.k"))) σ (σ.setVar "tr.z" (tgt k)) 3 :=
    run_assign' (evB_get' (evB_var hk hkB) htLen htk hzB) (by simp)
  have hb1 : (σ.setVar "tr.z" (tgt k)).vars "tr.b" = v * n := by
    rw [hv1 _ (by decide)]; exact hI.bval
  have hz1 : (σ.setVar "tr.z" (tgt k)).vars "tr.z" = tgt k := by simp
  have hk1 : (σ.setVar "tr.z" (tgt k)).vars "tr.k" = k := by
    rw [hv1 _ (by decide)]; exact hk
  have hp1 : (σ.setVar "tr.z" (tgt k)).vars "tr.p" = p := by
    rw [hv1 _ (by decide)]; exact hp
  have hiadd : (Expr.add (.var "tr.b") (.var "tr.z")).evalB B (σ.setVar "tr.z" (tgt k))
      = some (v * n + tgt k) :=
    evB_add (evB_var hb1 hbB) (evB_var hz1 hzB) (by omega)
  have hmkLen1 : v * n + tgt k < ((σ.setVar "tr.z" (tgt k)).arrs mk).length := by
    rw [ha1]; exact hidxLen
  have hlast : ∀ τ : Env, τ.vars "tr.k" = k →
      Run B (.assign "tr.k" (.add (.var "tr.k") (.lit 1))) τ (τ.setVar "tr.k" (k + 1)) 4 := by
    intro τ hτ
    exact run_assign' (evB_add (evB_var hτ hkB) (evalB_lit h1B) (by omega)) (by simp)
  by_cases hmem : (⟨tgt k, hzn⟩ : Fin n) ∈ trEmK n off tgt v j k
  · -- already emitted: the turn only advances the slot pointer
    have hcv : (σ.arrs mk).getD (v * n + tgt k) 0 = 1 := by rw [hcell, if_pos hmem]
    have hcond : (Cond.eq (.get mk (.add (.var "tr.b") (.var "tr.z"))) (.lit 0)).evalB B
        (σ.setVar "tr.z" (tgt k)) = some false := by
      have hg : (Expr.get mk (.add (.var "tr.b") (.var "tr.z"))).evalB B
          (σ.setVar "tr.z" (tgt k)) = some 1 :=
        evB_get' hiadd hmkLen1 (by rw [ha1]; exact hcv) h1B
      simpa using evalB_condEq hg (evalB_lit (show (0 : ℕ) < B by omega))
    have rite : Run B (.ite (.eq (.get mk (.add (.var "tr.b") (.var "tr.z"))) (.lit 0))
        (.seq (.store mk (.add (.var "tr.b") (.var "tr.z")) (.lit 1))
          (.seq (.store rt (.var "tr.p") (.var "tr.z"))
            (.assign "tr.p" (.add (.var "tr.p") (.lit 1))))) .skip)
        (σ.setVar "tr.z" (tgt k)) (σ.setVar "tr.z" (tgt k)) 8 :=
      (Run.ite_false hcond Run.skip).mono
        (by simp only [size_condEq, size_get, size_bin, size_var, size_lit]; omega)
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = (σ.setVar "tr.z" (tgt k)).setVar "tr.k" (k + 1) := ⟨_, rfl⟩
    have haa : τ.arrs = σ.arrs := by rw [hτ]; simp
    have hvv : ∀ y : String, y ≠ "tr.z" → y ≠ "tr.k" → τ.vars y = σ.vars y := by
      intro y h1 h2; rw [hτ]; simp [h1, h2]
    have hkv : τ.vars "tr.k" = k + 1 := by rw [hτ]; simp
    refine ⟨τ, 15, ?_, ?_, ?_, by omega⟩
    · rw [hτ]
      exact (r1.seq (rite.seq (hlast _ hk1))).mono (by omega)
    · exact
        { frame := hI.frame.of_eq (by rw [hvv _ hnz hnk]) (by rw [haa]) (by rw [haa])
            (by rw [haa]) (by rw [haa]) (by rw [haa])
          done := hI.done.of_eq (by rw [haa]) (by rw [haa]) (by rw [haa])
          vlt := hI.vlt
          vval := by rw [hvv _ (by decide) (by decide)]; exact hI.vval
          bval := by rw [hvv _ (by decide) (by decide)]; exact hI.bval
          endv := by rw [hvv _ (by decide) (by decide)]; exact hI.endv
          jval := by rw [hvv _ (by decide) (by decide)]; exact hI.jval
          jlo := hI.jlo
          jhi := hI.jhi
          wval := by rw [hvv _ (by decide) (by decide)]; exact hI.wval
          fval := by rw [hvv _ (by decide) (by decide)]; exact hI.fval
          klo := by rw [hkv]; omega
          khi := by rw [hkv]; omega
          cur := by
            rw [hkv, trEmK_succ_skip hklo hzn hmem, hvv _ (by decide) (by decide), hp]
            exact hcur.of_eq (by rw [haa]) (by rw [haa]) }
    · rw [hkv, hk]
  · -- a fresh candidate: mark the cell, append the target, bump the pointer
    have hcv : (σ.arrs mk).getD (v * n + tgt k) 0 = 0 := by rw [hcell, if_neg hmem]
    have hEsub : trEmK n off tgt v j k ⊆ trIn D ⟨v, hI.vlt⟩ :=
      trEmK_subset hcsr hI.vlt hI.jlo hI.jhi (le_of_lt hkhi)
    have hnew : (⟨tgt k, hzn⟩ : Fin n) ∈ trIn D ⟨v, hI.vlt⟩ := by
      refine trEmK_subset hcsr hI.vlt hI.jlo hI.jhi (j := j) (k := k + 1) hkhi ?_
      rw [trEmK_succ_emit hklo hzn]
      exact Finset.mem_insert_self _ _
    have hcardlt : (trEmK n off tgt v j k).card < (trIn D ⟨v, hI.vlt⟩).card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset hEsub).2 ⟨_, hnew, hmem⟩)
    have hdegv : trDeg D v = (trIn D ⟨v, hI.vlt⟩).card := by rw [trDeg, dif_pos hI.vlt]
    have hplt : p < trOff D (v + 1) := by
      have hc := hcur.card
      have hs := trOff_succ D v
      omega
    have hpn : p < trOff D n := lt_of_lt_of_le hplt (trOff_mono D (by omega))
    have hTle : trOff D n ≤ transPairCount D := trOff_le_transPairCount D
    have hrtLen := hI.frame.rtLen
    have hpLen : p < (σ.arrs rt).length := by omega
    have hpB : p + 1 < B := by omega
    have hpBB : p < B := by omega
    have hcond : (Cond.eq (.get mk (.add (.var "tr.b") (.var "tr.z"))) (.lit 0)).evalB B
        (σ.setVar "tr.z" (tgt k)) = some true := by
      have hg : (Expr.get mk (.add (.var "tr.b") (.var "tr.z"))).evalB B
          (σ.setVar "tr.z" (tgt k)) = some 0 :=
        evB_get' hiadd hmkLen1 (by rw [ha1]; exact hcv) (by omega)
      simpa using evalB_condEq hg (evalB_lit (show (0 : ℕ) < B by omega))
    have r2 : Run B (.store mk (.add (.var "tr.b") (.var "tr.z")) (.lit 1))
        (σ.setVar "tr.z" (tgt k))
        ((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1) 5 :=
      run_store' hiadd (evalB_lit h1B) hmkLen1 (by simp)
    have hmkrt : mk ≠ rt := Ne.symm hnm.rt_mk
    have hrt2 : ((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).arrs rt
        = σ.arrs rt := by simp [hnm.rt_mk]
    have hp2 : ((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).vars "tr.p" = p := by
      rw [vars_setArr]; exact hp1
    have hz2 : ((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).vars "tr.z"
        = tgt k := by rw [vars_setArr]; exact hz1
    have r3 : Run B (.store rt (.var "tr.p") (.var "tr.z"))
        ((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1)
        (((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).setArr rt p (tgt k)) 3 :=
      run_store' (evB_var hp2 hpBB) (evB_var hz2 hzB) (by rw [hrt2]; exact hpLen) (by simp)
    have hp3 : (((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).setArr rt p
        (tgt k)).vars "tr.p" = p := by rw [vars_setArr]; exact hp2
    have r4 : Run B (.assign "tr.p" (.add (.var "tr.p") (.lit 1)))
        (((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).setArr rt p (tgt k))
        ((((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).setArr rt p
          (tgt k)).setVar "tr.p" (p + 1)) 4 :=
      run_assign' (evB_add (evB_var hp3 hpBB) (evalB_lit h1B) (by omega)) (by simp)
    have hk4 : ((((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).setArr rt p
        (tgt k)).setVar "tr.p" (p + 1)).vars "tr.k" = k := by
      rw [vars_setVar, if_neg (by decide), vars_setArr, vars_setArr]; exact hk1
    have rbody : Run B (.seq (.store mk (.add (.var "tr.b") (.var "tr.z")) (.lit 1))
        (.seq (.store rt (.var "tr.p") (.var "tr.z"))
          (.assign "tr.p" (.add (.var "tr.p") (.lit 1)))))
        (σ.setVar "tr.z" (tgt k))
        ((((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).setArr rt p
          (tgt k)).setVar "tr.p" (p + 1)) 12 :=
      (r2.seq (r3.seq r4)).mono (by omega)
    have rite : Run B (.ite (.eq (.get mk (.add (.var "tr.b") (.var "tr.z"))) (.lit 0))
        (.seq (.store mk (.add (.var "tr.b") (.var "tr.z")) (.lit 1))
          (.seq (.store rt (.var "tr.p") (.var "tr.z"))
            (.assign "tr.p" (.add (.var "tr.p") (.lit 1))))) .skip)
        (σ.setVar "tr.z" (tgt k))
        ((((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k) 1).setArr rt p
          (tgt k)).setVar "tr.p" (p + 1)) 19 :=
      (Run.ite_true hcond rbody).mono
        (by simp only [size_condEq, size_get, size_bin, size_var, size_lit]; omega)
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = (((((σ.setVar "tr.z" (tgt k)).setArr mk (v * n + tgt k)
        1).setArr rt p (tgt k)).setVar "tr.p" (p + 1)).setVar "tr.k" (k + 1)) := ⟨_, rfl⟩
    have haMk : τ.arrs mk = (σ.arrs mk).set (v * n + tgt k) 1 := by
      rw [hτ]; simp [hmkrt]
    have haRt : τ.arrs rt = (σ.arrs rt).set p (tgt k) := by
      rw [hτ]; simp [hnm.rt_mk]
    have haO : ∀ a : String, a ≠ mk → a ≠ rt → τ.arrs a = σ.arrs a := by
      intro a h1 h2; rw [hτ]; simp [h1, h2]
    have hvK : τ.vars "tr.k" = k + 1 := by rw [hτ]; simp
    have hvP : τ.vars "tr.p" = p + 1 := by rw [hτ]; simp
    have hvO : ∀ y : String, y ≠ "tr.z" → y ≠ "tr.p" → y ≠ "tr.k" → τ.vars y = σ.vars y := by
      intro y h1 h2 h3; rw [hτ]; simp [h1, h2, h3]
    have hpv : trOff D v ≤ p := by have := hcur.card; omega
    refine ⟨τ, 26, ?_, ?_, ?_, le_rfl⟩
    · rw [hτ]
      exact (r1.seq (rite.seq (hlast _ hk4))).mono (by omega)
    · refine
        { frame := hI.frame.of_eq (hvO nN hnz hnp hnk) (haO o hnm.o_mk hnm.o_rt)
            (haO t hnm.t_mk hnm.t_rt) (haO ro hnm.ro_mk hnm.ro_rt)
            (by rw [haRt, List.length_set]) (by rw [haMk, List.length_set])
          done := ?_
          vlt := hI.vlt
          vval := by rw [hvO _ (by decide) (by decide) (by decide)]; exact hI.vval
          bval := by rw [hvO _ (by decide) (by decide) (by decide)]; exact hI.bval
          endv := by rw [hvO _ (by decide) (by decide) (by decide)]; exact hI.endv
          jval := by rw [hvO _ (by decide) (by decide) (by decide)]; exact hI.jval
          jlo := hI.jlo
          jhi := hI.jhi
          wval := by rw [hvO _ (by decide) (by decide) (by decide)]; exact hI.wval
          fval := by rw [hvO _ (by decide) (by decide) (by decide)]; exact hI.fval
          klo := by rw [hvK]; omega
          khi := by rw [hvK]; omega
          cur := ?_ }
      · -- the finished heads survive: nothing of theirs was written
        refine
          { roGet := by rw [haO ro hnm.ro_mk hnm.ro_rt]; exact hI.done.roGet
            rtSound := ?_, rtComplete := ?_, rtInj := ?_, mkDone := ?_, mkZero := ?_ }
        · intro a ha q hq1 hq2
          have h1 : trOff D ((a : ℕ) + 1) ≤ trOff D v := trOff_mono D (by omega)
          rw [haRt, getD_set_of_ne (show p ≠ q by omega)]
          exact hI.done.rtSound a ha q hq1 hq2
        · intro a ha u hu
          have h1 : trOff D ((a : ℕ) + 1) ≤ trOff D v := trOff_mono D (by omega)
          obtain ⟨q, hq1, hq2, hq3⟩ := hI.done.rtComplete a ha u hu
          exact ⟨q, hq1, hq2, by
            rw [haRt, getD_set_of_ne (show p ≠ q by omega)]; exact hq3⟩
        · intro a ha q r hq1 hq2 hr1 hr2 hqr
          have h1 : trOff D ((a : ℕ) + 1) ≤ trOff D v := trOff_mono D (by omega)
          rw [haRt, getD_set_of_ne (show p ≠ q by omega),
            getD_set_of_ne (show p ≠ r by omega)] at hqr
          exact hI.done.rtInj a ha q r hq1 hq2 hr1 hr2 hqr
        · intro a ha u
          rw [haMk, getD_set_of_ne (trRow_ne a.isLt hzn u.isLt (show v ≠ (a : ℕ) by omega))]
          exact hI.done.mkDone a ha u
        · intro a ha u
          rw [haMk, getD_set_of_ne (trRow_ne a.isLt hzn u.isLt (show v ≠ (a : ℕ) by omega))]
          exact hI.done.mkZero a ha u
      · -- the head under construction gains exactly the new candidate
        rw [hvK, hvP, trEmK_succ_emit hklo hzn]
        refine { card := ?_, sound := ?_, complete := ?_, inj := ?_, mark := ?_ }
        · rw [Finset.card_insert_of_notMem hmem]
          have := hcur.card; omega
        · intro q hq1 hq2
          rw [haRt]
          rcases Nat.lt_or_ge q p with hqp | hqp
          · rw [getD_set_of_ne (show p ≠ q by omega)]
            obtain ⟨h1, h2⟩ := hcur.sound q hq1 hqp
            exact ⟨h1, Finset.mem_insert_of_mem h2⟩
          · obtain rfl : p = q := by omega
            rw [getD_set_self hpLen]
            exact ⟨hzn, Finset.mem_insert_self _ _⟩
        · intro u hu
          rw [haRt]
          rcases Finset.mem_insert.1 hu with rfl | hu'
          · exact ⟨p, by omega, by omega, by rw [getD_set_self hpLen]⟩
          · obtain ⟨q, hq1, hq2, hq3⟩ := hcur.complete u hu'
            exact ⟨q, hq1, by omega, by
              rw [getD_set_of_ne (show p ≠ q by omega)]; exact hq3⟩
        · intro q r hq1 hq2 hr1 hr2 hqr
          rw [haRt] at hqr
          rcases Nat.lt_or_ge q p with hqp | hqp
          · rcases Nat.lt_or_ge r p with hrp | hrp
            · rw [getD_set_of_ne (show p ≠ q by omega),
                getD_set_of_ne (show p ≠ r by omega)] at hqr
              exact hcur.inj q r hq1 hqp hr1 hrp hqr
            · obtain rfl : p = r := by omega
              rw [getD_set_of_ne (show p ≠ q by omega), getD_set_self hpLen] at hqr
              obtain ⟨h1, h2⟩ := hcur.sound q hq1 hqp
              refine absurd ?_ hmem
              have heq : (⟨(σ.arrs rt).getD q 0, h1⟩ : Fin n) = ⟨tgt k, hzn⟩ := by
                ext; exact hqr
              rw [← heq]; exact h2
          · obtain rfl : p = q := by omega
            rcases Nat.lt_or_ge r p with hrp | hrp
            · rw [getD_set_self hpLen, getD_set_of_ne (show p ≠ r by omega)] at hqr
              obtain ⟨h1, h2⟩ := hcur.sound r hr1 hrp
              refine absurd ?_ hmem
              have heq : (⟨(σ.arrs rt).getD r 0, h1⟩ : Fin n) = ⟨tgt k, hzn⟩ := by
                ext; exact hqr.symm
              rw [← heq]; exact h2
            · omega
        · intro u
          rw [haMk]
          by_cases hu : u = (⟨tgt k, hzn⟩ : Fin n)
          · subst hu
            rw [getD_set_self hidxLen, if_pos (Finset.mem_insert_self _ _)]
          · have hne : (u : ℕ) ≠ tgt k := fun hc => hu (by ext; exact hc)
            rw [getD_set_of_ne (show v * n + tgt k ≠ v * n + (u : ℕ) by omega), hcur.mark u]
            simp [Finset.mem_insert, hu]
    · rw [hvK, hk]


/-! ## §8 The innermost scan -/

/-- **The innermost scan**: the mid vertex's row, one turn a slot, at
`30` a slot plus one last test. -/
theorem trInner_scan {B : ℕ} {nN o t ro rt mk : String}
    (hnm : TrNames o t ro rt mk) (hnN : nN ∉ trScalars)
    {n ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ} {v j : ℕ}
    (hB : n + n * n + arcCount D + transPairCount D < B)
    (hhi : off (tgt j + 1) < B) :
    Spec B (fun σ => TrIInv nN o t ro rt mk D ns off tgt v j σ ∧
        σ.vars "tr.k" = off (tgt j))
      (Csr.scan "tr.k" "tr.f" (trInner t rt mk))
      (fun _ σ' => TrIInv nN o t ro rt mk D ns off tgt v j σ' ∧
        σ'.vars "tr.k" = off (tgt j + 1))
      (30 * (off (tgt j + 1) - off (tgt j)) + 4) := by
  refine Csr.rowScan_spec B _ (off (tgt j + 1)) 26 "tr.k" "tr.f" (trInner t rt mk)
    (fun σ => TrIInv nN o t ro rt mk D ns off tgt v j σ) hhi
    (fun σ hI => ⟨hI.fval, hI.khi⟩) (fun σ hI hlt => trInner_step hnm hnN hB hI hlt)
    (fun σ h => h.1) (fun σ h => by have := h.2; omega)

/-! ## §9 One turn of the middle loop -/

/-- **One middle turn**, at `19 + 30·|inN w|`: load the mid vertex `w`
and its row bounds, scan its row, advance.  The `30`-a-slot term is the
inner scan's, and it is the term the budget's `transPairCount` pays. -/
theorem trMid_step {B : ℕ} {nN o t ro rt mk : String}
    (hnm : TrNames o t ro rt mk) (hnN : nN ∉ trScalars)
    {n ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ} {v : ℕ} {σ : Env}
    (hB : n + n * n + arcCount D + transPairCount D < B)
    (hM : TrMInv nN o t ro rt mk D ns off tgt v σ)
    (hjj : σ.vars "tr.j" < off (v + 1)) :
    ∃ σ' K', Run B (trMid o t rt mk) σ σ' K' ∧
      TrMInv nN o t ro rt mk D ns off tgt v σ' ∧
      σ'.vars "tr.j" = σ.vars "tr.j" + 1 ∧
      K' ≤ 19 + 30 * (off (tgt (σ.vars "tr.j") + 1) - off (tgt (σ.vars "tr.j"))) := by
  classical
  obtain ⟨-, hnj, -, hnw, hnk, hnf, -, -, -⟩ := trScalars_ne hnN
  have hcsr := hM.frame.csr
  have hvlt : v < n := hM.vlt
  have hnsarc : ns = arcCount D := hcsr.ns_eq_arcCount
  have hnsB : ns < B := by omega
  have hnB : n < B := by omega
  obtain ⟨j, hj⟩ : ∃ j, σ.vars "tr.j" = j := ⟨_, rfl⟩
  have hjlo : off v ≤ j := by rw [← hj]; exact hM.jlo
  have hjhi : j < off (v + 1) := by rw [← hj]; exact hjj
  have hjns : j < ns := hcsr.row_lt_ns (v := ⟨v, hvlt⟩) hjhi
  have hwn : tgt j < n := hcsr.tgtLt j hjns
  have hoLenT : j < (σ.arrs t).length := lt_of_lt_of_le hjns hcsr.tgtLen
  have htj : (σ.arrs t).getD j 0 = tgt j := hcsr.tgtGetD hjns
  have hoLen : n + 1 ≤ (σ.arrs o).length := hcsr.offLen
  have howj : (σ.arrs o).getD (tgt j) 0 = off (tgt j) := hcsr.offGetD (le_of_lt hwn)
  have howj1 : (σ.arrs o).getD (tgt j + 1) 0 = off (tgt j + 1) := hcsr.offGetD hwn
  have hoffw : off (tgt j) ≤ off (tgt j + 1) := hcsr.mono (tgt j + 1) hwn (tgt j) (by omega)
  have hoffw1 : off (tgt j + 1) ≤ ns := hcsr.off_le_ns hwn
  have hjB : j < B := by omega
  have hwB : tgt j < B := by omega
  have hofB : off (tgt j + 1) < B := by omega
  have hokB : off (tgt j) < B := by omega
  have h1B : (1 : ℕ) < B := by omega
  have hjLenO : tgt j < (σ.arrs o).length := by omega
  have hj1LenO : tgt j + 1 < (σ.arrs o).length := by omega
  have r1 : Run B (.assign "tr.w" (.get t (.var "tr.j"))) σ (σ.setVar "tr.w" (tgt j)) 3 :=
    run_assign' (evB_get' (evB_var hj hjB) hoLenT htj hwB) (by simp)
  have hw1 : (σ.setVar "tr.w" (tgt j)).vars "tr.w" = tgt j := by simp
  have hao1 : (σ.setVar "tr.w" (tgt j)).arrs = σ.arrs := by simp
  have r2 : Run B (.assign "tr.k" (.get o (.var "tr.w"))) (σ.setVar "tr.w" (tgt j))
      ((σ.setVar "tr.w" (tgt j)).setVar "tr.k" (off (tgt j))) 3 :=
    run_assign' (evB_get' (evB_var hw1 hwB) (by rw [hao1]; exact hjLenO)
      (by rw [hao1]; exact howj) hokB) (by simp)
  have hw2 : ((σ.setVar "tr.w" (tgt j)).setVar "tr.k" (off (tgt j))).vars "tr.w" = tgt j := by
    simp
  have hao2 : ((σ.setVar "tr.w" (tgt j)).setVar "tr.k" (off (tgt j))).arrs = σ.arrs := by simp
  obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = (((σ.setVar "tr.w" (tgt j)).setVar "tr.k"
      (off (tgt j))).setVar "tr.f" (off (tgt j + 1))) := ⟨_, rfl⟩
  have r3 : Run B (.assign "tr.f" (.get o (.add (.var "tr.w") (.lit 1))))
      ((σ.setVar "tr.w" (tgt j)).setVar "tr.k" (off (tgt j))) τ3 5 := by
    rw [hτ3]
    exact run_assign' (evB_get' (evB_add (evB_var hw2 hwB) (evalB_lit h1B) (by omega))
      (by rw [hao2]; exact hj1LenO) (by rw [hao2]; exact howj1) hofB) (by simp)
  have ha3 : τ3.arrs = σ.arrs := by rw [hτ3]; simp
  have hv3 : ∀ y : String, y ≠ "tr.w" → y ≠ "tr.k" → y ≠ "tr.f" → τ3.vars y = σ.vars y := by
    intro y h1 h2 h3; rw [hτ3]; simp [h1, h2, h3]
  have hw3 : τ3.vars "tr.w" = tgt j := by rw [hτ3]; simp
  have hk3 : τ3.vars "tr.k" = off (tgt j) := by rw [hτ3]; simp
  have hf3 : τ3.vars "tr.f" = off (tgt j + 1) := by rw [hτ3]; simp
  have hI3 : TrIInv nN o t ro rt mk D ns off tgt v j τ3 :=
    { frame := hM.frame.of_eq (hv3 nN hnw hnk hnf) (by rw [ha3]) (by rw [ha3]) (by rw [ha3])
        (by rw [ha3]) (by rw [ha3])
      done := hM.done.of_eq (by rw [ha3]) (by rw [ha3]) (by rw [ha3])
      vlt := hvlt
      vval := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hM.vval
      bval := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hM.bval
      endv := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hM.endv
      jval := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hj
      jlo := hjlo
      jhi := hjhi
      wval := hw3
      fval := hf3
      klo := le_of_eq hk3.symm
      khi := by rw [hk3]; exact hoffw
      cur := by
        rw [hk3, trEmK_start, hv3 _ (by decide) (by decide) (by decide)]
        have h := hM.cur
        rw [hj] at h
        exact h.of_eq (by rw [ha3]) (by rw [ha3]) }
  obtain ⟨τ4, hrun4, hI4, hk4⟩ :=
    (trInner_scan (v := v) (j := j) hnm hnN hB hofB).run ⟨hI3, hk3⟩
  have hj4 : τ4.vars "tr.j" = j := hI4.jval
  obtain ⟨τ5, hτ5⟩ : ∃ τ, τ = τ4.setVar "tr.j" (j + 1) := ⟨_, rfl⟩
  have r5 : Run B (.assign "tr.j" (.add (.var "tr.j") (.lit 1))) τ4 τ5 4 := by
    rw [hτ5]
    exact run_assign' (evB_add (evB_var hj4 hjB) (evalB_lit h1B) (by omega)) (by simp)
  have ha5 : τ5.arrs = τ4.arrs := by rw [hτ5]; simp
  have hv5 : ∀ y : String, y ≠ "tr.j" → τ5.vars y = τ4.vars y := by
    intro y h1; rw [hτ5]; simp [h1]
  have hj5 : τ5.vars "tr.j" = j + 1 := by rw [hτ5]; simp
  refine ⟨τ5, 19 + 30 * (off (tgt j + 1) - off (tgt j)), ?_, ?_, ?_, by rw [hj]⟩
  · exact (r1.seq (r2.seq (r3.seq (hrun4.seq r5)))).mono (by omega)
  · exact
      { frame := hI4.frame.of_eq (hv5 nN hnj) (by rw [ha5]) (by rw [ha5]) (by rw [ha5])
          (by rw [ha5]) (by rw [ha5])
        done := hI4.done.of_eq (by rw [ha5]) (by rw [ha5]) (by rw [ha5])
        vlt := hvlt
        vval := by rw [hv5 _ (by decide)]; exact hI4.vval
        bval := by rw [hv5 _ (by decide)]; exact hI4.bval
        endv := by rw [hv5 _ (by decide)]; exact hI4.endv
        jlo := by rw [hj5]; omega
        jhi := by rw [hj5]; omega
        cur := by
          rw [hj5, ← trEmK_end hjlo, hv5 _ (by decide)]
          have h := hI4.cur
          rw [hk4] at h
          exact h.of_eq (by rw [ha5]) (by rw [ha5]) }
  · rw [hj5, hj]

/-! ## §10 The middle scan -/

/-- **The middle scan**: the head's row of the input, one turn a slot,
at `23` a slot and `30` a transitive candidate — the amortization that
turns a nested loop into a linear charge. -/
theorem trMid_scan {B : ℕ} {nN o t ro rt mk : String}
    (hnm : TrNames o t ro rt mk) (hnN : nN ∉ trScalars)
    {n ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ} {v : ℕ}
    (hB : n + n * n + arcCount D + transPairCount D < B) :
    Spec B (fun σ => TrMInv nN o t ro rt mk D ns off tgt v σ ∧ σ.vars "tr.j" = off v)
      (Csr.scan "tr.j" "tr.e" (trMid o t rt mk))
      (fun _ σ' => TrMInv nN o t ro rt mk D ns off tgt v σ' ∧ σ'.vars "tr.j" = off (v + 1))
      (23 * (off (v + 1) - off v) + 30 * trRow off tgt v + 4) := by
  have hbound : ∀ σ : Env, TrMInv nN o t ro rt mk D ns off tgt v σ →
      σ.vars "tr.j" < B ∧ σ.vars "tr.e" < B := by
    intro σ hM
    have hcsr := hM.frame.csr
    have hnsarc : ns = arcCount D := hcsr.ns_eq_arcCount
    have h1 : off (v + 1) ≤ ns := hcsr.off_le_ns hM.vlt
    have h2 := hM.jhi
    have h3 := hM.endv
    exact ⟨by omega, by omega⟩
  refine (Spec.while_potential (b := .lt (.var "tr.j") (.var "tr.e"))
    (fun σ => TrMInv nN o t ro rt mk D ns off tgt v σ)
    (fun σ => 23 * (off (v + 1) - σ.vars "tr.j") + 30 * trRest off tgt v (σ.vars "tr.j"))
    (fun σ hM => evalB_condLt_vars (hbound σ hM).1 (hbound σ hM).2) ?_ (fun σ h => h.1)
    ?_).post ?_
  · intro σ hM hc
    have hlt : σ.vars "tr.j" < off (v + 1) := by
      have h1 := lt_of_condLt_true hc
      have h2 := hM.endv
      omega
    obtain ⟨σ', K', hrun, hM', hj', hK'⟩ := trMid_step hnm hnN hB hM hlt
    refine ⟨σ', K', hrun, hM', ?_⟩
    have hsplit := trRest_succ (off := off) (tgt := tgt) (v := v) hlt
    simp only [size_condLt, size_var]
    rw [hj']
    omega
  · intro σ h
    have hj := h.2
    have : trRest off tgt v (off v) = trRow off tgt v := rfl
    simp only [size_condLt, size_var]
    rw [hj]
    omega
  · rintro σ σ' - ⟨hM', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hM'.endv
    have h3 := hM'.jhi
    exact ⟨hM', by omega⟩


/-! ## §11 One turn of the outer loop -/

/-- **Closing a head**: with its row scanned to the end, the head's
emitted set is exactly its transitive in-neighbourhood, so it joins the
finished part. -/
theorem trDone_succ {ro rt mk : String} {n : ℕ} {D : Orientation n} {v : ℕ} {σ : Env}
    (hvlt : v < n) (hd : TrDone ro rt mk D v (v + 1) σ)
    (hc : TrCur rt mk D v (trIn D ⟨v, hvlt⟩) (trOff D (v + 1)) σ) :
    TrDone ro rt mk D (v + 1) (v + 1) σ := by
  refine { roGet := hd.roGet, rtSound := ?_, rtComplete := ?_, rtInj := ?_,
           mkDone := ?_, mkZero := hd.mkZero }
  · intro a ha q hq1 hq2
    rcases Nat.lt_or_ge (a : ℕ) v with h | h
    · exact hd.rtSound a h q hq1 hq2
    · obtain rfl : a = (⟨v, hvlt⟩ : Fin n) :=
        Fin.val_injective (show (a : ℕ) = v by omega)
      obtain ⟨h1, h2⟩ := hc.sound q hq1 hq2
      exact ⟨h1, mem_trIn.1 h2⟩
  · intro a ha u hu
    rcases Nat.lt_or_ge (a : ℕ) v with h | h
    · exact hd.rtComplete a h u hu
    · obtain rfl : a = (⟨v, hvlt⟩ : Fin n) :=
        Fin.val_injective (show (a : ℕ) = v by omega)
      exact hc.complete u (mem_trIn.2 hu)
  · intro a ha q r hq1 hq2 hr1 hr2 hqr
    rcases Nat.lt_or_ge (a : ℕ) v with h | h
    · exact hd.rtInj a h q r hq1 hq2 hr1 hr2 hqr
    · obtain rfl : a = (⟨v, hvlt⟩ : Fin n) :=
        Fin.val_injective (show (a : ℕ) = v by omega)
      exact hc.inj q r hq1 hq2 hr1 hr2 hqr
  · intro a ha u
    rcases Nat.lt_or_ge (a : ℕ) v with h | h
    · exact hd.mkDone a h u
    · obtain rfl : a = (⟨v, hvlt⟩ : Fin n) :=
        Fin.val_injective (show (a : ℕ) = v by omega)
      exact hc.mark u

/-- **One outer turn**, at `23 + 23·|inN v| + 30·(candidates at v)`:
anchor the head's offset, set its matrix row base, load its row and
scan it. -/
theorem trOuter_step {B : ℕ} {nN o t ro rt mk : String}
    (hnm : TrNames o t ro rt mk) (hnN : nN ∉ trScalars)
    {n ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ} {σ : Env}
    (hB : n + n * n + arcCount D + transPairCount D < B)
    (hO : TrOInv nN o t ro rt mk D ns off tgt σ)
    (hvv : σ.vars "tr.v" < n) :
    ∃ σ' K', Run B (trOuter nN o t ro rt mk) σ σ' K' ∧
      TrOInv nN o t ro rt mk D ns off tgt σ' ∧
      σ'.vars "tr.v" = σ.vars "tr.v" + 1 ∧
      K' ≤ 23 + 23 * (off (σ.vars "tr.v" + 1) - off (σ.vars "tr.v"))
        + 30 * trRow off tgt (σ.vars "tr.v") := by
  classical
  obtain ⟨hnv, hnj, hnee, -, -, -, -, -, hnb⟩ := trScalars_ne hnN
  have hcsr := hO.frame.csr
  have hnsarc : ns = arcCount D := hcsr.ns_eq_arcCount
  have hnsB : ns < B := by omega
  have hnB : n < B := by omega
  have hnnB : n * n < B := by omega
  obtain ⟨v, hv⟩ : ∃ v, σ.vars "tr.v" = v := ⟨_, rfl⟩
  have hvlt : v < n := by rw [← hv]; exact hvv
  have hpv : σ.vars "tr.p" = trOff D v := by rw [hO.pval, hv]
  have hdone : TrDone ro rt mk D v v σ := by have h := hO.done; rw [hv] at h; exact h
  have hoffv : off v ≤ off (v + 1) := hcsr.mono (v + 1) hvlt v (by omega)
  have hoff1 : off (v + 1) ≤ ns := hcsr.off_le_ns hvlt
  have hov : (σ.arrs o).getD v 0 = off v := hcsr.offGetD (le_of_lt hvlt)
  have hov1 : (σ.arrs o).getD (v + 1) 0 = off (v + 1) := hcsr.offGetD hvlt
  have hoLen : n + 1 ≤ (σ.arrs o).length := hcsr.offLen
  have hroLen : n + 1 ≤ (σ.arrs ro).length := hO.frame.roLen
  have hpT : trOff D v ≤ trOff D n := trOff_mono D (le_of_lt hvlt)
  have hTle : trOff D n ≤ transPairCount D := trOff_le_transPairCount D
  have hvn : v * n ≤ n * n := Nat.mul_le_mul (le_of_lt hvlt) (le_refl n)
  have hvB : v < B := by omega
  have h1B : (1 : ℕ) < B := by omega
  have hpB : trOff D v < B := by omega
  have hvnB : v * n < B := by omega
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setArr ro v (trOff D v) := ⟨_, rfl⟩
  obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "tr.b" (v * n) := ⟨_, rfl⟩
  obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = τ2.setVar "tr.j" (off v) := ⟨_, rfl⟩
  obtain ⟨τ4, hτ4⟩ : ∃ τ, τ = τ3.setVar "tr.e" (off (v + 1)) := ⟨_, rfl⟩
  have h1v : τ1.vars = σ.vars := by rw [hτ1]; simp
  have h1a : ∀ a : String, a ≠ ro → τ1.arrs a = σ.arrs a := by
    intro a ha; rw [hτ1]; simp [ha]
  have h2v : ∀ y : String, y ≠ "tr.b" → τ2.vars y = σ.vars y := by
    intro y h; rw [hτ2, hτ1]; simp [h]
  have h2a : ∀ a : String, a ≠ ro → τ2.arrs a = σ.arrs a := by
    intro a ha; rw [hτ2, hτ1]; simp [ha]
  have h3v : ∀ y : String, y ≠ "tr.b" → y ≠ "tr.j" → τ3.vars y = σ.vars y := by
    intro y h h'; rw [hτ3, hτ2, hτ1]; simp [h, h']
  have h3a : ∀ a : String, a ≠ ro → τ3.arrs a = σ.arrs a := by
    intro a ha; rw [hτ3, hτ2, hτ1]; simp [ha]
  have h4v : ∀ y : String, y ≠ "tr.b" → y ≠ "tr.j" → y ≠ "tr.e" → τ4.vars y = σ.vars y := by
    intro y h1 h2 h3; rw [hτ4, hτ3, hτ2, hτ1]; simp [h1, h2, h3]
  have h4b : τ4.vars "tr.b" = v * n := by rw [hτ4, hτ3, hτ2]; simp
  have h4j : τ4.vars "tr.j" = off v := by rw [hτ4, hτ3]; simp
  have h4e : τ4.vars "tr.e" = off (v + 1) := by rw [hτ4]; simp
  have h4a : ∀ a : String, a ≠ ro → τ4.arrs a = σ.arrs a := by
    intro a ha; rw [hτ4, hτ3, hτ2, hτ1]; simp [ha]
  have h4ro : τ4.arrs ro = (σ.arrs ro).set v (trOff D v) := by
    rw [hτ4, hτ3, hτ2, hτ1]; simp
  have r1 : Run B (.store ro (.var "tr.v") (.var "tr.p")) σ τ1 3 := by
    rw [hτ1]; exact run_store' (evB_var hv hvB) (evB_var hpv hpB) (by omega) (by simp)
  have r2 : Run B (.assign "tr.b" (.mul (.var "tr.v") (.var nN))) τ1 τ2 4 := by
    rw [hτ2]
    exact run_assign' (evB_mul (evB_var (by rw [h1v]; exact hv) hvB)
      (evB_var (by rw [h1v]; exact hO.frame.carrier) hnB) (by omega)) (by simp)
  have r3 : Run B (.assign "tr.j" (.get o (.var "tr.v"))) τ2 τ3 3 := by
    rw [hτ3]
    exact run_assign' (evB_get' (evB_var (by rw [h2v _ (by decide)]; exact hv) hvB)
      (by rw [h2a o hnm.o_ro]; omega) (by rw [h2a o hnm.o_ro]; exact hov) (by omega)) (by simp)
  have r4 : Run B (.assign "tr.e" (.get o (.add (.var "tr.v") (.lit 1)))) τ3 τ4 5 := by
    rw [hτ4]
    exact run_assign' (evB_get'
      (evB_add (evB_var (by rw [h3v _ (by decide) (by decide)]; exact hv) hvB)
        (evalB_lit h1B) (by omega))
      (by rw [h3a o hnm.o_ro]; omega) (by rw [h3a o hnm.o_ro]; exact hov1)
      (by omega)) (by simp)
  have hM4 : TrMInv nN o t ro rt mk D ns off tgt v τ4 :=
    { frame :=
        { csr := hcsr.of_eq (h4a o hnm.o_ro) (h4a t hnm.t_ro)
          carrier := by rw [h4v nN hnb hnj hnee]; exact hO.frame.carrier
          roLen := by rw [h4ro, List.length_set]; exact hroLen
          rtLen := by rw [h4a rt (Ne.symm hnm.ro_rt)]; exact hO.frame.rtLen
          mkLen := by rw [h4a mk (Ne.symm hnm.ro_mk)]; exact hO.frame.mkLen }
      done :=
        { roGet := by
            intro i hi
            rw [h4ro]
            rcases Nat.lt_or_ge i v with h | h
            · rw [List.getElem?_set_ne (show v ≠ i by omega)]
              exact hdone.roGet i h
            · obtain rfl : i = v := by omega
              rw [List.getElem?_set_self (by omega)]
          rtSound := by rw [h4a rt (Ne.symm hnm.ro_rt)]; exact hdone.rtSound
          rtComplete := by rw [h4a rt (Ne.symm hnm.ro_rt)]; exact hdone.rtComplete
          rtInj := by rw [h4a rt (Ne.symm hnm.ro_rt)]; exact hdone.rtInj
          mkDone := by rw [h4a mk (Ne.symm hnm.ro_mk)]; exact hdone.mkDone
          mkZero := by
            intro a ha u
            rw [h4a mk (Ne.symm hnm.ro_mk)]
            exact hdone.mkZero a (by omega) u }
      vlt := hvlt
      vval := by rw [h4v _ (by decide) (by decide) (by decide)]; exact hv
      bval := h4b
      endv := h4e
      jlo := le_of_eq h4j.symm
      jhi := by rw [h4j]; exact hoffv
      cur := by
        rw [h4j, trEmD_empty, h4v _ (by decide) (by decide) (by decide), hpv]
        exact
          { card := by simp
            sound := by intro q h1 h2; exact absurd h2 (by omega)
            complete := by intro u hu; exact absurd hu (by simp)
            inj := by intro q r h1 h2 h3 h4 h5; exact absurd h2 (by omega)
            mark := by
              intro u
              rw [h4a mk (Ne.symm hnm.ro_mk), if_neg (by simp)]
              exact hdone.mkZero ⟨v, hvlt⟩ (le_refl v) u } }
  obtain ⟨τ5, hrun5, hM5, hj5⟩ := (trMid_scan (v := v) hnm hnN hB).run ⟨hM4, h4j⟩
  have hcur5' : TrCur rt mk D v (trIn D ⟨v, hvlt⟩) (τ5.vars "tr.p") τ5 := by
    have h := hM5.cur
    rw [hj5, hcsr.trEmD_row_end' hvlt] at h
    exact h
  have hp5 : τ5.vars "tr.p" = trOff D (v + 1) := by
    have hc := hcur5'.card
    have hd : trDeg D v = (trIn D ⟨v, hvlt⟩).card := by rw [trDeg, dif_pos hvlt]
    have hs := trOff_succ D v
    omega
  have hv5 : τ5.vars "tr.v" = v := hM5.vval
  obtain ⟨τ6, hτ6⟩ : ∃ τ, τ = τ5.setVar "tr.v" (v + 1) := ⟨_, rfl⟩
  have r6 : Run B (.assign "tr.v" (.add (.var "tr.v") (.lit 1))) τ5 τ6 4 := by
    rw [hτ6]
    exact run_assign' (evB_add (evB_var hv5 hvB) (evalB_lit h1B) (by omega)) (by simp)
  have h6a : ∀ a : String, τ6.arrs a = τ5.arrs a := by intro a; rw [hτ6]; simp
  have h6v : ∀ y : String, y ≠ "tr.v" → τ6.vars y = τ5.vars y := by
    intro y h; rw [hτ6]; simp [h]
  have h6vv : τ6.vars "tr.v" = v + 1 := by rw [hτ6]; simp
  refine ⟨τ6, 23 + 23 * (off (v + 1) - off v) + 30 * trRow off tgt v, ?_, ?_, ?_, by rw [hv]⟩
  · exact (r1.seq (r2.seq (r3.seq (r4.seq (hrun5.seq r6))))).mono (by omega)
  · exact
      { frame := hM5.frame.of_eq (h6v nN hnv) (h6a o) (h6a t) (h6a ro) (by rw [h6a])
          (by rw [h6a])
        done := by
          rw [h6vv]
          exact trDone_succ hvlt (hM5.done.of_eq (h6a ro) (h6a rt) (h6a mk))
            (by rw [← hp5]; exact hcur5'.of_eq (h6a rt) (h6a mk))
        vle := by rw [h6vv]; omega
        pval := by rw [h6vv, h6v _ (by decide)]; exact hp5 }
  · rw [h6vv, hv]

/-! ## §12 The outer scan -/

/-- **The outer scan**: one turn a head, at `27` a head, `23` an arc
and `30` a transitive candidate.  This is the whole pass's charge:
`O(n + arcCount D + transPairCount D)`, with no term in `n²` and no
carrier scan inside a head's turn. -/
theorem trOuter_scan {B : ℕ} {nN o t ro rt mk : String}
    (hnm : TrNames o t ro rt mk) (hnN : nN ∉ trScalars)
    {n ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ}
    (hB : n + n * n + arcCount D + transPairCount D < B) :
    Spec B (fun σ => TrOInv nN o t ro rt mk D ns off tgt σ ∧ σ.vars "tr.v" = 0)
      (Csr.scan "tr.v" nN (trOuter nN o t ro rt mk))
      (fun _ σ' => TrOInv nN o t ro rt mk D ns off tgt σ' ∧ σ'.vars "tr.v" = n)
      (27 * n + 23 * ns + 30 * trPref off tgt n + 4) := by
  have hbound : ∀ σ : Env, TrOInv nN o t ro rt mk D ns off tgt σ →
      σ.vars "tr.v" < B ∧ σ.vars nN < B := by
    intro σ hO
    have h1 := hO.vle
    have h2 := hO.frame.carrier
    exact ⟨by omega, by omega⟩
  refine (Spec.while_potential (b := .lt (.var "tr.v") (.var nN))
    (fun σ => TrOInv nN o t ro rt mk D ns off tgt σ)
    (fun σ => 27 * (n - σ.vars "tr.v") + 23 * (ns - off (σ.vars "tr.v"))
      + 30 * (trPref off tgt n - trPref off tgt (σ.vars "tr.v")))
    (fun σ hO => evalB_condLt_vars (hbound σ hO).1 (hbound σ hO).2) ?_ (fun σ h => h.1)
    ?_).post ?_
  · intro σ hO hc
    have hlt : σ.vars "tr.v" < n := by
      have h1 := lt_of_condLt_true hc
      have h2 := hO.frame.carrier
      omega
    obtain ⟨σ', K', hrun, hO', hv', hK'⟩ := trOuter_step hnm hnN hB hO hlt
    refine ⟨σ', K', hrun, hO', ?_⟩
    have hcsr := hO.frame.csr
    have hmono : off (σ.vars "tr.v") ≤ off (σ.vars "tr.v" + 1) :=
      hcsr.mono (σ.vars "tr.v" + 1) hlt (σ.vars "tr.v") (by omega)
    have hle : off (σ.vars "tr.v" + 1) ≤ ns := hcsr.off_le_ns hlt
    have hpref := trPref_succ (off := off) (tgt := tgt) (σ.vars "tr.v")
    have hprefn : trPref off tgt (σ.vars "tr.v" + 1) ≤ trPref off tgt n :=
      trPref_mono (by omega)
    simp only [size_condLt, size_var]
    rw [hv']
    omega
  · intro σ h
    have hz := h.2
    have hcsr := h.1.frame.csr
    have h0 : off 0 = 0 := hcsr.zero
    have hp0 : trPref off tgt 0 = 0 := by simp [trPref]
    have hpn : trPref off tgt 0 ≤ trPref off tgt n := trPref_mono (by omega)
    simp only [size_condLt, size_var]
    rw [hz, h0, hp0]
    omega
  · rintro σ σ' - ⟨hO', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hO'.frame.carrier
    have h3 := hO'.vle
    exact ⟨hO', by omega⟩


/-! ## §13 The contract, and the pass that meets it -/

theorem trRow_lt_sq {n a u : ℕ} (ha : a < n) (hu : u < n) : a * n + u < n * n := by
  have h1 : (a + 1) * n ≤ n * n := Nat.mul_le_mul ha (le_refl n)
  have h2 : (a + 1) * n = a * n + n := by ring
  omega

/-- **Every output slot has an owner**: the offsets partition
`[0, trOff D n)` into the heads' rows. -/
theorem trOff_owner {n : ℕ} (D : Orientation n) :
    ∀ m, m ≤ n → ∀ q, q < trOff D m →
      ∃ a : Fin n, trOff D (a : ℕ) ≤ q ∧ q < trOff D ((a : ℕ) + 1) := by
  intro m
  induction m with
  | zero => intro _ q hq; rw [trOff_zero] at hq; exact absurd hq (by omega)
  | succ m ih =>
      intro hm q hq
      rcases Nat.lt_or_ge q (trOff D m) with h | h
      · exact ih (by omega) q h
      · exact ⟨⟨m, by omega⟩, h, hq⟩

/-- **`TransCsrIn`**: from an in-neighbour CSR of `D` in `(o, t)` with
the carrier size in the cell `nN`, leave in `(ro, rt, mk)` a region
exactly characterising `TransLink D` in both directions, with the slot
count in `nT` and the input CSR untouched.  `kb` is the pass's budget
at `(n, arcCount D, transPairCount D)` — the three figures
`ProgCoverCharge.levelCharge` prices a greedy round by.  The word-bound
hypothesis is that all four figures the pass computes with are words:
`n + n² + arcCount D + transPairCount D < B` (`n²` because the matrix
index `v·n + u` is one).

The matrix region is asked to be **clear on entry**.  That is the
machine's own initial state (`Imp.lean:20-44`: memory starts zeroed and
an array of any length is there for free), so a per-level `n²` window
costs nothing to have and nothing to prepare.  A pass that re-zeroed
one shared window between rounds would be `O(n + nt)`, one store per
emitted candidate, by scanning the output CSR; it is named here and not
written. -/
def TransCsrIn (B : ℕ) (nN nT o t ro rt mk : String) (trC : Com)
    (kb : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} (D : Orientation n) (ns : ℕ) (off tgt : ℕ → ℕ),
    Spec B
      (fun σ => TrInCsr o t D ns off tgt σ ∧ σ.vars nN = n ∧
        n + n * n + arcCount D + transPairCount D < B ∧
        n + 1 ≤ (σ.arrs ro).length ∧ transPairCount D ≤ (σ.arrs rt).length ∧
        n * n ≤ (σ.arrs mk).length ∧ (∀ i, i < n * n → (σ.arrs mk).getD i 0 = 0))
      trC
      (fun _ σ' => TrInCsr o t D ns off tgt σ' ∧
        ∃ ttF, TransCsrAt ro rt mk D ttF σ' ∧ σ'.vars nT = trOff D n)
      (kb n (arcCount D) (transPairCount D))

/-- **`TransCsrIn`, discharged** by `trCom` at
`trK n a T = 27·n + 23·a + 30·T + 13`, with `a = arcCount D` the input
CSR's slot count and `T = transPairCount D` the size of the
enumeration.  `O(n + arcCount D + transPairCount D)` and nothing
else. -/
theorem transCsrIn_trCom {B : ℕ} {nN nT o t ro rt mk : String}
    (hnm : TrNames o t ro rt mk) (hnN : nN ∉ trScalars) :
    TransCsrIn B nN nT o t ro rt mk (trCom nN nT o t ro rt mk) trK := by
  intro n D ns off tgt
  refine Spec.of_exists (fun σ hσ => ?_)
  classical
  obtain ⟨hcsr, hcar, hB, hroL, hrtL, hmkL, hzero⟩ := hσ
  obtain ⟨hnv, -, -, -, -, -, -, hnp, -⟩ := trScalars_ne hnN
  have hnsarc : ns = arcCount D := hcsr.ns_eq_arcCount
  have hnsB : ns < B := by omega
  have hnB : n < B := by omega
  have hTeq : trPref off tgt n = transPairCount D := hcsr.trPref_eq
  have hTle : trOff D n ≤ transPairCount D := trOff_le_transPairCount D
  have h0B : (0 : ℕ) < B := by omega
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setVar "tr.p" 0 := ⟨_, rfl⟩
  obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "tr.v" 0 := ⟨_, rfl⟩
  have r1 : Run B (.assign "tr.p" (.lit 0)) σ τ1 2 := by
    rw [hτ1]; exact run_assign' (evalB_lit h0B) (by simp)
  have r2 : Run B (.assign "tr.v" (.lit 0)) τ1 τ2 2 := by
    rw [hτ2]; exact run_assign' (evalB_lit h0B) (by simp)
  have h2a : τ2.arrs = σ.arrs := by rw [hτ2, hτ1]; simp
  have h2v : ∀ y : String, y ≠ "tr.p" → y ≠ "tr.v" → τ2.vars y = σ.vars y := by
    intro y h h'; rw [hτ2, hτ1]; simp [h, h']
  have h2p : τ2.vars "tr.p" = 0 := by rw [hτ2, hτ1]; simp
  have h2vv : τ2.vars "tr.v" = 0 := by rw [hτ2]; simp
  have hO2 : TrOInv nN o t ro rt mk D ns off tgt τ2 :=
    { frame :=
        { csr := hcsr.of_eq (by rw [h2a]) (by rw [h2a])
          carrier := by rw [h2v nN hnp hnv]; exact hcar
          roLen := by rw [h2a]; exact hroL
          rtLen := by rw [h2a]; exact hrtL
          mkLen := by rw [h2a]; exact hmkL }
      done := by
        rw [h2vv]
        exact
          { roGet := fun i hi => absurd hi (by omega)
            rtSound := fun a ha => absurd ha (by omega)
            rtComplete := fun a ha => absurd ha (by omega)
            rtInj := fun a ha => absurd ha (by omega)
            mkDone := fun a ha => absurd ha (by omega)
            mkZero := by
              intro a _ u
              rw [h2a]
              exact hzero _ (trRow_lt_sq a.isLt u.isLt) }
      vle := by rw [h2vv]; omega
      pval := by rw [h2vv, h2p, trOff_zero] }
  obtain ⟨τ3, hrun3, hO3, hv3⟩ :=
    (trOuter_scan (D := D) (ns := ns) (off := off) (tgt := tgt) hnm hnN hB).run ⟨hO2, h2vv⟩
  have hdone3 : TrDone ro rt mk D n n τ3 := by
    have h := hO3.done; rw [hv3] at h; exact h
  have hp3 : τ3.vars "tr.p" = trOff D n := by rw [hO3.pval, hv3]
  have hpB : trOff D n < B := by omega
  have hroL3 : n + 1 ≤ (τ3.arrs ro).length := hO3.frame.roLen
  have hrtL3 : transPairCount D ≤ (τ3.arrs rt).length := hO3.frame.rtLen
  have hnN3 : τ3.vars nN = n := hO3.frame.carrier
  obtain ⟨τ4, hτ4⟩ : ∃ τ, τ = τ3.setArr ro n (trOff D n) := ⟨_, rfl⟩
  obtain ⟨τ5, hτ5⟩ : ∃ τ, τ = τ4.setVar nT (trOff D n) := ⟨_, rfl⟩
  have r4 : Run B (.store ro (.var nN) (.var "tr.p")) τ3 τ4 3 := by
    rw [hτ4]; exact run_store' (evB_var hnN3 hnB) (evB_var hp3 hpB) (by omega) (by simp)
  have r5 : Run B (.assign nT (.var "tr.p")) τ4 τ5 2 := by
    rw [hτ5]
    exact run_assign' (evB_var (by rw [hτ4, vars_setArr]; exact hp3) hpB) (by simp)
  have h5ro : τ5.arrs ro = (τ3.arrs ro).set n (trOff D n) := by rw [hτ5, hτ4]; simp
  have h5a : ∀ a : String, a ≠ ro → τ5.arrs a = τ3.arrs a := by
    intro a ha; rw [hτ5, hτ4]; simp [ha]
  have h5nT : τ5.vars nT = trOff D n := by rw [hτ5]; simp
  have h5rt : τ5.arrs rt = τ3.arrs rt := h5a rt (Ne.symm hnm.ro_rt)
  have h5mk : τ5.arrs mk = τ3.arrs mk := h5a mk (Ne.symm hnm.ro_mk)
  refine ⟨τ5, 27 * n + 23 * ns + 30 * trPref off tgt n + 13, ?_, ?_, ?_, ?_⟩
  · exact (r1.seq (r2.seq (hrun3.seq (r4.seq r5)))).mono (by omega)
  · simp only [trK]; omega
  · exact (hO3.frame.csr).of_eq (h5a o hnm.o_ro) (h5a t hnm.t_ro)
  · refine ⟨fun q => (τ3.arrs rt).getD q 0, ?_, h5nT⟩
    refine
      { toLen := by rw [h5ro, List.length_set]; exact hroL3
        ttLen := by rw [h5rt]; omega
        markLen := by rw [h5mk]; exact hO3.frame.mkLen
        toGet := ?_
        ttGet := ?_
        ttLt := ?_
        sound := ?_
        complete := ?_
        inj := ?_
        markOne := ?_
        markZero := ?_ }
    · intro i hi
      rw [h5ro]
      rcases Nat.lt_or_ge i n with h | h
      · rw [List.getElem?_set_ne (show n ≠ i by omega)]
        exact hdone3.roGet i h
      · obtain rfl : i = n := by omega
        rw [List.getElem?_set_self (by omega)]
    · intro q hq
      rw [h5rt]
      exact getElem?_of_lt _ _ (by omega)
    · intro q hq
      obtain ⟨a, ha1, ha2⟩ := trOff_owner D n le_rfl q hq
      exact (hdone3.rtSound a a.isLt q ha1 ha2).1
    · intro v q hq1 hq2 h
      exact (hdone3.rtSound v v.isLt q hq1 hq2).2
    · intro v u hu
      exact hdone3.rtComplete v v.isLt u hu
    · intro v q r hq1 hq2 hr1 hr2 hqr
      exact hdone3.rtInj v v.isLt q r hq1 hq2 hr1 hr2 hqr
    · intro v u hu
      rw [h5mk, hdone3.mkDone v v.isLt u, if_pos (mem_trIn.2 hu)]
    · intro v u hu
      rw [h5mk, hdone3.mkDone v v.isLt u, if_neg (fun hc => hu (mem_trIn.1 hc))]

/-! ## §14 What the region says, read back -/

/-- **The region is exact, in both directions, in `O(1)`.**  With the
pass's output in place, `TransLink D u v` is the single cell
`mk[v·n + u]` and `TransLink D v u` is the single cell `mk[u·n + v]` —
which is what `greedyStep`'s `pick` filter tests
(`CoverRoutine.lean:212`), where both directions occur. -/
theorem transCsrAt_decides {ro rt mk : String} {n : ℕ} {D : Orientation n}
    {ttF : ℕ → ℕ} {σ : Env} (h : TransCsrAt ro rt mk D ttF σ) (u v : Fin n) :
    ((σ.arrs mk).getD ((v : ℕ) * n + (u : ℕ)) 0 = 1 ↔ TransLink D u v) ∧
      ((σ.arrs mk).getD ((u : ℕ) * n + (v : ℕ)) 0 = 1 ↔ TransLink D v u) :=
  h.mark_both u v

/-- **The CSR rows are exact too**, and deduplicated: row `v` of
`(ro, rt)` lists each transitive in-neighbour of `v` exactly once. -/
theorem transCsrAt_row {ro rt mk : String} {n : ℕ} {D : Orientation n}
    {ttF : ℕ → ℕ} {σ : Env} (h : TransCsrAt ro rt mk D ttF σ) (v u : Fin n) :
    (∃ q, trOff D (v : ℕ) ≤ q ∧ q < trOff D ((v : ℕ) + 1) ∧ ttF q = (u : ℕ)) ↔
      TransLink D u v := by
  constructor
  · rintro ⟨q, hq1, hq2, hq3⟩
    have hlt : ttF q < n := by rw [hq3]; exact u.isLt
    have := h.sound v q hq1 hq2 hlt
    have heq : (⟨ttF q, hlt⟩ : Fin n) = u := by ext; exact hq3
    rwa [heq] at this
  · exact h.complete v u

/-- The output's slot count never exceeds the enumeration it came
from. -/
theorem transCsrAt_slots_le {n : ℕ} (D : Orientation n) :
    trOff D n ≤ transPairCount D := trOff_le_transPairCount D


/-- **The budget, priced by an in-degree bound**: at in-degree `≤ d`
one run of the pass costs at most `n·(27 + 23·d + 30·d²) + 13`.  The
carrier enters linearly and never squared — the same
`d`-parameterization that keeps `n²` out of
`ProgCoverCharge.levelCharge_le`. -/
theorem trK_le {n : ℕ} {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    trK n (arcCount D) (transPairCount D) ≤ n * (27 + 23 * d + 30 * (d * d)) + 13 := by
  have h1 := arcCount_le hd
  have h2 := transPairCount_le hd
  calc trK n (arcCount D) (transPairCount D)
      = 27 * n + 23 * arcCount D + 30 * transPairCount D + 13 := rfl
    _ ≤ 27 * n + 23 * (n * d) + 30 * (n * (d * d)) + 13 := by omega
    _ = n * (27 + 23 * d + 30 * (d * d)) + 13 := by ring

/-! ## §15 The axiom surface -/

#print axioms transCsrIn_trCom

end Lax3Proofs.Prog
