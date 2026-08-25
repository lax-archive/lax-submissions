import Lax3Proofs.SolveCovLoad
import Lax3Proofs.ProgCoverCharge

/-!
# F6c12-5b — the fraternal candidate CSR

`CovAugAdjIn`'s augmentation-round body splits into two genuinely new
passes.  This file is the fraternal one: **from an in-neighbour CSR of
the current orientation `D`, an exact `GraphCsr` of `fratGraph D`**.

## What the pass enumerates, and what that costs

`fratGraph D` (`Augmentation.lean:178`) has `Adj u v := u ≠ v ∧
FratLink D u v`, and `FratLink D u v := ∃ w, u ∈ D.inN w ∧ v ∈ D.inN w`.
So the enumeration is BEII's own (`references/nodm05/BEII.tex:654-668`):
for each `w`, for each *ordered* pair `x, y` of slots of row `w`, emit
`(x, y)` unless `x = y`.  §3's `fratCands` is that list in the pass's
own order, and `length_fratCands_eq` is the file's cost anchor:

    (fratCands n R).length = fratPairCount D

on the nose — `fratPairCount D = Σ_w |D.inN w|²` (`ProgCoverCharge.lean:
150`) is *defined* as the size of this enumeration, and
`exists_chainCharge_le` already closes §7's envelope at that count.
The pass therefore has a budget of the shape

    fratK a b c d n m f = a·n + b·m + c·f + d,
    m = arcCount D,  f = fratPairCount D

and nothing else: `n` counts the per-vertex loop headers (the degree
zeroing, the prefix sums, and the two enumeration sweeps' outer loops),
`m = arcCount D` counts each sweep's middle loop — one turn per arc,
since the input CSR has exactly `arcCount D` slots (`InNCsr.ns_eq`) —
and `f = fratPairCount D` counts each sweep's inner loop body, one turn
per ordered pair.  `fratKStd` fixes the constants at
`240·n + 120·m + 200·f + 60`, with the command-by-command accounting in
its docstring; `fratK_le` and `arcCount_le_fratPairCount` record that
the middle term is dominated (`d ≤ d²`), so the shape collapses to
`O(n + fratPairCount D)`.  The `m` term is kept separate because the
program really does run two loops.

## The algorithm the budget is priced for

A counting sort by key plus an `n²` mark-array dedup, both single
passes over the same enumeration:

1. zero `dg` (`n` turns);
2. **count**: sweep the enumeration; at a candidate `(x, y)` with
   `x ≠ y` and `mk[x·n + y] = 0`, set `mk[x·n + y] := 1` and bump
   `dg[x]` (`n + arcCount D + fratPairCount D` turns);
3. prefix-sum `dg` into the output offsets (`n` turns);
4. **emit**: sweep the enumeration again; at `(x, y)` with `x ≠ y` and
   `mk[x·n + y] = 1`, write `y` at `x`'s cursor, bump it, and clear
   `mk[x·n + y]` back to `0` (same turn count).

Step 4's *clearing* test is what makes the second sweep emit each
distinct pair exactly once and leaves `mk` all-zero again, so no
region is ever re-zeroed and no key is ever compared: the mark region
is `n²` cells long, which costs nothing to *have* (`Imp.lean:20-44`,
memory starts zeroed) and is touched at most `fratPairCount D` times.
The abstract output of the two sweeps is §3's `fratOutRow` —
first-occurrence deduplication (`dedF`, `SolveCovLoad.lean:68`) of the
candidates keyed by their first component.

## What is proved here, and what is not

**Proved** — the whole abstract layer, i.e. everything about *which*
data the pass leaves, and everything about the counts:

* `graphCsr_fratPref` — the two arrays holding `fratOff`/`fratPref`
  **are** `GraphCsr o t (fratGraph D) (fratNs n R)`, on the nose: rows
  duplicate-free, row membership an iff with adjacency, offsets
  anchored and monotone, every target a vertex.  Exactness, both
  directions, no self-loops and the empty rows of isolated vertices all
  fall out of that one statement (`mem_fratOutRow` is the iff behind
  it).  `csrPrefix_fratPref` is the same content in the windowed form
  (`CsrPrefix`) that `≤`-sized allocations force — `GraphCsr`'s `Csr`
  clause pins array lengths exactly, so a pass writing into an
  over-long fresh region can only deliver a prefix.
* `length_fratCands_eq` — the enumeration is exactly `fratPairCount D`
  long; `InNCsr.ns_eq` — the input CSR has exactly `arcCount D` slots.
* `fratNs_le` — the output has at most `fratPairCount D` slots, so the
  output target region is inside the same envelope.
* `exists_fratCsr` — all three at once, from the input contract alone;
  `InNCsr.rows` is the bridge, and it is why nothing above is vacuous.

**Not proved** — the concrete IMP+ program.  §7 names the residual
`FratCsrAt` in the shape `AdjBuildAt` (`SolveSweepBuild.lean:1864`)
established for a pass a program can actually meet: the two figures in
named scalar cells and inside the word bound, since IMP+ has no
array-length primitive (`Imp.lean:158`) — this is Finding 1 of
`SolveSweepBuild`, and `AdjBuildIn` (`SolveSweepAdj.lean:308`) is the
landed statement that does not survive it.  `FratCsrAt` is quantified
over the program and its budget, exactly as `AdjBuildAt` is; the
budget shape is fixed by `fratK` and its constants by `fratKStd`.  No
command text is asserted here:
a program written but not verified is the failure mode this campaign
has already recorded three times, and the counts above are the part of
the budget that can be checked without one.

## Findings

1. **`Orientation.asymm` and `not_mem_self` are not used.**  The paper's
   digraphs permit two-cycles and Lean's `Orientation` forbids them
   (`Augmentation.lean:110`), but neither field enters: the `x ≠ y`
   test alone discharges `fratGraph`'s `u ≠ v`, and it does so even for
   a family with `w ∈ inN w`.  Every statement here is at an arbitrary
   `Orientation`, and no proof below appeals to either field — so no
   assumption is imported from BEII that the Lean object does not carry,
   and none of the Lean object's own extra strength is spent.
2. **`arcCount D ≤ fratPairCount D` always** (`d ≤ d²`), so the
   middle-loop term never widens the envelope.
3. **A pass cannot promise a bare `GraphCsr` on its output region.**
   `GraphCsr` contains `Lib.Csr`, whose first two clauses are
   `arrs o = arrOf (N+1) off` and `arrs t = arrOf ns tgt` — *exact*
   lengths — while the allocation convention gives a pass only
   `N + 1 ≤ length` and `ns ≤ length`.  The two are incompatible
   whenever the region is over-allocated, which is the normal case.
   `CsrPrefix` (`SolveGlueLoad.lean:65`) is the windowed statement that
   is meetable, and `AdjBuildAt`'s `GraphCsr` sits in its *pre*condition
   (where exactness is a hypothesis, not an obligation), so no landed
   statement is wrong here — but a residual stated with `GraphCsr` in
   the postcondition would have been unmeetable, and this one is
   therefore stated with `CsrPrefix`.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (arrOf_getD getD_eq_getElem)
open Lax3Proofs.Augmentation

/-! ## §1 The input: an orientation in compressed-row form

`GraphCsr`'s shape with `D.inN` in place of a graph's neighbourhoods.
An orientation is *not* a graph — `inN` is a plain family of finsets,
not symmetric — so the landed `GraphCsr` cannot state this, but every
clause is the same clause. -/

/-- **An in-neighbour CSR of `D`**: `Lib.Csr`'s relation on the pair
`(o, t)` at carrier `n` and slot count `ns`, anchored at `off 0 = 0`,
rows duplicate-free, and row `w` listing exactly the in-neighbours of
`w`. -/
def InNCsr (o t : String) {n : ℕ} (D : Orientation n) (ns : ℕ) (σ : Env) : Prop :=
  ∃ off tgt : ℕ → ℕ,
    Csr o t n ns n off tgt σ ∧ off 0 = 0 ∧
    (∀ w : Fin n, (Csr.row off tgt (w : ℕ)).Nodup) ∧
    ∀ (w : Fin n) (u : ℕ),
      u ∈ Csr.row off tgt (w : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN w

/-- A duplicate-free list of vertices whose membership is a finset's
has that finset's length. -/
theorem length_eq_card_of_rows {n : ℕ} {D : Orientation n} {R : ℕ → List ℕ}
    (hnd : ∀ w : Fin n, (R (w : ℕ)).Nodup)
    (hR : ∀ (w : Fin n) (u : ℕ),
      u ∈ R (w : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN w)
    (w : Fin n) : (R (w : ℕ)).length = (D.inN w).card := by
  classical
  have h1 : (R (w : ℕ)).toFinset.card = (R (w : ℕ)).length :=
    List.toFinset_card_of_nodup (hnd w)
  have h2 : (R (w : ℕ)).toFinset = (D.inN w).image (fun z : Fin n => (z : ℕ)) := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_image]
    rw [hR w u]
    constructor
    · rintro ⟨hu, hmem⟩
      exact ⟨⟨u, hu⟩, hmem, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.isLt, hz⟩
  rw [← h1, h2, Finset.card_image_of_injective _ Fin.val_injective]

/-- **The slot count of an in-neighbour CSR is `arcCount D`** — the
figure the pass's middle loop is charged at. -/
theorem InNCsr.ns_eq {o t : String} {n ns : ℕ} {D : Orientation n} {σ : Env}
    (h : InNCsr o t D ns σ) : ns = arcCount D := by
  obtain ⟨off, tgt, hc, h0, hnd, hR⟩ := h
  have hsum : ∑ i ∈ Finset.range n, Csr.rowLen off i = ns := by
    have hs := Csr.sum_rowLen hc n le_rfl
    rw [hc.last, h0] at hs
    omega
  have hlen : ∀ w : Fin n, Csr.rowLen off (w : ℕ) = (D.inN w).card := by
    intro w
    rw [← Csr.length_row off tgt (w : ℕ)]
    exact length_eq_card_of_rows hnd hR w
  rw [← hsum]
  show ∑ i ∈ Finset.range n, Csr.rowLen off i = ∑ w : Fin n, (D.inN w).card
  rw [← Fin.sum_univ_eq_sum_range (fun i => Csr.rowLen off i) n]
  exact Finset.sum_congr rfl fun w _ => hlen w

/-! ## §2 List plumbing: the prefixes of a row family

A CSR whose rows are `F 0, F 1, …` has target array `(List.range n).
flatMap F` and offsets the partial lengths.  All four facts a `Csr`
relation asks of that pair are proved once, for an arbitrary `F`. -/

section Plumbing

variable {α : Type*} (E : ℕ → List α) (F : ℕ → List ℕ)

theorem flatPref_succ (k : ℕ) :
    (List.range (k + 1)).flatMap E = (List.range k).flatMap E ++ E k := by
  rw [List.range_succ, List.flatMap_append]
  simp

theorem length_flatPref (k : ℕ) :
    ((List.range k).flatMap E).length = ∑ i ∈ Finset.range k, (E i).length := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [flatPref_succ, List.length_append, ih, Finset.sum_range_succ]

theorem length_flatPref_mono {a b : ℕ} (hab : a ≤ b) :
    ((List.range a).flatMap E).length ≤ ((List.range b).flatMap E).length := by
  rw [length_flatPref, length_flatPref]
  refine Finset.sum_le_sum_of_subset ?_
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

theorem mem_flatPref {k : ℕ} {b : α} :
    b ∈ (List.range k).flatMap E ↔ ∃ i, i < k ∧ b ∈ E i := by
  constructor
  · intro h
    obtain ⟨i, hi, hb⟩ := List.mem_flatMap.mp h
    exact ⟨i, List.mem_range.mp hi, hb⟩
  · rintro ⟨i, hi, hb⟩
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hb⟩

/-- Reading the concatenation at row `v`'s slot `t` reads row `v`. -/
theorem flatPref_getD {k v s : ℕ} (hv : v < k) (hs : s < (F v).length) :
    ((List.range k).flatMap F).getD (((List.range v).flatMap F).length + s) 0
      = (F v).getD s 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [flatPref_succ]
      rcases Nat.lt_or_ge v k with hvk | hvk
      · refine (List.getD_append _ _ _ _ ?_).trans (ih hvk)
        have h1 : ((List.range (v + 1)).flatMap F).length
            ≤ ((List.range k).flatMap F).length :=
          length_flatPref_mono F hvk
        rw [flatPref_succ, List.length_append] at h1
        omega
      · have hvk' : v = k := by omega
        subst hvk'
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp

/-- **Row `v` of the concatenation is `F v`** — the read-back every
`GraphCsr` clause is stated through. -/
theorem row_flatPref {n : ℕ} {v : ℕ} (hv : v < n) :
    Csr.row (fun k => ((List.range k).flatMap F).length)
        (fun p => ((List.range n).flatMap F).getD p 0) v = F v := by
  have hlen : Csr.rowLen (fun k => ((List.range k).flatMap F).length) v
      = (F v).length := by
    show ((List.range (v + 1)).flatMap F).length
      - ((List.range v).flatMap F).length = (F v).length
    rw [flatPref_succ, List.length_append]
    omega
  rw [Csr.row, hlen]
  refine List.ext_getElem (by simp) ?_
  intro k h1 h2
  simp only [arrOf, List.getElem_map, List.getElem_range]
  exact (flatPref_getD F hv h2).trans (getD_eq_getElem h2)

end Plumbing

/-! ## §3 The candidate enumeration and the output rows

Everything below is stated at an arbitrary row family `R : ℕ → List ℕ`
— the input CSR's rows — and, where an orientation is named, at an
arbitrary `Orientation`.  Finding 1: neither `not_mem_self` nor
`asymm` is used anywhere. -/

/-- The ordered pairs the pass enumerates at `w`: every pair of slots
of row `w`, in slot order.  The diagonal is present here and dropped
by the `x ≠ y` test in `fratOutRow`. -/
def fratPairsAt (R : ℕ → List ℕ) (w : ℕ) : List (ℕ × ℕ) :=
  (R w).flatMap fun x => (R w).map fun y => (x, y)

/-- **The fraternal candidate enumeration**, in the pass's own order:
outer loop over `w`, then the two slot loops of row `w`. -/
def fratCands (n : ℕ) (R : ℕ → List ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fratPairsAt R)

/-- **Row `v` of the output**: the second components of the candidates
whose first component is `v` and whose two components differ,
deduplicated at first occurrence — exactly what the mark-array sweep
emits. -/
def fratOutRow (n : ℕ) (R : ℕ → List ℕ) (v : ℕ) : List ℕ :=
  dedF ((fratCands n R).filterMap
    fun p => if p.1 = v ∧ p.2 ≠ v then some p.2 else none)

private theorem length_flatMap_map_pair (l m : List ℕ) :
    (l.flatMap fun x => m.map fun y => (x, y)).length = l.length * m.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_map,
        List.length_cons]
      ring

theorem length_fratCands (n : ℕ) (R : ℕ → List ℕ) :
    (fratCands n R).length
      = ∑ w ∈ Finset.range n, (R w).length * (R w).length := by
  rw [fratCands, length_flatPref]
  exact Finset.sum_congr rfl fun w _ => length_flatMap_map_pair (R w) (R w)

/-- **The cost anchor**: the enumeration is exactly `fratPairCount D`
long.  `fratPairCount D = Σ_w |D.inN w|²` is defined
(`ProgCoverCharge.lean:150`) as the size of this enumeration, and the
landed `exists_chainCharge_le` already prices the chain at it. -/
theorem length_fratCands_eq {n : ℕ} {D : Orientation n} {R : ℕ → List ℕ}
    (hlen : ∀ w : Fin n, (R (w : ℕ)).length = (D.inN w).card) :
    (fratCands n R).length = fratPairCount D := by
  rw [length_fratCands, fratPairCount,
    ← Fin.sum_univ_eq_sum_range (fun w => (R w).length * (R w).length) n]
  exact Finset.sum_congr rfl fun w _ => by rw [hlen w]

/-- **Row `v` of the output lists exactly the `fratGraph`-neighbours of
`v`.**  Both directions, no self-loop, and — read at a `v` in no
`inN w` — the empty row of an isolated vertex. -/
theorem mem_fratOutRow {n : ℕ} {D : Orientation n} {R : ℕ → List ℕ}
    (hR : ∀ (w : Fin n) (u : ℕ),
      u ∈ R (w : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN w)
    {v : ℕ} (hv : v < n) (y : ℕ) :
    y ∈ fratOutRow n R v ↔ ∃ hy : y < n, (fratGraph D).Adj ⟨v, hv⟩ ⟨y, hy⟩ := by
  have hadj : ∀ a b : Fin n, (fratGraph D).Adj a b ↔ (a ≠ b ∧ FratLink D a b) :=
    fun _ _ => fratGraph_adj
  rw [fratOutRow, mem_dedF, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hpe⟩
    by_cases hc : p.1 = v ∧ p.2 ≠ v
    · rw [if_pos hc] at hpe
      have hy2 : p.2 = y := Option.some.inj hpe
      obtain ⟨w, hw, hpw⟩ := (mem_flatPref (fratPairsAt R)).mp hp
      simp only [fratPairsAt] at hpw
      obtain ⟨a, ha, hpm⟩ := List.mem_flatMap.mp hpw
      obtain ⟨b, hb, hab⟩ := List.mem_map.mp hpm
      have hp1 : a = p.1 := congrArg Prod.fst hab
      have hp2 : b = p.2 := congrArg Prod.snd hab
      have hav : a = v := by rw [hp1, hc.1]
      have hby : b = y := by rw [hp2, hy2]
      have hvR : v ∈ R (w : ℕ) := by rw [← hav]; exact ha
      have hyR : y ∈ R (w : ℕ) := by rw [← hby]; exact hb
      obtain ⟨hun, hvmem⟩ := (hR ⟨w, hw⟩ v).mp hvR
      obtain ⟨hyn, hymem⟩ := (hR ⟨w, hw⟩ y).mp hyR
      refine ⟨hyn, (hadj _ _).mpr ⟨?_, ⟨w, hw⟩, hvmem, hymem⟩⟩
      intro hcc
      have hvy : v = y := congrArg Fin.val hcc
      exact hc.2 (by rw [hy2, ← hvy])
    · rw [if_neg hc] at hpe
      simp at hpe
  · rintro ⟨hy, hadjy⟩
    obtain ⟨hne, w, hvw, hyw⟩ := (hadj _ _).mp hadjy
    refine ⟨(v, y), ?_, ?_⟩
    · refine (mem_flatPref (fratPairsAt R)).mpr ⟨(w : ℕ), w.isLt, ?_⟩
      simp only [fratPairsAt]
      exact List.mem_flatMap.mpr
        ⟨v, (hR w v).mpr ⟨hv, hvw⟩,
          List.mem_map.mpr ⟨y, (hR w y).mpr ⟨hy, hyw⟩, rfl⟩⟩
    · have hne' : y ≠ v := by
        intro hcc
        exact hne (Fin.eq_of_val_eq hcc.symm)
      rw [if_pos (show (v, y).1 = v ∧ (v, y).2 ≠ v from ⟨rfl, hne'⟩)]

/-- Every entry of an output row is a vertex. -/
theorem fratOutRow_lt {n : ℕ} {D : Orientation n} {R : ℕ → List ℕ}
    (hR : ∀ (w : Fin n) (u : ℕ),
      u ∈ R (w : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN w)
    {v : ℕ} (hv : v < n) {y : ℕ} (hy : y ∈ fratOutRow n R v) : y < n :=
  ((mem_fratOutRow hR hv y).mp hy).1

/-- The output rows are duplicate-free: `dedF` is. -/
theorem nodup_fratOutRow (n : ℕ) (R : ℕ → List ℕ) (v : ℕ) :
    (fratOutRow n R v).Nodup := nodup_dedF _

/-! ## §4 The output CSR -/

/-- The output target array up to row `k`: the rows, concatenated. -/
def fratPref (n : ℕ) (R : ℕ → List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).flatMap (fratOutRow n R)

/-- The output offsets: the partial lengths. -/
def fratOff (n : ℕ) (R : ℕ → List ℕ) (k : ℕ) : ℕ := (fratPref n R k).length

/-- The output slot count. -/
def fratNs (n : ℕ) (R : ℕ → List ℕ) : ℕ := fratOff n R n

theorem fratOff_zero (n : ℕ) (R : ℕ → List ℕ) : fratOff n R 0 = 0 := rfl

theorem fratOff_succ (n : ℕ) (R : ℕ → List ℕ) (k : ℕ) :
    fratOff n R (k + 1) = fratOff n R k + (fratOutRow n R k).length := by
  rw [fratOff, fratOff, fratPref, fratPref, flatPref_succ, List.length_append]

/-- **The pass's output, read back**: two arrays holding the offsets and
the concatenated rows are a `GraphCsr` of `fratGraph D` — exactly, with
duplicate-free rows and membership an iff with adjacency. -/
theorem graphCsr_fratPref {o t : String} {n : ℕ} {D : Orientation n}
    {R : ℕ → List ℕ}
    (hR : ∀ (w : Fin n) (u : ℕ),
      u ∈ R (w : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN w)
    {σ : Env}
    (hoff : σ.arrs o = arrOf (n + 1) (fratOff n R))
    (htgt : σ.arrs t = fratPref n R n) :
    GraphCsr o t (fratGraph D) (fratNs n R) σ := by
  have hrow : ∀ v : Fin n,
      Csr.row (fratOff n R) (fun p => (fratPref n R n).getD p 0) (v : ℕ)
        = fratOutRow n R (v : ℕ) := fun v => row_flatPref _ v.isLt
  have htlt : ∀ p, p < fratNs n R → (fratPref n R n).getD p 0 < n := by
    intro p hp
    have hmem : (fratPref n R n).getD p 0 ∈ fratPref n R n := by
      rw [getD_eq_getElem hp]
      exact List.getElem_mem hp
    obtain ⟨i, hi, hy⟩ := (mem_flatPref (fratOutRow n R)).mp hmem
    exact fratOutRow_lt hR hi hy
  refine ⟨fratOff n R, fun p => (fratPref n R n).getD p 0,
    ⟨hoff, ?_, fun i _ => ?_, rfl, htlt⟩, fratOff_zero n R, ?_, ?_⟩
  · rw [htgt, fratNs, fratOff]
    exact (arrOf_getD (fratPref n R n)).symm
  · rw [fratOff_succ]
    omega
  · intro v
    rw [hrow v]
    exact nodup_fratOutRow n R (v : ℕ)
  · intro v y
    rw [hrow v]
    have := mem_fratOutRow hR v.isLt y
    simpa using this

/-- **The windowed form of the output** (`CsrPrefix`,
`SolveGlueLoad.lean:65`).  The allocation convention is `≤ length`, so
what a pass can leave is a *prefix*: `GraphCsr`'s own `Csr` clause pins
the arrays to exactly `n + 1` and `ns` cells, which an over-long fresh
region never satisfies.  This is therefore the shape the residual's
postcondition is stated at, and `graphCsr_fratPref` is the same content
on exact-length arrays. -/
theorem csrPrefix_fratPref {o' t' : String} {n : ℕ} {D : Orientation n}
    {R : ℕ → List ℕ}
    (hR : ∀ (w : Fin n) (u : ℕ),
      u ∈ R (w : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN w)
    (hne : o' ≠ t') {σ : Env}
    (hoL : n + 1 ≤ (σ.arrs o').length)
    (htL : fratNs n R ≤ (σ.arrs t').length)
    (hoff : (σ.arrs o').take (n + 1) = arrOf (n + 1) (fratOff n R))
    (htgt : (σ.arrs t').take (fratNs n R) = fratPref n R n) :
    CsrPrefix o' t' (fratGraph D) (fratNs n R) σ := by
  refine ⟨hoL, htL, graphCsr_fratPref hR ?_ ?_⟩
  · rw [arrs_winA_some (show (fun b => if b = o' then some (n + 1)
      else if b = t' then some (fratNs n R) else none) o' = some (n + 1)
      from by simp) σ]
    exact hoff
  · rw [arrs_winA_some (show (fun b => if b = o' then some (n + 1)
      else if b = t' then some (fratNs n R) else none) t' = some (fratNs n R)
      from by simp [Ne.symm hne]) σ]
    exact htgt

/-! ## §5 The output's size -/

private theorem length_filterMap_cons_ite (v : ℕ) (p : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    ((p :: l).filterMap fun r => if r.1 = v ∧ r.2 ≠ v then some r.2 else none).length
      = (if p.1 = v ∧ p.2 ≠ v then 1 else 0)
        + (l.filterMap fun r => if r.1 = v ∧ r.2 ≠ v then some r.2 else none).length := by
  by_cases hc : p.1 = v ∧ p.2 ≠ v
  · rw [List.filterMap_cons_some
        (f := fun r : ℕ × ℕ => if r.1 = v ∧ r.2 ≠ v then some r.2 else none)
        (a := p) (b := p.2) (if_pos hc),
      List.length_cons, if_pos hc]
    omega
  · rw [List.filterMap_cons_none
        (f := fun r : ℕ × ℕ => if r.1 = v ∧ r.2 ≠ v then some r.2 else none)
        (a := p) (if_neg hc), if_neg hc]
    omega

private theorem sum_filterMap_le (l : List (ℕ × ℕ)) (k : ℕ) :
    ∑ v ∈ Finset.range k,
        (l.filterMap fun p => if p.1 = v ∧ p.2 ≠ v then some p.2 else none).length
      ≤ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have hstep : ∀ v : ℕ,
          ((p :: l).filterMap
              fun r => if r.1 = v ∧ r.2 ≠ v then some r.2 else none).length
            = (if p.1 = v ∧ p.2 ≠ v then 1 else 0)
              + (l.filterMap
                  fun r => if r.1 = v ∧ r.2 ≠ v then some r.2 else none).length :=
        fun v => length_filterMap_cons_ite v p l
      have hsum1 : ∑ v ∈ Finset.range k,
          (if p.1 = v ∧ p.2 ≠ v then (1 : ℕ) else 0) ≤ 1 := by
        by_cases hm : p.1 ∈ Finset.range k
        · have hzero : ∀ b ∈ Finset.range k, b ≠ p.1 →
              (if p.1 = b ∧ p.2 ≠ b then (1 : ℕ) else 0) = 0 := by
            intro b _ hb
            exact if_neg fun hcc => hb hcc.1.symm
          rw [Finset.sum_eq_single_of_mem p.1 hm hzero]
          split
          · exact le_rfl
          · exact Nat.zero_le 1
        · have hzero : ∀ b ∈ Finset.range k,
              (if p.1 = b ∧ p.2 ≠ b then (1 : ℕ) else 0) = 0 := by
            intro b hb
            refine if_neg fun hcc => hm ?_
            rw [hcc.1]
            exact hb
          rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
          exact Nat.zero_le 1
      calc ∑ v ∈ Finset.range k,
            ((p :: l).filterMap
              fun r => if r.1 = v ∧ r.2 ≠ v then some r.2 else none).length
          = ∑ v ∈ Finset.range k,
              ((if p.1 = v ∧ p.2 ≠ v then 1 else 0)
                + (l.filterMap
                    fun r => if r.1 = v ∧ r.2 ≠ v then some r.2 else none).length) :=
            Finset.sum_congr rfl fun v _ => hstep v
        _ = (∑ v ∈ Finset.range k, (if p.1 = v ∧ p.2 ≠ v then 1 else 0))
              + ∑ v ∈ Finset.range k,
                  (l.filterMap
                    fun r => if r.1 = v ∧ r.2 ≠ v then some r.2 else none).length :=
            Finset.sum_add_distrib
        _ ≤ 1 + l.length := Nat.add_le_add hsum1 ih
        _ = (p :: l).length := by rw [List.length_cons]; omega

/-- **The output fits in the same envelope**: the edges of `fratGraph D`
are among the candidates, so the output target region needs at most
`fratPairCount D` cells. -/
theorem fratNs_le {n : ℕ} {D : Orientation n} {R : ℕ → List ℕ}
    (hlen : ∀ w : Fin n, (R (w : ℕ)).length = (D.inN w).card) :
    fratNs n R ≤ fratPairCount D := by
  rw [← length_fratCands_eq hlen, fratNs, fratOff, fratPref, length_flatPref]
  refine le_trans (Finset.sum_le_sum fun v _ => ?_) (sum_filterMap_le _ n)
  exact length_dedF_le _

/-- Finding 2: `d ≤ d²`, so the middle-loop term is dominated and the
budget's shape collapses to `O(n + fratPairCount D)`. -/
theorem arcCount_le_fratPairCount {n : ℕ} (D : Orientation n) :
    arcCount D ≤ fratPairCount D := by
  rw [arcCount, fratPairCount]
  refine Finset.sum_le_sum fun w _ => ?_
  rcases Nat.eq_zero_or_pos (D.inN w).card with h | h
  · rw [h]
  · exact Nat.le_mul_of_pos_left _ h

/-! ## §6 The bridge: the input contract feeds §3-§5

Nothing in §3-§5 is vacuous — the rows of an in-neighbour CSR are a row
family meeting every hypothesis those sections carry, so the whole
abstract layer applies to exactly the inputs the pass is given. -/

/-- **The rows of an in-neighbour CSR are §3's row family.** -/
theorem InNCsr.rows {o t : String} {n ns : ℕ} {D : Orientation n} {σ : Env}
    (h : InNCsr o t D ns σ) :
    ∃ R : ℕ → List ℕ,
      (∀ (w : Fin n) (u : ℕ),
        u ∈ R (w : ℕ) ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ D.inN w) ∧
      ∀ w : Fin n, (R (w : ℕ)).length = (D.inN w).card := by
  obtain ⟨off, tgt, -, -, hnd, hR⟩ := h
  exact ⟨Csr.row off tgt, hR, fun w => length_eq_card_of_rows hnd hR w⟩

/-- **The proved half of the pass, in one statement.**  From an
in-neighbour CSR of `D` alone: a row family whose candidate enumeration
is exactly `fratPairCount D` long, whose output has at most
`fratPairCount D` slots, and whose offsets and concatenated rows — laid
as prefixes in any two distinct arrays — are an exact CSR of
`fratGraph D` in the windowed form `CsrPrefix` (Finding 3).  What a
discharger of `FratCsrAt` still owes is the program that writes them. -/
theorem exists_fratCsr {o t : String} (o' t' : String) {n ns : ℕ}
    {D : Orientation n} {σ : Env} (h : InNCsr o t D ns σ) (hne : o' ≠ t') :
    ∃ R : ℕ → List ℕ,
      (fratCands n R).length = fratPairCount D ∧
      fratNs n R ≤ fratPairCount D ∧
      ∀ σ' : Env, n + 1 ≤ (σ'.arrs o').length →
        fratNs n R ≤ (σ'.arrs t').length →
        (σ'.arrs o').take (n + 1) = arrOf (n + 1) (fratOff n R) →
        (σ'.arrs t').take (fratNs n R) = fratPref n R n →
        CsrPrefix o' t' (fratGraph D) (fratNs n R) σ' := by
  obtain ⟨R, hR, hlen⟩ := h.rows
  exact ⟨R, length_fratCands_eq hlen, fratNs_le hlen,
    fun _ hoL htL hoff htgt => csrPrefix_fratPref hR hne hoL htL hoff htgt⟩

/-! ## §7 The residual: the pass, at named figure cells

The shape is `AdjBuildAt`'s (`SolveSweepBuild.lean:1864`), for the
reason recorded there as Finding 1: IMP+ reads no array length
(`Imp.lean:158`), so the carrier size and the two slot counts must sit
in named scalar cells, and every index the pass forms must be a word —
here that includes `x·n + y`, so the bound asked of `B` is `n·n < B`.
The mark region is required *zeroed on entry*, which is what a fresh
allocation is (`Imp.lean:20-44`), and the emit sweep restores it. -/

/-- The budget shape: `n` per-vertex loop headers (four sweeps of the
carrier), `m` middle-loop turns (one per arc; `m = arcCount D` is the
input slot count, `InNCsr.ns_eq`), `f` inner-loop turns (one per
ordered candidate pair; `f = fratPairCount D`, `length_fratCands_eq`),
and a constant setup.  `Spec`'s budget is an upper bound, so a
discharger may spend less than the constants allow. -/
def fratK (a b c d : ℕ) (n m f : ℕ) : ℕ := a * n + b * m + c * f + d

/-- **The concrete target**: `240·n + 120·m + 200·f + 60`.

The constants come from counting the intended program's commands
against the landed comparables — `bldK` (`SolveSweepBuild`) prices a
carrier scan at `11`–`12` fuel a vertex and a slot turn at `58`, and
`SolveCovLoad`'s scan at `38` a slot and `19` a row — and are
deliberately generous:

* `240·n`: four carrier sweeps (zero the degrees, prefix-sum them, and
  the two enumeration sweeps' outer loops, each of which loads a row's
  two bounds and resets a pointer);
* `120·m`: the two enumeration sweeps' middle loops, one turn per arc
  (read `t[p]` into `x`, reset the inner pointer, bump `p`);
* `200·f`: the two sweeps' inner-loop bodies, one turn per ordered
  candidate pair (read `t[q]`, the `x ≠ y` test, form `x·n + y`, the
  mark test and its store, the degree or cursor read and store, bump
  `q`);
* `60`: the setup.

They are an upper bound to be met, not a measurement: no `Spec` is
proved here, and a discharger that spends less still meets it
(`Spec.mono`).  What *is* proved is the count each constant multiplies
— `length_fratCands_eq` and `InNCsr.ns_eq`. -/
def fratKStd : ℕ → ℕ → ℕ → ℕ := fratK 240 120 200 60

/-- **The shape collapses to `O(n + fratPairCount D)`**: at any
orientation the middle-loop term is dominated (Finding 2). -/
theorem fratK_le {n : ℕ} (D : Orientation n) (a b c d : ℕ) :
    fratK a b c d n (arcCount D) (fratPairCount D)
      ≤ a * n + (b + c) * fratPairCount D + d := by
  have h := arcCount_le_fratPairCount D
  have hb : b * arcCount D ≤ b * fratPairCount D := Nat.mul_le_mul_left b h
  simp only [fratK]
  have : (b + c) * fratPairCount D
      = b * fratPairCount D + c * fratPairCount D := by ring
  omega

/-- **`FratCsrIn`, in the shape a program can meet.**  From an
in-neighbour CSR of `D` in `(o, t)` with the carrier in `nN`, its slot
count in `nS`, a zeroed `n·n`-cell mark region in `mk`, an `n`-cell
degree region in `dg` and output regions `o'`, `t'`: leave the input
CSR untouched, an exact CSR of `fratGraph D` in `(o', t')` — windowed
(`CsrPrefix`), since the allocations are `≤`-sized — with its slot
count in `nF` and inside `fratPairCount D`.

Quantified over the program and its budget exactly as `AdjBuildAt` is.
Everything about the *data* is discharged by `csrPrefix_fratPref`, and
everything about the *counts* by `length_fratCands_eq`, `InNCsr.ns_eq`
and `fratNs_le`; what is left open is the program. -/
def FratCsrAt (B : ℕ) (nN nS nF o t o' t' dg mk : String) (fc : Com)
    (kf : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} (D : Orientation n) (ns : ℕ),
    Spec B
      (fun σ => InNCsr o t D ns σ ∧ σ.vars nN = n ∧ σ.vars nS = ns ∧
        n * n < B ∧ fratPairCount D < B ∧
        n + 1 ≤ (σ.arrs o').length ∧ fratPairCount D ≤ (σ.arrs t').length ∧
        n ≤ (σ.arrs dg).length ∧ n * n ≤ (σ.arrs mk).length ∧
        (∀ i, (σ.arrs mk).getD i 0 = 0))
      fc
      (fun _ σ' => InNCsr o t D ns σ' ∧
        ∃ ns' : ℕ, CsrPrefix o' t' (fratGraph D) ns' σ' ∧
          σ'.vars nF = ns' ∧ ns' ≤ fratPairCount D)
      (kf n ns (fratPairCount D))

/-! ## §8 The axioms of the proved half -/

#print axioms graphCsr_fratPref
#print axioms mem_fratOutRow
#print axioms length_fratCands_eq
#print axioms InNCsr.ns_eq
#print axioms csrPrefix_fratPref
#print axioms fratNs_le
#print axioms arcCount_le_fratPairCount
#print axioms exists_fratCsr

end Lax3Proofs.Prog
