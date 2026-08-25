import Lax3Proofs.SolveAugFrat

/-!
# F6c12-5b-ii — the fraternal candidate CSR, as a program

`SolveAugFrat` proves the whole *mathematics* of this pass and leaves
the program open: its own docstring says the constants of `fratKStd`
are "an upper bound to be met, not a measurement… no `Spec` is proved
here".  This file writes the program and proves that `Spec`.

Everything mathematical is `SolveAugFrat`'s and is used verbatim:
`csrPrefix_fratPref` is the postcondition (the two array prefixes *are*
a windowed exact CSR of `fratGraph D`), `length_fratCands_eq` and
`InNCsr.ns_eq` are the two counts the budget multiplies, `fratNs_le`
bounds the output, and `fratKStd` is the budget.  Nothing about
`fratGraph` is re-proved here.

## The program

Two enumeration sweeps over `fratCands`, with two flat carrier sweeps
between them — exactly the four sweeps `fratKStd`'s docstring prices:

1. `frZeroCom` — zero the degree region `dg` (`n` turns);
2. `frSweep … frCountAct` — the counting sweep: at a candidate `(x, y)`
   with `x ≠ y` whose mark cell `mk[x·n + y]` is still clear, set the
   cell and bump `dg[x]`;
3. `frOffCom` — one carrier sweep turning `dg` into the output offsets:
   it writes the running sum into `o'` **and** into `dg` (which becomes
   the emit sweep's cursor array), closes `o'[n]` and publishes the
   slot count in `nF`;
4. `frSweep … frEmitAct` — the emit sweep: at a candidate `(x, y)` with
   `x ≠ y` whose mark cell is *set*, clear the cell, write `y` at `x`'s
   cursor `dg[x]` and bump it.

The mark region is `n·n` cells, required clear on entry — which is what
a fresh allocation is (`Imp.lean:20-44`) — and the emit sweep's
*clearing* test restores it, so no region is ever re-zeroed and the two
sweeps together touch `mk` at most `2·fratPairCount D` times.

The two enumeration sweeps share one skeleton, `frSweep`, proved once
in §4-§6: three nested loops (`w` over the carrier, `x` over the slots
of row `w` of the input, `y` over the slots of the same row) whose
turns are exactly the elements of `fratCands n (Csr.row off tgt)` in
order.  Its interface is `FrAct`: a body that, at a candidate `(a, b)`,
moves an abstract accumulator `J` from the processed prefix `L` to
`L ++ [(a, b)]` and leaves the loop's own cursors alone.  The two
concrete bodies (§7, §9) instantiate it.

## What the accumulator is

`outRow L v` (§1) is row `v` of the output *at a prefix `L`* of the
enumeration: `dedF` of the second components of the candidates of `L`
whose first component is `v` and whose two components differ.  At
`L = fratCands n R` it is `SolveAugFrat`'s `fratOutRow` definitionally
(`fratOutRow_eq`).  The counting sweep's invariant is
`dg[x] = |outRow L x|` and `mk[x·n + y] = 1 ↔ y ∈ outRow L x`; the emit
sweep's is `dg[x] = fratOff n R x + |outRow L x|`, the slots
`[fratOff n R x, dg[x])` of `t'` holding `outRow L x`, and
`mk[x·n + y] = 1 ↔ (y ∈ fratOutRow n R x ∧ y ∉ outRow L x)`.  Both step
by `dedF_snoc` (`SolveCovLoad.lean:138`), whose case split is exactly
the mark test.

## The budget, and where it is spent

`fratKStd n m f = 240·n + 120·m + 200·f + 60` is met with room:

| term | spent | allowed |
| --- | --- | --- |
| `n` | `11 + 22 + 21 + 22 = 76` | `240` |
| `m` | `21 + 21 = 42` | `120` |
| `f` | `35 + 38 = 73` | `200` |
| `1` | `6 + 6 + 13 + 6 = 31` | `60` |

`n` is the four carrier sweeps' turns, `m = arcCount D` the two
enumeration sweeps' middle loops (`InNCsr.ns_eq`: the input CSR has
exactly `arcCount D` slots), `f = fratPairCount D` their inner-loop
bodies (`length_fratCands_eq`: the enumeration has exactly that many
elements).  No term is tight; `Spec`'s budget is an upper bound.

## Findings

1. **The shape constraint of `AdjBuildAt` is met, not evaded.**  IMP+
   reads no array length (`Imp.lean:158`), so the carrier size sits in
   the named cell `nN` and the output slot count is *published* into
   `nF`; the pass never asks for `(σ.arrs a).length`.  The input slot
   count cell `nS` of `FratCsrAt` is not read by the program at all —
   the row bounds come from `o` — so the pass is correct at any value
   of it; the contract's clause is simply not needed.
2. **`n·n < B` is the word bound that matters.**  The only index the
   pass forms that is not already inside the input CSR is `x·n + y`,
   and `frRow_lt_sq` puts it below `n·n`.  Every other figure is below
   `fratPairCount D` or `n`, both of which `FratCsrAt`'s precondition
   bounds.  At `n = 0` the enumeration is empty and no literal `1` is
   ever evaluated, so `B = 1` is admissible — the loop bodies derive
   `2 ≤ B` from their own guard.
3. **The emit sweep's mark invariant must name the whole enumeration.**
   The tempting form "`mk[x·n + y] = 1` iff `(x, y)` is still to come"
   is false: clearing the cell at the first occurrence does not remove
   the pair from the remaining suffix.  The invariant carried here is
   `y ∈ fratOutRow n R x ∧ y ∉ outRow L x`, which is stable under both
   branches of the test.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (arrOf_getD getD_eq_getElem)
open Lax3Proofs.Augmentation

/-! ## §1 The output at a prefix of the enumeration

`SolveAugFrat.fratOutRow` reads the whole enumeration.  A sweep has
only read a prefix of it, so the invariants are stated at an arbitrary
prefix `L` and specialise to `fratOutRow` at `L = fratCands n R`. -/

/-- The second components of the candidates of `L` whose first
component is `v` and whose two components differ: row `v`'s emissions,
before deduplication. -/
def outCand (L : List (ℕ × ℕ)) (v : ℕ) : List ℕ :=
  L.filterMap fun p => if p.1 = v ∧ p.2 ≠ v then some p.2 else none

/-- **Row `v` of the output at a prefix `L` of the enumeration**:
first-occurrence deduplication of `outCand L v`. -/
def outRow (L : List (ℕ × ℕ)) (v : ℕ) : List ℕ := dedF (outCand L v)

/-- At the whole enumeration this is `SolveAugFrat`'s `fratOutRow`, by
definition. -/
theorem fratOutRow_eq (n : ℕ) (R : ℕ → List ℕ) (v : ℕ) :
    fratOutRow n R v = outRow (fratCands n R) v := rfl

theorem outCand_append (L M : List (ℕ × ℕ)) (v : ℕ) :
    outCand (L ++ M) v = outCand L v ++ outCand M v := by
  simp [outCand]

theorem outCand_singleton (a b v : ℕ) :
    outCand [(a, b)] v = if a = v ∧ b ≠ v then [b] else [] := by
  by_cases h : a = v ∧ b ≠ v <;> simp [outCand, h]

theorem mem_outCand {L : List (ℕ × ℕ)} {v y : ℕ} :
    y ∈ outCand L v ↔ (v, y) ∈ L ∧ y ≠ v := by
  rw [outCand, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hpe⟩
    by_cases hc : p.1 = v ∧ p.2 ≠ v
    · rw [if_pos hc] at hpe
      have hy : p.2 = y := Option.some.inj hpe
      refine ⟨?_, by rw [← hy]; exact hc.2⟩
      have : p = (v, y) := Prod.ext hc.1 hy
      rwa [← this]
    · rw [if_neg hc] at hpe; simp at hpe
  · rintro ⟨hm, hy⟩
    exact ⟨(v, y), hm, by rw [if_pos (show (v, y).1 = v ∧ (v, y).2 ≠ v from ⟨rfl, hy⟩)]⟩

/-- **Membership in a row, at any prefix.** -/
theorem mem_outRow {L : List (ℕ × ℕ)} {v y : ℕ} :
    y ∈ outRow L v ↔ (v, y) ∈ L ∧ y ≠ v := by
  rw [outRow, mem_dedF, mem_outCand]

theorem nodup_outRow (L : List (ℕ × ℕ)) (v : ℕ) : (outRow L v).Nodup := nodup_dedF _

@[simp] theorem outRow_nil (v : ℕ) : outRow [] v = [] := rfl

/-- A candidate whose first component is not `v`, or which is diagonal,
leaves row `v` alone. -/
theorem outRow_snoc_ne {L : List (ℕ × ℕ)} {a b v : ℕ} (h : ¬ (a = v ∧ b ≠ v)) :
    outRow (L ++ [(a, b)]) v = outRow L v := by
  rw [outRow, outCand_append, outCand_singleton, if_neg h, List.append_nil, outRow]

/-- **The step the mark test makes**: at an off-diagonal candidate
`(a, b)`, row `a` grows by `b` exactly when `b` is not already
there. -/
theorem outRow_snoc_eq {L : List (ℕ × ℕ)} {a b : ℕ} (h : b ≠ a) :
    outRow (L ++ [(a, b)]) a
      = if b ∈ outRow L a then outRow L a else outRow L a ++ [b] := by
  rw [outRow, outCand_append, outCand_singleton,
    if_pos (show a = a ∧ b ≠ a from ⟨rfl, h⟩), dedF_snoc, outRow]

theorem outRow_snoc_other {L : List (ℕ × ℕ)} {a b v : ℕ} (h : v ≠ a) :
    outRow (L ++ [(a, b)]) v = outRow L v :=
  outRow_snoc_ne (fun hc => h hc.1.symm)

private theorem foldl_dstep_append (l : List ℕ) :
    ∀ acc : List ℕ, ∃ r, l.foldl dstep acc = acc ++ r := by
  induction l with
  | nil => intro acc; exact ⟨[], by simp⟩
  | cons a l ih =>
      intro acc
      obtain ⟨r, hr⟩ := ih (dstep acc a)
      rw [List.foldl_cons, hr]
      by_cases ha : a ∈ acc
      · exact ⟨r, by rw [dstep, if_pos ha]⟩
      · exact ⟨a :: r, by rw [dstep, if_neg ha, List.append_assoc]; simp⟩

/-- **A row only ever grows at its end**: the row at a prefix of the
enumeration is a prefix of the row at the whole of it.  This is what
makes the emit sweep's cell-by-cell invariant stable, and what bounds
its cursor. -/
theorem outRow_prefix (L M : List (ℕ × ℕ)) (v : ℕ) :
    ∃ r, outRow (L ++ M) v = outRow L v ++ r := by
  rw [outRow, outCand_append, dedF, List.foldl_append]
  exact foldl_dstep_append _ _

theorem length_outRow_le (L M : List (ℕ × ℕ)) (v : ℕ) :
    (outRow L v).length ≤ (outRow (L ++ M) v).length := by
  obtain ⟨r, hr⟩ := outRow_prefix L M v
  rw [hr, List.length_append]
  omega

theorem outRow_getD_of_prefix (L M : List (ℕ × ℕ)) (v i : ℕ)
    (hi : i < (outRow L v).length) :
    (outRow (L ++ M) v).getD i 0 = (outRow L v).getD i 0 := by
  obtain ⟨r, hr⟩ := outRow_prefix L M v
  rw [hr, List.getD_append _ _ _ _ hi]

/-! ## §2 The prefixes of the enumeration

The three loops of a sweep stand at three nested positions in
`fratCands n R`, so each has its own name for "the part already
processed".  These are the lists, their steps, and the fact that each
is a prefix of the whole — which is what tells a sweep body that the
candidate in its hands really occurs in the enumeration. -/

private theorem take_prefix' {α : Type*} (l : List α) {a b : ℕ} (hab : a ≤ b) :
    ∃ M, l.take b = l.take a ++ M := by
  induction b with
  | zero => exact ⟨[], by rw [show a = 0 by omega]; simp⟩
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · obtain ⟨M, hM⟩ := ih (by omega)
        exact ⟨M ++ l[b]?.toList, by rw [List.take_add_one, hM, List.append_assoc]⟩
      · exact ⟨[], by rw [show a = b + 1 by omega]; simp⟩

/-- The candidates of the rows below `w`: the outer loop's processed
part. -/
def fratUpto (R : ℕ → List ℕ) (w : ℕ) : List (ℕ × ℕ) :=
  (List.range w).flatMap (fratPairsAt R)

theorem fratUpto_eq (n : ℕ) (R : ℕ → List ℕ) : fratUpto R n = fratCands n R := rfl

@[simp] theorem fratUpto_zero (R : ℕ → List ℕ) : fratUpto R 0 = [] := rfl

theorem fratUpto_succ (R : ℕ → List ℕ) (w : ℕ) :
    fratUpto R (w + 1) = fratUpto R w ++ fratPairsAt R w := flatPref_succ _ w

private theorem length_flatMap_pair (l m : List ℕ) :
    (l.flatMap fun x => m.map fun y => (x, y)).length = l.length * m.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_map, List.length_cons]
      ring

theorem length_fratPairsAt (R : ℕ → List ℕ) (w : ℕ) :
    (fratPairsAt R w).length = (R w).length * (R w).length :=
  length_flatMap_pair (R w) (R w)

theorem length_fratUpto_succ (R : ℕ → List ℕ) (w : ℕ) :
    (fratUpto R (w + 1)).length
      = (fratUpto R w).length + (R w).length * (R w).length := by
  rw [fratUpto_succ, List.length_append, length_fratPairsAt]

theorem fratUpto_prefix (R : ℕ → List ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ M, fratUpto R b = fratUpto R a ++ M := by
  induction b with
  | zero => exact ⟨[], by rw [show a = 0 by omega]; simp⟩
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · obtain ⟨M, hM⟩ := ih (by omega)
        exact ⟨M ++ fratPairsAt R b, by rw [fratUpto_succ, hM, List.append_assoc]⟩
      · exact ⟨[], by rw [show a = b + 1 by omega]; simp⟩

/-- The candidates of row `w` whose first component is one of the first
`i` slots: the middle loop's processed part of the current row. -/
def fratPre (R : ℕ → List ℕ) (w i : ℕ) : List (ℕ × ℕ) :=
  ((R w).take i).flatMap fun x => (R w).map fun y => (x, y)

/-- The candidates at the `i`-th slot of row `w` whose second component
is one of the first `k` slots: the inner loop's processed part. -/
def fratCur (R : ℕ → List ℕ) (w i k : ℕ) : List (ℕ × ℕ) :=
  ((R w).take k).map fun y => ((R w).getD i 0, y)

@[simp] theorem fratPre_zero (R : ℕ → List ℕ) (w : ℕ) : fratPre R w 0 = [] := by
  simp [fratPre]

@[simp] theorem fratCur_zero (R : ℕ → List ℕ) (w i : ℕ) : fratCur R w i 0 = [] := by
  simp [fratCur]

theorem fratCur_succ (R : ℕ → List ℕ) (w i k : ℕ) (hk : k < (R w).length) :
    fratCur R w i (k + 1)
      = fratCur R w i k ++ [((R w).getD i 0, (R w).getD k 0)] := by
  rw [fratCur, fratCur, List.take_add_one, List.map_append,
    List.getElem?_eq_getElem hk]
  simp [List.getElem?_eq_getElem hk]

theorem fratCur_full (R : ℕ → List ℕ) (w i : ℕ) :
    fratCur R w i (R w).length = (R w).map fun y => ((R w).getD i 0, y) := by
  rw [fratCur, List.take_length]

theorem length_fratCur (R : ℕ → List ℕ) (w i k : ℕ) (hk : k ≤ (R w).length) :
    (fratCur R w i k).length = k := by
  rw [fratCur, List.length_map, List.length_take]
  omega

theorem fratPre_succ' (R : ℕ → List ℕ) (w i : ℕ) (hi : i < (R w).length) :
    fratPre R w (i + 1) = fratPre R w i ++ fratCur R w i (R w).length := by
  rw [fratPre, fratPre, List.take_add_one, List.flatMap_append,
    List.getElem?_eq_getElem hi, fratCur_full]
  simp [List.getElem?_eq_getElem hi]

theorem fratPre_full (R : ℕ → List ℕ) (w : ℕ) :
    fratPre R w (R w).length = fratPairsAt R w := by
  rw [fratPre, List.take_length, fratPairsAt]

theorem fratPre_prefix (R : ℕ → List ℕ) (w : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ M, fratPre R w b = fratPre R w a ++ M := by
  obtain ⟨M, hM⟩ := take_prefix' (R w) hab
  exact ⟨M.flatMap fun x => (R w).map fun y => (x, y), by
    rw [fratPre, hM, List.flatMap_append, fratPre]⟩

theorem fratCur_prefix (R : ℕ → List ℕ) (w i : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ M, fratCur R w i b = fratCur R w i a ++ M := by
  obtain ⟨M, hM⟩ := take_prefix' (R w) hab
  exact ⟨M.map fun y => ((R w).getD i 0, y), by
    rw [fratCur, hM, List.map_append, fratCur]⟩

/-- **The candidate in a sweep body's hands really occurs**: the whole
enumeration splits at it, with everything already processed to its
left.  This is the hypothesis that lets the emit sweep conclude
`y ∈ fratOutRow n R x` from the mark alone. -/
theorem frat_split {n : ℕ} (R : ℕ → List ℕ) {w i k : ℕ} (hw : w < n)
    (hi : i < (R w).length) (hk : k < (R w).length) :
    ∃ M, fratCands n R
      = (fratUpto R w ++ fratPre R w i ++ fratCur R w i k)
        ++ ((R w).getD i 0, (R w).getD k 0) :: M := by
  obtain ⟨M₁, h1⟩ := fratUpto_prefix R (show w + 1 ≤ n by omega)
  obtain ⟨M₂, h2⟩ := fratPre_prefix R w (show i + 1 ≤ (R w).length by omega)
  obtain ⟨M₃, h3⟩ := fratCur_prefix R w i (show k + 1 ≤ (R w).length by omega)
  refine ⟨M₃ ++ M₂ ++ M₁, ?_⟩
  rw [← fratUpto_eq n R, h1, fratUpto_succ, ← fratPre_full R w, h2,
    fratPre_succ' R w i hi, h3, fratCur_succ R w i k hk]
  simp [List.append_assoc]

/-! ## §3 The program

Four sweeps.  The two enumeration sweeps share the skeleton `frSweep`,
whose body `act` is run once per candidate with the first component in
`fr.x`, the second in `fr.y` and the mark row base `x·n` in `fr.b`. -/

/-- The pass's scratch scalars: the three loop counters, the current
row's two bounds, the two components, the mark row base, and the four
scalars of the flat sweeps and the two bodies. -/
def frScalars : List String :=
  ["fr.w", "fr.j0", "fr.e", "fr.p", "fr.q", "fr.x", "fr.y", "fr.b",
    "fr.v", "fr.s", "fr.d", "fr.c"]

/-- One turn of a sweep's innermost loop: read the second component of
the candidate, run the body, advance. -/
def frInnerC (t : String) (act : Com) : Com :=
  .seq (.assign "fr.y" (.get t (.var "fr.q")))
    (.seq act (.assign "fr.q" (.add (.var "fr.q") (.lit 1))))

/-- One turn of a sweep's middle loop: read the first component, form
its mark row base `x·n`, rewind the inner pointer to the row start and
scan the row, advance. -/
def frMidC (nN t : String) (act : Com) : Com :=
  .seq (.assign "fr.x" (.get t (.var "fr.p")))
    (.seq (.assign "fr.b" (.mul (.var "fr.x") (.var nN)))
      (.seq (.assign "fr.q" (.var "fr.j0"))
        (.seq (Csr.scan "fr.q" "fr.e" (frInnerC t act))
          (.assign "fr.p" (.add (.var "fr.p") (.lit 1))))))

/-- One turn of a sweep's outer loop: load row `w`'s two bounds, scan
it, advance. -/
def frOuterC (nN o t : String) (act : Com) : Com :=
  .seq (.assign "fr.j0" (.get o (.var "fr.w")))
    (.seq (.assign "fr.e" (.get o (.add (.var "fr.w") (.lit 1))))
      (.seq (.assign "fr.p" (.var "fr.j0"))
        (.seq (Csr.scan "fr.p" "fr.e" (frMidC nN t act))
          (.assign "fr.w" (.add (.var "fr.w") (.lit 1))))))

/-- **One sweep of the candidate enumeration**: `act` once per element
of `fratCands n (Csr.row off tgt)`, in that list's own order. -/
def frSweep (nN o t : String) (act : Com) : Com :=
  .seq (.assign "fr.w" (.lit 0)) (Csr.scan "fr.w" nN (frOuterC nN o t act))

/-- **Sweep 1**: zero the degree region. -/
def frZeroCom (nN dg : String) : Com :=
  .seq (.assign "fr.v" (.lit 0))
    (Csr.scan "fr.v" nN
      (.seq (.store dg (.var "fr.v") (.lit 0))
        (.assign "fr.v" (.add (.var "fr.v") (.lit 1)))))

/-- **Sweep 3**: prefix-sum the degrees into the output offsets,
leaving the same running sum in `dg` — which the emit sweep then uses
as its cursor array — then close `o'[n]` and publish the slot count in
`nF`. -/
def frOffCom (nN nF o' dg : String) : Com :=
  .seq (.assign "fr.v" (.lit 0))
    (.seq (.assign "fr.s" (.lit 0))
      (.seq (Csr.scan "fr.v" nN
          (.seq (.assign "fr.d" (.get dg (.var "fr.v")))
            (.seq (.store o' (.var "fr.v") (.var "fr.s"))
              (.seq (.store dg (.var "fr.v") (.var "fr.s"))
                (.seq (.assign "fr.s" (.add (.var "fr.s") (.var "fr.d")))
                  (.assign "fr.v" (.add (.var "fr.v") (.lit 1))))))))
        (.seq (.store o' (.var nN) (.var "fr.s"))
          (.assign nF (.var "fr.s")))))

/-- **The counting sweep's body**: at an off-diagonal candidate whose
mark cell is still clear, set the cell and bump the first component's
degree. -/
def frCountAct (dg mk : String) : Com :=
  .ite (.eq (.var "fr.x") (.var "fr.y")) .skip
    (.ite (.eq (.get mk (.add (.var "fr.b") (.var "fr.y"))) (.lit 0))
      (.seq (.store mk (.add (.var "fr.b") (.var "fr.y")) (.lit 1))
        (.seq (.assign "fr.d" (.get dg (.var "fr.x")))
          (.store dg (.var "fr.x") (.add (.var "fr.d") (.lit 1)))))
      .skip)

/-- **The emit sweep's body**: at an off-diagonal candidate whose mark
cell is *set*, clear the cell, write the second component at the first
component's cursor and bump it. -/
def frEmitAct (t' dg mk : String) : Com :=
  .ite (.eq (.var "fr.x") (.var "fr.y")) .skip
    (.ite (.eq (.get mk (.add (.var "fr.b") (.var "fr.y"))) (.lit 1))
      (.seq (.store mk (.add (.var "fr.b") (.var "fr.y")) (.lit 0))
        (.seq (.assign "fr.c" (.get dg (.var "fr.x")))
          (.seq (.store t' (.var "fr.c") (.var "fr.y"))
            (.store dg (.var "fr.x") (.add (.var "fr.c") (.lit 1))))))
      .skip)

/-- **The pass.** -/
def fratCom (nN nF o t o' t' dg mk : String) : Com :=
  .seq (frZeroCom nN dg)
    (.seq (frSweep nN o t (frCountAct dg mk))
      (.seq (frOffCom nN nF o' dg)
        (frSweep nN o t (frEmitAct t' dg mk))))

/-- The two input regions and the four written regions are six distinct
arrays.  `o' ≠ t'` is what `csrPrefix_fratPref` asks; the rest is what
keeps each sweep's frame conditions true. -/
structure FrNames (o t o' t' dg mk : String) : Prop where
  /-- The input offsets are not a written region. -/
  o_o' : o ≠ o'
  /-- … -/
  o_t' : o ≠ t'
  /-- … -/
  o_dg : o ≠ dg
  /-- … -/
  o_mk : o ≠ mk
  /-- The input targets are not a written region. -/
  t_o' : t ≠ o'
  /-- … -/
  t_t' : t ≠ t'
  /-- … -/
  t_dg : t ≠ dg
  /-- … -/
  t_mk : t ≠ mk
  /-- The four written regions are pairwise distinct. -/
  o'_t' : o' ≠ t'
  /-- … -/
  o'_dg : o' ≠ dg
  /-- … -/
  o'_mk : o' ≠ mk
  /-- … -/
  t'_dg : t' ≠ dg
  /-- … -/
  t'_mk : t' ≠ mk
  /-- … -/
  dg_mk : dg ≠ mk

/-! ### Small array and run helpers

The same handful `SolveAugTrans` opens with, restated because they are
private there. -/

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

/-- The twelve scratch names, as twelve disequalities. -/
private theorem frScalars_ne {y : String} (h : y ∉ frScalars) :
    y ≠ "fr.w" ∧ y ≠ "fr.j0" ∧ y ≠ "fr.e" ∧ y ≠ "fr.p" ∧ y ≠ "fr.q" ∧
      y ≠ "fr.x" ∧ y ≠ "fr.y" ∧ y ≠ "fr.b" ∧ y ≠ "fr.v" ∧ y ≠ "fr.s" ∧
      y ≠ "fr.d" ∧ y ≠ "fr.c" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro hc
      rw [hc] at h
      exact h (by simp [frScalars])

/-- **Every mark index is a word**: the cell of the pair `(a, u)` is
below `n·n`, which `FratCsrAt`'s precondition bounds. -/
theorem frRow_lt_sq {n a u : ℕ} (ha : a < n) (hu : u < n) : a * n + u < n * n := by
  have h1 : (a + 1) * n ≤ n * n := Nat.mul_le_mul ha (le_refl n)
  have h2 : (a + 1) * n = a * n + n := by ring
  omega

/-- Two distinct mark rows never share a cell. -/
theorem frRow_ne {n a b x y : ℕ} (hx : x < n) (hy : y < n) (hab : a ≠ b) :
    a * n + x ≠ b * n + y := by
  rcases Nat.lt_or_ge a b with h | h
  · have h1 : (a + 1) * n ≤ b * n := Nat.mul_le_mul h (le_refl n)
    have h2 : (a + 1) * n = a * n + n := by ring
    omega
  · have hba : b < a := by omega
    have h1 : (b + 1) * n ≤ a * n := Nat.mul_le_mul hba (le_refl n)
    have h2 : (b + 1) * n = b * n + n := by ring
    omega

/-! ## §4 The sweep skeleton: what it carries and what it asks

`frSweep` is proved once, at an abstract accumulator `J` indexed by the
prefix of `fratCands` already processed.  A body meets `FrAct`: it
moves `J` from `L` to `L ++ [(a, b)]` at the candidate in its hands and
leaves the loop's own cursors and the input CSR alone.  `J` is required
to depend only on the arrays, which both concrete accumulators do. -/

/-- What every state of a sweep satisfies: the input CSR, untouched,
and the carrier size in its named cell. -/
structure FrFrame (nN o t : String) (n ns : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The input CSR. -/
  csr : Csr o t n ns n off tgt σ
  /-- The carrier size is in its cell. -/
  carrier : σ.vars nN = n

/-- What a sweep's body must leave alone: the input CSR's two arrays,
the carrier cell, and the loop's own seven cursors. -/
structure FrKeep (nN o t : String) (σ σ' : Env) : Prop where
  /-- The input offsets. -/
  aO : σ'.arrs o = σ.arrs o
  /-- The input targets. -/
  aT : σ'.arrs t = σ.arrs t
  /-- The carrier cell. -/
  vN : σ'.vars nN = σ.vars nN
  /-- The outer counter. -/
  vW : σ'.vars "fr.w" = σ.vars "fr.w"
  /-- The current row's start. -/
  vJ : σ'.vars "fr.j0" = σ.vars "fr.j0"
  /-- The current row's end. -/
  vE : σ'.vars "fr.e" = σ.vars "fr.e"
  /-- The middle pointer. -/
  vP : σ'.vars "fr.p" = σ.vars "fr.p"
  /-- The inner pointer. -/
  vQ : σ'.vars "fr.q" = σ.vars "fr.q"
  /-- The first component. -/
  vX : σ'.vars "fr.x" = σ.vars "fr.x"
  /-- The mark row base. -/
  vB : σ'.vars "fr.b" = σ.vars "fr.b"

/-- **The interface of a sweep body.**  Given the accumulator at the
processed prefix `L`, the candidate `(a, b)` in `fr.x`/`fr.y`, its mark
row base in `fr.b`, and the fact that the candidate really occurs where
the loops say it does, `act` advances the accumulator by one candidate
at a cost of `Ka`. -/
def FrAct (B : ℕ) (nN o t : String) (n : ℕ) (R : ℕ → List ℕ)
    (J : List (ℕ × ℕ) → Env → Prop) (act : Com) (Ka : ℕ) : Prop :=
  ∀ (L : List (ℕ × ℕ)) (a b : ℕ) (σ : Env), J L σ → a < n → b < n →
    (∃ M, fratCands n R = L ++ (a, b) :: M) →
    σ.vars "fr.x" = a → σ.vars "fr.y" = b → σ.vars "fr.b" = a * n →
    ∃ σ', Run B act σ σ' Ka ∧ J (L ++ [(a, b)]) σ' ∧ FrKeep nN o t σ σ'

/-- The outer loop's carried state. -/
structure FrO (nN o t : String) (n ns : ℕ) (off tgt : ℕ → ℕ)
    (J : List (ℕ × ℕ) → Env → Prop) (σ : Env) : Prop where
  /-- The ambient reading. -/
  frame : FrFrame nN o t n ns off tgt σ
  /-- The counter stays on the carrier. -/
  wle : σ.vars "fr.w" ≤ n
  /-- The rows below the counter are processed. -/
  acc : J (fratUpto (Csr.row off tgt) (σ.vars "fr.w")) σ

/-- The middle loop's carried state, at row `w`. -/
structure FrM (nN o t : String) (n ns : ℕ) (off tgt : ℕ → ℕ)
    (J : List (ℕ × ℕ) → Env → Prop) (w : ℕ) (σ : Env) : Prop where
  /-- The ambient reading. -/
  frame : FrFrame nN o t n ns off tgt σ
  /-- The row is a vertex. -/
  wlt : w < n
  /-- The row is in its cell. -/
  wval : σ.vars "fr.w" = w
  /-- The row's start. -/
  j0val : σ.vars "fr.j0" = off w
  /-- The row's end. -/
  eval : σ.vars "fr.e" = off (w + 1)
  /-- The middle pointer stays inside the row. -/
  plo : off w ≤ σ.vars "fr.p"
  /-- … -/
  phi : σ.vars "fr.p" ≤ off (w + 1)
  /-- The rows below `w`, and the candidates of `w` whose first
  component lies before the middle pointer. -/
  acc : J (fratUpto (Csr.row off tgt) w
    ++ fratPre (Csr.row off tgt) w (σ.vars "fr.p" - off w)) σ

/-- The innermost loop's carried state, at row `w` and slot `p`. -/
structure FrI (nN o t : String) (n ns : ℕ) (off tgt : ℕ → ℕ)
    (J : List (ℕ × ℕ) → Env → Prop) (w p : ℕ) (σ : Env) : Prop where
  /-- The ambient reading. -/
  frame : FrFrame nN o t n ns off tgt σ
  /-- The row is a vertex. -/
  wlt : w < n
  /-- The row is in its cell. -/
  wval : σ.vars "fr.w" = w
  /-- The row's start. -/
  j0val : σ.vars "fr.j0" = off w
  /-- The row's end. -/
  eval : σ.vars "fr.e" = off (w + 1)
  /-- The middle pointer. -/
  pval : σ.vars "fr.p" = p
  /-- … inside the row. -/
  plo : off w ≤ p
  /-- … -/
  phi : p < off (w + 1)
  /-- The first component. -/
  xval : σ.vars "fr.x" = tgt p
  /-- Its mark row base. -/
  bval : σ.vars "fr.b" = tgt p * n
  /-- The inner pointer stays inside the row. -/
  qlo : off w ≤ σ.vars "fr.q"
  /-- … -/
  qhi : σ.vars "fr.q" ≤ off (w + 1)
  /-- Everything processed, down to the inner pointer. -/
  acc : J (fratUpto (Csr.row off tgt) w ++ fratPre (Csr.row off tgt) w (p - off w)
    ++ fratCur (Csr.row off tgt) w (p - off w) (σ.vars "fr.q" - off w)) σ

/-- Reading the input CSR's row `w` at the offset the middle or inner
pointer stands at. -/
private theorem row_getD (off tgt : ℕ → ℕ) {w p : ℕ} (h1 : off w ≤ p)
    (h2 : p < off (w + 1)) : (Csr.row off tgt w).getD (p - off w) 0 = tgt p := by
  have hlt : p - off w < Csr.rowLen off w := by rw [Csr.rowLen]; omega
  rw [Csr.row, getD_arrOf _ hlt]
  congr 1
  omega

private theorem length_row_eq (off tgt : ℕ → ℕ) (w : ℕ) :
    (Csr.row off tgt w).length = off (w + 1) - off w := by
  rw [Csr.length_row, Csr.rowLen]

/-! ## §5 The three loops of a sweep -/

/-- **One inner turn**, at `Ka + 7`: read the second component of the
candidate, run the body, advance the inner pointer. -/
theorem frInner_step {B : ℕ} {nN o t : String} {n ns : ℕ} {off tgt : ℕ → ℕ}
    {J : List (ℕ × ℕ) → Env → Prop} {act : Com} {Ka : ℕ}
    (hnN : nN ∉ frScalars)
    (hJa : ∀ (L : List (ℕ × ℕ)) (ρ ρ' : Env), ρ'.arrs = ρ.arrs → J L ρ → J L ρ')
    (hact : FrAct B nN o t n (Csr.row off tgt) J act Ka)
    (hnsB : ns < B) (hsqB : n * n < B)
    {w p : ℕ} {σ : Env}
    (hI : FrI nN o t n ns off tgt J w p σ)
    (hqlt : σ.vars "fr.q" < off (w + 1)) :
    ∃ σ' K', Run B (frInnerC t act) σ σ' K' ∧
      FrI nN o t n ns off tgt J w p σ' ∧
      σ'.vars "fr.q" = σ.vars "fr.q" + 1 ∧ K' ≤ Ka + 7 := by
  classical
  obtain ⟨-, -, -, -, hNq, -, hNy, -, -, -, -, -⟩ := frScalars_ne hnN
  have hc := hI.frame.csr
  have hwlt := hI.wlt
  have hplo := hI.plo
  have hphi := hI.phi
  have hqlo := hI.qlo
  obtain ⟨q, hq⟩ : ∃ q, σ.vars "fr.q" = q := ⟨_, rfl⟩
  rw [hq] at hqlt hqlo
  have hrowle : off (w + 1) ≤ ns := hc.row_le hwlt
  have hpns : p < ns := by omega
  have hqns : q < ns := by omega
  have htp : tgt p < n := hc.target hpns
  have htq : tgt q < n := hc.target hqns
  have hn1 : 0 < n := by omega
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn1
  have hqB : q < B := by omega
  have htqB : tgt q < B := by omega
  have h1B : (1 : ℕ) < B := by omega
  have htLen : q < (σ.arrs t).length := by rw [hc.length_tgt]; omega
  -- the read of the second component
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setVar "fr.y" (tgt q) := ⟨_, rfl⟩
  have r1 : Run B (.assign "fr.y" (.get t (.var "fr.q"))) σ τ1 3 := by
    rw [hτ1]
    exact run_assign' (evB_get' (evB_var hq hqB) htLen (hc.getD_tgt hqns) htqB) (by simp)
  have ha1 : τ1.arrs = σ.arrs := by rw [hτ1]; simp
  have hv1 : ∀ y : String, y ≠ "fr.y" → τ1.vars y = σ.vars y := by
    intro y hy; rw [hτ1]; simp [hy]
  have hy1 : τ1.vars "fr.y" = tgt q := by rw [hτ1]; simp
  -- the candidate really occurs there
  have hrlen : (Csr.row off tgt w).length = off (w + 1) - off w := length_row_eq off tgt w
  have hilt : p - off w < (Csr.row off tgt w).length := by rw [hrlen]; omega
  have hklt : q - off w < (Csr.row off tgt w).length := by rw [hrlen]; omega
  have hgi : (Csr.row off tgt w).getD (p - off w) 0 = tgt p := row_getD off tgt hplo hphi
  have hgk : (Csr.row off tgt w).getD (q - off w) 0 = tgt q :=
    row_getD off tgt hqlo (by omega)
  obtain ⟨M, hM⟩ := frat_split (Csr.row off tgt) hwlt hilt hklt
  rw [hgi, hgk] at hM
  have haccL : J (fratUpto (Csr.row off tgt) w ++ fratPre (Csr.row off tgt) w (p - off w)
      ++ fratCur (Csr.row off tgt) w (p - off w) (q - off w)) τ1 := by
    refine hJa _ σ τ1 ha1 ?_
    have h := hI.acc
    rwa [hq] at h
  obtain ⟨τ2, hrun2, hacc2, hkeep⟩ :=
    hact _ (tgt p) (tgt q) τ1 haccL htp htq ⟨M, hM⟩
      (by rw [hv1 _ (by decide)]; exact hI.xval) hy1
      (by rw [hv1 _ (by decide)]; exact hI.bval)
  have hq2 : τ2.vars "fr.q" = q := by rw [hkeep.vQ, hv1 _ (by decide), hq]
  obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = τ2.setVar "fr.q" (q + 1) := ⟨_, rfl⟩
  have r3 : Run B (.assign "fr.q" (.add (.var "fr.q") (.lit 1))) τ2 τ3 4 := by
    rw [hτ3]
    exact run_assign' (evB_add (evB_var hq2 hqB) (evalB_lit h1B) (by omega)) (by simp)
  have ha3 : τ3.arrs = τ2.arrs := by rw [hτ3]; simp
  have hv3 : ∀ y : String, y ≠ "fr.q" → τ3.vars y = τ2.vars y := by
    intro y hy; rw [hτ3]; simp [hy]
  have hq3 : τ3.vars "fr.q" = q + 1 := by rw [hτ3]; simp
  refine ⟨τ3, Ka + 7, (r1.seq (hrun2.seq r3)).mono (by omega), ?_, by rw [hq3, hq], le_rfl⟩
  refine
    { frame :=
        { csr := hc.of_eq (by rw [ha3, hkeep.aO, ha1]) (by rw [ha3, hkeep.aT, ha1])
          carrier := by
            rw [hv3 _ hNq, hkeep.vN, hv1 _ hNy]; exact hI.frame.carrier }
      wlt := hwlt
      wval := by rw [hv3 _ (by decide), hkeep.vW, hv1 _ (by decide)]; exact hI.wval
      j0val := by rw [hv3 _ (by decide), hkeep.vJ, hv1 _ (by decide)]; exact hI.j0val
      eval := by rw [hv3 _ (by decide), hkeep.vE, hv1 _ (by decide)]; exact hI.eval
      pval := by rw [hv3 _ (by decide), hkeep.vP, hv1 _ (by decide)]; exact hI.pval
      plo := hplo
      phi := hphi
      xval := by rw [hv3 _ (by decide), hkeep.vX, hv1 _ (by decide)]; exact hI.xval
      bval := by rw [hv3 _ (by decide), hkeep.vB, hv1 _ (by decide)]; exact hI.bval
      qlo := by rw [hq3]; omega
      qhi := by rw [hq3]; omega
      acc := ?_ }
  have hstep : fratCur (Csr.row off tgt) w (p - off w) (q + 1 - off w)
      = fratCur (Csr.row off tgt) w (p - off w) (q - off w) ++ [(tgt p, tgt q)] := by
    rw [show q + 1 - off w = (q - off w) + 1 by omega,
      fratCur_succ (Csr.row off tgt) w (p - off w) (q - off w) hklt, hgi, hgk]
  rw [hq3, hstep, ← List.append_assoc]
  exact hJa _ τ2 τ3 ha3 hacc2

/-- **The innermost scan**: the whole of row `w` again, one turn a
slot, at `Ka + 11` a slot plus one last test. -/
theorem frInner_scan {B : ℕ} {nN o t : String} {n ns : ℕ} {off tgt : ℕ → ℕ}
    {J : List (ℕ × ℕ) → Env → Prop} {act : Com} {Ka : ℕ}
    (hnN : nN ∉ frScalars)
    (hJa : ∀ (L : List (ℕ × ℕ)) (ρ ρ' : Env), ρ'.arrs = ρ.arrs → J L ρ → J L ρ')
    (hact : FrAct B nN o t n (Csr.row off tgt) J act Ka)
    (hnsB : ns < B) (hsqB : n * n < B) {w p : ℕ} (hhi : off (w + 1) < B) :
    Spec B (fun σ => FrI nN o t n ns off tgt J w p σ ∧ σ.vars "fr.q" = off w)
      (Csr.scan "fr.q" "fr.e" (frInnerC t act))
      (fun _ σ' => FrI nN o t n ns off tgt J w p σ' ∧ σ'.vars "fr.q" = off (w + 1))
      ((Ka + 11) * (off (w + 1) - off w) + 4) :=
  Csr.rowScan_spec B _ (off (w + 1)) (Ka + 7) "fr.q" "fr.e" (frInnerC t act)
    (fun σ => FrI nN o t n ns off tgt J w p σ) hhi
    (fun _ hI => ⟨hI.eval, hI.qhi⟩)
    (fun _ hI hlt => frInner_step hnN hJa hact hnsB hsqB hI hlt)
    (fun _ h => h.1) (fun _ h => by rw [h.2])

private theorem lt_of_sq_lt {n B : ℕ} (h : n * n < B) : n < B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · omega
  · have : n ≤ n * n := Nat.le_mul_of_pos_left n hn
    omega

/-- **One middle turn**, at `17 + (Ka + 11)·|row w|`: read the first
component, form its mark row base, rewind the inner pointer and scan
row `w`, advance.  The `(Ka + 11)`-a-slot term is the inner scan's, and
it is what the budget's `fratPairCount` pays. -/
theorem frMid_step {B : ℕ} {nN o t : String} {n ns : ℕ} {off tgt : ℕ → ℕ}
    {J : List (ℕ × ℕ) → Env → Prop} {act : Com} {Ka : ℕ}
    (hnN : nN ∉ frScalars)
    (hJa : ∀ (L : List (ℕ × ℕ)) (ρ ρ' : Env), ρ'.arrs = ρ.arrs → J L ρ → J L ρ')
    (hact : FrAct B nN o t n (Csr.row off tgt) J act Ka)
    (hnsB : ns < B) (hsqB : n * n < B)
    {w : ℕ} {σ : Env}
    (hM : FrM nN o t n ns off tgt J w σ)
    (hplt : σ.vars "fr.p" < off (w + 1)) :
    ∃ σ' K', Run B (frMidC nN t act) σ σ' K' ∧
      FrM nN o t n ns off tgt J w σ' ∧
      σ'.vars "fr.p" = σ.vars "fr.p" + 1 ∧
      K' ≤ 17 + (Ka + 11) * (off (w + 1) - off w) := by
  classical
  obtain ⟨hNw, hNj, hNe, hNp, hNq, hNx, -, hNb, -, -, -, -⟩ := frScalars_ne hnN
  have hc := hM.frame.csr
  have hwlt := hM.wlt
  have hplo := hM.plo
  obtain ⟨p, hp⟩ : ∃ p, σ.vars "fr.p" = p := ⟨_, rfl⟩
  rw [hp] at hplt hplo
  have hrowle : off (w + 1) ≤ ns := hc.row_le hwlt
  have hoffw : off w ≤ off (w + 1) := hc.mono (by omega) (by omega)
  have hpns : p < ns := by omega
  have htp : tgt p < n := hc.target hpns
  have hn1 : 0 < n := by omega
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn1
  have hnB : n < B := lt_of_sq_lt hsqB
  have hpB : p < B := by omega
  have htpB : tgt p < B := by omega
  have h1B : (1 : ℕ) < B := by omega
  have hbB : tgt p * n < B := lt_trans (by have := frRow_lt_sq htp hn1; omega) hsqB
  have hoffB : off (w + 1) < B := by omega
  have howB : off w < B := by omega
  have htLen : p < (σ.arrs t).length := by rw [hc.length_tgt]; omega
  have hrlen : (Csr.row off tgt w).length = off (w + 1) - off w := length_row_eq off tgt w
  have hilt : p - off w < (Csr.row off tgt w).length := by rw [hrlen]; omega
  -- read the first component
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setVar "fr.x" (tgt p) := ⟨_, rfl⟩
  have r1 : Run B (.assign "fr.x" (.get t (.var "fr.p"))) σ τ1 3 := by
    rw [hτ1]
    exact run_assign' (evB_get' (evB_var hp hpB) htLen (hc.getD_tgt hpns) htpB) (by simp)
  have ha1 : τ1.arrs = σ.arrs := by rw [hτ1]; simp
  have hv1 : ∀ y : String, y ≠ "fr.x" → τ1.vars y = σ.vars y := by
    intro y hy; rw [hτ1]; simp [hy]
  have hx1 : τ1.vars "fr.x" = tgt p := by rw [hτ1]; simp
  -- form its mark row base
  obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "fr.b" (tgt p * n) := ⟨_, rfl⟩
  have r2 : Run B (.assign "fr.b" (.mul (.var "fr.x") (.var nN))) τ1 τ2 4 := by
    rw [hτ2]
    exact run_assign' (evB_mul (evB_var hx1 htpB)
      (evB_var (by rw [hv1 nN hNx]; exact hM.frame.carrier) hnB) hbB) (by simp)
  have ha2 : τ2.arrs = σ.arrs := by rw [hτ2]; simp [ha1]
  have hv2 : ∀ y : String, y ≠ "fr.x" → y ≠ "fr.b" → τ2.vars y = σ.vars y := by
    intro y hy hy'; rw [hτ2]; simp [hy']; exact hv1 y hy
  have hx2 : τ2.vars "fr.x" = tgt p := by rw [hτ2]; simp [hx1]
  have hb2 : τ2.vars "fr.b" = tgt p * n := by rw [hτ2]; simp
  -- rewind the inner pointer
  obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = τ2.setVar "fr.q" (off w) := ⟨_, rfl⟩
  have r3 : Run B (.assign "fr.q" (.var "fr.j0")) τ2 τ3 2 := by
    rw [hτ3]
    exact run_assign' (evB_var (by rw [hv2 _ (by decide) (by decide)]; exact hM.j0val)
      howB) (by simp)
  have ha3 : τ3.arrs = σ.arrs := by rw [hτ3]; simp [ha2]
  have hv3 : ∀ y : String, y ≠ "fr.x" → y ≠ "fr.b" → y ≠ "fr.q" →
      τ3.vars y = σ.vars y := by
    intro y hy hy' hy''; rw [hτ3]; simp [hy'']; exact hv2 y hy hy'
  have hq3 : τ3.vars "fr.q" = off w := by rw [hτ3]; simp
  have hI3 : FrI nN o t n ns off tgt J w p τ3 :=
    { frame :=
        { csr := hc.of_eq (by rw [ha3]) (by rw [ha3])
          carrier := by rw [hv3 nN hNx hNb hNq]; exact hM.frame.carrier }
      wlt := hwlt
      wval := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hM.wval
      j0val := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hM.j0val
      eval := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hM.eval
      pval := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hp
      plo := hplo
      phi := hplt
      xval := by rw [hτ3]; simp [hx2]
      bval := by rw [hτ3]; simp [hb2]
      qlo := by rw [hq3]
      qhi := by rw [hq3]; omega
      acc := by
        rw [hq3, Nat.sub_self, fratCur_zero, List.append_nil]
        refine hJa _ σ τ3 ha3 ?_
        have h := hM.acc
        rwa [hp] at h }
  obtain ⟨τ4, hrun4, hI4, hq4⟩ :=
    (frInner_scan (p := p) hnN hJa hact hnsB hsqB hoffB).run ⟨hI3, hq3⟩
  -- advance the middle pointer
  have hp4 : τ4.vars "fr.p" = p := hI4.pval
  obtain ⟨τ5, hτ5⟩ : ∃ τ, τ = τ4.setVar "fr.p" (p + 1) := ⟨_, rfl⟩
  have r5 : Run B (.assign "fr.p" (.add (.var "fr.p") (.lit 1))) τ4 τ5 4 := by
    rw [hτ5]
    exact run_assign' (evB_add (evB_var hp4 hpB) (evalB_lit h1B) (by omega)) (by simp)
  have ha5 : τ5.arrs = τ4.arrs := by rw [hτ5]; simp
  have hv5 : ∀ y : String, y ≠ "fr.p" → τ5.vars y = τ4.vars y := by
    intro y hy; rw [hτ5]; simp [hy]
  have hp5 : τ5.vars "fr.p" = p + 1 := by rw [hτ5]; simp
  refine ⟨τ5, 17 + (Ka + 11) * (off (w + 1) - off w),
    (r1.seq (r2.seq (r3.seq (hrun4.seq r5)))).mono (by omega), ?_,
    by rw [hp5, hp], le_rfl⟩
  refine
    { frame :=
        { csr := hI4.frame.csr.of_eq (by rw [ha5]) (by rw [ha5])
          carrier := by rw [hv5 nN hNp]; exact hI4.frame.carrier }
      wlt := hwlt
      wval := by rw [hv5 _ (by decide)]; exact hI4.wval
      j0val := by rw [hv5 _ (by decide)]; exact hI4.j0val
      eval := by rw [hv5 _ (by decide)]; exact hI4.eval
      plo := by rw [hp5]; omega
      phi := by rw [hp5]; omega
      acc := ?_ }
  have hstep : fratPre (Csr.row off tgt) w (p + 1 - off w)
      = fratPre (Csr.row off tgt) w (p - off w)
        ++ fratCur (Csr.row off tgt) w (p - off w) (Csr.row off tgt w).length := by
    rw [show p + 1 - off w = (p - off w) + 1 by omega,
      fratPre_succ' (Csr.row off tgt) w (p - off w) hilt]
  rw [hp5, hstep, ← List.append_assoc]
  refine hJa _ τ4 τ5 ha5 ?_
  have h := hI4.acc
  rwa [hq4, show off (w + 1) - off w = (Csr.row off tgt w).length from hrlen.symm] at h

/-- **The middle scan**: the slots of row `w` of the input, one turn a
slot.  This is where the enumeration's nested loop is amortized — the
turn count is the row's length and each turn carries the row's length
again, so the two together are the row's contribution to
`fratPairCount`. -/
theorem frMid_scan {B : ℕ} {nN o t : String} {n ns : ℕ} {off tgt : ℕ → ℕ}
    {J : List (ℕ × ℕ) → Env → Prop} {act : Com} {Ka : ℕ}
    (hnN : nN ∉ frScalars)
    (hJa : ∀ (L : List (ℕ × ℕ)) (ρ ρ' : Env), ρ'.arrs = ρ.arrs → J L ρ → J L ρ')
    (hact : FrAct B nN o t n (Csr.row off tgt) J act Ka)
    (hnsB : ns < B) (hsqB : n * n < B) {w : ℕ} (hhi : off (w + 1) < B) :
    Spec B (fun σ => FrM nN o t n ns off tgt J w σ ∧ σ.vars "fr.p" = off w)
      (Csr.scan "fr.p" "fr.e" (frMidC nN t act))
      (fun _ σ' => FrM nN o t n ns off tgt J w σ' ∧ σ'.vars "fr.p" = off (w + 1))
      ((21 + (Ka + 11) * (off (w + 1) - off w)) * (off (w + 1) - off w) + 4) :=
  Csr.rowScan_spec B _ (off (w + 1)) (17 + (Ka + 11) * (off (w + 1) - off w))
    "fr.p" "fr.e" (frMidC nN t act)
    (fun σ => FrM nN o t n ns off tgt J w σ) hhi
    (fun _ hM => ⟨hM.eval, hM.phi⟩)
    (fun _ hM hlt => frMid_step hnN hJa hact hnsB hsqB hM hlt)
    (fun _ h => h.1)
    (fun _ h => by
      rw [h.2, show 17 + (Ka + 11) * (off (w + 1) - off w) + 4
        = 21 + (Ka + 11) * (off (w + 1) - off w) from by omega])

/-- **One outer turn**, at `18 + 21·|row w| + (Ka + 11)·|row w|²`: load
the row's two bounds, scan it, advance. -/
theorem frOuter_step {B : ℕ} {nN o t : String} {n ns : ℕ} {off tgt : ℕ → ℕ}
    {J : List (ℕ × ℕ) → Env → Prop} {act : Com} {Ka : ℕ}
    (hnN : nN ∉ frScalars)
    (hJa : ∀ (L : List (ℕ × ℕ)) (ρ ρ' : Env), ρ'.arrs = ρ.arrs → J L ρ → J L ρ')
    (hact : FrAct B nN o t n (Csr.row off tgt) J act Ka)
    (hnsB : ns < B) (hsqB : n * n < B) {σ : Env}
    (hO : FrO nN o t n ns off tgt J σ)
    (hwlt : σ.vars "fr.w" < n) :
    ∃ σ' K', Run B (frOuterC nN o t act) σ σ' K' ∧
      FrO nN o t n ns off tgt J σ' ∧
      σ'.vars "fr.w" = σ.vars "fr.w" + 1 ∧
      K' ≤ 18 + 21 * (off (σ.vars "fr.w" + 1) - off (σ.vars "fr.w"))
        + (Ka + 11) * ((off (σ.vars "fr.w" + 1) - off (σ.vars "fr.w"))
          * (off (σ.vars "fr.w" + 1) - off (σ.vars "fr.w"))) := by
  classical
  obtain ⟨hNw, hNj, hNe, hNp, -, -, -, -, -, -, -, -⟩ := frScalars_ne hnN
  have hc := hO.frame.csr
  obtain ⟨w, hw⟩ : ∃ w, σ.vars "fr.w" = w := ⟨_, rfl⟩
  rw [hw] at hwlt
  have hrowle : off (w + 1) ≤ ns := hc.row_le hwlt
  have hoffw : off w ≤ off (w + 1) := hc.mono (by omega) (by omega)
  have hn1 : 0 < n := by omega
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn1
  have hnB : n < B := lt_of_sq_lt hsqB
  have hwB : w < B := by omega
  have h1B : (1 : ℕ) < B := by omega
  have hoffB : off (w + 1) < B := by omega
  have howB : off w < B := by omega
  have hoLen : (σ.arrs o).length = n + 1 := hc.length_off
  have hrlen : (Csr.row off tgt w).length = off (w + 1) - off w := length_row_eq off tgt w
  -- the row's start
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setVar "fr.j0" (off w) := ⟨_, rfl⟩
  have r1 : Run B (.assign "fr.j0" (.get o (.var "fr.w"))) σ τ1 3 := by
    rw [hτ1]
    exact run_assign' (evB_get' (evB_var hw hwB) (by omega)
      (hc.getD_off (by omega)) howB) (by simp)
  have ha1 : τ1.arrs = σ.arrs := by rw [hτ1]; simp
  have hv1 : ∀ y : String, y ≠ "fr.j0" → τ1.vars y = σ.vars y := by
    intro y hy; rw [hτ1]; simp [hy]
  -- the row's end
  obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "fr.e" (off (w + 1)) := ⟨_, rfl⟩
  have r2 : Run B (.assign "fr.e" (.get o (.add (.var "fr.w") (.lit 1)))) τ1 τ2 5 := by
    rw [hτ2]
    refine run_assign' (evB_get' (evB_add (evB_var (by rw [hv1 _ (by decide)]; exact hw) hwB)
      (evalB_lit h1B) (by omega)) ?_ ?_ hoffB) (by simp)
    · rw [ha1]; omega
    · rw [ha1]; exact hc.getD_off (by omega)
  have ha2 : τ2.arrs = σ.arrs := by rw [hτ2]; simp [ha1]
  have hv2 : ∀ y : String, y ≠ "fr.j0" → y ≠ "fr.e" → τ2.vars y = σ.vars y := by
    intro y hy hy'; rw [hτ2]; simp [hy']; exact hv1 y hy
  have hj02 : τ2.vars "fr.j0" = off w := by rw [hτ2]; simp [hτ1]
  have he2 : τ2.vars "fr.e" = off (w + 1) := by rw [hτ2]; simp
  -- the middle pointer
  obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = τ2.setVar "fr.p" (off w) := ⟨_, rfl⟩
  have r3 : Run B (.assign "fr.p" (.var "fr.j0")) τ2 τ3 2 := by
    rw [hτ3]; exact run_assign' (evB_var hj02 howB) (by simp)
  have ha3 : τ3.arrs = σ.arrs := by rw [hτ3]; simp [ha2]
  have hv3 : ∀ y : String, y ≠ "fr.j0" → y ≠ "fr.e" → y ≠ "fr.p" →
      τ3.vars y = σ.vars y := by
    intro y hy hy' hy''; rw [hτ3]; simp [hy'']; exact hv2 y hy hy'
  have hp3 : τ3.vars "fr.p" = off w := by rw [hτ3]; simp
  have hM3 : FrM nN o t n ns off tgt J w τ3 :=
    { frame :=
        { csr := hc.of_eq (by rw [ha3]) (by rw [ha3])
          carrier := by rw [hv3 nN hNj hNe hNp]; exact hO.frame.carrier }
      wlt := hwlt
      wval := by rw [hv3 _ (by decide) (by decide) (by decide)]; exact hw
      j0val := by rw [hτ3]; simp [hj02]
      eval := by rw [hτ3]; simp [he2]
      plo := by rw [hp3]
      phi := by rw [hp3]; omega
      acc := by
        rw [hp3, Nat.sub_self, fratPre_zero, List.append_nil]
        refine hJa _ σ τ3 ha3 ?_
        have h := hO.acc
        rwa [hw] at h }
  obtain ⟨τ4, hrun4, hM4, hp4⟩ :=
    (frMid_scan (w := w) hnN hJa hact hnsB hsqB hoffB).run ⟨hM3, hp3⟩
  -- advance the outer counter
  have hw4 : τ4.vars "fr.w" = w := hM4.wval
  obtain ⟨τ5, hτ5⟩ : ∃ τ, τ = τ4.setVar "fr.w" (w + 1) := ⟨_, rfl⟩
  have r5 : Run B (.assign "fr.w" (.add (.var "fr.w") (.lit 1))) τ4 τ5 4 := by
    rw [hτ5]
    exact run_assign' (evB_add (evB_var hw4 hwB) (evalB_lit h1B) (by omega)) (by simp)
  have ha5 : τ5.arrs = τ4.arrs := by rw [hτ5]; simp
  have hv5 : ∀ y : String, y ≠ "fr.w" → τ5.vars y = τ4.vars y := by
    intro y hy; rw [hτ5]; simp [hy]
  have hw5 : τ5.vars "fr.w" = w + 1 := by rw [hτ5]; simp
  refine ⟨τ5, 18 + 21 * (off (w + 1) - off w)
    + (Ka + 11) * ((off (w + 1) - off w) * (off (w + 1) - off w)),
    (r1.seq (r2.seq (r3.seq (hrun4.seq r5)))).mono (by
      have hexp : (21 + (Ka + 11) * (off (w + 1) - off w)) * (off (w + 1) - off w)
          = 21 * (off (w + 1) - off w)
            + (Ka + 11) * ((off (w + 1) - off w) * (off (w + 1) - off w)) := by ring
      omega), ?_,
    by rw [hw5, hw], by rw [hw]⟩
  refine
    { frame :=
        { csr := hM4.frame.csr.of_eq (by rw [ha5]) (by rw [ha5])
          carrier := by rw [hv5 nN hNw]; exact hM4.frame.carrier }
      wle := by rw [hw5]; omega
      acc := ?_ }
  have hstep : fratUpto (Csr.row off tgt) (w + 1)
      = fratUpto (Csr.row off tgt) w
        ++ fratPre (Csr.row off tgt) w (Csr.row off tgt w).length := by
    rw [fratUpto_succ, fratPre_full]
  rw [hw5, hstep]
  refine hJa _ τ4 τ5 ha5 ?_
  have h := hM4.acc
  rwa [hp4, show off (w + 1) - off w = (Csr.row off tgt w).length from hrlen.symm] at h

theorem length_fratUpto_le {n : ℕ} (R : ℕ → List ℕ) {w : ℕ} (hw : w ≤ n) :
    (fratUpto R w).length ≤ (fratCands n R).length := by
  obtain ⟨M, hM⟩ := fratUpto_prefix R hw
  rw [← fratUpto_eq n R, hM, List.length_append]
  omega

/-! ## §6 The sweep -/

/-- **The outer scan**: one turn a row, at `22` a row, `21` an arc and
`Ka + 11` a candidate.  This is the sweep's whole charge — linear in
`n`, the input's slot count and the size of the enumeration, with no
term in `n²` and no carrier scan inside a row's turn. -/
theorem frOuter_scan {B : ℕ} {nN o t : String} {n ns : ℕ} {off tgt : ℕ → ℕ}
    {J : List (ℕ × ℕ) → Env → Prop} {act : Com} {Ka : ℕ}
    (hnN : nN ∉ frScalars)
    (hJa : ∀ (L : List (ℕ × ℕ)) (ρ ρ' : Env), ρ'.arrs = ρ.arrs → J L ρ → J L ρ')
    (hact : FrAct B nN o t n (Csr.row off tgt) J act Ka)
    (hnsB : ns < B) (hsqB : n * n < B) :
    Spec B (fun σ => FrO nN o t n ns off tgt J σ ∧ σ.vars "fr.w" = 0)
      (Csr.scan "fr.w" nN (frOuterC nN o t act))
      (fun _ σ' => FrO nN o t n ns off tgt J σ' ∧ σ'.vars "fr.w" = n)
      (22 * n + 21 * ns + (Ka + 11) * (fratCands n (Csr.row off tgt)).length + 4) := by
  have hnB : n < B := lt_of_sq_lt hsqB
  have hbound : ∀ σ : Env, FrO nN o t n ns off tgt J σ →
      σ.vars "fr.w" < B ∧ σ.vars nN < B := by
    intro σ hO
    have h1 := hO.wle
    have h2 := hO.frame.carrier
    exact ⟨by omega, by omega⟩
  refine (Spec.while_potential (b := .lt (.var "fr.w") (.var nN))
    (fun σ => FrO nN o t n ns off tgt J σ)
    (fun σ => 22 * (n - σ.vars "fr.w") + 21 * (ns - off (σ.vars "fr.w"))
      + (Ka + 11) * ((fratCands n (Csr.row off tgt)).length
        - (fratUpto (Csr.row off tgt) (σ.vars "fr.w")).length))
    (fun σ hO => evalB_condLt_vars (hbound σ hO).1 (hbound σ hO).2) ?_ (fun _ h => h.1)
    ?_).post ?_
  · intro σ hO hc
    have hwlt : σ.vars "fr.w" < n := by
      have h1 := lt_of_condLt_true hc
      have h2 := hO.frame.carrier
      omega
    obtain ⟨σ', K', hrun, hO', hw', hK'⟩ := frOuter_step hnN hJa hact hnsB hsqB hO hwlt
    refine ⟨σ', K', hrun, hO', ?_⟩
    have hcsr := hO.frame.csr
    have hmono : off (σ.vars "fr.w") ≤ off (σ.vars "fr.w" + 1) :=
      hcsr.mono (by omega) (by omega)
    have hle : off (σ.vars "fr.w" + 1) ≤ ns := hcsr.row_le hwlt
    have hrlen : (Csr.row off tgt (σ.vars "fr.w")).length
        = off (σ.vars "fr.w" + 1) - off (σ.vars "fr.w") :=
      length_row_eq off tgt _
    have hLsucc : (fratUpto (Csr.row off tgt) (σ.vars "fr.w" + 1)).length
        = (fratUpto (Csr.row off tgt) (σ.vars "fr.w")).length
          + (off (σ.vars "fr.w" + 1) - off (σ.vars "fr.w"))
            * (off (σ.vars "fr.w" + 1) - off (σ.vars "fr.w")) := by
      rw [length_fratUpto_succ, hrlen]
    have hLle : (fratUpto (Csr.row off tgt) (σ.vars "fr.w" + 1)).length
        ≤ (fratCands n (Csr.row off tgt)).length :=
      length_fratUpto_le _ (by omega)
    have hmul : (Ka + 11) * ((fratCands n (Csr.row off tgt)).length
          - (fratUpto (Csr.row off tgt) (σ.vars "fr.w")).length)
        = (Ka + 11) * ((fratCands n (Csr.row off tgt)).length
            - (fratUpto (Csr.row off tgt) (σ.vars "fr.w" + 1)).length)
          + (Ka + 11) * ((off (σ.vars "fr.w" + 1) - off (σ.vars "fr.w"))
            * (off (σ.vars "fr.w" + 1) - off (σ.vars "fr.w"))) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    simp only [size_condLt, size_var]
    rw [hw']
    omega
  · intro σ h
    have hz := h.2
    have hcsr := h.1.frame.csr
    have h0 : off 0 ≤ ns := hcsr.le_ns (by omega)
    simp only [size_condLt, size_var]
    rw [hz]
    simp only [fratUpto_zero, List.length_nil, Nat.sub_zero]
    omega
  · rintro σ σ' - ⟨hO', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hO'.frame.carrier
    have h3 := hO'.wle
    exact ⟨hO', by omega⟩

/-- **One sweep**, discharged: from the input CSR and the accumulator at
the empty prefix, `frSweep` leaves the accumulator at the whole of
`fratCands n (Csr.row off tgt)`, at
`22·n + 21·ns + (Ka + 11)·|fratCands| + 6`. -/
theorem frSweep_spec {B : ℕ} {nN o t : String} {n ns : ℕ} {off tgt : ℕ → ℕ}
    {J : List (ℕ × ℕ) → Env → Prop} {act : Com} {Ka : ℕ}
    (hnN : nN ∉ frScalars)
    (hJa : ∀ (L : List (ℕ × ℕ)) (ρ ρ' : Env), ρ'.arrs = ρ.arrs → J L ρ → J L ρ')
    (hact : FrAct B nN o t n (Csr.row off tgt) J act Ka)
    (hnsB : ns < B) (hsqB : n * n < B) :
    Spec B (fun σ => FrFrame nN o t n ns off tgt σ ∧ J [] σ)
      (frSweep nN o t act)
      (fun _ σ' => FrFrame nN o t n ns off tgt σ' ∧
        J (fratCands n (Csr.row off tgt)) σ')
      (22 * n + 21 * ns + (Ka + 11) * (fratCands n (Csr.row off tgt)).length + 6) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hfr, hJ0⟩ := hσ
  obtain ⟨hNw, -, -, -, -, -, -, -, -, -, -, -⟩ := frScalars_ne hnN
  have h0B : (0 : ℕ) < B := by omega
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setVar "fr.w" 0 := ⟨_, rfl⟩
  have r1 : Run B (.assign "fr.w" (.lit 0)) σ τ1 2 := by
    rw [hτ1]; exact run_assign' (evalB_lit h0B) (by simp)
  have ha1 : τ1.arrs = σ.arrs := by rw [hτ1]; simp
  have hw1 : τ1.vars "fr.w" = 0 := by rw [hτ1]; simp
  have hO1 : FrO nN o t n ns off tgt J τ1 :=
    { frame :=
        { csr := hfr.csr.of_eq (by rw [ha1]) (by rw [ha1])
          carrier := by rw [hτ1, vars_setVar, if_neg hNw]; exact hfr.carrier }
      wle := by rw [hw1]; omega
      acc := by rw [hw1, fratUpto_zero]; exact hJa _ σ τ1 ha1 hJ0 }
  obtain ⟨τ2, hrun2, hO2, hw2⟩ := (frOuter_scan hnN hJa hact hnsB hsqB).run ⟨hO1, hw1⟩
  refine ⟨τ2, 22 * n + 21 * ns
      + (Ka + 11) * (fratCands n (Csr.row off tgt)).length + 6,
    (r1.seq hrun2).mono (by omega), le_rfl, hO2.frame, ?_⟩
  have h := hO2.acc
  rwa [hw2, fratUpto_eq] at h

/-! ## §7 The counting sweep -/

/-- A duplicate-free list of vertices is no longer than the carrier. -/
theorem length_le_of_lt {l : List ℕ} {n : ℕ} (hnd : l.Nodup) (hlt : ∀ y ∈ l, y < n) :
    l.length ≤ n := by
  classical
  have h1 : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnd
  have h2 : l.toFinset ⊆ Finset.range n := fun y hy =>
    Finset.mem_range.2 (hlt y (List.mem_toFinset.1 hy))
  have h3 := Finset.card_le_card h2
  rw [h1, Finset.card_range] at h3
  exact h3

/-- A diagonal candidate changes no row. -/
theorem outRow_snoc_diag {L : List (ℕ × ℕ)} {a : ℕ} (v : ℕ) :
    outRow (L ++ [(a, a)]) v = outRow L v := outRow_snoc_ne (fun h => h.2 h.1)

/-- Nor does a candidate whose second component is already in its
row. -/
theorem outRow_snoc_mem {L : List (ℕ × ℕ)} {a b : ℕ} (hab : b ≠ a)
    (hmem : b ∈ outRow L a) (v : ℕ) : outRow (L ++ [(a, b)]) v = outRow L v := by
  rcases eq_or_ne v a with rfl | hv
  · rw [outRow_snoc_eq hab, if_pos hmem]
  · exact outRow_snoc_other hv

/-- **The counting sweep's accumulator.**  At the processed prefix `L`:
every row's entries are vertices, each degree cell counts its row's
entries, and the mark cell of `(x, y)` is set exactly when `y` is
already in row `x`. -/
structure FrCount (dg mk : String) (n : ℕ) (L : List (ℕ × ℕ)) (σ : Env) : Prop where
  /-- The degree region. -/
  dgLen : n ≤ (σ.arrs dg).length
  /-- The mark region. -/
  mkLen : n * n ≤ (σ.arrs mk).length
  /-- Every entry of every row is a vertex. -/
  entLt : ∀ x, x < n → ∀ y ∈ outRow L x, y < n
  /-- The degrees so far. -/
  deg : ∀ x, x < n → (σ.arrs dg).getD x 0 = (outRow L x).length
  /-- The marks so far. -/
  mark : ∀ x, x < n → ∀ y, y < n →
    (σ.arrs mk).getD (x * n + y) 0 = if y ∈ outRow L x then 1 else 0

theorem frCount_arrs (dg mk : String) (n : ℕ) (L : List (ℕ × ℕ)) (σ σ' : Env)
    (h : σ'.arrs = σ.arrs) (hJ : FrCount dg mk n L σ) : FrCount dg mk n L σ' where
  dgLen := by rw [h]; exact hJ.dgLen
  mkLen := by rw [h]; exact hJ.mkLen
  entLt := hJ.entLt
  deg := by rw [h]; exact hJ.deg
  mark := by rw [h]; exact hJ.mark

/-- **The counting sweep's body meets `FrAct` at `24`.** -/
theorem frCount_act {B : ℕ} {nN o t o' t' dg mk : String} {n : ℕ} {R : ℕ → List ℕ}
    (hnm : FrNames o t o' t' dg mk) (hnN : nN ∉ frScalars) (hsqB : n * n < B) :
    FrAct B nN o t n R (FrCount dg mk n) (frCountAct dg mk) 24 := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hNd, -⟩ := frScalars_ne hnN
  intro L a b σ hJ ha hb _ hx hy hbb
  have hn1 : 0 < n := by omega
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn1
  have h0B : (0 : ℕ) < B := by omega
  have h1B : (1 : ℕ) < B := by omega
  have haB : a < B := by omega
  have hbB : b < B := by omega
  have hidx : a * n + b < n * n := frRow_lt_sq ha hb
  have hmkL : a * n + b < (σ.arrs mk).length := lt_of_lt_of_le hidx hJ.mkLen
  have hbase : (Expr.add (.var "fr.b") (.var "fr.y")).evalB B σ = some (a * n + b) :=
    evB_add (evB_var hbb (by omega)) (evB_var hy hbB) (by omega)
  have hcond1 : (Cond.eq (.var "fr.x") (.var "fr.y")).evalB B σ = some (a == b) :=
    evalB_condEq (evB_var hx haB) (evB_var hy hbB)
  by_cases hab : a = b
  · refine ⟨σ, (Run.ite_true (by rw [hcond1, hab]; simp) Run.skip).mono (by simp), ?_,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    subst hab
    exact
      { dgLen := hJ.dgLen
        mkLen := hJ.mkLen
        entLt := by
          intro x hx' y hy'; rw [outRow_snoc_diag] at hy'; exact hJ.entLt x hx' y hy'
        deg := by intro x hx'; rw [outRow_snoc_diag]; exact hJ.deg x hx'
        mark := by intro x hx' y hy'; rw [outRow_snoc_diag]; exact hJ.mark x hx' y hy' }
  · have hba : b ≠ a := fun hc => hab hc.symm
    have hcondF : (Cond.eq (.var "fr.x") (.var "fr.y")).evalB B σ = some false := by
      rw [hcond1]; simp [hab]
    have hmk := hJ.mark a ha b hb
    by_cases hmem : b ∈ outRow L a
    · have hmkv : (σ.arrs mk).getD (a * n + b) 0 = 1 := by rw [hmk, if_pos hmem]
      have hcond2 : (Cond.eq (.get mk (.add (.var "fr.b") (.var "fr.y"))) (.lit 0)).evalB B σ
          = some false := by
        rw [evalB_condEq (evB_get' hbase hmkL hmkv h1B) (evalB_lit h0B)]; simp
      refine ⟨σ, (Run.ite_false hcondF (Run.ite_false hcond2 Run.skip)).mono (by simp), ?_,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      have hsame : ∀ v, outRow (L ++ [(a, b)]) v = outRow L v := outRow_snoc_mem hba hmem
      exact
        { dgLen := hJ.dgLen
          mkLen := hJ.mkLen
          entLt := by intro x hx' y hy'; rw [hsame] at hy'; exact hJ.entLt x hx' y hy'
          deg := by intro x hx'; rw [hsame]; exact hJ.deg x hx'
          mark := by intro x hx' y hy'; rw [hsame]; exact hJ.mark x hx' y hy' }
    · have hmkv : (σ.arrs mk).getD (a * n + b) 0 = 0 := by rw [hmk, if_neg hmem]
      have hcond2 : (Cond.eq (.get mk (.add (.var "fr.b") (.var "fr.y"))) (.lit 0)).evalB B σ
          = some true := by
        rw [evalB_condEq (evB_get' hbase hmkL hmkv h0B) (evalB_lit h0B)]; simp
      have hrow : outRow (L ++ [(a, b)]) a = outRow L a ++ [b] := by
        rw [outRow_snoc_eq hba, if_neg hmem]
      have hother : ∀ v, v ≠ a → outRow (L ++ [(a, b)]) v = outRow L v :=
        fun v hv => outRow_snoc_other hv
      have hentNew : ∀ y ∈ outRow (L ++ [(a, b)]) a, y < n := by
        intro y hy'
        rw [hrow] at hy'
        rcases List.mem_append.1 hy' with h | h
        · exact hJ.entLt a ha y h
        · rw [List.mem_singleton.1 h]; exact hb
      have hdeglt : (outRow L a).length + 1 ≤ n := by
        have h := length_le_of_lt (nodup_outRow (L ++ [(a, b)]) a) hentNew
        rw [hrow, List.length_append, List.length_singleton] at h
        exact h
      have hdgv : (σ.arrs dg).getD a 0 = (outRow L a).length := hJ.deg a ha
      have hdgL : a < (σ.arrs dg).length := lt_of_lt_of_le ha hJ.dgLen
      obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setArr mk (a * n + b) 1 := ⟨_, rfl⟩
      have r1 : Run B (.store mk (.add (.var "fr.b") (.var "fr.y")) (.lit 1)) σ τ1 5 := by
        rw [hτ1]; exact run_store' hbase (evalB_lit h1B) hmkL (by simp)
      have ha1dg : τ1.arrs dg = σ.arrs dg := by rw [hτ1, arrs_setArr, if_neg hnm.dg_mk]
      obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "fr.d" (outRow L a).length := ⟨_, rfl⟩
      have r2 : Run B (.assign "fr.d" (.get dg (.var "fr.x"))) τ1 τ2 3 := by
        rw [hτ2]
        refine run_assign' (evB_get' (evB_var ?_ haB) ?_ ?_ (by omega)) (by simp)
        · rw [hτ1, vars_setArr]; exact hx
        · rw [ha1dg]; exact hdgL
        · rw [ha1dg]; exact hdgv
      obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = τ2.setArr dg a ((outRow L a).length + 1) := ⟨_, rfl⟩
      have r3 : Run B (.store dg (.var "fr.x") (.add (.var "fr.d") (.lit 1))) τ2 τ3 5 := by
        rw [hτ3]
        refine run_store' (evB_var ?_ haB)
          (evB_add (evB_var ?_ (by omega)) (evalB_lit h1B) (by omega)) ?_ (by simp)
        · rw [hτ2, vars_setVar, if_neg (by decide), hτ1, vars_setArr]; exact hx
        · rw [hτ2, vars_setVar, if_pos rfl]
        · rw [hτ2, arrs_setVar, ha1dg]; exact hdgL
      have h3dg : τ3.arrs dg = (σ.arrs dg).set a ((outRow L a).length + 1) := by
        rw [hτ3, arrs_setArr, if_pos rfl, hτ2, arrs_setVar, ha1dg]
      have h3mk : τ3.arrs mk = (σ.arrs mk).set (a * n + b) 1 := by
        rw [hτ3, arrs_setArr, if_neg (Ne.symm hnm.dg_mk), hτ2, arrs_setVar, hτ1,
          arrs_setArr, if_pos rfl]
      have h3other : ∀ c : String, c ≠ dg → c ≠ mk → τ3.arrs c = σ.arrs c := by
        intro c hc1 hc2
        rw [hτ3, arrs_setArr, if_neg hc1, hτ2, arrs_setVar, hτ1, arrs_setArr, if_neg hc2]
      have h3vars : ∀ y : String, y ≠ "fr.d" → τ3.vars y = σ.vars y := by
        intro y hy'
        rw [hτ3, vars_setArr, hτ2, vars_setVar, if_neg hy', hτ1, vars_setArr]
      refine ⟨τ3,
        (Run.ite_false hcondF (Run.ite_true hcond2 (r1.seq (r2.seq r3)))).mono (by simp),
        ?_, ?_⟩
      · refine { dgLen := ?_, mkLen := ?_, entLt := ?_, deg := ?_, mark := ?_ }
        · rw [h3dg, List.length_set]; exact hJ.dgLen
        · rw [h3mk, List.length_set]; exact hJ.mkLen
        · intro x hx' y hy'
          rcases eq_or_ne x a with rfl | hxa
          · exact hentNew y hy'
          · rw [hother x hxa] at hy'; exact hJ.entLt x hx' y hy'
        · intro x hx'
          rcases eq_or_ne x a with rfl | hxa
          · rw [h3dg, getD_set_self hdgL, hrow, List.length_append, List.length_singleton]
          · rw [h3dg, getD_set_of_ne (Ne.symm hxa), hother x hxa]; exact hJ.deg x hx'
        · intro x hx' y hy'
          rcases eq_or_ne x a with rfl | hxa
          · rcases eq_or_ne y b with rfl | hyb
            · rw [h3mk, getD_set_self hmkL, hrow, if_pos (by simp)]
            · rw [h3mk, getD_set_of_ne (by omega), hrow, hJ.mark x hx' y hy']
              by_cases hin : y ∈ outRow L x
              · rw [if_pos hin, if_pos (List.mem_append.2 (Or.inl hin))]
              · rw [if_neg hin, if_neg ?_]
                intro hc
                rcases List.mem_append.1 hc with h | h
                · exact hin h
                · exact hyb (List.mem_singleton.1 h)
          · rw [h3mk, getD_set_of_ne (Ne.symm (frRow_ne hy' hb hxa)), hother x hxa]
            exact hJ.mark x hx' y hy'
      · exact
          { aO := h3other o hnm.o_dg hnm.o_mk
            aT := h3other t hnm.t_dg hnm.t_mk
            vN := h3vars nN hNd
            vW := h3vars _ (by decide)
            vJ := h3vars _ (by decide)
            vE := h3vars _ (by decide)
            vP := h3vars _ (by decide)
            vQ := h3vars _ (by decide)
            vX := h3vars _ (by decide)
            vB := h3vars _ (by decide) }

/-! ## §8 The emit sweep -/

theorem fratOff_mono (n : ℕ) (R : ℕ → List ℕ) {a b : ℕ} (h : a ≤ b) :
    fratOff n R a ≤ fratOff n R b := by
  induction b with
  | zero => rw [show a = 0 by omega]
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hb | hb
      · have h1 := ih (by omega)
        rw [fratOff_succ]
        omega
      · rw [show a = b + 1 by omega]

/-- **Distinct rows own disjoint slots of the output.**  This is what
keeps the emit sweep's cell-by-cell invariant true of every row while
it writes into one. -/
theorem fratOff_disj {n : ℕ} (R : ℕ → List ℕ) {x a i j : ℕ} (hxa : x ≠ a)
    (hi : i < (fratOutRow n R x).length) (hj : j < (fratOutRow n R a).length) :
    fratOff n R x + i ≠ fratOff n R a + j := by
  rcases Nat.lt_or_ge x a with h | h
  · have h1 : fratOff n R (x + 1) ≤ fratOff n R a := fratOff_mono n R (by omega)
    rw [fratOff_succ] at h1
    omega
  · have h1 : fratOff n R (a + 1) ≤ fratOff n R x := fratOff_mono n R (by omega)
    rw [fratOff_succ] at h1
    omega

/-- **The emit sweep's accumulator.**  At the processed prefix `L`:
each cursor stands at its row's offset plus what has been emitted, the
slots between hold exactly that, and the mark cell of `(x, y)` is set
exactly when `y` belongs to row `x` of the *finished* output and has
not been emitted yet (Finding 3). -/
structure FrEmit (t' dg mk : String) (n : ℕ) (R : ℕ → List ℕ)
    (L : List (ℕ × ℕ)) (σ : Env) : Prop where
  /-- The cursor region. -/
  dgLen : n ≤ (σ.arrs dg).length
  /-- The mark region. -/
  mkLen : n * n ≤ (σ.arrs mk).length
  /-- The output target region. -/
  tLen : fratNs n R ≤ (σ.arrs t').length
  /-- Each cursor. -/
  cur : ∀ x, x < n → (σ.arrs dg).getD x 0 = fratOff n R x + (outRow L x).length
  /-- Each mark. -/
  mark : ∀ x, x < n → ∀ y, y < n →
    (σ.arrs mk).getD (x * n + y) 0
      = if y ∈ fratOutRow n R x ∧ y ∉ outRow L x then 1 else 0
  /-- Each slot written so far. -/
  slots : ∀ x, x < n → ∀ i, i < (outRow L x).length →
    (σ.arrs t').getD (fratOff n R x + i) 0 = (outRow L x).getD i 0

theorem frEmit_arrs (t' dg mk : String) (n : ℕ) (R : ℕ → List ℕ)
    (L : List (ℕ × ℕ)) (σ σ' : Env) (h : σ'.arrs = σ.arrs)
    (hJ : FrEmit t' dg mk n R L σ) : FrEmit t' dg mk n R L σ' where
  dgLen := by rw [h]; exact hJ.dgLen
  mkLen := by rw [h]; exact hJ.mkLen
  tLen := by rw [h]; exact hJ.tLen
  cur := by rw [h]; exact hJ.cur
  mark := by rw [h]; exact hJ.mark
  slots := by rw [h]; exact hJ.slots

/-- **The emit sweep's body meets `FrAct` at `27`.** -/
theorem frEmit_act {B : ℕ} {nN o t o' t' dg mk : String} {n : ℕ} {R : ℕ → List ℕ}
    (hnm : FrNames o t o' t' dg mk) (hnN : nN ∉ frScalars)
    (hsqB : n * n < B) (hfB : fratNs n R < B) :
    FrAct B nN o t n R (FrEmit t' dg mk n R) (frEmitAct t' dg mk) 27 := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hNc⟩ := frScalars_ne hnN
  intro L a b σ hJ ha hb hsplit hx hy hbb
  have hn1 : 0 < n := by omega
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn1
  have h0B : (0 : ℕ) < B := by omega
  have h1B : (1 : ℕ) < B := by omega
  have haB : a < B := by omega
  have hbB : b < B := by omega
  have hidx : a * n + b < n * n := frRow_lt_sq ha hb
  have hmkL : a * n + b < (σ.arrs mk).length := lt_of_lt_of_le hidx hJ.mkLen
  have hbase : (Expr.add (.var "fr.b") (.var "fr.y")).evalB B σ = some (a * n + b) :=
    evB_add (evB_var hbb (by omega)) (evB_var hy hbB) (by omega)
  have hcond1 : (Cond.eq (.var "fr.x") (.var "fr.y")).evalB B σ = some (a == b) :=
    evalB_condEq (evB_var hx haB) (evB_var hy hbB)
  obtain ⟨M, hM⟩ := hsplit
  have hLM : fratCands n R = (L ++ [(a, b)]) ++ M := by rw [hM]; simp
  have hpre1 : ∀ v, ∃ r, fratOutRow n R v = outRow L v ++ r := by
    intro v; rw [fratOutRow_eq, hM]; exact outRow_prefix L ((a, b) :: M) v
  have hpre2 : ∀ v, ∃ r, fratOutRow n R v = outRow (L ++ [(a, b)]) v ++ r := by
    intro v; rw [fratOutRow_eq, hLM]; exact outRow_prefix (L ++ [(a, b)]) M v
  have hlen1 : ∀ v, (outRow L v).length ≤ (fratOutRow n R v).length := by
    intro v; obtain ⟨r, hr⟩ := hpre1 v; rw [hr, List.length_append]; omega
  have hmemC : (a, b) ∈ fratCands n R := by rw [hM]; simp
  by_cases hab : a = b
  · refine ⟨σ, (Run.ite_true (by rw [hcond1, hab]; simp) Run.skip).mono (by simp), ?_,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    subst hab
    exact
      { dgLen := hJ.dgLen
        mkLen := hJ.mkLen
        tLen := hJ.tLen
        cur := by intro x hx'; rw [outRow_snoc_diag]; exact hJ.cur x hx'
        mark := by intro x hx' y hy'; rw [outRow_snoc_diag]; exact hJ.mark x hx' y hy'
        slots := by intro x hx' i hi'; rw [outRow_snoc_diag] at hi' ⊢; exact hJ.slots x hx' i hi' }
  · have hba : b ≠ a := fun hc => hab hc.symm
    have hcondF : (Cond.eq (.var "fr.x") (.var "fr.y")).evalB B σ = some false := by
      rw [hcond1]; simp [hab]
    have hbmem : b ∈ fratOutRow n R a := by
      rw [fratOutRow_eq]; exact mem_outRow.2 ⟨hmemC, hba⟩
    by_cases hmem : b ∈ outRow L a
    · have hmkv : (σ.arrs mk).getD (a * n + b) 0 = 0 := by
        rw [hJ.mark a ha b hb, if_neg (fun hc => hc.2 hmem)]
      have hcond2 : (Cond.eq (.get mk (.add (.var "fr.b") (.var "fr.y"))) (.lit 1)).evalB B σ
          = some false := by
        rw [evalB_condEq (evB_get' hbase hmkL hmkv h0B) (evalB_lit h1B)]; simp
      refine ⟨σ, (Run.ite_false hcondF (Run.ite_false hcond2 Run.skip)).mono (by simp), ?_,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      have hsame : ∀ v, outRow (L ++ [(a, b)]) v = outRow L v := outRow_snoc_mem hba hmem
      exact
        { dgLen := hJ.dgLen
          mkLen := hJ.mkLen
          tLen := hJ.tLen
          cur := by intro x hx'; rw [hsame]; exact hJ.cur x hx'
          mark := by intro x hx' y hy'; rw [hsame]; exact hJ.mark x hx' y hy'
          slots := by intro x hx' i hi'; rw [hsame] at hi' ⊢; exact hJ.slots x hx' i hi' }
    · have hmkv : (σ.arrs mk).getD (a * n + b) 0 = 1 := by
        rw [hJ.mark a ha b hb, if_pos ⟨hbmem, hmem⟩]
      have hcond2 : (Cond.eq (.get mk (.add (.var "fr.b") (.var "fr.y"))) (.lit 1)).evalB B σ
          = some true := by
        rw [evalB_condEq (evB_get' hbase hmkL hmkv h1B) (evalB_lit h1B)]; simp
      have hrow : outRow (L ++ [(a, b)]) a = outRow L a ++ [b] := by
        rw [outRow_snoc_eq hba, if_neg hmem]
      have hother : ∀ v, v ≠ a → outRow (L ++ [(a, b)]) v = outRow L v :=
        fun v hv => outRow_snoc_other hv
      have hstrict : (outRow L a).length < (fratOutRow n R a).length := by
        obtain ⟨r, hr⟩ := hpre2 a
        rw [hr, hrow, List.length_append, List.length_append, List.length_singleton]
        omega
      -- the cursor and its bounds
      obtain ⟨c, hc⟩ : ∃ c, c = fratOff n R a + (outRow L a).length := ⟨_, rfl⟩
      have hcsucc : c < fratOff n R (a + 1) := by
        rw [hc, fratOff_succ]; omega
      have hcns : c < fratNs n R := by
        have := fratOff_mono n R (show a + 1 ≤ n by omega)
        rw [fratNs]; omega
      have hcB : c < B := by omega
      have hctL : c < (σ.arrs t').length := lt_of_lt_of_le hcns hJ.tLen
      have hcurv : (σ.arrs dg).getD a 0 = c := by rw [hc]; exact hJ.cur a ha
      have hdgL : a < (σ.arrs dg).length := lt_of_lt_of_le ha hJ.dgLen
      obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setArr mk (a * n + b) 0 := ⟨_, rfl⟩
      have r1 : Run B (.store mk (.add (.var "fr.b") (.var "fr.y")) (.lit 0)) σ τ1 5 := by
        rw [hτ1]; exact run_store' hbase (evalB_lit h0B) hmkL (by simp)
      have ha1dg : τ1.arrs dg = σ.arrs dg := by rw [hτ1, arrs_setArr, if_neg hnm.dg_mk]
      have ha1t : τ1.arrs t' = σ.arrs t' := by rw [hτ1, arrs_setArr, if_neg hnm.t'_mk]
      obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "fr.c" c := ⟨_, rfl⟩
      have r2 : Run B (.assign "fr.c" (.get dg (.var "fr.x"))) τ1 τ2 3 := by
        rw [hτ2]
        refine run_assign' (evB_get' (evB_var ?_ haB) ?_ ?_ hcB) (by simp)
        · rw [hτ1, vars_setArr]; exact hx
        · rw [ha1dg]; exact hdgL
        · rw [ha1dg]; exact hcurv
      have h2c : τ2.vars "fr.c" = c := by rw [hτ2, vars_setVar, if_pos rfl]
      have h2y : τ2.vars "fr.y" = b := by
        rw [hτ2, vars_setVar, if_neg (by decide), hτ1, vars_setArr]; exact hy
      have h2x : τ2.vars "fr.x" = a := by
        rw [hτ2, vars_setVar, if_neg (by decide), hτ1, vars_setArr]; exact hx
      have ha2t : τ2.arrs t' = σ.arrs t' := by rw [hτ2, arrs_setVar, ha1t]
      have ha2dg : τ2.arrs dg = σ.arrs dg := by rw [hτ2, arrs_setVar, ha1dg]
      obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = τ2.setArr t' c b := ⟨_, rfl⟩
      have r3 : Run B (.store t' (.var "fr.c") (.var "fr.y")) τ2 τ3 3 := by
        rw [hτ3]
        exact run_store' (evB_var h2c hcB) (evB_var h2y hbB) (by rw [ha2t]; exact hctL)
          (by simp)
      have ha3dg : τ3.arrs dg = σ.arrs dg := by
        rw [hτ3, arrs_setArr, if_neg hnm.t'_dg.symm, ha2dg]
      obtain ⟨τ4, hτ4⟩ : ∃ τ, τ = τ3.setArr dg a (c + 1) := ⟨_, rfl⟩
      have r4 : Run B (.store dg (.var "fr.x") (.add (.var "fr.c") (.lit 1))) τ3 τ4 5 := by
        rw [hτ4]
        refine run_store' (evB_var ?_ haB)
          (evB_add (evB_var ?_ hcB) (evalB_lit h1B) (by omega)) ?_ (by simp)
        · rw [hτ3, vars_setArr]; exact h2x
        · rw [hτ3, vars_setArr]; exact h2c
        · rw [ha3dg]; exact hdgL
      have h4dg : τ4.arrs dg = (σ.arrs dg).set a (c + 1) := by
        rw [hτ4, arrs_setArr, if_pos rfl, ha3dg]
      have h4t : τ4.arrs t' = (σ.arrs t').set c b := by
        rw [hτ4, arrs_setArr, if_neg hnm.t'_dg, hτ3, arrs_setArr, if_pos rfl, ha2t]
      have h4mk : τ4.arrs mk = (σ.arrs mk).set (a * n + b) 0 := by
        rw [hτ4, arrs_setArr, if_neg (Ne.symm hnm.dg_mk), hτ3, arrs_setArr,
          if_neg (Ne.symm hnm.t'_mk), hτ2, arrs_setVar, hτ1, arrs_setArr, if_pos rfl]
      have h4other : ∀ z : String, z ≠ dg → z ≠ t' → z ≠ mk → τ4.arrs z = σ.arrs z := by
        intro z hz1 hz2 hz3
        rw [hτ4, arrs_setArr, if_neg hz1, hτ3, arrs_setArr, if_neg hz2, hτ2, arrs_setVar,
          hτ1, arrs_setArr, if_neg hz3]
      have h4vars : ∀ z : String, z ≠ "fr.c" → τ4.vars z = σ.vars z := by
        intro z hz
        rw [hτ4, vars_setArr, hτ3, vars_setArr, hτ2, vars_setVar, if_neg hz, hτ1,
          vars_setArr]
      refine ⟨τ4,
        (Run.ite_false hcondF
          (Run.ite_true hcond2 (r1.seq (r2.seq (r3.seq r4))))).mono (by simp), ?_, ?_⟩
      · refine { dgLen := ?_, mkLen := ?_, tLen := ?_, cur := ?_, mark := ?_, slots := ?_ }
        · rw [h4dg, List.length_set]; exact hJ.dgLen
        · rw [h4mk, List.length_set]; exact hJ.mkLen
        · rw [h4t, List.length_set]; exact hJ.tLen
        · intro x hx'
          rcases eq_or_ne x a with rfl | hxa
          · rw [h4dg, getD_set_self hdgL, hrow, List.length_append, List.length_singleton, hc]
            omega
          · rw [h4dg, getD_set_of_ne (Ne.symm hxa), hother x hxa]; exact hJ.cur x hx'
        · intro x hx' y hy'
          rcases eq_or_ne x a with rfl | hxa
          · rcases eq_or_ne y b with rfl | hyb
            · rw [h4mk, getD_set_self hmkL, hrow, if_neg ?_]
              rintro ⟨-, hc2⟩
              exact hc2 (List.mem_append.2 (Or.inr (by simp)))
            · rw [h4mk, getD_set_of_ne (by omega), hrow, hJ.mark x hx' y hy']
              by_cases hin : y ∈ outRow L x
              · rw [if_neg (fun hcj => hcj.2 hin),
                  if_neg (fun hcj => hcj.2 (List.mem_append.2 (Or.inl hin)))]
              · have hnot : y ∉ outRow L x ++ [b] := by
                  intro hcj
                  rcases List.mem_append.1 hcj with h | h
                  · exact hin h
                  · exact hyb (List.mem_singleton.1 h)
                by_cases hfy : y ∈ fratOutRow n R x
                · rw [if_pos ⟨hfy, hin⟩, if_pos ⟨hfy, hnot⟩]
                · rw [if_neg (fun hcj => hfy hcj.1), if_neg (fun hcj => hfy hcj.1)]
          · rw [h4mk, getD_set_of_ne (Ne.symm (frRow_ne hy' hb hxa)), hother x hxa]
            exact hJ.mark x hx' y hy'
        · intro x hx' i hi'
          rcases eq_or_ne x a with rfl | hxa
          · rw [hrow, List.length_append, List.length_singleton] at hi'
            rcases Nat.lt_or_ge i (outRow L x).length with hlt | hge
            · rw [h4t, getD_set_of_ne (by rw [hc]; omega), hJ.slots x hx' i hlt, hrow,
                List.getD_append _ _ _ _ hlt]
            · have hie : i = (outRow L x).length := by omega
              subst hie
              rw [h4t, ← hc, getD_set_self hctL, hrow,
                List.getD_append_right _ _ _ _ (le_refl _)]
              simp
          · rw [hother x hxa] at hi' ⊢
            have hile : i < (fratOutRow n R x).length := lt_of_lt_of_le hi' (hlen1 x)
            rw [h4t, getD_set_of_ne ?_, hJ.slots x hx' i hi']
            rw [hc]
            exact Ne.symm (fratOff_disj R hxa hile hstrict)
      · exact
          { aO := h4other o hnm.o_dg hnm.o_t' hnm.o_mk
            aT := h4other t hnm.t_dg hnm.t_t' hnm.t_mk
            vN := h4vars nN hNc
            vW := h4vars _ (by decide)
            vJ := h4vars _ (by decide)
            vE := h4vars _ (by decide)
            vP := h4vars _ (by decide)
            vQ := h4vars _ (by decide)
            vX := h4vars _ (by decide)
            vB := h4vars _ (by decide) }

/-! ## §9 The two flat carrier sweeps -/

/-- **Sweep 1, discharged**: the degree region is zeroed, at
`11·n + 6`. -/
theorem frZero_spec {B : ℕ} {nN dg : String} {n : ℕ}
    (hnN : nN ∉ frScalars) (hnB : n < B) :
    Spec B (fun σ => σ.vars nN = n ∧ n ≤ (σ.arrs dg).length)
      (frZeroCom nN dg)
      (fun _ σ' => σ'.vars nN = n ∧ n ≤ (σ'.arrs dg).length ∧
        ∀ x, x < n → (σ'.arrs dg).getD x 0 = 0)
      (11 * n + 6) := by
  obtain ⟨-, -, -, -, -, -, -, -, hNv, -, -, -⟩ := frScalars_ne hnN
  have hbody : Spec B
      (fun σ => (σ.vars nN = n ∧ σ.vars "fr.v" ≤ n ∧ n ≤ (σ.arrs dg).length ∧
        ∀ x, x < σ.vars "fr.v" → (σ.arrs dg).getD x 0 = 0) ∧ σ.vars "fr.v" < n)
      (.seq (.store dg (.var "fr.v") (.lit 0))
        (.assign "fr.v" (.add (.var "fr.v") (.lit 1))))
      (fun σ σ' => (σ'.vars nN = n ∧ σ'.vars "fr.v" ≤ n ∧ n ≤ (σ'.arrs dg).length ∧
        ∀ x, x < σ'.vars "fr.v" → (σ'.arrs dg).getD x 0 = 0) ∧
        σ'.vars "fr.v" = σ.vars "fr.v" + 1) 7 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hnn, hvle, hdl, hz⟩, hvlt⟩ := hσ
    obtain ⟨v, hv⟩ : ∃ v, σ.vars "fr.v" = v := ⟨_, rfl⟩
    rw [hv] at hvlt hvle hz
    have h0B : (0 : ℕ) < B := by omega
    have h1B : (1 : ℕ) < B := by omega
    have hvB : v < B := by omega
    have hvL : v < (σ.arrs dg).length := by omega
    obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setArr dg v 0 := ⟨_, rfl⟩
    have r1 : Run B (.store dg (.var "fr.v") (.lit 0)) σ τ1 3 := by
      rw [hτ1]; exact run_store' (evB_var hv hvB) (evalB_lit h0B) hvL (by simp)
    obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "fr.v" (v + 1) := ⟨_, rfl⟩
    have r2 : Run B (.assign "fr.v" (.add (.var "fr.v") (.lit 1))) τ1 τ2 4 := by
      rw [hτ2]
      exact run_assign' (evB_add (evB_var (by rw [hτ1, vars_setArr]; exact hv) hvB)
        (evalB_lit h1B) (by omega)) (by simp)
    have h2dg : τ2.arrs dg = (σ.arrs dg).set v 0 := by
      rw [hτ2, arrs_setVar, hτ1, arrs_setArr, if_pos rfl]
    have h2v : τ2.vars "fr.v" = v + 1 := by rw [hτ2, vars_setVar, if_pos rfl]
    have h2nN : τ2.vars nN = n := by
      rw [hτ2, vars_setVar, if_neg hNv, hτ1, vars_setArr]; exact hnn
    refine ⟨τ2, 7, (r1.seq r2).mono (by omega), le_rfl, ⟨h2nN, ?_, ?_, ?_⟩, by rw [h2v, hv]⟩
    · rw [h2v]; omega
    · rw [h2dg, List.length_set]; exact hdl
    · intro x hx'
      rw [h2v] at hx'
      rcases eq_or_ne x v with rfl | hxv
      · rw [h2dg, getD_set_self hvL]
      · rw [h2dg, getD_set_of_ne (Ne.symm hxv)]; exact hz x (by omega)
  refine Spec.conseq (Spec.forRangeZero (B := B) "fr.v" nN
    (fun σ => σ.vars nN = n ∧ σ.vars "fr.v" ≤ n ∧ n ≤ (σ.arrs dg).length ∧
      ∀ x, x < σ.vars "fr.v" → (σ.arrs dg).getD x 0 = 0) n 7 hnB
    (fun _ hI => hI.2.1) (fun _ hI => hI.1) hbody) ?_ ?_ (le_refl _)
  · rintro σ ⟨h1, h2⟩
    refine ⟨?_, by simp, by simpa using h2, ?_⟩
    · rw [vars_setVar, if_neg hNv]; exact h1
    · intro x hx'; simp at hx'
  · rintro σ σ' - ⟨⟨h1, -, h3, h4⟩, h5⟩
    exact ⟨h1, h3, fun x hx' => h4 x (by omega)⟩

/-- The prefix-sum sweep's carried state: the running sum is the offset
at the counter, the offsets below it are written into both `o'` and the
cursor region, and the degrees from it on are still untouched. -/
private def OffInv (nN o' dg : String) (n : ℕ) (R : ℕ → List ℕ) (σ : Env) : Prop :=
  σ.vars nN = n ∧ σ.vars "fr.v" ≤ n ∧ σ.vars "fr.s" = fratOff n R (σ.vars "fr.v") ∧
    n + 1 ≤ (σ.arrs o').length ∧ n ≤ (σ.arrs dg).length ∧
    (∀ i, i < σ.vars "fr.v" → (σ.arrs o').getD i 0 = fratOff n R i) ∧
    (∀ x, x < σ.vars "fr.v" → (σ.arrs dg).getD x 0 = fratOff n R x) ∧
    (∀ x, σ.vars "fr.v" ≤ x → x < n → (σ.arrs dg).getD x 0 = (fratOutRow n R x).length)

theorem fratOff_le_ns {n : ℕ} (R : ℕ → List ℕ) {k : ℕ} (hk : k ≤ n) :
    fratOff n R k ≤ fratNs n R := fratOff_mono n R hk

/-- **Sweep 3, discharged**: the degrees become the offsets, in `o'`
and in the cursor region alike, `o'[n]` is closed and the slot count is
published, at `21·n + 13`. -/
theorem frOff_spec {B : ℕ} {nN nF o' dg : String} {n : ℕ} {R : ℕ → List ℕ}
    (hnN : nN ∉ frScalars) (hnF : nF ∉ frScalars) (hFN : nF ≠ nN) (hod : o' ≠ dg)
    (hnB : n < B) (hfB : fratNs n R < B) :
    Spec B (fun σ => σ.vars nN = n ∧ n + 1 ≤ (σ.arrs o').length ∧
        n ≤ (σ.arrs dg).length ∧
        ∀ x, x < n → (σ.arrs dg).getD x 0 = (fratOutRow n R x).length)
      (frOffCom nN nF o' dg)
      (fun _ σ' => σ'.vars nN = n ∧ σ'.vars nF = fratNs n R ∧
        n + 1 ≤ (σ'.arrs o').length ∧ n ≤ (σ'.arrs dg).length ∧
        (∀ i, i ≤ n → (σ'.arrs o').getD i 0 = fratOff n R i) ∧
        (∀ x, x < n → (σ'.arrs dg).getD x 0 = fratOff n R x))
      (21 * n + 13) := by
  obtain ⟨-, -, -, -, -, -, -, -, hNv, hNs, hNd, -⟩ := frScalars_ne hnN
  obtain ⟨-, -, -, -, -, -, -, -, hFv, hFs, hFd, -⟩ := frScalars_ne hnF
  have h0B : (0 : ℕ) < B := by omega
  -- one turn of the prefix-sum loop
  have hbody : ∀ σ : Env, OffInv nN o' dg n R σ → σ.vars "fr.v" < n →
      ∃ σ' K', Run B
        (.seq (.assign "fr.d" (.get dg (.var "fr.v")))
          (.seq (.store o' (.var "fr.v") (.var "fr.s"))
            (.seq (.store dg (.var "fr.v") (.var "fr.s"))
              (.seq (.assign "fr.s" (.add (.var "fr.s") (.var "fr.d")))
                (.assign "fr.v" (.add (.var "fr.v") (.lit 1))))))) σ σ' K' ∧
        OffInv nN o' dg n R σ' ∧ σ'.vars "fr.v" = σ.vars "fr.v" + 1 ∧ K' ≤ 17 := by
    intro σ hI hvlt
    obtain ⟨hnn, hvle, hs, hoL, hdL, ho, hd, hdeg⟩ := hI
    obtain ⟨v, hv⟩ : ∃ v, σ.vars "fr.v" = v := ⟨_, rfl⟩
    rw [hv] at hvlt hvle hs ho hd hdeg
    have h1B : (1 : ℕ) < B := by omega
    have hvB : v < B := by omega
    have hstep : fratOff n R (v + 1) = fratOff n R v + (fratOutRow n R v).length :=
      fratOff_succ n R v
    have hoffle : fratOff n R (v + 1) ≤ fratNs n R := fratOff_le_ns R (by omega)
    have hsB : fratOff n R v < B := by omega
    have hdegB : (fratOutRow n R v).length < B := by omega
    have hvdL : v < (σ.arrs dg).length := by omega
    have hvoL : v < (σ.arrs o').length := by omega
    obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setVar "fr.d" (fratOutRow n R v).length := ⟨_, rfl⟩
    have r1 : Run B (.assign "fr.d" (.get dg (.var "fr.v"))) σ τ1 3 := by
      rw [hτ1]
      exact run_assign' (evB_get' (evB_var hv hvB) hvdL (hdeg v (by omega) hvlt) hdegB)
        (by simp)
    have ha1 : τ1.arrs = σ.arrs := by rw [hτ1]; simp
    have h1v : τ1.vars "fr.v" = v := by rw [hτ1, vars_setVar, if_neg (by decide)]; exact hv
    have h1s : τ1.vars "fr.s" = fratOff n R v := by
      rw [hτ1, vars_setVar, if_neg (by decide)]; exact hs
    have h1d : τ1.vars "fr.d" = (fratOutRow n R v).length := by
      rw [hτ1, vars_setVar, if_pos rfl]
    obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setArr o' v (fratOff n R v) := ⟨_, rfl⟩
    have r2 : Run B (.store o' (.var "fr.v") (.var "fr.s")) τ1 τ2 3 := by
      rw [hτ2]
      exact run_store' (evB_var h1v hvB) (evB_var h1s hsB) (by rw [ha1]; exact hvoL) (by simp)
    obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = τ2.setArr dg v (fratOff n R v) := ⟨_, rfl⟩
    have r3 : Run B (.store dg (.var "fr.v") (.var "fr.s")) τ2 τ3 3 := by
      rw [hτ3]
      refine run_store' (evB_var ?_ hvB) (evB_var ?_ hsB) ?_ (by simp)
      · rw [hτ2, vars_setArr]; exact h1v
      · rw [hτ2, vars_setArr]; exact h1s
      · rw [hτ2, arrs_setArr, if_neg (Ne.symm hod), ha1]; exact hvdL
    obtain ⟨τ4, hτ4⟩ : ∃ τ, τ = τ3.setVar "fr.s" (fratOff n R (v + 1)) := ⟨_, rfl⟩
    have r4 : Run B (.assign "fr.s" (.add (.var "fr.s") (.var "fr.d"))) τ3 τ4 4 := by
      rw [hτ4, hstep]
      refine run_assign' (evB_add (evB_var ?_ hsB) (evB_var ?_ hdegB) (by omega)) (by simp)
      · rw [hτ3, vars_setArr, hτ2, vars_setArr]; exact h1s
      · rw [hτ3, vars_setArr, hτ2, vars_setArr]; exact h1d
    obtain ⟨τ5, hτ5⟩ : ∃ τ, τ = τ4.setVar "fr.v" (v + 1) := ⟨_, rfl⟩
    have r5 : Run B (.assign "fr.v" (.add (.var "fr.v") (.lit 1))) τ4 τ5 4 := by
      rw [hτ5]
      refine run_assign' (evB_add (evB_var ?_ hvB) (evalB_lit h1B) (by omega)) (by simp)
      rw [hτ4, vars_setVar, if_neg (by decide), hτ3, vars_setArr, hτ2, vars_setArr]
      exact h1v
    have h5o : τ5.arrs o' = (σ.arrs o').set v (fratOff n R v) := by
      rw [hτ5, arrs_setVar, hτ4, arrs_setVar, hτ3, arrs_setArr, if_neg hod, hτ2,
        arrs_setArr, if_pos rfl, ha1]
    have h5d : τ5.arrs dg = (σ.arrs dg).set v (fratOff n R v) := by
      rw [hτ5, arrs_setVar, hτ4, arrs_setVar, hτ3, arrs_setArr, if_pos rfl, hτ2,
        arrs_setArr, if_neg (Ne.symm hod), ha1]
    have h5v : τ5.vars "fr.v" = v + 1 := by rw [hτ5, vars_setVar, if_pos rfl]
    have h5s : τ5.vars "fr.s" = fratOff n R (v + 1) := by
      rw [hτ5, vars_setVar, if_neg (by decide), hτ4, vars_setVar, if_pos rfl]
    have h5nN : τ5.vars nN = n := by
      rw [hτ5, vars_setVar, if_neg hNv, hτ4, vars_setVar, if_neg hNs, hτ3, vars_setArr,
        hτ2, vars_setArr, hτ1, vars_setVar, if_neg hNd]
      exact hnn
    refine ⟨τ5, 17, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), ?_,
      by rw [h5v, hv], le_rfl⟩
    refine ⟨h5nN, by rw [h5v]; omega, by rw [h5v, h5s], ?_, ?_, ?_, ?_, ?_⟩
    · rw [h5o, List.length_set]; exact hoL
    · rw [h5d, List.length_set]; exact hdL
    · intro i hi
      rw [h5v] at hi
      rcases eq_or_ne i v with rfl | hiv
      · rw [h5o, getD_set_self hvoL]
      · rw [h5o, getD_set_of_ne (Ne.symm hiv)]; exact ho i (by omega)
    · intro x hx'
      rw [h5v] at hx'
      rcases eq_or_ne x v with rfl | hxv
      · rw [h5d, getD_set_self hvdL]
      · rw [h5d, getD_set_of_ne (Ne.symm hxv)]; exact hd x (by omega)
    · intro x hx1 hx2
      rw [h5v] at hx1
      rw [h5d, getD_set_of_ne (by omega)]
      exact hdeg x (by omega) hx2
  -- the scan, then the two closing commands
  have hscan : Spec B (fun σ => OffInv nN o' dg n R σ ∧ σ.vars "fr.v" = 0)
      (Csr.scan "fr.v" nN
        (.seq (.assign "fr.d" (.get dg (.var "fr.v")))
          (.seq (.store o' (.var "fr.v") (.var "fr.s"))
            (.seq (.store dg (.var "fr.v") (.var "fr.s"))
              (.seq (.assign "fr.s" (.add (.var "fr.s") (.var "fr.d")))
                (.assign "fr.v" (.add (.var "fr.v") (.lit 1))))))))
      (fun _ σ' => OffInv nN o' dg n R σ' ∧ σ'.vars "fr.v" = n) (21 * n + 4) :=
    Csr.rowScan_spec B _ n 17 "fr.v" nN _ (fun σ => OffInv nN o' dg n R σ) hnB
      (fun _ hI => ⟨hI.1, hI.2.1⟩) (fun _ hI hlt => hbody _ hI hlt)
      (fun _ h => h.1) (fun _ h => by rw [h.2]; omega)
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hnn, hoL, hdL, hdeg⟩ := hσ
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setVar "fr.v" 0 := ⟨_, rfl⟩
  have r1 : Run B (.assign "fr.v" (.lit 0)) σ τ1 2 := by
    rw [hτ1]; exact run_assign' (evalB_lit h0B) (by simp)
  obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "fr.s" 0 := ⟨_, rfl⟩
  have r2 : Run B (.assign "fr.s" (.lit 0)) τ1 τ2 2 := by
    rw [hτ2]; exact run_assign' (evalB_lit h0B) (by simp)
  have ha2 : τ2.arrs = σ.arrs := by rw [hτ2, hτ1]; simp
  have h2v : τ2.vars "fr.v" = 0 := by
    rw [hτ2, vars_setVar, if_neg (by decide), hτ1, vars_setVar, if_pos rfl]
  have h2s : τ2.vars "fr.s" = 0 := by rw [hτ2, vars_setVar, if_pos rfl]
  have h2nN : τ2.vars nN = n := by
    rw [hτ2, vars_setVar, if_neg hNs, hτ1, vars_setVar, if_neg hNv]; exact hnn
  have hI2 : OffInv nN o' dg n R τ2 := by
    refine ⟨h2nN, by rw [h2v]; omega, by rw [h2v, h2s, fratOff_zero], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha2]; exact hoL
    · rw [ha2]; exact hdL
    · intro i hi; rw [h2v] at hi; omega
    · intro x hx'; rw [h2v] at hx'; omega
    · intro x _ hx2; rw [ha2]; exact hdeg x hx2
  obtain ⟨τ3, hrun3, hI3, hv3⟩ := hscan.run ⟨hI2, h2v⟩
  obtain ⟨h3nN, -, h3s, h3oL, h3dL, h3o, h3d, -⟩ := hI3
  rw [hv3] at h3s h3o h3d
  have hnsB' : fratNs n R < B := hfB
  have h3sv : τ3.vars "fr.s" = fratNs n R := by rw [h3s]; rfl
  obtain ⟨τ4, hτ4⟩ : ∃ τ, τ = τ3.setArr o' n (fratNs n R) := ⟨_, rfl⟩
  have r4 : Run B (.store o' (.var nN) (.var "fr.s")) τ3 τ4 3 := by
    rw [hτ4]
    exact run_store' (evB_var h3nN hnB) (evB_var h3sv hnsB') (by omega) (by simp)
  obtain ⟨τ5, hτ5⟩ : ∃ τ, τ = τ4.setVar nF (fratNs n R) := ⟨_, rfl⟩
  have r5 : Run B (.assign nF (.var "fr.s")) τ4 τ5 2 := by
    rw [hτ5]
    exact run_assign' (evB_var (by rw [hτ4, vars_setArr]; exact h3sv) hnsB') (by simp)
  have h5o : τ5.arrs o' = (τ3.arrs o').set n (fratNs n R) := by
    rw [hτ5, arrs_setVar, hτ4, arrs_setArr, if_pos rfl]
  have h5d : τ5.arrs dg = τ3.arrs dg := by
    rw [hτ5, arrs_setVar, hτ4, arrs_setArr, if_neg (Ne.symm hod)]
  have h5nF : τ5.vars nF = fratNs n R := by rw [hτ5, vars_setVar, if_pos rfl]
  have h5nN : τ5.vars nN = n := by
    rw [hτ5, vars_setVar, if_neg hFN.symm, hτ4, vars_setArr]; exact h3nN
  refine ⟨τ5, 21 * n + 13, (r1.seq (r2.seq (hrun3.seq (r4.seq r5)))).mono (by omega),
    le_rfl, h5nN, h5nF, ?_, ?_, ?_, ?_⟩
  · rw [h5o, List.length_set]; exact h3oL
  · rw [h5d]; exact h3dL
  · intro i hi
    rcases eq_or_ne i n with rfl | hin
    · rw [h5o, getD_set_self (by omega)]; rfl
    · rw [h5o, getD_set_of_ne (Ne.symm hin)]; exact h3o i (by omega)
  · intro x hx'
    rw [h5d]; exact h3d x hx'

/-! ## §10 The pass -/

/-- **Every output slot has an owner**: the offsets partition
`[0, fratNs n R)` into the rows. -/
theorem fratOff_owner {n : ℕ} (R : ℕ → List ℕ) :
    ∀ m, m ≤ n → ∀ q, q < fratOff n R m →
      ∃ v, v < m ∧ fratOff n R v ≤ q ∧ q < fratOff n R (v + 1) := by
  intro m
  induction m with
  | zero => intro _ q hq; rw [fratOff_zero] at hq; omega
  | succ m ih =>
      intro hm q hq
      rcases Nat.lt_or_ge q (fratOff n R m) with h | h
      · obtain ⟨v, hv1, hv2, hv3⟩ := ih (by omega) q h
        exact ⟨v, by omega, hv2, hv3⟩
      · exact ⟨m, by omega, h, hq⟩

/-- Reading the output target array at row `v`'s slot `s` reads row
`v` — `SolveAugFrat.flatPref_getD` at the pass's own names. -/
theorem fratPref_getD {n : ℕ} (R : ℕ → List ℕ) {v s : ℕ} (hv : v < n)
    (hs : s < (fratOutRow n R v).length) :
    (fratPref n R n).getD (fratOff n R v + s) 0 = (fratOutRow n R v).getD s 0 :=
  flatPref_getD (fratOutRow n R) hv hs

private theorem take_ext {l m : List ℕ} {k : ℕ} (hk : k ≤ l.length) (hm : m.length = k)
    (h : ∀ i, i < k → l.getD i 0 = m.getD i 0) : l.take k = m := by
  refine List.ext_getElem (by rw [List.length_take, hm]; omega) (fun i h1 h2 => ?_)
  rw [List.length_take] at h1
  have hi := h i (by omega)
  rw [getD_eq_getElem (by omega), getD_eq_getElem (by omega)] at hi
  simpa using hi

/-- **The pass, with everything it leaves.**

From an in-neighbour CSR of `D` in `(o, t)` with the carrier size in
`nN`, a zeroed `n·n`-cell mark region in `mk` and an `n`-cell degree
region in `dg`, `fratCom` leaves the input CSR untouched, an exact
windowed CSR of `fratGraph D` in `(o', t')` with its slot count in
`nF`, **and the mark region clear again**, at
`240·n + 120·ns + 200·fratPairCount D + 60`.

Every clause about the *data* is `SolveAugFrat.csrPrefix_fratPref`, and
the two counts the budget multiplies are its `InNCsr.ns_eq` and
`length_fratCands_eq`.

`FratCsrAt`'s `σ.vars nS = ns` clause is **not** among the hypotheses:
the program never reads the input slot count (Finding 1), so this is
the residual's precondition with that clause deleted. -/
theorem fratCom_spec {B : ℕ} {nN nF o t o' t' dg mk : String}
    (hnm : FrNames o t o' t' dg mk) (hnN : nN ∉ frScalars) (hnF : nF ∉ frScalars)
    (hFN : nF ≠ nN) {n : ℕ} (D : Orientation n) (ns : ℕ) :
    Spec B
      (fun σ => InNCsr o t D ns σ ∧ σ.vars nN = n ∧
        n * n < B ∧ fratPairCount D < B ∧
        n + 1 ≤ (σ.arrs o').length ∧ fratPairCount D ≤ (σ.arrs t').length ∧
        n ≤ (σ.arrs dg).length ∧ n * n ≤ (σ.arrs mk).length ∧
        (∀ i, (σ.arrs mk).getD i 0 = 0))
      (fratCom nN nF o t o' t' dg mk)
      (fun _ σ' => InNCsr o t D ns σ' ∧
        ∃ ns' : ℕ, CsrPrefix o' t' (fratGraph D) ns' σ' ∧
          σ'.vars nF = ns' ∧ ns' ≤ fratPairCount D ∧
          ∀ x, x < n → ∀ y, y < n → (σ'.arrs mk).getD (x * n + y) 0 = 0)
      (fratKStd n ns (fratPairCount D)) := by
  classical
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hin, hcarr, hsqB, hfB, ho'L, ht'L, hdgL, hmkL, hmk0⟩ := hσ
  have hnseq : ns = arcCount D := hin.ns_eq
  obtain ⟨off, tgt, hc, h0, hnd, hRiff⟩ := hin
  have hlen : ∀ w : Fin n, (Csr.row off tgt (w : ℕ)).length = (D.inN w).card :=
    fun w => length_eq_card_of_rows hnd hRiff w
  have hFeq : (fratCands n (Csr.row off tgt)).length = fratPairCount D :=
    length_fratCands_eq hlen
  have hNsle : fratNs n (Csr.row off tgt) ≤ fratPairCount D := fratNs_le hlen
  have hnB : n < B := lt_of_sq_lt hsqB
  have hnsB : ns < B := by have := arcCount_le_fratPairCount D; omega
  have hfnsB : fratNs n (Csr.row off tgt) < B := by omega
  -- sweep 1: zero the degrees
  obtain ⟨τ1, hrun1, h1nN, h1dL, h1z⟩ := (frZero_spec hnN hnB).run ⟨hcarr, hdgL⟩
  have hf1a : ∀ z : String, z ≠ dg → τ1.arrs z = σ.arrs z := fun z hz =>
    hrun1.frame_arr z (by simp [frZeroCom, Csr.scan, Com.warrs, hz])
  -- sweep 2: count
  have hfr1 : FrFrame nN o t n ns off tgt τ1 :=
    { csr := hc.of_eq (hf1a o hnm.o_dg) (hf1a t hnm.t_dg)
      carrier := h1nN }
  have h1mk : τ1.arrs mk = σ.arrs mk := hf1a mk (Ne.symm hnm.dg_mk)
  have hJ1 : FrCount dg mk n [] τ1 :=
    { dgLen := h1dL
      mkLen := by rw [h1mk]; exact hmkL
      entLt := by intro x _ y hy'; simp at hy'
      deg := by intro x hx'; rw [h1z x hx']; simp
      mark := by intro x _ y _; rw [h1mk, hmk0]; simp }
  obtain ⟨τ2, hrun2, hfr2, hJ2⟩ :=
    (frSweep_spec (act := frCountAct dg mk) (Ka := 24) hnN
      (fun L ρ ρ' hh hJ => frCount_arrs dg mk n L ρ ρ' hh hJ)
      (frCount_act (nN := nN) hnm hnN hsqB) hnsB hsqB).run ⟨hfr1, hJ1⟩
  have hf2a : ∀ z : String, z ≠ mk → z ≠ dg → τ2.arrs z = τ1.arrs z := fun z h1 h2 =>
    hrun2.frame_arr z (by
      simp [frSweep, frOuterC, frMidC, frInnerC, frCountAct, Csr.scan, Com.warrs, h1, h2])
  have hf2v : ∀ y : String, y ∉ frScalars → τ2.vars y = τ1.vars y := by
    intro y hy'
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -, -, e11, -⟩ := frScalars_ne hy'
    exact hrun2.frame_var y (by
      simp [frSweep, frOuterC, frMidC, frInnerC, frCountAct, Csr.scan, Com.wvars,
        e1, e2, e3, e4, e5, e6, e7, e8, e11])
  -- sweep 3: the prefix sums
  have h2o' : τ2.arrs o' = σ.arrs o' := by
    rw [hf2a o' hnm.o'_mk hnm.o'_dg, hf1a o' hnm.o'_dg]
  have h2t' : τ2.arrs t' = σ.arrs t' := by
    rw [hf2a t' hnm.t'_mk hnm.t'_dg, hf1a t' hnm.t'_dg]
  obtain ⟨τ3, hrun3, h3nN, h3nF, h3oL, h3dL, h3o, h3d⟩ :=
    (frOff_spec (R := Csr.row off tgt) hnN hnF hFN hnm.o'_dg hnB hfnsB).run
      ⟨hfr2.carrier, by rw [h2o']; exact ho'L, hJ2.dgLen, fun x hx' => hJ2.deg x hx'⟩
  have hf3a : ∀ z : String, z ≠ o' → z ≠ dg → τ3.arrs z = τ2.arrs z := fun z h1 h2 =>
    hrun3.frame_arr z (by simp [frOffCom, Csr.scan, Com.warrs, h1, h2])
  -- sweep 4: emit
  have h3mk : τ3.arrs mk = τ2.arrs mk :=
    hf3a mk (Ne.symm hnm.o'_mk) (Ne.symm hnm.dg_mk)
  have h3t' : τ3.arrs t' = σ.arrs t' := by
    rw [hf3a t' (Ne.symm hnm.o'_t') hnm.t'_dg, h2t']
  have hfr3 : FrFrame nN o t n ns off tgt τ3 :=
    { csr := hfr2.csr.of_eq (hf3a o hnm.o_o' hnm.o_dg) (hf3a t hnm.t_o' hnm.t_dg)
      carrier := h3nN }
  have hJ3 : FrEmit t' dg mk n (Csr.row off tgt) [] τ3 :=
    { dgLen := h3dL
      mkLen := by rw [h3mk]; exact hJ2.mkLen
      tLen := by rw [h3t']; omega
      cur := by intro x hx'; rw [h3d x hx']; simp
      mark := by
        intro x hx' y hy'
        rw [h3mk, hJ2.mark x hx' y hy']
        simp [fratOutRow_eq]
      slots := by intro x _ i hi'; simp at hi' }
  obtain ⟨τ4, hrun4, hfr4, hJ4⟩ :=
    (frSweep_spec (act := frEmitAct t' dg mk) (Ka := 27) hnN
      (fun L ρ ρ' hh hJ => frEmit_arrs t' dg mk n (Csr.row off tgt) L ρ ρ' hh hJ)
      (frEmit_act (nN := nN) hnm hnN hsqB hfnsB) hnsB hsqB).run ⟨hfr3, hJ3⟩
  have hf4a : ∀ z : String, z ≠ mk → z ≠ t' → z ≠ dg → τ4.arrs z = τ3.arrs z :=
    fun z h1 h2 h3 => hrun4.frame_arr z (by
      simp [frSweep, frOuterC, frMidC, frInnerC, frEmitAct, Csr.scan, Com.warrs,
        h1, h2, h3])
  have hf4v : ∀ y : String, y ∉ frScalars → τ4.vars y = τ3.vars y := by
    intro y hy'
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -, -, -, e12⟩ := frScalars_ne hy'
    exact hrun4.frame_var y (by
      simp [frSweep, frOuterC, frMidC, frInnerC, frEmitAct, Csr.scan, Com.wvars,
        e1, e2, e3, e4, e5, e6, e7, e8, e12])
  have h4o' : τ4.arrs o' = τ3.arrs o' := hf4a o' hnm.o'_mk hnm.o'_t' hnm.o'_dg
  have h4nF : τ4.vars nF = fratNs n (Csr.row off tgt) := by rw [hf4v nF hnF]; exact h3nF
  -- the two array prefixes the consumer reads
  have hoTake : (τ4.arrs o').take (n + 1)
      = arrOf (n + 1) (fratOff n (Csr.row off tgt)) := by
    refine take_ext (by rw [h4o']; exact h3oL) (by simp) (fun i hi => ?_)
    rw [h4o', h3o i (by omega), getD_arrOf _ hi]
  have htTake : (τ4.arrs t').take (fratNs n (Csr.row off tgt))
      = fratPref n (Csr.row off tgt) n := by
    refine take_ext hJ4.tLen rfl (fun q hq => ?_)
    obtain ⟨v, hv1, hv2, hv3⟩ := fratOff_owner (Csr.row off tgt) n le_rfl q hq
    rw [fratOff_succ] at hv3
    have hi : q - fratOff n (Csr.row off tgt) v
        < (fratOutRow n (Csr.row off tgt) v).length := by omega
    rw [show q = fratOff n (Csr.row off tgt) v + (q - fratOff n (Csr.row off tgt) v) by omega,
      hJ4.slots v hv1 _ hi, fratPref_getD (Csr.row off tgt) hv1 hi]
    rfl
  refine ⟨τ4, (11 * n + 6) + ((22 * n + 21 * ns
      + (24 + 11) * (fratCands n (Csr.row off tgt)).length + 6)
    + ((21 * n + 13) + (22 * n + 21 * ns
      + (27 + 11) * (fratCands n (Csr.row off tgt)).length + 6))),
    hrun1.seq (hrun2.seq (hrun3.seq hrun4)), ?_, ?_, ?_⟩
  · simp only [fratKStd, fratK]; omega
  · exact ⟨off, tgt, hfr4.csr, h0, hnd, hRiff⟩
  · refine ⟨fratNs n (Csr.row off tgt),
      csrPrefix_fratPref hRiff hnm.o'_t' (by rw [h4o']; exact h3oL) hJ4.tLen hoTake htTake,
      h4nF, hNsle, ?_⟩
    intro x hx' y hy'
    rw [hJ4.mark x hx' y hy', if_neg]
    rintro ⟨h1, h2⟩
    exact h2 h1

/-- **`FratCsrAt`, discharged** by `fratCom` at `fratKStd` — the landed
residual verbatim, `fratCom_spec` with the two clauses the contract
does not carry dropped (the unread `nS` cell from the precondition, the
restored mark region from the postcondition). -/
theorem fratCsrAt_fratCom {B : ℕ} {nN nS nF o t o' t' dg mk : String}
    (hnm : FrNames o t o' t' dg mk) (hnN : nN ∉ frScalars) (hnF : nF ∉ frScalars)
    (hFN : nF ≠ nN) :
    FratCsrAt B nN nS nF o t o' t' dg mk (fratCom nN nF o t o' t' dg mk) fratKStd := by
  intro n D ns
  refine ((fratCom_spec hnm hnN hnF hFN D ns).pre ?_).post ?_
  · rintro σ ⟨h1, h2, -, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro σ σ' - ⟨h1, ns', h2, h3, h4, -⟩
    exact ⟨h1, ns', h2, h3, h4⟩

/-- The hypothesis bundle is satisfiable, so nothing above is vacuous:
six distinct region names and two scalar names outside the pass's own
scratch. -/
example : FratCsrAt 64 "fr.nN" "fr.nS" "fr.nF" "in.o" "in.t" "ou.o" "ou.t" "sc.d" "sc.m"
    (fratCom "fr.nN" "fr.nF" "in.o" "in.t" "ou.o" "ou.t" "sc.d" "sc.m") fratKStd :=
  fratCsrAt_fratCom
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide)

/-! ## §11 The axiom surface -/

#print axioms fratCom_spec
#print axioms fratCsrAt_fratCom

end Lax3Proofs.Prog
