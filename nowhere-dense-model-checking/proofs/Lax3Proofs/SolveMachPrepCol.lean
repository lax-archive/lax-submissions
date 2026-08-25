import Lax3Proofs.SolveMachPrepBatch

/-!
# F6c12-1c — the colour-region writer, the last program of the pass

`profilesCom_specW` (`SolveFrameStages` §5) leaves the profile tables in
**separate arrays** — `mb` batch arrays `pdF j` and `Λc` class arrays
`puF c` — and returns the arena it was handed, at the *parent's*
palette. Nothing landed assembles

```
machChild.col = Impl.recordProfilesMS S.R (childColR S A π u) Dp Dc
```

over the `isoPal (relPal Λ) S.width S.R` layout. This file writes that
program and specifies it.

## Why the emitter is family-unrolled

**IMP+ has no array indirection** (`Imp.lean`: `Expr.get` names its
array statically). A loop over the `mb + Λc` table arrays is therefore
not expressible, and the emitter must be a `Nat`-recursive `.seq` of
static copies — exactly the shape `profilesCom` itself uses for its own
families (`batchSeq`/`classSeq`, `SolveBlocksProfiles` §6), with the
matching `warrs`/`wvars` inductions (§2 here). Only the **carrier** is
looped over, once: `colWriteCom` is `forZero vv cn` with the unrolled
family sequence as its body, so the machine loops are over the carrier
and the slots only (E10).

## The old colours need no relocation

The obvious reading of the layout says the writer must also *move* the
old colour rows: the input arena's colour region is row-major at stride
`Λc`, the output's at stride `isoPal Λc mb R`, so the `isoOld` slots
look like an in-place re-lay-out — with a genuine read/write aliasing
hazard, since the destination row overlaps later source rows.

It does not. Under the seam `Impl.ProfileTablesMS`, the class table
`Dc c` is a `BallTable` of `vsrc H (f c)` from the virtual source, so
`{z | Dc c z.castSucc ≤ 1}` is the distance-`0` neighbourhood of the
class, which is **the class itself** (`oldRow_eq_thr_one`, §4). The
`isoOld c` slot therefore reads off the *same* array `puF c` as the
`isoPu c b` slots, at threshold `b = 0` — the `pu` block emits `R + 2`
cells instead of `R + 1` and the colour region is **write-only** for
this program. That is hazard 5's rule ("check whether the figure is
recoverable from the data") applied to a whole region: no scratch copy,
no descending scan, no aliasing side condition.

## The budget

`colWriteK cN Λc mb R = (mb·(9R+13) + Λc·(9R+23) + 14)·cN + 6`, and
`colWriteK_le_profilesK` / `colWriteK_le_prepStageK` show it is
**absorbed** — no new term in `prepStageK`, and in particular **no
`A.N` term** (§6.1's `Θ(A.N²)` scratch trap), every figure being the
child's:

* each `pd` block's `(9R+13)·cN` rides `profilesK`'s own per-batch-slot
  charge `batchK cN cns R ≥ 13·cN + 15·cN·R`;
* each `pu` block's `(9R+23)·cN` rides one uniform class slot
  `msK cN cns R ≥ 129·cN + (91·cN+31)·(R+1)`;
* the loop's own `14·cN + 6` rides the **spare** class slot —
  `profilesK` is charged at `L := Λc + 1` (the marker's slot) and the
  emitter has only `Λc` `pu` families, the marker's row being one of
  them.

This is `mkBatchK_le_prepStageK`'s precedent at the third of the three
glue programs, and it needs no `1 ≤ cN` side condition.

## Hazards honoured

* **Profiles are measured in `preG`, before isolation.** The `Spec`
  takes the `ProfileTablesMS` witness at whatever graph the caller
  measured in and returns `recordProfilesMS` at the *same* tables;
  `machChild_eq_ofArena` then consumes it at `preG` verbatim. Nothing
  here reads the isolated graph at all.
* **The batch is the padded `batchFn`** — `Dp` is indexed by
  `Fin mb` with `mb = S.width`, one table per padded slot, duplicates
  included; the emitter unrolls over all `mb` of them.
* **`deleteVerts` isolates, it does not remove** — the carrier the row
  loop runs over is the child's whole carrier, `cN = childN`.
* **Windowed convention** — the precondition asks
  `cN * isoPal Λc mb R ≤ (σ.arrs ca).length`, never an equality; the
  `ColBits` prefix is a conclusion, not a hypothesis.
* **`ColBits` addresses row-major at `v·Λ' + c`** and a program emits
  numerals, so §3 turns `isoOld`/`isoPd`/`isoPu` into offsets through
  the landed `isoOld_val`/`isoPd_val`/`isoPu_val` and splits the
  palette with `isoPal_cases`.

## What is here, and what is not

§1 the emitter (`thrSeq`, `pdBlock`/`puBlock`, `pdSeq`/`puSeq`,
`colRowCom`, `colWriteCom`) and its budget, with the two absorption
lemmas; §2 the `warrs`/`wvars` inductions, ending at
`wvars_colWriteCom` (three scratch scalars) and `warrs_colWriteCom`
(one array, the colour region); §3 the palette as offsets
(`isoPal_offset_cases` and the three fit lemmas); §4
`oldRow_eq_thr_one`; §5 `thrSeq_spec`, the one genuinely new phase;
§6 `pdSeq_spec` and `puSeq_spec`, the family inductions (the blocks are
inlined into their steps); §7 `colWriteCom_spec`, the writer at the
offsets it emits; §8 `colWriteCom_rows`, the same at the palette's
slots — `ColBits`'s own clause at `Impl.recordProfilesMS R f Dp Dc` —
and `colWriteCom_machChild`, its instance at `machChild.col`.

**Not here**: the lift of §8 through `ArenaStW` at the two palettes
(the input arena is at `Λc`, the output at `isoPal Λc mb R`, so the
`col` window moves while the other four stay), and the composition of
the pass. Both are the discharger's, and neither is blocked: §8 already
delivers every cell of the colour region and preserves every other
array — the profile tables included — verbatim, with no reallocation.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3.ColoredGraphs
open Lax3Proofs.Driver

/-! ## §1 The emitter, and its budget

Three levels of unrolling, all over compile-time data: the thresholds
of one family member (`thrSeq`), the members of a family (`pdSeq`,
`puSeq`), and — the only loop — the carrier (`colWriteCom`). -/

/-- **The threshold run**: `k` consecutive colour cells from
`bs + off`, cell `i` holding the bit of `dd < i + sh`. Both profile
families are cumulative, so a whole slot family of one table entry is
this one run: `sh = 1` reads `Dp j v ≤ i`, `sh = 2` reads
`Dc c v ≤ i + 1` (the virtual source's shift). -/
def thrSeq (ca bs dd : String) (off sh : ℕ) : ℕ → Com
  | 0 => .skip
  | i + 1 => .seq (thrSeq ca bs dd off sh i)
      (.ite (.lt (.var dd) (.lit (i + sh)))
        (.store ca (.add (.var bs) (.lit (off + i))) (.lit 1))
        (.store ca (.add (.var bs) (.lit (off + i))) (.lit 0)))

/-- **One batch block**: read the `j`-th batch table at the current row
and emit its `R + 1` cumulative slots, at the `pd` family's offset. -/
def pdBlock (ca pd bs dd vv : String) (Λc R j : ℕ) : Com :=
  .seq (.assign dd (.get pd (.var vv)))
    (thrSeq ca bs dd (Λc + (R + 1) * j) 1 (R + 1))

/-- **One class block**: read the `c`-th class table at the current row
and emit `R + 2` cells from it — the `isoOld c` slot (threshold `0`,
which is the class itself) and the `R + 1` cumulative `isoPu c b`
slots. One array read, two slot families. -/
def puBlock (ca pu bs dd vv : String) (Λc mb R c : ℕ) : Com :=
  .seq (.assign dd (.get pu (.var vv)))
    (.seq (thrSeq ca bs dd c 2 1)
      (thrSeq ca bs dd (Λc + mb * (R + 1) + (R + 1) * c) 2 (R + 1)))

/-- The batch half, family-unrolled: one static `pdBlock` per padded
batch slot (`batchSeq`'s shape — a duplicate costs another block). -/
def pdSeq (ca : String) (pdF : ℕ → String) (bs dd vv : String)
    (Λc R : ℕ) : ℕ → Com
  | 0 => .skip
  | j + 1 => .seq (pdSeq ca pdF bs dd vv Λc R j)
      (pdBlock ca (pdF j) bs dd vv Λc R j)

/-- The class half, family-unrolled: one static `puBlock` per class
(`classSeq`'s shape). The marker class is one of them, and costs no
more than any other. -/
def puSeq (ca : String) (puF : ℕ → String) (bs dd vv : String)
    (Λc mb R : ℕ) : ℕ → Com
  | 0 => .skip
  | c + 1 => .seq (puSeq ca puF bs dd vv Λc mb R c)
      (puBlock ca (puF c) bs dd vv Λc mb R c)

/-- **One row**: the row's base index into the colour region, then both
family halves. Every cell of the row is written exactly once. -/
def colRowCom (ca : String) (pdF puF : ℕ → String) (bs dd vv : String)
    (Λc mb R : ℕ) : Com :=
  .seq (.assign bs (.mul (.var vv) (.lit (Driver.isoPal Λc mb R))))
    (.seq (pdSeq ca pdF bs dd vv Λc R mb) (puSeq ca puF bs dd vv Λc mb R Λc))

/-- **The colour-region writer**: one pass over the child's carrier,
each turn emitting a whole `isoPal` row off the `mb + Λc` table
arrays. -/
def colWriteCom (ca cn : String) (pdF puF : ℕ → String)
    (bs dd vv : String) (Λc mb R : ℕ) : Com :=
  forZero vv cn
    (.seq (colRowCom ca pdF puF bs dd vv Λc mb R)
      (.assign vv (.add (.var vv) (.lit 1))))

/-- **The writer's budget**: per carrier cell, one base multiply and one
increment (`4 + 4`), the two family sequences' own `skip`s (`1 + 1`),
`mb` batch blocks (`3` to read the table, `1 + 9·(R+1)` to emit) and
`Λc` class blocks (`3`, then `1 + 9` for the old slot and
`1 + 9·(R+1)` for the profile slots). -/
def colWriteK (cN Λc mb R : ℕ) : ℕ :=
  (mb * (9 * R + 13) + Λc * (9 * R + 23) + 14) * cN + 6

/-- **The writer's budget is absorbed.** `profilesK` already charges
`batchK` per padded batch slot and `msK` per class slot at
`L := Λc + 1`; the emitter has `mb` batch blocks, `Λc` class blocks and
a carrier loop, so the batch blocks ride the batch charge, the class
blocks ride `Λc` of the class charges, and the loop rides the **spare**
one. No new term, and no `A.N` term: every figure is the child's. -/
theorem colWriteK_le_profilesK (cN cns Λc mb R : ℕ) :
    colWriteK cN Λc mb R ≤ profilesK mb (Λc + 1) cN cns R := by
  have h1 : (9 * R + 13) * cN ≤ batchK cN cns R := by
    unfold batchK bfsK
    nlinarith [Nat.zero_le R, Nat.zero_le cN, Nat.zero_le cns]
  have h2 : (9 * R + 23) * cN ≤ msK cN cns R := by
    unfold msK classBitsK vsrcK bfsK
    nlinarith [Nat.zero_le R, Nat.zero_le cN, Nat.zero_le cns]
  have h3 : 14 * cN + 6 ≤ msK cN cns R := by
    unfold msK classBitsK vsrcK bfsK
    nlinarith [Nat.zero_le R, Nat.zero_le cN, Nat.zero_le cns]
  have hsplit : colWriteK cN Λc mb R
      = mb * ((9 * R + 13) * cN) + Λc * ((9 * R + 23) * cN) + (14 * cN + 6) := by
    unfold colWriteK; ring
  calc colWriteK cN Λc mb R
      = mb * ((9 * R + 13) * cN) + Λc * ((9 * R + 23) * cN)
          + (14 * cN + 6) := hsplit
    _ ≤ mb * batchK cN cns R + Λc * msK cN cns R + msK cN cns R :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h1)
          (Nat.mul_le_mul_left _ h2)) h3
    _ = profilesK mb (Λc + 1) cN cns R := by unfold profilesK; ring

/-- **The comparison the pass consumes** — `mkBatchK_le_prepStageK`'s
statement at the third glue program, and without its `1 ≤ cN` side
condition. -/
theorem colWriteK_le_prepStageK (cN cns dS k Λc ℓp hb mb R : ℕ) :
    colWriteK cN Λc mb R ≤ prepStageK cN cns dS k Λc ℓp hb mb R := by
  have h := colWriteK_le_profilesK cN cns Λc mb R
  unfold prepStageK
  omega

/-! ## §2 The frame surface, by the families' own induction

The unrolled sequences need the same `warrs`/`wvars` inductions
`batchSeq`/`classSeq` needed: the writer touches exactly one array —
the colour region — and exactly three scalars. -/

@[simp] theorem wvars_thrSeq (ca bs dd : String) (off sh k : ℕ) :
    (thrSeq ca bs dd off sh k).wvars = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (thrSeq ca bs dd off sh k).wvars ++ ([] ++ []) = []
    rw [ih]; rfl

theorem warrs_thrSeq (ca bs dd : String) (off sh k : ℕ) :
    ∀ a ∈ (thrSeq ca bs dd off sh k).warrs, a = ca := by
  induction k with
  | zero => intro a ha; simp [thrSeq] at ha
  | succ k ih =>
    intro a ha
    have he : (thrSeq ca bs dd off sh (k + 1)).warrs
        = (thrSeq ca bs dd off sh k).warrs ++ ([ca] ++ [ca]) := rfl
    rw [he] at ha
    rcases List.mem_append.mp ha with h | h
    · exact ih a h
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with rfl | rfl <;> rfl

theorem wvars_pdBlock (ca pd bs dd vv : String) (Λc R j : ℕ) :
    (pdBlock ca pd bs dd vv Λc R j).wvars = [dd] := by
  show [dd] ++ (thrSeq ca bs dd (Λc + (R + 1) * j) 1 (R + 1)).wvars = [dd]
  rw [wvars_thrSeq]; rfl

theorem warrs_pdBlock (ca pd bs dd vv : String) (Λc R j : ℕ) :
    ∀ a ∈ (pdBlock ca pd bs dd vv Λc R j).warrs, a = ca := by
  intro a ha
  have he : (pdBlock ca pd bs dd vv Λc R j).warrs
      = [] ++ (thrSeq ca bs dd (Λc + (R + 1) * j) 1 (R + 1)).warrs := rfl
  rw [he, List.nil_append] at ha
  exact warrs_thrSeq _ _ _ _ _ _ a ha

theorem wvars_puBlock (ca pu bs dd vv : String) (Λc mb R c : ℕ) :
    (puBlock ca pu bs dd vv Λc mb R c).wvars = [dd] := by
  show [dd] ++ ((thrSeq ca bs dd c 2 1).wvars
    ++ (thrSeq ca bs dd (Λc + mb * (R + 1) + (R + 1) * c) 2 (R + 1)).wvars) = [dd]
  rw [wvars_thrSeq, wvars_thrSeq]; rfl

theorem warrs_puBlock (ca pu bs dd vv : String) (Λc mb R c : ℕ) :
    ∀ a ∈ (puBlock ca pu bs dd vv Λc mb R c).warrs, a = ca := by
  intro a ha
  have he : (puBlock ca pu bs dd vv Λc mb R c).warrs
      = [] ++ ((thrSeq ca bs dd c 2 1).warrs
        ++ (thrSeq ca bs dd (Λc + mb * (R + 1) + (R + 1) * c) 2 (R + 1)).warrs) := rfl
  rw [he, List.nil_append] at ha
  rcases List.mem_append.mp ha with h | h
  · exact warrs_thrSeq _ _ _ _ _ _ a h
  · exact warrs_thrSeq _ _ _ _ _ _ a h

theorem wvars_pdSeq (ca : String) (pdF : ℕ → String) (bs dd vv : String)
    (Λc R k : ℕ) : ∀ y ∈ (pdSeq ca pdF bs dd vv Λc R k).wvars, y = dd := by
  induction k with
  | zero => intro y hy; simp [pdSeq] at hy
  | succ k ih =>
    intro y hy
    have he : (pdSeq ca pdF bs dd vv Λc R (k + 1)).wvars
        = (pdSeq ca pdF bs dd vv Λc R k).wvars
          ++ (pdBlock ca (pdF k) bs dd vv Λc R k).wvars := rfl
    rw [he] at hy
    rcases List.mem_append.mp hy with h | h
    · exact ih y h
    · rw [wvars_pdBlock] at h
      simpa using h

theorem warrs_pdSeq (ca : String) (pdF : ℕ → String) (bs dd vv : String)
    (Λc R k : ℕ) : ∀ a ∈ (pdSeq ca pdF bs dd vv Λc R k).warrs, a = ca := by
  induction k with
  | zero => intro a ha; simp [pdSeq] at ha
  | succ k ih =>
    intro a ha
    have he : (pdSeq ca pdF bs dd vv Λc R (k + 1)).warrs
        = (pdSeq ca pdF bs dd vv Λc R k).warrs
          ++ (pdBlock ca (pdF k) bs dd vv Λc R k).warrs := rfl
    rw [he] at ha
    rcases List.mem_append.mp ha with h | h
    · exact ih a h
    · exact warrs_pdBlock _ _ _ _ _ _ _ _ a h

theorem wvars_puSeq (ca : String) (puF : ℕ → String) (bs dd vv : String)
    (Λc mb R k : ℕ) : ∀ y ∈ (puSeq ca puF bs dd vv Λc mb R k).wvars, y = dd := by
  induction k with
  | zero => intro y hy; simp [puSeq] at hy
  | succ k ih =>
    intro y hy
    have he : (puSeq ca puF bs dd vv Λc mb R (k + 1)).wvars
        = (puSeq ca puF bs dd vv Λc mb R k).wvars
          ++ (puBlock ca (puF k) bs dd vv Λc mb R k).wvars := rfl
    rw [he] at hy
    rcases List.mem_append.mp hy with h | h
    · exact ih y h
    · rw [wvars_puBlock] at h
      simpa using h

theorem warrs_puSeq (ca : String) (puF : ℕ → String) (bs dd vv : String)
    (Λc mb R k : ℕ) : ∀ a ∈ (puSeq ca puF bs dd vv Λc mb R k).warrs, a = ca := by
  induction k with
  | zero => intro a ha; simp [puSeq] at ha
  | succ k ih =>
    intro a ha
    have he : (puSeq ca puF bs dd vv Λc mb R (k + 1)).warrs
        = (puSeq ca puF bs dd vv Λc mb R k).warrs
          ++ (puBlock ca (puF k) bs dd vv Λc mb R k).warrs := rfl
    rw [he] at ha
    rcases List.mem_append.mp ha with h | h
    · exact ih a h
    · exact warrs_puBlock _ _ _ _ _ _ _ _ _ a h

/-- **The writer's scalar surface**: three scratch names, none of them
an arena cell. -/
theorem wvars_colWriteCom (ca cn : String) (pdF puF : ℕ → String)
    (bs dd vv : String) (Λc mb R : ℕ) :
    ∀ y ∈ (colWriteCom ca cn pdF puF bs dd vv Λc mb R).wvars,
      y = vv ∨ y = bs ∨ y = dd := by
  intro y hy
  have he : (colWriteCom ca cn pdF puF bs dd vv Λc mb R).wvars
      = [vv] ++ (([bs] ++ ((pdSeq ca pdF bs dd vv Λc R mb).wvars
        ++ (puSeq ca puF bs dd vv Λc mb R Λc).wvars)) ++ [vv]) := rfl
  rw [he] at hy
  rcases List.mem_append.mp hy with h | h
  · exact Or.inl (by simpa using h)
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inr (Or.inl (by simpa using h))
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (Or.inr (wvars_pdSeq _ _ _ _ _ _ _ _ y h))
      · exact Or.inr (Or.inr (wvars_puSeq _ _ _ _ _ _ _ _ _ y h))
  · exact Or.inl (by simpa using h)

/-- **The writer's array surface**: the colour region, and nothing
else. -/
theorem warrs_colWriteCom (ca cn : String) (pdF puF : ℕ → String)
    (bs dd vv : String) (Λc mb R : ℕ) :
    ∀ a ∈ (colWriteCom ca cn pdF puF bs dd vv Λc mb R).warrs, a = ca := by
  intro a ha
  have he : (colWriteCom ca cn pdF puF bs dd vv Λc mb R).warrs
      = [] ++ (([] ++ ((pdSeq ca pdF bs dd vv Λc R mb).warrs
        ++ (puSeq ca puF bs dd vv Λc mb R Λc).warrs)) ++ []) := rfl
  rw [he, List.nil_append, List.nil_append, List.append_nil] at ha
  rcases List.mem_append.mp ha with h | h
  · exact warrs_pdSeq _ _ _ _ _ _ _ _ a h
  · exact warrs_puSeq _ _ _ _ _ _ _ _ _ a h

/-! ## §3 The palette as offsets

`ColBits` addresses the colour region row-major at `v·Λ' + c` and a
program emits numerals, so the writer needs the palette's three
families **as offsets**, and needs to know that an arbitrary slot is
one of them. `SolveMachPrepBatch` §7 supplies the numerals; this is the
partition in the form the emitter's payload matches, with the offsets
in the emitter's own association (`(R+1)·j + a`, not `a + (R+1)·j`). -/

section Offsets

variable {Λc mb R : ℕ}

/-- Every slot of the isolation palette is exactly one of the three
families, and its numeral is the family's offset. -/
theorem isoPal_offset_cases (c' : Fin (Driver.isoPal Λc mb R)) :
    (∃ c : Fin Λc, c' = Driver.isoOld c ∧ (c' : ℕ) = (c : ℕ)) ∨
      (∃ (j : Fin mb) (a : Fin (R + 1)), c' = Driver.isoPd j a ∧
        (c' : ℕ) = Λc + (R + 1) * (j : ℕ) + (a : ℕ)) ∨
      ∃ (c : Fin Λc) (b : Fin (R + 1)), c' = Driver.isoPu c b ∧
        (c' : ℕ) = Λc + mb * (R + 1) + (R + 1) * (c : ℕ) + (b : ℕ) := by
  rcases isoPal_cases c' with ⟨c, rfl⟩ | ⟨j, a, rfl⟩ | ⟨c, b, rfl⟩
  · exact Or.inl ⟨c, rfl, isoOld_val c⟩
  · refine Or.inr (Or.inl ⟨j, a, rfl, ?_⟩)
    rw [isoPd_val]; ring
  · refine Or.inr (Or.inr ⟨c, b, rfl, ?_⟩)
    rw [isoPu_val]; ring

/-- The `pd` family's offsets fit the row, at raw naturals — the bound
each of the emitter's stores rides. -/
theorem pd_offset_lt (j a : ℕ) (hj : j < mb) (ha : a < R + 1) :
    Λc + (R + 1) * j + a < Driver.isoPal Λc mb R := by
  have h : ((Driver.isoPd (Λ := Λc) ⟨j, hj⟩ ⟨a, ha⟩ :
      Fin (Driver.isoPal Λc mb R)) : ℕ) < Driver.isoPal Λc mb R :=
    (Driver.isoPd (Λ := Λc) ⟨j, hj⟩ ⟨a, ha⟩).isLt
  rw [isoPd_val] at h
  calc Λc + (R + 1) * j + a = Λc + (a + (R + 1) * j) := by ring
    _ < Driver.isoPal Λc mb R := h

/-- The `pu` family's offsets fit the row. -/
theorem pu_offset_lt (c b : ℕ) (hc : c < Λc) (hb : b < R + 1) :
    Λc + mb * (R + 1) + (R + 1) * c + b < Driver.isoPal Λc mb R := by
  have h : ((Driver.isoPu (mb := mb) ⟨c, hc⟩ ⟨b, hb⟩ :
      Fin (Driver.isoPal Λc mb R)) : ℕ) < Driver.isoPal Λc mb R :=
    (Driver.isoPu (mb := mb) (cap := R) ⟨c, hc⟩ ⟨b, hb⟩).isLt
  rw [isoPu_val] at h
  calc Λc + mb * (R + 1) + (R + 1) * c + b
      = Λc + (mb * (R + 1) + (b + (R + 1) * c)) := by ring
    _ < Driver.isoPal Λc mb R := h

/-- The old family's offsets fit the row. -/
theorem old_offset_lt (c : ℕ) (hc : c < Λc) : c < Driver.isoPal Λc mb R := by
  have h : ((Driver.isoOld (mb := mb) (cap := R) ⟨c, hc⟩ :
      Fin (Driver.isoPal Λc mb R)) : ℕ) < Driver.isoPal Λc mb R :=
    (Driver.isoOld (mb := mb) (cap := R) ⟨c, hc⟩).isLt
  rwa [isoOld_val] at h

end Offsets

/-! ## §4 The old colours are recoverable from the class tables

The finding that makes this program write-only on the colour region.
Under `ProfileTablesMS` the class table `Dc c` is a `BallTable` of the
virtual-source graph, so its threshold at `1` is the distance-`0`
neighbourhood of the class — the class itself. The `isoOld c` slot and
the `isoPu c 0` slot hold the *same* set, and both are read off the
array `puF c`. Nothing has to relocate the parent's colour rows. -/

/-- **The old row is the class table at threshold one.** -/
theorem oldRow_eq_thr_one {n Λ mb R : ℕ} {H : SimpleGraph (Fin n)}
    {w : Fin mb → Fin n} {f : Fin Λ → Set (Fin n)}
    {Dp : Fin mb → Fin n → ℕ} {Dc : Fin Λ → Fin (n + 1) → ℕ}
    (h : Impl.ProfileTablesMS H w f R Dp Dc) (c : Fin Λ) :
    f c = {z | Dc c z.castSucc ≤ 1} := by
  have hct := Impl.colorTable_of_ballTable (h.2 c) (b := 0) (Nat.zero_le R)
  rw [← hct]
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · exact fun hz => ⟨z, hz, WalkDistance.withinDist_refl H 0 z⟩
  · rintro ⟨y, hy, hw, hlen⟩
    rwa [SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hlen)]

/-! ## §5 The threshold run, specified

The one genuinely new phase: `k` cells written from one scalar, with a
frame clause naming the interval they occupy. Everything above is this
lemma plus bookkeeping. -/

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

/-- **The threshold run, specified**: the `k` cells `bs + off + i` hold
the bit of `dd < i + sh`, every other cell of the region is left alone,
no other array is touched, and no scalar is. -/
theorem thrSeq_spec {ca bs dd : String} {off sh base d : ℕ} :
    ∀ k : ℕ, 1 < B → base + (off + k) < B → d < B → k + sh < B →
    Spec B
      (fun σ => σ.vars bs = base ∧ σ.vars dd = d ∧
        base + (off + k) ≤ (σ.arrs ca).length)
      (thrSeq ca bs dd off sh k)
      (fun σ σ' =>
        (∀ i, i < k → (σ'.arrs ca).getD (base + (off + i)) 0
            = if d < i + sh then 1 else 0) ∧
        (∀ q, q < base + off ∨ base + (off + k) ≤ q →
            (σ'.arrs ca).getD q 0 = (σ.arrs ca).getD q 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ b, b ≠ ca → σ'.arrs b = σ.arrs b) ∧
        (∀ y, σ'.vars y = σ.vars y))
      (1 + 9 * k) := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ σ _
    refine ⟨σ, Run.skip.mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; omega
    · intro q _; rfl
    · intro b; rfl
    · intro b _; rfl
    · intro y; rfl
  | succ k ih =>
    intro hone hB hdB hshB σ hσ
    obtain ⟨hbs, hdd, hlen⟩ := hσ
    obtain ⟨σ₁, hrun₁, hpay₁, hfr₁, hlen₁, harr₁, hvar₁⟩ :=
      ih hone (by omega) hdB (by omega) σ ⟨hbs, hdd, by omega⟩
    have hbs₁ : σ₁.vars bs = base := by rw [hvar₁]; exact hbs
    have hdd₁ : σ₁.vars dd = d := by rw [hvar₁]; exact hdd
    have hlenca : base + (off + (k + 1)) ≤ (σ₁.arrs ca).length := by
      rw [hlen₁]; exact hlen
    have hidx : base + (off + k) < (σ₁.arrs ca).length := by omega
    -- the store's index, and the two constants
    have hbsB : σ₁.vars bs < B := by rw [hbs₁]; omega
    have hddB : σ₁.vars dd < B := by rw [hdd₁]; omega
    have hi : (Expr.add (.var bs) (.lit (off + k))).evalB B σ₁
        = some (base + (off + k)) := by
      have h1 : (Expr.var bs).evalB B σ₁ = some base := by
        rw [← hbs₁]; exact evalB_var hbsB
      have h2 : (Expr.lit (off + k)).evalB B σ₁ = some (off + k) :=
        evalB_lit (by omega)
      have h3 : Bop.add.apply base (off + k) < B := by
        simp only [Bop.apply_add]; omega
      simpa using evalB_bin h1 h2 h3
    have hddv : (Expr.var dd).evalB B σ₁ = some d := by
      rw [← hdd₁]; exact evalB_var hddB
    -- the cell, whichever branch it takes
    set val : ℕ := if d < k + sh then 1 else 0 with hval_def
    have hvalB : val < B := by rw [hval_def]; split <;> omega
    have hcell : Run B
        (.ite (.lt (.var dd) (.lit (k + sh)))
          (.store ca (.add (.var bs) (.lit (off + k))) (.lit 1))
          (.store ca (.add (.var bs) (.lit (off + k))) (.lit 0)))
        σ₁ (σ₁.setArr ca (base + (off + k)) val) 9 := by
      have hc := evalB_condLt (B := B) (σ := σ₁) hddv
        (evalB_lit (n := k + sh) (by omega))
      by_cases hlt : d < k + sh
      · have hval1 : val = 1 := by rw [hval_def, if_pos hlt]
        rw [hval1]
        exact Run.ite_true (by rw [hc]; simp [hlt])
          (Run.store hi (evalB_lit (by omega)) hidx)
      · have hval0 : val = 0 := by rw [hval_def, if_neg hlt]
        rw [hval0]
        exact Run.ite_false (by rw [hc]; simp [hlt])
          (Run.store hi (evalB_lit (by omega)) hidx)
    refine ⟨σ₁.setArr ca (base + (off + k)) val,
      (hrun₁.seq hcell).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi'
      rw [arrs_setArr, if_pos rfl]
      rcases Nat.lt_or_ge i k with hik | hik
      · rw [getD_set_of_ne (by omega)]
        exact hpay₁ i hik
      · obtain rfl : i = k := by omega
        rw [getD_set_self hidx, hval_def]
    · intro q hq
      rw [arrs_setArr, if_pos rfl, getD_set_of_ne (by omega)]
      exact hfr₁ q (by omega)
    · intro b
      rw [length_arrs_setArr]
      exact hlen₁ b
    · intro b hb
      rw [arrs_setArr, if_neg hb]
      exact harr₁ b hb
    · intro y
      rw [vars_setArr]
      exact hvar₁ y

/-! ## §6 The two families, by induction on their static copies

`batchSeq`/`classSeq`'s own shape: the `k`-th block reads array number
`k` and emits its slots, and the induction carries both the payload of
the blocks already run and the interval they occupy. The frame clauses
are stated at the *family's* region, which is what makes the two halves
compose: `pdSeq` writes only inside `[base+Λc, base+Λc+mb·(R+1))`, and
`puSeq` writes only outside it. -/

/-- The batch half, specified: `k` blocks, `k` tables, the `pd` region
and nothing else. -/
theorem pdSeq_spec {ca : String} {pdF : ℕ → String} {bs dd vv : String}
    {Λc mb R base v : ℕ} {Dp : ℕ → ℕ}
    (hone : 1 < B) (hddbs : dd ≠ bs) (hddvv : dd ≠ vv)
    (hvB : v < B) (hRB : R + 3 < B)
    (hrowB : base + Driver.isoPal Λc mb R < B) :
    ∀ k : ℕ, k ≤ mb →
    Spec B
      (fun σ => σ.vars bs = base ∧ σ.vars vv = v ∧
        (∀ j, j < mb → pdF j ≠ ca ∧ v < (σ.arrs (pdF j)).length ∧
          (σ.arrs (pdF j)).getD v 0 = Dp j ∧ Dp j < B) ∧
        base + Driver.isoPal Λc mb R ≤ (σ.arrs ca).length)
      (pdSeq ca pdF bs dd vv Λc R k)
      (fun σ σ' =>
        (∀ j, j < k → ∀ i, i < R + 1 →
          (σ'.arrs ca).getD (base + (Λc + (R + 1) * j + i)) 0
            = if Dp j ≤ i then 1 else 0) ∧
        (∀ q, q < base + Λc ∨ base + (Λc + mb * (R + 1)) ≤ q →
            (σ'.arrs ca).getD q 0 = (σ.arrs ca).getD q 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ b, b ≠ ca → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ dd → σ'.vars y = σ.vars y))
      (1 + k * (9 * R + 13)) := by
  have hpal : Driver.isoPal Λc mb R = Λc + (mb * (R + 1) + Λc * (R + 1)) := rfl
  intro k
  induction k with
  | zero =>
    intro _ σ _
    refine ⟨σ, Run.skip.mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; omega
    · intro q _; rfl
    · intro b; rfl
    · intro b _; rfl
    · intro y _; rfl
  | succ k ih =>
    intro hk σ hσ
    obtain ⟨hbs, hvv, htab, hlen⟩ := hσ
    obtain ⟨σ₁, hrun₁, hpay₁, hfr₁, hlen₁, harr₁, hvar₁⟩ :=
      ih (by omega) σ ⟨hbs, hvv, htab, hlen⟩
    obtain ⟨hne, hlk, hval, hvalB⟩ := htab k (by omega)
    have hbs₁ : σ₁.vars bs = base := by rw [hvar₁ bs (Ne.symm hddbs)]; exact hbs
    have hvv₁ : σ₁.vars vv = v := by rw [hvar₁ vv (Ne.symm hddvv)]; exact hvv
    have hpd₁ : σ₁.arrs (pdF k) = σ.arrs (pdF k) := harr₁ _ hne
    have hlenca : base + Driver.isoPal Λc mb R ≤ (σ₁.arrs ca).length := by
      rw [hlen₁]; exact hlen
    -- the read
    have hget : (Expr.get (pdF k) (.var vv)).evalB B σ₁ = some (Dp k) := by
      refine evalB_get (k := v) ?_ ?_ hvalB
      · rw [← hvv₁]; exact evalB_var (by rw [hvv₁]; omega)
      · rw [hpd₁, getElem?_of_lt _ _ hlk, hval]
    set σ₂ : Env := σ₁.setVar dd (Dp k) with hσ₂_def
    have hrun₂ : Run B (.assign dd (.get (pdF k) (.var vv))) σ₁ σ₂ 3 := by
      simpa [hσ₂_def] using Run.assign (x := dd) hget
    -- the block's own offset arithmetic
    have hmulk : (R + 1) * k + (R + 1) ≤ mb * (R + 1) := by
      have h := Nat.mul_le_mul_left (R + 1) (show k + 1 ≤ mb by omega)
      calc (R + 1) * k + (R + 1) = (R + 1) * (k + 1) := by ring
        _ ≤ (R + 1) * mb := h
        _ = mb * (R + 1) := Nat.mul_comm _ _
    have hoffB : base + (Λc + (R + 1) * k + (R + 1)) < B := by
      rw [hpal] at hrowB; omega
    obtain ⟨σ₃, hrun₃, hpay₃, hfr₃, hlen₃, harr₃, hvar₃⟩ :=
      thrSeq_spec (ca := ca) (bs := bs) (dd := dd) (off := Λc + (R + 1) * k)
        (sh := 1) (base := base) (d := Dp k) (R + 1) hone hoffB hvalB (by omega)
        σ₂ ⟨by rw [hσ₂_def, vars_setVar, if_neg (Ne.symm hddbs)]; exact hbs₁,
          by rw [hσ₂_def, vars_setVar, if_pos rfl],
          by rw [hσ₂_def, arrs_setVar]; rw [hpal] at hlenca; omega⟩
    have harr₂ : ∀ b, σ₂.arrs b = σ₁.arrs b := fun b => by
      rw [hσ₂_def, arrs_setVar]
    refine ⟨σ₃, ((hrun₁.seq (hrun₂.seq hrun₃)).mono (le_of_eq (by ring))),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj i hi
      rcases Nat.lt_or_ge j k with hjk | hjk
      · have hmulj : (R + 1) * j + (R + 1) ≤ (R + 1) * k := by
          have h := Nat.mul_le_mul_left (R + 1) (show j + 1 ≤ k by omega)
          calc (R + 1) * j + (R + 1) = (R + 1) * (j + 1) := by ring
            _ ≤ (R + 1) * k := h
        rw [hfr₃ _ (Or.inl (by omega)), harr₂, hpay₁ j hjk i hi]
      · obtain rfl : j = k := by omega
        rw [hpay₃ i hi]
        by_cases hle : Dp j ≤ i
        · rw [if_pos hle, if_pos (by omega)]
        · rw [if_neg hle, if_neg (by omega)]
    · intro q hq
      rw [hfr₃ q (by omega), harr₂]
      exact hfr₁ q hq
    · intro b
      rw [hlen₃ b, harr₂ b, hlen₁ b]
    · intro b hb
      rw [harr₃ b hb, harr₂ b]
      exact harr₁ b hb
    · intro y hy
      rw [hvar₃ y, hσ₂_def, vars_setVar, if_neg hy]
      exact hvar₁ y hy

/-- The class half, specified: `k` blocks, `k` tables, and **two** slot
families off each — the `isoOld` cell (threshold `1`, which is the
class itself by §4) and the `R + 1` `isoPu` cells. Neither touches the
`pd` region, which is what lets the two halves run in either order. -/
theorem puSeq_spec {ca : String} {puF : ℕ → String} {bs dd vv : String}
    {Λc mb R base v : ℕ} {Dc : ℕ → ℕ}
    (hone : 1 < B) (hddbs : dd ≠ bs) (hddvv : dd ≠ vv)
    (hvB : v < B) (hRB : R + 3 < B)
    (hrowB : base + Driver.isoPal Λc mb R < B) :
    ∀ k : ℕ, k ≤ Λc →
    Spec B
      (fun σ => σ.vars bs = base ∧ σ.vars vv = v ∧
        (∀ c, c < Λc → puF c ≠ ca ∧ v < (σ.arrs (puF c)).length ∧
          (σ.arrs (puF c)).getD v 0 = Dc c ∧ Dc c < B) ∧
        base + Driver.isoPal Λc mb R ≤ (σ.arrs ca).length)
      (puSeq ca puF bs dd vv Λc mb R k)
      (fun σ σ' =>
        (∀ c, c < k → (σ'.arrs ca).getD (base + c) 0
            = if Dc c ≤ 1 then 1 else 0) ∧
        (∀ c, c < k → ∀ i, i < R + 1 →
          (σ'.arrs ca).getD (base + (Λc + mb * (R + 1) + (R + 1) * c + i)) 0
            = if Dc c ≤ i + 1 then 1 else 0) ∧
        (∀ q, base + Λc ≤ q → q < base + (Λc + mb * (R + 1)) →
            (σ'.arrs ca).getD q 0 = (σ.arrs ca).getD q 0) ∧
        (∀ q, q < base ∨ base + Driver.isoPal Λc mb R ≤ q →
            (σ'.arrs ca).getD q 0 = (σ.arrs ca).getD q 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ b, b ≠ ca → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ dd → σ'.vars y = σ.vars y))
      (1 + k * (9 * R + 23)) := by
  have hpal : Driver.isoPal Λc mb R = Λc + (mb * (R + 1) + Λc * (R + 1)) := rfl
  intro k
  induction k with
  | zero =>
    intro _ σ _
    refine ⟨σ, Run.skip.mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc; omega
    · intro c hc; omega
    · intro q _ _; rfl
    · intro q _; rfl
    · intro b; rfl
    · intro b _; rfl
    · intro y _; rfl
  | succ k ih =>
    intro hk σ hσ
    obtain ⟨hbs, hvv, htab, hlen⟩ := hσ
    obtain ⟨σ₁, hrun₁, hold₁, hpu₁, hpdreg₁, hout₁, hlen₁, harr₁, hvar₁⟩ :=
      ih (by omega) σ ⟨hbs, hvv, htab, hlen⟩
    obtain ⟨hne, hlk, hval, hvalB⟩ := htab k (by omega)
    have hbs₁ : σ₁.vars bs = base := by rw [hvar₁ bs (Ne.symm hddbs)]; exact hbs
    have hvv₁ : σ₁.vars vv = v := by rw [hvar₁ vv (Ne.symm hddvv)]; exact hvv
    have hpu₁a : σ₁.arrs (puF k) = σ.arrs (puF k) := harr₁ _ hne
    have hlenca : base + Driver.isoPal Λc mb R ≤ (σ₁.arrs ca).length := by
      rw [hlen₁]; exact hlen
    have hget : (Expr.get (puF k) (.var vv)).evalB B σ₁ = some (Dc k) := by
      refine evalB_get (k := v) ?_ ?_ hvalB
      · rw [← hvv₁]; exact evalB_var (by rw [hvv₁]; omega)
      · rw [hpu₁a, getElem?_of_lt _ _ hlk, hval]
    set σ₂ : Env := σ₁.setVar dd (Dc k) with hσ₂_def
    have hrun₂ : Run B (.assign dd (.get (puF k) (.var vv))) σ₁ σ₂ 3 := by
      simpa [hσ₂_def] using Run.assign (x := dd) hget
    have harr₂ : ∀ b, σ₂.arrs b = σ₁.arrs b := fun b => by
      rw [hσ₂_def, arrs_setVar]
    have hmulk : (R + 1) * k + (R + 1) ≤ Λc * (R + 1) := by
      have h := Nat.mul_le_mul_left (R + 1) (show k + 1 ≤ Λc by omega)
      calc (R + 1) * k + (R + 1) = (R + 1) * (k + 1) := by ring
        _ ≤ (R + 1) * Λc := h
        _ = Λc * (R + 1) := Nat.mul_comm _ _
    -- the old slot
    obtain ⟨σ₃, hrun₃, hpayO, hfrO, hlenO, harrO, hvarO⟩ :=
      thrSeq_spec (ca := ca) (bs := bs) (dd := dd) (off := k) (sh := 2)
        (base := base) (d := Dc k) 1 hone (by rw [hpal] at hrowB; omega) hvalB
        (by omega)
        σ₂ ⟨by rw [hσ₂_def, vars_setVar, if_neg (Ne.symm hddbs)]; exact hbs₁,
          by rw [hσ₂_def, vars_setVar, if_pos rfl],
          by rw [hσ₂_def, arrs_setVar]; rw [hpal] at hlenca; omega⟩
    -- the profile slots
    obtain ⟨σ₄, hrun₄, hpayP, hfrP, hlenP, harrP, hvarP⟩ :=
      thrSeq_spec (ca := ca) (bs := bs) (dd := dd)
        (off := Λc + mb * (R + 1) + (R + 1) * k) (sh := 2) (base := base)
        (d := Dc k) (R + 1) hone (by rw [hpal] at hrowB; omega) hvalB (by omega)
        σ₃ ⟨by rw [hvarO bs, hσ₂_def, vars_setVar, if_neg (Ne.symm hddbs)]; exact hbs₁,
          by rw [hvarO dd, hσ₂_def, vars_setVar, if_pos rfl],
          by rw [hlenO ca, hσ₂_def, arrs_setVar]; rw [hpal] at hlenca; omega⟩
    refine ⟨σ₄, ((hrun₁.seq (hrun₂.seq (hrun₃.seq hrun₄))).mono
      (le_of_eq (by ring))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases Nat.lt_or_ge c k with hck | hck
      · rw [hfrP _ (Or.inl (by omega)), hfrO _ (Or.inl (by omega)), harr₂]
        exact hold₁ c hck
      · obtain rfl : c = k := by omega
        rw [hfrP _ (Or.inl (by omega))]
        have := hpayO 0 (by omega)
        simpa using this
    · intro c hc i hi
      rcases Nat.lt_or_ge c k with hck | hck
      · have hmulc : (R + 1) * c + (R + 1) ≤ (R + 1) * k := by
          have h := Nat.mul_le_mul_left (R + 1) (show c + 1 ≤ k by omega)
          calc (R + 1) * c + (R + 1) = (R + 1) * (c + 1) := by ring
            _ ≤ (R + 1) * k := h
        rw [hfrP _ (Or.inl (by omega)), hfrO _ (Or.inr (by omega)), harr₂]
        exact hpu₁ c hck i hi
      · obtain rfl : c = k := by omega
        rw [hpayP i hi]
        by_cases hle : Dc c ≤ i + 1
        · rw [if_pos hle, if_pos (by omega)]
        · rw [if_neg hle, if_neg (by omega)]
    · intro q hq1 hq2
      rw [hfrP q (Or.inl (by omega)), hfrO q (Or.inr (by omega)), harr₂]
      exact hpdreg₁ q hq1 hq2
    · intro q hq
      rw [hfrP q (by rw [hpal] at hq; omega),
        hfrO q (by rw [hpal] at hq; omega), harr₂]
      exact hout₁ q hq
    · intro b
      rw [hlenP b, hlenO b, harr₂ b, hlen₁ b]
    · intro b hb
      rw [harrP b hb, harrO b hb, harr₂ b]
      exact harr₁ b hb
    · intro y hy
      rw [hvarP y, hvarO y, hσ₂_def, vars_setVar, if_neg hy]
      exact hvar₁ y hy

/-! ## §7 The writer

The carrier loop, in `Spec.forRangeZero`'s own shape. The rows are
disjoint intervals of the colour region, so the invariant is "every row
below the counter is finished" and the step obligation is the two
family specs plus the two interval facts below. -/

private theorem row_lt_base {Λ' w v off : ℕ} (hwv : w < v) (hoff : off < Λ') :
    w * Λ' + off < v * Λ' := by
  have h : (w + 1) * Λ' ≤ v * Λ' := Nat.mul_le_mul_right _ (by omega)
  have h2 : (w + 1) * Λ' = w * Λ' + Λ' := by ring
  omega

private theorem row_top_le {Λ' v cN : ℕ} (hv : v < cN) :
    v * Λ' + Λ' ≤ cN * Λ' := by
  have h : (v + 1) * Λ' ≤ cN * Λ' := Nat.mul_le_mul_right _ (by omega)
  have h2 : (v + 1) * Λ' = v * Λ' + Λ' := by ring
  omega

/-- The loop's invariant: the counter, the tables (untouched, since the
writer's only array is `ca`), and every row strictly below the counter
finished in all three slot families. -/
private def ColInv (ca cn : String) (pdF puF : ℕ → String) (vv : String)
    (cN Λc mb R : ℕ) (Dp Dc : ℕ → ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars cn = cN ∧ τ.vars vv ≤ cN ∧
    cN * Driver.isoPal Λc mb R ≤ (τ.arrs ca).length ∧
    (∀ j, j < mb → pdF j ≠ ca ∧ cN ≤ (τ.arrs (pdF j)).length ∧
      ∀ w, w < cN → (τ.arrs (pdF j)).getD w 0 = Dp j w) ∧
    (∀ c, c < Λc → puF c ≠ ca ∧ cN ≤ (τ.arrs (puF c)).length ∧
      ∀ w, w < cN → (τ.arrs (puF c)).getD w 0 = Dc c w) ∧
    (∀ w, w < τ.vars vv → ∀ c, c < Λc →
      (τ.arrs ca).getD (w * Driver.isoPal Λc mb R + c) 0
        = if Dc c w ≤ 1 then 1 else 0) ∧
    (∀ w, w < τ.vars vv → ∀ j, j < mb → ∀ i, i < R + 1 →
      (τ.arrs ca).getD (w * Driver.isoPal Λc mb R + (Λc + (R + 1) * j + i)) 0
        = if Dp j w ≤ i then 1 else 0) ∧
    (∀ w, w < τ.vars vv → ∀ c, c < Λc → ∀ i, i < R + 1 →
      (τ.arrs ca).getD (w * Driver.isoPal Λc mb R
          + (Λc + mb * (R + 1) + (R + 1) * c + i)) 0
        = if Dc c w ≤ i + 1 then 1 else 0)

/-- **The colour-region writer, specified** (offset form): every cell
of every row of the `isoPal` region holds the bit its slot family
prescribes — the `isoOld` cells at the class table's threshold `1`, the
`isoPd` cells at the batch tables' thresholds, the `isoPu` cells at the
class tables' shifted thresholds. The table arrays and every other
array are untouched, no reallocation, three scratch scalars. -/
theorem colWriteCom_spec {ca cn : String} {pdF puF : ℕ → String}
    {bs dd vv : String} {cN Λc mb R : ℕ} {Dp Dc : ℕ → ℕ → ℕ}
    (hone : 1 < B) (hddbs : dd ≠ bs) (hddvv : dd ≠ vv) (hbsvv : bs ≠ vv)
    (hvvcn : vv ≠ cn) (hbscn : bs ≠ cn) (hddcn : dd ≠ cn)
    (hRB : R + 3 < B) (hNB : cN < B)
    (hrowB : cN * Driver.isoPal Λc mb R < B)
    (hpdB : ∀ j w, Dp j w < B) (hpuB : ∀ c w, Dc c w < B) :
    Spec B
      (fun σ => σ.vars cn = cN ∧
        cN * Driver.isoPal Λc mb R ≤ (σ.arrs ca).length ∧
        (∀ j, j < mb → pdF j ≠ ca ∧ cN ≤ (σ.arrs (pdF j)).length ∧
          ∀ w, w < cN → (σ.arrs (pdF j)).getD w 0 = Dp j w) ∧
        (∀ c, c < Λc → puF c ≠ ca ∧ cN ≤ (σ.arrs (puF c)).length ∧
          ∀ w, w < cN → (σ.arrs (puF c)).getD w 0 = Dc c w))
      (colWriteCom ca cn pdF puF bs dd vv Λc mb R)
      (fun σ σ' =>
        (∀ w, w < cN → ∀ c, c < Λc →
          (σ'.arrs ca).getD (w * Driver.isoPal Λc mb R + c) 0
            = if Dc c w ≤ 1 then 1 else 0) ∧
        (∀ w, w < cN → ∀ j, j < mb → ∀ i, i < R + 1 →
          (σ'.arrs ca).getD
              (w * Driver.isoPal Λc mb R + (Λc + (R + 1) * j + i)) 0
            = if Dp j w ≤ i then 1 else 0) ∧
        (∀ w, w < cN → ∀ c, c < Λc → ∀ i, i < R + 1 →
          (σ'.arrs ca).getD (w * Driver.isoPal Λc mb R
              + (Λc + mb * (R + 1) + (R + 1) * c + i)) 0
            = if Dc c w ≤ i + 1 then 1 else 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ b, b ≠ ca → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ vv → y ≠ bs → y ≠ dd → σ'.vars y = σ.vars y))
      (colWriteK cN Λc mb R) := by
  have hpal : Driver.isoPal Λc mb R = Λc + (mb * (R + 1) + Λc * (R + 1)) := rfl
  intro σ hσ
  obtain ⟨hcn, hlen, hpdT, hpuT⟩ := hσ
  have hbody : Spec B
      (fun τ => ColInv ca cn pdF puF vv cN Λc mb R Dp Dc τ ∧ τ.vars vv < cN)
      (.seq (colRowCom ca pdF puF bs dd vv Λc mb R)
        (.assign vv (.add (.var vv) (.lit 1))))
      (fun τ τ' => ColInv ca cn pdF puF vv cN Λc mb R Dp Dc τ' ∧
        τ'.vars vv = τ.vars vv + 1)
      (10 + mb * (9 * R + 13) + Λc * (9 * R + 23)) := by
    rintro τ ⟨hIτ, hltτ⟩
    obtain ⟨hcnτ, hvvτ, hlenτ, hpdτ, hpuτ, holdτ, hpdrowτ, hpurowτ⟩ := hIτ
    obtain ⟨v, hv_def⟩ : ∃ v : ℕ, τ.vars vv = v := ⟨_, rfl⟩
    rw [hv_def] at hltτ hvvτ holdτ hpdrowτ hpurowτ
    have htop : v * Driver.isoPal Λc mb R + Driver.isoPal Λc mb R
        ≤ cN * Driver.isoPal Λc mb R := row_top_le hltτ
    -- the row base
    have hmulv : (Expr.mul (.var vv) (.lit (Driver.isoPal Λc mb R))).evalB B τ
        = some (v * Driver.isoPal Λc mb R) := by
      have h1 : (Expr.var vv).evalB B τ = some v := by
        rw [← hv_def]; exact evalB_var (by rw [hv_def]; omega)
      have h2 : (Expr.lit (Driver.isoPal Λc mb R)).evalB B τ
          = some (Driver.isoPal Λc mb R) := evalB_lit (by omega)
      have h3 : Bop.mul.apply v (Driver.isoPal Λc mb R) < B := by
        simp only [Bop.apply_mul]; omega
      simpa using evalB_bin h1 h2 h3
    have hrun₁ : Run B
        (.assign bs (.mul (.var vv) (.lit (Driver.isoPal Λc mb R)))) τ
        (τ.setVar bs (v * Driver.isoPal Λc mb R)) 4 := by
      simpa using Run.assign (x := bs) hmulv
    have hτ₁arr : ∀ b, (τ.setVar bs (v * Driver.isoPal Λc mb R)).arrs b
        = τ.arrs b := fun b => by rw [arrs_setVar]
    have hτ₁bs : (τ.setVar bs (v * Driver.isoPal Λc mb R)).vars bs
        = v * Driver.isoPal Λc mb R := by rw [vars_setVar, if_pos rfl]
    have hτ₁vv : (τ.setVar bs (v * Driver.isoPal Λc mb R)).vars vv = v := by
      rw [vars_setVar, if_neg (Ne.symm hbsvv)]; exact hv_def
    -- the batch half
    obtain ⟨τ₂, hrun₂, hpdpay, hpdfr, hpdlen, hpdarr, hpdvar⟩ :=
      pdSeq_spec (ca := ca) (pdF := pdF) (bs := bs) (dd := dd) (vv := vv)
        (Λc := Λc) (mb := mb) (R := R)
        (base := v * Driver.isoPal Λc mb R) (v := v)
        (Dp := fun j => Dp j v) hone hddbs hddvv (by omega) hRB (by omega)
        mb le_rfl (τ.setVar bs (v * Driver.isoPal Λc mb R))
        ⟨hτ₁bs, hτ₁vv,
          fun j hj => by
            obtain ⟨h1, h2, h3⟩ := hpdτ j hj
            exact ⟨h1, by rw [hτ₁arr]; omega, by rw [hτ₁arr]; exact h3 v hltτ,
              hpdB j v⟩,
          by rw [hτ₁arr]; omega⟩
    -- the class half
    obtain ⟨τ₃, hrun₃, hopay, hupay, hpdreg, hout, hlen₃, harr₃, hvar₃⟩ :=
      puSeq_spec (ca := ca) (puF := puF) (bs := bs) (dd := dd) (vv := vv)
        (Λc := Λc) (mb := mb) (R := R)
        (base := v * Driver.isoPal Λc mb R) (v := v)
        (Dc := fun c => Dc c v) hone hddbs hddvv (by omega) hRB (by omega)
        Λc le_rfl τ₂
        ⟨by rw [hpdvar bs (Ne.symm hddbs), hτ₁bs],
          by rw [hpdvar vv (Ne.symm hddvv), hτ₁vv],
          fun c hc => by
            obtain ⟨h1, h2, h3⟩ := hpuτ c hc
            exact ⟨h1, by rw [hpdarr _ h1, hτ₁arr]; omega,
              by rw [hpdarr _ h1, hτ₁arr]; exact h3 v hltτ, hpuB c v⟩,
          by rw [hpdlen ca, hτ₁arr]; omega⟩
    -- the increment
    have hτ₃vv : τ₃.vars vv = v := by
      rw [hvar₃ vv (Ne.symm hddvv), hpdvar vv (Ne.symm hddvv), hτ₁vv]
    have hincr : (Expr.add (.var vv) (.lit 1)).evalB B τ₃ = some (v + 1) := by
      have h1 : (Expr.var vv).evalB B τ₃ = some v := by
        rw [← hτ₃vv]; exact evalB_var (by rw [hτ₃vv]; omega)
      have h2 : (Expr.lit 1).evalB B τ₃ = some 1 := evalB_lit hone
      have h3 : Bop.add.apply v 1 < B := by simp only [Bop.apply_add]; omega
      simpa using evalB_bin h1 h2 h3
    have hrun₄ : Run B (.assign vv (.add (.var vv) (.lit 1))) τ₃
        (τ₃.setVar vv (v + 1)) 4 := by
      simpa using Run.assign (x := vv) hincr
    have hτ₄arr : ∀ b, (τ₃.setVar vv (v + 1)).arrs b = τ₃.arrs b := fun b => by
      rw [arrs_setVar]
    have hτ₄vv : (τ₃.setVar vv (v + 1)).vars vv = v + 1 := by
      rw [vars_setVar, if_pos rfl]
    have harrca : ∀ b, b ≠ ca → (τ₃.setVar vv (v + 1)).arrs b = τ.arrs b :=
      fun b hb => by rw [hτ₄arr, harr₃ b hb, hpdarr b hb, hτ₁arr]
    have hlenca : ∀ b, ((τ₃.setVar vv (v + 1)).arrs b).length
        = (τ.arrs b).length := fun b => by
      rw [hτ₄arr, hlen₃ b, hpdlen b, hτ₁arr]
    refine ⟨τ₃.setVar vv (v + 1),
      (((hrun₁.seq (hrun₂.seq hrun₃)).seq hrun₄).mono (le_of_eq (by ring))),
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hτ₄vv, hv_def]⟩
    · rw [vars_setVar, if_neg (Ne.symm hvvcn), hvar₃ cn (Ne.symm hddcn),
        hpdvar cn (Ne.symm hddcn), vars_setVar, if_neg (Ne.symm hbscn)]
      exact hcnτ
    · rw [hτ₄vv]; omega
    · rw [hlenca ca]; exact hlenτ
    · intro j hj
      obtain ⟨h1, h2, h3⟩ := hpdτ j hj
      exact ⟨h1, by rw [harrca _ h1]; exact h2, by rw [harrca _ h1]; exact h3⟩
    · intro c hc
      obtain ⟨h1, h2, h3⟩ := hpuτ c hc
      exact ⟨h1, by rw [harrca _ h1]; exact h2, by rw [harrca _ h1]; exact h3⟩
    · intro w hw c hc
      rw [hτ₄vv] at hw
      rw [hτ₄arr]
      rcases Nat.lt_or_ge w v with hwv | hwv
      · have hlt := row_lt_base hwv (old_offset_lt (Λc := Λc) (mb := mb) (R := R) c hc)
        rw [hout (w * Driver.isoPal Λc mb R + c) (Or.inl hlt),
          hpdfr (w * Driver.isoPal Λc mb R + c) (Or.inl (by omega)), hτ₁arr]
        exact holdτ w (by omega) c hc
      · obtain rfl : w = v := by omega
        exact hopay c hc
    · intro w hw j hj i hi
      rw [hτ₄vv] at hw
      rw [hτ₄arr]
      rcases Nat.lt_or_ge w v with hwv | hwv
      · have hlt := row_lt_base hwv (pd_offset_lt (Λc := Λc) (mb := mb) (R := R) j i hj hi)
        rw [hout (w * Driver.isoPal Λc mb R + (Λc + (R + 1) * j + i))
            (Or.inl hlt),
          hpdfr (w * Driver.isoPal Λc mb R + (Λc + (R + 1) * j + i))
            (Or.inl (by omega)), hτ₁arr]
        exact hpdrowτ w (by omega) j hj i hi
      · obtain rfl : w = v := by omega
        have hmulj : (R + 1) * j + (R + 1) ≤ mb * (R + 1) := by
          have h := Nat.mul_le_mul_left (R + 1) (show j + 1 ≤ mb by omega)
          calc (R + 1) * j + (R + 1) = (R + 1) * (j + 1) := by ring
            _ ≤ (R + 1) * mb := h
            _ = mb * (R + 1) := Nat.mul_comm _ _
        rw [hpdreg (w * Driver.isoPal Λc mb R + (Λc + (R + 1) * j + i))
          (by omega) (by omega)]
        exact hpdpay j hj i hi
    · intro w hw c hc i hi
      rw [hτ₄vv] at hw
      rw [hτ₄arr]
      rcases Nat.lt_or_ge w v with hwv | hwv
      · have hlt := row_lt_base hwv (pu_offset_lt (Λc := Λc) (mb := mb) (R := R) c i hc hi)
        rw [hout (w * Driver.isoPal Λc mb R
              + (Λc + mb * (R + 1) + (R + 1) * c + i)) (Or.inl hlt),
          hpdfr (w * Driver.isoPal Λc mb R
              + (Λc + mb * (R + 1) + (R + 1) * c + i)) (Or.inl (by omega)),
          hτ₁arr]
        exact hpurowτ w (by omega) c hc i hi
      · obtain rfl : w = v := by omega
        exact hupay c hc i hi
  -- the loop
  have hloop := Spec.forRangeZero (B := B) vv cn
    (ColInv ca cn pdF puF vv cN Λc mb R Dp Dc) cN
    (10 + mb * (9 * R + 13) + Λc * (9 * R + 23)) hNB
    (fun _ hτ => hτ.2.1) (fun _ hτ => hτ.1) hbody
  have hIinit : ColInv ca cn pdF puF vv cN Λc mb R Dp Dc (σ.setVar vv 0) := by
    refine ⟨by rw [vars_setVar, if_neg (Ne.symm hvvcn)]; exact hcn,
      by rw [vars_setVar, if_pos rfl]; omega,
      by rw [arrs_setVar]; exact hlen, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨h1, h2, h3⟩ := hpdT j hj
      exact ⟨h1, by rw [arrs_setVar]; exact h2, by rw [arrs_setVar]; exact h3⟩
    · intro c hc
      obtain ⟨h1, h2, h3⟩ := hpuT c hc
      exact ⟨h1, by rw [arrs_setVar]; exact h2, by rw [arrs_setVar]; exact h3⟩
    · intro w hw
      rw [vars_setVar, if_pos rfl] at hw; omega
    · intro w hw
      rw [vars_setVar, if_pos rfl] at hw; omega
    · intro w hw
      rw [vars_setVar, if_pos rfl] at hw; omega
  obtain ⟨σ', hrun, hIfin, hvvfin⟩ := hloop.run hIinit
  obtain ⟨-, -, -, -, -, hold', hpd', hpu'⟩ := hIfin
  rw [hvvfin] at hold' hpd' hpu'
  refine ⟨σ', hrun.mono ?_, hold', hpd', hpu', ?_, ?_, ?_⟩
  · unfold colWriteK; ring_nf; omega
  · exact run_arrs_length_eq hrun
  · intro b hb
    exact hrun.frame_arr b fun h =>
      hb (warrs_colWriteCom ca cn pdF puF bs dd vv Λc mb R b h)
  · intro y h1 h2 h3
    refine hrun.frame_var y fun h => ?_
    rcases wvars_colWriteCom ca cn pdF puF bs dd vv Λc mb R y h with h' | h' | h'
    · exact h1 h'
    · exact h2 h'
    · exact h3 h'

/-! ## §8 The writer at the palette's slots, and at `machChild`

§7 is stated at the *offsets* the program emits. `isoPal_offset_cases`
turns them back into slots, and §4 turns the `isoOld` cells into the
old classes, so the region reads back as `ColBits`'s clause at
`Impl.recordProfilesMS` — which at the driver's own objects is
`machChild.col` by definition. -/

open Classical in
/-- **The colour region, at the palette's slots**: `ColBits`'s own
clause, at `Impl.recordProfilesMS R f Dp Dc`. The seam
`Impl.ProfileTablesMS` enters in exactly one place — the `isoOld`
cells, which the emitter reads off the class tables at threshold `1`
(§4). -/
theorem colWriteCom_rows {ca cn : String} {pdF puF : ℕ → String}
    {bs dd vv : String} {cN Λc mb R : ℕ}
    {H : SimpleGraph (Fin cN)} {wf : Fin mb → Fin cN}
    {f : Fin Λc → Set (Fin cN)}
    {Dp : Fin mb → Fin cN → ℕ} {Dc : Fin Λc → Fin (cN + 1) → ℕ}
    (hprof : Impl.ProfileTablesMS H wf f R Dp Dc)
    (hpdle : ∀ (j : Fin mb) (x : Fin cN), Dp j x ≤ R + 1)
    (hpule : ∀ (c : Fin Λc) (x : Fin (cN + 1)), Dc c x ≤ R + 2)
    (hone : 1 < B) (hddbs : dd ≠ bs) (hddvv : dd ≠ vv) (hbsvv : bs ≠ vv)
    (hvvcn : vv ≠ cn) (hbscn : bs ≠ cn) (hddcn : dd ≠ cn)
    (hRB : R + 3 < B) (hNB : cN < B)
    (hrowB : cN * Driver.isoPal Λc mb R < B) :
    Spec B
      (fun σ => σ.vars cn = cN ∧
        cN * Driver.isoPal Λc mb R ≤ (σ.arrs ca).length ∧
        (∀ j : Fin mb, pdF (j : ℕ) ≠ ca ∧ cN ≤ (σ.arrs (pdF (j : ℕ))).length ∧
          ∀ x : Fin cN, (σ.arrs (pdF (j : ℕ))).getD (x : ℕ) 0 = Dp j x) ∧
        (∀ c : Fin Λc, puF (c : ℕ) ≠ ca ∧ cN ≤ (σ.arrs (puF (c : ℕ))).length ∧
          ∀ x : Fin cN, (σ.arrs (puF (c : ℕ))).getD (x : ℕ) 0
            = Dc c x.castSucc))
      (colWriteCom ca cn pdF puF bs dd vv Λc mb R)
      (fun σ σ' =>
        (∀ (x : Fin cN) (c' : Fin (Driver.isoPal Λc mb R)),
          (σ'.arrs ca).getD ((x : ℕ) * Driver.isoPal Λc mb R + (c' : ℕ)) 0
            = if x ∈ Impl.recordProfilesMS R f Dp Dc c' then 1 else 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ b, b ≠ ca → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ vv → y ≠ bs → y ≠ dd → σ'.vars y = σ.vars y))
      (colWriteK cN Λc mb R) := by
  classical
  set Dp₀ : ℕ → ℕ → ℕ := fun j x =>
    if h : j < mb then (if h2 : x < cN then Dp ⟨j, h⟩ ⟨x, h2⟩ else 0) else 0
    with hDp₀
  set Dc₀ : ℕ → ℕ → ℕ := fun c x =>
    if h : c < Λc then
      (if h2 : x < cN then Dc ⟨c, h⟩ (Fin.castSucc ⟨x, h2⟩) else 0) else 0
    with hDc₀
  have hDp₀_eq : ∀ (j : Fin mb) (x : Fin cN), Dp₀ (j : ℕ) (x : ℕ) = Dp j x := by
    intro j x
    simp only [hDp₀, dif_pos j.isLt, dif_pos x.isLt, Fin.eta]
  have hDc₀_eq : ∀ (c : Fin Λc) (x : Fin cN),
      Dc₀ (c : ℕ) (x : ℕ) = Dc c x.castSucc := by
    intro c x
    simp only [hDc₀, dif_pos c.isLt, dif_pos x.isLt, Fin.eta]
  have hpdB : ∀ j x, Dp₀ j x < B := by
    intro j x
    by_cases h : j < mb
    · by_cases h2 : x < cN
      · have hv : Dp₀ j x = Dp ⟨j, h⟩ ⟨x, h2⟩ := by
          simp only [hDp₀, dif_pos h, dif_pos h2]
        have := hpdle ⟨j, h⟩ ⟨x, h2⟩
        omega
      · simp only [hDp₀, dif_pos h, dif_neg h2]; omega
    · simp only [hDp₀, dif_neg h]; omega
  have hpuB : ∀ c x, Dc₀ c x < B := by
    intro c x
    by_cases h : c < Λc
    · by_cases h2 : x < cN
      · have hv : Dc₀ c x = Dc ⟨c, h⟩ (Fin.castSucc ⟨x, h2⟩) := by
          simp only [hDc₀, dif_pos h, dif_pos h2]
        have := hpule ⟨c, h⟩ (Fin.castSucc ⟨x, h2⟩)
        omega
      · simp only [hDc₀, dif_pos h, dif_neg h2]; omega
    · simp only [hDc₀, dif_neg h]; omega
  refine ((colWriteCom_spec (ca := ca) (cn := cn) (pdF := pdF) (puF := puF)
    (bs := bs) (dd := dd) (vv := vv) (cN := cN) (Λc := Λc) (mb := mb) (R := R)
    (Dp := Dp₀) (Dc := Dc₀) hone hddbs hddvv hbsvv hvvcn hbscn hddcn hRB hNB
    hrowB hpdB hpuB).pre ?_).post ?_
  · rintro σ ⟨hcn, hlen, hpdT, hpuT⟩
    refine ⟨hcn, hlen, ?_, ?_⟩
    · intro j hj
      obtain ⟨h1, h2, h3⟩ := hpdT ⟨j, hj⟩
      exact ⟨h1, h2, fun x hx => by
        have := h3 ⟨x, hx⟩
        rw [this, ← hDp₀_eq ⟨j, hj⟩ ⟨x, hx⟩]⟩
    · intro c hc
      obtain ⟨h1, h2, h3⟩ := hpuT ⟨c, hc⟩
      exact ⟨h1, h2, fun x hx => by
        have := h3 ⟨x, hx⟩
        rw [this, ← hDc₀_eq ⟨c, hc⟩ ⟨x, hx⟩]⟩
  · rintro σ σ' - ⟨hold, hpd, hpu, hlen', harr', hvar'⟩
    refine ⟨?_, hlen', harr', hvar'⟩
    intro x c'
    rcases isoPal_offset_cases c' with ⟨c, rfl, hnum⟩ | ⟨j, a, rfl, hnum⟩
      | ⟨c, b, rfl, hnum⟩
    · rw [hnum, hold (x : ℕ) x.isLt (c : ℕ) c.isLt, hDc₀_eq c x,
        Impl.recordProfilesMS_old]
      have hf := oldRow_eq_thr_one hprof c
      by_cases hmem : x ∈ f c
      · rw [if_pos hmem, if_pos (by rw [hf] at hmem; exact hmem)]
      · rw [if_neg hmem, if_neg (fun hle => hmem (by rw [hf]; exact hle))]
    · rw [hnum, hpd (x : ℕ) x.isLt (j : ℕ) j.isLt (a : ℕ) a.isLt,
        hDp₀_eq j x, Impl.recordProfilesMS_pd]
      by_cases hle : Dp j x ≤ (a : ℕ)
      · rw [if_pos hle, if_pos (show x ∈ {z | Dp j z ≤ (a : ℕ)} from hle)]
      · rw [if_neg hle, if_neg (show x ∉ {z | Dp j z ≤ (a : ℕ)} from hle)]
    · rw [hnum, hpu (x : ℕ) x.isLt (c : ℕ) c.isLt (b : ℕ) b.isLt,
        hDc₀_eq c x, Impl.recordProfilesMS_pu]
      by_cases hle : Dc c x.castSucc ≤ (b : ℕ) + 1
      · rw [if_pos hle,
          if_pos (show x ∈ {z | Dc c (Fin.castSucc z) ≤ (b : ℕ) + 1} from hle)]
      · rw [if_neg hle,
          if_neg (show x ∉ {z | Dc c (Fin.castSucc z) ≤ (b : ℕ) + 1} from hle)]

open Classical in
/-- **The writer at `machChild`** — the leaf's own statement. Under the
`ProfileTablesMS` witness at the pre-isolation child (graph `preG`,
padded batch `batchFn`, marker-extended classes `childColR` — verbatim
`profilesCom_specW`'s deliverable, hazards 1 and 2), the colour region
reads back as `machChild`'s colour field, cell by cell, at a budget
`prepStageK` absorbs (`colWriteK_le_prepStageK`). Every other array,
the profile tables included, is preserved verbatim. -/
theorem colWriteCom_machChild {L n₀ : ℕ} (S : Setup L) {Λ : ℕ}
    (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {ca cn : String} {pdF puF : ℕ → String} {bs dd vv : String}
    {Dp : Fin S.width → Fin (childN S A π u) → ℕ}
    {Dc : Fin (relPal Λ) → Fin (childN S A π u + 1) → ℕ}
    (hprof : Impl.ProfileTablesMS (preG S A π u) (batchFn S A π u)
      (childColR S A π u) S.R Dp Dc)
    (hpdle : ∀ (j : Fin S.width) (x : Fin (childN S A π u)), Dp j x ≤ S.R + 1)
    (hpule : ∀ (c : Fin (relPal Λ)) (x : Fin (childN S A π u + 1)),
      Dc c x ≤ S.R + 2)
    (hone : 1 < B) (hddbs : dd ≠ bs) (hddvv : dd ≠ vv) (hbsvv : bs ≠ vv)
    (hvvcn : vv ≠ cn) (hbscn : bs ≠ cn) (hddcn : dd ≠ cn)
    (hRB : S.R + 3 < B) (hNB : childN S A π u < B)
    (hrowB : childN S A π u
      * Driver.isoPal (relPal Λ) S.width S.R < B) {ℓc : ℕ}
    (chan : Fin (childN S A π u) → Fin ℓc →
      List (Fin (childN S A π u))) :
    Spec B
      (fun σ => σ.vars cn = childN S A π u ∧
        childN S A π u * Driver.isoPal (relPal Λ) S.width S.R
          ≤ (σ.arrs ca).length ∧
        (∀ j : Fin S.width, pdF (j : ℕ) ≠ ca ∧
          childN S A π u ≤ (σ.arrs (pdF (j : ℕ))).length ∧
          ∀ x : Fin (childN S A π u),
            (σ.arrs (pdF (j : ℕ))).getD (x : ℕ) 0 = Dp j x) ∧
        (∀ c : Fin (relPal Λ), puF (c : ℕ) ≠ ca ∧
          childN S A π u ≤ (σ.arrs (puF (c : ℕ))).length ∧
          ∀ x : Fin (childN S A π u),
            (σ.arrs (puF (c : ℕ))).getD (x : ℕ) 0 = Dc c x.castSucc))
      (colWriteCom ca cn pdF puF bs dd vv (relPal Λ) S.width S.R)
      (fun σ σ' =>
        (∀ (x : Fin (machChild S A π u Dp Dc chan).N)
           (c' : Fin (Driver.isoPal (relPal Λ) S.width S.R)),
          (σ'.arrs ca).getD
              ((x : ℕ) * Driver.isoPal (relPal Λ) S.width S.R + (c' : ℕ)) 0
            = if x ∈ (machChild S A π u Dp Dc chan).col c' then 1 else 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ b, b ≠ ca → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ vv → y ≠ bs → y ≠ dd → σ'.vars y = σ.vars y))
      (colWriteK (childN S A π u) (relPal Λ) S.width S.R) :=
  colWriteCom_rows hprof hpdle hpule hone hddbs hddvv hbsvv hvvcn hbscn hddcn
    hRB hNB hrowB

end Phases

end Lax3Proofs.Prog
