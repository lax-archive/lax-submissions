import Lax3Proofs.SolveMachPrepRun
import Lax3Proofs.SolveChainRestrict

/-!
# F6c12-1a — the abstract↔machine channel seam, closed

Leaf G1 repaired the ⟨D⟩ finding by defining the batch off the arena's
**channel field**, `batchPar A u = {u} ∪ {z | ∃ e < A.hist.length,
z ∈ A.chan u e}` (`DriverArena` §batch). `SolveMachPrepRun` then read
§5 line 19 at the machine's objects. But the two layers were still not
joined: **`A.chan` occurred in exactly two files, `DriverArena` and
`DriverCorrect`, and nowhere in the machine layer** — `BlockPre` holds
`htabF j A` in the level's channel region, and nothing said that table
*is* the arena's channel.

This file closes that seam. It states the five pins the composition
needs and — the point — **gives a witness for each and proves the pin
of it**, so that no residual is left that nobody can satisfy.

## §1–§3 The pins, and their witnesses

* **The channel pin** `ChanPin`: `htabF j A v e = A.chan v ↑e` on the
  rounds that carry data. `htabF` is F7's own free parameter, of type
  `(j) → (A : Arena (S.pal j) n₀) → Fin A.N → Fin (ℓp j) → List (Fin A.N)`,
  and `A.chan : Fin A.N → ℕ → List (Fin A.N)`, so F7 may simply
  **define** it: `chanTab S ℓp j A v e := A.chan v ↑e`. The pin holds
  of that definition by `rfl`, and — §5 — it holds *unconditionally*,
  not merely below `hist.length`.
* **The round-count pin** `RoundPin`: `Adm j A → A.hist.length = j`.
  A scan of the channel columns needs a compile-time column count; `j`
  is the level constant. Witnessed by `prepAdm`, which also carries the
  `≤ 2R+1` row bound the channel region's stride is sized by, and which
  is **preserved along the driver's own recursion**: `prepAdm_root`,
  `prepAdm_child`. Both pins are monotone in `Adm`
  (`roundPin_mono`), so F7 may conjoin `prepAdm` onto whatever else
  admissibility must carry.
* **The column/width pins** `ColPin`/`BoundPin`/`RoomPin`/`FitPin`:
  `ℓp (j+1) = ℓp j`, `hbf (j+1) = hbf j`, `A.hist.length < ℓp (j+1)`
  (the column the supports call writes) and `A.hist.length ≤ ℓp j`
  (the columns the batch scan reads). Witnessed by the constant
  families `colCount S = fun _ => S.depth + 1` and
  `chanBound S = fun _ => 2 * S.R + 1`.

`PrepPins` bundles the five, and **`stdPins`** exhibits the whole
bundle at the canonical instantiation — the deliverable this file
exists for.

## §4 What the `ℓp` pin costs

`restrictCom_specW` (`SolveChainRestrict`) returns an
`MArena Λc n₀ ℓp` at the **parent's** `ℓp`/`hb`; so do
`supportsCom_specW` and `isolateCom_specW`. The `ChildLoadParts`
deliverable is at `ℓp (j+1)`/`hbf (j+1)`. The two pins close that gap
at *different* prices, and the difference is worth naming:

* `hbf (j+1) = hbf j` is an equation between **naturals in a
  non-type position** (`hb` is only the channel region's stride). It
  costs a rewrite; there is nothing to transport.
* `ℓp (j+1) = ℓp j` is an equation between the **index type** of the
  `hist` family, `Fin (ℓp ·)`. It costs a genuine re-indexing, given
  here as `castCols`: not `h ▸ A` on the whole structure, but the
  field-level `hist v e := A.hist v (Fin.cast h.symm e)`. Its four
  other fields are preserved by `rfl` (`castCols_N/G/col/up`); it
  commutes with `ofArena`, `restrict` and `isolate` by `rfl` and with
  the supports patch once the index equation is substituted
  (`castCols_patch`); and `ArenaStW` transports across it
  (`arenaStW_castCols`). `arenaStW_machChild_cast` is that transport at
  the deliverable — the single step a discharger takes at the
  hand-over.

The residual cost is then exactly zero **on the canonical witness**,
and that is not an accident: `castCols` re-indexes through
`Fin.cast`, which preserves `.val`, and `chanTab` reads its column
argument *only* through `.val`. `cast_val_table` records this, and
`chanTabChild_castCols` is the concrete instance the discharger uses.
An `htabF` that inspected its `Fin` argument any other way would pay
a real transport here — which is the second reason `chanTab` is the
right witness.

## §5–§6 What the pins buy

* **`hhtab` is discharged.** `childLoad_of_parts` /
  `childLoadAll_of_parts` / `centrePrepAll_of_parts`
  (`SolveMachPrep` §4–§6) each carry the seam hypothesis
  `htabF (j+1) (childArena …) = chanF j A u` as an assumption. At the
  witness it is `rfl` (`chanTab_hhtab`), so
  `centrePrepAll_of_parts_chanTab` concludes **verbatim
  `CentrePrepAll`** from the parts residual alone, with no seam
  hypothesis left.
* **The batch is a scan of a region the machine holds.**
  `mem_batchSet_iff_chanRow` is `SolveMachPrepRun`'s
  `mem_batchSet_iff_restrictHist` with both of its hypotheses supplied
  by the pins, so §5 line 19 now reads off `htabF j A` — the very
  table `BlockPre` puts in the level's channel region.
* **The supports column is named.** `roundCol` is the
  `Fin (ℓp (j+1))` index the one `supportsCom_specW` call writes; its
  value is `A.hist.length = j`, and `childChan` patches exactly there
  (`childChan_roundCol`).

## §8 The cluster-row copy (the first of the three missing programs)

`ClusterCsr.read_row` (`SolveChainCover` §3) is a *lemma* about the
cover stage's output; **`clusterRowCom`** is the loop that turns row
`u` of it into `restrictCom_specW`'s `ClusterList` scratch, and
**`clusterRowCom_spec`** is its contract: `ClusterList la (Xf u)` and
the cell `ck = |X_u|` out, three scalars and one array written, no
reallocation. Budget `clusterRowK k = 14·k + 16`, which
`clusterRowK_le_restrictK` shows is **absorbed by `restrictK`'s own
per-member charge of 132** — the glue adds no term to `prepStageK`, and
in particular no `A.N` term (§6.1's `Θ(A.N²)` trap).

## §9 What the batch builder must hit

Not the builder itself, but the three facts its loops close against,
each of which was unstated:

* **`WidthPin`**, witnessed at the campaign setup
  (`headlineSetup_widthPin`, off `Driver.mkSetup_width_le`) — so under
  the pins the batch fits the isolation palette
  (`batchSet_ncard_le_width`).
* **`range_batchFn_eq_batchSet`** — the pad is then exact, so
  `isolateCom_specW`'s `W = Set.range batchFn` and the scan's own
  `batchSet` are the *same set*. **One bit region serves both stages.**
* **`batchFn_eq_centre_of_le_ncard`** — the pad loop's postcondition,
  the half `SolveMachPrepRun.batchFn_eq_of_ncard_lt` does not cover; the
  two together pin all `S.width` slots.
* **`BatchWidthScr`** — `profilesCom_specW` asks for the index region at
  length *exactly* `S.width` and the frame clause forbids reallocation,
  so the length must arrive with the state. This is the clause the
  level's scratch descriptor must carry, and it is length-only
  (`hscrLen_and_batchWidth`), so carrying it is free.

## What remains

The two remaining programs: the **batch builder** (the channel-row scan
that marks the bit region, then the carrier scan that fills the index
region — the loop invariants are `mem_batchSet_iff_chanRow_level`,
`batchFn_eq_of_ncard_lt` and `batchFn_eq_centre_of_le_ncard`), and the
**colour-region writer** assembling `machChild.col` over the `isoPal`
layout. Nothing semantic blocks either; §1–§6 removed the last *stated*
obstruction, which was that no landed object connected `htabF` to
`A.chan`.

## Hazards honoured

* Profiles are measured in **`preG`, before isolation** — nothing here
  moves the batch past `restrict`; §5 is stated at `MArena.restrict`'s
  output.
* **Supports runs at radius `2R`** — `chanBound S = 2 * S.R + 1` is
  the row bound of a `2R` gradient walk, and `prepAdm_child` closes it
  through `childChan_length_le`, never at `S.R`.
* **Inherit-and-patch, one BFS** — `roundCol` is a *single* column
  index, `A.hist.length`; every older column is `restrict`'s filter.
* **`deleteVerts` isolates, it does not remove** — `castCols`
  commutes with `MArena.isolate` on the nose, carrier included.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3.ColoredGraphs
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The channel pin -/

/-- **The channel pin**: the level's channel table — `ProgDriver`'s free
parameter `htabF`, the table `BlockPre` puts in the machine's channel
region — *is* the arena's channel field on the rounds that carry data.
Below `hist.length` there is a round; the columns beyond are padding and
are never read (`DriverArena`, the `chan` field's docstring). -/
def ChanPin (S : Setup L) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)) : Prop :=
  ∀ (j : ℕ) (A : Arena (S.pal j) n₀) (v : Fin A.N) (e : Fin (ℓp j)),
    (e : ℕ) < A.hist.length → htabF j A v e = A.chan v (e : ℕ)

/-- **The witness**: the channel table *is* the channel field, read at
the column's numeral. The types line up by construction —
`htabF`'s target is `Fin (ℓp j) → List (Fin A.N)` and `A.chan`'s is
`ℕ → List (Fin A.N)` — so this is a definition F7 can simply make. -/
def chanTab (S : Setup L) (ℓp : ℕ → ℕ) :
    (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N) :=
  fun _ A v e => A.chan v (e : ℕ)

/-- The witness satisfies the pin — by `rfl`, and without the
round guard: `chanTab` agrees with the channel on *every* column, the
padding included. -/
theorem chanTab_apply (S : Setup L) (ℓp : ℕ → ℕ) (j : ℕ)
    (A : Arena (S.pal j) n₀) (v : Fin A.N) (e : Fin (ℓp j)) :
    chanTab (n₀ := n₀) S ℓp j A v e = A.chan v (e : ℕ) := rfl

/-- **The channel pin, witnessed.** -/
theorem chanTab_chanPin (S : Setup L) (ℓp : ℕ → ℕ) :
    ChanPin (n₀ := n₀) S ℓp (chanTab S ℓp) := fun _ _ _ _ _ => rfl

/-! ## §2 The round-count pin -/

/-- **The round-count pin**: an admissible level-`j` arena has run
exactly `j` rounds. A scan of the channel columns needs a compile-time
column count, and `j` — the level constant of the static layout — is
it. -/
def RoundPin (S : Setup L)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop) : Prop :=
  ∀ (j : ℕ) (A : Arena (S.pal j) n₀), Adm j A → A.hist.length = j

/-- The pin is monotone in the admissibility predicate: F7 may conjoin
whatever else it needs onto the witness without losing the pin. -/
theorem roundPin_mono (S : Setup L)
    {Adm Adm' : (j : ℕ) → Arena (S.pal j) n₀ → Prop}
    (hmono : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), Adm' j A → Adm j A)
    (h : RoundPin S Adm) : RoundPin S Adm' :=
  fun j A hA => h j A (hmono j A hA)

/-- **The witness**: the round count is the level, and every stored
channel row fits the `2R + 1` schedule bound (§4 — the bound the
channel region's stride `hb + 1` is sized by, `HistArr`). Both clauses
are needed together: the second is what makes `chanBound` an honest
region width for the first. -/
def prepAdm (S : Setup L) : (j : ℕ) → Arena (S.pal j) n₀ → Prop :=
  fun j A => A.hist.length = j ∧
    ∀ (v : Fin A.N) (e : ℕ), (A.chan v e).length ≤ 2 * S.R + 1

/-- **The round-count pin, witnessed.** -/
theorem prepAdm_roundPin (S : Setup L) :
    RoundPin (n₀ := n₀) S (prepAdm S) := fun _ _ h => h.1

/-- The witness at the root (§5 line 2): no rounds yet, empty rows. -/
theorem prepAdm_root (S : Setup L) {n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) : prepAdm (n₀ := n) S 0 (rootArena G col) :=
  ⟨rfl, fun _ _ => Nat.zero_le _⟩

/-- The witness is **preserved by the driver's own child step**: the
child appends one round (`childArena_hist`), and its channel rows fit
`2R + 1` because the patched column is a `2R` gradient walk and the
inherited ones are filtered parent rows (`childChan_length_le`). So the
pin is not a hypothesis nobody can meet — it holds along the recursion
the chain actually runs. -/
theorem prepAdm_child (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (h : prepAdm S j A) :
    prepAdm S (j + 1) (childArena S A π u) := by
  refine ⟨?_, ?_⟩
  · show ((A.up u, SimpleGraph.map A.up A.G) :: A.hist).length = j + 1
    rw [List.length_cons, h.1]
  · intro a e
    exact childChan_length_le S A π u h.2 a e

/-- The step in the shape `SolveStep`'s `hAdmChild` consumes. -/
theorem prepAdm_admChild (S : Setup L) (ord : CoverSpec.OrderingRoutine) :
    ∀ (j : ℕ) (A : Arena (S.pal j) n₀), prepAdm S j A → ¬ A.G = ⊥ →
      ∀ u : Fin A.N,
        prepAdm S (j + 1) (childArena S A ((ord A.N A.G).order) u) :=
  fun j A h _ u => prepAdm_child S j A _ u h

/-! ## §3 The column and width pins -/

/-- **The column pin**: the static layout gives every level the same
channel column count. (`restrictCom_specW` and the three stages after
it all return at the *parent's* `ℓp`; §4 prices what closing the gap
costs.) -/
def ColPin (ℓp : ℕ → ℕ) : Prop := ∀ j : ℕ, ℓp (j + 1) = ℓp j

/-- **The width pin**: likewise for the channel row bound `hb`. -/
def BoundPin (hbf : ℕ → ℕ) : Prop := ∀ j : ℕ, hbf (j + 1) = hbf j

/-- **The room pin**: this round's column index — `A.hist.length`, the
one column `supportsCom_specW` writes — is a legal column of the
child's channel region. -/
def RoomPin (S : Setup L) (ℓp : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop) : Prop :=
  ∀ (j : ℕ) (A : Arena (S.pal j) n₀), j < S.depth → Adm j A →
    A.hist.length < ℓp (j + 1)

/-- **The fit pin**: every column that carries a round is a legal
column of this level's own region — `mem_batchSet_iff_restrictHist`'s
`hlen`. -/
def FitPin (S : Setup L) (ℓp : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop) : Prop :=
  ∀ (j : ℕ) (A : Arena (S.pal j) n₀), j ≤ S.depth → Adm j A →
    A.hist.length ≤ ℓp j

/-- **The witness for `ℓp`**: one column per round the chain can run,
plus the round the deepest level still writes. -/
def colCount (S : Setup L) : ℕ → ℕ := fun _ => S.depth + 1

/-- **The witness for `hbf`**: §4's row bound, the length of a `2R`
gradient walk's support. -/
def chanBound (S : Setup L) : ℕ → ℕ := fun _ => 2 * S.R + 1

theorem colCount_colPin (S : Setup L) : ColPin (colCount S) := fun _ => rfl

theorem chanBound_boundPin (S : Setup L) : BoundPin (chanBound S) :=
  fun _ => rfl

theorem colCount_roomPin (S : Setup L) :
    RoomPin (n₀ := n₀) S (colCount S) (prepAdm S) := by
  intro j A hj hAdm
  show A.hist.length < S.depth + 1
  rw [hAdm.1]
  omega

theorem colCount_fitPin (S : Setup L) :
    FitPin (n₀ := n₀) S (colCount S) (prepAdm S) := by
  intro j A hj hAdm
  show A.hist.length ≤ S.depth + 1
  rw [hAdm.1]
  omega

/-- **The channel row bound, at the witness table**: `HistArr`'s own
clause `(hist v p).length ≤ hb`, discharged for `chanTab` from the
admissibility witness. Without this the width pin would be a promise
the region could not keep. -/
theorem chanTab_length_le (S : Setup L) (ℓp : ℕ → ℕ) (j : ℕ)
    {A : Arena (S.pal j) n₀} (hAdm : prepAdm S j A) (v : Fin A.N)
    (e : Fin (ℓp j)) :
    (chanTab (n₀ := n₀) S ℓp j A v e).length ≤ chanBound S j :=
  hAdm.2 v (e : ℕ)

/-- **The five pins, bundled.** -/
structure PrepPins (S : Setup L) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop) : Prop where
  /-- The level's channel table is the arena's channel field. -/
  chan : ChanPin S ℓp htabF
  /-- An admissible level-`j` arena has run exactly `j` rounds. -/
  round : RoundPin S Adm
  /-- One column count for every level. -/
  col : ColPin ℓp
  /-- One row bound for every level. -/
  bound : BoundPin hbf
  /-- This round's column fits the child's region. -/
  room : RoomPin S ℓp Adm
  /-- Every round's column fits this level's region. -/
  fit : FitPin S ℓp Adm

/-- **The bundle, witnessed** — the deliverable of §1–§3: the pins are
jointly satisfiable, at an instantiation the driver's own recursion
preserves (`prepAdm_root`, `prepAdm_child`) and whose row bound the
region really can hold (`chanTab_length_le`). -/
theorem stdPins (S : Setup L) :
    PrepPins (n₀ := n₀) S (colCount S) (chanTab S (colCount S))
      (chanBound S) (prepAdm S) where
  chan := chanTab_chanPin S (colCount S)
  round := prepAdm_roundPin S
  col := colCount_colPin S
  bound := chanBound_boundPin S
  room := colCount_roomPin S
  fit := colCount_fitPin S

/-! ## §4 The cast on a `Fin (ℓp ·)`-indexed family -/

/-- **The re-indexing the column pin costs.** `MArena`'s `hist` field
is indexed by `Fin ℓp`, so `ℓp (j+1) = ℓp j` cannot be discharged by a
rewrite: something must transport. This is that something — *not*
`h ▸ A` on the whole structure (which no later `rfl` would see
through), but the field-level re-index. The other four fields are
literally the same terms. -/
def castCols {Λ nr p q : ℕ} (h : p = q) (A : Impl.MArena Λ nr p) :
    Impl.MArena Λ nr q :=
  ⟨A.N, A.G, A.col, A.up, fun v e => A.hist v (Fin.cast h.symm e)⟩

section Cast

variable {Λ nr p q : ℕ}

@[simp] theorem castCols_N (h : p = q) (A : Impl.MArena Λ nr p) :
    (castCols h A).N = A.N := rfl

@[simp] theorem castCols_G (h : p = q) (A : Impl.MArena Λ nr p) :
    (castCols h A).G = A.G := rfl

@[simp] theorem castCols_col (h : p = q) (A : Impl.MArena Λ nr p) :
    (castCols h A).col = A.col := rfl

@[simp] theorem castCols_up (h : p = q) (A : Impl.MArena Λ nr p) :
    (castCols h A).up = A.up := rfl

@[simp] theorem castCols_hist (h : p = q) (A : Impl.MArena Λ nr p)
    (v : Fin A.N) (e : Fin q) :
    (castCols h A).hist v e = A.hist v (Fin.cast h.symm e) := rfl

/-- The cast at a trivial equation is the identity — the fact that
makes every commutation below discharge by `subst`. -/
@[simp] theorem castCols_rfl (A : Impl.MArena Λ nr p) :
    castCols rfl A = A := rfl

/-- **A `.val`-indexed column table is cast-invariant.** `Fin.cast`
preserves the numeral, so a table that reads its column argument only
through `↑e` — which is exactly what `chanTab` does — passes through
the cast unchanged. This is the reason the column pin costs *nothing*
on the canonical witness, and the reason a witness that inspected its
`Fin` argument otherwise would pay for it here. -/
theorem cast_val_table {N : ℕ} (h : p = q) (f : Fin N → ℕ → List (Fin N)) :
    (fun (v : Fin N) (e : Fin q) => f v ((Fin.cast h.symm e : Fin p) : ℕ))
      = fun (v : Fin N) (e : Fin q) => f v (e : ℕ) := rfl

/-- The cast commutes with `ofArena`, re-indexing the channel table. -/
theorem castCols_ofArena {A : Driver.Arena Λ nr}
    (htab : Fin A.N → Fin p → List (Fin A.N)) (h : p = q) :
    castCols h (Impl.ofArena A htab)
      = Impl.ofArena A (fun v e => htab v (Fin.cast h.symm e)) := rfl

/-- The cast commutes with `restrict` — carrier, graph, colours and
renaming on the nose, the filtered rows re-indexed. -/
theorem castCols_restrict (h : p = q) (A : Impl.MArena Λ nr p)
    (X : Set (Fin A.N)) :
    castCols h (A.restrict X) = (castCols h A).restrict X := rfl

/-- The cast commutes with `isolate`. `deleteVerts` isolates, never
removes: the carrier survives the cast unchanged, so the batch set `W`
is literally the same set on both sides. -/
theorem castCols_isolate (h : p = q) (A : Impl.MArena Λ nr p)
    (W : Set (Fin A.N)) :
    castCols h (A.isolate W) = (castCols h A).isolate W := rfl

/-- The cast commutes with the **supports patch** —
`supportsCom_specW`'s postcondition shape, `{A with hist := fun v p =>
if p = e then … else A.hist v p}`. The written column moves to
`Fin.cast h e`, which has the same numeral, so the one column the pass
writes stays the one column it wrote. -/
theorem castCols_patch (h : p = q) (A : Impl.MArena Λ nr p)
    (e : Fin p) (f : Fin A.N → List (Fin A.N)) :
    castCols h { A with hist := fun v r => if r = e then f v else A.hist v r }
      = { castCols h A with
          hist := fun v r => if r = Fin.cast h e then f v else
            (castCols h A).hist v r } := by
  subst h
  rfl

/-- **`ArenaStW` transports across the cast.** The windowed contract
reads the `hist` family only through `HistArr`'s offsets, which are
computed from `ℓp` and the column's numeral; the cast changes neither.
This is the whole of what the column pin costs a discharger: one
application of this lemma at the hand-over. -/
theorem arenaStW_castCols {nm : ArenaNames} {hb : ℕ} (h : p = q)
    (A : Impl.MArena Λ nr p) {σ : Env} (hA : ArenaStW nm hb A σ) :
    ArenaStW nm hb (castCols h A) σ := by
  subst h
  exact hA

/-- The converse direction, for reading a cast contract back. -/
theorem arenaStW_of_castCols {nm : ArenaNames} {hb : ℕ} (h : p = q)
    (A : Impl.MArena Λ nr p) {σ : Env}
    (hA : ArenaStW nm hb (castCols h A) σ) : ArenaStW nm hb A σ := by
  subst h
  exact hA

end Cast

/-- The cast at `machChild`: the assembled child at the parent's column
count becomes the assembled child at the level's, with the channel
re-indexed and nothing else moved. -/
theorem machChild_castCols (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {p q : ℕ} (h : p = q)
    (Dp : Fin S.width → Fin (childN S A π u) → ℕ)
    (Dc : Fin (relPal Λ) → Fin (childN S A π u + 1) → ℕ)
    (chan : Fin (childN S A π u) → Fin p → List (Fin (childN S A π u))) :
    castCols h (machChild S A π u Dp Dc chan)
      = machChild S A π u Dp Dc
          (fun v e => chan v (Fin.cast h.symm e)) := rfl

/-- **The hand-over, concretely**: the whole of what the column pin
costs a discharger. The stages assemble the machine child at the
*parent's* column count `ℓp j` (that is what `restrictCom_specW`,
`supportsCom_specW` and `isolateCom_specW` all return); the
`ChildLoadParts` deliverable is stated at `ℓp (j+1)`. One application
of this lemma moves between them, re-indexing the channel and moving
nothing else. -/
theorem arenaStW_machChild_cast (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {p q : ℕ} (h : q = p)
    {Dp : Fin S.width → Fin (childN S A π u) → ℕ}
    {Dc : Fin (relPal Λ) → Fin (childN S A π u + 1) → ℕ}
    (chan : Fin (childN S A π u) → Fin p → List (Fin (childN S A π u)))
    {nm : ArenaNames} {hb : ℕ} {σ : Env}
    (hst : ArenaStW nm hb (machChild S A π u Dp Dc chan) σ) :
    ArenaStW nm hb
      (machChild S A π u Dp Dc (fun v e => chan v (Fin.cast h e))) σ := by
  subst h
  exact hst

/-! ## §5 The seam hypothesis `hhtab`, discharged -/

open Classical in
/-- **The child's channel table**, at the child's own column type: the
inherit-and-patch channel `Driver.childChan`, read at the column's
numeral. This is `ChildLoadParts`' `chanF` at the witness. -/
noncomputable def chanTabChild (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ) (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)) :=
  fun a e => childChan S A ((ord A.N A.G).order) u a (e : ℕ)

/-- **The seam hypothesis, discharged.** `childLoad_of_parts`,
`childLoadAll_of_parts` and `centrePrepAll_of_parts` each assume
`htabF (j+1) (childArena …) = chanF j A u`, F7-suppliable "by
construction". At the witness it is `rfl` — the construction is
`chanTab`, and the child's channel field *is* `childChan`
(`childArena_chan`). -/
theorem chanTab_hhtab (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ) :
    ∀ (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N),
      chanTab (n₀ := n₀) S ℓp (j + 1)
          (childArena S A ((ord A.N A.G).order) u)
        = chanTabChild S ord ℓp j A u :=
  fun _ _ _ => rfl

/-- The cast, at the child's channel: re-indexing `chanTabChild` from
the parent's column count to the level's is the identity, because the
table is `.val`-indexed (`cast_val_table`). Concretely — this is the
step the discharger takes at the hand-over from `supportsCom_specW`
(which delivers at `ℓp j`) to the `ChildLoadParts` deliverable (stated
at `ℓp (j+1)`). -/
theorem chanTabChild_castCols (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ) (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N)
    (h : ℓp j = ℓp (j + 1)) :
    (fun (a : Fin (childN S A ((ord A.N A.G).order) u))
        (e : Fin (ℓp (j + 1))) =>
      childChan S A ((ord A.N A.G).order) u a
        ((Fin.cast h.symm e : Fin (ℓp j)) : ℕ))
      = chanTabChild S ord ℓp j A u := rfl

open Classical in
/-- **The hand-over at the witness**, in one step: the machine child
assembled at the parent's column count, with its channel the
inherit-and-patch table read at the column's numeral, *is* the
`ChildLoadParts` deliverable's arena at `ℓp (j+1)`. The cast is
invisible (`cast_val_table`), so the discharger pays nothing beyond
naming this lemma. -/
theorem arenaStW_machChild_chanTabChild (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ) (j : ℕ)
    (A : Arena (S.pal j) n₀) (u : Fin A.N) (hcol : ℓp (j + 1) = ℓp j)
    {Dp : Fin S.width →
      Fin (childN S A ((ord A.N A.G).order) u) → ℕ}
    {Dc : Fin (relPal (S.pal j)) →
      Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ}
    {nm : ArenaNames} {hb : ℕ} {σ : Env}
    (hst : ArenaStW nm hb
      (machChild S A ((ord A.N A.G).order) u Dp Dc
        (fun a (e : Fin (ℓp j)) =>
          childChan S A ((ord A.N A.G).order) u a (e : ℕ))) σ) :
    ArenaStW nm hb
      (machChild S A ((ord A.N A.G).order) u Dp Dc
        (chanTabChild S ord ℓp j A u)) σ :=
  arenaStW_machChild_cast S A _ u hcol _ hst

/-! ## §6 What the pins buy the batch scan -/

section Payoff

variable (S : Setup L) (ℓp : ℕ → ℕ)
  (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
    Fin A.N → Fin (ℓp j) → List (Fin A.N))
  (hbf : ℕ → ℕ) (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)

open Classical in
/-- **§5 line 19, at the level's own channel region.**
`SolveMachPrepRun.mem_batchSet_iff_restrictHist` needed two
hypotheses — that the region holds the driver's channel, and that the
arena has no more rounds than the region has columns. Both are pins,
so under `PrepPins` the batch is a scan of `htabF j A`: the table
`BlockPre` puts in the machine's channel region, restricted to the
cluster and read at row `centreChild`. This is the statement the batch
builder's loop invariant consumes. -/
theorem mem_batchSet_iff_chanRow
    (hp : PrepPins S ℓp htabF hbf Adm) (j : ℕ) (A : Arena (S.pal j) n₀)
    (hj : j ≤ S.depth) (hAdm : Adm j A) (π : Equiv.Perm (Fin A.N))
    (u : Fin A.N) (a : Fin (childN S A π u)) :
    a ∈ batchSet S A π u ↔
      a = centreChild S A π u ∨
        ∃ e : Fin (ℓp j), (e : ℕ) < A.hist.length ∧
          a ∈ ((Impl.ofArena A (htabF j A)).restrict (cluster S A π u)).hist
                (centreChild S A π u) e :=
  mem_batchSet_iff_restrictHist S A π u (htabF j A) (hp.fit j A hj hAdm)
    (fun v e he => hp.chan j A v e he) a

/-- The same, with the round count spelled out as the level: the scan
runs over columns `0, …, j-1`, a compile-time range. -/
theorem mem_batchSet_iff_chanRow_level
    (hp : PrepPins S ℓp htabF hbf Adm) (j : ℕ) (A : Arena (S.pal j) n₀)
    (hj : j ≤ S.depth) (hAdm : Adm j A) (π : Equiv.Perm (Fin A.N))
    (u : Fin A.N) (a : Fin (childN S A π u)) :
    a ∈ batchSet S A π u ↔
      a = centreChild S A π u ∨
        ∃ e : Fin (ℓp j), (e : ℕ) < j ∧
          a ∈ ((Impl.ofArena A (htabF j A)).restrict (cluster S A π u)).hist
                (centreChild S A π u) e := by
  rw [mem_batchSet_iff_chanRow S ℓp htabF hbf Adm hp j A hj hAdm π u a,
    hp.round j A hAdm]

/-- **This round's column**, as a legal index of the child's channel
region: `A.hist.length`, the one column `supportsCom_specW` writes.
Inherit-and-patch — there is exactly one. -/
def roundCol (hp : PrepPins S ℓp htabF hbf Adm) (j : ℕ)
    (A : Arena (S.pal j) n₀) (hj : j < S.depth) (hAdm : Adm j A) :
    Fin (ℓp (j + 1)) :=
  ⟨A.hist.length, hp.room j A hj hAdm⟩

@[simp] theorem roundCol_val (hp : PrepPins S ℓp htabF hbf Adm) (j : ℕ)
    (A : Arena (S.pal j) n₀) (hj : j < S.depth) (hAdm : Adm j A) :
    ((roundCol S ℓp htabF hbf Adm hp j A hj hAdm : Fin (ℓp (j + 1))) : ℕ)
      = A.hist.length := rfl

/-- The column index is the level — the compile-time constant the
static layout can emit. -/
theorem roundCol_eq_level (hp : PrepPins S ℓp htabF hbf Adm) (j : ℕ)
    (A : Arena (S.pal j) n₀) (hj : j < S.depth) (hAdm : Adm j A) :
    ((roundCol S ℓp htabF hbf Adm hp j A hj hAdm : Fin (ℓp (j + 1))) : ℕ)
      = j :=
  hp.round j A hAdm

open Classical in
/-- **The patch lands on `roundCol`**: the child's channel at this
round's column is the `2R` gradient-walk table, verbatim
`supportsCom_specW`'s deliverable at `d = 2 * S.R`. Every other column
is the parent's row filtered onto the cluster (`childChan_old`). -/
theorem childChan_roundCol (hp : PrepPins S ℓp htabF hbf Adm) (j : ℕ)
    (A : Arena (S.pal j) n₀) (hj : j < S.depth) (hAdm : Adm j A)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (a : Fin (childN S A π u)) :
    childChan S A π u a
        ((roundCol S ℓp htabF hbf Adm hp j A hj hAdm : Fin (ℓp (j + 1))) : ℕ)
      = descendCol (preG S A π u) (childDist S A π u) (2 * S.R) a :=
  childChan_new S A π u a

end Payoff

/-! ## §7 The headline: `CentrePrepAll` with the seam removed -/

open Classical in
/-- **Verbatim `CentrePrepAll` from the parts, seam discharged.**
`SolveMachPrep.centrePrepAll_of_parts` carries `hhtab` as a hypothesis;
at the canonical witness the hypothesis is `rfl`, so the prep segment's
whole remaining obligation is `ChildLoadPartsAll` — the stage
composition and the three programs, with nothing left to *state*. -/
theorem centrePrepAll_of_parts_chanTab (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ) (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hscrDown : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ σ, Scr j σ → Scr (j + 1) σ)
    (htabLen : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → ∀ σ,
      Scr j σ →
      n * (levelFml (Headline.headlineSetup C hC φ) (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hparts : ChildLoadPartsAll C hC φ ord G c w q ℓp
      (chanTab (Headline.headlineSetup C hC φ) ℓp) hbf Adm Scr ca co cm prepC
      (chanTabChild (Headline.headlineSetup C hC φ) ord ℓp) KP) :
    CentrePrepAll C hC φ ord G c w q ℓp
      (chanTab (Headline.headlineSetup C hC φ) ℓp) hbf Adm Scr ca co cm
      prepC KP :=
  centrePrepAll_of_parts C hC φ ord G c w q ℓp
    (chanTab (Headline.headlineSetup C hC φ) ℓp) hbf Adm Scr ca co cm prepC
    (chanTabChild (Headline.headlineSetup C hC φ) ord ℓp) KP hscrLen hscrDown
    htabLen (chanTab_hhtab (Headline.headlineSetup C hC φ) ord ℓp) hparts

/-! ## §8 Part 2, item 1: the cluster-row copy -/

section ClusterRow

private theorem getD_set_self' {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem getD_set_of_ne' {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c).getD q 0 = l.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
    List.getD_eq_getElem?_getD]

private theorem getElem?_of_lt' (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- **The cluster-row copy** — the first of the three programs
`SolveMachPrepRun` left unwritten. `ClusterCsr.read_row`
(`SolveChainCover` §3) is a *lemma* about the cover stage's output; this
is the loop that turns row `u` of that output into
`restrictCom_specW`'s `ClusterList` scratch. Base and length off the
offset array (`cb := co[u]`, `ck := co[u+1] - cb`), then `|X_u|` cells
copied left to right. -/
def clusterRowCom (co cm la cu cb ck ct : String) : Com :=
  .seq (.assign cb (.get co (.var cu)))
    (.seq (.assign ck (.sub (.get co (.add (.var cu) (.lit 1))) (.var cb)))
      (.seq (.assign ct (.lit 0))
        (.while (.lt (.var ct) (.var ck))
          (.seq (.store la (.var ct) (.get cm (.add (.var cb) (.var ct))))
            (.assign ct (.add (.var ct) (.lit 1)))))))

/-- The copy's budget: ten words per cell — a store of a two-level
expression and a bump — plus the loop's own four per turn, plus the
prologue's two assignments and the counter's initialisation. -/
def clusterRowK (k : ℕ) : ℕ := 14 * k + 16

/-- **The copy's budget is absorbed by the restrict stage's own
column.** `restrictK` already charges `132` per cluster member; the
copy charges `14`. So the glue introduces **no new term** into
`prepStageK` — in particular no `A.N` term, the `Θ(A.N²)` trap §6.1's
scratch paragraph warns about. -/
theorem clusterRowK_le_restrictK (dS k Λc ℓp hb : ℕ) :
    clusterRowK k ≤ restrictK dS k Λc ℓp hb := by
  have h : 14 * k ≤ k * (20 * Λc + (36 * hb + 42) * ℓp + 132) := by
    have : k * 14 ≤ k * (20 * Λc + (36 * hb + 42) * ℓp + 132) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  unfold clusterRowK restrictK
  omega

/-- The same against the pass's whole budget. -/
theorem clusterRowK_le_prepStageK (cN cns dS k Λc ℓp hb mb R : ℕ) :
    clusterRowK k ≤ prepStageK cN cns dS k Λc ℓp hb mb R := by
  have h := clusterRowK_le_restrictK dS k Λc ℓp hb
  unfold prepStageK
  omega

open Classical in
/-- **The cluster-row copy, specified.** From the cover stage's output
(`ClusterCsr` at the cluster family), the centre in `cu`, and a scratch
allocation of at least the row's length, the copy leaves
`restrictCom_specW`'s two preconditions verbatim — `ClusterList la (Xf u)`
and the cell `ck = |X_u|` — plus the frame: three scalars and one array
written, no reallocation.

The word bound asked of the caller is the cover output's own: every
offset the routine reads fits a word. Everything else rides `N < B`.

Budget `clusterRowK |X_u|`, absorbed by `restrictK`
(`clusterRowK_le_restrictK`). -/
theorem clusterRowCom_spec {B N : ℕ} {Xf : Fin N → Set (Fin N)}
    {co cm la cu cb ck ct : String} (u : Fin N) (hNB : N < B)
    (hla_cm : la ≠ cm) (hct_ck : ct ≠ ck) (hct_cb : ct ≠ cb)
    (hcb_ck : cb ≠ ck) (hcu_cb : cu ≠ cb) :
    Spec B
      (fun σ => ClusterCsr co cm Xf σ ∧ σ.vars cu = (u : ℕ) ∧
        (Xf u).ncard ≤ (σ.arrs la).length ∧
        (∀ i, i ≤ N → (σ.arrs co).getD i 0 < B))
      (clusterRowCom co cm la cu cb ck ct)
      (fun σ σ' => ClusterList la (Xf u) σ' ∧ σ'.vars ck = (Xf u).ncard ∧
        (∀ y, y ≠ cb → y ≠ ck → y ≠ ct → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ la → σ'.arrs a = σ.arrs a) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (clusterRowK (Xf u).ncard) := by
  intro σ hσ
  obtain ⟨hcsr, hcu, hlaL, hcoB⟩ := hσ
  -- the row, from the landed reading lemma
  obtain ⟨base, hbaseL, hbaseGet, hrow⟩ := ClusterCsr.read_row hcsr u
  obtain ⟨offC, -, hcoL, hco, hstep, -, -⟩ := hcsr
  set k : ℕ := (Xf u).ncard with hk_def
  have huN : (u : ℕ) < N := u.2
  have hB1 : 1 < B := by omega
  -- the two offsets, and their word bounds
  have hbase_eq : base = offC (u : ℕ) := by
    rw [← hbaseGet, hco (u : ℕ) (le_of_lt huN)]
  have hnextGet : (σ.arrs co).getD ((u : ℕ) + 1) 0 = base + k := by
    rw [hco ((u : ℕ) + 1) (by omega), hstep u, hbase_eq]
  have hbaseB : base < B := by
    rw [← hbaseGet]; exact hcoB (u : ℕ) (le_of_lt huN)
  have hsumB : base + k < B := by
    rw [← hnextGet]; exact hcoB ((u : ℕ) + 1) (by omega)
  -- the array lengths the reads need
  have hcoLen : (u : ℕ) + 1 < (σ.arrs co).length := by omega
  -- the loop invariant
  set I : Env → Prop := fun τ =>
    τ.vars ck = k ∧ τ.vars cb = base ∧ τ.arrs cm = σ.arrs cm ∧
      τ.vars ct ≤ k ∧ k ≤ (τ.arrs la).length ∧
      ∀ t, t < τ.vars ct →
        (τ.arrs la).getD t 0 = (σ.arrs cm).getD (base + t) 0 with hI_def
  -- the body: one cell copied, the counter bumped
  have hbody : Spec B (fun τ => I τ ∧ τ.vars ct < k)
      (.seq (.store la (.var ct) (.get cm (.add (.var cb) (.var ct))))
        (.assign ct (.add (.var ct) (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars ct = τ.vars ct + 1) 10 := by
    rintro τ ⟨⟨hck, hcb, hcmE, hle, hlaLen, hcells⟩, hlt⟩
    set t : ℕ := τ.vars ct with ht_def
    set v : ℕ := (σ.arrs cm).getD (base + t) 0 with hv_def
    have hvEmb : v = (Impl.restrictEmb (Xf u) ⟨t, hlt⟩ : Fin N) := hrow t hlt
    have hvB : v < B := by
      rw [hvEmb]
      exact lt_trans (Impl.restrictEmb (Xf u) ⟨t, hlt⟩).2 hNB
    have hidxLen : base + t < (σ.arrs cm).length := by omega
    -- the index expression, at the row's base
    have hidxE : (Expr.add (Expr.var cb) (Expr.var ct)).evalB B τ
        = some (base + t) := by
      have h1 : (Expr.var cb).evalB B τ = some base := by
        have hb : τ.vars cb < B := by rw [hcb]; omega
        simpa [hcb] using evalB_var (x := cb) (σ := τ) hb
      have h2 : (Expr.var ct).evalB B τ = some t :=
        evalB_var (x := ct) (σ := τ) (by omega)
      simpa using
        evalB_bin (op := .add) h1 h2 (by simpa using (by omega : base + t < B))
    -- the store
    have hrun1 : Run B
        (.store la (.var ct) (.get cm (.add (.var cb) (.var ct)))) τ
        (τ.setArr la t v) 6 :=
      Run.store (evalB_var (by omega))
        (evalB_get hidxE
          (by rw [hcmE]; exact getElem?_of_lt' _ _ hidxLen) hvB)
        (by omega)
    -- the bump
    have hrun2 : Run B (.assign ct (.add (.var ct) (.lit 1)))
        (τ.setArr la t v)
        ((τ.setArr la t v).setVar ct (t + 1)) 4 := by
      have hb : (Expr.bin .add (.var ct) (.lit 1)).evalB B (τ.setArr la t v)
          = some (t + 1) := by
        refine evalB_bin (evalB_var ?_) (evalB_lit hB1) (by simpa using (by omega : t + 1 < B))
        rw [vars_setArr]; omega
      have := Run.assign (x := ct) hb
      simpa using this
    refine ⟨_, (hrun1.seq hrun2).mono (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hct_ck), vars_setArr]; exact hck
    · rw [vars_setVar, if_neg (Ne.symm hct_cb), vars_setArr]; exact hcb
    · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hla_cm)]; exact hcmE
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, List.length_set]; exact hlaLen
    · intro t' ht'
      rw [vars_setVar, if_pos rfl] at ht'
      rw [arrs_setVar, arrs_setArr, if_pos rfl]
      rcases Nat.lt_or_ge t' t with hlt' | hge'
      · rw [getD_set_of_ne' (by omega)]
        exact hcells t' (by omega)
      · obtain rfl : t' = t := by omega
        rw [getD_set_self' (by omega)]
    · rw [vars_setVar, if_pos rfl]
  -- the loop
  have hloop := Spec.forRangeZero (B := B) ct ck I k 10 (by omega)
    (fun _ hτ => hτ.2.2.2.1) (fun _ hτ => hτ.1) hbody
  -- the prologue: `cb := co[u]`
  have hrunA : Run B (.assign cb (.get co (.var cu))) σ (σ.setVar cb base) 3 := by
    have h : (Expr.get co (.var cu)).evalB B σ = some base := by
      refine evalB_get (evalB_var (by omega)) ?_ hbaseB
      rw [hcu, ← hbaseGet]
      exact getElem?_of_lt' _ _ (by omega)
    simpa using Run.assign (x := cb) h
  -- the prologue: `ck := co[u+1] - cb`
  set σ1 : Env := σ.setVar cb base with hσ1_def
  have hrunB : Run B
      (.assign ck (.sub (.get co (.add (.var cu) (.lit 1))) (.var cb))) σ1
      (σ1.setVar ck k) 7 := by
    have hcu1 : σ1.vars cu = (u : ℕ) := by
      rw [hσ1_def, vars_setVar, if_neg hcu_cb]; exact hcu
    have hco1 : σ1.arrs co = σ.arrs co := by rw [hσ1_def, arrs_setVar]
    have hcb1 : σ1.vars cb = base := by rw [hσ1_def, vars_setVar, if_pos rfl]
    have hidxE : (Expr.add (Expr.var cu) (Expr.lit 1)).evalB B σ1
        = some ((u : ℕ) + 1) := by
      have h1 : (Expr.var cu).evalB B σ1 = some (u : ℕ) := by
        have hb : σ1.vars cu < B := by rw [hcu1]; omega
        simpa [hcu1] using evalB_var (x := cu) (σ := σ1) hb
      simpa using
        evalB_bin (op := .add) h1 (evalB_lit (σ := σ1) hB1)
          (by simpa using (by omega : (u : ℕ) + 1 < B))
    have hget : (Expr.get co (.add (.var cu) (.lit 1))).evalB B σ1
        = some (base + k) := by
      refine evalB_get hidxE ?_ hsumB
      rw [hco1, ← hnextGet]
      exact getElem?_of_lt' _ _ hcoLen
    have h : (Expr.sub (.get co (.add (.var cu) (.lit 1))) (.var cb)).evalB B σ1
        = some k := by
      have := evalB_bin (op := .sub) hget (evalB_var (by rw [hcb1]; omega))
        (by rw [hcb1]; simpa using (by omega : base + k - base < B))
      rw [hcb1] at this
      simpa using this
    simpa using Run.assign (x := ck) h
  -- the loop runs from the prologue's exit
  set σ2 : Env := σ1.setVar ck k with hσ2_def
  have hIinit : I (σ2.setVar ct 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg (Ne.symm hct_ck), hσ2_def, vars_setVar, if_pos rfl]
    · rw [vars_setVar, if_neg (Ne.symm hct_cb), hσ2_def, vars_setVar,
        if_neg hcb_ck, hσ1_def, vars_setVar, if_pos rfl]
    · rw [arrs_setVar, hσ2_def, arrs_setVar, hσ1_def, arrs_setVar]
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [arrs_setVar, hσ2_def, arrs_setVar, hσ1_def, arrs_setVar]; exact hlaL
    · intro t ht
      rw [vars_setVar, if_pos rfl] at ht
      omega
  obtain ⟨σ', hrunC, hIfin, hctfin⟩ := hloop.run hIinit
  -- assemble
  refine ⟨σ', ((hrunA.seq (hrunB.seq hrunC)).mono ?_), ?_, ?_, ?_, ?_, ?_⟩
  · unfold clusterRowK; omega
  · -- the cluster list, at the scratch region
    refine ⟨hIfin.2.2.2.2.1, fun t ht => ?_⟩
    have := hIfin.2.2.2.2.2 t (by rw [hctfin]; exact ht)
    rw [this, hrow t ht]
  · exact hIfin.1
  · intro y h1 h2 h3
    refine (hrunA.seq (hrunB.seq hrunC)).frame_var y ?_
    simp only [Com.wvars, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    tauto
  · intro a ha
    refine (hrunA.seq (hrunB.seq hrunC)).frame_arr a ?_
    simp only [Com.warrs, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · exact run_arrs_length_eq (hrunA.seq (hrunB.seq hrunC))

end ClusterRow

/-! ## §9 Part 2, item 2: what the batch builder must hit -/

/-- **The schedule's width pin** (§3's `m = ℓ(2R+1)`): the batch of any
level the chain runs fits the isolation palette's width. Not an
assumption — `Driver.mkSetup_width_le` proves it of the campaign setup
(`headlineSetup_widthPin`). -/
def WidthPin (S : Setup L) : Prop :=
  ∀ j : ℕ, j < S.depth → 1 + j * (2 * S.R + 1) ≤ S.width

/-- **The width pin, witnessed at the campaign setup.** -/
theorem headlineSetup_widthPin (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) : WidthPin (Headline.headlineSetup C hC φ) :=
  fun _ hj => mkSetup_width_le C hC _ _ _ hj

section Batch

variable (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N))
  (u : Fin A.N)

/-- **The batch fits the width**, under the pins: `batchSet_ncard_le`'s
figure `1 + hist.length·(2R+1)` with the round count read off the
round-count pin and the row bound off the admissibility witness. -/
theorem batchSet_ncard_le_width {j : ℕ} (hw : WidthPin S)
    (hAdm : (A.hist.length = j ∧
      ∀ (v : Fin A.N) (e : ℕ), (A.chan v e).length ≤ 2 * S.R + 1))
    (hj : j < S.depth) : (batchSet S A π u).ncard ≤ S.width := by
  refine (batchSet_ncard_le S A π u hAdm.2).trans ?_
  rw [hAdm.1]
  exact hw j hj

/-- **One bit region serves both stages.** `isolateCom_specW` asks for
`FinBitsW ba (Set.range batchFn)` — that is literally `childArena`'s
`deleteVerts preG (Set.range (batchFn …))` — while the scan of §6
computes `batchSet`. Under the width pin the pad is exact
(`Driver.range_pad`), so the two sets are **the same set**: the builder
writes one bit vector, not two, and the isolation reads the scan's own
output. -/
theorem range_batchFn_eq_batchSet {j : ℕ} (hw : WidthPin S)
    (hAdm : (A.hist.length = j ∧
      ∀ (v : Fin A.N) (e : ℕ), (A.chan v e).length ≤ 2 * S.R + 1))
    (hj : j < S.depth) :
    Set.range (batchFn S A π u) = batchSet S A π u :=
  range_pad (centreChild_mem_batchSet S A π u)
    (batchSet_ncard_le_width S A π u hw hAdm hj)

end Batch

/-- **The pad's tail**, the half `pad_eq_of_ncard_lt` does not cover: a
slot at or beyond the member count holds the designated element. -/
theorem pad_eq_of_le_ncard {k mb : ℕ} {X : Set (Fin k)} {x₀ : Fin k}
    (i : Fin mb) (h : X.ncard ≤ (i : ℕ)) : pad X x₀ i = x₀ := by
  unfold pad
  rw [dif_neg (by omega)]

/-- The same at the batch: once the scan has emitted every member, every
remaining slot of the index region holds the connector's own child name.
This is the pad loop's postcondition — together with
`batchFn_eq_of_ncard_lt` (the scan's own step) it pins every one of the
`S.width` slots. -/
theorem batchFn_eq_centre_of_le_ncard (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (i : Fin S.width)
    (h : (batchSet S A π u).ncard ≤ (i : ℕ)) :
    batchFn S A π u i = centreChild S A π u :=
  pad_eq_of_le_ncard i h

/-! ### The index region's length clause

`profilesCom_specW` asks for the batch region at length **exactly**
`mb = S.width` — an equality, not a `≤` — and `ChildLoadParts`' frame
clause forbids reallocation (`∀ b, (σ'.arrs b).length = (σ.arrs b).length`).
So the length cannot be established by the pass: it has to come in with
the state, which means the level's scratch descriptor `Scr` must carry
it. This is that clause, and the two facts that make carrying it free. -/

/-- **The index region's length clause**: the batch region is allocated
at exactly the schedule's width. -/
def BatchWidthScr (ba : String) (mb : ℕ) (σ : Env) : Prop :=
  (σ.arrs ba).length = mb

/-- It **is** `profilesCom_specW`'s length precondition, verbatim. -/
theorem batchWidthScr_profiles {ba : String} {mb : ℕ} {σ : Env}
    (h : BatchWidthScr ba mb σ) : (σ.arrs ba).length = mb := h

/-- It is **length-only**, so conjoining it onto a descriptor preserves
`centrePrep_of_childLoad`'s `hscrLen` obligation — the clause rides
every pass's frame for free. -/
theorem batchWidthScr_len {ba : String} {mb : ℕ} {σ σ' : Env}
    (h : BatchWidthScr ba mb σ)
    (hlen : ∀ b, (σ'.arrs b).length = (σ.arrs b).length) :
    BatchWidthScr ba mb σ' := by
  rw [BatchWidthScr, hlen ba]
  exact h

/-- The conjunction, at `hscrLen`'s shape. -/
theorem hscrLen_and_batchWidth {ba : String} {mb : ℕ} {Scr : ℕ → Env → Prop}
    (hscr : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ') :
    ∀ (j : ℕ) (σ σ' : Env), (Scr j σ ∧ BatchWidthScr ba mb σ) →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) →
      (Scr j σ' ∧ BatchWidthScr ba mb σ') :=
  fun j σ σ' h hlen => ⟨hscr j σ σ' h.1 hlen, batchWidthScr_len h.2 hlen⟩

end Lax3Proofs.Prog
