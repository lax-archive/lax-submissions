import Lax3Proofs.DriverArena
import Lax3Proofs.CoverEdgeSum
import Lax3Proofs.ImplBfs

/-!
# `restrict` and `isolate` (E12b, §6.1, §4 rows 1–2)

The first two rows of §4's operation table, as concrete functions on a
§4-shaped machine arena, each with the identity to the abstract layer
the driver (`DriverArena`) consumes, and with §6.1's cost statement —
including the one-scratch-array-per-*node* amortization, stated as
explicit state threaded across a node's children.

## §1 The machine arena and `restrict`

`MArena` is §4's structure with the CSR abstracted to a `SimpleGraph`
and, like `Driver.Arena`, the composite renaming to the ROOT carrier in
`up` (E6: the record is never re-typed); `hist` is §4's CORRECTED
per-vertex channel — per vertex and per ancestor round, the `≤ 2R+1`
support names of that round's walk, at the node's own names. (`own` is
not carried, for `DriverArena`'s reason: the writing child is
definitional there.)

`restrict A S` is §6.1: local names `Fin S.ncard` through the sorted
enumeration (`restrictEmb S`, the same `Driver.setEquiv` enumeration the
driver's compaction uses — "rank `S` to get local names"); the induced
graph (`comap` along the enumeration — the CSR built from the kept row
entries); the color rows copied; `up` set to the parent names composed
to the root; and `hist` **filtered** — each stored list intersected with
`S` and renamed local (`toLocal`), sound because carriers are nested
(D6): a support name outside `S` is outside the child's carrier and is
dropped, `restrict_hist_map` says the surviving parent names are exactly
the stored list's intersection with `S`, in order.

**The identities to `DriverArena`**, at `S := Driver.cluster Sch A π u`
(all definitional — E13 plugs this program where the abstract driver
holds its child):

* `restrict_N_eq_childN` — the carrier is `Driver.childN`;
* `restrict_G_eq_preG` — the graph half IS `Driver.preG` (`B₀` of §5
  lines 16/20, the arena the profiles are measured in, before
  isolation);
* `restrict_col_eq_childCol0` — the copied rows are `Driver.childCol0`
  (the marker/profile layers on top of them are E12c's
  `recordProfiles`, not `restrict`'s);
* `restrict_up_eq_childArena_up` — the renaming is `childArena`'s.

## §2 `isolate`

`isolate B W` drops the edges incident to `W`: it IS `deleteVerts B.G W`
(`isolate_G`, definitional) — Lax12's isolation, which keeps the carrier
(`isolate_N`): isolates, never removes. `childArena_G_eq_isolate_restrict`
is §5 line 21 as a program identity:
`(childArena …).G = (isolate (restrict A (cluster …)) (range batchFn)).G`.
The charge is one CSR sweep, `isolateCharge = Σ_v (deg v + 1) = 2M + N ≤
2‖B‖` (`isolateCharge_le_two_gsize`) — §4's `O(‖B‖)`.

## §3 The `restrict` charge and the scratch amortization

§6.1's charge is `O(Σ_{s∈S} deg_A(s) + |S|·(L + ℓ·R))`, and the
membership test rides **one scratch array per node, reused across
children and cleared only at the `|S|` touched entries**. The model:

* The scratch is the machine's parent-name-indexed Boolean array, read
  as the set of `true` entries. Marking a child's `S` is `scr ∪ S`
  (`|S|` writes), clearing is `\ S` at the same `|S|` touched entries —
  never a length-`A.N` wipe.
* `restrictSweep` threads the scratch across the node's child list —
  the fold with the array in the accumulator. `restrictSweep_fst`:
  starting clean, the scratch is clean again after every child (mark
  then clear restores `∅`), so each child scans against a scratch that
  decides membership in *its own* `S` — `scanRow_marked` and
  `restrict_adj_iff_scanRow` tie the scanned rows to `restrict`'s
  graph, and `histScan_marked` does the same for the `hist` filter.
  The invariant is load-bearing: against a dirty scratch, `scanRow`
  keeps stale neighbours and the scan is *wrong*, not slow — which is
  why the clear is charged per child.
* `childCharge` is the per-child account: `Σ_{s∈S} deg_A(s)` for the
  row scans (**degrees in the parent `A`** — see the hazard), plus
  `|S|·(L + ℓ·(2R+1))` for the color-row copies and the `hist` filter
  (`ℓ` lists of `≤ 2R+1` names per vertex, each name one scratch
  lookup), plus `2|S|` for mark and clear. **No `A.N` term**: the
  per-child array that would make the node `Θ(A.N²)` is visibly absent.
* `nodeCharge = A.N + Σ_children childCharge`
  (`restrictSweep_snd`/`nodeCharge_eq_sum`): the array's allocation is
  charged once per node, and nowhere else.

**Hazard (§4, the `K_{3,n−3}` witness): `O(‖A[S]‖ + |S|)` is FALSE.**
Scanning `s`'s CSR row costs `deg_A(s)`, not `deg_{A[S]}(s)`; on
`K_{3,n−3}` with `S` the 3-side, `‖A[S]‖ + |S| = 6` while the build
reads `Θ(n)` entries. No statement of that shape appears in this file;
every row scan below is priced at the *parent* degree.

## §4 The children aggregate

`sum_degSum_le_mul` is §4's double count: over the clusters of a
degree-`D` family, `Σ_u Σ_{s∈X_u} deg_A(s) = Σ_s deg_A(s)·|{u : s ∈
X_u}| ≤ D·2M` — the generic weighted count is `sum_sum_le_mul_sum`, the
vertex-count specialization of which is the landed
`CoverDegree.sum_ncard_le_mul`. With the degree in the shape
`CoverDegree.exists_cover_degree` delivers (`⌈c·N^δ⌉₊`, ceiling
included), `sum_degSum_le_rpow` concludes §4's aggregate
`≤ 2(c+1)·‖A‖^{1+δ}` — the `2c_D·‖A‖^{1+δ}` shape, with the `+1`
absorbing the ceiling exactly as in `CoverEdgeSum.sum_clusterWeight_le_rpow`,
and the whole children-building column absorbed by the cover term in §7.
`sum_childCharge_le` extends the count to the full per-child charge:
`≤ D·2M + N·D·(L + ℓ(2R+1) + 2)`, via `CoverDegree.sum_ncard_le_mul`
for the `|S|`-proportional half; `nodeCharge_le` adds the one
allocation. `_of_isNeighborhoodCover` variants consume the landed cover
predicate through its `degree_le` field.
-/

namespace Lax3Proofs.Impl

open Lax3.ColoredGraphs (Coloring)
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.CoverEdgeSum (graphWeight)

variable {n : ℕ}

/-! ### §1a The enumeration: local names for a vertex set -/

/-- The enumeration embedding of §6.1's "rank `S` to get local names":
the local carrier `Fin S.ncard` into the parent carrier, through the
same `Driver.setEquiv` the driver's compaction bijection uses — so the
identities to `preG`/`childArena` below are definitional. -/
noncomputable def restrictEmb (S : Set (Fin n)) : Fin S.ncard ↪ Fin n :=
  (Driver.setEquiv S).toEmbedding.trans (Function.Embedding.subtype _)

@[simp] theorem restrictEmb_apply (S : Set (Fin n)) (a : Fin S.ncard) :
    restrictEmb S a = ((Driver.setEquiv S) a : Fin n) := rfl

theorem restrictEmb_mem (S : Set (Fin n)) (a : Fin S.ncard) :
    restrictEmb S a ∈ S := ((Driver.setEquiv S) a).2

open Classical in
/-- The partial inverse of the enumeration: a parent name to its local
name if it has one — the reverse index the scratch array realizes. -/
noncomputable def toLocal (S : Set (Fin n)) (x : Fin n) : Option (Fin S.ncard) :=
  if h : x ∈ S then some ((Driver.setEquiv S).symm ⟨x, h⟩) else none

theorem toLocal_eq_none (S : Set (Fin n)) {x : Fin n} (hx : x ∉ S) :
    toLocal S x = none := by
  rw [toLocal, dif_neg hx]

theorem restrictEmb_toLocal (S : Set (Fin n)) {x : Fin n} (hx : x ∈ S)
    {a : Fin S.ncard} (h : toLocal S x = some a) : restrictEmb S a = x := by
  rw [toLocal, dif_pos hx] at h
  obtain rfl := Option.some_injective _ h
  show ((Driver.setEquiv S) ((Driver.setEquiv S).symm ⟨x, hx⟩) : Fin n) = x
  rw [Equiv.apply_symm_apply]

open Classical in
/-- The filtered list, read back at parent names, is exactly the stored
list's intersection with `S`, in order — "intersect the stored lists
with `S`" as a list identity. -/
theorem map_restrictEmb_filterMap_toLocal (S : Set (Fin n)) (l : List (Fin n)) :
    (l.filterMap (toLocal S)).map (fun b => (restrictEmb S b : Fin n))
      = l.filter fun x => decide (x ∈ S) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases hx : x ∈ S
    · have hsome : toLocal S x = some ((Driver.setEquiv S).symm ⟨x, hx⟩) := by
        rw [toLocal, dif_pos hx]
      rw [hsome, if_pos (by simpa using hx), List.map_cons, ih,
        restrictEmb_toLocal S hx hsome]
    · rw [toLocal_eq_none S hx, if_neg (by simpa using hx), ih]

/-! ### §1b The machine arena and `restrict` -/

/-- §4's data structure (module docstring): the carrier, the edges, the
color rows at the node's palette `Λ`, the composite renaming to the ROOT
carrier (size `n₀`), and D6's per-vertex channel — per vertex and per
ancestor round (`ℓp` rounds), the support names of that round's recorded
walk, at the node's own names. -/
structure MArena (Λ n₀ ℓp : ℕ) where
  /-- The number of vertices of this node's arena. -/
  N : ℕ
  /-- The edges of this node's arena. -/
  G : SimpleGraph (Fin N)
  /-- The color rows, at this node's palette. -/
  col : Coloring N Λ
  /-- This vertex's name at the ROOT (the composite of the `up` maps). -/
  up : Fin N ↪ Fin n₀
  /-- §4's `hist`: per vertex and per ancestor round, the stored support
  names, at this node's own carrier. -/
  hist : Fin N → Fin ℓp → List (Fin N)

variable {Λ n₀ ℓp : ℕ}

/-- **§6.1's `restrict A S`** — the induced sub-arena on `S`, at local
names `Fin S.ncard`: the induced graph, the color rows copied, `up` the
parent names (composed to the root, E6), `hist` filtered — each stored
list intersected with `S` and renamed local, sound because carriers are
nested (D6). -/
noncomputable def MArena.restrict (A : MArena Λ n₀ ℓp) (S : Set (Fin A.N)) :
    MArena Λ n₀ ℓp where
  N := S.ncard
  G := SimpleGraph.comap (fun a => (restrictEmb S a : Fin A.N)) A.G
  col := fun c => {a | restrictEmb S a ∈ A.col c}
  up := (restrictEmb S).trans A.up
  hist := fun a r => (A.hist (restrictEmb S a) r).filterMap (toLocal S)

open Classical in
/-- The `hist` half of `restrict`, sound: the filtered list at parent
names is the stored list's intersection with `S`, in order. -/
theorem restrict_hist_map (A : MArena Λ n₀ ℓp) (S : Set (Fin A.N))
    (a : Fin (A.restrict S).N) (r : Fin ℓp) :
    ((A.restrict S).hist a r).map (fun b => (restrictEmb S b : Fin A.N))
      = (A.hist (restrictEmb S a) r).filter fun x => decide (x ∈ S) :=
  map_restrictEmb_filterMap_toLocal S _

/-- Filtering never lengthens a stored list — with §4's `≤ 2R+1` bound
on the stored lists, the child's lists keep it. -/
theorem restrict_hist_length_le (A : MArena Λ n₀ ℓp) (S : Set (Fin A.N))
    (a : Fin (A.restrict S).N) (r : Fin ℓp) :
    ((A.restrict S).hist a r).length ≤ (A.hist (restrictEmb S a) r).length :=
  List.length_filterMap_le _ _

/-! ### §1c The identities to `DriverArena` -/

section DriverIdentity

variable {L : ℕ}

/-- A machine arena over the driver's abstract arena: the same carrier,
graph, colors and renaming, together with a concrete `hist` table (§4's
materialization of the abstract `(connector, arena)` channel). -/
noncomputable def ofArena (A : Driver.Arena Λ n₀)
    (h : Fin A.N → Fin ℓp → List (Fin A.N)) : MArena Λ n₀ ℓp :=
  ⟨A.N, A.G, A.col, A.up, h⟩

variable (Sch : Driver.Setup L) (A : Driver.Arena Λ n₀)
  (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
  (h : Fin A.N → Fin ℓp → List (Fin A.N))

/-- The restricted carrier IS the driver's child carrier. -/
theorem restrict_N_eq_childN :
    ((ofArena A h).restrict (Driver.cluster Sch A π u)).N
      = Driver.childN Sch A π u := rfl

/-- **The graph half of `restrict` IS `Driver.preG`** at
`S := cluster Sch A π u` — `B₀` of §5 lines 16/20, the graph the
profiles are measured in, *before* isolation. Definitional: both sides
are `A.G` comapped along the same `setEquiv` enumeration. -/
theorem restrict_G_eq_preG :
    ((ofArena A h).restrict (Driver.cluster Sch A π u)).G
      = Driver.preG Sch A π u := rfl

/-- **The copied color rows are `Driver.childCol0`** — the child's
colors at the parent palette; the marker and profile layers on top of
them belong to E12c's `recordProfiles`, not to `restrict`. -/
theorem restrict_col_eq_childCol0 :
    ((ofArena A h).restrict (Driver.cluster Sch A π u)).col
      = Driver.childCol0 Sch A π u := rfl

/-- **The renaming is `childArena`'s**: the enumeration into the parent,
composed to the root (E6 — the record is never re-typed). -/
theorem restrict_up_eq_childArena_up :
    ((ofArena A h).restrict (Driver.cluster Sch A π u)).up
      = (Driver.childArena Sch A π u).up := rfl

end DriverIdentity

/-! ### §2 `isolate` -/

/-- **§4 row 2, `isolate B W`** — drop the edges incident to `W`. It is
Lax12's `deleteVerts`: the carrier is kept, only edges go. -/
noncomputable def MArena.isolate (B : MArena Λ n₀ ℓp) (W : Set (Fin B.N)) :
    MArena Λ n₀ ℓp :=
  { B with G := deleteVerts B.G W }

/-- `deleteVerts` isolates, never removes: the carrier is unchanged. -/
@[simp] theorem isolate_N (B : MArena Λ n₀ ℓp) (W : Set (Fin B.N)) :
    (B.isolate W).N = B.N := rfl

/-- **The identity**: `isolate` IS `deleteVerts` at the batch set. -/
@[simp] theorem isolate_G (B : MArena Λ n₀ ℓp) (W : Set (Fin B.N)) :
    (B.isolate W).G = deleteVerts B.G W := rfl

@[simp] theorem isolate_col (B : MArena Λ n₀ ℓp) (W : Set (Fin B.N)) :
    (B.isolate W).col = B.col := rfl

@[simp] theorem isolate_hist (B : MArena Λ n₀ ℓp) (W : Set (Fin B.N)) :
    (B.isolate W).hist = B.hist := rfl

section DriverIdentity

variable {L : ℕ} (Sch : Driver.Setup L) (A : Driver.Arena Λ n₀)
  (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
  (h : Fin A.N → Fin ℓp → List (Fin A.N))

/-- **§5 line 21 as a program identity**: the driver's child graph is
`isolate` after `restrict` — restrict to the cluster, then isolate the
padded batch. This is where E13 plugs the two programs of this file
into `Driver.childArena`. -/
theorem childArena_G_eq_isolate_restrict :
    (Driver.childArena Sch A π u).G
      = (((ofArena A h).restrict (Driver.cluster Sch A π u)).isolate
          (Set.range (Driver.batchFn Sch A π u))).G := rfl

end DriverIdentity

/-- The charge of `isolate`: one sweep of the CSR, each row priced at
its full length — the machine rewrites every row, dropping the entries
incident to `W`. -/
noncomputable def isolateCharge (B : MArena Λ n₀ ℓp) [DecidableRel B.G.Adj] : ℕ :=
  ∑ v : Fin B.N, (B.G.degree v + 1)

theorem isolateCharge_eq (B : MArena Λ n₀ ℓp) [DecidableRel B.G.Adj] :
    isolateCharge B = 2 * B.G.edgeFinset.card + B.N := by
  rw [isolateCharge, Finset.sum_add_distrib,
    SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp

/-- **§4's `O(‖B‖)`**: the sweep costs `2M + N ≤ 2‖B‖`. -/
theorem isolateCharge_le_two_gsize (B : MArena Λ n₀ ℓp) [DecidableRel B.G.Adj] :
    isolateCharge B ≤ 2 * gsize B.G := by
  rw [isolateCharge_eq, gsize]
  omega

/-! ### §3a The scratch: one array per node -/

/-- One CSR row scan through the scratch: the neighbours of `s` the
machine keeps are those flagged in the scratch. Correct only against a
scratch marked with *this* child's `S` and nothing else
(`scanRow_marked`); a stale flag keeps a wrong neighbour — which is why
the sweep's clear is not optional. -/
def scanRow (G : SimpleGraph (Fin n)) (scr : Set (Fin n)) (s : Fin n) :
    Set (Fin n) :=
  {t | G.Adj s t ∧ t ∈ scr}

/-- Marking `S` on a clean scratch makes the scan keep exactly the
neighbours in `S` — §6.1's "scan each `s ∈ S`'s CSR row keeping
neighbours in `S`". -/
theorem scanRow_marked (G : SimpleGraph (Fin n)) (S : Set (Fin n)) (s : Fin n) :
    scanRow G ((∅ : Set (Fin n)) ∪ S) s = {t | G.Adj s t ∧ t ∈ S} := by
  rw [Set.empty_union]
  rfl

/-- The scanned rows against the marked clean scratch ARE `restrict`'s
graph: `a ~ b` in the child iff the scan of `a`'s row keeps `b`. -/
theorem restrict_adj_iff_scanRow (A : MArena Λ n₀ ℓp) (S : Set (Fin A.N))
    (a b : Fin (A.restrict S).N) :
    (A.restrict S).G.Adj a b
      ↔ restrictEmb S b ∈ scanRow A.G ((∅ : Set (Fin A.N)) ∪ S) (restrictEmb S a) := by
  rw [scanRow_marked]
  exact ⟨fun hadj => ⟨hadj, restrictEmb_mem S b⟩, fun hb => hb.1⟩

open Classical in
/-- The `hist` filter through the scratch: each stored name is one
scratch lookup, then the reverse index. -/
noncomputable def histScan (S : Set (Fin n)) (scr : Set (Fin n))
    (l : List (Fin n)) : List (Fin S.ncard) :=
  l.filterMap fun x => if x ∈ scr then toLocal S x else none

/-- Against the marked clean scratch, the scan computes exactly
`restrict`'s filtered `hist` list. -/
theorem histScan_marked (S : Set (Fin n)) (l : List (Fin n)) :
    histScan S ((∅ : Set (Fin n)) ∪ S) l = l.filterMap (toLocal S) := by
  unfold histScan
  congr 1
  funext x
  by_cases hx : x ∈ S
  · rw [if_pos (by simpa using hx)]
  · rw [if_neg (by simpa using hx), toLocal_eq_none S hx]

/-! ### §3b The per-child charge and the node's sweep -/

/-- `Σ_{s∈S} deg_G(s)` — the row-scan half of the charge. -/
noncomputable def degSum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Set (Fin n)) : ℕ :=
  ∑ s ∈ (Set.toFinite S).toFinset, G.degree s

/-- **The per-child charge of §6.1**, at parent graph `G`, `Lc` color
rows, `ℓp` ancestor rounds and profile radius `R`:

* `degSum G S = Σ_{s∈S} deg_G(s)` — the row scans, at **parent**
  degrees (`O(‖A[S]‖ + |S|)` is false, module docstring);
* `|S|·(Lc + ℓp·(2R+1))` — the color-row copies and the `hist` filter;
* `2|S|` — marking and clearing the scratch at the `|S|` touched
  entries.

**No `G`-carrier-sized term appears**: the allocation is the node's
(`nodeCharge`), not the child's. -/
noncomputable def childCharge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Lc ℓp R : ℕ) (S : Set (Fin n)) : ℕ :=
  degSum G S + S.ncard * (Lc + ℓp * (2 * R + 1)) + 2 * S.ncard

/-- **The node's sweep** — the fold over the child list with the scratch
in the accumulator: mark this child's `S` (`∪ S`, `|S|` writes), build
the child against the marked scratch, clear the `|S|` touched entries
(`\ S`), recurse on the remaining children with the *same* array. The
charge accumulates `childCharge` per child and nothing per child is
carrier-sized. -/
noncomputable def restrictSweep (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Lc ℓp R : ℕ) : List (Set (Fin n)) → Set (Fin n) → Set (Fin n) × ℕ
  | [], scr => (scr, 0)
  | S :: Ss, scr =>
      ((restrictSweep G Lc ℓp R Ss ((scr ∪ S) \ S)).1,
        childCharge G Lc ℓp R S + (restrictSweep G Lc ℓp R Ss ((scr ∪ S) \ S)).2)

/-- **The reuse invariant**: starting clean, the scratch is clean again
after every child — mark then clear restores `∅`, so each child's scan
sees a scratch that decides membership in its own `S`
(`restrict_adj_iff_scanRow`), across the whole child list, on one
array. -/
theorem restrictSweep_fst (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Lc ℓp R : ℕ) (Ss : List (Set (Fin n))) :
    (restrictSweep G Lc ℓp R Ss ∅).1 = ∅ := by
  induction Ss with
  | nil => rfl
  | cons S Ss ih =>
    show (restrictSweep G Lc ℓp R Ss ((∅ ∪ S) \ S)).1 = ∅
    rw [Set.empty_union, Set.diff_self]
    exact ih

/-- The sweep's charge is the sum of the per-child charges — no other
term, in particular no per-child allocation. -/
theorem restrictSweep_snd (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Lc ℓp R : ℕ) (Ss : List (Set (Fin n))) (scr : Set (Fin n)) :
    (restrictSweep G Lc ℓp R Ss scr).2
      = (Ss.map (childCharge G Lc ℓp R)).sum := by
  induction Ss generalizing scr with
  | nil => rfl
  | cons S Ss ih =>
    show childCharge G Lc ℓp R S + _ = _
    rw [ih, List.map_cons, List.sum_cons]

/-- **The node's whole `restrict` bill**: the scratch array is allocated
(and zeroed) once, `n`; every child pays `childCharge`. The `n` appears
exactly once — a per-child array would put it in `childCharge` and make
the node `Θ(n²)`; it is not there. -/
noncomputable def nodeCharge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Lc ℓp R : ℕ) (Ss : List (Set (Fin n))) : ℕ :=
  n + (restrictSweep G Lc ℓp R Ss ∅).2

theorem nodeCharge_eq_sum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Lc ℓp R : ℕ) (Ss : List (Set (Fin n))) :
    nodeCharge G Lc ℓp R Ss = n + (Ss.map (childCharge G Lc ℓp R)).sum := by
  rw [nodeCharge, restrictSweep_snd]

/-! ### §4 The children aggregate -/

variable {N : ℕ}

/-- The weighted fibre double count — the engine of §4's aggregate, the
weight-`1` case of which is the landed `CoverDegree.sum_ncard_le_mul`:
`Σ_u Σ_{s∈X_u} f(s) = Σ_s f(s)·|{u : s ∈ X_u}| ≤ d·Σ_s f(s)` for a
family of fibre degree `≤ d`. -/
theorem sum_sum_le_mul_sum (X : Fin N → Set (Fin N)) (f : Fin N → ℕ) (d : ℕ)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ d) :
    ∑ u : Fin N, ∑ s ∈ (Set.toFinite (X u)).toFinset, f s
      ≤ d * ∑ s : Fin N, f s := by
  classical
  have hind : ∀ u : Fin N, ∑ s ∈ (Set.toFinite (X u)).toFinset, f s
      = ∑ s : Fin N, if s ∈ X u then f s else 0 := by
    intro u
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext s; simp) fun _ _ => rfl
  have hfib : ∀ s : Fin N, ∑ u : Fin N, (if s ∈ X u then f s else 0)
      = {u : Fin N | s ∈ X u}.ncard * f s := by
    intro s
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext u
    simp
  calc ∑ u : Fin N, ∑ s ∈ (Set.toFinite (X u)).toFinset, f s
      = ∑ s : Fin N, ∑ u : Fin N, if s ∈ X u then f s else 0 := by
        rw [Finset.sum_congr rfl fun u _ => hind u]
        exact Finset.sum_comm
    _ = ∑ s : Fin N, {u : Fin N | s ∈ X u}.ncard * f s :=
        Finset.sum_congr rfl fun s _ => hfib s
    _ ≤ ∑ s : Fin N, d * f s :=
        Finset.sum_le_sum fun s _ => Nat.mul_le_mul_right _ (h s)
    _ = d * ∑ s : Fin N, f s := by rw [Finset.mul_sum]

/-- **§4's display**: `Σ_u Σ_{s∈X_u} deg_A(s) ≤ D·2M` — the row-scan
halves of all the children's `restrict`s, double-counted against the
cover degree. -/
theorem sum_degSum_le_mul (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (X : Fin N → Set (Fin N)) (d : ℕ)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ d) :
    ∑ u : Fin N, degSum G (X u) ≤ d * (2 * G.edgeFinset.card) := by
  have := sum_sum_le_mul_sum X (fun s => G.degree s) d h
  rwa [SimpleGraph.sum_degrees_eq_twice_card_edges] at this

/-- The same, consumed through the landed cover predicate. -/
theorem sum_degSum_le_of_isNeighborhoodCover {r d : ℕ} {G : SimpleGraph (Fin N)}
    [DecidableRel G.Adj] {X : Fin N → Set (Fin N)}
    (hcov : Lax3.NeighborhoodCovers.IsNeighborhoodCover G r X d) :
    ∑ u : Fin N, degSum G (X u) ≤ d * (2 * G.edgeFinset.card) :=
  sum_degSum_le_mul G X d hcov.degree_le

/-- **The full per-child charge, aggregated over a node's children**:
`Σ_u childCharge(X_u) ≤ D·2M + N·D·(L + ℓ(2R+1) + 2)` — the row scans
by the double count above, the `|S|`-proportional half by the landed
`CoverDegree.sum_ncard_le_mul`. Together with `nodeCharge`'s single
allocation this is §6.1's aggregate over a node. -/
theorem sum_childCharge_le (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (Lc ℓp R : ℕ) (X : Fin N → Set (Fin N)) (d : ℕ)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ d) :
    ∑ u : Fin N, childCharge G Lc ℓp R (X u)
      ≤ d * (2 * G.edgeFinset.card) + N * d * (Lc + ℓp * (2 * R + 1) + 2) := by
  have hV : ∑ u : Fin N, (X u).ncard ≤ N * d :=
    Lax3Proofs.CoverDegree.sum_ncard_le_mul X d h
  have hE : ∑ u : Fin N, degSum G (X u) ≤ d * (2 * G.edgeFinset.card) :=
    sum_degSum_le_mul G X d h
  have hsplit : ∑ u : Fin N, childCharge G Lc ℓp R (X u)
      = (∑ u : Fin N, degSum G (X u))
        + (∑ u : Fin N, (X u).ncard) * (Lc + ℓp * (2 * R + 1))
        + 2 * ∑ u : Fin N, (X u).ncard := by
    unfold childCharge
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
  rw [hsplit]
  have h1 : (∑ u : Fin N, (X u).ncard) * (Lc + ℓp * (2 * R + 1))
      ≤ N * d * (Lc + ℓp * (2 * R + 1)) := Nat.mul_le_mul_right _ hV
  have h2 : 2 * (∑ u : Fin N, (X u).ncard) ≤ 2 * (N * d) :=
    Nat.mul_le_mul_left _ hV
  refine le_trans (Nat.add_le_add (Nat.add_le_add hE h1) h2) (le_of_eq ?_)
  ring

/-- The node's whole bill against the cover degree: one allocation plus
the children aggregate. -/
theorem nodeCharge_le (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (Lc ℓp R : ℕ) (X : Fin N → Set (Fin N)) (d : ℕ)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ d) :
    nodeCharge G Lc ℓp R ((List.finRange N).map X)
      ≤ N + (d * (2 * G.edgeFinset.card)
          + N * d * (Lc + ℓp * (2 * R + 1) + 2)) := by
  have hlist : ((List.finRange N).map X |>.map (childCharge G Lc ℓp R)).sum
      = ∑ u : Fin N, childCharge G Lc ℓp R (X u) := by
    rw [List.map_map, Fin.sum_univ_def]
    rfl
  rw [nodeCharge_eq_sum, hlist]
  exact Nat.add_le_add_left (sum_childCharge_le G Lc ℓp R X d h) N

/-! ### §4a The aggregate at the cover's actual degree shape -/

theorem edgeFinset_card_le_graphWeight (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : G.edgeFinset.card ≤ graphWeight G := by
  have hM : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [CoverEdgeSum.graphWeight, ← hM]
  exact Nat.le_add_left _ _

/-- **§4's aggregate, closed**: with the cover degree in the exact shape
`CoverDegree.exists_cover_degree` delivers it — `⌈c·N^δ⌉₊`, ceiling
included — the children's total row-scan charge is at most
`2(c+1)·‖A‖^{1+δ}`: the `2c_D·‖A‖^{1+δ}` shape of §4, the `+1`
absorbing the ceiling exactly as in
`CoverEdgeSum.sum_clusterWeight_le_rpow`, whose hypotheses (`0 ≤ c`,
`0 ≤ δ`, `1 ≤ ‖A‖`) are also this statement's. Absorbed by the cover
term in §7. -/
theorem sum_degSum_le_rpow (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (X : Fin N → Set (Fin N)) (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hW : 1 ≤ graphWeight G)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ ⌈c * (N : ℝ) ^ δ⌉₊) :
    ((∑ u : Fin N, degSum G (X u) : ℕ) : ℝ)
      ≤ 2 * (c + 1) * ((graphWeight G : ℕ) : ℝ) ^ (1 + δ) := by
  set W : ℝ := ((graphWeight G : ℕ) : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW1
  have hNW : ((N : ℕ) : ℝ) ≤ W := by
    have hle : (N : ℕ) ≤ graphWeight G := by
      rw [CoverEdgeSum.graphWeight]; exact Nat.le_add_right _ _
    rw [hWdef]; exact_mod_cast hle
  have hMW : ((G.edgeFinset.card : ℕ) : ℝ) ≤ W := by
    rw [hWdef]; exact_mod_cast edgeFinset_card_le_graphWeight G
  -- the ceiling, honestly (as in `sum_clusterWeight_le_rpow`)
  have hxnn : (0 : ℝ) ≤ c * ((N : ℕ) : ℝ) ^ δ :=
    mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg _) δ)
  have hceil : ((⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ : ℕ) : ℝ) ≤ c * ((N : ℕ) : ℝ) ^ δ + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hxnn)
  have hmono : ((N : ℕ) : ℝ) ^ δ ≤ W ^ δ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNW hδ
  have hone : (1 : ℝ) ≤ W ^ δ := by
    have := Real.rpow_le_rpow (le_of_lt zero_lt_one) hW1 hδ
    rwa [Real.one_rpow] at this
  have hD : ((⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ : ℕ) : ℝ) ≤ (c + 1) * W ^ δ := by
    refine le_trans hceil ?_
    calc c * ((N : ℕ) : ℝ) ^ δ + 1 ≤ c * W ^ δ + W ^ δ :=
          add_le_add (mul_le_mul_of_nonneg_left hmono hc) hone
      _ = (c + 1) * W ^ δ := by ring
  -- the integer bound, cast up
  have hnat : ∑ u : Fin N, degSum G (X u)
      ≤ ⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ * (2 * G.edgeFinset.card) :=
    sum_degSum_le_mul G X _ h
  have hcast : ((∑ u : Fin N, degSum G (X u) : ℕ) : ℝ)
      ≤ ((⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ : ℕ) : ℝ) * (2 * ((G.edgeFinset.card : ℕ) : ℝ)) := by
    push_cast
    exact_mod_cast hnat
  refine le_trans hcast ?_
  have hstep : ((⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ : ℕ) : ℝ) * (2 * ((G.edgeFinset.card : ℕ) : ℝ))
      ≤ ((c + 1) * W ^ δ) * (2 * W) := by
    refine mul_le_mul hD (by linarith) (by positivity) ?_
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt hWpos) δ)
  refine le_trans hstep (le_of_eq ?_)
  rw [Real.rpow_add hWpos, Real.rpow_one]
  ring

/-- The aggregate at the cover predicate, degree in
`CoverDegree.exists_cover_degree`'s shape. -/
theorem sum_degSum_le_rpow_of_isNeighborhoodCover {r : ℕ}
    {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {X : Fin N → Set (Fin N)}
    {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hW : 1 ≤ graphWeight G)
    (hcov : Lax3.NeighborhoodCovers.IsNeighborhoodCover G r X ⌈c * (N : ℝ) ^ δ⌉₊) :
    ((∑ u : Fin N, degSum G (X u) : ℕ) : ℝ)
      ≤ 2 * (c + 1) * ((graphWeight G : ℕ) : ℝ) ^ (1 + δ) :=
  sum_degSum_le_rpow G X c δ hc hδ hW hcov.degree_le

end Lax3Proofs.Impl
