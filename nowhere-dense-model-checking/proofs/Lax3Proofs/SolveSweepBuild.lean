import Lax3Proofs.SolveSweepStep

/-!
# F6c12 (residual 3) — the cover sweep's BUILD pass, discharged

`SolveSweepStep` splits `CovSweepIn` at the deletable structure's seam
and names two residuals. This file discharges the first of them,
**`CovAdjBuildIn`**, with a concrete program and an honest budget: from
the arena's own CSR and the rank array, materialize the deletable
adjacency region `DelAdjSt (ao j) (aj j) (dg j) (mt j) A.G ∅` and the
order region `OrdArr (od j)`, preserving everything else.

## The program: four flat passes

* `bldOrdCom` — the rank inversion, `od[ra[i]] := i` (`OrdArr`'s entry
  `i` is the vertex of rank `i`, `RankArr`'s entry `v` is the rank of
  `v`; the scatter through `ra` is the inverse).
* `bldOffCom` — the offsets, `ao[i] := off[i]` for `i ≤ N`.
* `bldDegCom` — the live lengths, zeroed; the mate pass then uses `dg`
  itself as its cursor array, so the pass owes no scratch region of its
  own.
* `bldMateCom` — one owner-advancing pass over the arena's slot space
  (`Lib.Csr.ownerScan_spec`). At the slot of row `u` holding `w`, if
  `u < w` **both copies of the edge are emitted at once**: `w` into
  `aj[off u + dg u]`, `u` into `aj[off w + dg w]`, the two `mt` cells
  crossed, both cursors bumped. The copy in row `w` is skipped when the
  scan reaches it (`w < u` fails the test), so every edge is emitted
  exactly once and no mate is ever searched for — this is the counting
  trick the seam's docstring prices at `O(N + ns)`.

`bldK N ns = 93·N + 58·ns + 30`: three carrier scans at `12`, `12` and
`11` a vertex, and the slot pass at `58` a slot and `58` a row
(`ownerScan_spec`'s two-term potential, the turn at `54` either way).
Nothing here is a pass that is not priced.

## What this file proves

* `bldOrd_spec`, `bldOff_spec`, `bldDeg_spec`, `bldMate_spec` — the
  four passes, each at its own budget;
* `adjBuildAt_bldAdjCom` — the build contract of the deletable
  adjacency structure, at `81·N + 58·ns + 24` (`AdjBuildAt`, Finding 1);
* `covAdjBuildIn_bldCom` — the residual `CovAdjBuildIn`, **verbatim**,
  at `bldK A.N ns`;
* §9's control — the pass really runs on `K₂`, emitting the one edge at
  its lower copy and skipping the higher one, so none of the above is
  vacuous.

## Finding 1 — `AdjBuildIn` as landed is not dischargeable

`SolveSweepAdj.lean:308` states the build contract as
`∀ {N} (G) (ns), Spec B (GraphCsr o t G ns ∧ allocations) bldC (…) (kb N ns)`
— at one fixed `B`, and **naming no scalar cell that holds `N` or
`ns`**. Two things are then missing that no program can supply.

* An IMP+ program reads array lengths nowhere (they exist only to make
  an out-of-range access stuck, `Imp.lean`'s header), so a fixed
  command cannot find the end of a carrier whose size is only in the
  length of `o`, and the `Spec` quantifies over every `N` at once.
* At `N ≥ B` the pass's own indices are not words, and `Run`'s value
  bound fails on the first `store`.

§7 therefore states the same content in the shape a program *can*
meet — `AdjBuildAt`, which is `AdjBuildIn` with the two figures in
named cells and inside the word bound — and discharges it. The landed
`AdjBuildIn` is left unproved, deliberately; the residual this file
owes does not go through it, and `CovAdjBuildIn` supplies both
missing facts from the arena contract (`ArenaStW`'s `nN`/`nS` cells)
and the admissible word bound (`mcB`).

## Finding 2 — the arena's offsets *are* `DelAdjSt`'s

`GraphCsr`'s rows are duplicate-free and their membership is adjacency,
so row `v` has exactly `(G.neighborSet v).ncard` slots
(`srcCsr_of_graphCsr`): the arena's CSR offsets satisfy `DelAdjSt`'s
anchored degree-sum recursion on the nose (`offF_unique` is then the
landed fact identifying them with any other witness). Aliasing `ao` to
the arena's offset region would therefore have been sound. The pass copies instead, so that `ao`
stays an allocation of the discharger's own and the peel's `DelAdjSt`
never reads the arena's region.

The `S = ∅` clauses are discharged as stated, through
`Impl.deleteVerts_empty`; no duplicate-freeness clause is added
(`DelAdjSt.slot_injOn` derives it).

Both residual and program stay **parametric in `ord`**: the rank
inversion reads whatever permutation `RankArr` holds.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

/-! ## §0 Small array and run helpers

The statement shapes the passes are built from, each with its value
obligations named and its cost computed once. -/

private theorem getD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) :
    (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem getD_set_of_ne {l : List ℕ} {i k v : ℕ} (h : i ≠ k) :
    (l.set i v).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
    List.getD_eq_getElem?_getD]

/-- `a[x] := y`, two scalars. -/
private theorem run_store_var {B : ℕ} {a x y : String} {σ : Env}
    (hx : σ.vars x < B) (hy : σ.vars y < B)
    (hlt : σ.vars x < (σ.arrs a).length) :
    Run B (.store a (.var x) (.var y)) σ (σ.setArr a (σ.vars x) (σ.vars y)) 3 :=
  (Run.store (evalB_var hx) (evalB_var hy) hlt).mono (by simp)

/-- `a[x] := v`, a literal. -/
private theorem run_store_lit {B : ℕ} {a x : String} {σ : Env} {v : ℕ}
    (hx : σ.vars x < B) (hv : v < B) (hlt : σ.vars x < (σ.arrs a).length) :
    Run B (.store a (.var x) (.lit v)) σ (σ.setArr a (σ.vars x) v) 3 :=
  (Run.store (evalB_var hx) (evalB_lit hv) hlt).mono (by simp)

/-- `a[x] := b[x]`, the copy. -/
private theorem run_store_copy {B : ℕ} {a b x : String} {σ : Env} {v : ℕ}
    (hx : σ.vars x < B) (hb : (σ.arrs b)[σ.vars x]? = some v) (hvB : v < B)
    (hlt : σ.vars x < (σ.arrs a).length) :
    Run B (.store a (.var x) (.get b (.var x))) σ (σ.setArr a (σ.vars x) v) 4 :=
  (Run.store (evalB_var hx) (evalB_get (evalB_var hx) hb hvB) hlt).mono (by simp)

/-- `a[b[x]] := x`, the scatter store. -/
private theorem run_store_scatter {B : ℕ} {a b x : String} {σ : Env} {k : ℕ}
    (hx : σ.vars x < B) (hb : (σ.arrs b)[σ.vars x]? = some k) (hkB : k < B)
    (hlt : k < (σ.arrs a).length) :
    Run B (.store a (.get b (.var x)) (.var x)) σ
      (σ.setArr a k (σ.vars x)) 4 :=
  (Run.store (evalB_get (evalB_var hx) hb hkB) (evalB_var hx) hlt).mono (by simp)

/-- `a[x] := a[x] + 1`, the cursor bump. -/
private theorem run_store_incr {B : ℕ} {a x : String} {σ : Env} {va : ℕ}
    (hx : σ.vars x < B) (ha : (σ.arrs a)[σ.vars x]? = some va)
    (hsucc : va + 1 < B) (hlt : σ.vars x < (σ.arrs a).length) :
    Run B (.store a (.var x) (.add (.get a (.var x)) (.lit 1))) σ
      (σ.setArr a (σ.vars x) (va + 1)) 6 := by
  have e : (Expr.add (.get a (.var x)) (.lit 1)).evalB B σ = some (va + 1) :=
    evalB_bin (evalB_get (evalB_var hx) ha (by omega)) (evalB_lit (by omega))
      (by simpa using hsucc)
  exact (Run.store (evalB_var hx) e hlt).mono (by simp)

/-- `z := a[x]`, a read into a scalar. -/
private theorem run_assign_get {B : ℕ} {z a x : String} {σ : Env} {va : ℕ}
    (hx : σ.vars x < B) (ha : (σ.arrs a)[σ.vars x]? = some va) (haB : va < B) :
    Run B (.assign z (.get a (.var x))) σ (σ.setVar z va) 3 :=
  (Run.assign (evalB_get (evalB_var hx) ha haB)).mono (by simp)

/-- `z := a[x] + b[x]`, the slot address. -/
private theorem run_assign_add {B : ℕ} {z a b x : String} {σ : Env} {va vb : ℕ}
    (hx : σ.vars x < B) (ha : (σ.arrs a)[σ.vars x]? = some va)
    (hb : (σ.arrs b)[σ.vars x]? = some vb) (hsum : va + vb < B) :
    Run B (.assign z (.add (.get a (.var x)) (.get b (.var x)))) σ
      (σ.setVar z (va + vb)) 6 := by
  have e : (Expr.add (.get a (.var x)) (.get b (.var x))).evalB B σ
      = some (va + vb) :=
    evalB_bin (evalB_get (evalB_var hx) ha (by omega))
      (evalB_get (evalB_var hx) hb (by omega)) (by simpa using hsum)
  exact (Run.assign e).mono (by simp)

/-- `x + 1`, evaluated. -/
private theorem evalB_incr {B : ℕ} {y : String} {σ : Env} (hy : σ.vars y + 1 < B) :
    (Expr.add (.var y) (.lit 1)).evalB B σ = some (σ.vars y + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var y) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hy)
  simpa using h

/-- `x := x + 1`, the counter bump. -/
private theorem run_assign_incr {B : ℕ} {x : String} {σ : Env}
    (h : σ.vars x + 1 < B) :
    Run B (.assign x (.add (.var x) (.lit 1))) σ
      (σ.setVar x (σ.vars x + 1)) 4 := by
  have e : (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) :=
    evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using h)
  exact (Run.assign e).mono (by simp)

/-! ## §1 What the build pass reads of the arena's CSR

`GraphCsr` quantifies its two index functions away; a scanning pass
needs them, together with the facts that the offsets are the *degree
sums* (Finding 2) and that a row lists each neighbour exactly once.
`SrcCsr` is that package, stated at an allocation of *at least* the two
extents so that the windowed arena contract feeds it directly. -/

/-- **The source CSR, as the build pass reads it**: offsets anchored at
`0` with degree-sum steps, extent `off N = ns`, the two regions holding
`off` and `tgt` on allocations of at least their extents, every target
a vertex, every slot of row `v` a neighbour of `v`, every neighbour of
`v` in a slot of row `v`, and no two slots of one row equal. -/
structure SrcCsr (o t : String) {N : ℕ} (G : SimpleGraph (Fin N)) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The offsets are anchored. -/
  zero : off 0 = 0
  /-- One row per vertex, of exactly its degree. -/
  step : ∀ v : Fin N, off ((v : ℕ) + 1) = off (v : ℕ) + (G.neighborSet v).ncard
  /-- The extent. -/
  last : off N = ns
  /-- The offset region holds at least `N + 1` cells. -/
  offLen : N + 1 ≤ (σ.arrs o).length
  /-- The target region holds at least `ns` cells. -/
  tgtLen : ns ≤ (σ.arrs t).length
  /-- Reading an offset. -/
  offGet : ∀ i, i ≤ N → (σ.arrs o)[i]? = some (off i)
  /-- Reading a target. -/
  tgtGet : ∀ p, p < ns → (σ.arrs t)[p]? = some (tgt p)
  /-- Every target is a vertex. -/
  tgtLt : ∀ p, p < ns → tgt p < N
  /-- Every slot of row `v` holds a neighbour of `v`. -/
  sound : ∀ (v : Fin N) (p : ℕ), off (v : ℕ) ≤ p → p < off ((v : ℕ) + 1) →
    ∀ h : tgt p < N, G.Adj v ⟨tgt p, h⟩
  /-- Every neighbour of `v` sits in a slot of row `v`. -/
  complete : ∀ (v w : Fin N), G.Adj v w →
    ∃ p, off (v : ℕ) ≤ p ∧ p < off ((v : ℕ) + 1) ∧ tgt p = (w : ℕ)
  /-- No two slots of one row hold the same target. -/
  inj : ∀ (v : Fin N) (p r : ℕ), off (v : ℕ) ≤ p → p < off ((v : ℕ) + 1) →
    off (v : ℕ) ≤ r → r < off ((v : ℕ) + 1) → tgt p = tgt r → p = r

namespace SrcCsr

variable {o t : String} {N ns : ℕ} {G : SimpleGraph (Fin N)} {off tgt : ℕ → ℕ}
  {σ : Env}

/-- The offsets are monotone below `N` — the landed `offF_mono` at this
package's step clause. -/
theorem mono (h : SrcCsr o t G ns off tgt σ) :
    ∀ b, b ≤ N → ∀ a, a ≤ b → off a ≤ off b :=
  offF_mono h.step

/-- Every offset is at most the extent. -/
theorem off_le_ns (h : SrcCsr o t G ns off tgt σ) {i : ℕ} (hi : i ≤ N) :
    off i ≤ ns := by
  have := h.mono N le_rfl i hi
  rw [h.last] at this
  exact this

/-- A slot of a row is a slot of the structure. -/
theorem row_lt_ns (h : SrcCsr o t G ns off tgt σ) {v : Fin N} {p : ℕ}
    (hp : p < off ((v : ℕ) + 1)) : p < ns :=
  lt_of_lt_of_le hp (h.off_le_ns v.isLt)

/-- **A slot has one owner**: two rows containing the same slot are the
same row. -/
theorem owner_uniq (h : SrcCsr o t G ns off tgt σ) {a b p : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (h1 : off a ≤ p) (h2 : p < off (a + 1))
    (h3 : off b ≤ p) (h4 : p < off (b + 1)) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have := h.mono b hb (a + 1) (by omega)
    omega
  · exact heq
  · have := h.mono a ha (b + 1) (by omega)
    omega

/-- The arrays the pass never writes are the ones it reads: the package
transports along agreement on them. -/
theorem of_eq (h : SrcCsr o t G ns off tgt σ) {σ' : Env}
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t) :
    SrcCsr o t G ns off tgt σ' :=
  { h with
    offLen := by rw [ho]; exact h.offLen
    tgtLen := by rw [ht]; exact h.tgtLen
    offGet := by rw [ho]; exact h.offGet
    tgtGet := by rw [ht]; exact h.tgtGet }

end SrcCsr

/-- **The offsets of a `GraphCsr` are the degree sums** (Finding 2),
and its rows enumerate the neighbourhoods without repetition. The
allocation the pass reads may be longer than the exact-length state the
relation is stated at, as long as it agrees with it below the two
extents — which is how the windowed arena contract feeds this. -/
theorem srcCsr_of_graphCsr {o t : String} {N ns : ℕ} {G : SimpleGraph (Fin N)}
    {τ σ : Env} (h : GraphCsr o t G ns τ)
    (hoL : N + 1 ≤ (σ.arrs o).length) (htL : ns ≤ (σ.arrs t).length)
    (hoR : ∀ i, i ≤ N → (σ.arrs o)[i]? = (τ.arrs o)[i]?)
    (htR : ∀ p, p < ns → (σ.arrs t)[p]? = (τ.arrs t)[p]?) :
    ∃ off tgt, SrcCsr o t G ns off tgt σ := by
  classical
  obtain ⟨off, tgt, hc, h0, hnd, hadj⟩ := h
  refine ⟨off, tgt, ?_⟩
  -- the row of `v`, as a mapped range
  have hrow : ∀ v : Fin N, Csr.row off tgt (v : ℕ)
      = (List.range (Csr.rowLen off (v : ℕ))).map (fun k => tgt (off (v : ℕ) + k)) :=
    fun _ => rfl
  -- each row's length is the degree
  have hlen : ∀ v : Fin N, Csr.rowLen off (v : ℕ) = (G.neighborSet v).ncard := by
    intro v
    have hcard : (Csr.row off tgt (v : ℕ)).toFinset.card
        = (Csr.row off tgt (v : ℕ)).length :=
      List.toFinset_card_of_nodup (hnd v)
    have hset : ((Csr.row off tgt (v : ℕ)).toFinset : Set ℕ)
        = Fin.val '' (G.neighborSet v) := by
      ext u
      simp only [List.coe_toFinset, Set.mem_setOf_eq, hadj v u, Set.mem_image,
        SimpleGraph.mem_neighborSet]
      constructor
      · rintro ⟨hu, hA⟩
        exact ⟨⟨u, hu⟩, hA, rfl⟩
      · rintro ⟨z, hA, rfl⟩
        exact ⟨z.isLt, by simpa using hA⟩
    have h1 : (Csr.row off tgt (v : ℕ)).length = Csr.rowLen off (v : ℕ) :=
      Csr.length_row off tgt (v : ℕ)
    have h2 : ((Csr.row off tgt (v : ℕ)).toFinset : Set ℕ).ncard
        = (Csr.row off tgt (v : ℕ)).toFinset.card := Set.ncard_coe_finset _
    rw [← h1, ← hcard, ← h2, hset, Set.ncard_image_of_injective _ Fin.val_injective]
  refine
    { zero := h0
      step := ?_
      last := hc.last
      offLen := hoL
      tgtLen := htL
      offGet := ?_
      tgtGet := ?_
      tgtLt := fun p hp => hc.target hp
      sound := ?_
      complete := ?_
      inj := ?_ }
  · intro v
    have hm : off (v : ℕ) ≤ off ((v : ℕ) + 1) := hc.off_le_succ v.isLt
    have := hlen v
    rw [Csr.rowLen] at this
    omega
  · intro i hi
    rw [hoR i hi, hc.offArr, getElem?_arrOf off (by omega)]
  · intro p hp
    rw [htR p hp, hc.tgtArr, getElem?_arrOf tgt hp]
  · intro v p h1 h2 hlt
    have hmem : tgt p ∈ Csr.row off tgt (v : ℕ) := mem_row_iff.mpr ⟨p, h1, h2, rfl⟩
    obtain ⟨hw', hA⟩ := (hadj v (tgt p)).mp hmem
    exact hA
  · intro v u hA
    have hmem : (u : ℕ) ∈ Csr.row off tgt (v : ℕ) :=
      (hadj v (u : ℕ)).mpr ⟨u.isLt, by simpa using hA⟩
    exact mem_row_iff.mp hmem
  · intro v p r h1 h2 h3 h4 heq
    have hnd' := (List.nodup_map_iff_inj_on (List.nodup_range)).mp
      (by rw [← hrow v]; exact hnd v)
    have hlen' : Csr.rowLen off (v : ℕ) = off ((v : ℕ) + 1) - off (v : ℕ) := rfl
    have hp' : p - off (v : ℕ) ∈ List.range (Csr.rowLen off (v : ℕ)) := by
      rw [List.mem_range, hlen']; omega
    have hr' : r - off (v : ℕ) ∈ List.range (Csr.rowLen off (v : ℕ)) := by
      rw [List.mem_range, hlen']; omega
    have := hnd' _ hp' _ hr' (by
      rw [show off (v : ℕ) + (p - off (v : ℕ)) = p by omega,
        show off (v : ℕ) + (r - off (v : ℕ)) = r by omega]
      exact heq)
    omega

/-! ## §2 The emitted-edge bookkeeping

The mate pass emits an undirected edge when its scan reaches the copy
that lies in the *lower* endpoint's row; the state carried through the
scan is therefore indexed by the slot pointer. -/

/-- The scan has passed the slot of row `a` that holds `b`. -/
def SeenAt (off tgt : ℕ → ℕ) (j a b : ℕ) : Prop :=
  ∃ p, p < j ∧ off a ≤ p ∧ p < off (a + 1) ∧ tgt p = b

/-- **The edge `{a, b}` has been emitted** by the time the scan reaches
slot `j`: the scan has passed the copy in the lower endpoint's row. -/
def Seen (off tgt : ℕ → ℕ) (j a b : ℕ) : Prop :=
  (a < b ∧ SeenAt off tgt j a b) ∨ (b < a ∧ SeenAt off tgt j b a)

theorem Seen.symm {off tgt : ℕ → ℕ} {j a b : ℕ} (h : Seen off tgt j a b) :
    Seen off tgt j b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem seen_mono {off tgt : ℕ → ℕ} {j j' a b : ℕ} (hj : j ≤ j')
    (h : Seen off tgt j a b) : Seen off tgt j' a b := by
  rcases h with ⟨hlt, p, hp, h1, h2, h3⟩ | ⟨hlt, p, hp, h1, h2, h3⟩
  · exact Or.inl ⟨hlt, p, by omega, h1, h2, h3⟩
  · exact Or.inr ⟨hlt, p, by omega, h1, h2, h3⟩

/-- The emitted neighbours of `v` at slot `j`. -/
def seenNb {N : ℕ} (off tgt : ℕ → ℕ) (j : ℕ) (v : Fin N) : Set (Fin N) :=
  {w | Seen off tgt j (v : ℕ) (w : ℕ)}

/-! ## §3 The program -/

/-- The build pass's scratch scalars: the carrier counter, the slot
pointer, the owner, the target cell, and the two slot addresses. -/
def bldScalars : List String := ["bd.i", "bd.j", "bd.u", "bd.w", "bd.p", "bd.q"]

/-- **The rank inversion**: `od[ra[i]] := i`, one scatter store per
vertex — `OrdArr` is `RankArr`'s inverse. -/
def bldOrdCom (nN ra od : String) : Com :=
  .seq (.assign "bd.i" (.lit 0))
    (.while (.lt (.var "bd.i") (.var nN))
      (.seq (.store od (.get ra (.var "bd.i")) (.var "bd.i"))
        (.assign "bd.i" (.add (.var "bd.i") (.lit 1)))))

/-- **The offset copy**: `ao[i] := off[i]` for every `i ≤ N`, the last
cell after the scan (the offsets have `N + 1` entries). -/
def bldOffCom (nN o ao : String) : Com :=
  .seq
    (.seq (.assign "bd.i" (.lit 0))
      (.while (.lt (.var "bd.i") (.var nN))
        (.seq (.store ao (.var "bd.i") (.get o (.var "bd.i")))
          (.assign "bd.i" (.add (.var "bd.i") (.lit 1))))))
    (.store ao (.var nN) (.get o (.var nN)))

/-- **The live-length reset**: `dg[i] := 0`. The mate pass then uses
`dg` itself as its cursor array. -/
def bldDegCom (nN dg : String) : Com :=
  .seq (.assign "bd.i" (.lit 0))
    (.while (.lt (.var "bd.i") (.var nN))
      (.seq (.store dg (.var "bd.i") (.lit 0))
        (.assign "bd.i" (.add (.var "bd.i") (.lit 1)))))

/-- **The emission of one edge, both copies at once**: the two slot
addresses are read off the cursors first, then the two adjacency cells,
then the two mate cells, then the two cursors are bumped. -/
def bldEmit (o aj dg mt : String) : Com :=
  .seq (.assign "bd.p" (.add (.get o (.var "bd.u")) (.get dg (.var "bd.u"))))
    (.seq (.assign "bd.q" (.add (.get o (.var "bd.w")) (.get dg (.var "bd.w"))))
      (.seq (.store aj (.var "bd.p") (.var "bd.w"))
        (.seq (.store aj (.var "bd.q") (.var "bd.u"))
          (.seq (.store mt (.var "bd.p") (.var "bd.q"))
            (.seq (.store mt (.var "bd.q") (.var "bd.p"))
              (.seq (.store dg (.var "bd.u") (.add (.get dg (.var "bd.u")) (.lit 1)))
                (.store dg (.var "bd.w")
                  (.add (.get dg (.var "bd.w")) (.lit 1)))))))))

/-- One turn of the mate pass (`Lib.Csr`'s `ownerStep` shape): inside
the owner's row, read the target and emit the edge if this is its lower
copy; at the row's end, move the owner on. -/
def bldTurn (o t aj dg mt : String) : Com :=
  .ite (.lt (.var "bd.j") (.get o (.add (.var "bd.u") (.lit 1))))
    (.seq (.assign "bd.w" (.get t (.var "bd.j")))
      (.seq (.ite (.lt (.var "bd.u") (.var "bd.w")) (bldEmit o aj dg mt) .skip)
        (.assign "bd.j" (.add (.var "bd.j") (.lit 1)))))
    (.assign "bd.u" (.add (.var "bd.u") (.lit 1)))

/-- **The mate pass**: one owner-advancing pass over the whole slot
space. -/
def bldMateCom (nS o t aj dg mt : String) : Com :=
  .seq (.assign "bd.u" (.lit 0))
    (.seq (.assign "bd.j" (.lit 0))
      (Csr.scan "bd.j" nS (bldTurn o t aj dg mt)))

/-- **The three region passes**: the offsets, the reset, the mate
pass — the build of the deletable adjacency region proper. -/
def bldAdjCom (nN nS o t ao aj dg mt : String) : Com :=
  .seq (bldOffCom nN o ao)
    (.seq (bldDegCom nN dg) (bldMateCom nS o t aj dg mt))

/-- **The build pass**: the rank inversion, then the three region
passes. -/
def bldCom (nN nS o t ra ao aj dg mt od : String) : Com :=
  .seq (bldOrdCom nN ra od) (bldAdjCom nN nS o t ao aj dg mt)

/-- **The build pass's budget** at `(N, ns)`: three carrier scans at
`12`, `12` and `11` a vertex, and the slot pass at `58` a slot and `58`
a row (its turn costs `54` either way). `O(N + ns)`. -/
def bldK (N ns : ℕ) : ℕ := 93 * N + 58 * ns + 30

/-! ## §4 The three flat passes -/

private theorem getElem?_of_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

section Flat

variable {B : ℕ}

/-- The carried state of the rank inversion: the rank array intact, the
order region long enough, every rank below the counter already
written. -/
private def OrdInv (nN ra od : String) {N : ℕ} (π : Equiv.Perm (Fin N))
    (σ : Env) : Prop :=
  σ.vars nN = N ∧ σ.vars "bd.i" ≤ N ∧ RankArr ra π σ ∧
    N ≤ (σ.arrs od).length ∧
    ∀ v : Fin N, (v : ℕ) < σ.vars "bd.i" →
      (σ.arrs od).getD ((π v : Fin N) : ℕ) 0 = (v : ℕ)

/-- **The rank inversion, discharged**: `od` ends up holding `π`'s
inverse — `OrdArr` — at `12` a vertex. -/
theorem bldOrd_spec (nN ra od : String) {N : ℕ} (π : Equiv.Perm (Fin N))
    (hNB : N < B) (hni : nN ≠ "bd.i") (hro : ra ≠ od) :
    Spec B (fun σ => σ.vars nN = N ∧ RankArr ra π σ ∧ N ≤ (σ.arrs od).length)
      (bldOrdCom nN ra od) (fun _ σ' => OrdArr od π σ') (12 * N + 6) := by
  have hbody : Spec B (fun σ => OrdInv nN ra od π σ ∧ σ.vars "bd.i" < N)
      (.seq (.store od (.get ra (.var "bd.i")) (.var "bd.i"))
        (.assign "bd.i" (.add (.var "bd.i") (.lit 1))))
      (fun σ σ' => OrdInv nN ra od π σ' ∧ σ'.vars "bd.i" = σ.vars "bd.i" + 1) 8 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hn, hle, hra, hod, hcon⟩, hlt⟩ := hσ
    obtain ⟨i, hi⟩ : ∃ i, σ.vars "bd.i" = i := ⟨_, rfl⟩
    rw [hi] at hle hlt hcon
    have hkN : ((π ⟨i, hlt⟩ : Fin N) : ℕ) < N := (π ⟨i, hlt⟩).isLt
    have hrv : (σ.arrs ra).getD i 0 = ((π ⟨i, hlt⟩ : Fin N) : ℕ) := hra.2 ⟨i, hlt⟩
    have hrget : (σ.arrs ra)[i]? = some ((π ⟨i, hlt⟩ : Fin N) : ℕ) := by
      rw [getElem?_of_getD (show i < (σ.arrs ra).length by have := hra.1; omega), hrv]
    have hst : Run B (.store od (.get ra (.var "bd.i")) (.var "bd.i")) σ
        (σ.setArr od ((π ⟨i, hlt⟩ : Fin N) : ℕ) i) 4 := by
      have h := run_store_scatter (B := B) (a := od) (b := ra) (x := "bd.i")
        (σ := σ) (k := ((π ⟨i, hlt⟩ : Fin N) : ℕ)) (by omega)
        (by rw [hi]; exact hrget) (by omega) (by omega)
      rwa [hi] at h
    have h1i : (σ.setArr od ((π ⟨i, hlt⟩ : Fin N) : ℕ) i).vars "bd.i" = i := by
      simp [hi]
    have hinc : Run B (.assign "bd.i" (.add (.var "bd.i") (.lit 1)))
        (σ.setArr od ((π ⟨i, hlt⟩ : Fin N) : ℕ) i)
        ((σ.setArr od ((π ⟨i, hlt⟩ : Fin N) : ℕ) i).setVar "bd.i" (i + 1)) 4 := by
      have h := run_assign_incr (B := B) (x := "bd.i")
        (σ := σ.setArr od ((π ⟨i, hlt⟩ : Fin N) : ℕ) i) (by rw [h1i]; omega)
      rwa [h1i] at h
    refine ⟨_, 8, (hst.seq hinc).mono (by omega), le_rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hni, hn]
    · simp; omega
    · exact ⟨by simpa [hro] using hra.1, fun z => by simpa [hro] using hra.2 z⟩
    · simpa using hod
    · intro z hz
      have hzi : (z : ℕ) < i + 1 := by simpa using hz
      have harr : (((σ.setArr od ((π ⟨i, hlt⟩ : Fin N) : ℕ) i).setVar "bd.i"
          (i + 1)).arrs od) = (σ.arrs od).set ((π ⟨i, hlt⟩ : Fin N) : ℕ) i := by
        simp
      rw [harr]
      rcases Nat.lt_or_ge (z : ℕ) i with hlt' | hge
      · refine (getD_set_of_ne ?_).trans (hcon z (by omega))
        intro hcc
        have hzz : (⟨i, hlt⟩ : Fin N) = z := π.injective (Fin.ext hcc)
        have hval : i = (z : ℕ) := congrArg Fin.val hzz
        omega
      · have hzv : z = (⟨i, hlt⟩ : Fin N) :=
          Fin.ext (show (z : ℕ) = i by omega)
        rw [hzv, getD_set_self (by omega)]
    · simp [hi]
  refine ((Spec.forRangeZero "bd.i" nN (OrdInv nN ra od π) N 8 hNB
    (fun σ hI => hI.2.1) (fun σ hI => hI.1) hbody).pre ?_).post ?_
  · rintro σ ⟨hn, hra, hod⟩
    refine ⟨by simp [hni, hn], by simp, ⟨by simpa using hra.1, fun z => by
      simpa using hra.2 z⟩, by simpa using hod, ?_⟩
    intro z hz
    simp at hz
  · rintro σ σ' - ⟨⟨-, -, -, hod, hcon⟩, hend⟩
    refine ⟨hod, fun z => ?_⟩
    have h := hcon (π.symm z) (by rw [hend]; exact (π.symm z).isLt)
    simpa using h

/-- The carried state of the offset copy. -/
private def OffInv (o t nN ao : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (ns : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  SrcCsr o t G ns off tgt σ ∧ σ.vars nN = N ∧ σ.vars "bd.i" ≤ N ∧
    N + 1 ≤ (σ.arrs ao).length ∧
    ∀ i, i < σ.vars "bd.i" → (σ.arrs ao).getD i 0 = off i

/-- **The offset copy, discharged**: `ao` ends up holding the offsets
on `[0, N]`, at `12` a vertex plus the last cell. -/
theorem bldOff_spec (o t nN ao : String) {N ns : ℕ} {G : SimpleGraph (Fin N)}
    {off tgt : ℕ → ℕ} (hNB : N < B) (hnsB : ns < B) (hni : nN ≠ "bd.i")
    (hao : ao ≠ o) (hat : ao ≠ t) :
    Spec B (fun σ => SrcCsr o t G ns off tgt σ ∧ σ.vars nN = N ∧
        N + 1 ≤ (σ.arrs ao).length)
      (bldOffCom nN o ao)
      (fun _ σ' => SrcCsr o t G ns off tgt σ' ∧
        ∀ i, i ≤ N → (σ'.arrs ao).getD i 0 = off i) (12 * N + 10) := by
  have hbody : Spec B (fun σ => OffInv o t nN ao G ns off tgt σ ∧ σ.vars "bd.i" < N)
      (.seq (.store ao (.var "bd.i") (.get o (.var "bd.i")))
        (.assign "bd.i" (.add (.var "bd.i") (.lit 1))))
      (fun σ σ' => OffInv o t nN ao G ns off tgt σ' ∧
        σ'.vars "bd.i" = σ.vars "bd.i" + 1) 8 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hsrc, hn, hle, hlen, hcon⟩, hlt⟩ := hσ
    obtain ⟨i, hi⟩ : ∃ i, σ.vars "bd.i" = i := ⟨_, rfl⟩
    rw [hi] at hle hlt hcon
    have hoffB : off i < B := lt_of_le_of_lt (hsrc.off_le_ns (by omega)) hnsB
    have hst : Run B (.store ao (.var "bd.i") (.get o (.var "bd.i"))) σ
        (σ.setArr ao i (off i)) 4 := by
      have h := run_store_copy (B := B) (a := ao) (b := o) (x := "bd.i") (σ := σ)
        (v := off i) (by omega) (by rw [hi]; exact hsrc.offGet i (by omega))
        hoffB (by omega)
      rwa [hi] at h
    have h1i : (σ.setArr ao i (off i)).vars "bd.i" = i := by simp [hi]
    have hinc : Run B (.assign "bd.i" (.add (.var "bd.i") (.lit 1)))
        (σ.setArr ao i (off i))
        ((σ.setArr ao i (off i)).setVar "bd.i" (i + 1)) 4 := by
      have h := run_assign_incr (B := B) (x := "bd.i")
        (σ := σ.setArr ao i (off i)) (by rw [h1i]; omega)
      rwa [h1i] at h
    refine ⟨_, 8, (hst.seq hinc).mono (by omega), le_rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hsrc.of_eq (by simp [Ne.symm hao]) (by simp [Ne.symm hat])
    · simp [hni, hn]
    · simp; omega
    · simpa using hlen
    · intro k hk
      have hki : k < i + 1 := by simpa using hk
      have harr : (((σ.setArr ao i (off i)).setVar "bd.i" (i + 1)).arrs ao)
          = (σ.arrs ao).set i (off i) := by simp
      rw [harr]
      rcases Nat.lt_or_ge k i with hlt' | hge
      · exact (getD_set_of_ne (by omega)).trans (hcon k (by omega))
      · obtain rfl : k = i := by omega
        exact getD_set_self (by omega)
    · simp [hi]
  have hloop := Spec.forRangeZero "bd.i" nN (OffInv o t nN ao G ns off tgt) N 8
    hNB (fun σ hI => hI.2.2.1) (fun σ hI => hI.2.1) hbody
  have htail : Spec B (fun σ => OffInv o t nN ao G ns off tgt σ ∧
      σ.vars "bd.i" = N)
      (.store ao (.var nN) (.get o (.var nN)))
      (fun _ σ' => SrcCsr o t G ns off tgt σ' ∧
        ∀ i, i ≤ N → (σ'.arrs ao).getD i 0 = off i) 4 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hsrc, hn, hle, hlen, hcon⟩, hend⟩ := hσ
    have hoffB : off N < B := by rw [hsrc.last]; exact hnsB
    have hst : Run B (.store ao (.var nN) (.get o (.var nN))) σ
        (σ.setArr ao N (off N)) 4 := by
      have h := run_store_copy (B := B) (a := ao) (b := o) (x := nN) (σ := σ)
        (v := off N) (by omega) (by rw [hn]; exact hsrc.offGet N le_rfl)
        hoffB (by omega)
      rwa [hn] at h
    refine ⟨_, 4, hst.mono (by omega), le_rfl, ?_, ?_⟩
    · exact hsrc.of_eq (by simp [Ne.symm hao]) (by simp [Ne.symm hat])
    · intro k hk
      have harr : ((σ.setArr ao N (off N)).arrs ao) = (σ.arrs ao).set N (off N) := by
        simp
      rw [harr]
      rcases Nat.lt_or_ge k N with hlt' | hge
      · exact (getD_set_of_ne (by omega)).trans (hcon k (by omega))
      · obtain rfl : k = N := by omega
        exact getD_set_self (by omega)
  refine ((Spec.seq hloop htail (fun σ σ' _ hq => hq)
    (fun _ _ _ _ _ hq => hq)).pre ?_).mono (by omega)
  rintro σ ⟨hsrc, hn, hlen⟩
  exact ⟨hsrc.of_eq rfl rfl, by simp [hni, hn], by simp, by simpa using hlen,
    by intro k hk; simp at hk⟩

/-- The carried state of the live-length reset. -/
private def DegInv (nN dg : String) (N : ℕ) (σ : Env) : Prop :=
  σ.vars nN = N ∧ σ.vars "bd.i" ≤ N ∧ N ≤ (σ.arrs dg).length ∧
    ∀ i, i < σ.vars "bd.i" → (σ.arrs dg).getD i 0 = 0

/-- **The live-length reset, discharged**, at `11` a vertex. -/
theorem bldDeg_spec (nN dg : String) (N : ℕ) (hNB : N < B) (hni : nN ≠ "bd.i") :
    Spec B (fun σ => σ.vars nN = N ∧ N ≤ (σ.arrs dg).length)
      (bldDegCom nN dg)
      (fun _ σ' => ∀ i, i < N → (σ'.arrs dg).getD i 0 = 0) (11 * N + 6) := by
  have hbody : Spec B (fun σ => DegInv nN dg N σ ∧ σ.vars "bd.i" < N)
      (.seq (.store dg (.var "bd.i") (.lit 0))
        (.assign "bd.i" (.add (.var "bd.i") (.lit 1))))
      (fun σ σ' => DegInv nN dg N σ' ∧ σ'.vars "bd.i" = σ.vars "bd.i" + 1) 7 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hn, hle, hlen, hcon⟩, hlt⟩ := hσ
    obtain ⟨i, hi⟩ : ∃ i, σ.vars "bd.i" = i := ⟨_, rfl⟩
    rw [hi] at hle hlt hcon
    have hst : Run B (.store dg (.var "bd.i") (.lit 0)) σ (σ.setArr dg i 0) 3 := by
      have h := run_store_lit (B := B) (a := dg) (x := "bd.i") (σ := σ) (v := 0)
        (by omega) (by omega) (by omega)
      rwa [hi] at h
    have h1i : (σ.setArr dg i 0).vars "bd.i" = i := by simp [hi]
    have hinc : Run B (.assign "bd.i" (.add (.var "bd.i") (.lit 1)))
        (σ.setArr dg i 0) ((σ.setArr dg i 0).setVar "bd.i" (i + 1)) 4 := by
      have h := run_assign_incr (B := B) (x := "bd.i") (σ := σ.setArr dg i 0)
        (by rw [h1i]; omega)
      rwa [h1i] at h
    refine ⟨_, 7, (hst.seq hinc).mono (by omega), le_rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hni, hn]
    · simp; omega
    · simpa using hlen
    · intro k hk
      have hki : k < i + 1 := by simpa using hk
      have harr : (((σ.setArr dg i 0).setVar "bd.i" (i + 1)).arrs dg)
          = (σ.arrs dg).set i 0 := by simp
      rw [harr]
      rcases Nat.lt_or_ge k i with hlt' | hge
      · exact (getD_set_of_ne (by omega)).trans (hcon k (by omega))
      · obtain rfl : k = i := by omega
        exact getD_set_self (by omega)
    · simp [hi]
  refine ((Spec.forRangeZero "bd.i" nN (DegInv nN dg N) N 7 hNB
    (fun σ hI => hI.2.1) (fun σ hI => hI.1) hbody).pre ?_).post ?_
  · rintro σ ⟨hn, hlen⟩
    exact ⟨by simp [hni, hn], by simp, by simpa using hlen,
      by intro k hk; simp at hk⟩
  · rintro σ σ' - ⟨⟨-, -, -, hcon⟩, hend⟩
    intro k hk
    exact hcon k (by omega)

end Flat


/-! ## §5 The mate pass

The pass keeps, at every slot pointer `j`, exactly the invariant
`DelAdjSt` asks for, with the current graph replaced by the set of
edges already emitted (`Seen`). At `j = ns` that set is the whole edge
set (`seenNb_last`) and the invariant *is* the region. -/

section Mate

variable {o t : String} {N ns : ℕ} {G : SimpleGraph (Fin N)} {off tgt : ℕ → ℕ}
  {σ : Env}

/-- **The owner of a slot is a row**: the extent rules out an owner
that has walked off the end. -/
theorem SrcCsr.owner_lt (h : SrcCsr o t G ns off tgt σ) {u j : ℕ} (hu : u ≤ N)
    (hlo : off u ≤ j) (hj : j < ns) : u < N := by
  rcases Nat.lt_or_ge u N with hlt | hge
  · exact hlt
  · exfalso
    obtain rfl : u = N := by omega
    rw [h.last] at hlo
    omega

/-- Slots of different rows are different slots. -/
theorem SrcCsr.slot_ne (h : SrcCsr o t G ns off tgt σ) {a b : Fin N} {s r : ℕ}
    (hs : off (a : ℕ) + s < off ((a : ℕ) + 1))
    (hr : off (b : ℕ) + r < off ((b : ℕ) + 1)) (hab : (a : ℕ) ≠ (b : ℕ)) :
    off (a : ℕ) + s ≠ off (b : ℕ) + r := by
  intro heq
  exact hab (h.owner_uniq (le_of_lt a.isLt) (le_of_lt b.isLt) (by omega) hs
    (by omega) (by omega))

/-- A passed slot of row `a` holds a neighbour of `a`. -/
theorem SrcCsr.adj_of_seenAt (h : SrcCsr o t G ns off tgt σ) {j : ℕ} {a : Fin N}
    {b : ℕ} (hs : SeenAt off tgt j (a : ℕ) b) : ∃ hb : b < N, G.Adj a ⟨b, hb⟩ := by
  obtain ⟨p, -, h1, h2, h3⟩ := hs
  subst h3
  exact ⟨h.tgtLt p (h.row_lt_ns h2), h.sound a p h1 h2 _⟩

/-- A slot of row `v` holding `z` is an edge `v — z`. -/
theorem SrcCsr.adj_of_slot (h : SrcCsr o t G ns off tgt σ) {v z : Fin N} {p : ℕ}
    (h1 : off (v : ℕ) ≤ p) (h2 : p < off ((v : ℕ) + 1)) (h3 : tgt p = (z : ℕ)) :
    G.Adj v z := by
  have hz : tgt p < N := by rw [h3]; exact z.isLt
  have hA := h.sound v p h1 h2 hz
  have he : (⟨tgt p, hz⟩ : Fin N) = z := Fin.ext h3
  rwa [he] at hA

/-- Every emitted neighbour is a neighbour. -/
theorem seenNb_subset (h : SrcCsr o t G ns off tgt σ) (j : ℕ) (v : Fin N) :
    seenNb off tgt j v ⊆ G.neighborSet v := by
  intro z hz
  rcases hz with ⟨-, hs⟩ | ⟨-, hs⟩
  · obtain ⟨hb, hA⟩ := h.adj_of_seenAt hs
    simpa using hA
  · obtain ⟨hb, hA⟩ := h.adj_of_seenAt hs
    have : G.Adj z v := by simpa using hA
    exact this.symm

/-- The live prefix never outruns its row. -/
theorem seenNb_ncard_le (h : SrcCsr o t G ns off tgt σ) (j : ℕ) (v : Fin N) :
    (seenNb off tgt j v).ncard ≤ (G.neighborSet v).ncard :=
  Set.ncard_le_ncard (seenNb_subset h j v) (Set.toFinite _)

/-- **At the end of the scan every edge has been emitted.** -/
theorem seenNb_last (h : SrcCsr o t G ns off tgt σ) (v : Fin N) :
    seenNb off tgt ns v = G.neighborSet v := by
  refine Set.Subset.antisymm (seenNb_subset h ns v) fun z hz => ?_
  have hA : G.Adj v z := by simpa using hz
  have hne : (v : ℕ) ≠ (z : ℕ) := fun hc => G.ne_of_adj hA (Fin.ext hc)
  rcases Nat.lt_or_ge (v : ℕ) (z : ℕ) with hlt | hge
  · obtain ⟨p, h1, h2, h3⟩ := h.complete v z hA
    exact Or.inl ⟨hlt, p, h.row_lt_ns h2, h1, h2, h3⟩
  · have hlt : (z : ℕ) < (v : ℕ) := by omega
    obtain ⟨p, h1, h2, h3⟩ := h.complete z v hA.symm
    exact Or.inr ⟨hlt, p, h.row_lt_ns h2, h1, h2, h3⟩

/-- **One slot's worth of new information**: passing the slot `j` of
row `u` adds exactly the pair it holds, and only when it is the pair's
lower copy. -/
theorem seenAt_step (h : SrcCsr o t G ns off tgt σ) {j u : ℕ} (hu : u ≤ N)
    (hlo : off u ≤ j) (hhi : j < off (u + 1)) {a b : ℕ} (ha : a ≤ N) :
    SeenAt off tgt (j + 1) a b ↔ SeenAt off tgt j a b ∨ (a = u ∧ tgt j = b) := by
  constructor
  · rintro ⟨p, hp, h1, h2, h3⟩
    rcases Nat.lt_or_ge p j with hlt | hge
    · exact Or.inl ⟨p, hlt, h1, h2, h3⟩
    · obtain rfl : p = j := by omega
      exact Or.inr ⟨h.owner_uniq ha hu h1 h2 hlo hhi, h3⟩
  · rintro (⟨p, hp, h1, h2, h3⟩ | ⟨rfl, h3⟩)
    · exact ⟨p, by omega, h1, h2, h3⟩
    · exact ⟨j, by omega, hlo, hhi, h3⟩

/-- The same, for the undirected relation. -/
theorem seen_step (h : SrcCsr o t G ns off tgt σ) {j u : ℕ} (hu : u ≤ N)
    (hlo : off u ≤ j) (hhi : j < off (u + 1)) {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) :
    Seen off tgt (j + 1) a b ↔
      Seen off tgt j a b ∨
        (u < tgt j ∧ ((a = u ∧ b = tgt j) ∨ (a = tgt j ∧ b = u))) := by
  rw [Seen, Seen, seenAt_step h hu hlo hhi ha, seenAt_step h hu hlo hhi hb]
  constructor
  · rintro (⟨hab, hs | ⟨rfl, rfl⟩⟩ | ⟨hab, hs | ⟨rfl, rfl⟩⟩)
    · exact Or.inl (Or.inl ⟨hab, hs⟩)
    · exact Or.inr ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl (Or.inr ⟨hab, hs⟩)
    · exact Or.inr ⟨hab, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ((⟨hab, hs⟩ | ⟨hab, hs⟩) | ⟨hlt, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl ⟨hab, Or.inl hs⟩
    · exact Or.inr ⟨hab, Or.inl hs⟩
    · exact Or.inl ⟨hlt, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hlt, Or.inr ⟨rfl, rfl⟩⟩

/-- **The slot the scan is at was not emitted before**: its row holds
its target once (`inj`), so the pair it carries is new. -/
theorem not_seen_self (h : SrcCsr o t G ns off tgt σ) {j : ℕ} {uf : Fin N}
    (hlo : off (uf : ℕ) ≤ j) (hhi : j < off ((uf : ℕ) + 1))
    (hlt : (uf : ℕ) < tgt j) : ¬ Seen off tgt j (uf : ℕ) (tgt j) := by
  rintro (⟨-, p, hp, h1, h2, h3⟩ | ⟨hc, -⟩)
  · have := h.inj uf p j h1 h2 hlo hhi h3
    omega
  · omega

/-- **The emit step, abstractly**: the two endpoints gain each other,
every other vertex gains nothing. -/
theorem seenNb_step_emit (h : SrcCsr o t G ns off tgt σ) {j : ℕ} {uf wf : Fin N}
    (hlo : off (uf : ℕ) ≤ j) (hhi : j < off ((uf : ℕ) + 1))
    (hwf : (wf : ℕ) = tgt j) (hlt : (uf : ℕ) < (wf : ℕ)) :
    seenNb off tgt (j + 1) uf = insert wf (seenNb off tgt j uf) ∧
      seenNb off tgt (j + 1) wf = insert uf (seenNb off tgt j wf) ∧
      ∀ v : Fin N, v ≠ uf → v ≠ wf →
        seenNb off tgt (j + 1) v = seenNb off tgt j v := by
  have hu : (uf : ℕ) ≤ N := le_of_lt uf.isLt
  have hstep := fun (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) =>
    seen_step h hu hlo hhi ha hb
  refine ⟨?_, ?_, ?_⟩
  · ext z
    rw [Set.mem_insert_iff]
    show Seen off tgt (j + 1) (uf : ℕ) (z : ℕ) ↔ _
    rw [hstep _ _ hu (le_of_lt z.isLt)]
    constructor
    · rintro (hs | ⟨-, ⟨-, hzz⟩ | ⟨hcc, -⟩⟩)
      · exact Or.inr hs
      · exact Or.inl (Fin.ext (by omega))
      · omega
    · rintro (rfl | hs)
      · exact Or.inr ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩
      · exact Or.inl hs
  · ext z
    rw [Set.mem_insert_iff]
    show Seen off tgt (j + 1) (wf : ℕ) (z : ℕ) ↔ _
    rw [hstep _ _ (le_of_lt wf.isLt) (le_of_lt z.isLt)]
    constructor
    · rintro (hs | ⟨-, ⟨hcc, -⟩ | ⟨-, hzz⟩⟩)
      · exact Or.inr hs
      · omega
      · exact Or.inl (Fin.ext (by omega))
    · rintro (rfl | hs)
      · exact Or.inr ⟨by omega, Or.inr ⟨by omega, rfl⟩⟩
      · exact Or.inl hs
  · intro v hvu hvw
    ext z
    show Seen off tgt (j + 1) (v : ℕ) (z : ℕ) ↔ _
    rw [hstep _ _ (le_of_lt v.isLt) (le_of_lt z.isLt)]
    constructor
    · rintro (hs | ⟨-, ⟨hcc, -⟩ | ⟨hcc, -⟩⟩)
      · exact hs
      · exact absurd (Fin.ext hcc : v = uf) hvu
      · exact absurd (Fin.ext (hcc.trans hwf.symm) : v = wf) hvw
    · exact fun hs => Or.inl hs

/-- **The skip step, abstractly**: the copy in the higher endpoint's
row adds nothing — its edge was emitted at the lower copy. -/
theorem seenNb_step_skip (h : SrcCsr o t G ns off tgt σ) {j : ℕ} {uf : Fin N}
    (hlo : off (uf : ℕ) ≤ j) (hhi : j < off ((uf : ℕ) + 1))
    (hnot : ¬ (uf : ℕ) < tgt j) :
    ∀ v : Fin N, seenNb off tgt (j + 1) v = seenNb off tgt j v := by
  intro v
  ext z
  show Seen off tgt (j + 1) (v : ℕ) (z : ℕ) ↔ _
  rw [seen_step h (le_of_lt uf.isLt) hlo hhi (le_of_lt v.isLt) (le_of_lt z.isLt)]
  constructor
  · rintro (hs | ⟨hc, -⟩)
    · exact hs
    · omega
  · exact fun hs => Or.inl hs

end Mate

/-! ### §5.1 The emit block, as a state transformer -/

/-- The state the emit block leaves: the two addresses in their
scalars, the two adjacency cells, the two mate cells, the two cursors
bumped. -/
def emitEnv (aj dg mt : String) (σ : Env) (u wv du dw pu pw : ℕ) : Env :=
  (((((((σ.setVar "bd.p" pu).setVar "bd.q" pw).setArr aj pu wv).setArr aj pw u).setArr
    mt pu pw).setArr mt pw pu).setArr dg u (du + 1)).setArr dg wv (dw + 1)

section EmitEnv

variable {aj dg mt : String} {σ : Env} {u wv du dw pu pw : ℕ}

@[simp] theorem emitEnv_vars_of_ne {y : String} (h1 : y ≠ "bd.p") (h2 : y ≠ "bd.q") :
    (emitEnv aj dg mt σ u wv du dw pu pw).vars y = σ.vars y := by
  simp [emitEnv, h1, h2]

theorem emitEnv_p : (emitEnv aj dg mt σ u wv du dw pu pw).vars "bd.p" = pu := by
  simp [emitEnv]

theorem emitEnv_q : (emitEnv aj dg mt σ u wv du dw pu pw).vars "bd.q" = pw := by
  simp [emitEnv]

theorem emitEnv_aj (hajdg : aj ≠ dg) (hajmt : aj ≠ mt) :
    (emitEnv aj dg mt σ u wv du dw pu pw).arrs aj
      = ((σ.arrs aj).set pu wv).set pw u := by
  simp [emitEnv, hajdg, hajmt]

theorem emitEnv_mt (hmtdg : mt ≠ dg) (hajmt : aj ≠ mt) :
    (emitEnv aj dg mt σ u wv du dw pu pw).arrs mt
      = ((σ.arrs mt).set pu pw).set pw pu := by
  simp [emitEnv, hmtdg, Ne.symm hajmt]

theorem emitEnv_dg (hajdg : aj ≠ dg) (hmtdg : mt ≠ dg) :
    (emitEnv aj dg mt σ u wv du dw pu pw).arrs dg
      = ((σ.arrs dg).set u (du + 1)).set wv (dw + 1) := by
  simp [emitEnv, Ne.symm hajdg, Ne.symm hmtdg]

theorem emitEnv_other {b : String} (h1 : b ≠ aj) (h2 : b ≠ mt) (h3 : b ≠ dg) :
    (emitEnv aj dg mt σ u wv du dw pu pw).arrs b = σ.arrs b := by
  simp [emitEnv, h1, h2, h3]

end EmitEnv

section EmitRun

variable {o t aj dg mt : String} {B N ns : ℕ} {off : ℕ → ℕ} {σ : Env}
  {u wv du dw : ℕ}

/-- **The emit block runs**, at cost `36`: two address computations,
four stores into the two slot regions, two cursor bumps. -/
theorem bldEmit_run (hajdg : aj ≠ dg) (hajmt : aj ≠ mt) (hmtdg : mt ≠ dg)
    (hu : σ.vars "bd.u" = u) (hw : σ.vars "bd.w" = wv)
    (hoffu : (σ.arrs o)[u]? = some (off u))
    (hoffw : (σ.arrs o)[wv]? = some (off wv))
    (hdgu : (σ.arrs dg).getD u 0 = du) (hdgw : (σ.arrs dg).getD wv 0 = dw)
    (huN : u < N) (hwN : wv < N) (hne : u ≠ wv)
    (hdgL : N ≤ (σ.arrs dg).length) (hajL : ns ≤ (σ.arrs aj).length)
    (hmtL : ns ≤ (σ.arrs mt).length)
    (hpu : off u + du < ns) (hpw : off wv + dw < ns)
    (hnsB : ns < B) (hNB : N < B) (hduB : du + 1 < B) (hdwB : dw + 1 < B) :
    Run B (bldEmit o aj dg mt) σ
      (emitEnv aj dg mt σ u wv du dw (off u + du) (off wv + dw)) 36 := by
  have hdguE : (σ.arrs dg)[u]? = some du := by
    rw [getElem?_of_getD (by omega), hdgu]
  have hdgwE : (σ.arrs dg)[wv]? = some dw := by
    rw [getElem?_of_getD (by omega), hdgw]
  -- 1: the first address
  have s1 : Run B (.assign "bd.p" (.add (.get o (.var "bd.u")) (.get dg (.var "bd.u"))))
      σ (σ.setVar "bd.p" (off u + du)) 6 := by
    have h := run_assign_add (B := B) (z := "bd.p") (a := o) (b := dg) (x := "bd.u")
      (σ := σ) (va := off u) (vb := du) (by rw [hu]; omega) (by rw [hu]; exact hoffu)
      (by rw [hu]; exact hdguE) (by omega)
    exact h
  -- 2: the second address
  have s2 : Run B (.assign "bd.q" (.add (.get o (.var "bd.w")) (.get dg (.var "bd.w"))))
      (σ.setVar "bd.p" (off u + du))
      ((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)) 6 := by
    have hx : (σ.setVar "bd.p" (off u + du)).vars "bd.w" = wv := by simp [hw]
    have h := run_assign_add (B := B) (z := "bd.q") (a := o) (b := dg) (x := "bd.w")
      (σ := σ.setVar "bd.p" (off u + du)) (va := off wv) (vb := dw)
      (by rw [hx]; omega) (by rw [hx]; simpa using hoffw)
      (by rw [hx]; simpa using hdgwE) (by omega)
    exact h
  -- 3–6: the four stores
  have s3 : Run B (.store aj (.var "bd.p") (.var "bd.w"))
      ((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw))
      (((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv) 3 := by
    have hp : ((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).vars "bd.p"
        = off u + du := by simp
    have hq : ((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).vars "bd.w"
        = wv := by simp [hw]
    have h := run_store_var (B := B) (a := aj) (x := "bd.p") (y := "bd.w")
      (σ := ((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)))
      (by rw [hp]; omega) (by rw [hq]; omega) (by rw [hp]; simpa using by omega)
    rwa [hp, hq] at h
  have s4 : Run B (.store aj (.var "bd.q") (.var "bd.u"))
      (((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv)
      ((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u) 3 := by
    have hp : ((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv)).vars "bd.q" = off wv + dw := by simp
    have hq : ((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv)).vars "bd.u" = u := by simp [hu]
    have h := run_store_var (B := B) (a := aj) (x := "bd.q") (y := "bd.u")
      (σ := ((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv)))
      (by rw [hp]; omega) (by rw [hq]; omega) (by rw [hp]; simpa using by omega)
    rwa [hp, hq] at h
  have s5 : Run B (.store mt (.var "bd.p") (.var "bd.q"))
      ((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u)
      (((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)) 3 := by
    have hp : (((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u)).vars "bd.p" = off u + du := by simp
    have hq : (((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u)).vars "bd.q" = off wv + dw := by simp
    have h := run_store_var (B := B) (a := mt) (x := "bd.p") (y := "bd.q")
      (σ := (((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u)))
      (by rw [hp]; omega) (by rw [hq]; omega)
      (by rw [hp]; simpa [Ne.symm hajmt] using by omega)
    rwa [hp, hq] at h
  have s6 : Run B (.store mt (.var "bd.q") (.var "bd.p"))
      (((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw))
      ((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du)) 3 := by
    have hp : ((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw))).vars "bd.q" = off wv + dw := by simp
    have hq : ((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw))).vars "bd.p" = off u + du := by simp
    have h := run_store_var (B := B) (a := mt) (x := "bd.q") (y := "bd.p")
      (σ := ((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw))))
      (by rw [hp]; omega) (by rw [hq]; omega)
      (by rw [hp]; simpa [Ne.symm hajmt] using by omega)
    rwa [hp, hq] at h
  -- 7–8: the two cursor bumps
  have s7 : Run B (.store dg (.var "bd.u") (.add (.get dg (.var "bd.u")) (.lit 1)))
      ((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du))
      (((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du)).setArr dg u
        (du + 1)) 6 := by
    have hp : (((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du))).vars "bd.u" = u := by
      simp [hu]
    have hd : (((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du))).arrs dg
        = σ.arrs dg := by
      simp [Ne.symm hajdg, Ne.symm hmtdg]
    have h := run_store_incr (B := B) (a := dg) (x := "bd.u")
      (σ := (((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du))))
      (va := du) (by rw [hp]; omega) (by rw [hp, hd]; exact hdguE) (by omega)
      (by rw [hp, hd]; omega)
    rwa [hp] at h
  have s8 : Run B (.store dg (.var "bd.w") (.add (.get dg (.var "bd.w")) (.lit 1)))
      (((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du)).setArr dg u (du + 1))
      (emitEnv aj dg mt σ u wv du dw (off u + du) (off wv + dw)) 6 := by
    have hp : ((((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du)).setArr dg u
        (du + 1))).vars "bd.w" = wv := by simp [hw]
    have hd : ((((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du)).setArr dg u
        (du + 1))).arrs dg = (σ.arrs dg).set u (du + 1) := by
      simp [Ne.symm hajdg, Ne.symm hmtdg]
    have h := run_store_incr (B := B) (a := dg) (x := "bd.w")
      (σ := ((((((((σ.setVar "bd.p" (off u + du)).setVar "bd.q" (off wv + dw)).setArr aj
        (off u + du) wv).setArr aj (off wv + dw) u).setArr mt (off u + du)
        (off wv + dw)).setArr mt (off wv + dw) (off u + du)).setArr dg u (du + 1))))
      (va := dw) (by rw [hp]; omega)
      (by rw [hp, hd, List.getElem?_set_ne hne]; exact hdgwE) (by omega)
      (by rw [hp, hd]; simpa using by omega)
    rw [hp] at h
    exact h
  exact ((s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq s8))))))).mono
    (by omega))

end EmitRun

/-! ### §5.2 The invariant of the pass -/

/-- **The carried state of the mate pass**: the source CSR intact, the
slot count in its cell, the two pointers in the owner discipline, and —
with the current neighbourhood replaced by the *emitted* one — exactly
`DelAdjSt`'s degree, soundness-with-mate and completeness clauses. -/
structure MInv (o t nS aj dg mt : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (ns : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The source CSR is never written. -/
  src : SrcCsr o t G ns off tgt σ
  /-- The slot count, in its cell. -/
  nsEq : σ.vars nS = ns
  /-- The three output allocations. -/
  ajLen : ns ≤ (σ.arrs aj).length
  /-- The mate region's allocation. -/
  mtLen : ns ≤ (σ.arrs mt).length
  /-- The cursor region's allocation. -/
  dgLen : N ≤ (σ.arrs dg).length
  /-- The owner is a row or the end. -/
  uLe : σ.vars "bd.u" ≤ N
  /-- The slot pointer is a slot or the end. -/
  jLe : σ.vars "bd.j" ≤ ns
  /-- The owner owns the slot pointer. -/
  lo : off (σ.vars "bd.u") ≤ σ.vars "bd.j"
  /-- The cursor counts the emitted neighbours. -/
  deg : ∀ v : Fin N, (σ.arrs dg).getD (v : ℕ) 0
    = (seenNb off tgt (σ.vars "bd.j") v).ncard
  /-- Every live slot holds an emitted neighbour with a consistent
  mate. -/
  slot : ∀ (v : Fin N) (s : ℕ), s < (σ.arrs dg).getD (v : ℕ) 0 →
    ∃ z : Fin N, Seen off tgt (σ.vars "bd.j") (v : ℕ) (z : ℕ) ∧
      (σ.arrs aj).getD (off (v : ℕ) + s) 0 = (z : ℕ) ∧
      ∃ r, r < (σ.arrs dg).getD (z : ℕ) 0 ∧
        (σ.arrs mt).getD (off (v : ℕ) + s) 0 = off (z : ℕ) + r ∧
        (σ.arrs aj).getD (off (z : ℕ) + r) 0 = (v : ℕ) ∧
        (σ.arrs mt).getD (off (z : ℕ) + r) 0 = off (v : ℕ) + s
  /-- Every emitted neighbour sits in the live prefix. -/
  comp : ∀ v z : Fin N, Seen off tgt (σ.vars "bd.j") (v : ℕ) (z : ℕ) →
    ∃ s, s < (σ.arrs dg).getD (v : ℕ) 0 ∧
      (σ.arrs aj).getD (off (v : ℕ) + s) 0 = (z : ℕ)

section Turn

variable {o t nS aj dg mt : String} {B N ns : ℕ} {G : SimpleGraph (Fin N)}
  {off tgt : ℕ → ℕ} {σ : Env}

/-- A live slot lies in its own row. -/
theorem MInv.row_bound (h : MInv o t nS aj dg mt G ns off tgt σ) (v : Fin N)
    {s : ℕ} (hs : s < (σ.arrs dg).getD (v : ℕ) 0) :
    off (v : ℕ) + s < off ((v : ℕ) + 1) := by
  have h1 := h.deg v
  have h2 := seenNb_ncard_le h.src (σ.vars "bd.j") v
  have h3 := h.src.step v
  omega

variable (hajdg : aj ≠ dg) (hajmt : aj ≠ mt) (hmtdg : mt ≠ dg)
  (hajo : aj ≠ o) (hajt : aj ≠ t) (hmto : mt ≠ o) (hmtt : mt ≠ t)
  (hdgo : dg ≠ o) (hdgt : dg ≠ t)
  (hnSj : nS ≠ "bd.j") (hnSu : nS ≠ "bd.u") (hnSw : nS ≠ "bd.w")
  (hnSp : nS ≠ "bd.p") (hnSq : nS ≠ "bd.q")

include hajdg hajmt hmtdg hajo hajt hmto hmtt hdgo hdgt hnSj hnSu hnSw hnSp hnSq in
/-- **One turn of the mate pass**, in `ownerScan_spec`'s step form: it
either passes a slot — emitting the edge if this is its lower copy — or
moves the owner on, keeps the invariant, and costs at most `54` per
pointer move. -/
theorem bldTurn_step (hNB : N < B) (hnsB : ns < B) :
    ∀ σ, MInv o t nS aj dg mt G ns off tgt σ → σ.vars "bd.j" < ns →
      ∃ σ' K', Run B (bldTurn o t aj dg mt) σ σ' K' ∧
        MInv o t nS aj dg mt G ns off tgt σ' ∧
        σ.vars "bd.j" ≤ σ'.vars "bd.j" ∧ σ.vars "bd.u" ≤ σ'.vars "bd.u" ∧
        (σ.vars "bd.j" < σ'.vars "bd.j" ∨ σ.vars "bd.u" < σ'.vars "bd.u") ∧
        K' ≤ 54 * (σ'.vars "bd.j" - σ.vars "bd.j")
          + 54 * (σ'.vars "bd.u" - σ.vars "bd.u") := by
  intro σ hI hjns
  obtain ⟨u, hu⟩ : ∃ u, σ.vars "bd.u" = u := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, σ.vars "bd.j" = j := ⟨_, rfl⟩
  have hsrc := hI.src
  have huN : u ≤ N := by rw [← hu]; exact hI.uLe
  have hjle : j ≤ ns := by rw [← hj]; exact hI.jLe
  have hlo : off u ≤ j := by rw [← hu, ← hj]; exact hI.lo
  have hjns' : j < ns := by rw [← hj]; exact hjns
  have hult : u < N := hsrc.owner_lt huN hlo hjns'
  have hoffB : ∀ i, i ≤ N → off i < B := fun i hi =>
    lt_of_le_of_lt (hsrc.off_le_ns hi) hnsB
  have hcondval : (Expr.get o (.add (.var "bd.u") (.lit 1))).evalB B σ
      = some (off (u + 1)) := by
    have hx : (Expr.add (.var "bd.u") (.lit 1)).evalB B σ = some (u + 1) := by
      have h := evalB_incr (B := B) (y := "bd.u") (σ := σ) (by omega)
      rwa [hu] at h
    exact evalB_get hx (hsrc.offGet (u + 1) (by omega)) (hoffB _ (by omega))
  have hcond : (Cond.lt (.var "bd.j")
      (.get o (.add (.var "bd.u") (.lit 1)))).evalB B σ
      = some (decide (j < off (u + 1))) := by
    have h := evalB_condLt (evalB_var (B := B) (x := "bd.j") (σ := σ) (by omega))
      hcondval
    rwa [hj] at h
  by_cases hin : j < off (u + 1)
  · -- inside the owner's row
    have hcondT : (Cond.lt (.var "bd.j")
        (.get o (.add (.var "bd.u") (.lit 1)))).evalB B σ = some true := by
      rw [hcond]; simp [hin]
    obtain ⟨wv, hwv⟩ : ∃ wv, tgt j = wv := ⟨_, rfl⟩
    have hwN : wv < N := by rw [← hwv]; exact hsrc.tgtLt j hjns'
    have hread : Run B (.assign "bd.w" (.get t (.var "bd.j"))) σ
        (σ.setVar "bd.w" wv) 3 := by
      have h := run_assign_get (B := B) (z := "bd.w") (a := t) (x := "bd.j")
        (σ := σ) (va := wv) (by omega)
        (by rw [hj, ← hwv]; exact hsrc.tgtGet j hjns') (by omega)
      exact h
    have h1u : (σ.setVar "bd.w" wv).vars "bd.u" = u := by simp [hu]
    have h1w : (σ.setVar "bd.w" wv).vars "bd.w" = wv := by simp
    have h1j : (σ.setVar "bd.w" wv).vars "bd.j" = j := by simp [hj]
    have hcond2 : (Cond.lt (.var "bd.u") (.var "bd.w")).evalB B
        (σ.setVar "bd.w" wv) = some (decide (u < wv)) := by
      have h := evalB_condLt
        (evalB_var (B := B) (x := "bd.u") (σ := σ.setVar "bd.w" wv)
          (by rw [h1u]; omega))
        (evalB_var (B := B) (x := "bd.w") (σ := σ.setVar "bd.w" wv)
          (by rw [h1w]; omega))
      rwa [h1u, h1w] at h
    by_cases hlt : u < wv
    · -- the lower copy: emit the edge
      have hcond2T : (Cond.lt (.var "bd.u") (.var "bd.w")).evalB B
          (σ.setVar "bd.w" wv) = some true := by rw [hcond2]; simp [hlt]
      -- name the two endpoints as vertices
      obtain ⟨uf, huf⟩ : ∃ uf : Fin N, (uf : ℕ) = u := ⟨⟨u, hult⟩, rfl⟩
      obtain ⟨wf, hwf⟩ : ∃ wf : Fin N, (wf : ℕ) = wv := ⟨⟨wv, hwN⟩, rfl⟩
      subst huf
      subst hwf
      obtain ⟨du, hdu⟩ : ∃ du, (σ.arrs dg).getD (uf : ℕ) 0 = du := ⟨_, rfl⟩
      obtain ⟨dw, hdw⟩ : ∃ dw, (σ.arrs dg).getD (wf : ℕ) 0 = dw := ⟨_, rfl⟩
      have hAdj : G.Adj uf wf := hsrc.adj_of_slot hlo hin hwv
      have hnot : wf ∉ seenNb off tgt j uf := by
        have h := not_seen_self hsrc (uf := uf) hlo hin (by rw [hwv]; exact hlt)
        rw [hwv] at h
        exact h
      have hnot' : uf ∉ seenNb off tgt j wf := fun hc => hnot (Seen.symm hc)
      -- the cursors have not reached the ends of their rows
      have hdult : du < (G.neighborSet uf).ncard := by
        rw [← hdu, hI.deg uf, hj]
        exact Set.ncard_lt_ncard
          ((Set.ssubset_iff_of_subset (seenNb_subset hsrc j uf)).mpr
            ⟨wf, by simpa using hAdj, hnot⟩) (Set.toFinite _)
      have hdwlt : dw < (G.neighborSet wf).ncard := by
        rw [← hdw, hI.deg wf, hj]
        exact Set.ncard_lt_ncard
          ((Set.ssubset_iff_of_subset (seenNb_subset hsrc j wf)).mpr
            ⟨uf, by simpa using hAdj.symm, hnot'⟩) (Set.toFinite _)
      have hpu : off (uf : ℕ) + du < off ((uf : ℕ) + 1) := by
        have h := hsrc.step uf
        omega
      have hpw : off (wf : ℕ) + dw < off ((wf : ℕ) + 1) := by
        have h := hsrc.step wf
        omega
      have hpuns : off (uf : ℕ) + du < ns := hsrc.row_lt_ns (v := uf) hpu
      have hpwns : off (wf : ℕ) + dw < ns := hsrc.row_lt_ns (v := wf) hpw
      have hpune : off (uf : ℕ) + du ≠ off (wf : ℕ) + dw :=
        hsrc.slot_ne hpu hpw (by omega)
      have hajL := hI.ajLen
      have hmtL := hI.mtLen
      have hdgL := hI.dgLen
      -- the emitted sets after the step
      obtain ⟨hnbU, hnbW, hnbO⟩ := seenNb_step_emit hsrc hlo hin hwv.symm hlt
      have hseenNew : Seen off tgt (j + 1) (uf : ℕ) (wf : ℕ) := by
        have h : wf ∈ seenNb off tgt (j + 1) uf := by
          rw [hnbU]; exact Set.mem_insert _ _
        exact h
      -- the block runs
      have hemit := bldEmit_run (o := o) (N := N) (ns := ns) hajdg hajmt hmtdg
        h1u h1w (by simpa using hsrc.offGet (uf : ℕ) (le_of_lt hult))
        (by simpa using hsrc.offGet (wf : ℕ) (le_of_lt hwN))
        (by simpa using hdu) (by simpa using hdw) hult hwN (by omega)
        (by simpa using hdgL) (by simpa using hajL) (by simpa using hmtL)
        hpuns hpwns hnsB hNB (by omega) (by omega)
      have hincj : Run B (.assign "bd.j" (.add (.var "bd.j") (.lit 1)))
          (emitEnv aj dg mt (σ.setVar "bd.w" (wf : ℕ)) (uf : ℕ) (wf : ℕ) du dw
            (off (uf : ℕ) + du) (off (wf : ℕ) + dw))
          ((emitEnv aj dg mt (σ.setVar "bd.w" (wf : ℕ)) (uf : ℕ) (wf : ℕ) du dw
            (off (uf : ℕ) + du) (off (wf : ℕ) + dw)).setVar "bd.j" (j + 1)) 4 := by
        have hjj : (emitEnv aj dg mt (σ.setVar "bd.w" (wf : ℕ)) (uf : ℕ) (wf : ℕ)
            du dw (off (uf : ℕ) + du) (off (wf : ℕ) + dw)).vars "bd.j" = j := by
          rw [emitEnv_vars_of_ne (by decide) (by decide), h1j]
        have h := run_assign_incr (B := B) (x := "bd.j")
          (σ := emitEnv aj dg mt (σ.setVar "bd.w" (wf : ℕ)) (uf : ℕ) (wf : ℕ) du dw
            (off (uf : ℕ) + du) (off (wf : ℕ) + dw)) (by rw [hjj]; omega)
        rwa [hjj] at h
      set τ := (emitEnv aj dg mt (σ.setVar "bd.w" (wf : ℕ)) (uf : ℕ) (wf : ℕ) du dw
        (off (uf : ℕ) + du) (off (wf : ℕ) + dw)).setVar "bd.j" (j + 1) with hτdef
      -- the projections of the final state
      have hτj : τ.vars "bd.j" = j + 1 := by rw [hτdef]; simp
      have hτu : τ.vars "bd.u" = (uf : ℕ) := by rw [hτdef]; simp [hu]
      have hτnS : τ.vars nS = ns := by
        rw [hτdef]; simp [hnSj, hnSw, hnSp, hnSq, hI.nsEq]
      have hτaj : τ.arrs aj
          = ((σ.arrs aj).set (off (uf : ℕ) + du) (wf : ℕ)).set
            (off (wf : ℕ) + dw) (uf : ℕ) := by
        rw [hτdef, arrs_setVar, emitEnv_aj hajdg hajmt]; simp
      have hτmt : τ.arrs mt
          = ((σ.arrs mt).set (off (uf : ℕ) + du) (off (wf : ℕ) + dw)).set
            (off (wf : ℕ) + dw) (off (uf : ℕ) + du) := by
        rw [hτdef, arrs_setVar, emitEnv_mt hmtdg hajmt]; simp
      have hτdg : τ.arrs dg
          = ((σ.arrs dg).set (uf : ℕ) (du + 1)).set (wf : ℕ) (dw + 1) := by
        rw [hτdef, arrs_setVar, emitEnv_dg hajdg hmtdg]; simp
      have hτo : τ.arrs o = σ.arrs o := by
        rw [hτdef, arrs_setVar,
          emitEnv_other (Ne.symm hajo) (Ne.symm hmto) (Ne.symm hdgo)]; simp
      have hτt : τ.arrs t = σ.arrs t := by
        rw [hτdef, arrs_setVar,
          emitEnv_other (Ne.symm hajt) (Ne.symm hmtt) (Ne.symm hdgt)]; simp
      -- how the three written regions read back
      have hdgU : (τ.arrs dg).getD (uf : ℕ) 0 = du + 1 := by
        rw [hτdg, getD_set_of_ne (by omega), getD_set_self (by omega)]
      have hdgW : (τ.arrs dg).getD (wf : ℕ) 0 = dw + 1 := by
        rw [hτdg, getD_set_self (by rw [List.length_set]; omega)]
      have hdgO : ∀ k, k ≠ (uf : ℕ) → k ≠ (wf : ℕ) →
          (τ.arrs dg).getD k 0 = (σ.arrs dg).getD k 0 := by
        intro k h1 h2
        rw [hτdg, getD_set_of_ne (Ne.symm h2), getD_set_of_ne (Ne.symm h1)]
      have hdgMono : ∀ v : Fin N,
          (σ.arrs dg).getD (v : ℕ) 0 ≤ (τ.arrs dg).getD (v : ℕ) 0 := by
        intro v
        by_cases h1 : (v : ℕ) = (uf : ℕ)
        · rw [h1, hdgU, hdu]; omega
        by_cases h2 : (v : ℕ) = (wf : ℕ)
        · rw [h2, hdgW, hdw]; omega
        · rw [hdgO _ h1 h2]
      have hold : ∀ (v : Fin N) (s : ℕ), s < (σ.arrs dg).getD (v : ℕ) 0 →
          off (v : ℕ) + s ≠ off (uf : ℕ) + du ∧
            off (v : ℕ) + s ≠ off (wf : ℕ) + dw := by
        intro v s hs
        have hrow := hI.row_bound v hs
        constructor
        · by_cases h1 : (v : ℕ) = (uf : ℕ)
          · rw [h1] at hs ⊢
            rw [hdu] at hs
            omega
          · exact hsrc.slot_ne hrow hpu h1
        · by_cases h2 : (v : ℕ) = (wf : ℕ)
          · rw [h2] at hs ⊢
            rw [hdw] at hs
            omega
          · exact hsrc.slot_ne hrow hpw h2
      have hajOld : ∀ (v : Fin N) (s : ℕ), s < (σ.arrs dg).getD (v : ℕ) 0 →
          (τ.arrs aj).getD (off (v : ℕ) + s) 0
            = (σ.arrs aj).getD (off (v : ℕ) + s) 0 := by
        intro v s hs
        obtain ⟨h1, h2⟩ := hold v s hs
        rw [hτaj, getD_set_of_ne (Ne.symm h2), getD_set_of_ne (Ne.symm h1)]
      have hmtOld : ∀ (v : Fin N) (s : ℕ), s < (σ.arrs dg).getD (v : ℕ) 0 →
          (τ.arrs mt).getD (off (v : ℕ) + s) 0
            = (σ.arrs mt).getD (off (v : ℕ) + s) 0 := by
        intro v s hs
        obtain ⟨h1, h2⟩ := hold v s hs
        rw [hτmt, getD_set_of_ne (Ne.symm h2), getD_set_of_ne (Ne.symm h1)]
      have hajPu : (τ.arrs aj).getD (off (uf : ℕ) + du) 0 = (wf : ℕ) := by
        rw [hτaj, getD_set_of_ne (Ne.symm hpune), getD_set_self (by omega)]
      have hajPw : (τ.arrs aj).getD (off (wf : ℕ) + dw) 0 = (uf : ℕ) := by
        rw [hτaj, getD_set_self (by rw [List.length_set]; omega)]
      have hmtPu : (τ.arrs mt).getD (off (uf : ℕ) + du) 0 = off (wf : ℕ) + dw := by
        rw [hτmt, getD_set_of_ne (Ne.symm hpune), getD_set_self (by omega)]
      have hmtPw : (τ.arrs mt).getD (off (wf : ℕ) + dw) 0 = off (uf : ℕ) + du := by
        rw [hτmt, getD_set_self (by rw [List.length_set]; omega)]
      -- every old live slot survives unchanged
      have hOldSlot : ∀ (v : Fin N) (s : ℕ), s < (σ.arrs dg).getD (v : ℕ) 0 →
          ∃ z : Fin N, Seen off tgt (j + 1) (v : ℕ) (z : ℕ) ∧
            (τ.arrs aj).getD (off (v : ℕ) + s) 0 = (z : ℕ) ∧
            ∃ r, r < (τ.arrs dg).getD (z : ℕ) 0 ∧
              (τ.arrs mt).getD (off (v : ℕ) + s) 0 = off (z : ℕ) + r ∧
              (τ.arrs aj).getD (off (z : ℕ) + r) 0 = (v : ℕ) ∧
              (τ.arrs mt).getD (off (z : ℕ) + r) 0 = off (v : ℕ) + s := by
        intro v s hs
        obtain ⟨z, hz1, hz2, r, hr1, hr2, hr3, hr4⟩ := hI.slot v s hs
        rw [hj] at hz1
        refine ⟨z, seen_mono (by omega) hz1, ?_, r,
          lt_of_lt_of_le hr1 (hdgMono z), ?_, ?_, ?_⟩
        · rw [hajOld v s hs]; exact hz2
        · rw [hmtOld v s hs]; exact hr2
        · rw [hajOld z r hr1]; exact hr3
        · rw [hmtOld z r hr1]; exact hr4
      refine ⟨τ, 54, (Run.ite_true hcondT (hread.seq
        ((Run.ite_true hcond2T hemit).seq hincj))).mono (by simp), ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨hsrc.of_eq hτo hτt, hτnS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hτaj]; simpa using hajL
        · rw [hτmt]; simpa using hmtL
        · rw [hτdg]; simpa using hdgL
        · rw [hτu]; omega
        · rw [hτj]; omega
        · rw [hτu, hτj]; omega
        · -- the cursor still counts the emitted neighbours
          intro v
          rw [hτj]
          by_cases h1 : v = uf
          · subst h1
            rw [hdgU, hnbU, Set.ncard_insert_of_notMem hnot (Set.toFinite _)]
            have h := hI.deg v
            rw [hj, hdu] at h
            omega
          by_cases h2 : v = wf
          · subst h2
            rw [hdgW, hnbW, Set.ncard_insert_of_notMem hnot' (Set.toFinite _)]
            have h := hI.deg v
            rw [hj, hdw] at h
            omega
          · rw [hdgO _ (fun hc => h1 (Fin.ext hc)) (fun hc => h2 (Fin.ext hc)),
              hnbO v h1 h2]
            have h := hI.deg v
            rw [hj] at h
            exact h
        · -- every live slot is sound, with its mate
          intro v s hs
          rw [hτj]
          by_cases h1 : v = uf
          · subst h1
            rw [hdgU] at hs
            rcases Nat.lt_or_ge s du with hlt' | hge
            · exact hOldSlot v s (by rw [hdu]; exact hlt')
            · obtain rfl : s = du := by omega
              exact ⟨wf, hseenNew, hajPu, dw, by rw [hdgW]; omega, hmtPu, hajPw,
                hmtPw⟩
          by_cases h2 : v = wf
          · subst h2
            rw [hdgW] at hs
            rcases Nat.lt_or_ge s dw with hlt' | hge
            · exact hOldSlot v s (by rw [hdw]; exact hlt')
            · obtain rfl : s = dw := by omega
              exact ⟨uf, hseenNew.symm, hajPw, du, by rw [hdgU]; omega, hmtPw,
                hajPu, hmtPu⟩
          · refine hOldSlot v s ?_
            rw [← hdgO _ (fun hc => h1 (Fin.ext hc)) (fun hc => h2 (Fin.ext hc))]
            exact hs
        · -- every emitted neighbour is in the live prefix
          intro v z hz
          rw [hτj] at hz
          have hz' : Seen off tgt (j + 1) (v : ℕ) (z : ℕ) := hz
          rw [seen_step hsrc huN hlo hin (le_of_lt v.isLt) (le_of_lt z.isLt)] at hz'
          rcases hz' with hsold | ⟨-, hnew | hnew⟩
          · obtain ⟨s, hs1, hs2⟩ := hI.comp v z (by rw [hj]; exact hsold)
            exact ⟨s, lt_of_lt_of_le hs1 (hdgMono v), by
              rw [hajOld v s hs1]; exact hs2⟩
          · refine ⟨du, ?_, ?_⟩
            · rw [hnew.1, hdgU]; omega
            · rw [hnew.1, hajPu, hnew.2, hwv]
          · refine ⟨dw, ?_, ?_⟩
            · rw [hnew.1, hwv, hdgW]; omega
            · rw [hnew.1, hwv, hajPw, hnew.2]
      · rw [hj, hτj]; omega
      · rw [hu, hτu]
      · left; rw [hj, hτj]; omega
      · rw [hj, hu, hτj, hτu]; omega
    · -- the higher copy: skip
      have hcond2F : (Cond.lt (.var "bd.u") (.var "bd.w")).evalB B
          (σ.setVar "bd.w" wv) = some false := by rw [hcond2]; simp [hlt]
      have hincj : Run B (.assign "bd.j" (.add (.var "bd.j") (.lit 1)))
          (σ.setVar "bd.w" wv) ((σ.setVar "bd.w" wv).setVar "bd.j" (j + 1)) 4 := by
        have h := run_assign_incr (B := B) (x := "bd.j") (σ := σ.setVar "bd.w" wv)
          (by rw [h1j]; omega)
        rwa [h1j] at h
      have hsame : ∀ v : Fin N,
          seenNb off tgt (j + 1) v = seenNb off tgt j v :=
        seenNb_step_skip hsrc (uf := ⟨u, hult⟩) hlo hin (by rw [hwv]; omega)
      refine ⟨_, 54, (Run.ite_true hcondT (hread.seq
        ((Run.ite_false hcond2F Run.skip).seq hincj))).mono (by simp), ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨hsrc.of_eq rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hnSj, hnSw, hI.nsEq]
        · simpa using hI.ajLen
        · simpa using hI.mtLen
        · simpa using hI.dgLen
        · simp [hu]; omega
        · simp; omega
        · simp [hu]; omega
        · intro v
          rw [show ((σ.setVar "bd.w" wv).setVar "bd.j" (j + 1)).vars "bd.j" = j + 1 by
            simp, hsame v]
          simpa [hj] using hI.deg v
        · intro v s hs
          simp only [arrs_setVar] at hs ⊢
          obtain ⟨z, hz1, hz2, r, hr1, hr2, hr3, hr4⟩ := hI.slot v s hs
          refine ⟨z, ?_, hz2, r, hr1, hr2, hr3, hr4⟩
          rw [show ((σ.setVar "bd.w" wv).setVar "bd.j" (j + 1)).vars "bd.j" = j + 1 by
            simp, ← hj]
          exact seen_mono (by omega) hz1
        · intro v z hz
          rw [show ((σ.setVar "bd.w" wv).setVar "bd.j" (j + 1)).vars "bd.j" = j + 1 by
            simp] at hz
          have hz' : Seen off tgt (σ.vars "bd.j") (v : ℕ) (z : ℕ) := by
            rw [hj]
            have : z ∈ seenNb off tgt (j + 1) v := hz
            rw [hsame v] at this
            exact this
          simpa using hI.comp v z hz'
      · simp [hj]
      · simp [hu]
      · left; simp [hj]
      · simp [hj, hu]
  · -- at the end of the row: advance the owner
    have hcondF : (Cond.lt (.var "bd.j")
        (.get o (.add (.var "bd.u") (.lit 1)))).evalB B σ = some false := by
      rw [hcond]; simp [hin]
    have hadv : Run B (.assign "bd.u" (.add (.var "bd.u") (.lit 1))) σ
        (σ.setVar "bd.u" (u + 1)) 4 := by
      have h := run_assign_incr (B := B) (x := "bd.u") (σ := σ) (by omega)
      rwa [hu] at h
    refine ⟨_, 54, (Run.ite_false hcondF hadv).mono (by simp), ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨hsrc.of_eq rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hnSu, hI.nsEq]
      · simpa using hI.ajLen
      · simpa using hI.mtLen
      · simpa using hI.dgLen
      · simp; omega
      · simp [hj]; omega
      · simp [hj]; omega
      · intro v; simpa [hj] using hI.deg v
      · intro v s hs
        simp only [arrs_setVar] at hs ⊢
        obtain ⟨z, hz1, hz2, r, hr1, hr2, hr3, hr4⟩ := hI.slot v s hs
        exact ⟨z, by simpa using hz1, hz2, r, hr1, hr2, hr3, hr4⟩
      · intro v z hz
        simp only [vars_setVar] at hz
        simpa using hI.comp v z (by simpa using hz)
    · simp [hj]
    · simp [hu]
    · right; simp [hu]
    · simp [hj, hu]

end Turn

/-! ### §5.3 The pass -/

section Pass

variable {o t nS aj dg mt : String} {B N ns : ℕ} {G : SimpleGraph (Fin N)}
  {off tgt : ℕ → ℕ} {σ : Env}

@[simp] theorem seenNb_zero (off tgt : ℕ → ℕ) (v : Fin N) :
    seenNb off tgt 0 v = ∅ := by
  ext z
  constructor
  · rintro (⟨-, p, hp, -, -, -⟩ | ⟨-, p, hp, -, -, -⟩) <;>
      exact absurd hp (Nat.not_lt_zero p)
  · exact fun h => absurd h (Set.notMem_empty z)

/-- **At the end of the scan the invariant is the region**: every edge
has been emitted (`seenNb_last`), so the degree, soundness-with-mate
and completeness clauses are `DelAdjSt`'s at `S = ∅`. -/
theorem delAdjSt_of_MInv (ao : String)
    (h : MInv o t nS aj dg mt G ns off tgt σ) (hend : σ.vars "bd.j" = ns)
    (haoL : N + 1 ≤ (σ.arrs ao).length)
    (hao : ∀ i, i ≤ N → (σ.arrs ao).getD i 0 = off i) :
    DelAdjSt ao aj dg mt G ∅ σ := by
  have hsrc := h.src
  have hseen : ∀ (v z : Fin N), Seen off tgt (σ.vars "bd.j") (v : ℕ) (z : ℕ) ↔
      G.Adj v z := by
    intro v z
    rw [hend]
    constructor
    · intro hs
      have : z ∈ seenNb off tgt ns v := hs
      rw [seenNb_last hsrc v] at this
      simpa using this
    · intro hA
      have : z ∈ seenNb off tgt ns v := by rw [seenNb_last hsrc v]; simpa using hA
      exact this
  refine ⟨off, hsrc.zero, hsrc.step, haoL, hao, ?_, ?_, h.dgLen, ?_, ?_, ?_, ?_⟩
  · rw [hsrc.last]; exact h.ajLen
  · rw [hsrc.last]; exact h.mtLen
  · intro v hv; exact absurd hv (Set.notMem_empty v)
  · rintro v -
    rw [Impl.deleteVerts_empty, h.deg v, hend, seenNb_last hsrc v]
  · rintro v - s hs
    obtain ⟨z, hz1, hz2, r, hr1, hr2, hr3, hr4⟩ := h.slot v s hs
    exact ⟨z, by rw [Impl.deleteVerts_empty]; exact (hseen v z).mp hz1, hz2, r, hr1,
      hr2, hr3, hr4⟩
  · rintro v - z hA
    rw [Impl.deleteVerts_empty] at hA
    exact h.comp v z ((hseen v z).mpr hA)

/-- What the mate pass is started in: the source CSR, the slot count in
its cell, the three allocations, and a zeroed cursor region. -/
def MPre (o t nS aj dg mt : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (ns : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  SrcCsr o t G ns off tgt σ ∧ σ.vars nS = ns ∧
    ns ≤ (σ.arrs aj).length ∧ ns ≤ (σ.arrs mt).length ∧
    N ≤ (σ.arrs dg).length ∧ ∀ i, i < N → (σ.arrs dg).getD i 0 = 0

variable (hajdg : aj ≠ dg) (hajmt : aj ≠ mt) (hmtdg : mt ≠ dg)
  (hajo : aj ≠ o) (hajt : aj ≠ t) (hmto : mt ≠ o) (hmtt : mt ≠ t)
  (hdgo : dg ≠ o) (hdgt : dg ≠ t)
  (hnSj : nS ≠ "bd.j") (hnSu : nS ≠ "bd.u") (hnSw : nS ≠ "bd.w")
  (hnSp : nS ≠ "bd.p") (hnSq : nS ≠ "bd.q")

include hajdg hajmt hmtdg hajo hajt hmto hmtt hdgo hdgt hnSj hnSu hnSw hnSp hnSq in
/-- **The mate pass, discharged**: one owner-advancing pass leaves the
invariant at `j = ns`, at `58` a slot and `58` a row. -/
theorem bldMate_spec (hNB : N < B) (hnsB : ns < B) :
    Spec B (MPre o t nS aj dg mt G ns off tgt) (bldMateCom nS o t aj dg mt)
      (fun _ σ' => MInv o t nS aj dg mt G ns off tgt σ' ∧ σ'.vars "bd.j" = ns)
      (58 * ns + 58 * N + 8) := by
  have hA1 : Spec B (MPre o t nS aj dg mt G ns off tgt) (.assign "bd.u" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "bd.u" 0) 2 :=
    (Spec.assign (f := fun _ => 0) (fun σ _ => evalB_lit (by omega))).mono (by simp)
  have hA2 : Spec B (fun σ => MPre o t nS aj dg mt G ns off tgt σ ∧
      σ.vars "bd.u" = 0) (.assign "bd.j" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "bd.j" 0) 2 :=
    (Spec.assign (f := fun _ => 0) (fun σ _ => evalB_lit (by omega))).mono (by simp)
  have hscan := Csr.ownerScan_spec B (58 * ns + 58 * N + 4) N ns 54 54 "bd.j" nS
    "bd.u" (bldTurn o t aj dg mt)
    (P := fun σ => MInv o t nS aj dg mt G ns off tgt σ ∧
      σ.vars "bd.u" = 0 ∧ σ.vars "bd.j" = 0)
    (MInv o t nS aj dg mt G ns off tgt) hnsB
    (fun σ hI => ⟨hI.nsEq, hI.jLe, hI.uLe⟩)
    (bldTurn_step hajdg hajmt hmtdg hajo hajt hmto hmtt hdgo hdgt hnSj hnSu hnSw
      hnSp hnSq hNB hnsB)
    (fun σ hσ => hσ.1)
    (fun σ hσ => by rw [hσ.2.1, hσ.2.2]; omega)
  have hinner : Spec B (fun σ => MPre o t nS aj dg mt G ns off tgt σ ∧
      σ.vars "bd.u" = 0)
      (.seq (.assign "bd.j" (.lit 0)) (Csr.scan "bd.j" nS (bldTurn o t aj dg mt)))
      (fun _ σ' => MInv o t nS aj dg mt G ns off tgt σ' ∧ σ'.vars "bd.j" = ns)
      (2 + (58 * ns + 58 * N + 4)) := by
    refine Spec.seq hA2 hscan ?_ (fun _ _ _ _ _ hq => hq)
    rintro σ σ' ⟨⟨hsrc, hnsE, hajL, hmtL, hdgL, hzero⟩, hu0⟩ rfl
    have hu0' : (σ.setVar "bd.j" 0).vars "bd.u" = 0 := by simp [hu0]
    have hj0' : (σ.setVar "bd.j" 0).vars "bd.j" = 0 := by simp
    refine ⟨⟨hsrc.of_eq rfl rfl, by simp [hnSj, hnsE], by simpa using hajL,
      by simpa using hmtL, by simpa using hdgL, by rw [hu0']; omega,
      by rw [hj0']; omega, by rw [hu0', hj0', hsrc.zero], ?_, ?_, ?_⟩,
      hu0', hj0'⟩
    · intro v
      rw [hj0', seenNb_zero, Set.ncard_empty]
      simpa using hzero (v : ℕ) v.isLt
    · intro v s hs
      have : (σ.arrs dg).getD (v : ℕ) 0 = 0 := hzero (v : ℕ) v.isLt
      simp only [arrs_setVar] at hs
      omega
    · intro v z hz
      rw [hj0'] at hz
      exact absurd hz (by
        rintro (⟨-, p, hp, -, -, -⟩ | ⟨-, p, hp, -, -, -⟩) <;>
          exact absurd hp (Nat.not_lt_zero p))
  refine (Spec.seq hA1 hinner ?_ (fun _ _ _ _ _ hq => hq)).mono (by omega)
  rintro σ σ' ⟨hsrc, hnsE, hajL, hmtL, hdgL, hzero⟩ rfl
  exact ⟨⟨hsrc.of_eq rfl rfl, by simp [hnSu, hnsE], by simpa using hajL,
    by simpa using hmtL, by simpa using hdgL, by simpa using hzero⟩, by simp⟩

end Pass

/-! ## §6 The three passes of the structure, assembled

`AdjBuildIn` (`SolveSweepAdj.lean:308`) is `∀ {N} (G) (ns)` at a fixed
`B` and names no cell holding `N` or `ns`. No IMP+ program meets it
(Finding 1): array lengths are not readable, so a fixed command cannot
know where a carrier ends; and at `N ≥ B` the pass's own indices are
not words. `AdjBuildAt` is the same contract with the two figures in
named cells and inside the word bound — the shape a program can meet,
and the one the residual of §7 actually uses. -/

/-- The two figure cells are none of the build pass's scratch. -/
structure BldCells (nN nS : String) : Prop where
  /-- The carrier cell is not the counter. -/
  nN_i : nN ≠ "bd.i"
  /-- … nor the slot pointer. -/
  nN_j : nN ≠ "bd.j"
  /-- … nor the owner. -/
  nN_u : nN ≠ "bd.u"
  /-- … nor the target cell. -/
  nN_w : nN ≠ "bd.w"
  /-- … nor either address. -/
  nN_p : nN ≠ "bd.p"
  /-- … nor either address. -/
  nN_q : nN ≠ "bd.q"
  /-- The slot-count cell is not the counter. -/
  nS_i : nS ≠ "bd.i"
  /-- … nor the slot pointer. -/
  nS_j : nS ≠ "bd.j"
  /-- … nor the owner. -/
  nS_u : nS ≠ "bd.u"
  /-- … nor the target cell. -/
  nS_w : nS ≠ "bd.w"
  /-- … nor either address. -/
  nS_p : nS ≠ "bd.p"
  /-- … nor either address. -/
  nS_q : nS ≠ "bd.q"

theorem BldCells.nN_notMem {nN nS : String} (h : BldCells nN nS) :
    nN ∉ bldScalars := by
  simp only [bldScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.nN_i, h.nN_j, h.nN_u, h.nN_w, h.nN_p, h.nN_q⟩

theorem BldCells.nS_notMem {nN nS : String} (h : BldCells nN nS) :
    nS ∉ bldScalars := by
  simp only [bldScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.nS_i, h.nS_j, h.nS_u, h.nS_w, h.nS_p, h.nS_q⟩

/-- **The build pass's region discipline**: the five regions it writes
are pairwise distinct, and none of them is the arena's CSR pair or the
rank array. -/
structure BldNames (o t ra ao aj dg mt od : String) : Prop where
  /-- The five regions are pairwise distinct. -/
  ao_aj : ao ≠ aj
  /-- The five regions are pairwise distinct. -/
  ao_dg : ao ≠ dg
  /-- The five regions are pairwise distinct. -/
  ao_mt : ao ≠ mt
  /-- The five regions are pairwise distinct. -/
  ao_od : ao ≠ od
  /-- The five regions are pairwise distinct. -/
  aj_dg : aj ≠ dg
  /-- The five regions are pairwise distinct. -/
  aj_mt : aj ≠ mt
  /-- The five regions are pairwise distinct. -/
  aj_od : aj ≠ od
  /-- The five regions are pairwise distinct. -/
  dg_mt : dg ≠ mt
  /-- The five regions are pairwise distinct. -/
  dg_od : dg ≠ od
  /-- The five regions are pairwise distinct. -/
  mt_od : mt ≠ od
  /-- None of them is the CSR offsets. -/
  ao_o : ao ≠ o
  /-- None of them is the CSR targets. -/
  ao_t : ao ≠ t
  /-- None of them is the rank array. -/
  ao_ra : ao ≠ ra
  /-- None of them is the CSR offsets. -/
  aj_o : aj ≠ o
  /-- None of them is the CSR targets. -/
  aj_t : aj ≠ t
  /-- None of them is the rank array. -/
  aj_ra : aj ≠ ra
  /-- None of them is the CSR offsets. -/
  dg_o : dg ≠ o
  /-- None of them is the CSR targets. -/
  dg_t : dg ≠ t
  /-- None of them is the rank array. -/
  dg_ra : dg ≠ ra
  /-- None of them is the CSR offsets. -/
  mt_o : mt ≠ o
  /-- None of them is the CSR targets. -/
  mt_t : mt ≠ t
  /-- None of them is the rank array. -/
  mt_ra : mt ≠ ra
  /-- None of them is the CSR offsets. -/
  od_o : od ≠ o
  /-- None of them is the CSR targets. -/
  od_t : od ≠ t
  /-- None of them is the rank array. -/
  od_ra : od ≠ ra

private theorem lv_ne_lit {s b : String} (hlen : s.length = b.length)
    (hne : s ≠ b) (j : ℕ) : lv s j ≠ b :=
  fun h => hne (lv_inj hlen (h.trans (lv_zero b).symm)).1

/-- The level's two figure cells are never the build pass's scratch —
the `lv` mechanism's distinctness, at bases of one length. -/
theorem bldCells_arenaNames (j : ℕ) :
    BldCells (arenaNames j).nN (arenaNames j).nS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_lit (by decide) (by decide) j

section Frames

variable {nN nS o t ra ao aj dg mt od : String}

theorem not_mem_warrs_bldOrdCom {b : String} (h : b ≠ od) :
    b ∉ (bldOrdCom nN ra od).warrs := by
  simp [bldOrdCom, Com.warrs, h]

theorem not_mem_wvars_bldOrdCom {y : String} (h : y ≠ "bd.i") :
    y ∉ (bldOrdCom nN ra od).wvars := by
  simp [bldOrdCom, Com.wvars, h]

theorem not_mem_warrs_bldOffCom {b : String} (h : b ≠ ao) :
    b ∉ (bldOffCom nN o ao).warrs := by
  simp [bldOffCom, Com.warrs, h]

theorem not_mem_wvars_bldOffCom {y : String} (h : y ≠ "bd.i") :
    y ∉ (bldOffCom nN o ao).wvars := by
  simp [bldOffCom, Com.wvars, h]

theorem not_mem_warrs_bldDegCom {b : String} (h : b ≠ dg) :
    b ∉ (bldDegCom nN dg).warrs := by
  simp [bldDegCom, Com.warrs, h]

theorem not_mem_wvars_bldDegCom {y : String} (h : y ≠ "bd.i") :
    y ∉ (bldDegCom nN dg).wvars := by
  simp [bldDegCom, Com.wvars, h]

theorem not_mem_warrs_bldMateCom {b : String} (h1 : b ≠ aj) (h2 : b ≠ dg)
    (h3 : b ≠ mt) : b ∉ (bldMateCom nS o t aj dg mt).warrs := by
  simp [bldMateCom, bldTurn, bldEmit, Csr.scan, Com.warrs, h1, h2, h3]

theorem not_mem_wvars_bldMateCom {y : String} (h1 : y ≠ "bd.j") (h2 : y ≠ "bd.u")
    (h3 : y ≠ "bd.w") (h4 : y ≠ "bd.p") (h5 : y ≠ "bd.q") :
    y ∉ (bldMateCom nS o t aj dg mt).wvars := by
  simp [bldMateCom, bldTurn, bldEmit, Csr.scan, Com.wvars, h1, h2, h3, h4, h5]

theorem not_mem_warrs_bldCom {b : String} (h1 : b ≠ ao) (h2 : b ≠ aj)
    (h3 : b ≠ dg) (h4 : b ≠ mt) (h5 : b ≠ od) :
    b ∉ (bldCom nN nS o t ra ao aj dg mt od).warrs := by
  simp [bldCom, bldAdjCom, bldOrdCom, bldOffCom, bldDegCom, bldMateCom, bldTurn,
    bldEmit, Csr.scan, Com.warrs, h1, h2, h3, h4, h5]

theorem not_mem_wvars_bldCom {y : String} (h0 : y ≠ "bd.i") (h1 : y ≠ "bd.j")
    (h2 : y ≠ "bd.u") (h3 : y ≠ "bd.w") (h4 : y ≠ "bd.p") (h5 : y ≠ "bd.q") :
    y ∉ (bldCom nN nS o t ra ao aj dg mt od).wvars := by
  simp [bldCom, bldAdjCom, bldOrdCom, bldOffCom, bldDegCom, bldMateCom, bldTurn,
    bldEmit, Csr.scan, Com.wvars, h0, h1, h2, h3, h4, h5]

end Frames

section Assemble

variable {nN nS o t ra ao aj dg mt od : String} {B N ns : ℕ}
  {G : SimpleGraph (Fin N)} {off tgt : ℕ → ℕ}

/-- **The three region passes, composed**: from the source CSR and the
three raw allocations, the deletable adjacency region, at
`81·N + 58·ns + 24`. -/
theorem bldAdj_spec (hnm : BldNames o t ra ao aj dg mt od)
    (hcl : BldCells nN nS) (hNB : N < B) (hnsB : ns < B) :
    Spec B
      (fun σ => SrcCsr o t G ns off tgt σ ∧ σ.vars nN = N ∧ σ.vars nS = ns ∧
        N + 1 ≤ (σ.arrs ao).length ∧ ns ≤ (σ.arrs aj).length ∧
        N ≤ (σ.arrs dg).length ∧ ns ≤ (σ.arrs mt).length)
      (bldAdjCom nN nS o t ao aj dg mt)
      (fun _ σ' => SrcCsr o t G ns off tgt σ' ∧ DelAdjSt ao aj dg mt G ∅ σ')
      (81 * N + 58 * ns + 24) := by
  have h1 := specArrsLength (bldOff_spec (G := G) (off := off) (tgt := tgt) o t nN ao
    hNB hnsB hcl.nN_i hnm.ao_o hnm.ao_t).frame
  have h2 := specArrsLength (bldDeg_spec (B := B) nN dg N hNB hcl.nN_i).frame
  have h3 := specArrsLength (bldMate_spec (G := G) (off := off) (tgt := tgt)
    hnm.aj_dg hnm.aj_mt (Ne.symm hnm.dg_mt) hnm.aj_o hnm.aj_t hnm.mt_o hnm.mt_t
    hnm.dg_o hnm.dg_t hcl.nS_j hcl.nS_u hcl.nS_w hcl.nS_p hcl.nS_q hNB hnsB).frame
  have hinner : Spec B
      (fun σ => SrcCsr o t G ns off tgt σ ∧ σ.vars nN = N ∧ σ.vars nS = ns ∧
        (∀ i, i ≤ N → (σ.arrs ao).getD i 0 = off i) ∧
        N + 1 ≤ (σ.arrs ao).length ∧ ns ≤ (σ.arrs aj).length ∧
        N ≤ (σ.arrs dg).length ∧ ns ≤ (σ.arrs mt).length)
      (.seq (bldDegCom nN dg) (bldMateCom nS o t aj dg mt))
      (fun _ σ' => SrcCsr o t G ns off tgt σ' ∧ DelAdjSt ao aj dg mt G ∅ σ')
      ((11 * N + 6) + (58 * ns + 58 * N + 8)) := by
    refine Spec.seq (h2.pre (fun σ hσ => ⟨hσ.2.1, hσ.2.2.2.2.2.2.1⟩)) h3 ?_ ?_
    · rintro σ σ' ⟨hsrc, hnN', hnS', hao', haoL, hajL, hdgL, hmtL⟩
        ⟨⟨hzero, hfv, hfa, -, -⟩, hlen⟩
      refine ⟨hsrc.of_eq (hfa o (not_mem_warrs_bldDegCom (Ne.symm hnm.dg_o)))
        (hfa t (not_mem_warrs_bldDegCom (Ne.symm hnm.dg_t))), ?_, ?_, ?_, ?_, hzero⟩
      · rw [hfv nS (not_mem_wvars_bldDegCom hcl.nS_i)]; exact hnS'
      · rw [hlen aj]; exact hajL
      · rw [hlen mt]; exact hmtL
      · rw [hlen dg]; exact hdgL
    · rintro σ σ' σ'' ⟨hsrc, hnN', hnS', hao', haoL, hajL, hdgL, hmtL⟩
        ⟨⟨hzero, hfv, hfa, -, -⟩, hlen⟩ ⟨⟨⟨hinv, hend⟩, hfv2, hfa2, -, -⟩, hlen2⟩
      have haoEq : σ''.arrs ao = σ.arrs ao := by
        rw [hfa2 ao (not_mem_warrs_bldMateCom hnm.ao_aj hnm.ao_dg hnm.ao_mt),
          hfa ao (not_mem_warrs_bldDegCom hnm.ao_dg)]
      exact ⟨hinv.src, delAdjSt_of_MInv ao hinv hend (by rw [haoEq]; exact haoL)
        (by rw [haoEq]; exact hao')⟩
  refine Spec.seq (h1.pre (fun σ hσ => ⟨hσ.1, hσ.2.1, hσ.2.2.2.1⟩)) hinner ?_
    (fun _ _ _ _ _ hq => hq) |>.mono (by omega)
  rintro σ σ' ⟨hsrc, hnN', hnS', haoL, hajL, hdgL, hmtL⟩
    ⟨⟨⟨hsrc', hao'⟩, hfv, hfa, -, -⟩, hlen1⟩
  refine ⟨hsrc', ?_, ?_, hao', ?_, ?_, ?_, ?_⟩
  · rw [hfv nN (not_mem_wvars_bldOffCom hcl.nN_i)]; exact hnN'
  · rw [hfv nS (not_mem_wvars_bldOffCom hcl.nS_i)]; exact hnS'
  · rw [hlen1 ao]; exact haoL
  · rw [hlen1 aj]; exact hajL
  · rw [hlen1 dg]; exact hdgL
  · rw [hlen1 mt]; exact hmtL

end Assemble

/-! ## §7 The build contract, at named figure cells -/

/-- **The build contract a program can meet** — `AdjBuildIn`
(`SolveSweepAdj.lean:308`) with the carrier size in the cell `nN`, the
slot count in `nS`, and both inside the word bound. Finding 1: the
landed statement has neither, and no IMP+ command can supply them —
array lengths are unreadable, so a fixed program cannot find the end of
a carrier, and at `N ≥ B` the pass's own indices are not words. -/
def AdjBuildAt (B : ℕ) (nN nS o t ao aj dg mt : String) (bldC : Com)
    (kb : ℕ → ℕ → ℕ) : Prop :=
  ∀ {N : ℕ} (G : SimpleGraph (Fin N)) (ns : ℕ),
    Spec B
      (fun σ => GraphCsr o t G ns σ ∧ σ.vars nN = N ∧ σ.vars nS = ns ∧
        N < B ∧ ns < B ∧
        N + 1 ≤ (σ.arrs ao).length ∧ ns ≤ (σ.arrs aj).length ∧
        N ≤ (σ.arrs dg).length ∧ ns ≤ (σ.arrs mt).length)
      bldC
      (fun _ σ' => GraphCsr o t G ns σ' ∧ DelAdjSt ao aj dg mt G ∅ σ')
      (kb N ns)

theorem not_mem_warrs_bldAdjCom {nN nS o t ao aj dg mt b : String} (h1 : b ≠ ao)
    (h2 : b ≠ aj) (h3 : b ≠ dg) (h4 : b ≠ mt) :
    b ∉ (bldAdjCom nN nS o t ao aj dg mt).warrs := by
  simp [bldAdjCom, bldOffCom, bldDegCom, bldMateCom, bldTurn, bldEmit, Csr.scan,
    Com.warrs, h1, h2, h3, h4]

theorem not_mem_wvars_bldAdjCom {nN nS o t ao aj dg mt y : String} (h0 : y ≠ "bd.i")
    (h1 : y ≠ "bd.j") (h2 : y ≠ "bd.u") (h3 : y ≠ "bd.w") (h4 : y ≠ "bd.p")
    (h5 : y ≠ "bd.q") : y ∉ (bldAdjCom nN nS o t ao aj dg mt).wvars := by
  simp [bldAdjCom, bldOffCom, bldDegCom, bldMateCom, bldTurn, bldEmit, Csr.scan,
    Com.wvars, h0, h1, h2, h3, h4, h5]

/-- **`AdjBuildAt`, discharged** by the three region passes at
`81·N + 58·ns + 24`. -/
theorem adjBuildAt_bldAdjCom {nN nS o t ra ao aj dg mt od : String} {B : ℕ}
    (hnm : BldNames o t ra ao aj dg mt od) (hcl : BldCells nN nS) :
    AdjBuildAt B nN nS o t ao aj dg mt (bldAdjCom nN nS o t ao aj dg mt)
      (fun N ns => 81 * N + 58 * ns + 24) := by
  intro N G ns σ hσ
  obtain ⟨hcsr, hnN, hnS, hNB, hnsB, haoL, hajL, hdgL, hmtL⟩ := hσ
  have hoL : N + 1 ≤ (σ.arrs o).length := by
    obtain ⟨off0, tgt0, hc0, -⟩ := hcsr
    rw [hc0.length_off]
  have htL : ns ≤ (σ.arrs t).length := by
    obtain ⟨off0, tgt0, hc0, -⟩ := hcsr
    rw [hc0.length_tgt]
  obtain ⟨off, tgt, hsrc⟩ :=
    srcCsr_of_graphCsr hcsr hoL htL (fun _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨σ', hrun, ⟨-, hdel⟩, hfv, hfa, -, -⟩ :=
    (bldAdj_spec (G := G) (off := off) (tgt := tgt) hnm hcl hNB hnsB).frame.run
      ⟨hsrc, hnN, hnS, haoL, hajL, hdgL, hmtL⟩
  exact ⟨σ', hrun,
    graphCsr_of_eq hcsr
      (hfa o (not_mem_warrs_bldAdjCom (Ne.symm hnm.ao_o) (Ne.symm hnm.aj_o)
        (Ne.symm hnm.dg_o) (Ne.symm hnm.mt_o)))
      (hfa t (not_mem_warrs_bldAdjCom (Ne.symm hnm.ao_t) (Ne.symm hnm.aj_t)
        (Ne.symm hnm.dg_t) (Ne.symm hnm.mt_t))),
    hdel⟩

/-! ## §8 The residual, discharged -/

theorem RankArr.of_eq {ra : String} {N : ℕ} {π : Equiv.Perm (Fin N)} {σ σ' : Env}
    (h : RankArr ra π σ) (hra : σ'.arrs ra = σ.arrs ra) : RankArr ra π σ' := by
  rw [RankArr, hra]; exact h

theorem OrdArr.of_eq {od : String} {N : ℕ} {π : Equiv.Perm (Fin N)} {σ σ' : Env}
    (h : OrdArr od π σ) (hod : σ'.arrs od = σ.arrs od) : OrdArr od π σ' := by
  rw [OrdArr, hod]; exact h

/-- The two figures of an admissible arena are words. -/
theorem sq_lt_mcB {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {q : ℕ}
    (henc : EncodesGraph x n G) (hq : 1 ≤ q) : n * n < mcB q x := by
  have hlen := henc.length_eq
  have h2 : (x.length + 1) ^ 2 ≤ mcB q x := by
    rw [mcB]
    exact Nat.le_mul_of_pos_left _ hq
  rw [pow_two] at h2
  have h4 : (n + 1) * (n + 1) ≤ (x.length + 1) * (x.length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h5 : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
  omega

/-- The slot count is the degree sum — the figure the pass's budget is
stated at. -/
theorem SrcCsr.off_eq_sum {o t : String} {N ns : ℕ} {G : SimpleGraph (Fin N)}
    {off tgt : ℕ → ℕ} {σ : Env} (h : SrcCsr o t G ns off tgt σ) :
    ∀ k, k ≤ N → off k
      = ∑ i ∈ Finset.range k,
          if hi : i < N then (G.neighborSet ⟨i, hi⟩).ncard else 0 := by
  intro k
  induction k with
  | zero => intro _; simp [h.zero]
  | succ k ih =>
      intro hk
      have hkN : k < N := hk
      rw [Finset.sum_range_succ, ← ih (by omega), dif_pos hkN]
      exact h.step ⟨k, hkN⟩

theorem SrcCsr.ns_eq_sum {o t : String} {N ns : ℕ} {G : SimpleGraph (Fin N)}
    {off tgt : ℕ → ℕ} {σ : Env} (h : SrcCsr o t G ns off tgt σ) :
    ns = ∑ v : Fin N, (G.neighborSet v).ncard := by
  rw [← h.last, h.off_eq_sum N le_rfl,
    Finset.sum_range fun i => if hi : i < N then (G.neighborSet ⟨i, hi⟩).ncard else 0]
  exact Finset.sum_congr rfl fun v _ => by rw [dif_pos v.isLt]

open Classical in
/-- **F6c12 residual 3, discharged verbatim**: the cover sweep's build
pass — the concrete program `bldCom` at budget `bldK` — materializes
the deletable adjacency region of the arena's graph at the empty
deleted set and the order region, preserving the arena, the rank array,
the two output allocations and the peel's scratch. `CovAdjBuildIn` is
concluded **verbatim**, from hypotheses only of the F7-suppliable
kinds: `1 ≤ q` (the schedule constant is positive), the region names'
distinctness, and the build scratch descriptor's two duties — the five
allocations it must provide, and its own transport across the pass's
writes.

The budget counts: three carrier scans (`12`, `12` and `11` a vertex —
the rank inversion, the offset copy, the cursor reset) and one pass
over the slot space at `58` a slot and `58` a row. `O(N + ns)`, with
`ns` the arena's degree sum. -/
theorem covAdjBuildIn_bldCom (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od : ℕ → String) (Sbd Spl : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnm : ∀ j, BldNames (arenaNames j).off (arenaNames j).tgt (ra j)
      (ao j) (aj j) (dg j) (mt j) (od j))
    (hcol : ∀ j, ∀ b ∈ [ao j, aj j, dg j, mt j, od j],
      b ≠ (arenaNames j).col ∧ b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist)
    (hSbd : ∀ j σ, Sbd j σ →
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (ao j)).length ∧
      σ.vars (arenaNames j).nS ≤ (σ.arrs (aj j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (dg j)).length ∧
      σ.vars (arenaNames j).nS ≤ (σ.arrs (mt j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (od j)).length)
    (hSpl : ∀ (j : ℕ) (σ σ' : Env), Spl j σ →
      (∀ b, b ≠ ao j → b ≠ aj j → b ≠ dg j → b ≠ mt j → b ≠ od j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ bldScalars → σ'.vars y = σ.vars y) → Spl j σ') :
    CovAdjBuildIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ra ao aj dg mt od
      Sbd Spl
      (fun j => bldCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
        (arenaNames j).tgt (ra j) (ao j) (aj j) (dg j) (mt j) (od j))
      (fun _ A => bldK A.N (∑ v : Fin A.N, (A.G.neighborSet v).ncard)) := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hArena, hra, hcaL, hcoL, hSb, hSp⟩ := hσ
  have hcl := bldCells_arenaNames j
  have hnmj := hnm j
  -- the two figures, and that they are words
  have henc : EncodesGraph x n G := hx.1
  have hnN : σ.vars (arenaNames j).nN = A.N := hArena.n_eq
  have hNn : A.N ≤ n := hArena.st.N_le_root
  have hxB : x.length + 1 < mcB q x := length_add_one_lt_mcB (three_le_length henc) hq
  have hlenx := henc.length_eq
  have hNB : A.N < mcB q x := by omega
  have hnsq : σ.vars (arenaNames j).nS ≤ A.N * A.N := hArena.ns_le_sq
  have hsq : n * n < mcB q x := sq_lt_mcB henc hq
  have hnsB : σ.vars (arenaNames j).nS < mcB q x := by
    have h : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
    omega
  -- the arena's CSR, read through the window
  have hot : (arenaNames j).tgt ≠ (arenaNames j).off :=
    lv_ne_of_base_ne (by decide) (by decide) j j
  have hoL : A.N + 1 ≤ (σ.arrs (arenaNames j).off).length :=
    hArena.fits _ _ arenaWs_off
  have htL : σ.vars (arenaNames j).nS ≤ (σ.arrs (arenaNames j).tgt).length :=
    hArena.fits _ _ (arenaWs_tgt hot)
  have hcsrw : GraphCsr (arenaNames j).off (arenaNames j).tgt A.G
      (σ.vars (arenaNames j).nS)
      (winA (arenaWs (arenaNames j) ((Headline.headlineSetup C hC φ).pal j) (ℓp j)
        (hbf j) A.N (σ.vars (arenaNames j).nS)) σ) := hArena.st.csr
  obtain ⟨off, tgt, hsrc⟩ :=
    srcCsr_of_graphCsr hcsrw hoL htL
      (fun i hi => by
        rw [arrs_winA_some arenaWs_off, List.getElem?_take_of_lt (by omega)])
      (fun p hp => by
        rw [arrs_winA_some (arenaWs_tgt hot), List.getElem?_take_of_lt hp])
  -- the pass's two halves
  have hordS := specArrsLength (bldOrd_spec (B := mcB q x) (arenaNames j).nN (ra j)
    (od j) ((ord A.N A.G).order) hNB hcl.nN_i (Ne.symm hnmj.od_ra)).frame
  have hadjS := specArrsLength (bldAdj_spec (G := A.G) (off := off) (tgt := tgt)
    hnmj hcl hNB hnsB).frame
  obtain ⟨hSao, hSaj, hSdg, hSmt, hSod⟩ := hSbd j σ hSb
  rw [hnN] at hSao hSdg hSod
  obtain ⟨σ₁, hrun1, ⟨hord1, hfv1, hfa1, -, -⟩, hlen1⟩ :=
    hordS.run ⟨hnN, hra, hSod⟩
  obtain ⟨σ₂, hrun2, ⟨⟨-, hdel2⟩, hfv2, hfa2, -, -⟩, hlen2⟩ :=
    hadjS.run ⟨hsrc.of_eq
        (hfa1 _ (not_mem_warrs_bldOrdCom (Ne.symm hnmj.od_o)))
        (hfa1 _ (not_mem_warrs_bldOrdCom (Ne.symm hnmj.od_t))),
      by rw [hfv1 _ (not_mem_wvars_bldOrdCom hcl.nN_i)]; exact hnN,
      by rw [hfv1 _ (not_mem_wvars_bldOrdCom hcl.nS_i)],
      by rw [hlen1 (ao j)]; exact hSao, by rw [hlen1 (aj j)]; exact hSaj,
      by rw [hlen1 (dg j)]; exact hSdg, by rw [hlen1 (mt j)]; exact hSmt⟩
  -- the composed frame
  have hfa : ∀ b, b ≠ ao j → b ≠ aj j → b ≠ dg j → b ≠ mt j → b ≠ od j →
      σ₂.arrs b = σ.arrs b := by
    intro b h1 h2 h3 h4 h5
    rw [hfa2 b (not_mem_warrs_bldAdjCom h1 h2 h3 h4),
      hfa1 b (not_mem_warrs_bldOrdCom h5)]
  have hfv : ∀ y, y ∉ bldScalars → σ₂.vars y = σ.vars y := by
    intro y hy
    simp only [bldScalars, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hy
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hy
    rw [hfv2 y (not_mem_wvars_bldAdjCom h0 h1 h2 h3 h4 h5),
      hfv1 y (not_mem_wvars_bldOrdCom h0)]
  have hlen : ∀ b, (σ₂.arrs b).length = (σ.arrs b).length := by
    intro b
    rw [hlen2 b, hlen1 b]
  obtain ⟨hcolA, hupA, hhistA⟩ := hcol j (ao j) (by simp)
  obtain ⟨hcolJ, hupJ, hhistJ⟩ := hcol j (aj j) (by simp)
  obtain ⟨hcolD, hupD, hhistD⟩ := hcol j (dg j) (by simp)
  obtain ⟨hcolM, hupM, hhistM⟩ := hcol j (mt j) (by simp)
  obtain ⟨hcolO, hupO, hhistO⟩ := hcol j (od j) (by simp)
  refine ⟨σ₂, (hrun1.seq hrun2).mono ?_, ?_, ?_, ?_, hdel2, ?_, ?_, ?_⟩
  · show _ ≤ 93 * A.N + 58 * (∑ v : Fin A.N, (A.G.neighborSet v).ncard) + 30
    rw [← hsrc.ns_eq_sum]
    omega
  · -- the arena is intact
    exact arenaStW_of_eq hArena (hfv _ hcl.nN_notMem) (hfv _ hcl.nS_notMem)
      (hfa _ (Ne.symm hnmj.ao_o) (Ne.symm hnmj.aj_o) (Ne.symm hnmj.dg_o)
        (Ne.symm hnmj.mt_o) (Ne.symm hnmj.od_o))
      (hfa _ (Ne.symm hnmj.ao_t) (Ne.symm hnmj.aj_t) (Ne.symm hnmj.dg_t)
        (Ne.symm hnmj.mt_t) (Ne.symm hnmj.od_t))
      (hfa _ (Ne.symm hcolA) (Ne.symm hcolJ) (Ne.symm hcolD) (Ne.symm hcolM)
        (Ne.symm hcolO))
      (hfa _ (Ne.symm hupA) (Ne.symm hupJ) (Ne.symm hupD) (Ne.symm hupM)
        (Ne.symm hupO))
      (hfa _ (Ne.symm hhistA) (Ne.symm hhistJ) (Ne.symm hhistD) (Ne.symm hhistM)
        (Ne.symm hhistO))
  · -- the rank array is intact
    exact hra.of_eq (hfa _ (Ne.symm hnmj.ao_ra) (Ne.symm hnmj.aj_ra)
      (Ne.symm hnmj.dg_ra) (Ne.symm hnmj.mt_ra) (Ne.symm hnmj.od_ra))
  · -- the order region
    exact hord1.of_eq (hfa2 _ (not_mem_warrs_bldAdjCom (Ne.symm hnmj.ao_od)
      (Ne.symm hnmj.aj_od) (Ne.symm hnmj.dg_od) (Ne.symm hnmj.mt_od)))
  · rw [hlen (ca j)]; exact hcaL
  · rw [hlen (co j)]; exact hcoL
  · exact hSpl j σ σ₂ hSp hfa hfv

/-! ## §9 Control: the pass really runs

Not mathematics; a check that the build contract is not vacuously
dischargeable — the smallest instance with a real edge, `K₂`, whose
slot space the mate pass traverses, emitting the one edge at its lower
copy (slot `0`, row `0`, target `1`) and skipping the higher one (slot
`1`, row `1`, target `0`). -/

section Control

/-- The control state: the `K₂` CSR, and three raw output regions. -/
private def ctrlEnv : Env :=
  { vars := fun a => if a = "cn" then 2 else if a = "cs" then 2 else 0
    arrs := fun a =>
      if a = "c.o" then [0, 1, 2]
      else if a = "c.t" then [1, 0]
      else if a = "c.ao" then [0, 0, 0]
      else if a = "c.aj" then [0, 0]
      else if a = "c.dg" then [0, 0]
      else if a = "c.mt" then [0, 0]
      else []
    inp := []
    out := [] }

private theorem ctrl_ncard (v : Fin 2) :
    ((⊤ : SimpleGraph (Fin 2)).neighborSet v).ncard = 1 := by
  fin_cases v
  · show ((⊤ : SimpleGraph (Fin 2)).neighborSet 0).ncard = 1
    have h : (⊤ : SimpleGraph (Fin 2)).neighborSet 0 = {1} := by
      ext z; fin_cases z <;> simp
    rw [h, Set.ncard_singleton]
  · show ((⊤ : SimpleGraph (Fin 2)).neighborSet 1).ncard = 1
    have h : (⊤ : SimpleGraph (Fin 2)).neighborSet 1 = {0} := by
      ext z; fin_cases z <;> simp
    rw [h, Set.ncard_singleton]

private theorem ctrl_src :
    SrcCsr "c.o" "c.t" (⊤ : SimpleGraph (Fin 2)) 2 id (fun p => 1 - p) ctrlEnv := by
  refine ⟨rfl, ?_, rfl, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [ctrl_ncard v]
    rfl
  · intro i hi; interval_cases i <;> rfl
  · intro p hp; interval_cases p <;> rfl
  · intro p hp; omega
  · intro v p h1 h2 h3
    have hpv : p = (v : ℕ) := by simp only [id] at h1 h2; omega
    subst hpv
    simp only [SimpleGraph.top_adj, ne_eq, Fin.ext_iff]
    have := v.isLt
    omega
  · intro v z hA
    refine ⟨(v : ℕ), le_rfl, by simp only [id]; omega, ?_⟩
    simp only [SimpleGraph.top_adj, ne_eq, Fin.ext_iff] at hA
    have h1 := v.isLt
    have h2 := z.isLt
    omega
  · intro v p r h1 h2 h3 h4 _
    simp only [id] at h1 h2 h3 h4
    omega

private theorem ctrl_names :
    BldNames "c.o" "c.t" "c.ra" "c.ao" "c.aj" "c.dg" "c.mt" "c.od" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem ctrl_cells : BldCells "cn" "cs" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The build really runs, and really leaves the region**: on `K₂`
at the word bound `3`, the three passes terminate inside their budget
in a state holding the deletable adjacency region — both copies of the
one edge live, each the other's mate. -/
private theorem ctrl_run :
    ∃ σ', Run 3 (bldAdjCom "cn" "cs" "c.o" "c.t" "c.ao" "c.aj" "c.dg" "c.mt")
        ctrlEnv σ' (81 * 2 + 58 * 2 + 24) ∧
      DelAdjSt "c.ao" "c.aj" "c.dg" "c.mt" (⊤ : SimpleGraph (Fin 2)) ∅ σ' := by
  obtain ⟨σ', hrun, -, hdel⟩ :=
    (bldAdj_spec (B := 3) (N := 2) (ns := 2) (G := ⊤) (off := id)
      (tgt := fun p => 1 - p) ctrl_names ctrl_cells (by norm_num)
      (by norm_num)).run
      ⟨ctrl_src, rfl, rfl, by decide, by decide, by decide, by decide⟩
  exact ⟨σ', hrun, hdel⟩

end Control

/-! The leaf's axiom profile. The pass itself uses nothing but the
three of the ambient logic (`adjBuildAt_bldAdjCom`); the residual's own
statement quotes `Headline.headlineSetup`, so — exactly like the landed
`covSweepIn_of_build_peel` it feeds — the headline additionally carries
Lax12's endorsed `uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms adjBuildAt_bldAdjCom

#print axioms covAdjBuildIn_bldCom

end Lax3Proofs.Prog
