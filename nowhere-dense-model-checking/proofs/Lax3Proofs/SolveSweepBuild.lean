import Lax3Proofs.SolveSweepStep

/-!
# F6c11b (part 4) — the build pass, discharged: `CovAdjBuildIn`

`SolveSweepStep` names `CovAdjBuildIn`: per admissible level arena,
from `CovSweepIn`'s exact precondition, materialize the deletable
adjacency region of the arena's graph at the empty deleted set
(`DelAdjSt … ∅`) and invert the rank array into the order region
(`OrdArr`), preserving the arena, the rank array, the two output
allocations and the peel's scratch. This file provides the concrete
program and proves that contract, verbatim, as
`covAdjBuildIn_bldCom` — the `hbld` input of
`covSweepIn_of_build_peel`.

## The program: counting-trick build, `O(N + ns)`

Four passes over the level's regions, every figure read off the named
cells (`nN`, `nS`), never off an array length:

1. **Offset copy** — `ao[i] := off[i]` for `i ≤ N`: the arena CSR's
   offset function *is* the degree-sum offset function `DelAdjSt`
   demands (rows enumerate neighbourhoods without duplicates, so
   `rowLen = deg`).
2. **Cursor zero** — `dg[i] := 0`: `dg` doubles as the per-row write
   cursor of pass 3 and ends as the degree array.
3. **The edge pass** — one owner-advancing scan of the CSR slot space
   (`Lib.Csr.ownerScan_spec`'s discipline: slot pointer `iv`, owner
   `uv`). At a slot `(u, w)` with `w < u` — each undirected edge fires
   exactly once, at its higher endpoint's copy — append the two
   directed copies at their rows' cursors **simultaneously**:
   `aj[ao[u]+dg[u]] := w`, `aj[ao[w]+dg[w]] := u`, the two `mt` mate
   pointers at each other's positions, then bump both cursors. Both
   slot positions are known at that moment, so no sortedness of the
   CSR rows is needed (the landed `GraphCsr` promises none) and the
   mate pass costs `O(1)` per edge — the standard counting trick.
4. **Rank inversion** — `od[ra[i]] := i`: entry `π v` receives `v`,
   so entry `i` holds `π.symm i` — `OrdArr`.

The scan's bookkeeping is the `Trig`/`cntP` layer: an undirected edge
`{v, w}` is *placed* once the scan's slot pointer has passed its
trigger slot (the copy of the smaller endpoint in the larger's row —
unique, since rows have no duplicates), and the loop invariant states
`DelAdjSt`'s slot/mate/completeness clauses relative to the placed
set, which at `j = ns` is the whole edge set.

## The statement's shape

The headline takes only F7-suppliable hypotheses: `1 ≤ q`, pairwise
distinctness among the quantified name families (listed at the
theorem), and the abstract transport `hSplT` for the peel scratch
`Spl` — its written-name lists are the definitions `bldWrittenArrs` /
`bldWrittenVars`, which are exactly what the program writes. `Sbd` is
length-only (`bldSbd`): room for the five output regions at the
level-cell figures. The budget is closed-form affine in the carrier
and the arena's edge mass:
`Kbd j A = 70·Σ_v |N_G(v)| + 50·N + 30`.

The word-room story: every stored value is `≤ ns` or `< N`, and
`ns ≤ N² ≤ n² < (|x|+1)² ≤ mcB q x` (`ArenaStW.ns_le_sq`,
`ArenaSt.N_le_root`, the encoding's length identity, `1 ≤ q`).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax13Proofs.Codegen (getD_eq_getElem)

/-! ## §1 The program -/

/-- Pass 1: copy the CSR offsets into the region `ao` — the loop for
`i < N`, then the closing cell `ao[N] := off[N]`. -/
def bldOffCopy (o ao iv nN : String) : Com :=
  .seq
    (.seq (.assign iv (.lit 0))
      (.while (.lt (.var iv) (.var nN))
        (.seq (.store ao (.var iv) (.get o (.var iv)))
          (.assign iv (.add (.var iv) (.lit 1))))))
    (.store ao (.var nN) (.get o (.var nN)))

/-- Pass 2: zero the cursor/degree region `dg`. -/
def bldDegZero (dg iv nN : String) : Com :=
  .seq (.assign iv (.lit 0))
    (.while (.lt (.var iv) (.var nN))
      (.seq (.store dg (.var iv) (.lit 0))
        (.assign iv (.add (.var iv) (.lit 1)))))

/-- The placement block: both directed copies of the edge `{u, w}`
(`u` in `uv`, `w` in `wv`) appended at their rows' cursors, the two
mate pointers crossed, both cursors bumped. The cursors are read
before either is bumped, so all four positions are the entry state's. -/
def bldPlace (ao aj dg mt uv wv : String) : Com :=
  .seq (.store aj (.add (.get ao (.var uv)) (.get dg (.var uv))) (.var wv))
    (.seq (.store aj (.add (.get ao (.var wv)) (.get dg (.var wv))) (.var uv))
      (.seq (.store mt (.add (.get ao (.var uv)) (.get dg (.var uv)))
          (.add (.get ao (.var wv)) (.get dg (.var wv))))
        (.seq (.store mt (.add (.get ao (.var wv)) (.get dg (.var wv)))
            (.add (.get ao (.var uv)) (.get dg (.var uv))))
          (.seq (.store dg (.var uv) (.add (.get dg (.var uv)) (.lit 1)))
            (.store dg (.var wv) (.add (.get dg (.var wv)) (.lit 1)))))))

/-- One turn of the edge pass: inside the owner's row, read the
target and place the edge iff the target is below the owner; at the
row's end, advance the owner. -/
def bldTurn (t ao aj dg mt iv uv wv : String) : Com :=
  .ite (.lt (.var iv) (.get ao (.add (.var uv) (.lit 1))))
    (.seq (.assign wv (.get t (.var iv)))
      (.seq (.ite (.lt (.var wv) (.var uv)) (bldPlace ao aj dg mt uv wv) .skip)
        (.assign iv (.add (.var iv) (.lit 1)))))
    (.assign uv (.add (.var uv) (.lit 1)))

/-- Pass 3: the owner-advancing scan of the slot space. -/
def bldEdgePass (t ao aj dg mt iv uv wv nS : String) : Com :=
  .seq (.assign uv (.lit 0))
    (.seq (.assign iv (.lit 0))
      (Csr.scan iv nS (bldTurn t ao aj dg mt iv uv wv)))

/-- Pass 4: invert the rank array into the order region. -/
def bldOrdInv (ra od iv nN : String) : Com :=
  .seq (.assign iv (.lit 0))
    (.while (.lt (.var iv) (.var nN))
      (.seq (.store od (.get ra (.var iv)) (.var iv))
        (.assign iv (.add (.var iv) (.lit 1)))))

/-- **The build program** at explicit names: offsets, cursors, the
edge pass, the rank inversion. -/
def bldCoreCom (o t ra ao aj dg mt od iv uv wv nN nS : String) : Com :=
  .seq (bldOffCopy o ao iv nN)
    (.seq (bldDegZero dg iv nN)
      (.seq (bldEdgePass t ao aj dg mt iv uv wv nS)
        (bldOrdInv ra od iv nN)))

/-- The program family at the level names: the arena's CSR pair and
cells, the level's rank/output regions, the three fixed scratch
scalars. -/
def bldCom (ra ao aj dg mt od : ℕ → String) (iv uv wv : String) (j : ℕ) : Com :=
  bldCoreCom (arenaNames j).off (arenaNames j).tgt (ra j) (ao j) (aj j)
    (dg j) (mt j) (od j) iv uv wv (arenaNames j).nN (arenaNames j).nS

/-- The arrays the build pass writes — `hSplT`'s array list. -/
def bldWrittenArrs (ao aj dg mt od : ℕ → String) (j : ℕ) : List String :=
  [ao j, aj j, dg j, mt j, od j]

/-- The scalars the build pass writes — `hSplT`'s scalar list. -/
def bldWrittenVars (iv uv wv : String) (_j : ℕ) : List String := [iv, uv, wv]

/-- **The build scratch descriptor** (length-only, anchored at the
level cells): room for the five output regions at the arena's own
figures. -/
def bldSbd (ao aj dg mt od : ℕ → String) (j : ℕ) (σ : Env) : Prop :=
  σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (ao j)).length ∧
    σ.vars (arenaNames j).nS ≤ (σ.arrs (aj j)).length ∧
    σ.vars (arenaNames j).nN ≤ (σ.arrs (dg j)).length ∧
    σ.vars (arenaNames j).nS ≤ (σ.arrs (mt j)).length ∧
    σ.vars (arenaNames j).nN ≤ (σ.arrs (od j)).length

/-- The core budget at carrier `N` and slot count `ns`. -/
def bldCoreK (N ns : ℕ) : ℕ := 70 * ns + 50 * N + 30

/-! ### The write discipline, off the syntax -/

theorem warrs_bldCoreCom (o t ra ao aj dg mt od iv uv wv nN nS : String) :
    (bldCoreCom o t ra ao aj dg mt od iv uv wv nN nS).warrs
      ⊆ [ao, aj, dg, mt, od] := by
  intro b hb
  simp only [bldCoreCom, bldOffCopy, bldDegZero, bldEdgePass, bldTurn,
    bldPlace, bldOrdInv, Csr.scan, Com.warrs, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem wvars_bldCoreCom (o t ra ao aj dg mt od iv uv wv nN nS : String) :
    (bldCoreCom o t ra ao aj dg mt od iv uv wv nN nS).wvars ⊆ [iv, uv, wv] := by
  intro y hy
  simp only [bldCoreCom, bldOffCopy, bldDegZero, bldEdgePass, bldTurn,
    bldPlace, bldOrdInv, Csr.scan, Com.wvars, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-! ## §2 List plumbing -/

private theorem getElem?_of_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem h]

private theorem getD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) :
    (l.set i v).getD i 0 = v := by
  rw [getD_eq_getElem (by simpa using h), List.getElem_set]
  simp

private theorem getD_set_ne {l : List ℕ} {i k v : ℕ} (h : i ≠ k) :
    (l.set i v).getD k 0 = l.getD k 0 := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · rw [getD_eq_getElem (by simpa using hk), getD_eq_getElem hk,
      List.getElem_set, if_neg h]
  · rw [List.getD_eq_default _ _ (by simpa using hk),
      List.getD_eq_default _ _ (by simpa using hk)]

/-- The counter bump, the shape every pass's loop body ends in. -/
private theorem run_incr {B : ℕ} {iv : String} {σ : Env} {k : ℕ}
    (hk : σ.vars iv = k) (hkB : k + 1 < B) :
    Run B (.assign iv (.add (.var iv) (.lit 1))) σ (σ.setVar iv (k + 1)) 4 := by
  refine (Run.assign ?_).mono (by simp)
  have h1 : (Expr.var iv).evalB B σ = some (σ.vars iv) :=
    evalB_var (B := B) (by omega)
  rw [hk] at h1
  have h := evalB_bin (B := B) (op := .add) h1 (evalB_lit (B := B) (by omega))
    (by simpa using hkB)
  simpa using h

/-! ## §3 The placement bookkeeping: triggers and counts

The scan walks the slot space left to right. The *trigger* of an
undirected edge `{v, w}` is the slot of the copy `(max, min)` — the
smaller endpoint's occurrence in the larger's row, unique because rows
have no duplicates — and the edge is *placed* once the pointer has
passed it. `cntP j v` counts the placed edges at `v`; the pass's
invariant states the region's clauses relative to it. -/

section Count

variable {N : ℕ} (G : SimpleGraph (Fin N)) (off tgt : ℕ → ℕ)

/-- The edge `{v, w}` is placed by scan position `j`: it is an edge,
and its trigger slot — in the row of the larger endpoint, holding the
smaller — is below `j`. -/
private def Trig (j : ℕ) (v w : Fin N) : Prop :=
  G.Adj v w ∧ ∃ p, off (max (v : ℕ) (w : ℕ)) ≤ p ∧
    p < off (max (v : ℕ) (w : ℕ) + 1) ∧ p < j ∧ tgt p = min (v : ℕ) (w : ℕ)

open Classical in
/-- The number of placed edges at `v`. -/
private noncomputable def cntP (j : ℕ) (v : Fin N) : ℕ :=
  (Finset.univ.filter fun w => Trig G off tgt j v w).card

variable {G off tgt}

private theorem trig_adj {j : ℕ} {v w : Fin N} (h : Trig G off tgt j v w) :
    G.Adj v w := h.1

private theorem trig_mono {j j' : ℕ} (hj : j ≤ j') {v w : Fin N}
    (h : Trig G off tgt j v w) : Trig G off tgt j' v w := by
  obtain ⟨hadj, p, h1, h2, h3, h4⟩ := h
  exact ⟨hadj, p, h1, h2, by omega, h4⟩

private theorem trig_symm {j : ℕ} {v w : Fin N} (h : Trig G off tgt j v w) :
    Trig G off tgt j w v := by
  obtain ⟨hadj, p, h1, h2, h3, h4⟩ := h
  refine ⟨hadj.symm, p, ?_, ?_, h3, ?_⟩
  · rwa [Nat.max_comm]
  · rwa [Nat.max_comm]
  · rwa [Nat.min_comm]

open Classical in
private theorem cnt_mono {j j' : ℕ} (hj : j ≤ j') (v : Fin N) :
    cntP G off tgt j v ≤ cntP G off tgt j' v := by
  refine Finset.card_le_card fun w hw => ?_
  rw [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, trig_mono hj hw.2⟩

open Classical in
private theorem cnt_zero (v : Fin N) : cntP G off tgt 0 v = 0 := by
  rw [cntP, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro w - ⟨-, p, -, -, hp, -⟩
  omega

open Classical in
/-- The placed set at `v` sits inside the neighbourhood. -/
private theorem cnt_le (j : ℕ) (v : Fin N) :
    cntP G off tgt j v ≤ (G.neighborSet v).ncard := by
  classical
  rw [show (G.neighborSet v).ncard = (G.neighborSet v).toFinset.card from
    Set.ncard_eq_toFinset_card' _]
  refine Finset.card_le_card fun w hw => ?_
  rw [Finset.mem_filter] at hw
  rw [Set.mem_toFinset]
  exact (trig_adj hw.2 : G.Adj v w)

open Classical in
/-- Strictly, while some neighbour is unplaced. -/
private theorem cnt_lt_of_not_trig {j : ℕ} {v w : Fin N} (hadj : G.Adj v w)
    (hnot : ¬ Trig G off tgt j v w) :
    cntP G off tgt j v < (G.neighborSet v).ncard := by
  classical
  rw [show (G.neighborSet v).ncard = (G.neighborSet v).toFinset.card from
    Set.ncard_eq_toFinset_card' _]
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨w, by rwa [Set.mem_toFinset], by
      rw [Finset.mem_filter]; rintro ⟨-, h⟩; exact hnot h⟩
  · intro u hu
    rw [Finset.mem_filter] at hu
    rw [Set.mem_toFinset]
    exact (trig_adj hu.2 : G.Adj v u)

open Classical in
/-- At the end of the scan every edge is placed, so the count is the
degree. -/
private theorem cnt_eq_ncard_of_all {j : ℕ}
    (hall : ∀ v w : Fin N, G.Adj v w → Trig G off tgt j v w) (v : Fin N) :
    cntP G off tgt j v = (G.neighborSet v).ncard := by
  classical
  rw [show (G.neighborSet v).ncard = (G.neighborSet v).toFinset.card from
    Set.ncard_eq_toFinset_card' _, cntP]
  congr 1
  ext w
  rw [Finset.mem_filter, Set.mem_toFinset]
  exact ⟨fun h => trig_adj h.2, fun h => ⟨Finset.mem_univ w, hall v w h⟩⟩

end Count

/-! ### The CSR-derived facts the counting layer consumes -/

section CsrFacts

variable {N ns : ℕ} {G : SimpleGraph (Fin N)} {off tgt : ℕ → ℕ}

/-- General monotonicity from the stepwise clause. -/
private theorem off_mono (hstep : ∀ i, i < N → off i ≤ off (i + 1)) :
    ∀ k, k ≤ N → ∀ i, i ≤ k → off i ≤ off k := by
  intro k
  induction k with
  | zero =>
      intro _ i hi
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact le_rfl
  | succ m ih =>
      intro hk i hi
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by omega) i (by omega)) (hstep m (by omega))

/-- A slot below `ns` with its row bracket pinned has a unique owner. -/
private theorem owner_unique_pure (hstep : ∀ i, i < N → off i ≤ off (i + 1))
    {p u u' : ℕ} (hu : u < N) (hu' : u' < N)
    (h1 : off u ≤ p) (h2 : p < off (u + 1))
    (h3 : off u' ≤ p) (h4 : p < off (u' + 1)) : u = u' := by
  rcases lt_trichotomy u u' with h | h | h
  · have := off_mono hstep u' (by omega) (u + 1) (by omega)
    omega
  · exact h
  · have := off_mono hstep u (by omega) (u' + 1) (by omega)
    omega

/-- The row of `v` in the slot-function view: reading `Csr.row`
membership as a slot witness. -/
private theorem row_mem_slot {v w : ℕ}
    (h : w ∈ Csr.row off tgt v) :
    ∃ p, off v ≤ p ∧ p < off (v + 1) ∧ tgt p = w :=
  mem_row_iff.mp h

/-- **The offset step is the degree step**: rows enumerate the
neighbourhoods without duplicates, so `off (v+1) = off v + deg v`. -/
private theorem off_step_ncard
    (hstep : ∀ i, i < N → off i ≤ off (i + 1))
    (hnd : ∀ v : Fin N, (Csr.row off tgt (v : ℕ)).Nodup)
    (hadj : ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
    (v : Fin N) :
    off ((v : ℕ) + 1) = off (v : ℕ) + (G.neighborSet v).ncard := by
  classical
  have hlen : (Csr.row off tgt (v : ℕ)).length = Csr.rowLen off (v : ℕ) :=
    Csr.length_row off tgt (v : ℕ)
  have hcard : (Csr.row off tgt (v : ℕ)).toFinset.card
      = (Csr.row off tgt (v : ℕ)).length :=
    List.toFinset_card_of_nodup (hnd v)
  have hset : (Csr.row off tgt (v : ℕ)).toFinset
      = (G.neighborFinset v).map (⟨Fin.val, Fin.val_injective⟩ : Fin N ↪ ℕ) := by
    ext w
    simp only [List.mem_toFinset, hadj, Finset.mem_map,
      SimpleGraph.mem_neighborFinset, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hw, hAdj⟩
      exact ⟨⟨w, hw⟩, hAdj, rfl⟩
    · rintro ⟨u, hAdj, rfl⟩
      exact ⟨u.2, by simpa using hAdj⟩
  have hncard : (G.neighborSet v).ncard = G.degree v := by
    rw [Set.ncard_eq_toFinset_card', SimpleGraph.degree]
    congr 1
  have hrl : Csr.rowLen off (v : ℕ) = (G.neighborSet v).ncard := by
    rw [hncard, ← hlen, ← hcard, hset, Finset.card_map]
    rfl
  have hmono := hstep (v : ℕ) v.isLt
  rw [Csr.rowLen] at hrl
  omega

/-- Within one row, a target determines its slot (rows have no
duplicates). -/
private theorem row_tgt_inj
    (hnd : ∀ v : Fin N, (Csr.row off tgt (v : ℕ)).Nodup)
    {v : Fin N} {p q : ℕ} (hp1 : off (v : ℕ) ≤ p) (hp2 : p < off ((v : ℕ) + 1))
    (hq1 : off (v : ℕ) ≤ q) (hq2 : q < off ((v : ℕ) + 1))
    (heq : tgt p = tgt q) : p = q := by
  have hrow := hnd v
  have hlt₁ : p - off (v : ℕ) < Csr.rowLen off (v : ℕ) := by
    rw [Csr.rowLen]; omega
  have hlt₂ : q - off (v : ℕ) < Csr.rowLen off (v : ℕ) := by
    rw [Csr.rowLen]; omega
  have hlen : (Csr.row off tgt (v : ℕ)).length = Csr.rowLen off (v : ℕ) :=
    Csr.length_row off tgt (v : ℕ)
  have hget : ∀ (k : ℕ) (hk : k < Csr.rowLen off (v : ℕ)),
      (Csr.row off tgt (v : ℕ))[k]'(by omega) = tgt (off (v : ℕ) + k) := by
    intro k hk
    simp [Csr.row, arrOf]
  have h₁ : (Csr.row off tgt (v : ℕ))[p - off (v : ℕ)]'(by omega)
      = (Csr.row off tgt (v : ℕ))[q - off (v : ℕ)]'(by omega) := by
    rw [hget _ hlt₁, hget _ hlt₂,
      Nat.add_sub_cancel' hp1, Nat.add_sub_cancel' hq1, heq]
  have := (List.Nodup.getElem_inj_iff hrow).mp h₁
  omega

end CsrFacts

/-! ### The scan-step characterizations -/

section Step

variable {N ns : ℕ} {G : SimpleGraph (Fin N)} {off tgt : ℕ → ℕ}

/-- The current slot's edge, when it fires: the owner and the target
are adjacent. -/
private theorem adj_of_slot
    (hadj : ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
    {j : ℕ} {u wF : Fin N} (hju : off (u : ℕ) ≤ j)
    (hjhi : j < off ((u : ℕ) + 1)) (hw : tgt j = (wF : ℕ)) :
    G.Adj u wF := by
  have hmem : (wF : ℕ) ∈ Csr.row off tgt (u : ℕ) :=
    mem_row_iff.mpr ⟨j, hju, hjhi, hw⟩
  obtain ⟨hlt, hAdj⟩ := (hadj u (wF : ℕ)).mp hmem
  simpa using hAdj

/-- The firing edge is not yet placed: its trigger is the current
slot itself, and triggers are unique within a row. -/
private theorem not_trig_new
    (hnd : ∀ v : Fin N, (Csr.row off tgt (v : ℕ)).Nodup)
    {j : ℕ} {u wF : Fin N} (hju : off (u : ℕ) ≤ j)
    (hjhi : j < off ((u : ℕ) + 1)) (hw : tgt j = (wF : ℕ))
    (hwu : (wF : ℕ) < (u : ℕ)) : ¬ Trig G off tgt j u wF := by
  rintro ⟨-, p, h1, h2, h3, h4⟩
  rw [Nat.max_eq_left (le_of_lt hwu)] at h1 h2
  rw [Nat.min_eq_right (le_of_lt hwu)] at h4
  have : p = j := row_tgt_inj hnd h1 h2 hju hjhi (by rw [h4, hw])
  omega

/-- **The step characterization, firing case**: passing the slot
`(u, w)` with `w < u` places exactly the edge `{u, w}`. -/
private theorem trig_succ_place
    (hstep : ∀ i, i < N → off i ≤ off (i + 1))
    (hadj : ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
    {j : ℕ} {u wF : Fin N} (hju : off (u : ℕ) ≤ j)
    (hjhi : j < off ((u : ℕ) + 1)) (hw : tgt j = (wF : ℕ))
    (hwu : (wF : ℕ) < (u : ℕ)) (v w' : Fin N) :
    Trig G off tgt (j + 1) v w' ↔
      Trig G off tgt j v w' ∨ (v = u ∧ w' = wF) ∨ (v = wF ∧ w' = u) := by
  constructor
  · rintro ⟨hadj', p, h1, h2, h3, h4⟩
    rcases Nat.lt_or_ge p j with hpj | hpj
    · exact Or.inl ⟨hadj', p, h1, h2, hpj, h4⟩
    · obtain rfl : p = j := by omega
      -- the slot's owner is `u`, its target the row's entry
      have hmxN : max (v : ℕ) (w' : ℕ) < N := by
        have := v.isLt
        have := w'.isLt
        omega
      have hmx : max (v : ℕ) (w' : ℕ) = (u : ℕ) :=
        owner_unique_pure hstep hmxN u.isLt h1 h2 hju hjhi
      have hmn : min (v : ℕ) (w' : ℕ) = (wF : ℕ) := by rw [← h4, hw]
      rcases Nat.le_total (v : ℕ) (w' : ℕ) with hvw | hvw
      · rw [Nat.max_eq_right hvw] at hmx
        rw [Nat.min_eq_left hvw] at hmn
        exact Or.inr (Or.inr ⟨Fin.ext hmn, Fin.ext hmx⟩)
      · rw [Nat.max_eq_left hvw] at hmx
        rw [Nat.min_eq_right hvw] at hmn
        exact Or.inr (Or.inl ⟨Fin.ext hmx, Fin.ext hmn⟩)
  · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact trig_mono (by omega) h
    · exact ⟨adj_of_slot hadj hju hjhi hw, j,
        by rwa [Nat.max_eq_left (le_of_lt hwu)],
        by rwa [Nat.max_eq_left (le_of_lt hwu)], by omega,
        by rwa [Nat.min_eq_right (le_of_lt hwu)]⟩
    · exact ⟨(adj_of_slot hadj hju hjhi hw).symm, j,
        by rwa [Nat.max_eq_right (le_of_lt hwu)],
        by rwa [Nat.max_eq_right (le_of_lt hwu)], by omega,
        by rwa [Nat.min_eq_left (le_of_lt hwu)]⟩

/-- **The step characterization, silent case**: passing a slot whose
target is not below the owner places nothing (the trigger of that
edge lives in the other row). -/
private theorem trig_succ_skip
    (hstep : ∀ i, i < N → off i ≤ off (i + 1))
    {j : ℕ} {u : Fin N} (hju : off (u : ℕ) ≤ j)
    (hjhi : j < off ((u : ℕ) + 1)) (hge : (u : ℕ) ≤ tgt j) (v w' : Fin N) :
    Trig G off tgt (j + 1) v w' ↔ Trig G off tgt j v w' := by
  refine ⟨?_, trig_mono (by omega)⟩
  rintro ⟨hadj', p, h1, h2, h3, h4⟩
  rcases Nat.lt_or_ge p j with hpj | hpj
  · exact ⟨hadj', p, h1, h2, hpj, h4⟩
  · obtain rfl : p = j := by omega
    exfalso
    have hmxN : max (v : ℕ) (w' : ℕ) < N := by
      have := v.isLt
      have := w'.isLt
      omega
    have hmx : max (v : ℕ) (w' : ℕ) = (u : ℕ) :=
      owner_unique_pure hstep hmxN u.isLt h1 h2 hju hjhi
    have hne : (v : ℕ) ≠ (w' : ℕ) := fun hc => hadj'.ne (Fin.ext hc)
    have hminmax : min (v : ℕ) (w' : ℕ) < max (v : ℕ) (w' : ℕ) := by
      rcases Nat.le_total (v : ℕ) (w' : ℕ) with hvw | hvw
      · rw [Nat.max_eq_right hvw, Nat.min_eq_left hvw]; omega
      · rw [Nat.max_eq_left hvw, Nat.min_eq_right hvw]; omega
    rw [← h4, hmx] at hminmax
    omega

open Classical in
/-- The three count movements of a firing step. -/
private theorem cnt_succ_place
    (hstep : ∀ i, i < N → off i ≤ off (i + 1))
    (hnd : ∀ v : Fin N, (Csr.row off tgt (v : ℕ)).Nodup)
    (hadj : ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
    {j : ℕ} {u wF : Fin N} (hju : off (u : ℕ) ≤ j)
    (hjhi : j < off ((u : ℕ) + 1)) (hw : tgt j = (wF : ℕ))
    (hwu : (wF : ℕ) < (u : ℕ)) :
    cntP G off tgt (j + 1) u = cntP G off tgt j u + 1 ∧
      cntP G off tgt (j + 1) wF = cntP G off tgt j wF + 1 ∧
      ∀ v : Fin N, v ≠ u → v ≠ wF →
        cntP G off tgt (j + 1) v = cntP G off tgt j v := by
  have hne : wF ≠ u := fun hc => by rw [hc] at hwu; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [cntP, cntP,
      show (Finset.univ.filter fun w => Trig G off tgt (j + 1) u w)
        = insert wF (Finset.univ.filter fun w => Trig G off tgt j u w) from ?_,
      Finset.card_insert_of_notMem (by
        rw [Finset.mem_filter]
        rintro ⟨-, hc⟩
        exact not_trig_new hnd hju hjhi hw hwu hc)]
    ext w'
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter,
      trig_succ_place hstep hadj hju hjhi hw hwu u w']
    constructor
    · rintro ⟨-, h | ⟨-, rfl⟩ | ⟨hc, -⟩⟩
      · exact Or.inr ⟨Finset.mem_univ _, h⟩
      · exact Or.inl rfl
      · exact absurd hc.symm hne
    · rintro (rfl | ⟨-, h⟩)
      · exact ⟨Finset.mem_univ _, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨Finset.mem_univ _, Or.inl h⟩
  · rw [cntP, cntP,
      show (Finset.univ.filter fun w => Trig G off tgt (j + 1) wF w)
        = insert u (Finset.univ.filter fun w => Trig G off tgt j wF w) from ?_,
      Finset.card_insert_of_notMem (by
        rw [Finset.mem_filter]
        rintro ⟨-, hc⟩
        exact not_trig_new hnd hju hjhi hw hwu (trig_symm hc))]
    ext w'
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter,
      trig_succ_place hstep hadj hju hjhi hw hwu wF w']
    constructor
    · rintro ⟨-, h | ⟨hc, -⟩ | ⟨-, rfl⟩⟩
      · exact Or.inr ⟨Finset.mem_univ _, h⟩
      · exact absurd hc hne
      · exact Or.inl rfl
    · rintro (rfl | ⟨-, h⟩)
      · exact ⟨Finset.mem_univ _, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      · exact ⟨Finset.mem_univ _, Or.inl h⟩
  · intro v hvu hvw
    rw [cntP, cntP]
    congr 1
    ext w'
    rw [Finset.mem_filter, Finset.mem_filter,
      trig_succ_place hstep hadj hju hjhi hw hwu v w']
    constructor
    · rintro ⟨-, h | ⟨hc, -⟩ | ⟨hc, -⟩⟩
      · exact ⟨Finset.mem_univ _, h⟩
      · exact absurd hc hvu
      · exact absurd hc hvw
    · rintro ⟨-, h⟩
      exact ⟨Finset.mem_univ _, Or.inl h⟩

open Classical in
/-- No count moves on a silent step. -/
private theorem cnt_succ_skip
    (hstep : ∀ i, i < N → off i ≤ off (i + 1))
    {j : ℕ} {u : Fin N} (hju : off (u : ℕ) ≤ j)
    (hjhi : j < off ((u : ℕ) + 1)) (hge : (u : ℕ) ≤ tgt j) (v : Fin N) :
    cntP G off tgt (j + 1) v = cntP G off tgt j v := by
  rw [cntP, cntP]
  congr 1
  ext w'
  rw [Finset.mem_filter, Finset.mem_filter,
    trig_succ_skip hstep hju hjhi hge v w']

/-- At `j = ns` every edge is placed. -/
private theorem trig_at_ns
    (hstep : ∀ i, i < N → off i ≤ off (i + 1)) (hlast : off N = ns)
    (hadj : ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
    {v w : Fin N} (h : G.Adj v w) : Trig G off tgt ns v w := by
  have haux : ∀ v w : Fin N, G.Adj v w → (w : ℕ) ≤ (v : ℕ) →
      Trig G off tgt ns v w := by
    intro v w hvw hle
    have hmem : (w : ℕ) ∈ Csr.row off tgt (v : ℕ) :=
      (hadj v (w : ℕ)).mpr ⟨w.isLt, by simpa using hvw⟩
    obtain ⟨p, hp1, hp2, hp3⟩ := mem_row_iff.mp hmem
    have hpns : p < ns := by
      have := off_mono hstep N le_rfl ((v : ℕ) + 1) v.isLt
      omega
    exact ⟨hvw, p, by rwa [Nat.max_eq_left hle],
      by rwa [Nat.max_eq_left hle], hpns, by rwa [Nat.min_eq_right hle]⟩
  rcases Nat.le_total (w : ℕ) (v : ℕ) with hle | hle
  · exact haux v w h hle
  · exact trig_symm (haux w v h.symm hle)

/-- A live position is inside its row. -/
private theorem pos_lt_row_end
    (hoffstep : ∀ v : Fin N,
      off ((v : ℕ) + 1) = off (v : ℕ) + (G.neighborSet v).ncard)
    {j : ℕ} {v : Fin N} {t : ℕ} (ht : t < cntP G off tgt j v) :
    off (v : ℕ) + t < off ((v : ℕ) + 1) := by
  have h1 := cnt_le (G := G) (off := off) (tgt := tgt) j v
  have h2 := hoffstep v
  omega

/-- A row end is inside the slot space. -/
private theorem row_end_le_ns
    (hstep : ∀ i, i < N → off i ≤ off (i + 1)) (hlast : off N = ns)
    (v : Fin N) : off ((v : ℕ) + 1) ≤ ns := by
  have := off_mono hstep N le_rfl ((v : ℕ) + 1) v.isLt
  omega

/-- Positions in distinct rows are distinct. -/
private theorem pos_ne_of_row_ne
    (hstep : ∀ i, i < N → off i ≤ off (i + 1))
    {v v' : Fin N} (hne : v ≠ v') {t t' : ℕ}
    (ht : off (v : ℕ) + t < off ((v : ℕ) + 1))
    (ht' : off (v' : ℕ) + t' < off ((v' : ℕ) + 1)) :
    off (v : ℕ) + t ≠ off (v' : ℕ) + t' := by
  have hvne : (v : ℕ) ≠ (v' : ℕ) := fun hc => hne (Fin.ext hc)
  rcases Nat.lt_or_ge (v : ℕ) (v' : ℕ) with hlt | hge
  · have := off_mono hstep (v' : ℕ) (by omega) ((v : ℕ) + 1) (by omega)
    omega
  · have hlt : (v' : ℕ) < (v : ℕ) := by omega
    have := off_mono hstep (v : ℕ) (by omega) ((v' : ℕ) + 1) (by omega)
    omega

end Step

/-! ## §4 The edge pass -/

/-- The edge-pass invariant: the input regions pinned, the owner
discipline on the two pointers, and the region's clauses relative to
the placed set at the current scan position — `DelAdjSt`'s shape with
`cntP` for the degrees and `Trig` for the current adjacency. -/
private structure BInv (t ao aj dg mt iv uv nS : String) {N : ℕ}
    (G : SimpleGraph (Fin N)) (off tgt : ℕ → ℕ) (ns : ℕ)
    (tL aoL : List ℕ) (σ : Env) : Prop where
  hnS : σ.vars nS = ns
  htA : σ.arrs t = tL
  haoA : σ.arrs ao = aoL
  hu : σ.vars uv ≤ N
  hj : σ.vars iv ≤ ns
  hlo : off (σ.vars uv) ≤ σ.vars iv
  hhi : σ.vars uv < N → σ.vars iv ≤ off (σ.vars uv + 1)
  hajL : ns ≤ (σ.arrs aj).length
  hmtL : ns ≤ (σ.arrs mt).length
  hdgL : N ≤ (σ.arrs dg).length
  hdg : ∀ v : Fin N, (σ.arrs dg).getD (v : ℕ) 0 = cntP G off tgt (σ.vars iv) v
  hsound : ∀ v : Fin N, ∀ t' : ℕ, t' < cntP G off tgt (σ.vars iv) v →
    ∃ w : Fin N, Trig G off tgt (σ.vars iv) v w ∧
      (σ.arrs aj).getD (off (v : ℕ) + t') 0 = (w : ℕ) ∧
      ∃ s : ℕ, s < cntP G off tgt (σ.vars iv) w ∧
        (σ.arrs mt).getD (off (v : ℕ) + t') 0 = off (w : ℕ) + s ∧
        (σ.arrs aj).getD (off (w : ℕ) + s) 0 = (v : ℕ) ∧
        (σ.arrs mt).getD (off (w : ℕ) + s) 0 = off (v : ℕ) + t'
  hcomp : ∀ v w : Fin N, Trig G off tgt (σ.vars iv) v w →
    ∃ t' : ℕ, t' < cntP G off tgt (σ.vars iv) v ∧
      (σ.arrs aj).getD (off (v : ℕ) + t') 0 = (w : ℕ)

section EdgePass

variable {B N ns : ℕ} {t ao aj dg mt iv uv wv nS : String}
  {G : SimpleGraph (Fin N)} {off tgt : ℕ → ℕ} {tL aoL : List ℕ}

/-- A bounded read of a pinned array cell through a scalar index. -/
private theorem evalB_get_pin {a y : String} {σ : Env} {L : List ℕ}
    {k val : ℕ} (hL : σ.arrs a = L) (hy : σ.vars y = k) (hkB : k < B)
    (hk : k < L.length) (hval : L.getD k 0 = val) (hvalB : val < B) :
    (Expr.get a (.var y)).evalB B σ = some val := by
  have h1 : (Expr.var y).evalB B σ = some k := by
    rw [← hy]
    exact evalB_var (by rwa [hy])
  exact evalB_get h1 (by rw [hL, getElem?_of_getD hk, hval]) hvalB

/-- The row-cursor position expression `ao[y] + dg[y]`, evaluated. -/
private theorem evalB_pos {y : String} {σ : Env} {k ov cv : ℕ}
    (hao : σ.arrs ao = aoL) (hy : σ.vars y = k) (hkB : k < B)
    (hk : k < aoL.length) (hov : aoL.getD k 0 = ov) (hovB : ov < B)
    (hdgk : (σ.arrs dg).getD k 0 = cv) (hkdg : k < (σ.arrs dg).length)
    (hcvB : cv < B) (hsumB : ov + cv < B) :
    (Expr.add (.get ao (.var y)) (.get dg (.var y))).evalB B σ
      = some (ov + cv) := by
  have h1 := evalB_get_pin (B := B) hao hy hkB hk hov hovB
  have h2 := evalB_get_pin (B := B) (L := σ.arrs dg) rfl hy hkB hkdg hdgk hcvB
  have h := evalB_bin (op := .add) h1 h2 (by simpa using hsumB)
  simpa using h

variable (hstep : ∀ i, i < N → off i ≤ off (i + 1)) (h0 : off 0 = 0)
  (hlast : off N = ns) (htlt : ∀ p, p < ns → tgt p < N)
  (hnd : ∀ v : Fin N, (Csr.row off tgt (v : ℕ)).Nodup)
  (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt (v : ℕ) ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
  (hoffstep : ∀ v : Fin N,
    off ((v : ℕ) + 1) = off (v : ℕ) + (G.neighborSet v).ncard)
  (htL : ∀ p, p < ns → tL.getD p 0 = tgt p) (htLlen : ns ≤ tL.length)
  (haoL : ∀ i, i ≤ N → aoL.getD i 0 = off i) (haoLen : N + 1 ≤ aoL.length)
  (hNB : N + 1 < B) (hnsB : ns < B)
  (h_t_aj : t ≠ aj) (h_t_mt : t ≠ mt) (h_t_dg : t ≠ dg)
  (h_ao_aj : ao ≠ aj) (h_ao_mt : ao ≠ mt) (h_ao_dg : ao ≠ dg)
  (h_aj_mt : aj ≠ mt) (h_aj_dg : aj ≠ dg) (h_mt_dg : mt ≠ dg)
  (h_iv_uv : iv ≠ uv) (h_iv_wv : iv ≠ wv) (h_uv_wv : uv ≠ wv)
  (h_iv_nS : iv ≠ nS) (h_uv_nS : uv ≠ nS) (h_wv_nS : wv ≠ nS)

include hstep h0 hlast htlt hnd hadj hoffstep htL htLlen haoL haoLen hNB hnsB
  h_t_aj h_t_mt h_t_dg h_ao_aj h_ao_mt h_ao_dg h_aj_mt h_aj_dg h_mt_dg
  h_iv_uv h_iv_wv h_uv_wv h_iv_nS h_uv_nS h_wv_nS in
/-- **One turn of the edge pass**, in `ownerScan_spec`'s step form:
it either consumes one slot — placing the slot's edge when it fires —
or advances the owner, keeps the invariant, and costs `66` per slot,
`11` per row. -/
private theorem bldTurn_step :
    ∀ σ, BInv t ao aj dg mt iv uv nS G off tgt ns tL aoL σ →
      σ.vars iv < ns →
      ∃ σ' K', Run B (bldTurn t ao aj dg mt iv uv wv) σ σ' K' ∧
        BInv t ao aj dg mt iv uv nS G off tgt ns tL aoL σ' ∧
        σ.vars iv ≤ σ'.vars iv ∧ σ.vars uv ≤ σ'.vars uv ∧
        (σ.vars iv < σ'.vars iv ∨ σ.vars uv < σ'.vars uv) ∧
        K' ≤ 66 * (σ'.vars iv - σ.vars iv) + 11 * (σ'.vars uv - σ.vars uv) := by
  intro σ hI hjns
  set u := σ.vars uv with hu_def
  set j := σ.vars iv with hj_def
  -- the owner is a real row
  have huN : u < N := by
    rcases Nat.lt_or_ge u N with h | h
    · exact h
    · exfalso
      have h1 := hI.hu
      have h2 := hI.hlo
      obtain rfl : u = N := by omega
      rw [hlast] at h2
      omega
  -- the guard: `iv < ao[u+1]`
  have hoffu1B : off (u + 1) < B := by
    have h1 : off (u + 1) ≤ ns := by
      have := off_mono hstep N le_rfl (u + 1) (by omega)
      omega
    omega
  have huvB : σ.vars uv < B := by omega
  have hivB : σ.vars iv < B := by omega
  have hu1eval : (Expr.add (.var uv) (.lit 1)).evalB B σ = some (u + 1) := by
    have h1 : (Expr.var uv).evalB B σ = some (σ.vars uv) :=
      evalB_var (B := B) huvB
    rw [← hu_def] at h1
    have h2 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (B := B) (by omega)
    have h := evalB_bin (B := B) (op := .add) h1 h2
      (by simpa using show u + 1 < B by omega)
    simpa using h
  have hguard_rd : (Expr.get ao (.add (.var uv) (.lit 1))).evalB B σ
      = some (off (u + 1)) := by
    refine evalB_get hu1eval ?_ hoffu1B
    rw [hI.haoA, getElem?_of_getD (by omega), haoL (u + 1) (by omega)]
  have hguard : (Cond.lt (.var iv) (.get ao (.add (.var uv) (.lit 1)))).evalB
      B σ = some (decide (j < off (u + 1))) := by
    have h1 : (Expr.var iv).evalB B σ = some (σ.vars iv) :=
      evalB_var (B := B) hivB
    rw [← hj_def] at h1
    exact evalB_condLt h1 hguard_rd
  have hguard_size : (Cond.lt (.var iv)
      (.get ao (.add (.var uv) (.lit 1)))).size = 6 := by simp
  by_cases hslot : j < off (u + 1)
  · -- a slot of the owner's row
    have hguardT : (Cond.lt (.var iv)
        (.get ao (.add (.var uv) (.lit 1)))).evalB B σ = some true := by
      rw [hguard]
      congr 1
      simpa using hslot
    -- read the target
    set wn := tgt j with hwn_def
    have hwN : wn < N := htlt j hjns
    have hread : Run B (.assign wv (.get t (.var iv))) σ
        (σ.setVar wv wn) 3 := by
      refine (Run.assign (evalB_get_pin (B := B) hI.htA rfl
        (by rw [← hj_def]; omega) (by omega) ?_ (by omega))).mono (by simp)
      rw [← hj_def, htL j hjns]
    set σa := σ.setVar wv wn with hσa_def
    have ha_iv : σa.vars iv = j := by
      rw [hσa_def]
      simp [h_iv_wv, hj_def]
    have ha_uv : σa.vars uv = u := by
      rw [hσa_def]
      simp [h_uv_wv, hu_def]
    have ha_wv : σa.vars wv = wn := by rw [hσa_def]; simp
    have ha_arrs : σa.arrs = σ.arrs := by rw [hσa_def]; rfl
    -- the fire test
    have hcond : (Cond.lt (.var wv) (.var uv)).evalB B σa
        = some (decide (wn < u)) := by
      have h1 : (Expr.var wv).evalB B σa = some wn := by
        rw [← ha_wv]
        exact evalB_var (by rw [ha_wv]; omega)
      have h2 : (Expr.var uv).evalB B σa = some u := by
        rw [← ha_uv]
        exact evalB_var (by rw [ha_uv]; omega)
      exact evalB_condLt h1 h2
    by_cases hfire : wn < u
    · -- the firing slot: place the edge
      set uF : Fin N := ⟨u, huN⟩ with huF_def
      set wF : Fin N := ⟨wn, hwN⟩ with hwF_def
      have hju' : off (uF : ℕ) ≤ j := hI.hlo
      have hjhi' : j < off ((uF : ℕ) + 1) := hslot
      have hwtgt : tgt j = (wF : ℕ) := rfl
      have hwu' : (wF : ℕ) < (uF : ℕ) := hfire
      have hADJ : G.Adj uF wF := adj_of_slot hadj hju' hjhi' hwtgt
      have hnotu : ¬ Trig G off tgt j uF wF :=
        not_trig_new hnd hju' hjhi' hwtgt hwu'
      have hnotw : ¬ Trig G off tgt j wF uF := fun hc => hnotu (trig_symm hc)
      set cu := cntP G off tgt j uF with hcu_def
      set cw := cntP G off tgt j wF with hcw_def
      have hcu_lt : cu < (G.neighborSet uF).ncard :=
        cnt_lt_of_not_trig hADJ hnotu
      have hcw_lt : cw < (G.neighborSet wF).ncard :=
        cnt_lt_of_not_trig hADJ.symm hnotw
      have huF_val : (uF : ℕ) = u := rfl
      have hwF_val : (wF : ℕ) = wn := rfl
      set pu := off u + cu with hpu_def
      set pw := off wn + cw with hpw_def
      have hpu_row : pu < off (u + 1) := by
        have h := hoffstep uF
        rw [huF_val] at h
        omega
      have hpw_row : pw < off (wn + 1) := by
        have h := hoffstep wF
        rw [hwF_val] at h
        omega
      have hpu_ns : pu < ns := by
        have h := row_end_le_ns hstep hlast uF
        rw [huF_val] at h
        omega
      have hpw_ns : pw < ns := by
        have h := row_end_le_ns hstep hlast wF
        rw [hwF_val] at h
        omega
      have huw_ne : uF ≠ wF := fun hc => by
        rw [hc] at hwu'
        omega
      have hpupw : pu ≠ pw :=
        pos_ne_of_row_ne hstep huw_ne hpu_row hpw_row
      -- degree reads
      have hdgu : (σ.arrs dg).getD u 0 = cu := hI.hdg uF
      have hdgw : (σ.arrs dg).getD wn 0 = cw := hI.hdg wF
      have hcuB : cu < B := by omega
      have hcwB : cw < B := by omega
      have hoffuB : off u < B := by omega
      have hoffwB : off wn < B := by omega
      -- the six stores
      have hs1 : Run B
          (.store aj (.add (.get ao (.var uv)) (.get dg (.var uv))) (.var wv))
          σa (σa.setArr aj pu wn) 7 := by
        refine (Run.store (idx := pu) (v := wn) ?_ ?_ ?_).mono (by simp)
        · rw [hpu_def]
          refine evalB_pos (by rw [ha_arrs, hI.haoA]) ha_uv (by omega)
            (by omega) (haoL u (by omega)) hoffuB ?_ ?_ hcuB (by omega)
          · rw [ha_arrs, hdgu]
          · rw [ha_arrs]
            have := hI.hdgL
            omega
        · rw [← ha_wv]
          exact evalB_var (by rw [ha_wv]; omega)
        · rw [ha_arrs]
          have := hI.hajL
          omega
      set σ1 := σa.setArr aj pu wn with hσ1_def
      have h1_aj : σ1.arrs aj = (σ.arrs aj).set pu wn := by
        rw [hσ1_def]
        simp [ha_arrs]
      have h1_other : ∀ b, b ≠ aj → σ1.arrs b = σ.arrs b := by
        intro b hb
        rw [hσ1_def]
        simp [arrs_setArr, hb, ha_arrs]
      have h1_vars : σ1.vars = σa.vars := by rw [hσ1_def]; rfl
      have hs2 : Run B
          (.store aj (.add (.get ao (.var wv)) (.get dg (.var wv))) (.var uv))
          σ1 (σ1.setArr aj pw u) 7 := by
        refine (Run.store (idx := pw) (v := u) ?_ ?_ ?_).mono (by simp)
        · rw [hpw_def]
          refine evalB_pos (by rw [h1_other ao h_ao_aj, hI.haoA])
            (by rw [h1_vars, ha_wv]) (by omega) (by omega)
            (haoL wn (by omega)) hoffwB ?_ ?_ hcwB (by omega)
          · rw [h1_other dg (Ne.symm h_aj_dg), hdgw]
          · rw [h1_other dg (Ne.symm h_aj_dg)]
            have := hI.hdgL
            omega
        · have : σ1.vars uv = u := by rw [h1_vars, ha_uv]
          rw [← this]
          exact evalB_var (by rw [this]; omega)
        · rw [h1_aj, List.length_set]
          have := hI.hajL
          omega
      set σ2 := σ1.setArr aj pw u with hσ2_def
      have h2_aj : σ2.arrs aj = ((σ.arrs aj).set pu wn).set pw u := by
        rw [hσ2_def]
        simp [arrs_setArr, h1_aj]
      have h2_other : ∀ b, b ≠ aj → σ2.arrs b = σ.arrs b := by
        intro b hb
        rw [hσ2_def]
        simp only [arrs_setArr, if_neg hb]
        exact h1_other b hb
      have h2_vars : σ2.vars = σa.vars := by rw [hσ2_def]; simpa using h1_vars
      have hs3 : Run B
          (.store mt (.add (.get ao (.var uv)) (.get dg (.var uv)))
            (.add (.get ao (.var wv)) (.get dg (.var wv))))
          σ2 (σ2.setArr mt pu pw) 11 := by
        refine (Run.store (idx := pu) (v := pw) ?_ ?_ ?_).mono (by simp)
        · rw [hpu_def]
          refine evalB_pos (by rw [h2_other ao h_ao_aj, hI.haoA])
            (by rw [h2_vars, ha_uv]) (by omega) (by omega)
            (haoL u (by omega)) hoffuB ?_ ?_ hcuB (by omega)
          · rw [h2_other dg (Ne.symm h_aj_dg), hdgu]
          · rw [h2_other dg (Ne.symm h_aj_dg)]
            have := hI.hdgL
            omega
        · rw [hpw_def]
          refine evalB_pos (by rw [h2_other ao h_ao_aj, hI.haoA])
            (by rw [h2_vars, ha_wv]) (by omega) (by omega)
            (haoL wn (by omega)) hoffwB ?_ ?_ hcwB (by omega)
          · rw [h2_other dg (Ne.symm h_aj_dg), hdgw]
          · rw [h2_other dg (Ne.symm h_aj_dg)]
            have := hI.hdgL
            omega
        · rw [h2_other mt (Ne.symm h_aj_mt)]
          have := hI.hmtL
          omega
      set σ3 := σ2.setArr mt pu pw with hσ3_def
      have h3_mt : σ3.arrs mt = (σ.arrs mt).set pu pw := by
        rw [hσ3_def]
        simp [arrs_setArr, h2_other mt (Ne.symm h_aj_mt)]
      have h3_aj : σ3.arrs aj = ((σ.arrs aj).set pu wn).set pw u := by
        rw [hσ3_def]
        simp [arrs_setArr, h_aj_mt, h2_aj]
      have h3_other : ∀ b, b ≠ aj → b ≠ mt → σ3.arrs b = σ.arrs b := by
        intro b hb1 hb2
        rw [hσ3_def]
        simp only [arrs_setArr, if_neg hb2]
        exact h2_other b hb1
      have h3_vars : σ3.vars = σa.vars := by rw [hσ3_def]; simpa using h2_vars
      have hs4 : Run B
          (.store mt (.add (.get ao (.var wv)) (.get dg (.var wv)))
            (.add (.get ao (.var uv)) (.get dg (.var uv))))
          σ3 (σ3.setArr mt pw pu) 11 := by
        refine (Run.store (idx := pw) (v := pu) ?_ ?_ ?_).mono (by simp)
        · rw [hpw_def]
          refine evalB_pos (by rw [h3_other ao h_ao_aj h_ao_mt, hI.haoA])
            (by rw [h3_vars, ha_wv]) (by omega) (by omega)
            (haoL wn (by omega)) hoffwB ?_ ?_ hcwB (by omega)
          · rw [h3_other dg (Ne.symm h_aj_dg) (Ne.symm h_mt_dg), hdgw]
          · rw [h3_other dg (Ne.symm h_aj_dg) (Ne.symm h_mt_dg)]
            have := hI.hdgL
            omega
        · rw [hpu_def]
          refine evalB_pos (by rw [h3_other ao h_ao_aj h_ao_mt, hI.haoA])
            (by rw [h3_vars, ha_uv]) (by omega) (by omega)
            (haoL u (by omega)) hoffuB ?_ ?_ hcuB (by omega)
          · rw [h3_other dg (Ne.symm h_aj_dg) (Ne.symm h_mt_dg), hdgu]
          · rw [h3_other dg (Ne.symm h_aj_dg) (Ne.symm h_mt_dg)]
            have := hI.hdgL
            omega
        · rw [h3_mt, List.length_set]
          have := hI.hmtL
          omega
      set σ4 := σ3.setArr mt pw pu with hσ4_def
      have h4_mt : σ4.arrs mt = ((σ.arrs mt).set pu pw).set pw pu := by
        rw [hσ4_def]
        simp [arrs_setArr, h3_mt]
      have h4_aj : σ4.arrs aj = ((σ.arrs aj).set pu wn).set pw u := by
        rw [hσ4_def]
        simp [arrs_setArr, h_aj_mt, h3_aj]
      have h4_other : ∀ b, b ≠ aj → b ≠ mt → σ4.arrs b = σ.arrs b := by
        intro b hb1 hb2
        rw [hσ4_def]
        simp only [arrs_setArr, if_neg hb2]
        exact h3_other b hb1 hb2
      have h4_vars : σ4.vars = σa.vars := by rw [hσ4_def]; simpa using h3_vars
      have hs5 : Run B
          (.store dg (.var uv) (.add (.get dg (.var uv)) (.lit 1)))
          σ4 (σ4.setArr dg u (cu + 1)) 6 := by
        refine (Run.store (idx := u) (v := cu + 1) ?_ ?_ ?_).mono (by simp)
        · have : σ4.vars uv = u := by rw [h4_vars, ha_uv]
          rw [← this]
          exact evalB_var (by rw [this]; omega)
        · have h1 := evalB_get_pin (B := B) (L := σ4.arrs dg) rfl
            (show σ4.vars uv = u by rw [h4_vars, ha_uv]) (by omega)
            (by rw [h4_other dg (Ne.symm h_aj_dg) (Ne.symm h_mt_dg)]
                have := hI.hdgL
                omega)
            (by rw [h4_other dg (Ne.symm h_aj_dg) (Ne.symm h_mt_dg)]
                exact hdgu) hcuB
          have h := evalB_bin (op := .add) h1 (evalB_lit (n := 1) (by omega))
            (by simpa using by omega)
          simpa using h
        · rw [h4_other dg (Ne.symm h_aj_dg) (Ne.symm h_mt_dg)]
          have := hI.hdgL
          omega
      set σ5 := σ4.setArr dg u (cu + 1) with hσ5_def
      have h5_dg : σ5.arrs dg = (σ.arrs dg).set u (cu + 1) := by
        rw [hσ5_def]
        simp [arrs_setArr, h4_other dg (Ne.symm h_aj_dg) (Ne.symm h_mt_dg)]
      have h5_aj : σ5.arrs aj = ((σ.arrs aj).set pu wn).set pw u := by
        rw [hσ5_def]
        simp [arrs_setArr, h_aj_dg, h4_aj]
      have h5_mt : σ5.arrs mt = ((σ.arrs mt).set pu pw).set pw pu := by
        rw [hσ5_def]
        simp [arrs_setArr, h_mt_dg, h4_mt]
      have h5_vars : σ5.vars = σa.vars := by rw [hσ5_def]; simpa using h4_vars
      have hs6 : Run B
          (.store dg (.var wv) (.add (.get dg (.var wv)) (.lit 1)))
          σ5 (σ5.setArr dg wn (cw + 1)) 6 := by
        refine (Run.store (idx := wn) (v := cw + 1) ?_ ?_ ?_).mono (by simp)
        · have : σ5.vars wv = wn := by rw [h5_vars, ha_wv]
          rw [← this]
          exact evalB_var (by rw [this]; omega)
        · have hlen5 : wn < (σ5.arrs dg).length := by
            rw [h5_dg, List.length_set]
            have := hI.hdgL
            omega
          have hval5 : (σ5.arrs dg).getD wn 0 = cw := by
            rw [h5_dg, getD_set_ne (by omega), hdgw]
          have h1 := evalB_get_pin (B := B) (L := σ5.arrs dg) rfl
            (show σ5.vars wv = wn by rw [h5_vars, ha_wv]) (by omega)
            hlen5 hval5 hcwB
          have h := evalB_bin (op := .add) h1 (evalB_lit (n := 1) (by omega))
            (by simpa using by omega)
          simpa using h
        · rw [h5_dg, List.length_set]
          have := hI.hdgL
          omega
      set σ6 := σ5.setArr dg wn (cw + 1) with hσ6_def
      have h6_dg : σ6.arrs dg = ((σ.arrs dg).set u (cu + 1)).set wn (cw + 1) := by
        rw [hσ6_def]
        simp [arrs_setArr, h5_dg]
      have h6_aj : σ6.arrs aj = ((σ.arrs aj).set pu wn).set pw u := by
        rw [hσ6_def]
        simp [arrs_setArr, h_aj_dg, h5_aj]
      have h6_mt : σ6.arrs mt = ((σ.arrs mt).set pu pw).set pw pu := by
        rw [hσ6_def]
        simp [arrs_setArr, h_mt_dg, h5_mt]
      have h6_other : ∀ b, b ≠ aj → b ≠ mt → b ≠ dg → σ6.arrs b = σ.arrs b := by
        intro b hb1 hb2 hb3
        rw [hσ6_def]
        simp only [arrs_setArr, if_neg hb3]
        rw [hσ5_def]
        simp only [arrs_setArr, if_neg hb3]
        exact h4_other b hb1 hb2
      have h6_vars : σ6.vars = σa.vars := by rw [hσ6_def]; simpa using h5_vars
      -- the counter bump
      have hs7 : Run B (.assign iv (.add (.var iv) (.lit 1)))
          σ6 (σ6.setVar iv (j + 1)) 4 := by
        refine (Run.assign ?_).mono (by simp)
        have h1 : (Expr.var iv).evalB B σ6 = some j := by
          have : σ6.vars iv = j := by rw [h6_vars, ha_iv]
          rw [← this]
          exact evalB_var (by rw [this]; omega)
        have h := evalB_bin (op := .add) h1 (evalB_lit (n := 1) (by omega))
          (by simpa using by omega)
        simpa using h
      set σ' := σ6.setVar iv (j + 1) with hσ'_def
      -- the assembled run
      have hplace : Run B (bldPlace ao aj dg mt uv wv) σa σ6 48 := by
        have h := hs1.seq (hs2.seq (hs3.seq (hs4.seq (hs5.seq hs6))))
        exact (h.mono (by omega)).congr rfl
      have hinner : Run B
          (.ite (.lt (.var wv) (.var uv)) (bldPlace ao aj dg mt uv wv) .skip)
          σa σ6 52 := by
        refine Run.ite_true ?_ hplace
        rw [hcond]
        congr 1
        simpa using hfire
      have hbranch : Run B
          (.seq (.assign wv (.get t (.var iv)))
            (.seq (.ite (.lt (.var wv) (.var uv))
              (bldPlace ao aj dg mt uv wv) .skip)
              (.assign iv (.add (.var iv) (.lit 1)))))
          σ σ' 59 :=
        (hread.seq (hinner.seq hs7)).mono (by omega)
      have hrun : Run B (bldTurn t ao aj dg mt iv uv wv) σ σ' 66 := by
        refine (Run.ite_true hguardT hbranch).mono ?_
        rw [hguard_size]
      -- the new counts
      obtain ⟨hcnt_u, hcnt_w, hcnt_o⟩ :=
        cnt_succ_place (G := G) hstep hnd hadj hju' hjhi' hwtgt hwu'
      -- fresh positions: no live cell is at `pu` or `pw`
      have hfresh : ∀ (r : Fin N) (s : ℕ), s < cntP G off tgt j r →
          off (r : ℕ) + s ≠ pu ∧ off (r : ℕ) + s ≠ pw := by
        intro r s hs
        have hrow := pos_lt_row_end hoffstep hs
        constructor
        · by_cases hr : r = uF
          · subst hr
            rw [huF_val]
            omega
          · exact pos_ne_of_row_ne hstep hr hrow hpu_row
        · by_cases hr : r = wF
          · subst hr
            rw [hwF_val]
            omega
          · exact pos_ne_of_row_ne hstep hr hrow hpw_row
      -- the preserved-cell readers
      have haj_old : ∀ (r : Fin N) (s : ℕ), s < cntP G off tgt j r →
          (σ'.arrs aj).getD (off (r : ℕ) + s) 0
            = (σ.arrs aj).getD (off (r : ℕ) + s) 0 := by
        intro r s hs
        obtain ⟨hne1, hne2⟩ := hfresh r s hs
        rw [hσ'_def]
        show (σ6.arrs aj).getD (off (r : ℕ) + s) 0 = _
        rw [h6_aj, getD_set_ne (Ne.symm hne2), getD_set_ne (Ne.symm hne1)]
      have hmt_old : ∀ (r : Fin N) (s : ℕ), s < cntP G off tgt j r →
          (σ'.arrs mt).getD (off (r : ℕ) + s) 0
            = (σ.arrs mt).getD (off (r : ℕ) + s) 0 := by
        intro r s hs
        obtain ⟨hne1, hne2⟩ := hfresh r s hs
        rw [hσ'_def]
        show (σ6.arrs mt).getD (off (r : ℕ) + s) 0 = _
        rw [h6_mt, getD_set_ne (Ne.symm hne2), getD_set_ne (Ne.symm hne1)]
      have haj_pu : (σ'.arrs aj).getD pu 0 = wn := by
        rw [hσ'_def]
        show (σ6.arrs aj).getD pu 0 = wn
        rw [h6_aj, getD_set_ne (Ne.symm hpupw),
          getD_set_self (show pu < (σ.arrs aj).length by
            have := hI.hajL
            omega)]
      have haj_pw : (σ'.arrs aj).getD pw 0 = u := by
        rw [hσ'_def]
        show (σ6.arrs aj).getD pw 0 = u
        rw [h6_aj, getD_set_self (by
          rw [List.length_set]
          have := hI.hajL
          omega)]
      have hmt_pu : (σ'.arrs mt).getD pu 0 = pw := by
        rw [hσ'_def]
        show (σ6.arrs mt).getD pu 0 = pw
        rw [h6_mt, getD_set_ne (Ne.symm hpupw),
          getD_set_self (show pu < (σ.arrs mt).length by
            have := hI.hmtL
            omega)]
      have hmt_pw : (σ'.arrs mt).getD pw 0 = pu := by
        rw [hσ'_def]
        show (σ6.arrs mt).getD pw 0 = pu
        rw [h6_mt, getD_set_self (by
          rw [List.length_set]
          have := hI.hmtL
          omega)]
      have hdg' : ∀ v : Fin N,
          (σ'.arrs dg).getD (v : ℕ) 0 = cntP G off tgt (j + 1) v := by
        intro v
        have hdgv : (σ'.arrs dg).getD (v : ℕ) 0
            = (((σ.arrs dg).set u (cu + 1)).set wn (cw + 1)).getD (v : ℕ) 0 := by
          rw [hσ'_def]
          show (σ6.arrs dg).getD (v : ℕ) 0 = _
          rw [h6_dg]
        rw [hdgv]
        by_cases hv : v = uF
        · subst hv
          rw [huF_val, getD_set_ne (show wn ≠ u by omega),
            getD_set_self (show u < (σ.arrs dg).length by
              have := hI.hdgL; omega)]
          omega
        · by_cases hv' : v = wF
          · subst hv'
            rw [hwF_val, getD_set_self (by
              rw [List.length_set]
              have := hI.hdgL
              omega)]
            omega
          · have hvu : (v : ℕ) ≠ u := fun hc => hv (Fin.ext hc)
            have hvw : (v : ℕ) ≠ wn := fun hc => hv' (Fin.ext hc)
            rw [getD_set_ne (Ne.symm hvw), getD_set_ne (Ne.symm hvu),
              hI.hdg v, hcnt_o v hv hv']
      -- the invariant, re-established
      have hσ'_iv : σ'.vars iv = j + 1 := by rw [hσ'_def]; simp
      have hσ'_uv : σ'.vars uv = u := by
        rw [hσ'_def]
        simp only [vars_setVar, if_neg (Ne.symm h_iv_uv)]
        rw [h6_vars, ha_uv]
      have hσ'_nS : σ'.vars nS = ns := by
        rw [hσ'_def]
        simp only [vars_setVar, if_neg (Ne.symm h_iv_nS)]
        rw [h6_vars, hσa_def]
        simp only [vars_setVar, if_neg (Ne.symm h_wv_nS)]
        exact hI.hnS
      have hlen_aj' : (σ'.arrs aj).length = (σ.arrs aj).length := by
        rw [hσ'_def]
        show (σ6.arrs aj).length = _
        rw [h6_aj]
        simp
      have hlen_mt' : (σ'.arrs mt).length = (σ.arrs mt).length := by
        rw [hσ'_def]
        show (σ6.arrs mt).length = _
        rw [h6_mt]
        simp
      have hlen_dg' : (σ'.arrs dg).length = (σ.arrs dg).length := by
        rw [hσ'_def]
        show (σ6.arrs dg).length = _
        rw [h6_dg]
        simp
      have harr_t' : σ'.arrs t = tL := by
        rw [hσ'_def]
        show σ6.arrs t = tL
        rw [h6_other t h_t_aj h_t_mt h_t_dg]
        exact hI.htA
      have harr_ao' : σ'.arrs ao = aoL := by
        rw [hσ'_def]
        show σ6.arrs ao = aoL
        rw [h6_other ao h_ao_aj h_ao_mt h_ao_dg]
        exact hI.haoA
      refine ⟨σ', 66, hrun, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨hσ'_nS, harr_t', harr_ao',
          by rw [hσ'_uv]; exact hI.hu,
          by rw [hσ'_iv]; omega,
          by
            have h := hI.hlo
            rw [← hu_def, ← hj_def] at h
            rw [hσ'_uv, hσ'_iv]
            omega,
          by rw [hσ'_uv, hσ'_iv]; intro; omega,
          by rw [hlen_aj']; exact hI.hajL,
          by rw [hlen_mt']; exact hI.hmtL,
          by rw [hlen_dg']; exact hI.hdgL,
          by rw [hσ'_iv]; exact hdg',
          ?_, ?_⟩
        · -- soundness with a consistent mate, per live slot
          simp only [hσ'_iv]
          intro v t' ht'
          by_cases hv : v = uF
          · subst hv
            rw [hcnt_u] at ht'
            rcases Nat.lt_or_ge t' (cntP G off tgt j uF) with hlt | hge
            · obtain ⟨w₀, htr, hcell, s₀, hs₀, hmtc, hcell', hmtc'⟩ :=
                hI.hsound uF t' hlt
              exact ⟨w₀, trig_mono (Nat.le_succ j) htr,
                by rw [haj_old uF t' hlt]; exact hcell, s₀,
                lt_of_lt_of_le hs₀ (cnt_mono (Nat.le_succ j) w₀),
                by rw [hmt_old uF t' hlt]; exact hmtc,
                by rw [haj_old w₀ s₀ hs₀]; exact hcell',
                by rw [hmt_old w₀ s₀ hs₀]; exact hmtc'⟩
            · have ht'' : t' = cu := by omega
              subst ht''
              refine ⟨wF, (trig_succ_place hstep hadj hju' hjhi' hwtgt hwu'
                  uF wF).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_, cw, ?_, ?_, ?_, ?_⟩
              · rw [huF_val, hwF_val, ← hpu_def]
                exact haj_pu
              · rw [hcnt_w]
                omega
              · rw [huF_val, hwF_val, ← hpu_def, ← hpw_def]
                exact hmt_pu
              · rw [huF_val, hwF_val, ← hpw_def]
                exact haj_pw
              · rw [huF_val, hwF_val, ← hpw_def, ← hpu_def]
                exact hmt_pw
          · by_cases hv' : v = wF
            · subst hv'
              rw [hcnt_w] at ht'
              rcases Nat.lt_or_ge t' (cntP G off tgt j wF) with hlt | hge
              · obtain ⟨w₀, htr, hcell, s₀, hs₀, hmtc, hcell', hmtc'⟩ :=
                  hI.hsound wF t' hlt
                exact ⟨w₀, trig_mono (Nat.le_succ j) htr,
                  by rw [haj_old wF t' hlt]; exact hcell, s₀,
                  lt_of_lt_of_le hs₀ (cnt_mono (Nat.le_succ j) w₀),
                  by rw [hmt_old wF t' hlt]; exact hmtc,
                  by rw [haj_old w₀ s₀ hs₀]; exact hcell',
                  by rw [hmt_old w₀ s₀ hs₀]; exact hmtc'⟩
              · have ht'' : t' = cw := by omega
                subst ht''
                refine ⟨uF, (trig_succ_place hstep hadj hju' hjhi' hwtgt hwu'
                    wF uF).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_, cu, ?_, ?_, ?_, ?_⟩
                · rw [huF_val, hwF_val, ← hpw_def]
                  exact haj_pw
                · rw [hcnt_u]
                  omega
                · rw [huF_val, hwF_val, ← hpw_def, ← hpu_def]
                  exact hmt_pw
                · rw [huF_val, hwF_val, ← hpu_def]
                  exact haj_pu
                · rw [huF_val, hwF_val, ← hpu_def, ← hpw_def]
                  exact hmt_pu
            · rw [hcnt_o v hv hv'] at ht'
              obtain ⟨w₀, htr, hcell, s₀, hs₀, hmtc, hcell', hmtc'⟩ :=
                hI.hsound v t' ht'
              exact ⟨w₀, trig_mono (Nat.le_succ j) htr,
                by rw [haj_old v t' ht']; exact hcell, s₀,
                lt_of_lt_of_le hs₀ (cnt_mono (Nat.le_succ j) w₀),
                by rw [hmt_old v t' ht']; exact hmtc,
                by rw [haj_old w₀ s₀ hs₀]; exact hcell',
                by rw [hmt_old w₀ s₀ hs₀]; exact hmtc'⟩
        · -- completeness
          simp only [hσ'_iv]
          intro v w' htr'
          rw [trig_succ_place hstep hadj hju' hjhi' hwtgt hwu' v w'] at htr'
          rcases htr' with htr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · obtain ⟨t', ht', hcell⟩ := hI.hcomp v w' htr
            exact ⟨t', lt_of_lt_of_le ht' (cnt_mono (Nat.le_succ j) v),
              by rw [haj_old v t' ht']; exact hcell⟩
          · refine ⟨cu, ?_, ?_⟩
            · rw [hcnt_u]
              omega
            · rw [huF_val, hwF_val, ← hpu_def]
              exact haj_pu
          · refine ⟨cw, ?_, ?_⟩
            · rw [hcnt_w]
              omega
            · rw [huF_val, hwF_val, ← hpw_def]
              exact haj_pw
      · rw [hσ'_iv]
        omega
      · rw [hσ'_uv]
      · left
        rw [hσ'_iv]
        omega
      · rw [hσ'_iv, hσ'_uv]
        omega
    · -- the silent slot: the target is not below the owner
      set uF : Fin N := ⟨u, huN⟩ with huF_def
      have huF_val : (uF : ℕ) = u := rfl
      have hju' : off (uF : ℕ) ≤ j := hI.hlo
      have hjhi' : j < off ((uF : ℕ) + 1) := hslot
      have hge' : (uF : ℕ) ≤ tgt j := by
        rw [huF_val, ← hwn_def]
        omega
      have hskip : Run B (.ite (.lt (.var wv) (.var uv))
          (bldPlace ao aj dg mt uv wv) .skip) σa σa 5 := by
        refine Run.ite_false ?_ Run.skip
        rw [hcond]
        congr 1
        simpa using hfire
      have hs7' : Run B (.assign iv (.add (.var iv) (.lit 1))) σa
          (σa.setVar iv (j + 1)) 4 := by
        refine (Run.assign ?_).mono (by simp)
        have h1 : (Expr.var iv).evalB B σa = some j := by
          rw [← ha_iv]
          exact evalB_var (by rw [ha_iv]; omega)
        have h := evalB_bin (op := .add) h1 (evalB_lit (n := 1) (by omega))
          (by simpa using by omega)
        simpa using h
      set σ' := σa.setVar iv (j + 1) with hσ'_def
      have hbranch : Run B (.seq (.assign wv (.get t (.var iv)))
          (.seq (.ite (.lt (.var wv) (.var uv))
            (bldPlace ao aj dg mt uv wv) .skip)
            (.assign iv (.add (.var iv) (.lit 1))))) σ σ' 12 :=
        (hread.seq (hskip.seq hs7')).mono (by omega)
      have hrun : Run B (bldTurn t ao aj dg mt iv uv wv) σ σ' 19 := by
        refine (Run.ite_true hguardT hbranch).mono ?_
        rw [hguard_size]
      have hσ'_iv : σ'.vars iv = j + 1 := by rw [hσ'_def]; simp
      have hσ'_uv : σ'.vars uv = u := by
        rw [hσ'_def]
        simp only [vars_setVar, if_neg (Ne.symm h_iv_uv)]
        exact ha_uv
      have hσ'_nS : σ'.vars nS = ns := by
        rw [hσ'_def]
        simp only [vars_setVar, if_neg (Ne.symm h_iv_nS)]
        rw [hσa_def]
        simp only [vars_setVar, if_neg (Ne.symm h_wv_nS)]
        exact hI.hnS
      have hσ'_arrs : σ'.arrs = σ.arrs := by
        rw [hσ'_def]
        show σa.arrs = σ.arrs
        exact ha_arrs
      have hcnt' : ∀ v : Fin N,
          cntP G off tgt (j + 1) v = cntP G off tgt j v :=
        cnt_succ_skip hstep hju' hjhi' hge'
      refine ⟨σ', 19, hrun, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨hσ'_nS,
          by rw [hσ'_arrs]; exact hI.htA,
          by rw [hσ'_arrs]; exact hI.haoA,
          by rw [hσ'_uv]; exact hI.hu,
          by rw [hσ'_iv]; omega,
          by
            have h := hI.hlo
            rw [← hu_def, ← hj_def] at h
            rw [hσ'_uv, hσ'_iv]
            omega,
          by rw [hσ'_uv, hσ'_iv]; intro; omega,
          by rw [hσ'_arrs]; exact hI.hajL,
          by rw [hσ'_arrs]; exact hI.hmtL,
          by rw [hσ'_arrs]; exact hI.hdgL,
          ?_, ?_, ?_⟩
        · intro v
          rw [hσ'_arrs, hσ'_iv, hcnt' v]
          exact hI.hdg v
        · intro v t' ht'
          rw [hσ'_iv, hcnt' v] at ht'
          obtain ⟨w₀, htr, hcell, s₀, hs₀, hmtc, hcell', hmtc'⟩ :=
            hI.hsound v t' ht'
          simp only [hσ'_iv, hσ'_arrs]
          exact ⟨w₀, trig_mono (Nat.le_succ j) htr, hcell, s₀,
            by rw [hcnt' w₀]; exact hs₀, hmtc, hcell', hmtc'⟩
        · intro v w' htr'
          simp only [hσ'_iv, hσ'_arrs] at htr' ⊢
          rw [trig_succ_skip hstep hju' hjhi' hge' v w'] at htr'
          obtain ⟨t', ht', hcell⟩ := hI.hcomp v w' htr'
          exact ⟨t', by rw [hcnt' v]; exact ht', hcell⟩
      · rw [hσ'_iv]
        omega
      · rw [hσ'_uv]
      · left
        rw [hσ'_iv]
        omega
      · rw [hσ'_iv, hσ'_uv]
        omega
  · -- the row's end: advance the owner
    have hjeq : j = off (u + 1) := by
      have h := hI.hhi huN
      rw [← hu_def, ← hj_def] at h
      omega
    have hguardF : (Cond.lt (.var iv)
        (.get ao (.add (.var uv) (.lit 1)))).evalB B σ = some false := by
      rw [hguard]
      congr 1
      simpa using hslot
    have hassign : Run B (.assign uv (.add (.var uv) (.lit 1))) σ
        (σ.setVar uv (u + 1)) 4 :=
      (Run.assign hu1eval).mono (by simp)
    set σ' := σ.setVar uv (u + 1) with hσ'_def
    have hrun : Run B (bldTurn t ao aj dg mt iv uv wv) σ σ' 11 := by
      refine (Run.ite_false hguardF hassign).mono ?_
      rw [hguard_size]
    have hσ'_iv : σ'.vars iv = j := by
      rw [hσ'_def]
      simp only [vars_setVar, if_neg h_iv_uv]
      exact hj_def.symm
    have hσ'_uv : σ'.vars uv = u + 1 := by rw [hσ'_def]; simp
    have hσ'_nS : σ'.vars nS = ns := by
      rw [hσ'_def]
      simp only [vars_setVar, if_neg (Ne.symm h_uv_nS)]
      exact hI.hnS
    have hσ'_arrs : σ'.arrs = σ.arrs := by rw [hσ'_def]; rfl
    refine ⟨σ', 11, hrun, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨hσ'_nS,
        by rw [hσ'_arrs]; exact hI.htA,
        by rw [hσ'_arrs]; exact hI.haoA,
        by rw [hσ'_uv]; omega,
        by rw [hσ'_iv]; omega,
        by rw [hσ'_uv, hσ'_iv]; omega,
        ?_,
        by rw [hσ'_arrs]; exact hI.hajL,
        by rw [hσ'_arrs]; exact hI.hmtL,
        by rw [hσ'_arrs]; exact hI.hdgL,
        by intro v; rw [hσ'_arrs, hσ'_iv]; exact hI.hdg v,
        by
          intro v t' ht'
          rw [hσ'_iv] at ht'
          simp only [hσ'_iv, hσ'_arrs]
          exact hI.hsound v t' ht',
        by
          intro v w' htr'
          rw [hσ'_iv] at htr'
          simp only [hσ'_iv, hσ'_arrs]
          exact hI.hcomp v w' htr'⟩
      rw [hσ'_uv, hσ'_iv]
      intro hu1
      have hs2 := hstep (u + 1) hu1
      omega
    · rw [hσ'_iv]
    · rw [hσ'_uv]
      omega
    · right
      rw [hσ'_uv]
      omega
    · rw [hσ'_iv, hσ'_uv]
      omega

end EdgePass

end Lax3Proofs.Prog
