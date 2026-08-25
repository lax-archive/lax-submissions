import Lax3Proofs.SolveAugEmit

/-!
# F6c12-5c-iii — the augmentation round's transpose, as IMP+ text

`SolveAugEmit` (F6c12-5c-ii) proved **all the mathematics** of the greedy
round's body and left two residuals open, both quantified over a command
and a budget: `TransposeIn` and `StepEmitIn` (its Finding 4).  This file
discharges the first of the two — **`TransposeIn` is met by a concrete
`Com` at a concrete budget** — and adds the counting-sort layer that a
transpose needs and that nothing in the tower had.

`StepEmitIn` is **not** discharged here and nothing about it is asserted:
no command text for it appears below, and no weakened variant of its
contract is stated.  Its residual stands exactly as `SolveAugEmit`
left it.

## What `tpCom` is

A counting sort over the input CSR's slots, in three sweeps and one
nested pair:

* `tpCntCom` counts, one turn per slot: `dg[t[p]] += 1`, so `dg[u]`
  ends at `u`'s out-degree.  The extent `ns` is **not** in a named cell
  and does not have to be: it is `o[nN]`, the input CSR's own last
  offset, one array read (Finding 1).
* `tpOffCom` prefix-sums, one turn per vertex: `qo[i] := acc`,
  `dg[i] := acc`, `acc += deg`.  The degree is read into a scalar
  *before* the cell is overwritten, so the one region is first the
  counter and then the scatter's cursor and no third array exists.
* `tpScatCom` scatters, one outer turn per head and one inner turn per
  slot: `qt[dg[t[j]]] := v`, then bump the cursor.

The output is `OutCsrAt qo qt D otF` — `SolveAugEmit`'s §7 shape — with
the input CSR untouched.

## Why the sort is correct, in one line each

* **What the count sweep leaves** is the number of slots of the whole
  structure whose target is `u`; that this is `u`'s out-degree is the
  only real content of a counting sort, and it is `tpCnt_off`: an
  induction over heads in which `TrInCsr`'s `complete` supplies the
  slot a head contributes, `inj` says it contributes at most one, and
  `sound` says a slot contributes only to its own head.
* **What the scatter leaves** is pinned by an *address*, not by a set:
  `TpScatSt.fill` says slot `outOff D u + tpCnt tgt (off a) u` holds
  the head `a`.  Since heads run in increasing order, the input CSR's
  flat slot pointer is also the scatter's clock, so the cursor of `u`
  after the slots below `P` is `outOff D u + tpCnt tgt P u` — and
  `tpCnt_eq_of_row` (a head hits a target at most once, by `inj`) is
  why the address a head writes at is the one its *own* clock gives.
* That address form pins `OutCsrAt.inj` outright — two slots holding
  the same head are the same address — and `complete` then follows by
  counting: row `u` has exactly `|outNbrs D u|` slots, each holding a
  distinct out-neighbour, so every out-neighbour is in one
  (`Finset.surj_on_of_inj_on_of_card_le`).  Only `sound` and `inj` are
  carried by the loop.

## The budget

`tpK n a = 41·n + 40·a + 30`, at `a = arcCount D`: the counting sweep
`17` a slot, the prefix sweep `21` a vertex, the scatter `20` a head and
`22` a slot, plus `29` of fixed blocks.  `O(n + arcCount D)` and nothing
else — no carrier scan inside a head's turn and no `n²` term.
`tpK_le_emK` is that this sits inside `SolveAugEmit`'s own pinned
`emK n a f T = 300·n + 300·a + 200·f + 240·T + 80` with `259·n + 260·a`
still unspent, which is the room the rest of the round body was priced
at.

## Findings

1. **The transpose's extent needs no cell, and that is why the landed
   contract is meetable.**  `TransposeIn` names only `nN`, and a
   counting sort looks as though it needs the slot count too — which is
   exactly the shape that makes `AdjBuildIn` (`SolveSweepAdj.lean:308`)
   false, since IMP+ reads no array length (`Imp.lean:158`).  Here
   `ns = off n` is the input CSR's last offset, so `o[nN]` is it, and
   the first line of `tpCntCom` reads it into `tp.e`.  The contract is
   meetable for a reason rather than by luck.
2. **The scatter's invariant is an address, not a set.**  The obvious
   carried statement — "row `u` holds a set of out-neighbours, without
   repeats" — makes `inj` a separate induction and needs the emitted
   heads to be known increasing.  Stating instead *where* each head
   lands (`TpScatSt.fill`) makes `inj` a one-line consequence and
   removes the monotonicity bookkeeping entirely; the price is
   `tpCnt_eq_of_row`, which is three lines off `TrInCsr.inj`.
3. **`OutCsrAt.complete` is cheaper to derive than to carry.**  The
   loop maintains only soundness and the address; completeness at the
   end is pigeonhole on `|Ico (outOff u) (outOff (u+1))| =
   |outNbrs D u|`.  Carrying it would have added a clause to every one
   of the scatter's `2·arcCount D` steps.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine
open Lax3Proofs.TgtCoupling

/-! ## §0 Small array and run helpers

The shapes the sweeps are built from, each with its value obligations
named and its cost computed once.  These mirror `SolveSweepBuild`'s §0,
which is `private` there. -/

private theorem getD_set_self' {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem getD_set_of_ne' {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c).getD q 0 = l.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

private theorem getElem?_of_lt' (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

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

private theorem run_assign'' {B : ℕ} {x : String} {e : Expr} {σ : Env} {c K : ℕ}
    (he : e.evalB B σ = some c) (hK : 1 + e.size ≤ K) :
    Run B (.assign x e) σ (σ.setVar x c) K := (Run.assign he).mono hK

private theorem run_store'' {B : ℕ} {a : String} {i e : Expr} {σ : Env} {q c K : ℕ}
    (hi : i.evalB B σ = some q) (he : e.evalB B σ = some c)
    (hq : q < (σ.arrs a).length) (hK : 1 + i.size + e.size ≤ K) :
    Run B (.store a i e) σ (σ.setArr a q c) K := (Run.store hi he hq).mono hK

variable {n : ℕ}

/-! ## §1 The counting sort, abstractly

The transpose is a counting sort over the input CSR's slots, so what its
first sweep leaves in `dg[u]` is *the number of slots whose target is
`u`*, and what its scatter needs is that this number is `u`'s
out-degree.  That identification is the only real content of the sort:
it is a bijection between the slots of the whole structure carrying
target `u` and the heads that own them, and the three clauses
`sound`/`complete`/`inj` of `TrInCsr` are exactly what makes it one.
It is proved once here, by induction on the heads. -/

/-- The slots below `k` whose target is `u` — what the counting sweep
has accumulated in `dg[u]` after `k` turns. -/
def tpCnt (tgt : ℕ → ℕ) (k u : ℕ) : ℕ :=
  ((Finset.range k).filter (fun q => tgt q = u)).card

theorem tpCnt_zero (tgt : ℕ → ℕ) (u : ℕ) : tpCnt tgt 0 u = 0 := by
  simp [tpCnt]

theorem tpCnt_succ (tgt : ℕ → ℕ) (k u : ℕ) :
    tpCnt tgt (k + 1) u = tpCnt tgt k u + (if tgt k = u then 1 else 0) := by
  classical
  rw [tpCnt, tpCnt, Finset.range_add_one, Finset.filter_insert]
  by_cases h : tgt k = u
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, Nat.add_zero]

theorem tpCnt_le (tgt : ℕ → ℕ) (k u : ℕ) : tpCnt tgt k u ≤ k := by
  simpa [tpCnt] using Finset.card_filter_le (Finset.range k) (fun q => tgt q = u)

/-- The out-neighbours of `u` below `k` — what the scatter has written
into row `u` of the transpose once `k` heads have run. -/
noncomputable def outBelow (D : Orientation n) (u : Fin n) (k : ℕ) : Finset (Fin n) :=
  (outNbrs D u).filter (fun v => (v : ℕ) < k)

theorem mem_outBelow {D : Orientation n} {u v : Fin n} {k : ℕ} :
    v ∈ outBelow D u k ↔ u ∈ D.inN v ∧ (v : ℕ) < k := by
  rw [outBelow, Finset.mem_filter, mem_outNbrs]

theorem outBelow_zero (D : Orientation n) (u : Fin n) : outBelow D u 0 = ∅ := by
  ext v; simp [mem_outBelow]

theorem outBelow_last (D : Orientation n) (u : Fin n) : outBelow D u n = outNbrs D u := by
  ext v
  rw [mem_outBelow, mem_outNbrs]
  exact ⟨fun h => h.1, fun h => ⟨h, v.isLt⟩⟩

theorem outBelow_mono {D : Orientation n} {u : Fin n} {k l : ℕ} (hkl : k ≤ l) :
    outBelow D u k ⊆ outBelow D u l := by
  intro v hv
  rw [mem_outBelow] at hv ⊢
  exact ⟨hv.1, by omega⟩

theorem card_outBelow_succ {D : Orientation n} (u : Fin n) {k : ℕ} (hk : k < n) :
    (outBelow D u (k + 1)).card
      = (outBelow D u k).card + (if u ∈ D.inN (⟨k, hk⟩ : Fin n) then 1 else 0) := by
  classical
  have hval : ((⟨k, hk⟩ : Fin n) : ℕ) = k := rfl
  by_cases h : u ∈ D.inN (⟨k, hk⟩ : Fin n)
  · rw [if_pos h]
    have hins : outBelow D u (k + 1) = insert (⟨k, hk⟩ : Fin n) (outBelow D u k) := by
      ext v
      rw [mem_outBelow, Finset.mem_insert, mem_outBelow]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge (v : ℕ) k with hv | hv
        · exact Or.inr ⟨h1, hv⟩
        · exact Or.inl (Fin.ext (by rw [hval]; omega))
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨h, by rw [hval]; omega⟩
        · exact ⟨h1, by omega⟩
    have hnot : (⟨k, hk⟩ : Fin n) ∉ outBelow D u k := by
      rw [mem_outBelow, hval]
      rintro ⟨-, hc⟩
      omega
    rw [hins, Finset.card_insert_of_notMem hnot]
  · rw [if_neg h, Nat.add_zero]
    have heq : outBelow D u (k + 1) = outBelow D u k := by
      ext v
      rw [mem_outBelow, mem_outBelow]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rcases Nat.lt_or_ge (v : ℕ) k with hv | hv
        · exact hv
        · exact absurd (show v = (⟨k, hk⟩ : Fin n) from Fin.ext (by rw [hval]; omega))
            (fun hc => h (hc ▸ h1))
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
    rw [heq]
    omega

/-- **The counting sweep counts the out-degree.**  Below the offset of
head `k`, the slots carrying target `u` are in bijection with the heads
below `k` that `u` points at: `sound` puts every such slot's head into
that set, `complete` puts every such head into a slot, and `inj` is that
one head contributes at most one slot. -/
theorem tpCnt_off {o t : String} {ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ}
    {σ : Env} (h : TrInCsr o t D ns off tgt σ) (u : Fin n) :
    ∀ k, k ≤ n → tpCnt tgt (off k) (u : ℕ) = (outBelow D u k).card := by
  classical
  intro k
  induction k with
  | zero => intro _; rw [h.zero, tpCnt_zero, outBelow_zero, Finset.card_empty]
  | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hstep : off (k + 1) = off k + (D.inN (⟨k, hkn⟩ : Fin n)).card :=
        h.step ⟨k, hkn⟩
      have hmono : off k ≤ off (k + 1) := by omega
      have hsplit : (Finset.range (off (k + 1))).filter (fun q => tgt q = (u : ℕ))
          = ((Finset.range (off k)).filter (fun q => tgt q = (u : ℕ)))
            ∪ ((Finset.Ico (off k) (off (k + 1))).filter (fun q => tgt q = (u : ℕ))) := by
        rw [← Finset.filter_union]
        congr 1
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hmono]
      have hdisj : Disjoint ((Finset.range (off k)).filter (fun q => tgt q = (u : ℕ)))
          ((Finset.Ico (off k) (off (k + 1))).filter (fun q => tgt q = (u : ℕ))) := by
        refine Finset.disjoint_left.2 fun q hq hc => ?_
        rw [Finset.mem_filter, Finset.mem_range] at hq
        rw [Finset.mem_filter, Finset.mem_Ico] at hc
        omega
      have hIco : ((Finset.Ico (off k) (off (k + 1))).filter (fun q => tgt q = (u : ℕ))).card
          = (if u ∈ D.inN (⟨k, hkn⟩ : Fin n) then 1 else 0) := by
        by_cases hu : u ∈ D.inN (⟨k, hkn⟩ : Fin n)
        · rw [if_pos hu, Finset.card_eq_one]
          obtain ⟨p, hp1, hp2, hp3⟩ := h.complete ⟨k, hkn⟩ u hu
          refine ⟨p, Finset.eq_singleton_iff_unique_mem.2
            ⟨Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hp1, hp2⟩, hp3⟩, fun q hq => ?_⟩⟩
          rw [Finset.mem_filter, Finset.mem_Ico] at hq
          exact h.inj ⟨k, hkn⟩ q p hq.1.1 hq.1.2 hp1 hp2 (by rw [hq.2, hp3])
        · rw [if_neg hu, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro q hq hcon
          rw [Finset.mem_Ico] at hq
          have hlt : tgt q < n := by rw [hcon]; exact u.isLt
          have hmem := h.sound ⟨k, hkn⟩ q hq.1 hq.2 hlt
          have heq : (⟨tgt q, hlt⟩ : Fin n) = u := Fin.ext hcon
          exact hu (heq ▸ hmem)
      rw [tpCnt, hsplit, Finset.card_union_of_disjoint hdisj, hIco]
      rw [show ((Finset.range (off k)).filter (fun q => tgt q = (u : ℕ))).card
          = tpCnt tgt (off k) (u : ℕ) from rfl, ih (by omega),
        card_outBelow_succ u hkn]

/-- **The sweep's answer, at the extent**: `dg[u]` is `u`'s out-degree,
which is the transpose's own row length. -/
theorem tpCnt_ns {o t : String} {ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ}
    {σ : Env} (h : TrInCsr o t D ns off tgt σ) (u : Fin n) :
    tpCnt tgt ns (u : ℕ) = outDegAt D (u : ℕ) := by
  rw [← h.last, tpCnt_off h u n le_rfl, outBelow_last, outDegAt_coe]

/-- Every offset of the transpose is inside its extent. -/
theorem outOff_mono (D : Orientation n) {a b : ℕ} (hab : a ≤ b) :
    outOff D a ≤ outOff D b := by
  refine Finset.sum_le_sum_of_subset (fun x hx => ?_)
  simp only [Finset.mem_range] at hx ⊢
  omega

theorem outOff_le_arcCount (D : Orientation n) {k : ℕ} (hk : k ≤ n) :
    outOff D k ≤ arcCount D := by
  have := outOff_mono D hk
  rw [outOff_last] at this
  exact this

theorem outOff_le_succ (D : Orientation n) (k : ℕ) : outOff D k ≤ outOff D (k + 1) :=
  outOff_mono D (Nat.le_succ k)

/-! ## §2 The transpose: the program

Three sweeps and one nested pair.  Nothing here reads an array length:
the carrier size is the named cell `nN` and the slot count is `o[nN]`,
the input CSR's own last offset (Finding 1). -/

/-- The transpose's scratch scalars: the slot pointer and the extent,
the carrier counter, the running sum and the degree it reads out before
overwriting the cell, the target, the head, its row pointer and row end,
and the cursor. -/
def tpScalars : List String :=
  ["tp.p", "tp.e", "tp.i", "tp.a", "tp.d", "tp.u", "tp.v", "tp.j", "tp.f", "tp.c"]

/-- The names the transpose keeps apart: it writes `dg`, `qo` and `qt`,
and reads `o` and `t`. -/
structure TpNames (o t qo qt dg : String) : Prop where
  /-- The degrees are not the offsets of the input. -/
  dg_o : dg ≠ o
  /-- The degrees are not the targets of the input. -/
  dg_t : dg ≠ t
  /-- The output offsets are not the input's. -/
  qo_o : qo ≠ o
  /-- The output offsets are not the input's targets. -/
  qo_t : qo ≠ t
  /-- The output offsets are not the degrees. -/
  qo_dg : qo ≠ dg
  /-- The output targets are not the input's offsets. -/
  qt_o : qt ≠ o
  /-- The output targets are not the input's targets. -/
  qt_t : qt ≠ t
  /-- The output targets are not the degrees. -/
  qt_dg : qt ≠ dg
  /-- The two output regions are distinct. -/
  qt_qo : qt ≠ qo

/-- **The counting sweep**: one turn a slot, `dg[t[p]] += 1`.  The
extent is `o[nN]` — the input CSR's last offset, one array read. -/
def tpCntCom (nN o t dg : String) : Com :=
  .seq (.assign "tp.e" (.get o (.var nN)))
    (.seq (.assign "tp.p" (.lit 0))
      (Csr.scan "tp.p" "tp.e"
        (.seq (.assign "tp.u" (.get t (.var "tp.p")))
          (.seq (.store dg (.var "tp.u") (.add (.get dg (.var "tp.u")) (.lit 1)))
            (.assign "tp.p" (.add (.var "tp.p") (.lit 1)))))))

/-- **The prefix sweep**: one turn a vertex.  The degree is read into a
scalar *before* the cell is overwritten, so the same region is the
counter and then the scatter's cursor and no third array exists. -/
def tpOffCom (nN qo dg : String) : Com :=
  .seq (.assign "tp.a" (.lit 0))
    (.seq
      (.seq (.assign "tp.i" (.lit 0))
        (Csr.scan "tp.i" nN
          (.seq (.assign "tp.d" (.get dg (.var "tp.i")))
            (.seq (.store qo (.var "tp.i") (.var "tp.a"))
              (.seq (.store dg (.var "tp.i") (.var "tp.a"))
                (.seq (.assign "tp.a" (.add (.var "tp.a") (.var "tp.d")))
                  (.assign "tp.i" (.add (.var "tp.i") (.lit 1)))))))))
      (.store qo (.var nN) (.var "tp.a")))

/-- One inner turn of the scatter: read the target, take its cursor,
write the head there and bump. -/
def tpScatIn (t qt dg : String) : Com :=
  .seq (.assign "tp.u" (.get t (.var "tp.j")))
    (.seq (.assign "tp.c" (.get dg (.var "tp.u")))
      (.seq (.store qt (.var "tp.c") (.var "tp.v"))
        (.seq (.store dg (.var "tp.u") (.add (.var "tp.c") (.lit 1)))
          (.assign "tp.j" (.add (.var "tp.j") (.lit 1))))))

/-- One outer turn of the scatter: load the head's row and scan it. -/
def tpScatOut (o t qt dg : String) : Com :=
  .seq (.assign "tp.j" (.get o (.var "tp.v")))
    (.seq (.assign "tp.f" (.get o (.add (.var "tp.v") (.lit 1))))
      (.seq (Csr.scan "tp.j" "tp.f" (tpScatIn t qt dg))
        (.assign "tp.v" (.add (.var "tp.v") (.lit 1)))))

/-- **The scatter**: heads in increasing order, each head's whole row
before the next. -/
def tpScatCom (nN o t qt dg : String) : Com :=
  .seq (.assign "tp.v" (.lit 0)) (Csr.scan "tp.v" nN (tpScatOut o t qt dg))

/-- **The transpose**: count, prefix-sum, scatter. -/
def tpCom (nN o t qo qt dg : String) : Com :=
  .seq (tpCntCom nN o t dg) (.seq (tpOffCom nN qo dg) (tpScatCom nN o t qt dg))

/-- **The transpose's budget** at `(n, a)` with `a = arcCount D`.  The
counting sweep costs `17` a slot, the prefix sweep `21` a vertex, and
the scatter `20` a head plus `22` a slot; the fixed blocks add `30`.
`O(n + arcCount D)`, which is all `TransposeIn` asks for. -/
def tpK (n a : ℕ) : ℕ := 41 * n + 40 * a + 30

private theorem tpScalars_ne {y : String} (h : y ∉ tpScalars) :
    y ≠ "tp.p" ∧ y ≠ "tp.e" ∧ y ≠ "tp.i" ∧ y ≠ "tp.a" ∧ y ≠ "tp.d" ∧
      y ≠ "tp.u" ∧ y ≠ "tp.v" ∧ y ≠ "tp.j" ∧ y ≠ "tp.f" ∧ y ≠ "tp.c" := by
  simp only [tpScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- What every sweep of the transpose keeps: the input CSR, the carrier
cell, and the three allocations it writes into. -/
structure TpFrame (nN o t qo qt dg : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The input CSR, untouched. -/
  csr : TrInCsr o t D ns off tgt σ
  /-- The carrier size, in its cell. -/
  carrier : σ.vars nN = n
  /-- The output offsets fit. -/
  qoLen : n + 1 ≤ (σ.arrs qo).length
  /-- The output targets fit. -/
  qtLen : arcCount D ≤ (σ.arrs qt).length
  /-- The degrees fit. -/
  dgLen : n ≤ (σ.arrs dg).length

theorem TpFrame.of_eq {nN o t qo qt dg : String} {n : ℕ} {D : Orientation n} {ns : ℕ}
    {off tgt : ℕ → ℕ} {σ : Env} (h : TpFrame nN o t qo qt dg D ns off tgt σ)
    {σ' : Env} (hv : σ'.vars nN = σ.vars nN)
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t)
    (hqo : (σ'.arrs qo).length = (σ.arrs qo).length)
    (hqt : (σ'.arrs qt).length = (σ.arrs qt).length)
    (hdg : (σ'.arrs dg).length = (σ.arrs dg).length) :
    TpFrame nN o t qo qt dg D ns off tgt σ' where
  csr := h.csr.of_eq ho ht
  carrier := by rw [hv]; exact h.carrier
  qoLen := by rw [hqo]; exact h.qoLen
  qtLen := by rw [hqt]; exact h.qtLen
  dgLen := by rw [hdg]; exact h.dgLen

/-! ## §3 The counting sweep -/

/-- The carried state of the counting sweep: the frame, the extent in
`tp.e`, and `dg` holding the slot counts below the pointer. -/
private def TpCntInv (nN o t qo qt dg : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  TpFrame nN o t qo qt dg D ns off tgt σ ∧ σ.vars "tp.e" = ns ∧
    σ.vars "tp.p" ≤ ns ∧
    ∀ i, i < n → (σ.arrs dg).getD i 0 = tpCnt tgt (σ.vars "tp.p") i

/-- **The counting sweep, discharged**: `dg[u]` ends at `u`'s
out-degree, at `17` a slot. -/
theorem tpCnt_spec {B : ℕ} {nN o t qo qt dg : String} {n : ℕ} {D : Orientation n}
    {ns : ℕ} {off tgt : ℕ → ℕ} (hnm : TpNames o t qo qt dg) (hnN : nN ∉ tpScalars)
    (hB : n + arcCount D < B) (hns : ns = arcCount D) :
    Spec B (fun σ => TpFrame nN o t qo qt dg D ns off tgt σ ∧
        (∀ i, i < n → (σ.arrs dg).getD i 0 = 0))
      (tpCntCom nN o t dg)
      (fun _ σ' => TpFrame nN o t qo qt dg D ns off tgt σ' ∧
        (∀ i, i < n → (σ'.arrs dg).getD i 0 = outDegAt D i))
      (17 * ns + 10) := by
  classical
  obtain ⟨hnp, hne, -, -, -, hnu, -, -, -, -⟩ := tpScalars_ne hnN
  have hbody : Spec B
      (fun σ => TpCntInv nN o t qo qt dg D ns off tgt σ ∧ σ.vars "tp.p" < ns)
      (.seq (.assign "tp.u" (.get t (.var "tp.p")))
        (.seq (.store dg (.var "tp.u") (.add (.get dg (.var "tp.u")) (.lit 1)))
          (.assign "tp.p" (.add (.var "tp.p") (.lit 1)))))
      (fun σ σ' => TpCntInv nN o t qo qt dg D ns off tgt σ' ∧
        σ'.vars "tp.p" = σ.vars "tp.p" + 1) 13 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, hev, hple, hdgv⟩, hlt⟩ := hσ
    obtain ⟨p, hp⟩ : ∃ p, σ.vars "tp.p" = p := ⟨_, rfl⟩
    rw [hp] at hple hlt hdgv
    have hcsr := hfr.csr
    have hnsarc : ns = arcCount D := hcsr.ns_eq_arcCount
    have htlt : tgt p < n := hcsr.tgtLt p hlt
    have htget : (σ.arrs t)[p]? = some (tgt p) := hcsr.tgtGet p hlt
    have hdgL := hfr.dgLen
    have hcv : (σ.arrs dg).getD (tgt p) 0 = tpCnt tgt p (tgt p) := hdgv _ htlt
    have hcle : tpCnt tgt p (tgt p) ≤ p := tpCnt_le tgt p (tgt p)
    have r1 : Run B (.assign "tp.u" (.get t (.var "tp.p"))) σ
        (σ.setVar "tp.u" (tgt p)) 3 :=
      run_assign'' (evB_get' (evB_var' hp (by omega)) htget (by omega)) (by simp)
    have h1u : (σ.setVar "tp.u" (tgt p)).vars "tp.u" = tgt p := by simp
    have h1a : (σ.setVar "tp.u" (tgt p)).arrs = σ.arrs := by simp
    have hcget : ((σ.setVar "tp.u" (tgt p)).arrs dg)[tgt p]? =
        some (tpCnt tgt p (tgt p)) := by
      rw [h1a, ← hcv]; exact getElem?_of_lt' _ _ (by omega)
    have r2 : Run B (.store dg (.var "tp.u") (.add (.get dg (.var "tp.u")) (.lit 1)))
        (σ.setVar "tp.u" (tgt p))
        ((σ.setVar "tp.u" (tgt p)).setArr dg (tgt p) (tpCnt tgt p (tgt p) + 1)) 6 :=
      run_store'' (evB_var' h1u (by omega))
        (evB_add' (evB_get' (evB_var' h1u (by omega)) hcget (by omega))
          (evB_lit' (by omega)) (by omega))
        (by rw [h1a]; omega) (by simp)
    have h2p : ((σ.setVar "tp.u" (tgt p)).setArr dg (tgt p)
        (tpCnt tgt p (tgt p) + 1)).vars "tp.p" = p := by simp [hp]
    have r3 : Run B (.assign "tp.p" (.add (.var "tp.p") (.lit 1)))
        ((σ.setVar "tp.u" (tgt p)).setArr dg (tgt p) (tpCnt tgt p (tgt p) + 1))
        (((σ.setVar "tp.u" (tgt p)).setArr dg (tgt p)
          (tpCnt tgt p (tgt p) + 1)).setVar "tp.p" (p + 1)) 4 :=
      run_assign'' (evB_add' (evB_var' h2p (by omega)) (evB_lit' (by omega))
        (by omega)) (by simp)
    refine ⟨_, 13, (r1.seq (r2.seq r3)).mono (by omega), le_rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hfr.of_eq (by simp [hnp, hnu]) (by simp [Ne.symm hnm.dg_o])
        (by simp [Ne.symm hnm.dg_t]) (by simp [hnm.qo_dg]) (by simp [hnm.qt_dg])
        (by simp)
    · simp [hev]
    · simp; omega
    · intro i hi
      have harr : ((((σ.setVar "tp.u" (tgt p)).setArr dg (tgt p)
          (tpCnt tgt p (tgt p) + 1)).setVar "tp.p" (p + 1)).arrs dg)
          = (σ.arrs dg).set (tgt p) (tpCnt tgt p (tgt p) + 1) := by simp
      have hpv : ((((σ.setVar "tp.u" (tgt p)).setArr dg (tgt p)
          (tpCnt tgt p (tgt p) + 1)).setVar "tp.p" (p + 1)).vars "tp.p") = p + 1 := by
        simp
      rw [harr, hpv, tpCnt_succ]
      by_cases hti : tgt p = i
      · subst hti
        rw [getD_set_self' (by omega), if_pos rfl]
      · rw [getD_set_of_ne' hti, if_neg hti, Nat.add_zero]
        exact hdgv i hi
    · simp [hp]
  have hpre : Spec B
      (fun σ => TpFrame nN o t qo qt dg D ns off tgt σ ∧
        (∀ i, i < n → (σ.arrs dg).getD i 0 = 0))
      (.assign "tp.e" (.get o (.var nN)))
      (fun _ σ' => TpCntInv nN o t qo qt dg D ns off tgt (σ'.setVar "tp.p" 0)) 3 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hdg0⟩ := hσ
    have hcsr := hfr.csr
    have hnsarc : ns = arcCount D := hcsr.ns_eq_arcCount
    have hoget : (σ.arrs o)[n]? = some ns := by rw [hcsr.offGet n le_rfl, hcsr.last]
    have r1 : Run B (.assign "tp.e" (.get o (.var nN))) σ (σ.setVar "tp.e" ns) 3 :=
      run_assign'' (evB_get' (evB_var' hfr.carrier (by omega)) hoget (by omega))
        (by simp)
    refine ⟨_, 3, r1, le_rfl, ?_, ?_, ?_, ?_⟩
    · exact hfr.of_eq (by simp [hne, hnp]) (by simp) (by simp) (by simp) (by simp)
        (by simp)
    · simp
    · simp
    · intro i hi
      rw [show ((σ.setVar "tp.e" ns).setVar "tp.p" 0).arrs dg = σ.arrs dg from by simp,
        show ((σ.setVar "tp.e" ns).setVar "tp.p" 0).vars "tp.p" = 0 from by simp,
        tpCnt_zero]
      exact hdg0 i hi
  have hloop := Spec.forRangeZero (B := B) "tp.p" "tp.e"
    (TpCntInv nN o t qo qt dg D ns off tgt) ns 13 (by omega)
    (fun σ hI => hI.2.2.1) (fun σ hI => hI.2.1) hbody
  refine ((Spec.seq hpre hloop (fun σ σ' _ hq => hq) (fun σ σ' σ'' _ _ hq => ?_)).mono
    (by omega))
  obtain ⟨⟨hfr, -, -, hdgv⟩, hend⟩ := hq
  refine ⟨hfr, fun i hi => ?_⟩
  rw [hdgv i hi, hend]
  have := tpCnt_ns (h := hfr.csr) ⟨i, hi⟩
  exact this

/-! ## §4 The prefix sweep -/

theorem outDegAt_le_arcCount (D : Orientation n) (i : ℕ) : outDegAt D i ≤ arcCount D := by
  rcases Nat.lt_or_ge i n with h | h
  · have h1 : outOff D (i + 1) = outOff D i + outDegAt D i := outOff_succ D i
    have h2 : outOff D (i + 1) ≤ arcCount D := outOff_le_arcCount D (by omega)
    omega
  · rw [outDegAt, dif_neg (by omega)]
    exact Nat.zero_le _

/-- The carried state of the prefix sweep: below the counter the two
regions hold the offsets, above it `dg` still holds the degrees, and the
running sum is the offset at the counter. -/
private def TpOffInv (nN o t qo qt dg : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  TpFrame nN o t qo qt dg D ns off tgt σ ∧ σ.vars "tp.i" ≤ n ∧
    σ.vars "tp.a" = outOff D (σ.vars "tp.i") ∧
    (∀ i, i < σ.vars "tp.i" → (σ.arrs qo).getD i 0 = outOff D i) ∧
    (∀ i, i < σ.vars "tp.i" → (σ.arrs dg).getD i 0 = outOff D i) ∧
    (∀ i, σ.vars "tp.i" ≤ i → i < n → (σ.arrs dg).getD i 0 = outDegAt D i)

/-- **The prefix sweep, discharged**: `qo` holds `outOff D` on `[0, n]`
and `dg` is reset to the row starts, at `21` a vertex. -/
theorem tpOff_spec {B : ℕ} {nN o t qo qt dg : String} {n : ℕ} {D : Orientation n}
    {ns : ℕ} {off tgt : ℕ → ℕ} (hnm : TpNames o t qo qt dg) (hnN : nN ∉ tpScalars)
    (hB : n + arcCount D < B) :
    Spec B (fun σ => TpFrame nN o t qo qt dg D ns off tgt σ ∧
        (∀ i, i < n → (σ.arrs dg).getD i 0 = outDegAt D i))
      (tpOffCom nN qo dg)
      (fun _ σ' => TpFrame nN o t qo qt dg D ns off tgt σ' ∧
        (∀ i, i ≤ n → (σ'.arrs qo).getD i 0 = outOff D i) ∧
        (∀ i, i < n → (σ'.arrs dg).getD i 0 = outOff D i))
      (21 * n + 12) := by
  classical
  obtain ⟨-, -, hni, hna, hnd, -, -, -, -, -⟩ := tpScalars_ne hnN
  have hbody : Spec B
      (fun σ => TpOffInv nN o t qo qt dg D ns off tgt σ ∧ σ.vars "tp.i" < n)
      (.seq (.assign "tp.d" (.get dg (.var "tp.i")))
        (.seq (.store qo (.var "tp.i") (.var "tp.a"))
          (.seq (.store dg (.var "tp.i") (.var "tp.a"))
            (.seq (.assign "tp.a" (.add (.var "tp.a") (.var "tp.d")))
              (.assign "tp.i" (.add (.var "tp.i") (.lit 1)))))))
      (fun σ σ' => TpOffInv nN o t qo qt dg D ns off tgt σ' ∧
        σ'.vars "tp.i" = σ.vars "tp.i" + 1) 17 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, hile, hav, hqov, hdgv, hdegv⟩, hlt⟩ := hσ
    obtain ⟨i, hi⟩ : ∃ i, σ.vars "tp.i" = i := ⟨_, rfl⟩
    rw [hi] at hile hav hqov hdgv hdegv hlt
    have hdgL := hfr.dgLen
    have hqoL := hfr.qoLen
    have hdgi : (σ.arrs dg).getD i 0 = outDegAt D i := hdegv i le_rfl hlt
    have hdeglt : outDegAt D i ≤ arcCount D := outDegAt_le_arcCount D i
    have hoffi : outOff D i ≤ arcCount D := outOff_le_arcCount D (by omega)
    have hoffs : outOff D (i + 1) = outOff D i + outDegAt D i := outOff_succ D i
    have hoffi1 : outOff D (i + 1) ≤ arcCount D := outOff_le_arcCount D (by omega)
    have hdget : (σ.arrs dg)[i]? = some (outDegAt D i) := by
      rw [← hdgi]; exact getElem?_of_lt' _ _ (by omega)
    -- `tp.d := dg[i]`
    have r1 : Run B (.assign "tp.d" (.get dg (.var "tp.i"))) σ
        (σ.setVar "tp.d" (outDegAt D i)) 3 :=
      run_assign'' (evB_get' (evB_var' hi (by omega)) hdget (by omega)) (by simp)
    have e1i : (σ.setVar "tp.d" (outDegAt D i)).vars "tp.i" = i := by simp [hi]
    have e1a : (σ.setVar "tp.d" (outDegAt D i)).vars "tp.a" = outOff D i := by simp [hav]
    -- `qo[i] := tp.a`
    have r2 : Run B (.store qo (.var "tp.i") (.var "tp.a"))
        (σ.setVar "tp.d" (outDegAt D i))
        ((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)) 3 :=
      run_store'' (evB_var' e1i (by omega)) (evB_var' e1a (by omega))
        (by simp; omega) (by simp)
    -- `dg[i] := tp.a`
    have e2i : ((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).vars "tp.i"
        = i := by simp [hi]
    have e2a : ((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).vars "tp.a"
        = outOff D i := by simp [hav]
    have r3 : Run B (.store dg (.var "tp.i") (.var "tp.a"))
        ((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i))
        (((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr dg i
          (outOff D i)) 3 :=
      run_store'' (evB_var' e2i (by omega)) (evB_var' e2a (by omega))
        (by simp [Ne.symm hnm.qo_dg]; omega) (by simp)
    have e3a : ((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr dg i
        (outOff D i)).vars "tp.a") = outOff D i := by simp [hav]
    have e3d : ((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr dg i
        (outOff D i)).vars "tp.d") = outDegAt D i := by simp
    -- `tp.a := tp.a + tp.d`
    have r4 : Run B (.assign "tp.a" (.add (.var "tp.a") (.var "tp.d")))
        ((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr dg i
          (outOff D i)))
        (((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr dg i
          (outOff D i))).setVar "tp.a" (outOff D i + outDegAt D i)) 4 :=
      run_assign'' (evB_add' (evB_var' e3a (by omega)) (evB_var' e3d (by omega))
        (by omega)) (by simp)
    have e4i : (((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr dg i
        (outOff D i))).setVar "tp.a" (outOff D i + outDegAt D i)).vars "tp.i" = i := by
      simp [hi]
    -- `tp.i := tp.i + 1`
    have r5 : Run B (.assign "tp.i" (.add (.var "tp.i") (.lit 1)))
        (((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr dg i
          (outOff D i))).setVar "tp.a" (outOff D i + outDegAt D i))
        ((((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr dg i
          (outOff D i))).setVar "tp.a" (outOff D i + outDegAt D i)).setVar "tp.i"
            (i + 1)) 4 :=
      run_assign'' (evB_add' (evB_var' e4i (by omega)) (evB_lit' (by omega))
        (by omega)) (by simp)
    refine ⟨_, 17, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), le_rfl,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hfr.of_eq (by simp [hni, hna, hnd])
        (by simp [Ne.symm hnm.dg_o, Ne.symm hnm.qo_o])
        (by simp [Ne.symm hnm.dg_t, Ne.symm hnm.qo_t])
        (by simp [hnm.qo_dg]) (by simp [hnm.qt_dg, hnm.qt_qo])
        (by simp [Ne.symm hnm.qo_dg])
    · simp; omega
    · simp [hoffs]
    · intro k hk
      have hk' : k < i + 1 := by simpa using hk
      have harr : ((((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr
          dg i (outOff D i))).setVar "tp.a" (outOff D i + outDegAt D i)).setVar "tp.i"
            (i + 1)).arrs qo = (σ.arrs qo).set i (outOff D i) := by
        simp [hnm.qo_dg]
      rw [harr]
      rcases Nat.lt_or_ge k i with h | h
      · rw [getD_set_of_ne' (by omega)]; exact hqov k h
      · obtain rfl : k = i := by omega
        exact getD_set_self' (by omega)
    · intro k hk
      have hk' : k < i + 1 := by simpa using hk
      have harr : ((((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr
          dg i (outOff D i))).setVar "tp.a" (outOff D i + outDegAt D i)).setVar "tp.i"
            (i + 1)).arrs dg = (σ.arrs dg).set i (outOff D i) := by
        simp [Ne.symm hnm.qo_dg]
      rw [harr]
      rcases Nat.lt_or_ge k i with h | h
      · rw [getD_set_of_ne' (by omega)]; exact hdgv k h
      · obtain rfl : k = i := by omega
        exact getD_set_self' (by omega)
    · intro k hk1 hk2
      have hk' : i + 1 ≤ k := by simpa using hk1
      have harr : ((((((σ.setVar "tp.d" (outDegAt D i)).setArr qo i (outOff D i)).setArr
          dg i (outOff D i))).setVar "tp.a" (outOff D i + outDegAt D i)).setVar "tp.i"
            (i + 1)).arrs dg = (σ.arrs dg).set i (outOff D i) := by
        simp [Ne.symm hnm.qo_dg]
      rw [harr, getD_set_of_ne' (by omega)]
      exact hdegv k (by omega) hk2
    · simp [hi]
  have hstart : Spec B
      (fun σ => TpFrame nN o t qo qt dg D ns off tgt σ ∧
        (∀ i, i < n → (σ.arrs dg).getD i 0 = outDegAt D i))
      (.assign "tp.a" (.lit 0))
      (fun _ σ' => TpOffInv nN o t qo qt dg D ns off tgt (σ'.setVar "tp.i" 0)) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hdeg⟩ := hσ
    have r1 : Run B (.assign "tp.a" (.lit 0)) σ (σ.setVar "tp.a" 0) 2 :=
      run_assign'' (evB_lit' (by omega)) (by simp)
    refine ⟨_, 2, r1, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hfr.of_eq (by simp [hna, hni]) (by simp) (by simp) (by simp) (by simp)
        (by simp)
    · simp
    · simp [outOff]
    · intro k hk; simp at hk
    · intro k hk; simp at hk
    · intro k hk1 hk2
      rw [show (((σ.setVar "tp.a" 0).setVar "tp.i" 0).arrs dg) = σ.arrs dg from by simp]
      exact hdeg k hk2
  have hloop := Spec.forRangeZero (B := B) "tp.i" nN
    (TpOffInv nN o t qo qt dg D ns off tgt) n 17 (by omega)
    (fun σ hI => hI.2.1) (fun σ hI => hI.1.carrier) hbody
  have htail : Spec B
      (fun σ => TpOffInv nN o t qo qt dg D ns off tgt σ ∧ σ.vars "tp.i" = n)
      (.store qo (.var nN) (.var "tp.a"))
      (fun _ σ' => TpFrame nN o t qo qt dg D ns off tgt σ' ∧
        (∀ i, i ≤ n → (σ'.arrs qo).getD i 0 = outOff D i) ∧
        (∀ i, i < n → (σ'.arrs dg).getD i 0 = outOff D i)) 3 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hfr, hile, hav, hqov, hdgv, -⟩, hend⟩ := hσ
    rw [hend] at hav hqov hdgv
    have hoffn : outOff D n ≤ arcCount D := outOff_le_arcCount D le_rfl
    have hqoL := hfr.qoLen
    have r1 : Run B (.store qo (.var nN) (.var "tp.a")) σ
        (σ.setArr qo n (outOff D n)) 3 :=
      run_store'' (evB_var' hfr.carrier (by omega)) (evB_var' hav (by omega))
        (by omega) (by simp)
    refine ⟨_, 3, r1, le_rfl, ?_, ?_, ?_⟩
    · exact hfr.of_eq (by simp) (by simp [Ne.symm hnm.qo_o]) (by simp [Ne.symm hnm.qo_t])
        (by simp) (by simp [hnm.qt_qo]) (by simp [Ne.symm hnm.qo_dg])
    · intro k hk
      rw [show ((σ.setArr qo n (outOff D n)).arrs qo) = (σ.arrs qo).set n (outOff D n)
        from by simp]
      rcases Nat.lt_or_ge k n with h | h
      · rw [getD_set_of_ne' (by omega)]; exact hqov k h
      · obtain rfl : k = n := by omega
        exact getD_set_self' (by omega)
    · intro k hk
      rw [show ((σ.setArr qo n (outOff D n)).arrs dg) = σ.arrs dg
        from by simp [Ne.symm hnm.qo_dg]]
      exact hdgv k hk
  refine ((Spec.seq hstart (Spec.seq hloop htail (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' _ _ hq => hq)) (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' _ _ hq => hq)).mono (by omega))

/-! ## §5 The scatter

The heads run in increasing order, so the flat slot pointer of the input
CSR is *also* the scatter's clock: after the slots below `P` have been
placed, the cursor of `u` stands at `outOff D u + tpCnt tgt P u`.  The
carried statement `fill` is therefore not "row `u` holds a set of
out-neighbours" but the exact address of each: **slot
`outOff D u + tpCnt tgt (off a) u` holds the head `a`**.  That pins
`OutCsrAt`'s `inj` outright — two slots holding the same head are the
same address — and `complete` then follows by counting, because an
injection of a row into `outNbrs D u` between sets of the same size is
onto. -/

theorem tpCnt_mono (tgt : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) (u : ℕ) :
    tpCnt tgt a u ≤ tpCnt tgt b u := by
  refine Finset.card_le_card (fun x hx => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

/-- **A head hits a target at most once.**  Row `k` of the input has no
repeated target (`TrInCsr.inj`), so the slots of the row before `j` add
nothing to the count of `tgt j`: the cursor the scatter reads at slot
`j` is the one it had at the *start* of head `k`'s turn. -/
theorem tpCnt_eq_of_row {o t : String} {ns : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ}
    {σ : Env} (h : TrInCsr o t D ns off tgt σ) {k j : ℕ} (hk : k < n)
    (hj1 : off k ≤ j) (hj2 : j < off (k + 1)) :
    tpCnt tgt j (tgt j) = tpCnt tgt (off k) (tgt j) := by
  classical
  have hsplit : (Finset.range j).filter (fun q => tgt q = tgt j)
      = ((Finset.range (off k)).filter (fun q => tgt q = tgt j))
        ∪ ((Finset.Ico (off k) j).filter (fun q => tgt q = tgt j)) := by
    rw [← Finset.filter_union]
    congr 1
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hj1]
  have hempty : (Finset.Ico (off k) j).filter (fun q => tgt q = tgt j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro q hq hc
    rw [Finset.mem_Ico] at hq
    have := h.inj ⟨k, hk⟩ q j hq.1 (show q < off (k + 1) by omega) hj1 hj2 hc
    omega
  rw [tpCnt, tpCnt, hsplit, hempty, Finset.union_empty]

/-- Distinct heads own disjoint slices of the transpose. -/
theorem outOff_row_ne {D : Orientation n} {a b q r : ℕ} (hab : a ≠ b)
    (hq1 : outOff D a ≤ q) (hq2 : q < outOff D (a + 1))
    (hr1 : outOff D b ≤ r) (hr2 : r < outOff D (b + 1)) : q ≠ r := by
  rcases Nat.lt_or_ge a b with h | h
  · have : outOff D (a + 1) ≤ outOff D b := outOff_mono D (by omega)
    omega
  · have : outOff D (b + 1) ≤ outOff D a := outOff_mono D (by omega)
    omega

/-- **What the scatter has built after the slots below `P`.**  The
cursor of `u` is `outOff D u + tpCnt tgt P u`, and each filled slot
holds the head that put it there, at the address that head's own clock
determines. -/
structure TpScatSt (qt dg : String) {n : ℕ} (D : Orientation n) (off tgt : ℕ → ℕ)
    (P : ℕ) (σ : Env) : Prop where
  /-- The cursor of `u`. -/
  cur : ∀ u : Fin n, (σ.arrs dg).getD (u : ℕ) 0 = outOff D (u : ℕ) + tpCnt tgt P (u : ℕ)
  /-- Each filled slot of row `u` holds a head that points at `u`, at
  the address that head's clock gives it. -/
  fill : ∀ (u : Fin n) (q : ℕ), outOff D (u : ℕ) ≤ q →
    q < outOff D (u : ℕ) + tpCnt tgt P (u : ℕ) →
    ∃ h : (σ.arrs qt).getD q 0 < n,
      u ∈ D.inN (⟨(σ.arrs qt).getD q 0, h⟩ : Fin n) ∧
      q = outOff D (u : ℕ) + tpCnt tgt (off ((σ.arrs qt).getD q 0)) (u : ℕ)

/-- The carried state of one head's inner scan. -/
private def TpScInv (nN o t qo qt dg : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (k : ℕ) (σ : Env) : Prop :=
  TpFrame nN o t qo qt dg D ns off tgt σ ∧
    (∀ i, i ≤ n → (σ.arrs qo).getD i 0 = outOff D i) ∧
    σ.vars "tp.v" = k ∧ σ.vars "tp.f" = off (k + 1) ∧
    off k ≤ σ.vars "tp.j" ∧ σ.vars "tp.j" ≤ off (k + 1) ∧
    TpScatSt qt dg D off tgt (σ.vars "tp.j") σ

/-- The carried state of the scatter's outer scan. -/
private def TpScOInv (nN o t qo qt dg : String) {n : ℕ} (D : Orientation n) (ns : ℕ)
    (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  TpFrame nN o t qo qt dg D ns off tgt σ ∧
    (∀ i, i ≤ n → (σ.arrs qo).getD i 0 = outOff D i) ∧
    σ.vars "tp.v" ≤ n ∧
    TpScatSt qt dg D off tgt (off (σ.vars "tp.v")) σ

/-- **One inner turn of the scatter**, at `18`: read the target, take
its cursor, write the head there, bump. -/
private theorem tpScatIn_step {B : ℕ} {nN o t qo qt dg : String} {n : ℕ}
    {D : Orientation n} {ns : ℕ} {off tgt : ℕ → ℕ} {k : ℕ} {σ : Env}
    (hnm : TpNames o t qo qt dg) (hnN : nN ∉ tpScalars)
    (hB : n + arcCount D < B) (hns : ns = arcCount D)
    (hk : k < n) (hI : TpScInv nN o t qo qt dg D ns off tgt k σ)
    (hlt : σ.vars "tp.j" < off (k + 1)) :
    ∃ σ' K', Run B (tpScatIn t qt dg) σ σ' K' ∧
      TpScInv nN o t qo qt dg D ns off tgt k σ' ∧
      σ'.vars "tp.j" = σ.vars "tp.j" + 1 ∧ K' ≤ 18 := by
  classical
  obtain ⟨-, -, -, -, -, hnu, -, hnj, -, hnc⟩ := tpScalars_ne hnN
  obtain ⟨hfr, hqov, hvv, hfv, hj1, hj2, hst⟩ := hI
  obtain ⟨j, hj⟩ : ∃ j, σ.vars "tp.j" = j := ⟨_, rfl⟩
  rw [hj] at hj1 hj2 hlt hst
  have hcsr := hfr.csr
  have hoffle : off (k + 1) ≤ ns := hcsr.off_le_ns hk
  have hjns : j < ns := by omega
  have hul : tgt j < n := hcsr.tgtLt j hjns
  have htget : (σ.arrs t)[j]? = some (tgt j) := hcsr.tgtGet j hjns
  have hcv : (σ.arrs dg).getD (tgt j) 0 = outOff D (tgt j) + tpCnt tgt j (tgt j) :=
    hst.cur ⟨tgt j, hul⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = outOff D (tgt j) + tpCnt tgt j (tgt j) := ⟨_, rfl⟩
  rw [← hcd] at hcv
  have hsucc : tpCnt tgt (j + 1) (tgt j) = tpCnt tgt j (tgt j) + 1 := by
    rw [tpCnt_succ, if_pos rfl]
  have hcnt1 : tpCnt tgt (j + 1) (tgt j) ≤ tpCnt tgt ns (tgt j) :=
    tpCnt_mono tgt (by omega) _
  have hdeg : tpCnt tgt ns (tgt j) = outDegAt D (tgt j) :=
    tpCnt_ns hcsr ⟨tgt j, hul⟩
  have hoffsucc : outOff D (tgt j + 1) = outOff D (tgt j) + outDegAt D (tgt j) :=
    outOff_succ D (tgt j)
  have hoffb : outOff D (tgt j + 1) ≤ arcCount D := outOff_le_arcCount D (by omega)
  have hcb : c + 1 ≤ arcCount D := by omega
  have hc1 : outOff D (tgt j) ≤ c := by omega
  have hc2 : c < outOff D (tgt j + 1) := by omega
  have hqtL := hfr.qtLen
  have hdgL := hfr.dgLen
  -- `tp.u := t[tp.j]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "tp.u" (tgt j) := ⟨_, rfl⟩
  have r1 : Run B (.assign "tp.u" (.get t (.var "tp.j"))) σ σ1 3 := by
    rw [hσ1]
    exact run_assign'' (evB_get' (evB_var' hj (by omega)) htget (by omega)) (by simp)
  have h1u : σ1.vars "tp.u" = tgt j := by rw [hσ1]; simp
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  have hcget : (σ1.arrs dg)[tgt j]? = some c := by
    rw [h1a, ← hcv]; exact getElem?_of_lt' _ _ (by omega)
  -- `tp.c := dg[tp.u]`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "tp.c" c := ⟨_, rfl⟩
  have r2 : Run B (.assign "tp.c" (.get dg (.var "tp.u"))) σ1 σ2 3 := by
    rw [hσ2]
    exact run_assign'' (evB_get' (evB_var' h1u (by omega)) hcget (by omega)) (by simp)
  have h2c : σ2.vars "tp.c" = c := by rw [hσ2]; simp
  have h2u : σ2.vars "tp.u" = tgt j := by rw [hσ2, hσ1]; simp
  have h2v : σ2.vars "tp.v" = k := by rw [hσ2, hσ1]; simp [hvv]
  have h2a : σ2.arrs = σ.arrs := by rw [hσ2, hσ1]; simp
  -- `qt[tp.c] := tp.v`
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setArr qt c k := ⟨_, rfl⟩
  have r3 : Run B (.store qt (.var "tp.c") (.var "tp.v")) σ2 σ3 3 := by
    rw [hσ3]
    exact run_store'' (evB_var' h2c (by omega)) (evB_var' h2v (by omega))
      (by rw [h2a]; omega) (by simp)
  have h3c : σ3.vars "tp.c" = c := by rw [hσ3]; simp [h2c]
  have h3u : σ3.vars "tp.u" = tgt j := by rw [hσ3]; simp [h2u]
  have h3qt : σ3.arrs qt = (σ.arrs qt).set c k := by rw [hσ3]; simp [h2a]
  have h3dg : σ3.arrs dg = σ.arrs dg := by
    rw [hσ3]; simp [h2a, Ne.symm hnm.qt_dg]
  -- `dg[tp.u] := tp.c + 1`
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setArr dg (tgt j) (c + 1) := ⟨_, rfl⟩
  have r4 : Run B (.store dg (.var "tp.u") (.add (.var "tp.c") (.lit 1))) σ3 σ4 5 := by
    rw [hσ4]
    exact run_store'' (evB_var' h3u (by omega))
      (evB_add' (evB_var' h3c (by omega)) (evB_lit' (by omega)) (by omega))
      (by rw [h3dg]; omega) (by simp)
  have h4j : σ4.vars "tp.j" = j := by rw [hσ4, hσ3, hσ2, hσ1]; simp [hj]
  -- `tp.j := tp.j + 1`
  obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = σ4.setVar "tp.j" (j + 1) := ⟨_, rfl⟩
  have r5 : Run B (.assign "tp.j" (.add (.var "tp.j") (.lit 1))) σ4 σ5 4 := by
    rw [hσ5]
    exact run_assign'' (evB_add' (evB_var' h4j (by omega)) (evB_lit' (by omega))
      (by omega)) (by simp)
  -- the arrays of the final state
  have h5qt : σ5.arrs qt = (σ.arrs qt).set c k := by
    rw [hσ5, hσ4]; simp [h3qt, hnm.qt_dg]
  have h5dg : σ5.arrs dg = (σ.arrs dg).set (tgt j) (c + 1) := by
    rw [hσ5, hσ4]; simp [h3dg]
  have h5o : σ5.arrs o = σ.arrs o := by
    rw [hσ5, hσ4, hσ3, hσ2, hσ1]
    simp [Ne.symm hnm.dg_o, Ne.symm hnm.qt_o]
  have h5t : σ5.arrs t = σ.arrs t := by
    rw [hσ5, hσ4, hσ3, hσ2, hσ1]
    simp [Ne.symm hnm.dg_t, Ne.symm hnm.qt_t]
  have h5qo : σ5.arrs qo = σ.arrs qo := by
    rw [hσ5, hσ4, hσ3, hσ2, hσ1]
    simp [hnm.qo_dg, Ne.symm hnm.qt_qo]
  have h5nN : σ5.vars nN = σ.vars nN := by
    rw [hσ5, hσ4, hσ3, hσ2, hσ1]
    simp [hnj, hnc, hnu]
  refine ⟨σ5, 18, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), ?_, ?_, le_rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hfr.of_eq h5nN h5o h5t (by rw [h5qo]) (by rw [h5qt, List.length_set])
        (by rw [h5dg, List.length_set])
    · intro i hi; rw [h5qo]; exact hqov i hi
    · rw [hσ5, hσ4, hσ3, hσ2, hσ1]; simp [hvv]
    · rw [hσ5, hσ4, hσ3, hσ2, hσ1]; simp [hfv]
    · rw [hσ5]; simp; omega
    · rw [hσ5]; simp; omega
    · have hjv : σ5.vars "tp.j" = j + 1 := by rw [hσ5]; simp
      rw [hjv]
      refine ⟨?_, ?_⟩
      · intro u
        rw [h5dg]
        by_cases hu : (u : ℕ) = tgt j
        · rw [hu, getD_set_self' (by omega), hsucc]
          omega
        · rw [getD_set_of_ne' (Ne.symm hu), hst.cur u, tpCnt_succ,
            if_neg (fun hc => hu hc.symm), Nat.add_zero]
      · intro u q hq1 hq2
        rw [h5qt]
        by_cases hu : (u : ℕ) = tgt j
        · rw [tpCnt_succ, if_pos hu.symm] at hq2
          have hcu : c = outOff D (u : ℕ) + tpCnt tgt j (u : ℕ) := by rw [hu]; exact hcd
          rcases Nat.lt_or_ge q c with hqc | hqc
          · rw [getD_set_of_ne' (by omega)]
            exact hst.fill u q hq1 (by omega)
          · obtain rfl : q = c := by omega
            rw [getD_set_self' (by omega)]
            refine ⟨hk, ?_, ?_⟩
            · have hs := hcsr.sound ⟨k, hk⟩ j hj1 hlt hul
              have huu : u = (⟨tgt j, hul⟩ : Fin n) := Fin.ext hu
              rw [huu]; exact hs
            · rw [hu, hcd, tpCnt_eq_of_row hcsr hk hj1 hlt]
        · rw [tpCnt_succ, if_neg (fun hc => hu hc.symm), Nat.add_zero] at hq2
          have hcnt2 : tpCnt tgt j (u : ℕ) ≤ tpCnt tgt ns (u : ℕ) :=
            tpCnt_mono tgt (by omega) _
          have hdeg2 : tpCnt tgt ns (u : ℕ) = outDegAt D (u : ℕ) := tpCnt_ns hcsr u
          have hoff2 : outOff D ((u : ℕ) + 1) = outOff D (u : ℕ) + outDegAt D (u : ℕ) :=
            outOff_succ D (u : ℕ)
          have hqc : q ≠ c :=
            outOff_row_ne (D := D) hu hq1 (by omega) hc1 hc2
          rw [getD_set_of_ne' (Ne.symm hqc)]
          exact hst.fill u q hq1 hq2
  · rw [hσ5]; simp [hj]

theorem TpScatSt.of_eq {qt dg : String} {n : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ}
    {P : ℕ} {σ : Env} (h : TpScatSt qt dg D off tgt P σ) {σ' : Env}
    (hqt : σ'.arrs qt = σ.arrs qt) (hdg : σ'.arrs dg = σ.arrs dg) :
    TpScatSt qt dg D off tgt P σ' where
  cur := by rw [hdg]; exact h.cur
  fill := by rw [hqt]; exact h.fill

/-- **The scatter's inner scan**: one head's whole row, at `22` a
slot. -/
private theorem tpScatIn_scan {B : ℕ} {nN o t qo qt dg : String} {n : ℕ}
    {D : Orientation n} {ns : ℕ} {off tgt : ℕ → ℕ} {k : ℕ}
    (hnm : TpNames o t qo qt dg) (hnN : nN ∉ tpScalars)
    (hB : n + arcCount D < B) (hns : ns = arcCount D) (hk : k < n)
    (hoff : off (k + 1) ≤ ns) :
    Spec B (fun σ => TpScInv nN o t qo qt dg D ns off tgt k σ ∧
        σ.vars "tp.j" = off k)
      (Csr.scan "tp.j" "tp.f" (tpScatIn t qt dg))
      (fun _ σ' => TpScInv nN o t qo qt dg D ns off tgt k σ' ∧
        σ'.vars "tp.j" = off (k + 1))
      (22 * (off (k + 1) - off k) + 4) :=
  Csr.rowScan_spec B _ (off (k + 1)) 18 "tp.j" "tp.f" (tpScatIn t qt dg)
    (fun σ => TpScInv nN o t qo qt dg D ns off tgt k σ) (by omega)
    (fun _ hI => ⟨hI.2.2.2.1, hI.2.2.2.2.2.1⟩)
    (fun _ hI hlt => tpScatIn_step hnm hnN hB hns hk hI hlt)
    (fun _ h => h.1) (fun _ h => by have := h.2; omega)

/-- **One outer turn of the scatter**: load the head's row and scan
it. -/
private theorem tpScatOut_step {B : ℕ} {nN o t qo qt dg : String} {n : ℕ}
    {D : Orientation n} {ns : ℕ} {off tgt : ℕ → ℕ} {σ : Env}
    (hnm : TpNames o t qo qt dg) (hnN : nN ∉ tpScalars)
    (hB : n + arcCount D < B) (hns : ns = arcCount D)
    (hO : TpScOInv nN o t qo qt dg D ns off tgt σ) (hlt : σ.vars "tp.v" < n) :
    ∃ σ' K', Run B (tpScatOut o t qt dg) σ σ' K' ∧
      TpScOInv nN o t qo qt dg D ns off tgt σ' ∧
      σ'.vars "tp.v" = σ.vars "tp.v" + 1 ∧
      K' ≤ 16 + 22 * (off (σ.vars "tp.v" + 1) - off (σ.vars "tp.v")) := by
  classical
  obtain ⟨-, -, -, -, -, -, hnv, hnj, hnf, -⟩ := tpScalars_ne hnN
  obtain ⟨hfr, hqov, hvle, hst⟩ := hO
  obtain ⟨k, hk⟩ : ∃ k, σ.vars "tp.v" = k := ⟨_, rfl⟩
  rw [hk] at hvle hst hlt
  have hcsr := hfr.csr
  have hoff1 : off k ≤ off (k + 1) := hcsr.mono (k + 1) hlt k (by omega)
  have hoffle : off (k + 1) ≤ ns := hcsr.off_le_ns hlt
  have hoget : (σ.arrs o)[k]? = some (off k) := hcsr.offGet k (by omega)
  have hoget1 : (σ.arrs o)[k + 1]? = some (off (k + 1)) := hcsr.offGet (k + 1) hlt
  -- `tp.j := o[tp.v]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "tp.j" (off k) := ⟨_, rfl⟩
  have r1 : Run B (.assign "tp.j" (.get o (.var "tp.v"))) σ σ1 3 := by
    rw [hσ1]
    exact run_assign'' (evB_get' (evB_var' hk (by omega)) hoget (by omega)) (by simp)
  have h1v : σ1.vars "tp.v" = k := by rw [hσ1]; simp [hk]
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  -- `tp.f := o[tp.v + 1]`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "tp.f" (off (k + 1)) := ⟨_, rfl⟩
  have r2 : Run B (.assign "tp.f" (.get o (.add (.var "tp.v") (.lit 1)))) σ1 σ2 5 := by
    rw [hσ2]
    refine run_assign'' (evB_get' (evB_add' (evB_var' h1v (by omega))
      (evB_lit' (by omega)) (by omega)) ?_ (by omega)) (by simp)
    rw [h1a]; exact hoget1
  have h2a : σ2.arrs = σ.arrs := by rw [hσ2, hσ1]; simp
  have h2v : σ2.vars "tp.v" = k := by rw [hσ2]; simp [h1v]
  have h2f : σ2.vars "tp.f" = off (k + 1) := by rw [hσ2]; simp
  have h2j : σ2.vars "tp.j" = off k := by rw [hσ2, hσ1]; simp
  have h2nN : σ2.vars nN = σ.vars nN := by rw [hσ2, hσ1]; simp [hnf, hnj]
  have hI2 : TpScInv nN o t qo qt dg D ns off tgt k σ2 ∧ σ2.vars "tp.j" = off k := by
    refine ⟨⟨?_, ?_, h2v, h2f, h2j.ge, by rw [h2j]; exact hoff1, ?_⟩, h2j⟩
    · exact hfr.of_eq h2nN (by rw [h2a]) (by rw [h2a]) (by rw [h2a]) (by rw [h2a])
        (by rw [h2a])
    · intro i hi; rw [h2a]; exact hqov i hi
    · rw [h2j]; exact hst.of_eq (by rw [h2a]) (by rw [h2a])
  obtain ⟨σ3, hr3, hI3, hj3⟩ := (tpScatIn_scan hnm hnN hB hns hlt hoffle).run hI2
  obtain ⟨hfr3, hqov3, hvv3, -, -, -, hst3⟩ := hI3
  -- `tp.v := tp.v + 1`
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setVar "tp.v" (k + 1) := ⟨_, rfl⟩
  have r4 : Run B (.assign "tp.v" (.add (.var "tp.v") (.lit 1))) σ3 σ4 4 := by
    rw [hσ4]
    exact run_assign'' (evB_add' (evB_var' hvv3 (by omega)) (evB_lit' (by omega))
      (by omega)) (by simp)
  have h4a : σ4.arrs = σ3.arrs := by rw [hσ4]; simp
  have h4v : σ4.vars "tp.v" = k + 1 := by rw [hσ4]; simp
  have h4nN : σ4.vars nN = σ3.vars nN := by rw [hσ4]; simp [hnv]
  refine ⟨σ4, 3 + (5 + ((22 * (off (k + 1) - off k) + 4) + 4)),
    r1.seq (r2.seq (hr3.seq r4)), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hfr3.of_eq h4nN (by rw [h4a]) (by rw [h4a]) (by rw [h4a]) (by rw [h4a])
      (by rw [h4a])
  · intro i hi; rw [h4a]; exact hqov3 i hi
  · rw [h4v]; omega
  · rw [h4v]
    rw [hj3] at hst3
    exact hst3.of_eq (by rw [h4a]) (by rw [h4a])
  · rw [h4v, hk]
  · rw [hk]; omega

/-- **The scatter's outer scan**: one turn a head, `20` a head and `22`
a slot. -/
private theorem tpScat_scan {B : ℕ} {nN o t qo qt dg : String} {n : ℕ}
    {D : Orientation n} {ns : ℕ} {off tgt : ℕ → ℕ}
    (hnm : TpNames o t qo qt dg) (hnN : nN ∉ tpScalars)
    (hB : n + arcCount D < B) (hns : ns = arcCount D) :
    Spec B (fun σ => TpScOInv nN o t qo qt dg D ns off tgt σ ∧ σ.vars "tp.v" = 0)
      (Csr.scan "tp.v" nN (tpScatOut o t qt dg))
      (fun _ σ' => TpScOInv nN o t qo qt dg D ns off tgt σ' ∧ σ'.vars "tp.v" = n)
      (20 * n + 22 * ns + 4) := by
  refine (Spec.while_potential (b := .lt (.var "tp.v") (.var nN))
    (fun σ => TpScOInv nN o t qo qt dg D ns off tgt σ)
    (fun σ => 20 * (n - σ.vars "tp.v") + 22 * (ns - off (σ.vars "tp.v")))
    (fun σ hO => evalB_condLt_vars (by have := hO.2.2.1; omega)
      (by have := hO.1.carrier; omega)) ?_ (fun σ h => h.1) ?_).post ?_
  · intro σ hO hc
    have hlt : σ.vars "tp.v" < n := by
      have h1 := lt_of_condLt_true hc
      have h2 := hO.1.carrier
      omega
    obtain ⟨σ', K', hrun, hO', hv', hK'⟩ := tpScatOut_step hnm hnN hB hns hO hlt
    refine ⟨σ', K', hrun, hO', ?_⟩
    have hcsr := hO.1.csr
    have hmono : off (σ.vars "tp.v") ≤ off (σ.vars "tp.v" + 1) :=
      hcsr.mono (σ.vars "tp.v" + 1) hlt (σ.vars "tp.v") (by omega)
    have hle : off (σ.vars "tp.v" + 1) ≤ ns := hcsr.off_le_ns hlt
    simp only [size_condLt, size_var]
    rw [hv']
    omega
  · intro σ h
    have hz := h.2
    have h0 : off 0 = 0 := h.1.1.csr.zero
    simp only [size_condLt, size_var]
    rw [hz, h0]
    omega
  · rintro σ σ' - ⟨hO', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hO'.1.carrier
    have h3 := hO'.2.2.1
    exact ⟨hO', by omega⟩

/-- **The scatter, discharged**: from the row starts in `dg` and the
offsets in `qo`, the whole transpose. -/
theorem tpScat_spec {B : ℕ} {nN o t qo qt dg : String} {n : ℕ} {D : Orientation n}
    {ns : ℕ} {off tgt : ℕ → ℕ} (hnm : TpNames o t qo qt dg) (hnN : nN ∉ tpScalars)
    (hB : n + arcCount D < B) (hns : ns = arcCount D) :
    Spec B (fun σ => TpFrame nN o t qo qt dg D ns off tgt σ ∧
        (∀ i, i ≤ n → (σ.arrs qo).getD i 0 = outOff D i) ∧
        (∀ i, i < n → (σ.arrs dg).getD i 0 = outOff D i))
      (tpScatCom nN o t qt dg)
      (fun _ σ' => TpFrame nN o t qo qt dg D ns off tgt σ' ∧
        (∀ i, i ≤ n → (σ'.arrs qo).getD i 0 = outOff D i) ∧
        TpScatSt qt dg D off tgt ns σ')
      (20 * n + 22 * ns + 7) := by
  classical
  obtain ⟨-, -, -, -, -, -, hnv, -, -, -⟩ := tpScalars_ne hnN
  have hstart : Spec B
      (fun σ => TpFrame nN o t qo qt dg D ns off tgt σ ∧
        (∀ i, i ≤ n → (σ.arrs qo).getD i 0 = outOff D i) ∧
        (∀ i, i < n → (σ.arrs dg).getD i 0 = outOff D i))
      (.assign "tp.v" (.lit 0))
      (fun _ σ' => TpScOInv nN o t qo qt dg D ns off tgt σ' ∧ σ'.vars "tp.v" = 0) 2 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hfr, hqov, hdgv⟩ := hσ
    have r1 : Run B (.assign "tp.v" (.lit 0)) σ (σ.setVar "tp.v" 0) 2 :=
      run_assign'' (evB_lit' (by omega)) (by simp)
    have hva : (σ.setVar "tp.v" 0).arrs = σ.arrs := by simp
    refine ⟨_, 2, r1, le_rfl, ⟨?_, ?_, ?_, ?_⟩, by simp⟩
    · exact hfr.of_eq (by simp [hnv]) (by simp) (by simp) (by simp) (by simp) (by simp)
    · intro i hi; rw [hva]; exact hqov i hi
    · simp
    · have hv0 : (σ.setVar "tp.v" 0).vars "tp.v" = 0 := by simp
      rw [hv0, hfr.csr.zero]
      refine ⟨fun u => ?_, fun u q hq1 hq2 => ?_⟩
      · rw [hva, tpCnt_zero]
        simpa using hdgv (u : ℕ) u.isLt
      · rw [tpCnt_zero] at hq2; omega
  refine ((Spec.seq hstart (tpScat_scan hnm hnN hB hns) (fun σ σ' _ hq => hq)
    (fun σ σ' σ'' _ _ hq => ?_)).mono (by omega))
  obtain ⟨⟨hfr, hqov, -, hst⟩, hend⟩ := hq
  refine ⟨hfr, hqov, ?_⟩
  rw [hend] at hst
  rw [← hfr.csr.last]
  exact hst

/-! ## §6 `TransposeIn`, discharged -/

/-- **Every slot of the transpose has an owner**: the out-degree prefix
sums partition `[0, arcCount D)` into the heads' rows. -/
theorem outOff_owner (D : Orientation n) :
    ∀ m, m ≤ n → ∀ q, q < outOff D m →
      ∃ a : Fin n, outOff D (a : ℕ) ≤ q ∧ q < outOff D ((a : ℕ) + 1) := by
  intro m
  induction m with
  | zero => intro _ q hq; rw [outOff] at hq; simp at hq
  | succ m ih =>
      intro hm q hq
      rcases Nat.lt_or_ge q (outOff D m) with h | h
      · exact ih (by omega) q h
      · exact ⟨⟨m, by omega⟩, h, hq⟩

/-- **The scatter's output is an out-neighbour CSR.**  `sound` and
`inj` are `TpScatSt.fill` read at the extent — the address of a slot
determines the head in it — and `complete` is the counting argument:
row `u` has exactly `|outNbrs D u|` slots, each holding a distinct
out-neighbour, so every out-neighbour is in one. -/
theorem outCsrAt_of_scat {qo qt : String} {n : ℕ} {D : Orientation n}
    {off tgt : ℕ → ℕ} {ns : ℕ} {σ : Env} {dg : String} {o t nN : String}
    (hfr : TpFrame nN o t qo qt dg D ns off tgt σ)
    (hqov : ∀ i, i ≤ n → (σ.arrs qo).getD i 0 = outOff D i)
    (hst : TpScatSt qt dg D off tgt ns σ) :
    OutCsrAt qo qt D (fun q => (σ.arrs qt).getD q 0) σ := by
  classical
  have hrow : ∀ u : Fin n,
      outOff D ((u : ℕ) + 1) = outOff D (u : ℕ) + tpCnt tgt ns (u : ℕ) := by
    intro u
    rw [outOff_succ, tpCnt_ns hfr.csr u]
  have hinj : ∀ (v : Fin n) (p r : ℕ), outOff D (v : ℕ) ≤ p →
      p < outOff D ((v : ℕ) + 1) → outOff D (v : ℕ) ≤ r →
      r < outOff D ((v : ℕ) + 1) →
      (σ.arrs qt).getD p 0 = (σ.arrs qt).getD r 0 → p = r := by
    intro v p r hp1 hp2 hr1 hr2 hpr
    obtain ⟨-, -, hp3⟩ := hst.fill v p hp1 (by rw [← hrow]; exact hp2)
    obtain ⟨-, -, hr3⟩ := hst.fill v r hr1 (by rw [← hrow]; exact hr2)
    rw [hpr] at hp3
    omega
  refine
    { qoLen := hfr.qoLen
      qtLen := hfr.qtLen
      qoGet := ?_
      qtGet := ?_
      qtLt := ?_
      sound := ?_
      complete := ?_
      inj := hinj }
  · intro i hi
    have hlen := hfr.qoLen
    rw [getElem?_of_lt' _ _ (by omega), hqov i hi]
  · intro p hp
    have hlen := hfr.qtLen
    exact getElem?_of_lt' _ _ (by omega)
  · intro p hp
    have hp' : p < outOff D n := by rw [outOff_last]; exact hp
    obtain ⟨a, ha1, ha2⟩ := outOff_owner D n le_rfl p hp'
    exact (hst.fill a p ha1 (by rw [← hrow]; exact ha2)).1
  · intro v p hp1 hp2 h
    obtain ⟨hlt, hmem, -⟩ := hst.fill v p hp1 (by rw [← hrow]; exact hp2)
    have : (⟨(σ.arrs qt).getD p 0, hlt⟩ : Fin n) = ⟨(σ.arrs qt).getD p 0, h⟩ := rfl
    rw [← this]
    exact mem_outNbrs.2 hmem
  · intro v u hu
    have hcard : (outNbrs D v).card
        ≤ (Finset.Ico (outOff D (v : ℕ)) (outOff D ((v : ℕ) + 1))).card := by
      rw [Nat.card_Ico, hrow v, tpCnt_ns hfr.csr v, outDegAt_coe]
      omega
    have hmaps : ∀ (q : ℕ) (hq : q ∈ Finset.Ico (outOff D (v : ℕ))
        (outOff D ((v : ℕ) + 1))), (fun (q : ℕ)
          (hq : q ∈ Finset.Ico (outOff D (v : ℕ)) (outOff D ((v : ℕ) + 1))) =>
            (⟨(σ.arrs qt).getD q 0,
              (hst.fill v q (Finset.mem_Ico.1 hq).1
                (by rw [← hrow]; exact (Finset.mem_Ico.1 hq).2)).1⟩ : Fin n)) q hq
          ∈ outNbrs D v := by
      intro q hq
      exact mem_outNbrs.2
        (hst.fill v q (Finset.mem_Ico.1 hq).1
          (by rw [← hrow]; exact (Finset.mem_Ico.1 hq).2)).2.1
    have hinj' : ∀ (q r : ℕ) (hq : q ∈ Finset.Ico (outOff D (v : ℕ))
        (outOff D ((v : ℕ) + 1))) (hr : r ∈ Finset.Ico (outOff D (v : ℕ))
        (outOff D ((v : ℕ) + 1))),
        (⟨(σ.arrs qt).getD q 0,
          (hst.fill v q (Finset.mem_Ico.1 hq).1
            (by rw [← hrow]; exact (Finset.mem_Ico.1 hq).2)).1⟩ : Fin n)
        = (⟨(σ.arrs qt).getD r 0,
          (hst.fill v r (Finset.mem_Ico.1 hr).1
            (by rw [← hrow]; exact (Finset.mem_Ico.1 hr).2)).1⟩ : Fin n) → q = r := by
      intro q r hq hr heq
      have := congrArg Fin.val heq
      exact hinj v q r (Finset.mem_Ico.1 hq).1 (Finset.mem_Ico.1 hq).2
        (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2 this
    obtain ⟨q, hq, hqeq⟩ :=
      Finset.surj_on_of_inj_on_of_card_le
        (s := Finset.Ico (outOff D (v : ℕ)) (outOff D ((v : ℕ) + 1)))
        (t := outNbrs D v)
        (fun q hq => (⟨(σ.arrs qt).getD q 0,
          (hst.fill v q (Finset.mem_Ico.1 hq).1
            (by rw [← hrow]; exact (Finset.mem_Ico.1 hq).2)).1⟩ : Fin n))
        hmaps (fun a₁ a₂ ha₁ ha₂ h => hinj' a₁ a₂ ha₁ ha₂ h) hcard u hu
    refine ⟨q, (Finset.mem_Ico.1 hq).1, (Finset.mem_Ico.1 hq).2, ?_⟩
    exact (congrArg Fin.val hqeq).symm

/-- **`TransposeIn`, discharged** by `tpCom` at
`tpK n a = 41·n + 40·a + 30`: three sweeps, `O(n + arcCount D)`, and
no cell but `nN` (Finding 1). -/
theorem transposeIn_tpCom {B : ℕ} {nN o t qo qt dg : String}
    (hnm : TpNames o t qo qt dg) (hnN : nN ∉ tpScalars) :
    TransposeIn B nN o t qo qt dg (tpCom nN o t qo qt dg) tpK := by
  intro n D ns off tgt
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcsr, hcar, hB, hqoL, hqtL, hdgL, hdg0⟩ := hσ
  have hns : ns = arcCount D := hcsr.ns_eq_arcCount
  have hfr : TpFrame nN o t qo qt dg D ns off tgt σ :=
    { csr := hcsr, carrier := hcar, qoLen := hqoL, qtLen := hqtL, dgLen := hdgL }
  have hall : Spec B
      (fun σ => TpFrame nN o t qo qt dg D ns off tgt σ ∧
        (∀ i, i < n → (σ.arrs dg).getD i 0 = 0))
      (tpCom nN o t qo qt dg)
      (fun _ σ' => TpFrame nN o t qo qt dg D ns off tgt σ' ∧
        (∀ i, i ≤ n → (σ'.arrs qo).getD i 0 = outOff D i) ∧
        TpScatSt qt dg D off tgt ns σ')
      ((17 * ns + 10) + ((21 * n + 12) + (20 * n + 22 * ns + 7))) :=
    Spec.seq (tpCnt_spec hnm hnN hB hns)
      (Spec.seq (tpOff_spec hnm hnN hB) (tpScat_spec hnm hnN hB hns)
        (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq))
      (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq)
  obtain ⟨σ', hrun, hfr', hqov', hst'⟩ := hall.run ⟨hfr, hdg0⟩
  refine ⟨σ', _, hrun, ?_, hfr'.csr, ⟨_, outCsrAt_of_scat hfr' hqov' hst'⟩⟩
  simp only [tpK]
  omega

/-- **The transpose fits inside the round body's own budget**, with room
to spare.  `SolveAugEmit` priced a greedy round at
`emK n a f T = 300·n + 300·a + 200·f + 240·T + 80`; `tpCom` spends `41`
a vertex and `40` an arc of it, so `259·n + 260·a + 200·f + 240·T + 50`
is left for the adjacency stamping, the old-arc copy and the two
candidate phases — which is the accounting `emK`'s docstring gives them
(`300·a` is five arc-length passes, of which the transpose's count and
scatter are two). -/
theorem tpK_le_emK {n : ℕ} (D : Orientation n) (f T : ℕ) :
    tpK n (arcCount D) ≤ emK n (arcCount D) f T := by
  simp only [tpK, emK]
  omega

/-! ## §7 The axiom surface -/

#print axioms tpCnt_off
#print axioms tpCnt_ns
#print axioms tpCnt_eq_of_row
#print axioms outCsrAt_of_scat
#print axioms transposeIn_tpCom
#print axioms tpK_le_emK

end Lax3Proofs.Prog
