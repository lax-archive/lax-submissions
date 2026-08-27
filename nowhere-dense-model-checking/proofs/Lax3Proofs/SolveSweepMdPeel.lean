import Lax3Proofs.SolveSweepOrder

/-!
# F6c12 (wave w60/w61) — `CovMdPeelIn`: the machine min-degree peel

`SolveSweepOrder` names the peel pass of the machine ordering routine:
from the augmented graph's deletable adjacency region
(`DelAdjSt … (mdChain A.G R).toGraph ∅`), repeatedly pick the
minimum-degree live vertex at the pinned smallest-index tie-break,
write its rank counting down from `A.N - 1`, delete it — leaving
`RankArr (ra j) (mdPerm (mdChain A.G R).toGraph)`. This file
discharges that residual with a concrete program and budget.

## The route (supervisor-pinned): a lazy binary heap

An array-based binary min-heap of entries keyed `deg * N + index` —
one cell per entry, the lexicographic (degree, index) order becoming
the numeric order of the key since every index is `< N`. Every vertex
is pushed once at its initial degree; every degree decrement pushes a
*fresh* entry; nothing in the heap is ever updated in place. The pop
loop discards *stale* entries — those whose recorded degree differs
from the current `dg` cell — and the first valid top is exactly
`minDegVert` of the current peeled graph.

The entry invariant that makes the staleness test complete
(no separate deleted-marker is needed):

* every **live** vertex has **exactly one** entry at exactly its
  current degree (`hwit`), and all its entries are at degrees `≥` the
  current one (`hlow`) — degrees only decrease, entries record the
  degree at push time;
* every entry of a **deleted** vertex records a degree `≥ 1`, while
  its `dg` cell is `0` — so the test `dg[k % N] = k / N` fails on it.
  (The entry at the deletion-time degree is consumed by the pop that
  deletes the vertex; earlier entries record strictly larger degrees.)

Hence among all entries, keys below the live minimum's key all fail
the test, and the first key that passes decodes to `minDegVert`.

## Deletion without mates: lazy rows

The peel never compacts a row and never touches `mt`: deleting `v`
scans `v`'s **base** CSR row `[ao[v], ao[v+1])` and, for each target
`w` with `0 < dg[w]`, decrements `dg[w]` and pushes the fresh entry.
Within the row of a live `v` that test is exact — a live neighbour of
a live vertex has positive current degree, and a deleted one has a
zero cell — so `aj` and `mt` are read-only (`mt` entirely unused) and
the region's mate surgery is never performed. The rows of deleted
vertices are simply never trusted again: the scan of a later victim
re-tests every target. The total scan cost is the degree sum `nsAug`,
inside the budget's quasi-linear term; a scan is skipped when
`dg[v] = 0`, so its cost is covered by the potential of live cells.
The `DelAdjSt` region is consumed: the postcondition returns only the
rank array, as the residual demands.

## Structure

* **§1 the heap kit** — the region predicate `HeapSt` (size cell,
  readable prefix, parent-form heap property), `heapPushCom` /
  `heapPopCom` and their `Spec`s, parametric in names, with the
  content as the multiset `hMul n f`. Costs are
  `O(log₂ (size + 1) + 1)`, by a logarithmic variant.
* **§2 the parametric peel core** — `mdPeelCom` over arbitrary names
  and an arbitrary graph `F` on `Fin N` read from the named cell;
  `mdPeelCore_spec`: from `DelAdjSt ao aj dg mt F ∅` plus rank-array
  and heap room, the core leaves `ra` holding `mdRank F` on `[0, N)`,
  at budget `KmdPeel N (nsOf F)` — the region is destroyed, `ao`/`aj`
  and every array outside `{dg, ra, hp}` are untouched, and no array
  changes length. Wave w62's augmentation leaf re-runs this core on
  other graphs in scratch regions.
* **§3 the residual** — `covMdPeelIn_mdPeelCom` concludes
  `CovMdPeelIn` verbatim at the canonical scratch names, from
  hypotheses of the F7-suppliable kinds only: `1 ≤ q`, the name
  distinctness of the residual's region parameters, and the sweep
  scratch transport `hSswT`.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.CoverRoutine (mdChain mdPerm mdOrderingRoutine mdRank mdRankAux
  minDegVert minDegVert_mem minDegVert_spec card_nbrsIn_minDegVert
  mdRankAux_of_nonempty mdRank_lt mdPerm_val)
open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)

/-! ## §0 List and environment plumbing -/

section Plumbing

variable {l : List ℕ} {i k v : ℕ}

/-- Reading an in-range cell in the `getElem?` form `evalB` consumes. -/
theorem getElem?_of_lt (h : i < l.length) : l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- Reading back a fresh store. -/
theorem getD_set_self (h : i < l.length) : (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

/-- Reading past a store elsewhere. -/
theorem getD_set_ne (h : k ≠ i) : (l.set i v).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (fun hc => h hc.symm),
    List.getD_eq_getElem?_getD]

/-- No run of any command changes the length of any array: stores are
`List.set`. The frame fact the sweep-scratch transport consumes. -/
theorem _root_.Lax13Proofs.Imp.BigStep.length_arrs {c : Com} {σ σ' : Env} {n : ℕ}
    (h : BigStep c σ σ' n) (b : String) :
    (σ'.arrs b).length = (σ.arrs b).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr ..
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

/-- Every specification also preserves every array's length. -/
theorem _root_.Lax13Proofs.Reasoning.Spec.arrLengths {B : ℕ} {P : Env → Prop}
    {c : Com} {Q : Env → Env → Prop} {K : ℕ} (h : Spec B P c Q K) :
    Spec B P c (fun σ σ' => Q σ σ' ∧
      ∀ b, (σ'.arrs b).length = (σ.arrs b).length) K := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ
  refine ⟨σ', hr, hq, fun b => ?_⟩
  obtain ⟨k, -, hbs⟩ := hr
  exact (hbs.bigStep).length_arrs b

end Plumbing

/-! ## §1 The heap kit

An array-based binary min-heap over one region `hp` with its size in
the scalar `hs`. The content is carried abstractly: a function
`f : ℕ → ℕ` gives the prefix cells, and the multiset `hMul n f` is
what the pushes and pops move. Only the parent-form heap property is
carried — full sortedness is neither needed nor stated. -/

/-- The parent position of `t` (meaningful for `0 < t`). -/
def hPar (t : ℕ) : ℕ := (t - 1) / 2

/-- The content multiset of a heap prefix. -/
def hMul (n : ℕ) (f : ℕ → ℕ) : Multiset ℕ := (Multiset.range n).map f

theorem hMul_card (n : ℕ) (f : ℕ → ℕ) : (hMul n f).card = n := by
  rw [hMul, Multiset.card_map, Multiset.card_range]

theorem mem_hMul {n : ℕ} {f : ℕ → ℕ} {k : ℕ} :
    k ∈ hMul n f ↔ ∃ t, t < n ∧ f t = k := by
  rw [hMul]
  constructor
  · intro h
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp h
    exact ⟨t, Multiset.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact Multiset.mem_map.mpr ⟨t, Multiset.mem_range.mpr ht, rfl⟩

theorem f_mem_hMul {n : ℕ} (f : ℕ → ℕ) {t : ℕ} (ht : t < n) : f t ∈ hMul n f :=
  mem_hMul.mpr ⟨t, ht, rfl⟩

/-- `hMul` only reads the function below `n`. -/
theorem hMul_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ t < n, f t = g t) :
    hMul n f = hMul n g := by
  rw [hMul, hMul]
  exact Multiset.map_congr rfl fun t ht => h t (Multiset.mem_range.mp ht)

/-- Appending one cell at the top index. -/
theorem hMul_succ (n : ℕ) (f : ℕ → ℕ) : hMul (n + 1) f = f n ::ₘ hMul n f := by
  rw [hMul, hMul, Multiset.range_succ, Multiset.map_cons]

open Lax13Proofs.Reasoning.Lib in
/-- Swapping two prefix cells leaves the content multiset alone. -/
theorem hMul_swap {n ti xi : ℕ} (hti : ti < n) (hxi : xi < n) (hne : ti ≠ xi)
    (f : ℕ → ℕ) : hMul n (upd (upd f ti (f xi)) xi (f ti)) = hMul n f := by
  classical
  have hnd : (Multiset.range n).Nodup := Multiset.nodup_range n
  have h1 : Multiset.range n = ti ::ₘ (Multiset.range n).erase ti :=
    (Multiset.cons_erase (Multiset.mem_range.mpr hti)).symm
  have hxi' : xi ∈ (Multiset.range n).erase ti :=
    hnd.mem_erase_iff.mpr ⟨(Ne.symm hne), Multiset.mem_range.mpr hxi⟩
  have h2 : (Multiset.range n).erase ti =
      xi ::ₘ ((Multiset.range n).erase ti).erase xi :=
    (Multiset.cons_erase hxi').symm
  have hR : ∀ s ∈ ((Multiset.range n).erase ti).erase xi, s ≠ ti ∧ s ≠ xi := by
    intro s hs
    have hs1 : s ∈ (Multiset.range n).erase ti := Multiset.mem_of_mem_erase hs
    have hnd1 : ((Multiset.range n).erase ti).Nodup := hnd.erase ti
    exact ⟨(hnd.mem_erase_iff.mp hs1).1, (hnd1.mem_erase_iff.mp hs).1⟩
  set g := upd (upd f ti (f xi)) xi (f ti) with hg
  have hgt : g ti = f xi := by
    rw [hg, upd_apply, if_neg hne, upd_apply, if_pos rfl]
  have hgx : g xi = f ti := by rw [hg, upd_apply, if_pos rfl]
  have hgR : ∀ s ∈ ((Multiset.range n).erase ti).erase xi, g s = f s := by
    intro s hs
    obtain ⟨h1', h2'⟩ := hR s hs
    rw [hg, upd_apply, if_neg h2', upd_apply, if_neg h1']
  rw [hMul, hMul, h1, h2]
  rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons,
    hgt, hgx, Multiset.map_congr rfl hgR, Multiset.cons_swap]

open Lax13Proofs.Reasoning.Lib in
/-- Overwriting the root with the last cell and shrinking removes one
copy of the root's key from the content. -/
theorem hMul_pop {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) :
    hMul (n - 1) (upd f 0 (f (n - 1))) = (hMul n f).erase (f 0) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [hMul, Multiset.range_zero, Multiset.map_zero, hMul_succ, hMul,
      Multiset.range_zero, Multiset.map_zero, Multiset.erase_cons_head]
  · have h0m : (0 : ℕ) ∈ Multiset.range m := Multiset.mem_range.mpr hm
    have hnd : (Multiset.range m).Nodup := Multiset.nodup_range m
    set R := (Multiset.range m).erase 0 with hRdef
    have hdec : Multiset.range m = 0 ::ₘ R := (Multiset.cons_erase h0m).symm
    have hupd0 : upd f 0 (f m) 0 = f m := by rw [upd_apply, if_pos rfl]
    have hR : ∀ s ∈ R, upd f 0 (f m) s = f s := by
      intro s hs
      rw [upd_apply, if_neg (hnd.mem_erase_iff.mp hs).1]
    have hL : hMul m (upd f 0 (f m)) = f m ::ₘ R.map f := by
      rw [hMul, hdec, Multiset.map_cons, hupd0, Multiset.map_congr rfl hR]
    have hRHS : hMul (m + 1) f = f 0 ::ₘ (f m ::ₘ R.map f) := by
      rw [hMul_succ, hMul, hdec, Multiset.map_cons, Multiset.cons_swap]
    rw [hL, hRHS, Multiset.erase_cons_head]

/-- **The heap region**: the size in the cell `hs`, the prefix reading
back `f`, and the parent-form heap property on the prefix. Cells past
the prefix are unconstrained; the allocation's length is only bounded
below. -/
def HeapSt (hp hs : String) (n : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars hs = n ∧ n ≤ (σ.arrs hp).length ∧
    (∀ t, t < n → (σ.arrs hp).getD t 0 = f t) ∧
    (∀ t, 0 < t → t < n → f (hPar t) ≤ f t)

theorem HeapSt.size {hp hs : String} {n : ℕ} {f : ℕ → ℕ} {σ : Env}
    (h : HeapSt hp hs n f σ) : σ.vars hs = n := h.1

theorem HeapSt.len {hp hs : String} {n : ℕ} {f : ℕ → ℕ} {σ : Env}
    (h : HeapSt hp hs n f σ) : n ≤ (σ.arrs hp).length := h.2.1

theorem HeapSt.read {hp hs : String} {n : ℕ} {f : ℕ → ℕ} {σ : Env}
    (h : HeapSt hp hs n f σ) {t : ℕ} (ht : t < n) :
    (σ.arrs hp).getD t 0 = f t := h.2.2.1 t ht

/-- **The root is a minimum**: the parent-form property chains down. -/
theorem HeapSt.root_le {hp hs : String} {n : ℕ} {f : ℕ → ℕ} {σ : Env}
    (h : HeapSt hp hs n f σ) : ∀ t, t < n → f 0 ≤ f t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro htn
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · exact le_rfl
    · have hlt : hPar t < t := by
        rw [hPar]; omega
      exact le_trans (ih (hPar t) hlt (lt_trans hlt htn)) (h.2.2.2 t hpos htn)

theorem HeapSt.root_le_mem {hp hs : String} {n : ℕ} {f : ℕ → ℕ} {σ : Env}
    (h : HeapSt hp hs n f σ) {k : ℕ} (hk : k ∈ hMul n f) : f 0 ≤ k := by
  obtain ⟨t, ht, rfl⟩ := mem_hMul.mp hk
  exact h.root_le t ht

/-- The region transports along agreement on its array and cell. -/
theorem HeapSt.of_eq {hp hs : String} {n : ℕ} {f : ℕ → ℕ} {σ σ' : Env}
    (h : HeapSt hp hs n f σ) (harr : σ'.arrs hp = σ.arrs hp)
    (hv : σ'.vars hs = σ.vars hs) : HeapSt hp hs n f σ' := by
  refine ⟨by rw [hv]; exact h.1, by rw [harr]; exact h.2.1, ?_, h.2.2.2⟩
  intro t ht
  rw [harr]
  exact h.2.2.1 t ht

section HeapOps

open Lax13Proofs.Reasoning.Lib

variable {B : ℕ} (hp hs tv xv yv : String)

/-- Reading a scalar whose value the caller has named. -/
private theorem evB_var {B v : ℕ} {x : String} {σ : Env} (h : σ.vars x = v)
    (hB : v < B) : (Expr.var x).evalB B σ = some v := by
  rw [← h] at hB ⊢
  exact evalB_var hB

/-- Reading an array cell at a known index with a known value. -/
private theorem evB_get {B k v : ℕ} {a : String} {i : Expr} {σ : Env}
    (hi : i.evalB B σ = some k) (hk : k < (σ.arrs a).length)
    (hval : (σ.arrs a).getD k 0 = v) (hB : v < B) :
    (Expr.get a i).evalB B σ = some v :=
  evalB_get hi (by rw [getElem?_of_lt hk, hval]) hB

/-- One turn of the upward sift: compare with the parent, swap or stop
(stopping sets the position to `0`, which fails the loop condition). -/
def heapUpBody : Com :=
  .seq (.assign xv (.div (.sub (.var tv) (.lit 1)) (.lit 2)))
    (.ite (.lt (.get hp (.var tv)) (.get hp (.var xv)))
      (.seq (.assign yv (.get hp (.var tv)))
        (.seq (.store hp (.var tv) (.get hp (.var xv)))
          (.seq (.store hp (.var xv) (.var yv))
            (.assign tv (.var xv)))))
      (.assign tv (.lit 0)))

/-- **Push**: append the key held in `kv` at the top index and sift it
up. -/
def heapPushCom (kv : String) : Com :=
  .seq (.store hp (.var hs) (.var kv))
    (.seq (.assign tv (.var hs))
      (.seq (.assign hs (.add (.var hs) (.lit 1)))
        (.while (.lt (.lit 0) (.var tv)) (heapUpBody hp tv xv yv))))

/-- One turn of the downward sift: find the smaller child, swap or stop
(stopping sets the position to the size, which fails the loop
condition). -/
def heapDownBody : Com :=
  .seq
    (.seq (.assign xv (.add (.mul (.lit 2) (.var tv)) (.lit 1)))
      (.ite (.lt (.add (.mul (.lit 2) (.var tv)) (.lit 2)) (.var hs))
        (.ite (.lt (.get hp (.add (.mul (.lit 2) (.var tv)) (.lit 2)))
            (.get hp (.var xv)))
          (.assign xv (.add (.mul (.lit 2) (.var tv)) (.lit 2)))
          .skip)
        .skip))
    (.ite (.lt (.get hp (.var xv)) (.get hp (.var tv)))
      (.seq (.assign yv (.get hp (.var tv)))
        (.seq (.store hp (.var tv) (.get hp (.var xv)))
          (.seq (.store hp (.var xv) (.var yv))
            (.assign tv (.var xv)))))
      (.assign tv (.var hs)))

/-- **Pop**: overwrite the root with the last cell, shrink, sift down.
The caller reads the root before popping — there is no separate peek
command. -/
def heapPopCom : Com :=
  .seq (.assign hs (.sub (.var hs) (.lit 1)))
    (.seq (.assign yv (.get hp (.var hs)))
      (.seq (.store hp (.lit 0) (.var yv))
        (.seq (.assign tv (.lit 0))
          (.while (.lt (.add (.mul (.lit 2) (.var tv)) (.lit 1)) (.var hs))
            (heapDownBody hp hs tv xv yv)))))

/-- The downward sift's invariant: the array of size `m` is a heap
except possibly at the edges out of position `t`, the edge into `t`
holding and the grandparent compensating below `t`. The content
multiset `M` is already the popped one. -/
private def DownInv (m : ℕ) (M : Multiset ℕ) (σ : Env) : Prop :=
  ∃ t g, σ.vars tv = t ∧ t ≤ m ∧ σ.vars hs = m ∧ m ≤ (σ.arrs hp).length ∧
    (∀ s, s < m → (σ.arrs hp).getD s 0 = g s) ∧
    hMul m g = M ∧ (∀ s, s < m → g s < B) ∧
    (∀ s, 0 < s → s < m → hPar s ≠ t → g (hPar s) ≤ g s) ∧
    (0 < t → t < m → g (hPar t) ≤ g t ∧
      ∀ s, 0 < s → s < m → hPar s = t → g (hPar t) ≤ g s)

/-- Doubling under the logarithm. -/
private theorem log_two_mul_le {a b : ℕ} (ha : 0 < a) (h : 2 * a ≤ b) :
    Nat.log 2 a + 1 ≤ Nat.log 2 b := by
  have h1 : Nat.log 2 (a * 2) = Nat.log 2 a + 1 :=
    Nat.log_mul_base (by omega) (by omega)
  have h2 : Nat.log 2 (a * 2) ≤ Nat.log 2 b := Nat.log_mono_right (by omega)
  omega

/-- The upward sift's invariant: the array is a heap except possibly at
the edge into position `t`, with the grandparent compensating below
`t`. Content, size and bounds ride along. -/
private def UpInv (n k : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ t g, σ.vars tv = t ∧ t < n + 1 ∧
    σ.vars hs = n + 1 ∧ n + 1 ≤ (σ.arrs hp).length ∧
    (∀ s, s < n + 1 → (σ.arrs hp).getD s 0 = g s) ∧
    hMul (n + 1) g = k ::ₘ hMul n f ∧
    (∀ s, s < n + 1 → g s < B) ∧
    (∀ s, 0 < s → s < n + 1 → s ≠ t → g (hPar s) ≤ g s) ∧
    (0 < t → ∀ s, 0 < s → s < n + 1 → hPar s = t → g (hPar t) ≤ g s)

/-- The parent index of a positive position, in the form the program
computes it. -/
private theorem hPar_lt {t : ℕ} (ht : 0 < t) : hPar t < t := by
  rw [hPar]; omega

private theorem log_hPar_lt {t : ℕ} (ht : 0 < t) :
    Nat.log 2 (hPar t + 1) < Nat.log 2 (t + 1) := by
  have h1 : hPar t + 1 = (t + 1) / 2 := by rw [hPar]; omega
  have h3 : 0 < Nat.log 2 (t + 1) := Nat.log_pos (by omega) (by omega)
  rw [h1, Nat.log_div_base]
  omega

/-- Reading the truth of `lit < var`. -/
private theorem lt_of_condLt_lit_var {B m : ℕ} {x : String} {σ : Env}
    (h : (Cond.lt (.lit m) (.var x)).evalB B σ = some true) : m < σ.vars x := by
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

variable (hht : hs ≠ tv) (hhx : hs ≠ xv) (hhy : hs ≠ yv)
variable (htx : tv ≠ xv) (hty : tv ≠ yv) (hxy : xv ≠ yv)

include hht hhx hhy htx hty hxy in
/-- One turn of the upward sift keeps the invariant, drops the
logarithmic variant, and costs at most `24`. -/
private theorem upBody_step {n k : ℕ} {f : ℕ → ℕ} (hnB : 2 * n + 2 < B) :
    Spec B (fun σ => UpInv (B := B) hp hs tv n k f σ ∧
        (Cond.lt (.lit 0) (.var tv)).evalB B σ = some true)
      (heapUpBody hp tv xv yv)
      (fun σ σ' => UpInv (B := B) hp hs tv n k f σ' ∧
        Nat.log 2 (σ'.vars tv + 1) < Nat.log 2 (σ.vars tv + 1)) 24 := by
  refine Spec.of_exists ?_
  rintro σ ⟨⟨t, g, htv, htn, hhsv, hlen, hread, hcont, hgB, hi, hii⟩, hcond⟩
  have htpos : 0 < t := htv ▸ lt_of_condLt_lit_var hcond
  set p := hPar t with hpdef
  have hpt : p < t := hPar_lt htpos
  have hpn : p < n + 1 := lt_trans hpt htn
  have htB : t < B := by omega
  have hpB : p < B := by omega
  have htlen : t < (σ.arrs hp).length := lt_of_lt_of_le htn hlen
  have hplen : p < (σ.arrs hp).length := lt_of_lt_of_le hpn hlen
  -- the parent-position computation
  have hxEval : (Expr.div (.sub (.var tv) (.lit 1)) (.lit 2)).evalB B σ = some p := by
    refine evalB_bin (evalB_bin (evB_var htv htB) (evalB_lit (by omega)) ?_)
      (evalB_lit (by omega)) ?_
    · show t - 1 < B; omega
    · show (t - 1) / 2 < B
      have : (t - 1) / 2 ≤ t := Nat.le_of_lt_succ (by omega)
      omega
  set σ₁ := σ.setVar xv p with hσ₁
  have h1tv : σ₁.vars tv = t := by
    rw [hσ₁, vars_setVar, if_neg htx, htv]
  have h1xv : σ₁.vars xv = p := by rw [hσ₁, vars_setVar, if_pos rfl]
  have h1arr : σ₁.arrs hp = σ.arrs hp := by rw [hσ₁, arrs_setVar]
  -- the two compared cells
  have hgetT : (Expr.get hp (.var tv)).evalB B σ₁ = some (g t) := by
    refine evB_get (evB_var h1tv htB) ?_ ?_ (hgB t htn)
    · rw [h1arr]; exact htlen
    · rw [h1arr]; exact hread t htn
  have hgetX : (Expr.get hp (.var xv)).evalB B σ₁ = some (g p) := by
    refine evB_get (evB_var h1xv hpB) ?_ ?_ (hgB p hpn)
    · rw [h1arr]; exact hplen
    · rw [h1arr]; exact hread p hpn
  by_cases hlt : g t < g p
  · -- swap with the parent and move up
    have hcT : (Cond.lt (.get hp (.var tv)) (.get hp (.var xv))).evalB B σ₁
        = some true := by
      rw [evalB_condLt hgetT hgetX, decide_eq_true hlt]
    set σ₂ := σ₁.setVar yv (g t) with hσ₂
    have h2tv : σ₂.vars tv = t := by rw [hσ₂, vars_setVar, if_neg hty, h1tv]
    have h2xv : σ₂.vars xv = p := by
      rw [hσ₂, vars_setVar, if_neg hxy, h1xv]
    have h2yv : σ₂.vars yv = g t := by rw [hσ₂, vars_setVar, if_pos rfl]
    have h2arr : σ₂.arrs hp = σ.arrs hp := by rw [hσ₂, arrs_setVar, h1arr]
    set σ₃ := σ₂.setArr hp t (g p) with hσ₃
    have h3tv : σ₃.vars tv = t := by rw [hσ₃, vars_setArr, h2tv]
    have h3xv : σ₃.vars xv = p := by rw [hσ₃, vars_setArr, h2xv]
    have h3yv : σ₃.vars yv = g t := by rw [hσ₃, vars_setArr, h2yv]
    have h3arr : σ₃.arrs hp = (σ.arrs hp).set t (g p) := by
      rw [hσ₃, arrs_setArr, if_pos rfl, h2arr]
    have h3len : (σ₃.arrs hp).length = (σ.arrs hp).length := by
      rw [h3arr, List.length_set]
    set σ₄ := σ₃.setArr hp p (g t) with hσ₄
    have h4tv : σ₄.vars tv = t := by rw [hσ₄, vars_setArr, h3tv]
    have h4xv : σ₄.vars xv = p := by rw [hσ₄, vars_setArr, h3xv]
    have h4arr : σ₄.arrs hp = ((σ.arrs hp).set t (g p)).set p (g t) := by
      rw [hσ₄, arrs_setArr, if_pos rfl, h3arr]
    have h4len : (σ₄.arrs hp).length = (σ.arrs hp).length := by
      rw [h4arr, List.length_set, List.length_set]
    set σ₅ := σ₄.setVar tv p with hσ₅
    -- the run
    have hv1i : (Expr.var tv).evalB B σ₂ = some t := evB_var h2tv htB
    have hv1 : (Expr.get hp (.var xv)).evalB B σ₂ = some (g p) := by
      refine evB_get (evB_var h2xv hpB) ?_ ?_ (hgB p hpn)
      · rw [h2arr]; exact hplen
      · rw [h2arr]; exact hread p hpn
    have hr1 : t < (σ₂.arrs hp).length := by rw [h2arr]; exact htlen
    have hv2i : (Expr.var xv).evalB B σ₃ = some p := evB_var h3xv hpB
    have hv2 : (Expr.var yv).evalB B σ₃ = some (g t) := evB_var h3yv (hgB t htn)
    have hr2 : p < (σ₃.arrs hp).length := by rw [h3len]; exact hplen
    have hv3 : (Expr.var xv).evalB B σ₄ = some p := evB_var h4xv hpB
    refine ⟨σ₅, 24,
      (Run.seq (Run.assign hxEval) (Run.ite_true hcT
        (Run.seq (Run.assign hgetT) (Run.seq (Run.store hv1i hv1 hr1)
          (Run.seq (Run.store hv2i hv2 hr2) (Run.assign hv3)))))).mono
        (by simp only [Expr.size, Cond.size]; omega),
      le_rfl, ?_, ?_⟩
    · -- the invariant at the parent, with the swapped cells
      set g' := upd (upd g t (g p)) p (g t) with hg'
      have hg'p : g' p = g t := by rw [hg', upd_apply, if_pos rfl]
      have hg't : g' t = g p := by
        rw [hg', upd_apply, if_neg (Ne.symm hpt.ne), upd_apply, if_pos rfl]
      have hg'o : ∀ s, s ≠ t → s ≠ p → g' s = g s := by
        intro s h1 h2
        rw [hg', upd_apply, if_neg h2, upd_apply, if_neg h1]
      refine ⟨p, g', ?_, hpn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hσ₅, vars_setVar, if_pos rfl]
      · rw [hσ₅, vars_setVar, if_neg hht, hσ₄, vars_setArr, hσ₃, vars_setArr,
          hσ₂, vars_setVar, if_neg hhy, hσ₁, vars_setVar, if_neg hhx]
        exact hhsv
      · rw [hσ₅, arrs_setVar, h4len]; exact hlen
      · -- prefix reads
        intro s hs'
        rw [hσ₅, arrs_setVar, h4arr]
        rcases eq_or_ne s p with rfl | hsp
        · rw [getD_set_self (by rw [List.length_set]; exact hplen), hg'p]
        · rw [getD_set_ne hsp]
          rcases eq_or_ne s t with rfl | hst
          · rw [getD_set_self htlen, hg't]
          · rw [getD_set_ne hst, hread s hs', hg'o s hst hsp]
      · rw [hg', hMul_swap htn hpn hpt.ne' g]
        exact hcont
      · intro s hs'
        rcases eq_or_ne s p with rfl | hsp
        · rw [hg'p]; exact hgB t htn
        · rcases eq_or_ne s t with rfl | hst
          · rw [hg't]; exact hgB p hpn
          · rw [hg'o s hst hsp]; exact hgB s hs'
      · -- (i) at the new position
        intro s hs0 hsn hsp
        have hparp : hPar t = p := hpdef.symm
        rcases eq_or_ne s t with rfl | hst
        · -- the repaired edge `(p, t)`
          rw [hparp, hg'p, hg't]
          exact le_of_lt hlt
        · rcases eq_or_ne (hPar s) p with hsparp | hsparp
          · -- a sibling of `t` under `p`: the swapped-up key only shrank
            have hold := hi s hs0 hsn hst
            rw [hsparp] at hold
            rw [hsparp, hg'p, hg'o s hst hsp]
            exact le_trans (le_of_lt hlt) hold
          · rcases eq_or_ne (hPar s) t with hspart | hspart
            · -- a child of `t`: the grandparent compensation pays
              have hold := hii htpos s hs0 hsn hspart
              rw [hspart, hg't, hg'o s hst hsp]
              exact hold
            · -- an untouched pair
              rw [hg'o _ hspart hsparp, hg'o s hst hsp]
              exact hi s hs0 hsn hst
      · -- (ii) at the new position: the grandparent compensates below `p`
        intro hppos s hs0 hsn hspar
        have hpp := hPar_lt hppos
        have hparpp : hPar p ≠ t := by omega
        have hparpp' : hPar p ≠ p := by omega
        have hip := hi p hppos hpn hpt.ne
        rw [hg'o _ hparpp hparpp']
        rcases eq_or_ne s t with rfl | hst
        · rw [hg't]
          exact hip
        · have hps := hPar_lt hs0
          have hsp' : s ≠ p := by omega
          have hold := hi s hs0 hsn hst
          rw [hspar] at hold
          rw [hg'o s hst hsp']
          exact le_trans hip hold
    · -- the variant drops to the parent
      have h5tv : σ₅.vars tv = p := by rw [hσ₅, vars_setVar, if_pos rfl]
      rw [h5tv, htv, hpdef]
      exact log_hPar_lt htpos
  · -- the parent is no larger: stop, setting the position to `0`
    have hcF : (Cond.lt (.get hp (.var tv)) (.get hp (.var xv))).evalB B σ₁
        = some false := by
      rw [evalB_condLt hgetT hgetX, decide_eq_false hlt]
    have hple : g p ≤ g t := le_of_not_gt hlt
    set σ₂ := σ₁.setVar tv 0 with hσ₂
    refine ⟨σ₂, 14, ?_, by omega, ?_, ?_⟩
    · refine (Run.seq (Run.assign hxEval)
        (Run.ite_false hcF (Run.assign (evalB_lit (by omega))))).mono ?_
      simp only [Expr.size, Cond.size]
      omega
    · refine ⟨0, g, ?_, by omega, ?_, ?_, ?_, hcont, hgB, ?_, ?_⟩
      · rw [hσ₂, vars_setVar, if_pos rfl]
      · rw [hσ₂, vars_setVar, if_neg hht, hσ₁, vars_setVar, if_neg hhx]
        exact hhsv
      · rw [hσ₂, arrs_setVar, h1arr]; exact hlen
      · intro s hs'
        rw [hσ₂, arrs_setVar, h1arr]
        exact hread s hs'
      · intro s hs0 hsn _
        rcases eq_or_ne s t with rfl | hst
        · rw [hpdef.symm]
          exact hple
        · exact hi s hs0 hsn hst
      · intro h0; omega
    · have h2tv : σ₂.vars tv = 0 := by rw [hσ₂, vars_setVar, if_pos rfl]
      have hpos : 0 < Nat.log 2 (t + 1) :=
        Nat.log_pos (by omega) (show 2 ≤ t + 1 by omega)
      have h01 : Nat.log 2 (0 + 1) = 0 := by
        show Nat.log 2 1 = 0
        exact Nat.log_one_right 2
      rw [h2tv, htv, h01]
      exact hpos

include hht hhx hhy htx hty hxy in
/-- One turn of the downward sift keeps the invariant, drops the
logarithmic variant, and costs at most `48`. -/
private theorem downBody_step {m : ℕ} {M : Multiset ℕ} (hmB : 2 * m + 4 < B) :
    Spec B (fun σ => DownInv (B := B) hp hs tv m M σ ∧
        (Cond.lt (.add (.mul (.lit 2) (.var tv)) (.lit 1)) (.var hs)).evalB B σ
          = some true)
      (heapDownBody hp hs tv xv yv)
      (fun σ σ' => DownInv (B := B) hp hs tv m M σ' ∧
        (Nat.log 2 (m + 1) - Nat.log 2 (σ'.vars tv + 1))
          < (Nat.log 2 (m + 1) - Nat.log 2 (σ.vars tv + 1))) 48 := by
  refine Spec.of_exists ?_
  rintro σ ⟨⟨t, g, htv, htm, hhsv, hlen, hread, hcont, hgB, hi, hii⟩, hcond⟩
  -- the condition's truth: `2t + 1 < m`
  have htB : t < B := by omega
  have hmB' : m < B := by omega
  have hc1eval : (Expr.add (.mul (.lit 2) (.var tv)) (.lit 1)).evalB B σ
      = some (2 * t + 1) := by
    refine evalB_bin (evalB_bin (evalB_lit (by omega)) (evB_var htv htB) ?_)
      (evalB_lit (by omega)) ?_
    · show 2 * t < B; omega
    · show 2 * t + 1 < B; omega
  have ht1m : 2 * t + 1 < m := by
    have h2 := evalB_condLt hc1eval (evB_var hhsv hmB')
    rw [hcond] at h2
    have h3 := Option.some.inj h2
    exact of_decide_eq_true h3.symm
  have htm' : t < m := by omega
  -- the loop variant is positive
  have hVpos : Nat.log 2 (t + 1) + 1 ≤ Nat.log 2 (m + 1) :=
    log_two_mul_le (by omega) (by omega)
  -- the child-position computation
  have hxEval : (Expr.add (.mul (.lit 2) (.var tv)) (.lit 1)).evalB B σ
      = some (2 * t + 1) := hc1eval
  set σ₁ := σ.setVar xv (2 * t + 1) with hσ₁
  have h1tv : σ₁.vars tv = t := by rw [hσ₁, vars_setVar, if_neg htx, htv]
  have h1hs : σ₁.vars hs = m := by rw [hσ₁, vars_setVar, if_neg hhx, hhsv]
  have h1arr : σ₁.arrs hp = σ.arrs hp := by rw [hσ₁, arrs_setVar]
  have h1xv : σ₁.vars xv = 2 * t + 1 := by rw [hσ₁, vars_setVar, if_pos rfl]
  have h122 : (Expr.add (.mul (.lit 2) (.var tv)) (.lit 2)).evalB B σ₁
      = some (2 * t + 2) := by
    refine evalB_bin (evalB_bin (evalB_lit (by omega)) (evB_var h1tv htB) ?_)
      (evalB_lit (by omega)) ?_
    · show 2 * t < B; omega
    · show 2 * t + 2 < B; omega
  -- the choice of the smaller child, uniformly
  obtain ⟨σ₂, K₁, hrun₁₂, hK₁, h2tv, h2hs, h2arr, x, h2xv, hxlo', hxup',
      hxhi', hxmin1, hxmin2⟩ :
      ∃ σ₂ K₁, Run B (.seq (.assign xv (.add (.mul (.lit 2) (.var tv)) (.lit 1)))
          (.ite (.lt (.add (.mul (.lit 2) (.var tv)) (.lit 2)) (.var hs))
            (.ite (.lt (.get hp (.add (.mul (.lit 2) (.var tv)) (.lit 2)))
                (.get hp (.var xv)))
              (.assign xv (.add (.mul (.lit 2) (.var tv)) (.lit 2)))
              .skip)
            .skip)) σ σ₂ K₁ ∧ K₁ ≤ 30 ∧
        σ₂.vars tv = t ∧ σ₂.vars hs = m ∧ σ₂.arrs hp = σ.arrs hp ∧
        ∃ x, σ₂.vars xv = x ∧ 2 * t + 1 ≤ x ∧ x ≤ 2 * t + 2 ∧ x < m ∧
          g x ≤ g (2 * t + 1) ∧ (2 * t + 2 < m → g x ≤ g (2 * t + 2)) := by
    by_cases h22 : 2 * t + 2 < m
    · have hcT : (Cond.lt (.add (.mul (.lit 2) (.var tv)) (.lit 2))
          (.var hs)).evalB B σ₁ = some true := by
        rw [evalB_condLt h122 (evB_var h1hs hmB'), decide_eq_true h22]
      have hg22 : (Expr.get hp (.add (.mul (.lit 2) (.var tv)) (.lit 2))).evalB
          B σ₁ = some (g (2 * t + 2)) := by
        refine evB_get h122 ?_ ?_ (hgB _ h22)
        · rw [h1arr]; exact lt_of_lt_of_le h22 hlen
        · rw [h1arr]; exact hread _ h22
      have hg21 : (Expr.get hp (.var xv)).evalB B σ₁ = some (g (2 * t + 1)) := by
        refine evB_get (evB_var h1xv (by omega)) ?_ ?_ (hgB _ ht1m)
        · rw [h1arr]; exact lt_of_lt_of_le ht1m hlen
        · rw [h1arr]; exact hread _ ht1m
      by_cases hless : g (2 * t + 2) < g (2 * t + 1)
      · -- the right child is smaller
        have hcT2 : (Cond.lt (.get hp (.add (.mul (.lit 2) (.var tv)) (.lit 2)))
            (.get hp (.var xv))).evalB B σ₁ = some true := by
          rw [evalB_condLt hg22 hg21, decide_eq_true hless]
        refine ⟨σ₁.setVar xv (2 * t + 2), _,
          Run.seq (Run.assign hxEval) (Run.ite_true hcT
            (Run.ite_true hcT2 (Run.assign h122))), ?_, ?_, ?_, ?_,
          2 * t + 2, ?_, by omega, le_rfl, h22, ?_, ?_⟩
        · simp only [Expr.size, Cond.size]; omega
        · rw [vars_setVar, if_neg htx, h1tv]
        · rw [vars_setVar, if_neg hhx, h1hs]
        · rw [arrs_setVar, h1arr]
        · rw [vars_setVar, if_pos rfl]
        · exact le_of_lt hless
        · intro _; exact le_rfl
      · -- the left child stays
        have hcF2 : (Cond.lt (.get hp (.add (.mul (.lit 2) (.var tv)) (.lit 2)))
            (.get hp (.var xv))).evalB B σ₁ = some false := by
          rw [evalB_condLt hg22 hg21, decide_eq_false hless]
        refine ⟨σ₁, _,
          Run.seq (Run.assign hxEval) (Run.ite_true hcT
            (Run.ite_false hcF2 Run.skip)), ?_, h1tv, h1hs, h1arr,
          2 * t + 1, h1xv, le_rfl, by omega, ht1m, le_rfl, ?_⟩
        · simp only [Expr.size, Cond.size]; omega
        · intro _; exact le_of_not_gt hless
    · -- no right child
      have hcF : (Cond.lt (.add (.mul (.lit 2) (.var tv)) (.lit 2))
          (.var hs)).evalB B σ₁ = some false := by
        rw [evalB_condLt h122 (evB_var h1hs hmB'), decide_eq_false h22]
      refine ⟨σ₁, _,
        Run.seq (Run.assign hxEval) (Run.ite_false hcF Run.skip), ?_,
        h1tv, h1hs, h1arr, 2 * t + 1, h1xv, le_rfl, by omega, ht1m, le_rfl, ?_⟩
      · simp only [Expr.size, Cond.size]; omega
      · intro hc; exact absurd hc h22
  have hxB : x < B := by omega
  have hxt : t < x := by omega
  have hparx : hPar x = t := by rw [hPar]; omega
  -- the swap test
  have hgetX : (Expr.get hp (.var xv)).evalB B σ₂ = some (g x) := by
    refine evB_get (evB_var h2xv hxB) ?_ ?_ (hgB _ hxhi')
    · rw [h2arr]; exact lt_of_lt_of_le hxhi' hlen
    · rw [h2arr]; exact hread _ hxhi'
  have hgetT : (Expr.get hp (.var tv)).evalB B σ₂ = some (g t) := by
    refine evB_get (evB_var h2tv htB) ?_ ?_ (hgB _ htm')
    · rw [h2arr]; exact lt_of_lt_of_le htm' hlen
    · rw [h2arr]; exact hread _ htm'
  by_cases hlt : g x < g t
  · -- swap and descend
    have hcT : (Cond.lt (.get hp (.var xv)) (.get hp (.var tv))).evalB B σ₂
        = some true := by
      rw [evalB_condLt hgetX hgetT, decide_eq_true hlt]
    set σ₃ := σ₂.setVar yv (g t) with hσ₃
    have h3tv : σ₃.vars tv = t := by rw [hσ₃, vars_setVar, if_neg hty, h2tv]
    have h3xv : σ₃.vars xv = x := by rw [hσ₃, vars_setVar, if_neg hxy, h2xv]
    have h3yv : σ₃.vars yv = g t := by rw [hσ₃, vars_setVar, if_pos rfl]
    have h3arr : σ₃.arrs hp = σ.arrs hp := by rw [hσ₃, arrs_setVar, h2arr]
    set σ₄ := σ₃.setArr hp t (g x) with hσ₄
    have h4tv : σ₄.vars tv = t := by rw [hσ₄, vars_setArr, h3tv]
    have h4xv : σ₄.vars xv = x := by rw [hσ₄, vars_setArr, h3xv]
    have h4yv : σ₄.vars yv = g t := by rw [hσ₄, vars_setArr, h3yv]
    have h4arr : σ₄.arrs hp = (σ.arrs hp).set t (g x) := by
      rw [hσ₄, arrs_setArr, if_pos rfl, h3arr]
    have h4len : (σ₄.arrs hp).length = (σ.arrs hp).length := by
      rw [h4arr, List.length_set]
    set σ₅ := σ₄.setArr hp x (g t) with hσ₅
    have h5xv : σ₅.vars xv = x := by rw [hσ₅, vars_setArr, h4xv]
    have h5arr : σ₅.arrs hp = ((σ.arrs hp).set t (g x)).set x (g t) := by
      rw [hσ₅, arrs_setArr, if_pos rfl, h4arr]
    set σ₆ := σ₅.setVar tv x with hσ₆
    have hv1i : (Expr.var tv).evalB B σ₃ = some t := evB_var h3tv htB
    have hv1 : (Expr.get hp (.var xv)).evalB B σ₃ = some (g x) := by
      refine evB_get (evB_var h3xv hxB) ?_ ?_ (hgB _ hxhi')
      · rw [h3arr]; exact lt_of_lt_of_le hxhi' hlen
      · rw [h3arr]; exact hread _ hxhi'
    have hr1 : t < (σ₃.arrs hp).length := by
      rw [h3arr]; exact lt_of_lt_of_le htm' hlen
    have hv2i : (Expr.var xv).evalB B σ₄ = some x := evB_var h4xv hxB
    have hv2 : (Expr.var yv).evalB B σ₄ = some (g t) := evB_var h4yv (hgB _ htm')
    have hr2 : x < (σ₄.arrs hp).length := by
      rw [h4len]; exact lt_of_lt_of_le hxhi' hlen
    have hv3 : (Expr.var xv).evalB B σ₅ = some x := evB_var h5xv hxB
    refine ⟨σ₆, _, Run.seq hrun₁₂ (Run.ite_true hcT
        (Run.seq (Run.assign hgetT) (Run.seq (Run.store hv1i hv1 hr1)
          (Run.seq (Run.store hv2i hv2 hr2) (Run.assign hv3))))), ?_, ?_, ?_⟩
    · simp only [Expr.size, Cond.size]
      omega
    · -- the invariant at the child
      set g' := upd (upd g t (g x)) x (g t) with hg'
      have hg'x : g' x = g t := by rw [hg', upd_apply, if_pos rfl]
      have hg't : g' t = g x := by
        rw [hg', upd_apply, if_neg (by omega : t ≠ x), upd_apply, if_pos rfl]
      have hg'o : ∀ s, s ≠ t → s ≠ x → g' s = g s := by
        intro s h1 h2
        rw [hg', upd_apply, if_neg h2, upd_apply, if_neg h1]
      refine ⟨x, g', ?_, le_of_lt hxhi', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hσ₆, vars_setVar, if_pos rfl]
      · rw [hσ₆, vars_setVar, if_neg hht, hσ₅, vars_setArr, hσ₄, vars_setArr,
          hσ₃, vars_setVar, if_neg hhy, h2hs]
      · rw [hσ₆, arrs_setVar, h5arr, List.length_set, List.length_set]
        exact hlen
      · intro s hs'
        rw [hσ₆, arrs_setVar, h5arr]
        rcases eq_or_ne s x with rfl | hsx
        · rw [getD_set_self (by rw [List.length_set]; exact lt_of_lt_of_le hs' hlen),
            hg'x]
        · rw [getD_set_ne hsx]
          rcases eq_or_ne s t with rfl | hst
          · rw [getD_set_self (lt_of_lt_of_le htm' hlen), hg't]
          · rw [getD_set_ne hst, hread s hs', hg'o s hst hsx]
      · rw [hg', hMul_swap htm' hxhi' (by omega : t ≠ x) g]
        exact hcont
      · intro s hs'
        rcases eq_or_ne s x with rfl | hsx
        · rw [hg'x]; exact hgB t htm'
        · rcases eq_or_ne s t with rfl | hst
          · rw [hg't]; exact hgB x hxhi'
          · rw [hg'o s hst hsx]; exact hgB s hs'
      · -- (i) at the child position
        intro s hs0 hsm hsparx
        rcases eq_or_ne s x with rfl | hsx
        · -- the repaired edge `(t, x)`
          rw [hparx, hg't, hg'x]
          exact le_of_lt hlt
        · rcases eq_or_ne s t with rfl | hst
          · -- the edge into the old position: the compensation pays
            have hpart_t : hPar s ≠ s := (hPar_lt hs0).ne
            rw [hg'o _ hpart_t hsparx, hg't]
            exact (hii hs0 htm').2 x (by omega) hxhi' hparx
          · rcases eq_or_ne (hPar s) t with hspart | hspart
            · -- a sibling of `x` under `t`: the smaller child moved up
              have hs12 : s = 2 * t + 1 ∨ s = 2 * t + 2 := by
                rw [hPar] at hspart; omega
              rw [hspart, hg't, hg'o s hst hsx]
              rcases hs12 with rfl | rfl
              · exact hxmin1
              · exact hxmin2 hsm
            · -- an untouched pair
              have hsparnx : hPar s ≠ x := hsparx
              rw [hg'o _ hspart hsparnx, hg'o s hst hsx]
              exact hi s hs0 hsm hspart
      · -- (ii) at the child position
        intro _ hxm
        constructor
        · rw [hparx, hg't, hg'x]
          exact le_of_lt hlt
        · intro s hs0 hsm hspars
          have hps := hPar_lt hs0
          have hsx : s ≠ x := by omega
          have hst : s ≠ t := by omega
          rw [hparx, hg't, hg'o s hst hsx]
          have hold := hi s hs0 hsm (by omega)
          rw [hspars] at hold
          exact hold
    · -- the variant drops
      have h6tv : σ₆.vars tv = x := by rw [hσ₆, vars_setVar, if_pos rfl]
      rw [h6tv, htv]
      have hxlog : Nat.log 2 (t + 1) + 1 ≤ Nat.log 2 (x + 1) :=
        log_two_mul_le (by omega) (by omega)
      have hmlog : Nat.log 2 (x + 1) ≤ Nat.log 2 (m + 1) :=
        Nat.log_mono_right (by omega)
      omega
  · -- no smaller child: the heap is restored, stop
    have hcF : (Cond.lt (.get hp (.var xv)) (.get hp (.var tv))).evalB B σ₂
        = some false := by
      rw [evalB_condLt hgetX hgetT, decide_eq_false hlt]
    have hxle : g t ≤ g x := le_of_not_gt hlt
    set σ₃ := σ₂.setVar tv m with hσ₃
    refine ⟨σ₃, _, Run.seq hrun₁₂ (Run.ite_false hcF
        (Run.assign (evB_var h2hs hmB'))), ?_, ?_, ?_⟩
    · simp only [Expr.size, Cond.size]
      omega
    · refine ⟨m, g, ?_, le_rfl, ?_, ?_, ?_, hcont, hgB, ?_, ?_⟩
      · rw [hσ₃, vars_setVar, if_pos rfl]
      · rw [hσ₃, vars_setVar, if_neg hht, h2hs]
      · rw [hσ₃, arrs_setVar, h2arr]; exact hlen
      · intro s hs'
        rw [hσ₃, arrs_setVar, h2arr]
        exact hread s hs'
      · intro s hs0 hsm _
        rcases eq_or_ne (hPar s) t with hspart | hspart
        · have hs12 : s = 2 * t + 1 ∨ s = 2 * t + 2 := by
            rw [hPar] at hspart; omega
          rw [hspart]
          rcases hs12 with rfl | rfl
          · exact le_trans hxle hxmin1
          · exact le_trans hxle (hxmin2 hsm)
        · exact hi s hs0 hsm hspart
      · intro _ hmm
        exact absurd hmm (lt_irrefl m)
    · have h3tv : σ₃.vars tv = m := by rw [hσ₃, vars_setVar, if_pos rfl]
      rw [h3tv, htv]
      omega

include hht hhx hhy htx hty hxy in
/-- **The push contract**: from a heap of content `hMul n f` with one
free cell and the key `k` in `kv`, leave a heap of content
`k ::ₘ hMul n f`; only `hp` and the four working scalars are touched,
and no array changes length. -/
theorem heapPush_spec {n k : ℕ} {f : ℕ → ℕ} (kv : String)
    (hnB : 2 * n + 2 < B) (hkB : k < B) (hfB : ∀ t < n, f t < B) :
    Spec B (fun σ => HeapSt hp hs n f σ ∧ σ.vars kv = k ∧
        n + 1 ≤ (σ.arrs hp).length)
      (heapPushCom hp hs tv xv yv kv)
      (fun σ σ' => (∃ g, HeapSt hp hs (n + 1) g σ' ∧
          hMul (n + 1) g = k ::ₘ hMul n f) ∧
        (∀ b, b ≠ hp → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ hs → y ≠ tv → y ≠ xv → y ≠ yv → σ'.vars y = σ.vars y) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (28 * Nat.log 2 (n + 1) + 13) := by
  have hcore : Spec B (fun σ => HeapSt hp hs n f σ ∧ σ.vars kv = k ∧
        n + 1 ≤ (σ.arrs hp).length)
      (heapPushCom hp hs tv xv yv kv)
      (fun _ σ' => ∃ g, HeapSt hp hs (n + 1) g σ' ∧
        hMul (n + 1) g = k ::ₘ hMul n f)
      (28 * Nat.log 2 (n + 1) + 13) := by
    refine Spec.of_exists ?_
    rintro σ ⟨hH, hkv, hlen1⟩
    obtain ⟨hsize, hlen0, hreads, hprop⟩ := hH
    have hnB' : n < B := by omega
    have hstoreEv : (Expr.var kv).evalB B σ = some k := evB_var hkv hkB
    have hhsEv : (Expr.var hs).evalB B σ = some n := evB_var hsize hnB'
    have hrange : n < (σ.arrs hp).length := by omega
    set σ₁ := σ.setArr hp n k with hσ₁
    have h1hs : σ₁.vars hs = n := by rw [hσ₁, vars_setArr, hsize]
    have h1arr : σ₁.arrs hp = (σ.arrs hp).set n k := by
      rw [hσ₁, arrs_setArr, if_pos rfl]
    set σ₂ := σ₁.setVar tv n with hσ₂
    have h2hs : σ₂.vars hs = n := by rw [hσ₂, vars_setVar, if_neg hht, h1hs]
    set σ₃ := σ₂.setVar hs (n + 1) with hσ₃
    have h3tv : σ₃.vars tv = n := by
      rw [hσ₃, vars_setVar, if_neg (Ne.symm hht), hσ₂, vars_setVar, if_pos rfl]
    have h3arr : σ₃.arrs hp = (σ.arrs hp).set n k := by
      rw [hσ₃, arrs_setVar, hσ₂, arrs_setVar, h1arr]
    -- the appended state satisfies the sift invariant at the top index
    set g₀ := upd f n k with hg₀
    have hg₀n : g₀ n = k := by rw [hg₀, upd_apply, if_pos rfl]
    have hg₀o : ∀ s, s ≠ n → g₀ s = f s := by
      intro s h1
      rw [hg₀, upd_apply, if_neg h1]
    have hInv₃ : UpInv (B := B) hp hs tv n k f σ₃ := by
      refine ⟨n, g₀, h3tv, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hσ₃, vars_setVar, if_pos rfl]
      · rw [h3arr, List.length_set]; exact hlen1
      · intro s hs'
        rw [h3arr]
        rcases eq_or_ne s n with rfl | hsn
        · rw [getD_set_self hrange, hg₀n]
        · rw [getD_set_ne hsn, hreads s (by omega), hg₀o s hsn]
      · rw [hMul_succ, hg₀n, hMul_congr (fun s hs' => hg₀o s (by omega))]
      · intro s hs'
        rcases eq_or_ne s n with rfl | hsn
        · rw [hg₀n]; exact hkB
        · rw [hg₀o s hsn]; exact hfB s (by omega)
      · intro s hs0 hsn hst
        have hsn' : s < n := by omega
        have hps : hPar s < s := hPar_lt hs0
        rw [hg₀o s (by omega), hg₀o _ (by omega)]
        exact hprop s hs0 hsn'
      · intro hn0 s hs0 hsn hpars
        rw [hPar] at hpars
        omega
    have hbody := upBody_step hp hs tv xv yv hht hhx hhy htx hty hxy
      (n := n) (k := k) (f := f) hnB
    have hdefU : ∀ τ, UpInv (B := B) hp hs tv n k f τ →
        ∃ v, (Cond.lt (.lit 0) (.var tv)).evalB B τ = some v := by
      rintro τ ⟨t', g', h'tv, h'tn, -⟩
      exact ⟨_, evalB_condLt (evalB_lit (show (0:ℕ) < B by omega))
        (evB_var h'tv (show t' < B by omega))⟩
    have hKU : ∀ τ, τ = σ₃ →
        (1 + (Cond.lt (.lit 0) (.var tv)).size + 24)
            * Nat.log 2 (τ.vars tv + 1) + 1
          + (Cond.lt (.lit 0) (.var tv)).size
        ≤ 28 * Nat.log 2 (n + 1) + 4 := by
      rintro τ rfl
      rw [h3tv]
      simp only [Cond.size, Expr.size]
      omega
    have hwhile := Spec.while_count (B := B) (K := 28 * Nat.log 2 (n + 1) + 4)
      (P := fun τ => τ = σ₃)
      (UpInv (B := B) hp hs tv n k f)
      (fun τ => Nat.log 2 (τ.vars tv + 1)) 24 hdefU hbody
      (fun τ hτ => hτ ▸ hInv₃) hKU
    obtain ⟨σ', hrunW, hI', hcondF⟩ := hwhile.run rfl
    obtain ⟨t', g', h'tv, h'tn, h'hs, h'len, h'read, h'cont, h'gB, h'i, h'ii⟩ :=
      hI'
    have ht'0 : t' = 0 := by
      have h2 := evalB_condLt (B := B)
        (evalB_lit (show (0:ℕ) < B by omega))
        (evB_var h'tv (show t' < B by omega))
      rw [hcondF] at h2
      have h4 := of_decide_eq_false (Option.some.inj h2).symm
      omega
    have hev2 : (Expr.var hs).evalB B σ₁ = some n := evB_var h1hs hnB'
    have hev3 : (Expr.add (.var hs) (.lit 1)).evalB B σ₂ = some (n + 1) :=
      evalB_bin (evB_var h2hs hnB') (evalB_lit (by omega))
        (show n + 1 < B by omega)
    refine ⟨σ', _, Run.seq (Run.store hhsEv hstoreEv hrange)
      (Run.seq (Run.assign hev2) (Run.seq (Run.assign hev3) hrunW)), ?_,
      g', ⟨h'hs, h'len, h'read, ?_⟩, h'cont⟩
    · simp only [Expr.size]
      omega
    · intro s hs0 hsn
      exact h'i s hs0 hsn (by omega)
  have h2 := (hcore.arrLengths).frame
  refine h2.post ?_
  rintro σ σ' - ⟨⟨hq, hlens⟩, hfv, hfa, -, -⟩
  refine ⟨hq, ?_, ?_, hlens⟩
  · intro b hb
    refine hfa b ?_
    simp [heapPushCom, heapUpBody, Com.warrs, hb]
  · intro y h1 h2 h3 h4
    refine hfv y ?_
    simp [heapPushCom, heapUpBody, Com.wvars, h1, h2, h3, h4]

include hht hhx hhy htx hty hxy in
/-- **The pop contract**: from a nonempty heap of content `hMul n f`,
remove one copy of the root's key `f 0` — a minimum of the content, by
`HeapSt.root_le_mem` — leaving a heap of the erased content; only `hp`
and the four working scalars are touched, and no array changes
length. -/
theorem heapPop_spec {n : ℕ} {f : ℕ → ℕ}
    (hnB : 2 * n + 2 < B) (hn : 0 < n) (hfB : ∀ t < n, f t < B) :
    Spec B (fun σ => HeapSt hp hs n f σ)
      (heapPopCom hp hs tv xv yv)
      (fun σ σ' => (∃ g, HeapSt hp hs (n - 1) g σ' ∧
          hMul (n - 1) g = (hMul n f).erase (f 0)) ∧
        (∀ b, b ≠ hp → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ hs → y ≠ tv → y ≠ xv → y ≠ yv → σ'.vars y = σ.vars y) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (56 * Nat.log 2 (n + 1) + 20) := by
  have hcore : Spec B (fun σ => HeapSt hp hs n f σ)
      (heapPopCom hp hs tv xv yv)
      (fun _ σ' => ∃ g, HeapSt hp hs (n - 1) g σ' ∧
        hMul (n - 1) g = (hMul n f).erase (f 0))
      (56 * Nat.log 2 (n + 1) + 20) := by
    refine Spec.of_exists ?_
    rintro σ ⟨hsize, hlen0, hreads, hprop⟩
    have hnB' : n < B := by omega
    set m := n - 1 with hm
    -- the prefix: shrink, fetch the last cell, overwrite the root
    have hev1 : (Expr.sub (.var hs) (.lit 1)).evalB B σ = some m :=
      evalB_bin (evB_var hsize hnB') (evalB_lit (by omega))
        (show n - 1 < B by omega)
    set σ₁ := σ.setVar hs m with hσ₁
    have h1hs : σ₁.vars hs = m := by rw [hσ₁, vars_setVar, if_pos rfl]
    have h1arr : σ₁.arrs hp = σ.arrs hp := by rw [hσ₁, arrs_setVar]
    have hev2 : (Expr.get hp (.var hs)).evalB B σ₁ = some (f m) := by
      refine evB_get (evB_var h1hs (by omega)) ?_ ?_ (hfB m (by omega))
      · rw [h1arr]; omega
      · rw [h1arr]; exact hreads m (by omega)
    set σ₂ := σ₁.setVar yv (f m) with hσ₂
    have h2yv : σ₂.vars yv = f m := by rw [hσ₂, vars_setVar, if_pos rfl]
    have h2hs : σ₂.vars hs = m := by
      rw [hσ₂, vars_setVar, if_neg hhy, h1hs]
    have h2arr : σ₂.arrs hp = σ.arrs hp := by rw [hσ₂, arrs_setVar, h1arr]
    have hev3i : (Expr.lit 0).evalB B σ₂ = some 0 := evalB_lit (by omega)
    have hev3 : (Expr.var yv).evalB B σ₂ = some (f m) :=
      evB_var h2yv (hfB m (by omega))
    have hr3 : 0 < (σ₂.arrs hp).length := by rw [h2arr]; omega
    set σ₃ := σ₂.setArr hp 0 (f m) with hσ₃
    have h3arr : σ₃.arrs hp = (σ.arrs hp).set 0 (f m) := by
      rw [hσ₃, arrs_setArr, if_pos rfl, h2arr]
    set σ₄ := σ₃.setVar tv 0 with hσ₄
    set g₀ := upd f 0 (f m) with hg₀
    have hg₀0 : g₀ 0 = f m := by rw [hg₀, upd_apply, if_pos rfl]
    have hg₀o : ∀ s, s ≠ 0 → g₀ s = f s := by
      intro s h1
      rw [hg₀, upd_apply, if_neg h1]
    have hInv₄ : DownInv (B := B) hp hs tv m ((hMul n f).erase (f 0)) σ₄ := by
      refine ⟨0, g₀, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hσ₄, vars_setVar, if_pos rfl]
      · rw [hσ₄, vars_setVar, if_neg hht, hσ₃, vars_setArr, h2hs]
      · rw [hσ₄, arrs_setVar, h3arr, List.length_set]; omega
      · intro s hs'
        rw [hσ₄, arrs_setVar, h3arr]
        rcases eq_or_ne s 0 with rfl | hs0
        · rw [getD_set_self (by omega), hg₀0]
        · rw [getD_set_ne hs0, hreads s (by omega), hg₀o s hs0]
      · rw [hg₀, hm]
        exact hMul_pop hn f
      · intro s hs'
        rcases eq_or_ne s 0 with rfl | hs0
        · rw [hg₀0]; exact hfB m (by omega)
        · rw [hg₀o s hs0]; exact hfB s (by omega)
      · intro s hs0 hsm hpars
        have hps : hPar s < s := hPar_lt hs0
        rw [hg₀o s (by omega), hg₀o _ hpars]
        exact hprop s hs0 (by omega)
      · intro h0
        exact absurd h0 (lt_irrefl 0)
    have hbody := downBody_step hp hs tv xv yv hht hhx hhy htx hty hxy
      (m := m) (M := (hMul n f).erase (f 0)) (show 2 * m + 4 < B by omega)
    have hdefD : ∀ τ, DownInv (B := B) hp hs tv m ((hMul n f).erase (f 0)) τ →
        ∃ v, (Cond.lt (.add (.mul (.lit 2) (.var tv)) (.lit 1))
          (.var hs)).evalB B τ = some v := by
      rintro τ ⟨t', g', h'tv, h'tm, h'hs, -⟩
      refine ⟨_, evalB_condLt (evalB_bin (evalB_bin (evalB_lit (by omega))
        (evB_var h'tv (by omega)) ?_) (evalB_lit (by omega)) ?_)
        (evB_var h'hs (by omega))⟩
      · show 2 * t' < B; omega
      · show 2 * t' + 1 < B; omega
    have h4tv : σ₄.vars tv = 0 := by rw [hσ₄, vars_setVar, if_pos rfl]
    have hKD : ∀ τ, τ = σ₄ →
        (1 + (Cond.lt (.add (.mul (.lit 2) (.var tv)) (.lit 1))
            (.var hs)).size + 48)
            * (Nat.log 2 (m + 1) - Nat.log 2 (τ.vars tv + 1)) + 1
          + (Cond.lt (.add (.mul (.lit 2) (.var tv)) (.lit 1)) (.var hs)).size
        ≤ 56 * Nat.log 2 (m + 1) + 8 := by
      rintro τ rfl
      rw [h4tv]
      have h01 : Nat.log 2 (0 + 1) = 0 := Nat.log_one_right 2
      rw [h01]
      simp only [Cond.size, Expr.size]
      omega
    have hwhile := Spec.while_count (B := B)
      (K := 56 * Nat.log 2 (m + 1) + 8) (P := fun τ => τ = σ₄)
      (DownInv (B := B) hp hs tv m ((hMul n f).erase (f 0)))
      (fun τ => Nat.log 2 (m + 1) - Nat.log 2 (τ.vars tv + 1)) 48 hdefD hbody
      (fun τ hτ => hτ ▸ hInv₄) hKD
    obtain ⟨σ', hrunW, hI', hcondF⟩ := hwhile.run rfl
    obtain ⟨t', g', h'tv, h'tm, h'hs, h'len, h'read, h'cont, h'gB, h'i, h'ii⟩ :=
      hI'
    have hcEv : (Expr.add (.mul (.lit 2) (.var tv)) (.lit 1)).evalB B σ'
        = some (2 * t' + 1) := by
      refine evalB_bin (evalB_bin (evalB_lit (by omega))
        (evB_var h'tv (by omega)) ?_) (evalB_lit (by omega)) ?_
      · show 2 * t' < B; omega
      · show 2 * t' + 1 < B; omega
    have hstop : ¬ (2 * t' + 1 < m) := by
      have h2 := evalB_condLt hcEv (evB_var h'hs (by omega))
      rw [hcondF] at h2
      exact of_decide_eq_false (Option.some.inj h2).symm
    have hrun₄ := Run.seq (Run.assign hev1) (Run.seq (Run.assign hev2)
      (Run.seq (Run.store hev3i hev3 hr3) (Run.seq (Run.assign
        (evalB_lit (show (0:ℕ) < B by omega))) hrunW)))
    have hlog : Nat.log 2 (m + 1) ≤ Nat.log 2 (n + 1) :=
      Nat.log_mono_right (by omega)
    refine ⟨σ', _, hrun₄, ?_, g', ⟨h'hs, h'len, h'read, ?_⟩, h'cont⟩
    · simp only [Expr.size]
      omega
    · intro s hs0 hsm
      refine h'i s hs0 hsm ?_
      rw [hPar]
      omega
  have h2 := (hcore.arrLengths).frame
  refine h2.post ?_
  rintro σ σ' - ⟨⟨hq, hlens⟩, hfv, hfa, -, -⟩
  refine ⟨hq, ?_, ?_, hlens⟩
  · intro b hb
    refine hfa b ?_
    simp [heapPopCom, heapDownBody, Com.warrs, hb]
  · intro y h1 h2 h3 h4
    refine hfv y ?_
    simp [heapPopCom, heapDownBody, Com.wvars, h1, h2, h3, h4]

end HeapOps

/-! ## §2 The parametric peel core

### §2a The abstract peel sequence and its bridges -/

section PeelAbstract

variable {N : ℕ}

open Classical in
/-- The live sets of the pinned peel: start at the full carrier, erase
the pinned minimum-degree vertex each round. -/
noncomputable def peelLive (F : SimpleGraph (Fin N)) : ℕ → Finset (Fin N)
  | 0 => Finset.univ
  | i + 1 => if h : (peelLive F i).Nonempty
      then (peelLive F i).erase (minDegVert F (peelLive F i) h) else ∅

@[simp] theorem peelLive_zero (F : SimpleGraph (Fin N)) :
    peelLive F 0 = Finset.univ := rfl

theorem peelLive_succ (F : SimpleGraph (Fin N)) {i : ℕ}
    (h : (peelLive F i).Nonempty) :
    peelLive F (i + 1) = (peelLive F i).erase (minDegVert F (peelLive F i) h) := by
  rw [peelLive, dif_pos h]

theorem peelLive_card (F : SimpleGraph (Fin N)) :
    ∀ i, i ≤ N → (peelLive F i).card = N - i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hcard : (peelLive F k).card = N - k := ih (by omega)
      have hne : (peelLive F k).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      rw [peelLive_succ F hne,
        Finset.card_erase_of_mem (minDegVert_mem F _ hne), hcard]
      omega

theorem peelLive_nonempty (F : SimpleGraph (Fin N)) {i : ℕ} (hi : i < N) :
    (peelLive F i).Nonempty := by
  rw [← Finset.card_pos, peelLive_card F i (by omega)]
  omega

/-- On the live set, the stage ranking agrees with the global one. -/
theorem mdRankAux_peelLive (F : SimpleGraph (Fin N)) :
    ∀ i, i ≤ N → ∀ u ∈ peelLive F i,
      mdRankAux F (peelLive F i) u = mdRank F u := by
  intro i
  induction i with
  | zero => intro _ u _; rfl
  | succ k ih =>
      intro hk u hu
      have hne : (peelLive F k).Nonempty := peelLive_nonempty F (by omega)
      rw [peelLive_succ F hne] at hu
      obtain ⟨hune, humem⟩ := Finset.mem_erase.mp hu
      have h2 := mdRankAux_of_nonempty F hne u
      rw [if_neg hune] at h2
      rw [peelLive_succ F hne, ← h2]
      exact ih (by omega) u humem

/-- The pinned pick of round `i` has global rank `N - i - 1`. -/
theorem mdRank_pick (F : SimpleGraph (Fin N)) {i : ℕ} (hi : i < N)
    (hne : (peelLive F i).Nonempty) :
    mdRank F (minDegVert F (peelLive F i) hne) = N - i - 1 := by
  have h1 := mdRankAux_peelLive F i (by omega) _ (minDegVert_mem F _ hne)
  rw [← h1, mdRankAux_of_nonempty F hne, if_pos rfl,
    peelLive_card F i (by omega)]

theorem peelLive_last (F : SimpleGraph (Fin N)) : peelLive F N = ∅ := by
  rw [← Finset.card_eq_zero, peelLive_card F N le_rfl]
  omega

/-- Erasing a vertex from the live set erases it from every live
neighbourhood. -/
theorem nbrsIn_erase (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (v u : Fin N) : nbrsIn F (S.erase v) u = (nbrsIn F S u).erase v := by
  classical
  ext w
  rw [mem_nbrsIn, Finset.mem_erase, Finset.mem_erase, mem_nbrsIn]
  tauto

/-- A live degree is below the carrier size. -/
theorem card_nbrsIn_lt (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (u : Fin N) : (nbrsIn F S u).card < N := by
  classical
  have hsub : nbrsIn F S u ⊆ Finset.univ.erase u := by
    intro w hw
    obtain ⟨-, hadj⟩ := mem_nbrsIn.mp hw
    exact Finset.mem_erase.mpr ⟨F.ne_of_adj hadj, Finset.mem_univ w⟩
  calc (nbrsIn F S u).card ≤ (Finset.univ.erase u).card :=
        Finset.card_le_card hsub
    _ = N - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
          Fintype.card_fin]
    _ < N := by
        have : 0 < N := Fin.pos u
        omega

/-- A live vertex adjacent to a live vertex has positive live degree. -/
theorem card_nbrsIn_pos {F : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {v u : Fin N} (hv : v ∈ S) (hadj : F.Adj v u) :
    0 < (nbrsIn F S u).card :=
  Finset.card_pos.mpr ⟨v, mem_nbrsIn.mpr ⟨hv, hadj⟩⟩

/-- **The pinned choice is the encoded-key minimum**: with keys
`deg * N + index`, the lexicographic (degree, smallest index) choice is
the numeric minimum over the live set. -/
theorem minDegVert_key_le (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hne : S.Nonempty) :
    ∀ u ∈ S, (nbrsIn F S (minDegVert F S hne)).card * N
        + (minDegVert F S hne : ℕ)
      ≤ (nbrsIn F S u).card * N + (u : ℕ) := by
  classical
  intro u hu
  set v := minDegVert F S hne with hv
  have hvN : (v : ℕ) < N := v.isLt
  have hle : (nbrsIn F S v).card ≤ (nbrsIn F S u).card := by
    rw [hv, card_nbrsIn_minDegVert F S hne]
    exact Finset.inf'_le _ hu
  rcases lt_or_eq_of_le hle with hlt | heq
  · have h2 : (nbrsIn F S v).card * N + N ≤ (nbrsIn F S u).card * N := by
      have h3 := Nat.mul_le_mul_right N
        (show (nbrsIn F S v).card + 1 ≤ (nbrsIn F S u).card by omega)
      rwa [Nat.succ_mul] at h3
    omega
  · have humem : u ∈ S.filter fun w => (nbrsIn F S w).card
        = S.inf' hne fun w => (nbrsIn F S w).card := by
      refine Finset.mem_filter.mpr ⟨hu, ?_⟩
      rw [← heq, hv, card_nbrsIn_minDegVert F S hne]
    have hmin : v ≤ u := Finset.min'_le _ u humem
    have : (v : ℕ) ≤ (u : ℕ) := hmin
    rw [← heq]
    omega

/-- The base degree of an index, as a total function. -/
noncomputable def baseDeg (F : SimpleGraph (Fin N)) (t : ℕ) : ℕ :=
  if h : t < N then (F.neighborSet ⟨t, h⟩).ncard else 0

theorem baseDeg_eq (F : SimpleGraph (Fin N)) (u : Fin N) :
    baseDeg F (u : ℕ) = (F.neighborSet u).ncard := by
  rw [baseDeg, dif_pos u.isLt]

/-- The degree sum of the region's base graph — the budget currency of
the peel (`nsAug` at the residual's instance). -/
noncomputable def nsOf (F : SimpleGraph (Fin N)) : ℕ :=
  ∑ t ∈ Finset.range N, baseDeg F t

theorem baseDeg_lt (F : SimpleGraph (Fin N)) {t : ℕ} (ht : t < N) :
    baseDeg F t < N := by
  classical
  rw [baseDeg, dif_pos ht]
  have hsub : (F.neighborSet ⟨t, ht⟩).toFinset
      ⊆ Finset.univ.erase (⟨t, ht⟩ : Fin N) := by
    intro w hw
    rw [Set.mem_toFinset, SimpleGraph.mem_neighborSet] at hw
    exact Finset.mem_erase.mpr ⟨(F.ne_of_adj hw).symm, Finset.mem_univ w⟩
  have h1 : (F.neighborSet ⟨t, ht⟩).ncard
      ≤ (Finset.univ.erase (⟨t, ht⟩ : Fin N)).card := by
    rw [Set.ncard_eq_toFinset_card']
    exact Finset.card_le_card hsub
  have h2 : (Finset.univ.erase (⟨t, ht⟩ : Fin N)).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  omega

theorem nsOf_le (F : SimpleGraph (Fin N)) : nsOf F ≤ N * N := by
  calc nsOf F ≤ ∑ _t ∈ Finset.range N, N :=
        Finset.sum_le_sum fun t ht =>
          le_of_lt (baseDeg_lt F (Finset.mem_range.mp ht))
    _ = N * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The region's offsets are the partial base-degree sums. -/
theorem offF_eq_sum {F : SimpleGraph (Fin N)} {offF : ℕ → ℕ}
    (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1)
      = offF (v : ℕ) + (F.neighborSet v).ncard) :
    ∀ i, i ≤ N → offF i = ∑ t ∈ Finset.range i, baseDeg F t := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ k ih =>
      intro hk
      have hkN : k < N := hk
      rw [hstep ⟨k, hkN⟩, ih (by omega), Finset.sum_range_succ]
      congr 1
      rw [baseDeg, dif_pos hkN]

/-- The live-neighbourhood count at the full carrier is the base
degree. -/
theorem card_nbrsIn_univ (F : SimpleGraph (Fin N)) (u : Fin N) :
    (nbrsIn F Finset.univ u).card = (F.neighborSet u).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext w
  simp only [mem_nbrsIn, Finset.mem_univ, true_and, Finset.mem_coe,
    SimpleGraph.mem_neighborSet]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end PeelAbstract

/-! ### §2b The programs -/

/-- Decode the root: read the key, split it, test the recorded degree
against the current cell, and record the verdict in `zv`. -/
def chkCom (nNm dg hp kv dv vv zv : String) : Com :=
  .seq (.assign kv (.get hp (.lit 0)))
    (.seq (.assign dv (.div (.var kv) (.var nNm)))
      (.seq (.assign vv (.sub (.var kv) (.mul (.var dv) (.var nNm))))
        (.ite (.eq (.get dg (.var vv)) (.var dv))
          (.assign zv (.lit 0)) (.assign zv (.lit 1)))))

/-- One slot of the victim's base row: if the target is live, decrement
its degree and push the fresh entry. -/
def rowBody (nNm aj dg hp hsv tv xv yv kv iv wv : String) : Com :=
  .seq (.assign wv (.get aj (.var iv)))
    (.seq (.ite (.lt (.lit 0) (.get dg (.var wv)))
        (.seq (.assign xv (.sub (.get dg (.var wv)) (.lit 1)))
          (.seq (.store dg (.var wv) (.var xv))
            (.seq (.assign kv (.add (.mul (.var xv) (.var nNm)) (.var wv)))
              (heapPushCom hp hsv tv xv yv kv))))
        .skip)
      (.assign iv (.add (.var iv) (.lit 1))))

/-- One round: discard stale tops, then use the valid top — write its
rank, consume its entry, scan its base row, kill its degree cell. -/
def roundCom (nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv :
    String) : Com :=
  .seq (chkCom nNm dg hp kv dv vv zv)
    (.seq (.while (.eq (.var zv) (.lit 1))
        (.seq (heapPopCom hp hsv tv xv yv) (chkCom nNm dg hp kv dv vv zv)))
      (.seq (.store ra (.var vv) (.sub (.var rc) (.lit 1)))
        (.seq (.assign rc (.sub (.var rc) (.lit 1)))
          (.seq (heapPopCom hp hsv tv xv yv)
            (.seq (.ite (.lt (.lit 0) (.get dg (.var vv)))
                (.seq (.assign iv (.get ao (.var vv)))
                  (.while (.lt (.var iv) (.get ao (.add (.var vv) (.lit 1))))
                    (rowBody nNm aj dg hp hsv tv xv yv kv iv wv)))
                .skip)
              (.store dg (.var vv) (.lit 0)))))))

/-- One initial push: the vertex at the counter, at its base degree. -/
def initBody (nNm dg hp hsv tv xv yv kv iv : String) : Com :=
  .seq (.assign kv (.add (.mul (.get dg (.var iv)) (.var nNm)) (.var iv)))
    (.seq (heapPushCom hp hsv tv xv yv kv)
      (.assign iv (.add (.var iv) (.lit 1))))

/-- **The min-degree peel**: empty the heap, push every vertex at its
base degree, then run the counted rounds. -/
def mdPeelCom (nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv :
    String) : Com :=
  .seq (.assign hsv (.lit 0))
    (.seq (.seq (.assign iv (.lit 0))
        (.while (.lt (.var iv) (.var nNm))
          (initBody nNm dg hp hsv tv xv yv kv iv)))
      (.seq (.assign rc (.var nNm))
        (.while (.lt (.lit 0) (.var rc))
          (roundCom nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv))))

/-- **The peel budget**, in the residual's own currency: quasi-linear
in the carrier plus the degree sum. Constants honest, not
optimized. -/
def KmdPeel (N ns : ℕ) : ℕ :=
  100 * (N + ns) * (Nat.log 2 (N + ns + 1) + 1) + 100 * N + 100

/-! ### §2c The master invariant -/

/-- **The peel state**, between rounds: the frozen offset and row
arrays, the degree cells at the live degrees (zero on the deleted),
the rank cells written below the live set, and the heap holding, for
every live vertex, exactly one entry at exactly its current degree
(`hwit`), every entry decoding to a recorded degree at least the
current one — at least `1` for a deleted vertex (`hlow`) — and the
size account `2·|heap| + Σ dg ≤ 2N + nsOf F` (`hsize`). -/
structure PeelSt {N : ℕ} (F : SimpleGraph (Fin N))
    (nNm ao aj dg ra hp hsv : String) (aoL ajL : List ℕ)
    (live : Finset (Fin N)) (hn : ℕ) (fh : ℕ → ℕ) (σ : Env) : Prop where
  hao : σ.arrs ao = aoL
  haj : σ.arrs aj = ajL
  hnN : σ.vars nNm = N
  hdgL : N ≤ (σ.arrs dg).length
  hraL : N ≤ (σ.arrs ra).length
  hhpL : N * N + N ≤ (σ.arrs hp).length
  hdg : ∀ u : Fin N, (σ.arrs dg).getD (u : ℕ) 0
      = if u ∈ live then (nbrsIn F live u).card else 0
  hra : ∀ u : Fin N, u ∉ live → (σ.arrs ra).getD (u : ℕ) 0 = mdRank F u
  hheap : HeapSt hp hsv hn fh σ
  hwit : ∀ u ∈ live,
      (hMul hn fh).count ((nbrsIn F live u).card * N + (u : ℕ)) = 1
  hlow : ∀ k ∈ hMul hn fh, ∃ (d : ℕ) (u : Fin N), k = d * N + (u : ℕ) ∧
      d < N ∧ (u ∈ live → (nbrsIn F live u).card ≤ d) ∧ (u ∉ live → 1 ≤ d)
  hsize : 2 * hn + (∑ t ∈ Finset.range N, (σ.arrs dg).getD t 0)
      ≤ 2 * N + nsOf F

namespace PeelSt

variable {N : ℕ} {F : SimpleGraph (Fin N)}
variable {nNm ao aj dg ra hp hsv : String} {aoL ajL : List ℕ}
variable {live : Finset (Fin N)} {hn : ℕ} {fh : ℕ → ℕ} {σ : Env}

/-- Every heap key encodes a vertex and a degree below the carrier. -/
theorem key_lt (h : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ)
    {k : ℕ} (hk : k ∈ hMul hn fh) : k < N * N := by
  obtain ⟨d, u, rfl, hdN, -, -⟩ := h.hlow k hk
  have huN : (u : ℕ) < N := u.isLt
  have h1 : d * N + (u : ℕ) < (d + 1) * N := by rw [Nat.succ_mul]; omega
  have h2 : (d + 1) * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  omega

/-- Every heap prefix cell is below the square. -/
theorem fh_lt (h : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ)
    {t : ℕ} (ht : t < hn) : fh t < N * N :=
  h.key_lt (f_mem_hMul fh ht)

/-- The heap is nonempty while anything is live. -/
theorem hn_pos (h : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ)
    (hne : live.Nonempty) : 0 < hn := by
  obtain ⟨u, hu⟩ := hne
  have hcount := h.hwit u hu
  have hmem : ((nbrsIn F live u).card * N + (u : ℕ)) ∈ hMul hn fh := by
    rw [← Multiset.count_pos, hcount]
    omega
  have hcard : 0 < (hMul hn fh).card := by
    rw [Multiset.card_pos]
    intro h0
    rw [h0] at hmem
    exact absurd hmem (Multiset.notMem_zero _)
  rwa [hMul_card] at hcard

/-- A degree cell is below the carrier. -/
theorem dg_lt (h : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ)
    (u : Fin N) : (σ.arrs dg).getD (u : ℕ) 0 < N := by
  rw [h.hdg u]
  split
  · exact card_nbrsIn_lt F live u
  · exact Fin.pos u

/-- The state transports along agreement on what it reads. -/
theorem of_eq (h : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ)
    {σ' : Env} (hao' : σ'.arrs ao = σ.arrs ao)
    (haj' : σ'.arrs aj = σ.arrs aj) (hdg' : σ'.arrs dg = σ.arrs dg)
    (hra' : σ'.arrs ra = σ.arrs ra) (hhp' : σ'.arrs hp = σ.arrs hp)
    (hnN' : σ'.vars nNm = σ.vars nNm) (hhs' : σ'.vars hsv = σ.vars hsv) :
    PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ' where
  hao := by rw [hao', h.hao]
  haj := by rw [haj', h.haj]
  hnN := by rw [hnN', h.hnN]
  hdgL := by rw [hdg']; exact h.hdgL
  hraL := by rw [hra']; exact h.hraL
  hhpL := by rw [hhp']; exact h.hhpL
  hdg := by intro u; rw [hdg']; exact h.hdg u
  hra := by intro u hu; rw [hra']; exact h.hra u hu
  hheap := h.hheap.of_eq hhp' hhs'
  hwit := h.hwit
  hlow := h.hlow
  hsize := by
    have : (∑ t ∈ Finset.range N, (σ'.arrs dg).getD t 0)
        = ∑ t ∈ Finset.range N, (σ.arrs dg).getD t 0 := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hdg']
    rw [this]
    exact h.hsize

end PeelSt

/-! ### Sums over degree cells, and their one-cell updates -/

/-- The degree-cell sum — the `Σ dg` of the size account and the
potential. -/
def dgSum (dg : String) (N : ℕ) (σ : Env) : ℕ :=
  ∑ t ∈ Finset.range N, (σ.arrs dg).getD t 0

/-- The scan potential: the base-row width of every cell still
positive — what pays for the base-row scans of the victims. -/
def scanPot (ao dg : String) (N : ℕ) (σ : Env) : ℕ :=
  ∑ t ∈ Finset.range N, if 0 < (σ.arrs dg).getD t 0
    then (σ.arrs ao).getD (t + 1) 0 - (σ.arrs ao).getD t 0 else 0

/-- Updating one cell of a summed list, additively. -/
theorem sum_getD_set (l : List ℕ) {j : ℕ} (N v : ℕ) (hj : j < N)
    (hjl : j < l.length) :
    (∑ t ∈ Finset.range N, (l.set j v).getD t 0) + l.getD j 0
      = (∑ t ∈ Finset.range N, l.getD t 0) + v := by
  classical
  have hj' : j ∈ Finset.range N := Finset.mem_range.mpr hj
  rw [← Finset.add_sum_erase _ _ hj', ← Finset.add_sum_erase _ (fun t =>
    l.getD t 0) hj']
  have hcong : ∀ t ∈ (Finset.range N).erase j,
      (l.set j v).getD t 0 = l.getD t 0 := fun t ht =>
    getD_set_ne (Finset.mem_erase.mp ht).1
  rw [Finset.sum_congr rfl hcong, getD_set_self hjl]
  omega

/-- Updating one cell under the scan potential, additively: the term
of the touched cell moves, every other term stays. -/
theorem scanPot_set (ao dg : String) {N : ℕ} (σ : Env) {j v : ℕ}
    (hj : j < N) (hjl : j < (σ.arrs dg).length) (hne : ao ≠ dg) :
    scanPot ao dg N (σ.setArr dg j v)
        + (if 0 < (σ.arrs dg).getD j 0
            then (σ.arrs ao).getD (j + 1) 0 - (σ.arrs ao).getD j 0 else 0)
      = scanPot ao dg N σ
        + (if 0 < v
            then (σ.arrs ao).getD (j + 1) 0 - (σ.arrs ao).getD j 0 else 0) := by
  classical
  have hj' : j ∈ Finset.range N := Finset.mem_range.mpr hj
  have hao : (σ.setArr dg j v).arrs ao = σ.arrs ao := by
    rw [arrs_setArr, if_neg hne]
  have hdg : (σ.setArr dg j v).arrs dg = (σ.arrs dg).set j v := by
    rw [arrs_setArr, if_pos rfl]
  rw [scanPot, scanPot, ← Finset.add_sum_erase _ _ hj',
    ← Finset.add_sum_erase _ (fun t => if 0 < (σ.arrs dg).getD t 0
      then (σ.arrs ao).getD (t + 1) 0 - (σ.arrs ao).getD t 0 else 0) hj']
  have hcong : ∀ t ∈ (Finset.range N).erase j,
      (if 0 < ((σ.setArr dg j v).arrs dg).getD t 0
        then ((σ.setArr dg j v).arrs ao).getD (t + 1) 0
          - ((σ.setArr dg j v).arrs ao).getD t 0 else 0)
      = if 0 < (σ.arrs dg).getD t 0
        then (σ.arrs ao).getD (t + 1) 0 - (σ.arrs ao).getD t 0 else 0 := by
    intro t ht
    rw [hao, hdg, getD_set_ne (Finset.mem_erase.mp ht).1]
  rw [Finset.sum_congr rfl hcong, hao, hdg, getD_set_self hjl]
  omega

/-- The scan potential only reads the two arrays. -/
theorem scanPot_congr {ao dg : String} {N : ℕ} {σ σ' : Env}
    (hao : σ'.arrs ao = σ.arrs ao) (hdg : σ'.arrs dg = σ.arrs dg) :
    scanPot ao dg N σ' = scanPot ao dg N σ := by
  rw [scanPot, scanPot]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hao, hdg]

/-- The degree sum only reads its array. -/
theorem dgSum_congr {dg : String} {N : ℕ} {σ σ' : Env}
    (hdg : σ'.arrs dg = σ.arrs dg) : dgSum dg N σ' = dgSum dg N σ := by
  rw [dgSum, dgSum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hdg]

/-- The scan potential is at most the degree-sum currency, in a state
whose cell reads and offset reads are the region's. -/
theorem scanPot_le {ao dg : String} {N : ℕ} {σ : Env} {F : SimpleGraph (Fin N)}
    {offF : ℕ → ℕ}
    (hoffF : ∀ i, i ≤ N → (σ.arrs ao).getD i 0 = offF i)
    (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1)
      = offF (v : ℕ) + (F.neighborSet v).ncard) :
    scanPot ao dg N σ ≤ nsOf F := by
  rw [scanPot, nsOf]
  refine Finset.sum_le_sum fun t ht => ?_
  have htN := Finset.mem_range.mp ht
  split
  · rw [hoffF (t + 1) (by omega), hoffF t (by omega),
      offF_eq_sum h0 hstep (t + 1) (by omega),
      offF_eq_sum h0 hstep t (by omega), Finset.sum_range_succ]
    omega
  · omega

/-- The decode of an encoded key: the recorded degree. -/
theorem key_div {N d u : ℕ} (hN : 0 < N) (hu : u < N) : (d * N + u) / N = d := by
  rw [mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hu]
  omega

/-! ### §2d The chk pass -/

section PeelSteps

variable {B N : ℕ} {F : SimpleGraph (Fin N)}
variable {nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv : String}
variable {aoL ajL : List ℕ}

/-- **The decode-and-test pass**: read the root key, split it, compare
the recorded degree against the current cell, record the verdict.
Scalars only; the peel state rides across. -/
private theorem chk_run
    (hnods : ([nNm, hsv, kv, dv, vv, zv] : List String).Nodup)
    (hB : N * N + 4 * N + 4 ≤ B)
    {live : Finset (Fin N)} {hn : ℕ} {fh : ℕ → ℕ} {σ : Env}
    (hP : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ)
    (hne : live.Nonempty) :
    ∃ σ' K', Run B (chkCom nNm dg hp kv dv vv zv) σ σ' K' ∧ K' ≤ 20 ∧
      PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ' ∧
      (∀ y, y ∉ ([kv, dv, vv, zv] : List String) → σ'.vars y = σ.vars y) ∧
      (∀ b, σ'.arrs b = σ.arrs b) ∧
      ∃ (d₀ : ℕ) (u₀ : Fin N), fh 0 = d₀ * N + (u₀ : ℕ) ∧ d₀ < N ∧
        σ'.vars vv = (u₀ : ℕ) ∧ σ'.vars dv = d₀ ∧
        (σ'.vars zv = 0 ∨ σ'.vars zv = 1) ∧
        (σ'.vars zv = 0 ↔ (σ.arrs dg).getD (u₀ : ℕ) 0 = d₀) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hnods
  obtain ⟨⟨hns, hnk, hnd, hnv, hnz⟩, ⟨hsk, hsd, hsv', hsz⟩,
    ⟨hkd, hkv', hkz⟩, ⟨hdv', hdz⟩, hvz⟩ := hnods
  have hn0 : 0 < hn := hP.hn_pos hne
  have hN0 : 0 < N := by
    obtain ⟨u, -⟩ := hne
    exact Fin.pos u
  have hroot : fh 0 ∈ hMul hn fh := f_mem_hMul fh hn0
  obtain ⟨d₀, u₀, hkey, hd₀N, -, -⟩ := hP.hlow (fh 0) hroot
  have hkB : fh 0 < B := by
    have := hP.key_lt hroot
    omega
  have hdiv : fh 0 / N = d₀ := by rw [hkey]; exact key_div hN0 u₀.isLt
  have hdmul : d₀ * N ≤ fh 0 := by rw [hkey]; omega
  have hu₀N : (u₀ : ℕ) < N := u₀.isLt
  -- the reads and writes, one at a time
  have hev1 : (Expr.get hp (.lit 0)).evalB B σ = some (fh 0) := by
    refine evB_get (evalB_lit (by omega)) ?_ ?_ hkB
    · have := hP.hhpL
      omega
    · exact hP.hheap.read hn0
  set σ₁ := σ.setVar kv (fh 0) with hσ₁
  have h1kv : σ₁.vars kv = fh 0 := by rw [hσ₁, vars_setVar, if_pos rfl]
  have h1nN : σ₁.vars nNm = N := by
    rw [hσ₁, vars_setVar, if_neg hnk, hP.hnN]
  have hev2 : (Expr.div (.var kv) (.var nNm)).evalB B σ₁
      = some (fh 0 / N) := by
    have h := evalB_bin (op := .div) (evB_var h1kv hkB)
      (evB_var h1nN (show N < B by omega))
      (show Bop.div.apply (fh 0) N < B by rw [Bop.apply_div]; omega)
    rwa [Bop.apply_div] at h
  set σ₂ := σ₁.setVar dv (fh 0 / N) with hσ₂
  have h2dv : σ₂.vars dv = d₀ := by
    rw [hσ₂, vars_setVar, if_pos rfl, hdiv]
  have h2kv : σ₂.vars kv = fh 0 := by
    rw [hσ₂, vars_setVar, if_neg hkd, h1kv]
  have h2nN : σ₂.vars nNm = N := by
    rw [hσ₂, vars_setVar, if_neg hnd, h1nN]
  have hmul : (Expr.mul (.var dv) (.var nNm)).evalB B σ₂ = some (d₀ * N) := by
    have h := evalB_bin (op := .mul) (evB_var h2dv (show d₀ < B by omega))
      (evB_var h2nN (show N < B by omega))
      (show Bop.mul.apply d₀ N < B by rw [Bop.apply_mul]; omega)
    rwa [Bop.apply_mul] at h
  have hsubval : fh 0 - d₀ * N = (u₀ : ℕ) := by rw [hkey]; omega
  have hev3 : (Expr.sub (.var kv) (.mul (.var dv) (.var nNm))).evalB B σ₂
      = some (u₀ : ℕ) := by
    have h := evalB_bin (op := .sub) (evB_var h2kv hkB) hmul
      (show Bop.sub.apply (fh 0) (d₀ * N) < B by
        rw [Bop.apply_sub, hsubval]; omega)
    rwa [Bop.apply_sub, hsubval] at h
  set σ₃ := σ₂.setVar vv (u₀ : ℕ) with hσ₃
  have h3vv : σ₃.vars vv = (u₀ : ℕ) := by rw [hσ₃, vars_setVar, if_pos rfl]
  have h3dv : σ₃.vars dv = d₀ := by
    rw [hσ₃, vars_setVar, if_neg hdv', h2dv]
  have h3arr : ∀ b, σ₃.arrs b = σ.arrs b := by
    intro b
    rw [hσ₃, arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setVar]
  have hcellB : (σ.arrs dg).getD (u₀ : ℕ) 0 < B := by
    have := hP.dg_lt u₀
    omega
  have hevT : (Expr.get dg (.var vv)).evalB B σ₃
      = some ((σ.arrs dg).getD (u₀ : ℕ) 0) := by
    refine evB_get (evB_var h3vv (show (u₀ : ℕ) < B by omega)) ?_ ?_ hcellB
    · rw [h3arr]
      have := hP.hdgL
      omega
    · rw [h3arr]
  have hevD : (Expr.var dv).evalB B σ₃ = some d₀ :=
    evB_var h3dv (show d₀ < B by omega)
  -- shared frame facts for the final state, per branch value `z`
  have hframe : ∀ z : ℕ, ∀ y, y ∉ ([kv, dv, vv, zv] : List String) →
      ((σ₃.setVar zv z).vars y = σ.vars y) := by
    intro z y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
    rw [vars_setVar, if_neg hy4, hσ₃, vars_setVar, if_neg hy3, hσ₂,
      vars_setVar, if_neg hy2, hσ₁, vars_setVar, if_neg hy1]
  have harrs : ∀ z : ℕ, ∀ b, ((σ₃.setVar zv z).arrs b = σ.arrs b) := by
    intro z b
    rw [arrs_setVar, h3arr]
  have hPeel : ∀ z : ℕ,
      PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh (σ₃.setVar zv z) := by
    intro z
    refine hP.of_eq (harrs z ao) (harrs z aj) (harrs z dg) (harrs z ra)
      (harrs z hp) ?_ ?_
    · exact hframe z nNm (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hnk, hnd, hnv, hnz⟩)
    · exact hframe z hsv (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hsk, hsd, hsv', hsz⟩)
  by_cases hval : (σ.arrs dg).getD (u₀ : ℕ) 0 = d₀
  · have hcT : (Cond.eq (.get dg (.var vv)) (.var dv)).evalB B σ₃
        = some true := by
      rw [evalB_condEq hevT hevD]
      congr 1
      exact beq_iff_eq.mpr hval
    refine ⟨σ₃.setVar zv 0, 20,
      (Run.seq (Run.assign hev1) (Run.seq (Run.assign hev2)
        (Run.seq (Run.assign hev3) (Run.ite_true hcT
          (Run.assign (evalB_lit (show (0:ℕ) < B by omega))))))).mono
        (by simp only [Expr.size, Cond.size]; omega),
      le_rfl, hPeel 0, hframe 0, harrs 0, d₀, u₀, hkey, hd₀N, ?_, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg hvz, h3vv]
    · rw [vars_setVar, if_neg hdz, h3dv]
    · left
      rw [vars_setVar, if_pos rfl]
    · rw [vars_setVar, if_pos rfl]
      exact ⟨fun _ => hval, fun _ => rfl⟩
  · have hcF : (Cond.eq (.get dg (.var vv)) (.var dv)).evalB B σ₃
        = some false := by
      rw [evalB_condEq hevT hevD]
      congr 1
      exact beq_eq_false_iff_ne.mpr hval
    refine ⟨σ₃.setVar zv 1, 20,
      (Run.seq (Run.assign hev1) (Run.seq (Run.assign hev2)
        (Run.seq (Run.assign hev3) (Run.ite_false hcF
          (Run.assign (evalB_lit (show (1:ℕ) < B by omega))))))).mono
        (by simp only [Expr.size, Cond.size]; omega),
      le_rfl, hPeel 1, hframe 1, harrs 1, d₀, u₀, hkey, hd₀N, ?_, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg hvz, h3vv]
    · rw [vars_setVar, if_neg hdz, h3dv]
    · right
      rw [vars_setVar, if_pos rfl]
    · rw [vars_setVar, if_pos rfl]
      exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h hval⟩

/-- Encoded keys decode uniquely. -/
private theorem key_inj {N d d' u u' : ℕ} (hu : u < N) (hu' : u' < N)
    (h : d * N + u = d' * N + u') : d = d' ∧ u = u' := by
  have hN : 0 < N := by omega
  have h1 : (d * N + u) / N = d := key_div hN hu
  have h2 : (d' * N + u') / N = d' := key_div hN hu'
  have hd : d = d' := by rw [← h1, ← h2, h]
  subst hd
  exact ⟨rfl, by omega⟩

/-- **The first valid top is the pinned choice**: a root key whose
recorded degree matches the current cell decodes to `minDegVert` of
the live set, at its live degree. Below the live minimum every key is
stale; at it, the witness passes. -/
private theorem valid_root
    {live : Finset (Fin N)} {hn : ℕ} {fh : ℕ → ℕ} {σ : Env}
    (hP : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ)
    (hne : live.Nonempty) {d₀ : ℕ} {u₀ : Fin N}
    (hkey : fh 0 = d₀ * N + (u₀ : ℕ))
    (hcell : (σ.arrs dg).getD (u₀ : ℕ) 0 = d₀) :
    u₀ = minDegVert F live hne ∧ d₀ = (nbrsIn F live u₀).card := by
  have hn0 : 0 < hn := hP.hn_pos hne
  -- the decoded vertex is live: a dead one would need both a zero cell
  -- and a recorded degree of at least one
  have hlive : u₀ ∈ live := by
    by_contra hdead
    have h0 : (σ.arrs dg).getD (u₀ : ℕ) 0 = 0 := by
      rw [hP.hdg u₀, if_neg hdead]
    obtain ⟨d₁, u₁, hkey₁, -, -, hdead₁⟩ := hP.hlow (fh 0) (f_mem_hMul fh hn0)
    obtain ⟨hd, hu⟩ := key_inj u₁.isLt u₀.isLt (hkey₁.symm.trans hkey)
    have hu' : u₁ = u₀ := Fin.ext hu
    have h1 : 1 ≤ d₁ := hdead₁ (hu'.symm ▸ hdead)
    omega
  have hdeg : (nbrsIn F live u₀).card = d₀ := by
    rw [← hcell, hP.hdg u₀, if_pos hlive]
  -- the root is at most the witness key of the pinned choice, which is
  -- at most the key of the decoded vertex — a chain closing to equality
  set v := minDegVert F live hne with hv
  have hwmem : (nbrsIn F live v).card * N + (v : ℕ) ∈ hMul hn fh := by
    rw [← Multiset.count_pos, hP.hwit v (minDegVert_mem F live hne)]
    omega
  have hle1 : fh 0 ≤ (nbrsIn F live v).card * N + (v : ℕ) :=
    hP.hheap.root_le_mem hwmem
  have hle2 := minDegVert_key_le F live hne u₀ hlive
  rw [← hv, hdeg] at hle2
  rw [hkey] at hle1
  have heq : (nbrsIn F live v).card * N + (v : ℕ) = d₀ * N + (u₀ : ℕ) := by
    omega
  obtain ⟨-, hu⟩ := key_inj v.isLt u₀.isLt heq
  exact ⟨(Fin.ext hu).symm, hdeg.symm⟩

/-- **The stale-discard loop**: pop while the top's recorded degree
disagrees with its cell. Exits with the top valid, at a cost bounded
by the heap shrinkage — the amortized account the round consumes. -/
private theorem stale_run
    (hchk : ([nNm, hsv, kv, dv, vv, zv] : List String).Nodup)
    (hht : hsv ≠ tv) (hhx : hsv ≠ xv) (hhy : hsv ≠ yv)
    (htx : tv ≠ xv) (hty : tv ≠ yv) (hxy : xv ≠ yv)
    (hnt : nNm ≠ tv) (hnx : nNm ≠ xv) (hny : nNm ≠ yv)
    (haohp : ao ≠ hp) (hajhp : aj ≠ hp) (hdghp : dg ≠ hp) (hrahp : ra ≠ hp)
    (hB : N * N + 4 * N + 4 ≤ B)
    {live : Finset (Fin N)} {hn : ℕ} {fh : ℕ → ℕ} {σ : Env}
    (hP : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn fh σ)
    (hne : live.Nonempty)
    (hpost : ∃ (d₀ : ℕ) (u₀ : Fin N), fh 0 = d₀ * N + (u₀ : ℕ) ∧ d₀ < N ∧
      σ.vars vv = (u₀ : ℕ) ∧ σ.vars dv = d₀ ∧
      (σ.vars zv = 0 ∨ σ.vars zv = 1) ∧
      (σ.vars zv = 0 ↔ (σ.arrs dg).getD (u₀ : ℕ) 0 = d₀)) :
    ∃ σ' K' hn' fh', Run B
        (.while (.eq (.var zv) (.lit 1))
          (.seq (heapPopCom hp hsv tv xv yv) (chkCom nNm dg hp kv dv vv zv)))
        σ σ' K' ∧
      K' + (56 * Nat.log 2 (N + nsOf F + 1) + 44) * hn'
        ≤ (56 * Nat.log 2 (N + nsOf F + 1) + 44) * hn + 4 ∧
      hn' ≤ hn ∧
      PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn' fh' σ' ∧
      (∀ y, y ∉ ([kv, dv, vv, zv, hsv, tv, xv, yv] : List String) →
        σ'.vars y = σ.vars y) ∧
      (∀ b, b ≠ hp → σ'.arrs b = σ.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
      ∃ (d₀ : ℕ) (u₀ : Fin N), fh' 0 = d₀ * N + (u₀ : ℕ) ∧ d₀ < N ∧
        σ'.vars vv = (u₀ : ℕ) ∧ σ'.vars dv = d₀ ∧
        (σ'.arrs dg).getD (u₀ : ℕ) 0 = d₀ := by
  have hchkfacts := hchk
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hchkfacts
  obtain ⟨⟨hns, hnk, hnd, hnv, hnz⟩, ⟨hsk, hsd, hsv', hsz⟩, -, -, -⟩ :=
    hchkfacts
  set L := Nat.log 2 (N + nsOf F + 1) with hL
  set C := 56 * L + 44 with hC
  have hN0 : 0 < N := by
    obtain ⟨u, -⟩ := hne
    exact Fin.pos u
  set I : Env → Prop := fun τ =>
    ∃ hn' fh', PeelSt F nNm ao aj dg ra hp hsv aoL ajL live hn' fh' τ ∧
      hn' ≤ hn ∧
      (∀ y, y ∉ ([kv, dv, vv, zv, hsv, tv, xv, yv] : List String) →
        τ.vars y = σ.vars y) ∧
      (∀ b, b ≠ hp → τ.arrs b = σ.arrs b) ∧
      (∀ b, (τ.arrs b).length = (σ.arrs b).length) ∧
      ∃ (d₀ : ℕ) (u₀ : Fin N), fh' 0 = d₀ * N + (u₀ : ℕ) ∧ d₀ < N ∧
        τ.vars vv = (u₀ : ℕ) ∧ τ.vars dv = d₀ ∧
        (τ.vars zv = 0 ∨ τ.vars zv = 1) ∧
        (τ.vars zv = 0 ↔ (τ.arrs dg).getD (u₀ : ℕ) 0 = d₀) with hI
  have hzB : ∀ τ, I τ → ∃ v, (Cond.eq (.var zv) (.lit 1)).evalB B τ
      = some v := by
    rintro τ ⟨hn', fh', hPτ, -, -, -, -, d₀, u₀, -, -, -, -, hz01, -⟩
    refine ⟨_, evalB_condEq (evB_var rfl ?_) (evalB_lit (by omega))⟩
    rcases hz01 with h | h <;> rw [h] <;> omega
  have hstep : ∀ τ, I τ → (Cond.eq (.var zv) (.lit 1)).evalB B τ
      = some true →
      ∃ τ' K, Run B (.seq (heapPopCom hp hsv tv xv yv)
        (chkCom nNm dg hp kv dv vv zv)) τ τ' K ∧ I τ' ∧
        1 + (Cond.eq (.var zv) (.lit 1)).size + K + C * τ'.vars hsv
          ≤ C * τ.vars hsv := by
    rintro τ ⟨hn', fh', hPτ, hle, hvf, haf, hlf, d₀, u₀, hkey, hd₀N, hvv, hdv,
      hz01, hziff⟩
    intro hcond
    have hz1 : τ.vars zv = 1 := by
      have h2 := evalB_condEq (B := B) (evB_var (x := zv) rfl
        (by rcases hz01 with h | h <;> rw [h] <;> omega))
        (evalB_lit (show (1:ℕ) < B by omega))
      rw [hcond] at h2
      have h3 := (Option.some.inj h2).symm
      rcases hz01 with h | h
      · rw [h] at h3
        simp at h3
      · exact h
    have hzne : ¬ (τ.arrs dg).getD (u₀ : ℕ) 0 = d₀ := by
      intro hc
      have := hziff.mpr hc
      omega
    -- the pop
    have hn'0 : 0 < hn' := hPτ.hn_pos hne
    have hnsub : hn' ≤ N + nsOf F := by
      have := hPτ.hsize
      omega
    have hfB : ∀ t, t < hn' → fh' t < B := by
      intro t ht
      have := hPτ.fh_lt ht
      omega
    have hnB' : 2 * hn' + 2 < B := by
      have h1 := hPτ.hsize
      have h2 := nsOf_le F
      omega
    obtain ⟨σp, hrunp, ⟨g, hHp, hcont⟩, hparr, hpvar, hplen⟩ :=
      (heapPop_spec hp hsv tv xv yv hht hhx hhy htx hty hxy hnB' hn'0
        hfB).run hPτ.hheap
    have hpdg : σp.arrs dg = τ.arrs dg := hparr dg hdghp
    have hPp : PeelSt F nNm ao aj dg ra hp hsv aoL ajL live (hn' - 1) g
        σp := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hHp, ?_, ?_, ?_⟩
      · rw [hparr ao haohp, hPτ.hao]
      · rw [hparr aj hajhp, hPτ.haj]
      · rw [hpvar nNm hns hnt hnx hny, hPτ.hnN]
      · rw [hpdg]; exact hPτ.hdgL
      · rw [hparr ra hrahp]; exact hPτ.hraL
      · rw [hplen hp]; exact hPτ.hhpL
      · intro u
        rw [hpdg]
        exact hPτ.hdg u
      · intro u hu
        rw [hparr ra hrahp]
        exact hPτ.hra u hu
      · intro u hu
        rw [hcont]
        have hne' : (nbrsIn F live u).card * N + (u : ℕ) ≠ fh' 0 := by
          intro hc
          obtain ⟨hd, huu⟩ := key_inj u.isLt u₀.isLt (hc.trans hkey)
          refine hzne ?_
          rw [← huu, hPτ.hdg u, if_pos hu]
          exact hd
        rw [Multiset.count_erase_of_ne hne', hPτ.hwit u hu]
      · intro k hk
        rw [hcont] at hk
        exact hPτ.hlow k (Multiset.mem_of_mem_erase hk)
      · have hsum : (∑ t ∈ Finset.range N, (σp.arrs dg).getD t 0)
            = ∑ t ∈ Finset.range N, (τ.arrs dg).getD t 0 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hpdg]
        rw [hsum]
        have := hPτ.hsize
        omega
    -- the re-decode
    obtain ⟨σc, Kc, hrunc, hKc, hPc, hcvars, hcarrs, d₁, u₁, hkey₁, hd₁N,
      hvv₁, hdv₁, hz01₁, hziff₁⟩ := chk_run hchk hB hPp hne
    have hlogle : Nat.log 2 (hn' + 1) ≤ L := by
      rw [hL]
      exact Nat.log_mono_right (by omega)
    refine ⟨σc, _, Run.seq hrunp hrunc, ?_, ?_⟩
    · -- the invariant is maintained
      refine ⟨hn' - 1, g, hPc, by omega, ?_, ?_, ?_, d₁, u₁, hkey₁, hd₁N,
        hvv₁, hdv₁, hz01₁, ?_⟩
      · intro y hy
        have hy' := hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
        obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8⟩ := hy'
        rw [hcvars y (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hy1, hy2, hy3, hy4⟩), hpvar y hy5 hy6 hy7 hy8]
        exact hvf y hy
      · intro b hb
        rw [hcarrs b, hparr b hb]
        exact haf b hb
      · intro b
        rw [hcarrs b, hplen b]
        exact hlf b
      · rwa [← hcarrs dg] at hziff₁
    · -- the payment: one pop and one decode ride one unit of shrinkage
      have hhsτ : τ.vars hsv = hn' := hPτ.hheap.size
      have hhsc : σc.vars hsv = hn' - 1 := by
        rw [hcvars hsv (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hsk, hsd, hsv', hsz⟩)]
        exact hHp.size
      rw [hhsτ, hhsc]
      have hCsplit : C * hn' = C * (hn' - 1) + C := by
        conv_lhs => rw [show hn' = (hn' - 1) + 1 by omega]
        rw [Nat.mul_add, Nat.mul_one]
      rw [hCsplit]
      simp only [Cond.size, Expr.size]
      omega
  obtain ⟨d₀, u₀, hkey, hd₀N, hvv, hdv, hz01, hziff⟩ := hpost
  obtain ⟨σ', K, hrunW, hI', hcondF, hpay⟩ :=
    Run.while_potential I (fun τ => C * τ.vars hsv) hzB hstep
      (show I σ from ⟨hn, fh, hP, le_rfl, fun y _ => rfl, fun b _ => rfl,
        fun b => rfl, d₀, u₀, hkey, hd₀N, hvv, hdv, hz01, hziff⟩)
  obtain ⟨hn', fh', hP', hle', hvf', haf', hlf', d₁, u₁, hkey₁, hd₁N, hvv₁,
    hdv₁, hz01₁, hziff₁⟩ := hI'
  have hz0 : σ'.vars zv = 0 := by
    have h2 := evalB_condEq (B := B) (evB_var (x := zv) rfl
      (by rcases hz01₁ with h | h <;> rw [h] <;> omega))
      (evalB_lit (show (1:ℕ) < B by omega))
    rw [hcondF] at h2
    have h3 := (Option.some.inj h2).symm
    rcases hz01₁ with h | h
    · exact h
    · rw [h] at h3
      simp at h3
  have hcell := hziff₁.mp hz0
  have hhsσ : σ.vars hsv = hn := hP.hheap.size
  have hhs' : σ'.vars hsv = hn' := hP'.hheap.size
  rw [hhsσ, hhs'] at hpay
  refine ⟨σ', K, hn', fh', hrunW, ?_, hle', hP', hvf', haf', hlf',
    d₁, u₁, hkey₁, hd₁N, hvv₁, hdv₁, hcell⟩
  simp only [Cond.size, Expr.size] at hpay
  omega

end PeelSteps

/-! ### §2e The base-row scan -/

section RowScan

variable {N : ℕ}

open Classical in
/-- The live neighbours of the victim already seen by the scan: those
read off a slot strictly below the pointer. -/
noncomputable def procSet (F : SimpleGraph (Fin N)) (ajL : List ℕ)
    (offF : ℕ → ℕ) (live : Finset (Fin N)) (vstar : Fin N) (s : ℕ) :
    Finset (Fin N) :=
  (nbrsIn F live vstar).filter
    (fun w => ∃ t, offF (vstar : ℕ) + t < s ∧ t < baseDeg F (vstar : ℕ) ∧
      ajL.getD (offF (vstar : ℕ) + t) 0 = (w : ℕ))

theorem procSet_subset (F : SimpleGraph (Fin N)) (ajL : List ℕ)
    (offF : ℕ → ℕ) (live : Finset (Fin N)) (vstar : Fin N) (s : ℕ) :
    procSet F ajL offF live vstar s ⊆ nbrsIn F live vstar := by
  classical
  exact Finset.filter_subset _ _

theorem procSet_start (F : SimpleGraph (Fin N)) (ajL : List ℕ)
    (offF : ℕ → ℕ) (live : Finset (Fin N)) (vstar : Fin N) :
    procSet F ajL offF live vstar (offF (vstar : ℕ)) = ∅ := by
  classical
  rw [procSet, Finset.filter_eq_empty_iff]
  rintro w - ⟨t, ht, -, -⟩
  omega

/-- One live slot advances the seen set by exactly its target. -/
theorem procSet_succ_live {F : SimpleGraph (Fin N)} {ajL : List ℕ}
    {offF : ℕ → ℕ} {live : Finset (Fin N)} {vstar : Fin N} {t₀ : ℕ}
    (hrowInj : Set.InjOn (fun t => ajL.getD (offF (vstar : ℕ) + t) 0)
      {t | t < baseDeg F (vstar : ℕ)})
    (ht₀ : t₀ < baseDeg F (vstar : ℕ)) {w₀ : Fin N}
    (hw₀ : ajL.getD (offF (vstar : ℕ) + t₀) 0 = (w₀ : ℕ))
    (hw₀live : w₀ ∈ live) (hw₀adj : F.Adj w₀ vstar) :
    procSet F ajL offF live vstar (offF (vstar : ℕ) + t₀ + 1)
        = insert w₀ (procSet F ajL offF live vstar (offF (vstar : ℕ) + t₀))
      ∧ w₀ ∉ procSet F ajL offF live vstar (offF (vstar : ℕ) + t₀) := by
  classical
  constructor
  · ext w
    rw [Finset.mem_insert, procSet, procSet, Finset.mem_filter,
      Finset.mem_filter]
    constructor
    · rintro ⟨hwmem, t, htlt, htb, hval⟩
      rcases Nat.lt_or_ge (offF (vstar : ℕ) + t) (offF (vstar : ℕ) + t₀)
        with h | h
      · exact Or.inr ⟨hwmem, t, h, htb, hval⟩
      · have ht : t = t₀ := by omega
        subst ht
        left
        have : (w : ℕ) = (w₀ : ℕ) := by rw [← hval, hw₀]
        exact Fin.ext this
    · rintro (rfl | ⟨hwmem, t, htlt, htb, hval⟩)
      · exact ⟨mem_nbrsIn.mpr ⟨hw₀live, hw₀adj⟩, t₀, by omega, ht₀, hw₀⟩
      · exact ⟨hwmem, t, by omega, htb, hval⟩
  · rw [procSet, Finset.mem_filter]
    rintro ⟨-, t, htlt, htb, hval⟩
    have hne : t ≠ t₀ := by omega
    refine hne (hrowInj (Set.mem_setOf_eq ▸ htb) (Set.mem_setOf_eq ▸ ht₀) ?_)
    show ajL.getD (offF (vstar : ℕ) + t) 0
        = ajL.getD (offF (vstar : ℕ) + t₀) 0
    rw [hval, hw₀]

/-- A dead slot advances nothing. -/
theorem procSet_succ_dead {F : SimpleGraph (Fin N)} {ajL : List ℕ}
    {offF : ℕ → ℕ} {live : Finset (Fin N)} {vstar : Fin N} {t₀ : ℕ}
    {w₀ : Fin N}
    (hw₀ : ajL.getD (offF (vstar : ℕ) + t₀) 0 = (w₀ : ℕ))
    (hw₀dead : w₀ ∉ live) :
    procSet F ajL offF live vstar (offF (vstar : ℕ) + t₀ + 1)
      = procSet F ajL offF live vstar (offF (vstar : ℕ) + t₀) := by
  classical
  ext w
  rw [procSet, procSet, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hwmem, t, htlt, htb, hval⟩
    refine ⟨hwmem, t, ?_, htb, hval⟩
    rcases Nat.lt_or_ge (offF (vstar : ℕ) + t) (offF (vstar : ℕ) + t₀)
      with h | h
    · exact h
    · exfalso
      have ht : t = t₀ := by omega
      subst ht
      obtain ⟨hwlive, -⟩ := mem_nbrsIn.mp hwmem
      have : w = w₀ := Fin.ext (by rw [← hval, hw₀])
      exact hw₀dead (this ▸ hwlive)
  · rintro ⟨hwmem, t, htlt, htb, hval⟩
    exact ⟨hwmem, t, by omega, htb, hval⟩

/-- At the row's end everything live and adjacent has been seen. -/
theorem procSet_last {F : SimpleGraph (Fin N)} {ajL : List ℕ}
    {offF : ℕ → ℕ} {live : Finset (Fin N)} {vstar : Fin N}
    (hrowCom : ∀ w : Fin N, F.Adj vstar w →
      ∃ t, t < baseDeg F (vstar : ℕ) ∧
        ajL.getD (offF (vstar : ℕ) + t) 0 = (w : ℕ)) :
    procSet F ajL offF live vstar
        (offF (vstar : ℕ) + baseDeg F (vstar : ℕ))
      = nbrsIn F live vstar := by
  classical
  refine Finset.Subset.antisymm (procSet_subset ..) ?_
  intro w hw
  obtain ⟨hwlive, hwadj⟩ := mem_nbrsIn.mp hw
  obtain ⟨t, htb, hval⟩ := hrowCom w hwadj.symm
  rw [procSet, Finset.mem_filter]
  exact ⟨hw, t, by omega, htb, hval⟩

/-- The sharper size bound: degree sum plus carrier fits the square. -/
theorem nsOf_add_le (F : SimpleGraph (Fin N)) : nsOf F + N ≤ N * N := by
  rcases N with _ | n
  · simp [nsOf]
  · have h1 : nsOf F ≤ (n + 1) * n := by
      calc nsOf F ≤ ∑ _t ∈ Finset.range (n + 1), n := by
            refine Finset.sum_le_sum fun t ht => ?_
            have := baseDeg_lt F (Finset.mem_range.mp ht)
            omega
        _ = (n + 1) * n := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h2 : (n + 1) * n + (n + 1) = (n + 1) * (n + 1) := by ring
    omega

/-- **The mid-scan state**: the degree cells discounted on the seen
set `W`, the witness and staleness clauses phrased against the cells
with the victim already outside them, and the size account slackened
by `|W|` — one for each fresh push. -/
structure RowSt {N : ℕ} (F : SimpleGraph (Fin N))
    (nNm ao aj dg hp hsv : String) (aoL ajL : List ℕ)
    (live : Finset (Fin N)) (vstar : Fin N) (hn : ℕ) (fh : ℕ → ℕ)
    (W : Finset (Fin N)) (σ : Env) : Prop where
  hao : σ.arrs ao = aoL
  haj : σ.arrs aj = ajL
  hnN : σ.vars nNm = N
  hdgL : N ≤ (σ.arrs dg).length
  hhpL : N * N + N ≤ (σ.arrs hp).length
  hdg : ∀ u : Fin N, (σ.arrs dg).getD (u : ℕ) 0 =
      if u ∈ live then (nbrsIn F live u).card - (if u ∈ W then 1 else 0)
      else 0
  hheap : HeapSt hp hsv hn fh σ
  hwit : ∀ u ∈ live.erase vstar,
      (hMul hn fh).count ((σ.arrs dg).getD (u : ℕ) 0 * N + (u : ℕ)) = 1
  hlow : ∀ k ∈ hMul hn fh, ∃ (d : ℕ) (u' : Fin N), k = d * N + (u' : ℕ) ∧
      d < N ∧ (u' ∈ live.erase vstar → (σ.arrs dg).getD (u' : ℕ) 0 ≤ d) ∧
      (u' ∉ live.erase vstar → 1 ≤ d)
  hsize : 2 * hn + dgSum dg N σ ≤ 2 * N + nsOf F + W.card

/-- Every mid-scan heap cell is below the square. -/
theorem RowSt.fh_lt {N : ℕ} {F : SimpleGraph (Fin N)}
    {nNm ao aj dg hp hsv : String} {aoL ajL : List ℕ}
    {live : Finset (Fin N)} {vstar : Fin N} {hn : ℕ} {fh : ℕ → ℕ}
    {W : Finset (Fin N)} {σ : Env}
    (h : RowSt F nNm ao aj dg hp hsv aoL ajL live vstar hn fh W σ)
    {t : ℕ} (ht : t < hn) : fh t < N * N := by
  obtain ⟨d, u, hk, hdN, -, -⟩ := h.hlow (fh t) (f_mem_hMul fh ht)
  have huN : (u : ℕ) < N := u.isLt
  have h1 : d * N + (u : ℕ) < (d + 1) * N := by rw [Nat.succ_mul]; omega
  have h2 : (d + 1) * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  omega

/-- The mid-scan state transports along agreement on what it reads. -/
theorem RowSt.of_eq {N : ℕ} {F : SimpleGraph (Fin N)}
    {nNm ao aj dg hp hsv : String} {aoL ajL : List ℕ}
    {live : Finset (Fin N)} {vstar : Fin N} {hn : ℕ} {fh : ℕ → ℕ}
    {W : Finset (Fin N)} {σ : Env}
    (h : RowSt F nNm ao aj dg hp hsv aoL ajL live vstar hn fh W σ)
    {σ' : Env} (hao' : σ'.arrs ao = σ.arrs ao) (haj' : σ'.arrs aj = σ.arrs aj)
    (hdg' : σ'.arrs dg = σ.arrs dg) (hhp' : σ'.arrs hp = σ.arrs hp)
    (hnN' : σ'.vars nNm = σ.vars nNm) (hhs' : σ'.vars hsv = σ.vars hsv) :
    RowSt F nNm ao aj dg hp hsv aoL ajL live vstar hn fh W σ' where
  hao := by rw [hao', h.hao]
  haj := by rw [haj', h.haj]
  hnN := by rw [hnN', h.hnN]
  hdgL := by rw [hdg']; exact h.hdgL
  hhpL := by rw [hhp']; exact h.hhpL
  hdg := fun u => by rw [hdg']; exact h.hdg u
  hheap := h.hheap.of_eq hhp' hhs'
  hwit := fun u hu => by rw [hdg']; exact h.hwit u hu
  hlow := fun k hk => by
    obtain ⟨d, u', hk', hdN, hbr1, hbr2⟩ := h.hlow k hk
    exact ⟨d, u', hk', hdN, fun hu => by rw [hdg']; exact hbr1 hu, hbr2⟩
  hsize := by
    have hs' : dgSum dg N σ' = dgSum dg N σ := dgSum_congr hdg'
    rw [hs']
    exact h.hsize

end RowScan

section RowRun

variable {B N : ℕ} {F : SimpleGraph (Fin N)}
variable {nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv : String}
variable {aoL ajL : List ℕ} {offF : ℕ → ℕ}

set_option maxHeartbeats 1000000 in
/-- **The base-row scan**: walk the victim's whole base row; on every
live target, decrement its cell and push the fresh entry. Leaves the
mid-scan state at the full seen set, the heap grown by exactly the
victim's live degree, at a cost linear in the base row with one
logarithm on the pushes. -/
private theorem row_run
    (hht : hsv ≠ tv) (hhx : hsv ≠ xv) (hhy : hsv ≠ yv)
    (htx : tv ≠ xv) (hty : tv ≠ yv) (hxy : xv ≠ yv)
    (hnN_w : nNm ∉ ([wv, xv, kv, iv, hsv, tv, yv] : List String))
    (hvv_w : vv ∉ ([wv, xv, kv, iv, hsv, tv, yv] : List String))
    (hwx : wv ≠ xv) (hwk : wv ≠ kv) (hwi : wv ≠ iv)
    (hwhs : wv ≠ hsv) (hwt : wv ≠ tv) (hwy : wv ≠ yv)
    (hik : iv ≠ kv) (hix : iv ≠ xv) (hihs : iv ≠ hsv) (hit : iv ≠ tv)
    (hiy : iv ≠ yv) (hkhs : kv ≠ hsv) (hkt : kv ≠ tv) (hkx : kv ≠ xv)
    (hky : kv ≠ yv)
    (hdgao : dg ≠ ao) (hdgaj : dg ≠ aj) (haohp : ao ≠ hp)
    (hajhp : aj ≠ hp) (hdghp : dg ≠ hp)
    (hB : N * N + 4 * N + 4 ≤ B)
    (hrow : ∀ (u : Fin N) (t : ℕ), t < baseDeg F (u : ℕ) →
      ∃ w : Fin N, F.Adj u w ∧ ajL.getD (offF (u : ℕ) + t) 0 = (w : ℕ))
    (hrowInj : ∀ u : Fin N,
      Set.InjOn (fun t => ajL.getD (offF (u : ℕ) + t) 0)
        {t | t < baseDeg F (u : ℕ)})
    (hrowCom : ∀ (u w : Fin N), F.Adj u w →
      ∃ t, t < baseDeg F (u : ℕ) ∧ ajL.getD (offF (u : ℕ) + t) 0 = (w : ℕ))
    (hoffF : ∀ i, i ≤ N → aoL.getD i 0 = offF i)
    (hoff0 : offF 0 = 0)
    (hoffStep : ∀ v : Fin N, offF ((v : ℕ) + 1)
      = offF (v : ℕ) + (F.neighborSet v).ncard)
    (haoLen : N + 1 ≤ aoL.length) (hajLen : nsOf F ≤ ajL.length)
    {live : Finset (Fin N)} {vstar : Fin N} (hvs : vstar ∈ live)
    {hn₀ : ℕ} {fh₀ : ℕ → ℕ} {σ₀ : Env}
    (hR : RowSt F nNm ao aj dg hp hsv aoL ajL live vstar hn₀ fh₀ ∅ σ₀)
    (hiv : σ₀.vars iv = offF (vstar : ℕ))
    (hvv : σ₀.vars vv = (vstar : ℕ)) :
    ∃ σ' K' hn' fh', Run B
        (.while (.lt (.var iv) (.get ao (.add (.var vv) (.lit 1))))
          (rowBody nNm aj dg hp hsv tv xv yv kv iv wv)) σ₀ σ' K' ∧
      K' ≤ (28 * Nat.log 2 (N + nsOf F + 1) + 46) * baseDeg F (vstar : ℕ)
        + 7 ∧
      RowSt F nNm ao aj dg hp hsv aoL ajL live vstar hn' fh'
        (nbrsIn F live vstar) σ' ∧
      hn' = hn₀ + (nbrsIn F live vstar).card ∧
      dgSum dg N σ' + (nbrsIn F live vstar).card ≤ dgSum dg N σ₀ ∧
      (∀ y, y ∉ ([wv, xv, kv, iv, hsv, tv, yv] : List String) →
        σ'.vars y = σ₀.vars y) ∧
      (∀ b, b ≠ dg → b ≠ hp → σ'.arrs b = σ₀.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ₀.arrs b).length) := by
  set L := Nat.log 2 (N + nsOf F + 1) with hL
  have hN0 : 0 < N := Fin.pos vstar
  have hnsq := nsOf_add_le F
  have hoffN : ∀ i, i ≤ N → offF i ≤ nsOf F := by
    intro i hi
    have h1 := offF_mono (G := F) (offF := offF) hoffStep N le_rfl i hi
    have h2 := offF_eq_sum (F := F) hoff0 hoffStep N le_rfl
    rw [← nsOf] at h2
    omega
  have hvend : offF ((vstar : ℕ) + 1)
      = offF (vstar : ℕ) + baseDeg F (vstar : ℕ) := by
    rw [hoffStep vstar, baseDeg_eq]
  have hvN : (vstar : ℕ) < N := vstar.isLt
  -- the loop invariant
  set bodyC : Com := rowBody nNm aj dg hp hsv tv xv yv kv iv wv with hbody
  set condC : Cond := .lt (.var iv) (.get ao (.add (.var vv) (.lit 1)))
    with hcond
  set I : Env → Prop := fun τ =>
    ∃ s hn fh, τ.vars iv = s ∧ offF (vstar : ℕ) ≤ s ∧
      s ≤ offF ((vstar : ℕ) + 1) ∧ τ.vars vv = (vstar : ℕ) ∧
      RowSt F nNm ao aj dg hp hsv aoL ajL live vstar hn fh
        (procSet F ajL offF live vstar s) τ ∧
      hn = hn₀ + (procSet F ajL offF live vstar s).card ∧
      dgSum dg N τ + (procSet F ajL offF live vstar s).card ≤ dgSum dg N σ₀ ∧
      (∀ y, y ∉ ([wv, xv, kv, iv, hsv, tv, yv] : List String) →
        τ.vars y = σ₀.vars y) ∧
      (∀ b, b ≠ dg → b ≠ hp → τ.arrs b = σ₀.arrs b) ∧
      (∀ b, (τ.arrs b).length = (σ₀.arrs b).length) with hI
  -- reading the loop condition inside the invariant
  have hcondEval : ∀ τ s hn fh, τ.vars iv = s → τ.vars vv = (vstar : ℕ) →
      RowSt F nNm ao aj dg hp hsv aoL ajL live vstar hn fh
        (procSet F ajL offF live vstar s) τ →
      s ≤ offF ((vstar : ℕ) + 1) →
      condC.evalB B τ = some (decide (s < offF ((vstar : ℕ) + 1))) := by
    intro τ s hn fh hivτ hvvτ hRτ hsend
    have hsB : s < B := by
      have := hoffN ((vstar : ℕ) + 1) (by omega)
      omega
    have hidx : (Expr.add (.var vv) (.lit 1)).evalB B τ
        = some ((vstar : ℕ) + 1) := by
      have h := evalB_bin (op := .add) (evB_var hvvτ (by omega))
        (evalB_lit (by omega))
        (show Bop.add.apply (vstar : ℕ) 1 < B by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    refine evalB_condLt (evB_var hivτ hsB) ?_
    refine evB_get hidx ?_ ?_ ?_
    · rw [hRτ.hao]
      omega
    · rw [hRτ.hao]
      exact hoffF ((vstar : ℕ) + 1) (by omega)
    · have := hoffN ((vstar : ℕ) + 1) (by omega)
      omega
  have hdef : ∀ τ, I τ → ∃ v, condC.evalB B τ = some v := by
    rintro τ ⟨s, hn, fh, hivτ, -, hsend, hvvτ, hRτ, -, -, -, -, -⟩
    exact ⟨_, hcondEval τ s hn fh hivτ hvvτ hRτ hsend⟩
  -- one turn
  have hstep : ∀ τ, I τ → condC.evalB B τ = some true →
      ∃ τ', Run B bodyC τ τ' (28 * L + 39) ∧ I τ' ∧
        (offF ((vstar : ℕ) + 1) - τ'.vars iv)
          < (offF ((vstar : ℕ) + 1) - τ.vars iv) := by
    rintro τ ⟨s, hn, fh, hivτ, hslo, hsend, hvvτ, hRτ, hhn, hSle, hvf, haf,
      hlf⟩
    intro hcondT
    -- the condition's truth
    have hslt : s < offF ((vstar : ℕ) + 1) := by
      have h2 := hcondEval τ s hn fh hivτ hvvτ hRτ hsend
      rw [hcondT] at h2
      exact of_decide_eq_true (Option.some.inj h2).symm
    set t₀ := s - offF (vstar : ℕ) with ht₀
    have hst₀ : s = offF (vstar : ℕ) + t₀ := by omega
    have ht₀b : t₀ < baseDeg F (vstar : ℕ) := by omega
    obtain ⟨w₀, hadj, hval⟩ := hrow vstar t₀ ht₀b
    rw [← hst₀] at hval
    have hw₀vs : w₀ ≠ vstar := (F.ne_of_adj hadj).symm
    have hw₀N : (w₀ : ℕ) < N := w₀.isLt
    have hsB : s < B := by
      have := hoffN ((vstar : ℕ) + 1) (by omega)
      omega
    have hsaj : s < ajL.length := by
      have h1 := hoffN ((vstar : ℕ) + 1) (by omega)
      omega
    -- membership components of the two kept scalars
    have hnN_w' := hnN_w
    have hvv_w' := hvv_w
    simp only [List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hnN_w' hvv_w'
    obtain ⟨hnw, hnx', hnk', hni', hns', hnt', hny'⟩ := hnN_w'
    obtain ⟨hvw, hvx, hvk, hvi, hvhs, hvt, hvy⟩ := hvv_w'
    -- read the slot
    have hev1 : (Expr.get aj (.var iv)).evalB B τ = some (w₀ : ℕ) := by
      refine evB_get (evB_var hivτ hsB) ?_ ?_ (by omega)
      · rw [hRτ.haj]
        omega
      · rw [hRτ.haj]
        exact hval
    set τ₁ := τ.setVar wv (w₀ : ℕ) with hτ₁
    have h1wv : τ₁.vars wv = (w₀ : ℕ) := by rw [hτ₁, vars_setVar, if_pos rfl]
    have h1iv : τ₁.vars iv = s := by
      rw [hτ₁, vars_setVar, if_neg (Ne.symm hwi), hivτ]
    have h1arr : ∀ b, τ₁.arrs b = τ.arrs b := fun b => by
      rw [hτ₁, arrs_setVar]
    set W := procSet F ajL offF live vstar s with hW
    have hcellw : (τ.arrs dg).getD (w₀ : ℕ) 0
        = if w₀ ∈ live then (nbrsIn F live w₀).card
            - (if w₀ ∈ W then 1 else 0) else 0 := hRτ.hdg w₀
    have hcellN : (τ.arrs dg).getD (w₀ : ℕ) 0 < N := by
      rw [hcellw]
      have := card_nbrsIn_lt F live w₀
      split
      · split <;> omega
      · omega
    have hevT : (Expr.get dg (.var wv)).evalB B τ₁
        = some ((τ.arrs dg).getD (w₀ : ℕ) 0) := by
      refine evB_get (evB_var h1wv (by omega)) ?_ ?_ (by omega)
      · rw [h1arr]
        have := hRτ.hdgL
        omega
      · rw [h1arr]
    -- the shared size facts of the heap
    have hWsub : W ⊆ nbrsIn F live vstar := procSet_subset ..
    have hWcard : W.card ≤ (nbrsIn F live vstar).card :=
      Finset.card_le_card hWsub
    have hvsW : vstar ∉ W := by
      intro hc
      exact F.irrefl (mem_nbrsIn.mp (hWsub hc)).2
    have hcellvs : (τ.arrs dg).getD ((vstar : ℕ)) 0
        = (nbrsIn F live vstar).card := by
      rw [hRτ.hdg vstar, if_pos hvs, if_neg hvsW, Nat.sub_zero]
    have hSvs : (nbrsIn F live vstar).card ≤ dgSum dg N τ := by
      rw [← hcellvs, dgSum]
      exact Finset.single_le_sum (f := fun t => (τ.arrs dg).getD t 0)
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hvN)
    have hsz := hRτ.hsize
    have hnle : hn ≤ N + nsOf F := by omega
    have hlog : Nat.log 2 (hn + 1) ≤ L := by
      rw [hL]
      exact Nat.log_mono_right (by omega)
    have hcap : hn + 1 ≤ N * N + N := by omega
    have h2hnB : 2 * hn + 2 < B := by omega
    have hfB : ∀ t, t < hn → fh t < B := by
      intro t ht
      have := hRτ.fh_lt ht
      omega
    by_cases hlivew : w₀ ∈ live
    · -- a live target: decrement and push
      obtain ⟨hWstep, hw₀W⟩ := procSet_succ_live (hrowInj vstar) ht₀b
        (hst₀ ▸ hval) hlivew hadj.symm
      rw [← hst₀] at hWstep hw₀W
      rw [← hW] at hWstep hw₀W
      set c₁ := (nbrsIn F live w₀).card with hc₁
      have hcell1 : (τ.arrs dg).getD (w₀ : ℕ) 0 = c₁ := by
        rw [hcellw, if_pos hlivew, if_neg hw₀W, Nat.sub_zero]
      have hcpos : 0 < c₁ := card_nbrsIn_pos hvs hadj
      have hc₁N : c₁ < N := card_nbrsIn_lt F live w₀
      have hcT : (Cond.lt (.lit 0) (.get dg (.var wv))).evalB B τ₁
          = some true := by
        rw [evalB_condLt (evalB_lit (by omega)) hevT,
          decide_eq_true (by rw [hcell1]; omega)]
      have hev2 : (Expr.sub (.get dg (.var wv)) (.lit 1)).evalB B τ₁
          = some (c₁ - 1) := by
        have h := evalB_bin (op := .sub) hevT (evalB_lit (by omega))
          (show Bop.sub.apply ((τ.arrs dg).getD (w₀ : ℕ) 0) 1 < B by
            rw [Bop.apply_sub]; omega)
        rwa [Bop.apply_sub, hcell1] at h
      set τ₂ := τ₁.setVar xv (c₁ - 1) with hτ₂
      have h2wv : τ₂.vars wv = (w₀ : ℕ) := by
        rw [hτ₂, vars_setVar, if_neg hwx, h1wv]
      have h2xv : τ₂.vars xv = c₁ - 1 := by rw [hτ₂, vars_setVar, if_pos rfl]
      have h2iv : τ₂.vars iv = s := by
        rw [hτ₂, vars_setVar, if_neg hix, h1iv]
      have h2arr : ∀ b, τ₂.arrs b = τ.arrs b := fun b => by
        rw [hτ₂, arrs_setVar, h1arr]
      have hev3i : (Expr.var wv).evalB B τ₂ = some (w₀ : ℕ) :=
        evB_var h2wv (by omega)
      have hev3v : (Expr.var xv).evalB B τ₂ = some (c₁ - 1) :=
        evB_var h2xv (by omega)
      have hr3 : (w₀ : ℕ) < (τ₂.arrs dg).length := by
        rw [h2arr]
        have := hRτ.hdgL
        omega
      set τ₃ := τ₂.setArr dg (w₀ : ℕ) (c₁ - 1) with hτ₃
      have h3dgarr : τ₃.arrs dg = (τ.arrs dg).set (w₀ : ℕ) (c₁ - 1) := by
        rw [hτ₃, arrs_setArr, if_pos rfl, h2arr]
      have h3arr : ∀ b, b ≠ dg → τ₃.arrs b = τ.arrs b := fun b hb => by
        rw [hτ₃, arrs_setArr, if_neg hb, h2arr]
      have h3wv : τ₃.vars wv = (w₀ : ℕ) := by rw [hτ₃, vars_setArr, h2wv]
      have h3xv : τ₃.vars xv = c₁ - 1 := by rw [hτ₃, vars_setArr, h2xv]
      have h3nN : τ₃.vars nNm = N := by
        rw [hτ₃, vars_setArr, hτ₂, vars_setVar, if_neg hnx', hτ₁,
          vars_setVar, if_neg hnw]
        exact hRτ.hnN
      set key := (c₁ - 1) * N + (w₀ : ℕ) with hkeydef
      have hkeyN : key < N * N := by
        have h1 := Nat.mul_le_mul_right N (show c₁ - 1 + 1 ≤ N by omega)
        rw [Nat.succ_mul] at h1
        omega
      have hev4 : (Expr.add (.mul (.var xv) (.var nNm)) (.var wv)).evalB B τ₃
          = some key := by
        have hm := evalB_bin (op := .mul) (evB_var h3xv (by omega))
          (evB_var h3nN (by omega))
          (show Bop.mul.apply (c₁ - 1) N < B by
            rw [Bop.apply_mul]
            have := Nat.mul_le_mul_right N (show c₁ - 1 + 1 ≤ N by omega)
            rw [Nat.succ_mul] at this
            omega)
        rw [Bop.apply_mul] at hm
        have h := evalB_bin (op := .add) hm (evB_var h3wv (by omega))
          (show Bop.add.apply ((c₁ - 1) * N) (w₀ : ℕ) < B by
            rw [Bop.apply_add]
            omega)
        rwa [Bop.apply_add] at h
      set τ₄ := τ₃.setVar kv key with hτ₄
      have h4kv : τ₄.vars kv = key := by rw [hτ₄, vars_setVar, if_pos rfl]
      have h4arr : ∀ b, b ≠ dg → τ₄.arrs b = τ.arrs b := fun b hb => by
        rw [hτ₄, arrs_setVar, h3arr b hb]
      have h4dgarr : τ₄.arrs dg = (τ.arrs dg).set (w₀ : ℕ) (c₁ - 1) := by
        rw [hτ₄, arrs_setVar, h3dgarr]
      have h4hsv : τ₄.vars hsv = τ.vars hsv := by
        rw [hτ₄, vars_setVar, if_neg (Ne.symm hkhs), hτ₃, vars_setArr, hτ₂,
          vars_setVar, if_neg hhx, hτ₁, vars_setVar,
          if_neg (Ne.symm hwhs)]
      have hH₄ : HeapSt hp hsv hn fh τ₄ :=
        hRτ.hheap.of_eq (h4arr hp (Ne.symm hdghp)) h4hsv
      have hlen₄ : hn + 1 ≤ (τ₄.arrs hp).length := by
        rw [h4arr hp (Ne.symm hdghp)]
        have := hRτ.hhpL
        omega
      obtain ⟨σp, hrunp, ⟨g, hHp, hcont⟩, hparr, hpvar, hplen⟩ :=
        (heapPush_spec hp hsv tv xv yv hht hhx hhy htx hty hxy kv
          (n := hn) (k := key) (f := fh) h2hnB
          (lt_of_lt_of_le hkeyN (by omega)) hfB).run
          ⟨hH₄, h4kv, hlen₄⟩
      have hpiv : σp.vars iv = s := by
        rw [hpvar iv hihs hit hix hiy, hτ₄, vars_setVar, if_neg hik,
          hτ₃, vars_setArr, h2iv]
      have hoffv1 := hoffN ((vstar : ℕ) + 1) (by omega)
      have hev6 : (Expr.add (.var iv) (.lit 1)).evalB B σp = some (s + 1) :=
        evalB_bin (evB_var hpiv hsB) (evalB_lit (by omega))
          (show Bop.add.apply s 1 < B by rw [Bop.apply_add]; omega)
      set τ₆ := σp.setVar iv (s + 1) with hτ₆
      have h6dgarr : τ₆.arrs dg = (τ.arrs dg).set (w₀ : ℕ) (c₁ - 1) := by
        rw [hτ₆, arrs_setVar, hparr dg hdghp, h4dgarr]
      have h6arr : ∀ b, b ≠ dg → b ≠ hp → τ₆.arrs b = τ.arrs b := by
        intro b hb1 hb2
        rw [hτ₆, arrs_setVar, hparr b hb2, h4arr b hb1]
      have h6len : ∀ b, (τ₆.arrs b).length = (τ.arrs b).length := by
        intro b
        rw [hτ₆, arrs_setVar, hplen b, hτ₄, arrs_setVar, hτ₃, arrs_setArr]
        split
        · subst b
          rw [List.length_set, hτ₂, arrs_setVar, hτ₁, arrs_setVar]
        · rw [hτ₂, arrs_setVar, hτ₁, arrs_setVar]
      -- reading a cell after the store
      have hr3' : (w₀ : ℕ) < (τ.arrs dg).length := by
        have := hRτ.hdgL
        omega
      have hcell₆ : ∀ u : Fin N, (τ₆.arrs dg).getD (u : ℕ) 0
          = if (u : ℕ) = (w₀ : ℕ) then c₁ - 1
            else (τ.arrs dg).getD (u : ℕ) 0 := by
        intro u
        rw [h6dgarr]
        rcases eq_or_ne ((u : ℕ)) ((w₀ : ℕ)) with h | h
        · rw [if_pos h, h, getD_set_self hr3']
        · rw [if_neg h, getD_set_ne h]
      have hH₆ : HeapSt hp hsv (hn + 1) g τ₆ :=
        hHp.of_eq (by rw [hτ₆, arrs_setVar])
          (by rw [hτ₆, vars_setVar, if_neg (Ne.symm hihs)])
      have hWins : (insert w₀ W).card = W.card + 1 :=
        Finset.card_insert_of_notMem hw₀W
      have hw₀vs' : w₀ ∈ live.erase vstar :=
        Finset.mem_erase.mpr ⟨hw₀vs, hlivew⟩
      have hsum := sum_getD_set (τ.arrs dg) (j := (w₀ : ℕ)) N (c₁ - 1)
        hw₀N hr3'
      rw [hcell1] at hsum
      have hS₆ : dgSum dg N τ₆ + c₁ = dgSum dg N τ + (c₁ - 1) := by
        rw [dgSum, dgSum]
        have h6 : ∀ t ∈ Finset.range N, (τ₆.arrs dg).getD t 0
            = ((τ.arrs dg).set (w₀ : ℕ) (c₁ - 1)).getD t 0 := by
          intro t _
          rw [h6dgarr]
        rw [Finset.sum_congr rfl h6]
        exact hsum
      -- the updated row state
      have hR₆ : RowSt F nNm ao aj dg hp hsv aoL ajL live vstar (hn + 1) g
          (insert w₀ W) τ₆ := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hH₆, ?_, ?_, ?_⟩
        · rw [h6arr ao (Ne.symm hdgao) haohp]
          exact hRτ.hao
        · rw [h6arr aj (Ne.symm hdgaj) hajhp]
          exact hRτ.haj
        · rw [hτ₆, vars_setVar, if_neg hni',
            hpvar nNm hns' hnt' hnx' hny', hτ₄, vars_setVar, if_neg hnk',
            h3nN]
        · rw [h6len dg]
          exact hRτ.hdgL
        · rw [h6len hp]
          exact hRτ.hhpL
        · intro u
          rw [hcell₆ u]
          rcases eq_or_ne ((u : ℕ)) ((w₀ : ℕ)) with h | h
          · have hu : u = w₀ := Fin.ext h
            subst hu
            rw [if_pos h, if_pos hlivew, if_pos (Finset.mem_insert_self _ _),
              ← hc₁]
          · have hu : u ≠ w₀ := fun hc => h (by rw [hc])
            rw [if_neg h, hRτ.hdg u]
            by_cases hul : u ∈ live
            · rw [if_pos hul, if_pos hul]
              by_cases huW : u ∈ W
              · rw [if_pos huW, if_pos (Finset.mem_insert_of_mem huW)]
              · rw [if_neg huW, if_neg (by
                  rw [Finset.mem_insert]
                  rintro (hc | hc)
                  · exact hu hc
                  · exact huW hc)]
            · rw [if_neg hul, if_neg hul]
        · -- the witness clause at the updated cells
          intro u hu
          rw [hcont, hcell₆ u]
          rcases eq_or_ne ((u : ℕ)) ((w₀ : ℕ)) with h | h
          · have hueq : u = w₀ := Fin.ext h
            subst hueq
            rw [if_pos h]
            have hnotmem : ¬ ((c₁ - 1) * N + (u : ℕ)) ∈ hMul hn fh := by
              intro hc
              obtain ⟨d, u', hk', hdN, hbr1, -⟩ := hRτ.hlow _ hc
              obtain ⟨hd, huu⟩ := key_inj u'.isLt u.isLt hk'.symm
              have hu' : u' = u := Fin.ext huu
              subst hu'
              have := hbr1 hu
              rw [hcell1] at this
              omega
            rw [← hkeydef, Multiset.count_cons_self,
              Multiset.count_eq_zero.mpr hnotmem]
          · have hune : u ≠ w₀ := fun hc => h (by rw [hc])
            rw [if_neg h]
            have hkne : (τ.arrs dg).getD (u : ℕ) 0 * N + (u : ℕ) ≠ key := by
              intro hc
              rw [hkeydef] at hc
              obtain ⟨-, huu⟩ := key_inj u.isLt w₀.isLt hc
              exact hune (Fin.ext huu)
            rw [Multiset.count_cons_of_ne hkne]
            exact hRτ.hwit u hu
        · -- the staleness clause at the updated cells
          intro k hk
          rw [hcont] at hk
          rcases Multiset.mem_cons.mp hk with rfl | hk'
          · refine ⟨c₁ - 1, w₀, hkeydef, by omega, ?_, ?_⟩
            · rintro -
              rw [hcell₆ w₀, if_pos rfl]
            · intro hc
              exact absurd hw₀vs' hc
          · obtain ⟨d, u', hk', hdN, hbr1, hbr2⟩ := hRτ.hlow k hk'
            refine ⟨d, u', hk', hdN, ?_, hbr2⟩
            intro hu'
            rw [hcell₆ u']
            rcases eq_or_ne ((u' : ℕ)) ((w₀ : ℕ)) with h | h
            · rw [if_pos h]
              have hu'' : u' = w₀ := Fin.ext h
              subst hu''
              have := hbr1 hu'
              rw [hcell1] at this
              omega
            · rw [if_neg h]
              exact hbr1 hu'
        · -- the size account gains one unit of slack
          have hsz' := hRτ.hsize
          rw [hWins]
          have hdg6 : dgSum dg N τ₆ = ∑ t ∈ Finset.range N,
              (τ₆.arrs dg).getD t 0 := rfl
          omega
      refine ⟨τ₆, ?_, ?_, ?_⟩
      · -- the run
        refine (Run.seq (Run.assign hev1) (Run.seq
          (Run.ite_true hcT (Run.seq (Run.assign hev2)
            (Run.seq (Run.store hev3i hev3v hr3)
              (Run.seq (Run.assign hev4) hrunp))))
          (Run.assign hev6))).mono ?_
        have hKp : 28 * Nat.log 2 (hn + 1) + 13 ≤ 28 * L + 13 := by omega
        simp only [Expr.size, Cond.size]
        omega
      · -- the invariant at the next slot
        rw [hI]
        refine ⟨s + 1, hn + 1, g, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
        · rw [hτ₆, vars_setVar, if_pos rfl]
        · rw [hτ₆, vars_setVar, if_neg hvi,
            hpvar vv hvhs hvt hvx hvy, hτ₄, vars_setVar, if_neg hvk,
            hτ₃, vars_setArr, hτ₂, vars_setVar, if_neg hvx, hτ₁,
            vars_setVar, if_neg hvw, hvvτ]
        · rw [hWstep]
          exact hR₆
        · rw [hWstep, hWins, hhn]
          omega
        · rw [hWstep, hWins]
          omega
        · intro y hy
          have hy' := hy
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
          obtain ⟨hyw, hyx, hyk, hyi, hyhs, hyt, hyy⟩ := hy'
          rw [hτ₆, vars_setVar, if_neg hyi, hpvar y hyhs hyt hyx hyy, hτ₄,
            vars_setVar, if_neg hyk, hτ₃, vars_setArr, hτ₂, vars_setVar,
            if_neg hyx, hτ₁, vars_setVar, if_neg hyw]
          exact hvf y hy
        · intro b hb1 hb2
          rw [h6arr b hb1 hb2]
          exact haf b hb1 hb2
        · intro b
          rw [h6len b]
          exact hlf b
      · -- the variant drops
        have h6iv : τ₆.vars iv = s + 1 := by rw [hτ₆, vars_setVar, if_pos rfl]
        rw [h6iv, hivτ]
        omega
    · -- a dead target: only the pointer moves
      have hWstep := procSet_succ_dead (F := F) (ajL := ajL) (offF := offF)
        (live := live) (vstar := vstar) (t₀ := t₀) (hst₀ ▸ hval) hlivew
      rw [← hst₀] at hWstep
      rw [← hW] at hWstep
      have hcell0 : (τ.arrs dg).getD (w₀ : ℕ) 0 = 0 := by
        rw [hcellw, if_neg hlivew]
      have hcF : (Cond.lt (.lit 0) (.get dg (.var wv))).evalB B τ₁
          = some false := by
        rw [evalB_condLt (evalB_lit (by omega)) hevT,
          decide_eq_false (by rw [hcell0]; omega)]
      have hoffv1 := hoffN ((vstar : ℕ) + 1) (by omega)
      have h1ivB : (Expr.add (.var iv) (.lit 1)).evalB B τ₁ = some (s + 1) :=
        evalB_bin (evB_var h1iv hsB) (evalB_lit (by omega))
          (show Bop.add.apply s 1 < B by rw [Bop.apply_add]; omega)
      set τ₆ := τ₁.setVar iv (s + 1) with hτ₆
      have h6arr : ∀ b, τ₆.arrs b = τ.arrs b := fun b => by
        rw [hτ₆, arrs_setVar, h1arr]
      refine ⟨τ₆, ?_, ?_, ?_⟩
      · refine (Run.seq (Run.assign hev1) (Run.seq
          (Run.ite_false hcF Run.skip) (Run.assign h1ivB))).mono ?_
        simp only [Expr.size, Cond.size]
        omega
      · rw [hI]
        refine ⟨s + 1, hn, fh, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_⟩
        · rw [hτ₆, vars_setVar, if_pos rfl]
        · rw [hτ₆, vars_setVar, if_neg hvi, hτ₁, vars_setVar,
            if_neg hvw, hvvτ]
        · rw [hWstep]
          refine hRτ.of_eq (h6arr ao) (h6arr aj) (h6arr dg) (h6arr hp) ?_ ?_
          · rw [hτ₆, vars_setVar, if_neg hni', hτ₁, vars_setVar,
              if_neg hnw]
          · rw [hτ₆, vars_setVar, if_neg (Ne.symm hihs), hτ₁, vars_setVar,
              if_neg (Ne.symm hwhs)]
        · rw [hWstep]
          exact hhn
        · rw [hWstep]
          have hSeq : dgSum dg N τ₆ = dgSum dg N τ := dgSum_congr (h6arr dg)
          omega
        · intro y hy
          have hy' := hy
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
          obtain ⟨hyw, hyx, hyk, hyi, hyhs, hyt, hyy⟩ := hy'
          rw [hτ₆, vars_setVar, if_neg hyi, hτ₁, vars_setVar, if_neg hyw]
          exact hvf y hy
        · intro b hb1 hb2
          rw [h6arr b]
          exact haf b hb1 hb2
        · intro b
          rw [h6arr b]
          exact hlf b
      · have h6iv : τ₆.vars iv = s + 1 := by rw [hτ₆, vars_setVar, if_pos rfl]
        rw [h6iv, hivτ]
        omega
  -- the loop, counted on the slot pointer
  obtain ⟨σ', hrunW, hI', hcondF⟩ :=
    Run.while_count I (fun τ => offF ((vstar : ℕ) + 1) - τ.vars iv)
      (28 * L + 39) hdef hstep
      (show I σ₀ from ⟨offF (vstar : ℕ), hn₀, fh₀, hiv, le_rfl, by omega,
        hvv, by rw [procSet_start]; exact hR, by rw [procSet_start]; simp,
        by rw [procSet_start]; simp, fun y _ => rfl, fun b _ _ => rfl,
        fun b => rfl⟩)
  obtain ⟨s', hn', fh', hiv', hslo', hsend', hvv', hR', hhn', hSle', hvf',
    haf', hlf'⟩ := hI'
  have hs'end : s' = offF ((vstar : ℕ) + 1) := by
    have h2 := hcondEval σ' s' hn' fh' hiv' hvv' hR' hsend'
    rw [hcondF] at h2
    have h3 := of_decide_eq_false (Option.some.inj h2).symm
    omega
  have hfull : procSet F ajL offF live vstar s' = nbrsIn F live vstar := by
    rw [hs'end, hvend]
    exact procSet_last (fun w hw => hrowCom vstar w hw)
  rw [hfull] at hR' hhn' hSle'
  refine ⟨σ', _, hn', fh', hrunW, ?_, hR', hhn', hSle', hvf', haf', hlf'⟩
  have hA : 1 + condC.size + (28 * L + 39) = 28 * L + 46 := by
    rw [hcond]
    simp only [Cond.size, Expr.size]
    omega
  have hV₀ : offF ((vstar : ℕ) + 1) - σ₀.vars iv = baseDeg F (vstar : ℕ) := by
    rw [hiv, hvend]
    omega
  rw [hA, hV₀, hcond]
  simp only [Cond.size, Expr.size]
  omega

end RowRun

/-! ### §2f The round -/

section Round

variable {B N : ℕ} {F : SimpleGraph (Fin N)}
variable {nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv : String}
variable {aoL ajL : List ℕ} {offF : ℕ → ℕ}

/-- The scan potential is monotone under pointwise cell decrease. -/
theorem scanPot_mono {ao dg : String} {N : ℕ} {σ σ' : Env}
    (hao : σ'.arrs ao = σ.arrs ao)
    (hcells : ∀ t, t < N → (σ'.arrs dg).getD t 0 ≤ (σ.arrs dg).getD t 0) :
    scanPot ao dg N σ' ≤ scanPot ao dg N σ := by
  rw [scanPot, scanPot]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [hao]
  have := hcells t (Finset.mem_range.mp ht)
  split
  · rw [if_pos (by omega)]
  · omega

/-- Erasing the victim discounts exactly its live neighbours. -/
theorem card_nbrsIn_erase {N : ℕ} {F : SimpleGraph (Fin N)}
    {live : Finset (Fin N)} {vstar u : Fin N} (hu : u ∈ live)
    (hv : vstar ∈ live) :
    (nbrsIn F (live.erase vstar) u).card
      = (nbrsIn F live u).card
        - (if u ∈ nbrsIn F live vstar then 1 else 0) := by
  classical
  rw [nbrsIn_erase]
  by_cases hadj : vstar ∈ nbrsIn F live u
  · rw [Finset.card_erase_of_mem hadj,
      if_pos (mem_nbrsIn.mpr ⟨hu, (mem_nbrsIn.mp hadj).2.symm⟩)]
  · rw [Finset.erase_eq_of_notMem hadj,
      if_neg (fun hc => hadj (mem_nbrsIn.mpr ⟨hv, (mem_nbrsIn.mp hc).2.symm⟩))]
    omega

/-- **The outer invariant**: after `i` rounds the live set is the
peel's, the counter holds the remaining count, and the peel state
holds. -/
def OuterI (F : SimpleGraph (Fin N)) (nNm ao aj dg ra hp hsv rc : String)
    (aoL ajL : List ℕ) (σ : Env) : Prop :=
  ∃ i hn fh, i ≤ N ∧ σ.vars rc = N - i ∧
    PeelSt F nNm ao aj dg ra hp hsv aoL ajL (peelLive F i) hn fh σ

/-- **The round potential**: heap entries and degree units at the pop
rate, live base-row widths at the scan rate, and a constant per
remaining round. -/
def peelPot (ao dg hsv rc : String) (N L : ℕ) (σ : Env) : ℕ :=
  (56 * L + 44) * σ.vars hsv + (56 * L + 44) * dgSum dg N σ
    + (28 * L + 46) * scanPot ao dg N σ + 60 * σ.vars rc

set_option maxHeartbeats 1600000 in
/-- **One round of the peel**: discard stale tops, rank and delete the
pinned choice, and pay for everything out of the potential drop. -/
private theorem round_run
    (hnods : ([nNm, hsv, tv, xv, yv, kv, dv, vv, zv, iv, rc, wv] :
      List String).Nodup)
    (harr : ([hp, ra, dg, ao, aj] : List String).Nodup)
    (hB : N * N + 4 * N + 4 ≤ B)
    (hrow : ∀ (u : Fin N) (t : ℕ), t < baseDeg F (u : ℕ) →
      ∃ w : Fin N, F.Adj u w ∧ ajL.getD (offF (u : ℕ) + t) 0 = (w : ℕ))
    (hrowInj : ∀ u : Fin N,
      Set.InjOn (fun t => ajL.getD (offF (u : ℕ) + t) 0)
        {t | t < baseDeg F (u : ℕ)})
    (hrowCom : ∀ (u w : Fin N), F.Adj u w →
      ∃ t, t < baseDeg F (u : ℕ) ∧ ajL.getD (offF (u : ℕ) + t) 0 = (w : ℕ))
    (hoffF : ∀ i, i ≤ N → aoL.getD i 0 = offF i)
    (hoff0 : offF 0 = 0)
    (hoffStep : ∀ v : Fin N, offF ((v : ℕ) + 1)
      = offF (v : ℕ) + (F.neighborSet v).ncard)
    (haoLen : N + 1 ≤ aoL.length) (hajLen : nsOf F ≤ ajL.length) :
    ∀ σ, OuterI F nNm ao aj dg ra hp hsv rc aoL ajL σ →
      (Cond.lt (.lit 0) (.var rc)).evalB B σ = some true →
      ∃ σ' K, Run B
          (roundCom nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv)
          σ σ' K ∧
        OuterI F nNm ao aj dg ra hp hsv rc aoL ajL σ' ∧
        1 + 3 + K + peelPot ao dg hsv rc N (Nat.log 2 (N + nsOf F + 1)) σ'
          ≤ peelPot ao dg hsv rc N (Nat.log 2 (N + nsOf F + 1)) σ := by
  -- the name facts, once
  have hnods' := hnods
  have harr' := harr
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hnods' harr'
  obtain ⟨⟨n_s, n_t, n_x, n_y, n_k, n_d, n_v, n_z, n_i, n_r, n_w⟩,
    ⟨s_t, s_x, s_y, s_k, s_d, s_v, s_z, s_i, s_r, s_w⟩,
    ⟨t_x, t_y, t_k, t_d, t_v, t_z, t_i, t_r, t_w⟩,
    ⟨x_y, x_k, x_d, x_v, x_z, x_i, x_r, x_w⟩,
    ⟨y_k, y_d, y_v, y_z, y_i, y_r, y_w⟩,
    ⟨k_d, k_v, k_z, k_i, k_r, k_w⟩, ⟨d_v, d_z, d_i, d_r, d_w⟩,
    ⟨v_z, v_i, v_r, v_w⟩, ⟨z_i, z_r, z_w⟩, ⟨i_r, i_w⟩, r_w⟩ := hnods'
  obtain ⟨⟨A_pr, A_pd, A_pa, A_pj⟩, ⟨A_rd, A_ra, A_rj⟩, ⟨A_da, A_dj⟩,
    A_aj⟩ := harr'
  have hchk : ([nNm, hsv, kv, dv, vv, zv] : List String).Nodup :=
    hnods.sublist (by
      refine List.Sublist.cons₂ _ (List.Sublist.cons₂ _ ?_)
      refine List.Sublist.cons _ (List.Sublist.cons _
        (List.Sublist.cons _ ?_))
      refine List.Sublist.cons₂ _ (List.Sublist.cons₂ _
        (List.Sublist.cons₂ _ (List.Sublist.cons₂ _ ?_)))
      exact List.nil_sublist _)
  intro σ hO hcond
  obtain ⟨i, hn₀, fh₀, hiN, hrc₀, hP₀⟩ := hO
  set live := peelLive F i with hlive
  -- the counter is positive, so the live set is nonempty
  have hrcpos : 0 < σ.vars rc := lt_of_condLt_lit_var hcond
  have hiN' : i < N := by omega
  have hne : live.Nonempty := peelLive_nonempty F hiN'
  have hN0 : 0 < N := by
    obtain ⟨u, -⟩ := hne
    exact Fin.pos u
  have hnsq := nsOf_add_le F
  have hoffN : ∀ j', j' ≤ N → offF j' ≤ nsOf F := by
    intro j' hj'
    have h1 := offF_mono (G := F) (offF := offF) hoffStep N le_rfl j' hj'
    have h2 := offF_eq_sum (F := F) hoff0 hoffStep N le_rfl
    rw [← nsOf] at h2
    omega
  -- 1. decode the top
  obtain ⟨σc, Kc, hrunc, hKc, hPc, hcvars, hcarrs, dc, uc, hkeyc, hdcN,
    hvvc, hdvc, hz01c, hziffc⟩ := chk_run hchk hB hP₀ hne
  -- 2. discard stale tops
  have hrcc : σc.vars rc = N - i := by
    rw [hcvars rc (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(Ne.symm k_r), (Ne.symm d_r), (Ne.symm v_r), (Ne.symm z_r)⟩), hrc₀]
  obtain ⟨σs, Ks, hn₁, fh₁, hruns, hKs, hn₁le, hPs, hsvars, hsarrs, hslen,
    ds, us, hkeys, hdsN, hvvs, hdvs, hcells⟩ :=
    stale_run hchk s_t s_x s_y t_x t_y x_y n_t n_x n_y (Ne.symm A_pa) (Ne.symm A_pj)
      (Ne.symm A_pd) (Ne.symm A_pr) hB hPc hne ⟨dc, uc, hkeyc, hdcN, hvvc, hdvc,
        hz01c, by rw [← hcarrs dg] at hziffc; exact hziffc⟩
  -- 3. the valid top is the pinned choice
  obtain ⟨hus, hds⟩ := valid_root hPs hne hkeys hcells
  set vstar := minDegVert F live hne with hvstar
  set dstar := (nbrsIn F live vstar).card with hdstar
  have husv : (us : ℕ) = (vstar : ℕ) := by rw [hus]
  have hdsd : ds = dstar := by
    rw [hds, hus, hdstar]
  have hrcs : σs.vars rc = N - i := by
    rw [hsvars rc (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(Ne.symm k_r), (Ne.symm d_r), (Ne.symm v_r), (Ne.symm z_r), (Ne.symm s_r), (Ne.symm t_r),
        (Ne.symm x_r), (Ne.symm y_r)⟩), hrcc]
  have hvN : (vstar : ℕ) < N := vstar.isLt
  have hdstarlt : dstar < N := card_nbrsIn_lt F live vstar
  -- 4. write the rank
  have hevrai : (Expr.var vv).evalB B σs = some ((vstar : ℕ)) := by
    rw [← husv]
    exact evB_var hvvs (by omega)
  have hevrav : (Expr.sub (.var rc) (.lit 1)).evalB B σs
      = some (N - i - 1) := by
    have h := evalB_bin (op := .sub) (evB_var hrcs (by omega))
      (evalB_lit (by omega))
      (show Bop.sub.apply (N - i) 1 < B by rw [Bop.apply_sub]; omega)
    rwa [Bop.apply_sub] at h
  have hrra : (vstar : ℕ) < (σs.arrs ra).length := by
    have := hPs.hraL
    omega
  set σ₂ := σs.setArr ra (vstar : ℕ) (N - i - 1) with hσ₂
  have h2ra : σ₂.arrs ra = (σs.arrs ra).set (vstar : ℕ) (N - i - 1) := by
    rw [hσ₂, arrs_setArr, if_pos rfl]
  have h2arr : ∀ b, b ≠ ra → σ₂.arrs b = σs.arrs b := fun b hb => by
    rw [hσ₂, arrs_setArr, if_neg hb]
  have h2rc : σ₂.vars rc = N - i := by rw [hσ₂, vars_setArr, hrcs]
  -- 5. decrement the counter
  have hevrc : (Expr.sub (.var rc) (.lit 1)).evalB B σ₂
      = some (N - i - 1) := by
    have h := evalB_bin (op := .sub) (evB_var h2rc (by omega))
      (evalB_lit (by omega))
      (show Bop.sub.apply (N - i) 1 < B by rw [Bop.apply_sub]; omega)
    rwa [Bop.apply_sub] at h
  set σ₃ := σ₂.setVar rc (N - i - 1) with hσ₃
  have h3arr : ∀ b, b ≠ ra → σ₃.arrs b = σs.arrs b := fun b hb => by
    rw [hσ₃, arrs_setVar, h2arr b hb]
  have h3ra : σ₃.arrs ra = (σs.arrs ra).set (vstar : ℕ) (N - i - 1) := by
    rw [hσ₃, arrs_setVar, h2ra]
  have h3rc : σ₃.vars rc = N - i - 1 := by rw [hσ₃, vars_setVar, if_pos rfl]
  have h3vv : σ₃.vars vv = (vstar : ℕ) := by
    rw [hσ₃, vars_setVar, if_neg v_r, hσ₂, vars_setArr, ← husv]
    exact hvvs
  have h3nN : σ₃.vars nNm = N := by
    rw [hσ₃, vars_setVar, if_neg n_r, hσ₂, vars_setArr, hPs.hnN]
  have h3hsv : σ₃.vars hsv = σs.vars hsv := by
    rw [hσ₃, vars_setVar, if_neg s_r, hσ₂, vars_setArr]
  -- the heap and cells ride across the two writes
  have hH₃ : HeapSt hp hsv hn₁ fh₁ σ₃ :=
    hPs.hheap.of_eq (h3arr hp A_pr) h3hsv
  have hcell₃ : ∀ u : Fin N, (σ₃.arrs dg).getD (u : ℕ) 0
      = (σs.arrs dg).getD (u : ℕ) 0 := fun u => by
    rw [h3arr dg (Ne.symm A_rd)]
  -- 6. consume the pinned entry
  have hn₁pos : 0 < hn₁ := hPs.hn_pos hne
  have hn₁le' : hn₁ ≤ N + nsOf F := by
    have := hPs.hsize
    omega
  have hfB₁ : ∀ t, t < hn₁ → fh₁ t < B := by
    intro t ht
    have := hPs.fh_lt ht
    omega
  have hnB₁ : 2 * hn₁ + 2 < B := by
    have := hPs.hsize
    omega
  obtain ⟨σ₄, hrunp, ⟨g₁, hH₄, hcont₄⟩, hparr₄, hpvar₄, hplen₄⟩ :=
    (heapPop_spec hp hsv tv xv yv s_t s_x s_y t_x t_y x_y hnB₁ hn₁pos
      hfB₁).run hH₃
  have h4vv : σ₄.vars vv = (vstar : ℕ) := by
    rw [hpvar₄ vv (Ne.symm s_v) (Ne.symm t_v) (Ne.symm x_v) (Ne.symm y_v), h3vv]
  have h4nN : σ₄.vars nNm = N := by
    rw [hpvar₄ nNm n_s n_t n_x n_y, h3nN]
  have h4rc : σ₄.vars rc = N - i - 1 := by
    rw [hpvar₄ rc (Ne.symm s_r) (Ne.symm t_r) (Ne.symm x_r) (Ne.symm y_r), h3rc]
  have h4dg : σ₄.arrs dg = σs.arrs dg := by
    rw [hparr₄ dg (Ne.symm A_pd), h3arr dg (Ne.symm A_rd)]
  have h4ao : σ₄.arrs ao = aoL := by
    rw [hparr₄ ao (Ne.symm A_pa), h3arr ao (Ne.symm A_ra), hPs.hao]
  have h4aj : σ₄.arrs aj = ajL := by
    rw [hparr₄ aj (Ne.symm A_pj), h3arr aj (Ne.symm A_rj), hPs.haj]
  have h4ra : σ₄.arrs ra = (σs.arrs ra).set (vstar : ℕ) (N - i - 1) := by
    rw [hparr₄ ra (Ne.symm A_pr), h3ra]
  -- the pinned entry's key, in the choice's own terms
  have hkey₄ : fh₁ 0 = dstar * N + (vstar : ℕ) := by
    rw [hkeys, hdsd, husv]
  -- the degree cell of the choice
  have hcellv : (σ₄.arrs dg).getD ((vstar : ℕ)) 0 = dstar := by
    rw [h4dg, ← husv]
    rw [← hdsd]
    exact hcells
  -- shared membership bundles
  have hvv_row : vv ∉ ([wv, xv, kv, iv, hsv, tv, yv] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨v_w, Ne.symm x_v, Ne.symm k_v, v_i, Ne.symm s_v, Ne.symm t_v,
      Ne.symm y_v⟩
  have hnN_row : nNm ∉ ([wv, xv, kv, iv, hsv, tv, yv] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨n_w, n_x, n_k, n_i, n_s, n_t, n_y⟩
  have hrc_row : rc ∉ ([wv, xv, kv, iv, hsv, tv, yv] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨r_w, Ne.symm x_r, Ne.symm k_r, Ne.symm i_r, Ne.symm s_r,
      Ne.symm t_r, Ne.symm y_r⟩
  -- the post-consumption heap clauses, shared by both branches
  have hwit₄ : ∀ u ∈ live.erase vstar, (hMul (hn₁ - 1) g₁).count
      ((nbrsIn F live u).card * N + (u : ℕ)) = 1 := by
    intro u hu
    obtain ⟨hune, humem⟩ := Finset.mem_erase.mp hu
    rw [hcont₄, hkey₄]
    have hne' : (nbrsIn F live u).card * N + (u : ℕ)
        ≠ dstar * N + (vstar : ℕ) := by
      intro hc
      obtain ⟨-, huu⟩ := key_inj u.isLt vstar.isLt hc
      exact hune (Fin.ext huu)
    rw [Multiset.count_erase_of_ne hne']
    exact hPs.hwit u humem
  have hlow₄ : ∀ k ∈ hMul (hn₁ - 1) g₁, ∃ (d : ℕ) (u' : Fin N),
      k = d * N + (u' : ℕ) ∧ d < N ∧
      (u' ∈ live.erase vstar → (nbrsIn F live u').card ≤ d) ∧
      (u' ∉ live.erase vstar → 1 ≤ d) := by
    intro k hk
    rw [hcont₄] at hk
    obtain ⟨d, u', hk', hdN, hbr1, hbr2⟩ :=
      hPs.hlow k (Multiset.mem_of_mem_erase hk)
    refine ⟨d, u', hk', hdN, ?_, ?_⟩
    · intro hu'
      exact hbr1 (Finset.mem_erase.mp hu').2
    · intro hu'
      by_cases huv : u' = vstar
      · subst huv
        have hd' : dstar ≤ d := by
          rw [hdstar]
          exact hbr1 (minDegVert_mem F live hne)
        rcases Nat.eq_zero_or_pos dstar with hd0 | hdpos
        · by_contra hd1
          have hdz : d = 0 := by omega
          subst hdz
          rw [hk', hkey₄, hd0] at hk
          have hcnt := hPs.hwit vstar (minDegVert_mem F live hne)
          rw [← hdstar, hd0] at hcnt
          have hpos := Multiset.count_pos.mpr hk
          rw [Multiset.count_erase_self] at hpos
          omega
        · omega
      · exact hbr2 (fun hc => hu' (Finset.mem_erase.mpr ⟨huv, hc⟩))
  -- the guard on the choice's degree
  have hdgLen₄ : N ≤ (σ₄.arrs dg).length := by
    rw [h4dg]
    exact hPs.hdgL
  have hevg : (Cond.lt (.lit 0) (.get dg (.var vv))).evalB B σ₄
      = some (decide (0 < dstar)) := by
    refine evalB_condLt (evalB_lit (by omega)) ?_
    refine evB_get (evB_var h4vv (by omega)) (by omega) hcellv (by omega)
  -- the next live set
  have hlive' : peelLive F (i + 1) = live.erase vstar := peelLive_succ F hne
  have hvsmem : vstar ∈ live := minDegVert_mem F live hne
  have hrankv : mdRank F vstar = N - i - 1 := mdRank_pick F hiN' hne
  -- the degree bridge into the erased set
  have hdeg' : ∀ u : Fin N, u ∈ live → u ≠ vstar →
      (nbrsIn F (live.erase vstar) u).card
        = (nbrsIn F live u).card
          - (if u ∈ nbrsIn F live vstar then 1 else 0) :=
    fun u hu _ => card_nbrsIn_erase hu hvsmem
  -- the sums at the entry of the two branches
  have hSs : dgSum dg N σ₄ = dgSum dg N σs := by
    refine dgSum_congr ?_
    rw [h4dg]
  have hSσ : dgSum dg N σs = dgSum dg N σ := by
    refine dgSum_congr ?_
    rw [hsarrs dg (Ne.symm A_pd), hcarrs dg]
  have hTs : scanPot ao dg N σ₄ = scanPot ao dg N σ := by
    refine scanPot_congr ?_ ?_
    · rw [hparr₄ ao (Ne.symm A_pa), h3arr ao (Ne.symm A_ra),
        hsarrs ao (Ne.symm A_pa), hcarrs ao]
    · rw [h4dg, hsarrs dg (Ne.symm A_pd), hcarrs dg]
  have hhsσ : σ.vars hsv = hn₀ := hP₀.hheap.size
  have hhs₄ : σ₄.vars hsv = hn₁ - 1 := hH₄.size
  by_cases hdz : 0 < dstar
  · -- the live choice has neighbours: scan its base row
    have hcT : (Cond.lt (.lit 0) (.get dg (.var vv))).evalB B σ₄
        = some true := by
      rw [hevg, decide_eq_true hdz]
    have heviv : (Expr.get ao (.var vv)).evalB B σ₄
        = some (offF (vstar : ℕ)) := by
      refine evB_get (evB_var h4vv (by omega)) ?_ ?_ ?_
      · rw [h4ao]
        omega
      · rw [h4ao]
        exact hoffF (vstar : ℕ) (by omega)
      · have := hoffN (vstar : ℕ) (by omega)
        omega
    set σ₅ := σ₄.setVar iv (offF (vstar : ℕ)) with hσ₅
    have h5arr : ∀ b, σ₅.arrs b = σ₄.arrs b := fun b => by
      rw [hσ₅, arrs_setVar]
    have h5iv : σ₅.vars iv = offF (vstar : ℕ) := by
      rw [hσ₅, vars_setVar, if_pos rfl]
    have h5vv : σ₅.vars vv = (vstar : ℕ) := by
      rw [hσ₅, vars_setVar, if_neg v_i, h4vv]
    have h5rc : σ₅.vars rc = N - i - 1 := by
      rw [hσ₅, vars_setVar, if_neg (Ne.symm i_r), h4rc]
    -- the scan's entry state
    have hR₅ : RowSt F nNm ao aj dg hp hsv aoL ajL live vstar (hn₁ - 1) g₁
        ∅ σ₅ := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h5arr ao, h4ao]
      · rw [h5arr aj, h4aj]
      · rw [hσ₅, vars_setVar, if_neg n_i, h4nN]
      · rw [h5arr dg]
        exact hdgLen₄
      · rw [h5arr hp, hplen₄ hp, h3arr hp A_pr]
        exact hPs.hhpL
      · intro u
        rw [h5arr dg, h4dg, hPs.hdg u]
        rcases Finset.decidableMem u live with hd | hd
        · rw [if_neg hd, if_neg hd]
        · rw [if_pos hd, if_pos hd, if_neg (Finset.notMem_empty u),
            Nat.sub_zero]
      · exact hH₄.of_eq (h5arr hp) (by
          rw [hσ₅, vars_setVar, if_neg s_i])
      · intro u hu
        rw [h5arr dg, h4dg]
        have hcell : (σs.arrs dg).getD (u : ℕ) 0 = (nbrsIn F live u).card := by
          rw [hPs.hdg u, if_pos (Finset.mem_erase.mp hu).2]
        rw [hcell]
        exact hwit₄ u hu
      · intro k hk
        obtain ⟨d, u', hk', hdN, hbr1, hbr2⟩ := hlow₄ k hk
        refine ⟨d, u', hk', hdN, ?_, hbr2⟩
        intro hu'
        rw [h5arr dg, h4dg, hPs.hdg u', if_pos (Finset.mem_erase.mp hu').2]
        exact hbr1 hu'
      · have h1 : dgSum dg N σ₅ = dgSum dg N σs := by
          refine dgSum_congr ?_
          rw [h5arr dg, h4dg]
        have h2 : dgSum dg N σs = ∑ t ∈ Finset.range N,
            (σs.arrs dg).getD t 0 := rfl
        rw [h1]
        have := hPs.hsize
        simp only [Finset.card_empty]
        omega
    obtain ⟨σ₆, K₆, hn₃, g₂, hrun₆, hK₆, hR₆, hhn₃, hSle₆, hvf₆, haf₆,
      hlf₆⟩ := row_run s_t s_x s_y t_x t_y x_y hnN_row hvv_row
      (Ne.symm x_w) (Ne.symm k_w) (Ne.symm i_w) (Ne.symm s_w) (Ne.symm t_w)
      (Ne.symm y_w) (Ne.symm k_i) (Ne.symm x_i) (Ne.symm s_i) (Ne.symm t_i)
      (Ne.symm y_i) (Ne.symm s_k) (Ne.symm t_k) (Ne.symm x_k) (Ne.symm y_k)
      A_da A_dj (Ne.symm A_pa) (Ne.symm A_pj) (Ne.symm A_pd) hB hrow hrowInj
      hrowCom hoffF hoff0 hoffStep haoLen hajLen hvsmem hR₅ h5iv h5vv
    -- kill the choice's cell
    have h6vv : σ₆.vars vv = (vstar : ℕ) := by
      rw [hvf₆ vv hvv_row, h5vv]
    have h6dgL : (vstar : ℕ) < (σ₆.arrs dg).length := by
      rw [hlf₆ dg, h5arr dg]
      omega
    have hevzi : (Expr.var vv).evalB B σ₆ = some ((vstar : ℕ)) :=
      evB_var h6vv (by omega)
    set σ₇ := σ₆.setArr dg (vstar : ℕ) 0 with hσ₇
    have h7dg : σ₇.arrs dg = (σ₆.arrs dg).set (vstar : ℕ) 0 := by
      rw [hσ₇, arrs_setArr, if_pos rfl]
    have h7arr : ∀ b, b ≠ dg → σ₇.arrs b = σ₆.arrs b := fun b hb => by
      rw [hσ₇, arrs_setArr, if_neg hb]
    have h7vars : ∀ y, σ₇.vars y = σ₆.vars y := fun y => by
      rw [hσ₇, vars_setArr]
    -- the full-scan cell values
    have hvsnb : vstar ∉ nbrsIn F live vstar := by
      intro hc
      exact F.irrefl (mem_nbrsIn.mp hc).2
    have hcell₆ : ∀ u : Fin N, (σ₆.arrs dg).getD (u : ℕ) 0
        = if u ∈ live then (nbrsIn F live u).card
            - (if u ∈ nbrsIn F live vstar then 1 else 0) else 0 :=
      fun u => hR₆.hdg u
    have hcell₆v : (σ₆.arrs dg).getD ((vstar : ℕ)) 0 = dstar := by
      rw [hcell₆ vstar, if_pos hvsmem, if_neg hvsnb, Nat.sub_zero, hdstar]
    -- the peel state at the shrunken live set
    have hP₇ : PeelSt F nNm ao aj dg ra hp hsv aoL ajL (live.erase vstar)
        hn₃ g₂ σ₇ := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h7arr ao (Ne.symm A_da), hR₆.hao]
      · rw [h7arr aj (Ne.symm A_dj), hR₆.haj]
      -- (continue)
      · rw [h7vars nNm, hvf₆ nNm hnN_row, hσ₅, vars_setVar, if_neg n_i, h4nN]
      · rw [h7dg, List.length_set, hlf₆ dg, h5arr dg]
        exact hdgLen₄
      · rw [h7arr ra A_rd, haf₆ ra A_rd (Ne.symm A_pr), h5arr ra,
          h4ra, List.length_set]
        exact hPs.hraL
      · rw [h7arr hp A_pd, hlf₆ hp, h5arr hp, hplen₄ hp, h3arr hp A_pr]
        exact hPs.hhpL
      · intro u
        rcases eq_or_ne u vstar with rfl | huv
        · rw [h7dg, getD_set_self (by rw [hlf₆ dg, h5arr dg]; omega),
            if_neg (Finset.notMem_erase vstar live)]
        · have huval : (u : ℕ) ≠ (vstar : ℕ) := fun hc => huv (Fin.ext hc)
          rw [h7dg, getD_set_ne huval, hcell₆ u]
          by_cases hul : u ∈ live
          · rw [if_pos hul, if_pos (Finset.mem_erase.mpr ⟨huv, hul⟩),
              hdeg' u hul huv]
          · rw [if_neg hul, if_neg (fun hc => hul (Finset.mem_erase.mp hc).2)]
      · intro u hu
        rcases eq_or_ne u vstar with rfl | huv
        · rw [h7arr ra A_rd, haf₆ ra A_rd (Ne.symm A_pr), h5arr ra, h4ra,
            getD_set_self hrra, hrankv]
        · have hulive : u ∉ live := fun hc =>
            hu (Finset.mem_erase.mpr ⟨huv, hc⟩)
          have huval : (u : ℕ) ≠ (vstar : ℕ) := fun hc => huv (Fin.ext hc)
          rw [h7arr ra A_rd, haf₆ ra A_rd (Ne.symm A_pr), h5arr ra,
            h4ra, getD_set_ne huval]
          exact hPs.hra u hulive
      · exact hR₆.hheap.of_eq (h7arr hp A_pd) (h7vars hsv)
      · intro u hu
        have hcellu : (σ₇.arrs dg).getD (u : ℕ) 0
            = (nbrsIn F (live.erase vstar) u).card := by
          have huv := (Finset.mem_erase.mp hu).1
          have hul := (Finset.mem_erase.mp hu).2
          have huval : (u : ℕ) ≠ (vstar : ℕ) := fun hc => huv (Fin.ext hc)
          rw [h7dg, getD_set_ne huval, hcell₆ u, if_pos hul,
            hdeg' u hul huv]
        have hwit₆ := hR₆.hwit u hu
        rw [hcell₆ u, if_pos (Finset.mem_erase.mp hu).2,
          ← hdeg' u (Finset.mem_erase.mp hu).2 (Finset.mem_erase.mp hu).1]
          at hwit₆
        exact hwit₆
      · intro k hk
        obtain ⟨d, u', hk', hdN, hbr1, hbr2⟩ := hR₆.hlow k hk
        refine ⟨d, u', hk', hdN, ?_, hbr2⟩
        intro hu'
        have hbr := hbr1 hu'
        rw [hcell₆ u', if_pos (Finset.mem_erase.mp hu').2,
          ← hdeg' u' (Finset.mem_erase.mp hu').2 (Finset.mem_erase.mp hu').1]
          at hbr
        exact hbr
      · have hsum := sum_getD_set (σ₆.arrs dg) (j := (vstar : ℕ)) N 0
          (by omega) h6dgL
        rw [hcell₆v] at hsum
        have h7S : dgSum dg N σ₇ = ∑ t ∈ Finset.range N,
            ((σ₆.arrs dg).set (vstar : ℕ) 0).getD t 0 := by
          rw [dgSum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [h7dg]
        have h6size := hR₆.hsize
        rw [← hdstar] at h6size
        have h6S : dgSum dg N σ₆ = ∑ t ∈ Finset.range N,
            (σ₆.arrs dg).getD t 0 := rfl
        have h7S' : dgSum dg N σ₇ = ∑ t ∈ Finset.range N,
            (σ₇.arrs dg).getD t 0 := rfl
        omega
    -- the sums after the kill
    have hsum₇ := sum_getD_set (σ₆.arrs dg) (j := (vstar : ℕ)) N 0
      (by omega) h6dgL
    rw [hcell₆v] at hsum₇
    have h7S : dgSum dg N σ₇ = ∑ t ∈ Finset.range N,
        ((σ₆.arrs dg).set (vstar : ℕ) 0).getD t 0 := by
      rw [dgSum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [h7dg]
    have h6S : dgSum dg N σ₆ = ∑ t ∈ Finset.range N,
        (σ₆.arrs dg).getD t 0 := rfl
    have hS₅ : dgSum dg N σ₅ = dgSum dg N σ₄ := by
      refine dgSum_congr ?_
      rw [h5arr dg]
    -- the scan potential after the kill
    have hT₇ := scanPot_set ao dg (N := N) σ₆ (j := (vstar : ℕ)) (v := 0)
      (by omega) h6dgL (Ne.symm A_da)
    rw [← hσ₇] at hT₇
    rw [hcell₆v, if_pos hdz, if_neg (by omega : ¬ (0:ℕ) < 0)] at hT₇
    have hwidth : (σ₆.arrs ao).getD ((vstar : ℕ) + 1) 0
        - (σ₆.arrs ao).getD ((vstar : ℕ)) 0 = baseDeg F (vstar : ℕ) := by
      rw [hR₆.hao, hoffF ((vstar : ℕ) + 1) (by omega),
        hoffF (vstar : ℕ) (by omega), hoffStep vstar, ← baseDeg_eq]
      omega
    rw [hwidth] at hT₇
    have hT₆₅ : scanPot ao dg N σ₆ ≤ scanPot ao dg N σ₅ := by
      refine scanPot_mono (haf₆ ao (Ne.symm A_da) (Ne.symm A_pa)) ?_
      intro t ht
      have hc₆ := hcell₆ ⟨t, ht⟩
      have hc₅ : (σ₅.arrs dg).getD ((⟨t, ht⟩ : Fin N) : ℕ) 0
          = if (⟨t, ht⟩ : Fin N) ∈ live
            then (nbrsIn F live ⟨t, ht⟩).card else 0 := by
        rw [h5arr dg, h4dg, hPs.hdg ⟨t, ht⟩]
      show (σ₆.arrs dg).getD ((⟨t, ht⟩ : Fin N) : ℕ) 0
        ≤ (σ₅.arrs dg).getD ((⟨t, ht⟩ : Fin N) : ℕ) 0
      rw [hc₆, hc₅]
      split
      · split <;> omega
      · omega
    have hT₅ : scanPot ao dg N σ₅ = scanPot ao dg N σ₄ := by
      refine scanPot_congr ?_ ?_ <;> rw [h5arr]
    -- the final scalar cells
    have h7hs : σ₇.vars hsv = hn₃ := by
      rw [h7vars hsv]
      exact hR₆.hheap.size
    have h7rc : σ₇.vars rc = N - i - 1 := by
      rw [h7vars rc, hvf₆ rc hrc_row, h5rc]
    -- the round, assembled
    refine ⟨σ₇, _, Run.seq hrunc (Run.seq hruns (Run.seq
      (Run.store hevrai hevrav hrra) (Run.seq (Run.assign hevrc)
        (Run.seq hrunp (Run.seq (Run.ite_true hcT (Run.seq
          (Run.assign heviv) hrun₆))
          (Run.store hevzi (evalB_lit (show (0:ℕ) < B by omega))
            h6dgL)))))), ?_, ?_⟩
    · refine ⟨i + 1, hn₃, g₂, by omega, ?_, ?_⟩
      · rw [h7rc]
        omega
      · rw [hlive']
        exact hP₇
    · -- the ledger
      rw [peelPot, peelPot, h7hs, h7rc, hhsσ, hrc₀]
      have hlog₁ : Nat.log 2 (hn₁ + 1) ≤ Nat.log 2 (N + nsOf F + 1) :=
        Nat.log_mono_right (by omega)
      have hhn₃' : hn₃ + 1 = hn₁ + dstar := by
        rw [hhn₃, ← hdstar]
        omega
      have e1 : (56 * Nat.log 2 (N + nsOf F + 1) + 44) * hn₃
            + (56 * Nat.log 2 (N + nsOf F + 1) + 44)
          = (56 * Nat.log 2 (N + nsOf F + 1) + 44) * hn₁
            + (56 * Nat.log 2 (N + nsOf F + 1) + 44) * dstar := by
        calc (56 * Nat.log 2 (N + nsOf F + 1) + 44) * hn₃
              + (56 * Nat.log 2 (N + nsOf F + 1) + 44)
            = (56 * Nat.log 2 (N + nsOf F + 1) + 44) * (hn₃ + 1) := by ring
          _ = (56 * Nat.log 2 (N + nsOf F + 1) + 44) * (hn₁ + dstar) := by
              rw [hhn₃']
          _ = _ := by ring
      have hSdrop : dgSum dg N σ₇ + dstar + dstar ≤ dgSum dg N σ := by
        have h1 : dgSum dg N σ₆ + dstar ≤ dgSum dg N σ₅ := by
          have := hSle₆
          rw [← hdstar] at this
          omega
        omega
      have e2 : (56 * Nat.log 2 (N + nsOf F + 1) + 44)
            * (dgSum dg N σ₇ + dstar + dstar)
          ≤ (56 * Nat.log 2 (N + nsOf F + 1) + 44) * dgSum dg N σ :=
        Nat.mul_le_mul_left _ hSdrop
      have e2' : (56 * Nat.log 2 (N + nsOf F + 1) + 44)
            * (dgSum dg N σ₇ + dstar + dstar)
          = (56 * Nat.log 2 (N + nsOf F + 1) + 44) * dgSum dg N σ₇
            + (56 * Nat.log 2 (N + nsOf F + 1) + 44) * dstar
            + (56 * Nat.log 2 (N + nsOf F + 1) + 44) * dstar := by ring
      have hTdrop : scanPot ao dg N σ₇ + baseDeg F (vstar : ℕ)
          ≤ scanPot ao dg N σ := by
        rw [← hTs, ← hT₅]
        omega
      have e3 : (28 * Nat.log 2 (N + nsOf F + 1) + 46)
            * (scanPot ao dg N σ₇ + baseDeg F (vstar : ℕ))
          ≤ (28 * Nat.log 2 (N + nsOf F + 1) + 46) * scanPot ao dg N σ :=
        Nat.mul_le_mul_left _ hTdrop
      have e3' : (28 * Nat.log 2 (N + nsOf F + 1) + 46)
            * (scanPot ao dg N σ₇ + baseDeg F (vstar : ℕ))
          = (28 * Nat.log 2 (N + nsOf F + 1) + 46) * scanPot ao dg N σ₇
            + (28 * Nat.log 2 (N + nsOf F + 1) + 46)
              * baseDeg F (vstar : ℕ) := by ring
      have e4 : (56 * Nat.log 2 (N + nsOf F + 1) + 44) * 1
          ≤ (56 * Nat.log 2 (N + nsOf F + 1) + 44) * dstar :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_one] at e4
      simp only [Expr.size, Cond.size]
      omega
  · -- the choice is isolated: no scan, just the kill
    have hd0 : dstar = 0 := by omega
    have hcF : (Cond.lt (.lit 0) (.get dg (.var vv))).evalB B σ₄
        = some false := by
      rw [hevg, decide_eq_false hdz]
    have hnbem : nbrsIn F live vstar = ∅ := by
      rw [← Finset.card_eq_zero, ← hdstar]
      exact hd0
    have hdeg0 : ∀ u : Fin N, u ∈ live → u ≠ vstar →
        (nbrsIn F (live.erase vstar) u).card = (nbrsIn F live u).card := by
      intro u hu huv
      rw [hdeg' u hu huv, hnbem, if_neg (Finset.notMem_empty u),
        Nat.sub_zero]
    have hvdgL : (vstar : ℕ) < (σ₄.arrs dg).length := by omega
    have hevzi : (Expr.var vv).evalB B σ₄ = some ((vstar : ℕ)) :=
      evB_var h4vv (by omega)
    set σ₇ := σ₄.setArr dg (vstar : ℕ) 0 with hσ₇
    have h7dg : σ₇.arrs dg = (σ₄.arrs dg).set (vstar : ℕ) 0 := by
      rw [hσ₇, arrs_setArr, if_pos rfl]
    have h7arr : ∀ b, b ≠ dg → σ₇.arrs b = σ₄.arrs b := fun b hb => by
      rw [hσ₇, arrs_setArr, if_neg hb]
    have h7vars : ∀ y, σ₇.vars y = σ₄.vars y := fun y => by
      rw [hσ₇, vars_setArr]
    have hcell₄ : ∀ u : Fin N, (σ₄.arrs dg).getD (u : ℕ) 0
        = if u ∈ live then (nbrsIn F live u).card else 0 := by
      intro u
      rw [h4dg]
      exact hPs.hdg u
    -- the peel state at the shrunken live set
    have hP₇ : PeelSt F nNm ao aj dg ra hp hsv aoL ajL (live.erase vstar)
        (hn₁ - 1) g₁ σ₇ := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h7arr ao (Ne.symm A_da), h4ao]
      · rw [h7arr aj (Ne.symm A_dj), h4aj]
      · rw [h7vars nNm, h4nN]
      · rw [h7dg, List.length_set]
        exact hdgLen₄
      · rw [h7arr ra A_rd, h4ra, List.length_set]
        exact hPs.hraL
      · rw [h7arr hp A_pd, hplen₄ hp, h3arr hp A_pr]
        exact hPs.hhpL
      · intro u
        rcases eq_or_ne u vstar with rfl | huv
        · rw [h7dg, getD_set_self hvdgL,
            if_neg (Finset.notMem_erase vstar live)]
        · have huval : (u : ℕ) ≠ (vstar : ℕ) := fun hc => huv (Fin.ext hc)
          rw [h7dg, getD_set_ne huval, hcell₄ u]
          by_cases hul : u ∈ live
          · rw [if_pos hul, if_pos (Finset.mem_erase.mpr ⟨huv, hul⟩),
              hdeg0 u hul huv]
          · rw [if_neg hul, if_neg (fun hc => hul (Finset.mem_erase.mp hc).2)]
      · intro u hu
        rcases eq_or_ne u vstar with rfl | huv
        · rw [h7arr ra A_rd, h4ra, getD_set_self hrra, hrankv]
        · have hulive : u ∉ live := fun hc =>
            hu (Finset.mem_erase.mpr ⟨huv, hc⟩)
          have huval : (u : ℕ) ≠ (vstar : ℕ) := fun hc => huv (Fin.ext hc)
          rw [h7arr ra A_rd, h4ra, getD_set_ne huval]
          exact hPs.hra u hulive
      · exact hH₄.of_eq (h7arr hp A_pd) (h7vars hsv)
      · intro u hu
        rw [hdeg0 u (Finset.mem_erase.mp hu).2 (Finset.mem_erase.mp hu).1]
        exact hwit₄ u hu
      · intro k hk
        obtain ⟨d, u', hk', hdN, hbr1, hbr2⟩ := hlow₄ k hk
        refine ⟨d, u', hk', hdN, ?_, hbr2⟩
        intro hu'
        rw [hdeg0 u' (Finset.mem_erase.mp hu').2 (Finset.mem_erase.mp hu').1]
        exact hbr1 hu'
      · have hsum := sum_getD_set (σ₄.arrs dg) (j := (vstar : ℕ)) N 0
          (by omega) hvdgL
        have hcv : (σ₄.arrs dg).getD ((vstar : ℕ)) 0 = 0 := by
          rw [hcellv, hd0]
        rw [hcv] at hsum
        have h7S : (∑ t ∈ Finset.range N, (σ₇.arrs dg).getD t 0)
            = ∑ t ∈ Finset.range N,
              ((σ₄.arrs dg).set (vstar : ℕ) 0).getD t 0 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [h7dg]
        have h4S : dgSum dg N σ₄ = ∑ t ∈ Finset.range N,
            (σ₄.arrs dg).getD t 0 := rfl
        have hsz := hPs.hsize
        have hSs' : dgSum dg N σ₄ = ∑ t ∈ Finset.range N,
            (σs.arrs dg).getD t 0 := by
          rw [hSs]
          rfl
        omega
    -- the sums are untouched
    have hsum₇ := sum_getD_set (σ₄.arrs dg) (j := (vstar : ℕ)) N 0
      (by omega) hvdgL
    have hcv : (σ₄.arrs dg).getD ((vstar : ℕ)) 0 = 0 := by
      rw [hcellv, hd0]
    rw [hcv] at hsum₇
    have hS₇ : dgSum dg N σ₇ = dgSum dg N σ := by
      have h7S : dgSum dg N σ₇ = ∑ t ∈ Finset.range N,
          ((σ₄.arrs dg).set (vstar : ℕ) 0).getD t 0 := by
        rw [dgSum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [h7dg]
      have h4S : dgSum dg N σ₄ = ∑ t ∈ Finset.range N,
          (σ₄.arrs dg).getD t 0 := rfl
      rw [← hSσ, ← hSs]
      omega
    have hT₇ := scanPot_set ao dg (N := N) σ₄ (j := (vstar : ℕ)) (v := 0)
      (by omega) hvdgL (Ne.symm A_da)
    rw [← hσ₇] at hT₇
    rw [hcv, if_neg (by omega : ¬ (0:ℕ) < 0)] at hT₇
    have hT₇' : scanPot ao dg N σ₇ = scanPot ao dg N σ := by
      rw [← hTs]
      omega
    have h7hs : σ₇.vars hsv = hn₁ - 1 := by
      rw [h7vars hsv, hhs₄]
    have h7rc : σ₇.vars rc = N - i - 1 := by
      rw [h7vars rc, h4rc]
    refine ⟨σ₇, _, Run.seq hrunc (Run.seq hruns (Run.seq
      (Run.store hevrai hevrav hrra) (Run.seq (Run.assign hevrc)
        (Run.seq hrunp (Run.seq (Run.ite_false hcF Run.skip)
          (Run.store hevzi (evalB_lit (show (0:ℕ) < B by omega))
            hvdgL)))))), ?_, ?_⟩
    · refine ⟨i + 1, hn₁ - 1, g₁, by omega, ?_, ?_⟩
      · rw [h7rc]
        omega
      · rw [hlive']
        exact hP₇
    · -- the ledger, with the scan absent
      rw [peelPot, peelPot, h7hs, h7rc, hhsσ, hrc₀]
      have hlog₁ : Nat.log 2 (hn₁ + 1) ≤ Nat.log 2 (N + nsOf F + 1) :=
        Nat.log_mono_right (by omega)
      have e1 : (56 * Nat.log 2 (N + nsOf F + 1) + 44) * (hn₁ - 1)
            + (56 * Nat.log 2 (N + nsOf F + 1) + 44)
          = (56 * Nat.log 2 (N + nsOf F + 1) + 44) * hn₁ := by
        calc (56 * Nat.log 2 (N + nsOf F + 1) + 44) * (hn₁ - 1)
              + (56 * Nat.log 2 (N + nsOf F + 1) + 44)
            = (56 * Nat.log 2 (N + nsOf F + 1) + 44) * ((hn₁ - 1) + 1) := by
              ring
          _ = _ := by rw [show hn₁ - 1 + 1 = hn₁ by omega]
      have e2 : (56 * Nat.log 2 (N + nsOf F + 1) + 44) * dgSum dg N σ₇
          = (56 * Nat.log 2 (N + nsOf F + 1) + 44) * dgSum dg N σ := by
        rw [hS₇]
      have e3 : (28 * Nat.log 2 (N + nsOf F + 1) + 46) * scanPot ao dg N σ₇
          = (28 * Nat.log 2 (N + nsOf F + 1) + 46) * scanPot ao dg N σ := by
        rw [hT₇']
      simp only [Expr.size, Cond.size]
      omega

end Round

/-! ### §2g The core, assembled -/

section Core

variable {B N : ℕ} {F : SimpleGraph (Fin N)}
variable {nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv : String}

set_option maxHeartbeats 1600000 in
/-- **The parametric peel core** — the deliverable wave w62 re-runs on
other graphs. From the deletable adjacency region of `F` at the empty
deleted set (the offsets and rows are read, the mates never touched),
the carrier size in the named cell, and room for the rank array and
the heap, `mdPeelCom` leaves the rank array holding `mdRank F` on the
whole carrier. The region is consumed (`dg` is zeroed); every array
outside `{hp, dg, ra}` and every scalar outside the twelve working
cells is untouched, and no array changes length. Budget
`KmdPeel N (nsOf F)`, quasi-linear in the carrier plus the degree
sum. -/
theorem mdPeelCore_spec (mt : String)
    (hnods : ([nNm, hsv, tv, xv, yv, kv, dv, vv, zv, iv, rc, wv] :
      List String).Nodup)
    (harr : ([hp, ra, dg, ao, aj] : List String).Nodup)
    (hB : N * N + 4 * N + 4 ≤ B) :
    Spec B
      (fun σ => DelAdjSt ao aj dg mt F ∅ σ ∧ σ.vars nNm = N ∧
        N ≤ (σ.arrs ra).length ∧ N * N + N ≤ (σ.arrs hp).length)
      (mdPeelCom nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv)
      (fun σ σ' => (N ≤ (σ'.arrs ra).length ∧
          ∀ u : Fin N, (σ'.arrs ra).getD (u : ℕ) 0 = mdRank F u) ∧
        (∀ b, b ∉ ([hp, dg, ra] : List String) → σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ∉ ([hsv, tv, xv, yv, kv, dv, vv, zv, iv, rc, wv] :
          List String) → σ'.vars y = σ.vars y) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (KmdPeel N (nsOf F)) := by
  have hnods' := hnods
  have harr' := harr
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hnods' harr'
  obtain ⟨⟨n_s, n_t, n_x, n_y, n_k, n_d, n_v, n_z, n_i, n_r, n_w⟩,
    ⟨s_t, s_x, s_y, s_k, s_d, s_v, s_z, s_i, s_r, s_w⟩,
    ⟨t_x, t_y, t_k, t_d, t_v, t_z, t_i, t_r, t_w⟩,
    ⟨x_y, x_k, x_d, x_v, x_z, x_i, x_r, x_w⟩,
    ⟨y_k, y_d, y_v, y_z, y_i, y_r, y_w⟩,
    ⟨k_d, k_v, k_z, k_i, k_r, k_w⟩, ⟨d_v, d_z, d_i, d_r, d_w⟩,
    ⟨v_z, v_i, v_r, v_w⟩, ⟨z_i, z_r, z_w⟩, ⟨i_r, i_w⟩, r_w⟩ := hnods'
  obtain ⟨⟨A_pr, A_pd, A_pa, A_pj⟩, ⟨A_rd, A_ra, A_rj⟩, ⟨A_da, A_dj⟩,
    A_aj⟩ := harr'
  have hcore : Spec B
      (fun σ => DelAdjSt ao aj dg mt F ∅ σ ∧ σ.vars nNm = N ∧
        N ≤ (σ.arrs ra).length ∧ N * N + N ≤ (σ.arrs hp).length)
      (mdPeelCom nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv)
      (fun _ σ' => N ≤ (σ'.arrs ra).length ∧
        ∀ u : Fin N, (σ'.arrs ra).getD (u : ℕ) 0 = mdRank F u)
      (KmdPeel N (nsOf F)) := by
    refine Spec.of_exists ?_
    rintro σ₀ ⟨hDel, hnN₀, hraL₀, hhpL₀⟩
    obtain ⟨offF, hoff0, hoffStep, haoLen₀, haoRead, hajLen₀, hmtLen₀,
      hdgLen₀, -, hdgLive, hsound, hcomp⟩ := hDel
    set aoL := σ₀.arrs ao with haoL
    set ajL := σ₀.arrs aj with hajL
    -- the frozen row facts of the region at the empty deleted set
    have hoffN' : offF N = nsOf F := by
      rw [offF_eq_sum hoff0 hoffStep N le_rfl, nsOf]
    have hcell₀ : ∀ u : Fin N, (σ₀.arrs dg).getD (u : ℕ) 0
        = (nbrsIn F Finset.univ u).card := by
      intro u
      rw [hdgLive u (Set.notMem_empty u), Impl.deleteVerts_empty,
        card_nbrsIn_univ]
    have hcellBase : ∀ t, t < N → (σ₀.arrs dg).getD t 0 = baseDeg F t := by
      intro t ht
      have h := hdgLive (⟨t, ht⟩ : Fin N) (Set.notMem_empty _)
      rw [Impl.deleteVerts_empty] at h
      have h2 : baseDeg F t = (F.neighborSet (⟨t, ht⟩ : Fin N)).ncard := by
        rw [baseDeg, dif_pos ht]
      rw [h2]
      exact h
    have hrow : ∀ (u : Fin N) (t : ℕ), t < baseDeg F (u : ℕ) →
        ∃ w : Fin N, F.Adj u w ∧ ajL.getD (offF (u : ℕ) + t) 0 = (w : ℕ) := by
      intro u t ht
      have ht' : t < (σ₀.arrs dg).getD (u : ℕ) 0 := by
        rw [hcellBase (u : ℕ) u.isLt]
        exact ht
      obtain ⟨w, hadj, hval, -⟩ := hsound u (Set.notMem_empty u) t ht'
      rw [Impl.deleteVerts_empty] at hadj
      exact ⟨w, hadj, hval⟩
    have hrowCom : ∀ (u w : Fin N), F.Adj u w →
        ∃ t, t < baseDeg F (u : ℕ) ∧
          ajL.getD (offF (u : ℕ) + t) 0 = (w : ℕ) := by
      intro u w hadj
      have hadj' : (Lax12.UniformQuasiWideness.deleteVerts F ∅).Adj u w := by
        rw [Impl.deleteVerts_empty]
        exact hadj
      obtain ⟨t, ht, hval⟩ := hcomp u (Set.notMem_empty u) w hadj'
      rw [hcellBase (u : ℕ) u.isLt] at ht
      exact ⟨t, ht, hval⟩
    have hrowInj : ∀ u : Fin N,
        Set.InjOn (fun t => ajL.getD (offF (u : ℕ) + t) 0)
          {t | t < baseDeg F (u : ℕ)} := by
      intro u
      obtain ⟨offF', hoff0', hoffStep', hinj⟩ :=
        DelAdjSt.slot_injOn (ao := ao) (aj := aj) (dg := dg) (mt := mt)
          ⟨offF, hoff0, hoffStep, haoLen₀, haoRead, hajLen₀, hmtLen₀,
            hdgLen₀, fun v hv => absurd hv (Set.notMem_empty v), hdgLive,
            hsound, hcomp⟩ (Set.notMem_empty u)
      have hoffeq : offF' (u : ℕ) = offF (u : ℕ) :=
        offF_unique hoff0' hoff0 hoffStep' hoffStep (u : ℕ) (le_of_lt u.isLt)
      rw [hoffeq] at hinj
      have hset : {t | t < baseDeg F (u : ℕ)}
          = {t | t < (σ₀.arrs dg).getD (u : ℕ) 0} := by
        ext t
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hcellBase (u : ℕ) u.isLt]
      rw [hset]
      exact hinj
    have hoffRead : ∀ j', j' ≤ N → aoL.getD j' 0 = offF j' := haoRead
    have haoLen : N + 1 ≤ aoL.length := haoLen₀
    have hajLen : nsOf F ≤ ajL.length := by
      rw [← hoffN']
      exact hajLen₀
    have hnsq := nsOf_add_le F
    set L' := Nat.log 2 (N + nsOf F + 1) with hL'
    set keyAt : ℕ → ℕ := fun t => (σ₀.arrs dg).getD t 0 * N + t with hkeyAt
    have hkeyApp : ∀ t, keyAt t = (σ₀.arrs dg).getD t 0 * N + t :=
      fun _ => rfl
    have hkeyAtlt : ∀ t, t < N → keyAt t < N * N := by
      intro t ht
      have hc := hcellBase t ht
      have hb := baseDeg_lt F ht
      have h1 : keyAt t < ((σ₀.arrs dg).getD t 0 + 1) * N := by
        rw [hkeyApp t, Nat.succ_mul]
        omega
      have h2 : ((σ₀.arrs dg).getD t 0 + 1) * N ≤ N * N :=
        Nat.mul_le_mul_right N (by omega)
      omega
    set Iinit : Env → Prop := fun τ =>
      ∃ fh, τ.vars nNm = N ∧ τ.vars iv ≤ N ∧
        HeapSt hp hsv (τ.vars iv) fh τ ∧
        hMul (τ.vars iv) fh = (Multiset.range (τ.vars iv)).map keyAt ∧
        τ.arrs ao = σ₀.arrs ao ∧ τ.arrs aj = σ₀.arrs aj ∧
        τ.arrs dg = σ₀.arrs dg ∧ τ.arrs ra = σ₀.arrs ra ∧
        (∀ b, (τ.arrs b).length = (σ₀.arrs b).length) with hIinit
    have hinitBody : Spec B (fun τ => Iinit τ ∧ τ.vars iv < N)
        (initBody nNm dg hp hsv tv xv yv kv iv)
        (fun τ τ' => Iinit τ' ∧ τ'.vars iv = τ.vars iv + 1)
        (28 * L' + 24) := by
      refine Spec.of_exists ?_
      rintro τ ⟨⟨fh, hτnN, hτiv, hτH, hτM, hτao, hτaj, hτdg, hτra, hτlen⟩,
        hivN⟩
      have hcB : (τ.arrs dg).getD (τ.vars iv) 0 < N := by
        rw [hτdg, hcellBase (τ.vars iv) hivN]
        exact baseDeg_lt F hivN
      have hkeyτ : (τ.arrs dg).getD (τ.vars iv) 0 * N + τ.vars iv
          = keyAt (τ.vars iv) := by
        rw [hkeyAt, hτdg]
      have hkiB : keyAt (τ.vars iv) < N * N := hkeyAtlt (τ.vars iv) hivN
      have hevk : (Expr.add (.mul (.get dg (.var iv)) (.var nNm))
          (.var iv)).evalB B τ = some (keyAt (τ.vars iv)) := by
        have hg : (Expr.get dg (.var iv)).evalB B τ
            = some ((τ.arrs dg).getD (τ.vars iv) 0) := by
          refine evB_get (evB_var rfl (by omega)) ?_ rfl (by omega)
          rw [hτdg]
          omega
        have hm := evalB_bin (op := .mul) hg (evB_var hτnN (by omega))
          (show Bop.mul.apply ((τ.arrs dg).getD (τ.vars iv) 0) N < B by
            rw [Bop.apply_mul]
            have h1 : (τ.arrs dg).getD (τ.vars iv) 0 * N
                ≤ keyAt (τ.vars iv) := by
              rw [← hkeyτ]
              omega
            omega)
        rw [Bop.apply_mul] at hm
        have ha := evalB_bin (op := .add) hm (evB_var rfl (by omega))
          (show Bop.add.apply ((τ.arrs dg).getD (τ.vars iv) 0 * N)
              (τ.vars iv) < B by
            rw [Bop.apply_add, hkeyτ]
            omega)
        rwa [Bop.apply_add, hkeyτ] at ha
      set τ₁ := τ.setVar kv (keyAt (τ.vars iv)) with hτ₁
      have h1kv : τ₁.vars kv = keyAt (τ.vars iv) := by
        rw [hτ₁, vars_setVar, if_pos rfl]
      have h1arr : ∀ b, τ₁.arrs b = τ.arrs b := fun b => by
        rw [hτ₁, arrs_setVar]
      have hH₁ : HeapSt hp hsv (τ.vars iv) fh τ₁ :=
        hτH.of_eq (h1arr hp) (by rw [hτ₁, vars_setVar, if_neg s_k])
      have hfB : ∀ t, t < τ.vars iv → fh t < B := by
        intro t ht
        have hmem : fh t ∈ (Multiset.range (τ.vars iv)).map keyAt := by
          rw [← hτM]
          exact f_mem_hMul fh ht
        obtain ⟨t', ht', hval⟩ := Multiset.mem_map.mp hmem
        rw [← hval]
        have := hkeyAtlt t' (lt_of_lt_of_le (Multiset.mem_range.mp ht')
          (by omega))
        omega
      obtain ⟨σp, hrunp, ⟨g, hHp, hcont⟩, hparr, hpvar, hplen⟩ :=
        (heapPush_spec hp hsv tv xv yv s_t s_x s_y t_x t_y x_y kv
          (n := τ.vars iv) (k := keyAt (τ.vars iv)) (f := fh) (by omega)
          (by omega) hfB).run ⟨hH₁, h1kv, by
            rw [h1arr hp, hτlen hp]
            omega⟩
      have hpiv : σp.vars iv = τ.vars iv := by
        rw [hpvar iv (Ne.symm s_i) (Ne.symm t_i) (Ne.symm x_i)
          (Ne.symm y_i), hτ₁, vars_setVar, if_neg (Ne.symm k_i)]
      have hevinc : (Expr.add (.var iv) (.lit 1)).evalB B σp
          = some (τ.vars iv + 1) := by
        have h := evalB_bin (op := .add) (evB_var hpiv (by omega))
          (evalB_lit (by omega))
          (show Bop.add.apply (τ.vars iv) 1 < B by rw [Bop.apply_add]; omega)
        rwa [Bop.apply_add] at h
      set τ₂ := σp.setVar iv (τ.vars iv + 1) with hτ₂
      have h2iv : τ₂.vars iv = τ.vars iv + 1 := by
        rw [hτ₂, vars_setVar, if_pos rfl]
      refine ⟨τ₂, _, Run.seq (Run.assign hevk) (Run.seq hrunp
        (Run.assign hevinc)), ?_, ⟨⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        h2iv⟩⟩
      · have hlogi : Nat.log 2 (τ.vars iv + 1) ≤ L' := by
          rw [hL']
          exact Nat.log_mono_right (by omega)
        simp only [Expr.size, Cond.size]
        omega
      · rw [hτ₂, vars_setVar, if_neg n_i, hpvar nNm n_s n_t n_x n_y, hτ₁,
          vars_setVar, if_neg n_k, hτnN]
      · rw [h2iv]
        omega
      · rw [h2iv]
        exact hHp.of_eq (by rw [hτ₂, arrs_setVar])
          (by rw [hτ₂, vars_setVar, if_neg s_i])
      · rw [h2iv, hcont, hτM, Multiset.range_succ, Multiset.map_cons]
      · rw [hτ₂, arrs_setVar, hparr ao (Ne.symm A_pa), h1arr ao, hτao]
      · rw [hτ₂, arrs_setVar, hparr aj (Ne.symm A_pj), h1arr aj, hτaj]
      · rw [hτ₂, arrs_setVar, hparr dg (Ne.symm A_pd), h1arr dg, hτdg]
      · rw [hτ₂, arrs_setVar, hparr ra (Ne.symm A_pr), h1arr ra, hτra]
      · intro b
        rw [hτ₂, arrs_setVar, hplen b, h1arr b]
        exact hτlen b
    have hev0 : (Expr.lit 0).evalB B σ₀ = some 0 := evalB_lit (by omega)
    set σa := σ₀.setVar hsv 0 with hσa
    have hivv0 : (σa.setVar iv 0).vars iv = 0 := by
      rw [vars_setVar, if_pos rfl]
    have hIa : Iinit (σa.setVar iv 0) := by
      refine ⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [vars_setVar, if_neg n_i, hσa, vars_setVar, if_neg n_s, hnN₀]
      · rw [hivv0]
        omega
      · rw [hivv0]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [vars_setVar, if_neg s_i, hσa, vars_setVar, if_pos rfl]
        · exact Nat.zero_le _
        · intro t ht
          exact absurd ht (Nat.not_lt_zero t)
        · intro t h0 ht
          exact absurd ht (Nat.not_lt_zero t)
      · rw [hivv0]
        simp [hMul]
      · rw [arrs_setVar, hσa, arrs_setVar]
      · rw [arrs_setVar, hσa, arrs_setVar]
      · rw [arrs_setVar, hσa, arrs_setVar]
      · rw [arrs_setVar, hσa, arrs_setVar]
      · intro b
        rw [arrs_setVar, hσa, arrs_setVar]
    have hIiv : ∀ τ, Iinit τ → τ.vars iv ≤ N := by
      rintro τ ⟨fh, -, h, -⟩
      exact h
    have hInN : ∀ τ, Iinit τ → τ.vars nNm = N := by
      rintro τ ⟨fh, h, -⟩
      exact h
    obtain ⟨σb, hrunI, hIb, hivb⟩ :=
      (Spec.forRangeZero iv nNm Iinit N (28 * L' + 24) (by omega) hIiv hInN
        hinitBody).run hIa
    obtain ⟨fhb, hbnN, -, hbH, hbM, hbao, hbaj, hbdg, hbra, hblen⟩ := hIb
    rw [hivb] at hbH hbM
    have hevrcN : (Expr.var nNm).evalB B σb = some N :=
      evB_var hbnN (by omega)
    set σc := σb.setVar rc N with hσc
    have hcarr : ∀ b, σc.arrs b = σb.arrs b := fun b => by
      rw [hσc, arrs_setVar]
    have hOc : OuterI F nNm ao aj dg ra hp hsv rc aoL ajL σc := by
      refine ⟨0, N, fhb, by omega, ?_, ?_⟩
      · rw [hσc, vars_setVar, if_pos rfl]
        omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hcarr ao, hbao]
        · rw [hcarr aj, hbaj]
        · rw [hσc, vars_setVar, if_neg n_r, hbnN]
        · rw [hcarr dg, hbdg]
          exact hdgLen₀
        · rw [hcarr ra, hbra]
          exact hraL₀
        · rw [hcarr hp, hblen hp]
          exact hhpL₀
        · intro u
          rw [hcarr dg, hbdg, if_pos (by
            rw [peelLive_zero]
            exact Finset.mem_univ u)]
          rw [peelLive_zero]
          exact hcell₀ u
        · intro u hu
          exact absurd (by
            rw [peelLive_zero]
            exact Finset.mem_univ u) hu
        · exact hbH.of_eq (hcarr hp) (by
            rw [hσc, vars_setVar, if_neg s_r])
        · intro u hu
          rw [hbM]
          have hnd : ((Multiset.range N).map keyAt).Nodup := by
            refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range N)
            intro t ht t' ht' heq
            rw [hkeyAt] at heq
            exact (key_inj (Multiset.mem_range.mp ht)
              (Multiset.mem_range.mp ht') heq).2
          have hcellu : keyAt (u : ℕ)
              = (nbrsIn F (peelLive F 0) u).card * N + (u : ℕ) := by
            rw [hkeyApp, peelLive_zero, hcell₀ u]
          have hmem : (nbrsIn F (peelLive F 0) u).card * N + (u : ℕ)
              ∈ (Multiset.range N).map keyAt := by
            refine Multiset.mem_map.mpr ⟨(u : ℕ),
              Multiset.mem_range.mpr u.isLt, ?_⟩
            rw [hcellu]
          exact Multiset.count_eq_one_of_mem hnd hmem
        · intro k hk
          rw [hbM] at hk
          obtain ⟨t, ht, hval⟩ := Multiset.mem_map.mp hk
          have htN := Multiset.mem_range.mp ht
          refine ⟨(σ₀.arrs dg).getD t 0, ⟨t, htN⟩, ?_, ?_, ?_, ?_⟩
          · rw [← hval, hkeyAt]
          · rw [hcellBase t htN]
            exact baseDeg_lt F htN
          · intro hmem
            rw [peelLive_zero]
            exact le_of_eq (hcell₀ ⟨t, htN⟩).symm
          · intro hdead
            exact absurd (by
              rw [peelLive_zero]
              exact Finset.mem_univ _) hdead
        · rw [hcarr dg, hbdg]
          have hsum : (∑ t ∈ Finset.range N, (σ₀.arrs dg).getD t 0)
              = nsOf F := by
            rw [nsOf]
            refine Finset.sum_congr rfl fun t ht => ?_
            exact hcellBase t (Finset.mem_range.mp ht)
          rw [hsum]
    have hstepO : ∀ τ, OuterI F nNm ao aj dg ra hp hsv rc aoL ajL τ →
        (Cond.lt (.lit 0) (.var rc)).evalB B τ = some true →
        ∃ τ' K, Run B
            (roundCom nNm ao aj dg ra hp hsv tv xv yv kv dv vv zv iv rc wv)
            τ τ' K ∧ OuterI F nNm ao aj dg ra hp hsv rc aoL ajL τ' ∧
          1 + (Cond.lt (.lit 0) (.var rc)).size + K
              + peelPot ao dg hsv rc N L' τ'
            ≤ peelPot ao dg hsv rc N L' τ := by
      intro τ hI hc
      obtain ⟨τ', K, h1, h2, h3⟩ := round_run hnods harr hB hrow hrowInj
        hrowCom hoffRead hoff0 hoffStep haoLen hajLen τ hI hc
      refine ⟨τ', K, h1, h2, ?_⟩
      rw [hL']
      simp only [Cond.size, Expr.size]
      omega
    have hdefO : ∀ τ, OuterI F nNm ao aj dg ra hp hsv rc aoL ajL τ →
        ∃ v, (Cond.lt (.lit 0) (.var rc)).evalB B τ = some v := by
      rintro τ ⟨i, hn, fh, hiN, hrcτ, -⟩
      exact ⟨_, evalB_condLt (evalB_lit (by omega))
        (evB_var hrcτ (by omega))⟩
    obtain ⟨σd, Kd, hrunO, hOd, hcondF, hpay⟩ :=
      Run.while_potential (B := B)
        (OuterI F nNm ao aj dg ra hp hsv rc aoL ajL)
        (peelPot ao dg hsv rc N L') hdefO hstepO hOc
    obtain ⟨id, hnd, fhd, hidN, hrcd, hPd⟩ := hOd
    have hrc0 : σd.vars rc = 0 := by
      have h2 := evalB_condLt (B := B) (evalB_lit (show (0:ℕ) < B by omega))
        (evB_var hrcd (by omega))
      rw [hcondF] at h2
      have h3 := of_decide_eq_false (Option.some.inj h2).symm
      omega
    have hidN' : id = N := by omega
    rw [hidN'] at hPd
    have hlast : peelLive F N = ∅ := peelLive_last F
    have hΦc : peelPot ao dg hsv rc N L' σc
        ≤ (56 * L' + 44) * N + (56 * L' + 44) * nsOf F
          + (28 * L' + 46) * nsOf F + 60 * N := by
      rw [peelPot]
      have h1 : σc.vars hsv = N := by
        rw [hσc, vars_setVar, if_neg s_r]
        exact hbH.size
      have h2 : σc.vars rc = N := by rw [hσc, vars_setVar, if_pos rfl]
      have h3 : dgSum dg N σc = nsOf F := by
        rw [dgSum]
        have h4 : ∀ t ∈ Finset.range N, (σc.arrs dg).getD t 0
            = baseDeg F t := by
          intro t ht
          rw [hcarr dg, hbdg]
          exact hcellBase t (Finset.mem_range.mp ht)
        rw [Finset.sum_congr rfl h4]
        rfl
      have h5 : scanPot ao dg N σc ≤ nsOf F := by
        refine scanPot_le (F := F) (offF := offF) ?_ hoff0 hoffStep
        intro j' hj'
        rw [hcarr ao, hbao]
        exact hoffRead j' hj'
      have h6 : (28 * L' + 46) * scanPot ao dg N σc
          ≤ (28 * L' + 46) * nsOf F := Nat.mul_le_mul_left _ h5
      rw [h1, h2, h3]
      omega
    refine ⟨σd, _, Run.seq (Run.assign hev0) (Run.seq hrunI
      (Run.seq (Run.assign hevrcN) hrunO)), ?_, ?_, ?_⟩
    · have hKd : Kd ≤ peelPot ao dg hsv rc N L' σc + 1 + 3 := by
        have hp' := hpay
        simp only [Cond.size, Expr.size] at hp'
        omega
      rw [KmdPeel]
      have e1 : (28 * L' + 24 + 4) * N = 28 * (L' * N) + 28 * N := by ring
      have e2 : (56 * L' + 44) * N = 56 * (L' * N) + 44 * N := by ring
      have e3 : (56 * L' + 44) * nsOf F = 56 * (L' * nsOf F)
          + 44 * nsOf F := by ring
      have e4 : (28 * L' + 46) * nsOf F = 28 * (L' * nsOf F)
          + 46 * nsOf F := by ring
      have e5 : 100 * (N + nsOf F) * (Nat.log 2 (N + nsOf F + 1) + 1)
          = 100 * (L' * N) + 100 * (L' * nsOf F) + 100 * N
            + 100 * nsOf F := by
        rw [hL']
        ring
      simp only [Expr.size, Cond.size]
      omega
    · rw [hlast] at hPd
      exact hPd.hraL
    · intro u
      rw [hlast] at hPd
      exact hPd.hra u (Finset.notMem_empty u)
  -- the frame wrap
  have h2 := (hcore.arrLengths).frame
  refine h2.post ?_
  rintro σ σ' - ⟨⟨hq, hlens⟩, hfv, hfa, -, -⟩
  refine ⟨hq, ?_, ?_, hlens⟩
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine hfa b ?_
    simp [mdPeelCom, initBody, roundCom, rowBody, chkCom, heapPushCom,
      heapPopCom, heapUpBody, heapDownBody, Com.warrs, hb1, hb2, hb3]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9, hy10, hy11⟩ := hy
    refine hfv y ?_
    simp [mdPeelCom, initBody, roundCom, rowBody, chkCom, heapPushCom,
      heapPopCom, heapUpBody, heapDownBody, Com.wvars, hy1, hy2, hy3, hy4,
      hy5, hy6, hy7, hy8, hy9, hy10, hy11]

end Core


/-! ## §3 The residual, instantiated -/

section Residual

/-- The peel's heap region at level `j`. Base length 4, like every
level-tagged family. -/
def mpHeap (j : ℕ) : String := lv "mp.h" j

/-- The peel's eleven scratch scalars at level `j`, in the core's
frame order. -/
def mpWrittenVars (j : ℕ) : List String :=
  [lv "mp.s" j, lv "mp.t" j, lv "mp.x" j, lv "mp.y" j, lv "mp.k" j,
    lv "mp.d" j, lv "mp.v" j, lv "mp.z" j, lv "mp.i" j, lv "mp.r" j,
    lv "mp.w" j]

/-- The arrays the peel writes at level `j`: the heap scratch, the
degree region (consumed) and the rank output. -/
def mpWrittenArrs (dgO ra : ℕ → String) (j : ℕ) : List String :=
  [mpHeap j, dgO j, ra j]

/-- **The peel scratch descriptor**: room for the rank output (`N`
cells) and the heap (`N² + N` cells), both against the level's
carrier cell — the only allocations the pass needs beyond the
ordering seam's own regions. -/
def mpSmp (ra : ℕ → String) (j : ℕ) (σ : Env) : Prop :=
  σ.vars (arenaNames j).nN ≤ (σ.arrs (ra j)).length ∧
    σ.vars (arenaNames j).nN * σ.vars (arenaNames j).nN
      + σ.vars (arenaNames j).nN ≤ (σ.arrs (mpHeap j)).length

/-- `mpSmp` transports along the carrier cell and the two lengths —
the shape a pass that writes neither proves from its frame data
(w62's augmentation leaf consumes this). -/
theorem mpSmp_of_eq {ra : ℕ → String} {j : ℕ} {σ σ' : Env}
    (h : mpSmp ra j σ)
    (hn : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN)
    (hra : (σ'.arrs (ra j)).length = (σ.arrs (ra j)).length)
    (hhp : (σ'.arrs (mpHeap j)).length = (σ.arrs (mpHeap j)).length) :
    mpSmp ra j σ' := by
  rw [mpSmp, hn, hra, hhp]
  exact h

/-- The peel program at level `j`: the parametric core at the level's
carrier cell, the region names of the ordering seam, and the `mp`
scratch family. -/
def mpPeelC (aoO ajO dgO ra : ℕ → String) (j : ℕ) : Com :=
  mdPeelCom (arenaNames j).nN (aoO j) (ajO j) (dgO j) (ra j) (mpHeap j)
    (lv "mp.s" j) (lv "mp.t" j) (lv "mp.x" j) (lv "mp.y" j) (lv "mp.k" j)
    (lv "mp.d" j) (lv "mp.v" j) (lv "mp.z" j) (lv "mp.i" j) (lv "mp.r" j)
    (lv "mp.w" j)

/-- Distinct bases of one common length stay `Nodup` after tagging. -/
theorem nodup_lv (bases : List String) (j : ℕ)
    (h4 : ∀ s ∈ bases, s.length = 4) (hnd : bases.Nodup) :
    (bases.map (lv · j)).Nodup :=
  hnd.map_on fun s hs t ht heq => by
    by_contra hne
    exact lv_ne_of_base_ne ((h4 s hs).trans (h4 t ht).symm) hne j j heq

/-- A base outside a base list stays outside after tagging. -/
theorem lv_notMem {s : String} {bases : List String} (j : ℕ)
    (hlen : ∀ t ∈ bases, t.length = s.length) (hs : s ∉ bases) :
    lv s j ∉ bases.map (lv · j) := by
  intro hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  obtain ⟨rfl, -⟩ := lv_inj (hlen t ht) heq
  exact hs ht

/-- `nsOf` is the packet's degree sum: `∑ v, |N_F(v)|`. -/
theorem nsOf_eq_sum_ncard {N : ℕ} (F : SimpleGraph (Fin N)) :
    nsOf F = ∑ v : Fin N, (F.neighborSet v).ncard := by
  rw [nsOf, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun v _ => baseDeg_eq F v

set_option maxHeartbeats 800000 in
/-- **The residual, discharged**: `CovMdPeelIn` — verbatim, at the
concrete peel `mpPeelC`, the scratch `mpSmp` and the budget
`KmdPeel A.N (nsOf (mdChain A.G R).toGraph)` (that is
`100·(A.N + ns)·(log₂ (A.N + ns + 1) + 1) + 100·A.N + 100` at the
augmented degree sum `ns`, by `nsOf_eq_sum_ncard`) — from hypotheses
of the F7-suppliable kinds only: `1 ≤ q` (the value bound's constant
is positive, as in `SolveCovLoad`), one `Nodup` of the level's array
names (the heap scratch, the seam's four regions and the arena's
five — scalars need no hypothesis: the carrier cell and the `mp`
family are concrete `lv` names), and the sweep scratch's transport
along the peel's frame. -/
theorem covMdPeelIn_mdPeelCom (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnames : ∀ j, ([mpHeap j, ra j, dgO j, aoO j, ajO j,
      (arenaNames j).off, (arenaNames j).tgt, (arenaNames j).col,
      (arenaNames j).up, (arenaNames j).hist] : List String).Nodup)
    (hSswT : ∀ j σ σ', Ssw j σ →
      (∀ a, a ∉ mpWrittenArrs dgO ra j → σ'.arrs a = σ.arrs a) →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y, y ∉ mpWrittenVars j → σ'.vars y = σ.vars y) →
      Ssw j σ') :
    CovMdPeelIn C hC φ R G c w q ℓp htabF hbf Adm ca co ra aoO ajO dgO mtO
      (mpSmp ra) Ssw (mpPeelC aoO ajO dgO ra)
      (fun _j A => KmdPeel A.N (nsOf (mdChain A.G R).toGraph)) := by
  intro x hx j hj A _hAdm _hG
  -- the word bound: `(A.N + 2)² ≤ (|x| + 1)² ≤ q·(|x| + 1)²`
  have hNn : A.N ≤ n := by
    have h := Fintype.card_le_of_embedding A.up
    simpa using h
  have hlen := hx.1.length_eq
  have hB : A.N * A.N + 4 * A.N + 4 ≤ mcB q x := by
    have h1 : A.N + 2 ≤ x.length + 1 := by omega
    have h2 : (A.N + 2) * (A.N + 2) ≤ (x.length + 1) * (x.length + 1) :=
      Nat.mul_le_mul h1 h1
    have h3 : (x.length + 1) * (x.length + 1) ≤ mcB q x := by
      rw [mcB, pow_two]
      exact Nat.le_mul_of_pos_left _ hq
    have h4 : A.N * A.N + 4 * A.N + 4 = (A.N + 2) * (A.N + 2) := by ring
    omega
  -- the scalar names: all concrete, `Nodup` by the `lv` mechanism
  have hnods : ([(arenaNames j).nN, lv "mp.s" j, lv "mp.t" j, lv "mp.x" j,
      lv "mp.y" j, lv "mp.k" j, lv "mp.d" j, lv "mp.v" j, lv "mp.z" j,
      lv "mp.i" j, lv "mp.r" j, lv "mp.w" j] : List String).Nodup := by
    have h := nodup_lv ["sv.n", "mp.s", "mp.t", "mp.x", "mp.y", "mp.k",
      "mp.d", "mp.v", "mp.z", "mp.i", "mp.r", "mp.w"] j (by decide)
      (by decide)
    simpa [arenaNames] using h
  have hnNfree := (List.nodup_cons.mp hnods).1
  have hnSfree : (arenaNames j).nS ∉
      ([lv "mp.s" j, lv "mp.t" j, lv "mp.x" j, lv "mp.y" j, lv "mp.k" j,
        lv "mp.d" j, lv "mp.v" j, lv "mp.z" j, lv "mp.i" j, lv "mp.r" j,
        lv "mp.w" j] : List String) := by
    have h := lv_notMem (s := "sv.m") (bases := ["mp.s", "mp.t", "mp.x",
      "mp.y", "mp.k", "mp.d", "mp.v", "mp.z", "mp.i", "mp.r", "mp.w"]) j
      (by decide) (by decide)
    simpa [arenaNames] using h
  -- the array names: the hypothesis bundle, destructured
  have harr : ([mpHeap j, ra j, dgO j, aoO j, ajO j] : List String).Nodup :=
    (hnames j).sublist (List.take_sublist 5 [mpHeap j, ra j, dgO j, aoO j,
      ajO j, (arenaNames j).off, (arenaNames j).tgt, (arenaNames j).col,
      (arenaNames j).up, (arenaNames j).hist])
  have hnj := hnames j
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hnj
  obtain ⟨⟨h_r, h_d, h_ao, h_aj, h_o, h_t, h_c, h_u, h_h⟩,
    ⟨r_d, r_ao, r_aj, r_o, r_t, r_c, r_u, r_h⟩,
    ⟨d_ao, d_aj, d_o, d_t, d_c, d_u, d_h⟩,
    ⟨ao_aj, ao_o, ao_t, ao_c, ao_u, ao_h⟩, ⟨aj_o, aj_t, aj_c, aj_u, aj_h⟩,
    ⟨o_t, o_c, o_u, o_h⟩, ⟨t_c, t_u, t_h⟩, ⟨c_u, c_h⟩, u_h⟩ := hnj
  have hofree : (arenaNames j).off ∉
      ([mpHeap j, dgO j, ra j] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h_o, Ne.symm d_o, Ne.symm r_o⟩
  have htfree : (arenaNames j).tgt ∉
      ([mpHeap j, dgO j, ra j] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h_t, Ne.symm d_t, Ne.symm r_t⟩
  have hcfree : (arenaNames j).col ∉
      ([mpHeap j, dgO j, ra j] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h_c, Ne.symm d_c, Ne.symm r_c⟩
  have hufree : (arenaNames j).up ∉
      ([mpHeap j, dgO j, ra j] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h_u, Ne.symm d_u, Ne.symm r_u⟩
  have hhfree : (arenaNames j).hist ∉
      ([mpHeap j, dgO j, ra j] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h_h, Ne.symm d_h, Ne.symm r_h⟩
  -- the core, at the residual's graph and bound
  have hcore := mdPeelCore_spec (B := mcB q x) (N := A.N)
    (F := (mdChain A.G R).toGraph) (nNm := (arenaNames j).nN)
    (ao := aoO j) (aj := ajO j) (dg := dgO j) (ra := ra j) (hp := mpHeap j)
    (hsv := lv "mp.s" j) (tv := lv "mp.t" j) (xv := lv "mp.x" j)
    (yv := lv "mp.y" j) (kv := lv "mp.k" j) (dv := lv "mp.d" j)
    (vv := lv "mp.v" j) (zv := lv "mp.z" j) (iv := lv "mp.i" j)
    (rc := lv "mp.r" j) (wv := lv "mp.w" j) (mtO j) hnods harr hB
  refine (hcore.pre ?_).post ?_
  · rintro σ ⟨hAr, hDel, -, -, hSmp, -⟩
    have hnN : σ.vars (arenaNames j).nN = A.N := hAr.n_eq
    refine ⟨hDel, hnN, ?_, ?_⟩
    · rw [← hnN]
      exact hSmp.1
    · rw [← hnN]
      exact hSmp.2
  · rintro σ σ' ⟨hAr, -, hca, hco, -, hSsw⟩ ⟨⟨hraL', hraV⟩, hfa, hfv, hlens⟩
    refine ⟨?_, ⟨hraL', fun v => (hraV v).trans (mdPerm_val _ v).symm⟩,
      ?_, ?_, ?_⟩
    · exact arenaStW_of_eq hAr (hfv _ hnNfree) (hfv _ hnSfree)
        (hfa _ hofree) (hfa _ htfree) (hfa _ hcfree) (hfa _ hufree)
        (hfa _ hhfree)
    · rw [hlens (ca j)]
      exact hca
    · rw [hlens (co j)]
      exact hco
    · exact hSswT j σ σ' hSsw (fun a ha => hfa a ha) hlens
        (fun y hy => hfv y hy)

end Residual

end Lax3Proofs.Prog
