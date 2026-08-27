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
      rw [peelLive_succ F hne, ← if_neg (α := ℕ) hune
          (b := mdRankAux F ((peelLive F k).erase
            (minDegVert F (peelLive F k) hne)) u)
          (a := (peelLive F k).card - 1),
        ← mdRankAux_of_nonempty F hne u]
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
  · have h1 : (nbrsIn F S v).card * N + (v : ℕ)
        < ((nbrsIn F S v).card + 1) * N := by
      rw [Nat.succ_mul]
      omega
    have h2 : ((nbrsIn F S v).card + 1) * N ≤ (nbrsIn F S u).card * N :=
      Nat.mul_le_mul_right N (by omega)
    omega
  · have humem : u ∈ S.filter fun w => (nbrsIn F S w).card
        = S.inf' hne fun w => (nbrsIn F S w).card := by
      refine Finset.mem_filter.mpr ⟨hu, ?_⟩
      rw [← heq, hv, card_nbrsIn_minDegVert F S hne]
    have hmin : v ≤ u := Finset.min'_le _ u humem
    have : (v : ℕ) ≤ (u : ℕ) := hmin
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
  rw [baseDeg, dif_pos ht]
  have h := SimpleGraph.degree_lt_card_verts F (⟨t, ht⟩ : Fin N)
  rw [Fintype.card_fin] at h
  have heq : (F.neighborSet (⟨t, ht⟩ : Fin N)).ncard
      = F.degree (⟨t, ht⟩ : Fin N) := by
    rw [SimpleGraph.degree, ← Set.ncard_coe_finset]
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborFinset]
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
  simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_nbrsIn, Finset.mem_univ,
    true_and, Finset.mem_coe, SimpleGraph.mem_neighborSet]
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

end Lax3Proofs.Prog
