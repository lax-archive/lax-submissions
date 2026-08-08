import Lax3Proofs.RamBfs

/-!
# Block-driven breadth-first search: the touched-only engine

`RamBfs.bfsCom` searches correctly and charges the *carrier*: its cost is
`51 n + 44 ns + 30`, linear in the whole graph, and it is linear in the
whole graph for one reason only — it begins by filling the entire
distance array with the sentinel. A level of the cover pass runs a search
from every centre it claims, and there are `Θ(n)` of them; an `O(n)` fill
per centre is an `Ω(n²)` level, which is exactly the phase-cost floor the
B7 gate compiled. Nothing about the *search* is carrier-sized — a ball of
radius `r` around a centre touches `1 + deg v` cells per vertex it
reaches and not one more. Only the fill is.

So this file removes the fill, and pays for removing it with a contract.

### Clean in, clean out

`bfsBlockCom d` is `seedSrc; bfsDrain; unwind d` — the landed search with
its initial fill deleted at the front and an **unwind** bolted on at the
back. The precondition is that the distance array *already* holds the
sentinel everywhere,

    σ.arrs "dist" = arrOf n (fun _ => d + 1),

and the postcondition is that it holds the sentinel everywhere again, on
the nose, as the same list. In between, the search writes a distance
into `dist v` exactly for the vertices `v` it reaches, and the unwind
walks the queue — which *is* the list of vertices it reached, in arrival
order — and puts the sentinel back into each one. The unwind is
therefore charged to the ball and not to the carrier, and the level pays
the `O(n)` cleaning **once**, before its first centre, instead of once
per centre.

This is the P0.4 trail-acceptance mechanism with the trail already
present in the data: `Refine/BlockLeaves.lean`'s header records that a
known write set is better than a trail when the write set *is* known,
and here it is known — the write set of `dist` is the queue segment
`q[0 .. tail)` together with the source cell. The queue is the trail, so
the engine carries no trail array.

The source cell is the one that needs saying twice. `seedSrc` writes
`dist src := 0` **unconditionally** — a walk of length zero needs no
edges, so a dead source is at distance zero from itself — but it puts
the source on the queue only when the mask says it is alive. A dead
source is thus written and never enqueued, and the queue would not find
it. The unwind therefore ends with one unconditional store,
`dist src := d + 1`, which is a no-op when the source was alive and is
the whole restoration when it was not.

### What comes out

The search's answer cannot be left in `dist`, because `dist` is wiped.
It is handed back in two parallel arrays instead, both written only up to
`tail`:

* `q[0 .. tail)` — the vertices the search reached, without repetition,
  in breadth-first order. This is the **reached-set reading**: the
  segment is exactly the ball, `{v | M v ≠ 0 ∧ WD G M d s v}`.
* `qd[0 .. tail)` — their distances, `qd i` being the distance of `q i`.
  This is the **distance reading**, at the landed threshold form:
  `qd i ≤ k ↔ WD G M k s (q i)` for every `k ≤ d`, which is
  `RamBfs.Frontier.dist_le_iff` transported across the unwind.

The unwind copies each distance into `qd` on its way past, so the two
readings cost one pass over the ball between them.

`q` and `qd` are **output, not scratch**, and the contract treats them
that way: the precondition asks nothing of either beyond their length
(`∃ g, σ.arrs "q" = arrOf n g`), and the postcondition constrains only
the segment below `tail`. Nothing is claimed about the cells above it,
and nothing needs to be — that is precisely what makes a level of many
centres compose. Each centre writes `q` from index `0` upwards and reads
only below its own tail, so whatever the previous centre left higher up
is unreachable. The one array whose residue *would* compound is `dist`,
and `dist` is the one the engine restores exactly.

So "exit state = entry state" is a claim about `dist`, and it is the
literal one: the same list, cell for cell. `BfsBlockDiff.lean`'s sentinel
gate is its compiled reading.

### The cap convention

A vertex reached at depth exactly `d` is dequeued and its whole block is
scanned, relaxing nothing — the sentinel makes every test fail there.
This is the landed program's convention, inherited verbatim because the
program text is inherited verbatim, and the cost form agrees with it: the
ball's weight sums `1 + deg v` over vertices reached at depth **at most**
`d`, the depth-`d` vertices included with their full rows. An engine of
this family that dropped the depth-`d` rows would be cheaper and would
need a different program; this one does not, and the differential gate at
`d = 1` in `BfsBlockDiff.lean` pins the boundary against the landed
search's own answer.

### The charge

`bfsBlockK bw nb = 44 bw + 80 nb + 60`, where `bw` bounds the ball's slot
weight and `nb` its size. **No `n`, no `ns`.** The caller supplies any
finite `A` containing the ball and is charged for `A`; a block-driven
consumer passes its own block, and gets the arena-charged reading its
interface asks for.
-/

namespace Lax3Proofs.Refine.BfsBlock

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs

variable {n ns nt d s : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}

/-! ### The program

Three commands, two of them the landed search's own. Only `unwind` is
new, and it is a counted loop over the queue. -/

/-- One vertex of the trail: read the reached vertex off the queue, copy
its distance out into `qd`, and put the sentinel back into `dist`. -/
def unwindSlot (d : ℕ) : Com :=
  .seq (.assign "u" (.get "q" (.var "ri")))
    (.seq (.assign "du" (.get "dist" (.var "u")))
      (.seq (.store "qd" (.var "ri") (.var "du"))
        (.seq (.store "dist" (.var "u") (.lit (d + 1)))
          (.assign "ri" (.add (.var "ri") (.lit 1))))))

/-- **The unwind.** Walk the queue, restoring every distance cell the
search wrote and copying the distances out as it goes; then restore the
source's cell, which the queue does not name when the source is dead. -/
def unwind (d : ℕ) : Com :=
  .seq (.assign "ri" (.lit 0))
    (.seq (Csr.scan "ri" "tail" (unwindSlot d))
      (.store "dist" (.var "src") (.lit (d + 1))))

/-- **Depth-capped breadth-first search that charges its ball.** The
landed search with no initial fill and a trail unwind: `dist` comes in
holding the sentinel everywhere and goes out holding it everywhere, and
the answer leaves in `q` and `qd`. -/
def bfsBlockCom (d : ℕ) : Com := .seq seedSrc (.seq bfsDrain (unwind d))

/-! ### The charge

Two numbers, and neither of them is the carrier: the slot weight of the
ball and the size of the ball. -/

/-- **The cost of a block-driven search**, in the ball's slot weight
`bw` and the ball's size `nb`. Carrier-free by construction: `n` and `ns`
do not occur. -/
def bfsBlockK (bw nb : ℕ) : ℕ := 44 * bw + 80 * nb + 60

/-- The charge is monotone in both arguments, which is what lets a
consumer pass any superset of the ball. -/
theorem bfsBlockK_mono {bw bw' nb nb' : ℕ} (hb : bw ≤ bw') (hn : nb ≤ nb') :
    bfsBlockK bw nb ≤ bfsBlockK bw' nb' := by
  simp only [bfsBlockK]; omega

/-! ### The ball, and the two bounds the potential is paid out of

The landed search's potential is `44 (ns - sc) + 40 (n - tail) + 40 (tail
- head)`: the slots not yet scanned, the vertices not yet enqueued, and
the queue's own length. The first two terms are the carrier, and they are
there for a reason — `sc ≤ ns` and `tail ≤ n` are what make the
truncated subtractions behave.

Both bounds have a ball-sized twin, and that is the whole of the cost
argument. Everything the queue ever holds lies in the ball, so `tail` is
bounded by the ball's *size* and `sc` by the ball's *slot weight*. The
caller does not have to name the ball exactly: any finite `A` containing
it will do, and the charge is read off `A`. -/

variable {D Q : ℕ → ℕ} {head tail : ℕ}

/-- **A vertex the search discovers at a positive distance is alive.**
The masked graph has no edge with a dead end, so a walk that arrives
anywhere but its own start arrives at a live vertex. This is what lets
the unwind know that the *only* discovered vertex that can be missing
from the queue is the source. -/
theorem alive_of_wd {k a b : ℕ} (h : WD G M k a b) (hne : a ≠ b) : M b ≠ 0 := by
  induction k generalizing b with
  | zero => exact absurd h.eq_of_zero hne
  | succ k ih =>
      rcases h.tail with h' | ⟨c, -, hcb⟩
      · exact ih h' hne
      · exact hcb.alive_right

/-- Everything on the queue is in the ball, hence in anything covering
it: the queue holds live vertices whose written distance is at most the
cap, and a written distance is achieved by a walk. -/
theorem mem_of_queue (hF : Frontier G M d s D Q head tail) {A : Finset ℕ}
    (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A) {i : ℕ} (hi : i < tail) : Q i ∈ A := by
  obtain ⟨hqn, hqd, hqm⟩ := hF.qmem i hi
  exact hA _ hqn hqm (WD.mono hqd (hF.sound _ hqn hqd))

/-- **The queue is no longer than the ball.** The queue holds distinct
vertices of the ball, so its length is at most the ball's size — the
ball-sized replacement for `tail ≤ n`. -/
theorem tail_le_card (hF : Frontier G M d s D Q head tail) {A : Finset ℕ}
    (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A) : tail ≤ A.card := by
  have hsub : (Finset.range tail).image Q ⊆ A := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    exact mem_of_queue hF hA (Finset.mem_range.1 hi)
  have hcard : ((Finset.range tail).image Q).card = tail := by
    rw [Finset.card_image_of_injOn fun i hi j hj hq =>
      hF.qinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hq]
    exact Finset.card_range tail
  have := Finset.card_le_card hsub
  omega

/-- **The blocks the search has scanned fit inside the ball's weight.**
The expanded vertices are distinct members of the ball, so their blocks
sum to at most the ball's slot weight — the ball-sized replacement for
`sc ≤ ns`. -/
theorem sum_rowLen_head_le (hF : Frontier G M d s D Q head tail) (hht : head ≤ tail)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A) :
    ∑ i ∈ Finset.range head, Csr.rowLen O (Q i) ≤ ∑ v ∈ A, Csr.rowLen O v := by
  have hinj : ∀ i ∈ Finset.range head, ∀ j ∈ Finset.range head, Q i = Q j → i = j :=
    fun i hi j hj hq => hF.qinj i (by have := Finset.mem_range.1 hi; omega) j
      (by have := Finset.mem_range.1 hj; omega) hq
  have himg : ∑ v ∈ (Finset.range head).image Q, Csr.rowLen O v
      = ∑ i ∈ Finset.range head, Csr.rowLen O (Q i) := Finset.sum_image hinj
  rw [← himg]
  refine Finset.sum_le_sum_of_subset fun z hz => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
  exact mem_of_queue hF hA (by have := Finset.mem_range.1 hi; omega)

/-! ### Emptying the queue, charged to the ball -/

/-- **The ball-charged potential.** The landed potential with the carrier
replaced by the ball: `bw` slots to scan, `nb` vertices to enqueue, and
the queue's own length. Both parameters are fixed before the run, and
neither is `n`. -/
def BallPot (bw nb : ℕ) (τ : Env) : ℕ :=
  44 * (bw - τ.vars "sc") + 40 * (nb - τ.vars "tail") + 40 * (τ.vars "tail" - τ.vars "head")

/-- **The search, paid for out of the ball.** The program is the landed
`bfsDrain`, unchanged; only the accounting is new. A turn still releases
`44` per slot of the block it scans and `40` for the vertex it retires,
and the two ball bounds are what make the truncated subtractions of the
potential behave — exactly where the landed walk used `sc ≤ ns` and
`tail ≤ n`. -/
theorem drain_ball {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb)
    {τ : Env} (hI : DrainInv G M nt d s O T τ) :
    ∃ τ' K, Run B bfsDrain τ τ' K ∧ DrainInv G M nt d s O T τ' ∧
      τ'.vars "head" = τ'.vars "tail" ∧ K + BallPot bw nb τ' ≤ BallPot bw nb τ + 4 := by
  refine Queue.drain_run B n n "q" "head" "tail" expandRow (DrainInv G M nt d s O T)
    (BallPot bw nb) (fun σ hσ => ?_) hnB (fun σ hσ hlt => ?_) hI
  · obtain ⟨D₁, Q₁, ⟨-, -, -, -, -, -, hq⟩, hFr, -⟩ := hσ
    exact ⟨Q₁, σ.vars "head", σ.vars "tail", hq, rfl, rfl, hFr.hd, hFr.tl,
      fun i hi => (hFr.qmem i hi).1⟩
  · obtain ⟨D₁, Q₁, hse, hFr, hsum⟩ := hσ
    obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ :=
      expandRow_run hcsr hnB hnsB hnt hdB hMB hse hFr hlt hsum
    refine ⟨σ', K, hrun, hI', ?_⟩
    obtain ⟨D₂, Q₂, -, hFr', hsum'⟩ := hI'
    -- the block just scanned, as an opaque number: `omega` must not see
    -- through `rowLen` to the offsets
    set r := Csr.rowLen O (Q₁ (σ.vars "head")) with hr
    have hsc₂ : σ'.vars "sc" ≤ bw := by
      rw [hsum']; exact le_trans (sum_rowLen_head_le hFr' hFr'.hd hA) hbw
    have htail₂ : σ'.vars "tail" ≤ nb := le_trans (tail_le_card hFr' hA) hnb
    have hsc₁ : σ.vars "sc" ≤ bw := by
      rw [hsum]; exact le_trans (sum_rowLen_head_le hFr hFr.hd hA) hbw
    have htail₁ : σ.vars "tail" ≤ nb := le_trans (tail_le_card hFr hA) hnb
    have hhd := hFr'.hd
    have hhd0 := hFr.hd
    simp only [BallPot]
    omega

/-! ### The unwind

The queue is the trail. Walking it restores every distance cell the
search wrote, and copies each distance out into `qd` on the way past, so
the two readings cost one pass over the ball between them. -/

/-- What holds part-way through the unwind. Four clauses carry the work:
nothing exceeds the sentinel; a cell still *below* the sentinel belongs
either to the source or to a queue entry the walk has not reached yet;
the cells already passed have been copied out; and the cells not yet
passed still hold what the search left there. -/
def UnwindInv (n nt d s tf : ℕ) (O T M D Q : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ D' QD,
    τ.vars "n" = n ∧ τ.vars "src" = s ∧ τ.vars "tail" = tf ∧
    τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf nt T ∧
    τ.arrs "alv" = arrOf n M ∧ τ.arrs "dist" = arrOf n D' ∧
    τ.arrs "q" = arrOf n Q ∧ τ.arrs "qd" = arrOf n QD ∧
    τ.vars "ri" ≤ tf ∧
    (∀ z, z < n → D' z ≤ d + 1) ∧
    (∀ z, z < n → D' z ≤ d → z = s ∨ ∃ j, τ.vars "ri" ≤ j ∧ j < tf ∧ Q j = z) ∧
    (∀ j, j < τ.vars "ri" → QD j = D (Q j)) ∧
    (∀ j, τ.vars "ri" ≤ j → j < tf → D' (Q j) = D (Q j))

/-- **One entry of the trail.** Read the vertex off the queue, copy its
distance out, put the sentinel back. The queue's injectivity is what
keeps the fourth clause alive: the cell just overwritten is named by no
later entry. -/
theorem unwindSlot_run {B : ℕ} (hnB : n < B) (hdB : d + 1 < B) {tf : ℕ} (htf : tf ≤ n)
    {D Q : ℕ → ℕ} (hqn : ∀ i, i < tf → Q i < n)
    (hqinj : ∀ i, i < tf → ∀ j, j < tf → Q i = Q j → i = j)
    (hDd : ∀ z, z < n → D z ≤ d + 1)
    {τ : Env} (hI : UnwindInv n nt d s tf O T M D Q τ) (hlt : τ.vars "ri" < tf) :
    ∃ τ' K, Run B (unwindSlot d) τ τ' K ∧ K ≤ 30 ∧
      UnwindInv n nt d s tf O T M D Q τ' ∧ τ'.vars "ri" = τ.vars "ri" + 1 := by
  obtain ⟨D', QD, hn, hsrc, htl, hoff, htgt, halv, hdist, hq, hqd, hri, hcap, hdisc,
    hcopy, hkeep⟩ := hI
  have hrin : τ.vars "ri" < n := by omega
  have hQn : Q (τ.vars "ri") < n := hqn _ hlt
  have hDkeep : D' (Q (τ.vars "ri")) = D (Q (τ.vars "ri")) := hkeep _ le_rfl hlt
  have hDB : D (Q (τ.vars "ri")) ≤ d + 1 := hDd _ hQn
  -- the read at the queue
  have hrq : (τ.arrs "q").getD (τ.vars "ri") 0 = Q (τ.vars "ri") := by
    rw [hq, getD_arrOf Q hrin]
  have hrq' : (τ.arrs "q")[τ.vars "ri"]?.getD 0 = Q (τ.vars "ri") := by
    rw [← List.getD_eq_getElem?_getD]; exact hrq
  have hqlen : τ.vars "ri" < (τ.arrs "q").length := by rw [hq, length_arrOf]; exact hrin
  have hvB : (τ.arrs "q").getD (τ.vars "ri") 0 < B := by rw [hrq]; omega
  -- and the read at the distance array, in the environment that read runs in
  have hdlen : ((τ.setVar "u" ((τ.arrs "q").getD (τ.vars "ri") 0)).vars "u")
      < ((τ.setVar "u" ((τ.arrs "q").getD (τ.vars "ri") 0)).arrs "dist").length := by
    rw [arrs_setVar, vars_setVar, hdist, length_arrOf]; simpa [hrq'] using hQn
  have hdval : ((τ.setVar "u" ((τ.arrs "q").getD (τ.vars "ri") 0)).arrs "dist").getD
      ((τ.setVar "u" ((τ.arrs "q").getD (τ.vars "ri") 0)).vars "u") 0
      = D (Q (τ.vars "ri")) := by
    rw [arrs_setVar, vars_setVar]
    simp only [hrq, hdist, if_true]
    rw [getD_arrOf D' hQn, hDkeep]
  have hdval' : (τ.arrs "dist")[(τ.arrs "q")[τ.vars "ri"]?.getD 0]?.getD 0
      = D (Q (τ.vars "ri")) := by
    rw [hrq', ← List.getD_eq_getElem?_getD, hdist, getD_arrOf D' hQn, hDkeep]
  have hdB' : ((τ.setVar "u" ((τ.arrs "q").getD (τ.vars "ri") 0)).arrs "dist").getD
      ((τ.setVar "u" ((τ.arrs "q").getD (τ.vars "ri") 0)).vars "u") 0 < B := by
    rw [hdval]; omega
  have hqdlen : (τ.arrs "qd").length = n := by rw [hqd, length_arrOf]
  have hdistlen : (τ.arrs "dist").length = n := by rw [hdist, length_arrOf]
  have hriB : τ.vars "ri" + 1 < B := by omega
  run_vcg
  refine ⟨⟨upd D' (Q (τ.vars "ri")) (d + 1), upd QD (τ.vars "ri") (D (Q (τ.vars "ri"))),
    by simp [hn], by simp [hsrc], by simp [htl], by simp [hoff], by simp [htgt],
    by simp [halv], by simp [hdist, hrq', set_arrOf_eq_upd],
    by simp [hq], by simp [hqd, hdval', set_arrOf_eq_upd], by simp; omega, ?_, ?_, ?_, ?_⟩,
    by simp⟩
  · -- nothing exceeds the sentinel
    intro z hz
    by_cases hzw : z = Q (τ.vars "ri")
    · rw [hzw, upd_self]
    · rw [upd_of_ne _ hzw]; exact hcap z hz
  · -- a cell still below the sentinel belongs to a later entry, or to the source
    intro z hz hzd
    by_cases hzw : z = Q (τ.vars "ri")
    · rw [hzw, upd_self] at hzd; omega
    · rw [upd_of_ne _ hzw] at hzd
      rcases hdisc z hz hzd with hs | ⟨j, hj₁, hj₂, hj₃⟩
      · exact Or.inl hs
      · refine Or.inr ⟨j, ?_, hj₂, hj₃⟩
        have hjne : j ≠ τ.vars "ri" := by rintro rfl; exact hzw hj₃.symm
        simp
        omega
  · -- everything passed has been copied out
    intro j hj
    simp at hj
    by_cases hje : j = τ.vars "ri"
    · rw [hje, upd_self]
    · rw [upd_of_ne _ hje]; exact hcopy j (by omega)
  · -- and everything not yet passed still holds what the search left
    intro j hj₁ hj₂
    simp at hj₁
    have hjne : Q j ≠ Q (τ.vars "ri") := fun hqe =>
      absurd (hqinj j hj₂ (τ.vars "ri") hlt hqe) (by omega)
    rw [upd_of_ne _ hjne]
    exact hkeep j (by omega) hj₂

/-- **The trail, walked.** The kit's counted loop: the caller says what
one entry does and how far it moves the pointer, and the combinator
supplies the loop condition, the exit fact and the cost — thirty-four per
entry of the queue. -/
theorem unwind_scan_spec {B : ℕ} (hnB : n < B) (hdB : d + 1 < B) {tf : ℕ} (htf : tf ≤ n)
    {D Q : ℕ → ℕ} (hqn : ∀ i, i < tf → Q i < n)
    (hqinj : ∀ i, i < tf → ∀ j, j < tf → Q i = Q j → i = j)
    (hDd : ∀ z, z < n → D z ≤ d + 1) :
    Spec B (fun τ => UnwindInv n nt d s tf O T M D Q τ ∧ τ.vars "ri" = 0)
      (Csr.scan "ri" "tail" (unwindSlot d))
      (fun _ τ' => UnwindInv n nt d s tf O T M D Q τ' ∧ τ'.vars "ri" = tf)
      (34 * tf + 4) := by
  refine Csr.rowScan_spec B (34 * tf + 4) tf 30 "ri" "tail" (unwindSlot d)
    (UnwindInv n nt d s tf O T M D Q) (by omega) (fun σ hσ => ?_) (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨D₁, QD₁, -, -, htl, -, -, -, -, -, -, hri, -⟩ := hσ
    exact ⟨htl, hri⟩
  · obtain ⟨σ', K', hr, hK, hI', hri'⟩ := unwindSlot_run hnB hdB htf hqn hqinj hDd hσ hlt
    exact ⟨σ', K', hr, hI', hri', hK⟩

/-- **The unwind, end to end.** The queue is walked, and then the
source's own cell is restored unconditionally — the one cell the queue
does not name, because a dead source is written at distance zero and
never enqueued. What comes out is the distance array as it went in, the
queue untouched, and the distances copied into `qd`. -/
theorem unwind_run {B : ℕ} (hs : s < n) (hnB : n < B) (hdB : d + 1 < B) {tf : ℕ}
    (htf : tf ≤ n) {D Q : ℕ → ℕ} (hqn : ∀ i, i < tf → Q i < n)
    (hqinj : ∀ i, i < tf → ∀ j, j < tf → Q i = Q j → i = j)
    (hDd : ∀ z, z < n → D z ≤ d + 1)
    (hdisc0 : ∀ z, z < n → D z ≤ d → z = s ∨ ∃ j, j < tf ∧ Q j = z)
    {QD₀ : ℕ → ℕ} {τ : Env}
    (hn : τ.vars "n" = n) (hsrc : τ.vars "src" = s) (htl : τ.vars "tail" = tf)
    (hoff : τ.arrs "off" = arrOf (n + 1) O) (htgt : τ.arrs "tgt" = arrOf nt T)
    (halv : τ.arrs "alv" = arrOf n M) (hdist : τ.arrs "dist" = arrOf n D)
    (hq : τ.arrs "q" = arrOf n Q) (hqd : τ.arrs "qd" = arrOf n QD₀) :
    ∃ τ' K, Run B (unwind d) τ τ' K ∧ K ≤ 34 * tf + 14 ∧
      τ'.arrs "dist" = arrOf n (fun _ => d + 1) ∧ τ'.arrs "q" = arrOf n Q ∧
      ∃ QD, τ'.arrs "qd" = arrOf n QD ∧ ∀ j, j < tf → QD j = D (Q j) := by
  have hscanSpec := unwind_scan_spec (n := n) (nt := nt) (d := d) (s := s) (O := O) (T := T)
    (M := M) (B := B) hnB hdB htf hqn hqinj hDd (D := D) (Q := Q)
  run_vcg [hscanSpec]
  · -- what the loop left, plus the source's own cell
    rename_i w hpost
    obtain ⟨⟨D', QD, hn', hsrc', htl', hoff', htgt', halv', hdist', hq', hqd', hri',
      hcap', hdisc', hcopy', -⟩, hriend⟩ := hpost
    refine ⟨?_, by simp [hq'], QD, by simp [hqd'],
      fun j hj => hcopy' j (by rw [hriend]; exact hj)⟩
    have hset : (w.setArr "dist" (w.vars "src") (d + 1)).arrs "dist"
        = arrOf n (upd D' s (d + 1)) := by
      simp [hdist', hsrc', set_arrOf_eq_upd]
    rw [hset]
    refine arrOf_congr fun i hi => ?_
    by_cases his : i = s
    · rw [his, upd_self]
    · rw [upd_of_ne _ his]
      have h₁ := hcap' i hi
      have h₂ : ¬ D' i ≤ d := fun h => his (by
        rcases hdisc' i hi h with h' | ⟨j, hj₁, hj₂, -⟩
        · exact h'
        · omega)
      omega
  · -- the loop starts at the top of the queue, in the state the assignment left
    refine ⟨⟨D, QD₀, by simp [hn], by simp [hsrc], by simp [htl], by simp [hoff],
      by simp [htgt], by simp [halv], by simp [hdist], by simp [hq], by simp [hqd],
      by simp, fun z hz => hDd z hz, fun z hz hzd => ?_,
      fun j hj => by simp at hj, fun j _ _ => rfl⟩, by simp⟩
    rcases hdisc0 z hz hzd with h | ⟨j, hj₁, hj₂⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, by simp, hj₁, hj₂⟩
  · -- the source's number is a word
    rename_i w hleft hpost
    obtain ⟨⟨D', QD, -, hsrc', -⟩, -⟩ := hpost
    rw [hsrc']; omega
  · -- and its cell is inside the distance array
    rename_i w hleft hpost
    obtain ⟨⟨D', QD, -, hsrc', -, -, -, -, hdist', -⟩, -⟩ := hpost
    rw [hsrc', hdist', length_arrOf]; exact hs

/-! ### The engine

Three phases, and not one of them looks at the carrier: the seed, the
search, the unwind. -/

/-- **Block-driven breadth-first search, charged to its ball.** Handed a
block structure for `G`, a mask, a source, a distance array that already
holds the sentinel everywhere, and two output arrays, `bfsBlockCom d`
leaves

* the distance array holding the sentinel everywhere again — the same
  list it came in as, so the next centre may start at once;
* the ball in `q[0 .. tail)`, without repetition: the segment names
  exactly the live vertices within `d` of the source;
* their distances in `qd[0 .. tail)`, at the landed threshold reading.

The cost is `bfsBlockK bw nb` for any `A` containing the ball, `bw`
bounding its slot weight and `nb` its size. **Neither `n` nor `ns`
occurs**, and that absence is the whole point of the engine: the level
above may now run one of these per centre.

**Rebase G2/E6 (E4b's preferred fix).** Two facts this proof computes
were dropped at the final `refine` and re-derived by a full re-walk in
`Refine/ScatterBlockBfs.lean`; they are now IN the postcondition and
that re-walk is a one-line delegation:

* `σ'.vars "tail" ≤ nb` — the queue segment is charged to the *ball*,
  which is what lets a consumer walk it at block cost;
* `∀ i < σ'.vars "tail", Q i < n` — every queue entry is a vertex, which
  is what lets a consumer index an array by one. -/
theorem bfsBlock_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs "alv" = arrOf n M ∧ σ.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g))
      (bfsBlockCom d)
      (fun _ σ' => σ'.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        ∃ Q QD, σ'.arrs "q" = arrOf n Q ∧ σ'.arrs "qd" = arrOf n QD ∧
          σ'.vars "tail" ≤ n ∧ σ'.vars "tail" ≤ nb ∧
          (∀ i, i < σ'.vars "tail" → Q i < n) ∧
          (∀ v, v < n →
            ((∃ i, i < σ'.vars "tail" ∧ Q i = v) ↔ (M v ≠ 0 ∧ WD G M d s v))) ∧
          (∀ i, i < σ'.vars "tail" → ∀ j, j < σ'.vars "tail" → Q i = Q j → i = j) ∧
          (∀ i, i < σ'.vars "tail" → ∀ k, k ≤ d → (QD i ≤ k ↔ WD G M k s (Q i))))
      (bfsBlockK bw nb) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hsrc, hoff, htgt, halv, hdist, ⟨g₁, hq⟩, ⟨g₂, hqd⟩⟩ := hσ
  -- the seed, on an array that is clean already: no fill, and this is the
  -- only place the carrier could have entered
  obtain ⟨σ₁, K₁, hrun₁, hK₁, hI₁, hhead₁, hsc₁⟩ :=
    seedSrc_run (G := G) (O := O) (T := T) (nt := nt) hs hnB hdB hMB hn hsrc hoff htgt
      halv hdist (fun _ _ => rfl) hq
  -- the search, charged to the ball
  obtain ⟨σ₂, K₂, hrun₂, hI₂, hhead₂, hpay⟩ :=
    drain_ball hcsr hnB hnsB hnt hdB hMB hA hbw hnb hI₁
  obtain ⟨D, Q, ⟨hn₂, hsrc₂, hoff₂, htgt₂, halv₂, hdist₂, hq₂⟩, hFr₂, -⟩ := hI₂
  rw [hhead₂] at hFr₂
  -- neither the seed nor the search touches the second output array
  have hqd₂ : σ₂.arrs "qd" = arrOf n g₂ := by
    rw [hrun₂.frame_arr "qd" (by simp [bfsDrain, expandRow, scanSlot, Csr.loadRow, Csr.scan,
        Queue.drain, Com.warrs]),
      hrun₁.frame_arr "qd" (by simp [seedSrc, Com.warrs])]
    exact hqd
  -- what the search leaves, in the form the unwind asks for
  have htl : σ₂.vars "tail" ≤ n := hFr₂.tl
  have hqn : ∀ i, i < σ₂.vars "tail" → Q i < n := fun i hi => (hFr₂.qmem i hi).1
  have hDd : ∀ z, z < n → D z ≤ d + 1 := hFr₂.cap
  have hdisc0 : ∀ z, z < n → D z ≤ d → z = s ∨ ∃ j, j < σ₂.vars "tail" ∧ Q j = z := by
    intro z hz hzd
    by_cases hmz : M z = 0
    · -- a dead discovered vertex can only be the source
      refine Or.inl ?_
      by_contra hzs
      exact alive_of_wd (hFr₂.sound z hz hzd) (Ne.symm hzs) hmz
    · obtain ⟨i, hi, hqi⟩ := hFr₂.qall z hz hmz hzd
      exact Or.inr ⟨i, hi, hqi⟩
  -- the unwind
  obtain ⟨σ₃, K₃, hrun₃, hK₃, hdist₃, hq₃, QD, hqd₃, hcopy₃⟩ :=
    unwind_run (O := O) (T := T) (nt := nt) (M := M) hs hnB hdB htl hqn
      (fun i hi j hj => hFr₂.qinj i hi j hj) hDd hdisc0 hn₂ hsrc₂ rfl hoff₂ htgt₂ halv₂
      hdist₂ hq₂ hqd₂
  have htail₃ : σ₃.vars "tail" = σ₂.vars "tail" :=
    hrun₃.frame_var "tail" (by simp [unwind, unwindSlot, Csr.scan, Com.wvars])
  -- the ball bound at the seed, which is what the potential starts at
  obtain ⟨D₁, Q₁, -, hFr₁, -⟩ := hI₁
  have htail₁ : σ₁.vars "tail" ≤ nb := le_trans (tail_le_card hFr₁ hA) hnb
  have htail₂nb : σ₂.vars "tail" ≤ nb := le_trans (tail_le_card hFr₂ hA) hnb
  have hpot₁ : BallPot bw nb σ₁ = 44 * bw + 40 * nb := by
    simp only [BallPot, hhead₁, hsc₁]; omega
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_, le_rfl, hdist₃, Q, QD, hq₃, hqd₃,
    by omega, by omega, fun i hi => hqn i (by omega), fun v hv => ?_,
    fun i hi j hj => hFr₂.qinj i (by omega) j (by omega),
    fun i hi k hk => ?_⟩
  · -- the charge
    rw [hpot₁] at hpay
    simp only [bfsBlockK]
    omega
  · -- the queue segment is the ball
    rw [htail₃]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hqn', hqd', hqm'⟩ := hFr₂.qmem i hi
      exact ⟨hqm', WD.mono hqd' (hFr₂.sound _ hqn' hqd')⟩
    · rintro ⟨hmv, hwv⟩
      obtain ⟨i, hi, hqi⟩ := hFr₂.qall v hv hmv (hFr₂.complete d le_rfl v hwv)
      exact ⟨i, hi, hqi⟩
  · -- and the distances it carries are the landed thresholds
    rw [htail₃] at hi
    rw [hcopy₃ i hi]
    exact hFr₂.dist_le_iff (hqn i hi) hk

/-- **The engine at the pinned target array**, which is the widened walk
at `nt = ns`. Nothing is re-proved. -/
theorem bfsBlock_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧ σ.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g))
      (bfsBlockCom d)
      (fun _ σ' => σ'.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        ∃ Q QD, σ'.arrs "q" = arrOf n Q ∧ σ'.arrs "qd" = arrOf n QD ∧
          σ'.vars "tail" ≤ n ∧ σ'.vars "tail" ≤ nb ∧
          (∀ i, i < σ'.vars "tail" → Q i < n) ∧
          (∀ v, v < n →
            ((∃ i, i < σ'.vars "tail" ∧ Q i = v) ↔ (M v ≠ 0 ∧ WD G M d s v))) ∧
          (∀ i, i < σ'.vars "tail" → ∀ j, j < σ'.vars "tail" → Q i = Q j → i = j) ∧
          (∀ i, i < σ'.vars "tail" → ∀ k, k ≤ d → (QD i ≤ k ↔ WD G M k s (Q i))))
      (bfsBlockK bw nb) :=
  bfsBlock_specW hcsr hs hnB hnsB le_rfl hdB hMB hA hbw hnb

/-! ### The charge, against the probe's honesty controls

`G2CostProbe`'s §5 reads every landed engine's cost as
`k * (weight + 1)` with `k` a numeral fixed before the input — `150` for
the cover's per-centre walk, `65` for the landed search, `200` for the
block leaves. The block engine's is `80`, and it is read against the
*ball's* weight rather than the carrier's: `s` members and `ds` slots,
which is `MassWeight.blockSize + blockRowSum`, which is
`slotWeight n (csrW n O)`, which is the `blockWeight` the cover's
per-centre obligation is stated in. -/

/-! ### Why the sentinel is not radius-free, and what it would take
(wave E4c-c, Part B — the dead end, recorded)

E4c-c asked whether the atom's remaining carrier pass — the per-atom
`fillCom "dist" (r + 1)` in `RamDriver.scatDeadCom` — could be removed
outright by making the "unvisited" sentinel radius-**independent**. Then
`ScatterBlock.ArenaA`'s seventh clause would stop naming the radius,
`unwind` would maintain it across atoms of different radii, and the fill
would hoist out of the atom instead of merely becoming touched-only.

**It cannot be done to the landed program, and the reason is
structural** (wave E4c-d built the *forked* program that can — §7 below;
read this section as the record of why a fork was necessary).
The sentinel *is* the depth cap. `RamBfs.scanSlot` relaxes on the single
test `dn < dist[w]`, and that one test does three jobs: it rejects an
already-discovered vertex, it rejects one discovered at this level, and
it caps the search — a vertex reached at depth `d` offers `d + 1`, which
does not beat the sentinel `d + 1` that an undiscovered vertex holds.
`radius_free_sentinel_breaks_cap` below is that mechanism as
arithmetic: at any radius-free sentinel `S > d + 1` the same offer
*passes*, so the search runs past the cap and its cost becomes the whole
reachable component rather than the ball — which is the one property
this engine exists to have (`bfsBlockK` names no `n` and no `ns`).

Restoring the cap needs an explicit `dn ≤ d` guard, i.e. **new control
flow** — and `RamBfs` is frozen, since `RamCover` and the ordering phase
read the same walk. The array renaming that let E4c-c delete the mask
copy (`ScatterBlock.renCom_spec`) permutes array *names*; it cannot
introduce a test. So Part B is a *fork*, which is §7 below: the guard
sits at the dequeue rather than in `scanSlot`, so the landed slot and
its whole relaxation walk are reused verbatim, and only the frontier
invariant is re-proved.

**And the second half would not pay even if the first were done.** With
a radius-free sentinel the fill hoists only as far as a state that
maintains it, and `RamDriver.coverPhase` — which runs at *every* level,
before that level's cluster loop — calls `RamCover.coverCom`, whose
search is the landed `RamBfs.bfsCom` with its own `initDist` and no
unwind: it leaves `"dist"` holding an arbitrary array
(`RamCover`'s postcondition is `∃ g, σ.arrs "dist" = arrOf n g`). So the
single initialization reaches level entry at best, never the root, and
is carrier-charged once per level. That is the trade
`Refine.C0CloseProbe`'s level-interface material exists to refuse: one
floor swapped for another. A wave that wants the fill gone has to take
the cover phase's search with it. -/

/-- **The sentinel is the cap.** A vertex reached at depth `d` offers
`d + 1`. Against the radius-dependent sentinel `d + 1` the offer fails
and the search stops; against any radius-free sentinel `S` above it the
offer succeeds and the search does not. This is the whole of why
`ScatterBlock.ArenaA`'s distance clause names the atom's own radius. -/
theorem radius_free_sentinel_breaks_cap (d S : ℕ) (hS : d + 1 < S) :
    ¬ (d + 1 < d + 1) ∧ (d + 1 < S) := ⟨by omega, hS⟩

/-- **The block engine is weight-linear at coefficient `80`.** This is
the ball-charged replacement for `G2CostProbe.bfsQCost_le_weight`, whose
`65 * (n + ns + 1)` reads the *carrier*. -/
theorem bfsBlockK_le_weight (s ds : ℕ) : bfsBlockK ds s ≤ 80 * (s + ds + 1) := by
  simp only [bfsBlockK]; omega

/-- **And the size-only budget is refuted**, on a star: one vertex whose
block is arbitrarily long. The probe pairs every admissible coefficient
with a refutation of an inadmissible reading, and the reading that must
die here is the one that charges the ball's *size* and forgets its
edges — `MassWeight.turn_size_refuted`'s shape for this engine. -/
theorem bfsBlockK_size_refuted (ct : ℕ) : ∃ s ds : ℕ, ¬ (bfsBlockK ds s ≤ ct * (s + 1)) :=
  ⟨1, 2 * ct + 1, by simp only [bfsBlockK]; omega⟩

/-! ### The capped scan, and what a radius-free sentinel costs
(wave E4c-d, Phase 1 (a) — the design, compiled)

E4c-c's dead end above is the *unguarded* engine's. This section
answers the question the campaign put next: **can the search be capped
by control flow instead of by the sentinel, so that the sentinel may go
radius-free?**

The answer is yes, and the whole of it is a *weakening of one clause of
the frontier invariant*, which is what §7a compiles.

### What the guard is, and where it goes

The cheapest place for the guard is the *dequeue*, not the slot: a
vertex at depth `d` relaxes nothing anyway, so the whole row may be
skipped rather than scanned and discarded. `expandRowC d` is
`RamBfs.expandRow` with the row load and the row scan moved inside
`if dv < d`, and it is the only program text this route adds — the slot
`RamBfs.scanSlot` is used verbatim, so the two straight-line reads, the
three relaxation paths and the block-scan combinator are all the landed
ones.

### The one clause that has to give

With a radius-free sentinel `S > d` an undiscovered cell holds `S`, and
`RamBfs.Frontier.exp` — *everything before `head` has had its whole
block looked at, its neighbours ending at most one level below it* —
becomes **false** at the depth-`d` vertices, whose rows are now skipped.
It is false and it cannot be repaired: `capped_exp_is_forced` below
exhibits a state satisfying every other clause at which the landed `exp`
fails outright.

So `exp` is guarded by `D (Q i) < d`, and the question is whether the
exit argument survives that. It does, and for a reason that is not an
accident of the proof: `Frontier.complete`'s induction consumes `exp`
only at a vertex the induction hypothesis has already placed at distance
at most `k`, with `k + 1 ≤ d` — so it never asks about a depth-`d`
vertex in the first place. `FrontierC.complete` is the landed induction
with that observation supplied to the guard.

Every other clause is the landed one, with `cap` restated as the
disjunction `D w ≤ d ∨ D w = S` — which at `S = d + 1` is exactly
`D w ≤ d + 1`, so `frontierC_of_frontier` reads the landed invariant as
an instance of this one and the fork is a genuine generalisation rather
than a different statement.

### And the charge does not move

The guard is `1 + Cond.size = 4` extra nodes on the scanning branch and
replaces the whole row load and scan on the other. The landed turn's
bound is `44·rowLen + 30` against a release of `40` per retired vertex,
so there are ten nodes of slack; `capped_turn_pays` is the potential
step at `44·scanned + 34`, `scanned` being `rowLen` on the guard's true
branch and `0` on its false branch. **`bfsBlockK` keeps its numerals**:
no `n`, no `ns`, and not a larger constant either. -/

section Capped

variable {S : ℕ}

/-! #### §7a The frontier invariant of a capped search -/

/-- **The frontier invariant at a radius-free sentinel.**
`RamBfs.Frontier` with two changes and no others:

* `cap` is the disjunction — a cell is a real distance at most `d`, or
  it is the sentinel `S`. At `S = d + 1` this is the landed `D w ≤ d + 1`
  (`frontierC_of_frontier`);
* `exp` is guarded by `D (Q i) < d`, because a depth-`d` vertex's row is
  no longer scanned. `capped_exp_is_forced` is the proof that the guard
  is not a convenience. -/
structure FrontierC {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d s S : ℕ)
    (D Q : ℕ → ℕ) (head tail : ℕ) : Prop where
  /-- A cell is a distance below the cap, or the sentinel. -/
  cap : ∀ w < n, D w ≤ d ∨ D w = S
  /-- The source is at distance zero, alive or not. -/
  src : D s = 0
  /-- A written distance is achieved by a walk of the arena. -/
  sound : ∀ w < n, D w ≤ d → WD G M (D w) s w
  /-- The queue is a segment. -/
  hd : head ≤ tail
  /-- It holds vertices. -/
  tl : tail ≤ n
  /-- Everything on it is a discovered live vertex. -/
  qmem : ∀ i < tail, Q i < n ∧ D (Q i) ≤ d ∧ M (Q i) ≠ 0
  /-- Every discovered live vertex is on it. -/
  qall : ∀ w < n, M w ≠ 0 → D w ≤ d → ∃ i < tail, Q i = w
  /-- Nothing is on it twice. -/
  qinj : ∀ i < tail, ∀ j < tail, Q i = Q j → i = j
  /-- It is sorted by distance. -/
  qmono : ∀ i j, i ≤ j → j < tail → D (Q i) ≤ D (Q j)
  /-- It spans at most one level beyond whatever is still pending. -/
  qcap : ∀ i < tail, ∀ j, head ≤ j → j < tail → D (Q i) ≤ D (Q j) + 1
  /-- **Guarded expansion.** Everything before `head` *that the guard let
  through* has had its whole block looked at. A vertex at depth exactly
  `d` is dequeued and skipped, and claims nothing. -/
  exp : ∀ i < head, D (Q i) < d → ∀ w, MAdj G M (Q i) w → D w ≤ D (Q i) + 1

namespace FrontierC

/-- **The landed invariant is this one at `S = d + 1`.** Both changes are
weakenings, so nothing about the uncapped engine is lost: `cap`'s
disjunction is `D w ≤ d + 1` there, and dropping `exp`'s guard only
throws a hypothesis away. -/
theorem _root_.Lax3Proofs.Refine.BfsBlock.frontierC_of_frontier
    (hF : Frontier G M d s D Q head tail) : FrontierC G M d s (d + 1) D Q head tail where
  cap w hw := by have := hF.cap w hw; omega
  src := hF.src
  sound := hF.sound
  hd := hF.hd
  tl := hF.tl
  qmem := hF.qmem
  qall := hF.qall
  qinj := hF.qinj
  qmono := hF.qmono
  qcap := hF.qcap
  exp i hi _ w hw := hF.exp i hi w hw

/-- **There is room for one more**, verbatim from the landed proof: it
reads `qmem` and `qinj` only, and neither moved. -/
theorem tail_lt (hF : FrontierC G M d s S D Q head tail) {w : ℕ} (hw : w < n)
    (hnot : ∀ i < tail, Q i ≠ w) : tail < n := by
  have hsub : (Finset.range tail).image Q ⊆ (Finset.range n).erase w := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    have hi' := Finset.mem_range.1 hi
    exact Finset.mem_erase.2 ⟨hnot i hi', Finset.mem_range.2 (hF.qmem i hi').1⟩
  have hcard : ((Finset.range tail).image Q).card = tail := by
    rw [Finset.card_image_of_injOn (fun i hi j hj hq =>
      hF.qinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hq)]
    exact Finset.card_range tail
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_range.2 hw), Finset.card_range] at this
  omega

/-- **The one change the arrays ever undergo, capped.** The landed
`RamBfs.Frontier.relax` with one hypothesis moved: `D (Q head) + 1 ≤ d`
was *derived* there from the sentinel bound `D w ≤ d + 1`, and here it
is supplied by the guard — which is the whole of the trade. Every clause
is discharged exactly as it was, `cap`'s new disjunction taking its left
branch at the written cell. -/
theorem relax (hF : FrontierC G M d s S D Q head tail) (hht : head < tail)
    {w : ℕ} (hadj : MAdj G M (Q head) w) (hlt : D (Q head) + 1 < D w)
    (hd1 : D (Q head) + 1 ≤ d) :
    FrontierC G M d s S (upd D w (D (Q head) + 1)) (upd Q tail w) head (tail + 1) := by
  obtain ⟨hvn, hdv, hmv⟩ := hF.qmem head hht
  have hw : w < n := hadj.lt_right
  have hmw : M w ≠ 0 := hadj.alive_right
  -- nothing on the queue can be `w`: `qcap` bounds it by the head's distance plus one
  have hnq : ∀ i < tail, Q i ≠ w := by
    intro i hi hqi
    have := hF.qcap i hi head le_rfl hht
    rw [hqi] at this
    omega
  have htn : tail < n := hF.tail_lt hw hnq
  have hwv : w ≠ Q head := by
    intro hwe; rw [hwe] at hlt; omega
  have hws : s ≠ w := by
    intro hse; rw [← hse, hF.src] at hlt; omega
  refine ⟨fun z hz => ?_, ?_, fun z hz hzd => ?_, by omega, by omega, fun i hi => ?_,
    fun z hz hmz hzd => ?_, fun i hi j hj hij => ?_, fun i j hij hj => ?_,
    fun i hi j hj₁ hj₂ => ?_, fun i hi hdi z hz => ?_⟩
  · by_cases hzw : z = w
    · rw [hzw, upd_self]; exact Or.inl hd1
    · rw [upd_of_ne _ hzw]; exact hF.cap z hz
  · rw [upd_of_ne _ hws]; exact hF.src
  · by_cases hzw : z = w
    · subst hzw
      rw [upd_self]
      exact (hF.sound _ hvn hdv).step hadj
    · rw [upd_of_ne _ hzw] at hzd ⊢; exact hF.sound z hz hzd
  · by_cases hit : i = tail
    · rw [hit, upd_self, upd_self]; exact ⟨hw, by omega, hmw⟩
    · have hi' : i < tail := by omega
      rw [upd_of_ne _ hit, upd_of_ne _ (hnq i hi')]
      exact hF.qmem i hi'
  · by_cases hzw : z = w
    · exact ⟨tail, by omega, by rw [upd_self, hzw]⟩
    · rw [upd_of_ne _ hzw] at hzd
      obtain ⟨i, hi, rfl⟩ := hF.qall z hz hmz hzd
      exact ⟨i, by omega, upd_of_ne _ (by omega)⟩
  · by_cases hit : i = tail <;> by_cases hjt : j = tail
    · omega
    · rw [hit, upd_self, upd_of_ne _ hjt] at hij
      exact absurd hij.symm (hnq j (by omega))
    · rw [hjt, upd_self, upd_of_ne _ hit] at hij
      exact absurd hij (hnq i (by omega))
    · rw [upd_of_ne _ hit, upd_of_ne _ hjt] at hij
      exact hF.qinj i (by omega) j (by omega) hij
  · by_cases hjt : j = tail
    · rw [hjt, upd_self, upd_self]
      by_cases hit : i = tail
      · rw [hit, upd_self, upd_self]
      · rw [upd_of_ne _ hit, upd_of_ne _ (hnq i (by omega))]
        have := hF.qcap i (by omega) head le_rfl hht
        omega
    · rw [upd_of_ne _ hjt, upd_of_ne _ (hnq j (by omega))]
      have hit : i ≠ tail := by omega
      rw [upd_of_ne _ hit, upd_of_ne _ (hnq i (by omega))]
      exact hF.qmono i j hij (by omega)
  · by_cases hjt : j = tail
    · rw [hjt, upd_self, upd_self]
      by_cases hit : i = tail
      · rw [hit, upd_self, upd_self]; omega
      · rw [upd_of_ne _ hit, upd_of_ne _ (hnq i (by omega))]
        have := hF.qcap i (by omega) head le_rfl hht
        omega
    · have hj' : j < tail := by omega
      have hdvj : D (Q head) ≤ D (Q j) := hF.qmono head j hj₁ hj'
      rw [upd_of_ne _ hjt, upd_of_ne _ (hnq j hj')]
      by_cases hit : i = tail
      · rw [hit, upd_self, upd_self]; omega
      · rw [upd_of_ne _ hit, upd_of_ne _ (hnq i (by omega))]
        exact hF.qcap i (by omega) j hj₁ hj'
  · -- the guarded expansion clause: the guard is what the landed proof's
    -- appeal to `exp` now needs, and the goal carries it
    have hit : i ≠ tail := by omega
    rw [upd_of_ne _ hit] at hz hdi ⊢
    rw [upd_of_ne _ (hnq i (by omega))] at hdi ⊢
    by_cases hzw : z = w
    · exfalso
      have h₁ := hF.exp i hi hdi w (by rw [← hzw]; exact hz)
      have h₂ := hF.qmono i head (by omega) hht
      omega
    · rw [upd_of_ne _ hzw]; exact hF.exp i hi hdi z hz

/-- **The exit argument, capped.** The landed induction, unchanged in
shape: the last edge of a walk of length `k + 1` runs from a vertex the
induction hypothesis has placed at distance at most `k`, and `k < d`
because `k + 1 ≤ d` — so the guard is discharged by arithmetic the
induction already had. **This is the theorem the whole route turns on**:
a depth-`d` vertex's row is never needed by completeness. -/
theorem complete (hF : FrontierC G M d s S D Q tail tail) :
    ∀ k, k ≤ d → ∀ w, WD G M k s w → D w ≤ k := by
  intro k
  induction k with
  | zero =>
      intro _ w hwd
      rw [← hwd.eq_of_zero, hF.src]
  | succ k ih =>
      intro hk w hwd
      rcases hwd.tail with hshort | ⟨c, hc, hcw⟩
      · have := ih (by omega) w hshort; omega
      · have hcd : D c ≤ k := ih (by omega) c hc
        obtain ⟨i, hi, hQi⟩ := hF.qall c hc.lt_right hcw.alive_left (by omega)
        have hstep := hF.exp i hi (by rw [hQi]; omega) w (by rw [hQi]; exact hcw)
        rw [hQi] at hstep
        omega

/-- **What a capped search computes**, at the landed threshold form. -/
theorem dist_le_iff (hF : FrontierC G M d s S D Q tail tail) {w : ℕ} (hw : w < n) {k : ℕ}
    (hk : k ≤ d) : D w ≤ k ↔ WD G M k s w :=
  ⟨fun h => (hF.sound w hw (by omega)).mono h, hF.complete k hk w⟩

end FrontierC

/-! #### §7b The two seeds, at a radius-free sentinel

`RamBfs.frontier_seed_alive` and `_dead` read the fill's value only
through `¬ (S ≤ d)`, which is what makes an undiscovered cell
undiscovered. So both go through at any `S > d`, and the radius-free
sentinel enters the proof exactly here and nowhere else. -/

/-- A live source goes on the queue. -/
theorem frontierC_seed_alive (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d S : ℕ) (hdS : d < S)
    (hs : s < n) (hms : M s ≠ 0) {g Q : ℕ → ℕ} (hg : ∀ j < n, g j = S) (hQ : Q 0 = s) :
    FrontierC G M d s S (upd g s 0) Q 0 1 := by
  have hval : ∀ z, z < n → z ≠ s → upd g s 0 z = S := fun z hz hzs => by
    rw [upd_of_ne _ hzs]; exact hg z hz
  refine ⟨fun z hz => ?_, upd_self .., fun z hz hzd => ?_, by omega, by omega, fun i hi => ?_,
    fun z hz hmz hzd => ?_, fun i hi j hj hij => by omega, fun i j hij hj => ?_,
    fun i hi j hj₁ hj₂ => ?_, fun i hi => absurd hi (by omega)⟩
  · by_cases hzs : z = s
    · rw [hzs, upd_self]; exact Or.inl (by omega)
    · exact Or.inr (hval z hz hzs)
  · have hzs : z = s := by by_contra hne; rw [hval z hz hne] at hzd; omega
    subst hzs
    rw [upd_self]
    exact WD.refl G M 0 hs
  · have hi0 : i = 0 := by omega
    rw [hi0, hQ, upd_self]
    exact ⟨hs, by omega, hms⟩
  · have hzs : z = s := by by_contra hne; rw [hval z hz hne] at hzd; omega
    exact ⟨0, by omega, by rw [hQ, hzs]⟩
  · have : i = 0 ∧ j = 0 := by omega
    rw [this.1, this.2]
  · have : i = 0 ∧ j = 0 := by omega
    rw [this.1, this.2]; omega

/-- A dead source does not. -/
theorem frontierC_seed_dead (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d S : ℕ) (hdS : d < S)
    (hs : s < n) (hms : M s = 0) {g Q : ℕ → ℕ} (hg : ∀ j < n, g j = S) :
    FrontierC G M d s S (upd g s 0) Q 0 0 := by
  have hval : ∀ z, z < n → z ≠ s → upd g s 0 z = S := fun z hz hzs => by
    rw [upd_of_ne _ hzs]; exact hg z hz
  refine ⟨fun z hz => ?_, upd_self .., fun z hz hzd => ?_, by omega, by omega,
    fun i hi => absurd hi (by omega), fun z hz hmz hzd => ?_,
    fun i hi j hj hij => absurd hi (by omega), fun i j hij hj => absurd hj (by omega),
    fun i hi j hj₁ hj₂ => absurd hj₂ (by omega), fun i hi => absurd hi (by omega)⟩
  · by_cases hzs : z = s
    · rw [hzs, upd_self]; exact Or.inl (by omega)
    · exact Or.inr (hval z hz hzs)
  · have hzs : z = s := by by_contra hne; rw [hval z hz hne] at hzd; omega
    subst hzs
    rw [upd_self]
    exact WD.refl G M 0 hs
  · exfalso
    have hzs : z = s := by by_contra hne; rw [hval z hz hne] at hzd; omega
    rw [hzs] at hmz; exact hmz hms

/-! #### §7c The guard is forced, on data

The weakening of `exp` is not a proof convenience. Here is the state a
capped search at cap `d = 0` leaves on the single edge `0—1`, with the
radius-free sentinel `5`: the source is expanded, its row is skipped
because its distance is not below the cap, and the neighbour keeps the
sentinel. Every clause of `FrontierC` holds; the **landed** `exp` — the
same clause without its guard — fails at the only expanded vertex. -/

/-- The one-edge arena, all alive. -/
private def capMask : ℕ → ℕ := fun _ => 1

/-- The distances a capped search at `d = 0` leaves: the source at zero,
its neighbour still at the sentinel. -/
private def capDist : ℕ → ℕ := fun z => if z = 0 then 0 else 5

/-- The queue: the source alone. -/
private def capQ : ℕ → ℕ := fun _ => 0

private theorem capMAdj : MAdj (⊤ : SimpleGraph (Fin 2)) capMask 0 1 :=
  madj_of_adj (by omega) (by omega) (by decide) (by decide) (by decide)

/-- **The capped invariant holds** of the state a capped search leaves at
cap zero. -/
theorem capped_frontier_holds :
    FrontierC (⊤ : SimpleGraph (Fin 2)) capMask 0 0 5 capDist capQ 1 1 := by
  refine ⟨fun w hw => ?_, rfl, fun w hw hwd => ?_, le_rfl, by omega, fun i hi => ?_,
    fun w hw hmw hwd => ?_, fun i hi j hj hij => by omega, fun i j hij hj => le_rfl,
    fun i hi j hj₁ hj₂ => by omega, fun i hi hdi => absurd hdi (by omega)⟩
  · interval_cases w <;> simp [capDist]
  · have hw0 : w = 0 := by
      by_contra hne
      interval_cases w <;> simp_all [capDist]
    subst hw0
    exact WD.refl _ _ _ (by omega)
  · have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨by simp [capQ], by simp [capDist, capQ], by simp [capMask]⟩
  · have hw0 : w = 0 := by
      by_contra hne
      interval_cases w <;> simp_all [capDist]
    exact ⟨0, by omega, by simp [capQ, hw0]⟩

/-- **And the landed clause fails at it.** `RamBfs.Frontier.exp` reads
`∀ i < head, ∀ w, MAdj (Q i) w → D w ≤ D (Q i) + 1`; at `i = 0` the
source's neighbour is at the sentinel `5`, not at `1`. So the guard on
`FrontierC.exp` is forced by the program and not chosen by the proof —
which is the compiled form of "the sentinel *is* the cap"
(`radius_free_sentinel_breaks_cap`) at the level of the invariant. -/
theorem capped_exp_is_forced :
    ¬ (∀ i < 1, ∀ w, MAdj (⊤ : SimpleGraph (Fin 2)) capMask (capQ i) w →
        capDist w ≤ capDist (capQ i) + 1) := by
  intro h
  have := h 0 (by omega) 1 (by simpa [capQ] using capMAdj)
  simp [capDist, capQ] at this

/-! #### §7d The program, and the charge

`expandRowC d` is `RamBfs.expandRow` with the row load and the row scan
under `if dv < d`. Nothing else of the search moves: the slot is
`RamBfs.scanSlot` verbatim, so the relaxation test — and with it every
range and word obligation of `scanSlot_run` — is the landed one. -/

/-- **One turn of a capped search**: dequeue, and scan the block only
when the vertex's own distance is strictly below the cap. -/
def expandRowC (d : ℕ) : Com :=
  .seq (.assign "v" (.get "q" (.var "head")))
    (.seq (.assign "dv" (.get "dist" (.var "v")))
      (.seq (.assign "dn" (.add (.var "dv") (.lit 1)))
        (.seq (.ite (.lt (.var "dv") (.lit d))
                (.seq (Csr.loadRow "off" "v" "j" "jend") (Csr.scan "j" "jend" scanSlot))
                .skip)
          (.assign "head" (.add (.var "head") (.lit 1))))))

/-- **The capped search**: the same queue drain, at the capped turn. -/
def bfsDrainC (d : ℕ) : Com := Queue.drain "head" "tail" (expandRowC d)

/-- **The capped block engine**: the landed seed, the capped drain, the
landed unwind. Only the middle limb differs from `bfsBlockCom`. -/
def bfsBlockComC (d : ℕ) : Com := .seq seedSrc (.seq (bfsDrainC d) (unwind d))

/-- The guard writes nothing and reads two cells: **four nodes** on the
scanning branch, by the cost model's own arithmetic (`1 + Cond.size`). -/
theorem guard_size (d : ℕ) : (Cond.lt (Expr.var "dv") (Expr.lit d)).size = 3 := rfl

/-- The capped turn touches exactly the names the landed turn does, so
every frame of the block engine is the landed `simp`. -/
theorem wvars_expandRowC (d : ℕ) : (expandRowC d).wvars = (expandRow).wvars := by
  simp [expandRowC, expandRow, Csr.loadRow, Csr.scan, Com.wvars]

theorem warrs_expandRowC (d : ℕ) : (expandRowC d).warrs = (expandRow).warrs := by
  simp [expandRowC, expandRow, Csr.loadRow, Csr.scan, Com.warrs]

/-- **A capped turn still pays for itself out of the ball potential.**
This is `drain_ball`'s per-turn step, as arithmetic and with the guard's
branches unified: `scanned` is the block just scanned on the guard's
true branch and `0` on its false branch, and `sc` moves by exactly that.
The bound `44·scanned + 34` is the landed `44·rowLen + 30` plus the
guard's four nodes on the scanning branch, and is far above the
skipping branch's nineteen.

Since the step goes through, the potential is the landed `BallPot` and
`bfsBlockK` keeps its numerals — **no `n`, no `ns`, and no larger
constant.** -/
theorem capped_turn_pays {bw nb sc sc' hd0 tl0 tl1 scanned K : ℕ}
    (hsc' : sc' = sc + scanned) (hscb : sc' ≤ bw) (hsc : sc ≤ bw)
    (htl1 : tl1 ≤ nb) (htl0 : tl0 ≤ nb) (hhd : hd0 + 1 ≤ tl1) (hht : hd0 < tl0)
    (hK : K ≤ 44 * scanned + 34) :
    K + (44 * (bw - sc') + 40 * (nb - tl1) + 40 * (tl1 - (hd0 + 1)))
      ≤ 44 * (bw - sc) + 40 * (nb - tl0) + 40 * (tl0 - hd0) := by
  omega

/-- **And six nodes of the ten are still unspent**: the release per
retired vertex is forty, so a guard of up to ten nodes would have fitted
where four were needed. -/
theorem capped_turn_slack {scanned K : ℕ} (hK : K ≤ 44 * scanned + 34) :
    K + 6 ≤ 44 * scanned + 40 := by omega

end Capped

#print axioms bfsBlock_spec
#print axioms bfsBlock_specW
#print axioms FrontierC.relax
#print axioms FrontierC.complete
#print axioms frontierC_of_frontier
#print axioms capped_exp_is_forced

end Lax3Proofs.Refine.BfsBlock
