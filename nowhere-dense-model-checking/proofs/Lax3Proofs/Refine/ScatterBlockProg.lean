import Lax3Proofs.Refine.ScatterBlockCost
import Lax3Proofs.RamScatter

/-!
# The active-set scatter engine: program text and the member algebra

This is the base file of the active-set scatter variant. It carries the
program, the contract on the member list, and the arithmetic that makes
a walk of the member list say the same thing as a walk of the carrier.
The walks themselves are in `ScatterBlockMark.lean`,
`ScatterBlockClear.lean` and `ScatterBlock.lean`; the charge is in
`ScatterBlockCost.lean` and was fixed before any of them.

### The three carrier terms, and what replaces each

`RamScatter.scatterCom` is `cnt := 0; clearExc; scatterLoop; flag := …`,
and it touches the carrier in three places. The variant replaces each:

| landed | cost | active-set | cost |
|---|---|---|---|
| `clearExc` — fill all `n` bits | `11 n` | `clearMem` — clear the `mm` member bits | `25 mm` |
| `scatterLoop` — scan all `n`, test `tab[v]` | `25 n` | `scatBlockLoop` — walk the member list | `40 mm` |
| `bfsCom` + `markCom` per pick | `74 n + 44 ns` | `bfsBlockCom` + `markBall` per pick | `44 bw + 110 nb` |

The third is the one that needed new capital, and it is
`Refine/BfsBlock.lean`: a search whose cost is its ball's, which hands
the ball back in `q[0 .. tail)` and leaves `dist` holding the sentinel
exactly as it found it. Marking is then a walk of that queue, because
**the queue is the ball** — so the marking sweep, which in the landed
engine is a flat pass over the whole distance array, becomes a pass over
the vertices the search actually reached.

### The table disappears

The landed scan asks `tab[v] > 0` at every carrier cell. The active scan
does not ask at all: the member list *is* the table's set, listed. That
is the contract `MemList` below states — strictly increasing, sound and
complete for `X` — and it is what makes the two engines agree.

Strict monotonicity is not decoration. It is what lets the invariant be
carried at a *carrier* position while the loop counts *members*: after
`j` members the scan stands at `memPos j`, and between one member and
the next there is no vertex the greedy process could have selected,
because a selected vertex is a member. `memGap` is that lemma and
`progressA_gap` is its transport.

### What the invariant may no longer claim

The landed `RamScatter.Progress` says of the exclusion array

    ∀ w < n, (E w = 0 ↔ ∀ u < p, GSel u → ¬ WD r u w),

at **every** carrier cell. The active engine cannot say that and does
not: it clears only the member cells, so a cell that is not a member of
`X` holds whatever the previous atom left there. `ProgressA` therefore
relativises both the bit-bound and the biconditional to `MemOf X`.

This is a genuine weakening of an internal invariant, and it is sound
for a specific reason worth writing down: the scan only ever *reads* an
exclusion bit at a member, and the recursion `gsel_iff` only ever tests
one at a member, because `GSel u → MemOf X u`. Nothing downstream is
weakened, because the exported postcondition of the landed pass —
`scatter_spec`'s — mentions only `flag`, and this file's export proves
that same postcondition verbatim. The relativisation is invisible at the
interface; E6 inherits an engine with the landed answer at a new charge.
-/

namespace Lax3Proofs.Refine.ScatterBlock

open Lax3.ColoredGraphs Lax3.ScatterSentences
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamScatter

variable {n ns nt mm r t : ℕ} {G : SimpleGraph (Fin n)} {M O T Mem : ℕ → ℕ}
  {X : Set (Fin n)}

/-! ### §1 The member list -/

/-- The vertex *numbered* `a` lies in the set the atom is about. This is
`GSel`'s pattern for membership rather than selection. -/
def MemOf {n : ℕ} (X : Set (Fin n)) (a : ℕ) : Prop := ∃ h : a < n, (⟨a, h⟩ : Fin n) ∈ X

theorem MemOf.lt {a : ℕ} (h : MemOf X a) : a < n := h.1

/-- **The contract on the member list.** `Mem` enumerates the members of
`X`, in strictly increasing order, and there are `mm` of them. The
driver already carries member lists per block — this is the shape
`Refine/CoverBlock.lean` copies at `memCopyK mm = 12 mm + 6`. -/
structure MemList (n mm : ℕ) (Mem : ℕ → ℕ) (X : Set (Fin n)) : Prop where
  /-- Every listed entry is a vertex. -/
  lt : ∀ j, j < mm → Mem j < n
  /-- The list is strictly increasing, hence repetition-free. -/
  smono : ∀ i j, i < j → j < mm → Mem i < Mem j
  /-- Everything listed is a member. -/
  sound : ∀ j, j < mm → MemOf X (Mem j)
  /-- Every member is listed. -/
  complete : ∀ a, MemOf X a → ∃ j, j < mm ∧ Mem j = a

/-- The list is weakly increasing too, which is the form the gap
argument uses. -/
theorem MemList.mono (h : MemList n mm Mem X) {i j : ℕ} (hij : i ≤ j) (hj : j < mm) :
    Mem i ≤ Mem j := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (h.smono i j hlt hj)

/-! ### §1b The member count is a carrier count

A strictly increasing list of vertices is no longer than the carrier.
This is what lets every word bound the walks need be read off `n < B`,
and — since the member array is carried at the *carrier's* physical
length with a live prefix of `mm` cells — it is also what turns a
prefix index into an index of the array. -/

theorem MemList.le_of_lt (h : MemList n mm Mem X) {j : ℕ} (hj : j < mm) : j ≤ Mem j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hk : k < mm := by omega
      have h₁ := h.smono k (k + 1) (by omega) hj
      have h₂ := ih hk
      omega

/-- **There are no more members than vertices.** -/
theorem MemList.card_le (h : MemList n mm Mem X) : mm ≤ n := by
  rcases Nat.eq_zero_or_pos mm with rfl | hpos
  · exact Nat.zero_le _
  · have h1 : mm - 1 < mm := by omega
    have h₂ := h.le_of_lt h1
    have h₃ := h.lt (mm - 1) h1
    omega

/-- **The contract reads the live prefix only.** Two functions that
agree below the count are the same member list — the junk above the
live prefix is not part of the contract, and this is what lets a
live-prefix copy into a longer physical array carry the list. -/
theorem MemList.congr_prefix {Mem' : ℕ → ℕ} (h : MemList n mm Mem X)
    (hpre : ∀ k, k < mm → Mem' k = Mem k) : MemList n mm Mem' X where
  lt := fun j hj => by rw [hpre j hj]; exact h.lt j hj
  smono := fun i j hij hj => by
    rw [hpre i (by omega), hpre j hj]; exact h.smono i j hij hj
  sound := fun j hj => by rw [hpre j hj]; exact h.sound j hj
  complete := fun a ha => by
    obtain ⟨j, hj, hMj⟩ := h.complete a ha
    exact ⟨j, hj, by rw [hpre j hj]; exact hMj⟩

/-- **Where the scan stands after `j` members**: at the `j`-th member if
there is one, and at the end of the carrier once the list is spent. This
is the carrier position at which the landed invariant is read. -/
def memPos (n mm : ℕ) (Mem : ℕ → ℕ) (j : ℕ) : ℕ := if j < mm then Mem j else n

theorem memPos_of_lt {j : ℕ} (h : j < mm) : memPos n mm Mem j = Mem j := if_pos h

theorem memPos_of_ge {j : ℕ} (h : mm ≤ j) : memPos n mm Mem j = n := if_neg (by omega)

/-- The scan starts at or before the first member and ends at the end of
the carrier. -/
theorem memPos_le (h : MemList n mm Mem X) (j : ℕ) : memPos n mm Mem j ≤ n := by
  rw [memPos]
  split
  · exact le_of_lt (h.lt _ ‹_›)
  · exact le_rfl

/-- **The gap lemma, at the front**: nothing before the first member is
a member. -/
theorem memGap_zero (h : MemList n mm Mem X) {u : ℕ} (hu : u < memPos n mm Mem 0) :
    ¬ MemOf X u := by
  intro hmem
  obtain ⟨i, hi, hMi⟩ := h.complete u hmem
  have h0 : memPos n mm Mem 0 = Mem 0 := memPos_of_lt (by omega)
  rw [h0] at hu
  have : Mem 0 ≤ Mem i := h.mono (Nat.zero_le i) hi
  omega

/-- **The gap lemma, in the middle**: between one member and the next
there is no member. Strict monotonicity is exactly what this needs. -/
theorem memGap (h : MemList n mm Mem X) {j u : ℕ} (hj : j < mm) (hlt : Mem j < u)
    (hu : u < memPos n mm Mem (j + 1)) : ¬ MemOf X u := by
  intro hmem
  obtain ⟨i, hi, hMi⟩ := h.complete u hmem
  rcases Nat.lt_or_ge j i with hji | hij
  · -- a later entry, so at least the next one
    have hj1 : j + 1 ≤ i := hji
    have hle : Mem (j + 1) ≤ Mem i := h.mono hj1 hi
    have hpos : memPos n mm Mem (j + 1) = Mem (j + 1) :=
      memPos_of_lt (by omega)
    omega
  · -- an earlier or equal entry, so at most `Mem j`
    have hle : Mem i ≤ Mem j := h.mono hij hj
    omega

/-! ### §2 The invariant, relativised to the active set

`RamScatter.Progress`'s exclusion clause reads every carrier cell.
`ProgressA` reads only the cells the scan will read. -/

/-- **What the scan has established after the vertices before `p`**, at
the active-set reading. The first disjunct — the early exit — is the
landed one verbatim; only the exclusion clause of the second is
relativised. -/
def ProgressA (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (r t : ℕ) (X : Set (Fin n))
    (p : ℕ) (σ : Env) : Prop :=
  (σ.vars "cnt" = t ∧ t ≤ (greedySet (masked G M) r X).ncard) ∨
    (σ.vars "cnt" < t ∧ σ.vars "cnt" = (selBelow G M r X p).ncard ∧
      ∃ E, σ.arrs "exc" = arrOf n E ∧ (∀ w, MemOf X w → E w ≤ 1) ∧
        ∀ w, MemOf X w → (E w = 0 ↔ ∀ u < p, GSel G M r X u → ¬ WD G M r u w))

theorem ProgressA.cnt_le {p : ℕ} {σ : Env} (h : ProgressA G M r t X p σ) :
    σ.vars "cnt" ≤ t := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- It speaks of two names, so it transports across anything that leaves
them alone. -/
theorem ProgressA.of_eq {p : ℕ} {σ σ' : Env} (h : ProgressA G M r t X p σ)
    (hc : σ'.vars "cnt" = σ.vars "cnt") (he : σ'.arrs "exc" = σ.arrs "exc") :
    ProgressA G M r t X p σ' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂, E, hexc, hE1, hEiff⟩
  · exact Or.inl ⟨by rw [hc, h₁], h₂⟩
  · exact Or.inr ⟨by rw [hc]; exact h₁, by rw [hc]; exact h₂, E, by rw [he, hexc], hE1, hEiff⟩

/-- **A selected vertex is a member.** This is why relativising the
invariant to the members costs nothing: the recursion never asks about
anything else. -/
theorem memOf_of_gsel {a : ℕ} (h : GSel G M r X a) : MemOf X a :=
  ⟨h.lt, ((gsel_iff h.lt).1 h).1⟩

/-- A vertex the scan passes over changes nothing — the landed
`progress_succ_of_not`, at the relativised invariant. -/
theorem progressA_succ_of_not {p : ℕ} {σ : Env} (hg : ¬ GSel G M r X p)
    (h : ProgressA G M r t X p σ) : ProgressA G M r t X (p + 1) σ := by
  rcases h with hB | ⟨h₁, h₂, E, hexc, hE1, hEiff⟩
  · exact Or.inl hB
  · refine Or.inr ⟨h₁, by rw [h₂, selBelow_succ_of_not hg], E, hexc, hE1, fun w hw => ?_⟩
    rw [hEiff w hw]
    refine ⟨fun hall u hu hgu => ?_, fun hall u hu hgu => hall u (by omega) hgu⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
    · exact hall u hu' hgu
    · exact absurd hgu hg

/-- **Crossing a gap.** A stretch of the carrier holding nothing the
process selects moves the invariant without moving the machine. This is
what turns `mm` turns of the member scan into `n` turns of the landed
one. -/
theorem progressA_gap {p p' : ℕ} {σ : Env} (hp : p ≤ p')
    (hgap : ∀ u, p ≤ u → u < p' → ¬ GSel G M r X u)
    (h : ProgressA G M r t X p σ) : ProgressA G M r t X p' σ := by
  obtain ⟨k, rfl⟩ : ∃ k, p' = p + k := ⟨p' - p, by omega⟩
  clear hp
  induction k with
  | zero => exact h
  | succ k ih =>
      have hk : ProgressA G M r t X (p + k) σ :=
        ih (fun u hu hu' => hgap u hu (by omega))
      exact progressA_succ_of_not (hgap (p + k) (by omega) (by omega)) hk

/-- The member-list form of the gap: between consecutive members nothing
is selected, because everything selected is a member. -/
theorem progressA_step_gap (h : MemList n mm Mem X) {j : ℕ} (hj : j < mm) {σ : Env}
    (hP : ProgressA G M r t X (Mem j + 1) σ) :
    ProgressA G M r t X (memPos n mm Mem (j + 1)) σ := by
  rcases Nat.lt_or_ge (Mem j) (memPos n mm Mem (j + 1)) with hlt | hge
  · refine progressA_gap (by omega) (fun u hu hu' hgu => ?_) hP
    exact memGap h hj (by omega) hu' (memOf_of_gsel hgu)
  · -- the next position is not beyond this member, so there is nothing to cross
    have : memPos n mm Mem (j + 1) ≤ Mem j + 1 := by omega
    rcases Nat.lt_or_ge (memPos n mm Mem (j + 1)) (Mem j + 1) with hcon | hok
    · -- impossible: the list is increasing and `memPos` is `n` past the end
      exfalso
      rcases Nat.lt_or_ge (j + 1) mm with hj1 | hj1
      · rw [memPos_of_lt hj1] at hcon
        have := h.smono j (j + 1) (by omega) hj1
        omega
      · rw [memPos_of_ge hj1] at hcon
        have := h.lt j hj
        omega
    · have heq : memPos n mm Mem (j + 1) = Mem j + 1 := by omega
      rw [heq]; exact hP

/-- The invariant at the start of the scan is the invariant at the
carrier position the first member sits at. -/
theorem progressA_start (h : MemList n mm Mem X) {σ : Env}
    (hP : ProgressA G M r t X 0 σ) : ProgressA G M r t X (memPos n mm Mem 0) σ := by
  refine progressA_gap (Nat.zero_le _) (fun u _ hu' hgu => ?_) hP
  exact memGap_zero h hu' (memOf_of_gsel hgu)

/-- And at the end of the scan the position is the end of the carrier,
so the prefix is the whole greedy set. -/
theorem memPos_end (h : MemList n mm Mem X) : memPos n mm Mem mm = n :=
  memPos_of_ge le_rfl

/-! ### §3 The program

The landed pass's shape, limb for limb, with each carrier walk replaced
by its member or ball walk. The scalars are the landed ones plus three:
`mm` holds the member count, `sj` indexes the member list, and `mv`
holds the member the scan is at. `mw` is the mark loop's own, and `ri`
is the queue pointer `BfsBlock.unwind` already uses. -/

/-- One member of the clearing pass: read the member, clear its bit. -/
def clearSlot : Com :=
  .seq (.assign "mv" (.get "mem" (.var "mj")))
    (.seq (.store "exc" (.var "mv") (.lit 0))
      (.assign "mj" (.add (.var "mj") (.lit 1))))

/-- **The clearing pass, at the active set.** The landed `clearExc`
fills all `n` bits; this clears the `mm` the scan will read. -/
def clearMem : Com := .seq (.assign "mj" (.lit 0)) (Csr.scan "mj" "mm" clearSlot)

/-- One vertex of the ball: read it off the queue, set its bit.

**The guard is a defect report in program form.**
`BfsBlock.bfsBlock_spec`'s postcondition says the queue segment *names*
the ball — `∀ v, v < n → ((∃ i < tail, Q i = v) ↔ …)` — but it never says
that a queue entry is a vertex. The fact `∀ i < tail, Q i < n` exists
inside `bfsBlock_specW`'s own proof, as `Frontier.qmem`'s first
component, and is dropped at the interface. A consumer that indexes an
array by a queue entry therefore cannot discharge its range obligation,
and in IMP+ an out-of-range store is *stuck*, not a no-op.

Testing `mw < n` recovers that, at one comparison per ball vertex, and
leaves the marked set unchanged: the postcondition quantifies over
`w < n` anyway, so guarding a store that could only ever have fired
outside that range costs nothing semantically.

It is, however, **not sufficient on its own**, and that is worth
recording. The guard runs after the read, and the read
`.assign "mw" (.get "q" (.var "ri"))` is stuck too if `Q ri` exceeds the
*word* bound — `evalB_get`'s last obligation is `v < B`. So
`markBall_run` carries `hqB : ∀ i < tf, Q i < B` regardless, and the
guard buys only the range half of the problem.

Both halves are supplied here by `ScatterBlockBfs.bfsBlockA_specW`, this
wave's strengthened re-export, which carries `Q i < n` through to the
interface. Once the owning wave folds those clauses into
`bfsBlock_specW` itself — where `tail ≤ nb` is already computed and
*never used*, which is what makes the omission look accidental — this
guard and `hqB` can both go, and the ball walk drops from `18 tf + 9`
to `14 tf + 9`. -/
def markSlot : Com :=
  .seq (.assign "mw" (.get "q" (.var "ri")))
    (.seq (.ite (.lt (.var "mw") (.var "n")) (.store "exc" (.var "mw") (.lit 1)) .skip)
      (.assign "ri" (.add (.var "ri") (.lit 1))))

/-- **Marking the ball.** The landed `markCom` sweeps the whole distance
array; this walks the queue the block search handed back, which *is* the
ball, and then sets the source's own bit unconditionally.

The last store is not redundant. `BfsBlock`'s search writes a dead
source's distance cell but never enqueues it, so a dead source is in no
queue segment — and the landed engine does exclude it, because its flat
sweep reads `dist src = 0 ≤ r`. The unconditional store is how the ball
walk keeps that agreement, and it is the mirror of `unwind`'s own final
store. -/
def markBall : Com :=
  .seq (.assign "ri" (.lit 0))
    (.seq (Csr.scan "ri" "tail" markSlot)
      (.store "exc" (.var "src") (.lit 1)))

/-- Take the member the scan is at: count it, search from it, mark its
ball. -/
def pickBlock (r : ℕ) : Com :=
  .seq (.assign "cnt" (.add (.var "cnt") (.lit 1)))
    (.seq (.assign "src" (.var "mv"))
      (.seq (BfsBlock.bfsBlockCom r) markBall))

/-- One turn of the member scan, before the counter moves. **Two** tests,
not the landed three: the table test is gone, because being on the list
*is* the table test. -/
def scatBlockBody (r t : ℕ) : Com :=
  .ite (.lt (.var "cnt") (.lit t))
    (.ite (.eq (.get "exc" (.var "mv")) (.lit 0)) (pickBlock r) .skip)
    .skip

/-- One turn: read the member, decide it, advance. -/
def scatBlockStep (r t : ℕ) : Com :=
  .seq (.assign "mv" (.get "mem" (.var "sj")))
    (.seq (scatBlockBody r t) (.assign "sj" (.add (.var "sj") (.lit 1))))

/-- **The scan**, over the member list. -/
def scatBlockLoop (r t : ℕ) : Com :=
  .seq (.assign "sj" (.lit 0)) (Csr.scan "sj" "mm" (scatBlockStep r t))

/-- **The whole active-set pass**: clear, scan, report. The reporting
limb is the landed one, character for character. -/
def scatBlockCom (r t : ℕ) : Com :=
  .seq (.assign "cnt" (.lit 0))
    (.seq clearMem
      (.seq (scatBlockLoop r t)
        (.ite (.lt (.var "cnt") (.lit t)) (.assign "flag" (.lit 0)) (.assign "flag" (.lit 1)))))

/-! ### §4 Frames

Each is one `simp` against concrete program text. -/

@[simp] theorem wvars_clearSlot : clearSlot.wvars = ["mv", "mj"] := by
  simp [clearSlot, Com.wvars]

@[simp] theorem warrs_clearSlot : clearSlot.warrs = ["exc"] := by
  simp [clearSlot, Com.warrs]

@[simp] theorem wvars_markSlot : markSlot.wvars = ["mw", "ri"] := by
  simp [markSlot, Com.wvars]

@[simp] theorem warrs_markSlot : markSlot.warrs = ["exc"] := by
  simp [markSlot, Com.warrs]

theorem notMem_markBall_wvars (y : String)
    (hy : y ∈ ["n", "src", "sj", "mv", "cnt", "flag", "tail", "mm"]) :
    y ∉ markBall.wvars := by
  fin_cases hy <;> simp [markBall, markSlot, Csr.scan, Com.wvars]

theorem notMem_markBall_warrs (a : String)
    (ha : a ∈ ["off", "tgt", "alv", "mem", "dist", "q", "qd"]) : a ∉ markBall.warrs := by
  fin_cases ha <;> simp [markBall, markSlot, Csr.scan, Com.warrs]

theorem notMem_clearMem_wvars (y : String)
    (hy : y ∈ ["n", "src", "sj", "cnt", "flag", "tail", "mm"]) : y ∉ clearMem.wvars := by
  fin_cases hy <;> simp [clearMem, clearSlot, Csr.scan, Com.wvars]

theorem notMem_clearMem_warrs (a : String)
    (ha : a ∈ ["off", "tgt", "alv", "mem", "dist", "q", "qd"]) : a ∉ clearMem.warrs := by
  fin_cases ha <;> simp [clearMem, clearSlot, Csr.scan, Com.warrs]

/-! ### §5 The mask array, made a parameter — by renaming, not by rewriting

**Why a renaming and not a parameter.** The engine reads its mask in
exactly two places, and neither of them is in this family of files:
`RamBfs.seedSrc` asks `alv[src] > 0` before enqueueing the source, and
`RamBfs.scanSlot` asks `alv[w] > 0` before relaxing a target. Both are
landed program text with a whole correctness walk over them
(`seedSrc_run`, `expandRow_run`, `Queue.drain`), so turning the literal
`"alv"` into a parameter *there* would re-open that walk. What is
offered here instead is a transport: the engine is run on the program
with every array name pushed through an involution `f`, in the
environment with every array name pulled back through the same `f`, and
the two cancel. Nothing about the search is re-proved — `renCom_spec`
below carries any `Spec` across, cost included, because the renaming
does not change a single `Expr.size`.

The involution used downstream is `maskSwap av`, which exchanges `"alv"`
with `av` and fixes everything else. Applied to the engine — which never
mentions `av` — the result is literally "the engine, reading its mask
out of `av`", and `RamDriver.scatDeadCom` may then point it straight at
the child's own alive array instead of copying that array into `"alv"`
first.

An involution rather than a bijection is not a convenience: `Env`
renaming is a *pullback* (`renEnv f σ` reads array `a` as `σ.arrs (f a)`)
while `Com` renaming is a *pushforward*, so the two cancel only when `f`
is its own inverse. Injectivity alone would give the store case, but not
the reconstruction of the final environment. -/

/-- Rename the arrays an expression reads. -/
def renExpr (f : String → String) : Expr → Expr
  | .lit v => .lit v
  | .var x => .var x
  | .get a i => .get (f a) (renExpr f i)
  | .bin op e g => .bin op (renExpr f e) (renExpr f g)

/-- Rename the arrays a condition reads. -/
def renCond (f : String → String) : Cond → Cond
  | .eq e g => .eq (renExpr f e) (renExpr f g)
  | .lt e g => .lt (renExpr f e) (renExpr f g)

/-- Rename every array a command mentions, read or written. Scalars,
control flow and the tapes are untouched. -/
def renCom (f : String → String) : Com → Com
  | .skip => .skip
  | .assign x e => .assign x (renExpr f e)
  | .store a i e => .store (f a) (renExpr f i) (renExpr f e)
  | .seq c d => .seq (renCom f c) (renCom f d)
  | .ite b c d => .ite (renCond f b) (renCom f c) (renCom f d)
  | .while b c => .while (renCond f b) (renCom f c)
  | .read x => .read x
  | .write e => .write (renExpr f e)

/-- The environment that answers a question about array `a` with what
`σ` says about `f a`. -/
def renEnv (f : String → String) (σ : Env) : Env :=
  { σ with arrs := fun a => σ.arrs (f a) }

@[simp] theorem renEnv_arrs (f : String → String) (σ : Env) (a : String) :
    (renEnv f σ).arrs a = σ.arrs (f a) := rfl

@[simp] theorem renEnv_vars (f : String → String) (σ : Env) (x : String) :
    (renEnv f σ).vars x = σ.vars x := rfl

@[simp] theorem renEnv_out (f : String → String) (σ : Env) : (renEnv f σ).out = σ.out := rfl

@[simp] theorem renEnv_inp (f : String → String) (σ : Env) : (renEnv f σ).inp = σ.inp := rfl

/-- **The renaming is free.** Every node of the syntax tree survives, so
the evaluation cost — which is what the whole cost model is read off —
is the one the landed proof charged. -/
@[simp] theorem renExpr_size (f : String → String) (e : Expr) :
    (renExpr f e).size = e.size := by
  induction e with
  | lit v => rfl
  | var x => rfl
  | get a i ih => simp [renExpr, Expr.size, ih]
  | bin op e g ihe ihg => simp [renExpr, Expr.size, ihe, ihg]

@[simp] theorem renCond_size (f : String → String) (b : Cond) :
    (renCond f b).size = b.size := by
  cases b <;> simp [renCond, Cond.size]

/-- **The two renamings cancel.** Reading the renamed expression in `σ`
is reading the original in the pulled-back environment. -/
theorem renExpr_evalB {B : ℕ} (f : String → String) (e : Expr) (σ : Env) :
    (renExpr f e).evalB B σ = e.evalB B (renEnv f σ) := by
  induction e generalizing σ with
  | lit v => rfl
  | var x => rfl
  | get a i ih => simp [renExpr, Expr.evalB, ih]
  | bin op e g ihe ihg => simp [renExpr, Expr.evalB, ihe, ihg]

theorem renCond_evalB {B : ℕ} (f : String → String) (b : Cond) (σ : Env) :
    (renCond f b).evalB B σ = b.evalB B (renEnv f σ) := by
  cases b <;> simp [renCond, Cond.evalB, renExpr_evalB]

theorem renEnv_involutive {f : String → String} (hf : ∀ z, f (f z) = z) (σ : Env) :
    renEnv f (renEnv f σ) = σ := by
  cases σ
  simp only [renEnv, Env.mk.injEq, true_and, and_true]
  funext a
  rw [hf]

theorem renEnv_setVar (f : String → String) (σ : Env) (x : String) (v : ℕ) :
    renEnv f (σ.setVar x v) = (renEnv f σ).setVar x v := rfl

theorem renEnv_setArr {f : String → String} (hf : ∀ z, f (f z) = z) (σ : Env)
    (a : String) (k v : ℕ) :
    renEnv f (σ.setArr a k v) = (renEnv f σ).setArr (f a) k v := by
  simp only [renEnv, Env.setArr]
  congr 1
  funext b
  by_cases hb : f b = a
  · have hb' : b = f a := by rw [← hb, hf]
    rw [if_pos hb, if_pos hb', hf]
  · have hb' : b ≠ f a := fun h => hb (by rw [h, hf])
    rw [if_neg hb, if_neg hb']

/-- **The transport.** A run of `c` is a run of the renamed `c` in the
pulled-back environment, *at the same cost*. The induction is over the
derivation and every case is the corresponding cancellation lemma
above. -/
theorem renCom_bigStepB {B : ℕ} {f : String → String} (hf : ∀ z, f (f z) = z)
    {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    BigStepB B (renCom f c) (renEnv f σ) (renEnv f σ') k := by
  induction h with
  | skip => rw [renCom]; exact BigStepB.skip
  | @assign σ₀ x e v he =>
      rw [renCom, renEnv_setVar]
      have he' : (renExpr f e).evalB B (renEnv f σ₀) = some v := by
        rw [renExpr_evalB, renEnv_involutive hf]; exact he
      simpa only [renExpr_size] using BigStepB.assign (B := B) (x := x) he'
  | @store σ₀ a i e kk v hi he hk =>
      rw [renCom, renEnv_setArr hf]
      have hi' : (renExpr f i).evalB B (renEnv f σ₀) = some kk := by
        rw [renExpr_evalB, renEnv_involutive hf]; exact hi
      have he' : (renExpr f e).evalB B (renEnv f σ₀) = some v := by
        rw [renExpr_evalB, renEnv_involutive hf]; exact he
      have hk' : kk < ((renEnv f σ₀).arrs (f a)).length := by rw [renEnv_arrs, hf]; exact hk
      simpa only [renExpr_size] using BigStepB.store (B := B) hi' he' hk'
  | seq _ _ ih ih' => rw [renCom]; exact BigStepB.seq ih ih'
  | @ite_true b c d σ₀ σ₁ kk hb _ ih =>
      rw [renCom]
      have hb' : (renCond f b).evalB B (renEnv f σ₀) = some true := by
        rw [renCond_evalB, renEnv_involutive hf]; exact hb
      simpa only [renCond_size] using BigStepB.ite_true hb' ih
  | @ite_false b c d σ₀ σ₁ kk hb _ ih =>
      rw [renCom]
      have hb' : (renCond f b).evalB B (renEnv f σ₀) = some false := by
        rw [renCond_evalB, renEnv_involutive hf]; exact hb
      simpa only [renCond_size] using BigStepB.ite_false hb' ih
  | @while_true b c σ₀ σ₁ σ₂ kk kk' hb _ _ ih ih' =>
      rw [renCom] at ih' ⊢
      have hb' : (renCond f b).evalB B (renEnv f σ₀) = some true := by
        rw [renCond_evalB, renEnv_involutive hf]; exact hb
      simpa only [renCond_size] using BigStepB.while_true hb' ih ih'
  | @while_false b c σ₀ hb =>
      rw [renCom]
      have hb' : (renCond f b).evalB B (renEnv f σ₀) = some false := by
        rw [renCond_evalB, renEnv_involutive hf]; exact hb
      simpa only [renCond_size] using BigStepB.while_false (c := renCom f c) hb'
  | @read σ₀ x v rest h => rw [renCom]; exact BigStepB.read (B := B) (x := x) h
  | @write σ₀ e v he =>
      rw [renCom]
      have he' : (renExpr f e).evalB B (renEnv f σ₀) = some v := by
        rw [renExpr_evalB, renEnv_involutive hf]; exact he
      simpa only [renExpr_size] using BigStepB.write (B := B) he'

theorem renCom_run {B : ℕ} {f : String → String} (hf : ∀ z, f (f z) = z)
    {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) :
    Run B (renCom f c) (renEnv f σ) (renEnv f σ') K := by
  obtain ⟨k, hk, hbs⟩ := h
  exact ⟨k, hk, renCom_bigStepB hf hbs⟩

/-- **The transport at the interface.** Any landed `Spec` becomes a
`Spec` for the renamed program, with pre- and postcondition read in the
pulled-back environment and the charge unchanged. -/
theorem renCom_spec {B : ℕ} {f : String → String} (hf : ∀ z, f (f z) = z)
    {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ} (h : Spec B P c Q K) :
    Spec B (fun σ => P (renEnv f σ)) (renCom f c)
      (fun σ σ' => Q (renEnv f σ) (renEnv f σ')) K := by
  intro σ hσ
  obtain ⟨τ, hrun, hq⟩ := h _ hσ
  refine ⟨renEnv f τ, ?_, ?_⟩
  · have := renCom_run (f := f) hf hrun
    rwa [renEnv_involutive hf] at this
  · show Q (renEnv f σ) (renEnv f (renEnv f τ))
    rwa [renEnv_involutive hf]

/-! #### The frames of a renamed program -/

@[simp] theorem renCom_wvars (f : String → String) (c : Com) :
    (renCom f c).wvars = c.wvars := by
  induction c with
  | skip => rfl
  | assign x e => rfl
  | store a i e => rfl
  | seq c d ihc ihd => simp [renCom, Com.wvars, ihc, ihd]
  | ite b c d ihc ihd => simp [renCom, Com.wvars, ihc, ihd]
  | «while» b c ih => simp [renCom, Com.wvars, ih]
  | read x => rfl
  | write e => rfl

theorem renCom_warrs (f : String → String) (c : Com) :
    (renCom f c).warrs = c.warrs.map f := by
  induction c with
  | skip => rfl
  | assign x e => rfl
  | store a i e => rfl
  | seq c d ihc ihd => simp [renCom, Com.warrs, ihc, ihd]
  | ite b c d ihc ihd => simp [renCom, Com.warrs, ihc, ihd]
  | «while» b c ih => simp [renCom, Com.warrs, ih]
  | read x => rfl
  | write e => rfl

/-- **What the renamed program may write**, in the form a frame
condition consumes: `a` is written only if the *pulled-back* name is
written by the original. -/
theorem mem_renCom_warrs {f : String → String} (hf : ∀ z, f (f z) = z) (c : Com)
    {a : String} (ha : a ∈ (renCom f c).warrs) : f a ∈ c.warrs := by
  rw [renCom_warrs, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  rwa [hf]

theorem renCom_noWrite (f : String → String) : ∀ {c : Com}, c.NoWrite → (renCom f c).NoWrite
  | .skip, _ => by rw [renCom, Com.NoWrite]; trivial
  | .assign _ _, _ => by rw [renCom, Com.NoWrite]; trivial
  | .store _ _ _, _ => by rw [renCom, Com.NoWrite]; trivial
  | .read _, _ => by rw [renCom, Com.NoWrite]; trivial
  | .write _, h => by rw [Com.NoWrite] at h; exact absurd h id
  | .seq c d, h => by
      rw [Com.NoWrite] at h
      rw [renCom, Com.NoWrite]
      exact ⟨renCom_noWrite f h.1, renCom_noWrite f h.2⟩
  | .ite b c d, h => by
      rw [Com.NoWrite] at h
      rw [renCom, Com.NoWrite]
      exact ⟨renCom_noWrite f h.1, renCom_noWrite f h.2⟩
  | .while b c, h => by
      rw [Com.NoWrite] at h
      rw [renCom, Com.NoWrite]
      exact renCom_noWrite f h

/-! #### The involution the engine is renamed along -/

/-- Exchange `"alv"` with `av`, fix everything else. -/
def maskSwap (av : String) : String → String :=
  fun z => if z = "alv" then av else if z = av then "alv" else z

/-- **The swap is its own inverse**, which is what makes the two
renamings cancel. -/
theorem maskSwap_invol (av : String) (z : String) : maskSwap av (maskSwap av z) = z := by
  unfold maskSwap
  by_cases h : z = "alv"
  · subst h
    by_cases hav : av = "alv" <;> simp [hav]
  · by_cases hz : z = av <;> simp [h, hz]

@[simp] theorem maskSwap_alv (av : String) : maskSwap av "alv" = av := by simp [maskSwap]

theorem maskSwap_of_ne {av a : String} (h₁ : a ≠ "alv") (h₂ : a ≠ av) :
    maskSwap av a = a := by simp [maskSwap, h₁, h₂]

/-! ### §6 The engine at a named mask array

**The names the engine holds, and why the hypothesis is real.** The
active-set pass writes `"exc"`, `"dist"`, `"q"` and `"qd"`
(`Refine.ScatterDeadPass.warrs_scatBlockCom`) and reads `"off"`, `"tgt"`
and `"mem"` beside its mask. A mask array that is none of those seven
can be read *where it lies*: nothing the engine does disturbs it, and
nothing it reads is disturbed by pointing the mask elsewhere. Any of the
seven would alias — the caller's mask would be the engine's own scratch
— so the specification below carries the hypothesis rather than leaning
on the one instantiation that happens to satisfy it. -/

/-- **A mask array the engine may read in place**: none of the seven
names the pass itself holds. -/
def MaskFree (av : String) : Prop :=
  av ≠ "off" ∧ av ≠ "tgt" ∧ av ≠ "mem" ∧ av ≠ "dist" ∧ av ≠ "q" ∧ av ≠ "qd" ∧ av ≠ "exc"

/-- **The active-set pass, reading its mask out of `av`.** The landed
program with `"alv"` exchanged for `av`, and nothing else moved. Because
it is a renaming and not a rewrite, `renCom_spec` carries the landed
walk across whole: no clause of the search, the mark or the scan is
re-proved, and the charge is the same numeral. -/
def scatBlockComA (av : String) (r t : ℕ) : Com := renCom (maskSwap av) (scatBlockCom r t)

theorem wvars_scatBlockComA (av : String) (r t : ℕ) :
    (scatBlockComA av r t).wvars = (scatBlockCom r t).wvars := renCom_wvars _ _

theorem mem_warrs_scatBlockComA {av : String} {r t : ℕ} {a : String}
    (ha : a ∈ (scatBlockComA av r t).warrs) : maskSwap av a ∈ (scatBlockCom r t).warrs :=
  mem_renCom_warrs (maskSwap_invol av) _ ha

theorem noWrite_scatBlockComA {av : String} {r t : ℕ} (h : (scatBlockCom r t).NoWrite) :
    (scatBlockComA av r t).NoWrite := renCom_noWrite _ h

end Lax3Proofs.Refine.ScatterBlock
