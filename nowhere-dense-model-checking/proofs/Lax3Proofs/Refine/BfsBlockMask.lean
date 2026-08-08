import Lax3Proofs.Refine.BfsBlock

/-!
# The block search's distance contract, at the mask's support

`BfsBlock`'s clean-in/clean-out contract asks for the **whole** distance
array:

    σ.arrs "dist" = arrOf n (fun _ => d + 1),

and that whole-array clause is the last carrier-sized thing in the
atom's charge. `RamDriver.scatDeadCom` pays `fillCom "dist" (r + 1)` —
`11 n + 6` per atom — for no reason but to establish it, and
`ScatterDeadPass.dist_touched_only_refuted` records the refutation of the
touched-only fill *against this clause* together with the verdict that
"the clause would have to be narrowed to the mask's support, and that is
the engine's own contract". This file is that narrowing.

### Why the clause is stronger than the engine needs

Read the program text. `RamBfs.scanSlot` tests the mask **first**:

    .assign "w" (.get "tgt" (.var "j"))
    .ite (.lt (.lit 0) (.get "alv" (.var "w")))
          (.ite (.lt (.var "dn") (.get "dist" (.var "w"))) …)

so the relaxation reads `dist[w]` only at a masked-alive `w`.
`RamBfs.expandRow` reads `dist[v]` only for a `v` taken off the queue,
and `Frontier.qmem` pins every queue entry as alive. `BfsBlock.unwindSlot`
reads `dist[u]` only for `u` on the queue. The one distance cell the
engine touches outside the mask is the **source's**, which
`Frontier.src` pins by name and `seedSrc` writes before anything reads
it.

So the engine never reads an unmasked cell, and the contract should not
speak about one.

### What narrows, and what does not

Exactly two clauses of the frontier invariant carry the whole array:
`cap` and `sound`. Everything else is already mask-scoped or
queue-scoped — `qall` carries `M w ≠ 0` in the landed statement, which is
the evidence that the rest can. `exp` quantifies over `MAdj G M (Q i) w`,
and `MAdj.alive_right` makes it mask-scoped for free. `src` is about the
source and stays whole, because the program writes that cell
unconditionally.

### The two obstructions, and their verdicts

**§2 compiles both, at one state**, and that state is not artificial: it
is what a search leaves when the source is alive and every neighbour of
it is dead.

* `frontier_cap_refuted` — an unmasked cell may hold junk *above* the
  sentinel, so the landed `cap` is false.
* `frontier_sound_refuted` — **the sharp one.** An unmasked cell may hold
  junk *below the cap*, and then the landed `sound` demands a walk to a
  vertex the arena cannot reach. `sound` is not merely unprovable at a
  dead vertex; it is false there. So the narrowing is forced by the data
  and not chosen by the proof, exactly as `capped_exp_is_forced` forces
  §7's guard.
* `frontierM_holds` — and every narrowed clause holds at that same
  state. Satisfiability, not only refutation.

The verdict on the seeds (obstruction 2) is `frontierM_seed_alive` /
`_dead`: the dead-vertex argument the landed seeds make — "if `D z ≤ d`
then `z = s`, read off the fill at *every* `z`" — is never needed once
`cap` and `sound` are mask-scoped, and the dead **source** is carried by
`src` and by `qall`'s pre-existing mask guard. The seeds keep their
shape; only their hypothesis and two clauses narrow.

The verdict on the unwind (obstruction 1) is `unwindM_run`: the trail
clause `∀ j, ri ≤ j → j < tf → D' (Q j) = D (Q j)` names no mask at all,
so queue injectivity carries it across the narrowing untouched. What
changes is the *exit*: the array is no longer a known literal list, and
the exit clause becomes the same mask-scoped shape as the entry.
`cleanOn_not_literal` is the compiled refutation that it cannot be
anything stronger.

### It is a weakening

`frontierM_of_frontier`, `distClean_of_arrOf` and `unwindInvM_of_unwindInv`
read every landed form as an instance of the narrowed one, so a landed
consumer crosses the seam in one line and nothing downstream moves this
wave. That is what keeps the build green while the atom still runs
`fillCom`.
-/

namespace Lax3Proofs.Refine.BfsBlockMask

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.Refine.BfsBlock

variable {n ns nt d s : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}

/-! ### §1 The narrowed clause, and its packaging

The whole-array clause is an equation between lists. The narrowed one
cannot be: the cells off the mask hold whatever the caller left there,
so the array is named by an existential and constrained only on the
support. This is E-mem's `LevelPre` packaging, and it is lossless for the
same reason — the witness is pinned by the array at every index that
exists (`distClean_unique`). -/

/-- **Clean on the mask's support.** Every *live* cell of the carrier
holds the sentinel; nothing is claimed anywhere else. -/
def CleanOn (n d : ℕ) (M D₀ : ℕ → ℕ) : Prop := ∀ z, z < n → M z ≠ 0 → D₀ z = d + 1

/-- **The narrowed distance clause**, packaged. The array has the
carrier's physical length and holds the sentinel on the mask's support.

There is deliberately **no tail conjunct**: a clause about the cells off
the support would be a statement the caller has to walk the carrier to
establish, which is the very pass this line of work exists to delete. -/
def DistClean (n d : ℕ) (M : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ D₀, σ.arrs "dist" = arrOf n D₀ ∧ CleanOn n d M D₀

/-- **The landed whole-array clause is an instance.** This is the bridge
every landed caller crosses, and it is one line. -/
theorem distClean_of_arrOf {σ : Env} (h : σ.arrs "dist" = arrOf n (fun _ => d + 1)) :
    DistClean n d M σ :=
  ⟨fun _ => d + 1, h, fun _ _ _ => rfl⟩

/-- **The packaging is lossless.** Two witnesses for the same array agree
at every index the array has, so the existential hides nothing: it names
the array's own content and no more. -/
theorem distClean_unique {σ : Env} {D₀ D₁ : ℕ → ℕ} (h₀ : σ.arrs "dist" = arrOf n D₀)
    (h₁ : σ.arrs "dist" = arrOf n D₁) : ∀ z < n, D₀ z = D₁ z := by
  intro z hz
  have h : arrOf n D₀ = arrOf n D₁ := by rw [← h₀, h₁]
  have e₀ : (arrOf n D₀).getD z 0 = D₀ z := getD_arrOf D₀ hz
  have e₁ : (arrOf n D₁).getD z 0 = D₁ z := getD_arrOf D₁ hz
  rw [← e₀, ← e₁, h]

/-- **The `n = 0` control.** At the empty carrier the narrowed clause is
the array's length and nothing else — it constrains no cell, because
there is no cell. A tail conjunct would have had to say something here,
which is the tell that it is a carrier walk in disguise. -/
theorem distClean_zero {σ : Env} (h : σ.arrs "dist" = arrOf 0 (fun _ => 0)) :
    DistClean 0 d M σ :=
  ⟨fun _ => 0, h, fun z hz => absurd hz (by omega)⟩

/-- And at the empty carrier the narrowed clause is *strictly* weaker
than nothing at all only in the length: any `D₀` witnesses it. -/
theorem cleanOn_zero (d : ℕ) (M D₀ : ℕ → ℕ) : CleanOn 0 d M D₀ :=
  fun z hz => absurd hz (by omega)

/-! ### §2 The two obstructions, compiled — refutation and satisfiability
at one state

Three vertices. The source `0` is alive; `1` and `2` are dead. The
member-driven fill wrote the sentinel `d + 1 = 1` at the one live cell
and left the other two holding whatever was there — `7` at vertex `1`,
and, the case that matters, `0` at vertex `2`.

This is a state a real search leaves: the source is alive, its
neighbours are all dead, so the ball is `{0}`, the queue holds the source
alone and has been expanded. -/

/-- The mask: vertex `0` alive, `1` and `2` dead. -/
private def maskM : ℕ → ℕ := fun z => if z = 0 then 1 else 0

/-- The distance array a mask-scoped fill leaves, after the seed writes
the source's cell: the sentinel at the one live vertex, and junk at the
two dead ones — junk *above* the cap at `1`, and junk *below* it at `2`. -/
private def maskD : ℕ → ℕ := fun z => if z = 0 then 0 else if z = 1 then 7 else 0

/-- The queue: the source alone. -/
private def maskQ : ℕ → ℕ := fun _ => 0

private theorem maskM_eq_zero_of_ne {z : ℕ} (hz : z ≠ 0) : maskM z = 0 := by
  simp [maskM, hz]

private theorem eq_zero_of_maskM {z : ℕ} (h : maskM z ≠ 0) : z = 0 := by
  by_contra hz; exact h (maskM_eq_zero_of_ne hz)

/-- **The mask-scoped fill is a fill**: the state above satisfies the
narrowed clause, at the sentinel `d + 1 = 1` and cap `d = 0`. -/
theorem cleanOn_maskD : CleanOn 3 0 maskM (fun z => if z = 0 then 1 else maskD z) := by
  intro z _ hm
  rw [eq_zero_of_maskM hm]
  simp

/-- **Obstruction 2, first half: the landed `cap` is false.** An unmasked
cell may hold junk above the sentinel, and nothing in the engine stops
it — the engine never looks. -/
theorem frontier_cap_refuted : ¬ (∀ w < 3, maskD w ≤ 0 + 1) := by
  intro h
  have := h 1 (by omega)
  simp [maskD] at this

/-- **Obstruction 2, second half — the sharp one: the landed `sound` is
false.** An unmasked cell may hold junk *below* the cap, and then `sound`
demands a walk of the arena from the source to a vertex the arena cannot
reach at all. This is why the narrowing is forced by the program's data
and not chosen for the proof's convenience: `sound` at a dead vertex is
not merely unavailable, it is refuted. -/
theorem frontier_sound_refuted :
    ¬ (∀ w < 3, maskD w ≤ 0 →
        WD (⊤ : SimpleGraph (Fin 3)) maskM (maskD w) 0 w) := by
  intro h
  have hw : maskD 2 = 0 := by simp [maskD]
  have hwd := h 2 (by omega) (by omega)
  rw [hw] at hwd
  exact absurd hwd.eq_of_zero (by omega)

/-- **Obstruction 1, the exit: the narrowed clean-out cannot be a literal
list.** A state clean on the mask's support need not be — and here is
not — the array the whole-array clause names. So the exit clause of the
unwind has to take the entry's mask-scoped shape; there is no stronger
form to aim at. -/
theorem cleanOn_not_literal :
    CleanOn 3 0 maskM (fun z => if z = 0 then 1 else maskD z) ∧
      arrOf 3 (fun z => if z = 0 then 1 else maskD z) ≠ arrOf 3 (fun _ => 0 + 1) := by
  refine ⟨cleanOn_maskD, fun h => ?_⟩
  have := congrArg (fun l => List.getD l 1 0) h
  simp [getD_arrOf (fun z => if z = 0 then 1 else maskD z) (show 1 < 3 by omega),
    getD_arrOf (fun _ : ℕ => 0 + 1) (show 1 < 3 by omega), maskD] at this

/-! ### §3 The frontier invariant at the mask's support

`RamBfs.Frontier` with two clauses narrowed and no others. Every other
clause is the landed one, character for character: `qall` already carried
`M w ≠ 0`, `exp` gets it from `MAdj.alive_right`, and the queue clauses
speak only of entries, which `qmem` pins alive. -/

variable {D Q : ℕ → ℕ} {head tail : ℕ}

/-- **The frontier invariant, mask-scoped.** -/
structure FrontierM {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d s : ℕ)
    (D Q : ℕ → ℕ) (head tail : ℕ) : Prop where
  /-- Nothing **the engine can read** exceeds the sentinel. -/
  cap : ∀ w < n, M w ≠ 0 → D w ≤ d + 1
  /-- The source is at distance zero, alive or not. This one stays whole:
  the program writes that cell unconditionally. -/
  src : D s = 0
  /-- A written distance **at a live cell** is achieved by a walk. -/
  sound : ∀ w < n, M w ≠ 0 → D w ≤ d → WD G M (D w) s w
  /-- The queue is a segment. -/
  hd : head ≤ tail
  /-- It holds vertices. -/
  tl : tail ≤ n
  /-- Everything on it is a discovered live vertex. -/
  qmem : ∀ i < tail, Q i < n ∧ D (Q i) ≤ d ∧ M (Q i) ≠ 0
  /-- Every discovered live vertex is on it. **Landed, unchanged** — the
  mask guard was already here, and it is what makes the rest narrow. -/
  qall : ∀ w < n, M w ≠ 0 → D w ≤ d → ∃ i < tail, Q i = w
  /-- Nothing is on it twice. -/
  qinj : ∀ i < tail, ∀ j < tail, Q i = Q j → i = j
  /-- It is sorted by distance. -/
  qmono : ∀ i j, i ≤ j → j < tail → D (Q i) ≤ D (Q j)
  /-- It spans at most one level beyond whatever is still pending. -/
  qcap : ∀ i < tail, ∀ j, head ≤ j → j < tail → D (Q i) ≤ D (Q j) + 1
  /-- Everything before `head` has had its whole block looked at. Mask-scoped
  already: `MAdj.alive_right` makes `w` live. -/
  exp : ∀ i < head, ∀ w, MAdj G M (Q i) w → D w ≤ D (Q i) + 1

namespace FrontierM

/-- **The landed invariant is an instance.** Both changes are weakenings —
each narrowed clause simply drops the unmasked cells — so nothing about
the whole-array engine is lost, and every landed walk crosses the seam
here. -/
theorem _root_.Lax3Proofs.Refine.BfsBlockMask.frontierM_of_frontier
    (hF : Frontier G M d s D Q head tail) : FrontierM G M d s D Q head tail where
  cap w hw _ := hF.cap w hw
  src := hF.src
  sound w hw _ := hF.sound w hw
  hd := hF.hd
  tl := hF.tl
  qmem := hF.qmem
  qall := hF.qall
  qinj := hF.qinj
  qmono := hF.qmono
  qcap := hF.qcap
  exp := hF.exp

/-- **There is room for one more**, verbatim from the landed proof: it
reads `qmem` and `qinj` only, and neither moved. -/
theorem tail_lt (hF : FrontierM G M d s D Q head tail) {w : ℕ} (hw : w < n)
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

/-- **The one change the arrays ever undergo**, mask-scoped. The landed
`RamBfs.Frontier.relax`, clause for clause: the cell written is `w`,
which `MAdj.alive_right` makes live, so the two narrowed clauses are
discharged exactly where the landed ones were and the mask hypothesis is
carried, never consumed. -/
theorem relax (hF : FrontierM G M d s D Q head tail) (hht : head < tail)
    {w : ℕ} (hadj : MAdj G M (Q head) w) (hlt : D (Q head) + 1 < D w) :
    FrontierM G M d s (upd D w (D (Q head) + 1)) (upd Q tail w) head (tail + 1) := by
  obtain ⟨hvn, hdv, hmv⟩ := hF.qmem head hht
  have hw : w < n := hadj.lt_right
  have hmw : M w ≠ 0 := hadj.alive_right
  have hdw : D w ≤ d + 1 := hF.cap w hw hmw
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
  refine ⟨fun z hz hmz => ?_, ?_, fun z hz hmz hzd => ?_, by omega, by omega, fun i hi => ?_,
    fun z hz hmz hzd => ?_, fun i hi j hj hij => ?_, fun i j hij hj => ?_,
    fun i hi j hj₁ hj₂ => ?_, fun i hi z hz => ?_⟩
  · by_cases hzw : z = w
    · rw [hzw, upd_self]; omega
    · rw [upd_of_ne _ hzw]; exact hF.cap z hz hmz
  · rw [upd_of_ne _ hws]; exact hF.src
  · by_cases hzw : z = w
    · subst hzw
      rw [upd_self]
      exact (hF.sound _ hvn hmv hdv).step hadj
    · rw [upd_of_ne _ hzw] at hzd ⊢; exact hF.sound z hz hmz hzd
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
  · have hit : i ≠ tail := by omega
    rw [upd_of_ne _ hit] at hz ⊢
    rw [upd_of_ne _ (hnq i (by omega))]
    by_cases hzw : z = w
    · exfalso
      have h₁ := hF.exp i hi w (by rw [← hzw]; exact hz)
      have h₂ := hF.qmono i head (by omega) hht
      omega
    · rw [upd_of_ne _ hzw]; exact hF.exp i hi z hz

/-- **The exit argument**, verbatim from the landed proof: it reads
`src`, `qall` and `exp` and none of the three moved. -/
theorem complete (hF : FrontierM G M d s D Q tail tail) :
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
        have hstep := hF.exp i hi w (by rw [hQi]; exact hcw)
        rw [hQi] at hstep
        omega

/-- **What the search computes**, at the landed threshold form, read at a
live cell — which is the only kind of cell a consumer ever reads it at,
since every consumer reads it through the queue. -/
theorem dist_le_iff (hF : FrontierM G M d s D Q tail tail) {w : ℕ} (hw : w < n)
    (hmw : M w ≠ 0) {k : ℕ} (hk : k ≤ d) : D w ≤ k ↔ WD G M k s w :=
  ⟨fun h => (hF.sound w hw hmw (by omega)).mono h, hF.complete k hk w⟩

end FrontierM

/-- **Satisfiability: every narrowed clause holds** at the state §2's two
refutations are read off. The refutations are therefore about the landed
clauses and not about the state — this is the pair the campaign's rule
asks for. -/
theorem frontierM_holds :
    FrontierM (⊤ : SimpleGraph (Fin 3)) maskM 0 0 maskD maskQ 1 1 := by
  refine ⟨fun w hw hmw => ?_, by simp [maskD], fun w hw hmw hwd => ?_, le_rfl, by omega,
    fun i hi => ?_, fun w hw hmw hwd => ?_, fun i hi j hj hij => by omega,
    fun i j hij hj => le_rfl, fun i hi j hj₁ hj₂ => by omega, fun i hi w hadj => ?_⟩
  · rw [eq_zero_of_maskM hmw]; simp [maskD]
  · rw [eq_zero_of_maskM hmw]
    have h0 : maskD 0 = 0 := by simp [maskD]
    rw [h0]
    exact WD.refl _ _ _ (by omega)
  · have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨by simp [maskQ], by simp [maskQ, maskD], by simp [maskQ, maskM]⟩
  · exact ⟨0, by omega, by rw [eq_zero_of_maskM hmw]; simp [maskQ]⟩
  · rw [eq_zero_of_maskM hadj.alive_right]
    simp [maskQ, maskD]

/-! ### §4 The seeds, at a mask-scoped fill

This is obstruction 2's verdict, executed. `RamBfs.frontier_seed_alive`
and `_dead` argue "a cell below the cap belongs to the source" from
`hg : ∀ j < n, g j = d + 1` at **every** `j`, dead ones included, because
the landed `cap` and `sound` demand the conclusion at every `j`. Narrowed,
both the hypothesis and the two clauses lose the dead cells together, and
the argument is available exactly where it is still asked for.

The dead **source** is the case worth naming: `frontierM_seed_dead`'s
`sound` and `qall` are asked only at live `z`, and a live `z` is not the
source, so the fill is available at every `z` the clause reaches. -/

/-- A live source goes on the queue. -/
theorem frontierM_seed_alive (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d : ℕ) (hs : s < n)
    (hms : M s ≠ 0) {g Q : ℕ → ℕ} (hg : ∀ j < n, M j ≠ 0 → g j = d + 1) (hQ : Q 0 = s) :
    FrontierM G M d s (upd g s 0) Q 0 1 := by
  have hval : ∀ z, z < n → M z ≠ 0 → z ≠ s → upd g s 0 z = d + 1 :=
    fun z hz hmz hzs => by rw [upd_of_ne _ hzs]; exact hg z hz hmz
  refine ⟨fun z hz hmz => ?_, upd_self .., fun z hz hmz hzd => ?_, by omega, by omega,
    fun i hi => ?_, fun z hz hmz hzd => ?_, fun i hi j hj hij => by omega,
    fun i j hij hj => ?_, fun i hi j hj₁ hj₂ => ?_, fun i hi => absurd hi (by omega)⟩
  · by_cases hzs : z = s
    · rw [hzs, upd_self]; omega
    · rw [hval z hz hmz hzs]
  · have hzs : z = s := by
      by_contra hne; rw [hval z hz hmz hne] at hzd; omega
    subst hzs
    rw [upd_self]
    exact WD.refl G M 0 hs
  · have hi0 : i = 0 := by omega
    rw [hi0, hQ, upd_self]
    exact ⟨hs, by omega, hms⟩
  · have hzs : z = s := by
      by_contra hne; rw [hval z hz hmz hne] at hzd; omega
    exact ⟨0, by omega, by rw [hQ, hzs]⟩
  · have : i = 0 ∧ j = 0 := by omega
    rw [this.1, this.2]
  · have : i = 0 ∧ j = 0 := by omega
    rw [this.1, this.2]; omega

/-- A dead source does not. Note where the mask hypothesis lands: the two
clauses that ask about a cell are asked only at a **live** `z`, and a
live `z` is not this source, so the narrowed fill covers every cell they
reach. -/
theorem frontierM_seed_dead (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d : ℕ) (hs : s < n)
    (hms : M s = 0) {g Q : ℕ → ℕ} (hg : ∀ j < n, M j ≠ 0 → g j = d + 1) :
    FrontierM G M d s (upd g s 0) Q 0 0 := by
  have hns : ∀ z, M z ≠ 0 → z ≠ s := by rintro z hmz rfl; exact hmz hms
  have hval : ∀ z, z < n → M z ≠ 0 → upd g s 0 z = d + 1 :=
    fun z hz hmz => by rw [upd_of_ne _ (hns z hmz)]; exact hg z hz hmz
  refine ⟨fun z hz hmz => ?_, upd_self .., fun z hz hmz hzd => ?_, by omega, by omega,
    fun i hi => absurd hi (by omega), fun z hz hmz hzd => ?_,
    fun i hi j hj hij => absurd hi (by omega), fun i j hij hj => absurd hj (by omega),
    fun i hi j hj₁ hj₂ => absurd hj₂ (by omega), fun i hi => absurd hi (by omega)⟩
  · rw [hval z hz hmz]
  · rw [hval z hz hmz] at hzd; omega
  · rw [hval z hz hmz] at hzd; omega

/-! ### §5 The unwind, at a mask-scoped entry

This is obstruction 1's verdict, executed. The trail clause — the fourth
— names no mask: it says the cells the walk has **not** reached still
hold what the search left there, and queue injectivity is what keeps it
alive when a cell is overwritten. Nothing in that argument reads the
distance array outside the queue, so it crosses the narrowing untouched.

What changes is the exit. The landed `unwind_run` proves the array comes
back as the *same literal list* by an `arrOf_congr` over every `i < n`;
mask-scoped, the cells the walk never visits keep whatever they came in
with, and they are exactly the cells the narrowed clause says nothing
about. So the exit takes the entry's shape, and `cleanOn_not_literal` is
the compiled proof that there is nothing stronger to aim at. -/

/-- The unwind's invariant, mask-scoped. Two clauses narrow — the same
two, for the same reason — and the two trail clauses do not. -/
def UnwindInvM (n nt d s tf : ℕ) (O T M D Q : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ D' QD,
    τ.vars "n" = n ∧ τ.vars "src" = s ∧ τ.vars "tail" = tf ∧
    τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf nt T ∧
    τ.arrs "alv" = arrOf n M ∧ τ.arrs "dist" = arrOf n D' ∧
    τ.arrs "q" = arrOf n Q ∧ τ.arrs "qd" = arrOf n QD ∧
    τ.vars "ri" ≤ tf ∧
    (∀ z, z < n → M z ≠ 0 → D' z ≤ d + 1) ∧
    (∀ z, z < n → M z ≠ 0 → D' z ≤ d → z = s ∨ ∃ j, τ.vars "ri" ≤ j ∧ j < tf ∧ Q j = z) ∧
    (∀ j, j < τ.vars "ri" → QD j = D (Q j)) ∧
    (∀ j, τ.vars "ri" ≤ j → j < tf → D' (Q j) = D (Q j))

/-- **The landed unwind invariant is an instance.** -/
theorem unwindInvM_of_unwindInv {tf : ℕ} {D Q : ℕ → ℕ} {τ : Env}
    (h : UnwindInv n nt d s tf O T M D Q τ) : UnwindInvM n nt d s tf O T M D Q τ := by
  obtain ⟨D', QD, hn, hsrc, htl, hoff, htgt, halv, hdist, hq, hqd, hri, hcap, hdisc,
    hcopy, hkeep⟩ := h
  exact ⟨D', QD, hn, hsrc, htl, hoff, htgt, halv, hdist, hq, hqd, hri,
    fun z hz _ => hcap z hz, fun z hz _ => hdisc z hz, hcopy, hkeep⟩

/-- **One entry of the trail, mask-scoped.** The queue's injectivity is
still what keeps the fourth clause alive, and the mask enters only
through the two narrowed clauses — the cell being overwritten is a queue
entry, which `hqm` pins live. -/
theorem unwindSlotM_run {B : ℕ} (hnB : n < B) (hdB : d + 1 < B) {tf : ℕ} (htf : tf ≤ n)
    {D Q : ℕ → ℕ} (hqn : ∀ i, i < tf → Q i < n)
    (hqm : ∀ i, i < tf → M (Q i) ≠ 0)
    (hqinj : ∀ i, i < tf → ∀ j, j < tf → Q i = Q j → i = j)
    (hDd : ∀ z, z < n → M z ≠ 0 → D z ≤ d + 1)
    {τ : Env} (hI : UnwindInvM n nt d s tf O T M D Q τ) (hlt : τ.vars "ri" < tf) :
    ∃ τ' K, Run B (unwindSlot d) τ τ' K ∧ K ≤ 30 ∧
      UnwindInvM n nt d s tf O T M D Q τ' ∧ τ'.vars "ri" = τ.vars "ri" + 1 := by
  obtain ⟨D', QD, hn, hsrc, htl, hoff, htgt, halv, hdist, hq, hqd, hri, hcap, hdisc,
    hcopy, hkeep⟩ := hI
  have hrin : τ.vars "ri" < n := by omega
  have hQn : Q (τ.vars "ri") < n := hqn _ hlt
  have hQm : M (Q (τ.vars "ri")) ≠ 0 := hqm _ hlt
  have hDkeep : D' (Q (τ.vars "ri")) = D (Q (τ.vars "ri")) := hkeep _ le_rfl hlt
  have hDB : D (Q (τ.vars "ri")) ≤ d + 1 := hDd _ hQn hQm
  have hrq : (τ.arrs "q").getD (τ.vars "ri") 0 = Q (τ.vars "ri") := by
    rw [hq, getD_arrOf Q hrin]
  have hrq' : (τ.arrs "q")[τ.vars "ri"]?.getD 0 = Q (τ.vars "ri") := by
    rw [← List.getD_eq_getElem?_getD]; exact hrq
  have hqlen : τ.vars "ri" < (τ.arrs "q").length := by rw [hq, length_arrOf]; exact hrin
  have hvB : (τ.arrs "q").getD (τ.vars "ri") 0 < B := by rw [hrq]; omega
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
  · -- nothing a reader can see exceeds the sentinel
    intro z hz hmz
    by_cases hzw : z = Q (τ.vars "ri")
    · rw [hzw, upd_self]
    · rw [upd_of_ne _ hzw]; exact hcap z hz hmz
  · -- a live cell still below the sentinel belongs to a later entry, or to the source
    intro z hz hmz hzd
    by_cases hzw : z = Q (τ.vars "ri")
    · rw [hzw, upd_self] at hzd; omega
    · rw [upd_of_ne _ hzw] at hzd
      rcases hdisc z hz hmz hzd with hs | ⟨j, hj₁, hj₂, hj₃⟩
      · exact Or.inl hs
      · refine Or.inr ⟨j, ?_, hj₂, hj₃⟩
        have hjne : j ≠ τ.vars "ri" := by rintro rfl; exact hzw hj₃.symm
        simp
        omega
  · -- the cells already passed have been copied out
    intro j hj
    simp at hj
    by_cases hjr : j = τ.vars "ri"
    · rw [hjr, upd_self]
    · rw [upd_of_ne _ hjr]; exact hcopy j (by omega)
  · -- **the trail clause**: the cell just overwritten is named by no later
    -- entry, and this is queue injectivity and nothing else. No mask
    -- occurs in this argument, which is why it crosses the narrowing whole.
    intro j hj₁ hj₂
    simp at hj₁
    have hjne : Q j ≠ Q (τ.vars "ri") := fun hqe =>
      absurd (hqinj j hj₂ (τ.vars "ri") hlt hqe) (by omega)
    rw [upd_of_ne _ hjne]
    exact hkeep j (by omega) hj₂

end Lax3Proofs.Refine.BfsBlockMask
