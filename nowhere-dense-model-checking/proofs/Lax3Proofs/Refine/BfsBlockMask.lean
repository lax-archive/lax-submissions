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
  have e₀ := getD_arrOf (fun z => if z = 0 then 1 else maskD z) (show (1 : ℕ) < 3 by omega)
  have e₁ := getD_arrOf (fun _ : ℕ => 0 + 1) (show (1 : ℕ) < 3 by omega)
  rw [h, e₁] at e₀
  simp [maskD] at e₀

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

/-- **The trail, walked.** The kit's counted loop, at the narrowed
invariant. Thirty-four per entry of the queue — the same numeral, because
this route changes no program text. -/
theorem unwindM_scan_spec {B : ℕ} (hnB : n < B) (hdB : d + 1 < B) {tf : ℕ} (htf : tf ≤ n)
    {D Q : ℕ → ℕ} (hqn : ∀ i, i < tf → Q i < n)
    (hqm : ∀ i, i < tf → M (Q i) ≠ 0)
    (hqinj : ∀ i, i < tf → ∀ j, j < tf → Q i = Q j → i = j)
    (hDd : ∀ z, z < n → M z ≠ 0 → D z ≤ d + 1) :
    Spec B (fun τ => UnwindInvM n nt d s tf O T M D Q τ ∧ τ.vars "ri" = 0)
      (Csr.scan "ri" "tail" (unwindSlot d))
      (fun _ τ' => UnwindInvM n nt d s tf O T M D Q τ' ∧ τ'.vars "ri" = tf)
      (34 * tf + 4) := by
  refine Csr.rowScan_spec B (34 * tf + 4) tf 30 "ri" "tail" (unwindSlot d)
    (UnwindInvM n nt d s tf O T M D Q) (by omega) (fun σ hσ => ?_) (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨D₁, QD₁, -, -, htl, -, -, -, -, -, -, hri, -⟩ := hσ
    exact ⟨htl, hri⟩
  · obtain ⟨σ', K', hr, hK, hI', hri'⟩ :=
      unwindSlotM_run hnB hdB htf hqn hqm hqinj hDd hσ hlt
    exact ⟨σ', K', hr, hI', hri', hK⟩

/-- **The unwind, end to end, at a mask-scoped entry.** This is
obstruction 1's verdict. The queue is walked and then the source's own
cell is restored unconditionally — the one cell the queue does not name.

What comes out is **not** the array that went in, and cannot be: the
cells off the mask's support were never read, never written, and were
never described. What comes out is the entry's own clause, `CleanOn`, and
`cleanOn_not_literal` is the proof that nothing stronger is available. -/
theorem unwindM_run {B : ℕ} (hs : s < n) (hnB : n < B) (hdB : d + 1 < B) {tf : ℕ}
    (htf : tf ≤ n) {D Q : ℕ → ℕ} (hqn : ∀ i, i < tf → Q i < n)
    (hqm : ∀ i, i < tf → M (Q i) ≠ 0)
    (hqinj : ∀ i, i < tf → ∀ j, j < tf → Q i = Q j → i = j)
    (hDd : ∀ z, z < n → M z ≠ 0 → D z ≤ d + 1)
    (hdisc0 : ∀ z, z < n → M z ≠ 0 → D z ≤ d → z = s ∨ ∃ j, j < tf ∧ Q j = z)
    {QD₀ : ℕ → ℕ} {τ : Env}
    (hn : τ.vars "n" = n) (hsrc : τ.vars "src" = s) (htl : τ.vars "tail" = tf)
    (hoff : τ.arrs "off" = arrOf (n + 1) O) (htgt : τ.arrs "tgt" = arrOf nt T)
    (halv : τ.arrs "alv" = arrOf n M) (hdist : τ.arrs "dist" = arrOf n D)
    (hq : τ.arrs "q" = arrOf n Q) (hqd : τ.arrs "qd" = arrOf n QD₀) :
    ∃ τ' K, Run B (unwind d) τ τ' K ∧ K ≤ 34 * tf + 14 ∧
      (∃ D₂, τ'.arrs "dist" = arrOf n D₂ ∧ CleanOn n d M D₂) ∧
      τ'.arrs "q" = arrOf n Q ∧
      ∃ QD, τ'.arrs "qd" = arrOf n QD ∧ ∀ j, j < tf → QD j = D (Q j) := by
  have hscanSpec := unwindM_scan_spec (n := n) (nt := nt) (d := d) (s := s) (O := O) (T := T)
    (M := M) (B := B) hnB hdB htf hqn hqm hqinj hDd (D := D) (Q := Q)
  run_vcg [hscanSpec]
  · -- what the loop left, plus the source's own cell
    rename_i w hpost
    obtain ⟨⟨D', QD, hn', hsrc', htl', hoff', htgt', halv', hdist', hq', hqd', hri',
      hcap', hdisc', hcopy', -⟩, hriend⟩ := hpost
    have hset : (w.setArr "dist" (w.vars "src") (d + 1)).arrs "dist"
        = arrOf n (upd D' s (d + 1)) := by
      simp [hdist', hsrc', set_arrOf_eq_upd]
    refine ⟨⟨upd D' s (d + 1), hset, ?_⟩, by simp [hq'], QD, by simp [hqd'],
      fun j hj => hcopy' j (by rw [hriend]; exact hj)⟩
    intro i hi hmi
    by_cases his : i = s
    · rw [his, upd_self]
    · rw [upd_of_ne _ his]
      have h₁ := hcap' i hi hmi
      have h₂ : ¬ D' i ≤ d := fun h => his (by
        rcases hdisc' i hi hmi h with h' | ⟨j, hj₁, hj₂, -⟩
        · exact h'
        · omega)
      omega
  · -- the loop starts at the top of the queue, in the state the assignment left
    refine ⟨⟨D, QD₀, by simp [hn], by simp [hsrc], by simp [htl], by simp [hoff],
      by simp [htgt], by simp [halv], by simp [hdist], by simp [hq], by simp [hqd],
      by simp, fun z hz hmz => hDd z hz hmz, fun z hz hmz hzd => ?_,
      fun j hj => by simp at hj, fun j _ _ => rfl⟩, by simp⟩
    rcases hdisc0 z hz hmz hzd with h | ⟨j, hj₁, hj₂⟩
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

/-! ### §6 The engine, at a mask-scoped entry

**No program text moves.** The seed, the search and the unwind are the
landed commands, character for character; only the contract narrows. So
the potential is the landed `BfsBlock.BallPot`, the per-turn release is
the landed one, and `bfsBlockK bw nb = 44 bw + 80 nb + 60` keeps its
numerals — there is nothing here that could move them. -/

/-- Everything on the queue is in the ball. Landed, at the narrowed
invariant: it reads `qmem` and `sound`, and `qmem` supplies exactly the
mask hypothesis `sound` now asks for. -/
theorem memM_of_queue (hF : FrontierM G M d s D Q head tail) {A : Finset ℕ}
    (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A) {i : ℕ} (hi : i < tail) : Q i ∈ A := by
  obtain ⟨hqn, hqd, hqm⟩ := hF.qmem i hi
  exact hA _ hqn hqm (WD.mono hqd (hF.sound _ hqn hqm hqd))

/-- **The queue is no longer than the ball.** -/
theorem tail_le_cardM (hF : FrontierM G M d s D Q head tail) {A : Finset ℕ}
    (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A) : tail ≤ A.card := by
  have hsub : (Finset.range tail).image Q ⊆ A := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    exact memM_of_queue hF hA (Finset.mem_range.1 hi)
  have hcard : ((Finset.range tail).image Q).card = tail := by
    rw [Finset.card_image_of_injOn fun i hi j hj hq =>
      hF.qinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hq]
    exact Finset.card_range tail
  have := Finset.card_le_card hsub
  omega

/-- **The blocks the search has scanned fit inside the ball's weight.** -/
theorem sum_rowLen_head_leM (hF : FrontierM G M d s D Q head tail) (hht : head ≤ tail)
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
  exact memM_of_queue hF hA (by have := Finset.mem_range.1 hi; omega)

/-- The block scan's invariant, at the narrowed frontier. -/
def ScanInvM {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (nt d s head v dv sc₀ : ℕ)
    (O T Q₀ : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ D Q, SearchEnv n nt s O T M D Q τ ∧ FrontierM G M d s D Q head (τ.vars "tail") ∧
    τ.vars "head" = head ∧ head < τ.vars "tail" ∧ Q head = v ∧ D v = dv ∧
    τ.vars "v" = v ∧ τ.vars "dv" = dv ∧ τ.vars "dn" = dv + 1 ∧
    τ.vars "jend" = O (v + 1) ∧ O v ≤ τ.vars "j" ∧ τ.vars "j" ≤ O (v + 1) ∧
    τ.vars "sc" = sc₀ + (τ.vars "j" - O v) ∧
    (∀ j', O v ≤ j' → j' < τ.vars "j" → M (T j') ≠ 0 → D (T j') ≤ dv + 1) ∧
    (∀ i < head, Q i = Q₀ i)

/-- **One slot of the block, at a mask-scoped entry.** The landed walk,
with one structural change and no others: the mask test is split
**before** `run_vcg` rather than inside it. That is the whole of what the
narrowing costs, and it is forced — the word bound on the relaxation's
read of `dist[w]` is available only at a live `w`, which is precisely the
branch the program's own first test has already taken. -/
theorem scanSlotM_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {head v dv sc₀ : ℕ} (hv : v < n) (hsc₀ : sc₀ + Csr.rowLen O v ≤ ns)
    {Q₀ : ℕ → ℕ} {τ : Env} (hI : ScanInvM G M nt d s head v dv sc₀ O T Q₀ τ)
    (hjlt : τ.vars "j" < O (v + 1)) :
    ∃ τ' K, Run B scanSlot τ τ' K ∧ K ≤ 40 ∧
      ScanInvM G M nt d s head v dv sc₀ O T Q₀ τ' ∧ τ'.vars "j" = τ.vars "j" + 1 := by
  obtain ⟨D, Q, ⟨hn, hsrc, hoff, htgt, halv, hdist, hq⟩, hF, hhead, hht, hqv, hDv, hvv,
    hdvv, hdnv, hje, hj₁, hj₂, hsc, hscan, hq₀⟩ := hI
  obtain ⟨hvn', hdvle, hmv⟩ := hF.qmem head hht
  rw [hqv] at hvn' hdvle hmv
  rw [hDv] at hdvle
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hjns : τ.vars "j" < ns := by omega
  have hwn : T (τ.vars "j") < n := hcsr.target_lt' hv hjlt
  have hrj : (τ.arrs "tgt").getD (τ.vars "j") 0 = T (τ.vars "j") := by
    rw [htgt, getD_arrOf T (by omega)]
  have hrj' : (τ.arrs "tgt")[τ.vars "j"]?.getD 0 = T (τ.vars "j") := by
    rw [← List.getD_eq_getElem?_getD]; exact hrj
  have hjlen : τ.vars "j" < (τ.arrs "tgt").length := by rw [htgt, length_arrOf]; omega
  have hwB : (τ.arrs "tgt").getD (τ.vars "j") 0 < B := by rw [hrj]; omega
  have halvlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "alv").length := by
    rw [hrj, halv, length_arrOf]; exact hwn
  have halvv : (τ.arrs "alv").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0
      = M (T (τ.vars "j")) := by rw [hrj, halv, getD_arrOf M hwn]
  have halvB : (τ.arrs "alv").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0 < B := by
    rw [halvv]; exact hMB _ hwn
  have hdistlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "dist").length := by
    rw [hrj, hdist, length_arrOf]; exact hwn
  have hdistv : (τ.arrs "dist").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0
      = D (T (τ.vars "j")) := by rw [hrj, hdist, getD_arrOf D hwn]
  have hqlen : (τ.arrs "q").length = n := by rw [hq, length_arrOf]
  have hscB : τ.vars "sc" + 1 < B := by omega
  have hjB : τ.vars "j" + 1 < B := by omega
  have hdnB : τ.vars "dn" < B := by omega
  have hMw : M (T (τ.vars "j")) < B := hMB _ hwn
  have htlB : τ.vars "tail" ≤ n := hF.tl
  have hbrAlv : ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "alv").getD
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0
      = M (T (τ.vars "j")) := by rw [arrs_setVar, vars_setVar]; simpa using halvv
  have hbrDist : ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "dist").getD
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0
      = D (T (τ.vars "j")) := by rw [arrs_setVar, vars_setVar]; simpa using hdistv
  have hbrDn : (τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "dn" = dv + 1 := by
    simpa using hdnv
  -- **the word bound the narrowing does not owe.** The relaxation reads
  -- `dist[w]` inside a *condition* guarded by the mask test, and the kit
  -- charges no word bound for a read in a condition -- which is why the
  -- landed `hdistB`, derivable only from the whole-array `cap`, is simply
  -- absent here and the three branches are otherwise the landed ones.
  have hroom : dv + 1 < D (T (τ.vars "j")) → τ.vars "tail" < n := by
    intro hlt'
    refine hF.tail_lt hwn ?_
    intro i hi hqi
    have hc := hF.qcap i hi head le_rfl hht
    rw [hqi, hqv, hDv] at hc
    omega
  have hvne : dv + 1 < D (T (τ.vars "j")) → v ≠ T (τ.vars "j") := by
    intro hlt' hve
    rw [← hve, hDv] at hlt'
    omega
  run_vcg
  · -- the slot names a live vertex, and it takes the offer
    have hmw : M (T (τ.vars "j")) ≠ 0 := by omega
    have hlt' : dv + 1 < D (T (τ.vars "j")) := by omega
    have hadj : MAdj G M (Q head) (T (τ.vars "j")) := by
      rw [hqv]; exact hcsr.madj_of_slot hv hj₁ hjlt hmv hmw
    have hltq : D (Q head) + 1 < D (T (τ.vars "j")) := by rw [hqv, hDv]; exact hlt'
    have hrelax := hF.relax hht hadj hltq
    rw [hqv, hDv] at hrelax
    refine ⟨⟨upd D (T (τ.vars "j")) (dv + 1), upd Q (τ.vars "tail") (T (τ.vars "j")),
      ⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt], by simp [halv],
        by simp [hdist, hrj', hdnv, set_arrOf_eq_upd],
        by simp [hq, hrj', set_arrOf_eq_upd]⟩,
      by simpa using hrelax, by simp [hhead], by simp; omega,
      (upd_of_ne _ (show head ≠ τ.vars "tail" by omega)).trans hqv,
      (upd_of_ne _ (hvne hlt')).trans hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_,
      fun i hi => (upd_of_ne _ (by omega)).trans (hq₀ i hi)⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    by_cases hje' : T j' = T (τ.vars "j")
    · rw [hje', upd_self]
    · rw [upd_of_ne _ hje']
      rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
      · exact hscan j' hj₁' hlt'' hmj'
      · exact absurd (show j' = τ.vars "j" by simp at hj₂'; omega)
          (by rintro rfl; exact hje' rfl)
  · -- live, but already at most one level below: nothing is written
    refine ⟨⟨D, Q, ⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩,
      by simpa using hF, by simp [hhead], by simp [hht], by simp [hqv], hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
    · exact hscan j' hj₁' hlt'' hmj'
    · have : j' = τ.vars "j" := by simp at hj₂'; omega
      subst this
      omega
  · -- a dead target is passed over, and its cell is never read
    refine ⟨⟨D, Q, ⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩,
      by simpa using hF, by simp [hhead], by simp [hht], by simp [hqv], hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
    · exact hscan j' hj₁' hlt'' hmj'
    · have : j' = τ.vars "j" := by simp at hj₂'; omega
      subst this
      omega
  · -- **the whole price of the narrowing, in one goal.** The relaxation's
    -- read of `dist[w]` must be a word, and the landed proof got that from
    -- the whole-array `cap`. Mask-scoped it is not available *before* the
    -- walk — but the kit does not ask for it before the walk. It asks here,
    -- **inside the branch the program's own mask test has already taken**,
    -- where `M (T j) ≠ 0` is a hypothesis and narrowed `cap` applies. This
    -- is the compiled form of "the engine never reads an unmasked cell".
    rw [hbrDist]
    have hmw : M (T (τ.vars "j")) ≠ 0 := by omega
    have := hF.cap _ hwn hmw
    omega


/-- **The whole block of `v`, scanned** — forty-four per slot, the landed
numeral. -/
theorem scanM_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {head v dv sc₀ : ℕ} (hv : v < n) (hsc₀ : sc₀ + Csr.rowLen O v ≤ ns) {Q₀ : ℕ → ℕ} :
    Spec B (fun τ => ScanInvM G M nt d s head v dv sc₀ O T Q₀ τ ∧ τ.vars "j" = O v)
      (Csr.scan "j" "jend" scanSlot)
      (fun _ τ' => ScanInvM G M nt d s head v dv sc₀ O T Q₀ τ' ∧ τ'.vars "j" = O (v + 1))
      (44 * Csr.rowLen O v + 4) := by
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  refine Csr.rowScan_spec B (44 * Csr.rowLen O v + 4) (O (v + 1)) 40 "j" "jend" scanSlot
    (ScanInvM G M nt d s head v dv sc₀ O T Q₀) (by omega) (fun σ hσ => ?_) (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨D, Q, -, -, -, -, -, -, -, -, -, hje, -, hjle, -, -, -⟩ := hσ
    exact ⟨hje, hjle⟩
  · obtain ⟨σ', K', hr, hK, hI', hj'⟩ :=
      scanSlotM_run hcsr hnB hnsB hnt hdB hMB hv hsc₀ hσ hlt
    exact ⟨σ', K', hr, hI', hj', hK⟩

/-- The search loop's invariant, at the narrowed frontier. -/
def DrainInvM {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (nt d s : ℕ) (O T : ℕ → ℕ)
    (τ : Env) : Prop :=
  ∃ D Q, SearchEnv n nt s O T M D Q τ ∧
    FrontierM G M d s D Q (τ.vars "head") (τ.vars "tail") ∧
    τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen O (Q i)

/-- **One turn**, at the narrowed invariant. The vertex dequeued is a
queue entry, so `qmem` supplies the mask hypothesis for the read of
`dist[v]` and nothing about the turn changes: `44 · rowLen + 30`, the
landed bound. -/
theorem expandRowM_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) {D Q : ℕ → ℕ} {τ : Env}
    (hse : SearchEnv n nt s O T M D Q τ)
    (hF : FrontierM G M d s D Q (τ.vars "head") (τ.vars "tail"))
    (hht : τ.vars "head" < τ.vars "tail")
    (hsum : τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen O (Q i)) :
    ∃ τ' K, Run B expandRow τ τ' K ∧ K ≤ 44 * Csr.rowLen O (Q (τ.vars "head")) + 30 ∧
      DrainInvM G M nt d s O T τ' ∧ τ'.vars "head" = τ.vars "head" + 1 ∧
      τ'.vars "sc" = τ.vars "sc" + Csr.rowLen O (Q (τ.vars "head")) := by
  obtain ⟨hn, hsrc, hoff, htgt, halv, hdist, hq⟩ := id hse
  have htln := hF.tl
  have hhn : τ.vars "head" < n := by omega
  obtain ⟨v, hvdef⟩ : ∃ v, Q (τ.vars "head") = v := ⟨_, rfl⟩
  rw [hvdef]
  obtain ⟨hvn, hdvd, hmv⟩ := hF.qmem _ hht
  rw [hvdef] at hvn hdvd hmv
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hov : O v ≤ O (v + 1) := hcsr.mono v hvn
  have hsc₀ : τ.vars "sc" + Csr.rowLen O v ≤ ns := by
    have hstep : ∑ i ∈ Finset.range (τ.vars "head" + 1), Csr.rowLen O (Q i) ≤ ns :=
      hcsr.sum_rowLen_queue (fun i hi => (hF.qmem i (by omega)).1)
        (fun i hi j hj hqe => hF.qinj i (by omega) j (by omega) hqe)
    rw [Finset.sum_range_succ, hvdef] at hstep
    omega
  have hcsrRel : CsrWide.CsrW "off" "tgt" n ns nt n O T τ :=
    ⟨hoff, htgt, fun i hi => hcsr.mono i hi, hcsr.last, hnt,
      fun p hp => hcsr.target_lt p hp⟩
  have hrv : (τ.arrs "q").getD (τ.vars "head") 0 = v := by
    rw [hq, getD_arrOf Q hhn, hvdef]
  have hrv' : (τ.arrs "q")[τ.vars "head"]?.getD 0 = v := by
    rw [← List.getD_eq_getElem?_getD]; exact hrv
  have hqlen : τ.vars "head" < (τ.arrs "q").length := by rw [hq, length_arrOf]; omega
  have hvB : (τ.arrs "q").getD (τ.vars "head") 0 < B := by rw [hrv]; omega
  have hdlen : ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v")
      < ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").length := by
    rw [arrs_setVar, vars_setVar, hdist, length_arrOf]; simpa [hrv'] using hvn
  have hdval : ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
      ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0 = D v := by
    rw [arrs_setVar, vars_setVar]
    simp only [hrv, hdist]
    exact getD_arrOf D hvn
  have hdval' : (τ.arrs "dist")[(τ.arrs "q")[τ.vars "head"]?.getD 0]?.getD 0 = D v := by
    rw [hrv', ← List.getD_eq_getElem?_getD, hdist, getD_arrOf D hvn]
  have hdB' : ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
      ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0 < B := by
    rw [hdval]; omega
  have hdvB : ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).setVar "dv"
      (((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
        ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0)).vars "dv" = D v := by
    simp [hdval']
  have hheadB : τ.vars "head" + 1 < B := by omega
  have hscanSpec : Spec B
      (fun σ => ScanInvM G M nt d s (τ.vars "head") v (D v) (τ.vars "sc") O T Q σ ∧
        σ.vars "j" = O v)
      (Csr.scan "j" "jend" scanSlot)
      (fun _ σ' => DrainInvM G M nt d s O T (σ'.setVar "head" (τ.vars "head" + 1)) ∧
        σ'.vars "head" = τ.vars "head" ∧
        σ'.vars "sc" = τ.vars "sc" + Csr.rowLen O v ∧ σ'.vars "head" + 1 < B)
      (44 * Csr.rowLen O v + 4) :=
    (scanM_spec hcsr hnB hnsB hnt hdB hMB hvn hsc₀ (Q₀ := Q)).post fun _ σ' _ hQ => by
      obtain ⟨⟨D', Q', hse', hF', hhead', hht', hqv', hDv', hvv', hdvv', hdnv', hje',
        hjge', hjle', hsc', hscanned, hq₀'⟩, hj₄⟩ := hQ
      obtain ⟨hn', hsrc', hoff', htgt', halv', hdist', hq'⟩ := id hse'
      have hscv : σ'.vars "sc" = τ.vars "sc" + Csr.rowLen O v := by rw [hsc', hj₄, hrow]
      refine ⟨⟨D', Q', ⟨by simp [hn'], by simp [hsrc'], by simp [hoff'], by simp [htgt'],
          by simp [halv'], by simp [hdist'], by simp [hq']⟩, ?_, ?_⟩,
        hhead', hscv, by omega⟩
      · refine ⟨hF'.cap, hF'.src, hF'.sound, by simp; omega, by simpa using hF'.tl,
          by simpa using hF'.qmem, by simpa using hF'.qall, by simpa using hF'.qinj,
          by simpa using hF'.qmono, ?_, ?_⟩
        · intro i hi j hj₁ hj₂
          simp at hi hj₁ hj₂
          exact hF'.qcap i hi j (by omega) hj₂
        · intro i hi z hz
          simp at hi
          rcases Nat.lt_or_ge i (τ.vars "head") with hlt | hge
          · exact hF'.exp i hlt z hz
          · have hie : i = τ.vars "head" := by omega
            subst hie
            rw [hqv'] at hz ⊢
            rw [hDv']
            obtain ⟨j', hj'₁, hj'₂, hj'₃⟩ := hcsr.slot_of_madj hz
            rw [← hj'₃]
            exact hscanned j' hj'₁ (by rw [hj₄]; exact hj'₂) (by rw [hj'₃]; exact hz.alive_right)
      · show σ'.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head" + 1), Csr.rowLen O (Q' i)
        rw [Finset.sum_range_succ,
          Finset.sum_congr rfl fun i hi => by rw [hq₀' i (Finset.mem_range.1 hi)],
          ← hsum, hqv', hscv]
  run_vcg [CsrWide.loadRow_spec B n ns nt n "off" "tgt" "v" "j" "jend" O T (by decide)
      (by decide),
    hscanSpec]
  · simp_all
  · exact ⟨⟨by simpa using hcsrRel, by omega, hnsB⟩, by simp [hrv']; omega,
      by simp [hrv']; omega⟩
  · obtain ⟨-, -, -, rfl⟩ :=
      ‹CsrWide.LoadRowPostW "off" "tgt" "v" "j" "jend" n ns nt n O T _ _›
    refine ⟨⟨D, Q, ⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩, by simpa using hF, by simp,
      by simpa using hht, hvdef, rfl, by simp [hrv'], by simp [hdval'], by simp [hdval'],
      by simp [hrv'], by simp [hrv'], by simpa [hrv'] using hov, by simp [hrv'], ?_,
      fun i _ => rfl⟩, by simp [hrv']⟩
    intro j' h₁ h₂ h₃
    simp [hrv'] at h₂
    omega

/-- **The search, paid for out of the ball**, at the narrowed invariant.
The landed `BfsBlock.BallPot`, the landed release, the landed program. -/
theorem drainM_ball {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb)
    {τ : Env} (hI : DrainInvM G M nt d s O T τ) :
    ∃ τ' K, Run B bfsDrain τ τ' K ∧ DrainInvM G M nt d s O T τ' ∧
      τ'.vars "head" = τ'.vars "tail" ∧ K + BallPot bw nb τ' ≤ BallPot bw nb τ + 4 := by
  refine Queue.drain_run B n n "q" "head" "tail" expandRow (DrainInvM G M nt d s O T)
    (BallPot bw nb) (fun σ hσ => ?_) hnB (fun σ hσ hlt => ?_) hI
  · obtain ⟨D₁, Q₁, ⟨-, -, -, -, -, -, hq⟩, hFr, -⟩ := hσ
    exact ⟨Q₁, σ.vars "head", σ.vars "tail", hq, rfl, rfl, hFr.hd, hFr.tl,
      fun i hi => (hFr.qmem i hi).1⟩
  · obtain ⟨D₁, Q₁, hse, hFr, hsum⟩ := hσ
    obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ :=
      expandRowM_run hcsr hnB hnsB hnt hdB hMB hse hFr hlt hsum
    refine ⟨σ', K, hrun, hI', ?_⟩
    obtain ⟨D₂, Q₂, -, hFr', hsum'⟩ := hI'
    set r := Csr.rowLen O (Q₁ (σ.vars "head")) with hr
    have hsc₂ : σ'.vars "sc" ≤ bw := by
      rw [hsum']; exact le_trans (sum_rowLen_head_leM hFr' hFr'.hd hA) hbw
    have htail₂ : σ'.vars "tail" ≤ nb := le_trans (tail_le_cardM hFr' hA) hnb
    have hsc₁ : σ.vars "sc" ≤ bw := by
      rw [hsum]; exact le_trans (sum_rowLen_head_leM hFr hFr.hd hA) hbw
    have htail₁ : σ.vars "tail" ≤ nb := le_trans (tail_le_cardM hFr hA) hnb
    have hhd := hFr'.hd
    have hhd0 := hFr.hd
    simp only [BallPot]
    omega

/-- **The seed, at a mask-scoped fill.** The landed `seedSrc`, unchanged;
only the hypothesis about what the array holds narrows, and the two
branches are `frontierM_seed_alive` and `_dead`. -/
theorem seedSrcM_run {B : ℕ} (hs : s < n) (hnB : n < B) (hdB : d + 1 < B)
    (hMB : ∀ z < n, M z < B) {g g' : ℕ → ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hsrc : σ.vars "src" = s)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf nt T)
    (halv : σ.arrs "alv" = arrOf n M) (hdist : σ.arrs "dist" = arrOf n g)
    (hgd : ∀ j < n, M j ≠ 0 → g j = d + 1) (hq : σ.arrs "q" = arrOf n g') :
    ∃ σ' K, Run B seedSrc σ σ' K ∧ K ≤ 20 ∧ DrainInvM G M nt d s O T σ' ∧
      σ'.vars "head" = 0 ∧ σ'.vars "sc" = 0 := by
  have hsB : σ.vars "src" < B := by rw [hsrc]; omega
  have hdlen : σ.vars "src" < (σ.arrs "dist").length := by
    rw [hdist, length_arrOf, hsrc]; exact hs
  have hqlen : (σ.arrs "q").length = n := by rw [hq, length_arrOf]
  have halvlen : (σ.arrs "alv").length = n := by rw [halv, length_arrOf]
  have halvv : (σ.arrs "alv").getD (σ.vars "src") 0 = M s := by
    rw [halv, hsrc, getD_arrOf M hs]
  have halvv' : (σ.arrs "alv")[σ.vars "src"]?.getD 0 = M s := by
    rw [← List.getD_eq_getElem?_getD]; exact halvv
  have hMs : M s < B := hMB s hs
  run_vcg
  · refine ⟨⟨upd g s 0, upd g' 0 s, ⟨by simp [hn], by simp [hsrc], by simp [hoff],
        by simp [htgt], by simp [halv], by simp [hdist, hsrc, set_arrOf_eq_upd],
        by simp [hq, hsrc, set_arrOf_eq_upd]⟩, ?_, by simp⟩, by simp, by simp⟩
    have h := frontierM_seed_alive G M d hs (by omega) hgd (upd_self g' 0 s)
    simpa using h
  · refine ⟨⟨upd g s 0, upd g' 0 s, ⟨by simp [hn], by simp [hsrc], by simp [hoff],
        by simp [htgt], by simp [halv], by simp [hdist, hsrc, set_arrOf_eq_upd],
        by simp [hq, hsrc, set_arrOf_eq_upd]⟩, ?_, by simp⟩, by simp, by simp⟩
    have h := frontierM_seed_dead G M d hs (g := g) (Q := upd g' 0 s) (by omega) hgd
    simpa using h

/-! ### §7 The engine's contract, narrowed

The deliverable. Precondition and postcondition carry `DistClean` in
place of the whole-array equation, and everything else — the program, the
queue readings, the threshold reading, and the charge `bfsBlockK bw nb` —
is the landed statement, word for word.

The exit is where the honest weakening sits, and it is stated as one:
the engine no longer returns the array it was given. It returns an array
clean on the mask's support, which is exactly what the next atom's
precondition asks for, and `cleanOn_not_literal` is the compiled proof
that no stronger exit exists to aim at. -/

/-- **Block-driven breadth-first search, charged to its ball and
contracted at the mask's support.**

The precondition asks that the *live* cells of the distance array hold
the sentinel and says nothing whatever about the others; the
postcondition returns the same clause. Everything else is
`BfsBlock.bfsBlock_specW`, character for character, at the same program
and the same charge `bfsBlockK bw nb = 44 bw + 80 nb + 60` — **no `n`, no
`ns`, and no larger constant**, because no program text and no potential
moved.

`distClean_of_arrOf` is the one-line bridge from the landed whole-array
entry clause, so a caller that still runs `fillCom "dist"` is served by
this spec unchanged. -/
theorem bfsBlockM_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs "alv" = arrOf n M ∧ DistClean n d M σ ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g))
      (bfsBlockCom d)
      (fun _ σ' => DistClean n d M σ' ∧
        ∃ Q QD, σ'.arrs "q" = arrOf n Q ∧ σ'.arrs "qd" = arrOf n QD ∧
          σ'.vars "tail" ≤ n ∧ σ'.vars "tail" ≤ nb ∧
          (∀ i, i < σ'.vars "tail" → Q i < n) ∧
          (∀ v, v < n →
            ((∃ i, i < σ'.vars "tail" ∧ Q i = v) ↔ (M v ≠ 0 ∧ WD G M d s v))) ∧
          (∀ i, i < σ'.vars "tail" → ∀ j, j < σ'.vars "tail" → Q i = Q j → i = j) ∧
          (∀ i, i < σ'.vars "tail" → ∀ k, k ≤ d → (QD i ≤ k ↔ WD G M k s (Q i))))
      (bfsBlockK bw nb) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hsrc, hoff, htgt, halv, ⟨D₀, hdist, hclean⟩, ⟨g₁, hq⟩, ⟨g₂, hqd⟩⟩ := hσ
  obtain ⟨σ₁, K₁, hrun₁, hK₁, hI₁, hhead₁, hsc₁⟩ :=
    seedSrcM_run (G := G) (O := O) (T := T) (nt := nt) hs hnB hdB hMB hn hsrc hoff htgt
      halv hdist hclean hq
  obtain ⟨σ₂, K₂, hrun₂, hI₂, hhead₂, hpay⟩ :=
    drainM_ball hcsr hnB hnsB hnt hdB hMB hA hbw hnb hI₁
  obtain ⟨D, Q, ⟨hn₂, hsrc₂, hoff₂, htgt₂, halv₂, hdist₂, hq₂⟩, hFr₂, -⟩ := hI₂
  rw [hhead₂] at hFr₂
  have hqd₂ : σ₂.arrs "qd" = arrOf n g₂ := by
    rw [hrun₂.frame_arr "qd" (by simp [bfsDrain, expandRow, scanSlot, Csr.loadRow, Csr.scan,
        Queue.drain, Com.warrs]),
      hrun₁.frame_arr "qd" (by simp [seedSrc, Com.warrs])]
    exact hqd
  have htl : σ₂.vars "tail" ≤ n := hFr₂.tl
  have hqn : ∀ i, i < σ₂.vars "tail" → Q i < n := fun i hi => (hFr₂.qmem i hi).1
  have hqm : ∀ i, i < σ₂.vars "tail" → M (Q i) ≠ 0 := fun i hi => (hFr₂.qmem i hi).2.2
  have hDd : ∀ z, z < n → M z ≠ 0 → D z ≤ d + 1 := hFr₂.cap
  -- **the dead branch is gone.** Mask-scoped, this is `qall` and nothing
  -- else: the landed proof needed `sound` at a dead vertex here, which
  -- `frontier_sound_refuted` shows is not available and not true.
  have hdisc0 : ∀ z, z < n → M z ≠ 0 → D z ≤ d →
      z = s ∨ ∃ j, j < σ₂.vars "tail" ∧ Q j = z := by
    intro z hz hmz hzd
    obtain ⟨i, hi, hqi⟩ := hFr₂.qall z hz hmz hzd
    exact Or.inr ⟨i, hi, hqi⟩
  obtain ⟨σ₃, K₃, hrun₃, hK₃, hdist₃, hq₃, QD, hqd₃, hcopy₃⟩ :=
    unwindM_run (O := O) (T := T) (nt := nt) (M := M) hs hnB hdB htl hqn hqm
      (fun i hi j hj => hFr₂.qinj i hi j hj) hDd hdisc0 hn₂ hsrc₂ rfl hoff₂ htgt₂ halv₂
      hdist₂ hq₂ hqd₂
  have htail₃ : σ₃.vars "tail" = σ₂.vars "tail" :=
    hrun₃.frame_var "tail" (by simp [unwind, unwindSlot, Csr.scan, Com.wvars])
  obtain ⟨D₁, Q₁, -, hFr₁, -⟩ := hI₁
  have htail₁ : σ₁.vars "tail" ≤ nb := le_trans (tail_le_cardM hFr₁ hA) hnb
  have htail₂nb : σ₂.vars "tail" ≤ nb := le_trans (tail_le_cardM hFr₂ hA) hnb
  have hpot₁ : BallPot bw nb σ₁ = 44 * bw + 40 * nb := by
    simp only [BallPot, hhead₁, hsc₁]; omega
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_, le_rfl, hdist₃, Q, QD, hq₃, hqd₃,
    by omega, by omega, fun i hi => hqn i (by omega), fun v hv => ?_,
    fun i hi j hj => hFr₂.qinj i (by omega) j (by omega),
    fun i hi k hk => ?_⟩
  · rw [hpot₁] at hpay
    simp only [bfsBlockK]
    omega
  · rw [htail₃]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hqn', hqd', hqm'⟩ := hFr₂.qmem i hi
      exact ⟨hqm', WD.mono hqd' (hFr₂.sound _ hqn' hqm' hqd')⟩
    · rintro ⟨hmv, hwv⟩
      obtain ⟨i, hi, hqi⟩ := hFr₂.qall v hv hmv (hFr₂.complete d le_rfl v hwv)
      exact ⟨i, hi, hqi⟩
  · rw [htail₃] at hi
    rw [hcopy₃ i hi]
    exact hFr₂.dist_le_iff (hqn i hi) (hqm i hi) hk

/-- **The engine at the pinned target array**, which is the widened walk
at `nt = ns`. Nothing is re-proved. -/
theorem bfsBlockM_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧ DistClean n d M σ ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g))
      (bfsBlockCom d)
      (fun _ σ' => DistClean n d M σ' ∧
        ∃ Q QD, σ'.arrs "q" = arrOf n Q ∧ σ'.arrs "qd" = arrOf n QD ∧
          σ'.vars "tail" ≤ n ∧ σ'.vars "tail" ≤ nb ∧
          (∀ i, i < σ'.vars "tail" → Q i < n) ∧
          (∀ v, v < n →
            ((∃ i, i < σ'.vars "tail" ∧ Q i = v) ↔ (M v ≠ 0 ∧ WD G M d s v))) ∧
          (∀ i, i < σ'.vars "tail" → ∀ j, j < σ'.vars "tail" → Q i = Q j → i = j) ∧
          (∀ i, i < σ'.vars "tail" → ∀ k, k ≤ d → (QD i ≤ k ↔ WD G M k s (Q i))))
      (bfsBlockK bw nb) :=
  bfsBlockM_specW hcsr hs hnB hnsB le_rfl hdB hMB hA hbw hnb

/-! ### §8 The seam, in both directions

The narrowed spec has a **weaker precondition**, so it is the stronger
theorem at entry: a landed caller supplies more than it asks for and
crosses in one line (`distClean_of_arrOf`). It has a **weaker
postcondition**, and that is a real weakening, stated as one: a consumer
that needs the array back as a literal list does not get it, and
`cleanOn_not_literal` is why no such engine exists at this precondition.

The two are therefore incomparable as `Spec`s, which is the honest
reading. `BfsBlock.bfsBlock_specW` is untouched and still serves every
landed consumer; nothing downstream moves this wave. -/

/-- **The bridge, at the engine's own precondition.** A state satisfying
the landed whole-array entry clause satisfies the narrowed one, so
`bfsBlockM_specW` applies wherever `bfsBlock_specW` did. -/
theorem bfsBlockM_pre_of_bfsBlock_pre {σ : Env}
    (h : σ.vars "n" = n ∧ σ.vars "src" = s ∧
      σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
      σ.arrs "alv" = arrOf n M ∧ σ.arrs "dist" = arrOf n (fun _ => d + 1) ∧
      (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g)) :
    σ.vars "n" = n ∧ σ.vars "src" = s ∧
      σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
      σ.arrs "alv" = arrOf n M ∧ DistClean n d M σ ∧
      (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, distClean_of_arrOf h.2.2.2.2.2.1,
    h.2.2.2.2.2.2⟩

/-- **And the exit does not come back.** The narrowed postcondition does
not imply the landed one — `cleanOn_not_literal`'s array is clean on the
support and is not the literal list. Stated so that the weakening is
exhibited rather than asserted. -/
theorem bfsBlockM_post_not_bfsBlock_post :
    ¬ (∀ (D₂ : ℕ → ℕ), CleanOn 3 0 maskM D₂ → arrOf 3 D₂ = arrOf 3 (fun _ => 0 + 1)) := by
  intro h
  exact cleanOn_not_literal.2 (h _ cleanOn_not_literal.1)

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.frontierM_of_frontier' does not depend on any axioms -/
#guard_msgs in
#print axioms frontierM_of_frontier

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.frontier_cap_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frontier_cap_refuted

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.frontier_sound_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frontier_sound_refuted

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.frontierM_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frontierM_holds

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.frontierM_seed_alive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frontierM_seed_alive

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.frontierM_seed_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frontierM_seed_dead

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.unwindM_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unwindM_run

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.bfsBlockM_specW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bfsBlockM_specW

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.bfsBlockM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bfsBlockM_spec

/-- info: 'Lax3Proofs.Refine.BfsBlockMask.cleanOn_not_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cleanOn_not_literal

end Lax3Proofs.Refine.BfsBlockMask
