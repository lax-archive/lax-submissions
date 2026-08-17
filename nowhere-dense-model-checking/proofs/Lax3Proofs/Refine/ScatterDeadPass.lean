import Lax3Proofs.Refine.ScatterDeadEngine
import Lax3Proofs.RamDriverBot
import Lax3Proofs.TgtWidenProbe

/-!
# The dead-aware atom program, walked — wave R1.8-T3-flip, scope (b)

`Refine.ScatterDeadEngine.scatVal_of_cnt` decides a scatter atom of a
turn from three runtime numbers and reads no table row outside
`alive ∪ kills`:

    ScatVal (masked G Alv') (stepColoringP …) σs  ↔  σs.t ≤ cnt + (kc + oc)

with `cnt` the active-set engine's counter at the atom's *alive* set,
`kc` the atom's bits at the turn's kills, and `oc` the outside class's
one bit times its count. This file is the program that produces the
three, and the proof that it does.

## The six passes (design §6 (b))

1. `RamDriver.atomMemCom` — the child's member list filtered by the
   atom's table row into the engine's `"mem"`/`"mm"`. §2.
2. The engine's entry condition: a clean `"dist"`. Carrier-charge
   parity with the landed engine entry (`Refine.ArenaSeam.memEntry`) is
   accepted at this boundary. **The mask copy that used to stand beside
   it is gone** (wave E4c-c): the engine reads the child's alive array
   where it lies, so there is nothing to move and no scratch to clean,
   and §5c's charge is `12·n + 6` lighter. Making the *distance* fill
   active-set-driven was E4c-b's, and §5f is its result — the
   member-scale replacement is built, specified and clocked there and
   cannot be wired in, because `Refine.ScatterBlock.ArenaA` pins the
   whole array at the atom's own radius.
3. `Refine.ScatterBlock.scatBlockCom`, read through
   `Refine.ScatterDeadEngine.scatBlockCnt_specW` — the counter in its
   `∀ e` decision form, which is the only true reading (the naive
   `cnt = count` is compiled-refuted at the threshold cap, next door).
4. `RamDriver.killSumCom` — the atom's bits over `klName j`, summing to
   the kill term by `Refine.ScatterDeadFold.sum_bit_eq_ncard_inter`. §3.
5. `RamDriver.outProbeCom` + `RamDriver.outCntCom` — one probe vertex
   and three scalars. §4.
6. `RamDriver.atomFlagCom` — the threshold against the three terms. §5.

## §0 first: the two refutations

Standing practice on this campaign. The filter's obligation is falsified
before it is proved (`inplace_filter_refuted`: the in-place compaction
`RamDriver.memFilterCom` uses would be **wrong** here — the child's
member list is read again by every later atom of the same turn, and the
second atom of a two-atom turn sees a list the first one shortened), and
so is the probe's (`empty_class_probe_refuted`: with the class empty the
probe's vertex register still holds a vertex, and that vertex is *in*
the cluster — reading the register without its found flag would take an
in-cluster vertex's bit for the outside class's answer).
-/

namespace Lax3Proofs.Refine.ScatterDeadPass

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamScatter
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster (markSet)
open Lax3Proofs.Refine.ScatterBlock (MemList MemOf ArenaA BallBudget scatBlockCom scatBlockK)

variable {n B : ℕ}

/-! ### §0 The compiled refutations

The instrument is `TgtWidenProbe.execC`, as in `Refine.KillListPass` §0
and `Refine.DeadRowProbe` §5. -/

section Probes

open Lax3Proofs.TgtWidenProbe (execC pB pF PSt)

/-- The turn's data at a three-member child block: the child's list
`2, 5, 7` (three alive vertices of a ten-vertex carrier), two atom rows
— row `0` marks `2` and `7`, row `1` marks `5` — the turn's cluster
`{0, 1, 2}` and the child mask alive exactly at `2`. -/
def atSt : PSt :=
  { vars := [("n", 10), (mnumName 1, 3)]
    arrs := [(memName 1, [2, 5, 7, 0, 0, 0, 0, 0, 0, 0]),
             (tabName 1 0, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]),
             (tabName 1 1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]),
             (alvName 1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0]),
             (cluName 0, [1, 1, 1, 0, 0, 0, 0, 0, 0, 0]),
             ("mem", [9, 9, 9, 9, 9, 9, 9, 9, 9, 9])] }

-- **The filter emits each surviving member once, in the source's
-- order.** Row `0` keeps `2` and `7`; the count is two and the two
-- cells are in increasing order, which is `MemList`'s second clause.
#guard (execC pB pF (atomMemCom 0 0) atSt).1.isOk
#guard (execC pB pF (atomMemCom 0 0) atSt).1.scalar "mm" = 2
#guard (execC pB pF (atomMemCom 0 0) atSt).1.cell "mem" 0 = 2
#guard (execC pB pF (atomMemCom 0 0) atSt).1.cell "mem" 1 = 7

-- and the second atom of the same turn, at row `1`, sees the WHOLE
-- child list again: one survivor, `5`
#guard (execC pB pF (atomMemCom 0 1) atSt).1.scalar "mm" = 1
#guard (execC pB pF (atomMemCom 0 1) atSt).1.cell "mem" 0 = 5

/-- The in-place variant — `RamDriver.memFilterCom`'s shape, compacting
the child's list into itself. This is the program the refutation
runs. -/
def naiveAtomMemCom (j ti : ℕ) : Com :=
  .seq (.assign (mnumName (j + 1)) (.lit 0))
    (.seq (.assign "ak" (.lit 0))
      (.while (.lt (.var "ak") (.var "bq"))
        (.seq (.assign "av" (.get (memName (j + 1)) (.var "ak")))
          (.seq (.ite (.lt (.lit 0) (.get (tabName (j + 1) ti) (.var "av")))
                  (.seq (.store (memName (j + 1)) (.var (mnumName (j + 1))) (.var "av"))
                    (.assign (mnumName (j + 1)) (.add (.var (mnumName (j + 1))) (.lit 1))))
                  .skip)
            (.assign "ak" (.add (.var "ak") (.lit 1)))))))

/-- The same state with the raw bound the in-place variant walks. -/
def atStBq : PSt := { atSt with vars := ("bq", 3) :: atSt.vars }

/-- Two atoms of one turn, in place: filter by row `0`, then by row
`1`. -/
def naiveTwoAtoms : Com := .seq (naiveAtomMemCom 0 0) (naiveAtomMemCom 0 1)

/-- **The in-place filter is refuted.** A turn decides *every* scatter
atom of *every* tabled formula against the same child member list, so
the list must survive each atom. Compacting it in place does not: after
the first atom the list is `2, 7`, and the second atom — whose set is
`{5}`, a vertex the first atom's row dropped — reports the EMPTY list
where the truth is the one-element list `5`. `RamDriver.atomMemCom` is
out of place for exactly this reason, and the extra array it writes into
is the engine's own `"mem"`, which the engine overwrites at every atom
anyway. -/
theorem inplace_filter_refuted :
    (execC pB pF naiveTwoAtoms atStBq).1.scalar (mnumName 1) = 0 ∧
      (execC pB pF (atomMemCom 0 1) atSt).1.scalar "mm" = 1 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The probe's state with the class NON-empty: the cluster is `{0, 1}`
and the child mask is alive at `0` only, so `2` is the first vertex both
dead and outside. -/
def opSt (n : ℕ) : PSt :=
  { vars := [("n", n)]
    arrs := [(alvName 1, (List.replicate n 0).set 0 1),
             (cluName 0, ((List.replicate n 0).set 0 1).set 1 1)] }

-- **The probe finds the first outside vertex**, and its flag is set
#guard (execC pB pF (outProbeCom 0) (opSt 10)).1.isOk
#guard (execC pB pF (outProbeCom 0) (opSt 10)).1.scalar "of" = 1
#guard (execC pB pF (outProbeCom 0) (opSt 10)).1.scalar "oz" = 2

-- and the early exit is real: the same clock at carriers 10 and 200,
-- because the scan stops at the first hit
#guard (execC pB pF (outProbeCom 0) (opSt 10)).2 =
  (execC pB pF (outProbeCom 0) (opSt 200)).2

/-- The probe's state with the class EMPTY: the cluster is the whole
four-vertex carrier, so no vertex is outside it. -/
def opStFull : PSt :=
  { vars := [("n", 4)]
    arrs := [(alvName 1, [1, 0, 0, 0]), (cluName 0, [1, 1, 1, 1])] }

/-- **The bare probe register is refuted.** With the outside class empty
the scan finds nothing and `"oz"` still reads `0` — a vertex which is
*in* the cluster, and whose atom bit is therefore NOT the outside
class's answer (`Refine.ScatterDeadFold.outside_uniform` says nothing
about it). So the register alone cannot carry the class: the found flag
`"of"` is load-bearing, and the composite below multiplies the outside
term by a bit that is zero exactly when the flag is
(`Refine.ScatterDeadFold.outside_ncard_of_empty` is the branch it
takes). -/
theorem empty_class_probe_refuted :
    (execC pB pF (outProbeCom 0) opStFull).1.scalar "of" = 0 ∧
      (execC pB pF (outProbeCom 0) opStFull).1.scalar "oz" = 0 ∧
      (execC pB pF (outProbeCom 0) opStFull).1.cell (cluName 0) 0 = 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The kill walk's state: the turn's kill list `7, 91` (two kills, once
each — `RamDriver.killListCom`'s own product) against an atom row that
marks `7` and not `91`. -/
def ksSt : PSt :=
  { vars := [(kkName 0, 2)]
    arrs := [(klName 0, [7, 91, 0]),
             (tabName 1 0, ((List.replicate 100 0).set 7 1).set 5 1)] }

-- **The kill walk sums the row at the LISTED vertices**: one of the two
-- kills satisfies the atom, and the row's other set bit (at `5`, not a
-- kill) is not counted
#guard (execC pB pF (killSumCom 0 0) ksSt).1.isOk
#guard (execC pB pF (killSumCom 0 0) ksSt).1.scalar "kc" = 1

end Probes

/-! ### §0b The batch entry outside the cluster — the producer, decided

**Wave R1.8-T3-flip (c1b), the refutation.**
`Refine.DeadRowProbe.stepColoringP_subset` is what says the whole
outside class carries the EMPTY child row, and that is the fact the
outside term of `atomTerms_iff_scatVal` rides on
(`Refine.ScatterDeadFold.outside_uniform` →
`outside_ncard_of_probe`). It takes `hw : ∀ i, w i ∈ X`, and every
consumer down to `atomTerms_iff_scatVal` carries `hw` verbatim.

**The hypothesis is not removable**, and the refutation below is one
line of the palette's own slot equation: the batch-profile slot of the
entry `w i` at radius zero is `{x | WithinDist _ 0 x (w i)}`
(`Evaluator.isoColoring_slotPd`), which contains `w i` whatever `X` is,
and contains nothing else. So a batch entry outside the cluster is an
out-of-cluster vertex whose child row is NOT the empty one, while its
out-of-cluster neighbours' rows are — the class is not colour-uniform,
and the one-bit-times-a-count reading of the outside term is false.

**Wave (c2a), the verdict.** Two routes were on the table and a third
was the answer.

**2026-08-10 monotone-game follow-up.** The exact-arena counterexample
below remains valid, but it no longer constrains the executable
successor. `SplitterWinRec.ReachedSubR` permits that successor to retain
the current cluster while the mathematical generating set records the
omitted path portions. The batch set still remains unchanged; only the
recorded game position is now cluster-supported as well.

* *Narrow the batch* — one more `andCom` at the end of
  `RamDriver.batchCom`. It is not free, and
  `game_arena_sees_the_cluster_cut` below is why:
  the former exact successor cut the whole *game* ball by the batch,
  and that exact arena is **not** cluster-restricted, so the same
  intersection that is invisible at the child arena is visible there.
  The recorded round moves, and with it
  `RamDriverDescend.batchCom_spec`'s walk-support clause, whose
  conclusion weakens from `support ∩ ball ⊆ W` to
  `support ∩ ball ⊆ W ∩ X`. The escape would be a proof that `W ⊆ X`
  already, which would make the cut vacuous — but that is an export of
  nothing landed, and the geometry is against it: the batch is cut to
  the `2·cap`-ball of the connector in the **game** arena, while `X` is
  a `wreach`-cluster of the centre in the **work** arena, which
  `RamDriver.PlayRec` puts strictly below it.
* *Re-base the dead fold at `X ∪ Set.range w`* — **refuted on cost** by
  `dead_inter_union_batch` below: at the turn's own data the new inside
  half is the WHOLE batch, so the kill list would have to enumerate
  every batch entry and `RamDriverCluster.KillRowsAt` would owe a table
  row at each of them, including the out-of-cluster ones — whose rows
  are neither empty nor equal to one another, which is exactly what
  `outside_class_not_uniform_refuted` compiles. That is a rewrite of
  the kill pass and a re-run of `Refine.KillListPass.ctKL`.
* *Narrow the **enumeration**, not the batch* — what landed. The batch
  as a set is untouched, so `PlayRec`, `batchCom_spec`, `BatchData`,
  `KillRowsAt` and the kill list all stand verbatim; only
  `RamDriver.enumBatch`'s guard gains the cluster indicator. The child
  arena cannot see the difference (`RamDriver.deleteVerts_inter_cluster`,
  which `RamDriverCluster.masked_alv_eq` now runs through) and
  `RamDriver.sat_iff_eval_step` — the isolation rewrite itself — asks
  nothing whatever of `w`. It is correct whether or not `W ⊆ X` holds
  of the driver's states, which is why it does not need that question
  settled. The producer of `hw` is
  `RamDriverCluster.ClusterData.mem_cluster`, and
  `atomTerms_iff_scatVal_of_clusterData` at the end of §5 is the atom's
  verdict with the turn's data in place of the hypothesis. -/

/-- **The game arena is not blind to the cluster cut.** One edge, one
endpoint in the batch and the other in the cluster: deleting `W` and
deleting `W ∩ X` give different graphs. This is why narrowing the batch
itself is a different change from narrowing its enumeration — the child
arena has already had `Xᶜ` deleted from it and cannot tell the two
apart (`RamDriver.deleteVerts_inter_cluster`), while `PlayRec`'s game
arena has not. -/
theorem game_arena_sees_the_cluster_cut :
    ∃ (A : SimpleGraph (Fin 2)) (X W : Set (Fin 2)),
      Lax12.UniformQuasiWideness.deleteVerts A (W ∩ X) ≠
        Lax12.UniformQuasiWideness.deleteVerts A W := by
  refine ⟨⊤, {1}, {0}, fun h => ?_⟩
  have h0 : (Lax12.UniformQuasiWideness.deleteVerts (⊤ : SimpleGraph (Fin 2))
      (({0} : Set (Fin 2)) ∩ ({1} : Set (Fin 2)))).Adj 0 1 := by
    refine ⟨by decide, ?_, ?_⟩
    · rintro ⟨-, hc⟩; exact absurd hc (by decide)
    · rintro ⟨hc, -⟩; exact absurd hc (by decide)
  rw [h] at h0
  exact absurd h0.2.1 (by decide)

/-- **Route 2's inside half is the whole batch.** Re-basing
`Refine.ScatterDeadFold`'s split at `X ∪ W` does make the outside class
colour-uniform, but at the turn's own data the half the kill list would
then have to enumerate is `W` itself: a batch vertex is dead at the
child by `RamDriverCluster.BatchData`'s pointwise clause whether or not
it is in the cluster, and inside the cluster the dead ones are exactly
the batch. So route 2 costs a kill row at every batch entry — and by
`outside_class_not_uniform_refuted` the out-of-cluster entries do not
share a row, so no default bit pays for them. -/
theorem dead_inter_union_batch {M Alv' : ℕ → ℕ} {X W : Set (Fin n)}
    (hpt : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 ↔ (M (v : ℕ) ≠ 0 ∧ v ∈ X ∧ v ∉ W))
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0) :
    ScatterDeadFold.deadSet n Alv' ∩ (X ∪ W) = W := by
  ext v
  constructor
  · rintro ⟨hd, hX | hW⟩
    · by_contra hW
      exact absurd (ScatterDeadFold.mem_deadSet.1 hd) ((hpt v).2 ⟨hXalive v hX, hX, hW⟩)
    · exact hW
  · intro hW
    refine ⟨?_, Or.inr hW⟩
    show Alv' (v : ℕ) = 0
    by_contra hc
    exact ((hpt v).1 hc).2.2 hW

/-- **The refutation itself** (wave (c1b)): at a three-vertex carrier
with cluster `{0}`, empty graph and radius zero, the batch entry `1`
lies outside the cluster and *in* its own radius-zero profile slot,
while `2` — equally outside the cluster — does not. Two out-of-cluster
vertices with different colour rows: without `hw` the outside class is
not colour-uniform and the one-bit-times-a-count reading of the outside
term is false. -/
theorem outside_class_not_uniform_refuted :
    (1 : Fin 3) ∉ ({0} : Set (Fin 3)) ∧ (2 : Fin 3) ∉ ({0} : Set (Fin 3)) ∧
      (1 : Fin 3) ∈ stepColoringP (n := 3) 0 (⊥ : SimpleGraph (Fin 3))
        (fun c : Fin 0 => c.elim0) ({0} : Set (Fin 3)) (fun _ : Fin 1 => (1 : Fin 3))
        (Lax3Proofs.Evaluator.slotPd 0 0) ∧
      (2 : Fin 3) ∉ stepColoringP (n := 3) 0 (⊥ : SimpleGraph (Fin 3))
        (fun c : Fin 0 => c.elim0) ({0} : Set (Fin 3)) (fun _ : Fin 1 => (1 : Fin 3))
        (Lax3Proofs.Evaluator.slotPd 0 0) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · rw [stepColoringP, Lax3Proofs.Evaluator.isoColoring_slotPd]
    exact withinDist_refl _ 0 _
  · rw [stepColoringP, Lax3Proofs.Evaluator.isoColoring_slotPd]
    rintro ⟨p, hp⟩
    exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hp)) (by decide)

/-! ### §1 The atom's set, and the two readings of a table row

The set a scatter atom of the child depth speaks about is
`Refine.ScatterDeadFold.satSet`; what a table row is worth on a domain
is `Refine.DeadRowProbe.TableInvOn`. The walks below take the row as a
bare function with a bit hypothesis on a domain, which is what both
readings hand them. -/

/-- **The atom's alive set**, as the engine's member list enumerates it:
the vertices where the atom's row is set among the child's alive ones.
This is the `X` of `Refine.ScatterBlock.MemList` for the filtered
list. -/
def bitSet (n : ℕ) (A Tb : ℕ → ℕ) : Set (Fin n) :=
  {v : Fin n | A (v : ℕ) ≠ 0 ∧ Tb (v : ℕ) ≠ 0}

theorem mem_bitSet {A Tb : ℕ → ℕ} {v : Fin n} :
    v ∈ bitSet n A Tb ↔ A (v : ℕ) ≠ 0 ∧ Tb (v : ℕ) ≠ 0 := Iff.rfl

/-- The atom's alive set IS the atom's set intersected with the mask's,
whenever the row decides the atom at the alive vertices — which is what
`RamDriver.TableInv` (and its restriction `TableInvOn` to a domain
containing the alive ones) says. -/
theorem bitSet_eq_inter {A Tb : ℕ → ℕ} {S : Set (Fin n)}
    (hbit : ∀ v : Fin n, A (v : ℕ) ≠ 0 → (Tb (v : ℕ) ≠ 0 ↔ v ∈ S)) :
    bitSet n A Tb = S ∩ markSet n A := by
  ext v
  constructor
  · rintro ⟨hA, hT⟩
    exact ⟨(hbit v hA).1 hT, hA⟩
  · rintro ⟨hS, hA⟩
    exact ⟨hA, (hbit v hA).2 hS⟩

/-- **A repetition-free enumeration counts its set.** One lemma for the
two scalars the outside count is read off: the child's member list
counts the alive set, and the turn's kill list counts the kill set. -/
theorem ncard_eq_of_enum {S : Set (Fin n)} {m : ℕ} {f : ℕ → ℕ}
    (hlt : ∀ k, k < m → f k < n)
    (hinj : ∀ i, i < m → ∀ k, k < m → f i = f k → i = k)
    (hsound : ∀ k, (hk : k < m) → (⟨f k, hlt k hk⟩ : Fin n) ∈ S)
    (hcomp : ∀ v : Fin n, v ∈ S → ∃ k, k < m ∧ f k = (v : ℕ)) :
    S.ncard = m := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  have hb := Finset.card_bij (s := Finset.range m) (t := S.toFinset)
    (fun k hk => (⟨f k, hlt k (Finset.mem_range.1 hk)⟩ : Fin n))
    (fun k hk => Set.mem_toFinset.2 (hsound k (Finset.mem_range.1 hk)))
    (fun a ha b hb hab => hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb)
      (congrArg Fin.val hab))
    (fun v hv => by
      obtain ⟨k, hk, hkv⟩ := hcomp v (Set.mem_toFinset.1 hv)
      exact ⟨k, Finset.mem_range.2 hk, Fin.ext hkv⟩)
  rw [Finset.card_range] at hb
  exact hb.symm

/-! ### §2 The filter walk (design §6 (b), pass 1)

The child's member list, filtered by the atom's row into the engine's
array. The pass is `Csr.scan` over the child's member count, so
`Csr.rowScan_spec` carries the loop and the only content is the
invariant. It is the out-of-place twin of `RamDriverDescend`'s
`memFilter_spec`; §0's `inplace_filter_refuted` is why it must be. -/

/-- The cost of the atom's filter: charged at the child's member count,
with the carrier nowhere in it. -/
def atomMemCost (mm1 : ℕ) : ℕ := 23 * mm1 + 8

/-- What the atom's filter carries: the read pointer inside the child's
list, the write pointer behind it, and the emitted prefix — sound,
complete and strictly increasing against the part of the child list
already read. -/
def AtomFilt (n j ti mm1 : ℕ) (Mem1 Tb : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars (mnumName (j + 1)) = mm1 ∧ σ.vars "ak" ≤ mm1 ∧ σ.vars "mm" ≤ σ.vars "ak" ∧
    σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧
    σ.arrs (tabName (j + 1) ti) = arrOf n Tb ∧
    ∃ g, σ.arrs "mem" = arrOf n g ∧
      (∀ q, q < σ.vars "mm" → ∃ p, p < σ.vars "ak" ∧ g q = Mem1 p ∧ Tb (Mem1 p) ≠ 0) ∧
      (∀ p, p < σ.vars "ak" → Tb (Mem1 p) ≠ 0 → ∃ q, q < σ.vars "mm" ∧ g q = Mem1 p) ∧
      (∀ q₁ q₂, q₁ < q₂ → q₂ < σ.vars "mm" → g q₁ < g q₂)

theorem ak_ne_mnumName (j : ℕ) : ("ak" : String) ≠ mnumName (j + 1) := by
  simp [mnumName, String.ext_iff]

theorem av_ne_mnumName (j : ℕ) : ("av" : String) ≠ mnumName (j + 1) := by
  simp [mnumName, String.ext_iff]

theorem mem_ne_tabName (j ti : ℕ) : ("mem" : String) ≠ tabName j ti := by
  simp [tabName, String.ext_iff]

theorem memName_ne_tabName (j j' ti : ℕ) : memName j ≠ tabName j' ti := by
  simp [memName, tabName, String.ext_iff]

/-- **The atom's member list, walked.** From the child depth's own
member list and the atom's table row, the pass leaves in `"mem"`/`"mm"`
a `Refine.ScatterBlock.MemList` for the atom's alive set — the exact
hypothesis the block engine takes, at the exact set
`Refine.ScatterDeadEngine.scatVal_of_cnt`'s counter clause quantifies
over.

The row is read only at the *listed* vertices, so the bit hypothesis is
asked only there: no clause about a row outside `alive ∪ kills` enters,
which is the whole point of the R1.8 domain change. -/
theorem atomMemCom_spec {j ti mm1 : ℕ} {Mem1 Tb A : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B)
    (hMenum : MemEnum n mm1 Mem1 A)
    (hTbB : ∀ p, p < mm1 → Tb (Mem1 p) < B) :
    Spec B (fun σ => σ.vars (mnumName (j + 1)) = mm1 ∧
        σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧
        σ.arrs (tabName (j + 1) ti) = arrOf n Tb ∧ (∃ g, σ.arrs "mem" = arrOf n g))
      (atomMemCom j ti)
      (fun _ σ' => ∃ (Mem : ℕ → ℕ) (mm : ℕ), σ'.arrs "mem" = arrOf n Mem ∧
        σ'.vars "mm" = mm ∧ mm ≤ mm1 ∧
        MemList n mm Mem (bitSet n A Tb) ∧
        σ'.arrs (memName (j + 1)) = arrOf n Mem1 ∧
        σ'.arrs (tabName (j + 1) ti) = arrOf n Tb ∧
        σ'.vars (mnumName (j + 1)) = mm1)
      (atomMemCost mm1) := by
  classical
  obtain ⟨hMlt, hMmono, hMalv, hMcomp⟩ := id hMenum
  have hm1n : mm1 ≤ n := hMenum.card_le
  have hm1B : mm1 < B := by omega
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hmm1, hmem1, htab, hdst⟩ := hσ
  -- the two counters
  set σ₁ := σ.setVar "mm" 0 with hσ₁
  have hr₁ : Run B (.assign "mm" (.lit 0)) σ σ₁ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  set σ₂ := σ₁.setVar "ak" 0 with hσ₂
  have hr₂ : Run B (.assign "ak" (.lit 0)) σ₁ σ₂ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  -- one member of the child's list
  have hstep : ∀ ρ : Env, AtomFilt n j ti mm1 Mem1 Tb ρ → ρ.vars "ak" < mm1 →
      ∃ ρ' K', Run B (.seq (.assign "av" (.get (memName (j + 1)) (.var "ak")))
          (.seq (.ite (.lt (.lit 0) (.get (tabName (j + 1) ti) (.var "av")))
              (.seq (.store "mem" (.var "mm") (.var "av"))
                (.assign "mm" (.add (.var "mm") (.lit 1))))
              .skip)
            (.assign "ak" (.add (.var "ak") (.lit 1))))) ρ ρ' K' ∧
        AtomFilt n j ti mm1 Mem1 Tb ρ' ∧ ρ'.vars "ak" = ρ.vars "ak" + 1 ∧ K' ≤ 19 := by
    intro ρ hρ hlt
    obtain ⟨hmm1ρ, hakρ, hmmρ, hmem1ρ, htabρ, g, hgarr, hsound, hcomp, hmono⟩ := hρ
    set ak := ρ.vars "ak" with hak
    set mm := ρ.vars "mm" with hmm
    have hvn : Mem1 ak < n := hMlt ak hlt
    have hakn : ak < n := by omega
    -- the read
    have hake : (Expr.var "ak").evalB B ρ = some ak := by
      have h := evalB_var (B := B) (x := "ak") (σ := ρ) (by omega)
      rwa [← hak] at h
    have hread : (Expr.get (memName (j + 1)) (.var "ak")).evalB B ρ = some (Mem1 ak) :=
      evalB_get hake (by rw [hmem1ρ, getElem?_arrOf Mem1 hakn]) (by omega)
    set ρ₁ := ρ.setVar "av" (Mem1 ak) with hρ₁
    have hr'₁ : Run B (.assign "av" (.get (memName (j + 1)) (.var "ak"))) ρ ρ₁ 3 :=
      (Run.assign hread).mono (by simp [Expr.size])
    have hav₁ : ρ₁.vars "av" = Mem1 ak := by rw [hρ₁, vars_setVar, if_pos rfl]
    have hak₁ : ρ₁.vars "ak" = ak := by rw [hρ₁, vars_setVar, if_neg (by decide)]
    have hmm₁ : ρ₁.vars "mm" = mm := by rw [hρ₁, vars_setVar, if_neg (by decide)]
    have hmm1₁ : ρ₁.vars (mnumName (j + 1)) = mm1 := by
      rw [hρ₁, vars_setVar, if_neg (Ne.symm (av_ne_mnumName j))]; exact hmm1ρ
    have hmemd₁ : ρ₁.arrs "mem" = arrOf n g := by rw [hρ₁, arrs_setVar]; exact hgarr
    have hmem1₁ : ρ₁.arrs (memName (j + 1)) = arrOf n Mem1 := by
      rw [hρ₁, arrs_setVar]; exact hmem1ρ
    have htab₁ : ρ₁.arrs (tabName (j + 1) ti) = arrOf n Tb := by
      rw [hρ₁, arrs_setVar]; exact htabρ
    have hcond : (Cond.lt (.lit 0) (.get (tabName (j + 1) ti) (.var "av"))).evalB B ρ₁ =
        some (decide (0 < Tb (Mem1 ak))) := by
      refine evalB_condLt (evalB_lit (by omega)) ?_
      refine evalB_get ?_ (by rw [htab₁, getElem?_arrOf Tb hvn]) (hTbB ak hlt)
      have h := evalB_var (B := B) (x := "av") (σ := ρ₁) (by rw [hav₁]; omega)
      rwa [hav₁] at h
    -- the tail: the read pointer moves
    have htail : ∀ τ : Env, τ.vars "ak" = ak →
        ∃ τ', Run B (.assign "ak" (.add (.var "ak") (.lit 1))) τ τ' 4 ∧
          τ' = τ.setVar "ak" (ak + 1) := by
      intro τ hτ
      have he : (Expr.add (Expr.var "ak") (.lit 1)).evalB B τ = some (ak + 1) := by
        have h := evalB_bin (evalB_var (B := B) (x := "ak") (σ := τ) (by rw [hτ]; omega))
          (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
          (show Bop.add.apply (τ.vars "ak") 1 < B by rw [Bop.apply_add, hτ]; omega)
        rw [Bop.apply_add, hτ] at h
        exact h
      exact ⟨_, (Run.assign he).mono (by simp [Expr.size]), rfl⟩
    by_cases hkeep : 0 < Tb (Mem1 ak)
    · -- the member survives the row: append it
      have hmmn : mm < n := by omega
      have hmme₁ : (Expr.var "mm").evalB B ρ₁ = some mm := by
        have h := evalB_var (B := B) (x := "mm") (σ := ρ₁) (by rw [hmm₁]; omega)
        rwa [hmm₁] at h
      have have₁ : (Expr.var "av").evalB B ρ₁ = some (Mem1 ak) := by
        have h := evalB_var (B := B) (x := "av") (σ := ρ₁) (by rw [hav₁]; omega)
        rwa [hav₁] at h
      have hlen₁ : mm < (ρ₁.arrs "mem").length := by
        rw [hmemd₁, length_arrOf]; exact hmmn
      set ρ₂ := ρ₁.setArr "mem" mm (Mem1 ak) with hρ₂
      have hmm₂ : ρ₂.vars "mm" = mm := by rw [hρ₂, vars_setArr]; exact hmm₁
      have hmme₂ : (Expr.add (Expr.var "mm") (.lit 1)).evalB B ρ₂ = some (mm + 1) := by
        have h := evalB_bin (evalB_var (B := B) (x := "mm") (σ := ρ₂) (by rw [hmm₂]; omega))
          (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
          (show Bop.add.apply (ρ₂.vars "mm") 1 < B by rw [Bop.apply_add, hmm₂]; omega)
        rw [Bop.apply_add, hmm₂] at h
        exact h
      set ρ₃ := ρ₂.setVar "mm" (mm + 1) with hρ₃
      have hak₃ : ρ₃.vars "ak" = ak := by
        rw [hρ₃, vars_setVar, if_neg (by decide), hρ₂, vars_setArr, hak₁]
      obtain ⟨ρ₄, hr'₄, hρ₄⟩ := htail ρ₃ hak₃
      set gu : ℕ → ℕ := fun k => if k = mm then Mem1 ak else g k with hgu
      have hak₄ : ρ₄.vars "ak" = ak + 1 := by rw [hρ₄, vars_setVar, if_pos rfl]
      have hmm₄ : ρ₄.vars "mm" = mm + 1 := by
        rw [hρ₄, vars_setVar, if_neg (by decide), hρ₃, vars_setVar, if_pos rfl]
      have hmm1₄ : ρ₄.vars (mnumName (j + 1)) = mm1 := by
        rw [hρ₄, vars_setVar, if_neg (Ne.symm (ak_ne_mnumName j)), hρ₃, vars_setVar,
          if_neg (mnumName_ne_mm (j + 1)), hρ₂, vars_setArr]
        exact hmm1₁
      have hmemd₄ : ρ₄.arrs "mem" = arrOf n gu := by
        rw [hρ₄, arrs_setVar, hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_pos rfl, hmemd₁,
          set_arrOf]
      have hmem1₄ : ρ₄.arrs (memName (j + 1)) = arrOf n Mem1 := by
        rw [hρ₄, arrs_setVar, hρ₃, arrs_setVar, hρ₂, arrs_setArr,
          if_neg (memName_ne_mem (j + 1))]
        exact hmem1₁
      have htab₄ : ρ₄.arrs (tabName (j + 1) ti) = arrOf n Tb := by
        rw [hρ₄, arrs_setVar, hρ₃, arrs_setVar, hρ₂, arrs_setArr,
          if_neg (Ne.symm (mem_ne_tabName (j + 1) ti))]
        exact htab₁
      refine ⟨ρ₄, 19, ((hr'₁.seq ((Run.ite_true (by rw [hcond]; simp [hkeep])
        ((Run.store hmme₁ have₁ hlen₁).seq (Run.assign hmme₂))).seq hr'₄))).mono
          (by simp [Expr.size, Cond.size]), ?_, hak₄, le_rfl⟩
      refine ⟨hmm1₄, by omega, by omega, hmem1₄, htab₄, gu, hmemd₄, ?_, ?_, ?_⟩
      · intro q hq
        rw [hmm₄] at hq
        rw [hak₄]
        by_cases hqm : q = mm
        · exact ⟨ak, by omega, by rw [hqm, hgu]; simp, by omega⟩
        · obtain ⟨p, hp1, hp2, hp3⟩ := hsound q (by omega)
          exact ⟨p, by omega, by rw [hgu]; simp only []; rw [if_neg hqm]; exact hp2, hp3⟩
      · intro p hp hTp
        rw [hak₄] at hp
        rw [hmm₄]
        by_cases hpm : p = ak
        · exact ⟨mm, by omega, by rw [hgu]; simp [hpm]⟩
        · obtain ⟨q, hq1, hq2⟩ := hcomp p (by omega) hTp
          have hne : q ≠ mm := by omega
          exact ⟨q, by omega, by rw [hgu]; simp only []; rw [if_neg hne]; exact hq2⟩
      · intro q₁ q₂ h12 hq2
        rw [hmm₄] at hq2
        by_cases hq2m : q₂ = mm
        · have hne : q₁ ≠ mm := by omega
          rw [hgu]
          simp only []
          rw [if_pos hq2m, if_neg hne]
          obtain ⟨p, hp1, hp2, -⟩ := hsound q₁ (by omega)
          rw [hp2]
          exact hMmono p ak hp1 hlt
        · have hne : q₁ ≠ mm := by omega
          rw [hgu]
          simp only []
          rw [if_neg hne, if_neg hq2m]
          exact hmono q₁ q₂ h12 (by omega)
    · -- the row drops the member: only the read pointer moves
      obtain ⟨ρ₄, hr'₄, hρ₄⟩ := htail ρ₁ hak₁
      have hT0 : Tb (Mem1 ak) = 0 := by omega
      have hak₄ : ρ₄.vars "ak" = ak + 1 := by rw [hρ₄, vars_setVar, if_pos rfl]
      have hmm₄ : ρ₄.vars "mm" = mm := by
        rw [hρ₄, vars_setVar, if_neg (by decide)]; exact hmm₁
      have hmm1₄ : ρ₄.vars (mnumName (j + 1)) = mm1 := by
        rw [hρ₄, vars_setVar, if_neg (Ne.symm (ak_ne_mnumName j))]; exact hmm1₁
      have hmemd₄ : ρ₄.arrs "mem" = arrOf n g := by rw [hρ₄, arrs_setVar]; exact hmemd₁
      have hmem1₄ : ρ₄.arrs (memName (j + 1)) = arrOf n Mem1 := by
        rw [hρ₄, arrs_setVar]; exact hmem1₁
      have htab₄ : ρ₄.arrs (tabName (j + 1) ti) = arrOf n Tb := by
        rw [hρ₄, arrs_setVar]; exact htab₁
      refine ⟨ρ₄, 19, ((hr'₁.seq ((Run.ite_false (by rw [hcond]; simp [hkeep])
        Run.skip).seq hr'₄))).mono (by simp [Expr.size, Cond.size]), ?_, hak₄, le_rfl⟩
      refine ⟨hmm1₄, by omega, by omega, hmem1₄, htab₄, g, hmemd₄, ?_, ?_, ?_⟩
      · intro q hq
        rw [hmm₄] at hq
        rw [hak₄]
        obtain ⟨p, hp1, hp2, hp3⟩ := hsound q hq
        exact ⟨p, by omega, hp2, hp3⟩
      · intro p hp hTp
        rw [hak₄] at hp
        rw [hmm₄]
        have hpm : p ≠ ak := by
          rintro rfl
          exact hTp hT0
        exact hcomp p (by omega) hTp
      · intro q₁ q₂ h12 hq2
        rw [hmm₄] at hq2
        exact hmono q₁ q₂ h12 hq2
  -- the scan, entered at both counters zero
  obtain ⟨g₀, hg₀⟩ := hdst
  have hI₂ : AtomFilt n j ti mm1 Mem1 Tb σ₂ := by
    have hak₂ : σ₂.vars "ak" = 0 := by rw [hσ₂, vars_setVar, if_pos rfl]
    have hmm₂ : σ₂.vars "mm" = 0 := by
      rw [hσ₂, vars_setVar, if_neg (by decide), hσ₁, vars_setVar, if_pos rfl]
    have hmm1₂ : σ₂.vars (mnumName (j + 1)) = mm1 := by
      rw [hσ₂, vars_setVar, if_neg (Ne.symm (ak_ne_mnumName j)), hσ₁, vars_setVar,
        if_neg (mnumName_ne_mm (j + 1))]
      exact hmm1
    refine ⟨hmm1₂, by omega, by omega, ?_, ?_, g₀, ?_, ?_, ?_, ?_⟩
    · rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact hmem1
    · rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact htab
    · rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact hg₀
    · intro q hq; rw [hmm₂] at hq; omega
    · intro p hp; rw [hak₂] at hp; omega
    · intro q₁ q₂ _ hq2; rw [hmm₂] at hq2; omega
  obtain ⟨σ₃, hr₃, hI₃, hak₃⟩ :=
    (Csr.rowScan_spec B (23 * mm1 + 4) mm1 19 "ak" (mnumName (j + 1))
      (.seq (.assign "av" (.get (memName (j + 1)) (.var "ak")))
        (.seq (.ite (.lt (.lit 0) (.get (tabName (j + 1) ti) (.var "av")))
            (.seq (.store "mem" (.var "mm") (.var "av"))
              (.assign "mm" (.add (.var "mm") (.lit 1))))
            .skip)
          (.assign "ak" (.add (.var "ak") (.lit 1)))))
      (AtomFilt n j ti mm1 Mem1 Tb) hm1B (fun ρ hρ => ⟨hρ.1, hρ.2.1⟩) hstep (fun _ hρ => hρ)
      (fun ρ hρ => by
        have h : (19 + 4) * (mm1 - ρ.vars "ak") ≤ 23 * mm1 :=
          Nat.mul_le_mul le_rfl (by omega)
        omega)).run hI₂
  obtain ⟨hmm1₃, -, hmmle₃, hmem1₃, htab₃, g, hgarr, hsound, hcomp, hmono⟩ := hI₃
  rw [hak₃] at hsound hcomp hmmle₃
  refine ⟨σ₃, _, hr₁.seq (hr₂.seq hr₃), by rw [atomMemCost]; omega,
    g, σ₃.vars "mm", hgarr, rfl, hmmle₃,
    ⟨fun k hk => ?_, fun i k hik hk => hmono i k hik hk, fun k hk => ?_, fun a ha => ?_⟩,
    hmem1₃, htab₃, hmm1₃⟩
  · obtain ⟨p, hp1, hp2, -⟩ := hsound k hk
    rw [hp2]; exact hMlt p hp1
  · obtain ⟨p, hp1, hp2, hp3⟩ := hsound k hk
    refine ⟨by rw [hp2]; exact hMlt p hp1, ?_, ?_⟩
    · show A (g k) ≠ 0
      rw [hp2]; exact hMalv p hp1
    · show Tb (g k) ≠ 0
      rw [hp2]; exact hp3
  · obtain ⟨hlt, hA, hT⟩ := ha
    obtain ⟨p, hp1, hp2⟩ := hMcomp a hlt hA
    obtain ⟨q, hq1, hq2⟩ := hcomp p hp1 (by rw [hp2]; exact hT)
    exact ⟨q, hq1, by rw [hq2, hp2]⟩

/-! ### §3 The kill walk (design §6 (b), pass 4)

The atom's bits at the turn's kills. What the sum is worth is
`Refine.ScatterDeadFold.sum_bit_eq_ncard_inter`, whose four hypotheses
are `RamDriverCluster.KillListAt`'s four clauses — the reason the list
is stated at the sets, and the reason `killListCom` dedupes. -/

/-- The cost of the kill walk: the turn's kill count, at most the
buffer's width `mb`. Carrier-blind. -/
def killSumCost (kq : ℕ) : ℕ := 14 * kq + 8

/-- What the kill walk carries: the list, the row, and the partial sum
at the counter. -/
def KillSumInv (n mb j ti kq : ℕ) (kl Tb : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars (kkName j) = kq ∧ σ.vars "ke" ≤ kq ∧
    σ.arrs (klName j) = arrOf mb kl ∧ σ.arrs (tabName (j + 1) ti) = arrOf n Tb ∧
    σ.vars "kc" = ∑ e ∈ Finset.range (σ.vars "ke"), Tb (kl e)

theorem ke_ne_kkName (j : ℕ) : ("ke" : String) ≠ kkName j := by
  simp [kkName, String.ext_iff]

theorem kc_ne_kkName (j : ℕ) : ("kc" : String) ≠ kkName j := by
  simp [kkName, String.ext_iff]

/-- **The kill walk, walked.** At the exit `"kc"` holds the atom's bits
summed over the turn's kill list — the `∑` side of
`Refine.ScatterDeadFold.sum_bit_eq_ncard_inter`. The row is read only at
the listed vertices, which are exactly `RamDriverCluster.KillRowsAt`'s
domain: no clause about a row outside `alive ∪ kills` enters. -/
theorem killSumCom_spec {mb j ti kq : ℕ} {kl Tb : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hmbB : mb < B) (hkq : kq ≤ mb)
    (hkln : ∀ e, e < kq → kl e < n) (hbit : ∀ e, e < kq → Tb (kl e) ≤ 1) :
    Spec B (fun σ => σ.vars (kkName j) = kq ∧ σ.arrs (klName j) = arrOf mb kl ∧
        σ.arrs (tabName (j + 1) ti) = arrOf n Tb)
      (killSumCom j ti)
      (fun _ σ' => σ'.vars "kc" = ∑ e ∈ Finset.range kq, Tb (kl e) ∧
        σ'.vars (kkName j) = kq ∧ σ'.arrs (klName j) = arrOf mb kl ∧
        σ'.arrs (tabName (j + 1) ti) = arrOf n Tb)
      (killSumCost kq) := by
  have hkqB : kq < B := by omega
  have hsumle : ∀ m, m ≤ kq → (∑ e ∈ Finset.range m, Tb (kl e)) ≤ m := by
    intro m hm
    calc (∑ e ∈ Finset.range m, Tb (kl e)) ≤ ∑ _e ∈ Finset.range m, 1 :=
          Finset.sum_le_sum (fun e he => hbit e (by have := Finset.mem_range.1 he; omega))
      _ = m := by simp
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hkk, hkl, htab⟩ := hσ
  set σ₁ := σ.setVar "kc" 0 with hσ₁
  have hr₁ : Run B (.assign "kc" (.lit 0)) σ σ₁ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  set σ₂ := σ₁.setVar "ke" 0 with hσ₂
  have hr₂ : Run B (.assign "ke" (.lit 0)) σ₁ σ₂ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hstep : ∀ ρ : Env, KillSumInv n mb j ti kq kl Tb ρ → ρ.vars "ke" < kq →
      ∃ ρ' K', Run B (.seq (.assign "kc"
            (.add (.var "kc") (.get (tabName (j + 1) ti) (.get (klName j) (.var "ke")))))
          (.assign "ke" (.add (.var "ke") (.lit 1)))) ρ ρ' K' ∧
        KillSumInv n mb j ti kq kl Tb ρ' ∧ ρ'.vars "ke" = ρ.vars "ke" + 1 ∧ K' ≤ 10 := by
    intro ρ hρ hlt
    obtain ⟨hkkρ, hkeρ, hklρ, htabρ, hkcρ⟩ := hρ
    set ke := ρ.vars "ke" with hke
    have hkemb : ke < mb := by omega
    have hkln' : kl ke < n := hkln ke hlt
    have hbit' : Tb (kl ke) ≤ 1 := hbit ke hlt
    have hkee : (Expr.var "ke").evalB B ρ = some ke := by
      have h := evalB_var (B := B) (x := "ke") (σ := ρ) (by omega)
      rwa [← hke] at h
    have hinner : (Expr.get (klName j) (.var "ke")).evalB B ρ = some (kl ke) :=
      evalB_get hkee (by rw [hklρ, getElem?_arrOf kl hkemb]) (by omega)
    have houter : (Expr.get (tabName (j + 1) ti) (.get (klName j) (.var "ke"))).evalB B ρ =
        some (Tb (kl ke)) :=
      evalB_get hinner (by rw [htabρ, getElem?_arrOf Tb hkln']) (by omega)
    have hkce : (Expr.var "kc").evalB B ρ = some (ρ.vars "kc") := by
      refine evalB_var ?_
      rw [hkcρ]
      have := hsumle ke (by omega)
      omega
    have hadd : (Expr.add (Expr.var "kc")
        (.get (tabName (j + 1) ti) (.get (klName j) (.var "ke")))).evalB B ρ =
        some (ρ.vars "kc" + Tb (kl ke)) := by
      have h := evalB_bin hkce houter
        (show Bop.add.apply (ρ.vars "kc") (Tb (kl ke)) < B by
          rw [Bop.apply_add, hkcρ]
          have := hsumle ke (by omega)
          omega)
      rwa [Bop.apply_add] at h
    set ρ₁ := ρ.setVar "kc" (ρ.vars "kc" + Tb (kl ke)) with hρ₁
    have hr'₁ : Run B (.assign "kc"
        (.add (.var "kc") (.get (tabName (j + 1) ti) (.get (klName j) (.var "ke"))))) ρ ρ₁ 6 :=
      (Run.assign hadd).mono (by simp [Expr.size])
    have hke₁ : ρ₁.vars "ke" = ke := by rw [hρ₁, vars_setVar, if_neg (by decide)]
    have hkee₁ : (Expr.add (Expr.var "ke") (.lit 1)).evalB B ρ₁ = some (ke + 1) := by
      have h := evalB_bin (evalB_var (B := B) (x := "ke") (σ := ρ₁) (by rw [hke₁]; omega))
        (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
        (show Bop.add.apply (ρ₁.vars "ke") 1 < B by rw [Bop.apply_add, hke₁]; omega)
      rw [Bop.apply_add, hke₁] at h
      exact h
    set ρ₂ := ρ₁.setVar "ke" (ke + 1) with hρ₂
    have hr'₂ : Run B (.assign "ke" (.add (.var "ke") (.lit 1))) ρ₁ ρ₂ 4 :=
      (Run.assign hkee₁).mono (by simp [Expr.size])
    refine ⟨ρ₂, 10, (hr'₁.seq hr'₂).mono (by omega), ?_, ?_, le_rfl⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hρ₂, vars_setVar, if_neg (Ne.symm (ke_ne_kkName j)), hρ₁, vars_setVar,
          if_neg (Ne.symm (kc_ne_kkName j))]
        exact hkkρ
      · rw [hρ₂, vars_setVar, if_pos rfl]; omega
      · rw [hρ₂, arrs_setVar, hρ₁, arrs_setVar]; exact hklρ
      · rw [hρ₂, arrs_setVar, hρ₁, arrs_setVar]; exact htabρ
      · have h1 : ρ₂.vars "kc" = ρ₁.vars "kc" := by
          rw [hρ₂, vars_setVar, if_neg (by decide)]
        have h2 : ρ₂.vars "ke" = ke + 1 := by rw [hρ₂, vars_setVar, if_pos rfl]
        rw [h1, h2, hρ₁, vars_setVar, if_pos rfl, hkcρ, Finset.sum_range_succ]
    · rw [hρ₂, vars_setVar, if_pos rfl]
  have hI₂ : KillSumInv n mb j ti kq kl Tb σ₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ₂, vars_setVar, if_neg (Ne.symm (ke_ne_kkName j)), hσ₁, vars_setVar,
        if_neg (Ne.symm (kc_ne_kkName j))]
      exact hkk
    · rw [hσ₂, vars_setVar, if_pos rfl]; omega
    · rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact hkl
    · rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact htab
    · have h1 : σ₂.vars "kc" = σ₁.vars "kc" := by
        rw [hσ₂, vars_setVar, if_neg (by decide)]
      have h2 : σ₂.vars "ke" = 0 := by rw [hσ₂, vars_setVar, if_pos rfl]
      rw [h1, h2, hσ₁, vars_setVar, if_pos rfl]
      simp
  obtain ⟨σ₃, hr₃, hI₃, hke₃⟩ :=
    (Csr.rowScan_spec B (14 * kq + 4) kq 10 "ke" (kkName j)
      (.seq (.assign "kc"
          (.add (.var "kc") (.get (tabName (j + 1) ti) (.get (klName j) (.var "ke")))))
        (.assign "ke" (.add (.var "ke") (.lit 1))))
      (KillSumInv n mb j ti kq kl Tb) hkqB (fun ρ hρ => ⟨hρ.1, hρ.2.1⟩) hstep (fun _ hρ => hρ)
      (fun ρ hρ => by
        have h : (10 + 4) * (kq - ρ.vars "ke") ≤ 14 * kq := Nat.mul_le_mul le_rfl (by omega)
        omega)).run hI₂
  obtain ⟨hkk₃, -, hkl₃, htab₃, hkc₃⟩ := hI₃
  exact ⟨σ₃, _, hr₁.seq (hr₂.seq hr₃), by rw [killSumCost]; omega,
    by rw [hkc₃, hke₃], hkk₃, hkl₃, htab₃⟩

/-! ### §4 The outside probe (design §6 (b), pass 5)

One vertex answers for the whole outside class. The scan stops at the
first hit — the found branch sets the counter to the carrier's end — and
what it leaves is either a witness of `deadSet \ X` or the news that the
class is empty. Both are exactly the two branches
`Refine.ScatterDeadFold.outside_ncard_of_probe` and
`outside_ncard_of_empty` consume. -/

/-- The probe's charge at the **carrier** reading: one turn per vertex.
This is `outProbeCostB n n`, and it is the number the composition still
instantiates. -/
def outProbeCost (n : ℕ) : ℕ := 20 * n + 10

/-- **The probe's charge at the pigeonhole bound** (wave E4c-a). The
scan stops at the first vertex that is dead *and* out of the cluster,
and `outside_prefix_bound` below says every hit-free prefix is shorter
than the cluster: so the runtime is at most `min (xb + 1) n` turns once
`xb` bounds the cluster's size, not `n` of them. The `+ 1` is not slack
— the scan has to read the vertex *after* the last cluster member to
know it has left the cluster — and `outProbeCostB_at_xb_refuted` below
compiles that.

`min … n` keeps the carrier reading exact rather than merely implied:
`outProbeCostB n n = outProbeCost n` on the nose
(`outProbeCostB_carrier`), so the narrowing costs the composition
nothing at the instantiation it has today. -/
def outProbeCostB (n xb : ℕ) : ℕ := 20 * min (xb + 1) n + 10

/-- The carrier reading is the pigeonhole one at `xb := n`. -/
theorem outProbeCostB_carrier (n : ℕ) : outProbeCostB n n = outProbeCost n := by
  simp only [outProbeCostB, outProbeCost]; omega

theorem outProbeCostB_mono {n xb xb' : ℕ} (h : xb ≤ xb') :
    outProbeCostB n xb ≤ outProbeCostB n xb' := by
  simp only [outProbeCostB]; omega

theorem outProbeCostB_le_carrier (n xb : ℕ) : outProbeCostB n xb ≤ outProbeCost n := by
  simp only [outProbeCostB, outProbeCost]; omega

/-! The pigeonhole, restated here rather than imported. The landed
statement is `Refine.DeadRowProbe.exists_outside_in_prefix`, and that
file is **downstream** of this one — `DeadRowProbe` imports `DeadSweep`,
which imports the driver, which imports this file. This is the road's
third import-order defect and it is handled the landed way
(`RamDriver.TableInvOn` vs `Refine.DeadRowProbe.TableInvOn`): the
predicate is restated upstream and the identification is recorded
downstream. Here the restated object is a *theorem*, not a definition,
so there is nothing to record by `rfl`; the two proofs are the same
counting argument and `Refine.DeadRowProbe.exists_outside_in_prefix` is
the one every set-side consumer quotes. -/

/-- **Among the first `X.ncard + 1` vertices one is outside `X`.** -/
theorem exists_outside_le_ncard {n : ℕ} (X : Set (Fin n)) (hlt : X.ncard < n) :
    ∃ z : Fin n, (z : ℕ) ≤ X.ncard ∧ z ∉ X := by
  by_contra hcon
  have hall : ∀ z : Fin n, (z : ℕ) ≤ X.ncard → z ∈ X := by
    intro z hz
    by_contra hzX
    exact hcon ⟨z, hz, hzX⟩
  set f : Fin (X.ncard + 1) → Fin n :=
    fun i => ⟨(i : ℕ), lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt hlt)⟩ with hf
  have hinj : Function.Injective f := fun a b hab => by
    simpa [hf, Fin.ext_iff] using hab
  have hsub : Set.range f ⊆ X := by
    rintro z ⟨i, rfl⟩
    exact hall _ (Nat.le_of_lt_succ i.isLt)
  have hr : (Set.range f).ncard = X.ncard + 1 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have := Set.ncard_le_ncard hsub X.toFinite
  omega

/-- **The probe's loop bound, off the cluster's size.** A prefix of the
carrier that the probe walks without stopping is a prefix of vertices
that are in the cluster — the mask's own pointwise clause says an alive
vertex is one — so it is no longer than the cluster.

This is the hypothesis `outProbeCom_specB` takes, produced at the only
data a caller has: the cluster as a set and the child mask's
containment in it. -/
theorem outside_prefix_bound {n : ℕ} {X : Set (Fin n)} {Alv' Xa : ℕ → ℕ}
    (hXaS : ∀ v : Fin n, Xa (v : ℕ) ≠ 0 ↔ v ∈ X)
    (hsub : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ X)
    (m : ℕ) (hm : m ≤ n) (hfree : ∀ z, z < m → ¬ (Alv' z = 0 ∧ Xa z = 0)) :
    m ≤ X.ncard := by
  by_contra hcon
  have hltn : X.ncard < n := by omega
  obtain ⟨z, hzle, hzX⟩ := exists_outside_le_ncard X hltn
  have hXa0 : Xa (z : ℕ) = 0 := by
    by_contra hc
    exact hzX ((hXaS z).1 hc)
  have hAlv0 : Alv' (z : ℕ) = 0 := by
    by_contra hc
    exact hzX (hsub z hc)
  exact hfree (z : ℕ) (by omega) ⟨hAlv0, hXa0⟩

/-- What the probe carries: the two arrays it reads, the counter, and
the verdict — either nothing below the counter is dead-and-outside, or
the register holds a vertex that is.

**Wave E4c-a: the exit clause.** `of ≠ 0 → oi = n` was true of the walk
all along and never stated. The pigeonhole charge needs it: the variant
is measured against the cluster's size, so a state that has already
found its witness must be past the guard rather than merely flagged. -/
def ProbeInv (n j : ℕ) (Alv' Xa : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs (alvName (j + 1)) = arrOf n Alv' ∧
    σ.arrs (cluName j) = arrOf n Xa ∧ σ.vars "oi" ≤ n ∧ σ.vars "of" ≤ 1 ∧
    (σ.vars "of" = 0 → ∀ z, z < σ.vars "oi" → ¬ (Alv' z = 0 ∧ Xa z = 0)) ∧
    (σ.vars "of" ≠ 0 → σ.vars "oz" < n ∧ Alv' (σ.vars "oz") = 0 ∧ Xa (σ.vars "oz") = 0) ∧
    (σ.vars "of" ≠ 0 → σ.vars "oi" = n)

/-- **The outside probe, walked at the pigeonhole bound** (wave E4c-a).

The program is **unchanged** — this is the same `outProbeCom j` the
carrier walk ran, charged against a variant that counts down from the
cluster's size instead of the carrier's. The one thing it needs is
`hstop`: that a hit-free prefix is short, which is
`outside_prefix_bound` at the turn's own cluster. So narrowing the
probe is accounting and not a program change.

**Wave R1.8-T3-flip (c1d): the found flag is a bit.** The clause was in
`ProbeInv` all along and dropped at the interface; the composition needs
it, because the bit pass reads `"of"` in a guard and `evalB_var`'s
obligation is a word bound. -/
theorem outProbeCom_specB {j xb : ℕ} {Alv' Xa : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B)
    (hAB : ∀ k, k < n → Alv' k < B) (hXB : ∀ k, k < n → Xa k < B)
    (hstop : ∀ m, m ≤ n → (∀ z, z < m → ¬ (Alv' z = 0 ∧ Xa z = 0)) → m ≤ xb) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs (alvName (j + 1)) = arrOf n Alv' ∧
        σ.arrs (cluName j) = arrOf n Xa)
      (outProbeCom j)
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.arrs (alvName (j + 1)) = arrOf n Alv' ∧
        σ'.arrs (cluName j) = arrOf n Xa ∧ σ'.vars "of" ≤ 1 ∧
        (σ'.vars "of" = 0 → ∀ z, z < n → ¬ (Alv' z = 0 ∧ Xa z = 0)) ∧
        (σ'.vars "of" ≠ 0 → σ'.vars "oz" < n ∧ Alv' (σ'.vars "oz") = 0 ∧
          Xa (σ'.vars "oz") = 0))
      (outProbeCostB n xb) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, halv, hclu⟩ := hσ
  set σ₁ := σ.setVar "of" 0 with hσ₁
  have hr₁ : Run B (.assign "of" (.lit 0)) σ σ₁ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  set σ₂ := σ₁.setVar "oz" 0 with hσ₂
  have hr₂ : Run B (.assign "oz" (.lit 0)) σ₁ σ₂ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  set σ₃ := σ₂.setVar "oi" 0 with hσ₃
  have hr₃ : Run B (.assign "oi" (.lit 0)) σ₂ σ₃ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hof₃ : σ₃.vars "of" = 0 := by
    rw [hσ₃, vars_setVar, if_neg (by decide), hσ₂, vars_setVar, if_neg (by decide),
      hσ₁, vars_setVar, if_pos rfl]
  have hI₃ : ProbeInv n j Alv' Xa σ₃ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ₃, vars_setVar, if_neg (by decide), hσ₂, vars_setVar, if_neg (by decide),
        hσ₁, vars_setVar, if_neg (by decide)]
      exact hn
    · rw [hσ₃, arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact halv
    · rw [hσ₃, arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setVar]; exact hclu
    · rw [hσ₃, vars_setVar, if_pos rfl]; omega
    · rw [hof₃]; omega
    · intro _ z hz
      rw [hσ₃, vars_setVar, if_pos rfl] at hz
      omega
    · intro hne; exact absurd hof₃ hne
    · intro hne; exact absurd hof₃ hne
  -- the loop
  have hbody : Spec B (fun ρ => ProbeInv n j Alv' Xa ρ ∧
        (Cond.lt (.var "oi") (.var "n")).evalB B ρ = some true)
      (.ite (.lt (.lit 0) (.get (alvName (j + 1)) (.var "oi")))
        (.assign "oi" (.add (.var "oi") (.lit 1)))
        (.ite (.lt (.lit 0) (.get (cluName j) (.var "oi")))
          (.assign "oi" (.add (.var "oi") (.lit 1)))
          (.seq (.assign "of" (.lit 1))
            (.seq (.assign "oz" (.var "oi"))
              (.assign "oi" (.var "n"))))))
      (fun ρ ρ' => ProbeInv n j Alv' Xa ρ' ∧
        min (xb + 1) n - ρ'.vars "oi" < min (xb + 1) n - ρ.vars "oi") 16 := by
    refine Spec.of_exists (fun ρ hρ => ?_)
    obtain ⟨⟨hnρ, halvρ, hcluρ, hoiρ, hofρ, hno, hyes, hdone⟩, htrue⟩ := hρ
    have hoilt : ρ.vars "oi" < n := by
      have := lt_of_condLt_true htrue
      omega
    -- **the walk has not stopped yet**, so the flag is clear and the counter is
    -- inside the cluster — which is what makes the variant the cluster's and not
    -- the carrier's
    have hof0 : ρ.vars "of" = 0 := by
      by_contra hc
      have := hdone hc
      omega
    have hoixb : ρ.vars "oi" ≤ xb := hstop _ hoiρ (hno hof0)
    have hmlt : ρ.vars "oi" < min (xb + 1) n := by omega
    set oi := ρ.vars "oi" with hoi
    have hoie : (Expr.var "oi").evalB B ρ = some oi := by
      have h := evalB_var (B := B) (x := "oi") (σ := ρ) (by omega)
      rwa [← hoi] at h
    have hbump : ∀ τ : Env, τ.vars "oi" = oi →
        ∃ τ', Run B (.assign "oi" (.add (.var "oi") (.lit 1))) τ τ' 4 ∧
          τ' = τ.setVar "oi" (oi + 1) := by
      intro τ hτ
      have he : (Expr.add (Expr.var "oi") (.lit 1)).evalB B τ = some (oi + 1) := by
        have h := evalB_bin (evalB_var (B := B) (x := "oi") (σ := τ) (by rw [hτ]; omega))
          (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
          (show Bop.add.apply (τ.vars "oi") 1 < B by rw [Bop.apply_add, hτ]; omega)
        rw [Bop.apply_add, hτ] at h
        exact h
      exact ⟨_, (Run.assign he).mono (by simp [Expr.size]), rfl⟩
    have hcondA : (Cond.lt (.lit 0) (.get (alvName (j + 1)) (.var "oi"))).evalB B ρ =
        some (decide (0 < Alv' oi)) :=
      evalB_condLt (evalB_lit (by omega))
        (evalB_get hoie (by rw [halvρ, getElem?_arrOf Alv' hoilt]) (hAB _ hoilt))
    have hcondX : (Cond.lt (.lit 0) (.get (cluName j) (.var "oi"))).evalB B ρ =
        some (decide (0 < Xa oi)) :=
      evalB_condLt (evalB_lit (by omega))
        (evalB_get hoie (by rw [hcluρ, getElem?_arrOf Xa hoilt]) (hXB _ hoilt))
    -- the three branches
    have hbumped : ∀ τ : Env, τ = ρ.setVar "oi" (oi + 1) → ¬ (Alv' oi = 0 ∧ Xa oi = 0) →
        ProbeInv n j Alv' Xa τ ∧ min (xb + 1) n - τ.vars "oi" < min (xb + 1) n - oi := by
      intro τ hτ hnot
      have hoiτ : τ.vars "oi" = oi + 1 := by rw [hτ, vars_setVar, if_pos rfl]
      have hofτ : τ.vars "of" = 0 := by
        rw [hτ, vars_setVar, if_neg (by decide)]; exact hof0
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hoiτ]; omega⟩
      · rw [hτ, vars_setVar, if_neg (by decide)]; exact hnρ
      · rw [hτ, arrs_setVar]; exact halvρ
      · rw [hτ, arrs_setVar]; exact hcluρ
      · omega
      · rw [hofτ]; omega
      · intro hof z hz
        rw [hτ, vars_setVar, if_neg (by decide)] at hof
        rw [hoiτ] at hz
        rcases Nat.lt_or_ge z oi with h | h
        · exact hno hof z h
        · have : z = oi := by omega
          rw [this]; exact hnot
      · intro hof; exact absurd hofτ hof
      · intro hof; exact absurd hofτ hof
    by_cases hA : 0 < Alv' oi
    · obtain ⟨τ, hrτ, hτ⟩ := hbump ρ rfl
      exact ⟨τ, 16, (Run.ite_true (by rw [hcondA]; simp [hA]) hrτ).mono
        (by simp [Expr.size, Cond.size]), le_rfl,
        hbumped τ hτ (fun h => absurd h.1 (by omega))⟩
    · by_cases hX : 0 < Xa oi
      · obtain ⟨τ, hrτ, hτ⟩ := hbump ρ rfl
        exact ⟨τ, 16, (Run.ite_false (by rw [hcondA]; simp [hA])
          (Run.ite_true (by rw [hcondX]; simp [hX]) hrτ)).mono
            (by simp [Expr.size, Cond.size]), le_rfl,
          hbumped τ hτ (fun h => absurd h.2 (by omega))⟩
      · -- the hit: record the vertex and jump to the end
        set ρ₁ := ρ.setVar "of" 1 with hρ₁
        have hr'₁ : Run B (.assign "of" (.lit 1)) ρ ρ₁ 2 :=
          (Run.assign (evalB_lit (show (1 : ℕ) < B by omega))).mono (by simp [Expr.size])
        have hoi₁ : ρ₁.vars "oi" = oi := by rw [hρ₁, vars_setVar, if_neg (by decide)]
        set ρ₂ := ρ₁.setVar "oz" oi with hρ₂
        have hr'₂ : Run B (.assign "oz" (.var "oi")) ρ₁ ρ₂ 2 := by
          have h := evalB_var (B := B) (x := "oi") (σ := ρ₁) (by rw [hoi₁]; omega)
          rw [hoi₁] at h
          exact (Run.assign h).mono (by simp [Expr.size])
        have hn₂ : ρ₂.vars "n" = n := by
          rw [hρ₂, vars_setVar, if_neg (by decide), hρ₁, vars_setVar, if_neg (by decide)]
          exact hnρ
        set ρ₃ := ρ₂.setVar "oi" n with hρ₃
        have hr'₃ : Run B (.assign "oi" (.var "n")) ρ₂ ρ₃ 2 := by
          have h := evalB_var (B := B) (x := "n") (σ := ρ₂) (by rw [hn₂]; omega)
          rw [hn₂] at h
          exact (Run.assign h).mono (by simp [Expr.size])
        refine ⟨ρ₃, 16, (Run.ite_false (by rw [hcondA]; simp [hA])
          (Run.ite_false (by rw [hcondX]; simp [hX])
            (hr'₁.seq (hr'₂.seq hr'₃)))).mono (by simp [Expr.size, Cond.size]), le_rfl, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hρ₃, vars_setVar, if_neg (by decide)]; exact hn₂
          · rw [hρ₃, arrs_setVar, hρ₂, arrs_setVar, hρ₁, arrs_setVar]; exact halvρ
          · rw [hρ₃, arrs_setVar, hρ₂, arrs_setVar, hρ₁, arrs_setVar]; exact hcluρ
          · rw [hρ₃, vars_setVar, if_pos rfl]
          · rw [hρ₃, vars_setVar, if_neg (by decide), hρ₂, vars_setVar, if_neg (by decide),
              hρ₁, vars_setVar, if_pos rfl]
          · intro hof
            exfalso
            rw [hρ₃, vars_setVar, if_neg (by decide), hρ₂, vars_setVar, if_neg (by decide),
              hρ₁, vars_setVar, if_pos rfl] at hof
            omega
          · intro _
            rw [hρ₃, vars_setVar, if_neg (by decide), hρ₂, vars_setVar, if_pos rfl]
            exact ⟨hoilt, by omega, by omega⟩
          · intro _
            rw [hρ₃, vars_setVar, if_pos rfl]
        · rw [hρ₃, vars_setVar, if_pos rfl]
          omega
  obtain ⟨σ₄, hr₄, hI₄, hfalse⟩ :=
    (Spec.while_count (B := B) (P := ProbeInv n j Alv' Xa) (K := 20 * min (xb + 1) n + 4)
      (ProbeInv n j Alv' Xa) (fun τ => min (xb + 1) n - τ.vars "oi") 16
      (fun τ hτ => by
        refine ⟨decide (τ.vars "oi" < τ.vars "n"), ?_⟩
        refine evalB_condLt (evalB_var (by have := hτ.2.2.2.1; omega)) ?_
        exact evalB_var (by rw [hτ.1]; omega))
      hbody (fun _ hτ => hτ)
      (fun τ _ => by
        have h : (1 + 3 + 16) * (min (xb + 1) n - τ.vars "oi") ≤ 20 * min (xb + 1) n :=
          Nat.mul_le_mul le_rfl (by omega)
        simp only [size_condLt, size_var]
        omega)).run hI₃
  obtain ⟨hn₄, halv₄, hclu₄, hoi₄, hof₄, hno₄, hyes₄, -⟩ := hI₄
  have hoin : σ₄.vars "oi" = n := by
    have h := le_of_condLt_false hfalse
    rw [hn₄] at h
    omega
  rw [hoin] at hno₄
  exact ⟨σ₄, _, hr₁.seq (hr₂.seq (hr₃.seq hr₄)), by rw [outProbeCostB]; omega,
    hn₄, halv₄, hclu₄, hof₄, hno₄, hyes₄⟩

/-- **The outside probe at the carrier reading**, which is what the
composition still instantiates: `outProbeCom_specB` at `xb := n`, where
the loop bound is the trivial `m ≤ n` and the charge collapses to the
landed `20·n + 10` on the nose (`outProbeCostB_carrier`). Nothing above
this line moves; what E4c-a bought is the `xb` above it. -/
theorem outProbeCom_spec {j : ℕ} {Alv' Xa : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B)
    (hAB : ∀ k, k < n → Alv' k < B) (hXB : ∀ k, k < n → Xa k < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs (alvName (j + 1)) = arrOf n Alv' ∧
        σ.arrs (cluName j) = arrOf n Xa)
      (outProbeCom j)
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.arrs (alvName (j + 1)) = arrOf n Alv' ∧
        σ'.arrs (cluName j) = arrOf n Xa ∧ σ'.vars "of" ≤ 1 ∧
        (σ'.vars "of" = 0 → ∀ z, z < n → ¬ (Alv' z = 0 ∧ Xa z = 0)) ∧
        (σ'.vars "of" ≠ 0 → σ'.vars "oz" < n ∧ Alv' (σ'.vars "oz") = 0 ∧
          Xa (σ'.vars "oz") = 0))
      (outProbeCost n) :=
  (outProbeCom_specB (xb := n) hB hnB hAB hXB (fun _ hm _ => hm)).mono
    (le_of_eq (outProbeCostB_carrier n))

/-! ### §4b What the pigeonhole charge buys, and what it does not

The probe's slot is the first of `Refine.C0CloseProbe` §4's five
carrier summands to come off by accounting alone. Two compiled
statements say exactly how much: at a **fixed** cluster the narrow
charge is a constant while the carrier one is unbounded, and the `+ 1`
in `min (xb + 1) n` is not slack that could have been shaved. -/

#guard outProbeCostB 4096 3 = 90
#guard outProbeCost 4096 = 81930

/-- **The carrier term dies at the probe.** At a fixed cluster size no
numeral bounds the landed probe charge in terms of the narrow one —
the honest form of "the `Θ(n)` per atom is gone from this slot", in
`Refine.ScatterBlock.scatBlockK_carrier_free_vs_scatK`'s shape. -/
theorem outProbeCostB_carrier_free (xb c : ℕ) :
    ∃ n, c * outProbeCostB n xb < outProbeCost n := by
  refine ⟨c * (20 * (xb + 1) + 10) + 1, ?_⟩
  have h : outProbeCostB (c * (20 * (xb + 1) + 10) + 1) xb ≤ 20 * (xb + 1) + 10 := by
    simp only [outProbeCostB]; omega
  have h₂ : c * outProbeCostB (c * (20 * (xb + 1) + 10) + 1) xb
      ≤ c * (20 * (xb + 1) + 10) := Nat.mul_le_mul_left _ h
  simp only [outProbeCost]
  omega

/-- **And the `+ 1` is load-bearing.** A cluster of `xb` vertices sitting
at the front of the carrier is left only at index `xb`, so the scan runs
`xb + 1` turns; a charge of `20·xb + 10` would be claiming to read a cell
it never looked at. This is the negative control the campaign's probe
discipline asks for beside every narrowing. -/
theorem outProbeCostB_at_xb_refuted :
    ¬ (∀ n xb : ℕ, outProbeCostB n xb ≤ 20 * xb + 10) := by
  intro h
  have := h 4 1
  simp only [outProbeCostB] at this
  omega

/-- The outside count's charge: one assignment over an expression of
five nodes. **Wave R1.8-T3-flip (c1b) corrected this slot**: `scatDeadK`
carried `2` for this pass, which is `Run.assign`'s charge for a literal
(`1 + (Expr.lit _).size`), and the pass's expression is
`sub (sub (var "n") (var (mnumName (j+1)))) (var (kkName j))` — five
nodes, so `1 + 5`. No walk could ever have been closed at the old
number; the slot is the only summand of `scatDeadK` that had no proved
leaf under it. -/
def outCntCost : ℕ := 6

/-- **The outside count, walked.** `Refine.ScatterDeadFold.outside_ncard_eq`
is what the three scalars are worth — `|dead \ X| = n − |alive| − |kills|`
— and the pass is the one assignment that forms them. Nothing is
scanned. -/
theorem outCntCom_spec {j mm1 kq : ℕ} (hB : 1 < B) (hnB : n < B)
    (hmm1 : mm1 < B) (hkq : kq < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars (mnumName (j + 1)) = mm1 ∧
        σ.vars (kkName j) = kq)
      (outCntCom j)
      (fun _ σ' => σ'.vars "oc" = n - mm1 - kq ∧ σ'.vars "n" = n ∧
        σ'.vars (mnumName (j + 1)) = mm1 ∧ σ'.vars (kkName j) = kq)
      outCntCost := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hmv, hkv⟩ := hσ
  have hin : (Expr.sub (Expr.var "n") (.var (mnumName (j + 1)))).evalB B σ =
      some (n - mm1) := by
    have h := evalB_bin (evalB_var (B := B) (x := "n") (σ := σ) (by rw [hn]; omega))
      (evalB_var (B := B) (x := mnumName (j + 1)) (σ := σ) (by rw [hmv]; omega))
      (show Bop.sub.apply (σ.vars "n") (σ.vars (mnumName (j + 1))) < B by
        rw [Bop.apply_sub, hn, hmv]; omega)
    rwa [Bop.apply_sub, hn, hmv] at h
  have hout : (Expr.sub (Expr.sub (.var "n") (.var (mnumName (j + 1))))
      (.var (kkName j))).evalB B σ = some (n - mm1 - kq) := by
    have h := evalB_bin hin (evalB_var (B := B) (x := kkName j) (σ := σ) (by rw [hkv]; omega))
      (show Bop.sub.apply (n - mm1) (σ.vars (kkName j)) < B by
        rw [Bop.apply_sub, hkv]; omega)
    rwa [Bop.apply_sub, hkv] at h
  refine ⟨σ.setVar "oc" (n - mm1 - kq), _, Run.assign hout, ?_, ?_, ?_, ?_, ?_⟩
  · rw [outCntCost]; simp only [Expr.size]; omega
  · rw [vars_setVar, if_pos rfl]
  · rw [vars_setVar, if_neg (by decide)]; exact hn
  · rw [vars_setVar, if_neg (by simp [mnumName, String.ext_iff])]; exact hmv
  · rw [vars_setVar, if_neg (by simp [kkName, String.ext_iff])]; exact hkv

/-! ### §5 The verdict: the three registers decide the atom

The semantic half of pass 6, machine-free. What the three walks leave —
a bit sum over the kill list, a probe verdict, and three scalars — is
turned into `Refine.ScatterDeadEngine.scatVal_of_cnt`'s two hypotheses,
and the atom's answer is the threshold against the sum.

**The alignment the design flags.** `RamDriverCluster.KillListAt`'s set
is stated at the turn's own data — the PARENT mask, the cluster and the
batch — because the child mask alone cannot tell a kill from a vertex
that was dead already (`KillRowsAt`'s docstring). The dead fold's set is
`deadSet n Alv' ∩ X`, at the CHILD mask. `turnKills_eq_dead_inter`
below is the identification, and the hypothesis it costs is exactly
`Refine.MassAlive.inCluster_alive_iff`'s conclusion at an alive centre —
a cluster is alive-homogeneous, so every vertex of `X` is alive at the
parent depth. That is a fact the level already holds (the compaction
lists alive centres only, `RamDriver.compactCom`), so nothing of
`TableInv`/`LevelPost` has to move for it. -/

/-- The turn's kill set as `RamDriverCluster.KillListAt` states it: the
vertices alive at the parent depth, in the cluster, and in the batch. -/
def turnKills (M : ℕ → ℕ) (X W : Set (Fin n)) : Set (Fin n) :=
  {v : Fin n | M (v : ℕ) ≠ 0 ∧ v ∈ X ∧ v ∈ W}

/-- **The kill list's set IS the dead fold's kill half.** The two are
stated at different data on purpose; what identifies them is the
pointwise clause of `RamDriverCluster.BatchData` (wave R1.8-T1) in one
direction and the alive-homogeneity of a cluster in the other. -/
theorem turnKills_eq_dead_inter {M Alv' : ℕ → ℕ} {X W : Set (Fin n)}
    (hpt : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 ↔ (M (v : ℕ) ≠ 0 ∧ v ∈ X ∧ v ∉ W))
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0) :
    turnKills M X W = ScatterDeadFold.deadSet n Alv' ∩ X := by
  ext v
  constructor
  · rintro ⟨hM, hX, hW⟩
    refine ⟨?_, hX⟩
    show Alv' (v : ℕ) = 0
    by_contra h
    exact ((hpt v).1 h).2.2 hW
  · rintro ⟨hd, hX⟩
    have hM := hXalive v hX
    refine ⟨hM, hX, ?_⟩
    by_contra hW
    exact absurd (ScatterDeadFold.mem_deadSet.1 hd) ((hpt v).2 ⟨hM, hX, hW⟩)

/-- **The atom's verdict, decided by the three registers.** The engine's
counter, the kill walk's bit sum and the probe's bit times the outside
count decide the scatter atom — and no term of the three reads a table
row outside `alive ∪ kills`, which is the whole content of the R1.8
flip.

The kill-row hypothesis `hkbit` is asked at `turnKills`, which is
`RamDriverCluster.KillRowsAt`'s domain verbatim; the counter hypothesis
`hcnt` is `Refine.ScatterDeadEngine.scatBlockCnt_specW`'s last clause
verbatim; and the probe hypothesis is the two exits of
`outProbeCom_spec`. Nothing else about the tables enters. -/
theorem atomTerms_iff_scatVal {L mb cap : ℕ} {G A : SimpleGraph (Fin n)}
    {M Alv' Xa Tb kl : ℕ → ℕ} {col : Coloring n L} {w : Fin mb → Fin n}
    {X W : Set (Fin n)} {mm1 kq cnt kc bb oc : ℕ}
    (σs : ScatterSentence (Lax3Proofs.Evaluator.isoPalette (L + 1) mb cap))
    (hloc : IsLocal σs.β) (hw : ∀ i, w i ∈ X)
    (hXset : markSet n Xa = X)
    (hpt : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 ↔ (M (v : ℕ) ≠ 0 ∧ v ∈ X ∧ v ∉ W))
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hmm1 : (markSet n Alv').ncard = mm1)
    (hklt : ∀ e, e < kq → kl e < n)
    (hkinj : ∀ e₁, e₁ < kq → ∀ e₂, e₂ < kq → kl e₁ = kl e₂ → e₁ = e₂)
    (hksound : ∀ e, (he : e < kq) → (⟨kl e, hklt e he⟩ : Fin n) ∈ turnKills M X W)
    (hkcomp : ∀ v : Fin n, v ∈ turnKills M X W → ∃ e, e < kq ∧ kl e = (v : ℕ))
    (hkbit : ∀ v : Fin n, v ∈ turnKills M X W →
      Tb (v : ℕ) ≤ 1 ∧ (Tb (v : ℕ) ≠ 0 ↔ v ∈ ScatterDeadFold.satSet G A Alv' col X w σs.β))
    (hkc : kc = ∑ e ∈ Finset.range kq, Tb (kl e))
    (hoc : oc = n - mm1 - kq)
    (hout : ((∀ z, z < n → ¬ (Alv' z = 0 ∧ Xa z = 0)) ∧ bb = 0) ∨
      (∃ zo : Fin n, Alv' (zo : ℕ) = 0 ∧ Xa (zo : ℕ) = 0 ∧ bb ≤ 1 ∧
        (bb ≠ 0 ↔ zo ∈ ScatterDeadFold.satSet G A Alv' col X w σs.β)))
    (hcnt : ∀ e : ℕ, (σs.t ≤ cnt + e ↔
      σs.t ≤ (greedySet (masked G Alv') σs.r
        (ScatterDeadFold.satSet G A Alv' col X w σs.β ∩ markSet n Alv')).ncard + e)) :
    (RamDriverCluster.ScatVal (masked G Alv') (stepColoringP cap A col X w) σs ↔
      σs.t ≤ cnt + (kc + bb * oc)) := by
  classical
  set S := ScatterDeadFold.satSet G A Alv' col X w σs.β with hS
  have hK : turnKills M X W = ScatterDeadFold.deadSet n Alv' ∩ X :=
    turnKills_eq_dead_inter hpt hXalive
  -- the kill term
  have hkcval : kc = (ScatterDeadFold.deadSet n Alv' ∩ X ∩ S).ncard := by
    rw [hkc, ScatterDeadFold.sum_bit_eq_ncard_inter hklt hkinj hksound hkcomp hkbit, hK]
  -- the outside count, off the three scalars
  have hkqval : (ScatterDeadFold.deadSet n Alv' ∩ X).ncard = kq := by
    rw [← hK]
    exact ncard_eq_of_enum hklt hkinj hksound hkcomp
  have hocval : oc = (ScatterDeadFold.deadSet n Alv' \ X).ncard := by
    rw [ScatterDeadFold.outside_ncard_eq n Alv' X, hmm1, hkqval, hoc]
  -- the outside term, from the probe's two exits
  have houtval : bb * oc = ((ScatterDeadFold.deadSet n Alv' \ X) ∩ S).ncard := by
    rcases hout with ⟨hno, hbb0⟩ | ⟨zo, hzoA, hzoX, hbb1, hbbiff⟩
    · have hemp : ScatterDeadFold.deadSet n Alv' \ X = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun v hv => ?_
        refine hno (v : ℕ) v.isLt ⟨ScatterDeadFold.mem_deadSet.1 hv.1, ?_⟩
        by_contra hXa
        exact hv.2 (hXset ▸ (RamDriverCluster.mem_markSet.2 hXa))
      rw [hbb0, ScatterDeadFold.outside_ncard_of_empty (S := S) hemp, Nat.zero_mul]
    · have hzo : zo ∈ ScatterDeadFold.deadSet n Alv' \ X := by
        refine ⟨ScatterDeadFold.mem_deadSet.2 hzoA, fun hc => ?_⟩
        exact absurd (RamDriverCluster.mem_markSet.1 (hXset ▸ hc : zo ∈ markSet n Xa)) (by omega)
      rw [ScatterDeadFold.outside_ncard_of_probe (G := G) (A := A) (col := col) hw hloc hzo,
        ← hocval]
      by_cases hb : bb = 0
      · rw [if_neg (fun hc => (hbbiff.2 hc) hb), hb, Nat.zero_mul]
      · rw [if_pos (hbbiff.1 hb), show bb = 1 by omega, Nat.one_mul]
  -- and the fold
  exact ScatterDeadEngine.scatVal_of_cnt (G := G) (A := A) (M' := Alv') (col := col)
    (Xc := X) (w := w) σs hcnt hkcval houtval

/-- **The atom's verdict at the turn's own data** (wave R1.8-T3-flip
(c2a)). The same statement with `RamDriverCluster.ClusterData` in place
of the two hypotheses the turn owns: `hw` is `ClusterData.mem_cluster`
— the padded enumeration is the batch's cluster half, because
`RamDriver.enumBatch` guards on the cluster indicator — and `hpt` is
`RamDriverCluster.BatchData`'s pointwise mask clause (wave R1.8-T1).

This is the discharge `outside_class_not_uniform_refuted` said was
missing: nothing above the turn has to supply anything, and neither `X`
nor `w` has to escape `clusterStepImplements`'s existential. -/
theorem atomTerms_iff_scatVal_of_clusterData {L mb cap jd Bw : ℕ}
    {G A : SimpleGraph (Fin n)}
    {M Alv' Gam' Xa Tb kl : ℕ → ℕ} {col : Coloring n L} {w : Fin mb → Fin n}
    {X W : Set (Fin n)} {mm1 kq cnt kc bb oc : ℕ} {σ : Env}
    (σs : ScatterSentence (Lax3Proofs.Evaluator.isoPalette (L + 1) mb cap))
    (hloc : IsLocal σs.β)
    (hdat : RamDriverCluster.ClusterData n mb jd Bw G M X W w Alv' Gam' σ)
    (hXset : markSet n Xa = X)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hmm1 : (markSet n Alv').ncard = mm1)
    (hklt : ∀ e, e < kq → kl e < n)
    (hkinj : ∀ e₁, e₁ < kq → ∀ e₂, e₂ < kq → kl e₁ = kl e₂ → e₁ = e₂)
    (hksound : ∀ e, (he : e < kq) → (⟨kl e, hklt e he⟩ : Fin n) ∈ turnKills M X W)
    (hkcomp : ∀ v : Fin n, v ∈ turnKills M X W → ∃ e, e < kq ∧ kl e = (v : ℕ))
    (hkbit : ∀ v : Fin n, v ∈ turnKills M X W →
      Tb (v : ℕ) ≤ 1 ∧ (Tb (v : ℕ) ≠ 0 ↔ v ∈ ScatterDeadFold.satSet G A Alv' col X w σs.β))
    (hkc : kc = ∑ e ∈ Finset.range kq, Tb (kl e))
    (hoc : oc = n - mm1 - kq)
    (hout : ((∀ z, z < n → ¬ (Alv' z = 0 ∧ Xa z = 0)) ∧ bb = 0) ∨
      (∃ zo : Fin n, Alv' (zo : ℕ) = 0 ∧ Xa (zo : ℕ) = 0 ∧ bb ≤ 1 ∧
        (bb ≠ 0 ↔ zo ∈ ScatterDeadFold.satSet G A Alv' col X w σs.β)))
    (hcnt : ∀ e : ℕ, (σs.t ≤ cnt + e ↔
      σs.t ≤ (greedySet (masked G Alv') σs.r
        (ScatterDeadFold.satSet G A Alv' col X w σs.β ∩ markSet n Alv')).ncard + e)) :
    (RamDriverCluster.ScatVal (masked G Alv') (stepColoringP cap A col X w) σs ↔
      σs.t ≤ cnt + (kc + bb * oc)) :=
  atomTerms_iff_scatVal σs hloc hdat.mem_cluster hXset hdat.1.2.2.2.2.2.2.1 hXalive hmm1
    hklt hkinj hksound hkcomp hkbit hkc hoc hout hcnt

/-! ### §5b The two remaining leaves: the outside bit and the verdict

The bit is one `botCom` fragment at the probe vertex, guarded by the
probe's flag; the verdict is two assignments and a test. Together with
§2–§4 and the landed engine, that is all six passes of design §6 (b). -/

/-- The bit's charge: the fragment, the environment slot and the
guard. -/
noncomputable def atomBitCost {L : ℕ} (β : DistFO L 1) : ℕ := RamDriverBot.botCost β + 6

/-- **The outside bit, walked — the found branch.** At a probe vertex
the guard accepted, the fragment leaves the atom's truth *in the child
arena*: the vertex is dead there, so the edgeless reading `botCom`
computes is the arena reading (`Refine.DeadRow.sat_bot_of_dead₁`). -/
theorem atomBitCom_spec_found {jd L : ℕ} {C' : ℕ → ℕ → ℕ} {β : DistFO L 1}
    {G : SimpleGraph (Fin n)} {Alv' : ℕ → ℕ} {zo : Fin n}
    (hB : 1 < B) (hnB : n < B) (hcbit : ∀ c < L, ∀ v < n, C' c v ≤ 1)
    (hloc : IsLocal β) (hdead : Alv' (zo : ℕ) = 0) :
    Spec B (fun σ => RamDriverBot.BotEnv n L jd C' σ ∧ BotMem B β "bb" σ ∧
        σ.vars "of" ≠ 0 ∧ σ.vars "of" < B ∧ σ.vars "oz" = (zo : ℕ))
      (atomBitCom jd β)
      (fun _ σ' => σ'.vars "bb" ≤ 1 ∧
        (σ'.vars "bb" ≠ 0 ↔ Sat (masked G Alv') (colRead n C' L) (fun _ => zo) β))
      (atomBitCost β) := by
  have hEbb : RamDriverBot.Ext "b" "bb" := RamDriverBot.ext_of_prefix (by decide)
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcol, hmem, hof, hofB, hoz⟩ := hσ
  have hcond : (Cond.lt (.lit 0) (.var "of")).evalB B σ = some (decide (0 < σ.vars "of")) :=
    evalB_condLt (evalB_lit (by omega)) (evalB_var hofB)
  have hoze : (Expr.var "oz").evalB B σ = some (zo : ℕ) := by
    have h := evalB_var (B := B) (x := "oz") (σ := σ) (by rw [hoz]; omega)
    rwa [hoz] at h
  set σ₁ := σ.setVar (envName 0) (zo : ℕ) with hσ₁
  have hr₁ : Run B (.assign (envName 0) (.var "oz")) σ σ₁ 2 :=
    (Run.assign hoze).mono (by simp [Expr.size])
  obtain ⟨σ₂, hr₂, hb1, hbiff⟩ :=
    (RamDriverBot.bot_spec (jd := jd) hB hnB hcbit β hloc "bb" hEbb (fun _ => zo)).run
      (σ := σ₁) ⟨fun c hc => by rw [hσ₁, arrs_setVar]; exact hcol c hc,
        fun i => by rw [show (i : ℕ) = 0 from by omega, hσ₁, vars_setVar, if_pos rfl],
        botMem_of_length (fun a => by rw [hσ₁, arrs_setVar]) β "bb" hmem⟩
  refine ⟨σ₂, _, Run.ite_true (by rw [hcond]; simp [Nat.pos_of_ne_zero hof]) (hr₁.seq hr₂),
    ?_, hb1, ?_⟩
  · rw [atomBitCost]
    simp only [Cond.size, Expr.size]
    omega
  · rw [hbiff, Refine.DeadRow.sat_bot_of_dead₁ hdead hloc]

/-- **The outside bit, walked — the empty branch.** The probe found
nothing; the bit is zeroed, and with it the whole outside term. -/
theorem atomBitCom_spec_empty {jd L : ℕ} {β : DistFO L 1} (hB : 1 < B)
    (hloc : IsLocal β) :
    Spec B (fun σ => σ.vars "of" = 0 ∧ σ.vars "of" < B) (atomBitCom jd β)
      (fun _ σ' => σ'.vars "bb" = 0) (atomBitCost β) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hof, hofB⟩ := hσ
  have hcond : (Cond.lt (.lit 0) (.var "of")).evalB B σ = some (decide (0 < σ.vars "of")) :=
    evalB_condLt (evalB_lit (by omega)) (evalB_var hofB)
  refine ⟨σ.setVar "bb" 0, _,
    Run.ite_false (by rw [hcond]; simp [hof]) (Run.assign (evalB_lit (show 0 < B by omega))),
    ?_, by rw [vars_setVar, if_pos rfl]⟩
  rw [atomBitCost]
  simp only [Cond.size, Expr.size]
  omega

/-- The verdict's charge. -/
def atomFlagCost : ℕ := 14

/-- **The verdict, walked.** The three registers are summed and tested
against the atom's threshold; `Refine.ScatterDeadPass.atomTerms_iff_scatVal`
is what the test is worth. -/
theorem atomFlagCom_spec {t cnt kc bb oc : ℕ} (hB : 1 < B) (htB : t < B)
    (hbbB : bb < B) (hocB : oc < B) (hsB : cnt + (kc + bb * oc) < B) :
    Spec B (fun σ => σ.vars "cnt" = cnt ∧ σ.vars "kc" = kc ∧ σ.vars "bb" = bb ∧
        σ.vars "oc" = oc)
      (atomFlagCom t)
      (fun _ σ' => σ'.vars "flag" ≤ 1 ∧ (σ'.vars "flag" ≠ 0 ↔ t ≤ cnt + (kc + bb * oc)))
      atomFlagCost := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcnt, hkc, hbb, hoc⟩ := hσ
  have hmul : (Expr.mul (.var "bb") (.var "oc")).evalB B σ = some (bb * oc) := by
    have h := evalB_bin (evalB_var (B := B) (x := "bb") (σ := σ) (by rw [hbb]; omega))
      (evalB_var (B := B) (x := "oc") (σ := σ) (by rw [hoc]; omega))
      (show Bop.mul.apply (σ.vars "bb") (σ.vars "oc") < B by
        rw [Bop.apply_mul, hbb, hoc]; omega)
    rw [Bop.apply_mul, hbb, hoc] at h
    exact h
  have hin : (Expr.add (.var "kc") (.mul (.var "bb") (.var "oc"))).evalB B σ =
      some (kc + bb * oc) := by
    have h := evalB_bin (evalB_var (B := B) (x := "kc") (σ := σ) (by rw [hkc]; omega)) hmul
      (show Bop.add.apply (σ.vars "kc") (bb * oc) < B by rw [Bop.apply_add, hkc]; omega)
    rw [Bop.apply_add, hkc] at h
    exact h
  have hsum : (Expr.add (.var "cnt") (.add (.var "kc") (.mul (.var "bb") (.var "oc")))).evalB
      B σ = some (cnt + (kc + bb * oc)) := by
    have h := evalB_bin (evalB_var (B := B) (x := "cnt") (σ := σ) (by rw [hcnt]; omega)) hin
      (show Bop.add.apply (σ.vars "cnt") (kc + bb * oc) < B by
        rw [Bop.apply_add, hcnt]; omega)
    rw [Bop.apply_add, hcnt] at h
    exact h
  set σ₁ := σ.setVar "os" (cnt + (kc + bb * oc)) with hσ₁
  have hr₁ : Run B (.assign "os" (.add (.var "cnt")
      (.add (.var "kc") (.mul (.var "bb") (.var "oc"))))) σ σ₁ 8 :=
    (Run.assign hsum).mono (by simp [Expr.size])
  have hos₁ : σ₁.vars "os" = cnt + (kc + bb * oc) := by rw [hσ₁, vars_setVar, if_pos rfl]
  have hcond : (Cond.lt (.var "os") (.lit t)).evalB B σ₁ =
      some (decide (cnt + (kc + bb * oc) < t)) := by
    have h := evalB_condLt (B := B) (σ := σ₁)
      (evalB_var (x := "os") (by rw [hos₁]; omega)) (evalB_lit htB)
    rwa [hos₁] at h
  by_cases hlt : cnt + (kc + bb * oc) < t
  · refine ⟨σ₁.setVar "flag" 0, _,
      hr₁.seq (Run.ite_true (by rw [hcond]; simp [hlt])
        (Run.assign (evalB_lit (show 0 < B by omega)))), ?_, ?_, ?_⟩
    · rw [atomFlagCost]; simp only [Cond.size, Expr.size]; omega
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_pos rfl]
      exact ⟨fun h => absurd rfl h, fun h => absurd h (by omega)⟩
  · refine ⟨σ₁.setVar "flag" 1, _,
      hr₁.seq (Run.ite_false (by rw [hcond]; simp [hlt])
        (Run.assign (evalB_lit (show (1 : ℕ) < B by omega)))), ?_, ?_, ?_⟩
    · rw [atomFlagCost]; simp only [Cond.size, Expr.size]; omega
    · rw [vars_setVar, if_pos rfl]
    · rw [vars_setVar, if_pos rfl]
      exact ⟨fun _ => by omega, fun _ => by omega⟩

/-! ### §5c The program's charge

The program itself is `RamDriver.scatDeadCom`, and since wave (c1) it is
what `RamDriver.clusterCom` runs. It is written *there* rather than here
because the driver has to name it, and (c1) removed the vestigial import
that used to force the block engine's text below the driver — see that
definition's own docstring. What stays here is its charge and its
walks. -/

/-- **The distance fill's charge**: the child's member count, and the
carrier occurs nowhere in it. `RamDriver.memFillAt`'s loop bound is
`mnumName (j + 1)` and its body pays one unit more per cell than
`RamDriver.fillCom`'s, for the indirect address — against which the
carrier is gone.

It is defined here, in the section that sums the program's slots,
because since wave B4-walk-2m-3 that is what it is: a slot of
`scatDeadK`. Its walk is §5f's `memFillAt_spec`, and §5f's `#guard`s
clock it on the executable semantics. -/
def memFillAtCost (mm1 : ℕ) : ℕ := 14 * mm1 + 6

/-- The program's charge, pass by pass. **Wave E4c-c: the mask copy's
`12·n + 6` is gone from the sum**, because the pass is gone from the
program — the engine reads the child's alive array where it lies.

**Wave B4-walk-2m-3: the distance fill's slot is `memFillAtCost mm1`**,
not `11·n + 6`. The program runs `RamDriver.distMemCom`, a walk of the
child's member list, so the slot is read at `mm1` like the filter walk
beside it. Exactly **one** carrier reading is left in the whole sum,
`outProbeCost n`, and that one is a pigeonhole *cap*: the narrowed form
`scatDeadKX` below replaces it by `outProbeCostB n xb`, after which no
summand grows with `n` (`scatDeadKX_le_blk`).

The trade is not free at every instantiation. At `mm1 = n` the new slot
is `14·n + 6` against the retired `11·n + 6` and the sum is *larger*;
`C0CloseProbe.deadAtomK_root_eq`'s `119·n` becomes `122·n`. What the
wave buys is the argument the coefficient is read at, not the
coefficient.

**Wave R1.8-T3-flip (c1b): the outside count's slot is corrected**, from
`2` to `outCntCost = 6`. It was the one summand with no proved leaf
under it, and `2` is unachievable — `outCntCom_spec` above is the leaf,
and the pass's expression has five nodes. -/
noncomputable def scatDeadK {L : ℕ} (β : DistFO L 1) (n mm1 kq mm bw nb t : ℕ) : ℕ :=
  killSumCost kq + outProbeCost n + atomBitCost β + outCntCost + atomMemCost mm1 +
    memFillAtCost mm1 + scatBlockK mm bw nb t + atomFlagCost

/-- **The same charge, read at the turn's cluster** (wave B4-walk-1).

Four of `scatDeadK`'s readings are the walk's to narrow and they narrow
to the *same* number: the outside probe's loop bound (`outProbeCostB`,
built and unwired by E4c-a), the child's member count `mm1` — which the
filter walk **and, since wave B4-walk-2m-3, the distance fill** are both
read at — and the atom's own member count `mm`. All are bounded by the
cluster the turn descends into, because the child mask marks only
cluster vertices and the probe stops one step past the last of them. The
ball's two numbers stay the parameters they already were, so a caller
that narrows them narrows this charge with no further edit.

**Nothing here grows with the carrier.** `n` survives in exactly one
place, `outProbeCostB n xb = 20·min (xb + 1) n + 10`, and there it is a
*cap*: the charge is weakly increasing in `n`, constant once `n` passes
`xb + 1`, and dominated for every `n` by `scatDeadKBlk`, which does not
mention `n` at all. That is the whole content of the E4c line and it is
compiled below (`scatDeadKX_le_blk`, `scatDeadKX_carrier_free`), against
the negative control `scatDeadKXwhole` — this same charge at the retired
whole-array fill — which is unbounded in `n` at every fixed block
reading (`scatDeadKXwhole_unbounded`).

`scatDeadKX_carrier` is the identity at `xb := n` — the landed charge at
its own carrier instantiation, on the nose — so the hypothesis the walk
now takes is *weaker* than the one it took (`scatDeadKX_le_carrier`) and
no consumer owes anything new. -/
noncomputable def scatDeadKX {L : ℕ} (β : DistFO L 1) (n xb kq bw nb t : ℕ) : ℕ :=
  killSumCost kq + outProbeCostB n xb + atomBitCost β + outCntCost + atomMemCost xb +
    memFillAtCost xb + scatBlockK xb bw nb t + atomFlagCost

/-- **At the carrier reading the narrowed charge IS the landed one.** -/
theorem scatDeadKX_carrier {L : ℕ} (β : DistFO L 1) (n kq bw nb t : ℕ) :
    scatDeadKX β n n kq bw nb t = scatDeadK β n n kq n bw nb t := by
  simp only [scatDeadKX, scatDeadK, outProbeCostB_carrier]

/-- Monotone in the cluster reading and in the ball's two numbers. -/
theorem scatDeadKX_mono {L : ℕ} (β : DistFO L 1) {n xb xb' kq bw bw' nb nb' t : ℕ}
    (hx : xb ≤ xb') (hb : bw ≤ bw') (hn : nb ≤ nb') :
    scatDeadKX β n xb kq bw nb t ≤ scatDeadKX β n xb' kq bw' nb' t := by
  have h₁ : outProbeCostB n xb ≤ outProbeCostB n xb' := outProbeCostB_mono hx
  have h₂ : atomMemCost xb ≤ atomMemCost xb' := by simp only [atomMemCost]; omega
  have h₃ : scatBlockK xb bw nb t ≤ scatBlockK xb' bw' nb' t :=
    ScatterBlock.scatBlockK_mono hx hb hn le_rfl
  have h₄ : memFillAtCost xb ≤ memFillAtCost xb' := by simp only [memFillAtCost]; omega
  simp only [scatDeadKX]
  omega

/-- **THE WEAKENING, compiled.** A cluster reading under the carrier, at
a ball budget under the carrier's, charges no more than the landed
carrier instantiation — so every caller holding the landed bound holds
the narrowed one, and narrowing the walk asks nothing new of anybody. -/
theorem scatDeadKX_le_carrier {L : ℕ} (β : DistFO L 1) {n xb kq bw bw' nb nb' t : ℕ}
    (hx : xb ≤ n) (hb : bw ≤ bw') (hn : nb ≤ nb') :
    scatDeadKX β n xb kq bw nb t ≤ scatDeadK β n n kq n bw' nb' t :=
  le_trans (scatDeadKX_mono β hx hb hn) (le_of_eq (scatDeadKX_carrier β n kq bw' nb' t))

/-! ### §5c′ Block scale, compiled — what the whole E4c line was for

The claim the line has been making since E4c-a is that the per-atom
charge is read at the block the turn descends into and not at the
carrier. Wave B4-walk-1 narrowed the last three accounting readings;
wave B4-walk-2m-3 removed the last *program* reading. This section is
the statement that the claim is now true, and it is the wave's
acceptance test.

`outProbeCostB n xb = 20·min (xb + 1) n + 10` legitimately still names
`n`, so "the carrier does not occur" is false and "the charge does not
*grow* with the carrier" is what is true. Two theorems say it, and both
are needed:

* `scatDeadKX_le_blk` — for **every** `n`, the charge is at most
  `scatDeadKBlk`, a function of `xb`, `kq`, the ball and `t` alone. This
  is the block-scale bound. On its own it would still permit growth
  under the ceiling.
* `scatDeadKX_carrier_free` — above `xb + 1` the charge does not merely
  stay under the ceiling, it **is** the ceiling and stops moving:
  any two carriers past the block agree on the nose. On its own it would
  say nothing below `xb + 1`.

`scatDeadKX_mono_carrier` fills the gap between them: the charge is
weakly increasing in `n`, so the two together pin it completely.

The negative control is `scatDeadKXwhole`, the *same* narrowed charge at
the retired whole-array fill `11·n + 6`. `scatDeadKXwhole_trade` compiles
that it differs from `scatDeadKX` in that slot and nowhere else, and
`scatDeadKXwhole_unbounded` that it exceeds every constant at a fixed
block reading — which is exactly what `scatDeadKX_le_blk` denies of the
charge the program now pays. -/

/-- **The charge at the block reading alone**: `scatDeadKX` with the
outside probe's cap taken at its own block bound `xb + 1`. The carrier
does not occur. -/
noncomputable def scatDeadKBlk {L : ℕ} (β : DistFO L 1) (xb kq bw nb t : ℕ) : ℕ :=
  killSumCost kq + (20 * (xb + 1) + 10) + atomBitCost β + outCntCost + atomMemCost xb +
    memFillAtCost xb + scatBlockK xb bw nb t + atomFlagCost

/-- **THE ACCEPTANCE TEST, half one: the narrowed charge is bounded by a
function of the block reading alone**, at every carrier. -/
theorem scatDeadKX_le_blk {L : ℕ} (β : DistFO L 1) (n xb kq bw nb t : ℕ) :
    scatDeadKX β n xb kq bw nb t ≤ scatDeadKBlk β xb kq bw nb t := by
  have h : outProbeCostB n xb ≤ 20 * (xb + 1) + 10 := by
    simp only [outProbeCostB]; omega
  simp only [scatDeadKX, scatDeadKBlk]
  omega

/-- **…half two: past the block the carrier stops moving the charge.**
At any carrier the block's own scan bound fits into, the charge *is*
the block-scale bound, so two such carriers agree on the nose. -/
theorem scatDeadKX_carrier_free {L : ℕ} (β : DistFO L 1) {n xb : ℕ} (kq bw nb t : ℕ)
    (hn : xb + 1 ≤ n) :
    scatDeadKX β n xb kq bw nb t = scatDeadKBlk β xb kq bw nb t := by
  have h : outProbeCostB n xb = 20 * (xb + 1) + 10 := by
    simp only [outProbeCostB, Nat.min_eq_left hn]
  simp only [scatDeadKX, scatDeadKBlk, h]

/-- The two carriers, stated as the invariance it is. -/
theorem scatDeadKX_carrier_indep {L : ℕ} (β : DistFO L 1) {n n' xb : ℕ} (kq bw nb t : ℕ)
    (hn : xb + 1 ≤ n) (hn' : xb + 1 ≤ n') :
    scatDeadKX β n xb kq bw nb t = scatDeadKX β n' xb kq bw nb t := by
  rw [scatDeadKX_carrier_free β kq bw nb t hn, scatDeadKX_carrier_free β kq bw nb t hn']

/-- And weakly increasing in the carrier below that, which is what makes
the two halves above a complete description. -/
theorem scatDeadKX_mono_carrier {L : ℕ} (β : DistFO L 1) {n n' : ℕ} (xb kq bw nb t : ℕ)
    (h : n ≤ n') : scatDeadKX β n xb kq bw nb t ≤ scatDeadKX β n' xb kq bw nb t := by
  have hp : outProbeCostB n xb ≤ outProbeCostB n' xb := by
    simp only [outProbeCostB]; omega
  simp only [scatDeadKX]
  omega

/-- **The sharper claim is FALSE, and this is why the theorems above take
the hypothesis they take.** "The narrowed charge does not mention the
carrier" would be `scatDeadKX_carrier_indep` without `xb + 1 ≤ n`, and
it fails: at `xb = 1` the probe's cap reads `min 2 0 = 0` at the empty
carrier and `min 2 2 = 2` at `n = 2`, a difference of `40`. So the
honest statement of the wave is that nothing *grows* with the carrier
(`scatDeadKX_le_blk`) and that the carrier stops mattering past the
block (`scatDeadKX_carrier_free`) — not that it is absent. -/
theorem scatDeadKX_carrier_indep_refuted {L : ℕ} (β : DistFO L 1) :
    ¬ (∀ (n n' xb kq bw nb t : ℕ),
        scatDeadKX β n xb kq bw nb t = scatDeadKX β n' xb kq bw nb t) := by
  intro h
  have := h 0 2 1 0 0 0 0
  simp only [scatDeadKX, outProbeCostB, killSumCost, atomMemCost, outCntCost,
    memFillAtCost, atomFlagCost, ScatterBlock.scatBlockK_eq] at this
  omega

/-- **The negative control**: the narrowed charge at the *retired*
whole-array fill. Every other slot is the one `scatDeadKX` pays. -/
noncomputable def scatDeadKXwhole {L : ℕ} (β : DistFO L 1) (n xb kq bw nb t : ℕ) : ℕ :=
  killSumCost kq + outProbeCostB n xb + atomBitCost β + outCntCost + atomMemCost xb +
    (11 * n + 6) + scatBlockK xb bw nb t + atomFlagCost

/-- The control differs from the charge in the fill's slot and nowhere
else — so what the theorems below separate is the fill, not a bookkeeping
difference. -/
theorem scatDeadKXwhole_trade {L : ℕ} (β : DistFO L 1) (n xb kq bw nb t : ℕ) :
    scatDeadKXwhole β n xb kq bw nb t + memFillAtCost xb
      = scatDeadKX β n xb kq bw nb t + (11 * n + 6) := by
  simp only [scatDeadKXwhole, scatDeadKX, memFillAtCost]
  omega

/-- **The control grows with the carrier where the charge does not.** At
a block reading, a kill count, a ball budget and a pick count all fixed
before the arena, the retired fill's charge exceeds every constant. The
contrast with `scatDeadKX_le_blk` is the wave. -/
theorem scatDeadKXwhole_unbounded {L : ℕ} (β : DistFO L 1) (xb kq bw nb t K : ℕ) :
    ∃ n : ℕ, ¬ (scatDeadKXwhole β n xb kq bw nb t ≤ K) := by
  refine ⟨K + 1, fun h => ?_⟩
  simp only [scatDeadKXwhole] at h
  omega

/-- And no carrier-free bound exists for it at all, which is the same
fact stated as the failure of `scatDeadKX_le_blk`'s conclusion. -/
theorem scatDeadKXwhole_no_blk {L : ℕ} (β : DistFO L 1) (xb kq bw nb t : ℕ)
    (f : ℕ → ℕ) : ∃ n : ℕ, ¬ (scatDeadKXwhole β n xb kq bw nb t ≤ f xb) :=
  scatDeadKXwhole_unbounded β xb kq bw nb t (f xb)

/-! ### §5d The seam between the terms and the engine

The one thing the order of §5c has to buy is that the engine leaves the
three dead registers alone — it runs last, so nothing of the depth's own
arrays crosses it, but `"kc"`, `"bb"` and `"oc"` do. Both facts are one
`simp` off concrete program text (the block search's `d` occurs only in
literals, so nothing recurses). -/

/-- **The engine writes four arrays**, and none of them is a name the
driver or the atom program holds: not the child's member list, not a
table row, not the kill list, not a mask, not a colour array. -/
theorem warrs_scatBlockCom (r t : ℕ) {a : String} (ha : a ∈ (scatBlockCom r t).warrs) :
    a = "exc" ∨ a = "dist" ∨ a = "q" ∨ a = "qd" := by
  simp only [scatBlockCom, ScatterBlock.clearMem, ScatterBlock.clearSlot,
    ScatterBlock.scatBlockLoop, ScatterBlock.scatBlockStep, ScatterBlock.scatBlockBody,
    ScatterBlock.pickBlock, ScatterBlock.markBall, ScatterBlock.markSlot,
    BfsBlock.bfsBlockCom, BfsBlock.unwind, BfsBlock.unwindSlot, seedSrc,
    bfsDrain, expandRow, scanSlot, Fill.put, Csr.loadRow,
    Csr.scan, Queue.drain, Com.warrs, List.mem_append, List.mem_singleton, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  tauto

/-- **And the three dead registers survive it.** The kill sum, the
outside bit and the outside count are computed before the engine and
read after it; this is what says the order of `scatDeadCom` is
sound. -/
theorem notMem_wvars_scatBlockCom (r t : ℕ) (y : String)
    (hy : y ∈ ["kc", "bb", "oc", "n", "mm"]) : y ∉ (scatBlockCom r t).wvars := by
  fin_cases hy <;>
    simp [scatBlockCom, ScatterBlock.clearMem, ScatterBlock.clearSlot,
      ScatterBlock.scatBlockLoop, ScatterBlock.scatBlockStep, ScatterBlock.scatBlockBody,
      ScatterBlock.pickBlock, ScatterBlock.markBall, ScatterBlock.markSlot,
      BfsBlock.bfsBlockCom, BfsBlock.unwind, BfsBlock.unwindSlot, seedSrc,
      bfsDrain, expandRow, scanSlot, Fill.put, Csr.loadRow,
      Csr.scan, Queue.drain, Com.wvars]

/-! #### The same two facts at the named mask (wave E4c-c)

`RamDriver.scatDeadCom` runs `ScatterBlock.scatBlockComA`, the engine
under an array renaming, so the two seam facts have to be read there.
Neither is re-proved: scalars are untouched by an array renaming
(`ScatterBlock.renCom_wvars`), and the write set is the landed one
pushed through the swap, which fixes all four written names precisely
because `MaskFree` says the mask is none of them. -/

/-- **A per-depth mask array is free for the engine to read in place.**
`alvName a` begins `alv…`, and none of the seven names the pass holds
does. -/
theorem maskFree_alvName (a : ℕ) : ScatterBlock.MaskFree (alvName a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [alvName, String.ext_iff]

/-- **The renamed engine still writes exactly four arrays**, and the
mask is none of them — which is what makes reading it in place sound. -/
theorem warrs_scatBlockComA {av : String} (hav : ScatterBlock.MaskFree av) (r t : ℕ)
    {a : String} (ha : a ∈ (ScatterBlock.scatBlockComA av r t).warrs) :
    a = "exc" ∨ a = "dist" ∨ a = "q" ∨ a = "qd" := by
  obtain ⟨-, -, -, hd, hq, hqd, he⟩ := hav
  have hpull : ScatterBlock.maskSwap av a ∈ (scatBlockCom r t).warrs :=
    ScatterBlock.mem_warrs_scatBlockComA ha
  have hback : a = ScatterBlock.maskSwap av (ScatterBlock.maskSwap av a) :=
    (ScatterBlock.maskSwap_invol av a).symm
  rcases warrs_scatBlockCom r t hpull with h | h | h | h <;> rw [hback, h]
  · exact Or.inl (ScatterBlock.maskSwap_of_ne (by decide) (Ne.symm he))
  · exact Or.inr (Or.inl (ScatterBlock.maskSwap_of_ne (by decide) (Ne.symm hd)))
  · exact Or.inr (Or.inr (Or.inl (ScatterBlock.maskSwap_of_ne (by decide) (Ne.symm hq))))
  · exact Or.inr (Or.inr (Or.inr (ScatterBlock.maskSwap_of_ne (by decide) (Ne.symm hqd))))

/-- And the three dead registers survive the renamed engine too. -/
theorem notMem_wvars_scatBlockComA (av : String) (r t : ℕ) (y : String)
    (hy : y ∈ ["kc", "bb", "oc", "n", "mm"]) :
    y ∉ (ScatterBlock.scatBlockComA av r t).wvars := by
  rw [ScatterBlock.wvars_scatBlockComA]
  exact notMem_wvars_scatBlockCom r t y hy

/-- **The other eight passes' write sets** (wave R1.8-T3-flip (c1c)).
The engine's two facts above say what crosses *it*; the composition of
`RamDriver.scatDeadCom` needs the same reading of every other pass, and
the eight below are that reading, off concrete program text.

Together they are exactly the non-interference the program order claims:
the kill sum leaves `"kc"` and nothing else, the probe leaves `"of"`,
`"oz"`, `"oi"`, the bit leaves an `Ext "bb"` array and the environment
slots, the count leaves `"oc"`, the filter leaves `"mem"`/`"mm"`, the two
calling-convention passes leave `"alv"`/`"dist"` and the loop counter,
and the verdict leaves `"flag"`. No product of an earlier pass is a
write of a later one, which is why the four registers the verdict reads
all survive to it. -/
theorem warrs_killSumCom (j ti : ℕ) : (killSumCom j ti).warrs = [] := by
  simp [killSumCom, Com.warrs]

theorem notMem_wvars_killSumCom (j ti : ℕ) {y : String} (h₁ : y ≠ "kc") (h₂ : y ≠ "ke") :
    y ∉ (killSumCom j ti).wvars := by simp [killSumCom, Com.wvars, h₁, h₂]

theorem warrs_outProbeCom (j : ℕ) : (outProbeCom j).warrs = [] := by
  simp [outProbeCom, Com.warrs]

theorem notMem_wvars_outProbeCom (j : ℕ) {y : String} (h₁ : y ≠ "of") (h₂ : y ≠ "oz")
    (h₃ : y ≠ "oi") : y ∉ (outProbeCom j).wvars := by
  simp [outProbeCom, Com.wvars, h₁, h₂, h₃]

theorem warrs_outCntCom (j : ℕ) : (outCntCom j).warrs = [] := by simp [outCntCom, Com.warrs]

theorem notMem_wvars_outCntCom (j : ℕ) {y : String} (h : y ≠ "oc") :
    y ∉ (outCntCom j).wvars := by simp [outCntCom, Com.wvars, h]

theorem warrs_atomMemCom (j ti : ℕ) : (atomMemCom j ti).warrs = ["mem"] := by
  simp [atomMemCom, Com.warrs]

theorem notMem_wvars_atomMemCom (j ti : ℕ) {y : String} (h₁ : y ≠ "mm") (h₂ : y ≠ "ak")
    (h₃ : y ≠ "av") : y ∉ (atomMemCom j ti).wvars := by
  simp [atomMemCom, Com.wvars, h₁, h₂, h₃]

theorem warrs_atomFlagCom (t : ℕ) : (atomFlagCom t).warrs = [] := by
  simp [atomFlagCom, Com.warrs]

theorem notMem_wvars_atomFlagCom (t : ℕ) {y : String} (h₁ : y ≠ "os") (h₂ : y ≠ "flag") :
    y ∉ (atomFlagCom t).wvars := by simp [atomFlagCom, Com.wvars, h₁, h₂]

theorem warrs_copyCom (src dst : String) : (copyCom src dst).warrs = [dst] := by
  simp [copyCom, copyUpto, fillUpto, Com.warrs]

theorem notMem_wvars_copyCom (src dst : String) {y : String} (h : y ≠ "i") :
    y ∉ (copyCom src dst).wvars := by simp [copyCom, copyUpto, fillUpto, Com.wvars, h]

theorem warrs_fillCom (a : String) (e : Expr) : (fillCom a e).warrs = [a] := by
  simp [fillCom, fillUpto, Com.warrs]

theorem notMem_wvars_fillCom (a : String) (e : Expr) {y : String} (h : y ≠ "i") :
    y ∉ (fillCom a e).wvars := by simp [fillCom, fillUpto, Com.wvars, h]

open Classical in
/-- **The bit writes only below `"bb"`.** The fragment is the generated
evaluator's, so `RamDriverBot.warrs_botCom` settles it; the empty branch
writes no array at all. -/
theorem warrs_atomBitCom {jd L : ℕ} (β : DistFO L 1) (hloc : IsLocal β) {a : String}
    (ha : a ∈ (atomBitCom jd β).warrs) : RamDriverBot.Ext "bb" a := by
  rw [atomBitCom, Com.warrs, Com.warrs, Com.warrs, Com.warrs] at ha
  simp only [List.append_nil, List.nil_append] at ha
  exact RamDriverBot.warrs_botCom β hloc "bb" a ha

open Classical in
/-- **And it assigns only below `"bb"` and the environment slots.** The
guard's `"of"` and the probe's `"oz"` are read, not written; `"bb"`
itself is `Ext "bb"`, so the two branches fall into the same clause. -/
theorem wvars_atomBitCom {jd L : ℕ} (β : DistFO L 1) (hloc : IsLocal β) {y : String}
    (hy : y ∈ (atomBitCom jd β).wvars) :
    RamDriverBot.Ext "bb" y ∨ ∃ i, y = envName i := by
  rw [atomBitCom, Com.wvars, Com.wvars, Com.wvars, Com.wvars] at hy
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with (h | h) | h
  · exact Or.inr ⟨0, h⟩
  · rcases RamDriverBot.wvars_botCom β hloc "bb" y h with h' | ⟨i, -, h'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨i, h'⟩
  · exact Or.inl (by rw [h]; exact List.prefix_rfl)

/-! ### §5d′ The engine's budget, at the carrier

`Refine.ScatterBlock.scatBlock_specW` charges its scan at a *ball
budget*: a slot weight `bw` and a size `nb` that every ball of the arena
respects. The driver has no per-ball reading yet — that is E4c — so what
this wave supplies is the trivial witness, the whole carrier: the arena's
slot array is `ns` cells long and it has `n` vertices, and both numbers
come out of `RamBfs.CsrGraph` alone.

Two things make this the right shape to land now. The witness `A` does
not mention the mask, so **one** lemma serves every depth's `Alv'` — and
`Alv'` is existential inside `RamDriverCluster.clusterStepImplements`,
so a mask-specific budget could not be threaded in at all. And `bw`/`nb`
stay *parameters* of `RamDriverCluster.ScatterStep`, so narrowing them
later moves this discharge and nothing else. -/

/-- **Every ball fits in the carrier.** The witness is
`Finset.range n`; its slot weight telescopes to `O n − O 0 = ns`
(`RamBfs.CsrGraph.zero`, `.mono`, `.last`) and its size is `n`. -/
theorem ballBudget_carrier {G : SimpleGraph (Fin n)} {ns : ℕ} {O T : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) (M : ℕ → ℕ) (r : ℕ) : BallBudget n r G M O ns n := by
  have htel : ∀ m, m ≤ n → (∑ v ∈ Finset.range m, Csr.rowLen O v) = O m - O 0 := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
        have hmn : m < n := by omega
        rw [Finset.sum_range_succ, ih (by omega), Csr.rowLen]
        have h₀ : O 0 ≤ O m := hcsr.mono' (Nat.zero_le m) (by omega)
        have h₁ : O m ≤ O (m + 1) := hcsr.mono m hmn
        omega
  intro s _
  refine ⟨Finset.range n, fun v hv _ _ => Finset.mem_range.2 hv, ?_, by simp⟩
  rw [htel n le_rfl, hcsr.zero, hcsr.last]
  omega

/-! ### §5f Wave E4c-b: the two calling-convention copies, at the member
list — and what became of each

E4c-b built touched-only replacements for both carrier passes of
`RamDriver.scatDeadCom` and compiled that *at the contracts of the day*
neither could be wired in. The two halves then went opposite ways.

**The mask half was deleted, not replaced.** E4c-c took the other route:
not a cheaper copy but no copy at all. `RamDriver.scatDeadCom` no longer
contains `copyCom (alvName (j + 1)) "alv"`; the engine is
`Refine.ScatterBlock.scatBlockComA (alvName (j + 1))`, which reads the
child's alive array where it lies. So `memCopyAt`, `alvMemCom`,
`alvClrCom` and `entryMemCost` below are **superseded**, and they are
kept for one reason: the refutations of §5g are stated about them, and
those refutations are the evidence for why the copy had to be deleted
rather than re-charged. Deleting the definitions would delete the
record.

**The distance half was wired in** — wave B4-walk-2m-3.
`RamDriver.scatDeadCom` runs `RamDriver.distMemCom j r`, and
`memFillAt_spec` below is its walk in the driver's own composite
(`Refine.ScatterDeadTurn.scatDead_spec`, pass 6). What unblocked it was
not this section but the engine's contract: blocker 2 was the
*whole-array* seventh clause of `Refine.ScatterBlock.ArenaAt`, and waves
B4-walk-2m-1/2 re-walked the engine at
`Refine.ScatterBlockMask.ArenaAtM`, whose clause is
`Refine.ScatterBlock.DistClean n r M` — the sentinel at the mask's
support. `Refine.ScatterBlockMask.distClean_of_cover` is the one line
from this section's postcondition to that clause, and its `hcov`
hypothesis is `MemEnum`'s fourth clause verbatim. The two program
definitions moved to `RamDriver` for the import order; everything else
about the fill is still here.

Historically: `Refine.C0CloseProbe.scatDeadK_narrow_floor` compiled that
`23·n + 12` of §5c's charge survived every narrowing of the probe bound,
the two member counts and the ball budget — the mask copy `copyCom
(alvName (j + 1)) "alv"` and the distance fill `fillCom "dist" (r + 1)`
are carrier walks in `RamDriver.scatDeadCom`'s own text, so only a
program change could move them. This section is that program change,
built and measured, together with the two compiled reasons neither half
could be wired in *at the contracts of the day*. Both have since been:
the mask copy by deletion (E4c-c), the distance fill by the narrowed
arena (B4-walk-2m-3). The carrier residual of §5c's charge is now `0`,
and `scatDeadKX_le_blk` is that in one line.

**The replacement.** `memFillAt` and `memCopyAt` walk the child's member
list once and store at the *listed* vertex: `Refine.BlockLeaves`'s
touched-only template (`blockLoad0` at `15·m₁ + 15·m + 30`), at the one
list the atom already holds. Their charges are `memFillAtCost mm1 =
14·mm1 + 6` and `memCopyAtCost mm1 = 15·mm1 + 6` against the landed
`11·n + 6` and `12·n + 6`: one unit more per cell — the address is
indirect — and the carrier gone. §5f's `#guard`s clock both on the
executable semantics at two carrier widths and at zero members, with the
landed passes at the same slot as the growing negative control.

**What each leaves.** `memFillAt_spec` and `memCopyAt_spec` state the
touched-only law directly: the listed cells hold the new value, and
*every other cell holds what it held*. Read at the three uses:

* `alvMemCom_spec` — from an `"alv"` that is **zero off the child's
  alive set**, the mask copy leaves `σ'.arrs "alv" = arrOf n Alv'`,
  which is `Refine.ScatterBlock.ArenaA`'s mask clause verbatim, at
  `15·mm1 + 6`;
* `alvClrCom_spec` — and the clear puts it back, so the pair is a round
  trip and the discipline is self-maintaining *inside* the atom phase;
* `distMemCom_spec` — the fill leaves `r + 1` at every listed vertex,
  which is where the block search reads and writes (`BfsBlock`'s two
  guarded slots) — but **not** `ArenaA`'s clause, which is the whole
  array.

**Blocker 1, the mask: nothing pins the scratch.** `"alv"` is a
`RamDriverFrames.scratchArrs` entry: `RamDriver.LevelMem` gives its
*length* and nothing else, and `ScatPre.run`/`ScatterDeadTurn.DeadPre.run`
are stated so that any pass may scribble on it. At the atom's entry the
array holds whatever the turn's descent (`RamDriver.descendCom` copies
`gamName a` into it), the level's cover phase (`coverPhase` copies the
mask in and `RamCover.coverCom` destroys it) and the nested driver last
left there. So the touched-only copy's precondition — zero off the alive
set — is not derivable, and `alv_touched_only_needs_clean_scratch`
compiles the consequence on data: run from a dirty `"alv"`, the pass
leaves a mask that is *not* `Alv'`, and the difference is at a vertex the
block search walks through. The junk is not an accounting artefact, and
`mask_junk_flips_the_engine` is that on data: at one arena, one member
list, one radius and one threshold, moving only the mask cells the
child's alive set does **not** name moves the engine's own flag from `1`
to `0` — `BfsBlock`'s two mask reads are the search frontier's
eligibility test, so a junk-alive cell enlarges the ball and swallows a
pick. Making this precondition available is the driver-wide
clean-scratch discipline (the cover and order phases active-set-driven,
R1.6), not the atom's.

**Blocker 2, the distance: the clause was uniform and the radius moves
— and the clause is what gave way.** `ArenaA`'s seventh clause is
`σ.arrs "dist" = arrOf n (fun _ => r + 1)` — the *whole* array at the
atom's **own** radius. Consecutive atoms of a turn carry different radii
(`σs.r` is a field of each `ScatterSentence`), and the engine hands the
array back at its own sentinel, so every cell that the next atom does
not list is stale by exactly one radius step. No discipline on the
caller repairs that: `dist_touched_only_refuted` below compiles that the
member-scale fill leaves `ArenaA`'s clause false however clean the
incoming array was, and it is kept as the record of the reading that was
replaced.

E4c-b's reading of what that cost — "the clause would have to be
narrowed to the mask's support first, which is the engine's file and not
a one-line narrowing" — was right about the price and wrong about the
verdict. `BfsBlock.unwind_run` did prove the array comes back as the
same literal list by an `arrOf_congr` over every `i < n`, and
`RamBfs.Frontier`'s `cap`/`sound` clauses are consumed at dead vertices
in `frontier_seed_alive`/`frontier_seed_dead`; waves B4-walk-2m-1/2 paid
that price in `Refine.BfsBlockMask` and `Refine.ScatterBlockMask`,
re-walking engine and pass at `DistClean n r M`. Against **that** clause
the unlisted cells are dead and unconstrained, `distMemCom_spec`'s
postcondition suffices, and B4-walk-2m-3 wired the fill in.

So the mask half of this section stands as a refutation and the distance
half as a replacement that landed two waves later. `Refine.C0CloseProbe`
§4's constants moved with it. -/

section MemberScaleEntry

/-! The fill's own text is `RamDriver.memFillAt`, and `distMemCom` with
it. Wave B4-walk-2m-3 moved the two definitions there — nothing else —
because `RamDriver.scatDeadCom` runs them and this file is below the
driver; the section note at `RamDriver`'s plumbing records the move and
`scatDeadCom`'s docstring the precedent. Everything about them is still
here: the charge, the invariant, the walk, the write sets. -/

/-- The touched-only copy: the same walk as `RamDriver.memFillAt`,
reading the source at the listed vertex. -/
def memCopyAt (j : ℕ) (src a : String) : Com :=
  .seq (.assign "ac" (.lit 0))
    (.while (.lt (.var "ac") (.var (mnumName (j + 1))))
      (.seq (.assign "ax" (.get (memName (j + 1)) (.var "ac")))
        (.seq (.store a (.var "ax") (.get src (.var "ax")))
          (.assign "ac" (.add (.var "ac") (.lit 1))))))

/-- **The mask copy, touched-only**: the replacement for
`RamDriver.copyCom (alvName (j + 1)) "alv"`. -/
def alvMemCom (j : ℕ) : Com := memCopyAt j (alvName (j + 1)) "alv"

/-- **And its restore**: the same walk putting the scratch back to zero,
so that the pair leaves `"alv"` exactly as it found it. -/
def alvClrCom (j : ℕ) : Com := memFillAt j "alv" 0

/-- The copy's charge: one unit more per member than the fill's, for the
indirect read. -/
def memCopyAtCost (mm1 : ℕ) : ℕ := 15 * mm1 + 6

/-- The two together, as the atom would pay them: the mask set, the mask
restore and the distance fill, against the landed `23·n + 12`. -/
def entryMemCost (mm1 : ℕ) : ℕ := memCopyAtCost mm1 + memFillAtCost mm1 + memFillAtCost mm1

theorem entryMemCost_eq (mm1 : ℕ) : entryMemCost mm1 = 43 * mm1 + 18 := by
  simp only [entryMemCost, memCopyAtCost, memFillAtCost]; omega

/-! #### The write sets -/

theorem warrs_memFillAt (j : ℕ) (a : String) (c : ℕ) : (memFillAt j a c).warrs = [a] := by
  simp [memFillAt, Com.warrs]

theorem notMem_wvars_memFillAt (j : ℕ) (a : String) (c : ℕ) {y : String}
    (h₁ : y ≠ "ac") (h₂ : y ≠ "ax") : y ∉ (memFillAt j a c).wvars := by
  simp [memFillAt, Com.wvars, h₁, h₂]

theorem warrs_memCopyAt (j : ℕ) (src a : String) : (memCopyAt j src a).warrs = [a] := by
  simp [memCopyAt, Com.warrs]

theorem notMem_wvars_memCopyAt (j : ℕ) (src a : String) {y : String}
    (h₁ : y ≠ "ac") (h₂ : y ≠ "ax") : y ∉ (memCopyAt j src a).wvars := by
  simp [memCopyAt, Com.wvars, h₁, h₂]

theorem ac_ne_mnumName (j : ℕ) : ("ac" : String) ≠ mnumName (j + 1) := by
  simp [mnumName, String.ext_iff]

theorem ax_ne_mnumName (j : ℕ) : ("ax" : String) ≠ mnumName (j + 1) := by
  simp [mnumName, String.ext_iff]

/-- **The member fill leaves the tape alone** — the clause
`RamDriver.scatDeadCom`'s own `NoWrite` needs at the fill's slot since
wave B4-walk-2m-3. -/
theorem noWrite_memFillAt (j : ℕ) (a : String) (c : ℕ) : (memFillAt j a c).NoWrite := by
  simp [memFillAt, Com.NoWrite]

/-! #### The walks

The invariant is the touched-only law at the read pointer: the members
already read hold the new value, and every cell the read prefix does not
name still holds what it held when the pass started. -/

/-- What the touched-only fill carries. -/
def MemFillInv (n j mm1 : ℕ) (a : String) (c : ℕ) (Mem1 g₀ : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars (mnumName (j + 1)) = mm1 ∧ σ.vars "ac" ≤ mm1 ∧
    σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧
    ∃ g, σ.arrs a = arrOf n g ∧
      (∀ p, p < σ.vars "ac" → g (Mem1 p) = c) ∧
      (∀ v, v < n → (∀ p, p < σ.vars "ac" → Mem1 p ≠ v) → g v = g₀ v)

/-- **The touched-only fill, walked.** The listed cells hold `c`; every
other cell is untouched. The charge is the child's member count and the
carrier occurs nowhere in it. -/
theorem memFillAt_spec {j mm1 c : ℕ} {a : String} {Mem1 g₀ A : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hcB : c < B)
    (hane : a ≠ memName (j + 1)) (hMenum : MemEnum n mm1 Mem1 A) :
    Spec B (fun σ => σ.vars (mnumName (j + 1)) = mm1 ∧
        σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧ σ.arrs a = arrOf n g₀)
      (memFillAt j a c)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf n g ∧
          (∀ p, p < mm1 → g (Mem1 p) = c) ∧
          (∀ v, v < n → (∀ p, p < mm1 → Mem1 p ≠ v) → g v = g₀ v)) ∧
        σ'.vars (mnumName (j + 1)) = mm1 ∧
        σ'.arrs (memName (j + 1)) = arrOf n Mem1)
      (memFillAtCost mm1) := by
  obtain ⟨hMlt, -, -, -⟩ := id hMenum
  have hm1n : mm1 ≤ n := hMenum.card_le
  have hm1B : mm1 < B := by omega
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hmm1, hmem1, harr⟩ := hσ
  set σ₁ := σ.setVar "ac" 0 with hσ₁
  have hr₁ : Run B (.assign "ac" (.lit 0)) σ σ₁ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  -- one member of the list
  have hstep : ∀ ρ : Env, MemFillInv n j mm1 a c Mem1 g₀ ρ → ρ.vars "ac" < mm1 →
      ∃ ρ' K', Run B (.seq (.assign "ax" (.get (memName (j + 1)) (.var "ac")))
          (.seq (.store a (.var "ax") (.lit c))
            (.assign "ac" (.add (.var "ac") (.lit 1))))) ρ ρ' K' ∧
        MemFillInv n j mm1 a c Mem1 g₀ ρ' ∧ ρ'.vars "ac" = ρ.vars "ac" + 1 ∧ K' ≤ 10 := by
    intro ρ hρ hlt
    obtain ⟨hmm1ρ, hacρ, hmem1ρ, g, hgarr, hset, hkeep⟩ := hρ
    set ac := ρ.vars "ac" with hac
    have hvn : Mem1 ac < n := hMlt ac hlt
    have hacn : ac < n := by omega
    have hace : (Expr.var "ac").evalB B ρ = some ac := by
      have h := evalB_var (B := B) (x := "ac") (σ := ρ) (by omega)
      rwa [← hac] at h
    have hread : (Expr.get (memName (j + 1)) (.var "ac")).evalB B ρ = some (Mem1 ac) :=
      evalB_get hace (by rw [hmem1ρ, getElem?_arrOf Mem1 hacn]) (by omega)
    set ρ₁ := ρ.setVar "ax" (Mem1 ac) with hρ₁
    have hr'₁ : Run B (.assign "ax" (.get (memName (j + 1)) (.var "ac"))) ρ ρ₁ 3 :=
      (Run.assign hread).mono (by simp [Expr.size])
    have hax₁ : ρ₁.vars "ax" = Mem1 ac := by rw [hρ₁, vars_setVar, if_pos rfl]
    have hac₁ : ρ₁.vars "ac" = ac := by rw [hρ₁, vars_setVar, if_neg (by decide)]
    have hgarr₁ : ρ₁.arrs a = arrOf n g := by rw [hρ₁, arrs_setVar]; exact hgarr
    have hmem1₁ : ρ₁.arrs (memName (j + 1)) = arrOf n Mem1 := by
      rw [hρ₁, arrs_setVar]; exact hmem1ρ
    have hmm1₁ : ρ₁.vars (mnumName (j + 1)) = mm1 := by
      rw [hρ₁, vars_setVar, if_neg (Ne.symm (ax_ne_mnumName j))]; exact hmm1ρ
    -- the store at the listed vertex
    have haxe : (Expr.var "ax").evalB B ρ₁ = some (Mem1 ac) := by
      have h := evalB_var (B := B) (x := "ax") (σ := ρ₁) (by rw [hax₁]; omega)
      rwa [hax₁] at h
    have hlen₁ : Mem1 ac < (ρ₁.arrs a).length := by rw [hgarr₁, length_arrOf]; exact hvn
    set ρ₂ := ρ₁.setArr a (Mem1 ac) c with hρ₂
    have hr'₂ : Run B (.store a (.var "ax") (.lit c)) ρ₁ ρ₂ 3 :=
      (Run.store haxe (evalB_lit (by omega)) hlen₁).mono (by simp [Expr.size])
    have hac₂ : ρ₂.vars "ac" = ac := by rw [hρ₂, vars_setArr]; exact hac₁
    -- the read pointer moves
    have hace₂ : (Expr.add (Expr.var "ac") (.lit 1)).evalB B ρ₂ = some (ac + 1) := by
      have h := evalB_bin (evalB_var (B := B) (x := "ac") (σ := ρ₂) (by rw [hac₂]; omega))
        (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
        (show Bop.add.apply (ρ₂.vars "ac") 1 < B by rw [Bop.apply_add, hac₂]; omega)
      rw [Bop.apply_add, hac₂] at h
      exact h
    set ρ₃ := ρ₂.setVar "ac" (ac + 1) with hρ₃
    have hr'₃ : Run B (.assign "ac" (.add (.var "ac") (.lit 1))) ρ₂ ρ₃ 4 :=
      (Run.assign hace₂).mono (by simp [Expr.size])
    set gu : ℕ → ℕ := fun k => if k = Mem1 ac then c else g k with hgu
    have hac₃ : ρ₃.vars "ac" = ac + 1 := by rw [hρ₃, vars_setVar, if_pos rfl]
    have hmm1₃ : ρ₃.vars (mnumName (j + 1)) = mm1 := by
      rw [hρ₃, vars_setVar, if_neg (Ne.symm (ac_ne_mnumName j)), hρ₂, vars_setArr]
      exact hmm1₁
    have hgarr₃ : ρ₃.arrs a = arrOf n gu := by
      rw [hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_pos rfl, hgarr₁, set_arrOf]
    have hmem1₃ : ρ₃.arrs (memName (j + 1)) = arrOf n Mem1 := by
      rw [hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_neg (Ne.symm hane)]
      exact hmem1₁
    refine ⟨ρ₃, 10, ((hr'₁.seq (hr'₂.seq hr'₃))).mono (by omega), ?_, hac₃, le_rfl⟩
    refine ⟨hmm1₃, by omega, hmem1₃, gu, hgarr₃, ?_, ?_⟩
    · intro p hp
      rw [hac₃] at hp
      by_cases hpe : Mem1 p = Mem1 ac
      · rw [hgu]; simp only []; rw [hpe, if_pos rfl]
      · have hpac : p ≠ ac := fun h => hpe (by rw [h])
        rw [hgu]; simp only []; rw [if_neg hpe]
        exact hset p (by omega)
    · intro v hv hnot
      rw [hac₃] at hnot
      have hne : Mem1 ac ≠ v := hnot ac (by omega)
      rw [hgu]; simp only []; rw [if_neg (fun h => hne h.symm)]
      exact hkeep v hv (fun p hp => hnot p (by omega))
  have hI₁ : MemFillInv n j mm1 a c Mem1 g₀ σ₁ := by
    have hac₁ : σ₁.vars "ac" = 0 := by rw [hσ₁, vars_setVar, if_pos rfl]
    refine ⟨by rw [hσ₁, vars_setVar, if_neg (Ne.symm (ac_ne_mnumName j))]; exact hmm1,
      by omega, by rw [hσ₁, arrs_setVar]; exact hmem1, g₀,
      by rw [hσ₁, arrs_setVar]; exact harr, ?_, ?_⟩
    · intro p hp; rw [hac₁] at hp; omega
    · intro v _ _; rfl
  obtain ⟨σ₂, hr₂, hI₂, hac₂⟩ :=
    (Csr.rowScan_spec B (14 * mm1 + 4) mm1 10 "ac" (mnumName (j + 1))
      (.seq (.assign "ax" (.get (memName (j + 1)) (.var "ac")))
        (.seq (.store a (.var "ax") (.lit c))
          (.assign "ac" (.add (.var "ac") (.lit 1)))))
      (MemFillInv n j mm1 a c Mem1 g₀) hm1B (fun ρ hρ => ⟨hρ.1, hρ.2.1⟩) hstep
      (fun _ hρ => hρ)
      (fun ρ hρ => by
        have h : (10 + 4) * (mm1 - ρ.vars "ac") ≤ 14 * mm1 := Nat.mul_le_mul le_rfl (by omega)
        omega)).run hI₁
  obtain ⟨hmm1₂, -, hmem1₂, g, hgarr₂, hset₂, hkeep₂⟩ := hI₂
  rw [hac₂] at hset₂ hkeep₂
  exact ⟨σ₂, _, hr₁.seq hr₂, by rw [memFillAtCost]; omega,
    ⟨g, hgarr₂, hset₂, hkeep₂⟩, hmm1₂, hmem1₂⟩

/-- What the touched-only copy carries: the fill's law with the source
array frozen beside it. -/
def MemCopyInv (n j mm1 : ℕ) (src a : String) (Mem1 F g₀ : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars (mnumName (j + 1)) = mm1 ∧ σ.vars "ac" ≤ mm1 ∧
    σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧ σ.arrs src = arrOf n F ∧
    ∃ g, σ.arrs a = arrOf n g ∧
      (∀ p, p < σ.vars "ac" → g (Mem1 p) = F (Mem1 p)) ∧
      (∀ v, v < n → (∀ p, p < σ.vars "ac" → Mem1 p ≠ v) → g v = g₀ v)

/-- **The touched-only copy, walked.** The listed cells hold the source's
value; every other cell is untouched. -/
theorem memCopyAt_spec {j mm1 : ℕ} {src a : String} {Mem1 F g₀ A : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hFB : ∀ v, v < n → F v < B)
    (hane : a ≠ memName (j + 1)) (hsa : src ≠ a) (hMenum : MemEnum n mm1 Mem1 A) :
    Spec B (fun σ => σ.vars (mnumName (j + 1)) = mm1 ∧
        σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧ σ.arrs src = arrOf n F ∧
        σ.arrs a = arrOf n g₀)
      (memCopyAt j src a)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf n g ∧
          (∀ p, p < mm1 → g (Mem1 p) = F (Mem1 p)) ∧
          (∀ v, v < n → (∀ p, p < mm1 → Mem1 p ≠ v) → g v = g₀ v)) ∧
        σ'.vars (mnumName (j + 1)) = mm1 ∧
        σ'.arrs (memName (j + 1)) = arrOf n Mem1 ∧ σ'.arrs src = arrOf n F)
      (memCopyAtCost mm1) := by
  obtain ⟨hMlt, -, -, -⟩ := id hMenum
  have hm1n : mm1 ≤ n := hMenum.card_le
  have hm1B : mm1 < B := by omega
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hmm1, hmem1, hsrc, harr⟩ := hσ
  set σ₁ := σ.setVar "ac" 0 with hσ₁
  have hr₁ : Run B (.assign "ac" (.lit 0)) σ σ₁ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hstep : ∀ ρ : Env, MemCopyInv n j mm1 src a Mem1 F g₀ ρ → ρ.vars "ac" < mm1 →
      ∃ ρ' K', Run B (.seq (.assign "ax" (.get (memName (j + 1)) (.var "ac")))
          (.seq (.store a (.var "ax") (.get src (.var "ax")))
            (.assign "ac" (.add (.var "ac") (.lit 1))))) ρ ρ' K' ∧
        MemCopyInv n j mm1 src a Mem1 F g₀ ρ' ∧ ρ'.vars "ac" = ρ.vars "ac" + 1 ∧ K' ≤ 11 := by
    intro ρ hρ hlt
    obtain ⟨hmm1ρ, hacρ, hmem1ρ, hsrcρ, g, hgarr, hset, hkeep⟩ := hρ
    set ac := ρ.vars "ac" with hac
    have hvn : Mem1 ac < n := hMlt ac hlt
    have hacn : ac < n := by omega
    have hace : (Expr.var "ac").evalB B ρ = some ac := by
      have h := evalB_var (B := B) (x := "ac") (σ := ρ) (by omega)
      rwa [← hac] at h
    have hread : (Expr.get (memName (j + 1)) (.var "ac")).evalB B ρ = some (Mem1 ac) :=
      evalB_get hace (by rw [hmem1ρ, getElem?_arrOf Mem1 hacn]) (by omega)
    set ρ₁ := ρ.setVar "ax" (Mem1 ac) with hρ₁
    have hr'₁ : Run B (.assign "ax" (.get (memName (j + 1)) (.var "ac"))) ρ ρ₁ 3 :=
      (Run.assign hread).mono (by simp [Expr.size])
    have hax₁ : ρ₁.vars "ax" = Mem1 ac := by rw [hρ₁, vars_setVar, if_pos rfl]
    have hac₁ : ρ₁.vars "ac" = ac := by rw [hρ₁, vars_setVar, if_neg (by decide)]
    have hgarr₁ : ρ₁.arrs a = arrOf n g := by rw [hρ₁, arrs_setVar]; exact hgarr
    have hsrc₁ : ρ₁.arrs src = arrOf n F := by rw [hρ₁, arrs_setVar]; exact hsrcρ
    have hmem1₁ : ρ₁.arrs (memName (j + 1)) = arrOf n Mem1 := by
      rw [hρ₁, arrs_setVar]; exact hmem1ρ
    have hmm1₁ : ρ₁.vars (mnumName (j + 1)) = mm1 := by
      rw [hρ₁, vars_setVar, if_neg (Ne.symm (ax_ne_mnumName j))]; exact hmm1ρ
    have haxe : (Expr.var "ax").evalB B ρ₁ = some (Mem1 ac) := by
      have h := evalB_var (B := B) (x := "ax") (σ := ρ₁) (by rw [hax₁]; omega)
      rwa [hax₁] at h
    have hvale : (Expr.get src (.var "ax")).evalB B ρ₁ = some (F (Mem1 ac)) :=
      evalB_get haxe (by rw [hsrc₁, getElem?_arrOf F hvn]) (hFB _ hvn)
    have hlen₁ : Mem1 ac < (ρ₁.arrs a).length := by rw [hgarr₁, length_arrOf]; exact hvn
    set ρ₂ := ρ₁.setArr a (Mem1 ac) (F (Mem1 ac)) with hρ₂
    have hr'₂ : Run B (.store a (.var "ax") (.get src (.var "ax"))) ρ₁ ρ₂ 4 :=
      (Run.store haxe hvale hlen₁).mono (by simp [Expr.size])
    have hac₂ : ρ₂.vars "ac" = ac := by rw [hρ₂, vars_setArr]; exact hac₁
    have hace₂ : (Expr.add (Expr.var "ac") (.lit 1)).evalB B ρ₂ = some (ac + 1) := by
      have h := evalB_bin (evalB_var (B := B) (x := "ac") (σ := ρ₂) (by rw [hac₂]; omega))
        (evalB_lit (B := B) (show (1 : ℕ) < B by omega))
        (show Bop.add.apply (ρ₂.vars "ac") 1 < B by rw [Bop.apply_add, hac₂]; omega)
      rw [Bop.apply_add, hac₂] at h
      exact h
    set ρ₃ := ρ₂.setVar "ac" (ac + 1) with hρ₃
    have hr'₃ : Run B (.assign "ac" (.add (.var "ac") (.lit 1))) ρ₂ ρ₃ 4 :=
      (Run.assign hace₂).mono (by simp [Expr.size])
    set gu : ℕ → ℕ := fun k => if k = Mem1 ac then F (Mem1 ac) else g k with hgu
    have hac₃ : ρ₃.vars "ac" = ac + 1 := by rw [hρ₃, vars_setVar, if_pos rfl]
    have hmm1₃ : ρ₃.vars (mnumName (j + 1)) = mm1 := by
      rw [hρ₃, vars_setVar, if_neg (Ne.symm (ac_ne_mnumName j)), hρ₂, vars_setArr]
      exact hmm1₁
    have hgarr₃ : ρ₃.arrs a = arrOf n gu := by
      rw [hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_pos rfl, hgarr₁, set_arrOf]
    have hmem1₃ : ρ₃.arrs (memName (j + 1)) = arrOf n Mem1 := by
      rw [hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_neg (Ne.symm hane)]
      exact hmem1₁
    have hsrc₃ : ρ₃.arrs src = arrOf n F := by
      rw [hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_neg hsa]
      exact hsrc₁
    refine ⟨ρ₃, 11, ((hr'₁.seq (hr'₂.seq hr'₃))).mono (by omega), ?_, hac₃, le_rfl⟩
    refine ⟨hmm1₃, by omega, hmem1₃, hsrc₃, gu, hgarr₃, ?_, ?_⟩
    · intro p hp
      rw [hac₃] at hp
      by_cases hpe : Mem1 p = Mem1 ac
      · rw [hgu]; simp only []; rw [hpe, if_pos rfl]
      · have hpac : p ≠ ac := fun h => hpe (by rw [h])
        rw [hgu]; simp only []; rw [if_neg hpe]
        exact hset p (by omega)
    · intro v hv hnot
      rw [hac₃] at hnot
      have hne : Mem1 ac ≠ v := hnot ac (by omega)
      rw [hgu]; simp only []; rw [if_neg (fun h => hne h.symm)]
      exact hkeep v hv (fun p hp => hnot p (by omega))
  have hI₁ : MemCopyInv n j mm1 src a Mem1 F g₀ σ₁ := by
    have hac₁ : σ₁.vars "ac" = 0 := by rw [hσ₁, vars_setVar, if_pos rfl]
    refine ⟨by rw [hσ₁, vars_setVar, if_neg (Ne.symm (ac_ne_mnumName j))]; exact hmm1,
      by omega, by rw [hσ₁, arrs_setVar]; exact hmem1,
      by rw [hσ₁, arrs_setVar]; exact hsrc, g₀,
      by rw [hσ₁, arrs_setVar]; exact harr, ?_, ?_⟩
    · intro p hp; rw [hac₁] at hp; omega
    · intro v _ _; rfl
  obtain ⟨σ₂, hr₂, hI₂, hac₂⟩ :=
    (Csr.rowScan_spec B (15 * mm1 + 4) mm1 11 "ac" (mnumName (j + 1))
      (.seq (.assign "ax" (.get (memName (j + 1)) (.var "ac")))
        (.seq (.store a (.var "ax") (.get src (.var "ax")))
          (.assign "ac" (.add (.var "ac") (.lit 1)))))
      (MemCopyInv n j mm1 src a Mem1 F g₀) hm1B (fun ρ hρ => ⟨hρ.1, hρ.2.1⟩) hstep
      (fun _ hρ => hρ)
      (fun ρ hρ => by
        have h : (11 + 4) * (mm1 - ρ.vars "ac") ≤ 15 * mm1 := Nat.mul_le_mul le_rfl (by omega)
        omega)).run hI₁
  obtain ⟨hmm1₂, -, hmem1₂, hsrc₂, g, hgarr₂, hset₂, hkeep₂⟩ := hI₂
  rw [hac₂] at hset₂ hkeep₂
  exact ⟨σ₂, _, hr₁.seq hr₂, by rw [memCopyAtCost]; omega,
    ⟨g, hgarr₂, hset₂, hkeep₂⟩, hmm1₂, hmem1₂, hsrc₂⟩

/-! #### The three uses -/

/-- **The mask copy at the member list produces `ArenaA`'s mask clause**
— from a scratch array that is zero off the child's alive set, and at
`15·mm1 + 6` with the carrier nowhere in the charge.

The off-list half is `MemEnum`'s fourth clause read backwards: a vertex
the list omits is not alive, so the mask's own value there is zero, which
is what the clean scratch already holds. -/
theorem alvMemCom_spec {j mm1 : ℕ} {Mem1 Alv' : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hAB : ∀ v, v < n → Alv' v < B)
    (hMenum : MemEnum n mm1 Mem1 Alv') :
    Spec B (fun σ => σ.vars (mnumName (j + 1)) = mm1 ∧
        σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧
        σ.arrs (alvName (j + 1)) = arrOf n Alv' ∧
        σ.arrs "alv" = arrOf n (fun _ => 0))
      (alvMemCom j)
      (fun _ σ' => σ'.arrs "alv" = arrOf n Alv' ∧
        σ'.vars (mnumName (j + 1)) = mm1 ∧
        σ'.arrs (memName (j + 1)) = arrOf n Mem1 ∧
        σ'.arrs (alvName (j + 1)) = arrOf n Alv')
      (memCopyAtCost mm1) := by
  refine ((memCopyAt_spec (B := B) (n := n) (j := j) (mm1 := mm1)
    (src := alvName (j + 1)) (a := "alv") (Mem1 := Mem1) (F := Alv') (g₀ := fun _ => 0)
    (A := Alv') hB hnB hAB (by simp [memName, String.ext_iff])
    (by simp [alvName, String.ext_iff]) hMenum).post ?_)
  rintro σ σ' - ⟨⟨g, hgarr, hset, hkeep⟩, hmm1, hmem1, hsrc⟩
  refine ⟨?_, hmm1, hmem1, hsrc⟩
  rw [hgarr]
  refine arrOf_congr (fun v hv => ?_)
  by_cases hlist : ∃ p, p < mm1 ∧ Mem1 p = v
  · obtain ⟨p, hp, rfl⟩ := hlist
    exact hset p hp
  · push_neg at hlist
    rw [hkeep v hv (fun p hp => hlist p hp)]
    by_contra hne
    obtain ⟨p, hp, hpv⟩ := hMenum.2.2.2 v hv (fun h => hne h.symm)
    exact hlist p hp hpv

/-- **…and the restore puts it back.** The same walk at the constant
zero returns `"alv"` to the clean state the copy consumed, so the pair
is a round trip: an atom that sets the mask before the engine and clears
it after leaves the scratch exactly as it found it, at `14·mm1 + 6`. -/
theorem alvClrCom_spec {j mm1 : ℕ} {Mem1 Alv' : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B)
    (hMenum : MemEnum n mm1 Mem1 Alv') :
    Spec B (fun σ => σ.vars (mnumName (j + 1)) = mm1 ∧
        σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧
        σ.arrs "alv" = arrOf n Alv')
      (alvClrCom j)
      (fun _ σ' => σ'.arrs "alv" = arrOf n (fun _ => 0) ∧
        σ'.vars (mnumName (j + 1)) = mm1 ∧
        σ'.arrs (memName (j + 1)) = arrOf n Mem1)
      (memFillAtCost mm1) := by
  refine ((memFillAt_spec (B := B) (n := n) (j := j) (mm1 := mm1) (c := 0)
    (a := "alv") (Mem1 := Mem1) (g₀ := Alv') (A := Alv') hB hnB (by omega)
    (by simp [memName, String.ext_iff]) hMenum).post ?_)
  rintro σ σ' - ⟨⟨g, hgarr, hset, hkeep⟩, hmm1, hmem1⟩
  refine ⟨?_, hmm1, hmem1⟩
  rw [hgarr]
  refine arrOf_congr (fun v hv => ?_)
  by_cases hlist : ∃ p, p < mm1 ∧ Mem1 p = v
  · obtain ⟨p, hp, rfl⟩ := hlist
    exact hset p hp
  · push_neg at hlist
    rw [hkeep v hv (fun p hp => hlist p hp)]
    by_contra hne
    obtain ⟨p, hp, hpv⟩ := hMenum.2.2.2 v hv hne
    exact hlist p hp hpv

/-- **The distance fill at the member list**, at `14·mm1 + 6`: every
*listed* vertex holds the search's sentinel, and no other cell moves.
Since wave B4-walk-2m-3 this is the pass `RamDriver.scatDeadCom`
actually runs at the sixth slot.

That is where `Refine.BfsBlock`'s search reads and writes — its two mask
reads gate the relaxation, and its unwind walks the queue — and it is
`Refine.ScatterBlock.DistClean n r M`, the seventh clause of
`Refine.ScatterBlockMask.ArenaAtM`, once the driving list covers the
mask: `Refine.ScatterBlockMask.distClean_of_cover` applied to this
postcondition and to `MemEnum`'s fourth clause. It is **not**
`Refine.ScatterBlock.ArenaAt`'s seventh clause, which pins the whole
array; `dist_touched_only_refuted` is that gap, on data, and is why the
engine had to be re-walked first. -/
theorem distMemCom_spec {j mm1 r : ℕ} {Mem1 g₀ A : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hrB : r + 1 < B)
    (hMenum : MemEnum n mm1 Mem1 A) :
    Spec B (fun σ => σ.vars (mnumName (j + 1)) = mm1 ∧
        σ.arrs (memName (j + 1)) = arrOf n Mem1 ∧ σ.arrs "dist" = arrOf n g₀)
      (distMemCom j r)
      (fun _ σ' => (∃ g, σ'.arrs "dist" = arrOf n g ∧
          (∀ p, p < mm1 → g (Mem1 p) = r + 1) ∧
          (∀ v, v < n → (∀ p, p < mm1 → Mem1 p ≠ v) → g v = g₀ v)) ∧
        σ'.vars (mnumName (j + 1)) = mm1 ∧
        σ'.arrs (memName (j + 1)) = arrOf n Mem1)
      (memFillAtCost mm1) :=
  memFillAt_spec (B := B) (n := n) (j := j) (mm1 := mm1) (c := r + 1) (a := "dist")
    (Mem1 := Mem1) (g₀ := g₀) (A := A) hB hnB hrB (by simp [memName, String.ext_iff]) hMenum

end MemberScaleEntry

/-! ### §5g The replacement measured, and the two blockers on data

The instrument is `TgtWidenProbe.execC` again — the state, and the
`Lax13Proofs.BigStepB` clock currency for currency. What is checked:
the clock does not read the carrier, the landed passes at the same slot
do, and the two preconditions the replacement needs are exactly the two
the atom's entry state does not supply. -/

section MemberScaleProbes

open Lax3Proofs.TgtWidenProbe (execC pB pF PSt)

/-- A three-member child inside an `n`-cell carrier: the alive vertices
are `2`, `5` and `7`, the child mask is alive exactly there, and the two
scratch arrays are clean. -/
def mwSt (n : ℕ) : PSt :=
  { vars := [("n", n), (mnumName 1, 3)]
    arrs := [(memName 1, [2, 5, 7] ++ List.replicate (n - 3) 0),
             (alvName 1, (((List.replicate n 0).set 2 1).set 5 1).set 7 1),
             ("alv", List.replicate n 0),
             ("dist", List.replicate n 0)] }

/-- The same turn with no alive child at all. -/
def mwSt0 (n : ℕ) : PSt := { mwSt n with vars := [("n", n), (mnumName 1, 0)] }

-- **the mask copy at the member list runs, and moves exactly the three
-- listed cells**
#guard (execC pB pF (alvMemCom 0) (mwSt 10)).1.isOk
#guard (List.range 10).map ((execC pB pF (alvMemCom 0) (mwSt 10)).1.cell "alv") =
  [0, 0, 1, 0, 0, 1, 0, 1, 0, 0]

-- **the clock is carrier-blind**: the same three members inside a
-- ten-cell and a two-hundred-cell carrier clock identically
#guard (execC pB pF (alvMemCom 0) (mwSt 10)).2 = (execC pB pF (alvMemCom 0) (mwSt 200)).2
#guard (execC pB pF (alvClrCom 0) (mwSt 10)).2 = (execC pB pF (alvClrCom 0) (mwSt 200)).2
#guard (execC pB pF (distMemCom 0 1) (mwSt 10)).2 =
  (execC pB pF (distMemCom 0 1) (mwSt 200)).2

-- and it is the charge the specification claims, at three members and
-- at none: `15·3 + 6` and `14·3 + 6`, `6` when the list is empty
#guard (execC pB pF (alvMemCom 0) (mwSt 10)).2 = memCopyAtCost 3
#guard (execC pB pF (distMemCom 0 1) (mwSt 10)).2 = memFillAtCost 3
#guard (execC pB pF (alvMemCom 0) (mwSt0 10)).2 = memCopyAtCost 0
#guard (execC pB pF (distMemCom 0 1) (mwSt0 200)).2 = memFillAtCost 0

-- **the negative control**: the landed passes at the same two slots
-- clock the carrier, and grow with it
#guard (execC pB pF (copyCom (alvName 1) "alv") (mwSt 10)).2 <
  (execC pB pF (copyCom (alvName 1) "alv") (mwSt 200)).2
#guard (execC pB pF (fillCom "dist" (.lit 2)) (mwSt 10)).2 <
  (execC pB pF (fillCom "dist" (.lit 2)) (mwSt 200)).2
#guard (execC pB pF (copyCom (alvName 1) "alv") (mwSt 10)).2 = 12 * 10 + 6
#guard (execC pB pF (fillCom "dist" (.lit 2)) (mwSt 10)).2 = 11 * 10 + 6

/-- The same turn with the mask scratch **dirty** — the state the atom
actually starts in, since `"alv"` is a `RamDriverFrames.scratchArrs`
entry that the descent, the cover phase and the nested driver all write
and no clause of `ScatterDeadTurn.DeadPre` pins. -/
def mwStDirty (n : ℕ) : PSt :=
  { mwSt n with
    arrs := (mwSt n).arrs.map fun p => if p.1 = "alv" then ("alv", List.replicate n 1) else p }

/-- **BLOCKER 1, on data: the touched-only mask copy needs a clean
scratch.** Run from a dirty `"alv"` the pass leaves the three listed
cells right and everything else wrong — here vertex `3`, which the child
mask kills, comes out alive. That is not an accounting defect: `"alv"` is
the block search's eligibility test (`Refine.BfsBlock`'s two mask reads),
so a junk-alive cell puts a dead vertex on the frontier and enlarges the
ball the engine counts.

The landed `RamDriver.copyCom` is immune because it writes every cell;
the replacement is immune only under an invariant that says the scratch
is zero off the child's alive set, and `RamDriver.LevelMem` gives the
array's **length** and nothing else. Supplying that invariant is the
driver-wide clean-scratch discipline (R1.6), not this wave's. -/
theorem alv_touched_only_needs_clean_scratch :
    (execC pB pF (alvMemCom 0) (mwStDirty 10)).1.cell "alv" 2 = 1 ∧
      (execC pB pF (alvMemCom 0) (mwStDirty 10)).1.cell "alv" 3 = 1 ∧
      (execC pB pF (copyCom (alvName 1) "alv") (mwStDirty 10)).1.cell "alv" 3 = 0 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The same turn with `"dist"` clean **at the previous atom's radius** —
the state the engine's own clean-out leaves, since it restores the array
at its own sentinel. -/
def mwStPrev (n : ℕ) : PSt :=
  { mwSt n with
    arrs := (mwSt n).arrs.map fun p => if p.1 = "dist" then ("dist", List.replicate n 9) else p }

/-- **THE READING THAT WAS REPLACED, on data: the touched-only distance
fill cannot produce `ArenaA`'s clause.** Kept, not deleted: this is the
compiled record of the contract wave B4-walk-2m-3 had to move, and it
still refutes exactly what it always did.

The clause is `σ.arrs "dist" = arrOf n (fun _ => r + 1)` — the *whole*
array at this atom's own radius — and consecutive atoms of a turn carry
different radii, so the cells the child's list does not name are stale by
exactly one radius step whatever the caller does. Here the fill at
`r = 1` leaves `2` at the three listed vertices and the previous atom's
`9` everywhere else.

Unlike blocker 1 this was not repairable by any discipline on the
caller: the clause had to be narrowed to the mask's support, and that is
the engine's own contract — `Refine.BfsBlock.unwind_run` proves the array
comes back as the same literal list by an `arrOf_congr` over every
`i < n`, and `RamBfs.Frontier`'s `cap`/`sound` clauses are consumed at
*dead* vertices in `frontier_seed_alive`/`frontier_seed_dead`. Waves
B4-walk-2m-1/2 did narrow it, to `Refine.ScatterBlock.DistClean n r M`,
and against **that** clause this state is no counterexample at all: cell
`3` is dead, so nothing is claimed about it. The theorem below therefore
still holds and no longer bites — which is the precise sense in which
the fill became wirable. -/
theorem dist_touched_only_refuted :
    (execC pB pF (distMemCom 0 1) (mwStPrev 10)).1.cell "dist" 2 = 2 ∧
      (execC pB pF (distMemCom 0 1) (mwStPrev 10)).1.cell "dist" 3 = 9 ∧
      (execC pB pF (fillCom "dist" (.lit 2)) (mwStPrev 10)).1.cell "dist" 3 = 2 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A four-vertex arena whose only edges are `0—1` and `1—3`: the child
mask is alive at `0` and `3`, and the vertex between them is dead. The
member list is `[0, 3]`, the radius is `2` and the threshold is `2`. -/
def engSt (alv : List ℕ) : PSt :=
  { vars := [("n", 4), ("mm", 2)]
    arrs := [("off", [0, 1, 3, 3, 4]), ("tgt", [1, 0, 3, 1]),
             ("alv", alv), ("mem", [0, 3, 0, 0]),
             ("dist", [3, 3, 3, 3]), ("q", [0, 0, 0, 0]), ("qd", [0, 0, 0, 0]),
             ("exc", [0, 0, 0, 0])] }

/-- **BLOCKER 1 is semantic, not cosmetic: the engine's own answer moves
with the junk.** The same arena, the same member list, the same radius
and threshold — only the cells of `"alv"` that the child's alive set
does *not* name are different. At the true mask the walk `0—1—3` is
broken at the dead middle vertex, so the two members are two picks and
the flag is `1`; with the junk alive the ball of `0` swallows `3` and
the flag is `0`.

So the mask copy is not a charge that a better accounting could
re-attribute: `Refine.ScatterBlock.ArenaA`'s mask clause is what the
engine's conclusion is *about* (`masked G M`), and every cell of it is
load-bearing. A touched-only mask write is sound only against an
invariant that already zeroes the rest. -/
theorem mask_junk_flips_the_engine :
    (execC pB pF (scatBlockCom 2 2) (engSt [1, 0, 0, 1])).1.scalar "flag" = 1 ∧
      (execC pB pF (scatBlockCom 2 2) (engSt [1, 1, 1, 1])).1.scalar "flag" = 0 ∧
      (execC pB pF (scatBlockCom 2 2) (engSt [1, 0, 0, 1])).1.isOk ∧
      (execC pB pF (scatBlockCom 2 2) (engSt [1, 1, 1, 1])).1.isOk := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The round trip, on data**: mask copy, then restore, and the
scratch is back where it started. This is the half of the discipline the
atom phase *can* maintain by itself — what it cannot do is establish the
clean state the first time. -/
theorem alv_set_clear_round_trip :
    (List.range 10).map
        ((execC pB pF (.seq (alvMemCom 0) (alvClrCom 0)) (mwSt 10)).1.cell "alv") =
      List.replicate 10 0 := by
  decide +kernel

end MemberScaleProbes

/-! ### §5e The four driver passes, composed and run

The compiled integration gate: the four passes of `scatDeadCom` that
this wave wrote, in the order the program runs them, on one arena. The
engine and the `botCom` fragment are landed capital and are gated next
door; what this checks is that the four new passes **compose** — no
scratch name of one is a product of another, and the four registers the
verdict reads all arrive together. -/

section Integration

open Lax3Proofs.TgtWidenProbe (execC pB pF PSt)

/-- The four new passes, in program order (the engine's entry, the
engine and the verdict are the landed half). -/
def atomTermsCom (j ti : ℕ) : Com :=
  .seq (killSumCom j ti) (.seq (outProbeCom j) (.seq (outCntCom j) (atomMemCom j ti)))

/-- A ten-vertex turn: cluster `{0, 1, 2}`, the batch killing `0` and
`1`, so the child's alive set is `{2}` and its member list is `[2]`; the
atom's row marks `1` (a kill) and `2` (the alive member). The outside
class is the seven vertices `3 .. 9`. -/
def itSt : PSt :=
  { vars := [("n", 10), (kkName 0, 2), (mnumName 1, 1)]
    arrs := [(klName 0, [0, 1, 0]),
             (tabName 1 0, [0, 1, 1, 0, 0, 0, 0, 0, 0, 0]),
             (alvName 1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0]),
             (cluName 0, [1, 1, 1, 0, 0, 0, 0, 0, 0, 0]),
             (memName 1, [2, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
             ("mem", [9, 9, 9, 9, 9, 9, 9, 9, 9, 9])] }

/-- **The four passes compose.** One of the two kills satisfies the
atom, so the kill term is `1`; the first dead out-of-cluster vertex is
`3`, so the probe reports it and the outside term will be one bit times
`10 − 1 − 2 = 7`; and the filtered member list is the single alive
member `2`. Every register the verdict reads is present at once, which
is what the composition claims. -/
theorem atomTerms_compose :
    (execC pB pF (atomTermsCom 0 0) itSt).1.isOk = true ∧
      (execC pB pF (atomTermsCom 0 0) itSt).1.scalar "kc" = 1 ∧
      (execC pB pF (atomTermsCom 0 0) itSt).1.scalar "of" = 1 ∧
      (execC pB pF (atomTermsCom 0 0) itSt).1.scalar "oz" = 3 ∧
      (execC pB pF (atomTermsCom 0 0) itSt).1.scalar "oc" = 7 ∧
      (execC pB pF (atomTermsCom 0 0) itSt).1.scalar "mm" = 1 ∧
      (execC pB pF (atomTermsCom 0 0) itSt).1.cell "mem" 0 = 2 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

end Integration

/-! ### §6 Axioms -/

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.atomMemCom_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms atomMemCom_spec

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.killSumCom_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms killSumCom_spec

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.outProbeCom_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms outProbeCom_spec

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.outProbeCom_specB' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms outProbeCom_specB

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.outside_prefix_bound' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms outside_prefix_bound

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKX_carrier' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKX_carrier

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKX_mono' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKX_mono

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKX_le_carrier' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKX_le_carrier

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKX_le_blk' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKX_le_blk

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKX_carrier_free' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKX_carrier_free

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKX_carrier_indep' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKX_carrier_indep

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKX_mono_carrier' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKX_mono_carrier

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKX_carrier_indep_refuted' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKX_carrier_indep_refuted

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKXwhole_trade' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKXwhole_trade

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.scatDeadKXwhole_unbounded' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms scatDeadKXwhole_unbounded

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.noWrite_memFillAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms noWrite_memFillAt

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.exists_outside_le_ncard' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms exists_outside_le_ncard

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.atomTerms_iff_scatVal' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms atomTerms_iff_scatVal

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.atomTerms_iff_scatVal_of_clusterData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms atomTerms_iff_scatVal_of_clusterData

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.inplace_filter_refuted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms inplace_filter_refuted

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.game_arena_sees_the_cluster_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms game_arena_sees_the_cluster_cut

/-- info: 'Lax3Proofs.Refine.ScatterDeadPass.dead_inter_union_batch' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms dead_inter_union_batch

-- wave E4c-b: the touched-only replacement, its three readings, and the
-- two blockers
#print axioms memFillAt_spec
#print axioms memCopyAt_spec
#print axioms alvMemCom_spec
#print axioms alvClrCom_spec
#print axioms distMemCom_spec
#print axioms alv_touched_only_needs_clean_scratch
#print axioms dist_touched_only_refuted
#print axioms mask_junk_flips_the_engine
#print axioms alv_set_clear_round_trip

end Lax3Proofs.Refine.ScatterDeadPass
