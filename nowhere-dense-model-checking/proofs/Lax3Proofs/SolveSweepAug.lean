import Lax3Proofs.SolveSweepMdPeel

/-!
# F6c11b (part 5) — the augmentation pass, discharged: `CovAugAdjIn`

`SolveSweepOrder` names `CovAugAdjIn`: per admissible level arena,
from `CovOrderIn`'s exact precondition, run the `R` rounds of the
deterministic tight transitive–fraternal augmentation and leave the
symmetrized augmented graph `(mdChain A.G R).toGraph` as a deletable
adjacency region, preserving the arena, the two allocations, and the
two abstract scratch descriptors. This file provides the concrete
program family and proves that contract, verbatim, as
`covAugAdjIn_agCom` — the `hag` input of `covOrderIn_of_aug_mdPeel`.

## The representation: dense `N × N` 0/1 regions

Every intermediate object of the chain is carried as a **dense
adjacency matrix** — cell `u·N + v` of a flat region holds the
indicator of the relation at `(u, v)` (`agMat`, `agBit`). The
orientation `D_i` is the *arc* matrix (`agArc`): cell `u·N + v` is
`1` exactly when `u ∈ (mdChain A.G i).inN v`, mirroring `Orientation`'s
own in-neighbour convention. Two more matrices are needed — the round's
fraternity graph (`agFm`, which doubles as the arena graph's matrix at
the start and as the symmetrized graph's at the end) and the next
round's arcs (`agArc2`) — plus the rank output and the peel's heap.

Dense is the right shape here and not a concession: the pass is priced
per round against `A.N²` and `A.N³` (`Kag`), and the algorithm's own
demand enumeration is a *pair* enumeration, so the flat pair index
`p = u·N + v` is the natural loop counter. Every loop of the file is
therefore one of two shapes — a flat scan of `N` or `N²` cells, or a
flat scan of `N²` pairs each with an inner scan of the `N` witnesses
`w` — and both are `Spec.forRangeZero` with the decoded indices
`u = p / N`, `v = p - u·N` read off `Bop.div`.

## The passes, in the order the program runs them

1. `agGrCom` — the arena's CSR into the matrix `agFm` (zero, then one
   pass per row over the slot space, testing the row window).
2. `agBldCom` — **the shared builder**: a dense symmetric irreflexive
   matrix into the deletable region `(ao, aj, dg, mt)` at the empty
   deleted set. Degrees and their prefix sums into `ao`, cursors zeroed
   in `dg`, then the counting-trick placement over the `N²` pairs: at a
   pair `(u, w)` with `w < u` carrying an edge, both directed copies go
   in at their rows' cursors with the two mate pointers crossed. Used
   `R + 2` times — once for `A.G`, once per round for the round's
   fraternity graph, once for the final symmetrized graph.
3. `mdPeelCom` — the **landed** parametric peel core
   (`mdPeelCore_spec`), leaving `mdRank` of the built graph in `agRa`.
4. `agBaseCom` — `mdChain A.G 0 = baseOr A.G (mdPerm A.G)`: arc `u → v`
   iff `A.G.Adj u v` and `mdRank A.G u < mdRank A.G v` (`mem_baseOr`,
   `mdPerm_val`).
5. `agFratCom` — the round's fraternity matrix: `u ≠ v` and some `w`
   with `u → w ← v` (`fratGraph_adj`, `FratLink`).
6. `agStepCom` — the round's greedy step, `mem_greedyStep` clause by
   clause: the inner scan of `w` accumulates the three witness counts
   `TransLink D u v`, `TransLink D v u` and `FratLink D u v`
   (`FratLink` is symmetric, so `FratLink D v u` needs no fourth), and
   the σ-comparison is the rank array's.
7. `agSymCom` — `.toGraph`: adjacent iff an arc runs either way.

`agRoundC` is 5–6–the peel–7 for one round and `agRounds R` is its
`R`-fold iterate, so the per-round identity invariant
(`agRounds_spec`: the arc matrix holds `(mdChain A.G i).inN` pointwise)
is an induction on `R` rather than a loop invariant.

## The statement's shape

`covAugAdjIn_agCom` takes only F7-suppliable hypotheses: `1 ≤ q` (the
word bound's constant, as in every sibling), one `Nodup` of the level's
array names, and one transport hypothesis per abstract descriptor
(`hSmpT`, `hSswT`) in the landed shape of `covMdPeelIn_mdPeelCom`'s
`hSswT`. The scratch descriptor `agSag` is length-only, at the level's
own carrier cell. The budget is
`Kag j A = 400·(R+1)·A.N³ + 100·(R+2)·KmdPeel A.N (…)`-shaped — see
`agK`, stated off the abstract round objects.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine
open Lax13Proofs.Codegen (getD_eq_getElem)

/-! ## §1 The bit calculus and the witness counter -/

open Classical in
/-- The indicator of a proposition, as the machine stores it. One
canonical decision procedure — every `if` of this file goes through
`agBit`, so no `Nat.decLe`/`Classical.propDecidable` mismatch can
arise between a program's stored cell and an abstract reading of it. -/
noncomputable def agBit (b : Prop) : ℕ := if b then 1 else 0

@[simp] theorem agBit_pos {b : Prop} (h : b) : agBit b = 1 := by
  classical simp [agBit, h]

@[simp] theorem agBit_neg {b : Prop} (h : ¬ b) : agBit b = 0 := by
  classical simp [agBit, h]

theorem agBit_le_one (b : Prop) : agBit b ≤ 1 := by
  classical
  by_cases h : b <;> simp [agBit, h]

theorem agBit_eq_one_iff {b : Prop} : agBit b = 1 ↔ b := by
  classical
  by_cases h : b <;> simp [agBit, h]

theorem agBit_eq_zero_iff {b : Prop} : agBit b = 0 ↔ ¬ b := by
  classical
  by_cases h : b <;> simp [agBit, h]

theorem agBit_pos_iff {b : Prop} : 0 < agBit b ↔ b := by
  classical
  by_cases h : b <;> simp [agBit, h]

theorem agBit_mul (b c : Prop) : agBit b * agBit c = agBit (b ∧ c) := by
  classical
  by_cases hb : b <;> by_cases hc : c <;> simp [agBit, hb, hc]

open Classical in
/-- The number of witnesses below `k`: how many `w : Fin N` with
`w < k` satisfy `P`. Both a degree count (at `k = N`) and an
existential accumulator (`agCnt_pos_iff`) — the machine's inner scans
maintain exactly this one quantity. -/
noncomputable def agCnt {N : ℕ} (P : Fin N → Prop) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin N => (w : ℕ) < k ∧ P w).card

theorem agCnt_zero {N : ℕ} (P : Fin N → Prop) : agCnt P 0 = 0 := by
  classical
  simp [agCnt]

theorem agCnt_succ {N : ℕ} (P : Fin N → Prop) {k : ℕ} (hk : k < N) :
    agCnt P (k + 1) = agCnt P k + agBit (P ⟨k, hk⟩) := by
  classical
  have hsplit : (Finset.univ.filter fun w : Fin N => (w : ℕ) < k + 1 ∧ P w) =
      (Finset.univ.filter fun w : Fin N => (w : ℕ) < k ∧ P w) ∪
        (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hlt, hP⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · exact Or.inl ⟨h, hP⟩
      · exact Or.inr ⟨Fin.ext h, hP⟩
    · rintro (⟨h, hP⟩ | ⟨rfl, hP⟩)
      · exact ⟨Nat.lt_succ_of_lt h, hP⟩
      · exact ⟨Nat.lt_succ_self _, hP⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun w : Fin N => (w : ℕ) < k ∧ P w)
      (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hw'
    have h1 := (Finset.mem_filter.mp hw).2.1
    have h2 := (Finset.mem_filter.mp hw').2.1
    subst h2
    exact absurd h1 (lt_irrefl _)
  have hsecond : (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w).card
      = agBit (P ⟨k, hk⟩) := by
    by_cases hP : P ⟨k, hk⟩
    · have : (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w)
          = {(⟨k, hk⟩ : Fin N)} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; exact hP⟩⟩
      rw [this, Finset.card_singleton, agBit_pos hP]
    · have : (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w)
          = (∅ : Finset (Fin N)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and]
        rintro rfl
        exact hP
      rw [this, Finset.card_empty, agBit_neg hP]
  rw [agCnt, agCnt, hsplit, Finset.card_union_of_disjoint hdisj, hsecond]

theorem agCnt_le {N : ℕ} (P : Fin N → Prop) (k : ℕ) : agCnt P k ≤ N := by
  classical
  calc agCnt P k ≤ (Finset.univ : Finset (Fin N)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by simp

theorem agCnt_pos_iff {N : ℕ} {P : Fin N → Prop} {k : ℕ} :
    0 < agCnt P k ↔ ∃ w : Fin N, (w : ℕ) < k ∧ P w := by
  classical
  rw [agCnt, Finset.card_pos]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩

open Classical in
/-- At the full range the counter is the filter card — the degree, for
an adjacency predicate. -/
theorem agCnt_full {N : ℕ} (P : Fin N → Prop) :
    agCnt P N = (Finset.univ.filter P).card := by
  classical
  rw [agCnt]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, w.isLt, true_and]

theorem agCnt_neighborSet {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) :
    agCnt (fun w => H.Adj v w) N = (H.neighborSet v).ncard := by
  classical
  rw [agCnt_full, Set.ncard_eq_toFinset_card']
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborSet]

/-! ## §2 The builder's abstract layer -/

/-- **A dense `N × N` 0/1 region**: cell `u·N + v` holds the indicator
of `P u v`. Every intermediate object of the chain is carried in this
shape. -/
def agMat (a : String) {N : ℕ} (P : Fin N → Fin N → Prop) (σ : Env) : Prop :=
  N * N ≤ (σ.arrs a).length ∧
    ∀ u v : Fin N, (σ.arrs a).getD ((u : ℕ) * N + (v : ℕ)) 0 = agBit (P u v)

theorem agMat_of_eq {a : String} {N : ℕ} {P : Fin N → Fin N → Prop}
    {σ σ' : Env} (h : agMat a P σ) (he : σ'.arrs a = σ.arrs a) :
    agMat a P σ' := by
  rw [agMat, he]; exact h

theorem agMat_congr {a : String} {N : ℕ} {P Q : Fin N → Fin N → Prop}
    {σ : Env} (h : agMat a P σ) (he : ∀ u v, P u v ↔ Q u v) :
    agMat a Q σ := by
  refine ⟨h.1, fun u v => ?_⟩
  rw [h.2 u v]
  classical
  by_cases hp : P u v
  · rw [agBit_pos hp, agBit_pos ((he u v).1 hp)]
  · rw [agBit_neg hp, agBit_neg (fun hq => hp ((he u v).2 hq))]

/-- The flat pair index is below the square. -/
theorem agPair_lt {N : ℕ} (u v : Fin N) : (u : ℕ) * N + (v : ℕ) < N * N := by
  calc (u : ℕ) * N + (v : ℕ) < (u : ℕ) * N + N := by have := v.isLt; omega
    _ = ((u : ℕ) + 1) * N := by ring
    _ ≤ N * N := Nat.mul_le_mul_right N u.isLt

/-- Splitting a flat pair index is unique below the row width. -/
theorem agSplit {N a b u w : ℕ} (hb : b < N) (hw : w < N)
    (h : a * N + b = u * N + w) : a = u ∧ b = w := by
  rcases lt_trichotomy a u with hlt | heq | hgt
  · exfalso
    have e1 : (a + 1) * N = a * N + N := by ring
    have e2 : (a + 1) * N ≤ u * N := Nat.mul_le_mul_right N hlt
    omega
  · exact ⟨heq, by rw [heq] at h; omega⟩
  · exfalso
    have e1 : (u + 1) * N = u * N + N := by ring
    have e2 : (u + 1) * N ≤ a * N := Nat.mul_le_mul_right N hgt
    omega

/-- Decoding the flat pair index the machine's `div` computes. -/
theorem agDecode {N k : ℕ} (hk : k < N * N) :
    k / N < N ∧ k % N < N ∧ (k / N) * N + k % N = k := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · omega
    · exact h
  refine ⟨?_, Nat.mod_lt _ hN, ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk)
  · have h1 := Nat.div_add_mod k N
    have h2 : (k / N) * N = N * (k / N) := Nat.mul_comm _ _
    omega

/-- **The trigger key of an unordered pair**: the flat index of the
copy at the *larger* endpoint. Symmetric, and below `N²`. -/
def agKey {N : ℕ} (u v : Fin N) : ℕ :=
  if (v : ℕ) < (u : ℕ) then (u : ℕ) * N + (v : ℕ) else (v : ℕ) * N + (u : ℕ)

theorem agKey_symm {N : ℕ} (u v : Fin N) : agKey u v = agKey v u := by
  rcases lt_trichotomy (v : ℕ) (u : ℕ) with h | h | h
  · rw [agKey, agKey, if_pos h, if_neg (by omega)]
  · rw [agKey, agKey, if_neg (by omega), if_neg (by omega), h]
  · rw [agKey, agKey, if_neg (by omega), if_pos h]

theorem agKey_of_lt {N : ℕ} {u v : Fin N} (h : (v : ℕ) < (u : ℕ)) :
    agKey u v = (u : ℕ) * N + (v : ℕ) := by rw [agKey, if_pos h]

theorem agKey_lt {N : ℕ} (u v : Fin N) : agKey u v < N * N := by
  rcases lt_trichotomy (v : ℕ) (u : ℕ) with h | h | h
  · rw [agKey, if_pos h]; exact agPair_lt u v
  · rw [agKey, if_neg (by omega)]; exact agPair_lt v u
  · rw [agKey, if_neg (by omega)]; exact agPair_lt v u

/-- The key determines the pair: the two endpoints of a key are the
quotient and the remainder. -/
theorem agKey_pair {N : ℕ} {a b : Fin N} (hne : a ≠ b) {u w : Fin N}
    (h : agKey a b = (u : ℕ) * N + (w : ℕ)) :
    (a = u ∧ b = w) ∨ (a = w ∧ b = u) := by
  rcases lt_trichotomy (b : ℕ) (a : ℕ) with hlt | heq | hgt
  · rw [agKey, if_pos hlt] at h
    obtain ⟨h1, h2⟩ := agSplit b.isLt w.isLt h
    exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
  · exact absurd (Fin.ext heq.symm) hne
  · rw [agKey, if_neg (by omega)] at h
    obtain ⟨h1, h2⟩ := agSplit a.isLt w.isLt h
    exact Or.inr ⟨Fin.ext h2, Fin.ext h1⟩

open Classical in
/-- **The partially placed graph**: the edges of `H` whose trigger key
is below `k`. The placement scan's loop invariant is stated at it, and
at `k = N²` it is `H` itself. -/
noncomputable def agPre {N : ℕ} (H : SimpleGraph (Fin N)) (k : ℕ) :
    SimpleGraph (Fin N) where
  Adj u v := H.Adj u v ∧ agKey u v < k
  symm _ _ h := ⟨h.1.symm, by rw [agKey_symm]; exact h.2⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

theorem agPre_adj {N : ℕ} {H : SimpleGraph (Fin N)} {k : ℕ} {u v : Fin N} :
    (agPre H k).Adj u v ↔ H.Adj u v ∧ agKey u v < k := Iff.rfl

theorem agPre_zero {N : ℕ} (H : SimpleGraph (Fin N)) :
    agPre H 0 = (⊥ : SimpleGraph (Fin N)) := by
  ext u v
  simp only [agPre_adj, SimpleGraph.bot_adj]
  exact ⟨fun h => absurd h.2 (Nat.not_lt_zero _), fun h => absurd h (fun h => h)⟩

theorem agPre_full {N : ℕ} (H : SimpleGraph (Fin N)) :
    agPre H (N * N) = H := by
  ext u v
  exact ⟨fun h => h.1, fun h => ⟨h, agKey_lt u v⟩⟩

theorem agPre_mono {N : ℕ} {H : SimpleGraph (Fin N)} {k : ℕ} {u v : Fin N}
    (h : (agPre H k).Adj u v) : (agPre H (k + 1)).Adj u v :=
  ⟨h.1, Nat.lt_succ_of_lt h.2⟩

/-- The placement step **skips**: no edge of `H` has key `k`, so the
partial graph does not move. -/
theorem agPre_succ_skip {N : ℕ} (H : SimpleGraph (Fin N)) {k : ℕ}
    (hno : ∀ a b : Fin N, H.Adj a b → agKey a b ≠ k) :
    agPre H (k + 1) = agPre H k := by
  ext u v
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, lt_of_le_of_ne (Nat.lt_succ_iff.mp h2) (hno u v h1)⟩
  · exact agPre_mono

/-- The placement step **fires**: the partial graph gains exactly the
pair `{u, w}`. -/
theorem agPre_succ_place {N : ℕ} (H : SimpleGraph (Fin N)) {u w : Fin N}
    (hwu : (w : ℕ) < (u : ℕ)) (hadj : H.Adj u w) (a b : Fin N) :
    (agPre H ((u : ℕ) * N + (w : ℕ) + 1)).Adj a b ↔
      (agPre H ((u : ℕ) * N + (w : ℕ))).Adj a b ∨
        ((a = u ∧ b = w) ∨ (a = w ∧ b = u)) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr (agKey_pair (H.ne_of_adj h1) h)
  · rintro (h | h)
    · exact agPre_mono h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hadj, by rw [agKey_of_lt hwu]; exact Nat.lt_succ_self _⟩
      · exact ⟨hadj.symm, by
          rw [agKey_symm, agKey_of_lt hwu]; exact Nat.lt_succ_self _⟩

/-! ### The offset function and the partial region -/

/-- The degree-sum offsets of the built graph — `DelAdjSt`'s own
offset function, in closed form. -/
noncomputable def agOffF {N : ℕ} (H : SimpleGraph (Fin N)) (i : ℕ) : ℕ :=
  ∑ t ∈ Finset.range i, baseDeg H t

theorem agOffF_zero {N : ℕ} (H : SimpleGraph (Fin N)) : agOffF H 0 = 0 := by
  simp [agOffF]

theorem agOffF_succ {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) :
    agOffF H ((v : ℕ) + 1) = agOffF H (v : ℕ) + (H.neighborSet v).ncard := by
  rw [agOffF, agOffF, Finset.sum_range_succ, baseDeg_eq]

theorem agOffF_step {N : ℕ} (H : SimpleGraph (Fin N)) (i : ℕ) :
    agOffF H (i + 1) = agOffF H i + baseDeg H i := by
  rw [agOffF, agOffF, Finset.sum_range_succ]

theorem agOffF_mono {N : ℕ} (H : SimpleGraph (Fin N)) {i k : ℕ} (h : i ≤ k) :
    agOffF H i ≤ agOffF H k := by
  have hsub : Finset.range i ⊆ Finset.range k := Finset.range_subset_range.mpr h
  exact Finset.sum_le_sum_of_subset hsub

theorem agOffF_last {N : ℕ} (H : SimpleGraph (Fin N)) :
    agOffF H N = nsOf H := rfl

theorem agOffF_le_sq {N : ℕ} (H : SimpleGraph (Fin N)) {i : ℕ} (hi : i ≤ N) :
    agOffF H i ≤ N * N := by
  refine le_trans (agOffF_mono H hi) ?_
  rw [agOffF_last]
  exact nsOf_le H

/-- A live slot of a row sits inside that row's extent. -/
theorem agOffF_slot {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) {t : ℕ}
    (ht : t < (H.neighborSet v).ncard) :
    agOffF H (v : ℕ) + t < agOffF H ((v : ℕ) + 1) := by
  rw [agOffF_succ]; omega

/-- **The partial deletable region**: `DelAdjSt`'s degree, slot and
completeness clauses read against a *sub*graph `Hk` of the graph `H`
whose degree sums fix the offsets. At `Hk = H` it is the region. -/
def agPart (aj dg mt : String) {N : ℕ} (H Hk : SimpleGraph (Fin N))
    (σ : Env) : Prop :=
  (∀ v : Fin N, (σ.arrs dg).getD (v : ℕ) 0 = (Hk.neighborSet v).ncard) ∧
  (∀ v : Fin N, ∀ t : ℕ, t < (σ.arrs dg).getD (v : ℕ) 0 →
      ∃ w : Fin N, Hk.Adj v w ∧
        (σ.arrs aj).getD (agOffF H (v : ℕ) + t) 0 = (w : ℕ) ∧
        ∃ s : ℕ, s < (σ.arrs dg).getD (w : ℕ) 0 ∧
          (σ.arrs mt).getD (agOffF H (v : ℕ) + t) 0 = agOffF H (w : ℕ) + s ∧
          (σ.arrs aj).getD (agOffF H (w : ℕ) + s) 0 = (v : ℕ) ∧
          (σ.arrs mt).getD (agOffF H (w : ℕ) + s) 0 = agOffF H (v : ℕ) + t) ∧
  (∀ v w : Fin N, Hk.Adj v w → ∃ t : ℕ, t < (σ.arrs dg).getD (v : ℕ) 0 ∧
      (σ.arrs aj).getD (agOffF H (v : ℕ) + t) 0 = (w : ℕ))

/-- Sub-degrees never exceed the offsets' degrees. -/
theorem agSub_ncard_le {N : ℕ} {H Hk : SimpleGraph (Fin N)}
    (hsub : ∀ u v : Fin N, Hk.Adj u v → H.Adj u v) (v : Fin N) :
    (Hk.neighborSet v).ncard ≤ (H.neighborSet v).ncard :=
  Set.ncard_le_ncard (fun _ hw => hsub v _ hw) (Set.toFinite _)

open Classical in
/-- **The bridge**: the partial region at the full graph, together with
the offsets in `ao` and the two slot allocations, *is* the deletable
adjacency region at the empty deleted set. -/
theorem agDelAdjSt_of_part {ao aj dg mt : String} {N : ℕ}
    {H : SimpleGraph (Fin N)} {σ : Env}
    (hpart : agPart aj dg mt H H σ)
    (haoL : N + 1 ≤ (σ.arrs ao).length)
    (haoV : ∀ i, i ≤ N → (σ.arrs ao).getD i 0 = agOffF H i)
    (hajL : nsOf H ≤ (σ.arrs aj).length)
    (hmtL : nsOf H ≤ (σ.arrs mt).length)
    (hdgL : N ≤ (σ.arrs dg).length) :
    DelAdjSt ao aj dg mt H ∅ σ := by
  obtain ⟨hdeg, hsound, hcomp⟩ := hpart
  refine ⟨agOffF H, agOffF_zero H, agOffF_succ H, haoL, haoV, hajL, hmtL,
    hdgL, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact absurd hv (Set.notMem_empty v)
  · intro v _
    rw [hdeg v, Impl.deleteVerts_empty]
  · intro v _ t ht
    obtain ⟨w, hadj, hval, s, hs, hm1, hm2, hm3⟩ := hsound v t ht
    exact ⟨w, by rw [Impl.deleteVerts_empty]; exact hadj, hval, s, hs, hm1,
      hm2, hm3⟩
  · intro v _ w hw
    rw [Impl.deleteVerts_empty] at hw
    exact hcomp v w hw

/-! ## §3 List plumbing, branchless predicates, and the two scan rules -/

private theorem agGetElem?_of_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem h]

private theorem agGetD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) :
    (l.set i v).getD i 0 = v := by
  rw [getD_eq_getElem (by simpa using h), List.getElem_set]
  simp

private theorem agGetD_set_ne {l : List ℕ} {i k v : ℕ} (h : i ≠ k) :
    (l.set i v).getD k 0 = l.getD k 0 := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · rw [getD_eq_getElem (by simpa using hk), getD_eq_getElem hk,
      List.getElem_set, if_neg h]
  · rw [List.getD_eq_default _ _ (by simpa using hk),
      List.getD_eq_default _ _ (by simpa using hk)]

@[simp] theorem agVs_self (σ : Env) (x : String) (n : ℕ) :
    (σ.setVar x n).vars x = n := by simp [Env.setVar]

theorem agVs_ne (σ : Env) {x y : String} (h : y ≠ x) (n : ℕ) :
    (σ.setVar x n).vars y = σ.vars y := by simp [Env.setVar, h]

@[simp] theorem agVs_arrs (σ : Env) (x : String) (n : ℕ) (a : String) :
    (σ.setVar x n).arrs a = σ.arrs a := rfl

@[simp] theorem agAs_vars (σ : Env) (a : String) (i n : ℕ) (y : String) :
    (σ.setArr a i n).vars y = σ.vars y := rfl

@[simp] theorem agAs_self (σ : Env) (a : String) (i n : ℕ) :
    (σ.setArr a i n).arrs a = (σ.arrs a).set i n := by simp [Env.setArr]

theorem agAs_ne (σ : Env) {a b : String} (h : b ≠ a) (i n : ℕ) :
    (σ.setArr a i n).arrs b = σ.arrs b := by simp [Env.setArr, h]

/-! ### Branchless predicates

Every comparison the passes need is truncated-subtraction arithmetic
on `0/1` cells, so no pass but the placement needs a conditional at
all — and the placement needs exactly one. -/

/-- `agBit (m ≤ n)`, as an expression. -/
def agLeE (e f : Expr) : Expr := .sub (.lit 1) (.sub e f)
/-- `agBit (m < n)`, as an expression. -/
def agLtE (e f : Expr) : Expr := .sub (.lit 1) (.sub (.add e (.lit 1)) f)
/-- `agBit (m = n)`, as an expression. -/
def agEqE (e f : Expr) : Expr := .sub (.sub (.lit 1) (.sub e f)) (.sub f e)

theorem agNum_le (a b : ℕ) : 1 - (a - b) = agBit (a ≤ b) := by
  by_cases h : a ≤ b
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

theorem agNum_lt (a b : ℕ) : 1 - (a + 1 - b) = agBit (a < b) := by
  by_cases h : a < b
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

theorem agNum_eq (a b : ℕ) : 1 - (a - b) - (b - a) = agBit (a = b) := by
  by_cases h : a = b
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

theorem agNum_not {x : ℕ} {p : Prop} (h : x = agBit p) : 1 - x = agBit (¬ p) := by
  classical
  by_cases hp : p
  · rw [agBit_pos hp] at h; rw [agBit_neg (not_not_intro hp), h]
  · rw [agBit_neg hp] at h; rw [agBit_pos hp, h]

theorem agNum_and {x y : ℕ} {p q : Prop} (hx : x = agBit p) (hy : y = agBit q) :
    x * y = agBit (p ∧ q) := by rw [hx, hy, agBit_mul]

theorem agNum_or {x y : ℕ} {p q : Prop} (hx : x = agBit p) (hy : y = agBit q) :
    1 - (1 - x) * (1 - y) = agBit (p ∨ q) := by
  classical
  subst hx; subst hy
  by_cases hp : p <;> by_cases hq : q <;> simp [agBit, hp, hq]

theorem agNum_gt_zero (c : ℕ) : 1 - (1 - c) = agBit (0 < c) := by
  by_cases h : 0 < c
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

theorem agEvalSub {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m - n < B) :
    (Expr.sub e f).evalB B σ = some (m - n) :=
  evalB_bin (op := .sub) he hf h

theorem agEvalAdd {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m + n < B) :
    (Expr.add e f).evalB B σ = some (m + n) :=
  evalB_bin (op := .add) he hf h

theorem agEvalMul {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m * n < B) :
    (Expr.mul e f).evalB B σ = some (m * n) :=
  evalB_bin (op := .mul) he hf h

theorem agEvalDiv {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m / n < B) :
    (Expr.div e f).evalB B σ = some (m / n) :=
  evalB_bin (op := .div) he hf h

theorem agEval_leE {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (hmB : m < B)
    (h1B : 1 < B) : (agLeE e f).evalB B σ = some (agBit (m ≤ n)) := by
  have hs := agEvalSub he hf (by omega)
  rw [agLeE, ← agNum_le m n]
  exact agEvalSub (evalB_lit (B := B) (n := 1) h1B) hs (by omega)

theorem agEval_ltE {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (hmB : m + 1 < B)
    (h1B : 1 < B) : (agLtE e f).evalB B σ = some (agBit (m < n)) := by
  have ha := agEvalAdd he (evalB_lit (B := B) (n := 1) h1B) (by omega)
  have hs := agEvalSub ha hf (by omega)
  rw [agLtE, ← agNum_lt m n]
  exact agEvalSub (evalB_lit (B := B) (n := 1) h1B) hs (by omega)

theorem agEval_eqE {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (hmB : m < B)
    (hnB : n < B) (h1B : 1 < B) :
    (agEqE e f).evalB B σ = some (agBit (m = n)) := by
  have hs1 := agEvalSub he hf (by omega)
  have hs2 := agEvalSub hf he (by omega)
  have hs3 := agEvalSub (evalB_lit (B := B) (n := 1) h1B) hs1 (by omega)
  rw [agEqE, ← agNum_eq m n]
  exact agEvalSub hs3 hs2 (by omega)

/-! ### The two scan rules -/

/-- **The accumulate scan**: `av := 0; wv := 0; while wv < nm do
(av := av + e; wv := wv + 1)`. The summand `e` is evaluated at the
entry state's arrays and scalars with only the counter moved, which is
exactly what an inner scan sees. -/
private theorem agSumRun {B : ℕ} (L : ℕ) (av wv nm : String) (e : Expr)
    (Gf : ℕ → ℕ) (hav_wv : av ≠ wv) (hav_nm : av ≠ nm) (hwv_nm : wv ≠ nm)
    (hLB : L < B) (h1B : 1 < B)
    (hbnd : ∀ k, k ≤ L → (∑ i ∈ Finset.range k, Gf i) < B)
    (σ : Env) (hn : σ.vars nm = L)
    (he : ∀ τ : Env, (∀ a, τ.arrs a = σ.arrs a) →
        (∀ y, y ≠ av → y ≠ wv → τ.vars y = σ.vars y) → τ.vars wv < L →
        e.evalB B τ = some (Gf (τ.vars wv))) :
    ∃ σ', Run B (.seq (.assign av (.lit 0))
             (.seq (.assign wv (.lit 0))
               (.while (.lt (.var wv) (.var nm))
                 (.seq (.assign av (.add (.var av) e))
                   (.assign wv (.add (.var wv) (.lit 1)))))))
           σ σ' ((e.size + 11) * L + 8) ∧
      σ'.vars av = ∑ i ∈ Finset.range L, Gf i ∧
      (∀ y, y ≠ av → y ≠ wv → σ'.vars y = σ.vars y) ∧
      (∀ a, σ'.arrs a = σ.arrs a) := by
  set I : Env → Prop := fun τ => τ.vars wv ≤ L ∧
    τ.vars av = ∑ i ∈ Finset.range (τ.vars wv), Gf i ∧
    (∀ y, y ≠ av → y ≠ wv → τ.vars y = σ.vars y) ∧
    (∀ a, τ.arrs a = σ.arrs a) with hI_def
  have hbody : Spec B (fun τ => I τ ∧ τ.vars wv < L)
      (.seq (.assign av (.add (.var av) e))
        (.assign wv (.add (.var wv) (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars wv = τ.vars wv + 1) (e.size + 7) := by
    refine Spec.of_exists fun τ hτ => ?_
    obtain ⟨⟨hle, hsum, hfv, hfa⟩, hlt⟩ := hτ
    have hnext : (∑ i ∈ Finset.range (τ.vars wv + 1), Gf i) < B :=
      hbnd (τ.vars wv + 1) (by omega)
    have hstep : (∑ i ∈ Finset.range (τ.vars wv + 1), Gf i)
        = (∑ i ∈ Finset.range (τ.vars wv), Gf i) + Gf (τ.vars wv) :=
      Finset.sum_range_succ _ _
    have hcur : τ.vars av < B := by rw [hsum]; omega
    have hev := he τ hfa hfv hlt
    have hadd : (Expr.add (.var av) e).evalB B τ
        = some (τ.vars av + Gf (τ.vars wv)) :=
      agEvalAdd (evalB_var (B := B) hcur) hev (by rw [hsum]; omega)
    have h1 : Run B (.assign av (.add (.var av) e)) τ
        (τ.setVar av (τ.vars av + Gf (τ.vars wv))) (e.size + 3) :=
      (Run.assign hadd).mono (by simp [Expr.size]; omega)
    have hτ₁w : (τ.setVar av (τ.vars av + Gf (τ.vars wv))).vars wv = τ.vars wv :=
      agVs_ne τ (Ne.symm hav_wv) _
    have h2 : Run B (.assign wv (.add (.var wv) (.lit 1)))
        (τ.setVar av (τ.vars av + Gf (τ.vars wv)))
        ((τ.setVar av (τ.vars av + Gf (τ.vars wv))).setVar wv (τ.vars wv + 1))
        4 := by
      refine (Run.assign ?_).mono (by simp [Expr.size])
      have hv := evalB_var (B := B)
        (x := wv) (σ := τ.setVar av (τ.vars av + Gf (τ.vars wv)))
        (by rw [hτ₁w]; omega)
      rw [hτ₁w] at hv
      exact agEvalAdd hv (evalB_lit (B := B) (n := 1) h1B) (by omega)
    refine ⟨_, e.size + 7, (h1.seq h2).mono (by omega), le_rfl,
      ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [agVs_self]; omega
    · rw [agVs_self, agVs_ne _ hav_wv, agVs_self, hstep, hsum]
    · intro y hy1 hy2
      rw [agVs_ne _ hy2, agVs_ne _ hy1]
      exact hfv y hy1 hy2
    · intro a
      rw [agVs_arrs, agVs_arrs]
      exact hfa a
    · rw [agVs_self]
  have hloop := Spec.forRangeZero (B := B) wv nm I L (e.size + 7) hLB
    (fun τ hτ => hτ.1)
    (fun τ hτ => by
      rw [hτ.2.2.1 nm (Ne.symm hav_nm) (Ne.symm hwv_nm), hn])
    hbody
  have hstart : I ((σ.setVar av 0).setVar wv 0) := by
    refine ⟨by rw [agVs_self]; omega, ?_, ?_, ?_⟩
    · rw [agVs_self, agVs_ne _ hav_wv, agVs_self]
      simp
    · intro y hy1 hy2
      simp [Env.setVar, hy1, hy2]
    · intro a
      rw [agVs_arrs, agVs_arrs]
  obtain ⟨σ', hrun, hI', hwL⟩ := hloop.run hstart
  have hassign : Run B (.assign av (.lit 0)) σ (σ.setVar av 0) 2 :=
    (Run.assign (evalB_lit (B := B) (n := 0) (by omega))).mono (by simp [Expr.size])
  refine ⟨σ', (hassign.seq hrun).mono (le_of_eq (by ring)), ?_, ?_, ?_⟩
  · rw [hI'.2.1, hwL]
  · intro y hy1 hy2
    exact hI'.2.2.1 y hy1 hy2
  · intro a
    exact hI'.2.2.2 a

/-- **The store scan**: `pv := 0; while pv < nm do (bodyCore; pv := pv + 1)`,
where one turn of `bodyCore` writes the single array `dst` at the
counter's own cell and nothing else outside the scratch list `VS`.
Every flat pass of the file is an instance. -/
private theorem agScanRun {B : ℕ} (L Kb : ℕ) (dst : String) (VS : List String)
    (pv nm : String) (bodyCore : Com) (Ff : ℕ → ℕ)
    (hpv : pv ∈ VS) (hnm : nm ∉ VS) (hLB : L < B)
    (σ : Env) (hn : σ.vars nm = L) (hlen : L ≤ (σ.arrs dst).length)
    (hbody : ∀ τ : Env, τ.vars pv < L → (∀ y, y ∉ VS → τ.vars y = σ.vars y) →
        (∀ a, a ≠ dst → τ.arrs a = σ.arrs a) →
        (τ.arrs dst).length = (σ.arrs dst).length →
        (∀ p, p < τ.vars pv → (τ.arrs dst).getD p 0 = Ff p) →
        ∃ τ', Run B bodyCore τ τ' Kb ∧
          (∀ y, y ∉ VS → τ'.vars y = τ.vars y) ∧ τ'.vars pv = τ.vars pv ∧
          (∀ a, a ≠ dst → τ'.arrs a = τ.arrs a) ∧
          τ'.arrs dst = (τ.arrs dst).set (τ.vars pv) (Ff (τ.vars pv))) :
    ∃ σ', Run B (.seq (.assign pv (.lit 0))
              (.while (.lt (.var pv) (.var nm))
                (.seq bodyCore (.assign pv (.add (.var pv) (.lit 1)))))) σ σ'
            ((Kb + 8) * L + 6) ∧
      (∀ y, y ∉ VS → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ dst → σ'.arrs a = σ.arrs a) ∧
      (σ'.arrs dst).length = (σ.arrs dst).length ∧
      (∀ p, p < L → (σ'.arrs dst).getD p 0 = Ff p) := by
  set I : Env → Prop := fun τ => (∀ y, y ∉ VS → τ.vars y = σ.vars y) ∧
    (∀ a, a ≠ dst → τ.arrs a = σ.arrs a) ∧
    (τ.arrs dst).length = (σ.arrs dst).length ∧ τ.vars pv ≤ L ∧
    (∀ p, p < τ.vars pv → (τ.arrs dst).getD p 0 = Ff p) with hI_def
  have hbodyS : Spec B (fun τ => I τ ∧ τ.vars pv < L)
      (.seq bodyCore (.assign pv (.add (.var pv) (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars pv = τ.vars pv + 1) (Kb + 4) := by
    refine Spec.of_exists fun τ hτ => ?_
    obtain ⟨⟨hfv, hfa, hdl, hple, hpre⟩, hlt⟩ := hτ
    obtain ⟨τ₁, hr1, hfv1, hp1, hfa1, hd1⟩ := hbody τ hlt hfv hfa hdl hpre
    have hkB : τ.vars pv + 1 < B := by omega
    have h2 : Run B (.assign pv (.add (.var pv) (.lit 1))) τ₁
        (τ₁.setVar pv (τ.vars pv + 1)) 4 := by
      refine (Run.assign ?_).mono (by simp [Expr.size])
      have hv := evalB_var (B := B) (x := pv) (σ := τ₁) (by rw [hp1]; omega)
      rw [hp1] at hv
      exact agEvalAdd hv (evalB_lit (B := B) (n := 1) (by omega)) (by omega)
    have hklen : τ.vars pv < (τ.arrs dst).length := by omega
    refine ⟨τ₁.setVar pv (τ.vars pv + 1), Kb + 4, (hr1.seq h2).mono (by omega),
      le_rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro y hy
      have hne : y ≠ pv := fun hc => hy (hc ▸ hpv)
      rw [agVs_ne _ hne, hfv1 y hy]
      exact hfv y hy
    · intro a ha
      rw [agVs_arrs, hfa1 a ha]
      exact hfa a ha
    · rw [agVs_arrs, hd1, List.length_set]
      exact hdl
    · rw [agVs_self]; omega
    · intro p hp
      rw [agVs_self] at hp
      rw [agVs_arrs, hd1]
      rcases Nat.lt_or_ge p (τ.vars pv) with hlt' | hge'
      · rw [agGetD_set_ne (by omega)]
        exact hpre p hlt'
      · obtain rfl : p = τ.vars pv := by omega
        exact agGetD_set_self hklen
    · rw [agVs_self]
  have hloop := Spec.forRangeZero (B := B) pv nm I L (Kb + 4) hLB
    (fun τ hτ => hτ.2.2.2.1)
    (fun τ hτ => by rw [hτ.1 nm hnm, hn])
    hbodyS
  have hstart : I (σ.setVar pv 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      have hne : y ≠ pv := fun hc => hy (hc ▸ hpv)
      rw [agVs_ne _ hne]
    · intro a _; rw [agVs_arrs]
    · rw [agVs_arrs]
    · rw [agVs_self]; omega
    · intro p hp
      rw [agVs_self] at hp
      exact absurd hp (Nat.not_lt_zero _)
  obtain ⟨σ', hrun, hI', hpL⟩ := hloop.run hstart
  exact ⟨σ', hrun.mono (le_of_eq (by ring)), hI'.1, hI'.2.1, hI'.2.2.1,
    fun p hp => hI'.2.2.2.2 p (by omega)⟩

/-! ## §4 The programs -/

/-- `agBit (x = 0)`, arithmetically: truncated `1 - x`. -/
theorem agNum_zero (x : ℕ) : 1 - x = agBit (x = 0) := by
  by_cases h : x = 0
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

/-- The scan wrapper every flat pass shares: set the bound cell from
`be`, then run the counted store scan. -/
def agBndCom (be : Expr) (bodyCore : Com) (pv qv : String) : Com :=
  .seq (.assign qv be)
    (.seq (.assign pv (.lit 0))
      (.while (.lt (.var pv) (.var qv))
        (.seq bodyCore (.assign pv (.add (.var pv) (.lit 1))))))

/-- The inner accumulate loop every pass with a witness scan shares. -/
def agAccCom (av wv nm : String) (e : Expr) : Com :=
  .seq (.assign av (.lit 0))
    (.seq (.assign wv (.lit 0))
      (.while (.lt (.var wv) (.var nm))
        (.seq (.assign av (.add (.var av) e))
          (.assign wv (.add (.var wv) (.lit 1))))))

/-- Decode the flat pair index into its two endpoints. -/
def agDecCom (pv uv vv nN : String) : Com :=
  .seq (.assign uv (.div (.var pv) (.var nN)))
    (.assign vv (.sub (.var pv) (.mul (.var uv) (.var nN))))

/-! ### Pass 1 — the arena's CSR into a dense matrix -/

/-- The summand of the CSR probe: slot `w` is inside `u`'s row window
and holds `v`. -/
def agGrE (o t uv vv wv : String) : Expr :=
  .mul (.mul (agLeE (.get o (.var uv)) (.var wv))
      (agLtE (.var wv) (.get o (.add (.var uv) (.lit 1)))))
    (agEqE (.get t (.var wv)) (.var vv))

/-- One turn: decode the pair, probe the slot space, write the bit. -/
def agGrBody (o t gm pv uv vv wv av nN nS : String) : Com :=
  .seq (agDecCom pv uv vv nN)
    (.seq (agAccCom av wv nS (agGrE o t uv vv wv))
      (.store gm (.var pv) (.sub (.lit 1) (.sub (.lit 1) (.var av)))))

/-- **Pass 1**: the arena graph, as a dense matrix. -/
def agGrCom (o t gm pv uv vv wv av qv nN nS : String) : Com :=
  agBndCom (.mul (.var nN) (.var nN)) (agGrBody o t gm pv uv vv wv av nN nS)
    pv qv

/-! ### Pass 2 — the builder -/

/-- One turn of the offsets pass: `ao[v]` is the number of set cells
of the matrix strictly before row `v`. -/
def agOffBody (m ao pv wv av rv nN : String) : Com :=
  .seq (.assign rv (.mul (.var pv) (.var nN)))
    (.seq (agAccCom av wv rv (.get m (.var wv)))
      (.store ao (.var pv) (.var av)))

/-- **Builder pass a**: the degree-sum offsets. -/
def agOffCom (m ao pv wv av rv qv nN : String) : Com :=
  agBndCom (.add (.var nN) (.lit 1)) (agOffBody m ao pv wv av rv nN) pv qv

/-- **Builder pass b**: the row cursors, zeroed. -/
def agDgZCom (dg pv nN : String) : Com :=
  .seq (.assign pv (.lit 0))
    (.while (.lt (.var pv) (.var nN))
      (.seq (.store dg (.var pv) (.lit 0))
        (.assign pv (.add (.var pv) (.lit 1)))))

/-- The placement block: both directed copies of the edge `{u, w}` at
their rows' cursors, the two mate pointers crossed, both cursors
bumped. All four positions are read before either cursor moves. -/
def agPlaceStore (ao aj dg mt uv wv : String) : Com :=
  .seq (.store aj (.add (.get ao (.var uv)) (.get dg (.var uv))) (.var wv))
    (.seq (.store aj (.add (.get ao (.var wv)) (.get dg (.var wv))) (.var uv))
      (.seq (.store mt (.add (.get ao (.var uv)) (.get dg (.var uv)))
          (.add (.get ao (.var wv)) (.get dg (.var wv))))
        (.seq (.store mt (.add (.get ao (.var wv)) (.get dg (.var wv)))
            (.add (.get ao (.var uv)) (.get dg (.var uv))))
          (.seq (.store dg (.var uv) (.add (.get dg (.var uv)) (.lit 1)))
            (.store dg (.var wv) (.add (.get dg (.var wv)) (.lit 1)))))))

/-- One turn of the placement scan: decode, and place iff the pair is
an edge taken at its larger endpoint. The file's only conditional. -/
def agPlaceBody (m ao aj dg mt pv uv wv nN : String) : Com :=
  .seq (agDecCom pv uv wv nN)
    (.ite (.lt (.lit 0) (.mul (.get m (.var pv)) (agLtE (.var wv) (.var uv))))
      (agPlaceStore ao aj dg mt uv wv) .skip)

/-- **Builder pass c**: the counting-trick placement. -/
def agPlaceCom (m ao aj dg mt pv uv wv qv nN : String) : Com :=
  agBndCom (.mul (.var nN) (.var nN)) (agPlaceBody m ao aj dg mt pv uv wv nN)
    pv qv

/-- **The shared builder**: a dense symmetric irreflexive matrix into
the deletable adjacency region at the empty deleted set. -/
def agBldCom (m ao aj dg mt pv uv wv av rv qv nN : String) : Com :=
  .seq (agOffCom m ao pv wv av rv qv nN)
    (.seq (agDgZCom dg pv nN) (agPlaceCom m ao aj dg mt pv uv wv qv nN))

/-! ### Passes 3–7 — the chain -/

/-- **The base orientation**: an arc `u → v` for every edge running up
the rank. -/
def agBaseBody (gm ra arc pv uv vv nN : String) : Com :=
  .seq (agDecCom pv uv vv nN)
    (.store arc (.var pv)
      (.mul (.get gm (.var pv))
        (agLtE (.get ra (.var uv)) (.get ra (.var vv)))))

def agBaseCom (gm ra arc pv uv vv qv nN : String) : Com :=
  agBndCom (.mul (.var nN) (.var nN)) (agBaseBody gm ra arc pv uv vv nN) pv qv

/-- The fraternal summand: `u → w ← v`. -/
def agFratE (arc uv vv wv nN : String) : Expr :=
  .mul (.get arc (.add (.mul (.var uv) (.var nN)) (.var wv)))
    (.get arc (.add (.mul (.var vv) (.var nN)) (.var wv)))

/-- The transitive summand: `u → w → v`. -/
def agTransE (arc uv vv wv nN : String) : Expr :=
  .mul (.get arc (.add (.mul (.var uv) (.var nN)) (.var wv)))
    (.get arc (.add (.mul (.var wv) (.var nN)) (.var vv)))

/-- **The round's fraternity graph**, as a dense matrix. -/
def agFratBody (arc fm pv uv vv wv av nN : String) : Com :=
  .seq (agDecCom pv uv vv nN)
    (.seq (agAccCom av wv nN (agFratE arc uv vv wv nN))
      (.store fm (.var pv)
        (.mul (.sub (.lit 1) (agEqE (.var uv) (.var vv)))
          (.sub (.lit 1) (.sub (.lit 1) (.var av))))))

def agFratCom (arc fm pv uv vv wv av qv nN : String) : Com :=
  agBndCom (.mul (.var nN) (.var nN)) (agFratBody arc fm pv uv vv wv av nN)
    pv qv

/-- The greedy step's stored value, `mem_greedyStep` clause by clause:
the old arc, plus — when the pair is not yet adjacent, is demanded, and
the direction is either rank-forward or the only tight one — a new
arc. -/
def agStepE (arc ra pv uv vv av bv cv nN : String) : Expr :=
  .add (.get arc (.var pv))
    (.mul
      (.mul
        (.sub (.lit 1)
          (.add (.get arc (.var pv))
            (.get arc (.add (.mul (.var vv) (.var nN)) (.var uv)))))
        (.sub (.lit 1) (.sub (.lit 1) (.add (.var av) (.var cv)))))
      (.sub (.lit 1)
        (.mul (.sub (.lit 1) (agLtE (.get ra (.var uv)) (.get ra (.var vv))))
          (.sub (.lit 1) (.sub (.lit 1) (.add (.var bv) (.var cv)))))))

/-- **The greedy round**: three witness scans, then the step. -/
def agStepBody (arc arc2 ra pv uv vv wv av bv cv nN : String) : Com :=
  .seq (agDecCom pv uv vv nN)
    (.seq (agAccCom av wv nN (agTransE arc uv vv wv nN))
      (.seq (agAccCom bv wv nN (agTransE arc vv uv wv nN))
        (.seq (agAccCom cv wv nN (agFratE arc uv vv wv nN))
          (.store arc2 (.var pv) (agStepE arc ra pv uv vv av bv cv nN)))))

def agStepCom (arc arc2 ra pv uv vv wv av bv cv qv nN : String) : Com :=
  agBndCom (.mul (.var nN) (.var nN))
    (agStepBody arc arc2 ra pv uv vv wv av bv cv nN) pv qv

/-- **The symmetrization** `.toGraph`: adjacent iff an arc runs either
way. -/
def agSymBody (arc sm pv uv vv nN : String) : Com :=
  .seq (agDecCom pv uv vv nN)
    (.store sm (.var pv)
      (.sub (.lit 1) (.sub (.lit 1)
        (.add (.get arc (.var pv))
          (.get arc (.add (.mul (.var vv) (.var nN)) (.var uv)))))))

def agSymCom (arc sm pv uv vv qv nN : String) : Com :=
  agBndCom (.mul (.var nN) (.var nN)) (agSymBody arc sm pv uv vv nN) pv qv

/-- The buffer swap closing a round. -/
def agCopyCom (src dst pv qv nN : String) : Com :=
  agBndCom (.mul (.var nN) (.var nN)) (.store dst (.var pv) (.get src (.var pv)))
    pv qv

/-! ### The bound-scan rule -/

/-- `agBndCom`'s run: the wrapper of `agScanRun` with the bound cell
computed from `be` first. -/
private theorem agBndRun {B : ℕ} (L Kb : ℕ) (dst : String) (VS : List String)
    (pv qv : String) (be : Expr) (bodyCore : Com) (Ff : ℕ → ℕ)
    (hpv : pv ∈ VS) (hqv : qv ∉ VS) (hLB : L < B)
    (σ : Env) (hbe : be.evalB B σ = some L) (hlen : L ≤ (σ.arrs dst).length)
    (hbody : ∀ τ : Env, τ.vars pv < L →
        (∀ y, y ∉ VS → y ≠ qv → τ.vars y = σ.vars y) →
        (∀ a, a ≠ dst → τ.arrs a = σ.arrs a) →
        (τ.arrs dst).length = (σ.arrs dst).length →
        (∀ p, p < τ.vars pv → (τ.arrs dst).getD p 0 = Ff p) →
        ∃ τ', Run B bodyCore τ τ' Kb ∧
          (∀ y, y ∉ VS → τ'.vars y = τ.vars y) ∧ τ'.vars pv = τ.vars pv ∧
          (∀ a, a ≠ dst → τ'.arrs a = τ.arrs a) ∧
          τ'.arrs dst = (τ.arrs dst).set (τ.vars pv) (Ff (τ.vars pv))) :
    ∃ σ', Run B (agBndCom be bodyCore pv qv) σ σ'
            ((Kb + 8) * L + 7 + be.size) ∧
      (∀ y, y ∉ VS → y ≠ qv → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ dst → σ'.arrs a = σ.arrs a) ∧
      (σ'.arrs dst).length = (σ.arrs dst).length ∧
      (∀ p, p < L → (σ'.arrs dst).getD p 0 = Ff p) := by
  have hset : Run B (.assign qv be) σ (σ.setVar qv L) (1 + be.size) :=
    Run.assign hbe
  obtain ⟨σ', hrun, hfv, hfa, hdl, hval⟩ :=
    agScanRun (B := B) L Kb dst VS pv qv bodyCore Ff hpv hqv hLB
      (σ.setVar qv L) (agVs_self _ _ _) (by rw [agVs_arrs]; exact hlen)
      (by
        intro τ hlt hfv' hfa' hdl' hpre'
        refine hbody τ hlt (fun y hy hy2 => ?_) (fun a ha => ?_) ?_ hpre'
        · rw [hfv' y hy, agVs_ne _ hy2]
        · rw [hfa' a ha, agVs_arrs]
        · rw [hdl', agVs_arrs])
  refine ⟨σ', (hset.seq hrun).mono (by omega), ?_, ?_, ?_, ?_⟩
  · intro y hy hy2
    rw [hfv y hy, agVs_ne _ hy2]
  · intro a ha
    rw [hfa a ha, agVs_arrs]
  · rw [hdl, agVs_arrs]
  · exact hval

/-- The `N`-bounded flat scan, at the carrier cell itself. -/
private theorem agNRun {B N : ℕ} (Kb : ℕ) (dst : String) (VS : List String)
    (pv nN : String) (bodyCore : Com) (Ff : ℕ → ℕ)
    (hpv : pv ∈ VS) (hnN : nN ∉ VS) (hNB : N < B)
    (σ : Env) (hn : σ.vars nN = N) (hlen : N ≤ (σ.arrs dst).length)
    (hbody : ∀ τ : Env, τ.vars pv < N → (∀ y, y ∉ VS → τ.vars y = σ.vars y) →
        (∀ a, a ≠ dst → τ.arrs a = σ.arrs a) →
        (τ.arrs dst).length = (σ.arrs dst).length →
        (∀ p, p < τ.vars pv → (τ.arrs dst).getD p 0 = Ff p) →
        ∃ τ', Run B bodyCore τ τ' Kb ∧
          (∀ y, y ∉ VS → τ'.vars y = τ.vars y) ∧ τ'.vars pv = τ.vars pv ∧
          (∀ a, a ≠ dst → τ'.arrs a = τ.arrs a) ∧
          τ'.arrs dst = (τ.arrs dst).set (τ.vars pv) (Ff (τ.vars pv))) :
    ∃ σ', Run B (.seq (.assign pv (.lit 0))
              (.while (.lt (.var pv) (.var nN))
                (.seq bodyCore (.assign pv (.add (.var pv) (.lit 1)))))) σ σ'
            ((Kb + 8) * N + 6) ∧
      (∀ y, y ∉ VS → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ dst → σ'.arrs a = σ.arrs a) ∧
      (σ'.arrs dst).length = (σ.arrs dst).length ∧
      (∀ p, p < N → (σ'.arrs dst).getD p 0 = Ff p) :=
  agScanRun (B := B) N Kb dst VS pv nN bodyCore Ff hpv hnN hNB σ hn hlen hbody

/-! ## §5 The level's names, and the decode step -/

/-- The bases of the pass's own scratch scalars. All length 4, the
`lv` mechanism's requirement. -/
def agBases : List String :=
  ["ag.p", "ag.u", "ag.v", "ag.w", "ag.a", "ag.b", "ag.c", "ag.r"]

def agPv (j : ℕ) : String := lv "ag.p" j
def agUv (j : ℕ) : String := lv "ag.u" j
def agVv (j : ℕ) : String := lv "ag.v" j
def agWv (j : ℕ) : String := lv "ag.w" j
def agAv (j : ℕ) : String := lv "ag.a" j
def agBv (j : ℕ) : String := lv "ag.b" j
def agCv (j : ℕ) : String := lv "ag.c" j
def agRv (j : ℕ) : String := lv "ag.r" j
/-- The loop-bound cell: never written by a scan body. -/
def agQv (j : ℕ) : String := lv "ag.q" j

/-- The scalars a scan body may write. -/
def agVS (j : ℕ) : List String := agBases.map (lv · j)

/-- Two distinct four-character bases stay distinct at a level. -/
theorem agNeq {s t : String} (hs : s.length = 4) (ht : t.length = 4)
    (h : s ≠ t) (j : ℕ) : lv s j ≠ lv t j :=
  lv_ne_of_base_ne (hs.trans ht.symm) h j j

theorem agPv_mem (j : ℕ) : agPv j ∈ agVS j :=
  List.mem_map.mpr ⟨"ag.p", by decide, rfl⟩

theorem agQv_notMem (j : ℕ) : agQv j ∉ agVS j :=
  lv_notMem (s := "ag.q") (bases := agBases) j (by decide) (by decide)

theorem agNn_notMem (j : ℕ) : (arenaNames j).nN ∉ agVS j :=
  lv_notMem (s := "sv.n") (bases := agBases) j (by decide) (by decide)

theorem agNs_notMem (j : ℕ) : (arenaNames j).nS ∉ agVS j :=
  lv_notMem (s := "sv.m") (bases := agBases) j (by decide) (by decide)

/-- The full scalar family of the level, pairwise distinct: the eight
scratch cells, the bound cell, the eleven peel cells and the arena's
two. -/
theorem agScalars_nodup (j : ℕ) :
    ([agPv j, agUv j, agVv j, agWv j, agAv j, agBv j, agCv j, agRv j,
      agQv j, (arenaNames j).nN, (arenaNames j).nS] : List String).Nodup := by
  have h := nodup_lv ["ag.p", "ag.u", "ag.v", "ag.w", "ag.a", "ag.b", "ag.c",
    "ag.r", "ag.q", "sv.n", "sv.m"] j (by decide) (by decide)
  simpa [agPv, agUv, agVv, agWv, agAv, agBv, agCv, agRv, agQv, arenaNames]
    using h

/-- **The decode step**: the flat pair index into its quotient and
remainder, which are the pair's two endpoints. -/
private theorem agDecRun {B N : ℕ} (pv uv vv nN : String)
    (hup : uv ≠ pv) (hun : uv ≠ nN) (hsqB : N * N < B) (τ : Env) (hn : τ.vars nN = N)
    (hp : τ.vars pv < N * N) :
    Run B (agDecCom pv uv vv nN) τ
      ((τ.setVar uv (τ.vars pv / N)).setVar vv (τ.vars pv % N)) 10 := by
  obtain ⟨hdiv, hmod, hsplit⟩ := agDecode hp
  have hpB : τ.vars pv < B := by omega
  have hNB : N < B := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · omega
    · calc N ≤ N * N := Nat.le_mul_of_pos_left N hN
        _ < B := hsqB
  have h1 : Run B (.assign uv (.div (.var pv) (.var nN))) τ
      (τ.setVar uv (τ.vars pv / N)) 4 := by
    refine (Run.assign ?_).mono (by simp [Expr.size])
    have hv := evalB_var (B := B) (x := nN) (σ := τ) (by rw [hn]; omega)
    rw [hn] at hv
    exact agEvalDiv (evalB_var (B := B) hpB) hv (by omega)
  set τ₁ := τ.setVar uv (τ.vars pv / N) with hτ₁
  have hτ₁p : τ₁.vars pv = τ.vars pv := agVs_ne _ (Ne.symm hup) _
  have hτ₁n : τ₁.vars nN = N := by rw [hτ₁, agVs_ne _ (Ne.symm hun), hn]
  have hτ₁u : τ₁.vars uv = τ.vars pv / N := agVs_self _ _ _
  have hmul : τ.vars pv / N * N ≤ τ.vars pv := by omega
  have h2 : Run B (.assign vv (.sub (.var pv) (.mul (.var uv) (.var nN)))) τ₁
      (τ₁.setVar vv (τ.vars pv % N)) 6 := by
    refine (Run.assign ?_).mono (by simp [Expr.size])
    have hu := evalB_var (B := B) (x := uv) (σ := τ₁) (by rw [hτ₁u]; omega)
    have hnv := evalB_var (B := B) (x := nN) (σ := τ₁) (by rw [hτ₁n]; omega)
    rw [hτ₁u] at hu
    rw [hτ₁n] at hnv
    have hm := agEvalMul hu hnv (by omega)
    have hpe := evalB_var (B := B) (x := pv) (σ := τ₁) (by rw [hτ₁p]; omega)
    rw [hτ₁p] at hpe
    have := agEvalSub hpe hm (by omega)
    rw [show τ.vars pv - τ.vars pv / N * N = τ.vars pv % N by omega] at this
    exact this
  exact (h1.seq h2).mono (by omega)

/-! ## §6 Cell reads, and the store bodies -/

theorem agNum_or2 (p q : Prop) : 1 - (1 - (agBit p + agBit q)) = agBit (p ∨ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [agBit, hp, hq]

/-- The pair index decodes to its own endpoints. -/
theorem agDec_pair {N : ℕ} (u v : Fin N) :
    ((u : ℕ) * N + (v : ℕ)) / N = (u : ℕ) ∧
      ((u : ℕ) * N + (v : ℕ)) % N = (v : ℕ) := by
  obtain ⟨h1, h2, h3⟩ := agDecode (agPair_lt u v)
  exact agSplit h2 v.isLt h3

/-- Reading the cell of a flat index held in a scalar. -/
private theorem agEvalFlat {B : ℕ} (a pv : String) (ρ : Env) (k : ℕ)
    (hk : ρ.vars pv = k) (hkB : k < B) (hlen : k < (ρ.arrs a).length)
    (hval : (ρ.arrs a).getD k 0 < B) :
    (Expr.get a (.var pv)).evalB B ρ = some ((ρ.arrs a).getD k 0) := by
  refine evalB_get ?_ (agGetElem?_of_getD hlen) hval
  rw [← hk] at hkB ⊢
  exact evalB_var (B := B) hkB

/-- Reading the cell `x·N + y` of a dense matrix from two scalars. -/
private theorem agEvalCell {B N : ℕ} (a xv yv nN : String) (ρ : Env) (x y : ℕ)
    (hx : ρ.vars xv = x) (hy : ρ.vars yv = y) (hn : ρ.vars nN = N)
    (hxN : x < N) (hyN : y < N) (hsq : N * N < B)
    (hlen : N * N ≤ (ρ.arrs a).length)
    (hval : (ρ.arrs a).getD (x * N + y) 0 < B) :
    (Expr.get a (.add (.mul (.var xv) (.var nN)) (.var yv))).evalB B ρ
      = some ((ρ.arrs a).getD (x * N + y) 0) := by
  have hlt : x * N + y < N * N :=
    agPair_lt (⟨x, hxN⟩ : Fin N) (⟨y, hyN⟩ : Fin N)
  have hxv := evalB_var (B := B) (x := xv) (σ := ρ) (by rw [hx]; omega)
  have hnv := evalB_var (B := B) (x := nN) (σ := ρ) (by rw [hn]; omega)
  have hyv := evalB_var (B := B) (x := yv) (σ := ρ) (by rw [hy]; omega)
  rw [hx] at hxv
  rw [hn] at hnv
  rw [hy] at hyv
  have hm := agEvalMul hxv hnv (by omega)
  have ha := agEvalAdd hm hyv (by omega)
  exact evalB_get ha (agGetElem?_of_getD (by omega)) hval

/-- **The decode-and-store body**: the shape of every flat pass but the
placement. -/
private theorem agDecStoreRun {B N : ℕ} (dst pv uv vv nN : String) (e : Expr)
    (val : ℕ) (hup : uv ≠ pv) (hun : uv ≠ nN) (hvp : vv ≠ pv) (hvu : vv ≠ uv)
    (hvn : vv ≠ nN) (hsqB : N * N < B) (τ : Env) (hn : τ.vars nN = N)
    (hp : τ.vars pv < N * N) (hlen : τ.vars pv < (τ.arrs dst).length)
    (he : e.evalB B ((τ.setVar uv (τ.vars pv / N)).setVar vv (τ.vars pv % N))
        = some val) :
    ∃ τ', Run B (.seq (agDecCom pv uv vv nN) (.store dst (.var pv) e)) τ τ'
        (12 + e.size) ∧
      (∀ y, y ≠ uv → y ≠ vv → τ'.vars y = τ.vars y) ∧
      (∀ a, a ≠ dst → τ'.arrs a = τ.arrs a) ∧
      τ'.arrs dst = (τ.arrs dst).set (τ.vars pv) val := by
  have hdec := agDecRun (B := B) (N := N) pv uv vv nN hup hun hsqB τ hn hp
  set ρ := (τ.setVar uv (τ.vars pv / N)).setVar vv (τ.vars pv % N) with hρ
  have hρp : ρ.vars pv = τ.vars pv := by
    rw [hρ, agVs_ne _ hvp, agVs_ne _ hup]
  have hρa : ∀ a, ρ.arrs a = τ.arrs a := by
    intro a; rw [hρ, agVs_arrs, agVs_arrs]
  have hstore : Run B (.store dst (.var pv) e) ρ
      (ρ.setArr dst (τ.vars pv) val) (1 + 1 + e.size) := by
    refine (Run.store ?_ he ?_).mono (by simp [Expr.size])
    · rw [← hρp]
      exact evalB_var (B := B) (by rw [hρp]; omega)
    · rw [hρp, hρa]
      exact hlen
  refine ⟨ρ.setArr dst (τ.vars pv) val, (hdec.seq hstore).mono (by omega),
    ?_, ?_, ?_⟩
  · intro y hy1 hy2
    rw [agAs_vars, hρ, agVs_ne _ hy2, agVs_ne _ hy1]
  · intro a ha
    rw [agAs_ne _ ha, hρa]
  · rw [agAs_self, hρa]

end Lax3Proofs.Prog
