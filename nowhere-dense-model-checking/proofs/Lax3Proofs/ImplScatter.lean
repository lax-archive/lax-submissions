import Lax3.ScatterSentences
import Lax3Proofs.WalkDistance
import Lax3Proofs.ScatterChoices

/-!
# `greedyScatter` — the guarded early-stop sweep (E12, §6.5)

`algorithm-v2.md` §6.5's routine, as a program shape over the vertex
order, with the two facts the design charges it with:

```
if t = 0 then return 0                    -- without this the routine is Θ(N²)
picked := 0 ; marked := ∅
for v in order:
    if P(v) and v ∉ marked:
        picked += 1
        if picked = t: return t
        marked := marked ∪ ball_r(v)
return picked
```

## What is delivered

* `sweep` — the *unguarded* sweep over the canonical ascending order
  `List.finRange n`, and `mem_sweep_iff`/`length_sweep`: the sweep picks
  exactly `Lax3Proofs.ScatterChoices.greedySet` (the abstract driver's
  scatter set), so its count is `greedyChoice.size` — the identity to
  the abstract layer, at the set and at the number.
* `greedyScatter` — the guarded early-stop form, with the `t = 0` guard
  **explicit in the program text**, and `greedyScatter_eq_min`: its
  value is `min t (greedySet G r X).ncard`, which is §4's advertised
  result "`min(t, size of the greedy maximal r-scattered subset of P)`".
* `le_greedyScatter_iff` — the atom the driver actually consumes
  (`DriverArena.tablesAux`'s scatter branch is
  `σ.t ≤ S.choice.size B.G σ.r {…}` at `choice := greedyChoice`): the
  guarded count decides `t ≤ greedyChoice.size` exactly.
* `greedyScatterCost` and `greedyScatterCost_le` — the §4 charge
  `O(t·‖A‖)`, in the routine's own cost model: each loop step costs `1`
  (the `P(v)` and `marked` tests are array reads), each *non-final* pick
  costs `W` — the parameter standing for the ball-marking BFS, to be
  instantiated at `W := ‖A‖` since `‖ball_r(v)‖ ≤ ‖A‖` — and the
  early stop cuts the scan. The bound is `t * (n + W)`, and the `t = 0`
  case is the *equality* `greedyScatterCost_zero : … = 0`: the guard is
  a cost statement, not a value statement (the value at `t = 0` is `0`
  with or without the guard; the *scan* is what the guard removes).

## The `marked` set

The program text tests `∀ u ∈ acc, ¬ WithinDist G r u v` where `acc` is
the list of picked vertices — semantically *exactly* "`v ∉ marked`" for
`marked = ⋃_{u picked} ball_r(u)`. The machine maintains `marked` as a
bit array written by the marking BFS (that is what the per-pick charge
`W` pays for), so the test is `O(1)` per step; the Lean spelling reads
the picked list instead because the identity proofs consume the greedy
recursion `GreedyMem` in precisely this shape. The `if`s are on
undecidable `Prop`s (`WithinDist` carries a walk), so the definitions
are `noncomputable` via `Classical` — like `greedySet` itself, the
routine is "computable" in the source's RAM sense, not in the
code-extraction sense (`Lax3.ScatterSentences`'s module docstring makes
the same point for the abstract greedy process).

## Order sensitivity

The sweep runs over the *canonical ascending order* on `Fin n`, because
`greedySet`'s recursion `GreedyMem` is stated in that order. §4 D3
records that the choice of order is *not* load-bearing for the driver —
any order gives *a* maximal scattered set — but the identity proved here
is to the canonical-order `greedySet`, which is the set the canonical
scatter choice `greedyChoice` counts.
-/

namespace Lax3Proofs.Impl

open Lax3.ColoredGraphs Lax3.ScatterSentences

variable {n : ℕ}

/-! ### The unguarded sweep, and its identity to `greedySet` -/

open Classical in
/-- One pass of §6.5's loop body over the remaining order `l`, carrying
the picked list `acc`: pick `v` exactly when it satisfies the predicate
and is unmarked — no earlier picked vertex is within distance `r`. -/
noncomputable def sweepAcc (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    List (Fin n) → List (Fin n) → List (Fin n)
  | acc, [] => acc
  | acc, v :: vs =>
      if v ∈ X ∧ ∀ u ∈ acc, ¬ WithinDist G r u v
      then sweepAcc G r X (acc ++ [v]) vs
      else sweepAcc G r X acc vs

/-- The unguarded sweep: §6.5's loop with `t = ∞`, over the canonical
ascending order. -/
noncomputable def sweep (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    List (Fin n) :=
  sweepAcc G r X [] (List.finRange n)

/-- The greedy recursion, unfolded once (the equation of
`ScatterChoices.GreedyMem`). -/
theorem greedyMem_iff (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) (v : Fin n) :
    GreedyMem G r X v ↔
      v ∈ X ∧ ∀ u : Fin n, u < v → GreedyMem G r X u → ¬ WithinDist G r u v := by
  rw [GreedyMem]

/-- **The sweep invariant.** Along a strictly ascending remainder `l`,
with `acc` holding exactly the greedy members already processed (and
everything not in `l` processed, i.e. below `l`), the sweep ends with
exactly the greedy members, without duplicates. -/
theorem sweepAcc_spec (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    ∀ (l acc : List (Fin n)),
      l.Pairwise (· < ·) →
      (∀ u : Fin n, u ∈ acc ↔ GreedyMem G r X u ∧ u ∉ l) →
      (∀ u w : Fin n, u ∉ l → w ∈ l → u < w) →
      acc.Nodup →
      (∀ u : Fin n, u ∈ sweepAcc G r X acc l ↔ GreedyMem G r X u) ∧
        (sweepAcc G r X acc l).Nodup
  | [], acc, _, hacc, _, hnd => by
      refine ⟨fun u => ?_, by simpa [sweepAcc] using hnd⟩
      rw [sweepAcc, hacc u]
      simp
  | v :: vs, acc, hsort, hacc, hbelow, hnd => by
      have hvvs : ∀ w ∈ vs, v < w := fun w hw => (List.pairwise_cons.mp hsort).1 w hw
      have hsort' : vs.Pairwise (· < ·) := (List.pairwise_cons.mp hsort).2
      have hvnotvs : v ∉ vs := fun h => lt_irrefl v (hvvs v h)
      -- the test decides `GreedyMem v`
      have htest : (v ∈ X ∧ ∀ u ∈ acc, ¬ WithinDist G r u v) ↔ GreedyMem G r X v := by
        rw [greedyMem_iff]
        constructor
        · rintro ⟨hvX, hfar⟩
          refine ⟨hvX, fun u hu hgu => ?_⟩
          refine hfar u ((hacc u).mpr ⟨hgu, fun hul => ?_⟩)
          rcases List.mem_cons.mp hul with rfl | h
          · exact lt_irrefl _ hu
          · exact lt_asymm hu (hvvs u h)
        · rintro ⟨hvX, hfar⟩
          refine ⟨hvX, fun u hu => ?_⟩
          obtain ⟨hgu, hunl⟩ := (hacc u).mp hu
          exact hfar u (hbelow u v hunl (List.mem_cons_self ..)) hgu
      have hvacc : v ∉ acc := fun h => ((hacc v).mp h).2 (List.mem_cons_self ..)
      -- the two invariant clauses for the tail, in each branch
      by_cases hgv : GreedyMem G r X v
      · rw [sweepAcc, if_pos (htest.mpr hgv)]
        refine sweepAcc_spec G r X vs (acc ++ [v]) hsort' (fun u => ?_)
          (fun u w hu hw => ?_)
          (hnd.append (List.nodup_singleton v)
            (fun a ha hav => hvacc ((List.mem_singleton.mp hav) ▸ ha)))
        · constructor
          · intro hu
            rcases List.mem_append.mp hu with h | h
            · obtain ⟨hg, hnl⟩ := (hacc u).mp h
              exact ⟨hg, fun hvs => hnl (List.mem_cons_of_mem _ hvs)⟩
            · obtain rfl : u = v := by simpa using h
              exact ⟨hgv, hvnotvs⟩
          · rintro ⟨hg, hnvs⟩
            by_cases huv : u = v
            · subst huv; simp
            · exact List.mem_append.mpr (Or.inl ((hacc u).mpr
                ⟨hg, fun hl => (by simpa [huv] using hl : u ∈ vs) |> hnvs⟩))
        · by_cases huv : u = v
          · subst huv; exact hvvs w hw
          · exact hbelow u w (by simp [huv, hu]) (List.mem_cons_of_mem _ hw)
      · rw [sweepAcc, if_neg (fun h => hgv (htest.mp h))]
        refine sweepAcc_spec G r X vs acc hsort' (fun u => ?_)
          (fun u w hu hw => ?_) hnd
        · rw [hacc u]
          constructor
          · rintro ⟨hg, hnl⟩
            exact ⟨hg, fun hvs => hnl (List.mem_cons_of_mem _ hvs)⟩
          · rintro ⟨hg, hnvs⟩
            refine ⟨hg, fun hl => ?_⟩
            rcases List.mem_cons.mp hl with rfl | h
            · exact hgv hg
            · exact hnvs h
        · by_cases huv : u = v
          · subst huv; exact hvvs w hw
          · exact hbelow u w (by simp [huv, hu]) (List.mem_cons_of_mem _ hw)

/-- **The sweep picks exactly the greedy set** — the identity of the
routine's picked list with `ScatterChoices.greedySet`, the set the
canonical scatter choice `greedyChoice` counts. -/
theorem mem_sweep_iff (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) (v : Fin n) :
    v ∈ sweep G r X ↔ v ∈ greedySet G r X :=
  (sweepAcc_spec G r X (List.finRange n) [] (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange n))
    (by simp [List.mem_finRange]) (by simp [List.mem_finRange]) List.nodup_nil).1 v

theorem sweep_nodup (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    (sweep G r X).Nodup :=
  (sweepAcc_spec G r X (List.finRange n) [] (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange n))
    (by simp [List.mem_finRange]) (by simp [List.mem_finRange]) List.nodup_nil).2

/-- **The sweep's count is the greedy count**: the picked list has
exactly `(greedySet G r X).ncard` entries. -/
theorem length_sweep (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    (sweep G r X).length = (greedySet G r X).ncard := by
  classical
  have hset : greedySet G r X = ↑(sweep G r X).toFinset := by
    ext v
    simp [← mem_sweep_iff G r X v]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (sweep_nodup G r X)]

/-! ### The guarded early-stop form -/

open Classical in
/-- §6.5's loop with the early stop: picking the `t`-th vertex returns
`t` immediately, skipping both the rest of the scan and the final
marking BFS. -/
noncomputable def scatterAux (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (t : ℕ) : List (Fin n) → List (Fin n) → ℕ
  | acc, [] => acc.length
  | acc, v :: vs =>
      if v ∈ X ∧ ∀ u ∈ acc, ¬ WithinDist G r u v then
        if acc.length + 1 = t then t
        else scatterAux G r X t (acc ++ [v]) vs
      else scatterAux G r X t acc vs

/-- **`greedyScatter A r P t`** (§4, §6.5): the guarded greedy scatter
count, with the `t = 0` guard explicit in the program text. -/
noncomputable def greedyScatter (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (t : ℕ) : ℕ :=
  if t = 0 then 0 else scatterAux G r X t [] (List.finRange n)

/-- The sweep only ever appends: its result is at least as long as the
accumulator it started from. -/
theorem length_le_sweepAcc (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    ∀ (l acc : List (Fin n)), acc.length ≤ (sweepAcc G r X acc l).length
  | [], acc => by rw [sweepAcc]
  | v :: vs, acc => by
      rw [sweepAcc]
      split
      · exact le_trans (by simp) (length_le_sweepAcc G r X vs (acc ++ [v]))
      · exact length_le_sweepAcc G r X vs acc

/-- The guarded run computes the min of `t` with the unguarded count,
from any accumulator still below the cap. -/
theorem scatterAux_eq_min (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) (t : ℕ) :
    ∀ (l acc : List (Fin n)), acc.length < t →
      scatterAux G r X t acc l = min t (sweepAcc G r X acc l).length
  | [], acc, h => by
      rw [scatterAux, sweepAcc, Nat.min_eq_right (le_of_lt h)]
  | v :: vs, acc, h => by
      rw [scatterAux, sweepAcc]
      split
      · split
        · next hhit =>
          have hlen : t ≤ (sweepAcc G r X (acc ++ [v]) vs).length := by
            have := length_le_sweepAcc G r X vs (acc ++ [v])
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            omega
          exact (Nat.min_eq_left hlen).symm
        · next hmiss =>
          exact scatterAux_eq_min G r X t vs (acc ++ [v])
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      · exact scatterAux_eq_min G r X t vs acc h

/-- **The §4 result identity**: the guarded routine returns
`min(t, size of the greedy maximal r-scattered subset of X)`. -/
theorem greedyScatter_eq_min (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (t : ℕ) : greedyScatter G r X t = min t (greedySet G r X).ncard := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [greedyScatter]
  · rw [greedyScatter, if_neg (Nat.pos_iff_ne_zero.mp ht),
      scatterAux_eq_min G r X t (List.finRange n) [] (by simpa using ht)]
    exact congrArg _ (length_sweep G r X)

/-- The canonical scatter choice `greedyChoice` counts the greedy set —
definitionally. -/
theorem greedyChoice_size_eq (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    greedyChoice.size G r X = (greedySet G r X).ncard := rfl

/-- **The atom the driver consumes** (`Driver.tablesAux`'s scatter
branch at `choice := greedyChoice`): the guarded early-stop count
decides `σ.t ≤ greedyChoice.size` exactly, even though it never counts
past `t`. -/
theorem le_greedyScatter_iff (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (t : ℕ) : t ≤ greedyScatter G r X t ↔ t ≤ greedyChoice.size G r X := by
  rw [greedyScatter_eq_min, greedyChoice_size_eq, Nat.le_min]
  simp

/-! ### The charge (§4: `O(t·‖A‖)`, with `t = 0` explicit) -/

open Classical in
/-- The cost of the guarded run: `1` per scan step, plus `W` — the
ball-marking BFS, `W := ‖A‖` at the §4 instantiation — per non-final
pick. The final pick returns before marking, which the early-stop
branch's `1` records. -/
noncomputable def scatterCostAux (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (W t : ℕ) : List (Fin n) → List (Fin n) → ℕ
  | _, [] => 0
  | acc, v :: vs =>
      if v ∈ X ∧ ∀ u ∈ acc, ¬ WithinDist G r u v then
        if acc.length + 1 = t then 1
        else 1 + W + scatterCostAux G r X W t (acc ++ [v]) vs
      else 1 + scatterCostAux G r X W t acc vs

/-- The cost of `greedyScatter`: the `t = 0` guard pays nothing at all. -/
noncomputable def greedyScatterCost (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (W t : ℕ) : ℕ :=
  if t = 0 then 0 else scatterCostAux G r X W t [] (List.finRange n)

/-- **The guard, as the cost statement it is**: at `t = 0` the routine
does not scan. (Without the guard the scan alone is `Θ(N)` per call, and
the driver issues arena-many calls — the `Θ(N²)` of §6.5's margin note.) -/
theorem greedyScatterCost_zero (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (W : ℕ) : greedyScatterCost G r X W 0 = 0 := by
  simp [greedyScatterCost]

/-- The scan-plus-marking bound from any accumulator below the cap: the
remaining scan costs its length, and at most `t − 1 − |acc|` further
non-final picks each cost `W`. -/
theorem scatterCostAux_le (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (W t : ℕ) : ∀ (l acc : List (Fin n)), acc.length < t →
      scatterCostAux G r X W t acc l ≤ l.length + (t - 1 - acc.length) * W
  | [], acc, _ => by rw [scatterCostAux]; exact Nat.zero_le _
  | v :: vs, acc, h => by
      rw [scatterCostAux]
      split
      · split
        · rw [List.length_cons]
          exact le_trans (Nat.le_add_left 1 vs.length) (Nat.le_add_right _ _)
        · next hmiss =>
          have hrec := scatterCostAux_le G r X W t vs (acc ++ [v])
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          have hK : (t - 1 - acc.length) * W
              = (t - 1 - (acc ++ [v]).length) * W + W := by
            have hsucc : t - 1 - (acc ++ [v]).length + 1 = t - 1 - acc.length := by
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            rw [← hsucc, Nat.succ_mul]
          rw [List.length_cons, hK]
          refine le_trans (Nat.add_le_add_left hrec _) (le_of_eq ?_)
          simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      · have hrec := scatterCostAux_le G r X W t vs acc h
        rw [List.length_cons]
        refine le_trans (Nat.add_le_add_left hrec _) (le_of_eq ?_)
        simp only [Nat.add_left_comm, Nat.add_assoc]

/-- **The §4 charge**: `greedyScatter` costs `O(t·‖A‖)` — precisely
`t * (n + W)` with `W` the per-pick marking charge (`W := ‖A‖` at the
instantiation), and `0` outright at `t = 0`. -/
theorem greedyScatterCost_le (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n))
    (W t : ℕ) : greedyScatterCost G r X W t ≤ t * (n + W) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [greedyScatterCost_zero]
    exact Nat.zero_le _
  · rw [greedyScatterCost, if_neg (Nat.pos_iff_ne_zero.mp ht)]
    calc scatterCostAux G r X W t [] (List.finRange n)
        ≤ (List.finRange n).length + (t - 1 - ([] : List (Fin n)).length) * W :=
          scatterCostAux_le G r X W t (List.finRange n) [] (by simpa using ht)
      _ = n + (t - 1) * W := by simp
      _ ≤ t * n + t * W :=
          Nat.add_le_add (Nat.le_mul_of_pos_left n ht)
            (Nat.mul_le_mul_right W (Nat.sub_le t 1))
      _ = t * (n + W) := (Nat.mul_add t n W).symm

end Lax3Proofs.Impl
