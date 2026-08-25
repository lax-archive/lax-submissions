import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lax3Proofs.RefineBfsProbe
import Lax3Proofs.CoverCentres
import Lax3Proofs.DriverBfsTree

/-!
# `bfs` and `bfsSupports` (E12, §4/§6.1) — the tower's BFS consumed at `B₀`

E11's probe (`RefineBfsProbe`) instantiated the tower's masked BFS and
extracted its charge; its verdict binds this file: **the tower's
`bfs.init` is carrier-sized and its `bfs.expand` is alive-summed at
unmasked degrees, so the algorithm must call BFS on
`B₀ := restrict(A, X_u)` — carrier `|X_u|` — and never mask-on-the-big-
arena.** This file is that consumption, plus the support-materializing
variant `bfsSupports`.

## §1 `bfs` at `B₀`

`bfsAlg_computes_ball_B0` is `RefineBfsProbe.bfsAlg_computes_ball` at
the *full mask* — the mask is `fun _ => true` because after `restrict`
the carrier IS the cluster, which is the point of the verdict. The two
mask artifacts evaporate: `deleteVerts` at the dead set of the full mask
is the graph itself, and the alive-filter of the expand sum is `univ`,
so the charge closes to `chargeB0`:

    bfs.init    n + 1
    if          1
    bfs.level   d
    bfs.expand  2·M + n        (degree-sum formula; M = #edges of B₀)

`chargeB0_total` states the whole account: the four currencies sum to
**exactly `2·‖B₀‖ + d + 2`** (`‖H‖ := n + M`, §4's arena norm), and
`chargeB0_apply_ne` says every other currency is `0`. With `d ≤ 2R` a
compile-time constant this is §6.1's `bfs` charge `O(‖B₀‖)` — *the
carrier-sized shape, not the ball-sized shape*: per the probe's §3, the
tower spends the whole alive weight up front, and the ball-sized reading
of §6.1 is recovered only because the caller pays `restrict` first and
`Σ_u ‖B₀(u)‖`-type sums are the cover's own bounds (`Σ_u |X_u| ≤ D·N`).
This file does **not** claim the `O(‖ball_d(v)‖)` form on the
unrestricted arena — E11 established that no consumer-side statement
delivers it.

## §2 `bfsSupports` — materializing the walk supports

**Relocated to `DriverBfsTree` §1** (verbatim, same namespace and
spelling: `BallTable`, `parents`, `descend`, `bfsSupports` and their
specs), so that `Driver.childArena`'s downward channel can be *defined*
by them. This section's text is kept here because §2a below prices what
it defines. Nothing about the statements changed.

§4: *"one BFS from `v` materialising the `≤ d+1` support names at every
reached vertex"* — the data D6's `hist` channel stores. The machine gets
it from the BFS tree; here the tree is read off the distance array `D`
that the tower's spec guarantees (`BallTable`, the postcondition of
`bfsAlg_computes_ball` verbatim — this is the seam to E11, and it is
one hypothesis wide):

* `descend H D v` walks from `v` down the distance gradient — each step
  moves to the `Finset.min'` of the strictly-closer neighbours — and
  under `BallTable` this is a *witness walk support*:
  `descend_spec : ∃ w : H.Walk v s, w.length = D v ∧ w.support =
  descend H D v`. Its length is exactly `D v + 1 ≤ d + 1`
  (`length_descend`, `length_descend_le`) and every name on it is in
  the ball (`mem_descend_mem_ball`).
* `bfsSupports H D d` is the table: `some (descend …)` at reached
  vertices, `none` beyond the horizon.

## §2a The charge (§4: `O(d·‖ball_d(v)‖)`)

The machine materializes the table by dynamic programming down the BFS
levels — `descend`'s own equation `descend v = v :: descend (parent v)`
IS that sharing: per reached vertex, one parent scan of the CSR row
(`deg v + 1`) and one list of `D v + 1` names. `supportsCharge` is that
account summed over the reached set, and `supportsCharge_le` bounds it
by `(d + 2) * ballNorm`, where `ballNorm = Σ_{reached} (deg v + 1)` is
§6.1's touched measure at CSR reality (degrees in `H`, per the probe's
§3 — a row scan costs the row). Under `BallTable` the reached set is
exactly `ball H d s` (`mem_reached_iff`), so this is the §4 charge.

The Lean `descend` re-finds the parent by `Finset.min'` over the whole
carrier because it is a *definition of the value*; the charge model
prices the machine's row scan, and the theorems tie the two at the
value.
-/

namespace Lax3Proofs.Impl

open Lax13Proofs.Refine
open Lax3.ColoredGraphs (WithinDist ball)
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.WalkDistance
open Lax3Proofs.RefineBfsProbe (charge bfsAlg_computes_ball)

variable {n : ℕ}

/-! ### §1 The full-mask instantiation: `bfs` at `B₀` -/

/-- §4's arena norm `‖A‖ = N + M` for a graph on `Fin n`. -/
def gsize (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] : ℕ :=
  n + H.edgeFinset.card

/-- At the full mask nothing is deleted: `B₀` is its own alive graph. -/
theorem deleteVerts_full_mask (H : SimpleGraph (Fin n)) :
    deleteVerts H {x : Fin n | (fun _ : Fin n => true) x = false} = H := by
  ext u v
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by simp, by simp⟩

/-- **The `B₀` charge, closed**: init `n + 1`, one `if`, `d` levels,
and expand `2M + n` by the degree-sum formula. -/
def chargeB0 (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (d : ℕ) :
    ACost String ℕ :=
  ACost.cost "bfs.init" (n + 1) + ACost.cost "if" 1 + ACost.cost "bfs.level" d
    + ACost.cost "bfs.expand" (2 * H.edgeFinset.card + n)

/-- The probe's charge at the full mask is `chargeB0`: the alive filter
is everything, and the expand sum closes by `Σ_v deg v = 2M`. -/
theorem charge_full_mask (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (d : ℕ) :
    charge H (fun _ => true) d = chargeB0 H d := by
  unfold Lax3Proofs.RefineBfsProbe.charge chargeB0
  congr 2
  rw [Finset.filter_true_of_mem (fun _ _ => rfl), Finset.sum_add_distrib,
    SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp

/-- **E12's `bfs`, consumed at `B₀`** (the probe's verdict made a
statement): on the post-`restrict` arena the tower's BFS refines the
specification "an array deciding membership in every `ball H k s`,
`k ≤ d`, for `chargeB0 H d`" — full mask, no `deleteVerts` residue, the
charge in `‖B₀‖` shape. -/
theorem bfsAlg_computes_ball_B0 (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (s : Fin n) (d : ℕ) :
    Bfs.bfsAlg H (fun _ => true) s d ≤
      NRest.spec
        (fun D => ∀ v : Fin n, ∀ k ≤ d, (D v ≤ k ↔ v ∈ ball H k s))
        (fun _ => liftACost (chargeB0 H d)) := by
  have h := bfsAlg_computes_ball H (fun _ => true) s d
  rwa [charge_full_mask, deleteVerts_full_mask] at h

@[simp] theorem chargeB0_apply_init (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (d : ℕ) : (chargeB0 H d).toFun "bfs.init" = n + 1 := by
  simp [chargeB0]

@[simp] theorem chargeB0_apply_if (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (d : ℕ) : (chargeB0 H d).toFun "if" = 1 := by
  simp [chargeB0]

@[simp] theorem chargeB0_apply_level (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (d : ℕ) : (chargeB0 H d).toFun "bfs.level" = d := by
  simp [chargeB0]

@[simp] theorem chargeB0_apply_expand (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (d : ℕ) : (chargeB0 H d).toFun "bfs.expand" = 2 * H.edgeFinset.card + n := by
  simp [chargeB0]

/-- Every currency other than the four named ones is uncharged. -/
theorem chargeB0_apply_ne (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (d : ℕ)
    (key : String) (h₁ : key ≠ "bfs.init") (h₂ : key ≠ "if")
    (h₃ : key ≠ "bfs.level") (h₄ : key ≠ "bfs.expand") :
    (chargeB0 H d).toFun key = 0 := by
  simp [chargeB0, h₁, h₂, h₃, h₄]

/-- **The whole account** — the four currencies of a `B₀` call sum to
exactly `2·‖B₀‖ + d + 2`: §6.1's `bfs` charge in the carrier-sized shape
the tower actually states, `O(‖B₀‖)` at the compile-time constant
`d ≤ 2R`. -/
theorem chargeB0_total (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (d : ℕ) :
    (chargeB0 H d).toFun "bfs.init" + (chargeB0 H d).toFun "if"
      + (chargeB0 H d).toFun "bfs.level" + (chargeB0 H d).toFun "bfs.expand"
      = 2 * gsize H + d + 2 := by
  simp [gsize]
  omega


/-! ### §2a The charge -/

variable (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

/-- The reached set, read off the distance array (computable; equal to
the ball under `BallTable` — `mem_reached_iff`). -/
def reached (D : Fin n → ℕ) (d : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => D v ≤ d

/-- §6.1's touched measure at CSR reality: one row scan per reached
vertex, a row costing its full length in `H` (the probe's §3 point,
there made for `restrict`). -/
def ballNorm (D : Fin n → ℕ) (d : ℕ) : ℕ :=
  ∑ v ∈ reached D d, (H.degree v + 1)

/-- The charge of materializing the whole table: per reached vertex, the
parent-row scan (`deg v + 1`) plus the `D v + 1` names written —
`descend`'s sharing (`descend v = v :: descend (parent v)`) prices each
row once. -/
def supportsCharge (D : Fin n → ℕ) (d : ℕ) : ℕ :=
  ∑ v ∈ reached D d, (D v + 1 + (H.degree v + 1))

variable {H}

omit [DecidableRel H.Adj] in
/-- Under `BallTable` the reached set is exactly the ball. -/
theorem mem_reached_iff {s : Fin n} {d : ℕ} {D : Fin n → ℕ}
    (hD : BallTable H s d D) (v : Fin n) :
    v ∈ reached D d ↔ v ∈ ball H d s := by
  rw [reached, Finset.mem_filter]
  simp [hD v d le_rfl]

/-- **The §4 charge**: `bfsSupports` costs `O(d·‖ball‖)` — precisely at
most `(d + 2) * ballNorm`, with `ballNorm` the touched measure of the
reached set. -/
theorem supportsCharge_le (D : Fin n → ℕ) (d : ℕ) :
    supportsCharge H D d ≤ (d + 2) * ballNorm H D d := by
  have hnames : ∑ v ∈ reached D d, (D v + 1)
      ≤ (d + 1) * ballNorm H D d := by
    calc ∑ v ∈ reached D d, (D v + 1)
        ≤ ∑ v ∈ reached D d, (d + 1) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have := (Finset.mem_filter.mp hv).2
          omega
      _ = (reached D d).card * (d + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ballNorm H D d * (d + 1) := by
          refine Nat.mul_le_mul_right _ ?_
          calc (reached D d).card = ∑ _v ∈ reached D d, 1 := by
                rw [Finset.sum_const, smul_eq_mul, mul_one]
            _ ≤ ballNorm H D d := Finset.sum_le_sum fun v _ => by omega
      _ = (d + 1) * ballNorm H D d := Nat.mul_comm ..
  calc supportsCharge H D d
      = ∑ v ∈ reached D d, (D v + 1) + ballNorm H D d := by
        rw [supportsCharge, ballNorm, ← Finset.sum_add_distrib]
    _ ≤ (d + 1) * ballNorm H D d + ballNorm H D d :=
        Nat.add_le_add_right hnames _
    _ = (d + 2) * ballNorm H D d := by
        rw [Nat.add_mul, Nat.succ_mul, Nat.add_mul]
        omega

end Lax3Proofs.Impl
