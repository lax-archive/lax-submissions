import Lax13Proofs.Refine.Examples.Bfs
import Lax3Proofs.WalkDistance

/-!
# The `Refine` tower probe (E11, §8 step 5)

`Lax13Proofs.Refine.Examples.Bfs` is the tower's P1 acceptance program:
masked depth-capped BFS, specified as one `NRest.spec` and refined
abstract-to-abstract with the cost riding the refinement ordering
(`bfsAlg_correct : bfsAlg G M s d ≤ bfsSpec G M s d`). Its module
docstring promises that the bridge to this submission's vocabulary is
one line on the consumer's side, `rfl`-adjacent, because
`deleteVerts G {v | M v = false}` has exactly the adjacency `masked` has.
This file is that consumer: it tests the promise, instantiates the
acceptance theorem in ND-MC vocabulary, and extracts the charge.

## §1 The bridge, and its true size

The promise holds. `masked_eq_deleteVerts` is `ext` + one `simp`
(`masked`'s adjacency stores `M u = true`, `deleteVerts`'s stores
`¬ (M u = false)`, and `Bool.not_eq_false` is the whole distance between
them — this is why the proof is `simp` and not literally `rfl`).
`wd_iff_withinDist` and `wd_iff_mem_ball` are then transports across
that equality: `WD`, `WithinDist` and `∈ ball` are all definitionally
`∃ w : _.Walk u v, w.length ≤ k` once the graphs are identified.

## §2 The charge, verbatim in the cost algebra

`bfsAlg_computes_ball` below restates `bfsAlg_correct` against
`ball (deleteVerts G {v | M v = false})`. Its cost annotation — the
whole run's budget, quoted in the algebra it is stated in
(`ACost String ℕ`, lifted by `liftACost` into `ECost = ACost String ℕ∞`
on the spec) — is `charge G M d`:

    ACost.cost "bfs.init"   (n + 1)
  + ACost.cost "if"         1
  + ACost.cost "bfs.level"  d
  + ACost.cost "bfs.expand" (∑ v ∈ Finset.univ.filter (fun v => M v = true),
                               (G.degree v + 1))

`charge_eq_budget` proves this *is* the tower's `bfsBudgetN`, by `rfl`.

## §3 The §6.1 comparison — what the charge actually is

`algorithm-v2.md` §6.1 budgets `bfs A v d` at `O(‖ball_d(v)‖)`, the
touched-only measure (`‖·‖` = vertices + edges). The statement above
does **not** have that shape. Read off the statements, not the
docstrings:

* **`bfs.expand` is alive-summed, not ball-summed.** The sum ranges over
  *every* vertex the mask keeps alive, reachable from `s` within `d` or
  not, and each contributes its degree **in the unmasked `G`** — scanning
  a row costs the row's full length, which is CSR reality (§6.1 makes the
  same point for `restrict`: the charge is `Σ_{s∈S} deg_A(s)`, not
  `deg_{A[S]}(s)`). So at mask = cluster the charge is
  `∑_{v ∈ X_u} (deg_A v + 1)` — the shape of §6.1's `restrict` charge,
  not of its `bfs` charge. The proof's *energy* (`remWeight`, which
  telescopes by `remWeight_step`) is the touched-only measure, but the
  advertised budget `bfsBudgetN` spends the whole alive weight up front
  and `exit_cost_le` forfeits the remainder; tightening the spec to
  ball-shape would need the initial energy to be ball-weight, i.e. a
  frontier-stays-in-the-ball clause added to `Inv` — a restatement of the
  spec and invariant, not a one-line consumer patch.

* **`bfs.init` is carrier-sized and charged per call.** `n + 1` where
  `n` is the carrier of the graph handed in, once per `bfsAlg` call. §5
  line 17 runs one BFS per cluster; on the whole arena with mask = X_u
  that is `N_A + 1` per centre, i.e. `N · #centres` — the quadratic
  mistake the record warns about, *sitting in the init term rather than
  the expand term*. The statements therefore force §5's actual shape:
  BFS runs on `B₀ := restrict(A, X_u)` (carrier `|X_u|`), where init is
  `|X_u| + 1` and the expand sum is `Σ_{v∈X_u} (deg_{B₀} v + 1) ≤ ‖B₀‖ + |X_u|`,
  both covered by the cover's `Σ_u |X_u|`-type bounds. The mask
  mechanism *cannot* substitute for `restrict`: with mask alone, both
  init and expand are arena-sized per cluster.

* `d` units of `bfs.level` and one `if` are within any per-call budget
  (`d ≤ 2R`, a compile-time constant).

**Verdict:** the tower's charge for this routine is
`O(carrier + Σ_{alive} deg_G)` per call, which matches §6.1's
`O(‖ball_d(v)‖)` only after `restrict` has already been paid for — i.e.
the probe confirms the §5 pipeline order (restrict, then BFS) is forced
by the cost statements, and that a masked BFS on the unrestricted arena
would not meet the §6.1 budget.

## §4 Space (§11), one paragraph

`Refine/Sepref/SpaceBudgetProbe.lean` is a natural home for §11's
accounting and needs nothing built: its `nestedSkel` is already the
ND-MC driver's shape — within a turn, descend `levels` deep holding one
arena per level, unwind LIFO — with `peak_nestedSkel` giving peak
`setup + levels · aw` (arenas compose with *depth*, not with *turns*),
`nested_fits_iff` an `↔` against the word-size budget, and
`no_word_size_for_nested` the compiled failure once depth grows with
`n`. §11's obligation would land there as the `levels · aw = O(|x|)`
side condition (recursion depth `ℓ` is a compile-time constant here, so
the live question is only the per-level arena size — §11's `≤ N²` peak
for the cover). The file deliberately reproduces C0's domain in shape
without importing this package, so consuming it means instantiating its
symbolic `setup`/`aw`/`levels` at this campaign's numbers, on our side —
same seam as this file, and about as wide.
-/

namespace Lax3Proofs.RefineBfsProbe

open Lax13Proofs.Refine
open Lax3.ColoredGraphs (WithinDist ball)
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.WalkDistance (mem_ball)

variable {n : ℕ}

/-! ## The vocabulary bridge (§1) -/

/-- **The bridge, graph half.** The tower's masked graph *is* Lax12's
vertex deletion at the dead set of the mask. `ext` plus one `simp`
(`Bool.not_eq_false` is the entire gap — `masked` stores `M u = true`,
`deleteVerts` stores `¬ (M u = false)`). -/
theorem masked_eq_deleteVerts (G : SimpleGraph (Fin n)) (M : Fin n → Bool) :
    Bfs.masked G M = deleteVerts G {x | M x = false} := by
  ext u v
  show G.Adj u v ∧ M u = true ∧ M v = true ↔
    G.Adj u v ∧ u ∉ {x | M x = false} ∧ v ∉ {x | M x = false}
  simp [Set.mem_setOf_eq]

/-- **The bridge, distance half.** The tower's `WD` is this submission's
`WithinDist` of the vertex-deleted graph. A transport across
`masked_eq_deleteVerts`; both sides are definitionally
`∃ w : _.Walk u v, w.length ≤ k`. -/
theorem wd_iff_withinDist (G : SimpleGraph (Fin n)) (M : Fin n → Bool) (k : ℕ)
    (u v : Fin n) :
    Bfs.WD G M k u v ↔ WithinDist (deleteVerts G {x | M x = false}) k u v := by
  rw [show deleteVerts G {x | M x = false} = Bfs.masked G M from
    (masked_eq_deleteVerts G M).symm]
  exact Iff.rfl

/-- The ball spelling of the distance half: `WD G M k s v` says `v` lies
in the radius-`k` ball of `s` in the vertex-deleted graph. -/
theorem wd_iff_mem_ball (G : SimpleGraph (Fin n)) (M : Fin n → Bool) (k : ℕ)
    (s v : Fin n) :
    Bfs.WD G M k s v ↔ v ∈ ball (deleteVerts G {x | M x = false}) k s :=
  (wd_iff_withinDist G M k s v).trans mem_ball.symm

/-- The tower's postcondition, translated clause by clause: the array
decides membership in every ball of the vertex-deleted graph up to the
cap. -/
theorem post_iff_ball (G : SimpleGraph (Fin n)) (M : Fin n → Bool) (s : Fin n)
    (d : ℕ) (D : Fin n → ℕ) :
    Bfs.Post G M s d D ↔
      ∀ v : Fin n, ∀ k ≤ d,
        (D v ≤ k ↔ v ∈ ball (deleteVerts G {x | M x = false}) k s) :=
  forall_congr' fun v => forall_congr' fun k => imp_congr_right fun _ =>
    iff_congr Iff.rfl (wd_iff_mem_ball G M k s v)

/-! ## The charge, extracted and named (§2) -/

/-- **The probe's charge, in closed form**, in the algebra the tower
states it in (`ACost String ℕ`, lifted to `ECost` on the spec):
`(n+1)` units of `bfs.init`, one `if`, `d` units of `bfs.level`, and
`∑_{v alive} (deg_G v + 1)` units of `bfs.expand`. Note what the last
sum ranges over — every *alive* vertex, not every *reached* one, each at
its degree in the **unmasked** `G`; §3 of the module docstring is the
comparison of this shape against `algorithm-v2.md` §6.1. -/
def charge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (d : ℕ) : ACost String ℕ :=
  ACost.cost "bfs.init" (n + 1) + ACost.cost "if" 1 + ACost.cost "bfs.level" d
    + ACost.cost "bfs.expand"
        (∑ v ∈ Finset.univ.filter (fun v => M v = true), (G.degree v + 1))

/-- The closed form is the tower's advertised budget — definitionally. -/
theorem charge_eq_budget (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : Fin n → Bool) (d : ℕ) : charge G M d = Bfs.bfsBudgetN G M d := rfl

/-! ## The instantiated acceptance (§2) -/

/-- **E11's instantiation.** The tower's masked depth-capped BFS, read in
ND-MC vocabulary: `bfsAlg` refines the specification *"an array deciding
membership in every `ball (deleteVerts G {x | M x = false}) k s` for
`k ≤ d`, for `charge G M d`"*. Thin by design — the content is
`Bfs.bfsAlg_correct`; this theorem is the bridge applied to its
specification. -/
theorem bfsAlg_computes_ball (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : Fin n → Bool) (s : Fin n) (d : ℕ) :
    Bfs.bfsAlg G M s d ≤
      NRest.spec
        (fun D => ∀ v : Fin n, ∀ k ≤ d,
          (D v ≤ k ↔ v ∈ ball (deleteVerts G {x | M x = false}) k s))
        (fun _ => liftACost (charge G M d)) := by
  have h := Bfs.bfsAlg_correct G M s d
  have hspec : Bfs.bfsSpec G M s d =
      NRest.spec
        (fun D => ∀ v : Fin n, ∀ k ≤ d,
          (D v ≤ k ↔ v ∈ ball (deleteVerts G {x | M x = false}) k s))
        (fun _ => liftACost (charge G M d)) := by
    unfold Bfs.bfsSpec
    rw [charge_eq_budget]
    congr 1
    funext D
    exact propext (post_iff_ball G M s d D)
  rwa [hspec] at h

end Lax3Proofs.RefineBfsProbe
