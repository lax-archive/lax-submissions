import Lax3Proofs.CoverCentres

/-!
# The BFS tree layer, below the driver (`DriverBfsTree`)

Three landed blocks, **relocated verbatim** so that `Driver.Arena`'s
downward channel can be *defined* by them instead of merely compared
against them:

* `Impl.BallTable` / `Impl.parents` / `Impl.descend` / `Impl.bfsSupports`
  and their specs (was `ImplBfs` §2);
* `Prog.descendCol`, the stored column (was `SolveBlocksSupports` §1);
* `Prog.ballDist`, the canonical truncated distance table, and
  `ballTable_eq_ballDist` (was `SolveMachPrep` §1).

Nothing here is new mathematics and no statement changed: every name
keeps its old fully-qualified spelling, so the machine layer that used
to own these still refers to them unqualified after importing this
file. The only thing that moved is the position in the import graph —
these now sit *below* `DriverArena`, which is what lets `childArena`'s
channel be the very list `supportsCom_specW` writes rather than a
`Classical.choose`-picked walk support.

The import surface is deliberately thin: `CoverCentres` (for
`withinDist_of_mem_support`) and, through it, `WalkDistance` and
`Lax3.ColoredGraphs`' ball vocabulary. Nothing from the IMP+ tower.
-/

namespace Lax3Proofs.Impl

open Lax3.ColoredGraphs (WithinDist ball)
open Lax3Proofs.WalkDistance

variable {n : ℕ}

/-! ## §1 `bfsSupports`: the walk supports read off the distance array -/

/-- The postcondition the tower's BFS guarantees, in ND-MC vocabulary —
verbatim the spec of `bfsAlg_computes_ball` / `bfsAlg_computes_ball_B0`.
This single hypothesis is E11's seam: everything below consumes the
tower through it. -/
def BallTable (H : SimpleGraph (Fin n)) (s : Fin n) (d : ℕ) (D : Fin n → ℕ) : Prop :=
  ∀ v : Fin n, ∀ k ≤ d, (D v ≤ k ↔ v ∈ ball H k s)

variable (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

/-- The strictly-closer neighbours of `v` — the BFS-tree parent
candidates. Nonempty at every reached vertex of positive distance
(`parents_nonempty`). -/
def parents (D : Fin n → ℕ) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun u => H.Adj u v ∧ D u < D v

/-- **The support of one recorded walk**: from `v`, descend the distance
gradient to the source, taking the least parent at each step. Under
`BallTable` this list is the support of a walk of length exactly `D v`
(`descend_spec`). -/
def descend (D : Fin n → ℕ) (v : Fin n) : List (Fin n) :=
  if h : (parents H D v).Nonempty then
    v :: descend D ((parents H D v).min' h)
  else [v]
termination_by D v
decreasing_by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.2

/-- **`bfsSupports`** (§4): the per-vertex support table of one BFS —
the `≤ d+1` support names at every reached vertex, nothing beyond the
horizon. -/
def bfsSupports (D : Fin n → ℕ) (d : ℕ) (v : Fin n) : Option (List (Fin n)) :=
  if D v ≤ d then some (descend H D v) else none

variable {H}

/-- A reached vertex of positive distance has a strictly closer
neighbour: peel the first edge of its witness walk. -/
theorem parents_nonempty {s : Fin n} {d : ℕ} {D : Fin n → ℕ}
    (hD : BallTable H s d D) {v : Fin n} (hvd : D v ≤ d) (hv : 0 < D v) :
    (parents H D v).Nonempty := by
  obtain ⟨w, hw⟩ : WithinDist H (D v) v s :=
    withinDist_symm (mem_ball.mp ((hD v (D v) hvd).mp le_rfl))
  cases w with
  | nil =>
      have : D s ≤ 0 :=
        (hD s 0 (Nat.zero_le d)).mpr (mem_ball_self H 0 s)
      omega
  | cons hadj p =>
      rename_i u
      have hp : p.length ≤ D v - 1 := by
        simp only [SimpleGraph.Walk.length_cons] at hw
        omega
      have hu : D u ≤ D v - 1 :=
        (hD u (D v - 1) (by omega)).mpr (mem_ball.mpr (withinDist_symm ⟨p, hp⟩))
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj.symm, by omega⟩⟩

/-- **The support is a walk's support** — the correctness of `descend`:
at every reached vertex there is a walk to the source of length exactly
`D v` whose support is precisely the recorded list. -/
theorem descend_spec {s : Fin n} {d : ℕ} {D : Fin n → ℕ}
    (hD : BallTable H s d D) (v : Fin n) (hvd : D v ≤ d) :
    ∃ w : H.Walk v s, w.length = D v ∧ w.support = descend H D v := by
  rcases Nat.eq_zero_or_pos (D v) with h0 | hpos
  · -- the source itself: the empty walk
    obtain ⟨w, hw⟩ : WithinDist H 0 s v := mem_ball.mp ((hD v 0 (Nat.zero_le d)).mp (le_of_eq h0))
    cases w with
    | nil =>
        have hemp : ¬ (parents H D s).Nonempty := by
          rintro ⟨u, hu⟩
          have := (Finset.mem_filter.mp hu).2.2
          omega
        refine ⟨.nil, by simpa using h0.symm, ?_⟩
        rw [SimpleGraph.Walk.support_nil, descend, dif_neg hemp]
    | cons hadj p => simp at hw
  · -- one step down the gradient, then the recursive walk
    have hne := parents_nonempty hD hvd hpos
    set u := (parents H D v).min' hne with hu
    have hmem := (parents H D v).min'_mem hne
    rw [← hu, parents, Finset.mem_filter] at hmem
    obtain ⟨-, hadj, hlt⟩ := hmem
    obtain ⟨w', hw'len, hw'sup⟩ := descend_spec hD u (by omega)
    refine ⟨.cons hadj.symm w', ?_, ?_⟩
    · -- the length is exactly `D v`: the walk certifies `D v ≤ D u + 1`
      have hle : D v ≤ D u + 1 := by
        refine (hD v (D u + 1) (by omega)).mpr (mem_ball.mpr ?_)
        exact withinDist_symm ⟨.cons hadj.symm w', by simp [hw'len]⟩
      simp only [SimpleGraph.Walk.length_cons, hw'len]
      omega
    · rw [SimpleGraph.Walk.support_cons, hw'sup]
      conv_rhs => rw [descend]
      rw [dif_pos hne, ← hu]
termination_by D v
decreasing_by exact hlt

/-- The recorded list has exactly `D v + 1` names… -/
theorem length_descend {s : Fin n} {d : ℕ} {D : Fin n → ℕ}
    (hD : BallTable H s d D) {v : Fin n} (hv : D v ≤ d) :
    (descend H D v).length = D v + 1 := by
  obtain ⟨w, hwlen, hwsup⟩ := descend_spec hD v hv
  rw [← hwsup, SimpleGraph.Walk.length_support, hwlen]

/-- …which is §4's `≤ d + 1` bound. -/
theorem length_descend_le {s : Fin n} {d : ℕ} {D : Fin n → ℕ}
    (hD : BallTable H s d D) {v : Fin n} (hv : D v ≤ d) :
    (descend H D v).length ≤ d + 1 := by
  rw [length_descend hD hv]
  omega

/-- Every recorded name lies in the ball being materialized. -/
theorem mem_descend_mem_ball {s : Fin n} {d : ℕ} {D : Fin n → ℕ}
    (hD : BallTable H s d D) {v : Fin n} (hv : D v ≤ d) :
    ∀ x ∈ descend H D v, x ∈ ball H d s := by
  intro x hx
  obtain ⟨w, hwlen, hwsup⟩ := descend_spec hD v hv
  rw [← hwsup] at hx
  exact mem_ball.mpr (withinDist_symm
    (Lax3Proofs.CoverCentres.withinDist_of_mem_support w (by omega) hx).2)

/-- The table row of a reached vertex is its recorded support. -/
theorem bfsSupports_eq_some {d : ℕ} {D : Fin n → ℕ} {v : Fin n} (hv : D v ≤ d) :
    bfsSupports H D d v = some (descend H D v) := if_pos hv

/-- The table row beyond the horizon is empty. -/
theorem bfsSupports_eq_none {d : ℕ} {D : Fin n → ℕ} {v : Fin n} (hv : ¬ D v ≤ d) :
    bfsSupports H D d v = none := if_neg hv
end Lax3Proofs.Impl

namespace Lax3Proofs.Prog

open Lax3.ColoredGraphs (WithinDist ball)
open Lax3Proofs.WalkDistance
open Lax3Proofs.Impl (parents descend bfsSupports BallTable parents_nonempty
  length_descend)

/-! ## §2 The stored column (was `SolveBlocksSupports` §1) -/

section Abstract

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- **The stored column**: `Impl.descend`'s list at reached vertices,
the empty list beyond the horizon. -/
def descendCol (D : Fin N → ℕ) (d : ℕ) (v : Fin N) : List (Fin N) :=
  if D v ≤ d then descend G D v else []

variable {G}

/-- The column is `Impl.bfsSupports`, cell for cell (`none` reads back
as the empty list — the encoding `HistArr` stores). -/
theorem descendCol_eq_bfsSupports (D : Fin N → ℕ) (d : ℕ) (v : Fin N) :
    descendCol G D d v = (bfsSupports G D d v).getD [] := by
  rw [descendCol, Lax3Proofs.Impl.bfsSupports]
  by_cases h : D v ≤ d <;> simp [h]

theorem descendCol_of_reached {D : Fin N → ℕ} {d : ℕ} {v : Fin N}
    (h : D v ≤ d) : descendCol G D d v = descend G D v := if_pos h

theorem descendCol_of_far {D : Fin N → ℕ} {d : ℕ} {v : Fin N}
    (h : ¬ D v ≤ d) : descendCol G D d v = [] := if_neg h

/-- Length cells fit the schedule bound (`mcB` routing: `≤ d + 1`). -/
theorem descendCol_length_le {s : Fin N} {d : ℕ} {D : Fin N → ℕ}
    (hD : BallTable G s d D) (v : Fin N) :
    (descendCol G D d v).length ≤ d + 1 := by
  rw [descendCol]
  split
  · rw [length_descend hD ‹_›]
    omega
  · simp

end Abstract

/-! ## §3 The canonical truncated distance table (was `SolveMachPrep` §1) -/

open Classical in
/-- **The canonical truncated distance table** of one source at cap
`d`: the least radius reaching `v`, or `d + 1` beyond the horizon —
the unique table `bfsCom` can leave (`ballTable_eq_ballDist`). -/
noncomputable def ballDist {N : ℕ} (H : SimpleGraph (Fin N)) (s : Fin N)
    (d : ℕ) (v : Fin N) : ℕ :=
  if v ∈ ball H d s then sInf {k | v ∈ ball H k s} else d + 1

open Classical in
/-- The canonical table respects the horizon bound — the `≤ d + 1`
clause of `bfsCom_specW`'s deliverable. -/
theorem ballDist_le {N : ℕ} (H : SimpleGraph (Fin N)) (s : Fin N) (d : ℕ)
    (v : Fin N) : ballDist H s d v ≤ d + 1 := by
  rw [ballDist]
  by_cases hv : v ∈ ball H d s
  · rw [if_pos hv]
    exact le_trans (Nat.sInf_le hv) (Nat.le_succ d)
  · rw [if_neg hv]

open Classical in
/-- The canonical table is a `BallTable` — the other half of
`bfsCom_specW`'s deliverable. -/
theorem ballDist_ballTable {N : ℕ} (H : SimpleGraph (Fin N)) (s : Fin N)
    (d : ℕ) : Impl.BallTable H s d (ballDist H s d) := by
  intro v k hk
  by_cases hv : v ∈ ball H d s
  · rw [ballDist, if_pos hv]
    constructor
    · intro hle
      have hmem : v ∈ ball H (sInf {k | v ∈ ball H k s}) s :=
        Nat.sInf_mem (⟨d, hv⟩ : {k | v ∈ ball H k s}.Nonempty)
      exact ball_mono_radius H s hle hmem
    · intro hkm
      exact Nat.sInf_le hkm
  · rw [ballDist, if_neg hv]
    constructor
    · intro h
      exact absurd hk (by omega)
    · intro hkm
      exact absurd (ball_mono_radius H s hk hkm) hv

open Classical in
/-- **Uniqueness**: any table satisfying `BallTable` with the horizon
bound — verbatim what `bfsCom_specW` leaves in the distance region —
*is* the canonical table. This is what makes the pass's stored channel
independent of the run that produced it. -/
theorem ballTable_eq_ballDist {N : ℕ} {H : SimpleGraph (Fin N)}
    {s : Fin N} {d : ℕ} {D : Fin N → ℕ} (hD : Impl.BallTable H s d D)
    (hle : ∀ v, D v ≤ d + 1) : D = ballDist H s d := by
  funext v
  by_cases hv : v ∈ ball H d s
  · rw [ballDist, if_pos hv]
    have h1 : D v ≤ d := (hD v d le_rfl).mpr hv
    have h2 : v ∈ ball H (D v) s := (hD v (D v) h1).mp le_rfl
    have h3 : sInf {k | v ∈ ball H k s} ≤ D v := Nat.sInf_le h2
    have hmem : v ∈ ball H (sInf {k | v ∈ ball H k s}) s :=
      Nat.sInf_mem (⟨d, hv⟩ : {k | v ∈ ball H k s}.Nonempty)
    have h4 : D v ≤ sInf {k | v ∈ ball H k s} :=
      (hD v _ (le_trans h3 h1)).mpr hmem
    omega
  · rw [ballDist, if_neg hv]
    have h1 : ¬ D v ≤ d := fun h => hv ((hD v d le_rfl).mp h)
    have h2 := hle v
    omega

end Lax3Proofs.Prog
