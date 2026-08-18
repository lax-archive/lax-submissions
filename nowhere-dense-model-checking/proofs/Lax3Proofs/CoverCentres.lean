import Lax3Proofs.OrderedCovers

/-!
Named centres for the ordered cover: the function `ctr` the cover
routine must return alongside its clusters, and the `π`-min identity
that makes it the centre the covering condition talks about.

`IsNeighborhoodCover.ball_subset` is an existential — it says *some*
cluster contains the `r`-ball of `v`, and hands back no way to name it.
The construction of `OrderedCovers.isNeighborhoodCover_wreach` does
better than its own statement: the cluster it exhibits is the one
centred at a `π`-minimal vertex of `ball G r v`. This file turns that
witness into a function of `v`.

The definition is taken on the *weak reachability* set rather than the
ball — `ctr G π r v` is the `π`-minimal element of `wreach G π r v`,
which is what the cover routine already computes, fibre by fibre. The
identity that licenses the swap is the content of the file:

* `wreach G π r v ⊆ ball G r v`, dropping the minimality clause; and
* a `π`-minimal vertex of `ball G r v` lies in `wreach G π r v`,
  because every vertex on a walk of length at most `r` out of `v` is
  itself within distance `r` of `v`, hence in the ball, where the
  minimum is minimal — and that is exactly `wreach`'s third conjunct.

So the two `π`-minima coincide (`eq_ctr_of_min_ball`), and the
containment the design consumes,

    ball G r v ⊆ {w | ctr G π r v ∈ wreach G π (2 * r) w},

is the covering argument of `isNeighborhoodCover_wreach` with the
existential centre replaced by `ctr`. Note the two radii: `ctr` is taken
at radius `r`, the clusters at `2 * r`.

This is Grohe–Kreutzer–Siebertz's own algorithm rather than a repair of
it: the Remark following their Theorem 6.2 associates with `v` the
cluster of the `<`-minimal `u` with `v ∈ N_r^{G∖S(u)}(u)`, and their
Claim identifies `X_r[G,<,u]` with `N_r^{G∖S(u)}(u)`, so that `u` is the
`π`-minimal vertex weakly `r`-reachable from `v`.
-/

namespace Lax3Proofs.CoverCentres

open Lax3.ColoredGraphs
open Lax3.NeighborhoodCovers
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance
open Lax3Proofs.CoverConstruction
open Lax3Proofs.OrderedCovers

variable {n : ℕ}

/-! ### Support vertices of a short walk

`CoverConstruction.withinDist_of_mem_support` is `private`, so it is
restated here; it is public in this namespace, being needed by both the
`wreach`/`ball` comparison and the covering argument. -/

/-- Every vertex on a walk of length at most `r` is within distance `r`
of both endpoints: cutting the walk at that vertex splits its length. -/
theorem withinDist_of_mem_support {V : Type*} {G : SimpleGraph V} {a b : V}
    {r : ℕ} (p : G.Walk a b) (hp : p.length ≤ r) {y : V} (hy : y ∈ p.support) :
    WithinDist G r a y ∧ WithinDist G r y b := by
  classical
  have hlen := congrArg SimpleGraph.Walk.length (p.take_spec hy)
  rw [SimpleGraph.Walk.length_append] at hlen
  exact ⟨⟨p.takeUntil y hy, by omega⟩, ⟨p.dropUntil y hy, by omega⟩⟩

/-! ### The centre function -/

/-- A vertex is weakly `r`-reachable from itself, along the empty
walk. -/
theorem self_mem_wreach (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : v ∈ wreach G π r v :=
  mem_wreach_iff.mpr ⟨SimpleGraph.Walk.nil, by simp, by simp⟩

/-- The `π`-image of a weak reachability set is a nonempty finite set of
positions, so it has a least element. -/
theorem wreach_image_nonempty (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : (((Set.toFinite (wreach G π r v)).toFinset).image π).Nonempty :=
  ⟨π v, Finset.mem_image.mpr
    ⟨v, (Set.Finite.mem_toFinset _).mpr (self_mem_wreach G π r v), rfl⟩⟩

/-- **The centre of `v`**: the `π`-minimal vertex weakly `r`-reachable
from `v`. This is the cluster centre the cover routine returns for `v`,
computed from the same weak reachability fibres the cover itself is
built from. -/
noncomputable def ctr (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : Fin n :=
  π.symm ((((Set.toFinite (wreach G π r v)).toFinset).image π).min'
    (wreach_image_nonempty G π r v))

/-- The `π`-position of the centre is the least position occurring in
the weak reachability set. -/
theorem apply_ctr (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ) (v : Fin n) :
    π (ctr G π r v) =
      (((Set.toFinite (wreach G π r v)).toFinset).image π).min'
        (wreach_image_nonempty G π r v) :=
  π.apply_symm_apply _

/-- **First characterising property**: the centre of `v` is weakly
`r`-reachable from `v`. -/
theorem ctr_mem_wreach (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : ctr G π r v ∈ wreach G π r v := by
  obtain ⟨u, hu, hpu⟩ :=
    Finset.mem_image.mp (Finset.min'_mem _ (wreach_image_nonempty G π r v))
  have hcu : ctr G π r v = u := π.injective (by rw [apply_ctr, hpu])
  exact hcu ▸ (Set.Finite.mem_toFinset _).mp hu

/-- **Second characterising property**: the centre of `v` is `π`-minimal
in the weak reachability set of `v`. -/
theorem ctr_le_of_mem_wreach {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {r : ℕ}
    {v u : Fin n} (hu : u ∈ wreach G π r v) : π (ctr G π r v) ≤ π u := by
  rw [apply_ctr]
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨u, (Set.Finite.mem_toFinset _).mpr hu, rfl⟩)

/-! ### The `π`-min identity

The `π`-minimum of `wreach G π r v` is also the `π`-minimum of
`ball G r v`, so `ctr` may equally be read off the balls — which is the
form the existence proof of the cover uses — or off the weak
reachability fibres, which is the form the algorithm computes. -/

/-- Weak reachability implies reachability: dropping the minimality
clause from a weak reachability walk leaves a walk of length at most
`r`. -/
theorem wreach_subset_ball (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : wreach G π r v ⊆ ball G r v := by
  intro u hu
  obtain ⟨p, hp, -⟩ := mem_wreach_iff.mp hu
  exact mem_ball.mpr ⟨p, hp⟩

/-- The other half of the identity: a `π`-minimal vertex of the
`r`-ball of `v` is weakly `r`-reachable from `v`. Every vertex on a
walk from `v` of length at most `r` lies in that ball, so minimality
over the ball delivers `wreach`'s minimality-over-the-support
clause. -/
theorem mem_wreach_of_min_ball {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {r : ℕ}
    {v u : Fin n} (hu : u ∈ ball G r v) (hmin : ∀ y ∈ ball G r v, π u ≤ π y) :
    u ∈ wreach G π r v := by
  obtain ⟨q, hq⟩ := mem_ball.mp hu
  exact mem_wreach_iff.mpr
    ⟨q, hq, fun y hy => hmin y (mem_ball.mpr (withinDist_of_mem_support q hq hy).1)⟩

/-- The centre of `v` lies in the `r`-ball of `v`. -/
theorem ctr_mem_ball (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (v : Fin n) : ctr G π r v ∈ ball G r v :=
  wreach_subset_ball G π r v (ctr_mem_wreach G π r v)

/-- **The `π`-min identity.** The centre of `v` is `π`-minimal not only
in the weak reachability set of `v` but in the whole `r`-ball of `v`.

Take a `π`-minimal vertex `u` of the ball, which is finite and contains
`v`. It is weakly `r`-reachable from `v` by `mem_wreach_of_min_ball`, so
the centre is `π`-below it, and it is `π`-below everything in the
ball. -/
theorem ctr_le_of_mem_ball {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {r : ℕ}
    {v y : Fin n} (hy : y ∈ ball G r v) : π (ctr G π r v) ≤ π y := by
  classical
  obtain ⟨u, huF, hmin⟩ :=
    Finset.exists_min_image (Set.toFinite (ball G r v)).toFinset (fun x => π x)
      ⟨v, (Set.Finite.mem_toFinset _).mpr (mem_ball_self G r v)⟩
  have hu : u ∈ ball G r v := (Set.Finite.mem_toFinset _).mp huF
  have hmin' : ∀ z ∈ ball G r v, π u ≤ π z :=
    fun z hz => hmin z ((Set.Finite.mem_toFinset _).mpr hz)
  exact le_trans (ctr_le_of_mem_wreach (mem_wreach_of_min_ball hu hmin')) (hmin' y hy)

/-- The identity in its sharpest form: *the* `π`-minimal vertex of the
`r`-ball of `v` is the centre of `v`. The two `π`-minima of the
statement — over `wreach G π r v` and over `ball G r v` — coincide. -/
theorem eq_ctr_of_min_ball {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {r : ℕ}
    {v u : Fin n} (hu : u ∈ ball G r v) (hmin : ∀ y ∈ ball G r v, π u ≤ π y) :
    u = ctr G π r v :=
  π.injective (le_antisymm (hmin _ (ctr_mem_ball G π r v)) (ctr_le_of_mem_ball hu))

/-! ### Covering with a named centre -/

/-- **The containment the cover routine owes.** The `r`-ball of `v` is
contained in the cluster of `ctr G π r v` — the fibre of weak
`2r`-reachability over that vertex. This is the covering condition of
`OrderedCovers.isNeighborhoodCover_wreach` with the existential centre
replaced by a function of `v`.

The radii differ: the centre is the `π`-minimum at radius `r`, while
the clusters are taken at radius `2 * r`. A vertex `w` in the `r`-ball
of `v` reaches the centre by going back to `v` and out again — a walk of
length at most `2 * r` whose support stays inside the `r`-ball of `v`,
where the centre is `π`-minimal by the identity above. -/
theorem ball_subset_cluster_ctr (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) :
    ball G r v ⊆ {w | ctr G π r v ∈ wreach G π (2 * r) w} := by
  intro w hw
  obtain ⟨p, hp⟩ := mem_ball.mp hw
  obtain ⟨q, hq⟩ := mem_ball.mp (ctr_mem_ball G π r v)
  have hpr : p.reverse.length ≤ r := by
    rw [SimpleGraph.Walk.length_reverse]; exact hp
  refine mem_wreach_iff.mpr ⟨p.reverse.append q, ?_, fun y hy => ?_⟩
  · rw [SimpleGraph.Walk.length_append]; omega
  · refine ctr_le_of_mem_ball ?_
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hy with hy | hy
    · exact mem_ball.mpr (withinDist_symm (withinDist_of_mem_support p.reverse hpr hy).2)
    · exact mem_ball.mpr (withinDist_of_mem_support q hq hy).1

/-- **The cover with its centres.** For any ordering `π` whose weak
`2r`-reachability sets have at most `k` elements, the fibres of weak
`2r`-reachability form an `r`-neighborhood cover of radius `2 * r` and
degree `k` — and `ctr G π r` names, for each `v`, a cluster containing
the `r`-ball of `v`. This is the pair the cover routine returns. -/
theorem isNeighborhoodCover_wreach_ctr (G : SimpleGraph (Fin n)) (r k : ℕ)
    (π : Equiv.Perm (Fin n)) (hk : ∀ v, (wreach G π (2 * r) v).ncard ≤ k) :
    IsNeighborhoodCover G r (fun u => {w | u ∈ wreach G π (2 * r) w}) k ∧
      ∀ v : Fin n, ball G r v ⊆ (fun u => {w | u ∈ wreach G π (2 * r) w}) (ctr G π r v) :=
  ⟨isNeighborhoodCover_wreach G r k π hk, ball_subset_cluster_ctr G π r⟩

end Lax3Proofs.CoverCentres
