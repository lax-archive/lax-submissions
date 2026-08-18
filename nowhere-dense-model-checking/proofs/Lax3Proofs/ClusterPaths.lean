import Lax3Proofs.CoverConstruction
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
Cover clusters are path-closed: the fourth guarantee the model-checking
algorithm needs from its neighborhood cover, and which the endorsed
`IsNeighborhoodCover` does not carry.

The clusters of `OrderedCovers.isNeighborhoodCover_wreach` are the
*fibers* of weak reachability, `X u = {w | u ∈ wreach G π r w}` — the set
of vertices from which `u` is weakly `r`-reachable.  Note the direction:
the fiber fixes `u` and varies `w`, and membership `w ∈ X u` unfolds to a
walk **from `w` to `u`**.

A cluster is closed under passing to the support of its own witnessing
walks.  Take `w ∈ X u` and a witness `p : G.Walk w u` of length at most
`r` all of whose support is `π`-above `u`.  For `z ∈ p.support`, the
walk `p.dropUntil z` runs `z → u`, has support contained in `p.support`
and length at most that of `p`, so the minimality clause `∀ y ∈ support,
π u ≤ π y` — which speaks about the *endpoint* `u`, non-strictly, over the
*whole* support — transfers verbatim and `z ∈ X u`.  Hence `p` never
leaves `X u`.

That is what a caller needs to search *inside* the cluster: `p` lifts to
a walk of the induced graph `G[X u]`, so `u` and every `w ∈ X u` are
joined by a walk of length at most `r` in `G[X u]` itself, and one
parent-recording BFS from `u` inside `G[X u]` reaches all of it within
the cover radius.  Everything here is stated at a general radius `r`; the
algorithm instantiates `r := 2 * R`.
-/

namespace Lax3Proofs.ClusterPaths

open Lax3.ColoredGraphs
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance
open Lax3Proofs.CoverConstruction

variable {n : ℕ} {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {r : ℕ} {u w : Fin n}

/-! ### The fiber -/

/-- Membership in the cluster of `u`, spelled out.  The cluster is the
*fiber* `{w | u ∈ wreach G π r w}` of weak reachability over `u`, not the
reachability set `wreach G π r u`: `w` lies in it exactly when some walk
**from `w` to `u`** of length at most `r` has `u` as a `π`-minimal vertex
of its support. -/
theorem mem_fiber_iff :
    w ∈ {w | u ∈ wreach G π r w} ↔
      ∃ p : G.Walk w u, p.length ≤ r ∧ ∀ y ∈ p.support, π u ≤ π y :=
  Iff.rfl

/-- A vertex lies in its own cluster, witnessed by the empty walk.  The
center is available before any talk of walks *inside* the cluster. -/
theorem self_mem_fiber (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (u : Fin n) : u ∈ {w | u ∈ wreach G π r w} :=
  mem_fiber_iff.mpr ⟨.nil, by simp, by simp⟩

/-! ### Support closure -/

/-- **Cover clusters are path-closed.** A vertex `w` of the cluster of
`u` is joined to `u` by a walk of length at most `r` which never leaves
that cluster.

Take the walk `p : G.Walk w u` witnessing `w ∈ X u`.  For `z` on `p`, the
tail `p.dropUntil z` is a walk `z → u` whose support is contained in
`p.support` and whose length is at most `p.length`; the minimality clause
of `wreach` names the endpoint `u` and quantifies over the whole support,
so it holds for the tail verbatim, and `z ∈ X u`. -/
theorem exists_walk_support_subset_fiber (hw : w ∈ {w | u ∈ wreach G π r w}) :
    ∃ p : G.Walk w u, p.length ≤ r ∧ ∀ z ∈ p.support, z ∈ {w | u ∈ wreach G π r w} := by
  classical
  obtain ⟨p, hlen, hmin⟩ := mem_fiber_iff.mp hw
  refine ⟨p, hlen, fun z hz => mem_fiber_iff.mpr ⟨p.dropUntil z hz, ?_, ?_⟩⟩
  · have hspec := congrArg SimpleGraph.Walk.length (p.take_spec hz)
    rw [SimpleGraph.Walk.length_append] at hspec
    omega
  · exact fun y hy => hmin y (p.support_dropUntil_subset hz hy)

/-! ### Inside the induced graph -/

/-- Lifting a walk to an induced subgraph preserves its length. -/
private theorem length_induce {V : Type*} {G : SimpleGraph V} {S : Set V} {a b : V}
    (p : G.Walk a b) (hp : ∀ x ∈ p.support, x ∈ S) :
    (p.induce S hp).length = p.length := by
  have h := congrArg List.length (SimpleGraph.Walk.support_induce (s := S) p hp)
  simp only [SimpleGraph.Walk.length_support, List.length_attachWith] at h
  omega

/-- **A walk inside the cluster.** Every `w` in the cluster of `u` is
joined to `u` by a walk of length at most `r` *in the graph induced on
that cluster* — not merely by a walk of `G` that happens to stay inside
it.  This is the form a search run inside `G[X u]` consumes. -/
theorem exists_walk_induce_fiber (hw : w ∈ {w | u ∈ wreach G π r w}) :
    ∃ q : (G.induce {w | u ∈ wreach G π r w}).Walk ⟨w, hw⟩
        ⟨u, self_mem_fiber G π r u⟩, q.length ≤ r := by
  obtain ⟨p, hlen, hsub⟩ := exists_walk_support_subset_fiber hw
  exact ⟨p.induce _ hsub, by rw [length_induce]; exact hlen⟩

/-- The cluster of `u` has radius at most `r` around `u` *in its own
induced graph*: `u` is within distance `r` of every `w ∈ X u` inside
`G[X u]`.  This is `exists_walk_induce_fiber` read from the center
outwards, the direction a parent-recording BFS from `u` runs in. -/
theorem withinDist_induce_fiber (hw : w ∈ {w | u ∈ wreach G π r w}) :
    WithinDist (G.induce {w | u ∈ wreach G π r w}) r
      ⟨u, self_mem_fiber G π r u⟩ ⟨w, hw⟩ :=
  withinDist_symm (exists_walk_induce_fiber hw)

end Lax3Proofs.ClusterPaths
