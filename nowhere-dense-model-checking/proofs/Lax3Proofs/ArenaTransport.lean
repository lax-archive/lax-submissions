import Lax3Proofs.ReachedS
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Embedding

/-!
Carrier transport for the recorded game `Lax3Proofs.ReachedS` — leaf E6,
the gap of `algorithm-v2.md` §9 (third bullet) and D1 (`:125-141`).

# The gap

D1 materializes each child arena as a fresh compact structure on `Fin N`
with its own numbering, while every lemma of the correctness chain keeps
the carrier — `deleteVerts` isolates, it does not remove
(`Lax12/UniformQuasiWideness.lean:54-57`). The recorded game types its
arenas on one fixed carrier: `RoundS n` fixes `arena : SimpleGraph (Fin n)`
and `ReachedS r G rounds A` types `G`, every recorded arena, and `A` on
that same `Fin n`. §5 line 8's `# pre:` therefore does not typecheck
against a renumbered child; this file supplies the transports and the
verdict (final section) on what that line must say.

# The one pushforward

Everything is stated for a single operation: `SimpleGraph.map f` along an
arbitrary embedding `f : Fin n ↪ Fin m`, and the round map `mapRound f`
pushing a recorded round through it. This one spelling covers both
transports the design needs, because `SimpleGraph.map` puts **no edge
outside the range of `f`** — the added vertices are isolated in the
graph, exactly the way `deleteVerts` leaves its carrier:

* **renumbering along a bijection** is the case `f = σ.toEmbedding` for
  `σ : Fin n ≃ Fin m` — `reachedS_map_equiv` states it in the abstract
  `G' + hAdj` form that `Compaction` uses, because D1's compact
  structures come with their own adjacency and only an
  adjacency-matching condition relates them; `eq_map_of_equiv` pins such
  a `G'` down as the pushforward, so the abstract form is the concrete
  one in disguise;
* **adding isolated vertices** is the case of a non-surjective `f` —
  `reachedS_extend` in the abstract agree-and-isolated form, with
  `Fin.castLEEmb` (the design's padding) as the named instance
  `reachedS_extend_castLE`. A general embedding rather than `castLE`
  because the child-to-root composite of the design's `up` maps is a
  monotone injection onto a cluster, not an initial segment.

Not `SimpleGraph.map σ.toEmbedding` *versus* an abstract pair — both:
the concrete `reachedS_map`/`reachedS_restrict` are the workhorses, the
abstract corollaries are their interface to structures that arrive as
`G' + hAdj`.

# The crux

The hazard of the isolated-vertex direction is that `(f '' s)ᶜ` is not
`f '' sᶜ` for a non-surjective `f`. It never bites, for the one reason
the design relies on: **no edge of a pushforward leaves the range**
(`exists_of_map_adj`), so a vertex outside the range is isolated and no
walk reaches it. That is `ball_map` — the ball of the pushforward is
exactly the image of the ball, with nothing outside the range —
and it is what makes `nextArenaS` commute with the round map
(`nextArenaS_mapRound`): on the range, membership in an image and in its
complement reads through `f.injective`; off the range there are no edges
for `deleteVerts` to act on.

The walk lemmas are reproved here in the dozen lines each takes —
`Compaction.exists_walk_push`/`exists_walk_pull` are `private`, and are
in any case stated against a bijection with a subtype, not an embedding
of `Fin` carriers. `exists_walk_push` maps a walk edge by edge through
the embedding; `exists_walk_pull` produces its far endpoint itself —
a walk of the pushforward starting in the range never leaves it — which
is what makes `ball_map` a two-line consequence.

Both directions of the transport land: `reachedS_map` forward,
`reachedS_restrict` (and its applied form `reachedS_of_map`) backward.
The transports compose with `reachedS_descend`, which never leaves the
carrier: a driver keeps the record at the root, extends it by
`reachedS_descend`, and identifies the reached arena with the mapped
compact child by `nextArenaS_mapRound` — see the final section.
-/

namespace Lax3Proofs.ArenaTransport

open Lax3.ColoredGraphs
open Lax12.UniformQuasiWideness
open Lax3Proofs.SplitterBasics Lax3Proofs.WalkDistance Lax3Proofs.ReachedS

variable {n m r : ℕ}

/-! ### Walks through an embedding

A pushforward `G.map f` has an edge only between images of neighbours,
so its walks from an image vertex are images of walks — pushing is
Mathlib's `Walk.map` along the evident homomorphism, and pulling
recovers the preimage walk vertex by vertex, discovering along the way
that the far endpoint lies in the range. Both keep the length on the
nose.
-/

section Walks

variable (f : Fin n ↪ Fin m) {G : SimpleGraph (Fin n)}

/-- Every edge of a pushforward is the image of an edge: both endpoints
lie in the range of the embedding, so the vertices added by a
non-surjective embedding are **isolated** — present in the carrier,
carrying no edge. -/
theorem exists_of_map_adj {x y : Fin m} (h : (G.map f).Adj x y) :
    ∃ a b : Fin n, G.Adj a b ∧ f a = x ∧ f b = y :=
  (SimpleGraph.map_adj f G x y).mp h

/-- A walk pushes through the embedding edge by edge, at the same
length; every vertex of the image is the image of a vertex of the
original support. -/
theorem exists_walk_push {u v : Fin n} (p : G.Walk u v) :
    ∃ q : (G.map f).Walk (f u) (f v), q.length = p.length ∧
      ∀ z ∈ q.support, ∃ w ∈ p.support, f w = z := by
  induction p with
  | @nil a =>
    refine ⟨.nil, rfl, fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact ⟨a, by simp, hz.symm⟩
  | @cons a b c hab p ih =>
    obtain ⟨q, hqlen, hqsupp⟩ := ih
    refine ⟨.cons (SimpleGraph.map_adj_apply.mpr hab) q, by simp [hqlen],
      fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz'
    · exact ⟨a, by simp, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := hqsupp z hz'
      exact ⟨w, by simp [hw], rfl⟩

/-- A distance bound pushes through the embedding. -/
theorem withinDist_map {d : ℕ} {u v : Fin n} (h : WithinDist G d u v) :
    WithinDist (G.map f) d (f u) (f v) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hqlen, -⟩ := exists_walk_push f p
  exact ⟨q, hqlen.trans_le hp⟩

/-- A walk of the pushforward starting in the range pulls back, at the
same length: each edge is the image of an edge, so the walk never leaves
the range and its far endpoint is an image too. The endpoint is
*produced*, not assumed — this is what the ball identity below reads
off. -/
theorem exists_walk_pull {x y : Fin m} (q : (G.map f).Walk x y) {a : Fin n}
    (hax : f a = x) :
    ∃ (b : Fin n) (p : G.Walk a b), f b = y ∧ p.length = q.length ∧
      ∀ z ∈ p.support, f z ∈ q.support := by
  induction q generalizing a with
  | nil =>
    refine ⟨a, .nil, hax, rfl, fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact hax
  | @cons x c y hxc q ih =>
    obtain ⟨a₁, c', hac, ha₁, hc'⟩ := exists_of_map_adj f hxc
    obtain rfl : a₁ = a := f.injective (ha₁.trans hax.symm)
    obtain ⟨b, p, hby, hlen, hsupp⟩ := ih hc'
    refine ⟨b, .cons hac p, hby, by simp [hlen], fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons]
    rcases hz with rfl | hz'
    · exact Or.inl hax
    · exact Or.inr (hsupp z hz')

/-- Distance bounds between range vertices are blind to the embedding. -/
theorem withinDist_map_iff {d : ℕ} {u v : Fin n} :
    WithinDist (G.map f) d (f u) (f v) ↔ WithinDist G d u v := by
  refine ⟨fun h => ?_, withinDist_map f⟩
  obtain ⟨q, hq⟩ := h
  obtain ⟨b, p, hb, hlen, -⟩ := exists_walk_pull f q rfl
  obtain rfl : b = v := f.injective hb
  exact ⟨p, hlen.trans_le hq⟩

/-- **The crux of the isolated-vertex transport.** The ball of a
pushforward around an image vertex is exactly the image of the ball:
no walk leaves the range, because a vertex off the range carries no
edge. This is the statement that fails for a carrier extension that is
*not* isolated off the range, and it is why `ball` transports along
embeddings-with-isolated-rest and not merely along bijections. -/
theorem ball_map (G : SimpleGraph (Fin n)) (d : ℕ) (v : Fin n) :
    ball (G.map f) d (f v) = f '' ball G d v := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := mem_ball.mp hx
    obtain ⟨b, p, hb, hlen, -⟩ := exists_walk_pull f q rfl
    exact ⟨b, mem_ball.mpr ⟨p, hlen.trans_le hq⟩, hb⟩
  · rintro ⟨u, hu, rfl⟩
    exact mem_ball.mpr (withinDist_map f (mem_ball.mp hu))

end Walks

/-! ### Pushing a round -/

section RoundMap

variable (f : Fin n ↪ Fin m)

/-- A recorded round, pushed through an embedding of carriers: the
vertex through the map, the arena through the pushforward, the
restriction and generating sets through the image. -/
def mapRound (e : RoundS n) : RoundS m :=
  ⟨f e.vtx, e.arena.map f, f '' e.res, f '' e.gen⟩

@[simp] theorem mapRound_vtx (e : RoundS n) : (mapRound f e).vtx = f e.vtx := rfl

@[simp] theorem mapRound_arena (e : RoundS n) :
    (mapRound f e).arena = e.arena.map f := rfl

@[simp] theorem mapRound_res (e : RoundS n) : (mapRound f e).res = f '' e.res := rfl

@[simp] theorem mapRound_gen (e : RoundS n) : (mapRound f e).gen = f '' e.gen := rfl

/-- The batch of a pushed round is the image of the batch: images along
an injection commute with the intersection `gen ∩ res`. -/
theorem batchS_mapRound (e : RoundS n) :
    batchS (mapRound f e) = f '' batchS e :=
  (Set.image_inter f.injective).symm

/-- **The after-arena commutes with the round map.** This is where the
hazard `(f '' s)ᶜ ≠ f '' sᶜ` would bite and does not: on the range,
membership in `f '' e.res` and in the batch image reads through
`f.injective`; off the range the extra vertices of `(f '' e.res)ᶜ` are
already isolated in the pushforward, so deleting them changes no edge. -/
theorem nextArenaS_mapRound (e : RoundS n) :
    nextArenaS (mapRound f e) = (nextArenaS e).map f := by
  ext x y
  constructor
  · intro h
    obtain ⟨h1, hxb, hyb⟩ := deleteVerts_adj.mp h
    obtain ⟨hadj, hxr, hyr⟩ := deleteVerts_adj.mp h1
    obtain ⟨a, b, hab, rfl, rfl⟩ := exists_of_map_adj f hadj
    have har : a ∈ e.res := f.injective.mem_set_image.mp (Set.notMem_compl_iff.mp hxr)
    have hbr : b ∈ e.res := f.injective.mem_set_image.mp (Set.notMem_compl_iff.mp hyr)
    have hanb : a ∉ batchS e := fun hmem => hxb (by
      rw [batchS_mapRound]
      exact Set.mem_image_of_mem f hmem)
    have hbnb : b ∉ batchS e := fun hmem => hyb (by
      rw [batchS_mapRound]
      exact Set.mem_image_of_mem f hmem)
    exact SimpleGraph.map_adj_apply.mpr
      (deleteVerts_adj.mpr ⟨deleteVerts_adj.mpr ⟨hab, Set.notMem_compl_iff.mpr har,
        Set.notMem_compl_iff.mpr hbr⟩, hanb, hbnb⟩)
  · intro h
    obtain ⟨a, b, hab, rfl, rfl⟩ := exists_of_map_adj f h
    obtain ⟨h1, hanb, hbnb⟩ := deleteVerts_adj.mp hab
    obtain ⟨hadj, har, hbr⟩ := deleteVerts_adj.mp h1
    refine deleteVerts_adj.mpr ⟨deleteVerts_adj.mpr ⟨SimpleGraph.map_adj_apply.mpr hadj,
      Set.notMem_compl_iff.mpr (Set.mem_image_of_mem f (Set.notMem_compl_iff.mp har)),
      Set.notMem_compl_iff.mpr (Set.mem_image_of_mem f (Set.notMem_compl_iff.mp hbr))⟩,
      fun hmem => hanb ?_, fun hmem => hbnb ?_⟩
    · rw [batchS_mapRound] at hmem
      exact f.injective.mem_set_image.mp hmem
    · rw [batchS_mapRound] at hmem
      exact f.injective.mem_set_image.mp hmem

end RoundMap

/-! ### The transport, both ways -/

section Transport

variable (f : Fin n ↪ Fin m) {G A : SimpleGraph (Fin n)} {rounds : List (RoundS n)}

/-- **Forward transport along any embedding.** A play on the small
carrier is a play on the pushforward, round by round; the vertices a
non-surjective embedding adds are isolated in every pushed arena, so
they are `exU`-visible dead carrier — exactly what `deleteVerts` leaves
behind — and no clause of `ReachedS.step` sees them. The bijection case
is `f = σ.toEmbedding`; the isolated-extension case is any other `f`. -/
theorem reachedS_map (h : ReachedS r G rounds A) :
    ReachedS r (G.map f) (rounds.map (mapRound f)) (A.map f) := by
  induction h with
  | nil => exact .nil
  | @step rounds A v X S hh hv hres hself hwalk ih =>
    rw [List.map_cons, ← nextArenaS_mapRound]
    refine ReachedS.step ih ?_ ?_ ?_ ?_
    · obtain ⟨u, hu⟩ := hv
      exact ⟨f u, SimpleGraph.map_adj_apply.mpr hu⟩
    · show f '' X ⊆ ball (A.map f) r (f v)
      rw [ball_map]
      exact Set.image_mono hres
    · exact Set.mem_image_of_mem f hself
    · intro e' he' hwd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      obtain ⟨p, hplen, hpsub⟩ := hwalk e he ((withinDist_map_iff f).mp hwd)
      obtain ⟨q, hqlen, hqsupp⟩ := exists_walk_push f p
      refine ⟨q, hqlen.trans_le hplen, fun z hz => ?_⟩
      obtain ⟨w, hw, rfl⟩ := hqsupp z hz
      exact Set.mem_image_of_mem f (hpsub hw)

/-- **Backward transport.** A play of the pushforward all of whose
rounds are pushed rounds restricts to a play on the small carrier, and
its reached arena is the pushforward of the restricted one. The
inversion is `reachedS_cons` round by round; every clause pulls back
because no walk and no edge of a pushforward leaves the range. -/
theorem reachedS_restrict :
    ∀ {rounds : List (RoundS n)} {A' : SimpleGraph (Fin m)},
      ReachedS r (G.map f) (rounds.map (mapRound f)) A' →
      ∃ A, A' = A.map f ∧ ReachedS r G rounds A := by
  intro rounds
  induction rounds with
  | nil =>
    intro A' h
    cases h
    exact ⟨G, rfl, .nil⟩
  | cons e rest ih =>
    intro A' h
    have h' : ReachedS r (G.map f)
        (⟨f e.vtx, e.arena.map f, f '' e.res, f '' e.gen⟩ :: rest.map (mapRound f)) A' := h
    obtain ⟨h0, hv', hres', hself', hwalk', hA'⟩ := reachedS_cons h'
    obtain ⟨A₀, hEq, hR⟩ := ih h0
    obtain rfl : e.arena = A₀ := SimpleGraph.map_injective f hEq
    refine ⟨nextArenaS e, by rw [hA', ← nextArenaS_mapRound]; rfl, ?_⟩
    have hv : ∃ u, e.arena.Adj e.vtx u := by
      obtain ⟨u', hu'⟩ := hv'
      obtain ⟨a, b, hab, ha, hb⟩ := exists_of_map_adj f hu'
      obtain rfl : a = e.vtx := f.injective ha
      exact ⟨b, hab⟩
    have hres : e.res ⊆ ball e.arena r e.vtx := by
      intro x hx
      have h1 := hres' (Set.mem_image_of_mem f hx)
      rw [ball_map] at h1
      exact f.injective.mem_set_image.mp h1
    have hwalk : ∀ e₀ ∈ rest, WithinDist e₀.arena r e₀.vtx e.vtx →
        ∃ p : e₀.arena.Walk e₀.vtx e.vtx, p.length ≤ r ∧
          {z | z ∈ p.support} ⊆ e.gen := by
      intro e₀ he₀ hwd
      obtain ⟨q, hqlen, hqsub⟩ := hwalk' (mapRound f e₀)
        (List.mem_map_of_mem he₀) (withinDist_map f hwd)
      obtain ⟨b, p, hb, hlen, hsupp⟩ := exists_walk_pull f q rfl
      obtain rfl : b = e.vtx := f.injective hb
      refine ⟨p, hlen.trans_le hqlen, fun z hz => ?_⟩
      exact f.injective.mem_set_image.mp (hqsub (hsupp z hz))
    exact ReachedS.step hR hv hres (f.injective.mem_set_image.mp hself') hwalk

/-- The applied form of the backward transport: a pushed play reaching
the pushed arena restricts on the nose, by injectivity of the
pushforward. -/
theorem reachedS_of_map
    (h : ReachedS r (G.map f) (rounds.map (mapRound f)) (A.map f)) :
    ReachedS r G rounds A := by
  obtain ⟨A₀, hEq, hR⟩ := reachedS_restrict f h
  obtain rfl : A = A₀ := SimpleGraph.map_injective f hEq
  exact hR

end Transport

/-! ### Renumbering along a bijection, in the form D1's structures come in -/

section Bijection

variable (σ : Fin n ≃ Fin m) {G A : SimpleGraph (Fin n)}
  {G' A' : SimpleGraph (Fin m)} {rounds : List (RoundS n)}

/-- Along a bijection, an adjacency-matching condition pins the big
graph down as the pushforward: surjectivity leaves no vertex whose
edges the condition does not determine. This is what makes the abstract
`G' + hAdj` interface below the concrete transport in disguise. -/
theorem eq_map_of_equiv (hAdj : ∀ a b : Fin n, G'.Adj (σ a) (σ b) ↔ G.Adj a b) :
    G' = G.map σ.toEmbedding := by
  ext x y
  obtain ⟨a, rfl⟩ := σ.surjective x
  obtain ⟨b, rfl⟩ := σ.surjective y
  rw [hAdj a b]
  exact (SimpleGraph.map_adj_apply (f := σ.toEmbedding)).symm

/-- **Renumbering the recorded game along a bijection.** Stated as
`Compaction` states its transport: the renumbered graphs arrive as data
`G'`, `A'` together with adjacency-matching conditions through `σ`, not
as pushforward terms — D1's compact structures carry their own
adjacency. No order or monotonicity of `σ` enters. -/
theorem reachedS_map_equiv
    (hG : ∀ a b : Fin n, G'.Adj (σ a) (σ b) ↔ G.Adj a b)
    (hA : ∀ a b : Fin n, A'.Adj (σ a) (σ b) ↔ A.Adj a b)
    (h : ReachedS r G rounds A) :
    ReachedS r G' (rounds.map (mapRound σ.toEmbedding)) A' := by
  rw [eq_map_of_equiv σ hG, eq_map_of_equiv σ hA]
  exact reachedS_map σ.toEmbedding h

/-- The inverse renumbering: a play of the renumbered graph whose rounds
are pushed rounds is a play of the original, reaching an arena the
pushforward of the original's. -/
theorem reachedS_restrict_equiv
    (hG : ∀ a b : Fin n, G'.Adj (σ a) (σ b) ↔ G.Adj a b)
    (h : ReachedS r G' (rounds.map (mapRound σ.toEmbedding)) A') :
    ∃ A, A' = A.map σ.toEmbedding ∧ ReachedS r G rounds A := by
  rw [eq_map_of_equiv σ hG] at h
  exact reachedS_restrict σ.toEmbedding h

end Bijection

/-! ### Adding isolated vertices -/

section IsolatedExtension

variable {G A : SimpleGraph (Fin n)} {rounds : List (RoundS n)}

/-- A big graph that agrees with the small one under the embedding and
has every edge endpoint in the range — the added vertices isolated in
the *graph*, not merely renamed — is the pushforward. The second
hypothesis is the isolation clause; without it the extension is a
different graph and the transport is false. -/
theorem eq_map_of_isolated (f : Fin n ↪ Fin m) {G' : SimpleGraph (Fin m)}
    (hAgree : ∀ a b : Fin n, G'.Adj (f a) (f b) ↔ G.Adj a b)
    (hRange : ∀ x y : Fin m, G'.Adj x y → ∃ a, f a = x) :
    G' = G.map f := by
  ext x y
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := hRange x y h
    obtain ⟨b, rfl⟩ := hRange y (f a) h.symm
    exact SimpleGraph.map_adj_apply.mpr ((hAgree a b).mp h)
  · intro h
    obtain ⟨a, b, hab, rfl, rfl⟩ := exists_of_map_adj f h
    exact (hAgree a b).mpr hab

/-- **Adding isolated vertices, forward.** A play on the small carrier
is a play on any extension that agrees under the embedding and is
isolated outside its range. The inverse direction is
`reachedS_restrict`/`reachedS_of_map` after `eq_map_of_isolated`
rewrites the extension as the pushforward. -/
theorem reachedS_extend (f : Fin n ↪ Fin m) {G' A' : SimpleGraph (Fin m)}
    (hG : ∀ a b : Fin n, G'.Adj (f a) (f b) ↔ G.Adj a b)
    (hGr : ∀ x y : Fin m, G'.Adj x y → ∃ a, f a = x)
    (hA : ∀ a b : Fin n, A'.Adj (f a) (f b) ↔ A.Adj a b)
    (hAr : ∀ x y : Fin m, A'.Adj x y → ∃ a, f a = x)
    (h : ReachedS r G rounds A) :
    ReachedS r G' (rounds.map (mapRound f)) A' := by
  rw [eq_map_of_isolated f hG hGr, eq_map_of_isolated f hA hAr]
  exact reachedS_map f h

/-- The design's padding instance: extending the carrier along
`Fin.castLE`, the new vertices isolated. -/
theorem reachedS_extend_castLE (hnm : n ≤ m) (h : ReachedS r G rounds A) :
    ReachedS r (G.map (Fin.castLEEmb hnm))
      (rounds.map (mapRound (Fin.castLEEmb hnm))) (A.map (Fin.castLEEmb hnm)) :=
  reachedS_map (Fin.castLEEmb hnm) h

end IsolatedExtension

/-! ### The verdict on §5 line 8

`algorithm-v2.md` §5 line 8 reads

    8      # pre:  ReachedR 2R G rounds A  — a record of the play so far

At a renumbered child this does **not** typecheck, and no lemma of this
file (or any file) makes it: the three arguments of `ReachedS` — the
start graph, every recorded arena, and the reached arena — share one
carrier `Fin n`, while D1's child is `A : SimpleGraph (Fin N_j)`. A
precondition naming the root graph and the compact child in one
`ReachedS` instance is a type error, not a missing lemma. §5 must be
rewritten; the record is kept at the **root** carrier, and the line
should read:

    8      # pre:  ReachedS 2R G₀ hist (map upᵣ A)
    8      #       — hist : List (RoundS n₀) on the root carrier n₀; G₀ the
    8      #         root arena; upᵣ : Fin A.N ↪ Fin n₀ the composite of the
    8      #         `up` maps to the root; the record is never re-typed

(`ReachedS`, not `ReachedR`: the cluster restriction of §9 O1/O5 is the
already-landed generalization.) The invariant closes without ever
re-typing the record:

* at the root call (line 3), `upᵣ` is the identity embedding,
  `map id A = G₀`, and the precondition is `ReachedS.nil`;
* at the recursive call (line 24), the parent extends `hist` through
  `reachedS_descend` — which lives entirely on the root carrier, so the
  transports compose with it by never being needed in the step — and
  identifies the arena `reachedS_descend` reaches with `map upᵣ' B` of
  the child by `nextArenaS_mapRound` together with the restrict/isolate
  identity `map emb B = deleteVerts (deleteVerts A_par X_uᶜ) W` — the
  latter is the program's own specification of lines 16 and 21, D1's
  other half, owed by the implementation layer, not by the game;
* a driver that genuinely re-types a whole record — e.g. assembling a
  sub-play on the child carrier — moves it by `reachedS_map` /
  `reachedS_restrict` along the embedding, or `reachedS_map_equiv` along
  a renumbering bijection.
-/

end Lax3Proofs.ArenaTransport
