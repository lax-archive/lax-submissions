import Lax3Proofs.SplitterWinRec

/-!
The recorded splitter game of `Lax3Proofs.SplitterWinRec` with the
restriction of each round generalized from the full ball to an arbitrary
recorded set `S ⊆ ball` — the play record of the design's
cluster-restricted recursion (`algorithm-v2.md` §8 step 2, §9 O1/O5).

# Why this file exists

`ReachedR` hard-codes the restriction of each round to the full ball
around Connector's vertex: `nextArenaR` deletes the complement of
`ball e.arena r e.vtx`. The design's recursion instead restricts each
round to a **cluster** `X_u ⊆ ball_{2R}(v)` it computed, and isolates its
marked set inside that cluster. So the round of this file carries the
restriction set as **data**, `res`, next to the vertex, the arena and the
generating set; the after-arena deletes `resᶜ` and then the batch
`gen ∩ res`; and legality of the move — that the cluster really lies
inside the ball of the round — is a clause of `ReachedS.step`,
`res ⊆ ball arena r vtx`, recorded once and retrievable for every played
round (`resS_subset_ball`).

Every invariant of `ReachedR` survives with `res` in the place of the
ball, because none of their proofs ever used more of the ball than that
an edge surviving the round has both ends inside the set the round
restricted to: isolation is permanent (`isolatedS`), a vertex still
carrying an edge lies in the restriction set of every earlier round
(`mem_res_of_roundS`) and hence — through the legality clause — in its
ball, which is what arms the guarded walk clause (`pairS_walk`).
`no_full_survivalS`, `reachedS_no_survival` and `reachedS_length_lt` are
then word for word the ball versions, and `splitterWins_of_reachedS`
closes the same way: the rounds Splitter plays himself restrict to the
full ball, which is a legal `res` (`subset_rfl`), so the recorded history
may mix cluster rounds with his own.

`ReachedR` embeds as the special case `res = ball`: `reachedS_of_reachedR`
maps a ball play to an `S`-play round by round, and `reachedR_of_reachedS`
maps back every `S`-play all of whose rounds recorded the full ball. Both
directions are definitional on the arenas — `batchS`/`nextArenaS` at
`res = ball e.arena r e.vtx` *are* `batchR`/`nextArenaR` — so the two
records are visibly the same game.

As in `ReachedR`, no size clause is imposed on a recorded round: the
extraction never looks at the size of a batch, and the batch bound `m`
enters only through `splitterWins_of_reachedS`, whose own rounds it
measures.

The driver's step is `reachedS_descend`: at a reached position, from a
cluster `X ⊆ ball A r v` and a marked set `W ⊆ X` containing `v` whose
walk clauses hold cut down to `X`, it produces a recorded round whose
batch is **exactly** `W` — the after-arena is
`deleteVerts (deleteVerts A Xᶜ) W` on the nose, not up to a subset.

No tactic in this file is handed a concept-side definition, exactly as in
`SplitterWinRec`.
-/

namespace Lax3Proofs.ReachedS

open Lax3.ColoredGraphs Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.SplitterBasics Lax3Proofs.WalkDistance Lax3Proofs.SplitterWin
open Lax3Proofs.SplitterWinRec

section Play

/-! ### Rounds with a recorded restriction set, batches and arenas -/

variable {n r : ℕ}

/-- One played round of the cluster-restricted recorded game: the vertex
Connector picked, the arena it was picked in, the set the round
restricted the arena to, and the set of vertices Splitter meant to
isolate. Histories are lists of rounds, newest first.

Unlike `RoundR`, the restriction set is data of the round; that it lies
inside the ball of the round is the legality clause of
`ReachedS.step`. -/
structure RoundS (n : ℕ) where
  /-- Connector's vertex. -/
  vtx : Fin n
  /-- The arena the round was played in. -/
  arena : SimpleGraph (Fin n)
  /-- The set the round restricted the arena to. -/
  res : Set (Fin n)
  /-- The vertices Splitter meant to isolate. -/
  gen : Set (Fin n)

/-- What the round isolates: the part of its generating set inside the
set it restricts to. -/
def batchS (e : RoundS n) : Set (Fin n) :=
  e.gen ∩ e.res

/-- The batch lies in the restriction set of the round. -/
theorem batchS_subset_res (e : RoundS n) : batchS e ⊆ e.res :=
  Set.inter_subset_right

/-- Membership in the batch is membership in the generating set and in
the restriction set. -/
theorem mem_batchS {e : RoundS n} {z : Fin n} (hg : z ∈ e.gen)
    (hr : z ∈ e.res) : z ∈ batchS e := ⟨hg, hr⟩

/-- The arena after a round: restrict to the round's recorded set, then
isolate what the round meant to isolate. -/
def nextArenaS (e : RoundS n) : SimpleGraph (Fin n) :=
  deleteVerts (deleteVerts e.arena e.resᶜ) (batchS e)

/-- A round only removes edges. -/
theorem nextArenaS_le (e : RoundS n) : nextArenaS e ≤ e.arena :=
  le_trans (deleteVerts_le _ _) (deleteVerts_le _ _)

/-- Every edge surviving a round has both ends in the set the round
restricted to. -/
theorem mem_res_of_nextArenaS_adj {e : RoundS n} {z w : Fin n}
    (h : (nextArenaS e).Adj z w) : z ∈ e.res :=
  not_not.mp (deleteVerts_adj.mp (deleteVerts_adj.mp h).1).2.1

/-- No edge surviving a round touches the batch. -/
theorem not_mem_batchS_of_nextArenaS_adj {e : RoundS n} {z w : Fin n}
    (h : (nextArenaS e).Adj z w) : z ∉ batchS e :=
  (deleteVerts_adj.mp h).2.1

/-- Playing an isolated vertex loses at once: whatever the round records,
a legal restriction set around such a vertex lies in its ball, which is a
single vertex, so the arena the round leaves is edgeless. -/
theorem nextArenaS_eq_bot_of_isolated {e : RoundS n}
    (hres : e.res ⊆ ball e.arena r e.vtx)
    (hv : ∀ z, ¬ e.arena.Adj e.vtx z) : nextArenaS e = ⊥ := by
  ext z w
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hzw
  have h1 := (deleteVerts_adj.mp hzw).1
  have hz : z = e.vtx := eq_of_mem_ball_of_isolated hv
    (hres (not_not.mp (deleteVerts_adj.mp h1).2.1))
  have hw : w = e.vtx := eq_of_mem_ball_of_isolated hv
    (hres (not_not.mp (deleteVerts_adj.mp h1).2.2))
  subst hz
  subst hw
  exact hv _ (deleteVerts_adj.mp h1).1

/-! ### Reachable positions -/

variable {G : SimpleGraph (Fin n)}

-- The file's namespace and the game share their name by design — the
-- task's pinned interface — so the duplicate-namespace linter is
-- silenced for this declaration.
set_option linter.dupNamespace false in
/-- The positions of a play from `G` in which every Connector move so far
was a vertex that still had an incident edge, every recorded restriction
set was a legal one — inside the ball of the round — and every recorded
generating set is one Splitter's strategy could have meant: it contains
the round's own connector, and, for every earlier round whose arena puts
its connector within `r` of the new one, the support of a walk of length
at most `r` between them in that arena.

This is `ReachedR` with the restriction of a round generalized from the
full ball to the recorded set `X`; moves on isolated vertices are again
not recorded, since they end the play at once
(`nextArenaS_eq_bot_of_isolated`). -/
inductive ReachedS (r : ℕ) (G : SimpleGraph (Fin n)) :
    List (RoundS n) → SimpleGraph (Fin n) → Prop
  | nil : ReachedS r G [] G
  | step {rounds : List (RoundS n)} {A : SimpleGraph (Fin n)} {v : Fin n}
      {X S : Set (Fin n)}
      (h : ReachedS r G rounds A) (hv : ∃ u, A.Adj v u)
      (hres : X ⊆ ball A r v) (hself : v ∈ S)
      (hwalk : ∀ e ∈ rounds, WithinDist e.arena r e.vtx v →
        ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧ {z | z ∈ p.support} ⊆ S) :
      ReachedS r G (⟨v, A, X, S⟩ :: rounds) (nextArenaS ⟨v, A, X, S⟩)

variable {A : SimpleGraph (Fin n)} {rounds : List (RoundS n)}

/-- Inverting a played round: the arena an entry records is the position
its own older rounds reach, its vertex had an incident edge there, its
restriction set was legal, its generating set is one the strategy could
have meant, and the position after it is the round's own next arena. -/
theorem reachedS_cons {v : Fin n} {A₀ : SimpleGraph (Fin n)} {X S : Set (Fin n)}
    (h : ReachedS r G (⟨v, A₀, X, S⟩ :: rounds) A) :
    ReachedS r G rounds A₀ ∧ (∃ u, A₀.Adj v u) ∧ X ⊆ ball A₀ r v ∧ v ∈ S ∧
      (∀ e ∈ rounds, WithinDist e.arena r e.vtx v →
        ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧ {z | z ∈ p.support} ⊆ S) ∧
      A = nextArenaS ⟨v, A₀, X, S⟩ := by
  cases h with
  | step h hv hres hself hwalk => exact ⟨h, hv, hres, hself, hwalk, rfl⟩

/-- Every reachable arena is a subgraph of the original: rounds only
delete edges. -/
theorem reachedS_le (h : ReachedS r G rounds A) : A ≤ G := by
  induction h with
  | nil => exact le_rfl
  | step _ _ _ _ _ ih => exact le_trans (nextArenaS_le ..) ih

/-- Every earlier stretch of a play is itself a play. -/
theorem reachedS_suffix (h : ReachedS r G rounds A) :
    ∀ t : List (RoundS n), t <:+ rounds → ∃ B, ReachedS r G t B := by
  induction h with
  | nil =>
    intro t ht
    rw [List.suffix_nil.mp ht]
    exact ⟨G, ReachedS.nil⟩
  | @step rounds A v X S hh hv hres hself hwalk ih =>
    intro t ht
    rcases List.suffix_cons_iff.mp ht with rfl | ht'
    · exact ⟨_, ReachedS.step hh hv hres hself hwalk⟩
    · exact ih t ht'

/-- Every recorded round meant to isolate its own connector. -/
theorem selfS (h : ReachedS r G rounds A) : ∀ e ∈ rounds, e.vtx ∈ e.gen := by
  induction h with
  | nil => intro e he; exact absurd he (by simp)
  | @step rounds A v X S hh hv hres hself hwalk ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hself
    · exact ih e he'

/-- Every recorded restriction set was a legal move: it lies inside the
ball of its round. This is where a play retrieves the legality clause of
`ReachedS.step`. -/
theorem resS_subset_ball (h : ReachedS r G rounds A) :
    ∀ e ∈ rounds, e.res ⊆ ball e.arena r e.vtx := by
  induction h with
  | nil => intro e he; exact absurd he (by simp)
  | @step rounds A v X S hh hv hres hself hwalk ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hres
    · exact ih e he'

/-- **Isolation is permanent.** Every vertex a played round meant to
isolate has no incident edge in any later arena: in the arena right after
the round it is either outside the set the round restricted to or inside
the isolated batch, and later arenas only lose further edges. -/
theorem isolatedS (h : ReachedS r G rounds A) :
    ∀ e ∈ rounds, ∀ z ∈ e.gen, ∀ u, ¬ A.Adj z u := by
  induction h with
  | nil => intro e he; exact absurd he (by simp)
  | @step rounds A v X S hh hv hres hself hwalk ih =>
    intro e he z hz u hadj
    rcases List.mem_cons.mp he with rfl | he'
    · exact not_mem_batchS_of_nextArenaS_adj hadj
        (mem_batchS hz (mem_res_of_nextArenaS_adj hadj))
    · exact ih e he' z hz u (nextArenaS_le _ hadj)

/-- A vertex that still carries an edge lies in the restriction set of
every earlier round: a round keeps only the edges inside that set, and
later rounds keep fewer. Through `resS_subset_ball` it then lies in the
ball of that round too. -/
theorem mem_res_of_roundS (h : ReachedS r G rounds A) :
    ∀ e ∈ rounds, ∀ z u, A.Adj z u → z ∈ e.res := by
  induction h with
  | nil => intro e he; exact absurd he (by simp)
  | @step rounds A v X S hh hv hres hself hwalk ih =>
    intro e he z u hadj
    rcases List.mem_cons.mp he with rfl | he'
    · exact mem_res_of_nextArenaS_adj hadj
    · exact ih e he' z u (nextArenaS_le _ hadj)

/-- Connector never repeats a vertex in a surviving play: an earlier
vertex is isolated from the round it was played on, while the current one
still carries an edge. -/
theorem picksS_nodup (h : ReachedS r G rounds A) : (rounds.map RoundS.vtx).Nodup := by
  induction h with
  | nil => simp
  | @step rounds A v X S hh hv hres hself hwalk ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih⟩
    obtain ⟨e, he, hev⟩ := List.mem_map.mp hmem
    obtain ⟨u, hu⟩ := hv
    refine isolatedS hh e he e.vtx (selfS hh e he) u ?_
    show A.Adj e.vtx u
    rw [show e.vtx = v from hev]
    exact hu

/-! ### Pairs of rounds -/

/-- The position at the round with index `b`, together with the incident
edge its vertex still had there and the clause its generating set was
recorded under. -/
theorem reachedS_entry (h : ReachedS r G rounds A) {b : ℕ} (hb : b < rounds.length) :
    ReachedS r G (rounds.drop (b + 1)) (rounds[b]).arena ∧
      (∃ u, (rounds[b]).arena.Adj (rounds[b]).vtx u) ∧
      (∀ e ∈ rounds.drop (b + 1), WithinDist e.arena r e.vtx (rounds[b]).vtx →
        ∃ p : e.arena.Walk e.vtx (rounds[b]).vtx, p.length ≤ r ∧
          {z | z ∈ p.support} ⊆ (rounds[b]).gen) := by
  obtain ⟨B, hB⟩ := reachedS_suffix h (rounds.drop b) (List.drop_suffix b rounds)
  rw [List.drop_eq_getElem_cons hb] at hB
  obtain ⟨h1, h2, -, -, h5, -⟩ := reachedS_cons (v := (rounds[b]).vtx)
    (A₀ := (rounds[b]).arena) (X := (rounds[b]).res) (S := (rounds[b]).gen) hB
  exact ⟨h1, h2, h5⟩

/-- The walk a pair of rounds recorded. The newer round's vertex still
had an edge, so it lies in the restriction set the older round recorded —
which the legality clause puts inside that round's ball, arming the guard
the newer round's clause is under — and the set the newer round recorded
therefore contains the support of a genuine walk of length at most `r` in
the older round's arena. Its endpoints are distinct: the older vertex is
already isolated when the newer round is played. -/
theorem pairS_walk (h : ReachedS r G rounds A) {b a : ℕ}
    (hb : b < rounds.length) (ha : a < rounds.length) (hba : b < a) :
    ∃ p : (rounds[a]).arena.Walk (rounds[a]).vtx (rounds[b]).vtx,
      p.length ≤ r ∧ {z | z ∈ p.support} ⊆ (rounds[b]).gen ∧
      (rounds[a]).vtx ≠ (rounds[b]).vtx := by
  obtain ⟨hRb, ⟨u, hu⟩, hwalkb⟩ := reachedS_entry h hb
  have hmem : rounds[a] ∈ rounds.drop (b + 1) := getElem_mem_drop (j := b + 1) ha hba
  have hres : (rounds[b]).vtx ∈ (rounds[a]).res :=
    mem_res_of_roundS hRb rounds[a] hmem _ u hu
  have hball : (rounds[b]).vtx ∈ ball (rounds[a]).arena r (rounds[a]).vtx :=
    resS_subset_ball hRb rounds[a] hmem hres
  obtain ⟨p, hplen, hpsub⟩ := hwalkb rounds[a] hmem (mem_ball.mp hball)
  refine ⟨p, hplen, hpsub, fun hEq => ?_⟩
  refine isolatedS hRb rounds[a] hmem (rounds[a]).vtx (selfS hRb rounds[a] hmem) u ?_
  rw [hEq]
  exact hu

/-- **Distinct pairs' walks are disjoint.** A vertex an older round meant
to isolate has no edge in any arena from then on; but a walk recorded by
a pair of rounds strictly newer than it lives in a later arena and has
positive length, so each of its vertices does carry an edge. -/
theorem pairS_disjoint (h : ReachedS r G rounds A) {bNew aNew bOld : ℕ}
    (hbNew : bNew < rounds.length) (haNew : aNew < rounds.length)
    (hbOld : bOld < rounds.length) (hcross : aNew < bOld) {z : Fin n}
    (hzOld : z ∈ (rounds[bOld]).gen)
    {pNew : (rounds[aNew]).arena.Walk (rounds[aNew]).vtx (rounds[bNew]).vtx}
    (hne : (rounds[aNew]).vtx ≠ (rounds[bNew]).vtx) (hzNew : z ∈ pNew.support) :
    False := by
  obtain ⟨hRa, -, -⟩ := reachedS_entry h haNew
  have hiso : ∀ u, ¬ (rounds[aNew]).arena.Adj z u :=
    isolatedS hRa rounds[bOld] (getElem_mem_drop (j := aNew + 1) hbOld hcross) z hzOld
  have hlen0 : pNew.length ≠ 0 := fun h0 => hne (SimpleGraph.Walk.eq_of_length_eq_zero h0)
  obtain ⟨w, hw⟩ := exists_adj_of_mem_support pNew hlen0 hzNew
  exact hiso w hw

/-! ### No play lasts `N (2s + 2)` rounds -/

/-- **The extraction.** A play of `N (2·s + 2)` recorded rounds cannot
exist. Connector's vertices are `N (2·s + 2)` distinct vertices, so
quasi-wideness returns a separator `S` of at most `s` vertices and a
distance-`r` independent set `B` of at least `2·s + 2` of them. Pairing
the selected rounds off chronologically gives `s + 1` pairs whose
recorded walks are pairwise disjoint, so one of them avoids `S`; that
walk has length at most `r`, runs between two distinct members of `B` and
survives the deletion of `S`, contradicting the independence.

Nothing here looks at how large a batch is or which set a round
restricted to, which is why `ReachedS` imposes no bound on either. -/
theorem no_full_survivalS {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedS r G rounds A) (hlen : rounds.length = N (2 * s + 2)) : False := by
  classical
  have hPcard : ({z | z ∈ rounds.map RoundS.vtx} : Set (Fin n)).ncard = rounds.length := by
    have hcoe : ({z | z ∈ rounds.map RoundS.vtx} : Set (Fin n))
        = ((rounds.map RoundS.vtx).toFinset : Set (Fin n)) := by ext z; simp
    rw [hcoe, Set.ncard_coe_finset, List.toFinset_card_of_nodup (picksS_nodup h),
      List.length_map]
  obtain ⟨S, B, hS, hBP, hBcard, hInd⟩ := hQ _ (by rw [hPcard, hlen])
  -- enumerate `2 * s + 2` selected rounds chronologically and pair them off
  obtain ⟨bi, ai, hbl, hal, hba, hcross, hbB, haB⟩ :
      ∃ bi ai : Fin (s + 1) → ℕ,
        ∃ hbl : ∀ t, bi t < rounds.length, ∃ hal : ∀ t, ai t < rounds.length,
          (∀ t, bi t < ai t) ∧ (∀ t t' : Fin (s + 1), t < t' → ai t < bi t') ∧
          (∀ t, (rounds[bi t]'(hbl t)).vtx ∈ B) ∧ (∀ t, (rounds[ai t]'(hal t)).vtx ∈ B) := by
    set I : Finset (Fin rounds.length) :=
      Finset.univ.filter (fun i => (rounds[(i : ℕ)]'i.isLt).vtx ∈ B) with hI
    have hsub : B ⊆ (fun i : Fin rounds.length => (rounds[(i : ℕ)]'i.isLt).vtx) ''
        (I : Set (Fin rounds.length)) := by
      intro z hz
      obtain ⟨e, he, hez⟩ := List.mem_map.mp (hBP hz).1
      obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
      have hzi : (rounds[i]'hi).vtx = z := by rw [hie]; exact hez
      refine ⟨⟨i, hi⟩, Finset.mem_coe.mpr ?_, hzi⟩
      rw [hI, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show (rounds[i]'hi).vtx ∈ B
      rw [hzi]
      exact hz
    have hIcard : 2 * s + 2 ≤ I.card := by
      have h1 : B.ncard ≤ ((I : Set (Fin rounds.length))).ncard :=
        le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (Set.ncard_image_le (Set.toFinite _))
      rw [Set.ncard_coe_finset] at h1
      omega
    obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq hIcard
    have hmemB : ∀ k : Fin (2 * s + 2),
        (rounds[((J.orderEmbOfFin hJcard k : Fin rounds.length) : ℕ)]'
          (J.orderEmbOfFin hJcard k).isLt).vtx ∈ B := by
      intro k
      have hk := hJI (J.orderEmbOfFin_mem hJcard k)
      rw [hI, Finset.mem_filter] at hk
      exact hk.2
    have hmono : ∀ k k' : Fin (2 * s + 2), k < k' →
        ((J.orderEmbOfFin hJcard k : Fin rounds.length) : ℕ) <
          ((J.orderEmbOfFin hJcard k' : Fin rounds.length) : ℕ) :=
      fun k k' hkk' => (J.orderEmbOfFin hJcard).strictMono hkk'
    refine ⟨fun t => ((J.orderEmbOfFin hJcard ⟨2 * (t : ℕ), by have := t.isLt; omega⟩ :
              Fin rounds.length) : ℕ),
            fun t => ((J.orderEmbOfFin hJcard ⟨2 * (t : ℕ) + 1, by have := t.isLt; omega⟩ :
              Fin rounds.length) : ℕ),
            fun t => Fin.isLt _, fun t => Fin.isLt _, fun t => ?_, fun t t' htt' => ?_,
            fun t => hmemB _, fun t => hmemB _⟩
    · exact hmono _ _ (by simp)
    · refine hmono _ _ ?_
      have : (t : ℕ) < (t' : ℕ) := htt'
      simp only [Fin.mk_lt_mk]
      omega
  -- name the walk each pair recorded
  choose p hplen hpsub hpne using fun t : Fin (s + 1) => pairS_walk h (hbl t) (hal t) (hba t)
  -- distinct pairs' walks are disjoint, so one of them avoids `S`
  have hdisj : ∀ t t' : Fin (s + 1), t ≠ t' → ∀ z,
      z ∈ {z | z ∈ (p t).support} → z ∈ {z | z ∈ (p t').support} → False := by
    intro t t' hne z hz hz'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact pairS_disjoint h (hbl t) (hal t) (hbl t') (hcross t t' hlt)
        (hpsub t' hz') (hpne t) hz
    · exact pairS_disjoint h (hbl t') (hal t') (hbl t) (hcross t' t hlt)
        (hpsub t hz) (hpne t') hz'
  obtain ⟨t₀, ht₀⟩ := exists_avoiding hS (fun t => {z | z ∈ (p t).support}) hdisj
  -- that pair's walk contradicts distance independence
  have hAle : (rounds[ai t₀]'(hal t₀)).arena ≤ G := reachedS_le (reachedS_entry h (hal t₀)).1
  have hsupp : ∀ z ∈ (p t₀).support, z ∉ S := fun z hz => ht₀ z hz
  obtain ⟨q, hq⟩ := exists_walk_deleteVerts_of_le hAle (p t₀) hsupp
  have hgt := distIndependent_iff.mp hInd (haB t₀) (hbB t₀) (hpne t₀) q
  have hlt := hplen t₀
  omega

/-! ### The main induction -/

/-- Splitter wins from every recorded position of the cluster-restricted
game, by downward induction on the remaining round budget. From a
reachable position with `b` rounds still to play and `N (2·s + 2) − b`
rounds recorded, Splitter wins within `b` rounds: at budget zero the play
would have `N (2·s + 2)` recorded rounds, which `no_full_survivalS`
excludes; with a round left, Splitter plays `SplitterWin`'s own chosen
batch, restricting to the full ball — which is a legal recorded
restriction set, by `subset_rfl` — and playing an isolated vertex ends
the play at once. The history his own round extends may mix cluster
rounds with ball rounds; the extraction never looks at which. -/
theorem splitterWins_of_reachedS {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B) :
    ∀ (b : ℕ) (rounds : List (RoundS n)) (A : SimpleGraph (Fin n)),
      ReachedS r G rounds A → rounds.length + b = N (2 * s + 2) →
      SplitterWins (N (2 * s + 2) * (r + 1)) r b A := by
  intro b
  induction b with
  | zero =>
    intro rounds A hR hlen
    exact (no_full_survivalS hQ hR (by omega)).elim
  | succ b ih =>
    intro rounds A hR hlen
    rw [splitterWins_succ_iff]
    refine Or.inr fun v => ?_
    by_cases hv : ∃ u, A.Adj v u
    · -- the chosen batch of `SplitterWin`, recorded at the full ball
      classical
      set l : List (Round n) := rounds.map (fun e => (e.vtx, e.arena)) with hl
      set S : Set (Fin n) := genSet r l v with hS
      have hwalk : ∀ e ∈ rounds, WithinDist e.arena r e.vtx v →
          ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧ {z | z ∈ p.support} ⊆ S := by
        intro e he hwd
        obtain ⟨p, hplen, hpset⟩ := pathSet_spec hwd
        refine ⟨p, hplen, ?_⟩
        rw [← hpset]
        exact pathSet_subset_genSet (e := (e.vtx, e.arena))
          (List.mem_map_of_mem (f := fun e : RoundS n => (e.vtx, e.arena)) he) v
      have hcard : (batchS ⟨v, A, ball A r v, S⟩).ncard ≤ N (2 * s + 2) * (r + 1) := by
        have h1 : (batchS ⟨v, A, ball A r v, S⟩).ncard ≤ (genSet r l v).ncard :=
          Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
        have h2 := genSet_ncard_le r l v
        have h3 : l.length = rounds.length := by rw [hl, List.length_map]
        have h4 : (rounds.length + 1) * (r + 1) ≤ N (2 * s + 2) * (r + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h5 : (rounds.length + 1) * (r + 1) = rounds.length * (r + 1) + (r + 1) :=
          Nat.succ_mul _ _
        rw [h3] at h2
        omega
      exact ⟨batchS ⟨v, A, ball A r v, S⟩, Set.inter_subset_right, hcard,
        ih (⟨v, A, ball A r v, S⟩ :: rounds) (nextArenaS ⟨v, A, ball A r v, S⟩)
          (ReachedS.step hR hv subset_rfl (self_mem_genSet r l v) hwalk)
          (by simp only [List.length_cons]; omega)⟩
    · exact ⟨∅, Set.empty_subset _, by simp,
        splitterWins_of_eq_bot (eq_bot_of_isolated (fun z hz => hv ⟨z, hz⟩) ∅)⟩

/-! ### The driver-facing form -/

/-- **The descent step.** At a position reached with an edge still at the
connector `v`, a cluster `X` inside the ball of the round and a marked
set `W` inside `X` which contains `v` and, for every earlier round the
arena connects to `v`, the part of some short walk's support that stays
inside `X`, is the batch of a recorded round: the round records `W`
together with the parts of those supports that ran out of `X`, and
isolates **exactly** `W` — the after-arena is
`deleteVerts (deleteVerts A Xᶜ) W` on the nose.

This is the whole interface of the cluster-restricted game to the
program. The program owes no equation between the walk it found and any
other walk — only that the support of the one it found is inside `W`
where the cluster keeps it. -/
theorem reachedS_descend {v : Fin n} {X W : Set (Fin n)} (h : ReachedS r G rounds A)
    (hv : ∃ u, A.Adj v u) (hXball : X ⊆ ball A r v) (hWX : W ⊆ X) (hself : v ∈ W)
    (hwalk : ∀ e ∈ rounds, WithinDist e.arena r e.vtx v →
      ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧
        {z | z ∈ p.support} ∩ X ⊆ W) :
    ∃ S : Set (Fin n),
      ReachedS r G (⟨v, A, X, S⟩ :: rounds) (deleteVerts (deleteVerts A Xᶜ) W) := by
  classical
  set S : Set (Fin n) := W ∪ {z | ∃ e ∈ rounds, ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧
      ({w | w ∈ p.support} ∩ X ⊆ W) ∧ z ∈ p.support} with hS
  have hbatch : batchS ⟨v, A, X, S⟩ = W := by
    refine Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => ⟨Or.inl hz, hWX hz⟩)
    obtain ⟨hzg, hzr⟩ := hz
    rcases hzg with hzW | ⟨e, -, p, -, hpsub, hzp⟩
    · exact hzW
    · exact hpsub ⟨hzp, hzr⟩
  have hstep : ReachedS r G (⟨v, A, X, S⟩ :: rounds) (nextArenaS ⟨v, A, X, S⟩) :=
    ReachedS.step h hv hXball (Or.inl hself)
      (fun e he hwd => by
        obtain ⟨p, hplen, hpsub⟩ := hwalk e he hwd
        exact ⟨p, hplen, fun z hz => Or.inr ⟨e, he, p, hplen, hpsub, hz⟩⟩)
  refine ⟨S, ?_⟩
  rwa [nextArenaS, hbatch] at hstep

/-- **No play survives the round bound.** A history of `N (2·s + 2)`
recorded rounds or more cannot be reached: its last `N (2·s + 2)` rounds
would be a full-length play, which `no_full_survivalS` excludes. -/
theorem reachedS_no_survival {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedS r G rounds A) (hlen : N (2 * s + 2) ≤ rounds.length) : False := by
  obtain ⟨B, hB⟩ := reachedS_suffix h (rounds.drop (rounds.length - N (2 * s + 2)))
    (List.drop_suffix _ _)
  exact no_full_survivalS hQ hB (by rw [List.length_drop]; omega)

/-- The termination measure of a driver maintaining `ReachedS`: the
history is always shorter than the round bound. -/
theorem reachedS_length_lt {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedS r G rounds A) : rounds.length < N (2 * s + 2) := by
  by_contra hcon
  exact reachedS_no_survival hQ h (by omega)

/-! ### `ReachedR` is the special case `res = ball` -/

/-- A round of the recorded ball game, as a round of the
cluster-restricted game whose restriction set is the full ball. On such a
round `batchS` and `nextArenaS` are `batchR` and `nextArenaR`
definitionally. -/
def toRoundS (r : ℕ) (e : RoundR n) : RoundS n :=
  ⟨e.vtx, e.arena, ball e.arena r e.vtx, e.gen⟩

/-- Every play of the ball game is a play of the cluster-restricted game,
round by round: the full ball is a legal restriction set by
`subset_rfl`, and the arenas agree definitionally. -/
theorem reachedS_of_reachedR {rounds : List (RoundR n)}
    (h : ReachedR r G rounds A) :
    ReachedS r G (rounds.map (toRoundS r)) A := by
  induction h with
  | nil => exact .nil
  | @step rounds A v S hh hv hself hwalk ih =>
    rw [List.map_cons]
    exact ReachedS.step ih hv subset_rfl hself
      (fun e he hwd => by
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact hwalk e' he' hwd)

/-- A round of the cluster-restricted game, forgetting its restriction
set. -/
def toRoundR (e : RoundS n) : RoundR n :=
  ⟨e.vtx, e.arena, e.gen⟩

/-- The converse bridge: a play of the cluster-restricted game all of
whose rounds recorded the full ball is a play of the ball game. Together
with `reachedS_of_reachedR` this makes the two records visibly the same
game at `res = ball`. -/
theorem reachedR_of_reachedS (h : ReachedS r G rounds A) :
    (∀ e ∈ rounds, e.res = ball e.arena r e.vtx) →
    ReachedR r G (rounds.map toRoundR) A := by
  induction h with
  | nil => exact fun _ => .nil
  | @step rounds A v X S hh hv hres hself hwalk ih =>
    intro hball
    have hX : X = ball A r v := hball ⟨v, A, X, S⟩ (List.mem_cons_self ..)
    subst hX
    rw [List.map_cons]
    exact ReachedR.step (ih fun e he => hball e (List.mem_cons_of_mem _ he)) hv hself
      (fun e he hwd => by
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact hwalk e' he' hwd)

/-- The worked play of `SplitterWinRec.Demo`, transported: the clauses of
`ReachedS` can all be met at once, so the game is not vacuous. -/
example : ReachedS 2 (⊤ : SimpleGraph (Fin 3))
    ([Demo.rd2, Demo.rd1].map (toRoundS 2)) (nextArenaR 2 Demo.rd2) :=
  reachedS_of_reachedR Demo.reached2

end Play

end Lax3Proofs.ReachedS
