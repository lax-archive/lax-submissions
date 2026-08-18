import Lax3Proofs.CoverSpec

/-!
# A concrete ordering routine, and its `data` field discharged (F1)

`CoverSpec.IsCoverOrdering` has two fields.  This file discharges the first —
`data`, the six-clause `AugChainData` postcondition — by *building* the
routine the field is about: for every carrier and every graph, an `R`-round
greedy augmentation chain whose two eliminations are **minimal** in the
`ElimPost` sense.  The `time` field is not touched here; see the `steps`
placeholder below.

## The assembly

`AugChainData G D π R d₀ k` (`CoverDegree.lean:642-649`) asks for six things,
and they are produced in three places:

* **The chain** (clauses 1–2).  `greedyChain G` starts from `baseOr G π₀`,
  the orientation of `G` along its own greedy elimination ordering, and each
  round is `greedyStep σᵢ`, where `σᵢ` is a greedy elimination ordering of the
  current fraternity graph — an ordering whose back-degrees meet the *least*
  low-degree bound of `fratGraph (D i)`.  A `greedyStep` keeps the old arcs
  and orients every newly demanded pair along `σᵢ` whenever tightness permits,
  falling back to the forced transitive direction when it does not; that makes
  it simultaneously an `AugStep` (clause 1, via `IsAugChain`) and a
  `GreedyFratRound` (clause 2).  The landed `tightStep` cannot play this role:
  it orients along the ordering unconditionally, which is an `AugStep` only
  for `π`-increasing orientations, and a per-round elimination ordering has no
  reason to increase along the previous rounds' arcs.

* **The first elimination** (clauses 3–4).  `d₀ := elimBound G` is
  `sInf {k | LowDegreeVertices G k}`: clause 4 (leastness) is `Nat.sInf_le`,
  and membership — `LowDegreeVertices G d₀`, hence via
  `degeneracyLE_of_lowDegreeVertices` an ordering with back-degrees `≤ d₀`,
  hence `(D 0).InDegLE d₀` for the `baseOr` along it — is `Nat.sInf_mem`
  (the set is nonempty: every graph on `Fin m` satisfies the bound at `m`).

* **The last elimination** (clauses 5–6).  The same two-step at the
  symmetrized augmented graph `(D R).toGraph`: `k := elimBound (D R).toGraph`,
  `π :=` the permutation sorting its greedy elimination ranking.  `rankPerm`
  turns the injective ranking `Fin m → ℕ` into an `Equiv.Perm (Fin m)`
  inducing the same order, so `BackDegLE` transports across.

**No class hypothesis appears anywhere**: the routine is total
(`Classical.choice` picks the eliminations), and `greedyOrderingRoutine_data`
holds for *every* graph on every carrier.  The class enters only when
*bounding* `d₀` and `k` — the business of `CoverDegree.exists_cover_degree`,
not of this file.  This confirms E0's assessment that `data` needed only
assembly.

## What this file does *not* claim

`steps := 0` is a placeholder.  This file makes **no time claim**: `F5` owes
the `time` field of `IsCoverOrdering`, and `isCoverOrdering_greedyOrderingRoutine`
below takes it as a hypothesis so that `F5` only ever owes `time`.
-/

namespace Lax3Proofs.CoverRoutine

open scoped SimpleGraph
open Lax12.GraphClasses
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverDegree

variable {n : ℕ}

/-! ### The minimal low-degree bound

`ElimPost`-minimality made concrete: the least `k` such that every nonempty
vertex set carries a vertex of inside-degree at most `k`.  Membership is
`Nat.sInf_mem`, leastness is `Nat.sInf_le`; both clauses 4 and 6 of
`AugChainData` are read off these two lemmas. -/

/-- Every graph on `Fin n` satisfies the low-degree property at `n`: the
inside-neighbourhood is a subset of the set itself. -/
theorem lowDegreeVertices_card (F : SimpleGraph (Fin n)) : LowDegreeVertices F n := by
  intro S hS
  obtain ⟨v, hv⟩ := hS
  refine ⟨v, hv, ?_⟩
  calc (nbrsIn F S v).card ≤ S.card :=
        Finset.card_le_card fun u hu => (mem_nbrsIn.1 hu).1
    _ ≤ n := le_trans (Finset.card_le_univ S) (by simp)

/-- **The minimal elimination bound** of a graph: the least `k` for which
every nonempty vertex set has a vertex with at most `k` neighbours inside
it.  This is the `d₀` of the first elimination and the `k` of the last. -/
noncomputable def elimBound (F : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | LowDegreeVertices F k}

/-- The minimal bound is itself a valid low-degree bound (membership half of
minimality). -/
theorem lowDegreeVertices_elimBound (F : SimpleGraph (Fin n)) :
    LowDegreeVertices F (elimBound F) :=
  Nat.sInf_mem (s := {k | LowDegreeVertices F k}) ⟨n, lowDegreeVertices_card F⟩

/-- The minimal bound is least among the valid low-degree bounds (leastness
half of minimality; clauses 4 and 6 of `AugChainData` verbatim). -/
theorem elimBound_le {F : SimpleGraph (Fin n)} {k : ℕ}
    (h : LowDegreeVertices F k) : elimBound F ≤ k :=
  Nat.sInf_le h

/-! ### The greedy elimination ordering realizing it -/

/-- **The greedy elimination ranking** of a graph: an injective ranking whose
back-degrees meet the minimal elimination bound, obtained by peeling minimal-
degree vertices (`degeneracyLE_of_lowDegreeVertices`) at `elimBound`. -/
noncomputable def elimRank (F : SimpleGraph (Fin n)) : Fin n → ℕ :=
  Exists.choose (degeneracyLE_of_lowDegreeVertices (lowDegreeVertices_elimBound F))

theorem elimRank_injective (F : SimpleGraph (Fin n)) :
    Function.Injective (elimRank F) :=
  (Exists.choose_spec
    (degeneracyLE_of_lowDegreeVertices (lowDegreeVertices_elimBound F))).1

theorem elimRank_backDegLE (F : SimpleGraph (Fin n)) :
    BackDegLE F (elimRank F) (elimBound F) :=
  (Exists.choose_spec
    (degeneracyLE_of_lowDegreeVertices (lowDegreeVertices_elimBound F))).2

/-- Back-degree bounds are monotone in the bound. -/
theorem backDegLE_mono {F : SimpleGraph (Fin n)} {σ : Fin n → ℕ} {k k' : ℕ}
    (h : BackDegLE F σ k) (hk : k ≤ k') : BackDegLE F σ k' :=
  fun v => (h v).trans hk

/-! ### From an injective ranking to a permutation

`AugChainData`'s clause 5 speaks about a permutation, while greedy elimination
produces an injective ranking `Fin n → ℕ`.  `rankPerm` sorts the ranking's
image: it is the unique permutation inducing the same strict order, so every
order-determined property (`BackDegLE` in particular) transports across. -/

private theorem card_image_rank (σ : Fin n → ℕ) (hσ : Function.Injective σ) :
    (Finset.univ.image σ).card = n := by
  rw [Finset.card_image_of_injective _ hσ, Finset.card_univ, Fintype.card_fin]

/-- The permutation of `Fin n` induced by an injective ranking `σ : Fin n → ℕ`:
`v` goes to the rank of `σ v` in the sorted image of `σ`. -/
noncomputable def rankPerm (σ : Fin n → ℕ) (hσ : Function.Injective σ) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective
    (fun v => ((Finset.univ.image σ).orderIsoOfFin (card_image_rank σ hσ)).symm
      ⟨σ v, Finset.mem_image_of_mem σ (Finset.mem_univ v)⟩)
    (Finite.injective_iff_bijective.mp fun _u _v h =>
      hσ (congrArg Subtype.val
        (((Finset.univ.image σ).orderIsoOfFin (card_image_rank σ hσ)).symm.injective h)))

/-- `rankPerm` induces exactly the order of the ranking it sorts. -/
theorem rankPerm_lt_iff {σ : Fin n → ℕ} (hσ : Function.Injective σ) {u v : Fin n} :
    rankPerm σ hσ u < rankPerm σ hσ v ↔ σ u < σ v := by
  show ((Finset.univ.image σ).orderIsoOfFin (card_image_rank σ hσ)).symm _ <
      ((Finset.univ.image σ).orderIsoOfFin (card_image_rank σ hσ)).symm _ ↔ _
  rw [OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

/-- The order agreement, read on the underlying `ℕ`-values — the shape
`AugChainData`'s clause 5 uses. -/
theorem rankPerm_val_lt_iff {σ : Fin n → ℕ} (hσ : Function.Injective σ) {u v : Fin n} :
    ((rankPerm σ hσ u : Fin n) : ℕ) < ((rankPerm σ hσ v : Fin n) : ℕ) ↔ σ u < σ v := by
  rw [← Fin.lt_def]
  exact rankPerm_lt_iff hσ

/-- `BackDegLE` transports from a ranking to the permutation sorting it. -/
theorem backDegLE_rankPerm {F : SimpleGraph (Fin n)} {σ : Fin n → ℕ}
    (hσ : Function.Injective σ) {k : ℕ} (h : BackDegLE F σ k) :
    BackDegLE F (fun v => ((rankPerm σ hσ v : Fin n) : ℕ)) k := by
  intro v
  refine le_trans (le_of_eq ?_) (h v)
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, rankPerm_val_lt_iff hσ]

/-! ### The two eliminations, packaged -/

/-- **The greedy elimination permutation** of a graph: `elimRank`, sorted. -/
noncomputable def elimPerm (F : SimpleGraph (Fin n)) : Equiv.Perm (Fin n) :=
  rankPerm (elimRank F) (elimRank_injective F)

/-- The greedy elimination permutation has back-degrees at most the minimal
elimination bound — clause 5 of `AugChainData` at `F = (D R).toGraph`. -/
theorem elimPerm_backDegLE (F : SimpleGraph (Fin n)) :
    BackDegLE F (fun v => ((elimPerm F v : Fin n) : ℕ)) (elimBound F) :=
  backDegLE_rankPerm (elimRank_injective F) (elimRank_backDegLE F)

/-- The base orientation along the greedy elimination permutation has
in-degrees at most the minimal elimination bound — clause 3 of
`AugChainData`, with the `d₀` of clause 4. -/
theorem inDegLE_baseOr_elimPerm (G : SimpleGraph (Fin n)) :
    (baseOr G (elimPerm G)).InDegLE (elimBound G) := by
  intro v
  refine le_trans (le_of_eq ?_) (elimPerm_backDegLE G v)
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Finset.mem_coe, mem_baseOr, Set.mem_setOf_eq, Fin.lt_def]

/-! ### One greedy round

`tightStep π` is an `AugStep` only for `π`-increasing orientations
(`augStep_tightStep`): it refuses the arc `u → v` when `π v < π u`, and for a
transitive link that direction can be the only tight one.  A greedy round
orients along the *current* fraternity graph's elimination ordering, which the
accumulated arcs have no reason to respect — so the step here orients a newly
demanded pair along `σ` whenever the `σ`-direction is tight-permissible, and
in the forced transitive direction otherwise.  Tightness then holds by
construction, and the fraternal-only arcs (the ones `GreedyFratRound` asks
about) always go along `σ`, because a fraternal link is tight-permissible in
both directions. -/

/-- One greedy round on `D` along a ranking `σ`: keep the old arcs; orient
every newly demanded pair along `σ` when the `σ`-smaller-to-larger direction
is tight-permissible, and in the forced (transitive) direction otherwise. -/
noncomputable def greedyStep (σ : Fin n → ℕ) (D : Orientation n) :
    Orientation n where
  inN v := D.inN v ∪
    pick (fun u => ¬ D.Adjacent u v ∧ (TransLink D u v ∨ FratLink D u v) ∧
      (σ u < σ v ∨ ¬ (TransLink D v u ∨ FratLink D v u)))
  not_mem_self v h := by
    rcases Finset.mem_union.1 h with h | h
    · exact D.not_mem_self v h
    · obtain ⟨-, hlink, hcase⟩ := mem_pick.1 h
      rcases hcase with hlt | hno
      · exact absurd hlt (lt_irrefl _)
      · exact hno hlink
  asymm u v h h' := by
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h' with h' | h'
      · exact D.asymm u v h h'
      · exact (mem_pick.1 h').1 (Or.inr h)
    · rcases Finset.mem_union.1 h' with h' | h'
      · exact (mem_pick.1 h).1 (Or.inr h')
      · obtain ⟨-, hluv, hcu⟩ := mem_pick.1 h
        obtain ⟨-, hlvu, hcv⟩ := mem_pick.1 h'
        rcases hcu with hlt | hno
        · rcases hcv with hlt' | hno'
          · exact absurd (hlt.trans hlt') (lt_irrefl _)
          · exact hno' hluv
        · exact hno hlvu

theorem mem_greedyStep {σ : Fin n → ℕ} {D : Orientation n} {u v : Fin n} :
    u ∈ (greedyStep σ D).inN v ↔
      u ∈ D.inN v ∨
        (¬ D.Adjacent u v ∧ (TransLink D u v ∨ FratLink D u v) ∧
          (σ u < σ v ∨ ¬ (TransLink D v u ∨ FratLink D v u))) := by
  rw [show (greedyStep σ D).inN v = D.inN v ∪
      pick (fun u => ¬ D.Adjacent u v ∧ (TransLink D u v ∨ FratLink D u v) ∧
        (σ u < σ v ∨ ¬ (TransLink D v u ∨ FratLink D v u))) from rfl,
    Finset.mem_union]
  exact or_congr Iff.rfl mem_pick

/-- A greedy round is an augmentation step, for **every** orientation — no
`π`-increasing hypothesis.  Where the `σ`-direction of a demanded pair is not
tight-permissible, the opposite direction is, because the demand itself came
from a transitive link that way or a (symmetric) fraternal link. -/
theorem augStep_greedyStep {σ : Fin n → ℕ} (hσ : Function.Injective σ)
    {D : Orientation n} : AugStep D (greedyStep σ D) where
  mono _ _ hu := mem_greedyStep.2 (Or.inl hu)
  trans_cov u v hne hlink := by
    by_cases hadj : D.Adjacent u v
    · rcases hadj with hadj | hadj
      · exact Or.inl (mem_greedyStep.2 (Or.inl hadj))
      · exact Or.inr (mem_greedyStep.2 (Or.inl hadj))
    · by_cases hc : σ u < σ v ∨ ¬ (TransLink D v u ∨ FratLink D v u)
      · exact Or.inl (mem_greedyStep.2 (Or.inr ⟨hadj, Or.inl hlink, hc⟩))
      · obtain ⟨hnlt, hnn⟩ := not_or.1 hc
        refine Or.inr (mem_greedyStep.2 (Or.inr
          ⟨fun h => hadj (adjacent_comm h), not_not.1 hnn, Or.inl ?_⟩))
        exact lt_of_le_of_ne (not_lt.1 hnlt) fun h => hne (hσ h.symm)
  frat_cov u v hne hlink := by
    by_cases hadj : D.Adjacent u v
    · rcases hadj with hadj | hadj
      · exact Or.inl (mem_greedyStep.2 (Or.inl hadj))
      · exact Or.inr (mem_greedyStep.2 (Or.inl hadj))
    · rcases lt_or_gt_of_ne (fun hc : σ u = σ v => hne (hσ hc)) with hlt | hlt
      · exact Or.inl (mem_greedyStep.2 (Or.inr ⟨hadj, Or.inr hlink, Or.inl hlt⟩))
      · exact Or.inr (mem_greedyStep.2 (Or.inr
          ⟨fun h => hadj (adjacent_comm h), Or.inr hlink.symm, Or.inl hlt⟩))
  tight u v hu := by
    rcases mem_greedyStep.1 hu with hu | ⟨-, hu, -⟩
    · exact Or.inl hu
    · exact Or.inr hu

/-- A greedy round along the fraternity graph's own elimination ordering is a
`GreedyFratRound`: for every valid low-degree bound `k` the witness is the
elimination ordering itself — its back-degrees meet the *minimal* bound, hence
`k`; and every fraternal-only new arc goes along it, because a fraternal link
is tight-permissible in both directions, so the fallback never fires on one. -/
theorem greedyFratRound_greedyStep {D : Orientation n} :
    GreedyFratRound D (greedyStep (elimRank (fratGraph D)) D) := by
  intro k hk
  refine ⟨elimRank (fratGraph D),
    backDegLE_mono (elimRank_backDegLE (fratGraph D)) (elimBound_le hk), ?_⟩
  intro u v hu hold _htr hadj
  rcases mem_greedyStep.1 hu with h | ⟨-, -, hc⟩
  · exact absurd h hold
  · rcases hc with hlt | hno
    · exact hlt
    · exact absurd (Or.inr (fratGraph_adj.1 hadj).2.symm) hno

/-! ### The greedy chain -/

/-- **The greedy chain** of a graph: orient `G` along its own greedy
elimination ordering, then run greedy rounds, each along the elimination
ordering of the current fraternity graph.  Defined for all `i`; an `R`-round
phase reads rounds `0..R`. -/
noncomputable def greedyChain (G : SimpleGraph (Fin n)) : ℕ → Orientation n
  | 0 => baseOr G (elimPerm G)
  | i + 1 => greedyStep (elimRank (fratGraph (greedyChain G i))) (greedyChain G i)

theorem isAugChain_greedyChain (G : SimpleGraph (Fin n)) (R : ℕ) :
    IsAugChain G (greedyChain G) R :=
  ⟨baseOr_orients G (elimPerm G), fun i _ =>
    augStep_greedyStep (elimRank_injective (fratGraph (greedyChain G i)))⟩

theorem greedyFratRound_greedyChain (G : SimpleGraph (Fin n)) (i : ℕ) :
    GreedyFratRound (greedyChain G i) (greedyChain G (i + 1)) :=
  greedyFratRound_greedyStep

/-! ### The routine -/

/-- **The greedy ordering routine**: for every carrier and every graph, the
`R`-round greedy chain, the elimination permutation of its final symmetrized
augmented graph, and the two minimal elimination bounds.

`steps := 0` is a **placeholder that F5 replaces — this file makes no time
claim**.  The routine here is the mathematical assembly whose output satisfies
`AugChainData`; pricing it is the separate `time` half of `IsCoverOrdering`,
which `isCoverOrdering_greedyOrderingRoutine` below takes as a hypothesis. -/
noncomputable def greedyOrderingRoutine (R : ℕ) : CoverSpec.OrderingRoutine :=
  fun _m G =>
    { chain := greedyChain G
      order := elimPerm (greedyChain G R).toGraph
      inDeg := elimBound G
      backDeg := elimBound (greedyChain G R).toGraph
      steps := 0 }

/-- **The discharge of `data`, with no hypothesis at all**: for every round
count, every carrier and every graph — no graph class in sight — the greedy
ordering routine's output satisfies the six-clause `AugChainData`
postcondition, its two elimination bounds minimal in the `ElimPost` sense.
The class enters only when *bounding* the minimal `d₀` and `k`, which is
`CoverDegree.exists_cover_degree`'s business, not this file's. -/
theorem greedyOrderingRoutine_data (R : ℕ) :
    ∀ (m : ℕ) (G : SimpleGraph (Fin m)),
      AugChainData G ((greedyOrderingRoutine R) m G).chain
        ((greedyOrderingRoutine R) m G).order R
        ((greedyOrderingRoutine R) m G).inDeg
        ((greedyOrderingRoutine R) m G).backDeg :=
  fun _m G =>
    ⟨isAugChain_greedyChain G R,
     fun i _ => greedyFratRound_greedyChain G i,
     inDegLE_baseOr_elimPerm G,
     fun _k' hk' => elimBound_le hk',
     elimPerm_backDegLE (greedyChain G R).toGraph,
     fun _k' hk' => elimBound_le hk'⟩

/-- **The interface corollary**: for any class, the greedy ordering routine's
`data` field of `CoverSpec.IsCoverOrdering` is discharged outright; only the
`time` field is taken as a hypothesis.  F5 owes exactly `htime` and nothing
else. -/
theorem isCoverOrdering_greedyOrderingRoutine (C : GraphClass) (R : ℕ) (δ f : ℝ)
    (htime : ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ((greedyOrderingRoutine R) m G).steps ≤ f * (m : ℝ) ^ (1 + 2 * δ)) :
    CoverSpec.IsCoverOrdering C R δ f (greedyOrderingRoutine R) :=
  ⟨fun _n _Gn _hGn m G _hsub => greedyOrderingRoutine_data R m G, htime⟩

end Lax3Proofs.CoverRoutine
