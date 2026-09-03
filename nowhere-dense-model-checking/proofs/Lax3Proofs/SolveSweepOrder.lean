import Lax3Proofs.SolveSweepStep
import Lax3Proofs.CoverRoutine

/-!
# F6c11b (part 3) — the machine ordering routine, and `CovOrderIn` at it

`SolveCovStep`'s Finding 2: `timedGreedyRoutine`'s order is built from
`elimRank := Exists.choose …` — a choice-picked ranking no concrete
program can be *proved* to output — so `CovOrderIn` needs a
**machine-defined** ordering routine for F7 to instantiate the
headline's `∃ ord` with. This file builds it and proves its validity;
the machine pass itself is split at its seam into two named residuals,
with the verbatim-concluding glue (`covOrderIn_of_aug_mdPeel`).

## Finding 4 — min-degree peel of the arena graph alone cannot serve

`AugChainData`'s clauses 5–6 (`CoverDegree.lean:642-649`) constrain the
ordering at the **symmetrized augmented graph** `(D R).toGraph`, not at
`G`: clause 5 asks `BackDegLE (D R).toGraph π k` and clause 6 forces
`k ≤ elimBound (D R).toGraph` — jointly, `π` must be an *optimal*
elimination order of the augmented graph. An order computed from `G`
alone (min-degree peel of `G`) has no bound on its back-degrees in
`(D R).toGraph ⊇ G` and cannot meet the pair in general. So the
machine routine must peel the augmented graph — which in turn forces
the **chain itself** to be deterministic: `greedyChain`'s rounds order
along `elimRank (fratGraph …)`, choice-picked at every round, so its
augmented graph is not a machine target either.

## The deterministic replacement: `mdRank`

`mdRank F` is the greedy elimination ranking with every choice pinned:
repeatedly take the *minimum-degree vertex of the current peeled
graph, smallest index tie-break* (`minDegVert`), rank it last, recurse
(`mdRankAux`). It is injective with values `< n` (`mdRank_lt`), and —
the landed `degeneracyLE_of_lowDegreeVertices` argument rerun at the
pinned choice — its back-degrees meet **every** valid low-degree bound
(`mdRank_backDegLE`), in particular the minimal one `elimBound`: the
sInf-minimality clauses are attained, exactly as the E12 route
anticipated. Because its values are already `< n`, the permutation
`mdPerm` is direct (`Equiv.ofBijective`), with `(mdPerm F v : ℕ) =
mdRank F v` *definitional* — no `rankPerm` sorting layer between the
machine's rank array and the abstract order.

`mdChain` is `greedyChain` with `elimRank` replaced by `mdRank` at the
base and in every round; `greedyStep` itself is choice-free (its `pick`
is a `Classical.decPred` filter — extensionally determined, the
`if_congr`-class decidability that a machine CAN be proved against,
unlike `Exists.choose`). `mdOrderingRoutine R` packages the chain, the
peel of its augmented graph, and the two minimal elimination bounds;
`mdOrderingRoutine_data` discharges the full six-clause `AugChainData`
for it, on every carrier and every graph, no class hypothesis — the
mirror of `greedyOrderingRoutine_data`, now at a machine-matchable
routine. `isCoverOrdering_mdOrderingRoutine` leaves F5/E12 owing
exactly the `time` field, as before.

## The machine pass, split at its seam (§3)

`CovOrderIn` at `mdOrderingRoutine R` owes two passes:

* **`CovAugAdjIn` — the augmentation pass**: compute the `R` rounds of
  the deterministic tight transitive–fraternal augmentation and leave
  the *augmented* graph `(mdChain A.G R).toGraph` as a deletable
  adjacency region (`DelAdjSt`, `SolveSweepAdj`). This is the real
  GKS ordering algorithm (`thm:computingorientation`, resolving onto
  NOdM05); its machine construction and its `f·m^{1+2δ}` price are the
  chain `CoverSpec.lean`'s module docstring opened link by link —
  E12's priced obligation, not this leaf's.

* **`CovMdPeelIn` — the peel pass**: min-degree peel *over the
  deletable structure* (repeatedly pick the minimum-degree live
  vertex, smallest index tie-break — `dg` is maintained by
  `AdjDeleteIn`, a bucket-queue over degrees keeps the minimum at
  amortized `O(1)`), writing rank `N-1` downward, leaving
  `RankArr (ra j) (mdPerm (mdChain A.G R).toGraph)` — which *is*
  `RankArr` at the routine's order, definitionally.

`covOrderIn_of_aug_mdPeel` composes them into the verbatim
`CovOrderIn … (mdOrderingRoutine R) …` — the shape-(a) discharge:
parametric-conditional at the F7-chosen `ord`, concluded at the
concrete machine routine.
-/

namespace Lax3Proofs.CoverRoutine

open scoped SimpleGraph
open Lax12.GraphClasses
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverDegree

variable {n : ℕ}

/-! ## §1 The pinned greedy elimination -/

open Classical in
/-- **The pinned choice**: the minimum-degree vertex of `S` (degree
inside `S`), smallest index tie-break. Every ingredient is a `Finset`
minimum — extensionally determined, a machine target. -/
noncomputable def minDegVert (F : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : S.Nonempty) : Fin n :=
  (S.filter fun v => (nbrsIn F S v).card =
      S.inf' hS fun v => (nbrsIn F S v).card).min'
    (by
      obtain ⟨v, hv, hveq⟩ :=
        Finset.exists_mem_eq_inf' hS fun v => (nbrsIn F S v).card
      exact ⟨v, Finset.mem_filter.mpr ⟨hv, hveq.symm⟩⟩)

open Classical in
/-- The defining membership of the pinned choice: it lies in the
minimum-degree filter. -/
theorem minDegVert_spec (F : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : S.Nonempty) :
    minDegVert F S hS ∈ S.filter fun v => (nbrsIn F S v).card =
      S.inf' hS fun v => (nbrsIn F S v).card :=
  Finset.min'_mem _ _

theorem minDegVert_mem (F : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : S.Nonempty) : minDegVert F S hS ∈ S := by
  classical
  exact (Finset.mem_filter.mp (minDegVert_spec F S hS)).1

/-- The pinned choice attains the minimum inside degree. -/
theorem card_nbrsIn_minDegVert (F : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : S.Nonempty) :
    (nbrsIn F S (minDegVert F S hS)).card =
      S.inf' hS fun v => (nbrsIn F S v).card := by
  classical
  exact (Finset.mem_filter.mp (minDegVert_spec F S hS)).2

/-- The pinned choice has at most `k` neighbours inside `S`, for every
valid low-degree bound `k`: the low-degree witness only beats it up. -/
theorem card_nbrsIn_minDegVert_le {F : SimpleGraph (Fin n)} {k : ℕ}
    (hk : LowDegreeVertices F k) (S : Finset (Fin n)) (hS : S.Nonempty) :
    (nbrsIn F S (minDegVert F S hS)).card ≤ k := by
  classical
  obtain ⟨u, huS, hu⟩ := hk S hS
  calc (nbrsIn F S (minDegVert F S hS)).card
      = S.inf' hS (fun v => (nbrsIn F S v).card) :=
        card_nbrsIn_minDegVert F S hS
    _ ≤ (nbrsIn F S u).card := Finset.inf'_le _ huS
    _ ≤ k := hu

/-- **The pinned greedy elimination ranking on `S`**: peel the pinned
minimum-degree vertex, rank it last, recurse. Vertices outside `S` get
`0` (never read). -/
noncomputable def mdRankAux (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Fin n → ℕ :=
  if hS : S.Nonempty then
    fun x =>
      if x = minDegVert F S hS then S.card - 1
      else mdRankAux F (S.erase (minDegVert F S hS)) x
  else fun _ => 0
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem (minDegVert_mem F S hS)

theorem mdRankAux_of_nonempty (F : SimpleGraph (Fin n)) {S : Finset (Fin n)}
    (hS : S.Nonempty) (x : Fin n) :
    mdRankAux F S x =
      if x = minDegVert F S hS then S.card - 1
      else mdRankAux F (S.erase (minDegVert F S hS)) x := by
  rw [mdRankAux, dif_pos hS]

/-- The three peel invariants at once — `degeneracyLE_of_lowDegreeVertices`'s
induction (`Augmentation.lean:333`), rerun at the pinned choice: on
`S`, the ranking is injective, has values `< |S|`, and every vertex has
at most `k` lower-ranked neighbours inside `S`, for every valid
low-degree bound `k`. -/
theorem mdRankAux_props (F : SimpleGraph (Fin n)) {k : ℕ}
    (hk : LowDegreeVertices F k) :
    ∀ (m : ℕ) (S : Finset (Fin n)), S.card ≤ m →
      Set.InjOn (mdRankAux F S) ↑S ∧
      (∀ v ∈ S, mdRankAux F S v < S.card) ∧
      (∀ v ∈ S, ((nbrsIn F S v).filter
        (fun u => mdRankAux F S u < mdRankAux F S v)).card ≤ k) := by
  classical
  intro m
  induction m with
  | zero =>
      intro S hScard
      have : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hScard)
      subst this
      exact ⟨by simp, by simp, by simp⟩
  | succ m ih =>
      intro S hScard
      rcases S.eq_empty_or_nonempty with rfl | hS
      · exact ⟨by simp, by simp, by simp⟩
      have hv₀S : minDegVert F S hS ∈ S := minDegVert_mem F S hS
      set v₀ := minDegVert F S hS with hv₀
      have hv₀deg : (nbrsIn F S v₀).card ≤ k :=
        card_nbrsIn_minDegVert_le hk S hS
      have hcard : (S.erase v₀).card = S.card - 1 :=
        Finset.card_erase_of_mem hv₀S
      have hcpos : 0 < S.card := Finset.card_pos.2 hS
      have heq : ∀ x, mdRankAux F S x =
          if x = v₀ then S.card - 1 else mdRankAux F (S.erase v₀) x :=
        fun x => mdRankAux_of_nonempty F hS x
      obtain ⟨hinj', hlt', hdeg'⟩ := ih (S.erase v₀) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · -- injectivity on `S`
        intro x hx y hy hxy
        rw [heq x, heq y] at hxy
        by_cases hx0 : x = v₀ <;> by_cases hy0 : y = v₀
        · rw [hx0, hy0]
        · exfalso
          have hyl := hlt' y (Finset.mem_erase.2 ⟨hy0, hy⟩)
          rw [if_pos hx0, if_neg hy0] at hxy
          rw [hcard] at hyl
          omega
        · exfalso
          have hxl := hlt' x (Finset.mem_erase.2 ⟨hx0, hx⟩)
          rw [if_neg hx0, if_pos hy0] at hxy
          rw [hcard] at hxl
          omega
        · rw [if_neg hx0, if_neg hy0] at hxy
          exact hinj' (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hx0, hx⟩))
            (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hy0, hy⟩)) hxy
      · -- values below the card
        intro v hv
        rw [heq v]
        by_cases hv0 : v = v₀
        · rw [if_pos hv0]
          omega
        · rw [if_neg hv0]
          have hvl := hlt' v (Finset.mem_erase.2 ⟨hv0, hv⟩)
          rw [hcard] at hvl
          omega
      · -- the back-degree bound
        intro v hv
        by_cases hv0 : v = v₀
        · subst hv0
          exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hv₀deg
        · have hvE : v ∈ S.erase v₀ := Finset.mem_erase.2 ⟨hv0, hv⟩
          have hvlt := hlt' v hvE
          refine le_trans (Finset.card_le_card ?_) (hdeg' v hvE)
          intro u hu
          obtain ⟨huN, hulr⟩ := Finset.mem_filter.1 hu
          obtain ⟨huS, huadj⟩ := mem_nbrsIn.1 huN
          rw [heq u, heq v, if_neg hv0] at hulr
          have hu0 : u ≠ v₀ := by
            intro hc
            rw [if_pos hc] at hulr
            rw [hcard] at hvlt
            omega
          rw [if_neg hu0] at hulr
          exact Finset.mem_filter.2
            ⟨mem_nbrsIn.2 ⟨Finset.mem_erase.2 ⟨hu0, huS⟩, huadj⟩, hulr⟩

/-- **The pinned greedy elimination ranking** of a graph. -/
noncomputable def mdRank (F : SimpleGraph (Fin n)) : Fin n → ℕ :=
  mdRankAux F Finset.univ

theorem mdRank_injective (F : SimpleGraph (Fin n)) :
    Function.Injective (mdRank F) := by
  have h := (mdRankAux_props F (lowDegreeVertices_card F) n Finset.univ
    (by simp)).1
  intro x y hxy
  exact h (by simp) (by simp) hxy

/-- The pinned ranking's values are already positions: `mdRank F v < n`
— what lets the permutation below be direct, with no sorting layer. -/
theorem mdRank_lt (F : SimpleGraph (Fin n)) (v : Fin n) : mdRank F v < n := by
  have h := (mdRankAux_props F (lowDegreeVertices_card F) n Finset.univ
    (by simp)).2.1
  simpa using h v (Finset.mem_univ v)

/-- **The pinned peel attains every valid bound** — the sInf-minimality
attainment: `BackDegLE F (mdRank F) k` for *every* `k` with
`LowDegreeVertices F k`, in particular at `elimBound F`. This is the
clause that makes `mdRank` a drop-in replacement for the choice-picked
`elimRank`. -/
theorem mdRank_backDegLE {F : SimpleGraph (Fin n)} {k : ℕ}
    (hk : LowDegreeVertices F k) : BackDegLE F (mdRank F) k := by
  classical
  have h := (mdRankAux_props F hk n Finset.univ (by simp)).2.2
  intro v
  refine le_trans (le_of_eq ?_) (h v (Finset.mem_univ v))
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_nbrsIn, Finset.mem_univ,
    true_and]
  rfl

/-- **The pinned greedy elimination permutation**: direct, since the
ranking's values are positions — `(mdPerm F v : ℕ) = mdRank F v` holds
by `rfl`, so the machine's rank array *is* the abstract order's. -/
noncomputable def mdPerm (F : SimpleGraph (Fin n)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun v => (⟨mdRank F v, mdRank_lt F v⟩ : Fin n))
    (Finite.injective_iff_bijective.mp fun _u _v h =>
      mdRank_injective F (congrArg Fin.val h))

@[simp] theorem mdPerm_val (F : SimpleGraph (Fin n)) (v : Fin n) :
    ((mdPerm F v : Fin n) : ℕ) = mdRank F v := rfl

/-- Clause 5's shape at the minimal bound: the pinned permutation
eliminates `F` at `elimBound F`. -/
theorem mdPerm_backDegLE (F : SimpleGraph (Fin n)) :
    BackDegLE F (fun v => ((mdPerm F v : Fin n) : ℕ)) (elimBound F) :=
  mdRank_backDegLE (lowDegreeVertices_elimBound F)

/-- Clause 3 at the pinned permutation: the base orientation along it
has in-degrees at most the minimal elimination bound. -/
theorem inDegLE_baseOr_mdPerm (G : SimpleGraph (Fin n)) :
    (baseOr G (mdPerm G)).InDegLE (elimBound G) := by
  intro v
  refine le_trans (le_of_eq ?_) (mdPerm_backDegLE G v)
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Finset.mem_coe, mem_baseOr, Set.mem_setOf_eq, Fin.lt_def]

/-! ## §2 The deterministic chain and the routine -/

/-- A greedy round along the pinned ranking is a `GreedyFratRound`: the
witness ordering is the pinned peel itself — it attains every valid
bound (`mdRank_backDegLE`) — and every fraternal-only new arc goes
along it (`greedyStep`'s fallback never fires on a fraternal link). -/
theorem greedyFratRound_greedyStep_md {D : Orientation n} :
    GreedyFratRound D (greedyStep (mdRank (fratGraph D)) D) := by
  intro k hk
  refine ⟨mdRank (fratGraph D), mdRank_backDegLE hk, ?_⟩
  intro _u _v hu hold _htr hadj
  rcases mem_greedyStep.1 hu with h | ⟨-, -, hc⟩
  · exact absurd h hold
  · rcases hc with hlt | hno
    · exact hlt
    · exact absurd (Or.inr (fratGraph_adj.1 hadj).2.symm) hno

/-- **The deterministic greedy chain**: `greedyChain` with `elimRank`
replaced by the pinned `mdRank` at the base and in every round. Every
ingredient is extensionally determined by `G` — the chain a machine
augmentation pass can be proved against. -/
noncomputable def mdChain (G : SimpleGraph (Fin n)) : ℕ → Orientation n
  | 0 => baseOr G (mdPerm G)
  | i + 1 => greedyStep (mdRank (fratGraph (mdChain G i))) (mdChain G i)

theorem isAugChain_mdChain (G : SimpleGraph (Fin n)) (R : ℕ) :
    IsAugChain G (mdChain G) R :=
  ⟨baseOr_orients G (mdPerm G), fun i _ =>
    augStep_greedyStep (mdRank_injective (fratGraph (mdChain G i)))⟩

theorem greedyFratRound_mdChain (G : SimpleGraph (Fin n)) (i : ℕ) :
    GreedyFratRound (mdChain G i) (mdChain G (i + 1)) :=
  greedyFratRound_greedyStep_md

/-- **The machine ordering routine**: the deterministic chain, the
pinned peel of its final symmetrized augmented graph, the two minimal
elimination bounds. `steps := 0` is the same placeholder as the landed
`greedyOrderingRoutine`'s — F5/E12 own the `time` field. This is the
routine F7 instantiates the headline's `∃ ord` with. -/
noncomputable def mdOrderingRoutine (R : ℕ) : CoverSpec.OrderingRoutine :=
  fun _m G =>
    { chain := mdChain G
      order := mdPerm (mdChain G R).toGraph
      inDeg := elimBound G
      backDeg := elimBound (mdChain G R).toGraph
      steps := 0 }

/-- **The validity of the machine routine, with no hypothesis at all**:
the full six-clause `AugChainData` postcondition, both elimination
bounds minimal in the `ElimPost` sense — the mirror of
`greedyOrderingRoutine_data`, now at a machine-matchable routine. The
sInf-minimality clauses are attained because the pinned min-degree peel
attains `elimBound` (`mdRank_backDegLE`). -/
theorem mdOrderingRoutine_data (R : ℕ) :
    ∀ (m : ℕ) (G : SimpleGraph (Fin m)),
      AugChainData G ((mdOrderingRoutine R) m G).chain
        ((mdOrderingRoutine R) m G).order R
        ((mdOrderingRoutine R) m G).inDeg
        ((mdOrderingRoutine R) m G).backDeg :=
  fun _m G =>
    ⟨isAugChain_mdChain G R,
     fun i _ => greedyFratRound_mdChain G i,
     inDegLE_baseOr_mdPerm G,
     fun _k' hk' => elimBound_le hk',
     mdPerm_backDegLE (mdChain G R).toGraph,
     fun _k' hk' => elimBound_le hk'⟩

/-- The interface corollary, as for the landed routine: only the `time`
field of `CoverSpec.IsCoverOrdering` is owed. -/
theorem isCoverOrdering_mdOrderingRoutine (C : GraphClass) (R : ℕ) (δ f : ℝ)
    (htime : ∀ (n' : ℕ) (Gn : SimpleGraph (Fin n')), C n' Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ((mdOrderingRoutine R) m G).steps ≤ f * (m : ℝ) ^ (1 + 2 * δ)) :
    CoverSpec.IsCoverOrdering C R δ f (mdOrderingRoutine R) :=
  ⟨fun _n _Gn _hGn m G _hsub => mdOrderingRoutine_data R m G, htime⟩

end Lax3Proofs.CoverRoutine

/-! ## §3 The machine pass at the routine, split at its seam -/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.CoverRoutine (mdChain mdPerm mdOrderingRoutine)

variable {L n₀ : ℕ}

/-- **Named residual (1a-i): the augmentation pass** — per admissible
level arena at the word bound of every admissible input, from
`CovOrderIn`'s exact precondition, compute the `R` deterministic
augmentation rounds and leave the *augmented* graph
`(mdChain A.G R).toGraph` as a deletable adjacency region, preserving
the arena, the allocations, the peel scratch `Smp` and the sweep
scratch `Ssw`. The machine construction behind it (and its
`f·m^{1+2δ}` price) is the `CoverSpec` deferral chain — E12's priced
obligation. -/
def CovAugAdjIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Sag Smp Ssw : ℕ → Env → Prop) (agC : ℕ → Com)
    (Kag : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Sag j σ ∧ Smp j σ ∧ Ssw j σ)
        (agC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          DelAdjSt (aoO j) (ajO j) (dgO j) (mtO j)
            (mdChain A.G R).toGraph ∅ σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (Kag j A)

/-- **Named residual (1a-ii): the min-degree peel pass** — from the
augmented graph's deletable region, peel: repeatedly pick the
minimum-degree live vertex (smallest index tie-break — `dg` maintained
by the delete contract, a bucket queue over degrees keeps the minimum
at amortized `O(1)`), write its rank counting down from `A.N - 1`,
delete it. Leaves `RankArr` at `mdPerm (mdChain A.G R).toGraph` — the
routine's order, definitionally — preserving the arena, the
allocations and the sweep scratch. -/
def CovMdPeelIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Smp Ssw : ℕ → Env → Prop) (mpC : ℕ → Com)
    (Kmp : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          DelAdjSt (aoO j) (ajO j) (dgO j) (mtO j)
            (mdChain A.G R).toGraph ∅ σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
        (mpC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          RankArr (ra j) (mdPerm (mdChain A.G R).toGraph) σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Ssw j σ')
        (Kmp j A)

open Classical in
/-- **Residual (1a) of the cover leaf, discharged at the machine
routine's seam**: `CovOrderIn` holds — verbatim, at
`ord := mdOrderingRoutine R` — of the sequenced program `agC j ; mpC j`
at the summed budget, with the ordering pass's scratch descriptor the
conjunction of the two passes'. The rank array the peel leaves *is*
the routine's order: `(mdOrderingRoutine R A.N A.G).order` unfolds to
`mdPerm (mdChain A.G R).toGraph`. -/
theorem covOrderIn_of_aug_mdPeel (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Sag Smp Ssw : ℕ → Env → Prop) (agC mpC : ℕ → Com)
    (Kag Kmp : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hag : CovAugAdjIn C hC φ R G c w q ℓp htabF hbf Adm ca co
      aoO ajO dgO mtO Sag Smp Ssw agC Kag)
    (hmp : CovMdPeelIn C hC φ R G c w q ℓp htabF hbf Adm ca co ra
      aoO ajO dgO mtO Smp Ssw mpC Kmp) :
    CovOrderIn C hC φ (mdOrderingRoutine R) G c w q ℓp htabF hbf Adm ca co ra
      (fun j σ => Sag j σ ∧ Smp j σ) Ssw
      (fun j => .seq (agC j) (mpC j))
      (fun j A => Kag j A + Kmp j A) := by
  intro x hx j hj A hAdm hbot
  refine Spec.seq
    ((hag x hx j hj A hAdm hbot).pre ?_)
    (hmp x hx j hj A hAdm hbot) ?_ ?_
  · -- the ordering precondition is the augmentation pass's
    rintro σ ⟨hA, hca, hco, ⟨hSag, hSmp⟩, hSsw⟩
    exact ⟨hA, hca, hco, hSag, hSmp, hSsw⟩
  · -- the augmentation pass lands in the peel's precondition
    rintro σ σ' - ⟨hA', hadj', hca', hco', hSmp', hSsw'⟩
    exact ⟨hA', hadj', hca', hco', hSmp', hSsw'⟩
  · -- the peel's postcondition is the ordering's: the rank array is at
    -- the routine's order, definitionally
    rintro σ σ' σ'' - - ⟨hA'', hra'', hca'', hco'', hSsw''⟩
    exact ⟨hA'', hra'', hca'', hco'', hSsw''⟩

end Lax3Proofs.Prog
