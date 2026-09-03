import Lax3Proofs.CoverDegree

/-!
# The cover's running time, written as the assumption it is

**Everything in this file except `IsCoverOrdering.time` is derived. That one
field is the design's single unproved import, and it is stated as a hypothesis a
caller supplies — not as an `axiom`, and not hidden inside a definition.**

`plans/nowhere-dense-model-checking/algorithm-v2.md` §4 charges the routine
`cover A r` at `O(‖A‖^{1+2δ})`, and §7 makes that charge the leading term of the
whole cost recursion. Nothing in this package proves it. This file writes the
charge down once, in the shape §7 consumes, and derives from it everything the
landed layer already gives — so that the surface of the assumption is exactly
the part nobody has proved.

## What is assumed, and what is derived

An `OrderingRoutine` is an abstract routine: for every carrier `Fin m` and every
graph on it, an augmentation chain, an ordering, the two elimination bounds, and
a **real-valued step count**. `IsCoverOrdering C R δ f A` has two fields:

* `data` — the routine's output satisfies `CoverDegree.AugChainData`, the
  six-clause machine postcondition of the `R*` ordering phase
  (`CoverDegree.lean:642-649`). This is a *correctness* assumption, and it is
  the weaker half: the mathematics behind it is landed
  (`Augmentation.exists_augChain_wcol` `:1030`, `exists_greedy_round` `:1157`,
  `greedy_chain_inDegLE` `:1175`), what is missing is only the assembly of a
  greedy chain whose two eliminations are *minimal* in the `ElimPost` sense.
* `time` — `steps ≤ f · m^(1+2δ)`. **This is the leaf's real content.** See
  "what would discharge this" below.

Derived here, not assumed:

* `cover_of_isCoverOrdering` — the routine's ordering yields an
  `rc`-neighbourhood cover of radius `2·rc` whose family is the wreach fibre
  family `fun u => {w | u ∈ wreach G π (2·rc) w}` and whose degree is
  `⌈c·m^δ⌉₊`, with `c` fixed before the graph. This is
  `CoverDegree.exists_cover_degree` (`:366-378`) applied to the assumed
  `AugChainData`; the covering and radius clauses come from
  `OrderedCovers.isNeighborhoodCover_wreach` (`:111-113`) inside it.
* `wreach_degree_of_isCoverOrdering` — the same bound in the form
  `(wreach G π (2·rc) v).ncard ≤ ⌈c·m^δ⌉₊`
  (`CoverDegree.wreach_degree_of_data` `:654-660`).

Two guarantees the design also wants from `cover` are deliberately **not**
assumed here, because they are being proved elsewhere and assuming them would
hide real work: the path-closure of a cluster (`algorithm-v2.md` §5) and the
`ctr` assignment `ctr v := π-min (wreach_π(A,R,v))` (§4). Both are consequences
of the same wreach fibres and neither needs a new hypothesis.

## The exponent is `1 + 2δ`

`δ` is the *wcol* parameter — the exponent of the cover's degree bound
`⌈c·m^δ⌉₊`. The cover's *time* costs two of it. Grohe–Kreutzer–Siebertz's own
accounting for their own cover algorithm (`references/gks/nowheredense.tex`
:1459-1517) sets `δ := ε/2` and closes at `2n^{1+2δ} =: f(r,ε)·n^{1+ε}`; the
ordering it runs on is charged separately at `g(r,δ)·n^{1+δ}` (tex:1460-1463),
which the `1+2δ` term dominates. Rev 4 of `algorithm-v2.md` charged the routine
at `N^{1+δ}` in §4 while quoting `2δ` in §6.2. `E4` splits `ε` as
`δ = ε/(ℓ+2)` (`algorithm-v2.md:323`) precisely so that this term is affordable,
so `1 + 2*δ` is the exponent that must appear here.

## `f` is fixed before the input is read

`CoverOrderingTime` quantifies `f` (and the routine) **before** `n`, `Gn`, `m`
and `G` — `algorithm-v2.md` §3, "constants are free, `n^δ` is not". The
per-graph reading, where `f` may be chosen after seeing `G`, is worthless:
`exists_pointwise_bound` below proves it holds for *every* routine on every
nonempty carrier. That control is the reason the binder order is part of the
statement rather than an accident of it.

## What would discharge `IsCoverOrdering.time`

The chain of deferrals under this bound was opened link by link on 2026-08-17.
It terminates in a proof, and what is left is smaller than a paper:

1. GKS's cover theorem, `thm:alg-covers`, `references/gks/nowheredense.tex`
   :1254-1263 — cover of radius `2r`, degree `≤ n^ε`, in `f(r,ε)·n^{1+ε}`.
2. Its only superlinear stage is the *ordering*, `thm:computingorientation`
   (tex:1342-1352): for a nowhere dense class, an `r`-transitive fraternal
   augmentation with `Δ⁻(H) ≤ n^ε`, computable in `f(r,ε)·n^{1+ε}`. Its entire
   proof is the bracket *[Nešetřil–Ossona de Mendez 2005, Corollary 4.2,
   Theorem 4.3]*.
3. That resolves onto `references/nodm05/BEII.tex` §4, and the algorithm is
   there in full: transitivity arcs in `O(md(G)²·n)` (:615-620), fraternity
   edges in `O(md(G)²·n)` with `|L| ≤ md(G)²·n/2` (:672-674), and
   simplification + low-indegree orientation + merge in `O(md(G)²·n)`
   (:676-678), with the in-degree recurrence `md(G_{i+1}) ≤ md(G_i)² + 2∇₀(G_i)`
   at :570-571. The low-indegree orientation is itself proved unconditionally:
   an acyclic orientation of in-degree `⌊2∇₀(G)⌋` in `O(n+m)` (:446-499).
4. Part II's Lemma 4.1 (:530-542) is only a citation — *"Special case of Lemma
   6.1 of [POMNI]"* — and `[POMNI]` is part I, `references/nodm05i/BEI.tex`,
   where Lemma 6.1 is **proved in full** (:1064-1091, the ball-family argument)
   with Corollary 6.2 (:1092-1101) bounding `md(G_i)` along the chain.

What is *not* there: part II's Theorem 4.3 (:679-688) is stated for a class of
**bounded expansion** and fixed `c`, in time **`O(n)`**, and its Corollary 4.2
(:545-567) likewise opens *"Let `C` be a class with expansion bounded by a
function `f`"*. GKS cite both for a **nowhere dense** class with `Δ⁻ ≤ n^ε` in
`f(r,ε)·n^{1+ε}`. Those are different statements, and the difference is exactly
where the `1+2δ` comes from: with `md(G_i) ≤ n^{δ}` rather than a constant, the
per-round cost `O(md²·n)` reads `O(n^{1+2δ})`, and the round count is fixed in
advance. So discharging `time` needs (i) the nowhere-dense instantiation of
Corollary 4.2 — `∇_s` subpolynomial, closed under the `c`-fold composition of
the polynomials `P_i`, with an explicit threshold `n ≥ f(r,ε)` — and (ii) the
`O(md²·n)` accounting of the orientation step at `md = n^δ` rather than `md =
O(1)`. It does not need a paper this repository lacks.

## How a later leaf connects `steps` to a machine

`steps` is deliberately an abstract real-valued step count, not a word-RAM
program: this leaf is a statement leaf and does not build one. `E12`, the
`Arena` implementation (`execution-plan.md:306-315`), is expected to instantiate
`OrderingRoutine` with the actual `cover` implementation and read `steps` off
`Lax67`'s timed computation — at which point `IsCoverOrdering.data` becomes a
correctness proof about the program and `IsCoverOrdering.time` becomes the one
surviving hypothesis, in the same shape, about its running time.
-/

namespace Lax3Proofs.CoverSpec

open scoped SimpleGraph
open Lax3.NeighborhoodCovers
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity
open Lax12.ColoringNumbers
open Lax3Proofs.Augmentation
open Lax3Proofs.OrderedCovers
open Lax3Proofs.CoverDegree

/-! ### The routine -/

/-- **What one call of the ordering phase returns**, on the carrier `Fin m`:
the augmentation chain, the ordering read off its last round, the in-degree
bound of the first elimination and the back-degree bound of the last — the four
data `CoverDegree.AugChainData` constrains — together with the number of steps
the call took.

`steps` is an abstract cost, in `ℝ` so that it composes with §7's real-valued
recursion without a cast at every use. -/
structure OrderingOutput (m : ℕ) where
  /-- The augmentation chain the phase folds. -/
  chain : ℕ → Orientation m
  /-- The vertex order its final elimination defines. -/
  order : Equiv.Perm (Fin m)
  /-- The in-degree bound of the phase's first elimination. -/
  inDeg : ℕ
  /-- The back-degree bound of the phase's last elimination. -/
  backDeg : ℕ
  /-- The abstract step count of the call. -/
  steps : ℝ

/-- **An ordering routine**: a choice of output for every graph on every
carrier. Total, because the design calls `cover` at every node of the recursion
and on arenas of every size. -/
def OrderingRoutine : Type := ∀ m : ℕ, SimpleGraph (Fin m) → OrderingOutput m

/-! ### The assumption -/

/-- **The design's one unproved import, as a hypothesis.**

`IsCoverOrdering C R δ f A` says that on the class `C`, the routine `A`
computes an `R`-round ordering phase correctly (`data`) and in at most
`f · m^(1+2δ)` steps (`time`), uniformly over every subgraph copy `G ⊑ Gn` of
every member, on `G`'s own carrier.

Neither field is proved anywhere in this package. `data` is the weaker half —
the mathematics behind it is landed and only the assembly is missing. **`time`
is the claim.** The module docstring says what would discharge it and pins the
four links of the deferral chain to file and line. -/
structure IsCoverOrdering (C : GraphClass) (R : ℕ) (δ f : ℝ)
    (A : OrderingRoutine) : Prop where
  /-- The routine's output meets the six-clause postcondition of the `R*`
  ordering phase. -/
  data : ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
    ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
      AugChainData G (A m G).chain (A m G).order R (A m G).inDeg (A m G).backDeg
  /-- **The unproved claim.** The call costs at most `f · m^(1+2δ)` steps —
  `1 + 2*δ`, not `1 + δ`: `δ` is the wcol parameter and the cover costs two of
  it (`gks tex:1459-1517`). -/
  time : ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
    ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
      (A m G).steps ≤ f * (m : ℝ) ^ (1 + 2 * δ)

/-- **The assumption, quantified.** For every round count `R` and every
`δ > 0` there are a constant `f` and a routine `A` — *both fixed before any
graph is read* — such that `A` is a correct ordering phase costing at most
`f · m^(1+2δ)` steps on every subgraph copy of every member of `C`.

This is the hypothesis `E4`'s cost recurrence takes: its `δ` is the wcol
parameter of `D(N) = ⌈c_D·N^δ⌉` and the leading term of §7's recursion is
`a·N^{1+2δ}` with this `δ`. At the root `E4` sets `δ = ε/(ℓ+2)`
(`algorithm-v2.md:323`).

It is a `Prop`, taken as a hypothesis wherever it is needed. It is not an
`axiom` and nothing in this package proves it. -/
def CoverOrderingTime (C : GraphClass) : Prop :=
  ∀ (R : ℕ) (δ : ℝ), 0 < δ →
    ∃ f : ℝ, ∃ A : OrderingRoutine, IsCoverOrdering C R δ f A

/-! ### What follows from it, and from the landed layer

The point of the split: the cover, its radius, its covering property and its
degree are all *derived*. Only the step count is assumed. -/

/-- **The cover of the routine's ordering.** Given the assumption's correctness
field alone — the time field is not used — the wreach fibres of the routine's
ordering are an `rc`-neighbourhood cover of radius `2·rc` and degree
`⌈c·m^δ⌉₊`, with `c` fixed before the graph.

Everything here is `CoverDegree.exists_cover_degree` (`:366-378`); the covering
and radius clauses inside it are `OrderedCovers.isNeighborhoodCover_wreach`
(`:111-113`), which holds for *every* ordering. Nothing about the cover's
structure is assumed. -/
theorem cover_of_isCoverOrdering (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (δ f : ℝ) (hδ : 0 < δ)
    {A : OrderingRoutine} (hA : IsCoverOrdering C R δ f A) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        IsNeighborhoodCover G rc
          (fun u => {w | u ∈ wreach G (A m G).order (2 * rc) w}) ⌈c * (m : ℝ) ^ δ⌉₊ := by
  obtain ⟨c, hc⟩ := exists_cover_degree C hC rc R t ht hrt δ hδ
  refine ⟨c, fun n Gn hGn m G hsub => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hA.data n Gn hGn m G hsub
  exact hc n Gn hGn m G hsub (A m G).chain (A m G).order (A m G).inDeg (A m G).backDeg
    h₁ h₂ h₃ h₄ h₅ h₆

/-- **The degree bound in wreach form**, the shape a cover pass consumes:
`(wreach G π (2·rc) v).ncard ≤ ⌈c·m^δ⌉₊`. Again derived, from
`CoverDegree.wreach_degree_of_data` (`:654-660`). -/
theorem wreach_degree_of_isCoverOrdering (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (δ f : ℝ) (hδ : 0 < δ)
    {A : OrderingRoutine} (hA : IsCoverOrdering C R δ f A) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ v : Fin m, (wreach G (A m G).order (2 * rc) v).ncard ≤ ⌈c * (m : ℝ) ^ δ⌉₊ := by
  obtain ⟨c, hc⟩ := wreach_degree_of_data C hC rc R t ht hrt δ hδ
  exact ⟨c, fun n Gn hGn m G hsub v =>
    hc n Gn hGn m G hsub (A m G).chain (A m G).order (A m G).inDeg (A m G).backDeg
      (hA.data n Gn hGn m G hsub) v⟩

/-- **The two halves together, in the form `E4` takes.** From the assumption
`CoverOrderingTime C` and nowhere denseness: a routine, a degree constant `c`
and a time constant `f` — all three fixed before the input — such that at every
subgraph copy the routine returns a cover of degree `⌈c·m^δ⌉₊` and costs at most
`f·m^(1+2δ)` steps.

The degree half is a theorem of this package; the time half is the hypothesis.
-/
theorem exists_cover_routine (C : GraphClass) (hC : NowhereDense C)
    (hT : CoverOrderingTime C) (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (A : OrderingRoutine) (c f : ℝ),
      ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
        ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
          IsNeighborhoodCover G rc
              (fun u => {w | u ∈ wreach G (A m G).order (2 * rc) w}) ⌈c * (m : ℝ) ^ δ⌉₊ ∧
            (A m G).steps ≤ f * (m : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨f, A, hA⟩ := hT R δ hδ
  obtain ⟨c, hc⟩ := cover_of_isCoverOrdering C hC rc R t ht hrt δ f hδ hA
  exact ⟨A, c, f, fun n Gn hGn m G hsub =>
    ⟨hc n Gn hGn m G hsub, hA.time n Gn hGn m G hsub⟩⟩

/-! ### Two controls on the statement

Neither is mathematics; both are checks that the statement above says what it
is meant to say. -/

section Controls

/-- **Why `f` is quantified before the graph.** For *any* routine, any `δ`, and
any single graph on a nonempty carrier there is an `f` making the time bound
true — the per-graph reading of the assumption constrains nothing at all.

So a version of `CoverOrderingTime` that moved `∃ f` inside the graph binders
would be a weakening with no content, and would not discharge this leaf. -/
theorem exists_pointwise_bound (A : OrderingRoutine) (δ : ℝ) (m : ℕ) (hm : 0 < m)
    (G : SimpleGraph (Fin m)) :
    ∃ f : ℝ, (A m G).steps ≤ f * (m : ℝ) ^ (1 + 2 * δ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpow : (0 : ℝ) < (m : ℝ) ^ (1 + 2 * δ) := Real.rpow_pos_of_pos hm' _
  exact ⟨(A m G).steps / (m : ℝ) ^ (1 + 2 * δ), by
    rw [div_mul_cancel₀ _ (ne_of_gt hpow)]⟩

/-- The empty orientation, the only piece of data the control below needs. -/
private def emptyOrientation (m : ℕ) : Orientation m :=
  ⟨fun _ => ∅, fun _ => by simp, fun _ _ h => by simp at h⟩

/-- **The assumption is satisfiable.** On a class with no members it holds, so
nothing in the statement of `CoverOrderingTime` is accidentally contradictory —
a hypothesis that could never hold would make every consumer of it vacuous. -/
theorem coverOrderingTime_of_isEmpty (C : GraphClass) (hC : ∀ n G, ¬ C n G) :
    CoverOrderingTime C :=
  fun _R _δ _hδ =>
    ⟨0, fun m _ => ⟨fun _ => emptyOrientation m, 1, 0, 0, 0⟩,
      ⟨fun n Gn hGn => absurd hGn (hC n Gn), fun n Gn hGn => absurd hGn (hC n Gn)⟩⟩

end Controls

end Lax3Proofs.CoverSpec
