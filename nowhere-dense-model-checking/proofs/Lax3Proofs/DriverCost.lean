import Lax3Proofs.DriverArena
import Lax3Proofs.CostRecurrence
import Lax3Proofs.CoverEdgeSum

/-!
# The abstract cost of the driver (E9, deliverable 4)

`algorithm-v2.md` §7's recurrence, instantiated on the driver of
`DriverArena`. This file delivers, in order of decreasing completeness:

1. **The accounting** — `dcost`, the driver's abstract step count, one
   real number per node of the recursion tree, charged by §4's table:
   the cover routine's own `steps` at the node, a per-child charge
   *linear in the child's weight* with the multiplier `nodeCharge`
   (restrict + profiles + isolate + readback + the guarded greedy
   scatter), and the recursive charges. The leaf (fuel `0` or edgeless)
   is charged linearly (`BotTables`, §6.4).

   **Hazard 3 lives here.** The greedy scatter charge is
   `scatterBudget S j` per unit of child weight — the sum of `σ.t` over
   the schedule's scatter atoms at this depth. Charging `t · ‖B‖` for a
   call `greedyScatter(B, r, P, t)` is *only* sound for the **guarded**
   routine of §6.5, which returns immediately at `t = 0` and stops after
   `t` picks: at `t = 0` the charge here is `0`, and the unguarded
   routine would silently run the full greedy at `Θ(‖B‖²)` with a
   correct answer. The abstract charge encodes the guard; E12's machine
   routine must implement it.

2. **The per-node inequality** (`dcost_node_le`) — §7's node shape with
   the driver's *concrete* children: cover ≤ `f · ‖A‖^(1+2δ)` (from
   `CoverSpec.IsCoverOrdering.time`, carrier ≤ weight), children ≤
   `c·nodeCharge · (c_D + 1) · ‖A‖^(1+δ)`. The mass clause is **(★)
   discharged**: each child's weight is at most its cluster's weight
   (`weight_childArena_le` — the restriction loses vertices to none and
   edges to isolation only), and the cluster weights sum by
   `CoverEdgeSum.sum_clusterWeight_le_rpow` under the cover-degree
   bound, ceiling included (`sum_child_weight_le`).

3. **The named remainder** — `CostMajorant`, the one honest `Prop`
   between this file and §7's headline: a *size-indexed* majorant
   `T : depth → weight → ℝ` of the arena-indexed `dcost` satisfying
   `CostRecurrence.IsCostRecurrence`. Given it, the headline follows
   with **zero further conditions** (`dcost_root_le_of_majorant`, via
   `cost_root_le_chosenK` — `K := c_D + 1 + A` chosen, not constrained).

   *Why it is left as a hypothesis rather than proved*: `dcost` is
   indexed by arenas, `IsCostRecurrence` by `(depth, size)` pairs. The
   sup over arenas of a given weight is not available (the channel
   `hist` makes the arena type infinite), so the bridge is either a
   size-indexed re-run of `cost_le_of_isCostRecurrence`'s downward
   induction over the driver's actual recursion tree — mathematically
   `dcost_node_le` + the landed arithmetic, nothing new — or a
   refactor of `IsCostRecurrence` to an arena-shaped `node` clause.
   Either is a mechanical follow-up leaf consuming `dcost_node_le` and
   `chosenK_step`; neither changes a constant or an exponent. The
   split proposal in the campaign record names it.
-/

namespace Lax3Proofs.Driver

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences
open Lax12.UniformQuasiWideness Lax12.ColoringNumbers
open Lax3Proofs.LocalityFun

variable {L n₀ : ℕ}

/-! ### The accounting -/

/-- `‖A‖`: vertices plus edges (`algorithm-v2.md:431`). -/
noncomputable def weight {Λ : ℕ} (A : Arena Λ n₀) : ℕ :=
  Lax3Proofs.CoverEdgeSum.graphWeight A.G

/-- **The greedy scatter budget of one depth** (hazard 3): the sum of
`σ.t` over all scatter atoms of all decompositions at depth `j`. The
charge of one guarded call `greedyScatter(B, σ.r, P, σ.t)` is
`σ.t · ‖B‖` — zero at `σ.t = 0`, which is exactly what the `t = 0` guard
of §6.5 buys; without the guard the true cost would be `Θ(‖B‖²)`
regardless of `t`. -/
noncomputable def scatterBudget (S : Setup L) (j : ℕ) : ℕ :=
  ((F S j).map fun β =>
    ((scatterAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)).map
      fun σ => σ.t).sum).sum

/-- The per-child linear charge multiplier at depth `j`: one unit for
restrict + profiles + isolate (§4's aggregate, the `(2 + ℓR)·c_D` part
of `a` absorbing what is superlinear in it), the readback (`|ℱ_j|` per
owned vertex), and the guarded greedy scatter budget. A constant of the
schedule — fixed before the input is read. -/
noncomputable def nodeCharge (S : Setup L) (j : ℕ) : ℕ :=
  1 + (F S j).length + scatterBudget S j

open Classical in
/-- **The driver's abstract step count.** One real number per node of
the recursion tree of `tablesAux`, mirroring its structure: the leaf is
charged linearly; a node pays the cover routine's own `steps`, and, for
each centre with a nonempty cluster, a linear charge on the child plus
the child's own cost. (The empty clusters are §5 line 15's skipped
centres; they cost nothing and are recursed on by nobody.) -/
noncomputable def dcostAux (S : Setup L) (ord : CoverSpec.OrderingRoutine) (c : ℝ) :
    (fuel : ℕ) → (j : ℕ) → (A : Arena (S.pal j) n₀) → ℝ
  | 0, _, A => c * (weight A : ℝ)
  | fuel + 1, j, A =>
    if A.G = ⊥ then c * (weight A : ℝ)
    else
      (ord A.N A.G).steps +
        ∑ u : Fin A.N,
          (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
            (c * (nodeCharge S j : ℝ)) *
                (weight (childArena S A ((ord A.N A.G).order) u) : ℝ)
              + dcostAux S ord c fuel (j + 1)
                  (childArena S A ((ord A.N A.G).order) u)
          else 0)

/-- The cost of a depth-`j` node, at fuel `ℓ − j` — the mate of
`tables`. -/
noncomputable def dcost (S : Setup L) (ord : CoverSpec.OrderingRoutine) (c : ℝ)
    (j : ℕ) (A : Arena (S.pal j) n₀) : ℝ :=
  dcostAux S ord c (S.depth - j) j A

/-! ### The mass clause: (★) with the driver's concrete children -/

/-- **A child weighs no more than its cluster**: the carrier is the
cluster's, and every child edge is an internal edge of the cluster
(isolation only removes edges). This is the bridge from the driver's
children to `CoverEdgeSum`'s cluster weights. -/
theorem weight_childArena_le (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    weight (childArena S A π u) ≤
      Lax3Proofs.CoverEdgeSum.clusterWeight A.G (cluster S A π u) := by
  rw [weight, Lax3Proofs.CoverEdgeSum.graphWeight,
    Lax3Proofs.CoverEdgeSum.clusterWeight]
  refine Nat.add_le_add (le_of_eq rfl) ?_
  have hinj : Function.Injective
      (Sym2.map (fun a => ((childEquiv S A π u) a : Fin A.N))) :=
    Sym2.map.injective fun a b hab =>
      (childEquiv S A π u).injective (Subtype.ext hab)
  have himg : Sym2.map (fun a => ((childEquiv S A π u) a : Fin A.N)) ''
      (childArena S A π u).G.edgeSet ⊆
        Lax3Proofs.CoverEdgeSum.internalEdgeSet A.G (cluster S A π u) := by
    rintro e ⟨e', he', rfl⟩
    induction e' with
    | _ a b =>
      have he2 : (deleteVerts (preG S A π u) (Set.range (batchFn S A π u))).Adj a b :=
        he'
      have hadj : A.G.Adj ((childEquiv S A π u) a : Fin A.N)
          ((childEquiv S A π u) b : Fin A.N) := he2.1
      rw [Sym2.map_mk]
      refine ⟨hadj, ?_⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact ((childEquiv S A π u) a).2
      · exact ((childEquiv S A π u) b).2
  calc (childArena S A π u).G.edgeSet.ncard
      = (Sym2.map (fun a => ((childEquiv S A π u) a : Fin A.N)) ''
          (childArena S A π u).G.edgeSet).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (Lax3Proofs.CoverEdgeSum.internalEdgeSet A.G (cluster S A π u)).ncard :=
        Set.ncard_le_ncard himg (Set.toFinite _)

open Classical in
/-- **(★), discharged for the driver's children.** Under the cover
routine's degree bound — `⌈c_D · N^δ⌉₊`, ceiling included, at the
carrier `N = A.N` — the total weight of the nonempty children is at most
`(c_D + 1) · ‖A‖^(1+δ)`. `weight_childArena_le` per child, then
`CoverEdgeSum.sum_clusterWeight_le_rpow` for the cluster weights. -/
theorem sum_child_weight_le (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {cD δ : ℝ} (hcD : 0 ≤ cD) (hδ : 0 ≤ δ)
    (hW : 1 ≤ weight A)
    (hdeg : ∀ v : Fin A.N,
      {u : Fin A.N | v ∈ cluster S A π u}.ncard ≤ ⌈cD * (A.N : ℝ) ^ δ⌉₊) :
    ∑ u : Fin A.N, (if (cluster S A π u).Nonempty
        then (weight (childArena S A π u) : ℝ) else 0)
      ≤ (cD + 1) * (weight A : ℝ) ^ (1 + δ) := by
  have h1 : ∀ u : Fin A.N, (if (cluster S A π u).Nonempty
      then (weight (childArena S A π u) : ℝ) else 0)
      ≤ (Lax3Proofs.CoverEdgeSum.clusterWeight A.G (cluster S A π u) : ℝ) := by
    intro u
    split
    · exact_mod_cast weight_childArena_le S A π u
    · positivity
  calc ∑ u : Fin A.N, (if (cluster S A π u).Nonempty
        then (weight (childArena S A π u) : ℝ) else 0)
      ≤ ∑ u : Fin A.N,
          (Lax3Proofs.CoverEdgeSum.clusterWeight A.G (cluster S A π u) : ℝ) :=
        Finset.sum_le_sum fun u _ => h1 u
    _ = ((∑ u : Fin A.N,
          Lax3Proofs.CoverEdgeSum.clusterWeight A.G (cluster S A π u) : ℕ) : ℝ) := by
        push_cast
        rfl
    _ ≤ (cD + 1) * (weight A : ℝ) ^ (1 + δ) :=
        Lax3Proofs.CoverEdgeSum.sum_clusterWeight_le_rpow A.G _ cD δ hcD hδ hW hdeg

open Classical in
/-- **§7's node inequality, with the driver's concrete data.** At a node
with an edge, under the routine's time bound (`IsCoverOrdering.time`
shape, at the carrier) and its degree bound, one step of `dcostAux` is
within the recurrence's three charges: cover at `f·‖A‖^(1+2δ)`, children
at `c·nodeCharge·(c_D+1)·‖A‖^(1+δ)` — the mass clause is
`sum_child_weight_le` — and the recursive charges verbatim. -/
theorem dcost_node_le (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {c f cD δ : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) (hcD : 0 ≤ cD) (hδ : 0 ≤ δ)
    {fuel j : ℕ} (A : Arena (S.pal j) n₀) (hbot : A.G ≠ ⊥) (hW : 1 ≤ weight A)
    (hsteps : (ord A.N A.G).steps ≤ f * (A.N : ℝ) ^ (1 + 2 * δ))
    (hdeg : ∀ v : Fin A.N,
      {u : Fin A.N | v ∈ cluster S A ((ord A.N A.G).order) u}.ncard ≤
        ⌈cD * (A.N : ℝ) ^ δ⌉₊) :
    dcostAux S ord c (fuel + 1) j A ≤
      f * (weight A : ℝ) ^ (1 + 2 * δ)
      + (c * (nodeCharge S j : ℝ)) * ((cD + 1) * (weight A : ℝ) ^ (1 + δ))
      + ∑ u : Fin A.N, (if (cluster S A ((ord A.N A.G).order) u).Nonempty
          then dcostAux S ord c fuel (j + 1)
            (childArena S A ((ord A.N A.G).order) u) else 0) := by
  rw [dcostAux, if_neg hbot]
  have hNW : ((A.N : ℕ) : ℝ) ≤ (weight A : ℝ) := by
    have h : A.N ≤ weight A := Nat.le_add_right _ _
    exact_mod_cast h
  have hsteps' : (ord A.N A.G).steps ≤ f * (weight A : ℝ) ^ (1 + 2 * δ) := by
    refine hsteps.trans (mul_le_mul_of_nonneg_left ?_ hf)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNW (by positivity)
  have hsplit : ∀ u : Fin A.N,
      (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
        (c * (nodeCharge S j : ℝ)) *
            (weight (childArena S A ((ord A.N A.G).order) u) : ℝ)
          + dcostAux S ord c fuel (j + 1)
              (childArena S A ((ord A.N A.G).order) u)
      else 0)
      = (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
          (c * (nodeCharge S j : ℝ)) *
            (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) else 0)
        + (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
            dcostAux S ord c fuel (j + 1)
              (childArena S A ((ord A.N A.G).order) u) else 0) := by
    intro u
    split
    · rfl
    · rw [add_zero]
  rw [Finset.sum_congr rfl (fun u _ => hsplit u), Finset.sum_add_distrib]
  have hcharge : ∑ u : Fin A.N,
      (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
        (c * (nodeCharge S j : ℝ)) *
          (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) else 0)
      ≤ (c * (nodeCharge S j : ℝ)) * ((cD + 1) * (weight A : ℝ) ^ (1 + δ)) := by
    have hck : 0 ≤ c * (nodeCharge S j : ℝ) :=
      mul_nonneg hc (Nat.cast_nonneg _)
    have hfactor : ∀ u : Fin A.N,
        (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
          (c * (nodeCharge S j : ℝ)) *
            (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) else 0)
        = (c * (nodeCharge S j : ℝ)) *
          (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
            (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) else 0) := by
      intro u
      split
      · rfl
      · rw [mul_zero]
    rw [Finset.sum_congr rfl (fun u _ => hfactor u), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_child_weight_le S A _ hcD hδ hW hdeg) hck
  have hrec : ∑ u : Fin A.N,
      (if (cluster S A ((ord A.N A.G).order) u).Nonempty then
        dcostAux S ord c fuel (j + 1)
          (childArena S A ((ord A.N A.G).order) u) else 0)
      ≤ ∑ u : Fin A.N, (if (cluster S A ((ord A.N A.G).order) u).Nonempty
          then dcostAux S ord c fuel (j + 1)
            (childArena S A ((ord A.N A.G).order) u) else 0) := le_rfl
  linarith [hsteps', hcharge]

/-! ### The remainder, named, and the headline it yields -/

/-- **The one honest `Prop` between `dcost_node_le` and §7's headline**
(module docstring, item 3): a size-indexed majorant of the arena-indexed
cost, satisfying the landed Rev-5 recurrence. Its discharge is a
mechanical follow-up consuming `dcost_node_le` and the landed
arithmetic; it hides no constant and no exponent. -/
def CostMajorant (S : Setup L) (ord : CoverSpec.OrderingRoutine) (n₀ : ℕ)
    (c a ccost cD δ : ℝ) (T : ℕ → ℕ → ℝ) : Prop :=
  Lax3Proofs.CostRecurrence.IsCostRecurrence a ccost cD δ S.depth T ∧
    ∀ (j : ℕ) (A : Arena (S.pal j) n₀), dcost S ord c j A ≤ T j (weight A)

/-- **§7's headline for the driver, conditional on the majorant**: the
driver's cost at the root is `K^(ℓ+1) · ‖A₀‖^(1+ε)` with §3's chosen
`K = c_D + 1 + (a + c·(c_D+1))` — zero side conditions on `K`
(`CostRecurrence.cost_root_le_chosenK`), `δ = ε/(ℓ+2)`. -/
theorem dcost_root_le_of_majorant {S : Setup L}
    {ord : CoverSpec.OrderingRoutine} {n : ℕ} {c a ccost cD ε : ℝ}
    {T : ℕ → ℕ → ℝ}
    (ha : 0 ≤ a) (hcD : 0 ≤ cD) (hccD : cD ≤ ccost) (hε : 0 ≤ ε)
    (h : CostMajorant S ord n c a ccost cD (ε / ((S.depth : ℝ) + 2)) T)
    (G : SimpleGraph (Fin n)) (col : Coloring n L)
    (hn : 1 ≤ weight (rootArena (L := L) G col)) :
    dcost S ord c 0 (rootArena G col) ≤
      (cD + 1 + (a + ccost * (cD + 1))) ^ (S.depth + 1) *
        (weight (rootArena (L := L) G col) : ℝ) ^ (1 + ε) :=
  (h.2 0 (rootArena G col)).trans
    (Lax3Proofs.CostRecurrence.cost_root_le_chosenK ha hcD hccD hε h.1 hn)

end Lax3Proofs.Driver
