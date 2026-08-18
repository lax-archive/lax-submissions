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

3. **The recurrence, closed** (`dcostAux_le`, `dcost_root_le`) —
   `CostRecurrence.IsCostRecurrence` is size-indexed while `dcost` is
   arena-indexed (the channel `hist` makes the arena type infinite, so
   no sup over same-weight arenas is available); instead of bridging
   through a size-indexed majorant, the downward induction of
   `cost_le_of_isCostRecurrence` is run *directly over the driver's own
   recursion tree*, with the `node` step discharged at every node by
   `dcost_node_le`. The per-node hypotheses — the routine's time and
   degree bounds — are available everywhere because every node's graph
   is a **subgraph copy** (`⊑`) of the root's
   (`childArena_isContained` + transitivity), which is exactly the
   quantification `CoverSpec.IsCoverOrdering` carries. The step
   constant is §3's chosen `K` (`KD`, via
   `CostRecurrence.chosenK_step` — no side condition), and the root
   corollary at `δ = ε/(ℓ+2)` is
   `dcost_root_le : dcost ≤ K^(ℓ+1) · ‖A₀‖^(1+ε)` — §7's headline for
   the driver, **modulo only the cover routine's two bounds**, the
   design's one intended unproved import.
-/

namespace Lax3Proofs.Driver

open scoped SimpleGraph
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

/-! ### Closing the recurrence: the driver's cost bound

The size-vs-arena mismatch of `IsCostRecurrence` is bypassed by running
the downward induction directly over the driver's recursion: the per-node
hypotheses — the routine's time and degree bounds — are available at
*every* node because every node's graph is a subgraph copy (`⊑`) of the
root's: the child embeds in its node through the cluster inclusion
(`childArena_isContained`) and `⊑` is transitive. This is exactly the
quantification `CoverSpec.IsCoverOrdering` carries (`∀ G ⊑ Gn`), so
nothing beyond the design's one unproved import is consumed. -/

/-- The child arena's graph is a subgraph copy of its node's: the
cluster inclusion is injective and edge-preserving (isolation and
restriction only remove edges). -/
theorem childArena_isContained (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    (childArena S A π u).G ⊑ A.G :=
  ⟨⟨⟨fun a => ((childEquiv S A π u) a : Fin A.N), fun hab => hab.1⟩,
    fun _ _ hab => (childEquiv S A π u).injective (Subtype.ext hab)⟩⟩

/-- A child with a nonempty cluster is a nonempty structure. -/
theorem one_le_weight_child (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {u : Fin A.N} (hu : (cluster S A π u).Nonempty) :
    1 ≤ weight (childArena S A π u) := by
  have h : 0 < (cluster S A π u).ncard := (Set.ncard_pos (Set.toFinite _)).mpr hu
  calc 1 ≤ childN S A π u := h
    _ ≤ weight (childArena S A π u) := Nat.le_add_right _ _

/-- A child weighs no more than its node. -/
theorem weight_child_le (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    weight (childArena S A π u) ≤ weight A :=
  (weight_childArena_le S A π u).trans
    (Lax3Proofs.CostRecurrence.clusterWeight_le_graphWeight A.G _)

/-- The cluster fibre of a vertex IS its wreach set — the shape the
cover routine's degree bound is stated in. -/
theorem cluster_fibre_eq (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (v : Fin A.N) :
    {u : Fin A.N | v ∈ cluster S A π u} = wreach A.G π (2 * S.R) v :=
  rfl

/-- A depth-uniform bound on the per-child charge multipliers, over the
run's depths — a constant of the schedule. -/
noncomputable def chargeBound (S : Setup L) : ℕ :=
  (Finset.range (S.depth + 1)).sup (fun j => nodeCharge S j) + 1

theorem one_le_chargeBound (S : Setup L) : 1 ≤ chargeBound S :=
  Nat.le_add_left 1 _

theorem nodeCharge_le_chargeBound (S : Setup L) {j : ℕ} (hj : j ≤ S.depth) :
    nodeCharge S j ≤ chargeBound S :=
  (Finset.le_sup (Finset.mem_range.mpr (by omega))).trans (Nat.le_succ _)

/-- **§3's `K`, for the driver**: `K = c_D + 1 + (a + c·(c_D+1))` with
`a := f` (the cover's time constant) and the children's constant
`c · chargeBound` — chosen, not constrained
(`CostRecurrence.chosenK_step`). -/
noncomputable def KD (S : Setup L) (c cD f : ℝ) : ℝ :=
  cD + 1 + (f + c * (chargeBound S : ℝ) * (cD + 1))

/-- **The driver's cost solves §7's recurrence.** Downward induction on
the fuel over the driver's own recursion tree: under the cover routine's
time and degree bounds — quantified over subgraph copies of `Gn`,
exactly `IsCoverOrdering`'s shape — every node's cost is at most
`K^(fuel+1) · ‖A‖^(1+(fuel+2)δ)`. This is
`CostRecurrence.cost_le_of_isCostRecurrence`'s induction with the
`node` step discharged by `dcost_node_le` at each node; the subgraph
hypothesis descends by `childArena_isContained` and transitivity. -/
theorem dcostAux_le (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {c cD f δ : ℝ} {nn : ℕ} {Gn : SimpleGraph (Fin nn)}
    (hcD : 0 ≤ cD) (hcDc : cD ≤ c) (hf : 0 ≤ f) (hδ : 0 ≤ δ)
    (htime : ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
      (ord m G).steps ≤ f * (m : ℝ) ^ (1 + 2 * δ))
    (hdeg : ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
      ∀ v : Fin m, (wreach G (ord m G).order (2 * S.R) v).ncard ≤
        ⌈cD * (m : ℝ) ^ δ⌉₊) :
    ∀ (fuel j : ℕ), j + fuel ≤ S.depth → ∀ (A : Arena (S.pal j) n₀),
      A.G ⊑ Gn → 1 ≤ weight A →
      dcostAux S ord c fuel j A ≤
        KD S c cD f ^ (fuel + 1) * (weight A : ℝ) ^ (1 + ((fuel : ℝ) + 2) * δ) := by
  classical
  have hc : 0 ≤ c := hcD.trans hcDc
  have hcb1 : (1 : ℝ) ≤ (chargeBound S : ℝ) := by
    exact_mod_cast one_le_chargeBound S
  have hccb : 0 ≤ c * (chargeBound S : ℝ) := mul_nonneg hc (by linarith)
  have hcDcb : cD ≤ c * (chargeBound S : ℝ) :=
    hcDc.trans (le_mul_of_one_le_right hc hcb1)
  have hK1 : (1 : ℝ) ≤ KD S c cD f := by
    unfold KD
    nlinarith
  have hKnn : (0 : ℝ) ≤ KD S c cD f := by linarith
  have hcK : c ≤ KD S c cD f := by
    unfold KD
    nlinarith
  -- the leaf charge fits under every level's bound
  have hleaf : ∀ (W : ℕ), 1 ≤ W → ∀ (k : ℕ) (e : ℝ), 0 ≤ e →
      c * (W : ℝ) ≤ KD S c cD f ^ (k + 1) * (W : ℝ) ^ (1 + e) := by
    intro W hW k e he
    have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    have hpow : (W : ℝ) ≤ (W : ℝ) ^ (1 + e) := by
      have h := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith : (1 : ℝ) ≤ 1 + e)
      rwa [Real.rpow_one] at h
    have hKk : KD S c cD f ≤ KD S c cD f ^ (k + 1) :=
      le_self_pow₀ hK1 (Nat.succ_ne_zero k)
    calc c * (W : ℝ) ≤ KD S c cD f * (W : ℝ) ^ (1 + e) :=
          mul_le_mul hcK hpow (Nat.cast_nonneg W) hKnn
      _ ≤ KD S c cD f ^ (k + 1) * (W : ℝ) ^ (1 + e) :=
          mul_le_mul_of_nonneg_right hKk (Real.rpow_nonneg (Nat.cast_nonneg W) _)
  intro fuel
  induction fuel with
  | zero =>
    intro j hj A hcopy hW
    exact hleaf (weight A) hW 0 _ (by positivity)
  | succ fuel ih =>
    intro j hj A hcopy hW
    by_cases hbot : A.G = ⊥
    · rw [dcostAux, if_pos hbot]
      exact hleaf (weight A) hW (fuel + 1) _ (by positivity)
    · have hdeg' : ∀ v : Fin A.N,
          {u : Fin A.N | v ∈ cluster S A ((ord A.N A.G).order) u}.ncard ≤
            ⌈cD * (A.N : ℝ) ^ δ⌉₊ := by
        intro v
        rw [cluster_fibre_eq]
        exact hdeg A.N A.G hcopy v
      refine (dcost_node_le S ord hc hf hcD hδ A hbot hW
        (htime A.N A.G hcopy) hdeg').trans ?_
      set W : ℝ := (weight A : ℝ) with hWdef
      have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast hW
      have hWpos : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW1
      set K := KD S c cD f with hKdef
      have hKL : (0 : ℝ) ≤ K ^ (fuel + 1) := pow_nonneg hKnn _
      have hE : (0 : ℝ) ≤ W ^ (((fuel : ℝ) + 2) * δ) := Real.rpow_nonneg hWpos.le _
      -- each child's recursive charge, through the induction hypothesis
      have hterm : ∀ u : Fin A.N,
          (if (cluster S A ((ord A.N A.G).order) u).Nonempty
            then dcostAux S ord c fuel (j + 1)
              (childArena S A ((ord A.N A.G).order) u) else 0)
          ≤ (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * δ)) *
            (if (cluster S A ((ord A.N A.G).order) u).Nonempty
              then (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) else 0) := by
        intro u
        by_cases hne : (cluster S A ((ord A.N A.G).order) u).Nonempty
        · rw [if_pos hne, if_pos hne]
          have hWu := one_le_weight_child S A ((ord A.N A.G).order) hne
          have hIH := ih (j + 1) (by omega)
            (childArena S A ((ord A.N A.G).order) u)
            ((childArena_isContained S A ((ord A.N A.G).order) u).trans hcopy)
            hWu
          have hWu1 : (1 : ℝ) ≤
              (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) := by
            exact_mod_cast hWu
          have hWupos : (0 : ℝ) <
              (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) :=
            lt_of_lt_of_le zero_lt_one hWu1
          have hWuW : (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ≤ W := by
            rw [hWdef]
            exact_mod_cast weight_child_le S A ((ord A.N A.G).order) u
          have hsplit : (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
              (1 + ((fuel : ℝ) + 2) * δ)
              = (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) *
                (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
                  (((fuel : ℝ) + 2) * δ) := by
            rw [Real.rpow_add hWupos, Real.rpow_one]
          have hmono : (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
              (((fuel : ℝ) + 2) * δ) ≤ W ^ (((fuel : ℝ) + 2) * δ) :=
            Real.rpow_le_rpow hWupos.le hWuW (by positivity)
          calc dcostAux S ord c fuel (j + 1)
                (childArena S A ((ord A.N A.G).order) u)
              ≤ K ^ (fuel + 1) *
                (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
                  (1 + ((fuel : ℝ) + 2) * δ) := hIH
            _ = K ^ (fuel + 1) *
                ((weight (childArena S A ((ord A.N A.G).order) u) : ℝ) *
                  (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
                    (((fuel : ℝ) + 2) * δ)) := by rw [hsplit]
            _ ≤ K ^ (fuel + 1) *
                ((weight (childArena S A ((ord A.N A.G).order) u) : ℝ) *
                  W ^ (((fuel : ℝ) + 2) * δ)) := by
                refine mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)) hKL
            _ = (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * δ)) *
                (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) := by ring
        · rw [if_neg hne, if_neg hne, mul_zero]
      -- the recursive column, against the mass clause
      have hrec : ∑ u : Fin A.N,
          (if (cluster S A ((ord A.N A.G).order) u).Nonempty
            then dcostAux S ord c fuel (j + 1)
              (childArena S A ((ord A.N A.G).order) u) else 0)
          ≤ (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * δ)) *
            ((cD + 1) * W ^ (1 + δ)) := by
        calc ∑ u : Fin A.N,
            (if (cluster S A ((ord A.N A.G).order) u).Nonempty
              then dcostAux S ord c fuel (j + 1)
                (childArena S A ((ord A.N A.G).order) u) else 0)
            ≤ ∑ u : Fin A.N,
              (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * δ)) *
                (if (cluster S A ((ord A.N A.G).order) u).Nonempty
                  then (weight (childArena S A ((ord A.N A.G).order) u) : ℝ)
                  else 0) := Finset.sum_le_sum fun u _ => hterm u
          _ = (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * δ)) *
              ∑ u : Fin A.N,
                (if (cluster S A ((ord A.N A.G).order) u).Nonempty
                  then (weight (childArena S A ((ord A.N A.G).order) u) : ℝ)
                  else 0) := by rw [Finset.mul_sum]
          _ ≤ (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * δ)) *
              ((cD + 1) * W ^ (1 + δ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKL hE)
              exact sum_child_weight_le S A ((ord A.N A.G).order) hcD hδ hW hdeg'
      -- the three charges, each at the target exponent
      have hEsplit : W ^ (((fuel : ℝ) + 2) * δ) * W ^ (1 + δ)
          = W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) := by
        rw [← Real.rpow_add hWpos]
        congr 1
        ring
      have hEa : W ^ (1 + 2 * δ) ≤ W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) :=
        Real.rpow_le_rpow_of_exponent_le hW1
          (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) fuel) hδ])
      have hEc : W ^ (1 + δ) ≤ W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) :=
        Real.rpow_le_rpow_of_exponent_le hW1
          (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) fuel) hδ])
      have hNE : (0 : ℝ) ≤ W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) :=
        Real.rpow_nonneg hWpos.le _
      have hchargej : (nodeCharge S j : ℝ) ≤ (chargeBound S : ℝ) := by
        exact_mod_cast nodeCharge_le_chargeBound S (by omega)
      have h1 : f * W ^ (1 + 2 * δ) ≤ f * W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) :=
        mul_le_mul_of_nonneg_left hEa hf
      have h2 : (c * (nodeCharge S j : ℝ)) * ((cD + 1) * W ^ (1 + δ))
          ≤ c * (chargeBound S : ℝ) * (cD + 1) *
            W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) := by
        have hle : (c * (nodeCharge S j : ℝ)) * (cD + 1)
            ≤ c * (chargeBound S : ℝ) * (cD + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          exact mul_le_mul_of_nonneg_left hchargej hc
        calc (c * (nodeCharge S j : ℝ)) * ((cD + 1) * W ^ (1 + δ))
            = ((c * (nodeCharge S j : ℝ)) * (cD + 1)) * W ^ (1 + δ) := by ring
          _ ≤ (c * (chargeBound S : ℝ) * (cD + 1)) * W ^ (1 + δ) := by
              refine mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hWpos.le _)
          _ ≤ c * (chargeBound S : ℝ) * (cD + 1) *
              W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) := by
              refine mul_le_mul_of_nonneg_left hEc ?_
              positivity
      have h3 : (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * δ)) *
          ((cD + 1) * W ^ (1 + δ))
          = K ^ (fuel + 1) * (cD + 1) * W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) := by
        calc (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * δ)) * ((cD + 1) * W ^ (1 + δ))
            = K ^ (fuel + 1) * (cD + 1) *
              (W ^ (((fuel : ℝ) + 2) * δ) * W ^ (1 + δ)) := by ring
          _ = K ^ (fuel + 1) * (cD + 1) * W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) := by
              rw [hEsplit]
      have hstep := Lax3Proofs.CostRecurrence.chosenK_step
        (a := f) (c := c * (chargeBound S : ℝ)) (cD := cD) hf hcD hcDcb (fuel + 1)
      have hKstep : K ^ (fuel + 1) * (cD + 1) +
          (f + c * (chargeBound S : ℝ) * (cD + 1)) ≤ K ^ (fuel + 1 + 1) := by
        rw [hKdef]
        exact hstep
      have hcast : ((fuel + 1 : ℕ) : ℝ) + 2 = (fuel : ℝ) + 1 + 2 := by push_cast; ring
      rw [hcast]
      calc f * W ^ (1 + 2 * δ)
            + (c * (nodeCharge S j : ℝ)) * ((cD + 1) * W ^ (1 + δ))
            + ∑ u : Fin A.N,
              (if (cluster S A ((ord A.N A.G).order) u).Nonempty
                then dcostAux S ord c fuel (j + 1)
                  (childArena S A ((ord A.N A.G).order) u) else 0)
          ≤ f * W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ)
            + c * (chargeBound S : ℝ) * (cD + 1) *
              W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ)
            + K ^ (fuel + 1) * (cD + 1) * W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) :=
            add_le_add (add_le_add h1 h2) (hrec.trans (le_of_eq h3))
        _ = (K ^ (fuel + 1) * (cD + 1) +
              (f + c * (chargeBound S : ℝ) * (cD + 1))) *
            W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) := by ring
        _ ≤ K ^ (fuel + 1 + 1) * W ^ (1 + ((fuel : ℝ) + 1 + 2) * δ) :=
            mul_le_mul_of_nonneg_right hKstep hNE

/-- **§7's headline for the driver, closed** — modulo only the cover
routine's two bounds, in exactly `IsCoverOrdering`'s quantification: at
`δ = ε/(ℓ+2)`, the driver's cost at the root is
`K^(ℓ+1) · ‖A₀‖^(1+ε)` with the chosen `K = KD`. -/
theorem dcost_root_le (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {c cD f ε : ℝ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (hcD : 0 ≤ cD) (hcDc : cD ≤ c) (hf : 0 ≤ f) (hε : 0 ≤ ε)
    (htime : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
      (ord m H).steps ≤ f * (m : ℝ) ^ (1 + 2 * (ε / ((S.depth : ℝ) + 2))))
    (hdeg : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
      ∀ v : Fin m, (wreach H (ord m H).order (2 * S.R) v).ncard ≤
        ⌈cD * (m : ℝ) ^ (ε / ((S.depth : ℝ) + 2))⌉₊)
    (col : Coloring n L) (hW : 1 ≤ weight (rootArena (L := L) G col)) :
    dcost S ord c 0 (rootArena G col) ≤
      KD S c cD f ^ (S.depth + 1) *
        (weight (rootArena (L := L) G col) : ℝ) ^ (1 + ε) := by
  have hδ : 0 ≤ ε / ((S.depth : ℝ) + 2) := by positivity
  have hcopy : (rootArena (L := L) G col).G ⊑ G := ⟨SimpleGraph.Copy.id G⟩
  have h := dcostAux_le S ord hcD hcDc hf hδ htime hdeg S.depth 0 (by omega)
    (rootArena G col) hcopy hW
  rw [dcost, Nat.sub_zero]
  have hexp : 1 + ((S.depth : ℝ) + 2) * (ε / ((S.depth : ℝ) + 2)) = 1 + ε := by
    have h2 : ((S.depth : ℝ) + 2) ≠ 0 := by positivity
    field_simp
  rwa [hexp] at h

end Lax3Proofs.Driver
