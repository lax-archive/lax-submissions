import Lax3Proofs.SolveF7Adm

/-!
# F7-b — `KsChargeBridge`, discharged at the pinned `KB`

`SolveChain` §7 leaves the ledger bridge as a named obligation: the
solve budget `Ks` of `solveSpec_closed_scr` is dominated, input by
input, by a constant multiple of the charge ledger's total.  `SolveF7Adm`
pinned the two parameters it compares against (`chainAdm`, `chainKB`).
This file closes the comparison.

## What is proved

`b7_KsChargeBridge` — `SolveChain.KsChargeBridge` at

    Ks x = matK x + (Krl x + (chainKB S ord Kq ℓp hbf Kcov Kglue S.depth 0
             (rootArena G (Impl.trivialColoring n)) + (Kc + topEvalCost S av)))

with `S := Headline.headlineSetup C hC φ`, and the constant `cB`
exhibited (`b7Cb`).  The whole comparison rests on one node→root
induction (`b7_chainKB_le`) and one subtree bound below the edgeless
nodes (`b7_chainKB_bot`).

## The two pieces of real work the audit named

**(1) The `⊥`-node excess.**  `ProgCharge.frameChargeMS` pays `botC` at
an edgeless node and **stops recursing**; `chainKB` cannot stop, because
`frameStepAll_of_cover_prep_read`'s `hKB` holds the recursive slot
structurally at every arena.  So `chargeTotal (covC j A) ≤ chargeTotal
(mcChargeMS …)` is false as a blanket statement and the excess has to be
paid out of `botC` itself.  `b7_chainKB_bot` does exactly that: by
`SolveF7Adm` §10 the subtree below an edgeless node of carrier `N` is
`N` chains of one-vertex edgeless arenas, and the per-level budgets on
such a chain are schedule constants (`b7EdgeC`), so

    chainKB k j A ≤ (M₀ + k·(D + B'))·A.N + B'     (A.G = ⊥),

**linear in `A.N` with a `k`-linear coefficient** — not `2^k`, because
the branching stops at carrier one.  Against `chargeTotal (botC S j A)
= (1+|ℱ_j|)·‖A‖ ≥ A.N` and `k ≤ S.depth` this is a constant multiple of
the node's own ledger entry.  The bound needs `Kcov j A` and
`Kglue k j A` to be `O(A.N+1)` on edgeless arenas; both are abstract
parameters of `chainKB`, so those are hypotheses (`b7KcovBot`,
`b7Kglue`), named and not buried.

**(2) The scatter slack.**  At `σ.t = 0` the ledger's
`Impl.greedyScatterCost` is `0` while `scatterK N ns r 0 = 41N + 24`.
`b7_scatterK_le_greedy` proves the only form that can hold,

    scatterK N ns r t ≤ 130·(t+1)·(r+1)·(greedyScatterCost … + N + ns + 1),

and `b7_centreScatterK_le` charges the `N + ns + 1` residue at the node,
against the *supports* column (whose total is `≥ 2‖B₀ᵤ‖`), which is a
cluster-mass figure the ledger already sums — no new currency, nothing
quadratic in the carrier.

## The columns

Per centre (`b7_centre_le`), at `hbf j = 2·S.R+1`:

| machine | ledger column | constant |
|---|---|---|
| `restrictK` | `restrictC` | `132` (`restrictK_le_childCharge`) |
| `bfsK` + `supportsK` | `supportsC` | `69(2R+1) + 35(2R+2)` |
| `profilesK` | `profilesCMS` | `600(R+1)` (two-term match) |
| `isolateK` | `isolateC` | `33` (`isolateK_le_isolateCharge`, seam `rfl`) |
| `centreScatterK` | `supportsC` | `b7ScatC S j`, a schedule constant |

and at the node the `4`, `botComK`, `Kcov`, `Kglue` go against `botC` /
`covC` / `allocC` / `readC`.  Every level-dependent constant is a
`Finset.sup` over `j ≤ S.depth` (`b7Sup`) — the recursion's diagonal
`j + k` is invariant, so no level above the leaf is ever reached.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun
open Lax13Proofs.Refine (ACost)

variable {L n₀ : ℕ}

/-! ## §1 Two arithmetic helpers -/

/-- The supremum of a level-indexed constant over the levels the chain
can reach.  The recursion `(k+1, j) → (k, j+1)` keeps `j + k` fixed, so
from the root `(S.depth, 0)` every level visited satisfies
`j ≤ S.depth`. -/
def b7Sup (f : ℕ → ℕ) (d : ℕ) : ℕ := (Finset.range (d + 1)).sup f

theorem b7_le_sup (f : ℕ → ℕ) {d j : ℕ} (h : j ≤ d) : f j ≤ b7Sup f d :=
  Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))

/-- Pulling a constant factor out of a list sum. -/
theorem b7_sum_map_mul {α : Type*} (l : List α) (f : α → ℕ) (X : ℕ) :
    (l.map fun a => f a * X).sum = (l.map f).sum * X := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

/-! ## §2 The per-centre columns

Each machine stage budget of `centreK`/`centreScatterK` against the
ledger column `centreChargeMS` charges it at.  Every constant here is
`S.R`-, `S.width`- or schedule-determined; none carries a carrier
figure. -/

section Columns

variable (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
  (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)

open Classical in
/-- `B₀ᵤ`'s degree sum is twice its edge count — the seam between the
machine's slot count `ns` and the ledger's `gsize`. -/
theorem b7_deg_preG :
    (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
      = 2 * (preG S A π u).edgeFinset.card :=
  SimpleGraph.sum_degrees_eq_twice_card_edges _

open Classical in
/-- **The supports column carries the machine's `(N + ns + 1)`**: the
ledger's `"frame.supports"` entry at a centre is at least the child's
carrier plus its slot count plus one.  This is the home for every
machine budget whose envelope is `O(N + ns + 1)` — the BFS, the support
materialization and (via `b7_centreScatterK_le`) the scatter calls. -/
theorem b7_supports_ge :
    childN S A π u + (∑ v : Fin (childN S A π u), (preG S A π u).degree v) + 1
      ≤ chargeTotal (supportsC S j A π u) := by
  rw [chargeTotal_supportsC, b7_deg_preG]
  simp only [Impl.gsize]
  omega

open Classical in
/-- The shared BFS and the support materialization, together, against
the supports column. -/
theorem b7_bfs_supports_le :
    bfsK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
      + supportsK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
      ≤ (69 * (2 * S.R + 1) + 35 * (2 * S.R + 2))
          * chargeTotal (supportsC S j A π u) := by
  have hs := b7_supports_ge S j A π u
  have h1 := bfsK_le (childN S A π u)
    (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
  have h2 := supportsK_le (childN S A π u)
    (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
  have h1' : bfsK (childN S A π u)
      (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
      ≤ 69 * (2 * S.R + 1) * chargeTotal (supportsC S j A π u) :=
    h1.trans (Nat.mul_le_mul_left _ hs)
  have h2' : supportsK (childN S A π u)
      (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
      ≤ 35 * (2 * S.R + 2) * chargeTotal (supportsC S j A π u) :=
    h2.trans (Nat.mul_le_mul_left _ hs)
  calc _ ≤ 69 * (2 * S.R + 1) * chargeTotal (supportsC S j A π u)
            + 35 * (2 * S.R + 2) * chargeTotal (supportsC S j A π u) :=
        Nat.add_le_add h1' h2'
    _ = _ := (Nat.add_mul _ _ _).symm

open Classical in
/-- **The profiles column, the exact two-term match**: one call of the
ledger — batch or virtual-source — is already `≥ N + ns + 1`, so the
machine's `(mb + L)` calls at `600(R+1)(N+ns+1)` fit inside the
ledger's `mb·callCost + L·callCostMS` at the constant `600(R+1)`. -/
theorem b7_profiles_le :
    profilesK S.width (relPal (S.pal j)) (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) S.R
      ≤ 600 * (S.R + 1) * chargeTotal (profilesCMS S j A π u) := by
  rw [chargeTotal_profilesCMS]
  set N := childN S A π u with hN
  set ns := ∑ v : Fin (childN S A π u), (preG S A π u).degree v with hns
  have hdeg : ns = 2 * (preG S A π u).edgeFinset.card := b7_deg_preG S j A π u
  have hg : N + ns + 1 ≤ 2 * Impl.gsize (preG S A π u) + 2 := by
    simp only [Impl.gsize]
    omega
  -- one call of either kind dominates `N + ns + 1`
  have hcall : N + ns + 1 ≤ Impl.callCost (preG S A π u) S.R := by
    refine hg.trans ?_
    simp only [Impl.callCost]
    exact le_trans (by omega) (Nat.le_add_right _ ((S.R + 1) * N))
  have hcallMS : N + ns + 1 ≤ Impl.callCostMS (preG S A π u) S.R := by
    refine hg.trans ?_
    simp only [Impl.callCostMS]
    exact le_trans (by omega) (Nat.le_add_right _ ((S.R + 1) * N))
  have hlow : (S.width + relPal (S.pal j)) * (N + ns + 1)
      ≤ Impl.profilesChargeMS (preG S A π u) S.width (relPal (S.pal j)) S.R := by
    rw [Impl.profilesChargeMS, Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hcall)
      (Nat.mul_le_mul_left _ hcallMS)
  calc profilesK S.width (relPal (S.pal j)) N ns S.R
      ≤ (S.width + relPal (S.pal j)) * (600 * (S.R + 1) * (N + ns + 1)) :=
        profilesK_le _ _ _ _ _
    _ = 600 * (S.R + 1) * ((S.width + relPal (S.pal j)) * (N + ns + 1)) := by ring
    _ ≤ 600 * (S.R + 1)
          * Impl.profilesChargeMS (preG S A π u) S.width (relPal (S.pal j)) S.R :=
        Nat.mul_le_mul_left _ hlow

open Classical in
/-- **The isolate column**: the seam `((ofArena A htab).restrict X_u).N
= childN_u` and `Σ_v (…).G.degree v = Σ_v (preG_u).degree v` is
definitional (`Impl.restrict_N_eq_childN`, `Impl.restrict_G_eq_preG`
are both `rfl`), so `isolateK_le_isolateCharge` applies on the nose. -/
theorem b7_isolate_le {ℓpj : ℕ} (htab : Fin A.N → Fin ℓpj → List (Fin A.N)) :
    isolateK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
      ≤ 33 * (chargeTotal (isolateC S j A htab π u) + 1) := by
  rw [chargeTotal_isolateC]
  exact isolateK_le_isolateCharge ((Impl.ofArena A htab).restrict (cluster S A π u))

open Classical in
/-- **The restrict column**, exact at the channel bound `hb = 2R+1`
(`restrictK_le_childCharge`): the machine's row scans are priced at the
*parent* degrees, exactly as `Impl.childCharge` is. -/
theorem b7_restrict_le (ℓpj : ℕ) :
    restrictK (Impl.degSum A.G (cluster S A π u)) (childN S A π u) (S.pal j) ℓpj
        (2 * S.R + 1)
      ≤ 132 * (chargeTotal (restrictC S j A ℓpj π u) + 1) := by
  rw [chargeTotal_restrictC]
  exact restrictK_le_childCharge A.G (S.pal j) ℓpj S.R (cluster S A π u)

end Columns

/-! ## §3 The scatter slack (audit item (2))

The ledger's `Impl.greedyScatterCost` is **`0`** at `σ.t = 0` (that is
what the `t = 0` guard buys, `Impl.greedyScatterCost_zero`) while the
machine still pays `scatterK N ns r 0 = 41·N + 24` for the mark
region's cleanup and the scan unit.  A bound of the shape
`scatterK ≤ c · greedyScatterCost` is therefore **false**, and the only
form that can hold is the one below: the residue is linear in the
child's own dimensions, chargeable at the same node. -/

/-- **The per-atom form**: one guarded scatter call of the machine costs
at most a schedule constant times the ledger's own charge for that call
plus the child's carrier and slot count.  `c := 130·(t+1)·(r+1)` is a
schedule constant — `r` and `t` are fields of a scatter atom, fixed
before any input is read. -/
theorem b7_scatterK_le_greedy {m : ℕ} (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj] (X : Set (Fin m)) [DecidablePred (· ∈ X)]
    (N ns r t W : ℕ) :
    scatterK N ns r t
      ≤ 130 * ((t + 1) * (r + 1))
          * (Impl.greedyScatterCost H r X W t + N + ns + 1) := by
  refine (scatterK_le N ns r t).trans ?_
  have h : 130 * ((t + 1) * ((r + 1) * (N + ns + 1)))
      = 130 * ((t + 1) * (r + 1)) * (N + ns + 1) := by ring
  rw [h]
  exact Nat.mul_le_mul_left _ (by omega)

/-! ## §4 The scatter column at the node

The `N + ns + 1` residue of §3 goes against the **supports** column,
whose total is `≥ 2‖B₀ᵤ‖` (`b7_supports_ge`) — a cluster-mass figure the
ledger already sums per node through `sum_clusterWeight_le_rpow`.  No
new currency appears, and nothing is quadratic in the carrier. -/

open Classical in
/-- The schedule constant of the level's scatter calls: one
`130·(t+1)·(r+1)` per atom of every decomposition at depth `j`. -/
noncomputable def b7ScatC (S : Setup L) (j : ℕ) : ℕ :=
  ((F S j).map fun β =>
    ((scatterAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)).map
      fun σa => 130 * ((σa.t + 1) * (σa.r + 1))).sum).sum

section Scatter

variable (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
  (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)

open Classical in
/-- Isolation only deletes edges, so the isolated child's slot count is
at most `B₀ᵤ`'s. -/
theorem b7_childArena_deg_le :
    (∑ v : Fin (childN S A π u), (childArena S A π u).G.degree v)
      ≤ ∑ v : Fin (childN S A π u), (preG S A π u).degree v := by
  have hle : (childArena S A π u).G ≤ preG S A π u := by
    intro a b hab
    rw [childArena_G] at hab
    exact hab.1
  exact Finset.sum_le_sum fun v _ => SimpleGraph.degree_le_of_le hle

open Classical in
/-- **The scatter column**, at the node: the whole per-centre scatter
budget is a schedule constant times the child's `(N + ns + 1)`. -/
theorem b7_centreScatterK_le :
    centreScatterK S j A π u
      ≤ b7ScatC S j
          * (childN S A π u
              + (∑ v : Fin (childN S A π u), (preG S A π u).degree v) + 1) := by
  set X := childN S A π u
      + (∑ v : Fin (childN S A π u), (preG S A π u).degree v) + 1 with hX
  have hns : childN S A π u
      + (∑ v : Fin (childN S A π u), (childArena S A π u).G.degree v) + 1 ≤ X := by
    have := b7_childArena_deg_le S j A π u
    omega
  calc centreScatterK S j A π u
      ≤ ((F S j).map fun β =>
          ((scatterAtoms S.choice (stepFml S β.fml)
            (drank_stepFml S β.drank)).map
              fun σa => 130 * ((σa.t + 1) * (σa.r + 1)) * X).sum).sum := by
        refine List.sum_le_sum fun β _ => List.sum_le_sum fun σa _ => ?_
        refine (scatterK_le _ _ _ _).trans ?_
        have h : 130 * ((σa.t + 1) * ((σa.r + 1)
              * (childN S A π u
                + (∑ v : Fin (childN S A π u), (childArena S A π u).G.degree v)
                + 1)))
            = 130 * ((σa.t + 1) * (σa.r + 1))
              * (childN S A π u
                + (∑ v : Fin (childN S A π u), (childArena S A π u).G.degree v)
                + 1) := by ring
        rw [h]
        exact Nat.mul_le_mul_left _ hns
    _ = ((F S j).map fun β =>
          ((scatterAtoms S.choice (stepFml S β.fml)
            (drank_stepFml S β.drank)).map
              fun σa => 130 * ((σa.t + 1) * (σa.r + 1))).sum * X).sum := by
        refine congrArg List.sum (List.map_congr_left fun β _ => ?_)
        exact b7_sum_map_mul _ _ _
    _ = b7ScatC S j * X := by
        rw [b7ScatC]
        exact b7_sum_map_mul _ _ _

end Scatter

/-! ## §5 Below an edgeless node (audit item (1))

`SolveF7Adm` §10: below an edgeless node every cluster is a singleton,
so every child carries one vertex and is itself edgeless.  The per-centre
budget there is therefore a pure schedule constant — `b7EdgeC` — and the
whole subtree below an edgeless node of carrier `N` is `N` chains of
`≤ S.depth` one-vertex arenas. -/

/-- The per-centre budget at an edgeless node: every stage runs at
carrier `1` and slot count `0`.  A constant of the schedule. -/
noncomputable def b7EdgeC (S : Setup L) (ℓp : ℕ → ℕ) (j : ℕ) : ℕ :=
  (restrictK 0 1 (S.pal j) (ℓp j) (2 * S.R + 1)
    + (bfsK 1 0 (2 * S.R)
      + (supportsK 1 0 (2 * S.R)
        + (profilesK S.width (relPal (S.pal j)) 1 0 S.R + (isolateK 1 0 + 0)))))
    + 2 * b7ScatC S j

section Edgeless

variable (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
  (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)

open Classical in
theorem b7_degSum_eq_zero (hbot : A.G = ⊥) :
    Impl.degSum A.G (cluster S A π u) = 0 := by
  refine Finset.sum_eq_zero fun s _ => ?_
  refine Nat.le_zero.mp ?_
  have hsub : A.G.neighborFinset s ⊆ ∅ := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset, hbot] at hw
    exact hw.elim
  simpa using Finset.card_le_card hsub

open Classical in
theorem b7_deg_preG_eq_zero (hbot : A.G = ⊥) :
    (∑ v : Fin (childN S A π u), (preG S A π u).degree v) = 0 := by
  refine Finset.sum_eq_zero fun v _ => ?_
  refine Nat.le_zero.mp ?_
  have hsub : (preG S A π u).neighborFinset v ⊆ ∅ := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset, preG_eq_bot_of_bot S A π u hbot] at hw
    exact hw.elim
  simpa using Finset.card_le_card hsub

open Classical in
theorem b7_deg_childArena_eq_zero (hbot : A.G = ⊥) :
    (∑ v : Fin (childN S A π u), (childArena S A π u).G.degree v) = 0 :=
  Nat.le_zero.mp
    ((b7_childArena_deg_le S j A π u).trans
      (le_of_eq (b7_deg_preG_eq_zero S j A π u hbot)))

open Classical in
/-- **The per-centre budget at an edgeless node is a schedule
constant** — every carrier figure it reads is `1` or `0`. -/
theorem b7_centre_edge_le (ℓp : ℕ → ℕ) (hbot : A.G = ⊥) :
    centreK S A (ℓp j) (2 * S.R + 1) π u 0 + centreScatterK S j A π u
      ≤ b7EdgeC S ℓp j := by
  have hd := b7_degSum_eq_zero S j A π u hbot
  have hp := b7_deg_preG_eq_zero S j A π u hbot
  have hc := b7_deg_childArena_eq_zero S j A π u hbot
  have hN := childN_eq_one_of_bot S A π u hbot
  have hscat : centreScatterK S j A π u ≤ 2 * b7ScatC S j := by
    refine (b7_centreScatterK_le S j A π u).trans ?_
    rw [hp, hN]
    omega
  have hcen : centreK S A (ℓp j) (2 * S.R + 1) π u 0
      = restrictK 0 1 (S.pal j) (ℓp j) (2 * S.R + 1)
        + (bfsK 1 0 (2 * S.R)
          + (supportsK 1 0 (2 * S.R)
            + (profilesK S.width (relPal (S.pal j)) 1 0 S.R
              + (isolateK 1 0 + 0)))) := by
    rw [centreK, hd, hp, hN]
  rw [hcen, b7EdgeC]
  omega

end Edgeless

/-! ### The `⊥`-subtree bound

The two coefficients are kept apart on purpose: the `N`-linear
coefficient grows by one `D + B'` per level of fuel (a chain of
one-vertex arenas costs a constant per level), while the additive term
stays put.  A single-coefficient shape `M·(k+1)·(N+1)` does **not**
close the induction — the child's `+1` doubles it at carrier one. -/

/-- The `N`-coefficient of the `⊥`-subtree bound at fuel `k`. -/
noncomputable def b7BotA (S : Setup L) (ℓp : ℕ → ℕ) (M₀ ccov cglue k : ℕ) : ℕ :=
  M₀ + k * ((M₀ + ccov + cglue + b7Sup (b7EdgeC S ℓp) S.depth)
    + max (4 + M₀ + ccov + cglue) M₀)

/-- The additive term of the `⊥`-subtree bound — level- and
fuel-independent. -/
def b7BotB (M₀ ccov cglue : ℕ) : ℕ := max (4 + M₀ + ccov + cglue) M₀

theorem b7BotA_succ (S : Setup L) (ℓp : ℕ → ℕ) (M₀ ccov cglue k : ℕ) :
    b7BotA S ℓp M₀ ccov cglue (k + 1)
      = b7BotA S ℓp M₀ ccov cglue k
        + ((M₀ + ccov + cglue + b7Sup (b7EdgeC S ℓp) S.depth)
          + b7BotB M₀ ccov cglue) := by
  simp only [b7BotA, b7BotB]
  ring

theorem b7BotA_zero (S : Setup L) (ℓp : ℕ → ℕ) (M₀ ccov cglue : ℕ) :
    b7BotA S ℓp M₀ ccov cglue 0 = M₀ := by
  simp [b7BotA]

theorem b7_le_botB (M₀ ccov cglue : ℕ) : M₀ ≤ b7BotB M₀ ccov cglue :=
  le_max_right _ _

section BotSubtree

variable (S : Setup L) (ord : CoverSpec.OrderingRoutine) (Kq : ℕ) (ℓp hbf : ℕ → ℕ)
  (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
  (Kglue : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ)
  (M₀ ccov cglue : ℕ)

open Classical in
/-- **The `⊥`-subtree bound.** `chainKB` cannot stop at an edgeless node
— `frameStepAll_of_cover_prep_read`'s `hKB` holds the recursive slot
structurally at every arena — but what it spends below one is linear in
that node's carrier, with a coefficient linear in the remaining fuel.
The three hypotheses are exactly what the abstract slots of `chainKB`
have to supply: the leaf block's budget, and the cover and glue budgets
on edgeless arenas. -/
theorem b7_chainKB_bot
    (hhbf : ∀ i, hbf i = 2 * S.R + 1)
    (hbotK : ∀ i : ℕ, i ≤ S.depth → ∀ A : Arena (S.pal i) n₀,
      botComK A.N (S.pal i) Kq (levelFml S i) ≤ M₀ * (A.N + 1))
    (hKcovBot : ∀ (i : ℕ) (A : Arena (S.pal i) n₀), A.G = ⊥ →
      Kcov i A ≤ ccov * (A.N + 1))
    (hKglue : ∀ (k i : ℕ) (A : Arena (S.pal i) n₀),
      Kglue k i A ≤ cglue * (A.N + 1)) :
    ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + k ≤ S.depth → A.G = ⊥ →
      chainKB S ord Kq ℓp hbf Kcov Kglue k j A
        ≤ b7BotA S ℓp M₀ ccov cglue k * A.N + b7BotB M₀ ccov cglue := by
  intro k
  induction k with
  | zero =>
    intro j A hjk _
    rw [chainKB_zero, b7BotA_zero]
    have h := hbotK j (by omega) A
    have e : M₀ * (A.N + 1) = M₀ * A.N + M₀ := by ring
    have hb := b7_le_botB M₀ ccov cglue
    omega
  | succ k ih =>
    intro j A hjk hbot
    rw [chainKB_succ, hhbf, b7BotA_succ]
    set π : Equiv.Perm (Fin A.N) := (ord A.N A.G).order with hπ
    set E : ℕ := b7Sup (b7EdgeC S ℓp) S.depth with hE
    set a : ℕ := b7BotA S ℓp M₀ ccov cglue k with ha
    set b : ℕ := b7BotB M₀ ccov cglue with hb
    -- the per-centre budget below an edgeless node
    have hEj : b7EdgeC S ℓp j ≤ E := b7_le_sup _ (by omega)
    have hper : ∀ u : Fin A.N,
        centreK S A (ℓp j) (2 * S.R + 1) π u
            (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) (childArena S A π u))
          + centreScatterK S j A π u ≤ E + (a * 1 + b) := by
      intro u
      have hch : (childArena S A π u).G = ⊥ := childArena_G_eq_bot_of_bot S A π u hbot
      have hchN : (childArena S A π u).N = 1 := childN_eq_one_of_bot S A π u hbot
      have hrec := ih (j + 1) (childArena S A π u) (by omega) hch
      rw [hchN] at hrec
      have hown := b7_centre_edge_le S j A π u ℓp hbot
      rw [centreK_add_nxK]
      omega
    -- the centre loop
    have hloop : (((List.finRange A.N).map fun u =>
          centreK S A (ℓp j) (2 * S.R + 1) π u
              (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) (childArena S A π u))
            + centreScatterK S j A π u).sum)
        ≤ A.N * (E + (a * 1 + b)) := by
      calc (((List.finRange A.N).map fun u =>
              centreK S A (ℓp j) (2 * S.R + 1) π u
                  (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1)
                    (childArena S A π u))
                + centreScatterK S j A π u).sum)
          ≤ ((List.finRange A.N).map fun _ => E + (a * 1 + b)).sum :=
            List.sum_le_sum fun u _ => hper u
        _ = A.N * (E + (a * 1 + b)) := by
            simp [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]

    have hcov := hKcovBot j A hbot
    have hglue := hKglue k j A
    have hbotc := hbotK j (by omega) A
    have hbB : 4 + M₀ + ccov + cglue ≤ b := le_max_left _ _
    rw [frameElseK]
    -- pure arithmetic in the products, all ring-normalized
    have e1 : M₀ * (A.N + 1) = M₀ * A.N + M₀ := by ring
    have e2 : ccov * (A.N + 1) = ccov * A.N + ccov := by ring
    have e3 : cglue * (A.N + 1) = cglue * A.N + cglue := by ring
    have e4 : A.N * (E + (a * 1 + b)) = E * A.N + a * A.N + b * A.N := by ring
    have e5 : (a + ((M₀ + ccov + cglue + E) + b)) * A.N
        = a * A.N + M₀ * A.N + ccov * A.N + cglue * A.N + E * A.N + b * A.N := by
      ring
    have hmax : max (botComK A.N (S.pal j) Kq (levelFml S j))
        (Kcov j A + ((((List.finRange A.N).map fun u =>
            centreK S A (ℓp j) (2 * S.R + 1) π u
                (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) (childArena S A π u))
              + centreScatterK S j A π u).sum) + Kglue k j A))
        ≤ botComK A.N (S.pal j) Kq (levelFml S j)
          + (Kcov j A + ((((List.finRange A.N).map fun u =>
            centreK S A (ℓp j) (2 * S.R + 1) π u
                (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) (childArena S A π u))
              + centreScatterK S j A π u).sum) + Kglue k j A)) :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega

end BotSubtree

/-! ## §6 The per-centre budget against the per-centre ledger vector -/

/-- The per-centre constant: the five column constants of §2 plus the
level's scatter constant. -/
noncomputable def b7Cen (S : Setup L) (j : ℕ) : ℕ :=
  132 + (69 * (2 * S.R + 1) + 35 * (2 * S.R + 2)) + 600 * (S.R + 1) + 33
    + b7ScatC S j

open Classical in
/-- `centreChargeMS`'s total, kept as its six columns (the expanded form
is `chargeTotal_centreChargeMS`). -/
theorem b7_chargeTotal_centreChargeMS (S : Setup L) (j : ℕ)
    (A : Arena (S.pal j) n₀) (ℓpj : ℕ)
    (htab : Fin A.N → Fin ℓpj → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) →
      Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    chargeTotal (centreChargeMS S j A ℓpj htab nx nxC π u)
      = chargeTotal (restrictC S j A ℓpj π u)
        + (chargeTotal (supportsC S j A π u)
          + (chargeTotal (profilesCMS S j A π u)
            + (chargeTotal (isolateC S j A htab π u)
              + (chargeTotal (nxC (childArena S A π u))
                + scatterCost S j A π u (nx (childArena S A π u)))))) := by
  rw [centreChargeMS, chargeTotal_add, chargeTotal_add, chargeTotal_add,
    chargeTotal_add, chargeTotal_add, chargeTotal_cost (by decide)]

open Classical in
/-- **The per-centre comparison**: at the channel bound `hb = 2R+1`, the
machine's five stage budgets and its scatter calls together fit inside a
schedule constant times the ledger's four own columns for that centre
(the recursion slot and the scatter column are left over). -/
theorem b7_centre_le (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓpj : ℕ} (htab : Fin A.N → Fin ℓpj → List (Fin A.N))
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    centreK S A ℓpj (2 * S.R + 1) π u 0 + centreScatterK S j A π u
      ≤ b7Cen S j
          * (chargeTotal (restrictC S j A ℓpj π u)
            + (chargeTotal (supportsC S j A π u)
              + (chargeTotal (profilesCMS S j A π u)
                + (chargeTotal (isolateC S j A htab π u) + 1)))) := by
  have hr := b7_restrict_le S j A π u ℓpj
  have hbs := b7_bfs_supports_le S j A π u
  have hpr := b7_profiles_le S j A π u
  have hi := b7_isolate_le S j A π u htab
  have hsup := b7_supports_ge S j A π u
  have hsc : centreScatterK S j A π u
      ≤ b7ScatC S j * chargeTotal (supportsC S j A π u) :=
    (b7_centreScatterK_le S j A π u).trans (Nat.mul_le_mul_left _ hsup)
  have hcen : centreK S A ℓpj (2 * S.R + 1) π u 0
      = restrictK (Impl.degSum A.G (cluster S A π u)) (childN S A π u) (S.pal j)
          ℓpj (2 * S.R + 1)
        + (bfsK (childN S A π u)
            (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
          + (supportsK (childN S A π u)
              (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
            + (profilesK S.width (relPal (S.pal j)) (childN S A π u)
                (∑ v : Fin (childN S A π u), (preG S A π u).degree v) S.R
              + (isolateK (childN S A π u)
                  (∑ v : Fin (childN S A π u), (preG S A π u).degree v) + 0)))) :=
    rfl
  rw [hcen]
  set Rc := chargeTotal (restrictC S j A ℓpj π u) with hRc
  set Sc := chargeTotal (supportsC S j A π u) with hSc
  set Pc := chargeTotal (profilesCMS S j A π u) with hPc
  set Ic := chargeTotal (isolateC S j A htab π u) with hIc
  set C := b7Cen S j with hCdef
  have hC : C = 132 + (69 * (2 * S.R + 1) + 35 * (2 * S.R + 2))
      + 600 * (S.R + 1) + 33 + b7ScatC S j := hCdef
  have h1 : 132 * Rc ≤ C * Rc := Nat.mul_le_mul_right _ (by omega)
  have h2 : ((69 * (2 * S.R + 1) + 35 * (2 * S.R + 2)) + b7ScatC S j) * Sc
      ≤ C * Sc := Nat.mul_le_mul_right _ (by omega)
  have h3 : 600 * (S.R + 1) * Pc ≤ C * Pc := Nat.mul_le_mul_right _ (by omega)
  have h4 : 33 * Ic ≤ C * Ic := Nat.mul_le_mul_right _ (by omega)
  have e0 : C * (Rc + (Sc + (Pc + (Ic + 1)))) = C * Rc + C * Sc + C * Pc + C * Ic + C := by
    ring
  have e1 : 132 * (Rc + 1) = 132 * Rc + 132 := by ring
  have e3 : 33 * (Ic + 1) = 33 * Ic + 33 := by ring
  have e2 : ((69 * (2 * S.R + 1) + 35 * (2 * S.R + 2)) + b7ScatC S j) * Sc
      = (69 * (2 * S.R + 1) + 35 * (2 * S.R + 2)) * Sc + b7ScatC S j * Sc := by ring
  omega

/-! ## §7 The node→root induction

The comparison is `chainKB k j A ≤ M · chargeTotal (driverChargeMS …) + M`
— **no carrier term on the right**, which is what makes the step close:
the recursion slot's coefficient stays `M`, and the node's own charge is
paid from the ledger entries the recursion does not use (`allocC`,
`readC`, the four per-centre columns). -/

/-- The constant of the bridge, assembled from the leaf-block, cover,
glue and per-centre constants and the `⊥`-subtree coefficients. -/
noncomputable def b7M (S : Setup L) (ℓp : ℕ → ℕ) (M₀ ccov cglue : ℕ) : ℕ :=
  b7BotA S ℓp M₀ ccov cglue S.depth + b7BotB M₀ ccov cglue
    + b7Sup (b7Cen S) S.depth + M₀ + ccov + cglue + 4

theorem b7BotA_mono (S : Setup L) (ℓp : ℕ → ℕ) (M₀ ccov cglue : ℕ) {k k' : ℕ}
    (h : k ≤ k') :
    b7BotA S ℓp M₀ ccov cglue k ≤ b7BotA S ℓp M₀ ccov cglue k' := by
  simp only [b7BotA]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- `‖A‖ ≥ A.N`: the leaf column's total already carries the carrier. -/
theorem b7_N_le_weight {Λ : ℕ} (A : Arena Λ n₀) : A.N ≤ weight A := by
  simp only [weight, Lax3Proofs.CoverEdgeSum.graphWeight]
  omega

theorem b7_N_le_botTotal (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀) :
    A.N ≤ (1 + (F S j).length) * weight A :=
  (b7_N_le_weight A).trans (Nat.le_mul_of_pos_left _ (by omega))

/-- A per-centre affine sum, folded. -/
theorem b7_sum_map_affine {α : Type*} (l : List α) (f : α → ℕ) (M c : ℕ) :
    (l.map fun a => M * f a + c).sum = M * (l.map f).sum + c * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    ring

section Main

variable (S : Setup L) (ord : CoverSpec.OrderingRoutine) (Kq : ℕ) (ℓp hbf : ℕ → ℕ)
  (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
    Fin A.N → Fin (ℓp j) → List (Fin A.N))
  (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
  (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
  (Kglue : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ)
  (M₀ ccov cglue : ℕ)

open Classical in
theorem b7_driver_zero_total (j : ℕ) (A : Arena (S.pal j) n₀) :
    chargeTotal (driverChargeMS S ord ℓp htabF covC 0 j A)
      = (1 + (F S j).length) * weight A := by
  show chargeTotal (botC S j A) = _
  exact chargeTotal_botC S j A

open Classical in
theorem b7_driver_succ_bot (k j : ℕ) (A : Arena (S.pal j) n₀) (hbot : A.G = ⊥) :
    chargeTotal (driverChargeMS S ord ℓp htabF covC (k + 1) j A)
      = (1 + (F S j).length) * weight A := by
  show chargeTotal (frameChargeMS S ord j A (ℓp j) (htabF j A) _ _ _) = _
  rw [frameChargeMS, if_pos hbot]
  exact chargeTotal_botC S j A

open Classical in
theorem b7_driver_succ_ne_bot (k j : ℕ) (A : Arena (S.pal j) n₀)
    (hbot : ¬ A.G = ⊥) :
    chargeTotal (driverChargeMS S ord ℓp htabF covC (k + 1) j A)
      = chargeTotal (covC j A)
        + (A.N + ((((List.finRange A.N).map fun u =>
            chargeTotal (centreChargeMS S j A (ℓp j) (htabF j A)
              (fun B => Unroll.unrollAux S ord k (j + 1) B)
              (fun B => driverChargeMS S ord ℓp htabF covC k (j + 1) B)
              ((ord A.N A.G).order) u)).sum)
          + A.N * (1 + (F S j).length))) := by
  show chargeTotal (frameChargeMS S ord j A (ℓp j) (htabF j A) _ _ _) = _
  rw [frameChargeMS, if_neg hbot, chargeTotal_add, chargeTotal_add,
    chargeTotal_add, chargeTotal_listSum, List.map_map, chargeTotal_allocC,
    chargeTotal_readC]
  rfl

open Classical in
/-- **The node→root induction.**  Along the chain's own diagonal
(`j + k` invariant, so every level reached is `≤ S.depth`), the pinned
budget is a constant multiple of the ledger vector's total plus one
constant.  The four hypotheses are precisely the abstract slots of
`chainKB`: the channel bound the restrict column is proved at, the leaf
block's budget, and the cover and glue budgets — the last one twice,
once against the ledger's cover column and once, on edgeless arenas,
against the carrier alone, because the ledger has **no** cover column
there. -/
theorem b7_chainKB_le
    (hhbf : ∀ i, hbf i = 2 * S.R + 1)
    (hbotK : ∀ i : ℕ, i ≤ S.depth → ∀ A : Arena (S.pal i) n₀,
      botComK A.N (S.pal i) Kq (levelFml S i) ≤ M₀ * (A.N + 1))
    (hKcov : ∀ (i : ℕ) (A : Arena (S.pal i) n₀),
      Kcov i A ≤ ccov * (chargeTotal (covC i A) + A.N + 1))
    (hKcovBot : ∀ (i : ℕ) (A : Arena (S.pal i) n₀), A.G = ⊥ →
      Kcov i A ≤ ccov * (A.N + 1))
    (hKglue : ∀ (k i : ℕ) (A : Arena (S.pal i) n₀),
      Kglue k i A ≤ cglue * (A.N + 1)) :
    ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + k ≤ S.depth →
      chainKB S ord Kq ℓp hbf Kcov Kglue k j A
        ≤ b7M S ℓp M₀ ccov cglue
            * chargeTotal (driverChargeMS S ord ℓp htabF covC k j A)
          + b7M S ℓp M₀ ccov cglue := by
  set M := b7M S ℓp M₀ ccov cglue with hMdef
  have hM : M = b7BotA S ℓp M₀ ccov cglue S.depth + b7BotB M₀ ccov cglue
      + b7Sup (b7Cen S) S.depth + M₀ + ccov + cglue + 4 := hMdef
  have hMbotA : b7BotA S ℓp M₀ ccov cglue S.depth ≤ M := by omega
  have hMbotB : b7BotB M₀ ccov cglue ≤ M := by omega
  have hMcen : b7Sup (b7Cen S) S.depth ≤ M := by omega
  have hMM0 : M₀ ≤ M := by omega
  have hMcov : ccov ≤ M := by omega
  have hMsum : M₀ + ccov + cglue + b7Sup (b7Cen S) S.depth ≤ M := by omega
  have hM4 : 4 + M₀ + ccov + cglue ≤ M := by omega
  intro k
  induction k with
  | zero =>
    intro j A hjk
    rw [chainKB_zero, b7_driver_zero_total]
    have h := hbotK j (by omega) A
    have hN := b7_N_le_botTotal S j A
    have e : M₀ * (A.N + 1) = M₀ * A.N + M₀ := by ring
    have h2 : M₀ * A.N ≤ M * ((1 + (F S j).length) * weight A) :=
      (Nat.mul_le_mul_left _ hN).trans (Nat.mul_le_mul_right _ hMM0)
    omega
  | succ k ih =>
    intro j A hjk
    by_cases hbot : A.G = ⊥
    · -- the edgeless node: the ledger stops here, `chainKB` does not
      rw [b7_driver_succ_bot S ord ℓp htabF covC k j A hbot]
      have hb := b7_chainKB_bot S ord Kq ℓp hbf Kcov Kglue M₀ ccov cglue
        hhbf hbotK hKcovBot hKglue (k + 1) j A hjk hbot
      have hA : b7BotA S ℓp M₀ ccov cglue (k + 1) ≤ M :=
        (b7BotA_mono S ℓp M₀ ccov cglue (by omega : k + 1 ≤ S.depth)).trans hMbotA
      have hN := b7_N_le_botTotal S j A
      have h2 : b7BotA S ℓp M₀ ccov cglue (k + 1) * A.N
          ≤ M * ((1 + (F S j).length) * weight A) :=
        (Nat.mul_le_mul_left _ hN).trans (Nat.mul_le_mul_right _ hA)
      omega
    · -- the edged node: column by column
      rw [chainKB_succ, hhbf, frameElseK,
        b7_driver_succ_ne_bot S ord ℓp htabF covC k j A hbot]
      set π : Equiv.Perm (Fin A.N) := (ord A.N A.G).order with hπ
      set Cc := b7Sup (b7Cen S) S.depth with hCc
      have hCj : b7Cen S j ≤ Cc := b7_le_sup _ (by omega)
      have hper : ∀ u : Fin A.N,
          centreK S A (ℓp j) (2 * S.R + 1) π u
              (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) (childArena S A π u))
            + centreScatterK S j A π u
          ≤ M * chargeTotal (centreChargeMS S j A (ℓp j) (htabF j A)
                (fun B => Unroll.unrollAux S ord k (j + 1) B)
                (fun B => driverChargeMS S ord ℓp htabF covC k (j + 1) B) π u)
            + (Cc + M) := by
        intro u
        rw [centreK_add_nxK, b7_chargeTotal_centreChargeMS]
        have hown := b7_centre_le S j A (htabF j A) π u
        have hrec := ih (j + 1) (childArena S A π u) (by omega)
        set Rc := chargeTotal (restrictC S j A (ℓp j) π u) with hRc
        set Sc := chargeTotal (supportsC S j A π u) with hSc
        set Pc := chargeTotal (profilesCMS S j A π u) with hPc
        set Ic := chargeTotal (isolateC S j A (htabF j A) π u) with hIc
        set Tc := chargeTotal (driverChargeMS S ord ℓp htabF covC k (j + 1)
          (childArena S A π u)) with hTc
        set Xc := scatterCost S j A π u
          (Unroll.unrollAux S ord k (j + 1) (childArena S A π u)) with hXc
        have h1 : b7Cen S j * (Rc + (Sc + (Pc + (Ic + 1))))
            ≤ Cc * (Rc + (Sc + (Pc + (Ic + 1)))) := Nat.mul_le_mul_right _ hCj
        have e1 : Cc * (Rc + (Sc + (Pc + (Ic + 1))))
            = Cc * Rc + Cc * Sc + Cc * Pc + Cc * Ic + Cc := by ring
        have e2 : M * (Rc + (Sc + (Pc + (Ic + (Tc + Xc)))))
            = M * Rc + M * Sc + M * Pc + M * Ic + M * Tc + M * Xc := by ring
        have m1 : Cc * Rc ≤ M * Rc := Nat.mul_le_mul_right _ hMcen
        have m2 : Cc * Sc ≤ M * Sc := Nat.mul_le_mul_right _ hMcen
        have m3 : Cc * Pc ≤ M * Pc := Nat.mul_le_mul_right _ hMcen
        have m4 : Cc * Ic ≤ M * Ic := Nat.mul_le_mul_right _ hMcen
        omega
      have hloop : (((List.finRange A.N).map fun u =>
            centreK S A (ℓp j) (2 * S.R + 1) π u
                (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) (childArena S A π u))
              + centreScatterK S j A π u).sum)
          ≤ M * (((List.finRange A.N).map fun u =>
              chargeTotal (centreChargeMS S j A (ℓp j) (htabF j A)
                (fun B => Unroll.unrollAux S ord k (j + 1) B)
                (fun B => driverChargeMS S ord ℓp htabF covC k (j + 1) B)
                π u)).sum)
            + (Cc + M) * A.N := by
        calc (((List.finRange A.N).map fun u =>
              centreK S A (ℓp j) (2 * S.R + 1) π u
                  (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1)
                    (childArena S A π u))
                + centreScatterK S j A π u).sum)
            ≤ ((List.finRange A.N).map fun u =>
                M * chargeTotal (centreChargeMS S j A (ℓp j) (htabF j A)
                    (fun B => Unroll.unrollAux S ord k (j + 1) B)
                    (fun B => driverChargeMS S ord ℓp htabF covC k (j + 1) B)
                    π u) + (Cc + M)).sum :=
              List.sum_le_sum fun u _ => hper u
          _ = M * (((List.finRange A.N).map fun u =>
                chargeTotal (centreChargeMS S j A (ℓp j) (htabF j A)
                  (fun B => Unroll.unrollAux S ord k (j + 1) B)
                  (fun B => driverChargeMS S ord ℓp htabF covC k (j + 1) B)
                  π u)).sum) + (Cc + M) * (List.finRange A.N).length :=
              b7_sum_map_affine _ _ _ _
          _ = _ := by rw [List.length_finRange]
      set CS := (((List.finRange A.N).map fun u =>
        chargeTotal (centreChargeMS S j A (ℓp j) (htabF j A)
          (fun B => Unroll.unrollAux S ord k (j + 1) B)
          (fun B => driverChargeMS S ord ℓp htabF covC k (j + 1) B)
          π u)).sum) with hCS
      set cov := chargeTotal (covC j A) with hcov0
      set Fl := (F S j).length with hFl
      have hbotc := hbotK j (by omega) A
      have hcov : Kcov j A ≤ ccov * (cov + A.N + 1) := hKcov j A
      have hglue := hKglue k j A
      have hmax : max (botComK A.N (S.pal j) Kq (levelFml S j))
          (Kcov j A + ((((List.finRange A.N).map fun u =>
              centreK S A (ℓp j) (2 * S.R + 1) π u
                  (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1)
                    (childArena S A π u))
                + centreScatterK S j A π u).sum) + Kglue k j A))
          ≤ botComK A.N (S.pal j) Kq (levelFml S j)
            + (Kcov j A + ((((List.finRange A.N).map fun u =>
              centreK S A (ℓp j) (2 * S.R + 1) π u
                  (chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1)
                    (childArena S A π u))
                + centreScatterK S j A π u).sum) + Kglue k j A)) :=
        max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
      have e1 : M₀ * (A.N + 1) = M₀ * A.N + M₀ := by ring
      have e2 : ccov * (cov + A.N + 1) = ccov * cov + ccov * A.N + ccov := by ring
      have e3 : cglue * (A.N + 1) = cglue * A.N + cglue := by ring
      have e4 : (Cc + M) * A.N = Cc * A.N + M * A.N := by ring
      have e5 : M * (cov + (A.N + (CS + A.N * (1 + Fl))))
          = M * cov + M * A.N + M * CS + M * (A.N * (1 + Fl)) := by ring
      have e6 : (M₀ + ccov + cglue + Cc) * A.N
          = M₀ * A.N + ccov * A.N + cglue * A.N + Cc * A.N := by ring
      have hlin : (M₀ + ccov + cglue + Cc) * A.N ≤ M * A.N :=
        Nat.mul_le_mul_right _ hMsum
      have hcovM : ccov * cov ≤ M * cov := Nat.mul_le_mul_right _ hMcov
      have hNF : A.N ≤ A.N * (1 + Fl) := Nat.le_mul_of_pos_right _ (by omega)
      have hMNF : M * A.N ≤ M * (A.N * (1 + Fl)) := Nat.mul_le_mul_left _ hNF
      omega

end Main

/-! ## §8 The leaf-block constant, discharged

`M₀` is not left as an assumption: `botComK_le` gives it level by level
and `b7Sup` closes the finitely many levels the chain reaches. -/

/-- The leaf block's constant, over the levels the chain reaches. -/
noncomputable def b7BotK (S : Setup L) (Kq : ℕ) : ℕ :=
  b7Sup (fun i => (3 * 2 ^ S.pal i + 11 * S.pal i + 6 * Kq
      + evalKMax (S.pal i) Kq (levelFml S i) + 60)
    * (1 + (levelFml S i).length)) S.depth

theorem b7_botK_le (S : Setup L) (Kq : ℕ) :
    ∀ i : ℕ, i ≤ S.depth → ∀ A : Arena (S.pal i) n₀,
      botComK A.N (S.pal i) Kq (levelFml S i) ≤ b7BotK S Kq * (A.N + 1) := by
  intro i hi A
  refine (botComK_le A.N (S.pal i) Kq (levelFml S i)).trans ?_
  have h := b7_le_sup (fun i => (3 * 2 ^ S.pal i + 11 * S.pal i + 6 * Kq
      + evalKMax (S.pal i) Kq (levelFml S i) + 60)
    * (1 + (levelFml S i).length)) (d := S.depth) hi
  calc (3 * 2 ^ S.pal i + 11 * S.pal i + 6 * Kq
        + evalKMax (S.pal i) Kq (levelFml S i) + 60)
        * ((1 + (levelFml S i).length) * (A.N + 1))
      = ((3 * 2 ^ S.pal i + 11 * S.pal i + 6 * Kq
          + evalKMax (S.pal i) Kq (levelFml S i) + 60)
        * (1 + (levelFml S i).length)) * (A.N + 1) := by ring
    _ ≤ b7BotK S Kq * (A.N + 1) := Nat.mul_le_mul_right _ h

/-! ## §9 `KsChargeBridge`, discharged -/

open Classical in
/-- The root driver's total is part of the root ledger vector's total. -/
theorem b7_driver_le_mc (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L) :
    chargeTotal (driverChargeMS S ord ℓp htabF covC S.depth 0 (rootArena G col))
      ≤ chargeTotal (mcChargeMS S ord ℓp htabF covC G col) := by
  rw [mcChargeMS, chargeTotal_add]
  omega

/-- **The bridge's constant**, exhibited. -/
noncomputable def b7Cb (S : Setup L) (ℓp : ℕ → ℕ) (M₀ ccov cglue crl Kc : ℕ)
    (av : ScatterSentence L → Expr) : ℕ :=
  11 + crl + b7M S ℓp M₀ ccov cglue + 6 + Kc + topEvalCost S av

open Classical in
/-- **`SolveChain.KsChargeBridge`, discharged** at `KB := chainKB`
(`SolveF7Adm`) and the solve budget of `solveSpec_closed_scr`, with
`cB := b7Cb …` exhibited.

The four remaining hypotheses are the abstract slots of `chainKB` and of
`solveSpec_closed_scr` — nothing about the ledger or the chain is
assumed:

* `hhbf` — the channel bound the restrict column is proved at
  (`restrictK_le_childCharge`'s `hb = 2R+1`); the canonical
  instantiation.
* `hKcov` / `hKcovBot` — the cover stage's budget, against the ledger's
  cover column at an edged node and against the carrier at an edgeless
  one.  Two clauses because `frameChargeMS` has **no** cover column on
  the `A.G = ⊥` branch, while `frameElseK` pays `Kcov` unconditionally
  (`blockSpec_leaf_guard`'s `max`).  The edged clause is exactly the
  shape `ProgCoverChargeDeg.peelK_le_coverCFSel_total` delivers.
* `hKglue` — the frame's glue slot, linear in the carrier.
* `hKrl` — the root load, linear in the word.

`M₀` is discharged by §8 (`b7_botK_le`); `b7_KsChargeBridge_linear`
below exhibits the whole bundle at concrete non-zero budgets. -/
theorem b7_KsChargeBridge (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w Kq : ℕ) (ℓp hbf : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ACost String ℕ)
    (Kcov : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Kglue : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Krl : List ℕ → ℕ) (Kc : ℕ) (av : ScatterSentence 0 → Expr)
    (M₀ ccov cglue crl : ℕ)
    (hhbf : ∀ i, hbf i = 2 * (Headline.headlineSetup C hC φ).R + 1)
    (hbotK : ∀ i : ℕ, i ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ A : Arena ((Headline.headlineSetup C hC φ).pal i) n,
      botComK A.N ((Headline.headlineSetup C hC φ).pal i) Kq
          (levelFml (Headline.headlineSetup C hC φ) i)
        ≤ M₀ * (A.N + 1))
    (hKcov : ∀ (i : ℕ) (A : Arena ((Headline.headlineSetup C hC φ).pal i) n),
      Kcov i A ≤ ccov * (chargeTotal (covC i A) + A.N + 1))
    (hKcovBot : ∀ (i : ℕ) (A : Arena ((Headline.headlineSetup C hC φ).pal i) n),
      A.G = ⊥ → Kcov i A ≤ ccov * (A.N + 1))
    (hKglue : ∀ (k i : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal i) n),
      Kglue k i A ≤ cglue * (A.N + 1))
    (hKrl : ∀ x ∈ mcD n G c w, Krl x ≤ crl * (x.length + 1)) :
    KsChargeBridge C hC φ ord G c w ℓp htabF covC
      (fun x => matK x + (Krl x +
        (chainKB (Headline.headlineSetup C hC φ) ord Kq ℓp hbf Kcov Kglue
            (Headline.headlineSetup C hC φ).depth 0
            (rootArena G (Impl.trivialColoring n)) +
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))) := by
  classical
  refine ⟨b7Cb (Headline.headlineSetup C hC φ) ℓp M₀ ccov cglue crl Kc av, ?_⟩
  intro x hx
  set S := Headline.headlineSetup C hC φ with hS
  set M := b7M S ℓp M₀ ccov cglue with hMdef
  set cB := b7Cb S ℓp M₀ ccov cglue crl Kc av with hcBdef
  have hcB : cB = 11 + crl + M + 6 + Kc + topEvalCost S av := hcBdef
  have hchain := b7_chainKB_le S ord Kq ℓp hbf htabF covC Kcov Kglue M₀ ccov cglue
    hhbf hbotK hKcov hKcovBot hKglue S.depth 0
    (rootArena G (Impl.trivialColoring n)) (by omega)
  have hmc := b7_driver_le_mc S ord ℓp htabF covC G (Impl.trivialColoring n)
  set CT := chargeTotal (mcChargeMS S ord ℓp htabF covC G
    (Impl.trivialColoring n)) with hCT
  set CTd := chargeTotal (driverChargeMS S ord ℓp htabF covC S.depth 0
    (rootArena G (Impl.trivialColoring n))) with hCTd
  have hkrl := hKrl x hx
  have hMcB : M ≤ cB := by omega
  have h1 : M * CTd ≤ cB * CT :=
    (Nat.mul_le_mul_left _ hmc).trans (Nat.mul_le_mul_right _ hMcB)
  have e1 : crl * (x.length + 1) = crl * x.length + crl := by ring
  have e2 : cB * (CT + x.length + 1) = cB * CT + cB * x.length + cB := by ring
  have e3 : (11 + crl) * x.length = 11 * x.length + crl * x.length := by ring
  have h2 : (11 + crl) * x.length ≤ cB * x.length :=
    Nat.mul_le_mul_right _ (by omega)
  have hmat : matK x = 11 * x.length + 6 := rfl
  rw [hmat]
  omega

open Classical in
/-- **Anti-vacuity for the hypothesis bundle**: at the canonical channel
bound and the *non-zero* linear budgets `Kcov j A = A.N + 1`,
`Kglue k j A = A.N + 1`, `Krl x = |x| + 1`, every hypothesis of
`b7_KsChargeBridge` is discharged and the bridge holds outright.  So the
conditional form above is not conditional on anything unsatisfiable, and
`M₀` is never assumed — §8 supplies it. -/
theorem b7_KsChargeBridge_linear (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w Kq : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ACost String ℕ)
    (Kc : ℕ) (av : ScatterSentence 0 → Expr) :
    KsChargeBridge C hC φ ord G c w ℓp htabF covC
      (fun x => matK x + ((x.length + 1) +
        (chainKB (Headline.headlineSetup C hC φ) ord Kq ℓp
            (fun _ => 2 * (Headline.headlineSetup C hC φ).R + 1)
            (fun _ A => A.N + 1) (fun _ _ A => A.N + 1)
            (Headline.headlineSetup C hC φ).depth 0
            (rootArena G (Impl.trivialColoring n)) +
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))) :=
  b7_KsChargeBridge C hC φ ord G c w Kq ℓp _ htabF covC _ _ _ Kc av
    (b7BotK (Headline.headlineSetup C hC φ) Kq) 1 1 1
    (fun _ => rfl)
    (b7_botK_le (Headline.headlineSetup C hC φ) Kq)
    (fun i A => by omega) (fun i A _ => by omega) (fun k i A => by omega)
    (fun x _ => by omega)

/-! ## §10 Axiom profile -/

#print axioms b7_scatterK_le_greedy
#print axioms b7_supports_ge
#print axioms b7_bfs_supports_le
#print axioms b7_profiles_le
#print axioms b7_isolate_le
#print axioms b7_restrict_le
#print axioms b7_centreScatterK_le
#print axioms b7_centre_le
#print axioms b7_centre_edge_le
#print axioms b7_chainKB_bot
#print axioms b7_chainKB_le
#print axioms b7_botK_le
#print axioms b7_driver_le_mc
#print axioms b7_KsChargeBridge
#print axioms b7_KsChargeBridge_linear

end Lax3Proofs.Prog
