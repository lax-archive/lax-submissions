import Lax3Proofs.Unroll
import Lax3Proofs.ImplRestrict
import Lax3Proofs.ImplProfiles
import Lax3Proofs.ImplScatter
import Lax3Proofs.ImplBot
import Lax62Proofs.Refine.NREST.Foreach

/-!
# F3 — one frame of the driver, as an NREST program

`Unroll.frameEval` (`Unroll.lean`) is the code of one frame of the
unrolled driver: `tablesAux`'s recursive body at depth `j`, the
recursion abstracted into the oracle `next`. The machine routines a
frame calls are all landed with specs and charges (`Impl*`); what did
not exist is their **sequenced composition** as one cost-carrying
program in the refinement tower's monad
(`Lax62Proofs.Refine.NREST`). This file is that composition.

## The program (§5 lines 10–28, one node)

`frameProg` branches on the leaf test. On an edgeless arena it runs
`Impl.botEval` over the machine's color rows (§6.4) and returns the
row table. Otherwise:

1. **the cover slot** — a *parameter* `coverProg`, an NREST
   computation returning the vertex ordering, handed in with a
   spec-and-charge pair (hypothesis `hcover` of the refinement
   theorem: it returns `(ord A.N A.G).order` for budget `covC`).
   This is the same move `frameEval` makes with `next`; F5 fills the
   slot with the GKS sweep.
2. **the scratch allocation** — the node's one membership array
   (`ImplRestrict` §3): `A.N` units of `"frame.restrict"`, paid once
   per node, never per child. Together with the per-centre
   `Impl.childCharge` below, the node's total in that currency is
   exactly the landed sweep account `Impl.nodeCharge`
   (`restrict_account`).
3. **the per-centre fold** — `NRest.nfoldli` (the tower's list fold)
   over all centres, each running `centreProg`:

   * **restrict** — the machine arena
     `(ofArena A htab).restrict (cluster S A π u)` (`§6.1`), whose
     graph half IS `preG` — `B₀`, the arena *before* isolation —
     charged `Impl.childCharge` (row scans at parent degrees, color
     rows, `hist` filter, mark+clear);
   * **bfsSupports** — one BFS from the connector on `B₀`
     materializing the `≤ R+1` support names at every reached vertex
     (D6's channel data), as one `NRest.spec` whose postcondition is
     the tower's `BallTable` plus the `Impl.bfsSupports` table read
     off it; its value feeds the *machine's* downward channel, which
     the abstract arena represents by the `(connector, arena)` pair —
     hence the bound value is not consumed by this level's table;
   * **recordProfiles** — the `S.width + Σ_c |f c|` profile BFS
     calls, as one `NRest.spec` with postcondition
     `Impl.ProfileTables` **at `B₀.G = preG`, before isolation**
     (hazard 1: `recordProfiles_eq_childCol` is stated at `preG`;
     measured after isolation the rewrite would be unsound), then the
     row population `Impl.recordProfiles` — which, under the seam,
     IS `Driver.childCol`;
   * **isolate** — `B₀.isolate (Set.range (batchFn …))`, the padded
     batch's edges dropped (§5 line 21, *after* the profiles),
     charged one CSR sweep (`Impl.isolateCharge`);
   * **the recursion slot** — the parameter `nxProg`, called at the
     child arena *assembled from the computed pieces* (`B₁.G`, the
     recorded coloring, `B₁.up`, the extended channel); under the
     profile seam that record equals `Driver.childArena` on the nose
     (`mkChild_eq`), so the slot's spec (hypothesis `hnx`) delivers
     `nx (childArena S A π u)`;
   * **the scatter counts** — one guarded `Impl.greedyScatter` call
     per scatter atom of the level's decompositions (§5 lines 25–26),
     charged at the routine's own account `Impl.greedyScatterCost`
     with marking parameter `W := weight (childArena …)` — computed
     once per child, *not* once per table entry.
4. **the readback** — write-once, definitional via `centre` (E9):
   the entry at `(v, β)` reads the child table of `centre v` and the
   precomputed scatter counts; `1 + |ℱ_j|` units per vertex.

The per-node state across the centre fold is the accumulated family
of child tables (`Function.update` per centre, starting from §5 line
14's uninitialised table); the machine values (`MArena`) ride the
program as definite `returnT`s — the `let` names keep their carrier
`childN` definitionally transparent to the driver-typed batch and
profile data.

## The refinement theorem

`frameProg_le_spec`: given the two slots' spec-and-charge hypotheses,
the machine's row hypothesis `hcol`, and the canonical scatter choice
(`S.choice = greedyChoice` — the guarded routine decides exactly
`greedyChoice.size`, `le_greedyScatter_iff`), the frame program
refines the specification *"the returned table is
`Unroll.frameEval S ord j nx A`'s value, for budget `frameCharge`"*.
The proof crosses the landed identities exactly once each:
`restrict_G_eq_preG` / `childArena_G_eq_isolate_restrict` (both
definitional, inside `mkChild_eq`), `recordProfiles_eq_childCol`
(hazard 1's direction), `le_greedyScatter_iff` (the scatter atom),
and `botEval_eq_sat` (the leaf). The refinement calculus used is a
small spec-composition suite (`returnT_le_spec` … `bindT_le_spec`)
proved here against `NREST`'s primitives — the straight-line
counterpart of the `gwp` route `Refine/Examples/Bfs.lean` takes for
its loop.

## The charge

`frameCharge` is the advertised budget, one named currency per
routine (`"frame.restrict"`, `"frame.supports"`, `"frame.profiles"`,
`"frame.isolate"`, `"frame.scatter"`, `"frame.readback"`,
`"frame.bot"`) plus the two slots' own vectors. Each component is the
landed per-routine account: `Impl.childCharge`, a
`chargeB0 + (R+2)·2‖B₀‖` supports budget (`chargeB0_total` and
`supportsCharge_le` shapes, spent up front the way `bfsBudgetN`
spends the alive weight), `Impl.profilesCharge`,
`Impl.isolateCharge`, `Impl.greedyScatterCost` at `W := ‖child‖`.
`restrict_account` ties the frame's restrict column (one allocation +
per-centre `childCharge`) to `Impl.nodeCharge` — the
one-scratch-array-per-node amortization, as a charge identity.

**Deferred to the continuation (not attempted here):** the
comparison of `frameCharge`'s total against `Unroll.frameCost`'s
shape (`ord.steps + Σ_u (c·nodeCharge·‖child‖ + next child)`). What
is proved here towards it: the scatter column's per-child bound
`scatterCost_le` (`≤ scatterBudget · 2‖child‖`, inside `frameCost`'s
per-child linear envelope) and the restrict column's ledger identity
`frameCharge_restrict_toFun` (`= Impl.nodeCharge`, the scratch
amortization). Two facts constrain the continuation's statement,
read off the landed charges rather than the docstrings:

* **The restrict column is not per-child linear in the child.** The
  row scans are at *parent* degrees (the `K_{3,n−3}` hazard), so
  `childCharge ≰ c·‖child‖` per child; the column fits only the node
  aggregate `D·2M + N·D·const` (`Impl.sum_childCharge_le`) — the
  same `‖A‖^{1+δ}` envelope `dcost_node_le` gives its children
  column. The comparison must therefore be stated at the node
  aggregate under the cover-degree hypothesis, not child by child.
* **The profiles colour column exceeds `frameCost`'s envelope.**
  `Impl.profilesCharge`'s colour half is the iterated single-source
  route — `Σ_c |f c| ≤ L·N₀` calls at `Θ((R+1)·‖B₀‖)` each, i.e. up
  to `L·(R+1)·‖B₀‖²` per child — a factor `‖B₀‖` above
  `frameCost`'s `c·nodeCharge·‖child‖`, and the node aggregate
  `Σ_u ‖B₀ᵤ‖²` need not fit `‖A‖^{1+δ}` either (one cluster can be
  nearly the whole arena). This is `ImplProfiles`' recorded §6.3 gap
  (no multi-source BFS in the tower) surfacing at the composition:
  with the landed charges, the charge theorem against `frameCost`
  *as shaped* is false in the colour column. The continuation must
  either land a multi-source BFS (restoring §6.3's `m + L` count),
  or state the comparison against a cost shape whose per-child
  multiplier carries the extra `L·N₀` factor.
-/

namespace Lax3Proofs.Prog

open Lax62Proofs.Refine
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun

/-! ## A spec-composition calculus for straight-line NREST programs

`Refine/Examples/Bfs.lean` proves its refinement through `gwp` and the
loop rule; a frame is straight-line (its one fold is structural over a
list), so the four rules below — return, consume, bind, weaken — are
all it needs. Each is proved directly against `NREST`'s primitives.
All at `ECost`, the tower's cost carrier. -/

section SpecCalculus

variable {α β : Type}

private theorem coe_zero_le (c : ECost) :
    ((0 : ECost) : WithBot ECost) ≤ (c : WithBot ECost) :=
  WithBot.coe_le_coe.mpr (Nonneg.needname_nonneg c)

/-- A `returnT` refines any spec its value satisfies, for any budget
(`ECost` has no negative charges). -/
theorem returnT_le_spec {P : α → Prop} {x : α} (hx : P x) (c : ECost) :
    NRest.returnT x ≤ NRest.spec P fun _ => c := by
  rw [NRest.returnT, NRest.spec, NRest.rest_le_rest_iff]
  refine NRest.single_le_iff.mpr ?_
  rw [if_pos hx]
  exact coe_zero_le c

/-- Charging on top of a specified computation adds to the budget. -/
theorem consume_le_spec {m : NRest α ECost} {P : α → Prop} {c : ECost}
    (t : ECost) (hm : m ≤ NRest.spec P fun _ => c) :
    NRest.consume m t ≤ NRest.spec P fun _ => t + c := by
  classical
  refine le_trans (NRest.consume_mono hm le_rfl) ?_
  rw [NRest.spec, NRest.consume_rest, NRest.spec, NRest.rest_le_rest_iff]
  intro v
  show WithBot.map (t + ·) (if P v then ((c : ECost) : WithBot ECost) else ⊥)
    ≤ if P v then (((t + c : ECost) : ECost) : WithBot ECost) else ⊥
  by_cases h : P v
  · rw [if_pos h, if_pos h, WithBot.map_coe]
  · rw [if_neg h, if_neg h, WithBot.map_bot]

/-- The one-step program "pay `t`, return `x`". -/
theorem consume_returnT_le_spec {P : α → Prop} {x : α} (hx : P x) (t : ECost) :
    NRest.consume (NRest.returnT x) t ≤ NRest.spec P fun _ => t := by
  have h := consume_le_spec (m := NRest.returnT x) t (returnT_le_spec hx 0)
  rwa [add_zero] at h

/-- **The bind rule**: sequencing adds the budgets, and the second
program may assume the first's postcondition. -/
theorem bindT_le_spec {m : NRest α ECost} {f : α → NRest β ECost}
    {P : α → Prop} {Q : β → Prop} {c₁ c₂ : ECost}
    (hm : m ≤ NRest.spec P fun _ => c₁)
    (hf : ∀ x, P x → f x ≤ NRest.spec Q fun _ => c₂) :
    NRest.bindT m f ≤ NRest.spec Q fun _ => c₁ + c₂ := by
  refine le_trans (NRest.bindT_mono hm fun x => le_rfl) ?_
  rw [NRest.spec, NRest.bindT_rest]
  refine sSup_le ?_
  rintro n ⟨x, t, hx, rfl⟩
  by_cases hP : P x
  · rw [if_pos hP] at hx
    obtain rfl : c₁ = t := WithBot.coe_inj.mp hx
    exact consume_le_spec c₁ (hf x hP)
  · rw [if_neg hP] at hx
    exact absurd hx.symm WithBot.coe_ne_bot

/-- Consequence: weaken the postcondition, raise the budget. -/
theorem spec_le_spec {P Q : α → Prop} {c c' : ECost}
    (hPQ : ∀ x, P x → Q x) (hc : c ≤ c') :
    (NRest.spec P fun _ => c) ≤ NRest.spec Q fun _ => c' := by
  classical
  rw [NRest.spec, NRest.spec, NRest.rest_le_rest_iff]
  intro v
  show (if P v then ((c : ECost) : WithBot ECost) else ⊥)
    ≤ if Q v then ((c' : ECost) : WithBot ECost) else ⊥
  by_cases h : P v
  · rw [if_pos h, if_pos (hPQ v h)]
    exact WithBot.coe_le_coe.mpr hc
  · rw [if_neg h]
    exact bot_le

/-- `spec_le_spec`, composed onto a refinement. -/
theorem le_spec_weaken {m : NRest α ECost} {P Q : α → Prop} {c c' : ECost}
    (hm : m ≤ NRest.spec P fun _ => c) (hPQ : ∀ x, P x → Q x) (hc : c ≤ c') :
    m ≤ NRest.spec Q fun _ => c' :=
  le_trans hm (spec_le_spec hPQ hc)

end SpecCalculus

/-! ## The frame's data -/

variable {L n₀ : ℕ}

/-- The child table of one centre: the value the recursion slot
delivers for the child arena of `u`. -/
abbrev ChildTab (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : Type :=
  Fin (childN S A π u) → DistFO (S.pal (j + 1)) 1 → Prop

/-- The per-node fold state: the accumulated family of child tables,
one per centre. -/
abbrev Tabs (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) : Type :=
  (u : Fin A.N) → ChildTab S j A π u

/-! ## The charges, one named currency per routine

Every component is a landed per-routine account (module docstring).
`ℕ`-valued `ACost`s, lifted by `liftACost` where the program spends
them — the `Bfs.bfsBudgetN` discipline. -/

open Classical in
/-- The per-centre `restrict` charge: `Impl.childCharge` — row scans at
**parent** degrees, `|S|·(Lc + ℓp·(2R+1))` for rows and `hist`, `2|S|`
for mark and clear. No carrier-sized term: the allocation is the
node's (`allocC`). -/
noncomputable def restrictC (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ACost String ℕ :=
  ACost.cost "frame.restrict" (Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u))

/-- The node's scratch-array allocation (`ImplRestrict` §3): once per
node, in the same currency as the per-centre `restrict` charges, so
that the node's `"frame.restrict"` total is `Impl.nodeCharge`
(`restrict_account`). -/
noncomputable def allocC {L n₀ : ℕ} {S : Setup L} {j : ℕ}
    (A : Arena (S.pal j) n₀) : ACost String ℕ :=
  ACost.cost "frame.restrict" A.N

open Classical in
/-- The `bfsSupports` budget: one `chargeB0`-shaped BFS call
(`chargeB0_total`: `2‖B₀‖ + R + 2`) plus the support materialization at
its `(R+2)·ballNorm ≤ (R+2)·2‖B₀‖` bound (`supportsCharge_le`; the
whole-arena bound is spent up front, the `bfsBudgetN` discipline). -/
noncomputable def supportsC (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ACost String ℕ :=
  ACost.cost "frame.supports"
    ((2 * Impl.gsize (preG S A π u) + S.R + 2)
      + (S.R + 2) * (2 * Impl.gsize (preG S A π u)))

open Classical in
/-- The profile charge: `Impl.profilesCharge` — `S.width` batch calls
plus `Σ_c |f c|` colour calls (the iterated route), each at
`callCost = chargeB0 + (R+1)·n` rows, at `B₀ = preG`. -/
noncomputable def profilesC (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ACost String ℕ :=
  ACost.cost "frame.profiles"
    (Impl.profilesCharge (preG S A π u) S.width (childColR S A π u) S.R)

open Classical in
/-- The isolate charge: one CSR sweep of `B₀`
(`Impl.isolateCharge = 2M + N ≤ 2‖B₀‖`). -/
noncomputable def isolateC (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ACost String ℕ :=
  ACost.cost "frame.isolate"
    (Impl.isolateCharge ((Impl.ofArena A htab).restrict (cluster S A π u)))

/-- The scatter account of one child, at table `T`: one guarded
`greedyScatter` call per scatter atom of the level's decompositions,
each at the routine's own cost with marking parameter
`W := weight (childArena …)` (§6.5's `W := ‖A‖` instantiation). Zero
outright at `σ.t = 0` — the guard is a cost statement
(`greedyScatterCost_zero`). -/
noncomputable def scatterCost (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (T : ChildTab S j A π u) : ℕ :=
  ((F S j).map fun β =>
    ((scatterAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)).map fun σ =>
      Impl.greedyScatterCost (childArena S A π u).G σ.r {a | T a σ.β}
        (weight (childArena S A π u)) σ.t).sum).sum

/-- **The per-centre charge**: restrict, supports, profiles, isolate,
the recursion slot's own vector, and the scatter counts — nested
exactly as `centreProg` sequences them. The scatter component is
priced at the slot's delivered table `nx (childArena …)`, the same
dependence `Unroll.frameCost` has on its `next` parameter. -/
noncomputable def centreCharge (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ACost String ℕ :=
  restrictC S j A ℓp π u + (supportsC S j A π u + (profilesC S j A π u
    + (isolateC S j A htab π u + (nxC (childArena S A π u)
      + ACost.cost "frame.scatter"
          (scatterCost S j A π u (nx (childArena S A π u)))))))

/-- The leaf charge (§6.4): the `BotTables` row evaluation, linear in
the arena per schedule row — `(1 + |ℱ_j|) · ‖A‖`, the abstract
`c · weight A` of `Unroll.frameCost`'s leaf with `c` a schedule
constant. -/
noncomputable def botC (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀) :
    ACost String ℕ :=
  ACost.cost "frame.bot" ((1 + (F S j).length) * weight A)

/-- The readback charge: write-once via `centre` (E9) — one owner test
and `|ℱ_j|` entry reads per vertex; the scatter counts were already
paid per centre. -/
noncomputable def readC (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀) :
    ACost String ℕ :=
  ACost.cost "frame.readback" (A.N * (1 + (F S j).length))

/-- **The scratch amortization, as a charge identity**: the frame's
`"frame.restrict"` account — one allocation plus per-centre
`childCharge` — is exactly the landed sweep account
`Impl.nodeCharge` at the node's cluster list (`ImplRestrict` §3:
`restrictSweep`'s accumulator discipline; the invariant that the one
array is clean again after every child is `restrictSweep_fst`). -/
theorem restrict_account (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (π : Equiv.Perm (Fin A.N)) [DecidableRel A.G.Adj] :
    A.N + (((List.finRange A.N).map fun u =>
        Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u))).sum
      = Impl.nodeCharge A.G (S.pal j) ℓp S.R
          ((List.finRange A.N).map (cluster S A π)) := by
  rw [Impl.nodeCharge_eq_sum, List.map_map]
  rfl

/-! ## The per-centre pipeline -/

open Classical in
/-- **The per-centre body** (§5 lines 15–26, one centre): restrict →
bfsSupports → recordProfiles → isolate → the recursion slot → the
scatter counts. The machine values are definite (`consume`/`returnT`);
the two BFS stages are `NRest.spec`s in the tower's `BallTable`
vocabulary (E11's seam, one hypothesis wide); the recursion slot is
called at the child arena assembled from the computed pieces. The
`let`s keep the machine carrier `childN` definitionally transparent to
the driver-typed batch and profile data. -/
noncomputable def centreProg (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    NRest (ChildTab S j A π u) ECost :=
  -- `B₀ := restrict(A, X_u)` (§6.1): carrier the cluster, graph `preG`
  let B₀ := (Impl.ofArena A htab).restrict (cluster S A π u)
  NRest.bindT (NRest.consume (NRest.returnT B₀)
      (liftACost (restrictC S j A ℓp π u))) fun _ =>
  -- one BFS from the connector on `B₀`, supports materialized (§4, D6)
  NRest.bindT (NRest.spec
      (fun DT : (Fin B₀.N → ℕ) × (Fin B₀.N → Option (List (Fin B₀.N))) =>
        Impl.BallTable B₀.G (centreChild S A π u) S.R DT.1 ∧
          DT.2 = Impl.bfsSupports B₀.G DT.1 S.R)
      fun _ => liftACost (supportsC S j A π u)) fun _DT =>
  -- the `m + Σ_c |f c|` profile BFS calls, at `B₀` — BEFORE isolation
  NRest.bindT (NRest.spec
      (fun DD : (Fin S.width → Fin B₀.N → ℕ) ×
          (Fin (relPal (S.pal j)) → Fin B₀.N → Fin B₀.N → ℕ) =>
        Impl.ProfileTables B₀.G (batchFn S A π u)
          (relColoring B₀.col Set.univ) S.R DD.1 DD.2)
      fun _ => liftACost (profilesC S j A π u)) fun DD =>
  -- `recordProfiles`: populate the rows off the arrays (§6.3; the row
  -- writes are inside `profilesC`'s `callCost`)
  NRest.bindT (NRest.returnT
      (Impl.recordProfiles S.R (relColoring B₀.col Set.univ) DD.1 DD.2)) fun colC =>
  -- isolate the padded batch (§5 line 21 — AFTER the profiles)
  let B₁ := B₀.isolate (Set.range (batchFn S A π u))
  NRest.bindT (NRest.consume (NRest.returnT B₁)
      (liftACost (isolateC S j A htab π u))) fun _ =>
  -- the recursion slot, at the child assembled from the computed pieces
  NRest.bindT (nxProg ⟨childN S A π u, B₁.G, colC, B₁.up,
      (A.up u, histGraph S A π u) :: A.hist⟩) fun Tu =>
  -- the guarded scatter counts for this child (§5 lines 25–26)
  NRest.consume (NRest.returnT Tu)
    (liftACost (ACost.cost "frame.scatter" (scatterCost S j A π u Tu)))

/-- **The assembled child is the driver's child**: the record built
from the machine pieces — `isolate (restrict …)`'s graph and renaming,
the recorded coloring, the extended channel — equals
`Driver.childArena` as soon as the coloring does. The graph and
renaming halves are the landed definitional identities
(`restrict_G_eq_preG`, `childArena_G_eq_isolate_restrict`,
`restrict_up_eq_childArena_up`). -/
theorem mkChild_eq (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {colC : Coloring (childN S A π u) (S.pal (j + 1))}
    (hcolC : colC = childCol S A π u) :
    (⟨childN S A π u,
      (((Impl.ofArena A htab).restrict (cluster S A π u)).isolate
        (Set.range (batchFn S A π u))).G,
      colC,
      (((Impl.ofArena A htab).restrict (cluster S A π u)).isolate
        (Set.range (batchFn S A π u))).up,
      (A.up u, histGraph S A π u) :: A.hist⟩ : Arena (S.pal (j + 1)) n₀)
      = childArena S A π u := by
  subst hcolC
  rfl

/-- The refinement of the per-centre body: given the recursion slot's
spec-and-charge hypothesis, `centreProg` delivers exactly the oracle's
table at the driver's child arena, for `centreCharge`. -/
theorem centreProg_le_spec (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    {nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost}
    {nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop}
    {nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ}
    (hnx : ∀ B, nxProg B ≤ NRest.spec (fun T => T = nx B) fun _ => liftACost (nxC B))
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    centreProg S j A htab nxProg π u ≤
      NRest.spec (fun Tu : ChildTab S j A π u => Tu = nx (childArena S A π u))
        (fun _ => liftACost (centreCharge S j A ℓp htab nx nxC π u)) := by
  rw [centreProg, centreCharge]
  simp only [liftACost_add]
  -- restrict
  refine bindT_le_spec (consume_returnT_le_spec (P := fun _ => True) trivial _)
    fun _ _ => ?_
  -- supports
  refine bindT_le_spec le_rfl fun _DT _ => ?_
  -- profiles
  refine bindT_le_spec le_rfl fun DD hDD => ?_
  -- recordProfiles is a pure step
  rw [NRest.returnT_bindT]
  -- under the seam, the recorded coloring IS the driver's child colors
  -- (hazard 1: `recordProfiles_eq_childCol` is stated at `preG`)
  have hcolC : Impl.recordProfiles S.R (relColoring
      ((Impl.ofArena A htab).restrict (cluster S A π u)).col Set.univ) DD.1 DD.2
      = childCol S A π u :=
    Impl.recordProfiles_eq_childCol S A π u hDD
  -- isolate
  refine bindT_le_spec (consume_returnT_le_spec (P := fun _ => True) trivial _)
    fun _ _ => ?_
  -- the recursion slot: with the coloring rewritten, the assembled
  -- record is (definitionally) the driver's child arena
  rw [hcolC]
  refine bindT_le_spec (hnx (childArena S A π u)) fun Tu hTu => ?_
  -- the scatter step: pay the account at the delivered table
  subst hTu
  exact consume_returnT_le_spec
    (P := fun Tu : ChildTab S j A π u => Tu = nx (childArena S A π u)) rfl _

/-! ## The fold over the centres -/

/-- One fold step: run the per-centre body, write its table at `u`. -/
noncomputable def foldBody (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (acc : Tabs S j A π) :
    NRest (Tabs S j A π) ECost :=
  NRest.bindT (centreProg S j A htab nxProg π u) fun Tu =>
    NRest.returnT (Function.update acc u Tu)

/-- The fold's refinement, by structural induction over the centre
list: the processed centres hold the oracle's tables, the rest still
hold the accumulator's, and the charge is the sum of the per-centre
charges. -/
theorem fold_le_spec (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    {nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost}
    {nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop}
    {nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ}
    (hnx : ∀ B, nxProg B ≤ NRest.spec (fun T => T = nx B) fun _ => liftACost (nxC B))
    (π : Equiv.Perm (Fin A.N)) :
    ∀ (l : List (Fin A.N)) (acc : Tabs S j A π),
      NRest.nfoldli (fun _ => true) (foldBody S j A htab nxProg π) l acc ≤
        NRest.spec
          (fun T : Tabs S j A π => ∀ u : Fin A.N,
            (u ∈ l → T u = nx (childArena S A π u)) ∧ (u ∉ l → T u = acc u))
          (fun _ => liftACost ((l.map (centreCharge S j A ℓp htab nx nxC π)).sum)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    rw [NRest.nfoldli_nil]
    refine returnT_le_spec (fun u => ⟨fun hu => absurd hu (by simp), fun _ => rfl⟩) _
  | cons u us ih =>
    intro acc
    rw [NRest.nfoldli_cons, if_pos rfl, List.map_cons, List.sum_cons, liftACost_add]
    refine bindT_le_spec (P := fun acc' : Tabs S j A π =>
        acc' = Function.update acc u (nx (childArena S A π u))) ?_ ?_
    · -- one centre: run the body, write the delivered table
      rw [foldBody]
      have h := bindT_le_spec (centreProg_le_spec S j A htab hnx π u)
        (Q := fun acc' : Tabs S j A π =>
          acc' = Function.update acc u (nx (childArena S A π u)))
        (c₂ := 0)
        (fun Tu hTu => returnT_le_spec (by rw [hTu]) 0)
      rwa [add_zero] at h
    · -- the remaining centres, from the updated accumulator
      intro acc' hacc'
      subst hacc'
      refine le_spec_weaken (ih _) (fun T hT w => ?_) le_rfl
      obtain ⟨h₁, h₂⟩ := hT w
      constructor
      · intro hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · by_cases hwus : w ∈ us
          · exact h₁ hwus
          · rw [h₂ hwus, Function.update_self]
        · exact h₁ hw'
      · intro hw
        have hwu : w ≠ u := fun h => hw (h ▸ List.mem_cons_self ..)
        have hwus : w ∉ us := fun h => hw (List.mem_cons_of_mem _ h)
        rw [h₂ hwus, Function.update_of_ne hwu]

/-! ## The readback and the leaf -/

open Classical in
/-- **The write-once readback** (§5 lines 24–28, E9): the entry at
`(v, β)` reads the child table of `centre v` — ownership is
definitional via `centre` — and evaluates the decomposition, its local
atoms from the child table, its scatter atoms by the precomputed
guarded `greedyScatter` counts. This is `frameEval`'s text with the
machine's scatter routine in place of the abstract `choice.size`. -/
noncomputable def readback (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) (T : Tabs S j A π) :
    Fin A.N → DistFO (S.pal j) 1 → Prop :=
  fun v β =>
    let u := centre S A π v
    let B := childArena S A π u
    let vc : Fin B.N := (childEquiv S A π u).symm ⟨v, mem_cluster_centre S A π v⟩
    if h : IsLocal β ∧ DRank 1 (S.q - 1) β then
      (dec S (j := j) ⟨β, h.1, h.2⟩).eval
        (Sum.elim (fun ψ => T u vc ψ)
          (fun σ => σ.t ≤ Impl.greedyScatter B.G σ.r {a | T u a σ.β} σ.t))
    else True

/-- The readback computes `frameEval`'s non-leaf value: with the child
tables delivered by the oracle and the canonical scatter choice, the
guarded count decides each scatter atom exactly
(`le_greedyScatter_iff`). -/
theorem readback_eq_frameEval (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀)
    {nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop}
    (hbot : ¬ A.G = ⊥) (hchoice : S.choice = greedyChoice)
    {T : Tabs S j A ((ord A.N A.G).order)}
    (hT : ∀ u, T u = nx (childArena S A ((ord A.N A.G).order) u)) :
    readback S j A ((ord A.N A.G).order) T = Unroll.frameEval S ord j nx A := by
  rw [Unroll.frameEval, if_neg hbot]
  funext v β
  simp only [readback]
  by_cases h : IsLocal β ∧ DRank 1 (S.q - 1) β
  · rw [dif_pos h, dif_pos h]
    refine congrArg (fun f => (dec S (j := j) ⟨β, h.1, h.2⟩).eval f)
      (funext fun x => ?_)
    cases x with
    | inl ψ => simp only [Sum.elim_inl, hT]
    | inr σ =>
      simp only [Sum.elim_inr, hT, hchoice]
      exact propext (Impl.le_greedyScatter_iff _ _ _ _)
  · rw [dif_neg h, dif_neg h]

/-- The leaf value: `botEval` over the machine's rows computes
`frameEval`'s leaf table — `tablesAux_bot_eq_botEval`'s content at the
frame (`botEval_eq_sat` at the edgeless arena). -/
theorem botTable_eq_frameEval (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀)
    {nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop}
    {colB : Fin A.N → Fin (S.pal j) → Bool}
    (hcol : ∀ v c, colB v c = true ↔ v ∈ A.col c) (hbot : A.G = ⊥) :
    (fun (v : Fin A.N) (β : DistFO (S.pal j) 1) =>
        Impl.botEval colB (fun _ => v) β = true)
      = Unroll.frameEval S ord j nx A := by
  rw [Unroll.frameEval, if_pos hbot]
  funext v β
  show (Impl.botEval colB (fun _ => v) β = true) = Sat A.G A.col (fun _ => v) β
  refine propext ((Impl.botEval_eq_sat colB A.col hcol β (fun _ => v)).trans ?_)
  rw [hbot]

/-! ## The frame -/

open Classical in
/-- **The frame program** (§5 lines 10–28, one node of the unrolled
driver): the leaf test; else the cover slot, the node's scratch
allocation, the per-centre fold, and the write-once readback. The
cover pass (`coverProg`) and the recursive call (`nxProg`) are
parameters — each an NREST computation handed in with a
spec-and-charge pair, the same move `Unroll.frameEval` makes with
`next`. -/
noncomputable def frameProg (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (colB : Fin A.N → Fin (S.pal j) → Bool)
    (coverProg : NRest (Equiv.Perm (Fin A.N)) ECost)
    (nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost) :
    NRest (Fin A.N → DistFO (S.pal j) 1 → Prop) ECost :=
  if A.G = ⊥ then
    -- the leaf (§6.4): the finite row evaluator, linear charge
    NRest.consume
      (NRest.returnT fun (v : Fin A.N) (β : DistFO (S.pal j) 1) =>
        Impl.botEval colB (fun _ => v) β = true)
      (liftACost (botC S j A))
  else
    -- the cover slot (§5 line 13)
    NRest.bindT coverProg fun π =>
    -- the node's one scratch array (§6.1's amortization)
    NRest.bindT (NRest.consume (NRest.returnT ()) (liftACost (allocC A))) fun _ =>
    -- the per-centre pipeline, over every centre (§5 lines 15–26)
    NRest.bindT (NRest.nfoldli (fun _ => true) (foldBody S j A htab nxProg π)
      (List.finRange A.N) fun _ => fun _ _ => True) fun T =>
    -- the write-once readback (§5 lines 24–28)
    NRest.consume (NRest.returnT (readback S j A π T)) (liftACost (readC S j A))

open Classical in
/-- **The frame's advertised budget**, mirroring the program: the leaf
charge, or the cover slot's vector plus the node allocation, the
per-centre charges at the cover's ordering, and the readback. -/
noncomputable def frameCharge (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (covC : ACost String ℕ) (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ) :
    ACost String ℕ :=
  if A.G = ⊥ then botC S j A
  else covC + (allocC A
    + ((((List.finRange A.N).map
          (centreCharge S j A ℓp htab nx nxC ((ord A.N A.G).order))).sum)
        + readC S j A))

/-- **F3's refinement theorem.** Given

* the machine's row hypothesis `hcol` (§4's `col` array),
* the canonical scatter choice (`S.choice = greedyChoice` — the
  guarded routine decides exactly the greedy count),
* the cover slot's spec-and-charge pair `hcover` (F5's obligation:
  the slot returns the routine's ordering for budget `covC`), and
* the recursion slot's spec-and-charge pair `hnx` (the level below:
  for every child arena the slot delivers the oracle's table for
  budget `nxC`),

the frame program refines the specification *"the returned table is
`Unroll.frameEval S ord j nx A`'s value, for budget `frameCharge`"* —
one frame of the unrolled driver, as a machine-shaped, cost-carrying
NREST program. -/
theorem frameProg_le_spec (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    {colB : Fin A.N → Fin (S.pal j) → Bool}
    {coverProg : NRest (Equiv.Perm (Fin A.N)) ECost}
    {nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost}
    {nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop}
    {covC : ACost String ℕ} {nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ}
    (hcol : ∀ v c, colB v c = true ↔ v ∈ A.col c)
    (hchoice : S.choice = greedyChoice)
    (hcover : coverProg ≤
      NRest.spec (fun π => π = (ord A.N A.G).order) fun _ => liftACost covC)
    (hnx : ∀ B, nxProg B ≤ NRest.spec (fun T => T = nx B) fun _ => liftACost (nxC B)) :
    frameProg S j A htab colB coverProg nxProg ≤
      NRest.spec (fun T => T = Unroll.frameEval S ord j nx A)
        (fun _ => liftACost (frameCharge S ord j A ℓp htab nx covC nxC)) := by
  rw [frameProg, frameCharge]
  by_cases hbot : A.G = ⊥
  · rw [if_pos hbot, if_pos hbot]
    refine consume_returnT_le_spec
      (P := fun T => T = Unroll.frameEval S ord j nx A) ?_ _
    exact botTable_eq_frameEval S ord j A hcol hbot
  · rw [if_neg hbot, if_neg hbot]
    simp only [liftACost_add]
    -- the cover slot
    refine bindT_le_spec hcover fun π hπ => ?_
    subst hπ
    -- the scratch allocation
    refine bindT_le_spec (consume_returnT_le_spec (P := fun _ => True) trivial _)
      fun _ _ => ?_
    -- the centre fold
    refine bindT_le_spec
      (fold_le_spec S j A htab hnx ((ord A.N A.G).order) (List.finRange A.N)
        (fun _ => fun _ _ => True))
      fun T hT => ?_
    -- the readback
    refine consume_returnT_le_spec
      (P := fun T => T = Unroll.frameEval S ord j nx A) ?_ _
    exact readback_eq_frameEval S ord j A hbot hchoice
      fun u => (hT u).1 (List.mem_finRange u)

/-! ## The charge, read off the ledger (towards deliverable 3)

Per-currency closed forms of `frameCharge` — the inputs of the
comparison against `Unroll.frameCost`, which is the continuation's
theorem (module docstring). The two proved here are the ones with
one-line landed content: the scatter column's `t·‖A‖` bound (hazard
3's shape) and the restrict column's identity with the sweep account
(the scratch amortization). The slot-hygiene hypotheses (`hcov`,
`hnxC`: the slots do not spend the frame's own currencies) are
interface constraints on F4/F5, not facts. -/

/-- **The scatter column, bounded** (hazard 3's shape): the guarded
calls of one child cost at most `scatterBudget S j · 2‖child‖` —
`greedyScatterCost_le` per atom (`t·(n + W)` at `W := ‖child‖`,
`n ≤ ‖child‖`), summed over the level's atoms. Independent of the
table. -/
theorem scatterCost_le (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (T : ChildTab S j A π u) :
    scatterCost S j A π u T
      ≤ scatterBudget S j * (2 * weight (childArena S A π u)) := by
  have hNW : (childArena S A π u).N ≤ weight (childArena S A π u) :=
    Nat.le_add_right _ _
  calc scatterCost S j A π u T
      ≤ ((F S j).map fun β =>
          ((scatterAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)).map
            fun σ => σ.t * (2 * weight (childArena S A π u))).sum).sum := by
        refine List.sum_le_sum fun β _ => List.sum_le_sum fun σ _ => ?_
        refine le_trans (Impl.greedyScatterCost_le _ _ _ _ _) ?_
        exact Nat.mul_le_mul_left _ (by omega)
    _ = scatterBudget S j * (2 * weight (childArena S A π u)) := by
        rw [scatterBudget, ← List.sum_map_mul_right]
        congr 1
        refine List.map_congr_left fun β _ => ?_
        exact List.sum_map_mul_right ..

/-- `toFun` distributes over a list sum of cost vectors. -/
theorem toFun_listSum (l : List (ACost String ℕ)) (k : String) :
    l.sum.toFun k = (l.map fun x => x.toFun k).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.sum_cons, ACost.toFun_add, ih, List.map_cons, List.sum_cons]

open Classical in
/-- The per-centre `"frame.restrict"` ledger entry is exactly
`Impl.childCharge`, provided the recursion slot spends its own
currencies (`hnxC`). -/
theorem centreCharge_restrict_toFun (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (hnxC : ∀ B, (nxC B).toFun "frame.restrict" = 0) :
    (centreCharge S j A ℓp htab nx nxC π u).toFun "frame.restrict"
      = Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u) := by
  simp [centreCharge, restrictC, supportsC, profilesC, isolateC, hnxC,
    ACost.toFun_add]

open Classical in
/-- **The scratch amortization, on the frame's actual ledger**: at a
node with an edge, the frame's whole `"frame.restrict"` account — the
one allocation plus the per-centre `childCharge`s — is exactly the
landed sweep account `Impl.nodeCharge` at the node's cluster list
(`restrictSweep`'s accumulator discipline, `nodeCharge_eq_sum`).
Slot hygiene (`hcov`, `hnxC`) as above. -/
theorem frameCharge_restrict_toFun (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (covC : ACost String ℕ) (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    (hbot : ¬ A.G = ⊥)
    (hcov : covC.toFun "frame.restrict" = 0)
    (hnxC : ∀ B, (nxC B).toFun "frame.restrict" = 0) :
    (frameCharge S ord j A ℓp htab nx covC nxC).toFun "frame.restrict"
      = Impl.nodeCharge A.G (S.pal j) ℓp S.R
          ((List.finRange A.N).map (cluster S A ((ord A.N A.G).order))) := by
  rw [frameCharge, if_neg hbot, Impl.nodeCharge_eq_sum, List.map_map]
  simp only [ACost.toFun_add, hcov, toFun_listSum, List.map_map]
  have hmap : ∀ u : Fin A.N,
      ((fun x => ACost.toFun x "frame.restrict") ∘
        centreCharge S j A ℓp htab nx nxC ((ord A.N A.G).order)) u
      = (Impl.childCharge A.G (S.pal j) ℓp S.R ∘ cluster S A ((ord A.N A.G).order)) u :=
    fun u => centreCharge_restrict_toFun S j A ℓp htab nx nxC _ u hnxC
  rw [List.map_congr_left fun u _ => hmap u]
  simp [allocC, readC]

end Lax3Proofs.Prog
