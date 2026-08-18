import Lax3Proofs.ProgDriver
import Lax3Proofs.ProgCover
import Lax3Proofs.ImplMultiSource

/-!
# F3c — the program's charge against the abstract cost, at the node

`ProgDriver.driverCharge` is the level recursion of
`ProgFrame.frameCharge`; `DriverCost.dcost_root_le` prices the abstract
driver at `K^(ℓ+1)·‖A₀‖^(1+ε)`. This file closes the gap between them:
the **program's** ledger total obeys the same `‖A‖^{1+2δ}`-per-node /
`Σ‖child‖`-mass recurrence, so the root program's whole budget — the
driver's charge plus the top scatter column — is `≤ κ·(‖G‖+1)^{1+ε}` on
class members, and `≤ T x` against the axiom's own measure on CSR
encodings (E13's item (e) shape).

## The total

`chargeTotal` sums an `ACost String ℕ` ledger over the ten currencies
the program family spends (`progKeys`): the cover slot's two
(`"cover.order"`, `"cover.sweep"`), the frame's seven (`"frame.*"`),
and the root evaluation's `"top.scatter"`. `chargeTotal_support`-style
honesty is by construction: every vector below is a sum of
`ACost.cost` at these keys, and `mcChargeMS_toFun_eq_zero` proves the
whole root budget vanishes off `progKeys`, so the total genuinely is
the whole ledger. `totalE_liftACost` is the `ECost` bridge: the same
ten-currency total of the lifted budget is the `ℕ∞`-cast of
`chargeTotal` — the number F7 multiplies by the machine's `L.const`.

## Route (b): the profiles column, swapped (F3b consumed)

`frameCharge` hardcodes the iterated-route `Impl.profilesCharge` in its
`"frame.profiles"` column (`ProgFrame.profilesC`), and with that column
the comparison against the abstract cost shape is **false**
(`ProgFrame`'s module docstring: the colour half is `Σ_c |f c|` calls,
up to `L·N₀·(R+1)·‖B₀‖` per child — a node aggregate `Σ_u ‖B₀ᵤ‖²` that
does not fit `‖A‖^{1+δ}`). So route (b) is forced: `profilesCMS` /
`centreChargeMS` / `frameChargeMS` / `driverChargeMS` / `mcChargeMS`
are the landed charges with that **one column** swapped to F3b's
multi-source budget `Impl.profilesChargeMS` (`profilesChargeMS_le`:
`≤ (mb+L)·6(R+1)(‖B₀‖+1)` — §6.3's count restored). The lemma
`frameCharge`-users need is `driverChargeMS_toFun_eq` /
`mcChargeMS_toFun_eq`: **on every currency except `"frame.profiles"`
the MS budget is the landed budget**, entry by entry — so F3/F4's
ledger identities (`frameCharge_restrict_toFun`, slot hygiene, …)
transfer verbatim, and the program-side reroute (the profile stage's
`NRest.spec` rebudgeted at `profilesCMS`, its postcondition discharged
by `recordProfilesMS_eq_childCol`) changes exactly one column.

## The per-node comparison (`frameChargeMS_chargeTotal_le`)

At a node with an edge, under the cover-degree hypothesis in the
landed fibre form (`cluster_fibre_eq` converts it to the
`wreach`-degree bound `exists_wreach_degree_timedGreedyRoutine`
supplies) and a `f·N^{1+2δ}` bound on the cover slot's total
(`exists_coverCharge_le` supplies it for `coverC` at the honest
`timedGreedyRoutine` steps — F5's vacuity note is answered by
`coverC_order_eq_steps`), the frame's whole ledger total is

    ≤ (f + (c+1)·nodeConst)·‖A‖^{1+2δ} + Σ_u (recursion slot totals).

The comparison is **at the node aggregate**, never per child — the
restrict column is the parent-degree sweep account
(`Impl.sum_childCharge_le`), the supports/profiles/isolate columns are
priced through `gsize_preG_le : ‖B₀ᵤ‖ ≤ clusterWeight` and
`CoverEdgeSum.sum_clusterWeight_le_rpow`, the scatter column through
`scatterCost_le` and the mass clause. The `dcost_node_le`-shaped
middle term `c·Σ_u ‖child‖` is folded into the `‖A‖^{1+2δ}` envelope
via the same mass clause (`dcost_node_le` itself already folds it to
`(c_D+1)·‖A‖^{1+δ}`); a direct pointwise `κ·dcost` comparison is not
available — `dcost` has no `‖A‖^{1+δ}` lower bound at a node, while
the program's node columns genuinely spend it.

## The level lift and the headline

`driverChargeMS_chargeTotal_le` reruns `DriverCost.dcostAux_le`'s
downward induction on `chargeTotal ∘ driverChargeMS`: per-node the
inequality above, the recursive column through the mass clause
(`sum_child_weight_le`), empty clusters contributing `0`
(`driverChargeMS_chargeTotal_eq_zero`), the chosen constant
`KP = f + (c+1)·nodeConstBound + (c+1) + botBound`, per-level exponent
increment `2δ`. `mcChargeMS_chargeTotal_le` adds the root's scatter
column (`topScatterCost_le`, at the guard); at `δ = ε/(2(ℓ+2))` the
root exponent is `1+ε`. `exists_mcChargeMS_chargeTotal_le` is the
headline: on a nowhere dense class, for the priced routine
`timedGreedyRoutine (3R)` and the concrete cover family
`coverCF` (F5's `coverC` at the derived degree — the same
`(coverProg, coverC)` pair `coverProg_slot` fills the slot with),
constants fixed before the graph,

    chargeTotal (mcChargeMS …) ≤ κ·(‖G‖+1)^{1+ε} on members of C,

and `exists_mcChargeMS_T` is E13's item (e): `∃ c' T`,
`T x ≤ c'·(|x|+1)^{1+ε}` and the root budget total `≤ T x` on every
CSR encoding of a member (`graphWeight_add_three_le_length`'s
direction), at the campaign setup `headlineSetup C hC φ` — F7
multiplies by the machine's `L.const`.
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Refine
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ColoringNumbers
open Lax3Proofs.Driver
open Lax3Proofs.CoverEdgeSum

variable {L n₀ : ℕ}

/-! ## The total: ten named currencies, one ℕ -/

/-- The currencies the program family spends: the cover slot's two, the
frame's seven, the root evaluation's one. Every charge vector in this
file (and in `ProgFrame`/`ProgDriver`/`ProgCover`, with `coverC` in the
slot) is a sum of `ACost.cost` entries at these keys —
`mcChargeMS_toFun_eq_zero` below makes that honesty a theorem. -/
def progKeys : List String :=
  ["cover.order", "cover.sweep", "frame.restrict", "frame.supports",
   "frame.profiles", "frame.isolate", "frame.scatter", "frame.readback",
   "frame.bot", "top.scatter"]

/-- **The fixed total**: an `ACost String ℕ` ledger summed over the ten
program currencies — the `chargeB0_total`/`coverC_total` discipline, one
carrier (`ℕ`), cast to `ℝ` exactly once at the comparison. -/
def chargeTotal (v : ACost String ℕ) : ℕ := (progKeys.map v.toFun).sum

theorem chargeTotal_add (a b : ACost String ℕ) :
    chargeTotal (a + b) = chargeTotal a + chargeTotal b := by
  simp [chargeTotal, progKeys]

@[simp] theorem chargeTotal_zero : chargeTotal 0 = 0 := by
  simp [chargeTotal, progKeys]

/-- The total of one named charge at a program currency is the charge. -/
theorem chargeTotal_cost {k : String} (hk : k ∈ progKeys) (n : ℕ) :
    chargeTotal (ACost.cost k n) = n := by
  simp only [progKeys] at hk
  fin_cases hk <;> simp [chargeTotal, progKeys, ACost.toFun_cost]

theorem chargeTotal_listSum (l : List (ACost String ℕ)) :
    chargeTotal l.sum = (l.map chargeTotal).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.sum_cons, chargeTotal_add, ih, List.map_cons, List.sum_cons]

/-- A vector supported on the program currencies is its total: off
`progKeys` it vanishes. (Used through `mcChargeMS_toFun_eq_zero`.) -/
theorem chargeTotal_cost_notMem {k : String} (hk : k ∉ progKeys) (n : ℕ)
    (m : String) (hm : m ∈ progKeys) : (ACost.cost k n).toFun m = 0 :=
  ACost.toFun_cost_ne (fun h => hk (h ▸ hm)) n

/-- The `ECost` total over the same ten currencies. -/
def totalE (v : ECost) : ℕ∞ := (progKeys.map v.toFun).sum

/-- **The `ECost` bridge**: the ten-currency total of a lifted budget is
the `ℕ∞`-cast of `chargeTotal` — the seam at which F7 reads the number
off the NREST-level budget. -/
theorem totalE_liftACost (v : ACost String ℕ) :
    totalE (liftACost v) = (chargeTotal v : ℕ∞) := by
  rw [totalE, chargeTotal, Nat.cast_list_sum, List.map_map]
  rfl

/-! ## Route (b): the MS-routed charges

`frameCharge` hardcodes `Impl.profilesCharge` (the iterated route) in
`profilesC`, so the honest budget is a variant with exactly that column
swapped to F3b's `Impl.profilesChargeMS` — `(mb + L)` BFS calls, §6.3's
count. Everything else is the landed vector, entry by entry
(`driverChargeMS_toFun_eq`). -/

open Classical in
/-- The multi-source profile charge of one centre: `profilesC` with
`Impl.profilesCharge` replaced by `Impl.profilesChargeMS` at the same
node data — `S.width` batch calls plus one virtual-source call per
colour class of `childColR` (`relPal (S.pal j)` classes). -/
noncomputable def profilesCMS (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ACost String ℕ :=
  ACost.cost "frame.profiles"
    (Impl.profilesChargeMS (preG S A π u) S.width (relPal (S.pal j)) S.R)

/-- `centreCharge` with the profiles column at the MS route; the other
five summands are verbatim `ProgFrame.centreCharge`'s. -/
noncomputable def centreChargeMS (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ACost String ℕ :=
  restrictC S j A ℓp π u + (supportsC S j A π u + (profilesCMS S j A π u
    + (isolateC S j A htab π u + (nxC (childArena S A π u)
      + ACost.cost "frame.scatter"
          (scatterCost S j A π u (nx (childArena S A π u)))))))

open Classical in
/-- `frameCharge` with the profiles column at the MS route. -/
noncomputable def frameChargeMS (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (covC : ACost String ℕ) (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ) :
    ACost String ℕ :=
  if A.G = ⊥ then botC S j A
  else covC + (allocC A
    + ((((List.finRange A.N).map
          (centreChargeMS S j A ℓp htab nx nxC ((ord A.N A.G).order))).sum)
        + readC S j A))

/-- `driverCharge` with every level's profiles column at the MS route —
the same level recursion, wired to itself one level down. -/
noncomputable def driverChargeMS (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ) :
    (k : ℕ) → (j : ℕ) → (A : Arena (S.pal j) n₀) → ACost String ℕ
  | 0, j, A => botC S j A
  | k + 1, j, A =>
    frameChargeMS S ord j A (ℓp j) (htabF j A)
      (fun B => Unroll.unrollAux S ord k (j + 1) B)
      (covC j A)
      (fun B => driverChargeMS S ord ℓp htabF covC k (j + 1) B)

/-- `mcCharge` with the MS-routed driver charge: the root driver's
vector plus the root evaluation's `"top.scatter"` column, priced at the
delivered table exactly as `ProgDriver.mcCharge` prices it. -/
noncomputable def mcChargeMS (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L) : ACost String ℕ :=
  driverChargeMS S ord ℓp htabF covC S.depth 0 (rootArena G col)
    + ACost.cost "top.scatter"
        (topScatterCost S G col (tables S ord 0 (rootArena G col)))

/-! ### The lemma `frameCharge`-users need: one column moved, nine kept

On every currency except `"frame.profiles"` the MS vectors are the
landed vectors, entry by entry — so every ledger identity F3/F4 proved
about `frameCharge`/`mcCharge` (the restrict account, slot hygiene, the
scatter and readback columns) holds of the MS budget verbatim, and a
program whose profile stage is rebudgeted at `profilesCMS` changes
exactly one column of its advertised budget. -/

section UsersLemma

variable (S : Setup L) (ord : CoverSpec.OrderingRoutine) (j : ℕ)
  (A : Arena (S.pal j) n₀) (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
  (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)

theorem centreChargeMS_toFun_eq {k : String} (hk : k ≠ "frame.profiles")
    {nxC' nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ}
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (hnx : (nxC' (childArena S A π u)).toFun k
      = (nxC (childArena S A π u)).toFun k) :
    (centreChargeMS S j A ℓp htab nx nxC' π u).toFun k
      = (centreCharge S j A ℓp htab nx nxC π u).toFun k := by
  simp [centreChargeMS, centreCharge, profilesCMS, profilesC,
    ACost.toFun_add, ACost.toFun_cost_ne hk, hnx]

theorem frameChargeMS_toFun_eq {k : String} (hk : k ≠ "frame.profiles")
    {covC : ACost String ℕ}
    {nxC' nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ}
    (hnx : ∀ B, (nxC' B).toFun k = (nxC B).toFun k) :
    (frameChargeMS S ord j A ℓp htab nx covC nxC').toFun k
      = (frameCharge S ord j A ℓp htab nx covC nxC).toFun k := by
  rw [frameChargeMS, frameCharge]
  by_cases hbot : A.G = ⊥
  · rw [if_pos hbot, if_pos hbot]
  · rw [if_neg hbot, if_neg hbot]
    simp only [ACost.toFun_add, toFun_listSum, List.map_map]
    congr 2
    refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
    exact centreChargeMS_toFun_eq S j A ℓp htab nx hk _ u (hnx _)

/-- **The driver's MS budget is the landed budget off the profiles
column** — every non-`"frame.profiles"` ledger entry of
`driverChargeMS` equals `driverCharge`'s, at every level. -/
theorem driverChargeMS_toFun_eq (ℓpF : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓpF j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    {k : String} (hk : k ≠ "frame.profiles") :
    ∀ (fuel j : ℕ) (A : Arena (S.pal j) n₀),
      (driverChargeMS S ord ℓpF htabF covC fuel j A).toFun k
        = (driverCharge S ord ℓpF htabF covC fuel j A).toFun k := by
  intro fuel
  induction fuel with
  | zero => intro j A; rfl
  | succ fuel ih =>
    intro j A
    rw [driverChargeMS, driverCharge]
    exact frameChargeMS_toFun_eq S ord j A (ℓpF j) (htabF j A) _ hk
      (fun B => ih (j + 1) B)

/-- The root budget's users' lemma: `mcChargeMS` is `mcCharge` on every
currency except `"frame.profiles"` — including the `"top.scatter"`
column, which is identical. -/
theorem mcChargeMS_toFun_eq (ℓpF : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓpF j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L)
    {k : String} (hk : k ≠ "frame.profiles") :
    (mcChargeMS S ord ℓpF htabF covC G col).toFun k
      = (mcCharge S ord ℓpF htabF covC G col).toFun k := by
  rw [mcChargeMS, mcCharge]
  simp only [ACost.toFun_add]
  rw [driverChargeMS_toFun_eq S ord ℓpF htabF covC hk]

end UsersLemma

end Lax3Proofs.Prog
