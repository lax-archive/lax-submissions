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
open Lax62Proofs.Refine
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ColoringNumbers
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun
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
  simp only [chargeTotal, progKeys, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, ACost.toFun_add]
  omega

@[simp] theorem chargeTotal_zero : chargeTotal 0 = 0 := by
  simp [chargeTotal, progKeys]

/-- The total of one named charge at a program currency is the charge. -/
theorem chargeTotal_cost {k : String} (hk : k ∈ progKeys) (n : ℕ) :
    chargeTotal (ACost.cost k n) = n := by
  simp only [progKeys] at hk
  fin_cases hk <;> simp [chargeTotal, progKeys]

theorem chargeTotal_listSum (l : List (ACost String ℕ)) :
    chargeTotal l.sum = (l.map chargeTotal).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.sum_cons, chargeTotal_add, ih, List.map_cons, List.sum_cons]

/-- A vector supported on the program currencies is its total: off
`progKeys` it vanishes. (Used through `mcChargeMS_toFun_eq_zero`.) -/
theorem chargeTotal_cost_notMem {k : String} (hk : k ∉ progKeys) (n : ℕ)
    (m : String) (hm : m ∈ progKeys) : (ACost.cost k n).toFun m = 0 :=
  ACost.toFun_cost_ne (by rintro rfl; exact hk hm) n

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
    have hmap : ∀ u : Fin A.N,
        ((fun x => ACost.toFun x k)
          ∘ centreChargeMS S j A ℓp htab nx nxC' ((ord A.N A.G).order)) u
        = ((fun x => ACost.toFun x k)
          ∘ centreCharge S j A ℓp htab nx nxC ((ord A.N A.G).order)) u :=
      fun u => centreChargeMS_toFun_eq S j A ℓp htab nx hk _ u (hnx _)
    rw [List.map_congr_left fun u _ => hmap u]

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

/-! ## The per-currency closed forms of the components -/

section ComponentTotals

variable (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)

open Classical in
@[simp] theorem chargeTotal_restrictC (ℓp : ℕ) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    chargeTotal (restrictC S j A ℓp π u)
      = Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u) :=
  chargeTotal_cost (by decide) _

open Classical in
@[simp] theorem chargeTotal_supportsC (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    chargeTotal (supportsC S j A π u)
      = (2 * Impl.gsize (preG S A π u) + S.R + 2)
        + (S.R + 2) * (2 * Impl.gsize (preG S A π u)) :=
  chargeTotal_cost (by decide) _

open Classical in
@[simp] theorem chargeTotal_profilesCMS (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    chargeTotal (profilesCMS S j A π u)
      = Impl.profilesChargeMS (preG S A π u) S.width (relPal (S.pal j)) S.R :=
  chargeTotal_cost (by decide) _

open Classical in
@[simp] theorem chargeTotal_isolateC {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    chargeTotal (isolateC S j A htab π u)
      = Impl.isolateCharge ((Impl.ofArena A htab).restrict (cluster S A π u)) :=
  chargeTotal_cost (by decide) _

@[simp] theorem chargeTotal_allocC : chargeTotal (allocC A) = A.N :=
  chargeTotal_cost (by decide) _

@[simp] theorem chargeTotal_readC :
    chargeTotal (readC S j A) = A.N * (1 + (F S j).length) :=
  chargeTotal_cost (by decide) _

@[simp] theorem chargeTotal_botC :
    chargeTotal (botC S j A) = (1 + (F S j).length) * weight A :=
  chargeTotal_cost (by decide) _

end ComponentTotals

open Classical in
/-- The cover slot's total, at F5's concrete vector: the ordering
phase's honest `chainCharge` (the routine's abstract `steps` field,
`coverC_order_eq_steps` — the vacuity note's answer) plus the sweep's
account. -/
theorem chargeTotal_coverC (m : ℕ) (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    chargeTotal (coverC m G rc R D)
      = chainCharge G R
        + Impl.sweepCharge G ((timedGreedyRoutine R) m G).order rc D := by
  rw [coverC, chargeTotal_add, chargeTotal_cost (by decide),
    chargeTotal_cost (by decide)]

open Classical in
theorem chargeTotal_centreChargeMS (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u)
      = Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u)
        + (((2 * Impl.gsize (preG S A π u) + S.R + 2)
            + (S.R + 2) * (2 * Impl.gsize (preG S A π u)))
          + (Impl.profilesChargeMS (preG S A π u) S.width (relPal (S.pal j)) S.R
            + (Impl.isolateCharge ((Impl.ofArena A htab).restrict (cluster S A π u))
              + (chargeTotal (nxC (childArena S A π u))
                + scatterCost S j A π u (nx (childArena S A π u)))))) := by
  rw [centreChargeMS, chargeTotal_add, chargeTotal_add, chargeTotal_add,
    chargeTotal_add, chargeTotal_add, chargeTotal_restrictC, chargeTotal_supportsC,
    chargeTotal_profilesCMS, chargeTotal_isolateC, chargeTotal_cost (by decide)]

/-! ## The geometry: `B₀` weighs no more than its cluster -/

/-- The edge count of `preG` — `B₀` before isolation — is at most the
cluster's internal edge count: the compaction embeds its edge set into
`internalEdgeSet` (the `weight_childArena_le` argument, without the
isolation step). -/
theorem edgeSet_ncard_preG_le (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    (preG S A π u).edgeSet.ncard
      ≤ (internalEdgeSet A.G (cluster S A π u)).ncard := by
  have hinj : Function.Injective
      (Sym2.map (fun a => ((childEquiv S A π u) a : Fin A.N))) :=
    Sym2.map.injective fun a b hab =>
      (childEquiv S A π u).injective (Subtype.ext hab)
  have himg : Sym2.map (fun a => ((childEquiv S A π u) a : Fin A.N)) ''
      (preG S A π u).edgeSet ⊆ internalEdgeSet A.G (cluster S A π u) := by
    rintro e ⟨e', he', rfl⟩
    induction e' with
    | _ a b =>
      have hadj : A.G.Adj ((childEquiv S A π u) a : Fin A.N)
          ((childEquiv S A π u) b : Fin A.N) := he'
      rw [Sym2.map_mk]
      refine ⟨hadj, ?_⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact ((childEquiv S A π u) a).2
      · exact ((childEquiv S A π u) b).2
  calc (preG S A π u).edgeSet.ncard
      = (Sym2.map (fun a => ((childEquiv S A π u) a : Fin A.N)) ''
          (preG S A π u).edgeSet).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (internalEdgeSet A.G (cluster S A π u)).ncard :=
        Set.ncard_le_ncard himg (Set.toFinite _)

/-- The Finset/ncard bridge for edge counts (instance-free right side). -/
theorem edgeFinset_card_eq_ncard {m : ℕ} (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj] : H.edgeFinset.card = H.edgeSet.ncard := by
  rw [← SimpleGraph.coe_edgeFinset H, Set.ncard_coe_finset]

open Classical in
/-- **`‖B₀ᵤ‖ ≤ clusterWeight`**: the profile/supports arena of one
centre — carrier the cluster, edges before isolation — weighs no more
than the cluster's weight, so the per-centre `gsize`-priced columns sum
by `CoverEdgeSum.sum_clusterWeight_le_rpow`. -/
theorem gsize_preG_le (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    Impl.gsize (preG S A π u) ≤ clusterWeight A.G (cluster S A π u) := by
  show childN S A π u + (preG S A π u).edgeFinset.card
    ≤ (cluster S A π u).ncard + (internalEdgeSet A.G (cluster S A π u)).ncard
  rw [edgeFinset_card_eq_ncard]
  exact Nat.add_le_add le_rfl (edgeSet_ncard_preG_le S A π u)

/-! ## The per-node comparison (deliverable 1) -/

/-- **The per-level node constant** — a number of the schedule alone
(level `j`, history rounds `ℓp`), fixed before any graph is read. It
collects: the restrict column's per-vertex multiplier
(`S.pal j + ℓp(2R+1) + 2`), the per-`clusterWeight` coefficients of the
supports, profiles (MS), isolate and scatter columns, their per-vertex
constants, the readback, and the node allocation. -/
noncomputable def nodeConst (S : Setup L) (j ℓp : ℕ) : ℕ :=
  (S.pal j + ℓp * (2 * S.R + 1) + 2)
    + (2 * (S.R + 3) + 6 * (S.width + relPal (S.pal j)) * (S.R + 1) + 2
        + 2 * scatterBudget S j)
    + ((S.R + 2) + 6 * (S.width + relPal (S.pal j)) * (S.R + 1))
    + (F S j).length + 4

open Classical in
/-- **F3c's per-node comparison** (`dcost_node_le`-shaped, at the node
aggregate). At a node with an edge, under

* the cover-degree hypothesis in the landed fibre form (the shape
  `cluster_fibre_eq` converts `exists_wreach_degree_timedGreedyRoutine`
  into), and
* a `f·N^{1+2δ}` bound on the cover slot's total (what
  `exists_coverCharge_le` supplies for F5's `coverC` at the honest
  `timedGreedyRoutine` steps),

the frame's whole MS-routed ledger total is within the abstract node
envelope plus the recursion slots' own totals:

    total ≤ (f + (c+1)·nodeConst)·‖A‖^{1+2δ} + Σ_u total (nxC childᵤ).

The `c·Σ_u‖child‖` middle term of `dcost_node_le`'s shape is folded
into the envelope by the same mass clause
(`sum_clusterWeight_le_rpow`); the sum over the slots runs over **all**
centres — empty clusters' subtrees cost `0`
(`driverChargeMS_chargeTotal_of_bot`). -/
theorem frameChargeMS_chargeTotal_le (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (covC : ACost String ℕ) (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    {c f δ : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) (hδ : 0 ≤ δ)
    (hbot : ¬ A.G = ⊥) (hW : 1 ≤ weight A)
    (hcov : (chargeTotal covC : ℝ) ≤ f * (A.N : ℝ) ^ (1 + 2 * δ))
    (hdeg : ∀ v : Fin A.N,
      {u : Fin A.N | v ∈ cluster S A ((ord A.N A.G).order) u}.ncard
        ≤ ⌈c * (A.N : ℝ) ^ δ⌉₊) :
    (chargeTotal (frameChargeMS S ord j A ℓp htab nx covC nxC) : ℝ)
      ≤ (f + (c + 1) * (nodeConst S j ℓp : ℝ)) * (weight A : ℝ) ^ (1 + 2 * δ)
        + ∑ u : Fin A.N,
            (chargeTotal (nxC (childArena S A ((ord A.N A.G).order) u)) : ℝ) := by
  classical
  set π : Equiv.Perm (Fin A.N) := (ord A.N A.G).order with hπdef
  set d : ℕ := ⌈c * (A.N : ℝ) ^ δ⌉₊ with hddef
  -- abbreviations for the schedule constants of this level
  set Kr : ℕ := S.pal j + ℓp * (2 * S.R + 1) + 2 with hKrdef
  set Kc : ℕ := 2 * (S.R + 3) + 6 * (S.width + relPal (S.pal j)) * (S.R + 1) + 2
    + 2 * scatterBudget S j with hKcdef
  set Kq : ℕ := (S.R + 2) + 6 * (S.width + relPal (S.pal j)) * (S.R + 1) with hKqdef
  -- §1 the ℕ ledger, column by column
  have htot : chargeTotal (frameChargeMS S ord j A ℓp htab nx covC nxC)
      = chargeTotal covC + (A.N
        + ((((List.finRange A.N).map fun u =>
              chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u)).sum)
          + A.N * (1 + (F S j).length))) := by
    rw [frameChargeMS, if_neg hbot, chargeTotal_add, chargeTotal_add,
      chargeTotal_add, chargeTotal_listSum, List.map_map, chargeTotal_allocC,
      chargeTotal_readC]
    rfl
  have hlist : ((List.finRange A.N).map fun u =>
        chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u)).sum
      = ∑ u : Fin A.N, chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u) :=
    (Fin.sum_univ_def _).symm
  -- §2 per-centre columns against the cluster weight
  have hsup : ∀ u : Fin A.N,
      (2 * Impl.gsize (preG S A π u) + S.R + 2)
        + (S.R + 2) * (2 * Impl.gsize (preG S A π u))
      ≤ 2 * (S.R + 3) * clusterWeight A.G (cluster S A π u) + (S.R + 2) := by
    intro u
    have hg := gsize_preG_le S A π u
    calc (2 * Impl.gsize (preG S A π u) + S.R + 2)
          + (S.R + 2) * (2 * Impl.gsize (preG S A π u))
        = 2 * (S.R + 3) * Impl.gsize (preG S A π u) + (S.R + 2) := by ring
      _ ≤ 2 * (S.R + 3) * clusterWeight A.G (cluster S A π u) + (S.R + 2) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hg) _
  have hpro : ∀ u : Fin A.N,
      Impl.profilesChargeMS (preG S A π u) S.width (relPal (S.pal j)) S.R
      ≤ 6 * (S.width + relPal (S.pal j)) * (S.R + 1)
          * clusterWeight A.G (cluster S A π u)
        + 6 * (S.width + relPal (S.pal j)) * (S.R + 1) := by
    intro u
    refine (Impl.profilesChargeMS_le _ _ _ _).trans ?_
    have hg := gsize_preG_le S A π u
    calc (S.width + relPal (S.pal j))
          * (6 * (S.R + 1) * (Impl.gsize (preG S A π u) + 1))
        = 6 * (S.width + relPal (S.pal j)) * (S.R + 1) * Impl.gsize (preG S A π u)
          + 6 * (S.width + relPal (S.pal j)) * (S.R + 1) := by ring
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ hg) _
  have hiso : ∀ u : Fin A.N,
      Impl.isolateCharge ((Impl.ofArena A htab).restrict (cluster S A π u))
      ≤ 2 * clusterWeight A.G (cluster S A π u) := by
    intro u
    rw [Impl.isolateCharge_eq, edgeFinset_card_eq_ncard]
    have h1 : ((Impl.ofArena A htab).restrict (cluster S A π u)).G.edgeSet.ncard
        ≤ (internalEdgeSet A.G (cluster S A π u)).ncard :=
      edgeSet_ncard_preG_le S A π u
    have h2 : ((Impl.ofArena A htab).restrict (cluster S A π u)).N
        = (cluster S A π u).ncard := rfl
    have hcw : clusterWeight A.G (cluster S A π u)
        = (cluster S A π u).ncard + (internalEdgeSet A.G (cluster S A π u)).ncard :=
      rfl
    omega
  have hsc : ∀ u : Fin A.N,
      scatterCost S j A π u (nx (childArena S A π u))
      ≤ 2 * scatterBudget S j * clusterWeight A.G (cluster S A π u) := by
    intro u
    refine (scatterCost_le S j A π u _).trans ?_
    have h := weight_childArena_le S A π u
    calc scatterBudget S j * (2 * weight (childArena S A π u))
        ≤ scatterBudget S j * (2 * clusterWeight A.G (cluster S A π u)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
      _ = 2 * scatterBudget S j * clusterWeight A.G (cluster S A π u) := by ring
  have hcen : ∀ u : Fin A.N,
      chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u)
      ≤ Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u)
        + (Kc * clusterWeight A.G (cluster S A π u) + Kq)
        + chargeTotal (nxC (childArena S A π u)) := by
    intro u
    rw [chargeTotal_centreChargeMS]
    refine le_trans (Nat.add_le_add le_rfl (Nat.add_le_add (hsup u)
      (Nat.add_le_add (hpro u) (Nat.add_le_add (hiso u)
        (Nat.add_le_add le_rfl (hsc u)))))) ?_
    apply le_of_eq
    rw [hKcdef, hKqdef]
    ring
  -- §3 the node aggregates, in ℕ
  have hccN : ∑ u : Fin A.N, Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u)
      ≤ d * (2 * A.G.edgeFinset.card) + A.N * d * Kr := by
    rw [hKrdef]
    exact Impl.sum_childCharge_le A.G (S.pal j) ℓp S.R (fun u => cluster S A π u)
      d hdeg
  have hsumN : ∑ u : Fin A.N, chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u)
      ≤ (d * (2 * A.G.edgeFinset.card) + A.N * d * Kr)
        + (Kc * (∑ u : Fin A.N, clusterWeight A.G (cluster S A π u)) + A.N * Kq)
        + ∑ u : Fin A.N, chargeTotal (nxC (childArena S A π u)) := by
    calc ∑ u : Fin A.N, chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u)
        ≤ ∑ u : Fin A.N,
            (Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u)
              + (Kc * clusterWeight A.G (cluster S A π u) + Kq)
              + chargeTotal (nxC (childArena S A π u))) :=
          Finset.sum_le_sum fun u _ => hcen u
      _ = (∑ u : Fin A.N, Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u))
          + (Kc * (∑ u : Fin A.N, clusterWeight A.G (cluster S A π u)) + A.N * Kq)
          + ∑ u : Fin A.N, chargeTotal (nxC (childArena S A π u)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul, mul_comm A.N Kq]
      _ ≤ _ := by
          exact Nat.add_le_add (Nat.add_le_add hccN le_rfl) le_rfl
  -- §4 cast once, then the ℝ endgame
  set W : ℝ := (weight A : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW1
  set Wp : ℝ := W ^ ((1 : ℝ) + 2 * δ) with hWpdef
  have hWpnn : (0 : ℝ) ≤ Wp := Real.rpow_nonneg hWpos.le _
  have hWWp : W ≤ Wp := by
    rw [hWpdef]
    calc W = W ^ (1 : ℝ) := (Real.rpow_one W).symm
      _ ≤ W ^ ((1 : ℝ) + 2 * δ) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hNW : (A.N : ℝ) ≤ W := by
    rw [hWdef]
    exact_mod_cast Nat.le_add_right A.N (A.G.edgeSet.ncard)
  have hMW : (A.G.edgeFinset.card : ℝ) ≤ W := by
    rw [hWdef, edgeFinset_card_eq_ncard]
    exact_mod_cast Nat.le_add_left (A.G.edgeSet.ncard) A.N
  have hone_le : (1 : ℝ) ≤ W ^ δ := by
    rw [hWdef]
    exact one_le_rpow (by exact_mod_cast hW) hδ
  have hdC : (d : ℝ) ≤ (c + 1) * W ^ δ := by
    rw [hddef]
    have hceil : ((⌈c * (A.N : ℝ) ^ δ⌉₊ : ℕ) : ℝ) ≤ c * (A.N : ℝ) ^ δ + 1 :=
      (Nat.ceil_lt_add_one
        (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg _) δ))).le
    refine hceil.trans ?_
    have hNe : (A.N : ℝ) ^ δ ≤ W ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hNW hδ
    nlinarith [hone_le, hNe, hc]
  have hsplit : W ^ ((1 : ℝ) + δ) = W * W ^ δ := by
    rw [Real.rpow_add hWpos, Real.rpow_one]
  have hWdWp : W ^ ((1 : ℝ) + δ) ≤ Wp := by
    rw [hWpdef]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hcwR : ((∑ u : Fin A.N, clusterWeight A.G (cluster S A π u) : ℕ) : ℝ)
      ≤ (c + 1) * W ^ ((1 : ℝ) + δ) := by
    rw [hWdef]
    exact sum_clusterWeight_le_rpow A.G (fun u => cluster S A π u) c δ hc hδ hW hdeg
  -- the seven priced columns
  have hT1 : (chargeTotal covC : ℝ) ≤ f * Wp := by
    refine hcov.trans ?_
    rw [hWpdef]
    refine mul_le_mul_of_nonneg_left ?_ hf
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNW (by linarith)
  have hT2 : (A.N : ℝ) ≤ Wp := hNW.trans hWWp
  have hT3 : (d : ℝ) * (2 * (A.G.edgeFinset.card : ℝ)) ≤ 2 * (c + 1) * Wp := by
    have h1 : (d : ℝ) * (2 * (A.G.edgeFinset.card : ℝ))
        ≤ ((c + 1) * W ^ δ) * (2 * W) := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
      have hM0 : (0 : ℝ) ≤ 2 * (A.G.edgeFinset.card : ℝ) := by positivity
      refine mul_le_mul hdC (by linarith) hM0 (by positivity)
    refine h1.trans ?_
    calc ((c + 1) * W ^ δ) * (2 * W) = 2 * (c + 1) * (W * W ^ δ) := by ring
      _ = 2 * (c + 1) * W ^ ((1 : ℝ) + δ) := by rw [hsplit]
      _ ≤ 2 * (c + 1) * Wp := by
          refine mul_le_mul_of_nonneg_left hWdWp (by linarith)
  have hT4 : (A.N : ℝ) * (d : ℝ) * (Kr : ℝ) ≤ (Kr : ℝ) * (c + 1) * Wp := by
    have h1 : (A.N : ℝ) * (d : ℝ) ≤ W * ((c + 1) * W ^ δ) :=
      mul_le_mul hNW hdC (Nat.cast_nonneg _) hWpos.le
    have h2 : W * ((c + 1) * W ^ δ) = (c + 1) * W ^ ((1 : ℝ) + δ) := by
      rw [hsplit]; ring
    have h3 : (A.N : ℝ) * (d : ℝ) ≤ (c + 1) * Wp := by
      refine (h1.trans_eq h2).trans ?_
      exact mul_le_mul_of_nonneg_left hWdWp (by linarith)
    calc (A.N : ℝ) * (d : ℝ) * (Kr : ℝ) ≤ ((c + 1) * Wp) * (Kr : ℝ) :=
          mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
      _ = (Kr : ℝ) * (c + 1) * Wp := by ring
  have hT5 : (Kc : ℝ) * ((∑ u : Fin A.N, clusterWeight A.G (cluster S A π u) : ℕ) : ℝ)
      ≤ (Kc : ℝ) * (c + 1) * Wp := by
    calc (Kc : ℝ) * ((∑ u : Fin A.N, clusterWeight A.G (cluster S A π u) : ℕ) : ℝ)
        ≤ (Kc : ℝ) * ((c + 1) * W ^ ((1 : ℝ) + δ)) :=
          mul_le_mul_of_nonneg_left hcwR (Nat.cast_nonneg _)
      _ ≤ (Kc : ℝ) * ((c + 1) * Wp) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left hWdWp (by linarith)
      _ = (Kc : ℝ) * (c + 1) * Wp := by ring
  have hT6 : (A.N : ℝ) * (Kq : ℝ) ≤ (Kq : ℝ) * Wp := by
    calc (A.N : ℝ) * (Kq : ℝ) ≤ Wp * (Kq : ℝ) :=
          mul_le_mul_of_nonneg_right hT2 (Nat.cast_nonneg _)
      _ = (Kq : ℝ) * Wp := by ring
  have hT7 : (A.N : ℝ) * (1 + ((F S j).length : ℝ))
      ≤ (1 + ((F S j).length : ℝ)) * Wp := by
    calc (A.N : ℝ) * (1 + ((F S j).length : ℝ))
        ≤ Wp * (1 + ((F S j).length : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hT2 (by positivity)
      _ = (1 + ((F S j).length : ℝ)) * Wp := by ring
  -- the coefficient consolidation into the named constant
  have hcoef : f * Wp + Wp + 2 * (c + 1) * Wp + (Kr : ℝ) * (c + 1) * Wp
      + (Kc : ℝ) * (c + 1) * Wp + (Kq : ℝ) * Wp + (1 + ((F S j).length : ℝ)) * Wp
      ≤ (f + (c + 1) * (nodeConst S j ℓp : ℝ)) * Wp := by
    have hnc : (nodeConst S j ℓp : ℝ)
        = (Kr : ℝ) + (Kc : ℝ) + (Kq : ℝ) + ((F S j).length : ℝ) + 4 := by
      unfold nodeConst
      rw [hKrdef, hKcdef, hKqdef]
      push_cast
      ring
    have hco : f + 1 + 2 * (c + 1) + (Kr : ℝ) * (c + 1) + (Kc : ℝ) * (c + 1)
        + (Kq : ℝ) + (1 + ((F S j).length : ℝ))
        ≤ f + (c + 1) * (nodeConst S j ℓp : ℝ) := by
      rw [hnc]
      nlinarith [hc, Nat.cast_nonneg (α := ℝ) Kr, Nat.cast_nonneg (α := ℝ) Kc,
        Nat.cast_nonneg (α := ℝ) Kq, Nat.cast_nonneg (α := ℝ) (F S j).length]
    calc f * Wp + Wp + 2 * (c + 1) * Wp + (Kr : ℝ) * (c + 1) * Wp
        + (Kc : ℝ) * (c + 1) * Wp + (Kq : ℝ) * Wp + (1 + ((F S j).length : ℝ)) * Wp
        = (f + 1 + 2 * (c + 1) + (Kr : ℝ) * (c + 1) + (Kc : ℝ) * (c + 1)
            + (Kq : ℝ) + (1 + ((F S j).length : ℝ))) * Wp := by ring
      _ ≤ (f + (c + 1) * (nodeConst S j ℓp : ℝ)) * Wp :=
          mul_le_mul_of_nonneg_right hco hWpnn
  -- assemble
  have hcast : (chargeTotal (frameChargeMS S ord j A ℓp htab nx covC nxC) : ℝ)
      = (chargeTotal covC : ℝ) + ((A.N : ℝ)
        + ((∑ u : Fin A.N,
              (chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u) : ℝ))
          + (A.N : ℝ) * (1 + ((F S j).length : ℝ)))) := by
    rw [htot, hlist]
    push_cast
    ring
  have hsumR : ∑ u : Fin A.N,
        (chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u) : ℝ)
      ≤ ((d : ℝ) * (2 * (A.G.edgeFinset.card : ℝ)) + (A.N : ℝ) * (d : ℝ) * (Kr : ℝ))
        + ((Kc : ℝ) * ((∑ u : Fin A.N, clusterWeight A.G (cluster S A π u) : ℕ) : ℝ)
          + (A.N : ℝ) * (Kq : ℝ))
        + ∑ u : Fin A.N, (chargeTotal (nxC (childArena S A π u)) : ℝ) := by
    have h := hsumN
    have hcast2 : ((∑ u : Fin A.N,
          chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u) : ℕ) : ℝ)
        ≤ (((d * (2 * A.G.edgeFinset.card) + A.N * d * Kr)
            + (Kc * (∑ u : Fin A.N, clusterWeight A.G (cluster S A π u)) + A.N * Kq)
            + ∑ u : Fin A.N, chargeTotal (nxC (childArena S A π u)) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hcast2
    convert hcast2 using 2
    push_cast
    ring
  rw [hcast]
  have hmid : (chargeTotal covC : ℝ) + ((A.N : ℝ)
      + ((∑ u : Fin A.N,
            (chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u) : ℝ))
        + (A.N : ℝ) * (1 + ((F S j).length : ℝ))))
      ≤ f * Wp + Wp + 2 * (c + 1) * Wp + (Kr : ℝ) * (c + 1) * Wp
        + (Kc : ℝ) * (c + 1) * Wp + (Kq : ℝ) * Wp + (1 + ((F S j).length : ℝ)) * Wp
        + ∑ u : Fin A.N, (chargeTotal (nxC (childArena S A π u)) : ℝ) := by
    linarith [hsumR, hT1, hT2, hT3, hT4, hT5, hT6, hT7]
  refine hmid.trans ?_
  linarith [hcoef]

/-! ## The level lift (deliverable 2) -/

/-- An arena with no vertices is edgeless. -/
theorem arena_bot_of_N_eq_zero {Λ : ℕ} (A : Arena Λ n₀) (hN : A.N = 0) :
    A.G = ⊥ := by
  ext a b
  exact absurd a.pos (by omega)

/-- An arena with no vertices weighs nothing. -/
theorem weight_eq_zero_of_N_eq_zero {Λ : ℕ} (A : Arena Λ n₀) (hN : A.N = 0) :
    weight A = 0 := by
  have hbot := arena_bot_of_N_eq_zero A hN
  show A.N + A.G.edgeSet.ncard = 0
  rw [hbot, SimpleGraph.edgeSet_bot, Set.ncard_empty, hN]

/-- **Empty clusters cost nothing, at every fuel**: the subtree of an
empty child arena (both `driverChargeMS` branches immediately take the
leaf charge at weight `0`). This is what lets the per-node comparison
sum its slot terms over *all* centres while `dcostAux` skips the empty
ones. -/
theorem chargeTotal_driverChargeMS_of_N_eq_zero (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (fuel j : ℕ) (A : Arena (S.pal j) n₀) (hN : A.N = 0) :
    chargeTotal (driverChargeMS S ord ℓp htabF covC fuel j A) = 0 := by
  have hbot := arena_bot_of_N_eq_zero A hN
  have hw := weight_eq_zero_of_N_eq_zero A hN
  cases fuel with
  | zero => rw [driverChargeMS, chargeTotal_botC, hw, Nat.mul_zero]
  | succ fuel =>
    rw [driverChargeMS, frameChargeMS, if_pos hbot, chargeTotal_botC, hw,
      Nat.mul_zero]

/-- The leaf constant of the schedule, uniform over the run's depths. -/
noncomputable def botBound (S : Setup L) : ℕ :=
  (Finset.range (S.depth + 1)).sup (fun j => 1 + (F S j).length) + 1

theorem one_le_botBound (S : Setup L) : 1 ≤ botBound S := Nat.le_add_left 1 _

theorem bot_le_botBound (S : Setup L) {j : ℕ} (hj : j ≤ S.depth) :
    1 + (F S j).length ≤ botBound S := by
  have h : j ∈ Finset.range (S.depth + 1) := Finset.mem_range.mpr (by omega)
  exact (Finset.le_sup (f := fun j => 1 + (F S j).length) h).trans (Nat.le_succ _)

/-- The node constant of the schedule, uniform over the run's depths —
`DriverCost.chargeBound`'s mate for the program's ledger. -/
noncomputable def nodeConstBound (S : Setup L) (ℓp : ℕ → ℕ) : ℕ :=
  (Finset.range (S.depth + 1)).sup (fun j => nodeConst S j (ℓp j)) + 1

theorem nodeConst_le_nodeConstBound (S : Setup L) (ℓp : ℕ → ℕ) {j : ℕ}
    (hj : j ≤ S.depth) : nodeConst S j (ℓp j) ≤ nodeConstBound S ℓp := by
  have h : j ∈ Finset.range (S.depth + 1) := Finset.mem_range.mpr (by omega)
  exact (Finset.le_sup (f := fun j => nodeConst S j (ℓp j)) h).trans (Nat.le_succ _)

/-- **The program's recurrence constant** — `DriverCost.KD`'s mate:
`KP = f + (c+1)·nodeConstBound + (c+1) + botBound`, a function of the
schedule, the history-round profile `ℓp`, the cover-degree constant `c`
and the cover-time constant `f` alone — fixed before any graph. -/
noncomputable def KP (S : Setup L) (ℓp : ℕ → ℕ) (c f : ℝ) : ℝ :=
  f + (c + 1) * (nodeConstBound S ℓp : ℝ) + (c + 1) + (botBound S : ℝ)

theorem one_le_KP (S : Setup L) (ℓp : ℕ → ℕ) {c f : ℝ} (hc : 0 ≤ c)
    (hf : 0 ≤ f) : 1 ≤ KP S ℓp c f := by
  have hbB : (1 : ℝ) ≤ (botBound S : ℝ) := by exact_mod_cast one_le_botBound S
  have h1 : (0 : ℝ) ≤ (c + 1) * (nodeConstBound S ℓp : ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  unfold KP
  linarith

open Classical in
/-- **The level lift** — `DriverCost.dcostAux_le`'s downward induction,
rerun on `chargeTotal ∘ driverChargeMS`: under the cover slot's total
bound and the routine's wreach-degree bound, both quantified over
subgraph copies of `Gn` (exactly the shape
`exists_coverCharge_le`/`exists_wreach_degree_timedGreedyRoutine`
supply on a class member), every node's whole MS-routed program budget
obeys

    total ≤ KP^{fuel+1} · ‖A‖^{1+(fuel+2)·2δ}.

Per level: the node step is `frameChargeMS_chargeTotal_le`, the
recursive column goes through the mass clause (`sum_child_weight_le`),
empty clusters cost `0`, and the per-level exponent increment is `2δ`
(the node envelope's own exponent). -/
theorem driverChargeMS_chargeTotal_le (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    {c f δ : ℝ} {nn : ℕ} {Gn : SimpleGraph (Fin nn)}
    (hc : 0 ≤ c) (hf : 0 ≤ f) (hδ : 0 ≤ δ)
    (hcov : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), A.G ⊑ Gn →
      (chargeTotal (covC j A) : ℝ) ≤ f * (A.N : ℝ) ^ (1 + 2 * δ))
    (hdeg : ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
      ∀ v : Fin m, (wreach G ((ord m G).order) (2 * S.R) v).ncard
        ≤ ⌈c * (m : ℝ) ^ δ⌉₊) :
    ∀ (fuel j : ℕ), j + fuel ≤ S.depth → ∀ (A : Arena (S.pal j) n₀),
      A.G ⊑ Gn → 1 ≤ weight A →
      (chargeTotal (driverChargeMS S ord ℓp htabF covC fuel j A) : ℝ)
        ≤ KP S ℓp c f ^ (fuel + 1)
          * (weight A : ℝ) ^ (1 + ((fuel : ℝ) + 2) * (2 * δ)) := by
  classical
  have hbB : (1 : ℝ) ≤ (botBound S : ℝ) := by exact_mod_cast one_le_botBound S
  have hncB : (0 : ℝ) ≤ (nodeConstBound S ℓp : ℝ) := Nat.cast_nonneg _
  have hK1 : (1 : ℝ) ≤ KP S ℓp c f := by
    have h1 : (0 : ℝ) ≤ (c + 1) * (nodeConstBound S ℓp : ℝ) :=
      mul_nonneg (by linarith) hncB
    unfold KP
    linarith
  have hKnn : (0 : ℝ) ≤ KP S ℓp c f := by linarith
  -- the leaf charge fits under every level's bound
  have hleaf : ∀ (jj : ℕ), jj ≤ S.depth → ∀ (B : Arena (S.pal jj) n₀),
      1 ≤ weight B → ∀ (kk : ℕ) (e : ℝ), 0 ≤ e →
      (chargeTotal (botC S jj B) : ℝ)
        ≤ KP S ℓp c f ^ (kk + 1) * (weight B : ℝ) ^ (1 + e) := by
    intro jj hjj B hWB kk e he
    rw [chargeTotal_botC]
    have hW1 : (1 : ℝ) ≤ (weight B : ℝ) := by exact_mod_cast hWB
    have hpow : (weight B : ℝ) ≤ (weight B : ℝ) ^ (1 + e) := by
      have h := Real.rpow_le_rpow_of_exponent_le hW1
        (by linarith : (1 : ℝ) ≤ 1 + e)
      rwa [Real.rpow_one] at h
    have hbb : (1 : ℝ) + ((F S jj).length : ℝ) ≤ KP S ℓp c f := by
      have h1 : (1 : ℝ) + ((F S jj).length : ℝ) ≤ (botBound S : ℝ) := by
        exact_mod_cast bot_le_botBound S hjj
      have h2 : (0 : ℝ) ≤ (c + 1) * (nodeConstBound S ℓp : ℝ) :=
        mul_nonneg (by linarith) hncB
      refine h1.trans ?_
      unfold KP
      linarith
    have hKk : KP S ℓp c f ≤ KP S ℓp c f ^ (kk + 1) :=
      le_self_pow₀ hK1 (Nat.succ_ne_zero kk)
    push_cast
    calc (1 + ((F S jj).length : ℝ)) * (weight B : ℝ)
        ≤ KP S ℓp c f * (weight B : ℝ) ^ (1 + e) :=
          mul_le_mul hbb hpow (Nat.cast_nonneg _) hKnn
      _ ≤ KP S ℓp c f ^ (kk + 1) * (weight B : ℝ) ^ (1 + e) :=
          mul_le_mul_of_nonneg_right hKk
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  intro fuel
  induction fuel with
  | zero =>
    intro j hj A hcopy hWA
    rw [driverChargeMS]
    exact hleaf j (by omega) A hWA 0 _ (by positivity)
  | succ fuel ih =>
    intro j hj A hcopy hWA
    rw [driverChargeMS]
    by_cases hbot : A.G = ⊥
    · rw [frameChargeMS, if_pos hbot]
      exact hleaf j (by omega) A hWA (fuel + 1) _ (by positivity)
    · have hdeg' : ∀ v : Fin A.N,
          {u : Fin A.N | v ∈ cluster S A ((ord A.N A.G).order) u}.ncard
            ≤ ⌈c * (A.N : ℝ) ^ δ⌉₊ := by
        intro v
        rw [cluster_fibre_eq]
        exact hdeg A.N A.G hcopy v
      have hnode := frameChargeMS_chargeTotal_le S ord j A (ℓp j) (htabF j A)
        (fun B => Unroll.unrollAux S ord fuel (j + 1) B) (covC j A)
        (fun B => driverChargeMS S ord ℓp htabF covC fuel (j + 1) B)
        hc hf hδ hbot hWA (hcov j A hcopy) hdeg'
      refine hnode.trans ?_
      set W : ℝ := (weight A : ℝ) with hWdef
      have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast hWA
      have hWpos : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW1
      set K : ℝ := KP S ℓp c f with hKdef
      have hKL : (0 : ℝ) ≤ K ^ (fuel + 1) := pow_nonneg hKnn _
      have hE : (0 : ℝ) ≤ W ^ (((fuel : ℝ) + 2) * (2 * δ)) :=
        Real.rpow_nonneg hWpos.le _
      -- each slot total, through the induction hypothesis / the zero
      have hterm : ∀ u : Fin A.N,
          (chargeTotal (driverChargeMS S ord ℓp htabF covC fuel (j + 1)
            (childArena S A ((ord A.N A.G).order) u)) : ℝ)
          ≤ (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * (2 * δ))) *
            (if (cluster S A ((ord A.N A.G).order) u).Nonempty
              then (weight (childArena S A ((ord A.N A.G).order) u) : ℝ)
              else 0) := by
        intro u
        by_cases hne : (cluster S A ((ord A.N A.G).order) u).Nonempty
        · rw [if_pos hne]
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
              (1 + ((fuel : ℝ) + 2) * (2 * δ))
              = (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) *
                (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
                  (((fuel : ℝ) + 2) * (2 * δ)) := by
            rw [Real.rpow_add hWupos, Real.rpow_one]
          have hmono : (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
              (((fuel : ℝ) + 2) * (2 * δ)) ≤ W ^ (((fuel : ℝ) + 2) * (2 * δ)) :=
            Real.rpow_le_rpow hWupos.le hWuW (by positivity)
          calc (chargeTotal (driverChargeMS S ord ℓp htabF covC fuel (j + 1)
                (childArena S A ((ord A.N A.G).order) u)) : ℝ)
              ≤ K ^ (fuel + 1) *
                (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
                  (1 + ((fuel : ℝ) + 2) * (2 * δ)) := hIH
            _ = K ^ (fuel + 1) *
                ((weight (childArena S A ((ord A.N A.G).order) u) : ℝ) *
                  (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) ^
                    (((fuel : ℝ) + 2) * (2 * δ))) := by rw [hsplit]
            _ ≤ K ^ (fuel + 1) *
                ((weight (childArena S A ((ord A.N A.G).order) u) : ℝ) *
                  W ^ (((fuel : ℝ) + 2) * (2 * δ))) := by
                refine mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)) hKL
            _ = (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * (2 * δ))) *
                (weight (childArena S A ((ord A.N A.G).order) u) : ℝ) := by ring
        · rw [if_neg hne, mul_zero]
          have hN0 : (childArena S A ((ord A.N A.G).order) u).N = 0 := by
            have hemp : cluster S A ((ord A.N A.G).order) u = ∅ :=
              Set.not_nonempty_iff_eq_empty.mp hne
            show childN S A ((ord A.N A.G).order) u = 0
            show (cluster S A ((ord A.N A.G).order) u).ncard = 0
            rw [hemp, Set.ncard_empty]
          rw [chargeTotal_driverChargeMS_of_N_eq_zero S ord ℓp htabF covC
            fuel (j + 1) _ hN0]
          simp
      -- the recursive column, against the mass clause
      have hrec : ∑ u : Fin A.N,
          (chargeTotal (driverChargeMS S ord ℓp htabF covC fuel (j + 1)
            (childArena S A ((ord A.N A.G).order) u)) : ℝ)
          ≤ (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * (2 * δ))) *
            ((c + 1) * W ^ ((1 : ℝ) + δ)) := by
        calc ∑ u : Fin A.N,
            (chargeTotal (driverChargeMS S ord ℓp htabF covC fuel (j + 1)
              (childArena S A ((ord A.N A.G).order) u)) : ℝ)
            ≤ ∑ u : Fin A.N,
              (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * (2 * δ))) *
                (if (cluster S A ((ord A.N A.G).order) u).Nonempty
                  then (weight (childArena S A ((ord A.N A.G).order) u) : ℝ)
                  else 0) := Finset.sum_le_sum fun u _ => hterm u
          _ = (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * (2 * δ))) *
              ∑ u : Fin A.N,
                (if (cluster S A ((ord A.N A.G).order) u).Nonempty
                  then (weight (childArena S A ((ord A.N A.G).order) u) : ℝ)
                  else 0) := by rw [Finset.mul_sum]
          _ ≤ (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * (2 * δ))) *
              ((c + 1) * W ^ ((1 : ℝ) + δ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKL hE)
              exact sum_child_weight_le S A ((ord A.N A.G).order) hc hδ hWA hdeg'
      -- the exponent bookkeeping
      have hEsplit : W ^ (((fuel : ℝ) + 2) * (2 * δ)) * W ^ ((1 : ℝ) + δ)
          = W ^ (1 + (δ + ((fuel : ℝ) + 2) * (2 * δ))) := by
        rw [← Real.rpow_add hWpos]
        congr 1
        ring
      have hE1 : W ^ (1 + (δ + ((fuel : ℝ) + 2) * (2 * δ)))
          ≤ W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) :=
        Real.rpow_le_rpow_of_exponent_le hW1
          (by nlinarith [hδ, Nat.cast_nonneg (α := ℝ) fuel])
      have hEa : W ^ ((1 : ℝ) + 2 * δ)
          ≤ W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) :=
        Real.rpow_le_rpow_of_exponent_le hW1
          (by nlinarith [hδ, Nat.cast_nonneg (α := ℝ) fuel])
      have hNE : (0 : ℝ) ≤ W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) :=
        Real.rpow_nonneg hWpos.le _
      -- the node constant, uniformized
      have hncj : (nodeConst S j (ℓp j) : ℝ) ≤ (nodeConstBound S ℓp : ℝ) := by
        exact_mod_cast nodeConst_le_nodeConstBound S ℓp
          (show j ≤ S.depth by omega)
      have hamaxnn : (0 : ℝ) ≤ f + (c + 1) * (nodeConstBound S ℓp : ℝ) := by
        have h1 : (0 : ℝ) ≤ (c + 1) * (nodeConstBound S ℓp : ℝ) :=
          mul_nonneg (by linarith) hncB
        linarith
      have hamax : f + (c + 1) * (nodeConst S j (ℓp j) : ℝ)
          ≤ f + (c + 1) * (nodeConstBound S ℓp : ℝ) := by
        have h1 : (c + 1) * (nodeConst S j (ℓp j) : ℝ)
            ≤ (c + 1) * (nodeConstBound S ℓp : ℝ) :=
          mul_le_mul_of_nonneg_left hncj (by linarith)
        linarith
      -- the chosen K absorbs the step
      have hKstep : (f + (c + 1) * (nodeConstBound S ℓp : ℝ))
          + (c + 1) * K ^ (fuel + 1) ≤ K ^ (fuel + 1 + 1) := by
        have hK1k : (1 : ℝ) ≤ K ^ (fuel + 1) := one_le_pow₀ hK1
        have hKA : (f + (c + 1) * (nodeConstBound S ℓp : ℝ)) + (c + 1) ≤ K := by
          rw [hKdef]
          unfold KP
          linarith
        calc (f + (c + 1) * (nodeConstBound S ℓp : ℝ)) + (c + 1) * K ^ (fuel + 1)
            ≤ (f + (c + 1) * (nodeConstBound S ℓp : ℝ)) * K ^ (fuel + 1)
              + (c + 1) * K ^ (fuel + 1) := by
              nlinarith [hK1k, hamaxnn]
          _ = ((f + (c + 1) * (nodeConstBound S ℓp : ℝ)) + (c + 1))
              * K ^ (fuel + 1) := by ring
          _ ≤ K * K ^ (fuel + 1) :=
              mul_le_mul_of_nonneg_right hKA (by linarith)
          _ = K ^ (fuel + 1 + 1) := by ring
      -- assemble
      have hstep1 : (f + (c + 1) * (nodeConst S j (ℓp j) : ℝ)) * W ^ ((1 : ℝ) + 2 * δ)
          ≤ (f + (c + 1) * (nodeConstBound S ℓp : ℝ))
            * W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) :=
        mul_le_mul hamax hEa (Real.rpow_nonneg hWpos.le _) hamaxnn
      have hstep2 : (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * (2 * δ))) *
            ((c + 1) * W ^ ((1 : ℝ) + δ))
          ≤ (c + 1) * K ^ (fuel + 1)
            * W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) := by
        calc (K ^ (fuel + 1) * W ^ (((fuel : ℝ) + 2) * (2 * δ))) *
              ((c + 1) * W ^ ((1 : ℝ) + δ))
            = (c + 1) * K ^ (fuel + 1)
              * (W ^ (((fuel : ℝ) + 2) * (2 * δ)) * W ^ ((1 : ℝ) + δ)) := by ring
          _ = (c + 1) * K ^ (fuel + 1)
              * W ^ (1 + (δ + ((fuel : ℝ) + 2) * (2 * δ))) := by rw [hEsplit]
          _ ≤ (c + 1) * K ^ (fuel + 1)
              * W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) := by
              refine mul_le_mul_of_nonneg_left hE1 ?_
              exact mul_nonneg (by linarith) hKL
      have hcast2 : ((fuel + 1 : ℕ) : ℝ) + 2 = ((fuel : ℝ) + 1) + 2 := by
        push_cast
        ring
      rw [hcast2]
      calc (f + (c + 1) * (nodeConst S j (ℓp j) : ℝ)) * W ^ ((1 : ℝ) + 2 * δ)
            + ∑ u : Fin A.N,
                (chargeTotal (driverChargeMS S ord ℓp htabF covC fuel (j + 1)
                  (childArena S A ((ord A.N A.G).order) u)) : ℝ)
          ≤ (f + (c + 1) * (nodeConstBound S ℓp : ℝ))
              * W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ))
            + (c + 1) * K ^ (fuel + 1)
              * W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) :=
            add_le_add hstep1 (hrec.trans hstep2)
        _ = ((f + (c + 1) * (nodeConstBound S ℓp : ℝ)) + (c + 1) * K ^ (fuel + 1))
            * W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) := by ring
        _ ≤ K ^ (fuel + 1 + 1) * W ^ (1 + (((fuel : ℝ) + 1) + 2) * (2 * δ)) :=
            mul_le_mul_of_nonneg_right hKstep hNE

/-! ## The root: `mcChargeMS`, priced (the headline, deliverable 2) -/

/-- The scatter budget of the root evaluation: the sum of `σ.t` over
`top`'s scatter atoms — a constant of the schedule. The `t = 0` guard
is priced in: a zero atom charges nothing
(`Impl.greedyScatterCost_zero`). -/
noncomputable def topBudget (S : Setup L) : ℕ :=
  ((scatterAtoms S.choice S.φ S.hφ).map fun σ => σ.t).sum

/-- The root scatter column fits `topBudget · 2‖G‖`, independently of
the delivered table — `Impl.greedyScatterCost_le` per atom, at the §6.5
marking parameter `W := ‖rootArena‖`. -/
theorem topScatterCost_le (S : Setup L) (G : SimpleGraph (Fin n₀))
    (col : Coloring n₀ L) (T : Fin n₀ → DistFO L 1 → Prop) :
    topScatterCost S G col T ≤ topBudget S * (2 * graphWeight G) := by
  have hNW : n₀ ≤ graphWeight G := Nat.le_add_right _ _
  have hw : weight (rootArena G col) = graphWeight G := rfl
  calc topScatterCost S G col T
      ≤ ((scatterAtoms S.choice S.φ S.hφ).map fun σ =>
          σ.t * (2 * graphWeight G)).sum := by
        refine List.sum_le_sum fun σ _ => ?_
        refine le_trans (Impl.greedyScatterCost_le _ _ _ _ _) ?_
        exact Nat.mul_le_mul_left _ (by omega)
    _ = topBudget S * (2 * graphWeight G) := by
        rw [List.sum_map_mul_right, topBudget]

open Classical in
/-- **The root program's budget, priced on one graph**: under the cover
slot's total bound and the routine's wreach-degree bound over subgraph
copies of `G` itself, the whole `mcChargeMS` total — root driver plus
the top scatter column — is within
`(KP^{ℓ+1} + 2·topBudget)·‖G‖^{1+(ℓ+2)·2δ}`. -/
theorem mcChargeMS_chargeTotal_le (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    {c f δ : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) (hδ : 0 ≤ δ)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L)
    (hcov : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), A.G ⊑ G →
      (chargeTotal (covC j A) : ℝ) ≤ f * (A.N : ℝ) ^ (1 + 2 * δ))
    (hdeg : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
      ∀ v : Fin m, (wreach H ((ord m H).order) (2 * S.R) v).ncard
        ≤ ⌈c * (m : ℝ) ^ δ⌉₊)
    (hW : 1 ≤ graphWeight G) :
    (chargeTotal (mcChargeMS S ord ℓp htabF covC G col) : ℝ)
      ≤ (KP S ℓp c f ^ (S.depth + 1) + 2 * (topBudget S : ℝ))
        * (graphWeight G : ℝ) ^ (1 + ((S.depth : ℝ) + 2) * (2 * δ)) := by
  have hcopy : (rootArena (L := L) G col).G ⊑ G := ⟨SimpleGraph.Copy.id G⟩
  have hWr : 1 ≤ weight (rootArena (L := L) G col) := hW
  have hdrv := driverChargeMS_chargeTotal_le S ord ℓp htabF covC hc hf hδ
    hcov hdeg S.depth 0 (by omega) (rootArena G col) hcopy hWr
  rw [Headline.weight_rootArena] at hdrv
  have htot : chargeTotal (mcChargeMS S ord ℓp htabF covC G col)
      = chargeTotal (driverChargeMS S ord ℓp htabF covC S.depth 0 (rootArena G col))
        + topScatterCost S G col (tables S ord 0 (rootArena G col)) := by
    rw [mcChargeMS, chargeTotal_add, chargeTotal_cost (by decide)]
  have hW1 : (1 : ℝ) ≤ (graphWeight G : ℝ) := by exact_mod_cast hW
  have hE0 : (0 : ℝ) ≤ ((S.depth : ℝ) + 2) * (2 * δ) := by
    have h1 : (0 : ℝ) ≤ (S.depth : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) S.depth
      linarith
    have h2 : (0 : ℝ) ≤ 2 * δ := by linarith
    exact mul_nonneg h1 h2
  have hWe : (graphWeight G : ℝ)
      ≤ (graphWeight G : ℝ) ^ (1 + ((S.depth : ℝ) + 2) * (2 * δ)) := by
    have h := Real.rpow_le_rpow_of_exponent_le hW1
      (by linarith : (1 : ℝ) ≤ 1 + ((S.depth : ℝ) + 2) * (2 * δ))
    rwa [Real.rpow_one] at h
  have htop : (topScatterCost S G col (tables S ord 0 (rootArena G col)) : ℝ)
      ≤ 2 * (topBudget S : ℝ)
        * (graphWeight G : ℝ) ^ (1 + ((S.depth : ℝ) + 2) * (2 * δ)) := by
    have h : (topScatterCost S G col (tables S ord 0 (rootArena G col)) : ℝ)
        ≤ (topBudget S : ℝ) * (2 * (graphWeight G : ℝ)) := by
      exact_mod_cast topScatterCost_le S G col (tables S ord 0 (rootArena G col))
    refine h.trans ?_
    calc (topBudget S : ℝ) * (2 * (graphWeight G : ℝ))
        = 2 * (topBudget S : ℝ) * (graphWeight G : ℝ) := by ring
      _ ≤ 2 * (topBudget S : ℝ)
          * (graphWeight G : ℝ) ^ (1 + ((S.depth : ℝ) + 2) * (2 * δ)) := by
          refine mul_le_mul_of_nonneg_left hWe (by positivity)
  rw [htot]
  push_cast
  have hrhs : (KP S ℓp c f ^ (S.depth + 1) + 2 * (topBudget S : ℝ))
      * (graphWeight G : ℝ) ^ (1 + ((S.depth : ℝ) + 2) * (2 * δ))
      = KP S ℓp c f ^ (S.depth + 1)
          * (graphWeight G : ℝ) ^ (1 + ((S.depth : ℝ) + 2) * (2 * δ))
        + 2 * (topBudget S : ℝ)
          * (graphWeight G : ℝ) ^ (1 + ((S.depth : ℝ) + 2) * (2 * δ)) := by ring
  rw [hrhs]
  exact add_le_add hdrv htop

/-! ## The headline on a class (the `mcCharge_le`-shaped corollary) -/

/-- The headline's `δ`: `ε/(2(ℓ+2))` — half the abstract layer's
`ε/(ℓ+2)`, because the program's per-level exponent increment is `2δ`
(the node envelope's own exponent). -/
noncomputable def headlineδ (S : Setup L) (ε : ℝ) : ℝ :=
  ε / (2 * ((S.depth : ℝ) + 2))

/-- **The headline's cover family** — F5's slot vector, per node: the
priced greedy routine at `3·S.R` rounds, sweep radius `S.R`, degree
parameter `⌈cf·N^δ⌉₊`. `ProgCover.coverProg_slot` fills the frame's
cover slot with exactly this budget, so instantiating F4's
`CoverSlotSpec` at `coverProg`/`coverCF` makes `mcChargeMS` at this
family the MS-routed program's advertised budget. -/
noncomputable def coverCF (S : Setup L) (cf δ : ℝ) :
    (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ :=
  fun _j A => coverC A.N A.G S.R (3 * S.R) ⌈cf * (A.N : ℝ) ^ δ⌉₊

open Classical in
/-- **The leaf's headline** (`mcCharge_le`-shaped, at the MS-routed
budget): on a nowhere dense class, for every setup, `ε > 0` and
history-round profile `ℓp`, there are constants `cf, κ ≥ 0` — fixed
before any graph — such that on every member the whole root budget of
the program, at the honest priced routine `timedGreedyRoutine (3·S.R)`
and the concrete cover family `coverCF S cf (headlineδ S ε)`, is

    chargeTotal (mcChargeMS …) ≤ κ · (‖G‖+1)^{1+ε}.

The degree parameter of the sweep is `exists_coverCharge_le`'s derived
`⌈cf·N^δ⌉₊`; the wreach-degree constant of the recursion is
`exists_wreach_degree_timedGreedyRoutine`'s (it lives inside `κ`
through `KP`). The radius arithmetic `3t ≤ R`, `2·S.R ≤ 2^t`,
`1 ≤ S.R` is discharged by the setup itself (`t := S.R`,
`Setup.one_le_R`, `two_mul_le_two_pow`). F6/F7 consume this verbatim;
the decision clause is `ProgDriver.mcProg_headline`. -/
theorem exists_mcChargeMS_chargeTotal_le (C : GraphClass) (hC : NowhereDense C)
    (S : Setup L) {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) :
    ∃ cf κ : ℝ, 0 ≤ cf ∧ 0 ≤ κ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n L)
          (htabF : (j : ℕ) → (A : Arena (S.pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N)),
          (chargeTotal (mcChargeMS S (timedGreedyRoutine (3 * S.R)) ℓp htabF
              (coverCF S cf (headlineδ S ε)) G col) : ℝ)
            ≤ κ * ((graphWeight G : ℝ) + 1) ^ (1 + ε) := by
  have hδ : 0 < headlineδ S ε := by
    unfold headlineδ
    positivity
  obtain ⟨cdeg, hcdeg0, hdegAll⟩ := exists_wreach_degree_timedGreedyRoutine C hC
    S.R (3 * S.R) S.R le_rfl (two_mul_le_two_pow S.one_le_R) (headlineδ S ε) hδ
  obtain ⟨cs, fs, hcs0, hfs0, hcovAll⟩ := exists_coverCharge_le C hC
    S.R (3 * S.R) S.R le_rfl (two_mul_le_two_pow S.one_le_R) S.one_le_R
    (headlineδ S ε) hδ
  have hK1 : (1 : ℝ) ≤ KP S ℓp cdeg fs := one_le_KP S ℓp hcdeg0 hfs0
  have hκ0 : (0 : ℝ) ≤ KP S ℓp cdeg fs ^ (S.depth + 1) + 2 * (topBudget S : ℝ) := by
    have h1 : (0 : ℝ) ≤ KP S ℓp cdeg fs ^ (S.depth + 1) :=
      pow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ (topBudget S : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨cs, KP S ℓp cdeg fs ^ (S.depth + 1) + 2 * (topBudget S : ℝ),
    hcs0, hκ0, ?_⟩
  intro n G hG col htabF
  by_cases hW : 1 ≤ graphWeight G
  · -- the honest case: the lift at the root, then the exponent choice
    have hcovG : ∀ (j : ℕ) (A : Arena (S.pal j) n), A.G ⊑ G →
        (chargeTotal (coverCF S cs (headlineδ S ε) j A) : ℝ)
          ≤ fs * (A.N : ℝ) ^ (1 + 2 * headlineδ S ε) := by
      intro j A hsub
      have hCF : chargeTotal (coverCF S cs (headlineδ S ε) j A)
          = chainCharge A.G (3 * S.R)
            + Impl.sweepCharge A.G
                ((timedGreedyRoutine (3 * S.R)) A.N A.G).order S.R
                ⌈cs * (A.N : ℝ) ^ headlineδ S ε⌉₊ :=
        chargeTotal_coverC A.N A.G S.R (3 * S.R) _
      rw [hCF]
      exact_mod_cast hcovAll n G hG A.N A.G hsub
    have hdegG : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
        ∀ v : Fin m,
          (wreach H (((timedGreedyRoutine (3 * S.R)) m H).order) (2 * S.R) v).ncard
            ≤ ⌈cdeg * (m : ℝ) ^ headlineδ S ε⌉₊ :=
      fun m H hsub v => hdegAll n G hG m H hsub v
    have hmc := mcChargeMS_chargeTotal_le S (timedGreedyRoutine (3 * S.R)) ℓp
      htabF (coverCF S cs (headlineδ S ε)) hcdeg0 hfs0 hδ.le G col hcovG hdegG hW
    have hexp : 1 + ((S.depth : ℝ) + 2) * (2 * headlineδ S ε) = 1 + ε := by
      rw [headlineδ]
      have h2 : 2 * ((S.depth : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      try ring
    rw [hexp] at hmc
    refine hmc.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hκ0
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
  · -- the degenerate input: `‖G‖ = 0`, so the whole ledger is `0`
    have hgw : graphWeight G = 0 := by omega
    have hn : n = 0 := by
      have h : n ≤ graphWeight G := Nat.le_add_right _ _
      omega
    have hdz : chargeTotal (driverChargeMS S (timedGreedyRoutine (3 * S.R)) ℓp
        htabF (coverCF S cs (headlineδ S ε)) S.depth 0 (rootArena G col)) = 0 :=
      chargeTotal_driverChargeMS_of_N_eq_zero S (timedGreedyRoutine (3 * S.R))
        ℓp htabF _ S.depth 0 (rootArena G col) hn
    have htopz : topScatterCost S G col
        (tables S (timedGreedyRoutine (3 * S.R)) 0 (rootArena G col)) = 0 := by
      have h := topScatterCost_le S G col
        (tables S (timedGreedyRoutine (3 * S.R)) 0 (rootArena G col))
      rw [hgw] at h
      omega
    have hmcz : chargeTotal (mcChargeMS S (timedGreedyRoutine (3 * S.R)) ℓp htabF
        (coverCF S cs (headlineδ S ε)) G col) = 0 := by
      rw [mcChargeMS, chargeTotal_add, chargeTotal_cost (by decide), hdz, htopz]
    rw [hmcz, hgw]
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    exact hκ0

/-! ## The `T`-arithmetic close (deliverable 3, E13's item (e)) -/

open Lax11.GraphEncoding in
/-- **The endorsed axiom's `T` clause, at the charge level** — E13's
item (e), stated so F7 need only multiply by the machine's `L.const`:
for every nowhere dense `C`, plain sentence `φ : FO 0`, `ε > 0` and
history profile `ℓp`, there are `cf, c' ≥ 0` and a ℕ-valued
`T : List ℕ → ℕ` — all fixed before any input — with

* `T x ≤ c'·(|x|+1)^{1+ε}` for **every** word `x`, and
* on every member of `C` and every CSR encoding `x` of it
  (`EncodesGraph`), the root program's whole ledger total at the
  campaign setup — `mcChargeMS` at the priced routine and the headline
  cover family — is at most `T x`.

The encoding seam is `Headline.graphWeight_add_three_le_length`'s
direction (`‖G‖ ≤ |x|`); the `ECost` reading of the same number is
`totalE_liftACost`. -/
theorem exists_mcChargeMS_T (C : GraphClass) (hC : NowhereDense C)
    (φ : Lax3.FirstOrder.FO 0) {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 0 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n 0)
          (htabF : (j : ℕ) →
            (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N))
          (x : List ℕ), EncodesGraph x n G →
          chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ)
              (timedGreedyRoutine (3 * (Headline.headlineSetup C hC φ).R))
              ℓp htabF
              (coverCF (Headline.headlineSetup C hC φ) cf
                (headlineδ (Headline.headlineSetup C hC φ) ε))
              G col) ≤ T x := by
  obtain ⟨cf, κ, hcf0, hκ0, hmain⟩ :=
    exists_mcChargeMS_chargeTotal_le C hC (Headline.headlineSetup C hC φ) hε ℓp
  refine ⟨cf, κ + 1, fun x => ⌈κ * ((x.length : ℝ) + 1) ^ (1 + ε)⌉₊, hcf0,
    by linarith, ?_, ?_⟩
  · -- the `T` bound, for every word
    intro x
    have h1 : (1 : ℝ) ≤ (x.length : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) x.length
      linarith
    have hle1 : (1 : ℝ) ≤ ((x.length : ℝ) + 1) ^ (1 + ε) := by
      calc (1 : ℝ) = 1 ^ ((1 : ℝ) + ε) := (Real.one_rpow _).symm
        _ ≤ ((x.length : ℝ) + 1) ^ (1 + ε) :=
          Real.rpow_le_rpow (by norm_num) h1 (by linarith)
    have hy : (0 : ℝ) ≤ κ * ((x.length : ℝ) + 1) ^ (1 + ε) :=
      mul_nonneg hκ0 (by linarith)
    calc ((⌈κ * ((x.length : ℝ) + 1) ^ (1 + ε)⌉₊ : ℕ) : ℝ)
        ≤ κ * ((x.length : ℝ) + 1) ^ (1 + ε) + 1 := (Nat.ceil_lt_add_one hy).le
      _ ≤ (κ + 1) * ((x.length : ℝ) + 1) ^ (1 + ε) := by nlinarith [hle1, hκ0]
  · -- the budget against the axiom's measure, on members
    intro n G hG col htabF x hx
    have hb := hmain n G hG col htabF
    have hlen : (graphWeight G : ℝ) ≤ (x.length : ℝ) :=
      Nat.cast_le.mpr (Headline.graphWeight_le_length hx)
    have h2 : (chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ)
        (timedGreedyRoutine (3 * (Headline.headlineSetup C hC φ).R)) ℓp htabF
        (coverCF (Headline.headlineSetup C hC φ) cf
          (headlineδ (Headline.headlineSetup C hC φ) ε)) G col) : ℝ)
        ≤ κ * ((x.length : ℝ) + 1) ^ (1 + ε) := by
      refine hb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hκ0
      refine Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have h3 := h2.trans (Nat.le_ceil _)
    exact_mod_cast h3

/-! ## The total is the whole ledger: support honesty

Off the ten program currencies every vector of the family vanishes, so
`chargeTotal` (and, through `totalE_liftACost`, the `ECost` total F7
reads) misses nothing. -/

/-- A program-currency charge vanishes off `progKeys`. -/
theorem toFun_cost_eq_zero_of_notMem {kk : String} (hkk : kk ∈ progKeys)
    {k : String} (hk : k ∉ progKeys) (n : ℕ) : (ACost.cost kk n).toFun k = 0 :=
  ACost.toFun_cost_ne (by rintro rfl; exact hk hkk) n

open Classical in
/-- F5's `coverC` (hence `coverCF`) spends only program currencies. -/
theorem coverC_toFun_eq_zero_of_notMem (m : ℕ) (G : SimpleGraph (Fin m))
    (rc R D : ℕ) {k : String} (hk : k ∉ progKeys) :
    (coverC m G rc R D).toFun k = 0 :=
  coverC_toFun_ne m G rc R D (by rintro rfl; exact hk (by decide))
    (by rintro rfl; exact hk (by decide))

section Support

variable (S : Setup L) (ord : CoverSpec.OrderingRoutine)

open Classical in
theorem centreChargeMS_toFun_eq_zero (j : ℕ) (A : Arena (S.pal j) n₀) (ℓp : ℕ)
    (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {k : String} (hk : k ∉ progKeys)
    (hnxC : (nxC (childArena S A π u)).toFun k = 0) :
    (centreChargeMS S j A ℓp htab nx nxC π u).toFun k = 0 := by
  simp only [centreChargeMS, restrictC, supportsC, profilesCMS, isolateC,
    ACost.toFun_add, hnxC,
    toFun_cost_eq_zero_of_notMem (show "frame.restrict" ∈ progKeys by decide) hk,
    toFun_cost_eq_zero_of_notMem (show "frame.supports" ∈ progKeys by decide) hk,
    toFun_cost_eq_zero_of_notMem (show "frame.profiles" ∈ progKeys by decide) hk,
    toFun_cost_eq_zero_of_notMem (show "frame.isolate" ∈ progKeys by decide) hk,
    toFun_cost_eq_zero_of_notMem (show "frame.scatter" ∈ progKeys by decide) hk,
    add_zero]

open Classical in
theorem frameChargeMS_toFun_eq_zero (j : ℕ) (A : Arena (S.pal j) n₀) (ℓp : ℕ)
    (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop)
    (covC : ACost String ℕ) (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    {k : String} (hk : k ∉ progKeys) (hcovC : covC.toFun k = 0)
    (hnxC : ∀ B, (nxC B).toFun k = 0) :
    (frameChargeMS S ord j A ℓp htab nx covC nxC).toFun k = 0 := by
  rw [frameChargeMS]
  by_cases hbot : A.G = ⊥
  · rw [if_pos hbot]
    exact toFun_cost_eq_zero_of_notMem (by decide) hk _
  · rw [if_neg hbot]
    have hall : (allocC A).toFun k = 0 :=
      toFun_cost_eq_zero_of_notMem (by decide) hk _
    have hread : (readC S j A).toFun k = 0 :=
      toFun_cost_eq_zero_of_notMem (by decide) hk _
    have hz : ((List.finRange A.N).map
        ((fun x => ACost.toFun x k)
          ∘ centreChargeMS S j A ℓp htab nx nxC ((ord A.N A.G).order))).sum = 0 := by
      refine List.sum_eq_zero ?_
      intro x hx
      obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
      exact centreChargeMS_toFun_eq_zero S j A ℓp htab nx nxC _ u hk (hnxC _)
    simp only [ACost.toFun_add, toFun_listSum, List.map_map, hcovC, hall, hread,
      hz, add_zero]

open Classical in
/-- **Support honesty for the driver**: off the ten program currencies
the whole level recursion's ledger vanishes — provided the cover family
does (which `coverCF` satisfies,
`coverC_toFun_eq_zero_of_notMem`). -/
theorem driverChargeMS_toFun_eq_zero (ℓpF : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓpF j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    {k : String} (hk : k ∉ progKeys)
    (hcovC : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), (covC j A).toFun k = 0) :
    ∀ (fuel j : ℕ) (A : Arena (S.pal j) n₀),
      (driverChargeMS S ord ℓpF htabF covC fuel j A).toFun k = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro j A
    rw [driverChargeMS]
    exact toFun_cost_eq_zero_of_notMem (by decide) hk _
  | succ fuel ih =>
    intro j A
    rw [driverChargeMS]
    exact frameChargeMS_toFun_eq_zero S ord j A (ℓpF j) (htabF j A) _ _ _ hk
      (hcovC j A) (fun B => ih (j + 1) B)

open Classical in
/-- **Support honesty at the root**: `mcChargeMS` vanishes off
`progKeys`, so `chargeTotal` is the whole ledger — nothing is spent
outside the ten currencies the total sums. -/
theorem mcChargeMS_toFun_eq_zero (ℓpF : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓpF j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L)
    {k : String} (hk : k ∉ progKeys)
    (hcovC : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), (covC j A).toFun k = 0) :
    (mcChargeMS S ord ℓpF htabF covC G col).toFun k = 0 := by
  rw [mcChargeMS, ACost.toFun_add,
    driverChargeMS_toFun_eq_zero S ord ℓpF htabF covC hk hcovC,
    toFun_cost_eq_zero_of_notMem (by decide) hk _, add_zero]

end Support

end Lax3Proofs.Prog
