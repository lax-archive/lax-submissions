import Lax3Proofs.ProgCoverCharge
import Lax3Proofs.ProgFrame
import Lax3Proofs.ImplCover

/-!
# F5 — the cover slot: the ordering phase and the sweep, as one priced program

`ProgCoverCharge` priced the ordering phase and discharged
`CoverSpec.CoverOrderingTime` (`coverOrderingTime_of_nowhereDense`).
This file finishes the leaf's program half: **F3's cover slot, filled.**

## The program

`frameProg` (F3) takes the cover pass as a parameter `coverProg` with a
spec-and-charge hypothesis

    hcover : coverProg ≤ NRest.spec (fun π => π = (ord A.N A.G).order)
                           (fun _ => liftACost covC)

`Prog.coverProg` below is that program for `ord := timedGreedyRoutine R`:

1. **the ordering stage** — the priced greedy routine's ordering, a
   definite value, charged `"cover.order" (chainCharge G R)`; the
   ledger entry *is* the routine's abstract `steps` field
   (`coverC_order_eq_steps`, definitionally `timedGreedyRoutine_steps`)
   — the seam `E12` re-derives from a machine;
2. **the sweep stage** — GKS's cluster sweep (E12c): the emitted
   cluster list `Impl.sweepClusters` and the `ctr` assignment
   `Impl.sweepCtr`, both definite values, charged
   `"cover.sweep" (Impl.sweepCharge)` — the landed per-vertex account
   (BFS at its edge budget plus deletion overhead, `ImplCover` §4).
   The values are the machine's cluster data: the frame's abstract
   `cluster S A π u` reads them through the landed identities
   `sweepCluster_eq_cluster` and `sweepCtr_eq_centre`;
3. return the ordering — the slot's value.

`coverProg_le_spec` is the refinement, via F3's spec calculus;
`coverProg_slot` is its instantiation at an arena — literally the
`hcover` hypothesis of `frameProg_le_spec` at `ord := timedGreedyRoutine
R`, `covC := coverC`.

## The pipeline's cost, closed

`exists_coverCharge_le` is the leaf's capstone: on a nowhere dense
class, with the cover radius `rc ≥ 1` (E12c's genuine side condition,
supplied downstream by the design's `R ≥ 1`) and the radius arithmetic
`3t ≤ R`, `2·rc ≤ 2^t`, there are constants `c, f` — fixed before the
graph — such that on every subgraph copy of every member

    chainCharge + sweepCharge (at D = ⌈c·m^δ⌉₊)  ≤  f · m^{1+2δ}.

The degree parameter `D` fed to the sweep is **derived, not assumed**:
`exists_wreach_degree_timedGreedyRoutine` reads the wreach-degree bound
of the priced routine's ordering off `AugChainData` + the class
(`CoverDegree.wreach_degree_of_data` at `timedGreedyRoutine_data`).
The order half enters at its true exponent `m^{1+δ}`
(`exists_chainCharge_le`), the sweep at `2·D·(m·D)`
(`Impl.sweepCharge_le`) — the `m^{1+2δ}` term, which dominates, exactly
as in GKS (ordering `g·n^{1+ε}` tex:1460-1463, sweep `2n^{1+2δ}`
tex:1514-1517).
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Refine
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ColoringNumbers
open Lax3Proofs.CoverDegree
open Lax3Proofs.CoverRoutine

/-! ## The wreach degree of the priced routine's ordering

The hypothesis `Impl.sweepCharge_le` consumes, derived for the greedy
chain's final ordering from the class — not assumed. -/

/-- **The wreach-degree bound of the timed greedy routine's ordering**:
on a nowhere dense class, with the radius arithmetic, there is a `c ≥ 0`
— fixed before the graph — bounding every wreach set of the ordering
the priced routine outputs by `⌈c·m^δ⌉₊`.  This is
`CoverDegree.wreach_degree_of_data` consumed at
`timedGreedyRoutine_data`. -/
theorem exists_wreach_degree_timedGreedyRoutine (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ v : Fin m,
          (wreach G ((timedGreedyRoutine R) m G).order (2 * rc) v).ncard
            ≤ ⌈c * (m : ℝ) ^ δ⌉₊ := by
  obtain ⟨c, hc⟩ := wreach_degree_of_data C hC rc R t ht hrt δ hδ
  refine ⟨max c 0, le_max_right _ _, fun n Gn hGn m G hsub v => ?_⟩
  have h := hc n Gn hGn m G hsub _ _ _ _ (timedGreedyRoutine_data R m G) v
  refine h.trans (Nat.ceil_mono ?_)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg m) δ)

/-! ## The slot's charge vector -/

open Classical in
/-- **The cover slot's charge vector**: the ordering stage in
`"cover.order"` — the priced routine's `chainCharge` — and the sweep
stage in `"cover.sweep"` — `Impl.sweepCharge` at the slot's ordering
and degree parameter.  This is the `covC` the frame's `hcover`
hypothesis carries. -/
noncomputable def coverC (m : ℕ) (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    ACost String ℕ :=
  ACost.cost "cover.order" (chainCharge G R)
    + ACost.cost "cover.sweep"
        (Impl.sweepCharge G ((timedGreedyRoutine R) m G).order rc D)

open Classical in
@[simp] theorem coverC_toFun_order (m : ℕ) (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    (coverC m G rc R D).toFun "cover.order" = chainCharge G R := by
  simp [coverC, ACost.toFun_add]

open Classical in
@[simp] theorem coverC_toFun_sweep (m : ℕ) (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    (coverC m G rc R D).toFun "cover.sweep"
      = Impl.sweepCharge G ((timedGreedyRoutine R) m G).order rc D := by
  simp [coverC, ACost.toFun_add]

open Classical in
/-- **Slot hygiene**: the cover slot spends only its own two
currencies.  Instantiated at `"frame.restrict"` (and any other frame
currency) this is the `hcov` hypothesis of F3's ledger identities. -/
theorem coverC_toFun_ne (m : ℕ) (G : SimpleGraph (Fin m)) (rc R D : ℕ) {k : String}
    (h₁ : k ≠ "cover.order") (h₂ : k ≠ "cover.sweep") :
    (coverC m G rc R D).toFun k = 0 := by
  simp [coverC, ACost.toFun_add, ACost.toFun_cost_ne h₁, ACost.toFun_cost_ne h₂]

open Classical in
/-- **The ledger–routine seam**: the slot's `"cover.order"` entry is
exactly the priced routine's abstract `steps` field.  `E12` owes the
same number from a machine. -/
theorem coverC_order_eq_steps (m : ℕ) (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    (((coverC m G rc R D).toFun "cover.order" : ℕ) : ℝ)
      = ((timedGreedyRoutine R) m G).steps := by
  rw [coverC_toFun_order, timedGreedyRoutine_steps]

/-! ## The slot's program -/

open Classical in
/-- **The cover slot's program** (F3's `coverProg` parameter, filled):
pay the ordering phase and hold its ordering; run the sweep — the
cluster list and the `ctr` assignment, GKS's routine as landed in
`ImplCover` — and pay its account; return the ordering.  The sweep's
values are the machine's cluster data; the frame's abstract `cluster`
and `centre` read them through `Impl.sweepCluster_eq_cluster` and
`Impl.sweepCtr_eq_centre`. -/
noncomputable def coverProg (m : ℕ) (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    NRest (Equiv.Perm (Fin m)) ECost :=
  NRest.bindT (NRest.consume (NRest.returnT ((timedGreedyRoutine R) m G).order)
      (liftACost (ACost.cost "cover.order" (chainCharge G R)))) fun π =>
  NRest.bindT (NRest.consume
      (NRest.returnT (Impl.sweepClusters G π rc, Impl.sweepCtr G π rc))
      (liftACost (ACost.cost "cover.sweep" (Impl.sweepCharge G π rc D)))) fun _sw =>
  NRest.returnT π

open Classical in
/-- **The slot's refinement**: the cover program returns exactly the
priced routine's ordering, for budget `coverC` — the shape of F3's
`hcover` hypothesis, proved through the frame's own spec calculus. -/
theorem coverProg_le_spec (m : ℕ) (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    coverProg m G rc R D ≤
      NRest.spec (fun π => π = ((timedGreedyRoutine R) m G).order)
        (fun _ => liftACost (coverC m G rc R D)) := by
  rw [coverProg, coverC, liftACost_add]
  refine bindT_le_spec
    (consume_returnT_le_spec
      (P := fun π => π = ((timedGreedyRoutine R) m G).order) rfl _)
    fun π hπ => ?_
  subst hπ
  refine le_spec_weaken
    (bindT_le_spec
      (consume_returnT_le_spec (P := fun _ => True) trivial _)
      (fun _ _ => returnT_le_spec
        (P := fun π' => π' = ((timedGreedyRoutine R) m G).order) rfl 0))
    (fun _ hx => hx) (add_zero _).le

open Classical in
/-- The slot, at an arena: **F3's `hcover` hypothesis, discharged** for
`ord := timedGreedyRoutine R` and `covC := coverC A.N A.G S.R R D` —
`frameProg_le_spec` composes with this directly. -/
theorem coverProg_slot {L n₀ : ℕ} (S : Driver.Setup L) (j : ℕ)
    (A : Driver.Arena (S.pal j) n₀) (R D : ℕ) :
    coverProg A.N A.G S.R R D ≤
      NRest.spec (fun π => π = ((timedGreedyRoutine R) A.N A.G).order)
        (fun _ => liftACost (coverC A.N A.G S.R R D)) :=
  coverProg_le_spec A.N A.G S.R R D

/-! ## The pipeline's cost, closed -/

open Classical in
/-- **The cover pipeline's cost, proved** — the leaf's capstone: on a
nowhere dense class, with the radius arithmetic `3t ≤ R`,
`2·rc ≤ 2^t` and the sweep's genuine side condition `1 ≤ rc`, there
are `c, f ≥ 0` — both fixed before the graph — such that on every
subgraph copy of every member the **whole** cover charge, ordering
phase plus sweep at the derived degree `D = ⌈c·m^δ⌉₊`, is at most
`f·m^{1+2δ}`.  The two summands are `coverC`'s two ledger entries
(`coverC_toFun_order`/`coverC_toFun_sweep`). -/
theorem exists_coverCharge_le (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (hrc : 1 ≤ rc)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c f : ℝ, 0 ≤ c ∧ 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ((chainCharge G R
          + Impl.sweepCharge G ((timedGreedyRoutine R) m G).order rc
              ⌈c * (m : ℝ) ^ δ⌉₊ : ℕ) : ℝ)
          ≤ f * (m : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨c, hc0, hdeg⟩ :=
    exists_wreach_degree_timedGreedyRoutine C hC rc R t ht hrt δ hδ
  obtain ⟨f₁, hf₁0, hf₁⟩ := exists_chainCharge_le_double C hC R δ hδ
  refine ⟨c, f₁ + 2 * (c + 1) * (c + 1), hc0, by positivity, ?_⟩
  intro n Gn hGn m G hsub
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [chainCharge_zero, Impl.sweepCharge,
      Real.zero_rpow (show (1 : ℝ) + 2 * δ ≠ 0 by positivity)]
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set Dd : ℕ := ⌈c * (m : ℝ) ^ δ⌉₊ with hDddef
  have hD := hdeg n Gn hGn m G hsub
  have hsw : Impl.sweepCharge G ((timedGreedyRoutine R) m G).order rc Dd
      ≤ 2 * Dd * (m * Dd) := Impl.sweepCharge_le hrc hD
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ δ := one_le_rpow hm hδ.le
  have hceil : ((Dd : ℕ) : ℝ) ≤ (c + 1) * (m : ℝ) ^ δ := by
    calc ((Dd : ℕ) : ℝ) ≤ c * (m : ℝ) ^ δ + 1 :=
          (Nat.ceil_lt_add_one
            (mul_nonneg hc0 (Real.rpow_nonneg (Nat.cast_nonneg m) δ))).le
      _ ≤ (c + 1) * (m : ℝ) ^ δ := by nlinarith [hX1, hc0]
  have hpow : (m : ℝ) ^ (1 + 2 * δ) = (m : ℝ) * ((m : ℝ) ^ δ * (m : ℝ) ^ δ) := by
    rw [show (1 : ℝ) + 2 * δ = 1 + (δ + δ) by ring, Real.rpow_add hm0, Real.rpow_one,
      Real.rpow_add hm0]
  calc ((chainCharge G R
        + Impl.sweepCharge G ((timedGreedyRoutine R) m G).order rc Dd : ℕ) : ℝ)
      = (chainCharge G R : ℝ)
        + ((Impl.sweepCharge G ((timedGreedyRoutine R) m G).order rc Dd : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ f₁ * (m : ℝ) ^ (1 + 2 * δ)
        + 2 * ((c + 1) * (m : ℝ) ^ δ) * ((m : ℝ) * ((c + 1) * (m : ℝ) ^ δ)) := by
        refine add_le_add (hf₁ n Gn hGn m G hsub) ?_
        calc ((Impl.sweepCharge G ((timedGreedyRoutine R) m G).order rc Dd : ℕ) : ℝ)
            ≤ ((2 * Dd * (m * Dd) : ℕ) : ℝ) := by exact_mod_cast hsw
          _ = 2 * ((Dd : ℕ) : ℝ) * ((m : ℝ) * ((Dd : ℕ) : ℝ)) := by push_cast; ring
          _ ≤ 2 * ((c + 1) * (m : ℝ) ^ δ) * ((m : ℝ) * ((c + 1) * (m : ℝ) ^ δ)) := by
              gcongr
    _ = (f₁ + 2 * (c + 1) * (c + 1)) * (m : ℝ) ^ (1 + 2 * δ) := by rw [hpow]; ring

open Classical in
/-- The capstone, read on the slot's ledger: the total of `coverC`'s
two entries — the whole charge vector, by `coverC_toFun_ne` — is at
most `f·m^{1+2δ}`, the degree parameter derived from the class. -/
theorem exists_coverC_total_le (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (hrc : 1 ≤ rc)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c f : ℝ, 0 ≤ c ∧ 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (((coverC m G rc R ⌈c * (m : ℝ) ^ δ⌉₊).toFun "cover.order"
          + (coverC m G rc R ⌈c * (m : ℝ) ^ δ⌉₊).toFun "cover.sweep" : ℕ) : ℝ)
          ≤ f * (m : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨c, f, hc0, hf0, h⟩ := exists_coverCharge_le C hC rc R t ht hrt hrc δ hδ
  refine ⟨c, f, hc0, hf0, fun n Gn hGn m G hsub => ?_⟩
  rw [coverC_toFun_order, coverC_toFun_sweep]
  exact h n Gn hGn m G hsub

end Lax3Proofs.Prog
