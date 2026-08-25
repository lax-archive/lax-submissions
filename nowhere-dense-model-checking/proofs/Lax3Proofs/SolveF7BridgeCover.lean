import Lax3Proofs.SolveF7Bridge
import Lax3Proofs.ProgCoverChargeDeg
import Lax3Proofs.SolveAugRoundIn

/-!
# F7-b — the cover column of `KsChargeBridge`, at the machine's own budget

`SolveF7Bridge` discharges `SolveChain.KsChargeBridge` at the pinned
`chainKB` with the cover stage's budget left abstract, behind two named
hypotheses (`hKcov` at admissible edged arenas, `hKcovBot` at edgeless
ones).  This file removes both, at the budget the machine actually
spends: `SolveSweepPeel.peelK` at the ordering routine
`selOrderingRoutine bucketSel (3·S.R)`, against the ledger column
`coverCFSel bucketSel S cf (headlineδ S ε)`.

## Why the two clauses need different arguments

The landed column bound
`ProgCoverChargeDeg.exists_mcChargeMS_T_bucket_coverColumn` (clause 3)
holds **at every node whose arena embeds in the input** — `A.G ⊑ G`.
That is a fact about the arenas the run reaches, and
`SolveAugRoundIn.ardIsContained_of_chainAdm` delivers it from the pinned
admissibility predicate — but only on arenas *with an edge* (`Inv`'s
disjunct is `A.G = ⊥` or a reached round).  So:

* the **edged** clause is the landed column bound, routed through
  `chainAdm`.  This is exactly why `b7_chainKB_le` asks for `hKcov` at
  admissible arenas rather than at all of them: a universally quantified
  `hKcov` is a hypothesis this bound cannot supply.
* the **edgeless** clause needs no ledger column at all, and is proved
  here outright, with no hypothesis: at `A.G = ⊥` every cluster is a
  singleton and every back-degree is `0`, so

      peelK a b c S A π = (a + b) · A.N        (§1)

  and the `⊥`-subtree bound of `SolveF7Bridge` §5 has what it needs.
  This is the concrete instance of that section's `hKcovBot`, and it
  settles the audit's item (1) in the affirmative for the machine's own
  cover budget rather than for a placeholder.

The glue slot is taken at the constant the landed glue contract asks for
— `SolveF7Adm.chainKB_frameStep_hKB`'s `hglue` is `6 ≤ Kglue k j A` — so
`Kglue := fun _ _ _ => 6` meets both that contract and this file's
`hKglue` at `cglue = 6`.

## What is left

`b7c_KsChargeBridge_bucket` carries the ledger's own `(cf, c', T)` and
the bridge together, on every member of the class, with exactly one
hypothesis left standing: `hKrl`, the root load's budget, which is a
residual of `RootLoadSpec` and not of the ledger comparison.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.CoverRoutine
open Lax13Proofs.Refine (ACost)

variable {L n₀ : ℕ}

/-! ## §1 `peelK` on an edgeless arena

All three figures collapse: the carrier stays, each cluster is the
singleton `{u}` (`Driver.cluster_eq_singleton_of_isolated`), and every
back-degree `d_<` is `0` because there are no neighbours at all. -/

open Classical in
/-- Every cluster below an edgeless node is a singleton, so the cluster
mass is the carrier. -/
theorem b7c_clusterMass_of_bot (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (hbot : A.G = ⊥) :
    clusterMass S A π = A.N := by
  have h : ∀ u : Fin A.N, (cluster S A π u).ncard = 1 := by
    intro u
    rw [cluster_eq_singleton_of_isolated S A π
      (fun z hz => by simp [hbot] at hz), Set.ncard_singleton]
  simp only [clusterMass, h]
  simp

open Classical in
/-- `d_<(w) = 0` on an edgeless arena, so the peel's edge work vanishes.
This is the figure §7's envelope prices the BFS at; it is the one that
could have been quadratic, and at `⊥` it is `0`. -/
theorem b7c_peelEdgeWork_of_bot (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (hbot : A.G = ⊥) :
    peelEdgeWork S A π = 0 := by
  simp only [peelEdgeWork]
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun w _ => ?_
  refine Nat.le_zero.mp ?_
  have hsub : Impl.Nlt A.G π w ⊆ ∅ := by
    intro z hz
    rw [Impl.Nlt, Finset.mem_filter, SimpleGraph.mem_neighborFinset, hbot] at hz
    exact hz.1.elim
  simpa [Impl.dlt] using Finset.card_le_card hsub

open Classical in
/-- **The peel budget on an edgeless arena is `(a+b)·A.N`** — linear in
the carrier, with a schedule constant, and with no edge figure left. -/
theorem b7c_peelK_of_bot (a b c : ℕ) (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (hbot : A.G = ⊥) :
    peelK a b c S A π = (a + b) * A.N := by
  simp only [peelK, b7c_clusterMass_of_bot S A π hbot,
    b7c_peelEdgeWork_of_bot S A π hbot]
  ring

open Classical in
/-- **`b7_KsChargeBridge`'s `hKcovBot`, discharged at the machine's own
cover budget, with no hypothesis.**  The ledger has no cover column on
the `A.G = ⊥` branch of `frameChargeMS`, and none is needed: the peel
budget there is already a schedule constant times the carrier, which is
what `SolveF7Bridge` §5's `⊥`-subtree bound charges against `botC`. -/
theorem b7c_peelK_le_bot (a b c : ℕ) (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (hbot : A.G = ⊥) :
    peelK a b c S A π ≤ (a + b + c) * (A.N + 1) := by
  rw [b7c_peelK_of_bot a b c S A π hbot]
  exact Nat.mul_le_mul (by omega) (by omega)

/-! ## §2 The bridge at the machine's cover budget -/

open Lax11.GraphEncoding in
open Classical in
/-- **`KsChargeBridge` at the machine's own cover routine, ledger column
and peel budget**, on every member of the class.

The `(cf, c', T)` are the landed
`exists_mcChargeMS_T_bucket_coverColumn`'s, so the ledger bound of
clause 2 and the cover column of clause 3 are carried at the *same*
constant as the bridge — which is what lets this be chained with the
axiom's time clause without a second constant.

Both cover hypotheses of `b7_KsChargeBridge` are discharged here: the
edged one from clause 3 through `ardIsContained_of_chainAdm`, the
edgeless one from §1 outright.  `hbotK` is `SolveF7Bridge` §8's
`b7_botK_le`, the channel bound is the canonical `2R+1`, the glue slot
is the landed contract's own `6`, and admissibility is the pinned
`chainAdm` with its two hypothesis-free clauses.  What remains is
`hKrl` alone. -/
theorem b7c_KsChargeBridge_bucket
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) (Kq a b c : ℕ)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hG : C n G) (cw ww : ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (Krl : List ℕ → ℕ) (Kc crl : ℕ) (av : ScatterSentence 0 → Expr)
    (hKrl : ∀ x ∈ mcD n G cw ww, Krl x ≤ crl * (x.length + 1)) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 1 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      (∀ (col : Coloring n 0) (x : List ℕ), EncodesGraph x n G →
        chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ)
            (selOrderingRoutine (fun m => bucketSel m)
              (3 * (Headline.headlineSetup C hC φ).R)) ℓp htabF
            (coverCFSel (fun m => bucketSel m)
              (Headline.headlineSetup C hC φ) cf
              (headlineδ (Headline.headlineSetup C hC φ) ε)) G col) ≤ T x) ∧
      KsChargeBridge C hC φ
        (selOrderingRoutine (fun m => bucketSel m)
          (3 * (Headline.headlineSetup C hC φ).R)) G cw ww ℓp htabF
        (coverCFSel (fun m => bucketSel m) (Headline.headlineSetup C hC φ) cf
          (headlineδ (Headline.headlineSetup C hC φ) ε))
        (fun x => matK x + (Krl x +
          (chainKB (Headline.headlineSetup C hC φ)
              (selOrderingRoutine (fun m => bucketSel m)
                (3 * (Headline.headlineSetup C hC φ).R)) Kq ℓp
              (fun _ => 2 * (Headline.headlineSetup C hC φ).R + 1)
              (fun _ A => peelK a b c (Headline.headlineSetup C hC φ) A
                ((selOrderingRoutine (fun m => bucketSel m)
                    (3 * (Headline.headlineSetup C hC φ).R)) A.N A.G).order)
              (fun _ _ _ => 6)
              (Headline.headlineSetup C hC φ).depth 0
              (rootArena G (Impl.trivialColoring n)) +
            (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))) := by
  obtain ⟨cf, c', T, hcf1, hc'0, hT, hledger, hcol⟩ :=
    exists_mcChargeMS_T_bucket_coverColumn C hC φ hε ℓp
  refine ⟨cf, c', T, hcf1, hc'0, hT,
    fun col x hx => hledger n G hG col htabF x hx, ?_⟩
  refine b7_KsChargeBridge C hC φ _ G cw ww Kq ℓp _ htabF _ _ _ Krl Kc av
    (b7BotK (Headline.headlineSetup C hC φ) Kq) (a + b + c) 6 crl
    (chainAdm (Headline.headlineSetup C hC φ) G)
    (headlineSetup_chainAdm_root C hC φ G)
    (headlineSetup_chainAdm_admChild C hC φ _ G)
    (fun _ => rfl)
    (b7_botK_le (Headline.headlineSetup C hC φ) Kq)
    (fun i A hi hAdm hbot => ?_) (fun i A hbot => ?_)
    (fun k i A => by omega) hKrl
  · refine le_trans
      (hcol n G hG i A (ardIsContained_of_chainAdm hi hAdm hbot) a b c) ?_
    exact Nat.mul_le_mul_left (a + b + c) (by omega)
  · exact b7c_peelK_le_bot a b c _ A _ hbot

/-! ## §3 Axiom profile -/

#print axioms b7c_clusterMass_of_bot
#print axioms b7c_peelEdgeWork_of_bot
#print axioms b7c_peelK_of_bot
#print axioms b7c_peelK_le_bot
#print axioms b7c_KsChargeBridge_bucket

end Lax3Proofs.Prog
