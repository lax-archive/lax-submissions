import Lax3Proofs.ProgCharge

/-!
# F6b (part 3) — the frame program at the multi-source profile budget

F3c's finding 1 (`ProgCharge`'s module docstring): with `ProgFrame`'s
landed profile stage — the `NRest.spec` whose budget is the
iterated-route `profilesC` — the comparison of the program's ledger
against the abstract cost shape is **false** in the colour column, and
`ProgCharge` therefore prices the honest budget `frameChargeMS` with
that one column swapped to F3b's multi-source account `profilesCMS`.
What was still missing is the **program** at that budget: `frameCharge`
is only ever spent by `frameProg`, whose profile stage still advertises
`profilesC`.

This file is the reroute. `frameProgMS` is `ProgFrame.frameProg` with
exactly one stage changed: the per-centre profile `NRest.spec` is
re-specced at the multi-source seam —

* postcondition `Impl.ProfileTablesMS` (`mb` batch tables plus **one
  virtual-source table per colour class**, `m + L` calls — §6.3's
  count) instead of `Impl.ProfileTables` (`m + Σ_c |f c|` calls);
* budget `profilesCMS` (F3b's `Impl.profilesChargeMS`) instead of
  `profilesC`;
* the row population `Impl.recordProfilesMS`, whose identity to the
  driver's child colours is `recordProfilesMS_eq_childCol` — the same
  statement as `recordProfiles_eq_childCol`, at the same seam (`preG`,
  before isolation — hazard 1 unchanged).

Everything else — restrict, supports, isolate, the two slots, the
fold, the readback, the leaf — is verbatim `ProgFrame`'s, and
`frameProgMS_le_spec` is the same statement as `frameProg_le_spec` at
the `frameChargeMS` budget. The slot interfaces are `ProgFrame`'s own
(`hcover` for the cover slot, `hnx` for the recursion slot, `hcol` and
`hchoice` threaded), so a driver built on this frame consumes the MS
budget end to end with no interface change; on every currency except
`"frame.profiles"` the advertised budget is the landed one, entry by
entry (`frameChargeMS_toFun_eq` — F3c's users' lemma).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Refine
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun

variable {L n₀ : ℕ}

/-! ## The per-centre pipeline, profile stage rerouted -/

open Classical in
/-- **The per-centre body at the multi-source profile seam** —
`ProgFrame.centreProg` with exactly the profile stage changed: the
`NRest.spec` holds `mb` batch tables plus one virtual-source table per
colour class (`Impl.ProfileTablesMS`, `m + L` BFS calls), for the
multi-source budget `profilesCMS`, and the rows are populated by
`Impl.recordProfilesMS`. Every other stage is verbatim `centreProg`'s. -/
noncomputable def centreProgMS (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
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
  -- the `m + L` profile BFS calls (multi-source), at `B₀` — BEFORE
  -- isolation (hazard 1 unchanged: the seam is stated at `preG`)
  NRest.bindT (NRest.spec
      (fun DD : (Fin S.width → Fin B₀.N → ℕ) ×
          (Fin (relPal (S.pal j)) → Fin (B₀.N + 1) → ℕ) =>
        Impl.ProfileTablesMS B₀.G (batchFn S A π u)
          (childColR S A π u) S.R DD.1 DD.2)
      fun _ => liftACost (profilesCMS S j A π u)) fun DD =>
  -- `recordProfilesMS`: populate the rows off the `m + L` arrays
  NRest.bindT (NRest.returnT
      (Impl.recordProfilesMS S.R (childColR S A π u) DD.1 DD.2)) fun colC =>
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

/-- The refinement of the MS per-centre body: same statement as
`centreProg_le_spec`, at the `centreChargeMS` budget — the profile
postcondition is discharged into the driver's child colours by
`recordProfilesMS_eq_childCol` instead of `recordProfiles_eq_childCol`;
everything else is the landed proof verbatim. -/
theorem centreProgMS_le_spec (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    {nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost}
    {nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop}
    {nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ}
    (hnx : ∀ B, nxProg B ≤ NRest.spec (fun T => T = nx B) fun _ => liftACost (nxC B))
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    centreProgMS S j A htab nxProg π u ≤
      NRest.spec (fun Tu : ChildTab S j A π u => Tu = nx (childArena S A π u))
        (fun _ => liftACost (centreChargeMS S j A ℓp htab nx nxC π u)) := by
  rw [centreProgMS, centreChargeMS]
  simp only [liftACost_add]
  -- restrict
  refine bindT_le_spec (consume_returnT_le_spec (P := fun _ => True) trivial _)
    fun _ _ => ?_
  -- supports
  refine bindT_le_spec le_rfl fun _DT _ => ?_
  -- profiles, at the multi-source seam
  refine bindT_le_spec le_rfl fun DD hDD => ?_
  -- recordProfilesMS is a pure step
  rw [NRest.returnT_bindT]
  -- under the MS seam, the recorded coloring IS the driver's child
  -- colors (hazard 1: `recordProfilesMS_eq_childCol` is stated at `preG`)
  have hcolC : Impl.recordProfilesMS S.R (childColR S A π u) DD.1 DD.2
      = childCol S A π u :=
    Impl.recordProfilesMS_eq_childCol S A π u hDD
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

/-- One fold step at the MS profile stage: run the per-centre body,
write its table at `u` — `ProgFrame.foldBody` at `centreProgMS`. -/
noncomputable def foldBodyMS (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (acc : Tabs S j A π) :
    NRest (Tabs S j A π) ECost :=
  NRest.bindT (centreProgMS S j A htab nxProg π u) fun Tu =>
    NRest.returnT (Function.update acc u Tu)

/-- The MS fold's refinement — `ProgFrame.fold_le_spec` verbatim, at
the `centreChargeMS` per-centre charges. -/
theorem foldMS_le_spec (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    {ℓp : ℕ} (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    {nxProg : (B : Arena (S.pal (j + 1)) n₀) →
      NRest (Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop) ECost}
    {nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → DistFO (S.pal (j + 1)) 1 → Prop}
    {nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ}
    (hnx : ∀ B, nxProg B ≤ NRest.spec (fun T => T = nx B) fun _ => liftACost (nxC B))
    (π : Equiv.Perm (Fin A.N)) :
    ∀ (l : List (Fin A.N)) (acc : Tabs S j A π),
      NRest.nfoldli (fun _ => true) (foldBodyMS S j A htab nxProg π) l acc ≤
        NRest.spec
          (fun T : Tabs S j A π => ∀ u : Fin A.N,
            (u ∈ l → T u = nx (childArena S A π u)) ∧ (u ∉ l → T u = acc u))
          (fun _ => liftACost ((l.map (centreChargeMS S j A ℓp htab nx nxC π)).sum)) := by
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
      rw [foldBodyMS]
      have h := bindT_le_spec (centreProgMS_le_spec S j A htab hnx π u)
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

/-! ## The frame at the MS budget -/

open Classical in
/-- **The frame program at the multi-source profile budget** —
`ProgFrame.frameProg` with the per-centre profile stage rerouted
(`centreProgMS`); the leaf branch, the cover slot, the scratch
allocation and the readback are verbatim. This is the program whose
advertised budget is `ProgCharge.frameChargeMS` — the vector the
per-node comparison `frameChargeMS_chargeTotal_le` prices. -/
noncomputable def frameProgMS (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
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
    NRest.bindT (NRest.nfoldli (fun _ => true) (foldBodyMS S j A htab nxProg π)
      (List.finRange A.N) fun _ => fun _ _ => True) fun T =>
    -- the write-once readback (§5 lines 24–28)
    NRest.consume (NRest.returnT (readback S j A π T)) (liftACost (readC S j A))

/-- **The MS frame's refinement theorem — `frameProg_le_spec`'s exact
statement at the `frameChargeMS` budget.** The hypotheses are
`ProgFrame`'s own slot interfaces, unchanged: the row hypothesis
`hcol`, the canonical scatter choice `hchoice`, the cover slot's
spec-and-charge pair `hcover`, the recursion slot's `hnx`. A driver
recursion wired to this frame therefore consumes the multi-source
budget end to end with no interface change; the profile column is the
only budget entry that moved (`frameChargeMS_toFun_eq`). -/
theorem frameProgMS_le_spec (S : Setup L) (ord : CoverSpec.OrderingRoutine)
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
    frameProgMS S j A htab colB coverProg nxProg ≤
      NRest.spec (fun T => T = Unroll.frameEval S ord j nx A)
        (fun _ => liftACost (frameChargeMS S ord j A ℓp htab nx covC nxC)) := by
  rw [frameProgMS, frameChargeMS]
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
      (foldMS_le_spec S j A htab hnx ((ord A.N A.G).order) (List.finRange A.N)
        (fun _ => fun _ _ => True))
      fun T hT => ?_
    -- the readback
    refine consume_returnT_le_spec
      (P := fun T => T = Unroll.frameEval S ord j nx A) ?_ _
    exact readback_eq_frameEval S ord j A hbot hchoice
      fun u => (hT u).1 (List.mem_finRange u)

end Lax3Proofs.Prog
