import Lax3Proofs.SolveMachPrepAll

/-!
# F6c12 (residual 1) — the `CLInv` scratch seam, resolved

`SolveMachPrepAll` §6 pinned the one seam that stood between the landed
prep pieces and `ChildLoadPartsAll`:

> `restrictCom_specW`'s precondition carries a **content** clause —
> `(σ.arrs ra).take A.N = arrOf A.N (fun _ => 0)`, a clean rank
> scratch — on an array outside `levelArrays j`. `CLInv`
> (`SolveGlueLoop`) offers exactly one slot for such a clause, the
> scratch descriptor `Scr j` inside `BlockPre`; but
> `centrePrep_of_childLoad` (`SolveSegPrep`) and
> `centrePrepAll_of_parts_chanTab` (`SolveMachPrepPins` §7) both
> transport `Scr` with `hscrLen`, which is **length-only**.

This file resolves it, additively: nothing landed is edited, and the
`CentrePrepAll` corollary is reproduced with **no `hscrLen` hypothesis
at all**.

## §1 The clause, named — and the first escape, refuted

`RankScr ra nN` is the clean-window clause read at the level's own
carrier cell: `(σ.arrs ra).take (σ.vars nN) = arrOf (σ.vars nN) 0`.
Two small lemmas make it exactly the interface `restrictCom_specW`
speaks (`rankScr_take` in, `rankScr_of_take` out, both through
`ArenaStW.n_eq`), and `rankScr_frame` is the shape every *other*
transport in the chain needs (array equality, not lengths).

`rankScr_not_length_only` is the escape's refutation, as a theorem: a
`Scr` that implies `RankScr` and satisfies `hscrLen`'s `∀ σ σ'`
length-only shape is **inconsistent** — flip one cell of the scratch
and the lengths are unchanged. So "carry the clause in `Scr` and keep
`hscrLen`" is not a trade-off, it is a contradiction; the transport
must change.

## §2–§4 The change: the pass re-establishes the descriptor

The pass *does* restore the scratch — `restrictCom_specW` returns
`(σ'.arrs ra).take A.N = arrOf A.N (fun _ => 0)` verbatim, cleaning
only the `|S|` entries it touched (§6.1: "one scratch array per node,
cleared only at the touched entries, never one per child"). So the
descriptor is re-establishable **from the pass's own postcondition**,
and the smallest way to say so is to put it there:

* **`ChildLoadScr`** is `ChildLoad` with `Scr j σ'` conjoined to the
  postcondition, and **`ChildLoadPartsScr`** is `ChildLoadParts` with
  the same conjunct. Both weaken back (`childLoad_of_childLoadScr`,
  `childLoadParts_of_partsScr`), so nothing downstream is deprived.
* **`clInv_frame_scr`** is `clInv_frame` (`SolveStep`) with the
  descriptor handed in instead of transported — and it then needs no
  length clause either, because `BlockPre`'s table bound rides the
  level's own array frame.
* **`centrePrep_of_childLoadScr`** concludes verbatim `CentrePrep`
  from `ChildLoadScr` with **`hscrDown` and `htabLen` only**; the
  child's `Scr (j+1)` is `hscrDown` applied at `σ'`, not at `σ`, so
  the length-only transport disappears from the prep segment
  altogether. `centrePrepAll_of_partsScr_chanTab` (§4) is the whole
  corollary at the canonical channel witness: verbatim
  `CentrePrepAll` from `ChildLoadPartsScrAll`, `hscrDown`, `htabLen`.

**Why not the other shape.** The alternative the seam note floated —
keep `ChildLoadParts` as it is and replace `hscrLen` at its use sites
by a transport that also receives the pass's frame and restoration
facts — is strictly larger and leaks layout. That hypothesis has to
*name* the scratch array and *spell* its window in the signatures of
`centrePrep_of_childLoad`, `centrePrepAll_of_childLoad`,
`centrePrepAll_of_parts` and `centrePrepAll_of_parts_chanTab`, so four
landed statements grow a `ra`/`nN` parameter pair and a four-premise
hypothesis, and the corollary — which has no business knowing which
array the restrict stage ranks into — becomes layout-dependent.
Conjoining `Scr j σ'` says the same thing in one clause, keeps `Scr`
abstract, and leaves the naming where it belongs: with the discharger
of `ChildLoadPartsScrAll`, which holds the `Run` and can frame
whatever it likes. §5 records the obligation that move hands the
discharger, and §6 the ones it does **not** discharge, by name.

## §5 Nothing regressed

`childLoadPartsScr_of_parts` derives the strengthened residual from
the landed one plus `hscrLen`: any `Scr` that could be used before can
be used now, so the strengthening is free for a length-only
descriptor and is paid for only by a descriptor that actually carries
`RankScr`.

## §6 What the resolution does *not* reach

`hscrLen` still stands, unchanged, at five sites outside the prep
segment:

* `clInv_setVar_ctr` / `centreLoop_of_step` (`SolveGlueLoop` §1, §3) —
  the counter bump, where the arrays are literally the same list;
* `frameElse_of_cover_loop` (`SolveGlueStep` §3) — across the cover
  stage;
* `centreStep_of_prep_read` (`SolveStep` §3) — across the inner block,
  through `clInv_frame`;
* `centreRead_of_rows` (`SolveSegRead` §5) — across the return path;
* `hscrLen0` in `solveSpec_of_chain` (`SolveChain`) and
  `solveSpec_closed` (`SolveFrameBridge`) — the root load.

By §1 a `RankScr`-carrying `Scr` cannot satisfy any of them, so those
five need the same move, and `rankScr_frame` is the shape it takes:
none of the five *writes* the level's scratch, so array equality is
the honest premise where length equality is currently asked for. It is
available for free at the first and third (the counter bump changes no
array at all; the inner block is owned from `j + 1`, so `Run.frame`
gives it); at the second and fourth it has to be *stated*, because
`CoverAll` and `ReadRows` frame only `ca/co/cm :: levelArrays j` and
say nothing about an array outside that pool. That is a separate leaf,
on files this one does not own; what this file does is remove the
obstruction from the prep segment and state the remaining five, so
that nobody has to rediscover them.

## Hazards honoured

Nothing here moves a stage, a radius or a budget: no program is
defined, no cost is claimed, and `prepPassK`/`prepPassK_le` are
untouched — in particular **no `A.N` term** is introduced anywhere,
which is the whole reason the clean scratch may not be wiped inside
`prepC` (§6.1's `Θ(A.N²)` trap).
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The rank scratch's clean window, named -/

/-- **The clean rank scratch**, at the level's own carrier window: the
scratch array `ra` is all zeros on the prefix the level's carrier cell
`nN` names. This is the clause `restrictCom_specW` asks for and the
clause it returns — see `rankScr_take` and `rankScr_of_take` — and it
is the one *content* clause the child-building pass needs from the
loop invariant.

Reading the window off the cell rather than off `n₀` is what makes the
clause re-establishable: `restrictCom_specW` windows the scratch at
exactly `A.N`, so it restores exactly `take A.N` and says nothing about
the allocation beyond it. -/
def RankScr (ra nN : String) (σ : Env) : Prop :=
  (σ.arrs ra).take (σ.vars nN) = arrOf (σ.vars nN) (fun _ => 0)

section RankScrFacts

variable {Λ ℓp hb : ℕ} {ra : String} {nm : ArenaNames}

/-- **The clause, at `restrictCom_specW`'s spelling (in).** Under the
level's windowed contract the carrier cell *is* the carrier
(`ArenaStW.n_eq`), so the descriptor's clause is verbatim the lift's
content precondition. -/
theorem rankScr_take {A : Impl.MArena Λ n₀ ℓp} {σ : Env}
    (hA : ArenaStW nm hb A σ) (h : RankScr ra nm.nN σ) :
    (σ.arrs ra).take A.N = arrOf A.N (fun _ => 0) := by
  have hn : σ.vars nm.nN = A.N := hA.n_eq
  rw [← hn]
  exact h

/-- **The clause, at `restrictCom_specW`'s spelling (out).** The same
identification run backwards: the lift's *postcondition* re-establishes
the descriptor's clause. This is the whole of the third way — the pass
restores the scratch, and here that restoration is the clause. -/
theorem rankScr_of_take {A : Impl.MArena Λ n₀ ℓp} {σ : Env}
    (hA : ArenaStW nm hb A σ)
    (h : (σ.arrs ra).take A.N = arrOf A.N (fun _ => 0)) :
    RankScr ra nm.nN σ := by
  have hn : σ.vars nm.nN = A.N := hA.n_eq
  rw [RankScr, hn]
  exact h

/-- **The transport the clause really has**: agreement on the scratch
array and on the carrier cell. Every place in the chain where the
level's scratch is *untouched* — the counter bump, the cover stage, the
inner block, the return path — has this available; only the
child-building pass, which writes the scratch and restores it, does
not. -/
theorem rankScr_frame {nN : String} {σ σ' : Env} (h : RankScr ra nN σ)
    (harr : σ'.arrs ra = σ.arrs ra) (hvar : σ'.vars nN = σ.vars nN) :
    RankScr ra nN σ' := by
  rw [RankScr, harr, hvar]
  exact h

end RankScrFacts

/-- **The first escape, refuted.** `SolveMachPrepAll` §6 recorded that
carrying the clean-scratch clause in `Scr` "forfeits the
`CentrePrepAll` corollary". It is worse than that: a descriptor that
implies `RankScr` and satisfies `hscrLen`'s length-only `∀ σ σ'` shape
is outright **inconsistent** at any state whose window is non-empty —
flipping one cell of the scratch preserves every array's length, so
`hscrLen` would carry the clause to a state that plainly fails it.

So the two are not a trade-off to be balanced: `hscrLen` must go from
the prep segment, which is what §2–§4 do. -/
theorem rankScr_not_length_only {ra nN : String} {Scr : ℕ → Env → Prop}
    {j : ℕ}
    (hscrLen : ∀ σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hclean : ∀ σ, Scr j σ → RankScr ra nN σ)
    {σ : Env} (h : Scr j σ) (hpos : 0 < σ.vars nN)
    (hfit : σ.vars nN ≤ (σ.arrs ra).length) : False := by
  -- one cell of the scratch, flipped: same lengths, dirty window
  have hlen : ∀ b, ((σ.setArr ra 0 1).arrs b).length = (σ.arrs b).length := by
    intro b
    rw [arrs_setArr]
    by_cases hb : b = ra
    · subst hb; rw [if_pos rfl, List.length_set]
    · rw [if_neg hb]
  have hbad : RankScr ra nN (σ.setArr ra 0 1) :=
    hclean _ (hscrLen σ _ h hlen)
  have hzero : ((σ.arrs ra).set 0 1).take (σ.vars nN) = arrOf (σ.vars nN)
      (fun _ => 0) := by
    have := hbad
    rw [RankScr, arrs_setArr, if_pos rfl, vars_setArr] at this
    exact this
  have hlt : (0 : ℕ) < (σ.arrs ra).length := by omega
  have h1 : (((σ.arrs ra).set 0 1).take (σ.vars nN)).getD 0 0 = 1 := by
    rw [getD_take_of_lt hpos, List.getD_eq_getElem?_getD,
      List.getElem?_set_self hlt]
    rfl
  rw [hzero, getD_arrOf _ hpos] at h1
  exact absurd h1 (by decide)

/-! ## §2 `CLInv`, with the descriptor supplied -/

/-- **`clInv_frame` with the scratch descriptor handed in.** The landed
`clInv_frame` (`SolveStep`) transports every component of `CLInv` along
the level's own frame and re-derives `Scr j` from lengths alone. This
variant takes `Scr j σ'` as a premise instead — and then wants no
length clause at all, because `BlockPre`'s table bound rides the frame
on `(arenaNames j).tab`, which is already in the level's array pool.

This is the one step that lets a pass which *writes and restores* an
array outside `levelArrays j` still carry the loop invariant. -/
theorem clInv_frame_scr {S : Setup L} {ord : CoverSpec.OrderingRoutine}
    {ℓp : ℕ → ℕ}
    {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {hbf : ℕ → ℕ} {Scr : ℕ → Env → Prop} {ca co cm : ℕ → String}
    {k j : ℕ} {A : Arena (S.pal j) n₀} {m : ℕ} {σ σ' : Env}
    (hscr' : Scr j σ')
    (h : CLInv S ord ℓp htabF hbf Scr ca co cm k j A m σ)
    (hvN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN)
    (hvS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS)
    (harrs : ∀ a ∈ ca j :: co j :: cm j :: levelArrays j,
      σ'.arrs a = σ.arrs a) :
    CLInv S ord ℓp htabF hbf Scr ca co cm k j A m σ' := by
  obtain ⟨⟨hA, htab, -⟩, hctr, hcsr, hpart⟩ := h
  have hca : σ'.arrs (ca j) = σ.arrs (ca j) := harrs _ (by simp)
  have hco : σ'.arrs (co j) = σ.arrs (co j) := harrs _ (by simp)
  have hcm : σ'.arrs (cm j) = σ.arrs (cm j) := harrs _ (by simp)
  have hoff := harrs ((arenaNames j).off) (by simp [levelArrays])
  have htgt := harrs ((arenaNames j).tgt) (by simp [levelArrays])
  have hcol := harrs ((arenaNames j).col) (by simp [levelArrays])
  have hup := harrs ((arenaNames j).up) (by simp [levelArrays])
  have hhist := harrs ((arenaNames j).hist) (by simp [levelArrays])
  have htabeq := harrs ((arenaNames j).tab) (by simp [levelArrays])
  refine ⟨⟨arenaStW_of_eq hA hvN hvS hoff htgt hcol hup hhist, ?_, hscr'⟩,
    ctrArr_of_eq hctr hca, clusterCsr_of_eq hcsr hco hcm,
    tablePartial_of_eq hpart htabeq⟩
  rw [htabeq]
  exact htab

/-! ## §3 The pass, with the descriptor re-established -/

/-- **The child-building pass, with the level's scratch descriptor
restored.** Verbatim `ChildLoad` (`SolveSegPrep` §1) with one conjunct
added to the postcondition: the pass leaves the level's own descriptor
standing. That is a claim the pass can *make* — the restrict stage
returns its rank scratch clean (`restrictCom_specW`), and every later
stage of the pass leaves it alone — and it is exactly what
`centrePrep_of_childLoadScr` needs in place of a length-only
transport. -/
def ChildLoadScr (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + (k + 1) = S.depth →
    Adm j A → ¬ A.G = ⊥ → ∀ u : Fin A.N,
    Spec B
      (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
        σ.vars (ctrName j) = (u : ℕ))
      (prepC j)
      (fun σ σ' =>
        ArenaStW (arenaNames (j + 1)) (hbf (j + 1))
          (Impl.ofArena (childArena S A ((ord A.N A.G).order) u)
            (htabF (j + 1) (childArena S A ((ord A.N A.G).order) u))) σ' ∧
        Scr j σ' ∧
        (∀ y ∈ ctrName j :: levelScalars j, σ'.vars y = σ.vars y) ∧
        (∀ a ∈ ca j :: co j :: cm j :: levelArrays j, σ'.arrs a = σ.arrs a) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (KP k j A (u : ℕ))

/-- The strengthened pass weakens back to the landed one: nothing that
consumes `ChildLoad` is deprived. -/
theorem childLoad_of_childLoadScr (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (h : ChildLoadScr B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP) :
    ChildLoad B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP := by
  intro k j A hdiag hAdm hbot u
  refine (h k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' - ⟨hAW, -, hframe⟩
  exact ⟨hAW, hframe⟩

open Classical in
/-- **`CentrePrep` from the restoring pass — with no length-only
transport.** The invariant crosses by `clInv_frame_scr` on the pass's
own descriptor claim; the counter clause is the frame's; the child's
`BlockPre` is assembled from the deliverable, the table allocation
(`htabLen`, now read at `σ'` because the descriptor already stands
there) and the descriptor tower (`hscrDown`, applied at `σ'`).

Compare `centrePrep_of_childLoad` (`SolveSegPrep` §2): the only
hypothesis that disappears is `hscrLen`, and it disappears because the
pass supplies what it used to derive. -/
theorem centrePrep_of_childLoadScr (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    -- the descriptor tower: level `j`'s descriptor carries the deeper
    -- level's, wherever the chain still descends
    (hscrDown : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ → Scr (j + 1) σ)
    -- the level-`(j+1)` table allocation, at the root carrier
    (htabLen : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ →
      n₀ * (levelFml S (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hload : ChildLoadScr B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP) :
    CentrePrep B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP := by
  intro k j A hdiag hAdm hbot u
  refine (hload k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' ⟨hCL, -⟩ ⟨hAW, hscr', hvars, harrs, -⟩
  refine ⟨clInv_frame_scr hscr' hCL
      (hvars _ (by simp [levelScalars])) (hvars _ (by simp [levelScalars]))
      harrs,
    hvars _ (by simp), hAW, ?_, ?_⟩
  · -- the child's table allocation: below the root carrier, off the
    -- descriptor the pass itself left standing
    calc (childArena S A ((ord A.N A.G).order) u).N
          * (levelFml S (j + 1)).length
        ≤ n₀ * (levelFml S (j + 1)).length :=
          Nat.mul_le_mul_right _ (arenaN_le _)
      _ ≤ (σ'.arrs (arenaNames (j + 1)).tab).length :=
          htabLen j (by omega) σ' hscr'
  · -- the child's scratch descriptor: the tower's, at the exit state
    exact hscrDown j (by omega) σ' hscr'

/-- The restoring pass, quantified per admissible input. -/
def ChildLoadScrAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    ChildLoadScr (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      Adm Scr ca co cm prepC KP

open Classical in
/-- **Verbatim `CentrePrepAll` from the restoring pass** — the prep
segment's residual reduced to the machine pass plus the descriptor
tower's two facts, **with `hscrLen` gone**. -/
theorem centrePrepAll_of_childLoadScr (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hscrDown : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ σ, Scr j σ → Scr (j + 1) σ)
    (htabLen : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → ∀ σ,
      Scr j σ →
      n * (levelFml (Headline.headlineSetup C hC φ) (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hload : ChildLoadScrAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      prepC KP) :
    CentrePrepAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm prepC
      KP := by
  intro x hx
  exact centrePrep_of_childLoadScr (mcB q x) (Headline.headlineSetup C hC φ)
    ord ℓp htabF hbf Adm Scr ca co cm prepC KP hscrDown htabLen (hload x hx)

/-! ## §4 The same at the parts, and the corollary -/

open Classical in
/-- **The child-building pass at the parts, with the descriptor
restored** — verbatim `ChildLoadParts` (`SolveMachPrep` §4) with
`Scr j σ'` conjoined to the postcondition. This is the residual the
stage composition now owes. -/
def ChildLoadPartsScr (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) → (A : Arena (S.pal j) n₀) → (u : Fin A.N) →
      Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + (k + 1) = S.depth →
    Adm j A → ¬ A.G = ⊥ → ∀ u : Fin A.N,
    Spec B
      (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
        σ.vars (ctrName j) = (u : ℕ))
      (prepC j)
      (fun σ σ' =>
        (∃ (Dp : Fin S.width →
              Fin (childN S A ((ord A.N A.G).order) u) → ℕ)
           (Dc : Fin (relPal (S.pal j)) →
              Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ),
          Impl.ProfileTablesMS (preG S A ((ord A.N A.G).order) u)
            (batchFn S A ((ord A.N A.G).order) u)
            (childColR S A ((ord A.N A.G).order) u) S.R Dp Dc ∧
          ArenaStW (arenaNames (j + 1)) (hbf (j + 1))
            (machChild S A ((ord A.N A.G).order) u Dp Dc (chanF j A u))
            σ') ∧
        Scr j σ' ∧
        (∀ y ∈ ctrName j :: levelScalars j, σ'.vars y = σ.vars y) ∧
        (∀ a ∈ ca j :: co j :: cm j :: levelArrays j,
          σ'.arrs a = σ.arrs a) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (KP k j A (u : ℕ))

open Classical in
/-- The strengthened parts residual weakens back to the landed one. -/
theorem childLoadParts_of_partsScr (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) → (A : Arena (S.pal j) n₀) → (u : Fin A.N) →
      Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (h : ChildLoadPartsScr B S ord ℓp htabF hbf Adm Scr ca co cm prepC
      chanF KP) :
    ChildLoadParts B S ord ℓp htabF hbf Adm Scr ca co cm prepC chanF KP := by
  intro k j A hdiag hAdm hbot u
  refine (h k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' - ⟨hpost, -, hframe⟩
  exact ⟨hpost, hframe⟩

open Classical in
/-- **`ChildLoadScr` from the parts** — the assembly identity of
`SolveMachPrep` §4, carried across the added conjunct unchanged. -/
theorem childLoadScr_of_partsScr (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) → (A : Arena (S.pal j) n₀) → (u : Fin A.N) →
      Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (hhtab : ∀ (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N),
      htabF (j + 1) (childArena S A ((ord A.N A.G).order) u)
        = chanF j A u)
    (hparts : ChildLoadPartsScr B S ord ℓp htabF hbf Adm Scr ca co cm prepC
      chanF KP) :
    ChildLoadScr B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP := by
  intro k j A hdiag hAdm hbot u
  refine (hparts k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' - ⟨⟨Dp, Dc, hPT, hAW⟩, hscr', hframe⟩
  refine ⟨?_, hscr', hframe⟩
  rw [hhtab j A u, ← machChild_eq_ofArena S A ((ord A.N A.G).order) u
    (chanF j A u) hPT]
  exact hAW

/-- The parts residual with the descriptor restored, quantified per
admissible input. -/
def ChildLoadPartsScrAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      (u : Fin A.N) →
      Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) →
      Fin (ℓp (j + 1)) →
      List (Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    ChildLoadPartsScr (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF
      hbf Adm Scr ca co cm prepC chanF KP

open Classical in
/-- **`ChildLoadScrAll` from the parts**, per admissible input. -/
theorem childLoadScrAll_of_partsScr (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      (u : Fin A.N) →
      Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) →
      Fin (ℓp (j + 1)) →
      List (Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hhtab : ∀ (j : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) (u : Fin A.N),
      htabF (j + 1) (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) = chanF j A u)
    (hparts : ChildLoadPartsScrAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC chanF KP) :
    ChildLoadScrAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm prepC
      KP := by
  intro x hx
  exact childLoadScr_of_partsScr (mcB q x) (Headline.headlineSetup C hC φ)
    ord ℓp htabF hbf Adm Scr ca co cm prepC chanF KP hhtab (hparts x hx)

open Classical in
/-- **Verbatim `CentrePrepAll` from the parts, with the seam resolved.**
This is `SolveMachPrep.centrePrepAll_of_parts` with `hscrLen` removed:
the whole prep segment, from the parts residual plus the descriptor
tower's two facts and the channel seam. -/
theorem centrePrepAll_of_partsScr (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      (u : Fin A.N) →
      Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) →
      Fin (ℓp (j + 1)) →
      List (Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hscrDown : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ σ, Scr j σ → Scr (j + 1) σ)
    (htabLen : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → ∀ σ,
      Scr j σ →
      n * (levelFml (Headline.headlineSetup C hC φ) (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hhtab : ∀ (j : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) (u : Fin A.N),
      htabF (j + 1) (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) = chanF j A u)
    (hparts : ChildLoadPartsScrAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC chanF KP) :
    CentrePrepAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm prepC
      KP :=
  centrePrepAll_of_childLoadScr C hC φ ord G c w q ℓp htabF hbf Adm Scr
    ca co cm prepC KP hscrDown htabLen
    (childLoadScrAll_of_partsScr C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC chanF KP hhtab hparts)

open Classical in
/-- **The corollary, kept.** `SolveMachPrepPins` §7 reduced the whole
prep segment to `ChildLoadPartsAll` at the canonical channel witness,
at the price of `hscrLen`. Here is the same statement with the seam
resolved: verbatim `CentrePrepAll`, from the strengthened parts
residual and the descriptor tower alone. The channel seam is still
`rfl` (`chanTab_hhtab`). -/
theorem centrePrepAll_of_partsScr_chanTab (C : GraphClass)
    (hC : NowhereDense C) (φ : FO 0) (ord : CoverSpec.OrderingRoutine)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hscrDown : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ σ, Scr j σ → Scr (j + 1) σ)
    (htabLen : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → ∀ σ,
      Scr j σ →
      n * (levelFml (Headline.headlineSetup C hC φ) (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hparts : ChildLoadPartsScrAll C hC φ ord G c w q ℓp
      (chanTab (Headline.headlineSetup C hC φ) ℓp) hbf Adm Scr ca co cm prepC
      (chanTabChild (Headline.headlineSetup C hC φ) ord ℓp) KP) :
    CentrePrepAll C hC φ ord G c w q ℓp
      (chanTab (Headline.headlineSetup C hC φ) ℓp) hbf Adm Scr ca co cm
      prepC KP :=
  centrePrepAll_of_partsScr C hC φ ord G c w q ℓp
    (chanTab (Headline.headlineSetup C hC φ) ℓp) hbf Adm Scr ca co cm prepC
    (chanTabChild (Headline.headlineSetup C hC φ) ord ℓp) KP hscrDown
    htabLen (chanTab_hhtab (Headline.headlineSetup C hC φ) ord ℓp) hparts

/-! ## §5 Nothing regressed -/

open Classical in
/-- **The strengthening is free for a length-only descriptor.** Any
`Scr` that satisfied the landed `hscrLen` gets the added conjunct from
the pass's own no-reallocation clause, so `ChildLoadParts` and
`ChildLoadPartsScr` are interchangeable exactly where the old
hypothesis was available. The strengthening therefore costs only a
descriptor that genuinely carries content — which is the one case the
seam is about. -/
theorem childLoadPartsScr_of_parts (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) → (A : Arena (S.pal j) n₀) → (u : Fin A.N) →
      Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (h : ChildLoadParts B S ord ℓp htabF hbf Adm Scr ca co cm prepC
      chanF KP) :
    ChildLoadPartsScr B S ord ℓp htabF hbf Adm Scr ca co cm prepC
      chanF KP := by
  intro k j A hdiag hAdm hbot u
  refine (h k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' ⟨hCL, -⟩ ⟨hpost, hvars, harrs, hlen⟩
  exact ⟨hpost, hscrLen j σ σ' hCL.1.2.2 hlen, hvars, harrs, hlen⟩

open Classical in
/-- The same at the quantified residual: a length-only descriptor gets
the strengthened residual from the landed one. -/
theorem childLoadPartsScrAll_of_partsAll (C : GraphClass)
    (hC : NowhereDense C) (φ : FO 0) (ord : CoverSpec.OrderingRoutine)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      (u : Fin A.N) →
      Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) →
      Fin (ℓp (j + 1)) →
      List (Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (h : ChildLoadPartsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      prepC chanF KP) :
    ChildLoadPartsScrAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      prepC chanF KP :=
  fun x hx =>
    childLoadPartsScr_of_parts (mcB q x) (Headline.headlineSetup C hC φ) ord
      ℓp htabF hbf Adm Scr ca co cm prepC chanF KP hscrLen (h x hx)

open Classical in
/-- **The strengthened residual serves both routes.** It weakens to the
landed `ChildLoadPartsAll`, so a discharger who proves the strengthened
residual has also discharged `SolveMachPrepPins`'
`centrePrepAll_of_parts_chanTab` — for whatever descriptor still
satisfies `hscrLen` — while §4 gives the corollary for one that does
not. -/
theorem childLoadPartsAll_of_partsScrAll (C : GraphClass)
    (hC : NowhereDense C) (φ : FO 0) (ord : CoverSpec.OrderingRoutine)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      (u : Fin A.N) →
      Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) →
      Fin (ℓp (j + 1)) →
      List (Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (h : ChildLoadPartsScrAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      prepC chanF KP) :
    ChildLoadPartsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      prepC chanF KP :=
  fun x hx =>
    childLoadParts_of_partsScr (mcB q x) (Headline.headlineSetup C hC φ) ord
      ℓp htabF hbf Adm Scr ca co cm prepC chanF KP (h x hx)

end Lax3Proofs.Prog
